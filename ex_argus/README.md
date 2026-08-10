# ExArgus

ExArgus is the Elixir adapter for the Argus V4 authorization kernel. Its supported
runtime boundary is an opaque live `ExArgus.Instance`, the exact twelve V4 actions,
read-only V5 state and chain observations, and strict V5 recovery.

## Background and lifecycle

A background has exactly three fields:

```elixir
alias ExArgus.Instance
alias ExArgus.Kernel.Background

kinds = [:network_external, :network_internal, :filesystem_write, :ipc]
deny_all = Map.new(kinds, &{&1, nil})

background = %Background{
  mode: :enforce,
  allow_ceiling: deny_all,
  inspect_ceiling: deny_all
}

{:ok, instance} = Instance.new(background)
{:ok, state} = Instance.state(instance)
{:ok, chain} = Instance.status(instance)
```

`mode` is `:enforce` or `:monitor`. Both ceiling maps must contain exactly the four
egress keys above. Each value is `nil` (deny that band) or one of `:public`,
`:internal`, `:sensitive`, and `:restricted`; a level is admitted when it is at or
below the configured ceiling. The root is fixed as `"root"`, starts active, and holds
all fifteen capabilities. It is not a caller-configurable background field.

`new/1` returns a fresh live resource. `state/1` returns the canonical twelve-field,
read-only `ExArgus.Kernel.State`; it cannot be imported. `status/1` returns
`%ExArgus.Chain{version: 5, sequence: accepted_history_length, head: digest}`. At
genesis, the sequence is zero and the head binds the complete background.

## Live action API

Every accepted action returns `{:ok, %ExArgus.Envelope{}}`. A refusal returns
`{:error, %ExArgus.Error{}}` without changing state, sequence, or head.

The exact action surface is:

1. `register_tool(instance, tool)`
2. `unregister_tool(instance, tool)`
3. `delegate(instance, grantor, grantee)`
4. `grant_capability(instance, parent, child, capability)`
5. `grant_crossing(instance, grantor, agent, assignment, count)`
6. `revoke(instance, parent, target)`
7. `cascade_revoke(instance, child, parent)`
8. `ingest(instance, %ExArgus.Command.Ingest{})`
9. `begin_invocation(instance, %ExArgus.Command.BeginInvocation{})`
10. `authorize_inspected(instance, %ExArgus.Command.AuthorizeInspected{})`
11. `settle_invocation(instance, %ExArgus.Command.SettleInvocation{})`
12. `cross_output(instance, %ExArgus.Command.CrossOutput{})`

`resolve_quarantine(instance, invocation, outcome, attestation)` is a convenience helper
for a `settle_invocation` with a `:success` or `:failure` resolution. It is not a
thirteenth kernel action. The command, action, evidence, policy snapshot, and crossing
structs under `ExArgus.Command` and `ExArgus.Kernel` are closed: unknown keys, enum
values, duplicate set members, malformed UTF-8, and omitted trusted fields fail closed.

## Envelopes, persistence, and recovery

An accepted `%ExArgus.Envelope{}` contains the exact V5 version, positive sequence,
previous digest, digest, replay-complete command, and computed action. The adapter uses a
domain-separated SHA-256 chain; it does not choose a storage serialization and does not
persist anything.

The host must durably retain each accepted envelope and a protected trusted anchor
containing the latest head and length. Recover only with:

```elixir
Instance.recover(background, complete_envelope_history, trusted_chain)
```

`recover/3` strictly validates V5 structures and bounds, starts from the background-bound
genesis, re-executes each command in sequence, and checks its action, predecessor, and
digest. It exposes a live instance only when the final head and sequence equal the
supplied `%ExArgus.Chain{}`. Corruption returns an indexed typed error; recovery emits no
transition telemetry. A valid old prefix is still a rollback unless the host protects
its current head and length outside the envelope store.

## Fixed limits

The V5 profile is protocol-fixed and mirrored by `ExArgus.Limits`:

| Limit | Value |
| --- | ---: |
| UTF-8 bytes per opaque value | 1,024 |
| agents | 4,096 |
| parent or label-map keys | 4,096 |
| registered tools | 1,024 |
| pending invocations | 4,096 |
| open challenges | 4,096 |
| crossing grants | 16,384 |
| consumed invocation IDs | 65,536 |
| consumed attestations | 65,536 |
| consumed crossings | 65,536 |
| retained UTF-8 bytes | 16 MiB |
| accepted sequence | 100,000 |
| recovery envelopes | 100,000 |
| replay content bytes | 64 MiB |
| capabilities per set | 15 |
| egress kinds per set | 4 |
| confidentiality levels per set | 4 |
| integrity levels per set | 4 |

Limits are checked before commit. Capacity or sequence exhaustion is a typed refusal, not
a reason to bypass or rebuild the kernel with different limits.

## Telemetry

Each live transition attempt emits exactly one `[:ex_argus, :transition]` event after
its result is fixed. Measurements contain only `duration`. Metadata is bounded to
`command`, `outcome`, `sequence`, `reason`, `verdict`, `disposition`, and `branch`; it
never includes identifiers, hashes, commands, policies, evidence, prompts, arguments, or
results. Outcomes are `:accepted`, `:kernel_refused`, `:boundary_refused`, or
`:internal_error`.

Handlers run synchronously. Their absence or failure cannot change the fixed result, but
a slow handler can make a successful call appear timed out. Telemetry is observation,
not durable evidence.

## Host ordering and trust boundary

One host owner must serialize access to each live instance. The host must authenticate
and freeze command meaning, policy and assignment revisions, tenant and identity
bindings, authorizer verdicts, attested egress, and inspection, resolution, and
conformance evidence. For every accepted transition it must durably store the envelope
plus the protected head and length before issuing the next command or any authorized
effect.

If persistence fails, discard the advanced instance and recover from the prior durable
chain and trusted anchor. After a timeout or binding exception, treat the result as
ambiguous: do not retry blindly; discard and recover. The resource mutex provides atomic
in-process transitions, not host persistence ordering or rollback protection.

The extracted V4 kernel covers exactly 12 actions and yields all 32 invariants modulo
trusted Aeneas/Charon extraction, `CapacityOK`, and narrowed `OracleFidelity`. This does
not verify the handwritten Rust itself. Handwritten Rust, ExArgus and telemetry,
authentication/identity/evidence truth, serialization and persistence, the native
digest-chain adapter and trusted rollback anchor, and host one-owner/persist-before-effect
ordering are outside formal verification. The adapter is conformance-tested.

## Building and checking

Source builds are the default in every Mix environment:

```bash
cd ex_argus
mix compile
```

`EX_ARGUS_USE_PRECOMPILED=1` explicitly opts into the configured GitHub release artifacts.
`RUSTLER_PRECOMPILED_FORCE_BUILD=1` or `true` forces a source build and wins when both
variables are set. `RustlerPrecompiled`, the configured base URL, target matrix, and
checksum behavior remain part of the loader; precompiled publication is separate from a
source build.

Current checks:

```bash
mix format --check-formatted
MIX_ENV=test RUSTLER_PRECOMPILED_FORCE_BUILD=1 mix test
mix credo --strict
mix dialyzer
env -u EX_ARGUS_USE_PRECOMPILED -u RUSTLER_PRECOMPILED_FORCE_BUILD \
  MIX_ENV=prod mix compile --force
```
