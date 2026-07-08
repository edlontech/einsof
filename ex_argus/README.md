# ExArgus

Elixir binding for the verified `argus-kernel` authorization state machine
(TzimtzumV3, 16 spec actions). Pure functional: one function per kernel
transition. The caller owns state, the event log, and the (unverified)
authorizer, content-gate, and conformance oracles.

## Usage

    bg = %ExArgus.Kernel.Background{
      tools: %{
        "web_fetch" => %{
          capabilities: [:network_egress],
          egress: [:network_external],
          conf_floor: :public,
          output_bounded: true,
          issuer: "trusted",
          integ_floor: :untrusted,
          integ_inspect_floor: :untrusted,
          output_integ: :untrusted
        }
      },
      allow_ceiling: %{network_external: :sensitive},
      inspect_ceiling: %{},
      trusted_issuers: ["trusted"],
      instruction_issuer: %{}
    }

    state = ExArgus.Offline.initial_state()
    {:ok, state, _action} = ExArgus.Offline.register_tool(state, bg, "web_fetch")
    {:ok, state, _action} = ExArgus.Offline.delegate(state, bg, "root", "a1")
    {:ok, state, _action} = ExArgus.Offline.grant_capability(state, bg, "root", "a1", :network_egress)

    {:ok, state, {:invoke_start, "a1", "web_fetch", "i1"}} =
      ExArgus.Offline.invoke_start(state, bg, "a1", "web_fetch", "i1", true, %{}, [:network_external])

`tools` entries carry three integrity fields alongside the confidentiality
ones -- `integ_floor`/`integ_inspect_floor` (the dual integrity gate,
CHECK 4a/4b/4c) and `output_integ` (what the tool's own output emits at). All
three are required: the NIF decode fails closed on a missing key rather than
defaulting to a trusted level. `invoke_start`'s last argument is the
invocation's **attested egress** -- the egress kinds this specific call
actually touches, checked against the tool's declared `egress` set (see
below).

Transitions return `{:ok, state, action}` or `{:error, reason}`, where `reason` is one
of the closed `ExArgus.Offline.error_reason/0` atoms (mirroring `argus-kernel`'s
`KernelError`).

## Live vs offline

- `ExArgus.Instance` is the live authorization API. `Instance.new(bg)` returns an opaque
  handle holding the only mutable copy of the kernel state inside the verified NIF
  resource; transitions return `{:ok, seq, action} | {:error, reason}`. State exports only
  via `Instance.state/1`; it can never be imported back, so out-of-reachable-space state is
  unrepresentable on the live path. Restart recovery is `Instance.recover(bg, log)`, a
  strict event-sourced replay of a version-stamped `{fun, args}` log (see below).
- `ExArgus.Offline` is the state-passing API for offline use only (replay, shadow,
  property tests, explain on snapshots); never for live authorization. `ExArgus.Replay` and
  `ExArgus.Shadow` build on it.

## Egress attestation

The verified kernel's authorizer hook sees only `(agent, tool, invocation, state, bg)`; it
cannot see a per-call argument such as a URL, and it consumes egress only as an
uninterpreted per-invocation kind set -- it never sees a URL at all.
`ExArgus.EgressPolicy.classify/2` is a pure, fail-closed URL classifier: it maps a URL
against an agent's rule set to the **union** of kinds every matching rule attests, or
`:deny` on no match (or a malformed/unparseable URL). `ExArgus.EgressAuthorizer.attest/4`
folds that into the `{authorized?, attested_kinds}` pair `invoke_start` consumes, unioning
across multi-URL calls (`%{urls: [...]}`) and denying the whole call if any URL denies.
Call arguments with no URL dimension (e.g. `send_email`) attest the tool's full declared
egress set -- V2's static worst case, still sound, just less precise.

The kernel enforces two checks on the attested set, both fail-closed:
**narrowing** (attested kinds must be a subset of the tool's declared `egress`) and
**coverage** (an egress-bearing tool cannot be admitted on an empty attestation). Either
violation denies with `:attestation_invalid`. The adapter must never intersect a rule
union with the tool's declared set to "fix" an over-wide attestation -- that would
silently narrow a real attestation into a false one; let the kernel's `:attestation_invalid`
surface instead.

This keeps URL/path matching on the unverified, conformance-tested side of the
guest-model boundary: it can only subtract from what the kernel already permits, never
widen it, and `implementation_sound` is unchanged.

## Versioned event log

Every recordable log begins with `ExArgus.log_header/0` (`{:state_version, 4}`), checked
by `Instance.recover/2` and `Replay.run/2`/`diff/3` **before any entry replays**. A missing
or mismatched header returns `{:error, :state_version_mismatch}` (or the equivalent
`recovery_error` shape from `Instance.recover/2`) without touching any entry -- a
V3-shape-compatible V2 log (e.g. one containing only `delegate`/`invoke_complete`
entries, unchanged in arity) would otherwise replay structurally fine while meaning
something different (V2's `delegate` gave a full budget meter; V3's gives zero). The
version stamp makes that rejection deterministic instead of luck-based.

## Upgrading from V2

This is a hard break, not a migration. There is no V2-to-V3 log shim: restart every
live agent from a fresh `Instance.new/1` and start a fresh, version-stamped log.
Synthesizing V3 attestations for old V2 log entries would fabricate per-invocation
egress/integrity data that was never actually attested -- exactly what freshness and
narrowing exist to prevent.

## Operational notes

- **Budget-zero children.** `ExArgus.Offline.delegate/4` (and the `Instance` equivalent)
  spawns children at `agent_budget` 0. A freshly delegated child cannot pay for an
  endorsed return or an override re-arm until `sentinel_credit_budget` funds it; before
  that, completions route through the unendorsed path. This is kernel behavior, not a bug.
- **A blocked `sentinel_degrade_integrity` is a platform obligation.** When the dual
  integrity gate denies a degrade because a below-floor tool is in flight, the caller must
  hold the ingestion that triggered the degrade until the in-flight invocation completes
  and the degrade can be retried -- never deliver the ingested content and drop the
  degrade. The binding cannot enforce this; it only surfaces the denial.
- **Invocation replay precedence.** Through `ExArgus.Instance`, reusing an invocation id
  surfaces `:invocation_exists`, not `:invocation_replayed` -- the invocation-tool binding
  check fires first because `invocation_tool` persists across completion.
  `:invocation_replayed` is reachable at the transition level (an id present in
  `invocation_used` but absent from `invocation_tool`). Replay is denied either way.
- **The content-gate map is always safe empty.** `content_gate_targets/2` and
  `content_gate_map/3` compute exactly which invocations CHECK 2b/4b/4c will query for a
  vouch. An empty `%{}` is always safe -- fail-closed, it can never widen permissions --
  but any pair that lands in an INSPECT band then goes unvouched, so the transition
  denies (`:flow_gate_blocked` / `:integrity_floor_denied`).

## Diagnostics: explain, telemetry, shadow, replay

`ExArgus.Explain` mirrors the gate-consuming transitions read-only across six entry
points -- `explain_invoke`, `explain_return_unendorsed`, `explain_return_endorsed`,
`explain_sentinel_elevate_taint`, `explain_sentinel_degrade_integrity`, and
`explain_grant_override` -- returning the exact error the transition would return plus,
per denied pair, the counterfactual rescues (override grant, policy change, tool relabel,
content-gate pass, lever floor relabel). Agreement with the kernel is property-tested in
`argus-explain`. These reports are diagnostics from an unverified crate; feed them to
telemetry and policy review, never back into authorization decisions.

On a denial, pass the report to `ExArgus.Telemetry.emit_denied/2`
(`[:ex_argus, :flow, :denied]`); on an accepted `invoke_complete`, pass the action to
`ExArgus.Telemetry.emit_completed/2` (`[:ex_argus, :flow, :completed]`), which carries the
`endorsed` flag so the policy-review loop can distinguish endorsed from unendorsed
completions.

`ExArgus.Shadow.compare/3` runs one transition against a live and a candidate background
and diffs the decision. `ExArgus.Replay.run/2` plus `diff/3` replay a recorded,
version-stamped `{fun, args}` log (with recorded oracle verdicts) against alternative
backgrounds for trajectory-level evidence.

## Trust statement

`argus-kernel` is refined against TzimtzumV3 -- `implementation_sound` holds over all 16
spec actions -- modulo the trusted Aeneas/Charon extractor and two explicit assumptions,
`CapacityOK` and `OracleFidelity`. This binding, and the authorizer/content-gate/conformance
oracles it wraps, are **conformance-tested, not verified**: they sit on the unverified side
of the guest-model boundary. Do not treat `ex_argus`, the oracles, or the egress classifier
as carrying the kernel's proof.

## Snapshot wire version

`ExArgus.state_version/0` stamps the wire shape of `ExArgus.Kernel.State`. Callers that
persist a `State` snapshot store it with this version and fail closed on a mismatch. Bump
`@state_version` (in `lib/ex_argus.ex`) on any change to `Kernel.State`'s fields or the NIF
encode/decode, and update the golden field list in `test/ex_argus_test.exs`.

## Building locally

The native crate is at `native/argus_nif` and depends on `../argus` (monorepo
sibling). To force a local build instead of downloading a precompiled artifact:

    RUSTLER_PRECOMPILED_FORCE_BUILD=1 mix compile

(`:dev` and `:test` force-build by default.)

## Releasing precompiled artifacts

1. Tag `ex_argus-vX.Y.Z` and push; CI builds the cdylib for every target in
   `ExArgus.Native` and attaches the archives to the GitHub release.
2. Regenerate the checksum file and commit it:

       mix rustler_precompiled.download ExArgus.Native --all --print

The checksum file `checksum-Elixir.ExArgus.Native.exs` must be committed and
shipped in the Hex package.
