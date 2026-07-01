# ExArgus

Elixir binding for the verified `argus-kernel` authorization state machine
(TzimtzumV2). Pure functional: one function per kernel transition. The caller
owns state, the event log, and the (unverified) authorizer, content-gate, and
conformance oracles.

## Usage

    bg = %ExArgus.Kernel.Background{
      tools: %{"read_file" => %{capabilities: [:filesystem_read], egress: [],
                                conf_floor: :sensitive, output_bounded: false,
                                issuer: "trusted"}},
      flow_policy: %{}, flow_overrides: [],
      trusted_issuers: ["trusted"], instruction_issuer: %{}
    }

    state = ExArgus.Offline.initial_state()
    {:ok, state, _action} = ExArgus.Offline.register_tool(state, bg, "read_file")

Transitions return `{:ok, state, action}` or `{:error, reason}`, where `reason` is one
of the closed `ExArgus.Offline.error_reason/0` atoms (mirroring `argus-kernel`'s
`KernelError`).

## Live vs offline

- `ExArgus.Instance` is the live authorization API. `Instance.new(bg)` returns an opaque
  handle holding the only mutable copy of the kernel state inside the verified NIF
  resource; transitions return `{:ok, seq, action} | {:error, reason}`. State exports only
  via `Instance.state/1`; it can never be imported back, so out-of-reachable-space state is
  unrepresentable on the live path. Restart recovery is `Instance.recover(bg, log)`, a
  strict event-sourced replay of a `{fun, args}` log.
- `ExArgus.Offline` is the state-passing API for offline use only (replay, shadow,
  property tests, explain on snapshots); never for live authorization. `ExArgus.Replay` and
  `ExArgus.Shadow` build on it.

## Egress allowlist

The verified kernel's authorizer hook sees only `(agent, tool, state, bg)`; it cannot see
a per-call argument such as a URL. `ExArgus.EgressPolicy` is a pure, fail-closed URL/path
allowlist, and `ExArgus.EgressAuthorizer.admit?/4` folds its verdict into the single
authorizer boolean that `Instance.invoke_start/6` consumes. This keeps the destination ACL
on the unverified, conformance-tested side of the guest-model boundary; it can only
subtract from what the kernel already permits, never widen it, and `implementation_sound`
is unchanged.

## Diagnostics: explain, telemetry, shadow, replay

`ExArgus.Explain` mirrors the gate-consuming transitions read-only: it returns the exact
error the transition would return plus, per denied `(level, egress)` pair, the
counterfactual rescues (override grant, policy change, tool relabel, content-gate pass).
Agreement with the kernel is property-tested in `argus-explain`. These reports are
diagnostics from an unverified crate; feed them to telemetry and policy review, never back
into authorization decisions.

On a denial, pass the report to `ExArgus.Telemetry.emit_denied/2`
(`[:ex_argus, :flow, :denied]`); aggregate downstream into a periodic policy review.

`ExArgus.Shadow.compare/3` runs one transition against a live and a candidate background
and diffs the decision. `ExArgus.Replay.run/2` plus `diff/3` replay a recorded
`{fun, args}` log (with recorded oracle verdicts) against alternative backgrounds for
trajectory-level evidence.

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
