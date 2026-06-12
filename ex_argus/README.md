# ExArgus

Elixir binding for the verified `argus-kernel` authorization state machine
(TzimtzumV2). Pure functional: one function per kernel transition. The caller
owns state, the event log, and the (unverified) authorizer / content-gate /
conformance oracles.

## Usage

    bg = %ExArgus.Kernel.Background{
      tools: %{"read_file" => %{capabilities: [:filesystem_read], egress: [],
                                conf_floor: :sensitive, output_bounded: false,
                                issuer: "trusted"}},
      flow_policy: %{}, flow_overrides: [],
      trusted_issuers: ["trusted"], instruction_issuer: %{}
    }

    state = ExArgus.Kernel.initial_state()
    {:ok, state, _action} = ExArgus.Kernel.register_tool(state, bg, "read_file")

Transitions return `{:ok, state, action}` or `{:error, reason}`, where `reason` is one
of the closed `ExArgus.Kernel.error_reason/0` atoms (mirroring `argus-kernel`'s
`KernelError`).

## Diagnostics: explain, telemetry, shadow, replay

`ExArgus.Explain` mirrors the gate-consuming transitions read-only: it returns the exact
error the transition would return plus, per denied (level, egress) pair, the
counterfactual rescues (override grant / policy change / tool relabel / content-gate
pass). Agreement with the kernel is property-tested in `argus-explain`. Reports are
diagnostics from an unverified crate -- feed them to telemetry and policy review, never
back into authorization decisions.

On a denial, pass the report to `ExArgus.Telemetry.emit_denied/2`
(`[:ex_argus, :flow, :denied]`); aggregate downstream into a periodic policy review.

`ExArgus.Shadow.compare/3` runs one transition against a live and a candidate background
and diffs the decision. `ExArgus.Replay.run/2` + `diff/3` replay a recorded
`{fun, args}` log (with recorded oracle verdicts) against alternative backgrounds for
trajectory-level evidence.

## Snapshot wire version

`ExArgus.state_version/0` stamps the wire shape of `ExArgus.Kernel.State`. Callers that
persist a `State` snapshot store it with this version and fail closed on a mismatch.
**Bump `@state_version` (in `lib/ex_argus.ex`) on any change to `Kernel.State`'s fields
or the NIF encode/decode**, and update the golden field list in `test/ex_argus_test.exs`.

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

The checksum file `checksum-Elixir.ExArgus.Native.exs` MUST be committed and
shipped in the Hex package.
