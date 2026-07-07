# What the proofs actually show

The theorem is:

```
Tzimtzum.kav_sound : ∀ s, Kav.Reachable ksystem s → allInv s
```

Read it as: for any state `s` reachable by running the protocol's 13 actions in any
order, any number of times, `s` satisfies all 21 rules in `allInv`. The proof holds for
every reachable state, including ones nobody has written a test for.

## What is being proved

The protocol is a state machine: 13 actions (`register_tool`, `delegate`, `invoke_start`,
`revoke`, ...) that each take a state and produce a new one, plus 21 rules the state must
always satisfy. The rules split into two groups.

### 9 safety properties -- the rules that actually matter for security

- **root_always_active** -- the root agent can never be deactivated. There is always
  someone who can act.
- **default_deny** -- every in-flight tool call was actually authorized: the authorizer
  approved it, and the agent held every capability the tool required. Nothing runs by
  skipping a check.
- **flow_confinement** -- the core exfiltration guarantee. If an agent carries taint at
  some confidentiality level and is mid-invocation of a tool that sends data out, that
  combination is only allowed when the flow policy explicitly ALLOWs it, or the policy
  says INSPECT and a content gate approved it, or a one-time override lets it through.
  There is no fourth path. This is the formal version of "an agent that read your private
  files cannot silently email them out."
- **flow_confinement_weak** -- the same guarantee restated so it holds even if you don't
  trust the authorizer/content-gate oracles to behave correctly: pairs marked DENY are
  blocked by the state machine's structure, not by hoping an oracle says no.
- **capability_subsumption** -- a child agent's capabilities are always a subset of its
  parent's. Delegation can narrow authority; it can never broaden it.
- **revocation_clean** -- a deactivated agent has no leftover in-flight calls and no
  leftover taint. Revocation is immediate and total, not eventually-consistent.
- **tool_attestation_intact** -- every registered tool's declared labels came from a
  trusted issuer. A tool can't self-report as safe.
- **instruction_attestation_intact** -- the same guarantee for system prompts / loaded
  instructions: they must come from a trusted issuer, closing off "smuggle a malicious
  instruction in as if it were legitimate."
- **override_consumed_when_sole_justification** -- the one-time "break glass" override
  can't be reused. If an override is the only thing letting a tainted flow through, it is
  marked used at that moment.

### 12 strengthening invariants -- the scaffolding the proof needs to stand up

Consistency facts -- "the agent tree has one parent per node," "budgets stay within
bounds," "in-flight invocations only exist for active agents and registered tools" --
that have to hold at every step for the induction proving the safety properties to go
through. The load-bearing walls: nobody cares about them directly, but the roof
(`flow_confinement` and friends) falls without them. The full list is in
`Tzimtzum/Invariants.lean`.

The declassification budget (`agent_budget : AgentId → Nat`) is a total function, not a
relation: an agent's budget is a plain number, updated by classical `ite` point-updates
in every action that touches it. `delegate` sets a new agent's budget to 0 -- delegation
mints no budget; `sentinel_credit_budget` is the only faucet.

## How the proof is actually done

For each of the 21 rules and each of the 13 actions, there is a verification condition:
*if the rule holds before the action runs and the action's preconditions are met, the
rule still holds after.* That's 13 x 21 = 273 preservation checks, plus 21 checks that
the rules hold in the initial state -- 294 total. All but 6 are discharged automatically
by mathlib tactics (`grind`, `simp_all`, `auto`, `duper`); 6 are proved by hand:
`revocation_clean` under `delegate`, `invoke_complete`, `return_endorsed`,
`grant_override`, and `sentinel_credit_budget` (a classical `ite` elsewhere in the same
action's update stalls the shared automation on this one rule, even though
`revocation_clean` itself never mentions the budget), plus `budget_bounded` under
`sentinel_credit_budget` (the saturating credit hides its `≤ capacity` bound behind an
`@[irreducible]` definition the automation can't see through).

Those 294 local checks are then assembled into the one global theorem above by
induction over reachability: if the rules hold initially, and every action preserves
them, they hold in every reachable state, full stop.

The trust base is small and checkable: `#print axioms Tzimtzum.kav_sound` shows only
`propext`, `Classical.choice`, `Quot.sound` -- the three standard Lean kernel axioms.
No `sorry`, no SMT solver, no `native_decide`. Anyone with Lean installed can re-run
`make verify` and get the same PASS table.

## Why this is useful

- **It covers every reachable state.** A test suite checks the scenarios you wrote down.
  This covers all of them, including the ones an attacker would find and you wouldn't.
- **It gives "safe" a precise, checkable meaning.** "Prevents exfiltration via prompt
  injection" is a sentence people can talk past each other about. `flow_confinement` is a
  formula a machine either accepts or rejects.
- **Design bugs surface here, not in production.** A broken invariant fails a `lake
  build` in seconds. The same bug found later means either a pentest catches it or, worse,
  it ships.
- **It's a stable contract for the Rust kernel to refine against.** `argus-kernel` doesn't
  have to be independently argued safe -- it has to be shown to implement this spec, which
  is a narrower and more tractable question (see [Limitations](#limitations)).

## Limitations

Be precise about what "proved" covers here, because it's narrower than "the system is
secure."

- **This proves the abstract specification, not the Rust kernel by itself.** The
  connection is a separate layer: `argus-kernel` is mechanically extracted to Lean via
  Aeneas/Charon and refined against this spec in
  [`argus/formal-lean/`](../argus/formal-lean/), where `implementation_sound` shows every
  reachable state of the *extracted model* refines a safe abstract state. That refinement
  is complete, but it trusts the Aeneas/Charon extractor itself, and it rests on two
  explicit assumptions: `Vec` capacity bounds hold at runtime, and the runtime oracles
  agree with their abstract counterparts. It does not independently verify the
  hand-written Rust source.
- **The oracles are trusted, not verified.** `invocation_authorized`, `invocation_gate_passes`,
  `invocation_conforms`, `return_conforms`, `trusted_issuer` are uninterpreted in the spec.
  The proof says *if the oracle answers correctly, the state stays safe* -- it says
  nothing about whether the oracle's answer is actually correct. A misconfigured policy
  engine or a compromised content gate defeats the guarantee without breaking any proof.
- **Identity, tokens, and revocation propagation are out of scope entirely.** Per the
  guest-model decision, those live in an external SPIFFE/STS mesh and an unverified,
  conformance-tested Elixir adapter -- not in this proof.
- **Capability-combination attacks are explicitly not defended against.** An agent
  holding two individually-safe capabilities whose combination is unsafe is not caught by
  this spec -- a deliberate, documented non-goal.
- **This is a safety proof, not a liveness proof.** It shows nothing bad ever happens. It
  does not show the system makes progress, avoids deadlock, or ever lets a legitimate
  request through.
- **The model assumes one serialization point.** The proof treats actions as atomic
  steps over a single global state. That assumption has to hold in the real deployment
  (one GenServer, one mutex) for the guarantee to transfer -- sharding kernel state across
  processes would silently invalidate it.
- **It says nothing about the LLM's behavior.** The proof constrains what actions an
  agent is *allowed* to take. Whether the model behaves sensibly inside those bounds is a
  different problem this system doesn't address.
