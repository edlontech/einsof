# TzimtzumV4 authorization protocol

Tzimtzum is the formally verified source of truth for Einsof's authorization state
machine. It is a pure Lean 4 specification built on the [Kav](../kav/) transition-system
framework. The proof is kernel-checked; no SMT solver is in the trusted computing base.

For a plain-language account of the guarantees and limits, see
[PROOFS.md](PROOFS.md).

## Verified surface

V4 has **12 actions** and **32 state invariants**, all proved inductive:

1. `register_tool`
2. `unregister_tool`
3. `delegate`
4. `grant_capability`
5. `grant_crossing`
6. `revoke`
7. `cascade_revoke`
8. `ingest`
9. `begin_invocation`
10. `authorize_inspected`
11. `settle_invocation`
12. `cross_output`

The invariants are intentionally split into five bundles:

| Bundle | Count | Purpose |
|---|---:|---|
| S | 9 | agent tree, capability, revocation, active ownership |
| P | 12 | pending identity, freshness, gates, clearance |
| P′ | 2 | pairwise confidentiality and integrity compatibility |
| E | 6 | challenge/evidence scope, one-use, monitor/quarantine honesty |
| C | 3 | crossing-grant bound, active ownership, key pinning |

This is **416 logical VCs**: 32 initial-state obligations plus 12 × 32 preservation
obligations. Expensive semantic VCs are proved as single conjuncts and then reassembled;
that proof organization changes automation cost, not the logical count.

The local checks assemble through `Kav.reachable_sound` into:

```lean
Tzimtzum.kav_sound : ∀ s, Kav.Reachable ksystem s → allInv s
Tzimtzum.kav_soundP : -- the same theorem at arbitrary sort instantiations
```

Therefore every state reachable through any ordering of the 12 actions satisfies the
complete bundle.

## Protocol mechanics

### Invocation and inspection

`begin_invocation` checks capability, confidentiality clearance, pairwise flow,
authorizer approval, and pairwise integrity against a frozen policy snapshot and the
invocation's attested egress set.

Its canonical partition is:

- `allow` → a plain, contained pending invocation;
- `inspection_required` in `enforce` → an invocation-keyed challenge and no pending effect;
- `inspection_required` in `monitor` → a monitor-bypassed pending effect;
- `deny` in `monitor` → a monitor-bypassed pending effect;
- `deny` in `enforce` → no transition.

`authorize_inspected` requires exact challenge scope, one-use evidence, a positive
inspection verdict, and a re-evaluation of the live gate. A negative verdict or live-gate
failure closes fail-closed; a scope mismatch is rejected at the boundary and leaves the
challenge unresolved.

### Settlement and quarantine

`settle_invocation` absorbs the frozen output confidentiality/integrity pair on ordinary
success or failure. `ambiguous` keeps the invocation pending and marks it quarantined.
A quarantined record can settle only with a fresh resolution attestation scoped to that
invocation and declared outcome. Quarantined records remain in speculative and pairwise
quantifiers until resolution or revocation.

### Crossing

`grant_crossing` is the root-only operator faucet. It provisions a receiver/assignment key
with `{ remaining, provisioned }`; it is set-to-`n`, not additive.

`cross_output` has an exact trichotomy:

- `endorsed` when `endorsedOK` holds: consume scope-exact conformance evidence, decrement
  one grant use, and insert the assignment-bounded released pair into the receiver;
- `unendorsed` when endorsement is unavailable and the authenticated revision declares
  `release_unendorsed`: release at source labels with no evidence or grant consumption;
- `fail` when endorsement is unavailable and the revision declares `fail`: release
  nothing.

`cross_branch_total` and `cross_branch_exclusive` prove the partition total and disjoint.
The crossing id is consumed on every transitioning arm. Receiver-side permit holds or
monitor demotion prevent a label update from invalidating an in-flight permit.

## Named theorems

`Tzimtzum/Transitions.lean` and `Tzimtzum/Audit.lean` expose the citable results:

- T-1/T-2: `audit_integrity_confinement`, `audit_flow_confinement`;
- T-3/T-4: integrity monotonicity and confidentiality no-descent for all 12 actions,
  with the explicit agent-lifecycle exception;
- T-5: inspection does not restore either label dimension and its attestation cannot
  admit another invocation;
- T-6: exact E25 crossing frame, source-frame exception, and release bounds;
- T-7: `grant_conservation` for all 11 non-faucet actions;
- T-8: permit stability through ingestion, settlement, and crossing/monitor demotion;
- T-9: consumed invocation ids persist across every action and every begin burns a fresh id;
- T-10: quarantine requires scope-exact one-use resolution and remains in gate quantifiers;
- T-11: `audit_evidence_conservation` for inspected admission, quarantine resolution, and
  endorsed crossing steps whose pre-state is reachable;
- T-12: `audit_fresh_compartment`, the defensive post-delegation empty-label/pending/grant
  guarantee.

T-13 is deliberately only `replay_equivalence_statement`: Kav's closed relational actions
hide serialized parameters, so concrete replay determinism is a parent adapter/kernel
conformance obligation rather than a claimed abstract theorem.

`#print axioms` on every proof crown reports only:

```text
[propext, Classical.choice, Quot.sound]
```

There is no project-local `sorry`, `native_decide` proof, or unnamed protocol axiom.

## Build and verification

```bash
cd tzimtzum
lake exe cache get                       # after toolchain/dependency changes
make build                               # fast incremental abstract spec
make verify                              # package-clean full V4 verification
lake build Tzimtzum TzimtzumTest         # explicit spec + all-check target
```

`make verify` runs `lake clean tzimtzum` and then builds both libraries. It does not erase
mathlib's downloaded cache. The pinned toolchain is Lean 4.32.1/mathlib 4.32.1.

## Trust statement and scope

The proof establishes safety of the **abstract V4 transition system**. It does not prove:

- liveness, deadlock freedom, or that a legitimate request will be accepted;
- arbitrary capability-combination safety;
- LLM behavior;
- the external SPIFFE/STS identity mesh, persistence/serialization, append-before-commit,
  event attribution, or adapter correctness;
- attestation issuer truth or wall-clock freshness policy. The kernel checks positivity,
  exact scope, and one-use consumption; issuer authentication/truth is an external seam;
- the Aeneas/Charon extractor or hand-written Rust source.

External-ingress labels are adapter inputs. Agent-to-agent delivery is additionally checked
against the source agent's kernel-held labels, but authentic delivery and tenant identity
remain boundary obligations.

### `CrossInput` authentication boundary

`CrossInput` is the authenticated contract-revision/assignment request. Before constructing
it, the adapter must validate the exact revision descriptor and fallback, assignment digest
and bounds, receiver assignment pin, and applicable identity/tenant binding. Missing,
stale, or mismatched authority is rejected at the boundary and never reaches
`cross_output`; the kernel therefore does not authenticate those fields itself.

### State shapes the kernel must reproduce

V4 has 11 abstract sorts. Mutable state contains the agent tree/capabilities, dual label
sets, invocation-keyed `pending` and `challenges`, consumed invocation/attestation/crossing
histories, receiver/assignment-keyed crossing grants, and the tool registry. Egress
ceilings, enforcement mode, and root identity are immutable background.

A frozen action snapshot carries the exact composite `ToolId`, required capabilities,
confidentiality clearance, integrity allow/inspect floors, output label pair, declared
egress, and policy digest. Pending records additionally carry agent, attested egress,
admission, disposition, authorizer verdict, and quarantine. Challenge scope carries the
challenge id, agent, snapshot/egress, arguments hash, and authorizer verdict.

### Extracted-kernel refinement

[`argus/formal-lean`](../argus/formal-lean/) now proves
`ArgusLean.Refinement.implementation_sound` for the extracted V4 kernel over all twelve actions.
Every reachable extracted state refines a TzimtzumV4 state satisfying all 32 invariants, modulo the
trusted Charon/Aeneas extraction and two explicit hypotheses:

**`OracleFidelity`** is per-invocation agreement only for:

1. the authorizer verdict; and
2. egress-kind classification producing the attested egress set.

Inspection, quarantine resolution, and conformance decisions are explicit attestation inputs, not
timeless ContentGate/Conformance oracle relations. The kernel verifies their scope and one-use;
issuer truth remains external.

**`CapacityOK`** states governed-root initialization coherence, the fixed begin-time snapshot
prediction, `grant_crossing n < 2^32`, and exactly the allocations made by each successful branch:

- register: tool-set insertion;
- delegate: active/parent insertions;
- grant capability: outer capability map and child set;
- grant crossing: grant-map insertion;
- ingest: taint/integrity outer-map and inner-set insertions;
- begin: pending-or-challenge insertion plus consumed-id insertion;
- authorize: admitted-pending insertion plus consumed-attestation insertion;
- settle: ambiguous pending reinsertion, or non-ambiguous label and optional resolution-evidence
  writes;
- cross: unconditional crossing-id insertion; endorsed label/evidence/grant writes; or unendorsed
  source-label copies with joint destination/source bounds;
- removal and frame-only branches: no growth bound.

A single insertion requires `length < Usize.max`; bulk copying requires the exact destination/source
bounds exposed by the extracted loops. These premises apply only to successful commands from
reachable related states and are not hidden in concrete reachability.
