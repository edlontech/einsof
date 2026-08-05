# What the TzimtzumV4 proofs show

The headline theorem is:

```lean
Tzimtzum.kav_sound : ∀ s, Kav.Reachable ksystem s → allInv s
```

Read it as: start from any legal initial state and run the protocol's 12 registered actions
in any order, any number of times. Every state reached this way satisfies all 32 rules in
`allInv`. This includes interleavings nobody wrote as tests.

## The security contract

The 32 rules are split into five bundles because proving one monolithic conjunction is
needlessly expensive. The split is proof organization only; `allInv` contains every rule.

### S — structural rules (9)

- the root is always active and never has a parent;
- active parent/child edges are well formed, single-parent, and non-reflexive;
- a child's capabilities are a subset of its active parent's;
- the root has every capability;
- an inactive agent has no labels, pending effects, challenges, or crossing grants;
- every pending effect belongs to an active agent.

### P — pending invocation and gate rules (12)

Every pending invocation:

- is unique by invocation id, belongs to a registered exact tool identity, is non-root,
  and has its id in the never-cleared consumed history;
- carries an egress set that narrows to and covers its frozen declaration;
- carries a coherent frozen integrity band;
- was authorizer-approved and capability-approved when it is claimed `contained`;
- satisfies confidentiality flow confinement, integrity confinement, and confidentiality
  clearance against the agent's held/speculative labels.

The weak confinement variants separately establish that DENY-band combinations are
structurally impossible even without trusting an inspector's verdict.

### P′ — concurrency rules (2)

Any two contained pending invocations of one agent are pairwise compatible in both
confidentiality and integrity. The self-pair and quarantined records are included. These
rules are what let one invocation settle and absorb its frozen output labels without
invalidating another invocation that is still running.

### E — evidence rules (6)

- open challenges are invocation-keyed, enforce-only, and bind a coherent frozen scope;
- inspected admissions reference consumed one-use evidence;
- every non-contained/bypassed pending record is honest about monitor mode;
- quarantine is represented on the pending record, so it remains visible to every relevant
  speculative and pairwise quantifier.

### C — crossing authority rules (3)

- remaining crossing uses never exceed the grant's provisioned bound;
- grants belong only to active agents;
- each receiver/assignment key denotes one grant record.

`grant_crossing` is the only faucet. `grant_conservation` proves every other action frames,
deletes, or decrements remaining uses.

## What the gates prevent

### Confidentiality

An agent carrying sensitive taint cannot run an egress-bearing action unless every relevant
held/pending pair is in the ALLOW band or in the INSPECT band with the constrained pending
party vouched. There is no reusable override arm.

### Integrity / prompt injection

Untrusted content cannot drive a destructive action whose frozen integrity floor it fails
to clear. The integrity gate is the dual graduated gate: ALLOW, or INSPECT with one-use
vouching, otherwise deny. Endorsement is the only route to a more trusted output label;
it never cleans the source agent.

### Clearance

A tool's frozen confidentiality clearance limits how tainted its caller may be. This check
is distinct from egress flow policy: clearance is per target/action, while flow is per
channel.

### Parallel execution

The gate includes pairwise checks in both directions plus a self-check. A later invocation
cannot be admitted if its frozen output would make an existing permit unsafe, or vice
versa. Settlement can therefore absorb output labels freely. Monitor-mode label changes
demote affected permits rather than continuing to claim gates that no longer hold.

## Evidence, quarantine, and crossing

Inspection challenges bind invocation, challenge id, exact policy digest, arguments hash,
frozen egress, and authorizer verdict. Resolution consumes a fresh attestation id. Scope
mismatch never falls through to permission.

An ambiguous settlement quarantines the pending record. It cannot become an ordinary
success/failure settlement without a fresh resolution attestation scoped to that invocation
and declared outcome. Until then it stays in the speculative and pairwise sets.

An endorsed `cross_output` requires positive, scope-exact, unconsumed conformance evidence
and a non-exhausted receiver/assignment grant. The action atomically consumes the evidence,
decrements one grant use, and inserts an assignment-bounded pair into the receiver. An
unendorsed fallback releases only at source labels; a fail fallback releases nothing.

`audit_evidence_conservation` proves the kernel half for the three evidence-bearing event
classes from reachable pre-states:

- inspected admission;
- quarantine resolution;
- endorsed crossing (including exact provision-bounded grant decrement).

The complete input records are the event-side attribution. Issuer authentication and truth
are not fields in kernel state and are deliberately not fabricated by the proof.

## How the proof is assembled

There are 416 logical verification conditions:

```text
32 initial obligations + 12 actions × 32 preservation obligations
```

Each action is proved against the five sub-bundles, then reassembled into full `allInv`
preservation. `Kav.reachable_sound` performs ordinary induction over the reachable-state
relation: initial states satisfy the bundle, and every registered guarded transition
preserves it.

The proof crown and all named audit theorems report only:

```text
[propext, Classical.choice, Quot.sound]
```

There is no project-local `sorry`, no SMT solver in the trust base, and no
`native_decide` theorem masquerading as verification.

## Citable results

- `kav_sound` / `kav_soundP`: all 32 invariants in every reachable state;
- `audit_flow_confinement`: CHECK 3a/3b/3c preserves confidentiality confinement;
- `audit_integrity_confinement`: CHECK 5a/5b/5c preserves integrity confinement;
- `integrity_monotonicity`: surviving agents never lose old integrity observations;
- `confidentiality_no_descent`: surviving agents never lose old taint observations;
- `inspection_non_restoration`: inspection resolution frames both label dimensions;
- `crossing_frame_and_bound`: exact receiver/source frame and assignment bounds;
- `grant_conservation`: all 11 non-faucet actions are grant-non-increasing;
- `consumed_ids_monotone` + `invocation_freshness_subsumption`: begun ids cannot be reused;
- `quarantine_resolution_safety` + `quarantine_participates`;
- `audit_evidence_conservation`;
- `audit_fresh_compartment`: delegation creates an empty label/pending/grant compartment.

T-13 replay equivalence is **not** claimed as proved. `replay_equivalence_statement` records
the transition-level obligation; concrete serialized replay is tested at the adapter/kernel
boundary because Kav's closed actions existentially hide command parameters.

## Why this is useful

- It covers every reachable abstract state, not only selected examples.
- It gives “safe” a precise contract the Rust kernel can refine against.
- It turns protocol drift into a build failure.
- It separates kernel-checkable facts (scope, one-use, state updates) from external trust
  seams instead of blending them into one oversized “verified” claim.

## Limits and trust seams

This is a safety proof of the abstract protocol. It is not a proof that the whole deployed
system is secure.

- **Rust refinement status:** the current `argus/formal-lean` theorem is the V3 baseline.
  The V4 abstract proof is complete, but parent Task 8 must regenerate extraction and prove
  the new V4 action bundle before making an end-to-end V4 claim.
- **Extractor:** Aeneas/Charon and its generated semantic model are trusted.
- **Capacity:** the concrete refinement must assume the fired branch has enough `Vec`
  capacity; `grant_crossing n` additionally requires `n < 2^32` for Rust `u32`.
- **Oracle fidelity:** V4 needs per-invocation agreement only for authorizer verdict and
  attested-egress classification. Evidence verdicts are explicit inputs, not timeless
  oracle relations.
- **Authenticated construction:** the adapter must validate `CrossInput`'s exact revision,
  fallback, assignment bounds/digest, receiver pin, and tenant identity before construction.
- **Evidence truth:** the kernel checks positivity, exact scope, and one-use. It does not
  prove issuer authentication, issuer truth, or wall-clock freshness policy.
- **Operations:** identity/STS, canonical serialization, append-before-commit, event
  attribution, and crash/replay integration are outside the abstract theorem.
- **Non-goals:** liveness, arbitrary capability-combination hazards, and sensible LLM
  behavior.

Run the complete check from `tzimtzum/`:

```bash
make verify
lake build Tzimtzum TzimtzumTest
```
