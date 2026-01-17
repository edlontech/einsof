# Tzimtzum v2.3 -- Verification Report

| | |
|---|---|
| **Spec** | `TzimtzumV2.lean` (648 lines) |
| **Prover** | Lean 4 + Veil 2.0 + cvc5 (SMT) |
| **Date** | 2026-02-17 13:50 UTC |
| **Status** | **PASSED** |
| **VCs** | 200/200 passed |

## Safety Properties (7)

| Property | Init | invoke_complete | grant_capability | delegate | register_tool | return_endorsed | invoke_start | cascade_revoke | return_unendorsed | revoke |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `root_always_active` | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS |
| `default_deny` | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS |
| `flow_confinement` | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS |
| `flow_confinement_weak` | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS |
| `capability_subsumption` | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS |
| `revocation_clean` | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS |
| `taint_integrity` | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS |

## Strengthening Invariants (12)

| Property | Init | invoke_complete | grant_capability | delegate | register_tool | return_endorsed | invoke_start | cascade_revoke | return_unendorsed | revoke |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `parent_implies_active` | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS |
| `single_parent` | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS |
| `no_self_parent` | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS |
| `root_no_parent` | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS |
| `in_flight_active` | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS |
| `in_flight_registered` | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS |
| `in_flight_unique` | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS |
| `root_all_caps` | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS |
| `root_no_in_flight` | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS |
| `ghost_invoked_sound` | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS |
| `ghost_received_sound` | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS |
| `in_flight_flow_compat` | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS |

## Summary

- 7 safety properties
- 12 strengthening invariants
- 9 actions verified
- 200 verification conditions total
- 200 passed, 0 failed

