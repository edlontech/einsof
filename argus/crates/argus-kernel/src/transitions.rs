//! TzimtzumV4 pure transitions — the Charon/Aeneas extraction entry points.
//!
//! Each of the 12 V4 actions (`register_tool`, `unregister_tool`, `delegate`, `grant_capability`,
//! `grant_crossing`, `revoke`, `cascade_revoke`, `ingest`, `begin_invocation`,
//! `authorize_inspected`, `settle_invocation`, `cross_output`) is a pure
//! `fn(KernelState, &BackgroundTheory, ...) -> Result<(KernelState, KernelAction), KernelError>`.
//!
//! They are added by Tasks A2–A5. All traversals here MUST follow the §13 extraction discipline:
//! Vec-backed collections only, explicit index `while` loops, no closures, no early `return` in
//! loops, owned accessors only.
