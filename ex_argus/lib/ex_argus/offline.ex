defmodule ExArgus.Offline do
  @moduledoc """
  Pure functional, state-passing interface to the verified argus-kernel.

  **Offline use only** -- replay, shadow evaluation, property tests, and `explain` over a
  state snapshot. NEVER use this for live authorization: live callers must use
  `ExArgus.Instance`, which keeps the only mutable copy of the state inside the verified
  NIF resource. The caller here owns the state term, which makes out-of-reachable-space
  state construction representable -- exactly the hazard `ExArgus.Instance` removes.

  Each function returns `{:ok, new_state, action}` or `{:error, reason}`. Oracle verdicts
  for the oracle-consuming transitions are passed in: `invoke_start` takes a boolean
  authorizer verdict plus the invocation's attested egress kinds, `invoke_complete` and
  `return_endorsed` take a boolean conformance verdict (`return_endorsed` also takes the
  declared `clvl`/`ilvl` levels), and the gate-consuming transitions take a
  `%{invocation_id => boolean}` content-gate decision map. Use `content_gate_targets/2` or
  `content_gate_map/3` to compute exactly which invocations need a verdict.
  """

  alias ExArgus.Kernel.State
  alias ExArgus.Kernel.Types
  alias ExArgus.Native

  @type state :: State.t()
  @type background :: ExArgus.Kernel.Background.t()
  @type id :: String.t()

  @typedoc """
  A kernel-transition denial. Each variant names a precondition class and carries no
  payload -- human-readable diagnostics belong in the (unverified) adapter, not the
  verified kernel. This is the closed set a caller can rely on as a contract (e.g. to map
  to deny-telemetry).

  Keep it in sync with `KernelError` in `argus-kernel/src/error.rs`, which is the single
  source of truth; the NIF crosses each variant as the snake_case atom below.

  | Atom | Precondition class |
  | ---- | ------------------ |
  | `:tool_not_in_theory` | Tool has no metadata in the background theory. |
  | `:tool_already_registered` | Tool is already registered. |
  | `:tool_not_registered` | Tool is not registered. |
  | `:untrusted_issuer` | Issuer (of a tool or instruction) is not trusted. |
  | `:instruction_issuer_unknown` | Instruction has no registered issuer in the background theory. |
  | `:agent_inactive` | Named agent (actor / grantor / parent / child / target) is not active. |
  | `:agent_already_active` | Grantee is already active. |
  | `:root_not_allowed` | The operation may not target / be performed by the root agent. |
  | `:not_direct_child` | The agent is not a direct child of the named parent. |
  | `:parent_still_active` | Parent is still active (use `revoke`, not `cascade_revoke`). |
  | `:capability_missing` | A required capability is missing (required tool cap / declassify / credit-budget). |
  | `:invocation_exists` | An invocation with this id already exists. |
  | `:invocation_in_flight` | The invocation is already in-flight. |
  | `:not_in_flight` | The invocation is not in-flight for the agent. |
  | `:child_has_in_flight` | The child still has in-flight invocations. |
  | `:target_has_in_flight` | The grant target still has in-flight invocations (re-arm guard). |
  | `:flow_gate_blocked` | A flow-policy gate blocked the (level, egress) pair. |
  | `:authorizer_denied` | The authorizer denied the (agent, tool) pair. |
  | `:not_conforming` | A cross-boundary endorsed return failed the runtime conformance oracle. |
  | `:budget_exhausted` | The declassification budget is exhausted. |
  | `:missing_tool_binding` | An in-flight invocation has no tool binding. |
  | `:invocation_replayed` | This invocation id has been used before (freshness). |
  | `:attestation_invalid` | The attested egress is not a subset of the tool's declared egress, or an egress-bearing tool was attested empty (narrowing/coverage). |
  | `:integrity_floor_denied` | The dual integrity gate (CHECK 4a/4b/4c) denied on a below-floor level. |
  | `:lever_integrity_denied` | The declassifying child's held integrity is below the shared lever floor. |
  | `:declaration_not_covering` | The `return_endorsed` declared `(clvl, ilvl)` does not bound the child's held taint/integrity sets. |
  | `:tool_in_flight` | The tool has an in-flight invocation (blocks `unregister_tool`). |
  | `:event_store` | The event store failed to persist an event. |
  | `:state_version_mismatch` | Binding-level: an event log or state snapshot is not stamped for the current `ExArgus.state_version/0` (see `ExArgus.Instance.recover/2`). |
  """
  @type error_reason ::
          :tool_not_in_theory
          | :tool_already_registered
          | :tool_not_registered
          | :untrusted_issuer
          | :instruction_issuer_unknown
          | :agent_inactive
          | :agent_already_active
          | :root_not_allowed
          | :not_direct_child
          | :parent_still_active
          | :capability_missing
          | :invocation_exists
          | :invocation_in_flight
          | :not_in_flight
          | :child_has_in_flight
          | :target_has_in_flight
          | :flow_gate_blocked
          | :authorizer_denied
          | :not_conforming
          | :budget_exhausted
          | :missing_tool_binding
          | :invocation_replayed
          | :attestation_invalid
          | :integrity_floor_denied
          | :lever_integrity_denied
          | :declaration_not_covering
          | :tool_in_flight
          | :event_store
          | :state_version_mismatch

  @type outcome :: {:ok, state, tuple} | {:error, error_reason}

  defdelegate initial_state(), to: Native
  defdelegate register_tool(state, bg, tool), to: Native
  defdelegate unregister_tool(state, bg, tool), to: Native
  defdelegate load_instruction(state, bg, agent, instr), to: Native
  defdelegate delegate(state, bg, grantor, grantee), to: Native
  defdelegate grant_capability(state, bg, parent, child, cap), to: Native
  defdelegate revoke(state, bg, parent, target), to: Native
  defdelegate cascade_revoke(state, bg, child, parent), to: Native
  defdelegate sentinel_credit_budget(state, bg, agent, amount), to: Native
  defdelegate grant_override(state, bg, granter, target, tool, level), to: Native

  @doc """
  Cross-boundary endorsed return, declaring the confidentiality/integrity levels `clvl`/`ilvl`
  the parent accepts responsibility for; debits the parent's budget by
  `declass_weight(clvl) + integ_weight(ilvl)`.
  """
  defdelegate return_endorsed(state, bg, child, parent, return_conforms, clvl, ilvl), to: Native

  @doc """
  Starts an invocation. `attested_egress` is the egress kinds this call actually attests to
  (narrowing: must be a subset of the tool's declared egress; coverage: an egress-bearing
  tool cannot be admitted on an empty attestation).

  A reused invocation id surfaces `:invocation_exists`, not `:invocation_replayed`: the
  invocation-tool binding check fires first because `invocation_tool` persists.
  `:invocation_replayed` is reachable at the transition level (an id present in
  `invocation_used` but absent from `invocation_tool`). Replay is denied either way; a
  reused id through `ExArgus.Instance` observes `:invocation_exists` (design §6).
  """
  defdelegate invoke_start(
                state,
                bg,
                agent,
                tool,
                inv,
                authorizer_allows,
                content_gate,
                attested_egress
              ),
              to: Native

  @doc """
  Convenience arity threading `ExArgus.EgressAuthorizer.attest/4`'s `{authorized?, attested}`
  output directly, instead of unpacking it at each call site.
  """
  @spec invoke_start(state, background, id, id, id, {boolean, [Types.egress_kind()]}, map) ::
          outcome
  def invoke_start(state, bg, agent, tool, inv, {authorized?, attested_egress}, content_gate) do
    Native.invoke_start(state, bg, agent, tool, inv, authorized?, content_gate, attested_egress)
  end

  defdelegate invoke_complete(state, bg, agent, inv, conformance_conforms), to: Native
  defdelegate return_unendorsed(state, bg, child, parent, content_gate), to: Native
  defdelegate sentinel_elevate_taint(state, bg, agent, level, content_gate), to: Native
  defdelegate sentinel_degrade_integrity(state, bg, agent, level, content_gate), to: Native

  @doc """
  The `{agent, invocations}` the content gate will be queried for, for a gate-consuming
  action. The agent is fixed; only the invocation id varies -- the same tool can be in
  flight at multiple invocations with different vouches simultaneously, so the gate is keyed
  by invocation id, never by tool. Returns `{agent, [invocation_id]}`.
  """
  @spec content_gate_targets(state, tuple) :: {id, [id]}
  def content_gate_targets(%State{} = s, {:invoke_start, agent, _tool, inv}) do
    {agent, [inv | in_flight_invs(s, agent)]}
  end

  def content_gate_targets(%State{} = s, {:return_unendorsed, _child, parent}) do
    {parent, in_flight_invs(s, parent)}
  end

  def content_gate_targets(%State{} = s, {:sentinel_elevate_taint, agent, _level}) do
    {agent, in_flight_invs(s, agent)}
  end

  def content_gate_targets(%State{} = s, {:sentinel_degrade_integrity, agent, _level}) do
    {agent, in_flight_invs(s, agent)}
  end

  @doc """
  Build the `%{invocation_id => boolean}` content-gate map for an action by evaluating
  `fun.(agent, invocation_id)` over `content_gate_targets/2`.
  """
  @spec content_gate_map(state, tuple, (id, id -> boolean)) :: %{id => boolean}
  def content_gate_map(%State{} = s, action, fun) when is_function(fun, 2) do
    {agent, invs} = content_gate_targets(s, action)
    Map.new(invs, fn inv -> {inv, fun.(agent, inv)} end)
  end

  defp in_flight_invs(%State{} = s, agent), do: Map.get(s.in_flight, agent, [])
end
