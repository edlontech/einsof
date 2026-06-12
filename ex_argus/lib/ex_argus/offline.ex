defmodule ExArgus.Offline do
  @moduledoc """
  Pure functional, state-passing interface to the verified argus-kernel.

  **Offline use only** -- replay, shadow evaluation, property tests, and `explain` over a
  state snapshot. NEVER use this for live authorization: live callers must use
  `ExArgus.Instance`, which keeps the only mutable copy of the state inside the verified
  NIF resource. The caller here owns the state term, which makes out-of-reachable-space
  state construction representable -- exactly the hazard `ExArgus.Instance` removes.

  Each function returns `{:ok, new_state, action}` or `{:error, reason}`. Oracle verdicts
  for the three oracle-consuming transitions are passed in: `invoke_start` and
  `invoke_complete` take a boolean authorizer/conformance verdict, and the gate-consuming
  transitions take a `%{tool => boolean}` content-gate decision map. Use
  `content_gate_targets/2` or `content_gate_map/3` to compute exactly which tools need a
  verdict.
  """

  alias ExArgus.Kernel.State
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
  | `:capability_missing` | A required capability is missing (required tool cap / declassify / refresh-budget). |
  | `:invocation_exists` | An invocation with this id already exists. |
  | `:invocation_in_flight` | The invocation is already in-flight. |
  | `:not_in_flight` | The invocation is not in-flight for the agent. |
  | `:child_has_in_flight` | The child still has in-flight invocations. |
  | `:target_has_in_flight` | The grant target still has in-flight invocations (re-arm guard). |
  | `:flow_gate_blocked` | A flow-policy gate blocked the (level, egress) pair. |
  | `:authorizer_denied` | The authorizer denied the (agent, tool) pair. |
  | `:budget_exhausted` | The declassification budget is exhausted. |
  | `:missing_tool_binding` | An in-flight invocation has no tool binding. |
  | `:event_store` | The event store failed to persist an event. |
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
          | :budget_exhausted
          | :missing_tool_binding
          | :event_store

  @type outcome :: {:ok, state, tuple} | {:error, error_reason}

  defdelegate initial_state(), to: Native
  defdelegate register_tool(state, bg, tool), to: Native
  defdelegate load_instruction(state, bg, agent, instr), to: Native
  defdelegate delegate(state, bg, grantor, grantee), to: Native
  defdelegate grant_capability(state, bg, parent, child, cap), to: Native
  defdelegate revoke(state, bg, parent, target), to: Native
  defdelegate cascade_revoke(state, bg, child, parent), to: Native
  defdelegate return_endorsed(state, bg, child, parent), to: Native
  defdelegate sentinel_refresh_budget(state, bg, agent), to: Native
  defdelegate grant_override(state, bg, granter, target, tool, level), to: Native

  defdelegate invoke_start(state, bg, agent, tool, inv, authorizer_allows, content_gate),
    to: Native

  defdelegate invoke_complete(state, bg, agent, inv, conformance_conforms), to: Native
  defdelegate return_unendorsed(state, bg, child, parent, content_gate), to: Native
  defdelegate sentinel_elevate_taint(state, bg, agent, level, content_gate), to: Native

  @doc """
  The `{agent, tools}` the content gate will be queried for, for a gate-consuming action.
  The agent is fixed; only the tool varies. Returns `{agent, [tool]}`.
  """
  @spec content_gate_targets(state, tuple) :: {id, [id]}
  def content_gate_targets(%State{} = s, {:invoke_start, agent, tool, _inv}) do
    {agent, Enum.uniq([tool | in_flight_tools(s, agent)])}
  end

  def content_gate_targets(%State{} = s, {:return_unendorsed, _child, parent}) do
    {parent, in_flight_tools(s, parent)}
  end

  def content_gate_targets(%State{} = s, {:sentinel_elevate_taint, agent, _level}) do
    {agent, in_flight_tools(s, agent)}
  end

  @doc """
  Build the `%{tool => boolean}` content-gate map for an action by evaluating `fun.(agent, tool)`
  over `content_gate_targets/2`.
  """
  @spec content_gate_map(state, tuple, (id, id -> boolean)) :: %{id => boolean}
  def content_gate_map(%State{} = s, action, fun) when is_function(fun, 2) do
    {agent, tools} = content_gate_targets(s, action)
    Map.new(tools, fn tool -> {tool, fun.(agent, tool)} end)
  end

  defp in_flight_tools(%State{} = s, agent) do
    s.in_flight
    |> Map.get(agent, [])
    |> Enum.map(&Map.fetch!(s.invocation_tool, &1))
  end
end
