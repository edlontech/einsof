defmodule ExArgus.Kernel do
  @moduledoc """
  Pure functional interface to the verified argus-kernel.

  The caller owns the state, the event log, and the oracle implementations. Each function
  returns `{:ok, new_state, action}` or `{:error, reason}`. Oracle verdicts for the three
  oracle-consuming transitions are passed in: `invoke_start` and `invoke_complete` take a
  boolean authorizer/conformance verdict, and the gate-consuming transitions take a
  `%{tool => boolean}` content-gate decision map. Use `content_gate_targets/2` or
  `content_gate_map/3` to compute exactly which tools need a verdict.
  """

  alias ExArgus.Kernel.State
  alias ExArgus.Native

  @type state :: State.t()
  @type background :: ExArgus.Kernel.Background.t()
  @type id :: String.t()
  @type outcome :: {:ok, state, tuple} | {:error, atom}

  defdelegate initial_state(), to: Native
  defdelegate register_tool(state, bg, tool), to: Native
  defdelegate load_instruction(state, bg, agent, instr), to: Native
  defdelegate delegate(state, bg, grantor, grantee), to: Native
  defdelegate grant_capability(state, bg, parent, child, cap), to: Native
  defdelegate revoke(state, bg, parent, target), to: Native
  defdelegate cascade_revoke(state, bg, child, parent), to: Native
  defdelegate return_endorsed(state, bg, child, parent), to: Native
  defdelegate sentinel_refresh_budget(state, bg, agent), to: Native

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
