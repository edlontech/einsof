defmodule ExArgus.EgressAuthorizer do
  @moduledoc """
  Computes the `authorizer_allows` boolean for `ExArgus.Instance.invoke_start/6` from a
  per-call URL and an `ExArgus.EgressPolicy`.

  The verified kernel's authorizer hook is consulted with `(agent, tool, state, bg)` only --
  it cannot see a per-call argument like a URL. So URL/path admission is computed here, at the
  call site where the tool-call arguments are in hand, and folded into the single boolean the
  kernel consumes (CHECK 3 of `invoke_start`; a `false` => `:authorizer_denied`, fail-closed).
  This keeps the destination ACL on the unverified-but-conformance-tested side of the
  guest-model boundary; `implementation_sound` is unchanged.

  Compose with any base authorizer by `and`-ing the verdicts: a call is admitted iff every
  authorizer admits it.

      allow =
        base_authorizer?(agent, tool, state, bg) and
          ExArgus.EgressAuthorizer.admit?(policy, agent, tool, call_args)

      ExArgus.Instance.invoke_start(handle, agent, tool, inv, allow, content_gate)
  """

  alias ExArgus.EgressPolicy

  @doc """
  `true` iff the call is admissible. Tool calls that carry a binary `:url` are admitted iff
  `EgressPolicy.allows?/3` admits the URL for the agent; calls without a `:url` are not
  URL-filtered here (the kernel's capability + flow gates still govern them) and return `true`.
  """
  @spec admit?(EgressPolicy.policy(), String.t(), String.t(), map) :: boolean()
  def admit?(policy, agent, _tool, %{url: url}) when is_binary(url) do
    EgressPolicy.allows?(policy, agent, url)
  end

  def admit?(_policy, _agent, _tool, _call_args), do: true
end
