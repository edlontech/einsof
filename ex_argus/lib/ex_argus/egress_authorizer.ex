defmodule ExArgus.EgressAuthorizer do
  @moduledoc """
  Computes the `{authorized?, attested_kinds}` pair `ExArgus.Offline.invoke_start/8` (or its
  `attest/4`-aware convenience arity) consumes, from the per-call arguments and an
  `ExArgus.EgressPolicy`.

  The verified kernel's authorizer hook is consulted with `(agent, tool, state, bg)` only --
  it cannot see a per-call argument like a URL, and it never sees a URL at all (uninterpreted
  egress kinds only). So URL classification is computed here, at the call site where the
  tool-call arguments are in hand: a `false` authorized? folds into `:authorizer_denied`
  (CHECK 3), and the attested kinds feed the kernel's narrowing/coverage check, both
  fail-closed.

  URL-bearing call args (`:url` or `:urls`) classify per URL against the agent's rules and
  union the results; any denied URL denies the whole call with an empty attestation -- the
  adapter never trims the union down to the declared set, so an over-wide union surfaces as
  the kernel's `:attestation_invalid`, not a silently narrowed pass. Call args with no URL
  dimension attest `declared_egress` as-is (the tool's declared egress set from the
  background -- V2's static worst case, still sound, just less precise); `authorized?`
  follows the prior permissive default for this case.

  Compose with any base authorizer by `and`-ing the verdicts: a call is admitted iff every
  authorizer admits it.

      {allow, attested} =
        EgressAuthorizer.attest(policy, agent, declared_egress, call_args)

      allow = base_authorizer?(agent, tool, state, bg) and allow

      ExArgus.Instance.invoke_start(handle, agent, tool, inv, allow, content_gate, attested)
  """

  alias ExArgus.EgressPolicy
  alias ExArgus.Kernel.Types

  @doc """
  `{authorized?, attested_kinds}` for one tool call. See the moduledoc for the per-shape
  semantics of `call_args`.
  """
  @spec attest(EgressPolicy.policy(), String.t(), [Types.egress_kind()], map) ::
          {boolean, [Types.egress_kind()]}
  def attest(policy, agent, _declared_egress, %{url: url}) when is_binary(url) do
    classify_union(policy, agent, [url])
  end

  def attest(policy, agent, _declared_egress, %{urls: urls}) when is_list(urls) do
    classify_union(policy, agent, urls)
  end

  def attest(_policy, _agent, declared_egress, _call_args), do: {true, declared_egress}

  defp classify_union(policy, agent, urls) do
    rules = Map.get(policy, agent, [])

    urls
    |> Enum.reduce_while({:ok, []}, fn url, {:ok, acc} ->
      case EgressPolicy.classify(rules, url) do
        {:ok, kinds} -> {:cont, {:ok, Enum.uniq(acc ++ kinds)}}
        :deny -> {:halt, :deny}
      end
    end)
    |> case do
      {:ok, kinds} -> {true, kinds}
      :deny -> {false, []}
    end
  end
end
