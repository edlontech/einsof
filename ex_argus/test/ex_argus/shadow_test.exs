defmodule ExArgus.ShadowTest do
  use ExUnit.Case, async: true

  alias ExArgus.{Offline, Shadow}
  alias ExArgus.Kernel.Background

  defp bg(flow_policy) do
    %Background{
      tools: %{
        "send_email" => %{
          capabilities: [:network_egress],
          egress: [:network_external],
          conf_floor: :public,
          output_bounded: false,
          issuer: "trusted"
        }
      },
      flow_policy: flow_policy,
      flow_overrides: [],
      trusted_issuers: ["trusted"],
      instruction_issuer: %{}
    }
  end

  defp tainted_state(bg) do
    state = Offline.initial_state()
    {:ok, state, _} = Offline.register_tool(state, bg, "send_email")
    {:ok, state, _} = Offline.delegate(state, bg, "root", "a1")
    {:ok, state, _} = Offline.grant_capability(state, bg, "root", "a1", :network_egress)
    {:ok, state, _} = Offline.sentinel_elevate_taint(state, bg, "a1", :sensitive, %{})
    state
  end

  test "diverging candidate policy is reported" do
    live_bg = bg(%{{:public, :network_external} => :allow})

    candidate_bg =
      bg(%{
        {:public, :network_external} => :allow,
        {:sensitive, :network_external} => :allow
      })

    state = tainted_state(live_bg)

    result =
      Shadow.compare(live_bg, candidate_bg, fn b ->
        Offline.invoke_start(state, b, "a1", "send_email", "i1", true, %{})
      end)

    assert {:error, :flow_gate_blocked} = result.live
    assert {:ok, _, _} = result.candidate
    assert result.decision == :diverged
  end

  test "identical policies agree" do
    live_bg = bg(%{{:public, :network_external} => :allow})
    state = tainted_state(live_bg)

    result =
      Shadow.compare(live_bg, live_bg, fn b ->
        Offline.invoke_start(state, b, "a1", "send_email", "i1", true, %{})
      end)

    assert result.decision == :same
  end
end
