defmodule ExArgus.ReplayTest do
  use ExUnit.Case, async: true

  alias ExArgus.Replay
  alias ExArgus.Kernel.Background

  defp bg(allow_ceiling) do
    %Background{
      tools: %{
        "send_email" => %{
          capabilities: [:network_egress],
          egress: [:network_external],
          conf_floor: :public,
          output_bounded: false,
          issuer: "trusted",
          integ_floor: :untrusted,
          integ_inspect_floor: :untrusted,
          output_integ: :attested
        }
      },
      allow_ceiling: allow_ceiling,
      inspect_ceiling: %{},
      trusted_issuers: ["trusted"],
      instruction_issuer: %{}
    }
  end

  @log [
    {:register_tool, ["send_email"]},
    {:delegate, ["root", "a1"]},
    {:grant_capability, ["root", "a1", :network_egress]},
    {:sentinel_elevate_taint, ["a1", :sensitive, %{}]},
    {:invoke_start, ["a1", "send_email", "i1", true, %{}, [:network_external]]}
  ]

  test "run returns one outcome per entry and threads state through" do
    outcomes = Replay.run([ExArgus.log_header() | @log], bg(%{network_external: :public}))
    assert length(outcomes) == 5

    assert [{:ok, _, _}, {:ok, _, _}, {:ok, _, _}, {:ok, _, _}, {:error, :flow_gate_blocked}] =
             outcomes
  end

  test "errors do not halt the replay" do
    log = [{:register_tool, ["send_email"]} | @log]
    outcomes = Replay.run([ExArgus.log_header() | log], bg(%{network_external: :public}))
    assert [{:ok, _, _}, {:error, :tool_already_registered} | _] = outcomes
    assert length(outcomes) == 6
  end

  test "diff pinpoints the diverging entries" do
    live = bg(%{network_external: :public})
    candidate = bg(%{network_external: :sensitive})

    divergences = Replay.diff([ExArgus.log_header() | @log], live, candidate)

    assert [
             %{
               index: 4,
               entry: {:invoke_start, _},
               live: {:error, :flow_gate_blocked},
               candidate: {:ok, _, _}
             }
           ] = divergences
  end

  test "identical backgrounds produce no divergences" do
    live = bg(%{network_external: :public})
    assert Replay.diff([ExArgus.log_header() | @log], live, live) == []
  end

  test "run rejects a headerless log without replaying any entry" do
    assert Replay.run(@log, bg(%{network_external: :public})) == {:error, :state_version_mismatch}
  end

  test "run rejects a log stamped for a prior state version" do
    log = [{:state_version, 3} | @log]
    assert Replay.run(log, bg(%{network_external: :public})) == {:error, :state_version_mismatch}
  end

  test "diff rejects a headerless log" do
    live = bg(%{network_external: :public})
    assert Replay.diff(@log, live, live) == {:error, :state_version_mismatch}
  end

  test "diff rejects a log stamped for a prior state version" do
    live = bg(%{network_external: :public})
    log = [{:state_version, 3} | @log]
    assert Replay.diff(log, live, live) == {:error, :state_version_mismatch}
  end

  test "run rejects a log stamped with a float version, not just a numerically-equal integer" do
    log = [{:state_version, 4.0} | @log]

    assert Replay.run(log, bg(%{network_external: :public})) ==
             {:error, :state_version_mismatch}
  end

  test "run replays stamped-4 logs containing unregister_tool and sentinel_degrade_integrity" do
    log = [
      ExArgus.log_header(),
      {:register_tool, ["send_email"]},
      {:delegate, ["root", "a1"]},
      {:sentinel_degrade_integrity, ["a1", :standard, %{}]},
      {:unregister_tool, ["send_email"]}
    ]

    outcomes = Replay.run(log, bg(%{network_external: :public}))

    assert [{:ok, _, _}, {:ok, _, _}, {:ok, _, _}, {:ok, _, _}] = outcomes
  end
end
