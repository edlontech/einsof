defmodule ExArgus.Shadow.InstanceTest do
  use ExUnit.Case, async: true

  alias ExArgus.Instance
  alias ExArgus.Kernel.Background
  alias ExArgus.Shadow

  defp bg(allow_ceiling, opts \\ []) do
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
      trusted_issuers: Keyword.get(opts, :trusted_issuers, ["trusted"]),
      instruction_issuer: %{}
    }
  end

  defp setup_entries do
    [
      {:register_tool, ["send_email"]},
      {:delegate, ["root", "a1"]},
      {:grant_capability, ["root", "a1", :network_egress]},
      {:sentinel_elevate_taint, ["a1", :sensitive, %{}]}
    ]
  end

  defp thread(handle, entries) do
    Enum.each(entries, fn {fun, args} ->
      assert %{live: {:ok, _, _}} = Shadow.Instance.apply(handle, fun, args)
    end)

    handle
  end

  test "tightening candidate flips exactly the egress invoke, with a report" do
    h = Shadow.Instance.new(bg(%{network_external: :sensitive}), bg(%{network_external: :public}))
    thread(h, setup_entries())

    result =
      Shadow.Instance.invoke_start(h, "a1", "send_email", "i1", true, %{}, [:network_external])

    assert {:ok, seq, {:invoke_start, "a1", "send_email", "i1"}} = result.live
    assert result.candidate == {:deny, :flow_gate_blocked}
    assert result.report.verdict == :flow_gate_blocked
    assert ExArgus.Explain.denied?(result.report)

    assert Shadow.Instance.seq(h) == seq
    assert "i1" in Map.fetch!(Shadow.Instance.state(h).in_flight, "a1")
  end

  test "loosening candidate reports a deny -> allow divergence without advancing state" do
    h = Shadow.Instance.new(bg(%{network_external: :public}), bg(%{network_external: :sensitive}))
    thread(h, setup_entries())
    before = Shadow.Instance.state(h)

    result =
      Shadow.Instance.invoke_start(h, "a1", "send_email", "i1", true, %{}, [:network_external])

    assert result.live == {:error, :flow_gate_blocked}
    assert result.candidate == :allow
    assert result.report.verdict == nil
    refute ExArgus.Explain.denied?(result.report)

    assert Shadow.Instance.state(h) == before
  end

  test "identical backgrounds agree on every transition with nil reports" do
    live = bg(%{network_external: :sensitive})
    h = Shadow.Instance.new(live, live)

    entries =
      setup_entries() ++
        [
          {:invoke_start, ["a1", "send_email", "i1", true, %{}, [:network_external]]},
          {:invoke_complete, ["a1", "i1", true]}
        ]

    for {fun, args} <- entries do
      result = Shadow.Instance.apply(h, fun, args)
      assert %{live: {:ok, _, _}, candidate: :allow, report: nil} = result
    end

    dup = Shadow.Instance.apply(h, :register_tool, ["send_email"])
    assert dup.live == {:error, :tool_already_registered}
    assert dup.candidate == {:deny, :tool_already_registered}
    assert dup.report == nil
  end

  test "issuer-shrinking candidate flips register_tool via the verdict, report stays nil" do
    h =
      Shadow.Instance.new(
        bg(%{network_external: :public}),
        bg(%{network_external: :public}, trusted_issuers: [])
      )

    result = Shadow.Instance.apply(h, :register_tool, ["send_email"])
    assert {:ok, 1, _} = result.live
    assert result.candidate == {:deny, :untrusted_issuer}
    assert result.report == nil
  end

  test "apply/3 refuses an unknown transition without touching the instance" do
    h = Shadow.Instance.new(bg(%{}), bg(%{}))
    assert Shadow.Instance.apply(h, :not_a_transition, []) == {:error, :unknown_transition}
    assert Shadow.Instance.seq(h) == 0
  end

  test "recover/3 replays a logged trajectory to the same projection as Instance.recover" do
    live = bg(%{network_external: :sensitive})
    candidate = bg(%{network_external: :public})

    log =
      setup_entries() ++
        [{:invoke_start, ["a1", "send_email", "i1", true, %{}, [:network_external]]}]

    assert {:ok, h} = Shadow.Instance.recover(live, candidate, [ExArgus.log_header() | log])
    assert {:ok, plain} = Instance.recover(live, [ExArgus.log_header() | log])

    assert Shadow.Instance.state(h) == Instance.state(plain)
    assert Shadow.Instance.seq(h) == length(log)
  end

  test "recover/3 aborts strictly on header mismatch and on live refusal" do
    live = bg(%{network_external: :sensitive})

    assert {:error, %{index: 0, reason: :state_version_mismatch}} =
             Shadow.Instance.recover(live, live, [{:register_tool, ["send_email"]}])

    bad_log = [ExArgus.log_header(), {:delegate, ["ghost", "a1"]}]

    assert {:error, %{index: 0, entry: {:delegate, _}, reason: :agent_inactive}} =
             Shadow.Instance.recover(live, live, bad_log)
  end
end
