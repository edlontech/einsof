defmodule ExArgus.NativeBasicTest do
  use ExUnit.Case, async: true

  alias ExArgus.Kernel.Background
  alias ExArgus.Native

  defp trusted_bg do
    %Background{
      tools: %{
        "t" => %{
          capabilities: [],
          egress: [],
          conf_floor: :public,
          output_bounded: true,
          issuer: "trusted",
          integ_floor: :untrusted,
          integ_inspect_floor: :untrusted,
          output_integ: :attested
        }
      },
      allow_ceiling: %{},
      inspect_ceiling: %{},
      trusted_issuers: ["trusted"],
      instruction_issuer: %{}
    }
  end

  test "initial_state has root active with a full cap set" do
    s = Native.initial_state()
    assert "root" in s.agent_active
    assert length(Map.fetch!(s.agent_cap, "root")) == 18
    assert :declassify in Map.fetch!(s.agent_cap, "root")
  end

  test "register_tool then delegate" do
    s0 = Native.initial_state()
    bg = trusted_bg()

    assert {:ok, s1, {:register_tool, "t"}} = Native.register_tool(s0, bg, "t")
    assert "t" in s1.tool_registered

    assert {:ok, s2, {:delegate, "root", "a1"}} = Native.delegate(s1, bg, "root", "a1")
    assert "a1" in s2.agent_active
    assert Map.fetch!(s2.agent_parent, "a1") == "root"
  end

  test "errors surface as {:error, atom}" do
    s0 = Native.initial_state()
    bg = trusted_bg()
    assert {:error, :tool_not_in_theory} = Native.register_tool(s0, bg, "unknown")
  end
end
