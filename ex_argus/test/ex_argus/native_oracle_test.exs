defmodule ExArgus.NativeOracleTest do
  use ExUnit.Case, async: true

  alias ExArgus.Kernel.Background
  alias ExArgus.Native

  # A tool with no egress: the content gate is never consulted (the egress loops are empty).
  defp bg do
    %Background{
      tools: %{
        "read_file" => %{
          capabilities: [:filesystem_read],
          egress: [],
          conf_floor: :sensitive,
          output_bounded: false,
          issuer: "trusted"
        }
      },
      allow_ceiling: %{},
      inspect_ceiling: %{},
      trusted_issuers: ["trusted"],
      instruction_issuer: %{}
    }
  end

  test "invoke_start succeeds for an authorized, capable agent" do
    bg = bg()
    s0 = Native.initial_state()
    {:ok, s1, _} = Native.register_tool(s0, bg, "read_file")
    {:ok, s2, _} = Native.delegate(s1, bg, "root", "a1")
    {:ok, s3, _} = Native.grant_capability(s2, bg, "root", "a1", :filesystem_read)

    assert {:ok, s4, {:invoke_start, "a1", "read_file", "inv-1"}} =
             Native.invoke_start(s3, bg, "a1", "read_file", "inv-1", true, %{"read_file" => true})

    assert "inv-1" in Map.fetch!(s4.in_flight, "a1")
    assert Map.fetch!(s4.invocation_tool, "inv-1") == "read_file"
  end

  test "invoke_start denied by the authorizer" do
    bg = bg()
    s0 = Native.initial_state()
    {:ok, s1, _} = Native.register_tool(s0, bg, "read_file")
    {:ok, s2, _} = Native.delegate(s1, bg, "root", "a1")
    {:ok, s3, _} = Native.grant_capability(s2, bg, "root", "a1", :filesystem_read)

    assert {:error, :authorizer_denied} =
             Native.invoke_start(s3, bg, "a1", "read_file", "inv-1", false, %{"read_file" => true})
  end

  test "invoke_complete on a non-conforming non-bounded tool adds taint" do
    bg = bg()
    s0 = Native.initial_state()
    {:ok, s1, _} = Native.register_tool(s0, bg, "read_file")
    {:ok, s2, _} = Native.delegate(s1, bg, "root", "a1")
    {:ok, s3, _} = Native.grant_capability(s2, bg, "root", "a1", :filesystem_read)

    {:ok, s4, _} =
      Native.invoke_start(s3, bg, "a1", "read_file", "inv-1", true, %{"read_file" => true})

    assert {:ok, s5, {:invoke_complete, "a1", "inv-1"}} =
             Native.invoke_complete(s4, bg, "a1", "inv-1", false)

    assert :sensitive in Map.fetch!(s5.taint_levels, "a1")
    refute "inv-1" in Map.get(s5.in_flight, "a1", [])
  end
end
