defmodule ExArgus.LifecycleTest do
  use ExUnit.Case, async: true

  alias ExArgus.Offline
  alias ExArgus.Kernel.Background

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
      flow_policy: %{{:public, :network_external} => :allow},
      flow_overrides: [],
      trusted_issuers: ["trusted"],
      instruction_issuer: %{}
    }
  end

  test "register -> delegate -> grant -> invoke -> complete -> return -> revoke" do
    bg = bg()
    s = Offline.initial_state()

    {:ok, s, {:register_tool, "read_file"}} = Offline.register_tool(s, bg, "read_file")
    {:ok, s, {:delegate, "root", "a1"}} = Offline.delegate(s, bg, "root", "a1")
    {:ok, s, _} = Offline.grant_capability(s, bg, "root", "a1", :filesystem_read)
    {:ok, s, _} = Offline.grant_capability(s, bg, "root", "a1", :declassify)

    {:ok, s, _} =
      Offline.invoke_start(s, bg, "a1", "read_file", "inv-1", true, %{"read_file" => true})

    {:ok, s, _} = Offline.invoke_complete(s, bg, "a1", "inv-1", true)
    # bounded=false => not the zero-taint path => taint at the tool floor
    assert :sensitive in Map.fetch!(s.taint_levels, "a1")

    {:ok, s, {:return_endorsed, "a1", "root"}} = Offline.return_endorsed(s, bg, "a1", "root")
    {:ok, s, {:revoke, "root", "a1"}} = Offline.revoke(s, bg, "root", "a1")

    refute "a1" in s.agent_active
  end
end
