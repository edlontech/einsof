defmodule ExArgus.ErrorReasonTest do
  @moduledoc """
  Locks the deny-atom contract: the documented closed set must match
  `ExArgus.Offline.error_reason/0`, and the atoms the NIF actually emits on the wire must
  be members of it.
  """
  use ExUnit.Case, async: true

  alias ExArgus.Kernel.Background
  alias ExArgus.Native

  # The closed set of kernel-transition denials, mirrored from argus-kernel/src/error.rs
  # (the `KernelError` enum, the single source of truth). Keep in sync with that enum.
  @error_reasons ~w(
    tool_not_in_theory tool_already_registered tool_not_registered
    untrusted_issuer instruction_issuer_unknown
    agent_inactive agent_already_active root_not_allowed
    not_direct_child parent_still_active
    capability_missing
    invocation_exists invocation_in_flight not_in_flight child_has_in_flight
    flow_gate_blocked authorizer_denied budget_exhausted
    missing_tool_binding event_store
  )a

  defp bg do
    %Background{
      tools: %{
        "read_file" => %{
          capabilities: [:filesystem_read],
          egress: [],
          conf_floor: :sensitive,
          output_bounded: false,
          issuer: "trusted"
        },
        "send_email" => %{
          capabilities: [:network_egress],
          egress: [:network_external],
          conf_floor: :public,
          output_bounded: false,
          issuer: "trusted"
        },
        "evil_tool" => %{
          capabilities: [],
          egress: [],
          conf_floor: :public,
          output_bounded: false,
          issuer: "untrusted"
        }
      },
      flow_policy: %{{:public, :network_external} => :allow},
      flow_overrides: [],
      trusted_issuers: ["trusted"],
      instruction_issuer: %{}
    }
  end

  describe "the error_reason contract" do
    test "documents exactly 20 denial atoms" do
      assert length(@error_reasons) == 20
      assert length(Enum.uniq(@error_reasons)) == 20
    end

    test "ExArgus.Offline.error_reason/0 declares exactly the documented closed set" do
      assert declared_error_reasons() == Enum.sort(@error_reasons)
    end
  end

  describe "the NIF emits the documented atoms on the wire" do
    test "tool_not_in_theory: registering a tool absent from the theory" do
      assert {:error, reason} = Native.register_tool(Native.initial_state(), bg(), "ghost")
      assert reason == :tool_not_in_theory
      assert reason in @error_reasons
    end

    test "untrusted_issuer: registering a tool whose issuer is not trusted" do
      assert {:error, :untrusted_issuer} =
               Native.register_tool(Native.initial_state(), bg(), "evil_tool")
    end

    test "tool_already_registered: registering the same tool twice" do
      {:ok, s1, _} = Native.register_tool(Native.initial_state(), bg(), "read_file")
      assert {:error, :tool_already_registered} = Native.register_tool(s1, bg(), "read_file")
    end

    test "agent_inactive: delegating from an inactive grantor" do
      assert {:error, :agent_inactive} =
               Native.delegate(Native.initial_state(), bg(), "ghost", "child")
    end

    test "agent_already_active: delegating to an already-active grantee" do
      assert {:error, :agent_already_active} =
               Native.delegate(Native.initial_state(), bg(), "root", "root")
    end

    test "root_not_allowed: the root agent may not invoke a tool" do
      assert {:error, :root_not_allowed} =
               Native.invoke_start(
                 Native.initial_state(),
                 bg(),
                 "root",
                 "read_file",
                 "i",
                 true,
                 %{}
               )
    end

    test "not_direct_child: revoking an agent that is not a direct child" do
      assert {:error, :not_direct_child} =
               Native.revoke(Native.initial_state(), bg(), "root", "stranger")
    end

    test "instruction_issuer_unknown: loading an instruction with no registered issuer" do
      assert {:error, :instruction_issuer_unknown} =
               Native.load_instruction(Native.initial_state(), bg(), "root", "unknown-instr")
    end

    test "tool_not_registered: invoking a tool that is in theory but not registered" do
      {:ok, s1, _} = Native.delegate(Native.initial_state(), bg(), "root", "a1")

      assert {:error, :tool_not_registered} =
               Native.invoke_start(s1, bg(), "a1", "read_file", "i", true, %{})
    end

    test "capability_missing: refreshing budget without the refresh-budget capability" do
      {:ok, s1, _} = Native.delegate(Native.initial_state(), bg(), "root", "a1")
      assert {:error, :capability_missing} = Native.sentinel_refresh_budget(s1, bg(), "a1")
    end

    test "not_in_flight: completing an invocation that is not in flight" do
      assert {:error, :not_in_flight} =
               Native.invoke_complete(Native.initial_state(), bg(), "root", "ghost-inv", true)
    end

    test "invocation_exists: re-using an invocation id" do
      s = authorized_agent_state()

      {:ok, s, _} =
        Native.invoke_start(s, bg(), "a1", "read_file", "inv-1", true, %{"read_file" => true})

      assert {:error, :invocation_exists} =
               Native.invoke_start(s, bg(), "a1", "read_file", "inv-1", true, %{
                 "read_file" => true
               })
    end

    test "authorizer_denied: invoke_start with a denying authorizer" do
      s = authorized_agent_state()

      assert {:error, :authorizer_denied} =
               Native.invoke_start(s, bg(), "a1", "read_file", "inv-1", false, %{
                 "read_file" => true
               })
    end

    test "parent_still_active: cascade_revoke under a still-active parent" do
      {:ok, s1, _} = Native.delegate(Native.initial_state(), bg(), "root", "p")
      {:ok, s2, _} = Native.delegate(s1, bg(), "p", "c")
      assert {:error, :parent_still_active} = Native.cascade_revoke(s2, bg(), "c", "p")
    end

    test "child_has_in_flight: returning while the child still has an in-flight invocation" do
      s = authorized_agent_state()

      {:ok, s, _} =
        Native.invoke_start(s, bg(), "a1", "read_file", "inv-1", true, %{"read_file" => true})

      assert {:error, :child_has_in_flight} = Native.return_unendorsed(s, bg(), "a1", "root", %{})
    end

    test "flow_gate_blocked: a tainted agent's egress is denied by the flow gate" do
      s = authorized_agent_state()
      {:ok, s, _} = Native.grant_capability(s, bg(), "root", "a1", :network_egress)
      {:ok, s, _} = Native.register_tool(s, bg(), "send_email")

      # Complete a non-bounded, non-conforming read => a1 is tainted at :sensitive.
      {:ok, s, _} =
        Native.invoke_start(s, bg(), "a1", "read_file", "inv-r", true, %{"read_file" => true})

      {:ok, s, _} = Native.invoke_complete(s, bg(), "a1", "inv-r", false)

      # Sensitive egress to network_external is DENY (default), so the gate blocks send_email.
      assert {:error, :flow_gate_blocked} =
               Native.invoke_start(s, bg(), "a1", "send_email", "inv-e", true, %{
                 "send_email" => false
               })
    end
  end

  # An active non-root agent "a1" (child of root) registered for and capable of "read_file".
  defp authorized_agent_state do
    {:ok, s1, _} = Native.register_tool(Native.initial_state(), bg(), "read_file")
    {:ok, s2, _} = Native.delegate(s1, bg(), "root", "a1")
    {:ok, s3, _} = Native.grant_capability(s2, bg(), "root", "a1", :filesystem_read)
    s3
  end

  # The atom literals in the `@type error_reason :: ...` union, read back from the compiled
  # module so the test fails if the declared type drifts from the documented closed set.
  defp declared_error_reasons do
    {:ok, types} = Code.Typespec.fetch_types(ExArgus.Offline)

    {:type, {:error_reason, definition, []}} =
      Enum.find(types, fn {:type, {name, _def, _args}} -> name == :error_reason end)

    definition |> union_atoms() |> Enum.sort()
  end

  defp union_atoms({:type, _, :union, members}), do: Enum.flat_map(members, &union_atoms/1)
  defp union_atoms({:atom, _, atom}), do: [atom]
end
