defmodule ExArgus.LifecycleTest do
  use ExUnit.Case, async: true

  alias ExArgus.{Chain, Error, Instance, Native}
  alias ExArgus.Kernel.{Background, State}

  @egress [:network_external, :network_internal, :filesystem_write, :ipc]

  defp ceiling(value \\ nil), do: Map.new(@egress, &{&1, value})

  defp background do
    %Background{mode: :enforce, allow_ceiling: ceiling(), inspect_ceiling: ceiling()}
  end

  test "new, status, and state expose the fixed-root genesis" do
    assert {:ok, instance} = Instance.new(background())
    assert %Instance{} = instance

    assert {:ok, %Chain{version: 5, sequence: 0, head: head}} = Instance.status(instance)
    assert byte_size(head) == 32

    assert {:ok,
            %State{
              agent_active: ["root"],
              agent_parent: [],
              agent_cap: [
                {"root",
                 [
                   :filesystem_read,
                   :filesystem_write,
                   :filesystem_delete,
                   :network_egress,
                   :network_ingress,
                   :execution_shell,
                   :execution_code,
                   :credentials,
                   :system_info,
                   :system_modify,
                   :clipboard,
                   :browser_navigate,
                   :database_read,
                   :database_write,
                   :ipc
                 ]}
              ],
              taint_levels: [],
              integ_levels: [],
              pending: [],
              challenges: [],
              consumed_ids: [],
              consumed_attestations: [],
              consumed_crossings: [],
              crossing_grants: [],
              tool_registered: []
            }} = Instance.state(instance)
  end

  test "background is exact, closed, and fail-closed before Rustler decoding" do
    invalid = [
      {nil, :invalid_struct, []},
      {%Background{}, :unknown_enum, [:mode]},
      {Map.put(background(), :root, "other"), :invalid_keys, []},
      {%Background{background() | allow_ceiling: %{}}, :invalid_keys, [:allow_ceiling]},
      {%Background{background() | inspect_ceiling: Map.put(ceiling(), :other, nil)},
       :invalid_keys, [:inspect_ceiling]},
      {%Background{background() | allow_ceiling: Map.put(ceiling(), :network_external, :secret)},
       :unknown_enum, [:allow_ceiling, :network_external]}
    ]

    for {input, reason, path} <- invalid do
      assert {:error, %Error{class: :boundary, reason: ^reason, path: ^path}} =
               Instance.new(input)
    end
  end

  test "ordinary malformed lifecycle inputs return typed errors rather than badarg" do
    assert {:error, %Error{class: :boundary, reason: :invalid_struct}} = Instance.status(nil)
    assert {:error, %Error{class: :boundary, reason: :invalid_struct}} = Instance.state(%{})

    malformed = struct(Instance, resource: :not_a_reference)

    assert {:error, %Error{class: :boundary, reason: :invalid_type, path: [:resource]}} =
             Instance.status(malformed)

    assert {:error, %Error{class: :boundary, reason: :invalid_type, path: [:resource]}} =
             Instance.state(malformed)

    wrong_reference = struct(Instance, resource: make_ref())

    assert {:error, %Error{class: :boundary, reason: :invalid_type, path: [:resource]}} =
             Instance.status(wrong_reference)
  end

  test "native live and recovery resource types reject cross-use at the BEAM decoder boundary" do
    assert {:ok, live} = Native.instance_new(background())
    assert {:ok, recovery} = Native.recovery_new(background())
    assert {:ok, chain} = Native.instance_status(live)

    assert_raise ArgumentError, fn -> Native.instance_status(recovery) end
    assert_raise ArgumentError, fn -> Native.recovery_finalize(live, chain) end
  end

  test "source loading is default and force-build wins explicit precompiled opt-in" do
    source? = &ExArgus.MixProject.build_from_source?/1

    assert source?.(%{})
    refute source?.(%{"EX_ARGUS_USE_PRECOMPILED" => "1"})

    assert source?.(%{
             "EX_ARGUS_USE_PRECOMPILED" => "1",
             "RUSTLER_PRECOMPILED_FORCE_BUILD" => "1"
           })

    assert source?.(%{
             "EX_ARGUS_USE_PRECOMPILED" => "1",
             "RUSTLER_PRECOMPILED_FORCE_BUILD" => "true"
           })

    refute function_exported?(Native, :load_rustler_precompiled, 0)
  end

  test "Instance exposes only the Task 7 lifecycle" do
    assert Enum.sort(Instance.__info__(:functions)) ==
             Enum.sort(__struct__: 0, __struct__: 1, new: 1, state: 1, status: 1)
  end

  test "only the seven V4 NIF stubs are declared" do
    nifs =
      Native.__info__(:functions)
      |> Enum.filter(fn {name, _arity} ->
        name |> Atom.to_string() |> then(&String.starts_with?(&1, ["instance_", "recovery_"]))
      end)

    assert Enum.sort(nifs) ==
             Enum.sort(
               instance_new: 1,
               instance_apply: 2,
               instance_status: 1,
               instance_state: 1,
               recovery_new: 1,
               recovery_replay: 2,
               recovery_finalize: 2
             )
  end

  test "the package starts no application callback or process" do
    assert Application.spec(:ex_argus, :mod) in [nil, []]
    refute Code.ensure_loaded?(ExArgus.Application)
  end
end
