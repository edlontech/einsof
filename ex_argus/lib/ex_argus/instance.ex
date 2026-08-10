defmodule ExArgus.Instance do
  @moduledoc "Opaque live V4 kernel resource with lifecycle observations."

  alias ExArgus.{Chain, Error, Native}
  alias ExArgus.Kernel.Background

  @egress_kinds [:network_external, :network_internal, :filesystem_write, :ipc]
  @conf_levels [:public, :internal, :sensitive, :restricted]
  @background_keys [:__struct__, :mode, :allow_ceiling, :inspect_ceiling]
  @instance_keys [:__struct__, :resource]

  defstruct [:resource]

  @opaque t :: %__MODULE__{resource: reference()}

  @doc "Creates a fresh live instance at the fixed-root initial state."
  @spec new(Background.t()) :: {:ok, t()} | {:error, Error.t()}
  def new(background) do
    with :ok <- validate_background(background),
         {:ok, resource} <- Native.instance_new(background) do
      {:ok, %__MODULE__{resource: resource}}
    else
      {:error, %Error{}} = error -> error
      {:error, reason} -> map_native_error(reason)
      _other -> internal_error()
    end
  end

  @doc "Returns the canonical read-only V5 state projection."
  @spec state(t()) :: {:ok, ExArgus.Kernel.State.t()} | {:error, Error.t()}
  def state(instance), do: observe(instance, &Native.instance_state/1)

  @doc "Returns the accepted-history length and digest head."
  @spec status(t()) :: {:ok, Chain.t()} | {:error, Error.t()}
  def status(instance), do: observe(instance, &Native.instance_status/1)

  defp observe(instance, native) do
    with {:ok, resource} <- validate_instance(instance) do
      try do
        case native.(resource) do
          {:ok, value} -> {:ok, value}
          {:error, reason} -> map_native_error(reason)
          _other -> internal_error()
        end
      rescue
        ArgumentError -> boundary_error(:invalid_type, [:resource])
      end
    end
  end

  defp validate_background(%Background{} = background) do
    with :ok <- exact_keys(background, @background_keys, []),
         :ok <- enum(background.mode, [:enforce, :monitor], [:mode]),
         :ok <- ceiling(background.allow_ceiling, [:allow_ceiling]) do
      ceiling(background.inspect_ceiling, [:inspect_ceiling])
    end
  end

  defp validate_background(_background), do: boundary_error(:invalid_struct, [])

  defp validate_instance(%__MODULE__{} = instance) do
    with :ok <- exact_keys(instance, @instance_keys, []),
         true <- is_reference(instance.resource) do
      {:ok, instance.resource}
    else
      false -> boundary_error(:invalid_type, [:resource])
      {:error, %Error{}} = error -> error
    end
  end

  defp validate_instance(_instance), do: boundary_error(:invalid_struct, [])

  defp ceiling(value, path) when is_map(value) do
    with :ok <- exact_keys(value, @egress_kinds, path) do
      case Enum.find(@egress_kinds, &(value[&1] not in [nil | @conf_levels])) do
        nil -> :ok
        kind -> boundary_error(:unknown_enum, path ++ [kind])
      end
    end
  end

  defp ceiling(_value, path), do: boundary_error(:invalid_type, path)

  defp exact_keys(value, expected, path) do
    if map_size(value) == length(expected) and Enum.all?(expected, &Map.has_key?(value, &1)) do
      :ok
    else
      boundary_error(:invalid_keys, path)
    end
  end

  defp enum(value, allowed, path) do
    if value in allowed, do: :ok, else: boundary_error(:unknown_enum, path)
  end

  defp map_native_error(:instance_busy), do: boundary_error(:instance_busy, [])
  defp map_native_error(:capacity_exceeded), do: boundary_error(:capacity_exceeded, [])
  defp map_native_error(:sequence_exhausted), do: boundary_error(:sequence_exhausted, [])

  defp map_native_error(:resource_poisoned) do
    {:error, %Error{class: :internal, reason: :resource_poisoned}}
  end

  defp map_native_error(_reason), do: internal_error()

  defp boundary_error(reason, path) do
    {:error, %Error{class: :boundary, reason: reason, path: path}}
  end

  defp internal_error do
    {:error, %Error{class: :internal, reason: :native_contract_violation}}
  end
end
