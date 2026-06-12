defmodule ExArgus do
  @moduledoc "Elixir binding for the verified argus-kernel."

  @state_version 2

  @doc """
  Wire-shape version of `ExArgus.Kernel.State`.

  A monotonic stamp for the encoding of the kernel `State` term as it crosses the NIF.
  Bump it on any change to `ExArgus.Kernel.State`'s fields or the NIF encode/decode.

  Consumers that persist a snapshot of `State` store it alongside this version and fail
  closed -- reject the snapshot and replay from zero -- on a mismatch, so an old snapshot
  is never silently decoded against a newer shape.
  """
  @spec state_version() :: pos_integer()
  def state_version, do: @state_version
end
