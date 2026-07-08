defmodule ExArgus do
  @moduledoc "Elixir binding for the verified argus-kernel."

  @state_version 4

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

  @typedoc "The version-stamp entry every recordable log must begin with."
  @type header :: {:state_version, pos_integer}

  @doc """
  The version-stamp entry to prepend to any log persisted for
  `ExArgus.Instance.recover/2` or `ExArgus.Replay`.
  """
  @spec log_header() :: header
  def log_header, do: {:state_version, @state_version}

  @doc """
  Strip the version-stamp header from a recordable log. Returns `{:ok, rest}` when the
  log begins with `log_header/0`; `:error` for a missing header, a mismatched version, or
  an empty log. Checked before any entry replays -- see `ExArgus.Instance.recover/2` and
  `ExArgus.Replay`.
  """
  @spec strip_log_header([term]) :: {:ok, [term]} | :error
  def strip_log_header([{:state_version, v} | rest]) when v === @state_version, do: {:ok, rest}
  def strip_log_header(_), do: :error
end
