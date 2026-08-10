defmodule ExArgus do
  @moduledoc "Elixir boundary for the Argus V4 kernel and V5 runtime wire model."

  @state_version 5

  @doc "Returns the exact runtime wire and state-projection version."
  @spec state_version() :: 5
  def state_version, do: @state_version
end
