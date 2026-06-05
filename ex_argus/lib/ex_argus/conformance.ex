defmodule ExArgus.Conformance do
  @moduledoc "Behaviour for the (unverified) conformance oracle. Consulted by `invoke_complete`."
  alias ExArgus.Kernel.{Background, State}

  @callback conforms?(
              agent :: String.t(),
              tool :: String.t(),
              state :: State.t(),
              bg :: Background.t()
            ) ::
              boolean()
end
