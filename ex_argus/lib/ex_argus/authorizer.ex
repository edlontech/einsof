defmodule ExArgus.Authorizer do
  @moduledoc "Behaviour for the (unverified) authorizer oracle. Consulted by `invoke_start`."
  alias ExArgus.Kernel.{Background, State}

  @callback allows?(
              agent :: String.t(),
              tool :: String.t(),
              state :: State.t(),
              bg :: Background.t()
            ) ::
              boolean()
end
