defmodule ExArgus.ContentGate do
  @moduledoc "Behaviour for the (unverified) content-gate oracle. Consulted on INSPECT-mode flows."
  alias ExArgus.Kernel.{Background, State}

  @callback passes?(
              agent :: String.t(),
              tool :: String.t(),
              state :: State.t(),
              bg :: Background.t()
            ) ::
              boolean()
end
