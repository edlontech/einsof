defmodule ExArgus.MixProject do
  use Mix.Project

  def project do
    [
      app: :ex_argus,
      version: "0.3.0",
      elixir: "~> 1.19",
      start_permanent: Mix.env() == :prod,
      deps: deps()
    ]
  end

  def application do
    [extra_applications: [:logger]]
  end

  @doc false
  def build_from_source?(environment) when is_map(environment) do
    force_source? = environment["RUSTLER_PRECOMPILED_FORCE_BUILD"] in ["1", "true"]
    use_precompiled? = environment["EX_ARGUS_USE_PRECOMPILED"] == "1"

    force_source? or not use_precompiled?
  end

  defp deps do
    [
      {:credo, "~> 1.7", only: [:dev, :test], runtime: false},
      {:dialyxir, "~> 1.4", only: [:dev, :test], runtime: false},
      {:doctor, "~> 0.22", only: :dev},
      {:ex_check, "~> 0.16", only: [:dev, :test], runtime: false},
      {:ex_doc, "~> 0.34", only: :dev, runtime: false},
      {:mix_audit, ">= 0.0.0", only: [:dev, :test], runtime: false},
      # Rustler owns its required Jason compiler dependency; ExArgus has no runtime JSON contract.
      {:rustler, "~> 0.38.0", runtime: false},
      {:rustler_precompiled, "~> 0.9"},
      {:telemetry, "~> 1.3"}
    ]
  end
end
