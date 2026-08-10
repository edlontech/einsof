defmodule ExArgus.Native do
  @moduledoc false

  version = Mix.Project.config()[:version]

  # Source builds are the default. EX_ARGUS_USE_PRECOMPILED=1 opts in, while the
  # established force-build switch takes precedence and RustlerPrecompiled also honors
  # its documented global force-build override.
  use RustlerPrecompiled,
    otp_app: :ex_argus,
    crate: "argus_nif",
    base_url: "https://github.com/edlontech/einsof/releases/download/ex_argus-v#{version}",
    force_build: ExArgus.MixProject.build_from_source?(System.get_env()),
    version: version,
    targets: ~w(
      aarch64-apple-darwin
      x86_64-apple-darwin
      x86_64-unknown-linux-gnu
      aarch64-unknown-linux-gnu
      x86_64-unknown-linux-musl
      aarch64-unknown-linux-musl
    )

  def instance_new(_background), do: :erlang.nif_error(:nif_not_loaded)
  def instance_apply(_instance, _command), do: :erlang.nif_error(:nif_not_loaded)
  def instance_status(_instance), do: :erlang.nif_error(:nif_not_loaded)
  def instance_state(_instance), do: :erlang.nif_error(:nif_not_loaded)
  def recovery_new(_background), do: :erlang.nif_error(:nif_not_loaded)
  def recovery_replay(_recovery, _envelope), do: :erlang.nif_error(:nif_not_loaded)
  def recovery_finalize(_recovery, _expected), do: :erlang.nif_error(:nif_not_loaded)
end
