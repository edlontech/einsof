defmodule ExArgus.Native do
  @moduledoc false

  version = Mix.Project.config()[:version]

  use RustlerPrecompiled,
    otp_app: :ex_argus,
    crate: "argus_nif",
    base_url: "https://github.com/edlontech/einsof/releases/download/ex_argus-v#{version}",
    force_build:
      System.get_env("RUSTLER_PRECOMPILED_FORCE_BUILD") in ["1", "true"] ||
        Mix.env() in [:dev, :test],
    version: version,
    targets: ~w(
      aarch64-apple-darwin
      x86_64-apple-darwin
      x86_64-unknown-linux-gnu
      aarch64-unknown-linux-gnu
      x86_64-unknown-linux-musl
      aarch64-unknown-linux-musl
    )

  def initial_state, do: :erlang.nif_error(:nif_not_loaded)
  def register_tool(_state, _bg, _tool), do: :erlang.nif_error(:nif_not_loaded)
  def unregister_tool(_state, _bg, _tool), do: :erlang.nif_error(:nif_not_loaded)
  def load_instruction(_state, _bg, _agent, _instr), do: :erlang.nif_error(:nif_not_loaded)
  def delegate(_state, _bg, _grantor, _grantee), do: :erlang.nif_error(:nif_not_loaded)
  def grant_capability(_state, _bg, _parent, _child, _cap), do: :erlang.nif_error(:nif_not_loaded)
  def revoke(_state, _bg, _parent, _target), do: :erlang.nif_error(:nif_not_loaded)
  def cascade_revoke(_state, _bg, _child, _parent), do: :erlang.nif_error(:nif_not_loaded)

  def return_endorsed(_state, _bg, _child, _parent, _return_conforms, _clvl, _ilvl),
    do: :erlang.nif_error(:nif_not_loaded)

  def sentinel_credit_budget(_state, _bg, _agent, _amount), do: :erlang.nif_error(:nif_not_loaded)

  def grant_override(_state, _bg, _granter, _target, _tool, _level),
    do: :erlang.nif_error(:nif_not_loaded)

  def invoke_start(_s, _bg, _agent, _tool, _inv, _authorizer_allows, _content_gate, _attested_egress),
    do: :erlang.nif_error(:nif_not_loaded)

  def invoke_complete(_s, _bg, _agent, _inv, _conformance_conforms),
    do: :erlang.nif_error(:nif_not_loaded)

  def return_unendorsed(_s, _bg, _child, _parent, _content_gate),
    do: :erlang.nif_error(:nif_not_loaded)

  def sentinel_elevate_taint(_s, _bg, _agent, _level, _content_gate),
    do: :erlang.nif_error(:nif_not_loaded)

  def sentinel_degrade_integrity(_s, _bg, _agent, _level, _content_gate),
    do: :erlang.nif_error(:nif_not_loaded)

  def explain_invoke(_s, _bg, _agent, _tool, _inv, _authorizer_allows, _content_gate, _attested_egress),
    do: :erlang.nif_error(:nif_not_loaded)

  def explain_return_unendorsed(_s, _bg, _child, _parent, _content_gate),
    do: :erlang.nif_error(:nif_not_loaded)

  def explain_sentinel_elevate_taint(_s, _bg, _agent, _level, _content_gate),
    do: :erlang.nif_error(:nif_not_loaded)

  def explain_sentinel_degrade_integrity(_s, _bg, _agent, _level, _content_gate),
    do: :erlang.nif_error(:nif_not_loaded)

  def explain_return_endorsed(_s, _bg, _child, _parent, _return_conforms, _clvl, _ilvl),
    do: :erlang.nif_error(:nif_not_loaded)

  def explain_grant_override(_s, _bg, _granter, _target, _level),
    do: :erlang.nif_error(:nif_not_loaded)

  def instance_new(_bg), do: :erlang.nif_error(:nif_not_loaded)
  def instance_state(_h), do: :erlang.nif_error(:nif_not_loaded)
  def instance_seq(_h), do: :erlang.nif_error(:nif_not_loaded)
  def instance_register_tool(_h, _tool), do: :erlang.nif_error(:nif_not_loaded)
  def instance_unregister_tool(_h, _tool), do: :erlang.nif_error(:nif_not_loaded)
  def instance_load_instruction(_h, _agent, _instr), do: :erlang.nif_error(:nif_not_loaded)
  def instance_delegate(_h, _grantor, _grantee), do: :erlang.nif_error(:nif_not_loaded)
  def instance_grant_capability(_h, _parent, _child, _cap), do: :erlang.nif_error(:nif_not_loaded)
  def instance_revoke(_h, _parent, _target), do: :erlang.nif_error(:nif_not_loaded)
  def instance_cascade_revoke(_h, _child, _parent), do: :erlang.nif_error(:nif_not_loaded)

  def instance_return_endorsed(_h, _child, _parent, _return_conforms, _clvl, _ilvl),
    do: :erlang.nif_error(:nif_not_loaded)

  def instance_sentinel_credit_budget(_h, _agent, _amount), do: :erlang.nif_error(:nif_not_loaded)

  def instance_grant_override(_h, _granter, _target, _tool, _level),
    do: :erlang.nif_error(:nif_not_loaded)

  def instance_invoke_start(_h, _agent, _tool, _inv, _auth, _gate, _attested_egress),
    do: :erlang.nif_error(:nif_not_loaded)

  def instance_invoke_complete(_h, _agent, _inv, _conf),
    do: :erlang.nif_error(:nif_not_loaded)

  def instance_return_unendorsed(_h, _child, _parent, _gate),
    do: :erlang.nif_error(:nif_not_loaded)

  def instance_sentinel_elevate_taint(_h, _agent, _level, _gate),
    do: :erlang.nif_error(:nif_not_loaded)

  def instance_sentinel_degrade_integrity(_h, _agent, _level, _gate),
    do: :erlang.nif_error(:nif_not_loaded)

  def instance_explain_invoke(_h, _agent, _tool, _inv, _auth, _gate, _attested_egress),
    do: :erlang.nif_error(:nif_not_loaded)

  def instance_explain_return_unendorsed(_h, _child, _parent, _gate),
    do: :erlang.nif_error(:nif_not_loaded)

  def instance_explain_sentinel_elevate_taint(_h, _agent, _level, _gate),
    do: :erlang.nif_error(:nif_not_loaded)

  def instance_explain_sentinel_degrade_integrity(_h, _agent, _level, _gate),
    do: :erlang.nif_error(:nif_not_loaded)

  def instance_explain_return_endorsed(_h, _child, _parent, _return_conforms, _clvl, _ilvl),
    do: :erlang.nif_error(:nif_not_loaded)

  def instance_explain_grant_override(_h, _granter, _target, _level),
    do: :erlang.nif_error(:nif_not_loaded)
end
