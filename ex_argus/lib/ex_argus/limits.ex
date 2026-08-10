defmodule ExArgus.Limits do
  @moduledoc "Fixed V5 adapter capacity profile mirrored from the native boundary."

  @max_opaque_utf8_bytes 1_024
  @max_agents 4_096
  @max_parent_or_label_keys 4_096
  @max_tools 1_024
  @max_pending 4_096
  @max_challenges 4_096
  @max_crossing_grants 16_384
  @max_consumed_ids 65_536
  @max_consumed_attestations 65_536
  @max_consumed_crossings 65_536
  @max_retained_utf8_bytes 16 * 1024 * 1024
  @max_accepted_sequence 100_000
  @max_recovery_envelopes 100_000
  @max_replay_content_bytes 64 * 1024 * 1024
  @max_capabilities 15
  @max_egress_kinds 4
  @max_conf_levels 4
  @max_integ_levels 4

  def max_opaque_utf8_bytes, do: @max_opaque_utf8_bytes
  def max_agents, do: @max_agents
  def max_parent_or_label_keys, do: @max_parent_or_label_keys
  def max_tools, do: @max_tools
  def max_pending, do: @max_pending
  def max_challenges, do: @max_challenges
  def max_crossing_grants, do: @max_crossing_grants
  def max_consumed_ids, do: @max_consumed_ids
  def max_consumed_attestations, do: @max_consumed_attestations
  def max_consumed_crossings, do: @max_consumed_crossings
  def max_retained_utf8_bytes, do: @max_retained_utf8_bytes
  def max_accepted_sequence, do: @max_accepted_sequence
  def max_recovery_envelopes, do: @max_recovery_envelopes
  def max_replay_content_bytes, do: @max_replay_content_bytes
  def max_capabilities, do: @max_capabilities
  def max_egress_kinds, do: @max_egress_kinds
  def max_conf_levels, do: @max_conf_levels
  def max_integ_levels, do: @max_integ_levels
end
