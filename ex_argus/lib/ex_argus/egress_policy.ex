defmodule ExArgus.EgressPolicy do
  @moduledoc """
  Pure, fail-closed URL allowlist for network-egress admission.

  This is the **unverified** refinement that lives outside the proven kernel (per the
  guest-model split): it narrows *which* destinations an agent may reach, on top of the
  verified capability + flow gates. It can only ever subtract from what the kernel already
  permits -- it never widens access. The verified kernel never sees a URL; this decision is
  computed here and folded into the single authorizer boolean `invoke_start` consumes (see
  `ExArgus.EgressAuthorizer`).

  A policy is `%{agent_id => [rule]}`. A URL is admitted for an agent iff some rule for that
  agent matches. No rule, no agent entry, an unparseable URL, or anything that fails
  canonicalization => denied.

  ## Rule

      %{
        scheme: "https",                 # required; matched exactly (case-insensitive)
        host: "api.example.com",         # required; exact host (configure in punycode)
        port: 443,                       # required; matched exactly
        path_prefixes: ["/v1/", "/v2/"]  # optional; [] / absent => any path
      }

  Path prefixes match at **segment** granularity: `"/v1/"` admits `/v1` and `/v1/users` but
  not `/v10`. A rule without `:path_prefixes` admits any path on the matched host.

  ## Canonicalization (the trust-critical part)

  Hosts are lower-cased and de-trailing-dotted; ports default per scheme. A URL is denied if
  it: fails to parse, carries userinfo (`user@host` spoofing), uses a non-`http(s)` scheme,
  omits a host, contains an encoded path separator or dot-segment (`%2e`/`%2f`/`%5c`) or a
  backslash, or contains a `..` segment that escapes the path root. Host comparison is
  byte-exact after lower-casing: a Unicode host that is not the configured (punycode) host
  fails closed.
  """

  @allowed_schemes ~w(http https)

  @type rule :: %{
          required(:scheme) => String.t(),
          required(:host) => String.t(),
          required(:port) => :inet.port_number(),
          optional(:path_prefixes) => [String.t()]
        }
  @type policy :: %{optional(String.t()) => [rule]}

  @doc """
  `true` iff `url` is admissible for `agent` under `policy`. Total and fail-closed: any input
  it cannot positively match (including unparseable or malformed URLs) returns `false`.
  """
  @spec allows?(policy, String.t(), String.t()) :: boolean()
  def allows?(policy, agent, url)
      when is_map(policy) and is_binary(agent) and is_binary(url) do
    with [_ | _] = rules <- Map.get(policy, agent, []),
         {:ok, canon} <- canonicalize(url) do
      Enum.any?(rules, &match_rule?(&1, canon))
    else
      _ -> false
    end
  end

  def allows?(_policy, _agent, _url), do: false

  @spec canonicalize(String.t()) :: {:ok, map} | :error
  defp canonicalize(url) do
    with {:ok, uri} <- URI.new(url),
         scheme = normalize_scheme(uri.scheme),
         true <- scheme in @allowed_schemes,
         true <- is_nil(uri.userinfo),
         host = normalize_host(uri.host),
         true <- is_binary(host) and host != "",
         {:ok, segments} <- normalize_path(uri.path) do
      {:ok, %{scheme: scheme, host: host, port: uri.port, path_segments: segments}}
    else
      _ -> :error
    end
  end

  defp normalize_scheme(nil), do: nil
  defp normalize_scheme(scheme) when is_binary(scheme), do: String.downcase(scheme)

  defp normalize_host(nil), do: nil

  defp normalize_host(host) when is_binary(host) do
    host |> String.downcase() |> String.trim_trailing(".")
  end

  @spec normalize_path(String.t() | nil) :: {:ok, [String.t()]} | :error
  defp normalize_path(nil), do: {:ok, []}

  defp normalize_path(raw) do
    if encoded_traversal?(raw) do
      :error
    else
      case resolve(String.split(raw, "/"), []) do
        :error -> :error
        segments -> {:ok, segments}
      end
    end
  end

  defp encoded_traversal?(raw) do
    String.contains?(String.downcase(raw), ["%2e", "%2f", "%5c"]) or
      String.contains?(raw, "\\")
  end

  # Resolve `.`/`..` and collapse empty segments. `:error` if a `..` escapes the root.
  defp resolve([], acc), do: Enum.reverse(acc)
  defp resolve(["" | rest], acc), do: resolve(rest, acc)
  defp resolve(["." | rest], acc), do: resolve(rest, acc)
  defp resolve([".." | _rest], []), do: :error
  defp resolve([".." | rest], [_top | acc]), do: resolve(rest, acc)
  defp resolve([segment | rest], acc), do: resolve(rest, [segment | acc])

  defp match_rule?(rule, canon) do
    normalize_scheme(rule.scheme) == canon.scheme and
      normalize_host(rule.host) == canon.host and
      rule.port == canon.port and
      path_allowed?(Map.get(rule, :path_prefixes, []), canon.path_segments)
  end

  defp path_allowed?([], _segments), do: true

  defp path_allowed?(prefixes, segments) do
    Enum.any?(prefixes, fn prefix ->
      List.starts_with?(segments, String.split(prefix, "/", trim: true))
    end)
  end
end
