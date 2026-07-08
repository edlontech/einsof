defmodule ExArgus.EgressPolicyTest do
  use ExUnit.Case, async: true
  use ExUnitProperties

  alias ExArgus.EgressPolicy

  @rules [
    %{
      scheme: "https",
      host: "api.example.com",
      port: 443,
      path_prefixes: ["/v1/"],
      kind: :network_external
    },
    %{scheme: "https", host: "cdn.example.com", port: 443, kind: :network_external}
  ]

  describe "classify/2 -- positive matches" do
    test "attests the rule's kind for a configured host + path prefix (URL X)" do
      assert {:ok, [:network_external]} =
               EgressPolicy.classify(@rules, "https://api.example.com/v1/users")
    end

    test "attests at the prefix boundary exactly" do
      assert {:ok, [:network_external]} =
               EgressPolicy.classify(@rules, "https://api.example.com/v1")
    end

    test "attests any path on a host whose rule has no path_prefixes" do
      assert {:ok, [:network_external]} =
               EgressPolicy.classify(@rules, "https://cdn.example.com/anything/here")
    end

    test "host match is case-insensitive and ignores a trailing dot" do
      assert {:ok, [:network_external]} =
               EgressPolicy.classify(@rules, "HTTPS://API.EXAMPLE.COM./v1/x")
    end

    test "an explicit default port matches" do
      assert {:ok, [:network_external]} =
               EgressPolicy.classify(@rules, "https://api.example.com:443/v1/x")
    end

    test "multiple matching rules attest the union of their kinds, deduplicated" do
      rules = [
        %{scheme: "https", host: "api.example.com", port: 443, kind: :network_external},
        %{scheme: "https", host: "api.example.com", port: 443, kind: :filesystem_write},
        %{scheme: "https", host: "api.example.com", port: 443, kind: :network_external}
      ]

      assert {:ok, kinds} = EgressPolicy.classify(rules, "https://api.example.com/anything")
      assert Enum.sort(kinds) == [:filesystem_write, :network_external]
    end
  end

  describe "classify/2 -- denials (fail-closed)" do
    test "denies a non-allowlisted host (URL Y)" do
      assert :deny = EgressPolicy.classify(@rules, "https://evil.com/v1/users")
    end

    test "denies a path outside the prefix" do
      assert :deny = EgressPolicy.classify(@rules, "https://api.example.com/v2/users")
    end

    test "does not let /v1 prefix leak into /v10" do
      assert :deny = EgressPolicy.classify(@rules, "https://api.example.com/v10/users")
    end

    test "denies a non-default / mismatched port" do
      assert :deny = EgressPolicy.classify(@rules, "https://api.example.com:8443/v1/x")
    end

    test "denies a scheme downgrade" do
      assert :deny = EgressPolicy.classify(@rules, "http://api.example.com/v1/x")
    end

    test "denies userinfo host spoofing" do
      assert :deny = EgressPolicy.classify(@rules, "https://api.example.com@evil.com/v1/x")
    end

    test "denies path traversal" do
      assert :deny = EgressPolicy.classify(@rules, "https://api.example.com/v1/../../secret")
    end

    test "denies encoded path traversal" do
      assert :deny = EgressPolicy.classify(@rules, "https://api.example.com/v1/%2e%2e%2fsecret")
    end

    test "denies an encoded slash in the path" do
      assert :deny = EgressPolicy.classify(@rules, "https://api.example.com/v1%2fsecret")
    end

    test "denies a non-http(s) scheme" do
      assert :deny = EgressPolicy.classify(@rules, "file:///etc/passwd")
    end

    test "denies a schemeless / relative url" do
      assert :deny = EgressPolicy.classify(@rules, "api.example.com/v1/x")
    end

    test "denies an unparseable url" do
      assert :deny = EgressPolicy.classify(@rules, "ht!tp://::::")
    end

    test "denies a unicode homograph host (must be configured in punycode)" do
      assert :deny = EgressPolicy.classify(@rules, "https://аpi.example.com/v1/x")
    end

    test "denies under an empty rule list" do
      assert :deny = EgressPolicy.classify([], "https://api.example.com/v1/x")
    end

    test "is fail-closed on non-binary inputs" do
      assert :deny = EgressPolicy.classify(@rules, nil)
      assert :deny = EgressPolicy.classify(nil, "https://api.example.com/v1/x")
    end
  end

  describe "properties" do
    property "is total: never raises and returns :deny or {:ok, kinds} for arbitrary urls" do
      check all(url <- string(:printable)) do
        assert match?({:ok, _}, EgressPolicy.classify(@rules, url)) or
                 EgressPolicy.classify(@rules, url) == :deny
      end
    end

    property "an empty rule list denies every url" do
      check all(url <- string(:printable)) do
        assert :deny = EgressPolicy.classify([], url)
      end
    end

    property "adding rules never turns an attest into a deny (allowlist is monotone)" do
      base = [%{scheme: "https", host: "api.example.com", port: 443, kind: :network_external}]

      extra = [
        %{scheme: "https", host: "other.example.com", port: 443, kind: :network_external}
      ]

      check all(url <- url_gen()) do
        case EgressPolicy.classify(base, url) do
          {:ok, kinds} -> assert {:ok, ^kinds} = EgressPolicy.classify(base ++ extra, url)
          :deny -> :ok
        end
      end
    end

    property "an attested url always lands on an allowlisted host" do
      hosts = ["api.example.com", "cdn.example.com"]

      check all(url <- url_gen()) do
        if match?({:ok, _}, EgressPolicy.classify(@rules, url)) do
          assert Enum.any?(hosts, &String.contains?(String.downcase(url), &1))
        end
      end
    end
  end

  defp url_gen do
    gen all(
          scheme <- member_of(["https", "http", "ftp"]),
          host <-
            member_of(["api.example.com", "cdn.example.com", "evil.com", "API.EXAMPLE.COM"]),
          path <- member_of(["/v1/users", "/v2/x", "/", "/v1/../etc", "/v1%2fx"])
        ) do
      "#{scheme}://#{host}#{path}"
    end
  end
end
