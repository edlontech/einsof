defmodule ExArgus.EgressPolicyTest do
  use ExUnit.Case, async: true
  use ExUnitProperties

  alias ExArgus.EgressPolicy

  @policy %{
    "a1" => [
      %{scheme: "https", host: "api.example.com", port: 443, path_prefixes: ["/v1/"]},
      %{scheme: "https", host: "cdn.example.com", port: 443}
    ]
  }

  describe "allows?/3 -- positive matches" do
    test "admits a configured host + path prefix (URL X)" do
      assert EgressPolicy.allows?(@policy, "a1", "https://api.example.com/v1/users")
    end

    test "admits the prefix boundary exactly" do
      assert EgressPolicy.allows?(@policy, "a1", "https://api.example.com/v1")
    end

    test "admits any path on a host whose rule has no path_prefixes" do
      assert EgressPolicy.allows?(@policy, "a1", "https://cdn.example.com/anything/here")
    end

    test "host match is case-insensitive and ignores a trailing dot" do
      assert EgressPolicy.allows?(@policy, "a1", "HTTPS://API.EXAMPLE.COM./v1/x")
    end

    test "an explicit default port matches" do
      assert EgressPolicy.allows?(@policy, "a1", "https://api.example.com:443/v1/x")
    end
  end

  describe "allows?/3 -- denials" do
    test "denies a non-allowlisted host (URL Y)" do
      refute EgressPolicy.allows?(@policy, "a1", "https://evil.com/v1/users")
    end

    test "denies a path outside the prefix" do
      refute EgressPolicy.allows?(@policy, "a1", "https://api.example.com/v2/users")
    end

    test "does not let /v1 prefix leak into /v10" do
      refute EgressPolicy.allows?(@policy, "a1", "https://api.example.com/v10/users")
    end

    test "denies a non-default / mismatched port" do
      refute EgressPolicy.allows?(@policy, "a1", "https://api.example.com:8443/v1/x")
    end

    test "denies a scheme downgrade" do
      refute EgressPolicy.allows?(@policy, "a1", "http://api.example.com/v1/x")
    end

    test "denies userinfo host spoofing" do
      refute EgressPolicy.allows?(@policy, "a1", "https://api.example.com@evil.com/v1/x")
    end

    test "denies path traversal" do
      refute EgressPolicy.allows?(@policy, "a1", "https://api.example.com/v1/../../secret")
    end

    test "denies encoded path traversal" do
      refute EgressPolicy.allows?(@policy, "a1", "https://api.example.com/v1/%2e%2e%2fsecret")
    end

    test "denies an encoded slash in the path" do
      refute EgressPolicy.allows?(@policy, "a1", "https://api.example.com/v1%2fsecret")
    end

    test "denies a non-http(s) scheme" do
      refute EgressPolicy.allows?(@policy, "a1", "file:///etc/passwd")
    end

    test "denies a schemeless / relative url" do
      refute EgressPolicy.allows?(@policy, "a1", "api.example.com/v1/x")
    end

    test "denies an unparseable url" do
      refute EgressPolicy.allows?(@policy, "a1", "ht!tp://::::")
    end

    test "denies a unicode homograph host (must be configured in punycode)" do
      refute EgressPolicy.allows?(@policy, "a1", "https://аpi.example.com/v1/x")
    end

    test "denies an agent with no rules" do
      refute EgressPolicy.allows?(@policy, "ghost", "https://api.example.com/v1/x")
    end

    test "denies under an empty policy" do
      refute EgressPolicy.allows?(%{}, "a1", "https://api.example.com/v1/x")
    end

    test "is fail-closed on non-binary inputs" do
      refute EgressPolicy.allows?(@policy, "a1", nil)
      refute EgressPolicy.allows?(@policy, :a1, "https://api.example.com/v1/x")
    end
  end

  describe "properties" do
    property "is total: never raises and always returns a boolean for arbitrary urls" do
      check all(
              url <- string(:printable),
              agent <- member_of(["a1", "cdn", "ghost"])
            ) do
        assert is_boolean(EgressPolicy.allows?(@policy, agent, url))
      end
    end

    property "an empty policy denies every url" do
      check all(url <- string(:printable)) do
        refute EgressPolicy.allows?(%{}, "a1", url)
      end
    end

    property "adding rules never turns an allow into a deny (allowlist is monotone)" do
      base = [%{scheme: "https", host: "api.example.com", port: 443}]
      extra = [%{scheme: "https", host: "other.example.com", port: 443}]

      check all(url <- url_gen()) do
        if EgressPolicy.allows?(%{"a1" => base}, "a1", url) do
          assert EgressPolicy.allows?(%{"a1" => base ++ extra}, "a1", url)
        end
      end
    end

    property "an admitted url always lands on an allowlisted host" do
      hosts = ["api.example.com", "cdn.example.com"]

      check all(url <- url_gen()) do
        if EgressPolicy.allows?(@policy, "a1", url) do
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
