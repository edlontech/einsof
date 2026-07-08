defmodule ExArgus.EgressAuthorizerTest do
  use ExUnit.Case, async: true

  alias ExArgus.EgressAuthorizer
  alias ExArgus.Kernel.Background
  alias ExArgus.Native

  @policy %{
    "a1" => [%{scheme: "https", host: "api.example.com", port: 443, path_prefixes: ["/v1/"]}]
  }

  # A public-floor egress tool. allow_ceiling puts network_external in ALLOW for every level,
  # so the flow gate passes and the test isolates the authorizer (URL) decision.
  defp bg do
    %Background{
      tools: %{
        "http_get" => %{
          capabilities: [:network_egress],
          egress: [:network_external],
          conf_floor: :public,
          output_bounded: false,
          issuer: "trusted",
          integ_floor: :untrusted,
          integ_inspect_floor: :untrusted,
          output_integ: :attested
        }
      },
      allow_ceiling: %{network_external: :restricted},
      inspect_ceiling: %{},
      trusted_issuers: ["trusted"],
      instruction_issuer: %{}
    }
  end

  defp ready_state(bg) do
    s0 = Native.initial_state()
    {:ok, s1, _} = Native.register_tool(s0, bg, "http_get")
    {:ok, s2, _} = Native.delegate(s1, bg, "root", "a1")
    {:ok, s3, _} = Native.grant_capability(s2, bg, "root", "a1", :network_egress)
    s3
  end

  describe "admit?/4" do
    test "admits an allowlisted URL (X)" do
      assert EgressAuthorizer.admit?(@policy, "a1", "http_get", %{
               url: "https://api.example.com/v1/x"
             })
    end

    test "denies a non-allowlisted URL (Y)" do
      refute EgressAuthorizer.admit?(@policy, "a1", "http_get", %{url: "https://evil.com/v1/x"})
    end

    test "tool calls without a url are not egress-filtered" do
      assert EgressAuthorizer.admit?(@policy, "a1", "read_file", %{})
      assert EgressAuthorizer.admit?(@policy, "a1", "read_file", %{path: "/etc/hosts"})
    end
  end

  describe "verdict propagation through the kernel (the OracleFidelity seam)" do
    test "an EgressPolicy allow lets invoke_start through" do
      bg = bg()
      s3 = ready_state(bg)

      allow =
        EgressAuthorizer.admit?(@policy, "a1", "http_get", %{url: "https://api.example.com/v1/x"})

      assert allow

      assert {:ok, s4, {:invoke_start, "a1", "http_get", "inv-1"}} =
               Native.invoke_start(s3, bg, "a1", "http_get", "inv-1", allow, %{}, [
                 :network_external
               ])

      assert "inv-1" in Map.fetch!(s4.in_flight, "a1")
    end

    test "an EgressPolicy deny becomes :authorizer_denied in the kernel" do
      bg = bg()
      s3 = ready_state(bg)

      allow =
        EgressAuthorizer.admit?(@policy, "a1", "http_get", %{url: "https://evil.com/v1/x"})

      refute allow

      assert {:error, :authorizer_denied} =
               Native.invoke_start(s3, bg, "a1", "http_get", "inv-1", allow, %{}, [
                 :network_external
               ])
    end
  end
end
