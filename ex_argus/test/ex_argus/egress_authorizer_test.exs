defmodule ExArgus.EgressAuthorizerTest do
  use ExUnit.Case, async: true

  alias ExArgus.EgressAuthorizer
  alias ExArgus.Kernel.Background
  alias ExArgus.Native

  @policy %{
    "a1" => [
      %{
        scheme: "https",
        host: "api.example.com",
        port: 443,
        path_prefixes: ["/v1/"],
        kind: :network_external
      }
    ]
  }

  # A public-floor egress tool. allow_ceiling puts network_external and filesystem_write in
  # ALLOW for every level, so the flow gate passes and the test isolates the attest decision.
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
        },
        "no_egress_tool" => %{
          capabilities: [],
          egress: [],
          conf_floor: :public,
          output_bounded: true,
          issuer: "trusted",
          integ_floor: :untrusted,
          integ_inspect_floor: :untrusted,
          output_integ: :attested
        }
      },
      allow_ceiling: %{network_external: :restricted, filesystem_write: :restricted},
      inspect_ceiling: %{},
      trusted_issuers: ["trusted"],
      instruction_issuer: %{}
    }
  end

  defp ready_state(bg) do
    s0 = Native.initial_state()
    {:ok, s1, _} = Native.register_tool(s0, bg, "http_get")
    {:ok, s1b, _} = Native.register_tool(s1, bg, "no_egress_tool")
    {:ok, s2, _} = Native.delegate(s1b, bg, "root", "a1")
    {:ok, s3, _} = Native.grant_capability(s2, bg, "root", "a1", :network_egress)
    s3
  end

  describe "attest/4 -- single url" do
    test "attests the union of matching kinds for an allowlisted URL (X)" do
      assert {true, [:network_external]} =
               EgressAuthorizer.attest(@policy, "a1", [:network_external], %{
                 url: "https://api.example.com/v1/x"
               })
    end

    test "denies with an empty attestation for a non-allowlisted URL (Y)" do
      assert {false, []} =
               EgressAuthorizer.attest(@policy, "a1", [:network_external], %{
                 url: "https://evil.com/v1/x"
               })
    end
  end

  describe "attest/4 -- multiple urls" do
    test "unions kinds across all urls" do
      policy = %{
        "a1" => [
          %{scheme: "https", host: "api.example.com", port: 443, kind: :network_external},
          %{scheme: "https", host: "files.example.com", port: 443, kind: :filesystem_write}
        ]
      }

      assert {true, kinds} =
               EgressAuthorizer.attest(policy, "a1", [:network_external, :filesystem_write], %{
                 urls: ["https://api.example.com/x", "https://files.example.com/y"]
               })

      assert Enum.sort(kinds) == [:filesystem_write, :network_external]
    end

    test "any denied url denies the whole call with an empty attestation" do
      policy = %{
        "a1" => [%{scheme: "https", host: "api.example.com", port: 443, kind: :network_external}]
      }

      assert {false, []} =
               EgressAuthorizer.attest(policy, "a1", [:network_external], %{
                 urls: ["https://api.example.com/x", "https://evil.com/y"]
               })
    end
  end

  describe "attest/4 -- no url dimension" do
    test "attests the tool's declared egress set (V2-equivalent static worst case)" do
      assert {true, [:network_external]} =
               EgressAuthorizer.attest(@policy, "a1", [:network_external], %{path: "/etc/hosts"})

      assert {true, [:network_external]} =
               EgressAuthorizer.attest(@policy, "a1", [:network_external], %{})
    end

    test "a no-egress tool attests []" do
      assert {true, []} = EgressAuthorizer.attest(@policy, "a1", [], %{})
    end
  end

  describe "verdict propagation through the kernel (the OracleFidelity seam)" do
    test "an EgressPolicy allow lets invoke_start through" do
      bg = bg()
      s3 = ready_state(bg)

      {authorized?, attested} =
        EgressAuthorizer.attest(@policy, "a1", [:network_external], %{
          url: "https://api.example.com/v1/x"
        })

      assert authorized?

      assert {:ok, s4, {:invoke_start, "a1", "http_get", "inv-1"}} =
               Native.invoke_start(s3, bg, "a1", "http_get", "inv-1", authorized?, %{}, attested)

      assert "inv-1" in Map.fetch!(s4.in_flight, "a1")
    end

    test "an EgressPolicy deny becomes :authorizer_denied in the kernel" do
      bg = bg()
      s3 = ready_state(bg)

      # A no-egress tool: coverage/narrowing pass trivially on an empty attestation, isolating
      # the authorizer-verdict path (CHECK 3) from the narrowing/coverage checks that fire
      # first for an egress-bearing tool.
      {authorized?, attested} =
        EgressAuthorizer.attest(@policy, "a1", [], %{url: "https://evil.com/v1/x"})

      refute authorized?

      assert {:error, :authorizer_denied} =
               Native.invoke_start(
                 s3,
                 bg,
                 "a1",
                 "no_egress_tool",
                 "inv-1",
                 authorized?,
                 %{},
                 attested
               )
    end

    test "an attested kind outside the tool's declared set denies with :attestation_invalid (narrowing)" do
      bg = bg()
      s3 = ready_state(bg)

      policy = %{
        "a1" => [
          %{scheme: "https", host: "api.example.com", port: 443, kind: :network_external},
          %{scheme: "https", host: "api.example.com", port: 443, kind: :filesystem_write}
        ]
      }

      {authorized?, attested} =
        EgressAuthorizer.attest(policy, "a1", [:network_external], %{
          url: "https://api.example.com/x"
        })

      assert authorized?
      assert Enum.sort(attested) == [:filesystem_write, :network_external]

      assert {:error, :attestation_invalid} =
               Native.invoke_start(s3, bg, "a1", "http_get", "inv-1", authorized?, %{}, attested)
    end

    test "an empty attestation on an egress-bearing tool denies with :attestation_invalid (coverage)" do
      bg = bg()
      s3 = ready_state(bg)

      {authorized?, attested} =
        EgressAuthorizer.attest(@policy, "a1", [:network_external], %{path: "irrelevant"})

      assert authorized?
      assert attested == [:network_external]

      assert {:error, :attestation_invalid} =
               Native.invoke_start(s3, bg, "a1", "http_get", "inv-1", authorized?, %{}, [])
    end

    test "the adapter never intersects the union with the declared set -- the kernel deny surfaces" do
      bg = bg()
      s3 = ready_state(bg)

      policy = %{
        "a1" => [
          %{scheme: "https", host: "api.example.com", port: 443, kind: :network_external},
          %{scheme: "https", host: "api.example.com", port: 443, kind: :filesystem_write}
        ]
      }

      {true, attested} =
        EgressAuthorizer.attest(policy, "a1", [:network_external], %{
          url: "https://api.example.com/x"
        })

      # The union exceeds the declared set; a silently-intersecting adapter would trim this
      # back to [:network_external] and let the call through. It must not.
      assert :filesystem_write in attested

      assert {:error, :attestation_invalid} =
               Native.invoke_start(s3, bg, "a1", "http_get", "inv-1", true, %{}, attested)
    end
  end
end
