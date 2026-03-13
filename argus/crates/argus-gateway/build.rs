fn main() -> Result<(), Box<dyn std::error::Error>> {
    tonic_prost_build::configure().compile_protos(&["proto/argus/v1/gateway.proto"], &["proto"])?;
    Ok(())
}
