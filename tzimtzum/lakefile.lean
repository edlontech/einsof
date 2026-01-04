import Lake
open Lake DSL

require veil from git
  "https://github.com/verse-lab/veil" @ "veil-2.0-preview"

package tzimtzum where
  version := v!"0.2.0"

@[default_target]
lean_lib TzimtzumV2 where
  globs := #[`TzimtzumV2]
