import Lake
open Lake DSL

package «lean-keep» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «Keep» where
  srcDir := "."

lean_exe «smoke» where
  root := `Smoke
