import Lake
open Lake DSL

package «note» where
  -- add package configuration options here

lean_lib «Note» where
  -- add library configuration options here

@[default_target]
lean_exe «note» where
  root := `Main
