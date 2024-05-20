import Lake
open Lake DSL

package «feline_add» where
  -- add package configuration options here

lean_lib «FelineAdd» where
  -- add library configuration options here

@[default_target]
lean_exe «feline_add» where
  root := `Main
