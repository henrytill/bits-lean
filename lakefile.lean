import Lake
open Lake DSL

package "flean" where
  -- add package configuration options here

@[default_target]
lean_lib «Flean» where
  -- add library configuration options here

@[default_target]
lean_exe "greet" where
  root := `Greet
