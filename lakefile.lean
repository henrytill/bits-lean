import Lake
open Lake DSL

package "bits" where
  -- add package configuration options here

@[default_target]
lean_lib «Bits» where
  -- add library configuration options here

@[default_target]
lean_exe "greet" where
  root := `Greet

@[default_target]
lean_exe "cat" where
  root := `Cat
