import Lake
open Lake DSL

package «TPL_seminar» where
  -- add package configuration options here

lean_lib «TPLSeminar» where
  -- add library configuration options here

@[default_target]
lean_exe «tpl_seminar» where
  root := `Main
