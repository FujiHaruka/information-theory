import Lake

open System Lake DSL

package InformationTheory where
  version := v!"1.0.1"
  -- Distribute prebuilt oleans as a GitHub release asset. When this package is used as a
  -- dependency, Lake downloads the archive instead of rebuilding from source; if the fetch
  -- fails it warns and falls back to a source build. The library has no executable target,
  -- so the artifacts are platform independent and a single archive serves every host.
  releaseRepo := "https://github.com/FujiHaruka/information-theory"
  buildArchive := "InformationTheory.tar.gz"
  preferReleaseBuild := true

-- Development-only tooling (the Mathlib search tool loogle), enabled with `-R -Kdev=on`. It is
-- kept out of the default dependency set so that consumers of the library do not clone the
-- toolchain behind it, and is declared ahead of Mathlib so that Mathlib's pinned revisions of
-- the shared transitive dependencies take precedence.
meta if (get_config? dev).isSome then
require loogle from git "https://github.com/nomeata/loogle"@"3a988dbfa601ddbbfd9330d90c45e7a68263b9c7"

require "leanprover-community" / mathlib @ git "v4.31.0"

@[default_target] lean_lib InformationTheory where leanOptions :=
  #[⟨`weak.linter.mathlibStandardSet, true⟩, ⟨`weak.linter.unusedFintypeInType, false⟩]
