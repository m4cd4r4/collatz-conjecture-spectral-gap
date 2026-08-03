import Lake
open Lake DSL

package gapcert

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.27.0"

@[default_target]
lean_lib GapCertificate where
  roots := #[`GapCertificate, `OperatorChain, `CountingLemmas, `LevelMajorisation,
             `CollisionBound, `Assembly, `LemmaA, `TransferOperator, `CharacterBasis,
             `BlockVanishing, `OperatorBlock]
