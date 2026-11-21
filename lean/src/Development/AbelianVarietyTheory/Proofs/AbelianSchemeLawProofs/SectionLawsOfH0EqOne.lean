import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankSectionsLineBundlePowEqPow
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecMInvariantEqBotOrUnivAtGeometricPoint
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FirstCohomologyVanishesDescent
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FirstCohomologyVanishesOfIsoOfIsGen
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsMulEqSmulOneOfMulVecInjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankOfIsSecBasis
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsOfCubeBundleGenerator
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTheoremAndSectionsFiniteGrowthAbelianVariety

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw

theorem section_laws_of_h0_eq_one :
    (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))),
      Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)
        (SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K)))) = 1) →
      SecBaseChangeAnySt ∧ SecBaseChangeSt ∧ SecTwistSt := by
  intro h1
  have gi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
  have g := GlobalTheory.globalFns_holds
  have pbc := GlobalTheory.polBaseChange_holds
  have cg := GlobalTheory.AbLaw.CubeAssembly.cube_gen
  have grow := GlobalTheory.AbLaw.CubeAssembly.sections_growth
  have mulq := GlobalTheory.AbLaw.FromCube.mulA_props cg
  have rel := GlobalTheory.AbLaw.FromCube.sec_split cg
  have sq := (GlobalTheory.AbSquare.square_of_cube cg).1
  have neg := GlobalTheory.exists_gen_negLB g
  have mp := (GlobalTheory.MulPull.mulPull_of_cube_of_symm cg neg).1
  have gal := GlobalTheory.torsion_invariant_descends mulq
  have tw := GlobalTheory.twisted_pow_translate sq mulq
  have proj := GlobalTheory.AbLaw.polAV_veryAmpleBy pbc
  have h0 : GlobalSectionsRankAlgClosed :=
    GlobalTheory.FinrankGrowthBounds.finrank_sections_lineBundlePow_eq_pow gi h1 rel grow mulq
  have h0T := (GlobalTheory.secM_invariant_eq_bot_or_univ_at_geometric_point pbc).1 h0
  have van := GlobalTheory.AbLaw.PowVanish.first_cohomology_vanishes_powers
    proj GlobalTheory.T.serre_vanishing_very_ample.1 GlobalTheory.AbLaw.h1Zero_of_isIso mp mulq gal
  have perf := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj
  have matrixBasis := GlobalTheory.exists_matrix_basis_ker_of_exact_at_point
  obtain ⟨sbcAny, sbc⟩ := GlobalTheory.AbLaw.SecBC.secBaseChange_of_perf
    perf proj van GlobalTheory.AbLaw.h1Zero_of_isIso matrixBasis pbc h0T
  have stw : SecTwistSt := GlobalTheory.SecTwist.secTwist_of_perf
    perf proj van GlobalTheory.AbLaw.h1Zero_of_isIso matrixBasis pbc h0T tw
  exact ⟨sbcAny, sbc, stw⟩

end GlobalTheory.AbLaw
