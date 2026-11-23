module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle634
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtCoordCompatOfPull
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle772
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle675
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle705
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle773
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle774
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle776
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle753
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle775
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum.EndThick

noncomputable section
namespace GlobalTheory.Mum.EndThick

theorem isCoordEnd_thickMap_compat : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e : ℕ) (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X) (u : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A a' a) rosatiε)) (F : thickObj R I e G ⟶ thickObj R I e G) (F' : thickObj R I (e + 1) G ⟶ thickObj R I (e + 1) G), IsCoordEnd (U.gt e) a a' h' u F → IsCoordEnd (U.gt (e + 1)) a a' h' u F' → thickMap R I e G ≫ F'.left = F.left ≫ thickMap R I e G := by
  intro R _ _ I D A G _ _ U e a a' h' u F F' hF hF'
  have hq := U.gt_q e
  have hO : GlobalTheory.LevelCompat.thickMapOver I e G ≫ (U.gt (e + 1)).pG = (U.gt e).pG := Over.OverMorphism.ext hq
  have hL : ∀ χ, thickMap R I e G ≫ (lift (toUnit _ ≫ D.toPre.c χ) (U.gt (e + 1)).pG).left =
      (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left := by
    intro χ
    have : GlobalTheory.LevelCompat.thickMapOver I e G ≫ lift (toUnit _ ≫ D.toPre.c χ) (U.gt (e + 1)).pG =
        lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG := by
      simp only [comp_lift, comp_toUnit_assoc, hO]
    exact congrArg (·.left) this
  refine GlobalTheory.TorusCoord.ext_of_val (U.gt (e + 1)) _ _ ?_ ?_
  · calc (thickMap R I e G ≫ F'.left) ≫ (U.gt (e + 1)).pG.left
          = thickMap R I e G ≫ ((U.gt (e + 1)).pG.left ≫ a.left) := by rw [Category.assoc, hF'.1]
      _ = (U.gt e).pG.left ≫ a.left := by rw [← Category.assoc, hq]
      _ = F.left ≫ (U.gt e).pG.left := hF.1.symm
      _ = (F.left ≫ thickMap R I e G) ≫ (U.gt (e + 1)).pG.left := by rw [Category.assoc, hq]
  · intro χ w J hJ
    have e1 := hF'.2 χ _ (thickMap R I e G) w J hJ
    have e2 := hF.2 χ _ (𝟙 _) w J hJ
    rw [Category.id_comp] at e2
    rw [e1, ← val_pull hJ, val_corr hJ (U.gt_t e χ), e2]
    congr 1
    · have e3 := val_pull hJ ((U.gt (e + 1)).t (h' χ)) (thickMap R I e G) (𝟙 _)
      rw [Category.id_comp] at e3
      rw [← e3, val_corr hJ (U.gt_t e _)]
    · rw [val_pull hJ, val_pull hJ, hL, Category.id_comp]

end GlobalTheory.Mum.EndThick
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES


theorem _root_.GlobalTheory.T.kernelStable_iff_pulledBack_identity : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (T Y : Scheme.{0}) (s₁ : T ⟶ Sp R) (s : Y ⟶ Sp R) (t : T ⟶ Y) (o₁ : Obj b N s₁) (o : Obj b N s) (m : ObjMap o₁ o t) (B₁ : Over T) [GrpObj B₁] [IsCommMonObj B₁] (B : Over Y) [GrpObj B] [IsCommMonObj B] (θ : B₁.left ⟶ B.left) (ψ₁ : o₁.A ⟶ B₁) (ψ : o.A ⟶ B), IsGrpPullback B₁ B t θ → m.φ ≫ ψ.left = ψ₁.left ≫ θ → (KerStableAt o ψ t ↔ KerStableAt o₁ ψ₁ (𝟙 T)) := by
  first | (exact @GlobalTheory.UPel.HT.ES.kerStableAt_iff_pull) | (exact GlobalTheory.UPel.HT.ES.kerStableAt_iff_pull) | (intros; apply GlobalTheory.UPel.HT.ES.kerStableAt_iff_pull  <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj

namespace GlobalTheory.AmpleGen

theorem not_NV_of_ge :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A →
      ∃ c : ℕ, ∀ P : LB A.left, P.IsLB → ∀ j : ℕ, c ≤ j → ¬ NV A P j := by
  intro K _ _ A _ hA
  haveI : IsProper A.hom := hA.proper
  haveI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have hsep : IsSeparated A.hom := inferInstance
  obtain ⟨m, V, hV, hc⟩ :=
    GlobalTheory.exists_fin_affine_cover (X := A.left) (V := ⊤) (by simpa using isCompact_univ)
  refine ⟨m, fun P hP j hj hNV => ?_⟩
  obtain ⟨κ, _, _, W, hW, hWc, hne⟩ := hNV
  obtain ⟨e⟩ := GlobalTheory.AbLaw.cechLB_homology_equiv_of_affine_covers K A.left A.hom P κ W (Fin m) V
    hP hsep hW hWc hV hc j
  apply hne
  have hz : IsZero ((GlobalTheory.AbLaw.cechLB A.hom P V).X j) :=
    GlobalTheory.AbLaw.isZero_cechLB_X A.hom P V (by simpa using hj)
  have h0 : IsZero ((GlobalTheory.AbLaw.cechLB A.hom P V).homology j) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (HomologicalComplex.ExactAt.of_isZero hz)
  have : Subsingleton ((GlobalTheory.AbLaw.cechLB A.hom P V).homology j) :=
    ModuleCat.isZero_iff_subsingleton.1 h0
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
    (ModuleCat.isZero_iff_subsingleton.2 e.toEquiv.subsingleton)

end GlobalTheory.AmpleGen
end
end

section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

theorem _root_.GlobalTheory.T.fock_action_lower_right_commutes_embedding : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (b b' : Fin Q) (G : Mdl P Q), fockAct1 P Q R 0 (Eab (Sum.inr b) (Sum.inr b')) (embR P Q R h k G) = embR P Q R h k (opR P Q R k (Sum.inr b) (Sum.inr b') G) := by
  first | exact @GlobalTheory.CharPair.fockAct1_inr_inr_embR | exact GlobalTheory.CharPair.fockAct1_inr_inr_embR | (intros; apply GlobalTheory.CharPair.fockAct1_inr_inr_embR <;> assumption)
end

section

open GlobalTheory.LeviCut

theorem _root_.GlobalTheory.T.dualWeyl_schur_endomorphism : GlobalTheory.LeviCut.NablaSchur := by
  first | exact @GlobalTheory.LeviCut.nablaSchur | exact GlobalTheory.LeviCut.nablaSchur | (intros; apply GlobalTheory.LeviCut.nablaSchur <;> assumption)
end

section

open GlobalTheory.LeviCut

theorem _root_.GlobalTheory.T.dualWeyl_restriction_rowOperators : GlobalTheory.LeviCut.ResDer := by
  first | exact @GlobalTheory.LeviCut.dualWeyl_resDer | exact GlobalTheory.LeviCut.dualWeyl_resDer | (intros; apply GlobalTheory.LeviCut.dualWeyl_resDer <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset


theorem _root_.GlobalTheory.T.cech_h1_pullback_refinement_compat : ∀ {R' R'' : Type} [CommRing R'] [CommRing R''] {X' X'' : Scheme.{0}} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R' →+* R''} {ψ : X'' ⟶ X'} (w : ψ ≫ s' = s'' ≫ spMap σ) {κ : Type} [LinearOrder κ] (D' : κ → X'.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D' i)) (D'' : κ → X''.Opens) (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D'' i)) (hle : ∀ i, D'' i ≤ ψ ⁻¹ᵁ D' i) (y : HO1 s'), (CoefMap.restrict (OAff s'') (cov_mono D'' hD'').functor.op).pull1 (pullHO1 w y) = (pullCoef w D' hD' D'' hD'' hle).pull1 ((CoefMap.restrict (OAff s') (cov_mono D' hD').functor.op).pull1 y) := by
  first | exact @GlobalTheory.CechPoset.restrict_pull1_pullHO1 | exact GlobalTheory.CechPoset.restrict_pull1_pullHO1 | (intros; apply GlobalTheory.CechPoset.restrict_pull1_pullHO1 <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset


theorem _root_.GlobalTheory.T.exists_cech_cocycle_cohomologous_posetOneCocycle : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (f : Z1 F), ∃ z : CC F 1, δ F 1 z = 0 ∧ ∃ g : C0 F, f.1 - e1 F z = d0 F g := by
  first | exact @GlobalTheory.CechPoset.exists_cech_cocycle_cohomologous | exact GlobalTheory.CechPoset.exists_cech_cocycle_cohomologous | (intros; apply GlobalTheory.CechPoset.exists_cech_cocycle_cohomologous <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset


theorem _root_.GlobalTheory.T.orderedCechToCatCochainsZero_coboundary_comm : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (c : CC F 0), d0 F (e0 F c) = e1 F (δ F 0 c) := by
  first | exact @GlobalTheory.CechPoset.orderedCech_cochainsZero_coboundary_comm | exact GlobalTheory.CechPoset.orderedCech_cochainsZero_coboundary_comm | (intros; apply GlobalTheory.CechPoset.orderedCech_cochainsZero_coboundary_comm <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset


theorem _root_.GlobalTheory.T.alternatingToOrderedCechDegreeTwo_mem_cocyclesTwo : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (c : CC F 2), δ F 2 c = 0 → e2 F c ∈ Z2 F := by
  first | exact @GlobalTheory.CechPoset.e2_mem_Z2_of_delta_eq_zero | exact GlobalTheory.CechPoset.e2_mem_Z2_of_delta_eq_zero | (intros; apply GlobalTheory.CechPoset.e2_mem_Z2_of_delta_eq_zero <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset


theorem _root_.GlobalTheory.T.baseChangeTrivialBundleCech_bijective_of_affine : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (h : IsPullback φ s' s (spMap (algebraMap R R'))) {κ : Type} [LinearOrder κ] [Fintype κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)), (∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) → ∀ p : ℕ, Function.Bijective (Φ h.w D hD' p) := by
  first | exact @GlobalTheory.CechPoset.Φ_bijective_of_affine | exact GlobalTheory.CechPoset.Φ_bijective_of_affine | (intros; apply GlobalTheory.CechPoset.Φ_bijective_of_affine <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset


theorem _root_.GlobalTheory.T.baseChangeTrivialBundleCech_one_tmul : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)), Φ w D hD' 0 ((1 : R') ⊗ₜ[R] one s D) = fun _ => 1 := by
  first | exact @GlobalTheory.CechPoset.Φ_one_tmul | exact GlobalTheory.CechPoset.Φ_one_tmul | (intros; apply GlobalTheory.CechPoset.Φ_one_tmul <;> assumption)
end
