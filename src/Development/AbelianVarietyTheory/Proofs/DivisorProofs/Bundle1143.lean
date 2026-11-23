module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1109
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditivityDefectGeneratorInvariantSameImage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1085
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1034
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationTaylorPowerSeriesInjectiveLocalRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PinchLift

theorem ratio_tele {G : Type*} [CommGroup G] (a b c : G) : a * b⁻¹ * (c * a⁻¹) = c * b⁻¹ := by
  rw [mul_comm c, ← _root_.mul_assoc, mul_comm a b⁻¹, mul_inv_cancel_right, mul_comm]

theorem ratio_cancel_left {G : Type*} [CommGroup G] (w a b : G) : a * b⁻¹ = w * a * (w * b)⁻¹ := by
  rw [mul_inv, ← _root_.mul_assoc, mul_comm w a, mul_inv_cancel_right]

theorem assemble : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (L' : LB X') (LZ : LB Z) (hL' : L'.IsLB) (hLZ : LZ.IsLB) (w : LB.Iso (L'.pull i') (LZ.pull p')), w.IsGen → (∀ x : X, ∃ (W : X.Opens) (s' : ∀ k, Γ(X', L'.U k ⊓ p ⁻¹ᵁ W)ˣ) (sZ : ∀ j, Γ(Z, LZ.U j ⊓ i ⁻¹ᵁ W)ˣ), x ∈ W ∧ GlobalTheory.PinchLift.GenOn L' (p ⁻¹ᵁ W) s' ∧ GlobalTheory.PinchLift.GenOn LZ (i ⁻¹ᵁ W) sZ ∧ GlobalTheory.PinchLift.Matched i' p' L' LZ w (p ⁻¹ᵁ W) (i ⁻¹ᵁ W) s' sZ) → ∃ e : Pic X, GlobalTheory.CechPic.pull p e = cls L' hL' ∧ GlobalTheory.CechPic.pull i e = cls LZ hLZ := by
  intro X X' Z Z' p i i' p' hsq hG L' LZ hL' hLZ w _ hloc
  have hc : i' ≫ p = p' ≫ i := hsq.w
  have hpt : ∀ z : Z', i (p' z) = p (i' z) := fun z => (congrArg (fun q => q z) hc).symm
  choose W s' sZ hxW hs' hsZ hM using hloc
  have r'e := fun x y => GlobalTheory.T.exists_ratio_unit_of_lineBundle_generators_on_opens _ L' hL' _ _ (s' y) (s' x) (hs' y) (hs' x)
  choose r' hr' using r'e
  have rZe := fun x y => GlobalTheory.T.exists_ratio_unit_of_lineBundle_generators_on_opens _ LZ hLZ _ _ (sZ y) (sZ x) (hsZ y) (hsZ x)
  choose rZ hrZ using rZe
  have le' : ∀ x y : X, p ⁻¹ᵁ (W x ⊓ W y) ≤ p ⁻¹ᵁ W y ⊓ p ⁻¹ᵁ W x := fun x y _ h => ⟨h.2, h.1⟩
  have leZ : ∀ x y : X, i ⁻¹ᵁ (W x ⊓ W y) ≤ i ⁻¹ᵁ W y ⊓ i ⁻¹ᵁ W x := fun x y _ h => ⟨h.2, h.1⟩
  have ge := fun x y => GlobalTheory.T.exists_unit_of_pinchingSquare_glued_units _ _ _ _ p i i' p' hc hG (W x ⊓ W y) (res (le' x y) (r' x y)) (res (leZ x y) (rZ x y)) (by
    intro z hz
    have hz' : i (p' z) ∈ W x ⊓ W y := (hpt z).symm ▸ hz
    obtain ⟨k, hk⟩ := exists_chart hL' (i' z)
    obtain ⟨j, hj⟩ := exists_chart hLZ (p' z)
    rw [gm_res _ z _ hz, gm_res _ z _ hz', hr' x y Z' i' z k hk hz.2 hz.1, hrZ x y Z' p' z j hj hz'.2 hz'.1,
      hM y z j k hj hk hz'.2 hz.2, hM x z j k hj hk hz'.1 hz.1]
    exact ratio_cancel_left _ _ _)
  choose g hgp hgi using ge
  have Gp : ∀ x y (t : X') (k : L'.ι), p t ∈ W x → p t ∈ W y → t ∈ L'.U k →
      gm p t (W x ⊓ W y) (g x y) = gm (𝟙 X') t (L'.U k ⊓ p ⁻¹ᵁ W y) (s' y k) * (gm (𝟙 X') t (L'.U k ⊓ p ⁻¹ᵁ W x) (s' x k))⁻¹ := by
    intro x y t k hx hy hk
    rw [hgp x y t ⟨hx, hy⟩, gm_res _ t _ (show t ∈ p ⁻¹ᵁ (W x ⊓ W y) from ⟨hx, hy⟩), hr' x y X' (𝟙 X') t k hk hy hx]
  have Gi : ∀ x y (t : Z) (k : LZ.ι), i t ∈ W x → i t ∈ W y → t ∈ LZ.U k →
      gm i t (W x ⊓ W y) (g x y) = gm (𝟙 Z) t (LZ.U k ⊓ i ⁻¹ᵁ W y) (sZ y k) * (gm (𝟙 Z) t (LZ.U k ⊓ i ⁻¹ᵁ W x) (sZ x k))⁻¹ := by
    intro x y t k hx hy hk
    rw [hgi x y t ⟨hx, hy⟩, gm_res _ t _ (show t ∈ i ⁻¹ᵁ (W x ⊓ W y) from ⟨hx, hy⟩), hrZ x y Z (𝟙 Z) t k hk hy hx]
  let E : LB X := ⟨X, W, g⟩
  have hE : E.IsLB := by
    refine ⟨eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxW x⟩, fun x => ?_, fun x y z => ?_⟩
    · refine GlobalTheory.T.unit_eq_of_germs_pinching_square _ _ _ _ p i i' p' hc hG _ _ _ (fun t ht => ?_) (fun t ht => ?_)
      · obtain ⟨k, hk⟩ := exists_chart hL' t
        rw [map_one, gm_res _ t _ ht]
        exact (Gp x x t k ht ht hk).trans (mul_inv_cancel _)
      · obtain ⟨k, hk⟩ := exists_chart hLZ t
        rw [map_one, gm_res _ t _ ht]
        exact (Gi x x t k ht ht hk).trans (mul_inv_cancel _)
    · refine GlobalTheory.T.unit_eq_of_germs_pinching_square _ _ _ _ p i i' p' hc hG _ _ _ (fun t ht => ?_) (fun t ht => ?_)
      · obtain ⟨k, hk⟩ := exists_chart hL' t
        rw [map_mul, gm_res _ t _ ht, gm_res _ t _ ht, gm_res _ t _ ht]
        show gm p t (W x ⊓ W y) (g x y) * gm p t (W y ⊓ W z) (g y z) = gm p t (W x ⊓ W z) (g x z)
        rw [Gp x y t k ht.1.1 ht.1.2 hk, Gp y z t k ht.1.2 ht.2 hk, Gp x z t k ht.1.1 ht.2 hk]
        exact ratio_tele _ _ _
      · obtain ⟨k, hk⟩ := exists_chart hLZ t
        rw [map_mul, gm_res _ t _ ht, gm_res _ t _ ht, gm_res _ t _ ht]
        show gm i t (W x ⊓ W y) (g x y) * gm i t (W y ⊓ W z) (g y z) = gm i t (W x ⊓ W z) (g x z)
        rw [Gi x y t k ht.1.1 ht.1.2 hk, Gi y z t k ht.1.2 ht.2 hk, Gi x z t k ht.1.1 ht.2 hk]
        exact ratio_tele _ _ _
  refine ⟨cls E hE, ?_, ?_⟩
  · rw [← cls_pull hE p (pull_isLB hE p)]
    exact (cls_eq_iff _ _).2 (LBIso.symm (GlobalTheory.T.lineBundle_iso_pullback_of_local_unit_generators _ _ p L' X W g s' hs' Gp))
  · rw [← cls_pull hE i (pull_isLB hE i)]
    exact (cls_eq_iff _ _).2 (LBIso.symm (GlobalTheory.T.lineBundle_iso_pullback_of_local_unit_generators _ _ i LZ X W g sZ hsZ Gi))

end GlobalTheory.PinchLift
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.LatEnt

theorem _root_.GlobalTheory.T.exists_integral_residue_system_finiteAdeles_mod : ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 0 < N → ∃ R : Finset (Af E), (∀ a ∈ R, ∀ w, Valued.v (a w) ≤ 1) ∧ ∀ z : Af E, (∀ w, Valued.v (z w) ≤ 1) → ∃! a, a ∈ R ∧ ∀ w, Valued.v (z w - a w) ≤ radN E N w := by
  first | exact @GlobalTheory.CMVal.LatEnt.Res.exists_residues | exact GlobalTheory.CMVal.LatEnt.Res.exists_residues | (intros; apply GlobalTheory.CMVal.LatEnt.Res.exists_residues <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.LatEnt

theorem _root_.GlobalTheory.T.integralUnitCongruenceSubgroup_relIndex_ne_zero : ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 0 < N → (congr (radN E N)).relIndex (congr (fun _ => 1)) ≠ 0 := by
  first | exact @GlobalTheory.CMVal.LatEnt.relIndex_congr_radN_ne_zero | exact GlobalTheory.CMVal.LatEnt.relIndex_congr_radN_ne_zero | (intros; apply GlobalTheory.CMVal.LatEnt.relIndex_congr_radN_ne_zero <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer


theorem _root_.GlobalTheory.T.additivityDefect_generator_invariant_same_image : ∀ (S : Scheme.{0}) (A A' N T : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') [IsMonHom q] (χ : Γ((N ⊗ T).left, ⊤)ˣ) (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ), IsMonHom i → IsPullback i (toUnit N) q η[A'] → IsCharacter χ → IsEquivGen i q χ M e → ∀ (Z : Scheme.{0}) (y₁ y₂ : Z ⟶ (A ⊗ (A ⊗ T)).left), y₁ ≫ (pmap2 q T).left = y₂ ≫ (pmap2 q T).left → ∀ (k : (addBundle M).ι) (W : Z.Opens) (h₁ : W ≤ y₁ ⁻¹ᵁ ((pmap2 q T).left ⁻¹ᵁ (addBundle M).U k)) (h₂ : W ≤ y₂ ⁻¹ᵁ ((pmap2 q T).left ⁻¹ᵁ (addBundle M).U k)), res h₁ (pullU y₁ _ (addGen q M e k)) = res h₂ (pullU y₂ _ (addGen q M e k)) := by
  first | exact @GlobalTheory.CharKer.addGen_invariant | exact GlobalTheory.CharKer.addGen_invariant | (intros; apply GlobalTheory.CharKer.addGen_invariant <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer


theorem _root_.GlobalTheory.T.isPullbackLineBundleGenerator_additivityDefect : ∀ (S : Scheme.{0}) (A A' T : Over S) [MonObj A] [MonObj A'] (q : A ⟶ A') [IsMonHom q] (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ), IsPullGen (pmap q T).left M e → IsPullGen (pmap2 q T).left (addBundle M) (addGen q M e) := by
  first | exact @GlobalTheory.CharKer.isPullGen_addGen | exact GlobalTheory.CharKer.isPullGen_addGen | (intros; apply GlobalTheory.CharKer.isPullGen_addGen <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer


theorem _root_.GlobalTheory.T.prodMapPairTimesIdentity_flat_surjective_affine : ∀ (S : Scheme.{0}) (A A' T : Over S) (q : A ⟶ A'), Flat q.left → Surjective q.left → IsAffineHom q.left → Flat (pmap2 q T).left ∧ Surjective (pmap2 q T).left ∧ IsAffineHom (pmap2 q T).left := by
  first | exact @GlobalTheory.CharKer.pmap2_flat_surjective_isAffineHom | exact GlobalTheory.CharKer.pmap2_flat_surjective_isAffineHom | (intros; apply GlobalTheory.CharKer.pmap2_flat_surjective_isAffineHom <;> assumption)
end

section

noncomputable section

open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep

namespace GlobalTheory.SphGal

section Local

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem hasDiv_mul_mul {O : Subring L} {d : List ℤ} {g : GL (Fin n) L} (h : HasDiv O d g) {a b : GL (Fin n) L}
    (ha : a ∈ GLint (Fin n) O) (hb : b ∈ GLint (Fin n) O) : HasDiv O d (a * g * b) := by
  obtain ⟨ϖ, hϖ, a', ha', b', hb', e⟩ := h
  refine ⟨ϖ, hϖ, a * a', mul_mem ha ha', b' * b, mul_mem hb' hb, ?_⟩
  simp only [Units.val_mul, e, Matrix.mul_assoc]

theorem HasDiv.exists_eq_mul_mul {O : Subring L} (hO : ∀ x : L, Valued.v x ≤ 1 → x ∈ O) {d : List ℤ}
    {g s : GL (Fin n) L} (hg : HasDiv O d g) (hs : HasDiv O d s) :
    ∃ a b : GLint (Fin n) O, g = a * s * b := by
  first
  | exact @_root_.GlobalTheory.DoubleCosetDivisors.main
  | exact _root_.GlobalTheory.DoubleCosetDivisors.main
  | (apply _root_.GlobalTheory.DoubleCosetDivisors.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.DoubleCosetDivisors.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DoubleCosetDivisors.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DoubleCosetDivisors.main ..)

end Local

end GlobalTheory.SphGal

end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroPt

open GlobalTheory.LieVB GlobalTheory.Conormal

theorem kappa_cotMap_cst_smul (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M]
    [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (A : Over (Sp O)) [GrpObj A] (z : TM O M ⟶ A)
    (h : zeroSec O M ≫ z = η[A]) (c : O) (w : Γ(omega A, ⊤)) :
    kappa O M ((cotMap z h).app ⊤ (cst O c • w)) = c • kappa O M ((cotMap z h).app ⊤ w) := by
  rw [show (cotMap z h).app ⊤ (cst O c • w) = cst O c • (cotMap z h).app ⊤ w from
    (QCoh.appLinear (cotMap z h) ⊤).map_smul (cst O c) w]
  obtain ⟨b, hb⟩ := (isChart O M).d_surjective (sec_hom (zeroSec O M)) ((cotMap z h).app ⊤ w)
  rw [← hb]
  have key : cst O c • d (sec_hom (zeroSec O M)) (isChart O M).le b =
      d (sec_hom (zeroSec O M)) (isChart O M).le ((TM O M).hom.appLE ⊤ ⊤ le_top (cst O c) * b) := by
    rw [d_mul]
    erw [d_base (sec_hom (zeroSec O M)) (isChart O M).le le_top (cst O c)]
    rw [smul_zero, add_zero]
    erw [appLE_base (sec_hom (zeroSec O M)) _ _ le_rfl]
    rfl
  rw [key, kappa_d, kappa_d, map_mul, toTsze_base, TrivSqZeroExt.snd_mul]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem Phi_smul (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
    [IsCentralScalar O M] (A : Over (Sp O)) [GrpObj A] (z : TM O M ⟶ A)
    (h : zeroSec O M ≫ z = η[A]) (c : O) (w : Wmod A) :
    Phi z h (c • w) = c • Phi z h w :=
  kappa_cotMap_cst_smul O M A z h c w

end GlobalTheory.SqZeroPt
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FramesFGP

theorem finite_projective_top {O : Type} [CommRing O] (F : (Sp O).Modules)
    (h : ∀ x : Sp O, ∃ (U : (Sp O).Opens) (n : ℕ) (s : Fin n → Γ(F, U)),
      x ∈ U ∧ GlobalTheory.VB.IsFrame s) :
    Module.Finite Γ(Sp O, ⊤) Γ(F, ⊤) ∧ Module.Projective Γ(Sp O, ⊤) Γ(F, ⊤) := by
  haveI : F.IsQuasicoherent := GlobalTheory.OmegaGlobal.isQuasicoherent_of_frames h
  choose U n e hx he using h
  have hU := isAffineOpen_top (Sp O)
  let s : Set Γ(Sp O, ⊤) := {f | ∃ x, (Sp O).basicOpen f ≤ U x}
  have hs : Ideal.span s = ⊤ := by
    rw [← hU.self_le_iSup_basicOpen_iff]
    intro y _
    obtain ⟨f, hf, hyf⟩ := hU.exists_basicOpen_le (V := U y) ⟨y, hx y⟩ (by simp)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, y, hf⟩, hyf⟩
  haveI (g : s) := hU.isLocalization_basicOpen g.1
  haveI (g : s) := GlobalTheory.QCoh.isLocalizedModule_resBasicOpen F hU g.1
  let b (g : s) : Module.Basis (Fin (n g.2.choose)) Γ(Sp O, (Sp O).basicOpen g.1)
      Γ(F, (Sp O).basicOpen g.1) := (he g.2.choose).basis g.2.choose_spec
  haveI (g : s) : Module.Free Γ(Sp O, (Sp O).basicOpen g.1) Γ(F, (Sp O).basicOpen g.1) :=
    .of_basis (b g)
  haveI (g : s) : Module.Finite Γ(Sp O, (Sp O).basicOpen g.1) Γ(F, (Sp O).basicOpen g.1) :=
    .of_basis (b g)
  haveI (g : s) : Module.Flat Γ(Sp O, ⊤) Γ(F, (Sp O).basicOpen g.1) := by
    haveI : Module.Flat Γ(Sp O, ⊤) Γ(Sp O, (Sp O).basicOpen g.1) :=
      IsLocalization.flat _ (Submonoid.powers g.1)
    exact Module.Flat.trans Γ(Sp O, ⊤) Γ(Sp O, (Sp O).basicOpen g.1) _
  haveI hfp : Module.FinitePresentation Γ(Sp O, ⊤) Γ(F, ⊤) :=
    Module.FinitePresentation.of_localizationSpan' s hs
      (Mₚ := fun g : s => Γ(F, (Sp O).basicOpen g.1))
      (Rₚ := fun g : s => Γ(Sp O, (Sp O).basicOpen g.1))
      (fun g => GlobalTheory.QCoh.resBasicOpen F g.1) fun _ => Module.finitePresentation_of_projective _ _
  haveI : Module.Flat Γ(Sp O, ⊤) Γ(F, ⊤) :=
    Module.flat_of_isLocalized_span Γ(Sp O, ⊤) Γ(F, ⊤) s hs
      (fun g : s => Γ(F, (Sp O).basicOpen g.1)) (fun g => GlobalTheory.QCoh.resBasicOpen F g.1)
      fun _ => inferInstance
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

end GlobalTheory.FramesFGP

theorem GlobalTheory.FramesFGP.finite_projective_wmod : ∀ (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A],
    (∀ x : Sp O, ∃ (U : (Sp O).Opens) (n : ℕ) (s : Fin n → Γ(GlobalTheory.LieVB.omega A, U)),
      x ∈ U ∧ GlobalTheory.VB.IsFrame s) → Module.Finite O (Wmod A) ∧ Module.Projective O (Wmod A) := by
  intro O _ A _ h
  obtain ⟨h1, h2⟩ := GlobalTheory.FramesFGP.finite_projective_top (GlobalTheory.LieVB.omega A) h
  letI : Module Γ(Sp O, ⊤) (Wmod A) := inferInstanceAs (Module Γ(Sp O, ⊤) Γ(GlobalTheory.LieVB.omega A, ⊤))
  haveI : Module.Finite Γ(Sp O, ⊤) (Wmod A) := h1
  haveI : Module.Projective Γ(Sp O, ⊤) (Wmod A) := h2
  have hb : Function.Bijective (GlobalTheory.LieVB.cst O) :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of O)).inv
  let E : O ≃+* Γ(Sp O, ⊤) := RingEquiv.ofBijective (GlobalTheory.LieVB.cst O) hb
  letI : Algebra O Γ(Sp O, ⊤) := (GlobalTheory.LieVB.cst O).toAlgebra
  haveI : IsScalarTower O Γ(Sp O, ⊤) (Wmod A) := .of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Finite O Γ(Sp O, ⊤) :=
    Module.Finite.of_surjective (Algebra.linearMap O Γ(Sp O, ⊤)) hb.2
  refine ⟨Module.Finite.trans Γ(Sp O, ⊤) (Wmod A), ?_⟩
  haveI : RingHomInvPair (E.symm : Γ(Sp O, ⊤) →+* O) (E : O →+* Γ(Sp O, ⊤)) :=
    ⟨RingHom.ext E.apply_symm_apply, RingHom.ext E.symm_apply_apply⟩
  haveI : RingHomInvPair (E : O →+* Γ(Sp O, ⊤)) (E.symm : Γ(Sp O, ⊤) →+* O) := .symm _ _
  let e : Wmod A ≃ₛₗ[(E.symm : Γ(Sp O, ⊤) →+* O)] Wmod A :=
    { toFun := id
      invFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => by
        change r • m = GlobalTheory.LieVB.cst O (E.symm r) • m
        congr 1
        exact (E.apply_symm_apply r).symm
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Module.Projective.of_equiv e

end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open GlobalTheory.LieVB GlobalTheory.Conormal

namespace GlobalTheory.SqZeroPt

theorem zeroSec_sqZeroMap (O : Type) [CommRing O] (M N : Type) [AddCommGroup M] [Module O M]
    [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N]
    [IsCentralScalar O N] (l : M →ₗ[O] N) :
    zeroSec O N ≫ GlobalTheory.GrpTangent.sqZeroMap l = zeroSec O M := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  simp

theorem Phi_sqZeroMap_comp : ∀ (O : Type) [CommRing O] (M N : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N] [IsCentralScalar O N] (A : Over (Sp O)) [GrpObj A] (l : M →ₗ[O] N) (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O N ≫ (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) = η[A]) (w : Wmod A), Phi (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) h' w = l (Phi z h w) := by
  intro O _ M N _ _ _ _ _ _ _ _ A _ l z h h' w
  have hl := zeroSec_sqZeroMap O M N l
  rw [Phi_apply, Phi_apply, ← cotMap_comp h hl rfl h']
  obtain ⟨b, hb⟩ := (isChart O M).d_surjective (sec_hom (zeroSec O M)) ((cotMap z h).app ⊤ w)
  have e : (ConcreteCategory.hom (Scheme.Modules.Hom.app (cotMap z h ≫ cotMap (GlobalTheory.GrpTangent.sqZeroMap l) hl) ⊤)) w = (ConcreteCategory.hom (Scheme.Modules.Hom.app (cotMap (GlobalTheory.GrpTangent.sqZeroMap l) hl) ⊤)) ((ConcreteCategory.hom (Scheme.Modules.Hom.app (cotMap z h) ⊤)) w) := rfl
  rw [e, ← hb, cotMap_d (GlobalTheory.GrpTangent.sqZeroMap l) hl _ (le_preimage_top _ ⊤) (le_preimage_top _ ⊤), kappa_d, kappa_d, appLE_top]
  change (toTsze O N ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map l).toRingHom)).appTop b)).snd = _
  rw [show toTsze O N ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map l).toRingHom)).appTop b) = TrivSqZeroExt.map l (toTsze O M b) from
    congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (TrivSqZeroExt.map l).toRingHom)) b)]
  simp

end GlobalTheory.SqZeroPt
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.CuspMult

section
variable {H H' : Type} [Group H] [Group H'] {X : Type} [AddCommGroup X] [Module ℂ X]

def subrepCompIso (ρ : Representation ℂ H' X) (φ : H ≃* H') :
    Subrepresentation (ρ.comp φ.toMonoidHom : Representation ℂ H X) ≃o Subrepresentation ρ where
  toFun U := ⟨U.toSubmodule, fun g v hv => by
    have h := U.apply_mem_toSubmodule (φ.symm g) hv
    simpa using h⟩
  invFun U := ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (φ g) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_comp_mulEquiv (ρ : Representation ℂ H' X) (φ : H ≃* H') (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp φ.toMonoidHom : Representation ℂ H X) := by
  haveI : IsSimpleOrder (Subrepresentation ρ) := h
  exact (subrepCompIso ρ φ).isSimpleOrder

theorem isAdmissible_comp_equiv [TopologicalSpace H] [TopologicalSpace H'] (ρ : Representation ℂ H' X) (Φ : H ≃ₜ* H')
    (h : GlobalTheory.PRep.IsAdmissible ρ) :
    GlobalTheory.PRep.IsAdmissible (ρ.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H X) := by
  refine ⟨fun v => (h.1 v).preimage Φ.continuous, fun K hKo hKc => ?_⟩
  have e : GlobalTheory.PRep.fixed (ρ.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H X) K =
      GlobalTheory.PRep.fixed ρ (K.map Φ.toMulEquiv.toMonoidHom) := by
    ext v
    constructor
    · rintro hv ⟨_, g, hg, rfl⟩
      exact hv ⟨g, hg⟩
    · intro hv g
      exact hv ⟨_, g.1, g.2, rfl⟩
  rw [e]
  exact h.2 _ (Φ.toHomeomorph.isOpenMap _ hKo) (hKc.image Φ.continuous)

end

theorem isDecomp_comp_equiv : ∀ (H H' : Type) [Group H] [TopologicalSpace H] [Group H'] [TopologicalSpace H'] (X : Type)
    [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H' X) (C : Submodule ℂ X) (Φ : H ≃ₜ* H'),
    IsDecomp ρ C → IsDecomp (ρ.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H X) C := by
  intro H H' _ _ _ _ X _ _ ρ C Φ h x hx ho
  have ho' : IsOpen {g : H' | ρ g x = x} := by
    have := ho.preimage Φ.symm.continuous
    convert this using 1
    ext g
    show ρ g x = x ↔ ρ (Φ (Φ.symm g)) x = x
    rw [Φ.apply_symm_apply]
  have hm := h x hx ho'
  refine (?_ : irrSum ρ C ≤ irrSum (ρ.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H X) C) hm
  refine iSup₂_le fun U hU => ?_
  refine le_iSup₂_of_le (f := fun (U : Subrepresentation (ρ.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H X))
    (_ : U.toSubmodule ≤ C ∧ U.toRepresentation.IsIrreducible ∧ GlobalTheory.PRep.IsAdmissible U.toRepresentation) => U.toSubmodule)
    ((subrepCompIso ρ Φ.toMulEquiv).symm U) ⟨hU.1, ?_, ?_⟩ le_rfl
  · exact isIrreducible_comp_mulEquiv U.toRepresentation Φ.toMulEquiv hU.2.1
  · exact isAdmissible_comp_equiv U.toRepresentation Φ hU.2.2

end GlobalTheory.CuspMult
end

section

open IsLocalRing GlobalTheory.FormalOrigin

theorem _root_.GlobalTheory.T.derivationTaylorPowerSeries_injective_localRing : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [Algebra ℚ R] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (inc : R →+* A) (ev : A →+* R), (∀ r, ev (inc r) = r) → ∀ (n : ℕ) (ds : Fin n → Derivation ℤ A A) (z : Fin n → A), (∀ i, ev (z i) = 0) → (∀ a i, ev (ds a (z i)) = if a = i then 1 else 0) → maximalIdeal A = (maximalIdeal R).map inc ⊔ Ideal.span (Set.range z) → ∀ f, taylor ev (fun i => ⇑(ds i)) f = 0 → f = 0 := by
  first | exact @GlobalTheory.TaylorInj.taylor_injective | exact GlobalTheory.TaylorInj.taylor_injective | (intros; apply GlobalTheory.TaylorInj.taylor_injective <;> assumption)
end
