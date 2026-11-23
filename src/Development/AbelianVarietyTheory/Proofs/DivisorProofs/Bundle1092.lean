module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1056
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftOneParameterQuotientTorus
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteOfNotLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle071
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle061
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle393
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1058
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Preserves.Over
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle021
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer


theorem _root_.GlobalTheory.T.lineBundle_trivial_of_invariant_pullback_generator : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y), Flat p → Surjective p → IsAffineHom p → ∀ (M : LB Y) (e : ∀ k, Γ(X, p ⁻¹ᵁ M.U k)ˣ), IsPullGen p M e → (∀ (Z : Scheme.{0}) (y₁ y₂ : Z ⟶ X), y₁ ≫ p = y₂ ≫ p → ∀ (k : M.ι) (W : Z.Opens) (h₁ : W ≤ y₁ ⁻¹ᵁ (p ⁻¹ᵁ M.U k)) (h₂ : W ≤ y₂ ⁻¹ᵁ (p ⁻¹ᵁ M.U k)), res h₁ (pullU y₁ _ (e k)) = res h₂ (pullU y₂ _ (e k))) → Triv M := by
  first | exact @GlobalTheory.CharKer.triv_of_isPullGen_of_invariant | exact GlobalTheory.CharKer.triv_of_isPullGen_of_invariant | (intros; apply GlobalTheory.CharKer.triv_of_isPullGen_of_invariant <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TorusPic

theorem triv_of_isLB_splitTorus : ∀ (A : Type) [CommRing A], IsField A → ∀ (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (N : LB (splitTorus (Sp A) X).left), N.IsLB → Triv N := by
  intro A _ hA X _ _ _ N hN
  letI := hA.toField
  have : IsAffine (splitTorus (Sp A) X).left := by
    have := Diag.isAffineHom_hom (Sp A) X
    exact isAffine_of_isAffineHom (splitTorus (Sp A) X).hom
  have := GlobalTheory.SS.LiftTorus.subsingleton_pic_torus A X
  exact GlobalTheory.LB.exists_isGen_of_subsingleton_pic_top hN

end GlobalTheory.TorusPic
end
end

section

open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
open GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.DegCmp
variable {X : Scheme.{0}}

theorem pull_pw_g (H : LB X) (φ : X ⟶ X) (t : ℤ) (j j' : PUnit.{1} → H.ι) :
    ((GlobalTheory.AbLaw.pw H t).pull φ).g j j' = ((H.pull φ).g j j') ^ t := by
  simp only [LB.pull, LB.LinComb, GlobalTheory.AbLaw.pw, Finset.univ_unique, Finset.prod_singleton, zpow_one]
  erw [map_zpow, map_zpow]
  rfl

abbrev E (H : LB X) (φ : X ⟶ X) (q : ℕ) : LB X := ReciprocityTheory.ChartRestriction.G.Semi.LB.div (GlobalTheory.AbLaw.pw H (q : ℤ)) (H.pull φ)

def loc (H : LB X) (φ : X ⟶ X) (q t : ℕ) (σ : LB.Sec (E H φ q))
    (a : SecOn ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) (p : H.ι × (PUnit.{1} → H.ι)) : Γ(X, (E H φ q).U p) :=
  σ.f p ^ t *
    rs X (le_inf le_top inf_le_right : (E H φ q).U p ≤ ⊤ ⊓ ((GlobalTheory.AbLaw.pw H t).pull φ).U p.2) (GlobalTheory.LB.coord a p.2)

theorem units_id {U₁ U₂ W : X.Opens} (q t : ℕ) (u : Γ(X, U₁)ˣ) (v w : Γ(X, U₂)ˣ) (hw : w = v ^ (t : ℤ))
    (h₁ : W ≤ U₁) (h₂ : W ≤ U₂) :
    (res h₁ (u ^ (q : ℤ)) * (res h₂ v)⁻¹) ^ t * res h₂ w = res h₁ (u ^ ((q * t : ℕ) : ℤ)) := by
  subst hw
  simp only [map_zpow, ← zpow_natCast, mul_zpow, inv_zpow, ← zpow_mul, Nat.cast_mul]
  group

theorem loc_compat (H : LB X) (φ : X ⟶ X) (q t : ℕ) (σ : LB.Sec (E H φ q))
    (a : SecOn ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) (p p' : H.ι × (PUnit.{1} → H.ι)) :
    rs X (inf_le_left : (E H φ q).U p ⊓ (E H φ q).U p' ≤ (E H φ q).U p) (loc H φ q t σ a p) =
      rs X (inf_le_inf inf_le_left inf_le_left : (E H φ q).U p ⊓ (E H φ q).U p' ≤ H.U p.1 ⊓ H.U p'.1)
        ((GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)).g p.1 p'.1).val *
      rs X (inf_le_right : (E H φ q).U p ⊓ (E H φ q).U p' ≤ (E H φ q).U p') (loc H φ q t σ a p') := by
  have e1 : rs X (inf_le_left : (E H φ q).U p ⊓ (E H φ q).U p' ≤ (E H φ q).U p) (σ.f p) =
      ((E H φ q).g p p').val *
      rs X (inf_le_right : (E H φ q).U p ⊓ (E H φ q).U p' ≤ (E H φ q).U p') (σ.f p') := by
    have := GlobalTheory.LB.sec_rel σ p p' (W := (E H φ q).U p ⊓ (E H φ q).U p') inf_le_left inf_le_right le_rfl
    rw [this]
    congr 1
    exact rs_self _ _
  have e2 : rs X (le_inf le_top (inf_le_left.trans inf_le_right) :
        (E H φ q).U p ⊓ (E H φ q).U p' ≤ ⊤ ⊓ ((GlobalTheory.AbLaw.pw H t).pull φ).U p.2) (GlobalTheory.LB.coord a p.2) =
      rs X (inf_le_inf inf_le_right inf_le_right :
        (E H φ q).U p ⊓ (E H φ q).U p' ≤ ((GlobalTheory.AbLaw.pw H t).pull φ).U p.2 ⊓ ((GlobalTheory.AbLaw.pw H t).pull φ).U p'.2)
        (((GlobalTheory.AbLaw.pw H t).pull φ).g p.2 p'.2).val *
      rs X (le_inf le_top (inf_le_right.trans inf_le_right) :
        (E H φ q).U p ⊓ (E H φ q).U p' ≤ ⊤ ⊓ ((GlobalTheory.AbLaw.pw H t).pull φ).U p'.2) (GlobalTheory.LB.coord a p'.2) :=
    GlobalTheory.LB.coord_rel a p.2 p'.2 _ _ _
  have key : ((E H φ q).g p p') ^ t *
      res (inf_le_inf inf_le_right inf_le_right :
        (E H φ q).U p ⊓ (E H φ q).U p' ≤ ((GlobalTheory.AbLaw.pw H t).pull φ).U p.2 ⊓ ((GlobalTheory.AbLaw.pw H t).pull φ).U p'.2)
        (((GlobalTheory.AbLaw.pw H t).pull φ).g p.2 p'.2) =
      res (inf_le_inf inf_le_left inf_le_left : (E H φ q).U p ⊓ (E H φ q).U p' ≤ H.U p.1 ⊓ H.U p'.1)
        (H.g p.1 p'.1 ^ ((q * t : ℕ) : ℤ)) :=
    units_id q t (H.g p.1 p'.1) ((H.pull φ).g p.2 p'.2) _ (pull_pw_g H φ t p.2 p'.2) _ _
  have kv : ((E H φ q).g p p').val ^ t *
      rs X (inf_le_inf inf_le_right inf_le_right :
        (E H φ q).U p ⊓ (E H φ q).U p' ≤ ((GlobalTheory.AbLaw.pw H t).pull φ).U p.2 ⊓ ((GlobalTheory.AbLaw.pw H t).pull φ).U p'.2)
        (((GlobalTheory.AbLaw.pw H t).pull φ).g p.2 p'.2).val =
      rs X (inf_le_inf inf_le_left inf_le_left : (E H φ q).U p ⊓ (E H φ q).U p' ≤ H.U p.1 ⊓ H.U p'.1)
        ((GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)).g p.1 p'.1).val := by
    have := congrArg Units.val key
    rw [Units.val_mul, Units.val_pow_eq_pow_val] at this
    exact this
  unfold loc
  simp only [map_mul, map_pow, rs_rs]
  rw [e1, e2, mul_pow]
  linear_combination (rs X (inf_le_right : (E H φ q).U p ⊓ (E H φ q).U p' ≤ (E H φ q).U p') (σ.f p')) ^ t *
    rs X (le_inf le_top (inf_le_right.trans inf_le_right) :
        (E H φ q).U p ⊓ (E H φ q).U p' ≤ ⊤ ⊓ ((GlobalTheory.AbLaw.pw H t).pull φ).U p'.2) (GlobalTheory.LB.coord a p'.2) * kv
end GlobalTheory.DegCmp

namespace GlobalTheory.DegCmp
variable {X : Scheme.{0}}

theorem top_le_iSup_E {H : LB X} (hH : H.IsLB) (φ : X ⟶ X) (q : ℕ) : (⊤ : X.Opens) ≤ ⨆ p, (E H φ q).U p := by
  intro x _
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge (trivial : x ∈ (⊤ : X.Opens)))
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge (trivial : φ x ∈ (⊤ : X.Opens)))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, fun _ => j), hi, Set.mem_iInter.2 fun _ => hj⟩

theorem existsUnique_img {H : LB X} (hH : H.IsLB) (φ : X ⟶ X) (q t : ℕ) (σ : LB.Sec (E H φ q))
    (a : SecOn ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) :
    ∃! b : SecOn (GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)) ⊤, ∀ p : H.ι × (PUnit.{1} → H.ι),
      rs X (le_inf le_top inf_le_left : (E H φ q).U p ≤ ⊤ ⊓ H.U p.1) (GlobalTheory.LB.coord b p.1) = loc H φ q t σ a p :=
  SecOn.existsUnique_of_local (M := GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)) (isLB_pw hH ((q * t : ℕ) : ℤ)) (fun p : H.ι × (PUnit.{1} → H.ι) => (E H φ q).U p) (fun _ => le_top)
    (top_le_iSup_E hH φ q) (fun p => p.1) (fun _ => inf_le_left) (loc H φ q t σ a)
    (fun p p' => loc_compat H φ q t σ a p p')

def img {H : LB X} (hH : H.IsLB) (φ : X ⟶ X) (q t : ℕ) (σ : LB.Sec (E H φ q))
    (a : SecOn ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) : SecOn (GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)) ⊤ :=
  (existsUnique_img hH φ q t σ a).exists.choose

theorem img_spec {H : LB X} (hH : H.IsLB) (φ : X ⟶ X) (q t : ℕ) (σ : LB.Sec (E H φ q))
    (a : SecOn ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) (p : H.ι × (PUnit.{1} → H.ι)) :
    rs X (le_inf le_top inf_le_left : (E H φ q).U p ≤ ⊤ ⊓ H.U p.1) (GlobalTheory.LB.coord (img hH φ q t σ a) p.1) =
      loc H φ q t σ a p :=
  (existsUnique_img hH φ q t σ a).exists.choose_spec p

def imgLin {H : LB X} (hH : H.IsLB) (φ : X ⟶ X) (q t : ℕ) (σ : LB.Sec (E H φ q)) :
    SecOn ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤ →ₗ[Γ(X, ⊤)] SecOn (GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)) ⊤ where
  toFun := img hH φ q t σ
  map_add' a b := by
    refine (existsUnique_img hH φ q t σ (a + b)).unique (img_spec hH φ q t σ (a + b)) fun p => ?_
    erw [GlobalTheory.LB.coord_add, map_add, img_spec, img_spec]
    unfold loc
    erw [GlobalTheory.LB.coord_add, map_add]
    ring
  map_smul' r a := by
    refine (existsUnique_img hH φ q t σ (r • a)).unique (img_spec hH φ q t σ (r • a)) fun p => ?_
    erw [GlobalTheory.LB.coord_smul, map_mul, rs_rs, img_spec]
    unfold loc
    erw [GlobalTheory.LB.coord_smul, map_mul, rs_rs]
    simp only [RingHom.id_apply]
    ring

theorem imgLin_injective [IsIntegral X] {H : LB X} (hH : H.IsLB) (φ : X ⟶ X) (q t : ℕ) (σ : LB.Sec (E H φ q))
    (hσ : ∃ p : H.ι × (PUnit.{1} → H.ι), σ.f p ≠ 0) : Function.Injective (imgLin hH φ q t σ) := by
  obtain ⟨p₀, hp₀⟩ := hσ
  have hne : Nonempty ((E H φ q).U p₀) := by
    by_contra hc
    have hb : (E H φ q).U p₀ = ⊥ := by
      ext x
      exact ⟨fun hx => (hc ⟨⟨x, hx⟩⟩).elim, fun hx => hx.elim⟩
    have : Subsingleton Γ(X, (E H φ q).U p₀) := by rw [hb]; infer_instance
    exact hp₀ (Subsingleton.elim _ _)
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  have h0 : loc H φ q t σ a p₀ = 0 := by
    rw [← img_spec hH φ q t σ a p₀]
    change rs X _ (GlobalTheory.LB.coord (imgLin hH φ q t σ a) p₀.1) = 0
    rw [ha]
    erw [GlobalTheory.LB.coord_zero, map_zero]
  unfold loc at h0
  have h1 := (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hp₀)
  have hz := GlobalTheory.SecGrowth.sec_eq_zero (M := (GlobalTheory.AbLaw.pw H t).pull φ) (SecOn.topEquiv ((GlobalTheory.AbLaw.pw H t).pull φ) a) (k₀ := p₀.2)
    (W := (E H φ q).U p₀) inf_le_right (by erw [SecOn.topEquiv_f, rs_rs]; exact h1)
  apply (SecOn.topEquiv ((GlobalTheory.AbLaw.pw H t).pull φ)).injective
  rw [map_zero]
  exact GlobalTheory.LB.f_injective (funext hz)

end GlobalTheory.DegCmp

namespace GlobalTheory.DegCmp

theorem finite_finrank_pull_le {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of K)) (φ : X ⟶ X) (hφf : φ ≫ f = f) {H : LB X} (hH : H.IsLB) (q t : ℕ)
    (σ : LB.Sec (E H φ q)) (hσ : ∃ p : H.ι × (PUnit.{1} → H.ι), σ.f p ≠ 0)
    (hfin : Module.Finite K (SecOnR f (GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)) ⊤)) :
    Module.Finite K (SecOnR (φ ≫ f) ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) ∧
      Module.finrank K (SecOnR (φ ≫ f) ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) ≤
        Module.finrank K (SecOnR f (GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)) ⊤) := by
  rw [hφf]
  have hinj : Function.Injective (SecOnR.lin f (imgLin hH φ q t σ)) := imgLin_injective hH φ q t σ hσ
  exact ⟨Module.Finite.of_injective _ hinj, LinearMap.finrank_le_finrank_of_injective hinj⟩

end GlobalTheory.DegCmp

namespace GlobalTheory


open GlobalTheory.DegCmp in
theorem degree_le_of_pull_le_pow : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ (H : LB X) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB → GlobalTheory.AbLaw.VeryAmpleBy f H s → ∃ C : ℕ, ∀ (φ : X ⟶ X) [IsFinite φ] [Etale φ], φ ≫ f = f → ∀ (D q : ℕ), 1 ≤ q → (∀ x, φ.finrank x = D) → (∃ (σ : LB.Sec (LB.div (GlobalTheory.AbLaw.pw H (q : ℤ)) (H.pull φ))) (j : (LB.div (GlobalTheory.AbLaw.pw H (q : ℤ)) (H.pull φ)).ι), σ.f j ≠ 0) → D ≤ C * q ^ g := by
  intro k _ X _ f g hg H m s hH hs
  obtain ⟨hfin, -, c, C₀, -, hgrow⟩ := GlobalTheory.VeryAmpleGrowth.finite_monotone_growth k X f g hg H m s hH hs
  refine ⟨c * C₀ * 2 ^ g, fun φ _ _ hφf D q hq hD hσ => ?_⟩
  obtain ⟨σ, j, hj⟩ := hσ
  have hW : ∀ t : ℕ, Module.Finite k (SecOnR (φ ≫ f) ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) ∧
      Module.finrank k (SecOnR (φ ≫ f) ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) ≤
        Module.finrank k (SecOnR f (GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)) ⊤) := fun t =>
    finite_finrank_pull_le f φ hφf hH q t σ ⟨j, hj⟩ (hfin (q * t))
  obtain ⟨a, ha⟩ := GlobalTheory.finrank_sec_pull_sandwich k X X f φ H m s hH hs D hD hfin fun t => (hW t).1
  have h1 := (hgrow (a + 1) (by omega)).1
  have h2 := (ha (a + 1)).1
  have h3 := (hW (a + 1 + a)).2
  have h4 := (hgrow (q * (a + 1 + a)) (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))).2
  have hpos : 0 < (a + 1) ^ g := by positivity
  have key : D * (a + 1) ^ g ≤ (c * C₀ * 2 ^ g * q ^ g) * (a + 1) ^ g :=
    calc D * (a + 1) ^ g ≤ D * (c * Module.finrank k (SecOnR f (GlobalTheory.AbLaw.pw H ((a + 1 : ℕ) : ℤ)) ⊤)) :=
          Nat.mul_le_mul_left _ h1
      _ = c * (D * Module.finrank k (SecOnR f (GlobalTheory.AbLaw.pw H ((a + 1 : ℕ) : ℤ)) ⊤)) := by ring
      _ ≤ c * (C₀ * (q * (a + 1 + a)) ^ g) := Nat.mul_le_mul_left _ (h2.trans (h3.trans h4))
      _ ≤ c * (C₀ * (q * (2 * (a + 1))) ^ g) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (by omega)) g))
      _ = (c * C₀ * 2 ^ g * q ^ g) * (a + 1) ^ g := by rw [mul_pow, mul_pow]; ring
  exact Nat.le_of_mul_le_mul_right key hpos

end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

open FiniteCover

theorem finrank_sec_pull_sandwich_flat : ∀ (K : Type) [Field K] (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (f : X ⟶ Spec (CommRingCat.of K)) (φ : X' ⟶ X) [IsFinite φ] [Flat φ] [Surjective φ] (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ d : ℕ, (∀ x : X, φ.finrank x = d) → (∀ t : ℕ, Module.Finite K (SecOnR f (pw H t) ⊤)) → (∀ t : ℕ, Module.Finite K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤)) → ∃ a : ℕ, ∀ t : ℕ, d * Module.finrank K (SecOnR (f) (pw H t) ⊤) ≤ Module.finrank K (SecOnR (φ ≫ f) ((pw H (t + a : ℕ)).pull φ) ⊤) ∧ Module.finrank K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) ≤ d * Module.finrank K (SecOnR (f) (pw H (t + a : ℕ)) ⊤) := by
  intro K _ X X' _ _ f φ _ _ _ H n s hH hs d hd hV hW
  have hd1 : 1 ≤ d := hd _ ▸ φ.one_le_finrank_map (genericPoint X')
  letI : Algebra X.functionField X'.functionField := (functionFieldMap φ).toAlgebra
  letI : Algebra K X.functionField := ((toField generic_top).comp (cst f ⊤)).toAlgebra
  letI : Algebra K X'.functionField := ((toField generic_top).comp (cst (φ ≫ f) ⊤)).toAlgebra
  haveI : IsScalarTower K X.functionField X'.functionField :=
    IsScalarTower.of_algebraMap_eq fun r => by
      have w : φ ≫ f = (φ ≫ f) ≫ Spec.map (CommRingCat.ofHom (RingHom.id K)) := by simp
      have e := toField_appLE φ (U := ⊤) (V := ⊤) le_top generic_top generic_top (cst f ⊤ r)
      exact (congrArg (toField generic_top)
        (appLE_cst w (V := ⊤) (V' := ⊤) le_top r)).symm.trans e
  obtain ⟨hcov, hs⟩ := hs
  choose haff r hr _ using hs
  let I := {i // genericPoint X ∈ nonzeroLocus (s i)}
  haveI : Fintype I := Fintype.ofFinite I
  let D : I → X.Opens := fun i => nonzeroLocus (s i.1)
  have hη : ∀ i, genericPoint X ∈ D i := fun i => i.2
  have hc : ⊤ ≤ ⨆ i, D i := fun x hx => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, generic_mem hi⟩, hi⟩
  have hc' : ⊤ ≤ ⨆ i, φ ⁻¹ᵁ D i := fun x _ => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc (trivial : φ x ∈ ⊤))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  obtain ⟨i₀, -⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc generic_top)
  obtain ⟨k₀, h₀⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge generic_top)
  obtain ⟨x, hx⟩ := (chart_data φ (fun _ => rfl) (haff i₀.1) (hη i₀)).1
  rw [hd] at hx
  haveI : Module.Finite X.functionField X'.functionField :=
    Module.finite_of_finrank_pos (by omega)
  let e := Module.finBasisOfFinrankEq _ _ hx
  choose c hcm hc0 hc₁ hc₂ using fun i : I =>
    (chart_data φ (fun _ => rfl) (haff i.1) (hη i)).2 e
  let ρ : I → X.functionField := fun i => toField h₀ ((s i.1).f k₀)
  have hu : ∀ (i : I) k, IsUnit (rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k) ((s i.1).f k)) :=
    fun i k => SecOn.isUnit_rs_of_le_nonzeroLocus _ k _ inf_le_left
  have hρ : ∀ i, ρ i ≠ 0 := fun i => by
    have := ((hu i k₀).map (toField (generic_inf (hη i) h₀))).ne_zero
    rwa [toField_rs] at this
  have hρr : ∀ i k : I, ρ i / ρ k = toField (hη k) (r k.1 i.1) := fun i k => by
    have := congrArg (toField (generic_inf (hη k) h₀)) (hr k.1 i.1 k₀)
    rw [map_mul, toField_rs, toField_rs, toField_rs] at this
    exact (div_eq_iff (hρ k)).2 this
  let τ : ∀ (t : ℕ) (i : I), SecOn (pw H t) (D i) := fun t i => GlobalTheory.LB.ofSec (powSec (s i.1) t) (D i)
  have hτc : ∀ (t : ℕ) (i : I) (k : H.ι), GlobalTheory.LB.coord (τ t i) k =
      rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k) ((s i.1).f k) ^ t := fun t i k =>
    (GlobalTheory.LB.coord_ofSec _ _ _).trans (map_pow (rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k)) _ _)
  have hτ : ∀ (t : ℕ) (i : I) (k : H.ι), IsUnit (GlobalTheory.LB.coord (τ t i) k) := fun t i k =>
    (hτc t i k).symm ▸ (hu i k).pow t
  have hτv : ∀ (t : ℕ) (i : I), secVal (M := pw H t) (k₀ := k₀) h₀ (hη i) (τ t i) = ρ i ^ t :=
    fun t i => (congrArg (toField (generic_inf (hη i) h₀)) (hτc t i k₀)).trans (by
      rw [map_pow, toField_rs])
  have h₀' : ∀ t : ℕ, genericPoint X' ∈ ((pw H t).pull φ).U fun _ => k₀ := fun t =>
    le_pull (pw H t) φ (i := k₀) le_rfl (generic_mem_preimage φ h₀)
  refine finrank_sandwich e (fun i => (toField (hη i)).range)
    (fun i => (toField (generic_mem_preimage φ (hη i))).range) ρ c hρ hc0
    (fun i k => ⟨_, (hρr i k).symm⟩) (fun i k => ?_) ?_ hc₁ hc₂
    (fun t => SecOnR f (pw H t) ⊤) (fun t => SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) hV hW
    (fun t => secValLin (M := pw H t) (k₀ := k₀) h₀ f fun _ => rfl)
    (fun t => secValLin (h₀' t) (φ ≫ f) fun _ => rfl)
    (fun t => secVal_injective (M := pw H t) (k₀ := k₀) h₀ generic_top)
    (fun t => secVal_injective (h₀' t) generic_top) (fun t x => ?_) fun t y => ?_
  · obtain ⟨a, ha⟩ := hcm i
    rw [← ha, hρr]
    exact exists_mul_pow_mem (haff k.1) (hη k) (hη i) _
      (hρr i k ▸ div_ne_zero (hρ i) (hρ k)) (FiniteCover.basicOpen_le_nonzeroLocus _ _ _ (hr k.1 i.1)) a
  · rintro i _ ⟨a, rfl⟩
    exact ⟨_, toField_appLE φ le_rfl (hη i) _ a⟩
  · refine (exists_secVal_eq_iff (M := pw H t) (k₀ := k₀) h₀ (isLB_pw hH t) D hc hη (τ t) (hτ t)
      x).trans ?_
    simp only [hτv]
  · refine (exists_secVal_eq_iff (h₀' t) (LB.isLB_pull (isLB_pw hH t) φ) (fun i => φ ⁻¹ᵁ D i) hc'
      (fun i => generic_mem_preimage φ (hη i)) (fun i => SecOn.pull (pw H t) φ (D i) (τ t i))
      (fun i k => (hτ t i (k PUnit.unit)).map _) y).trans ?_
    refine forall_congr' fun i => ?_
    rw [secVal_pull (M := pw H t) (k₀ := k₀) h₀ φ (hη i), hτv]
    rfl

end GlobalTheory
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

namespace GlobalTheory

theorem outsideS_elt : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (k : GL (Fin a) (Af E)), ∃ k' : GL (Fin a) (Af E), (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k' = GeneralLinearGroup.map (pLoc E w) k) ∧ ∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k' = 1 := by
  intro E _ _ a S k
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨k, fun w _ => rfl, fun w hw => absurd hw (Finset.notMem_empty w)⟩
  | insert w S hwS ih =>
    obtain ⟨k', h1, h2⟩ := ih
    refine ⟨k' * (locGL E a w (GeneralLinearGroup.map (pLoc E w) k'))⁻¹, ?_, ?_⟩
    · intro v hv
      have hvw : v ≠ w := fun e => hv (e ▸ Finset.mem_insert_self _ _)
      rw [map_mul, map_inv, pLoc_locGL_of_ne hvw, inv_one, mul_one]
      exact h1 v (fun h => hv (Finset.mem_insert_of_mem h))
    · intro v hv
      rw [map_mul, map_inv]
      by_cases hvw : v = w
      · subst hvw; rw [pLoc_locGL, mul_inv_cancel]
      · rw [pLoc_locGL_of_ne hvw, inv_one, mul_one]
        exact h2 v ((Finset.mem_insert.1 hv).resolve_left hvw)

end GlobalTheory
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem exists_etale_kill_of_indEt : ∀ (q : ℕ) (B O : Type) [CommRing B] [CommRing O] [Algebra B O], IsUnit (q : B) → IndEt B O → ∀ (n i : ℤ) (y : Ht q (sp B) n i), pull _ (spMap (algebraMap B O)) _ _ y = 0 → ∃ (D : Type) (_ : CommRing D) (_ : Algebra B D) (_ : Algebra.Etale B D) (_ : D →ₐ[B] O), pull _ (spMap (algebraMap B D)) _ _ y = 0 := by
  intro q B O _ _ _ hq hO n i y hy
  obtain ⟨J, _, _, D, ι, ⟨hc⟩, het⟩ := GlobalTheory.T.exists_filtered_colimit_of_etale_of_indEt B O hO
  have hc' : IsColimit ((Under.forget (CommRingCat.of B)).mapCocone (Cocone.mk _ ι)) :=
    isColimitOfPreserves (Under.forget _) hc
  obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
  have hqj : IsUnit ((q : ((D ⋙ Under.forget _).obj j))) := by
    have := hq.map (D.obj j).hom.hom
    rw [map_natCast] at this
    exact this
  have hyj : pull _ (spMap ((Under.forget _).mapCocone (Cocone.mk _ ι) |>.ι.app j).hom) _ _
      (pull _ (spMap (D.obj j).hom.hom) _ _ y) = 0 := by
    erw [← pull_comp]
    have hw : (D.obj j).hom ≫ (ι.app j).right = CommRingCat.ofHom (algebraMap B O) := by
      simpa using Under.w (ι.app j)
    have : spMap ((Under.forget _).mapCocone (Cocone.mk _ ι) |>.ι.app j).hom ≫ spMap (D.obj j).hom.hom
        = spMap (algebraMap B O) := by
      simp only [spMap, ← Functor.map_comp, ← Spec.map_comp]
      congr 2 <;> simpa using hw
    erw [this]; exact hy
  obtain ⟨k, f, hk⟩ := (GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q (D ⋙ Under.forget _) _ hc' n i).2 j _ hqj hyj
  erw [← pull_comp] at hk
  have hwk : (D.obj j).hom ≫ (D.map f).right = (D.obj k).hom := by simpa using Under.w (D.map f)
  letI : Algebra B (D.obj k).right := (D.obj k).hom.hom.toAlgebra
  refine ⟨(D.obj k).right, inferInstance, this, het k, ⟨(ι.app k).right.hom, fun b => ?_⟩, ?_⟩
  · have hw : (D.obj k).hom ≫ (ι.app k).right = CommRingCat.ofHom (algebraMap B O) := by
      simpa using Under.w (ι.app k)
    exact congrArg (fun g => g.hom b) hw
  · have : spMap ((D ⋙ Under.forget _).map f).hom ≫ spMap (D.obj j).hom.hom
        = spMap (algebraMap B (D.obj k).right) := by
      simp only [spMap, ← Functor.map_comp, ← Spec.map_comp]
      congr 2 <;> simpa using hwk
    erw [this] at hk; exact hk

end GlobalTheory.EtC
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_complexAbelianVariety_sectionRatio_affine_cover : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∃ (n : ℕ) (W : Fin n → A.left.Opens) (r : ∀ k, Fin n → Γ(A.left, W k)), IsRatioCover u.ex W r := by
  first | exact @GlobalTheory.RatioCover.main | exact GlobalTheory.RatioCover.main | (intros; apply GlobalTheory.RatioCover.main <;> assumption)
end
