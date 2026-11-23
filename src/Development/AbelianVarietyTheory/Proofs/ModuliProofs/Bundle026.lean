module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingHenselianAndSmoothPointsLift
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.valuationRing_henselian_and_smooth_points_lift : ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K], HenselianLocalRing O ∧ IsAlgClosed (IsLocalRing.ResidueField O) ∧ ∀ (X : Scheme.{0}) (f : X ⟶ Sp O), Smooth f → ∀ x : Sp (IsLocalRing.ResidueField O) ⟶ X, x ≫ f = spMap (IsLocalRing.residue O) → ∃ y : Sp O ⟶ X, y ≫ f = 𝟙 _ ∧ spMap (IsLocalRing.residue O) ≫ y = x := by
  first | exact @GlobalTheory.valuationRing_henselian_and_lift_of_isAlgClosed | exact GlobalTheory.valuationRing_henselian_and_lift_of_isAlgClosed | (intros; apply GlobalTheory.valuationRing_henselian_and_lift_of_isAlgClosed <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory

private theorem differentiableOn_prod_of_forall {E κ : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set E}
    (s : Finset κ) (φ : κ → E → ℂ) (h : ∀ k, DifferentiableOn ℂ (φ k) S) :
    DifferentiableOn ℂ (fun z => ∏ k ∈ s, φ k z) S := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using differentiableOn_const (c := (1 : ℂ))
  | insert a t ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a).mul ih

section

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}
  (u : HolUnif A L g) (u' : HolUnif A' L' g') {K : Type} [Fintype K] (f : K → (A ⟶ A'))
  (F : K → ((Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ))) (ε : K → ℤ)

def linCombUnif (h : ∀ k z, u'.ex (F k z) = u.ex z ≫ f k) :
    HolUnif A (LB.LinComb L' (fun k => (f k).left) ε) g :=
  have hl : ∀ k z, (u'.ex (F k z)).left = (u.ex z).left ≫ (f k).left := fun k z => by
    rw [h k z]; rfl
  have hc : ∀ (j : K → L'.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ LB.wchart L' (fun k => (f k).left) j →
      ∀ k, ⊤ ≤ (u'.ex (F k z)).left ⁻¹ᵁ L'.U (j k) := fun j z hz k => by
    rw [hl k z]
    exact (CubeValues.le_preimage_wchart (u.ex z).left L' (fun k => (f k).left) j).1 hz k
  { ex := u.ex
    ex_add := u.ex_add
    ex_onto := u.ex_onto
    Λ := u.Λ
    ker := u.ker
    discrete := u.discrete
    full := u.full
    hol := u.hol
    fr := fun (j : K → L'.ι) z => ∏ k, u'.fr (j k) (F k z) ^ ε k
    fr_hol := fun j => by
      refine differentiableOn_prod_of_forall Finset.univ
        (fun k (z : Fin g → ℂ) => u'.fr (j k) (F k z) ^ ε k) fun k => ?_
      refine DifferentiableOn.zpow ?_ (Or.inl fun z hz => u'.fr_ne _ _ (hc j z hz k))
      exact (u'.fr_hol (j k)).comp (LinearMap.toContinuousLinearMap (F k)).differentiable.differentiableOn
        fun z hz => hc j z hz k
    fr_ne := fun j z hz => Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (u'.fr_ne _ _ (hc j z hz k))
    fr_compat := fun j j' z hz => by
      obtain ⟨h1, h2⟩ := (top_le_preimage_inf (u.ex z).left _ _).1 hz
      have e := CubeValues.val_linComb (u.ex z).left valAt'_rules L' (fun k => (f k).left) ε j j' h1 h2
      refine Eq.trans ?_ (congrArg (· * ∏ k, u'.fr (j' k) (F k z) ^ ε k) e.symm)
      show _ = (∏ k, _) * _
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← mul_zpow, ← hl k z]
      exact congrArg (· ^ ε k) (u'.fr_compat (j k) (j' k) (F k z)
        ((top_le_preimage_inf _ _ _).2 ⟨hc j z h1 k, hc j' z h2 k⟩)) }

end

theorem exists_holUnif_linComb : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (L : LB A.left) (L' : LB A'.left) (g g' : ℕ) (u : HolUnif A L g) (u' : HolUnif A' L' g') (K : Type) [Fintype K] (f : K → (A ⟶ A')) (F : K → ((Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ))) (ε : K → ℤ), (∀ k z, u'.ex (F k z) = u.ex z ≫ f k) → ∃ u₁ : HolUnif A (LB.LinComb L' (fun k => (f k).left) ε) g, u₁.ex = u.ex ∧ u₁.Λ = u.Λ ∧ ∀ (j : K → L'.ι) z, u₁.fr j z = ∏ k, u'.fr (j k) (F k z) ^ ε k := by
  intro A A' _ _ L L' g g' u u' K _ f F ε hF
  refine ⟨linCombUnif u u' f F ε hF, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · intro j z
    rfl

end GlobalTheory
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.OriginValue

theorem eq_of_valAt'_eq_of_isIso {X : Scheme.{0}} (x : Sp ℂ ⟶ X) [IsIso x] (W : X.Opens) (f g : Γ(X, W))
    (h : ⊤ ≤ x ⁻¹ᵁ W → valAt' x W f = valAt' x W g) : f = g := by
  by_cases hW : ⊤ ≤ x ⁻¹ᵁ W
  · have h1 := h hW
    rw [valAt'_eq_valAt x hW, valAt'_eq_valAt x hW, valAt, valAt] at h1
    have h2 := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).1 h1
    have e : (⊤ : (Sp ℂ).Opens) = x ⁻¹ᵁ W := le_antisymm hW le_top
    have : IsIso (homOfLE hW) := ⟨⟨homOfLE le_top, rfl, rfl⟩⟩
    have : IsIso (x.appLE W ⊤ hW) := by
      unfold Scheme.Hom.appLE
      infer_instance
    exact (ConcreteCategory.bijective_of_isIso (x.appLE W ⊤ hW)).1 h2
  · have hb : W = ⊥ := by
      rw [top_le_preimage_iff_mem] at hW
      refine le_bot_iff.1 fun y hy => ?_
      obtain ⟨q, rfl⟩ := x.surjective y
      have : q = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
      subst this
      exact (hW hy).elim
    subst hb
    exact Subsingleton.elim _ _

def constFnHom {X : Scheme.{0}} (f : X ⟶ Sp ℂ) (U : X.Opens) : ℂ →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ f.appLE ⊤ U (fun _ _ => trivial)).hom

theorem top_le_preimage_wchart_one {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (x : Sp ℂ ⟶ Y) (j : Fin 1 → L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => φ) j) : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U (j 0) :=
  (top_le_preimage_comp x φ _).2 (top_le_preimage_mono x (LB.wchart_le L (fun _ : Fin 1 => φ) j 0) h)

theorem ex_zero {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) : u.ex 0 = 1 :=
  (u.ker 0).2 u.Λ.zero_mem


open Classical in
def unitOrOne (c : ℂ) : ℂˣ := if h : c ≠ 0 then Units.mk0 c h else 1

theorem unitOrOne_val {c : ℂ} (h : c ≠ 0) : (unitOrOne c : ℂ) = c := by
  rw [unitOrOne, dite_eq_left h]; rfl

theorem exists_gen_isValueAt_origin : ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (a : ℤ) (T : Over (Sp ℂ)) [IsIso T.hom] (p : 𝟙_ (Over (Sp ℂ)) ⟶ T), ∃ τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (1 : T ⟶ P.A).left) (fun _ => a)), τ.IsGen ∧ ∀ (s : LB.Sec (Out.LPow P.A P.L a T)) (f : (Fin P.g → ℂ) → ℂ), (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L a T).U j) (s.f j) = f z * u.fr (j 0) z ^ (a : ℤ)) → Out.IsValueAt P.A P.L a s 1 τ (constFn T.hom ⊤ (f 0)) := by
  intro P u a T _ p
  let x : Sp ℂ ⟶ T.left := p.left
  have hx : x ≫ T.hom = 𝟙 _ := Over.w p
  have : IsIso x := by
    have : x = inv T.hom := IsIso.eq_inv_of_inv_hom_id hx
    rw [this]; infer_instance
  have h1 : p ≫ (1 : T ⟶ P.A) = u.ex 0 := by
    rw [ex_zero, MonObj.comp_one]
  have h1' : x ≫ (1 : T ⟶ P.A).left = (u.ex 0).left := congrArg CommaMorphism.left h1
  have hch : ∀ j : Fin 1 → P.L.ι, ⊤ ≤ x ⁻¹ᵁ LB.wchart P.L (fun _ : Fin 1 => (1 : T ⟶ P.A).left) j →
      ⊤ ≤ (u.ex 0).left ⁻¹ᵁ P.L.U (j 0) := fun j h => by
    have := top_le_preimage_wchart_one P.L _ x j h
    rwa [h1'] at this
  let τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (1 : T ⟶ P.A).left) (fun _ => a)) :=
    ⟨fun j => Units.map (constFnHom T.hom _).toMonoidHom (unitOrOne (u.fr (j 0) 0) ^ a)⟩
  have hτ : ∀ j : Fin 1 → P.L.ι, ⊤ ≤ x ⁻¹ᵁ LB.wchart P.L (fun _ : Fin 1 => (1 : T ⟶ P.A).left) j →
      valAt' x (LB.wchart P.L (fun _ : Fin 1 => (1 : T ⟶ P.A).left) j) (τ.s j).val = u.fr (j 0) 0 ^ a := fun j h => by
    refine (valAt'_constFn x T.hom hx _ _ h).trans ?_
    rw [Units.val_zpow_eq_zpow_val, unitOrOne_val (u.fr_ne _ _ (hch j h))]
  refine ⟨τ, fun i j => ?_, fun s f hs j => ?_⟩
  · apply Units.ext
    refine eq_of_valAt'_eq_of_isIso x _ _ _ fun h => ?_
    obtain ⟨hi, hj⟩ := (top_le_preimage_inf x _ _).1 h
    rw [Units.val_mul, valAt'_mul]
    refine ((valAt'_res x inf_le_left _ h).trans (hτ i hi)).trans ?_
    have e2 := (valAt'_res x inf_le_right _ h).trans (hτ j hj)
    refine Eq.trans ?_ (congrArg _ e2.symm)
    have hij : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ (P.L.U (i 0) ⊓ P.L.U (j 0)) :=
      (top_le_preimage_inf (u.ex 0).left _ _).2 ⟨hch i hi, hch j hj⟩
    rw [u.fr_compat _ _ _ hij, mul_zpow]
    congr 1
    simp only [LB.LinComb, Fin.prod_univ_one]
    refine Eq.trans ?_ (valAt'_zpow x h _ a).symm
    congr 1
    refine Eq.trans ?_ (valAt'_res x _ _ h).symm
    refine Eq.trans ?_ (valAt'_comp x (1 : T ⟶ P.A).left (P.L.U (i 0) ⊓ P.L.U (j 0)) (P.L.g (i 0) (j 0)).val).symm
    rw [h1']
  · refine eq_of_valAt'_eq_of_isIso x _ _ _ fun h => ?_
    rw [valAt'_mul, hτ j h, valAt'_map x _ _ h, valAt'_map x _ _ h, valAt'_constFn x T.hom hx _ _ le_top]
    refine (valAt'_comp x _ _ _).trans ?_
    have h2 : p ≫ Out.ptSecT P.A (1 : T ⟶ P.A) = lift p (u.ex 0) := by
      rw [Out.ptSecT, comp_lift, Category.comp_id, h1]
    have h2' : x ≫ (Out.ptSecT P.A (1 : T ⟶ P.A)).left = (lift p (u.ex 0)).left := congrArg CommaMorphism.left h2
    rw [h2']
    exact hs j 0 (hch j h)

end GlobalTheory.OriginValue
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory

theorem zeta_eq_pow_div_of_dvd {a b : ℕ} (hb : 0 < b) (h : a ∣ b) : zeta a = zeta b ^ (b / a) := by
  obtain ⟨c, rfl⟩ := h
  have ha : 0 < a := Nat.pos_of_mul_pos_right hb
  have hc : 0 < c := Nat.pos_of_mul_pos_left hb
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  rw [Nat.mul_div_cancel_left c ha, zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem levelField_le_of_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : KA l ≤ KA l₂ := by
  unfold KA
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  rcases hx with rfl | hx
  · exact IntermediateField.subset_adjoin _ _ (by simp)
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [zeta_eq_pow_div_of_dvd l₂.A_pos h]
    exact pow_mem (IntermediateField.subset_adjoin ℚ ({H.rt0, zeta l₂.A} : Set ℂ) (by simp)) _

def baseOfFinerLevel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : Base l (KA l₂) where
  unit := (baseKA l₂).unit
  ρ := (baseKA l₂).ρ
  ρ_sq := (baseKA l₂).ρ_sq
  ζ := IntermediateField.inclusion (levelField_le_of_dvd h) (baseKA l).ζ
  ζ_prim := (baseKA l).ζ_prim.map_of_injective (IntermediateField.inclusion_injective (levelField_le_of_dvd h))

def levelFieldIncl {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : KA l →+* KA l₂ :=
  (IntermediateField.inclusion (levelField_le_of_dvd h)).toRingHom

theorem coe_levelFieldIncl {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) (x : KA l) : ((levelFieldIncl h x : KA l₂) : ℂ) = (x : ℂ) :=
  IntermediateField.coe_inclusion (levelField_le_of_dvd h) x

theorem coe_baseKA_rho {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    (((baseKA l).ρ : KA l) : ℂ) = H.rt0 := rfl

theorem levelFieldIncl_rho {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : levelFieldIncl h (baseKA l).ρ = (baseOfFinerLevel h).ρ :=
  Subtype.ext ((coe_levelFieldIncl h _).trans ((coe_baseKA_rho l).trans (coe_baseKA_rho l₂).symm))

theorem levelFieldIncl_zeta {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : levelFieldIncl h (baseKA l).ζ = (baseOfFinerLevel h).ζ := rfl

theorem baseOfFinerLevel_rho {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : (baseOfFinerLevel h).ρ = (baseKA l₂).ρ := rfl

theorem baseOfFinerLevel_zeta {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l l₂ : Level H}
    (h : l.A ∣ l₂.A) : (baseOfFinerLevel h).ζ = (baseKA l₂).ζ ^ (l₂.A / l.A) := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, ← levelFieldIncl_zeta, coe_levelFieldIncl]
  exact zeta_eq_pow_div_of_dvd l₂.A_pos h

theorem exists_sabMap_of_base_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f g : S' ⟶ S} (n : SABMap t' t f) (h : f = g) :
    ∃ n' : SABMap t' t g, n'.φ = n.φ := by
  subst h
  exact ⟨n, rfl⟩

theorem exists_levelMap : (∀ (k : Type) [Field k] (X : Scheme.{0}) (s : X ⟶ Sp k), Smooth s → IsReduced X ∧ IsNormalScheme X ∧ IsLocallyNoetherian X) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b' : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o'' : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f' : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫ f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫ f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B : Type) [CommRing B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o₂ : Obj D l₂ b₂ s), l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (o : Obj D l b s) (m : SABMap o₂.t o.t (𝟙 S)), (∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = 𝟙 S ≫ (o.eta a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = 𝟙 S ≫ (o.etaA a).left)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (B : Type) [CommRing B] (b : Base l B) (j : KA l →+* B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsReduced S → j (baseKA l).ρ = b.ρ → j (baseKA l).ζ = b.ζ → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ f)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∃ (r : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) := by
  intro hsm _ hlow hrep E _ _ _ H D l l₂ Xo Xo₂ _ hd
  have hA : l.A ∣ l₂.A := hd.2.2
  obtain ⟨o, m₁, h₁, h₁A⟩ := hlow E H D l l₂ (KA l₂) (baseOfFinerLevel hA) (baseKA l₂) Xo₂.X Xo₂.s Xo₂.univ hd
    (baseOfFinerLevel_rho hA) (baseOfFinerLevel_zeta hA)
  have hred : IsReduced Xo₂.X := by
    have := Xo₂.smooth
    exact (hsm _ _ Xo₂.s (SmoothOfRelativeDimension.smooth D.dim Xo₂.s)).1
  obtain ⟨r, ⟨hr, ⟨m₂⟩⟩, -⟩ := hrep E H D l Xo (KA l₂) (baseOfFinerLevel hA) (levelFieldIncl hA) Xo₂.X Xo₂.s o hred
    (levelFieldIncl_rho hA) (levelFieldIncl_zeta hA)
  obtain ⟨m, hm⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₂.toSABMap m₁
  obtain ⟨n, hn⟩ := exists_sabMap_of_base_eq m (Category.id_comp r)
  have hφ : n.φ = m₁.φ ≫ m₂.toSABMap.φ := hn.trans hm
  refine ⟨r, levelFieldIncl hA, n, coe_levelFieldIncl hA, hr, fun a => ?_, fun a => ?_⟩
  · exact (congrArg (_ ≫ ·) hφ).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ m₂.toSABMap.φ) ((h₁ a).trans (Category.id_comp _))).trans (m₂.eta a)))
  · exact (congrArg (_ ≫ ·) hφ).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ m₂.toSABMap.φ) ((h₁A a).trans (Category.id_comp _))).trans (m₂.etaA a)))

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SimAlg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem modN_zero (n : ℕ) : D.ModN n 0 := ⟨0, by simp⟩

theorem modN_add {n : ℕ} {x y : D.La} (hx : D.ModN n x) (hy : D.ModN n y) : D.ModN n (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by rw [smul_add]⟩

theorem modN_neg {n : ℕ} {x : D.La} (hx : D.ModN n x) : D.ModN n (-x) := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨-a, by rw [smul_neg]⟩

theorem modN_map {n : ℕ} {x : D.La} (f : D.La →ₗ[𝓞 E] D.La) (hx : D.ModN n x) : D.ModN n (f x) := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨f a, by rw [map_nsmul]⟩

theorem modN_of_mul {n m : ℕ} {x : D.La} (hx : D.ModN (n * m) x) : D.ModN n x := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨m • a, by rw [mul_smul]⟩

theorem dvd_form_sub {n : ℕ} {x x' y y' : D.La} (hx : D.ModN n (x - x')) (hy : D.ModN n (y - y')) :
    (n : ℤ) ∣ D.EF x y - D.EF x' y' := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  have h1 : x = x' + n • a := by rw [← ha]; abel
  have h2 : y = y' + n • b := by rw [← hb]; abel
  refine ⟨D.EF x' b + D.EF a y' + n * D.EF a b, ?_⟩
  rw [h1, h2]
  simp only [map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
  ring

theorem exists_form_eq_one (h : 1 ≤ D.p + D.q) : ∃ a b : D.La, D.EF a b = 1 := by
  haveI := D.fin
  haveI := D.proj
  haveI : Nontrivial D.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [D.rank]; omega)
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  haveI : Module.IsTorsionFree ℤ D.La :=
    Function.Injective.moduleIsTorsionFree D.EF D.unimod.1 (fun r x => map_smul _ r x)
  haveI : Module.Free ℤ D.La := Module.free_of_finite_type_torsion_free'
  let B := Module.Free.chooseBasis ℤ D.La
  obtain ⟨i⟩ := B.index_nonempty
  obtain ⟨a, ha⟩ := D.unimod.2 (B.coord i)
  exact ⟨a, B i, by rw [ha]; simp⟩

theorem dvd_mult_inv (g : Sim D) {n : ℕ} (hn : 0 < n) {a b : D.La} (hab : D.EF a b = 1)
    (h : D.La →ₗ[𝓞 E] D.La) (hh : ∀ x, D.ModN n (g.f n (h x) - x)) :
    (n : ℤ) ∣ g.ν n * D.EF (h a) (h b) - 1 := by
  have h1 := g.mult n hn (h a) (h b)
  have h2 := dvd_form_sub (hh a) (hh b)
  rw [hab] at h2
  obtain ⟨c, hc⟩ := dvd_sub h2 h1
  exact ⟨c, by linear_combination hc⟩

theorem dvd_mult_tower (g : Sim D) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) {a b : D.La} (hab : D.EF a b = 1) :
    (n : ℤ) ∣ g.ν (n * m) - g.ν n := by
  have h1 := g.mult n hn a b
  have h2 : (n : ℤ) ∣ _ := Dvd.dvd.trans (by push_cast; exact Dvd.intro _ rfl) (g.mult (n * m) (Nat.mul_pos hn hm) a b)
  have h3 := dvd_form_sub (g.tower n m hn hm a) (g.tower n m hn hm b)
  rw [hab] at h1 h2
  obtain ⟨c, hc⟩ := dvd_add (dvd_sub h3 h2) h1
  exact ⟨c, by linear_combination hc⟩

def one (D : Datum H) : Sim D where
  f _ := LinearMap.id
  ν _ := 1
  tower n _ _ _ a := by simpa using modN_zero n
  inv n _ := ⟨LinearMap.id, fun a => by simpa using modN_zero n⟩
  mult n _ a b := by simp

def mul (g g' : Sim D) : Sim D where
  f n := g.f n ∘ₗ g'.f n
  ν n := g.ν n * g'.ν n
  tower n m hn hm a := by
    have h1 := g.tower n m hn hm (g'.f (n * m) a)
    have h2 := modN_map (g.f n) (g'.tower n m hn hm a)
    convert modN_add h1 h2 using 1
    simp
  inv n hn := by
    obtain ⟨h, hh⟩ := g.inv n hn
    obtain ⟨h', hh'⟩ := g'.inv n hn
    refine ⟨h' ∘ₗ h, fun a => ⟨?_, ?_⟩⟩
    · convert modN_add (modN_map h' (hh (g'.f n a)).1) (hh' a).1 using 1
      simp
    · convert modN_add (modN_map (g.f n) (hh' (h a)).2) (hh a).2 using 1
      simp
  mult n hn a b := by
    have h1 := g.mult n hn (g'.f n a) (g'.f n b)
    have h2 := Dvd.dvd.mul_left (g'.mult n hn a b) (g.ν n)
    obtain ⟨c, hc⟩ := dvd_add h1 h2
    exact ⟨c, by simp only [LinearMap.comp_apply]; linear_combination hc⟩

theorem exists_inv (g : Sim D) {a b : D.La} (hab : D.EF a b = 1) :
    ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧
      (n : ℤ) ∣ g.ν n * g'.ν n - 1 := by
  have hex : ∀ n : ℕ, ∃ h : D.La →ₗ[𝓞 E] D.La, 0 < n →
      ∀ a, D.ModN n (h (g.f n a) - a) ∧ D.ModN n (g.f n (h a) - a) := by
    intro n
    by_cases hn : 0 < n
    · obtain ⟨h, hh⟩ := g.inv n hn
      exact ⟨h, fun _ => hh⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose h hh using hex
  have hν : ∀ n : ℕ, 0 < n → (n : ℤ) ∣ g.ν n * D.EF (h n a) (h n b) - 1 := fun n hn =>
    dvd_mult_inv g hn hab (h n) fun x => (hh n hn x).2
  refine ⟨⟨h, fun n => D.EF (h n a) (h n b), ?_, ?_, ?_⟩, fun n hn => ⟨hh n hn, hν n hn⟩⟩
  · intro n m hn hm x
    have h1 := modN_neg (hh n hn (h (n * m) x)).1
    have h2 := modN_neg (modN_map (h n) (g.tower n m hn hm (h (n * m) x)))
    have h3 := modN_map (h n) (modN_of_mul (hh (n * m) (Nat.mul_pos hn hm) x).2)
    convert modN_add (modN_add h1 h2) h3 using 1
    simp only [map_sub]
    abel
  · intro n hn
    exact ⟨g.f n, fun x => ⟨(hh n hn x).2, (hh n hn x).1⟩⟩
  · intro n hn x y
    have h1 := Dvd.dvd.mul_left (g.mult n hn (h n x) (h n y)) (D.EF (h n a) (h n b))
    have h2 := Dvd.dvd.mul_left (dvd_form_sub (hh n hn x).2 (hh n hn y).2) (D.EF (h n a) (h n b))
    have h3 := Dvd.dvd.mul_right (hν n hn) (D.EF (h n x) (h n y))
    obtain ⟨c, hc⟩ := dvd_sub (dvd_sub h2 h1) h3
    exact ⟨c, by linear_combination hc⟩

theorem sim_group : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q → (∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ)) ∧ (∃ g : Sim D, ∀ n, g.f n = LinearMap.id ∧ g.ν n = 1) ∧ (∀ g g' : Sim D, ∃ g'' : Sim D, ∀ n, g''.f n = g.f n ∘ₗ g'.f n ∧ g''.ν n = g.ν n * g'.ν n) ∧ (∀ g : Sim D, ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧ (n : ℤ) ∣ g.ν n * g'.ν n - 1) := by
  intro E _ _ _ H D hpq
  obtain ⟨a, b, hab⟩ := exists_form_eq_one hpq
  refine ⟨fun g n m hn hm => ⟨dvd_mult_tower g hn hm hab, ?_⟩, ⟨one D, fun _ => ⟨rfl, rfl⟩⟩,
    fun g g' => ⟨mul g g', fun _ => ⟨rfl, rfl⟩⟩, fun g => exists_inv g hab⟩
  obtain ⟨h, hh⟩ := g.inv n hn
  obtain ⟨c, hc⟩ := dvd_mult_inv g hn hab h fun x => (hh x).2
  exact ⟨D.EF (h a) (h b), -c, by linear_combination hc⟩

end GlobalTheory.SimAlg
end
