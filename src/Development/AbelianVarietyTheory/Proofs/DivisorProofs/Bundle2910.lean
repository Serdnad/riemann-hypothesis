module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle189
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2636
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1802
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2779
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle587
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2784
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2783
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonLevelCoverPullbackProbability
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormIffLevelCoverPullback
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem GlobalTheory.FormalAlg.exists_chart_cocycle_of_pull : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (H₀ : LB (Y 0).left) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → ((∀ i, C.D 0 i = nonzeroLocus (s₀ i)) ∧ ∀ i j (m : H₀.ι), rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ j).f m) = rs (Y 0).left (inf_le_left : C.D 0 i ⊓ H₀.U m ≤ C.D 0 i) (C.ρ 0 i j) * rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ i).f m)) → ∀ γ : ∀ e, (Y 0).left ⟶ (Y e).left, γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ (e k : ℕ) (L : LB (Y e).left), L.IsLB → LBIso (L.pull (γ e)) (GlobalTheory.AbLaw.pw H₀ k) → ∃ g : ∀ i j, Γ((Y e).left, C.D e i ⊓ C.D e j)ˣ, (⟨Fin (n + 1), C.D e, g⟩ : LB (Y e).left).IsLB ∧ LBIso L ⟨Fin (n + 1), C.D e, g⟩ ∧ ∀ i j, (g i j).val - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k ∈ towerIdeal Y e I (C.D e i ⊓ C.D e j) := by
  rintro R _ I Y β hβ n C H₀ s₀ hH₀ ⟨hD, hρs⟩ γ hγ0 hγs e k L hL ⟨w, hw⟩
  have hpb : IsPullback (γ e) (Y 0).hom ((Y e).hom ≫ thick R I e) (thick R I 0) :=
    (GlobalTheory.T.isPullback_thick_tower_squares R I Y β hβ).2 γ hγ0 hγs e
  have hsurj : ∀ e, Surjective (γ e) := by
    intro e
    induction e with
    | zero => rw [hγ0]; infer_instance
    | succ e ih =>
      rw [← hγs e]
      have := MorphismProperty.of_isPullback (P := @Surjective) (hβ e).flip (GlobalTheory.GenSystem.surjective_thickTrans R I e)
      infer_instance
  have hpre := fun i => GlobalTheory.T.thickeningTowerCharts_preimage_and_germ_pullback R I Y β n C γ hγ0 hγs e i
  have hu := fun i => GlobalTheory.T.exists_local_frames_of_pullback_power_on_nonzeroLocus _ _ (γ e) H₀ (s₀ i) k L hL hH₀ w hw (C.D e i) ((hpre i).1.trans (hD i))
  choose u hu1 hu2 using hu
  have ht := fun i => GlobalTheory.T.lift_local_units_along_nilpotent_thickening R (I ^ (0 + 1)) (Y e).left (Y 0).left ((Y e).hom ≫ thick R I e) (γ e) (Y 0).hom
    hpb (hsurj e) L hL (C.D e i) (C.aff e i) (u i) (hu1 i)
  choose τ hτ1 hτ2 using ht
  obtain ⟨g, hgLB, hgIso, hg⟩ := GlobalTheory.T.cech_lineBundle_of_compatible_local_frames (Y e).left L hL n (C.D e) (C.cover e) τ hτ2
  refine ⟨g, hgLB, hgIso, fun i j => ?_⟩
  have hVaff : IsAffineOpen (C.D e i ⊓ C.D e j) := by
    have := (C.aff e i).basicOpen (C.ρ e i j)
    rwa [(GlobalTheory.T.thickeningTower_liftedRatios_projective_relations R I Y β hβ n C).1 e i j] at this
  obtain ⟨-, -, hker⟩ := GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R (I ^ (0 + 1)) (Y e).left (Y 0).left ((Y e).hom ≫ thick R I e) (γ e) (Y 0).hom hpb
  have hk := (hker _ hVaff).2

  have hτu : ∀ i m z (hz : γ e z ∈ C.D e i ⊓ L.U m), gm (γ e) z _ (τ i m) = gm (𝟙 _) z _ (u i m) := by
    intro i m z hz
    have h1 := gm_pull (𝟙 _) (γ e) z _ hz (τ i m)
    rw [Category.id_comp] at h1
    rw [← h1]
    congr 1
    exact Units.ext (hτ1 i m)
  have hmem : (g i j).val - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k ∈
      RingHom.ker ((γ e).app (C.D e i ⊓ C.D e j)).hom := by
    rw [RingHom.mem_ker]
    apply fn_ext
    intro z hz
    have hz' : γ e z ∈ C.D e i ⊓ C.D e j := hz
    obtain ⟨m, hm⟩ := exists_chart hL (γ e z)
    obtain ⟨a, ha⟩ := exists_chart hH₀ z
    have hzi : z ∈ C.D 0 i := (hpre i).1 ▸ hz'.1
    have hzj : z ∈ C.D 0 j := (hpre j).1 ▸ hz'.2
    have hm3 : γ e z ∈ C.D e i ⊓ C.D e j ⊓ L.U m := ⟨hz', hm⟩

    have hgz : gs (γ e) z _ (g i j).val = (gm (𝟙 _) z _ (u j m)).val * ((gm (𝟙 _) z _ (u i m))⁻¹).val := by
      rw [gs_unit _ z _ hz', ← gm_res (γ e) z (inf_le_left : C.D e i ⊓ C.D e j ⊓ L.U m ≤ C.D e i ⊓ C.D e j) hm3,
        hg i j m, map_mul, map_inv, gm_res _ z _ hm3, gm_res _ z _ hm3, hτu j m z ⟨hz'.2, hm⟩,
        hτu i m z ⟨hz'.1, hm⟩, Units.val_mul]

    have hsj := hu2 j z m a ⟨hz'.2, hm⟩ ha
    have hsi := hu2 i z m a ⟨hz'.1, hm⟩ ha
    have hrel : gs (𝟙 _) z _ ((s₀ j).f a) = gs (𝟙 _) z _ (C.ρ 0 i j) * gs (𝟙 _) z _ ((s₀ i).f a) := by
      have h := congrArg (gs (𝟙 _) z (C.D 0 i ⊓ H₀.U a)) (hρs i j a)
      have hmz : (𝟙 (Y 0).left) z ∈ C.D 0 i ⊓ H₀.U a := ⟨hzi, ha⟩
      rwa [gs_mul _ z _ hmz, gs_res _ z _ hmz, gs_res _ z _ hmz, gs_res _ z _ hmz] at h
    have hρz : gs (γ e) z _ (rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k) =
        gs (𝟙 _) z _ (C.ρ 0 i j) ^ k := by
      rw [gs_eq _ z _ hz', map_pow, map_pow, ← gs_eq _ z _ hz', gs_res _ z _ hz', (hpre i).2 j z hzi]
    have hu' : (gm (𝟙 _) z _ (u j m)).val = gs (𝟙 _) z _ (C.ρ 0 i j) ^ k * (gm (𝟙 _) z _ (u i m)).val := by
      have hW := (gm (𝟙 (Y 0).left) z _ (w.s (a, fun _ => m))).isUnit
      apply hW.mul_left_cancel
      rw [mul_comm _ (gm (𝟙 _) z _ (u j m)).val, ← hsj, hrel, mul_pow, hsi]
      ring
    have hsub := gs_pull (𝟙 _) (γ e) z (C.D e i ⊓ C.D e j) hz' ((g i j).val - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k)
    rw [Category.id_comp] at hsub
    have h0 : gs (𝟙 _) z (γ e ⁻¹ᵁ (C.D e i ⊓ C.D e j)) 0 = 0 := by rw [gs_eq _ z _ hz, map_zero, map_zero]
    rw [h0, hsub, gs_eq _ z _ hz', map_sub, map_sub, ← gs_eq _ z _ hz', ← gs_eq _ z _ hz', hgz, hρz, hu']
    rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one, sub_self]
  rw [hk] at hmem
  simpa only [towerIdeal, zero_add, pow_one] using hmem
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg.LiftCech

variable {R : Type} [CommRing R]

theorem map_cst_rs {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (J : Ideal R) {U V : X.Opens}
    (h : V ≤ U) {x : Γ(X, U)} (hx : x ∈ J.map (cst f U)) : rs X h x ∈ J.map (cst f V) := by
  have h' := Ideal.mem_map_of_mem (rs X h) hx
  rw [Ideal.map_map] at h'
  have e : (rs X h).comp (cst f U) = cst f V := RingHom.ext fun r => rs_cst f h r
  rwa [e] at h'

theorem gs_sub' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a - b) = gs f y U a - gs f y U b := by
  simp only [gs_eq f y U h, map_sub]

theorem gs_zero' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs
  split <;> simp

end GlobalTheory.FormalAlg.LiftCech


open GlobalTheory.FormalAlg.LiftCech in
theorem GlobalTheory.FormalAlg.lift_cech : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (e k : ℕ), (∀ c : ∀ i j, Γ((Y (e + 1)).left, C.D (e + 1) i ⊓ C.D (e + 1) j), (∀ i j, c i j ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _) → (∀ i j l, rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) j) (c i j) + rs (Y (e + 1)).left (inf_le_left.trans inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) j ⊓ C.D (e + 1) l) (c j l) = rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) l) (c i l)) → ∃ a : ∀ i, Γ((Y (e + 1)).left, C.D (e + 1) i), (∀ i, a i ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _) ∧ ∀ i j, c i j = rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (a i) - rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (a j)) → ∀ g : ∀ i j, Γ((Y (e + 1)).left, C.D (e + 1) i ⊓ C.D (e + 1) j)ˣ, (⟨Fin (n + 1), C.D (e + 1), g⟩ : LB (Y (e + 1)).left).IsLB → (∀ i j, (g i j).val - rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k ∈ towerIdeal Y (e + 1) I _) → ∀ σ : ∀ i, Γ((Y e).left, β e ⁻¹ᵁ C.D (e + 1) i), (∀ z i j, β e z ∈ C.D (e + 1) i → β e z ∈ C.D (e + 1) j → gs (𝟙 _) z _ (σ i) = gs (β e) z _ (g i j).val * gs (𝟙 _) z _ (σ j)) → ∃ σ' : LB.Sec (⟨Fin (n + 1), C.D (e + 1), g⟩ : LB (Y (e + 1)).left), ∀ i, ((β e).app (C.D (e + 1) i)).hom (σ'.f i) = σ i := by
  intro R _ I Y β hβ n C e k hH g hg hgρ σ hσ
  have hbp := (GlobalTheory.T.isPullback_thick_tower_squares R I Y β hβ).1 e
  have hk := GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R (I ^ (e + 1)) _ _ _ (β e) (Y e).hom hbp
  have hbas := (GlobalTheory.T.thickeningTower_liftedRatios_projective_relations R I Y β hβ n C).1 (e + 1)
  have hz := (GlobalTheory.T.thickeningTower_liftedRatios_generate_surjective R I Y β hβ n C).1 (e + 1)
  have hA : ∀ i j, IsAffineOpen (C.D (e + 1) i ⊓ C.D (e + 1) j) := fun i j =>
    hbas i j ▸ (C.aff (e + 1) i).basicOpen _
  have hker : ∀ (V : (Y (e + 1)).left.Opens), IsAffineOpen V → ∀ x,
      ((β e).app V).hom x = 0 ↔ x ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) V := fun V hV x => by
    rw [← RingHom.mem_ker, (hk.2.2 V hV).2]; rfl
  have hmem : ∀ (J : Ideal R) {U V : (Y (e + 1)).left.Opens} (h : V ≤ U) {x : Γ((Y (e + 1)).left, U)},
      x ∈ towerIdeal Y (e + 1) J U → rs (Y (e + 1)).left h x ∈ towerIdeal Y (e + 1) J V :=
    fun J _ _ h _ hx => map_cst_rs _ J h hx
  have hmul : ∀ (V : (Y (e + 1)).left.Opens) (x y : Γ((Y (e + 1)).left, V)), x ∈ towerIdeal Y (e + 1) I V →
      y ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) V → x * y = 0 := by
    intro V x y hx hy
    have h := Ideal.mul_mem_mul hx hy
    unfold towerIdeal at h
    rw [← Ideal.map_mul, ← pow_succ'] at h
    have h0 := hz V
    unfold towerIdeal at h0
    rw [h0] at h
    exact (Submodule.mem_bot _).1 h
  choose τ hτ using fun i => (hk.2.2 _ (C.aff (e + 1) i)).1 (σ i)
  have key : ∀ (x : (Y e).left) i, β e x ∈ C.D (e + 1) i →
      gs (β e) x (C.D (e + 1) i) (τ i) = gs (𝟙 _) x _ (σ i) := fun x i hxi => by
    rw [← hτ i, gs_pull (𝟙 _) (β e) x _ hxi, Category.id_comp]
  let c : ∀ i j, Γ((Y (e + 1)).left, C.D (e + 1) i ⊓ C.D (e + 1) j) := fun i j =>
    rs _ (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (τ i) -
      (g i j).val * rs _ (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (τ j)
  have hcdef : ∀ i j, c i j = rs _ (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (τ i) -
      (g i j).val * rs _ (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (τ j) := fun _ _ => rfl
  have hc : ∀ i j, c i j ∈ towerIdeal Y (e + 1) (I ^ (e + 1)) _ := by
    intro i j
    rw [← hker _ (hA i j)]
    apply fn_ext
    intro x hx
    have hxi : β e x ∈ C.D (e + 1) i := hx.1
    have hxj : β e x ∈ C.D (e + 1) j := hx.2
    rw [gs_pull (𝟙 _) (β e) x _ hx, Category.id_comp, gs_zero',
      hcdef, gs_sub' _ _ _ hx, gs_mul _ _ _ hx, gs_res _ _ _ hx, gs_res _ _ _ hx, key x i hxi, key x j hxj,
      hσ x i j hxi hxj, sub_self]
  have hcoc : ∀ i j l, rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) j) (c i j) + rs (Y (e + 1)).left (inf_le_left.trans inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) j ⊓ C.D (e + 1) l) (c j l) = rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) l) (c i l) := by
    intro i j l
    have h1 : rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) j) (g i j).val * rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) j ⊓ C.D (e + 1) l) (c j l) = rs (Y (e + 1)).left (inf_le_left.trans inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) j ⊓ C.D (e + 1) l) (c j l) := by
      rw [← sub_eq_zero, ← sub_mul]
      refine hmul _ _ _ ?_ (hmem _ _ (hc j l))
      have h := hmem I (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) i ⊓ C.D (e + 1) j) (hgρ i j)
      rwa [map_sub, map_pow, rs_rs] at h
    have hco := congrArg Units.val (hg.cocycle i j l)
    simp only [res, Units.val_mul, Units.coe_map, MonoidHom.coe_coe] at hco
    rw [← h1, hcdef, hcdef, hcdef]
    simp only [map_sub, map_mul, rs_rs]
    linear_combination (-(rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ⊓ C.D (e + 1) l ≤ C.D (e + 1) l) (τ l))) * hco
  obtain ⟨a, ha, hca⟩ := hH c hc hcoc
  refine ⟨⟨fun i => τ i - a i, fun i j => ?_⟩, fun i => ?_⟩
  · have h2 : (g i j).val * rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (a j) = rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (C.ρ (e + 1) i j) ^ k * rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (a j) := by
      rw [← sub_eq_zero, ← sub_mul]
      exact hmul _ _ _ (hgρ i j) (hmem _ _ (ha j))
    have h3 := hca i j
    rw [hcdef] at h3
    change rs (Y (e + 1)).left (inf_le_left : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) i) (τ i - a i) = (g i j).val * rs (Y (e + 1)).left (inf_le_right : C.D (e + 1) i ⊓ C.D (e + 1) j ≤ C.D (e + 1) j) (τ j - a j)
    rw [map_sub, map_sub]
    linear_combination h3 + h2
  · change ((β e).app (C.D (e + 1) i)).hom (τ i - a i) = σ i
    rw [map_sub, hτ i, (hker _ (C.aff (e + 1) i) (a i)).2 (ha i), sub_zero]
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFam.Gen0

section General

variable {X Y : Scheme.{0}}

def fs {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) : FreeAddCommGroup (Y ⟶ X) :=
  ∑ k, ε k • FreeAddCommGroup.of (φ k)

theorem formEq_of_fs {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (h : fs φ ε = fs φ' ε') : FormEq φ ε φ' ε' := by
  intro U _ g
  have e := congrArg (FreeAddCommGroup.lift (fun ψ => Additive.ofMul (g ψ))) h

  simp only [fs, map_sum, map_zsmul, FreeAddCommGroup.lift_apply_of] at e
  apply Additive.ofMul.injective
  simpa [ofMul_prod, ofMul_zpow] using e

theorem oneGen_isGen' (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := by
  intro i j
  have e : (LB.LinComb L (Y := Y) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim).g i j = 1 := by
    dsimp only [LB.LinComb]
    erw [Fintype.prod_empty]
    rfl
  show res _ (1 : Γ(Y, _)ˣ) = _ * res _ (1 : Γ(Y, _)ˣ)
  rw [map_one, map_one, e, _root_.one_mul]

def genSub (L : LB X) (Y : Scheme.{0}) : AddSubgroup (FreeAddCommGroup (Y ⟶ X)) where
  carrier := {f | ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ), fs φ ε = f ∧
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen}
  zero_mem' := ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, by simp [fs], LB.oneGen L, oneGen_isGen' L⟩
  add_mem' := by
    rintro _ _ ⟨K, _, φ, ε, rfl, t, ht⟩ ⟨K', _, φ', ε', rfl, t', ht'⟩
    exact ⟨K ⊕ K', inferInstance, Sum.elim φ φ', Sum.elim ε ε', by simp [fs, Fintype.sum_sum_type],
      LB.mulGen L φ ε φ' ε' t t', DVR.mulGen_isGen L φ ε φ' ε' t t' ht ht'⟩
  neg_mem' := by
    rintro _ ⟨K, _, φ, ε, rfl, t, ht⟩
    exact ⟨K, inferInstance, φ, fun k => - ε k, by simp [fs, neg_smul, Finset.sum_neg_distrib],
      LB.invGen L φ ε t, DVR.invGen_isGen L φ ε t ht⟩

variable {L : LB X}

theorem mem_of_gen {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε))
    (ht : t.IsGen) : fs φ ε ∈ genSub L Y := ⟨K, inferInstance, φ, ε, rfl, t, ht⟩

theorem gen_of_mem (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : fs φ ε ∈ genSub L Y) : ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  obtain ⟨K', _, φ', ε', e, t, ht⟩ := h
  obtain ⟨t', ht', -⟩ := exists_gen hL (formEq_of_fs e) t ht
  exact ⟨t', ht'⟩

theorem exists_cl (hL : L.IsLB) (Y : Scheme.{0}) : ∃ (U : Type) (_ : CommGroup U) (c : (Y ⟶ X) → U),
    ∀ (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ),
      (∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen) ↔ ∏ k, c (φ k) ^ ε k = 1 := by
  refine ⟨Multiplicative (FreeAddCommGroup (Y ⟶ X) ⧸ genSub L Y), inferInstance,
    fun ψ => Multiplicative.ofAdd (QuotientAddGroup.mk' _ (FreeAddCommGroup.of ψ)), fun K _ φ ε => ?_⟩
  have e : ∏ k, Multiplicative.ofAdd (QuotientAddGroup.mk' (genSub L Y) (FreeAddCommGroup.of (φ k))) ^ ε k =
      Multiplicative.ofAdd (QuotientAddGroup.mk' (genSub L Y) (fs φ ε)) := by

    simp only [fs, map_sum, map_zsmul, ofAdd_sum, ofAdd_zsmul]
  rw [e, ofAdd_eq_one, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  exact ⟨fun ⟨t, ht⟩ => mem_of_gen t ht, gen_of_mem hL⟩

end General

section Deg

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem exists_gen_twist [IsLocalRing R] (a : D.P.A ⟶ D.P.A) [IsMonHom a] (n j : ℤ) (mu ν δ β : D.X)
    (hν : D.c ν = D.c mu ≫ a) (u : LB.Gen (IotaLB D a ν δ)) (hu : u.IsGen) :
    ∃ u₀ : LB.Gen (LB.LinComb D.P.L (Sum.elim (tφ D a (β + (n • mu + j • δ)))
      (fun k => (padd D.P.A (𝟙 _) (toUnit _ ≫ D.c mu)).left ≫ tφ D a β k)) (dε n j)), u₀.IsGen := by
  obtain ⟨U, _, c, hc⟩ := exists_cl D.P.isLB D.P.A.left
  have k₀ : ∀ q : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A, c (toUnit D.P.A ≫ q).left = 1 := fun q => by
    obtain ⟨t, ht⟩ := DVR.exists_gen_of_local (V := R) D.P.L D.P.isLB (K := PUnit) (fun _ => q.left) (fun _ => 1)
    have h := (hc PUnit (fun _ => (toUnit D.P.A).left ≫ q.left) (fun _ => 1)).1 ⟨_, DVR.pullGen_isGen _ _ _ _ ht _⟩
    rw [Fintype.prod_unique, zpow_one] at h
    exact h
  have k₁ : c (1 : D.P.A ⟶ D.P.A).left = 1 := k₀ _
  have k₂ : ∀ χ, c (DVR.cP D D.P.A χ).left = 1 := fun χ => k₀ _
  have sq : ∀ χ χ', c (𝟙 _ * DVR.cP D D.P.A (χ + χ')).left / c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left =
      c (𝟙 _ * DVR.cP D D.P.A χ).left / c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left *
        (c (𝟙 _ * DVR.cP D D.P.A χ').left / c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left) := fun χ χ' => by
    have h := (prod_cub (𝟙 D.P.A) (DVR.cP D _ χ) (DVR.cP D _ χ') c).symm.trans ((hc thK _ thε).1
      ⟨LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t _, DVR.pullGen_isGen _ _ _ _ D.cub.isGen _⟩)
    rw [_root_.mul_assoc (𝟙 D.P.A), ← DVR.cPoint_add, k₂, k₂, k₂, k₁] at h
    rw [← div_eq_one, ← h]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_div, ofMul_one]
    abel
  let Φ : D.X →+ Additive U := AddMonoidHom.mk' (fun χ => Additive.ofMul
    (c (𝟙 _ * DVR.cP D D.P.A χ).left / c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left)) (fun χ χ' => congrArg Additive.ofMul (sq χ χ'))
  have e : ∀ χ, Additive.ofMul (c (𝟙 _ * DVR.cP D D.P.A χ).left) =
      Φ χ + Additive.ofMul (c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left) := fun χ =>
    congrArg Additive.ofMul (div_mul_cancel _ _).symm
  clear_value Φ
  have e₃ : Additive.ofMul (c (a * DVR.cP D _ ν).left) = Φ δ + Additive.ofMul (c a.left) := by
    have h := (hc _ _ _).1 ⟨u, hu⟩
    rw [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four] at h
    have h' : c (𝟙 _ * DVR.cP D D.P.A δ).left ^ (1 : ℤ) * c (DVR.cP D D.P.A δ).left ^ (-1 : ℤ) *
        c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left ^ (-1 : ℤ) * c (1 : D.P.A ⟶ D.P.A).left ^ (1 : ℤ) *
        (c (a * DVR.cP D D.P.A ν).left ^ (-1 : ℤ) * c (DVR.cP D D.P.A ν).left ^ (1 : ℤ) * c a.left ^ (1 : ℤ) *
          c (1 : D.P.A ⟶ D.P.A).left ^ (-1 : ℤ)) = 1 := h
    have h'' := congrArg Additive.ofMul h'
    simp only [ofMul_mul, ofMul_zpow, k₁, k₂, e, ofMul_one] at h''
    rw [eq_comm, ← sub_eq_zero, ← h'']
    module
  let T : D.P.A ⟶ D.P.A := 𝟙 _ * DVR.cP D _ mu
  have i₀ : T ≫ 𝟙 _ = 𝟙 _ * DVR.cP D _ mu := Category.comp_id _
  have i₁ : T ≫ (𝟙 _ * DVR.cP D _ β) = 𝟙 _ * DVR.cP D _ (mu + β) := by
    rw [MonObj.comp_mul, DVR.comp_cP, i₀, DVR.cPoint_add, _root_.mul_assoc]
  have i₂ : T ≫ DVR.cP D _ β = DVR.cP D _ β := DVR.comp_cP D _ _
  have i₃ : T ≫ (1 : D.P.A ⟶ D.P.A) = 1 := MonObj.comp_one _
  have i₄ : T ≫ a = a * DVR.cP D _ ν := by
    rw [MonObj.mul_comp, Category.id_comp, DVR.cP, DVR.cP, hν, Category.assoc]
  have h : c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left ^ (n - 1) * c (𝟙 _ * DVR.cP D D.P.A (β + (n • mu + j • δ))).left ^ (1 : ℤ) *
      c (DVR.cP D D.P.A (β + (n • mu + j • δ))).left ^ (-1 : ℤ) * c (1 : D.P.A ⟶ D.P.A).left ^ (1 : ℤ) * c a.left ^ j *
      (c (T ≫ 𝟙 _).left ^ (-(n - 1)) * c (T ≫ (𝟙 _ * DVR.cP D _ β)).left ^ (-1 : ℤ) *
        c (T ≫ DVR.cP D _ β).left ^ (-(-1) : ℤ) * c (T ≫ (1 : D.P.A ⟶ D.P.A)).left ^ (-1 : ℤ) * c (T ≫ a).left ^ (-j)) = 1 := by
    rw [i₀, i₁, i₂, i₃, i₄]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, k₁, k₂, e, e₃, ofMul_one, map_add (f := _), map_zsmul]
    module
  refine (hc _ _ _).2 ?_
  rw [Fintype.prod_sum_type, Fin.prod_univ_five, Fin.prod_univ_five]
  exact h

end Deg

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (n j : ℤ) (mu β β' : D.toPre.X), β' = β + shift h h' n j mu → ∃ u₀ : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (tφ D.toPre a β') (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c mu)).left ≫ tφ D.toPre a β k)) (dε n j)), u₀.IsGen := by
  intro R _ _ _ hR D a a' h h' hE n j mu β β' hβ
  obtain ⟨u, hu, -⟩ := exists_iota R hR D a a' h h' hE (h mu)
  haveI := hE.1
  subst hβ
  exact exists_gen_twist D.toPre a n j mu (h mu) (h' (h mu)) β (hE.2.2.2.1 mu) u hu

end GlobalTheory.TwFam.Gen0
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.exists_mumfordTerm_translate_normalisedGenerator : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X) (N : ℕ) (s₀ : SecT D.toPre a N (-1) 0) (ν : D.toPre.X) (u₀ : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (tφ D.toPre a (shift h h' N (-1) ν)) (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c ν)).left ≫ tφ D.toPre a 0 k)) (dε N (-1)))), u₀.IsGen → ∀ ρ : R, (∀ u, IsFac D.toPre a h N (-1) ν 0 (shift h h' N (-1) ν) u → ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → (val u x z J).val = gs x z ⊤ (scal ((fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left : (DegPre.BF D.toPre (FractionRing R)).left ⟶ Sp (FractionRing R)) (algebraMap R (FractionRing R) ρ)) * (val u₀ (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J).val) → ∃ t : SecT D.toPre a N (-1) (shift h h' N (-1) ν), TRel h ν s₀ t ∧ ∀ e : ℕ, ρ ∈ maximalIdeal R ^ (e + 1) → Van (maximalIdeal R) t e := by
  first | exact @GlobalTheory.MumTerm.exists_term | exact GlobalTheory.MumTerm.exists_term | (intros; apply GlobalTheory.MumTerm.exists_term <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.exists_cubeProduct_twistedSections_vanishing : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (n j n' j' n'' j'' : ℤ), n'' = n + n' → j'' = j + j' → ∀ (β β' : D.toPre.X) (f : SecT D.toPre a n j β) (g : SecT D.toPre a n' j' β'), ∃ p : SecT D.toPre a n'' j'' (β + β'), IsProdT f g p ∧ ∀ e, (Van (maximalIdeal R) f e ∨ Van (maximalIdeal R) g e) → Van (maximalIdeal R) p e := by
  first | exact @GlobalTheory.TwFam.exists_prodT_van | exact GlobalTheory.TwFam.exists_prodT_van | (intros; apply GlobalTheory.TwFam.exists_prodT_van <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.twistedExpansion_adicSums_admissibleBase : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ (e : ℕ) (b : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), ∀ (n j : ℤ) (τ : SecE U.toUnifPre b n j) (Ix : Type) (w : Ix → D.toPre.X) (s : ∀ i, SecT D.toPre a n j (w i)) (F : ∀ β, SecT D.toPre a n j β), Small (maximalIdeal R) s → IsSum (maximalIdeal R) s F → TExp U.toUnifPre τ s → TExp U.toUnifPre τ (w := id) F := by
  first | exact @GlobalTheory.TwFam.texp_sum | exact GlobalTheory.TwFam.texp_sum | (intros; apply GlobalTheory.TwFam.texp_sum <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.twistedExpansion_mul_of_memberProducts : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ (e : ℕ) (b : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), ∀ (n j n' j' n'' j'' : ℤ), n'' = n + n' → j'' = j + j' → ∀ (f : ∀ β, SecT D.toPre a n j β) (g : ∀ β, SecT D.toPre a n' j' β) (p : ∀ q : D.toPre.X × D.toPre.X, SecT D.toPre a n'' j'' (q.1 + q.2)) (τ : SecE U.toUnifPre b n j) (τ' : SecE U.toUnifPre b n' j') (τ'' : SecE U.toUnifPre b n'' j''), Small (maximalIdeal R) (w := id) f → Small (maximalIdeal R) (w := id) g → (∀ q : D.toPre.X × D.toPre.X, IsProdT (f q.1) (g q.2) (p q)) → TExp U.toUnifPre τ (w := id) f → TExp U.toUnifPre τ' (w := id) g → (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ'' x z J' = sval τ x z J' * sval τ' x z J') → TExp U.toUnifPre τ'' (w := fun q : D.toPre.X × D.toPre.X => q.1 + q.2) p := by
  first | exact @GlobalTheory.TwFam.texp_mul_of_prod | exact GlobalTheory.TwFam.texp_mul_of_prod | (intros; apply GlobalTheory.TwFam.texp_mul_of_prod <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.exists_adicSum_twistedSectionFamily_tendsToZero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (n j : ℤ) (Ix : Type) (w : Ix → D.toPre.X) (s : ∀ i, SecT D.toPre a n j (w i)), Small (maximalIdeal R) s → ∃ F : ∀ β, SecT D.toPre a n j β, IsSum (maximalIdeal R) s F ∧ Small (maximalIdeal R) (w := id) F := by
  first | exact @GlobalTheory.TwFam.AdicSum.exists_isSum | exact GlobalTheory.TwFam.AdicSum.exists_isSum | (intros; apply GlobalTheory.TwFam.AdicSum.exists_isSum <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.twistedFactor_exists_unique_const_mul_integralGenerator : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (h : D.toPre.X →+ D.toPre.X), IsMonHom a → (∀ y, D.toPre.c (h y) = D.toPre.c y ≫ a) → ∀ (n j : ℤ) (mu β β' : D.toPre.X) (u₀ : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (tφ D.toPre a β') (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c mu)).left ≫ tφ D.toPre a β k)) (dε n j))), u₀.IsGen → (∃ u, IsFac D.toPre a h n j mu β β' u) ∧ (∀ u u', IsFac D.toPre a h n j mu β β' u → IsFac D.toPre a h n j mu β β' u' → ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → val u x z J = val u' x z J) ∧ ∀ u : LB.Gen (LB.LinComb D.toPre.P.L (dφ D.toPre a mu β β') (dε n j)), u.IsGen → ∃ c : (FractionRing R), ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → (val u x z J).val = gs x z ⊤ (scal ((fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left : (DegPre.BF D.toPre (FractionRing R)).left ⟶ Sp (FractionRing R)) c) * (val u₀ (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J).val := by
  exact @GlobalTheory.TwFac.fac_exists_unique_const
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

theorem _root_.GlobalTheory.T.peterssonNorm_eq_of_levelCover_pullback : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → Even n → ∀ (f : cuspW Xo c U (wtZ a n)) (g : cuspW d.Xo₂ d.c₂ U₂ (wtZ a n)), Pull d (f : Rul Xo c) (g : Rul d.Xo₂ d.c₂) → ∀ σ₂ : d.c₂.F →+* ℂ, normW U₂ (xiR D) (fun _ => D.sp.W j) dict₂ (wtZ a n) σ₂ g = normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) (σ₂.comp (d.eF : c.F →+* d.c₂.F)) f := by
  first | exact @GlobalTheory.LevPullNorm.levPull_normW | exact GlobalTheory.LevPullNorm.levPull_normW | (intros; apply GlobalTheory.LevPullNorm.levPull_normW <;> assumption)
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

theorem _root_.GlobalTheory.T.cuspForm_iff_levelCover_pullback : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → Even n → ∀ f ∈ sec Xo c a n, ∀ g ∈ sec d.Xo₂ d.c₂ a n, Pull d f g → (g ∈ cusp d.Xo₂ d.c₂ U₂ a n ↔ f ∈ cusp Xo c U a n) := by
  first | exact @GlobalTheory.LevCusp.cusp_iff_pull | exact GlobalTheory.LevCusp.cusp_iff_pull | (intros; apply GlobalTheory.LevCusp.cusp_iff_pull <;> assumption)
end
