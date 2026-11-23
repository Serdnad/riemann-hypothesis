module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle668
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle667

@[expose] public section

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory.PolFan.Mark.SplitPull

theorem apply_eq_zero_of_isotropic {X : Type} [AddCommGroup X] {x : LinearMap.BilinForm ℤ X}
    (hs : ∀ y z, x y z = x z y) (hp : ∀ y, 0 ≤ x y y) {d : X} (hd : x d d = 0) (z : X) : x d z = 0 := by
  by_contra h
  have h1 := hp ((-(x d z * (x z z + 1))) • d + z)
  simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hd, hs z d] at h1
  have h2 : 1 ≤ x d z * x d z := mul_self_pos.2 h
  have h3 := hp z
  nlinarith [mul_le_mul_of_nonneg_right h2 (show 0 ≤ x z z + 1 by omega)]

variable {O : Type} [CommRing O] {bar : O → O} {ψ lab : InvFun O}
  {X X₁ : Type} [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁]
  {r : X →ₗ[O] X₁} {s : X₁ →ₗ[O] X}

def pullHom (r : X →ₗ[O] X₁) : LinearMap.BilinForm ℤ X₁ →ₗ[ℤ] LinearMap.BilinForm ℤ X where
  toFun := pull r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pull_pull (h : ∀ a, r (s a) = a) (β : LinearMap.BilinForm ℤ X₁) : pull s (pull r β) = β :=
  LinearMap.ext₂ fun a b => by simp [h]

theorem pull_injective (h : ∀ a, r (s a) = a) : Function.Injective (pull r) :=
  Function.LeftInverse.injective (pull_pull h)

theorem eq_pull (h : ∀ a, r (s a) = a) {β : LinearMap.BilinForm ℤ X₁} {x : LinearMap.BilinForm ℤ X}
    (hs : ∀ y z, x y z = x z y) (hp : ∀ y, 0 ≤ x y y) (hv : ∀ y, pull r β y y = 0 → x y y = 0) :
    pull r (pull s x) = x := by
  have key : ∀ a z, x (s (r a)) z = x a z := fun a z => by
    have := apply_eq_zero_of_isotropic hs hp (hv (a - s (r a)) (by simp [h])) z
    rw [map_sub, LinearMap.sub_apply] at this
    omega
  refine LinearMap.ext₂ fun a b => ?_
  rw [pull_apply, pull_apply, key, hs, key, hs]

variable [Module.Finite O X] [Module.Finite O X₁]

theorem inFace_pull_iff (h : ∀ a, r (s a) = a) {β x : LinearMap.BilinForm ℤ X₁} :
    InFace bar ψ lab (pull r β) (pull r x) ↔ InFace bar ψ lab β x := by
  have hr : Function.Surjective r := fun a => ⟨s a, h a⟩
  have e : pull r β + pull r x = pull r (β + x) := rfl
  unfold InFace
  rw [e]
  simp only [evalZ_pull _ hr, pull_apply]
  refine and_congr ⟨fun hx => ?_, pull_mem r⟩ (and_congr (hr.forall (p := fun y => 0 ≤ x y y)).symm
    (and_congr (hr.forall (p := fun y => β y y = 0 → x y y = 0)).symm Iff.rfl))
  rw [← pull_pull h x]
  exact pull_mem s hx

theorem InFace_eq_pull (h : ∀ a, r (s a) = a) {β : LinearMap.BilinForm ℤ X₁} {x : LinearMap.BilinForm ℤ X}
    (hx : InFace bar ψ lab (pull r β) x) : ∃ x₁, pull r x₁ = x :=
  ⟨_, eq_pull h hx.1.1 hx.2.1 hx.2.2.1⟩

theorem isIndec_pull_iff (h : ∀ a, r (s a) = a) {β x : LinearMap.BilinForm ℤ X₁} :
    IsIndec bar ψ lab (pull r β) (pull r x) ↔ IsIndec bar ψ lab β x := by
  have hne : ∀ y : LinearMap.BilinForm ℤ X₁, pull r y ≠ 0 ↔ y ≠ 0 := fun y =>
    (pull_injective h).ne_iff' (rfl : pull r 0 = 0)
  refine and_congr (inFace_pull_iff h) (and_congr (hne x) ⟨fun H y z hy hz y0 z0 e => ?_, fun H y z hy hz y0 z0 e => ?_⟩)
  · exact H _ _ ((inFace_pull_iff h).2 hy) ((inFace_pull_iff h).2 hz) ((hne y).2 y0) ((hne z).2 z0) (by rw [← e]; rfl)
  · obtain ⟨y, rfl⟩ := InFace_eq_pull h hy
    obtain ⟨z, rfl⟩ := InFace_eq_pull h hz
    exact H y z ((inFace_pull_iff h).1 hy) ((inFace_pull_iff h).1 hz) ((hne y).1 y0) ((hne z).1 z0)
      (pull_injective h e)

theorem isMarked_pull_iff' (h : ∀ a, r (s a) = a) (i : ℕ) (β : LinearMap.BilinForm ℤ X₁) :
    IsMarked bar ψ lab i X (pull r β) ↔ IsMarked bar ψ lab i X₁ β := by
  classical
  have hr : Function.Surjective r := fun a => ⟨s a, h a⟩
  have hsum : ∀ S : Finset (LinearMap.BilinForm ℤ X₁), ∑ x ∈ S.map ⟨pull r, pull_injective h⟩, x = pull r (∑ x ∈ S, x) :=
    fun S => by
      rw [Finset.sum_map]
      exact (map_sum (pullHom r) (fun x => x) S).symm
  unfold IsMarked
  rw [evalZ_pull _ hr]
  refine and_congr ⟨fun hx => ?_, pull_mem r⟩ (and_congr (hr.forall (p := fun y => 0 ≤ β y y)).symm
    (and_congr ⟨fun H k β' e => H k (pull r β') (by rw [← e]; rfl), fun H k β' e => H k (pull s β') ?_⟩
      (and_congr Iff.rfl ⟨?_, ?_⟩)))
  · rw [← pull_pull h β]
    exact pull_mem s hx
  · rw [← pull_pull h β, ← e]; rfl
  · rintro ⟨S, hS, k, hk, e⟩
    have hS' : (S.preimage (pull r) (pull_injective h).injOn).map ⟨pull r, pull_injective h⟩ = S := by
      ext x
      simp only [Finset.mem_map, Finset.mem_preimage, Function.Embedding.coeFn_mk]
      refine ⟨by rintro ⟨y, hy, rfl⟩; exact hy, fun hx => ?_⟩
      obtain ⟨y, rfl⟩ := InFace_eq_pull h ((hS x).1 hx).1
      exact ⟨y, hx, rfl⟩
    refine ⟨S.preimage (pull r) (pull_injective h).injOn, fun x => ?_, k, hk, pull_injective h ?_⟩
    · rw [Finset.mem_preimage, hS, isIndec_pull_iff h]
    · rw [← hsum, hS', ← e]; rfl
  · rintro ⟨S, hS, k, hk, e⟩
    refine ⟨S.map ⟨pull r, pull_injective h⟩, fun x => ?_, k, hk, ?_⟩
    · simp only [Finset.mem_map, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (isIndec_pull_iff h).2 ((hS y).1 hy)
      · intro hx
        obtain ⟨y, rfl⟩ := InFace_eq_pull h hx.1
        exact ⟨y, (hS y).2 ((isIndec_pull_iff h).1 hx), rfl⟩
    · rw [hsum, ← e]; rfl

theorem isMarked_pull_iff : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ lab : InvFun O) (i : ℕ) (X X₁ : Type)
    [AddCommGroup X] [Module O X] [Module.Finite O X] [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁]
    (r : X →ₗ[O] X₁) (s : X₁ →ₗ[O] X), (∀ a, r (s a) = a) → ∀ β : LinearMap.BilinForm ℤ X₁,
    IsMarked bar ψ lab i X (pull r β) ↔ IsMarked bar ψ lab i X₁ β :=
  fun _ _ _ _ _ i _ _ _ _ _ _ _ _ _ _ h β => isMarked_pull_iff' h i β

end GlobalTheory.PolFan.Mark.SplitPull
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

section Member

theorem finrank_int_eq_finrank_mul (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X] :
    Module.finrank ℤ X = Module.finrank ℚ E * Module.finrank (𝓞 E) X := by
  rw [← (TensorProduct.isBaseChange ℤ X ℚ).finrank_eq, ← (TensorProduct.isBaseChange (𝓞 E) X E).finrank_eq,
    Module.finrank_mul_finrank, (Algebra.IsPushout.cancelBaseChange ℤ ℚ (𝓞 E) E X).finrank_eq]

theorem free_int_of_projective (E : Type) [Field E] [NumberField E] {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]
    [Module.Finite (𝓞 E) Y] [Module.Projective (𝓞 E) Y] : Module.Free ℤ Y := by
  have : Module.Finite ℤ Y := Module.Finite.trans (𝓞 E) Y
  have : Module.IsTorsionFree ℤ Y := Module.IsTorsionFree.trans (𝓞 E)
  exact Module.free_of_finite_type_torsion_free'

theorem mem_psdCone_int {E : Type} [Field E] [NumberField E] (bar : 𝓞 E → 𝓞 E) {X : Type} [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hB : B ∈ psdCone (bar := bar) (X := X)) : B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X) := by
  obtain ⟨X₁, _, _, _, r, B₁, hr, h1, h2, h3⟩ := hB
  have : Module.Finite (𝓞 E) X₁ := Module.Finite.of_surjective r hr
  have : Module.Free ℤ X₁ := free_int_of_projective E
  exact ⟨X₁, _, _, inferInstance, r.restrictScalars ℤ, B₁, hr, ⟨h1.1, fun a y z => by simp⟩, h2, h3⟩

section ClassMin

open scoped Pointwise

variable {M n : ℕ} {C C' : (Fin n → ℤ) → (Fin n → ℤ) → ℝ}

theorem classMin_set_nonempty (M : ℕ) (C : (Fin n → ℤ) → (Fin n → ℤ) → ℝ) (y : Fin n → ZMod (M + 1)) :
    {x | ∃ a : Fin n → ℤ, redV M a = y ∧ C a a = x}.Nonempty := by
  obtain ⟨a, ha⟩ := redV_surjective M n y
  exact ⟨_, a, ha, rfl⟩

theorem classMin_set_bddBelow (hC : ∀ a, 0 ≤ C a a) (y : Fin n → ZMod (M + 1)) :
    BddBelow {x | ∃ a : Fin n → ℤ, redV M a = y ∧ C a a = x} :=
  ⟨0, by rintro _ ⟨a, -, rfl⟩; exact hC a⟩

theorem classMin_nonneg (hC : ∀ a, 0 ≤ C a a) (y : Fin n → ZMod (M + 1)) : 0 ≤ classMin M C y :=
  le_csInf (classMin_set_nonempty M C y) (by rintro _ ⟨a, -, rfl⟩; exact hC a)

theorem classMin_smul {t : ℝ} (ht : 0 ≤ t) (y : Fin n → ZMod (M + 1)) :
    classMin M (fun a b => t * C a b) y = t * classMin M C y := by
  unfold classMin
  have : {x | ∃ a : Fin n → ℤ, redV M a = y ∧ t * C a a = x} = t • {x | ∃ a : Fin n → ℤ, redV M a = y ∧ C a a = x} := by
    ext x
    simp only [Set.mem_smul_set, Set.mem_ofPred_eq, smul_eq_mul]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩; exact ⟨a, ha, rfl⟩
  rw [this, Real.sInf_smul_of_nonneg ht, smul_eq_mul]

theorem classMin_add_le (hC : ∀ a, 0 ≤ C a a) (hC' : ∀ a, 0 ≤ C' a a) (y : Fin n → ZMod (M + 1)) :
    classMin M C y + classMin M C' y ≤ classMin M (fun a b => C a b + C' a b) y := by
  refine le_csInf (classMin_set_nonempty M (fun a b => C a b + C' a b) y) ?_
  rintro _ ⟨a, ha, rfl⟩
  exact add_le_add (csInf_le (classMin_set_bddBelow hC y) ⟨a, ha, rfl⟩)
    (csInf_le (classMin_set_bddBelow hC' y) ⟨a, ha, rfl⟩)

theorem classMin_exists_nat {β : (Fin n → ℤ) → (Fin n → ℤ) → ℤ} (hβ : ∀ a, 0 ≤ β a a) (y : Fin n → ZMod (M + 1)) :
    ∃ k : ℕ, classMin M (fun a b => (β a b : ℝ)) y = k := by
  classical
  let T : Set ℕ := {k | ∃ a : Fin n → ℤ, redV M a = y ∧ β a a = k}
  have hT : T.Nonempty := by
    obtain ⟨a, ha⟩ := redV_surjective M n y
    exact ⟨(β a a).toNat, a, ha, (Int.toNat_of_nonneg (hβ a)).symm⟩
  obtain ⟨a₀, ha₀, e₀⟩ := Nat.sInf_mem hT
  refine ⟨sInf T, IsLeast.csInf_eq ⟨⟨a₀, ha₀, by simp only [e₀]; push_cast; rfl⟩, ?_⟩⟩
  rintro _ ⟨a, ha, rfl⟩
  have h1 : sInf T ≤ (β a a).toNat := Nat.sInf_le ⟨a, ha, (Int.toNat_of_nonneg (hβ a)).symm⟩
  have h2 : ((β a a).toNat : ℤ) = β a a := Int.toNat_of_nonneg (hβ a)
  show ((sInf T : ℕ) : ℝ) ≤ (β a a : ℝ)
  rw [← h2]
  exact_mod_cast h1

end ClassMin

variable {X : Type} [AddCommGroup X] [Module.Finite ℤ X]

theorem fineMean_eval_eq (M : ℕ) {d : ℕ} {s : (Fin d → ℤ) →ₗ[ℤ] X} (hs : Function.Surjective s)
    (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    (fineMean M).eval X (fun a b => B a b) =
      (((M : ℝ) + 1) ^ d)⁻¹ * ∑ y, classMin M (fun a b => B (s a) (s b)) y := by
  rw [(fineMean M).eval_eq hs]
  show _ * _ - B (s 0) (s 0) = _
  simp

end Member

theorem baseFun_props : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g q : ℕ) (φs : InvFun ℤ)
    (𝓜 : Finset ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
    IsPolFan (id : ℤ → ℤ) g φs → Module.finrank ℚ E * q ≤ g → Module.finrank (𝓞 E) X ≤ q →
    (∀ B ∈ psdCone (bar := H.bar) (X := X), ∀ t : ℝ, 0 ≤ t → evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) (t • B) =
      t * evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) B) ∧
    (∀ B ∈ psdCone (bar := H.bar) (X := X), ∀ B' ∈ psdCone (bar := H.bar) (X := X), evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) B +
      evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) B' ≤ evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) (B + B')) ∧
    (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜).evalZ β = n) ∧
    (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜).evalZ β) := by
  intro E _ _ _ H g q φs 𝓜 X _ _ _ _ hφ hE hX
  have : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  have : Module.Free ℤ X := free_int_of_projective E
  have hd : Module.finrank ℤ X ≤ g := by
    rw [finrank_int_eq_finrank_mul E X]
    exact (Nat.mul_le_mul_left _ hX).trans hE
  have hφX : IsPolFanOn id φs X := hφ X hd
  set d := Module.finrank ℤ X with hd_def
  let b := Module.finBasis ℤ X
  let s : (Fin d → ℤ) →ₗ[ℤ] X := b.equivFun.symm.toLinearMap
  have hs : Function.Surjective s := b.equivFun.symm.surjective
  set D := fineDen g 𝓜 with hD
  have key : ∀ B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ, evalR (baseFun (𝓞 E) D φs 𝓜) B = D * (evalR φs B +
      ∑ M ∈ 𝓜, (((M : ℝ) + 1) ^ d)⁻¹ * ∑ y, classMin M (fun a b => B (s a) (s b)) y) := by
    intro B
    rw [evalR, eval_baseFun]
    simp only [fineMean_eval_eq _ hs]
    rfl
  have keyZ : ∀ β : LinearMap.BilinForm ℤ X, (baseFun (𝓞 E) D φs 𝓜).evalZ β = D * (φs.evalZ β +
      ∑ M ∈ 𝓜, (((M : ℝ) + 1) ^ d)⁻¹ * ∑ y, classMin M (fun a b => (β (s a) (s b) : ℝ)) y) := by
    intro β
    rw [← evalR_toReal, key, evalR_toReal]
    simp only [toReal_apply]
  refine ⟨fun B hB t ht => ?_, fun B hB B' hB' => ?_, fun β hβ hp => ?_, fun β hβ hp h0 => ?_⟩
  · have hB0 := nonneg_of_mem_psdCone hB
    rw [key, key, hφX.homog B (mem_psdCone_int _ hB) t ht]
    simp only [LinearMap.smul_apply, smul_eq_mul, classMin_smul ht, ← Finset.mul_sum]
    simp only [mul_left_comm _ t, ← Finset.mul_sum]
    ring
  · have h1 := hφX.superadd B (mem_psdCone_int _ hB) B' (mem_psdCone_int _ hB')
    have h2 : ∀ M ∈ 𝓜, (((M : ℝ) + 1) ^ d)⁻¹ * ∑ y, classMin M (fun a b => B (s a) (s b)) y +
        (((M : ℝ) + 1) ^ d)⁻¹ * ∑ y, classMin M (fun a b => B' (s a) (s b)) y ≤
        (((M : ℝ) + 1) ^ d)⁻¹ * ∑ y, classMin M (fun a b => (B + B') (s a) (s b)) y := fun M _ => by
      rw [← mul_add, ← Finset.sum_add_distrib]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => ?_) (by positivity)
      simp only [LinearMap.add_apply]
      exact classMin_add_le (fun a => nonneg_of_mem_psdCone hB _) (fun a => nonneg_of_mem_psdCone hB' _) y
    have h3 := Finset.sum_le_sum h2
    rw [Finset.sum_add_distrib] at h3
    rw [key, key, key, ← mul_add]
    exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  · obtain ⟨n, hn⟩ := hφX.integral β (mem_balForms_int.2 hβ.1) hp
    have hdiv : ∀ M ∈ 𝓜, ∃ e : ℕ, D = (M + 1) ^ d * e := fun M hM =>
      (pow_dvd_pow (M + 1) hd).trans (Finset.dvd_prod_of_mem (fun M => (M + 1) ^ g) hM)
    choose! e he using hdiv
    choose k hk using fun M y => classMin_exists_nat (M := M) (β := fun a b => β (s a) (s b)) (fun a => hp (s a)) y
    refine ⟨D * n + ∑ M ∈ 𝓜, (e M : ℤ) * ∑ y, (k M y : ℤ), ?_⟩
    rw [keyZ, hn]
    simp only [hk]
    push_cast
    rw [mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun M hM => ?_
    have hM : (D : ℝ) = ((M : ℝ) + 1) ^ d * e M := by exact_mod_cast he M hM
    rw [hM]
    field_simp
  · have h1 := hφX.pos β (mem_balForms_int.2 hβ.1) hp h0
    rw [keyZ]
    refine mul_pos (by exact_mod_cast fineDen_pos g 𝓜) (add_pos_of_pos_of_nonneg h1 (Finset.sum_nonneg fun M _ =>
      mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ => classMin_nonneg (fun a => ?_) y)))
    exact_mod_cast hp (s a)

end GlobalTheory.PolFan
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem cell_gen_mem_cone_of_smul : ∀ {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m m' : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin m' → LinearMap.BilinForm ℤ X)
    (i : Fin m) (k : ℕ) (a : Fin m' → ℕ), IsCell bar φ δ → IsCell bar φ γ → 0 < k → k • δ i = ∑ j, a j • γ j →
    ∀ j, 0 < a j → ∃ (k' : ℕ) (b : Fin m → ℕ), 0 < k' ∧ k' • γ j = ∑ l, b l • δ l := by
  intro O _ bar φ X _ _ _ m m' δ γ i k a hδ hγ hk he j hj
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hδ.strict

  have eδ : φ.evalZ (k • δ i) = k * φ.evalZ (δ i) := by
    have := hδ.linear (Pi.single i (k : ℝ)) fun l => by
      by_cases h : l = i
      · subst h; simp
      · simp [Pi.single_apply, h]
    simp only [Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    rw [InvFun.evalZ]
    convert this using 2
    funext x y
    simp
  have eγ : φ.evalZ (∑ j, a j • γ j) = ∑ j, (a j : ℝ) * φ.evalZ (γ j) := by
    have := hγ.linear (fun j => (a j : ℝ)) fun j => by positivity
    rw [InvFun.evalZ]
    convert this using 2
    funext x y
    simp [LinearMap.sum_apply]
  have ℓδ : (ℓ (k • δ i) : ℝ) = k * (N * φ.evalZ (δ i)) := by
    rw [map_nsmul, ← h1 i, nsmul_eq_mul]; push_cast; rfl
  have ℓγ : (ℓ (∑ j, a j • γ j) : ℝ) = ∑ j, (a j : ℝ) * ℓ (γ j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; push_cast; simp [map_nsmul]
  have key : ∑ j, (a j : ℝ) * ((ℓ (γ j) : ℝ) - N * φ.evalZ (γ j)) = 0 := by
    have e1 : (ℓ (∑ j, a j • γ j) : ℝ) = N * φ.evalZ (∑ j, a j • γ j) := by
      rw [← he, ℓδ, eδ]; ring
    rw [ℓγ, eγ, Finset.mul_sum] at e1
    simp only [mul_sub, Finset.sum_sub_distrib, e1]
    rw [sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ => by ring
  have nn : ∀ j ∈ Finset.univ, 0 ≤ (a j : ℝ) * ((ℓ (γ j) : ℝ) - N * φ.evalZ (γ j)) := fun j _ =>
    mul_nonneg (by positivity) (sub_nonneg.2 (h2 _ (hγ.mem j) (hγ.nonneg j)))
  have z := (Finset.sum_eq_zero_iff_of_nonneg nn).1 key j (Finset.mem_univ _)
  have ha : (a j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  have heq : (N : ℝ) * φ.evalZ (γ j) = ℓ (γ j) := by
    have := (mul_eq_zero.1 z).resolve_left ha
    linarith
  exact h3 _ (hγ.mem j) (hγ.nonneg j) heq

end GlobalTheory.PolFan
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem exists_smul_eq_sum_of_sum_toReal_eq {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X]
    [Module O X] [Module.Finite O X] {m m' : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin m' → LinearMap.BilinForm ℤ X)
    (c : Fin m' → ℝ) (hδ : IsCell bar φ δ) (hγ : IsCell bar φ γ) (hc : ∀ j, 0 ≤ c j)
    (hs : ∑ i, toReal (δ i) = ∑ j, c j • toReal (γ j)) :
    ∀ i, ∃ (k : ℕ) (a : Fin m' → ℕ), 0 < k ∧ k • δ i = ∑ j, a j • γ j := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict

  have hrel : ∑ i, (ℓ (δ i) : ℝ) = ∑ j, c j * (ℓ (γ j) : ℝ) := by
    have e := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) ℓ
      (β := Sum.elim δ γ) (c := Sum.elim (fun _ => (1 : ℝ)) (fun j => -c j)) (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, one_smul, neg_smul, Finset.sum_neg_distrib, hs,
          add_neg_cancel])
    rw [Fintype.sum_sum_type] at e
    simp only [Sum.elim_inl, Sum.elim_inr, one_mul, neg_mul, Finset.sum_neg_distrib] at e
    linarith

  have hlinγ := (linearOn_iff φ γ).1 hγ.linear c hc
  have hlinδ := (linearOn_iff φ δ).1 hδ.linear (fun _ => 1) (fun _ => zero_le_one)
  simp only [one_smul, one_mul] at hlinδ
  rw [hs, hlinγ] at hlinδ

  have hsum : ∑ i, ((ℓ (δ i) : ℝ) - N * φ.evalZ (δ i)) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hlinδ, hrel, Finset.mul_sum]
    simp only [h1]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_eq_zero fun j _ => by ring
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ (ℓ (δ i) : ℝ) - N * φ.evalZ (δ i) := fun i _ =>
    sub_nonneg.2 (h2 _ (hδ.mem i) (hδ.nonneg i))
  intro i
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum i (Finset.mem_univ _)
  exact h3 _ (hδ.mem i) (hδ.nonneg i) (by linarith)

end GlobalTheory.PolFan
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

section Mult

variable {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X]

def cellMult {m : ℕ} (δ : Fin m → balForms bar X) : ℕ :=
  Nat.card (Submodule.torsion ℤ (balForms bar X ⧸ Submodule.span ℤ (Set.range δ)))

def IsPrim (β : balForms bar X) : Prop :=
  ∀ (k : ℕ) (β' : balForms bar X), β = k • β' → k = 1

def maxMult (q : ℕ) (φ : InvFun O) : ℕ∞ :=
  ⨆ (X : Type) (_ : AddCommGroup X) (_ : Module O X) (_ : Module.Finite O X) (_ : Module.Projective O X)
    (_ : Module.finrank O X ≤ q) (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ)
    (_ : LinearIndependent ℤ δ) (_ : ∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)),
    ((cellMult bar fun i => (⟨δ i, h.mem i⟩ : balForms bar X)) : ℕ∞)

variable {bar}

theorem not_isPrim_zero : ¬ IsPrim bar (0 : balForms bar X) := fun h => by
  have := h 0 0 (by simp)
  exact zero_ne_one this

end Mult

end GlobalTheory.PolFan
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory

theorem finite_projective_int_of_ringOfIntegers :
    ∀ (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.Finite ℤ X ∧ Module.Projective ℤ X ∧ Module.finrank ℤ X = Module.finrank ℚ E * Module.finrank (𝓞 E) X := by
  intro E _ _ X _ _ _ _
  have hfin : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  have hflat : Module.Flat ℤ X := Module.Flat.trans ℤ (𝓞 E) X
  have hfree : Module.Free ℤ X := inferInstance
  refine ⟨hfin, inferInstance, ?_⟩
  rw [finrank_int_eq_mul_of_finite (O := 𝓞 E), RingOfIntegers.rank]

end GlobalTheory
end
