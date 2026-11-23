module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart

@[expose] public section

section

open GlobalTheory.KZ GlobalTheory.Ord2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V
open scoped MatrixGroups

namespace GlobalTheory.KZ

theorem Tower.kmap_refl {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (l : ℕ) [Fact l.Prime] (x : X.Khat l) : X.kmap l (RingEquiv.refl X.K) x = x := by
  unfold Tower.kmap
  have : (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map (RingEquiv.refl X.K).toMonoidHom))) =
      (LinearMap.id : Additive X.Kˣ →ₗ[ℤ] Additive X.Kˣ) := by
    ext x; rfl
  rw [this, LinearMap.baseChange_id, AdicCompletion.map_id]
  rfl

end GlobalTheory.KZ
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
open GlobalTheory.Sl2Ad

namespace GlobalTheory.Sl2Ad

theorem form_ne_zero_of_isIrr : ∀ {K : Type} [Field K] [CharZero K] {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin 2) K), IsIrr ρ →
    ∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, ad (ρ g) *ᵥ y = c • y) → form y y ≠ 0 := by
  intro K _ _ Γ _ ρ hirr y hy hstab hform
  have hq : y 0 * y 1 + y 2 * y 2 = 0 := by
    rw [form_apply] at hform
    have h2 : (2 : K) * (y 0 * y 1 + y 2 * y 2) = 0 := by linear_combination hform
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hconj : ∀ g, ∃ c : K, ofCoord y * (ρ g : Matrix (Fin 2) (Fin 2) K) = (ρ g : Matrix (Fin 2) (Fin 2) K) * (c • ofCoord y) := by
    intro g
    obtain ⟨c, hc⟩ := hstab g⁻¹
    refine ⟨c, ?_⟩
    have h1 := coord_conj_ofCoord (ρ g⁻¹) y
    rw [hc] at h1
    have htr : ((ρ g⁻¹ : Matrix (Fin 2) (Fin 2) K) * ofCoord y * (((ρ g⁻¹)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).trace = 0 := by
      rw [trace_conj, trace_ofCoord]
    have h2 := ofCoord_coord htr
    rw [h1] at h2
    have h3 : ofCoord (c • y) = c • ofCoord y := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [ofCoord]
    rw [h3, map_inv, inv_inv] at h2
    have hu : (ρ g : Matrix (Fin 2) (Fin 2) K) * (((ρ g)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hu, Matrix.one_mul]
  let Wk : Submodule K (Fin 2 → K) := LinearMap.ker (Matrix.mulVecLin (ofCoord y))
  have hmem : ∀ x, x ∈ Wk ↔ ofCoord y *ᵥ x = 0 := fun x => by
    simp [Wk, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  have hinv : IsInv ρ Wk := by
    intro g x hx
    rw [hmem] at hx ⊢
    obtain ⟨c, hc⟩ := hconj g
    have hs : (c • ofCoord y) *ᵥ x = c • (ofCoord y *ᵥ x) := by
      ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
    rw [Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec, hs, hx, smul_zero, Matrix.mulVec_zero]
  have hy0 : ∀ a b c : K, a = 0 → b = 0 → c = 0 → y 0 = a → y 1 = b → y 2 = c → False := by
    intro a b c ha hb hc h0 h1 h2
    apply hy
    ext i; fin_cases i
    · simpa [ha] using h0
    · simpa [hb] using h1
    · simpa [hc] using h2
  rcases hirr.2.2 Wk le_top hinv with h | h
  · have hv1 : (![y 0, -y 2] : Fin 2 → K) ∈ Wk := by
      rw [hmem]; ext i; fin_cases i <;> simp [ofCoord, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> first | linear_combination | linear_combination hq | linear_combination -hq
    have hv2 : (![y 2, y 1] : Fin 2 → K) ∈ Wk := by
      rw [hmem]; ext i; fin_cases i <;> simp [ofCoord, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> first | linear_combination | linear_combination hq | linear_combination -hq
    rw [h, Submodule.mem_bot] at hv1 hv2
    have a0 := congrFun hv1 0
    have a1 := congrFun hv1 1
    have b1 := congrFun hv2 1
    simp at a0 a1 b1
    exact hy0 0 0 0 rfl rfl rfl a0 b1 a1
  · have hv1 : (Pi.single 0 1 : Fin 2 → K) ∈ Wk := h ▸ Submodule.mem_top
    have hv2 : (Pi.single 1 1 : Fin 2 → K) ∈ Wk := h ▸ Submodule.mem_top
    rw [hmem] at hv1 hv2
    have a0 := congrFun hv1 0
    have a1 := congrFun hv1 1
    have b0 := congrFun hv2 0
    simp [ofCoord, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at a0 a1 b0
    exact hy0 0 0 0 rfl rfl rfl b0 a1 a0

end GlobalTheory.Sl2Ad
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
open GlobalTheory.Sl2Ad

namespace GlobalTheory

theorem ad_invariant_eq_zero_of_isIrr {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {Γ : Type} [Group Γ]
    (ρ : Γ →* GL (Fin 2) K) (hρ : IsIrr ρ) (v : Fin 3 → K) (hv : ∀ g, ad (ρ g) *ᵥ v = v) : v = 0 := by
  set Y : Matrix (Fin 2) (Fin 2) K := ofCoord v with hY

  have hcomm : ∀ g, ((ρ g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * Y = Y * (ρ g : Matrix (Fin 2) (Fin 2) K) := by
    intro g
    have h1 : coord ((ρ g : Matrix (Fin 2) (Fin 2) K) * Y * (((ρ g)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = coord Y := by
      rw [coord_conj_ofCoord, hv g, coord_ofCoord]
    have h2 : (ρ g : Matrix (Fin 2) (Fin 2) K) * Y * (((ρ g)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = Y := by
      have := congrArg ofCoord h1
      rwa [ofCoord_coord (by rw [trace_conj, trace_ofCoord]), ofCoord_coord (trace_ofCoord v)] at this
    calc (ρ g : Matrix (Fin 2) (Fin 2) K) * Y
        = (ρ g : Matrix (Fin 2) (Fin 2) K) * Y * (((ρ g)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (ρ g : Matrix (Fin 2) (Fin 2) K) := by
          rw [Matrix.mul_assoc _ _ (ρ g : Matrix (Fin 2) (Fin 2) K), ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      _ = Y * (ρ g : Matrix (Fin 2) (Fin 2) K) := by rw [h2]
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' Y)
  set W := Module.End.eigenspace (Matrix.toLin' Y) μ with hW
  have hWne : W ≠ ⊥ := Module.End.hasEigenvalue_iff.mp hμ
  have hWinv : IsInv ρ W := by
    intro g x hx
    rw [hW, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hx ⊢
    rw [Matrix.mulVec_mulVec, ← hcomm g, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]
  have hWtop : W = ⊤ := by
    rcases hρ.2.2 W le_top hWinv with h | h
    · exact absurd h hWne
    · exact h
  have hYμ : Y = μ • (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    have hx : (Pi.single j 1 : Fin 2 → K) ∈ W := by rw [hWtop]; trivial
    rw [hW, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, Matrix.mulVec_single_one] at hx
    have := congrFun hx i
    simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Pi.single_apply, Ne.symm hij]
  have htr : (2 : K) * μ = 0 := by
    have := trace_ofCoord v
    rw [← hY, hYμ, Matrix.trace_smul, Matrix.trace_one] at this
    simpa [mul_comm] using this
  have hμ0 : μ = 0 := by
    rcases mul_eq_zero.mp htr with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hY0 : Y = 0 := by rw [hYμ, hμ0, zero_smul]
  rw [← coord_ofCoord v, ← hY, hY0]
  ext i; fin_cases i <;> simp [coord]

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.KillsMuOrd

theorem pow_apply_of_apply {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : G ℚ Ω) (ζ : Ω) (k : ℕ)
    (h : s ζ = ζ ^ k) : ∀ n : ℕ, (s ^ n) ζ = ζ ^ (k ^ n) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, h, ← pow_mul, pow_succ', mul_comm]

theorem pow_fixes {Ω : Type} [Field Ω] [Algebra ℚ Ω] (l : ℕ) [hl : Fact l.Prime] (s : G ℚ Ω) (ζ : Ω)
    (hζ : ζ ^ l = 1) : (s ^ (l - 1)) ζ = ζ := by
  by_cases h1 : ζ = 1
  · subst h1; simp
  have hord : orderOf ζ = l := orderOf_eq_prime hζ h1
  have hprim : IsPrimitiveRoot ζ l := hord ▸ IsPrimitiveRoot.orderOf ζ
  have hsζ : (s ζ) ^ l = 1 := by rw [← map_pow, hζ, map_one]
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  obtain ⟨k, hk, hk'⟩ := hprim.eq_pow_of_pow_eq_one hsζ
  have hkl : ¬ l ∣ k := by
    rintro ⟨j, rfl⟩
    apply h1
    have : s ζ = 1 := by rw [← hk', pow_mul, hζ, one_pow]
    exact (map_eq_one_iff s s.injective).mp this
  rw [pow_apply_of_apply s ζ k hk'.symm]
  have hz : ((k : ZMod l)) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hf : ((k ^ (l - 1) : ℕ) : ZMod l) = ((1 : ℕ) : ZMod l) := by
    push_cast; exact ZMod.pow_card_sub_one_eq_one hz
  rw [ZMod.natCast_eq_natCast_iff] at hf
  rw [← pow_mod_orderOf, hord, hf, Nat.one_mod_eq_one.mpr hl.out.one_lt.ne', pow_one]

theorem charPow_sub_one_eq_one : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (l : ℕ) [Fact l.Prime] (C : Type) [Monoid C]
    (χ : G ℚ Ω →* C) (s : G ℚ Ω), KillsMu l χ → χ s ^ (l - 1) = 1 := by
  intro Ω _ _ l _ C _ χ s h
  rw [← map_pow]
  exact h _ fun ζ hζ => pow_fixes l s ζ hζ

end GlobalTheory.KillsMuOrd
end
