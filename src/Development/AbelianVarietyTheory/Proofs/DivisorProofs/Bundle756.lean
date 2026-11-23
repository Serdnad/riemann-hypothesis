module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.StarVirtualCharacterEqApplyInv
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle716
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle747
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatLoc
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem trace_fin_eq_sum_diag (m : ℕ) (A : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ)) :
    LinearMap.trace ℂ (Fin m → ℂ) A = ∑ i, A (Pi.single i 1) i := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin m)), LinearMap.toMatrix_eq_toMatrix',
    Matrix.trace]
  simp [LinearMap.toMatrix'_apply]

variable {G : Type} [Group G] [Fintype G]

theorem sum_char_inv_mul_char_eq_zero_iff {V W : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (σ : Representation ℂ G V) (ρ : Representation ℂ G W) :
    ∑ g, σ.character g⁻¹ * ρ.character g = 0 ↔ (Representation.linHom σ ρ).invariants = ⊥ := by
  have hpos : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := G)).ne'
  haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hpos
  have hfr := Representation.card_inv_mul_sum_char_eq_finrank (Representation.linHom σ ρ)
  simp only [Representation.char_linHom] at hfr
  constructor
  · intro h
    rw [h, mul_zero] at hfr
    apply Submodule.finrank_eq_zero.mp
    exact_mod_cast hfr.symm
  · intro hb
    rw [hb, finrank_bot, Nat.cast_zero] at hfr
    exact (mul_eq_zero.mp hfr).resolve_left (inv_ne_zero hpos)

theorem comm_of_mem_invariants {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ G V) (ρ : Representation ℂ G W) {p : V →ₗ[ℂ] W}
    (hp : p ∈ (Representation.linHom σ ρ).invariants) (g : G) (x : V) : p (σ g x) = ρ g (p x) := by
  have h := congrArg (fun F : V →ₗ[ℂ] W => F (σ g x)) (hp g)
  simp only [Representation.linHom_apply, LinearMap.comp_apply] at h
  rw [← h, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem invariants_bot_of_quot {U V W : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G U) (ρ' : Representation ℂ G V)
    (ρ : Representation ℂ G W) (hirr : ρ'.IsIrreducible) {p : U →ₗ[ℂ] V}
    (hp : p ∈ (Representation.linHom σ ρ').invariants) (hp0 : p ≠ 0)
    (hb : (Representation.linHom σ ρ).invariants = ⊥) :
    (Representation.linHom ρ' ρ).invariants = ⊥ := by

  let S : Subrepresentation ρ' :=
    { toSubmodule := LinearMap.range p
      apply_mem_toSubmodule := by
        rintro g _ ⟨x, rfl⟩
        exact ⟨σ g x, comm_of_mem_invariants σ ρ' hp g x⟩ }
  have hrange : ∀ y : V, y ∈ LinearMap.range p := by
    rcases hirr.eq_bot_or_eq_top S with h | h
    · exfalso
      apply hp0
      ext x
      have hx : p x ∈ S.toSubmodule := ⟨x, rfl⟩
      have hb0 : (⊥ : Subrepresentation ρ').toSubmodule = ⊥ := rfl
      rw [h, hb0] at hx
      exact (Submodule.mem_bot ℂ).mp hx
    · intro y
      have ht : (⊤ : Subrepresentation ρ').toSubmodule = ⊤ := rfl
      have : y ∈ (⊤ : Subrepresentation ρ').toSubmodule := by rw [ht]; exact Submodule.mem_top
      rw [← h] at this
      exact this
  rw [eq_bot_iff]
  intro q hq
  rw [Submodule.mem_bot]
  have hqp : q ∘ₗ p ∈ (Representation.linHom σ ρ).invariants := by
    intro g
    ext x
    simp only [Representation.linHom_apply, LinearMap.comp_apply]
    rw [← comm_of_mem_invariants ρ' ρ hq, ← comm_of_mem_invariants σ ρ' hp, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply]
  rw [hb, Submodule.mem_bot] at hqp
  ext y
  obtain ⟨x, rfl⟩ := hrange y
  exact LinearMap.congr_fun hqp x

theorem sum_trace_smul_eq_zero {m : ℕ} (ρ₀ : Representation ℂ G (Fin m → ℂ)) {V : Type} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (hbot : (Representation.linHom ρ₀ ρ).invariants = ⊥)
    (B : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ)) :
    ∑ g : G, LinearMap.trace ℂ (Fin m → ℂ) (B ∘ₗ ρ₀ g⁻¹) • ρ g = 0 := by
  have hsum : ∀ f : (Fin m → ℂ) →ₗ[ℂ] V, ∑ g : G, Representation.linHom ρ₀ ρ g f = 0 := by
    intro f
    have hm : ∑ g : G, Representation.linHom ρ₀ ρ g f ∈ (Representation.linHom ρ₀ ρ).invariants := by
      intro h

      rw [map_sum]
      simp only [← Module.End.mul_apply, ← map_mul]
      exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun _ => rfl)
    rw [hbot] at hm
    exact (Submodule.mem_bot ℂ).mp hm
  ext v
  have key : ∀ i : Fin m, ∑ g : G, (B (ρ₀ g⁻¹ (Pi.single i 1))) i • ρ g v = 0 := by
    intro i
    have := congrArg (fun F : (Fin m → ℂ) →ₗ[ℂ] V => F (Pi.single i 1))
      (hsum (((LinearMap.proj i : (Fin m → ℂ) →ₗ[ℂ] ℂ) ∘ₗ B).smulRight v))
    simpa [Representation.linHom_apply, LinearMap.sum_apply] using this
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply]
  simp only [trace_fin_eq_sum_diag, Finset.sum_smul, LinearMap.comp_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero (fun i _ => key i)

end GlobalTheory.Shin

namespace GlobalTheory.Shin

theorem kills_twist_of_pair_ne_zero : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ]
    (φ : Γ →* MulAut G) (s : Γ), ∀ (χ : G ⋊[φ] Γ → ℂ) (Y : G → ℂ), IsChar ℂ ℂ χ →
    IsIrrChar ℂ ℂ (fun g => χ (inl g)) → IsChar ℂ ℂ Y → ∑ᶠ g, χ (inl g) * star (Y g) ≠ 0 →
    Kills (fun δ => χ (inl δ * inr s)) Y := by
  intro G Γ _ _ _ _ φ s χ Y hχ hirr hY hne V _ _ _ ρ h
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Finite (G ⋊[φ] Γ) :=
    Finite.of_injective (fun x : G ⋊[φ] Γ => (x.left, x.right))
      (fun x y hxy => SemidirectProduct.ext (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
  obtain ⟨m, ρh, hρh⟩ := hχ
  obtain ⟨k, ρ', hρ'irr, hρ'⟩ := hirr
  obtain ⟨n, σ, hσ⟩ := hY
  have hχc : ∀ x, χ x = ρh.character x := fun x => by simpa using hρh x
  have hYc : ∀ g, Y g = σ.character g := fun g => by simpa using hσ g
  have h0c : ∀ g, χ (inl g) = ρ'.character g := fun g => by simpa using hρ' g
  have hst : ∀ g, star (Y g) = σ.character g⁻¹ := fun g => by
    rw [star_virt_eq_inv G Y (AddSubgroup.subset_closure ⟨n, σ, hσ⟩) g, hYc]
  rw [finsum_eq_sum_of_fintype] at h hne

  have hb : (Representation.linHom σ ρ).invariants = ⊥ := by
    rw [← sum_char_inv_mul_char_eq_zero_iff]
    simp only [hst] at h
    exact h

  have hne' : (Representation.linHom σ ρ').invariants ≠ ⊥ := by
    rw [Ne, ← sum_char_inv_mul_char_eq_zero_iff]
    intro h'
    apply hne
    rw [← h']
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hst, h0c, mul_comm]
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne'
  have hb' := invariants_bot_of_quot σ ρ' ρ hρ'irr hp hp0 hb

  let ρ₀ : Representation ℂ G (Fin m → ℂ) := ρh.comp (inl : G →* G ⋊[φ] Γ)
  have hρ₀ : ∀ g, ρ₀.character g = ρ'.character g := fun g => by
    rw [← h0c, hχc]; rfl
  have hb₀ : (Representation.linHom ρ₀ ρ).invariants = ⊥ := by
    rw [← sum_char_inv_mul_char_eq_zero_iff]
    have := (sum_char_inv_mul_char_eq_zero_iff ρ' ρ).mpr hb'
    simpa only [hρ₀] using this
  have hstf : ∀ g, star (χ (inl g * inr s)) =
      LinearMap.trace ℂ (Fin m → ℂ) (ρh (inr s⁻¹) ∘ₗ ρ₀ g⁻¹) := fun g => by
    rw [star_virt_eq_inv (G ⋊[φ] Γ) χ (AddSubgroup.subset_closure ⟨m, ρh, hρh⟩), hχc, mul_inv_rev,
      ← map_inv, ← map_inv]
    simp only [Representation.character, map_mul]
    rfl
  rw [finsum_eq_sum_of_fintype]
  simp only [hstf]
  exact sum_trace_smul_eq_zero ρ₀ ρ hb₀ _

end GlobalTheory.Shin
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem trace_pi_eq_sum (n : ℕ) (A : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) :
    LinearMap.trace ℂ (Fin n → ℂ) A = ∑ i, A (Pi.single i 1) i := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix',
    Matrix.trace]
  simp [LinearMap.toMatrix'_apply]

theorem kills_self : ∀ (G : Type) [Group G] [Finite G] (Y : G → ℂ), IsChar ℂ ℂ Y → Kills Y Y := by
  intro G _ _ Y hY V _ _ _ ρ h
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨n, σ, hσ⟩ := hY
  have hYc : ∀ g, Y g = σ.character g := fun g => by simpa using hσ g
  have hst : ∀ g, star (Y g) = σ.character g⁻¹ := fun g => by
    rw [star_virt_eq_inv G Y (AddSubgroup.subset_closure ⟨n, σ, hσ⟩) g, hYc]
  rw [finsum_eq_sum_of_fintype] at h
  rw [finsum_eq_sum_of_fintype]
  simp only [hst] at h ⊢

  have hinv : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    have : 0 < Nat.card G := Nat.card_pos
    exact_mod_cast this.ne')
  have hfr := Representation.card_inv_mul_sum_char_eq_finrank (Representation.linHom σ ρ)
  simp only [Representation.char_linHom] at hfr
  have h' : ∑ g : G, σ.character g⁻¹ * ρ.character g = 0 := h
  rw [h', mul_zero] at hfr
  have hbot : (Representation.linHom σ ρ).invariants = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    exact_mod_cast hfr.symm

  have hsum : ∀ f : (Fin n → ℂ) →ₗ[ℂ] V, ∑ g : G, Representation.linHom σ ρ g f = 0 := by
    intro f
    have hm : ∑ g : G, Representation.linHom σ ρ g f ∈ (Representation.linHom σ ρ).invariants := by
      intro h

      rw [map_sum]
      simp only [← Module.End.mul_apply, ← map_mul]
      exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun _ => rfl)
    rw [hbot] at hm
    exact (Submodule.mem_bot ℂ).mp hm
  ext v
  have key : ∀ i : Fin n, ∑ g : G, (σ g⁻¹ (Pi.single i 1)) i • ρ g v = 0 := by
    intro i
    have := congrArg (fun F : (Fin n → ℂ) →ₗ[ℂ] V => F (Pi.single i 1))
      (hsum ((LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ).smulRight v))
    simpa [Representation.linHom_apply, LinearMap.sum_apply] using this
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply]
  simp only [Representation.character, trace_pi_eq_sum, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero (fun i _ => key i)

end GlobalTheory.Shin
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.latticeCorrespondence_torsion_relation_properties : ∀ (K : Type) [Field K] [CharZero K] (ι : K →+* ℂ) (Λ₀ Λ₁ : PeriodPair) (T : K → K → Prop) (c₀ c₁ : ℂ) (τ₀ τ₁ : ℍ), IsTr ι Λ₀ Λ₁ T → IsTauOf Λ₀ c₀ τ₀ → IsTauOf Λ₁ c₁ τ₁ → ∀ (N : ℕ) [NeZero N] (R : (Fin 2 → ZMod N) → (Fin 2 → ZMod N) → Prop), (∀ x y, R x y ↔ ∃ k k' : K, ι k = c₀ * tors N τ₀ x ∧ ι k' = c₁ * tors N τ₁ y ∧ T k k') → (∀ x, ∃ y, R x y) ∧ (∀ x y x' y', R x y → R x' y' → R (x - x') (y - y')) ∧ (∀ x y, R x y → (x = 0 ↔ y = 0)) := by
  first | exact @GlobalTheory.RelTors.main | exact GlobalTheory.RelTors.main | (intros; apply GlobalTheory.RelTors.main <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma mem_tauPair_lattice_iff (τ : ℍ) (z : ℂ) :
    z ∈ (_root_.GlobalTheory.QFam.tauPair τ).lattice ↔ ∃ m n : ℤ, (m : ℂ) * τ + n = z := by
  rw [PeriodPair.mem_lattice]
  simp [_root_.GlobalTheory.QFam.tauPair]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma modularGroup_denom_eq (γ : SL(2, ℤ)) (τ : ℍ) :
    UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) ↑τ =
      ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) := by
  simp [UpperHalfPlane.denom]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma modularGroup_denom_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
  rw [← modularGroup_denom_eq]
  exact UpperHalfPlane.denom_ne_zero _ τ

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma coe_modularGroup_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ • τ : ℍ) : ℂ) = (((γ 0 0 : ℤ) : ℂ) * τ + ((γ 0 1 : ℤ) : ℂ)) /
      (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma exists_tors_vact_eq_denom_mul_tors_smul_add (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N)
    (γ : SL(2, ℤ)) (τ : ℍ) :
    ∃ l ∈ (_root_.GlobalTheory.QFam.tauPair τ).lattice,
      _root_.GlobalTheory.WpFam.tors N τ (_root_.GlobalTheory.WpFam.vact N x γ) =
        (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * _root_.GlobalTheory.WpFam.tors N (γ • τ) x + l := by
  have hv0 : _root_.GlobalTheory.WpFam.vact N x γ 0 =
      x 0 * ((γ 0 0 : ℤ) : ZMod N) + x 1 * ((γ 1 0 : ℤ) : ZMod N) := by
    simp [_root_.GlobalTheory.WpFam.vact, _root_.GlobalTheory.WpFam.vmul, _root_.GlobalTheory.WpFam.redGL, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two]
  have hv1 : _root_.GlobalTheory.WpFam.vact N x γ 1 =
      x 0 * ((γ 0 1 : ℤ) : ZMod N) + x 1 * ((γ 1 1 : ℤ) : ZMod N) := by
    simp [_root_.GlobalTheory.WpFam.vact, _root_.GlobalTheory.WpFam.vmul, _root_.GlobalTheory.WpFam.redGL, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two]
  set y := _root_.GlobalTheory.WpFam.vact N x γ
  have h0 : (N : ℤ) ∣ ((y 0).val : ℤ) - ((x 0).val * γ 0 0 + (x 1).val * γ 1 0) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp [hv0]
  have h1 : (N : ℤ) ∣ ((y 1).val : ℤ) - ((x 0).val * γ 0 1 + (x 1).val * γ 1 1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp [hv1]
  obtain ⟨k, hk⟩ := h0
  obtain ⟨k', hk'⟩ := h1
  refine ⟨(k : ℂ) * τ + k', (mem_tauPair_lattice_iff τ _).2 ⟨k, k', rfl⟩, ?_⟩
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hD := modularGroup_denom_ne_zero γ τ
  have e0 := congrArg (fun t : ℤ => (t : ℂ)) hk
  have e1 := congrArg (fun t : ℤ => (t : ℂ)) hk'
  push_cast at e0 e1
  have hw : (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * ((γ • τ : ℍ) : ℂ) =
      ((γ 0 0 : ℤ) : ℂ) * τ + ((γ 0 1 : ℤ) : ℂ) := by
    rw [coe_modularGroup_smul, mul_div_assoc', mul_div_cancel_left₀ _ hD]
  unfold _root_.GlobalTheory.WpFam.tors
  rw [mul_div_assoc', div_add' _ _ _ hN, div_left_inj' hN]
  linear_combination (τ : ℂ) * e0 + e1 - ((x 0).val : ℂ) * hw

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma isTauOf_tauPair_denom_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    _root_.ReciprocityTheory.ChartRestriction.L1.IsTauOf (_root_.GlobalTheory.QFam.tauPair τ) (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ))
      (γ • τ) := by
  have hD := modularGroup_denom_ne_zero γ τ
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.det_coe
    rwa [Matrix.det_fin_two] at h
  have key : ∀ u v : ℤ, (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) *
      ((u : ℂ) * ((γ • τ : ℍ) : ℂ) + v) =
      ((u * γ 0 0 + v * γ 1 0 : ℤ) : ℂ) * τ + ((u * γ 0 1 + v * γ 1 1 : ℤ) : ℂ) := by
    intro u v
    rw [coe_modularGroup_smul]
    field_simp
    push_cast
    ring
  unfold _root_.ReciprocityTheory.ChartRestriction.L1.IsTauOf
  refine ⟨hD, fun z => ?_⟩
  rw [mem_tauPair_lattice_iff]
  constructor
  · rintro ⟨m, n, rfl⟩
    refine ⟨m * γ 1 1 - n * γ 1 0, -(m * γ 0 1) + n * γ 0 0, ?_⟩
    have h1 : (m * γ 1 1 - n * γ 1 0) * γ 0 0 + (-(m * γ 0 1) + n * γ 0 0) * γ 1 0 = m := by
      linear_combination m * hdet
    have h2 : (m * γ 1 1 - n * γ 1 0) * γ 0 1 + (-(m * γ 0 1) + n * γ 0 0) * γ 1 1 = n := by
      linear_combination n * hdet
    rw [key, h1, h2]
  · rintro ⟨u, v, rfl⟩
    exact ⟨_, _, (key u v).symm⟩


open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.isFam_wp_wpd : ∀ (N : ℕ) [NeZero N],
    _root_.GlobalTheory.QFam.IsFam (_root_.GlobalTheory.WpFam.vact N) 2
        (_root_.GlobalTheory.WpFam.wp N) ∧
      _root_.GlobalTheory.QFam.IsFam (_root_.GlobalTheory.WpFam.vact N) 3
        (_root_.GlobalTheory.WpFam.wpd N) := by
  intro N _
  constructor
  · intro x γ
    funext τ
    obtain ⟨l, hl, hP⟩ := exists_tors_vact_eq_denom_mul_tors_smul_add N x γ τ
    have hom := _root_.GlobalTheory.WpFam.homogeneity_of_isTauOf _ _ _ (isTauOf_tauPair_denom_smul γ τ)
    have hper : (_root_.GlobalTheory.QFam.tauPair τ).weierstrassP
        ((((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * _root_.GlobalTheory.WpFam.tors N (γ • τ) x + l) =
        (_root_.GlobalTheory.QFam.tauPair τ).weierstrassP
        ((((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * _root_.GlobalTheory.WpFam.tors N (γ • τ) x) :=
      (_root_.GlobalTheory.QFam.tauPair τ).weierstrassP_add_coe _ ⟨l, hl⟩
    rw [ModularForm.SL_slash_apply, modularGroup_denom_eq]
    unfold _root_.GlobalTheory.WpFam.wp
    rw [hP, hper, hom.2.1, zpow_neg, zpow_ofNat]
    ring
  · intro x γ
    funext τ
    obtain ⟨l, hl, hP⟩ := exists_tors_vact_eq_denom_mul_tors_smul_add N x γ τ
    have hom := _root_.GlobalTheory.WpFam.homogeneity_of_isTauOf _ _ _ (isTauOf_tauPair_denom_smul γ τ)
    have hper : (_root_.GlobalTheory.QFam.tauPair τ).derivWeierstrassP
        ((((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * _root_.GlobalTheory.WpFam.tors N (γ • τ) x + l) =
        (_root_.GlobalTheory.QFam.tauPair τ).derivWeierstrassP
        ((((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * _root_.GlobalTheory.WpFam.tors N (γ • τ) x) :=
      (_root_.GlobalTheory.QFam.tauPair τ).derivWeierstrassP_add_coe _ ⟨l, hl⟩
    rw [ModularForm.SL_slash_apply, modularGroup_denom_eq]
    unfold _root_.GlobalTheory.WpFam.wpd
    rw [hP, hper, hom.2.2.1, zpow_neg, zpow_ofNat]
    ring

end GlobalTheory.WpFam
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem jdet_isFrameOn_kap : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → A.IsFrameOn A.kap U (jdet A z) := by
  intro n Y _ _ _ _ _ ι La _ A U z hz
  refine ⟨⟨fun i => ?_, fun i j y hy hi hj => ?_⟩, fun y hy => hz.det_ne _ y hy (A.mem_pick y)⟩
  · set S := (A.chart i).target ∩ (A.chart i).symm ⁻¹' U with hS
    have hSo : IsOpen S := (A.chart i).isOpen_inter_preimage_symm hz.isOpen
    have hk : ∀ k, ContDiffOn ℂ ∞ (fun v => (z ((A.chart i).symm v)) k) S := fun k =>
      contDiffOn_of_differentiableOn n _ S hSo (fun v hv =>
        (EuclideanSpace.proj k : V n →L[ℂ] ℂ).differentiableAt.comp_differentiableWithinAt v
          (hz.holo i v hv))
    have hpi := contDiffOn_pi.mpr hk
    have h1 : ContDiffOn ℂ ∞ (z ∘ (A.chart i).symm) S :=
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.contDiff.comp_contDiffOn hpi
    have h2 : ContDiffOn ℂ ∞ (fderiv ℂ (z ∘ (A.chart i).symm)) S :=
      h1.fderiv_of_isOpen hSo (by simp)
    have h3 : DifferentiableOn ℂ (fun v => (fderiv ℂ (z ∘ (A.chart i).symm) v).det) S := by
      intro v hv
      exact ((flL_det_contDiffAt ((h2 v hv).contDiffAt (hSo.mem_nhds hv))).differentiableAt
        (by simp)).differentiableWithinAt
    refine h3.congr fun v hv => ?_
    simp only [Function.comp_apply, jdet, jz, (A.chart i).right_inv hv.1]
  · have hyt : A.chart i y ∈ (A.chart i).target := (A.chart i).map_source hi
    have hov : IsOpen (ovl A.chart i j) :=
      (A.chart i).isOpen_inter_preimage_symm (A.chart j).open_source
    have hmov : A.chart i y ∈ ovl A.chart i j := ⟨hyt, by simp [(A.chart i).left_inv hi, hj]⟩
    have hτ : DifferentiableAt ℂ (A.chart j ∘ (A.chart i).symm) (A.chart i y) :=
      (A.holo_trans i j).differentiableAt (hov.mem_nhds hmov)
    have hτy : (A.chart j ∘ (A.chart i).symm) (A.chart i y) = A.chart j y := by
      simp [(A.chart i).left_inv hi]
    have hSo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
      (A.chart j).isOpen_inter_preimage_symm hz.isOpen
    have hmj : A.chart j y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U :=
      ⟨(A.chart j).map_source hj, by simp [(A.chart j).left_inv hj, hy]⟩
    have hzj : DifferentiableAt ℂ (z ∘ (A.chart j).symm) ((A.chart j ∘ (A.chart i).symm) (A.chart i y)) := by
      rw [hτy]; exact (hz.holo j).differentiableAt (hSo.mem_nhds hmj)
    have hev : z ∘ (A.chart i).symm =ᶠ[𝓝 (A.chart i y)]
        (z ∘ (A.chart j).symm) ∘ (A.chart j ∘ (A.chart i).symm) := by
      filter_upwards [hov.mem_nhds hmov] with v hv
      simp only [Function.comp_apply, (A.chart j).left_inv hv.2]
    have hjz : jz A z i y = (jz A z j y).comp (fderiv ℂ (A.chart j ∘ (A.chart i).symm) (A.chart i y)) := by
      unfold jz
      rw [hev.fderiv_eq, fderiv_comp _ hzj hτ, hτy]
    simp only [jdet]
    rw [hjz, A.g_kap i j y hi hj]
    exact (LinearMap.det_comp _ _).trans (mul_comm _ _)

end GlobalTheory.OTY
end
