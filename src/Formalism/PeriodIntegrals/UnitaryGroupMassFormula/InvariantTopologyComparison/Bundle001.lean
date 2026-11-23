module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.AdBridge
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

noncomputable section

namespace PI.InvTopW

open NumberField IsDedekindDomain Matrix Topology Filter
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge

variable (I : AutInst)

theorem exists_not_mem_range : ∃ x : I.E, x ∉ Set.range (algebraMap I.F I.E) := by
  by_contra h
  push_neg at h
  have hs : Function.Surjective (Algebra.linearMap I.F I.E) := fun x => by
    obtain ⟨a, ha⟩ := h x
    exact ⟨a, ha⟩
  have e := (LinearEquiv.ofBijective (Algebra.linearMap I.F I.E)
    ⟨(algebraMap I.F I.E).injective, hs⟩).finrank_eq
  rw [I.cm.deg2] at e
  rw [Module.finrank_self] at e
  omega

private theorem exists_nat_mul_lemma {E : Type} [Field E] [NumberField E] (x : E) :
    ∃ d : ℕ, 1 ≤ d ∧ (d : E) * x ∈ Formalism.UG.intOE E := by
  have H : ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ ((y : E) * x) := by
    have hq : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors ℤ) x hq
    exact ⟨m, nonZeroDivisors.coe_ne_zero m, by rw [← zsmul_eq_mul]; exact hm⟩
  obtain ⟨y, hy0, hint⟩ := H
  have hmem : (y : E) * x ∈ Formalism.UG.intOE E :=
    RingHom.mem_range.2 ((IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).1 hint)
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg y
  · refine ⟨n, Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hy0), ?_⟩
    simpa using hmem
  · refine ⟨n, Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hy0), ?_⟩
    simpa using hmem

theorem exists_beta : ∃ β : I.E, β ∈ Formalism.UG.intOE I.E ∧ β ∉ Set.range (algebraMap I.F I.E) := by
  obtain ⟨x, hx⟩ := exists_not_mem_range I
  obtain ⟨d, hd, hdx⟩ := exists_nat_mul_lemma x
  have hd0 : (d : I.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  refine ⟨(d : I.E) * x, hdx, fun ⟨a, ha⟩ => hx ⟨a / d, ?_⟩⟩
  rw [map_div₀, map_natCast, ha]
  exact mul_div_cancel_left₀ x hd0

def beta : I.E := (exists_beta I).choose

theorem beta_mem : beta I ∈ Formalism.UG.intOE I.E := (exists_beta I).choose_spec.1

theorem beta_not_mem : beta I ∉ Set.range (algebraMap I.F I.E) := (exists_beta I).choose_spec.2

theorem linearIndependent_one_beta : LinearIndependent I.F ![(1 : I.E), beta I] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    simp at hst
    exact ⟨hst, rfl⟩
  · exfalso
    apply beta_not_mem I
    refine ⟨-s / t, ?_⟩
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    have ht' : algebraMap I.F I.E t ≠ 0 := (map_ne_zero _).2 ht
    rw [map_div₀, map_neg, div_eq_iff ht']
    linear_combination -hst

def basisE : Module.Basis (Fin 2) I.F I.E :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_one_beta I)
    (by rw [Fintype.card_fin, I.cm.deg2])

theorem basisE_apply (k : Fin 2) : basisE I k = ![(1 : I.E), beta I] k := by
  simp [basisE]

theorem basisE_mem (k : Fin 2) : basisE I k ∈ Formalism.UG.intOE I.E := by
  rw [basisE_apply]
  fin_cases k
  · exact one_mem _
  · exact beta_mem I

end PI.InvTopW
end
end

section

noncomputable section

namespace PI.InvTopW

open NumberField IsDedekindDomain Matrix Topology Filter
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge

theorem tmul_mem_IntAf (I : AutInst) {x : I.E} (hx : x ∈ Formalism.UG.intOE I.E)
    {a : Formalism.MainNotions.S.Af I.F} (ha : a ∈ Formalism.UG.intAd I.F) :
    x ⊗ₜ[I.F] a ∈ Formalism.MainNotions.S.IntAf I.F I.E := by
  have h1 : x ⊗ₜ[I.F] (1 : Formalism.MainNotions.S.Af I.F) ∈ Formalism.MainNotions.S.IntAf I.F I.E := by
    refine Subring.subset_closure ?_
    exact Or.inl ⟨⟨x, hx⟩, rfl⟩
  have h2 : (1 : I.E) ⊗ₜ[I.F] a ∈ Formalism.MainNotions.S.IntAf I.F I.E := by
    refine Subring.subset_closure ?_
    exact Or.inr ⟨⟨a, ha⟩, rfl⟩
  have h3 := mul_mem h1 h2
  rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at h3

theorem tmul_natCast_mul (I : AutInst) (N : ℕ) (b : I.E) (z : Formalism.MainNotions.S.Af I.F) :
    b ⊗ₜ[I.F] ((N : Formalism.MainNotions.S.Af I.F) * z) = (N : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * (b ⊗ₜ[I.F] z) := by
  rw [← nsmul_eq_mul, ← nsmul_eq_mul, TensorProduct.tmul_smul]

end PI.InvTopW
end
end

section

noncomputable section

namespace PI.InvTopW

open NumberField IsDedekindDomain Matrix Topology Filter
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge

def KgMat (I : AutInst) (g : ℕ) (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) :
    Prop :=
  (∀ y, y ∈ I.Lf ↔ M *ᵥ y ∈ I.Lf) ∧
    ∀ y ∈ I.Lf, ∃ z ∈ I.Lf, (M - 1) *ᵥ y = (g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • z

def InNInt (I : AutInst) (N : ℕ) (x : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) : Prop :=
  ∃ z ∈ Formalism.MainNotions.S.IntAf I.F I.E, x = (N : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * z

def EntriesLat : Prop :=
  ∀ (I : AutInst) (g : ℕ), 1 ≤ g → ∃ N : ℕ, 1 ≤ N ∧
    ∀ M M' : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), M * M' = 1 →
      (∀ i j, InNInt I N ((M - 1) i j)) → (∀ i j, InNInt I N ((M' - 1) i j)) → KgMat I g M

def FinNhdA : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), 1 ≤ N →
    {a : FiniteAdeleRing (𝓞 F) F | ∃ z ∈ Formalism.UG.intAd F, a = (N : FiniteAdeleRing (𝓞 F) F) * z} ∈
      𝓝 (0 : FiniteAdeleRing (𝓞 F) F)

def FinNhdB : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], ∀ U ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F),
    ∃ N : ℕ, 1 ≤ N ∧ ∀ z ∈ Formalism.UG.intAd F, (N : FiniteAdeleRing (𝓞 F) F) * z ∈ U

end PI.InvTopW
end
end
