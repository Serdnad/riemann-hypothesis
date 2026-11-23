module

import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExistsSat
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExtensionHermitianFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittFreeTuplesSplitQuadraticEtale
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle017
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle014
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle018
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace GlobalTheory.ClearingDenominatorsInOrder

theorem main {E W : Type} [Field E] [NumberField E] [AddCommGroup W] [Module E W]
    [Module (NumberField.RingOfIntegers E) W]
    [IsScalarTower (NumberField.RingOfIntegers E) E W]
    (L : Submodule (NumberField.RingOfIntegers E) W) :
    ∀ v ∈ Submodule.span E (↑L : Set W),
      ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ c • v ∈ L := by
  apply Formalism.L2.SG.Pf.LatEx.exists_smul_mem_of_mem_span <;> assumption

end GlobalTheory.ClearingDenominatorsInOrder
end

section

namespace GlobalTheory.ExistsSmulMemLattice

open NumberField

theorem exists_smul_mem {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
    {M : Submodule (RingOfIntegers K) V} {v : V} (hv : v ∈ Submodule.span K (M : Set V)) :
    ∃ d : RingOfIntegers K, d ≠ 0 ∧ d • v ∈ M := by
  apply Formalism.L2.SG.Pf.LatEx.exists_smul_mem_of_mem_span <;> assumption

end GlobalTheory.ExistsSmulMemLattice
end

section

open GlobalTheory.SgAlg Matrix

theorem _root_.GlobalTheory.T.isField_or_exists_swapped_idempotent_of_quadraticEtale : ∀ {E : Type} [CommRing E] (σ : E →+* E), IsQA σ → IsField E ∨ ∃ e : E, e * e = e ∧ e + σ e = 1 ∧ ∀ x : E, e * x ≠ 0 → ∃ y, e * x * y = e := by
  first | exact @GlobalTheory.SgAlg.isField_or_exists_idempotent_of_isQA | exact GlobalTheory.SgAlg.isField_or_exists_idempotent_of_isQA | (intros; apply GlobalTheory.SgAlg.isField_or_exists_idempotent_of_isQA <;> assumption)
end

section

open GlobalTheory.SgAlg Matrix

theorem _root_.GlobalTheory.T.witt_extension_hermitian_frames : ∀ {E : Type} [Field E] (σ : E →+* E), IsQA σ → ∀ {n a : ℕ} (J : Matrix (Fin n) (Fin n) E), IsHermU σ J → ∀ (X X' : Matrix (Fin n) (Fin a) E), Free X → Free X' → pairM σ J X X = pairM σ J X' X' → ∃ g, IsUn σ J g ∧ g * X = X' := by
  first | exact @GlobalTheory.SgAlg.witt_free_field | exact GlobalTheory.SgAlg.witt_free_field | (intros; apply GlobalTheory.SgAlg.witt_free_field <;> assumption)
end

section

open GlobalTheory.SgAlg Matrix

theorem _root_.GlobalTheory.T.witt_free_tuples_split_quadratic_etale : ∀ {E : Type} [CommRing E] (σ : E →+* E), IsQA σ → (∃ e : E, e * e = e ∧ e + σ e = 1 ∧ ∀ x : E, e * x ≠ 0 → ∃ y, e * x * y = e) → ∀ {n a : ℕ} (J : Matrix (Fin n) (Fin n) E), IsHermU σ J → ∀ (X X' : Matrix (Fin n) (Fin a) E), Free X → Free X' → pairM σ J X X = pairM σ J X' X' → ∃ g, IsUn σ J g ∧ g * X = X' := by
  first | exact @GlobalTheory.SgAlg.WittSplit.witt_split | exact GlobalTheory.SgAlg.WittSplit.witt_split | (intros; apply GlobalTheory.SgAlg.WittSplit.witt_split <;> assumption)
end

section

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc

namespace GlobalTheory.PowSmulMemLattice

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem exists_pow_mul_mem_O [IsNonarchimedeanLocalField F] (L : LocE F E)
    (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (c : E) :
    ∃ k : ℕ, algebraMap F E ((ϖ : F) ^ k) * c ∈ L.O := by
  haveI : IsFractionRing 𝒪[F] F := (Valuation.integer.integers (valuation F)).isFractionRing
  haveI : Module.Free F E := L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have hc : IsIntegral F c := Algebra.IsIntegral.isIntegral c
  obtain ⟨⟨m, hm⟩, hmc⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (nonZeroDivisors 𝒪[F]) c hc
  have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hm0 hϖ
  refine ⟨k, (L.O_def _).2 ?_⟩
  have h2 : IsIntegral 𝒪[F] ((u : 𝒪[F]) • (m • c)) := hmc.smul _
  convert h2 using 1
  have e1 : (ϖ : F) ^ k = ((ϖ ^ k : 𝒪[F]) : F) := by push_cast; rfl
  rw [e1, ← hu, smul_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply 𝒪[F] F E, mul_comm u.1 m]
  rfl

theorem exists_pow_smul_mem_of_isLat [IsNonarchimedeanLocalField F] (L : LocE F E)
    (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) {n : ℕ} (Λ : Submodule L.O (Fin n → E))
    (hΛ : GlobalTheory.HL.IsLat L Λ) (y : Fin n → E) :
    ∃ m : ℕ, (algebraMap F E : F → E) ((ϖ : F) ^ m) • y ∈ Λ := by
  have hpowO : ∀ j : ℕ, algebraMap F E ((ϖ : F) ^ j) ∈ L.O := by
    intro j
    refine (L.O_def _).2 ?_
    have : algebraMap F E ((ϖ : F) ^ j) = algebraMap 𝒪[F] E (ϖ ^ j) := by
      rw [IsScalarTower.algebraMap_apply 𝒪[F] F E]; push_cast; rfl
    rw [this]; exact isIntegral_algebraMap
  have hsm : ∀ j : ℕ, ∀ x ∈ Λ, algebraMap F E ((ϖ : F) ^ j) • x ∈ Λ := by
    intro j x hx
    exact Λ.smul_mem (⟨_, hpowO j⟩ : L.O) hx
  have hy : y ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hΛ.2]; trivial
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨i, hi⟩ := ha
    obtain ⟨j, hj⟩ := hb
    refine ⟨i + j, ?_⟩
    have e : algebraMap F E ((ϖ : F) ^ (i + j)) • (a + b) =
        algebraMap F E ((ϖ : F) ^ j) • (algebraMap F E ((ϖ : F) ^ i) • a) +
        algebraMap F E ((ϖ : F) ^ i) • (algebraMap F E ((ϖ : F) ^ j) • b) := by
      simp only [smul_add, smul_smul, ← map_mul, ← pow_add]
      rw [add_comm j i]
    rw [e]
    exact Λ.add_mem (hsm j _ hi) (hsm i _ hj)
  | smul c x _ hx =>
    obtain ⟨i, hi⟩ := hx
    obtain ⟨k, hk⟩ := exists_pow_mul_mem_O L ϖ hϖ c
    refine ⟨k + i, ?_⟩
    have e : algebraMap F E ((ϖ : F) ^ (k + i)) • (c • x) =
        (algebraMap F E ((ϖ : F) ^ k) * c) • (algebraMap F E ((ϖ : F) ^ i) • x) := by
      simp only [smul_smul, pow_add, map_mul]
      ring_nf
    rw [e]
    exact Λ.smul_mem (⟨_, hk⟩ : L.O) hi

end GlobalTheory.PowSmulMemLattice

end
end

section

open ValuativeRel

namespace GlobalTheory.CommonDenominator

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem algebraMap_mem_O (L : Formalism.MainNotions.S.Loc.LocE F E) (t : 𝒪[F]) :
    algebraMap F E (t : F) ∈ L.O := by
  rw [L.O_def]
  have h : algebraMap F E (t : F) = algebraMap 𝒪[F] E t := by
    rw [IsScalarTower.algebraMap_apply 𝒪[F] F E]; rfl
  rw [h]
  exact isIntegral_algebraMap

theorem exists_den (L : Formalism.MainNotions.S.Loc.LocE F E) (c : E) :
    ∃ t : 𝒪[F], t ≠ 0 ∧ algebraMap F E (t : F) * c ∈ L.O := by
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ L.rank
  have hc : IsIntegral F c := Algebra.IsIntegral.isIntegral c
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (nonZeroDivisors 𝒪[F]) (Rₘ := F) c hc
  refine ⟨(m : 𝒪[F]), nonZeroDivisors.ne_zero m.2, ?_⟩
  rw [L.O_def]
  have h : m • c = algebraMap F E ((m : 𝒪[F]) : F) * c := by
    rw [Submonoid.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply 𝒪[F] F E]; rfl
  rw [← h]
  exact hm

theorem main (L : Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} [IsNonarchimedeanLocalField F]
    {Λ : Submodule (↥(Formalism.MainNotions.S.Loc.LocE.O L)) (Fin n → E)} (hΛ : GlobalTheory.HL.IsLat L Λ)
    (x : Fin n → E) :
    ∃ (t : ↥(Valuation.integer (ValuativeRel.valuation F))),
      t ≠ (0 : ↥(Valuation.integer (ValuativeRel.valuation F))) ∧
      (Algebra.algebraMap F E : F → E) (↑t : F) • x ∈ Λ := by
  have hx : x ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hΛ.2]; exact Submodule.mem_top
  have key : ∀ (a : E) (ha : a ∈ L.O) (v : Fin n → E), v ∈ Λ → a • v ∈ Λ := by
    intro a ha v hv
    have := Λ.smul_mem (⟨a, ha⟩ : L.O) hv
    exact this
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simpa using Λ.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨t1, h1, hy⟩ := hy
    obtain ⟨t2, h2, hz⟩ := hz
    refine ⟨t1 * t2, mul_ne_zero h1 h2, ?_⟩
    have e : (Algebra.algebraMap F E : F → E) ((t1 * t2 : 𝒪[F]) : F) • (y + z)
        = algebraMap F E (t2 : F) • (algebraMap F E (t1 : F) • y)
          + algebraMap F E (t1 : F) • (algebraMap F E (t2 : F) • z) := by
      simp only [Subring.coe_mul, map_mul, smul_add, smul_smul]
      rw [mul_comm (algebraMap F E (t2 : F)) (algebraMap F E (t1 : F))]
    rw [e]
    exact Λ.add_mem (key _ (algebraMap_mem_O L t2) _ hy) (key _ (algebraMap_mem_O L t1) _ hz)
  | smul c y _ hy =>
    obtain ⟨t, ht, hy⟩ := hy
    obtain ⟨s, hs, hsc⟩ := exists_den L c
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    have e : (Algebra.algebraMap F E : F → E) ((s * t : 𝒪[F]) : F) • (c • y)
        = (algebraMap F E (s : F) * c) • (algebraMap F E (t : F) • y) := by
      simp only [Subring.coe_mul, map_mul, smul_smul]
      rw [mul_right_comm]
    rw [e]
    exact key _ hsc _ hy

end GlobalTheory.CommonDenominator
end

section

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc

namespace GlobalTheory.PowMulMemOrder

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem exists_pow_mul_mem (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (c : E) :
    ∃ k : ℕ, algebraMap F E ((ϖ : F) ^ k) * c ∈ L.O := by
  haveI : Module.Free F E := L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have hc : IsIntegral F c := Algebra.IsIntegral.isIntegral c
  obtain ⟨⟨m, hm0⟩, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (nonZeroDivisors 𝒪[F]) c hc
  have hmne : m ≠ 0 := nonZeroDivisors.ne_zero hm0
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hmne hϖ
  obtain ⟨u, hu⟩ := hk
  refine ⟨k, (L.O_def _).2 ?_⟩
  have h2 : IsIntegral 𝒪[F] ((u : 𝒪[F]) • ((⟨m, hm0⟩ : nonZeroDivisors 𝒪[F]) • c)) := hm.smul _
  convert h2 using 1
  simp only [Submonoid.smul_def, smul_smul, ← hu]
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply 𝒪[F] F E]
  rw [mul_comm (u : 𝒪[F]) m, hu]
  rfl

theorem main : ∀ {F : Type} [inst : Field F] [inst_1 : ValuativeRel F] [inst_2 : TopologicalSpace F] [IsNonarchimedeanLocalField F] {E : Type} [inst_4 : CommRing E] [inst_5 : Algebra F E] [inst_6 : TopologicalSpace E] (L : Formalism.MainNotions.S.Loc.LocE F E) {ϖ : ↥(Valuation.integer (ValuativeRel.valuation F))}, Irreducible ϖ → ∀ (p : ↥(Formalism.MainNotions.S.Loc.LocE.O L)), (↑p : E) = (Algebra.algebraMap F E : F → E) (↑ϖ : F) → ∀ {n : ℕ} {Λ : Submodule (↥(Formalism.MainNotions.S.Loc.LocE.O L)) (Fin n → E)}, GlobalTheory.HL.IsLat L Λ → ∀ (v : Fin n → E), ∃ (j : ℕ), p ^ j • v ∈ Λ := by
  intro F _ _ _ _ E _ _ _ L ϖ hϖ p hp n Λ hΛ v
  have key : ∀ c : E, ∃ k : ℕ, ((p ^ k : L.O) : E) * c ∈ L.O := by
    intro c
    obtain ⟨k, hk⟩ := exists_pow_mul_mem L hϖ c
    refine ⟨k, ?_⟩
    have : ((p ^ k : L.O) : E) = algebraMap F E ((ϖ : F) ^ k) := by
      rw [SubmonoidClass.coe_pow, hp, map_pow]
    rw [this]; exact hk
  have mono : ∀ (x : Fin n → E) (i j : ℕ), p ^ j • x ∈ Λ → p ^ (i + j) • x ∈ Λ := by
    intro x i j h
    rw [pow_add, mul_smul]
    exact Λ.smul_mem _ h
  have hv : v ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hΛ.2]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ (mono y a b hb)
    rw [add_comm]; exact mono x b a ha
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨k, hk⟩ := key c
    refine ⟨k + a, ?_⟩
    have e1 : p ^ (k + a) • (c • x) = (⟨((p ^ k : L.O) : E) * c, hk⟩ : L.O) • (p ^ a • x) := by
      simp only [Subring.smul_def, smul_smul, pow_add, Subring.coe_mul]
      congr 1
      ring
    rw [e1]
    exact Λ.smul_mem _ ha

end GlobalTheory.PowMulMemOrder
end
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Eichler

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem hf_add_l (a b y : Fin n → E) : hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_sub_l (a b y : Fin n → E) : hf L Hm (a - b) y = hf L Hm a y - hf L Hm b y := by
  simp [hf, sub_mul, Finset.sum_sub_distrib]

theorem hf_smul_l (c : E) (a y : Fin n → E) : hf L Hm (c • a) y = c * hf L Hm a y := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_add_r (a b y : Fin n → E) : hf L Hm y (a + b) = hf L Hm y a + hf L Hm y b := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_sub_r (a b y : Fin n → E) : hf L Hm y (a - b) = hf L Hm y a - hf L Hm y b := by
  simp [hf, mul_sub, Finset.sum_sub_distrib]

theorem hf_neg_r (a y : Fin n → E) : hf L Hm y (-a) = - hf L Hm y a := by
  simp [hf, Finset.sum_neg_distrib]

theorem hf_neg_l (a y : Fin n → E) : hf L Hm (-a) y = - hf L Hm a y := by
  simp [hf, Finset.sum_neg_distrib]

theorem hf_smul_r (c : E) (a y : Fin n → E) : hf L Hm y (c • a) = L.cj c * hf L Hm y a := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_cj {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm) (x y : Fin n → E) :
    L.cj (hf L Hm x y) = hf L Hm y x := by
  have h' : ∀ i j, L.cj (Hm j i) = Hm i j := fun i j => congrFun (congrFun h i) j

  simp only [hf, map_sum, map_mul, L.cj_cj, h']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

def eichL (x u : Fin n → E) (s : E) : (Fin n → E) →ₗ[E] (Fin n → E) where
  toFun := eich L Hm x u s
  map_add' a b := by
    simp only [eich, hf_add_l]; module
  map_smul' c a := by
    simp only [eich, hf_smul_l, RingHom.id_apply]; module

theorem eich_inv {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm) (x u : Fin n → E) (s : E)
    (hx : hf L Hm x x = 0) (hu : hf L Hm u x = 0) (hs : s + L.cj s = hf L Hm u u) (v : Fin n → E) :
    eich L Hm x (-u) (L.cj s) (eich L Hm x u s v) = v := by
  have hu' : hf L Hm x u = 0 := by rw [← hf_cj L h, hu, map_zero]
  simp only [eich, hf_add_l, hf_sub_l, hf_smul_l, hf_neg_r, hx, hu, hu', ← hs]
  module

theorem eich_isom {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm) (x u : Fin n → E) (s : E)
    (hx : hf L Hm x x = 0) (hu : hf L Hm u x = 0) (hs : s + L.cj s = hf L Hm u u) (v w : Fin n → E) :
    hf L Hm (eich L Hm x u s v) (eich L Hm x u s w) = hf L Hm v w := by
  have hu' : hf L Hm x u = 0 := by rw [← hf_cj L h, hu, map_zero]
  simp only [eich, hf_add_l, hf_sub_l, hf_smul_l, hf_add_r, hf_sub_r, hf_smul_r, hx, hu, hu', ← hs,
    hf_cj L h]
  ring

end

theorem eichler_isometry : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ (x u : Fin n → E) (s : E), hf L Hm x x = 0 → hf L Hm u x = 0 → s + L.cj s = hf L Hm u u → ∃ g ∈ isomG L Hm, (∀ v, g v = eich L Hm x u s v) ∧ ∀ v, g⁻¹ v = eich L Hm x (-u) (L.cj s) v := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hH x u s hx hu hs
  have h1 := eich_inv L hH.1 x u s hx hu hs
  have h2 := eich_inv L hH.1 x (-u) (L.cj s) hx (by rw [hf_neg_l, hu, neg_zero])
    (by rw [L.cj_cj, hf_neg_l, hf_neg_r, neg_neg, add_comm, hs])
  simp only [neg_neg, L.cj_cj] at h2
  refine ⟨{ eichL L Hm x u s with
      invFun := eich L Hm x (-u) (L.cj s)
      left_inv := h1
      right_inv := h2 }, ?_, fun _ => rfl, fun _ => rfl⟩
  exact fun v w => eich_isom L hH.1 x u s hx hu hs v w

end GlobalTheory.HL.Eichler
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL


open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.invVol_eq_div_of_le {G : Type*} [Group G] {D A B : Subgroup G}
    (hA : D ≤ A) (hB : D ≤ B) (h : D.relIndex A ≠ 0) :
    _root_.GlobalTheory.HL.invVol A B = (D.relIndex A : ℝ) / (D.relIndex B : ℝ) := by
  unfold _root_.GlobalTheory.HL.invVol
  have hDC : D ≤ A ⊓ B := le_inf hA hB
  have eA := Subgroup.relIndex_mul_relIndex D (A ⊓ B) A hDC inf_le_left
  have eB := Subgroup.relIndex_mul_relIndex D (A ⊓ B) B hDC inf_le_right
  rw [Subgroup.inf_relIndex_left] at eA
  rw [Subgroup.inf_relIndex_right] at eB
  have ha : D.relIndex (A ⊓ B) ≠ 0 := by
    intro h0
    apply h
    rw [← eA, h0, zero_mul]
  rw [← eA, ← eB, Nat.cast_mul, Nat.cast_mul,
    mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr ha)]


open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.invVol_mul_pos_le_conj : ∀ {G : Type} [Group G] (K0 K1 K : Subgroup G),
    K0.relIndex K1 ≠ 0 → K1.relIndex K0 ≠ 0 → K0.relIndex K ≠ 0 → K.relIndex K0 ≠ 0 →
    _root_.GlobalTheory.HL.invVol K0 K = _root_.GlobalTheory.HL.invVol K0 K1 * _root_.GlobalTheory.HL.invVol K1 K ∧
    0 < _root_.GlobalTheory.HL.invVol K0 K ∧
    (K ≤ K1 → _root_.GlobalTheory.HL.invVol K0 K =
      _root_.GlobalTheory.HL.invVol K0 K1 * (K.relIndex K1 : ℝ)) ∧
    ∀ g : G, _root_.GlobalTheory.HL.invVol (MulAut.conj g • K0) (MulAut.conj g • K) =
      _root_.GlobalTheory.HL.invVol K0 K := by
  intro G _ K0 K1 K h01 h10 h0K hK0
  have hd0 : (K0 ⊓ K1 ⊓ K).relIndex K0 ≠ 0 :=
    Subgroup.relIndex_inf_ne_zero (Subgroup.relIndex_inf_ne_zero (by simp) h10) hK0
  have hd1 : (K0 ⊓ K1 ⊓ K).relIndex K1 ≠ 0 := Subgroup.relIndex_ne_zero_trans hd0 h01
  have hdK : (K0 ⊓ K1 ⊓ K).relIndex K ≠ 0 := Subgroup.relIndex_ne_zero_trans hd0 h0K
  have l0 : K0 ⊓ K1 ⊓ K ≤ K0 := inf_le_left.trans inf_le_left
  have l1 : K0 ⊓ K1 ⊓ K ≤ K1 := inf_le_left.trans inf_le_right
  have lK : K0 ⊓ K1 ⊓ K ≤ K := inf_le_right
  have e0K := _root_.GlobalTheory.HL.invVol_eq_div_of_le l0 lK hd0
  have e01 := _root_.GlobalTheory.HL.invVol_eq_div_of_le l0 l1 hd0
  have e1K := _root_.GlobalTheory.HL.invVol_eq_div_of_le l1 lK hd1
  have hmul : _root_.GlobalTheory.HL.invVol K0 K =
      _root_.GlobalTheory.HL.invVol K0 K1 * _root_.GlobalTheory.HL.invVol K1 K := by
    rw [e0K, e01, e1K, div_mul_div_cancel₀ (Nat.cast_ne_zero.mpr hd1)]
  refine ⟨hmul, ?_, ?_, ?_⟩
  · rw [e0K]
    exact div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd0))
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hdK))
  · intro hle
    have h1 : K1.relIndex K = 1 := Subgroup.relIndex_eq_one.mpr hle
    rw [hmul]
    congr 1
    unfold _root_.GlobalTheory.HL.invVol
    rw [h1, Nat.cast_one, div_one]
  · intro g
    have hc : ∀ L : Subgroup G, MulAut.conj g • L = ConjAct.toConjAct g • L := fun L => rfl
    unfold _root_.GlobalTheory.HL.invVol
    rw [hc, hc, Subgroup.relIndex_pointwise_smul, Subgroup.relIndex_pointwise_smul]

end GlobalTheory.HL
end

section

open GlobalTheory.IdxInt
open scoped Pointwise Classical

theorem _root_.GlobalTheory.T.indexMeasureIntegral_transport_and_change : ∀ {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'], (∀ (e : W ≃+ W') (A : AddSubgroup W) (φ : W' → ℂ), (Nice (A.map e.toAddMonoidHom) φ ↔ Nice A (fun w => φ (e w))) ∧ cint (A.map e.toAddMonoidHom) φ = cint A (fun w => φ (e w))) ∧ ∀ (A A' : AddSubgroup W) (φ : W → ℂ), A.relIndex A' ≠ 0 → A'.relIndex A ≠ 0 → (Nice A φ ↔ Nice A' φ) ∧ cint A' φ * (A.relIndex A' : ℂ) = cint A φ * (A'.relIndex A : ℂ) := by
  first | exact @GlobalTheory.IdxInt.Transport.cint_map_and_change | exact GlobalTheory.IdxInt.Transport.cint_map_and_change | (intros; apply GlobalTheory.IdxInt.Transport.cint_map_and_change <;> assumption)
end

section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.measure_ball_eq_lintegral_upperMeasureDensity : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (l ν : Measure V) [l.IsAddHaarMeasure] [IsFiniteMeasure ν] (η : ℝ) (C : ℝ≥0), (∀ x : V, ‖x‖ < η → GlobalTheory.HaarDensChart.upperDens l ν x < C) → ∀ ρ : ℝ, ρ ≤ η → ν (Metric.ball 0 ρ) = ∫⁻ x in Metric.ball 0 ρ, GlobalTheory.HaarDensChart.upperDens l ν x ∂l := by
  first | exact @GlobalTheory.measure_ball_eq_lintegral_upperDens | exact GlobalTheory.measure_ball_eq_lintegral_upperDens | (intros; apply GlobalTheory.measure_ball_eq_lintegral_upperDens <;> assumption)
end
