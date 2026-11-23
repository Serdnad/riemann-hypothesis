module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle639
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Trace.Basic

@[expose] public section

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma omB_smul_mem {K : Type} [Field K] [Algebra ℂ K] (B : Subalgebra ℂ K) (q : ℕ) {b : K} (hb : b ∈ B)
    {y : DR ℂ K} (hy : y ∈ omB ℂ K B q) : b • y ∈ omB ℂ K B q := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b', hb', v, hv, rfl⟩ := hz
    apply Submodule.subset_span
    exact ⟨b * b', B.mul_mem hb hb', v, hv, by rw [smul_smul]⟩
  | zero => simp
  | add u w _ _ hu hw =>
    rw [smul_add]
    exact Submodule.add_mem _ hu hw
  | smul c u _ hu =>
    rw [smul_comm]
    exact Submodule.smul_mem _ c hu

private lemma ratio_mem_rB {F : Type} (K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K]
    [IsScalarTower ℂ F K] {d : ℕ} (x : Fin (d + 1) → F) (i j : Fin (d + 1)) :
    algebraMap F K (x j / x i) ∈ rB ℂ K x {i} := by
  rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
  have h : x j / x i ∈ rA ℂ x {i} := Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, j, rfl⟩
  exact isIntegral_algebraMap (x := (⟨x j / x i, h⟩ : rA ℂ x {i}))

private lemma omG_ratio {F : Type} [Field F] {d : ℕ} (x : Fin (d + 1) → Fˣ) (i j : Fin (d + 1)) (N : ℕ) :
    ((x j : F) / x i) ^ (N + d + 1) * ((x i : F) / x j) ^ N * omG x j = omG x i := by
  have hi : (x i : F) ≠ 0 := (x i).ne_zero
  have hj : (x j : F) ≠ 0 := (x j).ne_zero
  have h : omG x j = omG x i * ((x i : F) / x j) ^ (d + 1) := by
    simp only [omG]
    rw [show ((x i : F) / x j) ^ (d + 1) = ∏ _l : Fin (d + 1), ((x i : F) / x j) by simp [div_pow],
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    field_simp
  rw [h, ← inv_div (x j : F) (x i : F)]
  have ha : (x j : F) / x i ≠ 0 := div_ne_zero hj hi
  generalize (x j : F) / x i = a at ha ⊢
  rw [inv_pow, inv_pow]
  field_simp
  ring

private lemma pair_prod {F : Type} [Field F] {d : ℕ} (x : Fin (d + 1) → Fˣ) (i j : Fin (d + 1)) :
    (∏ l ∈ ({i, j} : Finset (Fin (d + 1))), (x l : F) / x i) = (x j : F) / x i := by
  by_cases h : i = j
  · subst h
    simp
  · rw [Finset.prod_pair h, div_self (x i).ne_zero, one_mul]

private theorem key_lemma' {K : Type} [Field K] [Algebra ℂ K] (s t : K) (y z : DR ℂ K) :
    actZ K (s ⊗ₜ[ℂ] t) (y ⊗ₜ[ℂ] z) = (s • y) ⊗ₜ[ℂ] (t • z) := by
  simp [actZ, Module.endTensorEndAlgHom, Module.endTensorEndAlgHom_apply]

private lemma key {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K]
    {d : ℕ} (x : Fin (d + 1) → Fˣ) (hc : IsFinCover ℂ K (xv x))
    (hmono : ∀ (q : ℕ) (s t : Finset (Fin (d + 1))), s.Nonempty → s ⊆ t →
      omB ℂ K (rB ℂ K (xv x) s) q ≤ omB ℂ K (rB ℂ K (xv x) t) q) (a : ℕ) (i j : Fin (d + 1))
    (m : DR ℂ K ⊗[ℂ] DR ℂ K) (hm : m ∈ MZ F K (xv x) a {j} {j}) :
    ∃ N0 : ℕ, ∀ N, N0 ≤ N → actZ K ((algebraMap F K ((x j : F) / x i) ^ (N + d + 1)) ⊗ₜ[ℂ]
      (algebraMap F K ((x i : F) / x j) ^ N)) m ∈ MZ F K (xv x) a {i} {j} := by
  have hu : algebraMap F K ((x j : F) / x i) ∈ rB ℂ K (xv x) {i} := ratio_mem_rB K (xv x) i j
  have hv : algebraMap F K ((x i : F) / x j) ∈ rB ℂ K (xv x) {j} := ratio_mem_rB K (xv x) j i
  have gen : ∀ y ∈ omB ℂ K (rB ℂ K (xv x) {j}) (d - a), ∀ z ∈ omB ℂ K (rB ℂ K (xv x) {j}) a,
      ∃ N0 : ℕ, ∀ N, N0 ≤ N → actZ K ((algebraMap F K ((x j : F) / x i) ^ (N + d + 1)) ⊗ₜ[ℂ]
        (algebraMap F K ((x i : F) / x j) ^ N)) (TensorProduct.mk ℂ (DR ℂ K) (DR ℂ K) y z) ∈
          MZ F K (xv x) a {i} {j} := by
    intro y hy z hz
    have hy' : y ∈ omB ℂ K (rB ℂ K (xv x) {i, j}) (d - a) :=
      hmono (d - a) {j} {i, j} (Finset.singleton_nonempty j)
        (Finset.singleton_subset_iff.mpr (by simp)) hy
    obtain ⟨N1, hN1⟩ := (GlobalTheory.T.kahlerFormsOverSubalgebra_standardOpen_iff_pow_smul ℂ F K d (xv x) hc {i, j} i (by simp) (d - a) y).mp hy'
    have hN1' : algebraMap F K ((x j : F) / x i) ^ N1 • y ∈ omB ℂ K (rB ℂ K (xv x) {i}) (d - a) := by
      rw [← pair_prod x i j]
      exact hN1
    refine ⟨N1, fun N hN => ?_⟩
    rw [TensorProduct.mk_apply, key_lemma']
    have h1 : algebraMap F K ((x j : F) / x i) ^ (N + d + 1) • y ∈
        omB ℂ K (rB ℂ K (xv x) {i}) (d - a) := by
      have e : N + d + 1 = (N + d + 1 - N1) + N1 := by omega
      rw [e, pow_add, ← smul_smul]
      exact _root_.omB_smul_mem _ _ (pow_mem hu _) hN1'
    have h2 : algebraMap F K ((x i : F) / x j) ^ N • z ∈ omB ℂ K (rB ℂ K (xv x) {j}) a :=
      _root_.omB_smul_mem _ _ (pow_mem hv _) hz
    exact Submodule.apply_mem_map₂ _ h1 h2
  unfold MZ at hm
  rw [Submodule.map₂_eq_span_image2] at hm
  induction hm using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨y, hy, z, hz, rfl⟩ := hw
    exact gen y hy z hz
  | zero => exact ⟨0, fun N _ => by simp⟩
  | add w w' _ _ h1 h2 =>
    obtain ⟨N1, h1⟩ := h1
    obtain ⟨N2, h2⟩ := h2
    exact ⟨max N1 N2, fun N hN => by
      rw [map_add (f := _)]
      exact Submodule.add_mem _ (h1 N (le_of_max_le_left hN)) (h2 N (le_of_max_le_right hN))⟩
  | smul c w _ h =>
    obtain ⟨N1, h⟩ := h
    exact ⟨N1, fun N hN => by
      rw [map_smul]
      exact Submodule.smul_mem _ c (h N hN)⟩

theorem UpperTheory.Gal.productCup_of_system.idIJ_of :
    IdJ → ActsLin → GoodZ → IdIJ := by
  intro hJ hL hG F K _ _ _ _ _ _ d x hc τ hτ a ha i j
  obtain ⟨m, hm, hact⟩ := hJ F K d x hc τ hτ a ha j
  have hmono : ∀ (q : ℕ) (s t : Finset (Fin (d + 1))), s.Nonempty → s ⊆ t →
      omB ℂ K (rB ℂ K (xv x) s) q ≤ omB ℂ K (rB ℂ K (xv x) t) q :=
    fun q => (hG F K d x hc q).2.2
  obtain ⟨N0, hN0⟩ := key x hc hmono a i j m hm
  refine ⟨_, hN0 N0 le_rfl, ?_⟩
  have h2 := (hL F K d x hc τ hτ a).2.1 m _
    ((algebraMap F K ((x j : F) / x i) ^ (N0 + d + 1)) ⊗ₜ[ℂ] (algebraMap F K ((x i : F) / x j) ^ N0)) hact
  rw [Algebra.TensorProduct.lmul'_apply_tmul, ← map_pow, ← map_pow, ← map_mul, ← map_mul,
    omG_ratio] at h2
  simpa only [map_pow] using h2
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K']
  [IsScalarTower ℂ F K'] {d : ℕ}

private theorem tower_rA (y : Fin (d + 1) → F) : IsScalarTower (rA ℂ y {0}) K K' :=
  .of_algebraMap_eq fun r => IsScalarTower.algebraMap_apply F K K' (r : F)

private theorem map_mem_rB (y : Fin (d + 1) → F) {b : K} (hb : b ∈ rB ℂ K y {0}) :
    algebraMap K K' b ∈ rB ℂ K' y {0} := by
  rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff] at hb ⊢
  haveI := tower_rA (K := K) (K' := K') y
  exact hb.algebraMap

private theorem trace_mem_rB (y : Fin (d + 1) → F) [FiniteDimensional K K'] {v : K'}
    (hv : v ∈ rB ℂ K' y {0}) : Algebra.trace K K' v ∈ rB ℂ K y {0} := by
  rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff] at hv ⊢
  haveI := tower_rA (K := K) (K' := K') y
  exact Algebra.isIntegral_trace hv

end

theorem UpperTheory.Gal.productCup_of_system.redK_of :
    RedK := by
  intro F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY
  haveI : FiniteDimensional F K' := hY.covY.fin
  haveI : FiniteDimensional K K' := Module.Finite.of_restrictScalars_finite F K K'
  have hred := hY.red
  unfold RedFib at hred ⊢
  constructor
  intro z hz
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨n, hn⟩ := hz
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_range_iff_exists_fun] at hn
  obtain ⟨c, hc⟩ := hn
  rw [Ideal.Quotient.eq_zero_iff_mem]
  set t : Fin d → F := fun j => xv x j.succ / xv x 0 with ht
  have hcK : ∑ j, (c j : K) * algebraMap F K (t j) = (a : K) ^ n := by
    have := congrArg (fun u : rB ℂ K (xv x) {0} => (u : K)) hc
    simpa only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, SubmonoidClass.coe_pow] using this
  let b : rB ℂ K' (xv x) {0} := ⟨algebraMap K K' a, map_mem_rB (xv x) a.2⟩
  have hb : b ∈ Ideal.span (Set.range fun j : Fin d =>
      (⟨algebraMap F K' (t j), tco_mem ℂ K' (xv x) j⟩ : rB ℂ K' (xv x) {0})) := by
    have hq : IsNilpotent (Ideal.Quotient.mk (Ideal.span (Set.range fun j : Fin d =>
        (⟨algebraMap F K' (t j), tco_mem ℂ K' (xv x) j⟩ : rB ℂ K' (xv x) {0}))) b) := by
      refine ⟨n, ?_⟩
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_range_iff_exists_fun]
      refine ⟨fun j => ⟨algebraMap K K' (c j), map_mem_rB (xv x) (c j).2⟩, ?_⟩
      apply Subtype.ext
      simp only [b, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, SubmonoidClass.coe_pow]

      rw [← map_pow, ← hcK, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, ← IsScalarTower.algebraMap_apply]
    exact (Ideal.Quotient.eq_zero_iff_mem).1 (hred.eq_zero _ hq)
  rw [Ideal.mem_span_range_iff_exists_fun] at hb
  obtain ⟨e, he⟩ := hb
  have key : (Module.finrank K K' : K) * (a : K) =
      ∑ j, Algebra.trace K K' (e j : K') * algebraMap F K (t j) := by
    have h1 := congrArg (fun u : rB ℂ K' (xv x) {0} => Algebra.trace K K' (u : K')) he

    simp only [b, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, map_sum,
    Algebra.trace_algebraMap, nsmul_eq_mul] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [IsScalarTower.algebraMap_apply F K K', mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul,
      mul_comm]
  have hmem : ((Module.finrank K K' : rB ℂ K (xv x) {0}) * a) ∈ Ideal.span (Set.range fun j : Fin d =>
      (⟨algebraMap F K (t j), tco_mem ℂ K (xv x) j⟩ : rB ℂ K (xv x) {0})) := by
    rw [Ideal.mem_span_range_iff_exists_fun]
    refine ⟨fun j => ⟨Algebra.trace K K' (e j : K'), trace_mem_rB (xv x) (e j).2⟩, ?_⟩
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, SubringClass.coe_natCast]
    exact key.symm
  have hpos : (Module.finrank K K' : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := K) (M := K')).ne'
  have hA : a = algebraMap ℂ (rB ℂ K (xv x) {0}) ((Module.finrank K K' : ℂ)⁻¹) *
      ((Module.finrank K K' : rB ℂ K (xv x) {0}) * a) := by
    rw [← mul_assoc, ← map_natCast (algebraMap ℂ (rB ℂ K (xv x) {0})), ← map_mul,
      inv_mul_cancel₀ hpos, map_one, one_mul]
  rw [hA]
  exact Ideal.mul_mem_left _ _ hmem
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

section IntegralMvPolynomialLemmas
variable {L V σ : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L)
  [AddCommGroup V] [Module L V] [Module ℂ V] [IsScalarTower ℂ L V]

variable [LinearOrder σ]

end IntegralMvPolynomialLemmas

end UpperTheory.Gal.productCup_of_system

private theorem lG_of_lemma {L : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L)
    [Algebra.FiniteType ℂ B] (I : Ideal B) (hI : I ≠ ⊤) :
    ∃ e : B →ₐ[ℂ] ℂ, ∀ b ∈ I, e b = 0 := by
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  letI := Ideal.Quotient.field M
  haveI : Module.Finite ℂ (B ⧸ M) := finite_of_finite_type_of_isJacobsonRing ℂ (B ⧸ M)
  haveI : Algebra.IsIntegral ℂ (B ⧸ M) := Algebra.IsIntegral.of_finite ℂ _
  have hbij : Function.Bijective (algebraMap ℂ (B ⧸ M)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let φ := AlgEquiv.ofBijective (Algebra.ofId ℂ (B ⧸ M)) hbij
  refine ⟨φ.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ M), fun b hb => ?_⟩
  have h0 : Ideal.Quotient.mk M b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hIM hb)
  simp [h0]

private theorem lG_of_lemma_2 {L W : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L)
    [AddCommGroup W] [Module L W] [Module ℂ W] [IsScalarTower ℂ L W] (N : Submodule ℂ W)
    (hN : ∀ b : B, ∀ v ∈ N, (b : L) • v ∈ N) (e : B →ₐ[ℂ] ℂ) :
    ∃ S : Submodule ℂ W, (∀ x ∈ S, ∃ b : B, e b ≠ 0 ∧ (b : L) • x ∈ N) ∧
      ∀ x, (∃ b : B, e b ≠ 0 ∧ (b : L) • x ∈ N) → x ∈ S := by
  refine ⟨{ carrier := {x | ∃ b : B, e b ≠ 0 ∧ (b : L) • x ∈ N}
            add_mem' := ?_
            zero_mem' := ⟨1, by simp, by simp⟩
            smul_mem' := ?_ }, fun x hx => hx, fun x hx => hx⟩
  · rintro x y ⟨b1, h1, hx⟩ ⟨b2, h2, hy⟩
    refine ⟨b1 * b2, by simp [h1, h2], ?_⟩
    rw [smul_add]
    apply N.add_mem
    · rw [Subalgebra.coe_mul, mul_comm (b1 : L), mul_smul]
      exact hN b2 _ hx
    · rw [Subalgebra.coe_mul, mul_smul]
      exact hN b1 _ hy
  · rintro c x ⟨b, hb, hx⟩
    exact ⟨b, hb, by rw [smul_comm]; exact N.smul_mem c hx⟩

private theorem lG_of_lemma_3 {L W : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L)
    [Algebra.FiniteType ℂ B] [AddCommGroup W] [Module L W] [Module ℂ W] [IsScalarTower ℂ L W]
    (N : Submodule ℂ W) (hN : ∀ b : B, ∀ v ∈ N, (b : L) • v ∈ N) (x : W)
    (hx : ∀ e : B →ₐ[ℂ] ℂ, ∃ b : B, e b ≠ 0 ∧ (b : L) • x ∈ N) : x ∈ N := by
  let I : Ideal B :=
    { carrier := {b | (b : L) • x ∈ N}
      add_mem' := fun {a c} ha hc => by
        simp only [Set.mem_setOf_eq, Subalgebra.coe_add, add_smul] at *
        exact N.add_mem ha hc
      zero_mem' := by simp
      smul_mem' := fun c {b} hb => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, Subalgebra.coe_mul, mul_smul] at *
        exact hN c _ hb }
  by_cases hI : I = ⊤
  · have h1 : (1 : B) ∈ I := by rw [hI]; exact Submodule.mem_top
    change ((1 : B) : L) • x ∈ N at h1
    simpa using h1
  · obtain ⟨e, he⟩ := lG_of_lemma B I hI
    obtain ⟨b, hb, hbx⟩ := hx e
    exact absurd (he b hbx) hb

theorem UpperTheory.Gal.productCup_of_system.lG_of :
    LG := by
  intro L _ _ B _ V σ _ _ _ _ _ _ A w hA
  have hAs : ∀ s, ∀ b : B, ∀ v ∈ A s, (b : L) • v ∈ A s := fun s b v hv => by
    simpa using hA s (b : L) b.2 v hv
  have hloc : ∀ (e : B →ₐ[ℂ] ℂ) (N : Submodule ℂ V), (∀ b : B, ∀ v ∈ N, (b : L) • v ∈ N) →
      ∀ v ∈ locM B e N, ∃ b : B, e b ≠ 0 ∧ (b : L) • v ∈ N := by
    intro e N hN v hv
    obtain ⟨S, hS1, hS2⟩ := lG_of_lemma_2 B N hN e
    have hle : locM B e N ≤ S := by
      unfold locM
      rw [Submodule.span_le]
      intro u hu
      exact hS2 u hu
    exact hS1 v (hle hv)
  constructor
  · intro n c hc
    have hwd : ∀ (b : L) (x : Finset σ → V),
        wd (fun i => Algebra.lsmul ℂ ℂ V (w i)) (b • x) =
          b • wd (fun i => Algebra.lsmul ℂ ℂ V (w i)) x := by
      intro b x
      funext t
      simp [wd, Finset.smul_sum, smul_comm b]
    have hC : ∀ (A' : Finset σ → Submodule ℂ V) (x : Finset σ → V),
        x ∈ (acx A' fun i => Algebra.lsmul ℂ ℂ V (w i)).C (n - 1) ↔
          ∀ s, x s ∈ (if (s.card : ℤ) = n - 1 then A' s else ⊥) := by
      intro A' x
      simp [acx, Submodule.mem_pi]
    have hB : ∀ (A' : Finset σ → Submodule ℂ V) (c : Finset σ → V),
        c ∈ (acx A' fun i => Algebra.lsmul ℂ ℂ V (w i)).B n ↔
          ∃ x ∈ (acx A' fun i => Algebra.lsmul ℂ ℂ V (w i)).C (n - 1),
            wd (fun i => Algebra.lsmul ℂ ℂ V (w i)) x = c := by
      intro A' c
      simp [Cx.B, acx]
    have hCstab : ∀ b : B, ∀ x ∈ (acx A fun i => Algebra.lsmul ℂ ℂ V (w i)).C (n - 1),
        (b : L) • x ∈ (acx A fun i => Algebra.lsmul ℂ ℂ V (w i)).C (n - 1) := by
      intro b x hx
      rw [hC] at hx ⊢
      intro s
      have hxs := hx s
      simp only [Pi.smul_apply]
      split_ifs at hxs ⊢ with h
      · exact hAs s b _ hxs
      · rw [Submodule.mem_bot] at hxs ⊢
        simp [hxs]
    have hNstab : ∀ b : B, ∀ c ∈ (acx A fun i => Algebra.lsmul ℂ ℂ V (w i)).B n,
        (b : L) • c ∈ (acx A fun i => Algebra.lsmul ℂ ℂ V (w i)).B n := by
      intro b c hc
      rw [hB] at hc ⊢
      obtain ⟨x, hx, rfl⟩ := hc
      exact ⟨_, hCstab b x hx, hwd _ _⟩
    refine lG_of_lemma_3 B _ hNstab c fun e => ?_
    obtain ⟨x, hx, rfl⟩ := (hB _ _).1 (hc e)
    obtain ⟨S, hS1, hS2⟩ := lG_of_lemma_2 B _ hCstab e
    have hxS : x ∈ S := by
      rw [← Finset.univ_sum_single x]
      refine S.sum_mem fun s _ => ?_
      have hxs := (hC _ x).1 hx s
      split_ifs at hxs with h
      · obtain ⟨b, hb, hbv⟩ := hloc e (A s) (hAs s) _ hxs
        apply hS2
        refine ⟨b, hb, ?_⟩
        rw [hC]
        intro t
        by_cases hts : t = s
        · subst hts
          simpa [h] using hbv
        · simp [hts]
      · rw [Submodule.mem_bot] at hxs
        rw [hxs, Pi.single_zero]
        exact S.zero_mem
    obtain ⟨b, hb, hbx⟩ := hS1 x hxS
    exact ⟨b, hb, (hB _ _).2 ⟨_, hbx, hwd _ _⟩⟩
  · intro m hm
    have hmem : ∀ r ∈ Set.range w, ∀ u ∈ A ∅,
        r • u ∈ sm (Algebra.lsmul ℂ ℂ V) (A ∅) (Set.range w) := by
      intro r hr u hu
      unfold sm
      exact (le_iSup₂ (f := fun r (_ : r ∈ Set.range w) =>
        Submodule.map (Algebra.lsmul ℂ ℂ V r) (A ∅)) r hr) (Submodule.mem_map_of_mem hu)
    have hstab : ∀ b : B, ∀ v ∈ sm (Algebra.lsmul ℂ ℂ V) (A ∅) (Set.range w),
        (b : L) • v ∈ sm (Algebra.lsmul ℂ ℂ V) (A ∅) (Set.range w) := by
      intro b v hv
      have hle : sm (Algebra.lsmul ℂ ℂ V) (A ∅) (Set.range w) ≤
          (sm (Algebra.lsmul ℂ ℂ V) (A ∅) (Set.range w)).comap (Algebra.lsmul ℂ ℂ V (b : L)) := by
        conv_lhs => unfold sm
        refine iSup₂_le fun r hr => ?_
        rintro _ ⟨u, hu, rfl⟩
        rw [Submodule.mem_comap]
        simp only [Algebra.lsmul_coe]
        rw [smul_comm]
        exact hmem r hr _ (hAs ∅ b u hu)
      simpa using hle hv
    refine lG_of_lemma_3 B _ hstab m fun e => ?_
    obtain ⟨S, hS1, hS2⟩ := lG_of_lemma_2 B _ hstab e
    apply hS1
    have hle : sm (Algebra.lsmul ℂ ℂ V) (locM B e (A ∅)) (Set.range w) ≤ S := by
      conv_lhs => unfold sm
      refine iSup₂_le fun r hr => ?_
      rintro _ ⟨v, hv, rfl⟩
      obtain ⟨b, hb, hbv⟩ := hloc e (A ∅) (hAs ∅) v hv
      apply hS2
      refine ⟨b, hb, ?_⟩
      simp only [Algebra.lsmul_coe]
      rw [smul_comm]
      exact hmem r hr _ hbv
    exact hle (hm e)
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

theorem UpperTheory.Gal.productCup_of_system.fixZ_of :
    ValBasic → RYBasic → FixZ := by
  intro hV hR F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 Fx A h e he
  have hmem : ∀ b ∈ rB ℂ K (xv x) {0}, algebraMap K K' b ∈ rB ℂ K' (xv x) {0} :=
    fun b hb => ((hR F K K' d x j2 h.toY0).2.2.2.1 {0} b hb).1
  let ι : rB ℂ K (xv x) {0} →ₐ[ℂ] rB ℂ K' (xv x) {0} :=
    ((IsScalarTower.toAlgHom ℂ K K').comp (rB ℂ K (xv x) {0}).val).codRestrict _ fun b => hmem b b.2
  have hι : ∀ (b : K) (hb : b ∈ rB ℂ K (xv x) {0}), (e.1.comp ι) ⟨b, hb⟩ = e.1 ⟨_, hmem b hb⟩ :=
    fun _ _ => rfl
  refine ⟨⟨e.1.comp ι, fun j => ?_⟩, ?_⟩
  · rw [hι]
    refine Eq.trans ?_ (e.2 j)
    congr 2
    exact (IsScalarTower.algebraMap_apply F K K' _).symm
  rintro v c ⟨b, hb, hbv, hzb, hz⟩
  rw [hι] at hzb
  rw [hι, hι] at hz
  have h1b := hmem b hb
  have h1bv := hmem _ hbv
  constructor
  · have hm : algebraMap K K' b * algebraMap K K' v ∈ rB ℂ K' (xv x) {0} := by
      rw [← map_mul]; exact h1bv
    refine ⟨_, h1b, hm, hzb, ?_⟩
    rw [← hz]
    congr 2
    exact (map_mul _ _ _).symm
  · have fix := (h.fx e).1 he
    obtain ⟨-, ⟨ev, hev⟩, -, hinv⟩ := hV K' (rB ℂ K' (xv x) {0}) e.1
    have v1 := fix b hb h1b
    have v2 := fix _ hbv h1bv
    obtain ⟨m1, hm1⟩ := (hev _ _).1 v1
    obtain ⟨m2, hm2⟩ := (hev _ _).1 v2
    obtain ⟨hne, hi⟩ := hinv _ _ v1 hzb
    have hv : j2 v = (j2 b)⁻¹ * j2 (b * v) := by
      rw [map_mul, inv_mul_cancel_left₀ hne]
    have hl : j2 v ∈ loc (rB ℂ K' (xv x) {0}) e.1 := by
      rw [hv]; exact mul_mem hi m2
    refine (hev _ _).2 ⟨hl, ?_⟩
    have hmul : (⟨j2 b, m1⟩ : loc (rB ℂ K' (xv x) {0}) e.1) * ⟨j2 v, hl⟩ = ⟨j2 (b * v), m2⟩ :=
      Subtype.ext (map_mul j2 b v).symm
    have := congrArg ev hmul
    rw [map_mul, hm1, hm2, hz] at this
    exact mul_left_cancel₀ hzb this
end
