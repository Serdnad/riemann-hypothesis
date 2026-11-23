module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle055
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.RootEx.UnipPow

theorem pow_dvd_choose {q : ℕ} (hq : q.Prime) (m : ℕ) {i : ℕ} (hi : i ≠ 0) :
    q ^ (m - i) ∣ (q ^ m).choose i := by
  have := Fact.mk hq
  rcases Nat.eq_zero_or_pos ((q ^ m).choose i) with h0 | hpos
  · rw [h0]
    exact dvd_zero _
  have hdvd : q ^ m ∣ (q ^ m).choose i * i := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hi
    obtain ⟨N, hN⟩ := Nat.exists_eq_add_one_of_ne_zero (pow_ne_zero m hq.ne_zero)
    rw [hN]
    exact ⟨N.choose j, (Nat.add_one_mul_choose_eq N j).symm⟩
  have hv : m ≤ padicValNat q ((q ^ m).choose i) + padicValNat q i := by
    rw [← (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hpos.ne' hi]
    exact ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) (mul_ne_zero hpos.ne' hi)).mp hdvd
  have hi' : padicValNat q i < i := by
    simpa only [Nat.padicValNat_def] using (padicValNat_le_nat_log i).trans_lt (Nat.log_lt_self q hi)
  exact ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hpos.ne').mpr (by omega)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_resCard_lt_one : valuation k (resCard k : k) < 1 := by
  have hres : IsLocalRing.residue 𝒪[k] (resCard k : 𝒪[k]) = 0 := by
    let := Fintype.ofFinite 𝓀[k]
    rw [map_natCast, resCard, Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero _
  have hnu : ¬ IsUnit (resCard k : 𝒪[k]) := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hres
    exact hres
  have hlt := (Valuation.Integer.not_isUnit_iff_valuation_lt_one (v := valuation k)).mp hnu
  simpa using hlt

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem valuation_natCast_le_one (j : ℕ) : valuation k (j : k) ≤ 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.cast_succ]
    exact ((valuation k).map_add _ _).trans (max_le ih (by simp))

theorem tendsto_choose (hq : (resCard k).Prime) {i : ℕ} (hi : i ≠ 0) :
    Filter.Tendsto (fun m : ℕ => (((resCard k ^ m).choose i : ℕ) : k)) Filter.atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero k).tendsto_right_iff]
  intro γ _
  have hq1 := valuation_resCard_lt_one (k := k)
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hq1 γ
  rw [Filter.eventually_atTop]
  refine ⟨n + i, fun m hm => ?_⟩
  obtain ⟨t, ht⟩ := pow_dvd_choose hq m hi
  show valuation k (((resCard k ^ m).choose i : ℕ) : k) < γ
  rw [ht, Nat.cast_mul, map_mul, Nat.cast_pow, map_pow]
  calc valuation k (resCard k : k) ^ (m - i) * valuation k (t : k)
      ≤ valuation k (resCard k : k) ^ (m - i) := mul_le_of_le_one_right' (valuation_natCast_le_one t)
    _ ≤ valuation k (resCard k : k) ^ n := pow_le_pow_right_of_le_one' hq1.le (by omega)
    _ < γ := hn

theorem add_one_pow_eq {R : Type} [Ring R] {a : R} {d : ℕ} (ha : a ^ d = 0) (M : ℕ) :
    (a + 1) ^ M = ∑ i ∈ Finset.range d, (M.choose i) • a ^ i := by
  rw [(Commute.one_right a).add_pow]
  simp only [one_pow, mul_one]
  have key : ∀ s : Finset ℕ, ∑ i ∈ s, a ^ i * (M.choose i : R) = ∑ i ∈ s, M.choose i • a ^ i :=
    fun s => Finset.sum_congr rfl fun i _ => by rw [nsmul_eq_mul]; exact (Nat.cast_comm _ _).symm
  rw [key]
  calc ∑ i ∈ Finset.range (M + 1), M.choose i • a ^ i
      = ∑ i ∈ Finset.range (M + 1 + d), M.choose i • a ^ i := by
        refine Finset.sum_subset (Finset.range_mono (by omega)) fun i hi hi' => ?_
        rw [Finset.mem_range] at hi'
        rw [Nat.choose_eq_zero_of_lt (by omega : M < i), zero_smul]
    _ = ∑ i ∈ Finset.range d, M.choose i • a ^ i := by
        refine (Finset.sum_subset (Finset.range_mono (by omega)) fun i hi hi' => ?_).symm
        rw [Finset.mem_range] at hi'
        rw [pow_eq_zero_of_le (by omega : d ≤ i) ha, smul_zero]

theorem tendsto_pow_of_nilpotent {ι : Type} [Fintype ι] [DecidableEq ι] (hq : (resCard k).Prime)
    {g : Matrix ι ι k} {d : ℕ} (ha : (g - 1) ^ (d + 1) = 0) :
    Filter.Tendsto (fun m : ℕ => g ^ (resCard k ^ m)) Filter.atTop (𝓝 1) := by
  have hexp : ∀ m : ℕ, g ^ (resCard k ^ m) =
      ∑ i ∈ Finset.range (d + 1), (((resCard k ^ m).choose i : ℕ) : k) • (g - 1) ^ i := by
    intro m
    have h := add_one_pow_eq ha (resCard k ^ m)
    rw [sub_add_cancel] at h
    rw [h]
    exact Finset.sum_congr rfl fun i _ => (Nat.cast_smul_eq_nsmul k _ _).symm
  have hlim := (tendsto_finsetSum (Finset.range d) fun i _ =>
    (tendsto_choose hq (Nat.succ_ne_zero i)).smul_const ((g - 1) ^ (i + 1))).add
    (tendsto_const_nhds (x := (1 : Matrix ι ι k)))
  simp only [zero_smul, Finset.sum_const_zero, zero_add] at hlim
  refine hlim.congr fun m => ?_
  rw [hexp, Finset.sum_range_succ']
  simp

theorem pow_sub_one_apply {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
    {g : GL (n ⊕ Fin c) K} (hg : InN p g) (j : ℕ) :
    ∀ r s : n ⊕ Fin c, lev p s < lev p r + j →
      (((g : Matrix (n ⊕ Fin c) (n ⊕ Fin c) K) - 1) ^ j) r s = 0 := by
  induction j with
  | zero =>
    intro r s h
    rw [pow_zero, Matrix.one_apply_ne (by rintro rfl; omega)]
  | succ j ih =>
    intro r s h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases ht : lev p t < lev p r + j
    · rw [ih r t ht, zero_mul]
    · rw [Matrix.sub_apply, hg t s (by omega), sub_self, mul_zero]

theorem pow_sub_one_eq_zero {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
    {g : GL (n ⊕ Fin c) K} (hg : InN p g) :
    ((g : Matrix (n ⊕ Fin c) (n ⊕ Fin c) K) - 1) ^ (c + p + 1) = 0 := by
  have hb : ∀ t : n ⊕ Fin c, lev p t ≤ c + p := by
    rintro (t | t)
    · show p ≤ c + p
      omega
    · show t.val + 1 ≤ c + p
      have := t.isLt
      omega
  ext r s
  rw [Matrix.zero_apply]
  exact pow_sub_one_apply hg _ r s (by have := hb s; omega)

theorem inN_of_mem {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
    {g : GL (n ⊕ Fin c) K} (hg : g ∈ N K n c p) : InN p g := by
  have hle : N K n c p ≤ GlobalTheory.RootEx.Model.Nsub K n c p :=
    (Subgroup.closure_le _).mpr fun x hx => hx
  exact hle hg

theorem exists_pow_mem_nhds (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ)
    (hq : (resCard k).Prime) :
    ∀ u ∈ N k n c p, ∀ U ∈ 𝓝 (1 : GL (n ⊕ Fin c) k), ∃ m : ℕ, u ^ (resCard k ^ m) ∈ U := by
  intro u hu U hU
  have h1 := tendsto_pow_of_nilpotent (k := k) hq (pow_sub_one_eq_zero (inN_of_mem hu))
  have h2 := tendsto_pow_of_nilpotent (k := k) hq (pow_sub_one_eq_zero (inN_of_mem (inv_mem hu)))
  have hA : Filter.Tendsto (fun m : ℕ => ((u ^ (resCard k ^ m) : GL (n ⊕ Fin c) k) :
      Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) Filter.atTop (𝓝 1) :=
    h1.congr fun m => (Units.val_pow_eq_pow_val _ _).symm
  have hB : Filter.Tendsto (fun m : ℕ => (((u ^ (resCard k ^ m))⁻¹ : GL (n ⊕ Fin c) k) :
      Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) Filter.atTop (𝓝 1) :=
    h2.congr fun m => by rw [← inv_pow, Units.val_pow_eq_pow_val]
  have hT : Filter.Tendsto (fun m : ℕ => u ^ (resCard k ^ m)) Filter.atTop (𝓝 1) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    have hP := hA.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp hB)
    simpa [Function.comp_def] using hP
  exact (hT.eventually_mem hU).exists

end GlobalTheory.RootEx.UnipPow
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.RootEx

theorem rowE_zero_eq_one {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] (c p : ℕ) :
    rowE c p (0 : n → k) = 1 := by
  apply Units.ext
  have hC : (Matrix.of fun (l : Fin c) (s : n) => if l.val + 1 = p then (0 : n → k) s else 0) = 0 := by
    ext l s
    simp
  show Matrix.fromBlocks 1 0
      (Matrix.of fun (l : Fin c) (s : n) => if l.val + 1 = p then (0 : n → k) s else 0) 1 = 1
  rw [hC, Matrix.fromBlocks_one]

theorem colE_zero_eq_one {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] (c p : ℕ) :
    colE c p (0 : n → k) = 1 := by
  apply Units.ext
  have hB : (Matrix.of fun (r : n) (i : Fin c) => if i.val + 1 = p then (0 : n → k) r else 0) = 0 := by
    ext r i
    simp
  show Matrix.fromBlocks 1
      (Matrix.of fun (r : n) (i : Fin c) => if i.val + 1 = p then (0 : n → k) r else 0) 0 1 = 1
  rw [hB, Matrix.fromBlocks_one]

private theorem sigmaCompactSpace_nonarchimedeanLocalField (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : SigmaCompactSpace k := by
  obtain ⟨γ, hγ0, hγ1⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := k)
  have hδ : (1 : ValueGroupWithZero k) < γ⁻¹ := one_lt_inv_iff₀.mpr ⟨hγ0, hγ1⟩
  refine ⟨⟨fun m : ℕ => {x : k | valuation k x ≤ γ⁻¹ ^ m},
    fun m => IsNonarchimedeanLocalField.isCompact_closedBall k _, ?_⟩⟩
  ext x
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact MulArchimedean.arch (valuation k x) hδ

private theorem fourier_fourier_eq_neg {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n]
    [DecidableEq n] (ψ : AddChar k Circle) (ν : Measure k) [SigmaFinite ν] [ν.IsAddHaarMeasure]
    (hF : ∀ f ∈ SB (n → k), ∫ y : n → k, (∫ x : n → k, f x * (ψ (x ⬝ᵥ y) : ℂ)
      ∂(Measure.pi fun _ => ν)) ∂(Measure.pi fun _ => ν) = f 0)
    (f : (n → k) → ℂ) (hf : f ∈ SB (n → k)) (z : n → k) :
    ∫ y : n → k, (∫ x : n → k, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) * (ψ (y ⬝ᵥ z) : ℂ)
      ∂(Measure.pi fun _ => ν) = f (-z) := by
  have hτ : (fun x : n → k => f (x - z)) ∈ SB (n → k) :=
    ⟨hf.1.comp_continuous (continuous_sub_right z), hf.2.comp_homeomorph (Homeomorph.subRight z)⟩
  have key : ∀ y : n → k, (∫ x : n → k, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν))
      * (ψ (y ⬝ᵥ z) : ℂ) = ∫ x : n → k, f (x - z) * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν) := by
    intro y
    rw [← integral_mul_const,
      ← integral_add_right_eq_self (fun x : n → k => f (x - z) * (ψ (x ⬝ᵥ y) : ℂ)) z]
    congr 1
    funext x
    simp only [add_sub_cancel_right, add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul,
      dotProduct_comm z y]
    ring
  calc _ = ∫ y : n → k, (∫ x : n → k, f (x - z) * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν))
        ∂(Measure.pi fun _ => ν) := by
          congr 1
          funext y
          exact key y
    _ = f (0 - z) := hF _ hτ
    _ = f (-z) := by rw [zero_sub]

theorem exDown_exUp_and_exUp_exDown : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (l : A →ₗ[ℂ] ℂ) (v : A), (IsNEquiv ψ p σ l → exDown ν p σ (exUp ν p σ l) v = l v) ∧ (IsNEquiv ψ (p + 1) σ l → exUp ν p σ (exDown ν p σ l) v = l v) := by
  intro k _ _ _ _ _ _ n _ _ c p hp hpc ψ hψc hψ1 ν hsd A _ _ σ hσ l v
  have : ν.IsAddHaarMeasure := hsd.1
  have hT := GlobalTheory.T.rootExchange_support_and_fourier_relation k n c p hp hpc ψ hψc hψ1 ν A σ hσ l v
  have hF := GlobalTheory.T.fourier_transform_inversion_localFieldPi k n ψ hψc hψ1 ν hsd
  constructor
  · intro hN
    obtain ⟨hSB, -, hint⟩ := hT.1 hN
    have h1 : exDown ν p σ (exUp ν p σ l) v
        = ∫ β : n → k, ∫ u : n → k, (fun u : n → k => l (σ (rowE c p u) v)) u * (ψ (u ⬝ᵥ β) : ℂ)
          ∂(Measure.pi fun _ => ν) ∂(Measure.pi fun _ => ν) := by
      unfold exDown
      congr 1
      funext β
      rw [hint β]
      congr 1
      funext u
      ring
    rw [h1, (hF _ hSB).2]
    simp [rowE_zero_eq_one]
  · intro hN
    obtain ⟨hSB, hcomm⟩ := hT.2 hN
    have : SigmaCompactSpace k := sigmaCompactSpace_nonarchimedeanLocalField k
    have : SigmaFinite ν := inferInstance
    have hF2 := fun f hf => (hF f hf).2
    have hG := (hF _ hSB).1
    have hGG := (hF _ hG).1
    have h1 : exUp ν p σ (exDown ν p σ l) v
        = ∫ u : n → k, ∫ y : n → k, (∫ x : n → k, (∫ β : n → k, l (σ (colE c (p + 1) β) v)
            * (ψ (β ⬝ᵥ x) : ℂ) ∂(Measure.pi fun _ => ν)) * (ψ (x ⬝ᵥ y) : ℂ)
            ∂(Measure.pi fun _ => ν)) * (ψ (y ⬝ᵥ u) : ℂ)
          ∂(Measure.pi fun _ => ν) ∂(Measure.pi fun _ => ν) := by
      unfold exUp exDown
      congr 1
      funext u
      rw [fourier_fourier_eq_neg ψ ν hF2 _ hG u]
      congr 1
      funext β
      rw [hcomm u β, dotProduct_neg, dotProduct_comm]
      ring
    rw [h1, hF2 _ hGG]
    simp only [dotProduct_zero, AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
    rw [hF2 _ hSB]
    show l (σ (colE c (p + 1) 0) v) = l v
    rw [colE_zero_eq_one, map_one]
    rfl

end GlobalTheory.RootEx
end

section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
open scoped ENNReal

namespace GlobalTheory.SmGL.LeviInt


open MeasureTheory Topology in
open scoped ENNReal in
open ValuativeRel Matrix in
theorem _root_.GlobalTheory.SmGL.LeviInt.nabs_det_eq_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {g : GL n k}
    (hg : g ∈ _root_.GlobalTheory.SplitWeil.KO k n) :
    _root_.GlobalTheory.SplitWeil.nabs k (GeneralLinearGroup.det g) = 1 := by
  obtain ⟨h1, h2⟩ := (_root_.GlobalTheory.SplitFlip.mem_KO_iff g).1 hg
  have hdet : ∀ M : Matrix n n k, (∀ i j, M i j ∈ (valuation k).integer) →
      M.det ∈ (valuation k).integer := by
    intro M hM
    rw [Matrix.det_apply]
    refine sum_mem fun σ _ => ?_
    rw [Units.smul_def]
    exact zsmul_mem (prod_mem fun i _ => hM _ _) _
  apply _root_.GlobalTheory.SmGL.nabs_eq_one
  have hd1 : valuation k ((GeneralLinearGroup.det g : kˣ) : k) ≤ 1 := by
    rw [← Valuation.mem_integer_iff, Matrix.GeneralLinearGroup.val_det_apply]
    exact hdet _ h1
  have hd2 : valuation k (((GeneralLinearGroup.det g)⁻¹ : kˣ) : k) ≤ 1 := by
    rw [← map_inv, ← Valuation.mem_integer_iff, Matrix.GeneralLinearGroup.val_det_apply]
    exact hdet _ h2
  have hprod : valuation k ((GeneralLinearGroup.det g : kˣ) : k) *
      valuation k (((GeneralLinearGroup.det g)⁻¹ : kˣ) : k) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  exact le_antisymm hd1 (hprod ▸ mul_le_of_le_one_right' hd2)


open MeasureTheory Topology in
open scoped ENNReal in
theorem _root_.GlobalTheory.SmGL.LeviInt.levi_integral_facts : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n), (∀ (g : _root_.GlobalTheory.SmGL.Levi k m) (u : GL n k), u ∈ _root_.GlobalTheory.SmGL.unipRad k e → (_root_.GlobalTheory.SmGL.leviEmb k e g * u ∈ _root_.GlobalTheory.SplitWeil.KO k n ↔ (∀ a, g a ∈ _root_.GlobalTheory.SplitWeil.KO k (m a)) ∧ u ∈ _root_.GlobalTheory.SplitWeil.KO k n)) ∧ (∀ p : _root_.GlobalTheory.SmGL.parab k e, (p : GL n k) ∈ _root_.GlobalTheory.SplitWeil.KO k n → ∀ a, _root_.GlobalTheory.SmGL.leviProj k e p a ∈ _root_.GlobalTheory.SplitWeil.KO k (m a)) ∧ (∀ g : _root_.GlobalTheory.SmGL.Levi k m, (∀ a, g a ∈ _root_.GlobalTheory.SplitWeil.KO k (m a)) → _root_.GlobalTheory.SmGL.modulus k m g = 1) ∧ (∀ g h : _root_.GlobalTheory.SmGL.Levi k m, _root_.GlobalTheory.SmGL.modulus k m (g * h) = _root_.GlobalTheory.SmGL.modulus k m g * _root_.GlobalTheory.SmGL.modulus k m h) ∧ Continuous (_root_.GlobalTheory.SmGL.modulus k m) ∧ Continuous (_root_.GlobalTheory.SmGL.leviProj k e) ∧ IsClosed (_root_.GlobalTheory.SmGL.parab k e : Set (GL n k)) ∧ IsClosed (_root_.GlobalTheory.SmGL.unipRad k e : Set (GL n k)) ∧ ∀ g : GL n k, ∃ p ∈ _root_.GlobalTheory.SmGL.parab k e, ∃ x ∈ _root_.GlobalTheory.SplitWeil.KO k n, g = p * x := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e
  have hT2 : T2Space k := (_root_.GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)).2
  have hlevi : ∀ (g : _root_.GlobalTheory.SmGL.Levi k m) (u : GL n k), u ∈ _root_.GlobalTheory.SmGL.unipRad k e →
      (_root_.GlobalTheory.SmGL.leviEmb k e g * u ∈ _root_.GlobalTheory.SplitWeil.KO k n ↔
        (∀ a, g a ∈ _root_.GlobalTheory.SplitWeil.KO k (m a)) ∧
          u ∈ _root_.GlobalTheory.SplitWeil.KO k n) := by
    intro g u hu
    rw [← Subgroup.inv_mem_iff, mul_inv_rev, ← map_inv]
    refine (_root_.GlobalTheory.SmGL.UnitInd.unip_mul_levi_mem_KO e ⟨u⁻¹, inv_mem hu⟩ g⁻¹).trans ?_
    have hinv : ∀ a, (g⁻¹) a = (g a)⁻¹ := fun a => rfl
    simp only [hinv, Subgroup.inv_mem_iff]
    exact and_comm
  have hemb : ∀ g : _root_.GlobalTheory.SmGL.Levi k m,
      _root_.GlobalTheory.SmGL.leviEmb k e g ∈ _root_.GlobalTheory.SmGL.parab k e := by
    intro g
    apply _root_.GlobalTheory.SmGL.mem_parab_iff.2
    intro a b i j hab
    classical
    simp [_root_.GlobalTheory.SmGL.leviEmb, Matrix.blockDiagonal'_apply, hab.ne']
  have hdec : ∀ p : _root_.GlobalTheory.SmGL.parab k e,
      ∃ u ∈ _root_.GlobalTheory.SmGL.unipRad k e,
        (p : GL n k) = _root_.GlobalTheory.SmGL.leviEmb k e (_root_.GlobalTheory.SmGL.leviProj k e p) * u := by
    intro p
    let L : _root_.GlobalTheory.SmGL.parab k e :=
      ⟨_root_.GlobalTheory.SmGL.leviEmb k e (_root_.GlobalTheory.SmGL.leviProj k e p), hemb _⟩
    have hL : _root_.GlobalTheory.SmGL.leviProj k e L = _root_.GlobalTheory.SmGL.leviProj k e p := by
      funext a
      ext i j
      simp [_root_.GlobalTheory.SmGL.leviProj_apply, L, _root_.GlobalTheory.SmGL.leviEmb, Matrix.blockDiagonal'_apply_eq]
    refine ⟨((L⁻¹ * p : _root_.GlobalTheory.SmGL.parab k e) : GL n k), ?_, ?_⟩
    · unfold _root_.GlobalTheory.SmGL.unipRad
      refine Subgroup.mem_map.mpr ⟨L⁻¹ * p, ?_, rfl⟩
      change _root_.GlobalTheory.SmGL.leviProj k e (L⁻¹ * p) = 1
      rw [map_mul, map_inv, hL, inv_mul_cancel]
    · rw [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (mul_inv_cancel_left _ _).symm
  have hproj : ∀ p : _root_.GlobalTheory.SmGL.parab k e,
      (p : GL n k) ∈ _root_.GlobalTheory.SplitWeil.KO k n →
        ∀ a, _root_.GlobalTheory.SmGL.leviProj k e p a ∈ _root_.GlobalTheory.SplitWeil.KO k (m a) := by
    intro p hp a
    obtain ⟨u, hu, hpu⟩ := hdec p
    rw [hpu] at hp
    exact ((hlevi _ u hu).1 hp).1 a
  have hmod : ∀ g : _root_.GlobalTheory.SmGL.Levi k m,
      (∀ a, g a ∈ _root_.GlobalTheory.SplitWeil.KO k (m a)) → _root_.GlobalTheory.SmGL.modulus k m g = 1 := by
    intro g hg
    unfold _root_.GlobalTheory.SmGL.modulus
    exact Finset.prod_eq_one fun a _ => by
      rw [_root_.GlobalTheory.SmGL.LeviInt.nabs_det_eq_one (hg a), one_zpow]
  have hmul : ∀ g h : _root_.GlobalTheory.SmGL.Levi k m,
      _root_.GlobalTheory.SmGL.modulus k m (g * h) = _root_.GlobalTheory.SmGL.modulus k m g * _root_.GlobalTheory.SmGL.modulus k m h := by
    intro g h
    unfold _root_.GlobalTheory.SmGL.modulus
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← mul_zpow, ← _root_.GlobalTheory.SmGL.nabs_mul', ← map_mul]
    rfl
  have hcont : Continuous (_root_.GlobalTheory.SmGL.leviProj k e) := by
    refine continuous_pi fun a => Units.continuous_iff.2 ⟨?_, ?_⟩
    · refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [Function.comp_apply, _root_.GlobalTheory.SmGL.leviProj_apply]
      exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem _ _
    · have hinv : ∀ p : _root_.GlobalTheory.SmGL.parab k e,
          (_root_.GlobalTheory.SmGL.leviProj k e p a)⁻¹ = _root_.GlobalTheory.SmGL.leviProj k e p⁻¹ a := by
        intro p
        rw [map_inv]
        rfl
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [hinv, _root_.GlobalTheory.SmGL.leviProj_apply, Subgroup.coe_inv]
      exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_elem _ _
  have hP : IsClosed (_root_.GlobalTheory.SmGL.parab k e : Set (GL n k)) := by
    have hset : (_root_.GlobalTheory.SmGL.parab k e : Set (GL n k)) =
        ⋂ (a) (b) (i : m a) (j : m b) (_ : b < a),
          {g : GL n k | (g : Matrix n n k) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0} := by
      ext g
      rw [SetLike.mem_coe, _root_.GlobalTheory.SmGL.mem_parab_iff]
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rw [hset]
    exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun i =>
      isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_eq (Units.continuous_val.matrix_elem _ _) continuous_const
  have hN : IsClosed (_root_.GlobalTheory.SmGL.unipRad k e : Set (GL n k)) := by
    have hset : (_root_.GlobalTheory.SmGL.unipRad k e : Set (GL n k)) =
        (_root_.GlobalTheory.SmGL.parab k e : Set (GL n k)) ∩
          ⋂ (a) (i : m a) (j : m a), {g : GL n k |
            (g : Matrix n n k) (e ⟨a, i⟩) (e ⟨a, j⟩) = (1 : Matrix (m a) (m a) k) i j} := by
      ext g
      rw [SetLike.mem_coe, _root_.GlobalTheory.SmGL.mem_unipRad]
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe]
    rw [hset]
    exact hP.inter (isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (Units.continuous_val.matrix_elem _ _) continuous_const)
  refine ⟨hlevi, hproj, hmod, hmul, _root_.GlobalTheory.SmGL.UnitInd.isLocallyConstant_modulus.continuous, hcont,
    hP, hN, fun g => ?_⟩
  obtain ⟨u, h, w, hw, rfl⟩ := _root_.GlobalTheory.SmGL.UnitInd.exists_iwasawa e g
  exact ⟨_, mul_mem (_root_.GlobalTheory.SmGL.unipRad_le_parab k e u.2)
    (hemb h), w, hw, rfl⟩

end GlobalTheory.SmGL.LeviInt
end
