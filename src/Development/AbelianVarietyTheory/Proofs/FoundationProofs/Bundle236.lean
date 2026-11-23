module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle217
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle209
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle024
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle220
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle219
public import Formalism.QuotientMetricDivisors.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle221
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle224
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle026
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle110
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle218
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Formalism.QuotientMetricDivisors.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

namespace GlobalTheory.ThetaConj.IopRepr

theorem mk_eq_iff {V : Type*} [AddCommGroup V] (A₁ A₂ : AddSubgroup V) (a b : A₂) :
    (QuotientAddGroup.mk a : A₂ ⧸ A₁.addSubgroupOf A₂) = QuotientAddGroup.mk b ↔
      (a : V) - (b : V) ∈ A₁ := by
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]
  rfl

theorem iop_eq_sum (D : D7) (T : Tor D) {N N' : ℕ} (A₁ A₂ : AddSubgroup (VC D N N'))
    (F : VC D N N' → ℂ) (hF : RepInd D T A₁ A₂ F) {n : ℕ} (x : Fin n → A₂)
    (hx : Function.Bijective
      (fun i => (QuotientAddGroup.mk (x i) : A₂ ⧸ A₁.addSubgroupOf A₂))) :
    Iop D T A₁ A₂ F =
      (fun z => ((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹ * ∑ i, aU D T (x i) F z) := by
  let e := Equiv.ofBijective _ hx
  letI : Fintype (A₂ ⧸ A₁.addSubgroupOf A₂) := Fintype.ofEquiv _ e
  have hn : (A₁.addSubgroupOf A₂).index = n := by
    rw [AddSubgroup.index, ← Nat.card_congr e]; simp
  funext z
  unfold Iop
  rw [hn, finsum_eq_sum_of_fintype, ← e.sum_comp]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ((Quotient.out (e i) : A₂) : VC D N N') - x i ∈ A₁ := by
    rw [← mk_eq_iff]
    exact Quotient.out_eq (e i)
  exact congrFun (hF _ (Quotient.out (e i) : A₂).2 _ (x i).2 h) z

theorem iop_pair : ∀ (D : D7) (T T' : Tor D) (N N' : ℕ) (A₁ A₂ A₁' A₂' : AddSubgroup (VC D N N')) (F F' : VC D N N' → ℂ) (R : VC D N N' → VC D N N' → Prop), (A₁.addSubgroupOf A₂).FiniteIndex → RepInd D T A₁ A₂ F → RepInd D T' A₁' A₂' F' → (∀ x ∈ A₂, ∃ x' ∈ A₂', R x x') → (∀ x' ∈ A₂', ∃ x ∈ A₂, R x x') → (∀ x x' y y', R x x' → R y y' → (x - y ∈ A₁ ↔ x' - y' ∈ A₁')) → ∃ (n : ℕ) (x x' : Fin n → VC D N N'), (∀ i, x i ∈ A₂ ∧ x' i ∈ A₂' ∧ R (x i) (x' i)) ∧ Iop D T A₁ A₂ F = (fun z => ((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹ * ∑ i, aU D T (x i) F z) ∧ Iop D T' A₁' A₂' F' = (fun z => ((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹ * ∑ i, aU D T' (x' i) F' z) := by
  intro D T T' N N' A₁ A₂ A₁' A₂' F F' R hfin hF hF' h1 h2 h3
  haveI : Finite (A₂ ⧸ A₁.addSubgroupOf A₂) := AddSubgroup.finite_quotient_of_finiteIndex
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (A₂ ⧸ A₁.addSubgroupOf A₂)
  let x : Fin n → A₂ := fun i => Quotient.out (e.symm i)
  have hxe : ∀ i, (QuotientAddGroup.mk (x i) : A₂ ⧸ A₁.addSubgroupOf A₂) = e.symm i :=
    fun i => Quotient.out_eq _
  have hx : Function.Bijective
      (fun i => (QuotientAddGroup.mk (x i) : A₂ ⧸ A₁.addSubgroupOf A₂)) := by
    have : (fun i => (QuotientAddGroup.mk (x i) : A₂ ⧸ A₁.addSubgroupOf A₂)) = e.symm :=
      funext hxe
    rw [this]; exact e.symm.bijective
  choose y hy hR using fun i => h1 (x i) (x i).2
  let x' : Fin n → A₂' := fun i => ⟨y i, hy i⟩
  have hx' : Function.Bijective
      (fun i => (QuotientAddGroup.mk (x' i) : A₂' ⧸ A₁'.addSubgroupOf A₂')) := by
    constructor
    · intro i j hij
      apply hx.1
      have := (mk_eq_iff _ _ _ _).1 hij
      exact (mk_eq_iff _ _ _ _).2 ((h3 _ _ _ _ (hR i) (hR j)).2 this)
    · intro q
      obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective q
      obtain ⟨a, ha, hab⟩ := h2 b b.2
      obtain ⟨i, hi⟩ := hx.2 (QuotientAddGroup.mk ⟨a, ha⟩)
      refine ⟨i, (mk_eq_iff _ _ _ _).2 ?_⟩
      exact (h3 _ _ _ _ (hR i) hab).1 ((mk_eq_iff _ _ _ _).1 hi)
  exact ⟨n, fun i => x i, y, fun i => ⟨(x i).2, hy i, hR i⟩,
    iop_eq_sum D T A₁ A₂ F hF x hx, iop_eq_sum D T' A₁' A₂' F' hF' x' hx'⟩

end GlobalTheory.ThetaConj.IopRepr
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

namespace GlobalTheory.ThetaConj

theorem ee_intCast_half (n : ℤ) : ee ((n : ℝ) / 2) = (-1 : ℂ) ^ n := by
  unfold ee
  rw [← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem al_of_qH (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') (m : ℤ) (h : qH D T x = m) :
    al D T x = (-1 : ℂ) ^ m := by
  unfold qH at h
  unfold al
  rw [h, round_intCast]

theorem qH_add_im (D : D7) (T : Tor D) {N N' : ℕ} (y u : VC D N N') :
    qH D T (y + u) - qH D T y - qH D T u + (Hf D T y u).im = 2 * (Hf D T (w0 D • y) u).im := by
  unfold qH
  rw [Hf_smul_left, Hf_add_left, Hf_add_right, Hf_add_right, Hf_conj D T y u]
  have h1 : (w0 D).re = 1 / 2 := by simp [w0]
  have h2 : (w0 D).im = Real.sqrt D.host.d / 2 := by simp [w0]
  simp only [Complex.add_re, Complex.conj_re, Complex.mul_im, h1, h2]
  ring

theorem repInd_of_thSp (D : D7) (T : Tor D) (N N' : ℕ) (A₁ A₂ : AddSubgroup (VC D N N'))
    (F : VC D N N' → ℂ) (hq : ∀ x ∈ A₂, ∃ m : ℤ, qH D T x = m)
    (hw : ∀ x ∈ A₂, ∀ y ∈ A₂, ∃ m : ℤ, (Hf D T (w0 D • x) y).im = m) (hF : F ∈ ThSp D T A₁) :
    RepInd D T A₁ A₂ F := by
  intro x hx y hy hxy
  have hu2 : x - y ∈ A₂ := A₂.sub_mem hx hy
  obtain ⟨u, rfl⟩ : ∃ u, x = y + u := ⟨x - y, by abel⟩
  rw [add_sub_cancel_left] at hxy hu2
  obtain ⟨a, ha⟩ := hq _ hx
  obtain ⟨b, hb⟩ := hq _ hy
  obtain ⟨c, hc⟩ := hq _ hu2
  obtain ⟨k, hk⟩ := hw _ hy _ hu2
  have h1 := qH_add_im D T y u
  rw [ha, hb, hc, hk] at h1
  have h2 : -(Hf D T y u).im = ((a - b - c - 2 * k : ℤ) : ℝ) := by push_cast; linarith
  funext z
  have h3 := U_U D T y u F z
  rw [h2, ee_intCast_half] at h3
  have h4 : al D T u * U D T y (U D T u F) z = U D T y F z := by
    have := hF.2 u hxy (z + y)
    conv_lhs => rw [U]
    conv_rhs => rw [U]
    rw [← mul_assoc, this]
  unfold aU
  rw [← h4, h3, al_of_qH D T _ _ ha, al_of_qH D T _ _ hb, al_of_qH D T _ _ hc, ← mul_assoc,
    ← mul_assoc, ← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]
  congr 1
  have : b + c + (a - b - c - 2 * k) = a + 2 * (-k) := by ring
  rw [this, zpow_add₀ (by norm_num), zpow_mul]
  norm_num

end GlobalTheory.ThetaConj
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.HolDS Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.HolDS

theorem eq_one_of_smul_haar_eq {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
    [BorelSpace H] [LocallyCompactSpace H] (ν : Measure H) [ν.IsHaarMeasure] {c : NNReal} (h : c • ν = ν) :
    c = 1 := by
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts H) := inferInstance
  have h0 : ν K ≠ 0 := (Measure.measure_pos_of_nonempty_interior ν K.interior_nonempty).ne'
  have h1 : ν K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have h2 : (c : ENNReal) * ν K = 1 * ν K := by
    conv_rhs => rw [← h]
    rw [one_mul, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [ENNReal.mul_left_inj h0 h1] at h2
  exact_mod_cast h2

theorem haar_unimodular : ∀ (p q : ℕ) (T : GrpData p q), T.haar.IsMulRightInvariant ∧ T.haar.IsInvInvariant := by
  intro p q T
  have h := blockOrd_finSumFinEquiv p q
  haveI := GlobalTheory.RealPar.SqInt.isHaarMeasure_map_covU h T
  set ε : Fin (p + q) → Bool := fun i => (finSumFinEquiv.symm i).isLeft
  set f := GlobalTheory.RealPar.SqInt.covU h T
  have hf : Measurable f := (GlobalTheory.RealPar.SqInt.continuous_covU h T).measurable
  obtain ⟨c, hc⟩ : ∃ c : NNReal, T.haar.map f = c • Formalism.REAL.muG ε :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩
  have hR : T.haar.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    have hg := Measure.map_right_mul_eq_modularCharacterFun_smul T.haar g
    have h1 : (T.haar.map (· * g)).map f = T.haar.map f := by
      have h2 : (T.haar.map (· * g)).map f = (T.haar.map f).map (· * f g) := by
        rw [Measure.map_map hf (measurable_mul_const g), Measure.map_map (measurable_mul_const _) hf]
        congr 1
        ext x
        simp
      rw [h2, hc, Measure.map_smul, Formalism.REAL.indefinite_unitary_unimodular _ ε (f g)]
      exact (measurable_mul_const _).aemeasurable
    rw [hg, Measure.map_smul] at h1
    · rw [hg, eq_one_of_smul_haar_eq _ h1, one_smul]
    · exact hf.aemeasurable
  refine ⟨hR, ⟨?_⟩⟩
  haveI : T.haar.inv.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsMulLeftInvariant := inferInstance
      toIsOpenPosMeasure := inferInstance }
  obtain ⟨d, hd⟩ : ∃ d : NNReal, T.haar.inv = d • T.haar := ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩
  have h1 : T.haar.inv.map f = T.haar.map f := by
    have h2 : T.haar.inv.map f = (T.haar.map f).map (fun x => x⁻¹) := by
      rw [Measure.inv_def, Measure.map_map hf measurable_inv, Measure.map_map measurable_inv hf]
      congr 1
      ext x
      simp
    rw [h2, hc, Measure.map_smul, Formalism.REAL.invInvariant_of Formalism.REAL.indefinite_unitary_unimodular _ ε]
    exact measurable_inv.aemeasurable
  rw [hd, Measure.map_smul] at h1
  · rw [hd, eq_one_of_smul_haar_eq _ h1, one_smul]
  · exact hf.aemeasurable

end GlobalTheory.HolDS
end

section

open GlobalTheory.DualWeyl MvPolynomial NumberField IsDedekindDomain
open Formalism.L2.DIV (colLat IsBasisAt dualFr)
open Formalism.HermitianLatticesTheory (localization₂)
open scoped Matrix

namespace GlobalTheory.DualWeylDual

variable {K : Type} [Field K] {N : ℕ}

theorem exists_smul_mem_of_le_locP (w : HeightOneSpectrum (𝓞 K)) {M M' : Submodule (𝓞 K) (Fin N → K)}
    (hM : M.FG) (h : M ≤ localization₂ w.asIdeal M') : ∃ t ∈ w.asIdeal.primeCompl, ∀ x ∈ M, t • x ∈ M' := by
  classical
  obtain ⟨s, rfl⟩ := hM
  have h1 : ∀ y : s, ∃ a ∈ w.asIdeal.primeCompl, a • (y : Fin N → K) ∈ M' := fun y =>
    h (Submodule.subset_span y.2)
  choose a ha0 ha using h1
  refine ⟨∏ y, a y, Submonoid.prod_mem _ fun y _ => ha0 y, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨y, hy⟩ : s)), mul_smul]
    exact M'.smul_mem _ (ha ⟨y, hy⟩)
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact M'.add_mem hy hz
  | smul c y _ hy => rw [smul_comm]; exact M'.smul_mem _ hy

theorem localization_dualFr_le (w : HeightOneSpectrum (𝓞 K)) {M M' : Submodule (𝓞 K) (Fin N → K)}
    (hM : M.FG) (h : localization₂ w.asIdeal M ≤ localization₂ w.asIdeal M') :
    localization₂ w.asIdeal (dualFr M') ≤ localization₂ w.asIdeal (dualFr M) := by
  obtain ⟨t, ht, htM⟩ := exists_smul_mem_of_le_locP w hM
    (fun x hx => h ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩)
  rintro φ ⟨s, hs, hφ⟩
  refine ⟨t * s, Submonoid.mul_mem _ ht hs, fun x hx => ?_⟩
  have h1 : (s • φ) ⬝ᵥ (t • x) ∈ (1 : Submodule (𝓞 K) K) := hφ _ (htM x hx)
  rwa [dotProduct_smul, ← smul_dotProduct, smul_smul] at h1

theorem dualFr_colLat (B : GL (Fin N) K) : dualFr (colLat B) = colLat (Formalism.BasicNotions.inside₂ K N B) := by
  apply SetLike.ext
  intro φ
  rw [mem_colLat_iff]
  constructor
  · intro h
    have h1 : ∀ j, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = φ ⬝ᵥ fun a => (B : Matrix (Fin N) (Fin N) K) a j := fun j =>
      Submodule.mem_one.mp (h _ (Submodule.subset_span ⟨j, rfl⟩))
    choose c hc using h1
    refine ⟨c, ?_⟩
    have h2 : (fun j => (c j : K)) = (B : Matrix (Fin N) (Fin N) K)ᵀ *ᵥ φ := by
      funext j
      rw [Matrix.mulVec_transpose]
      exact hc j
    rw [h2, Matrix.mulVec_mulVec]
    change (((B⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)ᵀ * _) *ᵥ φ = φ
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mulVec]
  · rintro ⟨c, rfl⟩ x hx
    obtain ⟨d, rfl⟩ := (mem_colLat_iff _ _).mp hx
    change (((B⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)ᵀ *ᵥ _) ⬝ᵥ _ ∈ _
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    refine Submodule.mem_one.mpr ⟨c ⬝ᵥ d, ?_⟩
    simp [dotProduct]

theorem isBasisAt_dualFr (w : HeightOneSpectrum (𝓞 K)) {L : Submodule (𝓞 K) (Fin N → K)} (hL : L.FG)
    {B : GL (Fin N) K} (hB : IsBasisAt w L B) : IsBasisAt w (dualFr L) (Formalism.BasicNotions.inside₂ K N B) := by
  unfold IsBasisAt at hB ⊢
  rw [← dualFr_colLat]
  exact le_antisymm (localization_dualFr_le w (Submodule.fg_span (Set.finite_range _)) hB.ge) (localization_dualFr_le w hL hB.le)

end GlobalTheory.DualWeylDual
end

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.fockNorm_extremal_vector_eq_bounded_nat : ∀ (n : ℕ) (lam : DomWeight n) (R : ℕ), (∀ i, lam.natW i ≤ R) → ∃ s : ℕ, 0 < s ∧ s ≤ (n.factorial) ^ (2 * R) * (R.factorial) ^ n ∧ ∀ (K : Type) [Field K] [StarRing K] [CharZero K], fockS (extremal K n lam) (extremal K n lam) = (s : K) := by
  first | exact @GlobalTheory.ExtremalNorm.fockS_extremal_eq_nat | exact GlobalTheory.ExtremalNorm.fockS_extremal_eq_nat | (intros; apply GlobalTheory.ExtremalNorm.fockS_extremal_eq_nat <;> assumption)
end

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

namespace GlobalTheory.TestLat

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}

theorem isBasisAt_inv_mul (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) (Fin n → K)) (B B' : GL (Fin n) K)
    (h : IsBasisAt w M B) (h' : IsBasisAt w M B') : IsBasisAt w (colLat 1) (B'⁻¹ * B) := by
  rw [← isBasisAt_gLat w B', ← colLat_mul, mul_one, mul_inv_cancel_left]
  exact h'.symm.trans h

theorem indep_of_stable (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) (T : Submodule (𝓞 K) (Pol K ι n))
    (hT : ∀ g : ι → GL (Fin n) K, (∀ τ, IsBasisAt w (colLat 1) (g τ)) → ∀ F ∈ T, actP lam g F ∈ T)
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (B B' : ι → GL (Fin n) K)
    (h : ∀ τ, IsBasisAt w (M τ) (B τ)) (h' : ∀ τ, IsBasisAt w (M τ) (B' τ)) (F : Pol K ι n) :
    actP lam B⁻¹ F ∈ T ↔ actP lam B'⁻¹ F ∈ T := by
  constructor
  · intro hF
    have := hT (B'⁻¹ * B) (fun τ => isBasisAt_inv_mul w (M τ) (B τ) (B' τ) (h τ) (h' τ)) _ hF
    rwa [← polyAction_mul, mul_inv_cancel_right] at this
  · intro hF
    have := hT (B⁻¹ * B') (fun τ => isBasisAt_inv_mul w (M τ) (B' τ) (B τ) (h' τ) (h τ)) _ hF
    rwa [← polyAction_mul, mul_inv_cancel_right] at this

theorem nabIndep_and_delIndep : NabIndep ∧ DelIndep :=
  ⟨fun K _ _ ι _ n lam w M B B' h h' F =>
      indep_of_stable lam w _ (GlobalTheory.T.polyAction_mem_locP_nabStd_of_isBasisAt K ι n lam w) M B B' h h' F,
    fun K _ _ ι _ n lam w M B B' h h' F =>
      indep_of_stable lam w _ (GlobalTheory.T.polyAction_mem_locP_delStd_of_isBasisAt K ι n lam w) M B B' h h' F⟩

end GlobalTheory.TestLat
end

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.neg_rank_mul_log_le_log_covolume_hermitian : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), IsRatHerm (cmMax K) H X → ∀ (s : ℕ), 0 < s → ∀ L : Submodule (𝓞 K) (Fin d → K), L.FG → (∀ x ∈ L, ∀ y ∈ L, (s : K) * (star x ⬝ᵥ H *ᵥ y) ∈ (algebraMap (𝓞 K) K).range) → -((Formalism.HN.rkK L : ℝ) * Real.log s) ≤ lcv X L := by
  first | exact @GlobalTheory.neg_rank_mul_log_le_lcv | exact GlobalTheory.neg_rank_mul_log_le_lcv | (intros; apply GlobalTheory.neg_rank_mul_log_le_lcv <;> assumption)
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.GradedKFin

variable {p q : ℕ}

theorem kset_one (T : GrpData p q) : (1 : T.G) ∈ T.Kset := by
  intro a b hab
  have : a ≠ b := by
    rintro rfl
    cases a <;> simp [sameBlock] at hab
  simp [Matrix.one_apply, this]

theorem kset_mul (T : GrpData p q) {g h : T.G} (hg : g ∈ T.Kset) (hh : h ∈ T.Kset) :
    g * h ∈ T.Kset := by
  intro a b hab
  rw [map_mul, Units.val_mul, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hac : sameBlock a c
  · have hcb : ¬ sameBlock c b := by
      cases a <;> cases b <;> cases c <;> simp_all [sameBlock]
    rw [hh c b hcb, mul_zero]
  · rw [hg a c hac, zero_mul]

theorem map_stable (hpq : 1 ≤ p + q) (T : GrpData p q) (σ : URep T) (M : GKMod p q)
    (j : M.V →ₗ[ℂ] σ.H)
    (hder : ∀ Y ∈ upq p q, ∀ x,
      HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0)
    (W : Submodule ℂ M.V) [FiniteDimensional ℂ W] (hW : KStable M.act W)
    {g : T.G} (hg : g ∈ T.Kset) : ∀ x ∈ W.map j, σ.π g x ∈ W.map j := by
  have hcl := GlobalTheory.CoverKGen.kset_gen p q hpq T g hg
  suffices h : (∀ x ∈ W.map j, σ.π g x ∈ W.map j) ∧ (∀ x ∈ W.map j, σ.π g⁻¹ x ∈ W.map j) from h.1
  clear hg
  induction hcl using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨Y, ⟨hY, hKC⟩, rfl⟩ := hg
    have hf := GlobalTheory.RealPar.flow_mem_map j (M.act Y) W (hW Y hKC) (fun t => σ.π (T.expt (t • Y)))
      (by simp [T.expt_zero]) (fun s t => by simp only [T.expt_add Y hY, map_mul]) (hder Y hY)
    have hinv : (T.expt Y)⁻¹ = T.expt ((-1 : ℝ) • Y) := by
      have := T.expt_add Y hY 1 (-1)
      rw [add_neg_cancel, zero_smul, T.expt_zero, one_smul] at this
      exact (eq_inv_of_mul_eq_one_right this.symm).symm
    refine ⟨?_, ?_⟩
    · have := hf 1
      simpa only [one_smul] using this
    · rw [hinv]; exact hf (-1)
  | one => simp
  | mul a b _ _ ha hb =>
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [map_mul]; exact ha.1 _ (hb.1 x hx)
    · rw [mul_inv_rev, map_mul]; exact hb.2 _ (ha.2 x hx)
  | inv a _ ha => exact ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

theorem isHCMod_of_graded : ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (σ : URep T) (M : GKMod p q) (j : M.V →ₗ[ℂ] σ.H), Function.Injective j → Dense (Set.range j) → (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0) → ∀ (N : ℕ → Submodule ℂ M.V) (k : T.G) (lam : ℕ → ℂ), (∀ m, FiniteDimensional ℂ (N m)) → (⨆ m, N m) = ⊤ → k ∈ T.Kset → Function.Injective lam → (∀ m, ∀ x ∈ N m, σ.π k (j x) = lam m • j x) → IsHCMod σ M j := by
  intro p q hpq T σ M j hj hd hder N k lam hfin htop hk hlam heig
  refine ⟨hj, fun x => ⟨?_, fun hx => ?_⟩, hder⟩
  · rintro ⟨v, rfl⟩
    obtain ⟨W, hWf, hv, hW⟩ := M.kfin v
    have hle : Submodule.span ℂ (Set.range fun g : T.Kset => σ.π g (j v)) ≤ W.map j := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact map_stable hpq T σ M j hder W hW g.2 _ ⟨v, hv, rfl⟩
    exact Submodule.finiteDimensional_of_le hle
  · have hsup : (⨆ m, (N m).map j) = LinearMap.range j := by
      rw [← Submodule.map_iSup, htop, Submodule.map_top]
    have hle := GlobalTheory.HolDS.finiteDimensional_stable_le_iSup_eigen σ.H (σ.π k) (σ.isom k)
      (fun m => (N m).map j) lam hlam (fun m => inferInstance)
      (by rintro m _ ⟨y, hy, rfl⟩; exact heig m y hy)
      (by rw [hsup]; exact hd)
      (Submodule.span ℂ (Set.range fun g : T.Kset => σ.π g x)) hx (by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨g, rfl⟩ := hw
          refine Submodule.subset_span ⟨⟨k * g, kset_mul T hk g.2⟩, ?_⟩
          simp only [map_mul]
          rfl
        | zero => simp
        | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
        | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha)
    rw [hsup] at hle
    exact hle (Submodule.subset_span ⟨⟨1, kset_one T⟩, by simp⟩)

end GlobalTheory.GradedKFin
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.monomialDeriv_cauchy_bound_gaussianGrowth : ∀ (D : D7) (N N' : ℕ) (G : VC D N N' → ℂ) (S A B : ℝ), 0 < A → 1 ≤ B → 0 ≤ S → Differentiable ℂ G → (∀ z, ‖G z‖ ^ 2 ≤ S * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / A)) → ∀ α : Mono D N N', (∀ k, (α k : ℝ) ≤ 2 * B) → ‖(α.prod fun _ n => (n.factorial : ℂ)) * taylor D G α‖ ^ 2 ≤ S * (2 * Real.exp 1 * Real.pi * B / A) ^ (α.sum fun _ n => n) := by
  first | exact @GlobalTheory.GaussCauchy.monomial_deriv_bound | exact GlobalTheory.GaussCauchy.monomial_deriv_bound | (intros; apply GlobalTheory.GaussCauchy.monomial_deriv_bound <;> assumption)
end
