module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeSqSubLeSlopeSqSpan
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean
public import Formalism.LocalRingCardinality.Lemmas
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Formalism.MeanHeightDescent.AverageDegreeBounds.GoodBadCut
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.OrthSum
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtGram
import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1109
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1110
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

namespace GlobalTheory.OrthSumGram

open Matrix

theorem blockDiagonal'_mulVec_apply' {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
    (M : ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ) (u : (Σ i, Fin (n i)) → ℂ) (i : ι) (j : Fin (n i)) :
    (blockDiagonal' M *ᵥ u) ⟨i, j⟩ = (M i *ᵥ fun l => u ⟨i, l⟩) j := by
  simp only [mulVec, dotProduct, Fintype.sum_sigma, blockDiagonal'_apply]
  rw [Finset.sum_eq_single i]
  · refine Finset.sum_congr rfl fun l _ => ?_
    simp
  · intro k _ hk
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [dite_eq_right (Ne.symm hk), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem orth_sum_hasGram : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] (ι : Type) [Fintype ι] (N : (K →+* ℂ) → V → ℝ) (W : ι → Submodule K V), (∀ σ x, 0 ≤ N σ x) → iSupIndep W → ⨆ i, W i = ⊤ → (∀ i, HasGram (fun σ (x : W i) => N σ x)) → (∀ σ, ∀ f : ∀ i, W i, N σ (∑ i, (f i : V)) ^ 2 = ∑ i, N σ (f i) ^ 2) → HasGram N := by
  classical
  intro K V _ _ _ _ ι _ N W hN hind htop hG hpy
  have hint : DirectSum.IsInternal W :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top W).2 ⟨hind, htop⟩
  let g := fun i => (hG i).some
  let n : ι → ℕ := fun i => (g i).1
  let b : ∀ i, Module.Basis (Fin (n i)) K (W i) := fun i => (g i).2.1.1
  let X : ∀ i, InfinitePlace K → Matrix (Fin (n i)) (Fin (n i)) ℂ := fun i => (g i).2.1.2
  have hX : ∀ i, IsGram (b i) (X i) (fun σ (x : W i) => N σ x) := fun i => (g i).2.2
  let B := hint.collectedBasis b
  have hB : ∀ a, B a = (b a.1 a.2 : V) := fun a => by
    simp only [B, DirectSum.IsInternal.collectedBasis_coe]
  let Xv : InfinitePlace K → Matrix (Σ i, Fin (n i)) (Σ i, Fin (n i)) ℂ := fun v => blockDiagonal' fun i => X i v
  have hmul : ∀ v, Xv v * blockDiagonal' (fun i => (X i v)⁻¹) = 1 := fun v => by
    simp only [Xv, ← blockDiagonal'_mul]
    rw [← blockDiagonal'_one]
    congr 1
    funext i
    exact Matrix.mul_nonsing_inv _ ((hX i v).1)
  refine IsGram.hasGram (b := B) (X := Xv) fun v => ⟨Matrix.isUnit_det_of_right_inverse (hmul v), fun x => ?_⟩
  have hinv : (Xv v)⁻¹ = blockDiagonal' (fun i => (X i v)⁻¹) := Matrix.inv_eq_right_inv (hmul v)
  let c := B.repr x
  let f : ∀ i, W i := fun i => ∑ j, c ⟨i, j⟩ • b i j
  have hx : x = ∑ i, (f i : V) := by
    conv_lhs => rw [← B.sum_repr x]
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [f, Submodule.coe_sum, Submodule.coe_smul, hB]
    rfl
  have hrep : ∀ i j, (b i).repr (f i) j = c ⟨i, j⟩ := fun i j => by
    simp only [f, Module.Basis.repr_sum_self]
  have hcoord : ∀ i j, Formalism.HermitianLatticesTheory.fcoord B Xv v x ⟨i, j⟩ = Formalism.HermitianLatticesTheory.fcoord (b i) (X i) v (f i) j := fun i j => by
    simp only [Formalism.HermitianLatticesTheory.fcoord, hinv, blockDiagonal'_mulVec_apply']
    congr 1
    funext l
    simp only [Formalism.HermitianLatticesTheory.vecAt, hrep, c]
  have hsq : Formalism.HermitianLatticesTheory.normAt B Xv v x ^ 2 = N v.embedding x ^ 2 := by
    rw [hx, hpy, ← hx]
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : Formalism.HermitianLatticesTheory.normAt (b i) (X i) v (f i) = N v.embedding (f i) := (hX i v).2 (f i)
    rw [← e]
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcoord]
  have h0 : 0 ≤ Formalism.HermitianLatticesTheory.normAt B Xv v x := Real.sqrt_nonneg _
  exact (sq_eq_sq₀ h0 (hN _ _)).1 hsq

end GlobalTheory.OrthSumGram
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

noncomputable section

namespace GlobalTheory.TwistIdeal

theorem htMap_le {K V W ι κ : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {b : Module.Basis ι K V} {X : InfinitePlace K → Matrix ι ι ℂ} {b' : Module.Basis κ K W}
    {X' : InfinitePlace K → Matrix κ κ ℂ} {N : (K →+* ℂ) → V → ℝ} {N' : (K →+* ℂ) → W → ℝ}
    (hG : IsGram b X N) (hG' : IsGram b' X' N') (φ : V →ₗ[K] W) (hφ : φ ≠ 0) (t : (K →+* ℂ) → ℝ)
    (ht : ∀ σ, 0 < t σ) (htc : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (hN : ∀ σ x, N' σ (φ x) ≤ t σ * N σ x) :
    Formalism.HN.htMap b X b' X' φ ≤ 2 * (∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ) := by
  have hop : ∀ v : InfinitePlace K, Formalism.HN.opNormAt b X b' X' v φ ^ 2 ≤ t v.embedding ^ 2 := fun v =>
    opNormAt_sq_le b X b' X' (fun v => (hG v).1) v (IsTotallyComplex.isComplex v) φ _ (sq_nonneg _) fun x => by
      rw [← normAt_sq_eq_majAt, ← normAt_sq_eq_majAt, (hG v).2, (hG' v).2, ← mul_pow]
      exact pow_le_pow_left₀ (normAt_nonneg _ _ _ _ |>.trans_eq ((hG' v).2 _)) (hN _ _) 2
  have hpos : ∀ v : InfinitePlace K, 0 < Formalism.HN.opNormAt b X b' X' v φ := fun v =>
    Formalism.HN.PlaceOperatorNorms.opNormAt_pos b X b' X' (fun v => (hG v).1) (fun v => (hG' v).1) v φ hφ
  have hs : ∑ σ : K →+* ℂ, Real.log (t σ) = 2 * ∑ v : InfinitePlace K, Real.log (t v.embedding) := by
    rw [← GlobalTheory.SlopeExt.sum_mk K fun v => Real.log (t v.embedding)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rcases InfinitePlace.embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h]
      have e : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ :=
        RingHom.ext fun x => by simp [ComplexEmbedding.conjugate_coe_eq]
      rw [e, htc σ]
  have hd : (Module.finrank ℚ K : ℝ) = 2 * Formalism.HN.nPl K := by
    have := GlobalTheory.SlopeExt.sum_mk K fun _ => (1 : ℝ)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Embeddings.card] at this
    rw [this]; rfl
  have hn : (0 : ℝ) < Formalism.HN.nPl K := by
    have : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.2 Module.finrank_pos
    linarith
  unfold Formalism.HN.htMap
  rw [hs, hd]
  have hsum : ∑ v, Real.log (Formalism.HN.opNormAt b X b' X' v φ ^ 2) ≤ ∑ v : InfinitePlace K, 2 * Real.log (t v.embedding) :=
    Finset.sum_le_sum fun v _ => by
      have := Real.log_le_log (pow_pos (hpos v) 2) (hop v)
      rw [Real.log_pow, Real.log_pow] at this
      rw [Real.log_pow]
      push_cast at this ⊢
      exact this
  rw [← Finset.mul_sum] at hsum
  rw [one_div, inv_mul_le_iff₀ hn]
  have : 2 * (2 * ∑ v : InfinitePlace K, Real.log (t v.embedding)) / (2 * (Formalism.HN.nPl K : ℝ)) * Formalism.HN.nPl K =
      2 * ∑ v : InfinitePlace K, Real.log (t v.embedding) := by
    field_simp
  linarith

end GlobalTheory.TwistIdeal

namespace GlobalTheory.TwistIdeal

theorem deg_add_le_deg_of_ideal_smul_le : ∀ (K V : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (W : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (N : (K →+* ℂ) → V → ℝ) (N' : (K →+* ℂ) → W → ℝ) (φ : V →ₗ[K] W) (t : (K →+* ℂ) → ℝ) (L : Submodule (𝓞 K) V) (L' : Submodule (𝓞 K) W) (𝔞 : Ideal (𝓞 K)), HasGram N → HasGram N' → Function.Injective φ → (∀ σ, 0 < t σ) → (∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) → (∀ σ x, N' σ (φ x) ≤ t σ * N σ x) → L.FG → L'.FG → 𝔞 ≠ ⊥ → 𝔞 • L.map (φ.restrictScalars (𝓞 K)) ≤ L' → Formalism.HN.rkK L' = Formalism.HN.rkK L → deg N L + (Formalism.HN.rkK L : ℝ) * (-((∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ)) - Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ)) ≤ deg N' L' := by
  intro K V _ _ _ _ _ _ _ W _ _ _ _ N N' φ t L L' 𝔞 hN hN' hinj htpos htc hNb hL hL' h𝔞 hsub hrk
  by_cases h0 : L = ⊥
  · subst h0
    have h1 : Formalism.HN.rkK (⊥ : Submodule (𝓞 K) V) = 0 := by simp [Formalism.HN.rkK]
    rw [h1] at hrk
    simp [deg, h1, hrk]
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := hN
  obtain ⟨⟨n', ⟨b', X'⟩, hG'⟩⟩ := hN'
  letI : StarRing K := starRingOfComm
  have hI : ((𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔞
  have hsm : Formalism.HermitianLatticesTheory.idealSmul (((𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) : Submodule (𝓞 K) K)
      (L.map (φ.restrictScalars (𝓞 K))) ≤ L' := by
    refine Submodule.span_le.2 ?_
    rintro z ⟨a, ha, x, hx, rfl⟩
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal (S := (nonZeroDivisors (𝓞 K))) (P := K)).1 ha
    rw [algebraMap_smul]
    exact hsub (Submodule.smul_mem_smul hr hx)
  have key := Formalism.ExtensionFiltration.twistLower K V (Fin n) W (Fin n') b X b' X' (fun v => (hG v).1) (fun v => (hG' v).1)
    φ L L' (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) hI hL hL' h0 hinj hsm hrk
  have hφ : φ ≠ 0 := by
    intro h
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    exact hx0 (hinj (by rw [h, map_zero, LinearMap.zero_apply]))
  have hht := htMap_le hG hG' φ hφ t htpos htc hNb
  rw [FractionalIdeal.coeIdeal_absNorm] at key
  have hb : slope_sq N L / 2 - (∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ) -
      Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ) ≤ slope_sq N' L' / 2 := by
    rw [slope_sq_eq hG hL, slope_sq_eq hG' hL']
    have e1 : 2 * (∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ) =
        2 * ((∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ)) := by ring
    have e2 : 2 * Real.log ((Ideal.absNorm 𝔞 : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ) =
        2 * (Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ)) := by push_cast; ring
    rw [e1] at hht
    rw [e2] at key
    linarith
  have hr : (0 : ℝ) ≤ Formalism.HN.rkK L := Nat.cast_nonneg _
  unfold deg GlobalTheory.AllWt.slope
  rw [hrk]
  nlinarith [mul_le_mul_of_nonneg_left hb hr]

end GlobalTheory.TwistIdeal
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

noncomputable section

namespace GlobalTheory.NormScale

theorem deg_scale : ∀ (K V : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N N' : (K →+* ℂ) → V → ℝ) (t : (K →+* ℂ) → ℝ), HasGram N → (∀ σ, 0 < t σ) → (∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) → (∀ σ x, N' σ x = t σ * N σ x) → HasGram N' ∧ ∀ L : Submodule (𝓞 K) V, L.FG → deg N' L = deg N L - (Formalism.HN.rkK L : ℝ) * ((∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ)) := by
  intro K V _ _ _ _ _ _ _ N N' t hN ht hc hN'
  letI : StarRing K := starRingOfComm
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := hN
  set X' : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ := fun v => ((t v.embedding : ℂ)⁻¹) • X v with hX'
  have htc : ∀ v : InfinitePlace K, (t v.embedding : ℂ) ≠ 0 := fun v => by
    exact_mod_cast (ht v.embedding).ne'
  have hinv : ∀ v, (X' v)⁻¹ = (t v.embedding : ℂ) • (X v)⁻¹ := fun v => by
    refine Matrix.inv_eq_left_inv ?_
    simp only [hX', Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.nonsing_inv_mul _ (hG v).1,
      inv_mul_cancel₀ (htc v), one_smul]
  have hfc : ∀ v x, Formalism.HermitianLatticesTheory.fcoord b X' v x = (t v.embedding : ℂ) • Formalism.HermitianLatticesTheory.fcoord b X v x := fun v x => by
    simp only [Formalism.HermitianLatticesTheory.fcoord, hinv]
    exact Matrix.smul_mulVec _ _ _
  have hnorm : ∀ v x, Formalism.HermitianLatticesTheory.normAt b X' v x = t v.embedding * Formalism.HermitianLatticesTheory.normAt b X v x := fun v x => by
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, hfc, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow,
      ← Finset.mul_sum]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (ht _)]
  have hG' : IsGram b X' N' := fun v => by
    refine ⟨?_, fun x => by rw [hnorm, (hG v).2, hN']⟩
    simp only [hX', Matrix.det_smul]
    exact (IsUnit.pow _ (isUnit_iff_ne_zero.2 (inv_ne_zero (htc v)))).mul (hG v).1
  refine ⟨hG'.hasGram, fun L hL => ?_⟩
  have hgram : ∀ v {j : ℕ} (e : Fin j → V), Formalism.HN.gramPl b X' v e = (((t v.embedding) ^ 2 : ℝ) : ℂ) • Formalism.HN.gramPl b X v e := by
    intro v j e
    ext a c
    simp only [Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, hfc, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, star_mul', Complex.star_def, Complex.conj_ofReal]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring
  have hdet : ∀ v {j : ℕ} (e : Fin j → V), (Formalism.HN.gramPl b X' v e).det.re =
      t v.embedding ^ (2 * j) * (Formalism.HN.gramPl b X v e).det.re := by
    intro v j e
    rw [hgram, Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul, ← pow_mul]
  haveI : Module.Finite K V := Module.Finite.of_basis b
  obtain ⟨e, heL, hsp, he⟩ := Submodule.exists_fun_fin_finrank_span_eq K (L : Set V)
  have hj : Formalism.HN.rkK L = Module.finrank K (Submodule.span K (L : Set V)) := rfl
  generalize Module.finrank K (Submodule.span K (L : Set V)) = j at e heL hsp he hj
  obtain ⟨-, g1, m1⟩ := GlobalTheory.SlopeExt.rk_mul_mu_eq b X (fun v => (hG v).1) e he L hL
    (Submodule.span_le.2 (Set.range_subset_iff.2 heL)) hj
  obtain ⟨-, g2, m2⟩ := GlobalTheory.SlopeExt.rk_mul_mu_eq b X' (fun v => (hG' v).1) e he L hL
    (Submodule.span_le.2 (Set.range_subset_iff.2 heL)) hj
  have hlog : ∀ v, Real.log (Formalism.HN.gramPl b X' v e).det.re =
      (2 * j : ℝ) * Real.log (t v.embedding) + Real.log (Formalism.HN.gramPl b X v e).det.re := fun v => by
    rw [hdet, Real.log_mul (pow_pos (ht _) _).ne' (g1 v).ne', Real.log_pow]
    push_cast; ring
  have hsum : ∑ σ : K →+* ℂ, Real.log (t σ) = 2 * ∑ v : InfinitePlace K, Real.log (t v.embedding) := by
    rw [← GlobalTheory.SlopeExt.sum_mk K (fun v => Real.log (t v.embedding))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rcases InfinitePlace.embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h]; exact congrArg Real.log (hc σ).symm
  have hfin : (Module.finrank ℚ K : ℝ) = 2 * Formalism.HN.nPl K := by
    have := GlobalTheory.SlopeExt.sum_mk K (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
    rw [← NumberField.Embeddings.card K ℂ, this]
    rfl
  have hP : (Formalism.HN.nPl K : ℝ) ≠ 0 := by exact_mod_cast Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.nPl_ne_zero
  rw [Finset.sum_congr rfl (fun v _ => hlog v), Finset.sum_add_distrib, ← Finset.mul_sum] at m2
  simp only [GlobalTheory.AllWt.deg, GlobalTheory.AllWt.slope, slope_sq_eq hG hL, slope_sq_eq hG' hL, hj, hsum, hfin]
  have key : (Formalism.HN.nPl K : ℝ) * ((j : ℝ) * Formalism.HN.muDef b X' L) = (Formalism.HN.nPl K : ℝ) * ((j : ℝ) * Formalism.HN.muDef b X L)
      - 2 * j * ∑ v : InfinitePlace K, Real.log (t v.embedding) := by linarith
  field_simp
  linear_combination key

end GlobalTheory.NormScale
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

noncomputable section

namespace GlobalTheory.OrthRankDeg

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]

theorem gram_zero [StarRing K] {n : ℕ} {b : Module.Basis (Fin n) K V}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} {N : (K →+* ℂ) → V → ℝ}
    (hG : GlobalTheory.AllWt.IsGram b X N) (v : InfinitePlace K) : N v.embedding 0 = 0 := by
  rw [← (hG v).2 0]
  simp [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Formalism.HermitianLatticesTheory.fcoord_zero]

theorem inner_realize_eq_zero [StarRing K] {n : ℕ} {b : Module.Basis (Fin n) K V}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} {N : (K →+* ℂ) → V → ℝ}
    (hG : GlobalTheory.AllWt.IsGram b X N) {x y : V}
    (h : ∀ v : InfinitePlace K, N v.embedding (x + y) ^ 2 = N v.embedding x ^ 2 + N v.embedding y ^ 2) :
    inner ℝ (Formalism.HermitianLatticesTheory.realize b X x) (Formalism.HermitianLatticesTheory.realize b X y) = 0 := by
  have hs : ∀ z, ‖Formalism.HermitianLatticesTheory.realize b X z‖ ^ 2 = ∑ v : InfinitePlace K, N v.embedding z ^ 2 := fun z => by
    rw [GlobalTheory.AllWt.norm_realize_sq]
    exact Finset.sum_congr rfl fun v _ => by rw [(hG v).2]
  have h1 := hs (x + y)
  rw [map_add (f := _), norm_add_sq_real, hs x, hs y] at h1
  rw [Finset.sum_congr rfl fun v _ => h v, Finset.sum_add_distrib] at h1
  linarith

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem inner_pair [StarRing K] {n : ℕ} {b : Module.Basis (Fin n) K V}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} {N : (K →+* ℂ) → V → ℝ}
    (hG : GlobalTheory.AllWt.IsGram b X N) {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → Submodule (𝓞 K) V)
    (hN : ∀ σ, ∀ f : ι → V, (∀ i, f i ∈ Submodule.span K (M i : Set V)) →
      N σ (∑ i, f i) ^ 2 = ∑ i, N σ (f i) ^ 2)
    {i j : ι} (hij : i ≠ j) {x y : V} (hx : x ∈ M i) (hy : y ∈ M j) :
    inner ℝ (Formalism.HermitianLatticesTheory.realize b X x) (Formalism.HermitianLatticesTheory.realize b X y) = 0 := by
  refine inner_realize_eq_zero hG fun v => ?_
  have hmem : ∀ (k : ι) (z : V) (_ : z ∈ M k) (l : ι),
      (Pi.single k z : ι → V) l ∈ Submodule.span K (M l : Set V) := by
    intro k z hz l
    by_cases hl : l = k
    · subst hl; simpa using Submodule.subset_span hz
    · simp [Pi.single_apply, hl]
  have h := hN v.embedding (Pi.single i x + Pi.single j y) fun l =>
    Submodule.add_mem _ (hmem i x hx l) (hmem j y hy l)
  have hsum : ∑ l, (Pi.single i x + Pi.single j y : ι → V) l = x + y := by
    simp [Finset.sum_add_distrib]
  have hpt : ∀ l, N v.embedding ((Pi.single i x + Pi.single j y : ι → V) l) ^ 2 =
      (Pi.single i (N v.embedding x ^ 2) : ι → ℝ) l + (Pi.single j (N v.embedding y ^ 2) : ι → ℝ) l := by
    intro l
    by_cases hli : l = i
    · subst hli; simp [Pi.single_apply, hij]
    · by_cases hlj : l = j
      · subst hlj; simp [Pi.single_apply, hli]
      · simp [Pi.single_apply, hli, hlj, gram_zero hG v]
  rw [hsum, Finset.sum_congr rfl fun l _ => hpt l, Finset.sum_add_distrib] at h
  simpa using h

theorem deg_eq [_root_.NumberField.IsTotallyComplex K] [StarRing K] {n : ℕ} {b : Module.Basis (Fin n) K V}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} {N : (K →+* ℂ) → V → ℝ}
    (hG : GlobalTheory.AllWt.IsGram b X N) (L : Submodule (𝓞 K) V) (hL : L.FG) :
    GlobalTheory.AllWt.deg N L = 1 / (Module.finrank ℚ K : ℝ) * Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize b X) L +
      (Formalism.HN.rkK L : ℝ) * ((-Real.log 2 + Formalism.HN.logDisc K / (Module.finrank ℚ K : ℝ)) / 2) := by
  have hX : ∀ v, IsUnit (X v).det := fun v => (hG v).1
  rw [GlobalTheory.AllWt.deg, GlobalTheory.AllWt.slope, GlobalTheory.AllWt.slope_sq_eq hG hL]
  by_cases h0 : L = ⊥
  · subst h0
    simp [Formalism.BranchingDeterminantCap.OrthogonalSumAlt.rkK_bot, Formalism.BranchingDeterminantCap.OrthogonalSumAlt.deg_bot b X hX]
  · have hr : Formalism.HN.rkK L ≠ 0 := fun h => h0 (Formalism.BranchingDeterminantCap.OrthogonalSumAlt.eq_bot_of_rkK b h)
    have hrk := (Formalism.HN.plLat K V (Fin n) b X hX L hL).2.1
    have hs : Formalism.HN.slope (Formalism.HermitianLatticesTheory.realize b X) L =
        Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize b X) L / (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) L : ℝ) := rfl
    have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := by
      exact_mod_cast (Formalism.BranchingDeterminantCap.OrthogonalSumAlt.finrank_pos' (K := K)).ne'
    have hr' : (Formalism.HN.rkK L : ℝ) ≠ 0 := by exact_mod_cast hr
    rw [Formalism.HN.muDef, hs, hrk]
    push_cast
    field_simp
    ring

end GlobalTheory.OrthRankDeg

namespace GlobalTheory.OrthRankDeg

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem sum_finset [_root_.NumberField.IsTotallyComplex K] [StarRing K] {n : ℕ} {b : Module.Basis (Fin n) K V}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} {N : (K →+* ℂ) → V → ℝ}
    (hG : GlobalTheory.AllWt.IsGram b X N) {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → Submodule (𝓞 K) V)
    (hM : ∀ i, (M i).FG)
    (hN : ∀ σ, ∀ f : ι → V, (∀ i, f i ∈ Submodule.span K (M i : Set V)) →
      N σ (∑ i, f i) ^ 2 = ∑ i, N σ (f i) ^ 2) (s : Finset ι) :
    (⨆ i ∈ s, M i).FG ∧ Formalism.HN.rkK (⨆ i ∈ s, M i) = ∑ i ∈ s, Formalism.HN.rkK (M i) ∧
      Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize b X) (⨆ i ∈ s, M i) =
        ∑ i ∈ s, Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize b X) (M i) := by
  have hX : ∀ v, IsUnit (X v).det := fun v => (hG v).1
  induction s using Finset.induction_on with
  | empty =>
    simp [Formalism.BranchingDeterminantCap.OrthogonalSumAlt.rkK_bot, Formalism.BranchingDeterminantCap.OrthogonalSumAlt.deg_bot b X hX, Submodule.fg_bot]
  | insert a s ha ih =>
    obtain ⟨ihfg, ihrk, ihdeg⟩ := ih
    rw [Finset.iSup_insert]
    set B := ⨆ i ∈ s, M i with hB
    have ho : ∀ x ∈ M a, ∀ y ∈ B,
        inner ℝ (Formalism.HermitianLatticesTheory.realize b X x) (Formalism.HermitianLatticesTheory.realize b X y) = 0 := by
      intro x hx y hy
      obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum M y).1 hy

      rw [← hμ, map_sum, inner_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      exact inner_pair hG M hN (by rintro rfl; exact ha hi) hx (μ i).2
    have hlA := (Formalism.HN.plLat K V (Fin n) b X hX (M a) (hM a)).1
    have hlB := (Formalism.HN.plLat K V (Fin n) b X hX B ihfg).1
    obtain ⟨hl, hdeg, -⟩ :=
      (Formalism.HN.hnSum.{0, 0, 0, 0} (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X)).2 (M a) B hlA hlB ho
    have hfg : (M a ⊔ B).FG := (hM a).sup ihfg
    have hinf : M a ⊓ B = ⊥ := by
      refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
      have h1 := ho x hx.1 x hx.2
      rw [inner_self_eq_zero] at h1
      exact Formalism.HN.HeightGram.realize_injective b X hX (by rw [h1, map_zero])
    have hrk := (Formalism.HN.degSupermod (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) (M a ⊔ B) (M a) B hl
      le_sup_left le_sup_right).1
    rw [hinf, (Formalism.HN.plLat K V (Fin n) b X hX _ hfg).2.1, (Formalism.HN.plLat K V (Fin n) b X hX _ (hM a)).2.1,
      (Formalism.HN.plLat K V (Fin n) b X hX _ ihfg).2.1,
      (Formalism.HN.plLat K V (Fin n) b X hX _ Submodule.fg_bot).2.1, Formalism.BranchingDeterminantCap.OrthogonalSumAlt.rkK_bot, mul_zero, add_zero,
      ← mul_add] at hrk
    have hrk' := Nat.eq_of_mul_eq_mul_left (Formalism.BranchingDeterminantCap.OrthogonalSumAlt.finrank_pos' (K := K)) hrk
    refine ⟨hfg, ?_, ?_⟩
    · rw [hrk', Finset.sum_insert ha, ihrk]
    · rw [hdeg, Finset.sum_insert ha, ihdeg]

theorem rkK_deg_iSup : ∀ (K V : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (ι : Type) [Fintype ι] (N : (K →+* ℂ) → V → ℝ)
    (M : ι → Submodule (𝓞 K) V), HasGram N → (∀ i, (M i).FG) →
    (∀ σ, ∀ f : ι → V, (∀ i, f i ∈ Submodule.span K (M i : Set V)) → N σ (∑ i, f i) ^ 2 = ∑ i, N σ (f i) ^ 2) →
    Formalism.HN.rkK (⨆ i, M i) = ∑ i, Formalism.HN.rkK (M i) ∧ deg N (⨆ i, M i) = ∑ i, deg N (M i) := by
  intro K V _ _ _ _ _ _ _ ι _ N M hG hM hN
  classical
  letI : StarRing K := starRingOfComm
  obtain ⟨⟨n, ⟨⟨b, X⟩, hbX⟩⟩⟩ := hG
  obtain ⟨hfg, hrk, hdeg⟩ := sum_finset hbX M hM hN Finset.univ
  have hu : (⨆ i ∈ (Finset.univ : Finset ι), M i) = ⨆ i, M i := by simp
  rw [hu] at hfg hrk hdeg
  refine ⟨hrk, ?_⟩
  rw [deg_eq hbX _ hfg, hdeg, hrk, Finset.mul_sum]
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => (deg_eq hbX _ (hM i)).symm

end GlobalTheory.OrthRankDeg
end
end

section

open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc

theorem _root_.GlobalTheory.T.irreducible_pencilLinePolynomial_generic_line : ∀ (F : Type) [Field F] (D N : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F), Irreducible f → Irreducible (GlobalTheory.PencilDisc.line (fun i j => (MvPolynomial.X (Sum.inl (i, j)) : MvPolynomial ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) F)) (fun j => MvPolynomial.X (Sum.inr (Sum.inl j))) (fun j => MvPolynomial.X (Sum.inr (Sum.inr j))) f) := by
  first | exact @GlobalTheory.PencilDisc.irreducible_line_generic | exact GlobalTheory.PencilDisc.irreducible_line_generic | (intros; apply GlobalTheory.PencilDisc.irreducible_line_generic <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc

theorem _root_.GlobalTheory.T.totalDegree_pencilLineDiscriminant_le : ∀ (F : Type) [Field F] (D N δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F), IsMultiHomogeneous (fun _ => δ) f → ∀ ξ₀ ξ₁ : Fin N → F, (GlobalTheory.PencilDisc.disc δ (fun i j => (MvPolynomial.X (i, j) : MvPolynomial (Fin D × Fin N) F)) (fun j => MvPolynomial.C (ξ₀ j)) (fun j => MvPolynomial.C (ξ₁ j)) f).totalDegree ≤ 2 * D * δ ^ 2 := by
  first | exact @GlobalTheory.PencilDiscDeg.totalDegree_disc_le | exact GlobalTheory.PencilDiscDeg.totalDegree_disc_le | (intros; apply GlobalTheory.PencilDiscDeg.totalDegree_disc_le <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc

theorem _root_.GlobalTheory.T.not_square_linear_factor_of_pencilLineDiscriminant_ne_zero : ∀ (F K : Type) [Field F] [Field K] [Algebra F K] (D N δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F) (s : Fin D → Fin N → K) (a b : Fin N → K), 1 ≤ δ → (GlobalTheory.PencilDisc.line s a b f).natDegree ≤ δ → (GlobalTheory.PencilDisc.line s a b f).coeff δ = MvPolynomial.aeval (GlobalTheory.HSChoice.join s b) f → GlobalTheory.PencilDisc.disc δ s a b f ≠ 0 → GlobalTheory.HSChoice.NoSquare (GlobalTheory.HSChoice.spec s f) := by
  first | exact @GlobalTheory.PencilDisc.noSquare_spec_of_disc_ne_zero | exact GlobalTheory.PencilDisc.noSquare_spec_of_disc_ne_zero | (intros; apply GlobalTheory.PencilDisc.noSquare_spec_of_disc_ne_zero <;> assumption)
end
