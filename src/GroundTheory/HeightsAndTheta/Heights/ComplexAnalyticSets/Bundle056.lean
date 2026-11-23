module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle043
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle034
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle046
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle032
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle045
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle035
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
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
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

theorem zeroSetIn_isAnalyticNear {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) :
    IsAnalyticNear (zeroSetIn I) w := by
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
  refine ⟨Set.univ, s.card, fun i z => eval z (s.equivFin.symm i : MvPolynomial σ ℂ), isOpen_univ, trivial,
    fun i => AnalyticOnNhd.eval_mvPolynomial _, ?_⟩
  ext z
  simp only [Set.mem_inter_iff, Set.mem_univ, and_true, Set.mem_ofPred_eq, true_and]
  constructor
  · intro hz i
    apply hz
    rw [← hs]
    exact Submodule.subset_span (s.equivFin.symm i).2
  · intro hz q hq
    have hle : Ideal.span (s : Set (MvPolynomial σ ℂ)) ≤ RingHom.ker (MvPolynomial.eval z) := by
      rw [Ideal.span_le]
      intro p hp
      rw [SetLike.mem_coe, RingHom.mem_ker]
      simpa using hz (s.equivFin ⟨p, hp⟩)
    rw [← hs] at hq
    exact hle hq

theorem NormalComplementConnected.proof (hvan : VanishNearPoint.Statement)
    (hgerm : NormalGermIrreducible.Statement) (hconn : IrreducibleGermComplementConnected.Statement) :
    NormalComplementConnected.Statement := by
  intro σ _ I h w hI hnorm hh hw U hU
  have hne : ¬ ∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → eval z h = 0 := by
    intro hev
    have hcl := zeroSetIn_subset_closure_diff hvan I h hI hh hw
    rw [mem_closure_iff_nhds] at hcl
    obtain ⟨z, hzt, hzZ, hzh⟩ := hcl _ hev
    exact hzh (hzt hzZ)
  exact hconn σ (zeroSetIn I) w (fun z => eval z h) (zeroSetIn_isAnalyticNear I w)
    (hgerm σ I w hI hnorm hw) (AnalyticOnNhd.eval_mvPolynomial h w trivial) hne U hU

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets Filter Topology

noncomputable section

theorem anForm_maDens_eq_geo_maDensity {D : ℕ} (φ : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    ReciprocityTheory.AnForm.maDens φ z = ReciprocityTheory.ChartRestriction.G.Geo.maDensity φ z :=
  rfl

theorem maDens_log_dualNorm_sheet {n e : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (ℓ : Fin n → ℂ) (A : Matrix (Fin e) (Fin n) ℂ) (y : Fin e → ℂ) (x : Fin n → ℂ)
    (s : (Fin e → ℂ) → Fin n → ℂ) (hx : x ∈ fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y)
    (hs : IsSheetAt (J ⊔ Ideal.span {linForm ℓ - 1}) A x s) :
    ReciprocityTheory.AnForm.maDens (fun k => (fun (_ : Fin e) x => Real.log (h.dualNorm x)) k ∘ s) y =
      (e.factorial : ℝ) / Real.pi ^ e * gramVol (fun y' => (h.matᵀ)⁻¹ *ᵥ s y') y /
        h.dualNorm x ^ (2 * (e + 1)) := by
  obtain ⟨U, hU, hyU, hdiff, hsx, -, -⟩ := hs
  obtain ⟨hxZ, rfl⟩ := hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    have h1 : eval (0 : Fin n → ℂ) (linForm ℓ - 1) = 0 :=
      hxZ _ (Ideal.mem_sup_right (Ideal.subset_span rfl))

    rw [map_sub, map_one, linForm, map_sum] at h1
    simp at h1
  have hdual : ∀ z, h.dualNorm z = ‖WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ z)‖ := fun z => by
    simp [HermNorm.dualNorm, EuclideanSpace.norm_eq]
  have hv : ∀ᶠ y' in 𝓝 (A *ᵥ x), DifferentiableAt ℂ (fun y' => (h.matᵀ)⁻¹ *ᵥ s y') y' := by
    filter_upwards [hU.mem_nhds hyU] with y' hy'
    have hs' := (hdiff y' hy').differentiableAt (hU.mem_nhds hy')
    exact (LinearMap.toContinuousLinearMap (Matrix.mulVecLin (h.matᵀ)⁻¹)).differentiableAt.comp y' hs'
  have hne : (fun y' => (h.matᵀ)⁻¹ *ᵥ s y') (A *ᵥ x) ≠ 0 := by
    intro h0
    have hpos := HermNorm.dualNorm_pos h hx0
    rw [hdual, ← hsx, show (h.matᵀ)⁻¹ *ᵥ s (A *ᵥ x) = 0 from h0] at hpos
    simp at hpos
  have key := ChartGramMA.proof e n _ _ hv hne
  have hF : (fun k : Fin e => (fun (_ : Fin e) x => Real.log (h.dualNorm x)) k ∘ s) =
      fun _ y' => Real.log ‖WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ s y')‖ := by
    funext k y'
    simp only [Function.comp_apply, hdual]
  rw [hF, anForm_maDens_eq_geo_maDensity, key, hsx, ← hdual]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets Metric

noncomputable section

theorem primeTube_isClosed_zeroSet {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroSet J) := by
  have : zeroSet J = ⋂ q ∈ J, {x : Fin n → ℂ | eval x q = 0} := by ext x; simp [zeroSet]
  rw [this]
  exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const

theorem primeTube_isClosed_zeroSetEuc {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) :
    IsClosed (zeroSetEuc J) := by
  have : zeroSetEuc J = ⋂ q ∈ J, {z : EuclideanSpace ℂ (Fin n) | eval (fun i => z i) q = 0} := by
    ext z; simp [zeroSetEuc]
  rw [this]
  exact isClosed_biInter fun q _ =>
    isClosed_eq ((MvPolynomial.continuous_eval q).comp (PiLp.continuous_ofLp 2 _)) continuous_const

theorem primeTube_exists_dim {n k : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : J.IsPrime)
    (hk : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (k : ℕ)) :
    ∃ d : ℕ, d ≤ k ∧ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d : ℕ) := by
  have hnn : 0 ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) := ringKrullDim_nonneg_of_nontrivial
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = x at hnn hk ⊢
  induction x using WithBot.recBotCoe with
  | bot => simp at hnn
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      rw [← WithBot.coe_natCast] at hk
      exact absurd (WithBot.coe_le_coe.1 hk) (by simp)
    | coe m => exact ⟨m, by exact_mod_cast hk, by norm_cast⟩

theorem primeTube_exact (hL : VarietyMassLower.Statement) (hM : MassFinite.Statement) {n d : ℕ}
    {J : Ideal (MvPolynomial (Fin n) ℂ)} {K : Set (Fin n → ℂ)} (hJ : J.IsPrime)
    (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d : ℕ)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Ioc (0 : ℝ) 1,
      volume (thickening r (zeroSet J ∩ K)) ≤ ENNReal.ofReal (C * r ^ ((2 * n : ℤ) - 2 * d)) := by
  set e : (Fin n → ℂ) → EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 with he_def
  have hdist : ∀ x y : Fin n → ℂ, dist x y ≤ dist (e x) (e y) := fun x y =>
    by simpa [he_def] using (PiLp.lipschitzWith_ofLp 2 (fun _ : Fin n => ℂ)).dist_le_mul (e x) (e y)
  obtain ⟨R, hR⟩ := ((hK.image (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ))).isBounded).exists_norm_le
  have hRK : ∀ x ∈ K, ‖e x‖ ≤ R := fun x hx => hR _ ⟨x, hx, rfl⟩
  obtain ⟨c, hc0, hc⟩ := hL n d J hJ hd R
  set M : ENNReal := μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ ball (0 : EuclideanSpace ℂ (Fin n)) (R + 1))
  have hMfin : M ≠ ⊤ := (hM n d J hJ hd (R + 1)).ne
  refine ⟨M.toReal * 4 ^ d * (4 * Real.pi) ^ n / c, by positivity, fun r hr => ?_⟩
  obtain ⟨hr0, hr1⟩ := hr
  set S := zeroSet J ∩ K
  have hS : IsCompact S := hK.inter_left (primeTube_isClosed_zeroSet J)

  set δ : NNReal := (r / 2).toNNReal
  have hδ : ((2 * δ : NNReal) : ℝ) = r := by
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity)]; push_cast; ring
  have hpack : packingNumber (2 * δ) S ≠ ⊤ := by
    obtain ⟨N, -, hNfin, hN⟩ := exists_finite_isCover_of_isCompact (ε := δ)
      (by rw [ne_eq, ← NNReal.coe_eq_zero, Real.coe_toNNReal _ (by positivity)]; exact (by positivity : r / 2 ≠ 0)) hS
    exact ne_top_of_le_ne_top (Set.encard_ne_top_iff.2 hNfin)
      ((packingNumber_two_mul_le_externalCoveringNumber δ S).trans hN.externalCoveringNumber_le_encard)
  set T0 := maximalSeparatedSet (2 * δ) S
  have hTfin : T0.Finite :=
    Set.encard_ne_top_iff.1 (by rw [encard_maximalSeparatedSet hpack]; exact hpack)
  set T := hTfin.toFinset
  have hTS : ∀ t ∈ T, t ∈ S := fun t ht => maximalSeparatedSet_subset (by simpa [T] using ht)

  have hcov : thickening r S ⊆ ⋃ t ∈ T, ball t (2 * r) := by
    intro p hp
    obtain ⟨s, hs, hps⟩ := mem_thickening_iff.1 hp
    have hs' := (isCover_maximalSeparatedSet hpack).subset_iUnion_closedBall hs
    obtain ⟨t, ht, hst⟩ := Set.mem_iUnion₂.1 hs'
    rw [mem_closedBall, hδ] at hst
    refine Set.mem_iUnion₂.2 ⟨t, by simpa [T] using ht, ?_⟩
    rw [mem_ball]
    linarith [dist_triangle p s t]
  have hvol : volume (thickening r S) ≤ ENNReal.ofReal ((T.card : ℝ) * (Real.pi * (2 * r) ^ 2) ^ n) := by
    refine (measure_mono hcov).trans ((measure_biUnion_finset_le T _).trans (le_of_eq ?_))
    simp only [volume_ball_pi_complex _ (by positivity : (0 : ℝ) < 2 * r), Finset.sum_const, nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]

  have hsep := isSeparated_maximalSeparatedSet (ε := 2 * δ) (A := S)
  have hdisj : (↑T : Set (Fin n → ℂ)).PairwiseDisjoint (fun t => zeroSetEuc J ∩ ball (e t) (r / 2)) := by
    intro x hx y hy hxy
    refine Set.disjoint_left.2 fun z hzx hzy => ?_
    have h1 : ((2 * δ : NNReal) : ENNReal) < edist x y := hsep (by simpa [T] using hx) (by simpa [T] using hy) hxy
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity), hδ] at h1
    have h2 := dist_triangle_left (e x) (e y) z
    simp only [Set.mem_inter_iff, mem_ball] at hzx hzy
    linarith [hdist x y, hzx.2, hzy.2]
  have hsub : (⋃ t ∈ T, zeroSetEuc J ∩ ball (e t) (r / 2)) ⊆
      zeroSetEuc J ∩ ball (0 : EuclideanSpace ℂ (Fin n)) (R + 1) := by
    refine Set.iUnion₂_subset fun t ht => fun z ⟨hz, hzt⟩ => ⟨hz, ?_⟩
    rw [mem_ball_zero_iff]
    rw [mem_ball, dist_eq_norm] at hzt
    have := hRK t (hTS t ht).2
    have := norm_le_norm_add_norm_sub' z (e t)
    linarith
  have hmass : (T.card : ENNReal) * ENNReal.ofReal (c * (r / 2) ^ (2 * d)) ≤ M := by
    refine le_trans ?_ (measure_mono hsub)
    rw [measure_biUnion_finset hdisj fun t _ =>
      (primeTube_isClosed_zeroSetEuc J).measurableSet.inter measurableSet_ball]
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun t ht => hc (e t) ?_ (hRK t (hTS t ht).2) (r / 2) ⟨by positivity, by linarith⟩
    have htZ := (hTS t ht).1
    intro q hq
    simpa [he_def] using htZ q hq
  have hcount : (T.card : ℝ) * (c * (r / 2) ^ (2 * d)) ≤ M.toReal := by
    have := ENNReal.toReal_mono hMfin hmass
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity)] at this

  refine hvol.trans (ENNReal.ofReal_le_ofReal ?_)
  set Y : ℝ := r ^ ((2 * n : ℤ) - 2 * d)
  have hY : Y * r ^ (2 * d) = r ^ (2 * n) := by
    simp only [Y]
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hr0.ne']
    congr 1; push_cast; ring
  have h4 : (r / 2) ^ (2 * d) * 4 ^ d = r ^ (2 * d) := by
    rw [div_pow, pow_mul, pow_mul]; field_simp; norm_num
  have hX : (T.card : ℝ) * (Real.pi * (2 * r) ^ 2) ^ n =
      (T.card : ℝ) * (c * (r / 2) ^ (2 * d)) * ((4 : ℝ) ^ d * (4 * Real.pi) ^ n * Y / c) := by
    rw [← h4] at hY
    have hX' : (Real.pi * (2 * r) ^ 2) ^ n = (4 * Real.pi) ^ n * r ^ (2 * n) := by
      rw [pow_mul, ← mul_pow]; ring
    rw [hX', ← hY]
    field_simp
  rw [hX]
  calc (T.card : ℝ) * (c * (r / 2) ^ (2 * d)) * ((4 : ℝ) ^ d * (4 * Real.pi) ^ n * Y / c)
      ≤ M.toReal * ((4 : ℝ) ^ d * (4 * Real.pi) ^ n * Y / c) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = M.toReal * 4 ^ d * (4 * Real.pi) ^ n / c * Y := by ring

theorem PrimeTubeVolume.proof (hL : VarietyMassLower.Statement) (hM : MassFinite.Statement) :
    PrimeTubeVolume.Statement := by
  intro n k J K hJ hk hK
  obtain ⟨d, hdk, hd⟩ := primeTube_exists_dim hJ hk
  obtain ⟨C, hC, hCr⟩ := primeTube_exact hL hM hJ hd hK
  refine ⟨C, hC, fun r hr => (hCr r hr).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hC))⟩
  exact zpow_le_zpow_right_of_le_one₀ hr.1 hr.2 (by omega)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

theorem isRadicalAt_of_associatedPrimes {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (hA : ∀ P ∈ associatedPrimes (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I),
      P ≤ RingHom.ker (eval q) → P ∈ I.minimalPrimes ∧ P ≠ RingHom.ker (eval q))
    (hB : ∀ P : Ideal (MvPolynomial (Fin n) ℂ), P.IsPrime → I ≤ P → P ≠ RingHom.ker (eval q) →
      ∀ g ∈ I.radical, ∃ s ∉ P, s * g ∈ I) :
    IsRadicalAt I q := by
  intro g hg
  by_contra hno
  simp only [not_exists, not_and] at hno
  have : (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime := RingHom.ker_isPrime _
  set N : Submodule (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) :=
    Submodule.span _ {Ideal.Quotient.mk I g}
  have hK : ∀ s, s ∈ Module.annihilator (MvPolynomial (Fin n) ℂ) N ↔ s * g ∈ I := by
    intro s
    change s ∈ N.annihilator ↔ _
    rw [Submodule.mem_annihilator_span_singleton]
    change Ideal.Quotient.mk I s * Ideal.Quotient.mk I g = 0 ↔ _
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  have hKq : Module.annihilator (MvPolynomial (Fin n) ℂ) N ≤ RingHom.ker (eval q) := by
    intro s hs
    by_contra h
    exact hno s h ((hK s).1 hs)
  obtain ⟨P, hPmin, hPq⟩ := Ideal.exists_minimalPrimes_le hKq
  have hPass : P ∈ associatedPrimes (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) :=
    associatedPrimes.subset_of_injective (f := N.subtype) Subtype.val_injective
      (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes _ _ hPmin)
  obtain ⟨hPI, hPne⟩ := hA P hPass hPq
  obtain ⟨s, hsP, hsg⟩ := hB P hPI.1.1 hPI.1.2 hPne g hg
  exact hsP (hPmin.1.2 ((hK s).2 hsg))

theorem SliceReducedGeneral.proof (hU : SliceUnmixedGeneral.Statement)
    (hB : SliceReducedAway.Statement) : SliceReducedGeneral.Statement := by
  intro n d J W u hJ hdim hu hW
  obtain ⟨f, hfW, hf⟩ := hU n d J W u hJ hdim hu hW
  refine ⟨f, hfW, fun q hq hfq => ?_⟩
  obtain ⟨O₁, hO₁o, hO₁d, hO₁⟩ := hf q hq hfq
  obtain ⟨O₂, hO₂o, hO₂d, hO₂⟩ := hB n d J q hJ.isRadical
  exact ⟨O₁ ∩ O₂, hO₁o.inter hO₂o, hO₁d.inter_of_isOpen_left hO₂d hO₁o,
    fun L hL => isRadicalAt_of_associatedPrimes (hO₁ L hL.1) (hO₂ L hL.2)⟩

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory
open scoped ENNReal

noncomputable section

theorem VarietyMassLower.proof (hG : VarietyTangentGraphDense.Statement)
    (hL : TangentGraphLowerDensity.Statement) (hM : VarietyLelongMono.Statement) :
    VarietyMassLower.Statement := by
  intro n d J hJ hd R
  set τ := μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) with hτdef
  have hτ : 0 < τ := TangentGraphLowerDensity.unitBall_pos d
  set m : ℝ≥0∞ := min τ 1 with hmdef
  have hm0 : 0 < m := lt_min hτ one_pos
  have hmtop : m ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hmτ : m ≤ τ := min_le_left _ _
  have hmr : 0 < m.toReal := ENNReal.toReal_pos hm0.ne' hmtop
  refine ⟨(1 / 2) * (1 / 2) ^ (2 * d) * m.toReal, by positivity, fun z hz _ ρ hρ => ?_⟩
  obtain ⟨hρ0, -⟩ := hρ
  obtain ⟨b, I₀, Ω, V, g, w₀, hcard, hΩ, hV, hw₀, hg, hproj, hZV, htan, hdist⟩ :=
    hG n d J hJ hd z hz (ρ / 2) (by linarith)
  have hz₀ : g w₀ ∈ zeroSetEuc J := by
    have h : g w₀ ∈ g '' Ω := ⟨w₀, hw₀, rfl⟩
    rw [← hZV] at h
    exact h.1
  obtain ⟨r₀, hr₀, hlow⟩ := hL n d b I₀ (zeroSetEuc J) Ω V g w₀ hcard hΩ hV hw₀ hg hproj hZV htan
    (1 / 2) ⟨by norm_num, by norm_num⟩
  set t := min (r₀ / 2) (ρ / 2) with htdef
  have ht0 : 0 < t := lt_min (by linarith) (by linarith)
  have htr : t < r₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hts : t ≤ ρ / 2 := min_le_right _ _
  have h1 := hlow t ⟨ht0, htr⟩
  have h2 := hM n d J hJ hd (g w₀) hz₀ t (ρ / 2) ht0 hts
  have hsub : zeroSetEuc J ∩ Metric.ball (g w₀) (ρ / 2) ⊆ zeroSetEuc J ∩ Metric.ball z ρ :=
    Set.inter_subset_inter_right _ (Metric.ball_subset_ball' (by linarith))
  have h3 := measure_mono (μ := μH[((2 * d : ℕ) : ℝ)]) hsub
  have key : ENNReal.ofReal (t ^ (2 * d)) * (ENNReal.ofReal ((1 / 2) * (ρ / 2) ^ (2 * d)) * τ) ≤
      ENNReal.ofReal (t ^ (2 * d)) * μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball (g w₀) (ρ / 2)) := by
    calc ENNReal.ofReal (t ^ (2 * d)) * (ENNReal.ofReal ((1 / 2) * (ρ / 2) ^ (2 * d)) * τ)
        = ENNReal.ofReal ((ρ / 2) ^ (2 * d)) * (ENNReal.ofReal ((1 / 2) * t ^ (2 * d)) * τ) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
          ring
      _ ≤ ENNReal.ofReal ((ρ / 2) ^ (2 * d)) *
            μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball (g w₀) t) := by gcongr
      _ ≤ _ := h2
  have key' := (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 (pow_pos ht0 _)).ne'
    ENNReal.ofReal_ne_top).1 key
  have hc : (1 / 2) * (1 / 2) ^ (2 * d) * m.toReal * ρ ^ (2 * d) =
      ((1 / 2) * (ρ / 2) ^ (2 * d)) * m.toReal := by
    rw [div_pow, div_pow, one_pow]
    ring
  calc ENNReal.ofReal ((1 / 2) * (1 / 2) ^ (2 * d) * m.toReal * ρ ^ (2 * d))
      = ENNReal.ofReal ((1 / 2) * (ρ / 2) ^ (2 * d)) * m := by
        rw [hc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hmtop]
    _ ≤ ENNReal.ofReal ((1 / 2) * (ρ / 2) ^ (2 * d)) * τ := by gcongr
    _ ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball (g w₀) (ρ / 2)) := key'
    _ ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball z ρ) := h3

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology

open scoped ENNReal NNReal

theorem AreaGraph.proof (h : AreaGraphBound.Statement) : AreaGraph.Statement := by
  intro k m U F hU hF A hAU hA

  change μH[(k : ℝ)] (realGraphPt F '' A) =
    ∫⁻ x in A, ENNReal.ofReal (graphJac (fderiv ℝ F x :
      EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) ∂(μH[(k : ℝ)])
  set S := μH[(k : ℝ)] (realGraphPt F '' A)
  set I := ∫⁻ x in A, ENNReal.ofReal (graphJac (fderiv ℝ F x :
      EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) ∂(μH[(k : ℝ)])

  have hplus : ∀ j : ℕ,
      Tendsto (fun δ : ℝ≥0 => ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ j) (𝓝[>] 0) (𝓝 1) := by
    intro j
    have hcont : Continuous (fun δ : ℝ≥0 => ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ j) :=
      (ENNReal.continuous_pow j).comp (ENNReal.continuous_coe.comp (continuous_const.add continuous_id))
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hminus : ∀ j : ℕ,
      Tendsto (fun δ : ℝ≥0 => ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ j) (𝓝[>] 0) (𝓝 1) := by
    intro j
    have hcont : Continuous (fun δ : ℝ≥0 => ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ j) :=
      (ENNReal.continuous_pow j).comp (ENNReal.continuous_coe.comp (continuous_const.sub continuous_id))
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds

  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0), 0 < δ ∧ δ < 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ≥0) < 1 from one_pos)] with δ hδ
    exact hδ
  have hb : ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0),
      S ≤ ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ (k + 1) * I ∧
        ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k * I ≤ ((1 + δ : ℝ≥0) : ℝ≥0∞) * S := by
    filter_upwards [hev] with δ hδ
    exact h k m U F hU hF A hAU hA δ hδ.1 hδ.2
  apply le_antisymm
  · have hlim := ENNReal.Tendsto.mul_const (hplus (k + 1)) (b := I) (Or.inl one_ne_zero)
    rw [one_mul] at hlim
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim (hb.mono fun δ hδ => hδ.1)
  · have hlim₁ := ENNReal.Tendsto.mul_const (hminus k) (b := I) (Or.inl one_ne_zero)
    have hlim₂ := ENNReal.Tendsto.mul_const (by simpa using hplus 1) (b := S) (Or.inl one_ne_zero)
    rw [one_mul] at hlim₁ hlim₂
    exact le_of_tendsto_of_tendsto hlim₁ hlim₂ (hb.mono fun δ hδ => hδ.2)

end GroundTheory.Heights₂.Heights
end
