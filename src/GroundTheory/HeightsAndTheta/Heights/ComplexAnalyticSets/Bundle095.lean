module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle049
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle051
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle059
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeFormCompare
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle062
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle064
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle063
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle077
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle065
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle046
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle083
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder

noncomputable section

namespace SheetComassAlt

theorem sheetJac_eq_norm_det {n d : ℕ} (s : (Fin d → ℂ) → Fin n → ℂ) (y : Fin d → ℂ)
    (hs : DifferentiableAt ℂ s y) :
    sheetJac s y = ‖((ReciprocityTheory.AnForm.A.jacC s y)ᴴ * ReciprocityTheory.AnForm.A.jacC s y).det‖ := by
  set S : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm.toLinearMap ∘ₗ
      ((fderiv ℂ s y : (Fin d → ℂ) →L[ℂ] (Fin n → ℂ)) : (Fin d → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ
        (WithLp.linearEquiv 2 ℂ (Fin d → ℂ)).toLinearMap with hS
  have hR : fderiv ℝ s y = (fderiv ℂ s y).restrictScalars ℝ := hs.fderiv_restrictScalars ℝ
  have e : (WithLp.linearEquiv 2 ℝ (Fin n → ℂ)).symm.toLinearMap ∘ₗ
      ((fderiv ℝ s y : (Fin d → ℂ) →L[ℝ] (Fin n → ℂ)) : (Fin d → ℂ) →ₗ[ℝ] (Fin n → ℂ)) ∘ₗ
        (WithLp.linearEquiv 2 ℝ (Fin d → ℂ)).toLinearMap = S.restrictScalars ℝ := by
    ext v : 1
    simp [hS, hR]
  rw [sheetJac, e, FrameJacobianSumAlt.areaJacobian_restrictScalars,
    FrameJacobianSumAlt.det_adjoint_comp]
  congr 2
  ext i j
  simp [hS, Matrix.mul_apply, ReciprocityTheory.AnForm.A.jacC, PiLp.inner_apply, mul_comm]

end SheetComassAlt

theorem SheetComass.proof : SheetComass.Statement := by
  intro n d J A φ R hφ
  choose U hUo hZU hφU using hφ
  have hK : IsCompact (zeroSet J ∩ Metric.closedBall (0 : Fin n → ℂ) R) :=
    (isCompact_closedBall (0 : Fin n → ℂ) R).inter_left (SheetSumMeasurable.isClosed_zeroSet J)
  obtain ⟨c, hc, hb⟩ := TubeFormComparison.exists_hessC_bound φ _ hK U hUo
    (fun i => Set.inter_subset_left.trans (hZU i))
    (fun i => (hφU i).of_le (WithTop.coe_le_coe.2 le_top))
  refine ⟨(d.factorial : ℝ) * (2 / Real.pi) ^ d * (3 ^ d * c ^ d), fun x hx s hs => ?_⟩
  obtain ⟨V, hV, hyV, hsd, hsx, -, -⟩ := hs
  have hsa : AnalyticAt ℂ s (A *ᵥ x) :=
    IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn hV hsd _ hyV
  have hφx : ∀ i, ContDiffAt ℝ 2 (φ i) (s (A *ᵥ x)) := fun i => by
    rw [hsx]
    exact ((hφU i).contDiffAt ((hUo i).mem_nhds (hZU i hx.1))).of_le (WithTop.coe_le_coe.2 le_top)
  set Jc := ReciprocityTheory.AnForm.A.jacC s (A *ᵥ x) with hJc
  set B := Jc.map (starRingEnd ℂ) with hB
  have hBJ : Bᴴ = Jcᵀ := by
    ext a b
    simp [hB]
  have hA : ∀ i, hessC (φ i ∘ s) (A *ᵥ x) = Bᴴ * hessC (φ i) x * B := fun i => by
    have h := ReciprocityTheory.AnForm.A.hessC_comp (φ i) s _ hsa (hφx i)
    rw [hsx] at h
    rw [hBJ]
    exact h
  have hle : ∀ k, ((fun _ : Fin d => (c : ℂ) • (Bᴴ * B)) k -
      (fun k => hessC (φ k ∘ s) (A *ᵥ x)) k).PosSemidef := fun k => by
    have e : (c : ℂ) • (Bᴴ * B) - Bᴴ * hessC (φ k) x * B =
        Bᴴ * (-hessC (φ k) x + (c : ℂ) • 1) * B := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      abel
    simp only [hA, e]
    exact (hb k x hx).2.conjTranspose_mul_mul_same B
  have hge : ∀ k, ((fun k => hessC (φ k ∘ s) (A *ᵥ x)) k +
      (fun _ : Fin d => (c : ℂ) • (Bᴴ * B)) k).PosSemidef := fun k => by
    have e : Bᴴ * hessC (φ k) x * B + (c : ℂ) • (Bᴴ * B) =
        Bᴴ * (hessC (φ k) x + (c : ℂ) • 1) * B := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    simp only [hA, e]
    exact (hb k x hx).1.conjTranspose_mul_mul_same B
  have key := ReciprocityTheory.AnForm.A.norm_mdisc_le_of_abs_le _ _ hle hge
  rw [ReciprocityTheory.AnForm.A.mdisc_const, Matrix.det_smul, Fintype.card_fin] at key
  have hconj : Bᴴ * B = (Jcᴴ * Jc).map (starRingEnd ℂ) := by
    rw [hBJ, hB]
    ext i j
    simp [Matrix.mul_apply, mul_comm]
  have hdet : ‖(Bᴴ * B).det‖ = sheetJac s (A *ᵥ x) := by
    have hm : ((Jcᴴ * Jc).map (starRingEnd ℂ)).det = starRingEnd ℂ (Jcᴴ * Jc).det :=
      (RingHom.map_det _ _).symm
    rw [SheetComassAlt.sheetJac_eq_norm_det s _ (hsd.differentiableAt (hV.mem_nhds hyV)), hconj, hm,
      Complex.norm_conj]
  have hre : (((c : ℂ) ^ d * (Bᴴ * B).det).re) ≤ c ^ d * sheetJac s (A *ᵥ x) := by
    refine (Complex.re_le_norm _).trans (le_of_eq ?_)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hc, hdet]
  have hm : |(mdisc fun k => hessC (φ k ∘ s) (A *ᵥ x)).re| ≤ 3 ^ d * (c ^ d * sheetJac s (A *ᵥ x)) :=
    (Complex.abs_re_le_norm _).trans (key.trans (mul_le_mul_of_nonneg_left hre (by positivity)))
  unfold maDens
  rw [abs_mul, abs_of_nonneg (by positivity), mul_assoc _ (3 ^ d * c ^ d), mul_assoc (3 ^ d)]
  exact mul_le_mul_of_nonneg_left hm (by positivity)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

namespace CurveGermComponents

variable {n : ℕ}

theorem mem_zeroSet_iff_le_ker (J : Ideal (MvPolynomial (Fin n) ℂ)) (x : Fin n → ℂ) :
    x ∈ zeroSet J ↔ J ≤ RingHom.ker (eval x : MvPolynomial (Fin n) ℂ →+* ℂ) := by
  simp only [zeroSet, Set.mem_ofPred_eq, SetLike.le_def, RingHom.mem_ker]

theorem isClosed_zeroSet (J : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroSet J) := by
  have h : zeroSet J = ⋂ f ∈ J, {x : Fin n → ℂ | eval x f = 0} := by
    ext x
    simp [zeroSet]
  rw [h]
  exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval f) continuous_const

theorem exists_minimalPrime_mem_zeroSet {I : Ideal (MvPolynomial (Fin n) ℂ)} {x : Fin n → ℂ}
    (hx : x ∈ zeroSet I) : ∃ W ∈ I.minimalPrimes, x ∈ zeroSet W := by
  rw [mem_zeroSet_iff_le_ker] at hx
  obtain ⟨W, hW, hle⟩ := Ideal.exists_minimalPrimes_le hx
  exact ⟨W, hW, (mem_zeroSet_iff_le_ker W x).2 hle⟩

theorem ringKrullDim_curveLocalRing_le_zero {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (hm : RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) ∈ I.minimalPrimes) :
    ringKrullDim (curveLocalRing I q) ≤ 0 := by
  set m := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) with hmdef
  let L := Localization.AtPrime m
  let J : Ideal L := I.map (algebraMap (MvPolynomial (Fin n) ℂ) L)
  change ringKrullDim (L ⧸ J) ≤ 0
  have hK : Ring.KrullDimLE 0 (L ⧸ J) := by
    rw [Ring.krullDimLE_zero_iff]
    intro p hp
    set Q := p.comap (Ideal.Quotient.mk J) with hQdef
    have hQ : Q.IsPrime := Ideal.comap_isPrime _ _
    have hP : (Q.comap (algebraMap (MvPolynomial (Fin n) ℂ) L)).IsPrime := Ideal.comap_isPrime _ _
    have hIP : I ≤ Q.comap (algebraMap (MvPolynomial (Fin n) ℂ) L) := by
      rw [← Ideal.map_le_iff_le_comap]
      intro y hy
      rw [hQdef, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hy]
      exact p.zero_mem
    have hPm : Q.comap (algebraMap (MvPolynomial (Fin n) ℂ) L) ≤ m := by
      exact (Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ.ne_top)).trans
        (Localization.AtPrime.under_maximalIdeal (I := m)).le
    have hPeq : Q.under (MvPolynomial (Fin n) ℂ) = m := le_antisymm hPm (hm.2 ⟨hP, hIP⟩ hPm)
    have hQmax : Q = IsLocalRing.maximalIdeal L := Localization.AtPrime.eq_maximalIdeal_iff_under_eq.1 hPeq
    have hQm : Q.IsMaximal := hQmax ▸ IsLocalRing.maximalIdeal.isMaximal L
    have h := Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective hQm
    rw [hQdef, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h
    exact h.resolve_left hp.ne_top
  exact_mod_cast Ring.krullDimLE_iff.1 hK

theorem ringKrullDim_localRingAt_eq_one {I W : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (hW : W ∈ I.minimalPrimes) (hq : q ∈ zeroSet W) (hdim : ringKrullDim (curveLocalRing I q) = 1) :
    ringKrullDim (localRingAt W q) = 1 := by
  set m := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) with hmdef
  have hWm : W ≤ m := (mem_zeroSet_iff_le_ker W q).1 hq
  have hWp : W.IsPrime := hW.1.1
  let L := Localization.AtPrime m
  have hle : I.map (algebraMap (MvPolynomial (Fin n) ℂ) L) ≤ W.map (algebraMap (MvPolynomial (Fin n) ℂ) L) :=
    Ideal.map_mono hW.1.2
  have hup : ringKrullDim (localRingAt W q) ≤ 1 := by
    rw [← hdim]
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
  have disj : Disjoint (m.primeCompl : Set (MvPolynomial (Fin n) ℂ)) W := by
    rw [Set.disjoint_left]
    intro a ha haW
    exact ha (hWm haW)
  have hWL : (W.map (algebraMap (MvPolynomial (Fin n) ℂ) L)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl L W hWp disj
  have hne : ¬ ringKrullDim (localRingAt W q) ≤ 0 := by
    intro h0
    have : Ring.KrullDimLE 0 (localRingAt W q) := Ring.krullDimLE_iff.2 (by exact_mod_cast h0)
    have : IsDomain (localRingAt W q) := Ideal.Quotient.isDomain _
    have hf : IsField (localRingAt W q) := Ring.KrullDimLE.isField_of_isDomain (R := localRingAt W q)
    have hmax : (W.map (algebraMap (MvPolynomial (Fin n) ℂ) L)).IsMaximal :=
      Ideal.Quotient.maximal_of_isField _ hf
    have hWeq : W = m := by
      have h1 := IsLocalization.under_map_of_isPrime_disjoint m.primeCompl L hWp disj
      rw [IsLocalRing.eq_maximalIdeal hmax, Localization.AtPrime.under_maximalIdeal] at h1
      exact h1.symm
    rw [hWeq] at hW
    have h2 := ringKrullDim_curveLocalRing_le_zero hW
    rw [hdim] at h2
    exact absurd h2 (by decide)
  exact le_antisymm hup (Order.succ_le_of_lt (lt_of_not_ge hne))

theorem exists_ringKrullDim_quotient_eq_nat (W : Ideal (MvPolynomial (Fin n) ℂ)) [W.IsPrime] :
    ∃ e : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (e : ℕ) := by
  have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ W)
  have h1 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ (n : ℕ) :=
    (ringKrullDim_quotient_le W).trans (by simp)
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = d at h0 h1 ⊢
  induction d using WithBot.recBotCoe with
  | bot => simp at h0
  | coe d =>
    induction d using ENat.recTopCoe with
    | top =>
      rw [← WithBot.coe_natCast, WithBot.coe_le_coe] at h1
      exact absurd h1 (not_le.2 (ENat.natCast_lt_top n))
    | coe e => exact ⟨e, rfl⟩

theorem proof : CurveGermComponents.Statement := by
  intro n I q hdim
  classical
  have hfin : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ I
  refine ⟨⋂ W ∈ {W ∈ I.minimalPrimes | q ∉ zeroSet W}, (zeroSet W)ᶜ, ?_, ?_⟩
  · exact (Filter.biInter_mem (hfin.subset (Set.sep_subset _ _))).2 fun W hW =>
      (isClosed_zeroSet W).isOpen_compl.mem_nhds hW.2
  · rintro x ⟨hxI, hxN⟩
    obtain ⟨W, hW, hxW⟩ := exists_minimalPrime_mem_zeroSet hxI
    have hqW : q ∈ zeroSet W := by
      by_contra hq
      exact Set.mem_iInter₂.1 hxN W ⟨hW, hq⟩ hxW
    refine ⟨W, hW, ?_, hqW, hxW⟩
    have hWp : W.IsPrime := hW.1.1
    obtain ⟨e, he⟩ := exists_ringKrullDim_quotient_eq_nat W
    have h1 := LocalDimDomain.proof n e W hWp he q hqW
    rw [ringKrullDim_localRingAt_eq_one hW hqW hdim] at h1
    rw [he]
    exact_mod_cast h1.symm

end CurveGermComponents

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

theorem RegMassNearSmall.proof (hCmp : RegFormCompare.Statement) (hBall : RegBallMass.Statement)
    (hCov : SmallSetBallCover.Statement) : RegMassNearSmall.Statement := by
  classical
  intro n d J I u φ f hJ hdim hu hφ hIdim hf hfc δ hδ
  by_cases h : ∃ A : Matrix (Fin (d + 1)) (Fin n) ℂ, IsFiniteProjection J A
  swap
  · exact ⟨Set.univ, isOpen_univ, Set.subset_univ _, fun χ _ _ _ ε _ => by simp [varInt, h, hδ.le]⟩
  set A := h.choose
  have hA : IsFiniteProjection J A := h.choose_spec
  have hfin : ∀ y, (ComplexSets.fibre J A y).Finite :=
    fun y => (FibreBound.proof n (d + 1) J A hJ hdim hA y).2.1
  set K := tsupport f
  obtain ⟨C₁, hC₁, h₁⟩ := hCmp n d J A φ f hJ hdim hA hφ hf hfc
  obtain ⟨C₂, hC₂, h₂⟩ := hBall n d J A u K hJ hdim hA hu hfc
  obtain ⟨C₃, hC₃, h₃⟩ := hCov n d I K hIdim hfc
  have hM : 0 ≤ C₁ * C₂ * C₃ := by positivity
  set r := min 1 (δ / (C₁ * C₂ * C₃ + 1))
  have hr : r ∈ Set.Ioc (0 : ℝ) 1 := ⟨lt_min one_pos (by positivity), min_le_left _ _⟩
  obtain ⟨T, hTK, hcov, hcard⟩ := h₃ r hr
  have hUo : IsOpen ((⋃ c ∈ T, Metric.ball c r) ∪ Kᶜ) :=
    (isOpen_biUnion fun (c : Fin n → ℂ) _ => Metric.isOpen_ball).union hfc.isClosed.isOpen_compl
  refine ⟨(⋃ c ∈ T, Metric.ball c r) ∪ Kᶜ, hUo, fun x hx => ?_, fun χ _ hχ1 hχU ε hε => ?_⟩
  · by_cases hxK : x ∈ K
    · exact Or.inl (hcov ⟨hx, hxK⟩)
    · exact Or.inr hxK
  set ψ : Fin (d + 1) → (Fin n → ℂ) → ℝ := vecCons (logReg u ε) fun _ => euclPot
  set w : (Fin n → ℂ) → ℝ := fun x => ∑ c ∈ T, (Metric.ball c r).indicator (fun _ => (1 : ℝ)) x with hw
  have hi0 : ∀ c x : Fin n → ℂ, 0 ≤ (Metric.ball c r).indicator (fun _ => (1 : ℝ)) x :=
    fun c x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hw0 : ∀ x, 0 ≤ w x := fun x => Finset.sum_nonneg fun c _ => hi0 c x
  have hvw : ∀ x ∈ K, |χ x| ≤ w x := by
    intro x hxK
    by_cases h0 : χ x = 0
    · rw [h0, abs_zero]
      exact hw0 x
    rcases hχU (subset_tsupport χ h0) with hxB | hxK'
    · obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.1 hxB
      calc |χ x| ≤ 1 := hχ1 x
        _ = (Metric.ball c r).indicator (fun _ => (1 : ℝ)) x := (Set.indicator_of_mem hxc (fun _ => (1 : ℝ))).symm
        _ ≤ w x := Finset.single_le_sum (f := fun c => (Metric.ball c r).indicator (fun _ => (1 : ℝ)) x)
            (fun c _ => hi0 c x) hc
    · exact absurd hxK hxK'
  have hsum : chartDens J A w ψ =
      fun y => ∑ c ∈ T, chartDens J A ((Metric.ball c r).indicator fun _ => 1) ψ y := by
    funext y
    simp only [chartDens, sheetSum]
    simp_rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp [hw, Finset.sum_mul]
  have hball := fun c (hc : c ∈ T) => h₂ ε hε c (hTK hc).2 r hr
  have hint : Integrable (chartDens J A w ψ) := by
    rw [hsum]
    exact integrable_finsetSum _ fun c hc => (hball c hc).1
  have hT : ∫ y, chartDens J A w ψ y ≤ T.card * (C₂ * r ^ (2 * d)) := by
    rw [hsum, integral_finsetSum _ fun c hc => (hball c hc).1, ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun c hc => (hball c hc).2
  rw [varInt, dite_eq_left h]
  calc |chartInt J A (fun x => χ x * f x) (vecCons (logReg u ε) φ)|
      ≤ ∫ y, C₁ * chartDens J A w ψ y := by
        refine abs_integral_le_integral_abs.trans (integral_mono_of_nonneg
          (Eventually.of_forall fun y => abs_nonneg _) (hint.const_mul C₁) (Eventually.of_forall fun y => ?_))
        exact (VarIntAdd.abs_chartDens_le hfin _ _ y).trans (h₁ u ε hε.1 χ w hw0 hvw y)
    _ = C₁ * ∫ y, chartDens J A w ψ y := integral_const_mul _ _
    _ ≤ C₁ * (T.card * (C₂ * r ^ (2 * d))) := mul_le_mul_of_nonneg_left hT hC₁
    _ = C₁ * C₂ * (T.card * r ^ (2 * d)) := by ring
    _ ≤ C₁ * C₂ * (C₃ * r ^ 2) := mul_le_mul_of_nonneg_left hcard (by positivity)
    _ ≤ (C₁ * C₂ * C₃ + 1) * r := by
        nlinarith [mul_le_mul_of_nonneg_left hr.2 (mul_nonneg hM hr.1.le), hr.1]
    _ ≤ (C₁ * C₂ * C₃ + 1) * (δ / (C₁ * C₂ * C₃ + 1)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
    _ = δ := mul_div_cancel₀ _ (by positivity)

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem BranchInCurveComponent.proof (h₁ : BranchInComponent.Statement) :
    BranchInCurveComponent.Statement := by
  intro n I q c hdim
  obtain ⟨J, hJ, hmaps⟩ := h₁ n I 1 q c
  have hJp : J.IsPrime := hJ.1.1
  have hIJ : I ≤ J := hJ.1.2
  have hq : q ∈ zeroSet J := c.map_zero ▸ hmaps (Metric.mem_ball_self c.radius_pos)
  refine ⟨J, hJ, ?_, Filter.mem_of_superset (Metric.ball_mem_nhds _ c.radius_pos) hmaps⟩
  have : Nontrivial (MvPolynomial (Fin n) ℂ ⧸ J) := inferInstance
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (n : ℕ) := by
    refine (ringKrullDim_quotient_le J).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  obtain ⟨e, he⟩ : ∃ e : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = e := by
    have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) :=
      ringKrullDim_nonneg_of_nontrivial
    generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d at h0 hle ⊢
    induction d using WithBot.recBotCoe with
    | bot => simp at h0
    | coe x =>
      induction x using ENat.recTopCoe with
      | top =>
        exfalso
        simp only [not_le.2 (show ((n : ℕ) : WithBot ℕ∞) < ((⊤ : ℕ∞) : WithBot ℕ∞) from
          WithBot.coe_lt_coe.2 (ENat.natCast_lt_top n))] at hle
      | coe e => exact ⟨e, rfl⟩
  have he1 : (e : WithBot ℕ∞) ≤ 1 := by
    rw [← LocalDimDomain.proof n e J hJp he q hq, ← hdim]
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor (Ideal.map_mono hIJ))
      (Ideal.Quotient.factor_surjective _)
  have he0 : e ≠ 0 := by
    rintro rfl
    have : Ring.KrullDimLE 0 (MvPolynomial (Fin n) ℂ ⧸ J) :=
      ringKrullDimZero_iff_ringKrullDim_eq_zero.2 (by simpa using he)
    have hJq : J = RingHom.ker (eval q) :=
      (Ideal.Quotient.maximal_of_isField J Ring.KrullDimLE.isField_of_isDomain).eq_of_le
        (RingHom.ker_ne_top _) fun f hf ↦ RingHom.mem_ker.2 (hq f hf)
    have hr := c.radius_pos
    have ht : (fun _ ↦ ((c.radius / 2 : ℝ) : ℂ)) ∈ Metric.ball (0 : Fin 1 → ℂ) c.radius := by
      rw [mem_ball_zero_iff, pi_norm_const, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
      linarith
    have hct : c.toFun (fun _ ↦ ((c.radius / 2 : ℝ) : ℂ)) = c.toFun 0 := by
      rw [c.map_zero]
      funext i
      have hmem : X i - C (q i) ∈ J := by
        rw [hJq, RingHom.mem_ker]
        simp
      simpa [sub_eq_zero] using hmaps ht _ hmem
    have h0 := congrFun (c.injOn ht (Metric.mem_ball_self hr) hct) 0
    simp only [Pi.zero_apply, Complex.ofReal_eq_zero] at h0
    linarith
  rw [he]
  have : e ≤ 1 := by exact_mod_cast he1
  have : e = 1 := by omega
  subst this
  rfl

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open scoped ContDiff

noncomputable section

def RadialPrimitive.Statement : Prop :=
  ∀ (e : ℕ) (a : ℝ → ℝ) (t₀ T : ℝ),
    ContDiff ℝ ∞ a → 0 < t₀ → (∀ t ∈ Set.Icc 0 t₀, a t = a 0) → (∀ t, T ≤ t → a t = 0) →
    (∫ τ in (0 : ℝ)..T, a τ * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1))) = 0 →
      ∃ Q : ℝ → ℝ, ContDiff ℝ ∞ Q ∧ (∃ R : ℝ, ∀ t, R ≤ t → Q t = 0) ∧
        deriv Q 0 = a 0 ∧ deriv (deriv Q) 0 = 0 ∧
        ∀ t, 0 < t →
          deriv Q t * t ^ (e + 1) = a t * t ^ (e + 1) - radialTransform (e + 1) a t ∧
            deriv (deriv Q) t * t ^ (e + 2) = ((e + 1 : ℕ) : ℝ) * radialTransform (e + 1) a t

end

end GroundTheory.Heights₂.Heights
end
