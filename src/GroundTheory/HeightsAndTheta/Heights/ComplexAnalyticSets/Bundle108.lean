module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle063
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle031
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle062
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle064
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle106
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeFormCompare
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle068
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle105
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle104
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle083
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle085
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartLocalOrder
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Ideal.Height
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle002
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle002

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem ringKrullDim_eq_one_of_surjective_of_ker_mem_minimalPrimes {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] (hR : ringKrullDim R = 1) {p : Ideal R} (hp : p ∈ minimalPrimes R) (φ : R →+* S)
    (hφ : Function.Surjective φ) (hker : RingHom.ker φ = p) : ringKrullDim S = 1 := by
  have hpp : p.IsPrime := hp.1.1
  refine le_antisymm (hR ▸ ringKrullDim_le_of_surjective φ hφ) ?_
  obtain ⟨x, y, hxy⟩ := Order.one_le_krullDim_iff.1 (le_of_eq hR.symm : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
  have hxm : x.asIdeal < IsLocalRing.maximalIdeal R :=
    lt_of_lt_of_le hxy (IsLocalRing.le_maximalIdeal y.isPrime.ne_top)
  have hpm : p < IsLocalRing.maximalIdeal R := by
    refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hpp.ne_top) fun h ↦ ?_
    have hpx : p ≤ x.asIdeal := hp.2 ⟨x.isPrime, bot_le⟩ (h ▸ hxm.le)
    exact (lt_of_le_of_lt hpx hxm).ne h
  have hk : ∀ K : Ideal R, p ≤ K → (K.map φ).comap φ = K := fun K hK ↦ by
    rw [Ideal.comap_map_of_surjective' φ hφ, hker, sup_eq_left.2 hK]
  have h0 : (p.map φ).IsPrime := Ideal.map_isPrime_of_surjective hφ hker.le
  have h1 : ((IsLocalRing.maximalIdeal R).map φ).IsPrime :=
    Ideal.map_isPrime_of_surjective hφ (hker.le.trans hpm.le)
  refine Order.one_le_krullDim_iff.2 ⟨⟨_, h0⟩, ⟨_, h1⟩, ?_⟩
  change p.map φ < (IsLocalRing.maximalIdeal R).map φ
  refine lt_of_le_of_ne (Ideal.map_mono hpm.le) fun h ↦ hpm.ne ?_
  rw [← hk p le_rfl, h, hk _ hpm.le]

theorem PlaceOnComponent.proof (h₁ : ReducedNormalisationPlace.Statement)
    (h₂ : CurveMinimalPrimeQuotient.Statement) : PlaceOnComponent.Statement := by
  intro n I q hrad hdim P
  have : IsReduced (curveLocalRing I q) := isReduced_curveLocalRing I q hrad
  have : Nontrivial (curveLocalRing I q) := by
    refine not_subsingleton_iff_nontrivial.1 fun h ↦ ?_
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact absurd hdim (by decide)
  have : IsLocalRing (curveLocalRing I q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  obtain ⟨p, hp, hS⟩ := h₁ (curveLocalRing I q) P
  obtain ⟨J, hJ, hJq, φ, hφ, hker, hφf⟩ := h₂ n I q p hp
  obtain ⟨P', hP'⟩ := hS (curveLocalRing J q) φ hφ hker
  refine ⟨J, hJ, hJq, ringKrullDim_eq_one_of_surjective_of_ker_mem_minimalPrimes hdim hp φ hφ hker, P', fun f ↦ ?_⟩
  have e := hP' (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f)
  rw [hφf] at e
  exact e

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

variable {n : ℕ}

theorem isLocalRing_curveLocalRing (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    [Nontrivial (curveLocalRing I q)] : IsLocalRing (curveLocalRing I q) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial (Fin n) ℂ)
    (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)))))) Ideal.Quotient.mk_surjective

theorem OrdFiniteNonZeroDivisor.proof : OrdFiniteNonZeroDivisor.Statement := by
  intro n I q f hrad hdim hord
  have : Nontrivial (curveLocalRing I q) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact WithBot.bot_ne_coe hdim
  have : IsLocalRing (curveLocalRing I q) := isLocalRing_curveLocalRing I q
  have : IsReduced (curveLocalRing I q) := isReduced_curveLocalRing I q hrad
  rw [mem_nonZeroDivisors_iff_right]
  intro y hyx
  by_contra hy

  obtain ⟨p, hp, hyp⟩ : ∃ p ∈ minimalPrimes (curveLocalRing I q), y ∉ p := by
    have : y ∉ (⊥ : Ideal (curveLocalRing I q)).radical := by
      rintro ⟨k, hk⟩
      exact hy (IsNilpotent.eq_zero ⟨k, (Submodule.mem_bot _).1 hk⟩)
    simpa [← Ideal.sInf_minimalPrimes, minimalPrimes] using this
  have hpP : p.IsPrime := hp.1.1
  have hxp := (hpP.mem_or_mem (hyx ▸ p.zero_mem)).resolve_left hyp

  have hpmax : ¬ p.IsMaximal := by
    intro hm
    have h1 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := curveLocalRing I q)
    rw [← IsLocalRing.eq_maximalIdeal hm, Ideal.height_eq_zero_iff.mpr hp, hdim] at h1
    exact absurd h1 (by decide)

  have : Algebra.IsIntegral (curveLocalRing I q) (curveNormalisation I q) :=
    inferInstanceAs (Algebra.IsIntegral (curveLocalRing I q)
      (integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))))
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p (⊥ : Ideal (curveNormalisation I q))
    (by rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1
      (algebraMap_curveNormalisation_injective I q)]; exact bot_le)
  obtain ⟨P, hPm, hQP⟩ := Ideal.exists_le_maximal Q hQ.ne_top
  apply hord ⟨P, hPm⟩
  have : P.IsPrime := hPm.isPrime
  have hd : Disjoint (P.primeCompl : Set (curveNormalisation I q)) Q :=
    Set.disjoint_left.2 fun a ha haQ ↦ ha (hQP haQ)
  set Q' := Q.map (algebraMap (curveNormalisation I q) (Localization.AtPrime P)) with hQ'def
  have : Q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint P.primeCompl _ Q hQ hd
  have hQ'u : Q'.under _ = Q := IsLocalization.under_map_of_isPrime_disjoint P.primeCompl _ hQ hd
  have hle : Ideal.span {(algebraMap (curveNormalisation I q) (Localization.AtPrime P)
      (algebraMap (curveLocalRing I q) (curveNormalisation I q)
        (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f)))} ≤ Q' := by
    rw [Ideal.span_singleton_le_iff_mem]
    refine Ideal.mem_map_of_mem _ ?_
    rw [← hQp] at hxp
    exact hxp

  change Module.length (Localization.AtPrime P) (Localization.AtPrime P ⧸ Ideal.span {_}) = ⊤
  by_contra hne
  rw [← ne_eq, Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at hne
  obtain ⟨-, hart⟩ := hne
  have : IsArtinian (Localization.AtPrime P) (Localization.AtPrime P ⧸ Q') :=
    isArtinian_of_surjective _ (Submodule.factor hle) (Submodule.factor_surjective hle)
  have : IsArtinianRing (Localization.AtPrime P ⧸ Q') := isArtinian_of_tower (Localization.AtPrime P) this
  have hQ'max : Q'.IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (IsArtinianRing.isField_of_isDomain _)
  have hQeq : Q = P := by
    rw [← hQ'u, IsLocalRing.eq_maximalIdeal hQ'max, Localization.AtPrime.under_maximalIdeal]
  apply hpmax
  rw [← hQp]
  have : Q.IsMaximal := hQeq ▸ hPm
  exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal Q

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix Filter Topology ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder

noncomputable section

namespace RegularizedFormComparison

open TubeFormComparison

theorem posSemidef_hessC_logReg_comp {n D : ℕ} (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε)
    (s : (Fin D → ℂ) → Fin n → ℂ) (y : Fin D → ℂ) (hs : AnalyticAt ℂ s y) :
    (hessC (logReg u ε ∘ s) y).PosSemidef := by
  set τ : (Fin D → ℂ) → Fin 1 → ℂ := fun z _ => ((√ε : ℝ) : ℂ)⁻¹ * linEval u (s z) with hτ
  have hτa : AnalyticAt ℂ τ y := by
    refine analyticAt_pi_iff.2 fun _ => analyticAt_const.mul ?_
    unfold linEval
    exact Finset.analyticAt_fun_sum (f := fun j z => u j * s z j) _ fun j _ =>
      analyticAt_const.mul (analyticAt_pi_iff.1 hs j)
  have hsq : ((√ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hε).ne'
  have he : logReg u ε ∘ s =
      fun z => (1 / 2 : ℝ) * HilbertSamuel.ProjFS.logPot (τ z) + Real.log ε / 2 := by
    funext z
    have h1 : HilbertSamuel.ProjFS.logPot (τ z) = Real.log (1 + ‖linEval u (s z)‖ ^ 2 / ε) := by
      show Real.log (1 + euclPot (τ z)) = _
      congr 2
      simp only [euclPot, hτ, Finset.univ_unique, Finset.sum_singleton, norm_mul, norm_inv, mul_pow,
        inv_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg ε),
        Real.sq_sqrt hε.le]
      ring
    have h2 : ‖linEval u (s z)‖ ^ 2 + ε = ε * (1 + ‖linEval u (s z)‖ ^ 2 / ε) := by
      field_simp
      ring
    simp only [Function.comp_apply, logReg]
    rw [h1, h2, Real.log_mul hε.ne' (by positivity)]
    ring
  have hconst : ∀ (F : (Fin D → ℂ) → ℝ) (c : ℝ), hessC (fun z => F z + c) y = hessC F y := by
    intro F c
    have h : fderiv ℝ (fun z => F z + c) = fderiv ℝ F := funext fun z => fderiv_add_const c
    unfold hessC
    rw [h]
  have hL2 : ContDiffAt ℝ 2 (HilbertSamuel.ProjFS.logPot (N := 1)) (τ y) :=
    ((SheetFormComparison.contDiff_logPot 1).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt
  rw [he, hconst (fun z => (1 / 2 : ℝ) * HilbertSamuel.ProjFS.logPot (τ z)),
    ReciprocityTheory.AnForm.M.hessC_const_mul']
  have hcomp : hessC (fun z => HilbertSamuel.ProjFS.logPot (τ z)) y =
      hessC (HilbertSamuel.ProjFS.logPot ∘ τ) y := rfl
  rw [hcomp, ReciprocityTheory.AnForm.A.hessC_comp _ τ y hτa hL2]
  have hP : (hessC (HilbertSamuel.ProjFS.logPot (N := 1)) (τ y)).PosSemidef :=
    ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ hL2 fun w => HilbertSamuel.ProjFS.levi_logPot_nonneg _ w
  set B := (ReciprocityTheory.AnForm.A.jacC τ y).map (starRingEnd ℂ) with hB
  have hBJ : Bᴴ = (ReciprocityTheory.AnForm.A.jacC τ y)ᵀ := by
    ext a b
    simp [hB]
  rw [← hBJ]
  exact (hP.conjTranspose_mul_mul_same B).smul (Complex.zero_le_real.2 (by norm_num))

theorem maDens_euclPot_nonneg {n d : ℕ} (g : (Fin n → ℂ) → ℝ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ)
    (y : Fin (d + 1) → ℂ) (hs : AnalyticAt ℂ s y) (hM : (hessC (g ∘ s) y).PosSemidef) :
    0 ≤ maDens (fun k => vecCons g (fun _ : Fin d => euclPot) k ∘ s) y := by
  have hE2 : ∀ _ : Fin d, ContDiffAt ℝ 2 (euclPot : (Fin n → ℂ) → ℝ) (s y) := fun _ =>
    ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt
  have hb : ∀ _ : Fin d, (hessC (euclPot : (Fin n → ℂ) → ℝ) (s y) + ((1 : ℝ) : ℂ) • 1).PosSemidef ∧
      (-hessC (euclPot : (Fin n → ℂ) → ℝ) (s y) + ((1 : ℝ) : ℂ) • 1).PosSemidef := fun _ => by
    rw [hessC_euclPot]
    refine ⟨?_, ?_⟩
    · simpa using Matrix.PosSemidef.one.add Matrix.PosSemidef.one
    · simpa using (Matrix.PosSemidef.zero : (0 : Matrix (Fin n) (Fin n) ℂ).PosSemidef)
  have key := abs_maDens_cons_le g (fun _ : Fin d => euclPot) s y hs hE2 hb hM
  have h0 := (abs_nonneg _).trans key
  rw [one_pow, mul_one] at h0
  exact nonneg_of_mul_nonneg_right h0 (by positivity)

end RegularizedFormComparison


open TubeFormComparison RegularizedFormComparison in
theorem RegFormCompare.proof : RegFormCompare.Statement := by
  intro n d J A φ f _hJ _hdim hA hφ hfc hfs
  set K := zeroSet J ∩ tsupport f with hKdef
  have hK : IsCompact K := hfs.isCompact.inter_left (isClosed_zeroSet J)
  choose U hU hZU hφU using hφ
  obtain ⟨c, hc, hb⟩ := exists_hessC_bound φ K hK U hU
    (fun i => Set.inter_subset_left.trans (hZU i)) (fun i => (hφU i).of_le (WithTop.coe_le_coe.2 le_top))
  obtain ⟨M, hM⟩ := hfc.bounded_above_of_compact_support hfs
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hC : 0 ≤ max M 0 * (3 ^ (d + 1) * c ^ d) := by positivity
  refine ⟨max M 0 * (3 ^ (d + 1) * c ^ d), hC, fun u ε hε v w hw hvw y => ?_⟩
  unfold chartDens chartAbsDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y),
    finsum_mem_eq_finite_toFinset_sum _ (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y), Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  obtain ⟨hxZ, hxy⟩ := hx
  subst hxy
  split_ifs with hsx
  swap
  · simp
  dsimp only
  obtain ⟨V, hV, hyV, hsd, hsx', -, -⟩ := hsx.choose_spec
  set s := hsx.choose with hsdef
  have hsa : AnalyticAt ℂ s (A *ᵥ x) :=
    analyticAt_pi_iff.2 fun i =>
      ReciprocityTheory.AnForm.Osgood.osgood _ V (fun z => s z i) hV (differentiableOn_pi.1 hsd i) _ hyV
  have hMs := posSemidef_hessC_logReg_comp u hε s (A *ᵥ x) hsa
  have hE := maDens_euclPot_nonneg (logReg u ε) s (A *ᵥ x) hsa hMs
  by_cases hxf : x ∈ tsupport f
  · have hφx : ∀ i, ContDiffAt ℝ 2 (φ i) (s (A *ᵥ x)) := fun i => by
      rw [hsx']
      exact ((hφU i).contDiffAt ((hU i).mem_nhds (hZU i hxZ))).of_le (WithTop.coe_le_coe.2 le_top)
    have hbx : ∀ i, (hessC (φ i) (s (A *ᵥ x)) + (c : ℂ) • 1).PosSemidef ∧
        (-hessC (φ i) (s (A *ᵥ x)) + (c : ℂ) • 1).PosSemidef := fun i => by
      rw [hsx']
      exact hb i x ⟨hxZ, hxf⟩
    have key := abs_maDens_cons_le _ φ s (A *ᵥ x) hsa hφx hbx hMs
    have hfx : |f x| ≤ max M 0 := (Real.norm_eq_abs (f x) ▸ hM x).trans (le_max_left _ _)
    have hvx : |v x| ≤ w x := hvw x hxf
    rw [abs_mul, abs_mul]
    calc |v x| * |f x| * |maDens (fun k => vecCons (logReg u ε) φ k ∘ s) (A *ᵥ x)|
        ≤ w x * max M 0 * (3 ^ (d + 1) * c ^ d *
            maDens (fun k => vecCons (logReg u ε) (fun _ => euclPot) k ∘ s) (A *ᵥ x)) := by
          have hwx := hw x
          have hK0 : 0 ≤ (3 : ℝ) ^ (d + 1) * c ^ d := by positivity
          have h1 : |v x| * |f x| ≤ w x * max M 0 := mul_le_mul hvx hfx (abs_nonneg _) (hw x)
          calc |v x| * |f x| * |maDens (fun k => vecCons (logReg u ε) φ k ∘ s) (A *ᵥ x)|
              ≤ w x * max M 0 * |maDens (fun k => vecCons (logReg u ε) φ k ∘ s) (A *ᵥ x)| :=
                mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
            _ ≤ _ := mul_le_mul_of_nonneg_left key (mul_nonneg hwx hM0)
      _ = _ := by ring
  · rw [image_eq_zero_of_notMem_tsupport hxf, mul_zero, zero_mul, abs_zero]
    exact mul_nonneg hC (mul_nonneg (hw x) hE)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets Metric Set

noncomputable section

theorem DivisorGoodPointBranches.proof : DivisorGoodPointBranches.Statement := by
  intro n d J u M q _hJ _hdim _hu hqJ hqu hreg hchart hdouble
  obtain ⟨A, O, V, g, -, hV, hqV, hg, hAg, hS⟩ := hreg
  obtain ⟨N₀, hN₀, hdbl⟩ := hdouble
  let F : Set (Fin n ⊕ Fin M.m → ℂ) :=
    {w | w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∧ IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q}
  have hmemF : ∀ w, w ∈ F ↔ (w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∧ IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q) :=
    fun w => Iff.rfl
  have hFfin : F.Finite := NormalModelFibre.fibre_finite M q
  obtain ⟨G, hGo, hGd⟩ := hFfin.t2_separation
  let _ : Fintype F := hFfin.fintype
  let e : Fin (Fintype.card F) ≃ F := (Fintype.equivFin F).symm
  have hbr : ∀ b : Fin (Fintype.card F), ∃ γ : VarBranch J (d + 1) q, ∃ ord : ℕ,
      (∃ U ∈ 𝓝 (e b : Fin n ⊕ Fin M.m → ℂ), ∀ w' ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ U,
        IndefiniteRowSideFullHecke.ComplexSets.firstCoords w' ∈ γ.image) ∧
      (∀ x ∈ γ.image, x ∈ N₀ ∧
        ∃ w' ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ G (e b), IndefiniteRowSideFullHecke.ComplexSets.firstCoords w' = x) ∧
      (∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet J ∩ N, linEval u x = 0 → x ∈ γ.slice) ∧
      VanishesToOrder (fun t => linEval u (γ.toFun t)) γ.radius ord ∧
      Function.Bijective (fderiv ℂ (fun τ => vecCons (τ 0)
        (LinearMap.toMatrix' (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) *ᵥ γ.toFun τ)) (0 : Fin (d + 1) → ℂ)) := by
    intro b
    have hb := (hmemF _).1 (e b).2
    obtain ⟨r, φ, k, hr, hφd, hφi, hφ0, hφZ, hφU, hvan, hinjD⟩ := hchart (e b) hb.1 hb.2
    obtain ⟨γ, h⟩ := GoodPointBranch.exists_branch M hqu hV hqV hg hAg hS hN₀ hdbl hb.2 hr hφd hφi hφ0
      hφZ hφU hvan hinjD ((hGo _).2.mem_nhds (hGo _).1)
    exact ⟨γ, k, h⟩
  choose γ ord hcovw himg hslice hvan hbij using hbr
  refine ⟨Fintype.card F, γ, ord, LinearMap.toMatrix' (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)),
    ?_, ?_, ?_, hvan, hbij⟩
  · choose U hU hUc using hcovw
    obtain ⟨N, hN, hNU⟩ := NormalModelFibre.eventually_mem_of_fibre_subset M (q := q)
      (isOpen_iUnion fun b => isOpen_interior (s := U b)) (fun w hw hwq => by
        obtain ⟨b, hb⟩ := e.surjective ⟨w, (hmemF w).2 ⟨hw, hwq⟩⟩
        refine mem_iUnion.2 ⟨b, mem_interior_iff_mem_nhds.2 ?_⟩
        have hbw : (e b : Fin n ⊕ Fin M.m → ℂ) = w := congrArg Subtype.val hb
        rw [← hbw]
        exact hU b)
    refine ⟨N, hN, fun x hx => ?_⟩
    obtain ⟨w, hw, rfl⟩ := NormalModelFibre.exists_mem_fibre M hx.1
    obtain ⟨b, hb⟩ := mem_iUnion.1 (hNU w hw hx.2)
    exact mem_iUnion.2 ⟨b, hUc b w ⟨hw, interior_subset hb⟩⟩
  · choose N' hN' hN'c using hslice
    exact ⟨⋂ b, N' b, Filter.iInter_mem.2 hN',
      fun x hx hxu b => hN'c b x ⟨hx.1, mem_iInter.1 hx.2 b⟩ hxu⟩
  · intro b b' hbb' x hx
    obtain ⟨hxN, w, ⟨hw, hwG⟩, rfl⟩ := himg b x hx.1
    obtain ⟨-, w', ⟨hw', hw'G⟩, hww'⟩ := himg b' _ hx.2
    have hne : w ≠ w' := by
      rintro rfl
      have hdisj : Disjoint (G (e b)) (G (e b')) :=
        hGd (e b).2 (e b').2 (fun h => hbb' (e.injective (Subtype.ext h)))
      exact Set.disjoint_left.1 hdisj hwG hw'G
    exact hdbl w hw w' hw' hww'.symm hxN hne

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

theorem NormalModelPointOfPlace.proof (hLoc : NormalisationModelLocalization.Statement)
    (hMax : ModelLocalizationMaximalPoint.Statement) (hAt : LocalizationAtPrimeQuotient.Statement.{0}) :
    NormalModelPointOfPlace.Statement := by
  intro n J q M hJ P
  obtain ⟨e, he⟩ := hLoc n J q M hJ
  obtain ⟨P', hP'def⟩ : ∃ P' : @Ideal (Localization (normalModelSubmonoid M q)) CommSemiring.toSemiring,
      P' = P.asIdeal.comap (e.symm : Localization (normalModelSubmonoid M q) →+* curveNormalisation J q) :=
    ⟨_, rfl⟩
  have hP' : P'.IsMaximal := by
    rw [hP'def]
    exact Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
  have hPp : P'.IsPrime := by
    rw [hP'def]
    infer_instance
  obtain ⟨w, hw, hq, hcomap⟩ := hMax n J q M P' hP'
  obtain ⟨eAt, heAt⟩ := hAt (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) M.ideal (normalModelSubmonoid M q) P'
    (RingHom.ker (eval w : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* ℂ)) hcomap
  let eP : Localization.AtPrime P.asIdeal ≃+* Localization.AtPrime P' :=
    IsLocalization.ringEquivOfRingEquiv (M := P.asIdeal.primeCompl) (T := P'.primeCompl)
      (Localization.AtPrime P.asIdeal) (Localization.AtPrime P') e (by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          subst hP'def
          show e.symm (e x) ∉ P.asIdeal
          simpa using hx
        · intro hy
          subst hP'def
          exact ⟨e.symm y, hy, by simp⟩)
  refine ⟨w, hw, hq, fun f ↦ ?_⟩
  rw [← ord_ringEquiv (eP.trans eAt)]
  congr 1
  rw [RingEquiv.trans_apply, IsLocalization.ringEquivOfRingEquiv_eq, he, heAt]
  rfl

end

end GroundTheory.Heights₂.Heights
end
