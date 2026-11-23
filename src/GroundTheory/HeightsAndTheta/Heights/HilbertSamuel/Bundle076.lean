module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle014
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle067
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle072
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle064
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageHilb
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle027
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMassStB

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

namespace MultiDegreePositive

theorem tendsto_diag (K : Type) [Fintype K] :
    Filter.Tendsto (fun n : ℤ => fun _ : K => n) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨∑ k, |b k|, fun a ha k => ?_⟩
  exact (le_abs_self _).trans
    ((Finset.single_le_sum (fun k _ => abs_nonneg (b k)) (Finset.mem_univ k)).trans ha)

theorem mixedDiff_succ {L : Type} [DecidableEq L] (b : L → ℤ) (H : (L → ℤ) → ℤ) (r : ℕ) :
    mixedDiff (fun _ : Fin (r + 1) => b) H = diffStep b (mixedDiff (fun _ : Fin r => b) H) := by
  simp only [mixedDiff, List.ofFn_succ, List.foldr_cons]

theorem mixedDiff_diag {K : Type} [DecidableEq K] (h : (K → ℤ) → ℤ) (g : (Unit → ℤ) → ℤ)
    (hg : ∀ n : ℤ, g (fun _ => n) = h (fun _ => n)) (r : ℕ) (n : ℤ) :
    mixedDiff (fun _ : Fin r => fun _ : Unit => (1 : ℤ)) g (fun _ => n) =
      mixedDiff (fun _ : Fin r => fun _ : K => (1 : ℤ)) h (fun _ => n) := by
  induction r generalizing n with
  | zero => simpa [mixedDiff] using hg n
  | succ r ih =>
    rw [mixedDiff_succ, mixedDiff_succ]
    have e1 : ∀ (L : Type), ((fun _ : L => n) - fun _ : L => (1 : ℤ)) = fun _ => n - 1 :=
      fun L => funext fun _ => rfl
    simp only [diffStep, e1, ih]

theorem pos_of_isEmpty {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] [IsEmpty K]
    {ι : K → Type} [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (e : ℕ) (hq : IsMultiProjPrime q)
    (hd : ringKrullDim (MRing ι F ⧸ q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    0 < intNum F q (fun _ : Fin e => fun _ : K => (1 : ℤ)) := by
  have hle := (ringKrullDim_quotient_le q).trans_eq
    (MvPolynomial.ringKrullDim_of_isNoetherianRing (R := F) (ι := Σ k, ι k))
  rw [hd, ringKrullDim_eq_zero_of_field, zero_add, ENat.card_eq_coe_natCard,
    Nat.card_of_isEmpty, Fintype.card_eq_zero,
    add_zero] at hle
  have he : e = 0 := by exact_mod_cast (nonpos_iff_eq_zero.mp (by exact_mod_cast hle) : (e : ℕ∞) = 0)
  subst he
  have hrel : FieldNumbers.relDim q = ((0 : ℕ) : WithBot (WithTop ℤ)) := by
    rw [FieldNumbers.relDim_of_ringKrullDim_eq q (0 + Fintype.card K) hd]
    simp only [Nat.cast_add, add_sub_cancel_right]
    rfl
  obtain ⟨hA, -⟩ := FieldNumbers.MixedDiffConst.full F K ι q hq.multiHomog hq.relevant 0 hrel
  obtain ⟨m, hm⟩ := (hA (fun _ : Fin 0 => fun _ : K => (1 : ℤ))).exists
  rw [← hm]
  have hm0 : mixedDiff (fun _ : Fin 0 => fun _ : K => (1 : ℤ)) (hilbFn q) m = hilbFn q m := rfl
  rw [hm0]
  obtain ⟨hfin, hval⟩ := FieldNumbers.GradedFinite.full F K ι q (fun _ => 0)
  have hmm : m = fun k => ((fun _ : K => (0 : ℕ)) k : ℤ) := funext fun k => isEmptyElim k
  rw [hmm, hval]
  have hne : (⟨Ideal.Quotient.mkₐ F q 1, Submodule.mem_map_of_mem
      (mem_weightedHomogeneousSubmodule F _ _ _ |>.mpr (isWeightedHomogeneous_one F _))⟩ :
        gradedPiece q (fun _ : K => 0)) ≠ 0 := by
    intro h0
    have h1 := congrArg Subtype.val h0
    simp only [Submodule.coe_zero, map_one] at h1
    exact hq.isPrime.ne_top (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using h1) |>
      (Ideal.eq_top_iff_one q).mpr)
  exact_mod_cast Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hne⟩

end MultiDegreePositive

theorem MultiDegreePositive.proof (hPrime : SegrePrime.Statement) (hHilb : SegreHilb.Statement)
    (hDim : SegreDimGe.Statement) : MultiDegreePositive.Statement := by
  intro F _ K _ _ ι _ q e hq hd
  rcases isEmpty_or_nonempty K with hK | hK
  · exact MultiDegreePositive.pos_of_isEmpty q e hq hd

  have hq' := hPrime F K ι q hq
  have hge := hDim F K ι q e hq hd
  have hle := (ringKrullDim_quotient_le (segrePrime F q)).trans_eq
    (MvPolynomial.ringKrullDim_of_isNoetherianRing (R := F)
      (ι := Σ _ : Unit, ∀ k, ι k))
  rw [ringKrullDim_eq_zero_of_field, zero_add, ENat.card_eq_coe_natCard] at hle

  obtain ⟨D, hD, heD⟩ : ∃ D : ℕ, ringKrullDim (MRing (fun _ : Unit => ∀ k, ι k) F ⧸
      segrePrime F q) = ((D + 1 : ℕ) : WithBot ℕ∞) ∧ e ≤ D := by
    generalize ringKrullDim (MRing (fun _ : Unit => ∀ k, ι k) F ⧸ segrePrime F q) = x at hge hle ⊢
    induction x using WithBot.recBotCoe with
    | bot => exact absurd hge (by simp)
    | coe x =>
      induction x using ENat.recTopCoe with
      | top =>
        have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((Nat.card (Σ _ : Unit, ∀ k, ι k) : ℕ∞) : WithBot ℕ∞) := hle
        exact absurd (WithBot.coe_le_coe.mp h') (not_le.mpr (ENat.natCast_lt_top _))
      | coe m =>
        have hm : e + 1 ≤ m := by exact_mod_cast hge
        exact ⟨m - 1, by rw [Nat.sub_add_cancel (by omega)]; rfl, by omega⟩
  have hrel : FieldNumbers.relDim q = ((e : ℕ) : WithBot (WithTop ℤ)) := by
    rw [FieldNumbers.relDim_of_ringKrullDim_eq q (e + Fintype.card K) hd]
    simp only [Nat.cast_add, add_sub_cancel_right]
    rfl
  have hrel' : FieldNumbers.relDim (segrePrime F q) = ((D : ℕ) : WithBot (WithTop ℤ)) := by
    rw [FieldNumbers.relDim_of_ringKrullDim_eq (segrePrime F q) (D + 1) hD]
    simp only [Fintype.card_unit, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    rfl
  obtain ⟨hA, hB⟩ := FieldNumbers.MixedDiffConst.full F K ι q hq.multiHomog hq.relevant e hrel
  obtain ⟨hA', -⟩ := FieldNumbers.MixedDiffConst.full F Unit (fun _ => ∀ k, ι k) (segrePrime F q)
    hq'.multiHomog hq'.relevant D hrel'
  have hpos := DegreePositive.proof F (∀ k, ι k) (segrePrime F q) D hq' hD
  have hdiag := MultiDegreePositive.mixedDiff_diag (hilbFn q) (hilbFn (segrePrime F q))
    (fun n => hHilb F K ι q n)
  have hA'd := (MultiDegreePositive.tendsto_diag Unit).eventually
    (hA' (fun _ : Fin D => fun _ : Unit => (1 : ℤ)))

  have hDe : D = e := by
    by_contra hne
    have hBd := (MultiDegreePositive.tendsto_diag K).eventually
      (hB D (by omega) (fun _ : Fin D => fun _ : K => (1 : ℤ)))
    obtain ⟨n, h1, h2⟩ := (hA'd.and hBd).exists
    rw [hdiag] at h1
    omega
  subst hDe
  have hAd := (MultiDegreePositive.tendsto_diag K).eventually
    (hA (fun _ : Fin D => fun _ : K => (1 : ℤ)))
  obtain ⟨n, h1, h2⟩ := (hA'd.and hAd).exists
  rw [hdiag] at h1
  omega

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

namespace SectionL2Lattice

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem measurableSet_mcPts (P : Ideal (MRing ι)) : MeasurableSet (mcPts P) := by
  have h1 : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have h2 : IsClosed {z : (Σ k, ι k) → ℂ | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun f => isClosed_iInter fun _ =>
      isClosed_eq (MvPolynomial.continuous_eval _) continuous_const
  exact h1.measurableSet.inter h2.measurableSet


omit [Fintype K] in
theorem isMultiHomog_sum_smul_map {r : ℕ} {e : K → ℕ} {g : Fin r → MRing ι} (hg : ∀ i, IsMultiHomog (g i) e)
    (c : Fin r → ℂ) : IsMultiHomog (∑ i, c i • map (Int.castRingHom ℂ) (g i)) e := by
  classical
  intro m hm k
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum hm)
  exact hg i m (MvPolynomial.support_map_subset _ _ (MvPolynomial.support_smul hi)) k

variable {Ω : Type} [Field Ω]


omit [∀ k, Fintype (ι k)] in
theorem chartLat_le_chartLatNm (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) : chartLat y a τ ≤ chartLatNm y a τ :=
  fun _ hs c hc => isIntegral_algebraMap (R := chartRingZ y c) (A := Ω) (x := ⟨_, hs c hc⟩)


omit [∀ k, Fintype (ι k)] in
theorem finite_chartLat (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) (hfin : Module.Finite ℤ (chartLatNm y a τ)) :
    Module.Finite ℤ (chartLat y a τ) ∧
      Module.finrank ℤ (chartLat y a τ) ≤ Module.finrank ℤ (chartLatNm y a τ) := by
  let f : chartLat y a τ →ₗ[ℤ] chartLatNm y a τ :=
    (AddSubgroup.inclusion (chartLat_le_chartLatNm y a τ)).toIntLinearMap
  have hf : Function.Injective f := AddSubgroup.inclusion_injective (chartLat_le_chartLatNm y a τ)
  have : Module.Finite ℤ (chartLat y a τ) := Module.Finite.of_injective f hf
  exact ⟨inferInstance, LinearMap.finrank_le_finrank_of_injective hf⟩

end SectionL2Lattice


open SectionL2Lattice in
theorem SectionL2Lattice.proof (hV : SectionPointValue.Statement) (hF : RealFormsOnPoints.Statement)
    (hG : L2GramLattice.Statement) (hN : NmSectionsRankBound.Statement) (hB : SectionSupBound.Statement) :
    SectionL2Lattice.Statement := by
  intro K _ ι _ Ω _ _ y D A har hbir hcont μ _ hμ hZ
  obtain ⟨w, hwc, hwrep, hwnorm, hwmul, hwden⟩ := hV K ι Ω y A har.2.1.2.2 hcont
  obtain ⟨hfin, C, -, hC⟩ := hN K ι Ω y D A.a har hbir
  have hae : ∀ᵐ z ∂μ, z ∈ mcPts (mCoordIdeal y) := hμ
  have hrest : μ.restrict (mcPts (mCoordIdeal y)) = μ := Measure.restrict_eq_self_of_ae_mem hae
  have hmeas : ∀ (n : ℕ) (s : chartLat y A.a n), AEStronglyMeasurable (w n s) μ := fun n s => by
    rw [← hrest]; exact (hwc n s).aestronglyMeasurable (measurableSet_mcPts _)
  have hbdd : ∀ (n : ℕ) (s : chartLat y A.a n), ∃ c : ℝ, ∀ᵐ z ∂μ, ‖w n s z‖ ≤ c := fun n s => by
    obtain ⟨c, -, hc⟩ := hB K ι Ω y A n s hcont s.2
    refine ⟨Real.exp c, hae.mono fun z hz => ?_⟩
    rw [← hwnorm n s z hz]
    exact secNormAt_le (Real.exp_pos c).le (isBoundedAt_of_isBoundedH hc hz)
  have hint : ∀ (n : ℕ) (s : chartLat y A.a n), Integrable (fun z => ‖w n s z‖ ^ 2) μ := fun n s => by
    obtain ⟨c, hc⟩ := hbdd n s
    refine (integrable_const (c ^ 2)).mono' ((hmeas n s).norm.pow 2) (hc.mono fun z hz => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) hz 2
  have key : ∀ n : ℕ, ∃ φ : chartLat y A.a n →+ EuclideanSpace ℝ (Fin (Module.finrank ℤ (chartLat y A.a n))),
      Function.Injective φ ∧ DiscreteTopology (imageLattice φ) ∧
      (∀ [DiscreteTopology (imageLattice φ)], IsZLattice ℝ (imageLattice φ)) ∧
      ∀ s, ‖φ s‖ = Real.sqrt (∫ z, ‖w n s z‖ ^ 2 ∂μ) := by
    intro n
    have : Module.Finite ℤ (chartLat y A.a n) := (finite_chartLat y A.a n (hfin n)).1
    have : Module.Free ℤ (chartLat y A.a n) := Module.free_of_finite_type_torsion_free'
    refine hG _ _ μ (w n) (hmeas n) (hbdd n) ?_
    intro r x hx c hc
    obtain ⟨e, e', h, g, hh, hg, he, hy, hgy⟩ := hwden n r x
    refine hF K ι Ω y (D + 1) e r g har hg ?_ c ?_
    · have h1 : LinearIndependent ℤ (fun i => (x i : Ω)) :=
        hx.map' (chartLat y A.a n).subtype.toIntLinearMap (LinearMap.ker_eq_bot.2 Subtype.val_injective)
      have h2 := h1.map' (LinearMap.mulRight ℤ (aeval y h))
        (LinearMap.ker_eq_bot.2 (mul_left_injective₀ hy))
      convert h2 using 1 <;> first | rfl | (funext i; simp [hgy i])
    · intro z hz
      have hF' := hZ e (∑ i, (c i : ℂ) • map (Int.castRingHom ℂ) (g i)) (isMultiHomog_sum_smul_map hg _) ?_ z hz

      · simpa only [map_sum, smul_eval] using hF'
      · filter_upwards [hc, hae] with z hz0 hzP

        rw [map_sum]
        simp only [smul_eval]
        calc ∑ i, (c i : ℂ) * eval z (map (Int.castRingHom ℂ) (g i))
            = ∑ i, (c i : ℂ) * (w n (x i) z * eval z (map (Int.castRingHom ℂ) h) * (A.h z : ℂ) ^ n) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [hwrep n (x i) e e' (g i) h z (hg i) hh he (hgy i) hzP]
          _ = (∑ i, (c i : ℂ) * w n (x i) z) * (eval z (map (Int.castRingHom ℂ) h) * (A.h z : ℂ) ^ n) := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun i _ => ?_
              ring
          _ = 0 := by rw [hz0, zero_mul]
  choose φ hinj hdisc hlat hnorm using key
  refine ⟨fun n => Module.finrank ℤ (chartLat y A.a n), φ, hinj, hdisc, fun n _ => hlat n, ?_, ?_, ?_, ?_⟩
  · intro n c s hc hs
    rw [hnorm, ← Real.sqrt_sq hc]
    refine Real.sqrt_le_sqrt ?_
    calc ∫ z, ‖w n s z‖ ^ 2 ∂μ ≤ ∫ _, c ^ 2 ∂μ :=
          integral_mono_of_nonneg (ae_of_all _ fun z => by positivity) (integrable_const _)
            (hae.mono fun z hz => by
              show ‖w n s z‖ ^ 2 ≤ c ^ 2
              rw [← hwnorm n s z hz]
              exact pow_le_pow_left₀ (secNormAt_nonneg _ _ _ _ _)
                (secNormAt_le hc (isBoundedAt_of_isBoundedH hs hz)) 2)
      _ = c ^ 2 := by simp
  · intro n k s t st ht hst
    rw [hnorm, hnorm]
    refine Real.sqrt_le_sqrt (integral_mono_of_nonneg (ae_of_all _ fun z => by positivity) (hint n s)
      (hae.mono fun z hz => ?_))
    have h1 : ‖w k t z‖ ≤ 1 := by
      rw [← hwnorm k t z hz]
      refine secNormAt_le zero_le_one fun dg dh g h hg hh hd he => ?_
      rw [one_mul]
      exact ht dg dh g h z hg hh hd he hz
    show ‖w (n + k) st z‖ ^ 2 ≤ ‖w n s z‖ ^ 2
    rw [hwmul n k s t st hst z hz, norm_mul, mul_pow]
    exact mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) h1)
  · exact ⟨C, fun n => le_trans (by exact_mod_cast (finite_chartLat y A.a n (hfin n)).2) (hC n)⟩
  · intro n s
    rw [hnorm, sectionL2Norm]
    congr 1
    refine integral_congr_ae (hae.mono fun z hz => ?_)
    simp only [hwnorm n s z hz]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial BlockImageHilb

noncomputable section

namespace PullConeDegree

section Lemmas

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  [CharZero Ω]


omit [CharZero Ω] in
theorem isWeightedHomogeneous_of_isMultiHomog {f : MvPolynomial (Σ k, ι k) ℚ} {a : K → ℕ}
    (hf : IsMultiHomog f a) : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a := by
  intro m hm
  funext k
  rw [weight_blockWeight_apply]
  exact hf m (mem_support_iff.mpr hm) k


omit [CharZero Ω] in
theorem isMultiHomog_of_isWeightedHomogeneous {f : MvPolynomial (Σ k, ι k) ℚ} {a : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a) : IsMultiHomog f a := by
  intro m hm k
  rw [← weight_blockWeight_apply, hf (mem_support_iff.mp hm)]


omit [DecidableEq K] [CharZero Ω] in
theorem prod_X_pow_eq_monomial (a : K → ℕ) :
    (∏ k, MvPolynomial.X k ^ a k : MvPolynomial K Ω) = monomial (Finsupp.equivFunOnFinite.symm a) 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp

theorem coeff_mConeMapQ (y : (Σ k, ι k) → Ω) (f : MvPolynomial (Σ k, ι k) ℚ) (n : K → ℕ) :
    AddMonoidAlgebra.coeff (mConeMapQ y f) (Finsupp.equivFunOnFinite.symm n) =
      aeval y (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) n f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial m r =>
    have hm := isWeightedHomogeneous_monomial (NumbersDVR.blockWeight ι) m r rfl
    rw [mConeMapQ_eq y hm, prod_X_pow_eq_monomial, C_mul_monomial, mul_one, coeff_monomial,
      weightedHomogeneousComponent_of_mem (n := Finsupp.weight (NumbersDVR.blockWeight ι) m) hm]
    by_cases h : n = Finsupp.weight (NumbersDVR.blockWeight ι) m
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun h' => h (Finsupp.equivFunOnFinite.symm.injective h').symm), map_zero]
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, hp, hq, map_add (f := _), map_add (f := _)]


omit [DecidableEq K] [CharZero Ω] in
theorem exists_dvd_monomial (N : ℕ) (hne : ∀ k, Nonempty (ι k)) (μ : (Σ k, ι k) →₀ ℕ)
    (hμ : ∀ k, N * Fintype.card (ι k) ≤ ∑ i, μ ⟨k, i⟩) (r : ℚ) :
    ∃ c : ∀ k, ι k, (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℚ)) ^ N ∣ monomial μ r := by
  have hc : ∀ k, ∃ i, N ≤ μ ⟨k, i⟩ := by
    intro k
    by_contra h
    simp only [not_exists, not_le] at h
    have hlt := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty (α := ι k)) (fun i _ => h i)
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm] at hlt
    exact absurd (hμ k) (not_le.mpr hlt)
  choose c hc using hc
  refine ⟨c, ?_⟩
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun i => by simp), Fintype.prod_sigma, ← Finset.prod_pow]
  refine Dvd.dvd.mul_left (Finset.prod_dvd_prod_of_dvd _ _ fun k _ => ?_) _
  exact (pow_dvd_pow _ (hc k)).trans
    (Finset.dvd_prod_of_mem (fun i => (X ⟨k, i⟩ : MvPolynomial (Σ k, ι k) ℚ) ^ μ ⟨k, i⟩) (Finset.mem_univ (c k)))

end Lemmas

theorem proof : PullConeDegree.Statement := by
  classical
  intro K _ ι _ Ω _ _ y D e L N hy hL hN d g hg hd
  have hne : ∀ k, Nonempty (ι k) := fun k => (hy k).elim fun i _ => ⟨i⟩

  have hgI : g ∈ coneNullIdeal y L := by
    rw [g.as_sum]
    refine Ideal.sum_mem _ fun μ hμ => ?_
    obtain ⟨c, hc⟩ := exists_dvd_monomial N hne μ
      (fun k => by rw [hg μ hμ k]; have := hd k; omega) (AddMonoidAlgebra.coeff g μ)
    exact Ideal.mem_of_dvd _ hc (hN c)
  have hI : coneNullIdeal y L = RingHom.ker (mConeMapQ y) ⊔
      Ideal.span (Set.range fun j => map (Int.castRingHom ℚ) (L j)) := by
    rw [coneNullIdeal, Ideal.span_union, ← map_mCoordIdeal]
    rfl
  rw [hI, Submodule.mem_sup] at hgI
  obtain ⟨u, hu, v, hv, huv⟩ := hgI
  obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp hv

  have hmapL : ∀ j, mConeMapQ y (map (Int.castRingHom ℚ) (L j)) =
      monomial (Finsupp.equivFunOnFinite.symm e) (aeval y (L j)) := by
    intro j
    have h : IsMultiHomog (map (Int.castRingHom ℚ) (L j)) e := fun m hm => hL j m (support_map_subset _ _ hm)
    rw [mConeMapQ_eq y (isWeightedHomogeneous_of_isMultiHomog h), prod_X_pow_eq_monomial, C_mul_monomial, mul_one,
      ← algebraMap_int_eq, aeval_map_algebraMap]
  have hψg : mConeMapQ y g =
      ∑ j, mConeMapQ y (b j) * monomial (Finsupp.equivFunOnFinite.symm e) (aeval y (L j)) := by

    rw [← huv, map_add (f := _), RingHom.mem_ker.mp hu, zero_add, ← hb, map_sum]
    simp only [map_mul, hmapL]

  refine ⟨fun j => weightedHomogeneousComponent (NumbersDVR.blockWeight ι) (d - e) (b j),
    fun j => isMultiHomog_of_isWeightedHomogeneous (weightedHomogeneousComponent_isWeightedHomogeneous _ _), ?_⟩
  have hc := congrArg (AddMonoidAlgebra.coeff · (Finsupp.equivFunOnFinite.symm d)) hψg
  rw [mConeMapQ_eq y (isWeightedHomogeneous_of_isMultiHomog hg), prod_X_pow_eq_monomial, C_mul_monomial, mul_one,
    coeff_monomial, if_pos rfl, coeff_sum] at hc
  rw [hc]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hle : Finsupp.equivFunOnFinite.symm e ≤ Finsupp.equivFunOnFinite.symm d :=
    Finsupp.le_def.mpr fun k => by simp only [Finsupp.coe_equivFunOnFinite_symm]; have := hd k; omega
  have hsub : Finsupp.equivFunOnFinite.symm d - Finsupp.equivFunOnFinite.symm e =
      Finsupp.equivFunOnFinite.symm (d - e) := by
    ext k
    simp
  rw [coeff_mul_monomial', if_pos hle, hsub, coeff_mConeMapQ]

end PullConeDegree

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem ProjFSMass.proof : ProjFSMass.Statement := by
  intro D Ω _ _ κ _ x e m hfr hFS
  exact ⟨gbPsi e, gb_isGoodProj hfr, gb_ptsIntegralAt hfr hFS⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
