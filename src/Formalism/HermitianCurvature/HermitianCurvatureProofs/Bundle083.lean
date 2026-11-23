module

public import Formalism.HermitianCurvature.Bundle004
public import Formalism.FormalDegreeBessel.Bundle002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle080
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleOfUnitWords
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SplLen
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMP2
public import Formalism.FormalDegreeBessel.FinalG
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle079
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle045
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle072
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SeminormCompletion
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle029
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.ContMDiffMap

@[expose] public section

section

open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.BigCellZetaMinors

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

variable {k r : ℕ}

theorem one_uw (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mat k r) ∈ UWset k r z := by
  refine ⟨?_, fun a => by simp, by simp⟩
  simp [UH]

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem dmin_sgs (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (g : Mat k r) (l : Fin (r + 2)) :
    Dmin k r D.z D.z' (sgs p g) l = Dmin k r D.z D.z' g l := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have hs : (Matrix.of p.1.2 * Matrix.of p.1.1 : Mat k r)⁻¹ ∈ Sset k r D.z := by
    rw [Matrix.mul_inv_rev]
    exact ⟨_, BigCellInversePair.uw_inv h1, _, WeylGroupFacts.mem_n_inv h2, rfl⟩
  have hs' : (Matrix.of p.2.2 * Matrix.of p.2.1 : Mat k r) ∈ Sset k r D.z' :=
    (sGroup k r D.z' D.z'_mem).2.1 _ ⟨1, one_uw _, _, h4, (Matrix.one_mul _).symm⟩ _
      ⟨_, h3, 1, WeylGroupFacts.mem_n_one, (Matrix.mul_one _).symm⟩
  rw [B5.sgs_eq]
  exact dInv k r D.z D.z' D.z_mem D.z'_mem _ hs _ hs' g l

theorem cmin_gq (D : RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ} (hq : q ∈ QDom k r D.z D.z') (a : Fin r) :
    cmin k r D.z D.z' (gq D q) a = q.1 a :=
  (bigCellMinors k r D.z D.z' q.1 (D.μsec q.2) D.z_mem D.z'_mem).2.1 hq.1 a

theorem zeta_gq (D : RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ} (hq : q ∈ QDom k r D.z D.z') :
    zeta k r D.z D.z' (gq D q) = q.2 := by
  have hz := (bigCellMinors k r D.z D.z' q.1 (D.μsec q.2) D.z_mem D.z'_mem).2.2 hq.1
  rw [BigCellHermitian.herm_bigCell _ _ D.z_mem D.z'_mem, (D.sec.2 q.2 hq.2).2] at hz
  exact hz

end Formalism.FourierDecayAlt.P.BigCellZetaMinors

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

end Formalism.FourierDecayAlt.P
end
end

section

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxA3

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

theorem _root_.Formalism.FourierDecayAlt.P.big_cell_orbit_set : GqOm := by
  intro k r Wp Wq _ _ _ _ D
  have hnull : (volume : Measure ((Fin r → ℂ) × ℂ))
      (Set.univ ×ˢ {w : ℂ | Complex.normSq w = Formalism.QuantumDeterminants.Tz k r D.z * Formalism.QuantumDeterminants.Tz k r D.z'}) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    have h0 : (volume : Measure ℂ)
        {w : ℂ | Complex.normSq w = Formalism.QuantumDeterminants.Tz k r D.z * Formalism.QuantumDeterminants.Tz k r D.z'} = 0 := by
      apply measure_mono_null (t := Metric.sphere (0 : ℂ)
        (Real.sqrt (Formalism.QuantumDeterminants.Tz k r D.z * Formalism.QuantumDeterminants.Tz k r D.z')))
      · intro w hw
        simp only [Set.mem_setOf_eq] at hw
        simp only [Metric.mem_sphere, dist_zero_right]
        rw [← hw, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
      · exact Measure.addHaar_sphere _ _ _
    rw [h0, mul_zero]
  rw [ae_restrict_iff' (Formalism.FourierDecayAlt.P.B7.measurableSet_Qset D)]
  filter_upwards [compl_mem_ae_iff.mpr hnull] with q hq hqQ
  apply Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom D
  simp only [B.Qset, Set.mem_setOf_eq] at hqQ
  unfold Formalism.QuantumDeterminants.bcWeight at hqQ
  split_ifs at hqQ with hle
  · refine ⟨?_, ?_⟩
    · intro a ha
      have hp : (∏ b : Fin r, ‖q.1 b‖ ^ (2 * (Formalism.QuantumDeterminants.Mdim k r b - 2))) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ a)
        rw [ha, norm_zero]
        apply zero_pow
        have := a.isLt
        unfold Formalism.QuantumDeterminants.Mdim
        omega
      rw [hp, zero_mul] at hqQ
      exact lt_irrefl _ hqQ
    · refine lt_of_le_of_ne hle ?_
      intro heq
      exact hq ⟨Set.mem_univ _, heq.symm⟩
  · exact absurd hqQ (lt_irrefl _)

end Formalism.FourierDecayAlt.P.JFxA3
end
end

section

open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxDs1

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jConv_of_jDom : Formalism.FourierDecayAlt.JF.JDom → Formalism.FourierDecayAlt.JF.JConv := by
  intro hD k r Wp Wq _ _ _ _ _ _ D A F hT hC
  obtain ⟨hmeas, hbd⟩ := hD k r Wp Wq D A 0 F hT hC
  have hx : Continuous (fun p : SS k r => xiP D p) := by
    clear hmeas hbd hD hT hC
    unfold xiP psi ell
    refine Continuous.mul ?_ (Continuous.star ?_)
    · refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        (Complex.continuous_re.comp (continuous_const.mul (continuous_finsetSum _ fun a _ => ?_)))))
      split_ifs
      · simp only [Matrix.of_apply]; fun_prop
      · simp only [Matrix.of_apply, Matrix.mulVec, dotProduct]; fun_prop
    · refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        (Complex.continuous_re.comp (continuous_const.mul (continuous_finsetSum _ fun a _ => ?_)))))
      split_ifs
      · simp only [Matrix.of_apply]; fun_prop
      · simp only [Matrix.of_apply, Matrix.mulVec, dotProduct]; fun_prop
  have h0 : (0 : ℕ) + 0 ≤ 0 := le_rfl
  refine ⟨?_, ?_⟩
  · intro g hg
    obtain ⟨b, hb, hbb⟩ := hbd {g} isCompact_singleton (Set.singleton_subset_iff.mpr hg)
    have hbg := hbb [] [] (by simp) (by simp) h0 g (Set.mem_singleton g)
    have hm := hmeas [] [] (by simp) (by simp) h0 g hg
    refine Integrable.mono' hb (hx.aestronglyMeasurable.smul hm) ?_
    filter_upwards [hbg] with p hp
    calc ‖xiP D p • rho D p F g‖ = ‖xiP D p‖ * ‖rho D p F g‖ := norm_smul _ _
      _ ≤ 1 * ‖rho D p F g‖ := by gcongr; exact SmoothnessOnGoodSet.norm_xiP D p
      _ = ‖rho D p (dLR (List.map (AdL p) []) (List.map (AdR p) []) F) g‖ := by rw [one_mul]; rfl
      _ ≤ b p := hp
  · intro K hK hKO
    obtain ⟨b, hb, hbb⟩ := hbd K hK hKO
    exact ⟨b, hb, fun g hg => hbb [] [] (by simp) (by simp) h0 g hg⟩

end Formalism.FourierDecayAlt.P.JFxDs1
end
end

section

theorem Formalism.FourierDecayAlt.P.capelli_rho_commute : Formalism.FourierDecayAlt.JF.CVRho := by
  exact Formalism.FourierDecayAlt.P.JFxE.cVRho
end

section

open Matrix Set
open scoped ComplexConjugate ContDiff Manifold Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def utv {k r m : ℕ} (ε T : ℝ) (Gp : Mat k r → ℝ) (om : Mat k r → Fin m → ℂ) (g : Mat k r) : Fin m → ℂ :=
  fun a => (Real.sqrt T : ℂ) * (Phh ε ((Gp g : ℝ) : ℂ) * om g a)

lemma utv_eq {k r m : ℕ} {ε T : ℝ} (hε : 0 < ε) (hT : 0 < T) (Gp : Mat k r → ℝ) (om : Mat k r → Fin m → ℂ)
    {g : Mat k r} (hg : ε / 2 < Gp g) : C6.unitOf T (Gp g) (om g) = utv ε T Gp om g := by
  have hx : 0 < Gp g := by linarith
  funext a
  simp only [C6.unitOf, utv, Phh, hh, Complex.ofReal_re, sc_one hε hg.le, one_mul, Pi.smul_apply,
    smul_eq_mul, sqrt_div_eq hT hx, Complex.ofReal_mul]
  ring

lemma utv_cd {k r m : ℕ} {ε T : ℝ} (hε : 0 < ε) {Gp : Mat k r → ℝ} {om : Mat k r → Fin m → ℂ}
    (hG : ContDiff ℝ ∞ (fun g => ((Gp g : ℝ) : ℂ))) (ho : ∀ a, ContDiff ℝ ∞ (fun g => om g a)) :
    ContDiff ℝ ∞ (utv ε T Gp om) := by
  refine contDiff_pi.2 fun a => ?_
  simp only [utv]
  exact contDiff_const.mul (((Phh_cd hε).comp hG).mul (ho a))

lemma sq2_unitOf_eq_one_of_sq2_eq_div {m : ℕ} {T Gv : ℝ} (hT : 0 < T) (hG : 0 < Gv) {v : Fin m → ℂ} (hv : C6.sq2 v = Gv / T) :
    C6.sq2 (C6.unitOf T Gv v) = 1 := by
  unfold C6.sq2 C6.unitOf at *
  simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Complex.normSq_ofReal]
  rw [← Finset.mul_sum, hv, Real.mul_self_sqrt (div_nonneg hT.le hG.le), div_mul_div_comm, mul_comm T Gv,
    div_self (mul_pos hG hT).ne']

lemma continuous_sum_squares (m : ℕ) : Continuous (C6.sq2 (m := m)) := by
  unfold C6.sq2
  exact continuous_finsetSum _ fun a _ => Complex.continuous_normSq.comp (continuous_apply a)

lemma norm_le_one_of_sq2_eq_one {m : ℕ} {v : Fin m → ℂ} (h : C6.sq2 v = 1) : ‖v‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => ?_
  have h1 : Complex.normSq (v a) ≤ 1 := by
    rw [← h]
    unfold C6.sq2
    exact Finset.single_le_sum (f := fun a => Complex.normSq (v a)) (fun i _ => Complex.normSq_nonneg _)
      (Finset.mem_univ a)
  have h2 : ‖v a‖ ^ 2 ≤ 1 := by rw [← Complex.normSq_eq_norm_sq]; exact h1
  nlinarith [norm_nonneg (v a)]

lemma spheres_compact (m m' : ℕ) :
    IsCompact {w : (Fin m → ℂ) × (Fin m' → ℂ) | C6.sq2 w.1 = 1 ∧ C6.sq2 w.2 = 1} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact (isClosed_eq ((continuous_sum_squares m).comp continuous_fst) continuous_const).inter
      (isClosed_eq ((continuous_sum_squares m').comp continuous_snd) continuous_const)
  · refine (Metric.isBounded_closedBall (x := (0 : (Fin m → ℂ) × (Fin m' → ℂ))) (r := 1)).subset ?_
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_prod_le_iff.2 ⟨norm_le_one_of_sq2_eq_one hw.1, norm_le_one_of_sq2_eq_one hw.2⟩

lemma bump_ext {F E : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (K O : Set F) (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (Pi : F → E) (hPi : ContDiffOn ℝ ∞ Pi O) :
    ∃ Φ : F → E, ContDiff ℝ ∞ Φ ∧ (∀ y ∈ K, Φ y = Pi y) ∧
      ∀ j : ℕ, ∃ B : ℝ, ∀ y ∈ K, ‖iteratedFDeriv ℝ j Φ y‖ ≤ B := by
  obtain ⟨V, hVo, hKV, hVO, -⟩ := exists_open_between_and_isCompact_closure hK hO hKO
  obtain ⟨χ, hχ0, hχ1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed (I := 𝓘(ℝ, F)) hVo.isClosed_compl
    hK.isClosed (disjoint_compl_left_iff_subset.2 hKV)
  have hχ : ContDiff ℝ ∞ (χ : F → ℝ) := contMDiff_iff_contDiff.1 χ.contMDiff
  have hΦ : ContDiff ℝ ∞ (fun y => χ y • Pi y) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ O
    · exact hχ.contDiffAt.smul (hPi.contDiffAt (hO.mem_nhds hx))
    · have hx' : x ∈ (closure V)ᶜ := fun h => hx (hVO h)
      have h0 : (fun y => χ y • Pi y) =ᶠ[𝓝 x] fun _ => (0 : E) := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx'] with y hy
        have hyV : y ∈ Vᶜ := fun h => hy (subset_closure h)
        simp [hχ0 hyV]
      exact contDiffAt_const.congr_of_eventuallyEq h0
  refine ⟨fun y => χ y • Pi y, hΦ, fun y hy => by simp [hχ1 hy], fun j => ?_⟩
  exact hK.exists_bound_of_continuousOn
    ((hΦ.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)).continuousOn)

end Formalism.FourierDecayAlt.P.AdmissibleLieWords

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem c6_fib_cost_of_pieces : C6.FibCostOfParts := by
  intro hU k r m m' om om' Gp T T' E _ _ Pi O hom hom' hGp hT hT' hsq hsq' hO hKO hPi ε hε i
  have hGcd : ContDiff ℝ ∞ (fun g => ((Gp g : ℝ) : ℂ)) := (poly_adm (n := 0) hGp).1
  have hGc : Continuous Gp := by
    have h := Complex.continuous_re.comp hGcd.continuous
    simp only [Function.comp_def, Complex.ofReal_re] at h
    exact h
  have ho : ∀ a, ContDiff ℝ ∞ (fun g => om g a) := fun a => (poly_adm (n := 0) (hom a)).1
  have ho' : ∀ a, ContDiff ℝ ∞ (fun g => om' g a) := fun a => (poly_adm (n := 0) (hom' a)).1
  have hu1 : ContDiff ℝ ∞ (utv ε T Gp om) := utv_cd hε hGcd ho
  have hu2 : ContDiff ℝ ∞ (utv ε T' Gp om') := utv_cd hε hGcd ho'
  have hψ : ContDiff ℝ ∞ (fun g => (utv ε T Gp om g, utv ε T' Gp om' g)) := hu1.prodMk hu2
  have hOε : IsOpen {g : Mat k r | ε / 2 < Gp g} := isOpen_lt continuous_const hGc

  have hsph : ∀ g ∈ GV k r, ε / 2 < Gp g →
      C6.unitOf T (Gp g) (om g) = utv ε T Gp om g ∧ C6.unitOf T' (Gp g) (om' g) = utv ε T' Gp om' g ∧
      (C6.unitOf T (Gp g) (om g), C6.unitOf T' (Gp g) (om' g)) ∈
        {w : (Fin m → ℂ) × (Fin m' → ℂ) | C6.sq2 w.1 = 1 ∧ C6.sq2 w.2 = 1} := by
    intro g hg hgt
    have hpos : 0 < Gp g := by linarith
    exact ⟨utv_eq hε hT Gp om hgt, utv_eq hε hT' Gp om' hgt, sq2_unitOf_eq_one_of_sq2_eq_div hT hpos (hsq g hg),
      sq2_unitOf_eq_one_of_sq2_eq_div hT' hpos (hsq' g hg)⟩
  obtain ⟨Φ, hΦ, hΦK, hΦb⟩ := bump_ext _ O (spheres_compact m m') hO hKO Pi hPi

  have hwl : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
      ∀ x ∈ wL u ++ wR v, inLie k r x.2 := by
    intro u v hu hv x hx
    rcases List.mem_append.mp hx with hx | hx
    · simp only [wL, List.mem_map] at hx
      obtain ⟨X, hX, rfl⟩ := hx
      exact (hu X hX).1
    · simp only [wR, List.mem_map, List.mem_reverse] at hx
      obtain ⟨X, hX, rfl⟩ := hx
      exact (hv X hX).1
  have hlen : ∀ u v : List (Mat k r), (wL u ++ wR v).length = u.length + v.length := by
    intro u v
    simp [wL, wR]
  choose C1 hC1 using hU k r m om Gp T hom hGp hT hsq ε hε
  choose C2 hC2 using hU k r m' om' Gp T' hom' hGp hT' hsq' ε hε
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∑ j ∈ Finset.range (i + 1), (|C1 j| + |C2 j|) := ⟨_, rfl⟩
  have hCM : ∀ j ≤ i, C1 j ≤ M ∧ C2 j ≤ M := by
    intro j hj
    have hmem : j ∈ Finset.range (i + 1) := Finset.mem_range.mpr (by omega)
    have hle := Finset.single_le_sum (f := fun j => |C1 j| + |C2 j|)
      (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hmem
    rw [← hM] at hle
    exact ⟨by linarith [le_abs_self (C1 j), abs_nonneg (C2 j)], by linarith [le_abs_self (C2 j), abs_nonneg (C1 j)]⟩
  have H : ∀ w, admitted i w → w ≠ [] → ∀ g ∈ {g : Mat k r | g ∈ GV k r ∧ ε ≤ Gp g},
      ‖Dw w (fun g => (utv ε T Gp om g, utv ε T' Gp om' g)) g‖ ≤
        M * gN g ^ (2 * (r + 1) * w.length + (r + 1)) := by
    rintro w ⟨u, v, hu, hv, hl, rfl⟩ - g ⟨hg, hge⟩
    have hgt : ε / 2 < Gp g := by linarith
    have hw := hwl u v hu hv
    have huv : C6.UnitWords k r u v (u.length + v.length) := ⟨hu, hv, rfl⟩
    have e1 : Dw (wL u ++ wR v) (utv ε T Gp om) g =
        Dw (wL u ++ wR v) (fun g' => C6.unitOf T (Gp g') (om g')) g :=
      Dw_congr_loc hw hOε (fun g' hg' hg'O => ((hsph g' hg' hg'O).1).symm) g hg hgt
    have e2 : Dw (wL u ++ wR v) (utv ε T' Gp om') g =
        Dw (wL u ++ wR v) (fun g' => C6.unitOf T' (Gp g') (om' g')) g :=
      Dw_congr_loc hw hOε (fun g' hg' hg'O => ((hsph g' hg' hg'O).2.1).symm) g hg hgt
    have f1 : Dw (wL u ++ wR v) (utv ε T Gp om) g =
        (Dw (wL u ++ wR v) (fun g => (utv ε T Gp om g, utv ε T' Gp om' g)) g).1 := by
      have h := congrFun (dw_clm (ContinuousLinearMap.fst ℝ (Fin m → ℂ) (Fin m' → ℂ)) (wL u ++ wR v) hψ) g
      simpa using h
    have f2 : Dw (wL u ++ wR v) (utv ε T' Gp om') g =
        (Dw (wL u ++ wR v) (fun g => (utv ε T Gp om g, utv ε T' Gp om' g)) g).2 := by
      have h := congrFun (dw_clm (ContinuousLinearMap.snd ℝ (Fin m → ℂ) (Fin m' → ℂ)) (wL u ++ wR v) hψ) g
      simpa using h
    have b1 := hC1 _ u v huv g hg hge
    have b2 := hC2 _ u v huv g hg hge
    rw [dLR_eq, ← e1, f1] at b1
    rw [dLR_eq, ← e2, f2] at b2
    have hexp : (r + 1) * (2 * (u.length + v.length) + 1) =
        2 * (r + 1) * (wL u ++ wR v).length + (r + 1) := by
      rw [hlen]; ring
    rw [hexp] at b1 b2
    have hY : 0 ≤ gN g ^ (2 * (r + 1) * (wL u ++ wR v).length + (r + 1)) :=
      pow_nonneg (le_trans zero_le_one (gN_ge_one hg)) _
    obtain ⟨m1, m2⟩ := hCM _ hl
    rw [Prod.norm_def]
    exact max_le (b1.trans (mul_le_mul_of_nonneg_right m1 hY)) (b2.trans (mul_le_mul_of_nonneg_right m2 hY))
  obtain ⟨C, -, hC⟩ := fdb (fun g => (utv ε T Gp om g, utv ε T' Gp om' g)) hψ
    {g : Mat k r | g ∈ GV k r ∧ ε ≤ Gp g} _
    (fun g hg => by rw [← (hsph g hg.1 (by linarith [hg.2])).1, ← (hsph g hg.1 (by linarith [hg.2])).2.1]
                    exact (hsph g hg.1 (by linarith [hg.2])).2.2)
    gN (fun g hg => gN_ge_one hg.1) (2 * (r + 1)) (r + 1) M i H i E Φ hΦ hΦb
  refine ⟨C, fun u v huv g hg hge => ?_⟩
  have hw := hwl u v huv.1 huv.2.1
  rw [dLR_eq]
  have e : Dw (wL u ++ wR v) (fun g' => Pi (C6.unitOf T (Gp g') (om g'), C6.unitOf T' (Gp g') (om' g'))) g =
      Dw (wL u ++ wR v) (fun g' => Φ (utv ε T Gp om g', utv ε T' Gp om' g')) g := by
    refine Dw_congr_loc hw hOε (fun g' hg' hg'O => ?_) g hg (show ε / 2 < Gp g by linarith)
    obtain ⟨h1, h2, h3⟩ := hsph g' hg' hg'O
    rw [← hΦK _ h3, h1, h2]
  rw [e]
  have hl : (wL u ++ wR v).length = i := by rw [hlen]; exact huv.2.2
  have hb := hC (wL u ++ wR v) (admissible_of_unit_words huv) hl.le g ⟨hg, hge⟩
  rw [hl] at hb
  have hexp : (2 * (r + 1) + (r + 1)) * i = 3 * (r + 1) * i := by ring
  rwa [hexp] at hb

theorem fibre_cost_estimate : C6.FibCost := c6_fib_cost_of_pieces fibre_unit_normalization

end Formalism.FourierDecayAlt.P
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

theorem isDom_omP {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') :
    Q.IsDom k r z z' 0 {g | 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := by
  refine ⟨?_, ?_⟩
  · have e : {g : Q.Mx k r | 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧
        ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} =
        {g | 0 < Formalism.QuantumDeterminants.Gf k r z z' g} ∩
          ⋂ a : Fin r, {g | Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := by
      ext g; simp
    rw [e]
    exact (isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.Ux8.cont_Gf k r z z')).inter
      (isOpen_iInter_of_finite fun a => isOpen_ne_fun (Formalism.FourierDecayAlt.P.Ux8.cont_Dmin k r z z' _) continuous_const)
  · rintro g ⟨-, hg⟩ s ⟨h, hh, m, hm, rfl⟩ s' ⟨h', hh', m', hm', rfl⟩
    have hs : h * m ∈ Sset k r z := ⟨h, hh, m, hm.1, rfl⟩
    have hs' : h' * m' ∈ Sset k r z' := ⟨h', hh', m', hm'.1, rfl⟩
    have hD : ∀ l, Dmin k r z z' (h * m * g * (h' * m')) l = Dmin k r z z' g l :=
      fun l => dInv k r z z' hz hz' _ hs _ hs' g l
    refine ⟨?_, fun a => by rw [hD]; exact hg.2 a⟩
    have e : Gf k r z z' (h * m * g * (h' * m')) = Gf k r z z' g := by
      unfold Gf
      rw [hD, hD]
    rw [e]
    exact hg.1

theorem coefficient_vector_preserves_form : CVPresFF := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ _ v J hJ Y s
  have hz := (T v).base.z_mem
  have hz' := (T v).base.z'_mem
  have hD : Q.IsDom S.G.k S.G.r (T v).base.z (T v).base.z' 0 (OmP S T v) := isDom_omP hz hz'
  have hC : Q.CV S.G.k S.G.r (Y : ℂ) J ∈
      Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) :=
    Formalism.FourierDecayAlt.P.operator_preserves_fusion_forms _ _ S.G.k S.G.r _ _ _ _ 0 _ (Y : ℂ) 0 0 hz hz' hD J hJ
  exact Formalism.FourierDecayAlt.P.Qx8.FFl_smul hC s

end Formalism.FourierDecayAlt.P.CutMP
end

section

theorem Formalism.FourierDecayAlt.P.q_radial_decomposition_of_pieces : Formalism.FourierDecayAlt.Q.RadialDecompositionOfParts :=
  radial_decomposition_of_parts
end
