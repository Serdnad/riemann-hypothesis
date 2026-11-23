module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle095
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle099
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle042
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open scoped ContDiff

noncomputable section

theorem RadialPrimitive.primitive_contDiff (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (c : ℝ) :
    ContDiff ℝ ∞ (fun t => ∫ τ in c..t, f τ) ∧ deriv (fun t => ∫ τ in c..t, f τ) = f := by
  have hd : deriv (fun t => ∫ τ in c..t, f τ) = f :=
    funext fun t => hf.continuous.deriv_integral f c t
  refine ⟨contDiff_infty_iff_deriv.2 ⟨fun t => ?_, by rw [hd]; exact hf⟩, hd⟩
  exact (hf.continuous.integral_hasStrictDerivAt c t).hasDerivAt.differentiableAt

theorem RadialPrimitive.proof : RadialPrimitive.Statement := by
  intro e a t₀ T ha ht₀ hconst hzero hint
  set c : ℝ := ((e + 1 : ℕ) : ℝ) with hc
  set g : ℝ → ℝ := fun τ => a τ * (c * τ ^ (e + 1 - 1)) with hg
  set P : ℝ → ℝ := fun t => ∫ τ in (0 : ℝ)..t, g τ with hP
  have hgs : ContDiff ℝ ∞ g := ha.mul (contDiff_const.mul (contDiff_id.pow _))
  obtain ⟨hPs, hPd⟩ := RadialPrimitive.primitive_contDiff g hgs 0
  have hrt : ∀ t, radialTransform (e + 1) a t = a t * t ^ (e + 1) - P t := fun t => rfl

  have hPc : ∀ t ∈ Set.Icc 0 t₀, P t = a 0 * t ^ (e + 1) := by
    intro t ht
    have h0 := radialTransform_eq_zero_of_const e a hconst ht
    rw [hrt, hconst t ht] at h0
    linarith
  set h : ℝ → ℝ := fun t => if t < t₀ then a 0 else P t / t ^ (e + 1) with hh
  have hlow : ∀ t, t < t₀ → h t = a 0 := fun t ht => if_pos ht
  have hpos : ∀ t, 0 < t → h t = P t / t ^ (e + 1) := by
    intro t ht
    by_cases h1 : t < t₀
    · rw [hlow t h1, hPc t ⟨ht.le, h1.le⟩, mul_div_assoc, div_self (pow_ne_zero _ ht.ne'), mul_one]
    · exact if_neg h1
  have hlowE : ∀ x, x < t₀ → h =ᶠ[nhds x] fun _ => a 0 := fun x hx =>
    Filter.eventually_of_mem (isOpen_Iio.mem_nhds hx) fun t ht => hlow t ht
  have hposE : ∀ x, 0 < x → h =ᶠ[nhds x] fun t => P t / t ^ (e + 1) := fun x hx =>
    Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hx) fun t ht => hpos t ht
  have hs : ContDiff ℝ ∞ h := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x < t₀
    · exact contDiffAt_const.congr_of_eventuallyEq (hlowE x hx)
    · have hx0 : 0 < x := lt_of_lt_of_le ht₀ (not_lt.1 hx)
      exact (hPs.contDiffAt.div (contDiff_id.pow _).contDiffAt (pow_ne_zero _ hx0.ne')).congr_of_eventuallyEq
        (hposE x hx0)

  set R : ℝ := max T t₀ with hR
  have hPz : ∀ t, R ≤ t → P t = 0 := by
    intro t ht
    have hTt : T ≤ t := le_trans (le_max_left _ _) ht
    have hgc : Continuous g := hgs.continuous
    have htail : ∫ τ in T..t, g τ = 0 := by
      have hcg : ∫ τ in T..t, g τ = ∫ τ in T..t, (0 : ℝ) :=
        intervalIntegral.integral_congr fun τ hτ => by
          rw [Set.uIcc_of_le hTt] at hτ
          simp [hg, hzero τ hτ.1]
      rw [hcg]
      simp
    have := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (a := 0) (b := T) (c := t)
      (hgc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _)
    simp only [hP]
    rw [← this, htail, add_zero]
    exact hint
  have hhz : ∀ t, R ≤ t → h t = 0 := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ht₀ (le_trans (le_max_right _ _) ht)
    rw [hpos t ht0, hPz t ht, zero_div]
  obtain ⟨hQs, hQd⟩ := RadialPrimitive.primitive_contDiff h hs R
  refine ⟨fun t => ∫ τ in R..t, h τ, hQs, ⟨R, fun t ht => ?_⟩, ?_, ?_, fun t ht => ⟨?_, ?_⟩⟩
  · have hcg : ∫ τ in R..t, h τ = ∫ τ in R..t, (0 : ℝ) :=
      intervalIntegral.integral_congr fun τ hτ => by
        rw [Set.uIcc_of_le ht] at hτ
        exact hhz τ hτ.1
    show ∫ τ in R..t, h τ = 0
    rw [hcg]
    simp
  · rw [hQd]
    exact hlow 0 ht₀
  · rw [hQd, (hlowE 0 ht₀).deriv_eq]
    simp
  · rw [hQd, hpos t ht, hrt, div_mul_cancel₀ _ (pow_ne_zero _ ht.ne')]
    ring
  · rw [hQd, (hposE t ht).deriv_eq, hrt]
    have hPt : HasDerivAt P (g t) t := (hgs.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt
    have hq : HasDerivAt (fun s => P s / s ^ (e + 1))
        ((g t * t ^ (e + 1) - P t * (((e + 1 : ℕ) : ℝ) * t ^ (e + 1 - 1))) / (t ^ (e + 1)) ^ 2) t :=
      hPt.div (hasDerivAt_pow (e + 1) t) (pow_ne_zero _ ht.ne')
    rw [hq.deriv]
    simp only [hg, hc, Nat.add_sub_cancel]
    have ht' : t ≠ 0 := ht.ne'
    push_cast
    field_simp
    ring

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ComplexSets Metric

noncomputable section

namespace NormalModelFibre

variable {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)

theorem firstCoords_mem_zeroSet {w : Fin n ⊕ Fin M.m → ℂ} (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) :
    IndefiniteRowSideFullHecke.ComplexSets.firstCoords w ∈ zeroSet J := by
  intro f hf
  have h1 : f ∈ M.ideal.comap
      (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin M.m) ℂ) := by
    rw [M.comap_eq]
    exact hf
  have h0 := hw _ (Ideal.mem_comap.1 h1)
  rw [eval_rename] at h0
  exact h0

theorem exists_mem_fibre {q : Fin n → ℂ} (hq : q ∈ zeroSet J) :
    ∃ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q := by
  have : M.ideal.IsPrime := M.isPrime
  have h0 : (0 : MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) ∉ normalModelSubmonoid M q := by
    intro h
    obtain ⟨f, hf, hf0⟩ := Submonoid.mem_map.1 h
    apply (Ideal.mem_primeCompl_iff).1 hf
    rw [RingHom.mem_ker]
    have h1 : rename Sum.inl f ∈ M.ideal := Ideal.Quotient.eq_zero_iff_mem.1 hf0
    have h2 : f ∈ J := by
      rw [← M.comap_eq]
      exact h1
    exact hq f h2
  have hle := le_nonZeroDivisors_of_noZeroDivisors h0
  have : Nontrivial (Localization (normalModelSubmonoid M q)) :=
    (IsLocalization.injective (M := normalModelSubmonoid M q)
      (S := Localization (normalModelSubmonoid M q)) hle).nontrivial
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (Localization (normalModelSubmonoid M q))
  obtain ⟨w, hw, hwq, -⟩ := ModelLocalizationMaximalPoint.proof n J q M P hP
  exact ⟨w, hw, hwq⟩

theorem fibre_finite (q : Fin n → ℂ) :
    {w | w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∧ IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q}.Finite := by
  choose P hPm hP using M.integral
  have hroots : (Set.univ.pi fun i : Fin M.m => {a : ℂ | ((P i).map (eval q)).IsRoot a}).Finite :=
    Set.Finite.pi fun i => Polynomial.finite_setOfPred_isRoot ((hPm i).map _).ne_zero
  refine (hroots.image fun y : Fin M.m → ℂ => Sum.elim q y).subset ?_
  rintro w ⟨hw, rfl⟩
  refine ⟨fun i => w (Sum.inr i), fun i _ => ?_, ?_⟩
  · exact IndefiniteRowSideFullHecke.ComplexSets.isRoot_map_eval_of_mem_zeroSetIn hw i (P i) (hP i)
  · funext s
    rcases s with i | i <;> rfl

theorem isClosed_zeroSetIn : IsClosed (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) := by
  have h : IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal = ⋂ f ∈ M.ideal, {z | eval z f = 0} := by
    ext z
    simp [IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn]
  rw [h]
  exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval f) continuous_const

theorem continuous_firstCoords : Continuous (IndefiniteRowSideFullHecke.ComplexSets.firstCoords (n := n) (m := M.m)) :=
  continuous_pi fun _ => continuous_apply _

theorem eventually_mem_of_fibre_subset {q : Fin n → ℂ} {U : Set (Fin n ⊕ Fin M.m → ℂ)} (hU : IsOpen U)
    (hfib : ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q → w ∈ U) :
    ∃ N ∈ 𝓝 q, ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w ∈ N → w ∈ U := by
  set K : Set (Fin n ⊕ Fin M.m → ℂ) := {w | w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∧
    IndefiniteRowSideFullHecke.ComplexSets.firstCoords w ∈ closedBall q 1} ∩ Uᶜ with hKdef
  have hKb : Bornology.IsBounded K :=
    (IndefiniteRowSideFullHecke.ComplexSets.NormalModelProper.proof n J M (closedBall q 1) isBounded_closedBall).subset
      Set.inter_subset_left
  have hKc : IsClosed K :=
    ((isClosed_zeroSetIn M).inter (isClosed_closedBall.preimage (continuous_firstCoords M))).inter
      hU.isClosed_compl
  have hK : IsCompact K := isCompact_of_isClosed_isBounded hKc hKb
  have hKi : IsClosed (IndefiniteRowSideFullHecke.ComplexSets.firstCoords '' K) :=
    (hK.image (continuous_firstCoords M)).isClosed
  have hq : q ∉ IndefiniteRowSideFullHecke.ComplexSets.firstCoords '' K := by
    rintro ⟨w, ⟨⟨hw, -⟩, hwU⟩, hwq⟩
    exact hwU (hfib w hw hwq)
  refine ⟨closedBall q 1 ∩ (IndefiniteRowSideFullHecke.ComplexSets.firstCoords '' K)ᶜ,
    inter_mem (closedBall_mem_nhds q one_pos) (hKi.isOpen_compl.mem_nhds hq), ?_⟩
  intro w hw hwN
  by_contra hwU
  exact hwN.2 ⟨w, ⟨⟨hw, hwN.1⟩, hwU⟩, rfl⟩

end NormalModelFibre

end

end GroundTheory.Heights₂.Heights
end
