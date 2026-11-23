module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle003
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle126
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle116
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle005
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle125
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle130
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AutomorphicArithmetic.CMTraceForms.Bundle001
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle127
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Formalism.LocalToGlobal.CharacterGerms.GeNatCast

@[expose] public section

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

section

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]


omit [FiniteDimensional ℂ Wp] in
theorem hsInner_self_eq_normSq (A : Wq →L[ℂ] Wp) : B.hsInner A A = ((‖B.hsVec A‖ ^ 2 : ℝ) : ℂ) := by
  unfold B.hsInner
  rw [inner_self_eq_norm_sq_to_K]
  simp

omit [FiniteDimensional ℂ Wp] in
theorem hsInner_zero_zero : B.hsInner (0 : Wq →L[ℂ] Wp) 0 = 0 := by
  simp [P.Topx1.hsInner_eq]

theorem levelForm_top_diag (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter)
    (a : C.LPt) :
    p.RR H (P.r + 1) w a a = Top.topOf P p.l0 p.T p.ν' p.m₀ p.Θ p.TP H w a a := by
  by_cases hg : D.IsLocPt a (P.r + 1) ∧ 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r a
  · unfold KB.Pl.RR D.RRplace
    rw [dite_eq_left ⟨hg.1, hg.1⟩, dite_eq_right (by omega), if_pos rfl]
    split_ifs with hw
    · subst hw
      exact (Formalism.FourierDecayAlt.P.top_of_empty Formalism.FourierDecayAlt.P.vector_valued_types Wp Wq P p.l0 p.T p.ν' p.m₀ p.Θ p.TP H a a p.hP p.hF
        hg.1 hg.1 hg.2 hg.2).symm
    · rfl
  · have hV : ∀ F, D.vecV p.T.base p.ν' p.m₀ F a = 0 := fun F => by
      unfold D.vecV
      rw [dite_eq_right hg]
    have ht : Top.topOf P p.l0 p.T p.ν' p.m₀ p.Θ p.TP H w a a = 0 := by
      simp only [Top.topOf, hV, ContinuousLinearMap.comp_zero, hsInner_zero_zero, mul_zero,
        Finset.sum_const_zero]
    rw [ht]
    unfold KB.Pl.RR D.RRplace
    split_ifs with h1 h2 h3 h4
    · omega
    · rw [hV, hsInner_zero_zero]
    · exact ht
    · rfl
    · rfl

end

theorem Ew_eq_norm_tv_sq : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ), TBB.Ew p (fun _ => 1) H (P.r + 1) w (TBB.bigPt P.r c) = ‖tv p H w c‖ ^ 2 := by
  intro Wp Wq _ _ _ _ _ _ P p H w c
  have h1 : TBB.normC (fun _ => 1) w = 1 := by simp [TBB.normC]
  unfold TBB.Ew TBB.NP
  rw [levelForm_top_diag, h1, div_one, PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  unfold Top.topOf
  simp only [hsInner_self_eq_normSq, ← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun ρ _ => ?_
  simp only [tv, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, TBB.TTp, KB.Pl.V]
  ring

end GlobalTheory.TopVec
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.Ahatv_mul_and_R0v_mul_mem_nfSpan_hats : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ b ∈ bset d, ∀ y : ℂ, d.L.Ahatv y * b ∈ nfSpan d (hats d.L) 0 0 1 ∧ d.L.R0v y * b ∈ nfSpan d (hats d.L) 0 0 1 := by
  first | exact @GlobalTheory.HatNF.GenMinus.minus_hats_pass_generators | exact GlobalTheory.HatNF.GenMinus.minus_hats_pass_generators | (intros; apply GlobalTheory.HatNF.GenMinus.minus_hats_pass_generators <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.Ahat_mul_and_R0_mul_mem_nfSpan_hats : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ b ∈ bset d, ∀ y : ℂ, d.L.Ahat y * b ∈ nfSpan d (hats d.L) 0 0 1 ∧ d.L.R0 y * b ∈ nfSpan d (hats d.L) 0 0 1 := by
  first | exact @GlobalTheory.HatNF.GenPlus.plus_hats_pass_generators | exact GlobalTheory.HatNF.GenPlus.plus_hats_pass_generators | (intros; apply GlobalTheory.HatNF.GenPlus.plus_hats_pass_generators <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.word_l_decomposition_nf_span : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (L : LevelData A P.r) (st : Start A) (s : ℂ), Comparison₂ d L st s → ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ w : List (Letter ℂ S), admitted st w → ∀ Y ∈ (ofWord L st w).inv, Y + 1 ∈ (ofWord L st w).inv → ∃ E : SlopeTestRemainingChoices S A, (∀ e e', E e e' ∈ nfSpan d ∅ 0 0 0) ∧ (ofWord L st w).l L Y = io (d.L.l0 Y) + kapL d.L * E := by
  first | exact @GlobalTheory.HatNF.WordL.word_l_shape | exact GlobalTheory.HatNF.WordL.word_l_shape | (intros; apply GlobalTheory.HatNF.WordL.word_l_shape <;> assumption)
end

section

open scoped ComplexOrder InnerProductSpace

namespace GlobalTheory.HatNF

section abstract

variable {V E ι : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem ev_symm_of_nonneg (ev : V →ₗ[ℂ] E) (T : Module.End ℂ V) (h : ∀ v, 0 ≤ ⟪ev v, ev (T v)⟫_ℂ) (v w : V) :
    ⟪ev w, ev (T v)⟫_ℂ = ⟪ev (T w), ev v⟫_ℂ := by
  have hd : ∀ u, ⟪ev u, ev (T u)⟫_ℂ = ⟪ev (T u), ev u⟫_ℂ := by
    intro u
    rw [← inner_conj_symm (ev (T u)) (ev u)]
    exact (Complex.conj_eq_iff_im.mpr (Complex.nonneg_iff.mp (h u)).2.symm).symm
  have h1 := hd (v + w)
  have h2 := hd (v + Complex.I • w)
  have h3 := hd v
  have h4 := hd w
  simp only [map_add (f := _), map_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    Complex.conj_I] at h1 h2
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2 - (1 / 2 + Complex.I / 2) * h3
    - (1 / 2 + Complex.I / 2 * (-Complex.I * Complex.I)) * h4
    + (1 / 2 : ℂ) * (⟪ev w, ev (T v)⟫_ℂ - ⟪ev (T w), ev v⟫_ℂ - ⟪ev v, ev (T w)⟫_ℂ + ⟪ev (T v), ev w⟫_ℂ) * hI

variable [Fintype ι] [DecidableEq ι]

theorem ev_symm_single (ev : V →ₗ[ℂ] E) (K : (ι → ℂ) →ₐ[ℂ] Module.End ℂ V)
    (h : ∀ f : ι → ℂ, (∀ i, 0 < f i) → ∀ v, 0 ≤ ⟪ev v, ev (K f v)⟫_ℂ) (i : ι) (v w : V) :
    ⟪ev w, ev (K (Pi.single i 1) v)⟫_ℂ = ⟪ev (K (Pi.single i 1) w), ev v⟫_ℂ := by
  have hp : ∀ j, (0 : ℂ) < ((Pi.single i 1 : ι → ℂ) + 1) j := by
    intro j
    by_cases hj : j = i
    · subst hj
      simpa using add_pos (zero_lt_one' ℂ) (zero_lt_one' ℂ)
    · simp [hj]
  have h1 := ev_symm_of_nonneg ev _ (h _ hp) v w
  simp only [map_add (f := _), map_one, LinearMap.add_apply, Module.End.one_apply, inner_add_left, inner_add_right] at h1
  linear_combination h1

theorem algHom_apply_eq_sum (ev : V →ₗ[ℂ] E) (K : (ι → ℂ) →ₐ[ℂ] Module.End ℂ V) (f : ι → ℂ) (v : V) :
    ev (K f v) = ∑ i, f i • ev (K (Pi.single i 1) v) := by
  have hf : f = ∑ i, f i • (Pi.single i 1 : ι → ℂ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hf]

  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]

theorem ev_adj (ev : V →ₗ[ℂ] E) (K : (ι → ℂ) →ₐ[ℂ] Module.End ℂ V)
    (h : ∀ f : ι → ℂ, (∀ i, 0 < f i) → ∀ v, 0 ≤ ⟪ev v, ev (K f v)⟫_ℂ) (f : ι → ℂ) (v w : V) :
    ⟪ev w, ev (K f v)⟫_ℂ = ⟪ev (K (fun i => star (f i)) w), ev v⟫_ℂ := by
  rw [algHom_apply_eq_sum, algHom_apply_eq_sum ev K (fun i => star (f i)), inner_sum, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, inner_smul_left, ev_symm_single ev K h]
  simp

theorem ev_single_le (ev : V →ₗ[ℂ] E) (K : (ι → ℂ) →ₐ[ℂ] Module.End ℂ V)
    (h : ∀ f : ι → ℂ, (∀ i, 0 < f i) → ∀ v, 0 ≤ ⟪ev v, ev (K f v)⟫_ℂ) (i : ι) (v : V) :
    ‖ev (K (Pi.single i 1) v)‖ ≤ ‖ev v‖ := by
  have hid : K (Pi.single i 1) (K (Pi.single i 1) v) = K (Pi.single i 1) v := by
    rw [← Module.End.mul_apply, ← map_mul, ← Pi.single_mul, mul_one]
  have h1 := ev_symm_single ev K h i v (K (Pi.single i 1) v)
  rw [hid] at h1
  set a := ev (K (Pi.single i 1) v)
  have h2 : ‖a‖ * ‖a‖ ≤ ‖a‖ * ‖ev v‖ := by
    calc ‖a‖ * ‖a‖ = ‖⟪a, a⟫_ℂ‖ := by
          rw [inner_self_eq_norm_sq_to_K]
          simp [sq]
      _ = ‖⟪a, ev v⟫_ℂ‖ := by rw [h1]
      _ ≤ _ := norm_inner_le_norm _ _
  rcases (norm_nonneg a).eq_or_lt with h0 | h0
  · rw [← h0]
    exact norm_nonneg _
  · exact le_of_mul_le_mul_left h2 h0

theorem ev_le (ev : V →ₗ[ℂ] E) (K : (ι → ℂ) →ₐ[ℂ] Module.End ℂ V)
    (h : ∀ f : ι → ℂ, (∀ i, 0 < f i) → ∀ v, 0 ≤ ⟪ev v, ev (K f v)⟫_ℂ) (f : ι → ℂ) (v : V) :
    ‖ev (K f v)‖ ≤ (∑ i, ‖f i‖) * ‖ev v‖ := by
  rw [algHom_apply_eq_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (ev_single_le ev K h i v) (norm_nonneg _)

end abstract

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

theorem kappa_ptAdj_ptB : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ f : M.Ty P → ℂ, PtAdj P Bs (d.κ f) ∧ PtB P Bs (d.κ f) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hN f
  classical
  let ev : (Fin P.r → ℂ) × Q.Mx P.k P.r →
      Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' →ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) := fun x =>
    { toFun := fun Φ => B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let K : (M.Ty P → ℂ) →ₐ[ℂ] Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :=
    (P5.Kfp.fstAlg _).comp d.κ
  have hpos : ∀ x, ∀ g : M.Ty P → ℂ, (∀ i, 0 < g i) → ∀ v, 0 ≤ ⟪ev x v, ev x (K g v)⟫_ℂ := fun x g hg v =>
    P5.kappaFibrePos Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hD.1 X d hN.1 hN.2.1 hN.2.2.1 hN.2.2.2 g hg v x.1 x.2
  refine ⟨fun Φ Ψ x _ => ?_, ∑ i, ‖f i‖, Finset.sum_nonneg fun _ _ => norm_nonneg _, fun Φ x _ => ?_⟩
  · rw [hN.2.2.1.1 f]
    exact ev_adj (ev x) K (hpos x) f Φ Ψ
  · exact ev_le (ev x) K (hpos x) f Φ

end GlobalTheory.HatNF
end

section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

noncomputable section

namespace GlobalTheory.PtTie

theorem emb_eq_of_inPsi {D : D7} {Q : Par D} (hp : Q.PinHost) {τ σ : D.host.E →+* ℂ} (hτ : InPsi Q.H τ)
    (hσ : InPsi Q.H σ) {x : D.host.E} (hx : x ∈ D.host.K) : τ x = σ x := by
  have hs : τ D.host.sqrtMinusD = σ D.host.sqrtMinusD := by
    rw [← hp.2.1]; exact hτ.trans hσ.symm
  have hx' : x ∈ IntermediateField.adjoin ℚ {D.host.sqrtMinusD} := hx
  induction hx' using IntermediateField.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff.1 hy]; exact hs
  | algebraMap q => simp
  | add a b ha hb iha ihb => rw [map_add (f := _), map_add (f := _), iha ha, ihb hb]
  | inv a ha iha => rw [map_inv₀, map_inv₀, iha ha]
  | mul a b ha hb iha ihb => rw [map_mul, map_mul, iha ha, ihb hb]

theorem prod_pow_wtA {D : D7} {Q : Par D} (hQ : Q.Pins) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j)
    {M : Type} [CommMonoid M] (F : (D.host.E →+* ℂ) → M) :
    ∏ τ : D.host.E →+* ℂ, F τ ^ (∑ i : Fin ((Q.Dw j).mult τ), wtA w (τ, (i : ℕ))) =
      ∏ t : D.what₂.Tau, (F (DV.tauEmb D t) ^ (∑ i, w.aP t i) *
        F (ComplexEmbedding.conjugate (DV.tauEmb D t)) ^ (∑ i, w.aM t i)) := by
  classical
  obtain ⟨hp, hq, -⟩ := hQ.2.2.2 j hj
  have hsw : ∀ τ : D.host.E →+* ℂ, ∑ i : Fin ((Q.Dw j).mult τ), wtA w (τ, (i : ℕ)) =
      ∑ t : D.what₂.Tau, ((if τ = DV.tauEmb D t then ∑ i : Fin ((Q.Dw j).mult τ), ext0 (w.aP t) (i : ℕ) else 0) +
        if τ = ComplexEmbedding.conjugate (DV.tauEmb D t) then
          ∑ i : Fin ((Q.Dw j).mult τ), ext0 (w.aM t) (i : ℕ) else 0) := by
    intro τ
    simp only [GlobalTheory.WeightExponents.wtA_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_add_distrib]
    split_ifs <;> simp
  have hs : ∀ {p m : ℕ} (f : Fin p → ℕ), m = p → ∑ i : Fin m, ext0 f i = ∑ i, f i := by
    rintro p m f rfl
    exact Finset.sum_congr rfl fun i _ => by simp [ext0, i.isLt]
  rw [Finset.prod_congr rfl fun τ _ => by rw [hsw τ, ← Finset.prod_pow_eq_pow_sum], Finset.prod_comm]
  refine Finset.prod_congr rfl fun t _ => ?_
  simp only [pow_add, pow_ite, pow_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
  simp only [Finset.mem_univ, if_true]
  have ht := hQ.1.2.2.2 t
  have hc : ¬ ComplexEmbedding.conjugate (DV.tauEmb D t) (Q.H.rt : D.host.E) = Q.H.rt0 :=
    GlobalTheory.WeightExponents.not_inPsi_conj hQ.1 t
  rw [hs _ (by rw [Datum.mult, if_pos ht, hp]), hs _ (by rw [Datum.mult, if_neg hc, hq])]

theorem emb_piBarO {D : D7} (EX : ErrX D) (i : Fin 2) (τ : D.host.E →+* ℂ) :
    τ ((piBarO EX i : 𝓞 D.host.E) : D.host.E) = starRingEnd ℂ (τ ((EX.piG i : 𝓞 D.host.E) : D.host.E)) := by
  have h1 : ((piBarO EX i : 𝓞 D.host.E) : D.host.E) = ((barE D (EX.piG i) : 𝓞 D.host.E) : D.host.E) := by
    rw [barE_eq_conj]; rfl
  rw [h1]
  exact IsCMField.complexEmbedding_complexConj D.host.E τ _

theorem nrm_eq_prod {D : D7} {Q : Par D} (hQ : Q.Pins) {j : ℕ} (hj : InR D j) (EX : ErrX D) (w : WeightFamilies.Wt D j)
    {τ : D.host.E →+* ℂ} (hτ : InPsi Q.H τ) :
    nrm (Q.Dw j) Q.c (wtA w) (EX.piG 0 * EX.piG 1) =
      ∏ i : Fin 2, embK Q.c τ (EX.piG i) ^ Dplus w * embK Q.c τ (piBarO EX i) ^ Dminus w := by
  have h1 : ∀ t i, embK Q.c (DV.tauEmb D t) (EX.piG i) = embK Q.c τ (EX.piG i) := fun t i =>
    Subtype.ext (emb_eq_of_inPsi hQ.1 (hQ.1.2.2.2 t) hτ (EX.piG_K i))
  have h2 : ∀ t i, embK Q.c (ComplexEmbedding.conjugate (DV.tauEmb D t)) (EX.piG i) = embK Q.c τ (piBarO EX i) :=
    fun t i => Subtype.ext (by
      rw [embK_coe, embK_coe, emb_piBarO, ← emb_eq_of_inPsi hQ.1 (hQ.1.2.2.2 t) hτ (EX.piG_K i)]
      simp)
  unfold nrm Dplus Dminus
  rw [prod_pow_wtA hQ hj w fun σ => embK Q.c σ (EX.piG 0 * EX.piG 1)]
  simp only [map_mul, h1, h2]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, Fin.prod_univ_two,
    mul_pow, mul_pow]
  ring

theorem map_nnW {D : D7} (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) {j : ℕ}
    (w : WeightFamilies.Wt D j) :
    ((nnW B hinj EX w : 𝓞 B.KO) : B.KO) = ∏ i : Fin 2, ((iE D hinj B (EX.piG i) : 𝓞 B.KO) : B.KO) ^ Dplus w *
      ((iE D hinj B (piBarO EX i) : 𝓞 B.KO) : B.KO) ^ Dminus w := by
  unfold nnW
  simp only [RingOfIntegers.coe_eq_algebraMap, map_prod, map_mul, map_pow]

theorem nrm_eq_nnW : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j), nrm (T.Q.Dw j) T.Q.c (wtA w) (EX.piG 0 * EX.piG 1) = ((nnW (recB h.toLawsCore) hinj EX w : 𝓞 T.Q.c.F) : T.Q.c.F) := by
  intro D T h j hj hinj EX w
  obtain ⟨τ, hτ, hE⟩ := exists_inPsi_iE_eq_embK D T h hinj
  rw [nrm_eq_prod h.pins hj EX w hτ]
  refine Eq.trans ?_ (map_nnW (recB h.toLawsCore) hinj EX w).symm
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← hE, ← hE]

end GlobalTheory.PtTie
end
end

section

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.ScalarOfRun

theorem ceil_toNat (x : ℝ) : ⌈x⌉.toNat = ⌈x⌉₊ := rfl

theorem barE_eq_piBarO {D : D7} (EX : ErrX D) (i : Fin 2) : barE D (EX.piG i) = piBarO EX i := by
  apply IsFractionRing.injective (𝓞 D.host.E) D.host.E
  exact barE_eq_conj D (EX.piG i)

theorem cP_of_mem_small (D : D7) (Tn : ℕ+) (N p : ℕ) (hp : p ∈ D.host.small) :
    (depPageOf D Tn (GlobalTheory.RunDepth.vdOf D)).cP N p = ⌈(padicValNat p D.host.QS : ℝ) * (N : ℝ)⌉.toNat := by
  unfold DepPage.cP
  rw [if_pos (show (depPageOf D Tn (GlobalTheory.RunDepth.vdOf D)).IsRam p from Or.inl hp)]
  show ⌈GlobalTheory.RunDepth.vdOf D p * _⌉.toNat = _
  rw [GlobalTheory.RunDepth.vdOf, if_pos hp]

theorem cP_of_isRam_of_notMem_small (D : D7) (Tn : ℕ+) {j : ℕ} (w : WeightFamilies.Wt D j) (p : ℕ) (hp : p ∉ D.host.small)
    (hr : (depPageOf D Tn (GlobalTheory.RunDepth.vdOf D)).IsRam p) :
    (depPageOf D Tn (GlobalTheory.RunDepth.vdOf D)).cP (WeightAlgebra.DF w) p = Formalism.MainNotions.DIV.Cons.cHalf w := by
  unfold DepPage.cP
  rw [if_pos hr, ceil_toNat]
  show ⌈GlobalTheory.RunDepth.vdOf D p * _⌉₊ = _
  rw [GlobalTheory.RunDepth.vdOf, if_neg hp, Formalism.MainNotions.DIV.Cons.cHalf]
  congr 1; ring

theorem depth_page_first_zeta_factor_eq_prime_power (D : D7) (Tn : ℕ+) {j : ℕ} (wL wF : WeightFamilies.Wt D j) :
    (depPageOf D Tn (GlobalTheory.RunDepth.vdOf D)).Z1 (WeightAlgebra.DF wL) (WeightAlgebra.DF wF) =
      pPow D (Tn * c2 D wL + c2 D wF) (Tn * Formalism.MainNotions.DIV.Cons.cHalf wL + Formalism.MainNotions.DIV.Cons.cHalf wF)
        (Tn * Formalism.MainNotions.DIV.Cons.cHalf wL + Formalism.MainNotions.DIV.Cons.cHalf wF) := by
  have hq := fun w => cP_of_isRam_of_notMem_small D Tn (j := j) w D.host.q D.host.q_notMem_small (Or.inr (Or.inl rfl))
  have hd := fun w => cP_of_isRam_of_notMem_small D Tn (j := j) w D.host.d D.host.d_notMem_small (Or.inr (Or.inr rfl))
  have hS := UpperTheory.prod_primeFactors_pow_ceil_padicValNat_mul_eq_pow D.host.QS Tn (WeightAlgebra.DF wL) (WeightAlgebra.DF wF) D.host.QS_pos.ne'
  unfold pPow c2
  rw [← hS]
  conv_rhs => enter [1, 2]; rw [← hq wL, ← hq wF]
  conv_rhs => enter [2]; rw [← hd wL, ← hd wF]
  unfold DepPage.Z1
  congr 2
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp' : p ∈ D.host.small := (Finset.mem_filter.1 hp).1
  rw [cP_of_mem_small D Tn _ p hp', cP_of_mem_small D Tn _ p hp']
  rfl

theorem sigAt_eq_sigRec : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (j : ℕ), InR D j → HalfEX T.toCore EX → ∀ (K : Type) [Field K] [NumberField K] [Algebra (𝓞 D.host.E) K] (φ : T.Q.c.F →+* K), (∀ x : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) K x = φ ((iE D hinj (recB h.toLawsCore) x : 𝓞 T.Q.c.F) : T.Q.c.F)) → sigAt (Dw := T.Q.Dw j) (H := T.Q.H) (LL := K) (GlobalTheory.RunDepth.depOf T.toCore EX Tp hK) j = φ ((sigRec (recB h.toLawsCore) hinj EX (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO : 𝓞 T.Q.c.F) : T.Q.c.F) := by
  intro D L Pm Tp hK T h hinj EX j hj hE K _ _ _ φ hφ
  have hM : LawsM T.toCore := h.toLawsCore.toLawsM
  let ψ : 𝓞 T.Q.c.F →+* K := φ.comp (algebraMap (𝓞 T.Q.c.F) T.Q.c.F)
  have hψ : ∀ x, algebraMap (𝓞 D.host.E) K x = ψ (iE D hinj (recB h.toLawsCore) x) := hφ
  let Tn : ℕ+ := ⟨Tp.TO, GlobalTheory.RunDepth.TO_pos Tp⟩
  have hnn : nnKAt (H := T.Q.H) (LL := K) (GlobalTheory.RunDepth.depOf T.toCore EX Tp hK) j =
      ψ (nnW (recB h.toLawsCore) hinj EX (kaR Tp hK j)) := by
    letI : StarRing (𝓞 D.host.E) := starRingOfComm
    refine (nnKAt_depDataOf T.toCore EX _ _ _ _ _ _ _ hM hE j).trans ?_
    refine Eq.trans ?_ (map_prod ψ _ _).symm
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [barE_eq_piBarO, hψ, hψ]
    exact ((map_mul ψ _ _).trans (congrArg₂ (· * ·) (map_pow ψ _ _) (map_pow ψ _ _))).symm
  have hL := GlobalTheory.WeightExponents.DF_wtA hM.pins hj (lR Tp hK j)
  have hF := GlobalTheory.WeightExponents.DF_wtA hM.pins hj (fR Tp hK j)
  have hn : (fR Tp hK j).n = 8 * D.R.f * D.R.r + 4 := Tp.nP_eq
  show nnKAt (H := T.Q.H) (LL := K) (GlobalTheory.RunDepth.depOf T.toCore EX Tp hK) j *
      (((D.host.g 0 * D.host.g 1 : ℕ) : K) ^ (D.R.f * D.R.r * (8 * D.R.f * D.R.r + 4)) *
        (((depPageOf D Tn (GlobalTheory.RunDepth.vdOf D)).Z1 (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA (lR Tp hK j)))
          (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA (fR Tp hK j))) : ℕ) : K)) =
      ψ (sigRec (recB h.toLawsCore) hinj EX (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO)
  rw [hnn, hL, hF, depth_page_first_zeta_factor_eq_prime_power, ← hn, ← Nat.cast_pow, ← Nat.cast_mul, ← map_natCast ψ, ← map_mul]
  rfl

end GlobalTheory.ScalarOfRun
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem numOf_Dplus_Dminus : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ), InR D j → (numOf D L).Dplus j = ((∑ τ, ∑ i, (kaR Tp hK j).aP τ i : ℕ) : ℚ) ∧ (numOf D L).Dminus j = ((∑ τ, ∑ i, (kaR Tp hK j).aM τ i : ℕ) : ℚ) := by
  intro D L Pm Tp hK j hj
  have hb := (GlobalTheory.T.realPlaceLabel_bijective_card_eq_f D).1
  have h1 := hj.1
  have h2 := hj.2
  constructor
  · have e : (numOf D L).Dplus j =
        ∑ z : RPl D.R, ∑ i ∈ Finset.range (D.R.sigW j).1, DV.aPlusQ D j (plOf D z) i := rfl
    rw [e, hb.sum_comp (fun τ => ∑ i ∈ Finset.range (D.R.sigW j).1, DV.aPlusQ D j τ i)]
    push_cast
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← (hK j h1 h2 τ).1 i, ← kaWt_big D hK (even_nV Tp) j h1 h2 τ i, Int.cast_natCast]
    rfl
  · have e : (numOf D L).Dminus j =
        ∑ z : RPl D.R, ∑ i ∈ Finset.range (D.R.sigW j).2, DV.aMinusQ D j (plOf D z) i := rfl
    rw [e, hb.sum_comp (fun τ => ∑ i ∈ Finset.range (D.R.sigW j).2, DV.aMinusQ D j τ i)]
    push_cast
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_range, ← Equiv.sum_comp Fin.revPerm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 := kaWt_small D hK (even_nV Tp) j h1 h2 τ i
    have e2 := (hK j h1 h2 τ).2 (Fin.rev i)
    have e3 := congrArg (fun q : ℤ => (q : ℚ)) e1
    simp only [Int.cast_natCast, Int.cast_neg] at e3
    rw [e2, neg_neg] at e3
    exact e3.symm

end GlobalTheory.RunDepth
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

theorem _root_.GlobalTheory.T.firstRows_bound_and_sizes_bounds : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ), InR D j → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b →
  (∀ τ : D.host.E →+* ℂ, (Tp.TO : ℝ) * wtA (lR Tp hK j) (τ, 0) ≤ 3 * L.sc.b) ∧ ∀ z : RPl D.R, L.sc.w'' D.R.n ≤ (numOf D L).w j z ∧ (numOf D L).w j z ≤ 2 * L.sc.b := by
  first | exact @GlobalTheory.FirstRows.first_rows_and_sizes | exact GlobalTheory.FirstRows.first_rows_and_sizes | (intros; apply GlobalTheory.FirstRows.first_rows_and_sizes <;> assumption)
end
