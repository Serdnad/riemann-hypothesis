module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle118
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle105
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle090
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle021
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle110
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordMDecompositionSelfAdjoint
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleGD
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleInv
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleSS
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StarStartConjugationIdentity
public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle005
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle119
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle122
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle120
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle117
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001

@[expose] public section

section

noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.ThetaQuot

def fac (d : ℕ) (y z : ℂ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq y : ℝ) : ℂ) +
    (-(Real.pi : ℂ) * h1 d z y - (Real.pi : ℂ) / 2 * h1 d y y))

lemma fac_ne (d : ℕ) (y z : ℂ) : fac d y z ≠ 0 := Complex.exp_ne_zero _

lemma nonzeroIndexPlaces_adelicDataResized_eq (d : ℕ) (y : ℂ) (F : ℂ → ℂ) (z : ℂ) : W1 d y F z = fac d y z * F (z + y) := by
  simp only [W1, U1, fac, Complex.exp_add]; ring

lemma fac_mul (d : ℕ) (α : ℂ) (m : ℕ) (hm : (m : ℂ) = α * conj α) (y z : ℂ) :
    fac d (α * y) (α * z) = fac d y z ^ m := by
  simp only [fac]
  rw [← Complex.exp_nat_mul]
  congr 1
  rw [hm, ← Complex.mul_conj, ← Complex.mul_conj]
  simp only [h1, map_mul]
  ring

lemma not_half (d : ℕ) (hd : 0 < d) : ¬ InOK d (0 - 1 / 2) := by
  apply GlobalTheory.MomOne.ScaledQuot.not_inOK_neg_half <;> assumption

lemma inOK_mul (d : ℕ) (hd : d % 4 = 3) {α β : ℂ} (ha : InOK d α) (hb : InOK d β) : InOK d (α * β) := by
  obtain ⟨u, v, rfl⟩ := ha
  obtain ⟨u', v', rfl⟩ := hb
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d + 1 = 4 * k := ⟨(d + 1) / 4, by omega⟩
  have hs : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]; simp
  have hk' : (d : ℂ) + 1 = 4 * k := by exact_mod_cast hk
  have hw : wK d ^ 2 = wK d - k := by
    simp only [wK]
    linear_combination (((Real.sqrt d : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq - (1 / 4) * hs - (1 / 4) * hk'
  refine ⟨u * u' - k * v * v', u * v' + v * u' + v * v', ?_⟩
  push_cast
  linear_combination (v * v' : ℂ) * hw

lemma zero_of_pole {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (p : ℂ)
    (h : meromorphicOrderAt (fun z => F z / G z) p < 0) : G p = 0 := by
  by_contra hp
  have ha : AnalyticAt ℂ (fun z => F z / G z) p := (hF.analyticAt p).div (hG.analyticAt p) hp
  exact absurd ha.meromorphicOrderAt_nonneg (not_le.mpr h)

theorem theta_quot : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ (α : ℂ) (m : ℕ), InOK d α → α ≠ 0 → (m : ℂ) = α * conj α → ∃ ε : ℂ → ℂ, Ell M.L ε ∧ AnalyticAt ℂ ε 0 ∧ ε 0 = 1 ∧ Bd 1 (hat M.ι (C ω * logS) ε) ∧ (∀ z, θ z ≠ 0 → θ (α * z) = θ z ^ m * ε z) ∧ ∀ y z, θ (z + y) ≠ 0 → W1 d (α * y) θ (α * z) = W1 d y θ z ^ m * ε (z + y) := by
  intro d q _ M ω θ hd hd16 hsp hL hch hθ α m hα hα0 hm
  obtain ⟨hdiff, h0, -, hW, hz⟩ := hθ
  have hd4 : d % 4 = 3 := by omega
  have hA : Differentiable ℂ (fun z => θ (α * z)) := hdiff.comp (differentiable_id.const_mul α)
  have hB : Differentiable ℂ (fun z => θ z ^ m) := hdiff.pow m
  have hper : ∀ l ∈ M.L.lattice, ∀ z, θ (α * z) = fac d l z ^ m * θ (α * (z + l)) ∧
      θ z ^ m = fac d l z ^ m * θ (z + l) ^ m := by
    intro l hl z
    have hl' := (hL l).1 hl
    constructor
    · have := congrFun (hW _ (inOK_mul d hd4 hα hl')) (α * z)
      rw [nonzeroIndexPlaces_adelicDataResized_eq, fac_mul d α m hm] at this
      rw [← this, mul_add]
    · have := congrFun (hW _ hl') z
      rw [nonzeroIndexPlaces_adelicDataResized_eq] at this
      rw [← mul_pow, this]
  have hEε : Ell M.L (fun z => θ (α * z) / θ z ^ m) := by
    refine ⟨fun p => (hA.analyticAt p).meromorphicAt.div (hB.analyticAt p).meromorphicAt, ?_⟩
    intro l hl z
    obtain ⟨h1', h2'⟩ := hper l hl z
    show θ (α * (z + l)) / θ (z + l) ^ m = θ (α * z) / θ z ^ m
    rw [h1', h2', mul_div_mul_left _ _ (pow_ne_zero m (fac_ne d l z))]
  have hEη : Ell M.L (fun z => θ z ^ m / θ (α * z)) := by
    refine ⟨fun p => (hB.analyticAt p).meromorphicAt.div (hA.analyticAt p).meromorphicAt, ?_⟩
    intro l hl z
    obtain ⟨h1', h2'⟩ := hper l hl z
    show θ (z + l) ^ m / θ (α * (z + l)) = θ z ^ m / θ (α * z)
    rw [h1', h2', mul_div_mul_left _ _ (pow_ne_zero m (fac_ne d l z))]
  have hA0 : θ (α * 0) ≠ 0 := by simp [h0]
  have hB0 : θ 0 ^ m ≠ 0 := by simp [h0]
  have haε : AnalyticAt ℂ (fun z => θ (α * z) / θ z ^ m) 0 :=
    (hA.analyticAt 0).div (hB.analyticAt 0) hB0
  have haη : AnalyticAt ℂ (fun z => θ z ^ m / θ (α * z)) 0 :=
    (hB.analyticAt 0).div (hA.analyticAt 0) hA0
  have hns : ∀ β p : ℂ, InOK d β → β ≠ 0 → θ (β * p) = 0 → ¬ M.Small p := by
    intro β p hβ hβ0 hp hs
    have hp0 : PrimeTo d q 0 := ⟨1, one_pos, Nat.coprime_one_left q, 0, 0, by simp⟩
    have := (GlobalTheory.T.smallTorsion_killed_by_prime_powers d q M ω hd hd16 hsp hL hch).2.2.2 p β 0 hβ hβ0 hp0
      (by simpa using hz _ hp) hs
    exact not_half d hd.pos this.2
  have hbε : Bdd (hat M.ι (C ω * logS) (fun z => θ (α * z) / θ z ^ m)) := by
    refine GlobalTheory.T.cpSeriesCoeffBounded_taylor_elliptic_of_poles q M _ _ hch hEε haε fun p hp => ?_
    have := zero_of_pole hA hB p hp
    exact hns 1 p ⟨1, 0, by simp⟩ one_ne_zero (by simpa using (pow_eq_zero_iff'.1 this).1)
  have hbη : Bdd (hat M.ι (C ω * logS) (fun z => θ z ^ m / θ (α * z))) := by
    refine GlobalTheory.T.cpSeriesCoeffBounded_taylor_elliptic_of_poles q M _ _ hch hEη haη fun p hp => ?_
    exact hns α p hα hα0 (zero_of_pole hB hA p hp)
  obtain ⟨hh1, hh2, -, hh4, -⟩ := GlobalTheory.T.cpTransportedTaylorSeriesInChart_ringHom_laws q M.ι (C ω * logS) hch.2.1
  have hprod : hat M.ι (C ω * logS) (fun z => θ (α * z) / θ z ^ m) *
      hat M.ι (C ω * logS) (fun z => θ z ^ m / θ (α * z)) = 1 := by
    rw [← (hh1 _ _ haε haη).2.1]
    have e1 : ∀ᶠ z in 𝓝 (0 : ℂ), θ (α * z) ≠ 0 := hA.continuous.continuousAt.eventually_ne hA0
    have e2 : ∀ᶠ z in 𝓝 (0 : ℂ), θ z ^ m ≠ 0 := hB.continuous.continuousAt.eventually_ne hB0
    have := (hh1 _ (fun _ => (1 : ℂ)) (haε.mul haη) analyticAt_const).2.2.1 (by
      filter_upwards [nhdsWithin_le_nhds e1, nhdsWithin_le_nhds e2] with z h1' h2'
      show θ (α * z) / θ z ^ m * (θ z ^ m / θ (α * z)) = 1
      field_simp)
    refine Eq.trans this ?_
    rw [hh2]; simp
  have hε0 : θ (α * 0) / θ 0 ^ m = 1 := by simp [h0]
  have hmain : ∀ z, θ z ≠ 0 → θ (α * z) = θ z ^ m * (θ (α * z) / θ z ^ m) := by
    intro z hz'
    field_simp
  refine ⟨fun z => θ (α * z) / θ z ^ m, hEε, haε, hε0, ?_, hmain, ?_⟩
  · refine ((GlobalTheory.T.cpSeriesCoeffNormBounded_ring_laws q).2.2.2.2.1 _ _ hbε hbη hprod ?_).1
    rw [hh4]; simp [h0]
  · intro y z hyz
    rw [nonzeroIndexPlaces_adelicDataResized_eq, nonzeroIndexPlaces_adelicDataResized_eq, fac_mul d α m hm, ← mul_add, mul_pow, mul_assoc]
    exact congrArg _ (hmain _ hyz)

end GlobalTheory.MomOne.ThetaQuot
end
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.word_m_decomposition_self_adjoint : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (L : LevelData A P.r) (st : Start A) (s : ℂ), Comparison₂ d L st s → ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ w : List (Letter ℂ S), admitted st w → ∀ Y ∈ (ofWord L st w).inv, star Y = Y → Y - 1 ∈ (ofWord L st w).inv → ∃ E : SlopeTestRemainingChoices S A, (∀ e e', E e e' ∈ nfSpan d ∅ 0 0 0) ∧ (ofWord L st w).m L Y = io (d.L.m0 Y) + io (d.L.ζ * d.L.ζbi * d.L.GGi) * E := by
  first | exact @GlobalTheory.HatNF.MShapeNF.mshape | exact GlobalTheory.HatNF.MShapeNF.mshape | (intros; apply GlobalTheory.HatNF.MShapeNF.mshape <;> assumption)
end

section

namespace GlobalTheory.HatNF.GenMinus

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
open Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.K

noncomputable section

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {P : M.Par}

omit [Algebra ℂ A] [StarModule ℂ A] in
theorem star_listProd (l : List A) : star l.prod = (l.map star).reverse.prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.prod_cons, star_mul, ih, List.prod_append]

omit [StarModule ℂ A] in
theorem mem_span (d : Q.NFData P A) {b X : A} (hb : b ∈ bmon d) (hX : X ∈ hats d.L) :
    b * X ∈ nfSpan d (hats d.L) 0 0 1 := by
  unfold nfSpan
  refine Submodule.subset_span ⟨b, hb, [X], rfl, ?_⟩
  simp [hX]

omit [StarModule ℂ A] in
theorem kap_comm (d : Q.NFData P A) (h : HatHyp d) (f : M.Ty P → ℂ) (y : ℂ) :
    Commute (d.κ f) (d.L.Ahatv y) ∧ Commute (d.κ f) (d.L.R0v y) := by
  obtain ⟨-, -, hR, -, -, -, hk⟩ := h
  have hf : ∀ g ∈ d.L.fns, Commute (d.κ f) g := fun g hg => hR.2.1 f g (Or.inl hg)
  have hn : Commute (d.κ f) d.L.nabs := hR.2.1 f _ (Or.inr (by simp))
  have hpb : ∀ l, Commute (d.κ f) (d.L.pb l) := fun l => hk f _ (by simp [TL.siteOps])
  obtain ⟨hA, hB⟩ := Formalism.FourierDecayAlt.P.MAx3.Q.comm_Tvprod d.L (d.κ f) hpb (fun l => hf _ (m_cb d.L l))
    (fun l => hf _ (m_cbi d.L l)) y
  have hA' : Commute (d.κ f) (d.L.Avr y) := hA
  have hB' : Commute (d.κ f) (d.L.Bvr y) := hB
  have hDr : Commute (d.κ f) d.L.Dr := Commute.list_prod_right _ _ fun x hx => by
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact hf _ (m_c d.L l)
  have hDrb : Commute (d.κ f) d.L.Drb := Commute.list_prod_right _ _ fun x hx => by
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact hf _ (m_cb d.L l)
  have hm : Commute (d.κ f) (d.L.m0 y) :=
    hn.neg_right.sub_right ((Algebra.commutes _ _).symm |> fun h : Commute (d.κ f) (algebraMap ℂ A (y - 1/2)) =>
      h.mul_right ((hf _ (m_ζ d.L)).mul_right (hf _ (m_GGi d.L))))
  exact ⟨hDrb.mul_right hA', (hDr.mul_right (hf _ (m_GG d.L))).mul_right ((hm.mul_right hA').add_right hB')⟩

omit [StarModule ℂ A] in
theorem ss_rule (d : Q.NFData P A) (h : HatHyp d) (i : ℕ) (hi : i ∈ Finset.Icc 1 (P.k - 1)) (Y : ℂ) :
    d.L.Ahatv Y * ssn d i = ssn d i * d.L.Ahatv (Y - 1) ∧ d.L.R0v Y * ssn d i = ssn d i * d.L.R0v (Y - 1) := by
  obtain ⟨-, -, hR, -⟩ := h
  obtain ⟨h1, h2⟩ := hR.2.2.2.2.1 i hi
  have hc := hR.2.2.1 i
  have h := Formalism.FourierDecayAlt.P.intertwinerConjugation _ P.r d.L (d.SS i) 0 (fun x hx => (hc x (Or.inl (Or.inl hx))).symm)
    (fun l => (hc _ (Or.inl (Or.inr ⟨l, rfl⟩))).symm) (fun l => (hc _ (Or.inr ⟨l, rfl⟩)).symm) h1 h2
    (fun x _ => by simp) (fun l => by simp) (fun l => by simp) (by simp) (by simp) Y
  exact ⟨h.2.2.1, h.2.2.2.1⟩

theorem sss_rule (d : Q.NFData P A) (h : HatHyp d) (i : ℕ) (hi : i ∈ Finset.Icc 1 (P.k - 1)) (Y : ℂ) :
    d.L.Ahatv Y * star (ssn d i) = star (ssn d i) * d.L.Ahatv (Y + 1) ∧
      d.L.R0v Y * star (ssn d i) = star (ssn d i) * d.L.R0v (Y + 1) := by
  obtain ⟨-, hS, hR, sp, sc, sci, -⟩ := h
  obtain ⟨h1, h2⟩ := hR.2.2.2.2.1 i hi
  have hc := hR.2.2.1 i
  obtain ⟨sz, szb, szi, szbi, sg, sgi⟩ := Formalism.FourierDecayAlt.P.TLA.M2.star_fns d.L hS
  have sn : star d.L.nab = d.L.nabs := hS.2.1
  have sns : star d.L.nabs = d.L.nab := by rw [← sn, star_star]
  have scb : ∀ l, star (d.L.cb l) = d.L.c l := fun l => by rw [← sc, star_star]
  have scbi : ∀ l, star (d.L.cbi l) = d.L.ci l := fun l => by rw [← sci, star_star]
  have spb : ∀ l, star (d.L.pb l) = -d.L.p l := fun l => by
    rw [← star_star (d.L.p l), sp, star_neg, neg_neg]
  have sf : ∀ x ∈ d.L.fns, star x ∈ d.L.fns := by
    intro x hx
    simp only [LevelData.fns, Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | (rfl | rfl | rfl | rfl | rfl | rfl))
    · rw [sc]; exact m_cb d.L l
    · rw [sci]; exact m_cbi d.L l
    · rw [scb]; exact m_c d.L l
    · rw [scbi]; exact m_ci d.L l
    · rw [sz]; exact m_ζb d.L
    · rw [szi]; exact m_ζbi d.L
    · rw [szb]; exact m_ζ d.L
    · rw [szbi]; exact m_ζi d.L
    · rw [sg]; exact m_GG d.L
    · rw [sgi]; exact m_GGi d.L
  have hf : ∀ x ∈ d.L.fns, Commute (star (d.SS i)) x := fun x hx => by
    have := (hc _ (Or.inl (Or.inl (sf x hx)))).star_star
    rwa [star_star] at this
  have hp : ∀ l, Commute (star (d.SS i)) (d.L.p l) := fun l => by
    have := (hc _ (Or.inr ⟨l, rfl⟩)).star_star
    rw [spb] at this
    exact Commute.neg_right_iff.1 this
  have hpb : ∀ l, Commute (star (d.SS i)) (d.L.pb l) := fun l => by
    have := (hc _ (Or.inl (Or.inr ⟨l, rfl⟩))).star_star
    rw [sp] at this
    exact Commute.neg_right_iff.1 this
  have c1 : star (d.SS i) * (d.L.GGi * d.L.ζb) = d.L.ζb * d.L.GGi * star (d.SS i) := by
    rw [((hf _ (m_GGi d.L)).mul_right (hf _ (m_ζb d.L))).eq, d.L.fns_comm _ (m_GGi d.L) _ (m_ζb d.L)]
  have c2 : star (d.SS i) * (d.L.GGi * d.L.ζ) = d.L.ζ * d.L.GGi * star (d.SS i) := by
    rw [((hf _ (m_GGi d.L)).mul_right (hf _ (m_ζ d.L))).eq, d.L.fns_comm _ (m_GGi d.L) _ (m_ζ d.L)]
  have k1 : d.L.nab * star (d.SS i) = star (d.SS i) * d.L.nab + d.L.ζb * d.L.GGi * star (d.SS i) := by
    have := congrArg star h2
    rw [star_mul, star_sub, star_mul, star_mul, star_mul, sns, sz, sgi] at this
    rw [← c1, this]; abel
  have k2 : d.L.nabs * star (d.SS i) = star (d.SS i) * d.L.nabs + d.L.ζ * d.L.GGi * star (d.SS i) := by
    have := congrArg star h1
    rw [star_mul, star_sub, star_mul, star_mul, star_mul, sn, szb, sgi] at this
    rw [← c2, this]; abel
  have sDrb : star d.L.Drb = d.L.Dr := by
    unfold LevelData.Drb LevelData.Dr
    rw [star_listProd, List.map_ofFn]
    have : (star ∘ d.L.cb) = d.L.c := funext scb
    rw [this, rev_prod d.L]
    intro x hx; obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact memF d.L (m_c d.L l)
  have sDri : star d.L.Dri = d.L.Drbi := by
    unfold LevelData.Dri LevelData.Drbi
    rw [star_listProd, List.map_ofFn]
    have : (star ∘ d.L.ci) = d.L.cbi := funext sci
    rw [this, rev_prod d.L]
    intro x hx; obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact memF d.L (m_cbi d.L l)
  have e : star (ssn d i) = star (d.SS i) * (d.L.Dr * d.L.Drbi) := by
    rw [ssn, star_mul, star_mul, sDrb, sDri, cl_comm d.L (memDrbi d.L) (memDr d.L)]
  have h := Formalism.FourierDecayAlt.P.intertwinerConjugation _ P.r d.L 0 (star (d.SS i)) (fun x _ => by simp) (fun l => by simp)
    (fun l => by simp) (by simp) (by simp) (fun x hx => (hf x hx).symm) (fun l => (hp l).symm)
    (fun l => (hpb l).symm) k1 k2 Y
  rw [e]
  exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

end

theorem minus_hats_pass_generators :
    ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d →
      ∀ b ∈ bset d, ∀ y : ℂ,
        d.L.Ahatv y * b ∈ nfSpan d (hats d.L) 0 0 1 ∧ d.L.R0v y * b ∈ nfSpan d (hats d.L) 0 0 1 := by
  intro P A _ _ _ _ d h b hb y
  have gen : ∀ {x}, x ∈ bset d → x ∈ bmon d := fun h => Submonoid.subset_closure h
  have mDD : d.L.D * d.L.Dbi ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mDbD : d.L.Db * d.L.Di ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mζi : d.L.ζi ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mζbi : d.L.ζbi ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have hdrv : d.L.Dr * d.L.Dbi ∈ bmon d := by
    rw [drv_eq]; exact Submonoid.mul_mem _ mDD mζi
  have sA : ∀ {x}, x ∈ bmon d → ∀ y, x * d.L.Ahatv y ∈ nfSpan d (hats d.L) 0 0 1 := fun hx y =>
    mem_span d hx (Or.inl (Or.inr ⟨y, rfl⟩))
  have sR : ∀ {x}, x ∈ bmon d → ∀ y, x * d.L.R0v y ∈ nfSpan d (hats d.L) 0 0 1 := fun hx y =>
    mem_span d hx (Or.inr ⟨y, rfl⟩)
  have hInv := Formalism.FourierDecayAlt.P.inverseCommutators _ P.r d.L y
  have hb' := gen hb
  rcases hb with (((hb | ⟨f, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · rw [← hInv.2.2.2.2.2.1, ← hInv.2.2.2.2.2.2.1]
      exact ⟨sA hb' _, sR hb' _⟩
    · rw [← hInv.2.2.1, vgen_ζbi_R]
      refine ⟨sA hb' _, Submodule.add_mem _ (sR hb' _) ?_⟩
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (sA mDD _))
        (Submodule.smul_mem _ _ (sA (Submonoid.mul_mem _ (Submonoid.mul_mem _ mζi mζbi) mDD) _))
    · rw [vgen_DD_A, vgen_DD_R]
      exact ⟨sA hb' _, Submodule.add_mem _ (sR hb' _) (Submodule.smul_mem _ _ (sA (Submonoid.mul_mem _ mDD hdrv) _))⟩
    · rw [vgen_DbD_A, vgen_DbD_R]
      exact ⟨sA hb' _, Submodule.add_mem _ (sR hb' _) (Submodule.smul_mem _ _ (sA (Submonoid.mul_mem _ mDbD hdrv) _))⟩
  · rw [← (kap_comm d h f y).1.eq, ← (kap_comm d h f y).2.eq]
    exact ⟨sA hb' _, sR hb' _⟩
  · have := ss_rule d h i (Finset.mem_Icc.2 (Set.mem_Icc.1 hi)) y
    rw [this.1, this.2]
    exact ⟨sA hb' _, sR hb' _⟩
  · have := sss_rule d h i (Finset.mem_Icc.2 (Set.mem_Icc.1 hi)) y
    simp only [] at hb' ⊢
    rw [this.1, this.2]
    exact ⟨sA hb' _, sR hb' _⟩

end GlobalTheory.HatNF.GenMinus
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

theorem _root_.GlobalTheory.T.cloudSizes_between_zero_and_twice_b : ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → L.Sc + L.etaSz ≤ 2 * L.sc.b ∧ ∀ j, InR D j → (∀ τ, 0 ≤ wj D j τ ∧ wj D j τ ≤ 2 * L.sc.b) ∧ (∀ t, wj D j (plOf D (false, t)) ≤ 2 * L.sc.b') ∧ ∀ z, (numOf D L).w j z = wj D j (plOf D z) := by
  first | exact @GlobalTheory.RunDepth.sizes_le_two_mul | exact GlobalTheory.RunDepth.sizes_le_two_mul | (intros; apply GlobalTheory.RunDepth.sizes_le_two_mul <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

theorem _root_.GlobalTheory.T.realPlaceLabel_bijective_card_eq_f : ∀ (D : D7), Function.Bijective (plOf D) ∧ Fintype.card D.what₂.Tau = D.R.f := by
  first | exact @GlobalTheory.RunDepth.plOf_bijective_card | exact GlobalTheory.RunDepth.plOf_bijective_card | (intros; apply GlobalTheory.RunDepth.plOf_bijective_card <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

theorem _root_.GlobalTheory.T.realPlaceWeightRowGap_mul_bounds_size : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ), InR D j → ∀ z : RPl D.R, L.sc.w'' D.R.n ≤ (numOf D L).w j z →
  (1 - ((Tp.Dp : ℝ) + 4) / Tp.TO) * (numOf D L).w j z ≤ (Tp.TO : ℝ) * gapW (numOf D L) (fun z => DV.tauEmb D (plOf D z)) (wtA (lR Tp hK j)) z ∧
  (Tp.TO : ℝ) * gapW (numOf D L) (fun z => DV.tauEmb D (plOf D z)) (wtA (lR Tp hK j)) z ≤ (numOf D L).w j z + 100 * ((numOf D L).Sc + (numOf D L).eta) := by
  first | exact @GlobalTheory.GoodDepth.Gap.gap_bounds | exact GlobalTheory.GoodDepth.Gap.gap_bounds | (intros; apply GlobalTheory.GoodDepth.Gap.gap_bounds <;> assumption)
end

section

set_option autoImplicit false

namespace GlobalTheory.GoodDepth

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

theorem placeTie_of_pins : ∀ (D : D7) (L : SizeData₂ D) (T : Core D), T.Q.Pins →
    PlaceTie (numOf D L) T.Q.c (fun z => DV.tauEmb D (plOf D z)) := by
  intro D L T hp
  have hh := hp.1
  refine ⟨?_, ?_, hh.1, D.host.hostE_isGalois, ?_, ?_, ?_⟩
  · intro z z' h
    exact (plOf_bijective_card D).1.1 (D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h)))
  · intro τ
    constructor
    · intro hτ
      have hex : ∃ t : D.what₂.Tau, τ = DV.tauEmb D t := by
        obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 τ
        by_cases hgP : g ∈ D.R.Psi
        · obtain ⟨t, ht⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D g).2 hgP
          exact ⟨t, hg.symm.trans ht⟩
        · exfalso
          have h2 : g * D.R.cc ∈ D.R.Psi := by
            by_contra h
            exact hgP ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g).2 h)
          obtain ⟨t, ht⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D (g * D.R.cc)).2 h2
          have h3 : DV.tauEmb D t (T.Q.H.rt : D.host.E) = T.Q.H.rt0 := hh.2.2.2 t
          rw [← ht, Formalism.L2.Geo.emb_mul_cc_comp, hg, RingHom.comp_apply] at h3
          have h4 : τ (D.host.conj (T.Q.H.rt : D.host.E)) = star (τ (T.Q.H.rt : D.host.E)) := Formalism.MainNotions.WeightFamilies.emb_conj D τ _
          have hτ' : τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0 := hτ
          have hc : (starRingEnd ℂ) T.Q.H.rt0 ≠ T.Q.H.rt0 := by
            intro he
            obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 he
            have hs := T.Q.H.sqrt_neg_disc_sq
            rw [hx] at hs
            have hs' : x ^ 2 = -(T.Q.H.d : ℝ) := by exact_mod_cast hs
            have hd : (0 : ℝ) < T.Q.H.d := by exact_mod_cast T.Q.H.d_prime.pos
            nlinarith [sq_nonneg x]
          apply hc
          calc star T.Q.H.rt0 = star (τ (T.Q.H.rt : D.host.E)) := by rw [hτ']
            _ = τ (D.host.conj (T.Q.H.rt : D.host.E)) := h4.symm
            _ = T.Q.H.rt0 := h3
      obtain ⟨t, ht⟩ := hex
      obtain ⟨z, hz⟩ := (plOf_bijective_card D).1.2 t
      exact ⟨z, by rw [ht, ← hz]⟩
    · rintro ⟨z, rfl⟩
      exact hh.2.2.2 _
  · intro σ τ
    exact D.host.galE_injective (by
      rw [D.host.galE_mul, D.host.galE_mul, mul_comm])
  · intro p hp h2 hq hd
    exact GlobalTheory.GoodDepth.not_dvd_discr_host D.R D.host p hp h2 hq hd
  · intro la hla z x
    exact GlobalTheory.FrobPlace.frob_place D L T.Q.H _ T.Q.c la hla z x

end GlobalTheory.GoodDepth
end

section

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

theorem _root_.GlobalTheory.T.theta_scaled_span_le_sigma_smul_unscaled_span : ∀ (D : D7) (B : WeightFamilies.Prov D) (P6 : ModuliIntegralCharts.Prov D) (j : ℕ) (X : WeightAlgebra.PJ D B P6 j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ), WeightAlgebra.IsF' ka wL wF T wF.n → ka.n = wF.n + T * wL.n → WeightFamilies.dimY D j ≤ T → sigRec B hinj EX ka wL wF T ≠ 0 ∧ ∀ F ∈ X.Theta (scalOfP B hinj EX p ka wL wF T) ka wL wF T, ∃ G ∈ thetaPlain X ka wL wF T, F = sigRec B hinj EX ka wL wF T • G := by
  first | exact @GlobalTheory.ScaledSpan.theta_le_sigma_smul | exact GlobalTheory.ScaledSpan.theta_le_sigma_smul | (intros; apply GlobalTheory.ScaledSpan.theta_le_sigma_smul <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.besselIntegral_integrable_and_cwContinuous_of_gap : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, (∀ w ∈ R.sm, Integrable (beInt z Formalism.QuantumDeterminants.cStd π R.σ w v) (μW.prod μN)) ∧ PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun w => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) := by
  first | exact @GlobalTheory.BesselConv.be_conv | exact GlobalTheory.BesselConv.be_conv | (intros; apply GlobalTheory.BesselConv.be_conv <;> assumption)
end
