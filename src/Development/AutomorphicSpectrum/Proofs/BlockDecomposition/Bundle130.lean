module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfEig
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
public import Formalism.RealPlaceAnalysis.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle078
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle117
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle118
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Formalism.RealPlaceAnalysis.Bundle003
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle119
public import Formalism.RealPlaceAnalysis.Bundle004
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle106
public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import Formalism.ConjugateSelfDual.Bundle001
public import GroundTheory.GlobalFields.KummerTheory.Bundle001
public import GroundTheory.GlobalFields.TateThesis.HeckeChar
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Order.Hom.Esakia
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle101

@[expose] public section

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirSeq

section Alg

variable {k : Type} [Field k]

theorem mul_colMat_of_mem {n : ℕ} (h : GL (Fin (n + 1)) k) (hh : h ∈ Mir k n) (v : Fin n → k) :
    (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) * colMat k n v =
      colMat k n ((blockMat k n (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)).mulVec v) := by
  have hl := (mem_Mir_iff k h).1 hh
  ext i j
  by_cases hj : j = Fin.last n
  · subst hj
    induction i using Fin.lastCases with
    | last =>
      have e : ∀ l : Fin n, (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.castSucc l) = 0 := by
        intro l
        rw [hl]
        simp [eLast, Pi.single_apply, Fin.castSucc_ne_last]
      simp [colMat, Matrix.mul_apply, Fin.sum_univ_castSucc, e]
    | cast i =>
      simp [colMat, Matrix.mul_apply, Fin.sum_univ_castSucc, mulVec, dotProduct, blockMat]
  · simp [colMat, Matrix.mul_apply, hj]

theorem colMat_mul_of_mem {n : ℕ} (h : GL (Fin (n + 1)) k) (hh : h ∈ Mir k n) (w : Fin n → k) :
    colMat k n w * (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = colMat k n w := by
  have hl := (mem_Mir_iff k h).1 hh
  ext i j
  have e : (colMat k n w * (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) i j =
      colMat k n w i (Fin.last n) * (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last n)]
    · intro l _ hlne
      simp [colMat, hlne]
    · simp
  rw [e, hl]
  by_cases hj : j = Fin.last n
  · subst hj
    simp [colMat, eLast]
  · simp [colMat, eLast, hj]

theorem conj_mem_MirUin {n : ℕ} (h : Mir k n) (u : MirUin k n) : h * (u : Mir k n) * h⁻¹ ∈ MirUin k n := by
  obtain ⟨v, hv⟩ := (u.2 : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  have hv' : ((u : Mir k n) : GL (Fin (n + 1)) k) = unip k n v := hv.symm
  show (h : GL (Fin (n + 1)) k) * ((u : Mir k n) : GL (Fin (n + 1)) k) * (h : GL (Fin (n + 1)) k)⁻¹ ∈ MirU k n
  rw [hv']
  refine ⟨Multiplicative.ofAdd ((blockMat k n ((h : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)).mulVec
    v.toAdd), ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  ext1
  rw [Units.val_mul, Units.val_mul]
  show (1 + colMat k n _) * _ = _ * (1 + colMat k n v.toAdd)
  rw [add_mul, mul_add, one_mul, mul_one, colMat_mul_of_mem _ h.2, mul_colMat_of_mem _ h.2]
  simp

end Alg

section Seq

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Beta

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ψ : AddChar k Circle) {n : ℕ}
  (τ : Representation ℂ (Mir k (n + 1)) V)

end Beta

variable (hI : BetaInd k) (hS : BetaSmooth k) (hC : BetaCompact k)


end Seq

end GlobalTheory.CompanionTheory.BZMirSeq

end
end

section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.JHMult
open PositivityTheory.Rg.BcN.F2 (FinSubq)

namespace GlobalTheory.CompanionTheory.RepFinSubq

variable {F G V W : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

theorem exists_series {ρ : Representation F G V} (h : HasFiniteLength ρ) :
    ∃ (N : ℕ) (S : Fin (N + 1) → Subrepresentation ρ), Monotone S ∧ S 0 = ⊥ ∧ S (Fin.last N) = ⊤ ∧
      ∀ t : Fin N, S t.castSucc ⋖ S t.succ := by
  obtain ⟨s, h0, h1⟩ := isFiniteLength_iff_exists_compositionSeries.1 h
  let e := (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).symm
  refine ⟨s.length, fun i => e (s i), ?_, ?_, ?_, fun t => ?_⟩
  · exact e.monotone.comp s.strictMono.monotone
  · show e s.head = ⊥
    rw [h0, map_bot]
  · show e s.last = ⊤
    rw [h1, map_top]
  · exact (apply_covBy_apply_iff e).2 (s.step t)

theorem isSubquotient_subQuot {ρ : Representation F G V} (S T : Subrepresentation ρ) :
    IsSubquotient (subQuot S T) ρ :=
  ⟨S, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.mkQ_surjective _⟩

theorem exists_factor_equiv {ρ : Representation F G V} {N : ℕ} {S : Fin (N + 1) → Subrepresentation ρ}
    (hS : Monotone S) (h0 : S 0 = ⊥) (h1 : S (Fin.last N) = ⊤) (hc : ∀ t : Fin N, S t.castSucc ⋖ S t.succ)
    {τ : Representation F G W} (hτ : τ.IsIrreducible) (hq : IsSubquotient τ ρ) :
    ∃ t : Fin N, Nonempty (τ.Equiv (subQuot (S t.succ) (S t.castSucc))) := by
  have hne : jhMult τ ρ ≠ 0 := jhMult_ne_zero_iff.2 hq
  rw [jhMult_filtration hτ S hS h0 h1] at hne
  obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨e⟩ := (jhMult_ne_zero_iff.1 ht).nonempty_equiv hτ (isIrreducible_subQuot (hc t))
  exact ⟨t, ⟨e.symm⟩⟩

theorem finSubq : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (ι : Type) [Fintype ι] [DecidableEq ι], FinSubq F ι := by
  intro F _ _ _ _ ι _ _ U _ _ ρ hρ hfl
  obtain ⟨N, S, hS, h0, h1, hc⟩ := exists_series hfl
  refine ⟨Fin N, inferInstance, fun t => _, fun _ => inferInstance, fun _ => inferInstance,
    fun t => subQuot (S t.succ) (S t.castSucc), fun t => ?_, fun W' _ _ τ' hτ hq => ?_⟩
  · exact ⟨(isSubquotient_subQuot _ _).isSmooth hρ, isIrreducible_subQuot (hc t), isSubquotient_subQuot _ _⟩
  · exact exists_factor_equiv hS h0 h1 hc hτ hq

end GlobalTheory.CompanionTheory.RepFinSubq
end

section

open Finset Matrix PositivityTheory.RgHe.Frame

noncomputable section

namespace GlobalTheory.CompanionTheory.RgHeFrame

def sg (b : Bool) : ℝ := if b then 1 else -1

lemma sg_mul_self (b : Bool) : sg b * sg b = 1 := by cases b <;> simp [sg]

lemma sg_ne_zero (b : Bool) : sg b ≠ 0 := by cases b <;> simp [sg]

lemma sg_cast (b : Bool) : ((sg b : ℝ) : ℂ) = if b then 1 else -1 := by cases b <;> simp [sg]

variable {n : ℕ}

def cc (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) (i : Fin (n + 1)) : ℝ := 1 / √|pfD d d' i|

def yy (ε' : Fin n → Bool) (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) (j : Fin n) : ℝ :=
  √(-(sg (ε' j) * pfR d d' j))

def G0 (ε' : Fin n → Bool) (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) (r : Fin n ⊕ Unit)
    (i : Fin (n + 1)) : ℝ :=
  Sum.elim (fun j => cc d d' i * yy ε' d d' j / (d i - d' j)) (fun _ => cc d d' i) r

def X0 (ε' : Fin n → Bool) (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) (r t : Fin n ⊕ Unit) : ℝ :=
  Sum.elim
    (fun a => Sum.elim (fun b => if a = b then d' a else 0) (fun _ => yy ε' d d' a) t)
    (fun _ => Sum.elim (fun b => sg (ε' b) * yy ε' d d' b) (fun _ => pfX d d') t) r

lemma yy_sq {ε' : Fin n → Bool} {d : Fin (n + 1) → ℝ} {d' : Fin n → ℝ} {j : Fin n}
    (h : 0 < -(sg (ε' j) * pfR d d' j)) :
    sg (ε' j) * (yy ε' d d' j * yy ε' d d' j) = -pfR d d' j := by
  unfold yy
  rw [Real.mul_self_sqrt h.le]
  have := sg_mul_self (ε' j)
  linear_combination (-pfR d d' j) * this

lemma cc_sq {d : Fin (n + 1) → ℝ} {d' : Fin n → ℝ} {i : Fin (n + 1)} {b : Bool}
    (h : 0 < sg b * pfD d d' i) : cc d d' i * cc d d' i * pfD d d' i = sg b := by
  have hcc : cc d d' i * cc d d' i = 1 / |pfD d d' i| := by
    unfold cc
    rw [div_mul_div_comm, Real.mul_self_sqrt (abs_nonneg _), one_mul]
  rw [hcc]
  cases b with
  | true =>
    have hp : 0 < pfD d d' i := by simpa [sg] using h
    rw [abs_of_pos hp]
    simp only [sg]
    field_simp
    simp
  | false =>
    have hp : pfD d d' i < 0 := by simpa [sg] using h
    rw [abs_of_neg hp]
    simp only [sg]
    have := hp.ne
    field_simp
    simp

lemma cc_ne_zero {d : Fin (n + 1) → ℝ} {d' : Fin n → ℝ} {i : Fin (n + 1)} {b : Bool}
    (h : 0 < sg b * pfD d d' i) : cc d d' i ≠ 0 := by
  intro h0
  have := cc_sq h
  rw [h0] at this
  exact sg_ne_zero b (by simpa using this.symm)

lemma sum_terms {ε' : Fin n → Bool} {d : Fin (n + 1) → ℝ} {d' : Fin n → ℝ}
    (hR : ∀ j, 0 < -(sg (ε' j) * pfR d d' j)) (i k : Fin (n + 1)) :
    ∑ j, (cc d d' i * yy ε' d d' j / (d i - d' j)) * sg (ε' j) *
        (cc d d' k * yy ε' d d' j / (d k - d' j)) =
      -(cc d d' i * cc d d' k * ∑ j, pfR d d' j / ((d i - d' j) * (d k - d' j))) := by
  rw [mul_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun j _ => ?_
  have h := yy_sq (hR j)
  calc (cc d d' i * yy ε' d d' j / (d i - d' j)) * sg (ε' j) *
        (cc d d' k * yy ε' d d' j / (d k - d' j))
      = cc d d' i * cc d d' k * (sg (ε' j) * (yy ε' d d' j * yy ε' d d' j)) /
          ((d i - d' j) * (d k - d' j)) := by
          simp only [div_eq_mul_inv, mul_inv]; ring
    _ = _ := by rw [h]; ring

lemma gram {ε : Fin (n + 1) → Bool} {d : Fin (n + 1) → ℝ} {ε' : Fin n → Bool} {d' : Fin n → ℝ}
    (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (hz : ε (e (Sum.inr ())) = true)
    (hs : ∀ a, ε (e (Sum.inl a)) = ε' a) (hinj : Function.Injective (Sum.elim d d'))
    (hD : ∀ i, 0 < sg (ε i) * pfD d d' i) (hR : ∀ j, 0 < -(sg (ε' j) * pfR d d' j))
    (i k : Fin (n + 1)) :
    ∑ r, G0 ε' d d' (e.symm r) i * sg (ε r) * G0 ε' d d' (e.symm r) k =
      if i = k then sg (ε i) else 0 := by
  rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
  simp only [Equiv.symm_apply_apply, G0, Sum.elim_inl, Sum.elim_inr, hs, hz, univ_unique,
    sum_singleton]
  rw [sum_terms hR]
  have hz1 : sg true = 1 := by simp [sg]
  rw [hz1]
  by_cases hik : i = k
  · subst hik
    have h1 := GlobalTheory.T.partial_fraction_square_identity d d' hinj i
    have h2 := cc_sq (hD i)
    simp only [if_true]
    have h3 : ∑ j, pfR d d' j / ((d i - d' j) * (d i - d' j)) =
        ∑ j, pfR d d' j / (d i - d' j) ^ 2 := by
      refine sum_congr rfl fun j _ => ?_
      rw [sq]
    rw [h3]
    linear_combination (cc d d' i * cc d d' i) * h1 + h2
  · have h1 := GlobalTheory.T.partial_fraction_off_diagonal_identity d d' hinj i k hik
    simp only [hik, if_false]
    linear_combination (cc d d' i * cc d d' k) * h1

lemma inter {d : Fin (n + 1) → ℝ} {ε' : Fin n → Bool} {d' : Fin n → ℝ}
    (hinj : Function.Injective (Sum.elim d d'))
    (hR : ∀ j, 0 < -(sg (ε' j) * pfR d d' j)) (r : Fin n ⊕ Unit) (i : Fin (n + 1)) :
    ∑ t, X0 ε' d d' r t * G0 ε' d d' t i = G0 ε' d d' r i * d i := by
  have hne : ∀ j, d i - d' j ≠ 0 := by
    intro j h
    have : (Sum.inl i : Fin (n + 1) ⊕ Fin n) = Sum.inr j :=
      hinj (by simpa using sub_eq_zero.mp h)
    simp at this
  rw [Fintype.sum_sum_type]
  rcases r with a | u
  · simp only [X0, G0, Sum.elim_inl, Sum.elim_inr, univ_unique, sum_singleton, ite_mul, zero_mul,
      sum_ite_eq, mem_univ, if_true]
    have := hne a
    field_simp
    ring
  · simp only [X0, G0, Sum.elim_inl, Sum.elim_inr, univ_unique, sum_singleton]
    have h0 := GlobalTheory.T.partial_fraction_diagonal_identity d d' hinj i
    have h1 : ∑ j, sg (ε' j) * yy ε' d d' j * (cc d d' i * yy ε' d d' j / (d i - d' j)) =
        -(cc d d' i * ∑ j, pfR d d' j / (d i - d' j)) := by
      rw [mul_sum, ← sum_neg_distrib]
      refine sum_congr rfl fun j _ => ?_
      have h := yy_sq (hR j)
      calc sg (ε' j) * yy ε' d d' j * (cc d d' i * yy ε' d d' j / (d i - d' j))
          = cc d d' i * (sg (ε' j) * (yy ε' d d' j * yy ε' d d' j)) / (d i - d' j) := by ring
        _ = _ := by rw [h]; ring
    rw [h1]
    linear_combination (-cc d d' i) * h0

theorem build : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (d : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (d' : Fin n → ℝ) (e : Fin n ⊕ Unit ≃ Fin (n + 1)), ε (e (Sum.inr ())) = true → (∀ a, ε (e (Sum.inl a)) = ε' a) → Function.Injective (Sum.elim d d') → (∀ i, 0 < (if ε i then (1 : ℝ) else -1) * pfD d d' i) → (∀ j, 0 < -((if ε' j then (1 : ℝ) else -1) * pfR d d' j)) → ∃ g X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, Formalism.REAL.inUJ ε g ∧ X * g = g * diagonal (fun i => ((d i : ℝ) : ℂ)) ∧ (∀ a b, X (e (Sum.inl a)) (e (Sum.inl b)) = if a = b then ((d' a : ℝ) : ℂ) else 0) ∧ ∀ i, ((Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) *ᵥ (Pi.single (e (Sum.inr ())) (1 : ℂ) : Fin (n + 1) → ℂ)) i ≠ 0 := by
  intro n ε d ε' d' e hz hs hinj hD hR
  have hD' : ∀ i, 0 < sg (ε i) * pfD d d' i := hD
  have hR' : ∀ j, 0 < -(sg (ε' j) * pfR d d' j) := hR
  obtain ⟨g, hg⟩ : ∃ g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      ∀ r i, g r i = ((G0 ε' d d' (e.symm r) i : ℝ) : ℂ) := ⟨Matrix.of _, fun _ _ => rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      ∀ r t, X r t = ((X0 ε' d d' (e.symm r) (e.symm t) : ℝ) : ℂ) := ⟨Matrix.of _, fun _ _ => rfl⟩
  refine ⟨g, X, ?_, ?_, ?_, ?_⟩
  · unfold Formalism.REAL.inUJ Formalism.REAL.Jm
    ext i k
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply, hg,
      RCLike.star_def, Complex.conj_ofReal]
    have h := gram e hz hs hinj hD' hR' i k
    have h2 := congrArg (fun x : ℝ => (x : ℂ)) h
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, sg_cast] at h2
    rw [h2]
    by_cases hik : i = k
    · simp [hik, sg_cast]
    · simp [hik]
  · ext r i
    rw [Matrix.mul_diagonal, Matrix.mul_apply, ← Equiv.sum_comp e]
    simp only [hg, hX, Equiv.symm_apply_apply]
    have h := inter (ε' := ε') hinj hR' (e.symm r) i
    exact_mod_cast h
  · intro a b
    simp only [hX, Equiv.symm_apply_apply, X0, Sum.elim_inl]
    split_ifs <;> simp
  · intro i
    rw [Matrix.mulVec_single_one]
    change (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) i (e (Sum.inr ())) ≠ 0
    unfold Formalism.REAL.Jm
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, hg,
      Equiv.symm_apply_apply, G0, Sum.elim_inr, hz, RCLike.star_def, Complex.conj_ofReal]
    have hc := cc_ne_zero (hD' i)
    have : ((cc d d' i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
    cases h : ε i <;> simpa using this

end GlobalTheory.CompanionTheory.RgHeFrame
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.similitude_between_nonempty_spheres : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ J : Matrix (Fin 2) (Fin 2) E, IsHermND σ J → ∀ β β' : F, β ≠ 0 → β' ≠ 0 → (PositivityTheory.Rg.Mass.sph σ J β).Nonempty → (PositivityTheory.Rg.Mass.sph σ J β').Nonempty → ∃ γ : GL (Fin 2) E, cT (σ : E →+* E) (γ : Matrix (Fin 2) (Fin 2) E) * J * (γ : Matrix (Fin 2) (Fin 2) E) = (algebraMap F E (β' / β)) • J := by
  first | exact @GlobalTheory.CompanionTheory.SimilExists.exists_similitude | exact GlobalTheory.CompanionTheory.SimilExists.exists_similitude | (intros; apply GlobalTheory.CompanionTheory.SimilExists.exists_similitude <;> assumption)
end

section

open PositivityTheory.Rg.Mass

theorem _root_.GlobalTheory.T.counting_bound_alt : CountBd := by
  first | exact @GlobalTheory.CompanionTheory.MassCount.countBd | exact GlobalTheory.CompanionTheory.MassCount.countBd | (intros; apply GlobalTheory.CompanionTheory.MassCount.countBd <;> assumption)
end

section


theorem _root_.GlobalTheory.T.norm_map_third_property : PositivityTheory.Rg.Tf.Loc.N1 → PositivityTheory.Rg.Tf.Loc.N2 → PositivityTheory.Rg.Tf.Loc.N3 := by
  first | exact @GlobalTheory.CompanionTheory.UnitNorm.norm_units_surjective | exact GlobalTheory.CompanionTheory.UnitNorm.norm_units_surjective | (intros; apply GlobalTheory.CompanionTheory.UnitNorm.norm_units_surjective <;> assumption)
end

section

open Formalism.REAL

theorem _root_.GlobalTheory.T.quantum_det_opposite_neg : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A), Formalism.REAL.GlRel X → ∀ v : ℂ, MulOpposite.unop (Formalism.REAL.qdet (fun i j => MulOpposite.op (-X i j)) v) = ((-1 : ℂ) ^ n) • Formalism.REAL.qdet X ((n : ℂ) - 1 - v) := by
  first | exact @GlobalTheory.CompanionTheory.CapelliAntipode.unop_qdet_op_neg | exact GlobalTheory.CompanionTheory.CapelliAntipode.unop_qdet_op_neg | (intros; apply GlobalTheory.CompanionTheory.CapelliAntipode.unop_qdet_op_neg <;> assumption)
end

section

open MeasureTheory

namespace GlobalTheory.CompanionTheory.HaarUJ

theorem haar_rinv_UJ : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (Formalism.REAL.UJ ε)) [μ.IsHaarMeasure],
    μ.IsMulRightInvariant := by
  intro n ε μ _
  have hν : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  have hμ : μ = Measure.haarScalarFactor μ (Formalism.REAL.muG ε) • Formalism.REAL.muG ε :=
    Measure.isMulLeftInvariant_eq_smul μ (Formalism.REAL.muG ε)
  refine ⟨fun g => ?_⟩
  rw [hμ, Measure.map_smul, map_mul_right_eq_self]
  exact (continuous_id.mul continuous_const).aemeasurable

end GlobalTheory.CompanionTheory.HaarUJ
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

theorem _root_.GlobalTheory.T.scaling_measure_product_archimedean : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ li : Measure (Ainf F), li.IsAddHaarMeasure → ∀ (ι : Type) [Fintype ι] (ε : ℝ), 0 < ε → Measure.map (fun (y : ι → Ainf F) (i : ι) => θ ε * y i) (Measure.pi fun _ => li) = ENNReal.ofReal ((ε ^ (Module.finrank ℚ F * Fintype.card ι))⁻¹) • Measure.pi fun _ => li := by
  first | exact @GlobalTheory.CompanionTheory.Equi.InfScale.map_theta_mul_pi | exact GlobalTheory.CompanionTheory.Equi.InfScale.map_theta_mul_pi | (intros; apply GlobalTheory.CompanionTheory.Equi.InfScale.map_theta_mul_pi <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ValuativeRel

namespace GlobalTheory.CompanionTheory.LocRes

theorem natCard_residueField_eq_normV : ∀ (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)), Nat.card 𝓀[v.adicCompletion F] = normV v := by
  intro F _ _ v
  rw [GroundTheory.Global.natCard_residueField_adicCompletion v, Ideal.absNorm_apply,
    Submodule.cardQuot_apply]
  rfl

end GlobalTheory.CompanionTheory.LocRes
end

section

open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem standardOpenSubgroup_le_ker_inv (F : Type) [Field F] [NumberField F] (χ : HeckeCharacter F)
    (h : standardOpenSubgroup F ≤ χ.toIdele.ker) :
    standardOpenSubgroup F ≤ (χ⁻¹).toIdele.ker := by
  intro x hx
  have hx' : χ.toIdele x = 1 := h hx
  show (χ⁻¹).toIdele x = 1
  rw [HeckeCharacter.toIdele_apply] at hx' ⊢
  change (χ _)⁻¹ = 1
  rw [hx', inv_one]

end GlobalTheory.CompanionTheory.PartialZeta
end
