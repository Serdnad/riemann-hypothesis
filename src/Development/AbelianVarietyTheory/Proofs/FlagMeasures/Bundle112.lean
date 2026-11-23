module

import Formalism.HermitianCurvature.HermitianCurvatureProofs.CorollaryAOfPropositionA
public import Formalism.HermitianLattices.Bundle003
public import Formalism.GL3MeanSquares.HookFormulaTorsion.GlobalBoundRefinements
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle023
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle022
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrbitStepSpace
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle026
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle101
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle025
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveTuplesHermitianGramCosetContent
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas.LProd

private lemma eventually_abs_le_half_add_of_doubling_bounds (m : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    1 / (x + 1) ^ (3 + m) + 4 / 2 ^ (3 + m) / ((x + 1) * (x + 1 + 1)) ≤
      4 / 2 ^ (3 + m) / (x * (x + 1)) := by
  have hx0 : 0 < x := by linarith
  have hp : (2 : ℝ) ^ m ≤ (x + 1) ^ m := pow_le_pow_left₀ (by norm_num) (by linarith) m
  have hp0 : (0 : ℝ) < 2 ^ m := by positivity

  have hdiff : 4 / 2 ^ (3 + m) / (x * (x + 1)) - 4 / 2 ^ (3 + m) / ((x + 1) * (x + 1 + 1)) =
      1 / (2 ^ m * (x * (x + 1) * (x + 2))) := by
    rw [pow_add]
    field_simp
    ring

  have hcube : x * (x + 1) * (x + 2) ≤ (x + 1) ^ 3 := by nlinarith
  have hle : 2 ^ m * (x * (x + 1) * (x + 2)) ≤ (x + 1) ^ (3 + m) := by
    calc 2 ^ m * (x * (x + 1) * (x + 2)) ≤ (x + 1) ^ m * (x + 1) ^ 3 :=
          mul_le_mul hp hcube (by positivity) (by positivity)
      _ = (x + 1) ^ (3 + m) := by ring
  have hterm : 1 / (x + 1) ^ (3 + m) ≤ 1 / (2 ^ m * (x * (x + 1) * (x + 2))) :=
    one_div_le_one_div_of_le (by positivity) hle
  linarith

theorem tsum_le (M : ℕ) (hM : 3 ≤ M) :
    (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ M) ≤ 1 + 2 / 2 ^ M := by
  apply Formalism.FourierDecayAlt.P.Sz2.zeta_sub_one_le <;> assumption

theorem log_tsum_le (M : ℕ) (hM : 3 ≤ M) :
    Real.log (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ M) ≤ 2 / 2 ^ M := by
  have h1 := tsum_le M hM
  have h0 : 0 ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ M := tsum_nonneg fun n => by positivity
  rcases h0.eq_or_lt with h | h
  · rw [← h, Real.log_zero]
    positivity
  · linarith [Real.log_le_sub_one_of_pos h]

private lemma sum_Ioc_two_div_two_pow (n₀ k : ℕ) :
    ∑ M ∈ Finset.Ioc n₀ (n₀ + k), (2 : ℝ) / 2 ^ M = 2 / 2 ^ n₀ - 2 / 2 ^ (n₀ + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, Finset.sum_Ioc_succ_top (Nat.le_add_right n₀ k), ih, pow_succ]
    field_simp
    ring

theorem geom_le (n₀ n : ℕ) : ∑ M ∈ Finset.Ioc n₀ n, (2 : ℝ) / 2 ^ M ≤ (2 : ℝ) ^ ((1 : ℤ) - n₀) := by
  rw [zpow_sub₀ two_ne_zero, zpow_one, zpow_natCast]
  rcases le_or_gt n n₀ with h | h
  · rw [Finset.Ioc_eq_empty_of_le h, Finset.sum_empty]
    positivity
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h.le
    rw [sum_Ioc_two_div_two_pow]
    have : (0 : ℝ) ≤ 2 / 2 ^ (n₀ + k) := by positivity
    linarith

theorem neg_log_prod_le : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ n₀ n : ℕ, 2 ≤ n₀ → -Real.log (∏ M ∈ Finset.Ioc n₀ n, Formalism.HermitianLatticesTheory.lValEta E M) ≤ Formalism.HermitianLatticesTheory.fDeg E * (2 : ℝ) ^ ((1 : ℤ) - n₀) ∧ 0 < ∏ M ∈ Finset.Ioc n₀ n, Formalism.HermitianLatticesTheory.lValEta E M := by
  intro E _ _ _ hE n₀ n hn₀
  have hL : ∀ M : ℕ, 2 ≤ M → 0 < Formalism.HermitianLatticesTheory.lValEta E M ∧
      |Real.log (Formalism.HermitianLatticesTheory.lValEta E M)| ≤ (Formalism.HermitianLatticesTheory.fDeg E : ℝ) * Real.log (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ M) :=
    fun M hM => (Formalism.HermitianLattices.GlobalBoundRefinements.log_l_value_field_bound E hE M hM).2
  have hpos : ∀ M ∈ Finset.Ioc n₀ n, 0 < Formalism.HermitianLatticesTheory.lValEta E M := fun M hM =>
    (hL M (by have := (Finset.mem_Ioc.mp hM).1; omega)).1
  refine ⟨?_, Finset.prod_pos hpos⟩
  rw [Real.log_prod (fun M hM => (hpos M hM).ne'), ← Finset.sum_neg_distrib]
  have hf : (0 : ℝ) ≤ Formalism.HermitianLatticesTheory.fDeg E := by positivity
  calc ∑ M ∈ Finset.Ioc n₀ n, -Real.log (Formalism.HermitianLatticesTheory.lValEta E M)
      ≤ ∑ M ∈ Finset.Ioc n₀ n, (Formalism.HermitianLatticesTheory.fDeg E : ℝ) * (2 / 2 ^ M) := by
        apply Finset.sum_le_sum
        intro M hM
        have hM3 : 3 ≤ M := by have := (Finset.mem_Ioc.mp hM).1; omega
        calc -Real.log (Formalism.HermitianLatticesTheory.lValEta E M) ≤ |Real.log (Formalism.HermitianLatticesTheory.lValEta E M)| := neg_le_abs _
          _ ≤ (Formalism.HermitianLatticesTheory.fDeg E : ℝ) * Real.log (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ M) := (hL M (by omega)).2
          _ ≤ (Formalism.HermitianLatticesTheory.fDeg E : ℝ) * (2 / 2 ^ M) := mul_le_mul_of_nonneg_left (log_tsum_le M hM3) hf
    _ = (Formalism.HermitianLatticesTheory.fDeg E : ℝ) * ∑ M ∈ Finset.Ioc n₀ n, (2 : ℝ) / 2 ^ M := by rw [Finset.mul_sum]
    _ ≤ Formalism.HermitianLatticesTheory.fDeg E * (2 : ℝ) ^ ((1 : ℤ) - n₀) := mul_le_mul_of_nonneg_left (geom_le n₀ n) hf

end GlobalTheory.FlagMeas.LProd
end

section

open NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.CoverRadiiEq

open Formalism.MainNotions.S GlobalTheory.Count

section Lie

variable {A : Type} [CommRing A] {n : ℕ}

theorem hform_eq_dot (s : A →+* A) (M : Matrix (Fin n) (Fin n) A) (u u' : Fin n → A) :
    Formalism.UG.hform s M u u' = (fun i => s (u i)) ⬝ᵥ (M *ᵥ u') := by
  unfold Formalism.UG.hform
  simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem hform_skew (s : A →+* A) (J Y : Matrix (Fin n) (Fin n) A) (u u' : Fin n → A) :
    Formalism.UG.hform s J (Y *ᵥ u) u' + Formalism.UG.hform s J u (Y *ᵥ u') =
      Formalism.UG.hform s (Formalism.UG.cT s Y * J + J * Y) u u' := by
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot]
  have h1 : (fun i => s ((Y *ᵥ u) i)) = (Y.map s) *ᵥ (fun i => s (u i)) := by
    funext i

    simp [mulVec, dotProduct, map_sum, map_mul]
  have h2 : ((Y.map s) *ᵥ (fun i => s (u i))) ⬝ᵥ (J *ᵥ u') =
      (fun i => s (u i)) ⬝ᵥ (((Y.map s)ᵀ * J) *ᵥ u') := by
    rw [← mulVec_mulVec, dotProduct_mulVec (fun i => s (u i)) (Y.map s)ᵀ, vecMul_transpose]
  rw [h1, h2, mulVec_mulVec, ← dotProduct_add, ← add_mulVec]
  rfl

private lemma hform_single_single' (s : A →+* A) (M : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    Formalism.UG.hform s M (Pi.single i 1) (Pi.single j 1) = M i j := by
  rw [hform_eq_dot]
  have e : (fun a => s ((Pi.single i (1 : A) : Fin n → A) a)) = (Pi.single i 1 : Fin n → A) := by
    funext a
    by_cases h : a = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  rw [e]
  simp

theorem skew_iff (s : A →+* A) (J Y : Matrix (Fin n) (Fin n) A) :
    Formalism.UG.cT s Y * J + J * Y = 0 ↔ GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets.IsSkew s J Y := by
  constructor
  · intro h u u'
    rw [hform_skew, h, hform_eq_dot, zero_mulVec, dotProduct_zero]
  · intro h
    ext i j
    rw [Matrix.zero_apply, ← hform_single_single' s (Formalism.UG.cT s Y * J + J * Y) i j, ← hform_skew]
    exact h _ _

end Lie

variable (I : AutInst)

end GlobalTheory.CoverRadiiEq
end
end

section

open MeasureTheory NumberField Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.CountBridge

theorem fdegOf_eq_of_isFdeg {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (μ : Measure (Formalism.REAL.UJ ε))
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d : ℝ) (hd : IsFdeg μ σ d) (w : H) (hw : ‖w‖ = 1) :
    fdegOf μ σ w = d := by
  obtain ⟨hpos, h⟩ := hd
  have h2 := (h w w w w).2
  have h3 : (fun g => coefOn (ε := ε) σ w w g * star (coefOn σ w w g)) =
      fun g => (((‖coefOn (ε := ε) σ w w g‖ ^ 2 : ℝ)) : ℂ) := by
    funext g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h3, integral_complex_ofReal, inner_self_eq_norm_sq_to_K, hw] at h2
  have h4 : ∫ g, ‖coefOn (ε := ε) σ w w g‖ ^ 2 ∂μ = 1 / d := by
    apply Complex.ofReal_injective
    rw [h2]
    simp
  unfold fdegOf
  rw [h4, hw]
  simp

theorem le_exp_of_log_le {x y : ℝ} (h : Real.log x ≤ y) : x ≤ Real.exp y :=
  (Real.le_exp_log x).trans (Real.exp_le_exp.mpr h)

theorem one_le_rd (I : AutInst) : 1 ≤ I.rd := by
  unfold AutInst.rd
  apply Real.one_le_rpow
  · have h : (1 : ℤ) ≤ |discr I.E| := Int.one_le_abs (discr_ne_zero I.E)
    exact_mod_cast h
  · positivity

theorem count_unbundled : GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem.CountingTheorem → ∀ A : ℝ, ∃ (n₀ : ℕ) (C₀ : ℝ), 0 ≤ C₀ ∧ ∀ n₁ ≥ n₀, ∀ C ≥ C₀, ∀ (I : AutInst) (b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ) (g g₀ : ℕ) (e : I.Gf → ℂ) (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)] [∀ v, CompleteSpace (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v) (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs] (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) (h : ℝ), (n₁ ≤ I.n ∧ (∃ p q : ℕ, (∀ v, I.pAt v = p ∧ I.qAt v = q) ∧ q ^ 2 ≤ I.n) ∧ 2 ≤ b ∧ Real.log (Real.log I.rd) ≤ I.n ∧ (∀ v, Formalism.QuantumDeterminants.IsHCParam (lam v)) ∧ (∀ v a, |lam v a| ≤ b ^ 2) ∧ I.IsAdmIdem μf g g₀ e ∧ 1 ≤ g ∧ (g : ℝ) ≤ b ^ A ∧ g₀.Prime ∧ 4 * I.n < g₀ ∧ ∀ P : Ideal (𝓞 I.E), P.IsMaximal → ((g₀ : 𝓞 I.E) ∈ P) → Ideal.absNorm P = g₀ ∧ (g₀ : 𝓞 I.E) ∉ P ^ 2) → ((∀ v, IsDS (I.ε v) (lam v) (σ v)) ∧ (∀ v, IsLowUnit (I.ε v) (lam v) (σ v) (w v)) ∧ I.IsHilbTensor σ σs tens ∧ μf.IsHaarMeasure ∧ I.IsFundDom (I.muA μf) fund ∧ I.IsRightReg μf fund R ∧ I.IsRConvF μf fund R e Re) → (∀ v, Formalism.QuantumDeterminants.GapAtLeast (I.ε v) (lam v) h) → C * (I.n : ℝ) ^ 19 * (I.f : ℝ) ^ 5 * Real.log (b * I.rd) ≤ h → Real.log (I.f : ℝ) ≤ Real.sqrt (I.n : ℝ) → Real.log (Real.log b) ≤ 1 / 16 * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ) → |(I.Dcount σs μf fund R Re : ℝ) - I.Dstar (∏ v, fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)) μf fund e| ≤ Real.exp (-(1 / 16) * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ)) * I.Dstar (∏ v, fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)) μf fund e := by
  intro hT A
  obtain ⟨n₀, hn₀⟩ := hT A
  refine ⟨n₀, max 0 (8 * 10 ^ 14 * (A + 4)), le_max_left _ _, ?_⟩
  intro n₁ hn₁ C hC I b lam g g₀ e H _ _ _ σ w Hs _ _ _ σs tens μf _ fund R Re h
    ⟨hn, ⟨p, q, hpq, hq⟩, hb, hrd, hHC, hlam, hadm, hg, hgb, hpr, hg₀, hsplit⟩
    ⟨hDS, hlow, htens, hhaar, hfund, hR, hRe⟩ hgap hh hf hbb
  let B : RowsAut :=
    { I := I, μf := μf, haar := hhaar, fund := fund, fund_spec := hfund, lam := lam, H := H, σ := σ,
      w := w, Hs := Hs, σs := σs, tens := tens, tens_spec := htens, R := R, R_spec := hR, g := g,
      g₀ := g₀, e := e, e_adm := hadm, Re := Re, Re_spec := hRe }
  have hfd : ∀ v, IsFdeg (Formalism.REAL.muG (I.ε v)) (σ v) (fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)) := by
    intro v
    obtain ⟨_, hnt, hU, hirr, hsq, -⟩ := hDS v
    obtain ⟨d, hd⟩ := GlobalTheory.schur_orthogonality_unitary I.n (I.ε v) (H v) (σ v) hU hirr hsq
    rw [fdegOf_eq_of_isFdeg _ _ d hd _ (hlow v).1]
    exact hd
  have hlog : 0 ≤ Real.log (b * I.rd) := by
    apply Real.log_nonneg
    have := one_le_rd I
    nlinarith
  have hC' : 8 * 10 ^ 14 * (A + 4) ≤ C := (le_max_right _ _).trans hC
  have hH : GlobalTheory.Count.CountHyp B A n₀ (fun v => fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)) p q b := by
    refine ⟨fun v => ⟨hHC v, hDS v, hlow v, hfd v⟩, hpq, le_trans hn₁ hn, hq, le_exp_of_log_le hrd, hf, hb,
      le_exp_of_log_le hbb, hlam, hg, hgb, hpr, hg₀, GlobalTheory.T.ncard_primesOver_eq_finrank_of_unramified_split I.E g₀ hpr hsplit, ?_⟩
    intro v a a' haa
    refine le_trans ?_ (hgap v a a' haa)
    refine le_trans ?_ hh
    show 8 * 10 ^ 14 * (A + 4) * (I.n : ℝ) ^ 19 * (I.f : ℝ) ^ 5 * Real.log (b * I.rd) ≤ _
    gcongr
  have hres := (hn₀ B _ p q b hH).2
  have he : -(1 / 16) * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ) =
      -(1 / 16 * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ)) := by ring
  rw [he]
  exact hres

end GlobalTheory.CountBridge
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.StepLoc

open GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace

theorem stepSpace_props_of_diff : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ), IsURepOn (UJset ε) σ → (∀ P, ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsDiffVec ε σ w) → ∀ P : ℕ, IsKStableOn ε σ (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P) ∧ (∀ X, inG ε X → ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, HasDerivAt (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit σ X w) (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X w) 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ (P + 1)) ∧ ∀ X, inG ε X → ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, ∀ w' ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, ∀ c : ℂ, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X (w + c • w') = GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X w + c • GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X w' := by
  intro n ε H _ _ _ σ lam hU hd P
  have hσ : IsCRepOn (UJset ε) σ := hU.1
  refine ⟨?_, fun X hX w hw => ⟨(hd P w hw X hX).hasDerivAt, ?_⟩,
    fun X hX w hw w' hw' c => dAct_add_smul (hd P w hw X hX) (hd P w' hw' X hX) c⟩
  · intro g hg v hv
    have : stepSpace ε lam σ P ≤ (stepSpace ε lam σ P).comap (σ g : H →ₗ[ℂ] H) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨l, u, hl, hX, hu, rfl⟩
      change σ g (dWord σ l u) ∈ stepSpace ε lam σ P
      rw [dWord_conj hσ hd hg hu l hX]
      refine dWord_mem (by simpa using hl) ?_ (lowKSub_stable ε lam σ g hg u hu)
      intro Y hY
      obtain ⟨X, hXl, rfl⟩ := List.mem_map.mp hY
      exact inG_conj hg (hX X hXl)
    exact this hv
  · induction hw using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨l, u, hl, hl', hu, rfl⟩ := hv
      refine dWord_mem (l := X :: l) (by simpa using hl) ?_ hu
      intro Y hY
      rcases List.mem_cons.mp hY with rfl | h
      · exact hX
      · exact hl' Y h
    | zero => rw [dAct_zero]; exact Submodule.zero_mem _
    | add x y hx hy ihx ihy =>
      have := dAct_add_smul (hd P x hx X hX) (hd P y hy X hX) 1
      rw [one_smul, one_smul] at this
      rw [this]
      exact Submodule.add_mem _ ihx ihy
    | smul c x hx ihx =>
      have := dAct_add_smul (hd P 0 (Submodule.zero_mem _) X hX) (hd P x hx X hX) c
      rw [zero_add, dAct_zero, zero_add] at this
      rw [this]
      exact Submodule.smul_mem _ c ihx

end GlobalTheory.StepLoc
end
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.IndChar

theorem isChar_iff_coord {G : Type} [Group G] (χ : G → ℂ) :
    GlobalTheory.GLq.IsChar χ ↔ GlobalTheory.BI.IsChar ℂ ℂ χ := by
  constructor
  · rintro ⟨V, hV⟩

    let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := (Module.finBasis ℂ V).equivFun
    refine ⟨Module.finrank ℂ V, GlobalTheory.BI.transportRep V.ρ e, fun g => ?_⟩
    rw [GlobalTheory.BI.character_transportRep, ← hV g]
    rfl
  · rintro ⟨n, ρ, hρ⟩
    refine ⟨FDRep.of ρ, fun g => ?_⟩
    rw [hρ g]
    rfl

theorem isChar_induced : ∀ (G : Type) [Group G] [Fintype G] (H : Subgroup G) (φ : H → ℂ), IsChar φ → IsChar (fun x : G => (Nat.card H : ℂ)⁻¹ * ∑ y : G, if h : y⁻¹ * x * y ∈ H then φ ⟨_, h⟩ else 0) := by
  intro G _ _ H φ hφ

  have hind : GlobalTheory.BI.IsChar ℂ ℂ (GlobalTheory.BI.ind H φ) :=
    GlobalTheory.BI.isChar_ind ℂ ℂ G H φ ((isChar_iff_coord φ).mp hφ)
  have heq : (fun x : G => (Nat.card H : ℂ)⁻¹ * ∑ y : G,
      if h : y⁻¹ * x * y ∈ H then φ ⟨_, h⟩ else 0) = GlobalTheory.BI.ind H φ := by
    funext x
    unfold GlobalTheory.BI.ind
    rw [finsum_eq_sum_of_fintype]
    congr 1
  rw [heq]
  exact (isChar_iff_coord _).mpr hind

end GlobalTheory.GLm.IndChar
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.IndexProd

theorem relIndex_eq_of_forall_mul {G : Type*} [Group G] {D N E : Subgroup G} (hNE : N ≤ E)
    (h : ∀ e ∈ E, ∃ n ∈ N, ∃ d ∈ D, n * d = e) : D.relIndex E = D.relIndex N := by
  symm
  refine Nat.card_congr (Equiv.ofBijective (Subgroup.quotientSubgroupOfEmbeddingOfLE D hNE)
    ⟨(Subgroup.quotientSubgroupOfEmbeddingOfLE D hNE).injective, ?_⟩)
  intro q
  induction q using QuotientGroup.induction_on with
  | H e =>
    obtain ⟨n, hn, d, hd, hnd⟩ := h e e.2
    refine ⟨QuotientGroup.mk ⟨n, hn⟩, ?_⟩
    rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [← hnd] using hd

theorem exists_mul_of_mem_sup {G : Type*} [Group G] {A M : Subgroup G}
    (h : ∀ s ∈ A, ∀ t ∈ M, s * t * s⁻¹ ∈ M) {x : G} (hx : x ∈ A ⊔ M) :
    ∃ a ∈ A, ∃ m ∈ M, a * m = x := by
  have hle : A ≤ Subgroup.normalizer M := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro t
    refine ⟨h s hs t, fun ht => ?_⟩
    have := h s⁻¹ (A.inv_mem hs) _ ht
    simpa [mul_assoc] using this
  have hx' : x ∈ ((A ⊔ M : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A M hle] at hx'
  obtain ⟨a, ha, m, hm, e⟩ := hx'
  exact ⟨a, ha, m, hm, e⟩

theorem relIndex_eq_inf_mul_sup {G : Type*} [Group G] {D A M : Subgroup G} (hDA : D ≤ A)
    (h : ∀ s ∈ A, ∀ t ∈ M, s * t * s⁻¹ ∈ M) :
    D.relIndex A = (D ⊓ M).relIndex (A ⊓ M) * (D ⊔ M).relIndex (A ⊔ M) := by
  have h1 : (D ⊔ M).relIndex (A ⊔ M) = (D ⊔ M).relIndex A :=
    relIndex_eq_of_forall_mul le_sup_left fun e he => by
      obtain ⟨a, ha, m, hm, e⟩ := exists_mul_of_mem_sup h he
      exact ⟨a, ha, m, (le_sup_right : M ≤ D ⊔ M) hm, e⟩
  have h2 : D.relIndex ((D ⊔ M) ⊓ A) = D.relIndex (A ⊓ M) :=
    relIndex_eq_of_forall_mul (le_inf (inf_le_right.trans le_sup_right) inf_le_left)
      fun e he => by
        obtain ⟨d, hd, m, hm, e'⟩ := exists_mul_of_mem_sup (fun s hs => h s (hDA hs)) he.1
        refine ⟨d * m * d⁻¹, ⟨?_, h d (hDA hd) m hm⟩, d, hd, by rw [← e']; simp⟩
        rw [e']
        exact A.mul_mem he.2 (A.inv_mem (hDA hd))
  have h3 : (D ⊓ M).relIndex (A ⊓ M) = D.relIndex (A ⊓ M) := by
    rw [← Subgroup.inf_relIndex_right D, ← Subgroup.inf_relIndex_right (D ⊓ M)]
    congr 1
    rw [inf_comm A M, ← inf_assoc, ← inf_assoc, inf_assoc D M M, inf_idem]
  rw [h1, h3, ← h2, Subgroup.relIndex_inf_mul_relIndex, inf_eq_left.2 le_sup_left]

theorem invVol_eq_inf_mul_sup_and_mono : ∀ (G : Type) [Group G] (R M A B : Subgroup G), M ≤ R → A ≤ R → B ≤ R → (∀ s ∈ R, ∀ t ∈ M, s * t * s⁻¹ ∈ M) → A.relIndex B ≠ 0 → B.relIndex A ≠ 0 → GlobalTheory.HL.invVol A B = GlobalTheory.HL.invVol (A ⊓ M) (B ⊓ M) * GlobalTheory.HL.invVol (A ⊔ M) (B ⊔ M) ∧ ∀ B' ≤ B, B'.relIndex A ≠ 0 → A.relIndex B' ≠ 0 → GlobalTheory.HL.invVol A B ≤ GlobalTheory.HL.invVol A B' ∧ GlobalTheory.HL.invVol A B ≤ (B'.relIndex A : ℝ) := by
  intro G _ R M A B _ hA hB hn hAB hBA
  constructor
  · have eA := relIndex_eq_inf_mul_sup (D := A ⊓ B) (M := M) inf_le_left
      (fun s hs => hn s (hA hs))
    have eB := relIndex_eq_inf_mul_sup (D := A ⊓ B) (M := M) inf_le_right
      (fun s hs => hn s (hB hs))
    have dA : (A ⊓ B).relIndex A ≠ 0 := by rwa [Subgroup.inf_relIndex_left]
    have dA' := dA
    rw [eA, mul_ne_zero_iff] at dA'
    rw [GlobalTheory.HL.invVol_eq_div_of_le inf_le_left inf_le_right dA,
      GlobalTheory.HL.invVol_eq_div_of_le (inf_le_inf_right M inf_le_left)
        (inf_le_inf_right M inf_le_right) dA'.1,
      GlobalTheory.HL.invVol_eq_div_of_le (sup_le_sup_right inf_le_left M)
        (sup_le_sup_right inf_le_right M) dA'.2, eA, eB]
    push_cast
    rw [div_mul_div_comm]
  · intro B' hB' h1 h2
    have dA : (A ⊓ B').relIndex A ≠ 0 := by rwa [Subgroup.inf_relIndex_left]
    have dB : (A ⊓ B').relIndex B ≠ 0 :=
      Subgroup.relIndex_inf_ne_zero hAB (Subgroup.relIndex_ne_zero_trans h1 hAB)
    have dB' : (A ⊓ B').relIndex B' ≠ 0 := by rwa [Subgroup.inf_relIndex_right]
    have hle : GlobalTheory.HL.invVol A B ≤ GlobalTheory.HL.invVol A B' := by
      rw [GlobalTheory.HL.invVol_eq_div_of_le inf_le_left (inf_le_right.trans hB') dA,
        GlobalTheory.HL.invVol_eq_div_of_le inf_le_left inf_le_right dA]
      refine div_le_div_of_nonneg_left (Nat.cast_nonneg _)
        (by exact_mod_cast Nat.pos_of_ne_zero dB') ?_
      exact_mod_cast Subgroup.relIndex_le_of_le_right hB' dB
    refine ⟨hle, hle.trans ?_⟩
    rw [GlobalTheory.HL.invVol]
    exact div_le_self (Nat.cast_nonneg _) (by exact_mod_cast Nat.pos_of_ne_zero h2)

end GlobalTheory.IndexProd
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.haarInvVolumeRelIndex_pi_univ_eq_finprod : ∀ {ι : Type} {G : ι → Type} [∀ i, Group (G i)] (K U : ∀ i, Subgroup (G i)), {i | K i ≠ U i}.Finite → (∀ i, (K i).relIndex (U i) ≠ 0 ∧ (U i).relIndex (K i) ≠ 0) → (Subgroup.pi Set.univ K).relIndex (Subgroup.pi Set.univ U) ≠ 0 ∧ (Subgroup.pi Set.univ U).relIndex (Subgroup.pi Set.univ K) ≠ 0 ∧ invVol (Subgroup.pi Set.univ K) (Subgroup.pi Set.univ U) = ∏ᶠ i, invVol (K i) (U i) := by
  first | exact @GlobalTheory.HL.invVol_pi_univ | exact GlobalTheory.HL.invVol_pi_univ | (intros; apply GlobalTheory.HL.invVol_pi_univ <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.primitiveTuples_hermitianGram_coset_content : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ m : ℕ, 2 * m + 3 ≤ n → ∀ B : Set (Matrix (Fin m) (Fin m) E), (∀ X ∈ B, X ∈ hermLat L m) → IsCO (hermLat L m) B → IsCO (tupLat L Λs m) {z : Fin m → Fin n → E | IsPrimT L Hm Λs z ∧ gramT L Hm z ∈ B} ∧ cont (hermLat L m) B ≤ 2 * cont (tupLat L Λs m) {z : Fin m → Fin n → E | IsPrimT L Hm Λs z ∧ gramT L Hm z ∈ B} ∧ cont (tupLat L Λs m) {z : Fin m → Fin n → E | IsPrimT L Hm Λs z ∧ gramT L Hm z ∈ B} ≤ 2 * cont (hermLat L m) B := by
  first | exact @GlobalTheory.HL.PrimVol.cont_primitive_tuples | exact GlobalTheory.HL.PrimVol.cont_primitive_tuples | (intros; apply GlobalTheory.HL.PrimVol.cont_primitive_tuples <;> assumption)
end
