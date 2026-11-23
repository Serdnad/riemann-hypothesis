module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle472
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle475
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle055
public import Formalism.RealPlaceAnalysis.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowMulRowGLInv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle462
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle465
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle466
public import GroundTheory.AutomorphicForms.FourierWhittaker.IsAddFundamentalDomainImageOfMapVecLattice
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle463
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SphOff

@[expose] public section

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount

theorem spinM_vacuum_lowest : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ), IsCliff c →
    ∀ q : ι → ℂ, (∀ a b, a < b → c b a *ᵥ q = 0) →
    (∀ a, spinM c a a *ᵥ q = ((-(rhoV n a) : ℝ) : ℂ) • q) ∧ ∀ a b, a < b → spinM c b a *ᵥ q = 0 := by
  intro n ι _ _ c hc q hq
  obtain ⟨h1, _⟩ := hc
  have two : (2 : Matrix ι ι ℂ) *ᵥ q = (2 : ℂ) • q := by
    have : (2 : Matrix ι ι ℂ) = (2 : ℂ) • (1 : Matrix ι ι ℂ) := by
      rw [two_smul]; exact one_add_one_eq_two.symm
    rw [this, Matrix.smul_mulVec, Matrix.one_mulVec]
  have anti : ∀ a b d e, c a b *ᵥ (c d e *ᵥ q) =
      (if a = e ∧ b = d then (2 : ℂ) • q else 0) - c d e *ᵥ (c a b *ᵥ q) := by
    intro a b d e
    have h := congrArg (fun M => M *ᵥ q) (h1 a b d e)
    simp only [Matrix.add_mulVec, Matrix.mulVec_mulVec] at h
    simp only [Matrix.mulVec_mulVec]
    rw [eq_sub_iff_add_eq, h]
    split_ifs
    · exact two
    · simp
  have sumv : ∀ (a b : Fin n), (∑ e, c a e * c e b) *ᵥ q = ∑ e, c a e *ᵥ (c e b *ᵥ q) := by
    intro a b
    simp only [Matrix.mulVec_mulVec]
    exact map_sum (Matrix.mulVec.addMonoidHomLeft q) _ _
  have hT : ∀ a e : Fin n, c a e *ᵥ (c e a *ᵥ q) =
      (if e < a then (2 : ℂ) else if e = a then 1 else 0) • q := by
    intro a e
    rcases lt_trichotomy e a with h | h | h
    · rw [if_pos h, anti a e e a, hq e a h]
      simp
    · subst h
      have h2 := anti e e e e
      simp only [and_self, if_true] at h2
      have h3 : (2 : ℂ) • (c e e *ᵥ (c e e *ᵥ q)) = (2 : ℂ) • q := by
        rw [two_smul]
        nth_rewrite 1 [h2]
        rw [two_smul]
        abel
      have h4 := smul_right_injective (ι → ℂ) (two_ne_zero : (2 : ℂ) ≠ 0) h3
      simpa using h4
    · rw [if_neg (not_lt.mpr h.le), if_neg h.ne', hq a e h]
      simp
  have hs : ∀ a : Fin n, ∑ e : Fin n, (if e < a then (2 : ℂ) else if e = a then 1 else 0) =
      2 * ((a : ℕ) : ℂ) + 1 := by
    intro a
    have h0 : ∀ e : Fin n, (if e < a then (2 : ℂ) else if e = a then 1 else 0) =
        (if e < a then 2 else 0) + (if e = a then 1 else 0) := by
      intro e
      rcases lt_trichotomy e a with h | h | h
      · simp [h, h.ne]
      · simp [h]
      · simp [not_lt.mpr h.le, h.ne']
    simp only [h0]
    rw [sum_add_distrib, ← Finset.sum_filter]
    have h5 : univ.filter (fun e : Fin n => e < a) = Finset.Iio a := by ext; simp
    rw [h5]
    simp [Fin.card_Iio, mul_comm]
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · unfold spinM
    rw [if_pos rfl, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sumv]
    simp only [hT]
    rw [← Finset.sum_smul, hs, smul_smul, ← sub_smul]
    congr 1
    simp only [rhoV]
    push_cast
    ring
  · unfold spinM
    rw [if_neg hab.ne', sub_zero, Matrix.smul_mulVec, sumv]
    have : ∀ e : Fin n, c b e *ᵥ (c e a *ᵥ q) = 0 := by
      intro e
      rcases lt_trichotomy e a with h | h | h
      · rw [anti b e e a, if_neg (fun hh => hab.ne' hh.1), hq e b (h.trans hab)]
        simp
      · subst h
        rw [anti b e e e, if_neg (fun hh => hab.ne' hh.1), hq e b hab]
        simp
      · rw [hq a e h]
        simp
    simp [this]

end GlobalTheory.CompanionTheory.RealCount
end
end

section

open Matrix
open GlobalTheory.CompanionTheory.GLK (expG)
open PositivityTheory.RgBcC.Real (uG)
open PositivityTheory.RgTw (Mat G)

namespace GlobalTheory.CompanionTheory.UnitaryExp

theorem exists_unitary_diag {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (h1 : Kᴴ * K = 1) (h2 : K * Kᴴ = 1) :
    ∃ (V : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ), Vᴴ * V = 1 ∧ V * Vᴴ = 1 ∧
      Vᴴ * K * V = Matrix.diagonal z ∧ ∀ a, ‖z a‖ = 1 := by
  classical
  set A : Matrix (Fin n) (Fin n) ℂ := K + Kᴴ with hA
  set B : Matrix (Fin n) (Fin n) ℂ := Complex.I • (K - Kᴴ) with hB
  have hAh : Aᴴ = A := by
    simp [hA, Matrix.conjTranspose_add, add_comm]
  have hBh : Bᴴ = B := by
    simp [hB, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, smul_sub]
    abel
  have hAB : A * B = B * A := by
    have e : (K + Kᴴ) * (K - Kᴴ) = (K - Kᴴ) * (K + Kᴴ) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, h1, h2]
      abel
    rw [hA, hB, Matrix.mul_smul, Matrix.smul_mul, e]
  obtain ⟨V, hV, hD⟩ := GlobalTheory.CompanionTheory.SimDiag.exists_unitary_isDiag ({A, B} : Set (Matrix (Fin n) (Fin n) ℂ))
    (by
      rintro X (rfl | rfl)
      · exact hAh
      · exact hBh)
    (by
      rintro X (rfl | rfl) Y (rfl | rfl)
      · rfl
      · exact hAB
      · exact hAB.symm
      · rfl)
  have hV1 : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.1 hV
  have hV2 : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hV
  have hKAB : K = (1 / 2 : ℂ) • (A - Complex.I • B) := by
    simp only [hA, hB, smul_smul, Complex.I_mul_I]
    module
  have hDd : (Vᴴ * K * V).IsDiag := by
    have e : Vᴴ * K * V = (1 / 2 : ℂ) • (Vᴴ * A * V - Complex.I • (Vᴴ * B * V)) := by
      conv_lhs => rw [hKAB]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]
    rw [e]
    exact ((hD A (by simp)).sub ((hD B (by simp)).smul _)).smul _
  refine ⟨V, Matrix.diag (Vᴴ * K * V), hV1, hV2, hDd.diagonal_diag.symm, fun a => ?_⟩
  set D := Vᴴ * K * V with hDdef
  have hDD : Dᴴ * D = 1 := by
    have e : Dᴴ = Vᴴ * Kᴴ * V := by
      simp [hDdef, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [e, hDdef]
    calc Vᴴ * Kᴴ * V * (Vᴴ * K * V) = Vᴴ * Kᴴ * (V * Vᴴ) * K * V := by
          simp only [Matrix.mul_assoc]
      _ = Vᴴ * (Kᴴ * K) * V := by
          rw [hV2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, hV1]
  have hent : star (D a a) * D a a = 1 := by
    have h := congrFun (congrFun hDD a) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a] at h
    · simpa [Matrix.conjTranspose_apply] using h
    · intro b _ hb
      have : D b a = 0 := hDd hb
      simp [this]
    · simp
  have hn : ‖D a a‖ ^ 2 = 1 := by
    have h3 : ((‖D a a‖ ^ 2 : ℝ) : ℂ) = 1 := by
      have := Complex.conj_mul' (D a a)
      push_cast
      rw [← this]
      simpa using hent
    exact_mod_cast h3
  have h0 : 0 ≤ ‖D a a‖ := norm_nonneg _
  show ‖D a a‖ = 1
  nlinarith [sq_nonneg (‖D a a‖ - 1), sq_nonneg (‖D a a‖ + 1)]

theorem exists_skew_exp_eq (n : ℕ) (k : Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ X : Mat n, Xᴴ = -X ∧ uG k = expG X 1 := by
  classical
  have h1 : (k : Matrix (Fin n) (Fin n) ℂ)ᴴ * (k : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 k.2
  have h2 : (k : Matrix (Fin n) (Fin n) ℂ) * (k : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.1 k.2
  obtain ⟨V, z, hV1, hV2, hD, hz⟩ := exists_unitary_diag _ h1 h2
  set w : Fin n → ℂ := fun a => (Complex.arg (z a) : ℂ) * Complex.I with hw
  have hexp : ∀ a, NormedSpace.exp (w a) = z a := by
    intro a
    have := Complex.norm_mul_exp_arg_mul_I (z a)
    rw [hz a] at this
    simpa [hw, Complex.exp_eq_exp_ℂ] using this
  have hk : (k : Matrix (Fin n) (Fin n) ℂ) = V * Matrix.diagonal z * Vᴴ := by
    rw [← hD]
    calc (k : Matrix (Fin n) (Fin n) ℂ)
        = (V * Vᴴ) * (k : Matrix (Fin n) (Fin n) ℂ) * (V * Vᴴ) := by
          rw [hV2]; simp
      _ = V * (Vᴴ * (k : Matrix (Fin n) (Fin n) ℂ) * V) * Vᴴ := by
          simp only [Matrix.mul_assoc]
  refine ⟨V * Matrix.diagonal w * Vᴴ, ?_, ?_⟩
  · have hs : star w = -w := by
      funext a
      simp [hw]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose, hs, Matrix.mul_assoc]
    have hn : Matrix.diagonal (-w) = -Matrix.diagonal w := (Matrix.diagonal_neg w).symm
    rw [hn, Matrix.neg_mul, Matrix.mul_neg]
  · refine Units.ext ?_
    let Vu : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨V, Vᴴ, hV2, hV1⟩
    have e := Matrix.exp_units_conj Vu (Matrix.diagonal w)
    have e2 : NormedSpace.exp (Matrix.diagonal w) = Matrix.diagonal z := by
      rw [Matrix.exp_diagonal]
      congr 1
      funext a
      rw [Pi.exp_def]
      exact hexp a
    rw [e2] at e
    have e3 : ((expG (V * Matrix.diagonal w * Vᴴ) 1 : G n) : Mat n) =
        NormedSpace.exp (V * Matrix.diagonal w * Vᴴ) := by
      delta expG
      simp only [IsUnit.unit_spec, Complex.ofReal_one, one_smul]
    rw [e3]
    exact hk.trans e.symm

end GlobalTheory.CompanionTheory.UnitaryExp
end

section

noncomputable section

open Matrix
open PositivityTheory.RgTw (Mat)

namespace GlobalTheory.CompanionTheory.GLK.Pair

section Ring

variable {A : Type*} [Ring A] [Algebra ℂ A]

theorem brk_ee (p q r s P Q : A) (h1 : p * r - r * p = P) (h2 : q * r - r * q = Q) (h3 : p * s - s * p = Q)
    (h4 : q * s - s * q = -P) :
    ((1 / 2 : ℂ) • (p - Complex.I • q)) * ((1 / 2 : ℂ) • (r - Complex.I • s))
      - ((1 / 2 : ℂ) • (r - Complex.I • s)) * ((1 / 2 : ℂ) • (p - Complex.I • q))
      = (1 / 2 : ℂ) • (P - Complex.I • Q) := by
  subst h1 h2
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul]
  linear_combination (norm := skip) (-(Complex.I / 4)) • h3 + (-(1 / 4) : ℂ) • h4
  match_scalars <;> (ring_nf; try simp [Complex.I_sq]; try ring)

theorem brk_ff (p q r s P Q : A) (h1 : p * r - r * p = P) (h2 : q * r - r * q = Q) (h3 : p * s - s * p = Q)
    (h4 : q * s - s * q = -P) :
    ((1 / 2 : ℂ) • (p + Complex.I • q)) * ((1 / 2 : ℂ) • (r + Complex.I • s))
      - ((1 / 2 : ℂ) • (r + Complex.I • s)) * ((1 / 2 : ℂ) • (p + Complex.I • q))
      = (1 / 2 : ℂ) • (P + Complex.I • Q) := by
  subst h1 h2
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
  linear_combination (norm := skip) (Complex.I / 4) • h3 + (-(1 / 4) : ℂ) • h4
  match_scalars <;> (ring_nf; try simp [Complex.I_sq]; try ring)

theorem brk_ef (p q r s P Q : A) (h1 : p * r - r * p = P) (h2 : q * r - r * q = Q) (h3 : p * s - s * p = Q)
    (h4 : q * s - s * q = -P) :
    ((1 / 2 : ℂ) • (p - Complex.I • q)) * ((1 / 2 : ℂ) • (r + Complex.I • s))
      = ((1 / 2 : ℂ) • (r + Complex.I • s)) * ((1 / 2 : ℂ) • (p - Complex.I • q)) := by
  subst h1 h2
  simp only [sub_mul, mul_sub, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_sub, smul_add, smul_smul]
  linear_combination (norm := skip) (Complex.I / 4) • h3 + (1 / 4 : ℂ) • h4
  match_scalars <;> (ring_nf; try simp [Complex.I_sq]; try ring)

end Ring

section Main

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def eP (D : Mat n → Module.End ℂ V) (Z : Mat n) : Module.End ℂ V :=
  (1 / 2 : ℂ) • (D Z - Complex.I • D (Complex.I • Z))

def fP (D : Mat n → Module.End ℂ V) (Z : Mat n) : Module.End ℂ V :=
  (1 / 2 : ℂ) • (D Z + Complex.I • D (Complex.I • Z))

theorem first_generator_eq_single (D : Mat n → Module.End ℂ V) (a b : Fin n) : e1 D a b = eP D (Matrix.single a b 1) := by
  simp [e1, eP, Matrix.smul_single]

theorem second_generator_eq_single (D : Mat n → Module.End ℂ V) (a b : Fin n) : f1 D a b = fP D (Matrix.single a b 1) := by
  simp [f1, fP, Matrix.smul_single]

variable {D : Mat n → Module.End ℂ V}

theorem D_neg (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X) (X : Mat n) : D (-X) = -D X := by
  simpa using hs (-1) X

theorem D_zero (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X) : D (0 : Mat n) = 0 := by
  simpa using hs 0 0

theorem D_sub (ha : ∀ X Y, D (X + Y) = D X + D Y) (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (X Y : Mat n) : D (X - Y) = D X - D Y := by
  rw [sub_eq_add_neg, ha, D_neg hs, sub_eq_add_neg]

theorem eP_zero (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X) : eP D (0 : Mat n) = 0 := by
  simp [eP, D_zero hs]

theorem fP_zero (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X) : fP D (0 : Mat n) = 0 := by
  simp [fP, D_zero hs]

theorem eP_sub (ha : ∀ X Y, D (X + Y) = D X + D Y) (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (X Y : Mat n) : eP D (X - Y) = eP D X - eP D Y := by
  simp only [eP, smul_sub, D_sub ha hs]
  abel

theorem fP_sub (ha : ∀ X Y, D (X + Y) = D X + D Y) (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (X Y : Mat n) : fP D (X - Y) = fP D X - fP D Y := by
  simp only [fP, smul_sub, smul_add, D_sub ha hs]
  abel

theorem brk_four (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (hb : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) (Z W : Mat n) :
    D Z * D W - D W * D Z = D (Z * W - W * Z) ∧
    D (Complex.I • Z) * D W - D W * D (Complex.I • Z) = D (Complex.I • (Z * W - W * Z)) ∧
    D Z * D (Complex.I • W) - D (Complex.I • W) * D Z = D (Complex.I • (Z * W - W * Z)) ∧
    D (Complex.I • Z) * D (Complex.I • W) - D (Complex.I • W) * D (Complex.I • Z) = -D (Z * W - W * Z) := by
  refine ⟨(hb Z W).symm, ?_, ?_, ?_⟩
  · rw [← hb]
    congr 1
    simp [smul_sub]
  · rw [← hb]
    congr 1
    simp [smul_sub]
  · rw [← hb, ← D_neg hs]
    congr 1
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I, neg_smul, one_smul]
    abel

theorem eP_brk (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (hb : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) (Z W : Mat n) :
    eP D Z * eP D W - eP D W * eP D Z = eP D (Z * W - W * Z) := by
  obtain ⟨h1, h2, h3, h4⟩ := brk_four hs hb Z W
  exact brk_ee _ _ _ _ _ _ h1 h2 h3 h4

theorem fP_brk (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (hb : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) (Z W : Mat n) :
    fP D Z * fP D W - fP D W * fP D Z = fP D (Z * W - W * Z) := by
  obtain ⟨h1, h2, h3, h4⟩ := brk_four hs hb Z W
  exact brk_ff _ _ _ _ _ _ h1 h2 h3 h4

theorem eP_fP_comm (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (hb : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) (Z W : Mat n) :
    eP D Z * fP D W = fP D W * eP D Z := by
  obtain ⟨h1, h2, h3, h4⟩ := brk_four hs hb Z W
  exact brk_ef _ _ _ _ _ _ h1 h2 h3 h4

theorem single_brk (a b c d : Fin n) :
    (Matrix.single a b (1 : ℂ)) * Matrix.single c d 1 - Matrix.single c d (1 : ℂ) * Matrix.single a b 1 =
      (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) := by
  have h : ∀ a b c d : Fin n, (Matrix.single a b (1 : ℂ)) * Matrix.single c d 1 =
      if b = c then Matrix.single a d 1 else 0 := by
    intro a b c d
    split_ifs with h
    · subst h; simp
    · exact Matrix.single_mul_single_of_ne a b c h 1 (c := (1 : ℂ))
  rw [h, h]

theorem eP_units (ha : ∀ X Y, D (X + Y) = D X + D Y) (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (hb : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) (a b c d : Fin n) :
    e1 D a b * e1 D c d - e1 D c d * e1 D a b =
      (if b = c then e1 D a d else 0) - (if d = a then e1 D c b else 0) := by
  simp only [first_generator_eq_single]
  rw [eP_brk hs hb, single_brk, eP_sub ha hs]
  split_ifs <;> simp [eP_zero hs]

theorem fP_units (ha : ∀ X Y, D (X + Y) = D X + D Y) (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X)
    (hb : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) (a b c d : Fin n) :
    f1 D a b * f1 D c d - f1 D c d * f1 D a b =
      (if b = c then f1 D a d else 0) - (if d = a then f1 D c b else 0) := by
  simp only [second_generator_eq_single]
  rw [fP_brk hs hb, single_brk, fP_sub ha hs]
  split_ifs <;> simp [fP_zero hs]

end Main

theorem gl_pair : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (D : Mat n → Module.End ℂ V),
    (∀ X Y, D (X + Y) = D X + D Y) → (∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X) →
    (∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) →
    Formalism.REAL.GlRel (e1 D) ∧ Formalism.REAL.GlRel (e2 D) ∧ ∀ a b c d, e1 D a b * e2 D c d = e2 D c d * e1 D a b := by
  intro n V _ _ D ha hs hb
  refine ⟨fun a b c d => eP_units ha hs hb a b c d, fun a b c d => ?_, fun a b c d => ?_⟩
  · have h := fP_units ha hs hb b a d c
    simp only [e2, neg_mul_neg]
    rw [h]
    simp only [eq_comm (a := b) (b := c), eq_comm (a := d) (b := a)]
    split_ifs <;> simp <;> abel
  · simp only [e2, mul_neg, neg_mul, first_generator_eq_single, second_generator_eq_single]
    rw [eP_fP_comm hs hb]

end GlobalTheory.CompanionTheory.GLK.Pair

end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

theorem _root_.GlobalTheory.T.infinite_vector_measure_isAddHaar : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (k : ℕ), (nuInf E k).IsAddHaarMeasure := by
  first | exact @GlobalTheory.CompanionTheory.CutOff.nuInf_isAddHaarMeasure | exact GlobalTheory.CompanionTheory.CutOff.nuInf_isAddHaarMeasure | (intros; apply GlobalTheory.CompanionTheory.CutOff.nuInf_isAddHaarMeasure <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

theorem _root_.GlobalTheory.T.box_fourier_integral_bound : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ} {ψ : AddChar (Ad E) ℂ}, (∀ x, ‖ψ x‖ = 1) → Continuous ψ → ∀ (L : AddSubgroup (Af E)), IsCompact (L : Set (Af E)) → IsOpen (L : Set (Af E)) → ∀ (c z : Fin k → Af E), ‖∫ f, (((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) * ψ (sFin E (∑ i, f i * z i)) ∂nuFin E k‖ ≤ (nuFin E k).real (boxL (L : Set (Af E)) c) ∧ (∫ f, (((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) * ψ (sFin E (∑ i, f i * z i)) ∂nuFin E k ≠ 0 → ∀ i, ∀ a ∈ L, ψ (sFin E (a * z i)) = 1) := by
  first | exact @GlobalTheory.CompanionTheory.CutOff.FinFT.box_fourier_main | exact GlobalTheory.CompanionTheory.CutOff.FinFT.box_fourier_main | (intros; apply GlobalTheory.CompanionTheory.CutOff.FinFT.box_fourier_main <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

theorem _root_.GlobalTheory.T.smooth_cutoff_translate_contDiff : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ} {φ : XB E k}, SmV (repI E k) φ → ∀ {b : (Fin k → Cinf E) → ℝ}, ContDiff ℝ ∞ b → (∀ x ∈ tsupport b, IsUnit (lastEnt x)) → ContDiff ℝ ∞ fun x => (b x : ℂ) • Rt E k (infGL E k (rowGL x))⁻¹ φ := by
  first | exact @GlobalTheory.CompanionTheory.CutOff.contDiff_cut_orbit | exact GlobalTheory.CompanionTheory.CutOff.contDiff_cut_orbit | (intros; apply GlobalTheory.CompanionTheory.CutOff.contDiff_cut_orbit <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

theorem _root_.GlobalTheory.T.adelic_vector_integral_product : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ} (A : (Fin k → Cinf E) → ℂ) (B : (Fin k → Af E) → ℂ), ∫ y, A (fun i => pInf E (y i)) * B (fun i => pFin E (y i)) ∂vecMeasure E (Fin k) = (∫ x, A x ∂nuInf E k) * ∫ f, B f ∂nuFin E k := by
  first | exact @GlobalTheory.CompanionTheory.CutOff.Split.integral_split | exact GlobalTheory.CompanionTheory.CutOff.Split.integral_split | (intros; apply GlobalTheory.CompanionTheory.CutOff.Split.integral_split <;> assumption)
end
