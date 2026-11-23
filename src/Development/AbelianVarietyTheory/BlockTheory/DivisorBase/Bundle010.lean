module

public import Formalism.LocalToGlobal.Divisibility.Numbers
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.Columns.Bundle013
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open scoped ComplexOrder Matrix
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum

section Defs

variable {K : Type} [Field K] [StarRing K] {ι : Type} [Fintype ι] {N n : ℕ}

def gramSum (hN : N = n + 1) (G' : Matrix (Fin n) (Fin n) K) (g : K) : Matrix (Fin N) (Fin N) K :=
  Matrix.of fun a b =>
    if ha : a.1 < n then (if hb : b.1 < n then G' ⟨a.1, ha⟩ ⟨b.1, hb⟩ else 0)
    else (if b.1 < n then 0 else if a = Br.iL hN ∧ b = Br.iL hN then g else 0)

def normSqAt (s : K →+* ℂ) (lam : ι → DomWeight N) (G : ι → Matrix (Fin N) (Fin N) K) (f : VV K lam) : ℝ :=
  (s (pairK lam G f f)).re

def IsScaledCoisometry (s : K →+* ℂ) (lam : ι → DomWeight N) (G : ι → Matrix (Fin N) (Fin N) K)
    (sg : ι → DomWeight n) (G' : ι → Matrix (Fin n) (Fin n) K) (P : VV K lam →ₗ[K] VV K sg) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∃ A : VV K sg →ₗ[K] VV K lam,
    (∀ (y : VV K sg) (x : VV K lam), pairK lam G (A y) x = pairK sg G' y (P x)) ∧
    ∀ y y' : VV K sg, s (pairK lam G (A y) (A y')) = ((ρ ^ 2 : ℝ) : ℂ) * s (pairK sg G' y y')

def HasOpNormSq (s : K →+* ℂ) (lam : ι → DomWeight N) (G : ι → Matrix (Fin N) (Fin N) K)
    (sg : ι → DomWeight n) (G' : ι → Matrix (Fin n) (Fin n) K) (P : VV K lam →ₗ[K] VV K sg) (C : ℝ) : Prop :=
  (∀ f : VV K lam, normSqAt s sg G' (P f) ≤ C * normSqAt s lam G f) ∧
  ∃ f : VV K lam, f ≠ 0 ∧ normSqAt s sg G' (P f) = C * normSqAt s lam G f

def factor (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) (T : ℝ) : ℝ :=
  T ^ (-((Br.nBr lam sg : ℤ) : ℝ) / 2) * |((Br.cBr hN lam sg : ℤ) : ℝ)| * Real.sqrt (Br.kapBr ℝ hN lam sg)

def orthNormSq (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) : ℝ :=
  ∏ τ, ((Br.cBr hN (lam τ) (sg τ) : ℤ) : ℝ) ^ 2 * Br.kapBr ℝ hN (lam τ) (sg τ)

def dOne (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) : ℤ :=
  ∑ i : Fin n, min (lam.w (Br.iC hN i) - lam.w (Br.iS hN i)) (Br.d0 hN lam sg)

end Defs

def LastMapNorm : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (s : K →+* ℂ), (∀ x : K, s (star x) = (starRingEnd ℂ) (s x)) →
  ∀ (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n),
    (∀ τ, Br.Interlace hN (lam τ) (sg τ)) → (∀ τ, Br.SameShift (lam τ) (sg τ)) →
  ∀ (G' : ι → Matrix (Fin n) (Fin n) K), (∀ τ, ((G' τ).map s).PosDef) →
  ∀ (T : ℝ), 0 < T → ∀ (g t : ι → K), (∀ τ, s (star (t τ) * g τ * t τ) = (T : ℂ)) →
    (∀ τ, IsScaledCoisometry s (fun _ : Unit => lam τ) (fun _ => gramSum hN (G' τ) (g τ)) (fun _ : Unit => sg τ)
        (fun _ => G' τ) (Br.brAt hN (fun _ : Unit => lam τ) (fun _ : Unit => sg τ) fun _ => t τ)
        (factor hN (lam τ) (sg τ) T)) ∧
    IsScaledCoisometry s lam (fun τ => gramSum hN (G' τ) (g τ)) sg G' (Br.brAt hN lam sg t)
      (∏ τ, factor hN (lam τ) (sg τ) T) ∧
    HasOpNormSq s lam (fun τ => gramSum hN (G' τ) (g τ)) sg G' (Br.brAt hN lam sg t)
      (T ^ (-∑ τ, Br.nBr (lam τ) (sg τ)) * orthNormSq hN lam sg)

def OrthNormLogBound : Prop :=
  ∃ C : ℝ, ∀ (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n),
    (∀ τ, Br.Interlace hN (lam τ) (sg τ)) →
  ∀ a : ℝ, (∀ τ, (((lam τ).spread : ℤ) : ℝ) ≤ 2 * a) →
    0 < orthNormSq hN lam sg ∧
    Real.log (orthNormSq hN lam sg) ≤
      ∑ τ, (2 * ((N : ℝ) - 1) * ((dOne hN (lam τ) (sg τ) : ℤ) : ℝ) + (N : ℝ) * ((N : ℝ) - 1) / 2) * Real.log (2 * a) ∧
    ∑ τ, (2 * ((N : ℝ) - 1) * ((dOne hN (lam τ) (sg τ) : ℤ) : ℝ) + (N : ℝ) * ((N : ℝ) - 1) / 2) * Real.log (2 * a) ≤
      C * ∑ τ, ((N : ℝ) * ((dOne hN (lam τ) (sg τ) : ℤ) : ℝ) + (N : ℝ) ^ 2) * Real.log (2 * a)

section Checks

variable {K : Type} [Field K] {N n : ℕ} (hN : N = n + 1) (G' : Matrix (Fin n) (Fin n) K) (g : K)

theorem fockB_self_nonneg {σ : Type} (f : MvPolynomial σ ℝ) : 0 ≤ fockB f f :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (mul_self_nonneg _) (Nat.cast_nonneg _)

theorem factor_sq (lam : DomWeight N) (sg : DomWeight n) {T : ℝ} (hT : 0 < T) :
    factor hN lam sg T ^ 2 =
      T ^ (-Br.nBr lam sg) * (((Br.cBr hN lam sg : ℤ) : ℝ) ^ 2 * Br.kapBr ℝ hN lam sg) := by
  have hk : 0 ≤ Br.kapBr ℝ hN lam sg := div_nonneg (fockB_self_nonneg _) (fockB_self_nonneg _)
  have h1 : (T ^ (-((Br.nBr lam sg : ℤ) : ℝ) / 2)) ^ 2 = T ^ (-Br.nBr lam sg) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT.le, ← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  rw [factor, mul_pow, mul_pow, h1, sq_abs, Real.sq_sqrt hk, mul_assoc]

end Checks

end GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum
end
end

section

open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ScaledCoisometryNorms

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br

def sumGram {K : Type} [Zero K] (N : ℕ) {n : ℕ} (G' : Matrix (Fin n) (Fin n) K) (g : K) : Matrix (Fin N) (Fin N) K :=
  Matrix.of fun a b =>
    if ha : a.1 < n then (if hb : b.1 < n then G' ⟨a.1, ha⟩ ⟨b.1, hb⟩ else 0) else (if b.1 < n then 0 else g)

theorem sumGram_entries {K : Type} [Zero K] {N n : ℕ} (hN : N = n + 1) (G' : Matrix (Fin n) (Fin n) K) (g : K) :
    (∀ a b : Fin n, sumGram N G' g (iC hN a) (iC hN b) = G' a b) ∧
      (∀ a : Fin n, sumGram N G' g (iC hN a) (iL hN) = 0 ∧ sumGram N G' g (iL hN) (iC hN a) = 0) ∧
      sumGram N G' g (iL hN) (iL hN) = g := by
  refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩ <;> simp [sumGram, iC, iL]

def nrmSq {K : Type} [Field K] [StarRing K] (s : K →+* ℂ) {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (G : ι → Matrix (Fin n) (Fin n) K) (f : VV K lam) : ℝ :=
  (s (pairK lam G f f)).re

def IsScaledCoisometry {K : Type} [Field K] [StarRing K] (s : K →+* ℂ) {ι : Type} [Fintype ι] {N n : ℕ}
    (lam : ι → DomWeight N) (sg : ι → DomWeight n) (G : ι → Matrix (Fin N) (Fin N) K) (G' : ι → Matrix (Fin n) (Fin n) K)
    (P : VV K lam →ₗ[K] VV K sg) (κ : ℝ) : Prop :=
  ∃ Q : VV K sg →ₗ[K] VV K lam,
    (∀ (y : VV K sg) (f : VV K lam), pairK lam G (Q y) f = pairK sg G' y (P f)) ∧
    ∀ y y' : VV K sg, s (pairK lam G (Q y) (Q y')) = (κ : ℂ) * s (pairK sg G' y y')

def orthSq {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) : ℝ :=
  ∏ τ, ((cBr hN (lam τ) (sg τ) : ℤ) : ℝ) ^ 2 * kapBr ℝ hN (lam τ) (sg τ)

def brSq {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) (T : ℝ) : ℝ :=
  ∏ τ, T ^ (-nBr (lam τ) (sg τ)) * (((cBr hN (lam τ) (sg τ) : ℤ) : ℝ) ^ 2 * kapBr ℝ hN (lam τ) (sg τ))

def NormConcl {K : Type} [Field K] [StarRing K] (s : K →+* ℂ) {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n) (G : ι → Matrix (Fin N) (Fin N) K) (G' : ι → Matrix (Fin n) (Fin n) K)
    (t : ι → K) (T : ℝ) : Prop :=
  0 < brSq hN lam sg T ∧
  IsScaledCoisometry s lam sg G G' (brAt hN lam sg t) (brSq hN lam sg T) ∧
  (∀ f : VV K lam, nrmSq s sg G' (brAt hN lam sg t f) ≤ brSq hN lam sg T * nrmSq s lam G f) ∧
  ∃ f : VV K lam, f ≠ 0 ∧ nrmSq s sg G' (brAt hN lam sg t f) = brSq hN lam sg T * nrmSq s lam G f

def BrNorm : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (s : K →+* ℂ), (∀ x, s (star x) = star (s x)) →
  ∀ (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n),
    (∀ τ, Interlace hN (lam τ) (sg τ)) → (∀ τ, SameShift (lam τ) (sg τ)) →
  ∀ (G' : ι → Matrix (Fin n) (Fin n) K), (∀ τ, ((G' τ).map s).PosDef) →
  ∀ (g t : ι → K) (T : ℝ), 0 < T → (∀ τ, ((‖s (t τ)‖ ^ 2 : ℝ) : ℂ) * s (g τ) = (T : ℂ)) →
    NormConcl s hN lam sg (fun τ => sumGram N (G' τ) (g τ)) G' t T

theorem brSq_eq {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) {T : ℝ}
    (hT : 0 < T) : brSq hN lam sg T = T ^ (-∑ τ, nBr (lam τ) (sg τ)) * orthSq hN lam sg := by
  unfold brSq orthSq
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.sum_neg_distrib]
  induction (Finset.univ : Finset ι) using Finset.cons_induction with
  | empty => simp
  | cons a S ha ih => rw [Finset.prod_cons, Finset.sum_cons, zpow_add₀ hT.ne', ih]

def wtOneZero : DomWeight 2 := ⟨![1, 0], by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all⟩

def wtZero : DomWeight 1 := ⟨fun _ => 0, fun _ _ _ => le_rfl⟩

end GlobalTheory.IndefiniteRowSideFullHecke.ScaledCoisometryNorms
end
end

section

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors

open Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV

def normSqAt {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) (h : S.Ok) (s : K →+* ℂ) (φ : S.D → S.V) : ℝ :=
  (S.ipAt h (InfinitePlace.mk s) φ φ).re

section Comparison₂

variable {X : Fields} {Word : Type} (Nd : NumDatum) (W : Wts X Word Nd.R)

end Comparison₂

section Ev

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ)

theorem mem_of_mem_divs {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} {P : HeightOneSpectrum A} (h : P ∈ divs a) :
    a ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with hf
  · simpa using h
  · simp at h

theorem evOk (hX : X.Ok) (hPr : Pr.Ok) (P : LevFam X.E X.K R.r Pr.vGs) (u : Pr.Word) :
    (evGSD W Ch sel (mu0 X.F X.E X.K Sg) P u).Ok := by
  have hM := mtildeOk W Ch sel (mu0 X.F X.E X.K Sg) hX P
  have hC := colVal_eqv W hX u R.m (Pr.vT u) (rowSG Pr sel (mu0 X.F X.E X.K Sg))
  have hT : ∀ Q : Pr.vT u, cO X.E (Pr.piT u) ∉ Q.1.asIdeal := by
    intro Q hQ
    have h1 : Pr.piT u ∈ Q.1.asIdeal := mem_of_mem_divs Q.2
    have h2 : X.conjO (Pr.piT u) ∈ Q.1.asIdeal := hQ
    obtain ⟨a, b, hab⟩ := hPr.piT_cop u
    exact Q.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)))
  have hG : ∀ w : rowSG Pr sel (mu0 X.F X.E X.K Sg), Pr.piT u ∉ w.1.asIdeal := by
    classical
    intro w hw
    have hw1 : w.1 ∈ Pr.vGs := by
      rcases Finset.mem_union.mp w.2 with h | h
      · exact h
      · rw [twistPrimes_trivialTuple_empty] at h
        simp at h
    have hg : ∃ i, ((Pr.g i : ℕ) : 𝓞 X.E) ∈ w.1.asIdeal := by
      rcases Finset.mem_union.mp hw1 with h | h
      · exact ⟨0, hPr.piG_norm 0 ▸ Ideal.mul_mem_left _ _ (mem_of_mem_divs h)⟩
      · exact ⟨1, hPr.piG_norm 1 ▸ Ideal.mul_mem_left _ _ (mem_of_mem_divs h)⟩
    have hgg : ((Pr.cond * (Pr.g 0 * Pr.g 1) ^ 2 : ℕ) : 𝓞 X.E) ∈ w.1.asIdeal := by
      push_cast
      refine Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ ?_ 2 two_pos)
      obtain ⟨i, hi⟩ := hg
      fin_cases i
      · exact Ideal.mul_mem_right _ _ hi
      · exact Ideal.mul_mem_left _ _ hi
    obtain ⟨c, hc⟩ := hPr.piT_cong u
    have h1 : Pr.piT u - 1 ∈ w.1.asIdeal := hc ▸ Ideal.mul_mem_right _ _ hgg
    exact w.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem hw h1))
  have hroot : ∀ g : FormG (rowTy Ch sel (mu0 X.F X.E X.K Sg) P).inv, ∃ m : ℕ, 0 < m ∧
      ((((rowTy Ch sel (mu0 X.F X.E X.K Sg) P).inv.chr g.2)⁻¹ : X.Kˣ) : X.K) ^ m = 1 := by
    intro g
    obtain ⟨m, hm, hc⟩ := (rowTy Ch sel (mu0 X.F X.E X.K Sg) P).inv.chr_root g.2
    exact ⟨m, hm, by rw [Units.val_inv_eq_inv_val, inv_pow, hc, inv_one]⟩
  refine ⟨hM.fin_orb, hM.fin_stab, ?_, ?_, ?_⟩
  · intro g d
    obtain ⟨m, hm, hc⟩ := hroot g
    have h1 := DecoSet.tilH_smul (N_m_succ R) (ST := Pr.vT u) (FormG.incl _ g) d hT hG
    exact (congrArg _ h1).trans ((hC.nab_smul _ _).trans (map_root_smul _ _ hm hc).symm)
  · intro g d
    obtain ⟨m, hm, hc⟩ := hroot g
    have h1 := DecoSet.tilH_smul (N_m_succ R) (ST := Pr.vT u) (FormG.incl _ g) d hT hG
    exact (congrArg _ h1).trans ((hC.del_smul _ _).trans (map_root_smul _ _ hm hc).symm)
  · intro g x y
    obtain ⟨m, hm, hc⟩ := hroot g
    show (colVal W u R.m (Pr.vT u) (rowSG Pr sel (mu0 X.F X.E X.K Sg))).pair
      (((((rowTy Ch sel (mu0 X.F X.E X.K Sg) P).inv.chr g.2)⁻¹ : X.Kˣ) : X.K) • _)
      (((((rowTy Ch sel (mu0 X.F X.E X.K Sg) P).inv.chr g.2)⁻¹ : X.Kˣ) : X.K) • _) =
      (colVal W u R.m (Pr.vT u) (rowSG Pr sel (mu0 X.F X.E X.K Sg))).pair x y
    rw [LinearMap.map_smulₛₗ₂, map_smul, hC.inv, smul_smul]
    show (star _ * _) • _ = _
    rw [star_mul_root hX.conjK hm hc, one_smul]

end Ev

theorem card_eq_f (Nd : NumDatum) (X : Fields) (pl : X.Tau ≃ RPl Nd.R) : X.f = Nd.R.f := by
  unfold Fields.f Ranks.f Ranks.n
  rw [Fintype.card_congr pl, Fintype.card_prod, Fintype.card_bool, Formalism.HC.Frame.card_A]

end GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors

end
end
