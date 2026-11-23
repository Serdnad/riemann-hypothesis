module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle150
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.LocallyUniformLimit
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.Chebotarev.Bundle001

@[expose] public section

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwo

theorem wirt_const_fun {Φ : Type} [Fintype Φ] (τ : Φ) (bar : Bool) (d : ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.wirt τ bar (fun _ : Φ → ℂ => d) = fun _ => 0 := by
  funext z
  simp [GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.wirt]

theorem wirtWord_const_fun {Φ : Type} [Fintype Φ] (ws : List (Φ × Bool)) (d : ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.wirtWord ws (fun _ : Φ → ℂ => d) = fun _ => if ws = [] then d else 0 := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.wirtWord_cons, ih]
    simp only [reduceCtorEq, if_false]
    exact wirt_const_fun w.1 w.2 _

theorem isGood_const (F : Type) [Field F] [NumberField F] (a : ℂ → ℂ)
    (ha : DifferentiableOn ℂ a GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane) :
    GlobalTheory.HeckeTwo.IsGood (fun σ (_ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) => a σ) := by
  refine ⟨fun σ _ => contDiffOn_const, fun w z _ => ?_⟩
  simp only [wirtWord_const_fun]
  split_ifs
  · exact ha
  · exact differentiableOn_const 0

theorem goodConst : ∀ (F : Type) [Field F] [NumberField F] (a : ℂ → ℂ), DifferentiableOn ℂ a GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane → GlobalTheory.HeckeTwo.IsGood (fun σ (_ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) => a σ) :=
  fun F _ _ a ha => isGood_const F a ha

end GlobalTheory.HeckeTwo
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo

open MeasureTheory

def hTransAB (a b : ℕ) (σ : ℂ) (ν y : ℝ) : ℂ :=
  ∫ t : ℝ, ((t : ℂ) + (y : ℂ) * I)⁻¹ ^ a * ((starRingEnd ℂ) ((t : ℂ) + (y : ℂ) * I))⁻¹ ^ b *
    ((‖(t : ℂ) + (y : ℂ) * I‖ : ℝ) : ℂ) ^ (-2 * σ) * Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))

theorem hTransAB_two_zero (σ : ℂ) (ν y : ℝ) : hTransAB 2 0 σ ν y = hTrans σ ν y := by
  unfold hTransAB hTrans phi
  congr 1; funext t
  simp only [pow_zero, mul_one]

variable {F : Type} [Field F] [NumberField F]

def termQ (σ : ℂ) (b ν : F) (q : Emb F → ℕ) (z : Emb F → ℂ) : ℂ :=
  ∏ τ : Emb F, (Complex.exp (2 * (Real.pi : ℂ) * I * ((τ ν * τ b * (z τ).re : ℝ) : ℂ)) *
    iteratedDeriv (q τ) (hTrans σ (τ ν)) (τ b * (z τ).im))

theorem termQ_zero (σ : ℂ) (b ν : F) (z : Emb F → ℂ) : termQ σ b ν 0 z = fTerm σ z b ν := by
  unfold termQ fTerm
  simp only [Pi.zero_apply, iteratedDeriv_zero]

end GlobalTheory.HeckeTwo
end
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwo.GoodAdd

variable {Φ : Type} [Fintype Φ]

open Classical in
theorem wirt_contDiffOn {U : Set (Φ → ℂ)} (hU : IsOpen U) {f : (Φ → ℂ) → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) (τ : Φ) (b : Bool) : ContDiffOn ℝ ∞ (wirt τ b f) U := by
  have hd : ContDiffOn ℝ ∞ (fun y => fderiv ℝ f y) U :=
    hf.fderiv_of_isOpen hU (by simp)
  have h1 : ContDiffOn ℝ ∞ (fun y => fderiv ℝ f y (Pi.single τ 1)) U :=
    hd.clm_apply contDiffOn_const
  have h2 : ContDiffOn ℝ ∞ (fun y => fderiv ℝ f y (Pi.single τ I)) U :=
    hd.clm_apply contDiffOn_const
  unfold wirt
  exact (h1.add (contDiffOn_const.mul h2)).div_const _

theorem wirtWord_contDiffOn {U : Set (Φ → ℂ)} (hU : IsOpen U) (w : List (Φ × Bool)) {f : (Φ → ℂ) → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) : ContDiffOn ℝ ∞ (wirtWord w f) U := by
  induction w with
  | nil => simpa [wirtWord_nil] using hf
  | cons a w ih => rw [wirtWord_cons]; exact wirt_contDiffOn hU ih _ _

theorem wirt_congr {U : Set (Φ → ℂ)} (hU : IsOpen U) {f g : (Φ → ℂ) → ℂ} (h : Set.EqOn f g U)
    (τ : Φ) (b : Bool) : Set.EqOn (wirt τ b f) (wirt τ b g) U := by
  intro z hz
  have he : f =ᶠ[nhds z] g := Filter.eventuallyEq_of_mem (hU.mem_nhds hz) h
  simp only [wirt, he.fderiv_eq]

theorem wirt_add {f g : (Φ → ℂ) → ℂ} {z : Φ → ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) (τ : Φ) (b : Bool) :
    wirt τ b (f + g) z = wirt τ b f z + wirt τ b g z := by
  have h : fderiv ℝ (f + g) z = fderiv ℝ f z + fderiv ℝ g z := fderiv_add hf hg
  simp only [wirt, h, ContinuousLinearMap.add_apply]
  ring

theorem wirtWord_add {U : Set (Φ → ℂ)} (hU : IsOpen U) (w : List (Φ × Bool)) {f g : (Φ → ℂ) → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) :
    Set.EqOn (wirtWord w (f + g)) (wirtWord w f + wirtWord w g) U := by
  induction w with
  | nil => intro z _; rfl
  | cons a w ih =>
    intro z hz
    rw [wirtWord_cons, wirtWord_cons, wirtWord_cons, wirt_congr hU ih _ _ hz]
    have hf' := wirtWord_contDiffOn hU w hf
    have hg' := wirtWord_contDiffOn hU w hg
    exact wirt_add ((hf'.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))
      ((hg'.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)) _ _

theorem upperHalf_isOpen (F : Type) [Field F] [NumberField F] : IsOpen (upperHalf F) := by
  have : upperHalf F = ⋂ τ : Emb F, {z : Emb F → ℂ | 0 < (z τ).im} := by
    ext z; simp [upperHalf]
  rw [this]
  exact isOpen_iInter_of_finite fun τ =>
    isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_apply τ))

end GlobalTheory.HeckeTwo.GoodAdd

theorem GlobalTheory.HeckeTwo.isGood_add : ∀ (F : Type) [Field F] [NumberField F] (P Q : ℂ → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) → ℂ), GlobalTheory.HeckeTwo.IsGood P → GlobalTheory.HeckeTwo.IsGood Q → GlobalTheory.HeckeTwo.IsGood (fun σ z => P σ z + Q σ z) := by
  intro F _ _ P Q hP hQ
  have hU := GlobalTheory.HeckeTwo.GoodAdd.upperHalf_isOpen F
  refine ⟨fun σ hσ => (hP.1 σ hσ).add (hQ.1 σ hσ), fun w z hz => ?_⟩
  refine ((hP.2 w z hz).add (hQ.2 w z hz)).congr fun σ hσ => ?_
  exact GlobalTheory.HeckeTwo.GoodAdd.wirtWord_add hU w (hP.1 σ hσ) (hQ.1 σ hσ) hz
end

section

open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge

namespace GlobalTheory

theorem lie_eigenSub_iff_flat : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ)) (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ) (F : Submodule w.valuationSubring (S → Fin N → C)) (τ : S), Function.Injective a → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration a F → Function.Injective (evalVec (liftA hv a) N) → (∀ y, y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N ↔ ∃ x, evalVec (liftA hv a) N x = y) → (∀ x, x ∈ (Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F}) ↔ evalVec (liftA hv a) N x ∈ F) → (∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N, (∀ s, x s ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s) → x ∈ F) → ∀ z : (Fin N → C) ⧸ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F τ, z ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N) F) τ ↔ ∃ x : Fin N → RS (liftA hv a), proj (liftA hv a) ((Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F})) x ∈ GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.eigSub (liftA hv a) τ ((Fin N → RS (liftA hv a)) ⧸ (Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F})) ∧ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.quotMap (w := w) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F τ) (fun i => ((GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.comp (liftA hv a) N τ x i : Int0 v) : C)) = z := by
  intro C _ w v hv S _ _ a N F τ hinj _hfilt _hevinj hrange hmem hlast z
  have hev : ∀ x : Fin N → RS (liftA hv a), ∀ s i,
      evalVec (liftA hv a) N (lin (liftA hv a) τ • x) s i
        = ((a s : C) - a τ) * evalVec (liftA hv a) N x s i := by
    intro x s i
    simp only [evalVec, Pi.smul_apply, smul_eq_mul, map_mul, ev_lin]
    rfl
  have hevs : ∀ x : Fin N → RS (liftA hv a), ∀ s,
      evalVec (liftA hv a) N (lin (liftA hv a) τ • x) s
        = ((a s : C) - a τ) • evalVec (liftA hv a) N x s := by
    intro x s; funext i; rw [hev]; rfl
  have heig : ∀ x : Fin N → RS (liftA hv a),
      proj (liftA hv a) ((Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F})) x ∈
          GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.eigSub (liftA hv a) τ ((Fin N → RS (liftA hv a)) ⧸ (Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F})) ↔
        evalVec (liftA hv a) N (lin (liftA hv a) τ • x) ∈ F := by
    intro x
    rw [← hmem]
    show lin (liftA hv a) τ • ((Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F})).mkQ x = 0 ↔ _
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hlie : z ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub
        (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N) F) τ ↔
      ∃ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N, ∀ s,
        (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s).mkQ (h s) =
          (Pi.single τ z : ∀ s, (Fin N → C) ⧸ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s) s := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub, GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie, Submodule.mem_comap,
      Submodule.mem_map]
    constructor
    · rintro ⟨h, hh, he⟩
      exact ⟨h, hh, fun s => congrFun he s⟩
    · rintro ⟨h, hh, he⟩
      exact ⟨h, hh, funext he⟩
  rw [hlie]
  constructor
  · rintro ⟨h, hh, he⟩
    obtain ⟨x, rfl⟩ := (hrange h).1 hh
    refine ⟨x, (heig x).2 ?_, ?_⟩
    · apply hlast _ ((hrange _).2 ⟨_, rfl⟩)
      intro s
      rw [hevs]
      by_cases hs : s = τ
      · rw [hs, sub_self, zero_smul]; exact zero_mem _
      · have h1 : evalVec (liftA hv a) N x s ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s := by
          have := he s
          rw [Pi.single_eq_of_ne hs, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
          exact this
        exact Submodule.smul_mem _ _ h1
    · have := he τ
      rw [Pi.single_eq_same] at this
      exact this
  · rintro ⟨x, hx, rfl⟩
    refine ⟨evalVec (liftA hv a) N x, (hrange _).2 ⟨x, rfl⟩, fun s => ?_⟩
    by_cases hs : s = τ
    · subst hs
      rw [Pi.single_eq_same]
      rfl
    · rw [Pi.single_eq_of_ne hs, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      have hy := (heig x).1 hx
      have hys : evalVec (liftA hv a) N (lin (liftA hv a) τ • x) s ∈
          GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s :=
        Submodule.subset_span ⟨_, hy, rfl⟩
      have hne : (a s : C) - a τ ≠ 0 := sub_ne_zero.2 fun e => hs (hinj (Subtype.ext e))
      have : evalVec (liftA hv a) N x s =
          ((a s : C) - a τ)⁻¹ • evalVec (liftA hv a) N (lin (liftA hv a) τ • x) s := by
        rw [hevs, smul_smul, inv_mul_cancel₀ hne, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ hys

end GlobalTheory
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwoMul

theorem wirt_const_mul {Φ : Type} [Fintype Φ] (τ : Φ) (bar : Bool) (c : ℂ) (g : (Φ → ℂ) → ℂ) :
    wirt τ bar (fun z => c * g z) = fun z => c * wirt τ bar g z := by
  funext z
  have h : fderiv ℝ (fun z => c * g z) z = c • fderiv ℝ g z := by
    have := congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := g) c) z
    simpa [Pi.smul_def, smul_eq_mul] using this
  simp only [wirt, h, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem wirtWord_const_mul {Φ : Type} [Fintype Φ] (ws : List (Φ × Bool)) (c : ℂ) (g : (Φ → ℂ) → ℂ) :
    wirtWord ws (fun z => c * g z) = fun z => c * wirtWord ws g z := by
  induction ws with
  | nil => rfl
  | cons w ws ih => rw [wirtWord_cons, wirtWord_cons, ih, wirt_const_mul]

theorem isGood_mul (F : Type) [Field F] [NumberField F] (k : ℂ → ℂ)
    (P : ℂ → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) → ℂ) (hk : DifferentiableOn ℂ k GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane)
    (hP : GlobalTheory.HeckeTwo.IsGood P) : GlobalTheory.HeckeTwo.IsGood (fun σ z => k σ * P σ z) := by
  obtain ⟨h1, h2⟩ := hP
  refine ⟨fun σ hσ => contDiffOn_const.mul (h1 σ hσ), fun w z hz => ?_⟩
  simp only [wirtWord_const_mul]
  exact hk.mul (h2 w z hz)

end GlobalTheory.HeckeTwoMul
end

section

open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge

namespace GlobalTheory.EvalVecRange

def toW {C : Type} [Field C] {w : Valuation C ℝ≥0} {v : AddValuation C (WithTop ℝ)}
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) : Int0 v →+* w.valuationSubring where
  toFun x := ⟨x, (hv x).1 x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def toV {C : Type} [Field C] {w : Valuation C ℝ≥0} {v : AddValuation C (WithTop ℝ)}
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) : w.valuationSubring →+* Int0 v where
  toFun x := ⟨x, (hv x).2 x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem ev_mk {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {S : Type} [Fintype S]
    [DecidableEq S] (b : S → Int0 v) (s : S) (g : Polynomial (Int0 v)) :
    ev b s (AdjoinRoot.mk _ g) = g.eval (b s) := by
  unfold ev
  rw [AdjoinRoot.liftAlgHom_mk]
  rfl

theorem evalVec_range : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ))
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S]
    (a : S → w.valuationSubring) (N : ℕ) (y : S → Fin N → C),
    y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N ↔ ∃ x, evalVec (liftA hv a) N x = y := by
  intro C _ w v hv S _ _ a N y
  constructor
  · intro hy
    choose f hf using hy
    refine ⟨fun i => AdjoinRoot.mk _ ((f i).map (toV hv)), ?_⟩
    funext s i
    simp only [evalVec]
    rw [ev_mk, Polynomial.eval_map, hf i s]
    have : liftA hv a s = toV hv (a s) := rfl
    rw [this, Polynomial.eval₂_hom]
    rfl
  · rintro ⟨x, rfl⟩ i
    obtain ⟨g, hg⟩ := AdjoinRoot.mk_surjective (x i)
    refine ⟨g.map (toW hv), fun s => ?_⟩
    simp only [evalVec]
    rw [← hg, ev_mk, Polynomial.eval_map]
    have : a s = toW hv (liftA hv a s) := rfl
    rw [this, Polynomial.eval₂_hom]
    rfl

end GlobalTheory.EvalVecRange
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo.APart

variable {F : Type} [Field F] [NumberField F]

theorem exists_den (I : FractionalIdeal (𝓞 F)⁰ F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ b ∈ I, ∃ x : 𝓞 F, (x : F) = (d : F) * b := by
  obtain ⟨d, hd, h⟩ := I.isFractional
  refine ⟨d, nonZeroDivisors.ne_zero hd, fun b hb => ?_⟩
  obtain ⟨x, hx⟩ := h b hb
  exact ⟨x, by rw [← Algebra.smul_def] at *; simpa using hx⟩

theorem summable_norm_rpow (I : FractionalIdeal (𝓞 F)⁰ F) {s : ℝ} (hs : 1 < s) :
    Summable (fun c : Quotient (unitRel I) => |((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| ^ (-s)) := by
  obtain ⟨d, hd, hdI⟩ := exists_den I
  choose g hg using fun c : Quotient (unitRel I) => hdI c.out.1 c.out.2.1
  have hd' : (d : F) ≠ 0 := by exact_mod_cast hd
  have hinj : Function.Injective (fun c : Quotient (unitRel I) => Ideal.span ({g c} : Set (𝓞 F))) := by
    intro c c' h
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1 h
    have h2 := congrArg (fun x : 𝓞 F => (x : F)) hu
    push_cast at h2
    refine Quotient.out_equiv_out.1 ⟨u, ?_⟩
    apply mul_left_cancel₀ hd'
    linear_combination ((u : 𝓞 F) : F) * hg c - hg c' - h2
  have hS := (ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal F hs).comp_injective hinj
  have hNd : 0 < |((Algebra.norm ℚ (d : F) : ℚ) : ℝ)| := by
    simp [Algebra.norm_eq_zero_iff, hd']
  refine (hS.mul_left (|((Algebra.norm ℚ (d : F) : ℚ) : ℝ)| ^ s)).congr fun c => ?_
  have e1 : ((Algebra.norm ℤ (g c) : ℤ) : ℚ) = Algebra.norm ℚ (d : F) * Algebra.norm ℚ c.out.1 := by
    rw [Algebra.coe_norm_int, hg, map_mul]
  have e2 : ((Algebra.norm ℤ (g c) : ℤ) : ℝ) =
      ((Algebra.norm ℚ (d : F) : ℚ) : ℝ) * ((Algebra.norm ℚ c.out.1 : ℚ) : ℝ) := by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) e1
  have hN : ((Ideal.absNorm (Ideal.span ({g c} : Set (𝓞 F))) : ℕ) : ℝ) =
      |((Algebra.norm ℚ (d : F) : ℚ) : ℝ)| * |((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| := by
    rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs, e2, abs_mul]
  simp only [Function.comp_apply]
  rw [hN, Real.mul_rpow (abs_nonneg _) (abs_nonneg _), ← mul_assoc, ← Real.rpow_add hNd, add_neg_cancel,
    Real.rpow_zero, one_mul]

theorem inv_natPow_rpow_neg_half_even_eq_pow {x : ℝ} (hx : 0 < x) (t : ℝ) : x ^ (-(2 + 2 * t)) = x⁻¹ ^ 2 * x ^ (-2 * t) := by
  rw [show -(2 + 2 * t) = -(2 : ℝ) + -2 * t by ring, Real.rpow_add hx, Real.rpow_neg hx.le, Real.rpow_two, inv_pow]

theorem rpow_le_add {x : ℝ} (hx : 0 < x) {r t R : ℝ} (hr : r ≤ t) (hR : t ≤ R) :
    x ^ (-2 * t) ≤ x ^ (-2 * r) + x ^ (-2 * R) := by
  rcases le_total x 1 with h | h
  · have := Real.rpow_le_rpow_of_exponent_ge hx h (show -2 * R ≤ -2 * t by linarith)
    linarith [Real.rpow_nonneg hx.le (-2 * r)]
  · have := Real.rpow_le_rpow_of_exponent_le h (show -2 * t ≤ -2 * r by linarith)
    linarith [Real.rpow_nonneg hx.le (-2 * R)]

variable [IsTotallyReal F]

theorem prod_latPt_zero (a : F) :
    ∏ τ : Emb F, latPt 0 (a, 0) τ =
      (2 * (Real.pi : ℂ) * I) ^ Fintype.card (Emb F) * ((Algebra.norm ℚ a : ℚ) : ℂ) := by
  simp only [latPt, Pi.zero_apply, map_zero, ofReal_zero, zero_mul, add_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, prod_emb]

end GlobalTheory.HeckeTwo.APart


open GlobalTheory.HeckeTwo.APart in
theorem GlobalTheory.HeckeTwo.aPart_differentiableOn : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F), DifferentiableOn ℂ (GlobalTheory.HeckeTwo.aPart 𝔞) GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane := by
  intro F _ _ _ 𝔞
  set P : Quotient (unitRel (latM 𝔞)) → ℂ := fun c => ∏ τ : Emb F, latPt 0 ((c.out.1 : F), (0 : F)) τ with hP
  have hP0 : ∀ c, P c ≠ 0 := fun c => by
    simp only [hP, prod_latPt_zero]
    refine mul_ne_zero (pow_ne_zero _ ?_) ?_
    · have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact mul_ne_zero (mul_ne_zero two_ne_zero hπ) I_ne_zero
    · exact_mod_cast (Algebra.norm_ne_zero_iff).2 c.out.2.2
  set K : ℝ := ‖(2 * (Real.pi : ℂ) * I) ^ Fintype.card (Emb F)‖ with hK
  have hK0 : 0 < K := by
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact norm_pos_iff.2 (pow_ne_zero _ (mul_ne_zero (mul_ne_zero two_ne_zero hπ) I_ne_zero))
  have hnP : ∀ c, ‖P c‖ = K * |((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| := fun c => by
    simp only [hP, prod_latPt_zero, norm_mul, hK]
    congr 1
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  have hsum : ∀ t : ℝ, 1 < t → Summable fun c => ‖P c‖ ^ (-t) := fun t ht =>
    ((summable_norm_rpow (latM 𝔞) ht).mul_left (K ^ (-t))).congr fun c => by
      rw [hnP, Real.mul_rpow hK0.le (abs_nonneg _)]
  have hnorm : ∀ c σ, ‖eisTerm 2 σ 0 ((c.out.1 : F), (0 : F))‖ = ‖P c‖⁻¹ ^ 2 * ‖P c‖ ^ (-2 * σ.re) := fun c σ => by
    show ‖(P c)⁻¹ ^ 2 * ((‖P c‖ : ℝ) : ℂ) ^ (-2 * σ)‖ = _
    rw [norm_mul, norm_pow, norm_inv, norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.2 (hP0 c))]
    simp
  intro σ₀ hσ₀
  have hσ₀' : -1 / 2 < σ₀.re := hσ₀
  set r : ℝ := (σ₀.re - 1 / 2) / 2 with hr
  set R : ℝ := σ₀.re + 1 with hR
  set U : Set ℂ := {σ | r < σ.re} ∩ {σ | σ.re < R} with hUdef
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  have hmem : σ₀ ∈ U := ⟨by show r < σ₀.re; rw [hr]; linarith, by show σ₀.re < R; rw [hR]; linarith⟩
  have hd : DifferentiableOn ℂ (fun σ => ∑' c : Quotient (unitRel (latM 𝔞)), eisTerm 2 σ 0 ((c.out.1 : F), (0 : F))) U := by
    refine differentiableOn_tsum_of_summable_norm
      (u := fun c => ‖P c‖⁻¹ ^ 2 * (‖P c‖ ^ (-2 * r) + ‖P c‖ ^ (-2 * R))) ?_ ?_ hU ?_
    · refine ((hsum (2 + 2 * r) (by rw [hr]; linarith)).add (hsum (2 + 2 * R) (by rw [hR]; linarith))).congr
        fun c => ?_
      have hx := norm_pos_iff.2 (hP0 c)
      rw [inv_natPow_rpow_neg_half_even_eq_pow hx, inv_natPow_rpow_neg_half_even_eq_pow hx]
      ring
    · intro c σ _
      show DifferentiableWithinAt ℂ (fun σ => (P c)⁻¹ ^ 2 * ((‖P c‖ : ℝ) : ℂ) ^ (-2 * σ)) U σ
      refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.const_mul ?_ _)
      refine DifferentiableAt.const_cpow (differentiableAt_id.const_mul _) (Or.inl ?_)
      exact_mod_cast (norm_pos_iff.2 (hP0 c)).ne'
    · intro c σ hσ
      rw [hnorm]
      have hx := norm_pos_iff.2 (hP0 c)
      gcongr
      exact rpow_le_add hx hσ.1.le hσ.2.le
  exact (hd.differentiableAt (hU.mem_nhds hmem)).differentiableWithinAt
end
end
