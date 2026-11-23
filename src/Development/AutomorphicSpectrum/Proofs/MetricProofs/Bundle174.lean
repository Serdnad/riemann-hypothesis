module

import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticDenseGoodPoints
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle103
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle097
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle145
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle123
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle173
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle146
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle166
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionFourth
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionSixth
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartNinth
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle101

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Holo

section Gen

variable {e N : ℕ} {s : Set (Fin e → ℂ)}

theorem analytic_minorIJ (g : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (hg : ∀ a b, AnalyticOnNhd ℂ (fun w => g w a b) s) (I J : Finset (Fin N)) :
    AnalyticOnNhd ℂ (fun w => minorIJ (g w) I J) s := by
  apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.DensR.analytic_minorIJ <;> assumption

theorem analytic_mul_entry (g g' : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (hg : ∀ a b, AnalyticOnNhd ℂ (fun w => g w a b) s)
    (hg' : ∀ a b, AnalyticOnNhd ℂ (fun w => g' w a b) s) (a b : Fin N) :
    AnalyticOnNhd ℂ (fun w => (g w * g' w) a b) s := by
  simp only [Matrix.mul_apply]
  have H := Finset.analyticOnNhd_sum (𝕜 := ℂ) (s := s) (Finset.univ : Finset (Fin N))
    (f := fun c w => g w a c * g' w c b) (fun c _ => (hg a c).mul (hg' c b))
  convert H using 1
  funext w
  rw [Finset.sum_apply]

theorem analytic_coord (i : Fin e) : AnalyticOnNhd ℂ (fun w : Fin e → ℂ => w i) s := by
  exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) i).analyticOnNhd s

end Gen

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {n e : ℕ}

theorem analytic_lowMat (s : Set (Fin e → ℂ)) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e) (τ' : Ψ) (a b : Fin N) :
    AnalyticOnNhd ℂ (fun w => lowMat (wL ε w) τ' a b) s := by
  by_cases hc : b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)
  · have hfun : (fun w => lowMat (wL ε w) τ' a b) = fun w => w (ε (Sum.inr (Sum.inl ⟨(τ', a, b), hc⟩))) := by
      funext w
      simp only [lowMat]
      rw [dite_eq_left hc]
      rfl
    rw [hfun]
    exact analytic_coord _
  · have hfun : (fun w => lowMat (wL ε w) τ' a b) = fun _ => if a = b then (1 : ℂ) else 0 := by
      funext w
      simp only [lowMat]
      rw [dite_eq_right hc]
    rw [hfun]
    exact analyticOnNhd_const

theorem analytic_wH (s : Set (Fin e → ℂ)) (h : Ψ → Matrix (Fin N) (Fin N) ℂ)
    (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e) (τ' : Ψ) (a b : Fin N) :
    AnalyticOnNhd ℂ (fun w => wH h ε τ' w a b) s := by
  exact analytic_mul_entry (s := s) (fun _ => h τ') (fun w => lowMat (wL ε w) τ') (fun _ _ => analyticOnNhd_const)
    (fun a b => analytic_lowMat s ε τ' a b) a b

theorem analytic_wH_snd (s : Set (Fin e → ℂ)) (h : Ψ → Matrix (Fin N) (Fin N) ℂ)
    (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e) (τ : Ψ) (ca cb : Fin N) (a b : Fin N) :
    AnalyticOnNhd ℂ (fun w => (wH h ε τ w * (1 + Matrix.single cb ca (wT ε w))) a b) s := by
  refine analytic_mul_entry (s := s) (fun w => wH h ε τ w) (fun w => 1 + Matrix.single cb ca (wT ε w))
    (fun a b => analytic_wH s h ε τ a b) (fun a' b' => ?_) a b
  beta_reduce
  by_cases hc : cb = a' ∧ ca = b'
  · have hfun : (fun w => (1 + Matrix.single cb ca (wT ε w)) a' b') =
        fun w => (1 : Matrix (Fin N) (Fin N) ℂ) a' b' + w (ε (Sum.inr (Sum.inr ()))) := by
      funext w
      rw [Matrix.add_apply, Matrix.single_apply, if_pos hc]
      rfl
    rw [hfun]
    exact analyticOnNhd_const.add (analytic_coord _)
  · have hfun : (fun w => (1 + Matrix.single cb ca (wT ε w)) a' b') =
        fun _ => (1 : Matrix (Fin N) (Fin N) ℂ) a' b' + 0 := by
      funext w
      rw [Matrix.add_apply, Matrix.single_apply, if_neg hc]
    rw [hfun]
    exact analyticOnNhd_const

theorem analytic_flagZ (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {s : Set (Fin e → ℂ)}
    (zb : (Fin e → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (H : (Fin e → ℂ) → Ψ → Matrix (Fin N) (Fin N) ℂ)
    (hzb : ∀ q, AnalyticOnNhd ℂ (fun w => zb w q) s)
    (hval : ∀ q I, AnalyticOnNhd ℂ (fun w => valAt M.x (F.u q I) (zb w)) s)
    (hH : ∀ τ' a b, AnalyticOnNhd ℂ (fun w => H w τ' a b) s) (q : Σ k, ι k) :
    AnalyticOnNhd ℂ (fun w => flagZ M F (zb w) (H w) q) s := by
  by_cases e' : ∃ p, M.blk p = some q.1
  · have hfun : (fun w => flagZ M F (zb w) (H w) q) = fun w =>
        ∑ I, valAt M.x (F.u q I) (zb w) * minorIJ (H w e'.choose.1) I (stepCols N j e'.choose.2) := by
      funext w
      simp only [flagZ]
      rw [dite_eq_left e']
    rw [hfun]
    have S := Finset.analyticOnNhd_sum (𝕜 := ℂ) (s := s) Finset.univ
      (f := fun I w => valAt M.x (F.u q I) (zb w) * minorIJ (H w e'.choose.1) I (stepCols N j e'.choose.2))
      (fun I _ => (hval q I).mul (analytic_minorIJ (fun w => H w e'.choose.1) (fun a b => hH _ a b) I _))
    convert S using 1
    funext w
    rw [Finset.sum_apply]
  · have hfun : (fun w => flagZ M F (zb w) (H w) q) = fun w => zb w ⟨⟨q.1, fun p hp => e' ⟨p, hp⟩⟩, q.2⟩ := by
      funext w
      simp only [flagZ]
      rw [dite_eq_right e']
    rw [hfun]
    exact hzb _

theorem analytic_wB {Λ : Type} (ε : Fin n ⊕ Λ ⊕ Unit ≃ Fin e) (V : Set (Fin n → ℂ)) :
    AnalyticOnNhd ℂ (wB ε) (wD ε V) := by
  exact AnalyticOnNhd.pi (fun i => analytic_coord (s := wD ε V) (ε (Sum.inl i)))

end Flag

theorem wPhi_holo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ p, AnalyticOnNhd ℂ (fun w => wPhi M F bl h ε k₀ τ ca cb w p) (wD ε V) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hctx p
  obtain ⟨-, -, -, -, -, -, -, ⟨-, -, hbl, hvl, -⟩, -, -, -⟩ := hctx
  have hB : AnalyticOnNhd ℂ (wB ε) (wD ε V) := analytic_wB ε V
  have hmaps : Set.MapsTo (wB ε) (wD ε V) V := fun w hw => hw
  have hzb : ∀ q, AnalyticOnNhd ℂ (fun w => bl (wB ε w) q) (wD ε V) := fun q => (hbl q).comp hB hmaps
  have hval : ∀ q I, AnalyticOnNhd ℂ (fun w => valAt M.x (F.u q I) (bl (wB ε w))) (wD ε V) :=
    fun q I => (hvl q I).comp hB hmaps
  obtain ⟨o, m⟩ := p
  cases o with
  | some k =>
    exact analytic_flagZ M F (fun w => bl (wB ε w)) (fun w τ' => wH h ε τ' w) hzb hval
      (fun τ' a' b' => analytic_wH _ h ε τ' a' b') ⟨k, m⟩
  | none =>
    refine analytic_flagZ M F (fun w => bl (wB ε w))
      (fun w => Function.update (fun τ' => wH h ε τ' w) τ (wH h ε τ w * (1 + Matrix.single cb ca (wT ε w))))
      hzb hval ?_ ⟨k₀, m⟩
    intro τ' a' b'
    by_cases hτ : τ' = τ
    · have hfun : (fun w => Function.update (fun τ'' => wH h ε τ'' w) τ
          (wH h ε τ w * (1 + Matrix.single cb ca (wT ε w))) τ' a' b') =
          fun w => (wH h ε τ w * (1 + Matrix.single cb ca (wT ε w))) a' b' := by
        funext w
        rw [Function.update_apply, if_pos hτ]
      rw [hfun]
      exact analytic_wH_snd _ h ε τ ca cb a' b'
    · have hfun : (fun w => Function.update (fun τ'' => wH h ε τ'' w) τ
          (wH h ε τ w * (1 + Matrix.single cb ca (wT ε w))) τ' a' b') = fun w => wH h ε τ' w a' b' := by
        funext w
        rw [Function.update_apply, if_neg hτ]
      rw [hfun]
      exact analytic_wH _ h ε τ' a' b'

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Holo
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem _root_.GlobalTheory.T.chernPart_sheet_image_eq : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ), IsProjOver p → ∀ (σ : k →+* ℂ) (D : ℕ) (B : LB X) (φ : ∀ σ : k →+* ℂ, Weight p σ B) (ψ : Weight t τ B), WOver φ ψ → (∀ σ, (φ σ).IsCInf) → ψ.IsCInf → ∀ (ε : ℤˣ) (S : Set (CxPts p σ)), MeasurableSet S → ψ.chernPart D ε (sheet t τ '' S) = (φ σ).chernPart D ε S := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BaseZ.chernPart_sheet | exact GlobalTheory.CompanionTheory.Ar.BaseZ.chernPart_sheet | (intros; apply GlobalTheory.CompanionTheory.Ar.BaseZ.chernPart_sheet <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem _root_.GlobalTheory.T.wZ_isCInf' : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (L : HermLB p) (τ : ℤ →+* ℂ), (wZ L t τ).IsCInf := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BaseZ.wZ_isCInf | exact GlobalTheory.CompanionTheory.Ar.BaseZ.wZ_isCInf | (intros; apply GlobalTheory.CompanionTheory.Ar.BaseZ.wZ_isCInf <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem _root_.GlobalTheory.T.flag_adjacent_twisted_resolution_third : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)), Nonempty RW.X := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FibNonempty.anLogRes_W_nonempty | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FibNonempty.anLogRes_W_nonempty | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FibNonempty.anLogRes_W_nonempty <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

theorem GlobalTheory.CompanionTheory.Ar.PB.WSq.fibre_potentials : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → ∀ (L' : LocPot RW.X) (v : RW.X → RW.X → ℂ) (cst : ℝ), IsNormFn M τ a k₀ ca cb RW (fun x => logNormSec L' v x + cst) → ∀ (U : ℕ → Set (Fin d → ℂ)) (G : ℕ → (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦY : ℕ → (Fin (d + 1) → ℂ) → FA.S.X) (ΦW : ℕ → (Fin (d + 2) → ℂ) → RW.X), (∀ m, IsOpen (U m)) → (∀ m, IsFibreChart FA τ a ca cb q (U m) (G m) (ΦY m) (ΦW m)) → ∃ α : ℕ → Ψ × Fin N → (Fin d → ℂ) → ℝ, (∀ m, ∀ w ∈ U m, (G m w).PosDef) ∧ (∀ m r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => G m w r s) (U m)) ∧ (∀ m p, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (α m p) (U m)) ∧ (∀ m (z : Fin (d + 1) → ℂ), Fin.tail z ∈ U m → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).potH p).φ (ΦY m z) (ΦY m z') = xiPot (G m (Fin.tail z')) (z' 0) + (Hh z').re) ∧ (∀ m p, p ≠ (τ, a) → ∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ U m → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ((FA.S.comap some).potH p).φ (ΦY m z) (ΦY m z') = α m p (Fin.tail z') + (Hh z').re) ∧ ∀ m (z : Fin (d + 2) → ℂ), Fin.tail (Fin.tail z) ∈ U m → z 0 ≠ z 1 → logNormSec L' v (ΦW m z) + cst + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).ph p (q 0 (ΦW m z)) + (FA.S.comap some).ph p (q 1 (ΦW m z))) = logSin (G m (Fin.tail (Fin.tail z))) (z 0) (z 1) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hb hcase hblk hca hcb RW q hq h0 h1 L' v cst hnorm U G ΦY ΦW hU hC
  have hC' := fun m => (isFibreChart_iff FA τ a ca cb q (U m) (G m) (ΦY m) (ΦW m)).1 (hC m)
  choose l H bp hD using hC'
  refine ⟨fun m => alphaOf BM (l m) (H m) (bp m), fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_⟩
  · exact GlobalTheory.T.two_point_fibre_chart_second K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb _ q (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
  · exact GlobalTheory.T.two_point_fibre_chart_third K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb _ q (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
  · exact GlobalTheory.T.two_point_fibre_chart_fourth K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb _ q (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
  · exact GlobalTheory.T.two_point_fibre_chart_sixth K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb _ q (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
  · exact GlobalTheory.T.two_point_fibre_chart_seventh K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb _ q (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
  · exact GlobalTheory.T.two_point_fibre_twisted_resolution K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb k₀ hblk RW q h0 h1 _ hnorm (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem _root_.GlobalTheory.T.flag_adjacent_twisted_resolution_fourth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → (Function.Injective fun w => (q 0 w, q 1 w)) → ∀ (l : Fin BM.q) (x : RW.X), FA.pr (q 0 x) ∈ BM.O l → (∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (fstPt k₀ (RW.lift x x)) p ≠ 0) → (∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (sndPt k₀ (RW.lift x x)) p ≠ 0) → ∃ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a₀ a₁ : ℂ), SameOrbit (RW.lift x x) (FC.wVec M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (FC.Lca τ ca cb c a₀) τ a k₀ ca cb (a₁ - a₀)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Cell.vector_of_chart | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Cell.vector_of_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Cell.vector_of_chart <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem _root_.GlobalTheory.T.flag_adjacent_twisted_resolution_sixth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → (Function.Injective fun w => (q 0 w, q 1 w)) → ∀ (l : Fin BM.q) (x : RW.X), FA.pr (q 0 x) ∈ BM.O l → ∀ V, IsOpen V → x ∈ V → ∃ x' ∈ V, FA.pr (q 0 x') ∈ BM.O l \ bdry BM.s ∧ ∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x'))) (fstPt k₀ (RW.lift x' x')) p ≠ 0 ∧ FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x'))) (sndPt k₀ (RW.lift x' x')) p ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.dens_w | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.dens_w | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.dens_w <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem _root_.GlobalTheory.T.flag_analytic_plucker_column_swap : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (ca cb : Fin N), ca < cb → ((cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) → ∀ (l : Fin BM.q) (x₀ : FA.Re.R.X), FA.pr (FA.Re.π x₀) ∈ BM.O l → (∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (FA.Re.π x₀))) (FA.Re.R.lift x₀ x₀) p ≠ 0) → ∃ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ), SameOrbit (FA.Re.R.lift x₀ x₀) (FC.flagPt M (BM.F l) (FC.bvec BM l (FA.pr (FA.Re.π x₀))) (FC.Lca τ ca cb c a)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_Lca_of_plk_ne | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_Lca_of_plk_ne | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_Lca_of_plk_ne <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

theorem _root_.GlobalTheory.T.flag_adjacent_chart_ninth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ w ∈ wD ε V, ∀ p : (o : Option K) → ι (o.getD k₀), (∀ o, wPhi M F bl h ε k₀ τ ca cb w ⟨o, p o⟩ ≠ 0) → (fderiv ℂ (fun w' => affCoord p (wPhi M F bl h ε k₀ τ ca cb w')) w).ker = ⊥ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.Imm.chart_immersion | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.Imm.chart_immersion | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.Imm.chart_immersion <;> assumption)
end
