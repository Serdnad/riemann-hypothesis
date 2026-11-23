module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle089
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle101
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle097
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle075
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJEqSubmatrix
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle012
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.VolumeModelCritChartEqZero
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices.InstFintypeFlIdx
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle103
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle088
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle102
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle002
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical


theorem _root_.GlobalTheory.T.flag_gap_holomorphic_pullback_first : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr), HasStepCharts M BM p κ v R pr → IsPotential R.A (potOf R (fsHerm ιk fun k => M.dy p (κ k))) → R.A.SmoothOn (bdry (fun x y => BM.s (pr x) (pr y)))ᶜ (stepPh M BM p v R pr) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CWeight.smoothOn_stepPh | exact GlobalTheory.CompanionTheory.Ar.PB.CWeight.smoothOn_stepPh | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CWeight.smoothOn_stepPh <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical


theorem _root_.GlobalTheory.T.log_block_metric_off_boundary : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (l : Fin BM.q) (x₀ : BM.Rb.X) (z : (Σ k, ι k) → ℂ), M.blk p = none → x₀ ∈ BM.O l \ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) → Real.log ((BM.hom p).h z) = blockPot j p.2 (BM.G l p.1 x₀) 1 + Real.log ‖baseMono M (BM.F l) p z * valAt M.x ((BM.F l).υ p)⁻¹ (basePart M.blk z)‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.BaseLine.main | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.BaseLine.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.BaseLine.main <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.PtBase

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem basePart_orbit {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem blocks_of_orbit {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (h' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  intro k
  obtain ⟨i, hi⟩ := h' k
  exact ⟨i, mul_ne_zero (hc k) hi⟩

theorem fstPt_blocks {k₀ : K} {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : ∀ o, ∃ i, z ⟨o, i⟩ ≠ 0) :
    ∀ k, ∃ i, fstPt k₀ z ⟨k, i⟩ ≠ 0 := fun k => h (some k)

theorem sndPt_blocks {k₀ : K} {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : ∀ o, ∃ i, z ⟨o, i⟩ ≠ 0) :
    ∀ k, ∃ i, sndPt k₀ z ⟨k, i⟩ ≠ 0 := by
  intro k
  by_cases e : k = k₀
  · subst e
    obtain ⟨i, hi⟩ := h none
    refine ⟨i, ?_⟩
    change z (v₁ k ⟨k, i⟩) ≠ 0
    rw [v₁_self]
    exact hi
  · obtain ⟨i, hi⟩ := h (some k)
    refine ⟨i, ?_⟩
    change z (v₁ k₀ ⟨k, i⟩) ≠ 0
    rw [v₁_ne (p := ⟨k, i⟩) e]
    exact hi

theorem basePart_snd_eq_fst {σ : Type} (blk : σ → Option K) {k₀ : K} (p : σ) (hp : blk p = some k₀)
    (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) :
    basePart blk (sndPt k₀ z) = basePart blk (fstPt k₀ z) := by
  funext q
  obtain ⟨⟨k, hk⟩, i⟩ := q
  have e : k ≠ k₀ := by
    rintro rfl
    exact hk p hp
  change z (v₁ k₀ ⟨k, i⟩) = z (v₀ k₀ ⟨k, i⟩)
  rw [v₁_ne (p := ⟨k, i⟩) e]
  rfl

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X), M.blk (τ, a) = some k₀ → IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ (x : RW.X) (z₀ z₁ : (Σ k, ι k) → ℂ), SameOrbit z₀ (fstPt k₀ (RW.lift x x)) → SameOrbit z₁ (sndPt k₀ (RW.lift x x)) → basePart M.blk z₀ ∈ mcPts (mCoordIdeal M.x) ∧ SameOrbit (basePart M.blk z₁) (basePart M.blk z₀) ∧ (∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0) ∧ ∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a k₀ ca cb RW pr hb hW x z₀ z₁ h₀ h₁
  have hL : ∀ o, ∃ i, RW.lift x x ⟨o, i⟩ ≠ 0 := (RW.mem x x (RW.mem_U x)).1
  have hbase : SameOrbit (basePart M.blk z₀) (Rb.lift (pr x) (pr x)) :=
    orbit_trans (basePart_orbit M.blk h₀) (orbit_symm (hW.2.1 x))
  refine ⟨?_, ?_, blocks_of_orbit h₀ (fstPt_blocks hL), blocks_of_orbit h₁ (sndPt_blocks hL)⟩
  · obtain ⟨c, hc, e⟩ := hbase
    rw [e]
    exact ((GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main _ _ _ M.x _ c hc).2 (Rb.mem (pr x) (pr x) (Rb.mem_U _))).1
  · have h₁' := basePart_orbit M.blk h₁
    rw [basePart_snd_eq_fst M.blk (τ, a) hb] at h₁'
    exact orbit_trans h₁' (orbit_symm (basePart_orbit M.blk h₀))

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.PtBase
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem mul_one_add_single_apply {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (ca cb : Fin N) (t : ℂ) (r c : Fin N) :
    (h * (1 + Matrix.single cb ca t)) r c = h r c + if c = ca then t * h r cb else 0 := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  simp only [Matrix.single_apply]
  split_ifs with hc
  · subst hc
    simp [mul_comm]
  · simp [Ne.symm hc]

theorem minorIJ_mul_transvection {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (I J : Finset (Fin N)) {ca cb : Fin N}
    (hne : ca ≠ cb) (t : ℂ) (hJ : ca ∈ J ↔ cb ∈ J) :
    minorIJ (h * (1 + Matrix.single cb ca t)) I J = minorIJ h I J := by
  unfold minorIJ
  split_ifs with e
  · by_cases hca : ca ∈ J
    · have hcb := hJ.1 hca
      obtain ⟨p, hp⟩ : ca ∈ Set.range (J.orderEmbOfFin (rfl : J.card = J.card)) := by
        rw [Finset.range_orderEmbOfFin]; exact hca
      obtain ⟨q, hq⟩ : cb ∈ Set.range (J.orderEmbOfFin (rfl : J.card = J.card)) := by
        rw [Finset.range_orderEmbOfFin]; exact hcb
      have hpq : p ≠ q := fun h' => hne (by rw [← hp, ← hq, h'])
      refine (congrArg Matrix.det ?_).trans
        (Matrix.det_updateCol_add_smul_self (h.submatrix (I.orderEmbOfFin e) (J.orderEmbOfFin rfl)) hpq t)
      ext a b
      rw [Matrix.submatrix_apply, mul_one_add_single_apply]
      by_cases hb : b = p
      · rw [hb, Matrix.updateCol_self]
        simp [hp, hq]
      · have hbc : J.orderEmbOfFin rfl b ≠ ca := fun h' =>
          hb ((J.orderEmbOfFin rfl).injective (h'.trans hp.symm))
        rw [Matrix.updateCol_ne hb]
        simp [hbc]
    · congr 1
      ext a b
      have hbc : J.orderEmbOfFin rfl b ≠ ca := fun h' => hca (h' ▸ Finset.orderEmbOfFin_mem J rfl b)
      simp [mul_one_add_single_apply, hbc]
  · rfl

theorem mem_stepCols_iff {N j : ℕ} {a b i ca cb : Fin N} (hb : (b : ℕ) = a + 1) (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) (hi : i ≠ a) :
    ca ∈ stepCols N j i ↔ cb ∈ stepCols N j i := by
  have hi' : (i : ℕ) ≠ a := fun h => hi (Fin.ext h)
  have := a.isLt
  have := b.isLt
  have := i.isLt
  have := ca.isLt
  have := cb.isLt
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold lastCol at hca
  split_ifs at hca ⊢ <;> omega

theorem fstPt_sndPt_wVec : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (t : ℂ), fstPt k₀ (FC.wVec M F b h τ a k₀ ca cb t) = FC.flagPt M F b h ∧ sndPt k₀ (FC.wVec M F b h τ a k₀ ca cb t) = FC.flagPt M F b (Function.update h τ (h τ * (1 + Matrix.single cb ca t))) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M τ a b k₀ ca cb hb hab hblk hca hcb F bv h t
  have hne : ca ≠ cb := by
    intro e
    have := congrArg Fin.val e
    omega
  refine ⟨?_, ?_⟩
  · funext p
    obtain ⟨k, m⟩ := p
    rfl
  · funext p
    obtain ⟨k, m⟩ := p
    simp only [sndPt, Function.comp_apply]
    by_cases hk : k = k₀
    · subst hk
      rw [v₁_self]
      show (∑ I, valAt M.x (F.u ⟨k, m⟩ I) bv * minorIJ (h τ * (1 + Matrix.single cb ca t)) I (stepCols N j a)) = _
      rw [flagPt_step M F bv _ hblk m]
      simp [Function.update_self]
    · rw [v₁_ne (p := ⟨k, m⟩) hk]
      show FC.flagPt M F bv h ⟨k, m⟩ = _
      by_cases hbase : ∀ p, M.blk p ≠ some k
      · simp [FC.flagPt, hbase]
      · push Not at hbase
        obtain ⟨⟨τ', i⟩, hp⟩ := hbase
        rw [flagPt_step M F bv h hp m, flagPt_step M F bv _ hp m]
        refine Finset.sum_congr rfl fun I _ => ?_
        dsimp only
        congr 1
        by_cases hτ : τ' = τ
        · subst hτ
          have hia : i ≠ a := by
            rintro rfl
            exact hk (Option.some_injective _ (hp.symm.trans hblk))
          rw [Function.update_self, minorIJ_mul_transvection _ _ _ hne t (mem_stepCols_iff hb hab hca hcb hia)]
        · rw [Function.update_of_ne hτ]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.Shear

variable {N : ℕ}

theorem shear_above {ca cb : Fin N} (hab : ca < cb) (t : ℂ) {x y : Fin N} (hxy : x < y) :
    (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) x y = 0 := by
  rw [SchurCalc.elem_apply, if_neg hxy.ne, if_neg, add_zero]
  rintro ⟨rfl, rfl⟩
  exact lt_asymm hab hxy

theorem shear_diag {ca cb : Fin N} (hab : ca < cb) (t : ℂ) (x : Fin N) :
    (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) x x = 1 := by
  rw [SchurCalc.elem_apply, if_pos rfl, if_neg, add_zero]
  rintro ⟨rfl, h⟩
  exact hab.ne h

theorem det_shear {ca cb : Fin N} (hab : ca < cb) (t : ℂ) :
    (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (fun x y h => shear_above hab t h)]
  exact Finset.prod_eq_one fun x _ => shear_diag hab t x

theorem minor_shear {ca cb : Fin N} (hab : ca < cb) (t : ℂ) (S : Finset (Fin N)) :
    minorIJ (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) S S = 1 := by
  have ht : ((1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).submatrix (S.orderEmbOfFin rfl)
      (S.orderEmbOfFin rfl)).BlockTriangular OrderDual.toDual :=
    fun x y h => shear_above hab t ((S.orderEmbOfFin rfl).strictMono h)
  rw [MinorCalc.minorIJ_eq_det _ S S _ rfl rfl, Matrix.det_of_lowerTriangular _ ht]
  exact Finset.prod_eq_one fun x _ => shear_diag hab t _

theorem support_shear {ca cb : Fin N} (t : ℂ) {S : Finset (Fin N)} (hS : ca ∈ S → cb ∈ S) (k c : Fin N)
    (hc : c ∈ S) (hk : k ∉ S) : (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) k c = 0 := by
  have hne : k ≠ c := fun e => hk (e ▸ hc)
  rw [SchurCalc.elem_apply, if_neg hne, if_neg, add_zero]
  rintro ⟨rfl, rfl⟩
  exact hk (hS hc)

theorem minor_mul_shear {ca cb : Fin N} (hab : ca < cb) (t : ℂ) {S : Finset (Fin N)} (hS : ca ∈ S → cb ∈ S)
    (A : Matrix (Fin N) (Fin N) ℂ) (I : Finset (Fin N)) :
    minorIJ (A * (1 + Matrix.single cb ca t)) I S = minorIJ A I S := by
  rw [MinorCalc.minorIJ_mul_of_support _ _ _ _ (support_shear t hS), minor_shear hab, mul_one]

theorem minor_gram_shear {ca cb : Fin N} (hab : ca < cb) (t : ℂ) {S : Finset (Fin N)} (hS : ca ∈ S → cb ∈ S)
    (G h : Matrix (Fin N) (Fin N) ℂ) :
    minorIJ ((h * (1 + Matrix.single cb ca t))ᴴ * G * (h * (1 + Matrix.single cb ca t))) S S =
      minorIJ (hᴴ * G * h) S S := by
  obtain ⟨H, hH⟩ : ∃ H, H = hᴴ * G * h := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin N) (Fin N) ℂ, U = 1 + Matrix.single cb ca t := ⟨_, rfl⟩
  have e : (h * U)ᴴ * G * (h * U) = (Uᴴ * H) * U := by
    rw [hH]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [← hU, ← hH, e, hU, minor_mul_shear hab t hS, ← hU]
  apply star_injective
  rw [← SchurCalc.minor_conjTranspose, ← SchurCalc.minor_conjTranspose, conjTranspose_mul,
    conjTranspose_conjTranspose, hU, minor_mul_shear hab t hS]

theorem shear_main : ∀ (N j : ℕ) (a b ca cb : Fin N) (t : ℂ), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) ∧ (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).det = 1 ∧ (∀ h : Matrix (Fin N) (Fin N) ℂ, ∀ i, facOf N j a (h * (1 + Matrix.single cb ca t)) i = facOf N j a h i) ∧ ∀ G h : Matrix (Fin N) (Fin N) ℂ, ∀ i, i ≠ a → blockPot j i G (h * (1 + Matrix.single cb ca t)) = blockPot j i G h := by
  intro N j a b ca cb t hj hb hcase hca hcb
  have hab : ca < cb := Fin.lt_def.2 (by omega)
  have ha2 := a.2
  have hb2 := b.2
  have hcb2 := cb.2
  unfold lastCol at hca
  have hblock : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j := by
    rcases hcase with h | h
    · rw [if_pos (by omega)] at hca
      omega
    · rw [if_neg (by omega)] at hca
      omega
  have hw : ca ∈ wIdx N j → cb ∈ wIdx N j := by
    simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have ho : ca ∈ omIdx N j → cb ∈ omIdx N j := by
    simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hstep : ∀ i : Fin N, i ≠ a → ca ∈ stepCols N j i → cb ∈ stepCols N j i := by
    intro i hi
    have hia : (i : ℕ) ≠ a := fun e => hi (Fin.ext e)
    have hi2 := i.2
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hcase with h | h
    · rw [if_pos (by omega)] at hca
      split_ifs <;> omega
    · rw [if_neg (by omega)] at hca
      split_ifs <;> omega
  refine ⟨?_, det_shear hab t, ?_, ?_⟩
  · intro p q hpq
    rw [SchurCalc.elem_apply, if_neg (fun e => hpq (by rw [e])), if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact hpq hblock.symm
  · intro h i
    unfold facOf
    rw [minor_mul_shear hab t hw, minor_mul_shear hab t ho]
  · intro G h i hi
    unfold blockPot
    rw [minor_gram_shear hab t (hstep i hi)]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.Shear
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl

section Cell

variable {Ψ : Type} {N j : ℕ}

def Sep (keep : Ψ × Fin N → Prop) (q : LowIdx Ψ N j) : Prop :=
  ∃ i, keep (q.1.1, i) ∧ IsProperStep N j i ∧ q.1.2.2 ∈ stepCols N j i ∧ q.1.2.1 ∉ stepCols N j i

abbrev PIdx (j : ℕ) (keep : Ψ × Fin N → Prop) : Type := {q : LowIdx Ψ N j // Sep keep q}

def cExt (keep : Ψ × Fin N → Prop) (c : PIdx j keep → ℂ) : LowIdx Ψ N j → ℂ :=
  fun q => if h : Sep keep q then c ⟨q, h⟩ else 0

def pMat (keep : Ψ × Fin N → Prop) (c : PIdx j keep → ℂ) (τ : Ψ) : Matrix (Fin N) (Fin N) ℂ :=
  lowMat (cExt keep c) τ

def pSteps (j : ℕ) (keep : Ψ × Fin N → Prop) (τ : Ψ) (b : Fin N) : Finset (Fin N) :=
  Finset.univ.filter fun i => keep (τ, i) ∧ IsProperStep N j i ∧ b ∈ stepCols N j i

def pStep (j : ℕ) (keep : Ψ × Fin N → Prop) (τ : Ψ) (b : Fin N) : Fin N :=
  if h : (pSteps j keep τ b).Nonempty then (pSteps j keep τ b).min' h else b

def pSgn (S : Finset (Fin N)) (a b : Fin N) : ℂ :=
  minorIJ (1 + Matrix.single a b (1 : ℂ)) (insert a (S.erase b)) S

end Cell

section Param

variable {n e : ℕ} {Λ : Type}

def pB (ε : Fin n ⊕ Λ ≃ Fin e) (w : Fin e → ℂ) : Fin n → ℂ := fun i => w (ε (Sum.inl i))

def pL (ε : Fin n ⊕ Λ ≃ Fin e) (w : Fin e → ℂ) : Λ → ℂ := fun q => w (ε (Sum.inr q))

def pD (ε : Fin n ⊕ Λ ≃ Fin e) (V : Set (Fin n → ℂ)) : Set (Fin e → ℂ) := {w | pB ε w ∈ V}

end Param

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)] {n e : ℕ}

def upV (v : (Σ k, ιk k) → (Σ k, ι k)) (z : (Σ k, ιk k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun q => if h : ∃ q', v q' = q then z h.choose else 0

def pBase (M : FlagModel y Ψ N j) (v : (Σ k, ιk k) → (Σ k, ι k)) (z : (Σ k, ιk k) → ℂ) :
    (Σ k, baseIdx ι M.blk k) → ℂ := basePart M.blk (upV v z)

def pRead (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (keep : Ψ × Fin N → Prop)
    (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (z : (Σ k, ι k) → ℂ) (τ : Ψ) (a b : Fin N) : ℂ :=
  (M.blk (τ, pStep j keep τ b)).elim 0 fun k =>
    twMinor M F zb (pStep j keep τ b) k (h τ)⁻¹ z (insert a ((stepCols N j (pStep j keep τ b)).erase b)) /
      (pSgn (stepCols N j (pStep j keep τ b)) a b *
        twMinor M F zb (pStep j keep τ b) k (h τ)⁻¹ z (stepCols N j (pStep j keep τ b)))

def pH (keep : Ψ × Fin N → Prop) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e) (τ : Ψ)
    (w : Fin e → ℂ) : Matrix (Fin N) (Fin N) ℂ := h τ * pMat keep (pL ε w) τ

def pPhi (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (keep : Ψ × Fin N → Prop)
    (v : (Σ k, ιk k) → (Σ k, ι k)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e) (w : Fin e → ℂ) : (Σ k, ιk k) → ℂ :=
  fun q => flagZ M F (bl (pB ε w)) (fun τ => pH keep h ε τ w) (v q)

def IsPCtx (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (κ : Kk → K)
    (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
    (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  IsBlockMap κ v ∧ (∀ k, k ∈ Set.range κ ↔ ((∀ p, M.blk p ≠ some k) ∨ ∃ p, keep p ∧ M.blk p = some k)) ∧
    M.IsFrame F ∧ IsBaseChart M Rb F kb V bl ∧
    (∀ z ∈ mcPts (mCoordIdeal M.x), SameOrbit (Rb.lift (r z) (r z)) z) ∧ ContinuousOn r (mcPts (mCoordIdeal M.x)) ∧
    ∀ τ, IsBlockDiag j (h τ) ∧ (h τ).det ≠ 0

def pO (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop)
    (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
    (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) : Set ((Σ k, ιk k) → ℂ) :=
  {z | z ∈ mcPts (mCoordIdeal (y ∘ v)) ∧ r (pBase M v z) ∈ (Rb.A.chart kb).source ∧
    Rb.A.chart kb (r (pBase M v z)) ∈ V ∧
    ∀ p k, keep p → M.blk p = some k →
      twMinor M F (pBase M v z) p.2 k (h p.1)⁻¹ (upV v z) (stepCols N j p.2) ≠ 0}

def pRho (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop)
    (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n)
    (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ)
    (ε : Fin n ⊕ PIdx j keep ≃ Fin e) (z : (Σ k, ιk k) → ℂ) : Fin e → ℂ := fun i =>
  match ε.symm i with
  | Sum.inl l => Rb.A.chart kb (r (pBase M v z)) l
  | Sum.inr q => pRead M F keep (pBase M v z) h (upV v z) q.1.1.1 q.1.1.2.1 q.1.1.2.2

theorem upV_apply {v : (Σ k, ιk k) → (Σ k, ι k)} (hv : Function.Injective v) (z : (Σ k, ιk k) → ℂ) (q : Σ k, ιk k) :
    upV v z (v q) = z q := by
  have h : ∃ q', v q' = v q := ⟨q, rfl⟩
  simp only [upV, dif_pos h]
  rw [hv h.choose_spec]

end Flag

end GlobalTheory.CompanionTheory.Ar.PB.PFl
end
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.volume_modelCrit_chart_eq_zero : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (j : Fin M.atlas.n), IsArithVar P (n + 1) → IsGoodProj P Q → volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelCrit M Q) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Push.Crit.modelCrit_null | exact GlobalTheory.CompanionTheory.Ar.Giv.Push.Crit.modelCrit_null | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Push.Crit.modelCrit_null <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical


theorem _root_.GlobalTheory.T.fubini_study_metric_smooth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (a : K → ℤ), IsSmoothHerm (fsHerm ι a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm <;> assumption)
end
