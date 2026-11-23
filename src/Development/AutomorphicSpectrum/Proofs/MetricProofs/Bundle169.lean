module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle097
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle166
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle122
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle162
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle103
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle132
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle167
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle146
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle134
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle120
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle164
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem exists_flags_of_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (d : ℕ) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 2) → ∀ (l : Fin BM.q), ∀ b' ∈ BM.O l, ∀ z ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)), SameOrbit (basePart M.blk (fstPt k₀ z)) (BM.Rb.lift b' b') → ∃ (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (t : ℂ), (∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0) ∧ SameOrbit z (FC.wVec M (BM.F l) (FC.bvec BM l b') h τ a k₀ ca cb t) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM d τ a b k₀ ca cb hb hj hblk hca hcb hy l b' hb' z hz ho
  obtain ⟨g1, g2, g3, g4⟩ := FC.bvec_good K ι Φ y Ψ N j M n BM l b' hb'
  set β := FC.bvec BM l b' with hβ
  obtain ⟨c, hc, ec⟩ : SameOrbit (basePart M.blk (fstPt k₀ z)) β := orbit_trans ho (orbit_symm g4)
  let t : Option K → ℂ := fun o => match o with
    | some k => if hk : ∀ p, M.blk p ≠ some k then (c ⟨k, hk⟩)⁻¹ else 1
    | none => 1
  have ht : ∀ o, t o ≠ 0 := fun o => by
    cases o with
    | none => exact one_ne_zero
    | some k =>
      by_cases hk : ∀ p, M.blk p ≠ some k
      · simp only [t, dif_pos hk]
        exact inv_ne_zero (hc _)
      · simp only [t, dif_neg hk]
        exact one_ne_zero
  let z₁ : (Σ o : Option K, ι (o.getD k₀)) → ℂ := fun p => t p.1 * z p
  have o2 : SameOrbit z₁ z := ⟨t, ht, rfl⟩
  have hz₁ : z₁ ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) :=
    mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal _) o2 hz
  have eb : basePart M.blk (fstPt k₀ z₁) = β := by
    funext q
    obtain ⟨⟨k, hk⟩, m⟩ := q
    have e : z ⟨some k, m⟩ = c ⟨k, hk⟩ * β ⟨⟨k, hk⟩, m⟩ := congrFun ec ⟨⟨k, hk⟩, m⟩
    show t (some k) * z ⟨some k, m⟩ = β _
    simp only [t, dif_pos hk]
    rw [e, inv_mul_cancel_left₀ (hc _)]
  have P := GlobalTheory.T.log_period_statement K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hj hblk hca hcb hy (BM.F l) z₁ (BM.isFrame l)
    (by rw [eb]; exact g1) (by rw [eb]; exact g2) (by rw [eb]; exact g3)
  obtain ⟨h, s, f1, f2⟩ := P.1 hz₁
  refine ⟨h, s, f1.2.1, orbit_trans (orbit_symm o2) ?_⟩
  have eb2 : basePart M.blk (sndPt k₀ z₁) = β := by
    funext q
    obtain ⟨⟨k, hk⟩, m⟩ := q
    have hne : k ≠ k₀ := fun e => hk (τ, a) (by rw [hblk, e])
    have e1 : sndPt k₀ z₁ ⟨k, m⟩ = fstPt k₀ z₁ ⟨k, m⟩ := by
      show z₁ (v₁ k₀ ⟨k, m⟩) = z₁ (v₀ k₀ ⟨k, m⟩)
      rw [v₁_ne hne]
      rfl
    exact e1.trans (congrFun eb ⟨⟨k, hk⟩, m⟩)
  have key : ∀ o : Option K, ∃ e : ℂ, e ≠ 0 ∧ ∀ m : ι (o.getD k₀),
      z₁ ⟨o, m⟩ = e * FC.wVec M (BM.F l) β h τ a k₀ ca cb s ⟨o, m⟩ := fun o => by
    cases o with
    | none =>
      obtain ⟨e, he, w⟩ := f2.2.2 (τ, a) k₀ hblk
      refine ⟨e, he, fun m => ?_⟩
      have w' := w m
      rw [eb2] at w'
      simp only [Function.update_self] at w'
      have e1 : sndPt k₀ z₁ ⟨k₀, m⟩ = z₁ ⟨none, m⟩ := by
        show z₁ (v₁ k₀ ⟨k₀, m⟩) = _
        rw [v₁_self]
      rw [← e1, w']
      rfl
    | some k =>
      by_cases hk : ∀ p, M.blk p ≠ some k
      · refine ⟨1, one_ne_zero, fun m => ?_⟩
        have e1 := congrFun eb ⟨⟨k, hk⟩, m⟩
        have e2 := congrFun (FC.basePart_flagPt M (BM.F l) β h) ⟨⟨k, hk⟩, m⟩
        show z₁ ⟨some k, m⟩ = 1 * FC.flagPt M (BM.F l) β h ⟨k, m⟩
        rw [one_mul]
        exact e1.trans e2.symm
      · push_neg at hk
        obtain ⟨p, hp⟩ := hk
        obtain ⟨e, he, w⟩ := f1.2.2 p k hp
        refine ⟨e, he, fun m => ?_⟩
        have w' := w m
        rw [eb] at w'
        show z₁ ⟨some k, m⟩ = e * FC.flagPt M (BM.F l) β h ⟨k, m⟩
        rw [FC.flagPt_step M (BM.F l) β h hp m]
        exact w'
  choose e he hm using key
  exact ⟨e, he, funext fun q => hm q.1 q.2⟩

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.WMem

section Mat

variable {N j : ℕ}

theorem transv_isBlockDiag {a b ca cb : Fin N} (hb : (b : ℕ) = a + 1) (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) (t : ℂ) :
    IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) := by
  have same : ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) := by
    have := a.2
    have := b.2
    have := cb.2
    unfold lastCol at hca
    split_ifs at hca <;> omega
  intro r s hrs
  have e1 : r ≠ s := fun e => hrs (by rw [e])
  rw [Matrix.add_apply, Matrix.one_apply_ne e1, zero_add, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hrs same.symm

theorem transv_det_one {ca cb : Fin N} (hc : (cb : ℕ) = ca + 1) (t : ℂ) :
    (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).det = 1 := by
  have hne : ca ≠ cb := fun e => by rw [e] at hc; omega
  have hlt : ca < cb := by rw [Fin.lt_def]; omega
  rw [Matrix.det_of_lowerTriangular _ fun r c h => ?_]
  · refine Finset.prod_eq_one fun c _ => ?_
    rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply_of_ne, add_zero]
    rintro ⟨rfl, e⟩
    exact hne e
  · have h' : r < c := h
    rw [Matrix.add_apply, Matrix.one_apply_ne h'.ne, Matrix.single_apply_of_ne, add_zero]
    rintro ⟨rfl, rfl⟩
    exact lt_asymm h' hlt

end Mat

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem isFlagOf_flagPt (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {b : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hb : ∀ k, b ⟨k, F.c k⟩ = 1) {h : Ψ → Matrix (Fin N) (Fin N) ℂ}
    (hh : ∀ τ, IsBlockDiag j (h τ) ∧ (h τ).det ≠ 0) : M.IsFlagOf F (flagPt M F b h) h := by
  refine ⟨fun k => by rw [basePart_flagPt]; exact hb k, hh, fun p k hp => ⟨1, one_ne_zero, fun m => ?_⟩⟩
  rw [basePart_flagPt, flagPt_step M F b h hp m, one_mul]

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (d : ℕ) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 2) → ∀ (l : Fin BM.q), ∀ b' ∈ BM.O l, ∀ (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (t : ℂ), (∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0) → FC.wVec M (BM.F l) (FC.bvec BM l b') h τ a k₀ ca cb t ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM d τ a b k₀ ca cb hb hab hk hca hcb hvar l b' hb' h t hh
  obtain ⟨h1, h2⟩ := GlobalTheory.T.flag_adjacent_plucker_orbit K ι Φ y Ψ N j M τ a b k₀ ca cb hb hab hk hca hcb (BM.F l) (bvec BM l b') h t
  obtain ⟨g1, g2, g3, -⟩ := GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec_good K ι Φ y Ψ N j M n BM l b' hb'
  have hh' : ∀ τ', IsBlockDiag j (Function.update h τ (h τ * (1 + Matrix.single cb ca t)) τ') ∧
      (Function.update h τ (h τ * (1 + Matrix.single cb ca t)) τ').det ≠ 0 := by
    intro τ'
    by_cases e : τ' = τ
    · subst e
      rw [Function.update_self]
      refine ⟨(hh τ').1.mul (transv_isBlockDiag hb hab hca hcb t), ?_⟩
      rw [Matrix.det_mul, transv_det_one hcb, mul_one]
      exact (hh τ').2
    · rw [Function.update_of_ne e]
      exact hh τ'
  have hbase : basePart M.blk (fstPt k₀ (wVec M (BM.F l) (bvec BM l b') h τ a k₀ ca cb t)) = bvec BM l b' := by
    rw [h1, basePart_flagPt]
  refine (GlobalTheory.T.log_period_statement K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hvar (BM.F l) _ (BM.isFrame l)
    (by rw [hbase]; exact g1) (by rw [hbase]; exact g2) (by rw [hbase]; exact g3)).2 ⟨h, t, ?_, ?_⟩
  · rw [h1]
    exact isFlagOf_flagPt M (BM.F l) g3 hh
  · rw [h2]
    exact isFlagOf_flagPt M (BM.F l) g3 hh'

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.WMem
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ z ∈ wO M Rb τ a k₀ ca cb F kb V r h, wRho M Rb τ k₀ ca cb F kb r h ε z ∈ wD ε V ∧ SameOrbit (wPhi M F bl h ε k₀ τ ca cb (wRho M Rb τ k₀ ca cb F kb r h ε z)) z := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hctx z hz
  have hctx' := hctx
  obtain ⟨hb, hab, hk, hca, hcb, hy, hF, hBC, hr, hrc, hh⟩ := hctx'
  obtain ⟨hmem, hsrc, hV, hden, hden2⟩ := hz
  obtain ⟨hzb, hG, horb, h', t', hh', Hf, Hs⟩ := GlobalTheory.T.flag_adjacent_chart_tenth K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h hctx z
    ⟨hmem, hsrc, hV, hden, hden2⟩
  have hS := Pts.same_summand hb hab hca hcb
  have hj := M.j_le
  set zb := baseOf M k₀ z with hzbdef
  set w := wRho M Rb τ k₀ ca cb F kb r h ε z with hw
  have hwB : wB ε w = Rb.A.chart kb (r zb) := by
    funext i
    simp [wB, hw, wRho, zb]
  have hwL : ∀ q, wL ε w q = lowRead M F zb h (fstPt k₀ z) q.1.1 q.1.2.1 q.1.2.2 := fun q => by
    simp [wL, hw, wRho, zb]
  have hwT : wT ε w = lowRead M F zb h (sndPt k₀ z) τ cb ca - lowRead M F zb h (fstPt k₀ z) τ cb ca := by
    simp [wT, hw, wRho, zb]
  refine ⟨show wB ε w ∈ V by rw [hwB]; exact hV, ?_⟩
  have hdu : ∀ τ', IsUnit (h τ').det := fun τ' => (hh τ').2.isUnit
  let G : Ψ → Matrix (Fin N) (Fin N) ℂ := fun τ' => (h τ')⁻¹ * h' τ'
  have hGb : ∀ τ', IsBlockDiag j (G τ') := fun τ' => ((hh τ').1.inv (hdu τ')).mul (hh' τ').1
  have hinvd : ∀ τ', ((h τ')⁻¹).det ≠ 0 := fun τ' h0 => by
    have h1 := Matrix.det_nonsing_inv_mul_det (h τ') (hdu τ')
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hGd : ∀ τ', (G τ').det ≠ 0 := fun τ' => by
    show ((h τ')⁻¹ * h' τ').det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (hinvd τ') (hh' τ').2
  have hmin : ∀ τ' i, IsProperStep N j i → minorIJ (G τ') (stepCols N j i) (stepCols N j i) ≠ 0 := by
    intro τ' i hi h0
    obtain ⟨k, hp⟩ : ∃ k, M.blk (τ', i) = some k := Option.ne_none_iff_exists'.1 fun e => (M.blk_none _).1 e hi
    obtain ⟨α, hα, hz₁⟩ := Hf (τ', i) k hp
    refine hden (τ', i) k hp ?_
    rw [GlobalTheory.T.frame_minor_value_formula K ι Φ y Ψ N j M F zb (τ', i) k (h' τ') (h τ')⁻¹ (fstPt k₀ z) α _ hF hzb hG hp (hh' τ').1 hz₁]
    show α * minorIJ (G τ') _ _ = 0
    rw [h0, mul_zero]
  choose L U hLb hLu hUb hUt hUd hLU using fun τ' => GlobalTheory.T.block_LU_factorization N j (G τ') hj (hGb τ') (hGd τ') (hmin τ')
  have hhL : ∀ τ', h τ' * (L τ' * U τ') = h' τ' := fun τ' => by
    rw [← hLU]
    exact Matrix.mul_nonsing_inv_cancel_left _ _ (hdu τ')
  have hlow : ∀ τ' (a' b' : Fin N), b' < a' → ((a' : ℕ) < N - j ↔ (b' : ℕ) < N - j) →
      lowRead M F zb h (fstPt k₀ z) τ' a' b' = L τ' a' b' := fun τ' a' b' e e' =>
    GlobalTheory.T.frame_LU_minor_value K ι Φ y Ψ N j M F zb h τ' a' b' (fstPt k₀ z) (h' τ') (L τ') (U τ') hF hzb hG (hh' τ').1 (hLU τ')
      (hLb τ') (hLu τ') (hUb τ') (hUt τ') (fun c _ => hUd τ' c) e e' (fun k hp => Hf (τ', stepOf N j b') k hp)
  have hlm : ∀ τ', lowMat (wL ε w) τ' = L τ' := fun τ' => by
    ext a' b'
    unfold lowMat
    split_ifs with e e'
    · rw [hwL]
      exact hlow τ' a' b' e.1 e.2
    · rw [e', (hLu τ').1]
    · rcases lt_or_gt_of_ne e' with e' | e'
      · exact ((hLu τ').2 _ _ e').symm
      · exact ((hLb τ') _ _ fun e'' => e ⟨e', e''⟩).symm
  obtain ⟨α₂, hα₂, hz₂⟩ := Hs
  have hne2 : minorIJ (L τ * U τ * (1 + Matrix.single cb ca t')) (stepCols N j a) (stepCols N j a) ≠ 0 := by
    intro h0
    refine hden2 ?_
    rw [GlobalTheory.T.frame_minor_value_formula K ι Φ y Ψ N j M F zb (τ, a) k₀ (h' τ * (1 + Matrix.single cb ca t')) (h τ)⁻¹ (sndPt k₀ z) α₂ _ hF hzb hG hk
      ((hh' τ).1.mul (Pts.transv_block hS t')) hz₂, ← Matrix.mul_assoc]
    show α₂ * minorIJ (G τ * _) _ _ = 0
    rw [hLU, h0, mul_zero]
  obtain ⟨t, Vm, hVb, hVt, hVd, hUV⟩ := GlobalTheory.T.LU_twist_refactorization N j a ca cb (L τ) (U τ) t' hj hca hcb hS (hLb τ) (hLu τ) (hUb τ) (hUt τ)
    (hUd τ) hne2
  have hlt : ca < cb := by rw [Fin.lt_def]; omega
  have hstep : stepOf N j ca = a := by
    have := a.2
    apply Fin.ext
    simp only [stepOf, hca, lastCol]
    split_ifs <;> omega
  have hcc : ∀ c, c ∈ stepCols N j (stepOf N j ca) → Vm c c ≠ 0 := fun c hc => hVd c (hstep ▸ hc)
  have hLe : ∀ r c, (L τ * (1 + Matrix.single cb ca t)) r c = L τ r c + if c = ca then L τ r cb * t else 0 := by
    intro r c
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
    congr 1
    by_cases e : c = ca
    · subst e
      simp [Matrix.mul_single_apply_same]
    · rw [if_neg e, Matrix.mul_single_apply_of_ne _ _ _ _ _ e]
  have hL2 : IsLowerUni (L τ * (1 + Matrix.single cb ca t)) := by
    refine ⟨fun r => ?_, fun r c e => ?_⟩
    · rw [hLe, (hLu τ).1]
      split_ifs with e
      · rw [e, (hLu τ).2 _ _ hlt, zero_mul, add_zero]
      · rw [add_zero]
    · rw [hLe, (hLu τ).2 _ _ e]
      split_ifs with e'
      · rw [(hLu τ).2 r cb (e.trans (e' ▸ hlt)), zero_mul, add_zero]
      · rw [add_zero]
  have hL2c : (L τ * (1 + Matrix.single cb ca t)) cb ca = L τ cb ca + t := by
    rw [hLe, if_pos rfl, (hLu τ).1, one_mul]
  have hsnd : lowRead M F zb h (sndPt k₀ z) τ cb ca = L τ cb ca + t := by
    rw [← hL2c]
    refine GlobalTheory.T.frame_LU_minor_value K ι Φ y Ψ N j M F zb h τ cb ca (sndPt k₀ z) (h' τ * (1 + Matrix.single cb ca t')) _ Vm hF hzb hG
      ((hh' τ).1.mul (Pts.transv_block hS t')) ?_ ((hLb τ).mul (Pts.transv_block hS t)) hL2 hVb hVt hcc hlt hS.symm ?_
    · rw [← Matrix.mul_assoc]
      show G τ * _ = _
      rw [hLU, Matrix.mul_assoc, hUV, Matrix.mul_assoc]
    · intro k hp
      rw [hstep, hk] at hp
      obtain rfl := Option.some.inj hp
      exact ⟨α₂, hα₂, by rw [hstep]; exact hz₂⟩
  have hwt : wT ε w = t := by
    rw [hwT, hsnd, hlow τ cb ca hlt hS.symm]
    ring
  have hHU : ∀ τ', (fun τ' => wH h ε τ' w) τ' * U τ' = h' τ' := fun τ' => by
    show h τ' * lowMat (wL ε w) τ' * U τ' = _
    rw [hlm, Matrix.mul_assoc, hhL]
  show SameOrbit (sqZ M F (bl (wB ε w)) (fun τ' => wH h ε τ' w) k₀ τ ca cb (wT ε w)) z
  rw [hwB, hwt]
  refine GlobalTheory.T.twisted_frame_value_formula K ι Φ y Ψ N j M τ a k₀ ca cb F _ z _ U Vm t hk hzb hG horb
    (fun τ' => ⟨hUb τ', hUt τ', hUd τ'⟩) hVb hVt hVd (fun p k hp => ?_) ⟨α₂, hα₂, fun m => ?_⟩
  · rw [hHU]
    exact Hf p k hp
  · have e : (fun τ' => wH h ε τ' w) τ * (1 + Matrix.single cb ca t) * Vm = h' τ * (1 + Matrix.single cb ca t') := by
      rw [← hHU τ, Matrix.mul_assoc, Matrix.mul_assoc, hUV]
    rw [e]
    exact hz₂ m

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto
end
end
