module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle097
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle102
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle075
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle103
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle004
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle088

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

private theorem sum_eq_sum_orderEmbOfFin_of_zero_off {N : ℕ} (S : Finset (Fin N)) (F : Fin N → ℂ)
    (hz : ∀ a, a ∉ S → F a = 0) :
    ∑ a, F a = ∑ z : Fin S.card, F (S.orderEmbOfFin rfl z) := by
  calc ∑ a, F a = ∑ a ∈ S, F a :=
        (Finset.sum_subset (Finset.subset_univ S) (fun a _ ha => hz a ha)).symm
    _ = ∑ i : S, F i := (Finset.sum_coe_sort S F).symm
    _ = ∑ z : Fin S.card, F (S.orderEmbOfFin rfl z) :=
        (Fintype.sum_equiv (S.orderIsoOfFin rfl).toEquiv _ _
          (fun z => by simp [Finset.coe_orderIsoOfFin_apply])).symm

private theorem minorIJ_mul_of_block {N : ℕ} (h B : Matrix (Fin N) (Fin N) ℂ) (S I : Finset (Fin N))
    (hB : ∀ a c, c ∈ S → a ∉ S → B a c = 0) :
    minorIJ (h * B) I S = minorIJ h I S * minorIJ B S S := by
  unfold minorIJ
  by_cases e : I.card = S.card
  · rw [dite_eq_left e, dite_eq_left e, dite_eq_left rfl, ← Matrix.det_mul]
    congr 1
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    exact sum_eq_sum_orderEmbOfFin_of_zero_off S (fun a => h (I.orderEmbOfFin e x) a * B a (S.orderEmbOfFin rfl y))
      (fun a ha => by rw [hB a _ (Finset.orderEmbOfFin_mem S rfl y) ha, mul_zero])
  · rw [dite_eq_right e, dite_eq_right e, zero_mul]

private theorem apply_eq_zero_of_mem_stepCols_not_mem {N j : ℕ} (B : Matrix (Fin N) (Fin N) ℂ) (i : Fin N)
    (hd : IsBlockDiag j B) (ht : B.BlockTriangular id) :
    ∀ a c, c ∈ stepCols N j i → a ∉ stepCols N j i → B a c = 0 := by
  intro a c hc ha
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hc ha
  have hi := i.isLt
  by_cases hblk : ((a : ℕ) < N - j ↔ (c : ℕ) < N - j)
  · apply ht
    show c < a
    rw [Fin.lt_def]
    split_ifs at hc ha <;> omega
  · exact hd a c hblk

private theorem minorIJ_ne_zero_of_blockTriangular {N : ℕ} (B : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N))
    (ht : B.BlockTriangular id) (hdet : B.det ≠ 0) : minorIJ B S S ≠ 0 := by
  unfold minorIJ
  rw [dite_eq_left rfl]
  have hdiag : ∀ a, B a a ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular ht] at hdet
    exact fun a => (Finset.prod_ne_zero_iff.mp hdet) a (Finset.mem_univ a)
  have htS : (B.submatrix (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl)).BlockTriangular id :=
    fun x y hxy => ht ((S.orderEmbOfFin rfl).strictMono hxy)
  rw [Matrix.det_of_isUpperTriangular htS]
  exact Finset.prod_ne_zero_iff.mpr (fun z _ => hdiag _)

theorem sameOrbit_flagPt_mul : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ) (h B : Ψ → Matrix (Fin N) (Fin N) ℂ), (∀ τ', IsBlockDiag j (B τ') ∧ (B τ').BlockTriangular id ∧ (B τ').det ≠ 0) → SameOrbit (FC.flagPt M F b fun τ' => h τ' * B τ') (FC.flagPt M F b h) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F b h B hB
  refine Exists.intro (fun k => if hk : ∀ p, M.blk p ≠ some k then (1 : ℂ) else
    minorIJ (B (not_forall.1 hk).choose.1) (stepCols N j (not_forall.1 hk).choose.2)
      (stepCols N j (not_forall.1 hk).choose.2)) ⟨fun k => ?_, ?_⟩
  · dsimp only
    split_ifs with hk
    · exact one_ne_zero
    · generalize (not_forall.1 hk).choose = p
      exact minorIJ_ne_zero_of_blockTriangular (B p.1) (stepCols N j p.2) (hB p.1).2.1 (hB p.1).2.2
  · funext q
    simp only [flagPt]
    split_ifs with hk
    · rw [one_mul]
    · generalize (not_forall.1 hk).choose = p
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun I _ => ?_)
      rw [minorIJ_mul_of_block (h p.1) (B p.1) (stepCols N j p.2) I
        (apply_eq_zero_of_mem_stepCols_not_mem (B p.1) p.2 (hB p.1).1 (hB p.1).2.1)]
      ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

theorem log_refNorm_blocks {κ : Type} [Fintype κ] {ρ : κ → Type} [∀ k, Fintype (ρ k)] (d : κ → ℤ)
    {z : (Σ k, ρ k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (refNorm d z) = ∑ k, (d k : ℝ) / 2 * Real.log (∑ i, ‖z ⟨k, i⟩‖ ^ 2) := by
  have hpos : ∀ k, 0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := fun k => by
    obtain ⟨i, hi⟩ := hz k
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2)
      (Finset.single_le_sum (fun i _ => sq_nonneg ‖z ⟨k, i⟩‖) (Finset.mem_univ i))
  unfold refNorm
  rw [Real.log_prod fun k _ => (Real.rpow_pos_of_pos (hpos k) _).ne']
  exact Finset.sum_congr rfl fun k _ => Real.log_rpow (hpos k) _

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem xiDeg_self (M : FlagModel y Ψ N j) {τ : Ψ} {a : Fin N} {k₀ : K} (hk : M.blk (τ, a) = some k₀) :
    xiDeg M τ a k₀ = -2 := by
  have hd : ∀ p, M.dy p k₀ = if p = (τ, a) then 1 else 0 := fun p => by
    have hn : ¬ ∀ p', M.blk p' ≠ some k₀ := fun h => h _ hk
    unfold FlagModel.dy
    rw [dite_eq_right hn]
    by_cases hp : p = (τ, a)
    · rw [if_pos (hp ▸ hk), if_pos hp]
    · rw [if_neg fun e => hp (M.blk_inj _ _ k₀ e hk), if_neg hp]
  unfold xiDeg
  simp only [hd, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp [xiCoef]

theorem log_potA : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K), M.blk (τ, a) = some k₀ → ∀ zz : (Σ o : Option K, ι (o.getD k₀)) → ℂ, (∀ o, ∃ i, zz ⟨o, i⟩ ≠ 0) → Real.log ((potA M τ a k₀).h zz) = -(1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h (fstPt k₀ zz)) + Real.log ((fsHerm ι (M.dy p)).h (sndPt k₀ zz))) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M τ a k₀ hk zz hz
  have hf : ∀ k, ∃ i, fstPt k₀ zz ⟨k, i⟩ ≠ 0 := fun k => hz (some k)
  have hs : ∀ k, ∃ i, sndPt k₀ zz ⟨k, i⟩ ≠ 0 := fun k => by
    by_cases e : k = k₀
    · subst e
      obtain ⟨i, hi⟩ := hz none
      refine ⟨i, ?_⟩
      simpa [sndPt, v₁_self] using hi
    · obtain ⟨i, hi⟩ := hz (some k)
      refine ⟨i, ?_⟩
      simpa [sndPt, v₁_ne (p := ⟨k, i⟩) e] using hi
  set A : K → ℝ := fun k => Real.log (∑ i, ‖fstPt k₀ zz ⟨k, i⟩‖ ^ 2) with hA
  set B : K → ℝ := fun k => Real.log (∑ i, ‖sndPt k₀ zz ⟨k, i⟩‖ ^ 2) with hB
  set Ln : ℝ := Real.log (∑ i : ι k₀, ‖zz ⟨none, i⟩‖ ^ 2) with hLn
  have hB₀ : B k₀ = Ln := by
    simp only [hB, hLn, sndPt, Function.comp_apply, v₁_self]
  have hBne : ∀ k, k ≠ k₀ → B k = A k := fun k e => by
    simp only [hA, hB, fstPt, sndPt, Function.comp_apply, v₀]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [v₁_ne (p := ⟨k, i⟩) e]
  have hlhs : Real.log ((potA M τ a k₀).h zz) = 1 / 2 * Ln + ∑ k, (aDeg M τ a k₀ (some k) : ℝ) / 2 * A k := by
    show Real.log (refNorm (aDeg M τ a k₀) zz) = _
    rw [log_refNorm_blocks _ hz, Fintype.sum_option]
    simp only [aDeg, hLn, hA]
    norm_num
    rfl
  have hrhs : ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h (fstPt k₀ zz)) +
      Real.log ((fsHerm ι (M.dy p)).h (sndPt k₀ zz))) = ∑ k, (xiDeg M τ a k : ℝ) / 2 * (A k + B k) := by
    have hp : ∀ p, Real.log ((fsHerm ι (M.dy p)).h (fstPt k₀ zz)) + Real.log ((fsHerm ι (M.dy p)).h (sndPt k₀ zz)) =
        ∑ k, (M.dy p k : ℝ) / 2 * (A k + B k) := fun p => by
      rw [fsHerm_h, fsHerm_h, log_refNorm_blocks _ hf, log_refNorm_blocks _ hs, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by simp only [hA, hB]; ring
    simp only [hp, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [xiDeg]
    push_cast
    rw [Finset.sum_div, Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hlhs, hrhs]
  have hterm : ∀ k, (aDeg M τ a k₀ (some k) : ℝ) / 2 * A k + 1 / 2 * ((xiDeg M τ a k : ℝ) / 2 * (A k + B k)) =
      if k = k₀ then -(1 / 2) * Ln else 0 := fun k => by
    by_cases e : k = k₀
    · subst e
      rw [if_pos rfl, hB₀, xiDeg_self M hk]
      simp only [aDeg, if_true]
      push_cast
      ring
    · rw [if_neg e, hBne k e]
      simp only [aDeg, if_neg e]
      push_cast
      ring
  have hsum := Finset.sum_congr (rfl : (Finset.univ : Finset K) = _) fun k _ => hterm k
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq' Finset.univ k₀, if_pos (Finset.mem_univ _)] at hsum
  linarith

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

theorem GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.diagSec_isSNC_diagSet : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), ∀ c : ℝ, IsSNC RW.A (secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) (diagSec ψ i₀ u) ![1] ![diagSet k₀ RW] := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL c x
  obtain ⟨⟨F, H, hW⟩, hVo, hxV, hVs, -, hu, hu0, hd, -⟩ := hL x
  have hsrc : ((ψ x).restrOpen (V x) hVo).source = V x := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact Set.inter_eq_right.mpr hVs
  refine ⟨(ψ x).restrOpen (V x) hVo, pa_compat_restr RW.A (ψ x) hW.1 (V x) hVo, by rw [hsrc]; exact hxV, ?_,
    fun _ => some (i₀ x), ?_, ?_, u x, ?_, ?_, ?_⟩
  · rw [hsrc]; exact subset_rfl
  · intro k k' _ _ _
    exact Subsingleton.elim k k'
  · intro k
    obtain rfl : k = 0 := Subsingleton.elim k 0
    rw [hsrc]
    ext w
    constructor
    · rintro ⟨hw, hwV⟩
      exact ⟨hwV, i₀ x, rfl, (hd w hwV).2 hw⟩
    · rintro ⟨hwV, i, hi, hw⟩
      obtain rfl : i₀ x = i := Option.some.inj hi
      exact ⟨(hd w hwV).1 hw, hwV⟩
  · rw [hsrc]; exact hu
  · rw [hsrc]; exact hu0
  · rw [hsrc]
    intro w _
    simp [diagSec]
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

theorem locSec_norm_eq : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (x x' : RW.X) (ψ ψ' : OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb kb' : Fin Rb.A.n) (σ σ' : Fin n ↪ Fin e) (i₀ i₀' : Fin e) (V V' : Set RW.X) (u u' : RW.X → ℂ), M.blk (τ, a) = some k₀ → IsWAtlas M Rb τ a k₀ ca cb RW pr → IsLocSec M Rb τ a k₀ ca cb RW pr x ψ kb σ i₀ V u → IsLocSec M Rb τ a k₀ ca cb RW pr x' ψ' kb' σ' i₀' V' u' → ∀ w ∈ V ∩ V', ‖u w * ψ w i₀‖ / (potA M τ a k₀).h (RW.lift x w) = ‖u' w * ψ' w i₀'‖ / (potA M τ a k₀).h (RW.lift x' w) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a k₀ ca cb RW pr x x' ψ ψ' kb kb' σ σ' i₀ i₀' V V' u u' _ _ hs hs' w hw
  obtain ⟨⟨F, H, hc⟩, -, -, hVs, hVU, -, hu, hd, hn⟩ := hs
  obtain ⟨-, -, -, -, hVU', -, hu', hd', hn'⟩ := hs'
  by_cases h0 : ψ w i₀ = 0
  · have h0' : ψ' w i₀' = 0 := (hd' w hw.2).2 ((hd w hw.1).1 h0)
    simp [h0, h0']
  have h0' : ψ' w i₀' ≠ 0 := fun h => h0 ((hd w hw.1).2 ((hd' w hw.2).1 h))
  obtain ⟨-, hF, -, -, -, hp⟩ := hc
  obtain ⟨hH, hG, z₀, z₁, hz₀, hz₁, hex⟩ := hp w (hVs hw.1)
  have hG' : M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) := by
    obtain ⟨c, hc0, hzc⟩ := hz₀
    have e₀ : basePart M.blk z₀ = fun q : Σ k, baseIdx ι M.blk k =>
        (fun k : NonPluckerBlocks M.blk => c k.1) q.1 * basePart M.blk (fstPt k₀ (RW.lift w w)) q := by
      rw [hzc]; rfl
    rw [e₀, GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.mCoordIdeal_torus (K := NonPluckerBlocks M.blk) (ι := baseIdx ι M.blk)
      (fun k : NonPluckerBlocks M.blk => c k.1) (fun k => hc0 k.1) (basePart M.blk (fstPt k₀ (RW.lift w w)))]
    exact hG
  have hD : IsPtData M τ a k₀ ca cb RW w z₀ z₁ F (H τ (ψ w)) (ψ w i₀) :=
    ⟨hF, hG', hz₀, hz₁, (hH τ).1, (hH τ).2, h0, fun i => (hex τ i).1, fun i => by
      simpa using (hex τ i).2⟩
  have e₁ := hn w hw.1 h0 z₀ z₁ F _ _ hD
  have e₂ := hn' w hw.2 h0' z₀ z₁ F _ _ hD
  have hA : 0 < (potA M τ a k₀).h (RW.lift x w) := (potA M τ a k₀).pos _ (RW.mem x w (hVU hw.1)).1
  have hA' : 0 < (potA M τ a k₀).h (RW.lift x' w) := (potA M τ a k₀).pos _ (RW.mem x' w (hVU' hw.2)).1
  have hN : 0 < ‖u w * ψ w i₀‖ := norm_pos_iff.2 (mul_ne_zero (hu w hw.1) h0)
  have hN' : 0 < ‖u' w * ψ' w i₀'‖ := norm_pos_iff.2 (mul_ne_zero (hu' w hw.2) h0')
  refine Real.log_injOn_pos (Set.mem_Ioi.2 (div_pos hN hA)) (Set.mem_Ioi.2 (div_pos hN' hA')) ?_
  rw [Real.log_div hN.ne' hA.ne', Real.log_div hN'.ne' hA'.ne', e₁, e₂]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

private theorem isPotential_secPot_of_isSmoothHerm {κ : Type} [Fintype κ] {ρ : κ → Type} [∀ k, Fintype (ρ k)]
    {P J : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ρ)} {e : ℕ} (R : ReciprocityTheory.ChartRestriction.G.Geo.AnLogRes P J e)
    (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ρ) (hA : ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A)
    (V : R.X → Set R.X) (hV : ∀ x, IsOpen (V x)) (hm : ∀ x, x ∈ V x) (hVU : ∀ x, V x ⊆ R.U x)
    (c : ℝ) : ReciprocityTheory.AnForm.M.IsPotential R.A (secPot R A V hV hm c) := by
  have hA' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := hA
  have hol : ∀ (x : R.X) (p : (k : κ) × ρ k) (j : Fin R.A.n) (t : Fin e → ℂ),
      t ∈ (R.A.chart j).target → (R.A.chart j).symm t ∈ R.U x →
      AnalyticAt ℂ (fun s => R.lift x ((R.A.chart j).symm s) p) t :=
    fun x p j t ht hu => R.holo x p j t ⟨ht, hu⟩
  have memNZ : ∀ (z0 y0 : R.X), y0 ∈ R.U z0 → ∀ k, ∃ i, R.lift z0 y0 ⟨k, i⟩ ≠ 0 := by
    intro z0 y0 h
    have h' := R.mem z0 y0 h
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.mcPts, Set.mem_ofPred_eq] at h'
    exact h'.1
  unfold ReciprocityTheory.AnForm.M.IsPotential ReciprocityTheory.AnForm.M.FinHolAtlas.SmoothOn
    ReciprocityTheory.AnForm.M.FinHolAtlas.HoloOn
  dsimp only [secPot]
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · have hlift : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => R.lift x ((R.A.chart j).symm t))
        ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' V x) := by
      rw [contDiffOn_pi]
      intro p
      have h1 : ContDiffOn ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => R.lift x ((R.A.chart j).symm t) p)
          ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' V x) :=
        fun t ht => (hol x p j t ht.1 (hVU x ht.2)).contDiffAt.contDiffWithinAt
      exact h1.restrict_scalars ℝ
    have hmem : ∀ t ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' V x,
        (∀ k, ∃ i, R.lift x ((R.A.chart j).symm t) ⟨k, i⟩ ≠ 0) :=
      fun t ht => memNZ x _ (hVU x ht.2)
    have hh := hA'.comp hlift (fun t ht => hmem t ht)
    have hne : ∀ t ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' V x,
        A.h (R.lift x ((R.A.chart j).symm t)) ≠ 0 :=
      fun t ht => (A.pos _ (hmem t ht)).ne'
    exact (hh.log hne).add contDiffOn_const
  · obtain ⟨hyx, hyx'⟩ := hy
    have hyU : y ∈ R.U x := hVU x hyx
    have hyU' : y ∈ R.U x' := hVU x' hyx'
    choose i hi using memNZ x' y hyU'
    obtain ⟨r, hr⟩ : ∃ r : κ → R.X → ℂ,
        ∀ k z, r k z = R.lift x z ⟨k, i k⟩ / R.lift x' z ⟨k, i k⟩ :=
      ⟨fun k z => R.lift x z ⟨k, i k⟩ / R.lift x' z ⟨k, i k⟩, fun _ _ => rfl⟩
    have hry : ∀ k, r k y ≠ 0 := by
      intro k
      obtain ⟨cy, hcy, hly⟩ := R.compat x x' y ⟨hyU, hyU'⟩
      have h1 := congrFun hly ⟨k, i k⟩
      rw [hr, h1]
      exact div_ne_zero (mul_ne_zero (hcy k) (hi k)) (hi k)
    obtain ⟨j, hj⟩ := R.A.cover y
    have hD : IsOpen ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' (R.U x ∩ R.U x')) :=
      (R.A.chart j).isOpen_inter_preimage_symm ((R.isOpen_U x).inter (R.isOpen_U x'))
    obtain ⟨O, hOdef⟩ : ∃ O : Set (Fin e → ℂ), O = {t | t ∈ (R.A.chart j).target ∧
        (R.A.chart j).symm t ∈ R.U x ∩ R.U x' ∧
        (∀ k, R.lift x' ((R.A.chart j).symm t) ⟨k, i k⟩ ≠ 0) ∧
        ∀ k, r k ((R.A.chart j).symm t) / r k y ∈ Complex.slitPlane} := ⟨_, rfl⟩
    have memO : ∀ t, t ∈ O ↔ (t ∈ (R.A.chart j).target ∧
        (R.A.chart j).symm t ∈ R.U x ∩ R.U x' ∧
        (∀ k, R.lift x' ((R.A.chart j).symm t) ⟨k, i k⟩ ≠ 0) ∧
        ∀ k, r k ((R.A.chart j).symm t) / r k y ∈ Complex.slitPlane) := by
      intro t; rw [hOdef]; rfl
    have hO : IsOpen O := by
      rw [isOpen_iff_mem_nhds]
      intro t ht
      obtain ⟨htT, htU, htne, htsl⟩ := (memO t).1 ht
      have hDn : (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' (R.U x ∩ R.U x') ∈ 𝓝 t :=
        hD.mem_nhds ⟨htT, htU⟩
      have hca : ∀ (z0 : R.X) (p : (k : κ) × ρ k), (R.A.chart j).symm t ∈ R.U z0 →
          ContinuousAt (fun s => R.lift z0 ((R.A.chart j).symm s) p) t :=
        fun z0 p hz => (hol z0 p j t htT hz).continuousAt
      have e1 : ∀ᶠ s in 𝓝 t, ∀ k, R.lift x' ((R.A.chart j).symm s) ⟨k, i k⟩ ≠ 0 := by
        rw [Filter.eventually_all]
        intro k
        exact (hca x' _ htU.2).eventually_ne (htne k)
      have e2 : ∀ᶠ s in 𝓝 t, ∀ k, r k ((R.A.chart j).symm s) / r k y ∈ Complex.slitPlane := by
        rw [Filter.eventually_all]
        intro k
        have hc0 : ContinuousAt (fun s => r k ((R.A.chart j).symm s)) t := by
          simp only [hr]
          exact (hca x _ htU.1).div (hca x' _ htU.2) (htne k)
        have hc : ContinuousAt (fun s => r k ((R.A.chart j).symm s) / r k y) t :=
          hc0.div_const _
        exact hc.preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds (htsl k))
      filter_upwards [hDn, e1, e2] with s hs1 hs2 hs3
      exact (memO s).2 ⟨hs1.1, hs1.2, hs2, hs3⟩
    have hWopen : IsOpen ((R.A.chart j).source ∩ (R.A.chart j) ⁻¹' O) :=
      (R.A.chart j).isOpen_inter_preimage hO
    have hsy : (R.A.chart j).symm ((R.A.chart j) y) = y := (R.A.chart j).left_inv hj
    have hyW : y ∈ (R.A.chart j).source ∩ (R.A.chart j) ⁻¹' O := by
      refine ⟨hj, (memO _).2 ?_⟩
      rw [hsy]
      refine ⟨(R.A.chart j).map_source hj, ⟨hyU, hyU'⟩, hi, fun k => ?_⟩
      rw [div_self (hry k)]
      exact Complex.one_mem_slitPlane
    have condW : ∀ z ∈ (R.A.chart j).source ∩ (R.A.chart j) ⁻¹' O, z ∈ R.U x ∧ z ∈ R.U x' ∧
        (∀ k, R.lift x' z ⟨k, i k⟩ ≠ 0) ∧ ∀ k, r k z / r k y ∈ Complex.slitPlane := by
      intro z hz
      have h2 := (memO ((R.A.chart j) z)).1 hz.2
      rw [(R.A.chart j).left_inv hz.1] at h2
      exact ⟨h2.2.1.1, h2.2.1.2, h2.2.2.1, h2.2.2.2⟩
    refine ⟨(R.A.chart j).source ∩ (R.A.chart j) ⁻¹' O, hWopen, hyW,
      fun z => (∑ k, ((A.a k : ℝ) : ℂ) * Complex.log (r k z / r k y)) +
        ((∑ k, (A.a k : ℝ) * Real.log ‖r k y‖ : ℝ) : ℂ), ?_, ?_⟩
    · intro j' t ht
      obtain ⟨hUx, hUx', hne, hsl⟩ := condW _ ht.2
      have hra : ∀ k, AnalyticAt ℂ (fun s => r k ((R.A.chart j').symm s)) t := by
        intro k
        simp only [hr]
        exact (hol x _ j' t ht.1 hUx).div (hol x' _ j' t ht.1 hUx') (hne k)
      show AnalyticAt ℂ (fun s => (∑ k, ((A.a k : ℝ) : ℂ) *
          Complex.log (r k ((R.A.chart j').symm s) / r k y)) +
        ((∑ k, (A.a k : ℝ) * Real.log ‖r k y‖ : ℝ) : ℂ)) t
      refine AnalyticAt.add ?_ analyticAt_const
      have hs : ∀ k ∈ (Finset.univ : Finset κ), AnalyticAt ℂ (fun s => ((A.a k : ℝ) : ℂ) *
          Complex.log (r k ((R.A.chart j').symm s) / r k y)) t :=
        fun k _ => analyticAt_const.mul (((hra k).div analyticAt_const (hry k)).clog (hsl k))
      have h3 := Finset.analyticAt_sum Finset.univ hs
      rw [Finset.sum_fn] at h3
      exact h3
    · intro z hz
      obtain ⟨hUx, hUx', hne, -⟩ := condW z hz.1.1
      obtain ⟨cz, hcz, hlz⟩ := R.compat x x' z ⟨hUx, hUx'⟩
      have hrz : ∀ k, r k z = cz k := by
        intro k
        rw [hr]
        have h1 := congrFun hlz ⟨k, i k⟩
        rw [h1]
        exact mul_div_cancel_right₀ _ (hne k)
      have hhz : A.h (R.lift x z) = (∏ k, ‖cz k‖ ^ A.a k) * A.h (R.lift x' z) := by
        rw [hlz]; exact A.smul cz _ hcz
      have hhpos : 0 < A.h (R.lift x' z) := A.pos _ (memNZ x' z hUx')
      have hczn : ∀ k, ‖cz k‖ ≠ 0 := fun k => norm_ne_zero_iff.2 (hcz k)
      have hryn : ∀ k, ‖r k y‖ ≠ 0 := fun k => norm_ne_zero_iff.2 (hry k)
      have lhs : (Real.log (A.h (R.lift x z)) + c) - (Real.log (A.h (R.lift x' z)) + c) =
          ∑ k, (A.a k : ℝ) * Real.log ‖cz k‖ := by
        rw [hhz, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hczn k))
          hhpos.ne', Real.log_prod (fun k _ => zpow_ne_zero _ (hczn k))]
        simp only [Real.log_zpow]
        ring
      show (Real.log (A.h (R.lift x z)) + c) - (Real.log (A.h (R.lift x' z)) + c) =
        ((∑ k, ((A.a k : ℝ) : ℂ) * Complex.log (r k z / r k y)) +
          ((∑ k, (A.a k : ℝ) * Real.log ‖r k y‖ : ℝ) : ℂ)).re
      rw [lhs]
      simp only [Complex.add_re, Complex.re_sum, Complex.re_ofReal_mul, Complex.ofReal_re,
        Complex.log_re, norm_div, hrz]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Real.log_div (hczn k) (hryn k)]
      ring

theorem isPotential_secPot : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), ∀ c : ℝ, IsPotential RW.A (secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL c
  have hS : ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm (potA M τ a k₀) := by
    unfold GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.potA
    exact GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm _ _ _
  exact isPotential_secPot_of_isSmoothHerm RW (potA M τ a k₀) hS V _ _ (fun x => (hL x).2.2.2.2.1) c

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end
end
