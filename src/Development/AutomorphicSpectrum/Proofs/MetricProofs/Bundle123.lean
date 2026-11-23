module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle038
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle108
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle089
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle115
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle097
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle082
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle109
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle112
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle100
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameChangeUnderFieldMap
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle101
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle111
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle113
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle102
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle114
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle037
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle088

@[expose] public section

section

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)


theorem _root_.GlobalTheory.T.ringKrullDim_chartComponents : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k),
    IsCxVar Q e → ∀ J ∈ chartComponents (conePts Q) σ i,
      ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartComponents_dim | exact GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartComponents_dim | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartComponents_dim <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph.StepExpr

section Minors

variable {R S : Type} [CommRing R] [CommRing S] {N : ℕ}

theorem minor_map (f : R →+* S) (A : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) :
    minorIJ (A.map f) I J = f (minorIJ A I J) := by
  unfold minorIJ
  split_ifs with e
  · rw [RingHom.map_det]; rfl
  · rw [map_zero]

theorem minor_one_self (I : Finset (Fin N)) : minorIJ (1 : Matrix (Fin N) (Fin N) R) I I = 1 := by
  unfold minorIJ
  rw [dite_eq_left rfl, Matrix.submatrix_one _ (I.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem detFac_one' (j : ℕ) (i : Fin N) : detFac j i (1 : Matrix (Fin N) (Fin N) R) = 1 := by
  simp [detFac, minor_one_self]

theorem stepCols_ne_empty (j : ℕ) (i : Fin N) : stepCols N j i ≠ ∅ := by
  have hi := i.2
  apply Finset.Nonempty.ne_empty
  by_cases h : (i : ℕ) + 1 ≤ j
  · exact ⟨⟨N - j, by omega⟩, by simp [stepCols, h]; omega⟩
  · exact ⟨⟨0, by omega⟩, by simp [stepCols, h]; omega⟩

theorem detFac_ne_zero' {E : Type} [Field E] {j : ℕ} (hj : j ≤ N) (i : Fin N) {T : Matrix (Fin N) (Fin N) E}
    (hT : IsBlockDiag j T) (hd : T.det ≠ 0) : detFac j i T ≠ 0 := by
  have h := ((GlobalTheory.T.block_diagonal_minor_vanishing E N j i hj).2.2.2 T T⁻¹ hT (hT.inv (isUnit_iff_ne_zero.2 hd))).2
  rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd), detFac_one'] at h
  intro h0
  rw [h0, zero_mul] at h
  exact one_ne_zero h

theorem det_map_ne {A B : Type} [Field A] [Field B] (f : A →+* B) {T : Matrix (Fin N) (Fin N) A} (hd : T.det ≠ 0) :
    (T.map f).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero f).2 hd

theorem inv_map' {A B : Type} [Field A] [Field B] (f : A →+* B) {T : Matrix (Fin N) (Fin N) A} (hd : T.det ≠ 0) :
    (T⁻¹).map f = (T.map f)⁻¹ := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd)]
  exact Matrix.map_one _ (map_zero f) (map_one f)

end Minors

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem flag_in_frame_blockDiag {E : Type} [Field E] {T g : Matrix (Fin N) (Fin N) E}
    (hT : IsBlockDiag j T) (hd : T.det ≠ 0) (hg : IsBlockDiag j g) : IsBlockDiag j (T⁻¹ * g) :=
  (hT.inv (isUnit_iff_ne_zero.2 hd)).mul hg

theorem read_minor (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (hF : M.IsFrame F)
    (p : Ψ × Fin N) (k : K) (hk : M.blk p = some k) (I' : Finset (Fin N)) (hI' : IsStepRows N j p.2 I') :
    detFac j p.2 ((F.T p.1).map (algebraMap M.Ω Φ)) *
        ∑ m : ι k, algebraMap M.Ω Φ (F.u' I' ⟨k, m⟩) * y ⟨k, m⟩ =
      algebraMap M.Ω Φ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') *
        minorIJ (((F.T p.1).map (algebraMap M.Ω Φ))⁻¹ * M.g p.1) I' (stepCols N j p.2) := by
  set α : M.Ω →+* Φ := algebraMap M.Ω Φ with hα
  set T := (F.T p.1).map α with hTdef
  have hdet : T.det ≠ 0 := det_map_ne α (hF.1 p.1).2
  have hTb : IsBlockDiag j T := (hF.1 p.1).1.map α
  set h := T⁻¹ * M.g p.1 with hh
  have hb : IsBlockDiag j h := flag_in_frame_blockDiag hTb hdet (M.g_block p.1)
  have hTh : T * h = M.g p.1 := by
    rw [hh, Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 hdet)]
  have hy : ∀ m : ι k, detFac j p.2 T * y ⟨k, m⟩ =
      α (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') * ∑ I, α (F.u ⟨k, m⟩ I) * minorIJ h I (stepCols N j p.2) := fun m => by
    have := GlobalTheory.T.block_minor_sum_frame_identity K ι Φ y Ψ N j M Φ α F hF p k hk m h hb
    rw [← hTdef, hTh] at this
    rw [M.y_step p k hk m]
    exact this
  have hv : ∀ I, ¬ IsStepRows N j p.2 I → minorIJ h I (stepCols N j p.2) = 0 := fun I hI =>
    ((GlobalTheory.T.block_diagonal_minor_vanishing Φ N j p.2 M.j_le).2.1 h I hb hI).resolve_right (stepCols_ne_empty j p.2)
  calc detFac j p.2 T * ∑ m : ι k, α (F.u' I' ⟨k, m⟩) * y ⟨k, m⟩
      = ∑ m : ι k, α (F.u' I' ⟨k, m⟩) * (detFac j p.2 T * y ⟨k, m⟩) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring
    _ = α (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') * ∑ I, (∑ m : ι k, α (F.u' I' ⟨k, m⟩) * α (F.u ⟨k, m⟩ I)) *
          minorIJ h I (stepCols N j p.2) := by
        simp only [hy, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun m _ => by ring
    _ = _ := by
        congr 1
        have hs : ∀ I, IsStepRows N j p.2 I → ∑ m : ι k, α (F.u' I' ⟨k, m⟩) * α (F.u ⟨k, m⟩ I) = if I' = I then 1 else 0 := fun I hI => by
          have := hF.2.2.1 p k hk I' I hI' hI

          simp only [← map_mul, ← map_sum, this]
          split_ifs <;> simp
        rw [Finset.sum_eq_single I' (fun I _ hne => ?_) (by simp), hs I' hI', if_pos rfl, one_mul]
        by_cases hI : IsStepRows N j p.2 I
        · rw [hs I hI, if_neg (Ne.symm hne), zero_mul]
        · rw [hv I hI, mul_zero]

theorem transPt_eq_smul_sum : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk), M'.IsFrame F' → M.IsFrame F → (∀ k, M'.x ⟨k, F'.c k⟩ ≠ 0) → (∀ k, M.x ⟨k, F.c k⟩ ≠ 0) → ∀ (p : Ψ × Fin N) (k : K) (k' : K'), M.blk p = some k → M'.blk p = some k' → ∃ c : Φ', c ≠ 0 ∧ ∀ m : ι k, transPt Cv ⟨k, m⟩ = c * ∑ m' : ι' k', algebraMap M'.Ω Φ' (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) * y' ⟨k', m'⟩ := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv F' F hF' hF hc' hc p k k' hk hk'
  set α : M'.Ω →+* Φ' := algebraMap M'.Ω Φ' with hα
  set ρ : M.Ω →+* Φ' := α.comp Cv.φ with hρ
  set T' := (F'.T p.1).map α with hT'
  set T := (F.T p.1).map ρ with hT
  have hdetφ : ((F.T p.1).map Cv.φ).det ≠ 0 := det_map_ne Cv.φ (hF.1 p.1).2
  have hdet' : T'.det ≠ 0 := det_map_ne α (hF'.1 p.1).2
  have hdet : T.det ≠ 0 := det_map_ne ρ (hF.1 p.1).2
  have hTb' : IsBlockDiag j T' := (hF'.1 p.1).1.map α
  have hTb : IsBlockDiag j T := (hF.1 p.1).1.map ρ
  set h' := T'⁻¹ * M'.g p.1 with hh'
  set h₀ := T⁻¹ * M'.g p.1 with hh₀
  have hb' : IsBlockDiag j h' := flag_in_frame_blockDiag hTb' hdet' (M'.g_block p.1)
  have hb₀ : IsBlockDiag j h₀ := flag_in_frame_blockDiag hTb hdet (M'.g_block p.1)
  have hTh₀ : T * h₀ = M'.g p.1 := by
    rw [hh₀, Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 hdet)]
  have hμ' : α (∏ k'', M'.x ⟨k'', F'.c k''⟩ ^ M'.b p k'') ≠ 0 :=
    (map_ne_zero α).2 (Finset.prod_ne_zero_iff.2 fun k'' _ => zpow_ne_zero _ (hc' k''))
  have hμ : ρ (∏ k'', M.x ⟨k'', F.c k''⟩ ^ M.b p k'') ≠ 0 :=
    (map_ne_zero ρ).2 (Finset.prod_ne_zero_iff.2 fun k'' _ => zpow_ne_zero _ (hc k''))
  have hd' : detFac j p.2 T' ≠ 0 := detFac_ne_zero' M'.j_le p.2 hTb' hdet'
  have hd : detFac j p.2 T ≠ 0 := detFac_ne_zero' M.j_le p.2 hTb hdet
  set μ' := α (∏ k'', M'.x ⟨k'', F'.c k''⟩ ^ M'.b p k'') with hμ'def
  set μ := ρ (∏ k'', M.x ⟨k'', F.c k''⟩ ^ M.b p k'') with hμdef
  set d' := detFac j p.2 T' with hd'def
  set d := detFac j p.2 T with hddef
  have hread : ∀ I', IsStepRows N j p.2 I' → minorIJ h' I' (stepCols N j p.2) =
      d' / μ' * ∑ m' : ι' k', α (F'.u' I' ⟨k', m'⟩) * y' ⟨k', m'⟩ := fun I' hI' => by
    have := read_minor M' F' hF' p k' hk' I' hI'
    rw [div_mul_eq_mul_div, eq_div_iff hμ', mul_comm]
    exact this.symm
  have hv : ∀ I, ¬ IsStepRows N j p.2 I → minorIJ h' I (stepCols N j p.2) = 0 := fun I hI =>
    ((GlobalTheory.T.block_diagonal_minor_vanishing Φ' N j p.2 M'.j_le).2.1 h' I hb' hI).resolve_right (stepCols_ne_empty j p.2)
  have hmat : h₀ = (trMat Cv F' F p.1).map α * h' := by
    have e : ((F.T p.1).map Cv.φ).map α = T := Matrix.ext fun _ _ => rfl
    rw [trMat, Matrix.map_mul, inv_map' α hdetφ, e, ← hT', hh', Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 hdet')]
  have e3 : ∀ I, minorIJ h₀ I (stepCols N j p.2) =
      ∑ I' ∈ Finset.univ.filter (IsStepRows N j p.2),
        α (minorIJ (trMat Cv F' F p.1) I I') * minorIJ h' I' (stepCols N j p.2) := fun I => by
    rw [hmat, (GlobalTheory.T.block_diagonal_minor_vanishing Φ' N j p.2 M'.j_le).1]
    simp only [minor_map]
    refine (Finset.sum_subset (Finset.filter_subset _ _) fun I' _ hI' => ?_).symm
    rw [hv I' (by simpa using hI'), mul_zero]
  have e1 : ∀ m : ι k, d * transPt Cv ⟨k, m⟩ =
      μ * ∑ I, α (Cv.φ (F.u ⟨k, m⟩ I)) * minorIJ h₀ I (stepCols N j p.2) := fun m => by
    have := GlobalTheory.T.block_minor_sum_frame_identity K ι Φ y Ψ N j M Φ' ρ F hF p k hk m h₀ hb₀
    rw [← hT, hTh₀] at this
    rw [transPt_step Cv p k hk m]
    exact this
  refine ⟨μ / d * (d' / μ'), mul_ne_zero (div_ne_zero hμ hd) (div_ne_zero hd' hμ'), fun m => ?_⟩
  have htr : transPt Cv ⟨k, m⟩ = μ / d * ∑ I, α (Cv.φ (F.u ⟨k, m⟩ I)) * minorIJ h₀ I (stepCols N j p.2) := by
    rw [div_mul_eq_mul_div, eq_div_iff hd, mul_comm]
    exact e1 m
  have hR : ∑ m' : ι' k', α (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) * y' ⟨k', m'⟩ =
      ∑ I, ∑ I' ∈ Finset.univ.filter (IsStepRows N j p.2),
        α (Cv.φ (F.u ⟨k, m⟩ I)) * α (minorIJ (trMat Cv F' F p.1) I I') *
          ∑ m' : ι' k', α (F'.u' I' ⟨k', m'⟩) * y' ⟨k', m'⟩ := by

    simp only [coE, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun I' _ => Finset.sum_congr rfl fun m' _ => by ring
  rw [htr, mul_assoc, hR]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [e3 I, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I' hI' => ?_
  rw [hread I' (Finset.mem_filter.1 hI').2]
  ring

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph.StepExpr
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem _root_.GlobalTheory.T.flag_cover_frames_at_base_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (zb : (Σ k, baseIdx ι' M'.blk k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk), zb ∈ mcPts (mCoordIdeal M'.x) → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal zb) → M.GoodAt F (mCoordIdeal (zb ∘ Cv.v)) → ∀ (p : Ψ × Fin N) (q : Σ k, ι k) (r : Σ k, ι' k), RegAt M'.x (mCoordIdeal zb) (coE Cv F' F p q r) ∧ valAt M'.x (coE Cv F' F p q r) zb = ∑ I, ∑ I' ∈ Finset.univ.filter (IsStepRows N j p.2), valAt M.x (F.u q I) (zb ∘ Cv.v) * minorIJ (Cv.trans F' F zb p.1) I I' * valAt M'.x (F'.u' I' r) zb := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.coE_regAt_valAt | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.coE_regAt_valAt | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.coE_regAt_valAt <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem transPt_block_base : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (z₁ : (Σ k, ι' k) → ℂ) (z₀ : (Σ k, ι k) → ℂ) (kb : NonPluckerBlocks M.blk), z₁ ∈ mcPts (mCoordIdeal y') → SameOrbit (basePart M.blk z₀) (basePart M'.blk z₁ ∘ Cv.v) → ∃ (e : Φ') (s : ι kb.1 → Φ') (t : ℂ), e ≠ 0 ∧ t ≠ 0 ∧ ∀ i, transPt Cv ⟨kb.1, i⟩ = e * s i ∧ IsValueAt y' (s i) z₁ (t * z₀ ⟨kb.1, i⟩) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv z₁ z₀ kb hz hO
  obtain ⟨c₀, hc₀, e₀⟩ := hO
  obtain ⟨c, hc⟩ := hz.1 (Cv.κ kb).1
  obtain ⟨hy, hv⟩ := GlobalTheory.T.coordinate_ratio_value_at_point K' ι' Φ' y' z₁ (Cv.κ kb).1 c hz hc
  have hw : ∀ i : ι kb.1, ∃ m : ι' (Cv.κ kb).1, Cv.v ⟨kb, i⟩ = ⟨Cv.κ kb, m⟩ := fun i => by
    have h1 := Cv.block.2.2.1 ⟨kb, i⟩
    rcases hq : Cv.v ⟨kb, i⟩ with ⟨k, m⟩
    rw [hq] at h1
    obtain rfl : k = Cv.κ kb := h1
    exact ⟨m, rfl⟩
  choose w hw using hw
  refine ⟨y' ⟨(Cv.κ kb).1, c⟩, fun i => y' ⟨(Cv.κ kb).1, w i⟩ / y' ⟨(Cv.κ kb).1, c⟩,
    (c₀ kb * z₁ ⟨(Cv.κ kb).1, c⟩)⁻¹, hy, inv_ne_zero (mul_ne_zero (hc₀ kb) hc), fun i => ⟨?_, ?_⟩⟩
  · rw [mul_div_cancel₀ _ hy]
    have h1 := transPt_base Cv (⟨kb, i⟩ : Σ k, baseIdx ι M.blk k)
    rw [← Cv.x_eq, hw i, ← M'.y_base] at h1
    exact h1
  · have h2 : z₀ ⟨kb.1, i⟩ = c₀ kb * z₁ ⟨(Cv.κ kb).1, w i⟩ := by
      have h3 := congrFun e₀ (⟨kb, i⟩ : Σ k, baseIdx ι M.blk k)
      simp only [Function.comp, hw i] at h3
      exact h3
    have h4 : (c₀ kb * z₁ ⟨(Cv.κ kb).1, c⟩)⁻¹ * z₀ ⟨kb.1, i⟩ =
        (z₁ ⟨(Cv.κ kb).1, c⟩)⁻¹ * z₁ ⟨(Cv.κ kb).1, w i⟩ := by
      rw [h2]
      have := hc₀ kb
      field_simp
    rw [h4]
    exact hv (w i)

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem plk_flagPt : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (p : Ψ × Fin N) (k : K), M.IsFrame F → b ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal b) → (∀ τ', IsBlockDiag j (h τ')) → M.blk p = some k → FC.plk M F b (FC.flagPt M F b h) p = minorIJ (h p.1) (stepCols N j p.2) (stepCols N j p.2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F b h p k hF hb hG hh hp
  have hCB := GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le
  have hoff : ∀ J, ¬ IsStepRows N j p.2 J → minorIJ (h p.1) J (stepCols N j p.2) = 0 := fun J hJ =>
    (hCB.2.1 (h p.1) J (hh p.1) hJ).resolve_right (CovMap.LocImg.stepCols_ne_empty M.j_le)
  have hI₀ : IsStepRows N j p.2 (stepCols N j p.2) := CovMap.LocImg.FV.isStepRows_stepCols p.2
  have hdelta : ∀ J, IsStepRows N j p.2 J →
      ∑ m : ι k, valAt M.x (F.u' (stepCols N j p.2) ⟨k, m⟩) b * valAt M.x (F.u ⟨k, m⟩ J) b =
        if stepCols N j p.2 = J then 1 else 0 := by
    intro J hJ
    have hu' := fun m : ι k => (hG.2.1 ⟨k, m⟩ (stepCols N j p.2)).2
    have hu := fun m : ι k => (hG.2.1 ⟨k, m⟩ J).1
    have e1 := (CovMap.LocImg.reg_sum hb Finset.univ (fun m : ι k => F.u' (stepCols N j p.2) ⟨k, m⟩ * F.u ⟨k, m⟩ J)
      fun m _ => (CovMap.LocImg.reg_mul hb (hu' m) (hu m)).1).2
    rw [hF.2.2.1 p k hp _ J hI₀ hJ] at e1
    rw [Finset.sum_congr rfl fun m _ => ((CovMap.LocImg.reg_mul hb (hu' m) (hu m)).2).symm, ← e1]
    split_ifs
    · exact map_one (CovMap.LocImg.regVal M.x hb)
    · exact map_zero (CovMap.LocImg.regVal M.x hb)
  have e1 : FC.plk M F b (FC.flagPt M F b h) p =
      ∑ J, (∑ m : ι k, valAt M.x (F.u' (stepCols N j p.2) ⟨k, m⟩) b * valAt M.x (F.u ⟨k, m⟩ J) b) *
        minorIJ (h p.1) J (stepCols N j p.2) := by
    simp only [FC.plk, hp, Option.elim_some]
    simp_rw [flagPt_step M F b h hp, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [e1, Finset.sum_eq_single (stepCols N j p.2)]
  · rw [hdelta _ hI₀, if_pos rfl, one_mul]
  · intro J _ hne
    by_cases hJ : IsStepRows N j p.2 J
    · rw [hdelta J hJ, if_neg hne.symm, zero_mul]
    · rw [hoff J hJ, mul_zero]
  · simp

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Coord

theorem nat_card_cIdx (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (τ : Ψ) (ca cb : Fin N) (hj : j ≤ N)
    (hab : ca < cb) (hblk : (cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) :
    Nat.card (FC.CIdx Ψ N j τ ca cb) + 1 = Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) := by
  classical
  obtain ⟨q0, hq0⟩ : ∃ q0 : LowIdx Ψ N j, q0.1 = (τ, cb, ca) := ⟨⟨(τ, cb, ca), hab, hblk⟩, rfl⟩
  have e : FC.CIdx Ψ N j τ ca cb ≃ {q : LowIdx Ψ N j // q ≠ q0} :=
    Equiv.subtypeEquivRight (fun q => by
      show q.1 ≠ (τ, cb, ca) ↔ q ≠ q0
      rw [← hq0]
      exact not_congr Subtype.ext_iff.symm)
  have h1 : Nat.card (Option {q : LowIdx Ψ N j // q ≠ q0}) = Nat.card (LowIdx Ψ N j) :=
    Nat.card_congr (Equiv.optionSubtypeNe q0)
  rw [Nat.card_eq_fintype_card, Fintype.card_option] at h1
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, h1, Nat.card_eq_fintype_card]
  convert GlobalTheory.CompanionTheory.Ar.PB.WMan.ChartCount.card_lowIdx Ψ N j hj

theorem nonempty_equiv_cIdx : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j n d : ℕ) (τ : Ψ) (ca cb : Fin N), j ≤ N →
    ca < cb → ((cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) →
    d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) →
    Nonempty (Fin d ≃ Fin n ⊕ FC.CIdx Ψ N j τ ca cb) := by
  intro Ψ _ _ N j n d τ ca cb hj hab hblk hd
  have h := nat_card_cIdx Ψ N j τ ca cb hj hab hblk
  apply Finite.card_eq.1
  rw [Nat.card_sum, Nat.card_eq_fintype_card (α := Fin d), Fintype.card_fin,
    Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]
  omega

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Coord
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem _root_.GlobalTheory.T.lower_unipotent_family_analytic : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (τ : Ψ) (ca cb : Fin N), ca < cb → ((cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) → (∀ (c : FC.CIdx Ψ N j τ ca cb → ℂ) τ', IsBlockDiag j (FC.Lc τ ca cb c τ') ∧ (FC.Lc τ ca cb c τ').det ≠ 0) ∧ (∀ τ' r s, AnalyticOnNhd ℂ (fun c : FC.CIdx Ψ N j τ ca cb → ℂ => FC.Lc τ ca cb c τ' r s) Set.univ) ∧ (∀ L : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (L τ') ∧ IsLowerUni (L τ')) → ∃ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ), FC.Lca τ ca cb c a = L) ∧ (∀ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ) τ', IsBlockDiag j (FC.Lca τ ca cb c a τ') ∧ IsLowerUni (FC.Lca τ ca cb c a τ')) ∧ ∀ (c c' : FC.CIdx Ψ N j τ ca cb → ℂ) (a a' : ℂ), FC.Lca τ ca cb c a = FC.Lca τ ca cb c' a' → c = c' ∧ a = a' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.LcFam.lc_main | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.LcFam.lc_main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.LcFam.lc_main <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem _root_.GlobalTheory.T.plucker_nonvanishing_orbit_invariant : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ) (z z' : (Σ k, ι k) → ℂ) (p : Ψ × Fin N), SameOrbit z z' → (FC.plk M F b z p ≠ 0 ↔ FC.plk M F b z' p ≠ 0) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.plk_ne_zero_iff_of_sameOrbit | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.plk_ne_zero_iff_of_sameOrbit | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.plk_ne_zero_iff_of_sameOrbit <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem _root_.GlobalTheory.T.flag_point_triangular_change_orbit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ) (h B : Ψ → Matrix (Fin N) (Fin N) ℂ), (∀ τ', IsBlockDiag j (B τ') ∧ (B τ').BlockTriangular id ∧ (B τ').det ≠ 0) → SameOrbit (FC.flagPt M F b fun τ' => h τ' * B τ') (FC.flagPt M F b h) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.sameOrbit_flagPt_mul | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.sameOrbit_flagPt_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.sameOrbit_flagPt_mul <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem _root_.GlobalTheory.T.two_point_fibre_chart_second : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ w ∈ Un, (Gn w).PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.gramPlane_posDef | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.gramPlane_posDef | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.gramPlane_posDef <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem _root_.GlobalTheory.T.elementary_factor_properties : ∀ (N j : ℕ) (a b ca cb : Fin N) (t : ℂ), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) ∧ (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).det = 1 ∧ (∀ h : Matrix (Fin N) (Fin N) ℂ, ∀ i, facOf N j a (h * (1 + Matrix.single cb ca t)) i = facOf N j a h i) ∧ ∀ G h : Matrix (Fin N) (Fin N) ℂ, ∀ i, i ≠ a → blockPot j i G (h * (1 + Matrix.single cb ca t)) = blockPot j i G h := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.Shear.shear_main | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.Shear.shear_main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.Shear.shear_main <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

theorem isSection_diagSec : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), M.blk (τ, a) = some k₀ → IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ c : ℝ, IsSection RW.A (secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) (diagSec ψ i₀ u) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL hblk hW c
  refine ⟨fun x => ?_, fun x x' w hw => ?_⟩
  · obtain ⟨⟨F, H, hC⟩, -, -, hsrc, -, hu, -⟩ := hL x
    intro l z hz
    have hz' : z ∈ (RW.A.chart l).target ∩ (RW.A.chart l).symm ⁻¹' (ψ x).source :=
      ⟨hz.1, hsrc hz.2⟩
    have h1 : AnalyticAt ℂ (u x ∘ (RW.A.chart l).symm) z := hu l z hz
    have h2 : AnalyticAt ℂ ((ψ x) ∘ (RW.A.chart l).symm) z := (hC.1 l).1 z hz'
    have h3 : AnalyticAt ℂ (fun w => ((ψ x) ∘ (RW.A.chart l).symm) w (i₀ x)) z :=
      analyticAt_pi_iff.1 h2 (i₀ x)
    exact h1.mul h3
  · have hx : 0 < (potA M τ a k₀).h (RW.lift x w) :=
      (potA M τ a k₀).pos _ (RW.mem x w ((hL x).2.2.2.2.1 hw.1)).1
    have hx' : 0 < (potA M τ a k₀).h (RW.lift x' w) :=
      (potA M τ a k₀).pos _ (RW.mem x' w ((hL x').2.2.2.2.1 hw.2)).1
    have hg := locSec_norm_eq K ι Φ y Ψ N j M n e Rb τ a k₀ ca cb RW pr x x' (ψ x) (ψ x') (kb x) (kb x') (σ x) (σ x')
      (i₀ x) (i₀ x') (V x) (V x') (u x) (u x') hblk hW (hL x) (hL x') w hw
    have key : ∀ (s h : ℝ), 0 < h → s * Real.exp (-(Real.log h + c)) = s / h * Real.exp (-c) := by
      intro s h hh
      rw [neg_add, Real.exp_add, Real.exp_neg (Real.log h), Real.exp_log hh, div_eq_mul_inv, mul_assoc]
    show ‖u x w * ψ x w (i₀ x)‖ * Real.exp (-(Real.log ((potA M τ a k₀).h (RW.lift x w)) + c)) =
      ‖u x' w * ψ x' w (i₀ x')‖ * Real.exp (-(Real.log ((potA M τ a k₀).h (RW.lift x' w)) + c))
    rw [key _ _ hx, key _ _ hx', hg]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end
end
