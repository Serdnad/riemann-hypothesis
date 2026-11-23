module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle089
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle082
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle115
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle122
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle096
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle101
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle141
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle134
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle121
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle079
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle075
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle084
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle102
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle103
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle113
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle126
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle142
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle003
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle143
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle016
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle144
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartLocalAnalyticTrivialization
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle078
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle009
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph GlobalTheory.CompanionTheory.Ar.PB.CovGraph.BStep

theorem _root_.GlobalTheory.T.flag_cover_frames_lift_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (z₁ : (Σ k, ι' k) → ℂ) (z₀ : (Σ k, ι k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (p : Ψ × Fin N) (k : K), z₁ ∈ mcPts (mCoordIdeal y') → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal (basePart M'.blk z₁)) → M.GoodAt F (mCoordIdeal (basePart M'.blk z₁ ∘ Cv.v)) → M'.IsFlagOf F' z₁ h → M.IsFlagOf F z₀ (fun τ => Cv.trans F' F (basePart M'.blk z₁) τ * h τ) → SameOrbit (basePart M.blk z₀) (basePart M'.blk z₁ ∘ Cv.v) → M.blk p = some k → ∃ (e : Φ') (s : ι k → Φ') (t : ℂ), e ≠ 0 ∧ t ≠ 0 ∧ ∀ m, transPt Cv ⟨k, m⟩ = e * s m ∧ IsValueAt y' (s m) z₁ (t * z₀ ⟨k, m⟩) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv z₁ z₀ F' F h p k hz₁ hF' hF hG' hG hfl' hfl horb hp
  set zb := basePart M'.blk z₁ with hzbdef
  have hzb : zb ∈ mcPts (mCoordIdeal M'.x) := (GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M').1 z₁ hz₁
  have hzv := GlobalTheory.T.flag_cover_base_point_maps_to_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv zb hzb
  have hstep : IsProperStep N j p.2 := by
    by_contra hn
    rw [(M.blk_none p).2 hn] at hp
    exact absurd hp (by simp)
  obtain ⟨k', hk'⟩ : ∃ k', M'.blk p = some k' :=
    Option.ne_none_iff_exists'.1 fun e => (M'.blk_none p).1 e hstep
  obtain ⟨c', hc'⟩ := hz₁.1 k'
  obtain ⟨hy0, hratio⟩ := GlobalTheory.T.coordinate_ratio_value_at_point K' ι' Φ' y' z₁ k' c' hz₁ hc'
  have ch' : ∀ k, M'.x ⟨k, F'.c k⟩ ≠ 0 := fun k => coord_ne hzb (hG'.1 k)
  have ch : ∀ k, M.x ⟨k, F.c k⟩ ≠ 0 := fun k => coord_ne hzv (hG.1 k)
  obtain ⟨c, hc0, htr⟩ :=
    GlobalTheory.T.flag_cover_frames_pullback K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv F' F hF' hF ch' ch p k k' hp hk'
  obtain ⟨a', ha', hz1⟩ := hfl'.2.2 p k' hk'
  obtain ⟨a, ha, hz0⟩ := hfl.2.2 p k hp
  have hcoeff (q : Σ k, ι k) (r : Σ k, ι' k) :
      RegAt M'.x (mCoordIdeal zb) (coE Cv F' F p q r) ∧
        valAt M'.x (coE Cv F' F p q r) zb =
          ∑ I, ∑ I' ∈ Finset.univ.filter (IsStepRows N j p.2),
            valAt M.x (F.u q I) (zb ∘ Cv.v) * minorIJ (Cv.trans F' F zb p.1) I I' *
              valAt M'.x (F'.u' I' r) zb := by
    have hT : ∀ a b, RegAt M'.x (mCoordIdeal zb) (trMat Cv F' F p.1 a b) := fun a b =>
      (Cv.agree zb hzb F' F hF' hF hG' hG p.1 a b).1
    have hminor := CovMap.LocImg.reg_minor hzb hT
    have hxv : M'.x ∘ Cv.v = Cv.φ ∘ M.x := funext Cv.x_eq
    have hu (I : Finset (Fin N)) :
        RegAt M'.x (mCoordIdeal zb) (Cv.φ (F.u q I)) ∧
          valAt M'.x (Cv.φ (F.u q I)) zb = valAt M.x (F.u q I) (zb ∘ Cv.v) := by
      obtain ⟨d, g, h, hg, hh, hn, he⟩ := (hG.2.1 q I).1
      have hg' := RegPhi.isMultiHomog_rename_block Cv.block hg
      have hh' := RegPhi.isMultiHomog_rename_block Cv.block hh
      have hn' := RegPhi.rename_notMem Cv.block hn
      have hae (f : MRing (baseIdx ι M.blk)) :
          aeval M'.x (rename Cv.v f) = Cv.φ (aeval M.x f) := by
        rw [aeval_rename, hxv, RegPhi.aeval_comp_ringHom]
      have he' : aeval M'.x (rename Cv.v g) = Cv.φ (F.u q I) * aeval M'.x (rename Cv.v h) := by
        rw [hae, hae, he, map_mul]
      refine ⟨⟨_, _, _, hg', hh', hn', he'⟩, ?_⟩
      let value := eval (zb ∘ Cv.v) (map (Int.castRingHom ℂ) g) /
        eval (zb ∘ Cv.v) (map (Int.castRingHom ℂ) h)
      have hv : IsValueAt M.x (F.u q I) (zb ∘ Cv.v) value :=
        ⟨d, g, h, hg, hh, ValRing.aeval_ne_zero_of_notMem hzv hh hn, he,
          ValRing.eval_ne_zero_of_notMem hh hn, rfl⟩
      have hv' : IsValueAt M'.x (Cv.φ (F.u q I)) zb value := by
        refine ⟨_, _, _, hg', hh', ValRing.aeval_ne_zero_of_notMem hzb hh' hn', he',
          ValRing.eval_ne_zero_of_notMem hh' hn', ?_⟩
        rw [RegPhi.eval_rename_block, RegPhi.eval_rename_block]
      exact (valAt_eq hzb hv').trans (valAt_eq hzv hv).symm
    have hterm (I I' : Finset (Fin N)) :
        RegAt M'.x (mCoordIdeal zb) (Cv.φ (F.u q I) * minorIJ (trMat Cv F' F p.1) I I' * F'.u' I' r) ∧
          valAt M'.x (Cv.φ (F.u q I) * minorIJ (trMat Cv F' F p.1) I I' * F'.u' I' r) zb =
            valAt M.x (F.u q I) (zb ∘ Cv.v) * minorIJ (Cv.trans F' F zb p.1) I I' *
              valAt M'.x (F'.u' I' r) zb := by
      obtain ⟨hreg, hval⟩ := CovMap.LocImg.reg_mul hzb (hu I).1 (hminor I I').1
      obtain ⟨hreg', hval'⟩ := CovMap.LocImg.reg_mul hzb hreg (hG'.2.1 r I').2
      refine ⟨hreg', hval'.trans ?_⟩
      rw [hval, (hu I).2, (hminor I I').2]
      rfl
    have hin (I : Finset (Fin N)) := CovMap.LocImg.reg_sum hzb
      (Finset.univ.filter (IsStepRows N j p.2)) _ (fun I' _ => (hterm I I').1)
    have hout := CovMap.LocImg.reg_sum hzb Finset.univ _ (fun I _ => (hin I).1)
    refine ⟨hout.1, hout.2.trans (Finset.sum_congr rfl fun I _ => ?_)⟩
    rw [(hin I).2]
    exact Finset.sum_congr rfl fun I' _ => (hterm I I').2
  have hE (m : ι k) (m' : ι' k') := hcoeff ⟨k, m⟩ ⟨k', m'⟩
  have hmin := GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le
  have hne : stepCols N j p.2 ≠ ∅ := stepCols_ne p.2 M.j_le
  obtain ⟨cc, hcc, horbE⟩ := horb
  have hval : ∀ s, valAt M.x s (basePart M.blk z₀) = valAt M.x s (zb ∘ Cv.v) := fun s => by
    rw [horbE]
    exact ((StepW.TorusAct.main _ _ _ M.x (zb ∘ Cv.v) cc hcc).2 hzv).2 s
  have hμ : ∀ I, ¬ IsStepRows N j p.2 I → minorIJ (h p.1) I (stepCols N j p.2) = 0 := fun I hI =>
    (hmin.2.1 (h p.1) I (hfl'.2.1 p.1).1 hI).resolve_right hne
  have isValueAt_valAt (s : M'.Ω) (hs : RegAt M'.x (mCoordIdeal zb) s) :
      IsValueAt M'.x s zb (valAt M'.x s zb) := by
    obtain ⟨v, hv⟩ := ValRing.exists_isValueAt hzb hs
    rwa [valAt_eq hzb hv]
  have valAt_sum_mul {α : Type} (S : Finset α) (f g : α → M'.Ω)
      (hf : ∀ i ∈ S, RegAt M'.x (mCoordIdeal zb) (f i))
      (hg : ∀ i ∈ S, RegAt M'.x (mCoordIdeal zb) (g i)) :
      valAt M'.x (∑ i ∈ S, f i * g i) zb = ∑ i ∈ S, valAt M'.x (f i) zb * valAt M'.x (g i) zb :=
    valAt_eq hzb (isValueAt_sum S _ _ fun i hi =>
      isValueAt_mul (isValueAt_valAt (f i) (hf i hi)) (isValueAt_valAt (g i) (hg i hi)))
  have hAB : ∀ I I', IsStepRows N j p.2 I → IsStepRows N j p.2 I' →
      ∑ m, valAt M'.x (F'.u' I ⟨k', m⟩) zb * valAt M'.x (F'.u ⟨k', m⟩ I') zb =
        if I = I' then 1 else 0 := fun I I' hI hI' => by
    rw [← valAt_sum_mul Finset.univ _ _ (fun m _ => (hG'.2.1 ⟨k', m⟩ I).2)
      (fun m _ => (hG'.2.1 ⟨k', m⟩ I').1), hF'.2.2.1 p k' hk' I I' hI hI']
    have h3 := ValRing.regAt_valAt_ring _ _ _ M'.x zb hzb
    split_ifs
    · exact h3.2.2.2.1
    · exact h3.2.2.1
  have hread := read_minor (IsStepRows N j p.2) _ _ hAB _ hμ (fun m => z₁ ⟨k', m⟩) a' hz1
  have key : ∀ m, ∑ m', valAt M'.x (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) zb * z₁ ⟨k', m'⟩ =
      a' * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (zb ∘ Cv.v) *
        minorIJ (Cv.trans F' F zb p.1 * h p.1) I (stepCols N j p.2) := fun m => by
    simp only [fun m' => (hE m m').2, hmin.1]
    exact move_minor (IsStepRows N j p.2) _ (fun I => by simp) _ _ _ _ hμ _ a' hread
  have baseValue (s : M'.Ω) (hs : RegAt M'.x (mCoordIdeal zb) s) :
      IsValueAt y' (algebraMap M'.Ω Φ' s) z₁ (valAt M'.x s zb) := by
    obtain ⟨v, hv⟩ := GlobalTheory.CompanionTheory.Ar.PB.ValRing.exists_isValueAt hzb hs
    rw [GroundTheory.Heights₂.Heights.LowerBoundFree.valAt_eq hzb hv]
    obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := hv
    let f : (Σ k, baseIdx ι' M'.blk k) → (Σ k, ι' k) := fun q => ⟨q.1.1, q.2⟩
    have ha : ∀ p : MRing (baseIdx ι' M'.blk), aeval y' (rename f p) = algebraMap M'.Ω Φ' (aeval M'.x p) := fun p => by
      have e : y' ∘ f = algebraMap M'.Ω Φ' ∘ M'.x := funext M'.y_base
      rw [aeval_rename, e, aeval_algebraMap_apply]
    have hev : ∀ p : MRing (baseIdx ι' M'.blk), eval z₁ (map (Int.castRingHom ℂ) (rename f p)) =
        eval (basePart M'.blk z₁) (map (Int.castRingHom ℂ) p) := fun p => by
      rw [map_rename, eval_rename]
      rfl
    refine ⟨_, rename f g, rename f h, isMultiHomog_rename_base M'.blk hg, isMultiHomog_rename_base M'.blk hh, ?_, ?_, ?_, ?_⟩
    · rw [ha]
      exact (map_ne_zero _).2 hy
    · rw [ha, ha, heq, map_mul]
    · rw [hev]
      exact hz0
    · rw [hev, hev]
  refine ⟨c * y' ⟨k', c'⟩, fun m => ∑ m', algebraMap M'.Ω Φ' (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) *
    (y' ⟨k', m'⟩ / y' ⟨k', c'⟩), a' / (a * z₁ ⟨k', c'⟩), mul_ne_zero hc0 hy0,
    div_ne_zero ha' (mul_ne_zero ha hc'), fun m => ⟨?_, ?_⟩⟩
  · show transPt Cv ⟨k, m⟩ = c * y' ⟨k', c'⟩ * ∑ m', algebraMap M'.Ω Φ' (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) *
      (y' ⟨k', m'⟩ / y' ⟨k', c'⟩)
    rw [htr m, mul_assoc]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    field_simp
  · have hv := isValueAt_sum Finset.univ
      (fun m' => algebraMap M'.Ω Φ' (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) * (y' ⟨k', m'⟩ / y' ⟨k', c'⟩))
      (fun m' => valAt M'.x (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) zb * ((z₁ ⟨k', c'⟩)⁻¹ * z₁ ⟨k', m'⟩))
      fun m' _ => isValueAt_mul (baseValue _ (hE m m').1) (hratio m')
    have e : ∑ m', valAt M'.x (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) zb * ((z₁ ⟨k', c'⟩)⁻¹ * z₁ ⟨k', m'⟩) =
        a' / (a * z₁ ⟨k', c'⟩) * z₀ ⟨k, m⟩ := by
      have e1 : ∑ m', valAt M'.x (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) zb * ((z₁ ⟨k', c'⟩)⁻¹ * z₁ ⟨k', m'⟩) =
          (z₁ ⟨k', c'⟩)⁻¹ * ∑ m', valAt M'.x (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) zb * z₁ ⟨k', m'⟩ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m' _ => by ring
      rw [e1, key m, hz0 m]
      simp only [hval]
      field_simp
    rw [← e]
    exact hv
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.ExactStep

theorem prod_base_split {K : Type} [Fintype K] {σ : Type} (blk : σ → Option K) (p : σ) (k₀ : K)
    (hp : blk p = some k₀) (f : K → ℝ)
    (hf : ∀ k, (¬ ∀ p', blk p' ≠ some k) → k ≠ k₀ → f k = 1) :
    ∏ k, f k = (∏ k : NonPluckerBlocks blk, f k.1) * f k₀ := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ fun k => ∀ p', blk p' ≠ some k]
  congr 1
  · exact Finset.prod_subtype _ (by simp) f
  · refine Finset.prod_eq_single_of_mem k₀ ?_ ?_
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, fun e => e p hp⟩
    · intro k hk e
      exact hf k (Finset.mem_filter.1 hk).2 e

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (k₀ : K) (l : Fin BM.q) (x₀ : BM.Rb.X) (z : (Σ k, ι k) → ℂ) (I₀ : Finset (Fin N)) (C : Matrix (Fin N) (Fin N) ℂ) (B : Finset (Fin N) → Matrix (Fin N) (Fin N) ℂ), M.blk p = some k₀ → IsGrChart N j p.2 I₀ C B → x₀ ∈ BM.O l \ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) → plk M (BM.F l) k₀ z I₀ ≠ 0 → Real.log ((BM.hom p).h z) = blockPot j p.2 (BM.G l p.1 x₀) (grMat C B I₀ (plk M (BM.F l) k₀ z)) + Real.log ‖baseMono M (BM.F l) p z * plk M (BM.F l) k₀ z I₀‖ := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p k₀ l x₀ z I₀ C B hp hC hx hz hor hw
  obtain ⟨h, a, hb, hd, ha, hstep, hzk⟩ := GlobalTheory.T.block_metric_grassmann_chart_local K ι Φ y Ψ N j M n BM p k₀ l x₀ z hp hx.1 hz hor
  obtain ⟨hHb, hHd, hHm⟩ := hC h a _ hb hd ha hstep hw
  have hL : BM.Rb.lift x₀ x₀ ∈ mcPts (mCoordIdeal M.x) := BM.Rb.mem x₀ x₀ (BM.Rb.mem_U x₀)
  have hor' := hor
  obtain ⟨c0, hc0, e0⟩ := hor'
  have hbz : basePart M.blk z ∈ mcPts (mCoordIdeal M.x) := by
    rw [e0]
    exact ((TorusAct.main _ _ _ M.x _ c0 hc0).2 hL).1
  have hne : ∀ k : NonPluckerBlocks M.blk, basePart M.blk z ⟨k, (BM.F l).c k⟩ ≠ 0 := by
    intro k h0
    have hl : BM.Rb.lift x₀ x₀ ⟨k, (BM.F l).c k⟩ = 0 := by
      have e1 := congrFun e0 ⟨k, (BM.F l).c k⟩
      rw [h0] at e1
      exact (mul_eq_zero.1 e1.symm).resolve_left (hc0 k)
    refine (BM.good l x₀ hx.1).1 k ?_
    show mConeMap (BM.Rb.lift x₀ x₀) (X ⟨k, (BM.F l).c k⟩) = 0
    rw [mConeMap, aeval_X, hl, map_zero, zero_mul]
  let c : K → ℂ := fun k => if hk : ∀ p', M.blk p' ≠ some k then
    (basePart M.blk z ⟨⟨k, hk⟩, (BM.F l).c ⟨k, hk⟩⟩)⁻¹ else if k = k₀ then (plk M (BM.F l) k₀ z I₀)⁻¹ else 1
  have hcb : ∀ k : NonPluckerBlocks M.blk, c k.1 = (basePart M.blk z ⟨k, (BM.F l).c k⟩)⁻¹ := fun k => dif_pos k.2
  have hk₀ : ¬ ∀ p', M.blk p' ≠ some k₀ := fun e => e p hp
  have hck : c k₀ = (plk M (BM.F l) k₀ z I₀)⁻¹ := (dif_neg hk₀).trans (if_pos rfl)
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : ∀ p', M.blk p' ≠ some k
    · rw [hcb ⟨k, hk⟩]
      exact inv_ne_zero (hne ⟨k, hk⟩)
    · by_cases e : k = k₀
      · rw [e, hck]
        exact inv_ne_zero hw
      · rw [show c k = 1 from (dif_neg hk).trans (if_neg e)]
        exact one_ne_zero
  have hz₂ := ((TorusAct.main K ι Φ y z c hc).2 hz).1
  have hval := ((TorusAct.main _ _ _ M.x _ (fun k : NonPluckerBlocks M.blk => c k.1) (fun k => hc _)).2 hbz).2
  have hbp : basePart M.blk (fun q : Σ k, ι k => c q.1 * z q) =
      fun q : Σ k, baseIdx ι M.blk k => c q.1.1 * basePart M.blk z q := rfl
  have hso : SameOrbit (basePart M.blk (fun q : Σ k, ι k => c q.1 * z q)) (BM.Rb.lift x₀ x₀) := by
    refine ⟨fun k => c k.1 * c0 k, fun k => mul_ne_zero (hc _) (hc0 k), ?_⟩
    rw [hbp, e0]
    funext q
    exact (mul_assoc _ _ _).symm
  have hnorm : ∀ k, basePart M.blk (fun q : Σ k, ι k => c q.1 * z q) ⟨k, (BM.F l).c k⟩ = 1 := fun k => by
    rw [hbp]
    show c k.1 * basePart M.blk z ⟨k, (BM.F l).c k⟩ = 1
    rw [hcb k, inv_mul_cancel₀ (hne k)]
  have hlog := (BM.induced l x₀ hx p _ hz₂ hso hnorm _ hHb hHd).1 k₀ hp (fun m => by
    rw [hbp, hzk m, hck]
    simp only [hval]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [mul_left_comm a, ← hHm I, mul_left_comm, ← mul_assoc _ _ (plk M (BM.F l) k₀ z I₀), mul_comm _ (plk M (BM.F l) k₀ z I₀),
      mul_inv_cancel_left₀ hw])
  have hs := (BM.hom p).smul c z hc
  rw [BM.hom_deg p] at hs
  have hdy : M.dy p k₀ = 1 := (dif_neg hk₀).trans (if_pos hp)
  have hdy0 : ∀ k, (¬ ∀ p', M.blk p' ≠ some k) → k ≠ k₀ → M.dy p k = 0 := fun k hk e =>
    (dif_neg hk).trans (if_neg fun e' => e (Option.some_injective _ (hp.symm.trans e')).symm)
  have hsplit := prod_base_split M.blk p k₀ hp (fun k => ‖c k‖ ^ M.dy p k)
    (fun k hk e => by simp only [hdy0 k hk e, zpow_zero])
  have hPQ : (∏ k, ‖c k‖ ^ M.dy p k) * ‖baseMono M (BM.F l) p z * plk M (BM.F l) k₀ z I₀‖ = 1 := by
    rw [hsplit, hdy, zpow_one, hck, norm_mul, baseMono, norm_prod, norm_inv]
    simp only [norm_zpow]
    rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw), mul_one]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [hcb k, norm_inv, _root_.inv_zpow, inv_mul_cancel₀ (zpow_ne_zero _ (norm_ne_zero_iff.2 (hne k)))]
  have hpos := (BM.hom p).pos (fun q => c q.1 * z q) hz₂.1
  have hQ : ‖baseMono M (BM.F l) p z * plk M (BM.F l) k₀ z I₀‖ ≠ 0 := fun e => by
    rw [e, mul_zero] at hPQ
    exact zero_ne_one hPQ
  have hh : (BM.hom p).h z =
      ‖baseMono M (BM.F l) p z * plk M (BM.F l) k₀ z I₀‖ * (BM.hom p).h fun q => c q.1 * z q := by
    rw [hs, ← mul_assoc, mul_comm ‖baseMono M (BM.F l) p z * plk M (BM.F l) k₀ z I₀‖, hPQ, one_mul]
  rw [hh, Real.log_mul hQ hpos.ne', hlog, add_comm]

end GlobalTheory.CompanionTheory.Ar.PB.StepW.ExactStep
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem _root_.GlobalTheory.T.two_point_fibre_chart_third : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => Gn w r s) Un := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.contDiffOn_gram_plane | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.contDiffOn_gram_plane | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.contDiffOn_gram_plane <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

theorem _root_.GlobalTheory.T.flag_adjacent_twisted_resolution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ (x : RW.X) (z₀ z₁ : (Σ k, ι k) → ℂ) (F : FrameData ι Ψ N M.Ω M.blk) (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), IsPtData M τ a k₀ ca cb RW x z₀ z₁ F h t → ¬ SameOrbit (fstPt k₀ (RW.lift x x)) (sndPt k₀ (RW.lift x x)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.not_sameOrbit_of_ptData | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.not_sameOrbit_of_ptData | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.not_sameOrbit_of_ptData <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan


theorem _root_.GlobalTheory.T.frame_LU_minor_value : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (hh : Ψ → Matrix (Fin N) (Fin N) ℂ) (τ' : Ψ) (a' b' : Fin N) (z : (Σ k, ι k) → ℂ) (A L U : Matrix (Fin N) (Fin N) ℂ), M.IsFrame F → zb ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal zb) → IsBlockDiag j A → (hh τ')⁻¹ * A = L * U → IsBlockDiag j L → IsLowerUni L → IsBlockDiag j U → U.BlockTriangular id → (∀ c ∈ stepCols N j (stepOf N j b'), U c c ≠ 0) → b' < a' → ((a' : ℕ) < N - j ↔ (b' : ℕ) < N - j) → (∀ k, M.blk (τ', stepOf N j b') = some k → ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k, z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ A I (stepCols N j (stepOf N j b'))) → lowRead M F zb hh z τ' a' b' = L a' b' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.LowRead.main | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.LowRead.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.LowRead.main <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

theorem _root_.GlobalTheory.T.frameData_local_degree_estimate : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∀ w ∈ pD ε V, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = pPhi M F keep v bl h ε w ∧ basePart M.blk z = bl (pB ε w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.PFl.Ext.main | exact GlobalTheory.CompanionTheory.Ar.PB.PFl.Ext.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.PFl.Ext.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

theorem _root_.GlobalTheory.T.prod_xb_pow_eq_xcOf_pow : ∀ {Ψ : Type} [Fintype Ψ] {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}
    (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type}
    [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (m : Ψ ⊕ Ψ → ℕ)
    (c : ∀ k : NonPluckerBlocks (blkF (Ψ := Ψ) (p := p) (q := q) K₀),
      baseIdx (idx (p := p) (q := q) J₀ n) (blkF (Ψ := Ψ) (p := p) (q := q) K₀) k)
    (r : Ψ × Fin (p + q)),
    ∏ k', xb A x₀ ⟨k', c k'⟩ ^ bF m r k' =
      xcOf x₀ c ^ (rkW r.2 * m (.inl r.1) + rkO r.2 * m (.inr r.1)) *
        (if p ≤ (r.2 : ℕ) + 1 then (zOf A c (.inl r.1))⁻¹ else 1) *
        (if (r.2 : ℕ) + 1 = p + q then (zOf A c (.inr r.1))⁻¹ else 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.prod_xb_zpow_bF | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.prod_xb_zpow_bF | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.prod_xb_zpow_bF <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun


theorem _root_.GlobalTheory.T.model_monomial_weight_product : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (n : Ψ ⊕ Ψ → ℕ) (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (m : Ψ ⊕ Ψ → ℕ) (h : ModelOK A x₀ m) (Φ : Type) [Field Φ] (y : K₀ ⊕ StepIx Ψ p q → Φ), (∀ k, y k ≠ 0) → ∀ (τ : Ψ) (i : Fin (p + q)), (∀ h1 : (i : ℕ) < p, ∏ k, y k ^ (-((model A x₀ m h).dy (τ, i) k)) = (∏ k, y (.inl k)) ^ (((i : ℕ) + 1) * m (.inl τ)) / y (.inr ⟨.inl τ, ⟨i, h1⟩⟩)) ∧ (∀ h1 : p ≤ (i : ℕ), ∏ k, y k ^ (-((model A x₀ m h).dy (τ, i) k)) = (∏ k, y (.inl k)) ^ (p * m (.inl τ) + ((i : ℕ) - p + 1) * m (.inr τ)) / ((if h0 : 0 < p then y (.inr ⟨.inl τ, ⟨p - 1, by show _ < p; omega⟩⟩) else 1) * y (.inr ⟨.inr τ, ⟨(i : ℕ) - p, by have := i.2; show _ < q; omega⟩⟩))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.StepMonomial.step_monomial | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.StepMonomial.step_monomial | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.StepMonomial.step_monomial <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.agreement_positive : AgreementPos := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.agreementPos | exact GlobalTheory.CompanionTheory.Ar.PB.agreementPos | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.agreementPos <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem _root_.GlobalTheory.T.push_down_of_arith_intersection_system : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → GroundTheory.Heights₂.Heights.LowerBoundFree.PushDown.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.pushDown | exact GlobalTheory.CompanionTheory.Ar.Giv.pushDown | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.pushDown <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix


theorem _root_.GlobalTheory.T.regularized_hodge_metric_formula : ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ) (t : ℝ), ∀ z ∈ mcPts (mCoordIdeal D.y), (muReg X.H X.S B t).h z = X.S.ref.h z * Real.exp (X.S.regWeight t (X.M.proj z)) * ∏ p ∈ D.SB B, D.vertFactor p z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Mix.muReg_h_eq_of_mem_mcPts | exact GlobalTheory.CompanionTheory.Ar.Giv.Mix.muReg_h_eq_of_mem_mcPts | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Mix.muReg_h_eq_of_mem_mcPts <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.chart_local_analytic_trivialization : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (a : Fin D.nCharts), ∀ t₀ ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1, ∃ (V : Set ((Σ k, J k) → ℂ)) (T : ((Σ k, J k) → ℂ) → Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ), IsOpen V ∧ (D.chart a).γ t₀ ∈ V ∧ AnalyticOnNhd ℂ T V ∧ T ((D.chart a).γ t₀) = t₀ ∧ ∀ z ∈ V ∩ mcPts (mCoordIdeal D.y), T z ∈ Metric.ball 0 1 ∧ ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusSmul c ((D.chart a).γ (T z)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.chart_torus_open | exact GlobalTheory.CompanionTheory.Ar.Cusp.chart_torus_open | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.chart_torus_open <;> assumption)
end
