module

public import Formalism.LocalToGlobal.GlobalTheory.GL4.Bundle004
public import Formalism.LocalToGlobal.GlobalTheory.GL4.ThirdPropositionOfClass
public import Formalism.LocalToGlobal.Columns.Bundle008
public import Formalism.LocalToGlobal.Columns.Bundle005
public import Formalism.SharpRestriction.GlobalSchurBounds.SlopeMaxOpenOfHookTwoLeV
public import Formalism.LocalToGlobal.GlobalTheory.GL4.ColumnLatticeExactSlope
public import Formalism.LocalToGlobal.GlobalTheory.GL4.Bundle002
public import Formalism.LocalToGlobal.GlobalTheory.GL4.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.TotallyPositiveTraceGeOfNormDiscr
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle017
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle022
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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

open Module NumberField IsDedekindDomain MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Col Formalism.BasicNotions.SkeletonIndexLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Int2

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)

theorem cf_mem_twId (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V)
    (hy : ∀ a, y a ∈ dualSub (D.sp.X 0) (D.clsLat u 0 c)) (g : D.what₂.Tau → GL (Fin (D.R.N 0)) D.what₂.LL)
    (hg : ∀ τ, ((g τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) = gM CV c y τ)
    {x : ((D.fm u).lat 0).V} (hx : x ∈ NC CV c) (m : MonI ((D.fm u).lam 0)) :
    cfMap ((D.fm u).lam 0) g (coE CV (hTV0 D u) x c) m ∈ twId ((D.fm u).lam 0) (MQ CV c) := by
  classical
  rw [mem_twId]
  intro w B hB
  set w' := D.plEq.symm w with hw'
  have hw : D.plEq w' = w := D.plEq.apply_symm_apply w
  have hLB : ∀ τ, LocBasis D w' (CV.Q c τ) (CV.eQ c τ) (B τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) :=
    fun τ => locBasis_of_isBasisAt CV c τ w' (B τ) (by rw [hw]; exact hB τ)
  let γ : (D.mem u).C.cls 0 → D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL := fun c' τ =>
    if c' = c then (B τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)
    else Classical.choose (exists_locBasis w' (CV.Q c' τ) (CV.Q_good c' τ) (CV.eQ c' τ))
  have hγ : ∀ c' τ, LocBasis D w' (CV.Q c' τ) (CV.eQ c' τ) (γ c' τ) := by
    intro c' τ
    by_cases h : c' = c
    · simp only [γ, if_pos h]
      rw [h]
      exact hLB τ
    · simp only [γ, if_neg h]
      exact Classical.choose_spec (exists_locBasis w' (CV.Q c' τ) (CV.Q_good c' τ) (CV.eQ c' τ))
  have hxL : x ∈ ((D.fm u).lat 0).L := by
    obtain ⟨x', hx', rfl⟩ := hx
    exact prjC_mem CV c hx'
  have hxW : x ∈ locW D.what₂.places w' ((D.fm u).lat 0).L := Submodule.subset_span hxL
  have hP := (CV.fin w' γ hγ x).1 hxW c
  simp only [γ, if_pos rfl] at hP
  set F : Pol D.what₂.LL D.what₂.Tau (D.R.N 0) := ((coE CV (hTV0 D u) x c : VV D.what₂.LL ((D.fm u).lam 0)) :
    Pol D.what₂.LL D.what₂.Tau (D.R.N 0)) with hF
  have hFco : F = CV.co x c := coE_coe CV (hTV0 D u) x c
  have hinvB : (fun τ => (B τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)⁻¹) =
      fun τ => (((B⁻¹) τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) := by
    funext τ
    rw [Pi.inv_apply, Matrix.coe_units_inv]
  rw [← hFco, hinvB, actAll_eq_actP] at hP
  have hF0 : actP ((D.fm u).lam 0) B⁻¹ F ∈ (map (σ := D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) (locRing w).subtype).range := by
    refine mem_range_of_coeff_mem _ fun m' => ?_
    rw [← hw]
    exact intW_mem_locRing w' (coeff_mem_of_intSpanAt w' _ hP m')
  have hU : ∀ τ a b, (((g * B) τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)ᵀ a b ∈
      locRing w := by
    intro τ a b
    have hcol : (fun c => (B τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) c a) ∈ localization₂ w.asIdeal (MQ CV c τ) := by
      rw [hB τ]
      exact le_localisation w _ (Submodule.subset_span ⟨a, rfl⟩)
    obtain ⟨s, hs, hsx⟩ := hcol
    rw [mem_locRing]
    refine ⟨s, hs, ?_⟩
    have := gM_int CV c y hy τ _ hsx b
    rw [← hg τ, Matrix.mulVec_smul] at this
    have e : (((g * B) τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)ᵀ a b =
        ((g τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) *ᵥ fun c => (B τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) c a) b := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [e]
    exact this
  have hkey := coeff_mem_of_mem_range _ (block_action_integral (locRing w) _ hU hF0) m.1
  have e : Formalism.GradedWeylDivisibility.blockAct D.what₂.LL (fun τ => (((g * B) τ : GL (Fin (D.R.N 0)) D.what₂.LL) :
      Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)ᵀ) (actP ((D.fm u).lam 0) B⁻¹ F) =
      detTwK ((D.fm u).lam 0) B⁻¹ • trAct g F := by
    show trAct (g * B) (actP ((D.fm u).lam 0) B⁻¹ F) = _
    rw [trAct_mul]
    simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply, map_smul, transpose_action_inv_right]
  rw [e, MvPolynomial.coeff_smul, smul_eq_mul, mem_locRing] at hkey
  exact hkey

end Int2

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Col

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ClassMap (D : D7) : Prop :=
  ∀ u (CV : ColVal D u) (c : (D.mem u).C.cls 0), (∃ y : Fin (D.R.N 0) → (D.sp.X 0).V, Formalism.MainNotions.flipTwoThree.ShortAt D u c y) →
    ∃ (φ : ((D.fm u).lat 0).V →ₗ[D.what₂.LL] (MonI ((D.fm u).lam 0) → D.what₂.LL))
      (I : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) (B : InfinitePlace D.what₂.LL → ℝ),
      Set.InjOn φ (NC CV c) ∧ I ≠ 0 ∧ (∀ x ∈ NC CV c, ∀ m, φ x m ∈ (I : Submodule (𝓞 D.what₂.LL) D.what₂.LL)) ∧ (∀ v, 0 < B v) ∧
      (∀ v x, normAt (Pi.basisFun D.what₂.LL (MonI ((D.fm u).lam 0))) (fun _ => (monD ((D.fm u).lam 0))⁻¹) v (φ x) ^ 2 ≤
        B v * normAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x ^ 2) ∧
      -(2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ D.what₂.LL : ℝ)) +
          (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (B v) ≤
        ∑ τ, (colAbsP D u τ * Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2) - (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u))

theorem slopeMaxClass_of_map (D : D7) (h : ClassMap D) : SlopeMaxClass D := by
  intro u CV c hy
  have := (columnHypotheses D u).tc
  obtain ⟨φ, I, B, hinj, hI0, hint, hB, hnorm, hnum⟩ := h u CV c hy
  have hne : (NC CV c).map (φ.restrictScalars (𝓞 D.what₂.LL)) ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (NC_ne_bot CV c)
    intro h0
    have hm : φ.restrictScalars (𝓞 D.what₂.LL) x ∈ (NC CV c).map (φ.restrictScalars (𝓞 D.what₂.LL)) := ⟨x, hx, rfl⟩
    rw [h0, Submodule.mem_bot] at hm
    exact hx0 (hinj hx (zero_mem _) (by rw [map_zero]; exact hm))
  have hm := muMax_le_mon D.what₂.LL ((D.fm u).lam 0) ((D.fm u).lat 0).b ((D.fm u).lat 0).X ((D.fm u).lat_good 0).1 (NC CV c)
    (((D.fm u).lat_good 0).2.1.map _) φ hinj hne I hI0 hint B hB hnorm (monCnu ((D.fm u).lam 0))
    (monCnu_pos _) (monW_ge_cNu _)
  have hl := log_monCnu ((D.fm u).lam 0) (rank_zero_pos D)
  rw [hl] at hm
  have hdW : ∀ τ, (dW ((D.fm u).lam 0 τ) : ℝ) = colAbsP D u τ := fun τ => by
    unfold dW
    push_cast
    exact sum_natWeight_eq_colAbsShifted D u τ
  have hN : ((D.R.N 0 : ℕ) : ℝ) = (D.R.k : ℝ) := by rw [Ranks.N_zero]
  simp only [hdW, hN] at hm
  have hk : (0 : ℝ) < D.R.k := by exact_mod_cast columnCount_pos D
  have hv : (0 : ℝ) < D.host.v := by have := two_le_half_rootDiscr D; linarith
  have hR : (∑ τ, (colAbsP D u τ * Real.log (4 * (D.R.k : ℝ) ^ 4 * D.host.v ^ 2) +
        Real.log (cNu ((D.fm u).lam 0 τ).natW) - (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u))) =
      (∑ τ, (colAbsP D u τ * Real.log (D.R.k : ℝ) + Real.log (cNu ((D.fm u).lam 0 τ).natW))) +
      ∑ τ, (colAbsP D u τ * Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2) - (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u)) := by
    have e4 : Real.log (4 * (D.R.k : ℝ) ^ 4 * D.host.v ^ 2) =
        Real.log (D.R.k : ℝ) + Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2) := by
      rw [← Real.log_mul hk.ne' (by positivity)]
      congr 1
      ring
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [e4]
    ring
  show muMaxDef ((D.fm u).lat 0).b ((D.fm u).lat 0).X (NC CV c) ≤ _
  rw [hR]
  linarith

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Col

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem shortAt_pos (D : D7) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V)
    (hy : Formalism.MainNotions.flipTwoThree.ShortAt D u c y) (w : InfinitePlace D.host.E) (a : Fin (D.R.N 0)) :
    0 < (w.embedding ((D.sp.X 0).hT (y a) (y a))).re := by
  obtain ⟨r, hr, he⟩ := (columnHypotheses D u).pos w.embedding (y a) (hy.2.1.ne_zero a)
  rw [he, Complex.ofReal_re]
  exact hr

def ClassMapT (D : D7) : Prop :=
  ∀ u (CV : ColVal D u) (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V), Formalism.MainNotions.flipTwoThree.ShortAt D u c y →
    ∃ (φ : ((D.fm u).lat 0).V →ₗ[D.what₂.LL] (MonI ((D.fm u).lam 0) → D.what₂.LL))
      (I : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) (Dv : InfinitePlace D.what₂.LL → ℝ),
      Set.InjOn φ (NC CV c) ∧ I ≠ 0 ∧ (∀ x ∈ NC CV c, ∀ m, φ x m ∈ (I : Submodule (𝓞 D.what₂.LL) D.what₂.LL)) ∧ (∀ v, 0 < Dv v) ∧
      (∀ v x, normAt (Pi.basisFun D.what₂.LL (MonI ((D.fm u).lam 0))) (fun _ => (monD ((D.fm u).lam 0))⁻¹) v (φ x) ^ 2 ≤
        ((∏ τ, (∑ a, (v.embedding (CV.rho τ ((D.sp.X 0).hT (y a) (y a)))).re) ^ dW ((D.fm u).lam 0 τ)) * Dv v) *
          normAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x ^ 2) ∧
      -(2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ D.what₂.LL : ℝ)) +
          (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (Dv v) ≤
        -∑ τ, (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u)

theorem class_map_of_archimedean (D : D7) (h : ClassMapT D) : ClassMap D := by
  intro u CV c hy
  obtain ⟨y, hy⟩ := hy
  have := (columnHypotheses D u).tc
  have := (columnHypotheses D u).tcE
  have hposE := shortAt_pos D u c y hy
  obtain ⟨φ, I, Dv, hinj, hI0, hint, hD, hnorm, hnum⟩ := h u CV c y hy
  set G : InfinitePlace D.what₂.LL → D.what₂.Tau → ℝ := fun v τ => ∑ a, (v.embedding (CV.rho τ ((D.sp.X 0).hT (y a) (y a)))).re with hG
  have hN0 : 0 < D.R.N 0 := rank_zero_pos D
  have hGc : ∀ v τ, G v τ = ∑ a, ((v.comap (CV.rho τ)).embedding ((D.sp.X 0).hT (y a) (y a))).re := fun v τ =>
    Finset.sum_congr rfl fun a _ => (re_comap (CV.rho τ) v _).symm
  have hGpos : ∀ v τ, 0 < G v τ := fun v τ => by
    rw [hGc]
    exact Finset.sum_pos (fun a _ => hposE _ a) ⟨⟨0, hN0⟩, Finset.mem_univ _⟩
  refine ⟨φ, I, fun v => (∏ τ, G v τ ^ dW ((D.fm u).lam 0 τ)) * Dv v, hinj, hI0, hint,
    fun v => mul_pos (Finset.prod_pos fun τ _ => pow_pos (hGpos v τ) _) (hD v), hnorm, ?_⟩
  have hlog : ∀ v, Real.log ((∏ τ, G v τ ^ dW ((D.fm u).lam 0 τ)) * Dv v) =
      (∑ τ, (dW ((D.fm u).lam 0 τ) : ℝ) * Real.log (G v τ)) + Real.log (Dv v) := fun v => by
    rw [Real.log_mul (Finset.prod_pos fun τ _ => pow_pos (hGpos v τ) _).ne' (hD v).ne',
      Real.log_prod (fun τ _ => (pow_pos (hGpos v τ) _).ne')]
    congr 1
    exact Finset.sum_congr rfl fun τ _ => Real.log_pow _ _
  have hmean : ∀ τ, (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (G v τ) ≤ Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2) := by
    intro τ
    have h1 := mean_over_places_comap D.host.E D.what₂.LL (CV.rho τ)
      (fun w => Real.log (∑ a, (w.embedding ((D.sp.X 0).hT (y a) (y a))).re))
    have h2 : (∑ v, Real.log (G v τ)) = ∑ v : InfinitePlace D.what₂.LL,
        Real.log (∑ a, ((v.comap (CV.rho τ)).embedding ((D.sp.X 0).hT (y a) (y a))).re) :=
      Finset.sum_congr rfl fun v _ => by rw [hGc]
    rw [h2, h1]
    exact shortAt_mean_log D u c y hy hposE
  have hdW : ∀ τ, (dW ((D.fm u).lam 0 τ) : ℝ) = colAbsP D u τ := fun τ => by
    unfold dW
    push_cast
    exact sum_natWeight_eq_colAbsShifted D u τ
  have hsplit : (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log ((∏ τ, G v τ ^ dW ((D.fm u).lam 0 τ)) * Dv v) =
      (∑ τ, (dW ((D.fm u).lam 0 τ) : ℝ) * ((1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (G v τ))) +
        (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (Dv v) := by
    simp only [hlog, Finset.sum_add_distrib, mul_add]
    congr 1
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun v _ => by ring
  have hbound : (∑ τ, (dW ((D.fm u).lam 0 τ) : ℝ) * ((1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (G v τ))) ≤
      ∑ τ, colAbsP D u τ * Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2) :=
    Finset.sum_le_sum fun τ _ => by
      rw [← hdW τ]
      exact mul_le_mul_of_nonneg_left (hmean τ) (Nat.cast_nonneg _)
  rw [hsplit]
  have e : (∑ τ, (colAbsP D u τ * Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2) -
      (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u))) =
      (∑ τ, colAbsP D u τ * Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2)) -
        ∑ τ, (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u) := Finset.sum_sub_distrib _ _
  rw [e]
  linarith

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

theorem column_exact_slope_family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : fam0 Fm ColSlopeEq :=
  ⟨0, fun _ _ _ _ => column_lattice_exact_slope _⟩

theorem lower_slope_inequality_family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : FamilySlopeLowerOpenPart Fm :=
  familySlopeLowerOpen_of_std standard_slope_lower hook_length_bound Fm (column_exact_slope_family Fm)

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end
