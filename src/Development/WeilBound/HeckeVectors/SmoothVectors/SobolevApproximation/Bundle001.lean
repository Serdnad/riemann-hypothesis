module

import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle032
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothVec
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfSt
public import Formalism.PeriodIntegrals.Bundle004
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.OrbitDerivatives.EtaleClosedPointLiftsSimpleRootsMonic
public import Development.WeilBound.HeckeVectors.SmoothVectors.SobolevApproximation.SobApproxHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BesselDerivatives.ExpSup
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KFiniteSmoothVectors.Garding
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle016
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.WeylBridge
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.PeriodIntegrals.Bundle013

@[expose] public section

section

open Matrix Topology
open scoped ComplexOrder

noncomputable section

namespace CompanionTheory.D.gk.HC

open Formalism.BasicNotions.TH (GrpData URep GKMod)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section UJ

variable {n : ℕ} (ε : Fin n → Bool)

theorem ujInvC {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.MainNotions.S.UJset ε) :
    (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = 1 := by
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', Formalism.REAL.Jm_mul_self]

theorem isMatGroupC : PI.IsMatGroup (Formalism.MainNotions.S.UJset ε) := by
  refine ⟨?_, ?_, fun a ha b hb => ?_, fun a ha => ?_⟩
  · exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  · show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε * 1 = Formalism.REAL.Jm ε; simp
  · have ha' : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := ha
    have hb' : bᴴ * Formalism.REAL.Jm ε * b = Formalism.REAL.Jm ε := hb
    show (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = Formalism.REAL.Jm ε
    calc (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [ha', hb']
  · have h1 := ujInvC ε ha
    have h2 : a * a⁻¹ = 1 := by rw [Matrix.inv_eq_left_inv h1]; exact mul_eq_one_comm.1 h1
    refine ⟨?_, h2⟩
    have ha' : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := ha
    show (a⁻¹)ᴴ * Formalism.REAL.Jm ε * a⁻¹ = Formalism.REAL.Jm ε
    calc (a⁻¹)ᴴ * Formalism.REAL.Jm ε * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * a⁻¹ := by rw [ha']
      _ = (a * a⁻¹)ᴴ * Formalism.REAL.Jm ε * (a * a⁻¹) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h2, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

def thetaC : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => Formalism.REAL.Jm ε * xᴴ * Formalism.REAL.Jm ε
      map_add' := fun a b => by rw [conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c a => by
        rw [conjTranspose_smul, star_trivial, Matrix.mul_smul, Matrix.smul_mul]; rfl }

theorem thetaC_eq {x : Matrix (Fin n) (Fin n) ℂ} (hx : x ∈ Formalism.MainNotions.S.UJset ε) : thetaC ε x = x⁻¹ :=
  (Matrix.inv_eq_left_inv (ujInvC ε hx)).symm

variable {ε} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem repOnC (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) : CompanionTheory.D.Upq.Sm.RepOn (Formalism.MainNotions.S.UJset ε) σ :=
  ⟨(isMatGroupC ε).2.1, (isMatGroupC ε).2.2.1, hσ.1.1, hσ.1.2⟩

theorem smoothVec_of_isSmC {w : H} (hw : CompanionTheory.D.Upq.Sm.IsSm (Formalism.MainNotions.S.UJset ε) σ w) :
    Formalism.L2.Theta.SmoothVec (Formalism.IndefR.Tow.SobPf.lieG (Formalism.REAL.Jm ε)) σ w := by
  intro m Xs hX
  have hc : ∀ (k : ℕ) (Ys : Fin k → Matrix (Fin n) (Fin n) ℂ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : Fin k → ℝ =>
        (List.ofFn fun i => NormedSpace.exp (t i • Ys i)).prod) := by
    intro k
    induction k with
    | zero =>
      intro Ys
      simpa using (contDiff_const : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun _ : Fin 0 → ℝ =>
        (1 : Matrix (Fin n) (Fin n) ℂ))
    | succ k ih =>
      intro Ys
      have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : Fin (k + 1) → ℝ =>
          NormedSpace.exp (t 0 • Ys 0)) := by
        have he : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => NormedSpace.exp (s • Ys 0)) := by
          simpa only [Complex.coe_smul] using PI.BesselDerivW.exp_contDiff (Ys 0)
        exact he.comp (contDiff_apply ℝ (fun _ => ℝ) (0 : Fin (k + 1)))
      have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : Fin (k + 1) → ℝ =>
          (List.ofFn fun i : Fin k => NormedSpace.exp (t i.succ • Ys i.succ)).prod) :=
        (ih (fun i => Ys i.succ)).comp
          (contDiff_pi.2 fun i => contDiff_apply ℝ (fun _ => ℝ) i.succ)
      simp only [List.ofFn_succ, List.prod_cons]
      exact PI.KFinSmoothW.Gard.contDiff_mat_mul h1 h2
  have hc := hc m Xs
  have hmem : ∀ t : Fin m → ℝ, (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod ∈ Formalism.MainNotions.S.UJset ε :=
    by
      intro t
      have hm : ∀ (k : ℕ) (Ys : Fin k → Matrix (Fin n) (Fin n) ℂ),
          (∀ i, (Ys i)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * Ys i = 0) →
          ∀ t : Fin k → ℝ,
          ((List.ofFn fun i => NormedSpace.exp (t i • Ys i)).prod)ᴴ * Formalism.REAL.Jm ε *
            (List.ofFn fun i => NormedSpace.exp (t i • Ys i)).prod = Formalism.REAL.Jm ε := by
        intro k
        induction k with
        | zero => intro Ys hYs t; simp
        | succ k ih =>
          intro Ys hYs t
          have hi := ih (fun i => Ys i.succ) (fun i => hYs i.succ) (fun i => t i.succ)
          have hl : (t 0 • Ys 0)ᴴ * Formalism.REAL.Jm ε +
              Formalism.REAL.Jm ε * (t 0 • Ys 0) = 0 := by
            have h := CCRuleCW.lie_smul
              (Formalism.REAL.Jm ε) (Ys 0) (hYs 0) (t 0)
            simpa only [Complex.coe_smul] using h
          have he := CCRuleCW.exp_mem_UH
            (Formalism.REAL.Jm ε) (t 0 • Ys 0) hl
          have hp := CCRuleCW.UH_mul
            (Formalism.REAL.Jm ε) _ _ he hi
          simpa only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq, List.ofFn_succ, List.prod_cons] using hp
      exact hm m Xs (fun i => hX i) t
  rw [contDiff_iff_contDiffAt]
  intro t0
  obtain ⟨U, F, hU, h0, hF, hEq⟩ := hw _ (hmem t0)
  have hev : (fun t : Fin m → ℝ => σ ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) w)
      =ᶠ[𝓝 t0] fun t => F ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) := by
    filter_upwards [hc.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds h0)] with t ht
    exact hEq _ ht (hmem t)
  exact ((hF.contDiffAt (hU.mem_nhds h0)).comp t0 hc.contDiffAt).congr_of_eventuallyEq hev

theorem kfinDense_UJC (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) : Dense {v : H | Formalism.MainNotions.S.IsKFin ε σ v} := by
  apply GlobalTheory.CompactRep.dense_isKFin <;> assumption

end UJ

end CompanionTheory.D.gk.HC
end
end

section

open Matrix Topology Filter
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace CompanionTheory.D.gk.HC

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem smoothVec_of_smD_A {v : H} (hv : v ∈ smD ε σ) :
    Formalism.L2.Theta.SmoothVec (Formalism.IndefR.Tow.SobPf.lieG (Formalism.REAL.Jm ε)) σ v := by
  rw [mem_smD_iff] at hv
  intro m Xs hX
  have hc := Formalism.IndefR.PeterssonHilbertSpace.sm_prod_exp_contDiff m Xs
  have hmem : ∀ t : Fin m → ℝ, Formalism.QuantumDeterminants.inUH (Formalism.REAL.Jm ε)
      ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) :=
    fun t => Formalism.IndefR.PeterssonHilbertSpace.sm_prod_exp_mem _ m Xs (fun i => hX i) t
  rw [contDiff_iff_contDiffAt]
  intro t0
  obtain ⟨U, F, hU, h0, hF, hEq⟩ := hv _ (hmem t0)
  have hev : (fun t : Fin m → ℝ => σ ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) v)
      =ᶠ[𝓝 t0] fun t => F ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) := by
    filter_upwards [hc.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds h0)] with t ht
    exact hEq _ ht (hmem t)
  exact ((hF.contDiffAt (hU.mem_nhds h0)).comp t0 hc.contDiffAt).congr_of_eventuallyEq hev

theorem isGRep_A (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) :
    Formalism.IndefR.Tow.SobPf.IsGRep (Formalism.REAL.Jm ε) σ :=
  ⟨hσ.1.1, hσ.1.2, hσ.2.1, hσ.2.2⟩

theorem cartan_A : Formalism.IndefR.Datum.IsCartanInv (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε) := by
  have h2 : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Jm_mul_Jm ε
  have hh : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := Jm_conjTranspose ε
  refine ⟨h2, ?_, ?_⟩
  · rw [hh, h2, Matrix.one_mul]
  · rw [h2]; exact Matrix.PosDef.one

theorem kfin_of_kfinG_A {a : H}
    (h : Formalism.IndefR.Tow.SobPf.KFinG (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε) σ a) : Formalism.MainNotions.S.IsKFin ε σ a := by
  obtain ⟨W, hW, haW, hst⟩ := h
  exact ⟨W, hW, haW, fun g hg x hx => hst g ⟨HW.hw_kset_subset ε hg, hg.2⟩ x hx⟩

theorem exists_kfin_near_A [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {w : H}
    (hw : w ∈ smD ε σ) {δ : ℝ} (hδ : 0 < δ) : ∃ a : H, Formalism.MainNotions.S.IsKFin ε σ a ∧ ‖a - w‖ < δ := by
  obtain ⟨a, -, haK, ha⟩ := CompanionTheory.D.gk.HC.sobApprox_holds (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε) σ cartan_A
    (isGRep_A hσ) w (smoothVec_of_smD_A hw) [[]] (by simp) δ hδ
  exact ⟨a, kfin_of_kfinG_A haK, by simpa [Formalism.IndefR.Tow.SobPf.dL] using ha [] (by simp)⟩

theorem eq_zero_of_perp_A [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {w : H}
    (hw : w ∈ smD ε σ) (h : ∀ a : H, Formalism.MainNotions.S.IsKFin ε σ a → ⟪a, w⟫_ℂ = 0) : w = 0 := by
  refine norm_eq_zero.1 (le_antisymm (le_of_forall_pos_le_add fun δ hδ => ?_) (norm_nonneg _))
  rw [zero_add]
  obtain ⟨a, ha, hlt⟩ := exists_kfin_near_A hσ hw hδ
  have h1 : ‖w‖ ^ 2 = RCLike.re ⟪w - a, w⟫_ℂ := by
    rw [inner_sub_left, map_sub, h a ha, map_zero, sub_zero, inner_self_eq_norm_sq]
  have h2 : RCLike.re ⟪w - a, w⟫_ℂ ≤ ‖w - a‖ * ‖w‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  rw [norm_sub_rev] at h2
  by_cases h0 : ‖w‖ = 0
  · rw [h0]; exact hδ.le
  · have hpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

theorem casimir_symm_A (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (x y : smD ε σ) :
    ⟪casimir (smE ε σ) x, y⟫_ℂ = ⟪x, casimir (smE ε σ) y⟫_ℂ := by
  have hU := isInfUnitary_of_isDerivedOn hσ (isDerivedOn_smE hσ)
  simp only [casimir, LinearMap.sum_apply, mul_apply_eq_comp, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hU, hU, ← mul_assoc]
  have : adjSign ε a b * adjSign ε b a = 1 := by
    unfold adjSign
    by_cases h : ε a = ε b
    · simp [h]
    · simp [h, Ne.symm h]
  rw [this, one_mul]

end CompanionTheory.D.gk.HC
end
end
