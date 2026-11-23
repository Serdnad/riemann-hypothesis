module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.Clause1
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.HarishChandraModulesIndefiniteUnitaryGroup
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.SubquotientNontrivial
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle183
import Development.WeilBound.HeckeVectors.SmoothVectors.SobolevApproximation.SobApproxHolds
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
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary

@[expose] public section

section

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped InnerProductSpace

namespace PositivityTheory.CW.KFiniteInclusion

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

def incl (hK : ∀ v : H, IsKFin ε σ v → v ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ) :
    kfin ε σ →ₗ[ℂ] ReciprocityTheory.ChartRestriction.DS.smD ε σ where
  toFun v := ⟨v, hK v v.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem incl_val (hK : ∀ v : H, IsKFin ε σ v → v ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ) (v : kfin ε σ) :
    ((incl hK v : ReciprocityTheory.ChartRestriction.DS.smD ε σ) : H) = v := rfl

theorem incl_inj (hK : ∀ v : H, IsKFin ε σ v → v ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ) {v w : kfin ε σ}
    (h : incl hK v = incl hK w) : v = w := by
  have h' := congrArg Subtype.val h
  exact Subtype.ext h'

def Eop (hK : ∀ v : H, IsKFin ε σ v → v ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ)
    (h2 : ∀ a b, ∀ v ∈ CompanionTheory.D.gk.HC.KF ε σ, ReciprocityTheory.ChartRestriction.DS.smE ε σ a b v ∈ CompanionTheory.D.gk.HC.KF ε σ)
    (a b : Fin n) : Module.End ℂ (kfin ε σ) :=
  let op := (ReciprocityTheory.ChartRestriction.DS.smE ε σ a b).comp (incl hK)
  ((ReciprocityTheory.ChartRestriction.DS.smD ε σ).subtype.comp op).codRestrict (kfin ε σ)
    fun v => h2 a b (incl hK v) v.2

variable (hK : ∀ v : H, IsKFin ε σ v → v ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ)
    (h2 : ∀ a b, ∀ v ∈ CompanionTheory.D.gk.HC.KF ε σ, ReciprocityTheory.ChartRestriction.DS.smE ε σ a b v ∈ CompanionTheory.D.gk.HC.KF ε σ)

theorem incl_E (a b : Fin n) (v : kfin ε σ) :
    incl hK (Eop hK h2 a b v) = ReciprocityTheory.ChartRestriction.DS.smE ε σ a b (incl hK v) := Subtype.ext rfl

theorem incl_actM (X : Mx n) (v : kfin ε σ) :
    incl hK (ReciprocityTheory.ChartRestriction.DS.actM (Eop hK h2) X v) = ReciprocityTheory.ChartRestriction.DS.actM (ReciprocityTheory.ChartRestriction.DS.smE ε σ) X (incl hK v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ReciprocityTheory.ChartRestriction.DS.actM, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, incl_E]

end PositivityTheory.CW.KFiniteInclusion

namespace PositivityTheory.CW

open KFiniteInclusion

theorem c1 : C1 := by
  intro n ε H _ _ _ σ hσ hirr
  obtain ⟨hK, h2⟩ := CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr
  have hD := ReciprocityTheory.ChartRestriction.DS.isDerivedOn_smE hσ
  have hun := ReciprocityTheory.ChartRestriction.DS.isInfUnitary_of_isDerivedOn hσ hD
  refine ⟨Eop hK h2, ?_, ?_, ?_, ?_⟩
  · intro X hX v
    have h := ReciprocityTheory.ChartRestriction.DS.dS_eq_actM hD (X := X) hX (incl hK v)
    have e1 : ((ReciprocityTheory.ChartRestriction.DS.actM (Eop hK h2) X v : kfin ε σ) : H) =
        ((ReciprocityTheory.ChartRestriction.DS.actM (ReciprocityTheory.ChartRestriction.DS.smE ε σ) X (incl hK v) : ReciprocityTheory.ChartRestriction.DS.smD ε σ) : H) := by
      rw [← incl_actM hK h2 X v]
      rfl
    rw [e1, ← h]
    simp only [ReciprocityTheory.ChartRestriction.DS.dS, dRep, Complex.coe_smul, incl_val]
  · intro a b c d
    refine LinearMap.ext fun v => incl_inj hK ?_
    have h := LinearMap.congr_fun (hD.glRep a b c d) (incl hK v)
    simp only [LinearMap.sub_apply, mul_apply_eq_comp, map_sub, incl_E] at h ⊢
    rw [h]
    split_ifs <;> simp [incl_E]
  · intro a b x y
    have h := hun a b (incl hK x) (incl hK y)
    rw [Submodule.coe_inner, Submodule.coe_inner] at h
    rw [Submodule.coe_inner, Submodule.coe_inner]
    exact h
  · intro N hN
    set M := N.map (incl hK) with hM
    have hMK : (M : Set (ReciprocityTheory.ChartRestriction.DS.smD ε σ)) ⊆ CompanionTheory.D.gk.HC.KF ε σ := by
      rintro _ ⟨w, -, rfl⟩
      exact w.2
    have hMst : ∀ a b, ∀ v ∈ M, ReciprocityTheory.ChartRestriction.DS.smE ε σ a b v ∈ M := by
      rintro a b _ ⟨w, hw, rfl⟩
      exact ⟨Eop hK h2 a b w, hN a b w hw, incl_E hK h2 a b w⟩
    rcases CompanionTheory.D.gk.HC.uIrr n ε H σ hσ hirr M hMK hMst with h | h
    · left
      refine eq_bot_iff.2 fun x hx => ?_
      have : incl hK x ∈ M := ⟨x, hx, rfl⟩
      rw [h, Submodule.mem_bot] at this
      rw [Submodule.mem_bot]
      exact incl_inj hK (this.trans (map_zero _).symm)
    · right
      refine eq_top_iff.2 fun x _ => ?_
      have : incl hK x ∈ (M : Set (ReciprocityTheory.ChartRestriction.DS.smD ε σ)) := by rw [h]; exact x.2
      obtain ⟨w, hw, e⟩ := this
      rwa [← incl_inj hK e]

end PositivityTheory.CW
end
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped ComplexOrder

namespace PositivityTheory.CW

theorem c5 : C5 := by
  intro n ε H _ _ _ σ hU hI
  have hHC := CompanionTheory.D.gk.HC.print_harishChandraModules
  refine ⟨fun v hv => GlobalTheory.CWGeneral.sm_of_isKFin hHC hU hI hv,
    fun v hv X hX => GlobalTheory.CWGeneral.isKFin_dRep_of_irred hHC hU hI hv hX, fun w hw S hS δ hδ => ?_⟩
  have hG : Formalism.IndefR.Tow.SobPf.IsGRep (Formalism.REAL.Jm ε) σ := ⟨hU.1.1, hU.1.2, hU.2.1, hU.2.2⟩
  have hC : Formalism.IndefR.Datum.IsCartanInv (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε) := by
    have hJ : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
      ext i j; simp only [Formalism.REAL.Jm, diagonal_conjTranspose, diagonal_apply]; split_ifs <;> simp_all
    refine ⟨Formalism.REAL.Jm_mul_self ε, ?_, ?_⟩
    · rw [hJ, Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one]
    · rw [Formalism.REAL.Jm_mul_self]; exact Matrix.PosDef.one
  set δ' : ℝ := δ / (S.length + 1) with hδ'
  have hδ'0 : 0 < δ' := div_pos hδ (by positivity)
  obtain ⟨v, hvS, hvK, hvw⟩ := CompanionTheory.D.gk.HC.sobApprox_holds (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε) σ hC hG w
    hw S hS δ' hδ'0
  refine ⟨v, ?_, ?_⟩
  · obtain ⟨W, hW, hvW, hst⟩ := hvK
    refine ⟨W, hW, hvW, fun g hg x hx => hst g ⟨?_, hg.2⟩ x hx⟩
    show gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
    rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
      (Matrix.mem_unitaryGroup_iff').1 hg.1, Matrix.one_mul]
  · have hv' : Sm ε σ v := hvS
    have key : ∀ l ∈ S, ‖Dw σ l (w - v)‖ ≤ δ' := by
      intro l hl
      have e : Dw σ l (w - v) = Dw σ l w - Dw σ l v := by
        have := Dw_add hU (hS l hl) (sm_iff.2 ((smooth (Jm ε) σ).sub_mem (sm_iff.1 hw) (sm_iff.1 hv'))) hv'
        rw [sub_add_cancel] at this
        rw [this, add_sub_cancel_right]
      rw [e, norm_sub_rev]
      exact (hvw l hl).le
    have hL : (S.length : ℝ) * δ' < δ := by
      rw [hδ', mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    delta sobNorm
    calc (S.map fun l => ‖l.foldr (dRep σ) (w - v)‖).sum
        ≤ (S.map fun l => ‖l.foldr (dRep σ) (w - v)‖).length • δ' :=
          List.sum_le_length_nsmul _ _ (fun x hx => by
            obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
            exact key l hl)
      _ = S.length * δ' := by simp
      _ < δ := hL

end PositivityTheory.CW
end
