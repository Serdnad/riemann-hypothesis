module

public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle072
public import Formalism.LocalToGlobal.Divisibility.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1150
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3


open Formalism.L2.Col in
theorem eigSum_mul_proj_eq {E I C : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (h : I → Module.End ℂ E) (e : Module.End ℂ E) (Ec : C → Submodule ℂ E) (lab : C → I → ℂ)
    (he : e * e = e) (hr : (⨆ c, Ec c) = LinearMap.range e)
    (hh : ∀ c, ∀ w ∈ Ec c, ∀ i, h i w = lab c i • w) :
    _root_.Formalism.L2.Col.PairComm (fun i => h i * e) ∧ ∀ Q : (I → ℂ) → Prop, ¬ Q 0 →
      _root_.Formalism.L2.Col.eigSum (fun i => h i * e) Q = ⨆ (c : C) (_ : Q (lab c)), Ec c := by
  first
  | exact @_root_.GlobalTheory.IndependentInfimum.main
  | exact _root_.GlobalTheory.IndependentInfimum.main
  | (apply _root_.GlobalTheory.IndependentInfimum.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IndependentInfimum.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IndependentInfimum.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IndependentInfimum.main ..)

end GlobalTheory.Hk3
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3.DualHecke

theorem comp_C_mul_X_dualPoly {K : Type} [Field K] (t u : K) (R : K[X]) :
    (Formalism.L2.DIV.dualPoly t R).comp (C u * X) = Formalism.L2.DIV.dualPoly (t * u) R := by
  unfold Formalism.L2.DIV.dualPoly
  rw [mul_comp, C_comp, comp_assoc, mul_comp, C_comp, X_comp, C_mul]
  congr 2
  ring

theorem dualPoly_heckePolyOf_comp : ∀ (K : Type) [Field K] (n q : ℕ) (a b : ℕ → K) (s s' : K), (q : K) ≠ 0 → s ≠ 0 → 0 < n → a 0 = 1 → (∀ j, j ≤ n → b j * a n = a (n - j)) → dualPoly (s * s' * (q : K) ^ (n - 1)) ((Formalism.L2.Col.heckePolyOf n q b).comp (C s * X)) = (Formalism.L2.Col.heckePolyOf n q a).comp (C s' * X) := by
  intro K _ n q a b s s' hq hs hn h0 h
  have han : a n ≠ 0 := by
    intro h1
    have e := h n le_rfl
    rw [Nat.sub_self, h0, h1, mul_zero] at e
    exact zero_ne_one e
  have hbn : b n * a n = 1 := by
    have e := h n le_rfl
    rwa [Nat.sub_self, h0] at e
  have hb0 : b 0 = 1 := by
    have e := h 0 (Nat.zero_le _)
    rw [Nat.sub_zero] at e
    exact mul_right_cancel₀ han (by rw [e, one_mul])
  have hdual : ∀ k ≤ n, b n * a k = b (n - k) := by
    intro k hk
    have e := h (n - k) (Nat.sub_le _ _)
    rw [Nat.sub_sub_self hk] at e
    rw [← e]
    linear_combination b (n - k) * hbn
  have H := GlobalTheory.PartsCompare.heckePolyOf_dual (n := n) (q := q) hq (a := b) (b := a) hb0 hdual
  have hc := GlobalTheory.PartsCompare.dualPoly_comp (inv_ne_zero hs) (s * s' * (q : K) ^ (n - 1))
    (Formalism.L2.Col.heckePolyOf n q b)
  rw [inv_inv] at hc
  rw [hc, H, comp_C_mul_X_dualPoly]
  congr 1
  field_simp

end GlobalTheory.Hk3.DualHecke
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

variable {D : D7}

theorem symplO_half_off (S T : HSp D) {a : AE D} {x u : WO S T} (hx : IsHalf a x) (hu : ∀ i j, cA D a * u i j = 0) :
    symplO S T x u = 0 := by
  have h0 : cA D a • u = 0 := Matrix.ext fun i j => by
    show cA D a * u i j = 0
    exact hu i j
  rw [← (GlobalTheory.SplitScalar.isHalf_iff _ _).1 hx, GlobalTheory.SplitScalar.symplO_smul, h0, GlobalTheory.SplitScalar.symplO_zero_right]

theorem heisO_comm_off (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {a : AE D} {x u : WO S T} (hx : IsHalf a x)
    (hu : ∀ i j, cA D a * u i j = 0) (g : WO S T → ℂ) :
    heisO ψ S T u (heisO ψ S T x g) = heisO ψ S T x (heisO ψ S T u g) := by
  rw [GlobalTheory.SplitScalar.heisO_comm, GlobalTheory.SplitScalar.symplO_skew, symplO_half_off S T hx hu, neg_zero,
    AddChar.map_zero_eq_one, one_smul]

theorem heisO_fix_thetaAt_off : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T))
    (c : ℂ) (f₀ Φ f : WO S T → ℂ), IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f → ∀ u : WO S T,
    (∀ i j, e * u i j = 0 ∧ cA D e * u i j = 0) → heisO ψ S T u f₀ = f₀ → heisO ψ S T u f = f := by
  intro D ψ S T e Λ c f₀ Φ f h u hu hf₀
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := h
  have hm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ ((GlobalTheory.SplitScalar.heisL ψ S T u).comp Tm) :=
    { trans := fun Φ' hΦ' x hx => by
        simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply]
        rw [hTm.trans Φ' hΦ' x hx, heisO_comm_off ψ S T hx (fun i j => (hu i j).2)]
      modul := fun Φ' hΦ' y hy => by
        simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply]
        rw [hTm.modul Φ' hΦ' y hy,
          heisO_comm_off ψ S T hy (fun i j => by rw [GlobalTheory.DualPairCheck.cA_cA]; exact (hu i j).1)]
      vac := by
        simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply]
        rw [hTm.vac, hf₀] }
  have h1 := hall _ hm
  have h2 := hall _ hTm
  simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply] at h1
  rw [h2] at h1 ⊢
  exact h1.symm

end GlobalTheory.Hk3

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem joint_eigenvectors_eq_zero_of_sum_eq_zero (ι κ M : Type) [AddCommGroup M] [Module ℂ M]
    (A : ι → Module.End ℂ M) (χ : κ → ι → ℂ) (v : κ → M) (s : Finset κ)
    (heig : ∀ k ∈ s, ∀ i, A i (v k) = χ k i • v k) (hinj : Set.InjOn χ s)
    (hsum : ∑ k ∈ s, v k = 0) : ∀ k ∈ s, v k = 0 := by
  classical
  induction s using Finset.induction_on generalizing v with
  | empty => simp
  | insert a s ha ih =>
    have hsum' : v a + ∑ k ∈ s, v k = 0 := by rwa [Finset.sum_insert ha] at hsum
    have hs : ∀ k ∈ s, v k = 0 := by
      intro k hk
      have hne : χ k ≠ χ a := by
        intro h
        have hka : k = a := hinj (by simp [hk]) (by simp) h
        exact ha (hka ▸ hk)
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      have hw : (χ k i - χ a i) • v k = 0 := by
        refine ih (fun j => (χ j i - χ a i) • v j) ?_ ?_ ?_ k hk
        · intro j hj i'
          have h1 := heig j (Finset.mem_insert_of_mem hj) i'
          simp only [map_smul, h1]
          rw [smul_comm]
        · exact hinj.mono (by simp)
        · have h2 : A i (v a + ∑ k ∈ s, v k) - χ a i • (v a + ∑ k ∈ s, v k) = 0 := by
            rw [hsum']; simp

          rw [map_add (f := _), map_sum, heig a (Finset.mem_insert_self a s) i, smul_add, Finset.smul_sum,
          add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib] at h2
          rw [← h2]
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [heig j (Finset.mem_insert_of_mem hj) i, sub_smul]
      exact (smul_eq_zero.mp hw).resolve_left (sub_ne_zero.mpr hi)
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · simpa [Finset.sum_eq_zero hs] using hsum'
    · exact hs k hk

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HkUp

theorem adjoint_apply_of_normal_eigen {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V) (hT : Commute T (LinearMap.adjoint T))
    (μ : ℂ) (v : V) (hv : T v = μ • v) :
    LinearMap.adjoint T v = (starRingEnd ℂ) μ • v := by
  set S : Module.End ℂ V := T - μ • LinearMap.id with hS
  have hSadj : LinearMap.adjoint S = LinearMap.adjoint T - (starRingEnd ℂ) μ • LinearMap.id := by
    rw [hS, map_sub, LinearMap.adjoint.map_smulₛₗ, LinearMap.adjoint_id]
  have hcomm : Commute S (LinearMap.adjoint S) := by
    rw [hSadj, hS]
    exact (((hT.sub_right (Commute.smul_right (Commute.one_right _) _)).sub_left
      ((Commute.one_left _).smul_left _ |>.sub_right (Commute.smul_right (Commute.one_right _) _))))
  have hSv : S v = 0 := by simp [hS, hv]
  have h0 : LinearMap.adjoint S v = 0 := by
    have : ⟪LinearMap.adjoint S v, LinearMap.adjoint S v⟫_ℂ = 0 := by
      rw [LinearMap.adjoint_inner_left, ← Module.End.mul_apply, hcomm.eq, Module.End.mul_apply,
        hSv, map_zero, inner_zero_right]
    exact inner_self_eq_zero.mp this
  rw [hSadj] at h0
  simpa [sub_eq_zero] using h0

theorem eigen_up_along_adjoint : ∀ {X E I : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (Θ : X →ₗ[ℂ] E) (op : I → Module.End ℂ X) (h : I → Module.End ℂ E), (∀ i u, Θ (op i u) = h i (Θ u)) → (∀ i, Commute (op i) (LinearMap.adjoint (op i))) → (∀ i, Commute (h i) (LinearMap.adjoint (h i))) → ∀ i (l : ℂ) w, h i w = l • w → op i (LinearMap.adjoint Θ w) = l • LinearMap.adjoint Θ w := by
  intro X E I _ _ _ _ _ _ Θ op h hint hop hh i l w hw
  have hstar : LinearMap.adjoint (h i) w = (starRingEnd ℂ) l • w :=
    adjoint_apply_of_normal_eigen (h i) (hh i) l w hw

  have hcomp : Θ ∘ₗ op i = h i ∘ₗ Θ := LinearMap.ext (hint i)
  have hadj : LinearMap.adjoint (op i) ∘ₗ LinearMap.adjoint Θ
      = LinearMap.adjoint Θ ∘ₗ LinearMap.adjoint (h i) := by
    rw [← LinearMap.adjoint_comp, ← LinearMap.adjoint_comp, hcomp]
  have h1 : LinearMap.adjoint (op i) (LinearMap.adjoint Θ w)
      = (starRingEnd ℂ) l • LinearMap.adjoint Θ w := by
    have := LinearMap.congr_fun hadj w
    simp only [LinearMap.comp_apply] at this
    rw [this, hstar, map_smulₛₗ, RingHom.id_apply]
  have h2 := adjoint_apply_of_normal_eigen (LinearMap.adjoint (op i)) ?_ _ _ h1
  · simpa [LinearMap.adjoint_adjoint] using h2
  · rw [LinearMap.adjoint_adjoint]; exact (hop i).symm

end GlobalTheory.HkUp
end
