module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle027

public import Formalism.RealPlaceAnalysis.Bundle005
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.L2Embedding
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Finiteness.Lattice
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgExh

open Formalism.REAL (qdet qminor Tm)
open _root_.CompanionTheory.RgExh
open _root_.CompanionTheory.RgExh.Hk

theorem commute_qdet_of {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (T : A)
    (h : ∀ a b, Commute (E a b) T) (u : ℂ) : Commute (qdet E u) T := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  refine Commute.sum_left _ _ _ fun σ _ => ?_
  refine Commute.mul_left (Int.cast_commute _ _) ?_
  refine Commute.list_prod_left _ _ fun x hx => ?_
  rw [List.mem_ofFn] at hx
  obtain ⟨k, rfl⟩ := hx
  unfold Formalism.REAL.Tm
  refine Commute.add_left ?_ (h _ _)
  split_ifs
  · exact Algebra.commute_algebraMap_left _ _
  · exact Commute.zero_left _

theorem commute_compLeft_om {n : ℕ} (X : GMod n) (u : ℂ) :
    Commute ((qdet X.E u).compLeft (Fin n)) (om X) := by
  have hc := Formalism.REAL.qDetCentral (Module.End ℂ X.V) n X.E X.gl u
  unfold Commute SemiconjBy
  refine LinearMap.ext fun f => funext fun b => ?_

  simp only [Module.End.mul_apply, LinearMap.compLeft_apply, Function.comp_apply, om, LinearMap.coe_mk,
  AddHom.coe_mk, map_sum]
  exact Finset.sum_congr rfl fun a _ => LinearMap.congr_fun (hc a b) (f a)

theorem qdetTens : QdetTens := by
  intro n X u
  rcases n with _ | m
  · exact LinearMap.ext fun f => funext fun i => i.elim0
  · have hT : ∀ a b, Commute (tensE X a b) (om X) := by
      intro a b
      unfold Commute SemiconjBy
      refine LinearMap.ext fun f => funext fun c => ?_
      have key : ∀ d, X.E a b (X.E d c (f d)) =
          ((if b = d then X.E a c else 0) - (if c = a then X.E d b else 0)) (f d) + X.E d c (X.E a b (f d)) := by
        intro d
        have h1 := LinearMap.congr_fun (X.gl a b d c) (f d)
        rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, sub_eq_iff_eq_add] at h1
        exact h1

      simp only [Module.End.mul_apply, tensE, eOp, om, LinearMap.add_apply, LinearMap.compLeft_apply,
      Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, map_sum, map_add]
      rw [Finset.sum_congr rfl fun d _ => key d]
      by_cases hca : c = a
      · subst hca
        simp [Finset.sum_add_distrib, LinearMap.sub_apply, apply_ite, Finset.sum_sub_distrib]
        simp only [ite_apply, LinearMap.zero_apply, Pi.zero_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        abel
      · simp [Finset.sum_add_distrib, LinearMap.sub_apply, apply_ite, hca, Finset.sum_sub_distrib]
        simp only [ite_apply, LinearMap.zero_apply, Pi.zero_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        abel
    have hC : Commute (qdet (tensE X) u) (u • (1 : Module.End ℂ (Fin (m + 1) → X.V)) + om X) :=
      Commute.add_right ((Commute.one_right _).smul_right u) (commute_qdet_of _ _ hT u)
    have hD : Commute ((qdet X.E u).compLeft (Fin (m + 1)))
        (u • (1 : Module.End ℂ (Fin (m + 1) → X.V)) + om X) :=
      Commute.add_right ((Commute.one_right _).smul_right u) (commute_compLeft_om X u)
    rw [hC.eq, GlobalTheory.T.HeckeRankOne m X u, mul_add, GlobalTheory.T.OmegaMinor m X u, ← hD.eq]
    simp only [add_smul, one_smul, mul_add, mul_one]
    abel

end GlobalTheory.CompanionTheory.RgExh
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.RgSteps

open _root_.CompanionTheory.RgExh
open Formalism.REAL (IsWeight)
open CompanionTheory.D.LK (LocFin)

variable {n : ℕ}

theorem locFin_tens (ε : Fin n → Bool) (X : GMod n) (h : LocFin ε X.E) : LocFin ε (tens X).E := by
  intro u
  choose S hSfd hSst hSmem using fun i => h (u i)
  haveI : ∀ i, FiniteDimensional ℂ (S i) := hSfd
  have hTst : ∀ a b, ε a = ε b → ∀ x ∈ ⨆ i, S i, X.E a b x ∈ ⨆ i, S i := by
    intro a b hab x hx
    refine Submodule.iSup_induction S (motive := fun y => X.E a b y ∈ ⨆ i, S i) hx
      (fun i y hy => (le_iSup S i) (hSst i a b hab y hy)) (by simp) ?_
    intro y w hy hw
    rw [(X.E a b).map_add]
    exact Submodule.add_mem _ hy hw
  have hfd : FiniteDimensional ℂ (Submodule.pi Set.univ fun _ : Fin n => ⨆ i, S i) := by
    let f : (Submodule.pi Set.univ fun _ : Fin n => ⨆ i, S i) →ₗ[ℂ] (Fin n → ↥(⨆ i, S i)) :=
      { toFun := fun v i => ⟨v.1 i, v.2 i (Set.mem_univ i)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact FiniteDimensional.of_injective f
      (fun v w hvw => Subtype.ext (funext fun i => congrArg Subtype.val (congrFun hvw i)))
  refine ⟨Submodule.pi Set.univ (fun _ : Fin n => ⨆ i, S i), hfd, ?_, ?_⟩
  · intro a b hab v hv i _
    have hv' : ∀ j, v j ∈ ⨆ i, S i := fun j => hv j (Set.mem_univ j)
    change X.E a b (v i) + (if i = a then v b else 0) ∈ ⨆ i, S i
    refine Submodule.add_mem _ (hTst a b hab _ (hv' i)) ?_
    split_ifs
    · exact hv' b
    · exact Submodule.zero_mem _
  · intro i _
    exact (le_iSup S i) (hSmem i)

theorem finiteDimensional_comap_subtype {V : Type} [AddCommGroup V] [Module ℂ V]
    (S T : Submodule ℂ V) [FiniteDimensional ℂ T] : FiniteDimensional ℂ (T.comap S.subtype) := by
  refine FiniteDimensional.of_injective
    (LinearMap.codRestrict T (S.subtype ∘ₗ (T.comap S.subtype).subtype) fun x => x.2) ?_
  intro x y hxy
  have hv : ((x : S) : V) = ((y : S) : V) := congrArg (fun w : T => (w : V)) hxy
  exact Subtype.ext (Subtype.ext hv)

theorem locFin_sub (ε : Fin n → Bool) (X : GMod n) (S : Submodule ℂ X.V)
    (h : ∀ a b, ∀ x ∈ S, X.E a b x ∈ S) (hX : LocFin ε X.E) : LocFin ε (X.sub S h).E := by
  intro x
  obtain ⟨F, hF, hst, hx⟩ := hX x.1
  haveI := hF
  refine ⟨F.comap S.subtype, finiteDimensional_comap_subtype S F, ?_, hx⟩
  intro a b hab v hv
  exact hst a b hab v.1 hv

theorem intWt_tens (X : GMod n) (h : IntWt X) : IntWt (tens X) := by
  intro μ u hu hw a
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra hc
    exact hu (funext fun j => by_contra fun hj => hc ⟨j, hj⟩)
  have hw' : Formalism.REAL.IsWeight X.E (fun b => if b = i then μ b - 1 else μ b) (u i) := by
    intro b
    have hb : X.E b b (u i) + (if i = b then u b else 0) = (μ b : ℂ) • u i := congrFun (hw b) i
    by_cases hbi : b = i
    · subst hbi
      simp only [if_true] at hb ⊢
      rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul, ← hb]
      exact (add_sub_cancel_right _ _).symm
    · simp only [if_neg hbi, if_neg (Ne.symm hbi), add_zero] at hb ⊢
      exact hb
  obtain ⟨m, hm⟩ := h _ (u i) hi hw' a
  by_cases hai : a = i
  · subst hai
    simp only [if_true] at hm
    exact ⟨m + 1, by push_cast; linarith⟩
  · simp only [if_neg hai] at hm
    exact ⟨m, hm⟩

theorem intWt_sub (X : GMod n) (S : Submodule ℂ X.V) (h : ∀ a b, ∀ x ∈ S, X.E a b x ∈ S)
    (hX : IntWt X) : IntWt (X.sub S h) := by
  intro μ x hx hw a
  exact hX μ x.1 (fun h0 => hx (Subtype.ext h0)) (fun b => congrArg Subtype.val (hw b)) a

theorem locFin_step (ε : Fin n → Bool) (X : GMod n) (z : ℂ) (h : LocFin ε X.E) :
    LocFin ε (step X z).E := by
  exact locFin_sub ε (_root_.CompanionTheory.RgExh.tens X) _ _ (locFin_tens ε X h)

theorem intWt_step (X : GMod n) (z : ℂ) (h : IntWt X) : IntWt (step X z) := by
  exact intWt_sub (_root_.CompanionTheory.RgExh.tens X) _ _ (intWt_tens X h)

theorem pathFin :
    ∀ (n : ℕ) (ε : Fin n → Bool) (X : GMod n) (χ : Fin n → ℂ) (ss : List (Fin n)),
      (LocFin ε X.E → LocFin ε (path X χ ss).E) ∧ (IntWt X → IntWt (path X χ ss)) := by
  intro n ε X χ ss
  induction ss generalizing X χ with
  | nil => exact ⟨id, id⟩
  | cons s ss ih =>
    have h := ih (step X (χ s)) (χ + Pi.single s 1)
    exact ⟨fun hX => h.1 (locFin_step ε X (χ s) hX),
      fun hX => h.2 (intWt_step X (χ s) hX)⟩

end GlobalTheory.CompanionTheory.RgSteps
end
end
