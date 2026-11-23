module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle216
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle217
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle230
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle219
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle096
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle428
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle223
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle006
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical


theorem _root_.GlobalTheory.T.realComponent_central_definiteUnitary_eq_unit_scalar : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (S : HSp D) (x : DefSp S), x.Is → ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ∀ τ : D.what₂.Tau, ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ compAt θ τ (Formalism.L2.Theta.mt S z) = ζ • (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) := by
  first | exact @GlobalTheory.CenterScalar.center_scalar | exact GlobalTheory.CenterScalar.center_scalar | (intros; apply GlobalTheory.CenterScalar.center_scalar <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical


theorem _root_.GlobalTheory.T.weilOperator_sourceRealPoint_commute_heisenbergComb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ z ∈ GinfC S, ∀ c : WO S T →₀ ℂ, IsFinComb c → ∀ g : WO S T → ℂ, IsThetaFunO ψ S T g → om (z, 1) (comb ψ S T c g) = comb ψ S T c (om (z, 1) g) := by
  first | exact @GlobalTheory.SeeSaw.RealComm.om_comb | exact GlobalTheory.SeeSaw.RealComm.om_comb | (intros; apply GlobalTheory.SeeSaw.RealComm.om_comb <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finiteElements_act_fockVectors_through_datum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T) (k : KerDat S T), x.Is → y.Is → k.Is ψ θ x y → ∀ P, IsThetaFunO ψ S T (k.pt ψ θ x y P) ∧ ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ p : ℂ, k.om (g, h) (comb ψ S T k.c k.vac) = p • comb ψ S T k.c k.vac → k.om (g, h) (k.pt ψ θ x y P) = p • k.pt ψ θ x y P := by
  first | exact @GlobalTheory.FockFin.pt_finite | exact GlobalTheory.FockFin.pt_finite | (intros; apply GlobalTheory.FockFin.pt_finite <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section

namespace GlobalTheory.ProdLocInv

section Ops

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D)

def lOp (c : WO A S →₀ ℂ) (C : WO A S → WO S A' → ℂ) : WO A S → WO S A' → ℂ :=
  fun u v => comb ψ A S c (fun u' => C u' v) u

def rOp (c : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) : WO A S → WO S A' → ℂ :=
  fun u => comb ψ S A' c (C u)

theorem biComb_eq_lOp_rOp (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) :
    biComb ψ A S A' c c' C = lOp ψ A S A' c (rOp ψ A S A' c' C) := rfl

theorem lOp_rOp (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) :
    lOp ψ A S A' c (rOp ψ A S A' c' C) = rOp ψ A S A' c' (lOp ψ A S A' c C) := by
  funext u v
  simp only [lOp, rOp, comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem lOp_lOp (c d e : WO A S →₀ ℂ) (h : ∀ f, comb ψ A S e f = comb ψ A S c (comb ψ A S d f))
    (C : WO A S → WO S A' → ℂ) : lOp ψ A S A' c (lOp ψ A S A' d C) = lOp ψ A S A' e C := by
  funext u v
  exact congrFun (h fun u'' => C u'' v).symm u

theorem rOp_rOp (c d e : WO S A' →₀ ℂ) (h : ∀ f, comb ψ S A' e f = comb ψ S A' c (comb ψ S A' d f))
    (C : WO A S → WO S A' → ℂ) : rOp ψ A S A' c (rOp ψ A S A' d C) = rOp ψ A S A' e C := by
  funext u
  exact (h (C u)).symm

theorem lOp_comm (c d : WO A S →₀ ℂ) (h : ∀ f, comb ψ A S c (comb ψ A S d f) = comb ψ A S d (comb ψ A S c f))
    (C : WO A S → WO S A' → ℂ) : lOp ψ A S A' c (lOp ψ A S A' d C) = lOp ψ A S A' d (lOp ψ A S A' c C) := by
  funext u v
  exact congrFun (h fun u'' => C u'' v) u

theorem rOp_comm (c d : WO S A' →₀ ℂ) (h : ∀ f, comb ψ S A' c (comb ψ S A' d f) = comb ψ S A' d (comb ψ S A' c f))
    (C : WO A S → WO S A' → ℂ) : rOp ψ A S A' c (rOp ψ A S A' d C) = rOp ψ A S A' d (rOp ψ A S A' c C) := by
  funext u
  exact h (C u)

theorem biComb_comp (c d e : WO A S →₀ ℂ) (c' d' e' : WO S A' →₀ ℂ)
    (hl : ∀ f, comb ψ A S e f = comb ψ A S c (comb ψ A S d f))
    (hr : ∀ f, comb ψ S A' e' f = comb ψ S A' c' (comb ψ S A' d' f)) (C : WO A S → WO S A' → ℂ) :
    biComb ψ A S A' c c' (biComb ψ A S A' d d' C) = biComb ψ A S A' e e' C := by
  simp only [biComb_eq_lOp_rOp]
  rw [← lOp_rOp ψ A S A' d c', lOp_lOp ψ A S A' c d e hl, rOp_rOp ψ A S A' c' d' e' hr]

theorem biComb_comm (c d : WO A S →₀ ℂ) (c' d' : WO S A' →₀ ℂ)
    (hl : ∀ f, comb ψ A S c (comb ψ A S d f) = comb ψ A S d (comb ψ A S c f))
    (hr : ∀ f, comb ψ S A' c' (comb ψ S A' d' f) = comb ψ S A' d' (comb ψ S A' c' f)) (C : WO A S → WO S A' → ℂ) :
    biComb ψ A S A' c c' (biComb ψ A S A' d d' C) = biComb ψ A S A' d d' (biComb ψ A S A' c c' C) := by
  simp only [biComb_eq_lOp_rOp]
  rw [← lOp_rOp ψ A S A' d c', lOp_comm ψ A S A' c d hl, rOp_comm ψ A S A' c' d' hr, lOp_rOp ψ A S A' c d']

theorem comb_single_zero (T T' : HSp D) (f : WO T T' → ℂ) : comb ψ T T' (Finsupp.single 0 1) f = f := by
  classical
  funext w
  have h0 : symplOH T T' w 0 = 0 := by simp [symplOH, symplO, hO]
  simp [comb, heisO, h0]

end Ops

theorem comm_foldr {α ι : Type} (F : α → α) (H : ι → α → α) (l : List ι) (h : ∀ i ∈ l, ∀ x, F (H i x) = H i (F x))
    (x : α) : F (l.foldr H x) = l.foldr H (F x) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons]
    rw [h i (by simp), ih (fun j hj => h j (by simp [hj]))]

theorem foldr_mem {α ι : Type} (H : ι → α → α) (s : Set α) (l : List ι) (h : ∀ i ∈ l, ∀ x ∈ s, H i x ∈ s) (x : α)
    (hx : x ∈ s) : l.foldr H x ∈ s := by
  induction l with
  | nil => exact hx
  | cons i l ih => exact h i (by simp) _ (ih fun j hj => h j (by simp [hj]))

section Lists

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D)

theorem prodList {ι' : Type} (e₁ : ι' → WO A S →₀ ℂ) (e₂ : ι' → WO S A' →₀ ℂ) (l : List ι') :
    ∃ (e : WO A S →₀ ℂ) (e' : WO S A' →₀ ℂ),
      (∀ w ∈ e.support, w ∈ AddSubmonoid.closure (⋃ i ∈ l, ((e₁ i).support : Set (WO A S)))) ∧
      (∀ w ∈ e'.support, w ∈ AddSubmonoid.closure (⋃ i ∈ l, ((e₂ i).support : Set (WO S A')))) ∧
      ∀ C, biComb ψ A S A' e e' C = l.foldr (fun i C => biComb ψ A S A' (e₁ i) (e₂ i) C) C := by
  classical
  induction l with
  | nil =>
    refine ⟨Finsupp.single 0 1, Finsupp.single 0 1, ?_, ?_, fun C => ?_⟩
    · intro w hw
      rw [Finsupp.mem_support_single] at hw
      rw [hw.1]; exact zero_mem _
    · intro w hw
      rw [Finsupp.mem_support_single] at hw
      rw [hw.1]; exact zero_mem _
    · funext u v
      simp only [List.foldr_nil, biComb, comb_single_zero]
  | cons i l ih =>
    obtain ⟨e0, e0', hs, hs', hc⟩ := ih
    obtain ⟨c, hcs, hcf⟩ := (GlobalTheory.HeisComb.main D ψ A S).1 (e₁ i) e0
    obtain ⟨c', hcs', hcf'⟩ := (GlobalTheory.HeisComb.main D ψ S A').1 (e₂ i) e0'
    refine ⟨c, c', ?_, ?_, fun C => ?_⟩
    · intro w hw
      obtain ⟨x, hx, y, hy, rfl⟩ := hcs w hw
      refine add_mem (AddSubmonoid.subset_closure ?_) (AddSubmonoid.closure_mono ?_ (hs y hy))
      · simp only [Set.mem_iUnion]
        exact ⟨i, by simp, hx⟩
      · intro z hz
        simp only [Set.mem_iUnion] at hz ⊢
        obtain ⟨j, hj, hz⟩ := hz
        exact ⟨j, List.mem_cons_of_mem _ hj, hz⟩
    · intro w hw
      obtain ⟨x, hx, y, hy, rfl⟩ := hcs' w hw
      refine add_mem (AddSubmonoid.subset_closure ?_) (AddSubmonoid.closure_mono ?_ (hs' y hy))
      · simp only [Set.mem_iUnion]
        exact ⟨i, by simp, hx⟩
      · intro z hz
        simp only [Set.mem_iUnion] at hz ⊢
        obtain ⟨j, hj, hz⟩ := hz
        exact ⟨j, List.mem_cons_of_mem _ hj, hz⟩
    · rw [List.foldr_cons, ← hc]
      exact (biComb_comp ψ A S A' _ _ _ _ _ _ hcf hcf' C).symm

theorem keyList {ι' : Type} (e₁ g₁ : ι' → WO A S →₀ ℂ) (e₂ g₂ : ι' → WO S A' →₀ ℂ)
    (Cl Vl : ι' → Set (WO A S → WO S A' → ℂ)) (l : List ι') (hl : l.Nodup)
    (horth : ∀ i ∈ l, ∀ i' ∈ l, i ≠ i' → (∀ x, x ∈ (e₁ i).support ∨ x ∈ (g₁ i).support → ∀ y ∈ (e₁ i').support,
      symplO A S x y = 0) ∧ ∀ x, x ∈ (e₂ i).support ∨ x ∈ (g₂ i).support → ∀ y ∈ (e₂ i').support, symplO S A' x y = 0)
    (hloc : ∀ i ∈ l, ∀ C ∈ Cl i, biComb ψ A S A' (e₁ i) (e₂ i) C ∈ Vl i ∧
      C = biComb ψ A S A' (g₁ i) (g₂ i) (biComb ψ A S A' (e₁ i) (e₂ i) C))
    (hstab : ∀ i ∈ l, ∀ i' ∈ l, i ≠ i' → ∀ C ∈ Cl i, biComb ψ A S A' (e₁ i') (e₂ i') C ∈ Cl i)
    (C : WO A S → WO S A' → ℂ) (hC : ∀ i ∈ l, C ∈ Cl i) :
    (∀ i ∈ l, l.foldr (fun i C => biComb ψ A S A' (e₁ i) (e₂ i) C) C ∈ Vl i) ∧
      C = l.foldr (fun i C => biComb ψ A S A' (g₁ i) (g₂ i) C)
        (l.foldr (fun i C => biComb ψ A S A' (e₁ i) (e₂ i) C) C) := by
  induction l generalizing C with
  | nil => simp
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    have ih' := ih hl.2 (fun a ha b hb hab => horth a (by simp [ha]) b (by simp [hb]) hab)
      (fun a ha => hloc a (by simp [ha])) (fun a ha b hb hab => hstab a (by simp [ha]) b (by simp [hb]) hab)
    have hne : ∀ j ∈ l, i ≠ j := fun j hj h => hl.1 (h ▸ hj)
    have hEE : ∀ j ∈ l, ∀ Y, biComb ψ A S A' (e₁ i) (e₂ i) (biComb ψ A S A' (e₁ j) (e₂ j) Y) =
        biComb ψ A S A' (e₁ j) (e₂ j) (biComb ψ A S A' (e₁ i) (e₂ i) Y) := by
      intro j hj Y
      obtain ⟨h1, h2⟩ := horth i (by simp) j (by simp [hj]) (hne j hj)
      exact biComb_comm ψ A S A' _ _ _ _
        ((GlobalTheory.HeisComb.main D ψ A S).2.1 _ _ fun x hx y hy => h1 x (Or.inl hx) y hy)
        ((GlobalTheory.HeisComb.main D ψ S A').2.1 _ _ fun x hx y hy => h2 x (Or.inl hx) y hy) Y
    have hGE : ∀ j ∈ l, ∀ Y, biComb ψ A S A' (e₁ i) (e₂ i) (biComb ψ A S A' (g₁ j) (g₂ j) Y) =
        biComb ψ A S A' (g₁ j) (g₂ j) (biComb ψ A S A' (e₁ i) (e₂ i) Y) := by
      intro j hj Y
      obtain ⟨h1, h2⟩ := horth j (by simp [hj]) i (by simp) (hne j hj).symm
      exact (biComb_comm ψ A S A' _ _ _ _
        ((GlobalTheory.HeisComb.main D ψ A S).2.1 (g₁ j) (e₁ i) fun x hx y hy => h1 x (Or.inr hx) y hy)
        ((GlobalTheory.HeisComb.main D ψ S A').2.1 (g₂ j) (e₂ i) fun x hx y hy => h2 x (Or.inr hx) y hy) Y).symm
    have hEL := comm_foldr (biComb ψ A S A' (e₁ i) (e₂ i)) (fun j C => biComb ψ A S A' (e₁ j) (e₂ j) C) l hEE
    have hGL := comm_foldr (biComb ψ A S A' (e₁ i) (e₂ i)) (fun j C => biComb ψ A S A' (g₁ j) (g₂ j) C) l hGE
    have hCi : C ∈ Cl i := hC i (by simp)
    have hstabL : l.foldr (fun j C => biComb ψ A S A' (e₁ j) (e₂ j) C) C ∈ Cl i :=
      foldr_mem _ (Cl i) l (fun j hj Y hY => hstab i (by simp) j (by simp [hj]) (hne j hj) Y hY) C hCi
    obtain ⟨-, ihC⟩ := ih' C (fun j hj => hC j (by simp [hj]))
    obtain ⟨ihV2, -⟩ := ih' (biComb ψ A S A' (e₁ i) (e₂ i) C)
      (fun j hj => hstab j (by simp [hj]) i (by simp) (hne j hj).symm C (hC j (by simp [hj])))
    refine ⟨fun j hj => ?_, ?_⟩
    · simp only [List.foldr_cons]
      rcases List.mem_cons.1 hj with h | hj
      · subst h
        exact (hloc _ (by simp) _ hstabL).1
      · rw [hEL]
        exact ihV2 j hj
    · simp only [List.foldr_cons]
      rw [← hGL, ← ihC]
      exact (hloc i (by simp) C hCi).2

end Lists

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (ι' P : Type) (l : List ι') (X : P → WO A S → WO S A' → ℂ) (e₁ g₁ : ι' → WO A S →₀ ℂ) (e₂ g₂ : ι' → WO S A' →₀ ℂ) (Cl Vl : ι' → Set (WO A S → WO S A' → ℂ)), l.Nodup → (∀ i ∈ l, ∀ i' ∈ l, i ≠ i' → (∀ x, x ∈ (e₁ i).support ∨ x ∈ (g₁ i).support → ∀ y ∈ (e₁ i').support, symplO A S x y = 0) ∧ ∀ x, x ∈ (e₂ i).support ∨ x ∈ (g₂ i).support → ∀ y ∈ (e₂ i').support, symplO S A' x y = 0) → (∀ i ∈ l, ∀ p, X p ∈ Cl i) → (∀ i ∈ l, ∀ C ∈ Cl i, biComb ψ A S A' (e₁ i) (e₂ i) C ∈ Vl i ∧ C = biComb ψ A S A' (g₁ i) (g₂ i) (biComb ψ A S A' (e₁ i) (e₂ i) C)) → (∀ i ∈ l, ∀ i' ∈ l, i ≠ i' → ∀ C ∈ Cl i, biComb ψ A S A' (e₁ i') (e₂ i') C ∈ Cl i) → ∃ (e : WO A S →₀ ℂ) (e' : WO S A' →₀ ℂ), (∀ w ∈ e.support, w ∈ AddSubmonoid.closure (⋃ i ∈ l, ((e₁ i).support : Set (WO A S)))) ∧ (∀ w ∈ e'.support, w ∈ AddSubmonoid.closure (⋃ i ∈ l, ((e₂ i).support : Set (WO S A')))) ∧ ∀ p, (∀ i ∈ l, biComb ψ A S A' e e' (X p) ∈ Vl i) ∧ X p = l.foldr (fun i C => biComb ψ A S A' (g₁ i) (g₂ i) C) (biComb ψ A S A' e e' (X p)) := by
  intro D ψ A S A' ι' P l X e₁ g₁ e₂ g₂ Cl Vl hl horth hX hloc hstab
  obtain ⟨e, e', hs, hs', hc⟩ := prodList ψ A S A' e₁ e₂ l
  refine ⟨e, e', hs, hs', fun p => ?_⟩
  rw [hc]
  exact keyList ψ A S A' e₁ g₁ e₂ g₂ Cl Vl l hl horth hloc hstab (X p) fun i hi => hX i hi p

end GlobalTheory.ProdLocInv
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.isCompact_realPoints_of_definiteHermitianSpaceData : ∀ (D : D7) (A : HSp D) (x : DefSp A), x.Is → IsCompact (GinfC A : Set (GA D A)) := by
  first | exact @GlobalTheory.SeeSaw.isCompact_ginfC_of_defSp | exact GlobalTheory.SeeSaw.isCompact_ginfC_of_defSp | (intros; apply GlobalTheory.SeeSaw.isCompact_ginfC_of_defSp <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.orth_allHeisenbergTranslates_of_orth_real_latticeVacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ vac, IsVacO ψ θ S T x.s y.s x.L y.L vac → ∀ (v : VolM D T.rank S.rank) f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T x.L y.L fun _ => True) f → (∀ u : WO S T, u.map (finPart D) = 0 → thPair v.μ v.𝓕 f (heisO ψ S T u vac) = 0) → ∀ u : WO S T, thPair v.μ v.𝓕 f (heisO ψ S T u vac) = 0 := by
  first | exact @GlobalTheory.FinOrth.orth_all | exact GlobalTheory.FinOrth.orth_all | (intros; apply GlobalTheory.FinOrth.orth_all <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical


theorem _root_.GlobalTheory.T.pureTensorFock_unitScaledBasis_monomial : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ ζ : D.what₂.Tau → ℂ, (∀ τ, ‖ζ τ‖ = 1) → ∀ α : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T x.s y.s (fun τ => ζ τ • x.B τ) y.B f (MvPolynomial.monomial α 1) = (∏ τ, (if (x.s τ = 1 ↔ y.s τ = 1) then (ζ τ)⁻¹ else ζ τ) ^ (∑ v ∈ α.support with v.1 = τ, α v)) • pureTensorO ψ θ S T x.s y.s x.B y.B f (MvPolynomial.monomial α 1) := by
  first | exact @GlobalTheory.FockScal.pureTensorO_scal | exact GlobalTheory.FockScal.pureTensorO_scal | (intros; apply GlobalTheory.FockScal.pureTensorO_scal <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.orth_realHeisenbergTranslates_vacuum_of_orth_fock : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ vac, IsVacO ψ θ S T x.s y.s x.L y.L vac → ∀ (v : VolM D T.rank S.rank) f, IsThetaFunO ψ S T f → (∀ P, thPair v.μ v.𝓕 f (pureTensorO ψ θ S T x.s y.s x.B y.B vac P) = 0) → ∀ u : WO S T, u.map (finPart D) = 0 → thPair v.μ v.𝓕 f (heisO ψ S T u vac) = 0 := by
  first | exact @GlobalTheory.FockRealOrth.orth_real_translate | exact GlobalTheory.FockRealOrth.orth_real_translate | (intros; apply GlobalTheory.FockRealOrth.orth_real_translate <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff Topology


theorem _root_.GlobalTheory.T.hasDerivAt_sobolevThetaForm_heisenberg_along_real_line : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (ℓ : (WO S T → ℂ) → ℂ), IsSobForm ψ θ S T ℓ → ∀ f, IsThetaFunO ψ S T f → ∀ M : ℝ →+ WO S T, Continuous M → (∀ s, (M s).map (finPart D) = 0) → ∀ w : WO S T, HasDerivAt (fun s : ℝ => ℓ (heisO ψ S T (w + M s) f)) (ℓ (heisO ψ S T w (fun p => deriv (fun s : ℝ => heisO ψ S T (M s) f p) 0)) - deriv (fun s : ℝ => ψ (symplOH S T w (M s))) 0 * ℓ (heisO ψ S T w f)) 0 := by
  first | exact @GlobalTheory.MatCoeffDeriv.hasDerivAt_form_heisO_line | exact GlobalTheory.MatCoeffDeriv.hasDerivAt_form_heisO_line | (intros; apply GlobalTheory.MatCoeffDeriv.hasDerivAt_form_heisO_line <;> assumption)
end

section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.compactAverageSchwartzProjection_mem_adelicSchwartz : ∀ (D : D7), ∀ θ : InfFam D, IsInfFam θ → ∀ (T : HSp D) (n : ℕ) (K : Subgroup (GA D T)), IsCompact (K : Set (GA D T)) → ∀ ν : Measure K, IsProbabilityMeasure ν → ∀ Φ ∈ schwartzA θ T.rank n, projS ν Φ ∈ schwartzA θ T.rank n := by
  first | exact @GlobalTheory.CompactAvgSchwartz.projS_mem | exact GlobalTheory.CompactAvgSchwartz.projS_mem | (intros; apply GlobalTheory.CompactAvgSchwartz.projS_mem <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.MultRapid

theorem multT_apply_rapidDec : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (θ : InfFam D), IsInfFam θ → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ F ∈ MultT θ M J χ, ∀ v : SmT M, IsAutFunSm θ V (F v) ∧ IsCuspFun V (F v) ∧ GlobalTheory.Grow.RapidDec V (F v) := by
  intro hP D V S M θ hθ J χ F hF v
  obtain ⟨ha, hc⟩ := GlobalTheory.PairLift.LowAllPf.multT_apply_smooth_cusp θ M J χ F hF v
  exact ⟨ha, hc, GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ ha hc⟩

end GlobalTheory.ChainOnto.MultRapid
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

theorem _root_.GlobalTheory.T.exists_flag_dual_basis_selfDualLatticeAtPlace : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a), Tame D v → ∀ M : AddSubgroup (Fin S.rank → AE D), IsSDAt S v M → ∃ b : Mx D ρ ρ, (∀ i j, j < i → b i j = 0) ∧ (∀ i j, b i j ∈ idAt D (· = v)) ∧ (∀ i, (fun k => (d.jX * b) k i) ∈ M) ∧ ∃ c' : Mx D S.rank ρ, (∀ i, (fun k => c' k i) ∈ M) ∧ adj c' * (gA S * (d.jX * b)) = ε • (1 : Mx D ρ ρ) := by
  intro D S S₀ ρ d v ε hεε hεc hεI hε ht M ⟨hsupp, ⟨m, hm, hmul⟩, hdual⟩
  obtain ⟨K, hK, hint⟩ := GlobalTheory.IwaFlag.exists_nat_isIntegral_fin
    (Sum.elim (fun p : Fin S.rank × Fin ρ => d.e p.1 p.2)
      (fun p : Fin S.rank × Fin ρ => d.e' p.1 p.2))
  have hcol (z : Fin S.rank → D.host.E) (hz : ∀ l, IsIntegral ℤ ((K : D.host.E) * z l)) :
      (fun l => ((m * K : ℕ) : AE D) * ε * incA D (z l)) ∈ M := by
    have hscale : (fun l => ((m * K : ℕ) : AE D) * ε * incA D (z l)) =
        (m : AE D) • fun l => ε * incA D ((K : D.host.E) * z l) := by
      funext l
      rw [Pi.smul_apply, smul_eq_mul, RingHom.map_mul, map_natCast, Nat.cast_mul]
      ring
    rw [hscale]
    exact hmul _ fun l => GlobalTheory.IwaFlag.mul_incA_mem hεI (hz l)
  have hflag := GlobalTheory.IwaFlag.exists_flag_dual_matrix
    (c := cA D) (O := GlobalTheory.IwaFlag.intGrpAt D v) (M := M) (gA S)
    cA_cA hεε hεc hεI (fun a ha => (hε a).1 ha.1)
    (fun _ ha _ hb => GlobalTheory.IwaFlag.mul_mem_intAt ha hb)
    (fun a ha => ⟨(hε _).2 (by rw [← hεc, ← RingHom.map_mul, (hε a).1 ha.1]),
      (FrameLat.cA_int_iff a).2 ha.2⟩)
    (GlobalTheory.IwaFlag.princ_intGrpAt hεε hεc hεI hε ht)
    (fun y hy i => (hε _).1 (hsupp y hy i))
    (fun y hy => hdual y fun i => (hε _).2 (hy i)) d.jX d.jY d.gram_YX (m * K) (Nat.mul_pos hm hK)
    (fun k => hcol (fun l => d.e l k) fun l => hint (Sum.inl (l, k)))
    (fun k => hcol (fun l => d.e' l k) fun l => hint (Sum.inr (l, k)))
  obtain ⟨b, h1, h2, h3, c', h4, h5⟩ := hflag
  exact ⟨b, h1, fun i j => (hε _).2 (h2 i j), h3, c', h4, h5⟩
end
