module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Mathlib.Order.Sigma
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle021
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle052
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle002
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open Matrix ValuativeRel

noncomputable section

namespace GlobalTheory.SphBlock

theorem exists_eigen_at_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α : Type) [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (n : Type) [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (X : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)) (χ : kˣ →* ℂˣ) (x : IndSp e (piTensor σ)), x ≠ 0 → (∀ g ∈ KO k n, multiProd e σ g x = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • x) → ∃ w : PiTensorProduct ℂ X, w ≠ 0 ∧ ∀ a, ∀ h ∈ KO k (m a), piTensor σ (Pi.mulSingle a h) w = (χ (Matrix.GeneralLinearGroup.det h) : ℂ) • w := by
  intro k _ _ _ _ α _ _ m _ _ n _ _ e X _ _ σ χ x hx hK
  classical
  set f := x.1.1 with hf
  have hval : ∀ {d : Type} [Fintype d] [DecidableEq d] {g : GL d k}, g ∈ KO k d →
      valuation k (GeneralLinearGroup.det g : k) = 1 := by
    intro d _ _ g hg
    obtain ⟨g, rfl⟩ := hg
    have h1 : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap 𝒪[k] k) g) : kˣ) : k) =
        algebraMap 𝒪[k] k (GeneralLinearGroup.det g : 𝒪[k]ˣ) :=
      ((algebraMap 𝒪[k] k).map_det _).symm
    rw [h1]
    exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)
  have hfK : ∀ κ ∈ KO k n, f κ = (χ (GeneralLinearGroup.det κ) : ℂ) • f 1 := by
    intro κ hκ
    have h := congrArg (fun y : IndSp e (piTensor σ) => y.1.1 1) (hK κ hκ)
    have h2 : (multiProd e σ κ x).1.1 1 = f (1 * κ) := parInd_apply e (piTensor σ) κ 1 x
    rw [h2, one_mul] at h
    exact h
  refine ⟨f 1, ?_, ?_⟩
  · intro h0
    apply hx
    have hall : ∀ g, f g = 0 := by
      intro g
      obtain ⟨u, l, κ, hκ, rfl⟩ := UnitInd.exists_iwasawa e g
      let p : parab k e := ⟨(u : GL n k) * leviEmb k e l,
        mul_mem (unipRad_le_parab k e u.2) (leviEmb_mem_parab k e l)⟩
      have := parInd_law e (piTensor σ) x p κ
      change f ((u : GL n k) * leviEmb k e l * κ) = _ at this
      rw [this, show x.1.1 κ = f κ from rfl, hfK κ hκ, h0, smul_zero, map_zero, smul_zero]
    apply Subtype.ext; apply Subtype.ext; funext g
    exact hall g
  · intro a h hh
    set l : Levi k m := Pi.mulSingle a h with hl
    have hlK : ∀ b, l b ∈ KO k (m b) := by
      intro b
      by_cases hb : b = a
      · subst hb; simp [l, hh]
      · simp [l, Pi.mulSingle_eq_of_ne hb, one_mem]
    have hemb : leviEmb k e l ∈ KO k n := by
      have := (UnitInd.unip_mul_levi_mem_KO e (1 : unipRad k e) l).2 ⟨one_mem _, hlK⟩
      simpa using this
    have hdet : GeneralLinearGroup.det (leviEmb k e l) = GeneralLinearGroup.det h := by
      rw [det_leviEmb, Finset.prod_eq_single a]
      · simp [l]
      · intro b _ hb; simp [l, Pi.mulSingle_eq_of_ne hb]
      · simp
    have hδ : deltaHalf k m l = 1 := by
      rw [deltaHalf_apply]
      refine Finset.prod_eq_one fun b _ => isUnram_absPow k _ _ (hval (hlK b))
    let p : parab k e := ⟨leviEmb k e l, leviEmb_mem_parab k e l⟩
    have hlaw := parInd_law e (piTensor σ) x p 1
    have hp : leviProj k e p = l := leviProj_leviEmb k e l
    rw [mul_one, hp, hδ, Units.val_one, one_smul] at hlaw
    change f (leviEmb k e l) = piTensor σ l (f 1) at hlaw
    rw [hfK _ hemb, hdet] at hlaw
    exact hlaw.symm

end GlobalTheory.SphBlock
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

noncomputable section
open ValuativeRel Matrix GlobalTheory.SmGL.MultiIrr GlobalTheory.LocGL
open scoped TensorProduct

namespace GlobalTheory.SmGL.Stages

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ind₂_equiv_right {a b n V W U : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype n] [DecidableEq n] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U] (h : a ⊕ b ≃ n) (A : Representation ℂ (GL a k) V)
    {B : Representation ℂ (GL b k) W} {B' : Representation ℂ (GL b k) U} (φ : B.Equiv B') :
    Nonempty ((ind₂ h (extTensor A B)).Equiv (ind₂ h (extTensor A B'))) := by
  refine ⟨parIndEquiv _ (compEquiv (.mk (φ.toLinearEquiv.lTensor V) fun g => ?_) _)⟩
  refine TensorProduct.ext' fun v w => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.lTensor_tmul, extTensor_tmul]
  congr 1
  exact φ.toIntertwiningMap.isIntertwining _ _ _ _

theorem piTensor_tmulEquivDep {β₀ β₁ : Type} {Γ X : β₀ ⊕ₗ β₁ → Type} [∀ c, Group (Γ c)]
    [∀ c, AddCommGroup (X c)] [∀ c, Module ℂ (X c)] (ρ : ∀ c, Representation ℂ (Γ c) (X c)) (g : ∀ c, Γ c)
    (x : (⨂[ℂ] i, X (toLex (.inl i))) ⊗[ℂ] (⨂[ℂ] j, X (toLex (.inr j)))) :
    piTensor ρ g (PiTensorProduct.tmulEquivDep ℂ (fun c => X (toLex c)) x) =
      PiTensorProduct.tmulEquivDep ℂ (fun c => X (toLex c))
      (TensorProduct.map (piTensor (fun i => ρ (toLex (.inl i))) fun i => g (toLex (.inl i)))
        (piTensor (fun j => ρ (toLex (.inr j))) fun j => g (toLex (.inr j))) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact map_zero (piTensor ρ g)
  | add x y hx hy => simp only [map_add (f := _)]; exact (map_add (piTensor ρ g) _ _).trans (by rw [hx, hy]; rfl)
  | tmul v w =>
    induction v using PiTensorProduct.induction_on with
    | add v v' hv hv' => simp only [TensorProduct.add_tmul, map_add (f := _)]; exact (map_add (piTensor ρ g) _ _).trans (by rw [hv, hv']; rfl)
    | smul_tprod c v =>
      induction w using PiTensorProduct.induction_on with
      | add w w' hw hw' => simp only [TensorProduct.tmul_add, map_add (f := _)]; exact (map_add (piTensor ρ g) _ _).trans (by rw [hw, hw']; rfl)
      | smul_tprod c' w =>
        have key : piTensor ρ g (PiTensorProduct.tmulEquivDep ℂ (fun c => X (toLex c))
            (PiTensorProduct.tprod ℂ v ⊗ₜ PiTensorProduct.tprod ℂ w)) =
            PiTensorProduct.tmulEquivDep ℂ (fun c => X (toLex c))
              (PiTensorProduct.tprod ℂ (fun a => ρ (toLex (.inl a)) (g (toLex (.inl a))) (v a)) ⊗ₜ
                PiTensorProduct.tprod ℂ (fun a => ρ (toLex (.inr a)) (g (toLex (.inr a))) (w a))) := by
          rw [PiTensorProduct.tmulEquivDep_apply, PiTensorProduct.tmulEquivDep_apply]
          refine (piTensor_tprod ρ g _).trans ?_
          congr 1
          funext i
          rcases i with i | i <;> rfl
        simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul, map_smul, TensorProduct.map_tmul,
          piTensor_tprod]
        rw [← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul',
          ← TensorProduct.smul_tmul', map_smul, map_smul, map_smul, map_smul, ← key]
        exact (LinearMap.map_smul _ _ _).trans (congrArg _ (LinearMap.map_smul _ _ _))

def splitEquiv {s : ℕ} (t : Fin (s + 1) → ℕ) :
    (Fin (t 0) ⊕ₗ Σₗ i : Fin s, Fin (t i.succ)) ≃ Σₗ a, Fin (t a) where
  toFun c := Sum.elim (fun j => toLex (⟨0, j⟩ : Σ a, Fin (t a)))
    (fun x => toLex (⟨(ofLex x).1.succ, (ofLex x).2⟩ : Σ a, Fin (t a))) (ofLex c)
  invFun c := Fin.cases (motive := fun a => Fin (t a) → Fin (t 0) ⊕ₗ Σₗ i : Fin s, Fin (t i.succ))
    (fun j => toLex (.inl j)) (fun i j => toLex (.inr (toLex ⟨i, j⟩))) (ofLex c).1 (ofLex c).2
  left_inv c := by
    rcases c with j | ⟨i, j⟩ <;> rfl
  right_inv c := by
    obtain ⟨a, j⟩ := c
    induction a using Fin.cases <;> rfl

theorem stages_equiv (s : ℕ) : ∀ (d t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ)
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (X : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (X a b)] [∀ a b, Module ℂ (X a b)]
    (ρ : ∀ a b, Representation ℂ (GL (Fin (d' a b)) k) (X a b)) (n : Type) [Fintype n] [DecidableEq n]
    (e : (Σ a, Fin (d a)) ≃ n),
    ∃ E : (Σ c : (Σₗ a, Fin (t a)), Fin (d' (ofLex c).1 (ofLex c).2)) ≃ n,
      Nonempty ((multiProd e fun a => multiProd (e' a) (ρ a)).Equiv
        (multiProd E fun c => ρ (ofLex c).1 (ofLex c).2)) := by
  induction s with
  | zero =>
    intro d t d' e' X _ _ ρ n _ _ e
    haveI : IsEmpty n := ⟨fun x => (e.symm x).1.elim0⟩
    haveI : IsEmpty (Σₗ a : Fin 0, Fin (t a)) := ⟨fun c => (ofLex c).1.elim0⟩
    haveI : IsEmpty (Σ c : (Σₗ a : Fin 0, Fin (t a)), Fin (d' (ofLex c).1 (ofLex c).2)) :=
      ⟨fun x => (ofLex x.1).1.elim0⟩
    let E : (Σ c : (Σₗ a : Fin 0, Fin (t a)), Fin (d' (ofLex c).1 (ofLex c).2)) ≃ n :=
      Equiv.equivOfIsEmpty _ _
    exact ⟨E, GlobalTheory.T.parabolicInductionProduct_equiv_of_no_blocks (k := k) _ _ _ _⟩
  | succ s ih =>
    intro d t d' e' X _ _ ρ n _ _ e
    have E1 := multiProd_succ_equiv (k := k) (m := fun a => Fin (d a))
      (X := fun a => IndSp (e' a) (piTensor (ρ a))) e fun a => multiProd (e' a) (ρ a)
    obtain ⟨E1⟩ := E1
    have E2 := ih (fun i => d i.succ) (fun i => t i.succ) (fun i => d' i.succ) (fun i => e' i.succ)
      (fun i => X i.succ) (fun i => ρ i.succ) _ (Equiv.refl _)
    obtain ⟨Er, ⟨E2⟩⟩ := E2
    let mS : Fin (t 0) ⊕ₗ (Σₗ i : Fin s, Fin (t i.succ)) → Type :=
      fun c => Fin (d' (ofLex (splitEquiv t c)).1 (ofLex (splitEquiv t c)).2)
    let Es : (Σ c, mS c) ≃ n := (Equiv.sumSigmaDistrib fun x => mS (toLex x)).trans
      ((Equiv.sumCongr (e' 0) Er).trans ((headTail _).trans e))
    have E4 := GlobalTheory.T.inductionInStages_twoFactors_equiv (k := k) (m := mS)
      (a := Fin (d 0)) (b := Σ i : Fin s, Fin (d i.succ)) (V := ⨂[ℂ] b, X 0 b) (W := ⨂[ℂ] c : Σₗ i : Fin s, Fin (t i.succ), X (ofLex c).1.succ (ofLex c).2)
      (U := ⨂[ℂ] c : Fin (t 0) ⊕ₗ (Σₗ i : Fin s, Fin (t i.succ)), X (ofLex (splitEquiv t c)).1 (ofLex (splitEquiv t c)).2) Es ((headTail _).trans e) (e' 0) Er
      (fun _ _ => rfl) (fun _ _ => rfl) (piTensor (ρ 0))
      (piTensor fun c : Σₗ i : Fin s, Fin (t i.succ) => ρ (ofLex c).1.succ (ofLex c).2)
      (piTensor fun c => ρ (ofLex (splitEquiv t c)).1 (ofLex (splitEquiv t c)).2)

      (PiTensorProduct.tmulEquivDep ℂ fun c => X (ofLex (splitEquiv t (toLex c))).1 (ofLex (splitEquiv t (toLex c))).2)
      fun g x => piTensor_tmulEquivDep (X := fun c => X (ofLex (splitEquiv t c)).1 (ofLex (splitEquiv t c)).2)
        (fun c => ρ (ofLex (splitEquiv t c)).1 (ofLex (splitEquiv t c)).2) g x
    obtain ⟨E4⟩ := E4
    have E2' : (multiProd (Equiv.refl _) fun i : Fin s => multiProd (e' i.succ) (ρ i.succ)).Equiv
        (parInd (m := fun j => mS (toLex (Sum.inr j))) Er (piTensor fun c : Σₗ i : Fin s, Fin (t i.succ) => ρ (ofLex c).1.succ (ofLex c).2)) := E2
    have E3 := ind₂_equiv_right ((headTail fun i => Fin (d i)).trans e)
      (parInd (α := Fin (t 0)) (m := fun i => mS (toLex (Sum.inl i))) (e' 0) (piTensor (ρ 0))) E2'
    obtain ⟨E3⟩ := E3
    let Esig : (Σ c : (Σₗ a, Fin (t a)), Fin (d' (ofLex c).1 (ofLex c).2)) ≃ n :=
      (Equiv.sigmaCongrLeft (β := fun c : Σₗ a, Fin (t a) => Fin (d' (ofLex c).1 (ofLex c).2))
        (splitEquiv t)).symm.trans Es
    have E5 := GlobalTheory.T.parabolicInductionProduct_block_renaming_equiv (k := k) (splitEquiv t) (GlobalTheory.T.lexSum_splitFirstBlock_strictMono s t) (splitEquiv t).surjective
      Esig Es (fun c' x => congrArg Es ((Equiv.sigmaCongrLeft
        (β := fun c : Σₗ a, Fin (t a) => Fin (d' (ofLex c).1 (ofLex c).2)) (splitEquiv t)).symm_apply_apply ⟨c', x⟩).symm) fun c => ρ (ofLex c).1 (ofLex c).2
    obtain ⟨E5⟩ := E5
    exact ⟨Esig, ⟨E1.symm.trans (E3.trans (E4.trans E5.symm))⟩⟩

theorem isSubquotient_multiProd_multiProd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (s n : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (t : Fin s → ℕ)
    (d' : ∀ a, Fin (t a) → ℕ) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (X : ∀ a, Fin (t a) → Type)
    [∀ a b, AddCommGroup (X a b)] [∀ a b, Module ℂ (X a b)]
    (ρ : ∀ a b, Representation ℂ (GL (Fin (d' a b)) k) (X a b)) (_ : ∀ a b, IsSmooth (ρ a b)) :
    ∃ E : (Σ c : Fin (∑ a, t a), Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) ≃ Fin n,
      IsSubquotient (multiProd e fun a => multiProd (e' a) (ρ a))
        (multiProd E fun c => ρ (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) := by
  have hφ := stages_equiv (k := k) s d t d' e' X ρ (Fin n) e
  obtain ⟨E0, ⟨φ⟩⟩ := hφ
  let F : Fin (∑ a, t a) ≃ Σₗ a, Fin (t a) := finSigmaFinEquiv.symm.trans toLex
  let E : (Σ c : Fin (∑ a, t a), Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) ≃ Fin n :=
    (Equiv.sigmaCongrLeft (β := fun c : Σₗ a, Fin (t a) => Fin (d' (ofLex c).1 (ofLex c).2)) F).trans E0
  have hψ := GlobalTheory.T.parabolicInductionProduct_block_renaming_equiv (k := k) F (GlobalTheory.T.finSigmaFinEquiv_symm_strictMono_toLex s t) F.surjective E0 E
    (fun _ _ => rfl) fun c => ρ (ofLex c).1 (ofLex c).2
  obtain ⟨ψ⟩ := hψ
  exact ⟨E, .of_injective (φ.trans ψ).toIntertwiningMap (φ.trans ψ).toLinearEquiv.injective⟩

end GlobalTheory.SmGL.Stages
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil


namespace GlobalTheory

namespace CentralSplit

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

noncomputable def prodOp (ρ : Representation ℂ G V) (z : G) (a : ℕ → ℂ) : ℕ → Module.End ℂ V
  | 0 => 1
  | m + 1 => prodOp ρ z a m * (ρ z - a m • 1)

noncomputable def prodScal (c : ℂ) (a : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1
  | m + 1 => prodScal c a m * (c - a m)

theorem prodOp_succ_apply (ρ : Representation ℂ G V) (z : G) (a : ℕ → ℂ) (m : ℕ) (v : V) :
    prodOp ρ z a (m + 1) v = prodOp ρ z a m (ρ z v - a m • v) := by
  simp [prodOp]

theorem prodOp_comm (ρ : Representation ℂ G V) (z : G) (hz : ∀ g, g * z = z * g) (a : ℕ → ℂ)
    (m : ℕ) (g : G) (v : V) : prodOp ρ z a m (ρ g v) = ρ g (prodOp ρ z a m v) := by
  induction m generalizing v with
  | zero => rfl
  | succ m ih =>
    have hzg : ρ z (ρ g v) = ρ g (ρ z v) := by
      rw [← Module.End.mul_apply, ← map_mul, ← hz, map_mul, Module.End.mul_apply]
    rw [prodOp_succ_apply, prodOp_succ_apply, hzg, ← LinearMap.map_smul (ρ g),
      ← LinearMap.map_sub (ρ g), ih]

theorem prodScal_ne_zero (c : ℂ) (a : ℕ → ℂ) (M : ℕ) (h : ∀ m < M, a m ≠ c) :
    ∀ m ≤ M, prodScal c a m ≠ 0 := by
  intro m hm
  induction m with
  | zero => simp [prodScal]
  | succ m ih =>
    simp only [prodScal]
    exact mul_ne_zero (ih (by omega)) (sub_ne_zero.2 (h m (by omega)).symm)

end CentralSplit


open CentralSplit in
theorem exists_intertwining_of_central_step : ∀ {G V Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G V) (τ : Representation ℂ G Y) (N : ℕ) (S : Fin (N + 1) → Subrepresentation ρ),
    Monotone S → S 0 = ⊥ → S (Fin.last N) = ⊤ → ∀ (z : G), (∀ g, g * z = z * g) →
    ∀ (t₀ : Fin N) (c : ℂ) (c' : Fin N → ℂ), (∀ t, t ≠ t₀ → c' t ≠ c) →
    (∀ t, t ≠ t₀ → ∀ y, subQuot (S t.succ) (S t.castSucc) z y = c' t • y) →
    Nonempty ((subQuot (S t₀.succ) (S t₀.castSucc)).Equiv τ) → (∀ y, τ z y = c • y) → Nontrivial Y →
    ∃ (φ : ρ.IntertwiningMap τ) (v : V), φ v ≠ 0 := by
  intro G V Y _ _ _ _ _ ρ τ N S _ _ htop z hz t₀ c c' hc' hstep hΨ hτ _
  obtain ⟨Ψ⟩ := hΨ
  set B := S t₀.succ with hBdef
  set A := S t₀.castSucc with hAdef
  let a : ℕ → ℂ := fun i => if h : i < N then c' ⟨i, h⟩ else 0
  let M := N - (t₀.val + 1)

  have hZ : ∀ y, subQuot B A z y = c • y := by
    intro y
    apply Ψ.toLinearEquiv.injective
    have h1 := Representation.IntertwiningMap.isIntertwining _ _ Ψ.toIntertwiningMap z y
    rw [Representation.Equiv.toLinearEquiv_apply, h1, hτ, map_smul, Representation.Equiv.toLinearEquiv_apply]
  have ha : ∀ m (hm : t₀.val + 1 + m < N), a (t₀.val + 1 + m) = c' ⟨t₀.val + 1 + m, by omega⟩ := by
    intro m hm; simp [a, hm]

  have L1 : ∀ m, ∀ (h : t₀.val + 1 + m < N + 1), ∀ v, v ∈ (S ⟨t₀.val + 1 + m, h⟩).toSubmodule →
      prodOp ρ z (fun i => a (t₀.val + 1 + i)) m v ∈ B.toSubmodule := by
    intro m
    induction m with
    | zero =>
      intro h v hv
      have e : (⟨t₀.val + 1 + 0, h⟩ : Fin (N + 1)) = t₀.succ := by ext; simp
      rw [e] at hv
      exact hv
    | succ m ih =>
      intro h v hv
      let t : Fin N := ⟨t₀.val + 1 + m, by omega⟩
      have ht : t ≠ t₀ := fun e => by have := congrArg Fin.val e; simp only [t] at this; omega
      have hvs : v ∈ (S t.succ).toSubmodule := by
        have : t.succ = ⟨t₀.val + 1 + (m + 1), h⟩ := by ext; simp [t]; omega
        rw [this]; exact hv
      have hq := hstep t ht (Submodule.Quotient.mk ⟨v, hvs⟩)
      have hmem : ρ z v - c' t • v ∈ (S t.castSucc).toSubmodule := by
        have e2 : subQuot (S t.succ) (S t.castSucc) z (Submodule.Quotient.mk ⟨v, hvs⟩) =
            Submodule.Quotient.mk ⟨ρ z v, (S t.succ).apply_mem_toSubmodule z hvs⟩ := rfl
        rw [e2, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hq
        simpa using hq
      rw [prodOp_succ_apply]
      have e3 : a (t₀.val + 1 + m) = c' t := ha m (by omega)
      simp only [e3]
      exact ih (by omega) _ hmem

  have L2 : ∀ m, ∀ b (hb : b ∈ B.toSubmodule), ∃ h' : prodOp ρ z (fun i => a (t₀.val + 1 + i)) m b ∈ B.toSubmodule,
      (Submodule.Quotient.mk ⟨_, h'⟩ : B.toSubmodule ⧸ A.toSubmodule.comap B.toSubmodule.subtype) =
        prodScal c (fun i => a (t₀.val + 1 + i)) m • Submodule.Quotient.mk ⟨b, hb⟩ := by
    intro m
    induction m with
    | zero => intro b hb; exact ⟨hb, by simp [prodOp, prodScal]⟩
    | succ m ih =>
      intro b hb
      have hb' : ρ z b - a (t₀.val + 1 + m) • b ∈ B.toSubmodule :=
        B.toSubmodule.sub_mem (B.apply_mem_toSubmodule z hb) (B.toSubmodule.smul_mem _ hb)
      obtain ⟨h', e⟩ := ih _ hb'
      refine ⟨by rw [prodOp_succ_apply]; exact h', ?_⟩
      have e4 : (Submodule.Quotient.mk ⟨_, hb'⟩ : B.toSubmodule ⧸ A.toSubmodule.comap B.toSubmodule.subtype) =
          (c - a (t₀.val + 1 + m)) • Submodule.Quotient.mk ⟨b, hb⟩ := by
        have e5 : subQuot B A z (Submodule.Quotient.mk ⟨b, hb⟩) =
            Submodule.Quotient.mk ⟨ρ z b, B.apply_mem_toSubmodule z hb⟩ := rfl
        rw [sub_smul, ← hZ, e5, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_sub]
        rfl
      simp only [prodOp_succ_apply, prodScal]
      rw [mul_smul, ← e4, ← e]
  set op := prodOp ρ z (fun i => a (t₀.val + 1 + i)) M with hop
  have hNM : t₀.val + 1 + M = N := by omega
  have hM : ∀ v, op v ∈ B.toSubmodule := by
    intro v
    refine L1 M (by omega) v ?_
    have e : (⟨t₀.val + 1 + M, by omega⟩ : Fin (N + 1)) = Fin.last N := by ext; simp [hNM]
    rw [e, htop]
    trivial
  have hlam : prodScal c (fun i => a (t₀.val + 1 + i)) M ≠ 0 := by
    refine prodScal_ne_zero c _ M (fun m hm => ?_) M le_rfl
    show a (t₀.val + 1 + m) ≠ c
    rw [ha m (by omega)]
    exact hc' _ (fun e => by have := congrArg Fin.val e; simp only at this; omega)
  let φlin : V →ₗ[ℂ] Y := Ψ.toLinearMap ∘ₗ (A.toSubmodule.comap B.toSubmodule.subtype).mkQ ∘ₗ
    LinearMap.codRestrict B.toSubmodule op hM
  have hφ : ∀ g v, φlin (ρ g v) = τ g (φlin v) := by
    intro g v
    have e6 : (LinearMap.codRestrict B.toSubmodule op hM) (ρ g v) =
        B.toRepresentation g (LinearMap.codRestrict B.toSubmodule op hM v) :=
      Subtype.ext (prodOp_comm ρ z hz _ M g v)
    show Ψ.toIntertwiningMap (Submodule.mkQ _ (LinearMap.codRestrict _ op hM (ρ g v))) =
      τ g (Ψ.toIntertwiningMap (Submodule.mkQ _ (LinearMap.codRestrict _ op hM v)))
    have e8 : Submodule.mkQ (A.toSubmodule.comap B.toSubmodule.subtype)
        (B.toRepresentation g (LinearMap.codRestrict B.toSubmodule op hM v)) =
        subQuot B A g (Submodule.mkQ _ (LinearMap.codRestrict B.toSubmodule op hM v)) := rfl
    rw [e6, e8]
    exact Representation.IntertwiningMap.isIntertwining _ _ Ψ.toIntertwiningMap g _
  refine ⟨φlin.intertwiningMap_of_isIntertwiningMap ρ τ hφ, ?_⟩
  obtain ⟨y, hy⟩ := exists_ne (0 : Y)
  obtain ⟨⟨b, hb⟩, hx⟩ := Submodule.Quotient.mk_surjective _ (Ψ.toLinearEquiv.symm y)
  obtain ⟨h', e⟩ := L2 M b hb
  refine ⟨b, ?_⟩
  rw [LinearMap.toIntertwiningMap]
  have e7 : φlin b = Ψ.toLinearEquiv (Submodule.Quotient.mk ⟨op b, h'⟩) := rfl
  rw [e7, e, hx, map_smul, LinearEquiv.apply_symm_apply]
  exact smul_ne_zero hlam hy

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil


namespace GlobalTheory.ExactIrr

theorem main : ∀ (H : Type) [Group H] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V) (P : ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y], Representation ℂ H Y → Prop), HasFiniteLength ρ → (∀ (Y Y' : Type) [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Y'] [Module ℂ Y'] (σ : Representation ℂ H Y) (σ' : Representation ℂ H Y') (f : σ.IntertwiningMap σ'), Function.Injective f → P Y σ → P Y' σ') → (∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (σ : Representation ℂ H Y), P Y σ → Nontrivial Y) → (∀ A B : Subrepresentation ρ, B ≤ A → P _ A.toRepresentation → P _ B.toRepresentation ∨ P _ (subQuot A B)) → P V ρ → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (σ : Representation ℂ H Y), σ.IsIrreducible ∧ IsSubquotient σ ρ ∧ P Y σ := by
  intro H _ V _ _ ρ P hl hinj hnt hsplit hP
  obtain ⟨hGT, hLT⟩ := (hasFiniteLength_iff_wellFounded ρ).1 hl
  let j : ρ.IntertwiningMap (⊤ : Subrepresentation ρ).toRepresentation :=
    ⟨LinearMap.codRestrict _ LinearMap.id (fun _ => trivial), fun _ => rfl⟩
  have hjinj : Function.Injective j := fun a b h => congrArg Subtype.val h
  have hTop : P _ (⊤ : Subrepresentation ρ).toRepresentation := hinj _ _ _ _ _ hjinj hP
  obtain ⟨A, hA, hAmin⟩ := hLT.has_min {A : Subrepresentation ρ | P _ A.toRepresentation} ⟨⊤, hTop⟩
  have hAbot : A ≠ ⊥ := by
    rintro rfl
    have hnt' := hnt _ _ hA
    have : Subsingleton (⊥ : Subrepresentation ρ).toSubmodule :=
      inferInstanceAs (Subsingleton (⊥ : Submodule ℂ V))
    exact not_subsingleton _ this
  obtain ⟨B, hBA, hB⟩ := exists_le_covBy_of_lt (bot_lt_iff_ne_bot.2 hAbot)
  rcases hsplit A B hB.le hA with h | h
  · exact absurd hB.lt (hAmin B h)
  · exact ⟨_, _, _, subQuot A B, isIrreducible_subQuot hB,
      ⟨A, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.Quotient.mk_surjective _⟩, h⟩

end GlobalTheory.ExactIrr
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.OffSQ

end GlobalTheory.OffSQ
end
