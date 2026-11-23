module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle297
import GroundTheory.LocalFields.LocalFourierHaar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
open scoped TensorProduct

namespace PositivityTheory.Rg.BcB.N3.PseStage

open PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Lin

variable {U X Y : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

theorem coordL_lTensor {ι : Type} [DecidableEq ι] (b : Module.Basis ι ℂ U) (g : X →ₗ[ℂ] Y) (v : U ⊗[ℂ] X) :
    TensorProduct.equivFinsuppOfBasisLeft b (LinearMap.lTensor U g v) =
      Finsupp.mapRange g (map_zero g) (TensorProduct.equivFinsuppOfBasisLeft b v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul u x =>
    ext i
    simp
  | add v w hv hw =>
    rw [map_add (f := _), map_add (f := _), hv, hw, map_add (f := _), Finsupp.mapRange_add (map_add g)]

theorem coordR_rTensor {ι : Type} [DecidableEq ι] (b : Module.Basis ι ℂ U) (g : X →ₗ[ℂ] Y) (v : X ⊗[ℂ] U) :
    TensorProduct.equivFinsuppOfBasisRight b (LinearMap.rTensor U g v) =
      Finsupp.mapRange g (map_zero g) (TensorProduct.equivFinsuppOfBasisRight b v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x u =>
    ext i
    simp
  | add v w hv hw =>
    rw [map_add (f := _), map_add (f := _), hv, hw, map_add (f := _), Finsupp.mapRange_add (map_add g)]

theorem eq_zero_of_lTensor {G : Type} [Group G] (π : G →* (X →ₗ[ℂ] X)) (S : Set G) (f : X →ₗ[ℂ] Y)
    (hf : ∀ x, (∀ h ∈ S, π h x = x) → f x = 0 → x = 0) (v : U ⊗[ℂ] X)
    (hv : ∀ h ∈ S, LinearMap.lTensor U (π h) v = v) (h0 : LinearMap.lTensor U f v = 0) : v = 0 := by
  classical
  let b := Module.Free.chooseBasis ℂ U
  have key : TensorProduct.equivFinsuppOfBasisLeft b v = 0 := by
    ext i
    have h1 : ∀ h ∈ S, π h (TensorProduct.equivFinsuppOfBasisLeft b v i) =
        TensorProduct.equivFinsuppOfBasisLeft b v i := by
      intro h hh
      have := congrArg (fun w => TensorProduct.equivFinsuppOfBasisLeft b w i) (hv h hh)
      simpa [coordL_lTensor] using this
    have h2 : f (TensorProduct.equivFinsuppOfBasisLeft b v i) = 0 := by
      have := congrArg (fun w => TensorProduct.equivFinsuppOfBasisLeft b w i) h0
      simpa [coordL_lTensor] using this
    simpa using hf _ h1 h2
  exact (LinearEquiv.map_eq_zero_iff _).mp key

theorem eq_zero_of_rTensor {G : Type} [Group G] (π : G →* (X →ₗ[ℂ] X)) (S : Set G) (f : X →ₗ[ℂ] Y)
    (hf : ∀ x, (∀ h ∈ S, π h x = x) → f x = 0 → x = 0) (v : X ⊗[ℂ] U)
    (hv : ∀ h ∈ S, LinearMap.rTensor U (π h) v = v) (h0 : LinearMap.rTensor U f v = 0) : v = 0 := by
  classical
  let b := Module.Free.chooseBasis ℂ U
  have key : TensorProduct.equivFinsuppOfBasisRight b v = 0 := by
    ext i
    have h1 : ∀ h ∈ S, π h (TensorProduct.equivFinsuppOfBasisRight b v i) =
        TensorProduct.equivFinsuppOfBasisRight b v i := by
      intro h hh
      have := congrArg (fun w => TensorProduct.equivFinsuppOfBasisRight b w i) (hv h hh)
      simpa [coordR_rTensor] using this
    have h2 : f (TensorProduct.equivFinsuppOfBasisRight b v i) = 0 := by
      have := congrArg (fun w => TensorProduct.equivFinsuppOfBasisRight b w i) h0
      simpa [coordR_rTensor] using this
    simpa using hf _ h1 h2
  exact (LinearEquiv.map_eq_zero_iff _).mp key

end Lin

variable {n : ℕ} {V W Z : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup Z] [Module ℂ Z]

theorem kinj_comp {π : Representation ℂ (GL (Fin n) k) V} {σ : Representation ℂ (GL (Fin n) k) W}
    {τ : Representation ℂ (GL (Fin n) k) Z} (S : π.IntertwiningMap σ) (T : σ.IntertwiningMap τ) (hS : KInj k S)
    (hT : KInj k T) : KInj k (T.comp S) := by
  intro v hv h0
  have hv' : ∀ h : ↥(KO k (Fin n)), π h v = ((1 : ↥(KO k (Fin n)) →* ℂˣ) h : ℂ) • v := hv
  have hSv : S v ∈ GlobalTheory.PRep.fixed σ (KO k (Fin n)) := by
    show ∀ h : ↥(KO k (Fin n)), σ h (S v) = ((1 : ↥(KO k (Fin n)) →* ℂˣ) h : ℂ) • S v
    intro h
    rw [← S.isIntertwining, hv' h, map_smul]
  exact hS v hv (hT (S v) hSv h0)

theorem kinj_equiv {π : Representation ℂ (GL (Fin n) k) V} {σ : Representation ℂ (GL (Fin n) k) W} (E : π.Equiv σ) :
    KInj k E.toIntertwiningMap := by
  intro v _ h
  simpa using h

end PositivityTheory.Rg.BcB.N3.PseStage

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel MeasureTheory

namespace PositivityTheory.Rg.BcB.N3.PseSat

open PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem injective_of_ne_zero {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W} (hi : π.IsIrreducible) (f : π.IntertwiningMap σ)
    (hf : f ≠ 0) : Function.Injective f := by
  have := hi
  let S : Subrepresentation π := ⟨LinearMap.ker f.toLinearMap, fun g v hv => by
    show f (π g v) = 0
    rw [f.isIntertwining]
    simp only [LinearMap.mem_ker] at hv
    simp [show f v = 0 from hv]⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top S with h | h
  · intro a b hab
    have : a - b ∈ S.toSubmodule := by
      show f.toLinearMap (a - b) = 0
      rw [map_sub]
      exact sub_eq_zero.2 hab
    rw [h] at this
    exact sub_eq_zero.1 this
  · exfalso
    apply hf
    ext v
    have : v ∈ S.toSubmodule := by rw [h]; trivial
    exact this

theorem isSubquotient_of_injective {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W} (f : π.IntertwiningMap σ) (hf : Function.Injective f) :
    IsSubquotient π σ := by
  let R : Subrepresentation σ := ⟨LinearMap.range f.toLinearMap, by
    rintro g _ ⟨v, rfl⟩
    exact ⟨π g v, by simpa using Representation.IntertwiningMap.isIntertwining _ _ f g v⟩⟩
  let e := LinearEquiv.ofInjective f.toLinearMap hf
  refine ⟨R, ⟨e.symm.toLinearMap, fun g => ?_⟩, e.symm.surjective⟩
  ext ⟨w, v, rfl⟩
  apply e.injective
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  show _ = f (π g (e.symm ⟨f v, v, rfl⟩))
  have h1 : e.symm ⟨f v, v, rfl⟩ = v := e.symm_apply_eq.2 rfl
  rw [h1, f.isIntertwining]
  rfl

theorem satPerm : SatPerm k := by
  intro n ξ η V _ _ π hs hi hsph hq ⟨f, hf⟩
  have hinj := injective_of_ne_zero hi f hf
  have hq' := isSubquotient_of_injective f hinj
  borelize (GL (Fin n) k)
  have h1 := GlobalTheory.CompanionTheory.SphSupp.isSatakeParameter_of_isSubquotient (k := k) ξ hq (μ := Measure.haar)
  have h2 := GlobalTheory.CompanionTheory.SphSupp.isSatakeParameter_of_isSubquotient (k := k) η hq' (μ := Measure.haar)
  have hK := (GlobalTheory.CompanionTheory.SphSupp.isSpherical_iff_fixedVectors π).1 hsph
  exact GroundTheory.Automorphic.Spherical.satakeParameter_unique hK h1 h2

end PositivityTheory.Rg.BcB.N3.PseSat
end
end
