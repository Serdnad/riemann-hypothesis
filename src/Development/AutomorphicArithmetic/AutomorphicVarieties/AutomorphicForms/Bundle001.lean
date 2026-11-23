module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
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

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep
open scoped TensorProduct

namespace UpperTheory.V.TR

variable {E : Type} [Field E] [NumberField E] {a : ℕ}


variable (E a) in
def regFun : Subalgebra ℂ (GL (Fin a) (Rinf E) → ℂ) :=
  Algebra.adjoin ℂ ({f | ∃ v i j, f = fun y => ((y.val i j v : ℝ) : ℂ)} ∪ {f | ∃ v, f = fun y => ((y.val.det v : ℝ) : ℂ)⁻¹})


variable (E a) in
structure AlgRep where

  d : ℕ

  mat : GL (Fin a) (Rinf E) →* Matrix (Fin d) (Fin d) ℂ
  reg : ∀ i j, (fun y => mat y i j) ∈ regFun E a
  pos : 0 < d
  irred : ∀ W : Submodule ℂ (Fin d → ℂ), (∀ y, ∀ v ∈ W, mat y *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤



open Classical in
def AlgRep.HasInfChar (Ξ : AlgRep E a) (v : InfinitePlace E) (m : Multiset ℂ) : Prop :=
  let dmat (X : Lie E a) : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ :=
    Matrix.of fun i j =>
      fderiv ℝ (fun x : Lie E a => if h : IsUnit (Matrix.of x) then Ξ.mat h.unit i j else 0)
        (oneL E a) X
  Multiset.card m = a ∧ ∀ u : ℂ,
    Formalism.REAL.qdet (fun i j => dmat (toL (Matrix.single i j (Pi.single v 1))))
        (u + ((a : ℂ) - 1) / 2) =
    (m.map (u + ·)).prod • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)



section Complex

omit [NumberField E]

variable {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
  (κ : Kinf E a → Module.End ℂ M) (L : Lie E a →ₗ[ℝ] Module.End ℂ M)

end Complex

variable [IsTotallyReal E]


end UpperTheory.V.TR

namespace UpperTheory.V.Af

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def levelRep (Γ : Subgroup (GL (Fin a) E)) (U : Subgroup (GL (Fin a) (Af E))) {d : ℕ}
    (ξ : GL (Fin a) E →* Matrix (Fin d) (Fin d) ℂ) :
    Representation ℂ ↥Γ ((GL (Fin a) (Af E) ⧸ U) → Fin d → ℂ) where
  toFun γ :=
    { toFun := fun f x => ξ γ *ᵥ f ((GeneralLinearGroup.map (algebraMap E (Af E)) γ.1)⁻¹ • x)
      map_add' := fun f g => funext fun x => by simp [Matrix.mulVec_add]
      map_smul' := fun c f => funext fun x => by simp [Matrix.mulVec_smul] }
  map_one' := by ext f x; simp
  map_mul' γ δ := by ext f x; simp [mul_smul]

def cohDim (Γ : Subgroup (GL (Fin a) E)) (U : Subgroup (GL (Fin a) (Af E))) {d : ℕ}
    (ξ : GL (Fin a) E →* Matrix (Fin d) (Fin d) ℂ) : Cardinal :=
  Cardinal.sum fun q : ℕ => Module.rank ℂ (groupCohomology (Rep.of (levelRep Γ U ξ)) q)

variable [_root_.NumberField.IsTotallyComplex E]

def ratC (Ξ : GlobalTheory.GKCoh.AlgRep E a) : GL (Fin a) E →* Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ :=
  Ξ.mat.comp ((GeneralLinearGroup.map (pInf E)).comp (ratGL E a))


omit [_root_.NumberField.IsTotallyComplex E] in
def AlgInfChar (Ξ : GlobalTheory.GKCoh.AlgRep E a) (τ : E →+* ℂ) (m : Multiset ℂ) : Prop :=
  Multiset.card m = a ∧ ∀ u : ℂ, Formalism.REAL.qdet (fun i j => (1 / 2 : ℂ) • (Ξ.dmat (toL (Matrix.single i j (atEmb τ 1))) -
      Complex.I • Ξ.dmat (toL (Matrix.single i j (atEmb τ Complex.I))))) (u + ((a : ℂ) - 1) / 2) =
    (m.map (u + ·)).prod • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)

def IsFinComp (π : CuspSub E a) (σ : SmIrr (GL (Fin a) (Af E))) : Prop :=
  ∃ f : σ.V →ₗ[ℂ] π.V, f ≠ 0 ∧ ∀ g v, f (σ.ρ g v) = π.finPart g (f v)


omit [_root_.NumberField.IsTotallyComplex E] in
def IsConjBy (σ : ℂ ≃+* ℂ) (τ τ' : SmIrr (GL (Fin a) (Af E))) : Prop :=
  ∃ T : τ.V ≃+ τ'.V, (∀ (c : ℂ) v, T (c • v) = σ c • T v) ∧ ∀ g v, T (τ.ρ g v) = τ'.ρ g (T v)

end UpperTheory.V.Af
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Neutral.B1 GlobalTheory.CuspRep Formalism.L2.Host

namespace UpperTheory.V.Af

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ}

def IsInvTOf (π π' : TR.CuspSub F a) : Prop :=
  ∃ e : π.V ≃ₗ[ℂ] π'.V, (∀ k φ, π'.op (.fin k) (e φ) = e (π.op (.fin (invT a (Af F) k)) φ)) ∧
    (∀ k φ, π'.op (.cpt k) (e φ) = e (π.op (.cpt k) φ)) ∧
    ∀ X φ, π'.op (.lie X) (e φ) = e (π.op (.lie (TR.toL (-(Matrix.of X)ᵀ))) φ)

def IsTwistOf (π : TR.CuspSub F a) (χ : HChar F) (π' : TR.CuspSub F a) : Prop :=
  ∃ (e : π.V ≃ₗ[ℂ] π'.V) (d : TR.Rinf F →ₗ[ℝ] ℂ),
    (∀ (z : TR.Rinf F) (u : (TR.Rinf F)ˣ), (∀ v, u.val v = Real.exp (z v)) →
      ((χ.1 (TR.infId F u) : ℂˣ) : ℂ) = Complex.exp (d z)) ∧
    (∀ k φ, π'.op (.fin k) (e φ) = ((chiDet a χ (finGL F a k) : ℂˣ) : ℂ) • e (π.op (.fin k) φ)) ∧
    (∀ k φ, π'.op (.cpt k) (e φ) =
      ((chiDet a χ (TR.infGL F a (Unitary.toUnits k)) : ℂˣ) : ℂ) • e (π.op (.cpt k) φ)) ∧
    ∀ X φ, π'.op (.lie X) (e φ) = e (π.op (.lie X) φ) + d (Matrix.of X).trace • e φ

theorem isSelfDualBy_of_iso {π π₁ π₂ : TR.CuspSub F a} {χ : HChar F} (B : π.V →ₗ[ℂ] π.V →ₗ[ℂ] ℂ)
    (hl : ∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) (hr : ∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0)
    (hf : ∀ k φ ψ, B (π.op (.fin k) φ) (π.op (.fin (invT a (Af F) k)) ψ) = B φ ψ)
    (hc : ∀ k φ ψ, B (π.op (.cpt k) φ) (π.op (.cpt k) ψ) = B φ ψ)
    (hX : ∀ X φ ψ, B (π.op (.lie X) φ) ψ + B φ (π.op (.lie (TR.toL (-(Matrix.of X)ᵀ))) ψ) = 0)
    (h₁ : IsInvTOf π π₁) (h₂ : IsTwistOf π₁ χ π₂) (h : π.Iso π₂) : π.IsSelfDualBy χ := by
  obtain ⟨e₁, f₁, c₁, x₁⟩ := h₁
  obtain ⟨e₂, d, hd, f₂, c₂, x₂⟩ := h₂
  obtain ⟨T, hT⟩ := h
  let S : π.V ≃ₗ[ℂ] π.V := (e₁.trans e₂).trans T.symm
  have hS : ∀ ψ, T (S ψ) = e₂ (e₁ ψ) := fun ψ => T.apply_symm_apply _
  refine ⟨B.compl₂ S.symm.toLinearMap, d, fun φ h => hl φ fun ψ => ?_, fun ψ h => ?_, hd, fun k φ ψ => ?_,
    fun k φ ψ => ?_, fun X φ ψ => ?_⟩
  · simpa using h (S ψ)
  · exact S.symm.map_eq_zero_iff.1 (hr _ h)
  · obtain ⟨ψ, rfl⟩ := S.surjective ψ
    have e : π.op (.fin k) (S ψ) = S (((chiDet a χ (finGL F a k) : ℂˣ) : ℂ) • π.op (.fin (invT a (Af F) k)) ψ) :=
      T.injective (by rw [hT, hS, hS, f₂, f₁, map_smul, map_smul])
    simp [e, hf]
  · obtain ⟨ψ, rfl⟩ := S.surjective ψ
    have e : π.op (.cpt k) (S ψ) =
        S (((chiDet a χ (TR.infGL F a (Unitary.toUnits k)) : ℂˣ) : ℂ) • π.op (.cpt k) ψ) :=
      T.injective (by rw [hT, hS, hS, c₂, c₁, map_smul, map_smul])
    simp [e, hc]
  · obtain ⟨ψ, rfl⟩ := S.surjective ψ
    have e : π.op (.lie X) (S ψ) = S (π.op (.lie (TR.toL (-(Matrix.of X)ᵀ))) ψ + d (Matrix.of X).trace • ψ) :=
      T.injective (by rw [hT, hS, hS, x₂, x₁, map_add (f := _), map_add (f := _), map_smul, map_smul])
    have := hX X φ ψ
    simp only [e, LinearMap.compl₂_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, map_add (f := _), map_smul, smul_eq_mul]
    linear_combination this

end UpperTheory.V.Af
end
end
