module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.CechCubeBaseChange.BcSumSingle
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV

namespace UpperTheory.Gal.G3

def SplitDesc : Prop := ∀ {Z Y W : Scheme.{0}} (s : Y ⟶ Z) (c : W ⟶ Z) [IsFinite c] [Etale c] [Surjective c] (J : Type) [Finite J]
  (σ : J → (W ⟶ Y)), Splits s c σ → IsFinite s ∧ Etale s

def CharVan : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k], (l : k) = 0 → ∀ {X : Scheme.{0}} (_ : X ⟶ sp k) (n i : ℤ),
  Subsingleton (Hl l (sch.obj X) n i)

def CorrUniq : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] {Z Y Z' : Scheme.{0}} (_ : Z ⟶ sp k) (s : Y ⟶ Z) (t : Y ⟶ Z')
  (A A' : Htot l (sch.obj Z') →ₗ[ℚ_[l]] Htot l (sch.obj Z)), IsCorrOp l s t A → IsCorrOp l s t A' → A = A'

def VBcS : Prop := ∀ (l : ℕ) [Fact l.Prime] (k Ω : Type) [Field k] [IsAlgClosed k] [Field Ω] [IsAlgClosed Ω] (φ : k →+* Ω),
  IsUnit (l : k) → ∀ {X : Scheme.{0}} (p : X ⟶ sp k) [IsProper p] [Smooth p] (n i : ℤ),
  Function.Bijective (pullHQ l (sch.map (pullback.fst p (Spec.map (CommRingCat.ofHom φ)))) n i)

end UpperTheory.Gal.G3

end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR
open PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC

namespace UpperTheory.Gal.G3

private theorem secMap_eq_appLE {k : Type} [CommRing k] {X : Scheme.{0}} (s : X ⟶ Sp k) (U : X.Opens) :
    secMap s U = (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ s.appLE ⊤ U le_top := rfl

private theorem pushout_secMap {k k' : Type} [CommRing k] [CommRing k'] [Algebra k k']
    {X X' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k'} {g : X' ⟶ X}
    (h : IsPullback g s' s (spMap (algebraMap k k'))) {V : X.Opens} (hV : IsAffineOpen V) :
    IsPushout (secMap s V) (CommRingCat.ofHom (algebraMap k k')) (g.app V)
      (secMap s' (g ⁻¹ᵁ V)) := by
  have po := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := V) (UY := g ⁻¹ᵁ V) le_top le_top
    (by simp)).mp (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hV)
  refine po.of_iso (Scheme.ΓSpecIso (.of k)) (Iso.refl _) (Scheme.ΓSpecIso (.of k')) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp [secMap_eq_appLE, Scheme.Hom.appLE]
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  · simp [Scheme.Hom.app_eq_appLE]
  · simp [secMap_eq_appLE, Scheme.Hom.appLE]

private theorem isBC_semiSl_of_pushout {k k' : Type} [CommRing k] [CommRing k'] [Algebra k k'] {J : Type}
    (e : Module.Basis J k k') {B B' : Type} [CommRing B] [CommRing B'] [Algebra k B] [Algebra k' B']
    {α : B →+* B'} (hα : SemiHom (algebraMap k k') α)
    (H : IsPushout (CommRingCat.ofHom (algebraMap k B)) (CommRingCat.ofHom (algebraMap k k'))
      (CommRingCat.ofHom α) (CommRingCat.ofHom (algebraMap k' B'))) : IsBC e (semiSl hα) := by
  classical
  letI : Algebra B B' := α.toAlgebra
  letI : Algebra k B' := ((algebraMap k' B').comp (algebraMap k k')).toAlgebra
  haveI : IsScalarTower k k' B' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower k B B' := IsScalarTower.of_algebraMap_eq fun r ↦
    (congrArg (fun q ↦ q.hom r) H.w).symm
  have P : Algebra.IsPushout k k' B B' := CommRingCat.isPushout_iff_isPushout.1 H.flip
  have key : (bcSum e (semiSl hα) : (J →₀ B) → B') =
      P.out.equiv ∘ (TensorProduct.equivFinsuppOfBasisLeft e).symm := by
    funext x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), Function.comp_apply, hx, hy] at *
    | single j b =>
      rw [bcSum_single, Function.comp_apply, TensorProduct.equivFinsuppOfBasisLeft_symm_apply,
        Finsupp.sum_single_index (by simp), IsBaseChange.equiv_tmul]
      rfl
  unfold IsBC
  rw [key]
  exact P.out.equiv.bijective.comp (TensorProduct.equivFinsuppOfBasisLeft e).symm.bijective

theorem jHSections : P_sections := by
  intro k k' _ _ _ J e X X' s s' g h V hV
  exact isBC_semiSl_of_pushout e (semiHom_appSecS h.w V) (pushout_secMap h hV)

end UpperTheory.Gal.G3

end
end

section

open CategoryTheory AlgebraicGeometry

namespace UpperTheory.Gal.G3

theorem jHCover : PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_cover := by
  intro k _ X s _
  haveI : X.IsSeparated := ⟨by rw [← Limits.terminal.comp_from s]; infer_instance⟩
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  let C := X.affineCover.finiteSubcover
  let e := Fintype.equivFin C.I₀
  refine ⟨Fintype.card C.I₀, fun i => (C.f (e.symm i)).opensRange, ?_, ?_⟩
  · rw [e.symm.surjective.iSup_comp (fun j => (C.f j).opensRange)]
    exact C.iSup_opensRange
  · intro S hS
    have h := IsAffineOpen.biInf (X := X) (S : Set (Fin (Fintype.card C.I₀))) S.finite_toSet
      (Finset.coe_nonempty.mpr hS) (U := fun i => (C.f (e.symm i)).opensRange)
      (fun i _ => isAffineOpen_opensRange _)
    simpa only [Finset.mem_coe] using h

end UpperTheory.Gal.G3
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC

theorem UpperTheory.Gal.G3.jHAffine :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_affine := by
  intro k k' _ _ φ X X' s s' g h
  exact MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
end
