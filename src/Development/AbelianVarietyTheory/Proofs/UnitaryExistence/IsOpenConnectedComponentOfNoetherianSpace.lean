module

import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.IsOpenConnectedComponentOfNoetherianSpace
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfRatPoint
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace

noncomputable section

namespace GlobalTheory

universe u v

theorem isOpen_connectedComponent_of_noetherianSpace {X : Type u} [TopologicalSpace X]
    [NoetherianSpace X] (x : X) : IsOpen (connectedComponent x) := by
  first | exact _root_.CrystallineSemistableComparison.isOpen_connectedComponent_of_noetherianSpace | exact @_root_.CrystallineSemistableComparison.isOpen_connectedComponent_of_noetherianSpace | apply _root_.CrystallineSemistableComparison.isOpen_connectedComponent_of_noetherianSpace <;> assumption

theorem geometricallyConnected_of_isAlgClosed {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [ConnectedSpace X] :
    GeometricallyConnected f := by
  apply GlobalTheory.RatPointConn.of_isAlgClosed

section Sub

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {A N : C} [GrpObj N]

theorem exists_grpObj_of_mono_of_fac (n : A ⟶ N) [Mono n] (e : 𝟙_ C ⟶ A) (m : A ⊗ A ⟶ A) (i : A ⟶ A)
    (he : e ≫ n = η[N]) (hm : m ≫ n = (n ⊗ₘ n) ≫ μ[N]) (hi : i ≫ n = n ≫ ι[N]) :
    ∃ _ : GrpObj A, IsMonHom n := by
  first | exact _root_.GlobalTheory.ReducedSubgroup.exists_grpObj_of_mono | exact @_root_.GlobalTheory.ReducedSubgroup.exists_grpObj_of_mono | apply _root_.GlobalTheory.ReducedSubgroup.exists_grpObj_of_mono <;> assumption

end Sub

theorem finite_points_of_isOpenMap_unit {k : Type} [Field k] [IsAlgClosed k] (N : Over (Sp k))
    [GrpObj N] [LocallyOfFiniteType N.hom] [NoetherianSpace N.left]
    (h : IsOpenMap η[N].left) : Finite (𝟙_ (Over (Sp k)) ⟶ N) := by
  let pt : Sp k := IsLocalRing.closedPoint k
  let F : (𝟙_ (Over (Sp k)) ⟶ N) → N.left := fun x => x.left pt
  have hF : Function.Injective F := fun x y hxy =>
    Over.OverMorphism.ext (ext_of_apply_closedPoint_eq N.hom x.w y.w hxy)
  have ho : ∀ x, IsOpen {F x} := fun x => by
    have hx : η[N] ≫ (GrpObj.mulRight x).hom = x := by
      simpa [comp_lift_assoc] using lift_comp_one_left (𝟙 _) x
    have : IsIso (GrpObj.mulRight x).hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).map (GrpObj.mulRight x).hom))
    have h₁ : IsOpenMap x.left := by
      rw [← hx, Over.comp_left]
      exact (GrpObj.mulRight x).hom.left.isOpenMap.comp h
    have h₂ := h₁ {pt} (by
      have : Subsingleton (Sp k) := inferInstance
      convert isOpen_univ
      exact Set.eq_univ_of_forall fun a => this.elim _ _)
    rwa [Set.image_singleton] at h₂
  obtain ⟨t, -, ht⟩ := (NoetherianSpace.isCompact (Set.range F)).elim_nhds_subcover
    (fun y => {y}) (by rintro _ ⟨x, rfl⟩; exact (ho x).mem_nhds rfl)
  have : (Set.range F).Finite := t.finite_toSet.subset fun y hy => by simpa using ht hy
  exact (Set.finite_range_iff hF).1 this

theorem exists_neutralComponent : ∀ (k : Type) [Field k] [IsAlgClosed k] (N : Over (Sp k)) [GrpObj N], Smooth N.hom → QuasiCompact N.hom → ∃ (N₀ : Over (Sp k)) (_ : GrpObj N₀) (ν : N₀ ⟶ N) (g : ℕ), IsMonHom ν ∧ IsOpenImmersion ν.left ∧ IsClosedImmersion ν.left ∧ GeometricallyConnected N₀.hom ∧ SmoothOfRelativeDimension g N₀.hom ∧ (g = 0 → Finite (𝟙_ (Over (Sp k)) ⟶ N)) := by
  intro k _ _ N _ hs hq
  have : IsLocallyNoetherian N.left := LocallyOfFiniteType.isLocallyNoetherian N.hom
  have : CompactSpace N.left := QuasiCompact.compactSpace_of_compactSpace N.hom
  have : IsNoetherian N.left := {}
  let pt : (𝟙_ (Over (Sp k))).left := IsLocalRing.closedPoint k
  let e₀ : N.left := η[N].left pt
  let U : N.left.Opens := ⟨connectedComponent e₀, isOpen_connectedComponent_of_noetherianSpace e₀⟩
  let N₀ : Over (Sp k) := Over.mk (U.ι ≫ N.hom)
  let ν : N₀ ⟶ N := Over.homMk U.ι rfl
  have hνo : IsOpenImmersion ν.left := inferInstanceAs (IsOpenImmersion U.ι)
  have hr : Set.range ν.left = connectedComponent e₀ := U.range_ι
  have hνc : IsClosedImmersion ν.left := .of_isPreimmersion _ (hr ▸ isClosed_connectedComponent)
  have : Mono ν := Over.mono_of_mono_left ν
  have hsm : Smooth N₀.hom := inferInstanceAs (Smooth (U.ι ≫ N.hom))
  have hc : ConnectedSpace N₀.left :=
    isConnected_iff_connectedSpace.1 (isConnected_connectedComponent (x := e₀))
  have hg : GeometricallyConnected N₀.hom := geometricallyConnected_of_isAlgClosed N₀.hom

  have fac : ∀ (T : Over (Sp k)) [ConnectedSpace T.left] (φ : T ⟶ N) (t : 𝟙_ _ ⟶ T),
      t ≫ φ = η[N] → ∃ ψ : T ⟶ N₀, ψ ≫ ν = φ := by
    intro T _ φ t ht
    have hsub : Set.range φ.left ⊆ Set.range ν.left := by
      rw [hr]
      refine (isConnected_range φ.left.continuous).subset_connectedComponent ⟨t.left pt, ?_⟩
      simp only [e₀, ← ht, Over.comp_left, Scheme.Hom.comp_apply]
    refine ⟨Over.homMk (IsOpenImmersion.lift ν.left φ.left hsub) ?_, ?_⟩
    · rw [← ν.w, IsOpenImmersion.lift_fac_assoc, φ.w]
    · exact Over.OverMorphism.ext (IsOpenImmersion.lift_fac ν.left φ.left hsub)
  have : ConnectedSpace (𝟙_ (Over (Sp k))).left := inferInstanceAs (ConnectedSpace (Sp k))
  obtain ⟨e, he⟩ := fac (𝟙_ _) η[N] (𝟙 _) (Category.id_comp _)
  have : ConnectedSpace (N₀ ⊗ N₀).left :=
    inferInstanceAs (ConnectedSpace ↥(pullback N₀.hom N₀.hom))
  obtain ⟨m, hm⟩ := fac (N₀ ⊗ N₀) ((ν ⊗ₘ ν) ≫ μ[N]) (lift e e)
    (by simpa [he] using lift_comp_one_left (𝟙 _) η[N])
  obtain ⟨i, hi⟩ := fac N₀ (ν ≫ ι[N]) e (by simp [reassoc_of% he])
  obtain ⟨G, hG⟩ := exists_grpObj_of_mono_of_fac ν e m i he hm hi
  obtain ⟨g, hgd⟩ := exists_dim_of_preconnected N₀.hom (e.left pt)
  refine ⟨N₀, G, ν, g, hG, hνo, hνc, hg, hgd, ?_⟩
  rintro rfl
  have : Etale N₀.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 hgd
  have : Etale (e.left ≫ N₀.hom) := by
    rw [e.w]; exact inferInstanceAs (Etale (𝟙 (Sp k)))
  have : Etale e.left := Etale.of_comp e.left N₀.hom
  refine finite_points_of_isOpenMap_unit N ?_
  rw [← he, Over.comp_left]
  exact (e.left ≫ ν.left).isOpenMap

end GlobalTheory
