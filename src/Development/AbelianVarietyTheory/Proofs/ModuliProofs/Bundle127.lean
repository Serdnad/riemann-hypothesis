module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjProperRelAmpleOfProjectiveCoordinateRep
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjectiveCoordinateRepresentationClosedSubsch
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle063
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle039
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SegreCoordinates
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.CubicalSymmetricTriv
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle116
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle007
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNonvanishing
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle119
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle120
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.GraphSegre

theorem idealOf_eq_graphIdeal {K σ₁ σ₂ : Type} [CommRing K] {Y X₁ X₂ : Scheme.{0}} (s : Y ⟶ Sp K)
    (M₁ : LB X₁) (th₁ : σ₁ → M₁.Sec) (a₁ : Y ⟶ X₁) (M₂ : LB X₂) (th₂ : σ₂ → M₂.Sec) (a₂ : Y ⟶ X₂)
    (N : LB Y) (ty : σ₁ × σ₂ → N.Sec) (h₁ : M₁.IsLB) (h₂ : M₂.IsLB) (hN : N.IsLB)
    (H : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (v₁ : σ₁ → T) (v₂ : σ₂ → T), SecCoord M₁ th₁ (y ≫ a₁) v₁ →
      SecCoord M₂ th₂ (y ≫ a₂) v₂ → SecCoord N ty y (fun i => v₁ i.1 * v₂ i.2)) :
    idealOf s N ty (𝟙 Y) = graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂ := by
  ext F
  simp only [idealOf, graphIdeal, Ideal.mem_iInf, RingHom.mem_ker, Category.comp_id]
  constructor
  · intro hF T _ β y v₁ v₂ h
    exact hF T _ β y _ ⟨h.1, H T y v₁ v₂ h.2.1 h.2.2⟩
  · intro hF T _ β y v h
    refine eq_zero_of_localization _ fun J hJ => ?_
    set φ := algebraMap T (Localization.AtPrime J) with hφ
    obtain ⟨v₁, hv₁⟩ := (GlobalTheory.ZM.LocalCoord.secCoord_local X₁ M₁ σ₁ th₁ h₁).1 (Localization.AtPrime J) ((spMap φ ≫ y) ≫ a₁)
    obtain ⟨v₂, hv₂⟩ := (GlobalTheory.ZM.LocalCoord.secCoord_local X₂ M₂ σ₂ th₂ h₂).1 (Localization.AtPrime J) ((spMap φ ≫ y) ≫ a₂)
    have hv := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N _ ty T y v hN h.2).1 _ φ
    obtain ⟨u, hu⟩ := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N _ ty _ _ _ hN (H _ _ v₁ v₂ hv₁ hv₂)).2.2 _ hv
    have hv₁' := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique X₁ M₁ _ th₁ _ _ _ h₁ hv₁).2.1 u
    have hs : (spMap φ ≫ y) ≫ s = spMap (φ.comp β) := by
      rw [Category.assoc, h.1]
      exact (Spec.map_comp (CommRingCat.ofHom β) (CommRingCat.ofHom φ)).symm
    have key := hF _ _ (φ.comp β) (spMap φ ≫ y) _ v₂ ⟨hs, hv₁', hv₂⟩
    rw [MvPolynomial.map_eval₂Hom, ← key]
    congr 2
    funext i
    rw [hu i, _root_.mul_assoc]

theorem projRep_graph : ∀ (R K σ₁ σ₂ : Type) [CommRing R] [CommRing K] [Finite σ₁] [Finite σ₂] (x : R →+* K) (I₁ : Ideal (MvPolynomial σ₁ R)) (I₂ : Ideal (MvPolynomial σ₂ R)) (Z₁ Z₂ : Over (Sp R)) (M₁ : LB Z₁.left) (M₂ : LB Z₂.left) (th₁ : σ₁ → M₁.Sec) (th₂ : σ₂ → M₂.Sec) (Y : Scheme.{0}) (s : Y ⟶ Sp K) (a₁ : Y ⟶ Z₁.left) (a₂ : Y ⟶ Z₂.left), ProjRep I₁ Z₁.hom M₁ th₁ → ProjRep I₂ Z₂.hom M₂ th₂ → IsPullback a₁ s Z₁.hom (spMap x) → a₂ ≫ Z₂.hom = s ≫ spMap x → ∃ (N : LB Y) (ty : σ₁ × σ₂ → N.Sec), ProjRep (graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂) s N ty ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (v₁ : σ₁ → T) (v₂ : σ₂ → T), SecCoord M₁ th₁ (y ≫ a₁) v₁ → SecCoord M₂ th₂ (y ≫ a₂) v₂ → SecCoord N ty y (fun i => v₁ i.1 * v₂ i.2) := by
  intro R K σ₁ σ₂ _ _ _ _ x I₁ I₂ Z₁ Z₂ M₁ M₂ th₁ th₂ Y s a₁ a₂ r₁ r₂ hp ha₂
  obtain ⟨I₃, M₃, th₃, r₃, hseg⟩ := GlobalTheory.ZM.SegreCoord.segre_coordinates R σ₁ σ₂ I₁ I₂ Z₁ Z₂ M₁ M₂ th₁ th₂ r₁ r₂
  have hprop : IsProper Z₂.hom := (GlobalTheory.ZM.projRep_projective_ample R σ₂ I₂ Z₂ M₂ th₂ r₂).2.1
  have hP : IsPullback (fst Z₁ Z₂).left (snd Z₁ Z₂).left Z₁.hom Z₂.hom := IsPullback.of_hasPullback Z₁.hom Z₂.hom
  have hW := IsPullback.of_hasPullback (Z₁ ⊗ Z₂).hom (spMap x)
  generalize pullback.fst (Z₁ ⊗ Z₂).hom (spMap x) = π at hW
  generalize pullback.snd (Z₁ ⊗ Z₂).hom (spMap x) = s' at hW
  generalize pullback (Z₁ ⊗ Z₂).hom (spMap x) = Wd at π s' hW
  obtain ⟨th', r', hbc⟩ := GlobalTheory.ZM.RepBC.projRep_baseChange R K _ x I₃ _ Wd _ s' π M₃ th₃ r₃ hW
  have hfw : (fst Z₁ Z₂).left ≫ Z₁.hom = (Z₁ ⊗ Z₂).hom := Over.w _
  let a : Y ⟶ (Z₁ ⊗ Z₂).left := hP.lift a₁ a₂ (hp.w.trans ha₂.symm)
  have e₁ : a ≫ (fst Z₁ Z₂).left = a₁ := hP.lift_fst _ _ _
  have e₂ : a ≫ (snd Z₁ Z₂).left = a₂ := hP.lift_snd _ _ _
  let i : Y ⟶ Wd := hW.lift a s (by rw [← hfw, ← Category.assoc, e₁, hp.w])
  have i₁ : i ≫ π = a := hW.lift_fst _ _ _
  have i₂ : i ≫ s' = s := hW.lift_snd _ _ _
  let q : Wd ⟶ Y := hp.lift (π ≫ (fst Z₁ Z₂).left) s' (by rw [Category.assoc, hfw, hW.w])
  have q₁ : q ≫ a₁ = π ≫ (fst Z₁ Z₂).left := hp.lift_fst _ _ _
  have q₂ : q ≫ s = s' := hp.lift_snd _ _ _
  have hq : IsPullback π q (fst Z₁ Z₂).left a₁ := by
    refine IsPullback.of_bot ?_ q₁.symm hp
    rw [q₂, hfw]; exact hW
  have hsf : IsSeparated (fst Z₁ Z₂).left :=
    MorphismProperty.of_isPullback (P := @IsSeparated) hP.flip inferInstance
  have hsq : IsSeparated q := MorphismProperty.of_isPullback (P := @IsSeparated) hq hsf
  have hiq : i ≫ q = 𝟙 Y := by
    refine hp.hom_ext ?_ ?_
    · rw [Category.assoc, q₁, ← Category.assoc, i₁, e₁, Category.id_comp]
    · rw [Category.assoc, q₂, i₂, Category.id_comp]
  have hci : IsClosedImmersion i := by
    have : IsClosedImmersion (i ≫ q) := by rw [hiq]; infer_instance
    exact IsClosedImmersion.of_comp i q
  have hN : ((M₃.pull π).pull i).IsLB := pull_isLB r'.1 i
  have hc : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (v : σ₁ × σ₂ → T),
      SecCoord ((M₃.pull π).pull i) (fun j => GlobalTheory.ZM.RepBC.secPull _ i (th' j)) y v ↔
        SecCoord (M₃.pull π) th' (y ≫ i) v := fun T _ y v => GlobalTheory.ZM.RepBC.secCoord_pull _ th' i y v
  have rY := GlobalTheory.ZM.ClosedCoord.projRep_closed K _ _ Wd Y s' _ th' i _ _ r' hci hN hc
  have H : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (v₁ : σ₁ → T) (v₂ : σ₂ → T), SecCoord M₁ th₁ (y ≫ a₁) v₁ →
      SecCoord M₂ th₂ (y ≫ a₂) v₂ →
      SecCoord ((M₃.pull π).pull i) (fun j => GlobalTheory.ZM.RepBC.secPull _ i (th' j)) y (fun i => v₁ i.1 * v₂ i.2) := by
    intro T _ y v₁ v₂ h₁ h₂
    rw [hc, hbc, Category.assoc, i₁]
    refine hseg T _ v₁ v₂ ?_ ?_
    · rwa [Category.assoc, e₁]
    · rwa [Category.assoc, e₂]
  rw [i₂, idealOf_eq_graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂ _ _ r₁.1 r₂.1 hN H] at rY
  exact ⟨_, _, rY, H⟩

end GlobalTheory.ZM.GraphSegre
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.UU GlobalTheory.IndefiniteRowSideFullHecke.CubicalSymmetricTriv
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CubCompare
variable {S S' : Scheme.{0}}

section Gen
variable {X X' Y Y' : Scheme.{0}} {K : Type} [Fintype K]

end Gen

section Pack
variable {G : Over S} [GrpObj G] [IsCommMonObj G]

end Pack

section Maps
variable {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

end Maps

section Triv
variable {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]


variable {L : RigLB G} {i : H ⟶ G}




variable {c : CubicalStr G L} [IsMonHom i]


end Triv

section Wt
variable {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G]

theorem gs_appLE {Y Z : Scheme.{0}} (r : Z ⟶ Y) (V : Y.Opens) (h : ⊤ ≤ r ⁻¹ᵁ V) (u : Γ(Y, V)) (z : Z) :
    gs (𝟙 Z) z ⊤ ((r.appLE V ⊤ h).hom u) = gs r z V u :=
  (gs_res (𝟙 Z) z h trivial _).trans ((gs_pull (𝟙 Z) r z V (h trivial) u).trans (by rw [Category.id_comp]))

theorem gs_comp {Y Z Z' : Scheme.{0}} (ρ : Z' ⟶ Z) (r : Z ⟶ Y) (V : Y.Opens) (z : Z') (h : r (ρ z) ∈ V) (u : Γ(Y, V)) :
    gs (ρ ≫ r) z V u = (ρ.stalkMap z).hom (gs r (ρ z) V u) := by
  rw [gs_eq (ρ ≫ r) z V h, gs_eq r _ V h]
  exact (Scheme.Hom.germ_stalkMap_apply ρ (r ⁻¹ᵁ V) z h _).symm

theorem isWt_iff_germ (i : splitTorus S X ⟶ G) (V : G.left.Opens) (u : Γ(G.left, V)) (χ : X) :
    IsWt i V u χ ↔ ∀ (T : Over S) (z : T.left) (t : T ⟶ splitTorus S X) (x : T ⟶ G), x.left z ∈ V →
      ((t ≫ i) * x).left z ∈ V → gs ((t ≫ i) * x).left z V u = (charV χ z t).val * gs x.left z V u := by
  have key : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V) (z : Z.left),
      gs (𝟙 Z.left) z ⊤ (t.left.appTop.hom (charUnit S X χ).val * (g.left.appLE _ ⊤ h₂).hom u) =
        (charV χ z t).val * gs g.left z V u := fun Z t g h₂ z => by
    rw [gs_mul _ z ⊤ trivial, gs_appLE, ← chV_val, gs_unit _ z ⊤ trivial, charV, gm_charUnit]
  constructor
  · intro h T z t x hx hx'
    let O : T.left.Opens := x.left ⁻¹ᵁ V ⊓ ((t ≫ i) * x).left ⁻¹ᵁ V
    let ρ : Over.mk (O.ι ≫ T.hom) ⟶ T := Over.homMk O.ι rfl
    have e : ((ρ ≫ t) ≫ i) * (ρ ≫ x) = ρ ≫ ((t ≫ i) * x) := by rw [MonObj.comp_mul, Category.assoc]
    have h₁ : ⊤ ≤ (((ρ ≫ t) ≫ i) * (ρ ≫ x)).left ⁻¹ᵁ V := by rw [e]; exact fun y _ => y.2.2
    have h₂ : ⊤ ≤ (ρ ≫ x).left ⁻¹ᵁ V := fun y _ => y.2.1
    have a := congrArg (gs (𝟙 _) (⟨z, hx, hx'⟩ : O) ⊤) (h _ (ρ ≫ t) (ρ ≫ x) h₁ h₂)
    erw [key, gs_appLE] at a
    rw [e] at a
    unfold charV at a
    erw [← gs_unit _ _ ⊤ trivial] at a
    have inj : ∀ y : O.toScheme, Function.Injective (O.ι.stalkMap y).hom := fun y =>
      (ConcreteCategory.bijective_of_isIso _).1
    apply inj ⟨z, hx, hx'⟩
    rw [charV, ← gs_unit _ _ ⊤ trivial]
    exact ((gs_comp O.ι _ V ⟨z, hx, hx'⟩ hx' u).symm.trans a).trans ((congrArg₂ (· * ·)
      (gs_comp O.ι t.left ⊤ ⟨z, hx, hx'⟩ trivial _) (gs_comp O.ι x.left V ⟨z, hx, hx'⟩ hx u)).trans (map_mul _ _ _).symm)
  · intro h Z t g h₁ h₂
    refine fn_ext fun z _ => ?_
    rw [key, gs_appLE]
    exact h Z z t g (h₂ trivial) (h₁ trivial)

end Wt

section Ext
variable {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G]

variable {B : Over S} [GrpObj B]


end Ext

section Desc
variable {G H B : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] [GrpObj B] [IsCommMonObj B]
  {i : H ⟶ G} [IsMonHom i] {q : G ⟶ B} [IsMonHom q] {P : CP G} {M : CP B} {w : LB.Iso P.L.L (M.L.L.pull q.left)}



end Desc

end GlobalTheory.CubCompare
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.GenSecFibre

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.VVRank GlobalTheory.EmbPull TopologicalSpace

variable {S : Scheme.{0}} (P : PolAV S) {T T' : Over S}

theorem mem_nonzeroLocus_pullS (a : ℤ) (h : T' ⟶ T) (th : LB.Sec (LPow P.A P.L a T)) (z : (T' ⊗ P.A).left) :
    z ∈ nonzeroLocus (pullS P.A a h th) ↔ (h ▷ P.A).left z ∈ nonzeroLocus th := by
  have e : ∀ j, z ∈ (LPow P.A P.L a T').U j → (IsUnit (gs (𝟙 _) z _ ((pullS P.A a h th).f j)) ↔
      IsUnit (gs (𝟙 _) ((h ▷ P.A).left z) _ (th.f j))) := fun j hj => by
    have q := gs_pullTo (φ := fun _ : Fin 1 => (snd T P.A).left) (ε := fun _ => a) th (h ▷ P.A).left
      (fun _ => whisker_snd_left P.A h) (𝟙 _) z j hj
    rw [Category.id_comp] at q
    have q' := q.trans (gs_stalkMap (h ▷ P.A).left z _ (wchart_le_of_eq _ (fun _ => whisker_snd_left P.A h) j hj) _)
    exact (iff_of_eq (congrArg IsUnit q')).trans (isUnit_map_iff _ _)
  rw [mem_nonzeroLocus, mem_nonzeroLocus]
  refine exists_congr fun j => ⟨fun ⟨hj, u⟩ => ⟨?_, (e j hj).1 u⟩, fun ⟨hj, u⟩ => ?_⟩
  · exact wchart_le_of_eq (φ := fun _ : Fin 1 => (snd T P.A).left) _ (fun _ => whisker_snd_left P.A h) j hj
  · have hj' := mem_wchart_of_eq (φ := fun _ : Fin 1 => (snd T P.A).left) _ (fun _ => whisker_snd_left P.A h) z j hj
    exact ⟨hj', (e j hj').2 u⟩

theorem exists_mem_nonzeroLocus (hS : SecBaseChangeAnySt) [IsAffine T.left] {th : LB.Sec (LPow P.A P.L 1 T)}
    (H : IsGenSec P.A P.L 1 th) (p : T.left) :
    ∃ q : (T ⊗ P.A).left, (fst T P.A).left q = p ∧ q ∈ nonzeroLocus th := by
  let w : Spec (CommRingCat.of (T.left.residueField p)) ⟶ T.left := T.left.fromSpecResidueField p
  let h : Over.mk (w ≫ T.hom) ⟶ T := Over.homMk w rfl
  have : IsAffine (Over.mk (w ≫ T.hom)).left := inferInstanceAs (IsAffine (Spec _))
  have h₀ := ThetaCoset.ne_zero_of_isGenSec hS P (w ≫ T.hom) (isGenSec_pullS P hS h H)
  have := P.isAb.smooth
  have : Smooth (fst (Over.mk (w ≫ T.hom)) P.A).left :=
    inferInstanceAs (Smooth (pullback.fst (w ≫ T.hom) P.A.hom))
  have : IsReduced (Over.mk (w ≫ T.hom) ⊗ P.A).left :=
    isReduced_scheme_of_smooth_of_isIntegrallyClosed (T.left.residueField p) (fst (Over.mk (w ≫ T.hom)) P.A).left
  obtain ⟨z, hz⟩ : ∃ z, z ∈ nonzeroLocus (pullS P.A 1 h th) := by
    by_contra hn
    refine h₀ (Subtype.ext (funext fun j => ?_))
    exact eq_zero_of_basicOpen_eq_bot _ (le_bot_iff.1 fun z hz => hn ⟨z, Opens.mem_iSup.2 ⟨j, hz⟩⟩)
  refine ⟨(h ▷ P.A).left z, ?_, (mem_nonzeroLocus_pullS P 1 h th z).1 hz⟩
  rw [← Scheme.Hom.comp_apply, (isPullback_whisker P.A h).w, Scheme.Hom.comp_apply]
  exact (T.left.range_fromSpecResidueField p).le ⟨_, rfl⟩

theorem map_sub_eq_zero' {R R' M M' : Type} [CommRing R] [CommRing R'] [AddCommGroup M] [AddCommGroup M'] [Module R M]
    [Module R' M'] (σ : R →+* R') (φ : M →ₛₗ[σ] M') (s t : M) (b : M') (a c d₀ e₀ : R) (d e : R')
    (ht : φ t = d • b) (hs : φ s = e • b) (hd : σ d₀ = σ a * d) (he : σ e₀ = σ c * e) :
    φ ((d₀ * c) • s - (e₀ * a) • t) = 0 := by
  rw [map_sub, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, map_mul, map_mul, ht, hs, hd, he, smul_smul, smul_smul,
    sub_eq_zero]
  congr 1
  ring

theorem isGenSec_of_fibres (hS : SecBaseChangeAnySt) [IsAffine T.left] {th : LB.Sec (LPow P.A P.L 1 T)}
    (H : ∀ p : T.left, ∃ q : (T ⊗ P.A).left, (fst T P.A).left q = p ∧ q ∈ nonzeroLocus th) :
    IsGenSec P.A P.L 1 th := by
  intro s
  let I : Ideal Γ(T.left, ⊤) := (Submodule.span Γ(T.left, ⊤)
    {SecM.ofSec P.A th}).comap (LinearMap.toSpanSingleton _ _ (SecM.ofSec P.A s))
  have key : ∀ p : T.left, ∃ f ∈ I, p ∈ T.left.basicOpen f := fun p => by
    obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl (T.hom p)
    have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
    obtain ⟨f, hf, hp⟩ := (isAffineOpen_top T.left).exists_basicOpen_le (V := T.hom ⁻¹ᵁ V) ⟨p, hV⟩ trivial
    let W := T.left.basicOpen f
    let l : overRes W ⟶ overRes (T := baseOver S) V := Over.homMk
      (IsOpenImmersion.lift V.ι (W.ι ≫ T.hom) (by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨y, rfl⟩
        exact hf y.2)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
    have hW : IsAffineOpen W := (isAffineOpen_top _).basicOpen f
    have : IsAffine (overRes W).left := hW
    obtain ⟨c, -⟩ := exists_basis P 1 b hb (overRes W) l
    have rep : ∀ x : SecM P.A P.L 1 (overRes W), ∃ d : Γ((overRes W).left, ⊤), x = d • (c hq.default :) := fun x => by
      have := c.sum_repr x
      rw [Fintype.sum_unique] at this
      exact ⟨_, this.symm⟩
    obtain ⟨d, hd⟩ := rep (pullM P.A P.L 1 (overResι W) (SecM.ofSec P.A th))
    obtain ⟨e, he⟩ := rep (pullM P.A P.L 1 (overResι W) (SecM.ofSec P.A s))
    obtain ⟨m, d₀, hd₀⟩ : ∃ (m : ℕ) (d₀ : Γ(T.left, ⊤)), (overResι W).left.appTop.hom d₀ =
        (overResι W).left.appTop.hom (f ^ m) * d := exists_pow_mul_extend f d
    obtain ⟨n, e₀, he₀⟩ : ∃ (m : ℕ) (d₀ : Γ(T.left, ⊤)), (overResι W).left.appTop.hom d₀ =
        (overResι W).left.appTop.hom (f ^ m) * e := exists_pow_mul_extend f e
    obtain ⟨N, hN⟩ := exists_pow_kill_secM P 1 f ((d₀ * f ^ n) • SecM.ofSec P.A s - (e₀ * f ^ m) • SecM.ofSec P.A th)
      (map_sub_eq_zero' _ _ _ _ _ _ _ _ _ d e hd he hd₀ he₀)
    have hu : p ∈ T.left.basicOpen d₀ := by
      obtain ⟨q, hqp, hq0⟩ := H p
      obtain ⟨z, hz, hz'⟩ := Scheme.exists_preimage_of_isPullback (isPullback_whisker P.A (overResι W)) q
        ⟨p, hp⟩ hqp
      subst hz
      obtain ⟨j, hj, u⟩ := (mem_nonzeroLocus _ _).1 ((mem_nonzeroLocus_pullS P 1 (overResι W) th z).2 hq0)
      have k := (congrArg (fun x => gs (𝟙 _) z _ (x.1 j)) hd).trans (PushInv.gs_smul P.A P.L _ 1 d _ j z hj)
      have u₁ : IsUnit (gs (fst (overRes W) P.A).left z ⊤ d) := isUnit_of_mul_isUnit_left (k ▸ u)
      rw [gs_stalkMap _ z ⊤ trivial, isUnit_map_iff, gs_eq _ _ ⊤ trivial] at u₁
      have u₂ : (fst (overRes W) P.A).left z ∈ (overRes W).left.basicOpen d := (Scheme.mem_basicOpen_top _ _ _).2 u₁
      have u₃ : (⟨p, hp⟩ : (overRes W).left) ∈ (overResι W).left ⁻¹ᵁ T.left.basicOpen d₀ := by
        rw [Scheme.preimage_basicOpen_top, hd₀, Scheme.basicOpen_mul, ← Scheme.preimage_basicOpen_top]
        refine ⟨?_, hz' ▸ u₂⟩
        change p ∈ T.left.basicOpen (f ^ m)
        rw [Scheme.mem_basicOpen_top] at hp ⊢
        rw [map_pow]
        exact hp.pow _
      exact u₃
    refine ⟨f ^ N * (d₀ * f ^ n), Submodule.mem_span_singleton.2 ⟨f ^ N * (e₀ * f ^ m), ?_⟩, ?_⟩
    · rw [smul_sub, sub_eq_zero, ← mul_smul, ← mul_smul] at hN
      exact hN.symm
    · rw [Scheme.mem_basicOpen_top] at hp hu ⊢
      simp only [map_mul, map_pow]
      exact (hp.pow _).mul (hu.mul (hp.pow _))
  have hI : Ideal.span (I : Set Γ(T.left, ⊤)) = ⊤ :=
    (isAffineOpen_top T.left).self_le_iSup_basicOpen_iff.1 fun p _ => by
      obtain ⟨f, hf, hp⟩ := key p
      exact Opens.mem_iSup.2 ⟨⟨f, hf⟩, hp⟩
  rw [Ideal.span_eq, Ideal.eq_top_iff_one] at hI
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hI
  rw [LinearMap.toSpanSingleton_apply, one_smul] at hr
  exact ⟨r, fun j => (congrArg (fun q => q.1 j) hr).symm⟩

theorem isGenSec_iff_fibres : Out.Laws2 → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (R : Type) [CommRing R] (y : Sp R ⟶ S) (th : LB.Sec (Out.LPow P.A P.L 1 (Over.mk y))), Out.IsGenSec P.A P.L 1 th ↔ ∀ p : Sp R, ∃ q : (Over.mk y ⊗ P.A).left, (fst (Over.mk y) P.A).left q = p ∧ q ∈ Out.nonzeroLocus th := by
  intro h S P R _ y th
  have : IsAffine (Over.mk y).left := inferInstanceAs (IsAffine (Spec _))
  exact ⟨exists_mem_nonzeroLocus P h.secBaseChangeAny,
    isGenSec_of_fibres P (T := Over.mk y) h.secBaseChangeAny⟩

end GlobalTheory.GenSecFibre
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.isQProjOver_comp_of_isFinite_noetherianBase : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X Y : Scheme.{0}) (f : X ⟶ Y) (s : Y ⟶ Sp R), IsFinite f → IsQProjOver s → IsQProjOver (f ≫ s) := by
  first | exact @GlobalTheory.isQProjOver_comp_of_isFinite_noetherian | exact GlobalTheory.isQProjOver_comp_of_isFinite_noetherian | (intros; apply GlobalTheory.isQProjOver_comp_of_isFinite_noetherian <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory


open AlgebraicGeometry CategoryTheory Limits in
theorem _root_.GlobalTheory.isProjOver_of_isProper_of_isImmersion {A : Type} [CommRing A]
    {B X : Scheme.{0}} (e : B ⟶ X)
    [IsImmersion e] {x : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp A} (hx : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver x) [IsProper (e ≫ x)] :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (e ≫ x) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver at hx
  obtain ⟨N, i, hi, -, rfl⟩ := hx
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver
  haveI : IsProper (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str A N) := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str A N
  haveI : IsProper ((e ≫ i) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str A N) := by rw [Category.assoc]; infer_instance
  haveI : IsProper (e ≫ i) := IsProper.of_comp (e ≫ i) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str A N)
  exact ⟨N, e ≫ i, .of_isPreimmersion _ (e ≫ i).isClosedMap.isClosed_range, by simp⟩

open AlgebraicGeometry CategoryTheory Limits in
private theorem isPullback_fst_comp_map {X Y Z W : Scheme.{0}} (f : X ⟶ Y) (s : Y ⟶ Z)
    (t : W ⟶ Z) :
    IsPullback (pullback.fst (f ≫ s) t)
      (pullback.map (f ≫ s) t s t f (𝟙 _) (𝟙 _) (by simp) (by simp)) f (pullback.fst s t) := by
  have h₁ : pullback.map (f ≫ s) t s t f (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ pullback.fst s t =
      pullback.fst (f ≫ s) t ≫ f := pullback.lift_fst _ _ _
  have h₂ : pullback.map (f ≫ s) t s t f (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ pullback.snd s t =
      pullback.snd (f ≫ s) t := (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  refine IsPullback.of_bot ?_ h₁.symm (IsPullback.of_hasPullback s t)
  rw [h₂]
  exact IsPullback.of_hasPullback (f ≫ s) t

open AlgebraicGeometry CategoryTheory Limits in
private theorem isImmersion_pullback_lift_of_isPullback {X Y Z W P : Scheme.{0}} (f : X ⟶ Y)
    (s : Y ⟶ Z) (t : W ⟶ Z) (y : W ⟶ Y) (hy : y ≫ s = t) (φ : P ⟶ X) (b : P ⟶ W)
    (h : IsPullback φ b f y) :
    IsImmersion (pullback.lift (f := f ≫ s) (g := t) φ b
      (by rw [← hy, ← Category.assoc, h.w, Category.assoc])) := by
  set Γ : W ⟶ pullback s t := pullback.lift y (𝟙 W) (by rw [hy, Category.id_comp]) with hΓdef
  have hΓs : Γ ≫ pullback.snd s t = 𝟙 W := pullback.lift_snd _ _ _
  have hΓf : Γ ≫ pullback.fst s t = y := pullback.lift_fst _ _ _
  haveI : IsImmersion (Γ ≫ pullback.snd s t) := by rw [hΓs]; infer_instance
  haveI : IsImmersion Γ := IsImmersion.of_comp Γ (pullback.snd s t)
  set e : P ⟶ pullback (f ≫ s) t := pullback.lift (f := f ≫ s) (g := t) φ b
    (by rw [← hy, ← Category.assoc, h.w, Category.assoc]) with hedef
  have hef : e ≫ pullback.fst (f ≫ s) t = φ := pullback.lift_fst _ _ _
  have hes : e ≫ pullback.snd (f ≫ s) t = b := pullback.lift_snd _ _ _
  set g := pullback.map (f ≫ s) t s t f (𝟙 _) (𝟙 _) (by simp) (by simp) with hgdef
  have hg₁ : g ≫ pullback.fst s t = pullback.fst (f ≫ s) t ≫ f := pullback.lift_fst _ _ _
  have hg₂ : g ≫ pullback.snd s t = pullback.snd (f ≫ s) t :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hsq : e ≫ g = b ≫ Γ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hg₁, hΓf, ← Category.assoc, hef, h.w]
    · rw [Category.assoc, Category.assoc, hg₂, hΓs, hes, Category.comp_id]
  have hleft : IsPullback e b g Γ := by
    refine IsPullback.of_right ?_ hsq (isPullback_fst_comp_map f s t)
    rw [hef, hΓf]
    exact h
  exact MorphismProperty.of_isPullback (P := @IsImmersion) hleft.flip ‹IsImmersion Γ›


open AlgebraicGeometry CategoryTheory Limits in
theorem _root_.GlobalTheory.isProjOver_of_isPullback_of_isProper_of_isQProjOver :
    ∀ (R A : Type) [CommRing R] [CommRing A] (S : Scheme.{0}) (s : S ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (G : Over S)
      (y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp A ⟶ S) (B : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp A)) (φ : B.left ⟶ G.left), IsProper G.hom →
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver (G.hom ≫ s) → IsPullback φ B.hom G.hom y → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver B.hom := by
  intro R A _ _ S s G y B φ hG hq hpb
  let j : R →+* A :=
    (Spec.preimage (y ≫ s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))).hom
  have hj : y ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap
    simp only [j, CommRingCat.ofHom_hom]
    exact (Spec.map_preimage _).symm
  haveI := isImmersion_pullback_lift_of_isPullback G.hom s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j) y hj φ B.hom hpb
  haveI : IsProper B.hom := MorphismProperty.of_isPullback (P := @IsProper) hpb hG
  have hqQ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver (pullback.snd (G.hom ≫ s) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j)) :=
    (_root_.GlobalTheory.isQProjOver_baseChange_and_finite_restrict R A j _ _).1 hq
  have he : pullback.lift (f := G.hom ≫ s) (g := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j) φ B.hom
      (by rw [← hj, ← Category.assoc, hpb.w, Category.assoc]) ≫
        pullback.snd (G.hom ≫ s) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j) = B.hom := pullback.lift_snd _ _ _
  haveI : IsProper (pullback.lift (f := G.hom ≫ s) (g := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j) φ B.hom
      (by rw [← hj, ← Category.assoc, hpb.w, Category.assoc]) ≫
        pullback.snd (G.hom ≫ s) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j)) := by rw [he]; infer_instance
  rw [← he]
  exact _root_.GlobalTheory.isProjOver_of_isProper_of_isImmersion _ hqQ

end GlobalTheory
end
