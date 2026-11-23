module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle508
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle494
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace UpperTheory.Gal.TranscendenceTraces

def PhiUniv : Prop := ∀ (Q : ℕ) {Z S : Scheme.{0}} (p : Z ⟶ S) (G J : Shv (ZMod Q)) (t : Fam0 p G J),
  ∃! m : (phi p (ZMod Q)).obj G ⟶ J, ∀ A a, Sec.map m ((phiE p G).app A a) = t.app A a

def DSOne : Prop := ∀ (R : Type) [CommRing R] {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (T : ShortComplex (Shv R)), T.Exact →
  ∀ (U : Scheme.{0}) (u : U ⟶ S) (b : Sec T.X₂ (pullback p u)), Sec.map T.g b = 0 →
  Loc U fun V g => ∃ a : DS p T.X₁ V, DS.map p T.f V a = DS.res p T.X₂ g (inc p T.X₂ u b)

def DSLoc : Prop := ∀ (R : Type) [CommRing R] {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (T : ShortComplex (Shv R)), T.Exact →
  ∀ (U : Scheme.{0}) (x : DS p T.X₂ U), DS.map p T.g U x = 0 →
  Loc U fun V g => ∃ a : DS p T.X₁ V, DS.map p T.f V a = DS.res p T.X₂ g x

def PhiExact : Prop := ∀ (R : Type) [CommRing R] {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (T : ShortComplex (Shv R)),
  T.Exact → (T.map (phi p R)).Exact

def PhiQis : Prop := ∀ (R : Type) [CommRing R] (Φ : Shv R ⥤ Shv R) [Φ.Additive],
  (∀ T : ShortComplex (Shv R), T.Exact → (T.map Φ).Exact) → ∀ F : Shv R,
  ∃ ε : sgl (Φ.obj F) ⟶ (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj (res R F), QuasiIso ε ∧
    sglι (Φ.obj F) ≫ ε.f 0 = Φ.map (resι R F)

def ExtRes : Prop := ∀ (R : Type) [CommRing R] (F G : Shv R) (T : Cx R) (ε : sgl F ⟶ T) [QuasiIso ε],
  (∀ a : F ⟶ G, ∃ m : T ⟶ res R G, sglι F ≫ ε.f 0 ≫ m.f 0 = a ≫ resι R G) ∧
  ∀ m m' : T ⟶ res R G, sglι F ≫ ε.f 0 ≫ m.f 0 = sglι F ≫ ε.f 0 ≫ m'.f 0 → ∀ (U : Scheme.{0}) (i n k : ℤ), i + 1 = n → n + 1 = k →
    ∀ y : Sec (T.X n) U, Sec.map (T.d n k) y = 0 → ∃ c, Sec.map ((res R G).d i n) c = Sec.map (m.f n) y - Sec.map (m'.f n) y

def FamHom : Prop := ∀ (Q : ℕ) {Z S : Scheme.{0}} (p : Z ⟶ S) (Φ : Shv (ZMod Q) ⥤ Shv (ZMod Q)) [Φ.Additive]
  (e : ∀ G, Fam0 p G (Φ.obj G)), Rep0 p Q Φ e → ∀ I J : Cx (ZMod Q),
  (∀ m : (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J, ∃ τ : Fam p I J,
    ∀ n A a, (τ.deg n).app A a = Sec.map (F := Φ.obj (I.X n)) (m.f n) ((e (I.X n)).app A a)) ∧
  ∀ τ : Fam p I J, ∃ m : (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J,
    ∀ n A a, (τ.deg n).app A a = Sec.map (F := Φ.obj (I.X n)) (m.f n) ((e (I.X n)).app A a)

end UpperTheory.Gal.TranscendenceTraces

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem cohomologyClass_mk_zsmul {R : Type} [CommRing R] {K L : Cx R} {n : ℤ} (d : ℤ) (a : Cocycle K L n) :
    CohomologyClass.mk (d • a) = d • CohomologyClass.mk a :=
  map_zsmul (CohomologyClass.mkAddMonoidHom K L n) d a

private theorem ev_cocycle_add {R : Type} [CommRing R] (I : Cx R) (X : Scheme) (n : ℤ) (h0 : -((0 : ℕ) : ℤ) + n = n)
    (α β : Cocycle ((chains R).obj (sch.obj X)) I n) :
    ev ((α + β : Cocycle ((chains R).obj (sch.obj X)) I n) : Cochain ((chains R).obj (sch.obj X)) I n) 0 n h0 X (𝟙 X) =
      ev (α : Cochain ((chains R).obj (sch.obj X)) I n) 0 n h0 X (𝟙 X) +
        ev (β : Cochain ((chains R).obj (sch.obj X)) I n) 0 n h0 X (𝟙 X) := by
  rw [Cocycle.coe_add]
  exact ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := I) (n := n)).1 _ _ 0 n h0 X (𝟙 X)).1

private theorem ev_cocycle_zsmul {R : Type} [CommRing R] (I : Cx R) (X : Scheme) (n : ℤ) (h0 : -((0 : ℕ) : ℤ) + n = n)
    (d : ℤ) (α : Cocycle ((chains R).obj (sch.obj X)) I n) :
    ev ((d • α : Cocycle ((chains R).obj (sch.obj X)) I n) : Cochain ((chains R).obj (sch.obj X)) I n) 0 n h0 X (𝟙 X) =
      d • ev (α : Cochain ((chains R).obj (sch.obj X)) I n) 0 n h0 X (𝟙 X) := by
  rw [Cocycle.coe_smul]
  exact ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := I) (n := n)).1 _ 0 0 n h0 X (𝟙 X)).2.2.2 d

theorem UpperTheory.Gal.TranscendenceTraces.rpBasic_of :
    RpBasic := by
  intro R _ I X n
  have ev_lin := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := I) (n := n)
  have key := fun (α : Cocycle ((chains R).obj (sch.obj X)) I n) =>
    (GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R X I (n - 1) n (n + 1) (by ring) rfl).2 α
  have h0 : -((0 : ℕ) : ℤ) + n = n := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
    exact ⟨_, α, rfl, rfl⟩
  · rintro x a ⟨α, -, rfl⟩
    exact (key α).1
  · rintro x x' a a' ⟨α, rfl, ha⟩ ⟨β, rfl, hb⟩
    subst ha hb
    have hiff : CohomologyClass.mk α = CohomologyClass.mk β ↔
        ∃ y, Sec.map (I.d (n - 1) n) y =
          ev (α : Cochain ((chains R).obj (sch.obj X)) I n) 0 n h0 X (𝟙 X) -
            ev (β : Cochain ((chains R).obj (sch.obj X)) I n) 0 n h0 X (𝟙 X) := by
      rw [← sub_eq_zero, ← CohomologyClass.mk_sub, (key (α - β)).2, Cocycle.coe_sub,
        (ev_lin.1 (α : Cochain _ I n) β 0 n h0 X (𝟙 X)).2.1]
    refine ⟨hiff, fun h => hiff.2 ⟨0, ?_⟩, ⟨α + β, CohomologyClass.mk_add α β, ev_cocycle_add I X n h0 α β⟩,
      fun d => ⟨d • α, cohomologyClass_mk_zsmul d α, ev_cocycle_zsmul I X n h0 d α⟩⟩
    rw [h, sub_self]
    exact map_zero _
  · rintro Y f x a ⟨α, rfl, rfl⟩
    refine ⟨zcomp (Cocycle.ofHom ((chains R).map (sch.map f))) α (zero_add n), rfl, ?_⟩
    have h1 := ev_lin.2.2.2.1 (sch.map f) (α : Cochain _ I n) 0 n h0 Y (𝟙 Y)
    have h2 := ev_lin.2.1 (α : Cochain _ I n) 0 n h0 Y X f (𝟙 X)
    exact h1.trans h2.symm
  · rintro R' _ J ρ x a ⟨α, rfl, rfl⟩
    obtain ⟨β, hβ⟩ := SemiMap.image_exists ρ (sch.obj X) n α
    exact ⟨β, (SemiMap.op_spec ρ (sch.obj X) n α β hβ).symm, hβ 0 n h0 X (𝟙 X)⟩
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces
open scoped TensorProduct

theorem UpperTheory.Gal.TranscendenceTraces.locFinAff_of :
    Chart → RingSplit → LocFinAff := by
  intro hC hR W V U _ π r _ _ _ x
  let A := Γ(U, ⊤)
  let u : Spec (CommRingCat.of A) ⟶ U := U.isoSpec.inv
  obtain ⟨B, _, _, v, _, hpb⟩ := hC r A u
  haveI : IsIso v := hpb.isIso_fst_of_isIso
  let f : W ⟶ Spec (CommRingCat.of B) := π ≫ inv v
  obtain ⟨C, g, h, hg, hh⟩ := GlobalTheory.T.exists_etaleFaithfullyFlat_refining_etale_surjection (CommRingCat.of B) W f inferInstance inferInstance
  letI : Algebra B C := g.hom.toAlgebra
  haveI : Algebra.Etale B C := hg.1
  haveI : Module.FaithfullyFlat B C := hg.2
  let P : PrimeSpectrum A := U.isoSpec.hom x
  obtain ⟨E, _, _, hE, ⟨Q, hQ⟩, ⟨φ⟩⟩ := hR A B C P
  let gE : Spec (CommRingCat.of E) ⟶ U := Spec.map (CommRingCat.ofHom (algebraMap A E)) ≫ u
  haveI : Etale (Spec.map (CommRingCat.ofHom (algebraMap A E))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hE)
  have big := (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A B E)).paste_horiz hpb
  have hhπ : h ≫ π = Spec.map g ≫ v := by
    rw [← hh]
    simp [f]
  refine ⟨Spec (CommRingCat.of E), gE, inferInstance, inferInstance, ⟨Q, ?_⟩, ?_⟩
  · change u (Spec.map (CommRingCat.ofHom (algebraMap A E)) Q) = x
    have e : Spec.map (CommRingCat.ofHom (algebraMap A E)) Q = P := hQ
    rw [e]
    show U.isoSpec.inv (U.isoSpec.hom x) = x
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  · refine ⟨big.lift (pullback.fst r gE) (pullback.snd r gE) pullback.condition ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ h, ?_⟩
    have eφ : g ≫ CommRingCat.ofHom φ.toRingHom = CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom := by
      ext b
      exact φ.commutes b
    rw [Category.assoc, Category.assoc, hhπ, ← Category.assoc (Spec.map _) (Spec.map g) v, ← Spec.map_comp, eφ]
    exact big.lift_fst _ _ _
end
