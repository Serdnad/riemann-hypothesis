module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle742
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle743
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS

noncomputable section

namespace GlobalTheory.SpecField

open AlgebraicGeometry

variable {A : Type} [CommRing A]

theorem dualMap_fst {B : Type} [CommRing B] (f : A →+* B) (x : DualNumber A) :
    (Formalism.L2.Pj.dualMap f x).fst = f x.fst := by
  simp [Formalism.L2.Pj.dualMap]

theorem dualMap_snd {B : Type} [CommRing B] (f : A →+* B) (x : DualNumber A) :
    (Formalism.L2.Pj.dualMap f x).snd = f x.snd := by
  simp [Formalism.L2.Pj.dualMap]

variable (σ : A →+* DualNumber A) (hσ : ∀ a, (σ a).fst = a) (S : Submonoid A)

def liftLoc : LocalizedModule S A →+* DualNumber (LocalizedModule S A) :=
  IsLocalization.lift (M := S) (g := (Formalism.L2.Pj.dualMap (algebraMap A (LocalizedModule S A))).comp σ)
    (fun y => by
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, RingHom.comp_apply, dualMap_fst, hσ]
      exact IsLocalization.map_units _ y)

theorem liftLoc_algebraMap (a : A) :
    liftLoc σ hσ S (algebraMap A _ a) = Formalism.L2.Pj.dualMap (algebraMap A (LocalizedModule S A)) (σ a) :=
  IsLocalization.lift_eq _ _

theorem liftLoc_fst (b : LocalizedModule S A) : (liftLoc σ hσ S b).fst = b := by
  have h : ((TrivSqZeroExt.fstHom (LocalizedModule S A) (LocalizedModule S A) (LocalizedModule S A)).toRingHom.comp
      (liftLoc σ hσ S)) = RingHom.id _ :=
    IsLocalization.ringHom_ext S (RingHom.ext fun a => by
      simp [liftLoc_algebraMap, dualMap_fst, hσ])
  exact congrArg (fun φ => φ b) h

def dloc (b : LocalizedModule S A) : LocalizedModule S A := (liftLoc σ hσ S b).snd

theorem dloc_add (b b' : LocalizedModule S A) : dloc σ hσ S (b + b') = dloc σ hσ S b + dloc σ hσ S b' := by
  simp [dloc]

theorem dloc_mul (b b' : LocalizedModule S A) :
    dloc σ hσ S (b * b') = b * dloc σ hσ S b' + b' * dloc σ hσ S b := by
  simp only [dloc, map_mul, TrivSqZeroExt.snd_mul, liftLoc_fst, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op]
  ring

theorem dloc_algebraMap (a : A) : dloc σ hσ S (algebraMap A _ a) = algebraMap A _ (σ a).snd := by
  simp [dloc, liftLoc_algebraMap, dualMap_snd]

theorem mk_mul_algebraMap (m : A) (u : S) :
    LocalizedModule.mk m u * algebraMap A (LocalizedModule S A) u = algebraMap A _ m := by
  rw [show algebraMap A (LocalizedModule S A) u = LocalizedModule.mk (u : A) 1 from rfl]
  erw [LocalizedModule.mk_mul_mk]
  rw [show algebraMap A (LocalizedModule S A) m = LocalizedModule.mk m 1 from rfl, LocalizedModule.mk_eq]
  exact ⟨1, by simp [Submonoid.smul_def, smul_eq_mul]; ring⟩

theorem dloc_mk (r : A) (t : S) :
    dloc σ hσ S (LocalizedModule.mk r t) =
      LocalizedModule.mk (t * (σ r).snd - r * (σ t).snd) (t * t) := by
  have h1 := mk_mul_algebraMap S r t
  have h2 := congrArg (dloc σ hσ S) h1
  rw [dloc_mul, dloc_algebraMap, dloc_algebraMap] at h2
  have hu : IsUnit (algebraMap A (LocalizedModule S A) ((t * t : S) : A)) := IsLocalization.map_units _ (t * t)
  refine (hu.mul_left_inj).1 ?_
  rw [mk_mul_algebraMap]
  simp only [Submonoid.coe_mul, map_mul, map_sub]
  linear_combination (algebraMap A (LocalizedModule S A) t) * h2 -
    (algebraMap A (LocalizedModule S A) (σ t).snd) * h1

def dsec (O : (Sp A).Opens) (s : Γ(Sp A, O)) : Γ(Sp A, O) :=
  ⟨fun x => dloc σ hσ _ (s.1 x), fun x => by
    obtain ⟨V, hxV, i, r, t, w⟩ := s.2 x
    refine ⟨V, hxV, i, t * (σ r).snd - r * (σ t).snd, t * t, fun y => ?_⟩
    obtain ⟨ht, hs⟩ := w y
    refine ⟨fun h => ((PrimeSpectrum.isPrime (y.1 : PrimeSpectrum A)).mem_or_mem h).elim ht ht, ?_⟩
    exact (congrArg (dloc σ hσ _) hs).trans (dloc_mk σ hσ _ r ⟨t, ht⟩)⟩

theorem isField_dsec : IsField ⊤ (dsec σ hσ) :=
  ⟨fun _ _ f f' => Subtype.ext (funext fun x => dloc_add σ hσ _ (f.1 x) (f'.1 x)),
    fun _ _ f f' => Subtype.ext (funext fun x => dloc_mul σ hσ _ (f.1 x) (f'.1 x)),
    fun _ _ _ _ _ => rfl⟩

theorem dsec_top (a : A) :
    dsec σ hσ ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (σ a).snd :=
  Subtype.ext (funext fun x => dloc_algebraMap σ hσ _ a)

end GlobalTheory.SpecField

theorem GlobalTheory.SpecField.exists_isField (A : Type) [CommRing A] (σ : A →+* DualNumber A) (hσ : ∀ a, (σ a).fst = a) :
    ∃ d : ∀ O : (Sp A).Opens, Γ(Sp A, O) → Γ(Sp A, O), IsField ⊤ d ∧
      ∀ a : A, d ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (σ a).snd :=
  ⟨GlobalTheory.SpecField.dsec σ hσ, GlobalTheory.SpecField.isField_dsec σ hσ, GlobalTheory.SpecField.dsec_top σ hσ⟩
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace GlobalTheory.InvFieldRing

attribute [local instance] Over.cartesianMonoidalCategory

section Val

variable {A : Type} [CommRing A] {Y : Scheme.{0}}

theorem valR_of (x : Sp A ⟶ Y) (V : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(Y, V)) :
    valR x V f = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE V ⊤ h).hom f) := by
  unfold valR
  rw [dite_eq_left h]

theorem valR_add (x : Sp A ⟶ Y) (V : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) (f g : Γ(Y, V)) :
    valR x V (f + g) = valR x V f + valR x V g := by
  simp only [valR_of x V h, map_add (f := _)]

theorem valR_mul (x : Sp A ⟶ Y) (V : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) (f g : Γ(Y, V)) :
    valR x V (f * g) = valR x V f * valR x V g := by
  simp only [valR_of x V h, map_mul]

theorem valR_appLE {Z : Scheme.{0}} (x : Sp A ⟶ Z) (g : Z ⟶ Y) (V : Y.Opens) (W : Z.Opens) (e : W ≤ g ⁻¹ᵁ V)
    (h : ⊤ ≤ x ⁻¹ᵁ W) (f : Γ(Y, V)) : valR x W ((g.appLE V W e).hom f) = valR (x ≫ g) V f := by
  have h' : ⊤ ≤ (x ≫ g) ⁻¹ᵁ V := h.trans (x.preimage_mono e)
  rw [valR_of x W h, valR_of (x ≫ g) V h', ← Scheme.Hom.appLE_comp_appLE x g V W ⊤ e h]
  rfl

theorem valR_constFn {B : Type} [CommRing B] (x : Sp A ⟶ Y) (p : Y ⟶ Sp B) (ψ : B →+* A) (hx : x ≫ p = spMap ψ)
    (V : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) (a : B) : valR x V (constFn p V a) = ψ a := by
  unfold constFn
  refine (valR_appLE x p ⊤ V (fun _ _ => trivial) h _).trans ?_
  rw [hx, valR_of _ _ le_rfl]
  have n := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ))
  have e' : ((spMap ψ).appLE ⊤ ⊤ le_rfl) = (spMap ψ).appTop := (Scheme.Hom.app_eq_appLE _).symm
  change (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (ψ a) =
    (spMap ψ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom a) at n
  rw [e', ← n]
  exact (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id_apply _

theorem valR_spMap_comp {A' : Type} [CommRing A'] (ψ : A →+* A') (x : Sp A ⟶ Y) (V : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V)
    (f : Γ(Y, V)) : valR (spMap ψ ≫ x) V f = ψ (valR x V f) := by
  have h' : ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ V := fun y _ => h (Set.mem_univ ((spMap ψ) y))
  rw [valR_of _ V h', valR_of x V h]
  have e : (spMap ψ ≫ x).appLE V ⊤ h' = x.appLE V ⊤ h ≫ (spMap ψ).appTop :=
    (Scheme.Hom.appLE_comp_appLE (spMap ψ) x V ⊤ ⊤ h le_rfl).symm
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  change ((spMap ψ ≫ x).appLE V ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of A')).hom).hom f =
    (x.appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom ψ).hom f
  rw [e, Category.assoc, n]

end Val

section Geo

theorem surjective_spMap_fst (R : Type) [CommRing R] : Surjective (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  have hs : Function.Surjective (TrivSqZeroExt.fstHom R R R).toRingHom := fun x => ⟨TrivSqZeroExt.inl x, rfl⟩
  refine ⟨fun P => ?_⟩
  have : P ∈ Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    rw [range_comap_of_surjective _ _ hs]
    intro x hx
    refine (P : PrimeSpectrum (DualNumber R)).2.mem_of_pow_mem 2 ?_
    have hx' : x.fst = 0 := hx
    have : x ^ 2 = 0 := by ext <;> simp [sq, hx']
    rw [this]; exact zero_mem _
  exact this

theorem spMap_fst_comp (R : Type) [CommRing R] :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

theorem appLE_eq_of_eq {Y Z : Scheme.{0}} {g g' : Z ⟶ Y} (hg : g = g') (V : Y.Opens) (W : Z.Opens)
    (e : W ≤ g ⁻¹ᵁ V) (e' : W ≤ g' ⁻¹ᵁ V) : g.appLE V W e = g'.appLE V W e' := by
  subst hg
  rfl

theorem appLE_appLE {Y Z Q : Scheme.{0}} (g : Z ⟶ Y) (k : Q ⟶ Z) (V : Y.Opens) (W : Z.Opens) (W' : Q.Opens)
    (e : W ≤ g ⁻¹ᵁ V) (e' : W' ≤ k ⁻¹ᵁ W) (f : Γ(Y, V)) :
    (k.appLE W W' e').hom ((g.appLE V W e).hom f) = ((k ≫ g).appLE V W' (e'.trans (k.preimage_mono e))).hom f := by
  rw [← Scheme.Hom.appLE_comp_appLE k g V W W' e e']
  rfl

theorem appLE_res {Y Z : Scheme.{0}} (g : Z ⟶ Y) {V V' : Y.Opens} {W W' : Z.Opens} (h : V' ≤ V) (h' : W' ≤ W)
    (e : W ≤ g ⁻¹ᵁ V) (e' : W' ≤ g ⁻¹ᵁ V') (f : Γ(Y, V)) :
    (g.appLE V' W' e').hom (resG Y h f) = resG Z h' ((g.appLE V W e).hom f) := by
  change (Y.presheaf.map (homOfLE h).op ≫ g.appLE V' W' e').hom f = (g.appLE V W e ≫ Z.presheaf.map (homOfLE h').op).hom f
  rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

theorem appLE_constFn {R : Type} [CommRing R] {Z Q : Scheme.{0}} (p : Z ⟶ Sp R) (k : Q ⟶ Z) (W : Z.Opens)
    (W' : Q.Opens) (e' : W' ≤ k ⁻¹ᵁ W) (a : R) : (k.appLE W W' e').hom (constFn p W a) = constFn (k ≫ p) W' a := by
  unfold constFn
  exact appLE_appLE p k ⊤ W W' _ e' _

theorem constFn_spMap {R S : Type} [CommRing R] [CommRing S] {Y : Scheme.{0}} (q : Y ⟶ Sp S) (φ : R →+* S)
    (O : Y.Opens) (a : R) : constFn (q ≫ spMap φ) O a = constFn q O (φ a) := by
  have h : (spMap φ).appLE ⊤ ⊤ (fun _ _ => trivial) = (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, ← Scheme.Hom.appLE_eq_app]; rfl
  have h2 := congrArg (fun ψ => ψ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  have h3 := congrArg (fun ψ => ψ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE q (spMap φ) ⊤ ⊤ O (fun _ _ => trivial) (fun _ _ => trivial))
  rw [h] at h3
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2 h3
  unfold constFn
  rw [← h3, h2]

theorem constFn_eps_sq {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Sp (DualNumber R)) (O : Y.Opens) :
    constFn p O DualNumber.eps * constFn p O DualNumber.eps = 0 := by
  simp only [constFn, ← map_mul, DualNumber.eps_mul_eps, map_zero]

theorem res_constFn {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Sp R) {V W : Y.Opens} (h : W ≤ V) (a : R) :
    resG Y h (constFn f V a) = constFn f W a :=
  congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (f.appLE_map (U := ⊤) (fun _ _ => trivial) (homOfLE h).op)

theorem res_app {Y Z : Scheme.{0}} (f : Z ⟶ Y) {V W : Y.Opens} (h : W ≤ V) (h' : f ⁻¹ᵁ W ≤ f ⁻¹ᵁ V) (a : Γ(Y, V)) :
    resG Z h' ((f.app V).hom a) = (f.app W).hom (resG Y h a) := by
  change (f.app V ≫ Z.presheaf.map (homOfLE h').op).hom a = (Y.presheaf.map (homOfLE h).op ≫ f.app W).hom a
  rw [Scheme.Hom.naturality]
  rfl

end Geo

section Group

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  (U : X.affineOpens) (u : Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)

def tanPt (hu : IsTanAtG t (chart U) u) : tEpsG (chart U) ⟶ t.G := Over.homMk u hu.1

def transl (hu : IsTanAtG t (chart U) u) : tEpsG (chart U) ⊗ t.G ⟶ t.G :=
  snd _ t.G * (fst _ t.G ≫ tanPt t U u hu)

end Group

section Group2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  (U : X.affineOpens) (u : Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)

end Group2

end GlobalTheory.InvFieldRing
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.CechKSSmul

theorem valR_mul_of_le {A : Type} [CommRing A] {Z : Scheme.{0}} (x : Sp A ⟶ Z) (O : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ O) (a b : Γ(Z, O)) : valR x O (a * b) = valR x O a * valR x O b := by
  simp only [valR, dif_pos h, map_mul]

theorem valR_sub_of_le {A : Type} [CommRing A] {Z : Scheme.{0}} (x : Sp A ⟶ Z) (O : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ O) (a b : Γ(Z, O)) : valR x O (a - b) = valR x O a - valR x O b := by
  simp only [valR, dif_pos h, map_sub]

theorem valR_appLE_comp {A : Type} [CommRing A] {Y Z : Scheme.{0}} (x : Sp A ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens)
    (W : Y.Opens) (e : W ≤ g ⁻¹ᵁ U) (h : ⊤ ≤ x ⁻¹ᵁ W) (a : Γ(Z, U)) :
    valR x W ((g.appLE U W e).hom a) = valR (x ≫ g) U a := by
  have h' : ⊤ ≤ (x ≫ g) ⁻¹ᵁ U := fun y hy => e (h hy)
  simp only [valR, dif_pos h, dif_pos h']
  exact congrArg (fun q => (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (q.hom a))
    (Scheme.Hom.appLE_comp_appLE x g U W ⊤ e h)

theorem fromSpec_appLE_top_eq {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ h = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  convert Category.comp_id _
  exact (Spec Γ(X, U)).presheaf.map_id _

theorem valR_spMap_chart {X : Scheme.{0}} (U : X.affineOpens) {S : Type} [CommRing S] (φ : Γ(X, U.1) →+* S)
    (r : Γ(X, U.1)) : valR (spMap φ ≫ chart U) U.1 r = φ r := by
  have h1 : ⊤ ≤ (chart U) ⁻¹ᵁ U.1 := by
    show ⊤ ≤ U.2.fromSpec ⁻¹ᵁ U.1
    rw [U.2.fromSpec_preimage_self]
  rw [← valR_appLE_comp (spMap φ) (chart U) U.1 ⊤ h1 (fun _ _ => trivial)]
  have e : (chart U).appLE U.1 ⊤ h1 = (Scheme.ΓSpecIso Γ(X, U.1)).inv := by
    exact fromSpec_appLE_top_eq U.2 h1
  rw [e]
  simp only [valR, dif_pos (show ⊤ ≤ spMap φ ⁻¹ᵁ ⊤ from fun _ _ => trivial)]
  have e2 : (spMap φ).appLE ⊤ ⊤ (fun _ _ => trivial) = (spMap φ).appTop :=
    Scheme.Hom.appLE_eq_app (f := spMap φ) (U := ⊤)
  rw [e2]
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have := congrArg (fun q => q.hom ((Scheme.ΓSpecIso Γ(X, U.1)).inv.hom r)) n
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  rw [this]
  congr 1
  exact (Scheme.ΓSpecIso Γ(X, U.1)).inv_hom_id_apply r

theorem resG_appLE' {Y Z : Scheme.{0}} (f : Y ⟶ Z) {W : Z.Opens} {O O' : Y.Opens} (h : O' ≤ O) (e : O ≤ f ⁻¹ᵁ W)
    (a : Γ(Z, W)) : resG Y h ((f.appLE W O e).hom a) = (f.appLE W O' (h.trans e)).hom a := by
  rw [← Scheme.Hom.appLE_map f e (homOfLE h).op]
  rfl

end GlobalTheory.CechKSSmul
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS

namespace GlobalTheory.FieldTransport

theorem exists_isField_transport : ∀ (Z : Scheme.{0}) (W : Z.Opens) (hW : IsAffineOpen W) (δ : Γ(Z, W) → Γ(Z, W)) (d' : ∀ O : (Spec Γ(Z, W)).Opens, Γ(Spec Γ(Z, W), O) → Γ(Spec Γ(Z, W), O)), IsField ⊤ d' → (∀ a, d' ⊤ ((Scheme.ΓSpecIso Γ(Z, W)).inv.hom a) = (Scheme.ΓSpecIso Γ(Z, W)).inv.hom (δ a)) → ∃ d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O), IsField W d ∧ ∀ a, d W a = δ a := by
  intro Z W hW δ d' hd hδ
  classical
  have hiso : ∀ O : Z.Opens, O ≤ W → IsIso (hW.fromSpec.app O) := fun O h =>
    hW.fromSpec.isIso_app O (by rwa [hW.opensRange_fromSpec])
  let e : ∀ O : Z.Opens, O ≤ W → Γ(Z, O) ≃+* Γ(Spec Γ(Z, W), hW.fromSpec ⁻¹ᵁ O) := fun O h =>
    haveI := hiso O h; (asIso (hW.fromSpec.app O)).commRingCatIsoToRingEquiv
  have he : ∀ O (h : O ≤ W) f, e O h f = (hW.fromSpec.app O).hom f := fun _ _ _ => rfl
  have hres : ∀ O O' (h : O' ≤ O) (f : Γ(Z, O)),
      (hW.fromSpec.app O').hom (resG Z h f) =
        resG (Spec Γ(Z, W)) (hW.fromSpec.preimage_mono h) ((hW.fromSpec.app O).hom f) := by
    intro O O' h f
    have := congrArg (fun g => g.hom f) (hW.fromSpec.naturality (homOfLE h).op)
    simpa [resG] using this
  refine ⟨fun O f => if h : O ≤ W then (e O h).symm (d' (hW.fromSpec ⁻¹ᵁ O) (e O h f)) else 0,
    ⟨?_, ?_, ?_⟩, ?_⟩
  · intro O h f f'
    simp only [dif_pos h, map_add (f := _), hd.1 _ le_top]
  · intro O h f f'
    simp only [dif_pos h, map_mul, hd.2.1 _ le_top, map_add (f := _), RingEquiv.symm_apply_apply]
  · intro O O' h hO f
    have hO' : O' ≤ W := h.trans hO
    simp only [dif_pos hO, dif_pos hO']
    apply (e O' hO').injective
    simp only [RingEquiv.apply_symm_apply, he O' hO', hres]
    rw [← he O hO, ← he O hO, RingEquiv.apply_symm_apply, hd.2.2 _ _ _ le_top]
    exact (e O' hO').apply_symm_apply _
  · intro a
    simp only [dif_pos (le_refl W)]
    apply (e W (le_refl W)).symm_apply_eq.mpr
    have hs : hW.fromSpec ⁻¹ᵁ W ≤ ⊤ := le_top
    have key : ∀ x, e W (le_refl W) x = resG (Spec Γ(Z, W)) hs ((Scheme.ΓSpecIso Γ(Z, W)).inv.hom x) := by
      intro x
      rw [he W (le_refl W), IsAffineOpen.fromSpec_app_self, CommRingCat.comp_apply]
      rfl
    rw [key, key, hd.2.2 _ _ hs le_rfl, hδ]

end GlobalTheory.FieldTransport
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LogKS.FieldImage

variable {Z Z' : Scheme.{0}} (φ : Z' ⟶ Z) [IsOpenImmersion φ]

def appEquiv (O : Z.Opens) (h : O ≤ φ.opensRange) : Γ(Z, O) ≃+* Γ(Z', φ ⁻¹ᵁ O) :=
  haveI := Scheme.Hom.isIso_app φ O h
  (asIso (φ.app O)).commRingCatIsoToRingEquiv

theorem appEquiv_apply (O : Z.Opens) (h : O ≤ φ.opensRange) (f : Γ(Z, O)) :
    appEquiv φ O h f = (φ.app O).hom f := rfl

theorem app_res {W W' : Z.Opens} (h : W' ≤ W) (f : Γ(Z, W)) :
    (φ.app W').hom (resG Z h f) = resG Z' (Scheme.Hom.preimage_mono φ h) ((φ.app W).hom f) := by
  have := congrArg (fun g => g.hom f) (Scheme.Hom.naturality φ (homOfLE h).op)
  simpa [resG] using this


open Classical in
def push (d : ∀ O : Z'.Opens, Γ(Z', O) → Γ(Z', O)) (O : Z.Opens) (f : Γ(Z, O)) : Γ(Z, O) :=
  if h : O ≤ φ.opensRange then (appEquiv φ O h).symm (d (φ ⁻¹ᵁ O) ((φ.app O).hom f)) else 0

theorem app_push (d : ∀ O : Z'.Opens, Γ(Z', O) → Γ(Z', O)) (O : Z.Opens) (h : O ≤ φ.opensRange)
    (f : Γ(Z, O)) : (φ.app O).hom (push φ d O f) = d (φ ⁻¹ᵁ O) ((φ.app O).hom f) := by
  rw [push, dite_eq_left h, ← appEquiv_apply φ O h, RingEquiv.apply_symm_apply]

theorem le_range {W₀ : Z'.Opens} {O : Z.Opens} (hO : O ≤ φ ''ᵁ W₀) : O ≤ φ.opensRange :=
  hO.trans (Scheme.Hom.image_le_opensRange φ W₀)

theorem preimage_le {W₀ : Z'.Opens} {O : Z.Opens} (hO : O ≤ φ ''ᵁ W₀) : φ ⁻¹ᵁ O ≤ W₀ := by
  have := Scheme.Hom.preimage_mono φ hO
  rwa [Scheme.Hom.preimage_image_eq] at this

theorem inj_app {O : Z.Opens} (h : O ≤ φ.opensRange) : Function.Injective (φ.app O).hom :=
  (appEquiv φ O h).injective

theorem isField_push (W₀ : Z'.Opens) (d : ∀ O : Z'.Opens, Γ(Z', O) → Γ(Z', O)) (hd : IsField W₀ d) :
    IsField (φ ''ᵁ W₀) (push φ d) := by
  obtain ⟨hadd, hmul, hres⟩ := hd
  refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h hW f => ?_⟩
  · apply inj_app φ (le_range φ hW)
    rw [map_add (f := _), app_push φ d W (le_range φ hW), app_push φ d W (le_range φ hW),
      app_push φ d W (le_range φ hW), map_add, hadd _ (preimage_le φ hW)]
  · apply inj_app φ (le_range φ hW)
    rw [map_add (f := _), map_mul, map_mul, app_push φ d W (le_range φ hW), app_push φ d W (le_range φ hW),
      app_push φ d W (le_range φ hW), map_mul, hmul _ (preimage_le φ hW)]
  · have hW' : W' ≤ φ ''ᵁ W₀ := h.trans hW
    apply inj_app φ (le_range φ hW')
    rw [app_push φ d W' (le_range φ hW'), app_res, app_res, app_push φ d W (le_range φ hW),
      hres _ _ _ (preimage_le φ hW)]

end GlobalTheory.LogKS.FieldImage

theorem GlobalTheory.LogKS.isField_image : ∀ (Z Z' : Scheme.{0}) (φ : Z' ⟶ Z) [IsOpenImmersion φ] (W₀ : Z'.Opens) (d : ∀ O : Z'.Opens, Γ(Z', O) → Γ(Z', O)), IsField W₀ d → ∃ d₂ : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O), IsField (φ ''ᵁ W₀) d₂ ∧ ∀ (O : Z.Opens), O ≤ φ ''ᵁ W₀ → ∀ f : Γ(Z, O), (φ.app O).hom (d₂ O f) = d (φ ⁻¹ᵁ O) ((φ.app O).hom f) := by
  intro Z Z' φ _ W₀ d hd
  exact ⟨FieldImage.push φ d, FieldImage.isField_push φ W₀ d hd,
    fun O hO f => FieldImage.app_push φ d O (FieldImage.le_range φ hO) f⟩
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isIsogenyDegree_killedBy_primeToP_harrisTaylor : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s), (∀ c : 𝓞 D.F, c ≠ 0 → GlobalTheory.IwLevel.IsIsogDeg (o.act.act (algebraMap (𝓞 D.F) D.O c)) ((Algebra.norm ℤ c).natAbs ^ (D.m * D.n))) → ∀ (𝔟 : Ideal (𝓞 D.F)), 𝔟 ⊔ Ideal.span {(p : 𝓞 D.F)} = ⊤ → ∀ (K : Over S) (i : K ⟶ o.A), Mono i → (∀ (T : Over S) (x : T ⟶ o.A), GlobalTheory.IwLevel.InSub i x ↔ GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (𝔟.map (algebraMap (𝓞 D.F) D.O)) x) → GlobalTheory.IwLevel.IsIsogDeg (toUnit K) (Ideal.absNorm 𝔟 ^ (D.m * D.n)) := by
  first | (exact @GlobalTheory.IwLevel.PrimeToP.isIsogDeg_killedBy) | (exact GlobalTheory.IwLevel.PrimeToP.isIsogDeg_killedBy) | (intros; apply GlobalTheory.IwLevel.PrimeToP.isIsogDeg_killedBy <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.casimir_central_and_on_highestWeight : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → (∀ Z, casimir act * act Z = act Z * casimir act) ∧ ∀ (μ : Ix p q → ℚ) (v : V), v ∈ hwSub act μ → (∑ a, ∑ b, if sameBlock a b then act (Eab a b) (act (Eab b a) v) else 0) = ((∑ a, μ a ^ 2 + (∑ i : Fin p, μ (.inl i) * ((p : ℚ) - 1 - 2 * (i : ℕ))) + (∑ j : Fin q, μ (.inr j) * ((q : ℚ) - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) • v := by
  first | exact @GlobalTheory.CasimirHighest.casimir_central_and_highest | exact GlobalTheory.CasimirHighest.casimir_central_and_highest | (intros; apply GlobalTheory.CasimirHighest.casimir_central_and_highest <;> assumption)
end
