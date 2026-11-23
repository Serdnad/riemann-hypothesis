module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInOfIsPullDeg
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle060
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

@[expose] public section

open AlgebraicGeometry CategoryTheory
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable local instance (priority := high) grpObjUniformizationPullback
    {S T : Scheme.{0}} (f : T ⟶ S) (G : Over S) [GrpObj G] : GrpObj ((Over.pullback f).obj G) :=
  letI : (Over.pullback f).Monoidal := (Over.instBraidedPullback (f := f)).toMonoidal
  Functor.grpObjObj (F := Over.pullback f)

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory

namespace PsiScalIn

open PsiInPull PsiInPow

variable {R : Type} [CommRing R] [IsDomain R]

def sig (z : Spec (CommRingCat.of (FractionRing R))) :
    FractionRing R →+* (Spec (CommRingCat.of (FractionRing R))).presheaf.stalk z :=
  ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ z trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom

theorem gs_scal_id (z : Spec (CommRingCat.of (FractionRing R))) (c : FractionRing R) :
    gs (𝟙 _) z ⊤ (scal (𝟙 (Spec (CommRingCat.of (FractionRing R)))) c) = sig z c := by
  rw [gs_eq _ z ⊤ trivial]; rfl

theorem gs_toOpen (z : Spec (CommRingCat.of (FractionRing R))) (V : (Spec (CommRingCat.of R)).Opens)
    (hz : jK R z ∈ V) (r : R) : gs (jK R) z V (DegPre.toOpen V r) = sig z (algebraMap R _ r) := by
  have nat := congrArg (fun g => g.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
  refine (gs_res (jK R) z (le_top : V ≤ ⊤) hz _).trans ((gs_eq (jK R) z ⊤ trivial _).trans ?_)
  simp only [sig, RingHom.comp_apply]
  rw [nat]
  rfl

theorem key (D : DegPre R)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (a : D.X → (FractionRing R)ˣ) (h : PsiScal D ga a) (χ : D.X) (q : D.P.L.ι)
    (V : (Spec (CommRingCat.of R)).Opens) (hle : V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U q)
    (z : Spec (CommRingCat.of (FractionRing R))) (hz : jK R z ∈ V) :
    ∃ u : Γ(Spec (CommRingCat.of R), V)ˣ,
      (gm (𝟙 _) z (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) (fun _ => q)) ((D.psi χ).s (fun _ => q))).val =
        sig z (a χ).val * gs (jK R) z V u.val := by
  have hle' : V ≤ LB.wchart D.P.L (fun _ : PUnit => (D.c χ).left) (fun _ => q) := fun y hy =>
    mem_wchart _ _ _ _ (hle hy)
  obtain ⟨J, hJ, e⟩ := exists_good D.P.L D.P.isLB (Z := (TK R).left) z (K := PUnit) (fun _ => D.xK χ) (fun _ => q)
    (fun _ _ _ => rfl) (fun _ => hle hz)
  have e0 : J (D.xK χ) = q := e PUnit.unit
  have v := (h χ).2 (TK R) (𝟙 _) z J hJ
  have v1 := val_of (D.psi χ) (𝟙 _) z J (fun _ => q) (fun _ => (congrArg J (Category.id_comp _)).trans e0)
  have v2 := val_of (ga χ) (toUnit (TK R)).left z J (fun _ => q) (fun _ => e0)
  refine ⟨res hle' ((ga χ).s (fun _ => q)), (congrArg Units.val v1).symm.trans (v.trans ?_)⟩
  refine congrArg₂ (· * ·) (gs_scal_id z _) ?_
  refine (congrArg Units.val v2).trans ?_
  exact ((gs_unit _ _ _ hz _).trans (congrArg Units.val (gm_res _ _ hle' hz _))).symm

theorem main_local [IsLocalRing R] (D : DegPre R)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (a : D.X → (FractionRing R)ˣ) (h : PsiScal D ga a) (χ : D.X) (J : Ideal R) :
    D.PsiIn χ J ↔ ∃ r ∈ J, algebraMap R (FractionRing R) r = (a χ).val := by
  constructor
  · intro H
    obtain ⟨q, hq⟩ := exists_chart D.P.isLB ((D.c χ).left (IsLocalRing.closedPoint R))
    have hle : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U q := fun y _ =>
      (IsLocalRing.specializes_closedPoint y).mem_open ((D.c χ).left ⁻¹ᵁ D.P.L.U q).isOpen hq
    obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) :=
      inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
    obtain ⟨r, hr, e⟩ := gs_of_psiIn D χ J H q ⊤ (isAffineOpen_top _) hle z trivial
    obtain ⟨u, hu⟩ := key D ga a h χ q ⊤ hle z trivial
    have hs : Function.Surjective (DegPre.toOpen (R := R) ⊤) := by
      intro b
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom b, ?_⟩
      simp [DegPre.toOpen]
    obtain ⟨s, hsJ, es⟩ := (Ideal.mem_map_iff_of_surjective _ hs).1 (Ideal.mul_mem_right (u⁻¹).val _ hr)
    refine ⟨s, hsJ, (sig z).injective ?_⟩
    have hz : jK R z ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) := trivial
    rw [← gs_toOpen z ⊤ hz, es, gs_mul _ _ _ hz, e.trans hu, _root_.mul_assoc,
      ← gs_mul _ _ _ hz, Units.mul_inv, gs_eq _ _ _ hz, map_one, map_one, _root_.mul_one]
  · rintro ⟨r, hr, e⟩
    refine psiIn_of_gs D χ J fun q V _ hle z hz => ?_
    obtain ⟨u, hu⟩ := key D ga a h χ q V hle z hz
    refine ⟨DegPre.toOpen V r * u.val, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hr), ?_⟩
    rw [gs_mul _ _ _ hz, gs_toOpen z V hz, e]
    exact hu.symm

end PsiScalIn

theorem psiIn_iff_scalar_mem : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegPre V) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing V)ˣ), PsiScal D ga a → ∀ (χ : D.X) (J : Ideal V), J ≠ ⊥ → (D.PsiIn χ J ↔ ∃ r ∈ J, algebraMap V (FractionRing V) r = (a χ).val) :=
  fun _ _ _ _ D ga a h χ J _ => PsiScalIn.main_local D ga a h χ J

end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU

theorem eq_one_of_pow_eq_one_of_localHom {W Ω : Type} [CommRing W] [IsLocalRing W] [Field Ω] (f : W →+* Ω)
    [IsLocalHom f] {N : ℕ} (hN : IsUnit (N : W)) {ζ : W} (h : ζ ^ N = 1) (hf : f ζ = 1) : ζ = 1 := by
  have hu : IsUnit (∑ i ∈ Finset.range N, ζ ^ i) := by
    refine isUnit_of_map_unit f _ ?_
    have := hN.map f

    simpa [map_sum, hf] using this
  have := geom_sum_mul ζ N
  rw [h, sub_self] at this
  exact sub_eq_zero.1 ((hu.mul_right_eq_zero).1 this)

theorem unit_eq_one_of_localHom {W Ω : Type} [CommRing W] [IsLocalRing W] [Field Ω] (f : W →+* Ω)
    [IsLocalHom f] {N : ℕ} (hN : IsUnit (N : W)) {ζ : Γ(Spec (CommRingCat.of W), ⊤)ˣ} (h : ζ ^ N = 1)
    (hf : Units.map (Spec.map (CommRingCat.ofHom f)).appTop.hom.toMonoidHom ζ = 1) : ζ = 1 := by
  have nat := congrArg (fun q => q.hom ζ.val) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
  have hf' : (Spec.map (CommRingCat.ofHom f)).appTop.hom ζ.val = 1 := congrArg Units.val hf
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, hf', map_one, CommRingCat.hom_ofHom] at nat
  have h1 := eq_one_of_pow_eq_one_of_localHom f hN
    (ζ := (Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom ζ.val)
    (by rw [← map_pow, ← Units.val_pow_eq_pow_val, h, Units.val_one, map_one]) nat.symm
  apply Units.ext
  apply (Scheme.ΓSpecIso (CommRingCat.of W)).commRingCatIsoToRingEquiv.injective
  rw [Units.val_one, map_one]
  exact h1

theorem IsCPMap.cubWeil_iff {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'}
    [GrpObj G'] [IsCommMonObj G'] {P : CP G} {P' : CP G'} {F : G'.left ⟶ G.left} {hw} {w}
    (h : IsCPMap P' P f F hw w) {N : ℕ} {T : Over S'} {x y : T ⟶ G'} (hx : x ^ N = 1) (hy : y ^ N = 1)
    (ζ : Γ(T.left, ⊤)ˣ) : CubWeil P'.c N x y ζ ↔ CubWeil P.c N (toBase hw x) (toBase hw y) ζ := by
  refine ⟨cubWeil_map _ _ _ _ _ _ _ _ _ _ h N T x y ζ, fun h' => ?_⟩
  obtain ⟨ξ, hξ, -⟩ := existsUnique_cubWeil P'.c hx hy
  have := (cubWeil_map _ _ _ _ _ _ _ _ _ _ h N T x y ξ hξ).unique h'
  exact this ▸ hξ

theorem TQ.Desc.cubWeil_one_iff {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {X : Type} [AddCommGroup X]
    {Q : TQ G X} {P : CP G} (D : Q.Desc P) {N : ℕ} {T : Over S} {x y : T ⟶ G} (hx : x ^ N = 1) (hy : y ^ N = 1) :
    CubWeil P.c N x y 1 ↔ CubWeil D.M.c N (x ≫ Q.q) (y ≫ Q.q) 1 := by
  rw [D.map.cubWeil_iff hx hy]
  let ρ : T ⟶ Over.mk (T.hom ≫ 𝟙 S) := Over.homMk (𝟙 T.left) (by simp)
  let ρ' : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have hw : Q.q.left ≫ Q.B.hom = G.hom ≫ 𝟙 S := by simp
  have e : ∀ a : T ⟶ G, ρ ≫ toBase hw a = a ≫ Q.q := fun a =>
    Over.OverMorphism.ext (Category.id_comp (a.left ≫ Q.q.left))
  have e' : ∀ a : T ⟶ G, ρ' ≫ (a ≫ Q.q) = toBase hw a := fun a =>
    Over.OverMorphism.ext (Category.id_comp (a.left ≫ Q.q.left))
  constructor
  · intro h
    have := h.comp ρ
    rwa [e, e, map_one] at this
  · intro h
    have := h.comp ρ'
    rwa [e', e', map_one] at this

theorem cubWeil_one_iff_closedFibre : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (W Ω : Type) [CommRing W] [IsLocalRing W] [Algebra V W] [Field Ω] (f' : W →+* Ω), IsLocalHom f' → ∀ (p : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (0 + 1)))) (N : ℕ), IsUnit (N : V) → ∀ (y y' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (x x' : Over.mk p ⟶ thickObj V (IsLocalRing.maximalIdeal V) 0 G), y ^ N = 1 → y' ^ N = 1 → x.left ≫ (fstG _ 0 G).left = (Spec.map (CommRingCat.ofHom f')) ≫ y.left → x'.left ≫ (fstG _ 0 G).left = (Spec.map (CommRingCat.ofHom f')) ≫ y'.left → (CubWeil s.P.c N y y' 1 ↔ CubWeil (t.l 0).D.M.c N (x ≫ (t.l 0).Q.q) (x' ≫ (t.l 0).Q.q) 1) := by
  intro V _ _ _ A G _ _ s t W Ω _ _ _ _ f' hf' p N hN y y' x x' hy hy' hx hx'
  let I := IsLocalRing.maximalIdeal V
  have hw : pullback.fst G.hom (thick V I 0) ≫ G.hom = (thickObj V I 0 G).hom ≫ thick V I 0 := pullback.condition
  obtain ⟨w, hl⟩ := (t.l 0).lev
  have hρ : Spec.map (CommRingCat.ofHom f') ≫ Spec.map (CommRingCat.ofHom (algebraMap V W)) =
      (Over.mk p).hom ≫ thick V I 0 := by
    have a := Over.w (toBase hw x)
    have b := Over.w y
    exact (congrArg (Spec.map (CommRingCat.ofHom f') ≫ ·) b).symm.trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ G.hom) hx).symm.trans a))
  let ρ : Over.mk ((Over.mk p).hom ≫ thick V I 0) ⟶ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) :=
    Over.homMk (Spec.map (CommRingCat.ofHom f')) hρ
  have e : ρ ≫ y = toBase hw x := Over.OverMorphism.ext hx.symm
  have e' : ρ ≫ y' = toBase hw x' := Over.OverMorphism.ext hx'.symm
  have inj : ∀ a b : Over.mk p ⟶ thickObj V I 0 G, toBase hw a = toBase hw b → a = b := fun a b h =>
    Over.OverMorphism.ext (pullback.hom_ext (congrArg (fun q => q.left) h) ((Over.w a).trans (Over.w b).symm))
  have tor : ∀ (a : Over.mk p ⟶ thickObj V I 0 G) (b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G),
      b ^ N = 1 → ρ ≫ b = toBase hw a → a ^ N = 1 := fun a b hb h => by
    refine inj _ _ ((map_pow (toBaseHom hl.mul _) a N).trans (Eq.trans ?_ (map_one (toBaseHom hl.mul _)).symm))
    exact (congrArg (· ^ N) h.symm).trans (by rw [← MonObj.comp_pow, hb, MonObj.comp_one])
  have hxN := tor x y hy e
  have hxN' := tor x' y' hy' e'
  refine Iff.trans ?_ ((t.l 0).D.cubWeil_one_iff hxN hxN')
  refine Iff.trans ?_ (hl.cubWeil_iff hxN hxN' 1).symm
  constructor
  · intro h
    have := h.comp ρ
    rw [e, e', map_one] at this
    exact this
  · intro h
    obtain ⟨ζ, hζ, -⟩ := existsUnique_cubWeil s.P.c hy hy'
    have c := hζ.comp ρ
    rw [e, e'] at c
    have hNW : IsUnit (N : W) := by simpa using hN.map (algebraMap V W)
    have : ζ = 1 := unit_eq_one_of_localHom f' hNW hζ.pow_eq_one (c.unique h)
    exact this ▸ hζ

end GlobalTheory.UU
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU.ImagePairing

theorem eq_map_of_isCPMap {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'}
    [GrpObj G'] [IsCommMonObj G'] {P : CP G} {P' : CP G'} {F : G'.left ⟶ G.left} {hw} {w}
    (h : IsCPMap P' P f F hw w) {N : ℕ} {T' : Over S'} {T : Over S} (r : T'.left ⟶ T.left)
    (hr : r ≫ T.hom = T'.hom ≫ f) {x' y' : T' ⟶ G'} {x y : T ⟶ G} (hx : x'.left ≫ F = r ≫ x.left)
    (hy : y'.left ≫ F = r ≫ y.left) {ζ' ζ} (h' : CubWeil P'.c N x' y' ζ') (h₀ : CubWeil P.c N x y ζ) :
    ζ' = Units.map r.appTop.hom.toMonoidHom ζ := by
  let ρ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk r hr
  have a := cubWeil_map S S' f G G' P P' F hw w h N T' x' y' ζ' h'
  have ex : toBase hw x' = ρ ≫ x := Over.OverMorphism.ext hx
  have ey : toBase hw y' = ρ ≫ y := Over.OverMorphism.ext hy
  rw [ex, ey] at a
  exact a.unique (h₀.comp ρ)

theorem pow_eq_one_of_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} [GrpObj G] {N : ℕ} {T' : Over S'}
    {T : Over S} (r : T'.left ⟶ T.left) (hr : r ≫ T.hom = T'.hom ≫ f) {x' : T' ⟶ (Over.pullback f).obj G}
    {x : T ⟶ G} (hx : x'.left ≫ pullback.fst G.hom f = r ≫ x.left) (h : x ^ N = 1) : x' ^ N = 1 := by
  let ρ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk r hr
  let β : (T' ⟶ (Over.pullback f).obj G) →* (Over.mk (T'.hom ≫ f) ⟶ G) :=
    MonoidHom.mk' (toBase (A := G) (A' := (Over.pullback f).obj G) (g := pullback.fst G.hom f) pullback.condition)
      (toBase_mul_pullback G f T')
  have ex : β x' = ρ ≫ x := Over.OverMorphism.ext hx
  have e : β (x' ^ N) = β 1 := by rw [map_pow, map_one, ex, ← MonObj.comp_pow, h, MonObj.comp_one]
  refine Over.OverMorphism.ext (pullback.hom_ext (congrArg (fun q => q.left) e) ?_)
  exact (Over.w (x' ^ N)).trans (Over.w (1 : T' ⟶ (Over.pullback f).obj G)).symm

theorem fn_eq_of_thick {R : Type} [CommRing R] (I : Ideal R) [IsHausdorff I R]
    (a b : Γ(Spec (CommRingCat.of R), ⊤))
    (h : ∀ e, (thick R I e).appTop.hom a = (thick R I e).appTop.hom b) : a = b := by
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
  have key : ∀ (e : ℕ) (c : Γ(Spec (CommRingCat.of R), ⊤)),
      Ideal.Quotient.mk (I ^ (e + 1)) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c) =
        (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I ^ (e + 1)))).hom.hom ((thick R I e).appTop.hom c) := fun e c =>
    (congrArg (fun q => q.hom c)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))))).symm
  have := IsHausdorff.StrictMono.funext' I (a := fun n => n + 1) (strictMono_id.add_const 1)
    (f := fun _ : Unit => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a)
    (g := fun _ : Unit => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom b)
    (fun n _ => (key n a).trans ((congrArg _ (h n)).trans (key n b).symm))
  exact congrFun this ()

theorem exists_thick_hom {V W : Type} [CommRing V] [CommRing W] [Algebra V W] (I : Ideal V) (e : ℕ) :
    ∃ φ : Spec (CommRingCat.of (W ⧸ (I.map (algebraMap V W)) ^ (e + 1))) ⟶ Spec (CommRingCat.of (V ⧸ I ^ (e + 1))),
      thick W (I.map (algebraMap V W)) e ≫ Spec.map (CommRingCat.ofHom (algebraMap V W)) = φ ≫ thick V I e := by
  refine ⟨Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ (algebraMap V W) ?_)), ?_⟩
  · rw [← Ideal.map_pow]; exact Ideal.le_comap_map
  · simp only [thick, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]

theorem cubWeil_image : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∀ (N : ℕ) (x x' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (b b' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B) (ζ), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x').left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b').left) → b ^ N = 1 → b' ^ N = 1 → CubWeil s.P.c N x x' ζ → CubWeil a.M.c N b b' ζ := by
  intro V _ _ _ A G _ _ s t a W _ _ _ hW _ N x x' b b' ζ hx hx' hb hb' h
  obtain ⟨ξ, hξ, -⟩ := existsUnique_cubWeil a.M.c hb hb'
  suffices e : ζ = ξ from e ▸ hξ
  refine Units.ext (fn_eq_of_thick ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) _ _ fun e => ?_)
  obtain ⟨φ, hφ⟩ := exists_thick_hom (W := W) (IsLocalRing.maximalIdeal V) e
  let r := thick W ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) e
  have lifts : ∀ y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G,
      ∃ ye : Over.mk φ ⟶ thickObj V (IsLocalRing.maximalIdeal V) e G,
        ye.left ≫ pullback.fst G.hom (thick V _ e) = r ≫ y.left := fun y =>
    ⟨Over.homMk (pullback.lift (r ≫ y.left) φ ((Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (Over.w y)).trans hφ)))
      (pullback.lift_snd _ _ _), pullback.lift_fst _ _ _⟩
  obtain ⟨y, hy⟩ := lifts x
  obtain ⟨y', hy'⟩ := lifts x'
  obtain ⟨θ, hθ, -⟩ := existsUnique_cubWeil (t.l e).Pe.c
    (pow_eq_one_of_pullback (T' := Over.mk φ) (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))))
      _ r hφ hy h.1)
    (pow_eq_one_of_pullback (T' := Over.mk φ) (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))))
      _ r hφ hy' h.2.1)
  obtain ⟨w, hw⟩ := (t.l e).lev
  obtain ⟨hp, v, hv⟩ := a.b_pb e
  have e₁ := eq_map_of_isCPMap hw (T' := Over.mk φ)
    (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))) r hφ hy hy' hθ h
  obtain ⟨u, -, hu⟩ := hv.exists_comp (t.l e).D.map (by
    rw [Category.assoc, hp.1.w, ← Category.assoc, Over.w, Category.id_comp])
  have e₂ := eq_map_of_isCPMap hu (T' := Over.mk φ)
    (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))) r
    (hφ.trans (congrArg (φ ≫ ·) (Category.id_comp _).symm)) (hx e _ r y.left hy) (hx' e _ r y'.left hy') hθ hξ
  exact congrArg Units.val (e₁.symm.trans e₂)

end GlobalTheory.UU.ImagePairing
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU

theorem card_and_nondeg_of_pullback (hL : Laws) {S S' : Scheme.{0}} [IsLocallyNoetherian S'] (f : S' ⟶ S)
    (A : PolAV S') {G : Over S} [GrpObj G] [IsCommMonObj G] (P : CP G) (φ : A.A.left ⟶ G.left)
    (hφ : IsPullback φ A.A.hom G.hom f)
    (mul : ∀ (T : Over S') (x y : T ⟶ A.A), toBase hφ.w (x * y) = toBase hφ.w x * toBase hφ.w y)
    (hw : LBIso A.L (P.L.L.pull φ)) {F : Type} [Field F] [IsAlgClosed F] (q : Spec (CommRingCat.of F) ⟶ S')
    {N : ℕ} (h1 : 1 ≤ N) (hN : (N : F) ≠ 0) :
    Nat.card {x : Over.mk (q ≫ f) ⟶ G // x ^ N = 1} = N ^ (2 * A.g) ∧
      ∀ x : Over.mk (q ≫ f) ⟶ G, x ^ N = 1 →
        (∀ y : Over.mk (q ≫ f) ⟶ G, y ^ N = 1 → CubWeil P.c N x y 1) → x = 1 := by
  haveI := A.isAb.comm
  obtain ⟨w, hg⟩ := hw
  obtain ⟨rig, hr, c, s, h₁, h₂, h₃, hm⟩ := exists_isCPMap P mul A.L A.isLB w hg
  let β : (Over.mk q ⟶ A.A) →* (Over.mk (q ≫ f) ⟶ G) := toBaseHom mul (Over.mk q)
  have hβ : ∀ y, (β y).left = y.left ≫ φ := fun y => rfl
  have inj : Function.Injective β := fun a b e => Over.OverMorphism.ext (hφ.hom_ext
    ((hβ a).symm.trans ((congrArg CommaMorphism.left e).trans (hβ b))) ((Over.w a).trans (Over.w b).symm))
  have surj : Function.Surjective β := fun x =>
    ⟨Over.homMk (hφ.lift x.left q (Over.w x)) (hφ.lift_snd _ _ _),
      Over.OverMorphism.ext ((hβ _).trans (hφ.lift_fst _ _ _))⟩
  have hp : ∀ y, y ^ N = 1 ↔ β y ^ N = 1 := fun y => by
    rw [← map_pow, ← map_one β, inj.eq_iff]
  refine ⟨?_, fun x hx h => ?_⟩
  · rw [← (hL.mulN S' A N h1).2.2.2.2 F q hN]
    exact (Nat.card_congr ((Equiv.ofBijective β ⟨inj, surj⟩).subtypeEquiv hp)).symm
  · obtain ⟨x, rfl⟩ := surj x
    have hx' := (hp x).2 hx
    rw [GlobalTheory.ThetaRep.eq_one_of_weilIs hL A q hN x hx' fun y hy => ?_, map_one]
    obtain ⟨ζ, hζ, -⟩ := existsUnique_cubWeil c hx' hy
    have e := (cubWeil_map _ _ f G A.A P ⟨_, c, s, h₁, h₂, h₃⟩ φ _ w hm N (Over.mk q) x y ζ hζ).unique (h _ ((hp y).1 hy))
    exact (cubWeil_iff_weilIs hL.globalFns A.isAb hx' hy 1).1 (e ▸ hζ)

theorem generic_card_and_nondeg : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (N : ℕ), 1 ≤ N → Nat.card {x : TF (R := V) F ⟶ G // x ^ N = 1} = N ^ (2 * A.g) ∧ ∀ x : TF (R := V) F ⟶ G, x ^ N = 1 → (∀ y : TF (R := V) F ⟶ G, y ^ N = 1 → CubWeil s.P.c N x y 1) → x = 1 := by
  intro hL V _ _ _ A G _ _ s F _ _ _ N h1
  haveI := s.gen_hom
  haveI : CharZero V := s.cdvr.2.2
  haveI : CharZero (FractionRing V) := charZero_of_injective_ringHom (IsFractionRing.injective V (FractionRing V))
  haveI : CharZero F := charZero_of_injective_ringHom (algebraMap (FractionRing V) F).injective
  let φ : A.A.left ⟶ G.left := s.gen.inv.left ≫ pullback.fst G.hom (jK V)
  haveI : IsIso s.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map s.gen.inv))
  have hφ : IsPullback φ A.A.hom G.hom (jK V) := by
    have a : IsPullback s.gen.inv.left A.A.hom (pullback.snd G.hom (jK V)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Over.w s.gen.inv).trans (Category.comp_id _).symm⟩
    simpa using a.paste_horiz (IsPullback.of_hasPullback G.hom (jK V))
  refine card_and_nondeg_of_pullback hL (jK V) A s.P φ hφ (fun T x y => ?_) ?_ (jFK F) h1
    (Nat.cast_ne_zero.2 (by omega))
  · have e : ∀ a : T ⟶ A.A, toBase hφ.w a = toBase (A := G) (A' := (Over.pullback (jK V)).obj G)
        (g := pullback.fst G.hom (jK V)) pullback.condition (a ≫ s.gen.inv) := fun a =>
      Over.OverMorphism.ext (Category.assoc _ _ _).symm
    rw [e, e, e, MonObj.mul_comp, toBase_mul_pullback]
  · exact LBIso.chartPull (chartPullSec A.L s.gen.hom.left s.gen.inv.left
      (congrArg CommaMorphism.left s.gen.inv_hom_id)) (chartPullSame s.P.L.L _ _ _ _ fun _ => rfl) ⟨s.wA, s.wA_gen⟩

end GlobalTheory.UU
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU

section

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G B T : Over S} {G' B' : Over S'} [GrpObj G] [GrpObj B] [GrpObj G']
  [GrpObj B'] {φ : G'.left ⟶ G.left} {β : B'.left ⟶ B.left}

theorem exists_imageHom (hG : IsGrpPullback G' G f φ) (hB : IsGrpPullback B' B f β) (q : G' ⟶ B') [IsMonHom q]
    {Z : Scheme.{0}} (r : Z ⟶ T.left) (xe : Z ⟶ G'.left) (x₀ : T ⟶ G) (h₀ : xe ≫ φ = r ≫ x₀.left) :
    ∃ (Y : Over S) (R : Y ⟶ T) (Φ : (T ⟶ G) → (Y ⟶ B)), Φ 1 = 1 ∧ (∀ x y, Φ (x * y) = Φ x * Φ y) ∧
      (∀ x, Φ x⁻¹ = (Φ x)⁻¹) ∧
      (∀ x b, (∀ ye : Z ⟶ G'.left, ye ≫ φ = r ≫ x.left → ye ≫ q.left ≫ β = r ≫ b.left) → Φ x = R ≫ b) ∧
      ∀ b, Φ x₀ = R ≫ b → xe ≫ q.left ≫ β = r ≫ b.left := by
  have hc : r ≫ T.hom = (xe ≫ G'.hom) ≫ f := by
    rw [Category.assoc, ← hG.1.w, reassoc_of% h₀, Over.w]
  obtain ⟨eG, heG⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hG _ _ hc
  obtain ⟨eB, heB⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hB _ _ hc
  let R : Over.mk (r ≫ T.hom) ⟶ T := Over.homMk r rfl
  refine ⟨_, R, fun x => eB (eG.symm (R ≫ x) ≫ q), ?_, fun x y => ?_, fun x => ?_, fun x b h => ?_,
    fun b h => ?_⟩
  · simp only [MonObj.comp_one, map_one, MonObj.one_comp]
  · simp only [MonObj.comp_mul, map_mul, MonObj.mul_comp]
  · simp only [GrpObj.comp_inv, map_inv, GrpObj.inv_comp]
  · apply Over.OverMorphism.ext
    refine (heB _).trans ((Category.assoc _ _ _).trans (h _ ?_))
    refine (heG _).symm.trans ?_
    rw [MulEquiv.apply_symm_apply]
    rfl
  · let xe' : Over.mk (xe ≫ G'.hom) ⟶ G' := Over.homMk xe rfl
    have h₁ : eG xe' = R ≫ x₀ := Over.OverMorphism.ext ((heG _).trans h₀)
    have h₂ : eB (xe' ≫ q) = R ≫ b := by
      rw [← h]
      beta_reduce
      rw [← h₁, MulEquiv.symm_apply_apply]
    exact (Category.assoc _ _ _).symm.trans ((heB (xe' ≫ q)).symm.trans (congrArg (fun z => z.left) h₂))

end

theorem image_one_mul_inv : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [Algebra V W] (x x' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (b b' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ ((1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G)).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ ((1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B)).left) ∧ ((∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x').left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b').left) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x * x').left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b * b').left) ∧ (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x⁻¹).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b⁻¹).left)) := by
  intro V _ _ _ A G _ _ s t a W _ _ x x' b b'
  have hG := fun e => isGrpPullback_pullback G (thick V (IsLocalRing.maximalIdeal V) e)
  have hB := fun e => (a.b_pb e).1
  have hq := fun e => (t.l e).Q.q_hom
  refine ⟨fun e Z r xe h => ?_, fun h₁ h₂ => ⟨fun e Z r xe h => ?_, fun e Z r xe h => ?_⟩⟩
  · obtain ⟨Y, R, Φ, e₁, -, -, -, k⟩ := exists_imageHom (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))) (hG e)
      (hB e) (t.l e).Q.q r xe _ h
    exact k 1 (by rw [e₁, MonObj.comp_one])
  · obtain ⟨Y, R, Φ, -, e₂, -, l, k⟩ := exists_imageHom (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))) (hG e)
      (hB e) (t.l e).Q.q r xe _ h
    exact k _ (by rw [e₂, l x b (h₁ e Z r), l x' b' (h₂ e Z r), MonObj.comp_mul])
  · obtain ⟨Y, R, Φ, -, -, e₃, l, k⟩ := exists_imageHom (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))) (hG e)
      (hB e) (t.l e).Q.q r xe _ h
    exact k _ (by rw [e₃, l x b (h₁ e Z r), GrpObj.comp_inv])

end GlobalTheory.UU
end
