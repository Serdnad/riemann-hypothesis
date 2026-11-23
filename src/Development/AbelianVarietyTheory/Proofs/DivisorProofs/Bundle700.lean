module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle599
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle612
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle652
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle384
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle562
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle666
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle629
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.existsUnique_levGrp_of_isEtLevOver : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (l l' : D.La → (Over.mk x ⟶ o.A)), IsEtLevOver o w0 r l → IsEtLevOver o w0 r l' → ∃! g : LevGrp D w0 r, ∀ y, l (levAct g y) = l' y := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.etLev_rel_existsUnique) | (exact GlobalTheory.UPel.HT.EtLev.etLev_rel_existsUnique) | (intros; apply GlobalTheory.UPel.HT.EtLev.etLev_rel_existsUnique  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.etale_level_base_change : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (T T' : Over S) (l : D.La → (T ⟶ o.A)) (f : T' ⟶ T), IsEtLevOver o w0 r l → IsEtLevOver o w0 r (fun y => f ≫ l y) := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.isEtLevOver_pull) | (exact GlobalTheory.UPel.HT.EtLev.isEtLevOver_pull) | (intros; apply GlobalTheory.UPel.HT.EtLev.isEtLevOver_pull  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.etale_level_group_action : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (T : Over S) (l : D.La → (T ⟶ o.A)) (g : LevGrp D w0 r), IsEtLevOver o w0 r l → IsEtLevOver o w0 r (fun y => l (levAct g y)) := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.isEtLevOver_levAct) | (exact GlobalTheory.UPel.HT.EtLev.isEtLevOver_levAct) | (intros; apply GlobalTheory.UPel.HT.EtLev.isEtLevOver_levAct <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.isEtLev_iff_isEtLevOver' : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S T : Scheme.{0}) (s : S ⟶ Sp R) (t : T ⟶ S) (s₁ : T ⟶ Sp R) (o : Obj b N s) (o₁ : Obj b N s₁) (m : ObjMap o₁ o t) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (l : D.La → (𝟙_ (Over T) ⟶ o₁.A)), IsEtLev o₁ w0 r l ↔ IsEtLevOver o w0 r (T := Over.mk t) (fun y => ptOf m (l y)) := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.isEtLev_iff_isEtLevOver) | (exact GlobalTheory.UPel.HT.EtLev.isEtLev_iff_isEtLevOver) | (intros; apply GlobalTheory.UPel.HT.EtLev.isEtLev_iff_isEtLevOver  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.EtC.MVExact
open GlobalTheory.EtC.FreeMonoEpi

variable {R : Type} [CommRing R]

theorem sec_map_add {F G : Shv R} (φ ψ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ + ψ) x = Sec.map φ x + Sec.map ψ x := rfl

theorem sec_map_neg {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (-φ) x = -Sec.map φ x := rfl

theorem sec_map_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem sec_biprod_ext {M N : Shv R} {U : Scheme.{0}} (x y : Sec (M ⊞ N) U)
    (h1 : Sec.map biprod.fst x = Sec.map biprod.fst y) (h2 : Sec.map biprod.snd x = Sec.map biprod.snd y) : x = y := by
  have e : ∀ z : Sec (M ⊞ N) U, z = Sec.map (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) z := fun z => by
    rw [biprod.total]; rfl
  rw [e x, e y, sec_map_add, sec_map_add, sec_map_comp, sec_map_comp, sec_map_comp, sec_map_comp, h1, h2]

theorem gsum_add (P : PSh) (V : Scheme.{0}) (a b : P.obj (op V) →₀ ULift.{1} R) :
    gsum R P V (a + b) = gsum R P V a + gsum R P V b :=
  Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)

theorem gsum_neg (P : PSh) (V : Scheme.{0}) (a : P.obj (op V) →₀ ULift.{1} R) :
    gsum R P V (-a) = -gsum R P V a := by
  rw [gsum, Finsupp.sum_neg_index (h := fun x r => r • freeGen R P V x) (fun _ => zero_smul _ _)]
  simp only [neg_smul]
  rw [Finsupp.sum, Finset.sum_neg_distrib]; rfl

theorem md_comp {M : Type 1} [AddCommMonoid M] (X : Scheme.{0}) {W' W V : Scheme.{0}} (k'' : W' ⟶ W) (k' : W ⟶ V)
    (c : (V ⟶ X) →₀ M) :
    Finsupp.mapDomain (fun x : W ⟶ X => k'' ≫ x) (Finsupp.mapDomain ((yoneda.obj X).map k'.op) c) =
      Finsupp.mapDomain ((yoneda.obj X).map (k'' ≫ k').op) c := by
  rw [← Finsupp.mapDomain_comp]
  congr 1

theorem exact_abstract (R : Type) [CommRing R] {X₁ X₂ X₃ X₄ : Scheme.{0}} (u : X₁ ⟶ X₂) (v : X₁ ⟶ X₃) (c : X₂ ⟶ X₄)
    (d : X₃ ⟶ X₄) (G : ∀ V : Scheme.{0}, (V ⟶ X₄) → Prop) (hsq : u ≫ c = v ≫ d) [Mono c]
    (hc : ∀ V (x : V ⟶ X₂), G V (x ≫ c)) (hd : ∀ V (y : V ⟶ X₃), G V (y ≫ d) → ∃ x, x ≫ v = y)
    (hp : ∀ T (y y' : T ⟶ X₃), y ≫ d = y' ≫ d → Loc T fun V k => k ≫ y = k ≫ y' ∨ G V (k ≫ y ≫ d))
    (w : biprod.lift ((free R).map (yoneda.map u)) (-(free R).map (yoneda.map v)) ≫
      biprod.desc ((free R).map (yoneda.map c)) ((free R).map (yoneda.map d)) = 0) :
    (ShortComplex.mk _ _ w).Exact := by
  classical
  rw [GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally]
  intro T b hb
  have h2 := (GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R (yoneda.obj X₂) T).1 (Sec.map biprod.fst b)
  have h3 := (GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R (yoneda.obj X₃) T).1 (Sec.map biprod.snd b)
  apply FreeMonoEpi.loc_trans
  refine FreeMonoEpi.loc_mono (GlobalTheory.EtC.loc_and T _ _ h2 h3) ?_
  rintro V k ⟨⟨c2, hc2⟩, ⟨c3, hc3⟩⟩
  change Sec.res k (Sec.map biprod.fst b) = gsum R _ V c2 at hc2
  change Sec.res k (Sec.map biprod.snd b) = gsum R _ V c3 at hc3
  have key : gsum R (yoneda.obj X₄) V (Finsupp.mapDomain ((yoneda.map c).app (op V)) c2 +
      Finsupp.mapDomain ((yoneda.map d).app (op V)) c3) = 0 := by
    have e0 : Sec.res k (Sec.map (biprod.desc ((free R).map (yoneda.map c)) ((free R).map (yoneda.map d))) b) = 0 := by
      have : Sec.map (biprod.desc ((free R).map (yoneda.map c)) ((free R).map (yoneda.map d))) b = 0 := hb
      rw [this]; exact map_zero _
    rw [gsum_add, ← map_gsum, ← map_gsum, ← hc2, ← hc3, ← map_res, ← map_res, ← sec_map_comp, ← sec_map_comp,
      ← sec_map_add, ← biprod.desc_eq, map_res, e0]
  apply FreeMonoEpi.loc_trans
  refine FreeMonoEpi.loc_mono ((GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R (yoneda.obj X₄) V).2 _ key) ?_
  intro W k' hk'
  set c2' := Finsupp.mapDomain ((yoneda.obj X₂).map k'.op) c2 with hc2'
  set c3' := Finsupp.mapDomain ((yoneda.obj X₃).map k'.op) c3 with hc3'
  have rel : Finsupp.mapDomain (fun x : W ⟶ X₂ => x ≫ c) c2' + Finsupp.mapDomain (fun y : W ⟶ X₃ => y ≫ d) c3' = 0 := by
    rw [← hk', Finsupp.mapDomain_add, hc2', hc3', ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp,
      ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    congr 2 <;> (funext x; simp)
  have hl : Loc W fun W' k'' => ∀ i : c3'.support × c3'.support, i.1.1 ≫ d = i.2.1 ≫ d →
      k'' ≫ i.1.1 = k'' ≫ i.2.1 ∨ G W' (k'' ≫ i.1.1 ≫ d) :=
    FreeMonoEpi.loc_fin _ fun i => by
      by_cases h : i.1.1 ≫ d = i.2.1 ≫ d
      · exact FreeMonoEpi.loc_mono (hp W _ _ h) fun _ _ e _ => e
      · exact FreeMonoEpi.loc_all fun _ _ e => absurd e h
  refine FreeMonoEpi.loc_mono hl ?_
  intro W' k'' hk''
  obtain ⟨a, ha1, ha2⟩ := GlobalTheory.T.mapDomain_relation_lift_commuting_square (ULift.{1} R) (W ⟶ X₂) (W ⟶ X₃) (W ⟶ X₄) (W' ⟶ X₁) (W' ⟶ X₂) (W' ⟶ X₃) (W' ⟶ X₄)
    (· ≫ c) (· ≫ d) (· ≫ u) (· ≫ v) (· ≫ c) (· ≫ d) (k'' ≫ ·) (k'' ≫ ·) (k'' ≫ ·) (G W')
    (fun x => by simp) (fun y => by simp) (fun x => by simp [hsq]) (fun x y h => (cancel_mono c).1 h) (hc W') (hd W')
    c2' c3' rel (fun y hy y' hy' h => by
      rcases hk'' (⟨y, hy⟩, ⟨y', hy'⟩) h with e | e
      · exact Or.inl e
      · exact Or.inr (by simpa using e))
  refine ⟨gsum R (yoneda.obj X₁) W' a, ?_⟩
  apply sec_biprod_ext
  · rw [← sec_map_comp, biprod.lift_fst, map_gsum, map_res, res_comp, hc2, res_gsum']
    congr 1
    change Finsupp.mapDomain (fun x : W' ⟶ X₁ => x ≫ u) a = _
    rw [ha1, hc2', md_comp]
  · rw [← sec_map_comp, biprod.lift_snd, sec_map_neg, map_gsum, map_res, res_comp, hc3, res_gsum']
    have ha2' : Finsupp.mapDomain ((yoneda.map v).app (op W')) a =
        -Finsupp.mapDomain ((yoneda.obj X₃).map (k'' ≫ k').op) c3 := by
      refine ha2.trans ?_
      rw [hc3', md_comp]
    rw [ha2', gsum_neg, neg_neg]

theorem rho_comp {B C : CommRingCat.{0}} (h : B ⟶ C) {V : Scheme.{0}} (y : V ⟶ Spec C) :
    (Scheme.ΓSpecIso B).inv ≫ (y ≫ Spec.map h).appTop = h ≫ (Scheme.ΓSpecIso C).inv ≫ y.appTop := by
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

theorem rho_toSpec {B : CommRingCat.{0}} {V : Scheme.{0}} (φ : B ⟶ Γ(V, ⊤)) :
    (Scheme.ΓSpecIso B).inv ≫ (V.toSpecΓ ≫ Spec.map φ).appTop = φ := by
  rw [rho_comp, Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]

theorem eq_toSpec {B : Type} [CommRing B] {V : Scheme.{0}} (y : V ⟶ Spec (CommRingCat.of B)) :
    y = V.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ y.appTop) :=
  ext_to_Spec (by simp only [Scheme.Γ_map_op]; exact (rho_toSpec _).symm)

theorem unit_of_away {B : Type} [CommRing B] (g : B) {V : Scheme.{0}}
    (x : V ⟶ Spec (CommRingCat.of (Localization.Away g))) :
    IsUnit (((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
      (x ≫ Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g)))).appTop).hom g) := by
  rw [rho_comp, CommRingCat.hom_comp, RingHom.comp_apply]
  exact (IsLocalization.Away.algebraMap_isUnit g).map _

theorem lift_away {B : Type} [CommRing B] (g : B) {V : Scheme.{0}} (y : V ⟶ Spec (CommRingCat.of B))
    (hy : IsUnit (((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ y.appTop).hom g)) :
    ∃ x : V ⟶ Spec (CommRingCat.of (Localization.Away g)),
      x ≫ Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g))) = y := by
  let ψ := IsLocalization.Away.lift (S := Localization.Away g) g hy
  refine ⟨V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ : CommRingCat.of _ ⟶ Γ(V, ⊤)), ?_⟩
  rw [Category.assoc, ← Spec.map_comp, eq_toSpec y]
  congr 2
  ext b
  simp [ψ]

theorem mv_exact : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) → (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) → ∃ w, (ShortComplex.mk (biprod.lift ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f))))) (-(free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f)))))))) (biprod.desc ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))))) ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A')))))) w).Exact := by
  intro R _ A A' _ _ _ _ f h1 h2
  obtain ⟨e, u, he, hu⟩ := GlobalTheory.T.etale_tensor_diagonal_complement_over_basicOpen A A' f h1 h2
  have hsq : Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) =
      Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f)))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A A')) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    simp [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  have w : biprod.lift ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f))))) (-(free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f))))))) ≫ biprod.desc ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))))) ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A'))))) = 0 := by
    rw [biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
      ← Functor.map_comp, hsq, add_neg_cancel]
  refine ⟨w, exact_abstract R _ _ _ _
    (fun V z => IsUnit (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ z.appTop).hom f)) hsq
    (fun V x => unit_of_away f x) (fun V y hy => ?_) (fun T y y' h => GlobalTheory.T.locally_equal_or_unit A A' f e u he hu T y y' h) w⟩
  rw [rho_comp, CommRingCat.hom_comp, RingHom.comp_apply] at hy
  exact lift_away (algebraMap A A' f) y hy

end GlobalTheory.EtC.MVExact
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem _root_.GlobalTheory.T.isGenerator_isoBundle_of_matrix_relation : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (R : Type) [CommRing R] (A' B' : Over (Sp R)) (Φ' : A' ⟶ B') (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left) (c : Fin mA → Fin mB → Γ(Sp R, ⊤)) (u : ∀ p, Γ(A'.left, (isoLB (L := L) (M := M) k Φ' ψA ψB).U p)ˣ), GlobalTheory.HomFixUniv.Generates bA ψA A'.hom c → (∀ (j : Fin mB) (p : (Fin 1 → M.ι) × (Fin 1 → L.ι)),
      ((Φ'.left ≫ ψB).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        (u p).val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p) (by simp)).hom (c i j) *
          (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)) → (⟨u⟩ : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB)).IsGen := by
  first | (exact @GlobalTheory.HomFixUniv.isGen_of_matRel) | (exact GlobalTheory.HomFixUniv.isGen_of_matRel) | (intros; apply GlobalTheory.HomFixUniv.isGen_of_matRel  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem _root_.GlobalTheory.T.exists_zeroSection_value_in_powerFrame : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (k : ℕ) (eA : LB.Gen (L.pull (eSec A))) (s : LB.Sec (LPow A L (k : ℤ) (topS Rg))), L.IsLB → eA.IsGen → ∃ α : Γ(Sp Rg, ⊤), GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) s α := by
  first | (exact @GlobalTheory.HomFixUnivVals.vals) | (exact GlobalTheory.HomFixUnivVals.vals) | (intros; apply GlobalTheory.HomFixUnivVals.vals  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem _root_.GlobalTheory.T.homogeneousForm_vanishing_combination_chart_indep : ∀ (Rg : Type) [CommRing Rg] (A₀ T X : Scheme.{0}) (N : LB A₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (t : T ⟶ Sp Rg) (c : Fin mA → Fin mB → Γ(T, ⊤)) (d : ℕ) (F : MvPolynomial (Fin mB) Rg), F.IsHomogeneous d → ∀ (z : X) (q q' : N.ι), φ z ∈ N.U q → φ z ∈ N.U q' → (MvPolynomial.eval₂Hom (gc (p ≫ t) z) (comb a φ p c z q) F = 0 ↔ MvPolynomial.eval₂Hom (gc (p ≫ t) z) (comb a φ p c z q') F = 0) := by
  first | (exact @GlobalTheory.HomFixUniv.formVanish_chart_indep) | (exact GlobalTheory.HomFixUniv.formVanish_chart_indep) | (intros; apply GlobalTheory.HomFixUniv.formVanish_chart_indep  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem _root_.GlobalTheory.T.linearNormalisation_closed_subscheme : ∀ (Rg : Type) [CommRing Rg] (mA mB : ℕ) (α : Fin mA → Γ(Sp Rg, ⊤)) (β : Fin mB → Γ(Sp Rg, ⊤)), ∃ (Z : Scheme.{0}) (ιZ : Z ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), IsClosedImmersion ιZ ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), (GlobalTheory.HomFixUniv.Normal (g ≫ affπ Rg (mA * mB)) (matOf g) α β ↔ ∃ w : T ⟶ Z, w ≫ ιZ = g) := by
  first | (exact @GlobalTheory.HomFixUniv.normal_closed) | (exact GlobalTheory.HomFixUniv.normal_closed) | (intros; apply GlobalTheory.HomFixUniv.normal_closed  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem _root_.GlobalTheory.T.diagonalToUnitTensor_isPullback_isIso : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) (T X' : Scheme.{0}) (φ : X' ⟶ A.left) (p : X' ⟶ T) (t : T ⟶ Sp Rg), (IsPullback φ p A.hom t → IsPullback (φ ≫ GlobalTheory.HomFixUniv.θ A) p (GlobalTheory.HomFixUniv.fA A) t) ∧ GlobalTheory.HomFixUniv.θ A ≫ GlobalTheory.HomFixUniv.fA A = A.hom ∧ IsIso (GlobalTheory.HomFixUniv.θ A) := by
  first | (exact @GlobalTheory.HomFixUniv.θ_pullback) | (exact GlobalTheory.HomFixUniv.θ_pullback) | (intros; apply GlobalTheory.HomFixUniv.θ_pullback  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType

theorem _root_.GlobalTheory.T.trace_ringOfIntegers_action_sum_embeddings_eigenspace : ∀ (F : Type) [Field F] [NumberField F] (g : ℕ) (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (c : 𝓞 F), (φ c).trace = ∑ τ : F →+* ℂ, (Module.finrank ℂ (eigSp φ τ) : ℂ) * τ (c : F) := by
  first | (exact @GlobalTheory.UPel.HT.LieType.trace_eq_sum_finrank_eigSp) | (exact GlobalTheory.UPel.HT.LieType.trace_eq_sum_finrank_eigSp) | (intros; apply GlobalTheory.UPel.HT.LieType.trace_eq_sum_finrank_eigSp  <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.LevelSchwartz

theorem mem_schA_of_level : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (Φ : (Fin N → AF F) → ℂ),
    (∃ U : AddSubgroup (Fin N → AF F), IsOpen (U : Set (Fin N → AF F)) ∧ ∀ u ∈ U, inf u = 0 → ∀ x, Φ (x + u) = Φ x) →
    (∃ K : Set (Fin N → Af F), IsCompact K ∧ ∀ x, Φ x ≠ 0 → fin x ∈ K) →
    (∀ x, ∃ g : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ, ∀ t, g t = Φ (x + embR t)) →
    Φ ∈ GlobalTheory.WeilM.schA F (Fin N) := by
  intro F _ _ N Φ ⟨U, hUo, hU⟩ ⟨K, hK, hKs⟩ hS
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let ι : (Fin N → Af F) →+ (Fin N → AF F) :=
    { toFun := fun v i => pairA F 0 (v i)
      map_zero' := rfl
      map_add' := fun a b => by
        funext i
        show (((0 : Ainf F), a i + b i) : Ainf F × Af F) = ((0 : Ainf F), a i) + ((0 : Ainf F), b i)
        simp }
  have hιc : Continuous ι := continuous_pi fun i =>
    (show Continuous fun v : Fin N → Af F => (((0 : Ainf F), v i) : Ainf F × Af F) from
      continuous_const.prodMk (continuous_apply i))
  have hιinf : ∀ v, inf (ι v) = 0 := fun v => rfl
  have hfin : ∀ a t, fin (ι a + embR t) = a := fun a t => by
    funext i
    show (a i + 0 : Af F) = a i
    exact add_zero _
  have hdec : ∀ y : Fin N → AF F, y = ι (fin y) + embR (fun i => e (y i).1) := fun y => by
    funext i
    show (y i : Ainf F × Af F) = (((0 : Ainf F), (y i).2) : Ainf F × Af F) + ((e.symm (e (y i).1), (0 : Af F)))
    rw [RingEquiv.symm_apply_apply]
    refine Prod.ext ?_ ?_ <;> simp
  let W : AddSubgroup (Fin N → Af F) := U.comap ι
  have hWo : IsOpen (W : Set (Fin N → Af F)) := hUo.preimage hιc
  have hWcl : IsClosed (W : Set (Fin N → Af F)) := AddSubgroup.isClosed_of_isOpen W hWo
  have hinv : ∀ a b, -a + b ∈ W → ∀ z, Φ (ι b + z) = Φ (ι a + z) := by
    intro a b hab z
    rw [← hU (ι (-a + b)) hab (hιinf _) (ι a + z)]
    congr 1
    rw [map_add (f := _), map_neg]
    abel
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun a : Fin N → Af F => {b | -a + b ∈ W})
    (fun a => hWo.preimage (continuous_const.add continuous_id))
    (fun b _ => Set.mem_iUnion.2 ⟨b, show -b + b ∈ W by rw [neg_add_cancel]; exact W.zero_mem⟩)
  let T : Finset ((Fin N → Af F) ⧸ W) := t.image QuotientAddGroup.mk
  choose g hg using fun q : (Fin N → Af F) ⧸ W => hS (ι q.out)
  let ind : ((Fin N → Af F) ⧸ W) → (Fin N → Af F) → ℂ := fun q a =>
    if (QuotientAddGroup.mk a : (Fin N → Af F) ⧸ W) = q then 1 else 0
  have key : Φ = ∑ q ∈ T, GlobalTheory.WeilM.pureA F (g q) (ind q) := by
    funext y
    rw [Finset.sum_apply]
    show Φ y = ∑ q ∈ T, g q (fun i => e (y i).1) *
      (if (QuotientAddGroup.mk (fin y) : (Fin N → Af F) ⧸ W) = q then (1 : ℂ) else 0)
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hT
    · rw [hg]
      conv_lhs => rw [hdec y]
      exact hinv _ _ (QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)) _
    · by_contra hne
      obtain ⟨b, hb, hab⟩ := Set.mem_iUnion₂.1 (ht (hKs y hne))
      exact hT (Finset.mem_image.2 ⟨b, hb, QuotientAddGroup.eq.2 hab⟩)
  rw [key]
  refine Submodule.sum_mem _ fun q _ => ?_
  by_cases h0 : ∀ s, g q s = 0
  · have : GlobalTheory.WeilM.pureA F (g q) (ind q) = 0 := by
      funext y
      simp [GlobalTheory.WeilM.pureA, h0]
    rw [this]
    exact zero_mem _
  push_neg at h0
  obtain ⟨s0, hs0⟩ := h0
  refine Submodule.subset_span ⟨g q, ind q, ?_, rfl⟩
  let C : Set (Fin N → Af F) := {a | -q.out + a ∈ W}
  have hCcl : IsClosed C := hWcl.preimage (continuous_const.add continuous_id)
  have hCK : C ⊆ K := by
    intro a ha
    have h1 : Φ (ι a + embR s0) ≠ 0 := by
      rw [hinv _ _ ha, ← hg]
      exact hs0
    simpa [hfin] using hKs _ h1
  have hmk : IsLocallyConstant (fun a : Fin N → Af F => (a : (Fin N → Af F) ⧸ W)) :=
    (IsLocallyConstant.iff_exists_open _).2 fun x => ⟨{b | -b + x ∈ W},
      hWo.preimage (continuous_neg.add continuous_const), by simp, fun b hb => QuotientAddGroup.eq.2 hb⟩
  refine ⟨hmk.comp fun q' => if q' = q then (1 : ℂ) else 0, ?_⟩
  refine HasCompactSupport.intro' (hK.of_isClosed_subset hCcl hCK) hCcl fun x hx => ?_
  show (if (QuotientAddGroup.mk x : (Fin N → Af F) ⧸ W) = q then (1 : ℂ) else 0) = 0
  rw [if_neg]
  intro hq
  apply hx
  show -q.out + x ∈ W
  exact QuotientAddGroup.eq.1 (by rw [hq, QuotientAddGroup.out_eq'])

end GlobalTheory.LevelSchwartz

end
end
