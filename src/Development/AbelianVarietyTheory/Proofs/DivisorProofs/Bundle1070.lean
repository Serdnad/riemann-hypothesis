module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GtPtsVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DescDefect

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

theorem compat_gm {L : LB X} {φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ} (hC : DescCompat f L φ)
    {T : Scheme.{0}} (s : T ⟶ pullback f f) (t : T) (i i' j j' : L.ι)
    (hi : pullback.fst f f (s t) ∈ L.U i) (hi' : pullback.fst f f (s t) ∈ L.U i')
    (hj : pullback.snd f f (s t) ∈ L.U j) (hj' : pullback.snd f f (s t) ∈ L.U j') :
    gm s t _ (φ i' j') =
      gm (s ≫ pullback.fst f f) t _ (L.g i i') * gm s t _ (φ i j) * gm (s ≫ pullback.snd f f) t _ (L.g j' j) := by
  have l₁ : chart f L i j ⊓ chart f L i' j' ≤ pullback.fst f f ⁻¹ᵁ (L.U i ⊓ L.U i') :=
    fun z hz => ⟨hz.1.1, hz.2.1⟩
  have l₂ : chart f L i j ⊓ chart f L i' j' ≤ pullback.snd f f ⁻¹ᵁ (L.U j' ⊓ L.U j) :=
    fun z hz => ⟨hz.2.2, hz.1.2⟩
  have hO : res (inf_le_right : chart f L i j ⊓ chart f L i' j' ≤ _) (φ i' j') =
      res l₁ (pullU (pullback.fst f f) _ (L.g i i')) * res inf_le_left (φ i j) *
        res l₂ (pullU (pullback.snd f f) _ (L.g j' j)) := by
    apply unit_ext
    intro z hz
    rw [map_mul, map_mul, gm_res _ z _ hz, gm_res _ z _ hz, gm_res _ z _ hz, gm_res _ z _ hz,
      gm_pull (𝟙 _) (pullback.fst f f) z _ (l₁ hz) _, gm_pull (𝟙 _) (pullback.snd f f) z _ (l₂ hz) _,
      Category.id_comp, Category.id_comp]
    exact hC z i i' j j' hz.1.1 hz.2.1 hz.1.2 hz.2.2
  have hst : s t ∈ chart f L i j ⊓ chart f L i' j' := ⟨⟨hi, hj⟩, ⟨hi', hj'⟩⟩
  have e := congrArg (gm s t (chart f L i j ⊓ chart f L i' j')) hO
  rw [map_mul, map_mul, gm_res _ t _ hst, gm_res _ t _ hst, gm_res _ t _ hst, gm_res _ t _ hst,
    gm_pull s (pullback.fst f f) t _ (l₁ hst) _, gm_pull s (pullback.snd f f) t _ (l₂ hst) _] at e
  exact e

theorem defect_exists : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ),
    L.IsLB → DescCompat f L φ → ∃ D : Γ(Triple f, ⊤)ˣ, Defect f L φ D := by
  intro X Y f L φ hL hC
  set a := pullback.fst (pullback.snd f f) (pullback.fst f f) with ha
  set b := pullback.snd (pullback.snd f f) (pullback.fst f f) with hb
  have hab : a ≫ pullback.snd f f = b ≫ pullback.fst f f := pullback.condition
  have hca : pr13 f ≫ pullback.fst f f = a ≫ pullback.fst f f := pullback.lift_fst _ _ _
  have hcb : pr13 f ≫ pullback.snd f f = b ≫ pullback.snd f f := pullback.lift_snd _ _ _
  have pab : ∀ x, pullback.snd f f (a x) = pullback.fst f f (b x) := fun x => by
    have := congrArg (fun h : Triple f ⟶ X => h x) hab
    simpa only [Scheme.Hom.comp_apply] using this
  have pca : ∀ x, pullback.fst f f (pr13 f x) = pullback.fst f f (a x) := fun x => by
    have := congrArg (fun h : Triple f ⟶ X => h x) hca
    simpa only [Scheme.Hom.comp_apply] using this
  have pcb : ∀ x, pullback.snd f f (pr13 f x) = pullback.snd f f (b x) := fun x => by
    have := congrArg (fun h : Triple f ⟶ X => h x) hcb
    simpa only [Scheme.Hom.comp_apply] using this

  have K : ∀ (T : Scheme.{0}) (s : T ⟶ Triple f) (t : T) (i j k i' j' k' : L.ι),
      pullback.fst f f (a (s t)) ∈ L.U i → pullback.fst f f (a (s t)) ∈ L.U i' →
      pullback.snd f f (a (s t)) ∈ L.U j → pullback.snd f f (a (s t)) ∈ L.U j' →
      pullback.snd f f (b (s t)) ∈ L.U k → pullback.snd f f (b (s t)) ∈ L.U k' →
      gm (s ≫ a) t _ (φ i j) * gm (s ≫ b) t _ (φ j k) * (gm (s ≫ pr13 f) t _ (φ i k))⁻¹ =
        gm (s ≫ a) t _ (φ i' j') * gm (s ≫ b) t _ (φ j' k') * (gm (s ≫ pr13 f) t _ (φ i' k'))⁻¹ := by
    intro T s t i j k i' j' k' hi hi' hj hj' hk hk'
    have hjb : pullback.fst f f (b (s t)) ∈ L.U j := pab (s t) ▸ hj
    have hjb' : pullback.fst f f (b (s t)) ∈ L.U j' := pab (s t) ▸ hj'
    have hic : pullback.fst f f (pr13 f (s t)) ∈ L.U i := (pca (s t)).symm ▸ hi
    have hic' : pullback.fst f f (pr13 f (s t)) ∈ L.U i' := (pca (s t)).symm ▸ hi'
    have hkc : pullback.snd f f (pr13 f (s t)) ∈ L.U k := (pcb (s t)).symm ▸ hk
    have hkc' : pullback.snd f f (pr13 f (s t)) ∈ L.U k' := (pcb (s t)).symm ▸ hk'
    have E1 := compat_gm f hC (s ≫ a) t i i' j j' hi hi' hj hj'
    have E2 := compat_gm f hC (s ≫ b) t j j' k k' hjb hjb' hk hk'
    have E3 := compat_gm f hC (s ≫ pr13 f) t i i' k k' hic hic' hkc hkc'
    have hc := gm_cocycle hL (s ≫ b ≫ pullback.fst f f) t (i := j') (j := j) (k := j') hjb' hjb hjb'
    rw [gm_self hL _ t hjb'] at hc
    simp only [Category.assoc] at E1 E2 E3
    rw [hca, hcb] at E3
    rw [hab] at E1
    rw [E1, E2, E3]
    generalize gm (s ≫ b ≫ pullback.fst f f) t _ (L.g j' j) = G2 at hc ⊢
    generalize gm (s ≫ b ≫ pullback.fst f f) t _ (L.g j j') = G3 at hc ⊢
    have : G3 = G2⁻¹ := eq_inv_of_mul_eq_one_right hc
    subst this
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  let V : L.ι × L.ι × L.ι → (Triple f).Opens := fun p =>
    a ⁻¹ᵁ chart f L p.1 p.2.1 ⊓ b ⁻¹ᵁ chart f L p.2.1 p.2.2 ⊓ pr13 f ⁻¹ᵁ chart f L p.1 p.2.2
  have la : ∀ p, V p ≤ a ⁻¹ᵁ chart f L p.1 p.2.1 := fun p => inf_le_left.trans inf_le_left
  have lb : ∀ p, V p ≤ b ⁻¹ᵁ chart f L p.2.1 p.2.2 := fun p => inf_le_left.trans inf_le_right
  have lc : ∀ p, V p ≤ pr13 f ⁻¹ᵁ chart f L p.1 p.2.2 := fun p => inf_le_right
  have memV : ∀ (x : Triple f) (i j k : L.ι), pullback.fst f f (a x) ∈ L.U i → pullback.snd f f (a x) ∈ L.U j →
      pullback.snd f f (b x) ∈ L.U k → x ∈ V (i, j, k) := fun x i j k hi hj hk =>
    ⟨⟨⟨hi, hj⟩, ⟨(show pullback.fst f f (b x) ∈ L.U j from pab x ▸ hj), hk⟩⟩,
      ⟨(show pullback.fst f f (pr13 f x) ∈ L.U i from (pca x).symm ▸ hi),
        (show pullback.snd f f (pr13 f x) ∈ L.U k from (pcb x).symm ▸ hk)⟩⟩
  let u : ∀ p, Γ(Triple f, V p)ˣ := fun p =>
    res (la p) (pullU a _ (φ p.1 p.2.1)) * res (lb p) (pullU b _ (φ p.2.1 p.2.2)) *
      (res (lc p) (pullU (pr13 f) _ (φ p.1 p.2.2)))⁻¹
  have hu : ∀ (T : Scheme.{0}) (s : T ⟶ Triple f) (t : T) (p : L.ι × L.ι × L.ι), s t ∈ V p →
      gm s t (V p) (u p) = gm (s ≫ a) t _ (φ p.1 p.2.1) * gm (s ≫ b) t _ (φ p.2.1 p.2.2) *
        (gm (s ≫ pr13 f) t _ (φ p.1 p.2.2))⁻¹ := by
    intro T s t p hp
    simp only [u, map_mul, map_inv]
    rw [gm_res _ t _ hp, gm_res _ t _ hp, gm_res _ t _ hp, gm_pull s a t _ (la p hp) _,
      gm_pull s b t _ (lb p hp) _, gm_pull s (pr13 f) t _ (lc p hp) _]
  obtain ⟨D, hD⟩ := glue_unit ⊤ V (fun _ => le_top) (fun x _ => by
      obtain ⟨i, hi⟩ := exists_chart hL (pullback.fst f f (a x))
      obtain ⟨j, hj⟩ := exists_chart hL (pullback.snd f f (a x))
      obtain ⟨k, hk⟩ := exists_chart hL (pullback.snd f f (b x))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j, k), memV x i j k hi hj hk⟩) u (fun p p' x hx => by
      rw [hu _ (𝟙 _) x p hx.1, hu _ (𝟙 _) x p' hx.2]
      exact K _ (𝟙 _) x _ _ _ _ _ _ hx.1.1.1.1 hx.2.1.1.1 hx.1.1.1.2 hx.2.1.1.2 hx.1.1.2.2 hx.2.1.2.2)
  refine ⟨D, fun T r t i j k hi hj hk => ?_⟩
  have hm := memV (r t) i j k hi hj hk
  rw [← gm_res r t (fun _ _ => trivial : V (i, j, k) ≤ ⊤) hm D, hD (i, j, k), hu T r t (i, j, k) hm]
  exact inv_mul_cancel_right _ _

end GlobalTheory.DescDefect
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DescNorm.RigidW

theorem triple_ext {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g h : Z ⟶ Triple f)
    (h1 : g ≫ pullback.fst _ _ ≫ pullback.fst f f = h ≫ pullback.fst _ _ ≫ pullback.fst f f)
    (h2 : g ≫ pullback.fst _ _ ≫ pullback.snd f f = h ≫ pullback.fst _ _ ≫ pullback.snd f f)
    (h3 : g ≫ pullback.snd _ _ ≫ pullback.snd f f = h ≫ pullback.snd _ _ ≫ pullback.snd f f) : g = h := by
  have c := pullback.condition (f := pullback.snd f f) (g := pullback.fst f f)
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [Category.assoc] using h1
    · simpa only [Category.assoc] using h2
  · apply pullback.hom_ext
    · simp only [Category.assoc, ← c]
      simpa only [Category.assoc] using h2
    · simpa only [Category.assoc] using h3

theorem appTop_comp {X Y Z : Scheme.{0}} (g : X ⟶ Y) (h : Y ⟶ Z) (x : Γ(Z, ⊤)) :
    (g ≫ h).appTop.hom x = g.appTop.hom (h.appTop.hom x) := by
  rw [Scheme.Hom.comp_appTop]; rfl

section
variable {K : Type} [Field K] {A A' B : Over (Sp K)} [GrpObj B] (q : A ⟶ A')

theorem snd_hom : pullback.snd (q ▷ B).left (q ▷ B).left ≫ (A ⊗ B).hom =
    pullback.fst (q ▷ B).left (q ▷ B).left ≫ (A ⊗ B).hom := by
  rw [← Over.w (q ▷ B), pullback.condition_assoc]


variable (B) in
def W0 : Over (Sp K) :=
  Over.mk (pullback.fst _ _ ≫ pullback.fst (q ▷ B).left (q ▷ B).left ≫ (A ⊗ B).hom : Triple (q ▷ B).left ⟶ Sp K)

def p1 : W0 B q ⟶ A ⊗ B := Over.homMk (pullback.fst _ _ ≫ pullback.fst _ _) (by simp [W0])

def p2 : W0 B q ⟶ A ⊗ B := Over.homMk (pullback.fst _ _ ≫ pullback.snd _ _) (by
  simp only [W0, Over.mk_hom]; rw [Category.assoc, snd_hom])

def p3 : W0 B q ⟶ A ⊗ B := Over.homMk (pullback.snd _ _ ≫ pullback.snd _ _) (by
  simp only [W0, Over.mk_hom]; rw [Category.assoc, snd_hom, ← pullback.condition_assoc, snd_hom])

theorem rigidityTripleFibreProductFirstCoord_left : (p1 q).left = pullback.fst _ _ ≫ pullback.fst (q ▷ B).left (q ▷ B).left := rfl
theorem rigidityTripleFibreProductSecondCoord_left : (p2 q).left = pullback.fst _ _ ≫ pullback.snd (q ▷ B).left (q ▷ B).left := rfl
theorem rigidityTripleFibreProductThirdCoord_left : (p3 q).left = pullback.snd _ _ ≫ pullback.snd (q ▷ B).left (q ▷ B).left := rfl

theorem p12 : p1 q ≫ q ▷ B = p2 q ≫ q ▷ B := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, rigidityTripleFibreProductFirstCoord_left, rigidityTripleFibreProductSecondCoord_left]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)

theorem p23 : p2 q ≫ q ▷ B = p3 q ≫ q ▷ B := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, rigidityTripleFibreProductThirdCoord_left, rigidityTripleFibreProductSecondCoord_left]
  exact (congrArg (· ≫ _) pullback.condition).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm))

end
end GlobalTheory.DescNorm.RigidW

namespace GlobalTheory.DescNorm.RigidW
section
variable {K : Type} [Field K] {A A' B : Over (Sp K)} [GrpObj B] (q : A ⟶ A')

def beta : W0 B q ⟶ B := p1 q ≫ snd A B

theorem rigidityTripleSecondCoord_snd_eq_groupCoord : p2 q ≫ snd A B = beta q := by
  rw [beta, ← whiskerRight_snd q B, ← Category.assoc, ← Category.assoc, p12]

theorem rigidityTripleThirdCoord_snd_eq_groupCoord : p3 q ≫ snd A B = beta q := by
  rw [← rigidityTripleSecondCoord_snd_eq_groupCoord, ← whiskerRight_snd q B, ← Category.assoc, ← Category.assoc, p23]

def E (u : W0 B q ⟶ A ⊗ B) : B ⊗ W0 B q ⟶ A ⊗ B := lift (snd B (W0 B q) ≫ u ≫ fst A B) (fst B (W0 B q))

theorem E_eq {u v : W0 B q ⟶ A ⊗ B} (h : u ≫ q ▷ B = v ≫ q ▷ B) : E q u ≫ q ▷ B = E q v ≫ q ▷ B := by
  have h' : u ≫ fst A B ≫ q = v ≫ fst A B ≫ q := by
    have := congrArg (· ≫ fst A' B) h
    simpa using this
  apply CartesianMonoidalCategory.hom_ext
  · simp [E, h']
  · simp [E]

theorem E_left_eq {u v : W0 B q ⟶ A ⊗ B} (h : u ≫ q ▷ B = v ≫ q ▷ B) :
    (E q u).left ≫ (q ▷ B).left = (E q v).left ≫ (q ▷ B).left := by
  rw [← Over.comp_left, ← Over.comp_left, E_eq q h]

theorem lift_E (x : W0 B q ⟶ B) (u : W0 B q ⟶ A ⊗ B) : lift x (𝟙 _) ≫ E q u = lift (u ≫ fst A B) x := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [E]

def eL : (B ⊗ W0 B q).left ⟶ Triple (q ▷ B).left :=
  pullback.lift (pullback.lift (E q (p1 q)).left (E q (p2 q)).left (E_left_eq q (p12 q)))
    (pullback.lift (E q (p2 q)).left (E q (p3 q)).left (E_left_eq q (p23 q)))
    ((pullback.lift_snd _ _ _).trans (pullback.lift_fst _ _ _).symm)

theorem eL_1 : eL q ≫ pullback.fst _ _ ≫ pullback.fst (q ▷ B).left (q ▷ B).left = (E q (p1 q)).left := by
  rw [eL, ← Category.assoc, pullback.lift_fst, pullback.lift_fst]
theorem eL_2 : eL q ≫ pullback.fst _ _ ≫ pullback.snd (q ▷ B).left (q ▷ B).left = (E q (p2 q)).left := by
  rw [eL, ← Category.assoc, pullback.lift_fst, pullback.lift_snd]
theorem eL_3 : eL q ≫ pullback.snd _ _ ≫ pullback.snd (q ▷ B).left (q ▷ B).left = (E q (p3 q)).left := by
  rw [eL, ← Category.assoc, pullback.lift_snd, pullback.lift_snd]

theorem sec_beta : (lift (beta q) (𝟙 (W0 B q))).left ≫ eL q = 𝟙 _ := by
  apply triple_ext
  · rw [Category.assoc, eL_1, ← Over.comp_left, lift_E]
    refine (congrArg Over.Hom.left (?_ : lift (p1 q ≫ fst A B) (beta q) = p1 q)).trans
      ((rigidityTripleFibreProductFirstCoord_left q).trans (Category.id_comp _).symm)
    apply CartesianMonoidalCategory.hom_ext <;> simp [beta]
  · rw [Category.assoc, eL_2, ← Over.comp_left, lift_E]
    refine (congrArg Over.Hom.left (?_ : lift (p2 q ≫ fst A B) (beta q) = p2 q)).trans
      ((rigidityTripleFibreProductSecondCoord_left q).trans (Category.id_comp _).symm)
    apply CartesianMonoidalCategory.hom_ext <;> simp [rigidityTripleSecondCoord_snd_eq_groupCoord]
  · rw [Category.assoc, eL_3, ← Over.comp_left, lift_E]
    refine (congrArg Over.Hom.left (?_ : lift (p3 q ≫ fst A B) (beta q) = p3 q)).trans
      ((rigidityTripleFibreProductThirdCoord_left q).trans (Category.id_comp _).symm)
    apply CartesianMonoidalCategory.hom_ext <;> simp [rigidityTripleThirdCoord_snd_eq_groupCoord]

theorem lift_one (u : W0 B q ⟶ A ⊗ B) : lift (u ≫ fst A B) (1 : W0 B q ⟶ B) = u ≫ zb A B := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [zb]
  · simp [zb, MonObj.comp_one]

theorem sec_one : (lift (1 : W0 B q ⟶ B) (𝟙 (W0 B q))).left ≫ eL q = rhoW q := by
  apply triple_ext
  · rw [Category.assoc, eL_1, ← Over.comp_left, lift_E, lift_one, Over.comp_left, rigidityTripleFibreProductFirstCoord_left]
    exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (rhoZ_fst q).symm)).trans (rhoW_fst_assoc q _).symm
  · rw [Category.assoc, eL_2, ← Over.comp_left, lift_E, lift_one, Over.comp_left, rigidityTripleFibreProductSecondCoord_left]
    exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (rhoZ_snd q).symm)).trans (rhoW_fst_assoc q _).symm
  · rw [Category.assoc, eL_3, ← Over.comp_left, lift_E, lift_one, Over.comp_left, rigidityTripleFibreProductThirdCoord_left]
    exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (rhoZ_snd q).symm)).trans (rhoW_snd_assoc q _).symm

theorem rhoW_appTop (hB : IsAbelianScheme B) (D : Γ(Triple (q ▷ B).left, ⊤)) : (rhoW q).appTop.hom D = D := by
  have hs : Function.Surjective ((snd B (W0 B q)).left.appTop).hom :=
    surjective_app_of_isAbelianScheme GlobalTheory.SemiRigid.globalFns _ (Out.TLinPf.isAb_pullback (W0 B q).hom B hB) ⊤
  obtain ⟨F, hF⟩ := hs ((eL q).appTop.hom D)
  have hsnd : ∀ x : W0 B q ⟶ B, (lift x (𝟙 (W0 B q))).left ≫ (snd B (W0 B q)).left = 𝟙 _ := fun x => by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have key : ∀ x : W0 B q ⟶ B, ((lift x (𝟙 (W0 B q))).left ≫ eL q).appTop.hom D = F := by
    intro x
    calc ((lift x (𝟙 (W0 B q))).left ≫ eL q).appTop.hom D
        = (lift x (𝟙 (W0 B q))).left.appTop.hom ((eL q).appTop.hom D) := appTop_comp _ _ _
      _ = (lift x (𝟙 (W0 B q))).left.appTop.hom ((snd B (W0 B q)).left.appTop.hom F) := by rw [hF]
      _ = ((lift x (𝟙 (W0 B q))).left ≫ (snd B (W0 B q)).left).appTop.hom F := (appTop_comp _ _ _).symm
      _ = F := by rw [hsnd x, Scheme.Hom.id_appTop]; rfl
  have h1 : D = F := by
    have h := key (beta q)
    rw [sec_beta] at h
    exact h
  have h0 := key 1
  rw [sec_one] at h0
  exact h0.trans h1.symm

end

theorem gm_rhoW_eq_gm_id_of_abelian : ∀ (K : Type) [Field K] (A A' B : Over (Sp K)) [GrpObj B] (q : A ⟶ A'), IsAbelianScheme B →
    ∀ (D : Γ(Triple (q ▷ B).left, ⊤)ˣ) (w : Triple (q ▷ B).left), gm (rhoW q) w ⊤ D = gm (𝟙 _) w ⊤ D := by
  intro K _ A A' B _ q hB D w
  have := gm_comp_top (𝟙 _) (rhoW q) w D D (rhoW_appTop q hB D.val)
  rwa [Category.id_comp] at this

end GlobalTheory.DescNorm.RigidW
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Pinch.Aff

theorem pinched_of_iso (g : ℕ) {S S' Z B' C Y B₂ C₂ Y₂ : Scheme.{0}} {s' : S' ⟶ S} {z : Z ⟶ S}
    {b' : B' ⟶ S'} {e : C ⟶ Z} {i : Y ⟶ B'} {q : Y ⟶ C}
    {b₂ : B₂ ⟶ S'} {e₂ : C₂ ⟶ Z} {i₂ : Y₂ ⟶ B₂} {q₂ : Y₂ ⟶ C₂}
    (eB : B' ≅ B₂) (eC : C ≅ C₂) (eY : Y ≅ Y₂)
    (hb : b' = eB.hom ≫ b₂) (he : e = eC.hom ≫ e₂) (hi : i ≫ eB.hom = eY.hom ≫ i₂)
    (hq : q ≫ eC.hom = eY.hom ≫ q₂) (x : B') (h : Pinched g s' z b₂ e₂ i₂ q₂ (eB.hom x)) :
    Pinched g s' z b' e i q x := by
  obtain ⟨U, U', V, u, p, j, n, k, hu, hp, hj, hx, hn, hl⟩ := h
  refine ⟨U, U', V, u, p, j ≫ eB.inv, n, k ≫ eC.inv, hu, ?_, inferInstance, ?_, ?_, ?_⟩
  · simpa [hb] using hp
  · obtain ⟨t, ht⟩ := hx
    refine ⟨t, ?_⟩
    simp [ht]
  · simpa [he] using hn
  · intro T a a' h
    obtain ⟨y, hy1, hy2⟩ := hl T a a' h
    refine ⟨y ≫ eY.inv, ?_, ?_⟩
    · have : eY.inv ≫ i = i₂ ≫ eB.inv := by
        rw [Iso.inv_comp_eq, ← Category.assoc, ← hi]; simp
      rw [Category.assoc, this, ← Category.assoc, hy1, Category.assoc]
    · have : eY.inv ≫ q = q₂ ≫ eC.inv := by
        rw [Iso.inv_comp_eq, ← Category.assoc, ← hq]; simp
      rw [Category.assoc, this, ← Category.assoc, hy2, Category.assoc]

theorem isPushout_of_isPullback_Spec {A B C D : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D}
    {k : C ⟶ D} (H : IsPullback (Spec.map h) (Spec.map k) (Spec.map f) (Spec.map g)) :
    IsPushout f g h k := by
  have w : k.op ≫ g.op = h.op ≫ f.op := by
    apply Quiver.Hom.unop_inj
    simp only [unop_comp, Quiver.Hom.unop_op]
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp]
    exact H.w.symm
  exact (IsPullback.of_map Scheme.Spec w H.flip).unop

end GlobalTheory.Pinch.Aff

namespace GlobalTheory.Pinch.Aff

theorem pinched_affine_of_spec : (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (C' D E : Type) [CommRing C'] [CommRing D] [CommRing E] (φ : R' →+* C') (δ : R ⧸ c →+* D) (π : C' →+* E) (ψ : D →+* E), φ.Smooth → δ.IsStandardSmoothOfRelativeDimension g → IsPushout (CommRingCat.ofHom (φ.comp (algebraMap R R'))) (CommRingCat.ofHom (Ideal.Quotient.mk c)) (CommRingCat.ofHom π) (CommRingCat.ofHom (ψ.comp δ)) → IsPushout (CommRingCat.ofHom (δ.comp (Ideal.Quotient.mk c))) (CommRingCat.ofHom (algebraMap R R')) (CommRingCat.ofHom ψ) (CommRingCat.ofHom (π.comp φ)) → ∀ y : Sp E, GlobalTheory.Pinch.Pinched g (spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) (spMap φ) (spMap δ) (spMap π) (spMap ψ) (spMap π y)) → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (B' C Y : Scheme.{0}) (b' : B' ⟶ Sp R') (e : C ⟶ Sp (R ⧸ c)) (i : Y ⟶ B') (q : Y ⟶ C), IsAffine B' → IsAffine C → Smooth b' → e.appTop.hom.IsStandardSmoothOfRelativeDimension g → IsPullback i (q ≫ e) (b' ≫ spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) → IsPullback q (i ≫ b') (e ≫ spMap (Ideal.Quotient.mk c)) (spMap (algebraMap R R')) → ∀ y : Y, GlobalTheory.Pinch.Pinched g (spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) b' e i q (i y) := by
  intro H R _ _ R' _ _ _ hinj c hc g B' C Y b' e i q hB hC hsm hss h1 h2 y
  haveI : IsAffine Y := IsAffine.of_isPullback h1
  haveI := hsm
  set φc : CommRingCat.of R' ⟶ Γ(B', ⊤) := Spec.preimage (B'.isoSpec.inv ≫ b') with hφc
  set δc : CommRingCat.of (R ⧸ c) ⟶ Γ(C, ⊤) := Spec.preimage (C.isoSpec.inv ≫ e) with hδc
  set πc : Γ(B', ⊤) ⟶ Γ(Y, ⊤) := Spec.preimage (Y.isoSpec.inv ≫ i ≫ B'.isoSpec.hom) with hπc
  set ψc : Γ(C, ⊤) ⟶ Γ(Y, ⊤) := Spec.preimage (Y.isoSpec.inv ≫ q ≫ C.isoSpec.hom) with hψc
  have eφ : spMap φc.hom = B'.isoSpec.inv ≫ b' := by simp [spMap, φc]
  have eδ : spMap δc.hom = C.isoSpec.inv ≫ e := by simp [spMap, δc]
  have eπ : spMap πc.hom = Y.isoSpec.inv ≫ i ≫ B'.isoSpec.hom := by simp [spMap, πc]
  have eψ : spMap ψc.hom = Y.isoSpec.inv ≫ q ≫ C.isoSpec.hom := by simp [spMap, ψc]
  have hφs : φc.hom.Smooth := by
    rw [← HasRingHomProperty.Spec_iff (P := @Smooth), hφc, Spec.map_preimage]
    infer_instance
  have hδ : δc = (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ c))).inv ≫ e.appTop := by
    apply Spec.map_injective
    rw [hδc, Spec.map_preimage, Spec.map_comp, Iso.inv_comp_eq, ← Category.assoc,
      Scheme.isoSpec_hom_naturality, Category.assoc, Scheme.isoSpec_Spec_hom, ← Spec.map_comp,
      Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  have hδs : δc.hom.IsStandardSmoothOfRelativeDimension g := by
    rw [hδ, CommRingCat.hom_comp]
    exact (RingHom.isStandardSmoothOfRelativeDimension_respectsIso.cancel_left_isIso _ _).mpr hss
  have hp1 : IsPushout (CommRingCat.ofHom (φc.hom.comp (algebraMap R R'))) (CommRingCat.ofHom (Ideal.Quotient.mk c))
      (CommRingCat.ofHom πc.hom) (CommRingCat.ofHom (ψc.hom.comp δc.hom)) := by
    apply isPushout_of_isPullback_Spec
    simp only [CommRingCat.ofHom_comp, Spec.map_comp]
    change IsPullback (spMap πc.hom) (spMap ψc.hom ≫ spMap δc.hom) (spMap φc.hom ≫ spMap (algebraMap R R'))
      (spMap (Ideal.Quotient.mk c))
    rw [eφ, eδ, eπ, eψ]
    refine IsPullback.of_iso h1 Y.isoSpec B'.isoSpec (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp
  have hp2 : IsPushout (CommRingCat.ofHom (δc.hom.comp (Ideal.Quotient.mk c))) (CommRingCat.ofHom (algebraMap R R'))
      (CommRingCat.ofHom ψc.hom) (CommRingCat.ofHom (πc.hom.comp φc.hom)) := by
    apply isPushout_of_isPullback_Spec
    simp only [CommRingCat.ofHom_comp, Spec.map_comp]
    change IsPullback (spMap ψc.hom) (spMap πc.hom ≫ spMap φc.hom) (spMap δc.hom ≫ spMap (Ideal.Quotient.mk c))
      (spMap (algebraMap R R'))
    rw [eφ, eδ, eπ, eψ]
    refine IsPullback.of_iso h2 Y.isoSpec C.isoSpec (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp
  have hP := H R R' hinj c hc g Γ(B', ⊤) Γ(C, ⊤) Γ(Y, ⊤) φc.hom δc.hom πc.hom ψc.hom hφs hδs hp1 hp2
    (Y.isoSpec.hom y)
  have hpt : spMap πc.hom (Y.isoSpec.hom y) = B'.isoSpec.hom (i y) := by
    rw [eπ]; simp
  rw [hpt] at hP
  refine pinched_of_iso g B'.isoSpec C.isoSpec Y.isoSpec ?_ ?_ ?_ ?_ (i y) hP
  · rw [eφ]; simp
  · rw [eδ]; simp
  · rw [eπ]; simp
  · rw [eψ]; simp

end GlobalTheory.Pinch.Aff
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PinchLift

theorem exists_ratio_unit : ∀ (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (O₁ O₂ : Y.Opens) (s₁ : ∀ k, Γ(Y, L.U k ⊓ O₁)ˣ) (s₂ : ∀ k, Γ(Y, L.U k ⊓ O₂)ˣ), GlobalTheory.PinchLift.GenOn L O₁ s₁ → GlobalTheory.PinchLift.GenOn L O₂ s₂ → ∃ r : Γ(Y, O₁ ⊓ O₂)ˣ, ∀ (T : Scheme.{0}) (f : T ⟶ Y) (t : T) (k : L.ι), f t ∈ L.U k → f t ∈ O₁ → f t ∈ O₂ → gm f t (O₁ ⊓ O₂) r = gm f t (L.U k ⊓ O₁) (s₁ k) * (gm f t (L.U k ⊓ O₂) (s₂ k))⁻¹ := by
  intro Y L hL O₁ O₂ s₁ s₂ h₁ h₂
  have hW : ∀ k, L.U k ⊓ (O₁ ⊓ O₂) ≤ O₁ ⊓ O₂ := fun k => inf_le_right
  have hc : O₁ ⊓ O₂ ≤ ⨆ k, L.U k ⊓ (O₁ ⊓ O₂) := fun y hy => by
    obtain ⟨k, hk⟩ := exists_chart hL y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk, hy⟩
  have i₁ : ∀ k, L.U k ⊓ (O₁ ⊓ O₂) ≤ L.U k ⊓ O₁ := fun k => inf_le_inf_left _ inf_le_left
  have i₂ : ∀ k, L.U k ⊓ (O₁ ⊓ O₂) ≤ L.U k ⊓ O₂ := fun k => inf_le_inf_left _ inf_le_right
  let u : ∀ k, Γ(Y, L.U k ⊓ (O₁ ⊓ O₂))ˣ := fun k => res (i₁ k) (s₁ k) * (res (i₂ k) (s₂ k))⁻¹
  have hu : ∀ (T : Scheme.{0}) (f : T ⟶ Y) (t : T) (k : L.ι), f t ∈ L.U k ⊓ (O₁ ⊓ O₂) →
      gm f t (L.U k ⊓ (O₁ ⊓ O₂)) (u k) = gm f t (L.U k ⊓ O₁) (s₁ k) * (gm f t (L.U k ⊓ O₂) (s₂ k))⁻¹ := by
    intro T f t k hy
    simp only [u, map_mul, map_inv, gm_res f t (i₁ k) hy, gm_res f t (i₂ k) hy]
  obtain ⟨r, hr⟩ := glue_unit (O₁ ⊓ O₂) (fun k => L.U k ⊓ (O₁ ⊓ O₂)) hW hc u (by
    intro k l y hy
    have hk : y ∈ L.U k ⊓ (O₁ ⊓ O₂) := hy.1
    have hl : y ∈ L.U l ⊓ (O₁ ⊓ O₂) := hy.2
    show gm (𝟙 Y) y (L.U k ⊓ (O₁ ⊓ O₂)) (u k) = gm (𝟙 Y) y (L.U l ⊓ (O₁ ⊓ O₂)) (u l)
    rw [hu Y (𝟙 Y) y k hk, hu Y (𝟙 Y) y l hl, h₁ k l y hk.1 hl.1 hk.2.1, h₂ k l y hk.1 hl.1 hk.2.2,
      ← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div])
  refine ⟨r, fun T f t k hk ht₁ ht₂ => ?_⟩
  have hy : f t ∈ L.U k ⊓ (O₁ ⊓ O₂) := ⟨hk, ht₁, ht₂⟩
  rw [← gm_res f t (hW k) hy r, hr k, hu T f t k hy]

end GlobalTheory.PinchLift
end
end
