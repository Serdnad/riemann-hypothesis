module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle940
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationCrystalFormAdjointConjAction
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarSpecialUnitaryLyingOverFlagDomain
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
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LBGlue

variable {R : Type} [CommRing R] {X X₀ : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X} {L : LB X₀}

abbrev UU (t : (Small i L)ᵒᵖ) : X.Opens := t.unop.1.1.1

theorem le_of_hom {t t' : (Small i L)ᵒᵖ} (a : t ⟶ t') : UU t' ≤ UU t := leOfHom a.unop

theorem hom_eq {t t' : (Small i L)ᵒᵖ} (a b : t ⟶ t') : a = b :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

def homOf {t t' : (Small i L)ᵒᵖ} (h : UU t' ≤ UU t) : t ⟶ t' :=
  (homOfLE (show t'.unop ≤ t.unop from h)).op

variable (u : C1 (smallG i L ⋙ OAff s)) (hu : ∀ t t' a, IsUnit (u t t' a))

def uu (t t' : (Small i L)ᵒᵖ) (a : t ⟶ t') : Γ(X, UU t')ˣ := (hu t t' a).unit

variable {u hu}

theorem uu_comp (hm : mdef _ u = 0) {t t' t'' : (Small i L)ᵒᵖ} (a : t ⟶ t') (b : t' ⟶ t'') :
    res (le_of_hom b) (uu u hu t t' a) * uu u hu t' t'' b = uu u hu t t'' (a ≫ b) := by
  apply Units.ext
  have := congrFun (congrFun (congrFun (congrFun (congrFun hm t) t') t'') a) b
  exact sub_eq_zero.1 this

theorem gm_uu (hm : mdef _ u = 0) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) {t t' r : (Small i L)ᵒᵖ}
    (a : t ⟶ t') (b : t' ⟶ r) (hy : f y ∈ UU r) :
    gm f y (UU t') (uu u hu t t' a) =
      gm f y (UU r) (uu u hu t r (a ≫ b)) * (gm f y (UU r) (uu u hu t' r b))⁻¹ := by
  rw [← uu_comp hm a b, map_mul, gm_res f y _ hy, mul_inv_cancel_right]

theorem exists_g (hm : mdef _ u = 0) (hB : IsBasis (smallG i L)) (t t' : (Small i L)ᵒᵖ) :
    ∃ g : Γ(X, UU t ⊓ UU t')ˣ, ∀ p : (r : (Small i L)ᵒᵖ) × (t ⟶ r) × (t' ⟶ r),
      res (le_inf (le_of_hom p.2.1) (le_of_hom p.2.2)) g = uu u hu t p.1 p.2.1 * (uu u hu t' p.1 p.2.2)⁻¹ := by
  refine glue_unit _ (fun p : (r : (Small i L)ᵒᵖ) × (t ⟶ r) × (t' ⟶ r) ↦ UU p.1)
    (fun p ↦ le_inf (le_of_hom p.2.1) (le_of_hom p.2.2)) (fun x hx ↦ ?_) _ (fun p q x hx ↦ ?_)
  · obtain ⟨r, hr, hle⟩ := hB.cover x _ hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨r, homOf (hle.trans inf_le_left), homOf (hle.trans inf_le_right)⟩, hr⟩
  · obtain ⟨r, hr, hle⟩ := hB.cover x _ hx
    have c : p.1 ⟶ r := homOf (hle.trans inf_le_left)
    have d : q.1 ⟶ r := homOf (hle.trans inf_le_right)
    rw [map_mul, map_mul, map_inv, map_inv, gm_uu hm (𝟙 X) x p.2.1 c hr, gm_uu hm (𝟙 X) x p.2.2 c hr,
      gm_uu hm (𝟙 X) x q.2.1 d hr, gm_uu hm (𝟙 X) x q.2.2 d hr, hom_eq (q.2.1 ≫ d) (p.2.1 ≫ c),
      hom_eq (q.2.2 ≫ d) (p.2.2 ≫ c)]
    group

variable (u hu)

def glueLB (hm : mdef _ u = 0) (hB : IsBasis (smallG i L)) : LB X :=
  ⟨(Small i L)ᵒᵖ, UU, fun t t' ↦ Classical.choose (exists_g (hu := hu) hm hB t t')⟩

variable {u hu}

theorem gm_glue (hm : mdef _ u = 0) (hB : IsBasis (smallG i L)) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y)
    {t t' r : (Small i L)ᵒᵖ} (a : t ⟶ r) (b : t' ⟶ r) (hy : f y ∈ UU r) :
    gm f y (UU t ⊓ UU t') ((glueLB u hu hm hB).g t t') =
      gm f y (UU r) (uu u hu t r a) * (gm f y (UU r) (uu u hu t' r b))⁻¹ := by
  have := Classical.choose_spec (exists_g (hu := hu) hm hB t t') ⟨r, a, b⟩
  show gm f y _ (Classical.choose (exists_g (hu := hu) hm hB t t')) = _
  rw [← gm_res f y (le_inf (le_of_hom a) (le_of_hom b)) hy, this, map_mul, map_inv]

theorem isLB_glue (hm : mdef _ u = 0) (hB : IsBasis (smallG i L)) : (glueLB u hu hm hB).IsLB := {
  cover := by
    refine eq_top_iff.2 fun x _ ↦ ?_
    obtain ⟨r, hr, -⟩ := hB.cover x ⊤ trivial
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨r, hr⟩
  g_self := fun (t : (Small i L)ᵒᵖ) ↦ by
    refine unit_ext fun x hx ↦ ?_
    obtain ⟨r, hr, hle⟩ := hB.cover x (UU t) hx
    rw [gm_res _ x _ hx, map_one]
    exact (gm_glue hm hB (𝟙 X) x (homOf hle) (homOf hle) hr).trans (mul_inv_cancel _)
  cocycle := fun (t t' t'' : (Small i L)ᵒᵖ) ↦ by
    refine unit_ext fun x hx ↦ ?_
    obtain ⟨r, hr, hle⟩ := hB.cover x (UU t ⊓ UU t' ⊓ UU t'') hx
    have a : t ⟶ r := homOf (hle.trans (inf_le_left.trans inf_le_left))
    have b : t' ⟶ r := homOf (hle.trans (inf_le_left.trans inf_le_right))
    have c : t'' ⟶ r := homOf (hle.trans inf_le_right)
    rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, gm_res _ x _ hx]
    refine (congrArg₂ (· * ·) (gm_glue hm hB (𝟙 X) x a b hr) (gm_glue hm hB (𝟙 X) x b c hr)).trans
      ((?_ : _ = _).trans (gm_glue hm hB (𝟙 X) x a c hr).symm)
    group }

theorem gm_lift (hl : IsLift s i L u) {t r : (Small i L)ᵒᵖ} (a : t ⟶ r) (y : X₀) (hy : i y ∈ UU r) :
    gm i y (UU r) (uu u hu t r a) = gm (𝟙 X₀) y _ (L.g t.unop.1.2 r.unop.1.2) := by
  have e := gm_pull (𝟙 X₀) i y (UU r) hy (uu u hu t r a)
  rw [Category.id_comp] at e
  have e' : pullU i (UU r) (uu u hu t r a) = res (Small.le_inf a) (L.g t.unop.1.2 r.unop.1.2) :=
    Units.ext (hl t r a)
  rw [← e, e', gm_res (𝟙 X₀) y _ hy]

def chart (hL : L.IsLB) (hl : IsLift s i L u) (hm : mdef _ u = 0) (hB : IsBasis (smallG i L)) :
    ChartPull ((glueLB u hu hm hB).pull i) L (𝟙 X₀) where
  idx J := (J PUnit.unit).unop.1.2
  le J y hy := (J PUnit.unit).unop.2 (mem_pull.1 hy)
  g y J J' hj hj' := by
    have hx : i y ∈ UU (J PUnit.unit) := mem_pull.1 hj
    have hx' : i y ∈ UU (J' PUnit.unit) := mem_pull.1 hj'
    obtain ⟨r, hr, hle⟩ := hB.cover (i y) (UU (J PUnit.unit) ⊓ UU (J' PUnit.unit)) ⟨hx, hx'⟩
    let t₁ : (Small i L)ᵒᵖ := J PUnit.unit
    let t₂ : (Small i L)ᵒᵖ := J' PUnit.unit
    have a : t₁ ⟶ r := homOf (hle.trans inf_le_left)
    have b : t₂ ⟶ r := homOf (hle.trans inf_le_right)
    have e := gm_pull_g (glueLB u hu hm hB) i (𝟙 X₀) y J J' hj hj'
    rw [Category.id_comp] at e
    refine e.trans ((gm_glue hm hB i y a b hr).trans ?_)
    rw [gm_lift hl a y hr, gm_lift hl b y hr]
    have hjr : (𝟙 X₀) y ∈ L.U r.unop.1.2 := r.unop.2 hr
    have hj₁ : (𝟙 X₀) y ∈ L.U (J PUnit.unit).unop.1.2 := (J PUnit.unit).unop.2 hx
    have hj₂ : (𝟙 X₀) y ∈ L.U (J' PUnit.unit).unop.1.2 := (J' PUnit.unit).unop.2 hx'
    rw [← gm_cocycle hL (𝟙 X₀) y hj₁ hj₂ hjr, mul_inv_cancel_right]

end GlobalTheory.LBGlue


open GlobalTheory.LBGlue in
theorem GlobalTheory.LBLift.exists_pic_of_strict_lift : ∀ (R : Type) [CommRing R] (X X₀ : Scheme.{0}) (s : X ⟶ Sp R)
    (i : X₀ ⟶ X) (L : LB X₀) (hL : L.IsLB) (u : C1 (smallG i L ⋙ OAff s)), IsBasis (smallG i L) →
    IsLift s i L u → (∀ t t' a, IsUnit (u t t' a)) → mdef _ u = 0 →
    ∃ c : Pic X, GlobalTheory.CechPic.pull i c = cls L hL := by
  intro R _ X X₀ s i L hL u hB hl hu hm
  refine ⟨cls _ (isLB_glue (hu := hu) hm hB), ?_⟩
  rw [← cls_pull (isLB_glue (hu := hu) hm hB) i (pull_isLB (isLB_glue (hu := hu) hm hB) i)]
  exact (cls_eq_iff _ hL).2 (iso_of_chart hL (chart hL hl hm hB))
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LBLift

theorem app_presheaf_map {X Y : Scheme.{0}} (f : Y ⟶ X) {V W : X.Opens} (h : W ≤ V) (x : Γ(X, V)) :
    (f.app W).hom ((X.presheaf.map (homOfLE h).op).hom x) =
      (Y.presheaf.map (homOfLE (f.preimage_mono h)).op).hom ((f.app V).hom x) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl

theorem presheaf_map_map {Y : Scheme.{0}} {U V W : Y.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (y : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h₂).op).hom ((Y.presheaf.map (homOfLE h₁).op).hom y) =
      (Y.presheaf.map (homOfLE (h₂.trans h₁)).op).hom y := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

variable {R : Type} [CommRing R] {I : Ideal R} {X X₀ : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X} {L : LB X₀}

theorem isBasis_smallG (hi : IsThick I s i) (hL : L.IsLB) : IsBasis (smallG i L) := by
  haveI := hi.closed
  have hind : Topology.IsInducing i.base := i.isClosedEmbedding.isInducing
  have cov : ∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : (Small i L)ᵒᵖ,
      x ∈ ((smallG i L).obj t).unop.1 ∧ ((smallG i L).obj t).unop.1 ≤ U := by
    intro x U hx
    obtain ⟨x₀, rfl⟩ := hi.surj.surj x
    have hx₀ : x₀ ∈ ⨆ j, L.U j := by rw [hL.cover]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx₀
    obtain ⟨V, hV, hVe⟩ := hind.isOpen_iff.1 (L.U j).isOpen
    have hxV : i.base x₀ ∈ (⟨V, hV⟩ : X.Opens) ⊓ U := ⟨show x₀ ∈ i.base ⁻¹' V from hVe ▸ hj, hx⟩
    obtain ⟨W, hW, hxW, hWle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hxV
    have hsm : i ⁻¹ᵁ W ≤ L.U j := fun y hy ↦ by
      show y ∈ (L.U j : Set X₀)
      rw [← hVe]
      exact (hWle hy).1
    exact ⟨Opposite.op ⟨(⟨W, hW⟩, j), hsm⟩, hxW, fun y hy ↦ (hWle hy).2⟩
  refine ⟨cov, fun t₁ t₂ x U hx h₁ h₂ ↦ ?_⟩
  obtain ⟨t₃, hx₃, hle⟩ := cov x (U ⊓ ((smallG i L).obj t₁).unop.1 ⊓ ((smallG i L).obj t₂).unop.1)
    ⟨⟨hx, h₁⟩, h₂⟩
  exact ⟨t₃, ⟨(homOfLE (show t₃.unop ≤ t₁.unop from fun y hy ↦ (hle hy).1.2)).op⟩,
    ⟨(homOfLE (show t₃.unop ≤ t₂.unop from fun y hy ↦ (hle hy).2)).op⟩, hx₃, fun y hy ↦ (hle hy).1.1⟩

theorem exists_isLift (hi : IsThick I s i) : ∃ u, IsLift s i L u :=
  ⟨fun p q a ↦ (hi.app_surj q.unop.1.1 (res (Small.le_inf a) (L.g p.unop.1.2 q.unop.1.2)).val).choose,
    fun p q a ↦ (hi.app_surj q.unop.1.1 _).choose_spec⟩

end GlobalTheory.LBLift

namespace GlobalTheory.LBLift
variable {R : Type} [CommRing R] {I : Ideal R} {X X₀ : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X} {L : LB X₀}

theorem isUnit_of_sqZero {A A₀ : Type} [CommRing A] [CommRing A₀] (p : A →+* A₀)
    (hp : Function.Surjective p) (K : Ideal A) (hK : K ^ 2 = ⊥) (hker : ∀ a, p a = 0 → a ∈ K)
    (x : A) (hx : IsUnit (p x)) : IsUnit x := by
  obtain ⟨v, hv⟩ := hx.exists_right_inv
  obtain ⟨y, rfl⟩ := hp v
  have hn : x * y - 1 ∈ K := hker _ (by simp [hv])
  have hsq : (x * y - 1) * (x * y - 1) = 0 := by
    have : (x * y - 1) * (x * y - 1) ∈ K ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hn hn
    rw [hK] at this; simpa using this
  have hnil : IsNilpotent (x * y - 1) := ⟨2, by rw [pow_two, hsq]⟩
  have : IsUnit (x * y) := by simpa using hnil.isUnit_one_add
  exact isUnit_of_mul_isUnit_left this

theorem lift_isUnit (hI : I ^ 2 = ⊥) (hi : IsThick I s i) {u : C1 (smallG i L ⋙ OAff s)} (hu : IsLift s i L u)
    (p q : (Small i L)ᵒᵖ) (a : p ⟶ q) : IsUnit (u p q a) := by
  have hK : ∀ (A : Type) [CommRing A] [Algebra R A], (I.map (algebraMap R A)) ^ 2 = ⊥ := fun A _ _ ↦ by
    rw [← Ideal.map_pow, hI, Ideal.map_bot]
  exact isUnit_of_sqZero (A := Γ(X, q.unop.1.1.1)) (i.app q.unop.1.1.1).hom (hi.app_surj q.unop.1.1)
    (I.map (algebraMap R (Sec s q.unop.1.1.1))) (hK (Sec s q.unop.1.1.1)) (fun b hb ↦ (hi.ker q.unop.1.1 b).1 hb) (u p q a)
    ((hu p q a).symm ▸ Units.isUnit _)

theorem lift_mdef (hi : IsThick I s i) (hL : L.IsLB) {u : C1 (smallG i L ⋙ OAff s)} (hu : IsLift s i L u) :
    In2 I _ (mdef _ u) := by
  intro t t' t'' a b
  refine (hi.ker t''.unop.1.1 _).1 ?_
  have hb : t''.unop.1.1.1 ≤ t'.unop.1.1.1 := leOfHom b.unop
  have h2 : i ⁻¹ᵁ t''.unop.1.1.1 ≤ L.U t.unop.1.2 ⊓ L.U t'.unop.1.2 ⊓ L.U t''.unop.1.2 :=
    le_inf ((i.preimage_mono hb).trans (Small.le_inf a)) t''.unop.2
  have hc := congrArg (fun w ↦ (X₀.presheaf.map (homOfLE h2).op).hom w.val)
    (hL.cocycle t.unop.1.2 t'.unop.1.2 t''.unop.1.2)
  simp only [Units.val_mul, map_mul, res, Units.coe_map, MonoidHom.coe_coe,
    presheaf_map_map] at hc
  have k : ∀ (x : Γ(X, t'.unop.1.1.1)) (y z : Γ(X, t''.unop.1.1.1)),
      (i.app t'.unop.1.1.1).hom x = (res (Small.le_inf a) (L.g t.unop.1.2 t'.unop.1.2)).val →
      (i.app t''.unop.1.1.1).hom y = (res (Small.le_inf b) (L.g t'.unop.1.2 t''.unop.1.2)).val →
      (i.app t''.unop.1.1.1).hom z = (res (Small.le_inf (a ≫ b)) (L.g t.unop.1.2 t''.unop.1.2)).val →
      (i.app t''.unop.1.1.1).hom ((X.presheaf.map (homOfLE hb).op).hom x * y - z) = 0 := by
    intro x y z hx hy hz
    rw [map_sub, map_mul, app_presheaf_map, hx, hy, hz, sub_eq_zero]
    simp only [res, Units.coe_map, MonoidHom.coe_coe, presheaf_map_map]
    exact hc
  exact k _ _ _ (hu t t' a) (hu t' t'' b) (hu t t'' (a ≫ b))

theorem isLiftOfTransitionUnits_of_ideal_cochain_change (hi : IsThick I s i) {u : C1 (smallG i L ⋙ OAff s)} (hu : IsLift s i L u)
    (u' : C1 (smallG i L ⋙ OAff s)) (h : In1 I _ (u' - u)) : IsLift s i L u' := by
  intro p q a
  have h0 := (hi.ker q.unop.1.1 _).2 (h p q a)
  have e : u' p q a = u p q a + (u' - u) p q a := by simp
  rw [e]
  exact (map_add (i.app q.unop.1.1.1).hom (u p q a) ((u' - u) p q a)).trans
    ((congrArg₂ (· + ·) (hu p q a) h0).trans (add_zero _))

end GlobalTheory.LBLift

namespace GlobalTheory.LBLift

theorem small_basis_lift : ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = ⊥ → ∀ (X X₀ : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (L : LB X₀), IsThick I s i → L.IsLB → IsBasis (smallG i L) ∧ (∃ u, IsLift s i L u) ∧ ∀ u, IsLift s i L u → (∀ t t' a, IsUnit (u t t' a)) ∧ In2 I _ (mdef _ u) ∧ ∀ u', In1 I _ (u' - u) → IsLift s i L u' := by
  intro R _ I hI X X₀ s i L hi hL
  exact ⟨isBasis_smallG hi hL, exists_isLift hi, fun u hu ↦
    ⟨lift_isUnit hI hi hu, lift_mdef hi hL hu, fun u' h ↦ isLiftOfTransitionUnits_of_ideal_cochain_change hi hu u' h⟩⟩

end GlobalTheory.LBLift
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LBLift

namespace CocCorr

variable {R : Type} [CommRing R] {I : Ideal R}

theorem mul_eq_zero_of_mem (hI : I ^ 2 = ⊥) {S : Type} [CommRing S] [Algebra R S] {x y : S}
    (hx : x ∈ I.map (algebraMap R S)) (hy : y ∈ I.map (algebraMap R S)) : x * y = 0 := by
  have h : I.map (algebraMap R S) ^ 2 = ⊥ := by rw [← Ideal.map_pow, hI, Ideal.map_bot]
  have := Ideal.mul_mem_mul hx hy
  rw [← pow_two, h] at this
  exact (Submodule.mem_bot _).1 this

theorem map_mem {S S' : Type} [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S'] (φ : S →+* S')
    (hφ : ∀ r : R, φ (algebraMap R S r) = algebraMap R S' r) {x : S}
    (hx : x ∈ I.map (algebraMap R S)) : φ x ∈ I.map (algebraMap R S') := by
  have h := Ideal.mem_map_of_mem φ hx
  rwa [Ideal.map_map, show φ.comp (algebraMap R S) = algebraMap R S' from RingHom.ext hφ] at h

end CocCorr

open CocCorr in
theorem cocycle_of_sqZero : ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = ⊥ → ∀ (D T : Type) [Category.{0} D] [Category.{0} T] (F : D ⥤ CommAlgCat.{0} R) (F' : T ⥤ CommAlgCat.{0} R) (n₀ n₁ n₂ : CoefMap (RingHom.id R) F F'), PrimI I n₀ n₁ n₂ → ∀ (u : C1 F) (v : C0 F'), (∀ t t' a, IsUnit (u t t' a)) → In2 I F (mdef F u) → (∀ t, IsUnit (v t)) → MulRel I n₀ n₁ n₂ u v → ∃ u' : C1 F, In1 I F (u' - u) ∧ mdef F u' = 0 := by
  intro R _ I hI D T _ _ F F' n₀ n₁ n₂ hP u v hu hm hv hrel

  have hmpI : ∀ {t t' : D} (b : t ⟶ t') {x : F.obj t}, x ∈ I.map (algebraMap R (F.obj t)) →
      mp F b x ∈ I.map (algebraMap R (F.obj t')) := fun b x hx ↦
    map_mem (mp F b).toRingHom (fun r ↦ (mp F b).commutes r) hx
  have hmpI' : ∀ {t t' : T} (b : t ⟶ t') {x : F'.obj t}, x ∈ I.map (algebraMap R (F'.obj t)) →
      mp F' b x ∈ I.map (algebraMap R (F'.obj t')) := fun b x hx ↦
    map_mem (mp F' b).toRingHom (fun r ↦ (mp F' b).commutes r) hx
  have hαI : ∀ (n : CoefMap (RingHom.id R) F F') (t : T) {x : F.obj (n.G.obj t)},
      x ∈ I.map (algebraMap R (F.obj (n.G.obj t))) → n.α t x ∈ I.map (algebraMap R (F'.obj t)) := by
    intro n t x hx
    refine map_mem (n.α t) (fun r ↦ ?_) hx
    rw [Algebra.algebraMap_eq_smul_one, n.smul, map_one, RingHom.id_apply, Algebra.algebraMap_eq_smul_one]

  let z : C2 F := fun t t' t'' a b ↦ mdef F u t t' t'' a b * Ring.inverse (u t t'' (a ≫ b))
  have hzI : In2 I F z := fun t t' t'' a b ↦ Ideal.mul_mem_right _ _ (hm t t' t'' a b)
  have hz_eq : ∀ {t t' t'' : D} (a : t ⟶ t') (b : t' ⟶ t''),
      mp F b (u t t' a) * u t' t'' b = u t t'' (a ≫ b) + u t t'' (a ≫ b) * z t t' t'' a b := by
    intro t t' t'' a b
    have h1 := Ring.mul_inverse_cancel _ (hu t t'' (a ≫ b))
    simp only [z, mdef]
    linear_combination (-(mp F b (u t t' a) * u t' t'' b - u t t'' (a ≫ b))) * h1

  have hz2 : z ∈ Z2 F := by
    intro t t' t'' t''' a b c
    have e1 := congrArg (mp F c) (hz_eq a b)
    simp only [map_mul, map_add (f := _), ← mp_comp] at e1
    have e2 := hz_eq (a ≫ b) c
    have e3 := hz_eq a (b ≫ c)
    have e4 := hz_eq b c
    rw [Category.assoc] at e2
    have p1 := mul_eq_zero_of_mem hI (hmpI c (hzI _ _ _ a b)) (hzI _ _ _ (a ≫ b) c)
    have p2 := mul_eq_zero_of_mem hI (hzI _ _ _ a (b ≫ c)) (hzI _ _ _ b c)
    have hU : u t t''' (a ≫ b ≫ c) * (mp F c (z t t' t'' a b) + z t t'' t''' (a ≫ b) c
        - z t t' t''' a (b ≫ c) - z t' t'' t''' b c) = 0 := by
      linear_combination (-(u t'' t''' c)) * e1 - (1 + mp F c (z t t' t'' a b)) * e2
        + (1 + z t' t'' t''' b c) * e3 + mp F (b ≫ c) (u t t' a) * e4
        - u t t''' (a ≫ b ≫ c) * p1 + u t t''' (a ≫ b ≫ c) * p2
    have := ((hu _ _ _).mul_right_eq_zero).1 hU
    linear_combination this

  let U : CoefMap (RingHom.id R) F F' → C1 F' := fun n t t' a ↦ n.α t' (u _ _ (n.G.map a))
  let W : C1 F' := fun t t' a ↦ U n₁ t t' a * U n₂ t t' a * mp F' a (v t)
  let f : C1 F' := fun t t' a ↦ (U n₀ t t' a * v t' - W t t' a) * Ring.inverse (W t t' a)
  have hUu : ∀ n t t' a, IsUnit (U n t t' a) := fun n t t' a ↦ (hu _ _ _).map (n.α t')
  have hWu : ∀ t t' a, IsUnit (W t t' a) := fun t t' a ↦
    ((hUu n₁ t t' a).mul (hUu n₂ t t' a)).mul ((hv t).map (mp F' a))
  have hfI : In1 I F' f := fun t t' a ↦ Ideal.mul_mem_right _ _ (hrel t t' a)
  have hf_eq : ∀ {t t' : T} (a : t ⟶ t'), U n₀ t t' a * v t' =
      U n₁ t t' a * U n₂ t t' a * mp F' a (v t) + U n₁ t t' a * U n₂ t t' a * mp F' a (v t) * f t t' a := by
    intro t t' a
    have h1 := Ring.mul_inverse_cancel _ (hWu t t' a)
    simp only [f]
    linear_combination (-(U n₀ t t' a * v t' - W t t' a)) * h1
  have hUeq : ∀ (n : CoefMap (RingHom.id R) F F') {t t' t'' : T} (a : t ⟶ t') (b : t' ⟶ t''),
      mp F' b (U n t t' a) * U n t' t'' b = U n t t'' (a ≫ b) +
        U n t t'' (a ≫ b) * n.α t'' (z _ _ _ (n.G.map a) (n.G.map b)) := by
    intro n t t' t'' a b
    have h := congrArg (n.α t'') (hz_eq (n.G.map a) (n.G.map b))
    simp only [map_mul, map_add (f := _), n.naturality, ← Functor.map_comp] at h
    exact h
  have hd : d1 F' f = (n₀.pullbackTwoCocycle ⟨z, hz2⟩).1 - (n₁.pullbackTwoCocycle ⟨z, hz2⟩).1 - (n₂.pullbackTwoCocycle ⟨z, hz2⟩).1 := by
    funext t t' t'' a b
    simp only [d1_apply, Pi.sub_apply, CoefMap.pullCocycleTwo_apply]
    have ra := congrArg (mp F' b) (hf_eq a)
    simp only [map_mul, map_add (f := _), ← mp_comp] at ra
    have rb := hf_eq b
    have rab := hf_eq (a ≫ b)
    have h0 := hUeq n₀ a b
    have h1 := hUeq n₁ a b
    have h2 := hUeq n₂ a b
    set a0 := mp F' b (U n₀ t t' a)
    set a1 := mp F' b (U n₁ t t' a)
    set a2 := mp F' b (U n₂ t t' a)
    set b0 := U n₀ t' t'' b
    set b1 := U n₁ t' t'' b
    set b2 := U n₂ t' t'' b
    set c0 := U n₀ t t'' (a ≫ b)
    set c1 := U n₁ t t'' (a ≫ b)
    set c2 := U n₂ t t'' (a ≫ b)
    set V := mp F' (a ≫ b) (v t)
    set V' := mp F' b (v t')
    set V'' := v t''
    set F1 := mp F' b (f t t' a)
    set F2 := f t' t'' b
    set F3 := f t t'' (a ≫ b)
    set Z0 := n₀.α t'' (z _ _ _ (n₀.G.map a) (n₀.G.map b))
    set Z1 := n₁.α t'' (z _ _ _ (n₁.G.map a) (n₁.G.map b))
    set Z2' := n₂.α t'' (z _ _ _ (n₂.G.map a) (n₂.G.map b))
    have indexFFirst : F1 ∈ I.map (algebraMap R (F'.obj t'')) := hmpI' b (hfI _ _ a)
    have indexFSecond : F2 ∈ I.map (algebraMap R (F'.obj t'')) := hfI _ _ b
    have indexFThird : F3 ∈ I.map (algebraMap R (F'.obj t'')) := hfI _ _ (a ≫ b)
    have iZ0 : Z0 ∈ I.map (algebraMap R (F'.obj t'')) := hαI n₀ t'' (hzI _ _ _ _ _)
    have iZ1 : Z1 ∈ I.map (algebraMap R (F'.obj t'')) := hαI n₁ t'' (hzI _ _ _ _ _)
    have iZ2 : Z2' ∈ I.map (algebraMap R (F'.obj t'')) := hαI n₂ t'' (hzI _ _ _ _ _)
    have hT : c1 * c2 * V * V' * ((1 + Z1) * (1 + Z2') * (1 + F1) * (1 + F2) - (1 + F3) * (1 + Z0)) = 0 := by
      linear_combination (-(a1 * a2 * V * (1 + F1))) * rb - b0 * V'' * ra
        - V * V' * (1 + F1) * (1 + F2) * (c1 * (1 + Z1) * h2 + a2 * b2 * h1) + (1 + Z0) * V' * rab + V' * V'' * h0
    have hK : IsUnit (c1 * c2 * V * V') :=
      (((hUu n₁ _ _ _).mul (hUu n₂ _ _ _)).mul ((hv t).map _)).mul ((hv t').map _)
    have hX := (hK.mul_right_eq_zero).1 hT
    linear_combination hX - (1 + F1 + F2 + F1 * F2) * mul_eq_zero_of_mem hI iZ1 iZ2
      - (1 + F2) * mul_eq_zero_of_mem hI iZ1 indexFFirst - mul_eq_zero_of_mem hI iZ1 indexFSecond
      - (1 + F2) * mul_eq_zero_of_mem hI iZ2 indexFFirst - mul_eq_zero_of_mem hI iZ2 indexFSecond
      - mul_eq_zero_of_mem hI indexFFirst indexFSecond + mul_eq_zero_of_mem hI indexFThird iZ0

  obtain ⟨f₀, hf₀I, hf₀⟩ := hP ⟨z, hz2⟩ f hzI hfI hd
  refine ⟨fun t t' a ↦ u t t' a * (1 - f₀ t t' a), fun t t' a ↦ ?_, ?_⟩
  · simp only [Pi.sub_apply]
    rw [show u t t' a * (1 - f₀ t t' a) - u t t' a = -(u t t' a * f₀ t t' a) by ring]
    exact (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_left _ _ (hf₀I t t' a))
  · funext t t' t'' a b
    simp only [mdef, Pi.zero_apply, map_mul, map_sub, map_one]
    have e := hz_eq a b
    have ed := congrFun (congrFun (congrFun (congrFun (congrFun hf₀ t) t') t'') a) b
    rw [d1_apply] at ed
    have iF := hmpI b (hf₀I t t' a)
    have iG := hf₀I t' t'' b
    have iz := hzI t t' t'' a b
    linear_combination (1 - mp F b (f₀ t t' a)) * (1 - f₀ t' t'' b) * e - u t t'' (a ≫ b) * ed
      + u t t'' (a ≫ b) * (1 + z t t' t'' a b) * mul_eq_zero_of_mem hI iF iG
      - u t t'' (a ≫ b) * mul_eq_zero_of_mem hI iz iF - u t t'' (a ≫ b) * mul_eq_zero_of_mem hI iz iG

end GlobalTheory.LBLift
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.polarizationCrystalForm_adjoint_conj_action : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {K : Type} [Field K] {x : Sp K ⟶ Xo.X} {A : Over (Sp K)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G x π → ∀ (a : OAct (𝓞 E) A), (∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) → ∀ {ψ : LinearMap.BilinForm K (HdR A)}, IsPolForm (dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ → IsAdjointFor a (fun z => H.bar z) ψ := by
  first | exact @GlobalTheory.PolAdjoint.polForm_adjoint | exact GlobalTheory.PolAdjoint.polForm_adjoint | (intros; apply GlobalTheory.PolAdjoint.polForm_adjoint <;> assumption)
end

section

open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem _root_.GlobalTheory.T.exists_haar_specialUnitary_lying_over_flagDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) [MeasurableSpace (realSU X.Ψ X.Gm)] [BorelSpace (realSU X.Ψ X.Gm)], 1 ≤ r → IsOrth X x → ∃ ν : Measure (realSU X.Ψ X.Gm), ν.IsHaarMeasure ∧ ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul y b) = φ y) → ∫⁻ g, φ (X.lmulC (fun τ => (((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x) ∂ν = ∫⁻ z, φ (cpt X x z) ∂muF X x := by
  first | exact @GlobalTheory.SUHaarOver.exists_haar_lying_over | exact GlobalTheory.SUHaarOver.exists_haar_lying_over | (intros; apply GlobalTheory.SUHaarOver.exists_haar_lying_over <;> assumption)
end
