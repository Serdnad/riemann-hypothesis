module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
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
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

lemma res_of_le_of_le {X : Scheme.{0}} {U Z : X.Opens} (h : Z ≤ U) (h' : U ≤ Z) (x : Γ(X, U)ˣ) :
    res h' (res h x) = x := by
  rw [res_res']
  ext
  simp [res]

def gw {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (ψ : K → (Y ⟶ X)) (ε : K → ℤ) (j j' : K → L.ι) :
    Γ(Y, LB.wchart L ψ j ⊓ LB.wchart L ψ j')ˣ :=
  ∏ k, (res (le_inf (inf_le_left.trans (LB.wchart_le L ψ j k)) (inf_le_right.trans (LB.wchart_le L ψ j' k)) :
      LB.wchart L ψ j ⊓ LB.wchart L ψ j' ≤ ψ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)))
    (pullU (ψ k) _ (L.g (j k) (j' k)))) ^ (ε k)


lemma eq_top_of_closedPoint_mem {V : Type} [CommRing V] [IsLocalRing V] (U : (Spec (CommRingCat.of V)).Opens)
    (hU : (IsLocalRing.closedPoint V : Spec (CommRingCat.of V)) ∈ U) : U = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  exact (IsLocalRing.specializes_closedPoint (R := V) x).mem_open U.isOpen hU

theorem exists_gen_of_isLB_local {V : Type} [CommRing V] [IsLocalRing V]
    (M : LB (Spec (CommRingCat.of V))) (hM : M.IsLB) : ∃ e : M.Gen, e.IsGen := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, (IsLocalRing.closedPoint V : Spec (CommRingCat.of V)) ∈ M.U i := by
    have : (IsLocalRing.closedPoint V : Spec (CommRingCat.of V)) ∈
        (⊤ : (Spec (CommRingCat.of V)).Opens) := trivial
    rw [← hM.cover] at this
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have htop := eq_top_of_closedPoint_mem _ hi₀
  have hto : ∀ W : (Spec (CommRingCat.of V)).Opens, W ≤ M.U i₀ := fun W => by
    rw [htop]
    exact le_top
  refine ⟨⟨fun i => res (le_inf le_rfl (hto _) : M.U i ≤ M.U i ⊓ M.U i₀) (M.g i i₀)⟩, fun i j => ?_⟩
  have hc := congrArg (res (le_inf le_rfl (hto _) : M.U i ⊓ M.U j ≤ M.U i ⊓ M.U j ⊓ M.U i₀))
    (hM.cocycle i j i₀)
  simp only [map_mul, res_res'] at hc
  simp only [res_res']
  rw [← hc]
  congr 1

theorem exists_gen_of_local {V : Type} [CommRing V] [IsLocalRing V] {X : Scheme.{0}} (L : LB X) (hL : L.IsLB)
    {K : Type} [Fintype K] (φ : K → (Spec (CommRingCat.of V) ⟶ X)) (ε : K → ℤ) :
    ∃ e : LB.Gen (LB.LinComb L φ ε), e.IsGen := exists_gen_of_isLB_local _ (linComb_isLB (L := L) (φ := φ) (ε := ε) hL)

lemma exists_chart_top {V : Type} [CommRing V] [IsLocalRing V] {X : Scheme.{0}} (L : LB X) (hL : L.IsLB)
    {K : Type} [Fintype K] (φ : K → (Spec (CommRingCat.of V) ⟶ X)) (ε : K → ℤ) :
    ∃ j₀ : K → L.ι, LB.wchart L φ j₀ = ⊤ := by
  have hc : ∀ k, ∃ i, (φ k).base (IsLocalRing.closedPoint V) ∈ L.U i := by
    intro k
    have : (φ k).base (IsLocalRing.closedPoint V) ∈ (⊤ : X.Opens) := trivial
    rw [← hL.cover] at this
    exact TopologicalSpace.Opens.mem_iSup.1 this
  choose j₀ hj₀ using hc
  exact ⟨j₀, eq_top_of_closedPoint_mem _ (Set.mem_iInter.2 fun k => hj₀ k)⟩

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}

lemma hasVal_of_ne_zero (hϖ : Irreducible ϖ) {c : FractionRing V} (hc : c ≠ 0) : ∃ n, HasVal ϖ c n := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) c
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hc
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨l, u', hu'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hϖ0 : algebraMap V (FractionRing V) ϖ ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    exact hϖ.ne_zero
  have hu'0 : algebraMap V (FractionRing V) (u' : V) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    exact u'.ne_zero
  refine ⟨(k : ℤ) - l, u * u'⁻¹, ?_⟩
  rw [hu, hu', zpow_sub₀ hϖ0]
  simp only [Units.val_mul, map_mul, map_pow, map_units_inv, zpow_natCast]
  field_simp

private lemma hasVal_eq_of_hasVal_of_le (hϖ : Irreducible ϖ) {c : FractionRing V} {n m : ℤ}
    (hn : HasVal ϖ c n) (hm : HasVal ϖ c m) (h : m ≤ n) : n = m := by
  obtain ⟨u, hu⟩ := hn
  obtain ⟨u', hu'⟩ := hm
  have hA0 : algebraMap V (FractionRing V) ϖ ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    exact hϖ.ne_zero
  have hU0 : algebraMap V (FractionRing V) (u : V) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    exact u.ne_zero
  have e : algebraMap V (FractionRing V) ϖ ^ n * algebraMap V (FractionRing V) (u : V) =
      algebraMap V (FractionRing V) ϖ ^ m * algebraMap V (FractionRing V) (u' : V) :=
    hu.symm.trans hu'
  obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h)
  have h1 : algebraMap V (FractionRing V) ϖ ^ d =
      algebraMap V (FractionRing V) ((u' * u⁻¹ : Vˣ) : V) := by
    rw [← zpow_natCast, ← hd, zpow_sub₀ hA0, Units.val_mul, map_mul, map_units_inv,
      div_eq_iff (zpow_ne_zero _ hA0)]
    field_simp
    linear_combination e
  rw [← map_pow] at h1
  have h2 := IsFractionRing.injective V (FractionRing V) h1
  have hunit : IsUnit (ϖ ^ d) := by
    rw [h2]
    exact Units.isUnit _
  have hd0 : d = 0 := by
    by_contra hd0
    exact hϖ.not_isUnit ((isUnit_pow_iff hd0).1 hunit)
  omega

lemma hasVal_unique (hϖ : Irreducible ϖ) {c : FractionRing V} {n m : ℤ} (hn : HasVal ϖ c n)
    (hm : HasVal ϖ c m) : n = m := by
  rcases le_total m n with h | h
  · exact hasVal_eq_of_hasVal_of_le hϖ hn hm h
  · exact (hasVal_eq_of_hasVal_of_le hϖ hm hn h).symm

lemma hasVal_mul_unit {c : FractionRing V} {n : ℤ} (hn : HasVal ϖ c n) (v : Vˣ) :
    HasVal ϖ (c * algebraMap V (FractionRing V) (v : V)) n := by
  obtain ⟨u, hu⟩ := hn
  refine ⟨u * v, ?_⟩
  rw [hu, Units.val_mul, map_mul]
  ring

lemma genHasVal_units {X : Scheme.{0}} (L : LB X) {Ix : Type} [Fintype Ix]
    (φ : Ix → (Spec (CommRingCat.of V) ⟶ X)) (φ' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X))
    (hφ : ∀ k, φ' k = jK V ≫ φ k) (ε : Ix → ℤ) (t : LB.Gen (LB.LinComb L φ' ε)) {n : ℤ}
    (hn : GenHasVal ϖ L φ φ' hφ ε t n) :
    ∃ e : LB.Gen (LB.LinComb L φ ε), e.IsGen ∧ ∃ c : FractionRing V, HasVal ϖ c n ∧
      ∀ j : Ix → L.ι, ∃ C : Γ(Spec (CommRingCat.of (FractionRing V)), LB.wchart L φ' j)ˣ,
        C.val = resTop _ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) ∧
        (t.s j : Γ(Spec (CommRingCat.of (FractionRing V)), LB.wchart L φ' j)ˣ) =
          C * res (wchart_le_preimage L (jK V) φ φ' hφ j) (pullU (jK V) _ (e.s j)) := by
  obtain ⟨e, he, c, hc, h⟩ := hn
  refine ⟨e, he, c, hc, fun j => ?_⟩
  obtain ⟨y, hy⟩ : ∃ y : Γ(Spec (CommRingCat.of (FractionRing V)), LB.wchart L φ' j)ˣ, y = t.s j :=
    ⟨_, rfl⟩
  have hj := h j
  rw [← hy] at hj ⊢
  refine ⟨y * (res (wchart_le_preimage L (jK V) φ φ' hφ j) (pullU (jK V) _ (e.s j)))⁻¹, ?_, ?_⟩
  · rw [Units.val_mul, hj]
    first
      | exact Units.mul_inv_cancel_right _ _
      | simp
  · exact (inv_mul_cancel_right _ _).symm



lemma genHasVal_top {X : Scheme.{0}} (L : LB X) {Ix : Type} [Fintype Ix]
    (φ : Ix → (Spec (CommRingCat.of V) ⟶ X)) (ε : Ix → ℤ) (t : LB.Gen (LB.LinComb L (fun k => jK V ≫ φ k) ε)) {n : ℤ}
    (hn : GenHasVal ϖ L φ (fun k => jK V ≫ φ k) (fun _ => rfl) ε t n) (j₀ : Ix → L.ι)
    (htop : LB.wchart L φ j₀ = ⊤) (hK : (⊤ : (Spec (CommRingCat.of (FractionRing V))).Opens) ≤
      LB.wchart L (fun k => jK V ≫ φ k) j₀) :
    ∃ c : FractionRing V, HasVal ϖ c n ∧ ∃ eV : Vˣ,
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).hom.hom (res hK (t.s j₀)).val =
        c * algebraMap V (FractionRing V) (eV : V) := by
  obtain ⟨e, he, c, hc, hte⟩ := hn
  have hV : (⊤ : (Spec (CommRingCat.of V)).Opens) ≤ LB.wchart L φ j₀ := htop ▸ le_rfl
  set E : Γ(Spec (CommRingCat.of V), ⊤)ˣ := res hV (e.s j₀) with hE
  set eV : Vˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom.toMonoidHom E with heV
  refine ⟨c, hc, eV, ?_⟩
  have h1 := congrArg ((Spec (CommRingCat.of (FractionRing V))).presheaf.map (homOfLE hK).op).hom (hte j₀)
  erw [map_mul] at h1
  have hA : ((Spec (CommRingCat.of (FractionRing V))).presheaf.map (homOfLE hK).op).hom (t.s j₀).val =
      (res hK (t.s j₀)).val := rfl
  rw [hA] at h1
  rw [h1]
  erw [map_mul]
  congr 1
  · simp only [resTop, scal, Scheme.Hom.id_appTop, ← CommRingCat.comp_apply, ← Functor.map_comp]
    have : (homOfLE (le_top : LB.wchart L (fun k => jK V ≫ φ k) j₀ ≤ ⊤)).op ≫ (homOfLE hK).op =
        𝟙 (Opposite.op (⊤ : (Spec (CommRingCat.of (FractionRing V))).Opens)) := Subsingleton.elim _ _
    rw [Category.id_comp, ← Functor.map_comp]
    erw [this, CategoryTheory.Functor.map_id]
    simp
  · simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe, heV, hE, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe]
    have hnat := congrArg (fun f => (CommRingCat.Hom.hom f)
        (((Spec (CommRingCat.of V)).presheaf.map (homOfLE hV).op).hom (e.s j₀).val))
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V))))
    simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at hnat
    erw [← hnat]
    rw [CommRingCat.comp_apply]
    congr 1


omit [IsDiscreteValuationRing V] in
theorem isDominant_jK : IsDominant (jK V) := by
  constructor
  have hinj : Function.Injective (algebraMap V (FractionRing V)) := IsFractionRing.injective V _
  have : DenseRange (PrimeSpectrum.comap (algebraMap V (FractionRing V))) :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]
      exact bot_le)
  exact this

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

section BoxSec

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

abbrev prK (pG : IsPowGrp G' G j) (i : Fin j) : pullback G'.hom (jK R) ⟶ pullback G.hom (jK R) :=
  ((Over.pullback (jK R)).map (pG.pr i)).left

lemma prK_fst (pG : IsPowGrp G' G j) (i : Fin j) :
    prK pG i ≫ pullback.fst G.hom (jK R) = pullback.fst G'.hom (jK R) ≫ (pG.pr i).left := by
  simp only [prK, Over.pullback_map_left, pullback.lift_fst]

variable {LG : LB G.left} {LG' : LB G'.left}

lemma boxSec_le_a (pG : IsPowGrp G' G j) (jN : Fin j → LG.ι) (jL : LG'.ι) :
    pullback.fst G'.hom (jK R) ⁻¹ᵁ (LB.div (boxLB LG pG.pr) LG').U (jN, jL) ≤
      LB.wchart LG' (fun _ : Fin 1 => pullback.fst G'.hom (jK R)) (fun _ => jL) :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy.2

lemma boxSec_le_b (pG : IsPowGrp G' G j) (jN : Fin j → LG.ι) (jL : LG'.ι) (i : Fin j) :
    pullback.fst G'.hom (jK R) ⁻¹ᵁ (LB.div (boxLB LG pG.pr) LG').U (jN, jL) ≤
      prK pG i ⁻¹ᵁ LB.wchart LG (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => jN i) := by
  intro y hy
  have h := Set.mem_iInter.1 hy.1 i
  refine Set.mem_iInter.2 fun _ => ?_
  show (pullback.fst G.hom (jK R)).base ((prK pG i).base y) ∈ (LG.U (jN i) : Set G.left)
  rw [← Scheme.Hom.comp_apply, prK_fst, Scheme.Hom.comp_apply]
  exact h

def IsBoxSecK (pG : IsPowGrp G' G j) (w : LB.Iso LG' (boxLB LG pG.pr)) (k : ℕ)
    (s' : LB.Sec (LB.LinComb LG' (K := Fin 1) (fun _ => pullback.fst G'.hom (jK R))
      (fun _ => (k : ℤ))))
    (s : Fin j → LB.Sec (LB.LinComb LG (K := Fin 1) (fun _ => pullback.fst G.hom (jK R))
      (fun _ => (k : ℤ)))) : Prop :=
  ∀ (jN : Fin j → LG.ι) (jL : LG'.ι),
    ((pullU (Y := pullback G'.hom (jK R)) (pullback.fst G'.hom (jK R)) _ (w.s (jN, jL))) ^ k).val *
      ((pullback G'.hom (jK R)).presheaf.map (homOfLE (boxSec_le_a pG jN jL)).op).hom
        (s'.f (fun _ => jL)) =
    ∏ i, ((pullback G'.hom (jK R)).presheaf.map (homOfLE (boxSec_le_b pG jN jL i)).op).hom
      (((prK pG i).app _).hom ((s i).f (fun _ => jN i)))

end BoxSec

section BoxFam

lemma box_le_of_comp {X X' Y Y' : Scheme.{0}} (L : LB X) {j : ℕ} {Kx : Type} [Fintype Kx]
    (pr : Fin j → (X' ⟶ X)) (φ' : Kx → (Y' ⟶ X')) (φ : Kx → (Y ⟶ X)) (p : Y' ⟶ Y) (i : Fin j)
    (hφ : ∀ a, φ' a ≫ pr i = p ≫ φ a) (jN : Kx → Fin j → L.ι) :
    LB.wchart (LB.LinComb L pr (fun _ => 1)) φ' jN ≤ p ⁻¹ᵁ LB.wchart L φ (fun a => jN a i) := by
  intro y hy
  refine Set.mem_iInter.2 fun a => ?_
  have h1 := Set.mem_iInter.1 hy a
  have h2 := Set.mem_iInter.1 h1 i
  show (φ a).base (p.base y) ∈ (L.U (jN a i) : Set X)
  rw [← Scheme.Hom.comp_apply, ← hφ a, Scheme.Hom.comp_apply]
  exact h2

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ}

abbrev prB {D' D : DegPre R} (pD : IsPowDeg D' D j) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (i : Fin j) :
    (DegPre.BF D' F).left ⟶ (DegPre.BF D F).left :=
  (TF (R := R) F ◁ pD.pw.pr i).left

def IsBoxFam {D' D : DegPre R} (pD : IsPowDeg D' D j) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (F' : Fam D' F k) (Fs : Fin j → Fam D F k) : Prop :=
  ∀ α' : D'.X, ∃ hφ : ∀ (i : Fin j) (a : Fin 4),
      DegPre.famφ D' F α' a ≫ (pD.pw.pr i).left = prB pD F i ≫ DegPre.famφ D F (pD.xe α' i) a,
    ∀ (jN : Fin 4 → Fin j → D.P.L.ι) (jM : Fin 4 → D'.P.L.ι),
      (@id (Γ((DegPre.BF D' F).left, LB.wchart (boxLB D.P.L pD.pw.pr) (DegPre.famφ D' F α') jN ⊓
          LB.wchart D'.P.L (DegPre.famφ D' F α') jM)ˣ)
        ((LB.linCombIso pD.w (DegPre.famφ D' F α') (DegPre.famε k)).s (jN, jM))).val *
        ((DegPre.BF D' F).left.presheaf.map (homOfLE (inf_le_right :
          LB.wchart (boxLB D.P.L pD.pw.pr) (DegPre.famφ D' F α') jN ⊓
            LB.wchart D'.P.L (DegPre.famφ D' F α') jM ≤
          LB.wchart D'.P.L (DegPre.famφ D' F α') jM)).op).hom ((F'.s α').f jM) =
      ∏ i, ((DegPre.BF D' F).left.presheaf.map (homOfLE (inf_le_left.trans
          (box_le_of_comp D.P.L (fun i => (pD.pw.pr i).left) (DegPre.famφ D' F α')
            (DegPre.famφ D F (pD.xe α' i)) (prB pD F i) i (hφ i) jN) :
          LB.wchart (boxLB D.P.L pD.pw.pr) (DegPre.famφ D' F α') jN ⊓
            LB.wchart D'.P.L (DegPre.famφ D' F α') jM ≤
          prB pD F i ⁻¹ᵁ LB.wchart D.P.L (DegPre.famφ D F (pD.xe α' i)) (fun a => jN a i))).op).hom
        (((prB pD F i).app _).hom (((Fs i).s (pD.xe α' i)).f (fun a => jN a i)))

end BoxFam

section Prod

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {j : ℕ} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {pD : IsPowDeg D'.toPre D.toPre j} {pA : IsPowPolAV A' A j} {pG : IsPowGrp G' G j}
  {U' : Unif I D' A' G'} {U : Unif I D A G}

end Prod

section BoxQ

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ}

def IsBoxGtF {D' D : DegPre R} (pD : IsPowDeg D' D j) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (g' : GtPtF D' F) (g : Fin j → GtPtF D F) : Prop :=
  (∀ i, g'.b ≫ pD.pw.pr i = (g i).b) ∧
    ∀ χ' : D'.X, ∃ hψ : ∀ (i : Fin j) (a : Fin 4),
        DegPre.gtφ D' F g'.b χ' a ≫ (pD.pw.pr i).left =
          𝟙 _ ≫ DegPre.gtφ D F (g i).b (pD.xe χ' i) a,
      LB.Gen.Maps (LB.linCombIso pD.w _ DegPre.gtε) (g'.s χ')
        (GeneratorPullback.boxGen D.P.L (fun i => (pD.pw.pr i).left) _ DegPre.gtε (fun i =>
          GeneratorPullback.pullAlong D.P.L (pD.pw.pr i).left (𝟙 _) _ DegPre.gtε _ (hψ i)
            ((g i).s (pD.xe χ' i))))

def IsBoxQk {D' D : DegPre R} (pD : IsPowDeg D' D j) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (p' : QkPt D' F k) (p : Fin j → QkPt D F k) : Prop :=
  pD.xe p'.y = (fun i => (p i).y) ∧ IsBoxGtF pD F p'.g (fun i => (p i).g)

end BoxQ

section ProdMap

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {j : ℕ} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {pD : IsPowDeg D'.toPre D.toPre j} {pA : IsPowPolAV A' A j} {pG : IsPowGrp G' G j}
  {U' : Unif I D' A' G'} {U : Unif I D A G}

end ProdMap

end ReciprocityTheory.ChartRestriction.G.DVR
end
end
