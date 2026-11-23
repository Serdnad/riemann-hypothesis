module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle003
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsaRos

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
namespace GlobalTheory.UT

theorem sumV_tail {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {Ix : Type} {x : Ix → F} {s : F}
    (h : SumV v x s) (q : ℚ) (S : Finset Ix) (hS : ∀ i, i ∉ S → (q : WithTop ℚ) ≤ v (x i)) :
    (q : WithTop ℚ) ≤ v (s - ∑ i ∈ S, x i) := by
  classical
  obtain ⟨S', hS'⟩ := h q
  have h1 := hS' (S ∪ S') Finset.subset_union_right
  have h2 : (q : WithTop ℚ) ≤ v (∑ i ∈ (S ∪ S') \ S, x i) :=
    v.map_le_sum fun i hi => hS i (Finset.mem_sdiff.1 hi).2
  have h3 := Finset.sum_sdiff (f := x) (Finset.subset_union_left (s₁ := S) (s₂ := S'))
  have h4 : s - ∑ i ∈ S, x i = (s - ∑ i ∈ S ∪ S', x i) + ∑ i ∈ (S ∪ S') \ S, x i := by
    rw [← h3]; ring
  rw [h4]
  exact v.map_le_add h1 h2

theorem nullV_bdd {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {Ix : Type} {x : Ix → F}
    (h : NullV v x) : ∃ m : ℚ, ∀ i, (m : WithTop ℚ) ≤ v (x i) := by
  have hf := (h 0).image (fun i => (v (x i)).untopD 0)
  obtain ⟨m, hm⟩ := hf.bddBelow
  refine ⟨min m 0, fun i => ?_⟩
  by_cases hi : v (x i) < ((0 : ℚ) : WithTop ℚ)
  · have h1 := hm ⟨i, hi, rfl⟩
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hi)
    simp only [← hr, WithTop.untopD_coe] at h1
    rw [← hr]
    exact WithTop.coe_le_coe.2 ((min_le_left _ _).trans h1)
  · exact (WithTop.coe_le_coe.2 (min_le_right _ _)).trans (not_lt.1 hi)

theorem le_v_mul {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {x y : F} {p r q : ℚ}
    (hx : (p : WithTop ℚ) ≤ v x) (hy : (r : WithTop ℚ) ≤ v y) (h : q = p + r) : (q : WithTop ℚ) ≤ v (x * y) := by
  rw [v.map_mul, h, WithTop.coe_add]
  exact add_le_add hx hy

theorem sumV_of_convolution : ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)) (X : Type) [AddCommGroup X] (a b c : X → F), NullV v a → NullV v b → (∀ α, SumV v (fun χ => a χ * b (α - χ)) (c α)) → ∀ sb sc : F, SumV v b sb → SumV v c sc → sb ≠ 0 → SumV v a (sc / sb) := by
  classical
  intro F _ v X _ a b c ha hb hc sb sc hsb hsc h0 q
  obtain ⟨ma, hma⟩ := nullV_bdd v ha
  obtain ⟨mb, hmb⟩ := nullV_bdd v hb
  have hinv : v sb⁻¹ ≠ ⊤ := v.ne_top_iff.2 (inv_ne_zero h0)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hinv
  set q' : ℚ := q - r with hq'
  refine ⟨(ha (q' - mb)).toFinset, fun T hT => ?_⟩
  set Sb := (hb (q' - ma)).toFinset with hSb
  have hTa : ∀ χ, χ ∉ T → ((q' - mb : ℚ) : WithTop ℚ) ≤ v (a χ) := fun χ hχ =>
    not_lt.1 fun h => hχ (hT ((Set.Finite.mem_toFinset _).2 h))
  have hSb' : ∀ β, β ∉ Sb → ((q' - ma : ℚ) : WithTop ℚ) ≤ v (b β) := fun β hβ =>
    not_lt.1 fun h => hβ ((Set.Finite.mem_toFinset _).2 h)
  set U : Finset X := Finset.image₂ (· + ·) T Sb with hU
  have h1 : ∀ α, (q' : WithTop ℚ) ≤ v (c α - ∑ χ ∈ T, a χ * b (α - χ)) := fun α =>
    sumV_tail v (hc α) q' T fun χ hχ => le_v_mul v (hTa χ hχ) (hmb _) (by ring)
  have h2 : ∀ α, α ∉ U → (q' : WithTop ℚ) ≤ v (c α) := by
    intro α hα
    have : (q' : WithTop ℚ) ≤ v (∑ χ ∈ T, a χ * b (α - χ)) := by
      refine v.map_le_sum fun χ hχ => le_v_mul v (hma _) (hSb' _ fun h => hα ?_) (by ring)
      exact Finset.mem_image₂.2 ⟨χ, hχ, α - χ, h, by simp⟩
    have h3 := v.map_le_add (h1 α) this
    rwa [sub_add_cancel] at h3
  have h3 := sumV_tail v hsc q' U h2
  have h4 : (q' : WithTop ℚ) ≤ v (∑ α ∈ U, (c α - ∑ χ ∈ T, a χ * b (α - χ))) :=
    v.map_le_sum fun α _ => h1 α
  have h5 : ∀ χ ∈ T, ((q' - ma : ℚ) : WithTop ℚ) ≤ v (sb - ∑ α ∈ U, b (α - χ)) := by
    intro χ hχ
    have e : ∑ α ∈ U, b (α - χ) = ∑ β ∈ U.image (· - χ), b β :=
      (Finset.sum_image (f := b) (g := (· - χ)) fun x _ y _ h => sub_left_injective h).symm
    rw [e]
    refine sumV_tail v hsb _ _ fun β hβ => hSb' β fun h => hβ ?_
    exact Finset.mem_image.2 ⟨χ + β, Finset.mem_image₂.2 ⟨χ, hχ, β, h, rfl⟩, by simp⟩
  have h6 : (q' : WithTop ℚ) ≤ v (∑ χ ∈ T, a χ * (sb - ∑ α ∈ U, b (α - χ))) :=
    v.map_le_sum fun χ hχ => le_v_mul v (hma χ) (h5 χ hχ) (by ring)
  have h7 := v.map_le_sub (v.map_le_add h3 h4) h6
  have e : sc / sb - ∑ i ∈ T, a i =
      (sc - ∑ i ∈ U, c i + ∑ α ∈ U, (c α - ∑ χ ∈ T, a χ * b (α - χ)) -
        ∑ χ ∈ T, a χ * (sb - ∑ α ∈ U, b (α - χ))) * sb⁻¹ := by
    simp only [Finset.sum_sub_distrib, mul_sub, Finset.mul_sum, ← Finset.sum_mul]
    rw [Finset.sum_comm (s := U) (t := T)]
    field_simp
    ring
  rw [e]
  exact le_v_mul v h7 hr.le (by rw [hq']; ring)

end GlobalTheory.UT
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefBasic

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

omit [IsDomain R] in
theorem pt_eq (z z' : (TF (R := R) F).left) : z = z' :=
  Subsingleton.elim (α := PrimeSpectrum F) z z'

def cstH (z : (TF (R := R) F).left) : F →+* (TF (R := R) F).left.presheaf.stalk z :=
  ((TF (R := R) F).left.presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom

omit [IsDomain R] in
theorem cst_eq (z : (TF (R := R) F).left) (x : F) : cst F z x = cstH z x :=
  gs_eq (𝟙 _) z ⊤ trivial _

omit [IsDomain R] in
theorem cstH_surj (z : (TF (R := R) F).left) : Function.Surjective (cstH (R := R) z) := by
  intro a
  obtain ⟨U, hU, s, rfl⟩ := (TF (R := R) F).left.presheaf.germ_exist a
  obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => pt_eq z y ▸ hU
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 s
  exact ⟨x, congrArg ((TF (R := R) F).left.presheaf.germ ⊤ z trivial).hom hx⟩

omit [IsDomain R] in
theorem cstH_inj (z : (TF (R := R) F).left) : Function.Injective (cstH (R := R) z) :=
  (cstH (R := R) z).injective

omit [IsDomain R] in
theorem exists_pt : Nonempty (TF (R := R) F).left := ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F)⟩

theorem exists_good' {X Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (z : Z) : ∃ J, Good L z J := by
  choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)
  exact ⟨I, hI⟩

def trU {X Z : Scheme.{0}} (L : LB X) (z : Z) (J J' : (Z ⟶ X) → L.ι) (ψ : Z ⟶ X) : (Z.presheaf.stalk z)ˣ :=
  gm ψ z (L.U (J ψ) ⊓ L.U (J' ψ)) (L.g (J ψ) (J' ψ))

theorem val_tr {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (r : Z ⟶ Y) {z : Z} {J J'} (hJ : Good L z J) (hJ' : Good L z J') :
    val t r z J = (∏ k, trU L z J J' (r ≫ φ k) ^ ε k) * val t r z J' :=
  gen_trans ht r z (hJ.mem φ r) (hJ'.mem φ r)

theorem sval_tr {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) {z : Z} {J J'} (hJ : Good L z J) (hJ' : Good L z J') :
    sval s r z J = (∏ k, trU L z J J' (r ≫ φ k) ^ ε k).val * sval s r z J' :=
  sec_trans s r z (hJ.mem φ r) (hJ'.mem φ r)

theorem exists_gen_pt {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (y₀ : Y) (hY : ∀ y : Y, y = y₀) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) : ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  obtain ⟨J, hJ⟩ := exists_good' hL y₀
  let j₀ : K → L.ι := fun k => J (𝟙 Y ≫ φ k)
  have h₀ : ∀ y : Y, (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ j₀ := fun y => by
    rw [hY y]; exact hJ.mem φ (𝟙 Y)
  have le : ∀ j, LB.wchart L φ j ≤ LB.wchart L φ j ⊓ LB.wchart L φ j₀ := fun j y hy => ⟨hy, h₀ y⟩
  refine ⟨⟨fun j => res (le j) ((LB.LinComb L φ ε).g j j₀)⟩, fun j j' => unit_ext fun y hy => ?_⟩
  have v : ∀ j, y ∈ LB.wchart L φ j → gm (𝟙 Y) y (LB.wchart L φ j) (res (le j) ((LB.LinComb L φ ε).g j j₀)) =
      trF φ ε (𝟙 Y) y j j₀ := fun j hj =>
    (gm_res (𝟙 Y) y (le j) hj _).trans (gm_linComb L φ ε (𝟙 Y) y j j₀ hj (h₀ y))
  refine ((gm_res (𝟙 Y) y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L φ ε (𝟙 Y) y j j' hy.1 hy.2) ((gm_res (𝟙 Y) y _ hy _).trans (v j' hy.2)))).symm)
  exact (trF_trans hL φ ε (𝟙 Y) y hy.1 hy.2 (h₀ y)).symm

theorem prod_line (k : ℕ) (b : TF (R := R) F ⟶ D.P.A) {U : Type} [CommGroup U]
    (h : ((TF (R := R) F).left ⟶ D.P.A.left) → U) :
    ∏ i, h (DegPre.lineφ D F b i) ^ DegPre.lineε k i = h (1 : TF (R := R) F ⟶ D.P.A).left ^ k * (h b.left ^ k)⁻¹ := by
  rw [Fin.prod_univ_two]
  show h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h b.left ^ (-(k : ℤ)) = _
  rw [zpow_neg, zpow_natCast, zpow_natCast]

theorem isCoef_unique {k : ℕ} {g : GtPtF D F} {w : Frm D F k g.b} {χ : D.X} {s} {x y : F}
    (hx : IsCoef k g w χ s x) (hy : IsCoef k g w χ s y) : x = y := by
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB z
  have e := (hx z J hJ).trans (hy z J hJ).symm
  rw [← Units.val_pow_eq_pow_val, Units.mul_left_inj, cst_eq, cst_eq] at e
  exact cstH_inj z e

theorem coef_eq {k : ℕ} {g : GtPtF D F} {w : Frm D F k g.b} {χ : D.X} {s : Fam D F k} {x : F}
    (hx : IsCoef k g w χ (s.s χ) x) : coef s g w χ = x :=
  isCoef_unique (Classical.epsilon_spec (p := IsCoef k g w χ (s.s χ)) ⟨x, hx⟩) hx

theorem exists_isCoef {k : ℕ} (g : GtPtF D F) {w : Frm D F k g.b} (hw : w.IsGen) (χ : D.X) (s) :
    ∃ x, IsCoef k g w χ s x := by
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J', hJ'⟩ := exists_good' D.P.isLB z
  obtain ⟨x, hx⟩ := cstH_surj z (sval s (lift (𝟙 (TF (R := R) F)) g.b).left z J' * (val (g.s χ) (𝟙 _) z J').val *
    (val w (𝟙 _) z J').val * ((rigV D (TF (R := R) F).hom z J' ^ k)⁻¹).val)
  refine ⟨x, fun z' J hJ => ?_⟩
  obtain rfl := pt_eq z z'
  have a₁ := sval_tr s (lift (𝟙 (TF (R := R) F)) g.b).left hJ hJ'
  have a₂ := val_tr (g.isGen χ) (𝟙 _) hJ hJ'
  have a₃ := val_tr hw (𝟙 _) hJ hJ'
  have a₄ : rigV D (TF (R := R) F).hom z J = trU D.P.L z J J' (1 : TF (R := R) F ⟶ D.P.A).left *
      rigV D (TF (R := R) F).hom z J' := by
    refine (val_tr (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig_gen
      (TF (R := R) F).hom hJ hJ').trans ?_
    rw [Fintype.prod_unique, zpow_one]; rfl
  rw [prod_fam D F (lift (𝟙 (TF (R := R) F)) g.b) χ k (trU D.P.L z J J'), lift_snd] at a₁
  simp only [Category.id_comp] at a₂ a₃
  rw [prod_gt g.b χ (trU D.P.L z J J')] at a₂
  rw [prod_line k g.b (trU D.P.L z J J')] at a₃
  rw [cst_eq, hx, a₁, a₂, a₃, a₄, ← Units.val_pow_eq_pow_val, mul_comm (Units.val _) (sval _ _ _ _)]
  simp only [_root_.mul_assoc, ← Units.val_mul]
  congr 2
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
  module

theorem isCoef_coef {k : ℕ} (g : GtPtF D F) {w : Frm D F k g.b} (hw : w.IsGen) (χ : D.X) (s : Fam D F k) :
    IsCoef k g w χ (s.s χ) (coef s g w χ) :=
  Classical.epsilon_spec (p := IsCoef k g w χ (s.s χ)) (exists_isCoef g hw χ _)

theorem sval_lin {k : ℕ} (b : TF (R := R) F ⟶ D.P.A) (s s' : Fam D F k) (c : F) (χ : D.X) {z : (TF (R := R) F).left} {J}
    (hJ : Good D.P.L z J) : sval ((c • s + s').s χ) (lift (𝟙 (TF (R := R) F)) b).left z J =
      cst F z c * sval (s.s χ) (lift (𝟙 (TF (R := R) F)) b).left z J +
        sval (s'.s χ) (lift (𝟙 (TF (R := R) F)) b).left z J := by
  have hm := hJ.mem (DegPre.famφ D F χ) (lift (𝟙 (TF (R := R) F)) b).left
  refine (gs_add _ z _ hm _ _).trans (congrArg₂ (· + ·) ((gs_mul _ z _ hm _ _).trans (congrArg₂ (· * ·) ?_ rfl)) rfl)
  refine (gs_res _ z le_top hm _).trans ((gs_pull _ (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _).trans ?_)
  rw [← Over.comp_left, lift_fst]; rfl

theorem exists_frame_ratio {k : ℕ} {b : TF (R := R) F ⟶ D.P.A} {w w' : Frm D F k b} (hw : w.IsGen) (hw' : w'.IsGen) :
    ∃ c : F, c ≠ 0 ∧ ∀ z J, Good D.P.L z J → (val w' (𝟙 _) z J).val = cst F z c * (val w (𝟙 _) z J).val := by
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J', hJ'⟩ := exists_good' D.P.isLB z
  obtain ⟨c, hc⟩ := cstH_surj z (val w' (𝟙 _) z J' * (val w (𝟙 _) z J')⁻¹).val
  refine ⟨c, fun h => ?_, fun z' J hJ => ?_⟩
  · rw [h, map_zero] at hc
    exact Units.ne_zero _ hc.symm
  · obtain rfl := pt_eq z z'
    rw [cst_eq, hc, val_tr hw (𝟙 _) hJ hJ', val_tr hw' (𝟙 _) hJ hJ', ← Units.val_mul]
    congr 1
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem coef_basic : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (g : GtPtF D F), (∃ w : Frm D F k g.b, w.IsGen) ∧ (g.b = 1 → ∃ w : Frm D F k g.b, FrmOne w) ∧ ∀ w : Frm D F k g.b, w.IsGen → (∀ χ s, ∃! x, IsCoef k g w χ s x) ∧ (∀ (s s' : Fam D F k) (c : F) χ, coef (c • s + s') g w χ = c * coef s g w χ + coef s' g w χ) ∧ (∀ w' : Frm D F k g.b, w'.IsGen → ∃ c : F, c ≠ 0 ∧ (∀ z J, Good D.P.L z J → (val w' (𝟙 _) z J).val = cst F z c * (val w (𝟙 _) z J).val) ∧ ∀ (s : Fam D F k) χ, coef s g w' χ = c * coef s g w χ) ∧ ∀ (t : Multiplicative D.X →* Fˣ) (g₀ g' : GtPtF D F) (w' : Frm D F k g'.b), IsTor t g₀ → g.IsAdd g₀ g' → (∀ z J, Good D.P.L z J → val w' (𝟙 _) z J = val w (𝟙 _) z J) → ∀ (s : Fam D F k) χ, coef s g' w' χ = (t (Multiplicative.ofAdd χ)).val * coef s g w χ := by
  intro R _ _ D F _ _ k g
  obtain ⟨z₀⟩ := exists_pt (R := R) (F := F)
  refine ⟨exists_gen_pt D.P.isLB z₀ (fun y => pt_eq y z₀) _ _, fun hb => ?_, fun w hw => ⟨fun χ s => ?_, ?_, ?_, ?_⟩⟩
  · obtain ⟨w, hw, hv⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F g.b) (ε' := DegPre.lineε k)
      (fun U _ h => by rw [prod_line, hb, mul_inv_cancel]; exact Fintype.prod_empty _)
      (LB.oneGen D.P.L (Y := (TF (R := R) F).left))
      (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
    exact ⟨w, hw, fun z J hJ => (hv _ _ z J hJ).trans (val_one _)⟩
  · obtain ⟨x, hx⟩ := exists_isCoef g hw χ s
    exact ⟨x, hx, fun y hy => isCoef_unique hy hx⟩
  · intro s s' c χ
    refine coef_eq fun z J hJ => ?_
    have a := isCoef_coef g hw χ s z J hJ
    have a' := isCoef_coef g hw χ s' z J hJ
    rw [sval_lin g.b s s' c χ hJ]
    simp only [cst_eq, map_add (f := _), map_mul] at a a' ⊢
    linear_combination cstH z c * a + a'
  · intro w' hw'
    obtain ⟨c, hc, hv⟩ := exists_frame_ratio hw hw'
    refine ⟨c, hc, hv, fun s χ => coef_eq fun z J hJ => ?_⟩
    have a := isCoef_coef g hw χ s z J hJ
    rw [hv z J hJ]
    simp only [cst_eq, map_mul] at a ⊢
    linear_combination cstH z c * a
  · intro t g₀ g' w' ht hadd hv s χ
    obtain ⟨hb, hs⟩ := (isAdd_iff _ _ _).1 hadd
    refine coef_eq fun z J hJ => ?_
    have C : IsCub (th D (T := TF (R := R) F) z J) := isCub_cubV D.cub hJ
    have a := isCoef_coef g hw χ s z J hJ
    have e := hs χ z J hJ
    rw [ht.1, _root_.mul_one] at hb
    have e₀ : th D z J (cP D _ χ) g.b g₀.b = 1 := by rw [ht.1, C.face₃]
    rw [e₀, _root_.mul_one] at e
    have e₁ : lift (𝟙 (TF (R := R) F)) g'.b = lift (𝟙 (TF (R := R) F)) g.b := by rw [hb]
    rw [hv z J hJ, e, e₁, Units.val_mul, ht.2 χ z J hJ]
    simp only [cst_eq, map_mul] at a ⊢
    linear_combination cstH z (t (Multiplicative.ofAdd χ)).val * a

end GlobalTheory.UT.CoefBasic
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupConn

theorem connectedSpace_of_section {X S : Scheme.{0}} (f : X ⟶ S) [GeometricallyConnected f]
    [ConnectedSpace S] (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) : ConnectedSpace X := by

  have hsec : ∀ y : S, f (s y) = y := fun y => by
    simpa using congrArg (fun g : S ⟶ S => g y) hs
  obtain ⟨y₀⟩ := (inferInstance : Nonempty S)
  refine connectedSpace_iff_connectedComponent.mpr ⟨s y₀, Set.eq_univ_iff_forall.mpr fun x => ?_⟩
  have hbase : s (f x) ∈ connectedComponent (s y₀) :=
    (isPreconnected_range s.continuous).subset_connectedComponent ⟨y₀, rfl⟩ ⟨f x, rfl⟩
  have hfib : x ∈ connectedComponent (s (f x)) :=
    (f.isConnected_preimage_singleton (f x)).isPreconnected.subset_connectedComponent
      (show f (s (f x)) = f x from hsec (f x)) rfl
  rw [connectedComponent_eq hbase]
  exact hfib

theorem connectedSpace_tensor {S : Scheme.{0}} (G : Over S) [GrpObj G] [GeometricallyConnected G.hom]
    (Y : Over S) [ConnectedSpace Y.left] : ConnectedSpace (G ⊗ Y).left := by

  have : GeometricallyConnected (snd G Y).left :=
    show GeometricallyConnected (pullback.snd G.hom Y.hom) from inferInstance
  have hsec : (lift (toUnit Y ≫ η[G]) (𝟙 Y)).left ≫ (snd G Y).left = 𝟙 Y.left := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  exact connectedSpace_of_section (snd G Y).left _ hsec

theorem connectedSpace_group : ∀ (S : Scheme.{0}) [ConnectedSpace S] (G : Over S) [GrpObj G] [Smooth G.hom] [GeometricallyConnected G.hom], ConnectedSpace G.left ∧ ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] (Y : Over S), ConnectedSpace Y.left → ConnectedSpace (splitTorus S X ⊗ Y).left ∧ ConnectedSpace (G ⊗ Y).left := by
  intro S _ G _ _ _
  refine ⟨connectedSpace_of_section (S := S) (X := G.left) G.hom η[G].left (Over.w _),
    fun X _ _ Y _ => ⟨?_, connectedSpace_tensor G Y⟩⟩

  have : UniqueSums X :=
    UniqueSums.of_injective_addHom (Module.Free.chooseBasis ℤ X).repr.toAddEquiv.toAddHom
      (Module.Free.chooseBasis ℤ X).repr.injective inferInstance
  exact connectedSpace_tensor (splitTorus S X) Y

end GlobalTheory.GroupConn
end
