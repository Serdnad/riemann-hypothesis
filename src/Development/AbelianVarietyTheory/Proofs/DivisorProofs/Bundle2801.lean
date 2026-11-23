module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle018
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRingEquiv
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle055
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Mum.RosUniq
open GlobalTheory.CechPic GlobalTheory.EndRosati

theorem pt_eq_of_cls {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB)
    (hK : KTriv A L) {R' : Type} [CommRing R'] {t : Spec (CommRingCat.of R') ⟶ S} (a b : Over.mk t ⟶ A)
    (H : pull (snd (Over.mk t) A * (fst (Over.mk t) A ≫ a)⁻¹ * (fst (Over.mk t) A ≫ b)).left (cls L hL) -
        pull (fst (Over.mk t) A ≫ b).left (cls L hL) =
      pull (snd (Over.mk t) A * (fst (Over.mk t) A ≫ a)⁻¹ * (fst (Over.mk t) A ≫ a)).left (cls L hL) -
        pull (fst (Over.mk t) A ≫ a).left (cls L hL)) : b = a := by
  let T : Over S := Over.mk t
  let x : T ⟶ A := b * a⁻¹
  have hx : lift (fst T A ≫ x) (snd T A) ≫ μ[A] = snd T A * (fst T A ≫ a)⁻¹ * (fst T A ≫ b) := by
    rw [← Hom.mul_def]
    simp only [x, MonObj.comp_mul, GrpObj.comp_inv]
    ac_rfl
  have hy : snd T A * (fst T A ≫ a)⁻¹ * (fst T A ≫ a) = snd T A := inv_mul_cancel_right _ _
  rw [hy, ← hx] at H
  have h1 : x = 1 := hK R' t x fun s => by
    obtain ⟨i, hi⟩ := exists_chart hL (a.left s)
    obtain ⟨i', hi'⟩ := exists_chart hL (b.left s)
    let V : (Spec (CommRingCat.of R')).Opens := a.left ⁻¹ᵁ L.U i ⊓ b.left ⁻¹ᵁ L.U i'
    refine ⟨V, ⟨hi, hi'⟩, ?_⟩
    have z : ∀ (c : T ⟶ A) (l : L.ι), V ≤ c.left ⁻¹ᵁ L.U l →
        pull ((fst T A).left ⁻¹ᵁ V).ι (pull (fst T A ≫ c).left (cls L hL)) = 0 := fun c l hl => by
      rw [← pull_comp]
      exact (cls_eq_zero_iff (LB.isLB_pull hL _)).2 (BoxKernel.gen_of_chart (LB.isLB_pull hL _) (fun _ => l)
        fun y => mem_pull.2 (hl y.2))
    have hT : (translDiff A L x).IsLB := LB.isLB_linComb hL _ _
    refine (cls_eq_zero_iff (LB.isLB_pull hT _)).1 ?_
    refine (cls_pull hT _ _).trans ((congrArg _ (cls_linComb hL _ _ hT)).trans ?_)
    have e : ∑ k : Fin 2, (![1, -1] : Fin 2 → ℤ) k • pull ((![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left,
        (snd T A).left] : Fin 2 → _) k) (cls L hL) =
        pull (fst T A ≫ b).left (cls L hL) - pull (fst T A ≫ a).left (cls L hL) := by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul]
      linear_combination (norm := abel) H
    refine (congrArg _ e).trans ?_
    exact (map_sub _ _ _).trans ((congrArg₂ (· - ·) (z b i' inf_le_right) (z a i inf_le_left)).trans (sub_zero _))
  exact mul_inv_eq_one.1 h1

end GlobalTheory.Mum.RosUniq


open GlobalTheory.CechPic GlobalTheory.EndRosati GlobalTheory.Mum.RosUniq in
theorem GlobalTheory.Mum.rosatiAdj_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (f g g' : D.toPre.P.A ⟶ D.toPre.P.A), IsMonHom f → IsMonHom g → IsMonHom g' → RosatiAdj D.toPre.P.A D.toPre.P.L f g → RosatiAdj D.toPre.P.A D.toPre.P.L f g' → g = g' := by
  intro R _ _ _ _ D f g g' hf hg hg' Hg Hg'
  have hGF := GlobalTheory.firstFiveLaws.1.globalFns
  obtain ⟨r, hr, -⟩ := exists_ros hGF D.toPre.P.isAb D.toPre.P.isLB f g Hg
  obtain ⟨r', hr', -⟩ := exists_ros hGF D.toPre.P.isAb D.toPre.P.isLB f g' Hg'
  have key : ∀ {T : Over (Spec (CommRingCat.of R))} (x y : T ⟶ D.toPre.P.A),
      pull (x * (y ≫ g)).left (cls _ D.toPre.P.isLB) - pull (y ≫ g).left (cls _ D.toPre.P.isLB) =
      pull (x * (y ≫ g')).left (cls _ D.toPre.P.isLB) - pull (y ≫ g').left (cls _ D.toPre.P.isLB) :=
    fun x y => by
      have h₁ := cls_of_rosati D.toPre.P.isLB r hr x y
      have h₂ := cls_of_rosati D.toPre.P.isLB r' hr' x y
      linear_combination (norm := abel) h₂ - h₁
  let cv := D.toPre.P.A.left.affineOpenCover
  refine Over.OverMorphism.ext (Scheme.Cover.hom_ext cv.openCover _ _ fun j => ?_)
  let t : Spec (CommRingCat.of (cv.X j)) ⟶ Spec (CommRingCat.of R) := cv.f j ≫ D.toPre.P.A.hom
  let y : Over.mk t ⟶ D.toPre.P.A := Over.homMk (cv.f j) rfl
  have k := key (snd (Over.mk t) D.toPre.P.A * (fst _ _ ≫ y ≫ g')⁻¹) (fst (Over.mk t) D.toPre.P.A ≫ y)
  simp only [Category.assoc] at k
  have e := pt_eq_of_cls D.toPre.P.isLB D.toPre.P.ktriv (y ≫ g') (y ≫ g) k
  exact congrArg (·.left) e
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.OriginSec

theorem isUnit_sval_iff' {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    IsUnit (sval s r z J) ↔ r z ∈ nonzeroLocus s := by
  have key : ∀ (U : Y.Opens) (_ : r z ∈ U) (f : Γ(Y, U)), IsUnit (gs r z U f) ↔ IsUnit (gs (𝟙 Y) (r z) U f) :=
    fun U h f => by rw [gs_stalkMap r z U h, isUnit_map_iff]
  refine ⟨fun h => (mem_nonzeroLocus s _).2 ⟨_, hJ.mem φ r, (key _ (hJ.mem φ r) _).1 h⟩, fun h => ?_⟩
  obtain ⟨j, hj, hu⟩ := (mem_nonzeroLocus s _).1 h
  rw [sval, sec_trans s r z (hJ.mem φ r) hj]
  exact (Units.isUnit _).mul ((key _ hj _).2 hu)

theorem c_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) : D.c 0 = η[D.P.A] := by
  have h := D.c_add 0 0
  simp only [add_zero, padd] at h
  rw [← Hom.mul_def] at h
  have : D.c 0 = 1 := by simpa using h
  rw [this, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

theorem formEq_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (k : ℕ) :
    FormEq (K := Fin 1) (fun _ => 𝟙 D.P.A.left) (fun _ => (k : ℤ)) (D.famφB 0) (DegPre.famε k) := by
  have e1 : (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ η[D.P.A])).left = 𝟙 D.P.A.left := by
    rw [padd, ← Hom.mul_def, ← Hom.one_def, _root_.mul_one]; rfl
  intro U _ h
  rw [Fin.prod_univ_four, Fin.prod_univ_one]
  simp only [DegPre.famφB, DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, c_zero, e1]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  module

end GlobalTheory.Mum.OriginSec


open GlobalTheory.Mum.OriginSec GlobalTheory.SecRingIso in
theorem GlobalTheory.Mum.exists_secB_zero_nonzero_origin : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ b : D.toPre.SecB k 0, eSec D.toPre.P.A (closedPoint R) ∈ nonzeroLocus b := by
  intro R _ _ _ _ D
  have : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  obtain ⟨n, hn, a, b, ha, hb⟩ := GlobalTheory.exists_sec_succ_of_relAmple R D.toPre.P.A D.toPre.P.L D.toPre.P.isLB
    D.toPre.P.ample (eSec D.toPre.P.A (closedPoint R))
  let Q : ℕ → Prop := fun m => ∃ d : H0 D.toPre.P.L m, eSec D.toPre.P.A (closedPoint R) ∈ nonzeroLocus d
  have hQ : ∀ m m', Q m → Q m' → Q (m + m') := fun m m' ⟨d, hd⟩ ⟨d', hd'⟩ => by
    obtain ⟨e, he⟩ := exists_mul d d'
    exact ⟨e, mem_mul he hd hd'⟩
  have hij : ∀ i j : ℕ, Q (n * (i + 1) + (n + 1) * j) := by
    intro i j
    induction j with
    | zero =>
      induction i with
      | zero => simpa using (⟨a, ha⟩ : Q n)
      | succ i ih =>
        have := hQ _ _ ih ⟨a, ha⟩
        rwa [show n * (i + 1 + 1) + (n + 1) * 0 = n * (i + 1) + (n + 1) * 0 + n by ring]
    | succ j ih =>
      have := hQ _ _ ih ⟨b, hb⟩
      rwa [show n * (i + 1) + (n + 1) * (j + 1) = n * (i + 1) + (n + 1) * j + (n + 1) by ring]
  refine ⟨n * (n + 1), fun k hk => ?_⟩
  obtain ⟨d, hd⟩ : Q k := by
    have hk' : n * (k / n) + k % n = k := Nat.div_add_mod k n
    have hr : k % n < n := Nat.mod_lt _ hn
    have hq : n + 1 ≤ k / n := (Nat.le_div_iff_mul_le hn).2 (by rw [mul_comm]; exact hk)
    obtain ⟨t, ht⟩ : ∃ t, k / n = k % n + 1 + t := ⟨k / n - k % n - 1, by omega⟩
    have e : k = n * (t + 1) + (n + 1) * (k % n) := by
      conv_lhs => rw [← hk', ht]
      ring
    rw [e]
    exact hij _ _
  obtain ⟨b', hb'⟩ := exists_sec D.toPre.P.isLB (formEq_zero D.toPre k) d
  refine ⟨b', ?_⟩
  obtain ⟨J, hJ⟩ : ∃ J, Good D.toPre.P.L (eSec D.toPre.P.A (closedPoint R)) J :=
    ⟨fun χ => (exists_chart D.toPre.P.isLB (χ (eSec D.toPre.P.A (closedPoint R)))).choose,
      fun χ => (exists_chart D.toPre.P.isLB (χ (eSec D.toPre.P.A (closedPoint R)))).choose_spec⟩
  have h1 := (isUnit_sval_iff' d (𝟙 _) _ hJ).2 hd
  rw [← hb' _ (𝟙 _) _ J hJ] at h1
  exact (isUnit_sval_iff' b' (𝟙 _) _ hJ).1 h1
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem finite_modif_eq_gp : ∀ (R : Type) [CommRing R] [IsDomain R] (M M' : Modif R) (h : M'.S ⟶ M.S), IsFinite h →
    M'.gp ≫ h = M.gp → ∀ (Z : Scheme.{0}) (a : Z ⟶ M'.S) (c : Z ⟶ Sp (FractionRing R)), a ≫ h = c ≫ M.gp →
    a = c ≫ M'.gp := by
  intro R _ _ M M' h hh e Z a c hac
  haveI := M'.integral
  have cA : ∀ {X Y W : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ W) (x : Γ(W, ⊤)),
      (f ≫ g).appTop.hom x = f.appTop.hom (g.appTop.hom x) := fun f g x => by
    rw [Scheme.Hom.comp_appTop]; rfl
  have hsub : Subsingleton (Sp (FractionRing R)) := inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
  let pt : Sp (FractionRing R) := (default : PrimeSpectrum (FractionRing R))
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (X := M.S) (U := ⊤) (x := M.gp pt) trivial
  have hgU : ∀ y : Sp (FractionRing R), M.gp y ∈ U := fun y => by rwa [Subsingleton.elim y pt]
  have hV : IsAffineOpen (h ⁻¹ᵁ U) := hU.preimage h
  have ha : Set.range a ⊆ Set.range (h ⁻¹ᵁ U).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    show h (a z) ∈ U
    rw [← Scheme.Hom.comp_apply, hac, Scheme.Hom.comp_apply]; exact hgU _
  have hg : Set.range M'.gp ⊆ Set.range (h ⁻¹ᵁ U).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    show h (M'.gp z) ∈ U
    rw [← Scheme.Hom.comp_apply, e]; exact hgU _
  obtain ⟨a₀, fa⟩ : ∃ a₀, a₀ ≫ (h ⁻¹ᵁ U).ι = a := ⟨_, IsOpenImmersion.lift_fac _ _ ha⟩
  obtain ⟨g₀, fg⟩ : ∃ g₀, g₀ ≫ (h ⁻¹ᵁ U).ι = M'.gp := ⟨_, IsOpenImmersion.lift_fac _ _ hg⟩
  suffices key : a₀ = c ≫ g₀ by rw [← fa, key, Category.assoc, fg]
  haveI : IsAffine (h ⁻¹ᵁ U) := hV
  have hq1 : a₀ ≫ ((h ⁻¹ᵁ U).ι ≫ h ≫ M.π) = c ≫ jK R := by
    rw [reassoc_of% fa, reassoc_of% hac, M.gp_π]
  have hq2 : g₀ ≫ ((h ⁻¹ᵁ U).ι ≫ h ≫ M.π) = jK R := by
    rw [reassoc_of% fg, reassoc_of% e, M.gp_π]
  have hinj : Function.Injective g₀.appTop.hom := by
    haveI : IsDominant (g₀ ≫ (h ⁻¹ᵁ U).ι) := by rw [fg]; exact M'.dominant
    haveI : IsDominant g₀ := IsDominant.of_comp_of_isOpenImmersion g₀ (h ⁻¹ᵁ U).ι
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx0
    apply eq_zero_of_basicOpen_eq_bot
    by_contra hne
    obtain ⟨y, hy⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
    obtain ⟨z, hz⟩ := g₀.denseRange.exists_mem_open (Scheme.basicOpen _ x).isOpen ⟨y, hy⟩
    have hz' : z ∈ g₀ ⁻¹ᵁ Scheme.basicOpen _ x := hz
    have hx0' : (ConcreteCategory.hom (g₀.app ⊤)) x = 0 := hx0
    rw [Scheme.preimage_basicOpen, hx0', Scheme.basicOpen_zero] at hz'
    exact hz'
  have hfrac : ∀ x : Γ(Sp (FractionRing R), ⊤), ∃ r t : Γ(Sp R, ⊤),
      IsUnit ((jK R).appTop.hom t) ∧ x * (jK R).appTop.hom t = (jK R).appTop.hom r := by
    intro x
    have nat : ∀ s, (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom ((jK R).appTop.hom s) =
        algebraMap R (FractionRing R) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom s) := fun s =>
      congrArg (fun φ => φ.hom s) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    have inj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom :=
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv.injective
    obtain ⟨r', t', ht', hx'⟩ := IsFractionRing.div_surjective (A := R)
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom x)
    have ht0 : algebraMap R (FractionRing R) t' ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht'
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r', (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom t', ?_, ?_⟩
    · have hu : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom
          ((jK R).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom t'))) := by
        rw [nat]; simpa using ht0
      have := hu.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
      simpa using this
    · apply inj
      rw [map_mul, nat, nat]
      have hi : ∀ s, (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom s) = s :=
        fun s => congrArg (fun φ => φ.hom s) (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id
      rw [hi, hi, ← hx']
      exact div_mul_cancel₀ _ ht0
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop]
  ext b
  obtain ⟨r, t, ht, hx⟩ := hfrac (g₀.appTop.hom b)
  have e1 : b * ((h ⁻¹ᵁ U).ι ≫ h ≫ M.π).appTop.hom t = ((h ⁻¹ᵁ U).ι ≫ h ≫ M.π).appTop.hom r := by
    apply hinj
    rw [map_mul, ← cA, ← cA, hq2, hx]
  have e2 := congrArg a₀.appTop.hom e1
  rw [map_mul, ← cA, ← cA, hq1, cA, cA, ← hx, map_mul] at e2
  exact (IsUnit.mul_left_inj (ht.map c.appTop.hom)).1 e2

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem jK_appTop_injective (R : Type) [CommRing R] [IsDomain R] :
    Function.Injective (jK R).appTop.hom := by
  intro a b h
  have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom h
  have h3 : ∀ x, (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom ((jK R).appTop.hom x) =
      algebraMap R (FractionRing R) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) := fun x =>
    congrArg (fun f => f.hom x) e
  rw [h3, h3] at h2
  have h4 := IsFractionRing.injective R (FractionRing R) h2
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom h4
  simpa using this

theorem Modif.gp_appTop_injective {R : Type} [CommRing R] [IsDomain R] (M : Modif R) :
    Function.Injective M.gp.appTop.hom := by
  haveI := M.integral
  haveI := M.dominant
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro s hs
  rw [← AlgebraicGeometry.basicOpen_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨y, hy⟩ := M.gp.denseRange.exists_mem_open (M.S.basicOpen s).isOpen ⟨x, hx⟩
  have : y ∈ M.gp ⁻¹ᵁ M.S.basicOpen s := hy
  rw [Scheme.preimage_basicOpen_top, hs, Scheme.basicOpen_zero] at this
  exact absurd this (by simp)

theorem Modif.appTop_comp {R : Type} [CommRing R] [IsDomain R] (M : Modif R) (a : Γ(Sp R, ⊤)) :
    M.gp.appTop.hom (M.π.appTop.hom a) = (jK R).appTop.hom a := by
  rw [← M.gp_π, Scheme.Hom.comp_appTop]
  rfl

theorem Modif.appTop_bijective_surjective : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (M : Modif R), Function.Bijective M.π.appTop.hom ∧ Surjective M.π := by
  intro R _ _ _ _ M
  haveI := M.proper
  haveI := M.integral
  have hinj : Function.Injective M.π.appTop.hom := fun a b h => jK_appTop_injective R (by
    rw [← M.appTop_comp, ← M.appTop_comp, h])
  refine ⟨⟨hinj, fun b => ?_⟩, ⟨?_⟩⟩
  ·
    obtain ⟨p, hpm, hp⟩ := isIntegral_appTop_of_universallyClosed M.π b
    let eR := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
    let eK := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv
    have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    have h3 : ∀ x, eK ((jK R).appTop.hom x) = algebraMap R (FractionRing R) (eR x) := fun x =>
      congrArg (fun f => f.hom x) e
    have hc : IsIntegral R (eK (M.gp.appTop.hom b)) := by
      refine ⟨p.map eR.toRingHom, hpm.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have : (algebraMap R (FractionRing R)).comp eR.toRingHom =
          (eK.toRingHom.comp M.gp.appTop.hom).comp M.π.appTop.hom := by
        ext x
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
        rw [M.appTop_comp, h3]
      rw [this]
      calc _ = (eK.toRingHom.comp M.gp.appTop.hom) (p.eval₂ M.π.appTop.hom b) :=
            (Polynomial.hom_eval₂ _ _ _ _).symm
        _ = 0 := by rw [hp, map_zero]
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hc
    refine ⟨eR.symm r, M.gp_appTop_injective (eK.injective ?_)⟩
    rw [M.appTop_comp, h3, RingEquiv.apply_symm_apply, hr]
  ·
    have hcl : IsClosed (Set.range M.π) := (M.π.isClosedMap).isClosed_range
    have hd : Dense (Set.range (jK R)) := (Modif.self R).dominant.denseRange
    have hsub : Set.range (jK R) ⊆ Set.range M.π := by
      rintro _ ⟨y, rfl⟩
      exact ⟨M.gp y, by rw [← Scheme.Hom.comp_apply, M.gp_π]⟩
    have := (hd.mono hsub).closure_eq
    rw [hcl.closure_eq] at this
    exact Set.range_eq_univ.1 this

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical

namespace GlobalTheory.Mum

theorem eq_gp_of_lies_over_bot {R : Type} [CommRing R] [IsDomain R] {S : Scheme.{0}} [IsReduced S] (π : S ⟶ Sp R)
    (gp : Sp (FractionRing R) ⟶ S) (hgp : gp ≫ π = jK R) (hd : IsDominant gp)
    {B : CommRingCat} (e₀ : Spec B ⟶ S) [he₀ : IsOpenImmersion e₀] (P : Spec B)
    (hP : π (e₀ P) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)) (k : Sp (FractionRing R)) : e₀ P = gp k := by
  have hsub : Set.range gp ⊆ Set.range e₀ := by
    obtain ⟨a, ha⟩ := hd.denseRange.exists_mem_open e₀.isOpenEmbedding.isOpen_range ⟨e₀ P, P, rfl⟩
    rintro _ ⟨x, rfl⟩
    rwa [Subsingleton.elim x a]
  set g' := IsOpenImmersion.lift e₀ gp hsub with hg'
  have hfac : g' ≫ e₀ = gp := IsOpenImmersion.lift_fac _ _ _
  set g := Spec.preimage g' with hg
  set ρ := Spec.preimage (e₀ ≫ π) with hρ
  have hgg : Spec.map g = g' := Spec.map_preimage _
  have hρρ : Spec.map ρ = e₀ ≫ π := Spec.map_preimage _
  have hcomp : ρ ≫ g = CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hgg, hρρ, ← Category.assoc, hfac, hgp]
  have hcomp' : ∀ r, g.hom (ρ.hom r) = algebraMap R (FractionRing R) r := fun r => by
    have := congrArg (fun f => f.hom r) hcomp
    simpa using this
  have hden : DenseRange g' := by
    rw [denseRange_iff_closure_range, e₀.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image,
      ← Set.range_comp]
    have : (e₀ ∘ g') = gp := by funext x; rw [← hfac]; rfl
    rw [this, hd.denseRange.closure_range, Set.preimage_univ]
  have hred : _root_.IsReduced B := by
    have : IsReduced (Spec B) := isReduced_of_isOpenImmersion e₀
    exact (affine_isReduced_iff B).1 this
  have hinj : Function.Injective g.hom := by
    have h1 : DenseRange (PrimeSpectrum.comap g.hom) := by rw [← hgg] at hden; exact hden
    have h2 := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical g.hom).1 h1
    rw [nilradical_eq_zero] at h2
    exact (RingHom.injective_iff_ker_eq_bot _).2 (le_bot_iff.1 h2)
  have hPρ : Ideal.comap ρ.hom P.asIdeal = ⊥ := by
    have h2 : (Spec.map ρ) P = π (e₀ P) := by rw [hρρ]; rfl
    rw [hP] at h2
    exact congrArg PrimeSpectrum.asIdeal h2
  have hPb : P.asIdeal = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, s, hs, hxs⟩ := IsFractionRing.div_surjective (A := R) (g.hom x)
    have hs0 : algebraMap R (FractionRing R) s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    have h0 : ρ.hom s * x - ρ.hom a = 0 := by
      apply hinj
      rw [map_sub, map_mul, hcomp', hcomp', ← hxs, map_zero, mul_div_cancel₀ _ hs0, sub_self]
    have ha : a ∈ Ideal.comap ρ.hom P.asIdeal := by
      rw [Ideal.mem_comap, ← sub_eq_zero.1 h0]
      exact P.asIdeal.mul_mem_left _ hx
    rw [hPρ, Ideal.mem_bot] at ha
    have hx0 : g.hom x = 0 := by rw [← hxs, ha, map_zero, zero_div]
    rw [Ideal.mem_bot]
    exact hinj (by rw [hx0, map_zero])
  rw [← hfac]
  show e₀ P = e₀ (g' k)
  congr 1
  rw [← hgg]
  apply PrimeSpectrum.ext
  show P.asIdeal = Ideal.comap g.hom k.asIdeal
  have hk : k.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ _ k.isPrime
  rw [hPb, hk, Ideal.comap_bot_of_injective _ hinj]

theorem modif_pt_over_gen : ∀ (R : Type) [CommRing R] [IsDomain R] (M' : Modif R) (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W) (ξ : Sp W ⟶ M'.S), Function.Injective φ → ξ ≫ M'.π = spMap φ → ∃ (w : Sp W) (k : Sp (FractionRing R)), ξ w = M'.gp k := by
  intro R _ _ M' W _ _ φ ξ hφ hξ
  have : IsReduced M'.S := by have := M'.integral; infer_instance
  let w : Sp W := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum W)
  let k : Sp (FractionRing R) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))
  refine ⟨w, k, ?_⟩
  let j := M'.S.affineCover.idx (ξ w)
  have hoi : IsOpenImmersion (M'.S.affineCover.f j) := M'.S.affineCover.map_prop j
  obtain ⟨P, hP⟩ := M'.S.affineCover.covers (ξ w)
  rw [← hP]
  refine eq_gp_of_lies_over_bot (he₀ := hoi) M'.π M'.gp M'.gp_π M'.dominant (M'.S.affineCover.f j) P ?_ k
  refine (congrArg M'.π hP).trans ?_
  have h1 : M'.π (ξ w) = (spMap φ) w := by rw [← hξ]; rfl
  rw [h1]
  apply PrimeSpectrum.ext
  show Ideal.comap φ ⊥ = ⊥
  exact Ideal.comap_bot_of_injective _ hφ

end GlobalTheory.Mum
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT

theorem _root_.GlobalTheory.T.rosatiAdjoint_unique_degenerationData : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (f g g' : D.toPre.P.A ⟶ D.toPre.P.A), IsMonHom f → IsMonHom g → IsMonHom g' → RosatiAdj D.toPre.P.A D.toPre.P.L f g → RosatiAdj D.toPre.P.A D.toPre.P.L f g' → g = g' := by
  first | exact @GlobalTheory.Mum.rosatiAdj_unique | exact GlobalTheory.Mum.rosatiAdj_unique | (intros; apply GlobalTheory.Mum.rosatiAdj_unique <;> assumption)

end
end
