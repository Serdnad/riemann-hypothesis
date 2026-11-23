module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotGoodClassZeroSucc
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
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MvPolynomial TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.ProjFrac

noncomputable section
namespace GlobalTheory.ZM.ProjCoord
variable {R : Type} [CommRing R] {N : ℕ} {A : Type} [CommRing A] {Y : Scheme.{0}}


theorem pt_str (c : R →+* A) (v : Fin (N + 1) → A)
    (hv : Ideal.span (Set.range v) = ⊤) : pt c v hv ≫ PSpace.str R N = spMap c := by
  rw [pt, PSpace.str, ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
  congr 1
  ext1
  exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C c v r

set_option backward.isDefEq.respectTransparency false in
theorem secCoord_iff {σ : Type} (e : σ ≃ Fin (N + 1)) (φ : Y ⟶ PSpace R N) (c : R →+* A) (x : Sp A ⟶ Y)
    (hx : (x ≫ φ) ≫ PSpace.str R N = spMap c) (v : σ → A) :
    SecCoord ((O1 R N).pull φ) (fun a => Cartier.secPull (coord R N (e a)) φ) x v ↔
      ∃ hv : Ideal.span (Set.range (v ∘ e.symm)) = ⊤, x ≫ φ = pt c (v ∘ e.symm) hv := by
  have hU : ∀ j : PUnit → PUnit → Fin (N + 1), (((O1 R N).pull φ).pull x).U j = (x ≫ φ) ⁻¹ᵁ chart R N (j ⟨⟩ ⟨⟩) := fun j => by
    rw [pull_U, pull_U]; rfl
  have hval : ∀ (l : Fin (N + 1)) (j : PUnit → PUnit → Fin (N + 1)) (h : (((O1 R N).pull φ).pull x).U j ≤ x ⁻¹ᵁ ((O1 R N).pull φ).U (j PUnit.unit)),
      (x.appLE _ _ h).hom ((Cartier.secPull (coord R N l) φ).f (j PUnit.unit)) = pullRatio (x ≫ φ) _ (j ⟨⟩ ⟨⟩) (hU j).le l := fun l j h => by
    have := resG_secPull_coord φ l (j ⟨⟩) le_rfl
    rw [resG_self] at this
    rw [this, appLE_pullRatio]
  constructor
  · rintro ⟨τ, -, H⟩
    have H' : ∀ (l i : Fin (N + 1)), pullRatio (x ≫ φ) _ i (hU fun _ _ => i).le l =
        fnOn _ (v (e.symm l)) * (show Γ(Sp A, (((O1 R N).pull φ).pull x).U fun _ _ => i) from (τ.s fun _ _ => i).val) := fun l i => by
      have := (hval _ (fun _ _ => i) _).symm.trans (H (e.symm l) (fun _ _ => i) (pull_U _ _ _).le)
      rw [Equiv.apply_symm_apply] at this
      exact this
    have hle : ∀ i, (((O1 R N).pull φ).pull x).U (fun _ _ => i) ≤ spOpen (v (e.symm i)) := fun i => by
      have h1 := H' i i
      rw [pullRatio_self] at h1
      have hu : IsUnit (fnOn ((((O1 R N).pull φ).pull x).U (fun _ _ => i)) (v (e.symm i))) := IsUnit.of_mul_eq_one _ h1.symm
      have := (Sp A).basicOpen_of_isUnit hu
      rw [basicOpen_fnOn] at this
      exact inf_eq_left.1 this
    have hcov : ∀ y : Sp A, ∃ i, y ∈ (((O1 R N).pull φ).pull x).U (fun _ _ => i) := fun y => by
      obtain ⟨i, hi⟩ := exists_mem_chart R N ((x ≫ φ) y)
      exact ⟨i, (hU _).ge hi⟩
    have hv : Ideal.span (Set.range (v ∘ e.symm)) = ⊤ := by
      refine iSup_spOpen_eq_top_iff.1 (top_le_iff.1 fun y _ => ?_)
      obtain ⟨i, hi⟩ := hcov y
      exact Opens.mem_iSup.2 ⟨i, hle i hi⟩
    refine ⟨hv, hom_ext (hx.trans (pt_str c _ hv).symm) fun y => ?_⟩
    obtain ⟨i, hi⟩ := hcov y
    have h2 := (hle i).trans (pt_preimage_chart c _ hv i).ge
    refine ⟨_, hi, i, (hU _).le, h2, fun l => ?_⟩
    have h1 := H' i i
    rw [pullRatio_self] at h1
    have h3 := pullRatio_pt_mul c _ hv i l h2
    rw [H' l i]
    simp only [Function.comp] at h3
    rw [← h3, mul_assoc, ← h1, mul_one]
  · rintro ⟨hv, hp⟩
    have hle : ∀ j : PUnit → PUnit → Fin (N + 1), (((O1 R N).pull φ).pull x).U j ≤ pt c _ hv ⁻¹ᵁ chart R N (j ⟨⟩ ⟨⟩) :=
      fun j => hp ▸ (hU j).le
    have hu : ∀ j : PUnit → PUnit → Fin (N + 1), IsUnit (fnOn ((((O1 R N).pull φ).pull x).U j) (v (e.symm (j ⟨⟩ ⟨⟩)))) := fun j =>
      isUnit_of_basicOpen_eq _ (by
        rw [basicOpen_fnOn]
        exact inf_eq_left.2 ((hle j).trans (pt_preimage_chart c _ hv _).le))
    refine ⟨⟨fun j => (hu j).unit⁻¹⟩, fun i j => ?_, fun a j h => ?_⟩
    · dsimp only
      rw [map_inv, map_inv, ← div_eq_mul_inv, eq_div_iff_mul_eq', inv_mul_eq_iff_eq_mul]
      refine Units.ext ?_
      have hW : (((O1 R N).pull φ).pull x).U i ⊓ (((O1 R N).pull φ).pull x).U j ≤ (x ≫ φ) ⁻¹ᵁ chart R N (i ⟨⟩ ⟨⟩) :=
        inf_le_left.trans (hU i).le
      have hg : ((((O1 R N).pull φ).pull x).g i j).val = pullRatio (x ≫ φ) _ (i ⟨⟩ ⟨⟩) hW (j ⟨⟩ ⟨⟩) := by
        have h1 := restrict_pullback_O1_transition φ (i ⟨⟩) (j ⟨⟩) inf_le_left inf_le_right
        rw [resG_self] at h1
        rw [pull_g]
        have hW' : (((O1 R N).pull φ).pull x).U i ⊓ (((O1 R N).pull φ).pull x).U j ≤
            x ⁻¹ᵁ (((O1 R N).pull φ).U (i ⟨⟩) ⊓ ((O1 R N).pull φ).U (j ⟨⟩)) :=
          le_inf (inf_le_left.trans (pull_U _ _ _).le) (inf_le_right.trans (pull_U _ _ _).le)
        exact (congrArg (x.appLE _ _ hW').hom h1).trans (appLE_pullRatio x hW')
      rw [Units.val_mul, hg, pullRatio_of_eq hp hW (hp ▸ hW)]
      have h3 := pullRatio_pt_mul c _ hv (i ⟨⟩ ⟨⟩) (j ⟨⟩ ⟨⟩) (hp ▸ hW)
      refine Eq.trans (resG_fnOn inf_le_right _) (h3.symm.trans ((mul_comm _ _).trans ?_))
      exact congrArg (· * _) (resG_fnOn inf_le_left _).symm
    · rw [hval, pullRatio_of_eq hp _ (hle j)]
      have h3 := pullRatio_pt_mul c _ hv (j ⟨⟩ ⟨⟩) (e a) (hle j)
      simp only [Function.comp, Equiv.symm_apply_apply] at h3
      change _ = fnOn _ (v a) * ((hu j).unit⁻¹).val
      rw [← h3, mul_assoc, IsUnit.mul_val_inv, mul_one]


omit [CommRing A] in
theorem range_comp_symm {σ τ : Type} (e : σ ≃ τ) (v : σ → A) : Set.range (v ∘ e.symm) = Set.range v :=
  e.symm.surjective.range_comp v

section
variable (K : Type) [Field K] (g n N' : ℕ) {M : ℕ} (e : Ix g (N' ^ 2) ≃ Fin (M + 1))

end

end GlobalTheory.ZM.ProjCoord
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ZM

variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

namespace DimZero
open Out.Inh GlobalTheory.ZM.Model

theorem translT_zero {T : Over S} (x : T ⟶ (zeroPolAV S).A) : (Out.translT (zeroPolAV S).A x).left = 𝟙 _ := by
  have : Out.translT (zeroPolAV S).A x = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [Out.translT]
    · exact toUnit_unique _ _
  rw [this]; rfl

theorem exists_gen {X : Scheme.{0}} (L : LB X) (hL : ∀ i j, L.g i j = 1) : ∃ t : L.Gen, t.IsGen ∧ ∀ i, t.s i = 1 :=
  ⟨⟨fun _ => 1⟩, fun i j => by
    rw [hL, _root_.one_mul]; exact (map_one _).trans (map_one _).symm, fun _ => rfl⟩

theorem corr_comm {X Y : Scheme.{0}} (L : LB X) [Unique L.ι] {K : Type} [Fintype K] (φ φ' : K → (Y ⟶ X)) (ε : K → ℤ)
    (a : LB.Gen (LB.LinComb L φ ε)) (b : LB.Gen (LB.LinComb L φ' ε)) (h h' : Y ⟶ Y) (hh : h = 𝟙 Y) (hh' : h' = 𝟙 Y)
    (c : LB.Gen (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim)) (hc : ∀ j, c.s j = 1) :
    LB.Gen.Corr L _ _ _ _ (LB.mulGen _ _ _ _ _ a (LB.pullGen _ _ _ b h))
      (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ b (LB.pullGen _ _ _ a h')) c) := by
  subst hh hh'
  intro j j' _ _ _
  obtain rfl : j = fun _ => default := Subsingleton.elim _ _
  obtain rfl : j' = fun _ => default := Subsingleton.elim _ _
  have e1 : ∀ (V W : Y.Opens) (h1 : V ≤ W) (U U' : Y.Opens) (h2 : W ≤ U) (h3 : W ≤ U') (u : Γ(Y, U)ˣ) (v : Γ(Y, U')ˣ),
      res h1 (res h2 u * res h3 v) = res (h1.trans h2) u * res (h1.trans h3) v := by
    intros; rw [map_mul, DVR.res_res', DVR.res_res']
  refine (e1 _ _ _ _ _ _ _ _ _).trans (Eq.trans ?_ (e1 _ _ _ _ _ _ _ _ _).symm)
  refine Eq.trans ?_ (congrArg₂ (· * ·) (e1 _ _ _ _ _ _ _ _ _) ((congrArg _ (hc _)).trans (map_one _))).symm
  rw [_root_.mul_one, _root_.mul_comm]
  refine congrArg₂ (· * ·) ?_ ?_
  · exact (DVR.res_res' _ _ _)
  · exact (DVR.res_res' _ _ _).symm

theorem weilIs_zero (L : LB (zeroPolAV S).A.left) [Unique L.ι] (hL : ∀ i j, L.g i j = 1) (n : ℤ) {T : Over S}
    (x y : T ⟶ (zeroPolAV S).A) : Out.WeilIs (zeroPolAV S).A L n x y 1 := by
  intro p
  have ex : ∀ z : Out.overRes (T := T) ⊤ ⟶ (zeroPolAV S).A, ∃ θ : Out.ThetaGrp _ L n _, θ.pt = z := fun z => by
    obtain ⟨t, ht, -⟩ := exists_gen (Out.thetaLB _ L n z) (linComb_g_one L hL _ _)
    exact ⟨⟨z, t, ht⟩, rfl⟩
  refine ⟨⊤, trivial, ?_, fun θx θy _ _ => ?_⟩
  · obtain ⟨θx, hx⟩ := ex (Out.overResι ⊤ ≫ x)
    obtain ⟨θy, hy⟩ := ex (Out.overResι ⊤ ≫ y)
    exact ⟨θx, θy, hx, hy⟩
  · have hc : Out.unitRes (T := T) ⊤ 1 = 1 := map_one _
    rw [hc]
    exact corr_comm L _ _ _ _ _ _ _ (translT_zero _) (translT_zero _) _
      (fun j => (congrArg _ (map_one _)).trans (map_one _))

def zeroSieg (k : ℕ) {B : Type} [CommRing B] (ζ : B) (s : S ⟶ Sp B) : SiegPre 0 k ζ s where
  A := (zeroPolAV S).A
  comm := (zeroPolAV S).isAb.comm
  ab := (zeroPolAV S).isAb
  P := trivLB _
  isLB := trivLB_isLB _
  rig₁ := (exists_gen _ (linComb_triv_g _ _)).imp fun _ h => h.1
  rig₂ := (exists_gen _ (linComb_triv_g _ _)).imp fun _ h => h.1
  symm := lbIso_of_g _ _ (fun _ _ => rfl) (linComb_triv_g _ _)
  lev := fun _ => 1
  lev_add := fun _ _ => toUnit_unique _ _
  lev_tors := fun _ => toUnit_unique _ _
  geom := fun K _ _ x β z _ _ => by
    refine ⟨fun a => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => toUnit_unique _ _⟩,
      fun _ _ => ⟨0, toUnit_unique _ _⟩, fun a a' => ?_⟩
    have h1 : unitOn (z ^ (2 * omegaStd a a')) = 1 := by
      have : omegaStd a a' = 0 := by simp [omegaStd]
      rw [this, mul_zero, zpow_zero]
      exact map_one _
    rw [h1]
    exact @weilIs_zero S _ (inferInstanceAs (Unique (PUnit → PUnit))) (linComb_triv_g _ _) _ _ _ _

theorem principal_zeroSieg (k : ℕ) {B : Type} [CommRing B] (ζ : B) (s : S ⟶ Sp B) : (zeroSieg k ζ s).Principal := by
  refine ⟨?_, fun _ _ _ => toUnit_unique _ _⟩
  generalize hM : (zeroSieg k ζ s).diag = M
  have hg : ∀ i j, M.g i j = 1 := by subst hM; exact linComb_triv_g _ _
  have hU : ∃ i, M.U i = ⊤ := by
    subst hM; exact ⟨fun _ => PUnit.unit, top_unique fun y _ => Set.mem_iInter.2 fun _ => trivial⟩
  obtain ⟨i₀, hi₀⟩ := hU
  change LB (𝟙_ (Over S)).left at M
  change Out.RelAmple (𝟙_ (Over S)) M
  intro U hU
  haveI : IsIso (𝟙_ (Over S)).hom := by show IsIso (𝟙 S); infer_instance
  let Y := ((𝟙_ (Over S)).hom ⁻¹ᵁ U).toScheme
  have hp : ∀ i j, (Out.powOver (𝟙_ (Over S)) M U 1).g i j = 1 := fun i j => by
    exact linComb_g_one M hg _ _ i j
  let s0 : LB.Sec (Out.powOver (𝟙_ (Over S)) M U 1) :=
    ⟨fun _ => 1, by
      intro i j; rw [hp, Units.val_one, _root_.one_mul]; repeat erw [map_one]
      all_goals rfl⟩
  have hD : Out.nonzeroLocus s0 = ⊤ := by
    apply top_unique
    intro x _
    simp only [Out.nonzeroLocus, s0, Scheme.basicOpen_one]
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i₀, Set.mem_iInter.2 fun _ => by
      show _ ∈ M.U i₀
      rw [hi₀]; trivial⟩
  refine ⟨1, le_rfl, 0, fun _ => s0, by simp only [iSup_const]; exact hD,
    fun _ => ⟨?_, fun _ => 1, ?_, ?_⟩⟩
  · rw [hD]
    have : IsAffine Y := hU
    exact isAffineOpen_top Y
  · intro j k
    erw [map_one]; (try erw [map_one]); (try erw [map_one]); exact (_root_.mul_one _).symm
  · intro p
    obtain ⟨a, rfl⟩ := surj_appLE ((𝟙_ (Over S)).hom ∣_ U) _ hD le_top p
    exact ⟨MvPolynomial.C a, MvPolynomial.eval₂Hom_C _ _ _⟩

end DimZero

end GlobalTheory.ZM
end
end
