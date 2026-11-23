module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallinePeriodEqCechDeRhamPeriod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle917
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
public import Development.AbelianVarietyTheory.Definitions.Divisors.CechDeRhamCoefMapOneFormsRestrictAlongFunctor
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle918
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.crystalline_period_eq_cechDeRham_period : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (c : FirstDeRham (str A)) (q : u.Λ →+ ℂ) (per : u.Λ →+ Hol (fibFam u).V), (∀ l, per l = algebraMap ℂ _ (q l)) → IsPeriod (fibUnif u) c per → IsPer u.ex u.Λ (cmp1 (str A) c) q := by
  first | exact @GlobalTheory.PerLink.main | exact GlobalTheory.PerLink.main | (intros; apply GlobalTheory.PerLink.main <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_frame_factorOfAutomorphy_log : ∀ (A : Over (Sp ℂ)) [GrpObj A] {g : ℕ} (L : LB A.left) (u : HolUnif A L g) (M : LB A.left) (u' : HolUnif A M g), M.IsLB → u'.ex = u.ex → ∀ (H : Matrix (Fin g) (Fin g) ℂ) (χ : u'.Λ → ℂ), u'.IsAH H χ → ∀ (K : Charts (fibFam u)) (r : Real K (A.hom ≫ 𝟙 _) (algebraMap ℂ (Hol (fibFam u).V))), r.IsFor (fibUnif u) → ∀ (j : K.K → M.ι), (∀ k, ⊤ ≤ r.x k ⁻¹ᵁ M.U (j k)) → ∃ (fr : ∀ k, Hol (K.W k)) (a lg : u.Λ → ∀ k, Hol (K.W k)), (∀ k, IsUnit (fr k)) ∧ (∀ l k' k (h : K.le l k' k) (hh : ⊤ ≤ r.x k' ⁻¹ᵁ (M.U (j k') ⊓ M.U (j k))), fr k' = evalAt (r.x k') (M.U (j k') ⊓ M.U (j k)) hh (M.g (j k') (j k)).val * a l k' * Charts.sh h (fr k)) ∧ (∀ l k, IsUnit (a l k)) ∧ (∀ l k c, dw c (a l k) = dw c (lg l k) * a l k) ∧ (∀ l m k'' k' (h : K.le m k'' k'), a (l + m) k'' = Charts.sh h (a l k') * a m k'') ∧ (∀ l m k'' k' (h : K.le m k'' k'), Charts.sh h (lg l k') = lg l k'' + K.cst k'' (algebraMap ℂ (Hol (fibFam u).V) ((Real.pi : ℂ) * ((m : Fin g → ℂ) ⬝ᵥ H.mulVec (star (l : Fin g → ℂ)))))) ∧ (∀ l m k, lg (l + m) k = lg l k + lg m k) := by
  first | exact @GlobalTheory.AnPer.FrameFn.exists_frame_factor_log | exact GlobalTheory.AnPer.FrameFn.exists_frame_factor_log | (intros; apply GlobalTheory.AnPer.FrameFn.exists_frame_factor_log <;> assumption)
end

section

open GlobalTheory.AnPer

theorem _root_.GlobalTheory.T.periods_exist_affine_zero_section : PExist := by
  first | exact @GlobalTheory.AnPer.periods_exist | exact GlobalTheory.AnPer.periods_exist | (intros; apply GlobalTheory.AnPer.periods_exist <;> assumption)
end

section

open GlobalTheory.AnPer

theorem _root_.GlobalTheory.T.periods_of_deRham_classes_unique : PUniq := by
  first | exact @GlobalTheory.AnPer.period_unique | exact GlobalTheory.AnPer.period_unique | (intros; apply GlobalTheory.AnPer.period_unique <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SqLift

theorem dual_eq_sum_of_ker {R R₁ : Type} [CommRing R] [CommRing R₁] (ρ : R →+* R₁) {P : Type*}
    [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P] (x : Module.Dual R P)
    (hx : ∀ c, ρ (x c) = 0) :
    ∃ (n : ℕ) (j : Fin n → R) (d : Fin n → Module.Dual R P), (∀ k, ρ (j k) = 0) ∧
      x = ∑ k, j k • d k := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R P
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  refine ⟨n, fun k ↦ x (f (Pi.single k 1)), fun k ↦ (LinearMap.proj k) ∘ₗ s, fun k ↦ hx _, ?_⟩
  ext c
  have e1 : s c = ∑ k, s c k • (Pi.single k (1 : R) : Fin n → R) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  have e2 : x c = x (f (s c)) := by rw [← LinearMap.comp_apply f s, hs, LinearMap.id_apply]

  rw [e2, e1, map_sum, map_sum]
  simp [mul_comm]

theorem isAdmissible_reduce : AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A₁ : Over (Sp R₁)) [GrpObj A₁] (A : Over (Sp R)) [GrpObj A]
      (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left) (i : A₀.left ⟶ A.left)
      (h₁ : IsGrpPullback A₀ A₁ (spMap π₁) i₁) (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (h : IsGrpPullback A₀ A (spMap π) i),
      i₁ ≫ i₂ = i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ F : Submodule R (HdR A), IsAdmissible h F → ∃ F₁ : Submodule R₁ (HdR A₁), IsAdmissible h₁ F₁ ∧
      ∀ y : HdR A₁, y ∈ F₁ ↔ ∃ x ∈ F, (redMor h₂).Corr x y := by
  intro P R R₁ R₀ _ _ _ I J I₁ κ π hJ ρ κ₁ π₁ hs g A₀ _ A₁ _ A _ i₁ i₂ i h₁ h₂ h hi hA hg F hF
  obtain ⟨PF, -, PB, -, -⟩ := P
  letI : Algebra R R₁ := ρ.toAlgebra
  have hbc : (AbelianDeRham.bcMor h₂).IsBC := (PB R A g hA hg R₁ A₁ i₂ h₂).1
  obtain ⟨hfin, hproj, -⟩ := PF.prim hA hg

  have hPs : Function.Surjective (redMor h₂).pull := by
    intro c₁
    obtain ⟨z, rfl⟩ := hbc.2 c₁
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
    | tmul r c =>
      obtain ⟨r', rfl⟩ := hs.surj r
      exact ⟨r' • c, by rw [liftSemi_tmul, LinearMap.map_smulₛₗ]⟩
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩
  have hex : ∀ x : HdR A, ∃ y : HdR A₁, (redMor h₂).Corr x y := fun x ↦ hbc.exists x
  have huniq : ∀ {x : HdR A} {y y' : HdR A₁}, (redMor h₂).Corr x y → (redMor h₂).Corr x y' → y = y' := by
    intro x y y' e e'
    refine LinearMap.ext fun c₁ ↦ ?_
    obtain ⟨c, rfl⟩ := hPs c₁
    rw [e c, e' c]
  have hlift : ∀ y : HdR A₁, ∃ x : HdR A, (redMor h₂).Corr x y := by
    intro y
    let l : primDR A →ₗ[R] R₁ :=
      { toFun c := y ((redMor h₂).pull c)
        map_add' := by simp
        map_smul' r c := by rw [LinearMap.map_smulₛₗ, map_smul]; rfl }
    obtain ⟨x, hx⟩ := Module.projective_lifting_property (Algebra.linearMap R R₁) l hs.surj
    exact ⟨x, fun c ↦ (LinearMap.congr_fun hx c).symm⟩
  let S : Submodule R (HdR A) → Submodule R₁ (HdR A₁) := fun F ↦
    { carrier := {y | ∃ x ∈ F, (redMor h₂).Corr x y}
      add_mem' := by
        rintro a b ⟨x, hx, ex⟩ ⟨x', hx', ex'⟩
        exact ⟨x + x', F.add_mem hx hx', fun c ↦ by simp [ex c, ex' c]⟩
      zero_mem' := ⟨0, F.zero_mem, fun c ↦ by simp⟩
      smul_mem' := by
        rintro r₁ y ⟨x, hx, ex⟩
        obtain ⟨r, rfl⟩ := hs.surj r₁
        exact ⟨r • x, F.smul_mem r hx, fun c ↦ by simp [ex c]⟩ }
  have comp : ∀ c, (redMor h₁).pull ((redMor h₂).pull c) = (redMor h).pull c :=
    fun c ↦ GrpMor.pull_pull (redMor h₂) (redMor h₁) (redMor h) (fun r ↦ RingHom.congr_fun hs.comp r) hi c
  obtain ⟨⟨N, hN⟩, hFil⟩ := hF
  refine ⟨S F, ⟨⟨S N, ⟨?_, ?_⟩⟩, fun y ↦ ?_⟩, fun y ↦ Iff.rfl⟩
  · refine Submodule.disjoint_def.2 fun y ⟨f, hf, ef⟩ ⟨n, hn, en⟩ ↦ ?_
    have hx : ∀ c, ρ ((f - n) c) = 0 := fun c ↦ by
      rw [LinearMap.sub_apply, map_sub, ← ef c, ← en c, sub_self]
    obtain ⟨k, j, d, hj, hsum⟩ := dual_eq_sum_of_ker ρ (f - n) hx
    have hfp : f = (Submodule.linearProjOfIsCompl F N hN (f - n) : HdR A) := by
      have e1 : Submodule.linearProjOfIsCompl F N hN f = ⟨f, hf⟩ :=
        Submodule.linearProjOfIsCompl_apply_left hN ⟨f, hf⟩
      have e2 : Submodule.linearProjOfIsCompl F N hN n = 0 :=
        (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hN).2 hn
      rw [map_sub, e1, e2, sub_zero]
    refine LinearMap.ext fun c₁ ↦ ?_
    obtain ⟨c, rfl⟩ := hPs c₁
    rw [ef c, hfp, hsum]

    simp [map_sum, Submodule.coe_sum, hj]
  · refine codisjoint_iff_le_sup.2 fun y _ ↦ ?_
    obtain ⟨x, ex⟩ := hlift y
    obtain ⟨f, hf, n, hn, rfl⟩ := Submodule.mem_sup.1 (hN.sup_eq_top ▸ Submodule.mem_top : x ∈ F ⊔ N)
    obtain ⟨yf, ef⟩ := hex f
    obtain ⟨yn, en⟩ := hex n
    refine Submodule.mem_sup.2 ⟨yf, ⟨f, hf, ef⟩, yn, ⟨n, hn, en⟩, huniq (fun c ↦ ?_) ex⟩
    rw [LinearMap.add_apply, LinearMap.add_apply, ef c, en c, map_add (f := _)]
  · rw [hFil y]
    constructor
    · rintro ⟨x, hx, e⟩
      obtain ⟨x₁, e₁⟩ := hex x
      refine ⟨x₁, ⟨x, hx, e₁⟩, fun c₁ ↦ ?_⟩
      obtain ⟨c, rfl⟩ := hPs c₁
      rw [comp, e c, e₁ c]
      exact (RingHom.congr_fun hs.comp _).symm
    · rintro ⟨x₁, ⟨x, hx, e₁⟩, e⟩
      exact ⟨x, hx, fun c ↦ by rw [← comp, e, e₁ c]; exact RingHom.congr_fun hs.comp _⟩

end GlobalTheory.SqLift
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SqLift.ProdFil

variable {R : Type} [CommRing R] {I : Ideal R}

theorem left_ext {B : Scheme.{0}} {X Y : Over B} {T : Scheme.{0}} (g h : T ⟶ (X ⊗ Y).left)
    (h1 : g ≫ (fst X Y).left = h ≫ (fst X Y).left) (h2 : g ≫ (snd X Y).left = h ≫ (snd X Y).left) :
    g = h := by
  have w : h ≫ (X ⊗ Y).hom = g ≫ (X ⊗ Y).hom := by
    rw [← Over.w (fst X Y), ← Category.assoc, ← Category.assoc, h1]
  have := CartesianMonoidalCategory.hom_ext (Over.homMk g rfl : Over.mk (g ≫ (X ⊗ Y).hom) ⟶ X ⊗ Y)
    (Over.homMk h w) (Over.OverMorphism.ext (by simpa using h1)) (Over.OverMorphism.ext (by simpa using h2))
  exact congrArg (fun f => f.left) this

theorem primitive_pullback_mem_hodgeFiltration_of_monHom (κ : DividedPowers I) {S : Scheme.{0}} {t : S ⟶ Sp R} {A A' : Over S} [GrpObj A]
    [GrpObj A'] (f : A' ⟶ A) [IsMonHom f] {X X' : Over (Sp R)} {i : A.left ⟶ X.left} {i' : A'.left ⟶ X'.left}
    (w : i ≫ X.hom = A.hom ≫ t) (w' : i' ≫ X'.hom = A'.hom ≫ t) (m : X'.left ⟶ X.left) (hm : m ≫ X.hom = X'.hom)
    (e : f.left ≫ i = i' ≫ m) {c : prim κ t A} (hc : c ∈ primitiveCrystalHodgeLiftClasses κ A X i w) :
    primPull κ t f c ∈ primitiveCrystalHodgeLiftClasses κ A' X' i' w' := by
  obtain ⟨a, ha, hac⟩ := Submodule.mem_map.1 (Submodule.mem_comap.1 hc)
  have hmor : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R) (X'.hom ≫ 𝟙 _) (RingHom.id R) m :=
    IsMor.of_over (dp0 R) (by rw [← Category.assoc, hm])
  refine Submodule.mem_comap.2 (Submodule.mem_map.2 ⟨hmor.pull1 a, hmor.pullback1_mem_hodgeFiltration ha, ?_⟩)
  have hfi : IsMor (dp0 R) (X.hom ≫ 𝟙 _) κ (A'.hom ≫ t) (RingHom.id R) (f.left ≫ i) :=
    IsMor.of_dividedPowersZeroIdeal κ (by rw [Cris.spMap_id, Category.comp_id, Category.comp_id, Category.assoc, w,
      ← Category.assoc, Over.w f])
  rw [IsMor.pullback1_comp _ _ hfi (fun _ ↦ rfl) e.symm]
  change _ = (homMor κ t f).isMor.pull1 c.1
  rw [show (c : Cris.H1 κ (A.hom ≫ t)) = _ from hac.symm]
  exact (IsMor.pullback1_comp _ _ hfi (fun _ ↦ rfl) rfl a).symm

theorem schemeFil_tensor_iff : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I) (π : R →+* R₀)
    (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (X Y : Over (Sp R)) (i : A₀.left ⟶ X.left) (j : B₀.left ⟶ Y.left)
    (wi : i ≫ X.hom = A₀.hom ≫ spMap π) (wj : j ≫ Y.hom = B₀.hom ≫ spMap π)
    (e : Sp R ⟶ X.left) (e' : Sp R ⟶ Y.left), e ≫ X.hom = 𝟙 _ → e' ≫ Y.hom = 𝟙 _ →
    (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left ≫ i = spMap π ≫ e → (1 : Over.mk (𝟙 (Sp R₀)) ⟶ B₀).left ≫ j = spMap π ≫ e' →
    ∀ (l : (A₀ ⊗ B₀).left ⟶ (X ⊗ Y).left), l ≫ (fst X Y).left = (fst A₀ B₀).left ≫ i → l ≫ (snd X Y).left = (snd A₀ B₀).left ≫ j →
    ∀ (wl : l ≫ (X ⊗ Y).hom = (A₀ ⊗ B₀).hom ≫ spMap π) (d : Crys κ (spMap π) (A₀ ⊗ B₀)),
    d ∈ schemeFil κ (A₀ ⊗ B₀) (X ⊗ Y) l wl ↔
      push κ (spMap π) (fst A₀ B₀) d ∈ schemeFil κ A₀ X i wi ∧ push κ (spMap π) (snd A₀ B₀) d ∈ schemeFil κ B₀ Y j wj := by
  intro R R₀ _ _ I κ π A₀ B₀ _ _ X Y i j wi wj e e' he he' h1 h1' l hl1 hl2 wl d
  have hAB : IsMonHom (1 : A₀ ⟶ B₀) := inferInstanceAs (IsMonHom (toUnit A₀ ≫ η[B₀]))
  have hBA : IsMonHom (1 : B₀ ⟶ A₀) := inferInstanceAs (IsMonHom (toUnit B₀ ≫ η[A₀]))
  have one_left : ∀ (C D : Over (Sp R₀)) [GrpObj C] [GrpObj D],
      (1 : C ⟶ D).left = C.hom ≫ (1 : Over.mk (𝟙 (Sp R₀)) ⟶ D).left := by
    intro C D _ _
    have : (1 : C ⟶ D) = (Over.homMk C.hom (by simp) : C ⟶ Over.mk (𝟙 (Sp R₀))) ≫ 1 := by simp
    rw [this]; rfl
  constructor
  · intro H
    constructor
    · refine (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ ?_
      rw [push_apply]
      exact (Submodule.mem_dualAnnihilator _).1 H _
        (primitive_pullback_mem_hodgeFiltration_of_monHom κ (fst A₀ B₀) wi wl (fst X Y).left (Over.w _) hl1.symm hc)
    · refine (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ ?_
      rw [push_apply]
      exact (Submodule.mem_dualAnnihilator _).1 H _
        (primitive_pullback_mem_hodgeFiltration_of_monHom κ (snd A₀ B₀) wj wl (snd X Y).left (Over.w _) hl2.symm hc)
  · rintro ⟨H1, H2⟩
    refine (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ ?_
    let ι₁ : A₀ ⟶ A₀ ⊗ B₀ := lift (𝟙 A₀) 1
    let ι₂ : B₀ ⟶ A₀ ⊗ B₀ := lift 1 (𝟙 B₀)
    have hmul : (fst A₀ B₀ ≫ ι₁) * (snd A₀ B₀ ≫ ι₂) = 𝟙 _ := by
      ext
      · rw [MonObj.mul_comp]; simp [ι₁, ι₂]
      · rw [MonObj.mul_comp]; simp [ι₁, ι₂]
    have hdec : c = primPull κ _ (fst A₀ B₀) (primPull κ _ ι₁ c) + primPull κ _ (snd A₀ B₀) (primPull κ _ ι₂ c) := by
      apply Subtype.ext
      have := c.2 (A₀ ⊗ B₀) (fst A₀ B₀ ≫ ι₁) (snd A₀ B₀ ≫ ι₂)
      rw [hmul, ← pullOver_pullOver, ← pullOver_pullOver] at this
      have hid : pullOver κ (spMap π) (𝟙 (A₀ ⊗ B₀)) (c : Cris.H1 κ ((A₀ ⊗ B₀).hom ≫ spMap π)) = c :=
        IsMor.pullCohomologyOne_id _ _
      rw [← hid, this]; rfl

    let mX : X ⟶ X ⊗ Y := lift (𝟙 X) (Over.homMk (X.hom ≫ e') (by simp [he']))
    let mY : Y ⟶ X ⊗ Y := lift (Over.homMk (Y.hom ≫ e) (by simp [he])) (𝟙 Y)
    have eX : ι₁.left ≫ l = i ≫ mX.left := by
      apply left_ext
      · rw [Category.assoc, hl1, Category.assoc, ← Over.comp_left, ← Category.assoc, ← Over.comp_left]
        simp [ι₁, mX]
      · rw [Category.assoc, hl2, Category.assoc, ← Over.comp_left, ← Category.assoc, ← Over.comp_left]
        simp only [ι₁, mX, lift_snd, Over.homMk_left]
        rw [one_left, Category.assoc, h1', ← Category.assoc, ← wi, Category.assoc]
    have eY : ι₂.left ≫ l = j ≫ mY.left := by
      apply left_ext
      · rw [Category.assoc, hl1, Category.assoc, ← Over.comp_left, ← Category.assoc, ← Over.comp_left]
        simp only [ι₂, mY, lift_fst, Over.homMk_left]
        rw [one_left, Category.assoc, h1, ← Category.assoc, ← wj, Category.assoc]
      · rw [Category.assoc, hl2, Category.assoc, ← Over.comp_left, ← Category.assoc, ← Over.comp_left]
        simp [ι₂, mY]
    have k1 := primitive_pullback_mem_hodgeFiltration_of_monHom κ ι₁ wl wi mX.left (Over.w _) eX hc
    have k2 := primitive_pullback_mem_hodgeFiltration_of_monHom κ ι₂ wl wj mY.left (Over.w _) eY hc
    rw [hdec, map_add (f := _), ← push_apply κ _ (fst A₀ B₀) d, ← push_apply κ _ (snd A₀ B₀) d, (Submodule.mem_dualAnnihilator _).1 H1 _ k1,
      (Submodule.mem_dualAnnihilator _).1 H2 _ k2, add_zero]

end GlobalTheory.SqLift.ProdFil
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem crys_two_reductions : AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A₁ : Over (Sp R₁)) [GrpObj A₁] (A : Over (Sp R)) [GrpObj A]
      (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left) (i : A₀.left ⟶ A.left)
      (h₁ : IsGrpPullback A₀ A₁ (spMap π₁) i₁) (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (h : IsGrpPullback A₀ A (spMap π) i),
      i₁ ≫ i₂ = i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∃ N : GrpMor (divided₂ hJ) (spMap ρ) A₁ κ (spMap π) A₀ (RingHom.id R) (spMap π₁) i₁,
      Function.Bijective (N.pull : prim (divided₂ hJ) (spMap ρ) A₁ →ₗ[R] prim κ (spMap π) A₀) ∧
      ∀ d : Crys κ (spMap π) A₀, crysToDR κ h d = crysToDR (divided₂ hJ) h₂ ((N.pull : prim (divided₂ hJ) (spMap ρ) A₁ →ₗ[R] prim κ (spMap π) A₀).dualMap d) := by
  intro P R R₁ R₀ _ _ _ I J I₁ κ π hJ ρ κ₁ π₁ st g A₀ _ A₁ _ A _ i₁ i₂ i h₁ h₂ h e hA hg
  obtain ⟨-, -, -, PR, -⟩ := P
  have hπ : Function.Surjective π := by
    rw [← st.comp]; exact st.surj₁.comp st.surj
  have hb : spMap π₁ ≫ spMap ρ = spMap π ≫ spMap (RingHom.id R) := by
    rw [Cris.spMap_id, Category.comp_id, ← st.comp, Cris.spMap_comp]
  let N : GrpMor (divided₂ hJ) (spMap ρ) A₁ κ (spMap π) A₀ (RingHom.id R) (spMap π₁) i₁ :=
    GrpMor.of_isGrpPullback st.dpJ hb h₁
  have key : ∀ c, N.pull ((liftMor (divided₂ hJ) h₂).pull c) = (liftMor κ h).pull c := fun c ↦
    GrpMor.pull_pull (liftMor (divided₂ hJ) h₂) N (liftMor κ h) (fun _ ↦ rfl) e c
  have b := PR R A g hA hg I κ st.nil R₀ π hπ st.ker A₀ i h
  have b₂ := PR R A g hA hg J (divided₂ hJ) (isDPNilpotent_squareZero hJ) R₁ ρ st.surj st.kerJ A₁ i₂ h₂
  refine ⟨N, ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩, fun d ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := b₂.2 x
    obtain ⟨y, rfl⟩ := b₂.2 y
    have : (liftMor κ h).pull x = (liftMor κ h).pull y := by
      rw [← key, ← key]; exact hxy
    rw [b.1 this]
  · obtain ⟨c, rfl⟩ := b.2 y
    exact ⟨_, key c⟩
  · ext c
    show d ((liftMor κ h).pull c) = d (N.pull ((liftMor (divided₂ hJ) h₂).pull c))
    rw [key]

end GlobalTheory.SqLift
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem schemeFil_comp_iso (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I) (π : R →+* R₀)
    (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (σ : A₀ ⟶ B₀) [IsMonHom σ] [IsIso σ] (X : Over (Sp R)) (j : B₀.left ⟶ X.left)
    (wj : j ≫ X.hom = B₀.hom ≫ spMap π) (w : (σ.left ≫ j) ≫ X.hom = A₀.hom ≫ spMap π) (d : Crys κ (spMap π) A₀) :
    d ∈ schemeFil κ A₀ X (σ.left ≫ j) w ↔ push κ (spMap π) σ d ∈ schemeFil κ B₀ X j wj := by
  haveI : IsMonHom (inv σ) :=
    { one_hom := by rw [← cancel_mono σ]; simp
      mul_hom := by
        rw [← cancel_mono σ]
        simp only [Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, IsIso.inv_hom_id] }

  have mK : IsMor (dp0 R) (X.hom ≫ 𝟙 _) κ (A₀.hom ≫ spMap π) (RingHom.id R) (σ.left ≫ j) :=
    IsMor.of_dividedPowersZeroIdeal (s := X.hom ≫ 𝟙 _) κ (s' := A₀.hom ≫ spMap π) (σ := RingHom.id R) (φ := σ.left ≫ j)
      (by rw [Cris.spMap_id, Category.comp_id, Category.comp_id, w])
  have mJ : IsMor (dp0 R) (X.hom ≫ 𝟙 _) κ (B₀.hom ≫ spMap π) (RingHom.id R) j :=
    IsMor.of_dividedPowersZeroIdeal (s := X.hom ≫ 𝟙 _) κ (s' := B₀.hom ≫ spMap π) (σ := RingHom.id R) (φ := j)
      (by rw [Cris.spMap_id, Category.comp_id, Category.comp_id, wj])
  have key : ∀ a, (homMor κ (spMap π) σ).isMor.pull1 (mJ.pull1 a) = mK.pull1 a := fun a ↦
    IsMor.pullback1_comp _ _ _ (fun _ ↦ rfl) rfl a
  have key' : ∀ a, (homMor κ (spMap π) (inv σ)).isMor.pull1 (mK.pull1 a) = mJ.pull1 a := fun a ↦
    IsMor.pullback1_comp _ _ _ (fun _ ↦ rfl) (by rw [← Category.assoc, ← Over.comp_left, IsIso.inv_hom_id, Over.id_left,
      Category.id_comp]) a
  have back : ∀ c : prim κ (spMap π) A₀, primPull κ (spMap π) σ (primPull κ (spMap π) (inv σ) c) = c := fun c ↦ by
    refine Subtype.ext ?_
    change (homMor κ (spMap π) σ).isMor.pull1 ((homMor κ (spMap π) (inv σ)).isMor.pull1 c.1) = c.1
    rw [IsMor.pullback1_comp _ _ (IsMor.id κ (A₀.hom ≫ spMap π)) (fun _ ↦ rfl)
      (by rw [← Over.comp_left, IsIso.hom_inv_id, Over.id_left])]
    exact IsMor.pullCohomologyOne_id _ _
  simp only [schemeFil, primitiveCrystalHodgeLiftClasses, Submodule.mem_dualAnnihilator, Submodule.mem_comap, Submodule.mem_map,
    Submodule.subtype_apply, push_apply]
  constructor
  · rintro H c ⟨a, ha, e⟩
    refine H _ ⟨a, ha, ?_⟩
    change mK.pull1 a = _
    rw [← key, e]; rfl
  · rintro H c ⟨a, ha, e⟩
    have := H (primPull κ (spMap π) (inv σ) c) ⟨a, ha, ?_⟩
    · rwa [back] at this
    · change mJ.pull1 a = (homMor κ (spMap π) (inv σ)).isMor.pull1 c.1
      rw [← key', e]

end GlobalTheory.SqLift
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FilRed

theorem filtration_reduction : AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A₁ : Over (Sp R₁)) [GrpObj A₁] (A : Over (Sp R)) [GrpObj A]
      (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left) (i : A₀.left ⟶ A.left)
      (h₁ : IsGrpPullback A₀ A₁ (spMap π₁) i₁) (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (h : IsGrpPullback A₀ A (spMap π) i),
      i₁ ≫ i₂ = i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (M : GrpMor κ (spMap π) A₀ κ₁ (spMap π₁) A₀ ρ (𝟙 _) (𝟙 _)) (F : Submodule R (HdR A)) (F₁ : Submodule R₁ (HdR A₁)),
      (∀ y : HdR A₁, y ∈ F₁ ↔ ∃ x ∈ F, (redMor h₂).Corr x y) →
      (∀ d₁, crysToDR κ₁ h₁ d₁ ∈ F₁ ↔ ∃ d, crysToDR κ h d ∈ F ∧ M.Corr d d₁) ∧
      ((∀ y : HdR A₁, y ∈ Fil A₁ ↔ ∃ x ∈ Fil A, (redMor h₂).Corr x y)) := by
  intro P R R₁ R₀ _ _ _ I J I₁ κ π hJ ρ κ₁ π₁ hS g A₀ _ A₁ _ A _ i₁ i₂ i h₁ h₂ h e hA hg M F F₁ hF
  have hπ : Function.Surjective π := hS.comp ▸ hS.surj₁.comp hS.surj
  have H := canonical_of_abelianDeRham P hS.nil hπ hS.ker
  have hb := H.crysToDR_bijective h hA hg
  have hs := (H g A₀ A i h hA hg).1.2
  have e' : i₁ ≫ i₂ = 𝟙 _ ≫ i := by rw [e, Category.id_comp]
  have key : ∀ d d₁, (redMor h₂).Corr (crysToDR κ h d) (crysToDR κ₁ h₁ d₁) ↔ M.Corr d d₁ := by
    intro d d₁
    refine ⟨fun H' c' ↦ ?_, fun H' ↦ crysToDR_corr κ h h₁ M (redMor h₂) e' H'⟩
    obtain ⟨c, rfl⟩ := hs c'
    have k : GrpMor (dp0 R) (𝟙 (Sp R)) A κ₁ (spMap π₁) A₀
        (ρ.comp (RingHom.id R)) (𝟙 _ ≫ spMap π) (𝟙 _ ≫ i) := by
      let m := liftMor κ h
      refine ⟨IsDPMorphism.comp _ M.dp m.dp, ?_, ?_, ?_⟩
      · rw [Category.assoc, m.base, ← Category.assoc, M.base, Category.assoc, Cris.spMap_comp]
      · rw [Category.assoc, m.w, ← Category.assoc, M.w, Category.assoc]
      · intro T x y x₀ y₀ hx hy
        let x₁ : Over.mk (T.hom ≫ 𝟙 _) ⟶ A₀ := Over.homMk (x.left ≫ 𝟙 _) (by
          simp only [Over.mk_hom, Category.assoc]; rw [M.w, reassoc_of% (Over.w x)])
        let y₁ : Over.mk (T.hom ≫ 𝟙 _) ⟶ A₀ := Over.homMk (y.left ≫ 𝟙 _) (by
          simp only [Over.mk_hom, Category.assoc]; rw [M.w, reassoc_of% (Over.w y)])
        let x₂ : Over.mk ((Over.mk (T.hom ≫ 𝟙 _)).hom ≫ spMap π) ⟶ A := Over.homMk x₀.left (by simpa using Over.w x₀)
        let y₂ : Over.mk ((Over.mk (T.hom ≫ 𝟙 _)).hom ≫ spMap π) ⟶ A := Over.homMk y₀.left (by simpa using Over.w y₀)
        have h₁ : (x₁ * y₁).left = (x * y).left ≫ 𝟙 _ := M.mul T x y x₁ y₁ rfl rfl
        have h₂ : (x₂ * y₂).left = (x₁ * y₁).left ≫ i :=
          m.mul _ x₁ y₁ x₂ y₂ (by simp [x₂, x₁, hx]) (by simp [y₂, y₁, hy])
        have h₃ : (x₀ * y₀).left = (x₂ * y₂).left := by
          simp only [Hom.mul_def, Over.comp_left, Over.lift_left, x₂, y₂, Over.homMk_left]
        rw [h₃, h₂, h₁, Category.assoc]
    rw [GrpMor.pull_pull (liftMor κ h) M k (fun _ ↦ rfl) rfl c,
      ← GrpMor.pull_pull (redMor h₂) (liftMor κ₁ h₁) k (fun _ ↦ rfl) e' c]
    exact H' c
  refine ⟨fun d₁ ↦ ?_, (canonical_of_abelianDeRham P (isDPNilpotent_squareZero hJ) hS.surj hS.kerJ g A₁ A i₂ h₂ hA hg).2.2⟩
  rw [hF]
  constructor
  · rintro ⟨x, hx, c⟩
    obtain ⟨d, rfl⟩ := hb.2 x
    exact ⟨d, hx, (key d d₁).1 c⟩
  · rintro ⟨d, hd, c⟩
    exact ⟨_, hd, (key d d₁).2 c⟩

end GlobalTheory.FilRed
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.totalOneCochains_baseChange_bijective_finiteCategory : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → Function.Bijective (liftSemi (pullTot1 (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F'))) := by
  first | exact @GlobalTheory.liftSemi_pullTot1_bijective | exact GlobalTheory.liftSemi_pullTot1_bijective | (intros; apply GlobalTheory.liftSemi_pullTot1_bijective <;> assumption)
end
