module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3146
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2778
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2779
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle815
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2910
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2908
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3148
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle040
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2386
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1492
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3149
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3150
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.invariants_of_trivial_on_thickenings_alt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → IsGal (algebraMap R R') → ∀ (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] [Algebra.FiniteType R' C'] (act : Gal (algebraMap R R') →* (C' ≃ₐ[R] C')), (∀ σ r, act σ (algebraMap R' C' r) = algebraMap R' C' (σ.1 r)) → ∀ (O : Type) [CommRing O] [Algebra R O] [Module.Flat R O] [Algebra.FiniteType R O] (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C')), (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) → (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (act σ y) = i e x) → (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) → ∀ C : Subalgebra R C', (∀ x, x ∈ C ↔ ∀ σ, act σ x = x) → Algebra.FiniteType R C ∧ Module.Finite C C' ∧ ∃ f : C, f - 1 ∈ (maximalIdeal R).map (algebraMap R C) ∧ (∀ x : C', ∃ n : ℕ, (f : C') ^ n * x ∈ Set.range (Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _)) ∧ (∀ t : TensorProduct R C R', Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t = 0 → ∃ n : ℕ, ((f ^ n) ⊗ₜ[R] (1 : R')) * t = 0) ∧ ∀ e, Nonempty ((O ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C))) := by
  first | exact @GlobalTheory.InvAlg.invariants_of_trivial_on_thickenings | exact GlobalTheory.InvAlg.invariants_of_trivial_on_thickenings | (intros; apply GlobalTheory.InvAlg.invariants_of_trivial_on_thickenings <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_section_translate_mem_near_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (N : Near π G') (e : Sp R ⟶ N.U.left), e ≫ N.U.hom = 𝟙 _ → N.Pt (𝟙 S) (π ≫ e) (1 : Over.mk (𝟙 S) ⟶ G').left → ∀ (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (g : Over.mk s ⟶ G'), IrreducibleSpace (pullback G'.hom s : Scheme.{0}) → closedPoint R ∉ Set.range (s ≫ π) → ∃ (a : Sp R ⟶ N.U.left) (x : Over.mk (𝟙 S) ⟶ G'), a ≫ N.U.hom = 𝟙 _ ∧ N.Pt (𝟙 S) (π ≫ a) x.left ∧ Set.range (g * (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x).left ⊆ Set.range N.u := by
  first | exact @GlobalTheory.MoveNear.exists_section_translate_mem | exact GlobalTheory.MoveNear.exists_section_translate_mem | (intros; apply GlobalTheory.MoveNear.exists_section_translate_mem <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FormalAlg.TowerH1
variable {R : Type} [CommRing R] {I : Ideal R}
  {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}

theorem cst_eq_zero (e : ℕ) (V : (Y e).left.Opens) {a : R} (ha : a ∈ I ^ (e + 1)) :
    AbLaw.cst ((Y e).hom ≫ thick R I e) V a = 0 := by
  have h : (thick R I e).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) = 0 := by
    have := congrArg (fun q => q.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [← this]
    simp [Ideal.Quotient.eq_zero_iff_mem.2 ha]
  simp only [AbLaw.cst, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, h, map_zero]

theorem mul_eq_zero_of_mem (e : ℕ) (V : (Y e).left.Opens) {x y : Γ((Y e).left, V)}
    (hx : x ∈ towerIdeal Y e I V) (hy : y ∈ towerIdeal Y e (I ^ e) V) : x * y = 0 := by
  have h : x * y ∈ towerIdeal Y e (I ^ (e + 1)) V := by
    have h0 := Ideal.mul_mem_mul hx hy
    unfold towerIdeal at h0 ⊢
    rw [← Ideal.map_mul, ← pow_succ'] at h0
    exact h0
  have hb : towerIdeal Y e (I ^ (e + 1)) V = ⊥ := by
    unfold towerIdeal
    rw [Ideal.map_eq_bot_iff_le_ker]
    intro a ha
    exact cst_eq_zero e V ha
  rw [hb] at h
  exact h

theorem mul_eq_mul_of_sub_mem (e : ℕ) (V : (Y e).left.Opens) {x x' y : Γ((Y e).left, V)}
    (hx : x - x' ∈ towerIdeal Y e I V) (hy : y ∈ towerIdeal Y e (I ^ e) V) : x * y = x' * y := by
  have := mul_eq_zero_of_mem e V hx hy
  rw [sub_mul] at this
  exact sub_eq_zero.1 this

theorem pow_mul_eq_pow_mul_of_sub_mem (e : ℕ) (V : (Y e).left.Opens) {x x' y : Γ((Y e).left, V)}
    (hx : x - x' ∈ towerIdeal Y e I V) (hy : y ∈ towerIdeal Y e (I ^ e) V) (m : ℕ) :
    x ^ m * y = x' ^ m * y :=
  mul_eq_mul_of_sub_mem e V (Ideal.mem_of_dvd _ (sub_dvd_pow_sub_pow x x' m) hx) hy

theorem pow_mul_eq_of_sub_one_mem (e : ℕ) (V : (Y e).left.Opens) {x y : Γ((Y e).left, V)}
    (hx : x - 1 ∈ towerIdeal Y e I V) (hy : y ∈ towerIdeal Y e (I ^ e) V) (m : ℕ) : x ^ m * y = y := by
  rw [pow_mul_eq_pow_mul_of_sub_mem e V hx hy m, one_pow, one_mul]

theorem rs_mem (e : ℕ) (J : Ideal R) {U V : (Y e).left.Opens} (h : V ≤ U) {x : Γ((Y e).left, U)}
    (hx : x ∈ towerIdeal Y e J U) : rs (Y e).left h x ∈ towerIdeal Y e J V := by
  unfold towerIdeal at hx ⊢
  have h1 := Ideal.mem_map_of_mem (rs (Y e).left h) hx
  rw [Ideal.map_map] at h1
  have h2 : (rs (Y e).left h).comp (AbLaw.cst ((Y e).hom ≫ thick R I e) U) = AbLaw.cst ((Y e).hom ≫ thick R I e) V :=
    RingHom.ext fun r => rs_cst _ h r
  rwa [h2] at h1

theorem isUnit_rs_of_le_basicOpen {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U))
    (hb : V ≤ X.basicOpen f) : IsUnit (rs X h f) := by
  have hu : IsUnit (rs X (X.basicOpen_le f) f) := X.toRingedSpace.isUnit_res_basicOpen f
  have := hu.map (rs X hb)
  rwa [rs_rs] at this

end GlobalTheory.FormalAlg.TowerH1

namespace GlobalTheory.FormalAlg.TowerH1

theorem ev_X {R : Type} [CommRing R] {I : Ideal R}
    {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    {β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left} {n : ℕ} (C : Charts I Y β n) (e : ℕ) (i m : Fin (n + 1)) :
    C.ev e i (MvPolynomial.X m) = C.ρ e i m := by
  simp only [Charts.ev, MvPolynomial.eval₂Hom_X']

end GlobalTheory.FormalAlg.TowerH1


open GlobalTheory.FormalAlg.TowerH1 in
theorem GlobalTheory.FormalAlg.towerCech_h1_uniform : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ e : ℕ, (∀ c : ∀ i j, Γ((Y e).left, C.D e i ⊓ C.D e j), (∀ i j, c i j ∈ towerIdeal Y e (I ^ e) _) → (∀ i j l, rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i ⊓ C.D e j) (c i j) + rs (Y e).left (inf_le_left.trans inf_le_left : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i) (C.ρ e i j) ^ k * rs (Y e).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e j ⊓ C.D e l) (c j l) = rs (Y e).left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i ⊓ C.D e l) (c i l)) → ∃ a : ∀ i, Γ((Y e).left, C.D e i), (∀ i, a i ∈ towerIdeal Y e (I ^ e) _) ∧ ∀ i j, c i j = rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (a i) - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k * rs (Y e).left (inf_le_right : C.D e i ⊓ C.D e j ≤ C.D e j) (a j)) := by
  intro R _ _ I Y β hβ n C
  classical
  let J : ℕ → Ideal (MvPolynomial (Fin (n + 1)) R) := fun e => ⨅ i, RingHom.ker (C.ev e i)
  have hJ : ∀ e F, F ∈ J e ↔ ∀ i, C.ev e i F = 0 := by
    intro e F
    simp only [J, Ideal.mem_iInf, RingHom.mem_ker]
  obtain ⟨d₀, hd₀⟩ := GlobalTheory.T.uniform_serre_vanishing_cech_cocycles R I n J (fun e t a F ha _ _ hF =>
    (hJ _ _).2 fun i => GlobalTheory.T.liftedRatios_eval_ideal_mul_eq_zero_succ R I Y β hβ n C e a F i ha ((hJ e F).1 hF i))
  refine ⟨d₀, fun k hk e c hc hcoc => ?_⟩
  have lev := GlobalTheory.T.thickeningTower_liftedRatios_projective_relations R I Y β hβ n C
  choose N₀ hN₀ using fun i j => GlobalTheory.T.exists_homogeneous_form_of_overlap_ideal_pow_thickening R I Y β hβ n C e i j (c i j) (hc i j)
  let N := Finset.univ.sup (fun p : Fin (n + 1) × Fin (n + 1) => N₀ p.1 p.2)
  have hN : ∀ i j, N₀ i j ≤ N := fun i j =>
    Finset.le_sup (f := fun p : Fin (n + 1) × Fin (n + 1) => N₀ p.1 p.2) (Finset.mem_univ (i, j))
  choose F hFh hFc hFe using fun i j => hN₀ i j N (hN i j) k
  have hFm : ∀ i j, F i j ∈ Ideal.map MvPolynomial.C (I ^ e) := fun i j =>
    MvPolynomial.mem_map_C_iff.2 (hFc i j)

  have htri : ∀ i j l, ∃ L : ℕ, ((MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) * MvPolynomial.X j * MvPolynomial.X l) ^ L *
      (MvPolynomial.X l ^ N * F i j + MvPolynomial.X i ^ N * F j l - MvPolynomial.X j ^ N * F i l) ∈ J e := by
    intro i j l
    have hH : (MvPolynomial.X l ^ N * F i j + MvPolynomial.X i ^ N * F j l - MvPolynomial.X j ^ N * F i l :
        MvPolynomial (Fin (n + 1)) R).IsHomogeneous (N + (k + 2 * N)) :=
      (((MvPolynomial.isHomogeneous_X_pow l N).mul (hFh i j)).add
        ((MvPolynomial.isHomogeneous_X_pow i N).mul (hFh j l))).sub
        ((MvPolynomial.isHomogeneous_X_pow j N).mul (hFh i l))
    have hHc : ∀ m, AddMonoidAlgebra.coeff (MvPolynomial.X l ^ N * F i j + MvPolynomial.X i ^ N * F j l -
        MvPolynomial.X j ^ N * F i l : MvPolynomial (Fin (n + 1)) R) m ∈ I ^ e :=
      MvPolynomial.mem_map_C_iff.1 (sub_mem (add_mem (Ideal.mul_mem_left _ _ (hFm i j))
        (Ideal.mul_mem_left _ _ (hFm j l))) (Ideal.mul_mem_left _ _ (hFm i l)))

    have hTij : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i ⊓ C.D e j := inf_le_left
    have hTil : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i ⊓ C.D e l := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hTjl : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e j ⊓ C.D e l := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have hTi : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i := inf_le_left.trans inf_le_left
    have hTj : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e j := inf_le_left.trans inf_le_right
    have h1 : rs (Y e).left hTi (C.ev e i (F i j)) =
        rs (Y e).left hTi (C.ρ e i j) ^ N * rs (Y e).left hTij (c i j) := by
      have := congrArg (rs (Y e).left hTij) (hFe i j)
      simpa only [rs_rs, map_mul, map_pow] using this
    have h3 : rs (Y e).left hTi (C.ev e i (F i l)) =
        rs (Y e).left hTi (C.ρ e i l) ^ N * rs (Y e).left hTil (c i l) := by
      have := congrArg (rs (Y e).left hTil) (hFe i l)
      simpa only [rs_rs, map_mul, map_pow] using this
    have h2 : rs (Y e).left hTi (C.ev e i (F j l)) =
        rs (Y e).left hTi (C.ρ e i j) ^ (k + 2 * N) * (rs (Y e).left hTj (C.ρ e j l) ^ N *
          rs (Y e).left hTjl (c j l)) := by
      have t1 := congrArg (rs (Y e).left hTij)
        (GlobalTheory.T.homogeneousForm_chart_change_coeff_ideal_pow R I Y β hβ n C e (k + 2 * N) (F j l) (hFh j l) (hFc j l) i j).2.2
      have t2 := congrArg (rs (Y e).left hTjl) (hFe j l)
      simp only [rs_rs, map_mul, map_pow] at t1 t2
      rw [t1, t2]
    have hcjl : rs (Y e).left hTjl (c j l) ∈ towerIdeal Y e (I ^ e) _ := rs_mem e _ hTjl (hc j l)
    have hP : rs (Y e).left hTi (C.ρ e i i) - 1 ∈ towerIdeal Y e I _ := by
      have := rs_mem e I hTi (lev.2.1 e i)
      rwa [map_sub, map_one] at this
    have hB : rs (Y e).left hTi (C.ρ e i l) - rs (Y e).left hTi (C.ρ e i j) * rs (Y e).left hTj (C.ρ e j l)
        ∈ towerIdeal Y e I _ := by
      have := rs_mem e I hTij (lev.2.2 e i j l)
      simpa only [map_sub, map_mul, rs_rs] using this
    have e1 := pow_mul_eq_of_sub_one_mem e _ hP hcjl N
    have e2 := pow_mul_eq_pow_mul_of_sub_mem e _ hB hcjl N
    have hyp := hcoc i j l
    have hz : rs (Y e).left hTi (C.ev e i (MvPolynomial.X l ^ N * F i j + MvPolynomial.X i ^ N * F j l -
        MvPolynomial.X j ^ N * F i l)) = 0 := by
      simp only [map_add (f := _), map_sub, map_mul, map_pow, ev_X]
      rw [h1, h2, h3]
      linear_combination (rs (Y e).left hTi (C.ρ e i j) ^ (k + 2 * N) * rs (Y e).left hTj (C.ρ e j l) ^ N) * e1 -
        rs (Y e).left hTi (C.ρ e i j) ^ (k + N) * e2 +
        rs (Y e).left hTi (C.ρ e i j) ^ N * rs (Y e).left hTi (C.ρ e i l) ^ N * hyp
    obtain ⟨L, hL⟩ := GlobalTheory.T.homogeneousForm_killed_by_power_of_tripleChart_product R I Y β hβ n C e _ _ hH hHc i j l hz
    exact ⟨L, (hJ _ _).2 hL⟩

  obtain ⟨N', G, hGh, hGc, hrel⟩ := hd₀ k hk e N F hFh hFc htri
  have tr := fun i j => GlobalTheory.T.homogeneousForm_chart_change_coeff_ideal_pow R I Y β hβ n C e (k + N') (G j) (hGh j) (hGc j) i j
  refine ⟨fun i => C.ev e i (G i), fun i => (tr i i).1, fun i j => ?_⟩
  obtain ⟨L, hL⟩ := hrel i j
  have hl : C.D e i ⊓ C.D e j ≤ C.D e i := inf_le_left
  have hr : C.D e i ⊓ C.D e j ≤ C.D e j := inf_le_right
  have h0 := congrArg (rs (Y e).left hl) ((hJ _ _).1 hL i)
  simp only [map_mul, map_sub, map_pow, ev_X, map_zero] at h0
  rw [hFe i j, (tr i j).2.2] at h0
  have hci := hc i j
  have hai : rs (Y e).left hl (C.ev e i (G i)) ∈ towerIdeal Y e (I ^ e) _ := rs_mem e _ hl (tr i i).1
  have haj : rs (Y e).left hr (C.ev e j (G j)) ∈ towerIdeal Y e (I ^ e) _ := rs_mem e _ hr (tr j j).1
  have hP : rs (Y e).left hl (C.ρ e i i) - 1 ∈ towerIdeal Y e I _ := by
    have := rs_mem e I hl (lev.2.1 e i)
    rwa [map_sub, map_one] at this
  have ec := pow_mul_eq_of_sub_one_mem e _ hP hci (L + N')
  have ea := pow_mul_eq_of_sub_one_mem e _ hP hai (L + N)
  have eb := pow_mul_eq_of_sub_one_mem e _ hP haj (L + N + N')
  have hu : IsUnit (rs (Y e).left hl (C.ρ e i j) ^ (L + N + N')) :=
    (isUnit_rs_of_le_basicOpen hl _ (lev.1 e i j).ge).pow _
  have hw : rs (Y e).left hl (C.ρ e i j) ^ (L + N + N') * (c i j - (rs (Y e).left hl (C.ev e i (G i)) -
      rs (Y e).left hl (C.ρ e i j) ^ k * rs (Y e).left hr (C.ev e j (G j)))) = 0 := by
    linear_combination h0 - rs (Y e).left hl (C.ρ e i j) ^ (L + N + N') * ec +
      rs (Y e).left hl (C.ρ e i j) ^ (L + N + N') * ea -
      rs (Y e).left hl (C.ρ e i j) ^ (L + N + N' + k) * eb
  exact sub_eq_zero.1 ((hu.mul_right_eq_zero).1 hw)
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem GlobalTheory.TwFam.exists_prod_family : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (n j n' j' n'' j'' : ℤ), n'' = n + n' → j'' = j + j' → ∀ (f : ∀ β, SecT D.toPre a n j β) (g : ∀ β, SecT D.toPre a n' j' β), Small (maximalIdeal R) (w := id) f → Small (maximalIdeal R) (w := id) g → TFE h h' f → TFE h h' g → ∃ F : ∀ β, SecT D.toPre a n'' j'' β, Small (maximalIdeal R) (w := id) F ∧ TFE h h' F ∧ ∀ (e : ℕ) (τ : SecE U.toUnifPre (b e) n j) (τ' : SecE U.toUnifPre (b e) n' j'), TExp U.toUnifPre τ (w := id) f → TExp U.toUnifPre τ' (w := id) g → ∃ τ'' : SecE U.toUnifPre (b e) n'' j'', (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ'' x z J' = sval τ x z J' * sval τ' x z J') ∧ TExp U.toUnifPre τ'' (w := id) F := by
  intro R _ _ _ hadm D a a' h h' hED A G _ _ hG U b hb n j n' j' n'' j'' hn hj f g hfs hgs hf hg
  have hP := GlobalTheory.T.exists_cubeProduct_twistedSections_vanishing R hadm D a n j n' j' n'' j'' hn hj
  choose p hpP hpV using fun q : D.toPre.X × D.toPre.X => hP q.1 q.2 (f q.1) (g q.2)
  have hps : Small (maximalIdeal R) (w := fun q : D.toPre.X × D.toPre.X => q.1 + q.2) p := by
    intro e
    refine ((hfs e).prod (hgs e)).subset ?_
    intro q hq
    by_contra hc
    simp only [Set.mem_prod, Set.mem_setOf_eq, not_and_or, not_not] at hc
    exact hq (hpV q e hc)
  obtain ⟨F, hFs, hFsm⟩ := GlobalTheory.T.exists_adicSum_twistedSectionFamily_tendsToZero R hadm D a n'' j'' (D.toPre.X × D.toPre.X) (fun q => q.1 + q.2) p hps
  refine ⟨F, hFsm, ?_, ?_⟩
  · let σ : D.toPre.X → (D.toPre.X × D.toPre.X) ≃ (D.toPre.X × D.toPre.X) := fun mu =>
      Equiv.prodCongr (Equiv.addRight (shift h h' n j mu)) (Equiv.addRight (shift h h' n' j' mu))
    have hσw : ∀ mu q, (σ mu q).1 + (σ mu q).2 = q.1 + q.2 + shift h h' n'' j'' mu := by
      intro mu q
      subst hn hj
      simp only [σ, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.coe_addRight, shift, add_smul]
      abel
    have hσr : ∀ (mu : D.toPre.X) (q : D.toPre.X × D.toPre.X), TRel h mu (p q) (p (σ mu q)) := fun mu q =>
      GlobalTheory.T.twistedRelation_mul_of_related_pairs R hadm D a a' h h' hED n j n' j' n'' j'' hn hj mu q.1 q.2 (σ mu q).1 (σ mu q).2
        (f q.1) (g q.2) (p q) (f _) (g _) (p (σ mu q)) rfl rfl (hpP q) (hpP (σ mu q)) (hf mu q.1) (hg mu q.2)
    exact GlobalTheory.T.twistedFunctionalEquation_of_adicSum_termwise R hadm D a a' h h' hED n'' j'' (D.toPre.X × D.toPre.X) (fun q => q.1 + q.2) p F σ
      hps hFs hσw hσr
  · intro e τ τ' hτ hτ'
    have hform : FormEq
        (Sum.elim ![(fstG (maximalIdeal R) e G).left, (b e).left ≫ (fstG (maximalIdeal R) e G).left]
          ![(fstG (maximalIdeal R) e G).left, (b e).left ≫ (fstG (maximalIdeal R) e G).left])
        (Sum.elim ![n, j] ![n', j'])
        ![(fstG (maximalIdeal R) e G).left, (b e).left ≫ (fstG (maximalIdeal R) e G).left] ![n'', j''] := by
      intro V _ k
      rw [Fintype.prod_sum_type]
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Sum.elim_inl,
        Sum.elim_inr, hn, hj, zpow_add]
      exact mul_mul_mul_comm _ _ _ _
    obtain ⟨τ'', hτ''⟩ := exists_sec U.LG.isLB hform (H1.SectionArithmetic.mulSec τ τ')
    have hmul : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'),
        Good U.LG.L z J' → sval τ'' x z J' = sval τ x z J' * sval τ' x z J' := fun Z x z J' hJ =>
      (hτ'' Z x z J' hJ).trans (H1.SectionArithmetic.sval_mulSec τ τ' x z hJ)
    exact ⟨τ'', hmul, GlobalTheory.T.twistedExpansion_adicSums_admissibleBase R hadm D a A G hG U e (b e) n'' j'' τ'' (D.toPre.X × D.toPre.X)
      (fun q => q.1 + q.2) p F hps hFs
      (GlobalTheory.T.twistedExpansion_mul_of_memberProducts R hadm D a A G hG U e (b e) n j n' j' n'' j'' hn hj f g p τ τ' τ'' hfs hgs hpP hτ hτ' hmul)⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

theorem exists_pull_expansion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (k : ℕ) (σ : H0 U.LG.L k) (f : IntFam (maximalIdeal R) D.toPre k), (∀ e, U.ExpandsAt e k σ f.f) → ∃ ρ : ∀ β, SecT D.toPre a 0 k β, Small (maximalIdeal R) (w := id) ρ ∧ TFE h h' ρ ∧ ∀ e, ∃ τ : SecE U.toUnifPre (b e) 0 k, (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ x z J' = sval σ (x ≫ (b e).left ≫ (fstG (maximalIdeal R) e G).left) z J') ∧ TExp U.toUnifPre τ (w := id) ρ := by
  intro R _ _ _ hR D a a' h h' hE A G _ _ hG U b hb k σ f hσ
  choose u hu using GlobalTheory.T.exists_normalisedTwistedIotaGenerator R hR D a a' h h' hE
  choose s hs hv using fun α => GlobalTheory.T.exists_pullbackTwistedSection_vanishing R hR D a k α (h' α) (u α) (f.f α) (hu α).1
  have hsm : Small (maximalIdeal R) (w := fun α => h' α) s := fun e =>
    (f.small e).subset fun α hα hf => hα (hv α e hf)
  obtain ⟨ρ, hρ, hρs⟩ := GlobalTheory.T.exists_adicSum_twistedSectionFamily_tendsToZero R hR D a 0 k _ (fun α => h' α) s hsm
  refine ⟨ρ, hρs, GlobalTheory.T.twistedFunctionalEquation_of_adicSum_termwise R hR D a a' h h' hE 0 k _ (fun α => h' α) s ρ
    (fun mu => Equiv.addRight (k • h mu)) hsm hρ (fun mu i => by simp [shift])
    (fun mu i => GlobalTheory.T.twistedRelation_pullback_of_integralThetaFunctionalEquation R hR D a a' h h' hE k f mu i _ _ _ _ (hu _) (hu _) (hs _) (hs _)), fun e => ?_⟩
  have hL : U.LG.L.IsLB := U.LG.isLB
  have h1 : (LB.oneGen U.LG.L (Y := (thickObj R (maximalIdeal R) e G).left)).IsGen := fun _ _ =>
    (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm
  obtain ⟨τ, hτ⟩ := exists_sec hL (K' := Fin 2)
    (φ' := ![(fstG (maximalIdeal R) e G).left, (b e).left ≫ (fstG (maximalIdeal R) e G).left]) (ε' := ![(0 : ℤ), (k : ℤ)])
    (fun V _ g => by simp [Fintype.prod_sum_type, Fin.prod_univ_two])
    (pullMulSec σ ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (LB.oneGen U.LG.L) h1)
  have key : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' →
      sval τ x z J' = sval σ (x ≫ (b e).left ≫ (fstG (maximalIdeal R) e G).left) z J' := fun Z x z J hJ => by
    rw [hτ Z x z J hJ, sval_pullMulSec _ _ _ _ _ _ hJ, val_one, Units.val_one, _root_.mul_one]
  exact ⟨τ, key, GlobalTheory.T.twistedExpansion_adicSums_admissibleBase R hR D a A G hG U e (b e) 0 k τ _ (fun α => h' α) s ρ hsm hρ
    (GlobalTheory.T.expansion_pullback_formal_endomorphism_termwise R hR D a a' h h' hE A G hG U b hb k e σ f.f u s τ (hσ e) hu hs key)⟩

end GlobalTheory.TwFam
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hasProperSmoothDualRepresentative_noetherian_induction : ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (∀ J : Ideal R, J ≠ ⊥ → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk J)))) → HasRep A g (𝟙_ _) := by
  first | exact @GlobalTheory.DualCon.Step.step | exact GlobalTheory.DualCon.Step.step | (intros; apply GlobalTheory.DualCon.Step.step <;> assumption)
end

section


open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.FlatCore

namespace GlobalTheory.DefCoreLie

theorem frameDeg_def (hCM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : GlobalTheory.CM.CMObj H K ρ σ₁ p q) (F : GlobalTheory.CM.GenFib X.B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → q = 0 → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat X.B.t.act τ) - ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat X.B.t.act (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) = ((p : ℝ) - q) / 2 * (GlobalTheory.CM.logOm E χ).re) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (hH : GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H) [NeZero H.d] (χ : DirichletCharacter ℂ H.d) (hχ : GlobalTheory.IsKroneckerChar χ)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)
    (hL : Laws U x) (hq : Dw.q = 0) : FrameDeg U x (GlobalTheory.CM.logOm E χ).re := by
  intro Z τ s ρ hρ
  obtain ⟨K, iF, iN, iA, y, ρ₀, σ₁, X, t₀, hy, hm₁, hm₂, hρ₀⟩ := GlobalTheory.T.exists_cm_goodReduction_point_on_component E H Dw l Xo c r U x hL Z
  obtain ⟨F⟩ := GlobalTheory.CM.GenFib.nonempty_of_baseChange GlobalTheory.polBaseChange_holds K X.B.pol
  obtain ⟨⟨h, hh⟩, -⟩ :=
    GlobalTheory.CM.LieMetric.exists_unique_isHerm GlobalTheory.thetaUnifAV_all GlobalTheory.abelianSchemeLaws_all.1 K X.B.pol F
  let f : 𝓞 E →+* K := (algebraMap c.F K).comp (embK c τ.1)
  have hf : ∀ a, IsIntegral ℤ (f a) := fun a =>
    (Algebra.IsIntegral.isIntegral (R := ℤ) a).map f.toIntAlgHom
  let t : 𝓞 E →+* 𝓞 K := f.codRestrict (integralClosure ℤ K).toSubring hf
  have ht : ∀ a, ((t a : 𝓞 K) : K) = algebraMap c.F K (embK c τ.1 a) := fun a => rfl
  obtain ⟨hfin, hdeg⟩ := GlobalTheory.T.flatLineDegree_eq_eigenLattice_degree_sub E H Dw l Xo c r U x hL Z τ s ρ hρ K y hy X.B t₀ hm₁ hm₂ F h hh t ht
  have htρ : t H.rt = ρ₀ := by
    apply RingOfIntegers.ext
    rw [ht, hρ₀ τ]
  exact ⟨hfin, hdeg.trans (hCM E H hH χ hχ K ρ₀ σ₁ Dw.p Dw.q X F h hh hq t htρ)⟩

end GlobalTheory.DefCoreLie

namespace GlobalTheory.DefCoreLie

end GlobalTheory.DefCoreLie
end

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem _root_.GlobalTheory.T.exists_nonzero_cuspForm_parallelWeight_each_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c), ∃ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n ∧ (∀ τ i, i < Dw.mult τ → 2 ≤ a (τ, i)) ∧ 4 * (finrank ℚ E * r) + 4 ≤ n ∧ ∃ f ∈ cuspOn U Z (wtZ a n), f ≠ 0 := by
  first | exact @GlobalTheory.FlatCore.NonzeroCusp.exists_cuspOn_ne_zero | exact GlobalTheory.FlatCore.NonzeroCusp.exists_cuspOn_ne_zero | (intros; apply GlobalTheory.FlatCore.NonzeroCusp.exists_cuspOn_ne_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.transfer_of_rule4' : ∀ κ : Rule, Rule4 κ → Transfer κ := by
  first | exact @GlobalTheory.MBLow.KeyTop.transfer_of_rule4 | exact GlobalTheory.MBLow.KeyTop.transfer_of_rule4 | (intros; apply GlobalTheory.MBLow.KeyTop.transfer_of_rule4 <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.poincareLelong_normalCrossings_smoothProjective : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → SmoothOfRelativeDimension (e + 1) p → ∀ (L : Fin e → MLine p σ) (M : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (nonzeroLocus s).compl) → ∀ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), 2 * Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) (M.logSec s) = ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L u z - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) u := by
  first | exact @GlobalTheory.Mix.PLSnc.poincareLelong_snc | exact GlobalTheory.Mix.PLSnc.poincareLelong_snc | (intros; apply GlobalTheory.Mix.PLSnc.poincareLelong_snc <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
namespace GlobalTheory.Mix

theorem logSec_intg_proj : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → ∀ (L : Fin D → MLine p σ) (M : MLine p σ) (s : M.B.Sec), genericPoint X ∈ nonzeroLocus s → Intg L (M.logSec s) := by
  intro hP F _ X _ _ p σ D hproj hdim L M s hs
  haveI : CharZero F := RingHom.charZero σ
  obtain ⟨Y, hY, π, hsm, hprojY, hdimY, hgen, hdeg, -⟩ :=
    GlobalTheory.T.exists_logResolution_projective_of_principalisation hP F X p D hproj hdim ⊥ (fun h => h)
  haveI : Smooth (π ≫ p) := SmoothOfRelativeDimension.smooth D (π ≫ p)
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (π ≫ p)
  obtain ⟨s', hz, hn, -⟩ := GlobalTheory.T.exists_pullback_section_zeros_norm_multiplicities F X Y p (π ≫ p) σ π rfl M s
  have hs' : genericPoint Y ∈ nonzeroLocus s' := by
    rw [hz]; show π (genericPoint Y) ∈ nonzeroLocus s; rw [hgen]; exact hs
  have hsmooth := GlobalTheory.T.integrable_logNormSection_mixedChernForms F Y (π ≫ p) σ D hprojY hsm (fun i => (L i).pull π rfl) (M.pull π rfl) s' hs'
  have hmeas := (GlobalTheory.Mix.SecNorm.logSec_basic F X p σ M s).1
  have hpush := (GlobalTheory.T.mixedIntegral_pullback_genericallyFinite F X Y p (π ≫ p) σ D hproj hdim hprojY π rfl hgen (by rw [hdeg]; exact one_ne_zero) L (M.logSec s) hmeas).1
  refine hpush.1 ?_
  have hfun : (fun y => M.logSec s (ptMap π rfl σ y)) = (M.pull π rfl).logSec s' := by
    funext y; simp only [MLine.logSec]; rw [hn y]
  rw [hfun]; exact hsmooth

end GlobalTheory.Mix
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.arithKleiman_selfIntersection_nonneg : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → 1 ≤ D → (∀ (C : HermLB p) (h : X → ℝ), C.IsNef D → C.IsArithHeight h → ∀ z, z ≠ genericPoint X → 0 ≤ h z) → ∀ (C : HermLB p) (c : ℝ), C.IsNef D → C.IsSelfInter c → 0 ≤ c := by
  first | exact @GlobalTheory.KleimanStep.selfInter_nonneg | exact GlobalTheory.KleimanStep.selfInter_nonneg | (intros; apply GlobalTheory.KleimanStep.selfInter_nonneg <;> assumption)
end
