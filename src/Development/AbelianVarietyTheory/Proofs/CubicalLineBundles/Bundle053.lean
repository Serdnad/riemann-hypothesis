module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle036
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle048
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle049
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle039
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.LieLoc

theorem coord_eq_sum {R₀ R K : Type} [CommRing R₀] [CommRing R] [CommRing K] {f : R₀ →+* R} {g : R →+* K}
    {A₀ : Over (Sp R₀)} {G : Over (Sp R)} {A : Over (Sp K)} [GrpObj A₀] [GrpObj G] [GrpObj A] [IsCommMonObj A]
    {φ : G.left ⟶ A₀.left} {ψ : A.left ⟶ G.left} (hφ : IsGrpPullback G A₀ (spMap f) φ)
    (hψ : IsGrpPullback A G (spMap g) ψ) {n m : ℕ} {v : Fin n → (epsR K ⟶ A)} (hv : IsLieBasis v)
    {e : Fin m → (epsR R ⟶ G)} (he : IsLieBasis e) {M : Fin m → Fin n → K}
    (hM : ∀ i, ∃ w, IsVecOver g ψ (e i) w ∧ IsLieComb (M i) v w)
    {u : epsR R₀ ⟶ A₀} (hu : IsTangent u) {w : epsR K ⟶ A} (hw : IsVecOver (g.comp f) (ψ ≫ φ) u w)
    {c : Fin n → K} (hc : IsLieComb c v w) : ∃ a : Fin m → R, c = ∑ i, g (a i) • M i := by
  choose e₀ h₁ h₂ using hM
  obtain ⟨u', hu', -⟩ := existsUnique_isVecOver hφ.1 u
  obtain ⟨a, ha, -⟩ := he.2 u' (hu'.isTangent hφ hu)
  have h₃ := (lieComb_baseChange R K g G A ψ hψ m e u' a e₀ w h₁ ha).1
    (EllComp.isVecOver_cancel hφ.1 hψ.1 hu' hw)
  obtain ⟨-, ht, hcomp, -⟩ := LieComb.lieComb_algebra K A n v hv.1
  exact ⟨a, (hv.2 w (ht _ _ hc)).unique hc (hcomp m M e₀ _ w h₂ h₃)⟩

theorem exists_denom {O R R' K : Type} [CommRing O] [CommRing R] [CommRing R'] [CommRing K] [Algebra O R]
    [Algebra R R'] [Algebra O K] (N : Submonoid O) [IsLocalization N R] (r : O)
    [IsLocalization.Away (algebraMap O R r) R'] (g : R' →+* K)
    (hg : ∀ x, g (algebraMap R R' (algebraMap O R x)) = algebraMap O K x) {m : ℕ} (b : Fin m → R') :
    ∃ s ∈ N, ∃ (k : ℕ) (a : Fin m → O), ∀ i, (r ^ k * s) • g (b i) = algebraMap O K (a i) := by
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers (algebraMap O R r)) b
  choose x hx using hk
  obtain ⟨⟨s, hs⟩, h⟩ := IsLocalization.exist_integer_multiples_of_finite N x
  choose a ha using h
  refine ⟨s, hs, k, a, fun i => ?_⟩
  rw [← hg, ha, Algebra.smul_def, Algebra.smul_def, map_mul (algebraMap R R'), hx, ← hg, Algebra.smul_def, ← map_mul]
  simp only [map_mul, map_pow]
  ring

theorem lieLat_localization : ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (R : Type) [CommRing R] [Algebra (𝓞 K) R] [Algebra R K] [IsScalarTower (𝓞 K) R K] (N : Submonoid (𝓞 K)) [IsLocalization N R] (G : Over (Sp R)) [GrpObj G] (φ : G.left ⟶ P.A.left) (ψ : F.P₀.A.left ⟶ G.left) (e : Fin F.P₀.g → (epsR R ⟶ G)) (e₀ : Fin F.P₀.g → (epsR K ⟶ F.P₀.A)) (M : Matrix (Fin F.P₀.g) (Fin F.P₀.g) K), IsGrpPullback G P.A (spMap (algebraMap (𝓞 K) R)) φ → IsGrpPullback F.P₀.A G (spMap (algebraMap R K)) ψ → ψ ≫ φ = F.φ → IsLieBasis e → (∀ i, IsVecOver (algebraMap R K) ψ (e i) (e₀ i) ∧ IsLieComb (M i) F.v (e₀ i)) →
  (∀ i, ∃ s ∈ N, s • M i ∈ F.lieLat) ∧ ∀ c ∈ F.lieLat, ∃ a : Fin F.P₀.g → R, c = ∑ i, algebraMap R K (a i) • M i := by
  intro K _ _ P F R _ _ _ _ N _ G _ φ ψ e e₀ M hφ hψ hF he hM
  refine ⟨fun i => ?_, fun c hc => ?_⟩
  · obtain ⟨n, r, M', -, hr, hL, hb⟩ := GlobalTheory.T.lie_lattice_local_basis_description K P F
    have key : ∀ j, ∃ s ∈ N, ∃ (k : ℕ) (a : Fin F.P₀.g → 𝓞 K), (r j ^ k * s) • M i = ∑ l, a l • M' j l := by
      intro j
      let R' := Localization.Away (algebraMap (𝓞 K) R (r j))
      have hu : IsUnit (algebraMap R K (algebraMap (𝓞 K) R (r j))) := by
        rw [← IsScalarTower.algebraMap_apply]
        exact IsUnit.mk0 _ (by simpa using (hr j).1)
      let g : R' →+* K := IsLocalization.Away.lift (algebraMap (𝓞 K) R (r j)) hu
      have hg : g.comp (algebraMap R R') = algebraMap R K := IsLocalization.Away.lift_comp _ hu
      have hg' : ∀ x, g (algebraMap R R' (algebraMap (𝓞 K) R x)) = algebraMap (𝓞 K) K x := fun x => by
        rw [IsScalarTower.algebraMap_apply (𝓞 K) R K, ← hg]; rfl
      let _ : Algebra R' K := g.toAlgebra
      have : IsScalarTower (𝓞 K) R' K := IsScalarTower.of_algebraMap_eq fun x => by
        rw [IsScalarTower.algebraMap_apply (𝓞 K) R R']; exact (hg' x).symm
      have h' := isGrpPullback_pullback G (spMap (algebraMap R R'))
      have n' : IsGrpPullback F.P₀.A G (spMap g ≫ spMap (algebraMap R R')) ψ :=
        hψ.congr (by rw [spMap_comp_spMap, hg]) rfl
      have w : ψ ≫ G.hom = (F.P₀.A.hom ≫ spMap g) ≫ spMap (algebraMap R R') :=
        n'.1.w.trans (Category.assoc _ _ _).symm
      have e₁ := h'.1.lift_fst _ _ w
      have hψ' := h'.cancel (n'.congr rfl e₁.symm) (h'.1.lift_snd _ _ w)
      obtain ⟨e', he', hM'⟩ := hb j R' _ _ _
        (by rw [IsScalarTower.algebraMap_apply (𝓞 K) R R']; exact IsLocalization.Away.algebraMap_isUnit _)
        ((h'.comp hφ).congr (by rw [spMap_comp_spMap, ← IsScalarTower.algebraMap_eq]) rfl) hψ'
        (by rw [← Category.assoc, e₁, hF])
      obtain ⟨b, hb⟩ := coord_eq_sum h' hψ' F.basis he' hM' (he.1 i) (by rw [e₁, hg]; exact (hM i).1) (hM i).2
      obtain ⟨s, hs, k, a, ha⟩ := exists_denom N (r j) g hg' b
      refine ⟨s, hs, k, a, ?_⟩
      rw [hb, Finset.smul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [← smul_assoc, ha, algebraMap_smul]
    classical
    choose s hs k a h using key
    refine ⟨∏ j, s j, prod_mem fun j _ => hs j, (hL _).2 fun j => ⟨k j, (∏ l ∈ Finset.univ.erase j, s l) • a j, ?_⟩⟩
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), smul_smul, ← _root_.mul_assoc, _root_.mul_comm, ← smul_smul, h,
      Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [smul_smul]; rfl
  · induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨u, hu, w, hw, hc⟩ := hc
      exact coord_eq_sum hφ hψ F.basis he (fun i => ⟨_, hM i⟩) hu
        (by rw [hF, ← IsScalarTower.algebraMap_eq]; exact hw) hc
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, by simp [add_smul, Finset.sum_add_distrib]⟩
    | smul t x _ hx =>
      obtain ⟨a, rfl⟩ := hx
      refine ⟨algebraMap (𝓞 K) R t • a, ?_⟩
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun l _ => by
        rw [Pi.smul_apply, smul_eq_mul, map_mul, ← IsScalarTower.algebraMap_apply, mul_smul, algebraMap_smul K t]

end GlobalTheory.CM.LieLoc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.LieLattice

theorem exists_smul_eq_sum_rows {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    {g : ℕ} (M : Matrix (Fin g) (Fin g) K) (hM : M.det ≠ 0) (c : Fin g → K) :
    ∃ d : O, d ≠ 0 ∧ ∃ a : Fin g → O, d • c = ∑ j, a j • M j := by
  obtain ⟨x, hx⟩ : ∃ x : Fin g → K, Matrix.vecMul x M = c :=
    ⟨Matrix.vecMul c M⁻¹, by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hM), Matrix.vecMul_one]⟩
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) x
  choose a ha using hd
  refine ⟨d, nonZeroDivisors.coe_ne_zero d, a, ?_⟩
  rw [← hx, Matrix.vecMul_eq_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_assoc, ← ha j, algebraMap_smul]

theorem fg_and_span_eq_top {O K : Type} [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] {g n : ℕ} (L : Submodule O (Fin g → K)) (r : Fin n → O)
    (M : Fin n → Matrix (Fin g) (Fin g) K) (hr : Ideal.span (Set.range r) = ⊤) (hM : ∀ i, (M i).det ≠ 0)
    (hL : ∀ c, c ∈ L ↔ ∀ i, ∃ (k : ℕ) (a : Fin g → O), r i ^ k • c = ∑ j, a j • M i j) :
    L.FG ∧ Submodule.span K (L : Set (Fin g → K)) = ⊤ := by
  constructor
  · let N : Submodule O (Fin g → K) := Submodule.span O (Set.range fun p : Fin n × Fin g => M p.1 p.2)
    have hN : N.FG := Submodule.fg_span (Set.finite_range _)
    refine Submodule.FG.of_le hN fun c hc => ?_
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem N (Set.range r) hr c ?_
    rintro ⟨_, i, rfl⟩
    obtain ⟨k, a, h⟩ := (hL c).1 hc i
    refine ⟨k, ?_⟩
    change r i ^ k • c ∈ N
    rw [h]
    exact N.sum_mem fun j _ => N.smul_mem _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  · classical
    rw [eq_top_iff]
    intro c _
    choose d hd a ha using fun i => exists_smul_eq_sum_rows (O := O) (M i) (hM i) c
    have hD : (∏ i, d i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hd i
    have hmem : (∏ i, d i) • c ∈ L := by
      refine (hL _).2 fun i => ⟨0, fun j => (∏ l ∈ Finset.univ.erase i, d l) * a i j, ?_⟩
      rw [pow_zero, one_smul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul, ha, Finset.smul_sum]
      simp only [mul_smul]
    have hK : algebraMap O K (∏ i, d i) ≠ 0 := by
      rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective O K)]
    have e : c = (algebraMap O K (∏ i, d i))⁻¹ • ((∏ i, d i) • c) := by
      rw [← algebraMap_smul K (∏ i, d i) c, smul_smul, inv_mul_cancel₀ hK, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem lieLat_fg_and_span_eq_top :
    ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P),
      F.lieLat.FG ∧ Submodule.span K (F.lieLat : Set (Fin F.P₀.g → K)) = ⊤ := by
  intro K _ _ P F
  obtain ⟨n, r, M, hr, hM, hL, -⟩ := GlobalTheory.T.lie_lattice_local_basis_description K P F
  exact fg_and_span_eq_top F.lieLat r M hr (fun i => (hM i).2) hL

end GlobalTheory.CM.LieLattice
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.HermSq

section general

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (br : R →+* R)

def IsSumOfNorms (B : M → M → R) : Prop :=
  ∃ (J : Type) (_ : Fintype J) (l : J → M →ₗ[R] R), ∀ x y, B x y = ∑ k, l k x * br (l k y)

variable {br}

theorem IsSumOfNorms.congr {B B' : M → M → R} (h : IsSumOfNorms br B) (e : ∀ x y, B' x y = B x y) : IsSumOfNorms br B' := by
  obtain ⟨J, _, l, hl⟩ := h
  exact ⟨J, inferInstance, l, fun x y => (e x y).trans (hl x y)⟩

theorem IsSumOfNorms.zero : IsSumOfNorms br (fun (_ _ : M) => (0 : R)) :=
  ⟨Empty, inferInstance, fun e => e.elim, fun x y => by simp⟩

theorem IsSumOfNorms.one (f : M →ₗ[R] R) : IsSumOfNorms br (fun x y => f x * br (f y)) :=
  ⟨Unit, inferInstance, fun _ => f, fun x y => by simp⟩

theorem IsSumOfNorms.add {B B' : M → M → R} (h : IsSumOfNorms br B) (h' : IsSumOfNorms br B') :
    IsSumOfNorms br (fun x y => B x y + B' x y) := by
  obtain ⟨J, _, l, hl⟩ := h
  obtain ⟨J', _, l', hl'⟩ := h'
  refine ⟨J ⊕ J', inferInstance, Sum.elim l l', fun x y => ?_⟩
  simp [Fintype.sum_sum_type, hl, hl']

theorem IsSumOfNorms.nsmul {B : M → M → R} (h : IsSumOfNorms br B) (n : ℕ) :
    IsSumOfNorms br (fun x y => (n : R) * B x y) := by
  induction n with
  | zero => exact IsSumOfNorms.zero.congr fun x y => by simp
  | succ n ih => exact (ih.add h).congr fun x y => by push_cast; ring

theorem IsSumOfNorms.comp {B : M → M → R} (h : IsSumOfNorms br B) (Z : M →ₗ[R] M) :
    IsSumOfNorms br (fun x y => B (Z x) (Z y)) := by
  obtain ⟨J, _, l, hl⟩ := h
  exact ⟨J, inferInstance, fun k => l k ∘ₗ Z, fun x y => hl _ _⟩

theorem IsSumOfNorms.sum {κ : Type} (s : Finset κ) {B : κ → M → M → R} (h : ∀ i, IsSumOfNorms br (B i)) :
    IsSumOfNorms br (fun x y => ∑ i ∈ s, B i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact IsSumOfNorms.zero.congr fun x y => by simp
  | insert a s ha ih => exact ((h a).add ih).congr fun x y => by rw [Finset.sum_insert ha]

variable (g : M → M →ₗ[R] R) (herm : ∀ x y, g x y = br (g y x))


include herm in
theorem exists_step (e : M) (q : ℕ) (hq : g e e = q) :
    ∃ Z : M →ₗ[R] M, Z e = 0 ∧
      ∀ x y, g (Z y) (Z x) = (q : R) ^ 2 * g y x - q * (g e x * br (g e y)) := by
  refine ⟨(q : R) • LinearMap.id - (g e).smulRight e, by simp [hq], fun x y => ?_⟩
  have h1 : ∀ a, g (((q : R) • LinearMap.id - (g e).smulRight e : M →ₗ[R] M) y) a
      = q * g y a - br (g e y) * g e a := by
    intro a
    rw [herm]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
      map_sub, map_smul, smul_eq_mul, map_mul, map_natCast]
    rw [← herm, ← herm e a]
  rw [h1]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
      map_sub, map_smul, smul_eq_mul, hq]
  rw [herm y e]
  ring

variable (pos : ∀ x, x ≠ 0 → ∃ q : ℕ, 1 ≤ q ∧ g x x = q)

include herm pos in
theorem exists_kill {κ : Type} (v : κ → M) (s : Finset κ) :
    ∃ (N : ℕ) (Z : M →ₗ[R] M), 1 ≤ N ∧ (∀ i ∈ s, Z (v i) = 0) ∧
      IsSumOfNorms br (fun x y => (N : R) * g y x - g (Z y) (Z x)) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, LinearMap.id, le_rfl, by simp, IsSumOfNorms.zero.congr fun x y => by simp⟩
  | insert a s ha ih =>
    obtain ⟨N, Z, hN, hZ, hB⟩ := ih
    by_cases he : Z (v a) = 0
    · refine ⟨N, Z, hN, fun i hi => ?_, hB⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      exacts [he, hZ i hi]
    · obtain ⟨q, hq1, hq⟩ := pos _ he
      obtain ⟨Y, hY, hY'⟩ := exists_step g herm _ q hq
      refine ⟨q ^ 2 * N, Y ∘ₗ Z, Nat.mul_pos (pow_pos hq1 2) hN, fun i hi => ?_, ?_⟩
      · rcases Finset.mem_insert.1 hi with rfl | hi
        · exact hY
        · simp [hZ i hi]
      · refine ((hB.nsmul (q ^ 2)).add (((IsSumOfNorms.one (g (Z (v a)))).comp Z).nsmul q)).congr fun x y => ?_
        simp only [LinearMap.comp_apply, hY']
        push_cast
        ring


include herm pos in
theorem exists_split {n : ℕ} (u w : Fin n → M) (fr : ∀ a, a = ∑ i, g (w i) a • u i) :
    ∃ (N m : ℕ) (l : M →ₗ[R] (Fin m → R)) (r : (Fin m → R) →ₗ[R] M), 1 ≤ N ∧ r ∘ₗ l = LinearMap.id ∧
      ∀ x y, (N : R) * g y x = ∑ k, l x k * br (l y k) := by
  classical
  obtain ⟨N, Z, hN, hZ, hB⟩ := exists_kill g herm pos u Finset.univ
  have hZ0 : ∀ a, Z a = 0 := fun a => by

    rw [fr a, map_sum]
    exact Finset.sum_eq_zero fun i hi => by rw [map_smul, hZ i hi, smul_zero]
  have hB' : IsSumOfNorms br (fun x y => (N : R) * g y x) := hB.congr fun x y => by simp [hZ0]
  have key : ∀ e : M, ∃ K : ℕ, IsSumOfNorms br (fun x y => (K : R) * g y x - g e x * br (g e y)) := by
    intro e
    by_cases he : e = 0
    · refine ⟨0, IsSumOfNorms.zero.congr fun x y => ?_⟩
      subst he
      rw [herm 0 x]; simp
    · obtain ⟨q, hq1, hq⟩ := pos _ he
      obtain ⟨Y, -, hY'⟩ := exists_step g herm _ q hq
      obtain ⟨c, hc⟩ : ∃ c : ℕ, N * q = c + 1 := ⟨N * q - 1, by have := Nat.mul_pos hN hq1; omega⟩
      have hc' : (N : R) * q = c + 1 := by exact_mod_cast congrArg (Nat.cast : ℕ → R) hc
      refine ⟨N * q ^ 2, ((hB'.comp Y).add ((IsSumOfNorms.one (g e)).nsmul c)).congr fun x y => ?_⟩
      simp only [hY']
      push_cast
      linear_combination (g e x * br (g e y)) * hc'
  choose K hK using key
  obtain ⟨J, _, l, hl⟩ := hB'.add (IsSumOfNorms.sum Finset.univ fun i => hK (w i))
  let eqv := Fintype.equivFin (Fin n ⊕ J)
  refine ⟨N + ∑ i, K (w i), Fintype.card (Fin n ⊕ J),
    LinearMap.pi fun k => Sum.elim (fun i => g (w i)) l (eqv.symm k),
    ∑ i, (LinearMap.proj (eqv (Sum.inl i)) : (Fin _ → R) →ₗ[R] R).smulRight (u i), by omega, ?_, fun x y => ?_⟩
  · ext a
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply,
      LinearMap.pi_apply, Equiv.symm_apply_apply, Sum.elim_inl, LinearMap.id_apply]
    exact (fr a).symm
  · simp only [LinearMap.pi_apply]
    rw [eqv.symm.sum_comp (fun k => Sum.elim (fun i => g (w i)) l k x * br (Sum.elim (fun i => g (w i)) l k y)),
      Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [← hl x y]
    simp only [Finset.sum_sub_distrib, ← Finset.sum_mul]
    push_cast
    ring

end general

theorem kForm_sum_sq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H), IsKForm D ε h → (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → ∃ (N m : ℕ) (l : D.La →ₗ[OK H] (Fin m → OK H)) (r : (Fin m → OK H) →ₗ[OK H] D.La), 1 ≤ N ∧ r ∘ₗ l = LinearMap.id ∧ ∀ x y, (N : 𝓞 E) * (h x y : OK H) = ∑ k, ((l x k : OK H) : 𝓞 E) * H.bar (l y k : OK H) := by
  intro E _ _ _ H D ε h hh hpos
  obtain ⟨h₀, -, huniq, hherm, -, hdiag, -, n, u, w, fr⟩ := GlobalTheory.CM.exists_kForm E H D ε
  obtain ⟨-, -, ⟨br, hbr, -⟩, -⟩ := GlobalTheory.CM.OK_isDedekindDomain_and_projective E H
  obtain rfl := huniq h hh
  let g : D.La → D.La →ₗ[OK H] OK H := fun y =>
    { toFun := fun x => h₀ x y
      map_add' := fun a b => by rw [map_add (f := _)]; rfl
      map_smul' := fun c a => by rw [map_smul]; rfl }
  obtain ⟨N, m, l, r, hN, hr, hl⟩ := exists_split (br := br.toRingHom) g
    (fun x y => Subtype.ext ((hherm x y).trans (hbr _).symm))
    (fun x hx => by
      have h1 := hpos x hx
      refine ⟨((ε : ℤ) * D.EF (H.w0 • x) x).toNat, by omega, Subtype.ext ?_⟩
      refine (hdiag x).trans ?_
      conv_lhs => rw [← Int.toNat_of_nonneg h1.le]
      rw [Int.cast_natCast, SubringClass.coe_natCast]) u w fr
  refine ⟨N, m, l, r, hN, hr, fun x y => ?_⟩
  have := congrArg (OK H).val (hl x y)

  simp only [map_mul, map_sum, map_natCast, Subalgebra.coe_val] at this
  simp only [← hbr]
  exact this

end GlobalTheory.CM.HermSq
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.exists_unique_cmHermitianLatticeForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ), ∃ h : D.La →ₗ[OK H] D.La →+ OK H, IsKForm D ε (fun x y => h x y) ∧ (∀ h' : D.La → D.La → OK H, IsKForm D ε h' → h' = fun x y => h x y) ∧ (∀ x y, ((h y x : OK H) : 𝓞 E) = H.bar (h x y : OK H)) ∧ (∀ (s : 𝓞 E) x y, h (s • x) y = h x (H.bar s • y)) ∧ (∀ x, ((h x x : OK H) : 𝓞 E) = (((ε : ℤ) * D.EF (H.w0 • x) x : ℤ) : 𝓞 E)) ∧ (∀ f : D.La →ₗ[OK H] OK H, ∃! y, ∀ x, f x = h x y) ∧ ∃ (n : ℕ) (x y : Fin n → D.La), ∀ a, a = ∑ i, h a (y i) • x i := by
  first | exact @GlobalTheory.CM.exists_kForm | exact GlobalTheory.CM.exists_kForm | (intros; apply GlobalTheory.CM.exists_kForm <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.lieAlgebraSquaredLength_comp_pairing_hom : ThetaUnifAV → Out.Laws → ∀ (R : Type) [CommRing R] (P P' : Out.PolAV (Sp R)) (f : P.A ⟶ P'.A) (g : P.A ⟶ P.A) (v : epsR R ⟶ P.A) (a : R) (s : R →+* ℂ) (r r' : ℝ), IsMonHom f → IsMonHom g → LamEq P'.L f f P.L g (𝟙 P.A) → IsTangent v → IsLieComb ![a] ![v] (v ≫ g) → IsLieNormSq P v s r → IsLieNormSq P' (v ≫ f) s r' → r' = (s a).re * r := by
  first | exact @GlobalTheory.NormHom.lieNormSq_comp | exact GlobalTheory.NormHom.lieNormSq_comp | (intros; apply GlobalTheory.NormHom.lieNormSq_comp <;> assumption)
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.lieLattice_localization_modelLieAlgebra : ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (R : Type) [CommRing R] [Algebra (𝓞 K) R] [Algebra R K] [IsScalarTower (𝓞 K) R K] (N : Submonoid (𝓞 K)) [IsLocalization N R] (G : Over (Sp R)) [GrpObj G] (φ : G.left ⟶ P.A.left) (ψ : F.P₀.A.left ⟶ G.left) (e : Fin F.P₀.g → (epsR R ⟶ G)) (e₀ : Fin F.P₀.g → (epsR K ⟶ F.P₀.A)) (M : Matrix (Fin F.P₀.g) (Fin F.P₀.g) K), IsGrpPullback G P.A (spMap (algebraMap (𝓞 K) R)) φ → IsGrpPullback F.P₀.A G (spMap (algebraMap R K)) ψ → ψ ≫ φ = F.φ → IsLieBasis e → (∀ i, IsVecOver (algebraMap R K) ψ (e i) (e₀ i) ∧ IsLieComb (M i) F.v (e₀ i)) →
  (∀ i, ∃ s ∈ N, s • M i ∈ F.lieLat) ∧ ∀ c ∈ F.lieLat, ∃ a : Fin F.P₀.g → R, c = ∑ i, algebraMap R K (a i) • M i := by
  first | exact @GlobalTheory.CM.LieLoc.lieLat_localization | exact GlobalTheory.CM.LieLoc.lieLat_localization | (intros; apply GlobalTheory.CM.LieLoc.lieLat_localization <;> assumption)

end
end
