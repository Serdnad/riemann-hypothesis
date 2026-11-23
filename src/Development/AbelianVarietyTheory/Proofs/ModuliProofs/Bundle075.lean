module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSegreCoordinates
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle068
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle070
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymmetricLiftTorsionPointActionOnTheta
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.dense_e8Sharp_after_adjoining_all_matrices : ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g k J b s), (∀ u v, ∃ j, a j = Matrix.single u v 1) → Dense (fromSet em (SharpClass (b := b) W a bas em) t) → ∃ t' : TObj g k (J ⊕ Matrix (Fin 8) (Fin 8) ℤ) b s, Dense (fromSet em (SharpClass (b := b) W (Sum.elim a id) bas em) t') ∧ ∀ c : SiegPre h k (b.ζ : o) s, IsSharp W (Sum.elim a id) bas t' c → IsSharp W a bas t c := by
  first | exact @GlobalTheory.exists_dense_sharp_all_matrices | exact GlobalTheory.exists_dense_sharp_all_matrices | (intros; apply GlobalTheory.exists_dense_sharp_all_matrices <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV

noncomputable section
namespace GlobalTheory.ZV.FormSec
open GlobalTheory.SegreCoord (ev ev_eq ev_ext ev_stalkMap Loc loc_of_secCoord exists_secCoord)

theorem eval₂_scale {R A σ : Type} [CommRing R] [CommRing A] (φ : R →+* A) (x : σ → A) (c : A)
    {F : MvPolynomial σ R} {e : ℕ} (hF : F.IsHomogeneous e) :
    MvPolynomial.eval₂ φ (fun j => c * x j) F = c ^ e * MvPolynomial.eval₂ φ x F := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have h : ∑ i ∈ d.support, d i = e := by
    have := hF (MvPolynomial.mem_support_iff.1 hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h]
  ring

variable {R σ : Type} [CommRing R] {X : Scheme.{0}} {p : X ⟶ Sp R} {M : LB X} {th : σ → M.Sec}

theorem mem_idealOf {F : MvPolynomial σ R} : F ∈ idealOf p M th (𝟙 X) ↔
    ∀ (T : Type) [CommRing T] (β : R →+* T) (y : Sp T ⟶ X) (v : σ → T), y ≫ p = spMap β → SecCoord M th y v →
      MvPolynomial.eval₂ β v F = 0 := by
  simp only [idealOf, Ideal.mem_iInf, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom, Category.comp_id, and_imp]

theorem homogeneousComponent_mem {F : MvPolynomial σ R} (hF : F ∈ idealOf p M th (𝟙 X)) (e : ℕ) :
    MvPolynomial.homogeneousComponent e F ∈ idealOf p M th (𝟙 X) := by
  refine mem_idealOf.2 fun T _ β x v hx h => ?_
  let φ : T →+* LaurentPolynomial T := (Polynomial.toLaurent (R := T)).comp Polynomial.C
  have h1 := Coord.scale (Coord.baseChange h φ) (LaurentPolynomial.isUnit_T (R := T) 1).unit
  have h2 := mem_idealOf.1 hF _ (φ.comp β) _ _ (by rw [Category.assoc, hx]; exact (spMap_comp β φ).symm) h1
  have h3 : MvPolynomial.eval₂ (Polynomial.C.comp β) (fun i => Polynomial.X * Polynomial.C (v i)) F = 0 := by
    apply Polynomial.toLaurent_injective
    rw [map_zero, MvPolynomial.eval₂_comp_left, ← h2]
    congr 1
    funext i
    simp [φ]
  have h4 : ∀ n, MvPolynomial.eval₂ (Polynomial.C.comp β) (fun i => Polynomial.X * Polynomial.C (v i))
      (MvPolynomial.homogeneousComponent n F) =
      Polynomial.monomial n (MvPolynomial.eval₂ β v (MvPolynomial.homogeneousComponent n F)) := fun n => by
    rw [eval₂_scale _ _ _ (MvPolynomial.homogeneousComponent_isHomogeneous n F), ← Polynomial.C_mul_X_pow_eq_monomial,
      _root_.mul_comm, MvPolynomial.eval₂_comp_left]
    rfl
  by_cases he : F.totalDegree < e
  · rw [MvPolynomial.homogeneousComponent_eq_zero _ _ he, MvPolynomial.eval₂_zero]
  rw [← MvPolynomial.sum_homogeneousComponent F, MvPolynomial.eval₂_sum] at h3
  have h5 := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q e) h3
  simp only [h4, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_range,
    Polynomial.coeff_zero] at h5
  rwa [if_pos (by omega)] at h5

theorem isUnit_gs_iff {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) {U : X.Opens} (h : r z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ X.basicOpen a := by
  rw [gs_eq r z U h, ← Scheme.Hom.germ_stalkMap_apply, isUnit_map_iff, X.mem_basicOpen a _ h]

theorem not_mem_of_isUnit_ev {T : Type} [CommRing T] (y : Sp T) {a : T} (h : IsUnit (ev y a)) :
    a ∉ (show PrimeSpectrum T from y).asIdeal := by
  rw [ev_eq, isUnit_gs_iff (𝟙 _) y (U := ⊤) trivial] at h
  have h' : y ∈ (Spec (CommRingCat.of T)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of T)).inv a) := h
  rw [basicOpen_eq_of_affine] at h'
  exact h'

theorem span_eq_top (hc : ⨆ i, Out.nonzeroLocus (th i) = ⊤) {T : Type} [CommRing T] {x : Sp T ⟶ X} {v : σ → T}
    (h : SecCoord M th x v) : Ideal.span (Set.range v) = ⊤ := by
  by_contra hJ
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hJ
  let y : Sp T := (⟨m, hm.isPrime⟩ : PrimeSpectrum T)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc.ge (Set.mem_univ (x y)))
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
  have hk' : x y ∈ M.U k := X.basicOpen_le _ hk
  obtain ⟨u, hu⟩ := loc_of_secCoord h y k hk'
  have := (isUnit_gs_iff x y hk' _).2 hk
  rw [hu] at this
  exact not_mem_of_isUnit_ev y (isUnit_of_mul_isUnit_left this) (hle (Ideal.subset_span ⟨i, rfl⟩))

theorem mem_of_X_mul_mem (hc : ⨆ i, Out.nonzeroLocus (th i) = ⊤) {F : MvPolynomial σ R}
    (hF : ∀ i, MvPolynomial.X i * F ∈ idealOf p M th (𝟙 X)) : F ∈ idealOf p M th (𝟙 X) := by
  refine mem_idealOf.2 fun T _ β x v hx h => ?_
  obtain ⟨s, c, e⟩ := GlobalTheory.SegreCoord.exists_comb (span_eq_top hc h)
  rw [← _root_.one_mul (MvPolynomial.eval₂ β v F), ← e, Finset.sum_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  have := mem_idealOf.1 (hF i) T β x v hx h
  rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] at this
  rw [_root_.mul_assoc, this, mul_zero]


variable (p th) in
def formSec {d : ℕ} {F : MvPolynomial σ R} (hF : F.IsHomogeneous d) : (lbPow M d).Sec where
  f j := MvPolynomial.eval₂ ((resG X le_top).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom))
    (fun i => resG X (LB.wchart_le M (fun _ : PUnit => 𝟙 X) j PUnit.unit) ((th i).f (j PUnit.unit))) F
  compat j j' := by
    have l₁ : (lbPow M d).U j ⊓ (lbPow M d).U j' ≤ M.U (j ⟨⟩) := inf_le_left.trans (Cartier.lbPow_U M d j).le
    have l₂ : (lbPow M d).U j ⊓ (lbPow M d).U j' ≤ M.U (j' ⟨⟩) := inf_le_right.trans (Cartier.lbPow_U M d j').le
    have e := fun i => Cartier.sec_compat (th i) (j ⟨⟩) (j' ⟨⟩) l₁ l₂
    change resG X _ _ = _ * resG X _ _
    refine (MvPolynomial.eval₂_comp_left _ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·)
      ((congrArg Units.val (Cartier.lbPow_g M d j j')).trans (Units.val_pow_eq_pow_val _ _))
      (MvPolynomial.eval₂_comp_left _ _ _ _)).symm)
    refine Eq.trans ?_ (eval₂_scale _ _ _ hF)
    congr 1
    · exact RingHom.ext fun a => (Cartier.resG_resG _ _ _).trans (Cartier.resG_resG _ _ _).symm
    · funext i
      exact (Cartier.resG_resG _ _ _).trans ((e i).trans (congrArg _ (Cartier.resG_resG _ _ _).symm))

theorem gs_formSec {d : ℕ} {F : MvPolynomial σ R} (hF : F.IsHomogeneous d) {T : Type} [CommRing T] {β : R →+* T}
    {x : Sp T ⟶ X} {v : σ → T} (hx : x ≫ p = spMap β) (h : SecCoord M th x v) (y : Sp T) (j : PUnit → M.ι)
    (hy : x y ∈ (lbPow M d).U j) : ∃ u : ((Sp T).presheaf.stalk y)ˣ,
      gs x y _ ((formSec p th hF).f j) = u * ev y (MvPolynomial.eval₂ β v F) := by
  obtain ⟨u, hu⟩ := loc_of_secCoord h y (j ⟨⟩) ((Cartier.lbPow_U M d j).le hy)
  refine ⟨u ^ d, ?_⟩
  let ψ : Γ(X, (lbPow M d).U j) →+* (Sp T).presheaf.stalk y :=
    ((Sp T).presheaf.germ (x ⁻¹ᵁ (lbPow M d).U j) y hy).hom.comp (x.app _).hom
  have hψ : ∀ a, gs x y _ a = ψ a := fun a => gs_eq x y _ hy a
  rw [hψ, MvPolynomial.eval₂_comp_left (ev y), Units.val_pow_eq_pow_val, ← eval₂_scale _ _ _ hF]
  refine (MvPolynomial.eval₂_comp_left ψ _ _ _).trans ?_
  congr 1
  · refine RingHom.ext fun a => ?_
    refine (hψ _).symm.trans ((gs_res x y le_top hy _).trans ((gs_pull x p y ⊤ trivial _).trans ?_))
    rw [hx, ← Category.comp_id (spMap β), GlobalTheory.SegreCoord.gs_stalkMap _ _ _ ⊤ trivial, ← ev_eq, ← ev_stalkMap]
    rfl
  · funext i
    exact (hψ _).symm.trans ((gs_res x y _ hy _).trans ((hu i).trans (_root_.mul_comm _ _)))

theorem formSec_eq_zero_iff (hM : M.IsLB) {d : ℕ} {F : MvPolynomial σ R} (hF : F.IsHomogeneous d) :
    (∀ j, (formSec p th hF).f j = 0) ↔ F ∈ idealOf p M th (𝟙 X) := by
  constructor
  · intro h0
    refine mem_idealOf.2 fun T _ β x v hx h => ev_ext fun y => ?_
    obtain ⟨k, hk⟩ := exists_chart hM (x y)
    have hy : x y ∈ (lbPow M d).U (fun _ => k) := (Cartier.lbPow_U M d _).ge hk
    obtain ⟨u, hu⟩ := gs_formSec hF hx h y _ hy
    have h1 : gs x y _ (0 : Γ(X, (lbPow M d).U (fun _ => k))) = 0 := by rw [gs_eq x y _ hy, map_zero, map_zero]
    rw [map_zero]
    exact u.mul_right_eq_zero.1 (hu.symm.trans ((congrArg (gs x y _) (h0 fun _ => k)).trans h1))
  · intro hI j
    refine fn_ext fun z hz => ?_
    obtain ⟨V, hV, hzV, hle⟩ := exists_isAffineOpen_mem_and_subset hz
    let x : Sp Γ(X, V) ⟶ X := hV.fromSpec
    haveI : IsOpenImmersion x := inferInstanceAs (IsOpenImmersion hV.fromSpec)
    have hr : Set.range x = V := hV.range_fromSpec
    obtain ⟨y, rfl⟩ : z ∈ Set.range x := hr.ge hzV
    obtain ⟨v, hv⟩ := exists_secCoord (th := th) hM (x := x) (k := j ⟨⟩)
      fun y => (Cartier.lbPow_U M d j).le (hle (hr.le ⟨y, rfl⟩))
    have hx : x ≫ p = spMap (Spec.preimage (x ≫ p)).hom := (Spec.map_preimage _).symm
    obtain ⟨u, hu⟩ := gs_formSec hF hx hv y j hz
    rw [mem_idealOf.1 hI _ _ x v hx hv, map_zero, mul_zero, ← Category.comp_id x,
      GlobalTheory.SegreCoord.gs_stalkMap x (𝟙 X) y _ hz] at hu
    rw [gs_eq (𝟙 X) (x y) _ hz 0, map_zero, map_zero]
    exact (asIso (x.stalkMap y)).commRingCatIsoToRingEquiv.injective (hu.trans (map_zero _).symm)

theorem eval_eq_zero_iff {K : Type} [Field K] {p : X ⟶ Sp K} (hM : M.IsLB) {d : ℕ} {F : MvPolynomial σ K}
    (hF : F.IsHomogeneous d) {y : Sp K ⟶ X} {v : σ → K} (hy : y ≫ p = 𝟙 _) (h : SecCoord M th y v) :
    MvPolynomial.eval v F = 0 ↔ ¬ ⊤ ≤ y ⁻¹ᵁ Out.nonzeroLocus (formSec p th hF) := by
  have hy' : y ≫ p = spMap (RingHom.id K) := hy.trans (Spec.map_id (CommRingCat.of K)).symm
  rw [← not_iff_not, not_not]
  constructor
  · intro h0 z _
    obtain ⟨k, hk⟩ := exists_chart hM (y z)
    have hz : y z ∈ (lbPow M d).U (fun _ => k) := (Cartier.lbPow_U M d _).ge hk
    obtain ⟨u, hu⟩ := gs_formSec hF hy' h z _ hz
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => k, (isUnit_gs_iff y z hz _).1 ?_⟩
    rw [hu]
    exact u.isUnit.mul ((Ne.isUnit h0).map (ev z))
  · intro hle h0
    let z : Sp K := (⊥ : PrimeSpectrum K)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show y z ∈ Out.nonzeroLocus (formSec p th hF) from hle (Set.mem_univ z))
    have hz : y z ∈ (lbPow M d).U j := X.basicOpen_le _ hj
    obtain ⟨u, hu⟩ := gs_formSec hF hy' h z j hz
    have hun := (isUnit_gs_iff y z hz _).2 hj
    rw [hu, show MvPolynomial.eval₂ (RingHom.id K) v F = 0 from h0, map_zero, mul_zero] at hun
    exact not_isUnit_zero hun

theorem ideal_of_veryAmple : ∀ (K σ : Type) [Field K] [Finite σ] (X : Scheme.{0}) (p : X ⟶ Sp K) (M : LB X) (th : σ → M.Sec), M.IsLB → VAmp p M th → (∀ F ∈ idealOf p M th (𝟙 X), ∀ e, MvPolynomial.homogeneousComponent e F ∈ idealOf p M th (𝟙 X)) ∧ (∀ F, (∀ i, MvPolynomial.X i * F ∈ idealOf p M th (𝟙 X)) → F ∈ idealOf p M th (𝟙 X)) ∧ ∀ (d : ℕ) (F : MvPolynomial σ K), F.IsHomogeneous d → ∃ τ : (lbPow M d).Sec, (∀ j, τ.f j = MvPolynomial.eval₂ ((resG X le_top).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)) (fun i => resG X (LB.wchart_le M (fun _ : PUnit => 𝟙 X) j PUnit.unit) ((th i).f (j PUnit.unit))) F) ∧ ((∀ j, τ.f j = 0) ↔ F ∈ idealOf p M th (𝟙 X)) ∧ ∀ (y : Sp K ⟶ X) (v : σ → K), y ≫ p = 𝟙 _ → SecCoord M th y v → (MvPolynomial.eval v F = 0 ↔ ¬ ⊤ ≤ y ⁻¹ᵁ Out.nonzeroLocus τ) :=
  fun _ _ _ _ _ p _ th hM hV => ⟨fun _ hF e => homogeneousComponent_mem hF e, fun _ hF => mem_of_X_mul_mem hV.1 hF,
    fun _ _ hF => ⟨formSec p th hF, fun _ => rfl, formSec_eq_zero_iff hM hF,
      fun _ _ hy h => eval_eq_zero_iff hM hF hy h⟩⟩

end GlobalTheory.ZV.FormSec
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoordChart

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (h : B →+* C) :
    spMap h ≫ spMap f = spMap (h.comp f) := by
  unfold spMap
  rw [← Spec.map_comp]; rfl

theorem sp_inj {A B : Type} [CommRing A] [CommRing B] {f h : A →+* B} (e : spMap f = spMap h) : f = h := by
  have := Spec.map_injective e
  exact congrArg CommRingCat.Hom.hom this

theorem sp_surj {A B : Type} [CommRing A] [CommRing B] (z : Sp B ⟶ Sp A) : ∃ f : A →+* B, spMap f = z :=
  ⟨(Spec.preimage z).hom, Spec.map_preimage z⟩

theorem lift_chart {o : Type} [CommRing o] {g n N' : ℕ} {I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)}
    (Y : MMPre n N' I) {R : Type} [CommRing R] (β : o →+* R) (x : Sp R ⟶ Y.MM) (v : Ix g (N' ^ 2) → R)
    {K : Type} [Field K] (y : R →+* K) [IsOpenImmersion x] (hx : x ≫ Y.s = spMap β)
    (hv : SecCoord Y.de Y.th x v) (c : Kˣ)
    {L : Type} [CommRing L] (ψ : L →+* K) (hψ : ∀ l, ψ l ≠ 0 → IsUnit l) (β' : o →+* L)
    (w : Ix g (N' ^ 2) → L) (hβ : ψ.comp β' = y.comp β) (hw : ∀ a, ψ (w a) = c * y (v a))
    (hI : ∀ F ∈ I, MvPolynomial.eval₂ β' w F = 0) :
    ∃ φ : R →+* L, ψ.comp φ = y ∧ φ.comp β = β' ∧ ∃ u : Lˣ, ∀ a, w a = u * φ (v a) := by
  have h1 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hv).1 K y
  have h2 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB h1).2.1 c
  have h3 : (spMap y ≫ x) ≫ Y.s = spMap (y.comp β) := by rw [Category.assoc, hx, sp_comp]
  have hK := Y.loc K _ _ _ h3 h2
  have hL : InMM n N' I β' w := by
    refine ⟨hI, fun q hq a => ?_⟩
    obtain ⟨d, hd⟩ := hK.2 ⊥ Ideal.isPrime_bot a
    refine ⟨d, fun hm => hq.ne_top (Ideal.eq_top_of_isUnit_mem _ hm (hψ _ ?_))⟩
    rw [hw]
    simpa using hd
  obtain ⟨z, ⟨hz1, hz2⟩, -⟩ := Y.pts L β' w hL
  have h4 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hz2).1 K ψ
  have h5 : (spMap ψ ≫ z) ≫ Y.s = spMap (y.comp β) := by rw [Category.assoc, hz1, sp_comp, hβ]
  have heq : spMap ψ ≫ z = spMap y ≫ x := by
    refine (Y.pts K _ _ hK).unique ⟨h5, ?_⟩ ⟨h3, h2⟩
    simpa only [hw] using h4
  have hr : Set.range z ⊆ Set.range x := by
    rintro _ ⟨p, rfl⟩
    let p₀ : Sp K := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
    have hs : p ⤳ spMap ψ p₀ := by
      refine (PrimeSpectrum.le_iff_specializes (R := L) p (spMap ψ p₀)).1 ?_
      intro l hl
      change ψ l ∈ (⊥ : Ideal K)
      by_contra hne
      exact p.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hl (hψ _ (by simpa using hne)))
    refine (hs.map z.continuous).mem_open x.isOpenEmbedding.isOpen_range ⟨spMap y p₀, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, heq]
  obtain ⟨φ, hφ⟩ := sp_surj (IsOpenImmersion.lift x z hr)
  have hz : spMap φ ≫ x = z := by rw [hφ, IsOpenImmersion.lift_fac]
  refine ⟨φ, sp_inj ?_, sp_inj ?_, ?_⟩
  · rw [← cancel_mono x, ← sp_comp, Category.assoc, hz, heq]
  · rw [← sp_comp, ← hx, ← Category.assoc, hz, hz1]
  · have h6 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hv).1 L φ
    rw [hz] at h6
    exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB h6).2.2 w hz2

theorem clear_denom {o σ R L : Type} [CommRing o] [CommRing R] [CommRing L] (β : o →+* R) (φ : R →+* L)
    (v : σ → R) (w : σ → L) (t : R) (h : ∀ a, w a * φ t = φ (v a)) (F : MvPolynomial σ o) :
    ∃ (r : R) (m : ℕ), MvPolynomial.eval₂ (φ.comp β) w F * φ t ^ m = φ r := by
  induction F using MvPolynomial.induction_on with
  | C c => exact ⟨β c, 0, by simp⟩
  | add p q hp hq =>
    obtain ⟨r, m, h1⟩ := hp
    obtain ⟨r', m', h2⟩ := hq
    refine ⟨r * t ^ m' + r' * t ^ m, m + m', ?_⟩
    rw [MvPolynomial.eval₂_add, map_add (f := _), map_mul, map_mul, ← h1, ← h2, map_pow, map_pow]
    ring
  | mul_X p a hp =>
    obtain ⟨r, m, h1⟩ := hp
    refine ⟨r * v a, m + 1, ?_⟩
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, map_mul, ← h1, ← h a]
    ring

theorem residue_generic : ∀ (o : Type) [CommRing o] (g n N' : ℕ) (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (Y : MMPre n N' I) (R : Type) [CommRing R] (β : o →+* R) (x : Sp R ⟶ Y.MM) (v : Ix g (N' ^ 2) → R) (K : Type) [Field K] (y : R →+* K) (a₀ : Ix g (N' ^ 2)), 0 < N' → IsOpenImmersion x → x ≫ Y.s = spMap β → SecCoord Y.de Y.th x v → (∀ k : K, ∃ r r' : R, y r' ≠ 0 ∧ k * y r' = y r) → y (v a₀) ≠ 0 → Subfield.closure (Set.range (y.comp β) ∪ Set.range (fun a => y (v a) / y (v a₀))) = ⊤ ∧ (RingHom.ker y ∈ minimalPrimes R → RingHom.ker (MvPolynomial.eval₂Hom (y.comp β) (fun a => y (v a) / y (v a₀))) ∈ (I ⊔ Ideal.span {MvPolynomial.X a₀ - 1}).minimalPrimes) := by
  intro o _ g n N' I Y R _ β x v K _ y a₀ _ hox hx hv hfr h0
  let c : Kˣ := (Units.mk0 _ h0)⁻¹
  have hc : ∀ a, y (v a) / y (v a₀) = c * y (v a) := fun a => by
    simp [c, div_eq_inv_mul]
  have h1 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hv).1 K y
  have h2 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB h1).2.1 c
  have h3 : (spMap y ≫ x) ≫ Y.s = spMap (y.comp β) := by rw [Category.assoc, hx, sp_comp]
  have hK : ∀ F ∈ I, MvPolynomial.eval₂ (y.comp β) (fun a => y (v a) / y (v a₀)) F = 0 := by
    simpa only [hc] using (Y.loc K _ _ _ h3 h2).1
  constructor
  · set E := Subfield.closure (Set.range (y.comp β) ∪ Set.range (fun a => y (v a) / y (v a₀))) with hE
    let β' : o →+* E := (y.comp β).codRestrict E fun t => Subfield.subset_closure (Or.inl ⟨t, rfl⟩)
    let w : Ix g (N' ^ 2) → E := fun a => ⟨y (v a) / y (v a₀), Subfield.subset_closure (Or.inr ⟨a, rfl⟩)⟩
    obtain ⟨φ, hφ, -⟩ := lift_chart Y β x v y hx hv c E.subtype
      (fun l hl => IsUnit.mk0 l (fun h => hl (by rw [h, map_zero]))) β' w rfl (fun a => hc a) (by
        intro F hF
        apply E.subtype.injective
        rw [MvPolynomial.eval₂_comp_left, map_zero]
        exact hK F hF)
    have hy : ∀ r, y r ∈ E := fun r => by rw [← hφ]; exact (φ r).2
    rw [eq_top_iff]
    intro k _
    obtain ⟨r, r', hr, hk⟩ := hfr k
    rw [eq_div_of_mul_eq hr hk]
    exact E.div_mem (hy r) (hy r')
  · intro hmin
    set ev := MvPolynomial.eval₂Hom (y.comp β) (fun a => y (v a) / y (v a₀)) with hev
    refine ⟨⟨RingHom.ker_isPrime ev, sup_le (fun F hF => hK F hF) ?_⟩, ?_⟩
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      change ev _ = 0
      simp [hev, h0]
    rintro P ⟨hP, hJ⟩ hle
    let e : (MvPolynomial (Ix g (N' ^ 2)) o ⧸ P) →+* K := Ideal.Quotient.lift P ev fun a ha => hle ha
    haveI : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
    let L := Localization.AtPrime (RingHom.ker e)
    have hu : ∀ s : (RingHom.ker e).primeCompl, IsUnit (e s) := fun s => IsUnit.mk0 _ s.2
    let ψ : L →+* K := IsLocalization.lift (M := (RingHom.ker e).primeCompl) hu
    let π : MvPolynomial (Ix g (N' ^ 2)) o →+* L := (algebraMap _ L).comp (Ideal.Quotient.mk P)
    have hπ : ∀ F, ψ (π F) = ev F := fun F => by
      simp only [ψ, π, RingHom.comp_apply, IsLocalization.lift_eq]
      rfl
    have hπe : ∀ F, MvPolynomial.eval₂ (π.comp MvPolynomial.C) (fun a => π (MvPolynomial.X a)) F = π F := fun F => by
      conv_rhs => rw [← MvPolynomial.eval₂_eta F, MvPolynomial.eval₂_comp_left]
      rfl
    have hπ0 : ∀ F, π F = 0 ↔ F ∈ P := fun F => by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact map_eq_zero_iff _ (IsLocalization.injective L (RingHom.ker e).primeCompl_le_nonZeroDivisors)
    have hψ : ∀ l, ψ l ≠ 0 → IsUnit l := by
      intro l hl
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker e).primeCompl l
      rw [IsLocalization.AtPrime.isUnit_mk'_iff L (RingHom.ker e)]
      intro ha
      apply hl
      change ψ (IsLocalization.mk' L a s) = 0
      rw [IsLocalization.lift_mk'_spec, mul_zero]
      exact ha
    obtain ⟨φ, hφ, hβ, u, hw⟩ := lift_chart Y β x v y hx hv c ψ hψ (π.comp MvPolynomial.C)
      (fun a => π (MvPolynomial.X a)) (by ext t; simp [hπ, hev]) (fun a => by rw [hπ, ← hc]; simp [hev])
      (fun F hF => by rw [hπe, hπ0]; exact hJ (Ideal.mem_sup_left hF))
    have hone : (u : L) * φ (v a₀) = 1 := by
      rw [← hw, ← sub_eq_zero, ← map_one π, ← map_sub, hπ0]
      exact hJ (Ideal.mem_sup_right (Ideal.subset_span rfl))
    have hker : RingHom.ker y ≤ RingHom.ker φ :=
      hmin.2 ⟨RingHom.ker_isPrime φ, bot_le⟩ (fun r hr => by
        rw [RingHom.mem_ker] at hr ⊢
        rw [← hφ, RingHom.comp_apply, hr, map_zero])
    intro F hF
    obtain ⟨r, m, hr⟩ := clear_denom β φ v (fun a => π (MvPolynomial.X a)) (v a₀)
      (fun a => by
        change π (MvPolynomial.X a) * _ = _
        rw [hw a, mul_right_comm, hone, _root_.one_mul]) F
    rw [hβ, hπe] at hr
    have hyr : r ∈ RingHom.ker y := by
      rw [RingHom.mem_ker] at hF ⊢
      rw [← hφ, RingHom.comp_apply, ← hr, map_mul, hπ, hF, zero_mul]
    have hφr : φ r = 0 := hker hyr
    rw [hφr] at hr
    rw [← hπ0]
    exact ((IsUnit.of_mul_eq_one_right _ hone).pow m).mul_left_eq_zero.1 hr

end GlobalTheory.CoordChart
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem morphisms_descend_to_large_subfield :
    ∀ (K : Type) [Field K] (K₀ : Subfield K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀) (Z : Scheme.{0}) (q : Z ⟶ Sp K₀) [QuasiCompact p₀] [QuasiSeparated p₀] [LocallyOfFinitePresentation q] (I : Type) [Finite I] (f : I → (X ⟶ Z)), IsPullback φ p p₀ (spMap K₀.subtype) → (∀ j, f j ≫ q = φ ≫ p₀) → ∃ s : Finset K, ∀ (K₁ : Subfield K) (h : K₀ ≤ K₁), (s : Set K) ⊆ K₁ → ∀ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ₁ : X₁ ⟶ X₀) (ψ : X ⟶ X₁), IsPullback φ₁ p₁ p₀ (spMap (Subfield.inclusion h)) → ψ ≫ φ₁ = φ → ψ ≫ p₁ = p ≫ spMap K₁.subtype → ∃ f₁ : I → (X₁ ⟶ Z), ∀ j, ψ ≫ f₁ j = f j ∧ f₁ j ≫ q = φ₁ ≫ p₀ := by
  intro K _ K₀ X₀ X p₀ p φ Z q _ _ _ I _ f hX hf
  have hX' : IsPullback φ p p₀ (spMap (algebraMap K₀ K)) := hX
  obtain ⟨R, g, ⟨s, rfl⟩, -, hg⟩ := Spread.exists_fg_forall_comp_eq (A := K) p₀ q
    (fun j ↦ hX'.isoPullback.inv ≫ f j)
    (fun j ↦ by rw [Category.assoc, hf, IsPullback.isoPullback_inv_fst_assoc]) ⊥ Subalgebra.fg_bot
  refine ⟨s, fun K₁ h hs X₁ p₁ φ₁ ψ h₁ hψ₁ hψ₂ ↦ ?_⟩
  have hle : ∀ x ∈ Algebra.adjoin K₀ (s : Set K), x ∈ K₁ := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hs hx
    | algebraMap r => exact h r.2
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  let e : Algebra.adjoin K₀ (s : Set K) →+* K₁ :=
    (Algebra.adjoin K₀ (s : Set K)).val.toRingHom.codRestrict K₁ fun x ↦ hle x x.2
  have he₁ : spMap e ≫ spMap (algebraMap K₀ (Algebra.adjoin K₀ (s : Set K))) =
      spMap (Subfield.inclusion h) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have he₂ : spMap K₁.subtype ≫ spMap e =
      spMap (Algebra.adjoin K₀ (s : Set K)).val.toRingHom := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let u : X₁ ⟶ pullback p₀ (spMap (algebraMap K₀ (Algebra.adjoin K₀ (s : Set K)))) :=
    pullback.lift φ₁ (p₁ ≫ spMap e) (by rw [Category.assoc, he₁, h₁.w])
  have hu : ψ ≫ u = hX'.isoPullback.hom ≫ Spread.bcMap p₀ (Algebra.adjoin K₀ (s : Set K)).val := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, Spread.bcMap_fst, IsPullback.isoPullback_hom_fst,
        pullback.lift_fst, hψ₁]
    · rw [Category.assoc, Category.assoc, Spread.bcMap_snd, IsPullback.isoPullback_hom_snd_assoc,
        pullback.lift_snd, ← Category.assoc, hψ₂, Category.assoc, he₂]
  refine ⟨fun j ↦ u ≫ g j, fun j ↦ ⟨?_, ?_⟩⟩
  · rw [← Category.assoc, hu, Category.assoc, (hg j).2, Iso.hom_inv_id_assoc]
  · rw [Category.assoc, (hg j).1, pullback.lift_fst_assoc]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.exists_smoothOfRelDim_of_isUnit_proper_flat : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (g : ℕ) (K : Type) [Field K] (x : R →+* K), IsProper s → Flat s → SmoothOfRelativeDimension g (pullback.snd s (spMap x)) → ∃ f : R, x f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) → SmoothOfRelativeDimension g (pullback.snd s (spMap φ)) := by
  first | exact @GlobalTheory.SmoothNearFibre.exists_smoothOfRelativeDimension_of_isUnit | exact GlobalTheory.SmoothNearFibre.exists_smoothOfRelativeDimension_of_isUnit | (intros; apply GlobalTheory.SmoothNearFibre.exists_smoothOfRelativeDimension_of_isUnit <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.symmetricLift_torsionPoint_action_on_theta : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (N : ℕ) (l : u.Λ) (f : (Fin P.g → ℂ) → ℂ) (T : Over (Sp ℂ)) [IsIso T.hom] (p : 𝟙_ (Over (Sp ℂ)) ⟶ T) (x : T ⟶ P.A) (U : Out.ThetaGrp P.A P.L ((N : ℤ) ^ 2) T) (s s' : LB.Sec (Out.LPow P.A P.L ((N : ℤ) ^ 2) T)), u.IsAH Hm χ → Odd N → p ≫ x = u.ex (((N : ℂ) ^ 2)⁻¹ • (l : Fin P.g → ℂ)) → Out.SymLift P.A P.L ((N : ℤ) ^ 2) (N ^ 2) x U → Out.IsActOf P.A P.L ((N : ℤ) ^ 2) U s s' → (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L ((N : ℤ) ^ 2) T).U j) (s.f j) = f z * u.fr (j 0) z ^ (((N : ℤ) ^ 2) : ℤ)) → (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L ((N : ℤ) ^ 2) T).U j) (s'.f j) = (χ l * Complex.exp (-(Real.pi / 2 / (N : ℂ) ^ 2) * hermForm Hm l l - Real.pi * hermForm Hm z l) * f (z + ((N : ℂ) ^ 2)⁻¹ • (l : Fin P.g → ℂ))) * u.fr (j 0) z ^ (((N : ℤ) ^ 2) : ℤ)) := by
  first | exact @GlobalTheory.symLift_act_in_frame | exact GlobalTheory.symLift_act_in_frame | (intros; apply GlobalTheory.symLift_act_in_frame <;> assumption)
end
