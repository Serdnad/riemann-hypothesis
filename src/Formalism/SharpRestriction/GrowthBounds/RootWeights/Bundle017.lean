module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle002
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle010
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.MemWeightSpaceIffDiagonalEigen
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle008
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightProjectionPreservesLattice
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle004
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle013
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle005
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.GenericMatrixEvaluationDet
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees

@[expose] public section

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section lat
variable {n : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module (KK O) W] [Module O W] [IsScalarTower O (KK O) W]

theorem homLattice_binomial_stable [CharZero (KK O)] [FiniteDimensional (KK O) W] (E : GLOps n (KK O) W) (hE : IsGLRep E)
    (M : Submodule O W) (hM : UZStable (O := O) E M)
    (L : Submodule (KK O) W) (hL : IsSubrepresentation E L) (a : Fin n) (k : ℕ)
    (f : L →ₗ[KK O] W) (hf : f ∈ homLattice M L) :
    binomE (homRepresentation (restrictRepresentation E L hL) E) a k f ∈ homLattice M L := by
  have hres := restrictRepresentation_isRep E hE L hL
  obtain ⟨s, π, h1, h2, h3, h4, h5⟩ := weight_projections_exist (restrictRepresentation E L hL) hres
  obtain ⟨s', π', h1', h2', h3', h4', h5'⟩ := weight_projections_exist E hE
  have hdec : f = ∑ mu' ∈ s', ∑ mu ∈ s, (π' mu' ∘ₗ f ∘ₗ π mu) := by
    ext x
    simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    have : ∀ mu' ∈ s', ∑ mu ∈ s, π' mu' (f (π mu x)) = π' mu' (f x) := by
      intro mu' _

      rw [← map_sum, ← map_sum, h5]
    rw [Finset.sum_congr rfl this, h5']
  have hwt : ∀ mu' mu, (π' mu' ∘ₗ f ∘ₗ π mu) ∈ weightSp (homRepresentation (restrictRepresentation E L hL) E) (mu' - mu) := by
    intro mu' mu
    rw [mem_weightSp_iff_diagonal_apply]
    intro c
    ext x
    simp only [homRepresentation_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      (mem_weightSp_iff_diagonal_apply E mu' _).1 (h4' mu' _) c, weightProjection_diagonal_apply_eq_smul _ hres mu (π mu) (h1 mu) c x, map_smul,
      Pi.sub_apply, Int.cast_sub, sub_smul, LinearMap.sub_apply]
  have hcoe : ∀ mu, L.subtype ∘ₗ π mu = π' mu ∘ₗ L.subtype := by
    intro mu
    refine linearMap_ext_on_weightSpaces _ hres _ _ fun nu y hy => ?_
    have hy' : (y : W) ∈ weightSp E nu := (restrict_mem_weightSpace_iff E L hL nu y).1 hy
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    by_cases h : nu = mu
    · subst h; rw [(h1 nu).1 y hy, (h1' nu).1 _ hy']
    · rw [(h1 mu).2 nu h y hy, (h1' mu).2 nu h _ hy']; rfl
  have hmem : ∀ mu' mu, (π' mu' ∘ₗ f ∘ₗ π mu) ∈ homLattice M L := by
    intro mu' mu x hx
    have hx1 : ((π mu x : L) : W) ∈ M := by
      have := congrArg (fun g : L →ₗ[KK O] W => g x) (hcoe mu)
      simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
      rw [this]
      exact weightProjection_preserves_lattice E hE M hM mu (π' mu) (h1' mu) _ hx
    exact weightProjection_preserves_lattice E hE M hM mu' (π' mu') (h1' mu') _ (hf _ hx1)

  rw [hdec, map_sum]
  refine Submodule.sum_mem _ fun mu' _ => ?_

  rw [map_sum]
  refine Submodule.sum_mem _ fun mu _ => ?_
  rw [binomial_diagonal_apply_weight _ a (mu' - mu) _ (hwt mu' mu) k]
  exact int_smul_mem_lattice _ _ (hmem mu' mu)

theorem mem_homLattice_iff_basis (M : Submodule O W) (L : Submodule (KK O) W) {d : ℕ} (b : Module.Basis (Fin d) (KK O) L)
    (hbM : ∀ i, ((b i : L) : W) ∈ M)
    (hbc : ∀ x : L, (x : W) ∈ M → ∀ i, ∃ o : O, b.coord i x = algebraMap O (KK O) o) (f : L →ₗ[KK O] W) :
    f ∈ homLattice M L ↔ ∀ i, f (b i) ∈ M := by
  constructor
  · intro hf i
    exact hf (b i) (hbM i)
  · intro hf
    show ∀ x : L, (x : W) ∈ M → f x ∈ M
    intro x hx
    choose o ho using hbc x hx
    have hx' : x = ∑ i, b.coord i x • b i := by
      simp only [Module.Basis.coord_apply]
      exact (b.sum_repr x).symm

    rw [hx', map_sum]
    refine M.sum_mem fun i _ => ?_
    rw [map_smul, ho i, algebraMap_smul]
    exact M.smul_mem (o i) (hf i)

end lat

theorem hom_lattice_dividedPower_stable : HomLatticeDividedPowerStable := by
  intro O _ _ _ _ n W _ _ _ _ _ E hE M hM hMQ L hL
  obtain ⟨d, b, hbM, hbc⟩ := lattice_adapted_basis_exists O W M hM.2 hMQ L
  have hiff := mem_homLattice_iff_basis M L b hbM hbc
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro u (⟨a, c, k, hac, rfl⟩ | ⟨a, k, rfl⟩) f hf
    · exact homLattice_dividedPower_stable E M hM.1 L hL a c hac k f hf
    · exact homLattice_binomial_stable E hE M hM.1 L hL a k f hf
  · have : homLattice M L = (Submodule.pi Set.univ fun _ : Fin d => M).map
        ((b.constr (KK O)).toLinearMap.restrictScalars O) := by
      ext f
      rw [hiff]
      constructor
      · intro hf
        exact ⟨fun i => f (b i), fun i _ => hf i, b.constr_self (KK O) f⟩
      · rintro ⟨y, hy, rfl⟩ i
        have : (b.constr (KK O) y) (b i) = y i := b.constr_basis (KK O) y i
        simpa [this] using hy i trivial
    rw [this]
    exact (Submodule.fg_pi fun _ => hM.2).map _
  · rw [eq_top_iff]
    intro f _
    choose a ha hax using fun i => exists_clear_denominators_alt M (f (b i)) (by rw [hMQ]; trivial)
    have hA : (∏ i, a i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => ha i
    have hA1 : algebraMap O (KK O) (∏ i, a i) ≠ 0 := by
      simpa using (IsFractionRing.injective O (KK O)).ne hA
    have h1 : (∏ i, a i) • f ∈ homLattice M L := by
      rw [hiff]
      intro i
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem a (Finset.mem_univ i)
      rw [LinearMap.smul_apply, hc, mul_comm, mul_smul]
      exact M.smul_mem _ (hax i)
    have h2 : f = (algebraMap O (KK O) (∏ i, a i))⁻¹ • ((∏ i, a i) • f) := by
      rw [← algebraMap_smul (KK O) (∏ i, a i) f, smul_smul, inv_mul_cancel₀ hA1, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem fock_form_finset_sum {σ : Type} (F G : MvPolynomial σ K) (s : Finset (σ →₀ ℕ)) (hs : F.support ⊆ s) :
    fock F G = ∑ m ∈ s, F.coeff m * G.coeff m * (expFact m : K) := by
  unfold fock
  refine Finset.sum_subset hs ?_
  intro m _ hm
  rw [MvPolynomial.mem_support_iff, not_not] at hm
  simp [hm]

theorem fock_form_symm {σ : Type} (F G : MvPolynomial σ K) : fock F G = fock G F := by
  classical
  rw [fock_form_finset_sum F G (F.support ∪ G.support) Finset.subset_union_left,
    fock_form_finset_sum G F (F.support ∪ G.support) Finset.subset_union_right]
  exact Finset.sum_congr rfl (fun m _ => by ring)

theorem fock_form_add_right {σ : Type} (F G G' : MvPolynomial σ K) : fock F (G + G') = fock F G + fock F G' := by
  unfold fock
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun m _ => by rw [MvPolynomial.coeff_add]; ring)

theorem fock_form_smul_right {σ : Type} (c : K) (F G : MvPolynomial σ K) : fock F (c • G) = c • fock F G := by
  unfold fock
  rw [smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun m _ => by rw [MvPolynomial.coeff_smul, smul_eq_mul]; ring)

def fockBilinear (K : Type) [Field K] (σ : Type) : MvPolynomial σ K →ₗ[K] MvPolynomial σ K →ₗ[K] K :=
  LinearMap.mk₂ K (fun F G => fock F G)
    (fun F F' G => by
      rw [fock_form_symm, fock_form_add_right, fock_form_symm G F, fock_form_symm G F'])
    (fun c F G => by rw [fock_form_symm, fock_form_smul_right, fock_form_symm G F])
    (fun F G G' => fock_form_add_right F G G')
    (fun c F G => fock_form_smul_right c F G)

theorem fockBilinear_apply {σ : Type} (F G : MvPolynomial σ K) : fockBilinear K σ F G = fock F G := rfl

theorem fock_form_monomial {σ : Type} (m : σ →₀ ℕ) (c : K) (G : MvPolynomial σ K) :
    fock (monomial m c) G = c * G.coeff m * (expFact m : K) := by
  classical
  rw [fock_form_finset_sum _ G {m} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl]

theorem exponent_factorial_add_single_one {σ : Type} [Fintype σ] (u : σ →₀ ℕ) (v : σ) :
    expFact (u + Finsupp.single v 1) = (u v + 1) * expFact u := by
  classical
  unfold expFact
  rw [Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero),
    Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero),
    Fintype.prod_eq_mul_prod_compl v, Fintype.prod_eq_mul_prod_compl v (fun i => (u i).factorial)]
  have h1 : ∀ i ∈ ({v}ᶜ : Finset σ),
      ((u + Finsupp.single v 1 : σ →₀ ℕ) i).factorial = (u i).factorial := by
    intro i hi
    rw [Finset.mem_compl, Finset.mem_singleton] at hi
    simp [Finsupp.single_apply, Ne.symm hi]
  rw [Finset.prod_congr rfl h1]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  ring

theorem fock_mul_adjoint_pderiv {σ : Type} [Fintype σ] (v : σ) (F G : MvPolynomial σ K) :
    fock (X v * F) G = fock F (pderiv v G) := by
  classical
  have addL : ∀ A B C : MvPolynomial σ K, fock (A + B) C = fock A C + fock B C := by
    intro A B C
    rw [fock_form_symm, fock_form_add_right, fock_form_symm C A, fock_form_symm C B]
  induction F using MvPolynomial.induction_on' with
  | monomial m c =>
    induction G using MvPolynomial.induction_on' with
    | monomial n d =>
      rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, MvPolynomial.pderiv_monomial,
        fock_form_monomial, fock_form_monomial, MvPolynomial.coeff_monomial,
        MvPolynomial.coeff_monomial, add_comm (Finsupp.single v 1) m, exponent_factorial_add_single_one]
      by_cases h : n = m + Finsupp.single v 1
      · subst h
        simp only [add_tsub_cancel_right, if_true, Finsupp.add_apply, Finsupp.single_eq_same]
        push_cast
        ring
      · rw [if_neg h]
        by_cases h' : n - Finsupp.single v 1 = m
        · have hv : n v = 0 := by
            by_contra hv
            apply h
            rw [← h', tsub_add_cancel_of_le]
            exact Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hv)
          simp [h', hv]
        · simp [h']
    | add G1 G2 h1 h2 => rw [fock_form_add_right, map_add (f := _), fock_form_add_right, h1, h2]
  | add F1 F2 h1 h2 => rw [mul_add, addL, addL, h1, h2]

theorem fock_pderiv_adjoint_mul {σ : Type} [Fintype σ] (v : σ) (F G : MvPolynomial σ K) :
    fock (pderiv v F) G = fock F (X v * G) := by
  rw [fock_form_symm, ← fock_mul_adjoint_pderiv, fock_form_symm]

theorem fock_form_contravariant (LL : Letters ι) (S : Set ι) (a b : Fin n) (F G : MvPolynomial (ι × Fin n) K) :
    fockBilinear K (ι × Fin n) (glOps K n LL S a b F) G = fockBilinear K (ι × Fin n) F (glOps K n LL S b a G) := by
  classical

  simp only [glOps, glAct, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  split_ifs with h1 h2
  · simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, fockBilinear_apply]
    rw [fock_mul_adjoint_pderiv, fock_pderiv_adjoint_mul]
  · simp only [LinearMap.neg_apply, map_neg, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      Derivation.coeFn_coe, fockBilinear_apply]
    rw [fock_mul_adjoint_pderiv, fock_pderiv_adjoint_mul]
  · simp

theorem polynomial_representation_holds : PolynomialGLRepresentation := by
  intro K _ _ ι _ n LL
  exact ⟨fun S => polynomial_isGLRep LL S, fun S S' hd a b c d => disjoint_letters_commute LL S S' hd a b c d,
    fun S S' hs a b => gl_operator_union_add LL S S' hs a b, fun S d a b F hF => gl_operator_preserves_multidegree LL S d a b F hF,
    fun d => homogeneous_multidegree_findim d, fun S mu F hF m hm => weight_vector_monomial_weight LL S mu F hF m hm,
    ⟨fockBilinear K (ι × Fin n), fun F G => rfl, fun S a b F G => fock_form_contravariant LL S a b F G⟩⟩

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem zpow_finset_sum_root_weights {G α : Type*} [CommGroup G] (u : G) (s : Finset α) (f : α → ℤ) :
    u ^ (∑ i ∈ s, f i) = ∏ i ∈ s, u ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add, ih]

theorem torus_acts_through_weight : TorusActsThroughWeight := by
  intro R B _ _ ι _ LL n S φ D m c
  classical
  have hu : (∏ v : ι × Fin n, (if v.1 ∈ S then (if LL.vec v.1 then D v.2 else (D v.2)⁻¹) else 1 : Bˣ) ^ (m v)) = ∏ a, D a ^ (wtS LL S m a) := by
    simp only [wtS, zpow_finset_sum_root_weights]
    rw [Fintype.prod_prod_type_right]
    refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun l _ => ?_
    split_ifs <;> simp [zpow_neg, zpow_natCast, inv_pow]
  have hU : (∏ v : ι × Fin n, (((if v.1 ∈ S then (if LL.vec v.1 then D v.2 else (D v.2)⁻¹) else 1 : Bˣ) : Bˣ) : B) ^ (m v)) = ((∏ a, D a ^ (wtS LL S m a) : Bˣ) : B) := by
    rw [← hu, Units.coe_prod]
    simp only [Units.val_pow_eq_pow_val]
  simp only [matrixSubst, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial, RingHom.coe_comp,
    Function.comp_apply]
  rw [Finsupp.prod_congr (g2 := fun v e => (MvPolynomial.C (((if v.1 ∈ S then (if LL.vec v.1 then D v.2 else (D v.2)⁻¹) else 1 : Bˣ) : Bˣ) : B) * X v) ^ e) ?_]
  · rw [Finsupp.prod_fintype _ _ (fun _ => by simp),
      Finset.prod_congr rfl (fun v _ => mul_pow _ _ _), Finset.prod_mul_distrib,
      MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => by simp), ← hU]
    simp only [map_mul, map_prod, map_pow]
    ring
  · intro v _
    congr 1
    split_ifs with h1 h2
    · rw [Finset.sum_eq_single v.2 (fun b _ hb => by simp [Matrix.diagonal_apply, hb, Ne.symm hb])
        (fun h => absurd (Finset.mem_univ _) h)]
      simp [Matrix.diagonal_apply]
    · rw [Finset.sum_eq_single v.2 (fun b _ hb => by simp [Matrix.diagonal_apply, hb, Ne.symm hb])
        (fun h => absurd (Finset.mem_univ _) h)]
      simp [Matrix.diagonal_apply]
    · simp

theorem specialise_coefficientMap {R : Type*} [CommRing R] {n : ℕ} {K : Type*} [CommRing K] (φ : R →+* K)
    {g0 g0inv : Matrix (Fin n) (Fin n) K} (h : g0 * g0inv = 1) :
    (mul_sp φ g0 g0inv h).comp (coefficientMap R n) = φ := by
  ext r
  simp only [coefficientMap, RingHom.comp_apply, mul_sp_alg, genericMatrixEvaluation, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_C]

theorem specialise_genericMatrix {R : Type*} [CommRing R] {n : ℕ} {K : Type*} [CommRing K] (φ : R →+* K)
    {g0 g0inv : Matrix (Fin n) (Fin n) K} (h : g0 * g0inv = 1) :
    (genericMatrixRootWeights R n).map (mul_sp φ g0 g0inv h) = g0 := by
  ext i k
  have hg := congrFun (congrFun (generic_matrix_evaluation_eq (j := φ) (g0 := g0)) i) k
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at hg
  simp only [genericMatrixRootWeights, Matrix.map_apply, mul_sp_alg]
  exact hg

theorem specialise_genericMatrixInverse {R : Type*} [CommRing R] {n : ℕ} {K : Type*} [CommRing K] (φ : R →+* K)
    {g0 g0inv : Matrix (Fin n) (Fin n) K} (h : g0 * g0inv = 1) :
    (genericMatrixInverse R n).map (mul_sp φ g0 g0inv h) = g0inv := by
  have hadj : g0.adjugate = g0.det • g0inv := by
    calc g0.adjugate = g0.adjugate * (g0 * g0inv) := by rw [h, Matrix.mul_one]
      _ = (g0.adjugate * g0) * g0inv := (Matrix.mul_assoc _ _ _).symm
      _ = g0.det • g0inv := by rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have hu := mul_sp_inv (j := φ) (g0 := g0) (g0inv := g0inv) h
  ext i k
  have hA := congrFun (congrFun (RingHom.map_adjugate (genericMatrixEvaluation φ g0) (genMat R n)) i) k
  rw [generic_matrix_evaluation_eq] at hA
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at hA
  simp only [genericMatrixInverse, Matrix.map_apply, map_mul, mul_sp_alg, hA, hadj, Matrix.smul_apply, smul_eq_mul]
  linear_combination (g0inv i k) * hu

theorem generic_monomials_specialise : GenericMonomialsSpecialise := by
  intro R _ ι _ LL n S k1 _ φ g0 g0inv h G
  have hAi : ∀ a b, mul_sp φ g0 g0inv h (genericMatrixInverse R n a b) = g0inv a b := fun a b => by
    have e := congrFun (congrFun (specialise_genericMatrixInverse φ h) a) b
    simpa only [Matrix.map_apply] using e
  have hAg : ∀ a b, mul_sp φ g0 g0inv h (genericMatrixRootWeights R n a b) = g0 a b := fun a b => by
    have e := congrFun (congrFun (specialise_genericMatrix φ h) a) b
    simpa only [Matrix.map_apply] using e
  have hAc : ∀ r, mul_sp φ g0 g0inv h (coefficientMap R n r) = φ r := fun r =>
    RingHom.congr_fun (specialise_coefficientMap φ h) r
  have e : (MvPolynomial.map (mul_sp φ g0 g0inv h)).comp
      (matrixSubst LL S (coefficientMap R n) (genericMatrixInverse R n) (genericMatrixRootWeights R n)) = matrixSubst LL S φ g0inv g0 := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, matrixSubst, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C,
        MvPolynomial.map_C, hAc]
    · intro w
      simp only [RingHom.comp_apply, matrixSubst, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
      split_ifs <;> simp [map_sum, hAi, hAg]
  have key : matrixSubst LL S φ g0inv g0 G = MvPolynomial.map (mul_sp φ g0 g0inv h) (genericTranslate LL S G) := by
    rw [← e]
    rfl
  rw [key]
  exact MvPolynomial.support_map_subset _ _

end Formalism.MainNotions.G.GLWeightTheory
end
end
