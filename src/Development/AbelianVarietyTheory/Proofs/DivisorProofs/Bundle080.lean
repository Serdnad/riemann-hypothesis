module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

@[expose] public section

section

open Polynomial
namespace GlobalTheory

private lemma rank_submatrix_fromBlocks_one_zero_eq {F : Type} [Field F] {m : Type} [Fintype m] [DecidableEq m]
    (a b : ℕ) (e : m ≃ Fin a ⊕ Fin b) :
    ((Matrix.fromBlocks (1 : Matrix (Fin a) (Fin a) F) 0 0 (0 : Matrix (Fin b) (Fin b) F)).submatrix
      e e).rank = a := by
  classical
  have hd : (Matrix.fromBlocks (1 : Matrix (Fin a) (Fin a) F) 0 0 (0 : Matrix (Fin b) (Fin b) F)) =
      Matrix.diagonal (Sum.elim (fun _ => (1 : F)) (fun _ => 0)) := by
    rw [← Matrix.fromBlocks_diagonal]
    simp
  rw [Matrix.rank_submatrix, hd, Matrix.rank_diagonal]
  simp [Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]


open Matrix in
theorem eigDim_rank_map {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) : (M.map φ).rank = M.rank := by
  classical
  obtain ⟨V, U, e, hV, hU, h⟩ := Matrix.exists_rank_normal_form M
  have hVd : IsUnit (V.map φ).det := by
    rw [show (V.map φ).det = φ V.det from (RingHom.map_det φ V).symm]
    exact ((Matrix.isUnit_iff_isUnit_det V).mp hV).map φ
  have hUd : IsUnit (U.map φ).det := by
    rw [show (U.map φ).det = φ U.det from (RingHom.map_det φ U).symm]
    exact ((Matrix.isUnit_iff_isUnit_det U).mp hU).map φ
  have h' : V.map φ * M.map φ * U.map φ =
      (Matrix.fromBlocks (1 : Matrix (Fin M.rank) (Fin M.rank) L) 0 0
        (0 : Matrix (Fin (Fintype.card n - M.rank)) (Fin (Fintype.card n - M.rank)) L)).submatrix
          e e := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, h]
    simp [← Matrix.submatrix_map, Matrix.fromBlocks_map]
  calc (M.map φ).rank = (V.map φ * M.map φ * U.map φ).rank := by
        rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hUd,
          Matrix.rank_mul_eq_right_of_isUnit_det _ _ hVd]
    _ = M.rank := by rw [h']; exact rank_submatrix_fromBlocks_one_zero_eq _ _ e

private lemma finrank_ker_toLin'_add_rank_eq_card {L : Type} [Field L] {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n L) :
    Module.finrank L (LinearMap.ker (Matrix.toLin' A)) + A.rank = Fintype.card n := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' A)
  rw [Matrix.toLin'_apply'] at h ⊢
  rw [Module.finrank_pi] at h
  rw [← Matrix.finrank_range_mulVecLin]
  omega

theorem eigDim_ker_map {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) :
    Module.finrank L (LinearMap.ker (Matrix.toLin' (M.map φ))) =
      Module.finrank K (LinearMap.ker (Matrix.toLin' M)) := by
  have h1 := finrank_ker_toLin'_add_rank_eq_card (M.map φ)
  have h2 := finrank_ker_toLin'_add_rank_eq_card M
  rw [eigDim_rank_map] at h1
  omega

theorem eigDim_aeval_toLin' {K : Type} [Field K] {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) (f : K[X]) :
    aeval (Matrix.toLin' M) f = Matrix.toLin' (aeval M f) :=
  Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv' : Matrix n n K ≃ₐ[K] _) M f

theorem eigDim_aeval_map {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) (f : K[X]) :
    (aeval M f).map φ = aeval (M.map φ) (f.map φ) := by
  have h : (φ.mapMatrix : Matrix n n K →+* Matrix n n L).comp (algebraMap K (Matrix n n K)) =
      (algebraMap L (Matrix n n L)).comp φ := by
    ext r i j
    by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, hij]
  change φ.mapMatrix (Polynomial.eval₂ (algebraMap K (Matrix n n K)) M f) =
    Polynomial.eval₂ (algebraMap L (Matrix n n L)) (M.map φ) (f.map φ)
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_map, h]
  rfl

theorem eigDim_ker_aeval_map {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : Type}
    [Fintype n] [DecidableEq n] (M : Matrix n n K) (f : K[X]) :
    Module.finrank L (LinearMap.ker (aeval (Matrix.toLin' (M.map φ)) (f.map φ))) =
      Module.finrank K (LinearMap.ker (aeval (Matrix.toLin' M) f)) := by
  rw [eigDim_aeval_toLin', eigDim_aeval_toLin', ← eigDim_aeval_map, eigDim_ker_map]

theorem eigDim_ker_mul {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) {p q : K[X]} (h : IsCoprime p q) :
    Module.finrank K (LinearMap.ker (aeval T (p * q))) =
      Module.finrank K (LinearMap.ker (aeval T p)) +
        Module.finrank K (LinearMap.ker (aeval T q)) := by
  rw [← Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime T h]
  have hd := Polynomial.disjoint_ker_aeval_of_isCoprime T h
  have hs := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (aeval T p))
    (LinearMap.ker (aeval T q))
  rw [hd.eq_bot] at hs
  simpa using hs

theorem eigDim_ker_prod {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (s : Finset K) :
    Module.finrank K (LinearMap.ker (aeval T (∏ z ∈ s, (X - C z)))) =
      ∑ z ∈ s, Module.finrank K (LinearMap.ker (aeval T (X - C z))) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, map_one, Module.End.one_eq_id, LinearMap.ker_id]
    simp
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, eigDim_ker_mul T, ih]
    refine IsCoprime.prod_right fun z hz => ?_
    refine Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr ?_).isUnit
    rintro rfl
    exact ha hz

theorem finrank_ker_aeval_eq_natDegree_mul_finrank_eigenspace :
    ∀ (F : Type) [Field F] [Finite F] (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι F) (f : F[X]) (y : AlgebraicClosure F), Irreducible f → aeval y f = 0 → Module.finrank F (LinearMap.ker (aeval (Matrix.toLin' M) f)) = f.natDegree * Module.finrank (AlgebraicClosure F) (Module.End.eigenspace (Matrix.toLin' (M.map (algebraMap F (AlgebraicClosure F)))) y) := by
  intro F _ _ ι _ _ M f y hf hy
  classical
  rw [← eigDim_ker_aeval_map (algebraMap F (AlgebraicClosure F)) M f]
  set g := f.map (algebraMap F (AlgebraicClosure F)) with hg
  set T := Matrix.toLin' (M.map (algebraMap F (AlgebraicClosure F))) with hT
  have hsep : g.Separable := (PerfectField.separable_of_irreducible hf).map
  have hne : g ≠ 0 := Polynomial.map_ne_zero hf.ne_zero
  have hnd := Polynomial.nodup_roots hsep
  have hcard : Multiset.card g.roots = g.natDegree :=
    (IsAlgClosed.splits g).natDegree_eq_card_roots.symm
  have hfac := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have hprod : (g.roots.map fun a => X - C a).prod = ∏ a ∈ g.roots.toFinset, (X - C a) := by
    rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]
  have hlc : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hne
  have hker : aeval T g = g.leadingCoeff • aeval T (∏ a ∈ g.roots.toFinset, (X - C a)) := by
    conv_lhs => rw [← hfac, hprod]
    rw [map_mul, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  have hterm : ∀ a ∈ g.roots.toFinset, Module.finrank (AlgebraicClosure F) (LinearMap.ker (aeval T (X - C a))) =
      Module.finrank (AlgebraicClosure F) (Module.End.eigenspace T y) := by
    intro a ha
    have haroot : aeval a f = 0 := by
      have h0 := Polynomial.IsRoot.eq_zero ((Polynomial.mem_roots hne).mp (Multiset.mem_toFinset.mp ha))
      rwa [hg, Polynomial.eval_map_algebraMap] at h0
    have hmin : minpoly F a = minpoly F y := by
      rw [← minpoly.eq_of_irreducible hf haroot, ← minpoly.eq_of_irreducible hf hy]
    obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.mp ((Normal.minpoly_eq_iff_mem_orbit (AlgebraicClosure F)).mp hmin)
    rw [AlgEquiv.smul_def] at hσ
    have hmat : (M.map (algebraMap F (AlgebraicClosure F)) - y • (1 : Matrix ι ι (AlgebraicClosure F))).map (σ : AlgebraicClosure F →+* AlgebraicClosure F) = M.map (algebraMap F (AlgebraicClosure F)) - a • 1 := by
      ext i j
      by_cases hij : i = j <;> simp [hij, hσ]
    have e1 : aeval T (X - C a) = Matrix.toLin' (M.map (algebraMap F (AlgebraicClosure F)) - a • 1) := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, hT,
        map_sub, map_smul, Matrix.toLin'_one, Module.End.one_eq_id]
    have e2 : T - y • 1 = Matrix.toLin' (M.map (algebraMap F (AlgebraicClosure F)) - y • 1) := by
      rw [hT, map_sub, map_smul, Matrix.toLin'_one, Module.End.one_eq_id]
    rw [Module.End.eigenspace_def, e1, e2, ← hmat, eigDim_ker_map]
  rw [hker, LinearMap.ker_smul _ _ hlc, eigDim_ker_prod, Finset.sum_congr rfl hterm,
    Finset.sum_const, smul_eq_mul, Multiset.toFinset_card_of_nodup hnd, hcard, hg,
    Polynomial.natDegree_map]

end GlobalTheory
end

section

namespace GlobalTheory

theorem mem_smul_of_forall_char_pow_eq_one
    (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (F : Type) [Field F]
    [IsAlgClosed F] (k : ℕ) (hk : (k : F) ≠ 0) (d : X)
    (hd : ∀ τ : Multiplicative X →* Fˣ, τ ^ k = 1 → τ (Multiplicative.ofAdd d) = 1) :
    ∃ z : X, d = k • z := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  by_contra hne
  push_neg at hne
  have hex : ∃ i, ¬ (k : ℤ) ∣ b.repr d i := by
    by_contra h
    push_neg at h
    apply hne (∑ i, (b.repr d i / k) • b i)
    apply b.repr.injective
    ext j
    rw [← natCast_zsmul]

    simp [map_sum, Finsupp.single_apply, Int.mul_ediv_cancel' (h j)]
  obtain ⟨i, hi⟩ := hex
  have hk0 : k ≠ 0 := by rintro rfl; exact hk (by simp)
  haveI : NeZero (k : F) := ⟨hk⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F k
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hk0
  let u : Fˣ := Units.mk0 ζ hζ0
  have hu : IsPrimitiveRoot u k := IsPrimitiveRoot.coe_units_iff.mp (by simpa [u] using hζ)
  let τ : Multiplicative X →* Fˣ :=
    (zpowersHom Fˣ u).comp (AddMonoidHom.toMultiplicative (b.coord i).toAddMonoidHom)
  have hτ : ∀ x : X, τ (Multiplicative.ofAdd x) = u ^ (b.repr x i) := by
    intro x; simp [τ]
  have hτk : τ ^ k = 1 := by
    ext x
    show (τ x ^ k : Fˣ).val = (1 : Fˣ).val
    congr 1
    rw [← ofAdd_toAdd x, hτ, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      hu.pow_eq_one, one_zpow]
  have h1 := hd τ hτk
  rw [hτ] at h1
  exact hi ((hu.zpow_eq_one_iff_dvd _).1 h1)

end GlobalTheory
end

section

namespace GlobalTheory

def FieldCopy (k : Type) : Type := k

instance FieldCopy.instField (k : Type) [h : Field k] : Field (FieldCopy k) := h

instance FieldCopy.instIsAlgClosed (k : Type) [Field k] [h : IsAlgClosed k] :
    IsAlgClosed (FieldCopy k) := h

theorem exists_ringEquiv_extending_of_ker_le :
    ∀ (k : Type) [Field k] [IsAlgClosed k], (∀ x : k, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1) →
      ∀ (R : Subring k) (J : Type) (α β : J → k),
        (∀ p : MvPolynomial J R, MvPolynomial.aeval α p = 0 → MvPolynomial.aeval β p = 0) →
        ∃ φ : k ≃+* k, (∀ r ∈ R, φ r = r) ∧ ∀ j, φ (α j) = β j := by
  intro k _ _ hroot R J α β hker
  let eα : MvPolynomial J R →ₐ[R] k := MvPolynomial.aeval α
  let eβ : MvPolynomial J R →ₐ[R] k := MvPolynomial.aeval β
  let S : Subalgebra R k := eα.range
  have hle : ∀ p ∈ RingHom.ker eα.rangeRestrict, eβ p = 0 := by
    intro p hp
    rw [RingHom.mem_ker] at hp
    apply hker
    have := congrArg Subtype.val hp
    simpa using this
  let ψ0 : S →ₐ[R] k := (Ideal.Quotient.liftₐ (RingHom.ker eα.rangeRestrict) eβ hle).comp
    (Ideal.quotientKerAlgEquivOfSurjective (AlgHom.rangeRestrict_surjective eα)).symm.toAlgHom
  have hψ0 : ∀ p, ψ0 (eα.rangeRestrict p) = eβ p := by
    intro p
    have h1 : (Ideal.quotientKerAlgEquivOfSurjective (AlgHom.rangeRestrict_surjective eα)).symm
        (eα.rangeRestrict p) = Ideal.Quotient.mk _ p := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    simp only [ψ0, AlgHom.comp_apply]
    erw [h1]
    rfl
  let ψ : S →+* FieldCopy k := ψ0.toRingHom
  have hψinj : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro s hs
    by_contra hne
    have hne' : (s : k) ≠ 0 := fun h => hne (Subtype.ext h)
    obtain ⟨n, hn, hsn⟩ := hroot _ hne'
    have hsn' : s ^ n = 1 := Subtype.ext (by simpa using hsn)
    have : ψ s ^ n = 1 := by rw [← map_pow, hsn', map_one]
    rw [hs, zero_pow (by omega)] at this
    exact zero_ne_one this
  letI : Algebra S (FieldCopy k) := ψ.toAlgebra
  haveI : Module.IsTorsionFree S (FieldCopy k) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_
    rw [Algebra.smul_def, mul_eq_zero] at h
    rcases h with h | h
    · left
      exact hψinj (h.trans (map_zero ψ).symm)
    · exact Or.inr h
  haveI : Algebra.IsIntegral S k := by
    constructor
    intro x
    by_cases hx : x = 0
    · rw [hx]; exact isIntegral_zero
    · obtain ⟨n, hn, hxn⟩ := hroot x hx
      refine ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 (by omega), ?_⟩
      simp [hxn]
  let θ' : k →ₐ[S] FieldCopy k := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let θ : k →+* k := θ'.toRingHom
  have hθS : ∀ s : S, θ (s : k) = ψ0 s := by
    intro s
    have := θ'.commutes s
    exact this
  have hθinj : Function.Injective θ := θ.injective
  have hθsurj : Function.Surjective θ := by
    intro y
    by_cases hy : y = 0
    · exact ⟨0, by rw [hy, map_zero]⟩
    obtain ⟨n, hn, hyn⟩ := hroot y hy
    let T := Polynomial.nthRootsFinset n (1 : k)
    have hmem : ∀ x : k, x ∈ T ↔ x ^ n = 1 := fun x => Polynomial.mem_nthRootsFinset (by omega) 1
    let f : T → T := fun t => ⟨θ t, (hmem _).2 (by rw [← map_pow, (hmem _).1 t.2, map_one])⟩
    have hf : Function.Injective f := by
      intro a b hab
      exact Subtype.ext (hθinj (congrArg Subtype.val hab))
    obtain ⟨t, ht⟩ := Finite.injective_iff_surjective.1 hf ⟨y, (hmem y).2 hyn⟩
    exact ⟨t, congrArg Subtype.val ht⟩
  refine ⟨RingEquiv.ofBijective θ ⟨hθinj, hθsurj⟩, ?_, ?_⟩
  · intro r hr
    have hrS : (r : k) ∈ S := ⟨MvPolynomial.C ⟨r, hr⟩, by simp [eα]; rfl⟩
    show θ r = r
    have h2 : (⟨r, hrS⟩ : S) = eα.rangeRestrict (MvPolynomial.C ⟨r, hr⟩) :=
      Subtype.ext (by simp [eα]; rfl)
    rw [show r = ((⟨r, hrS⟩ : S) : k) from rfl, hθS, h2, hψ0]
    simp [eβ]
  · intro j
    show θ (α j) = β j
    have h2 : (⟨α j, ⟨MvPolynomial.X j, by simp [eα]⟩⟩ : S) = eα.rangeRestrict (MvPolynomial.X j) :=
      Subtype.ext (by simp [eα])
    rw [show α j = ((⟨α j, ⟨MvPolynomial.X j, by simp [eα]⟩⟩ : S) : k) from rfl, hθS, h2, hψ0]
    simp [eβ]

end GlobalTheory
end

section

universe u_1 u_2 u_3

namespace GlobalTheory.InjectiveAlgebraHomExistence

theorem exists_algHom_of_injective {A : Type u_1} {B : Type u_2} {K : Type u_3}
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Field K] [IsAlgClosed K]
    [Algebra A B] [Algebra A K] [Algebra.IsIntegral A B]
    (hB : Function.Injective (algebraMap A B)) (hK : Function.Injective (algebraMap A K)) :
    Nonempty (B →ₐ[A] K) := by
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective _ _).2 hB
  haveI : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective _ _).2 hK
  exact ⟨IsAlgClosed.lift⟩

theorem exists_ringHom_comp_algebraMap_eq {R : Type u_1} {S : Type u_2} {K : Type u_3}
    [CommRing R] [CommRing S] [Field K] [IsAlgClosed K] [Algebra R S] [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S)) (ψ : R →+* K) :
    ∃ x : S →+* K, x.comp (algebraMap R S) = ψ := by
  have hp : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := S)
    (RingHom.ker ψ) ⊥ (by
      intro r hr
      have h0 : algebraMap R S r = 0 := by simpa using hr
      have : r = 0 := hinj (by simpa using h0)
      simp [this])
  let f : R ⧸ RingHom.ker ψ →+* S ⧸ Q := Ideal.quotientMap Q (algebraMap R S) hQp.ge
  have hf : Function.Injective f := Ideal.quotientMap_injective' hQp.le
  letI : Algebra (R ⧸ RingHom.ker ψ) (S ⧸ Q) := f.toAlgebra
  letI : Algebra (R ⧸ RingHom.ker ψ) K := (RingHom.kerLift ψ).toAlgebra
  haveI : Algebra.IsIntegral (R ⧸ RingHom.ker ψ) (S ⧸ Q) := by
    constructor
    intro y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨P, hP, hs⟩ := Algebra.IsIntegral.isIntegral (R := R) s
    refine ⟨P.map (Ideal.Quotient.mk _), hP.map _, ?_⟩
    have hc : (algebraMap (R ⧸ RingHom.ker ψ) (S ⧸ Q)).comp (Ideal.Quotient.mk _)
        = (Ideal.Quotient.mk Q).comp (algebraMap R S) := by
      ext r
      rfl
    rw [Polynomial.eval₂_map, hc, ← Polynomial.hom_eval₂, hs, map_zero]
  obtain ⟨g⟩ : Nonempty ((S ⧸ Q) →ₐ[R ⧸ RingHom.ker ψ] K) :=
    exists_algHom_of_injective hf (RingHom.kerLift_injective ψ)
  refine ⟨(g : (S ⧸ Q) →+* K).comp (Ideal.Quotient.mk Q), ?_⟩
  ext r
  have := g.commutes (Ideal.Quotient.mk _ r)
  exact this

end GlobalTheory.InjectiveAlgebraHomExistence
end

section

namespace GlobalTheory.ValuationExtensionExistence

theorem exists_extension {V R K : Type} [CommRing V] [CommRing R] [IsDomain R] [Field K]
    [IsAlgClosed K] [Algebra V R] [Algebra.IsIntegral V R] [FaithfulSMul V R] (ev : V →+* K) :
    ∃ ev₁ : R →+* K, ev₁.comp (algebraMap V R) = ev := by
  classical

  have : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := R) (RingHom.ker ev) ⊥ (by
    rw [(show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective V R))]
    exact bot_le)
  have := hQ
  have : Q.LiesOver (RingHom.ker ev) := ⟨hQp.symm⟩

  let : Algebra (V ⧸ RingHom.ker ev) K := (RingHom.kerLift ev).toAlgebra
  have : Module.IsTorsionFree (V ⧸ RingHom.ker ev) K :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (RingHom.kerLift_injective ev)
  have : Module.IsTorsionFree (V ⧸ RingHom.ker ev) (R ⧸ Q) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective _ _)
  have : Algebra.IsIntegral (V ⧸ RingHom.ker ev) (R ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver Q (RingHom.ker ev)
  have : Algebra.IsAlgebraic (V ⧸ RingHom.ker ev) (R ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let f : R ⧸ Q →ₐ[V ⧸ RingHom.ker ev] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨(f : R ⧸ Q →+* K).comp (Ideal.Quotient.mk Q), ?_⟩
  ext v
  have h := f.commutes (Ideal.Quotient.mk (RingHom.ker ev) v)
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver] at h
  exact h.trans (RingHom.kerLift_mk ev v)

theorem main : ∀ (V R K : Type) [inst : CommRing V] [IsDomain V] [IsLocalRing V]
    [inst_3 : CommRing R] [IsDomain R] [IsLocalRing R] [inst_6 : Field K] [IsAlgClosed K]
    (ρ : V →+* R), Function.Injective (⇑ρ : V → R) → RingHom.Finite ρ →
      IsLocalHom ρ ∧ ∀ (ev : V →+* K), ∃ (ev₁ : R →+* K), RingHom.comp ev₁ ρ = ev := by
  intro V R K _ _ _ _ _ _ _ _ ρ hinj hfin
  have hint : ρ.IsIntegral := hfin.to_isIntegral
  refine ⟨?_, fun ev => ?_⟩
  · refine ((IsLocalRing.local_hom_tfae ρ).out 5 1).mp ?_
    exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' ρ hint _)
  · let := ρ.toAlgebra
    have : Algebra.IsIntegral V R := ⟨hint⟩
    have : FaithfulSMul V R := (faithfulSMul_iff_algebraMap_injective V R).2 hinj
    exact exists_extension ev

end GlobalTheory.ValuationExtensionExistence
end

section

namespace GlobalTheory.ReducedAdjoinRootSeparable

theorem isReduced_adjoinRoot_of_separable {k : Type} [Field k] {f : Polynomial k}
    (hf : f.Separable) : IsReduced (AdjoinRoot f) := by
  have h1 : IsRadical f := isRadical_iff_squarefree_or_zero.2 (Or.inl hf.squarefree)
  have h2 : (Ideal.span {f}).IsRadical := isRadical_iff_span_singleton.1 h1
  exact (Ideal.isRadical_iff_quotient_reduced _).1 h2

end GlobalTheory.ReducedAdjoinRootSeparable
end
