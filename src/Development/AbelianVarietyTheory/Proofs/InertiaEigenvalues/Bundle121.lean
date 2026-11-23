module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.PremisesModel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IwahoriEigenvaluesOfNewton
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle098
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle093
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle099
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle003

@[expose] public section

section

open Polynomial

namespace GlobalTheory.UnitLemma.Centraliser

theorem charpoly_dvd_pow_of_aeval_eq_zero {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (p : R[X]) (hp : aeval M p = 0) : M.charpoly ∣ p ^ Fintype.card n := by
  set a : Matrix n n R[X] := algebraMap R[X] (Matrix n n R[X]) X with ha_def
  set b : Matrix n n R[X] := (Algebra.ofId R R[X]).mapMatrix M with hb_def
  have hab : Commute a b := Algebra.commutes X b
  have key : ∀ q : R[X], ∃ H, (a - b) * H = aeval a q - aeval b q := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨H1, h1⟩ := hp
      obtain ⟨H2, h2⟩ := hq
      exact ⟨H1 + H2, by rw [mul_add, h1, h2, map_add (f := _), map_add (f := _)]; abel⟩
    | monomial k c =>
      refine ⟨algebraMap R (Matrix n n R[X]) c * ∑ i ∈ Finset.range k, a ^ i * b ^ (k - 1 - i), ?_⟩
      rw [aeval_monomial, aeval_monomial, ← mul_assoc, ← Algebra.commutes, mul_assoc, hab.mul_geom_sum₂,
        mul_sub]
  obtain ⟨H, hH⟩ := key p
  have hb : aeval b p = 0 := by
    rw [hb_def, aeval_algHom_apply, hp, map_zero]
  have ha : aeval a p = algebraMap R[X] (Matrix n n R[X]) p := by
    rw [ha_def, aeval_algebraMap_apply, aeval_X_left_apply]
  have hch : (a - b).det = M.charpoly := rfl
  refine ⟨H.det, ?_⟩
  rw [← hch, ← Matrix.det_mul, hH, hb, sub_zero, ha, Matrix.algebraMap_eq_diagonal, Matrix.det_diagonal]
  simp

theorem P_dvd_of_aeval_eq_zero {K : UQ} (B : InvAlg K) (hsep : B.P.Separable) (p : K.E[X])
    (hp : aeval B.g p = 0) : B.P ∣ p := by
  have h1 : aeval (Algebra.lmul K.E B.A B.g) p = 0 := by
    rw [aeval_algHom_apply, hp, map_zero]
  let bs := Module.finBasis K.E B.A
  have h2 : aeval (LinearMap.toMatrixAlgEquiv bs (Algebra.lmul K.E B.A B.g)) p = 0 := by
    rw [aeval_algHom_apply, h1, map_zero]
  have h3 := charpoly_dvd_pow_of_aeval_eq_zero _ p h2
  have h4 : (LinearMap.toMatrixAlgEquiv bs (Algebra.lmul K.E B.A B.g)).charpoly = B.P := by
        exact LinearMap.charpoly_toMatrix _ bs
  rw [h4] at h3
  exact hsep.squarefree.isRadical _ _ h3

theorem aeval_g_P {K : UQ} (B : InvAlg K) : aeval B.g B.P = 0 := by
  have h := LinearMap.aeval_self_charpoly (LinearMap.mulLeft K.E B.g)
  have h' : Algebra.lmul K.E B.A (aeval B.g B.P) = 0 := by
    rw [← aeval_algHom_apply]; exact h
  simpa using congrArg (fun f : Module.End K.E B.A => f 1) h'

theorem exists_aeval_eq {K : UQ} (B : InvAlg K) (hsep : B.P.Separable) (y : B.A) :
    ∃ p : K.E[X], aeval B.g p = y := by
  have hm : B.P.Monic := LinearMap.charpoly_monic _
  have hP : eval₂ (↑(Algebra.ofId K.E B.A)) B.g B.P = 0 := aeval_g_P B
  let φ := AdjoinRoot.liftAlgHom B.P (Algebra.ofId K.E B.A) B.g hP
  let pb := AdjoinRoot.powerBasis' hm
  haveI : Module.Finite K.E (AdjoinRoot B.P) := pb.finite
  have hrank : Module.finrank K.E (AdjoinRoot B.P) = Module.finrank K.E B.A := by
    rw [pb.finrank, AdjoinRoot.powerBasis'_dim]
    exact LinearMap.charpoly_natDegree _
  have hinj : Function.Injective φ.toLinearMap := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
    rw [AdjoinRoot.mk_eq_zero]
    apply P_dvd_of_aeval_eq_zero B hsep
    simpa [φ, AdjoinRoot.liftAlgHom_mk, aeval_def] using hz
  obtain ⟨z, hz⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hinj y
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  exact ⟨p, by simpa [φ, AdjoinRoot.liftAlgHom_mk, aeval_def] using hz⟩

theorem eq_zero_of_isNilpotent {K : UQ} (B : InvAlg K) (hsep : B.P.Separable) (a : B.A)
    (ha : IsNilpotent a) : a = 0 := by
  obtain ⟨p, rfl⟩ := exists_aeval_eq B hsep a
  obtain ⟨m, hm⟩ := ha
  have h1 : B.P ∣ p ^ m := P_dvd_of_aeval_eq_zero B hsep _ (by rw [map_pow, hm])
  obtain ⟨q, rfl⟩ := hsep.squarefree.isRadical m p h1
  rw [map_mul, aeval_g_P, zero_mul]

theorem eq_zero_of_trace_mul {K : UQ} (B : InvAlg K) (hsep : B.P.Separable) (a : B.A)
    (ha : ∀ y, Algebra.trace K.E B.A (a * y) = 0) : a = 0 := by
  apply eq_zero_of_isNilpotent B hsep
  let bs := Module.finBasis K.E B.A
  have hN : IsNilpotent (Algebra.leftMulMatrix bs a) := by
    apply ReciprocityTheory.L2DbarEstimates.Y.isNilpotent_of_trace_pow
    intro k hk _
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [← map_pow, ← Algebra.trace_eq_matrix_trace, pow_succ']
    exact ha _
  obtain ⟨m, hm⟩ := hN
  refine ⟨m, Algebra.leftMulMatrix_injective bs ?_⟩
  rw [map_pow, hm, map_zero]

end GlobalTheory.UnitLemma.Centraliser
end

section

open GlobalTheory.UnitLemma Polynomial

noncomputable section

namespace GlobalTheory.IwahoriRoots

open IsDedekindDomain

section Val

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {E : Type} [Field E]
  [Algebra O E] [IsFractionRing O E]

theorem valuation_unif (ϖ : O) (hϖ : Irreducible ϖ) :
    (IsDiscreteValuationRing.maximalIdeal O).valuation E (algebraMap O E ϖ) = WithZero.exp (-1 : ℤ) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton _ hϖ.ne_zero
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ)

theorem valuation_of_isUnit {u : O} (hu : IsUnit u) :
    (IsDiscreteValuationRing.maximalIdeal O).valuation E (algebraMap O E u) = 1 := by
  obtain ⟨u, rfl⟩ := hu
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  set v := IsDiscreteValuationRing.maximalIdeal O
  have h1 := v.intValuation_le_one (u : O)
  have h2 := v.intValuation_le_one ((u⁻¹ : Oˣ) : O)
  have h3 : v.intValuation (u : O) * v.intValuation ((u⁻¹ : Oˣ) : O) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = v.intValuation (u : O) * v.intValuation ((u⁻¹ : Oˣ) : O) := h3.symm
    _ ≤ v.intValuation (u : O) * 1 := by gcongr
    _ = v.intValuation (u : O) := mul_one _

end Val

theorem isUnit_diag_of_lower {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (x : GL (Fin n) O)
    (hx : ∀ i j, j < i → (x : Matrix (Fin n) (Fin n) O) i j ∈ IsLocalRing.maximalIdeal O)
    (i : Fin n) : IsUnit ((x : Matrix (Fin n) (Fin n) O) i i) := by
  have h1 : ((x : Matrix (Fin n) (Fin n) O).map (IsLocalRing.residue O)).BlockTriangular id := by
    intro a b hab
    simp only [Matrix.map_apply]
    exact (IsLocalRing.residue_eq_zero_iff _).2 (hx a b hab)
  have h2 : IsUnit ((x : Matrix (Fin n) (Fin n) O).map (IsLocalRing.residue O)).det := by
    have e : ((x : Matrix (Fin n) (Fin n) O).map (IsLocalRing.residue O)).det =
        IsLocalRing.residue O (x : Matrix (Fin n) (Fin n) O).det := (RingHom.map_det _ _).symm
    rw [e]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 x.isUnit).map _
  rw [Matrix.det_of_upperTriangular h1] at h2
  have h3 := isUnit_of_dvd_unit (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) h2
  simp only [Matrix.map_apply] at h3
  exact isUnit_of_map_unit (IsLocalRing.residue O) _ h3

theorem iwahori_roots : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (ϖ : O), Irreducible ϖ →
    ∀ (n : ℕ) (a : Fin n → ℤ), StrictAnti a → ∀ x y : GL (Fin n) O,
    (∀ i j, j < i → (x : Matrix (Fin n) (Fin n) O) i j ∈ IsLocalRing.maximalIdeal O) →
    (∀ i j, j < i → (y : Matrix (Fin n) (Fin n) O) i j ∈ IsLocalRing.maximalIdeal O) →
    ∃ r : Fin n → E, (∀ i, r i ≠ 0 ∧ val O (r i) = a i) ∧
      ((x : Matrix (Fin n) (Fin n) O).map (algebraMap O E) *
        Matrix.diagonal (fun i => algebraMap O E ϖ ^ a i) *
        (y : Matrix (Fin n) (Fin n) O).map (algebraMap O E)).charpoly = ∏ i, (X - C (r i)) := by
  intro O _ _ _ _ E _ _ _ _ ϖ hϖ n a ha x y hx hy
  have hspan := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hm : ϖ ∈ IsLocalRing.maximalIdeal O := by rw [hspan]; exact Ideal.mem_span_singleton_self ϖ
  haveI : IsAdicComplete (Ideal.span {ϖ}) O := by rw [← hspan]; infer_instance
  have hinj : Function.Injective (algebraMap O E) := IsFractionRing.injective O E
  have hϖ0 : algebraMap O E ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  obtain ⟨N, hNa⟩ : ∃ N : ℤ, ∀ i, N ≤ a i := by
    obtain ⟨N, hN⟩ := (Set.finite_range a).bddBelow
    exact ⟨N, fun i => hN ⟨i, rfl⟩⟩
  let b : Fin n → ℕ := fun i => (a i - N).toNat
  have hab : ∀ i, a i = N + b i := fun i => by
    have := hNa i
    simp only [b]
    omega
  have hb : StrictAnti b := fun i j h => by
    have := ha h
    rw [hab, hab] at this
    omega
  have hdvd : ∀ z : O, z ∈ IsLocalRing.maximalIdeal O → ϖ ∣ z := fun z hz => by
    rw [hspan] at hz
    exact Ideal.mem_span_singleton.1 hz
  set G : Matrix (Fin n) (Fin n) O :=
    (x : Matrix (Fin n) (Fin n) O) * Matrix.diagonal (fun i => ϖ ^ b i) * y with hG
  have hroot := GlobalTheory.IwahoriEigen.exists_root_of_coeff ϖ hm hb G.charpoly
    (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]) (fun j hj => by
      have := GlobalTheory.IwahoriNewtonTest.intersectionNumber_baseChange O ϖ hm n b hb x y (isUnit_diag_of_lower x hx)
        (isUnit_diag_of_lower y hy) (fun i j h => hdvd _ (hx i j h)) (fun i j h => hdvd _ (hy i j h))
        (n - j) (Nat.sub_le _ _)
      rwa [Nat.sub_sub_self hj] at this)
  choose z hz hzr using hroot
  set M : Matrix (Fin n) (Fin n) E := (x : Matrix (Fin n) (Fin n) O).map (algebraMap O E) *
    Matrix.diagonal (fun i => algebraMap O E ϖ ^ a i) *
    (y : Matrix (Fin n) (Fin n) O).map (algebraMap O E) with hM
  have hMG : M = algebraMap O E ϖ ^ N • G.map (algebraMap O E) := by
    have : Matrix.diagonal (fun i => algebraMap O E ϖ ^ a i) =
        algebraMap O E ϖ ^ N • (Matrix.diagonal (fun i => ϖ ^ b i)).map (algebraMap O E) := by
      rw [Matrix.diagonal_map (map_zero _), ← Matrix.diagonal_smul]
      congr 1
      funext i
      rw [hab, zpow_add₀ hϖ0]
      simp
    rw [hM, this, hG, Matrix.map_mul, Matrix.map_mul, Matrix.mul_smul, Matrix.smul_mul]
  let r : Fin n → E := fun i => algebraMap O E ϖ ^ N * algebraMap O E (ϖ ^ b i * z i)
  have hr0 : ∀ i, r i ≠ 0 := fun i =>
    mul_ne_zero (zpow_ne_zero _ hϖ0) ((map_ne_zero_iff _ hinj).2
      (mul_ne_zero (pow_ne_zero _ hϖ.ne_zero) (hz i).ne_zero))
  have hv : ∀ i, (IsDiscreteValuationRing.maximalIdeal O).valuation E (r i) =
      WithZero.exp (-(a i)) := fun i => by
    simp only [r, map_mul, map_pow, map_zpow₀, valuation_unif ϖ hϖ, valuation_of_isUnit (hz i), mul_one]
    rw [← WithZero.exp_zsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add, hab]
    congr 1
    simp
    ring
  have hval : ∀ i, val O (r i) = a i := fun i => by
    simp only [val, hv i, WithZero.log_exp, neg_neg]
  have hrinj : Function.Injective r := fun i j h => by
    have h1 := hval i
    rw [h, hval j] at h1
    exact ha.injective h1.symm
  have hrt : ∀ i, M.charpoly.IsRoot (r i) := fun i => by
    have h1 : ((G.map (algebraMap O E)).charpoly).IsRoot (algebraMap O E (ϖ ^ b i * z i)) := by
      rw [Matrix.charpoly_map]
      exact Polynomial.IsRoot.map (algebraMap O E) (hzr i)
    rw [IsRoot.def, Matrix.eval_charpoly] at h1 ⊢
    have : Matrix.scalar (Fin n) (r i) - M = algebraMap O E ϖ ^ N •
        (Matrix.scalar (Fin n) (algebraMap O E (ϖ ^ b i * z i)) - G.map (algebraMap O E)) := by
      rw [hMG, smul_sub]
      congr 1
      rw [Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.diagonal_smul]
      rfl
    rw [this, Matrix.det_smul, h1, mul_zero]
  refine ⟨r, fun i => ⟨hr0 i, hval i⟩, ?_⟩
  refine eq_of_monic_of_dvd_of_natDegree_le (monic_prod_X_sub_C _ _) M.charpoly_monic ?_ ?_
  · exact Finset.prod_dvd_of_coprime
      (fun i _ j _ h => pairwise_coprime_X_sub_C hrinj h) fun i _ => dvd_iff_isRoot.2 (hrt i)
  · rw [Matrix.charpoly_natDegree_eq_dim, natDegree_finsetProd_X_sub_C_eq_card]
    simp

end GlobalTheory.IwahoriRoots
end
end

section

namespace GlobalTheory.UnitLemma.TwistUnit

open GlobalTheory.UnitLemma Polynomial

theorem mem_adjoin_of_mul_eq_one {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {s t : A}
    (h : s * t = 1) (ht : IsIntegral O t) : t ∈ Algebra.adjoin O {s} := by
  exact GlobalTheory.UnitLemma.UnitBase.mem_adjoin_of_mul_eq_one' h ht

theorem adjoin_stab {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {s : A} (L : Submodule O A)
    (hL : ∀ y ∈ L, s * y ∈ L) {a : A} (ha : a ∈ Algebra.adjoin O {s}) : ∀ y ∈ L, a * y ∈ L := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx; exact hL
  | algebraMap r =>
    intro y hy
    rw [← Algebra.smul_def]; exact L.smul_mem r hy
  | add x z _ _ hx hz =>
    intro y hy
    rw [add_mul]; exact L.add_mem (hx y hy) (hz y hy)
  | mul x z _ _ hx hz =>
    intro y hy
    rw [mul_assoc]; exact hx _ (hz y hy)

variable {K : UQ}

theorem trace_σ (B : InvAlg K) (a : B.A) :
    Algebra.trace K.E B.A (B.σ a) = K.c (Algebra.trace K.E B.A a) := by
  classical
  let b := Module.Free.chooseBasis K.E B.A
  have hsm : ∀ (e : K.E) (y : B.A), B.σ (e • y) = K.c e • B.σ y := by
    intro e y
    rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]
  have hli : LinearIndependent K.E ((B.σ : B.A →+ B.A) ∘ b) := by
    refine b.linearIndependent.map_of_injective_injective (fun r => K.c.symm r) (B.σ : B.A →+ B.A) ?_ ?_ ?_
    · intro r hr
      simpa using hr
    · intro m hm
      have : B.σ m = 0 := hm
      simpa using this
    · intro r m
      show B.σ (K.c.symm r • m) = r • B.σ m
      rw [hsm, RingEquiv.apply_symm_apply]
  have hsp : ⊤ ≤ Submodule.span K.E (Set.range ((B.σ : B.A →+ B.A) ∘ b)) := by
    intro y _
    have h1 : y = ∑ j, K.c (b.repr (B.σ.symm y) j) • B.σ (b j) := by
      conv_lhs => rw [← B.σ.apply_symm_apply y, ← b.sum_repr (B.σ.symm y)]

      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => hsm _ _
    rw [h1]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let b' : Module.Basis (Module.Free.ChooseBasisIndex K.E B.A) K.E B.A := Module.Basis.mk hli hsp
  have hb' : ∀ i, b' i = B.σ (b i) := fun i => by
    simp only [b', Module.Basis.mk_apply]
    rfl
  have hrepr : ∀ y i, b'.repr (B.σ y) i = K.c (b.repr y i) := by
    intro y i
    have h1 : B.σ y = ∑ j, K.c (b.repr y j) • b' j := by
      conv_lhs => rw [← b.sum_repr y]

      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [hsm, hb']
    rw [h1, b'.repr_sum_self]

  rw [Algebra.trace_eq_matrix_trace b', Algebra.trace_eq_matrix_trace b, Matrix.trace, Matrix.trace,
  map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  rw [hb', ← map_mul, hrepr]

theorem mem_range_c (e : K.E) : K.c e ∈ (algebraMap K.O K.E).range ↔ e ∈ (algebraMap K.O K.E).range := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨b, hb⟩ := K.c_int a
    refine ⟨b, ?_⟩
    rw [← hb, ha, K.c_c]
  · rintro ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := K.c_int a
    exact ⟨b, hb.symm⟩

theorem trace_σ_mem (B : InvAlg K) (a : B.A) :
    Algebra.trace K.E B.A (B.σ a) ∈ (algebraMap K.O K.E).range ↔
      Algebra.trace K.E B.A a ∈ (algebraMap K.O K.E).range := by
  rw [trace_σ, mem_range_c]

theorem twisted_unit_eq_unit : ∀ (K : UQ) (B : InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable → IsIntegral K.O B.g →
    ∀ (ε : B.A), (ε = 1 ∨ ε = -1) → ∃ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * (ε * B.g) ∧
      ∀ x : B.Aˣ, B.σ (x : B.A) = x →
        {L : Submodule K.O B.A | IsLat K.O K.E L ∧ ∀ z, z ∈ L ↔ ∀ y ∈ L,
          B.herm (β₀ * x) y z ∈ (algebraMap K.O K.E).range} = B.X x := by
  intro K B hg hs hi ε hε
  obtain ⟨β₀, hβ, hb1, hb2⟩ := GlobalTheory.T.exists_unit_basePoint_adjoin_twisted_sigma K B hg hs hi ε hε
  refine ⟨β₀, hβ, fun x hx => ?_⟩
  set R := (algebraMap K.O K.E).range with hR
  set T := Algebra.trace K.E B.A with hT
  have hεT : ∀ a, T (ε * a) ∈ R ↔ T a ∈ R := by
    intro a
    rcases hε with rfl | rfl
    · rw [one_mul]
    · rw [neg_one_mul, map_neg, neg_mem_iff]
  have hstab : ∀ L : Submodule K.O B.A, (∀ y ∈ L, B.g * y ∈ L) → ∀ w : B.A,
      ((∀ y ∈ L, T ((β₀ : B.A) * x * y * B.σ w) ∈ R) ↔ ∀ y ∈ L, T ((x : B.A) * y * B.σ w) ∈ R) := by
    intro L hL w
    have s1 := adjoin_stab L hL hb1
    have s2 := adjoin_stab L hL hb2
    constructor
    · intro h y hy
      have := h _ (s2 y hy)
      have e : (β₀ : B.A) * x * (((β₀⁻¹ : B.Aˣ) : B.A) * y) * B.σ w = x * y * B.σ w := by
        have := β₀.mul_inv
        linear_combination (↑x * y * B.σ w) * this
      rwa [e] at this
    · intro h y hy
      have := h _ (s1 y hy)
      rwa [show (x : B.A) * ((β₀ : B.A) * y) * B.σ w = β₀ * x * y * B.σ w by ring] at this
  have hX' : ∀ (L : Submodule K.O B.A) (w : B.A),
      ((∀ y ∈ L, T ((x : B.A) * w * B.σ y) ∈ R) ↔ ∀ y ∈ L, T ((x : B.A) * y * B.σ w) ∈ R) := by
    intro L w
    refine forall₂_congr fun y _ => ?_
    rw [← trace_σ_mem B]
    rw [show B.σ ((x : B.A) * w * B.σ y) = x * y * B.σ w by
      rw [map_mul, map_mul, hx, B.σ_σ]; ring]
  have hsym : ∀ a b : B.A, T ((β₀ : B.A) * x * a * B.σ b) ∈ R ↔
      T ((β₀ : B.A) * x * (B.g * b) * B.σ a) ∈ R := by
    intro a b
    rw [← trace_σ_mem B ((β₀ : B.A) * x * a * B.σ b),
      show B.σ ((β₀ : B.A) * x * a * B.σ b) = ε * ((β₀ : B.A) * x * (B.g * b) * B.σ a) by
        rw [map_mul, map_mul, map_mul, hβ, hx, B.σ_σ]; ring, hεT]
  have hgg : B.σ B.g * B.g = 1 := by rw [mul_comm]; exact hg
  have hgad : B.g ∈ Algebra.adjoin K.O {B.σ B.g} := mem_adjoin_of_mul_eq_one hgg hi
  ext L
  simp only [Set.mem_setOf_eq, InvAlg.X, InvAlg.herm, Units.val_mul, ← hT, ← hR]
  constructor
  · rintro ⟨hLat, hU⟩
    have h1 : ∀ y ∈ L, B.σ B.g * y ∈ L := by
      intro y hy
      rw [hU]
      intro y' hy'
      rw [hsym, show (β₀ : B.A) * x * (B.g * (B.σ B.g * y)) * B.σ y' = β₀ * x * y * B.σ y' by
        linear_combination ((β₀ : B.A) * x * y * B.σ y') * hg]
      exact (hU y').1 hy' y hy
    have h2 : ∀ y ∈ L, B.g * y ∈ L := adjoin_stab L h1 hgad
    refine ⟨hLat, h2, fun y => ?_⟩
    rw [hX' L y, ← hstab L h2, ← hU]
  · rintro ⟨hLat, h2, hXc⟩
    refine ⟨hLat, fun z => ?_⟩
    rw [hstab L h2, ← hX', ← hXc]

end GlobalTheory.UnitLemma.TwistUnit
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.UU_eq_sum_over_torus_orbits : ∀ (K : UQ) (B : InvAlg K) (x w : B.A), Finite (Orb K.O B.T (B.X x)) → (∀ o : Orb K.O B.T (B.X x), Finite {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M}) → B.UU x w = ∑ᶠ o : Orb K.O B.T (B.X x), Nat.card {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M} := by
  first | exact @GlobalTheory.UnitLemma.UU_eq_sum_orbits | exact GlobalTheory.UnitLemma.UU_eq_sum_orbits | (intros; apply GlobalTheory.UnitLemma.UU_eq_sum_orbits <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_nhds_one_etaleAlgebra_mul_invariant : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (φ : A.L → ℂ), IsTest φ → ∃ U ∈ 𝓝 (1 : A.K), ∀ s ∈ U, ∀ s' ∈ U, s * s' = 1 → ∀ y : A.L, φ (y * algebraMap A.K A.L s) = φ y := by
  first | exact @GlobalTheory.JR.MulInv.exists_nhds_one_mul_invariant | exact GlobalTheory.JR.MulInv.exists_nhds_one_mul_invariant | (intros; apply GlobalTheory.JR.MulInv.exists_nhds_one_mul_invariant <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.isLocallyConstant_etaleTraceAddChar_hermitianKernel : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → IsLocallyConstant (A.psiK ψ) ∧ ∀ (x : A.K) (y' : A.L), IsLocallyConstant (fun y => A.kerL ψ x y y') := by
  first | exact @GlobalTheory.JR.Hyp.isLocallyConstant_psiK_kerL | exact GlobalTheory.JR.Hyp.isLocallyConstant_psiK_kerL | (intros; apply GlobalTheory.JR.Hyp.isLocallyConstant_psiK_kerL <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.finiteEtaleHermitian_linearEquiv_continuous : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)), Continuous j ∧ Continuous j.symm := by
  first | exact @GlobalTheory.JR.et_equiv_continuous | exact GlobalTheory.JR.et_equiv_continuous | (intros; apply GlobalTheory.JR.et_equiv_continuous <;> assumption)
end
