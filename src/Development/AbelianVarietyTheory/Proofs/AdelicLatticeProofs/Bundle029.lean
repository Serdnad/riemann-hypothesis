module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle018
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Trace.Basic

@[expose] public section

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem relIndex_eq_prime_of_generated {G : Type} [CommGroup G] {p : ℕ} (hp : p.Prime)
    (E K : Subgroup G) (x : G) (hxE : x ∈ E) (hxK : x ∉ K) (hxp : x ^ p ∈ K)
    (hgen : ∀ y ∈ E, ∃ k : ℕ, y / x ^ k ∈ K) : K.relIndex E = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  set c : E ⧸ K.subgroupOf E := QuotientGroup.mk (⟨x, hxE⟩ : E) with hc
  have ho : orderOf c = p := by
    apply orderOf_eq_prime
    · rw [hc, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hxp
    · rw [hc, Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hxK
  have hall : ∀ y : E ⧸ K.subgroupOf E, y ∈ Submonoid.powers c := by
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := hgen y y.2
    refine ⟨k, ?_⟩
    simp only [hc]
    rw [← QuotientGroup.mk_pow, eq_comm, QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
    simpa using hk
  rw [Subgroup.relIndex, Subgroup.index, ← ho]
  exact (orderOf_eq_card_of_forall_mem_powers hall).symm

theorem exists_independent_prime_relIndex_subgroups (p : ℕ) (G ι : Type) [CommGroup G] [DecidableEq ι]
    (U H : Subgroup G) (K : ι → Subgroup G) (good : ι → Prop) (m : ℕ) (hp : p.Prime)
    (hH : H.relIndex U = p ^ m) (h1 : ∀ i, good i → U ⊓ H ≤ K i)
    (h2 : ∀ i, good i → ∀ x ∈ U, x ^ p ∈ K i)
    (h2' : ∀ i, good i → ∀ x ∈ U, x ∉ K i → ∀ y ∈ U, ∃ k : ℕ, y / x ^ k ∈ K i)
    (h3 : ∀ x ∈ U, x ∉ H → ∃ i, good i ∧ x ∉ K i) (k : ℕ) (hk : k ≤ m) :
    ∃ T : Finset ι, T.card = k ∧ (∀ i ∈ T, good i) ∧
      (∀ i ∈ T, ∃ u ∈ U, u ∉ K i ∧ ∀ j ∈ T, j ≠ i → u ∈ K j) ∧
      ∃ D : Subgroup G, (∀ x, x ∈ D ↔ ∀ i ∈ T, x ∈ K i) ∧ D.relIndex U = p ^ k := by
  induction k with
  | zero =>
    refine ⟨∅, rfl, by simp, by simp, ⊤, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨T, hT, hg, hA, D, hD, hDi⟩ := ih (by omega)
    have hx : ∃ x ∈ U, x ∈ D ∧ x ∉ H := by
      by_contra hcon
      push Not at hcon
      have heq : D ⊓ U = H ⊓ U := by
        ext x
        simp only [Subgroup.mem_inf]
        constructor
        · rintro ⟨a, b⟩
          exact ⟨hcon x b a, b⟩
        · rintro ⟨a, b⟩
          exact ⟨(hD x).2 fun i hi => h1 i (hg i hi) ⟨b, a⟩, b⟩
      have h4 : D.relIndex U = H.relIndex U := by
        rw [← Subgroup.inf_relIndex_right D U, heq, Subgroup.inf_relIndex_right]
      rw [hDi, hH] at h4
      have := Nat.pow_right_injective hp.two_le h4
      omega
    obtain ⟨x, hxU, hxD, hxH⟩ := hx
    obtain ⟨j, hj, hxj⟩ := h3 x hxU hxH
    have hjT : j ∉ T := fun h => hxj ((hD x).1 hxD j h)
    refine ⟨insert j T, by rw [Finset.card_insert_of_notMem hjT, hT], ?_, ?_, K j ⊓ D, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hj
      · exact hg i hi
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · refine ⟨x, hxU, hxj, fun l hl hli => ?_⟩
        rcases Finset.mem_insert.1 hl with rfl | hl
        · exact absurd rfl hli
        · exact (hD x).1 hxD l hl
      · obtain ⟨u, huU, hui, hu⟩ := hA i hi
        obtain ⟨n, hn⟩ := h2' j hj x hxU hxj u huU
        refine ⟨u / x ^ n, U.div_mem huU (U.pow_mem hxU n), ?_, fun l hl hli => ?_⟩
        · intro h
          apply hui
          have := (K i).mul_mem h ((K i).pow_mem ((hD x).1 hxD i hi) n)
          simpa using this
        · rcases Finset.mem_insert.1 hl with rfl | hl
          · exact hn
          · exact (K l).div_mem (hu l hl hli) ((K l).pow_mem ((hD x).1 hxD l hl) n)
    · intro y
      simp only [Subgroup.mem_inf, hD, Finset.forall_mem_insert]
    · have h5 : (K j).relIndex (D ⊓ U) = p :=
        relIndex_eq_prime_of_generated hp (D ⊓ U) (K j) x ⟨hxD, hxU⟩ hxj (h2 j hj x hxU)
          (fun y hy => h2' j hj x hxU hxj y hy.2)
      rw [← Subgroup.relIndex_inf_mul_relIndex, h5, hDi, pow_succ, mul_comm]

theorem exists_indep_prime_index : ∀ (p : ℕ) (G ι : Type) [CommGroup G] [DecidableEq ι] (U H : Subgroup G) (K : ι → Subgroup G) (good : ι → Prop) (m : ℕ), p.Prime → H.relIndex U = p ^ m → (∀ i, good i → U ⊓ H ≤ K i) → (∀ i, good i → ∀ x ∈ U, x ^ p ∈ K i) → (∀ i, good i → ∀ x ∈ U, x ∉ K i → ∀ y ∈ U, ∃ k : ℕ, y / x ^ k ∈ K i) → (∀ x ∈ U, x ∉ H → ∃ i, good i ∧ x ∉ K i) → ∃ T : Finset ι, T.card = m ∧ (∀ i ∈ T, good i) ∧ ∀ i ∈ T, ∃ u ∈ U, u ∉ K i ∧ ∀ j ∈ T, j ≠ i → u ∈ K j := by
  intro p G ι _ _ U H K good m hp hH h1 h2 h2' h3
  obtain ⟨T, a, b, c, -⟩ :=
    exists_independent_prime_relIndex_subgroups p G ι U H K good m hp hH h1 h2 h2' h3 m le_rfl
  exact ⟨T, a, b, c⟩

end GlobalTheory.CNorm
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem pow_card_le_index_iInf_of_prime :
    ∀ (p : ℕ) (G ι : Type) [CommGroup G] [Fintype ι] (K : ι → Subgroup G), p.Prime →
      (∀ (i : ι) (x : G), x ^ p ∈ K i) → (∀ i, ∃ x, x ∉ K i ∧ ∀ j, j ≠ i → x ∈ K j) →
      (⨅ i, K i).index ≠ 0 → p ^ Fintype.card ι ≤ (⨅ i, K i).index := by
  intro p G ι _ _ K hp hpow hx hind
  classical
  choose x hx1 hx2 using hx
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (G ⧸ (⨅ i, K i)) := Nat.finite_of_card_ne_zero hind
  have hord : ∀ j, orderOf (QuotientGroup.mk' (K j) (x j)) = p := by
    intro j
    apply orderOf_eq_prime
    · rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hpow j _
    · rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
      exact hx1 j
  have hprod : ∀ (n : ι → Fin p) (j : ι),
      QuotientGroup.mk' (K j) (∏ i, x i ^ (n i : ℕ)) = (QuotientGroup.mk' (K j) (x j)) ^ (n j : ℕ) := by
    intro n j
    rw [map_prod, Finset.prod_eq_single j]
    · rw [map_pow]
    · intro i _ hij
      rw [map_pow]
      have : QuotientGroup.mk' (K j) (x i) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hx2 i j (Ne.symm hij)
      rw [this, one_pow]
    · intro h
      exact absurd (Finset.mem_univ j) h
  let f : (ι → Fin p) → G ⧸ (⨅ i, K i) := fun n => QuotientGroup.mk (∏ i, x i ^ (n i : ℕ))
  have hf : Function.Injective f := by
    intro n m h
    have h1 := QuotientGroup.eq.1 h
    funext j
    have h2 := Subgroup.mem_iInf.1 h1 j
    have h3 : QuotientGroup.mk' (K j) (∏ i, x i ^ (n i : ℕ))
        = QuotientGroup.mk' (K j) (∏ i, x i ^ (m i : ℕ)) := QuotientGroup.eq.2 h2
    rw [hprod, hprod] at h3
    apply Fin.ext
    refine pow_injOn_Iio_orderOf ?_ ?_ h3
    · rw [hord]; exact (n j).2
    · rw [hord]; exact (m j).2
  have := Nat.card_le_card_of_injective f hf
  simpa [Subgroup.index] using this

end GlobalTheory.CNorm
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm


open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
theorem _root_.GlobalTheory.CNorm.algebraMap_norm_tensor_eq_prod_conjugates (F E K : Type) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] [CommRing K] [Algebra F K] (y : K ⊗[F] E) :
    algebraMap K (K ⊗[F] E) (Algebra.norm K y) =
      ∏ g : E ≃ₐ[F] E, Algebra.TensorProduct.map (AlgHom.id K K) (g : E →ₐ[F] E) y := by
  classical
  set G := E ≃ₐ[F] E
  have hcard : Fintype.card G = Module.finrank F E := by
    rw [← IsGalois.card_aut_eq_finrank F E, Nat.card_eq_fintype_card]
  let b : Module.Basis G F E := (Module.finBasis F E).reindex (Fintype.equivFinOfCardEq hcard).symm
  let b' : Module.Basis G K (K ⊗[F] E) := Algebra.TensorProduct.basis K b
  set A := Algebra.leftMulMatrix b' y with hA
  let P : Matrix G G E := fun g j => g (b j)
  have hP : P.det ≠ 0 := by
    intro h
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h
    have hj : ∀ j, ∑ g, v g * g (b j) = 0 := fun j => by
      simpa [Matrix.vecMul, dotProduct, P] using congrFun hv j
    have hx : ∀ x : E, ∑ g, v g * g x = 0 := fun x => by
      calc ∑ g, v g * g x = ∑ g, v g * g (∑ j, b.repr x j • b j) := by rw [b.sum_repr]
        _ = ∑ j, b.repr x j • ∑ g, v g * g (b j) := by

          simp only [map_sum, Algebra.smul_def, map_mul, AlgEquiv.commutes, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun g _ => by rw [AlgEquiv.commutes]; ring
        _ = 0 := by simp [hj]
    have hli := (linearIndependent_monoidHom E E).comp
      (fun g : G => (g : E ≃* E).toMonoidHom) (fun g₁ g₂ h => by
        ext x; exact DFunLike.congr_fun h x)
    have := Fintype.linearIndependent_iff.mp hli v (by
      funext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
        Pi.zero_apply]
      exact hx x)
    exact hv0 (funext this)
  let P' : Matrix G G (K ⊗[F] E) := P.map Algebra.TensorProduct.includeRight
  have key : Matrix.diagonal
      (fun g : G => Algebra.TensorProduct.map (AlgHom.id K K) (g : E →ₐ[F] E) y) * P'
      = P' * A.map (algebraMap K (K ⊗[F] E)) := by
    ext g j
    have h1 : y * b' j = ∑ i, A i j • b' i := by
      simpa [A, Algebra.leftMulMatrix_eq_repr_mul] using (b'.sum_repr (y * b' j)).symm
    have h2 := congrArg (Algebra.TensorProduct.map (AlgHom.id K K) (g : E →ₐ[F] E)) h1

    simp only [map_mul, map_sum, b', Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one, Algebra.smul_def,
    AlgHom.commutes] at h2
    rw [Matrix.diagonal_mul, Matrix.mul_apply]
    change _ * (1 ⊗ₜ[F] (g : E →ₐ[F] E) (b j)) =
      ∑ i, (1 ⊗ₜ[F] (g : E →ₐ[F] E) (b i)) * algebraMap K (K ⊗[F] E) (A i j)
    rw [h2]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hdet := congrArg Matrix.det key
  have hAdet : (A.map (algebraMap K (K ⊗[F] E))).det = algebraMap K (K ⊗[F] E) A.det :=
    (RingHom.map_det _ _).symm
  have hPdet : P'.det = Algebra.TensorProduct.includeRight P.det :=
    (RingHom.map_det (Algebra.TensorProduct.includeRight : E →ₐ[F] K ⊗[F] E).toRingHom P).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, hAdet, hA,
    ← Algebra.norm_eq_matrix_det] at hdet
  have hu : IsUnit P'.det := by
    rw [hPdet]; exact (isUnit_iff_ne_zero.mpr hP).map _
  exact (hu.mul_left_cancel (by rw [mul_comm]; exact hdet)).symm

end GlobalTheory.CNorm
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem tensor_exists_of_galois_fixed :
    ∀ (F M E K : Type) [Field F] [CharZero F] [Field M] [Field E] [Algebra F M] [Algebra M E] [Algebra F E] [IsScalarTower F M E] [FiniteDimensional M E] [IsGalois M E] [CommRing K] [Algebra F K] (y : K ⊗[F] E), (∀ h : E ≃ₐ[M] E, Algebra.TensorProduct.map (AlgHom.id K K) ((h.restrictScalars F : E ≃ₐ[F] E) : E →ₐ[F] E) y = y) → ∃ z : K ⊗[F] M, Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom F M E) z = y := by
  intro F M E K _ _ _ _ _ _ _ _ _ _ _ _ y hy
  classical
  have key : ∀ x : K ⊗[F] E, ∃ z : K ⊗[F] M,
      Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom F M E) z =
      ∑ h : E ≃ₐ[M] E, Algebra.TensorProduct.map (AlgHom.id K K)
        ((h.restrictScalars F : E ≃ₐ[F] E) : E →ₐ[F] E) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul k e =>
      refine ⟨k ⊗ₜ Algebra.trace M E e, ?_⟩
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rw [← TensorProduct.tmul_sum]
      congr 1
      exact trace_eq_sum_automorphisms e
    | add a b ha hb =>
      obtain ⟨za, ha⟩ := ha
      obtain ⟨zb, hb⟩ := hb
      refine ⟨za + zb, ?_⟩
      simp only [map_add (f := _), Finset.sum_add_distrib, ha, hb]
  obtain ⟨z, hz⟩ := key y
  simp only [hy, Finset.sum_const, Finset.card_univ] at hz
  have hm : ((Fintype.card (E ≃ₐ[M] E) : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨((Fintype.card (E ≃ₐ[M] E) : ℕ) : F)⁻¹ • z, ?_⟩
  rw [LinearMapClass.map_smul_of_tower, hz, ← Nat.cast_smul_eq_nsmul F, smul_smul,
    inv_mul_cancel₀ hm, one_smul]

end GlobalTheory.CNorm
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem card_ker_comp_eq {M : Type} [CommGroup M] (f g : M →* M) :
    Nat.card (f.comp g).ker = Nat.card g.ker * Nat.card (g.range.subgroupOf f.ker) := by
  have hle : g.ker ≤ (f.comp g).ker := by
    intro x hx
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx ⊢
    rw [hx, map_one]
  have h1 := Subgroup.card_mul_index (g.ker.subgroupOf (f.comp g).ker)
  have h2 : (g.ker.subgroupOf (f.comp g).ker).index = Nat.card ((f.comp g).ker.map g) :=
    Subgroup.relIndex_ker _ _
  have h3 : (f.comp g).ker.map g = g.range ⊓ f.ker := by
    rw [← MonoidHom.comap_ker, Subgroup.map_comap_eq]
  have h4 : Nat.card (g.range.subgroupOf f.ker) = Nat.card (g.range ⊓ f.ker : Subgroup M) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [← h1, h2, h3, h4, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]

theorem index_range_comp_mul {M : Type} [CommGroup M] (f g : M →* M) :
    (f.comp g).range.index * Nat.card f.ker * Nat.card g.ker =
      f.range.index * g.range.index * Nat.card (f.comp g).ker := by
  have h1 : (f.comp g).range.index = (g.range ⊔ f.ker).index * f.range.index := by
    rw [MonoidHom.range_comp, Subgroup.index_map]
  have h2 : g.range.relIndex f.ker * (g.range ⊔ f.ker).index = g.range.index := by
    rw [← Subgroup.relIndex_sup_left, Subgroup.relIndex_mul_index le_sup_left]
  have h3 : Nat.card (g.range.subgroupOf f.ker) * g.range.relIndex f.ker = Nat.card f.ker :=
    Subgroup.card_mul_index _
  rw [h1, card_ker_comp_eq, ← h2, ← h3]
  ring

theorem index_range_ker_pow_succ_endomorphism {M : Type} [CommGroup M] (f : Monoid.End M)
    (hK : Nat.card (MonoidHom.ker f) ≠ 0) (k : ℕ) :
    Nat.card (MonoidHom.ker (f ^ (k + 1) : Monoid.End M)) ≠ 0 ∧
    (MonoidHom.range (f ^ (k + 1) : Monoid.End M)).index * Nat.card (MonoidHom.ker f) ^ (k + 1) =
      (MonoidHom.range f).index ^ (k + 1) *
        Nat.card (MonoidHom.ker (f ^ (k + 1) : Monoid.End M)) := by
  induction k with
  | zero => simpa using hK
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hc : (f ^ (k + 1 + 1) : Monoid.End M) = MonoidHom.comp f (f ^ (k + 1) : Monoid.End M) := by
      rw [pow_succ' f (k + 1)]; rfl
    rw [hc]
    constructor
    · refine (card_ker_comp_eq (M := M) f (f ^ (k + 1) : Monoid.End M)).trans_ne
        (mul_ne_zero ih1 ?_)
      have h3 := Subgroup.card_mul_index
        ((MonoidHom.range (f ^ (k + 1) : Monoid.End M)).subgroupOf (MonoidHom.ker f))
      intro h
      rw [h, zero_mul] at h3
      exact hK h3.symm
    · have h := index_range_comp_mul (M := M) f (f ^ (k + 1) : Monoid.End M)
      apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero ih1)
      generalize (MonoidHom.comp f (f ^ (k + 1) : Monoid.End M)).range.index = A at *
      generalize Nat.card (MonoidHom.comp f (f ^ (k + 1) : Monoid.End M)).ker = B at *
      generalize (MonoidHom.range (f ^ (k + 1) : Monoid.End M)).index = C at *
      generalize Nat.card (MonoidHom.ker (f ^ (k + 1) : Monoid.End M)) = D at *
      generalize Nat.card (MonoidHom.ker f) = K at *
      generalize (MonoidHom.range f).index = I at *
      calc A * K ^ (k + 1 + 1) * D = (A * K * D) * K ^ (k + 1) := by ring
        _ = I * B * (C * K ^ (k + 1)) := by rw [h]; ring
        _ = I ^ (k + 1 + 1) * B * D := by rw [ih2]; ring

theorem index_ker_iterate :
    ∀ (M : Type) [CommGroup M] (f : Monoid.End M) (k : ℕ), (MonoidHom.range (f ^ (k + 1) : Monoid.End M)).index ≠ 0 → Nat.card (MonoidHom.ker (f ^ (k + 1) : Monoid.End M)) ≠ 0 → (MonoidHom.range f).index ≠ 0 ∧ Nat.card (MonoidHom.ker f) ≠ 0 ∧ (MonoidHom.range (f ^ (k + 1) : Monoid.End M)).index * Nat.card (MonoidHom.ker f) ^ (k + 1) = (MonoidHom.range f).index ^ (k + 1) * Nat.card (MonoidHom.ker (f ^ (k + 1) : Monoid.End M)) := by
  intro M _ f k hI hK
  have hr : MonoidHom.range (f ^ (k + 1) : Monoid.End M) ≤ MonoidHom.range f := by
    rintro _ ⟨x, rfl⟩
    exact ⟨(f ^ k : Monoid.End M) x, by rw [pow_succ']; rfl⟩
  have hk : MonoidHom.ker f ≤ MonoidHom.ker (f ^ (k + 1) : Monoid.End M) := by
    intro x hx
    have hx' : f x = 1 := hx
    rw [pow_succ]
    change (f ^ k : Monoid.End M) (f x) = 1
    rw [hx', map_one]
  have hK' : Nat.card (MonoidHom.ker f) ≠ 0 :=
    ne_zero_of_dvd_ne_zero hK (Subgroup.card_dvd_of_le hk)
  exact ⟨ne_zero_of_dvd_ne_zero hI (Subgroup.index_dvd_of_le hr), hK',
    (index_range_ker_pow_succ_endomorphism f hK' k).2⟩

end GlobalTheory.CNorm
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem mem_smul_top_iff_repr {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M) (J : Ideal R) (x : M) :
    x ∈ (J • ⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ J := by
  constructor
  · intro hx i
    refine Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun y z hy hz => ?_)
    · simpa using J.mul_mem_right _ hr
    · simpa using J.add_mem hy hz
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

theorem isAdicComplete_of_free_finite {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (I : Ideal R) (h : IsAdicComplete I R) :
    IsAdicComplete I M := by
  classical
  let b := Module.Free.chooseBasis R M
  have key : ∀ (n : ℕ) (x y : M), x ≡ y [SMOD (I ^ n • ⊤ : Submodule R M)] ↔
      ∀ i, b.repr x i ≡ b.repr y i [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro n x y
    rw [SModEq.sub_mem, mem_smul_top_iff_repr b]
    refine forall_congr' fun i => ?_
    rw [SModEq.sub_mem]
    simp
  have hH : IsHausdorff I M := by
    refine ⟨fun x hx => ?_⟩
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    have := h.toIsHausdorff.haus (b.repr x i) fun n => by
      simpa using (key n x 0).1 (hx n) i
    simpa using this
  have hP : IsPrecomplete I M := by
    refine ⟨fun f hf => ?_⟩
    have hc : ∀ i, ∃ L : R, ∀ n, b.repr (f n) i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] :=
      fun i => h.toIsPrecomplete.prec (f := fun n => b.repr (f n) i)
        fun {m n} hmn => (key m _ _).1 (hf hmn) i
    choose L hL using hc
    refine ⟨b.equivFun.symm L, fun n => (key n _ _).2 fun i => ?_⟩
    have : b.repr (b.equivFun.symm L) i = L i := by
      rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [this]
    exact hL i n
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }

theorem isAdicComplete_span_algebraMap_of_free_finite :
    ∀ (R O : Type) [CommRing R] [CommRing O] [Algebra R O] [Module.Free R O] [Module.Finite R O]
      (t : R), IsAdicComplete (Ideal.span {t}) R →
        IsAdicComplete (Ideal.span {algebraMap R O t}) O := by
  intro R O _ _ _ _ _ t h
  have h1 : IsAdicComplete (Ideal.span {t}) O := isAdicComplete_of_free_finite _ h
  have h2 : Ideal.span {algebraMap R O t} = (Ideal.span {t}).map (algebraMap R O) := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [h2]
  exact (IsAdicComplete.map_algebraMap_iff _ O).2 h1

end GlobalTheory.CNorm
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.coords_leftMulMatrix_const_baseChange : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ x : F, (∀ k, b.repr (algebraMap F A x) k = algebraMap ℚ R (ω.repr x k)) ∧ Algebra.leftMulMatrix b (algebraMap F A x) = (Algebra.leftMulMatrix ω x).map (algebraMap ℚ R) := by
  first | exact @GlobalTheory.ClassFin.coords_const_baseChange | exact GlobalTheory.ClassFin.coords_const_baseChange | (intros; apply GlobalTheory.ClassFin.coords_const_baseChange <;> assumption)
end
