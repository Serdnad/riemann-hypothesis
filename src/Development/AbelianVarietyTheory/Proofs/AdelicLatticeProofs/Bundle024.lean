module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
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
public import Mathlib.FieldTheory.KummerExtension
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
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

@[expose] public section

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem herb_relIndex_map_range {A : Type} [CommGroup A] (f : A →* A) (H : Subgroup A) :
    (H.map f).relIndex f.range = (H ⊔ f.ker).index := by
  rw [← Subgroup.comap_map_eq, Subgroup.index_comap]

theorem herb_lattice {A : Type} [CommGroup A] (B C K : Subgroup A) (hCK : C ≤ K) :
    (C ⊔ B).index * Nat.card ↥(B ⊓ K) =
      (B ⊔ K).index * C.relIndex K * Nat.card ↥(C ⊓ B) := by
  have h1 : (C ⊔ B).relIndex (B ⊔ K) * (B ⊔ K).index = (C ⊔ B).index :=
    Subgroup.relIndex_mul_index (sup_le (hCK.trans le_sup_right) le_sup_left)
  have h2 : (C ⊔ B).relIndex (B ⊔ K) = (C ⊔ B ⊓ K).relIndex K := by
    have e : B ⊔ K = K ⊔ (C ⊔ B) := by
      apply le_antisymm
      · exact sup_le (le_sup_right.trans le_sup_right) le_sup_left
      · exact sup_le le_sup_right (sup_le (hCK.trans le_sup_right) le_sup_left)
    rw [e, Subgroup.relIndex_sup_right, ← sup_inf_assoc_of_le B hCK, Subgroup.inf_relIndex_right]
  have h3 : C.relIndex (C ⊔ B ⊓ K) * (C ⊔ B ⊓ K).relIndex K = C.relIndex K :=
    Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left (sup_le hCK inf_le_right)
  have h4 : C.relIndex (C ⊔ B ⊓ K) = C.relIndex (B ⊓ K) := Subgroup.relIndex_sup_left _ _
  have h5 : Nat.card ↥(C ⊓ B) * C.relIndex (B ⊓ K) = Nat.card ↥(B ⊓ K) := by
    have e : C ⊓ (B ⊓ K) = C ⊓ B := by
      rw [inf_comm B K, ← inf_assoc, inf_eq_left.2 hCK]
    rw [← Subgroup.inf_relIndex_right C, e, ← Subgroup.relIndex_bot_left,
      ← Subgroup.relIndex_bot_left]
    exact Subgroup.relIndex_mul_relIndex _ _ _ bot_le (e ▸ inf_le_right)
  rw [← h1, h2, ← h3, h4, ← h5]
  ring

theorem herb_nrm_apply_sigma {A : Type} [CommGroup A] (σ : A →* A) (p : ℕ)
    (h : ∀ a, σ^[p] a = a) (a : A) : nrm σ p (σ a) = nrm σ p a := by
  have e1 := Finset.prod_range_succ (fun i => σ^[i] a) p
  have e2 := Finset.prod_range_succ' (fun i => σ^[i] a) p
  rw [e1] at e2
  simp only [h, Function.iterate_zero, id, Function.iterate_succ_apply] at e2
  rw [nrm_apply, nrm_apply]
  exact (mul_right_cancel e2).symm

theorem herb_nrm_of_fix {A : Type} [CommGroup A] (σ : A →* A) (p : ℕ) (b : A)
    (hb : b ∈ fix σ) : nrm σ p b = b ^ p := by
  rw [nrm_apply, Finset.prod_congr rfl (fun i _ => Function.iterate_fixed ((mem_fix σ b).1 hb) i)]
  simp

theorem herb_index_identity : ∀ (p : ℕ) (A : Type) [CommGroup A] (σ : A →* A), (∀ a, σ^[p] a = a) → (nrm σ p).range.relIndex (fix σ) * ((dif σ).range.map (dif σ)).relIndex (dif σ).range * pTor p (fix σ) = pIdx p (fix σ) * (dif σ).range.relIndex (nrm σ p).ker * Nat.card ↥((dif σ).range ⊓ fix σ) := by
  intro p A _ σ h
  have hker : (dif σ).ker = fix σ := by
    ext a
    rw [MonoidHom.mem_ker, dif_apply, mem_fix, div_eq_one]
  have hCK : (dif σ).range ≤ (nrm σ p).ker := by
    rintro _ ⟨a, rfl⟩
    rw [MonoidHom.mem_ker, dif_apply, _root_.map_div, herb_nrm_apply_sigma σ p h, div_self']
  have hNB : (nrm σ p).range ≤ fix σ := by
    rintro _ ⟨a, rfl⟩
    rw [mem_fix, ← herb_nrm_apply_sigma σ p h a]
    conv_lhs => rw [herb_nrm_apply_sigma σ p h a]
    rw [nrm_apply, nrm_apply, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Function.iterate_succ_apply σ i a, Function.iterate_succ_apply']
  have hpow : pows p (fix σ) = (fix σ).map (nrm σ p) := by
    ext x
    simp only [pows, Subgroup.mem_map, powMonoidHom_apply]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b, hb, herb_nrm_of_fix σ p b hb⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b, hb, (herb_nrm_of_fix σ p b hb).symm⟩
  have htor : pTor p (fix σ) = Nat.card ↥(fix σ ⊓ (nrm σ p).ker) := by
    unfold pTor
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [Subgroup.mem_inf, MonoidHom.mem_ker]
    refine and_congr_right fun hx => ?_
    rw [herb_nrm_of_fix σ p x hx]
  have hidx : pIdx p (fix σ) =
      (fix σ ⊔ (nrm σ p).ker).index * (nrm σ p).range.relIndex (fix σ) := by
    unfold pIdx
    rw [hpow, ← herb_relIndex_map_range]
    exact (Subgroup.relIndex_mul_relIndex _ _ _ (Subgroup.map_le_range _ _) hNB).symm
  have hl := herb_lattice (fix σ) (dif σ).range (nrm σ p).ker hCK
  rw [herb_relIndex_map_range, hker, htor, hidx, mul_assoc, hl]
  ring

end GlobalTheory.CNorm
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem pTor_eq_card_inf_ker (p : ℕ) {G : Type} [CommGroup G] (U : Subgroup G) :
    pTor p U = Nat.card (U ⊓ (powMonoidHom p : G →* G).ker : Subgroup G) := by
  unfold pTor
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker, powMonoidHom_apply])

theorem pIdx_pTor_ker_range :
    ∀ (p : ℕ) (A A' : Type) [CommGroup A] [CommGroup A'] (g : A →* A'), pIdx p g.ker ≠ 0 → pTor p g.ker ≠ 0 → pIdx p g.range ≠ 0 → pTor p g.range ≠ 0 → pIdx p (⊤ : Subgroup A) ≠ 0 ∧ pTor p (⊤ : Subgroup A) ≠ 0 ∧ pIdx p (⊤ : Subgroup A) * pTor p g.ker * pTor p g.range = pIdx p g.ker * pIdx p g.range * pTor p (⊤ : Subgroup A) := by
  intro p A A' _ _ g hIK hTK hIR hTR
  have hcomm : (powMonoidHom p : A' →* A').comp g = g.comp (powMonoidHom p : A →* A) := by
    ext a; simp [map_pow]
  have hRp : pows p g.range = (powMonoidHom p : A →* A).range.map g := by
    simp only [pows, MonoidHom.range_eq_map, Subgroup.map_map, hcomm]
  have hKpow : g.ker.map (powMonoidHom p : A →* A) ≤ g.ker := by
    rintro _ ⟨k, hk, rfl⟩
    exact g.ker.pow_mem hk p

  have eA : pIdx p (⊤ : Subgroup A) =
      (powMonoidHom p : A →* A).range.relIndex g.ker * pIdx p g.range := by
    have h1 : pIdx p (⊤ : Subgroup A) = (powMonoidHom p : A →* A).range.index := by
      rw [pIdx, Subgroup.relIndex_top_right, pows, ← MonoidHom.range_eq_map]
    rw [h1, ← Subgroup.relIndex_mul_index
      (le_sup_left : (powMonoidHom p : A →* A).range ≤ (powMonoidHom p : A →* A).range ⊔ g.ker),
      Subgroup.relIndex_sup_left, ← Subgroup.comap_map_eq, Subgroup.index_comap, pIdx, hRp]

  have eK : pIdx p g.ker = (g.ker.map (powMonoidHom p : A →* A)).relIndex
      ((powMonoidHom p : A →* A).range ⊓ g.ker) * (powMonoidHom p : A →* A).range.relIndex g.ker := by
    have h0 : pIdx p g.ker = (g.ker.map (powMonoidHom p : A →* A)).relIndex g.ker := rfl
    rw [h0, ← Subgroup.relIndex_mul_relIndex _ ((powMonoidHom p : A →* A).range ⊓ g.ker) _
      (le_inf (Subgroup.map_le_range _ _) hKpow) inf_le_right, Subgroup.inf_relIndex_right]

  have hB : g.ker.comap (powMonoidHom p : A →* A) = (powMonoidHom p : A' →* A').ker.comap g := by
    ext a; simp [MonoidHom.mem_ker, map_pow]
  have hKB : g.ker ≤ g.ker.comap (powMonoidHom p : A →* A) := fun x hx => g.ker.pow_mem hx p
  have hQB : (powMonoidHom p : A →* A).ker ≤ g.ker.comap (powMonoidHom p : A →* A) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    simp [Subgroup.mem_comap, hx]

  have eR : pTor p g.range = g.ker.relIndex (powMonoidHom p : A →* A).ker *
      (g.ker.map (powMonoidHom p : A →* A)).relIndex ((powMonoidHom p : A →* A).range ⊓ g.ker) := by
    have h1 : pTor p g.range = g.ker.relIndex (g.ker.comap (powMonoidHom p : A →* A)) := by
      rw [pTor_eq_card_inf_ker, Subgroup.relIndex_ker, hB, Subgroup.map_comap_eq]
    have h2 : (g.ker ⊔ (powMonoidHom p : A →* A).ker).relIndex
        (g.ker.comap (powMonoidHom p : A →* A)) =
        (g.ker.map (powMonoidHom p : A →* A)).relIndex ((powMonoidHom p : A →* A).range ⊓ g.ker) := by
      rw [← Subgroup.comap_map_eq, Subgroup.relIndex_comap, Subgroup.map_comap_eq]
    rw [h1, ← Subgroup.relIndex_mul_relIndex g.ker (g.ker ⊔ (powMonoidHom p : A →* A).ker) _
      le_sup_left (sup_le hKB hQB), h2,
      Subgroup.relIndex_sup_left]

  have eT : pTor p (⊤ : Subgroup A) = pTor p g.ker * g.ker.relIndex (powMonoidHom p : A →* A).ker := by
    have h := Subgroup.relIndex_mul_relIndex ⊥ (g.ker ⊓ (powMonoidHom p : A →* A).ker)
      (powMonoidHom p : A →* A).ker bot_le inf_le_right
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, Subgroup.inf_relIndex_right] at h
    rw [pTor_eq_card_inf_ker, pTor_eq_card_inf_ker, top_inf_eq, ← h]
  rw [eK] at hIK ⊢
  rw [eR] at hTR ⊢
  rw [eA, eT]
  refine ⟨mul_ne_zero (right_ne_zero_of_mul hIK) hIR, mul_ne_zero hTK (left_ne_zero_of_mul hTR), ?_⟩
  ring

end GlobalTheory.CNorm
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem norm_map_of_basis {F L A B ι : Type} [CommRing F] [CommRing L] [CommRing A] [CommRing B]
    [Algebra F A] [Algebra L B] [Fintype ι] [DecidableEq ι] (φ : F →+* L) (ψ : A →+* B)
    (hψ : ∀ c, ψ (algebraMap F A c) = algebraMap L B (φ c))
    (b : Module.Basis ι F A) (b' : Module.Basis ι L B) (hb : ∀ i, ψ (b i) = b' i) (y : A) :
    Algebra.norm L (ψ y) = φ (Algebra.norm F y) := by
  have hr : ∀ (x : A) (i : ι), b'.repr (ψ x) i = φ (b.repr x i) := by
    intro x i
    have h1 : ψ x = ∑ j, φ (b.repr x j) • b' j := by
      conv_lhs => rw [← b.sum_repr x]

      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, hψ, hb]
    rw [h1, b'.repr_sum_self]
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b', RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, ← hb, ← map_mul, hr]

theorem exists_basis_pow_root {L : Type} [Field L] {p : ℕ} (hp : 0 < p) (a : L) :
    ∃ b : Module.Basis (Fin p) L (AdjoinRoot (X ^ p - C a : L[X])),
      ∀ i, b i = AdjoinRoot.root (X ^ p - C a : L[X]) ^ (i : ℕ) := by
  have hne : (X ^ p - C a : L[X]) ≠ 0 := X_pow_sub_C_ne_zero hp a
  have hd : (AdjoinRoot.powerBasis hne).dim = p := by
    rw [AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C _]
  refine ⟨(AdjoinRoot.powerBasis hne).basis.reindex (finCongr hd), fun i => ?_⟩
  rw [Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, AdjoinRoot.powerBasis_gen]
  simp

theorem powSub_le_kNorm_and_kNorm_map : ∀ (p : ℕ), 0 < p → (∀ (F L : Type) [Field F] [Field L] (φ : F →+* L) (δ : F), powSub p φ ≤ kNorm p φ δ) ∧ ∀ (F L : Type) [Field F] [Field L] (φ : F →+* L) (δ : F), kNorm p (RingHom.id F) δ ≤ kNorm p φ δ := by
  intro p hp
  constructor
  · intro F L _ _ φ δ x hx
    obtain ⟨r, hr⟩ := (mem_powSub p φ x).1 hx
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne'] at hr
      exact (map_ne_zero φ).2 x.ne_zero hr.symm
    obtain ⟨b, -⟩ := exists_basis_pow_root hp (φ δ)
    refine (mem_kNorm p φ δ x).2
      ⟨Units.map (algebraMap L (AdjoinRoot (X ^ p - C (φ δ) : L[X]))).toMonoidHom
        (Units.mk0 r hr0), ?_⟩
    change Algebra.norm L (algebraMap L _ r) = _
    rw [Algebra.norm_algebraMap_of_basis b, Fintype.card_fin, hr]
  · intro F L _ _ φ δ x hx
    obtain ⟨y, hy⟩ := (mem_kNorm p (RingHom.id F) δ x).1 hx
    obtain ⟨b, hb⟩ := exists_basis_pow_root hp (RingHom.id F δ)
    obtain ⟨b', hb'⟩ := exists_basis_pow_root hp (φ δ)
    have hdv : (X ^ p - C (φ δ) : L[X]) ∣ (X ^ p - C (RingHom.id F δ) : F[X]).map φ := by
      simp
    let ψ := AdjoinRoot.map φ _ _ hdv
    refine (mem_kNorm p φ δ x).2 ⟨Units.map ψ.toMonoidHom y, ?_⟩
    change Algebra.norm L (ψ y) = _
    rw [norm_map_of_basis φ ψ (fun c => by simp [ψ]) b b'
      (fun i => by simp [hb, hb', ψ]) y, hy]
    rfl

end GlobalTheory.CNorm
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

section
variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem tensor_repr_map {ι : Type} (b : Module.Basis ι F E) {K K' : Type} [CommRing K] [Algebra F K]
    [CommRing K'] [Algebra F K'] (φ : K →ₐ[F] K') (y : K ⊗[F] E) (i : ι) :
    (Algebra.TensorProduct.basis K' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) y) i =
      φ ((Algebra.TensorProduct.basis K b).repr y i) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul k e =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.basis_repr_tmul,
      Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]
  | add u v hu hv => simp only [map_add (f := _), Finsupp.add_apply, hu, hv]

theorem tensor_norm_map [FiniteDimensional F E] {K K' : Type} [CommRing K] [Algebra F K]
    [CommRing K'] [Algebra F K'] (φ : K →ₐ[F] K') (y : K ⊗[F] E) :
    Algebra.norm K' (Algebra.TensorProduct.map φ (AlgHom.id F E) y) = φ (Algebra.norm K y) := by
  classical
  let b := Module.Free.chooseBasis F E
  rw [Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis K' b),
    Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis K b)]
  rw [show (φ : K → K') = φ.toRingHom from rfl, RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.basis_apply]
  have h1 : (1 : K') ⊗ₜ[F] b j = Algebra.TensorProduct.map φ (AlgHom.id F E) ((1 : K) ⊗ₜ[F] b j) := by
    simp
  rw [h1, ← map_mul, tensor_repr_map b φ]
  rfl

theorem tensor_norm_one_tmul [FiniteDimensional F E] (K : Type) [CommRing K] [Algebra F K] (e : E) :
    Algebra.norm K ((1 : K) ⊗ₜ[F] e) = algebraMap F K (Algebra.norm F e) := by
  classical
  let b := Module.Free.chooseBasis F E
  rw [Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis K b), Algebra.norm_eq_matrix_det b,
    RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.basis_repr_tmul]
  simp

end

theorem tnorm_baseChange : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E], (∀ (K K' : Type) [Field K] [Algebra F K] [Field K'] [Algebra F K'] (_ : K →ₐ[F] K') (x : F), TNorm F E K x → TNorm F E K' x) ∧ (∀ (K : Type) [Field K] [Algebra F K] (e : E), TNorm F E K (Algebra.norm F e)) ∧ ∀ (K : Type) [Field K] [Algebra F K] (x y : F), y ≠ 0 → TNorm F E K (x * y) → TNorm F E K y → TNorm F E K x := by
  intro F E _ _ _ _
  refine ⟨?_, ?_, ?_⟩
  · rintro K K' _ _ _ _ φ x ⟨y, hy⟩
    refine ⟨Algebra.TensorProduct.map φ (AlgHom.id F E) y, ?_⟩
    rw [tensor_norm_map φ y, hy, AlgHom.commutes]
  · intro K _ _ e
    exact ⟨(1 : K) ⊗ₜ[F] e, tensor_norm_one_tmul K e⟩
  · rintro K _ _ x y hy0 ⟨a, ha⟩ ⟨c, hc⟩
    have hyK : algebraMap F K y ≠ 0 := (_root_.map_ne_zero _).mpr hy0
    have hu : IsUnit (Algebra.lmul K (K ⊗[F] E) c) := by
      rw [LinearMap.isUnit_iff_isUnit_det, ← Algebra.norm_apply, hc]
      exact hyK.isUnit
    obtain ⟨d, hd⟩ := ((Module.End.isUnit_iff _).mp hu).2 1
    have hd' : c * d = 1 := hd
    have hn : Algebra.norm K c * Algebra.norm K d = 1 := by
      rw [← map_mul, hd', map_one]
    refine ⟨a * d, ?_⟩
    rw [map_mul, ha, map_mul]
    rw [hc] at hn
    calc algebraMap F K x * algebraMap F K y * Algebra.norm K d
        = algebraMap F K x * (algebraMap F K y * Algebra.norm K d) := by ring
      _ = algebraMap F K x := by rw [hn, mul_one]

end GlobalTheory.CNorm
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep.ReflStep

variable {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E)

theorem herm_sub_smul_left (z x w : Fin n → E) (e : E) :
    hermE c G (z - e • x) w = hermE c G z w - e * hermE c G x w := by
  simp only [hermE, Finset.mul_sum, ← Finset.sum_sub_distrib, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem herm_sub_smul_right (z x w : Fin n → E) (e : E) :
    hermE c G w (z - e • x) = hermE c G w z - c e * hermE c G w x := by
  simp only [hermE, Finset.mul_sum, ← Finset.sum_sub_distrib, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    map_sub, map_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem herm_smul_left (x w : Fin n → E) (e : E) :
    hermE c G (e • x) w = e * hermE c G x w := by
  simp only [hermE, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem herm_conj (h : IsHermForm c G) (x y : Fin n → E) : c (hermE c G x y) = hermE c G y x := by

  simp only [hermE, map_sum, map_mul, h.1, h.2.2.1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem refl_mulVec (x v : Fin n → E) (u : E) :
    refl c G x u *ᵥ v = v + ((u - 1) * hermE c G v x / hermE c G x x) • x := by
  have hd : (G *ᵥ fun b => c (x b)) ⬝ᵥ v = hermE c G v x := by
    simp only [hermE, dotProduct, Matrix.mulVec, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [refl, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, hd]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  ring

theorem exists_refl (h : IsHermForm c G) (x z : Fin n → E) (hz : hermE c G z z = hermE c G x x) (e : E)
    (he : c e = e) (he2 : e * e = 1) (hy : hermE c G (z - e • x) (z - e • x) ≠ 0) :
    ∃ u : E, u * c u = 1 ∧ refl c G (z - e • x) u *ᵥ z = e • x := by
  obtain ⟨a, ha⟩ : ∃ a, a = hermE c G z (z - e • x) := ⟨_, rfl⟩
  have hyy : hermE c G (z - e • x) (z - e • x) = a + c a := by
    rw [ha, herm_conj c G h, herm_sub_smul_left c G z x (z - e • x), herm_sub_smul_left c G z x z,
      herm_sub_smul_right c G z x x, he, hz]
    linear_combination (hermE c G x x) * he2
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hy (by simpa using hyy)
  have hca : c a ≠ 0 := by simpa using ha0
  refine ⟨-c a / a, ?_, ?_⟩
  · rw [map_div₀, map_neg, h.1]
    field_simp
  · rw [refl_mulVec, ← ha]
    have : (-c a / a - 1) * a / hermE c G (z - e • x) (z - e • x) = -1 := by
      rw [div_eq_iff hy, hyy]
      field_simp
      ring
    rw [this]
    simp

end GlobalTheory.UnRep.ReflStep


open GlobalTheory.UnRep.ReflStep in
theorem GlobalTheory.UnRep.exists_refl_prod_mulVec_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ x z : Fin n → E, hermE c G x x ≠ 0 → hermE c G z z = hermE c G x x → ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1 ∧ p.1 ∈ Submodule.span E {x, z}) ∧ (l.map fun p => refl c G p.1 p.2).prod *ᵥ z = x := by
  intro F E _ _ _ _ _ c n G h x z hx hz
  have hxs : x ∈ Submodule.span E ({x, z} : Set (Fin n → E)) := Submodule.subset_span (by simp)
  have hzs : z ∈ Submodule.span E ({x, z} : Set (Fin n → E)) := Submodule.subset_span (by simp)
  have hmem : ∀ e : E, z - e • x ∈ Submodule.span E ({x, z} : Set (Fin n → E)) := fun e =>
    Submodule.sub_mem _ hzs (Submodule.smul_mem _ _ hxs)
  by_cases h1 : hermE c G (z - (1 : E) • x) (z - (1 : E) • x) = 0
  · have h2 : hermE c G (z - (-1 : E) • x) (z - (-1 : E) • x) ≠ 0 := by
      intro h2
      rw [herm_sub_smul_left, herm_sub_smul_right, herm_sub_smul_right] at h1 h2
      simp only [map_one, map_neg, hz] at h1 h2
      apply hx
      have h4 : (4 : E) * hermE c G x x = 0 := by linear_combination h1 + h2
      exact (mul_eq_zero.1 h4).resolve_left (by norm_num)
    obtain ⟨u, hu, hu'⟩ := exists_refl c G h x z hz (-1) (by simp) (by simp) h2
    refine ⟨[(x, -1), (z - (-1 : E) • x, u)], ?_, ?_⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨hx, by simp, hxs⟩
      · exact ⟨h2, hu, hmem _⟩
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [← Matrix.mulVec_mulVec, hu', refl_mulVec, herm_smul_left, ← add_smul]
      have : (-1 : E) + (-1 - 1) * (-1 * hermE c G x x) / hermE c G x x = 1 := by
        field_simp
        ring
      rw [this, one_smul]
  · obtain ⟨u, hu, hu'⟩ := exists_refl c G h x z hz 1 (by simp) (by simp) h1
    refine ⟨[(z - (1 : E) • x, u)], ?_, ?_⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact ⟨h1, hu, hmem _⟩
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [hu', one_smul]
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_isKum : ∀ (p : ℕ) (F : Type) [Field F] [CharZero F] (ζ δ : F), p.Prime → IsPrimitiveRoot ζ p → (∀ r : F, r ^ p ≠ δ) → ∃ (E : Type) (_ : Field E) (_ : Algebra F E) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ := by
  intro p F _ _ ζ δ hp hζ hδ
  have : Fact (Irreducible (X ^ p - C δ)) := ⟨X_pow_sub_C_irreducible_of_prime hp hδ⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  refine ⟨AdjoinRoot (X ^ p - C δ), inferInstance, inferInstance, AdjoinRoot.root _,
    autAdjoinRootXPowSubC p δ hζ.toRootsOfUnity, ?_⟩
  refine ⟨hp, hζ, hδ, ?_, ?_, AdjoinRoot.adjoinRoot_eq_top⟩
  · have h := AdjoinRoot.eval₂_root (X ^ p - C δ)
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h
    rw [h, AdjoinRoot.algebraMap_eq]
  · rw [autAdjoinRootXPowSubC_root, Algebra.smul_def, IsPrimitiveRoot.val_toRootsOfUnity_coe]

end GlobalTheory.CNorm
end
