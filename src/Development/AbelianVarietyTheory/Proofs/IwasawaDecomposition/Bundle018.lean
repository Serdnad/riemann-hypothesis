module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Algebra.Exact.Basic

@[expose] public section

section

open NumberField

namespace GlobalTheory

theorem embeddings_eval_onto (L : Type) [Field L] [NumberField L] (K : Type) [Field K] [CharZero K]
    (z : (L →+* K) → K) :
    ∃ y : Fin (Module.finrank ℚ L) → K, ∀ σ : L →+* K,
      ∑ i, σ (Module.finBasis ℚ L i) * y i = z σ := by
  classical
  set b := Module.finBasis ℚ L
  let M : Matrix (L →+* K) (Fin (Module.finrank ℚ L)) K := Matrix.of fun σ i => σ (b i)

  have hD : LinearIndependent K (fun σ : L →+* K => (σ : L → K)) := by
    have h := linearIndependent_monoidHom L K
    have hinj : Function.Injective (fun σ : L →+* K => (σ.toMonoidHom : L →* K)) := by
      intro σ τ h'
      ext x
      exact DFunLike.congr_fun h' x
    exact h.comp _ hinj
  have hrow : LinearIndependent K M.row := by
    rw [Fintype.linearIndependent_iff] at hD ⊢
    intro g hg
    apply hD g
    have hb : ∀ i, ∑ σ, g σ * σ (b i) = 0 := by
      intro i
      have := congr_fun hg i
      simpa [M, Matrix.row, Finset.sum_apply] using this
    funext x
    rw [← b.sum_repr x]

    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, map_sum]
    have : ∀ σ : L →+* K, ∀ i, σ (b.repr x i • b i) = (b.repr x i : K) * σ (b i) := by
      intro σ i
      rw [Algebra.smul_def, map_mul]
      simp
    simp_rw [this, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h2 : ∑ σ : L →+* K, g σ * ((b.repr x i : K) * σ (b i)) =
        (b.repr x i : K) * ∑ σ : L →+* K, g σ * σ (b i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun σ _ => by ring
    rw [h2, hb i, mul_zero]
  have hrank : M.rank = Fintype.card (L →+* K) := hrow.rank_matrix
  have htop : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Matrix.finrank_range_mulVecLin, hrank, Module.finrank_fintype_fun_eq_card]
  have hz : z ∈ LinearMap.range M.mulVecLin := by rw [htop]; trivial
  obtain ⟨y, hy⟩ := hz
  refine ⟨y, fun σ => ?_⟩
  have := congr_fun hy σ
  simpa [M, Matrix.mulVec, dotProduct] using this

end GlobalTheory
end

section

open NumberField Matrix

namespace GlobalTheory

theorem det_one_add_smul_poly_eval {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    Polynomial.eval z (det (1 + (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C)) = det (1 + z • M) := by
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.one_apply]
  split_ifs <;> simp [mul_comm]

theorem det_one_add_smul_poly_ne_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    det (1 + (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C) ≠ 0 := by
  intro h
  have := det_one_add_smul_poly_eval M 0
  rw [h] at this
  simp at this

theorem finite_det_one_add_smul_eq_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    {z : ℂ | det (1 + z • M) = 0}.Finite := by
  refine (Polynomial.rootSet_finite (det (1 + (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C)) ℂ).subset ?_
  intro z hz
  rw [Polynomial.mem_rootSet_of_ne (det_one_add_smul_poly_ne_zero M)]
  simp only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id]
  rw [det_one_add_smul_poly_eval]
  exact hz

theorem exists_normOne_det_one_add_ne_zero : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ),
    ∃ a : L, a * (IsCMField.complexConj L : L →+* L) a = 1 ∧ ∀ σ : L →+* ℂ, (1 + σ a • X σ).det ≠ 0 := by
  intro L _ _ _ n X
  set c : L →+* L := (IsCMField.complexConj L : L →+* L) with hc
  have hcc : ∀ x, c (c x) = x := fun x => IsCMField.complexConj_apply_apply L x
  obtain ⟨μ, hμ⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one L)
  have hμ' : c μ ≠ μ := hμ
  have hne : ∀ t : ℚ, (t : L) + μ ≠ 0 := by
    intro t h
    apply hμ'
    have h1 : μ = -(t : L) := by linear_combination h
    rw [h1, map_neg, map_ratCast]
  have hne' : ∀ t : ℚ, (t : L) + c μ ≠ 0 := by
    intro t h
    apply hμ'
    have h1 : c μ = -(t : L) := by linear_combination h
    have h2 : μ = -(t : L) := by rw [← hcc μ, h1, map_neg, map_ratCast]
    rw [h1, h2]
  let a : ℚ → L := fun t => ((t : L) + μ) / ((t : L) + c μ)
  have hca : ∀ t, c (a t) = ((t : L) + c μ) / ((t : L) + μ) := by
    intro t
    simp only [a, map_div₀, map_add (f := _), map_ratCast, hcc]
  have hnorm : ∀ t, a t * c (a t) = 1 := by
    intro t
    rw [hca]
    simp only [a]
    field_simp [hne t, hne' t]
  have hinj : Function.Injective a := by
    intro t s h
    simp only [a] at h
    rw [div_eq_div_iff (hne' t) (hne' s)] at h
    have h3 : ((t : L) - s) * (c μ - μ) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact_mod_cast sub_eq_zero.mp h4
    · exact absurd (sub_eq_zero.mp h4) hμ'
  have hfin : (⋃ σ : L →+* ℂ, (fun t => σ (a t)) ⁻¹' {z : ℂ | det (1 + z • X σ) = 0}).Finite := by
    refine Set.finite_iUnion fun σ => ?_
    exact (finite_det_one_add_smul_eq_zero (X σ)).preimage
      (fun t _ s _ h => hinj (σ.injective h))
  obtain ⟨t, ht⟩ := (Set.infinite_univ (α := ℚ)).diff hfin |>.nonempty
  refine ⟨a t, hnorm t, fun σ hσ => ht.2 ?_⟩
  exact Set.mem_iUnion.mpr ⟨σ, hσ⟩

end GlobalTheory
end

section

open NumberField Matrix

namespace GlobalTheory

variable {n : ℕ}

theorem cayleyInv_one_sub (X : Matrix (Fin n) (Fin n) ℂ) (hu : IsUnit (X + 1).det) :
    1 - (X - 1) * (X + 1)⁻¹ = (2:ℂ) • (X + 1)⁻¹ := by
  have h1 : (X + 1) * (X + 1)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have e : (X + 1) - (X - 1) = (1 : Matrix (Fin n) (Fin n) ℂ) + 1 := by abel
  calc 1 - (X - 1) * (X + 1)⁻¹ = (X + 1) * (X + 1)⁻¹ - (X - 1) * (X + 1)⁻¹ := by rw [h1]
    _ = ((X + 1) - (X - 1)) * (X + 1)⁻¹ := by rw [← Matrix.sub_mul]
    _ = (2:ℂ) • (X + 1)⁻¹ := by rw [e, add_mul, one_mul, two_smul]

theorem cayleyInv_one_add (X : Matrix (Fin n) (Fin n) ℂ) (hu : IsUnit (X + 1).det) :
    1 + (X - 1) * (X + 1)⁻¹ = X * ((2:ℂ) • (X + 1)⁻¹) := by
  have h1 : (X + 1) * (X + 1)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have e : (X + 1) + (X - 1) = X + X := by abel
  calc 1 + (X - 1) * (X + 1)⁻¹ = (X + 1) * (X + 1)⁻¹ + (X - 1) * (X + 1)⁻¹ := by rw [h1]
    _ = (X + X) * (X + 1)⁻¹ := by rw [← add_mul, e]
    _ = X * ((2:ℂ) • (X + 1)⁻¹) := by rw [mul_smul_comm, two_smul, add_mul]

theorem cayleyInv_det_one_sub (X : Matrix (Fin n) (Fin n) ℂ) (hu : IsUnit (X + 1).det) :
    IsUnit (1 - (X - 1) * (X + 1)⁻¹).det := by
  rw [cayleyInv_one_sub _ hu, isUnit_iff_ne_zero]
  intro h0
  have h2 : ((2:ℂ) • (X + 1)⁻¹ * (X + 1)).det = (2:ℂ) ^ n := by
    rw [smul_mul_assoc, nonsing_inv_mul _ hu, det_smul, det_one, mul_one, Fintype.card_fin]
  rw [det_mul, h0, zero_mul] at h2
  exact (pow_ne_zero n two_ne_zero) h2.symm

theorem cayleyInv_skew (X Z : Matrix (Fin n) (Fin n) ℂ) (hXZ : X * Zᵀ = 1)
    (hX : IsUnit (X + 1).det) (hZ : IsUnit (Z + 1).det) :
    (Z - 1) * (Z + 1)⁻¹ = -((X - 1) * (X + 1)⁻¹)ᵀ := by
  have hZX : Zᵀ * X = 1 := mul_eq_one_comm.mp hXZ
  have hAZ : Xᵀ * Z = 1 := by
    simpa [transpose_mul, transpose_transpose, transpose_one] using congrArg Matrix.transpose hZX
  have hA : IsUnit (Xᵀ + 1).det := by
    rw [show Xᵀ + 1 = (X + 1)ᵀ by rw [transpose_add, transpose_one], det_transpose]; exact hX
  have key : (Xᵀ + 1) * (Z - 1) = -((Xᵀ - 1) * (Z + 1)) := by
    simp only [mul_sub, mul_add, sub_mul, add_mul, mul_one, one_mul, hAZ]; abel
  rw [transpose_mul, transpose_nonsing_inv, transpose_add, transpose_sub, transpose_one]
  calc (Z - 1) * (Z + 1)⁻¹ = (Xᵀ + 1)⁻¹ * ((Xᵀ + 1) * (Z - 1)) * (Z + 1)⁻¹ := by
        rw [← Matrix.mul_assoc, nonsing_inv_mul _ hA, Matrix.one_mul]
    _ = (Xᵀ + 1)⁻¹ * (-((Xᵀ - 1) * (Z + 1))) * (Z + 1)⁻¹ := by rw [key]
    _ = -((Xᵀ + 1)⁻¹ * (Xᵀ - 1)) := by
        rw [mul_neg, neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hZ,
          Matrix.mul_one]

theorem unitary_isCayley_of_det_ne_zero : ∀ (L : Type) [Field L] [NumberField L] (n : ℕ)
    (X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ),
    (∀ σ, X σ * (X (ComplexEmbedding.conjugate σ))ᵀ = 1) → (∀ σ, (1 + X σ).det ≠ 0) →
    ∃ Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, (∀ σ, Y (ComplexEmbedding.conjugate σ) = -(Y σ)ᵀ) ∧
      (∀ σ, (1 - Y σ).det ≠ 0) ∧ ∀ σ, (1 + Y σ) * (1 - Y σ)⁻¹ = X σ := by
  intro L _ _ n X hX hdet
  have hu : ∀ σ, IsUnit (X σ + 1).det := fun σ => by
    rw [add_comm]; exact isUnit_iff_ne_zero.mpr (hdet σ)
  refine ⟨fun σ => (X σ - 1) * (X σ + 1)⁻¹, fun σ => ?_, fun σ => ?_, fun σ => ?_⟩
  · exact cayleyInv_skew (X σ) (X (ComplexEmbedding.conjugate σ)) (hX σ) (hu σ) (hu _)
  · exact isUnit_iff_ne_zero.mp (cayleyInv_det_one_sub (X σ) (hu σ))
  · show (1 + (X σ - 1) * (X σ + 1)⁻¹) * (1 - (X σ - 1) * (X σ + 1)⁻¹)⁻¹ = X σ
    have hY := cayleyInv_det_one_sub (X σ) (hu σ)
    rw [cayleyInv_one_add _ (hu σ), ← cayleyInv_one_sub _ (hu σ), Matrix.mul_assoc,
      mul_nonsing_inv _ hY, Matrix.mul_one]

end GlobalTheory
end

section

open IsLocalRing

namespace GlobalTheory

theorem adicCompletion_evalₐ_of_val {R : Type} [CommRing R] (I : Ideal R) (x : AdicCompletion I R)
    {n : ℕ} (d : R) (hd : x.val n = Submodule.Quotient.mk d) :
    AdicCompletion.evalₐ I n x = Ideal.Quotient.mk (I ^ n) d := by
  rw [← AdicCompletion.factor_eval_eq_evalₐ I x (by simp), AdicCompletion.eval_apply]
  erw [hd]
  rfl

theorem adicCompletion_val_of_le {R : Type} [CommRing R] (I : Ideal R) (x : AdicCompletion I R)
    {m n : ℕ} (hmn : m ≤ n) (d : R) (hd : x.val n = Submodule.Quotient.mk d) :
    x.val m = Submodule.Quotient.mk d := by
  rw [← x.prop hmn, hd]
  rfl

theorem adicCompletion_injective_ringHom_of_finite
    (D N : Type) [CommRing D] [CommRing N] [IsNoetherianRing D] [Algebra D N]
    [Module.Finite D N] (hinj : Function.Injective (algebraMap D N)) (J : Ideal D) :
    ∃ f : AdicCompletion J D →+* AdicCompletion (J.map (algebraMap D N)) N,
      Function.Injective f := by
  set φ := algebraMap D N with hφ
  have hle : ∀ n : ℕ, J ^ n ≤ ((J.map φ) ^ n).comap φ := fun n => by
    rw [← Ideal.map_pow]; exact Ideal.le_comap_map
  let g : (n : ℕ) → AdicCompletion J D →+* N ⧸ (J.map φ) ^ n := fun n =>
    (Ideal.quotientMap ((J.map φ) ^ n) φ (hle n)).comp (AdicCompletion.evalₐ J n).toRingHom
  have hg : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow (J.map φ) hmn).comp (g n) = g m := by
    intro m n hmn
    ext x
    obtain ⟨d, hd⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
    have hn := adicCompletion_evalₐ_of_val J x d hd.symm
    have hm := adicCompletion_evalₐ_of_val J x d (adicCompletion_val_of_le J x hmn d hd.symm)
    simp only [g, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hn, hm,
      Ideal.quotientMap_mk]
    rfl
  refine ⟨AdicCompletion.liftRingHom _ g hg, ?_⟩
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have hmap := AdicCompletion.map_injective J (f := Algebra.linearMap D N) hinj
  apply hmap
  rw [map_zero]
  apply AdicCompletion.ext
  intro n
  obtain ⟨d, hd⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
  have h1 := adicCompletion_evalₐ_of_val J x d hd.symm
  have h2 := congrArg (AdicCompletion.evalₐ (J.map φ) n) hx
  rw [AdicCompletion.evalₐ_liftRingHom, map_zero] at h2
  simp only [g, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, h1,
    Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at h2
  rw [AdicCompletion.map_val_apply]
  erw [← hd]
  rw [LinearMap.reduceModIdeal_apply]
  refine ((Submodule.Quotient.mk_eq_zero _).2 ?_).trans rfl
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow]
  exact h2

end GlobalTheory
end

section

open IsLocalRing

namespace GlobalTheory.AdicQuot

open AdicCompletion

variable {A : Type} [CommRing A] (J q : Ideal A)

theorem mem_smul_top_iff (n : ℕ) (b : A ⧸ q) :
    b ∈ (J ^ n • ⊤ : Submodule A (A ⧸ q)) ↔ b ∈ (J.map (Ideal.Quotient.mk q)) ^ n := by
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow]
  rfl

theorem pow_le_comap (n : ℕ) :
    J ^ n ≤ ((J.map (Ideal.Quotient.mk q)) ^ n).comap (Ideal.Quotient.mk q) := by
  rw [← Ideal.map_pow]; exact Ideal.le_comap_map

noncomputable def lev (n : ℕ) :
    AdicCompletion J A →+* (A ⧸ q) ⧸ (J.map (Ideal.Quotient.mk q)) ^ n :=
  (Ideal.quotientMap _ (Ideal.Quotient.mk q) (pow_le_comap J q n)).comp (evalₐ J n).toRingHom

theorem lev_mk (n : ℕ) (s : AdicCauchySequence J A) :
    lev J q n (AdicCompletion.mk J A s) = Ideal.Quotient.mk _ (Ideal.Quotient.mk q (s n)) := by
  simp [lev, evalₐ_mk, Ideal.quotientMap_mk]

theorem lev_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow _ hle).comp (lev J q n) = lev J q m := by
  ext x
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J A x
  have h1 := s.property hle
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  simp only [RingHom.comp_apply, lev_mk]
  rw [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.Quotient.eq, ← map_sub]
  have h3 : s n - s m ∈ J ^ m := by rw [← neg_sub]; exact neg_mem h1
  exact Ideal.mem_comap.mp (pow_le_comap J q m h3)

noncomputable def psi : AdicCompletion J A →+* AdicCompletion (J.map (Ideal.Quotient.mk q)) (A ⧸ q) :=
  AdicCompletion.liftRingHom _ (lev J q) (fun hle ↦ lev_compat J q hle)

theorem evalₐ_psi (n : ℕ) (x : AdicCompletion J A) :
    evalₐ _ n (psi J q x) = lev J q n x := by
  simp [psi]

theorem map_val_mk_eq_iff (s : AdicCauchySequence J A) (n : ℕ) (c : A ⧸ q) :
    (map J (Submodule.mkQ q) (AdicCompletion.mk J A s)).val n = Submodule.Quotient.mk c ↔
      lev J q n (AdicCompletion.mk J A s) = Ideal.Quotient.mk _ c := by
  rw [map_val_apply, mk_apply_coe, lev_mk, Submodule.mkQ_apply, LinearMap.reduceModIdeal_apply,
    Submodule.Quotient.eq, Ideal.Quotient.eq, mem_smul_top_iff]
  rfl

theorem ker_psi [IsNoetherianRing A] :
    RingHom.ker (psi J q) = q.map (algebraMap A (AdicCompletion J A)) := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    have hz : map J (Submodule.mkQ q) x = 0 := by
      obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J A x
      ext n
      have := (map_val_mk_eq_iff J q s n 0).mpr (by rw [← evalₐ_psi, hx, _root_.map_zero, _root_.map_zero])
      simpa using this
    obtain ⟨y, rfl⟩ := ((AdicCompletion.map_exact (I := J) (f := q.subtype) (g := q.mkQ)
      Subtype.val_injective (LinearMap.exact_subtype_mkQ q) (Submodule.mkQ_surjective q)) x).mp hz
    obtain ⟨t, rfl⟩ := ofTensorProduct_surjective_of_finite J q y
    clear hx hz
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      rw [ofTensorProduct_tmul, map_smul, map_of, smul_eq_mul]
      have hm : (of J A) (q.subtype m) = algebraMap A (AdicCompletion J A) (m : A) := by
        rw [AdicCompletion.algebraMap_apply]; rfl
      rw [hm]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ m.2)
    | add a b ha hb => rw [map_add (f := _), map_add (f := _)]; exact add_mem ha hb
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    refine ext_evalₐ fun n ↦ ?_
    rw [evalₐ_psi, _root_.map_zero, lev, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes, Ideal.Quotient.algebraMap_eq, Ideal.quotientMap_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha, _root_.map_zero]

theorem psi_surjective [IsNoetherianRing A] : Function.Surjective (psi J q) := by
  intro y
  obtain ⟨t, rfl⟩ := AdicCompletion.mk_surjective _ _ y
  let t' : AdicCauchySequence J (A ⧸ q) := ⟨t.val, fun {m n} hmn ↦ by
    have h := t.property hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
    rw [SModEq.sub_mem, mem_smul_top_iff]; exact h⟩
  obtain ⟨x, hx⟩ := map_surjective J (Submodule.mkQ_surjective q) (AdicCompletion.mk J _ t')
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J A x
  refine ⟨AdicCompletion.mk J A s, ext_evalₐ fun n ↦ ?_⟩
  rw [evalₐ_psi, evalₐ_mk]
  refine (map_val_mk_eq_iff J q s n (t n)).mp ?_
  rw [hx]; rfl

end GlobalTheory.AdicQuot

theorem GlobalTheory.adicCompletion_quotient_ringEquiv :
    ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (J q : Ideal A),
      Nonempty ((AdicCompletion J A ⧸ q.map (algebraMap A (AdicCompletion J A))) ≃+*
        AdicCompletion (J.map (Ideal.Quotient.mk q)) (A ⧸ q)) := by
  intro A _ _ J q
  exact ⟨(Ideal.quotEquivOfEq (GlobalTheory.AdicQuot.ker_psi J q).symm).trans
    (RingHom.quotientKerEquivOfSurjective (GlobalTheory.AdicQuot.psi_surjective J q))⟩
end

section

namespace GlobalTheory.MulSubOneValuation

theorem mul_sub_one_le_of_valuation {K Γ : Type*} [CommRing K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) {n : ℕ} {γ : Γ} (hγ : γ ≤ 1) {A B : Matrix (Fin n) (Fin n) K}
    (hA : ∀ r s, v (A r s - (1 : Matrix (Fin n) (Fin n) K) r s) ≤ γ)
    (hB : ∀ r s, v (B r s - (1 : Matrix (Fin n) (Fin n) K) r s) ≤ γ) (r s : Fin n) :
    v ((A * B) r s - (1 : Matrix (Fin n) (Fin n) K) r s) ≤ γ := by

  have hM : A * B - 1 = (A - 1) + (B - 1) + (A - 1) * (B - 1) := by noncomm_ring
  have he : (A * B) r s - (1 : Matrix (Fin n) (Fin n) K) r s =
      (A - 1) r s + (B - 1) r s + ((A - 1) * (B - 1)) r s := by
    simpa [Matrix.sub_apply, Matrix.add_apply] using congrArg (fun M : Matrix (Fin n) (Fin n) K => M r s) hM
  rw [he, Matrix.mul_apply]
  refine v.map_add_le (v.map_add_le (hA r s) (hB r s)) (v.map_sum_le fun k _ => ?_)
  calc v ((A - 1) r k * (B - 1) k s) = v ((A - 1) r k) * v ((B - 1) k s) := map_mul v _ _
    _ ≤ γ * γ := mul_le_mul' (hA r k) (hB k s)
    _ ≤ γ := mul_le_of_le_one_right' hγ

theorem mul_sub_one_le {E : Type} [Field E] [NumberField E]
    {P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)} {n N : ℕ}
    {A B : Matrix (Fin n) (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion E P)}
    (hA : ∀ r s : Fin n, (Valued.v : IsDedekindDomain.HeightOneSpectrum.adicCompletion E P →
      WithZero (Multiplicative ℤ)) (A r s - (1 : Matrix (Fin n) (Fin n)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion E P)) r s) ≤ WithZero.exp (-(N : ℤ)))
    (hB : ∀ r s : Fin n, (Valued.v : IsDedekindDomain.HeightOneSpectrum.adicCompletion E P →
      WithZero (Multiplicative ℤ)) (B r s - (1 : Matrix (Fin n) (Fin n)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion E P)) r s) ≤ WithZero.exp (-(N : ℤ)))
    (r s : Fin n) :
    (Valued.v : IsDedekindDomain.HeightOneSpectrum.adicCompletion E P →
      WithZero (Multiplicative ℤ)) ((A * B) r s - (1 : Matrix (Fin n) (Fin n)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion E P)) r s) ≤ WithZero.exp (-(N : ℤ)) := by
  have hγ : WithZero.exp (-(N : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  exact mul_sub_one_le_of_valuation Valued.v hγ hA hB r s

end GlobalTheory.MulSubOneValuation
end
