module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Ramification

@[expose] public section

section

namespace GroundTheory.Global

open IsDedekindDomain NumberField WithZeroMulInt WithZero Topology Filter

noncomputable section

namespace SemiLocal

variable {L : Type*} [Field L] [NumberField L]

theorem exists_sub_mem_pow_of_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → HeightOneSpectrum (𝓞 L)) (hw : Function.Injective w) (i : ι) (n : ℕ) :
    ∃ a : 𝓞 L, ∀ j, a - (if j = i then 1 else 0) ∈ (w j).asIdeal ^ n := by
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Finset.univ)
    (fun j ↦ (w j).asIdeal) (fun _ ↦ n) (fun j _ ↦ (w j).prime)
    (fun j _ k _ hjk h ↦ hjk (hw (HeightOneSpectrum.ext h)))
    (fun j ↦ if j.1 = i then 1 else 0)
  exact ⟨y, fun j ↦ hy j (Finset.mem_univ j)⟩

theorem norm_algebraMap_le_of_mem_pow (w : HeightOneSpectrum (𝓞 L)) (a : 𝓞 L) (n : ℕ)
    (ha : a ∈ w.asIdeal ^ n) :
    ‖algebraMap (𝓞 L) (w.adicCompletion L) a‖ ≤
      ((toNNReal (HeightOneSpectrum.absNorm_ne_zero w) (exp (-1 : ℤ)) : ℝ)) ^ n := by
  rw [IsScalarTower.algebraMap_apply (𝓞 L) L (w.adicCompletion L),
    HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply, ← FinitePlace.embedding_apply, FinitePlace.norm_embedding_int, ← NNReal.coe_pow,
    NNReal.coe_le_coe, ← map_pow]
  apply (toNNReal_strictMono (HeightOneSpectrum.one_lt_absNorm_nnreal w)).monotone
  rw [← exp_nsmul, smul_neg, nsmul_one]
  exact (w.intValuation_le_pow_iff_mem a n).2 ha

theorem toNNReal_exp_neg_one_lt_one (w : HeightOneSpectrum (𝓞 L)) :
    ((toNNReal (HeightOneSpectrum.absNorm_ne_zero w) (exp (-1 : ℤ)) : ℝ)) < 1 := by
  rw [← NNReal.coe_one, NNReal.coe_lt_coe,
    toNNReal_lt_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal w)]
  rw [← exp_zero, exp_lt_exp]
  norm_num

theorem denseRange_algebraMap_pi {ι : Type*} [Finite ι] (w : ι → HeightOneSpectrum (𝓞 L))
    (hw : Function.Injective w) :
    DenseRange (fun x : L ↦ fun i ↦ algebraMap L ((w i).adicCompletion L) x) := by
  classical
  have := Fintype.ofFinite ι
  let f : L →+* ((i : ι) → (w i).adicCompletion L) := RingHom.pi fun i ↦ algebraMap L _
  let S : Subring ((i : ι) → (w i).adicCompletion L) := f.range.topologicalClosure
  have hδ : ∀ i, Pi.single i 1 ∈ S := by
    intro i
    choose a ha using fun n ↦ exists_sub_mem_pow_of_injective w hw i n
    refine mem_closure_of_tendsto (b := atTop) (f := fun n ↦ f (algebraMap (𝓞 L) L (a n))) ?_
      (Eventually.of_forall fun n ↦ ⟨_, rfl⟩)
    rw [tendsto_pi_nhds]
    intro j
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (NNReal.coe_nonneg _)
        (toNNReal_exp_neg_one_lt_one (w j)))
    have h := norm_algebraMap_le_of_mem_pow (w j) _ n (ha n j)
    refine le_of_eq_of_le ?_ h
    congr 1
    by_cases hji : j = i
    · subst hji
      simp [f, ← IsScalarTower.algebraMap_apply]
    · simp [f, hji, ← IsScalarTower.algebraMap_apply]
  have hE : ∀ y : ι → L, (fun i ↦ algebraMap L ((w i).adicCompletion L) (y i)) ∈ S := by
    intro y
    have : (fun i ↦ algebraMap L ((w i).adicCompletion L) (y i)) =
        ∑ i, Pi.single i 1 * f (y i) := by
      funext j
      simp only [Finset.sum_apply, Pi.mul_apply, f, RingHom.pi_apply]
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb.symm]
      · simp
    rw [this]
    exact S.sum_mem fun i _ ↦ S.mul_mem (hδ i) (f.range.le_topologicalClosure ⟨y i, rfl⟩)
  have hdense : DenseRange (fun y : ι → L ↦ fun i ↦ algebraMap L ((w i).adicCompletion L) (y i)) :=
    DenseRange.piMap fun i ↦ HeightOneSpectrum.denseRange_algebraMap L (w i)
  have hsub : Set.range (fun y : ι → L ↦ fun i ↦ algebraMap L ((w i).adicCompletion L) (y i)) ⊆
      closure (Set.range f) := by
    rintro _ ⟨y, rfl⟩
    exact hE y
  exact dense_closure.1 (hdense.mono hsub)

end SemiLocal

end

end GroundTheory.Global
end

section

namespace GroundTheory.Global

open IsDedekindDomain NumberField TensorProduct Module Matrix

noncomputable section

namespace SemiLocal

theorem det_blockDiagonal' {α : Type*} [Fintype α] [DecidableEq α] {m : α → Type*}
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {R : Type*} [CommRing R]
    (d : ∀ i, Matrix (m i) (m i) R) : (blockDiagonal' d).det = ∏ k, (d k).det := by
  classical
  let _ : LinearOrder α := LinearOrder.lift' (Fintype.equivFin α) (Fintype.equivFin α).injective
  rw [(blockTriangular_blockDiagonal' d).det_fintype]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  have : (blockDiagonal' d).toSquareBlock Sigma.fst k =
      (d k).submatrix (Equiv.sigmaSubtype k) (Equiv.sigmaSubtype k) := by
    ext ⟨⟨i, a⟩, hi⟩ ⟨⟨j, b⟩, hj⟩
    dsimp only at hi hj
    subst hi hj
    simp [toSquareBlock_def, Equiv.sigmaSubtype]
  rw [this, det_submatrix_equiv_self]

variable {R : Type*} [Field R] {ι : Type*} [Fintype ι] {S : ι → Type*} [∀ i, CommRing (S i)]
  [∀ i, Algebra R (S i)] [∀ i, Module.Finite R (S i)]

omit [∀ i, Module.Finite R (S i)] in
theorem leftMulMatrix_pi [DecidableEq ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
    [∀ i, DecidableEq (κ i)] (b : ∀ i, Basis (κ i) R (S i)) (x : ∀ i, S i) :
    Algebra.leftMulMatrix (Pi.basis b) x =
      blockDiagonal' fun i ↦ Algebra.leftMulMatrix (b i) (x i) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rw [Algebra.leftMulMatrix_eq_repr_mul, blockDiagonal'_apply', Pi.basis_repr, Pi.basis_apply]
  by_cases h : i = j
  · subst h
    simp [Algebra.leftMulMatrix_eq_repr_mul]
  · simp [h]

theorem norm_pi (x : ∀ i, S i) : Algebra.norm R x = ∏ i, Algebra.norm R (x i) := by
  classical
  let b := fun i ↦ Module.finBasis R (S i)
  rw [Algebra.norm_eq_matrix_det (Pi.basis b), leftMulMatrix_pi, det_blockDiagonal']
  exact Finset.prod_congr rfl fun i _ ↦ (Algebra.norm_eq_matrix_det (b i) (x i)).symm

theorem trace_pi (x : ∀ i, S i) :
    Algebra.trace R (∀ i, S i) x = ∑ i, Algebra.trace R (S i) (x i) := by
  classical
  let b := fun i ↦ Module.finBasis R (S i)
  rw [Algebra.trace_eq_matrix_trace (Pi.basis b), leftMulMatrix_pi, trace_blockDiagonal']
  exact Finset.sum_congr rfl fun i _ ↦ (Algebra.trace_eq_matrix_trace (b i) (x i)).symm

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K))

theorem trace_one_tmul (x : L) :
    Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)
        ((1 : v.adicCompletion K) ⊗ₜ[K] x) =
      algebraMap K (v.adicCompletion K) (Algebra.trace K L x) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange]

end SemiLocal

end

end GroundTheory.Global
end

section

namespace GroundTheory.Global

open IsDedekindDomain NumberField

noncomputable section

namespace SemiLocal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]


variable (L) in
abbrev PlacesOver (v : HeightOneSpectrum (𝓞 K)) : Type _ :=
  {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal}

instance (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver (L := L) v) : w.1.asIdeal.LiesOver v.asIdeal :=
  w.2


variable (L) in
def placesOverEquiv (v : HeightOneSpectrum (𝓞 K)) :
    PlacesOver (L := L) v ≃ v.asIdeal.primesOver (𝓞 L) where
  toFun w := ⟨w.1.asIdeal, w.1.isPrime, w.2⟩
  invFun P := ⟨⟨P.1, P.2.1, (have := P.2.2; Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P.1)⟩, P.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (v : HeightOneSpectrum (𝓞 K)) : Fintype (PlacesOver (L := L) v) :=
  Fintype.ofEquiv _ (placesOverEquiv (L := L) v).symm

section Map

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

def completionMap : v.adicCompletion K →+* w.adicCompletion L :=
  (HeightOneSpectrum.adicCompletion.equiv L w).symm.toRingHom.comp <|
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
      (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver (K := K) L v w).continuous).comp
      (HeightOneSpectrum.adicCompletion.equiv K v).toRingHom

theorem continuous_completionMap : Continuous (completionMap v w) :=
  (HeightOneSpectrum.adicCompletion.continuous_ofCompletion L w).comp <|
    UniformSpace.Completion.continuous_map.comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion K v)

theorem completionMap_algebraMap (x : K) :
    completionMap v w (algebraMap K (v.adicCompletion K) x) =
      algebraMap K (w.adicCompletion L) x := by
  apply HeightOneSpectrum.adicCompletion.ext
  change UniformSpace.Completion.map _
      ((algebraMap K (WithVal (v.valuation K)) x : WithVal _) :
        UniformSpace.Completion (WithVal (v.valuation K))) =
    ((algebraMap K (WithVal (w.valuation L)) x : WithVal _) :
        UniformSpace.Completion (WithVal (w.valuation L)))
  rw [UniformSpace.Completion.map_coe
    (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver (K := K) L v w)]
  rfl

theorem valued_completionMap (x : v.adicCompletion K) :
    Valued.v (completionMap v w x) = Valued.v x ^ w.asIdeal.ramificationIdx (𝓞 K) := by
  set e := w.asIdeal.ramificationIdx (𝓞 K) with he
  have he0 : e ≠ 0 := (Ideal.ramificationIdx_pos (R := 𝓞 K) w.asIdeal).ne'
  have hK : ∀ k : K, Valued.v (completionMap v w (algebraMap K _ k)) =
      Valued.v (algebraMap K (v.adicCompletion K) k) ^ e := by
    intro k
    rw [completionMap_algebraMap, IsScalarTower.algebraMap_apply K L (w.adicCompletion L),
      HeightOneSpectrum.algebraMap_adicCompletion, HeightOneSpectrum.algebraMap_adicCompletion]
    simpa only [Function.comp_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      Algebra.algebraMap_self, RingHom.id_apply, he] using
      (HeightOneSpectrum.valuation_liesOver L v w k).symm
  have hclosed : IsClosed
      {x : v.adicCompletion K | Valued.v (completionMap v w x) = Valued.v x ^ e} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x0 hx0
    have h0 : x0 ≠ 0 := by
      rintro rfl
      simp [zero_pow he0] at hx0
    have h1 : Valued.v x0 ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    have h2 : Valued.v (completionMap v w x0) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 ((map_ne_zero_iff _ (completionMap v w).injective).2 h0)
    filter_upwards [Valued.locally_const h1,
      (continuous_completionMap v w).continuousAt.preimage_mem_nhds (Valued.locally_const h2)]
      with x hx hx'
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff] at hx hx' hx0 ⊢
    rwa [hx, hx']
  exact (HeightOneSpectrum.denseRange_algebraMap K v).induction_on x hclosed hK

scoped instance algebraCompletion : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  (completionMap v w).toAlgebra

theorem algebraMap_completion_eq :
    algebraMap (v.adicCompletion K) (w.adicCompletion L) = completionMap v w := rfl

scoped instance : IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) :=
  .of_algebraMap_eq fun x ↦ (completionMap_algebraMap v w x).symm

scoped instance : ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) where
  continuous_smul := ((continuous_completionMap v w).comp continuous_fst).mul continuous_snd

end Map

end SemiLocal

end

end GroundTheory.Global
end
