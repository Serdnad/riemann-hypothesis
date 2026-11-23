module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenericBlockMatrixIsBlockDiag
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle095
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CauchyBinet
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepShape

theorem upper_of_steps : ∀ (N j : ℕ) (a b ca cb : Fin N) (C : Matrix (Fin N) (Fin N) ℂ), j ≤ N → (b : ℕ) = a + 1 →
    ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsBlockDiag j C →
    (∀ i, IsProperStep N j i → i ≠ a → ∀ r c, c ∈ stepCols N j i → r ∉ stepCols N j i → C r c = 0) →
    ∀ r c, c < r → ¬ (r = cb ∧ c = ca) → C r c = 0 := by
  intro N j a b ca cb C hj hb hcase hca hcb hbd hv r c hcr hne
  have hr := r.2
  have hc := c.2
  have ha := a.2
  have hb' := b.2
  have hcb' := cb.2
  have hlt : (c : ℕ) < r := hcr
  have hba : b ≠ a := by
    intro h
    rw [h] at hb
    omega
  unfold lastCol at hca
  by_cases hs : ((r : ℕ) < N - j ↔ (c : ℕ) < N - j)
  swap
  · exact hbd r c hs
  by_cases hW : N - j ≤ (c : ℕ)
  · obtain ⟨i, hi⟩ : ∃ i : Fin N, (i : ℕ) = c - (N - j) := ⟨⟨(c : ℕ) - (N - j), by omega⟩, rfl⟩
    by_cases hia : i = a
    · have hai : (a : ℕ) = c - (N - j) := by rw [← hia]; exact hi
      rw [if_pos (by omega)] at hca
      have hcc : c = ca := Fin.ext (by omega)
      have hrcb : (r : ℕ) ≠ cb := fun h => hne ⟨Fin.ext h, hcc⟩
      refine hv b ⟨by omega, by omega⟩ hba r c ?_ ?_
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_pos (by omega)]
        omega
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_pos (by omega)]
        omega
    · refine hv i ⟨by omega, by omega⟩ hia r c ?_ ?_
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_pos (by omega)]
        omega
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_pos (by omega)]
        omega
  · obtain ⟨i, hi⟩ : ∃ i : Fin N, (i : ℕ) = j + c := ⟨⟨j + (c : ℕ), by omega⟩, rfl⟩
    by_cases hia : i = a
    · have hai : (a : ℕ) = j + c := by rw [← hia]; exact hi
      rw [if_neg (by omega)] at hca
      have hcc : c = ca := Fin.ext (by omega)
      have hrcb : (r : ℕ) ≠ cb := fun h => hne ⟨Fin.ext h, hcc⟩
      refine hv b ⟨by omega, by omega⟩ hba r c ?_ ?_
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_neg (by omega)]
        omega
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_neg (by omega)]
        omega
    · refine hv i ⟨by omega, by omega⟩ hia r c ?_ ?_
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_neg (by omega)]
        omega
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_neg (by omega)]
        omega

end GlobalTheory.CompanionTheory.Ar.PB.StepShape
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

section Homog

variable {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiHomog_rename_base {σ : Type} (blk : σ → Option K) {d' : NonPluckerBlocks blk → ℕ}
    {g : MRing (baseIdx ι blk)} (hg : IsMultiHomog g d') :
    open Classical in
    IsMultiHomog (rename (fun q : Σ k, baseIdx ι blk k => (⟨q.1.1, q.2⟩ : Σ k, ι k)) g)
      (fun k => if h : ∀ p, blk p ≠ some k then d' ⟨k, h⟩ else 0) := by
  classical
  have hinj : Function.Injective (fun q : Σ k, baseIdx ι blk k => (⟨q.1.1, q.2⟩ : Σ k, ι k)) := by
    rintro ⟨⟨k, hk⟩, a⟩ ⟨⟨k', hk'⟩, b⟩ h
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
    cases h
    rfl
  intro m hm k
  rw [support_rename_of_injective hinj, Finset.mem_image] at hm
  obtain ⟨m', hm', rfl⟩ := hm
  beta_reduce
  by_cases h : ∀ p, blk p ≠ some k
  · rw [dite_eq_left h, ← hg m' hm' ⟨k, h⟩]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finsupp.mapDomain_apply_of_injective hinj m' ⟨⟨k, h⟩, i⟩
  · rw [dite_eq_right h]
    refine Finset.sum_eq_zero fun i _ => Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨⟨⟨k', hk'⟩, b⟩, e⟩
    obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp e
    exact h hk'

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}

end Homog

section Minors

variable {N : ℕ}

theorem minorIJ_eq_det_of_card {R : Type} [CommRing R] (h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) {r : ℕ}
    (hI : I.card = r) (hJ : J.card = r) :
    minorIJ h I J = (h.submatrix (I.orderEmbOfFin hI) (J.orderEmbOfFin hJ)).det := by
  subst hJ
  unfold minorIJ
  rw [dite_eq_left hI]

theorem minorIJ_mul_sum {R : Type} [CommRing R] (T h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) :
    minorIJ (T * h) I J = ∑ I', minorIJ T I I' * minorIJ h I' J := by
  classical
  by_cases e : I.card = J.card
  · have hm : (T * h).submatrix (I.orderEmbOfFin e) (J.orderEmbOfFin rfl) =
        T.submatrix (I.orderEmbOfFin e) id * h.submatrix id (J.orderEmbOfFin rfl) := by
      ext a b
      simp [Matrix.mul_apply]
    have hsum : ∑ I', minorIJ T I I' * minorIJ h I' J =
        ∑ S : {S : Finset (Fin N) // S.card = J.card}, minorIJ T I S.1 * minorIJ h S.1 J := by
      rw [← Finset.sum_filter_of_ne (s := Finset.univ) (p := fun S : Finset (Fin N) => S.card = J.card)]
      · exact Finset.sum_subtype _ (by simp) _
      · intro S _ hS
        by_contra hc
        apply hS
        rw [show minorIJ h S J = 0 by unfold minorIJ; rw [dite_eq_right hc], mul_zero]
    rw [minorIJ_eq_det_of_card _ I J e rfl, hm, ReciprocityTheory.ChartRestriction.DS.cauchyBinet, hsum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [minorIJ_eq_det_of_card T I S.1 e S.2, minorIJ_eq_det_of_card h S.1 J S.2 rfl]
    rfl
  · have h0 : minorIJ (T * h) I J = 0 := by
      unfold minorIJ
      rw [dite_eq_right e]
    rw [h0]
    symm
    refine Finset.sum_eq_zero fun I' _ => ?_
    by_cases e' : I.card = I'.card
    · rw [show minorIJ h I' J = 0 by
        unfold minorIJ
        rw [dite_eq_right fun c => e (e'.trans c)], mul_zero]
    · rw [show minorIJ T I I' = 0 by unfold minorIJ; rw [dite_eq_right e'], zero_mul]

theorem minorIJ_block_zero {R : Type} [CommRing R] {j : ℕ} {i : Fin N} {h : Matrix (Fin N) (Fin N) R}
    (hh : IsBlockDiag j h) {I : Finset (Fin N)} (hnot : ¬ IsStepRows N j i I) :
    minorIJ h I (stepCols N j i) = 0 := by
  have hiN := i.isLt
  by_cases e : I.card = (stepCols N j i).card
  · have hsub : ¬ I ⊆ if (i : ℕ) + 1 ≤ j then wIdx N j else omIdx N j := fun hs => hnot ⟨e, hs⟩
    obtain ⟨a, haI, haB⟩ := Finset.not_subset.mp hsub
    have hr : a ∈ Set.range (I.orderEmbOfFin e) := by
      rw [Finset.range_orderEmbOfFin]
      exact haI
    obtain ⟨r, rfl⟩ := hr
    unfold minorIJ
    rw [dite_eq_left e]
    refine Matrix.det_eq_zero_of_row_eq_zero r fun c => ?_
    have hb := Finset.orderEmbOfFin_mem (stepCols N j i) rfl c
    refine hh _ _ ?_
    generalize (stepCols N j i).orderEmbOfFin rfl c = b at hb
    generalize I.orderEmbOfFin e r = a at haB
    by_cases hc : (i : ℕ) + 1 ≤ j
    · simp only [stepCols, wIdx, Finset.mem_filter, Finset.mem_univ, true_and, if_pos hc] at hb haB
      omega
    · simp only [stepCols, omIdx, Finset.mem_filter, Finset.mem_univ, true_and, if_neg hc] at hb haB
      omega
  · unfold minorIJ
    rw [dite_eq_right e]

end Minors

section Model

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ}

end Model

end GlobalTheory.CompanionTheory.Ar.PB
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem IsGenericFlag.indep_twist_mul_genUp : ∀ (Ω Φ : Type) [Field Ω] [Field Φ] [Algebra Ω Φ] (Ψ : Type) (N j : ℕ) (g : Ψ → Matrix (Fin N) (Fin N) Φ) (T : Ψ → Matrix (Fin N) (Fin N) Ω), (∀ τ, IsBlockDiag j (g τ)) → IsGenericFlag Ω j g → (∀ τ, IsBlockDiag j (T τ) ∧ (T τ).det ≠ 0) → AlgebraicIndependent Ω (fun q : inertBlockIndex Ψ N j => (((T q.1.1)⁻¹.map (algebraMap Ω (MvPolynomial (UpIdx Ψ N j) Φ))) * ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1)) q.1.2.1 q.1.2.2) := by
  intro Ω Φ _ _ _ Ψ N j g T hg hgen hT
  have hTu : ∀ τ, IsUnit (T τ).det := fun τ => isUnit_iff_ne_zero.mpr (hT τ).2
  have hM : ∀ τ, IsBlockDiag j ((g τ).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j τ) :=
    fun τ => IsBlockDiag.mul (IsBlockDiag.map (hg τ) (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ))
      (genUp_blockDiag (R := Φ) τ)
  have key : ∀ (R : Type) [CommRing R] [Algebra Ω R] (f : MvPolynomial (inertBlockIndex Ψ N j) Ω →ₐ[Ω] R)
      (Z : Ψ → Matrix (Fin N) (Fin N) R), (∀ τ, IsBlockDiag j (Z τ)) →
      (∀ q : inertBlockIndex Ψ N j, f (X q) = Z q.1.1 q.1.2.1 q.1.2.2) →
      ∀ τ c b, f (genericBlockMatrix Ω N j τ c b) = Z τ c b := by
    intro R _ _ f Z hZ hf τ c b
    exact congrFun (congrFun (generic_block_matrix_map f.toRingHom hZ hf τ) c) b
  have hlin : ∀ (R : Type) [CommRing R] [Algebra Ω R] (f : MvPolynomial (inertBlockIndex Ψ N j) Ω →ₐ[Ω] R)
      (U : Matrix (Fin N) (Fin N) Ω) (G : Matrix (Fin N) (Fin N) (MvPolynomial (inertBlockIndex Ψ N j) Ω)) (a b : Fin N),
      f ((U.map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω)) * G) a b)
        = (U.map (algebraMap Ω R) * G.map f) a b := by
    intro R _ _ f U G a b

    simp only [Matrix.mul_apply, map_sum, map_mul, Matrix.map_apply, AlgHom.commutes]
  obtain ⟨φ, hφ⟩ : ∃ φ : MvPolynomial (inertBlockIndex Ψ N j) Ω →ₐ[Ω] MvPolynomial (inertBlockIndex Ψ N j) Ω,
      ∀ q : inertBlockIndex Ψ N j, φ (X q) = ((T q.1.1)⁻¹.map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω))
        * genericBlockMatrix Ω N j q.1.1) q.1.2.1 q.1.2.2 :=
    ⟨MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j => ((T q.1.1)⁻¹.map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω))
        * genericBlockMatrix Ω N j q.1.1) q.1.2.1 q.1.2.2), fun q => MvPolynomial.aeval_X _ q⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : MvPolynomial (inertBlockIndex Ψ N j) Ω →ₐ[Ω] MvPolynomial (inertBlockIndex Ψ N j) Ω,
      ∀ q : inertBlockIndex Ψ N j, ψ (X q) = ((T q.1.1).map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω))
        * genericBlockMatrix Ω N j q.1.1) q.1.2.1 q.1.2.2 :=
    ⟨MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j => ((T q.1.1).map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω))
        * genericBlockMatrix Ω N j q.1.1) q.1.2.1 q.1.2.2), fun q => MvPolynomial.aeval_X _ q⟩
  have hZ : ∀ τ, IsBlockDiag j ((T τ).map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω)) * genericBlockMatrix Ω N j τ) :=
    fun τ => IsBlockDiag.mul (IsBlockDiag.map (hT τ).1 (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω)))
      (generic_block_matrix_isBlockDiag (R := Ω) τ)
  have hψg := key _ ψ _ hZ hψ
  have hGψ : ∀ τ, (genericBlockMatrix Ω N j τ).map ψ
      = (T τ).map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω)) * genericBlockMatrix Ω N j τ :=
    fun τ => Matrix.ext fun c b => by rw [Matrix.map_apply]; exact hψg τ c b
  have hcomp : ∀ p, ψ (φ p) = p := by
    have hc : ψ.comp φ = AlgHom.id Ω _ := by
      apply MvPolynomial.algHom_ext
      intro q
      rw [AlgHom.comp_apply, AlgHom.id_apply, hφ, hlin _ ψ, hGψ, ← Matrix.mul_assoc, ← Matrix.map_mul,
        Matrix.nonsing_inv_mul _ (hTu _),
        show ((1 : Matrix (Fin N) (Fin N) Ω).map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω))) = 1 from
          (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω)).mapMatrix.map_one,
        Matrix.one_mul, generic_block_matrix_apply]
    intro p
    exact DFunLike.congr_fun hc p
  have hx := IsGenericFlag.indep_mul_genUp hg hgen
  have hxg := key _ (MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j =>
      ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1) q.1.2.1 q.1.2.2)) _ hM
    (fun q => MvPolynomial.aeval_X _ q)
  have hGx : ∀ τ, (genericBlockMatrix Ω N j τ).map (MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j =>
      ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1) q.1.2.1 q.1.2.2))
      = (g τ).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j τ :=
    fun τ => Matrix.ext fun c b => by rw [Matrix.map_apply]; exact hxg τ c b
  have h1 : ∀ r, MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j => (((T q.1.1)⁻¹.map (algebraMap Ω (MvPolynomial (UpIdx Ψ N j) Φ)))
        * ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1)) q.1.2.1 q.1.2.2) r
      = MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j =>
        ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1) q.1.2.1 q.1.2.2) (φ r) := by
    have hc : (MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j => (((T q.1.1)⁻¹.map (algebraMap Ω (MvPolynomial (UpIdx Ψ N j) Φ)))
        * ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1)) q.1.2.1 q.1.2.2))
      = (MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j =>
        ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1) q.1.2.1 q.1.2.2)).comp φ := by
      apply MvPolynomial.algHom_ext
      intro q
      rw [AlgHom.comp_apply, MvPolynomial.aeval_X, hφ, hlin, hGx]
    intro r
    exact DFunLike.congr_fun hc r
  rw [algebraicIndependent_iff_injective_aeval] at hx ⊢
  intro p p' hpp
  have h2 : φ p = φ p' := hx (by rw [← h1, ← h1]; exact hpp)
  calc p = ψ (φ p) := (hcomp p).symm
    _ = ψ (φ p') := by rw [h2]
    _ = p' := hcomp p'

end GlobalTheory.CompanionTheory.Ar.PB
end
end

section

noncomputable section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.IwBlock

theorem exists_blocks_add {L : Type} [Field L] (V : ValuationSubring L) (n m : ℕ)
    (A : Matrix (Fin (n + m)) (Fin (n + m)) L)
    (hA : ∀ a b : Fin (n + m), ¬ ((a : ℕ) < n ↔ (b : ℕ) < n) → A a b = 0) (hd : A.det ≠ 0) :
    ∃ (K : Matrix (Fin (n + m)) (Fin (n + m)) V) (U : Matrix (Fin (n + m)) (Fin (n + m)) L),
      IsUnit K.det ∧ (∀ a b : Fin (n + m), ¬ ((a : ℕ) < n ↔ (b : ℕ) < n) → U a b = 0) ∧
      U.BlockTriangular id ∧ (∀ a, U a a ≠ 0) ∧ A = K.map (algebraMap V L) * U := by
  let e : Fin n ⊕ Fin m ≃ Fin (n + m) := finSumFinEquiv
  let A₁ : Matrix (Fin n) (Fin n) L := fun i k => A (e (Sum.inl i)) (e (Sum.inl k))
  let A₂ : Matrix (Fin m) (Fin m) L := fun i k => A (e (Sum.inr i)) (e (Sum.inr k))
  have lt_l : ∀ i : Fin n, ((e (Sum.inl i) : Fin (n + m)) : ℕ) < n := fun i => by simp [e]
  have ge_r : ∀ i : Fin m, ¬ ((e (Sum.inr i) : Fin (n + m)) : ℕ) < n := fun i => by simp [e]
  have val_l : ∀ i : Fin n, ((e (Sum.inl i) : Fin (n + m)) : ℕ) = i := fun i => by simp [e]
  have val_r : ∀ i : Fin m, ((e (Sum.inr i) : Fin (n + m)) : ℕ) = n + i := fun i => by simp [e]
  have hB : A.submatrix e e = fromBlocks A₁ 0 0 A₂ := by
    ext (i | i) (k | k)
    · rfl
    · exact hA _ _ fun h => ge_r k (h.1 (lt_l i))
    · exact hA _ _ fun h => ge_r i (h.2 (lt_l k))
    · rfl
  have hdet : A₁.det * A₂.det ≠ 0 := by
    rw [← det_fromBlocks_zero₂₁ A₁ 0 A₂, ← hB, det_submatrix_equiv_self]
    exact hd
  obtain ⟨k₁, U₁, hk₁, hU₁, hd₁, e₁⟩ := GlobalTheory.ValIwasawa.iwasawa_matrix (V := V) A₁ (left_ne_zero_of_mul hdet)
  obtain ⟨k₂, U₂, hk₂, hU₂, hd₂, e₂⟩ := GlobalTheory.ValIwasawa.iwasawa_matrix (V := V) A₂ (right_ne_zero_of_mul hdet)
  refine ⟨(fromBlocks k₁ 0 0 k₂).submatrix e.symm e.symm, (fromBlocks U₁ 0 0 U₂).submatrix e.symm e.symm,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [det_submatrix_equiv_self, det_fromBlocks_zero₂₁]
    exact hk₁.mul hk₂
  · intro a b h
    obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    rcases x with i | i <;> rcases y with k | k
    · exact absurd (iff_of_true (lt_l i) (lt_l k)) h
    · simp
    · simp
    · exact absurd (iff_of_false (ge_r i) (ge_r k)) h
  · intro a b h
    obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    have h' : ((e y : Fin (n + m)) : ℕ) < (e x : Fin (n + m)) := h
    rcases x with i | i <;> rcases y with k | k
    · rw [val_l, val_l] at h'
      simpa using hU₁ (show k < i from h')
    · simp
    · simp
    · rw [val_r, val_r] at h'
      simpa using hU₂ (show k < i from Nat.lt_of_add_lt_add_left h')
  · intro a
    obtain ⟨x, rfl⟩ := e.surjective a
    rcases x with i | i
    · simpa using hd₁ i
    · simpa using hd₂ i
  · have h1 : A = (fromBlocks A₁ 0 0 A₂).submatrix e.symm e.symm := by
      rw [← hB]; ext a b; simp
    have h3 : fromBlocks A₁ 0 0 A₂ =
        (fromBlocks k₁ 0 0 k₂).map (algebraMap V L) * fromBlocks U₁ 0 0 U₂ := by
      rw [fromBlocks_map, fromBlocks_multiply, ← e₁, ← e₂,
        Matrix.map_zero _ (map_zero (algebraMap V L)), Matrix.map_zero _ (map_zero (algebraMap V L))]
      simp
    rw [h1, h3, ← submatrix_mul_equiv _ _ _ e.symm _]
    rfl

theorem exists_blocks {L : Type} [Field L] (V : ValuationSubring L) (N n : ℕ) (hn : n ≤ N)
    (A : Matrix (Fin N) (Fin N) L)
    (hA : ∀ a b : Fin N, ¬ ((a : ℕ) < n ↔ (b : ℕ) < n) → A a b = 0) (hd : A.det ≠ 0) :
    ∃ (K : Matrix (Fin N) (Fin N) V) (U : Matrix (Fin N) (Fin N) L),
      IsUnit K.det ∧ (∀ a b : Fin N, ¬ ((a : ℕ) < n ↔ (b : ℕ) < n) → U a b = 0) ∧
      U.BlockTriangular id ∧ (∀ a, U a a ≠ 0) ∧ A = K.map (algebraMap V L) * U := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact exists_blocks_add V n m A hA hd

theorem inv_diag_ne_zero {L : Type} [Field L] {N : ℕ} {U : Matrix (Fin N) (Fin N) L}
    (hU : U.BlockTriangular id) (hd : IsUnit U.det) (a : Fin N) : U⁻¹ a a ≠ 0 := by
  have hI : U⁻¹.BlockTriangular id := by
    letI := Matrix.invertibleOfIsUnitDet U hd
    exact blockTriangular_inv_of_blockTriangular hU
  intro e
  have h := congrFun (congrFun (nonsing_inv_mul U hd) a) a
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single a (fun c _ hc => ?_) (by simp), e,
    zero_mul] at h
  · exact zero_ne_one h
  · rcases lt_or_gt_of_ne hc with l | l
    · rw [hI l, zero_mul]
    · rw [hU l, mul_zero]

theorem main : ∀ (L : Type) [Field L] (V : ValuationSubring L) (N j : ℕ) (A : Matrix (Fin N) (Fin N) L), IsBlockDiag j A → A.det ≠ 0 → ∃ b : Matrix (Fin N) (Fin N) L, IsBlockDiag j b ∧ b.BlockTriangular id ∧ (∀ a, b a a ≠ 0) ∧ (∀ a c, (A * b) a c ∈ V) ∧ (A * b).det ≠ 0 ∧ ((A * b).det)⁻¹ ∈ V := by
  intro L _ V N j A hA hd
  obtain ⟨K, U, hK, hUb, hUt, hUd, hAe⟩ := exists_blocks V N (N - j) (Nat.sub_le N j) A hA hd
  have hUdet : IsUnit U.det := by
    rw [det_of_upperTriangular hUt]
    exact (Finset.prod_ne_zero_iff.2 fun a _ => hUd a).isUnit
  have hAU : A * U⁻¹ = K.map (algebraMap V L) := by
    rw [hAe, Matrix.mul_nonsing_inv_cancel_right _ _ hUdet]
  have hKdet : (K.map (algebraMap V L)).det = algebraMap V L K.det := (RingHom.map_det _ K).symm
  have hUb' : IsBlockDiag j U := hUb
  refine ⟨U⁻¹, hUb'.inv hUdet, ?_, inv_diag_ne_zero hUt hUdet, fun a c => ?_, ?_, ?_⟩
  · letI := Matrix.invertibleOfIsUnitDet U hUdet
    exact blockTriangular_inv_of_blockTriangular hUt
  · rw [hAU]
    exact (K a c).2
  · rw [hAU, hKdet]
    exact (hK.map (algebraMap V L)).ne_zero
  · rw [hAU, hKdet]
    obtain ⟨u, hu⟩ := hK
    rw [← hu]
    have e : (algebraMap V L (u : V))⁻¹ = algebraMap V L ((u⁻¹ : Vˣ) : V) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← map_mul, Units.mul_inv, map_one]
    rw [e]
    exact ((u⁻¹ : Vˣ) : V).2

end GlobalTheory.CompanionTheory.Ar.PB.IwBlock
end
end
