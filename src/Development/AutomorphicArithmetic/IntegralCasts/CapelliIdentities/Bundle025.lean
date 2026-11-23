module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Algebra.Module.PID
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Analysis.Normed.Group.Ultra
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Algebra.Polynomial.Module.AEval
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section

section

open MeasureTheory in
private theorem UpperTheory.Reformulated.B.Qh3.one_side {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (ν : Measure Ω) (X : Ω → ι → ℝ) (f : Ω → ℝ) (hX : Measurable X) (hf : Integrable f ν)
    (G : (ι → ℝ) → ℂ) (hG : Measurable G) :
    ∫ x, G x ∂Measure.map X (ν.withDensity fun ω ↦ ENNReal.ofReal (f ω)) =
      ∫ ω, G (X ω) * ((max (f ω) 0 : ℝ) : ℂ) ∂ν := by
  rw [integral_map hX.aemeasurable hG.aestronglyMeasurable]
  have h : AEMeasurable (fun ω ↦ (f ω).toNNReal) ν := hf.aemeasurable.real_toNNReal
  have h2 := integral_withDensity_eq_integral_smul₀ h (fun ω ↦ G (X ω))
  refine Eq.trans h2 ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal', Complex.real_smul, mul_comm]

open MeasureTheory in
private theorem UpperTheory.Reformulated.B.Qh3.int_mul {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (ν : Measure Ω) (X : Ω → ι → ℝ) (f : Ω → ℝ) (hX : Measurable X) (hf : Integrable f ν)
    (G : (ι → ℝ) → ℂ) (hG : Measurable G) (hb : ∀ x, ‖G x‖ ≤ (1 : ℝ)) :
    Integrable (fun ω ↦ G (X ω) * ((max (f ω) 0 : ℝ) : ℂ)) ν := by
  have h1 : Integrable (fun ω ↦ ((max (f ω) 0 : ℝ) : ℂ)) ν := hf.pos_part.ofReal
  exact h1.bdd_mul (c := 1) (hG.comp hX).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω ↦ hb _)

theorem UpperTheory.Reformulated.B.Qh3.real_diff :
    ∀ {Ω ι : Type} [inst : MeasurableSpace Ω] [Fintype ι]
    (ν : MeasureTheory.Measure Ω) (X : Ω → ι → ℝ) (f : Ω → ℝ),
    Measurable X →
      MeasureTheory.Integrable f ν →
        ∀ (G : (ι → ℝ) → ℂ),
          Measurable G →
            (∀ (x : ι → ℝ), ‖G x‖ ≤ (1 : ℝ)) →
              ∫ (x : ι → ℝ), G x ∂MeasureTheory.Measure.map X (ν.withDensity fun (ω : Ω) ↦ ENNReal.ofReal (f ω)) -
                  ∫ (x : ι → ℝ), G x ∂MeasureTheory.Measure.map X (ν.withDensity fun (ω : Ω) ↦ ENNReal.ofReal (-f ω)) =
                ∫ (ω : Ω), G (X ω) * (↑(f ω) : ℂ) ∂ν := by
  intro Ω ι _ _ ν X f hX hf G hG hb
  have hn : MeasureTheory.Integrable (fun ω ↦ -f ω) ν := hf.neg
  rw [UpperTheory.Reformulated.B.Qh3.one_side ν X f hX hf G hG,
    UpperTheory.Reformulated.B.Qh3.one_side ν X (fun ω ↦ -f ω) hX hn G hG,
    ← MeasureTheory.integral_sub (UpperTheory.Reformulated.B.Qh3.int_mul ν X f hX hf G hG hb)
      (UpperTheory.Reformulated.B.Qh3.int_mul ν X (fun ω ↦ -f ω) hX hn G hG hb)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
  have h : max (f ω) 0 - max (-f ω) 0 = f ω := max_zero_sub_max_neg_zero_eq_self (f ω)
  simp only
  rw [← mul_sub, ← Complex.ofReal_sub, h]
end

section

theorem UpperTheory.Reformulated.B.TriangularFactorizationNearIdentity.factor :
    ∀ {L : Type} [inst : NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ),
      (0 : ℝ) ≤ r →
        r < (1 : ℝ) →
          ∀ (A : Matrix (Fin n) (Fin n) L),
            (∀ (i j : Fin n), ‖(A - (1 : Matrix (Fin n) (Fin n) L)) i j‖ ≤ r) →
              ∃ (U : Matrix (Fin n) (Fin n) L) (W : Matrix (Fin n) (Fin n) L),
                (∀ (i j : Fin n), j < i → U i j = (0 : L)) ∧
                  (∀ (i j : Fin n), i < j → W i j = (0 : L)) ∧
                    (∀ (i j : Fin n), ‖(U - (1 : Matrix (Fin n) (Fin n) L)) i j‖ ≤ r) ∧
                      (∀ (i j : Fin n), ‖(W - (1 : Matrix (Fin n) (Fin n) L)) i j‖ ≤ r) ∧ A = U * W := by
  intro L _ _ n r h0 h1
  induction n with
  | zero =>
    intro A _
    exact ⟨1, 1, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      Subsingleton.elim _ _⟩
  | succ n ih =>
    intro A hA
    have hlc : ∀ i : Fin n, Fin.last n ≠ i.castSucc := fun i => (Fin.castSucc_lt_last i).ne'
    have hcl : ∀ i : Fin n, i.castSucc ≠ Fin.last n := fun i => (Fin.castSucc_lt_last i).ne
    have hd1 : ‖A (Fin.last n) (Fin.last n) - 1‖ ≤ r := by
      simpa using hA (Fin.last n) (Fin.last n)
    have hd : ‖A (Fin.last n) (Fin.last n)‖ = 1 := by
      have hne : ‖A (Fin.last n) (Fin.last n) - 1‖ ≠ ‖(1 : L)‖ := by
        rw [norm_one]; exact (hd1.trans_lt h1).ne
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
      rw [sub_add_cancel, norm_one] at this
      rw [this]
      exact max_eq_right (hd1.trans h1.le)
    have hd0 : A (Fin.last n) (Fin.last n) ≠ 0 := by
      intro h; rw [h, norm_zero] at hd; exact zero_ne_one hd
    have hb : ∀ i : Fin n, ‖A i.castSucc (Fin.last n)‖ ≤ r := fun i => by
      simpa [Matrix.one_apply_ne (hcl i)] using hA i.castSucc (Fin.last n)
    have hc : ∀ i : Fin n, ‖A (Fin.last n) i.castSucc‖ ≤ r := fun i => by
      simpa [Matrix.one_apply_ne (hlc i)] using hA (Fin.last n) i.castSucc
    have hu : ∀ i : Fin n, ‖A i.castSucc (Fin.last n) / A (Fin.last n) (Fin.last n)‖ ≤ r :=
      fun i => by rw [norm_div, hd, div_one]; exact hb i
    have hone : ∀ i j : Fin n, (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) L) i.castSucc j.castSucc
        = (1 : Matrix (Fin n) (Fin n) L) i j := fun i j => by
      simp [Matrix.one_apply]
    obtain ⟨U, W, hU, hW, hU1, hW1, hUW⟩ := ih
      (Matrix.of fun i j : Fin n => A i.castSucc j.castSucc -
        A i.castSucc (Fin.last n) / A (Fin.last n) (Fin.last n) * A (Fin.last n) j.castSucc)
      (fun i j => by
        have h2 := hA i.castSucc j.castSucc
        rw [Matrix.sub_apply, hone] at h2
        rw [Matrix.sub_apply, Matrix.of_apply, sub_right_comm, sub_eq_add_neg]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 ?_)
        rw [norm_neg, norm_mul]
        calc _ ≤ r * 1 := mul_le_mul (hu i) ((hc j).trans h1.le) (norm_nonneg _) h0
          _ = r := mul_one r)
    refine ⟨Matrix.of fun i j => Fin.lastCases (motive := fun _ => L)
        (Fin.lastCases (motive := fun _ => L) 1 (fun _ => 0) j)
        (fun i' => Fin.lastCases (motive := fun _ => L)
          (A i'.castSucc (Fin.last n) / A (Fin.last n) (Fin.last n)) (fun j' => U i' j') j) i,
      Matrix.of fun i j => Fin.lastCases (motive := fun _ => L)
        (A (Fin.last n) j)
        (fun i' => Fin.lastCases (motive := fun _ => L) 0 (fun j' => W i' j') j) i,
      ?_, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · exact absurd hij (lt_irrefl _)
      · simp
      · exact absurd hij (Fin.le_last _).not_gt
      · simpa using hU _ _ (by simpa using hij)
    · intro i j hij
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · exact absurd hij (lt_irrefl _)
      · exact absurd hij (Fin.le_last _).not_gt
      · simp
      · simpa using hW _ _ (by simpa using hij)
    · intro i j
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · simpa using h0
      · simpa [Matrix.one_apply_ne (hlc _)] using h0
      · simpa [Matrix.one_apply_ne (hcl _), hd] using hb _
      · rw [Matrix.sub_apply, hone]
        simpa using hU1 _ _
    · intro i j
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · simpa using hd1
      · simpa [Matrix.one_apply_ne (hlc _)] using hc _
      · simpa [Matrix.one_apply_ne (hcl _)] using h0
      · rw [Matrix.sub_apply, hone]
        simpa using hW1 _ _
    · ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · simp
      · simp
      · simp [hd0]
      · rename_i i j
        have := congrFun (congrFun hUW i) j
        rw [Matrix.of_apply, Matrix.mul_apply] at this
        simp only [Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last]
        rw [← this, sub_add_cancel]
end

section

private def unitBallSubring (K : Type) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simpa using ha

theorem UpperTheory.Reformulated.B.Qh18.rootb :
    ∀ {K : Type} [inst : NormedField K] [IsUltrametricDist K] (l m : ℕ),
    Nat.Prime l → l ≠ (2 : ℕ) → ∀ (z : K), z ^ l ^ m = (1 : K) → ‖z - (1 : K)‖ ^ l ^ m ≤ ‖(↑l : K)‖ := by
  intro K _ _ l m hl _ z hz
  have hN : l ^ m ≠ 0 := pow_ne_zero _ hl.ne_zero
  have hz1 : ‖z‖ = 1 := by
    have h := congrArg norm hz
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN).1 h
  have hzS : z ∈ unitBallSubring K := hz1.le
  have hx : z - 1 ∈ unitBallSubring K := sub_mem hzS (one_mem _)
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hl (⟨z - 1, hx⟩ : unitBallSubring K) 1 m
  have hr' := congrArg (Subtype.val) hr
  push_cast at hr'
  have hrn : ‖(r : K)‖ ≤ 1 := r.2
  have hxn : ‖z - 1‖ ≤ 1 := hx
  rw [sub_add_cancel, hz] at hr'
  have e : (z - 1) ^ l ^ m = -((l : K) * ((z - 1) * (r : K))) := by
    simp only [one_pow, mul_one] at hr'
    linear_combination (-1 : K) * hr'
  rw [← norm_pow, e, norm_neg, norm_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (mul_le_one₀ hxn (norm_nonneg _) hrn)
end

section

noncomputable def UpperTheory.Reformulated.B.ProjectiveLineOf.P1 :
    Prop :=
    ∀ (k : Type) [inst : NontriviallyNormedField k] [LocallyCompactSpace k] [CharZero k] (n : ℕ) (γ : GL (Fin n) k),
      (↑γ : Matrix (Fin n) (Fin n) k).charpoly.Separable →
        ∀ (D : Set (GL (Fin n) k)),
          IsCompact D →
            ∃ (C : Set (GL (Fin n) k)),
              IsCompact C ∧ ∀ (x : GL (Fin n) k), x⁻¹ * γ * x ∈ D → ∃ (t : GL (Fin n) k), t * γ = γ * t ∧ ∃ y ∈ C, x = t * y

section

open Polynomial Matrix

private theorem charpoly_dvd_of_aeval {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k)
    (hA : A.charpoly.Separable) (p : k[X]) (hp : aeval A p = 0) : A.charpoly ∣ p := by
  by_cases hp0 : p = 0
  · simp [hp0]
  let K := AlgebraicClosure k
  let f := algebraMap k K
  rw [← Polynomial.map_dvd_map' f]
  have hsep : (A.charpoly.map f).Separable := hA.map
  refine (IsAlgClosed.splits _).dvd_of_roots_le_roots hsep.ne_zero ?_
  rw [Multiset.le_iff_subset (nodup_roots hsep)]
  intro r hr
  have hr' : (A.map f).charpoly.IsRoot r := by
    rw [Matrix.charpoly_map]; exact isRoot_of_mem_roots hr
  rw [← Matrix.mem_spectrum_iff_isRoot_charpoly] at hr'
  have h1 := spectrum.subset_polynomial_aeval (A.map f) (p.map f) ⟨r, hr', rfl⟩
  have h2 : aeval (A.map f) (p.map f) = 0 := by
    have h3 : aeval ((Algebra.ofId k K).mapMatrix A) p = 0 := by
      rw [aeval_algHom_apply, hp, map_zero]
    rw [aeval_map_algebraMap]
    exact h3
  rw [mem_roots (Polynomial.map_ne_zero hp0)]
  by_contra hne
  rw [h2, spectrum.mem_iff, sub_zero] at h1
  exact h1 ((IsUnit.mk0 _ hne).map _)

private def krylov {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k) (v : Fin n → k) :
    Matrix (Fin n) (Fin n) k :=
  Matrix.of fun i j => ((A ^ (j : ℕ)) *ᵥ v) i

private theorem krylov_mulVec {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k)
    (v : Fin n → k) (p : k[X]) (hp : p.degree < n) :
    krylov A v *ᵥ (fun j => p.coeff j) = aeval A p *ᵥ v := by
  have h : aeval A p = ∑ j : Fin n, p.coeff j • A ^ (j : ℕ) := by
    conv_lhs => rw [← p.sum_C_mul_X_pow_eq, ← Polynomial.sum_fin _ (by simp) hp]
    simp [Algebra.smul_def]
  rw [h, Matrix.sum_mulVec]
  ext i
  simp [krylov, Matrix.mulVec, dotProduct, Finset.sum_apply, Finset.mul_sum, mul_comm, mul_left_comm,
    mul_assoc]

private theorem exists_krylov_det_ne_zero {k : Type} [Field k] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) k) (hA : A.charpoly.Separable) :
    ∃ v, (krylov A v).det ≠ 0 := by
  obtain ⟨x, hx⟩ := Module.exists_ker_toSpanSingleton_eq_annihilator k[X]
    (Module.AEval' (Matrix.toLin' A))
  obtain ⟨v, rfl⟩ := (Module.AEval'.of _).surjective x
  refine ⟨v, fun hdet => ?_⟩
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let p : k[X] := (degreeLTEquiv k n).symm c
  have hpdeg : p.degree < n := mem_degreeLT.mp ((degreeLTEquiv k n).symm c).2
  have hpc : (fun j : Fin n => p.coeff j) = c := (degreeLTEquiv k n).apply_symm_apply c
  have hlin : aeval (Matrix.toLin' A) p = Matrix.toLin' (aeval A p) :=
    aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)) A p
  have h1 : aeval A p *ᵥ v = 0 := by rw [← krylov_mulVec A v p hpdeg, hpc, hc]
  have h2 : p ∈ Module.annihilator k[X] (Module.AEval' (Matrix.toLin' A)) := by
    rw [← hx, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply,
      ← Module.AEval.of_aeval_smul, Module.End.smul_def, hlin, Matrix.toLin'_apply, h1, map_zero]
  rw [Module.AEval.annihilator_eq_ker_aeval, RingHom.mem_ker, hlin, map_eq_zero_iff _ Matrix.toLin'.injective] at h2
  have h3 := charpoly_dvd_of_aeval A hA p h2
  have h4 : p = 0 := by
    refine eq_zero_of_dvd_of_degree_lt h3 ?_
    simpa [Matrix.charpoly_degree_eq_dim] using hpdeg
  apply hc0
  rw [← hpc, h4]
  rfl

private theorem mul_krylov {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k)
    (v : Fin n → k) :
    A * krylov A v = krylov A v *
      Matrix.of fun i j : Fin n => (X ^ ((j : ℕ) + 1) %ₘ A.charpoly).coeff i := by
  ext i j
  have hdeg : (X ^ ((j : ℕ) + 1) %ₘ A.charpoly).degree < n := by
    simpa [Matrix.charpoly_degree_eq_dim] using
      degree_modByMonic_lt (X ^ ((j : ℕ) + 1)) A.charpoly_monic
  have h := congrFun (krylov_mulVec A v _ hdeg) i
  rw [← Matrix.pow_eq_aeval_mod_charpoly, pow_succ' A, ← Matrix.mulVec_mulVec] at h
  exact h.symm

private theorem continuous_krylov {k : Type} [NontriviallyNormedField k] {n : ℕ} (v : Fin n → k) :
    Continuous fun δ : GL (Fin n) k => krylov (δ : Matrix (Fin n) (Fin n) k) v := by
  refine continuous_matrix fun i j => ?_
  exact (continuous_apply i).comp ((Units.continuous_val.pow _).matrix_mulVec continuous_const)

private theorem exists_compact_krylov {k : Type} [NontriviallyNormedField k] {n : ℕ}
    (v : Fin n → k) (S : Set (GL (Fin n) k)) (hS : IsCompact S)
    (h : ∀ δ ∈ S, (krylov (δ : Matrix (Fin n) (Fin n) k) v).det ≠ 0) :
    ∃ C : Set (GL (Fin n) k), IsCompact C ∧
      ∀ δ ∈ S, ∃ u ∈ C, (u : Matrix (Fin n) (Fin n) k) = krylov (δ : Matrix (Fin n) (Fin n) k) v := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let Φ : S → GL (Fin n) k := fun δ => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (h δ.1 δ.2)
  have hval : ∀ δ : S, (Φ δ : Matrix (Fin n) (Fin n) k) =
      krylov (δ.1 : Matrix (Fin n) (Fin n) k) v := fun δ => rfl
  have hc : Continuous fun δ : S => krylov (δ.1 : Matrix (Fin n) (Fin n) k) v :=
    (continuous_krylov v).comp continuous_subtype_val
  have hΦ : Continuous Φ := by
    rw [Units.continuous_iff]
    refine ⟨hc, ?_⟩
    simp_rw [Matrix.coe_units_inv, hval, Matrix.inv_def, Ring.inverse_eq_inv']
    exact (hc.matrix_det.inv₀ fun δ => h δ.1 δ.2).smul hc.matrix_adjugate
  exact ⟨Set.range Φ, isCompact_range hΦ, fun δ hδ => ⟨Φ ⟨δ, hδ⟩, ⟨_, rfl⟩, rfl⟩⟩

private theorem isClosed_charpoly_eq {k : Type} [NontriviallyNormedField k] [CharZero k] {n : ℕ}
    (χ : k[X]) :
    IsClosed {δ : GL (Fin n) k | (δ : Matrix (Fin n) (Fin n) k).charpoly = χ} := by
  have h : {δ : GL (Fin n) k | (δ : Matrix (Fin n) (Fin n) k).charpoly = χ} =
      ⋂ r : k, {δ : GL (Fin n) k |
        (Matrix.scalar (Fin n) r - (δ : Matrix (Fin n) (Fin n) k)).det = χ.eval r} := by
    ext δ
    simp only [Set.mem_setOf_eq, Set.mem_iInter, ← Matrix.eval_charpoly]
    exact ⟨fun h r => by rw [h], Polynomial.funext⟩
  rw [h]
  exact isClosed_iInter fun r =>
    isClosed_eq (continuous_const.sub Units.continuous_val).matrix_det continuous_const

end

theorem UpperTheory.Reformulated.B.ProjectiveLineOf.p1_holds :
    UpperTheory.Reformulated.B.ProjectiveLineOf.P1 := by
  intro k _ _ _ n γ hγ D hD
  classical
  set χ := (γ : Matrix (Fin n) (Fin n) k).charpoly with hχ
  have hD' := hD.inter_right (isClosed_charpoly_eq (n := n) χ)
  let U : (Fin n → k) → Set (GL (Fin n) k) := fun v =>
    {δ | (krylov (δ : Matrix (Fin n) (Fin n) k) v).det ≠ 0}
  have hU : ∀ v, IsOpen (U v) := fun v =>
    isOpen_ne_fun (continuous_krylov v).matrix_det continuous_const
  obtain ⟨s, hs⟩ := hD'.elim_finite_subcover U hU (by
    rintro δ ⟨-, hδ⟩
    exact Set.mem_iUnion.mpr (exists_krylov_det_ne_zero _ (by rw [hδ]; exact hγ)))
  obtain ⟨S, hSc, hSU, hS⟩ := hD'.finite_compact_cover s U (fun v _ => hU v) hs
  choose C hCc hC using fun v => exists_compact_krylov v (S v) (hSc v) (hSU v)
  obtain ⟨v₀, hv₀⟩ := exists_krylov_det_ne_zero _ hγ
  let u₀ : GL (Fin n) k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hv₀
  have hu₀ : (u₀ : Matrix (Fin n) (Fin n) k) = krylov (γ : Matrix (Fin n) (Fin n) k) v₀ := rfl
  refine ⟨⋃ v ∈ s, (fun u => u₀ * u⁻¹) '' C v,
    s.isCompact_biUnion fun v _ => (hCc v).image (by fun_prop), fun x hx => ?_⟩
  have hch : ((x⁻¹ * γ * x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly = χ := by
    rw [Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, mul_inv_cancel_left]
  have hmem : x⁻¹ * γ * x ∈ ⋃ v ∈ s, S v := hS ▸ ⟨hx, hch⟩
  obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp hmem
  obtain ⟨u, huC, hu⟩ := hC v _ hxv
  have h1 := mul_krylov ((x⁻¹ * γ * x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) v
  have h2 := mul_krylov (γ : Matrix (Fin n) (Fin n) k) v₀
  rw [← hu, hch] at h1
  rw [← hu₀, ← hχ] at h2
  have h3 : u⁻¹ * (x⁻¹ * γ * x) * u = u₀⁻¹ * γ * u₀ := by
    apply Units.ext
    rw [mul_assoc, mul_assoc u₀⁻¹, Units.val_mul, Units.val_mul, h1, Units.val_mul,
      Units.val_mul, h2, Units.inv_mul_cancel_left, Units.inv_mul_cancel_left]
  refine ⟨x * u * u₀⁻¹, ?_, u₀ * u⁻¹, Set.mem_iUnion₂.mpr ⟨v, hv, u, huC, rfl⟩, by group⟩
  calc x * u * u₀⁻¹ * γ = x * u * (u₀⁻¹ * γ * u₀) * u₀⁻¹ := by group
    _ = γ * (x * u * u₀⁻¹) := by rw [← h3]; group
end

section

theorem UpperTheory.Reformulated.B.Qi6.det_ne_zero :
    ∀ {F : Type} [inst : NormedField F] [IsUltrametricDist F] {m : ℕ}
    (t : F),
    ‖t‖ = (1 : ℝ) →
      ∀ (E : Matrix (Fin m) (Fin m) F),
        (∀ (a b : Fin m), ‖E a b‖ < (1 : ℝ)) → (t • (1 : Matrix (Fin m) (Fin m) F) + E).det ≠ (0 : F) := by
  intro F _ _ m t ht E hE hdet
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  haveI : Nonempty (Fin m) := ⟨i⟩
  obtain ⟨a, ha⟩ := Finite.exists_max (fun j => ‖v j‖)
  have hpos : 0 < ‖v a‖ := lt_of_lt_of_le (norm_pos_iff.mpr hi) (ha i)
  have hrow : t * v a = -∑ b, E a b * v b := by
    have h := congrFun hMv a
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h
    exact eq_neg_of_add_eq_zero_left h
  obtain ⟨b, -, hb⟩ := IsUltrametricDist.exists_norm_finsetSum_le (Finset.univ : Finset (Fin m))
    (fun b => E a b * v b)
  have h1 : ‖v a‖ = ‖∑ b, E a b * v b‖ := by
    rw [← norm_neg (∑ b, E a b * v b), ← hrow, norm_mul, ht, one_mul]
  have h2 : ‖E a b * v b‖ < ‖v a‖ := by
    rw [norm_mul]
    calc ‖E a b‖ * ‖v b‖ ≤ ‖E a b‖ * ‖v a‖ :=
          mul_le_mul_of_nonneg_left (ha b) (norm_nonneg _)
      _ < 1 * ‖v a‖ := mul_lt_mul_of_pos_right (hE a b) hpos
      _ = ‖v a‖ := one_mul _
  exact absurd (h1.le.trans hb) (not_le.mpr h2)
end

section

noncomputable def UpperTheory.Reformulated.B.BallSubgroup.ball :
    (L : Type) → [inst : NontriviallyNormedField L] → [IsUltrametricDist L] → ValuationSubring L :=
  fun L _ _ =>
    { carrier := {x : L | ‖x‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [norm_mul]
        exact mul_le_one₀ ha (norm_nonneg b) hb
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rwa [norm_neg]
      mem_or_inv_mem' := fun x => by
        simp only [Set.mem_setOf_eq]
        rcases le_total ‖x‖ 1 with h | h
        · exact Or.inl h
        · right
          rw [norm_inv]
          exact inv_le_one_of_one_le₀ h }
end
