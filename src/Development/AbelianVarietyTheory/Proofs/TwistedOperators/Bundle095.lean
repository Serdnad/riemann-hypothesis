module

public import Formalism.LocalRingCardinality.DataTheta
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

section

noncomputable section
namespace GlobalTheory.FockDegree
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

theorem inner_eq_zero_of_deriv {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : ℝ → H →L[ℂ] H) (hn : ∀ t x, ‖U t x‖ = ‖x‖) (hinv : ∀ t x, U t (U (-t) x) = x)
    (K : H →L[ℂ] H) (hK : ∀ t x, K (U t x) = U t (K x)) (x v : H) (a b : ℝ) (hab : a ≠ b)
    (hx : HasDerivAt (fun t : ℝ => U t x) ((Complex.I * a) • x) 0)
    (hv : HasDerivAt (fun t : ℝ => U t v) ((Complex.I * b) • v) 0) :
    inner ℂ x (K v) = 0 := by
  have hU : ∀ t y z, inner ℂ (U t y) (U t z) = inner ℂ y z := fun t y z =>
    LinearIsometry.inner_map_map (⟨(U t).toLinearMap, hn t⟩ : H →ₗᵢ[ℂ] H) y z
  have h1 : HasDerivAt (fun t : ℝ => K (U t v)) (K ((Complex.I * b) • v)) 0 :=
    (K.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hv
  have h2 := HasDerivAt.inner ℂ (hasDerivAt_const (0 : ℝ) x) h1
  have h3 : HasDerivAt (fun t : ℝ => U (-t) x) ((-1 : ℝ) • ((Complex.I * a) • x)) 0 := by
    have hx' : HasDerivAt (fun t : ℝ => U t x) ((Complex.I * a) • x) (-0) := by
      rw [neg_zero]; exact hx
    exact hx'.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
  have h4 := HasDerivAt.inner ℂ h3 (hasDerivAt_const (0 : ℝ) (K v))
  have heq : (fun t : ℝ => inner ℂ x (K (U t v))) = fun t : ℝ => inner ℂ (U (-t) x) (K v) := by
    funext t
    rw [hK, ← hU t (U (-t) x) (K v), hinv]
  rw [heq] at h2
  have h5 := h2.unique h4
  simp only [map_smul, inner_smul_right, inner_zero_left, inner_zero_right, add_zero, zero_add,
    neg_smul, one_smul, inner_neg_left, inner_smul_left, map_mul, Complex.conj_I,
    Complex.conj_ofReal] at h5
  have h6 : (Complex.I * ((b : ℂ) - a)) * inner ℂ x (K v) = 0 := by
    linear_combination h5
  rcases mul_eq_zero.1 h6 with h | h
  · exfalso
    rcases mul_eq_zero.1 h with h | h
    · exact Complex.I_ne_zero h
    · exact hab (by exact_mod_cast (sub_eq_zero.1 h).symm)
  · exact h

theorem Jm_eq_diagonal (p q : ℕ) :
    Jm p q = Matrix.diagonal (fun a => if a.isLeft then (1 : ℂ) else -1) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem smul_I_Jm_mem (p q : ℕ) (t : ℝ) : t • (Complex.I • Jm p q) ∈ upq p q := by
  have h : (Jm p q).conjTranspose = Jm p q := by
    rw [Jm_eq_diagonal, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    by_cases ha : a.isLeft <;> simp [ha]
  simp [upq, Matrix.conjTranspose_smul, h]

theorem I_Jm_mem (p q : ℕ) : Complex.I • Jm p q ∈ upq p q := by
  simpa using smul_I_Jm_mem p q 1

theorem commute_Jm_of_isKC {p q : ℕ} (X : Mat p q) (hX : IsKC X) : Commute X (Jm p q) := by
  rw [Jm_eq_diagonal]
  show X * _ = _ * X
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases a with a | a <;> rcases b with b | b
  · simp
  · rw [hX _ _ (by simp [sameBlock])]; simp
  · rw [hX _ _ (by simp [sameBlock])]; simp
  · simp

theorem commute_expt {p q : ℕ} (T : GrpData p q) (k : T.G) (hk : k ∈ T.Kset) (t : ℝ) :
    k * T.expt (t • (Complex.I • Jm p q)) = T.expt (t • (Complex.I • Jm p q)) * k := by
  apply T.emb.injective
  simp only [map_mul, Prod.mk.injEq]
  refine ⟨?_, mul_comm _ _⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, T.expt_cov _ (smul_I_Jm_mem p q t)]
  exact (((commute_Jm_of_isKC _ hk).smul_right Complex.I).smul_right t).exp_right.eq

theorem omAct_I_Jm_monomial (p q r s : ℕ) (α : Ln p q r s →₀ ℕ) :
    omAct p q r s (Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm
      (Complex.I • Jm _ _)) (MvPolynomial.monomial α 1) =
    (Complex.I * ((α.degree : ℝ) + (Fintype.card (Ln p q r s) : ℝ) / 2 : ℝ)) •
      MvPolynomial.monomial α 1 := by
  rw [omAct_apply, LinearMap.sum_apply]
  have : ∀ l : Ln p q r s, (∑ l', (Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm
      (Complex.I • Jm _ _)) l l' • omE l l') (MvPolynomial.monomial α 1) =
      (Complex.I * (((α l : ℕ) : ℂ) + 1 / 2)) • (MvPolynomial.monomial α 1 : Pol p q r s) := by
    intro l
    rw [Finset.sum_eq_single l]
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Jm_eq_diagonal,
        Matrix.smul_apply, Matrix.diagonal_apply_eq, lineEquiv_isLeft, LinearMap.smul_apply]
      cases hl : linePos l
      · rw [omE_neg l hl, smul_smul]; congr 1; simp; ring
      · rw [omE_pos l hl, smul_smul]; congr 1; simp
    · intro l' _ hl'
      have : lineEquiv p q r s l ≠ lineEquiv p q r s l' :=
        fun h => hl' ((lineEquiv p q r s).injective h).symm
      simp [Jm_eq_diagonal, Matrix.diagonal_apply_ne _ this]
    · simp
  rw [Finset.sum_congr rfl fun l _ => this l, ← Finset.sum_smul, ← Finset.mul_sum]
  congr 2
  rw [Finsupp.degree_eq_sum, Finset.sum_add_distrib]
  simp
  ring

theorem omAct_I_Jm_homog (p q r s d : ℕ) (P : Pol p q r s) (hP : P ∈ homog (Ix p q × Ix r s) d) :
    omAct p q r s (Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm
      (Complex.I • Jm _ _)) P =
    (Complex.I * ((d : ℝ) + (Fintype.card (Ln p q r s) : ℝ) / 2 : ℝ)) • P := by
  have hP' : P.IsHomogeneous d := hP
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]

  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hd : α.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hP' (MvPolynomial.mem_support_iff.1 hα)
  have : (MvPolynomial.monomial α (P.coeff α) : Pol p q r s) =
      P.coeff α • MvPolynomial.monomial α 1 := by
    rw [MvPolynomial.smul_monomial]; simp
  rw [this, map_smul, omAct_I_Jm_monomial, hd, smul_comm]

theorem inner_Om_eq_zero {p q r s : ℕ} {T0 : GrpData (p * r + q * s) (p * s + q * r)}
    {T1 : GrpData p q} {T2 : GrpData r s} (F : FockData T0 T1 T2) (k : T0.G) (hk : k ∈ T0.Kset)
    {d d' : ℕ} (hd : d' ≠ d) (R : Pol p q r s) (hR : R ∈ homog (Ix p q × Ix r s) d')
    (P : Pol p q r s) (hP : P ∈ homog (Ix p q × Ix r s) d) :
    inner ℂ (F.ι R) (F.Om k (F.ι P)) = 0 := by
  refine inner_eq_zero_of_deriv (fun t => F.Om (T0.expt (t • (Complex.I • Jm _ _))))
    (fun t x => F.isom _ x) ?_ (F.Om k) ?_ _ _
    ((d' : ℝ) + (Fintype.card (Ln p q r s) : ℝ) / 2)
    ((d : ℝ) + (Fintype.card (Ln p q r s) : ℝ) / 2) ?_ ?_ ?_
  · intro t x
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← T0.expt_add _ (I_Jm_mem _ _),
      add_neg_cancel, zero_smul, T0.expt_zero, map_one]
    rfl
  · intro t x
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, commute_expt T0 k hk, map_mul]
    rfl
  · intro h
    exact hd (by exact_mod_cast add_right_cancel h)
  · have := F.der _ (I_Jm_mem _ _) R
    rwa [omAct_I_Jm_homog p q r s d' R hR, map_smul] at this
  · have := F.der _ (I_Jm_mem _ _) P
    rwa [omAct_I_Jm_homog p q r s d P hP, map_smul] at this

theorem one_mem_Kset {p q : ℕ} (T : GrpData p q) : (1 : T.G) ∈ T.Kset := by
  intro a b hab
  rw [map_one, Units.val_one, Matrix.one_apply_ne]
  rintro rfl
  rcases a with a | a <;> simp [sameBlock] at hab

instance finiteDimensional_homog (σ : Type) [Finite σ] (d : ℕ) :
    FiniteDimensional ℂ (homog σ d) :=
  Module.Finite.iff_fg.2 (MvPolynomial.homogeneousSubmodule_fg σ ℂ d)

theorem Om_Kset_homog : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s) (F : FockData T0 T1 T2), ∀ k ∈ T0.Kset, ∀ (d : ℕ), ∀ P ∈ homog (Ix p q × Ix r s) d, ∃ Q ∈ homog (Ix p q × Ix r s) d, F.Om k (F.ι P) = F.ι Q := by
  intro p q r s T0 T1 T2 F k hk d P hP
  let E : Submodule ℂ F.H := (homog (Ix p q × Ix r s) d).map F.ι
  haveI : FiniteDimensional ℂ E := inferInstance
  obtain ⟨e, he, w', hw', hw⟩ := E.exists_add_mem_mem_orthogonal (F.Om k (F.ι P))
  obtain ⟨Q, hQ, rfl⟩ := he
  refine ⟨Q, hQ, ?_⟩
  have h0 : ∀ R, inner ℂ (F.ι R) w' = 0 := by
    intro R
    induction R using MvPolynomial.induction_on' with
    | add R S hR hS => rw [map_add (f := _), inner_add_left, hR, hS, add_zero]
    | monomial α c =>
      have hm : MvPolynomial.monomial α c ∈ homog (Ix p q × Ix r s) α.degree :=
        MvPolynomial.isHomogeneous_monomial c rfl
      by_cases h : α.degree = d
      · exact hw' _ ⟨_, h ▸ hm, rfl⟩
      · have h1 := inner_Om_eq_zero F k hk h _ hm P hP
        have h2 := inner_Om_eq_zero F 1 (one_mem_Kset T0) h _ hm Q hQ
        rw [map_one, ContinuousLinearMap.one_apply] at h2
        rwa [hw, inner_add_right, h2, zero_add] at h1
  have : w' = 0 := by
    have hc : IsClosed {x : F.H | inner ℂ x w' = 0} :=
      isClosed_eq (by fun_prop) continuous_const
    have hsub : Set.range F.ι ⊆ {x : F.H | inner ℂ x w' = 0} := by
      rintro _ ⟨R, rfl⟩; exact h0 R
    have := hc.closure_subset_iff.2 hsub (F.dense w')
    exact inner_self_eq_zero.1 this
  rw [hw, this, add_zero]

end GlobalTheory.FockDegree
end
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Matrix

noncomputable section

namespace GlobalTheory.RealPar.DerivedAdjoint

variable {p q : ℕ}

theorem Jm_diag (p q : ℕ) :
    Jm p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  unfold Jm Formalism.UG.Jpq
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply, Matrix.diagonal_apply, eq_comm] <;> split_ifs <;> simp

theorem Jm_mul_Jm (p q : ℕ) : Jm p q * Jm p q = 1 := by
  rw [Jm_diag, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  rcases i with i | i <;> simp

theorem Jm_conjTranspose (p q : ℕ) : (Jm p q)ᴴ = Jm p q := by
  rw [Jm_diag, Matrix.diagonal_conjTranspose]
  congr 1
  ext i
  rcases i with i | i <;> simp

theorem adjZ_adjZ (Z : Mat p q) : adjZ (adjZ Z) = Z := by
  unfold adjZ
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Jm_conjTranspose, ← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]
  simp only [Matrix.mul_assoc, Jm_mul_Jm, Matrix.mul_one]

theorem adjZ_add (X Y : Mat p q) : adjZ (X + Y) = adjZ X + adjZ Y := by
  unfold adjZ
  rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]

theorem adjZ_sub (X Y : Mat p q) : adjZ (X - Y) = adjZ X - adjZ Y := by
  unfold adjZ
  rw [Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]

theorem adjZ_smul (c : ℂ) (X : Mat p q) : adjZ (c • X) = star c • adjZ X := by
  unfold adjZ
  rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem mem_upq_of_adjZ {X : Mat p q} (h : adjZ X = -X) : X ∈ upq p q := by
  unfold upq
  show Xᴴ * Jm p q + Jm p q * X = 0
  have key : Jm p q * adjZ X = Xᴴ * Jm p q := by
    unfold adjZ
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]
  rw [← key, h, Matrix.mul_neg, neg_add_cancel]

theorem inner_map (T : GrpData p q) (πU : URep T) (g : T.G) (x y : πU.H) :
    inner ℂ (πU.π g x) (πU.π g y) = inner ℂ x y := by
  exact (LinearIsometry.mk (πU.π g).toLinearMap (πU.isom g)).inner_map_map x y

theorem derived_adjoint : ∀ (p q : ℕ) (T : GrpData p q) (πU : URep T) (M : GKMod p q) (j : M.V →ₗ[ℂ] πU.H), (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0) → (∀ Z x y, inner ℂ (j (M.act Z x)) (j y) = inner ℂ (j x) (j (M.act (adjZ Z) y))) := by
  intro p q T πU M j hd

  have skew : ∀ Y ∈ upq p q, ∀ x y,
      inner ℂ (j (M.act Y x)) (j y) = - inner ℂ (j x) (j (M.act Y y)) := by
    intro Y hY x y
    have h1 := (hd Y hY x).inner ℂ (hd Y hY y)
    have hconst : (fun t : ℝ => inner ℂ (πU.π (T.expt (t • Y)) (j x)) (πU.π (T.expt (t • Y)) (j y)))
        = fun _ => inner ℂ (j x) (j y) := by
      funext t
      exact inner_map T πU _ (j x) (j y)
    rw [hconst] at h1
    have h0 := h1.unique (hasDerivAt_const (0 : ℝ) (inner ℂ (j x) (j y)))
    simp only [zero_smul, T.expt_zero, map_one, ContinuousLinearMap.one_apply] at h0
    linear_combination h0

  have adj_of_mem : ∀ Y ∈ upq p q, adjZ Y = -Y := by
    intro Y hY
    have hY' : Yᴴ * Jm p q + Jm p q * Y = 0 := hY
    have e : Yᴴ * Jm p q = -(Jm p q * Y) := eq_neg_of_add_eq_zero_left hY'
    unfold adjZ
    rw [Matrix.mul_assoc, e, Matrix.mul_neg, ← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]
  have base : ∀ Y ∈ upq p q, ∀ x y,
      inner ℂ (j (M.act Y x)) (j y) = inner ℂ (j x) (j (M.act (adjZ Y) y)) := by
    intro Y hY x y
    rw [adj_of_mem Y hY, map_neg, LinearMap.neg_apply, map_neg, inner_neg_right]
    exact skew Y hY x y

  intro Z x y
  obtain ⟨A, hA⟩ : ∃ A : Mat p q, A = (1 / 2 : ℂ) • (Z - adjZ Z) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Mat p q, B = (-Complex.I / 2) • (Z + adjZ Z) := ⟨_, rfl⟩
  have hc : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    linear_combination (-1 / 2 : ℂ) * Complex.I_sq
  have hs1 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  have hs2 : star (-Complex.I / 2) = Complex.I / 2 := by
    apply Complex.ext <;> simp
  have hZ : Z = A + Complex.I • B := by
    rw [hA, hB, smul_smul, hc]
    module
  have hAm : A ∈ upq p q := by
    apply mem_upq_of_adjZ
    rw [hA, adjZ_smul, adjZ_sub, adjZ_adjZ, hs1]
    module
  have hBm : B ∈ upq p q := by
    apply mem_upq_of_adjZ
    rw [hB, adjZ_smul, adjZ_add, adjZ_adjZ, hs2]
    module
  rw [hZ]
  simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, inner_add_left,
    inner_add_right, inner_smul_left, inner_smul_right, adjZ_add, adjZ_smul, base A hAm,
    base B hBm, starRingEnd_apply]

end GlobalTheory.RealPar.DerivedAdjoint

end
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.AnalyticVec

theorem map_flow_eq_zero {V E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (ι : V → E) (a : V → V) (U : ℝ → E →L[ℝ] E) (h0 : U 0 = 1) (hadd : ∀ s t, U (s + t) = U s * U t)
    (hder : ∀ v, HasDerivAt (fun t : ℝ => U t (ι v)) (ι (a v)) 0)
    (han : ∀ v, AnalyticOnNhd ℝ (fun t : ℝ => U t (ι v)) Set.univ)
    (L : E →L[ℝ] F) (hL : ∀ v, L (ι v) = 0) (v : V) (t : ℝ) : L (U t (ι v)) = 0 := by
  have hd : ∀ w s, HasDerivAt (fun r : ℝ => U r (ι w)) (U s (ι (a w))) s := by
    intro w s
    have e : (fun r : ℝ => U r (ι w)) = fun r => U s (U (r - s) (ι w)) := by
      funext r
      have hr : r = s + (r - s) := by ring
      conv_lhs => rw [hr]
      rw [hadd, ContinuousLinearMap.mul_apply]
    rw [e]
    have hs : HasDerivAt (fun r : ℝ => r - s) 1 s := (hasDerivAt_id s).sub_const s
    have hz : HasDerivAt (fun r : ℝ => U r (ι w)) (ι (a w)) ((fun r : ℝ => r - s) s) := by
      simpa using hder w
    have h2 : HasDerivAt ((fun r : ℝ => U r (ι w)) ∘ (fun r : ℝ => r - s)) ((1 : ℝ) • ι (a w)) s :=
      HasDerivAt.scomp s hz hs
    rw [one_smul] at h2
    exact (U s).hasFDerivAt.comp_hasDerivAt s h2
  have hit : ∀ n w, deriv^[n] (fun r : ℝ => L (U r (ι w))) = fun r => L (U r (ι (a^[n] w))) := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [Function.iterate_succ_apply]
      have hD : deriv (fun r : ℝ => L (U r (ι w))) = fun r => L (U r (ι (a w))) := by
        funext r
        exact (L.hasFDerivAt.comp_hasDerivAt r (hd w r)).deriv
      rw [hD, ih (a w), Function.iterate_succ_apply]
  have hf : AnalyticOnNhd ℝ (fun r : ℝ => L (U r (ι v))) Set.univ :=
    fun r _ => (L.analyticAt _).comp (han v r (Set.mem_univ r))
  obtain ⟨p, hp⟩ := hf 0 (Set.mem_univ 0)
  have hc : ∀ n, p.coeff n = 0 := by
    intro n
    obtain ⟨ρ, hpr⟩ := hp
    have h1 := hpr.factorial_smul 1 n
    rw [← iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iterate, hit n v] at h1
    dsimp only at h1
    rw [h0, ContinuousLinearMap.one_apply, hL] at h1
    have h2 : ((n.factorial : ℝ)) • p.coeff n = 0 := by
      rw [Nat.cast_smul_eq_nsmul ℝ]
      exact h1
    exact (smul_eq_zero.mp h2).resolve_left (by exact_mod_cast n.factorial_ne_zero)
  have hp0 : p = 0 := by
    ext n y
    rw [p.apply_eq_prod_smul_coeff, hc n, smul_zero]
    rfl
  rw [hp0] at hp
  have hev : (fun r : ℝ => L (U r (ι v))) =ᶠ[nhds 0] 0 := HasFPowerSeriesAt.eventually_eq_zero hp
  have := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0) hev
    (Set.mem_univ t)
  simpa using this

private theorem eventually_abs_le_half_add_of_doubling_bounds {p q : ℕ} (T : GrpData p q) (π₁ π₂ : URep T) (M : GKMod p q)
    (j₁ : M.V →ₗ[ℂ] π₁.H) (j₂ : M.V →ₗ[ℂ] π₂.H) (Y : Mat p q) (hY : Y ∈ upq p q)
    (hd1 : ∀ x, HasDerivAt (fun t : ℝ => π₁.π (T.expt (t • Y)) (j₁ x)) (j₁ (M.act Y x)) 0)
    (hd2 : ∀ x, HasDerivAt (fun t : ℝ => π₂.π (T.expt (t • Y)) (j₂ x)) (j₂ (M.act Y x)) 0)
    (ha1 : ∀ x, AnalyticOnNhd ℝ (fun t : ℝ => π₁.π (T.expt (t • Y)) (j₁ x)) Set.univ)
    (ha2 : ∀ x, AnalyticOnNhd ℝ (fun t : ℝ => π₂.π (T.expt (t • Y)) (j₂ x)) Set.univ)
    (h : T.G) (hh : ∀ x y, inner ℂ (j₁ x) (π₁.π h (j₁ y)) = inner ℂ (j₂ x) (π₂.π h (j₂ y)))
    (t : ℝ) : ∀ x y, inner ℂ (j₁ x) (π₁.π (h * T.expt (t • Y)) (j₁ y)) =
      inner ℂ (j₂ x) (π₂.π (h * T.expt (t • Y)) (j₂ y)) := by
  intro x y
  let U : ℝ → (π₁.H × π₂.H) →L[ℝ] (π₁.H × π₂.H) := fun s =>
    ((π₁.π (T.expt (s • Y))).restrictScalars ℝ).prodMap ((π₂.π (T.expt (s • Y))).restrictScalars ℝ)
  let L : (π₁.H × π₂.H) →L[ℝ] ℂ :=
    (((innerSL ℂ (j₁ x)).comp (π₁.π h)).restrictScalars ℝ).comp (ContinuousLinearMap.fst ℝ _ _) -
    (((innerSL ℂ (j₂ x)).comp (π₂.π h)).restrictScalars ℝ).comp (ContinuousLinearMap.snd ℝ _ _)
  have key := map_flow_eq_zero (fun v => (j₁ v, j₂ v)) (M.act Y) U ?_ ?_ ?_ ?_ L ?_ y t
  · have e : L (U t (j₁ y, j₂ y)) = inner ℂ (j₁ x) (π₁.π (h * T.expt (t • Y)) (j₁ y)) -
        inner ℂ (j₂ x) (π₂.π (h * T.expt (t • Y)) (j₂ y)) := by
      simp [L, U, map_mul]
    rw [e, sub_eq_zero] at key
    exact key
  · refine ContinuousLinearMap.ext fun z => ?_
    simp [U, T.expt_zero]
  · intro s r
    refine ContinuousLinearMap.ext fun z => ?_
    simp [U, T.expt_add Y hY, map_mul]
    rfl
  · intro v
    exact (hd1 v).prodMk (hd2 v)
  · intro v
    exact (ha1 v).prod (ha2 v)
  · intro v
    simp [L, hh]

theorem inner_apply_eq_of_analytic : ∀ (p q : ℕ) (T : GrpData p q), Subgroup.closure (T.expt '' upq p q) = ⊤ → ∀ (π₁ π₂ : URep T) (M : GKMod p q) (j₁ : M.V →ₗ[ℂ] π₁.H) (j₂ : M.V →ₗ[ℂ] π₂.H), (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => π₁.π (T.expt (t • Y)) (j₁ x)) (j₁ (M.act Y x)) 0) → (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => π₂.π (T.expt (t • Y)) (j₂ x)) (j₂ (M.act Y x)) 0) → (∀ Y ∈ upq p q, ∀ x, AnalyticOnNhd ℝ (fun t : ℝ => π₁.π (T.expt (t • Y)) (j₁ x)) Set.univ) → (∀ Y ∈ upq p q, ∀ x, AnalyticOnNhd ℝ (fun t : ℝ => π₂.π (T.expt (t • Y)) (j₂ x)) Set.univ) → (∀ x y, inner ℂ (j₁ x) (j₁ y) = inner ℂ (j₂ x) (j₂ y)) → ∀ g x y, inner ℂ (j₁ x) (π₁.π g (j₁ y)) = inner ℂ (j₂ x) (π₂.π g (j₂ y)) := by
  intro p q T hT π₁ π₂ M j₁ j₂ hd1 hd2 ha1 ha2 hiso
  let Q : T.G → Prop := fun h => ∀ x y, inner ℂ (j₁ x) (π₁.π h (j₁ y)) = inner ℂ (j₂ x) (π₂.π h (j₂ y))
  let S : Subgroup T.G :=
    { carrier := {g | ∀ h, Q h ↔ Q (h * g)}
      mul_mem' := fun {a b} ha hb h => (ha h).trans (by rw [hb (h * a), mul_assoc])
      one_mem' := fun h => by rw [mul_one]
      inv_mem' := fun {g} hg h => by
        have e := hg (h * g⁻¹)
        rw [inv_mul_cancel_right] at e
        exact e.symm }
  have hle : Subgroup.closure (T.expt '' upq p q) ≤ S := by
    rw [Subgroup.closure_le]
    rintro _ ⟨Y, hY, rfl⟩ h
    have e : T.expt Y * T.expt ((-1 : ℝ) • Y) = 1 := by
      have e1 := T.expt_add Y hY 1 (-1)
      rw [one_smul, show (1 : ℝ) + -1 = 0 by norm_num, zero_smul, T.expt_zero] at e1
      exact e1.symm
    constructor
    · intro hh
      have h2 := eventually_abs_le_half_add_of_doubling_bounds T π₁ π₂ M j₁ j₂ Y hY (hd1 Y hY) (hd2 Y hY) (ha1 Y hY) (ha2 Y hY) h hh 1
      rw [one_smul] at h2
      exact h2
    · intro hh
      have h2 := eventually_abs_le_half_add_of_doubling_bounds T π₁ π₂ M j₁ j₂ Y hY (hd1 Y hY) (hd2 Y hY) (ha1 Y hY) (ha2 Y hY)
        (h * T.expt Y) hh (-1)
      rw [mul_assoc, e, mul_one] at h2
      exact h2
  have q1 : Q 1 := by
    intro x y
    rw [map_one, map_one, ContinuousLinearMap.one_apply, ContinuousLinearMap.one_apply]
    exact hiso x y
  intro g
  have hg : g ∈ S := hle (by rw [hT]; exact Subgroup.mem_top g)
  have q2 := (hg 1).mp q1
  rw [one_mul] at q2
  exact q2

end GlobalTheory.AnalyticVec
end
