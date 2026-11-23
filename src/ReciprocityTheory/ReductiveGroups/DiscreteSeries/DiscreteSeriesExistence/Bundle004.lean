module

public import Formalism.HermitianCurvature.StatementB
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.PolarJmConjTranspose
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle011
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle003

@[expose] public section

section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def sztJd (ε : Fin n → Bool) : Fin n → ℂ := fun a => if ε a then 1 else -1

theorem szt_Jm_eq (ε : Fin n → Bool) : Jm ε = Matrix.diagonal (sztJd ε) := rfl

theorem szt_jd_sq (ε : Fin n → Bool) (a : Fin n) : sztJd ε a * sztJd ε a = 1 := by
  unfold sztJd
  split_ifs <;> norm_num

theorem szt_lead_Jconj (ε : Fin n → Bool) (z : Matrix (Fin n) (Fin n) ℂ) (i : ℕ) :
    S7.lead i (Jm ε * z * Jm ε) = S7.lead i z := by
  unfold S7.lead
  split_ifs with h
  · have hsub : (Jm ε * z * Jm ε).submatrix (Fin.castLE h) (Fin.castLE h) =
        Matrix.diagonal (sztJd ε ∘ Fin.castLE h) * z.submatrix (Fin.castLE h) (Fin.castLE h) *
          Matrix.diagonal (sztJd ε ∘ Fin.castLE h) := by
      rw [szt_Jm_eq]
      ext a b
      simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Function.comp_apply]
    rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    have hA : (∏ a, (sztJd ε ∘ Fin.castLE h) a) * (∏ a, (sztJd ε ∘ Fin.castLE h) a) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun a _ => szt_jd_sq ε _
    calc (∏ a, (sztJd ε ∘ Fin.castLE h) a) * (z.submatrix (Fin.castLE h) (Fin.castLE h)).det *
          (∏ a, (sztJd ε ∘ Fin.castLE h) a)
        = ((∏ a, (sztJd ε ∘ Fin.castLE h) a) * (∏ a, (sztJd ε ∘ Fin.castLE h) a)) *
            (z.submatrix (Fin.castLE h) (Fin.castLE h)).det := by ring
      _ = (z.submatrix (Fin.castLE h) (Fin.castLE h)).det := by rw [hA, one_mul]
  · rfl

theorem szt_phiM_Jconj (ε : Fin n → Bool) (μ : Fin n → ℤ) (z : Matrix (Fin n) (Fin n) ℂ) :
    S7.PhiM μ (Jm ε * z * Jm ε) = S7.PhiM μ z := by
  unfold S7.PhiM
  simp only [szt_lead_Jconj]

theorem szt_phiM_inv_conj {ε : Fin n → Bool} (μ : Fin n → ℤ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X)
    (k : S7.KG ε) :
    S7.PhiM μ (S7.toMK k⁻¹ * NormedSpace.exp X * S7.toMK k)⁻¹ =
      S7.PhiM μ (S7.toMK k⁻¹ * NormedSpace.exp X * S7.toMK k) := by
  obtain ⟨hY, hE⟩ := S7.inP_conj k⁻¹ hX
  simp only [inv_inv] at hY hE
  rw [← hE, Matrix.inv_eq_left_inv (PolarDecomposition.polar_exp_neg_mul _), ← S7.inP_JXJ hY,
    PolarDecomposition.polar_exp_Jconj, szt_phiM_Jconj]

section Cayley

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

theorem szt_unitary (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) : Pᴴ * P = 1 ∧ P * Pᴴ = 1 := by
  have hPu : P ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := hP.2
  refine ⟨?_, ?_⟩
  · have := (Matrix.mem_unitaryGroup_iff' (A := P)).mp hPu
    simpa [Matrix.star_eq_conjTranspose] using this
  · have := (Matrix.mem_unitaryGroup_iff (A := P)).mp hPu
    simpa [Matrix.star_eq_conjTranspose] using this

theorem szt_conj_mem (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : P * g * P⁻¹ ∈ UJset ε := by
  rw [← mir_UJset_eq]
  obtain ⟨e1, e2⟩ := szt_unitary hP
  have hinv : P⁻¹ = Pᴴ := Matrix.inv_eq_left_inv e1
  have hc : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.1.2
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε
  rw [hinv]
  calc (P * g * Pᴴ)ᴴ * Formalism.REAL.Jm ε * (P * g * Pᴴ)
      = P * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * Pᴴ := by
        simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = P * Pᴴ * Formalism.REAL.Jm ε * (P * Pᴴ) := by
        rw [hc, hg', ← hc]; simp [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [e2]; simp

theorem szt_hs_conj (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    S7.hs (P * g * P⁻¹) = S7.hs g := by
  obtain ⟨e1, -⟩ := szt_unitary hP
  have hinv : P⁻¹ = Pᴴ := Matrix.inv_eq_left_inv e1
  have h := S7.decA_hs_conj (K := Pᴴ) (by rw [Matrix.conjTranspose_conjTranspose]; exact e1) g
  rw [Matrix.conjTranspose_conjTranspose] at h
  rw [hinv]
  exact h

end Cayley

theorem szt_gN_eq {k r : ℕ} (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Formalism.FourierDecayAlt.B.gN g = Real.sqrt (S7.hs g) := by
  unfold Formalism.FourierDecayAlt.B.gN S7.hs
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact Complex.normSq_eq_norm_sq _

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem bhw_Ecc_Eab (hE : IsGlRep E) {μ : Fin n → ℝ} {v : D} (hv : ∀ c, E c c v = ((μ c : ℝ) : ℂ) • v)
    (a b : Fin n) (c : Fin n) : E c c (E a b v) = (((μ + root a b) c : ℝ) : ℂ) • E a b v := by
  have h : E c c (E a b v) - E a b (E c c v) =
      (if c = a then E c b else 0) v - (if b = c then E a c else 0) v :=
    LinearMap.congr_fun (hE c c a b) v
  rw [sub_eq_iff_eq_add.mp h, hv c, map_smul]
  rcases eq_or_ne c a with h1 | h1 <;> rcases eq_or_ne c b with h2 | h2
  · subst h1; subst h2; simp [root]
  · subst h1; simp [root, Pi.single_apply, Ne.symm h2, h2, add_smul, add_comm]
  · subst h2; simp [root, Pi.single_apply, h1, sub_smul, add_smul]; exact add_comm _ _
  · simp [root, Pi.single_apply, h1, h2, Ne.symm h2]

private theorem hasDerivAt_zero_mem_of_forall_mem_finiteDim {S : Submodule ℂ H} [FiniteDimensional ℂ S] {f : ℝ → H} {L : H}
    (hf : HasDerivAt f L 0) (hS : ∀ t, f t ∈ S) : L ∈ S := by
  have hc : IsClosed (S : Set H) := Submodule.closed_of_finiteDimensional S
  refine hc.mem_of_tendsto hf.tendsto_slope_zero (Filter.Eventually.of_forall fun t => ?_)
  rw [zero_add]
  exact Submodule.smul_of_tower_mem S t⁻¹ (S.sub_mem (hS t) (hS 0))

private theorem exp_real_smul_mem_Kset_of_skewHermitian_commute_Jm (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X)
    (hJ : X * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Formalism.REAL.Kset ε := by
  have hsk : ((t : ℂ) • X)ᴴ = -((t : ℂ) • X) := by
    rw [Matrix.conjTranspose_smul, hX]; simp
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hsk,
      ← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl ((t : ℂ) • X)))]
    simp
  · exact (Commute.exp_left (Commute.smul_left hJ (t : ℂ))).eq

private theorem inG_of_conjTranspose_eq_neg_commute_Jm (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X)
    (hJ : X * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * X) : inG ε X := by
  have hJJ : Jm ε = Formalism.REAL.Jm ε := rfl
  show Xᴴ * Jm ε + Jm ε * X = 0
  rw [hJJ, hX, neg_mul, hJ]
  simp

private theorem commute_Jm_of_support_same_sign (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : ∀ i j, X i j ≠ 0 → ε i = ε j) : X * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * X := by
  ext i j
  rw [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : X i j = 0
  · simp [h]
  · rw [hX i j h]; ring

private theorem E_mem_of_isKStableOn_of_same_sign (hD : IsDerivedOn ε σ D E) {S : Submodule ℂ H} [FiniteDimensional ℂ S]
    (hS : Formalism.MainNotions.S.IsKStableOn ε σ S) (a b : Fin n) (he : ε a = ε b) (w : D) (hw : (w : H) ∈ S) :
    ((E a b w : D) : H) ∈ S := by
  have gen : ∀ c : ℂ, (((c • E a b - star c • E b a) w : D) : H) ∈ S := by
    intro c
    have hsk : (Matrix.of fun i j => (if i = a then (if j = b then c else 0) else 0) -
        (if i = b then (if j = a then star c else 0) else 0) : Matrix (Fin n) (Fin n) ℂ)ᴴ =
        -(Matrix.of fun i j => (if i = a then (if j = b then c else 0) else 0) -
        (if i = b then (if j = a then star c else 0) else 0)) := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.neg_apply]
      split_ifs <;> simp
    have hcm := commute_Jm_of_support_same_sign ε (Matrix.of fun i j => (if i = a then (if j = b then c else 0) else 0) -
        (if i = b then (if j = a then star c else 0) else 0)) (by
      intro i j h
      simp only [Matrix.of_apply] at h
      split_ifs at h <;> simp_all)
    have hact : actM E (Matrix.of fun i j => (if i = a then (if j = b then c else 0) else 0) -
        (if i = b then (if j = a then star c else 0) else 0)) = c • E a b - star c • E b a := by
      have key : ∀ (p q : Fin n) (d : ℂ),
          (∑ i, ∑ j, (if i = p then (if j = q then d else 0) else 0) • E i j) = d • E p q := by
        intro p q d
        rw [Finset.sum_eq_single p (fun i _ hi => by simp [hi]) (by simp),
          Finset.sum_eq_single q (fun j _ hj => by simp [hj]) (by simp)]
        simp
      simp only [actM, Matrix.of_apply, sub_smul, Finset.sum_sub_distrib]
      rw [key, key]
    rw [← hact]
    exact hasDerivAt_zero_mem_of_forall_mem_finiteDim (hD.deriv _ (inG_of_conjTranspose_eq_neg_commute_Jm ε _ hsk hcm) w)
      (fun t => hS _ (exp_real_smul_mem_Kset_of_skewHermitian_commute_Jm ε _ hsk hcm t) _ hw)
  have h1 := gen 1
  have hI := gen Complex.I
  have h2 : ((((2 * Complex.I) • E a b w : D)) : H) ∈ S := by
    have : (2 * Complex.I) • E a b w =
        Complex.I • ((((1 : ℂ) • E a b - star (1 : ℂ) • E b a) w)) +
          (Complex.I • E a b - star Complex.I • E b a) w := by
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, star_one, one_smul,
        Complex.star_def, Complex.conj_I, neg_smul, sub_neg_eq_add, smul_sub]
      rw [two_mul, add_smul]
      abel
    rw [this, Submodule.coe_add, Submodule.coe_smul]
    exact S.add_mem (S.smul_mem _ h1) hI
  rw [Submodule.coe_smul] at h2
  exact (Submodule.smul_mem_iff S (by simp [Complex.I_ne_zero])).1 h2

private theorem not_CDom_add_root_of_lt (ε : Fin n → Bool) (μ : Fin n → ℝ) (a b : Fin n) (hab : a < b)
    (h : Formalism.MainNotions.S.CDom ε (μ + root a b) μ) : False := by
  obtain ⟨c, hc, hsum⟩ := h
  rw [sub_add_cancel_left] at hsum
  have hr : ∀ i j : Fin n, ∑ k : Fin n, ((k : ℕ) : ℝ) * (Formalism.REAL.root i j) k =
      ((i : ℕ) : ℝ) - ((j : ℕ) : ℝ) := by
    intro i j
    simp [Formalism.REAL.root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
  have hL : ∑ k : Fin n, ((k : ℕ) : ℝ) * (-(root a b)) k = ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) := by
    simp [root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
  have hR : ∑ k : Fin n, ((k : ℕ) : ℝ) * (∑ i, ∑ j, (c i j : ℝ) • Formalism.REAL.root i j) k =
      ∑ i, ∑ j, (c i j : ℝ) * (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hr i j, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have h1 : ∑ k : Fin n, ((k : ℕ) : ℝ) * (-(root a b)) k =
      ∑ k : Fin n, ((k : ℕ) : ℝ) * (∑ i, ∑ j, (c i j : ℝ) • Formalism.REAL.root i j) k := by
    rw [hsum]
  rw [hL, hR] at h1
  have hle : ∑ i, ∑ j, (c i j : ℝ) * (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) ≤ 0 := by
    refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j _ => ?_
    by_cases h0 : c i j = 0
    · simp [h0]
    · have hij : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast (hc i j h0).1
      have hcn : (0 : ℝ) ≤ (c i j : ℝ) := Nat.cast_nonneg _
      nlinarith
  have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  linarith

theorem exists_isKHWVec_of_isKTypeOf (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {μ : Fin n → ℝ} {S : Submodule ℂ H} (hS : Formalism.MainNotions.S.IsKTypeOf ε σ μ S) (hSD : S ≤ D) :
    ∃ w : D, (w : H) ∈ S ∧ w ≠ 0 ∧ IsKHWVec ε E μ w := by
  obtain ⟨hfd, hst, -, ⟨v, hvS, hv0, hvw⟩, hdom⟩ := hS
  haveI : FiniteDimensional ℂ S := hfd
  have hwt := (isWtOn_iff hσ hD ⟨v, hSD hvS⟩ μ).1 hvw
  refine ⟨⟨v, hSD hvS⟩, hvS, ?_, fun a => hwt a, fun a b hab he => ?_⟩
  · intro h
    apply hv0
    simpa using congrArg (fun x : D => (x : H)) h
  · by_contra hne
    have huS : ((E a b ⟨v, hSD hvS⟩ : D) : H) ∈ S := E_mem_of_isKStableOn_of_same_sign hD hst a b he _ hvS
    have hu0 : ((E a b ⟨v, hSD hvS⟩ : D) : H) ≠ 0 := fun h => hne (by simpa using h)
    have huw : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ (μ + root a b) ((E a b ⟨v, hSD hvS⟩ : D) : H) :=
      (isWtOn_iff hσ hD _ (μ + root a b)).2 (fun c => bhw_Ecc_Eab hD.glRep hwt a b c)
    exact not_CDom_add_root_of_lt ε μ a b hab (hdom _ _ huS hu0 huw)

end ReciprocityTheory.ChartRestriction.DS
end
end
