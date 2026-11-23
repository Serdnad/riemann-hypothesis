module

public import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Bundle001
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Analysis.Matrix.Order

@[expose] public section

section

open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu

noncomputable section

namespace GlobalTheory.CompanionTheory.BmuWordBd

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def lieSub {n : ℕ} (Hm : Mat n) : Submodule ℝ (Mat n) where
  carrier := {X | Lie Hm X}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Lie] at *
    rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, ha, hb, add_zero]
  zero_mem' := by simp [Lie]
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq, Lie] at *
    rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, ha, smul_zero]

theorem exists_basis_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S : Submodule ℝ E) :
    ∃ (N : ℕ) (b : Fin N → E) (κ : ℝ), 0 ≤ κ ∧ (∀ i, b i ∈ S) ∧
      ∀ X, X ∈ S → ∃ c : Fin N → ℝ, X = ∑ i, c i • b i ∧ ∀ i, |c i| ≤ κ * ‖X‖ := by
  let bS := Module.finBasis ℝ S
  let L : Fin (Module.finrank ℝ S) → (S →L[ℝ] ℝ) := fun i => LinearMap.toContinuousLinearMap (bS.coord i)
  refine ⟨Module.finrank ℝ S, fun i => (bS i : E), ∑ i, ‖L i‖,
    Finset.sum_nonneg (fun i _ => norm_nonneg _), fun i => (bS i).2, ?_⟩
  intro X hX
  refine ⟨fun i => bS.repr ⟨X, hX⟩ i, ?_, ?_⟩
  · calc X = ((⟨X, hX⟩ : S) : E) := rfl
      _ = ((∑ i, bS.repr ⟨X, hX⟩ i • bS i : S) : E) := by rw [bS.sum_repr]
      _ = ∑ i, bS.repr ⟨X, hX⟩ i • (bS i : E) := by simp only [Submodule.coe_sum, Submodule.coe_smul]
  · intro i
    have h1 : |bS.repr ⟨X, hX⟩ i| ≤ ‖L i‖ * ‖X‖ := by
      have := (L i).le_opNorm ⟨X, hX⟩
      simpa [L, Real.norm_eq_abs] using this
    have h2 : ‖L i‖ ≤ ∑ j, ‖L j‖ := Finset.single_le_sum (fun j _ => norm_nonneg (L j)) (Finset.mem_univ i)
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))

theorem exists_basis {n : ℕ} (Hm : Mat n) :
    ∃ (N : ℕ) (b : Fin N → Mat n) (κ : ℝ), 0 ≤ κ ∧ (∀ i, Lie Hm (b i)) ∧
      ∀ X, Lie Hm X → ∃ c : Fin N → ℝ, X = ∑ i, c i • b i ∧ ∀ i, |c i| ≤ κ * ‖X‖ := by
  obtain ⟨N, b, κ, hκ, hb, hX⟩ := exists_basis_sub (lieSub Hm)
  exact ⟨N, b, κ, hκ, hb, fun X hXL => hX X hXL⟩

theorem dsW_sum {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] {G : Set (Mat n)}
    {σ : Mat n → (H →L[ℂ] H)} (h : RepOn G σ) {ι : Type*} (s : Finset ι) (v : ι → H)
    (hv : ∀ i, IsSm G σ (v i)) {W : List (Mat n)} (hW : LieW G W) :
    IsSm G σ (∑ i ∈ s, v i) ∧ dsW σ W (∑ i ∈ s, v i) = ∑ i ∈ s, dsW σ W (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨IsSm.zero, by simpa using dsW_smul h (IsSm.zero (G := G) (σ := σ)) (0 : ℂ) hW⟩
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨(hv a).add ih.1, by rw [dsW_add h (hv a) ih.1 hW, ih.2]⟩

private theorem ex_mem_UH_of_lie {n : ℕ} {Hm X : Mat n} (hsq : Hm * Hm = 1) (hX : Lie Hm X) (t : ℝ) :
    ex X t ∈ Formalism.QuantumDeterminants.UH Hm := by
  have hinv : Hm⁻¹ = Hm := Matrix.inv_eq_right_inv hsq
  have hU : IsUnit Hm := ⟨⟨Hm, Hm, hsq, hsq⟩, rfl⟩
  have h1 : Xᴴ * Hm = -(Hm * X) := eq_neg_of_add_eq_zero_left hX
  have hXH : Xᴴ = Hm * (-X) * Hm := by
    calc Xᴴ = Xᴴ * Hm * Hm := by rw [mul_assoc, hsq, mul_one]
      _ = Hm * (-X) * Hm := by rw [h1, Matrix.mul_neg]
  have hconj : ((t : ℂ) • X)ᴴ = Hm * (-((t : ℂ) • X)) * Hm⁻¹ := by
    rw [Matrix.conjTranspose_smul, hXH, hinv]
    simp [Matrix.mul_smul, Matrix.smul_mul, Complex.conj_ofReal]
  show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Hm * NormedSpace.exp ((t : ℂ) • X) = Hm
  rw [← Matrix.exp_conjTranspose, hconj, Matrix.exp_conj _ _ hU, hinv, mul_assoc (Hm * _) Hm Hm, hsq,
    mul_one, mul_assoc, ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl ((t : ℂ) • X))),
    neg_add_cancel, NormedSpace.exp_zero, mul_one]

private theorem dsW_append' {n : ℕ} {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (σ : Mat n → (H →L[ℂ] H)) (P W : List (Mat n)) (v : H) :
    dsW σ (P ++ W) v = dsW σ P (dsW σ W v) := by
  show List.foldr (ds σ) v (P ++ W) = List.foldr (ds σ) (List.foldr (ds σ) v W) P
  exact List.foldr_append

theorem wordBd_of_dsLin : DsLin → WordBd := by
  intro hD
  unfold WordBd
  intro n Hm H _ _ _ σ hU w hw m
  have hrep : RepOn (Formalism.QuantumDeterminants.UH Hm) σ := hU.rep
  have hsq : Hm * Hm = 1 := hU.sq
  have hlie : ∀ W : List (Mat n), LieWd Hm W → LieW (Formalism.QuantumDeterminants.UH Hm) W :=
    fun W hW X hX t => ex_mem_UH_of_lie hsq (hW X hX) t
  obtain ⟨N, b, κ, hκ, hb, hc⟩ := exists_basis Hm
  have hexp : ∀ v, IsSm (Formalism.QuantumDeterminants.UH Hm) σ v → ∀ X, Lie Hm X →
      ∃ c : Fin N → ℝ, (∀ i, |c i| ≤ κ * ‖X‖) ∧ ds σ X v = ∑ i, (c i : ℂ) • ds σ (b i) v := by
    intro v hv X hX
    obtain ⟨Λ, hΛ⟩ := hD n Hm H σ hU v hv
    obtain ⟨c, hXc, hcb⟩ := hc X hX
    refine ⟨c, hcb, ?_⟩

    rw [hΛ X hX, hXc, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, ← hΛ (b i) (hb i), Complex.coe_smul]
  have hlb : ∀ i, LieWd Hm [b i] := by
    intro i Y hY
    rw [List.mem_singleton] at hY
    subst hY
    exact hb i
  have key : ∀ k : ℕ, ∀ P : List (Mat n), LieWd Hm P → ∃ C : ℝ, 0 ≤ C ∧
      ∀ W : List (Mat n), LieWd Hm W → W.length ≤ k →
        ‖dsW σ (P ++ W) w‖ ≤ C * (W.map (fun X => ‖X‖)).prod := by
    intro k
    induction k with
    | zero =>
      intro P _
      refine ⟨‖dsW σ P w‖, norm_nonneg _, fun W _ hW => ?_⟩
      have hW0 : W = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hW)
      subst hW0
      simp
    | succ k ih =>
      intro P hP
      have hPb : ∀ i, LieWd Hm (P ++ [b i]) := by
        intro i Y hY
        rcases List.mem_append.1 hY with h | h
        · exact hP Y h
        · exact hlb i Y h
      choose C hC0 hC using fun i : Fin N => ih (P ++ [b i]) (hPb i)
      refine ⟨max ‖dsW σ P w‖ (κ * ∑ i, C i), le_max_of_le_left (norm_nonneg _), ?_⟩
      intro W hW hlen
      cases W with
      | nil =>
        simp only [List.append_nil, List.map_nil, List.prod_nil, mul_one]
        exact le_max_left _ _
      | cons X W' =>
        have hX : Lie Hm X := hW X List.mem_cons_self
        have hW' : LieWd Hm W' := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
        have hlen' : W'.length ≤ k := by simpa using hlen
        have hv : IsSm (Formalism.QuantumDeterminants.UH Hm) σ (dsW σ W' w) := hw.dsW hrep (hlie W' hW')
        obtain ⟨c, hcb, hds⟩ := hexp _ hv X hX
        have hsm : ∀ i, IsSm (Formalism.QuantumDeterminants.UH Hm) σ (ds σ (b i) (dsW σ W' w)) :=
          fun i => hv.dsW hrep (hlie [b i] (hlb i))
        have heq : dsW σ (P ++ X :: W') w = ∑ i, (c i : ℂ) • dsW σ ((P ++ [b i]) ++ W') w := by
          rw [dsW_append', dsW_cons, hds,
            (dsW_sum hrep Finset.univ _ (fun i => (hsm i).smul (c i : ℂ)) (hlie P hP)).2]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [dsW_smul hrep (hsm i) _ (hlie P hP), dsW_append', dsW_append']
          rfl
        have hprod : 0 ≤ (W'.map (fun X => ‖X‖)).prod :=
          List.prod_nonneg (fun a ha => by
            obtain ⟨Y, _, rfl⟩ := List.mem_map.1 ha
            exact norm_nonneg _)
        simp only [List.map_cons, List.prod_cons]
        rw [heq]
        calc ‖∑ i, (c i : ℂ) • dsW σ ((P ++ [b i]) ++ W') w‖
            ≤ ∑ i, ‖(c i : ℂ) • dsW σ ((P ++ [b i]) ++ W') w‖ := norm_sum_le _ _
          _ ≤ ∑ i, (κ * ‖X‖) * (C i * (W'.map (fun X => ‖X‖)).prod) := by
              refine Finset.sum_le_sum fun i _ => ?_
              rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
              exact mul_le_mul (hcb i) (hC i W' hW' hlen') (norm_nonneg _)
                (mul_nonneg hκ (norm_nonneg _))
          _ = (κ * ∑ i, C i) * (‖X‖ * (W'.map (fun X => ‖X‖)).prod) := by
              rw [Finset.mul_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl fun i _ => ?_
              ring
          _ ≤ max ‖dsW σ P w‖ (κ * ∑ i, C i) * (‖X‖ * (W'.map (fun X => ‖X‖)).prod) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg (norm_nonneg _) hprod)
  obtain ⟨C, hC0, hC⟩ := key m [] (fun X hX => absurd hX List.not_mem_nil)
  exact ⟨C, hC0, fun W hW hlen => by simpa using hC W hW hlen⟩

end GlobalTheory.CompanionTheory.BmuWordBd
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.BmuIwa

open Matrix CompanionTheory.Bmu CompanionTheory.D.gk.admitted.CholeskyDecomposition Formalism.QuantumDeterminants
open scoped ComplexOrder MatrixOrder

theorem adapted_dec_one {n : ℕ} {p : Fin n → Fin n} {b : Fin n → ℤ} {c : Fin n → ℂ} (h : Adapted p b c)
    (g : Matrix (Fin n) (Fin n) ℂ) (hg : gᴴ * dp p 0 c * g = dp p 0 c) :
    ∃ k B : Matrix (Fin n) (Fin n) ℂ, kᴴ * k = 1 ∧ kᴴ * dp p 0 c * k = dp p 0 c ∧
      Bᴴ * dp p 0 c * B = dp p 0 c ∧ g = k * B ∧ B.BlockTriangular id := by
  set A := dp p 0 c with hAdef
  have hA : A * A = 1 := h.mul_self
  have hAH : Aᴴ = A := h.herm
  have hg' : g * A * gᴴ = A := flip hA hg
  have hgu : IsUnit g := by
    refine ⟨⟨g, A * gᴴ * A, ?_, ?_⟩, rfl⟩
    · calc g * (A * gᴴ * A) = (g * A * gᴴ) * A := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hg', hA]
    · calc (A * gᴴ * A) * g = A * (gᴴ * A * g) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hg, hA]
  obtain ⟨B, a, hB, ha, hBd, hBS⟩ :=
    exists_cholesky (PosDef.conjTranspose_mul_self g (mulVec_injective_of_isUnit hgu))
  have hBdet : IsUnit B.det := by
    rw [det_of_isUpperTriangular hB]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => by
      rw [hBd i]; exact RCLike.ofReal_ne_zero.2 (ha i).ne')
  have hBi : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul _ hBdet
  have hBi' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hBdet
  have hBiH : B⁻¹ᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, hBi', conjTranspose_one]

  have hS : Bᴴ * B * A * (Bᴴ * B) = A := by
    rw [hBS]
    calc gᴴ * g * A * (gᴴ * g) = gᴴ * (g * A * gᴴ) * g := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hg', hg]
  have hS1 : A * (Bᴴ * B) * A * Bᴴ * B = 1 := by
    calc A * (Bᴴ * B) * A * Bᴴ * B = A * (Bᴴ * B * A * (Bᴴ * B)) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hS, hA]
  have hu : B * (A * (Bᴴ * B) * A * Bᴴ) = 1 := mul_eq_one_comm.1 hS1
  have hw : (B * (A * Bᴴ * A))ᴴ * (B * (A * Bᴴ * A)) = 1 := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hAH]
    calc A * (B * A) * Bᴴ * (B * (A * Bᴴ * A)) = A * (B * (A * (Bᴴ * B) * A * Bᴴ)) * A := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hu, Matrix.mul_one, hA]
  have hw1 : B * (A * Bᴴ * A) = 1 :=
    eq_one_of_posSemidef hw (h.posSemidef hB ha hBd fun i j hij =>
      eq_zero_of_unitary_blockTriangular hw ((h.tri hB).mul (h.conj_tri hB)) hij)
  have hw2 : (A * Bᴴ * A) * B = 1 := mul_eq_one_comm.1 hw1
  have hBA : Bᴴ * A * B = A := by
    calc Bᴴ * A * B = (A * A) * (Bᴴ * A * B) := by rw [hA, Matrix.one_mul]
      _ = A * ((A * Bᴴ * A) * B) := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hw2, Matrix.mul_one]
  refine ⟨g * B⁻¹, B, ?_, ?_, hBA, ?_, hB⟩
  · rw [conjTranspose_mul]
    calc B⁻¹ᴴ * gᴴ * (g * B⁻¹) = B⁻¹ᴴ * (gᴴ * g) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (B⁻¹ᴴ * Bᴴ) * (B * B⁻¹) := by rw [← hBS]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBiH, hBi', Matrix.one_mul]
  · rw [conjTranspose_mul]
    calc B⁻¹ᴴ * gᴴ * A * (g * B⁻¹) = B⁻¹ᴴ * (gᴴ * A * g) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = B⁻¹ᴴ * (Bᴴ * A * B) * B⁻¹ := by rw [hg, hBA]
      _ = (B⁻¹ᴴ * Bᴴ) * A * (B * B⁻¹) := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hBiH, hBi', Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.mul_assoc, hBi, Matrix.mul_one]

theorem conj_mem {n : ℕ} {A g : Matrix (Fin n) (Fin n) ℂ} (hA : A * A = 1) (hAH : Aᴴ = A)
    (hg : gᴴ * A * g = A) : (A * gᴴ * A)ᴴ * A * (A * gᴴ * A) = A := by
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, hAH]
  calc A * (g * A) * A * (A * gᴴ * A) = A * (g * (A * A) * A * gᴴ) * A := by simp only [Matrix.mul_assoc]
    _ = A := by rw [hA, Matrix.mul_one, CompanionTheory.D.gk.admitted.CholeskyDecomposition.flip hA hg, hA, Matrix.one_mul]

theorem conj_mul {n : ℕ} {A g : Matrix (Fin n) (Fin n) ℂ} (hA : A * A = 1)
    (hg : gᴴ * A * g = A) : (A * gᴴ * A) * g = 1 := by
  calc (A * gᴴ * A) * g = A * (gᴴ * A * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, hA]

theorem adapted_dec_left {n : ℕ} {p : Fin n → Fin n} {b : Fin n → ℤ} {c : Fin n → ℂ} (h : Adapted p b c)
    (x : Matrix (Fin n) (Fin n) ℂ) (hx : xᴴ * dp p 0 c * x = dp p 0 c) :
    ∃ s κ : Matrix (Fin n) (Fin n) ℂ, sᴴ * dp p 0 c * s = dp p 0 c ∧ κᴴ * dp p 0 c * κ = dp p 0 c ∧
      s.BlockTriangular id ∧ κᴴ * κ = 1 ∧ x = s * κ := by
  have hA := h.mul_self
  have hAH := h.herm
  obtain ⟨k, B, hk, hkA, hBA, hg, hB⟩ := adapted_dec_one h _ (conj_mem hA hAH hx)
  set A := dp p 0 c
  have hBl := conj_mul hA hBA
  have hk' : k * kᴴ = 1 := mul_eq_one_comm.1 hk
  refine ⟨A * Bᴴ * A, kᴴ, conj_mem hA hAH hBA, ?_, ?_, ?_, ?_⟩
  · rw [conjTranspose_conjTranspose]; exact CompanionTheory.D.gk.admitted.CholeskyDecomposition.flip hA hkA
  · let _ : Invertible B := invertibleOfLeftInverse B _ hBl
    rw [← inv_eq_left_inv hBl]
    exact blockTriangular_inv_of_blockTriangular hB
  · rw [conjTranspose_conjTranspose]; exact hk'
  · have h1 : k * B * x = 1 := by rw [← hg]; exact conj_mul hA hx
    calc x = (A * Bᴴ * A * B) * x := by rw [hBl, Matrix.one_mul]
      _ = A * Bᴴ * A * ((kᴴ * k) * B * x) := by rw [hk, Matrix.one_mul]; simp only [Matrix.mul_assoc]
      _ = A * Bᴴ * A * kᴴ * (k * B * x) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one]

def pq (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) := if outer k r i then i.rev else i

def bq (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℤ := if outer k r i then 2 * (i.val : ℤ) - (2 * r + k) else 0

theorem pq_val (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    (pq k r i).val = if i.val ≤ r ∨ r + k ≤ i.val then 2 * r + k - i.val else i.val := by
  unfold pq
  by_cases h : outer k r i
  · rw [if_pos h, if_pos (show i.val ≤ r ∨ r + k ≤ i.val from h), Fin.val_rev]; omega
  · rw [if_neg h, if_neg (show ¬ (i.val ≤ r ∨ r + k ≤ i.val) from h)]

theorem bq_eq (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    bq k r i = if i.val ≤ r ∨ r + k ≤ i.val then 2 * (i.val : ℤ) - (2 * r + k) else 0 := by
  unfold bq
  by_cases h : outer k r i
  · rw [if_pos h, if_pos (show i.val ≤ r ∨ r + k ≤ i.val from h)]
  · rw [if_neg h, if_neg (show ¬ (i.val ≤ r ∨ r + k ≤ i.val) from h)]

theorem adapted_pq (k r : ℕ) : Adapted (pq k r) (bq k r) (fun _ => 1) := by
  constructor
  · intro i
    apply Fin.ext
    have := i.2
    rw [pq_val, pq_val]
    split_ifs <;> omega
  · intro i j hij
    rw [bq_eq, bq_eq]
    split_ifs <;> omega
  · intro i
    have := i.2
    rw [bq_eq, bq_eq, pq_val]
    split_ifs <;> omega
  · intro i hi
    apply Fin.ext
    have := i.2
    rw [bq_eq] at hi
    rw [pq_val]
    split_ifs at hi ⊢ <;> omega
  · intro i j hi hij
    apply Fin.ext
    rw [bq_eq] at hi
    rw [bq_eq, bq_eq] at hij
    split_ifs at hi hij <;> omega
  · intro i
    simp
  · intro i
    simp
  · intros
    rfl
  · intros
    rfl

theorem Hq_eq_dp (k r : ℕ) : Hq k r = dp (pq k r) 0 (fun _ => 1) := by
  ext i j
  have hi := i.2
  simp only [Hq, dp, Matrix.of_apply, Pi.zero_apply, ite_self, zero_add, Fin.ext_iff, pq_val]
  by_cases h : outer k r i
  · rw [if_pos h, if_pos (show i.val ≤ r ∨ r + k ≤ i.val from h)]
    exact if_congr (by omega) rfl rfl
  · rw [if_neg h, if_neg (show ¬ (i.val ≤ r ∨ r + k ≤ i.val) from h)]
    exact if_congr eq_comm rfl rfl

theorem iwaQ : IwaQ := by
  intro k r _ x hx
  have hx' : xᴴ * Hq k r * x = Hq k r := hx
  rw [Hq_eq_dp] at hx'
  obtain ⟨s, κ, hs, hκ, h1, h2, h3⟩ := adapted_dec_left (adapted_pq k r) x hx'
  rw [← Hq_eq_dp] at hs hκ
  exact ⟨s, hs, κ, hκ, h1, h2, h3⟩

end GlobalTheory.CompanionTheory.BmuIwa
end
end

section

open Finset

namespace GlobalTheory.CompanionTheory.DSHighestOfKType

open Formalism.REAL (GlRel KHighest IsWeight)
open PI.UpqRep (CDom root)

variable {n : ℕ}

theorem height_root (a b : Fin n) : ∑ i : Fin n, ((i : ℕ) : ℝ) * root a b i = ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ) := by
  simp [root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]

theorem not_cdom_add_root (ε : Fin n → Bool) (μ : Fin n → ℝ) {a b : Fin n} (hab : a < b) :
    ¬ CDom ε (μ + root a b) μ := by
  rintro ⟨c, hc, h⟩
  have h1 : ∑ i : Fin n, ((i : ℕ) : ℝ) * (μ - (μ + root a b)) i = ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) := by
    have : ∀ i : Fin n, ((i : ℕ) : ℝ) * (μ - (μ + root a b)) i = -(((i : ℕ) : ℝ) * root a b i) := by
      intro i; simp
    simp only [this, Finset.sum_neg_distrib, height_root]; ring
  have h2 : ∑ i : Fin n, ((i : ℕ) : ℝ) * (∑ x, ∑ y, (c x y : ℝ) • root x y) i
      = ∑ x, ∑ y, (c x y : ℝ) * (((x : ℕ) : ℝ) - ((y : ℕ) : ℝ)) := by
    simp only [← height_root, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have h3 : ∑ x, ∑ y, (c x y : ℝ) * (((x : ℕ) : ℝ) - ((y : ℕ) : ℝ)) ≤ 0 := by
    refine Finset.sum_nonpos fun x _ => Finset.sum_nonpos fun y _ => ?_
    by_cases h0 : c x y = 0
    · simp [h0]
    · have hxy : ((x : ℕ) : ℝ) < ((y : ℕ) : ℝ) := by exact_mod_cast (hc x y h0).1
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
  have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  rw [h, h2] at h1
  linarith

theorem isWeight_apply {V : Type} [AddCommGroup V] [Module ℂ V] {E : Fin n → Fin n → Module.End ℂ V}
    (hE : GlRel E) {μ : Fin n → ℝ} {v : V} (hv : IsWeight E μ v) (a b : Fin n) :
    IsWeight E (μ + root a b) (E a b v) := by
  intro c
  have h := LinearMap.congr_fun (hE c c a b) v
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hv c, map_smul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  by_cases h1 : c = a <;> by_cases h2 : b = c
  · subst h1; subst h2; simp [root]
  · subst h1; simp [root, h2, Ne.symm h2, add_smul, add_comm]
  · subst h2; simp [root, h1, add_smul, add_comm]
  · simp [root, h1, h2, Ne.symm h2]

theorem hwOfType : CompanionTheory.D.DSIC.StabLink → CompanionTheory.D.DSIC.WtLink → CompanionTheory.D.DSIC.HWofType := by
  intro hS hW n ε H _ _ σ S E hσ hm μ T hT hTS
  obtain ⟨hfin, hst, -, ⟨v, hvT, hv0, hvw⟩, hdom⟩ := hT
  have hmap : (T.comap S.subtype).map S.subtype = T := by
    rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr hTS
  have hfinU : FiniteDimensional ℂ (T.comap S.subtype) :=
    (Submodule.comapSubtypeEquivOfLe hTS).symm.finiteDimensional
  have hU := (hS n ε H σ S E hσ hm _ hfinU).2 (by rw [hmap]; exact hst)
  have hw : IsWeight E μ (⟨v, hTS hvT⟩ : S) := (hW n ε H σ S E hσ hm μ _).2 hvw
  refine ⟨⟨v, hTS hvT⟩, fun h => hv0 (congrArg Subtype.val h), hvT, hw, fun a b hab hε => ?_⟩
  by_contra hne
  have hmem := hU a b hε ⟨v, hTS hvT⟩ hvT
  have hw' := (hW n ε H σ S E hσ hm _ _).1 (isWeight_apply hm.gl hw a b)
  exact not_cdom_add_root ε μ hab (hdom _ _ hmem (fun h => hne (Subtype.ext h)) hw')

end GlobalTheory.CompanionTheory.DSHighestOfKType
end
