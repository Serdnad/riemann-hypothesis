module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle040
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle043
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle049
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle003
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

theorem _root_.GlobalTheory.T.lowerBoundConst_at_large_multiple_numerical_bounds : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 CL : ℝ) (N del : ℕ), InR D j → PageOK large₂ X H C2 A2 CT ka wL wF Tn nP nW h0 → 0 < CL → 0 < N → 0 < del → Real.log N ≤ nbR large₂ wL → Real.log del ≤ 1041 * Zb D large₂ ^ 3 → LamConst j large₂ CL 2 (wsmul (8 * ((WeightFamilies.dimY D j + 2) * N) ^ 2 * (WeightFamilies.dimY D j + 1) * del * (1 + ⌈PO D large₂⌉₊)) wL) (lamR large₂ CL wL) (8 * ((WeightFamilies.dimY D j + 2) * N) ^ 2 * (WeightFamilies.dimY D j + 1) * del * (1 + ⌈PO D large₂⌉₊)) wL.size ∧ 3 ≤ WeightFamilies.dimY D j ∧ wL.n = nW ∧ 0 < wL.n ∧ (DF wL : ℝ) ≤ wL.size ∧ 2 ≤ wL.size ∧ 1 ≤ PO D large₂ ∧ 1 ≤ zBase large₂ ∧ cc D large₂ C2 A2 7 wL * (g0 D : ℝ) ≤ 1 / 2 ∧ PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2) ≤ max 1 (PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2)) := by
  first | exact @GlobalTheory.RunJoin.lamConst_lamR_rows | exact GlobalTheory.RunJoin.lamConst_lamR_rows | (intros; apply GlobalTheory.RunJoin.lamConst_lamR_rows <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

theorem _root_.GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces : ∀ D : D7, (∀ θ θ' : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), IsInfFam θ → IsInfFam θ' → θ = θ') ∧ ∀ θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), IsInfFam θ → ∀ V : HSp D, RealPoints θ V := by
  first | exact @GlobalTheory.SmoothForms.RealPts.realPoints | exact GlobalTheory.SmoothForms.RealPts.realPoints | (intros; apply GlobalTheory.SmoothForms.RealPts.realPoints <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos


theorem _root_.GlobalTheory.T.rightDerivativeRelation_of_locallyUniformLimit : ∀ (n : ℕ) (ε : Fin n → Bool) (F : Mx n → ℂ), CSm ε F → ∀ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List (Ltr ε)),
    (∀ C : Set (Mx n), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ f : Mx n → ℂ, CSm ε f ∧
      (∀ y ∈ C, y ∈ UJset ε → ‖F y - f y‖ < δ) ∧ ∀ y ∈ UJset ε, ∑ i, c i * wordF (u i) f y = 0) →
    ∀ y ∈ UJset ε, ∑ i, c i * wordF (u i) F y = 0 := by
  intro n ε F hF m c u hlim y hy
  have hmem : ∀ g : UJ ε, umat g ∈ UJset ε := fun g => g.2
  have hcont : Continuous fun g : UJ ε => ∑ i, c i * wordF (u i) F (umat g) := by
    refine continuous_finsetSum _ (fun i _ => ?_)
    exact continuous_const.mul (CSm.continuous (CSm.wordF hF (u i)))
  have key : ∀ φ, IsTest ε φ →
      ∫ g : UJ ε, φ (umat g) * ∑ i, c i * wordF (u i) F (umat g) ∂(muG ε) = 0 := by
    intro φ hφ
    choose ψ hψ hadj using fun i => exists_adjoint_word (u i) hφ

    have expand : ∀ G, CSm ε G →
        ∫ g : UJ ε, φ (umat g) * ∑ i, c i * wordF (u i) G (umat g) ∂(muG ε)
          = ∑ i, c i * ∫ g : UJ ε, ψ i (umat g) * G (umat g) ∂(muG ε) := by
      intro G hG
      have hfun : (fun g : UJ ε => φ (umat g) * ∑ i, c i * wordF (u i) G (umat g))
          = fun g => ∑ i, c i * (φ (umat g) * wordF (u i) G (umat g)) := by
        funext g
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [hfun, MeasureTheory.integral_finsetSum]
      · refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [MeasureTheory.integral_const_mul, hadj i G hG]
      · intro i _
        exact (IsTest.integrable hφ (CSm.wordF hG (u i))).const_mul (c i)
    have h1 : CSm ε (fun _ : Mx n => (1 : ℂ)) := cSm_of_contDiff _ contDiff_const
    have hint1 : ∀ i, MeasureTheory.Integrable (fun g : UJ ε => ‖ψ i (umat g)‖) (muG ε) := by
      intro i
      simpa using (IsTest.integrable (hψ i) h1).norm
    set A : Fin m → ℝ := fun i => ∫ g : UJ ε, ‖ψ i (umat g)‖ ∂(muG ε) with hA
    set B : ℝ := ∑ i, ‖c i‖ * A i with hB
    have hA0 : ∀ i, 0 ≤ A i := fun i => MeasureTheory.integral_nonneg (fun g => norm_nonneg _)
    have hB0 : 0 ≤ B := Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (hA0 i))
    set X := ∫ g : UJ ε, φ (umat g) * ∑ i, c i * wordF (u i) F (umat g) ∂(muG ε) with hX

    have bound : ∀ δ : ℝ, 0 < δ → ‖X‖ ≤ δ * B := by
      intro δ hδ
      let K : Set (UJ ε) := ⋃ i, tsupport (fun g : UJ ε => ψ i (umat g))
      have hK : IsCompact K := isCompact_iUnion (fun i => (hψ i).2.isCompact)
      have hC : IsCompact ((fun g : UJ ε => umat g) '' K) := hK.image (umat_emb ε).continuous
      obtain ⟨f, hf, hclose, hzero⟩ := hlim _ hC δ hδ
      have e0 : ∑ i, c i * ∫ g : UJ ε, ψ i (umat g) * f (umat g) ∂(muG ε) = 0 := by
        rw [← expand f hf]
        have hz : (fun g : UJ ε => φ (umat g) * ∑ i, c i * wordF (u i) f (umat g)) = fun _ => 0 := by
          funext g
          rw [hzero _ (hmem g), mul_zero]
        rw [hz, MeasureTheory.integral_zero]
      have hXf : X = ∑ i, c i * ((∫ g : UJ ε, ψ i (umat g) * F (umat g) ∂(muG ε))
          - ∫ g : UJ ε, ψ i (umat g) * f (umat g) ∂(muG ε)) := by
        rw [hX, expand F hF]
        simp only [mul_sub, Finset.sum_sub_distrib, e0, sub_zero]
      rw [hXf]
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum (fun i _ => ?_ : ∀ i ∈ Finset.univ, _ ≤ ‖c i‖ * (δ * A i))).trans
        (le_of_eq ?_)
      · rw [norm_mul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        show _ ≤ δ * ∫ g : UJ ε, ‖ψ i (umat g)‖ ∂(muG ε)
        rw [← MeasureTheory.integral_sub (IsTest.integrable (hψ i) hF) (IsTest.integrable (hψ i) hf),
          ← MeasureTheory.integral_const_mul]
        refine MeasureTheory.norm_integral_le_of_norm_le ((hint1 i).const_mul δ)
          (Filter.Eventually.of_forall (fun g => ?_))
        rw [← mul_sub, norm_mul]
        by_cases hg : g ∈ tsupport (fun g : UJ ε => ψ i (umat g))
        · have hgC : umat g ∈ (fun g : UJ ε => umat g) '' K := ⟨g, Set.mem_iUnion.2 ⟨i, hg⟩, rfl⟩
          rw [mul_comm δ]
          exact mul_le_mul_of_nonneg_left (hclose _ hgC (hmem g)).le (norm_nonneg _)
        · have h0 : ψ i (umat g) = 0 :=
            image_eq_zero_of_notMem_tsupport (f := fun g : UJ ε => ψ i (umat g)) hg
          rw [h0]
          simp
      · rw [hB, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
    by_contra hne
    have hpos : 0 < ‖X‖ := norm_pos_iff.2 hne
    have hle := bound (‖X‖ / (B + 1)) (div_pos hpos (by linarith))
    have hlt : ‖X‖ / (B + 1) * B < ‖X‖ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  have h := eq_zero_of_test (fun g : UJ ε => ∑ i, c i * wordF (u i) F (umat g)) hcont key (mkU y hy)
  simpa [umat_mkU] using h
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

namespace GlobalTheory.TypeSum.CasBasisFacts

variable {n : ℕ}

lemma inG_iff_entry (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inG ε X ↔ ∀ i j, star (X j i) * (if ε j = true then (1:ℂ) else -1) +
      (if ε i = true then (1:ℂ) else -1) * X i j = 0 := by
  unfold inG Jm
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    simpa [mul_diagonal, diagonal_mul, conjTranspose_apply] using this
  · intro h
    ext i j
    simpa [mul_diagonal, diagonal_mul, conjTranspose_apply] using h i j

lemma i_smul_diag_casimir_unit_mem_indefinite_lie (ε : Fin n → Bool) (a : Fin n) : inG ε (Complex.I • unitE a a) := by
  rw [inG_iff_entry]
  intro i j
  simp only [unitE, invSqrtTwo, Matrix.single_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
  split_ifs <;> simp_all <;> grind

lemma same_sign_casimir_skew_sum_mem_indefinite_lie (ε : Fin n → Bool) (a b : Fin n) (hab : a ≠ b) (he : ε a = ε b) :
    inG ε (invSqrtTwo • (unitE a b - unitE b a)) := by
  rw [inG_iff_entry]
  intro i j
  simp only [unitE, invSqrtTwo, Matrix.single_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
  split_ifs <;> simp_all

lemma same_sign_casimir_i_sym_sum_mem_indefinite_lie (ε : Fin n → Bool) (a b : Fin n) (hab : a ≠ b) (he : ε a = ε b) :
    inG ε ((invSqrtTwo * Complex.I) • (unitE a b + unitE b a)) := by
  rw [inG_iff_entry]
  intro i j
  simp only [unitE, invSqrtTwo, Matrix.single_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
  split_ifs <;> simp_all

lemma opp_sign_casimir_sym_sum_mem_indefinite_lie (ε : Fin n → Bool) (a b : Fin n) (hab : a ≠ b) (he : ε a ≠ ε b) :
    inG ε (invSqrtTwo • (unitE a b + unitE b a)) := by
  rw [inG_iff_entry]
  intro i j
  simp only [unitE, invSqrtTwo, Matrix.single_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
  split_ifs <;> simp_all

lemma opp_sign_casimir_i_skew_sum_mem_indefinite_lie (ε : Fin n → Bool) (a b : Fin n) (hab : a ≠ b) (he : ε a ≠ ε b) :
    inG ε ((invSqrtTwo * Complex.I) • (unitE a b - unitE b a)) := by
  rw [inG_iff_entry]
  intro i j
  simp only [unitE, invSqrtTwo, Matrix.single_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
  split_ifs <;> simp_all

lemma i_smul_diag_casimir_unit_skewHermitian (a : Fin n) : (Complex.I • unitE a a)ᴴ = -(Complex.I • unitE a a) := by
  simp [unitE, Matrix.conjTranspose_single]
  ext i j
  simp [Matrix.single_apply]
  split_ifs <;> simp

lemma casimir_unit_skew_diff_skewHermitian (a b : Fin n) :
    (invSqrtTwo • (unitE a b - unitE b a))ᴴ = -(invSqrtTwo • (unitE a b - unitE b a)) := by
  simp [unitE, invSqrtTwo, Matrix.conjTranspose_single]
  module

lemma casimir_unit_i_sym_sum_skewHermitian (a b : Fin n) :
    ((invSqrtTwo * Complex.I) • (unitE a b + unitE b a))ᴴ =
      -((invSqrtTwo * Complex.I) • (unitE a b + unitE b a)) := by
  simp [unitE, invSqrtTwo, Matrix.conjTranspose_single]
  ext i j
  simp [Matrix.single_apply]
  split_ifs <;> simp

lemma casimir_unit_sym_sum_hermitian (a b : Fin n) :
    (invSqrtTwo • (unitE a b + unitE b a))ᴴ = invSqrtTwo • (unitE a b + unitE b a) := by
  simp [unitE, invSqrtTwo, Matrix.conjTranspose_single, add_comm]

lemma casimir_unit_i_skew_diff_hermitian (a b : Fin n) :
    ((invSqrtTwo * Complex.I) • (unitE a b - unitE b a))ᴴ =
      (invSqrtTwo * Complex.I) • (unitE a b - unitE b a) := by
  simp [unitE, invSqrtTwo, Matrix.conjTranspose_single]
  module

lemma i_smul_diag_casimir_unit_hs_le_one (a : Fin n) : hs (Complex.I • unitE a a) ≤ 1 := by
  unfold hs
  have : ∀ i j, ‖(Complex.I • unitE a a) i j‖ ^ 2 = if a = i then (if a = j then 1 else 0) else 0 := by
    intro i j
    simp only [unitE, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    split_ifs <;> simp_all
  simp only [this]
  simp

lemma pair_hs (a b : Fin n) (hab : a ≠ b) (c : ℂ) (hc : ‖c‖ ^ 2 = 1 / 2) (t : ℂ) (ht : ‖t‖ = 1) :
    hs (c • (unitE a b + t • unitE b a)) ≤ 1 := by
  unfold hs
  have : ∀ i j, ‖(c • (unitE a b + t • unitE b a)) i j‖ ^ 2 =
      (if a = i then (if b = j then 1 / 2 else 0) else 0) +
        (if b = i then (if a = j then 1 / 2 else 0) else 0) := by
    intro i j
    simp only [unitE, Matrix.smul_apply, Matrix.add_apply, Matrix.single_apply, smul_eq_mul]
    split_ifs <;> simp_all [norm_mul, mul_pow]
  simp only [this]
  simp [Finset.sum_add_distrib]
  norm_num

lemma norm_sq_invSqrtTwo : ‖invSqrtTwo‖ ^ 2 = 1 / 2 := by
  simp [invSqrtTwo, norm_inv, inv_pow]

lemma casimir_unit_skew_diff_hs_le_one (a b : Fin n) (hab : a ≠ b) : hs (invSqrtTwo • (unitE a b - unitE b a)) ≤ 1 := by
  have e : unitE a b - unitE b a = unitE a b + (-1 : ℂ) • unitE b a := by
    simp [sub_eq_add_neg]
  rw [e]
  exact pair_hs a b hab _ norm_sq_invSqrtTwo _ (by simp)

lemma casimir_unit_i_sym_sum_hs_le_one (a b : Fin n) (hab : a ≠ b) :
    hs ((invSqrtTwo * Complex.I) • (unitE a b + unitE b a)) ≤ 1 := by
  have e : unitE a b + unitE b a = unitE a b + (1 : ℂ) • unitE b a := by simp
  rw [e]
  exact pair_hs a b hab _ (by rw [norm_mul, mul_pow, norm_sq_invSqrtTwo]; simp) _ (by simp)

lemma mem_pairs {ε : Fin n → Bool} {same : Bool} {a b : Fin n} (h : (a, b) ∈ pairs ε same) :
    a ≠ b ∧ ((ε a = ε b) ↔ same = true) := by
  simp only [pairs, List.mem_filter, List.pair_mem_product, List.mem_finRange, true_and,
    Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨ne_of_lt h.1, ?_⟩
  have h2 := h.2
  cases same <;> cases hx : ε a <;> cases hy : ε b <;> simp_all

end GlobalTheory.TypeSum.CasBasisFacts


open GlobalTheory.TypeSum.CasBasisFacts in
theorem GlobalTheory.TypeSum.CasBasis.bases_mem_lie : ∀ (n : ℕ) (ε : Fin n → Bool),
    (∀ i, kB ε i ∈ lieSet ε ∧ (kB ε i)ᴴ = -kB ε i ∧ hs (kB ε i) ≤ 1) ∧
      ∀ b, pB ε b ∈ lieSet ε ∧ (pB ε b)ᴴ = pB ε b := by
  intro n ε
  constructor
  · intro i
    have hm : kB ε i ∈ kList ε := List.get_mem _ _
    generalize kB ε i = X at hm ⊢
    simp only [kList, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons,
      List.not_mem_nil, or_false] at hm
    rcases hm with ⟨a, -, rfl⟩ | ⟨⟨a, b⟩, hp, rfl | rfl⟩
    · exact ⟨i_smul_diag_casimir_unit_mem_indefinite_lie ε a, i_smul_diag_casimir_unit_skewHermitian a, i_smul_diag_casimir_unit_hs_le_one a⟩
    · obtain ⟨hab, he⟩ := mem_pairs hp
      exact ⟨same_sign_casimir_skew_sum_mem_indefinite_lie ε a b hab (he.2 rfl), casimir_unit_skew_diff_skewHermitian a b, casimir_unit_skew_diff_hs_le_one a b hab⟩
    · obtain ⟨hab, he⟩ := mem_pairs hp
      exact ⟨same_sign_casimir_i_sym_sum_mem_indefinite_lie ε a b hab (he.2 rfl), casimir_unit_i_sym_sum_skewHermitian a b, casimir_unit_i_sym_sum_hs_le_one a b hab⟩
  · intro i
    have hm : pB ε i ∈ pList ε := List.get_mem _ _
    generalize pB ε i = X at hm ⊢
    simp only [pList, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨⟨a, b⟩, hp, rfl | rfl⟩
    · obtain ⟨hab, he⟩ := mem_pairs hp
      exact ⟨opp_sign_casimir_sym_sum_mem_indefinite_lie ε a b hab (fun h => by simpa using he.1 h), casimir_unit_sym_sum_hermitian a b⟩
    · obtain ⟨hab, he⟩ := mem_pairs hp
      exact ⟨opp_sign_casimir_i_skew_sum_mem_indefinite_lie ε a b hab (fun h => by simpa using he.1 h), casimir_unit_i_skew_diff_hermitian a b⟩
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

noncomputable section
namespace GlobalTheory.TypeSum.CasBasis
variable {n : ℕ} {ε : Fin n → Bool}

theorem mem_lieSet_iff_entry {X : Mx n} : X ∈ lieSet ε ↔
    ∀ i j, star (X j i) * (if ε j then 1 else -1) + (if ε i then 1 else -1) * X i j = 0 := by
  simp only [lieSet, Set.mem_setOf_eq, inG, Jm]
  rw [← Matrix.ext_iff]
  simp [mul_diagonal, diagonal_mul, conjTranspose_apply]

theorem smul_unitE_diag_mem (a : Fin n) {c : ℂ} (hc : star c = -c) : c • unitE a a ∈ lieSet ε := by
  rw [mem_lieSet_iff_entry]
  intro i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, unitE, single_apply, smul_eq_mul, star_mul', hc,
    star_sub, star_add]
  split_ifs <;> simp only [star_one, star_zero] at * <;> grind

theorem smul_unitE_sub_mem_same {a b : Fin n} (h : ε a = ε b) {c : ℂ} (hc : star c = c) :
    c • (unitE a b - unitE b a) ∈ lieSet ε := by
  rw [mem_lieSet_iff_entry]
  intro i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, unitE, single_apply, smul_eq_mul, star_mul', hc,
    star_sub, star_add]
  split_ifs <;> simp only [star_one, star_zero] at * <;> grind

theorem smul_unitE_add_mem_same {a b : Fin n} (h : ε a = ε b) {c : ℂ} (hc : star c = -c) :
    c • (unitE a b + unitE b a) ∈ lieSet ε := by
  rw [mem_lieSet_iff_entry]
  intro i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, unitE, single_apply, smul_eq_mul, star_mul', hc,
    star_sub, star_add]
  split_ifs <;> simp only [star_one, star_zero] at * <;> grind

theorem smul_unitE_add_mem_opp {a b : Fin n} (h : ε a ≠ ε b) {c : ℂ} (hc : star c = c) :
    c • (unitE a b + unitE b a) ∈ lieSet ε := by
  rw [mem_lieSet_iff_entry]
  intro i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, unitE, single_apply, smul_eq_mul, star_mul', hc,
    star_sub, star_add]
  split_ifs <;> simp only [star_one, star_zero] at * <;> grind

theorem smul_unitE_sub_mem_opp {a b : Fin n} (h : ε a ≠ ε b) {c : ℂ} (hc : star c = -c) :
    c • (unitE a b - unitE b a) ∈ lieSet ε := by
  rw [mem_lieSet_iff_entry]
  intro i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, unitE, single_apply, smul_eq_mul, star_mul', hc,
    star_sub, star_add]
  split_ifs <;> simp only [star_one, star_zero] at * <;> grind

theorem star_invSqrtTwo : star invSqrtTwo = invSqrtTwo := by
  simp [invSqrtTwo]

theorem star_invSqrtTwo_mul_I : star (invSqrtTwo * Complex.I) = -(invSqrtTwo * Complex.I) := by
  simp [invSqrtTwo]

theorem kList_mem_lieSet {X : Mx n} (hX : X ∈ kList ε) : X ∈ lieSet ε := by
  simp only [kList, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at hX
  rcases hX with ⟨a, -, rfl⟩ | ⟨p, hp, hX⟩
  · exact smul_unitE_diag_mem a (by simp [Complex.star_def])
  · have hs : ε p.1 = ε p.2 := by
      simp [pairs] at hp
      exact hp.2.2
    rcases hX with rfl | rfl
    · exact smul_unitE_sub_mem_same hs star_invSqrtTwo
    · exact smul_unitE_add_mem_same hs star_invSqrtTwo_mul_I

theorem pList_mem_lieSet {X : Mx n} (hX : X ∈ pList ε) : X ∈ lieSet ε := by
  simp only [pList, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hX
  obtain ⟨p, hp, hX⟩ := hX
  have hs : ε p.1 ≠ ε p.2 := by
    simp [pairs] at hp
    exact hp.2.2
  rcases hX with rfl | rfl
  · exact smul_unitE_add_mem_opp hs star_invSqrtTwo
  · exact smul_unitE_sub_mem_opp hs star_invSqrtTwo_mul_I

theorem bases_mem_lieSet : ∀ (n : ℕ) (ε : Fin n → Bool), (∀ i, kB ε i ∈ lieSet ε) ∧ ∀ b, pB ε b ∈ lieSet ε :=
  fun _ _ => ⟨fun i => kList_mem_lieSet (List.get_mem _ i), fun b => pList_mem_lieSet (List.get_mem _ b)⟩

end GlobalTheory.TypeSum.CasBasis
end
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined

namespace GlobalTheory.TypeSum.CasBasis

theorem unitE_apply_eq_zero_of_sign {n : ℕ} {ε : Fin n → Bool} {i j a b : Fin n}
    (h : (ε i = ε j) ≠ (ε a = ε b)) : unitE i j a b = 0 := by
  rw [unitE, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact h rfl

theorem kList_entry_zero {n : ℕ} {ε : Fin n → Bool} {X : Mx n} (hX : X ∈ kList ε) {a b : Fin n}
    (hab : ε a ≠ ε b) : X a b = 0 := by
  unfold kList at hX
  rcases List.mem_append.1 hX with h | h
  · obtain ⟨c, -, rfl⟩ := List.mem_map.1 h
    have h1 : unitE c c a b = 0 :=
      unitE_apply_eq_zero_of_sign (ε := ε) (by simp [hab])
    simp only [Matrix.smul_apply, h1, smul_zero]
  · obtain ⟨p, hp, hX⟩ := List.mem_flatMap.1 h
    have hpe : ε p.1 = ε p.2 := by
      have := (List.mem_filter.1 hp).2
      simp at this
      exact this.2
    have h1 : unitE p.1 p.2 a b = 0 :=
      unitE_apply_eq_zero_of_sign (ε := ε) (by simp [hab, hpe])
    have h2 : unitE p.2 p.1 a b = 0 :=
      unitE_apply_eq_zero_of_sign (ε := ε) (by simp [hab, hpe])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl <;>
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, h1, h2, sub_zero, add_zero, smul_zero]

theorem pList_entry_zero {n : ℕ} {ε : Fin n → Bool} {Y : Mx n} (hY : Y ∈ pList ε) {a b : Fin n}
    (hab : ε a = ε b) : Y a b = 0 := by
  unfold pList at hY
  obtain ⟨p, hp, hY⟩ := List.mem_flatMap.1 hY
  have hpe : ε p.1 ≠ ε p.2 := by
    have := (List.mem_filter.1 hp).2
    simp at this
    exact this.2
  have h1 : unitE p.1 p.2 a b = 0 :=
    unitE_apply_eq_zero_of_sign (ε := ε) (by simp [hab, hpe])
  have h2 : unitE p.2 p.1 a b = 0 :=
    unitE_apply_eq_zero_of_sign (ε := ε) (by simp [hab, Ne.symm hpe])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hY
  rcases hY with rfl | rfl <;>
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, h1, h2, sub_zero, add_zero, smul_zero]

theorem re_trace_kB_mul_pB : ∀ (n : ℕ) (ε : Fin n → Bool) (i : Fin (kList ε).length) (b : Fin (pList ε).length),
    (trace (kB ε i * pB ε b)).re = 0 := by
  intro n ε i b
  have hX : kB ε i ∈ kList ε := List.get_mem _ _
  have hY : pB ε b ∈ pList ε := List.get_mem _ _
  have : trace (kB ε i * pB ε b) = 0 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => ?_
    by_cases h : ε a = ε c
    · rw [pList_entry_zero hY h.symm, mul_zero]
    · rw [kList_entry_zero hX h, zero_mul]
  rw [this, Complex.zero_re]

end GlobalTheory.TypeSum.CasBasis
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.KFourier


theorem _root_.GlobalTheory.T.eq_zero_of_orthogonal_compactUnitaryPolyFun : ∀ {n : ℕ} (ε : Fin n → Bool) (h : KG ε → ℂ), Continuous h → (∀ d, ∀ q ∈ GlobalTheory.KFourier.polyV ε d, ∫ k, star (q k) * h k ∂(muK ε) = 0) → h = 0 := by
  first | exact @GlobalTheory.KFourier.eq_zero_of_orth_poly | exact GlobalTheory.KFourier.eq_zero_of_orth_poly | (intros; apply GlobalTheory.KFourier.eq_zero_of_orth_poly <;> assumption)
end
