module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReciprocityTheory.DualLattices.Bundle001
public import Mathlib.FieldTheory.Perfect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle183
public import Mathlib.FieldTheory.Separable
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle004
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.OreLocalization.Ring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle216
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
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
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle120
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtOrderProdSub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory

noncomputable section

variable {C : Type} [Field C]

theorem powRow_nonneg_of_nsmul {a : WithTop ℝ} {N : ℕ} (hN : N ≠ 0) (h : 0 ≤ N • a) : 0 ≤ a := by
  cases a with
  | top => exact le_top
  | coe r =>
    have e : ((N • r : ℝ) : WithTop ℝ) = N • (r : WithTop ℝ) := WithTop.coe_nsmul _ _
    rw [← e] at h
    have h' : (0 : ℝ) ≤ N • r := by exact_mod_cast h
    rw [nsmul_eq_mul] at h'
    have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    have : 0 ≤ r := by
      by_contra hr
      push Not at hr
      nlinarith
    exact_mod_cast this

theorem powRow_int_root [IsAlgClosed C] (v : AddValuation C (WithTop ℝ)) {N : ℕ} (hN : 0 < N)
    (y : C) (hy : IsIntV v y) : ∃ x, x ^ N = y ∧ IsIntV v x := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y hN
  refine ⟨x, hx, powRow_nonneg_of_nsmul hN.ne' ?_⟩
  rw [← AddValuation.map_pow, hx]
  exact hy

theorem powRow_int_of_le (v : AddValuation C (WithTop ℝ)) {a b : C} (hb : b ≠ 0)
    (h : v b ≤ v (a * b)) : IsIntV v a := by
  unfold IsIntV
  rw [AddValuation.map_mul] at h
  have hb' : v b ≠ ⊤ := (v.ne_top_iff).2 hb
  cases hvb : v b with
  | top => exact absurd hvb hb'
  | coe r =>
    rw [hvb] at h
    cases hva : v a with
    | top => exact le_top
    | coe s =>
      rw [hva] at h
      have h2 : r ≤ s + r := by exact_mod_cast h
      exact_mod_cast (by linarith : (0 : ℝ) ≤ s)

theorem powRow_v_neg_one_pow (v : AddValuation C (WithTop ℝ)) (k : ℕ) : v ((-1 : C) ^ k) = 0 := by
  rw [AddValuation.map_pow, AddValuation.map_neg, AddValuation.map_one, smul_zero]

theorem powRow_exists [IsAlgClosed C] (v : AddValuation C (WithTop ℝ)) {V : Type} [AddCommGroup V]
    [Module C V] (N : ℕ) (hN : 0 < N) (j : ℕ) : ∀ (m : ℕ) (z : Fin m → V),
    Module.finrank C (Submodule.span C (Set.range z)) ≤ j →
    ∃ x : Matrix (Fin m) (Fin m) C, (∀ w u, IsIntV v (x w u)) ∧ v x.det = 0 ∧
      ∀ w : Fin m, j ≤ w.val → ∑ u, (x w u) ^ N • z u = 0 := by
  intro m
  induction m with
  | zero =>
    intro z _
    exact ⟨1, fun w => w.elim0, by simp, fun w => w.elim0⟩
  | succ m ih =>
    intro z hz
    by_cases hli : LinearIndependent C z
    · have hmj : m + 1 ≤ j := by
        have := finrank_span_eq_card hli
        simp only [Fintype.card_fin] at this
        omega
      refine ⟨1, ?_, by simp [AddValuation.map_one], fun w hw => absurd hw (by omega)⟩
      intro w u
      unfold IsIntV
      rw [Matrix.one_apply]
      split_ifs <;> simp
    · obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hli
      obtain ⟨u0, -, hu0⟩ := Finset.exists_min_image Finset.univ (fun u => v (g u))
        ⟨i, Finset.mem_univ _⟩
      have hg0 : g u0 ≠ 0 := by
        intro h0
        apply hi
        have := hu0 i (Finset.mem_univ _)
        rw [h0, AddValuation.map_zero] at this
        exact (v.top_iff).1 (top_le_iff.1 this)
      set c : Fin (m + 1) → C := fun u => g u / g u0 with hc
      have hc0 : c u0 = 1 := div_self hg0
      have hcint : ∀ u, IsIntV v (c u) := by
        intro u
        apply powRow_int_of_le v hg0
        have : c u * g u0 = g u := div_mul_cancel₀ _ hg0
        rw [this]
        exact hu0 u (Finset.mem_univ _)
      have hcz : ∑ u, c u • z u = 0 := by
        have : ∑ u, c u • z u = (g u0)⁻¹ • ∑ u, g u • z u := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [smul_smul, hc]
          simp only [div_eq_mul_inv, mul_comm]
        rw [this, hg, smul_zero]
      choose r hr hrint using fun u => powRow_int_root v hN (c u) (hcint u)
      set r' : Fin (m + 1) → C := Function.update r u0 1 with hr'
      have hr'N : ∀ u, r' u ^ N = c u := by
        intro u
        by_cases hu : u = u0
        · subst hu; rw [hr', Function.update_self, one_pow, hc0]
        · rw [hr', Function.update_of_ne hu, hr]
      have hr'int : ∀ u, IsIntV v (r' u) := by
        intro u
        by_cases hu : u = u0
        · subst hu; rw [hr', Function.update_self]; unfold IsIntV; rw [AddValuation.map_one]
        · rw [hr', Function.update_of_ne hu]; exact hrint u
      have hz' : Module.finrank C (Submodule.span C (Set.range (z ∘ u0.succAbove))) ≤ j := by
        have : Module.Finite C (Submodule.span C (Set.range z)) :=
          Module.Finite.span_of_finite C (Set.finite_range z)
        refine le_trans (Submodule.finrank_mono (Submodule.span_mono ?_)) hz
        rintro _ ⟨k, rfl⟩
        exact ⟨_, rfl⟩
      obtain ⟨x', hx'int, hx'det, hx'k⟩ := ih (z ∘ u0.succAbove) hz'
      let A : Matrix (Fin (m + 1)) (Fin (m + 1)) C :=
        Matrix.of (Fin.snoc (fun w' => Fin.insertNth (α := fun _ => C) u0 0 (x' w')) r')
      have hAlast : ∀ u, A (Fin.last m) u = r' u := by
        intro u; simp [A, Fin.snoc_last]
      have hAcs : ∀ w' u, A w'.castSucc u = Fin.insertNth (α := fun _ => C) u0 0 (x' w') u := by
        intro w' u; simp [A, Fin.snoc_castSucc]
      refine ⟨A, ?_, ?_, ?_⟩
      · intro w u
        induction w using Fin.lastCases with
        | last => rw [hAlast]; exact hr'int u
        | cast w' =>
          rw [hAcs]
          induction u using Fin.succAboveCases u0 with
          | x =>
            rw [Fin.insertNth_apply_same]; unfold IsIntV; rw [AddValuation.map_zero]; exact le_top
          | p k => rw [Fin.insertNth_apply_succAbove]; exact hx'int w' k
      · rw [Matrix.det_succ_column A u0]
        rw [Fintype.sum_eq_single (Fin.last m)]
        · have hsub : A.submatrix (Fin.last m).succAbove u0.succAbove = x' := by
            ext w' k
            simp only [Matrix.submatrix_apply, Fin.succAbove_last]
            rw [hAcs, Fin.insertNth_apply_succAbove]
          rw [hsub, hAlast]
          rw [AddValuation.map_mul, AddValuation.map_mul, powRow_v_neg_one_pow, hx'det]
          have : r' u0 = 1 := by rw [hr', Function.update_self]
          rw [this, AddValuation.map_one]
          simp
        · intro w hw
          induction w using Fin.lastCases with
          | last => exact absurd rfl hw
          | cast w' => rw [hAcs, Fin.insertNth_apply_same]; simp
      · intro w hw
        induction w using Fin.lastCases with
        | last =>
          simp only [hAlast, hr'N]
          exact hcz
        | cast w' =>
          simp only [hAcs]
          rw [Fin.sum_univ_succAbove _ u0, Fin.insertNth_apply_same, zero_pow hN.ne', zero_smul,
            zero_add]
          simp only [Fin.insertNth_apply_succAbove]
          exact hx'k w' (by simpa using hw)

theorem powRow_matrix : ∀ (C : Type) [Field C] [IsAlgClosed C] (v : AddValuation C (WithTop ℝ)) (V : Type) [AddCommGroup V] [Module C V] (N : ℕ), 0 < N → ∀ (j m : ℕ) (z : Fin m → V), Module.finrank C (Submodule.span C (Set.range z)) ≤ j → ∃ x : Matrix (Fin m) (Fin m) C, (∀ w u, IsIntV v (x w u)) ∧ v x.det = 0 ∧ ∀ w : Fin m, j ≤ w.val → ∑ u, (x w u) ^ N • z u = 0 := by
  intro C _ _ v V _ _ N hN j m z hz
  exact powRow_exists v N hN j m z hz

end

end GlobalTheory
end

section

open scoped TensorProduct

namespace GlobalTheory

theorem square_presentation_counital_comul_of_finrank (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (n : ℕ) :
    ∀ (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (ε : A →ₐ[k] k)
      (Δ : A →ₐ[k] A ⊗[k] A), Module.finrank k A = n →
      ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧
        (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) →
      IsNilpotent (RingHom.ker ε) →
      (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] A) (g : Fin s → MvPolynomial (Fin s) k),
        Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A _ _ _ ε Δ hn hΔ hε
  obtain ⟨d, x, l, hl, hlx, hadj⟩ := GlobalTheory.T.exists_generators_dual_point_derivations_augmented k A ε hε
  choose D hD using fun i => GlobalTheory.T.exists_invariant_derivation_of_counital_comul k A ε Δ hΔ (l i) (hl i)
  obtain ⟨E, hE⟩ := GlobalTheory.T.exists_derivations_dual_to_family_of_nilpotent_aug k A ε hε d x D (fun i j => by rw [hD, hlx])
  have hnt : Nontrivial A := ε.toRingHom.domain_nontrivial
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    refine ⟨0, MvPolynomial.aeval x, fun _ => 0, ?_, ?_⟩
    · rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval, hadj]
    · rw [Set.range_eq_empty, Ideal.span_empty, ← RingHom.injective_iff_ker_eq_bot]
      intro f g h
      rw [MvPolynomial.eq_C_of_isEmpty f, MvPolynomial.eq_C_of_isEmpty g] at h ⊢
      simp only [MvPolynomial.aeval_C] at h
      rw [(algebraMap k A).injective h]
  · obtain ⟨B, hB, Δ', hΔ'⟩ := GlobalTheory.T.frobeniusSubalgebra_counital_comul p k A ε Δ hΔ
    have hp : (p : A) = 0 := by
      rw [← map_natCast (algebraMap k A), CharP.cast_eq_zero, map_zero]
    have hEB : ∀ i, ∀ b ∈ B, E i b = 0 := by
      intro i b hb
      obtain ⟨c, rfl⟩ := (hB b).1 hb
      rw [Derivation.leibniz_pow, nsmul_eq_mul, hp, zero_mul]
    have hBtop : B ≠ ⊤ := by
      intro h
      have h1 := hE ⟨0, hd⟩ ⟨0, hd⟩
      rw [hEB _ _ (h ▸ Algebra.mem_top), if_pos rfl] at h1
      exact zero_ne_one h1
    have hlt : Module.finrank k B < n := by
      rw [← hn]
      have : (Subalgebra.toSubmodule B) ≠ ⊤ := by
        intro h
        apply hBtop
        rw [← Algebra.toSubmodule_eq_top]
        exact h
      exact Submodule.finrank_lt this
    have hfin : Module.Finite k B :=
      Module.Finite.of_injective B.val.toLinearMap Subtype.val_injective
    have hε' : IsNilpotent (RingHom.ker (ε.comp B.val)) := by
      obtain ⟨m, hm⟩ := hε
      refine ⟨m, ?_⟩
      have h1 : (RingHom.ker (ε.comp B.val)) = Ideal.comap B.val (RingHom.ker ε) := by
        ext b; simp [RingHom.mem_ker, Ideal.mem_comap]
      rw [h1, Ideal.zero_eq_bot, eq_bot_iff]
      refine (Ideal.le_comap_pow _ m).trans ?_
      rw [hm, Ideal.zero_eq_bot]
      intro b hb
      rw [Ideal.mem_comap, Ideal.mem_bot] at hb
      rw [Ideal.mem_bot]
      exact Subtype.ext hb
    refine GlobalTheory.T.exists_square_presentation_of_tower k B A (ih _ hlt B (ε.comp B.val) Δ' rfl hΔ' hε') ?_
    refine ⟨d, MvPolynomial.aeval x, _, ?_,
      GlobalTheory.T.ker_aeval_truncatedPolynomial_presentation p (Fact.out : p.Prime).pos B A d x
        (fun i => ⟨x i ^ p, (hB _).2 ⟨x i, rfl⟩⟩) (fun i => rfl)
        (GlobalTheory.T.truncatedMonomials_linearIndependent_over_constants p k A d x E hE B hEB)⟩
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval, eq_top_iff]
    intro a _
    have ha : a ∈ Algebra.adjoin k (Set.range x) := hadj ▸ Algebra.mem_top
    have hle : Algebra.adjoin k (Set.range x) ≤
        (Algebra.adjoin B (Set.range x)).restrictScalars k :=
      Algebra.adjoin_le Algebra.subset_adjoin
    exact hle ha

theorem square_presentation_of_counital_comul : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CommRing A] [Algebra k A] [CharP k p] [PerfectRing k p] [Module.Finite k A] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → IsNilpotent (RingHom.ker ε) → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] A) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) := by
  intro p _ k A _ _ _ _ _ _ ε Δ h hε
  exact square_presentation_counital_comul_of_finrank p k _ A ε Δ rfl h hε

end GlobalTheory
end

section

open Polynomial Matrix

namespace GlobalTheory.ConjLocal

variable {R : Type} [CommRing R] {n : ℕ}

def iterMat (Y : Matrix (Fin n) (Fin n) R) (v : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => (Y ^ (j : ℕ) *ᵥ v) i

def compMat (Q : R[X]) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if (j : ℕ) + 1 < n then (if (i : ℕ) = (j : ℕ) + 1 then 1 else 0) else -Q.coeff i

theorem exists_linearIndependent_iterates {K : Type} [Field K] (M : Matrix (Fin n) (Fin n) K)
    (hs : M.charpoly.Separable) :
    ∃ v : Fin n → K, LinearIndependent K (fun j : Fin n => (M ^ (j : ℕ)) *ᵥ v) := by
  obtain ⟨e, -, he⟩ := Formalism.IrreducibleCountingLemmas.Z.exists_annihilator_eq (toLin' M) (by rw [charpoly_toLin']; exact hs)
    (toLin' M).charpoly dvd_rfl
  refine ⟨e, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let q : K[X] := ∑ j : Fin n, monomial (j : ℕ) (c j)
  have ha : ∀ p : K[X], aeval (toLin' M) p = toLin' (aeval M p) := fun p =>
    aeval_algHom_apply (toLinAlgEquiv' (R := K) (n := Fin n)) M p
  have hq0 : aeval (toLin' M) q e = 0 := by
    rw [ha, toLin'_apply]
    have haq : aeval M q = ∑ j : Fin n, c j • M ^ (j : ℕ) := by

      simp [q, map_sum, aeval_monomial, Algebra.smul_def]
    rw [haq, Matrix.sum_mulVec]
    simpa [Matrix.smul_mulVec] using hc
  have hdvd := he q hq0
  rw [charpoly_toLin'] at hdvd
  have hdeg : q.degree < M.charpoly.degree := by
    rw [degree_eq_natDegree M.charpoly_monic.ne_zero, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun j _ => ?_
    exact lt_of_le_of_lt (degree_monomial_le _ _) (by exact_mod_cast j.2)
  have hq : q = 0 := eq_zero_of_dvd_of_degree_lt hdvd hdeg
  intro j
  have := congrArg (fun p : K[X] => p.coeff j) hq
  simp only [q, Polynomial.finsetSum_coeff, coeff_monomial_apply, Fin.val_inj,
    coeff_zero] at this
  simpa using this

end GlobalTheory.ConjLocal

namespace GlobalTheory.ConjLocal

variable {R : Type} [CommRing R] {n : ℕ}

theorem pow_dim_mulVec [Nontrivial R] (Y : Matrix (Fin n) (Fin n) R) (v : Fin n → R) (i : Fin n) :
    (Y ^ n *ᵥ v) i = -∑ k : Fin n, Y.charpoly.coeff k * (Y ^ (k : ℕ) *ᵥ v) i := by
  have h0 := Matrix.aeval_self_charpoly Y
  have hm := Y.charpoly_monic.as_sum
  rw [charpoly_natDegree_eq_dim, Fintype.card_fin] at hm
  rw [hm] at h0

  simp only [map_add (f := _), map_pow, aeval_X, map_sum, map_mul, aeval_C] at h0
  have := congrArg (fun M => (M *ᵥ v) i) h0
  simp only [add_mulVec, sum_mulVec, Pi.add_apply, Finset.sum_apply, zero_mulVec, Pi.zero_apply] at this
  rw [eq_neg_iff_add_eq_zero, ← this, ← Fin.sum_univ_eq_sum_range]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mulVec_mulVec, algebraMap_eq_diagonal, mulVec_diagonal]
  rfl

theorem mul_iterMat [Nontrivial R] (Y : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    Y * iterMat Y v = iterMat Y v * compMat Y.charpoly := by
  ext i j
  have hl : (Y * iterMat Y v) i j = (Y ^ ((j : ℕ) + 1) *ᵥ v) i := by
    rw [pow_succ', ← mulVec_mulVec]; rfl
  rw [hl, Matrix.mul_apply]
  simp only [iterMat, compMat, Matrix.of_apply]
  split_ifs with hj
  · rw [Finset.sum_eq_single ⟨(j : ℕ) + 1, hj⟩]
    · simp
    · intro b _ hb
      rw [if_neg (fun h => hb (Fin.ext h)), mul_zero]
    · simp
  · have : (j : ℕ) + 1 = n := by omega
    rw [this, pow_dim_mulVec, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

theorem exists_isUnit_det_iterMat [IsLocalRing R] (Y : Matrix (Fin n) (Fin n) R) (hs : Y.charpoly.Separable) :
    ∃ v : Fin n → R, IsUnit (iterMat Y v).det := by
  let f := IsLocalRing.residue R
  have hs' : (Y.map f).charpoly.Separable := by rw [Matrix.charpoly_map]; exact hs.map
  obtain ⟨w, hw⟩ := exists_linearIndependent_iterates (Y.map f) hs'
  choose v hv using fun i => IsLocalRing.residue_surjective (w i)
  refine ⟨v, ?_⟩
  have hmap : (iterMat Y v).map f = iterMat (Y.map f) w := by
    ext i j
    simp only [iterMat, Matrix.map_apply, Matrix.of_apply, ← Matrix.map_pow, RingHom.map_mulVec]
    congr 1
    funext k
    exact hv k
  have hunit : IsUnit (iterMat (Y.map f) w) := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    convert hw using 1
    funext j
    ext i
    rfl
  apply isUnit_of_map_unit f
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap]
  exact (Matrix.isUnit_iff_isUnit_det _).1 hunit

end GlobalTheory.ConjLocal
end

section

open Polynomial Matrix GlobalTheory.LatOrb

namespace GlobalTheory.LatOrb

theorem exists_cyclicVector_of_separable_charpoly {K : Type} [Field K] (n : ℕ)
    (γ : Matrix (Fin n) (Fin n) K) (hs : γ.charpoly.Separable) :
    ∃ v₀ : Fin n → K, ∀ u : Fin n → K, ∃ p : K[X], u = aeval γ p *ᵥ v₀ := by
  have hs' : (Matrix.toLin' γ).charpoly.Separable := by rwa [Matrix.charpoly_toLin']
  obtain ⟨e, he⟩ := Formalism.IrreducibleCountingLemmas.Z.base_change_cyclic_vector K (Fin n → K) (Matrix.toLin' γ) hs'
  refine ⟨e, fun u => ?_⟩
  obtain ⟨p, hp⟩ := he u
  refine ⟨p, ?_⟩
  rw [← hp]
  have h : aeval (Matrix.toLin' γ) p = Matrix.toLin' (aeval γ p) := by
    have := (aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)).toAlgHom γ p).symm
    exact this.symm
  rw [h, Matrix.toLin'_apply]

end GlobalTheory.LatOrb
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_sqZero_extend_localizationAway_pow : ∀ (R' A S : Type) [CommRing R'] [CommRing A] [CommRing S] [Algebra R' A] [Algebra R' S]
    [Algebra.FinitePresentation R' A] (J : Ideal S), J ^ 2 = ⊥ → ∀ (g : S) (φ : A →ₐ[R'] S)
    (ψ : A →ₐ[R'] Localization.Away g),
    (∀ x, ψ x - algebraMap S (Localization.Away g) (φ x) ∈ J.map (algebraMap S (Localization.Away g))) →
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ χ : A →ₐ[R'] S, (∀ x, χ x - φ x ∈ J) ∧
      ∀ x, algebraMap S (Localization.Away g) (χ x) = algebraMap S (Localization.Away g) (φ x) +
        algebraMap S (Localization.Away g) g ^ N * (ψ x - algebraMap S (Localization.Away g) (φ x)) := by
  first | exact @GlobalTheory.SecGlue.exists_sqZero_extend_pow | exact GlobalTheory.SecGlue.exists_sqZero_extend_pow | (intros; apply GlobalTheory.SecGlue.exists_sqZero_extend_pow <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_pow_mul_eq_of_algebraMap_localizationAway_eq : ∀ (R' A S : Type) [CommRing R'] [CommRing A] [CommRing S] [Algebra R' A] [Algebra R' S]
    [Algebra.FiniteType R' A] (χ₁ χ₂ : A →ₐ[R'] S) (g : S),
    (∀ x, algebraMap S (Localization.Away g) (χ₁ x) = algebraMap S (Localization.Away g) (χ₂ x)) →
    ∃ N : ℕ, ∀ x, g ^ N * χ₁ x = g ^ N * χ₂ x := by
  first | exact @GlobalTheory.algHom_eq_mul_pow_of_eq_localizationAway | exact GlobalTheory.algHom_eq_mul_pow_of_eq_localizationAway | (intros; apply GlobalTheory.algHom_eq_mul_pow_of_eq_localizationAway <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_away_unit_map_eq : ∀ (A : Type) [CommRing A] (M : Submonoid A) (u : (Localization M)ˣ), ∃ m ∈ M, ∃ v : (Localization.Away m)ˣ, ∀ φ : Localization.Away m →+* Localization M, φ.comp (algebraMap A _) = algebraMap A _ → Units.map φ.toMonoidHom v = u := by
  first | (exact @GlobalTheory.units_localization_descend_away) | (exact GlobalTheory.units_localization_descend_away) | (intros; apply GlobalTheory.units_localization_descend_away <;> assumption)
end
