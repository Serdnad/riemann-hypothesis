module

public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle483
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle237
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle231
public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle220
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Noetherian.Nilpotent
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle004
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle005
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

@[expose] public section

section

open scoped ComplexOrder Matrix

namespace GlobalTheory.WeightedLS

open Matrix

variable {M g : ℕ}

theorem det_pos (L : Matrix (Fin M) (Fin g) ℝ) (hL : L.rank = g) (D : Fin M → ℝ)
    (hD : ∀ k, 0 < D k) : 0 < (L.transpose * Matrix.diagonal D * L).det := by
  have hinj : Function.Injective L.mulVec := by
    have h := LinearMap.finrank_range_add_finrank_ker L.mulVecLin
    have h2 : Module.finrank ℝ (LinearMap.range L.mulVecLin) = g := (Matrix.finrank_range_mulVecLin L).trans hL
    rw [h2, Module.finrank_fin_fun] at h
    have h3 : Module.finrank ℝ (LinearMap.ker L.mulVecLin) = 0 := by omega
    have h4 : LinearMap.ker L.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h3
    exact LinearMap.ker_eq_bot.mp h4
  have hP : (Matrix.diagonal D).PosDef := Matrix.posDef_diagonal_iff.mpr hD
  have h := hP.conjTranspose_mul_mul_same hinj
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h.det_pos

theorem det_eq_sum (L X : Matrix (Fin M) (Fin g) ℝ) (D : Fin M → ℝ) :
    (L.transpose * Matrix.diagonal D * X).det = ∑ S : {S : Finset (Fin M) // S.card = g},
      (∏ j, D (S.1.orderEmbOfFin S.2 j)) * ((L.submatrix (S.1.orderEmbOfFin S.2) id).det *
        (X.submatrix (S.1.orderEmbOfFin S.2) id).det) := by
  rw [ReciprocityTheory.ChartRestriction.DS.S7.det_mul_eq_sum_submatrix]
  refine Finset.sum_congr rfl fun S _ => ?_
  have h : (L.transpose * Matrix.diagonal D).submatrix id (S.1.orderEmbOfFin S.2) =
      (L.submatrix (S.1.orderEmbOfFin S.2) id).transpose *
        Matrix.diagonal (fun j => D (S.1.orderEmbOfFin S.2 j)) := by
    ext i j
    simp [Matrix.mul_diagonal]
  rw [h, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  ring

theorem block_bound (A : Matrix (Fin g) (Fin g) ℝ) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (c : Fin g → ℝ) (k : Fin g),
      |A.det * (A.updateCol k c).det| ≤ K * ‖c‖ * (A.det * A.det) := by
  by_cases hA : A.det = 0
  · exact ⟨0, le_rfl, fun c k => by simp [hA]⟩
  · let f : (Fin g → ℝ) →L[ℝ] (Fin g → ℝ) := LinearMap.toContinuousLinearMap (Matrix.cramer A)
    have hp : 0 < |A.det| := abs_pos.mpr hA
    refine ⟨‖f‖ / |A.det|, by positivity, fun c k => ?_⟩
    have h1 : |(A.updateCol k c).det| ≤ ‖f‖ * ‖c‖ := by
      have h2 : (A.updateCol k c).det = f c k := by
        simp [f, Matrix.cramer_apply]
      rw [h2]
      exact (norm_le_pi_norm (f c) k).trans (f.le_opNorm c)
    rw [abs_mul, ← abs_mul_abs_self A.det]
    calc |A.det| * |(A.updateCol k c).det| ≤ |A.det| * (‖f‖ * ‖c‖) :=
          mul_le_mul_of_nonneg_left h1 hp.le
      _ = _ := by field_simp

theorem weighted_least_squares_bound : ∀ (M g : ℕ) (L : Matrix (Fin M) (Fin g) ℝ), L.rank = g →
    ∃ K : ℝ, ∀ (D : Fin M → ℝ) (b : Fin M → ℝ), (∀ k, 0 < D k) →
      ‖((L.transpose * Matrix.diagonal D * L)⁻¹ * L.transpose * Matrix.diagonal D).mulVec b‖ ≤
        K * ‖b‖ := by
  intro M g L hL
  choose K hK0 hK using fun S : {S : Finset (Fin M) // S.card = g} =>
    block_bound (L.submatrix (S.1.orderEmbOfFin S.2) id)
  refine ⟨∑ S, K S, fun D b hD => ?_⟩
  have hKs : 0 ≤ ∑ S, K S := Finset.sum_nonneg fun S _ => hK0 S
  have hdet := det_pos L hL D hD
  set A := L.transpose * Matrix.diagonal D * L with hA
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => ?_
  have hx : A.det * (A⁻¹ * L.transpose * Matrix.diagonal D).mulVec b k =
      (L.transpose * Matrix.diagonal D * L.updateCol k b).det := by
    have h1 := Matrix.det_smul_inv_mulVec_eq_cramer A ((L.transpose * Matrix.diagonal D).mulVec b)
      (isUnit_iff_ne_zero.mpr hdet.ne')
    have h2 := congrFun h1 k
    rw [Matrix.cramer_apply, Matrix.mulVec_mulVec, ← Matrix.mul_assoc] at h2
    rw [← smul_eq_mul, ← Pi.smul_apply, h2]
    congr 1
    ext i j
    by_cases hj : j = k
    · subst hj
      simp [Matrix.mul_apply (M := L.transpose * Matrix.diagonal D), Matrix.mulVec, dotProduct]
    · simp [hA, Matrix.mul_apply (M := L.transpose * Matrix.diagonal D), Matrix.updateCol_ne hj]
  have hb : |(L.transpose * Matrix.diagonal D * L.updateCol k b).det| ≤
      (∑ S, K S) * ‖b‖ * A.det := by
    rw [hA, det_eq_sum, det_eq_sum, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun S _ => ?_)
    set e := S.1.orderEmbOfFin S.2 with he
    have hp : 0 ≤ ∏ j, D (e j) := Finset.prod_nonneg fun j _ => (hD _).le
    have hu : (L.updateCol k b).submatrix e id = (L.submatrix e id).updateCol k (b ∘ e) := by
      ext i j
      by_cases hj : j = k
      · subst hj; simp
      · simp [Matrix.updateCol_ne hj]
    have hn : ‖b ∘ e‖ ≤ ‖b‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => norm_le_pi_norm b (e i)
    have hKS : K S ≤ ∑ S, K S :=
      Finset.single_le_sum (f := K) (fun S _ => hK0 S) (Finset.mem_univ S)
    rw [abs_mul, abs_of_nonneg hp, hu, mul_left_comm]
    refine mul_le_mul_of_nonneg_left ((hK S (b ∘ e) k).trans ?_) hp
    exact mul_le_mul_of_nonneg_right (mul_le_mul hKS hn (norm_nonneg _) hKs) (mul_self_nonneg _)
  rw [← hx, abs_mul, abs_of_pos hdet, mul_comm] at hb
  exact le_of_mul_le_mul_right hb hdet

end GlobalTheory.WeightedLS
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem preirreducibleSpace_of_continuous_surjective_fibreChart {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [hX : PreirreducibleSpace X] (f : X → Y) (hf : Continuous f)
    (hs : Function.Surjective f) : PreirreducibleSpace Y :=
  ⟨by simpa [Set.image_univ_of_surjective hs] using
    hX.isPreirreducible_univ.image f hf.continuousOn⟩

theorem preirreducibleSpace_tensor_congr_fibreChart (A B C k : Type) [CommRing A] [CommRing B]
    [CommRing C] [CommRing k] [Algebra A B] [Algebra A C] [Algebra A k] (e : B ≃ₐ[A] C) :
    PreirreducibleSpace (PrimeSpectrum (k ⊗[A] B)) ↔ PreirreducibleSpace (PrimeSpectrum (k ⊗[A] C)) := by
  let E : k ⊗[A] B ≃ₐ[A] k ⊗[A] C := Algebra.TensorProduct.congr AlgEquiv.refl e
  let H := PrimeSpectrum.homeomorphOfRingEquiv E.toRingEquiv
  constructor
  · intro h
    exact preirreducibleSpace_of_continuous_surjective_fibreChart H H.continuous H.surjective
  · intro h
    exact preirreducibleSpace_of_continuous_surjective_fibreChart H.symm H.symm.continuous
      H.symm.surjective

theorem preirreducibleSpace_fibre_standardEtale_spreads :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ) [Algebra (MvPolynomial (Fin n) A) B] [IsScalarTower A (MvPolynomial (Fin n) A) B], Algebra.IsStandardEtale (MvPolynomial (Fin n) A) B → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω], PreirreducibleSpace (PrimeSpectrum (Ω ⊗[A] B)) → ∃ (a : A) (I : Finset A), algebraMap A Ω a ≠ 0 ∧ (∀ c ∈ I, algebraMap A Ω c = 0) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra A k], algebraMap A k a ≠ 0 → (∀ c ∈ I, algebraMap A k c = 0) → PreirreducibleSpace (PrimeSpectrum (k ⊗[A] B)) := by
  intro A B _ _ _ n _ _ hB Ω _ _ _ hΩ
  obtain ⟨f, g, hf, hd, ⟨e⟩⟩ := GlobalTheory.T.standardEtale_localization_away_quotient_span A B n hB
  have hΩ' := (GlobalTheory.T.preirreducibleSpace_fibreHypersurface_spectrum_iff A _ f g Ω).1 ((preirreducibleSpace_tensor_congr_fibreChart A _ _ Ω e).1 hΩ)
  obtain ⟨a, I, ha, hI, hk⟩ := GlobalTheory.T.hypersurface_part_geometric_irreducible_spreads A (Option (Fin n)) f g none hf hd Ω (algebraMap A Ω) hΩ'
  refine ⟨a, I, ha, hI, ?_⟩
  intro k _ _ _ hak hIk
  exact (preirreducibleSpace_tensor_congr_fibreChart A _ _ k e).2
    ((GlobalTheory.T.preirreducibleSpace_fibreHypersurface_spectrum_iff A _ f g k).2 (hk k (algebraMap A k) hak hIk))

end GlobalTheory
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

theorem exists_perfectPart_algHom : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A],
    ∃ π : A →ₐ[k] A, ((∀ a : A, IsNilpotent (a - π a)) ∧ ∀ a : A, ∃ b : A, π a = π b ^ p) := by
  intro p _ k _ _ _ A _ _ _
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨AlgHom.id k A, fun a => ⟨1, Subsingleton.elim _ _⟩, fun a => ⟨a, Subsingleton.elim _ _⟩⟩
  haveI : CharP A p := charP_of_injective_algebraMap (algebraMap k A).injective p
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨n, hn⟩ := IsNoetherianRing.isNilpotent_nilradical A
  set N := nilradical A with hNdef
  set q := p ^ (n + 1) with hqdef
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hq : ∀ x : A, x ∈ N → x ^ q = 0 := by
    intro x hx
    have h1 : x ^ n ∈ N ^ n := Ideal.pow_mem_pow hx n
    rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at h1
    have hle : n ≤ q := by
      have := Nat.lt_pow_self (n := n + 1) hp1
      omega
    rw [← Nat.sub_add_cancel hle, pow_add, h1, mul_zero]
  haveI : Module.Finite k (A ⧸ N) := Module.Finite.trans A (A ⧸ N)
  haveI : IsReduced (A ⧸ N) := (Ideal.isRadical_iff_quotient_reduced N).mp (Ideal.radical_isRadical _)
  have hroot : ∀ m : ℕ, ∀ a : A ⧸ N, ∃ b, a = b ^ p ^ m := by
    intro m
    induction m with
    | zero => intro a; exact ⟨a, by simp⟩
    | succ m ih =>
      intro a
      obtain ⟨b, hb⟩ := ih a
      obtain ⟨c, hc⟩ := GlobalTheory.T.exists_pow_char_eq_of_isReduced_finite' p k (A ⧸ N) b
      exact ⟨c, by rw [hb, hc, ← pow_mul, ← pow_succ']⟩
  have hlift : ∀ a : A, ∃ b : A, a - b ^ q ∈ N := by
    intro a
    obtain ⟨c, hc⟩ := hroot (n + 1) (Ideal.Quotient.mk N a)
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨b, ?_⟩
    rw [← Ideal.Quotient.eq, map_pow]
    exact hc
  have hu : ∀ a b c : A, a - b ^ q ∈ N → a - c ^ q ∈ N → b ^ q = c ^ q := by
    intro a b c hb hc
    have h1 : (b - c) ^ q ∈ N := by
      rw [hqdef, sub_pow_char_pow]
      have : b ^ p ^ (n + 1) - c ^ p ^ (n + 1) = (a - c ^ q) - (a - b ^ q) := by ring
      rw [this]
      exact N.sub_mem hc hb
    have h2 : b - c ∈ N := mem_nilradical.mpr (IsNilpotent.of_pow (mem_nilradical.mp h1))
    have h3 := hq _ h2
    rw [hqdef, sub_pow_char_pow, sub_eq_zero] at h3
    exact h3
  choose β hβ using hlift
  have hf : ∀ a c : A, a - c ^ q ∈ N → β a ^ q = c ^ q := fun a c hc => hu a _ _ (hβ a) hc
  let π : A →ₐ[k] A :=
    { toFun := fun a => β a ^ q
      map_one' := by
        rw [hf 1 1 (by simp), one_pow]
      map_mul' := fun x y => by
        rw [hf (x * y) (β x * β y) ?_, mul_pow]
        have : x * y - (β x * β y) ^ q = x * (y - β y ^ q) + (x - β x ^ q) * β y ^ q := by ring
        rw [this]
        exact N.add_mem (N.mul_mem_left _ (hβ y)) (N.mul_mem_right _ (hβ x))
      map_zero' := by
        rw [hf 0 0 (by rw [zero_pow (by positivity), sub_zero]; exact N.zero_mem), zero_pow (by positivity)]
      map_add' := fun x y => by
        rw [hf (x + y) (β x + β y) ?_, hqdef, add_pow_char_pow]
        rw [hqdef, add_pow_char_pow]
        have : x + y - (β x ^ p ^ (n + 1) + β y ^ p ^ (n + 1)) =
            (x - β x ^ q) + (y - β y ^ q) := by rw [hqdef]; ring
        rw [this]
        exact N.add_mem (hβ x) (hβ y)
      commutes' := fun c => by
        set d := (iterateFrobeniusEquiv k p (n + 1)).symm c with hd
        have hdc : d ^ q = c := by
          have h0 := RingEquiv.apply_symm_apply (iterateFrobeniusEquiv k p (n + 1)) c
          rw [iterateFrobeniusEquiv_apply, iterateFrobenius_def] at h0
          rw [hqdef, hd]
          exact h0
        rw [hf _ (algebraMap k A d) ?_, ← map_pow, hdc]
        rw [← map_pow, hdc, sub_self]
        exact N.zero_mem }
  have hπ : ∀ a, π a = β a ^ q := fun a => rfl
  refine ⟨π, fun a => ?_, fun a => ⟨β a ^ p ^ n, ?_⟩⟩
  · rw [hπ]
    exact mem_nilradical.mp (hβ a)
  · rw [map_pow, ← pow_mul, ← pow_succ, hπ a]
    have h2 : β a - π (β a) ∈ N := mem_nilradical.mpr (by rw [hπ]; exact mem_nilradical.mp (hβ _))
    have h3 := hq _ h2
    rw [hqdef, sub_pow_char_pow, sub_eq_zero] at h3
    exact h3

end GlobalTheory
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv

theorem exists_unique_dual_of_compatible_mod_pow :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (a : O)
      [IsAdicComplete (Ideal.span {a}) O] (u : ∀ n : ℕ, M →ₗ[O] O ⧸ Ideal.span {a ^ n}),
      (∀ n w (x : O), u (n + 1) w = Ideal.Quotient.mk _ x → u n w = Ideal.Quotient.mk _ x) →
      ∃! l : Module.Dual O M, ∀ n w, Ideal.Quotient.mk _ (l w) = u n w := by
  intro O M _ _ _ a _ u hu

  have sep : ∀ y : O, (∀ n : ℕ, y ∈ Ideal.span {a ^ n}) → y = 0 := by
    intro y hy
    refine IsHausdorff.haus' (I := Ideal.span {a}) y fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact hy n
  have key : ∀ w : M, ∃! y : O, ∀ n, Ideal.Quotient.mk (Ideal.span {a ^ n}) y = u n w := by
    intro w
    choose x hx using fun n => Ideal.Quotient.mk_surjective (u n w)
    have step : ∀ n, x n - x (n + 1) ∈ Ideal.span {a ^ n} := by
      intro n
      exact Ideal.Quotient.eq.mp ((hx n).trans (hu n w (x (n + 1)) (hx (n + 1)).symm))
    have cauchy : ∀ m n, m ≤ n → x m - x n ∈ Ideal.span {a ^ m} := by
      intro m n hmn
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ k hmk ih =>
        have h2 : x k - x (k + 1) ∈ Ideal.span {a ^ m} :=
          (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow a hmk)) (step k)
        have := Ideal.add_mem _ ih h2
        simpa using this
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {a}) x (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
      exact cauchy m n hmn)
    refine ⟨L, fun n => ?_, fun y hy => ?_⟩
    · have h := hL n
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow] at h
      rw [← hx n]
      exact Ideal.Quotient.eq.mpr (by simpa using (Ideal.span {a ^ n}).neg_mem h)
    · refine sub_eq_zero.mp (sep _ fun n => ?_)
      have h := hL n
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow] at h
      exact Ideal.Quotient.eq.mp ((hy n).trans (hx n).symm) |> fun h' => by
        simpa using Ideal.add_mem _ h' h
  choose f hf huniq using key
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, ?_, ?_⟩
  · intro w w'
    refine (huniq (w + w') _ fun n => ?_).symm
    rw [map_add (f := _), map_add (f := _), hf, hf]
  · intro c w
    refine (huniq (c • w) _ fun n => ?_).symm
    rw [RingHom.id_apply, smul_eq_mul, map_mul, map_smul, ← hf w n, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq]
  · exact fun n w => hf w n
  · intro l hl
    exact LinearMap.ext fun w => huniq w (l w) fun n => hl n w

end GlobalTheory.PDiv
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem tensor_projective_dvd_of_coord_dvd :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (N : Type) [AddCommGroup N] [Module O N] [Module.Projective O M] [Module.Projective O N] (a : O) (z : M ⊗[O] N), (∀ (φ : Module.Dual O M) (ψ : Module.Dual O N), a ∣ TensorProduct.dualDistrib O M N (φ ⊗ₜ ψ) z) → ∃ y, z = a • y := by
  intro O M _ _ _ N _ _ _ _ a z h
  obtain ⟨s, hs⟩ := (Module.Projective.out : ∃ s : M →ₗ[O] M →₀ O,
    Function.LeftInverse (Finsupp.linearCombination O id) s)
  obtain ⟨s', hs'⟩ := (Module.Projective.out : ∃ s : N →ₗ[O] N →₀ O,
    Function.LeftInverse (Finsupp.linearCombination O id) s)
  have hf : ∀ (w : M ⊗[O] N) (p : M × N), finsuppTensorFinsupp' O M N (TensorProduct.map s s' w) p =
      TensorProduct.dualDistrib O M N ((Finsupp.lapply p.1 ∘ₗ s) ⊗ₜ (Finsupp.lapply p.2 ∘ₗ s')) w := by
    intro w ⟨i, j⟩
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp [finsuppTensorFinsupp'_apply_apply, dualDistrib_apply]
    | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  set f := finsuppTensorFinsupp' O M N (TensorProduct.map s s' z) with hfdef
  have hdiv : ∀ p, a ∣ f p := fun p => by rw [hfdef, hf]; exact h _ _
  choose c hc using hdiv
  let g : M × N →₀ O := ∑ p ∈ f.support, Finsupp.single p (c p)
  have hg : f = a • g := by
    simp only [g, Finset.smul_sum, Finsupp.smul_single, smul_eq_mul, ← hc]
    exact (Finsupp.sum_single f).symm
  have hid : (Finsupp.linearCombination O id : (M →₀ O) →ₗ[O] M) ∘ₗ s = LinearMap.id :=
    LinearMap.ext hs
  have hid' : (Finsupp.linearCombination O id : (N →₀ O) →ₗ[O] N) ∘ₗ s' = LinearMap.id :=
    LinearMap.ext hs'
  refine ⟨TensorProduct.map (Finsupp.linearCombination O id) (Finsupp.linearCombination O id)
    ((finsuppTensorFinsupp' O M N).symm g), ?_⟩
  rw [← map_smul, ← map_smul, ← hg, hfdef, LinearEquiv.symm_apply_apply, ← LinearMap.comp_apply,
    ← TensorProduct.map_comp, hid, hid', TensorProduct.map_id, LinearMap.id_apply]

end GlobalTheory
end

section

open scoped Matrix

namespace GlobalTheory

theorem exists_isotropic_graph_isUnit_lowerRow : ∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    (∃ x : O, IsUnit (c x - x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det := by
  have hfield := GlobalTheory.T.exists_isotropic_graph_det_ne_zero
  have hlift := GlobalTheory.T.exists_skew_lift_mod_maximalIdeal

  intro O _ _ c hc h2 hx0 n J hJ hJdet g hg hgu
  obtain ⟨x, hx⟩ := hx0
  haveI : IsLocalHom c := ⟨fun a ha => by simpa [hc] using ha.map c⟩
  set π := IsLocalRing.residue O with hπ
  set σ : IsLocalRing.ResidueField O →+* IsLocalRing.ResidueField O := IsLocalRing.ResidueField.map c with hσ
  have hσπ : ∀ a, σ (π a) = π (c a) := fun a => IsLocalRing.ResidueField.map_residue c a
  have hσσ : ∀ y, σ (σ y) = y := by
    intro y; obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y; rw [hσπ, hσπ, hc]
  have hε : ∃ ε, ε ≠ 0 ∧ σ ε = -ε := ⟨π (c x - x), (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hx, by
    rw [hσπ, map_sub, hc, ← neg_sub, map_neg]⟩
  have hmapc : ∀ {m : Type} (M : Matrix m m O), (M.map c).map π = (M.map π).map σ := by
    intro m M; ext i j; simp [hσπ]
  have hJ' : ∀ i j, σ (J.map π j i) = J.map π i j := by intro i j; simp [hσπ, hJ]
  have hJdet' : (J.map π).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hJdet
  have hg' : (g.map π).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hg
  have hgu' : (g.map π)ᵀ * Matrix.fromBlocks 0 (J.map π) (J.map π) 0 * (g.map π).map σ
      = Matrix.fromBlocks 0 (J.map π) (J.map π) 0 := by
    have := congrArg (fun M => M.map π) hgu
    simpa only [Matrix.map_mul, Matrix.transpose_map, hmapc, Matrix.fromBlocks_map,
      Matrix.map_zero _ (map_zero π)] using this
  obtain ⟨Zb, hZb, hdet⟩ := hfield _ σ hσσ hε n _ hJ' hJdet' _ hg' hgu'
  obtain ⟨Z₀, hZ₀⟩ : ∃ Z₀ : Matrix (Fin n) (Fin n) O, Z₀.map π = Zb :=
    ⟨fun i j => (IsLocalRing.residue_surjective (Zb i j)).choose, by
      ext i j; exact (IsLocalRing.residue_surjective (Zb i j)).choose_spec⟩
  have hZ₀m : ∀ i j, (Z₀ᵀ * J + J * Z₀.map c) i j ∈ IsLocalRing.maximalIdeal O := by
    intro i j
    rw [← IsLocalRing.residue_eq_zero_iff]
    have := congrArg (fun M => M i j) hZb
    simp only [Matrix.zero_apply] at this
    rw [← this, ← hZ₀, ← hmapc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add π)]
    rfl
  obtain ⟨Z, hZ, hZm⟩ := hlift O c hc h2 n J hJ hJdet Z₀ hZ₀m
  refine ⟨Z, hZ, ?_⟩
  have hZπ : Z.map π = Zb := by
    rw [← hZ₀]; ext i j
    simp only [Matrix.map_apply]
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hZm i j
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← hπ, RingHom.map_det, RingHom.mapMatrix_apply,
    Matrix.map_add _ (map_add π), Matrix.map_mul, hZπ]
  exact hdet

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.fractionRing_away_etale_dedekind_artinian_reduced : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B) (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'], IsArtinianRing (FractionRing (Localization.Away (algebraMap B A' f))) ∧ IsReduced (FractionRing (Localization.Away (algebraMap B A' f))) := by
  first | (exact @GlobalTheory.fractionRing_away_etale_isArtinian_isReduced) | (exact GlobalTheory.fractionRing_away_etale_isArtinian_isReduced) | (intros; apply GlobalTheory.fractionRing_away_etale_isArtinian_isReduced <;> assumption)
end
