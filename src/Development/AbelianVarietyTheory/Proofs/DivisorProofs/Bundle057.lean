module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

@[expose] public section

section

namespace GlobalTheory.SpectralLemmaSecond

open Matrix

theorem main : (let d1 : {m k : Type} → [Fintype m] → [Fintype k] → Matrix m k ℂ → ℝ := @(fun {m k : Type} [Fintype m] [Fintype k] (M : Matrix m k ℂ) ↦ ∑ i : m, ∑ j : k, ‖M i j‖); ∀ {m k p : Type} [inst : Fintype m] [inst_1 : Fintype k] [inst_2 : Fintype p] (M : Matrix m k ℂ) (N : Matrix k p ℂ), d1 (M * N) ≤ d1 M * d1 N) := by
  intro d1 m k p _ _ _ M N
  simp only [d1]
  have hB : ∀ l : k, ∑ j : p, ‖N l j‖ ≤ ∑ l' : k, ∑ j : p, ‖N l' j‖ := fun l =>
    Finset.single_le_sum (f := fun l' => ∑ j : p, ‖N l' j‖)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.mem_univ l)
  calc ∑ i : m, ∑ j : p, ‖(M * N) i j‖
      ≤ ∑ i : m, ∑ j : p, ∑ l : k, ‖M i l‖ * ‖N l j‖ := by
        gcongr with i _ j _
        rw [Matrix.mul_apply]
        refine (norm_sum_le _ _).trans ?_
        gcongr with l _
        exact (norm_mul _ _).le
    _ = ∑ i : m, ∑ l : k, ‖M i l‖ * ∑ j : p, ‖N l j‖ := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [Finset.mul_sum]
    _ ≤ ∑ i : m, ∑ l : k, ‖M i l‖ * ∑ l' : k, ∑ j : p, ‖N l' j‖ := by
        gcongr with i _ l _
        exact hB l
    _ = (∑ i : m, ∑ l : k, ‖M i l‖) * ∑ l' : k, ∑ j : p, ‖N l' j‖ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_mul]

end GlobalTheory.SpectralLemmaSecond
end

section

open Topology Filter

namespace GlobalTheory

theorem span_finiteDimensional_of_bounded_forms {V : Type} [AddCommGroup V] [Module ℂ V]
    (s : Set V) (hs : ∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C) :
    FiniteDimensional ℂ (Submodule.span ℂ s) := by
  classical
  obtain ⟨t, hts, hspan, hli⟩ := exists_linearIndependent ℂ s
  have ht : t.Finite := by
    by_contra hinf
    have hinf' : t.Infinite := hinf
    let e : ℕ ↪ t := hinf'.natEmbedding
    have hli' : LinearIndepOn ℂ id t := hli
    let b := Module.Basis.extend hli'
    let v : (hli'.extend (Set.subset_univ t)) → ℂ := fun i =>
      if h : ∃ k : ℕ, ((e k : t) : V) = (i : V) then (h.choose : ℂ) else 0
    obtain ⟨C, hC⟩ := hs (b.constr ℂ v)
    have key : ∀ k : ℕ, b.constr ℂ v ((e k : t) : V) = (k : ℂ) := by
      intro k
      have hmem : ((e k : t) : V) ∈ hli'.extend (Set.subset_univ t) :=
        hli'.subset_extend _ (e k).2
      have hb : b ⟨_, hmem⟩ = ((e k : t) : V) := by simp [b, Module.Basis.coe_extend]
      rw [← hb, Module.Basis.constr_basis]
      have h : ∃ j : ℕ, ((e j : t) : V) = ((⟨_, hmem⟩ : hli'.extend (Set.subset_univ t)) : V) :=
        ⟨k, rfl⟩
      simp only [v, dif_pos h]
      have hj : h.choose = k := e.injective (Subtype.ext h.choose_spec)
      rw [hj]
    obtain ⟨k, hk⟩ := exists_nat_gt C
    have hle := hC _ (hts (e k).2)
    rw [key, Complex.norm_natCast] at hle
    linarith
  have hfd : FiniteDimensional ℂ (Submodule.span ℂ t) := FiniteDimensional.span_of_finite ℂ ht
  rw [hspan] at hfd
  exact hfd

end GlobalTheory
end

section

open Matrix Polynomial

namespace GlobalTheory

theorem norm_multiset_prod_near_one (s : Multiset ℂ) (hs : ∀ μ ∈ s, ‖μ - 1‖ ≤ 1 / 2) :
    (1 / 2 : ℝ) ^ Multiset.card s ≤ ‖s.prod‖ ∧ ‖s.prod‖ ≤ (3 / 2 : ℝ) ^ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha := hs a (Multiset.mem_cons_self a s)
    obtain ⟨h1, h2⟩ := ih (fun μ hμ => hs μ (Multiset.mem_cons_of_mem hμ))
    have hlo : (1 / 2 : ℝ) ≤ ‖a‖ := by
      have := norm_sub_norm_le (1 : ℂ) (1 - a)
      rw [norm_one, sub_sub_cancel, norm_sub_rev] at this
      linarith
    have hhi : ‖a‖ ≤ 3 / 2 := by
      have := norm_add_le (a - 1) 1
      rw [sub_add_cancel, norm_one] at this
      linarith
    rw [Multiset.prod_cons, Multiset.card_cons, norm_mul, pow_succ, pow_succ]
    constructor
    · rw [mul_comm ((1 / 2 : ℝ) ^ _)]
      exact mul_le_mul hlo h1 (by positivity) (norm_nonneg _)
    · rw [mul_comm ((3 / 2 : ℝ) ^ _)]
      exact mul_le_mul hhi h2 (norm_nonneg _) (by norm_num)

theorem det_near_one_bounds (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ)
    (hA : ∀ i j, ‖A i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ ε) (hn : (n : ℝ) * ε ≤ 1 / 2) :
    (1 / 2 : ℝ) ^ n ≤ ‖A.det‖ ∧ ‖A.det‖ ≤ 2 ^ n := by
  have hroot : ∀ μ ∈ A.charpoly.roots, ‖μ - 1‖ ≤ 1 / 2 := by
    intro μ hμ
    have hr : A.charpoly.IsRoot μ := isRoot_of_mem_roots hμ
    have hev : Module.End.HasEigenvalue (Matrix.toLin' A) μ := by
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']; exact hr
    obtain ⟨k, hk⟩ := eigenvalue_mem_ball hev
    rw [Metric.mem_closedBall, dist_eq_norm] at hk
    have hdiag : ‖A k k - 1‖ ≤ ε := by simpa using hA k k
    have h1n : 1 ≤ n := Fin.pos k
    have hoff : ∑ j ∈ Finset.univ.erase k, ‖A k j‖ ≤ ((n : ℝ) - 1) * ε := by
      have hle : ∀ j ∈ Finset.univ.erase k, ‖A k j‖ ≤ ε := by
        intro j hj
        have hjk : k ≠ j := (Finset.ne_of_mem_erase hj).symm
        simpa [Matrix.one_apply_ne hjk] using hA k j
      calc _ ≤ ∑ _j ∈ Finset.univ.erase k, ε := Finset.sum_le_sum hle
        _ = ((n : ℝ) - 1) * ε := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub h1n, Nat.cast_one]
    calc ‖μ - 1‖ = ‖(μ - A k k) + (A k k - 1)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖μ - A k k‖ + ‖A k k - 1‖ := norm_add_le _ _
      _ ≤ ((n : ℝ) - 1) * ε + ε := add_le_add (hk.trans hoff) hdiag
      _ = n * ε := by ring
      _ ≤ 1 / 2 := hn
  have hcard : Multiset.card A.charpoly.roots = n := by
    rw [(splits_iff_card_roots).mp (IsAlgClosed.splits _), Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  obtain ⟨h1, h2⟩ := norm_multiset_prod_near_one _ hroot
  rw [hcard, ← Matrix.det_eq_prod_roots_charpoly] at h1 h2
  refine ⟨h1, h2.trans ?_⟩
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) n

end GlobalTheory
end

section

open Matrix

namespace GlobalTheory

theorem herm_scale_entry_bound : ∀ {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ), P.IsHermitian → (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) → ∃ K : ℝ, ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), 0 < s → Yᴴ * P * Y = (s : ℂ) • P → ∀ i j, ‖Y i j‖ ^ 2 ≤ K * s := by
  intro n P _hP hpos
  cases n with
  | zero => exact ⟨0, fun _ _ _ _ i => i.elim0⟩
  | succ k =>
  set q : (Fin (k+1) → ℂ) → ℝ := fun x => (star x ⬝ᵥ P *ᵥ x).re with hq
  have hcont : Continuous q := by
    simp only [hq, dotProduct, mulVec, Pi.star_apply]
    fun_prop
  have hsmul : ∀ (t : ℝ) (x : Fin (k+1) → ℂ), q ((t : ℂ) • x) = t ^ 2 * q x := by
    intro t x
    simp only [hq, star_smul, Complex.star_def, Complex.conj_ofReal, mulVec_smul, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
    rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
    ring
  obtain ⟨x0, hx0S, hmin⟩ := (isCompact_sphere (0 : Fin (k+1) → ℂ) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) hcont.continuousOn
  set m := q x0 with hm_def
  have hx0 : x0 ≠ 0 := by
    intro h; rw [h] at hx0S; simp at hx0S
  have hm : 0 < m := hpos x0 hx0
  have hlow : ∀ x, m * ‖x‖ ^ 2 ≤ q x := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp [hq]
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    set u : Fin (k+1) → ℂ := ((‖x‖⁻¹ : ℝ) : ℂ) • x with hu
    have huS : u ∈ Metric.sphere (0 : Fin (k+1) → ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, hu, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
    have hxu : x = ((‖x‖ : ℝ) : ℂ) • u := by
      rw [hu, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_smul]
    have h1 : m ≤ q u := hmin huS
    have hqx : q x = ‖x‖ ^ 2 * q u := by
      conv_lhs => rw [hxu]
      exact hsmul _ _
    rw [hqx]
    nlinarith [sq_nonneg ‖x‖]
  have hY : ∀ (Y : Matrix (Fin (k+1)) (Fin (k+1)) ℂ) (s : ℝ), Yᴴ * P * Y = (s : ℂ) • P →
      ∀ x, q (Y *ᵥ x) = s * q x := by
    intro Y s h x
    simp only [hq]
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, h,
      Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
  set C : ℝ := ∑ j, ‖P j j‖ with hC
  refine ⟨C / m, fun Y s hs h i j => ?_⟩
  set e : Fin (k+1) → ℂ := Pi.single j 1 with he
  have hYe : Y *ᵥ e = fun i => Y i j := by
    rw [he, mulVec_single_one]; rfl
  have hqe : q e = (P j j).re := by
    simp [hq, he, mulVec_single_one]
  have hle : ‖Y i j‖ ≤ ‖Y *ᵥ e‖ := by
    rw [hYe]; exact norm_le_pi_norm (fun i => Y i j) i
  have hPjj : (P j j).re ≤ C :=
    (Complex.re_le_norm _).trans (Finset.single_le_sum (f := fun j => ‖P j j‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ j))
  have key : m * ‖Y *ᵥ e‖ ^ 2 ≤ s * (P j j).re := by
    rw [← hqe, ← hY Y s h e]; exact hlow _
  have h2 : ‖Y i j‖ ^ 2 ≤ ‖Y *ᵥ e‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
  rw [div_mul_eq_mul_div, le_div_iff₀ hm]
  nlinarith [mul_le_mul_of_nonneg_left hPjj hs.le]

end GlobalTheory
end

section

open NumberField IsDedekindDomain Filter

namespace GlobalTheory.BddFinite

theorem exists_le_exp_nat (B : WithZero (Multiplicative ℤ)) : ∃ n : ℕ, B ≤ WithZero.exp (n : ℤ) := by
  induction B using WithZero.recZeroCoe with
  | zero => exact ⟨0, zero_le'⟩
  | coe m =>
    refine ⟨(Multiplicative.toAdd m).toNat, ?_⟩
    rw [WithZero.exp, WithZero.coe_le_coe, ← Multiplicative.toAdd_le]
    simp only [toAdd_ofAdd]
    exact Int.self_le_toNat _

theorem exists_clearing {K : Type} [Field K] [NumberField K] (A : Set K)
    (w : HeightOneSpectrum (𝓞 K)) (B : WithZero (Multiplicative ℤ))
    (hB : ∀ x ∈ A, w.valuation K x ≤ B) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ ∀ x ∈ A, w.valuation K ((a : K) * x) ≤ 1 := by
  obtain ⟨n, hn⟩ := exists_le_exp_nat B
  have hne : w.asIdeal ^ n ≠ ⊥ := pow_ne_zero n w.ne_bot
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨r, hr0, fun x hx => ?_⟩
  have h1 : w.intValuation r ≤ WithZero.exp (-(n : ℤ)) := (w.intValuation_le_pow_iff_mem r n).2 hr
  rw [map_mul]
  have h2 : w.valuation K (r : K) = w.intValuation r := w.valuation_of_algebraMap r
  rw [h2]
  calc w.intValuation r * w.valuation K x ≤ WithZero.exp (-(n : ℤ)) * WithZero.exp (n : ℤ) :=
        mul_le_mul' h1 ((hB x hx).trans hn)
    _ = 1 := by rw [← WithZero.exp_add]; simp

theorem finite_of_bdd : ∀ (K : Type) [Field K] [NumberField K] (A : Set K) (R : ℝ), (∀ x ∈ A, ∀ τ : K →+* ℂ, ‖τ x‖ ≤ R) → (∀ w : HeightOneSpectrum (𝓞 K), ∃ B : WithZero (Multiplicative ℤ), ∀ x ∈ A, w.valuation K x ≤ B) → (∀ᶠ w : HeightOneSpectrum (𝓞 K) in cofinite, ∀ x ∈ A, w.valuation K x ≤ 1) → A.Finite := by
  classical
  intro K _ _ A R hR hB hcof
  choose B hB using hB
  choose a ha0 ha using fun w => exists_clearing A w (B w) (hB w)
  have hF : {w : HeightOneSpectrum (𝓞 K) | ¬ ∀ x ∈ A, w.valuation K x ≤ 1}.Finite :=
    Filter.eventually_cofinite.mp hcof
  set F := hF.toFinset with hFdef
  set d : 𝓞 K := ∏ w ∈ F, a w with hd
  have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun w _ => ha0 w)
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd0

  have hval : ∀ x ∈ A, ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K ((d : K) * x) ≤ 1 := by
    intro x hx v
    by_cases hv : v ∈ F
    · have hsplit : (d : K) = ((∏ w ∈ F.erase v, a w : 𝓞 K) : K) * (a v : K) := by
        rw [hd, ← Finset.prod_erase_mul F a hv]; push_cast; ring
      rw [hsplit, mul_assoc, map_mul]
      exact mul_le_one' (v.valuation_le_one _) (ha v x hx)
    · have hv' : ∀ y ∈ A, v.valuation K y ≤ 1 := by
        have : v ∉ {w : HeightOneSpectrum (𝓞 K) | ¬ ∀ x ∈ A, w.valuation K x ≤ 1} := by
          simpa [F] using hv
        simpa using this
      rw [map_mul]
      exact mul_le_one' (v.valuation_le_one _) (hv' x hx)
  set M : ℝ := ∑ τ : K →+* ℂ, ‖τ (d : K)‖ with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun τ _ => norm_nonneg _)
  have hfin := NumberField.Embeddings.finite_of_norm_le K ℂ (M * R)
  refine (hfin.image (fun y => (d : K)⁻¹ * y)).subset ?_
  intro x hx
  refine ⟨(d : K) * x, ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K _ (hval x hx)
    rw [← hy]
    exact (NumberField.RingOfIntegers.isIntegral_coe y)
  · intro τ
    rw [map_mul, norm_mul]
    have h1 : ‖τ (d : K)‖ ≤ M :=
      Finset.single_le_sum (f := fun τ : K →+* ℂ => ‖τ (d : K)‖) (fun τ _ => norm_nonneg _) (Finset.mem_univ τ)
    exact mul_le_mul h1 (hR x hx τ) (norm_nonneg _) hM0
  · simp only
    rw [← mul_assoc, inv_mul_cancel₀ hdK, one_mul]

end GlobalTheory.BddFinite
end

section

open NumberField IsDedekindDomain Filter

namespace GlobalTheory.BCT.SuppFin

theorem exists_ne_zero_intValuation_le_of_finset {E : Type} [Field E] [NumberField E]
    (T : Finset (HeightOneSpectrum (𝓞 E))) (n : HeightOneSpectrum (𝓞 E) → ℕ) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ v ∈ T, v.intValuation d ≤ WithZero.exp (-(n v : ℤ)) := by
  classical
  have hJ : (∏ v ∈ T, v.asIdeal ^ n v) ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    exact fun v _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact v.ne_bot)
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  exact ⟨d, hd0, fun v hv => (v.intValuation_le_pow_iff_mem d (n v)).mpr
    ((Ideal.prod_le_inf.trans (Finset.inf_le hv)) hd)⟩

theorem finite_of_valuation_bounded_of_norm_le_one :
    ∀ (E : Type) [Field E] [NumberField E] (X : Set E),
      (∀ w : HeightOneSpectrum (𝓞 E), ∃ N : ℤ, ∀ a ∈ X, w.valuation E a ≤ WithZero.exp N) →
      (∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ a ∈ X, w.valuation E a ≤ 1) →
      (∀ a ∈ X, ∀ τ : E →+* ℂ, ‖τ a‖ ≤ 1) → X.Finite := by
  intro E _ _ X hN hcof hτ
  classical
  choose N hN using hN
  have hTf := Filter.eventually_cofinite.1 hcof
  obtain ⟨d, hd0, hd⟩ := exists_ne_zero_intValuation_le_of_finset (E := E) hTf.toFinset
    (fun w => (N w).toNat)
  set d' : E := algebraMap (𝓞 E) E d with hd'
  have hd'0 : d' ≠ 0 := by
    rw [hd']; exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).2 hd0
  set B : ℝ := ∑ τ : E →+* ℂ, ‖τ d'‖ with hB
  have hval : ∀ a ∈ X, ∀ w : HeightOneSpectrum (𝓞 E), w.valuation E (d' * a) ≤ 1 := by
    intro a ha w
    rw [map_mul, hd', HeightOneSpectrum.valuation_of_algebraMap]
    by_cases hw : w ∈ hTf.toFinset
    · have h1 := hd w hw
      have h2 := hN w a ha
      have h3 : w.intValuation d ≤ WithZero.exp (-(N w)) :=
        h1.trans (WithZero.exp_le_exp.2 (by omega))
      calc w.intValuation d * w.valuation E a ≤ WithZero.exp (-(N w)) * WithZero.exp (N w) :=
            mul_le_mul' h3 h2
        _ = 1 := by rw [← WithZero.exp_add]; simp
    · have h2 : ∀ a ∈ X, w.valuation E a ≤ 1 := by
        simpa [Set.Finite.mem_toFinset] using hw
      exact mul_le_one' (w.intValuation_le_one d) (h2 a ha)
  have himg : (fun x => d' * x) '' X ⊆
      {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ B} := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨?_, fun φ => ?_⟩
    · obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E (d' * a) (hval a ha)
      show IsIntegral ℤ (d' * a)
      rw [← hr]
      exact RingOfIntegers.isIntegral_coe r
    · show ‖φ (d' * a)‖ ≤ B
      rw [map_mul, norm_mul]
      calc ‖φ d'‖ * ‖φ a‖ ≤ ‖φ d'‖ * 1 :=
            mul_le_mul_of_nonneg_left (hτ a ha φ) (norm_nonneg _)
        _ = ‖φ d'‖ := mul_one _
        _ ≤ B := Finset.single_le_sum (f := fun τ : E →+* ℂ => ‖τ d'‖)
              (fun _ _ => norm_nonneg _) (Finset.mem_univ φ)
  exact Set.Finite.of_finite_image ((NumberField.Embeddings.finite_of_norm_le E ℂ B).subset himg)
    (fun x _ y _ hxy => mul_left_cancel₀ hd'0 hxy)

end GlobalTheory.BCT.SuppFin
end

section

open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

theorem integrable_sq_pow_mul_iteratedFDeriv_schwartz
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : SchwartzMap E F) (i j : ℕ) :
    Integrable (fun z => (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2) μ := by
  have hint : Integrable (fun z => ‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) μ :=
    SchwartzMap.integrable_pow_mul_iteratedFDeriv μ f i j
  set C := SchwartzMap.seminorm ℝ i j f
  refine (hint.const_mul C).mono' ?_ ?_
  · exact (hint.aestronglyMeasurable.aemeasurable.pow_const 2).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun z => ?_)
    have h0 : 0 ≤ ‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖ := by positivity
    have hC : ‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖ ≤ C := SchwartzMap.le_seminorm ℝ i j f z
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), sq]
    exact mul_le_mul_of_nonneg_right hC h0

end GlobalTheory
end

section

open MeasureTheory

namespace GlobalTheory


open Real in
theorem schwartz_eq_fourier_synthesis :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (m : SchwartzMap V ℂ),
    ∃ (d : ℕ) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] V →L[ℝ] ℝ) (h : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ),
    ∀ x, m x = ∫ ξ, h ξ * Complex.exp (Complex.I * (A ξ x : ℂ)) := by
  intro V _ _ _ m
  let e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) := toEuclidean
  let m' : SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm m
  let A : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V →L[ℝ] ℝ :=
    (2 * π) • (((ContinuousLinearMap.compL ℝ V _ ℝ).flip (e : V →L[ℝ] _)).comp (innerSL ℝ))
  have hA : ∀ ξ x, A ξ x = 2 * π * inner ℝ ξ (e x) := by
    intro ξ x
    simp [A]
  refine ⟨Module.finrank ℝ V, A, (FourierTransform.fourier m' : SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ), fun x => ?_⟩
  have h1 : m x = m' (e x) := by
    simp [m']
  have h2 := congrArg (fun f : SchwartzMap _ ℂ => f (e x)) (FourierTransform.fourierInv_fourier_eq (F := SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ℂ) m')
  rw [h1, ← h2, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  congr 1
  ext ξ
  rw [hA, smul_eq_mul, mul_comm]
  congr 2
  push_cast
  ring

end GlobalTheory
end
