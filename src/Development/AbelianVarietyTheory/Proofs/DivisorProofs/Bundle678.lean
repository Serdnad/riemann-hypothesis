module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle640
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.TotallySplit
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle037
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle637
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle334
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContCxOfDegreewise
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle649
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle639
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Artinian.Instances
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003

@[expose] public section

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.sum_realEmbeddings_eq_trace_totallyReal : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (y : F), ∑ i : Emb F, ((i y : ℝ) : ℂ) = ((Algebra.trace ℚ F y : ℚ) : ℂ) := by
  first | exact @GlobalTheory.HilbFam.sum_realEmb_eq_trace | exact GlobalTheory.HilbFam.sum_realEmb_eq_trace | (intros; apply GlobalTheory.HilbFam.sum_realEmb_eq_trace <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem torusPair_pow_eq_one_iff {F : Type} [Field F] [Finite F] (n : ℕ) (α : AlgebraicClosure F) (h0 : α ≠ 0) :
    α ^ (Nat.card F ^ n - 1) = 1 ↔ (minpoly F α).natDegree ∣ n := by
  have hi : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  rw [(minpoly.irreducible hi).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X, minpoly.dvd_iff]
  have hq : 0 < Nat.card F ^ n := pow_pos Nat.card_pos _
  simp only [map_sub, map_pow, aeval_X, sub_eq_zero]
  obtain ⟨k, hk⟩ : ∃ k, Nat.card F ^ n = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hq).symm⟩
  rw [hk, Nat.add_sub_cancel, pow_succ]
  constructor
  · intro h; rw [h, one_mul]
  · intro h; exact mul_right_cancel₀ h0 (h.trans (one_mul α).symm)

theorem torusPair_finite_monic {F : Type} [Field F] [Finite F] (n : ℕ) :
    {P : F[X] | P.Monic ∧ P.natDegree = n ∧ P.coeff 0 ≠ 0}.Finite := by
  have : Finite (Polynomial.degreeLT F (n + 1)) := Finite.of_equiv _ (degreeLTEquiv F (n + 1)).symm.toEquiv
  have h : (Polynomial.degreeLT F (n + 1) : Set F[X]).Finite := Set.toFinite _
  refine h.subset fun P hP => ?_
  simp only [SetLike.mem_coe, mem_degreeLT]
  exact (degree_le_of_natDegree_le hP.2.1.le).trans_lt (by exact_mod_cast Nat.lt_succ_self n)

theorem torusPair_finite_torus {F : Type} [Field F] [Finite F] (n : ℕ) (hn : 0 < n) :
    {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}.Finite := by
  have hq : 1 < Nat.card F ^ n := Nat.one_lt_pow hn.ne' Finite.one_lt_card
  refine (Polynomial.nthRootsFinset (Nat.card F ^ n - 1) (1 : AlgebraicClosure F)).finite_toSet.subset
    fun α hα => ?_
  exact Finset.mem_coe.2 ((Polynomial.mem_nthRootsFinset (by omega) _).2 hα)

theorem torusPair_mangoldt_pow {F : Type} [Field F] (s : F[X] → ℂ) (f : F[X]) (hf : f.Monic)
    (hirr : Irreducible f) (r : ℕ) (hr : 0 < r) : mangoldt s (f ^ r) = s f := by
  have hset : {g : F[X] | g.Monic ∧ Irreducible g ∧ ∃ r' : ℕ, 0 < r' ∧ f ^ r = g ^ r'} = {f} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hg, hgi, r', hr', he⟩
      have h1 : g ∣ f ^ r := he ▸ dvd_pow_self g hr'.ne'
      have h2 : g ∣ f := hgi.prime.dvd_of_dvd_pow h1
      exact eq_of_monic_of_associated hg hf (hgi.associated_of_dvd hirr h2)
    · rintro rfl
      exact ⟨hf, hirr, r, hr, rfl⟩
  rw [mangoldt, hset, finsum_mem_singleton]

theorem torusPair_mangoldt_sum (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (n k : ℕ)
    (S : F[X] → ℂ) (hn : 0 < n) :
    ∑ᶠ P ∈ {P : F[X] | P.Monic ∧ P.natDegree = n ∧ P.coeff 0 ≠ 0}, mangoldt (rootSum θ k) P * star (S P) =
      ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1},
        θ α ^ k * star (S (minpoly F α ^ (n / (minpoly F α).natDegree))) := by
  have hq : 1 < Nat.card F ^ n := Nat.one_lt_pow hn.ne' Finite.one_lt_card
  have hi : ∀ α : AlgebraicClosure F, IsIntegral F α := fun α => Algebra.IsIntegral.isIntegral α
  have hne : ∀ α : AlgebraicClosure F, α ^ (Nat.card F ^ n - 1) = 1 → α ≠ 0 := by
    rintro α h rfl
    rw [zero_pow (by omega)] at h
    exact zero_ne_one h
  rw [finsum_mem_eq_finite_toFinset_sum _ (torusPair_finite_monic n),
    finsum_mem_eq_finite_toFinset_sum _ (torusPair_finite_torus n hn),
    ← Finset.sum_fiberwise_of_maps_to (s := (torusPair_finite_torus (F := F) n hn).toFinset)
      (t := (torusPair_finite_monic (F := F) n).toFinset)
      (g := fun α => minpoly F α ^ (n / (minpoly F α).natDegree))]
  swap
  · intro α hα
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hα ⊢
    have hm := minpoly.monic (hi α)
    refine ⟨hm.pow _, ?_, ?_⟩
    · rw [hm.natDegree_pow, Nat.div_mul_cancel ((torusPair_pow_eq_one_iff n α (hne α hα)).1 hα)]
    · rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero]
      exact pow_ne_zero _ (minpoly.coeff_zero_ne_zero (hi α) (hne α hα))
  refine Finset.sum_congr rfl fun P hP => ?_
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hP
  obtain ⟨hP, hd, h0⟩ := hP
  by_cases hex : ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m
  swap
  · have hempty : {f : F[X] | f.Monic ∧ Irreducible f ∧ ∃ m : ℕ, 0 < m ∧ P = f ^ m} = ∅ := by
      ext f
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hf, hirr, m, hm, rfl⟩
      exact hex ⟨f, m, hf, hirr, hm, rfl⟩
    rw [mangoldt, hempty, finsum_mem_empty, zero_mul]
    refine (Finset.sum_eq_zero fun α hα => ?_).symm
    exfalso
    obtain ⟨hα1, hα2⟩ := Finset.mem_filter.1 hα
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hα1
    have hdv := (torusPair_pow_eq_one_iff n α (hne α hα1)).1 hα1
    exact hex ⟨minpoly F α, n / (minpoly F α).natDegree, minpoly.monic (hi α), minpoly.irreducible (hi α),
      Nat.div_pos (Nat.le_of_dvd hn hdv) (minpoly.natDegree_pos (hi α)), hα2.symm⟩
  obtain ⟨f, m, hf, hirr, hm, rfl⟩ := hex
  rw [hf.natDegree_pow] at hd
  have hdiv : n / f.natDegree = m := by
    rw [← hd, Nat.mul_div_cancel _ hirr.natDegree_pos]
  have hmp : ∀ α : AlgebraicClosure F, aeval α f = 0 → minpoly F α = f := fun α h =>
    (minpoly.eq_of_irreducible_of_monic hirr h hf).symm
  have hfib : Finset.filter (fun α : AlgebraicClosure F => minpoly F α ^ (n / (minpoly F α).natDegree) = f ^ m)
      (torusPair_finite_torus (F := F) n hn).toFinset = (f.map (algebraMap F (AlgebraicClosure F))).roots.toFinset := by
    ext α
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Multiset.mem_toFinset]
    rw [mem_roots (hf.map _).ne_zero, IsRoot.def, eval_map_algebraMap]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : n / (minpoly F α).natDegree ≠ 0 :=
        (Nat.div_pos (Nat.le_of_dvd hn ((torusPair_pow_eq_one_iff n α (hne α h1)).1 h1))
          (minpoly.natDegree_pos (hi α))).ne'
      have h4 := congrArg (aeval α) h2
      rw [map_pow, map_pow, minpoly.aeval, zero_pow h3] at h4
      exact pow_eq_zero_iff hm.ne' |>.1 h4.symm
    · intro h
      have hα : α ≠ 0 := by
        rintro rfl
        apply h0
        rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero]
        rw [aeval_def, eval₂_at_zero, map_eq_zero] at h
        rw [h, zero_pow hm.ne']
      rw [torusPair_pow_eq_one_iff n α hα, hmp α h, hdiv]
      exact ⟨Dvd.intro_left _ hd, rfl⟩
  have hsep : f.Separable := PerfectField.separable_of_irreducible hirr
  have hnd : (f.map (algebraMap F (AlgebraicClosure F))).roots.Nodup := nodup_roots hsep.map
  rw [hfib, torusPair_mangoldt_pow _ f hf hirr m hm, rootSum,
    ← Multiset.dedup_eq_self.2 hnd, ← Multiset.toFinset_val, ← Finset.sum_eq_multiset_sum,
    Finset.val_toFinset, Finset.sum_mul]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [Multiset.mem_toFinset, mem_roots (hf.map _).ne_zero, IsRoot.def, eval_map_algebraMap] at hα
  rw [hmp α hα, hdiv]

theorem torusPair_finsum_GL_eq_ipGL (F : Type) [Field F] [Finite F] (m : ℕ) (s S : F[X] → ℂ) :
    ∑ᶠ x : GL (Fin m) F, psiG s m x * star (chG S m x) =
      ipGL (psi s (Fin m → F)) (fun g => S (LinearMap.charpoly g)) := by
  have h : ∀ x : GL (Fin m) F, psiG s m x * star (chG S m x) =
      (fun g => psi s (Fin m → F) g * star (S (LinearMap.charpoly g)))
        (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F)) := by
    intro x; simp [psiG, chG, Matrix.charpoly_toLin']
  rw [finsum_congr h, ipGL, ← finsum_mem_univ]
  apply finsum_mem_eq_of_bijOn (fun x : GL (Fin m) F => Matrix.toLin' (x : Matrix (Fin m) (Fin m) F))
  · refine ⟨fun x _ => ?_, fun x _ y _ hxy => ?_, fun g hg => ?_⟩
    · have := x.isUnit.map (Matrix.toLinAlgEquiv' (R := F) (n := Fin m))
      simpa using this
    · exact Units.ext (Matrix.toLin'.injective hxy)
    · have hu : IsUnit (LinearMap.toMatrix' g) := by
        have := (show IsUnit g from hg).map (LinearMap.toMatrixAlgEquiv' (R := F) (n := Fin m))
        simpa using this
      exact ⟨hu.unit, Set.mem_univ _, by simp⟩
  · intro x _; rfl

theorem psiG_rootSum_pair_chG_eq_sum_torus : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (m k : ℕ) (S : F[X] → ℂ), 0 < m → ((Nat.card F : ℂ) ^ m - 1) * ∑ᶠ x, psiG (rootSum θ k) m x * star (chG S m x) =
      (Nat.card (GL (Fin m) F) : ℂ) * ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ m - 1) = 1},
        θ α ^ k * star (S (minpoly F α ^ (m / (minpoly F α).natDegree))) := by
  intro F _ _ θ m k S hm
  have hadd := (rootSum_isAdditive_and_pow_X_sub_one F θ k).1
  have hq1 : 1 < Nat.card F ^ m := Nat.one_lt_pow hm.ne' Finite.one_lt_card
  have hq : (Nat.card F : ℂ) ^ m - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast hq1.ne'
  rw [torusPair_finsum_GL_eq_ipGL, ipGL_charpoly_eq_finsum_mass, Module.finrank_fin_fun,
    ← torusPair_mangoldt_sum F θ m k S hm]
  have hterm : ∀ P ∈ {P : F[X] | P.Monic ∧ P.natDegree = m ∧ P.coeff 0 ≠ 0},
      mass (psi (rootSum θ k) (Fin m → F)) P * star (S P) =
        (Nat.card (GL (Fin m) F) : ℂ) * (mangoldt (rootSum θ k) P * star (S P)) / ((Nat.card F : ℂ) ^ m - 1) := by
    intro P hP
    obtain ⟨hPm, hPd, -⟩ := hP
    rw [mass_psi_eq_glCard_mul_mangoldt_div F (Fin m → F) (rootSum θ k) hadd P hPm (by simpa using hPd), hPd,
      glCard]
    ring
  rw [finsum_mem_congr rfl hterm, finsum_mem_eq_finite_toFinset_sum _ (torusPair_finite_monic m),
    finsum_mem_eq_finite_toFinset_sum _ (torusPair_finite_monic m), ← Finset.sum_div, ← Finset.mul_sum,
    mul_div_cancel₀ _ hq]

end GlobalTheory.Shin
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RatCrit

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem hankel_pow_mul (a : F) (c : ℕ → F) (n : ℕ) :
    hankel (fun i => a ^ i * c i) n = a ^ (n * (n + 1)) * hankel c n := by
  have hM : (Matrix.of fun i j : Fin (n + 1) => a ^ ((i : ℕ) + j) * c (i + j)) =
      Matrix.diagonal (fun i : Fin (n + 1) => a ^ (i : ℕ)) * (Matrix.of fun i j : Fin (n + 1) => c (i + j)) *
        Matrix.diagonal (fun i : Fin (n + 1) => a ^ (i : ℕ)) := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.of_apply, pow_add]
    ring
  unfold hankel
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]
  have hs : (∑ i : Fin (n + 1), (i : ℕ)) * 2 = n * (n + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => i) (n + 1), Finset.sum_range_id_mul_two]
    simp [mul_comm]
  rw [← hs, pow_mul]
  ring

theorem ord_mul' (v : Place k F) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    ord v (x * y) = ord v x + ord v y := by
  unfold ord
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy)]
  ring

theorem ord_pow' (v : Place k F) (x : F) (m : ℕ) : ord v (x ^ m) = m * ord v x := by
  unfold ord
  rw [map_pow, WithZero.log_pow, nsmul_eq_mul]
  ring

theorem ord_of_eq_one (v : Place k F) {x : F} (h : v.1 x = 1) : ord v x = 0 := by
  simp [ord, h]

end GlobalTheory.RatCrit

namespace GlobalTheory.RatCrit

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem ord_hankel_ge (v : Place k F) (φ : PowerSeries F) (u : F) (e ψ : PowerSeries v.O) (hu : u ≠ 0)
    (he0 : PowerSeries.constantCoeff e ≠ 0)
    (heq : sc v u e * φ = sc v u ψ) (n : ℕ) (hH : hankel (fun i => PowerSeries.coeff i φ) n ≠ 0) :
    ((n * (n + 1) : ℕ) : ℤ) * ord v u - ((2 * (n + 1) : ℕ) : ℤ) * ord v ((PowerSeries.constantCoeff e : v.O) : F) ≤
      ord v (hankel (fun i => PowerSeries.coeff i φ) n) := by
  have hr : ∀ f : PowerSeries F, PowerSeries.rescale u⁻¹ (PowerSeries.rescale u f) = f := by
    intro f; ext m
    simp only [PowerSeries.coeff_rescale, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hu, one_pow, one_mul]
  have h1 : PowerSeries.map v.O.subtype e * PowerSeries.rescale u⁻¹ φ = PowerSeries.map v.O.subtype ψ := by
    have := congrArg (PowerSeries.rescale u⁻¹) heq
    simpa only [sc, RingHom.comp_apply, map_mul, hr] using this
  obtain ⟨z, hz⟩ := GlobalTheory.T.hankelDeterminant_integral_of_quotient v.O F v.O.subtype e ψ (PowerSeries.rescale u⁻¹ φ) n h1
  have h2 : (fun i => PowerSeries.coeff i φ) = fun i => u ^ i * PowerSeries.coeff i (PowerSeries.rescale u⁻¹ φ) := by
    funext i
    rw [PowerSeries.coeff_rescale, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hu, one_pow, one_mul]
  set c : F := ((PowerSeries.constantCoeff e : v.O) : F) with hc
  set H := hankel (fun i => PowerSeries.coeff i φ) n with hHdef
  set H0 := hankel (fun i => PowerSeries.coeff i (PowerSeries.rescale u⁻¹ φ)) n with hH0
  have h3 : H = u ^ (n * (n + 1)) * H0 := by rw [hHdef, h2, hankel_pow_mul]
  have hz' : (z : F) = c ^ (2 * (n + 1)) * H0 := hz
  have h4 : c ^ (2 * (n + 1)) * H = u ^ (n * (n + 1)) * (z : F) := by rw [h3, hz']; ring
  have hH0 : H0 ≠ 0 := by
    intro h; exact hH (by rw [h3, h, mul_zero])
  have hcne : c ≠ 0 := by
    intro h; apply he0; ext; simpa [hc] using h
  have hzne : (z : F) ≠ 0 := by rw [hz']; exact mul_ne_zero (pow_ne_zero _ hcne) hH0
  have hz1 : 0 ≤ ord v (z : F) :=
    ((GlobalTheory.T.functionFieldPlaceOrder_calculus k F v).2.2.1 _ hzne).1 ((Valuation.mem_valuationSubring_iff _ _).1 z.2)
  have h5 := congrArg (ord v) h4
  rw [ord_mul' v (pow_ne_zero _ hcne) hH, ord_mul' v (pow_ne_zero _ hu) hzne, ord_pow', ord_pow'] at h5
  linarith

end GlobalTheory.RatCrit

namespace GlobalTheory.RatCrit

theorem isRat_of_adelic : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (φ : PowerSeries F) (u : Place k F → F) (e ψ : ∀ v : Place k F, PowerSeries v.O), (∀ v, u v ≠ 0) → {v | ord v (u v) ≠ 0}.Finite → 0 < ∑ᶠ v, ord v (u v) → (∀ v, PowerSeries.constantCoeff (e v) ≠ 0) → {v | ¬ IsUnit (PowerSeries.constantCoeff (e v))}.Finite → (∀ v, sc v (u v) (e v) * φ = sc v (u v) (ψ v)) → IsRat φ := by
  intro k F _ _ _ _ _ hFF φ u e ψ hu0 hufin hdeg he0 hefin heq
  classical
  set c : Place k F → F := fun v => ((PowerSeries.constantCoeff (e v) : v.O) : F) with hc
  have hcunit : ∀ v, IsUnit (PowerSeries.constantCoeff (e v)) → v.1 (c v) = 1 := by
    intro v h
    obtain ⟨a, ha⟩ := h
    have h1 := ValuationSubring.valuation_unit v.O a
    rw [ha] at h1
    exact (Valuation.isEquiv_valuation_valuationSubring v.1).eq_one_iff_eq_one.2 h1
  set δ := ∑ᶠ v, ord v (c v) with hδ
  set D := ∑ᶠ v, ord v (u v) with hD
  apply GlobalTheory.T.isRat_of_hankel_eventually_eq_zero F φ ((2 * δ).toNat + 1)
  intro n hn
  by_contra hH
  obtain ⟨hHfin, hHsum⟩ := GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k F hFF _ hH
  set H := hankel (fun i => PowerSeries.coeff i φ) n with hHdef
  let T : Finset (Place k F) := hufin.toFinset ∪ hefin.toFinset ∪ hHfin.toFinset
  have sU : Function.support (fun v => ord v (u v)) ⊆ (T : Set (Place k F)) := by
    intro v hv
    simp only [T, Finset.coe_union, Set.Finite.coe_toFinset]
    exact Or.inl (Or.inl hv)
  have sC : Function.support (fun v => ord v (c v)) ⊆ (T : Set (Place k F)) := by
    intro v hv
    simp only [T, Finset.coe_union, Set.Finite.coe_toFinset]
    refine Or.inl (Or.inr ?_)
    intro h
    exact hv (ord_of_eq_one v (hcunit v h))
  have sH : Function.support (fun v => ord v H) ⊆ (T : Set (Place k F)) := by
    intro v hv
    simp only [T, Finset.coe_union, Set.Finite.coe_toFinset]
    refine Or.inr ?_
    intro h
    exact hv (ord_of_eq_one v h)
  rw [finsum_eq_sum_of_support_subset _ sH] at hHsum
  rw [finsum_eq_sum_of_support_subset _ sC] at hδ
  rw [finsum_eq_sum_of_support_subset _ sU] at hD
  have hsum : ∑ v ∈ T, (((n * (n + 1) : ℕ) : ℤ) * ord v (u v) - ((2 * (n + 1) : ℕ) : ℤ) * ord v (c v)) ≤
      ∑ v ∈ T, ord v H :=
    Finset.sum_le_sum fun v _ => ord_hankel_ge v φ (u v) (e v) (ψ v) (hu0 v) (he0 v) (heq v) n hH
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hD, ← hδ, hHsum] at hsum
  have hn' : 2 * δ + 1 ≤ (n : ℤ) := by
    have := Int.self_le_toNat (2 * δ)
    omega
  have hD1 : 1 ≤ D := hdeg
  push_cast at hsum
  have h6 : (n + 1 : ℤ) * (n * D - 2 * δ) ≤ 0 := by linarith [hsum]
  have h7 : (n : ℤ) * D - 2 * δ ≤ 0 := by
    by_contra h8
    push_neg at h8
    have : (0 : ℤ) < (n + 1 : ℤ) * (n * D - 2 * δ) := mul_pos (by positivity) h8
    linarith
  have h9 : (n : ℤ) ≤ n * D := by nlinarith [(Nat.cast_nonneg n : (0 : ℤ) ≤ n)]
  linarith

end GlobalTheory.RatCrit
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ContLevel

theorem chains_map_f (R : Type) [CommRing R] {E E' : Spc} (φ : E ⟶ E') (k : ℕ) :
    ((chains R).map φ).f (-(k : ℤ)) = (chainsXIso R E k).hom ≫ (free R).map (φ.app (op (SimplexCategory.mk k))) ≫ (chainsXIso R E' k).inv :=
  HomologicalComplex.extendMap_f ((chainsN R).map φ) ComplexShape.embeddingDownNat (i := k) rfl

end GlobalTheory.EtC.ContLevel


open GlobalTheory.EtC.ContLevel in
theorem GlobalTheory.EtC.contCone_of_levelwise : ∀ (R : Type) [CommRing R] (F : Shv R) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Spc) (c : Cone G), (∀ k : SimplexCategoryᵒᵖ, ContCone R F (((evaluation _ PSh).obj k ⋙ disc).mapCone c)) → ContCone R F c := by
  intro R _ F I _ _ G c hG
  obtain ⟨-, hneg, -, -, -, hpos⟩ := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F
  obtain ⟨cl, hsurj, hiff, hzero, hpull⟩ := GlobalTheory.T.etaleSpaceCohomology_presheaf_classes_as_cocycles R F
  refine fun n => GlobalTheory.EtC.cont_cx_of_degreewise R I (G ⋙ chains R) ((chains R).mapCone c) (res R F)
     (fun i p hp => hpos (G.obj i) p hp) (fun p hp => hpos c.pt p hp) hneg ?_ n
  intro p s
  by_cases hp : 0 < p
  · constructor
    · intro t _
      obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
      refine ⟨i, 0, 0, zero_comp, ?_⟩
      have : t = 0 := (hpos c.pt p hp).eq_of_src _ _
      simp [this]
    · intro i u _ _
      refine ⟨i, 𝟙 i, 0, ?_⟩
      have : u = 0 := (hpos (G.obj i) p hp).eq_of_src _ _
      simp [this]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨(-p).toNat, by omega⟩
    have hk := hG (op (SimplexCategory.mk k)) s
    constructor
    · intro t ht
      let t' := (chainsXIso R c.pt k).inv ≫ t
      have ht' : t' ≫ (res R F).d s (s + 1) = 0 := by simp [t', ht]
      obtain ⟨i, y, hy⟩ := hk.1 (cl _ s t' ht')
      obtain ⟨u', hu', rfl⟩ := hsurj _ s y
      obtain ⟨h2, hp2⟩ := hpull (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj c.pt) (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj (G.obj i)) ((c.π.app i).app (op (SimplexCategory.mk k))) s u' hu'
      change pull R (disc.map ((c.π.app i).app (op (SimplexCategory.mk k)))) F s _ = _ at hy
      rw [hp2, hiff] at hy
      obtain ⟨y', hy'⟩ := hy
      refine ⟨i, (chainsXIso R (G.obj i) k).hom ≫ u', (chainsXIso R c.pt k).hom ≫ y', by simp [hu'], ?_⟩
      change ((chains R).map (c.π.app i)).f _ ≫ _ = _
      rw [chains_map_f]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [hy']
      simp [t', Preadditive.comp_add]
    · rintro i u hu ⟨y, hy⟩
      let u' := (chainsXIso R (G.obj i) k).inv ≫ u
      have hu' : u' ≫ (res R F).d s (s + 1) = 0 := by simp [u', hu]
      have hdie : pull R ((((evaluation _ PSh).obj (op (SimplexCategory.mk k)) ⋙ disc).mapCone c).π.app i) F s
          (cl _ s u' hu') = 0 := by
        change pull R (disc.map ((c.π.app i).app _)) F s _ = 0
        obtain ⟨h2, hp2⟩ := hpull (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj c.pt) (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj (G.obj i)) ((c.π.app i).app (op (SimplexCategory.mk k))) s u' hu'
        rw [hp2, ← hzero (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj c.pt) s, hiff]
        refine ⟨(chainsXIso R c.pt k).inv ≫ y, ?_⟩
        change ((chains R).map (c.π.app i)).f _ ≫ u = _ at hy
        rw [chains_map_f] at hy
        rw [zero_add, Category.assoc, ← hy]
        simp [u']
      obtain ⟨k', f, hf⟩ := hk.2 i _ hdie
      change pull R (disc.map ((G.map f).app (op (SimplexCategory.mk k)))) F s _ = 0 at hf
      obtain ⟨h3, hp3⟩ := hpull (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj (G.obj k')) (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj (G.obj i)) ((G.map f).app (op (SimplexCategory.mk k))) s u' hu'
      rw [hp3, ← hzero (((evaluation _ PSh).obj (op (SimplexCategory.mk k))).obj (G.obj k')) s, hiff] at hf
      obtain ⟨y'', hy''⟩ := hf
      refine ⟨k', f, (chainsXIso R (G.obj k') k).hom ≫ y'', ?_⟩
      change ((chains R).map (G.map f)).f _ ≫ u = _
      rw [chains_map_f, zero_add] at *
      simp only [Category.assoc]
      exact congrArg ((chainsXIso R (G.obj k') k).hom ≫ ·) hy''

end
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.etale_leviNonneg_of_chart_plurisubharmonic : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ φ : Y → ℝ, (∀ x ∈ U, ∃ i, x ∈ (A.chart i).source ∧ ContDiffAt ℝ ∞ (φ ∘ (A.chart i).symm) (A.chart i x) ∧ ∀ ξ : Fin n → ℂ, 0 ≤ A.leviAt i φ x ξ) → LeviNonneg n (fun y : U => z y) (fun y : U => φ y) := by
  first | exact @GlobalTheory.OTY.etale_leviNonneg | exact GlobalTheory.OTY.etale_leviNonneg | (intros; apply GlobalTheory.OTY.etale_leviNonneg <;> assumption)
end
