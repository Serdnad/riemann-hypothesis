module

public import Development.EtaleCohomology.EtaleTrace.Bundle003
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
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
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open MvPolynomial

namespace LateralTheory.EtaleTrace.Cov

theorem homRel_aeval_scale (k K : Type) [Field k] [Field K] [Algebra k K] {n : ℕ} (v : Fin n → K)
    (H : MvPolynomial (Fin n) k) (m : ℕ) (hH : H.IsHomogeneous m) :
    aeval (fun j => Polynomial.C (v j) * Polynomial.X) H = Polynomial.C (aeval v H) * Polynomial.X ^ m := by
  classical

  rw [aeval_def, eval₂_eq, aeval_def, eval₂_eq, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : (∑ i ∈ d.support, d i) = m := by
    have := hH (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg, map_mul, map_prod, map_pow]
  rw [IsScalarTower.algebraMap_apply k K (Polynomial K), Polynomial.algebraMap_eq, mul_assoc]

theorem HomRel_of : HomRel := by
  intro k K _ _ _ d hd n hn v
  classical
  set x : Fin n → Polynomial K := fun j => Polynomial.C (v j) * Polynomial.X with hx
  have htr : Algebra.trdeg k (Polynomial K) = Algebra.trdeg k K + 1 := by
    rw [← trdeg_add_eq (R := k) (S := K) (A := Polynomial K), Polynomial.trdeg_of_isDomain]
  have hni : ¬ AlgebraicIndependent k x := by
    intro h
    have h1 := h.cardinalMk_le_trdeg
    rw [htr, Cardinal.mk_fin] at h1
    have h2 : ((n : ℕ) : Cardinal) ≤ ((d + 1 : ℕ) : Cardinal) := by
      push_cast; exact h1.trans (by gcongr)
    have : n ≤ d + 1 := by exact_mod_cast h2
    omega
  rw [algebraicIndependent_iff] at hni
  push Not at hni
  obtain ⟨G, hGx, hG0⟩ := hni
  obtain ⟨m, hm⟩ : ∃ m, homogeneousComponent m G ≠ 0 := by
    by_contra h
    push Not at h
    apply hG0
    rw [← sum_homogeneousComponent G]
    exact Finset.sum_eq_zero fun i _ => h i
  refine ⟨m, homogeneousComponent m G, hm, homogeneousComponent_isHomogeneous m G, ?_⟩
  have hsum : aeval x G = ∑ i ∈ Finset.range (G.totalDegree + 1),
      Polynomial.C (aeval v (homogeneousComponent i G)) * Polynomial.X ^ i := by
    conv_lhs => rw [← sum_homogeneousComponent G]

    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ =>
      homRel_aeval_scale k K v _ i (homogeneousComponent_isHomogeneous i G)
  have hmem : m ∈ Finset.range (G.totalDegree + 1) := by
    rw [Finset.mem_range]
    by_contra h
    exact hm (homogeneousComponent_eq_zero m G (by omega))
  have hc := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p m) (hsum.symm.trans hGx)
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hc
  rwa [Finset.sum_ite_eq, if_pos hmem] at hc

end LateralTheory.EtaleTrace.Cov
end
end

section

noncomputable section
open MvPolynomial

namespace LateralTheory.EtaleTrace.StepPf

lemma eval₂_mul_left {k R σ : Type} [CommSemiring k] [CommSemiring R] (f : k →+* R) (x : σ → R) (r : R)
    {m : ℕ} {F : MvPolynomial σ k} (hF : F.IsHomogeneous m) :
    eval₂ f (fun j => r * x j) F = r ^ m * eval₂ f x F := by
  rw [eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = m := by
    have := hF (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

lemma jet_sub {k K : Type} [Field k] [Field K] [Algebra k K] (a b : K) (c : k) :
    ((a - algebraMap k K c * b), KaehlerDifferential.D k K (a - algebraMap k K c * b)) =
      (a, KaehlerDifferential.D k K a) - (algebraMap k K c) • (b, KaehlerDifferential.D k K b) := by
  ext
  · simp [Algebra.smul_def]
  · simp [Derivation.leibniz]

lemma exists_c {k K : Type} [Field k] [Infinite k] [Field K] [Algebra k K] {n : ℕ}
    (F : MvPolynomial (Fin (n + 1)) k) (hF0 : F ≠ 0) (a : Fin (n + 1) → K) (j0 : Fin (n + 1)) (ha : a j0 ≠ 0) :
    ∃ c : Fin (n + 1) → k, eval c F ≠ 0 ∧ c (Fin.last n) ≠ 0 ∧ ∑ j, a j * algebraMap k K (c j) ≠ 0 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k K, φ (a j0) ≠ 0 := by
    by_contra h
    push Not at h
    exact ha ((Module.forall_dual_apply_eq_zero_iff k (a j0)).mp h)
  set G : MvPolynomial (Fin (n + 1)) k := ∑ j, C (φ (a j)) * X j with hGdef
  have hG : ∀ c, eval c G = φ (∑ j, a j * algebraMap k K (c j)) := by
    intro c

    simp only [hGdef, map_sum, map_mul, eval_C, eval_X]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm (a j), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have hG0 : G ≠ 0 := by
    intro h
    have := hG (Pi.single j0 1)
    rw [h] at this
    simp [Pi.single_apply] at this
    exact hφ this.symm
  have hP : F * X (Fin.last n) * G ≠ 0 := mul_ne_zero (mul_ne_zero hF0 (X_ne_zero _)) hG0
  obtain ⟨c, hc⟩ : ∃ c, eval c (F * X (Fin.last n) * G) ≠ 0 := by
    by_contra h
    push Not at h
    exact hP (MvPolynomial.funext fun x => by simpa using h x)
  simp only [map_mul, eval_X] at hc
  refine ⟨c, ?_, ?_, ?_⟩
  · exact left_ne_zero_of_mul (left_ne_zero_of_mul hc)
  · exact right_ne_zero_of_mul (left_ne_zero_of_mul hc)
  · intro h0
    apply right_ne_zero_of_mul hc
    rw [hG, h0, map_zero]

theorem Step_of : LateralTheory.EtaleTrace.Cov.Step := by
  intro k K _ _ _ _ n v m F hF0 hFh hFv hli
  obtain ⟨a, ha, j0, hj0⟩ := Fintype.not_linearIndependent_iff.mp hli
  obtain ⟨c, hcF, hcl, hcs⟩ := exists_c F hF0 a j0 hj0
  set e : k := (c (Fin.last n))⁻¹ with he
  set d : Fin (n + 1) → k := fun j => e * c j with hd
  have hdl : d (Fin.last n) = 1 := inv_mul_cancel₀ hcl
  have hdF : eval d F ≠ 0 := by
    have h := eval₂_mul_left (RingHom.id k) c e hFh
    change eval₂ (RingHom.id k) d F ≠ 0
    rw [show (fun j => e * c j) = d from rfl] at h
    rw [h]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hcl)) hcF
  set s : K := ∑ j, a j * algebraMap k K (d j) with hsdef
  have hs0 : s ≠ 0 := by
    have : s = algebraMap k K e * ∑ j, a j * algebraMap k K (c j) := by
      simp only [hsdef, hd, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    exact mul_ne_zero ((map_ne_zero _).mpr (inv_ne_zero hcl)) hcs
  set w : Fin n → K := fun j => v j.castSucc - algebraMap k K (d j.castSucc) * v (Fin.last n) with hw
  have hjw : ∀ j, LateralTheory.EtaleTrace.Cov.jet k w j =
      LateralTheory.EtaleTrace.Cov.jet k v j.castSucc - algebraMap k K (d j.castSucc) • LateralTheory.EtaleTrace.Cov.jet k v (Fin.last n) := by
    intro j
    exact jet_sub _ _ _
  have h1 : ∀ j : Fin n, LateralTheory.EtaleTrace.Cov.jet k v j.castSucc =
      LateralTheory.EtaleTrace.Cov.jet k w j + algebraMap k K (d j.castSucc) • LateralTheory.EtaleTrace.Cov.jet k v (Fin.last n) := by
    intro j; rw [hjw]; abel
  have hlast : s • LateralTheory.EtaleTrace.Cov.jet k v (Fin.last n) = -(∑ j : Fin n, a j.castSucc • LateralTheory.EtaleTrace.Cov.jet k w j) := by
    have hs : s = ∑ j : Fin n, a j.castSucc * algebraMap k K (d j.castSucc) + a (Fin.last n) := by
      rw [hsdef, Fin.sum_univ_castSucc, hdl, map_one, mul_one]
    rw [Fin.sum_univ_castSucc] at ha
    simp_rw [h1, smul_add, Finset.sum_add_distrib, smul_smul] at ha
    rw [hs, add_smul, Finset.sum_smul, eq_neg_iff_add_eq_zero, ← ha]
    abel
  refine ⟨w, ?_, ?_, ?_⟩
  · intro j
    refine Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) ?_
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      rw [hjw]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
    · have hL : LateralTheory.EtaleTrace.Cov.jet k v (Fin.last n) ∈ Submodule.span K (Set.range (LateralTheory.EtaleTrace.Cov.jet k w)) := by
        have : LateralTheory.EtaleTrace.Cov.jet k v (Fin.last n) = s⁻¹ • (s • LateralTheory.EtaleTrace.Cov.jet k v (Fin.last n)) := by
          rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
        rw [this, hlast]
        refine Submodule.smul_mem _ _ (Submodule.neg_mem _ (Submodule.sum_mem _ fun j _ => ?_))
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      induction j using Fin.lastCases with
      | last => exact hL
      | cast j =>
        rw [h1]
        exact Submodule.add_mem _ (Submodule.subset_span ⟨j, rfl⟩) (Submodule.smul_mem _ _ hL)
  · intro O hO hk ⟨i, hvi, hvO⟩
    let ι : k →+* O := (algebraMap k K).codRestrict O hk
    let U : Fin (n + 1) → O := fun j => ⟨v j / v i, hvO j⟩
    have hUF : eval₂ ι U F = 0 := by
      apply Subtype.val_injective
      have h := eval₂_comp_left O.subtype ι U F
      change O.subtype (eval₂ ι U F) = 0
      rw [h]
      have h2 : O.subtype.comp ι = algebraMap k K := by ext x; rfl
      have h3 : (O.subtype ∘ U) = fun j => (v i)⁻¹ * v j := by
        funext j; simp [U, div_eq_inv_mul]
      rw [h2, h3, eval₂_mul_left _ _ _ hFh, ← aeval_def, hFv, mul_zero]
    let W : Fin n → O := fun l => U l.castSucc - ι (d l.castSucc) * U (Fin.last n)
    have hWv : ∀ l, (W l : K) = w l / v i := by
      intro l
      simp only [W, U, ι, hw, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, RingHom.codRestrict_apply]
      ring
    by_contra hcon
    push Not at hcon
    have hWm : ∀ l, IsLocalRing.residue O (W l) = 0 := by
      intro l
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨y, hy⟩ := hu.exists_right_inv
      have hval : w l / v i * (y : K) = 1 := by
        rw [← hWv]
        exact congrArg Subtype.val hy
      have hwl : w l ≠ 0 := by
        intro h0; rw [h0, zero_div, zero_mul] at hval; exact zero_ne_one hval
      obtain ⟨j, hj⟩ := hcon l hwl
      apply hj
      have : v j / w l = v j / v i * (y : K) := by
        rw [eq_comm, eq_div_iff hwl]
        calc v j / v i * (y : K) * w l = v j * (w l / v i * (y : K)) := by ring
          _ = v j := by rw [hval, mul_one]
      rw [this]
      exact O.mul_mem (hvO j) y.2
    set π := IsLocalRing.residue O
    set t := π (U (Fin.last n))
    have hπU : (fun j => π (U j)) = fun j => t * (π.comp ι) (d j) := by
      funext j
      induction j using Fin.lastCases with
      | last => rw [hdl, map_one, mul_one]
      | cast l =>
        have := hWm l
        simp only [W, map_sub, map_mul, sub_eq_zero] at this
        rw [this, RingHom.comp_apply, mul_comm]
    have hmain : t ^ m * (π.comp ι) (eval d F) = 0 := by
      have h := eval₂_comp_left π ι U F
      rw [hUF, map_zero] at h
      have h' : (π ∘ U) = fun j => t * (π.comp ι) (d j) := hπU
      rw [h', eval₂_mul_left _ _ _ hFh] at h
      have h4 := eval₂_comp_left (π.comp ι) (RingHom.id k) d F
      rw [RingHom.comp_id] at h4
      rw [h]
      exact congrArg (t ^ m * ·) h4
    have hne : (π.comp ι) (eval d F) ≠ 0 := (map_ne_zero _).mpr hdF
    have ht : t = 0 := pow_eq_zero_iff'.mp ((mul_eq_zero.mp hmain).resolve_right hne) |>.1
    have hUi : π (U i) = 0 := by
      have := congrFun hπU i
      rw [this, ht, zero_mul]
    have : U i = 1 := Subtype.ext (by simp [U, div_self hvi])
    rw [this, map_one] at hUi
    exact one_ne_zero hUi

end LateralTheory.EtaleTrace.StepPf
end
end

section

noncomputable section
open MvPolynomial

namespace LateralTheory.EtaleTrace.Cov

lemma pf_div_mem {k K : Type} [Field k] [Field K] [Algebra k K] {n : ℕ} (v : Fin n → K) (O : Subring K)
    (hk : ∀ c : k, algebraMap k K c ∈ O) (y : K) (hv : ∀ j, v j / y ∈ O) (x : K)
    (hx : x ∈ Submodule.span k (Set.range v)) : x / y ∈ O := by
  induction hx using Submodule.span_induction with
  | mem z hz => obtain ⟨j, rfl⟩ := hz; exact hv j
  | zero => simp
  | add a b _ _ ha hb => rw [add_div]; exact O.add_mem ha hb
  | smul c a _ ha => rw [Algebra.smul_def, mul_div_assoc]; exact O.mul_mem (hk c) ha

lemma pf_finrank {k K : Type} [Field k] [Field K] [Algebra k K] (d : ℕ) (hd : Module.finrank K Ω[K⁄k] = d)
    {n : ℕ} (v : Fin n → K) (hv : Submodule.span K (Set.range (jet k v)) = ⊤) :
    Module.Finite K (K × Ω[K⁄k]) ∧ Module.finrank K (K × Ω[K⁄k]) = d + 1 := by
  have hf : Module.Finite K (K × Ω[K⁄k]) := ⟨by rw [← hv]; exact Submodule.fg_span (Set.finite_range _)⟩
  have : Module.Finite K Ω[K⁄k] := Module.Finite.of_surjective (LinearMap.snd K K Ω[K⁄k]) LinearMap.snd_surjective
  refine ⟨hf, ?_⟩
  rw [Module.finrank_prod, Module.finrank_self, hd]; omega

lemma pf_card {k K : Type} [Field k] [Field K] [Algebra k K] (d : ℕ) (hd : Module.finrank K Ω[K⁄k] = d)
    {n : ℕ} (v : Fin n → K) (hv : Submodule.span K (Set.range (jet k v)) = ⊤) : d + 1 ≤ n := by
  obtain ⟨_, h⟩ := pf_finrank d hd v hv
  have := finrank_range_le_card (R := K) (jet k v)
  have e := congrArg (fun s : Submodule K (K × Ω[K⁄k]) => Module.finrank K s) hv
  simp only [finrank_top] at e
  simp only [Set.finrank, Fintype.card_fin] at this
  omega

theorem Project_of (hStep : Step) (hHom : HomRel) : Project := by
  intro k K _ _ _ _ d hd htr n v hv
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (pf_card d hd v hv)
  induction m with
  | zero =>
    obtain ⟨hf, hr⟩ := pf_finrank d hd v hv
    refine ⟨v, fun i => Submodule.subset_span ⟨i, rfl⟩, hv,
      linearIndependent_of_top_le_span_of_card_eq_finrank hv.ge (by simp [hr]), ?_⟩
    intro O _ _ h; exact h
  | succ m ih =>
    obtain ⟨hf, hr⟩ := pf_finrank d hd v hv
    have hdep : ¬ LinearIndependent K (jet k v) := by
      intro hl
      have := hl.fintype_card_le_finrank
      simp [hr] at this
    obtain ⟨e, F, hF0, hFh, hFv⟩ := hHom k K d htr (d + 1 + (m + 1)) (by omega) v
    obtain ⟨w', hw'k, hw'sp, hw'O⟩ := hStep k K (d + 1 + m) v e F hF0 hFh hFv hdep
    obtain ⟨w, hwk, hwsp, hwli, hwO⟩ := ih w' (hw'sp.trans hv)
    refine ⟨w, fun i => ?_, hwsp, hwli, ?_⟩
    · exact Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hw'k j) (hwk i)
    · intro O hO hk h
      obtain ⟨i, hi, hiO⟩ := hw'O O hO hk h
      obtain ⟨l, hl, hlO⟩ := hwO O hO hk ⟨i, hi, fun j => pf_div_mem v O hk _ hiO _ (hw'k j)⟩
      refine ⟨l, hl, fun j => ?_⟩
      have : v j / w l = (v j / w' i) * (w' i / w l) := by field_simp
      rw [this]; exact O.mul_mem (hiO j) (hlO i)

end LateralTheory.EtaleTrace.Cov
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

theorem finrank_frac_of_stdSmooth (k R K : Type) [Field k] [CommRing R] [IsDomain R] [Field K]
    [Algebra k R] [Algebra R K] [Algebra k K] [IsScalarTower k R K] [IsFractionRing R K] (d : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension d k R] :
    Module.finrank K Ω[K⁄k] = d := by
  have : Algebra.FormallyEtale R K := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors R)
  have : Algebra.IsStandardSmooth k R := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth d
  have : Module.Free R Ω[R⁄k] := Algebra.IsStandardSmooth.free_kaehlerDifferential
  have hr : Module.rank R Ω[R⁄k] = d := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential d
  have hf : Module.finrank R Ω[R⁄k] = d := Module.finrank_eq_of_rank_eq hr
  rw [← (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R K).finrank_eq, Module.finrank_baseChange, hf]

theorem FieldDim_of : FieldDim := by
  intro k _ d X _ p hp
  letI := (kHom p).toAlgebra
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := hp.exists_isStandardSmoothOfRelativeDimension (genericPoint X)
  have hUtop : U = ⊤ := by
    have hs : Subsingleton (PrimeSpectrum k) := inferInstance
    ext y
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    have hy : p.base (genericPoint X) ∈ U := e hx
    exact (show y = p.base (genericPoint X) from hs.elim _ _) ▸ hy
  subst hUtop
  have : Nonempty V := ⟨⟨_, hx⟩⟩
  let ψ : CommRingCat.of k ⟶ Γ(X, V) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ V e
  have hψ : ψ.hom.IsStandardSmoothOfRelativeDimension d := by
    have := hf.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv)
    exact this
  letI : Algebra k Γ(X, V) := ψ.hom.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension d k Γ(X, V) := hψ
  haveI : IsScalarTower k Γ(X, V) X.functionField := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c
    have key : Scheme.Hom.appTop p ≫ X.presheaf.germ ⊤ (genericPoint X) trivial =
        Scheme.Hom.appLE p ⊤ V e ≫ X.germToFunctionField V := by
      rw [Scheme.Hom.appLE, Category.assoc]
      exact (congrArg (Scheme.Hom.app p ⊤ ≫ ·) (X.presheaf.germ_res (homOfLE le_top) (genericPoint X) hx)).symm
    simp only [RingHom.algebraMap_toAlgebra, kHom, ψ]
    have H : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial =
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ V e) ≫ X.germToFunctionField V := by
      rw [Category.assoc, ← key]
    exact congrArg (fun f => CommRingCat.Hom.hom f c) H
  haveI := functionField_isFractionRing_of_isAffineOpen X V hV
  exact finrank_frac_of_stdSmooth k Γ(X, V) X.functionField d

end LateralTheory.EtaleTrace.Cov
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

theorem pn_sep (k : Type) [Field k] (d : ℕ) : IsSeparated (PNto k d) := by
  unfold PNto; infer_instance

theorem algebraMap_field_homogeneousDegreeZero_surjective (k : Type) [Field k] (d : ℕ) :
    Function.Surjective (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k 0)) := by
  rintro ⟨x, hx⟩
  refine ⟨AddMonoidAlgebra.coeff x 0, ?_⟩
  apply Subtype.ext
  have h0 := (MvPolynomial.mem_homogeneousSubmodule 0 x).1 hx
  have h : x = C (AddMonoidAlgebra.coeff x 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 ((MvPolynomial.totalDegree_zero_iff_isHomogeneous _).2 h0)
  show (algebraMap k (MvPolynomial (Fin (d + 1)) k)) (AddMonoidAlgebra.coeff x 0) = x
  conv_rhs => rw [h]
  rfl

instance ft0 (k : Type) [Field k] (d : ℕ) :
    Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k 0) (MvPolynomial (Fin (d+1)) k) := by
  have : IsScalarTower k (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k 0) (MvPolynomial (Fin (d+1)) k) := by
    exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact Algebra.FiniteType.of_restrictScalars_finiteType k _ _

theorem pn_lft (k : Type) [Field k] (d : ℕ) : LocallyOfFiniteType (PNto k d) := by
  unfold PNto
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k 0)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.FiniteType.of_surjective _ (algebraMap_field_homogeneousDegreeZero_surjective k d)
  infer_instance

def PNIntegral : Prop := ∀ (k : Type) [Field k] (d : ℕ), IsIntegral (PN k d)

theorem PNBasic_of (h : PNIntegral) : PNBasic := fun k _ d => ⟨h k d, pn_sep k d, pn_lft k d⟩

end LateralTheory.EtaleTrace.Cov
end
end

section

open CategoryTheory AlgebraicGeometry

namespace LateralTheory.EtaleTrace

theorem PtCover_of : PtCover := by
  intro k _ _ T hT
  obtain ⟨Y, g, hg, y, hy⟩ := (Scheme.geometricFiber k).jointly_surjective T hT (𝟙 (S k))
  have hy' : y ≫ g = 𝟙 (S k) := hy
  have := T.downward_closed hg y
  rwa [hy'] at this

end LateralTheory.EtaleTrace
end
