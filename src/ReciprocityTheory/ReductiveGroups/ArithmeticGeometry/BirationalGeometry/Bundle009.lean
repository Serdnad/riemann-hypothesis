module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle001

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def segQ (P : Ideal (MRing ι)) (i : (k : K) → ι k) : MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal P :=
  Ideal.Quotient.mk _ (segMon i)

private lemma rename_inl_aeval_mul_prod_X_inr_pow_eq_of_support {r : ℕ} {S : Type} [Fintype S] (c : S → ℕ)
    (H : MvPolynomial (Fin r ⊕ S) ℚ) (hc : ∀ m ∈ H.support, ∀ s, m (Sum.inr s) = c s) :
    rename Sum.inl (aeval (Sum.elim (X : Fin r → MvPolynomial (Fin r) ℚ) 1) H) *
      ∏ s, (X (Sum.inr s) : MvPolynomial (Fin r ⊕ S) ℚ) ^ c s = H := by
  classical
  conv_rhs => rw [H.as_sum]
  conv_lhs => rw [H.as_sum]

  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type]
  simp only [map_mul, map_prod, map_pow, aeval_C, aeval_X, Sum.elim_inl, Sum.elim_inr,
    Pi.one_apply, one_pow, Finset.prod_const_one, mul_one, rename_C, rename_X, algebraMap_eq,
    hc m hm, mul_assoc]

private lemma aeval_sumElim_one_eq_aeval_aeval_sumElim_X_one {r : ℕ} {S : Type} {B : Type*} [CommRing B] [Algebra ℚ B]
    (a : Fin r → B) (H : MvPolynomial (Fin r ⊕ S) ℚ) :
    aeval (Sum.elim a 1) H = aeval a (aeval (Sum.elim (X : Fin r → MvPolynomial (Fin r) ℚ) 1) H) := by
  have hf : (fun i : Fin r ⊕ S => aeval a (Sum.elim (X : Fin r → MvPolynomial (Fin r) ℚ) 1 i)) =
      Sum.elim a (1 : S → B) := by
    funext i
    cases i <;> simp
  rw [← AlgHom.comp_apply, comp_aeval, hf]

theorem algebraicIndependent_sumElim (P : Ideal (MRing ι)) (hP : P.IsPrime) (hH : IsHorizontal P)
    (hhom : IsMultiHomogIdeal P) (k0 : K) (i0 : (k : K) → ι k)
    (hi0 : ∀ k, (X ⟨k, i0 k⟩ : MRing ι) ∉ P) {r : ℕ} (L : Fin r → ((k : K) → ι k) → ℚ)
    (hind : AlgebraicIndependent ℚ (forms (segQ P) L)) :
    AlgebraicIndependent ℚ (Sum.elim (forms (segQ P) L)
      (fun k' : {k // k ≠ k0} => Ideal.Quotient.mk (qIdeal P) (X ⟨k'.1, i0 k'.1⟩))) := by
  classical
  have : IsDomain (MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal P) := isDomain_qQuot P hP hH
  set b : {k // k ≠ k0} → MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal P :=
    fun k' => Ideal.Quotient.mk (qIdeal P) (X ⟨k'.1, i0 k'.1⟩) with hbdef
  let yt : Fin r ⊕ {k // k ≠ k0} → MvPolynomial (Σ k, ι k) ℚ :=
    Sum.elim (fun j => ∑ t, L j t • segMon t) (fun k' => X ⟨k'.1, i0 k'.1⟩)
  have hyt : (fun e => Ideal.Quotient.mkₐ ℚ (qIdeal P) (yt e)) = Sum.elim (forms (segQ P) L) b := by
    funext e
    cases e with
    | inl j => simp [yt, forms, segQ, map_sum, Ideal.Quotient.mkₐ_eq_mk]
    | inr k' => simp [yt, b, Ideal.Quotient.mkₐ_eq_mk]
  have hhomY : ∀ e, IsWeightedHomogeneous (blkWt (ι := ι)) (yt e) (sWt k0 r e) := by
    rintro (j | k')
    · have hmem : (∑ t, L j t • segMon t) ∈
          weightedHomogeneousSubmodule ℚ (blkWt (ι := ι)) oneK :=
        Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (segMon_isWeightedHomogeneous t)
      exact hmem
    · exact isWeightedHomogeneous_X ℚ (blkWt (ι := ι)) ⟨k'.1, i0 k'.1⟩
  have hb : ∀ k', b k' ≠ 0 := by
    intro k' h
    rw [hbdef, Ideal.Quotient.eq_zero_iff_mem] at h
    exact hi0 k'.1 (mem_of_qmap_mem_qIdeal P hP hH (by simpa using h))
  have hev : ∀ G, aeval (Sum.elim (forms (segQ P) L) b) G =
      Ideal.Quotient.mk (qIdeal P) (aeval (R := ℚ) yt G) := by
    intro G
    rw [← hyt, ← comp_aeval, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [algebraicIndependent_iff]
  intro H hH0
  have hmem : aeval (R := ℚ) yt H ∈ qIdeal P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hev]
    exact hH0
  have key : ∀ δ, weightedHomogeneousComponent (sWt k0 r) δ H = 0 := by
    intro δ
    have hHd : IsWeightedHomogeneous (sWt k0 r) (weightedHomogeneousComponent (sWt k0 r) δ H) δ :=
      weightedHomogeneousComponent_isWeightedHomogeneous _ _
    have hcomp := weightedHomogeneousComponent_mem_of_mem ℚ (blkWt (ι := ι))
      (qIdeal_isHomogeneous P hhom) hmem δ
    rw [component_aeval (sWt k0 r) yt hhomY H δ] at hcomp
    have h0 : aeval (Sum.elim (forms (segQ P) L) b) (weightedHomogeneousComponent (sWt k0 r) δ H) = 0 := by
      rw [hev, Ideal.Quotient.eq_zero_iff_mem]
      exact hcomp
    by_contra hne
    obtain ⟨n0, hn0⟩ := Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.mp hne)
    rw [aeval_sumElim_factor k0 hHd hn0] at h0
    have hprod : (∏ k', b k' ^ n0 (Sum.inr k')) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k' _ => pow_ne_zero _ (hb k')
    have h1 := (mul_eq_zero.mp h0).resolve_left hprod
    rw [aeval_sumElim_one_eq_aeval_aeval_sumElim_X_one] at h1
    have h2 := algebraicIndependent_iff.mp hind _ h1
    apply hne
    rw [← rename_inl_aeval_mul_prod_X_inr_pow_eq_of_support (fun s => n0 (Sum.inr s))
      (weightedHomogeneousComponent (sWt k0 r) δ H) ?_, h2, map_zero, zero_mul]
    intro m hm s
    exact inr_eq_of_weight_eq k0 ((hHd (mem_support_iff.mp hm)).trans
      (hHd (mem_support_iff.mp hn0)).symm) s
  ext n
  have := congrArg (AddMonoidAlgebra.coeff · n) (key (Finsupp.weight (sWt k0 r) n))
  rw [coeff_weightedHomogeneousComponent, if_pos rfl] at this
  simpa using this

theorem forms_not_algebraicIndependent (P : Ideal (MRing ι)) (e : ℕ) (hP : IsArithVar P (e + 1))
    {r : ℕ} (hr : e + 1 < r) (L : Fin r → ((k : K) → ι k) → ℚ) :
    ¬ AlgebraicIndependent ℚ (forms (segQ P) L) := by
  classical
  intro hind
  obtain ⟨hne, ⟨hprime, hhom, hrel⟩, hH, hdim⟩ := hP
  obtain ⟨k0⟩ := hne
  choose i0 hi0 using hrel
  have hall := algebraicIndependent_sumElim P hprime hH hhom k0 i0 hi0 L hind
  set n := Fintype.card (Fin r ⊕ {k // k ≠ k0})
  have hall' := hall.comp _ (Fintype.equivFin (Fin r ⊕ {k // k ≠ k0})).symm.injective
  have hle := succ_le_ringKrullDim_of_algebraicIndependent P hprime hH _ hall'
  rw [hdim] at hle
  have hle' : n + 1 ≤ e + 1 + Fintype.card K := by exact_mod_cast hle
  have hcard : n + 1 = r + Fintype.card K := by
    have h1 : Fintype.card {k // k ≠ k0} = Fintype.card K - 1 := by
      simp [Fintype.card_subtype_compl]
    have h2 : 0 < Fintype.card K := Fintype.card_pos_iff.mpr ⟨k0⟩
    simp only [n, Fintype.card_sum, Fintype.card_fin, h1]
    omega
  omega

end

end ReciprocityTheory.ChartRestriction.G.Geo
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  [∀ k, DecidableEq (ι k)]

variable (ι) in
def segMono (i : (k : K) → ι k) : MvPolynomial (Σ k, ι k) ℂ := ∏ k, X ⟨k, i k⟩

theorem eval_segMono (i : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) : eval z (segMono ι i) = segre z i := by
  simp [segMono, segre, map_prod]

theorem segMono_homog (i : (k : K) → ι k) :
    IsWeightedHomogeneous (blkW ι) (segMono ι i) (fun _ => 1) := by
  have := IsWeightedHomogeneous.prod (w := blkW ι) Finset.univ
    (fun k => (X ⟨k, i k⟩ : MvPolynomial (Σ k, ι k) ℂ))
    (fun k => blkW ι ⟨k, i k⟩) (fun k _ => isWeightedHomogeneous_X ℂ _ _)
  unfold segMono
  convert this using 1
  funext k'
  simp [blkW, Finset.sum_apply, Pi.single_apply]

variable {e : ℕ}

def psiPoly (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (j : Fin (e + 1)) :
    MvPolynomial (Σ k, ι k) ℂ :=
  ∑ i, C (Ψ (fun i' => if i = i' then 1 else 0) j) * segMono ι i

theorem eval_psiPoly (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (j : Fin (e + 1))
    (z : (Σ k, ι k) → ℂ) : eval z (psiPoly Ψ j) = Ψ (segre z) j := by
  have hs : segre z = ∑ i, segre z i • (fun i' => if i = i' then (1 : ℂ) else 0) := by
    funext i'
    simp [Finset.sum_apply]

  simp only [psiPoly, map_sum, map_mul, eval_C, eval_segMono]
  conv_rhs => rw [hs]

  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem psiPoly_homog (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (j : Fin (e + 1)) :
    IsWeightedHomogeneous (blkW ι) (psiPoly Ψ j) (fun _ => 1) := by
  have hmem : psiPoly Ψ j ∈ weightedHomogeneousSubmodule ℂ (blkW ι) (fun _ => 1) := by
    unfold psiPoly
    refine Submodule.sum_mem _ (fun i _ => ?_)
    rw [C_mul']
    exact Submodule.smul_mem _ _ ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr (segMono_homog i))
  exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp hmem

variable (ι) in
def idealC (P : Ideal (MRing ι)) : Ideal (MvPolynomial (Σ k, ι k) ℂ) :=
  Ideal.map (map (Int.castRingHom ℂ)) P

theorem eval_idealC {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) {f}
    (hf : f ∈ idealC ι P) : eval z f = 0 := by
  have hle : idealC ι P ≤ RingHom.ker (eval z) := by
    rw [idealC, Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, RingHom.mem_ker]
    exact hz.2 g hg
  exact hle hf

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem idealC_homog {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) :
    (idealC ι P).IsHomogeneous (weightedHomogeneousSubmodule ℂ (blkW ι)) := by
  obtain ⟨S, hS, rfl⟩ := hP
  rw [idealC, Ideal.map_span]
  apply Ideal.homogeneous_span
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨a, ha⟩ := hS g hg
  exact ⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr (isWeightedHomogeneous_map_of_isMultiHomog ha)⟩

theorem segre_rel {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (hΨ : IsGoodProj P Ψ) (i : (k : K) → ι k) :
    ∃ r : ℕ, 0 < r ∧ ∃ G : Fin (e + 1) → MvPolynomial ((k : K) → ι k) ℂ,
      (∀ j, (G j).totalDegree ≤ r - 1) ∧
      ∀ z ∈ mcPts P, segre z i ^ r = ∑ j, Ψ (segre z) j * eval (segre z) (G j) := by
  classical
  set J : Ideal (MvPolynomial (Σ k, ι k) ℂ) := idealC ι P ⊔ Ideal.span (Set.range (psiPoly Ψ)) with hJ
  have hvan : segMono ι i ∈ MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ J) := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro z hz0
    rw [MvPolynomial.mem_zeroLocus_iff] at hz0
    have hz : ∀ p ∈ J, eval z p = 0 := fun p hp => hz0 p hp
    change eval z (segMono ι i) = 0
    by_contra hne
    have hmc : z ∈ mcPts P := by
      refine ⟨fun k => ⟨i k, ?_⟩, fun f hf => ?_⟩
      · intro h0
        apply hne
        rw [eval_segMono]
        exact Finset.prod_eq_zero (Finset.mem_univ k) h0
      · exact hz _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf))
    apply hΨ z hmc
    funext j
    have := hz (psiPoly Ψ j) (Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩))
    rw [eval_psiPoly] at this
    exact this
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hvan
  obtain ⟨n, hn⟩ := hvan
  have hn1 : segMono ι i ^ (n + 1) ∈ J := by
    rw [pow_succ]
    exact J.mul_mem_right _ hn
  obtain ⟨g, hg, a, ha, hga⟩ := Submodule.mem_sup.mp hn1
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp ha
  have hcomp : ∀ j, ∃ G : MvPolynomial ((k : K) → ι k) ℂ, G.totalDegree ≤ n ∧ ∀ z : (Σ k, ι k) → ℂ,
      eval z (weightedHomogeneousComponent (blkW ι) (fun _ => n) (c j)) = eval (segre z) G :=
    fun j => diag_of_homog n (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  choose G hG1 hG2 using hcomp
  refine ⟨n + 1, Nat.succ_pos n, G, fun j => by simpa using hG1 j, ?_⟩
  intro z hz
  have hD : (fun _ : K => n + 1) = (fun _ : K => n) + (fun _ : K => 1) := by
    funext k; simp
  have hseg : weightedHomogeneousComponent (blkW ι) (fun _ : K => n + 1) (segMono ι i ^ (n + 1)) =
      segMono ι i ^ (n + 1) := by
    have hh := (segMono_homog (ι := ι) i).pow (n + 1)
    have hh' : (n + 1) • (fun _ : K => (1 : ℕ)) = fun _ : K => n + 1 := by funext k; simp
    rw [hh'] at hh
    exact weightedHomogeneousComponent_eq_self hh
  have hgc : weightedHomogeneousComponent (blkW ι) (fun _ : K => n + 1) g ∈ idealC ι P := by
    have h := (idealC_homog hP) (fun _ : K => n + 1) hg
    rw [← weightedDecomposition.decompose'_apply ℂ (blkW ι) g (fun _ : K => n + 1)]
    exact h
  have hterm : ∀ j, weightedHomogeneousComponent (blkW ι) (fun _ : K => n + 1) (c j * psiPoly Ψ j) =
      weightedHomogeneousComponent (blkW ι) (fun _ : K => n) (c j) * psiPoly Ψ j := by
    intro j
    rw [hD]
    exact comp_mul_homog (psiPoly_homog Ψ j) (c j) _
  have heq := congrArg (weightedHomogeneousComponent (blkW ι) (fun _ : K => n + 1)) hga

  rw [hseg, map_add (f := _), ← hc, map_sum] at heq
  simp only [hterm] at heq
  have hev := congrArg (eval z) heq

  rw [map_add (f := _), map_sum, eval_idealC hz hgc, zero_add, map_pow, eval_segMono] at hev
  rw [← hev]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_mul, hG2, eval_psiPoly, mul_comm]

theorem fibreFinite : FibreFiniteStatement := by
  intro K _ ι _ P e Ψ hP hΨ y
  classical
  choose r hr G hG hrel using fun i => segre_rel hP.2.1.2.1 Ψ hΨ i
  let H : ((k : K) → ι k) → MvPolynomial ((k : K) → ι k) ℂ := fun i =>
    ∑ j, C ((Fin.cons 1 y : Fin (e + 1) → ℂ) j) * G i j
  refine (fibSys_finite r H (fun i => ?_)).subset ?_
  · refine lt_of_le_of_lt ((totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_))
      (Nat.sub_lt (hr i) one_pos)
    exact (totalDegree_mul _ _).trans (by simpa using hG i j)
  · rintro w ⟨z, hz, rfl, hΨz⟩ i
    rw [hrel i z hz, hΨz]
    simp [H]

end ReciprocityTheory.ChartRestriction.G.Geo
end
end
