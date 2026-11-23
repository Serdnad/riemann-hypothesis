module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle024
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle028
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle017
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwMemIwC
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

@[expose] public section

section

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

theorem UpperTheory.V.AlgebraTools.hkSum :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] (b : Bern n q H), b.Faithful → ∀ (ι : Type) [Fintype ι] (a c : ι → MvPolynomial (Fin n) R), IsDual a c →
      ∑ i, b.th (a i) * b.one * b.th (c i) = b.th (NN n q) := by
  intro R _ _ n q H _ _ b hb ι _ a c hd
  classical
  let S : H → Prop := fun h => ∃ e : Perm (Fin n) → MvPolynomial (Fin n) R,
    ∑ u, b.th (e u) * b.T u = h
  have S_zero : S 0 := ⟨0, by simp⟩
  have S_add : ∀ h₁ h₂, S h₁ → S h₂ → S (h₁ + h₂) := by
    rintro h₁ h₂ ⟨e₁, rfl⟩ ⟨e₂, rfl⟩
    refine ⟨e₁ + e₂, ?_⟩
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp [add_mul]
  have S_sub : ∀ h₁ h₂, S h₁ → S h₂ → S (h₁ - h₂) := by
    rintro h₁ h₂ ⟨e₁, rfl⟩ ⟨e₂, rfl⟩
    refine ⟨e₁ - e₂, ?_⟩
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp [sub_mul]
  have S_sum : ∀ {κ : Type} (s : Finset κ) (f : κ → H), (∀ k ∈ s, S (f k)) → S (∑ k ∈ s, f k) :=
    fun s f hf => Finset.sum_induction f S S_add S_zero hf
  have S_th : ∀ x, S (b.th x) := by
    intro x
    refine ⟨fun u => if u = 1 then x else 0, ?_⟩
    rw [Finset.sum_eq_single (1 : Perm (Fin n))]
    · simp [b.T_one]
    · intro u _ hu
      simp [hu]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have S_T : ∀ w h, S h → S (b.T w * h) := by
    rintro w h ⟨e, rfl⟩
    obtain ⟨e', he'⟩ := UpperTheory.V.AlgebraTools.hkSpan R n q H b w e
    exact ⟨e', he'.symm⟩
  have S_thmul : ∀ x h, S h → S (b.th x * h) := by
    rintro x h ⟨e, rfl⟩
    refine ⟨fun u => x * e u, ?_⟩
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [map_mul, mul_assoc]
  have hE : S (∑ i, b.th (a i) * b.one * b.th (c i)) := by
    refine S_sum _ _ fun i _ => ?_
    rw [mul_assoc, Bern.one, Finset.sum_mul]
    exact S_thmul _ _ (S_sum _ _ fun w _ => S_T _ _ (S_th _))
  obtain ⟨e, he⟩ := S_sub _ _ hE (S_th (NN n q))
  have hx : ∀ x, (∑ i, b.th (a i) * b.one * b.th (c i)) * b.th x * b.one
      = b.th (NN n q * x) * b.one := by
    intro x
    rw [Finset.sum_mul, Finset.sum_mul]
    have step : ∀ i, b.th (a i) * b.one * b.th (c i) * b.th x * b.one
        = b.th (a i * dd (c i * (NN n q * x))) * b.one := by
      intro i
      have hs := UpperTheory.V.AlgebraTools.hkSandwich R n q H b hb (c i * x)
      calc b.th (a i) * b.one * b.th (c i) * b.th x * b.one
          = b.th (a i) * (b.one * b.th (c i * x) * b.one) := by
            rw [map_mul]
            simp only [mul_assoc]
        _ = b.th (a i) * (b.th (dd (NN n q * (c i * x))) * b.one) := by rw [hs]
        _ = b.th (a i * dd (c i * (NN n q * x))) * b.one := by
            rw [map_mul, mul_left_comm (NN n q) (c i) x, mul_assoc]

    rw [Finset.sum_congr rfl fun i _ => step i, ← Finset.sum_mul, ← map_sum,
    (UpperTheory.V.AlgebraTools.hkDualExp R n ι a c hd (NN n q * x)).1]
  have he0 := UpperTheory.V.AlgebraTools.hkFaith R n q H b hb e (fun x => by
    rw [he, sub_mul, sub_mul, hx x, ← map_mul, sub_self])
  rw [he0] at he
  simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero] at he
  exact (sub_eq_zero.mp he.symm)
end

section

open IsLocalRing UpperTheory.V.AlgebraTools

private theorem UpperTheory.V.AlgebraTools.generic_kernel_monotone
    (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι]
    (z : Matrix ι ι P) (m : ι → P)
    (h : CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m)) (c d : ι) :
    genKer z m c ≤ genKer z m d := by
  classical
  intro f hf
  haveI hQ : (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)).IsPrime :=
    isPrime_map_C (ι := ι) (maximalIdeal P)
  set Q : Ideal (MvPolynomial ι P) := Ideal.map MvPolynomial.C (maximalIdeal P) with hQdef
  let L := Localization.AtPrime Q
  let J : Ideal L := Ideal.map (algebraMap (MvPolynomial ι P) L) (chartIdeal z m d)
  haveI hJ : J.IsPrime := chartIdeal_localization_isPrime P ι z m h d Q le_rfl
  haveI : IsLocalRing (L ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
  let ψ : MvPolynomial ι P →+* L ⧸ J := (Ideal.Quotient.mk J).comp (algebraMap (MvPolynomial ι P) L)
  let φ : P →+* L ⧸ J := ψ.comp MvPolynomial.C
  have hJle : J ≤ maximalIdeal L := IsLocalRing.le_maximalIdeal hJ.ne_top
  have hψ : ∀ g ∈ chartIdeal z m d, ψ g = 0 := fun g hg =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hg)
  haveI : IsLocalHom φ := by
    constructor
    intro p hp
    by_contra hpu
    have hpm : p ∈ maximalIdeal P := (IsLocalRing.mem_maximalIdeal p).2 hpu
    have hC : (MvPolynomial.C p : MvPolynomial ι P) ∈ Q := Ideal.mem_map_of_mem _ hpm
    have hL : algebraMap (MvPolynomial ι P) L (MvPolynomial.C p) ∈ maximalIdeal L :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff L Q _).2 hC
    obtain ⟨u, hu⟩ := hp
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (↑(u⁻¹) : L ⧸ J)
    have h1 : algebraMap (MvPolynomial ι P) L (MvPolynomial.C p) * y - 1 ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one, hy]
      have hu' : Ideal.Quotient.mk J (algebraMap (MvPolynomial ι P) L (MvPolynomial.C p)) = ↑u :=
        hu.symm
      rw [hu', Units.mul_inv, sub_self]
    have h3 : algebraMap (MvPolynomial ι P) L (MvPolynomial.C p) * y ∈ maximalIdeal L :=
      Ideal.mul_mem_right _ _ hL
    have h4 : (1 : L) ∈ maximalIdeal L := by
      have h5 := Ideal.sub_mem _ h3 (hJle h1)
      simpa using h5
    exact (IsLocalRing.maximalIdeal.isMaximal L).ne_top ((Ideal.eq_top_iff_one _).2 h4)
  let l : ι → L ⧸ J := fun j => ψ (lam P d j)
  have hl : l d = 1 := by
    show ψ (lam P d d) = 1
    simp [lam]
  have hmul : (z.map φ).mulVec l = 0 := by
    funext i
    have hmem : (z.map MvPolynomial.C).mulVec (lam P d) i ∈ chartIdeal z m d :=
      Ideal.subset_span ⟨Sum.inl i, rfl⟩
    have h0 := hψ _ hmem
    rw [RingHom.map_mulVec, Matrix.map_map] at h0
    exact h0
  have hm : ∀ j, φ (m j) = l j * φ (m d) := by
    intro j
    by_cases hj : j = d
    · subst hj
      rw [hl, one_mul]
    · have hmem : MvPolynomial.C (m j) - lam P d j * MvPolynomial.C (m d) ∈ chartIdeal z m d :=
        Ideal.subset_span ⟨Sum.inr ⟨j, hj⟩, rfl⟩
      have h0 := hψ _ hmem
      rw [map_sub, map_mul, sub_eq_zero] at h0
      exact h0
  have hlamc : lam P d c ∉ Q := by
    rw [hQdef, MvPolynomial.mem_map_C_iff]
    intro hall
    by_cases hcd : c = d
    · have h0 := hall 0
      rw [show lam P d c = 1 from if_pos hcd, MvPolynomial.coeff_zero_one] at h0
      exact (IsLocalRing.maximalIdeal.isMaximal P).ne_top ((Ideal.eq_top_iff_one _).2 h0)
    · have h0 := hall (Finsupp.single c 1)
      rw [show lam P d c = MvPolynomial.X c from if_neg hcd, MvPolynomial.coeff_X, if_pos rfl] at h0
      exact (IsLocalRing.maximalIdeal.isMaximal P).ne_top ((Ideal.eq_top_iff_one _).2 h0)
  have hunitL : IsUnit (algebraMap (MvPolynomial ι P) L (lam P d c)) :=
    IsLocalization.map_units L (⟨lam P d c, hlamc⟩ : Q.primeCompl)
  have hunit : IsUnit (l c) := hunitL.map (Ideal.Quotient.mk J)
  set w : L ⧸ J := ↑hunit.unit⁻¹ with hwdef
  have hw : w * l c = 1 := hunit.val_inv_mul
  let l' : ι → L ⧸ J := fun j => w * l j
  have hl' : l' c = 1 := hw
  have hmul' : (z.map φ).mulVec l' = 0 := by
    funext i
    have h7 := congrFun hmul i
    simp only [l', Matrix.mulVec, dotProduct, Pi.zero_apply] at h7 ⊢
    simp_rw [mul_left_comm _ w]
    rw [← Finset.mul_sum, h7, mul_zero]
  have hm' : ∀ j, φ (m j) = l' j * φ (m c) := by
    intro j
    show φ (m j) = w * l j * φ (m c)
    rw [hm c, hm j]
    calc l j * φ (m d) = l j * φ (m d) * (w * l c) := by rw [hw, mul_one]
      _ = w * l j * (l c * φ (m d)) := by ring
  have hk := genKer_le_ker P ι z m h c (L ⧸ J) φ l' hl' hmul' hm' hf
  rw [RingHom.mem_ker] at hk
  have hfJ : algebraMap (MvPolynomial ι P) L (MvPolynomial.C f) ∈ J :=
    Ideal.Quotient.eq_zero_iff_mem.1 hk
  obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, hx⟩ := (IsLocalization.mem_map_algebraMap_iff Q.primeCompl L).1 hfJ
  simp only at hx
  rw [← map_mul, IsLocalization.eq_iff_exists Q.primeCompl L] at hx
  obtain ⟨⟨t, ht⟩, htx⟩ := hx
  simp only at htx
  refine ⟨t * s, ?_, ?_⟩
  · exact Q.primeCompl.mul_mem ht hs
  · have h6 : t * s * MvPolynomial.C f = t * a := by rw [← htx]; ring
    rw [h6]
    exact Ideal.mul_mem_left _ _ ha

theorem UpperTheory.V.AlgebraTools.genKer_eq :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) →
      ∀ c d : ι, genKer z m c = genKer z m d := by
  intro P _ _ ι _ _ z m h c d
  exact le_antisymm (generic_kernel_monotone P ι z m h c d) (generic_kernel_monotone P ι z m h d c)
end

section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.AlgebraTools

open GlobalTheory.IwahoriTraceProof

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem unipO_le (C : Subgroup 𝓀[k]ˣ) : unipO k n ≤ iwC k n C := le_sup_of_le_left le_sup_right

private theorem KOne_le (C : Subgroup 𝓀[k]ˣ) : KOne k (Fin n) ≤ iwC k n C := le_sup_of_le_left le_sup_left

private theorem iwC_le (C : Subgroup 𝓀[k]ˣ) : iwC k n C ≤ iwahori k (Fin n) :=
  fun g hg => (((memIwC k n C).1 g).1 hg).1

private theorem inf_U (C : Subgroup 𝓀[k]ˣ) : unipB k (Fin n) ⊓ iwC k n C = unipO k n :=
  le_antisymm (inf_le_inf_left _ ((iwC_le C).trans (iwahori_le_KO k _))) (le_inf inf_le_left (unipO_le C))

private theorem inf_L (C : Subgroup 𝓀[k]ˣ) :
    unipBLower k (Fin n) ⊓ iwC k n C = unipBLower k (Fin n) ⊓ KOne k (Fin n) := by
  refine le_antisymm (fun c hc => ⟨hc.1, GlobalTheory.StepData.mem_KOne.2 fun i j => ?_⟩) (inf_le_inf_left _ (KOne_le C))
  obtain ⟨h2, h3⟩ := mem_unipBLower.1 hc.1
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h2 i j h, one_apply_ne h.ne]
  · simp [h3 i]
  · simpa [one_apply_ne h.ne'] using (mem_iwahori.1 (iwC_le C hc.2)).2 i j h

private theorem dom_le {t : Fin n → kˣ} (ht : Dom t) {i j : Fin n} (h : i ≤ j) :
    valuation k ((t i * (t j)⁻¹ : kˣ) : k) ≤ 1 := by
  rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
  exact mul_inv_le_one_of_le₀ (ht i j h) zero_le

private theorem dom_U {t : Fin n → kˣ} (ht : Dom t) :
    ∀ u ∈ unipO k n, diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹ ∈ unipO k n := by
  have key : ∀ u ∈ unipO k n, GlobalTheory.StepData.IntM
      (diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹).val := fun u hu i j => by
    rw [← map_inv, diag_mul_mul_diag]
    rcases lt_or_ge j i with h | h
    · rw [((mem_unipB k).1 hu.1).1 i j h, mul_zero]
      exact zero_mem _
    · exact mul_mem (dom_le ht h) (GlobalTheory.StepData.intM_of_mem_KO hu.2 i j)
  intro u hu
  refine ⟨conj_mem_unipB _ hu.1, GlobalTheory.StepData.mem_KO.2 ⟨key u hu, ?_⟩⟩
  convert key _ (inv_mem hu) using 2
  group

private theorem dom_L {t : Fin n → kˣ} (ht : Dom t) :
    ∀ u ∈ unipBLower k (Fin n) ⊓ KOne k (Fin n),
      (diagT k (Fin n) t)⁻¹ * u * diagT k (Fin n) t ∈ KOne k (Fin n) := by
  intro u hu
  have h1 := conj_mem_unipBLower t⁻¹ hu.1
  rw [map_inv, inv_inv] at h1
  refine GlobalTheory.StepData.mem_KOne.2 fun i j => ?_
  rcases lt_trichotomy i j with h | rfl | h
  · simp only [Matrix.sub_apply, (mem_unipBLower.1 h1).1 i j h, one_apply_ne h.ne, sub_self, map_zero, zero_lt_one]
  · simp only [Matrix.sub_apply, (mem_unipBLower.1 h1).2 i, one_apply_eq, sub_self, map_zero, zero_lt_one]
  · have h2 := GlobalTheory.StepData.mem_KOne.1 hu.2 i j
    rw [Matrix.sub_apply, one_apply_ne h.ne', sub_zero] at h2 ⊢
    rw [← map_inv, diag_mul_mul_diag, mul_comm (_ : kˣ), map_mul]
    exact (mul_le_of_le_one_left' (dom_le ht h.le)).trans_lt h2

private noncomputable def torFact (C : Subgroup 𝓀[k]ˣ) : LeviFact (iwC k n C) where
  Uf := unipB k (Fin n)
  Mf := (diagT k (Fin n)).range
  Lf := unipBLower k (Fin n)
  M_U := by
    rintro _ ⟨t, rfl⟩ u hu
    exact conj_mem_unipB t hu
  M_L := by
    rintro _ ⟨t, rfl⟩ u hu
    exact conj_mem_unipBLower t hu
  uniq := by
    rintro u hu _ ⟨t, rfl⟩ l hl e
    have e' : u⁻¹ = diagT k (Fin n) t * l := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, e])
    obtain ⟨a1, a2⟩ := (mem_unipB k).1 (inv_mem hu)
    obtain ⟨b1, b2⟩ := mem_unipBLower.1 hl
    have ent : ∀ i j, (u⁻¹).val i j = (t i : k) * l.val i j := fun i j => by
      rw [e', Units.val_mul, val_diagT, diagonal_mul]
    constructor
    · rw [← inv_eq_one]
      ext i j
      rcases lt_trichotomy i j with h | rfl | h
      · rw [ent, b1 i j h, mul_zero, Units.val_one, one_apply_ne h.ne]
      · rw [a2, Units.val_one, one_apply_eq]
      · rw [a1 i j h, Units.val_one, one_apply_ne h.ne']
    · have : t = 1 := funext fun i => Units.ext (by
        have := ent i i
        rw [a2, b2, mul_one] at this
        exact this.symm)
      rw [this, map_one]
  fact g hg := by
    obtain ⟨u, hu, d, -, c, hc, rfl⟩ := iwahori_factorisation (iwC_le C hg)
    have h1 : u ∈ iwC k n C := unipO_le C hu
    have h2 : c ∈ iwC k n C := KOne_le C hc.2
    refine ⟨u, ⟨hu.1, h1⟩, _, ⟨⟨d, rfl⟩, ?_⟩, c, ⟨hc.1, h2⟩, rfl⟩
    have := mul_mem (inv_mem h1) (mul_mem hg (inv_mem h2))
    rwa [mul_inv_cancel_right, inv_mul_cancel_left] at this

end

end UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.factTorus :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ), ∃ F : LeviFact (iwC k n C), F.Uf = unipB k (Fin n) ∧ F.Mf = (diagT k (Fin n)).range ∧ F.Lf = unipBLower k (Fin n) ∧ F.Uf ⊓ iwC k n C = unipO k n ∧ F.Lf ⊓ iwC k n C = unipBLower k (Fin n) ⊓ KOne k (Fin n) ∧ ∀ t : Fin n → kˣ, F.NormJ (diagT k (Fin n) t) ∧ (Dom t → F.Pos (diagT k (Fin n) t)) := by
  intro k _ _ _ _ n C
  refine ⟨torFact C, rfl, rfl, rfl, inf_U C, inf_L C, fun t => ⟨?_, fun ht => ⟨⟨t, rfl⟩, fun u hu => ?_, fun l hl => ?_⟩⟩⟩
  · rintro _ ⟨⟨s, rfl⟩, hs⟩
    have e : diagT k (Fin n) t * diagT k (Fin n) s = diagT k (Fin n) s * diagT k (Fin n) t := by
      rw [← map_mul, mul_comm, map_mul]
    constructor
    · rwa [e, mul_inv_cancel_right]
    · rwa [mul_assoc, ← e, inv_mul_cancel_left]
  · exact unipO_le C (dom_U ht u (inf_U C ▸ hu))
  · exact KOne_le C (dom_L ht l (inf_L C ▸ hl))
end
