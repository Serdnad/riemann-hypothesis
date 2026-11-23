module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle134
import Formalism.FormalDegreeBessel.FinalG
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHat
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle086
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle111
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle132
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle136
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle128

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Polynomial

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.CurvScal

noncomputable section

theorem pl_monic (s : Finset ℕ) (f : ℕ → ℂ) : (∏ i ∈ s, (X + C (f i))).Monic :=
  monic_prod_of_monic _ _ (fun i _ => monic_X_add_C (f i))

theorem pl_natDegree (s : Finset ℕ) (f : ℕ → ℂ) : (∏ i ∈ s, (X + C (f i))).natDegree = s.card := by
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_add_C (f i))]
  simp [natDegree_X_add_C]

theorem pl_top (s : Finset ℕ) (f : ℕ → ℂ) : (∏ i ∈ s, (X + C (f i))).coeff s.card = 1 := by
  have h := (pl_monic s f).coeff_natDegree
  rwa [pl_natDegree] at h

theorem pl_next (s : Finset ℕ) (f : ℕ → ℂ) (hs : 0 < s.card) :
    (∏ i ∈ s, (X + C (f i))).coeff (s.card - 1) = ∑ i ∈ s, f i := by
  have h := nextCoeff_of_natDegree_pos (p := ∏ i ∈ s, (X + C (f i))) (by rw [pl_natDegree]; exact hs)
  rw [pl_natDegree] at h
  rw [← h, Monic.nextCoeff_prod _ _ (fun i _ => monic_X_add_C (f i))]
  simp [nextCoeff_X_add_C]

theorem pl_high (s : Finset ℕ) (f : ℕ → ℂ) {j : ℕ} (hj : s.card < j) : (∏ i ∈ s, (X + C (f i))).coeff j = 0 :=
  coeff_eq_zero_of_natDegree_lt (by rw [pl_natDegree]; exact hj)

theorem top2 (p : ℂ[X]) (N : ℕ) (h : p.natDegree < N + 2) (u : ℂ) :
    p.eval u = u ^ (N + 1) * p.coeff (N + 1) + u ^ N * p.coeff N + ∑ i ∈ Finset.range N, u ^ i * p.coeff i := by
  rw [eval_eq_sum_range' h, Finset.sum_range_succ, Finset.sum_range_succ]
  have : ∀ i, p.coeff i * u ^ i = u ^ i * p.coeff i := fun i => mul_comm _ _
  simp only [this]
  ring

theorem card_Icc_one (n : ℕ) : (Finset.Icc 1 n).card = n := by simp

theorem xC_leading_terms_alt (P : M.Par) (m : ℕ) (hm : P.k = m + 2) (ρ : M.Ty P) :
    ∃ c : ℕ → ℂ, ∀ u : ℂ, M.xC P ρ u = u ^ (P.k - 1) + (absTy P ρ : ℂ) * u ^ (P.k - 2) +
        ∑ i ∈ Finset.range (P.k - 2), u ^ i * c i := by
  have h1 : P.k - 1 = m + 1 := by omega
  have h2 : P.k - 2 = m := by omega
  let f : ℕ → ℂ := fun i => ((M.rho P ρ i : ℝ) : ℂ)
  refine ⟨fun i => (∏ i ∈ Finset.Icc 1 (m + 1), (X + C (f i))).coeff i, fun u => ?_⟩
  have hx : M.xC P ρ u = (∏ i ∈ Finset.Icc 1 (m + 1), (X + C (f i))).eval u := by
    rw [eval_prod]; unfold M.xC; rw [h1]; simp [f]
  rw [hx, top2 _ m (by rw [pl_natDegree, card_Icc_one]; omega) u, h1, h2]
  have ht := pl_top (Finset.Icc 1 (m + 1)) f
  have hn := pl_next (Finset.Icc 1 (m + 1)) f (by rw [card_Icc_one]; omega)
  rw [card_Icc_one] at ht hn
  rw [Nat.add_sub_cancel] at hn
  rw [ht, hn]
  have ha : (absTy P ρ : ℂ) = ∑ i ∈ Finset.Icc 1 (m + 1), f i := by
    simp only [absTy, h1, f]; push_cast; rfl
  rw [ha]; ring

theorem part_ex (P : M.Par) (m : ℕ) (hm : P.k = m + 2) (ρ : M.Ty P) (ex : Finset ℕ)
    (hex : ∃ l ∈ ex, l ∈ Finset.Icc 1 (P.k - 1)) :
    ∃ c : ℕ → ℂ, ∀ u : ℂ, M.xEx P ex ρ u = ∑ i ∈ Finset.range (P.k - 1), u ^ i * c i := by
  have h1 : P.k - 1 = m + 1 := by omega
  let f : ℕ → ℂ := fun i => ((M.rho P ρ i : ℝ) : ℂ)
  let s := Finset.Icc 1 (m + 1) \ ex
  have hs : s.card < m + 1 := by
    obtain ⟨l, hl, hlI⟩ := hex
    rw [h1] at hlI
    have hss : s ⊂ Finset.Icc 1 (m + 1) :=
      (Finset.ssubset_iff_of_subset Finset.sdiff_subset).2 ⟨l, hlI, by simp [s, hl]⟩
    have := Finset.card_lt_card hss
    rwa [card_Icc_one] at this
  refine ⟨fun i => (∏ i ∈ s, (X + C (f i))).coeff i, fun u => ?_⟩
  have hx : M.xEx P ex ρ u = (∏ i ∈ s, (X + C (f i))).eval u := by
    rw [eval_prod]; unfold M.xEx; rw [h1]; simp [f, s]
  rw [hx, eval_eq_sum_range' (by rw [pl_natDegree]; omega) u, h1]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem part_w (P : M.Par) (m : ℕ) (hm : P.k = m + 2) (ρ : M.Ty P) :
    ∃ c : ℕ → ℂ, ∀ u : ℂ, M.wC P ρ u = u ^ (P.k + 1) * (-(P.TT : ℂ)) +
        u ^ P.k * ((P.TT : ℂ) * ((absTy P ρ : ℂ) - 1 - sumU P)) + ∑ i ∈ Finset.range P.k, u ^ i * c i := by
  have h1 : P.k - 1 = m + 1 := by omega
  let fx : ℕ → ℂ := fun i => ((M.rho P ρ i : ℝ) : ℂ) + 1
  let xp := ∏ i ∈ Finset.Icc 1 (m + 1), (X + C (fx i))
  have hxp : M.coordinatePolynomial P ρ = xp := by unfold M.coordinatePolynomial; rw [h1]
  have xmon : xp.Monic := pl_monic _ _
  have xdeg : xp.natDegree = m + 1 := by rw [pl_natDegree, card_Icc_one]
  have xtop : xp.coeff (m + 1) = 1 := by
    have := pl_top (Finset.Icc 1 (m + 1)) fx; rwa [card_Icc_one] at this
  have xnext : xp.coeff m = ∑ i ∈ Finset.Icc 1 (m + 1), fx i := by
    have := pl_next (Finset.Icc 1 (m + 1)) fx (by rw [card_Icc_one]; omega)
    rwa [card_Icc_one, Nat.add_sub_cancel] at this
  have xhigh : xp.coeff (m + 2) = 0 := pl_high _ _ (by rw [card_Icc_one]; omega)
  let fa : ℕ → ℂ := fun i => 1 / 2 + (P.u i : ℂ)
  let fb : ℕ → ℂ := fun i => 1 / 2 + (P.u' i : ℂ)
  let pa := ∏ i ∈ Finset.Icc 1 (m + 2), (X + C (fa i))
  let pb := ∏ i ∈ Finset.Icc 1 (m + 2), (X + C (fb i))
  have hT : (-((P.T : ℂ) * (P.T' : ℂ))) = -(P.TT : ℂ) := by simp [M.Par.TT]
  have hq : M.qP P = C (-(P.TT : ℂ)) * (pa * pb) := by
    unfold M.qP; rw [hm, Finset.prod_mul_distrib, hT]
  have abmon : (pa * pb).Monic := (pl_monic _ _).mul (pl_monic _ _)
  have abdeg : (pa * pb).natDegree = 2 * m + 4 := by
    rw [(pl_monic _ _).natDegree_mul (pl_monic _ _), pl_natDegree, pl_natDegree, card_Icc_one]; ring
  have abtop : (pa * pb).coeff (2 * m + 4) = 1 := by rw [← abdeg]; exact abmon.coeff_natDegree
  have abnext : (pa * pb).coeff (2 * m + 3) =
      ∑ i ∈ Finset.Icc 1 (m + 2), fa i + ∑ i ∈ Finset.Icc 1 (m + 2), fb i := by
    have h := nextCoeff_of_natDegree_pos (p := pa * pb) (by rw [abdeg]; omega)
    rw [abdeg, show 2 * m + 4 - 1 = 2 * m + 3 by omega] at h
    rw [← h, (pl_monic _ _).nextCoeff_mul (pl_monic _ _),
      Monic.nextCoeff_prod _ _ (fun i _ => monic_X_add_C (fa i)),
      Monic.nextCoeff_prod _ _ (fun i _ => monic_X_add_C (fb i))]
    simp only [nextCoeff_X_add_C]
  let NS : ℂ[X] := ∑ l ∈ Finset.Icc 1 (m + 1), C ((M.Nrm P l ρ : ℝ) : ℂ) *
    ((∏ j ∈ (Finset.Icc 1 (m + 1)).erase l, (X + C ((M.rho P ρ j : ℝ) : ℂ))) *
      ∏ j ∈ (Finset.Icc 1 (m + 1)).erase l, (X + C (((M.rho P ρ j : ℝ) : ℂ) + 1)))
  have hw : M.wNum P ρ = M.qP P + NS := by unfold M.wNum; rw [h1]
  have nsdeg : NS.natDegree ≤ 2 * m + 2 := by
    apply natDegree_sum_le_of_forall_le
    intro l hl
    refine (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)
    have hc : ((Finset.Icc 1 (m + 1)).erase l).card = m := by
      rw [Finset.card_erase_of_mem hl, card_Icc_one]; omega
    have e1 := pl_natDegree ((Finset.Icc 1 (m + 1)).erase l) (fun j => ((M.rho P ρ j : ℝ) : ℂ))
    have e2 := pl_natDegree ((Finset.Icc 1 (m + 1)).erase l) (fun j => ((M.rho P ρ j : ℝ) : ℂ) + 1)
    rw [e1, e2, hc]; omega
  let c0 : ℂ := (P.TT : ℂ) * ((absTy P ρ : ℂ) - 1 - sumU P)
  let Q0 : ℂ[X] := C (-(P.TT : ℂ)) * X ^ (m + 3) + C c0 * X ^ (m + 2)
  let G : ℂ[X] := M.wNum P ρ - xp * Q0
  have e_xQ : xp * Q0 = C (-(P.TT : ℂ)) * (xp * X ^ (m + 3)) + C c0 * (xp * X ^ (m + 2)) := by
    simp only [Q0]; ring
  have c4a : (xp * X ^ (m + 3)).coeff (2 * m + 4) = 1 := by
    rw [show 2 * m + 4 = (m + 1) + (m + 3) by ring, coeff_mul_X_pow, xtop]
  have c4b : (xp * X ^ (m + 2)).coeff (2 * m + 4) = 0 := by
    rw [show 2 * m + 4 = (m + 2) + (m + 2) by ring, coeff_mul_X_pow, xhigh]
  have c3a : (xp * X ^ (m + 3)).coeff (2 * m + 3) = xp.coeff m := by
    rw [show 2 * m + 3 = m + (m + 3) by ring, coeff_mul_X_pow]
  have c3b : (xp * X ^ (m + 2)).coeff (2 * m + 3) = 1 := by
    rw [show 2 * m + 3 = (m + 1) + (m + 2) by ring, coeff_mul_X_pow, xtop]
  have Q0deg : (xp * Q0).natDegree ≤ 2 * m + 4 := by
    refine natDegree_mul_le.trans ?_
    rw [xdeg]
    have : Q0.natDegree ≤ m + 3 := (natDegree_add_le _ _).trans
      (max_le (natDegree_C_mul_X_pow_le _ _) ((natDegree_C_mul_X_pow_le _ _).trans (by omega)))
    omega
  have qdeg : (M.qP P).natDegree ≤ 2 * m + 4 := by
    rw [hq]; exact (natDegree_C_mul_le _ _).trans abdeg.le
  have hA : (absTy P ρ : ℂ) = ∑ i ∈ Finset.Icc 1 (m + 1), ((M.rho P ρ i : ℝ) : ℂ) := by
    simp only [absTy, h1]; push_cast; rfl
  have hS : sumU P = ∑ i ∈ Finset.Icc 1 (m + 2), (P.u i : ℂ) + ∑ i ∈ Finset.Icc 1 (m + 2), (P.u' i : ℂ) := by
    simp only [sumU, hm, Finset.sum_add_distrib]
  have Gdeg : G.natDegree ≤ 2 * m + 2 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    simp only [G, hw, coeff_sub, coeff_add]
    rw [coeff_eq_zero_of_natDegree_lt (p := NS) (by omega), add_zero]
    rcases (show N = 2 * m + 3 ∨ N = 2 * m + 4 ∨ 2 * m + 4 < N by omega) with h | h | h
    · subst h
      rw [e_xQ, coeff_add, coeff_C_mul, coeff_C_mul, c3a, c3b, xnext, hq, coeff_C_mul, abnext]
      simp only [fa, fb, fx, c0, hA, hS, Finset.sum_add_distrib, Finset.sum_const, card_Icc_one, nsmul_eq_mul]
      push_cast
      ring
    · subst h
      rw [e_xQ, coeff_add, coeff_C_mul, coeff_C_mul, c4a, c4b, hq, coeff_C_mul, abtop]; ring
    · rw [coeff_eq_zero_of_natDegree_lt (by omega : (M.qP P).natDegree < N),
        coeff_eq_zero_of_natDegree_lt (by omega : (xp * Q0).natDegree < N)]; ring
  have hG := modByMonic_add_div G xp
  have hdiv : M.wNum P ρ /ₘ xp = Q0 + G /ₘ xp := by
    refine (div_modByMonic_unique (Q0 + G /ₘ xp) (G %ₘ xp) xmon ⟨?_, degree_modByMonic_lt _ xmon⟩).1
    calc G %ₘ xp + xp * (Q0 + G /ₘ xp) = xp * Q0 + (G %ₘ xp + xp * (G /ₘ xp)) := by ring
      _ = xp * Q0 + G := by rw [hG]
      _ = M.wNum P ρ := by simp only [G]; ring
  have Gq : (G /ₘ xp).natDegree < m + 2 := by rw [natDegree_divByMonic _ xmon, xdeg]; omega
  refine ⟨fun i => (G /ₘ xp).coeff i, fun u => ?_⟩
  unfold M.wC
  rw [hxp, hdiv, eval_add, eval_eq_sum_range' Gq u, hm]
  simp only [Q0, c0, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  have : ∀ i, (G /ₘ xp).coeff i * u ^ i = u ^ i * (G /ₘ xp).coeff i := fun i => mul_comm _ _
  simp only [this]
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.CurvScal

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem curvature_scalar_holds : GTCCurvScal := by
  intro P hk ρ
  obtain ⟨m, hm⟩ : ∃ m, P.k = m + 2 := ⟨P.k - 2, by omega⟩
  exact ⟨CurvScal.part_w P m hm ρ, CurvScal.xC_leading_terms_alt P m hm ρ, fun ex hex => CurvScal.part_ex P m hm ρ ex hex⟩

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

variable {k r : ℕ}

theorem single_conjT {n : ℕ} (p q : Fin n) (c : ℂ) : (Matrix.single p q c)ᴴ = Matrix.single q p (star c) := by
  ext x y
  simp only [conjTranspose_apply, single_apply]
  by_cases h1 : p = y <;> by_cases h2 : q = x <;> simp [h1, h2]

theorem hpk_col_eI (i : Fin (2 * r + k + 1)) (c : Fin r) :
    Hpk k r i (eI k r c) = if i = esI k r c then 1 else 0 := by
  have hc := c.isLt
  simp only [Hpk, eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_col_esI (i : Fin (2 * r + k + 1)) (c : Fin r) :
    Hpk k r i (esI k r c) = if i = eI k r c then 1 else 0 := by
  have hc := c.isLt
  simp only [Hpk, eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mul_single_eI (c : Fin r) (q : Fin (2 * r + k + 1)) (x : ℂ) :
    Hpk k r * Matrix.single (eI k r c) q x = Matrix.single (esI k r c) q x := by
  ext i l
  by_cases hl : l = q
  · subst hl
    rw [mul_single_apply_same, hpk_col_eI, single_apply]
    by_cases h : i = esI k r c <;> simp [h, eq_comm]
  · rw [mul_single_apply_of_ne _ _ _ _ _ hl, single_apply_of_col_ne _ _ (Ne.symm hl)]

theorem hpk_mul_single_esI (c : Fin r) (q : Fin (2 * r + k + 1)) (x : ℂ) :
    Hpk k r * Matrix.single (esI k r c) q x = Matrix.single (eI k r c) q x := by
  ext i l
  by_cases hl : l = q
  · subst hl
    rw [mul_single_apply_same, hpk_col_esI, single_apply]
    by_cases h : i = eI k r c <;> simp [h, eq_comm]
  · rw [mul_single_apply_of_ne _ _ _ _ _ hl, single_apply_of_col_ne _ _ (Ne.symm hl)]

theorem eI_ne_esI (b c : Fin r) : eI k r b ≠ esI k r c := by
  have := b.isLt; have := c.isLt
  simp only [eI, esI, ne_eq, Fin.ext_iff]; omega

theorem eI_inj {b c : Fin r} (h : eI k r b = eI k r c) : b = c := by
  simp only [eI, Fin.ext_iff] at h; exact Fin.ext h

theorem esI_inj {b c : Fin r} (h : esI k r b = esI k r c) : b = c := by
  have := b.isLt; have := c.isLt
  simp only [esI, Fin.ext_iff] at h; exact Fin.ext (by omega)

section nl

variable (j : ℕ) (hj : j + 1 ≤ r) (a : Fin j → ℂ)

def Xn : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  ∑ b : Fin j, (a b • Matrix.single (esI k r ⟨j, by omega⟩) (esI k r ⟨b, by omega⟩) (1 : ℂ) -
    conj (a b) • Matrix.single (eI k r ⟨b, by omega⟩) (eI k r ⟨j, by omega⟩) (1 : ℂ))

theorem nL_eq : LevelPointCoordinates.nL k r j hj a = 1 + Xn j hj a := rfl

theorem hX : Hpk k r * Xn j hj a = ∑ b : Fin j, (a b • Matrix.single (eI k r ⟨j, by omega⟩) (esI k r ⟨b, by omega⟩) (1 : ℂ) -
    conj (a b) • Matrix.single (esI k r ⟨b, by omega⟩) (eI k r ⟨j, by omega⟩) (1 : ℂ)) := by
  unfold Xn
  rw [Matrix.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, hpk_mul_single_esI, hpk_mul_single_eI]

theorem hXh : (Xn (k := k) j hj a)ᴴ = ∑ b : Fin j, (conj (a b) • Matrix.single (esI k r ⟨b, by omega⟩) (esI k r ⟨j, by omega⟩) (1 : ℂ) -
    a b • Matrix.single (eI k r ⟨j, by omega⟩) (eI k r ⟨b, by omega⟩) (1 : ℂ)) := by
  unfold Xn
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, single_conjT, single_conjT]
  simp

theorem hXhH : (Xn (k := k) j hj a)ᴴ * Hpk k r = -(Hpk k r * Xn j hj a) := by
  have hH : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1
  have e : (Xn (k := k) j hj a)ᴴ * Hpk k r = (Hpk k r * Xn j hj a)ᴴ := by
    rw [Matrix.conjTranspose_mul, hH]
  rw [e, hX, Matrix.conjTranspose_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, single_conjT, single_conjT]
  simp only [star_one, RCLike.star_def, Complex.conj_conj]
  abel

theorem hXHX : (Xn (k := k) j hj a)ᴴ * Hpk k r * Xn j hj a = 0 := by
  rw [Matrix.mul_assoc, hX, hXh, Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun b' _ => ?_
  have n1 : esI k r ⟨j, by omega⟩ ≠ eI k r ⟨j, by omega⟩ := (eI_ne_esI _ _).symm
  have n2 : esI k r ⟨j, by omega⟩ ≠ esI k r ⟨b', by omega⟩ := fun h => by
    have := congrArg Fin.val (esI_inj h); simp at this; omega
  have n3 : eI k r ⟨b, by omega⟩ ≠ eI k r ⟨j, by omega⟩ := fun h => by
    have := congrArg Fin.val (eI_inj h); simp at this; omega
  have n4 : eI k r ⟨b, by omega⟩ ≠ esI k r ⟨b', by omega⟩ := eI_ne_esI _ _
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    single_mul_single_of_ne _ _ _ _ n1, single_mul_single_of_ne _ _ _ _ n2, single_mul_single_of_ne _ _ _ _ n3,
    single_mul_single_of_ne _ _ _ _ n4, smul_zero, sub_zero]

theorem nL_uh : LevelPointCoordinates.nL k r j hj a ∈ UH (Hpk k r) := by
  show (LevelPointCoordinates.nL k r j hj a)ᴴ * Hpk k r * LevelPointCoordinates.nL k r j hj a = Hpk k r
  rw [nL_eq, Matrix.conjTranspose_add, Matrix.conjTranspose_one]
  have h1 := hXhH (k := k) j hj a
  have h2 := hXHX (k := k) j hj a
  calc (1 + (Xn j hj a)ᴴ) * Hpk k r * (1 + Xn j hj a)
      = Hpk k r + ((Xn (k := k) j hj a)ᴴ * Hpk k r + Hpk k r * Xn j hj a) +
          (Xn (k := k) j hj a)ᴴ * Hpk k r * Xn j hj a := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]; abel
    _ = Hpk k r := by rw [h2, h1]; abel

theorem nL_apply (p q : Fin (2 * r + k + 1)) :
    LevelPointCoordinates.nL k r j hj a p q = (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) p q +
      ∑ b : Fin j, (a b * Matrix.single (esI k r ⟨j, by omega⟩) (esI k r ⟨b, by omega⟩) (1 : ℂ) p q -
        conj (a b) * Matrix.single (eI k r ⟨b, by omega⟩) (eI k r ⟨j, by omega⟩) (1 : ℂ) p q) := by
  rw [nL_eq, Matrix.add_apply, Xn, Matrix.sum_apply]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]

theorem nL_mem : LevelPointCoordinates.nL k r j hj a ∈ Nset k r := by
  refine ⟨nL_uh j hj a, ?_, ?_⟩
  · intro c i hci
    rw [nL_apply, Finset.sum_eq_zero, add_zero]
    · by_cases h : i = eI k r c <;> simp [h, Matrix.one_apply]
    · intro b _
      have hc := c.isLt
      rw [single_apply_of_col_ne _ _ (fun h => eI_ne_esI c ⟨b, by omega⟩ h.symm), mul_zero, zero_sub]
      rw [single_apply, if_neg, mul_zero, neg_zero]
      rintro ⟨h1, h2⟩
      have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2
      simp only [eI] at e1 e2
      have := b.isLt
      omega
  · intro i q hq1 hq2 hi
    rw [nL_apply, Finset.sum_eq_zero, add_zero]
    · by_cases h : i = q <;> simp [h, Matrix.one_apply]
    · intro b _
      have hb := b.isLt
      rw [single_apply, if_neg, single_apply, if_neg, mul_zero, mul_zero, sub_zero]
      · rintro ⟨_, h2⟩
        have e2 := congrArg Fin.val h2; simp only [eI] at e2; omega
      · rintro ⟨_, h2⟩
        have e2 := congrArg Fin.val h2; simp only [esI] at e2; omega

end nl

end Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

theorem jdg_gauge_of_core {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : Gauge.IsFrameB P Bs e)
    (hcore : ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), Gauge.FamR P Bs Dc Φ →
        ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
          MA.toSm P (Gauge.rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
            MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ')) ρ) :
    ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs), ∀ Y : ℝ,
      Gauge.trJB P Bs e (Q.CV P.k P.r (Y : ℂ) J) =
        MA.actA P (Wd.C0 (MA.QQr P (MA.DQ P)) (MA.sites P (MA.DQ P)) (Y : ℂ)) (Gauge.trJB P Bs e J) := by
  intro J hJ Y
  obtain ⟨hF, hres, hcv⟩ := Gauge.gauge_transition_chain_holds Wp Wq P Bs hpl hk J hJ
  set Φ := Q.resG P.k P.r (Fin.last P.r) J with hΦ
  have hJe : Gauge.trJB P Bs e J = fun ρ => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ) := by
    funext ρ
    exact congrArg (MA.toSm P) (hres e ρ)
  have hpair : ∀ a b : Fin 2,
      (∀ ρ, Gauge.rawR P Bs.μsec e (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) P.r) a)
        (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b
          (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) P.r) b) Φ))) ρ ∈ MA.smSub P.r P.TT) ∧
      ∀ ρ, MA.toSm P (Gauge.rawR P Bs.μsec e (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) P.r) a)
        (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b
          (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) P.r) b) Φ))) ρ) =
        MA.actA P (star (Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) a) * MA.QQr P (MA.DQ P) (Y : ℂ) a b *
          Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) b) (Gauge.trJB P Bs e J) ρ := by
    intro a b
    obtain ⟨hF1, hV1⟩ := Gauge.gauge_vector_transition_holds Wp Wq P Bs hpl hk e he _ Φ hF Y b
    have hF2 := Gauge.quadratic_local_family_holds Wp Wq P Bs hpl hk _ _ hF1 Y a b
    obtain ⟨hF3, hV2⟩ := Gauge.gauge_conj_vector_transition Wp Wq P Bs hpl hk e he _ _ hF2 Y a
    refine ⟨fun ρ => Gauge.raw_gauge_smoothness_holds Wp Wq P Bs hpl hk e he _ _ hF3 ρ, fun ρ => ?_⟩
    have hin : (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e
        (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) P.r) b) Φ) ρ')) =
        MA.actA P (Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) b) (Gauge.trJB P Bs e J) := by
      funext ρ'
      rw [hV1 ρ', hJe]
    have hmid : (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e
        (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b
          (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) P.r) b) Φ)) ρ')) =
        MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b)
          (MA.actA P (Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) b) (Gauge.trJB P Bs e J)) := by
      funext ρ'
      rw [hcore _ _ hF1 Y a b ρ', hin]
    rw [hV2 ρ, Gauge.actA_mul, Gauge.actA_mul, hmid]
  funext ρ
  show MA.toSm P (Gauge.rawJ P Bs e (Q.CV P.k P.r (Y : ℂ) J) ρ) = _
  rw [hcv e ρ Y]
  rw [show Wd.C0 (MA.QQr P (MA.DQ P)) (MA.sites P (MA.DQ P)) (Y : ℂ) =
      ∑ a, ∑ b, star (Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) a) * MA.QQr P (MA.DQ P) (Y : ℂ) a b *
        Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) b from rfl]
  simp only [Gauge.actA_sum, Finset.sum_apply]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ((hpair a b).2 ρ).symm]
  rw [Gauge.toSm_of_mem P (Subalgebra.sum_mem _ fun a _ => Subalgebra.sum_mem _ fun b _ => (hpair a b).1 ρ)]
  apply Subtype.ext
  simp only [AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Gauge.toSm_of_mem P ((hpair a b).1 ρ)]

theorem jdg_exists_of_gCore (hK : Gauge.GCore) (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E]
    (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ) (hB : BuiltOW Cc S T f χ ν' m₀ top A₀) (v : Fin S.f) :
    ∃ e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
      IsFrame S T v e ∧ IsGauge S T v e ∧ IsGaugeQQ S T v e := by
  obtain ⟨hBP, -, -, -⟩ := hB
  obtain ⟨-, -, -, hIB, -, -, -, -, -, -, hk2, -, -⟩ := hBP
  obtain ⟨-, -, -, hpl, -, -⟩ := hIB.2 v
  obtain ⟨e, he, hc⟩ := hK (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hpl hk2
  exact ⟨e, he, jdg_gauge_of_core (D.parOf S v) (T v).base hpl hk2 e he hc, hc⟩

end

end Formalism.FourierDecayAlt.P.CutMP
end
