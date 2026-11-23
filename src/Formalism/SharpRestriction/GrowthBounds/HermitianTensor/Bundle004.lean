module

public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.Bundle002
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle004
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.OneMemDualWeyl
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.MemInvariantSectionsIffIntegral
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.MemInvariantSectionsTwoWeightIff
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.NuOfLoZero
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.QaWeightRowInd
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.Bundle003
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

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem contraction_of_pairing_lemmas (hPh : QPh) (hSC : SubCoeffP) (hSM : SubMapP) (hSR : SubRowP) (hLC : LamCoeffP) (hLE : LamEquivP)
    (hLM : LamMulP) (hLV : LamEvalP) (hMem : LamMemP) (hMu : SubMuP) (hTop : TopLineP) (hLift : LiftP) (hDD : DetDivP)
    (hIC : IntCapP) (hHw : HwMulP) : ContractionStandardLattice := by
  classical
  intro p n' R mm hmm a ccl P Q lam hlam h0 hl hmid h8
  have hfr := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  have := R.charZero
  have : Infinite R.Kf := inferInstance
  have hloA : Antitone (lam - wtPQ (mm + 1) P Q) := caLo_anti mm ccl P Q lam hlam h0 hl hmid
  have hlo'A : Antitone (dualWt (lam - wtPQ (mm + 1) P Q)) := qsDualWt_anti _ hloA
  have hαZ := nuOf_lam_mid mm ccl Q lam hl hmid
  have hβZ := nuOf_lo_mid mm ccl P Q lam h0 hl hmid
  have hβ'Z := nuOf_lo'_mid mm ccl P Q lam h0 hl hmid
  have hbd := lam_mid_bd mm ccl lam hmid
  have hαA : Antitone (fun j => nuOf lam (midI mm j)) := fun i j hij => nuOf_anti lam hlam (midI_mono mm hij)
  have hαN : ∀ i, (fun j => nuOf lam (midI mm j)) i ≤ Q + 2 * ccl := by
    intro i
    show nuOf lam (midI mm i) ≤ Q + 2 * ccl
    have := hαZ i; have := hbd i; omega
  have hαc : ∀ i j, (fun j => nuOf lam (midI mm j)) i ≤ (fun j => nuOf lam (midI mm j)) j + 2 * ccl := by
    intro i j
    show nuOf lam (midI mm i) ≤ nuOf lam (midI mm j) + 2 * ccl
    have := hαZ i; have := hαZ j; have := hbd i; have := hbd j; omega
  obtain ⟨L, hInv, hInt, nb, u, u', ka, hnb, hka, hu, hu', hdiag⟩ :=
    hPh p n' R mm hmm a (2 * ccl) (Q + 2 * ccl) (fun j => nuOf lam (midI mm j)) hαA hαN hαc h8
  have hα' : (fun i : Fin mm => Q + 2 * ccl - (fun j => nuOf lam (midI mm j)) i.rev) =
      fun j => nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j) := by
    funext j
    show Q + 2 * ccl - nuOf lam (midI mm j.rev) = _
    have h1 := hβ'Z j; have h2 := hαZ j.rev; have h3 := hbd j.rev; omega
  rw [hα'] at hInv hInt hu'
  have hαβ : (fun j => nuOf lam (midI mm j)) = fun j => nuOf (lam - wtPQ (mm + 1) P Q) (midI mm j) + Q := by
    funext j
    have := hαZ j; have := hβZ j; omega
  have hwA : ∀ a b, Antitone (nuOf (wtPQ (mm + 1) a b)) := fun a b => nuOf_anti _ (wtPQ_anti (mm + 1) a b (by omega))
  have hK : ∀ v ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf lam),
      ∀ t ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))),
        lamOf R.Kf mm L (blockEmb R.Kf true v * blockEmb R.Kf false t) ∈
          dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl))) :=
    hMem R.Kf mm (Q + 2 * ccl) (nuOf lam) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q)))
      (nuOf (wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl))) L (nuOf_last _) (nuOf_last _) (nuOf_last _)
      (by rw [nuOf_wt_zero, nuOf_lam_zero mm ccl P Q lam h0 hl, nuOf_lo'_zero mm ccl P Q lam h0 hl]; omega)
      (fun j => nuOf_wt_mid mm _ _ j) hInv
  refine ⟨lamOf R.Kf mm L, hK, fun g _ v _ t _ => hLE R.Kf mm L g v t, ?_, ?_⟩
  · intro v hv t ht
    refine hIC R.O R.Kf hinj _ _ _ (hK v (intO_le _ _ v hv) t (intO_le _ _ t ht)) ?_
    intro x
    obtain ⟨v0, hv0, rfl⟩ := hv
    obtain ⟨t0, ht0, rfl⟩ := ht
    have e1 : (mapAlgHom (Algebra.ofId R.O R.Kf)).toLinearMap v0 = map (algebraMap R.O R.Kf) v0 := rfl
    have e2 : (mapAlgHom (Algebra.ofId R.O R.Kf)).toLinearMap t0 = map (algebraMap R.O R.Kf) t0 := rfl
    rw [hLC, e1, e2, hSM, hSM]
    have : (∑ y ∈ Finset.HasAntidiagonal.antidiagonal x,
        L (blockEmb R.Kf true (AddMonoidAlgebra.coeff (map (map (algebraMap R.O R.Kf)) (subY R.O mm v0)) y.1) *
          blockEmb R.Kf false (AddMonoidAlgebra.coeff (map (map (algebraMap R.O R.Kf)) (subY R.O mm t0)) y.2))) ∈
        (algebraMap R.O R.Kf).range := by
      refine sum_mem fun y _ => ?_
      rw [coeff_map, coeff_map]
      exact hInt _ ⟨AddMonoidAlgebra.coeff (subY R.O mm v0) y.1, hSC R.O mm _ v0 hv0 _, rfl⟩ _
        ⟨AddMonoidAlgebra.coeff (subY R.O mm t0) y.2, hSC R.O mm _ t0 ht0 _, rfl⟩
    exact this
  · have hβA : Antitone (fun j => nuOf (lam - wtPQ (mm + 1) P Q) (midI mm j)) :=
      fun i j hij => nuOf_anti _ hloA (midI_mono mm hij)
    have hβc : ∀ j, (fun j => nuOf (lam - wtPQ (mm + 1) P Q) (midI mm j)) j ≤ 2 * ccl := by
      intro j
      show nuOf (lam - wtPQ (mm + 1) P Q) (midI mm j) ≤ 2 * ccl
      have := hβZ j; have := hbd j; omega
    have hβ'A : Antitone (fun j => nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j)) :=
      fun i j hij => nuOf_anti _ hlo'A (midI_mono mm hij)
    have hβ'c : ∀ j, (fun j => nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j)) j ≤ 2 * ccl := by
      intro j
      show nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j) ≤ 2 * ccl
      have := hβ'Z j; have := hbd j.rev; omega
    have hS : ∀ b, ∃ s0 ∈ dualWeyl R.O (mm + 1 + 1) (mm + 1 + 1) (nuOf (lam - wtPQ (mm + 1) P Q)),
        RowA 0 s0 (2 * ccl) ∧ RowA (Fin.last (mm + 1)) s0 0 ∧
          map (algebraMap R.O R.Kf) (detY R.O mm ^ Q * resY R.O mm s0) = u b := by
      intro b
      obtain ⟨f, hf, hfe⟩ := hu b
      rw [hαβ] at hf
      obtain ⟨w0, hw0, rfl⟩ := hDD R.O mm Q _ hmm hβA f hf
      obtain ⟨s0, hs0, hr0, hrl, hres⟩ := hLift R.O mm (2 * ccl) _ hβA hβc w0 hw0
      rw [shapeC_lo mm ccl P Q lam h0 hl] at hs0
      exact ⟨s0, hs0, hr0, hrl, by rw [hres]; exact hfe⟩
    have hS' : ∀ a', ∃ s0 ∈ dualWeyl R.O (mm + 1 + 1) (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))),
        RowA 0 s0 (2 * ccl) ∧ RowA (Fin.last (mm + 1)) s0 0 ∧ map (algebraMap R.O R.Kf) (resY R.O mm s0) = u' a' := by
      intro a'
      obtain ⟨f, hf, hfe⟩ := hu' a'
      obtain ⟨s0, hs0, hr0, hrl, hres⟩ := hLift R.O mm (2 * ccl) _ hβ'A hβ'c f hf
      rw [shapeC_lo' mm ccl P Q lam h0 hl] at hs0
      exact ⟨s0, hs0, hr0, hrl, by rw [hres]; exact hfe⟩
    choose s0 hs0 hs0r hs0l hs0e using hS
    choose t0 ht0 ht0r ht0l ht0e using hS'
    refine ⟨nb, fun b => map (algebraMap R.O R.Kf) (s0 b), fun a' => map (algebraMap R.O R.Kf) (t0 a'), ka, ?_, hka,
      fun b => ⟨⟨s0 b, hs0 b, rfl⟩, rowA_map _ 0 _ _ (hs0r b)⟩, fun a' => ⟨⟨t0 a', ht0 a', rfl⟩, rowA_map _ 0 _ _ (ht0r a')⟩, ?_⟩
    · have e : (fun j : Fin mm => ((nuOf lam (midI mm j) : ℕ) : ℤ)) = fun j => lam (midI mm j) + ((Q : ℤ) + ccl) := by
        funext j
        rw [hαZ j]; ring
      rw [hnb, e]
      exact weylDim_add_const mm (fun j => lam (midI mm j)) ((Q : ℤ) + ccl)
    · intro a' b F hF
      have e1 := hLM R.Kf mm Q L F (map (algebraMap R.O R.Kf) (s0 b)) (map (algebraMap R.O R.Kf) (t0 a'))
        (hMu p n' R mm hmm P Q F hF)
      have hF0 : hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q)) ∈
          dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (wtPQ (mm + 1) 0 Q)) := hwMem R.Kf _ _ le_rfl _ (hwA 0 Q)
      have hF0sub := hMu p n' R mm hmm 0 Q _ hF0
      have e2 := hLM R.Kf mm Q L _ (map (algebraMap R.O R.Kf) (s0 b)) (map (algebraMap R.O R.Kf) (t0 a')) hF0sub
      have hSK : map (algebraMap R.O R.Kf) (s0 b) ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (lam - wtPQ (mm + 1) P Q)) :=
        dualWeylMap R.O R.Kf _ _ _ _ _ (hs0 b)
      have hTK : map (algebraMap R.O R.Kf) (t0 a') ∈
          dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))) :=
        dualWeylMap R.O R.Kf _ _ _ _ _ (ht0 a')
      have hInv' : PhInv R.Kf mm (Q + 2 * ccl)
          (fun j => (nuOf (wtPQ (mm + 1) 0 Q) + nuOf (lam - wtPQ (mm + 1) P Q)) (midI mm j))
          (fun j => nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j)) L := by
        have e : (fun j => (nuOf (wtPQ (mm + 1) 0 Q) + nuOf (lam - wtPQ (mm + 1) P Q)) (midI mm j)) =
            fun j => nuOf lam (midI mm j) := by
          funext j
          rw [Pi.add_apply, nuOf_wt_mid]
          have := hαZ j; have := hβZ j; omega
        rw [e]; exact hInv
      have hΨmem := hMem R.Kf mm (Q + 2 * ccl) (nuOf (wtPQ (mm + 1) 0 Q) + nuOf (lam - wtPQ (mm + 1) P Q))
        (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))) (nuOf (wtPQ (mm + 1) (2 * ccl) (Q + 2 * ccl))) L
        (by rw [Pi.add_apply, nuOf_last, nuOf_last]) (nuOf_last _) (nuOf_last _)
        (by rw [nuOf_wt_zero, Pi.add_apply, nuOf_wt_zero, nuOf_lo_zero mm ccl P Q lam h0 hl,
              nuOf_lo'_zero mm ccl P Q lam h0 hl]; omega)
        (fun j => nuOf_wt_mid mm _ _ j) hInv' _ (dualWeyl_mul R.Kf _ _ _ _ hF0 hSK) _ hTK
      have hr0 : RowA 0 (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q))) Q := by
        have h := rowA_hw R.Kf _ _ (hwA 0 Q) 0
        rwa [nuOf_wt_zero, zero_add] at h
      have hrl : RowA (Fin.last (mm + 1)) (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q))) 0 := by
        have h := rowA_hw R.Kf _ _ (hwA 0 Q) (Fin.last (mm + 1))
        rwa [nuOf_last] at h
      have hΨ0 := rowA_lam hLC hSR R.Kf mm L 0 _ _ _ _
        (rowA_mul 0 _ _ _ _ hr0 (rowA_map (algebraMap R.O R.Kf) 0 _ _ (hs0r b)))
        (rowA_map (algebraMap R.O R.Kf) 0 _ _ (ht0r a'))
      have hΨl := rowA_lam hLC hSR R.Kf mm L (Fin.last (mm + 1)) _ _ _ _
        (rowA_mul (Fin.last (mm + 1)) _ _ _ _ hrl (rowA_map (algebraMap R.O R.Kf) _ _ _ (hs0l b)))
        (rowA_map (algebraMap R.O R.Kf) _ _ _ (ht0l a'))
      have ed : Q + 2 * ccl + 2 * ccl = 2 * ccl + (Q + 2 * ccl) := by omega
      rw [ed] at hΨ0
      have hΨ := hTop p n' R mm hmm (2 * ccl) (Q + 2 * ccl) _ hΨmem hΨ0 hΨl
      have hres0 : resY R.Kf mm (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q))) = detY R.Kf mm ^ Q := by
        unfold resY
        rw [hF0sub, map_mul, eval_C, evalId_map, (hHw R.Kf _ _ _ (hwA 0 Q) (hwA 0 Q)).2, map_one, mul_one]
      have hκ : eval (idPoint R.Kf (mm + 1 + 1) (mm + 1 + 1))
          (lamOf R.Kf mm L (blockEmb R.Kf true (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q)) *
            map (algebraMap R.O R.Kf) (s0 b)) * blockEmb R.Kf false (map (algebraMap R.O R.Kf) (t0 a')))) =
          if a' = b then (p : R.Kf) ^ ka b else 0 := by
        have hub : u b = detY R.Kf mm ^ Q * map (algebraMap R.O R.Kf) (resY R.O mm (s0 b)) := by
          rw [← hs0e b, map_mul, map_pow, detY_map]
        rw [hLV, resY_mul, hres0, resY_map hSM, resY_map hSM, ht0e, ← hub, hdiag a' b]
      have hsh : nuOf (wtPQ (mm + 1) (2 * ccl) (Q + 2 * ccl)) =
          nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)) + nuOf (wtPQ (mm + 1) 0 Q) := by
        have := nuOf_wt_add mm (2 * ccl) (2 * ccl) 0 Q
        rwa [add_zero, add_comm (2 * ccl) Q] at this
      rw [hκ, hsh, (hHw R.Kf _ _ _ (hwA (2 * ccl) (2 * ccl)) (hwA 0 Q)).1] at hΨ
      have hne : hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q)) ≠ 0 := hwNe R.Kf _ _ le_rfl _
      have hΦ := mul_left_cancel₀ hne (a := hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q)))
        (c := C (if a' = b then (p : R.Kf) ^ ka b else 0) * hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl))))
        (by rw [← e2, hΨ]; ring)
      rw [e1, hΦ]
      split_ifs
      · rw [smul_eq_C_mul]; ring
      · rw [C_0, zero_mul, mul_zero]

end Formalism.MainNotions.flipOneThree.Pf

end
end

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

section LC

variable {K σ ρ : Type} [Field K]

private theorem coeff_lcoef_eq (L : MvPolynomial ρ K →ₗ[K] K) (f : MvPolynomial σ (MvPolynomial ρ K))
    (w : σ →₀ ℕ) : AddMonoidAlgebra.coeff (lcoef L f) w = L (AddMonoidAlgebra.coeff f w) :=
  coeff_sum_monomial_linear L f w

theorem qa_lcoef_C (L : MvPolynomial ρ K →ₗ[K] K) (b : MvPolynomial ρ K) :
    lcoef L (C b : MvPolynomial σ (MvPolynomial ρ K)) = C (L b) := by
  classical
  ext w
  rw [coeff_lcoef_eq, coeff_C, coeff_C]
  split_ifs <;> simp

theorem qa_lcoef_mapC_mul (L : MvPolynomial ρ K →ₗ[K] K) (G : MvPolynomial σ K)
    (h : MvPolynomial σ (MvPolynomial ρ K)) : lcoef L (map C G * h) = G * lcoef L h := by
  classical
  ext w

  rw [coeff_lcoef_eq, coeff_mul, coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coeff_map, coeff_lcoef_eq, MvPolynomial.C_mul', map_smul, smul_eq_mul]

theorem qa_eval_lcoef (L : MvPolynomial ρ K →ₗ[K] K) (x : σ → K) (h : MvPolynomial σ (MvPolynomial ρ K)) :
    eval x (lcoef L h) = L (eval (fun i => C (x i)) h) := by
  classical

  rw [show lcoef L h = ∑ u ∈ h.support, monomial u (L (AddMonoidAlgebra.coeff h u)) from rfl, map_sum]

  conv_rhs => rw [h.as_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [eval_monomial, eval_monomial]
  rw [show (u.prod fun n e => (C (x n) : MvPolynomial ρ K) ^ e) = C (u.prod fun n e => x n ^ e) by
    simp [Finsupp.prod, map_prod, map_pow]]
  rw [mul_comm (AddMonoidAlgebra.coeff h u), MvPolynomial.C_mul', map_smul, smul_eq_mul, mul_comm]

theorem qa_lcoef_rowAct {k n : ℕ} (L : MvPolynomial ρ K →ₗ[K] K) (g : Matrix (Fin k) (Fin k) K)
    (h : MvPolynomial (Fin k × Fin n) (MvPolynomial ρ K)) :
    lcoef L (rowAct (MvPolynomial ρ K) (g.map C) h) = rowAct K g (lcoef L h) := by
  classical
  have key : ∀ P : MvPolynomial (Fin k × Fin n) K,
      rowAct (MvPolynomial ρ K) (g.map C) (map C P) = map C (rowAct K g P) := by
    intro P
    have e := MvPolynomial.ringHom_ext
      (f := ((rowAct (MvPolynomial ρ K) (n := n) (g.map C)).toRingHom.comp (map C) :
        MvPolynomial (Fin k × Fin n) K →+* MvPolynomial (Fin k × Fin n) (MvPolynomial ρ K)))
      (g := ((map C).comp (rowAct K (n := n) g).toRingHom :
        MvPolynomial (Fin k × Fin n) K →+* MvPolynomial (Fin k × Fin n) (MvPolynomial ρ K)))
      (fun a => by simp [rowAct]) (fun i => by simp [rowAct, Matrix.map_apply, map_sum])
    simpa using RingHom.congr_fun e P
  conv_lhs => rw [h.as_sum]
  conv_rhs => rw [h.as_sum]

  simp only [map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hm : (monomial u (AddMonoidAlgebra.coeff h u) : MvPolynomial (Fin k × Fin n) (MvPolynomial ρ K)) =
      map C (monomial u 1) * C (AddMonoidAlgebra.coeff h u) := by
    rw [map_monomial, map_one, mul_comm, C_mul_monomial, mul_one]
  have hr1 : rowAct (MvPolynomial ρ K) (n := n) (g.map C) (C (AddMonoidAlgebra.coeff h u)) = C (AddMonoidAlgebra.coeff h u) := by simp [rowAct]
  have hr2 : rowAct K (n := n) g (C (L (AddMonoidAlgebra.coeff h u))) = C (L (AddMonoidAlgebra.coeff h u)) := by simp [rowAct]
  rw [hm, map_mul, key, hr1, qa_lcoef_mapC_mul, qa_lcoef_mapC_mul, qa_lcoef_C, map_mul, hr2]

end LC

section S2

variable {K : Type} [Field K] {r : ℕ}

theorem qa_blockEmb_C {S : Type} {k n : ℕ} (b : S) (a : K) : blockEmb K (k := k) (n := n) b (C a) = C a := by
  simp [blockEmb]

theorem qa_blockEmb_X {S : Type} {k n : ℕ} (b : S) (x : Fin k × Fin n) : blockEmb K b (X x) = X (b, x) := by
  simp [blockEmb]

theorem block_substitution_C (a : K) : sub2 K r (C a) = C (C a) := by
  simp [sub2]

theorem block_substitution_X (b : Bool) (x : Fin (r + 1 + 1) × Fin (r + 1 + 1)) :
    sub2 K r (X (b, x)) = map (blockEmb K (k := r) (n := r) b).toRingHom (subY K r (X x)) := by
  simp [sub2]

theorem block_substitution_blockEmb (b : Bool) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) :
    sub2 K r (blockEmb K b v) = map (blockEmb K (k := r) (n := r) b).toRingHom (subY K r v) := by
  induction v using MvPolynomial.induction_on
  next a =>
    rw [qa_blockEmb_C, block_substitution_C]
    simp [subY]
  next p q hp hq =>
    rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), map_add (f := _)]
  next p x hp =>
    rw [map_mul, map_mul, hp, qa_blockEmb_X, block_substitution_X, map_mul, map_mul]

theorem qa_blockEmb_comp_C (b : Bool) :
    ((blockEmb K (k := r) (n := r) b).toRingHom).comp C = (C : K →+* MvPolynomial (Bool × (Fin r × Fin r)) K) := RingHom.ext fun a => by simp

theorem qa_lamOf_apply (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K)
    (x : MvPolynomial (Bool × (Fin (r + 1 + 1) × Fin (r + 1 + 1))) K) : lamOf K r L x = lcoef L (sub2 K r x) := rfl

theorem qa_eval_map_block (b : Bool)
    (h : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) K)) :
    eval (fun i => (C (idPoint K (r + 1 + 1) (r + 1 + 1) i) : MvPolynomial (Bool × (Fin r × Fin r)) K))
        (map (blockEmb K (k := r) (n := r) b).toRingHom h) =
      blockEmb K b (eval (idPoint (MvPolynomial (Fin r × Fin r) K) (r + 1 + 1) (r + 1 + 1)) h) := by
  rw [MvPolynomial.eval_map]
  show _ = (blockEmb K (k := r) (n := r) b).toRingHom
    (MvPolynomial.eval₂ (RingHom.id _) (idPoint (MvPolynomial (Fin r × Fin r) K) (r + 1 + 1) (r + 1 + 1)) h)
  rw [MvPolynomial.eval₂_comp_left, RingHom.comp_id]
  congr 1
  funext i
  simp only [Function.comp_apply, idPoint]
  split_ifs <;> simp

end S2

theorem lamCoeffP : LamCoeffP := by
  classical
  intro K _ r L v t u

  rw [qa_lamOf_apply, map_mul, block_substitution_blockEmb, block_substitution_blockEmb, coeff_lcoef_eq, coeff_mul, map_sum]
  simp only [coeff_map]
  rfl

theorem lamMulP : LamMulP := by
  classical
  intro K _ r Q L F s t hF
  rw [qa_lamOf_apply, map_mul (blockEmb K true) F s, map_mul (sub2 K r), map_mul (sub2 K r),
    block_substitution_blockEmb, block_substitution_blockEmb, block_substitution_blockEmb, hF,
    map_mul (map (blockEmb K (k := r) (n := r) true).toRingHom), map_C, MvPolynomial.map_map,
    qa_blockEmb_comp_C, ← qa_lcoef_mapC_mul]
  congr 1
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  ring

theorem lamEvalP : LamEvalP := by
  classical
  intro K _ r L v t
  rw [qa_lamOf_apply, map_mul, block_substitution_blockEmb, block_substitution_blockEmb, qa_eval_lcoef, map_mul,
    qa_eval_map_block, qa_eval_map_block]
  rfl

theorem lamEquivP : LamEquivP := by
  intro K _ r L g v t
  have hcomm : ∀ (b : Bool) (P : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) K)),
      map (blockEmb K (k := r) (n := r) b).toRingHom
          (rowAct (MvPolynomial (Fin r × Fin r) K) (n := r + 1 + 1) (g.map C) P) =
        rowAct (MvPolynomial (Bool × (Fin r × Fin r)) K) (n := r + 1 + 1) (g.map C)
          (map (blockEmb K (k := r) (n := r) b).toRingHom P) := by
    intro b P
    have e := MvPolynomial.ringHom_ext
      (f := ((map (blockEmb K (k := r) (n := r) b).toRingHom).comp
          (rowAct (MvPolynomial (Fin r × Fin r) K) (n := r + 1 + 1) (g.map C)).toRingHom :
        MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) K) →+*
          MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K)))
      (g := ((rowAct (MvPolynomial (Bool × (Fin r × Fin r)) K) (n := r + 1 + 1) (g.map C)).toRingHom.comp
          (map (blockEmb K (k := r) (n := r) b).toRingHom) :
        MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) K) →+*
          MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K)))
      (fun c => by simp [rowAct]) (fun i => by simp [rowAct, Matrix.map_apply, map_sum])
    simpa using RingHom.congr_fun e P
  rw [qa_lamOf_apply, qa_lamOf_apply, map_mul (sub2 K r), map_mul (sub2 K r), block_substitution_blockEmb,
    block_substitution_blockEmb, block_substitution_blockEmb, block_substitution_blockEmb, qa_subY_rowAct, qa_subY_rowAct, hcomm, hcomm,
    ← map_mul (rowAct (MvPolynomial (Bool × (Fin r × Fin r)) K) (n := r + 1 + 1) (g.map C)), qa_lcoef_rowAct]

end Formalism.MainNotions.flipOneThree.Pf

end
end

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial

variable (A : Type) [CommRing A] (r : ℕ)

theorem detY_eq : detY A r = (genY A r).det := rfl

end Formalism.MainNotions.flipOneThree.Pf

end
end
