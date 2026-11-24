module

public import Formalism.PadicSubsetSums.CentralIdempotents.GaloisIrreducibility
public import Formalism.PadicSubsetSums.StableGradedCounts.IRRIrredCountUpper
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Polynomial UniqueFactorizationMonoid

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility



theorem type_count_exact : TypeCountExact := by
  classical
  intro K _ _ N n hN
  suffices H : ((Finset.univ : Finset (Fin N → K)).filter (fun c =>
      Squarefree (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0 ∧
      ∀ d ∈ Finset.Icc 1 N, ((normalizedFactors (monicOf c)).map
        Polynomial.natDegree).count d = n d)).card =
      ∏ d ∈ Finset.Icc 1 N,
        (((Finset.univ : Finset (Fin d → K)).filter
          (fun c => Irreducible (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0)).card).choose (n d) by
    convert H
  have L1 : ∀ m : Multiset K[X], (∀ q ∈ m, q.Monic ∧ Irreducible q ∧ q.coeff 0 ≠ 0) →
      m.prod.Monic ∧ normalizedFactors m.prod = m ∧
        m.prod.natDegree = (m.map Polynomial.natDegree).sum ∧ m.prod.coeff 0 ≠ 0 := by
    intro m h
    have hm : ∀ q ∈ m, q.Monic := fun q hq => (h q hq).1
    refine ⟨by simpa using monic_multiset_prod_of_monic m id hm,
      ?_, natDegree_multiset_prod_of_monic m hm, ?_⟩
    · rw [normalizedFactors_prod_eq m (fun q hq => (h q hq).2.1)]
      simpa using Multiset.map_congr rfl (fun q hq => (hm q hq).normalize_eq_self)
    · rw [coeff_zero_eq_eval_zero, eval_multiset_prod]
      exact Multiset.prod_ne_zero (by
        rintro hzero
        obtain ⟨q, hq, heval⟩ := Multiset.mem_map.mp hzero
        exact (h q hq).2.2 (coeff_zero_eq_eval_zero q ▸ heval))
  have L2 : ∀ (T : Finset K[X]) (d : ℕ), (T.val.map Polynomial.natDegree).count d =
      (T.filter (fun q => q.natDegree = d)).card := by
    intro T d
    rw [Multiset.count_map]
    exact congrArg Multiset.card (Multiset.filter_congr (fun x _ => eq_comm))
  have F : ∀ c : Fin N → K, (monicOf c).coeff 0 ≠ 0 → ∀ q ∈ normalizedFactors (monicOf c),
      q.Monic ∧ Irreducible q ∧ q.coeff 0 ≠ 0 ∧ 1 ≤ q.natDegree ∧ q.natDegree ≤ N := by
    intro c hc q hq
    have hirr := irreducible_of_normalized_factor q hq
    have hmon : q.Monic := (normalize_normalized_factor q hq) ▸ monic_normalize hirr.ne_zero
    have hdvd := dvd_of_mem_normalizedFactors hq
    refine ⟨hmon, hirr, fun h0 => hc (X_dvd_iff.mp ((X_dvd_iff.mpr h0).trans hdvd)),
      Irreducible.natDegree_pos hirr, ?_⟩
    simpa [monicOf_natDegree] using natDegree_le_of_dvd hdvd (monicOf_monic c).ne_zero
  have P (c : Fin N → K) (hc : (monicOf c).coeff 0 ≠ 0) :
      (normalizedFactors (monicOf c)).prod = monicOf c := by
    have hm : (normalizedFactors (monicOf c)).prod.Monic := by
      simpa using monic_multiset_prod_of_monic _ id (fun q hq => (F c hc q hq).1)
    exact eq_of_monic_of_associated hm (monicOf_monic c) (prod_normalizedFactors (monicOf_monic c).ne_zero)
  set Irr : ℕ → Finset K[X] := fun d => ((Finset.univ : Finset (Fin d → K)).filter
    (fun c => Irreducible (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0)).image monicOf with hIrrdef
  have hIrr : ∀ (d : ℕ) (q : K[X]), q ∈ Irr d ↔
      q.Monic ∧ q.natDegree = d ∧ Irreducible q ∧ q.coeff 0 ≠ 0 := by
    intro d q
    simp only [Irr, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨c, ⟨h1, h2⟩, rfl⟩
      exact ⟨monicOf_monic c, monicOf_natDegree c, h1, h2⟩
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨fun i => q.coeff i, ?_, monicOf_coeffs h1 h2⟩
      rw [monicOf_coeffs h1 h2]
      exact ⟨h3, h4⟩
  set U : ((d : ℕ) → d ∈ Finset.Icc 1 N → Finset K[X]) → Finset K[X] :=
    fun f => (Finset.Icc 1 N).attach.biUnion (fun x => f x.1 x.2) with hUdef
  have hmemT : ∀ (f : (d : ℕ) → d ∈ Finset.Icc 1 N → Finset K[X]) (q : K[X]),
      q ∈ U f ↔ ∃ d, ∃ hd : d ∈ Finset.Icc 1 N, q ∈ f d hd := by
    intro f q
    simp only [U]
    rw [Finset.mem_biUnion]
    constructor
    · rintro ⟨x, _, hx⟩
      exact ⟨x.1, x.2, hx⟩
    · rintro ⟨d, hd, hq⟩
      exact ⟨⟨d, hd⟩, Finset.mem_attach _ _, hq⟩
  have key : ∀ f : ((d : ℕ) → d ∈ Finset.Icc 1 N → Finset K[X]),
      (∀ d (hd : d ∈ Finset.Icc 1 N), f d hd ∈ (Irr d).powersetCard (n d)) →
      (U f).val.prod.Monic ∧ normalizedFactors (U f).val.prod = (U f).val ∧
        (U f).val.prod.natDegree = N ∧ (U f).val.prod.coeff 0 ≠ 0 ∧
        ∀ d (hd : d ∈ Finset.Icc 1 N), (U f).filter (fun q => q.natDegree = d) = f d hd := by
    intro f hf
    have hprop : ∀ d (hd : d ∈ Finset.Icc 1 N) q, q ∈ f d hd →
        q.Monic ∧ q.natDegree = d ∧ Irreducible q ∧ q.coeff 0 ≠ 0 := fun d hd q hq =>
      (hIrr d q).mp ((Finset.mem_powersetCard.mp (hf d hd)).1 hq)
    have hfib : ∀ d (hd : d ∈ Finset.Icc 1 N),
        (U f).filter (fun q => q.natDegree = d) = f d hd := by
      intro d hd
      ext q
      rw [Finset.mem_filter, hmemT]
      constructor
      · rintro ⟨⟨d', hd', hq⟩, hdeg⟩
        have hdd : d' = d := (hprop d' hd' q hq).2.1.symm.trans hdeg
        subst hdd
        exact hq
      · intro hq
        exact ⟨⟨d, hd, hq⟩, (hprop d hd q hq).2.1⟩
    have hall : ∀ q ∈ (U f).val, q.Monic ∧ Irreducible q ∧ q.coeff 0 ≠ 0 := by
      intro q hq
      obtain ⟨d, hd, hq'⟩ := (hmemT f q).mp hq
      obtain ⟨h1, _, h3, h4⟩ := hprop d hd q hq'
      exact ⟨h1, h3, h4⟩
    obtain ⟨hmon, hnf, hdeg, hc0⟩ := L1 _ hall
    refine ⟨hmon, hnf, ?_, hc0, hfib⟩
    rw [hdeg, ← hN]
    have hmaps : ∀ q ∈ U f, q.natDegree ∈ Finset.Icc 1 N := by
      intro q hq
      obtain ⟨d, hd, hq'⟩ := (hmemT f q).mp hq
      rw [(hprop d hd q hq').2.1]
      exact hd
    have hsum : ((U f).val.map Polynomial.natDegree).sum = ∑ q ∈ U f, q.natDegree := rfl
    rw [hsum, ← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl ?_
    intro d hd
    rw [hfib d hd, Finset.sum_const_nat (fun q hq => (hprop d hd q hq).2.1),
      (Finset.mem_powersetCard.mp (hf d hd)).2, mul_comm]
  have hTval : ∀ c : Fin N → K, Squarefree (monicOf c) →
      (normalizedFactors (monicOf c)).toFinset.val = normalizedFactors (monicOf c) := by
    intro c hsq
    rw [Multiset.toFinset_val]
    exact Multiset.dedup_eq_self.mpr
      ((squarefree_iff_nodup_normalizedFactors (monicOf_monic c).ne_zero).mp hsq)
  refine (Finset.card_nbij' (t := (Finset.Icc 1 N).pi (fun d => (Irr d).powersetCard (n d)))
    (fun (c : Fin N → K) (d : ℕ) (_ : d ∈ Finset.Icc 1 N) =>
      (normalizedFactors (monicOf c)).toFinset.filter (fun q => q.natDegree = d))
    (fun (f : (d : ℕ) → d ∈ Finset.Icc 1 N → Finset K[X]) (k : Fin N) => ((U f).val.prod).coeff k)
    ?_ ?_ ?_ ?_).trans ?_
  · intro c hc
    rw [Finset.mem_coe, Finset.filter_congr_decidable, Finset.mem_filter] at hc
    obtain ⟨_, hsq, hc0, hcount⟩ := hc
    rw [Finset.mem_coe, Finset.mem_pi]
    intro d hd
    rw [Finset.mem_powersetCard]
    constructor
    · intro q hq
      rw [Finset.mem_filter, Multiset.mem_toFinset] at hq
      obtain ⟨h1, h2, h3, _, _⟩ := F c hc0 q hq.1
      exact (hIrr d q).mpr ⟨h1, hq.2, h2, h3⟩
    · have h := L2 (normalizedFactors (monicOf c)).toFinset d
      rw [hTval c hsq] at h
      rw [← h]
      exact hcount d hd
  · intro f hf
    rw [Finset.mem_coe, Finset.mem_pi] at hf
    obtain ⟨hmon, hnf, hdeg, hc0, hfib⟩ := key f hf
    have hp := monicOf_coeffs hmon hdeg
    rw [Finset.mem_coe, Finset.filter_congr_decidable, Finset.mem_filter]
    dsimp only
    rw [hp]
    refine ⟨Finset.mem_univ _, (squarefree_iff_nodup_normalizedFactors hmon.ne_zero).mpr ?_, hc0, ?_⟩
    · rw [hnf]
      exact (U f).nodup
    · intro d hd
      rw [hnf, L2, hfib d hd]
      exact (Finset.mem_powersetCard.mp (hf d hd)).2
  · intro c hc
    rw [Finset.mem_coe, Finset.filter_congr_decidable, Finset.mem_filter] at hc
    obtain ⟨_, hsq, hc0, _⟩ := hc
    have hU : U (fun d _ => (normalizedFactors (monicOf c)).toFinset.filter
        (fun q => q.natDegree = d)) = (normalizedFactors (monicOf c)).toFinset := by
      ext q
      simp only [U]
      rw [Finset.mem_biUnion]
      constructor
      · rintro ⟨x, _, hq⟩
        exact (Finset.mem_filter.mp hq).1
      · intro hq
        obtain ⟨_, _, _, h4, h5⟩ := F c hc0 q (Multiset.mem_toFinset.mp hq)
        exact ⟨⟨q.natDegree, Finset.mem_Icc.mpr ⟨h4, h5⟩⟩, Finset.mem_attach _ _,
          Finset.mem_filter.mpr ⟨hq, rfl⟩⟩
    funext k
    dsimp only
    rw [hU, hTval c hsq, P c hc0, monicOf_coeff]
  · intro f hf
    rw [Finset.mem_coe, Finset.mem_pi] at hf
    obtain ⟨hmon, hnf, hdeg, _, hfib⟩ := key f hf
    funext d hd
    dsimp only
    rw [monicOf_coeffs hmon hdeg, hnf, Finset.val_toFinset, hfib d hd]
  · rw [Finset.card_pi]
    refine Finset.prod_congr rfl ?_
    intro d _
    rw [Finset.card_powersetCard]
    simp only [Irr]
    rw [Finset.card_image_of_injective _ monicOf_injective]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
