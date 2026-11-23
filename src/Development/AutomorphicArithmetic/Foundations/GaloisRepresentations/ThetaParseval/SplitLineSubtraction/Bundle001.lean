module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.TwoUpOKOf
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

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions GlobalTheory.HeckeGal GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.V.Af (algSat)
open UpperTheory.Gal.TP.Sub

private theorem multiset_bind_pure_coe_eq_map (S : Multiset ℂˣ) :
    (do let a ← S; Pure.pure (a : ℂ) : Multiset ℂ) = Multiset.map (fun a : ℂˣ => (a : ℂ)) S := by
  show Multiset.bind S (fun a => {(a : ℂ)}) = _
  exact Multiset.bind_singleton _ _

private theorem multiset_map_fin_eq_map_range (t : ℕ) (f : ℕ → ℂ) :
    Multiset.map (fun i : Fin t => f i) Finset.univ.val = Multiset.map f (Finset.range t).val := by
  rw [Fin.univ_val_map, List.ofFn_eq_map]
  have h : List.map (fun i : Fin t => f i) (List.finRange t) = List.map f (List.range t) := by
    rw [← List.map_coe_finRange_eq_range, List.map_map]
    rfl
  rw [h, ← Multiset.map_coe]
  rfl

theorem UpperTheory.Gal.TP.Sub.satId_holds :
    SatId := by
  intro E _ _ w n t B x y k c hk hc
  have hq0 : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact w.ne_bot
  have hs : ∀ m : ℕ, (((((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((m : ℝ) - 1) / 2) : ℝ)) : ℂ) =
      ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((m : ℂ) - 1) / 2) := by
    intro m
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  simp only [algSat, GlobalTheory.LFun.seg, hs]
  rw [multiset_bind_pure_coe_eq_map, multiset_bind_pure_coe_eq_map]
  simp only [Multiset.map_add (f := _), Multiset.map_map]
  have hR := multiset_map_fin_eq_map_range t (fun j : ℕ => (x : ℂ) *
      ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) + 2 * t - 2) / 2 - (j : ℂ)))
  have hc' : c = fun i : Fin t => (fun j : ℕ => (x : ℂ) *
      ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) + 2 * t - 2) / 2 - (j : ℂ))) (i : ℕ) := funext hc
  rw [hc', hR]
  congr 1
  · apply Multiset.map_congr rfl
    intro b _
    simp only [Function.comp, Units.val_mul, Units.val_inv_eq_inv_val, hk]
    have hsplit : (((n + t : ℕ) : ℂ) - 1) / 2 = ((n : ℂ) - 1) / 2 + (t : ℂ) / 2 := by
      push_cast
      ring
    rw [hsplit, Complex.cpow_add _ _ hq0, Complex.cpow_neg, mul_inv, mul_inv, inv_inv, inv_inv]
    ring
  · apply Multiset.map_congr rfl
    intro j _
    simp only [Function.comp, Units.val_mul, GlobalTheory.LFun.npowU, Units.val_mk0, GlobalTheory.LFun.npow]
    rw [mul_left_comm, ← Complex.cpow_add _ _ hq0]
    congr 2
    push_cast
    ring
end

section

namespace UpperTheory.Gal.TP.Sub

open Formalism.BasicNotions

private theorem multiset_map_fin_add_eq_add {n t : ℕ} (f : Fin (n + t) → ℤ) :
    Multiset.map f Finset.univ.val =
      Multiset.map (fun k : Fin n => f (Fin.castAdd t k)) Finset.univ.val +
        Multiset.map (fun i : Fin t => f (Fin.natAdd n i)) Finset.univ.val := by
  rw [Fin.univ_val_map, List.ofFn_add, ← Multiset.coe_add, Fin.univ_val_map, Fin.univ_val_map]
  rfl

private theorem multiset_map_fin_rev_eq {n : ℕ} (f : Fin n → ℤ) :
    Multiset.map f Finset.univ.val = Multiset.map (fun k : Fin n => f k.rev) Finset.univ.val := by
  conv_lhs => rw [← Multiset.map_univ_val_equiv (Fin.revPerm : Equiv.Perm (Fin n)), Multiset.map_map]
  rfl

theorem wtId_holds : WtId := by
  intro n t lam lam' mX mW hL
  refine ⟨fun m p hm hp => ?_, fun m p hm hp => ?_⟩
  · unfold wtJumps
    rw [multiset_map_fin_add_eq_add]
    congr 1
    · rw [Multiset.map_map]
      congr 1
      funext k
      have h1 := hL (Fin.castAdd t k)
      simp only [Fin.coe_castAdd, k.2, dif_pos, Fin.eta] at h1
      simp only [Function.comp_apply, Fin.coe_castAdd]
      omega
    · rw [multiset_map_fin_rev_eq (fun i : Fin t => -p i)]
      congr 1
      funext i
      have h1 := hL (Fin.natAdd n i)
      have h2 := hp i.rev
      simp only [Fin.coe_natAdd, Fin.val_rev] at h1 h2 ⊢
      rw [dite_eq_right (by omega)] at h1
      have hi := i.2
      push_cast at h1
      omega
  · unfold wtJumps
    rw [multiset_map_fin_rev_eq, multiset_map_fin_rev_eq (fun k : Fin n => ((k : ℕ) : ℤ) - lam.dual.w k)]
    simp only [DomWeight.dual, Fin.rev_rev, Fin.val_rev]
    rw [multiset_map_fin_add_eq_add]
    congr 1
    · rw [Multiset.map_map]
      congr 1
      funext k
      have h1 := hL (Fin.castAdd t k)
      simp only [Fin.coe_castAdd, k.2, dif_pos, Fin.eta] at h1
      simp only [Function.comp_apply, Fin.coe_castAdd]
      have hk := k.2
      omega
    · congr 1
      funext i
      have h1 := hL (Fin.natAdd n i)
      have h2 := hp i
      simp only [Fin.coe_natAdd] at h1 h2 ⊢
      rw [dite_eq_right (by omega)] at h1
      have hi := i.2
      have hc : ((n + t - (n + (i : ℕ) + 1) : ℕ) : ℤ) = (t : ℤ) - 1 - (i : ℕ) := by
        rw [Nat.cast_sub (by omega)]
        push_cast
        ring
      push_cast at h1
      rw [hc]
      omega

end UpperTheory.Gal.TP.Sub
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions GlobalTheory.HeckeGal GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.V.Af (algSat)
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.embSplit_holds :
    EmbSplit := by
  intro E _ _ _ emb
  have hcj : ∀ (φ : E →+* ℂ), (ComplexEmbedding.conjugate φ).comp
      (algebraMap (maximalRealSubfield E) E) =
      ComplexEmbedding.conjugate (φ.comp (algebraMap (maximalRealSubfield E) E)) := by
    intro φ
    ext x
    simp [ComplexEmbedding.conjugate_coe_eq]
  have hinj : ∀ (w w' : InfinitePlace (maximalRealSubfield E)), w.embedding = w'.embedding → w = w' := by
    intro w w' h
    rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w', h]
  refine ⟨?_, ?_, ?_⟩
  · intro τ
    let w := InfinitePlace.mk (τ.comp (algebraMap (maximalRealSubfield E) E))
    refine ⟨w, ?_⟩
    have hw : (InfinitePlace.mk τ).comap (algebraMap (maximalRealSubfield E) E) =
        (InfinitePlace.mk (emb w).1).comap (algebraMap (maximalRealSubfield E) E) := by
      rw [InfinitePlace.comap_mk, InfinitePlace.comap_mk, (emb w).2, InfinitePlace.mk_embedding]
    have hmk : InfinitePlace.mk τ = InfinitePlace.mk (emb w).1 :=
      (IsCMField.equivInfinitePlace E).injective hw
    rcases InfinitePlace.mk_eq_iff.1 hmk with h | h
    · exact Or.inl h
    · right
      rw [← h]
      ext x
      simp [ComplexEmbedding.conjugate_coe_eq]
  · intro w w' h
    apply hinj
    rw [← (emb w).2, ← (emb w').2, h]
  · intro w w' h
    have h1 : w.embedding = ComplexEmbedding.conjugate w'.embedding := by
      rw [← (emb w).2, ← (emb w').2, h, hcj]
    have hww : w = w' := by
      rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w', h1,
        InfinitePlace.mk_conjugate_eq]
    subst hww
    apply IsTotallyComplex.complexEmbedding_not_isReal (emb w).1
    exact h.symm
end
