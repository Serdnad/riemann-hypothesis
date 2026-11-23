module

public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.LinearAlgebra.Quotient.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free

@[expose] public section

section

open Finset Function

namespace GlobalTheory

theorem multilinear_vanish_of_prod_vanish_of_agree_off_finset {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {X : ι → Type} (A : ∀ i, Submodule K (X i → K)) {M : Type} [AddCommGroup M]
    [Module K M] (P : (∀ i, A i) →ₘₗ[K] M) (S : Finset ι) :
    ∀ {D : Type} (s : Finset D) (c : D → K) (f : D → ∀ i, A i),
      (∀ i ∉ S, ∀ d ∈ s, ∀ d' ∈ s, f d i = f d' i) →
      (∀ x : ∀ i, X i, ∑ d ∈ s, c d * ∏ i, (f d i : X i → K) (x i) = 0) →
      ∑ d ∈ s, c d • P (f d) = 0 := by
  induction S using Finset.induction_on with
  | empty =>
    intro D s c f hconst hx
    rcases s.eq_empty_or_nonempty with rfl | ⟨d₀, hd₀⟩
    · simp
    have hf : ∀ d ∈ s, f d = f d₀ := fun d hd =>
      funext fun i => hconst i (Finset.notMem_empty i) d hd d₀ hd₀
    have hsum : ∑ d ∈ s, c d • P (f d) = (∑ d ∈ s, c d) • P (f d₀) := by
      rw [Finset.sum_smul]; exact Finset.sum_congr rfl fun d hd => by rw [hf d hd]
    have hx' : ∀ x : ∀ i, X i, (∑ d ∈ s, c d) * ∏ i, (f d₀ i : X i → K) (x i) = 0 := by
      intro x; rw [Finset.sum_mul, ← hx x]
      exact Finset.sum_congr rfl fun d hd => by rw [hf d hd]
    rw [hsum]
    by_cases hc : ∑ d ∈ s, c d = 0
    · rw [hc, zero_smul]
    · by_contra hne
      have hex : ∀ i, ∃ t : X i, (f d₀ i : X i → K) t ≠ 0 := by
        intro i
        by_contra h
        push Not at h
        apply hne
        have h0 : f d₀ i = 0 := by
          apply Subtype.ext
          funext t
          simpa using h t
        rw [P.map_coord_zero i h0, smul_zero]
      choose x hxne using hex
      have h1 := hx' x
      rw [mul_eq_zero] at h1
      rcases h1 with h | h
      · exact hc h
      · exact (Finset.prod_ne_zero_iff.mpr fun i _ => hxne i) h
  | insert i₀ S hi₀ ih =>
    intro D s c f hconst hx
    classical
    let W : Submodule K (A i₀) := Submodule.span K (↑(s.image fun d => f d i₀))
    let b := Module.finBasis K W
    have hmem : ∀ d ∈ s, f d i₀ ∈ W := fun d hd =>
      Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨d, hd, rfl⟩)
    let a : D → Fin (Module.finrank K W) → K := fun d l =>
      if hd : d ∈ s then b.repr ⟨f d i₀, hmem d hd⟩ l else 0
    have hexp : ∀ d ∈ s, f d i₀ = ∑ l, a d l • (b l : A i₀) := by
      intro d hd
      have h := congrArg Subtype.val (b.sum_repr ⟨f d i₀, hmem d hd⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h
      simp only [a, dite_eq_left hd]
      exact h.symm
    have hP : ∀ d ∈ s, P (f d) = ∑ l, a d l • P (update (f d) i₀ (b l)) := by
      intro d hd
      have e : f d = update (f d) i₀ (∑ l, a d l • (b l : A i₀)) := by
        rw [← hexp d hd, update_eq_self]
      rw [e, P.map_update_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [P.map_update_smul, RingHom.id_apply, update_idem]

    have hsplit : ∀ (g : ∀ i, A i) (y : ∀ i, X i), ∏ i, (g i : X i → K) (y i) =
        (g i₀ : X i₀ → K) (y i₀) * ∏ i ∈ univ.erase i₀, (g i : X i → K) (y i) := fun g y =>
      (Finset.mul_prod_erase univ (fun i => (g i : X i → K) (y i)) (mem_univ i₀)).symm
    have hupd : ∀ (g : ∀ i, A i) (v : A i₀) (y : ∀ i, X i),
        ∏ i ∈ univ.erase i₀, (update g i₀ v i : X i → K) (y i) =
          ∏ i ∈ univ.erase i₀, (g i : X i → K) (y i) := fun g v y =>
      Finset.prod_congr rfl fun i hi => by rw [update_of_ne (Finset.ne_of_mem_erase hi)]
    have hupdx : ∀ (g : ∀ i, A i) (y : ∀ i, X i) (t : X i₀),
        ∏ i ∈ univ.erase i₀, (g i : X i → K) (update y i₀ t i) =
          ∏ i ∈ univ.erase i₀, (g i : X i → K) (y i) := fun g y t =>
      Finset.prod_congr rfl fun i hi => by rw [update_of_ne (Finset.ne_of_mem_erase hi)]
    have hli : LinearIndependent K (fun l => ((b l : A i₀) : X i₀ → K)) :=
      b.linearIndependent.map' ((A i₀).subtype ∘ₗ W.subtype)
        (LinearMap.ker_eq_bot_of_injective (Subtype.val_injective.comp Subtype.val_injective))

    have hB : ∀ (x : ∀ i, X i) (l : Fin (Module.finrank K W)),
        ∑ d ∈ s, c d * a d l * ∏ i ∈ univ.erase i₀, (f d i : X i → K) (x i) = 0 := by
      intro x
      refine Fintype.linearIndependent_iff.mp hli _ ?_
      funext t
      have h := hx (update x i₀ t)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← h]
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [hsplit, hupdx, update_self, hexp d hd]
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    have hstep : ∑ d ∈ s, c d • P (f d) =
        ∑ l, ∑ d ∈ s, (c d * a d l) • P (update (f d) i₀ (b l)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [hP d hd, Finset.smul_sum]
      simp only [mul_smul]
    rw [hstep]
    refine Finset.sum_eq_zero fun l _ => ih s (fun d => c d * a d l)
      (fun d => update (f d) i₀ (b l)) ?_ ?_
    · intro i hi d hd d' hd'
      by_cases h : i = i₀
      · subst h; simp
      · simp only [update_of_ne h]
        exact hconst i (by simp [h, hi]) d hd d' hd'
    · intro x
      have h := hB x l
      calc ∑ d ∈ s, c d * a d l * ∏ i, (update (f d) i₀ (b l) i : X i → K) (x i)
          = ((b l : A i₀) : X i₀ → K) (x i₀) *
              ∑ d ∈ s, c d * a d l * ∏ i ∈ univ.erase i₀, (f d i : X i → K) (x i) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun d _ => ?_
            rw [hsplit, hupd, update_self]
            ring
        _ = 0 := by rw [h, mul_zero]

theorem multilinear_vanish_of_prod_vanish {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {X : ι → Type} (A : ∀ i, Submodule K (X i → K)) {M : Type} [AddCommGroup M]
    [Module K M] (P : (∀ i, A i) →ₘₗ[K] M) {D : Type} (s : Finset D) (c : D → K)
    (f : D → ∀ i, A i)
    (hx : ∀ x : ∀ i, X i, ∑ d ∈ s, c d * ∏ i, (f d i : X i → K) (x i) = 0) :
    ∑ d ∈ s, c d • P (f d) = 0 :=
  multilinear_vanish_of_prod_vanish_of_agree_off_finset A P univ s c f (fun i hi => absurd (mem_univ i) hi) hx

end GlobalTheory
end

section

open Finset Function in

theorem _root_.GlobalTheory.T.sum_smul_multilinear_eq_zero_of_prod_vanish : ∀ {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} (A : ∀ i, Submodule K (X i → K)) {M : Type} [AddCommGroup M] [Module K M] (P : (∀ i, A i) →ₘₗ[K] M) {D : Type} (s : Finset D) (c : D → K) (f : D → ∀ i, A i), (∀ x : ∀ i, X i, ∑ d ∈ s, c d * ∏ i, (f d i : X i → K) (x i) = 0) → ∑ d ∈ s, c d • P (f d) = 0 := by
  intro K _ ι _ _ X A M _ _ P
  have vanish (S : Finset ι) :
      ∀ {D : Type} (s : Finset D) (c : D → K) (f : D → ∀ i, A i),
        (∀ i ∉ S, ∀ d ∈ s, ∀ d' ∈ s, f d i = f d' i) →
        (∀ x : ∀ i, X i, ∑ d ∈ s, c d * ∏ i, (f d i : X i → K) (x i) = 0) →
        ∑ d ∈ s, c d • P (f d) = 0 := by
    induction S using Finset.induction_on with
    | empty =>
      intro D s c f hconst hx
      rcases s.eq_empty_or_nonempty with rfl | ⟨d₀, hd₀⟩
      · simp
      have hf : ∀ d ∈ s, f d = f d₀ := fun d hd =>
        funext fun i => hconst i (Finset.notMem_empty i) d hd d₀ hd₀
      have hsum : ∑ d ∈ s, c d • P (f d) = (∑ d ∈ s, c d) • P (f d₀) := by
        rw [Finset.sum_smul]; exact Finset.sum_congr rfl fun d hd => by rw [hf d hd]
      have hx' : ∀ x : ∀ i, X i, (∑ d ∈ s, c d) * ∏ i, (f d₀ i : X i → K) (x i) = 0 := by
        intro x; rw [Finset.sum_mul, ← hx x]
        exact Finset.sum_congr rfl fun d hd => by rw [hf d hd]
      rw [hsum]
      by_cases hc : ∑ d ∈ s, c d = 0
      · rw [hc, zero_smul]
      · by_contra hne
        have hex : ∀ i, ∃ t : X i, (f d₀ i : X i → K) t ≠ 0 := by
          intro i
          by_contra h
          push Not at h
          apply hne
          have h0 : f d₀ i = 0 := by
            apply Subtype.ext
            funext t
            simpa using h t
          rw [P.map_coord_zero i h0, smul_zero]
        choose x hxne using hex
        have h1 := hx' x
        rw [mul_eq_zero] at h1
        rcases h1 with h | h
        · exact hc h
        · exact (Finset.prod_ne_zero_iff.mpr fun i _ => hxne i) h
    | insert i₀ S hi₀ ih =>
      intro D s c f hconst hx
      classical
      let W : Submodule K (A i₀) := Submodule.span K (↑(s.image fun d => f d i₀))
      let b := Module.finBasis K W
      have hmem : ∀ d ∈ s, f d i₀ ∈ W := fun d hd =>
        Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨d, hd, rfl⟩)
      let a : D → Fin (Module.finrank K W) → K := fun d l =>
        if hd : d ∈ s then b.repr ⟨f d i₀, hmem d hd⟩ l else 0
      have hexp : ∀ d ∈ s, f d i₀ = ∑ l, a d l • (b l : A i₀) := by
        intro d hd
        have h := congrArg Subtype.val (b.sum_repr ⟨f d i₀, hmem d hd⟩)
        simp only [Submodule.coe_sum, Submodule.coe_smul] at h
        simp only [a, dite_eq_left hd]
        exact h.symm
      have hP : ∀ d ∈ s, P (f d) = ∑ l, a d l • P (update (f d) i₀ (b l)) := by
        intro d hd
        have e : f d = update (f d) i₀ (∑ l, a d l • (b l : A i₀)) := by
          rw [← hexp d hd, update_eq_self]
        rw [e, P.map_update_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [P.map_update_smul, RingHom.id_apply, update_idem]

      have hsplit : ∀ (g : ∀ i, A i) (y : ∀ i, X i), ∏ i, (g i : X i → K) (y i) =
          (g i₀ : X i₀ → K) (y i₀) * ∏ i ∈ univ.erase i₀, (g i : X i → K) (y i) := fun g y =>
        (Finset.mul_prod_erase univ (fun i => (g i : X i → K) (y i)) (mem_univ i₀)).symm
      have hupd : ∀ (g : ∀ i, A i) (v : A i₀) (y : ∀ i, X i),
          ∏ i ∈ univ.erase i₀, (update g i₀ v i : X i → K) (y i) =
            ∏ i ∈ univ.erase i₀, (g i : X i → K) (y i) := fun g v y =>
        Finset.prod_congr rfl fun i hi => by rw [update_of_ne (Finset.ne_of_mem_erase hi)]
      have hupdx : ∀ (g : ∀ i, A i) (y : ∀ i, X i) (t : X i₀),
          ∏ i ∈ univ.erase i₀, (g i : X i → K) (update y i₀ t i) =
            ∏ i ∈ univ.erase i₀, (g i : X i → K) (y i) := fun g y t =>
        Finset.prod_congr rfl fun i hi => by rw [update_of_ne (Finset.ne_of_mem_erase hi)]
      have hli : LinearIndependent K (fun l => ((b l : A i₀) : X i₀ → K)) :=
        b.linearIndependent.map' ((A i₀).subtype ∘ₗ W.subtype)
          (LinearMap.ker_eq_bot_of_injective (Subtype.val_injective.comp Subtype.val_injective))

      have hB : ∀ (x : ∀ i, X i) (l : Fin (Module.finrank K W)),
          ∑ d ∈ s, c d * a d l * ∏ i ∈ univ.erase i₀, (f d i : X i → K) (x i) = 0 := by
        intro x
        refine Fintype.linearIndependent_iff.mp hli _ ?_
        funext t
        have h := hx (update x i₀ t)
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        rw [← h]
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d hd => ?_
        rw [hsplit, hupdx, update_self, hexp d hd]
        simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring
      have hstep : ∑ d ∈ s, c d • P (f d) =
          ∑ l, ∑ d ∈ s, (c d * a d l) • P (update (f d) i₀ (b l)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d hd => ?_
        rw [hP d hd, Finset.smul_sum]
        simp only [mul_smul]
      rw [hstep]
      refine Finset.sum_eq_zero fun l _ => ih s (fun d => c d * a d l)
        (fun d => update (f d) i₀ (b l)) ?_ ?_
      · intro i hi d hd d' hd'
        by_cases h : i = i₀
        · subst h; simp
        · simp only [update_of_ne h]
          exact hconst i (by simp [h, hi]) d hd d' hd'
      · intro x
        have h := hB x l
        calc ∑ d ∈ s, c d * a d l * ∏ i, (update (f d) i₀ (b l) i : X i → K) (x i)
            = ((b l : A i₀) : X i₀ → K) (x i₀) *
                ∑ d ∈ s, c d * a d l * ∏ i ∈ univ.erase i₀, (f d i : X i → K) (x i) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun d _ => ?_
              rw [hsplit, hupd, update_self]
              ring
          _ = 0 := by rw [h, mul_zero]
  intro D s c f hx
  exact vanish univ s c f (fun i hi => absurd (mem_univ i) hi) hx
end

section

open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PicTorsionForm

open CommRing Module

variable {B : Type} [CommRing B]

theorem exists_local_generator (M : Type) [AddCommGroup M] [Module B M] [Module.Invertible B M]
    (p : Ideal B) [p.IsPrime] : ∃ e : M, ∀ x : M, ∃ w a : B, w ∉ p ∧ w • x = a • e := by
  have ⟨f⟩ := Invertible.free_iff_linearEquiv.mp
    (inferInstance : Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M))
  obtain ⟨e, s, he⟩ : ∃ (e : M) (s : p.primeCompl), LocalizedModule.mk e s = f.symm 1 :=
    LocalizedModule.induction_on (β := fun y => ∃ (e : M) (s : p.primeCompl), LocalizedModule.mk e s = y)
      (fun e s => ⟨e, s, rfl⟩) (f.symm 1)
  refine ⟨e, fun x => ?_⟩
  obtain ⟨a, t, ht⟩ : ∃ (a : B) (t : p.primeCompl), Localization.mk a t = f (LocalizedModule.mk x 1) :=
    Localization.induction_on (f (LocalizedModule.mk x 1)) fun z => ⟨z.1, z.2, rfl⟩
  have key : LocalizedModule.mk x (1 : p.primeCompl) = LocalizedModule.mk (a • e) (t * s) := by
    rw [← f.symm_apply_apply (LocalizedModule.mk x 1), ← ht, ← mul_one (Localization.mk a t),
      ← smul_eq_mul, map_smul, ← he, LocalizedModule.mk_smul_mk]
  obtain ⟨u, hu⟩ := (LocalizedModule.mk_eq).mp key
  refine ⟨(u : B) * ((t : B) * s), u * a, ?_, ?_⟩
  · exact p.primeCompl.mul_mem u.2 (p.primeCompl.mul_mem t.2 s.2)
  · simpa only [Submonoid.smul_def, Submonoid.coe_mul, OneMemClass.coe_one, one_smul, smul_smul] using hu

theorem tensorPow_equiv (c : Pic B) (n : ℕ) :
    Nonempty (Pic.AsModule (c ^ n) ≃ₗ[B] ⨂[B] _ : Fin n, Pic.AsModule c) := by
  induction n with
  | zero =>
    have ⟨e⟩ := Pic.ext_iff.mp (pow_zero c)
    have ⟨g⟩ := Pic.mk_eq_one_iff.mp (Pic.mk_eq_self (M := (1 : Pic B)))
    exact ⟨e ≪≫ₗ g ≪≫ₗ (PiTensorProduct.isEmptyEquiv (Fin 0)).symm⟩
  | succ n ih =>
    obtain ⟨ih⟩ := ih
    have ⟨e1⟩ := Pic.ext_iff.mp (pow_succ c n)
    have ⟨e2⟩ := Pic.ext_iff.mp (Pic.mul_eq_tensor (c ^ n) c)
    exact ⟨e1 ≪≫ₗ e2 ≪≫ₗ Pic.mk.linearEquiv B _ ≪≫ₗ TensorProduct.congr ih
      (PiTensorProduct.subsingletonEquiv (R := B) (s := fun _ : Fin 1 => Pic.AsModule c) 0).symm ≪≫ₗ
      PiTensorProduct.tmulEquiv B (Pic.AsModule c) ≪≫ₗ PiTensorProduct.reindex B _ finSumFinEquiv⟩

theorem exists_form : ∀ (B : Type) [CommRing B] (q : ℕ) (c : CommRing.Pic B), c ^ q = 1 →
    ∃ φ : (Π _ : Fin q, CommRing.Pic.AsModule c) →ₘₗ[B] B,
      ∀ p : Ideal B, p.IsPrime → ∃ e : CommRing.Pic.AsModule c, φ (fun _ => e) ∉ p := by
  intro B _ q c hc
  obtain ⟨T⟩ := tensorPow_equiv c q
  have ⟨e1⟩ := Pic.ext_iff.mp hc
  have ⟨g⟩ := Pic.mk_eq_one_iff.mp (Pic.mk_eq_self (M := (1 : Pic B)))
  let ψ : (⨂[B] _ : Fin q, Pic.AsModule c) ≃ₗ[B] B := T.symm ≪≫ₗ e1 ≪≫ₗ g
  refine ⟨ψ.toLinearMap.compMultilinearMap (PiTensorProduct.tprod B), fun p hp => ?_⟩
  obtain ⟨x, hx⟩ : ∃ x : Fin q → Pic.AsModule c, ψ (PiTensorProduct.tprod B x) ∉ p := by
    by_contra! h
    have hall : ∀ t, ψ t ∈ p := fun t => by
      induction t using PiTensorProduct.induction_on with
      | smul_tprod r x => rw [map_smul, smul_eq_mul]; exact p.mul_mem_left r (h x)
      | add a b ha hb => rw [map_add (f := _)]; exact p.add_mem ha hb
    exact hp.ne_top ((Ideal.eq_top_iff_one p).mpr (by simpa using hall (ψ.symm 1)))
  obtain ⟨e, he⟩ := exists_local_generator (Pic.AsModule c) p
  choose w a hw hwa using fun i => he (x i)
  refine ⟨e, fun hmem => ?_⟩
  have hmem' : ψ (PiTensorProduct.tprod B fun _ => e) ∈ p := hmem
  have h1 : ψ (PiTensorProduct.tprod B (fun i => w i • x i)) =
      (∏ i, w i) * ψ (PiTensorProduct.tprod B x) := by
    simp only [MultilinearMap.map_smul_univ, RingHom.id_apply, map_smul, smul_eq_mul]
  have h2 : ψ (PiTensorProduct.tprod B (fun i => w i • x i)) =
      (∏ i, a i) * ψ (PiTensorProduct.tprod B (fun _ => e)) := by
    simp_rw [hwa]
    simp only [MultilinearMap.map_smul_univ, RingHom.id_apply, map_smul, smul_eq_mul]
  have hin : (∏ i, w i) * ψ (PiTensorProduct.tprod B x) ∈ p := by
    rw [← h1, h2]; exact p.mul_mem_left _ hmem'
  rcases hp.mem_or_mem hin with h | h
  · exact (p.primeCompl.prod_mem fun i _ => hw i) h
  · exact hx h

end GlobalTheory.PicTorsionForm
end
end

section

noncomputable section

namespace GlobalTheory.HTRho

variable {k H O C : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O] [CommRing C] [Algebra C O]

def mSub (σ : O →+* Module.End k H) (χ : C →+* k) (X : Submodule k H) : Submodule k H :=
  Submodule.span k {z | ∃ c : C, ∃ x ∈ X, z = σ (algebraMap C O c) x - χ c • x}

def jSub {ι : Type*} (σ : O →+* Module.End k H) (χ : ι → C →+* k) (X : Submodule k H) : Submodule k H :=
  Submodule.span k {z | ∃ (r : ℕ) (lam : Fin r → k) (c : Fin r → C) (x : H), x ∈ X ∧
    (∀ i, ∑ l, lam l * χ i (c l) = 0) ∧ z = ∑ l, lam l • σ (algebraMap C O (c l)) x}

def homO {X Y : Type*} [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    (σX : O →+* Module.End k X) (σY : O →+* Module.End k Y) : Submodule k (X →ₗ[k] Y) where
  carrier := {T | ∀ a, T ∘ₗ σX a = σY a ∘ₗ T}
  zero_mem' a := by simp
  add_mem' {S T} hS hT a := by rw [LinearMap.add_comp, LinearMap.comp_add, hS a, hT a]
  smul_mem' c T hT a := by rw [LinearMap.smul_comp, LinearMap.comp_smul, hT a]

theorem mem_homO {X Y : Type*} [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    (σX : O →+* Module.End k X) (σY : O →+* Module.End k Y) (T : X →ₗ[k] Y) :
    T ∈ homO σX σY ↔ ∀ a x, T (σX a x) = σY a (T x) := by
  simp only [homO, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq,
    LinearMap.ext_iff, LinearMap.comp_apply]

def rAct (σ : O →+* Module.End k H) (X : Submodule k H) (h : ∀ a, ∀ x ∈ X, σ a x ∈ X) :
    O →+* Module.End k X where
  toFun a := (σ a).restrict (h a)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

def qAct (σ : O →+* Module.End k H) (X : Submodule k H) (h : ∀ a, ∀ x ∈ X, σ a x ∈ X) :
    O →+* Module.End k (H ⧸ X) where
  toFun a := X.mapQ X (σ a) (fun x hx => h a x hx)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

@[simp] theorem qAct_mk (σ : O →+* Module.End k H) (X : Submodule k H) (h : ∀ a, ∀ x ∈ X, σ a x ∈ X)
    (a : O) (x : H) : qAct σ X h a (X.mkQ x) = X.mkQ (σ a x) := rfl

theorem mSub_stable (σ : O →+* Module.End k H) (χ : C →+* k) (X : Submodule k H)
    (hX : ∀ a, ∀ x ∈ X, σ a x ∈ X) : ∀ a, ∀ x ∈ mSub σ χ X, σ a x ∈ mSub σ χ X := by
  intro a x hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, y, hy, rfl⟩ := hz
    refine Submodule.subset_span ⟨c, σ a y, hX a y hy, ?_⟩
    rw [map_sub, map_smul, ← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul,
      Algebra.commutes]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem jSub_stable {ι : Type*} (σ : O →+* Module.End k H) (χ : ι → C →+* k) (X : Submodule k H)
    (hX : ∀ a, ∀ x ∈ X, σ a x ∈ X) : ∀ a, ∀ x ∈ jSub σ χ X, σ a x ∈ jSub σ χ X := by
  intro a x hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, lam, c, y, hy, hc, rfl⟩ := hz
    refine Submodule.subset_span ⟨r, lam, c, σ a y, hX a y hy, hc, ?_⟩

    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, ← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul, Algebra.commutes]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem qAct_mSub_algebraMap (σ : O →+* Module.End k H) (χ : C →+* k) (c : C) :
    qAct σ (mSub σ χ ⊤) (mSub_stable σ χ ⊤ (fun _ _ _ => trivial)) (algebraMap C O c) = χ c • 1 := by
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearMap.smul_apply,
    Module.End.one_apply]
  change (mSub σ χ ⊤).mkQ (σ (algebraMap C O c) x) = χ c • (mSub σ χ ⊤).mkQ x
  rw [← map_smul, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span ⟨c, x, trivial, rfl⟩

end GlobalTheory.HTRho
end
end
