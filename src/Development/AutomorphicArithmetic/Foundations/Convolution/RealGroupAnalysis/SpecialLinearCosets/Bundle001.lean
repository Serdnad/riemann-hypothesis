module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle001
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

section SlopeTestRemainingChoices

open GroundTheory.LocalField

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

private def boxSet (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℤ) : Set (Matrix (Fin 2) (Fin 2) K) :=
  {m | ∀ i j, m i j ∈ valBall K n}

private theorem isOpen_boxSet (n : ℤ) : IsOpen (boxSet K n) := by
  have : boxSet K n = ⋂ i, ⋂ j, (fun X : Matrix (Fin 2) (Fin 2) K => X i j) ⁻¹'
      (valBall K n : Set K) := by
    ext X; simp [boxSet]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isOpen_valBall _).preimage ((continuous_apply j).comp (continuous_apply i))

private theorem isCompact_boxSet (n : ℤ) : IsCompact (boxSet K n) := by
  have : boxSet K n = Set.univ.pi fun _ : Fin 2 => Set.univ.pi fun _ : Fin 2 =>
      (valBall K n : Set K) := by
    ext X
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_valBall n

private def boxGrp (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℤ) : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) K)) where
  carrier := Multiplicative.toAdd ⁻¹' boxSet K n
  one_mem' := fun _ _ => zero_mem _
  mul_mem' := fun ha hb i j => add_mem (ha i j) (hb i j)
  inv_mem' := fun ha i j => neg_mem (ha i j)

private theorem lgrp_matrix : Lgrp (Multiplicative (Matrix (Fin 2) (Fin 2) K)) := by
  intro N hN
  have hS : Multiplicative.ofAdd ⁻¹' N ∈ 𝓝 (0 : Matrix (Fin 2) (Fin 2) K) :=
    (continuous_ofAdd.tendsto (0 : Matrix (Fin 2) (Fin 2) K)) hN
  obtain ⟨r, hr⟩ := GroundTheory.Automorphic.GodementJacquet.exists_valBall_subset hS
  refine ⟨boxGrp K r, (isOpen_boxSet (r : ℤ)).preimage continuous_toAdd, ?_, ?_⟩
  · have := (isCompact_boxSet (K := K) (r : ℤ)).image continuous_ofAdd
    convert this using 1
    ext x
    constructor
    · intro hx
      exact ⟨Multiplicative.toAdd x, hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  · intro x hx
    exact hr hx

private def cgrp (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) where
  carrier := {g | g.1 - 1 ∈ boxSet K ((n : ℤ) + 1)}
  one_mem' := by
    intro i j
    simp
  mul_mem' := by
    intro a b ha hb i j
    have e : (a * b).1 - 1 = (a.1 - 1) * (b.1 - 1) + (a.1 - 1) + (b.1 - 1) := by
      rw [Matrix.SpecialLinearGroup.coe_mul]; noncomm_ring
    rw [e]
    refine add_mem (add_mem ?_ (ha i j)) (hb i j)
    rw [Matrix.mul_apply]
    refine sum_mem fun l _ => ?_
    exact valBall_antitone (by omega) (mul_mem_valBall (ha i l) (hb l j))
  inv_mem' := by
    intro g hg i j
    have e : (g⁻¹).1 = !![g.1 1 1, -g.1 0 1; -g.1 1 0, g.1 0 0] := by
      rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    have h00 := hg 0 0
    have h01 := hg 0 1
    have h10 := hg 1 0
    have h11 := hg 1 1
    simp only [Matrix.sub_apply, Matrix.one_apply_eq] at h00 h11
    simp only [Matrix.sub_apply, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero] at h01 h10
    rw [e]
    fin_cases i <;> fin_cases j <;> simp
    · exact h11
    · exact h01
    · exact h10
    · exact h00

private theorem isOpen_cgrp (n : ℕ) :
    IsOpen (cgrp K n : Set (Matrix.SpecialLinearGroup (Fin 2) K)) := by
  have hc : Continuous fun g : Matrix.SpecialLinearGroup (Fin 2) K => g.1 - 1 :=
    continuous_subtype_val.sub continuous_const
  exact (isOpen_boxSet _).preimage hc

private theorem isCompact_cgrp [T2Space K] (n : ℕ) :
    IsCompact (cgrp K n : Set (Matrix.SpecialLinearGroup (Fin 2) K)) := by
  refine (Subtype.isCompact_iff (p := fun A : Matrix (Fin 2) (Fin 2) K => A.det = 1)).2 ?_
  have hC : IsCompact ((fun m : Matrix (Fin 2) (Fin 2) K => m + 1) '' boxSet K ((n : ℤ) + 1)) :=
    (isCompact_boxSet _).image (continuous_id.add continuous_const)
  have hD : IsClosed {m : Matrix (Fin 2) (Fin 2) K | m.det = 1} :=
    isClosed_eq (Continuous.matrix_det continuous_id) continuous_const
  convert hC.inter_right hD using 1
  ext m
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g.1 - 1, hg, by simp⟩, g.2⟩
  · rintro ⟨⟨y, hy, rfl⟩, hd⟩
    refine ⟨⟨y + 1, hd⟩, ?_, rfl⟩
    change (y + 1) - 1 ∈ boxSet K ((n : ℤ) + 1)
    simpa using hy

private theorem lgrp_sl [T2Space K] : Lgrp (Matrix.SpecialLinearGroup (Fin 2) K) := by
  intro N hN
  obtain ⟨W, hW', hWN⟩ := (mem_nhds_subtype {A : Matrix (Fin 2) (Fin 2) K | A.det = 1} (1 : Matrix.SpecialLinearGroup (Fin 2) K) N).1 hN
  have hW : W ∈ 𝓝 (1 : Matrix (Fin 2) (Fin 2) K) := hW'
  have hS : (fun m : Matrix (Fin 2) (Fin 2) K => m + 1) ⁻¹' W ∈ 𝓝 (0 : Matrix (Fin 2) (Fin 2) K) := by
    have hc : Continuous fun m : Matrix (Fin 2) (Fin 2) K => m + 1 :=
      continuous_id.add continuous_const
    have := hc.tendsto (0 : Matrix (Fin 2) (Fin 2) K)
    rw [zero_add] at this
    exact this hW
  obtain ⟨r, hr⟩ := GroundTheory.Automorphic.GodementJacquet.exists_valBall_subset hS
  refine ⟨cgrp K r, isOpen_cgrp r, isCompact_cgrp r, fun g hg => hWN ?_⟩
  have h1 : g.1 - 1 ∈ (fun m : Matrix (Fin 2) (Fin 2) K => m + 1) ⁻¹' W :=
    hr fun i j => valBall_antitone (m := (r : ℤ)) (n := (r : ℤ) + 1) (by omega) (hg i j)
  have h2 : (g.1 - 1) + 1 ∈ W := h1
  rw [sub_add_cancel] at h2
  exact h2

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.I.lgrp :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F), Lgrp (SL v) ∧ Lgrp (Multiplicative (M2 v)) := by
  intro F _ _ v
  exact ⟨lgrp_sl, lgrp_matrix⟩
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.I.cosetSpan :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G], Lgrp G → ∀ a ∈ SB G, ∀ N ∈ 𝓝 (1 : G),
      ∃ (U : Subgroup G) (s : Finset G) (c : G → ℂ), IsOpen (U : Set G) ∧ IsCompact (U : Set G) ∧ (U : Set G) ⊆ N ∧
        ∀ x, a x = ∑ g ∈ s, c g * ind U (g⁻¹ * x) := by
  intro G _ _ _ _ hL a ha N hN
  have hlc : IsLocallyConstant a := (GroundTheory.LocalField.mem_schwartzBruhat.1 ha).1
  have hcs : HasCompactSupport a := (GroundTheory.LocalField.mem_schwartzBruhat.1 ha).2
  have hK : IsCompact (tsupport a) := hcs
  have hS : IsOpen {p : G × G | a (p.1 * p.2) = a p.1} := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    have hev := (IsLocallyConstant.iff_eventually_eq a).1 hlc
    have e1 : ∀ᶠ q : G × G in 𝓝 p, a (q.1 * q.2) = a (p.1 * p.2) :=
      ((continuous_fst.mul continuous_snd).tendsto p).eventually (hev (p.1 * p.2))
    have e2 : ∀ᶠ q : G × G in 𝓝 p, a q.1 = a p.1 :=
      (continuous_fst.tendsto p).eventually (hev p.1)
    filter_upwards [e1, e2] with q h1 h2
    show a (q.1 * q.2) = a q.1
    rw [h1, h2]
    exact hp
  obtain ⟨W1, W0, -, hW0, hKW, h1W, hWS⟩ :=
    generalized_tube_lemma hK (isCompact_singleton (x := (1 : G))) hS (by
      rintro ⟨x, u⟩ ⟨-, hu⟩
      have hu' : u = 1 := hu
      subst hu'
      show a (x * 1) = a x
      rw [mul_one])
  have hN' : N ∩ W0 ∈ 𝓝 (1 : G) := Filter.inter_mem hN (hW0.mem_nhds (h1W rfl))
  obtain ⟨U, hUo, hUc, hUN⟩ := hL _ hN'
  have hinv0 : ∀ x ∈ tsupport a, ∀ u ∈ U, a (x * u) = a x := fun x hx u hu =>
    hWS (Set.mk_mem_prod (hKW hx) (hUN hu).2)
  have hinv : ∀ x, ∀ u ∈ U, a (x * u) = a x := by
    intro x u hu
    by_cases hx : x ∈ tsupport a
    · exact hinv0 x hx u hu
    by_cases hxu : x * u ∈ tsupport a
    · have h := hinv0 _ hxu u⁻¹ (U.inv_mem hu)
      rw [mul_inv_cancel_right] at h
      exact h.symm
    · rw [image_eq_zero_of_notMem_tsupport hxu, image_eq_zero_of_notMem_tsupport hx]
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun x => {y : G | x⁻¹ * y ∈ U}) (by
    intro x _
    have ho : IsOpen {y : G | x⁻¹ * y ∈ U} :=
      hUo.preimage (continuous_const.mul continuous_id)
    refine ho.mem_nhds ?_
    show x⁻¹ * x ∈ U
    rw [inv_mul_cancel]
    exact U.one_mem)
  let r : G → G := fun x => Quotient.out (QuotientGroup.mk x : G ⧸ U)
  have hr : ∀ x, (r x)⁻¹ * x ∈ U := fun x => QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
  have h1 : ∀ y ∈ U, ind U y = 1 := fun y hy => by simp [ind, hy]
  have h0 : ∀ y, y ∉ U → ind U y = 0 := fun y hy => by simp [ind, hy]
  refine ⟨U, t.image r, a, hUo, hUc, fun x hx => (hUN hx).1, ?_⟩
  intro x
  have huniq : ∀ g ∈ t.image r, ∀ g' ∈ t.image r, g⁻¹ * x ∈ U → g'⁻¹ * x ∈ U → g' = g := by
    intro g hg g' hg' hgx hgx'
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hg
    obtain ⟨y', -, rfl⟩ := Finset.mem_image.1 hg'
    have e : (QuotientGroup.mk y : G ⧸ U) = QuotientGroup.mk y' := by
      have a1 : (QuotientGroup.mk (r y) : G ⧸ U) = QuotientGroup.mk x := QuotientGroup.eq.2 hgx
      have a2 : (QuotientGroup.mk (r y') : G ⧸ U) = QuotientGroup.mk x := QuotientGroup.eq.2 hgx'
      have b1 : (QuotientGroup.mk (r y) : G ⧸ U) = QuotientGroup.mk y := QuotientGroup.out_eq' _
      have b2 : (QuotientGroup.mk (r y') : G ⧸ U) = QuotientGroup.mk y' := QuotientGroup.out_eq' _
      rw [← b1, ← b2, a1, a2]
    show Quotient.out (QuotientGroup.mk y' : G ⧸ U) = Quotient.out (QuotientGroup.mk y : G ⧸ U)
    rw [e]
  by_cases h : ∃ g ∈ t.image r, g⁻¹ * x ∈ U
  · obtain ⟨g, hg, hgx⟩ := h
    rw [Finset.sum_eq_single g, h1 _ hgx, mul_one]
    · have e := hinv g _ hgx
      rw [mul_inv_cancel_left] at e
      exact e
    · intro b hb hne
      rw [h0, mul_zero]
      intro hbx
      exact hne (huniq g hg b hb hgx hbx)
    · intro hn
      exact absurd hg hn
  · have hx0 : a x = 0 := by
      by_contra hne
      have hxs : x ∈ tsupport a := subset_tsupport _ hne
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hxs)
      refine h ⟨r y, Finset.mem_image_of_mem r hy, ?_⟩
      have e : (r y)⁻¹ * x = ((r y)⁻¹ * y) * (y⁻¹ * x) := by group
      rw [e]
      exact U.mul_mem (hr y) hxy
    rw [hx0]
    symm
    apply Finset.sum_eq_zero
    intro g hg
    rw [h0 _ (fun hgx => h ⟨g, hg, hgx⟩), mul_zero]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.I.cosetSum :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (U U' : Subgroup G), U' ≤ U → IsCompact (U : Set G) → IsOpen (U' : Set G) →
      ∃ s : Finset G, s.Nonempty ∧ (∀ g ∈ s, g ∈ U) ∧ ∀ x, ind U x = ∑ g ∈ s, ind U' (x * g⁻¹) := by
  intro G _ _ _ _ U U' hle hU hU'
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  have hopen : IsOpen ((U'.subgroupOf U : Subgroup U) : Set U) := hU'.preimage continuous_subtype_val
  haveI : Finite (U ⧸ U'.subgroupOf U) := Subgroup.quotient_finite_of_isOpen _ hopen
  haveI : Finite (Quotient (QuotientGroup.rightRel (U'.subgroupOf U))) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel (U'.subgroupOf U)).symm
  letI : Fintype (Quotient (QuotientGroup.rightRel (U'.subgroupOf U))) := Fintype.ofFinite _
  let mk : U → Quotient (QuotientGroup.rightRel (U'.subgroupOf U)) := fun u => Quotient.mk _ u
  let r : Quotient (QuotientGroup.rightRel (U'.subgroupOf U)) → G := fun q => ((Quotient.out q : U) : G)
  have hrU : ∀ q, r q ∈ U := fun q => (Quotient.out q : U).2
  have hinj : Function.Injective r := by
    intro a b h
    have : (Quotient.out a : U) = Quotient.out b := Subtype.ext h
    rw [← Quotient.out_eq a, ← Quotient.out_eq b, this]
  have key : ∀ (u : U) q, (u : G) * (r q)⁻¹ ∈ U' ↔ q = mk u := by
    intro u q
    have h1 : mk (Quotient.out q) = q := Quotient.out_eq q
    constructor
    · intro h
      rw [← h1]
      refine Quotient.sound ?_
      change QuotientGroup.rightRel _ _ _
      rw [QuotientGroup.rightRel_apply]
      change ((u * (Quotient.out q)⁻¹ : U) : G) ∈ U'
      simpa [r] using h
    · intro h
      have h2 : mk (Quotient.out q) = mk u := h1.trans h
      have h3 := Quotient.exact h2
      change QuotientGroup.rightRel _ _ _ at h3
      rw [QuotientGroup.rightRel_apply] at h3
      have h4 : ((u * (Quotient.out q)⁻¹ : U) : G) ∈ U' := h3
      simpa [r] using h4
  refine ⟨Finset.univ.image r, ⟨r (mk 1), Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩, ?_, ?_⟩
  · intro g hg
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hg
    exact hrU q
  · intro x
    rw [Finset.sum_image (fun a _ b _ h => hinj h)]
    by_cases hx : x ∈ U
    · have h1 : ind U x = 1 := by simp [ind, Set.indicator, hx]
      rw [h1, Finset.sum_eq_single (mk ⟨x, hx⟩)]
      · have : x * (r (mk ⟨x, hx⟩))⁻¹ ∈ U' := (key ⟨x, hx⟩ _).mpr rfl
        simp [ind, Set.indicator, this]
      · intro q _ hq
        have : x * (r q)⁻¹ ∉ U' := fun h => hq ((key ⟨x, hx⟩ q).mp h)
        simp [ind, Set.indicator, this]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · have h1 : ind U x = 0 := by simp [ind, Set.indicator, hx]
      rw [h1]
      symm
      refine Finset.sum_eq_zero fun q _ => ?_
      have : x * (r q)⁻¹ ∉ U' := fun h => hx (by
        have := U.mul_mem (hle h) (hrU q)
        simpa using this)
      simp [ind, Set.indicator, this]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.I

section

variable {F : Type} [Field F] [NumberField F] (v : P F)

private theorem cp_cont : Continuous (cp v) := by
  have h1 : Continuous (pLoc F v) :=
    RestrictedProduct.continuous_eval (R := fun v : P F => v.adicCompletion F) v
  have h2 : Continuous (pFin F) := continuous_snd
  exact h1.comp h2

private theorem cp_rt (c : F) : cp v (rt c) = algebraMap F (Kv v) c := rfl

private theorem cp_sg (x : Kv v) : cp v (sg v x) = x := (UpperTheory.ConvolutionTheory.R2.H.sgLaws F v).2.2.1 x

private theorem sg_cp (a : A F) : sg v (cp v a) = a * sg v 1 := by
  rw [(UpperTheory.ConvolutionTheory.R2.H.sgLaws F v).2.1 a 1, mul_one]

private theorem e_idem : sg v 1 * sg v 1 = sg v 1 := by
  rw [← sg_cp v (sg v 1), cp_sg]

private theorem away_eq (X : V4 F) (i : Fin 4) : away v X i = (1 - sg v 1) * X i := by
  change X i - sg v (cp v (X i)) = _
  rw [sg_cp]; ring

private theorem cp_away (X : V4 F) (i : Fin 4) : cp v (away v X i) = 0 := by
  change cp v (X i - sg v (cp v (X i))) = 0
  rw [map_sub, cp_sg, sub_self]

private theorem sg_add' (x y : Kv v) : sg v (x + y) = sg v x + sg v y :=
  (UpperTheory.ConvolutionTheory.R2.H.sgLaws F v).1 x y

private theorem two_ne : (2 : Kv v) ≠ 0 := by
  intro h
  have h' : algebraMap F (Kv v) 2 = algebraMap F (Kv v) 0 := by
    rw [map_ofNat, map_zero]; exact h
  exact two_ne_zero ((algebraMap F (Kv v)).injective h')

end

end UpperTheory.ConvolutionTheory.R2.I

theorem UpperTheory.ConvolutionTheory.R2.I.matLaws :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F) (δ : F) (θ : Kv v), θ ^ 2 = algebraMap F (Kv v) δ → θ ≠ 0 →
      (∀ m : M2 v, ∃ y : V4 F, ∀ X, mat v θ (X + y) = mat v θ X + m ∧ away v (X + y) = away v X) ∧
      (∀ X Y, B4 δ Y X = B4 δ (away v Y) (away v X) + sg v (BM (mat v θ Y) (mat v θ X))) ∧
      (∀ b X, sg v b * q4 δ X = sg v (-(b * (mat v θ X).det))) ∧
      Continuous (mat v θ) ∧ Continuous (away v) ∧ (∀ X, away v (away v X) = away v X) ∧
      ∀ X, mat v θ (away v X) = 0 := by
  intro F _ _ v δ θ hθ hθ0
  have h2 := two_ne v
  have hc := cp_cont v
  have hs : Continuous (sg v) := (UpperTheory.ConvolutionTheory.R2.H.sgLaws F v).2.2.2.2.2.2.2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    refine ⟨![sg v (m 1 1), sg v (m 0 0), sg v ((m 0 1 + m 1 0) / 2), sg v ((m 0 1 - m 1 0) / (2 * θ))],
      fun X => ⟨?_, ?_⟩⟩
    · have e1 : (m 0 1 + m 1 0) / 2 + (m 0 1 - m 1 0) / (2 * θ) * θ = m 0 1 := by
        field_simp
        ring
      have e2 : (m 0 1 + m 1 0) / 2 - (m 0 1 - m 1 0) / (2 * θ) * θ = m 1 0 := by
        field_simp
        ring
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j
      · change cp v (X 1 + sg v (m 0 0)) = cp v (X 1) + m 0 0
        rw [map_add (f := _), cp_sg]
      · change cp v (X 2 + sg v ((m 0 1 + m 1 0) / 2)) +
            cp v (X 3 + sg v ((m 0 1 - m 1 0) / (2 * θ))) * θ = cp v (X 2) + cp v (X 3) * θ + m 0 1
        rw [map_add (f := _), map_add (f := _), cp_sg, cp_sg]
        linear_combination e1
      · change cp v (X 2 + sg v ((m 0 1 + m 1 0) / 2)) -
            cp v (X 3 + sg v ((m 0 1 - m 1 0) / (2 * θ))) * θ = cp v (X 2) - cp v (X 3) * θ + m 1 0
        rw [map_add (f := _), map_add (f := _), cp_sg, cp_sg]
        linear_combination e2
      · change cp v (X 0 + sg v (m 1 1)) = cp v (X 0) + m 1 1
        rw [map_add (f := _), cp_sg]
    · funext i
      change (X i + _) - sg v (cp v (X i + _)) = X i - sg v (cp v (X i))
      rw [map_add (f := _), sg_add']
      fin_cases i <;> simp [cp_sg] <;> ring
  · intro X Y
    have hB : BM (mat v θ Y) (mat v θ X) = cp v (B4 δ Y X) := by
      simp only [BM, mat, B4, map_sub, map_add (f := _), map_mul, cp_rt, ← hθ, map_ofNat]
      simp
      ring
    rw [hB, sg_cp]
    have he := e_idem v
    simp only [B4, away_eq]
    generalize sg v 1 = e at he
    generalize rt δ = d
    linear_combination (-(2 * (Y 2 * X 2 - d * (Y 3 * X 3)) - Y 1 * X 0 - Y 0 * X 1)) * he
  · intro b X
    have hq : -(b * (mat v θ X).det) = cp v (q4 δ X) * b := by
      simp only [mat, q4, Matrix.det_fin_two_of, map_sub, map_mul, map_pow, cp_rt, ← hθ]
      ring
    rw [hq, mul_comm, (UpperTheory.ConvolutionTheory.R2.H.sgLaws F v).2.1]
  · refine continuous_matrix fun i j => ?_
    have h : ∀ k : Fin 4, Continuous fun X : V4 F => cp v (X k) := fun k => hc.comp (continuous_apply k)
    fin_cases i <;> fin_cases j <;> simp [mat]
    · exact h 1
    · exact (h 2).add ((h 3).mul continuous_const)
    · exact (h 2).sub ((h 3).mul continuous_const)
    · exact h 0
  · refine continuous_pi fun i => ?_
    exact (continuous_apply i).sub (hs.comp (hc.comp (continuous_apply i)))
  · intro X
    funext i
    change away v X i - sg v (cp v (away v X i)) = _
    rw [cp_away]
    have : sg v 0 = 0 := by
      have := sg_add' v 0 0
      simpa using this
    rw [this, sub_zero]
  · intro X
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mat, cp_away]
end
