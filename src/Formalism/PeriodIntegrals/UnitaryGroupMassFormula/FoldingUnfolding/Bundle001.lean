module

public import Formalism.PeriodIntegrals.Bundle016
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FoldingUnfolding.TransExists
public import Formalism.PeriodIntegrals.Bundle012
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

@[expose] public section

section

open MeasureTheory
open scoped ENNReal NNReal
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable

namespace PI.FoldDCUnfold.W

universe u

theorem pointwise_of (h1 : TransIndep.{u}) (h3 : DCTrans.{u})
    {G : Type u} [Group G] (Γ S S' : Subgroup G) (hS : S ≤ Γ) (hS' : S' ≤ Γ)
    (D D' : Set G) (hD : IsRightTransversal Γ S D) (hD' : IsRightTransversal Γ S' D')
    (R : Set G) (hR : IsDoubleTransversal Γ S S' R)
    (E : G → Set G) (hE : ∀ r ∈ R, IsRightTransversal S (stab S S' r) (E r))
    (g h : G → ℝ≥0∞) (hg : ∀ s ∈ S, ∀ y : G, g (s * y) = g y)
    (hh : ∀ s ∈ S', ∀ y : G, h (s * y) = h y) (x : G) :
    (∑' δ : D, g ((δ : G) * x)) * (∑' δ' : D', h ((δ' : G) * x)) =
      ∑' r : R, ∑' p : (E (r : G) × D),
        g ((p.1 : G) * (p.2 : G) * x) * h ((r : G)⁻¹ * ((p.1 : G) * (p.2 : G) * x)) := by
  obtain ⟨hinj, hT⟩ := h3 G Γ S S' hS hS' R hR E hE
  have key : ∀ δ : D, ∑' δ' : D', h ((δ' : G) * x) =
      ∑' r : R, ∑' t : E (r : G), h ((r : G)⁻¹ * ((t : G) * (δ : G) * x)) := by
    intro δ
    have hδ : (δ : G) ∈ Γ := hD.1 δ.2
    have h1' : ∑' η : Set.range (fun q : (Σ r : R, E (r : G)) => (q.1 : G)⁻¹ * (q.2 : G)),
        h ((η : G) * (δ : G) * x) = ∑' η : D', h ((η : G) * x) :=
      h1 G Γ S' _ D' hT hD' (δ : G) hδ (fun y => h (y * x))
        (fun s hs y => by rw [mul_assoc]; exact hh s hs (y * x))
    have h2' : ∑' η : Set.range (fun q : (Σ r : R, E (r : G)) => (q.1 : G)⁻¹ * (q.2 : G)),
        h ((η : G) * (δ : G) * x) =
        ∑' q : (Σ r : R, E (r : G)), h ((q.1 : G)⁻¹ * (q.2 : G) * (δ : G) * x) :=
      tsum_range (fun η : G => h (η * (δ : G) * x)) hinj
    rw [← h1', h2', ENNReal.tsum_sigma']
    refine tsum_congr fun r => tsum_congr fun t => ?_
    simp only [mul_assoc]
  have hg' : ∀ r : R, ∀ t : E (r : G), ∀ δ : D,
      g ((t : G) * (δ : G) * x) = g ((δ : G) * x) := by
    intro r t δ
    have ht : (t : G) ∈ S := (hE r r.2).1 t.2
    rw [mul_assoc]
    exact hg _ ht _
  calc (∑' δ : D, g ((δ : G) * x)) * (∑' δ' : D', h ((δ' : G) * x))
      = ∑' δ : D, g ((δ : G) * x) * ∑' δ' : D', h ((δ' : G) * x) := ENNReal.tsum_mul_right.symm
    _ = ∑' δ : D, ∑' r : R, ∑' t : E (r : G),
          g ((t : G) * (δ : G) * x) * h ((r : G)⁻¹ * ((t : G) * (δ : G) * x)) := by
        refine tsum_congr fun δ => ?_
        rw [key δ, ← ENNReal.tsum_mul_left]
        refine tsum_congr fun r => ?_
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun t => ?_
        rw [hg' r t δ]
    _ = ∑' r : R, ∑' t : E (r : G), ∑' δ : D,
          g ((t : G) * (δ : G) * x) * h ((r : G)⁻¹ * ((t : G) * (δ : G) * x)) := by
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun r => ?_
        rw [ENNReal.tsum_comm]
    _ = _ := by
        refine tsum_congr fun r => ?_
        exact (ENNReal.tsum_prod (f := fun (t : E (r : G)) (δ : D) =>
          g ((t : G) * (δ : G) * x) * h ((r : G)⁻¹ * ((t : G) * (δ : G) * x)))).symm

theorem foldDCUnfold_of (h0 : TransExists.{u}) (h1 : TransIndep.{u}) (h2 : TransProd.{u})
    (h3 : DCTrans.{u}) (hU : PI.FoldUnfold.FoldUnfold.{u}) : PI.FoldDCUnfold.FoldDCUnfold.{u} := by
  intro G _ _ _ μ _ Γ S S' _ hS hS' D D' hD hD' R hR Fs hFs FΓ hFΓ g h hgm hhm hg hh
  have hΓc : (Γ : Set G).Countable := Set.countable_coe_iff.mp (inferInstanceAs (Countable Γ))
  have hstabS : ∀ r : G, stab S S' r ≤ S := fun r => inf_le_left
  choose E hE using fun r : G => h0 G S (stab S S' r) (hstabS r)
  have hTP := fun r : G => h2 G Γ S (stab S S' r) (E r) D (hstabS r) hS (hE r) hD
  have hpt : ∀ x : G, (∑' δ : D, g ((δ : G) * x)) * (∑' δ' : D', h ((δ' : G) * x)) =
      ∑' r : R, ∑' η : Set.range (fun p : E (r : G) × D => (p.1 : G) * (p.2 : G)),
        g ((η : G) * x) * h ((r : G)⁻¹ * ((η : G) * x)) := by
    intro x
    rw [pointwise_of h1 h3 Γ S S' hS hS' D D' hD hD' R hR E (fun r _ => hE r) g h hg hh x]
    refine tsum_congr fun r => ?_
    have h2' : ∑' η : Set.range (fun p : E (r : G) × D => (p.1 : G) * (p.2 : G)),
        g ((η : G) * x) * h ((r : G)⁻¹ * ((η : G) * x)) =
        ∑' p : E (r : G) × D,
          g ((p.1 : G) * (p.2 : G) * x) * h ((r : G)⁻¹ * ((p.1 : G) * (p.2 : G) * x)) :=
      tsum_range (fun η : G => g (η * x) * h ((r : G)⁻¹ * (η * x))) (hTP (r : G)).1
    rw [h2']
  have hFm : ∀ r : G, Measurable (fun y : G => g y * h (r⁻¹ * y)) := fun r =>
    hgm.mul (hhm.comp (measurable_const_mul r⁻¹))
  have hinv : ∀ r : G, ∀ s ∈ stab S S' r, ∀ y : G,
      g (s * y) * h (r⁻¹ * (s * y)) = g y * h (r⁻¹ * y) := by
    intro r s hs y
    have hs2 := Subgroup.mem_inf.mp
      (show s ∈ S ⊓ S'.comap (MulAut.conj r⁻¹).toMonoidHom from hs)
    have hs' : r⁻¹ * s * r ∈ S' := by
      simpa [MulAut.conj_apply] using Subgroup.mem_comap.mp hs2.2
    rw [hg s hs2.1 y]
    congr 1
    calc h (r⁻¹ * (s * y)) = h ((r⁻¹ * s * r) * (r⁻¹ * y)) := by congr 1; group
      _ = h (r⁻¹ * y) := hh _ hs' _
  haveI : Countable R := (hΓc.mono hR.1).to_subtype
  simp_rw [hpt]
  rw [lintegral_tsum (fun r => ?_)]
  · refine tsum_congr fun r => ?_
    exact hU G μ Γ (stab S S' r) ((hstabS r).trans hS) (Fs r) (hFs r r.2) FΓ hFΓ _
      (hTP (r : G)).2 (fun y : G => g y * h ((r : G)⁻¹ * y)) (hFm r) (hinv r)
  · haveI : Countable (Set.range (fun p : E (r : G) × D => (p.1 : G) * (p.2 : G))) :=
      (hΓc.mono (hTP (r : G)).2.1).to_subtype
    exact (Measurable.tsum fun η : Set.range (fun p : E (r : G) × D => (p.1 : G) * (p.2 : G)) =>
      (hFm (r : G)).comp (measurable_const_mul (η : G))).aemeasurable

end PI.FoldDCUnfold.W
end

section

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable

namespace PI.FoldDCUnfold.W

universe u

theorem dc_core {G : Type u} [Group G] (Γ S S' : Subgroup G) (hS : S ≤ Γ) (hS' : S' ≤ Γ)
    (R : Set G) (hR : IsDoubleTransversal Γ S S' R)
    (E : G → Set G) (hE : ∀ r ∈ R, IsRightTransversal S (stab S S' r) (E r))
    (p q : Σ r : R, E (r : G)) (s1 s2 : G) (hs1 : s1 ∈ S') (hs2 : s2 ∈ S')
    (heq : s1 * ((p.1 : G)⁻¹ * (p.2 : G)) = s2 * ((q.1 : G)⁻¹ * (q.2 : G))) :
    p = q ∧ s1 = s2 := by
  obtain ⟨⟨r, hr⟩, e, he⟩ := p
  obtain ⟨⟨r', hr'⟩, e', he'⟩ := q
  change s1 * (r⁻¹ * e) = s2 * (r'⁻¹ * e') at heq
  have heS : e ∈ S := (hE r hr).1 he
  have heS' : e' ∈ S := (hE r' hr').1 he'
  have hrr : (⟨r, hr⟩ : R) = ⟨r', hr'⟩ := by
    refine (hR.2 r (hR.1 hr)).unique ⟨1, S.one_mem, 1, S'.one_mem, by simp⟩
      ⟨e * e'⁻¹, S.mul_mem heS (S.inv_mem heS'), s2⁻¹ * s1, S'.mul_mem (S'.inv_mem hs2) hs1, ?_⟩
    calc e * e'⁻¹ * r' * (s2⁻¹ * s1) = e * (s2 * (r'⁻¹ * e'))⁻¹ * s1 := by group
      _ = e * (s1 * (r⁻¹ * e))⁻¹ * s1 := by rw [heq]
      _ = r := by group
  have hrr' : r = r' := congrArg Subtype.val hrr
  subst hrr'
  have hstab : e * e'⁻¹ ∈ stab S S' r := by
    refine Subgroup.mem_inf.mpr ⟨S.mul_mem heS (S.inv_mem heS'), ?_⟩
    rw [Subgroup.mem_comap]
    have h : r⁻¹ * (e * e'⁻¹) * r = s1⁻¹ * s2 := by
      calc r⁻¹ * (e * e'⁻¹) * r = s1⁻¹ * (s1 * (r⁻¹ * e)) * e'⁻¹ * r := by group
        _ = s1⁻¹ * (s2 * (r⁻¹ * e')) * e'⁻¹ * r := by rw [heq]
        _ = s1⁻¹ * s2 := by group
    show r⁻¹ * (e * e'⁻¹) * r⁻¹⁻¹ ∈ S'
    rw [inv_inv, h]
    exact S'.mul_mem (S'.inv_mem hs1) hs2
  have hee : e = e' := by
    have hu := ((hE r hr).2 e heS).unique (y₁ := (1, ⟨e, he⟩))
      (y₂ := (⟨e * e'⁻¹, hstab⟩, ⟨e', he'⟩)) (by simp) (by simp)
    exact congrArg (fun x => (x.2 : G)) hu
  subst hee
  exact ⟨rfl, mul_right_cancel heq⟩

theorem double_coset_translation : DCTrans.{u} := by
  intro G _ Γ S S' hS hS' R hR E hE
  have hEsub : ∀ r ∈ R, E r ⊆ (S : Set G) := fun r hr => (hE r hr).1
  refine ⟨fun p q hpq => ?_, ?_, fun γ hγ => ?_⟩
  · refine (dc_core Γ S S' hS hS' R hR E hE p q 1 1 S'.one_mem S'.one_mem ?_).1
    rw [one_mul, one_mul]
    exact hpq
  · rintro _ ⟨⟨⟨r, hr⟩, ⟨e, he⟩⟩, rfl⟩
    exact Γ.mul_mem (Γ.inv_mem (hR.1 hr)) (hS (hEsub r hr he))
  · obtain ⟨⟨r, hr⟩, ⟨s, hs, s', hs', hrep⟩, -⟩ := hR.2 γ⁻¹ (Γ.inv_mem hγ)
    change s * r * s' = γ⁻¹ at hrep
    obtain ⟨⟨⟨t, ht⟩, ⟨e, he⟩⟩, hte, -⟩ := (hE r hr).2 s⁻¹ (S.inv_mem hs)
    change t * e = s⁻¹ at hte
    have ht' : r⁻¹ * t * r ∈ S' := by
      have h2 := (Subgroup.mem_inf.mp ht).2
      rw [Subgroup.mem_comap] at h2
      change r⁻¹ * t * r⁻¹⁻¹ ∈ S' at h2
      rwa [inv_inv] at h2
    have hmem : s'⁻¹ * (r⁻¹ * t * r) ∈ S' := S'.mul_mem (S'.inv_mem hs') ht'
    have hγeq : s'⁻¹ * (r⁻¹ * t * r) * (r⁻¹ * e) = γ := by
      calc s'⁻¹ * (r⁻¹ * t * r) * (r⁻¹ * e) = s'⁻¹ * r⁻¹ * (t * e) := by group
        _ = s'⁻¹ * r⁻¹ * s⁻¹ := by rw [hte]
        _ = (s * r * s')⁻¹ := by group
        _ = γ := by rw [hrep, inv_inv]
    refine ⟨(⟨s'⁻¹ * (r⁻¹ * t * r), hmem⟩,
      ⟨r⁻¹ * e, ⟨⟨⟨r, hr⟩, ⟨e, he⟩⟩, rfl⟩⟩), hγeq, ?_⟩
    rintro ⟨⟨a, ha⟩, ⟨d, ⟨p, rfl⟩⟩⟩ hy
    obtain ⟨hp, ha'⟩ := dc_core Γ S S' hS hS' R hR E hE p ⟨⟨r, hr⟩, ⟨e, he⟩⟩ a
      (s'⁻¹ * (r⁻¹ * t * r)) ha hmem (hy.trans hγeq.symm)
    subst hp
    exact Prod.ext (Subtype.ext ha') (Subtype.ext rfl)

end PI.FoldDCUnfold.W
end

section

open MeasureTheory
open scoped ENNReal NNReal
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable

namespace PI.FoldDCUnfold.W

universe u

theorem translation_exists : TransExists.{u} := by
  intro G _ K H hHK
  classical
  obtain ⟨rep, hrepdef⟩ : ∃ rep : G → G,
      ∀ γ, rep γ = (Quotient.mk (QuotientGroup.rightRel H) γ).out := ⟨_, fun _ => rfl⟩
  have hrep : ∀ γ, γ * (rep γ)⁻¹ ∈ H := fun γ => by
    rw [hrepdef]
    exact QuotientGroup.rightRel_apply.mp
      (Quotient.exact (Quotient.out_eq (Quotient.mk (QuotientGroup.rightRel H) γ)))
  have hrep_eq : ∀ γ γ', γ * γ'⁻¹ ∈ H → rep γ = rep γ' := fun γ γ' h => by
    rw [hrepdef, hrepdef]
    congr 1
    exact Quotient.sound (QuotientGroup.rightRel_apply.mpr (by simpa using H.inv_mem h))
  have hrepK : ∀ γ ∈ K, rep γ ∈ K := fun γ hγ => by
    have h1 : rep γ = (γ * (rep γ)⁻¹)⁻¹ * γ := by group
    rw [h1]
    exact K.mul_mem (K.inv_mem (hHK (hrep γ))) hγ
  refine ⟨rep '' (K : Set G), ?_, ?_⟩
  · rintro _ ⟨γ, hγ, rfl⟩
    exact hrepK γ hγ
  · intro γ hγ
    refine ⟨(⟨γ * (rep γ)⁻¹, hrep γ⟩, ⟨rep γ, γ, hγ, rfl⟩), by simp, ?_⟩
    rintro ⟨⟨s, hs⟩, ⟨e, ⟨γ', hγ', rfl⟩⟩⟩ he
    have he' : s * rep γ' = γ := he
    have h1 : rep γ' = rep γ := by
      have h2 : rep (rep γ') = rep γ' :=
        hrep_eq _ _ (by simpa using H.inv_mem (hrep γ'))
      rw [← h2]
      apply hrep_eq
      rw [← he']
      simpa using H.inv_mem hs
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show s = γ * (rep γ)⁻¹
      calc s = s * rep γ' * (rep γ')⁻¹ := by group
        _ = γ * (rep γ)⁻¹ := by rw [he', h1]
    · exact h1

theorem translation_independent : TransIndep.{u} := by
  intro G _ Γ H T T' hT hT' c hc f hf
  classical
  have hmem : ∀ η : T, (η : G) * c ∈ Γ := fun η => Γ.mul_mem (hT.1 η.2) hc
  choose φ hφ using fun η : T => (hT'.2 _ (hmem η)).exists
  have hfeq : ∀ η : T, f ((η : G) * c) = f ((φ η).2 : G) := fun η => by
    rw [← hφ η, hf _ (φ η).1.2]
  have hinj : Function.Injective (fun η => (φ η).2) := by
    intro η₁ η₂ h12
    have h12' : (φ η₁).2 = (φ η₂).2 := h12
    have e1 : ((φ η₁).1 : G) * ((φ η₂).2 : G) = η₁ * c := by rw [← h12']; exact hφ η₁
    have e2 : ((φ η₂).1 : G) * ((φ η₂).2 : G) = η₂ * c := hφ η₂
    have hk : (((φ η₂).1 : G) * ((φ η₁).1 : G)⁻¹) * η₁ = η₂ := by
      calc (((φ η₂).1 : G) * ((φ η₁).1 : G)⁻¹) * η₁
          = ((φ η₂).1 : G) * ((φ η₁).1 : G)⁻¹ * (η₁ * c) * c⁻¹ := by group
        _ = ((φ η₂).1 : G) * ((φ η₁).1 : G)⁻¹ * (((φ η₁).1 : G) * ((φ η₂).2 : G)) * c⁻¹ := by
          rw [e1]
        _ = (((φ η₂).1 : G) * ((φ η₂).2 : G)) * c⁻¹ := by group
        _ = η₂ * c * c⁻¹ := by rw [e2]
        _ = η₂ := by group
    have hu := (hT.2 (η₂ : G) (hT.1 η₂.2)).unique
      (y₁ := ((1 : H), η₂)) (y₂ := (⟨((φ η₂).1 : G) * ((φ η₁).1 : G)⁻¹,
        H.mul_mem (φ η₂).1.2 (H.inv_mem (φ η₁).1.2)⟩, η₁)) (by simp) hk
    exact (congrArg Prod.snd hu).symm
  have hsurj : Function.Surjective (fun η => (φ η).2) := by
    intro η'
    have hm : (η' : G) * c⁻¹ ∈ Γ := Γ.mul_mem (hT'.1 η'.2) (Γ.inv_mem hc)
    obtain ⟨⟨s, η⟩, hsη, -⟩ := hT.2 _ hm
    have hsη' : (s : G) * η = η' * c⁻¹ := hsη
    refine ⟨η, ?_⟩
    have hy : ((s : G))⁻¹ * η' = η * c := by
      have : (η : G) = (s : G)⁻¹ * (η' * c⁻¹) := by rw [← hsη']; group
      rw [this]
      group
    have hu := (hT'.2 _ (hmem η)).unique (hφ η)
      (y₂ := (⟨(s : G)⁻¹, H.inv_mem s.2⟩, η')) hy
    exact congrArg Prod.snd hu
  calc ∑' η : T, f ((η : G) * c) = ∑' η : T, f ((φ η).2 : G) := tsum_congr hfeq
    _ = ∑' η' : T', f η' :=
      Equiv.tsum_eq (Equiv.ofBijective (fun η => (φ η).2) ⟨hinj, hsurj⟩) (fun η' : T' => f η')

theorem translation_product : TransProd.{u} := by
  intro G _ Γ S H E D hHS hSΓ hE hD
  have key : ∀ (e₁ e₂ : E) (d₁ d₂ : D), (e₁ : G) * d₁ = e₂ * d₂ → e₁ = e₂ ∧ d₁ = d₂ := by
    intro e₁ e₂ d₁ d₂ h
    have hγ : (e₁ : G) * d₁ ∈ Γ := Γ.mul_mem (hSΓ (hE.1 e₁.2)) (hD.1 d₁.2)
    have u := (hD.2 _ hγ).unique (y₁ := (⟨e₁, hE.1 e₁.2⟩, d₁)) (y₂ := (⟨e₂, hE.1 e₂.2⟩, d₂))
      rfl h.symm
    have hd : d₁ = d₂ := congrArg Prod.snd u
    have he : (e₁ : G) = e₂ := congrArg (fun p : S × D => ((p.1 : S) : G)) u
    exact ⟨Subtype.ext he, hd⟩
  refine ⟨fun p q h => ?_, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := key p.1 q.1 p.2 q.2 h
    exact Prod.ext h1 h2
  · rintro _ ⟨p, rfl⟩
    exact Γ.mul_mem (hSΓ (hE.1 p.1.2)) (hD.1 p.2.2)
  · intro γ hγ
    obtain ⟨⟨s, d⟩, hsd, hsd_u⟩ := hD.2 γ hγ
    obtain ⟨⟨h, e⟩, hhe, hhe_u⟩ := hE.2 s s.2
    have hsd' : (s : G) * d = γ := hsd
    have hhe' : (h : G) * e = s := hhe
    refine ⟨(h, ⟨(e : G) * d, ⟨(e, d), rfl⟩⟩), ?_, ?_⟩
    · show (h : G) * ((e : G) * d) = γ
      rw [← mul_assoc, hhe']
      exact hsd'
    · rintro ⟨h', ⟨x, ⟨⟨e', d'⟩, rfl⟩⟩⟩ hx
      have hx' : (h' : G) * ((e' : G) * d') = γ := hx
      have hs' : (h' : G) * e' ∈ S := S.mul_mem (hHS h'.2) (hE.1 e'.2)
      have u1 := hsd_u (⟨(h' : G) * e', hs'⟩, d')
        (by show (h' : G) * e' * d' = γ; rw [mul_assoc]; exact hx')
      have hd' : d' = d := congrArg Prod.snd u1
      have hs1 : (h' : G) * e' = s := congrArg (fun p : S × D => ((p.1 : S) : G)) u1
      have u2 := hhe_u (h', e') hs1
      have hh : h' = h := congrArg Prod.fst u2
      have he : e' = e := congrArg Prod.snd u2
      subst hd' hh he
      rfl

end PI.FoldDCUnfold.W
end
