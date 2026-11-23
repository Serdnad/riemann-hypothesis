module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1428
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1500
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1427
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1505
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1506
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SmoothNormalise

theorem inv_mem_of_isField {κ' : Type} [Field κ'] {O : Subring κ'} (hF : IsField O) {f : κ'}
    (hf : f ∈ O) (h0 : f ≠ 0) : f⁻¹ ∈ O := by
  obtain ⟨y, hy⟩ := hF.mul_inv_cancel (a := (⟨f, hf⟩ : O)) (fun e => h0 (congrArg Subtype.val e))
  have : f * (y : κ') = 1 := congrArg Subtype.val hy
  rw [inv_eq_of_mul_eq_one_right this]; exact y.2

theorem const_of_isField {κ' : Type} [Field κ'] [Algebra ℂ κ'] {O : Subring κ'}
    (hO : IsLocModel (algebraMap ℂ κ') O) (hR : RatRes (algebraMap ℂ κ') O) (hF : IsField O) :
    ∀ x : κ', ∃ α : ℂ, x = algebraMap ℂ κ' α := by
  have hc : ∀ f ∈ O, ∃ α : ℂ, f = algebraMap ℂ κ' α := by
    intro f hf
    obtain ⟨α, hα, h⟩ := hR f hf
    refine ⟨α, ?_⟩
    rcases h with h | h
    · exact sub_eq_zero.1 h
    · by_contra hne
      exact h (inv_mem_of_isField hF hα (sub_ne_zero.2 hne))
  intro x
  obtain ⟨a, ha, b, hb, hb0, e⟩ := hO.frac x
  obtain ⟨α, rfl⟩ := hc a ha
  obtain ⟨β, rfl⟩ := hc b hb
  refine ⟨α / β, ?_⟩
  rw [map_div₀, eq_div_iff hb0, e]

theorem top_model_of_const {κ' : Type} [Field κ'] [Algebra ℂ κ']
    (hc : ∀ x : κ', ∃ α : ℂ, x = algebraMap ℂ κ' α) :
    ∃ (hB : IsLocModel (algebraMap ℂ κ') ⊤), RatRes (algebraMap ℂ κ') ⊤ ∧
    (letI := hB.isLocalRing; IsLocalRing.maximalIdeal (⊤ : Subring κ') = Ideal.span (Set.range (Fin.elim0 : Fin 0 → (⊤ : Subring κ')))) ∧
    (MvPolynomial.eval₂Hom ((algebraMap ℂ κ').codRestrict ⊤ hB.const_mem) (Fin.elim0 : Fin 0 → (⊤ : Subring κ'))).FormallyEtale ∧
    TrBasis (algebraMap ℂ κ') (fun i => ((Fin.elim0 i : (⊤ : Subring κ')) : κ')) := by
  have hsurj : Function.Surjective ((algebraMap ℂ κ').codRestrict (⊤ : Subring κ') (fun _ => trivial)) :=
    fun x => by obtain ⟨α, hα⟩ := hc x; exact ⟨α, Subtype.ext hα.symm⟩
  let hB : IsLocModel (algebraMap ℂ κ') ⊤ :=
    { const_mem := fun _ => trivial
      isLocalRing := (Subring.topEquiv (R := κ')).symm.isLocalRing
      essFiniteType := (RingHom.FiniteType.of_surjective _ hsurj).essFiniteType
      frac := fun f => ⟨f, trivial, 1, trivial, one_ne_zero, mul_one f⟩ }
  refine ⟨hB, ?_, ?_, ?_, ?_⟩
  · intro r _
    obtain ⟨α, hα⟩ := hc r
    exact ⟨α, by rw [hα, sub_self]; exact nonUnit_zero _⟩
  · letI := hB.isLocalRing
    have hfield : IsField (⊤ : Subring κ') := by
      refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {a} ha => ?_⟩
      have ha' : (a : κ') ≠ 0 := fun e => ha (Subtype.ext e)
      exact ⟨⟨(a : κ')⁻¹, trivial⟩, Subtype.ext (mul_inv_cancel₀ ha')⟩
    rw [Set.range_eq_empty, Ideal.span_empty]
    exact IsLocalRing.isField_iff_maximalIdeal_eq.1 hfield
  · have hb : Function.Bijective (MvPolynomial.eval₂Hom ((algebraMap ℂ κ').codRestrict ⊤ hB.const_mem) (Fin.elim0 : Fin 0 → (⊤ : Subring κ'))) := by
      refine ⟨fun P Q e => ?_, fun x => ?_⟩
      · rw [MvPolynomial.eq_C_of_isEmpty P, MvPolynomial.eq_C_of_isEmpty Q] at e ⊢
        simp only [MvPolynomial.eval₂Hom_C] at e
        exact congrArg _ (((algebraMap ℂ κ').codRestrict ⊤ hB.const_mem).injective e)
      · obtain ⟨α, hα⟩ := hsurj x
        exact ⟨MvPolynomial.C α, by simpa using hα⟩
    letI := (MvPolynomial.eval₂Hom ((algebraMap ℂ κ').codRestrict ⊤ hB.const_mem) (Fin.elim0 : Fin 0 → (⊤ : Subring κ'))).toAlgebra
    exact Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId _ _) hb)
  · have e : (algebraMap ℂ κ').toAlgebra = (inferInstance : Algebra ℂ κ') :=
      Algebra.algebra_ext _ _ fun _ => rfl
    unfold TrBasis
    rw [e, isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic]
    refine ⟨algebraicIndependent_empty_type, ⟨fun x => ?_⟩⟩
    obtain ⟨α, rfl⟩ := hc x
    exact isAlgebraic_algebraMap (algebraMap ℂ (Algebra.adjoin ℂ (Set.range (fun i : Fin 0 => ((Fin.elim0 i : (⊤ : Subring κ')) : κ')))) α)

theorem inv_not_mem {κ' : Type} [Field κ'] [Algebra ℂ κ'] (F : Place (algebraMap ℂ κ'))
    {B : Subring κ'} (hBF : B ≤ F.ring.toSubring) {f : κ'} (hf : f ≠ 0) (hp : 0 < F.ord f) :
    f⁻¹ ∉ B := by
  intro h
  have := (F.ord_nonneg_iff (inv_ne_zero hf)).2 (hBF h)
  rw [F.ord_inv] at this
  omega

theorem nonUnit_sub {κ' : Type} [Field κ'] {B : Subring κ'} [IsLocalRing B] {x y : κ'}
    (hx : NonUnit B x) (hy : NonUnit B y) : NonUnit B (x - y) := by
  have hx' := (nonUnit_iff (R := B) ⟨x, hx.1⟩).1 hx
  have hy' := (nonUnit_iff (R := B) ⟨y, hy.1⟩).1 hy
  have h := (nonUnit_iff (R := B) (⟨x, hx.1⟩ - ⟨y, hy.1⟩)).2
  exact h ((IsLocalRing.mem_maximalIdeal _).1 (Ideal.sub_mem _
    ((IsLocalRing.mem_maximalIdeal _).2 hx') ((IsLocalRing.mem_maximalIdeal _).2 hy')))

theorem normalise_at_smooth_point : ∀ {κ' : Type} [Field κ'] [Algebra ℂ κ'] (O : Subring κ') (l : ℕ) (a : Fin l → κ'),
  IsLocModel (algebraMap ℂ κ') O → RatRes (algebraMap ℂ κ') O → a ≠ 0 →
  ∃ (B : Subring κ') (hB : IsLocModel (algebraMap ℂ κ') B) (r : ℕ) (τ : Fin r → B),
    RatRes (algebraMap ℂ κ') B ∧ Dominates (RingHom.id κ') B O ∧
    (letI := hB.isLocalRing; IsLocalRing.maximalIdeal B = Ideal.span (Set.range τ)) ∧
    (MvPolynomial.eval₂Hom ((algebraMap ℂ κ').codRestrict B hB.const_mem) τ).FormallyEtale ∧
    TrBasis (algebraMap ℂ κ') (fun i => (τ i : κ')) ∧ ∃ j₀, a j₀ ≠ 0 ∧ ∀ i, a i / a j₀ ∈ B := by
  classical
  intro κ' _ _ O l a hO hR ha
  obtain ⟨j, hj⟩ := Function.ne_iff.1 ha
  by_cases hF : IsField O
  · have hc := const_of_isField hO hR hF
    obtain ⟨hB, h1, h2, h3, h4⟩ := top_model_of_const hc
    refine ⟨⊤, hB, 0, Fin.elim0, h1, fun f hf => ⟨trivial, fun hn => ?_⟩, h2, h3, h4, j, hj,
      fun _ => trivial⟩
    refine ⟨trivial, Or.inl ?_⟩
    by_contra h0
    rcases hn.2 with h | h
    · exact h0 h
    · exact h (inv_mem_of_isField hF hf h0)
  · obtain ⟨F, hFO, hpos⟩ := GlobalTheory.T.exists_place_dominating_local_domain_complex O hO hF
    obtain ⟨j₀, hj₀, hdiv⟩ : ∃ j₀, a j₀ ≠ 0 ∧ ∀ i, a i / a j₀ ∈ F.ring := by
      obtain ⟨j₀, hj₀s, hmin⟩ := (Finset.univ.filter (fun i => a i ≠ 0)).exists_min_image
        (fun i => F.ord (a i)) ⟨j, by simpa using hj⟩
      have hj₀ : a j₀ ≠ 0 := (Finset.mem_filter.1 hj₀s).2
      refine ⟨j₀, hj₀, fun i => ?_⟩
      by_cases hi : a i = 0
      · rw [hi, zero_div]; exact zero_mem _
      · have hne : a i / a j₀ ≠ 0 := div_ne_zero hi hj₀
        rw [← F.ord_nonneg_iff hne, div_eq_mul_inv, F.ord_mul hi (inv_ne_zero hj₀), F.ord_inv]
        have := hmin i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
        omega
    letI : Algebra ℂ O := ((algebraMap ℂ κ').codRestrict O hO.const_mem).toAlgebra
    haveI : Algebra.EssFiniteType ℂ O := hO.essFiniteType
    obtain ⟨σ, hσ⟩ := (Algebra.essFiniteType_iff ℂ O).1 inferInstance
    let S : Finset κ' := σ.image (fun x : O => (x : κ')) ∪ Finset.univ.image (fun i => a i / a j₀)
    have hS : ∀ x ∈ S, x ∈ F.ring := by
      intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
        exact hFO _ y.2
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
        exact hdiv i
    obtain ⟨A, hAs, hAF, hSA, hAfrac⟩ := GlobalTheory.T.exists_smooth_finiteType_subalgebra_in_ring F S hS
    obtain ⟨B, hB, hRB, hAB, hBF, hsm⟩ := GlobalTheory.T.exists_pointLocalRing_closedPoint_centre_of_place F A hAs hAF hAfrac
    obtain ⟨r, τ, hm, het, htr⟩ := GlobalTheory.T.exists_etaleCoords_localRingOfVarietyPoint_residueComplex B hB hRB hsm
    have hSB : ∀ x ∈ S, x ∈ B := fun x hx => hAB (hSA x hx)
    letI := hB.isLocalRing
    letI := hO.isLocalRing

    have hadj : ∀ t : O, t ∈ Algebra.adjoin ℂ (σ : Set O) → (t : κ') ∈ B := by
      intro t ht
      induction ht using Algebra.adjoin_induction with
      | mem x hx => exact hSB _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx))
      | algebraMap α => exact hB.const_mem α
      | add x y _ _ hx hy => exact B.add_mem hx hy
      | mul x y _ _ hx hy => exact B.mul_mem hx hy

    have hnon : ∀ f ∈ B, NonUnit O f → NonUnit B f := by
      intro f hfB hn
      refine ⟨hfB, ?_⟩
      by_cases h0 : f = 0
      · exact Or.inl h0
      · refine Or.inr (inv_not_mem F hBF h0 (hpos ⟨f, hn.1⟩ ?_ h0))
        exact (IsLocalRing.mem_maximalIdeal _).2 ((nonUnit_iff (R := O) ⟨f, hn.1⟩).1 hn)

    have hunit : ∀ t : O, IsUnit t → (t : κ') ∈ B → (t : κ')⁻¹ ∈ B := by
      intro t ht htB
      by_contra hinv
      have htn : NonUnit B (t : κ') := ⟨htB, Or.inr hinv⟩
      obtain ⟨α, hα⟩ := hR t t.2
      have hαB : algebraMap ℂ κ' α ∈ B := hB.const_mem α
      have hu : NonUnit B ((t : κ') - algebraMap ℂ κ' α) := hnon _ (B.sub_mem htB hαB) hα
      have hc : NonUnit B (algebraMap ℂ κ' α) := by
        simpa using nonUnit_sub htn hu
      by_cases hα0 : α = 0
      · subst hα0
        simp only [map_zero, sub_zero] at hα
        exact (nonUnit_iff (R := O) t).1 hα ht
      · rcases hc.2 with h | h
        · exact hα0 ((map_eq_zero_iff _ (algebraMap ℂ κ').injective).1 h)
        · exact h (by rw [← map_inv₀]; exact hB.const_mem _)
    refine ⟨B, hB, r, τ, hRB, fun f hf => ?_, hm, het, htr, j₀, hj₀,
      fun i => hSB _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))⟩
    obtain ⟨t, htA, htu, hft⟩ := hσ ⟨f, hf⟩
    have htB := hadj t htA
    have hfB : f ∈ B := by
      have h1 := hadj _ hft
      have h2 := hunit t htu htB
      have ht0 : (t : κ') ≠ 0 := fun e => htu.ne_zero (Subtype.ext e)
      have : f = (f * (t : κ')) * (t : κ')⁻¹ := by field_simp
      rw [this]
      exact B.mul_mem h1 h2
    exact ⟨hfB, hnon f hfB⟩

end GlobalTheory.SmoothNormalise
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.IndepCx

theorem finiteType_int {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) {U : X.Opens} (hU : IsAffineOpen U) : Algebra.FiniteType ℤ Γ(X, U) := by
  obtain ⟨N, j, _, hj⟩ := hX.isProjOver
  have := isProper_str k N
  have : IsProper p := hj ▸ inferInstance
  have h1 : (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U).FiniteType :=
    (p.finiteType_appLE (isAffineOpen_top _) hU _).comp
      (.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)
  have := hX.finite
  have h0 : (algebraMap ℤ k).FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
  have h2 := h1.comp h0
  rw [RingHom.ext_int ((ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U).comp (algebraMap ℤ k)) (algebraMap ℤ Γ(X, U))] at h2
  exact RingHom.finiteType_algebraMap.1 h2

end GlobalTheory.HSAmp.IndepCx

namespace GlobalTheory.HSAmp


open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX) in
theorem linearIndependent_vals : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), ∀ (a b : ℤ) (ι : Type) [Fintype ι] (f : ι → X.functionField),
    (∀ i, f i ∈ P.H a b) → LinearIndependent ℤ f → ∀ c : ι → ℂ,
    (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∑ i, c i * val P a b σ y (f i) = 0) → c = 0 := by
  intro k _ X _ p D hX P a b ι _ f hf hli c hc
  classical
  obtain ⟨i, hi⟩ := exists_chart P.L.isLB (genericPoint X)
  obtain ⟨j, hj⟩ := exists_chart P.A.isLB (genericPoint X)
  obtain ⟨U, hU, hgU, hle⟩ := exists_isAffineOpen_mem_and_subset (x := genericPoint X)
    (U := P.L.B.U i ⊓ P.A.B.U j) ⟨hi, hj⟩
  have hl : U ≤ P.L.B.U i := fun x hx => (hle hx).1
  have hr : U ≤ P.A.B.U j := fun x hx => (hle hx).2
  have : Nonempty U := ⟨⟨_, hgU⟩⟩
  have : CharZero Γ(X, U) :=
    ((resG X (le_top : U ≤ ⊤)).charZero_iff (map_injective_of_isIntegral X _)).1 hX.charZero
  have := IndepCx.finiteType_int hX hU
  choose g hg using fun l => exists_fnOf_eq hgU fun x hx => hf l x i j (hl hx) (hr hx)
  have hu0 : (P.r i : X.functionField) ^ a * (P.r' j : X.functionField) ^ b ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ (P.r i).ne_zero) (zpow_ne_zero _ (P.r' j).ne_zero)
  have hloc : ∀ l, P.loc a b (f l) i j = f l * ((P.r i : X.functionField) ^ a * (P.r' j : X.functionField) ^ b) :=
    fun l => by simp only [Pair.loc]; ring
  have hgli : LinearIndependent ℤ g := by
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro n hn
    apply hli n
    have h1 := congrArg (fnOf U hgU) hn

    rw [map_sum, map_zero] at h1
    simp only [map_zsmul, hg, hloc] at h1
    have h2 : (∑ l, n l • f l) * ((P.r i : X.functionField) ^ a * (P.r' j : X.functionField) ^ b) = 0 := by
      rw [Finset.sum_mul]; simpa only [smul_mul_assoc] using h1
    exact (mul_eq_zero.1 h2).resolve_right hu0
  set e := Fintype.equivFin ι
  obtain ⟨x, hx⟩ := GlobalTheory.CxPointsSep.exists_det_ne_zero Γ(X, U) (Fintype.card ι) (g ∘ e.symm)
    (hgli.comp _ e.symm.injective)
  have key : ∀ s, ∑ l, c l * x s (g l) = 0 := by
    intro s
    have hy : ofHom (σ := (x s).comp (algX p U)) hU (x s) (fun _ => rfl) ∈ ptsIn p ((x s).comp (algX p U)) U :=
      ofHom_mem hU _ _
    obtain ⟨θ, hθ, hval⟩ := GlobalTheory.T.sectionValueUnitFrame_eq_localFunction_unitScalar k X p P a b _ _ i j (ptsIn_mono hl hy) (ptsIn_mono hr hy)
    have h0 := hc _ (ofHom (σ := (x s).comp (algX p U)) hU (x s) (fun _ => rfl))
    have hθ0 : θ ≠ 0 := by
      intro h; rw [h, norm_zero] at hθ; exact zero_ne_one hθ
    set E : ℂ := ((Real.exp (-(a * (P.L.φ ((x s).comp (algX p U))).φ i
      (ofHom (σ := (x s).comp (algX p U)) hU (x s) (fun _ => rfl)) +
      b * (P.A.φ ((x s).comp (algX p U))).φ j (ofHom (σ := (x s).comp (algX p U)) hU (x s) (fun _ => rfl))) / 2) : ℝ) : ℂ)
      with hEdef
    have hE : E ≠ 0 := Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'
    have hv : ∀ l, val P a b _ (ofHom (σ := (x s).comp (algX p U)) hU (x s) (fun _ => rfl)) (f l) =
        θ * E * x s (g l) := by
      intro l
      rw [hval (f l) (hf l), ← hg l, ratVal_fnOf hy hgU, ev_ofHom]
      ring
    simp only [hv] at h0
    have h3 : θ * E * ∑ l, c l * x s (g l) = 0 := by
      rw [Finset.mul_sum, ← h0]
      exact Finset.sum_congr rfl fun l _ => by ring
    exact (mul_eq_zero.1 h3).resolve_left (mul_ne_zero hθ0 hE)
  have hM : Matrix.mulVec (Matrix.of fun s t => x s ((g ∘ e.symm) t)) (c ∘ e.symm) = 0 := by
    funext s
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Function.comp_apply, Pi.zero_apply]
    rw [← key s, ← e.symm.sum_comp (fun l => c l * x s (g l))]
    exact Finset.sum_congr rfl fun t _ => mul_comm _ _
  have hz := Matrix.eq_zero_of_mulVec_eq_zero hx hM
  funext l
  simpa using congrFun hz (e l)

end GlobalTheory.HSAmp
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

namespace GlobalTheory.MixHt

theorem enat_add_natCast_eq_natCast_exists {c : ℕ∞} {a b : ℕ} (h : c + (a : ℕ∞) = (b : ℕ∞)) : ∃ n : ℕ, c = n ∧ n + a = b := by
  induction c using ENat.recTopCoe with
  | top => simp at h
  | coe n => exact ⟨n, rfl, by exact_mod_cast h⟩

theorem dimOne : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ,
    topologicalKrullDim Y = (e + 1 : ℕ) → (∀ z : Y, Order.coheight z = 1 ↔ HasDim z e) ∧
    ∀ (z : Y) (w : clo z), Order.coheight z = 1 →
      (topologicalKrullDim (clo z) = e ∧ (Order.coheight w = 1 ↔ Order.coheight (cloι z w) = 2)) := by
  intro k _ Y _ q hq e hY
  have hB := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k Y q hq
  have hC := GlobalTheory.T.coheight_add_pointClosureDim_eq_dim k Y q hq (e + 1) hY
  have h1 : ∀ z : Y, Order.coheight z = 1 ↔ HasDim z e := by
    intro z
    obtain ⟨m, hm⟩ := hB.1
    obtain ⟨d, -, hd⟩ := hm z
    obtain ⟨n, hn, hnd⟩ := enat_add_natCast_eq_natCast_exists (hC z d hd)
    constructor
    · intro hz
      rw [hz] at hn
      have : n = 1 := by exact_mod_cast hn.symm
      subst this
      have : d = e := by omega
      exact this ▸ hd
    · intro hz
      have := hB.2.1 z d e hd hz
      subst this
      rw [hn]
      have : n = 1 := by omega
      simp [this]
  refine ⟨h1, fun z w hz => ?_⟩
  have hze : HasDim z e := (h1 z).1 hz
  have hgen : HasDim (genericPoint (clo z)) e := by
    rw [← hB.2.2.2.2.1 (clo z) (cloι z) (genericPoint (clo z)) e, cloι_genericPoint]
    exact hze
  have hdim : topologicalKrullDim (clo z) = e := (hB.2.2.2.2.2 (clo z) e).1 hgen
  refine ⟨hdim, ?_⟩
  have hq' : IsAmb (cloι z ≫ q) := hq.sub (cloι z)
  have hB' := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k (clo z) (cloι z ≫ q) hq'
  obtain ⟨m, hm⟩ := hB'.1
  obtain ⟨d, -, hd⟩ := hm w
  have hd' : HasDim (cloι z w) d := (hB.2.2.2.2.1 (clo z) (cloι z) w d).2 hd
  obtain ⟨n, hn, hnd⟩ := enat_add_natCast_eq_natCast_exists (GlobalTheory.T.coheight_add_pointClosureDim_eq_dim k (clo z) (cloι z ≫ q) hq' e hdim w d hd)
  obtain ⟨n', hn', hnd'⟩ := enat_add_natCast_eq_natCast_exists (hC (cloι z w) d hd')
  have : n' = n + 1 := by omega
  rw [hn, hn', this]
  constructor
  · intro h
    have : n = 1 := by exact_mod_cast h
    simp [this]
  · intro h
    have : n + 1 = 2 := by exact_mod_cast h
    have : n = 1 := by omega
    simp [this]

end GlobalTheory.MixHt
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem locU_of_iSup_range_eq_top : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (M' : Type) [AddCommGroup M'] [Module ℂ M'] (F' : ι → ι → Module.End ℂ M') (G : Set (M →ₗ[ℂ] M')), (∀ f ∈ G, ∀ a b, s a = s b → ∀ x, f (F a b x) = F' a b (f x)) → (⨆ f ∈ G, LinearMap.range f) = ⊤ → LocU s F → LocU s F' := by
  intro ι M _ _ _ _ s F M' _ _ F' G hG hsup hloc t
  classical
  have hy : ∀ y ∈ t, ∃ S : Finset G, y ∈ ⨆ i ∈ S, LinearMap.range (i : M →ₗ[ℂ] M') := by
    intro y _
    have h1 : y ∈ ⨆ i : G, LinearMap.range (i : M →ₗ[ℂ] M') := by
      rw [iSup_subtype'' G (fun f : M →ₗ[ℂ] M' => LinearMap.range f), hsup]; trivial
    exact Submodule.mem_iSup_iff_exists_finset.1 h1
  choose S hS using hy
  let SS : Finset G := t.attach.biUnion (fun y => S y.1 y.2)
  have hmem : ∀ y ∈ t, y ∈ ⨆ i ∈ SS, LinearMap.range (i : M →ₗ[ℂ] M') := by
    intro y hy
    exact (biSup_mono (fun i hi => Finset.mem_biUnion.2 ⟨⟨y, hy⟩, Finset.mem_attach _ _, hi⟩) :
      (⨆ i ∈ S y hy, LinearMap.range (i : M →ₗ[ℂ] M')) ≤ _) (hS y hy)
  let e : SS ≃ Fin SS.card := SS.equivFin
  let f : Fin SS.card → (M →ₗ[ℂ] M') := fun k => ((e.symm k).1 : M →ₗ[ℂ] M')
  let g : (Fin SS.card → M) →ₗ[ℂ] M' := ∑ k, f k ∘ₗ LinearMap.proj k
  have hg : ∀ x, g x = ∑ k, f k (x k) := by intro x; simp [g]
  have hrange : ∀ y ∈ t, y ∈ LinearMap.range g := by
    intro y hy
    refine (iSup₂_le ?_ : (⨆ i ∈ SS, LinearMap.range (i : M →ₗ[ℂ] M')) ≤ LinearMap.range g) (hmem y hy)
    intro i hi w hw
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 hw
    refine ⟨Pi.single (e ⟨i, hi⟩) x, ?_⟩
    rw [hg, Finset.sum_eq_single (e ⟨i, hi⟩)]
    · simp [f]
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  choose z hz using fun y hy => LinearMap.mem_range.1 (hrange y hy)
  obtain ⟨U, hU, hUU⟩ := GlobalTheory.T.isLocallyBlockUnitary_pi_fin ι M s F hloc SS.card (t.attach.image fun y : {x // x ∈ t} => z y.1 y.2)
  refine ⟨U.map g, ?_, GlobalTheory.T.isBlockUnitaryFiniteSubspace_map_intertwiner ι (Fin SS.card → M) s _ M' F' g U ?_ hUU⟩
  · intro y hy
    exact ⟨z y hy, hU _ (Finset.mem_image.2 ⟨⟨y, hy⟩, Finset.mem_attach _ _, rfl⟩), hz y hy⟩
  · intro a b hab x _

    rw [hg, hg, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    exact hG (f k) (e.symm k).1.2 a b hab (x k)

end GlobalTheory.HoweR
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.exists_dominant_restriction_pointClosures : ∀ (X Y : Scheme.{0}) (π : Y ⟶ X) (y : Y), ∃ g : clo y ⟶ clo (π y), g ≫ cloι (π y) = cloι y ≫ π ∧ g (genericPoint _) = genericPoint _ ∧ ∀ w : clo y, g.residueDegree w = π.residueDegree (cloι y w) := by
  first | exact @GlobalTheory.MixHt.clo_restrict_dominant | exact GlobalTheory.MixHt.clo_restrict_dominant | (intros; apply GlobalTheory.MixHt.clo_restrict_dominant <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.complexPointsOverRingHom_isHomeomorph_baseChange : ∀ (k K : Type) [CommRing k] [CommRing K] (ρ : k →+* K) (X G : Scheme.{0}) (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap ρ)) (τ : K →+* ℂ), IsHomeomorph (bcPt hp.w τ) := by
  first | exact @GlobalTheory.Mix.isHomeomorph_bcPt | exact GlobalTheory.Mix.isHomeomorph_bcPt | (intros; apply GlobalTheory.Mix.isHomeomorph_bcPt <;> assumption)
end
