module

public import Formalism.ConjugateSelfDual.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.RingTheory.Localization.Cardinality
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem frob_fixes_root_of_one_mod (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (M : ℕ) (ζ : F) (hζ : IsPrimitiveRoot ζ M) (v : HeightOneSpectrum (𝓞 F))
    (hMv : ((M : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (A : ValuationSubring Ω) (hA : Formalism.ConjugateSelfDual.IsPlaceOver A v) (σ : Formalism.ConjugateSelfDual.G F Ω)
    (hσ : Formalism.ConjugateSelfDual.IsFrob A (Formalism.ConjugateSelfDual.normV v) σ)
    (x : 𝓞 F) (hx : x - 1 ∈ v.asIdeal) (w : Ω) (hw : w ^ M = algebraMap F Ω (x : F)) :
    σ w = w := by
  set q := Formalism.ConjugateSelfDual.normV v
  set x' := algebraMap F Ω (x : F) with hx'
  have hM0 : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; simp at hMv
    · exact h
  haveI : NeZero M := ⟨hM0.ne'⟩
  have hx1 : A.valuation (x' - 1) < 1 := by
    have := (hA (x - 1)).2 hx
    simpa [hx'] using this
  have hMk : ¬ A.valuation (M : Ω) < 1 := by
    intro h; apply hMv; apply (hA (M : 𝓞 F)).1; simpa using h
  have hpow : ∀ y : Ω, y ^ M ∈ A → y ∈ A := by
    intro y hy
    rw [← A.valuation_le_one_iff] at hy ⊢
    rwa [map_pow, pow_le_one_iff hM0.ne'] at hy
  have hx'A : x' ∈ A := by
    have h1 : x' - 1 ∈ A := (A.valuation_le_one_iff _).1 hx1.le
    simpa using add_mem h1 A.one_mem
  have hwA : w ∈ A := hpow w (hw ▸ hx'A)
  set ζ' := algebraMap F Ω ζ with hζ'
  have hζ'p : IsPrimitiveRoot ζ' M := hζ.map_of_injective (algebraMap F Ω).injective
  have hσζ : ∀ n : ℕ, σ (ζ' ^ n) = ζ' ^ n := by
    intro n; rw [map_pow, hζ', AlgEquiv.commutes]
  have hσx : σ x' = x' := AlgEquiv.commutes σ _
  have hroot : ∀ μ : Ω, μ ^ M = 1 → μ ∈ A := fun μ h => hpow μ (h ▸ A.one_mem)
  let res := IsLocalRing.residue A
  have key : ∀ a b : A, res a = res b ↔ A.valuation ((a : Ω) - b) < 1 := by
    intro a b
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
    simp
  have hfrob : ∀ a : A, ∃ b : A, (b : Ω) = σ a ∧ res b = res a ^ q := by
    intro a
    have h := hσ.2 a ((A.valuation_le_one_iff _).2 a.2)
    have hb : σ (a : Ω) ∈ A := by
      have h1 : σ (a:Ω) - (a:Ω) ^ q ∈ A := (A.valuation_le_one_iff _).1 h.le
      have h2 : (a : Ω) ^ q ∈ A := A.pow_mem a.2 q
      simpa using add_mem h1 h2
    refine ⟨⟨_, hb⟩, rfl, ?_⟩
    rw [← map_pow, key]; simpa using h

  obtain ⟨μ, hμM, hμ⟩ : ∃ μ : Ω, μ ^ M = 1 ∧ A.valuation (w - μ) < 1 := by
    have hprod := congrArg (Polynomial.eval w) (X_pow_sub_one_eq_prod hM0 hζ'p)
    simp only [eval_sub, eval_pow, eval_X, eval_one, eval_prod, eval_C] at hprod
    by_contra hcon
    push_neg at hcon
    have h1 : A.valuation (w ^ M - 1) = 1 := by
      rw [hprod, map_prod]
      apply Finset.prod_eq_one
      intro μ hμ
      have hμM : μ ^ M = 1 := (mem_nthRootsFinset hM0 (1 : Ω)).1 hμ
      apply le_antisymm
      · exact (A.valuation_le_one_iff _).2 (A.sub_mem hwA (hroot μ hμM))
      · exact hcon μ hμM
    rw [hw] at h1
    rw [h1] at hx1
    exact lt_irrefl _ hx1
  obtain ⟨j, -, hj⟩ := hζ'p.eq_pow_of_pow_eq_one hμM

  let aw : A := ⟨w, hwA⟩
  let aμ : A := ⟨μ, hroot μ hμM⟩
  have hwμ : res aw = res aμ := (key aw aμ).2 hμ
  obtain ⟨bw, hbw, hbw'⟩ := hfrob aw
  obtain ⟨bμ, hbμ, hbμ'⟩ := hfrob aμ
  have hbμe : bμ = aμ := by
    apply Subtype.ext
    rw [hbμ]; show σ μ = μ
    rw [← hj, hσζ]
  rw [hbμe] at hbμ'
  have hB : res bw = res aw := by
    rw [hbw', hwμ, ← hbμ']

  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow hM0.ne'] at hw
    rw [← hw] at hx1
    simp at hx1
  have hx'0 : x' ≠ 0 := by rw [← hw]; exact pow_ne_zero _ hw0
  set ξ := σ w / w with hξ
  have hξM : ξ ^ M = 1 := by
    rw [hξ, div_pow, ← map_pow, hw, hσx, div_self hx'0]
  let aξ : A := ⟨ξ, hroot ξ hξM⟩
  have hbw_eq : bw = aξ * aw := by
    apply Subtype.ext
    show (bw : Ω) = ξ * w
    rw [hbw, hξ, div_mul_cancel₀ _ hw0]
  have hresw : res aw ≠ 0 := by
    intro h0
    have h1 : res (aw ^ M) = 0 := by rw [map_pow, h0, zero_pow hM0.ne']
    have h2 : res (aw ^ M) = res 1 := by
      rw [key]
      have : ((aw ^ M : A) : Ω) = x' := by simp [aw, hw]
      rw [this]; simpa using hx1
    rw [h1, map_one] at h2
    exact zero_ne_one h2
  have hresξ : res aξ = 1 := by
    have h := hB
    rw [hbw_eq, map_mul] at h
    exact mul_right_cancel₀ hresw (h.trans (one_mul _).symm)
  by_contra hne
  have hξ1 : ξ ≠ 1 := by
    intro h; apply hne
    rw [hξ] at h
    exact (div_eq_one_iff_eq hw0).1 h
  have hsum : ∑ l ∈ Finset.range M, ξ ^ l = 0 := by
    rw [geom_sum_eq hξ1, hξM, sub_self, zero_div]
  have hsumA : ∑ l ∈ Finset.range M, aξ ^ l = 0 := by
    apply Subtype.ext
    simpa [aξ] using hsum
  have hres : res ((M : ℕ) : A) = res 0 := by
    have := congrArg res hsumA

    rw [map_sum] at this
    simp only [map_pow, hresξ, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one] at this
    rw [map_natCast, this]
  rw [key] at hres
  apply hMk
  simpa using hres

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.L2.Pj

namespace GlobalTheory.ComplexEmbedding

open Cardinal IsLocalRing

theorem mk_le_continuum_of_finite_residueField (V : Type) [CommRing V] [IsLocalRing V]
    [IsNoetherianRing V] [Finite (ResidueField V)] : #V ≤ 𝔠 := by
  have hfin : ∀ n : ℕ, Finite (V ⧸ maximalIdeal V ^ n) := fun n =>
    haveI : Finite (V ⧸ maximalIdeal V) := inferInstanceAs (Finite (ResidueField V))
    Ideal.finite_quotient_pow (maximalIdeal V).fg_of_isNoetherianRing n
  let f : V → ∀ n : ℕ, V ⧸ maximalIdeal V ^ n := fun x n => Ideal.Quotient.mk _ x
  have hinj : Function.Injective f := by
    intro x y hxy
    have : x - y ∈ ⨅ n : ℕ, maximalIdeal V ^ n :=
      Ideal.mem_iInf.2 fun n => Ideal.Quotient.eq.1 (congrFun hxy n)
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal V).ne_top] at this
    exact sub_eq_zero.1 this
  refine (mk_le_of_injective hinj).trans ?_
  rw [mk_pi]
  refine (prod_le_prod _ (fun _ => ℵ₀) fun n => mk_le_aleph0).trans ?_
  simp

theorem exists_embedding_of_mk_le_continuum {K Ω : Type} [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] (hΩ : #Ω ≤ 𝔠) (σ : K →+* ℂ) :
    ∃ P : Ω →+* ℂ, P.comp (algebraMap K Ω) = σ := by
  let _ : Algebra K ℂ := σ.toAlgebra
  have hK : #K ≤ ℵ₀ := by
    have := Algebra.IsAlgebraic.cardinalMk_le_max ℚ K
    simpa [Cardinal.mkRat] using this
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K Ω
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis K ℂ
  have hst : #s ≤ #t := by
    have h1 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hK
      (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum)
    rw [← h1, Cardinal.mk_complex]
    exact (Cardinal.mk_subtype_le _).trans hΩ
  obtain ⟨e⟩ := hst
  have hv : AlgebraicIndependent K (((↑) : t → ℂ) ∘ e) := ht.1.comp e e.injective
  let f : IntermediateField.adjoin K (Set.range ((↑) : s → Ω)) →ₐ[K] ℂ :=
    (IntermediateField.val _).comp (hv.aevalEquivField.toAlgHom.comp hs.1.reprField)
  have halg := hs.isAlgebraic_field
  obtain ⟨φ, -⟩ := IntermediateField.exists_algHom_of_splits' f
    (fun (x : Ω) => ⟨(Algebra.IsAlgebraic.isAlgebraic
      (R := IntermediateField.adjoin K (Set.range ((↑) : s → Ω))) x).isIntegral, IsAlgClosed.splits _⟩)
  refine ⟨φ.toRingHom, ?_⟩
  ext x
  exact φ.commutes x

theorem exists_embedding_fractionField :
    ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (T : CDVR), T.FinRes →
      ∀ io : K →+* T.Fr, ∃ ι : T.Fr →+* ℂ, ι.comp io = σ := by
  intro K _ _ σ T hT io
  haveI : Finite (ResidueField T.V) := hT
  have hV := mk_le_continuum_of_finite_residueField T.V
  have hF : #T.Fr ≤ 𝔠 := by
    rw [show #T.Fr = #T.V from IsFractionRing.cardinalMk T.V T.Fr]
    exact hV
  exact @exists_embedding_of_mk_le_continuum K T.Fr _ _ _ io.toAlgebra hF σ

end GlobalTheory.ComplexEmbedding
end

section

open Formalism.L2.Pj

open IsLocalRing

namespace GlobalTheory

theorem isIntegral_adjoin_of_forall_cdvr (K Ω : Type) [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] (gens : Finset Ω)
    (hcl : Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) = ⊤) (x : Ω)
    (hx : ∀ (T : CDVR), Countable (IsLocalRing.ResidueField T.V) → ∀ φ : Ω →+* T.Fr,
      (∀ k : K, φ (algebraMap K Ω k) ∈ (algebraMap T.V T.Fr).range) →
      (∀ g ∈ gens, φ g ∈ (algebraMap T.V T.Fr).range) → φ x ∈ (algebraMap T.V T.Fr).range) :
    IsIntegral (Algebra.adjoin K (gens : Set Ω)) x := by
  classical
  set A := Algebra.adjoin K (gens : Set Ω) with hAdef

  have hfrac : ∀ z : Ω, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ z * b = a := by
    intro z
    have hz : z ∈ Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) := hcl ▸ trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Subfield.mem_closure_iff.mp hz
    have hc : Subring.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) = A.toSubring :=
      (Algebra.adjoin_eq_ring_closure _).symm
    rw [hc] at ha hb
    rcases eq_or_ne b 0 with rfl | hb0
    · exact ⟨0, A.zero_mem, 1, A.one_mem, one_ne_zero, by simp⟩
    · exact ⟨a, ha, b, hb, hb0, div_mul_cancel₀ a hb0⟩

  have hKc : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  have hΩc : Countable Ω := by
    have hs : (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)).Countable :=
      (Set.countable_range _).union gens.finite_toSet.countable
    have h1 : Cardinal.mk (Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω))) ≤
        Cardinal.aleph0 :=
      (Subfield.cardinalMk_closure_le_max _).trans
        (max_le (Cardinal.mk_le_aleph0_iff.2 hs.to_subtype) le_rfl)
    have h2 := Cardinal.mk_le_aleph0_iff.1 h1
    rw [hcl] at h2
    exact Function.Injective.countable (f := fun (z : Ω) => (⟨z, trivial⟩ : (⊤ : Subfield Ω)))
      fun a b h => congrArg Subtype.val h

  have hAft : Algebra.FiniteType K A := .adjoin_of_finite gens.finite_toSet
  have hAn : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  have hess : Algebra.EssFiniteType A Ω := by
    refine (Algebra.essFiniteType_iff A Ω).mpr ⟨∅, fun z => ?_⟩
    obtain ⟨a, ha, b, hb, hb0, hab⟩ := hfrac z
    simp only [Finset.coe_empty, Algebra.adjoin_empty, Algebra.mem_bot]
    exact ⟨b, ⟨⟨b, hb⟩, rfl⟩, isUnit_iff_ne_zero.mpr hb0, ⟨⟨a, ha⟩, hab.symm⟩⟩
  by_contra hni
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hni isIntegral_zero

  letI := invertibleOfNonzero (inv_ne_zero hx0)
  let B := Algebra.adjoin A {x⁻¹}
  let xinv : B := ⟨x⁻¹, Algebra.subset_adjoin rfl⟩
  have hne : (⊥ : Ideal A).map (algebraMap A B) ⊔ Ideal.span {xinv} ≠ ⊤ := by
    intro heq
    obtain ⟨p, hp, hpx⟩ := Algebra.exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top
      x⁻¹ (⊥ : Ideal A) bot_ne_top heq
    have hm : p.Monic := by
      rw [Ideal.mem_bot, sub_eq_zero] at hp
      exact hp
    rw [invOf_eq_inv, inv_inv] at hpx
    exact hni ⟨p, hm, by rw [← Polynomial.aeval_def, hpx]⟩
  obtain ⟨W, hW, hW'⟩ := Ideal.image_subset_nonunits_valuationSubring (A := B.toSubring) _ hne
  have hxW : x⁻¹ ∈ W.nonunits := hW' ⟨xinv, Ideal.mem_sup_right (Ideal.subset_span rfl), rfl⟩

  obtain ⟨V, hV, hAV, -, hxV⟩ := exists_discreteValuationSubring_of_valuationSubring (R := A)
    W (fun r => hW (B.algebraMap_mem r)) (s := ∅) (t := {x⁻¹}) Set.finite_empty
    (Set.finite_singleton _) (by simp) (by simpa using hxW) ⟨x⁻¹, rfl, inv_ne_zero hx0⟩
  have hxV' : x⁻¹ ∈ V.nonunits := hxV _ rfl
  have hKV : ∀ k : K, algebraMap K Ω k ∈ V := fun k => hAV (algebraMap K A k)
  have hgV : ∀ g ∈ gens, g ∈ V := fun g hg => hAV ⟨g, Algebra.subset_adjoin hg⟩

  let ι := algebraMap V (AdicCompletion (maximalIdeal V) V)
  have hch : CharZero (AdicCompletion (maximalIdeal V) V) :=
    (RingHom.charZero_iff (ι.comp ((algebraMap K Ω).codRestrict V hKV)).injective).1 inferInstance
  let T : CDVR := { V := AdicCompletion (maximalIdeal V) V, ch0 := hch }
  have hVc : Countable V := Subtype.countable
  have hres : Countable (ResidueField T.V) := by
    have hsurj : Function.Surjective ((residue T.V).comp ι) := by
      intro t0
      obtain ⟨t, rfl⟩ := residue_surjective t0
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
        (AdicCompletion.evalₐ (maximalIdeal V) 1 t)
      refine ⟨r, ?_⟩
      change residue T.V (ι r) = residue T.V t
      change Ideal.Quotient.mk _ (ι r) = Ideal.Quotient.mk _ t
      rw [Ideal.Quotient.eq]
      intro hu
      have hnt : Nontrivial (V ⧸ maximalIdeal V ^ 1) := by
        rw [pow_one]; infer_instance
      have h1 := hu.map (AdicCompletion.evalₐ (maximalIdeal V) 1)
      rw [map_sub] at h1
      change IsUnit ((AdicCompletion.evalₐ (maximalIdeal V) 1) (AdicCompletion.of _ _ r) - _) at h1
      rw [AdicCompletion.evalₐ_of, hr, sub_self] at h1
      exact not_isUnit_zero h1
    exact hsurj.countable
  have hg : Function.Injective ((algebraMap T.V T.Fr).comp ι) :=
    (IsFractionRing.injective T.V T.Fr).comp (algebraMap_adicCompletion_injective_of_dvr V)
  let φ : Ω →+* T.Fr := IsFractionRing.lift (A := V) hg
  have hφ : ∀ v : V, φ v = algebraMap T.V T.Fr (ι v) := fun v => IsFractionRing.lift_algebraMap hg v
  obtain ⟨t, ht⟩ := hx T hres φ (fun k => ⟨ι ⟨_, hKV k⟩, (hφ ⟨_, hKV k⟩).symm⟩)
    (fun g hg' => ⟨ι ⟨g, hgV g hg'⟩, (hφ ⟨g, hgV g hg'⟩).symm⟩)
  let y : V := ⟨x⁻¹, V.nonunits_subset hxV'⟩
  have h1 : algebraMap T.V T.Fr (t * ι y) = 1 := by
    rw [map_mul, ht, ← hφ y]
    change φ x * φ x⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hx0, map_one]
  have h2 : t * ι y = 1 := IsFractionRing.injective T.V T.Fr (h1.trans (map_one _).symm)
  have h3 : IsUnit (ι y) := isUnit_iff_exists_inv.mpr ⟨t, by rw [mul_comm]; exact h2⟩
  exact (ValuationSubring.coe_mem_nonunits_iff (a := y)).mp hxV' (isUnit_of_map_unit ι y h3)

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.L2.Pj IsLocalRing

namespace GlobalTheory.GaussPoint

theorem C_dvd_iff {V : Type*} [CommRing V] (a : V) (f : PowerSeries V) :
    PowerSeries.C a ∣ f ↔ ∀ n, a ∣ PowerSeries.coeff n f := by
  constructor
  · rintro ⟨g, rfl⟩ n
    rw [PowerSeries.coeff_C_mul]
    exact dvd_mul_right _ _
  · intro h
    choose c hc using h
    refine ⟨PowerSeries.mk c, ?_⟩
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc]

theorem isPrime_span_C {V : Type*} [CommRing V] {a : V} (ha : Prime a) :
    (Ideal.span {(PowerSeries.C a : PowerSeries V)}).IsPrime := by
  have h1 : (Ideal.span {a}).IsPrime := (Ideal.span_singleton_prime ha.ne_zero).2 ha
  have h2 : Ideal.span {(PowerSeries.C a : PowerSeries V)} =
      RingHom.ker (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {a}))) := by
    ext f
    rw [Ideal.mem_span_singleton, C_dvd_iff, RingHom.mem_ker, PowerSeries.ext_iff]
    refine forall_congr' fun n => ?_
    rw [PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rw [h2]
  exact RingHom.ker_isPrime _

section Val

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
  [Algebra V K] [IsFractionRing V K]

theorem valV_irreducible {π : V} (hπ : Irreducible π) :
    valV V (algebraMap V K π) = WithZero.exp (-1 : ℤ) := by
  rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton _ hπ.ne_zero hπ.maximalIdeal_eq

theorem valV_unit {u : V} (hu : IsUnit u) : valV V (algebraMap V K u) = 1 := by
  rw [valV, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
  exact fun h => h hu

theorem vV_map_eq {V' K' : Type} [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V']
    [Field K'] [Algebra V' K'] [IsFractionRing V' K'] (f : V →+* V') (i : K →+* K')
    (hi : ∀ a, i (algebraMap V K a) = algebraMap V' K' (f a)) {π : V} (hπ : Irreducible π)
    (hπ' : Irreducible (f π)) (x : K) : vV V' (i x) = vV V x := by
  have key : ∀ a : V, valV V' (i (algebraMap V K a)) = valV V (algebraMap V K a) := by
    intro a
    by_cases ha : a = 0
    · simp [ha]
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    rw [hi]
    simp only [map_mul, map_pow]
    rw [valV_unit u.isUnit, valV_unit (u.isUnit.map f), valV_irreducible hπ, valV_irreducible hπ']
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := V) x
  simp only [vV, map_div₀, key]

end Val

theorem exists_gaussPoint (T : CDVR) (ϖ : T.V) (hϖ : Irreducible ϖ) :
    ∃ (T' : CDVR) (ev : PowerSeries T.V →+* T'.V) (i : T.Fr →+* T'.Fr), Function.Injective ev ∧
      IsUnit (ev PowerSeries.X) ∧ (∀ s, ev (PowerSeries.C ϖ) ∣ ev s → PowerSeries.C ϖ ∣ s) ∧
      (∀ a, i (algebraMap T.V T.Fr a) = algebraMap T'.V T'.Fr (ev (PowerSeries.C a))) ∧
      ∀ x, vV T'.V (i x) = vV T.V x := by
  let R := PowerSeries T.V
  let P : Ideal R := Ideal.span {(PowerSeries.C ϖ : PowerSeries T.V)}
  haveI hP : P.IsPrime := isPrime_span_C hϖ.prime
  let L := Localization.AtPrime P
  have hinj : Function.Injective (algebraMap R L) :=
    IsLocalization.injective L P.primeCompl_le_nonZeroDivisors
  have hm : maximalIdeal L = Ideal.span {algebraMap R L (PowerSeries.C ϖ)} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]
  have hC0 : (PowerSeries.C ϖ : R) ≠ 0 := fun h =>
    hϖ.ne_zero (PowerSeries.C_injective (h.trans (map_zero _).symm))
  have hn : ¬ IsNilpotent (algebraMap R L (PowerSeries.C ϖ)) := by
    rw [IsNilpotent.map_iff hinj]
    exact fun h => hC0 h.eq_zero
  obtain ⟨_, hdvr, hirr⟩ := isDiscreteValuationRing_of_maximalIdeal_eq_span hm hn
  let S := AdicCompletion (maximalIdeal L) L
  let ev : R →+* S := (algebraMap L S).comp (algebraMap R L)
  have hev : Function.Injective ev :=
    (algebraMap_adicCompletion_injective_of_dvr L).comp hinj
  have hirr' : Irreducible (ev (PowerSeries.C ϖ)) :=
    irreducible_algebraMap_adicCompletion_of_dvr hirr
  have hunit : ∀ s : R, ¬ PowerSeries.C ϖ ∣ s → IsUnit (ev s) := fun s hs =>
    (IsLocalization.map_units L (⟨s, fun h => hs (Ideal.mem_span_singleton.1 h)⟩ :
      P.primeCompl)).map (algebraMap L S)
  haveI : CharZero S := charZero_of_injective_ringHom
    (f := ev.comp PowerSeries.C) (hev.comp PowerSeries.C_injective)
  let T' : CDVR := { V := S }
  let g : T.V →+* T'.Fr := (algebraMap T'.V T'.Fr).comp (ev.comp PowerSeries.C)
  have hg : Function.Injective g :=
    (IsFractionRing.injective T'.V T'.Fr).comp (hev.comp PowerSeries.C_injective)
  have hi : ∀ a, IsFractionRing.lift (K := T.Fr) hg (algebraMap T.V T.Fr a) =
      algebraMap T'.V T'.Fr (ev (PowerSeries.C a)) := fun a => IsFractionRing.lift_algebraMap hg a
  refine ⟨T', ev, IsFractionRing.lift hg, hev, hunit _ ?_, fun s hs => ?_, hi,
    vV_map_eq (ev.comp PowerSeries.C) _ hi hϖ hirr'⟩
  · rw [C_dvd_iff]
    intro h
    have h1 := h 1
    rw [PowerSeries.coeff_one_X] at h1
    exact hϖ.not_isUnit (isUnit_of_dvd_one h1)
  · by_contra h
    exact hirr'.not_isUnit (isUnit_of_dvd_unit hs (hunit s h))

end GlobalTheory.GaussPoint
end
