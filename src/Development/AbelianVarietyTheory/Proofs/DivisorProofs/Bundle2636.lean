module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenOfFrames
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1772
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle672
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsPrincipalIdealRingOfIsLocalization
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle912
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle067
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle676
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle399
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2618
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2619
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivMemOfForallPowSuccDivPowMem
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102

@[expose] public section

section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.ConeInterior

section Help

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X]

theorem exists_nat_comb {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : IsCone bar φ γ)
    {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X) {c : Fin m → ℝ} (hc : ∀ i, 0 ≤ c i)
    (h : toReal β = ∑ i, c i • toReal (γ i)) : ∃ n : Fin m → ℕ, β = ∑ i, n i • γ i := by
  classical
  obtain ⟨f, hf⟩ := hγ.basis.exists_dual
  have hz : ∀ i, c i = (f i ⟨β, hβ⟩ : ℤ) := fun i => by
    have h0 : ∑ o : Option (Fin m), (Option.elim o (-1) c) • toReal ((balForms bar X).subtype
        (Option.elim o (⟨β, hβ⟩ : balForms bar X) fun k => ⟨γ k, hγ.mem k⟩)) = 0 := by
      rw [Fintype.sum_option]
      simp only [Option.elim_none, Option.elim_some, Submodule.subtype_apply, h, neg_one_smul, neg_add_cancel]
    have := sum_mul_eq_zero_of_sum_toReal Subtype.val_injective (f i) h0
    rw [Fintype.sum_option] at this
    simp only [Option.elim_none, Option.elim_some, hf] at this
    simp at this
    linarith
  have hn : ∀ i, ∃ n : ℕ, c i = n := fun i => by
    have h1 : (0 : ℤ) ≤ f i ⟨β, hβ⟩ := by exact_mod_cast (hz i ▸ hc i : (0 : ℝ) ≤ (f i ⟨β, hβ⟩ : ℤ))
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h1
    exact ⟨n, by rw [hz i, hn, Int.cast_natCast]⟩
  choose n hn using hn
  refine ⟨n, LinearMap.ext₂ fun a b => ?_⟩
  have := LinearMap.congr_fun₂ h a b
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul, hn, nsmul_eq_mul] at this ⊢
  exact_mod_cast this

theorem exists_pos_comb (hP : IsPolFanOn bar φ X) {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X)
    (hp : toReal β ∈ psdCone (bar := bar) (X := X)) :
    ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (cf : Fin m → ℕ),
      IsCone bar φ γ ∧ (∀ j, 0 < cf j) ∧ β = ∑ j, cf j • γ j := by
  classical
  obtain ⟨m, γ, c, hγ, hc, h⟩ := hP.cover _ hp
  obtain ⟨n, hn⟩ := exists_nat_comb hγ hβ hc h
  let S : Finset (Fin m) := Finset.univ.filter fun i => 0 < n i
  let s : Fin S.card ↪ Fin m := (S.orderEmbOfFin rfl).toEmbedding
  have hs : Finset.univ.map s = S := Finset.map_orderEmbOfFin_univ S rfl
  refine ⟨S.card, fun i => γ (s i), fun i => n (s i), hP.face _ _ γ s hγ, fun j => ?_, ?_⟩
  · exact (Finset.mem_filter.1 (S.orderEmbOfFin_mem rfl j)).2
  · rw [hn, ← Finset.sum_map Finset.univ s fun i => n i • γ i, hs]
    refine (Finset.sum_subset (Finset.subset_univ S) fun i _ hi => ?_).symm
    have : n i = 0 := by simpa [S] using hi
    rw [this, zero_smul]

end Help

theorem exists_pos_comb_int : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ r : ℕ, r ≤ g → ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → toReal b ∈ psdCone (bar := (id : ℤ → ℤ)) (X := (Fin r → ℤ)) → ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ)) (cf : Fin m → ℕ), IsCone id φ γ ∧ (∀ j, 0 < cf j) ∧ b = ∑ j, cf j • γ j := by
  intro g φ hφ r hr b hb hp
  exact exists_pos_comb (hφ (Fin r → ℤ) (by simpa using hr)) (mem_balForms_int.2 hb) hp

end GlobalTheory.ConeInterior
end

section

noncomputable section

open IsLocalRing GlobalTheory.Toroidal

namespace GlobalTheory.MonoVal

theorem eq_span_monomial_of_forall_cdvr (k : Type) [Field k] [CharZero k] (m e : ℕ) (I : Ideal (ChartRing k m e))
    (a : Fin m → ℕ)
    (h : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ ψ : ChartRing k m e →+* W,
      Function.Injective ψ → IsLocalHom ψ → I.map ψ = Ideal.span {ψ (∏ i, bdParam k m e i ^ a i)}) :
    I = Ideal.span {∏ i, bdParam k m e i ^ a i} := by
  set q : ChartRing k m e := ∏ i, bdParam k m e i ^ a i with hqdef
  haveI : CharZero (ChartRing k m e) := (MvPowerSeries.constantCoeff : ChartRing k m e →+* k).charZero
  obtain ⟨hN, hIC, -, -⟩ := GlobalTheory.ChartCone.isCN_chartRing k m e
  haveI := hN
  haveI := hIC
  have hX : ∀ j : Fin m ⊕ Fin e, (MvPowerSeries.X j : ChartRing k m e) ≠ 0 := by
    intro j hj
    have := congrArg (MvPowerSeries.coeff (Finsupp.single j 1)) hj
    simp [MvPowerSeries.coeff_X] at this
  have hq0 : q ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hX _)
  have loc_of : ∀ {V : Type} [CommRing V] [IsLocalRing V] (φ : ChartRing k m e →+* V),
      (maximalIdeal V).comap φ = maximalIdeal (ChartRing k m e) → IsLocalHom φ := by
    intro V _ _ φ hφ
    refine ⟨fun x hx => ?_⟩
    by_contra hnu
    have hx' : x ∈ maximalIdeal (ChartRing k m e) := hnu
    rw [← hφ, Ideal.mem_comap] at hx'
    exact hx' hx

  have hle : I ≤ Ideal.span {q} := by
    intro f hf
    rw [Ideal.mem_span_singleton]
    refine GlobalTheory.ValCrit.dvd_of_forall_cdvr _ f q hq0 fun V _ _ _ φ hV hinj hφ => ?_
    have hm := h V hV φ hinj (loc_of φ hφ)
    rw [← Ideal.mem_span_singleton, ← hm]
    exact Ideal.mem_map_of_mem φ hf
  refine le_antisymm hle ?_
  rw [Ideal.span_le, Set.singleton_subset_iff]
  by_contra hqI
  let I' : Ideal (ChartRing k m e) := Submodule.comap (LinearMap.mulLeft (ChartRing k m e) q) I
  have hmemI' : ∀ g, g ∈ I' ↔ q * g ∈ I := fun g => Iff.rfl
  have key : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ψ : ChartRing k m e →+* V),
      GlobalTheory.LN.CDvr V → Function.Injective ψ → IsLocalHom ψ → False := by
    intro V _ _ _ ψ hV hinj hψ
    have hmap := h V hV ψ hinj hψ
    have hI : I = Ideal.span {q} * I' := by
      apply le_antisymm
      · intro f hf
        obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.1 (hle hf)
        exact Ideal.mem_span_singleton_mul.2 ⟨g, (hmemI' g).2 (by rwa [mul_comm]), mul_comm _ _⟩
      · rw [Ideal.span_singleton_mul_le_iff]
        intro z hz
        exact (hmemI' z).1 hz
    have hψq : ψ q ≠ 0 := (map_ne_zero_iff ψ hinj).2 hq0
    have htop : Ideal.map ψ I' = ⊤ := by
      have h2 : Ideal.span {ψ q} * Ideal.map ψ I' = Ideal.span {ψ q} * ⊤ := by
        have h3 : Ideal.map ψ (Ideal.span {q} * I') = Ideal.span {ψ q} * Ideal.map ψ I' := by
          rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton]
        rw [Ideal.mul_top, ← h3, ← hI, hmap]
      exact (Ideal.span_singleton_mul_right_inj hψq).1 h2
    have hI'ne : I' ≠ ⊤ := by
      intro ht
      apply hqI
      have h1 : (1 : ChartRing k m e) ∈ I' := ht ▸ Submodule.mem_top
      simpa using (hmemI' 1).1 h1
    have hle' : Ideal.map ψ I' ≤ maximalIdeal V := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have hx' := IsLocalRing.le_maximalIdeal hI'ne hx
      rw [mem_maximalIdeal, mem_nonunits_iff] at hx'
      rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
      exact fun hu => hx' (isUnit_of_map_unit ψ x hu)
    exact (IsLocalRing.maximalIdeal.isMaximal V).ne_top (top_le_iff.1 (htop ▸ hle'))
  rcases isEmpty_or_nonempty (Fin m ⊕ Fin e) with hσ | hne
  ·
    let ψ0 : ChartRing k m e →+* PowerSeries k :=
      (PowerSeries.C : k →+* PowerSeries k).comp (MvPowerSeries.constantCoeff : ChartRing k m e →+* k)
    have hc : ∀ f : ChartRing k m e, f = MvPowerSeries.C (MvPowerSeries.constantCoeff f) := by
      intro f
      ext n
      have hn : n = 0 := Subsingleton.elim _ _
      subst hn
      simp
    have hinj : Function.Injective ψ0 := by
      intro f g hfg
      have h1 : MvPowerSeries.constantCoeff f = MvPowerSeries.constantCoeff g := by
        simpa [ψ0] using congrArg PowerSeries.constantCoeff hfg
      rw [hc f, hc g, h1]
    have hloc : IsLocalHom ψ0 := by
      refine ⟨fun f hf => ?_⟩
      rw [MvPowerSeries.isUnit_iff_constantCoeff]
      have h1 : IsUnit (PowerSeries.constantCoeff (ψ0 f)) := hf.map _
      simpa [ψ0] using h1
    exact key (PowerSeries k) ψ0 (GlobalTheory.FrameGen.cDvr_powerSeries k) hinj hloc
  · obtain ⟨j⟩ := hne
    have hdvd : (MvPowerSeries.X j : ChartRing k m e) ∣ 1 :=
      GlobalTheory.ValCrit.dvd_of_forall_cdvr _ 1 _ (hX j) fun V _ _ _ φ hV hinj hφ =>
        (key V φ hV hinj (loc_of φ hφ)).elim
    have hu := isUnit_of_dvd_one hdvd
    rw [MvPowerSeries.isUnit_iff_constantCoeff] at hu
    simp at hu

end GlobalTheory.MonoVal
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DvrDiv

theorem dvd_of_forall_cDvr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (a b : R), b ≠ 0 → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ φ : R →+* V, Function.Injective φ → φ b ∣ φ a) → b ∣ a := by
  intro R _ _ _ _ _ a b hb h
  classical
  by_cases ha : a = 0
  · exact ha ▸ dvd_zero b
  let K := FractionRing R
  obtain ⟨h1, h2, -⟩ := GlobalTheory.normal_domain_height_one.{0, 0, 0} R K
  have hbK : algebraMap R K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb
  suffices hmem : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      algebraMap R K a / algebraMap R K b ∈ primeLocalSubalgebra K p by
    obtain ⟨r, hr⟩ := (h2 (algebraMap R K a / algebraMap R K b)).2 hmem
    refine ⟨r, IsFractionRing.injective R K ?_⟩
    rw [map_mul, hr, mul_div_cancel₀ _ hbK]
  intro p _ hp
  obtain ⟨-, hD, -⟩ := h1 p hp
  let D := primeLocalSubalgebra K p
  haveI : IsDiscreteValuationRing D := hD
  let W := AdicCompletion (IsLocalRing.maximalIdeal D) D
  let iW : D →+* W := algebraMap D W
  let φ : R →+* W := iW.comp (algebraMap R D)
  have hRD : Function.Injective (algebraMap R D) := fun x y hxy =>
    IsFractionRing.injective R K (congrArg Subtype.val hxy)
  have hφ : Function.Injective φ := (algebraMap_adicCompletion_injective_of_dvr D).comp hRD
  haveI : CharZero W := (RingHom.charZero_iff hφ).1 inferInstance
  have hW : GlobalTheory.LN.CDvr W := ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨t, ht⟩ := h W hW φ hφ
  have hdvd : algebraMap R D b ∣ algebraMap R D a := by
    rcases ValuationRing.dvd_total (algebraMap R D b) (algebraMap R D a) with hd | ⟨c, hc⟩
    · exact hd
    have ha' : φ a ≠ 0 := (map_ne_zero_iff _ hφ).mpr ha
    have e : φ a * (iW c * t) = φ a * 1 := by
      rw [_root_.mul_one]
      calc φ a * (iW c * t) = iW (algebraMap R D a * c) * t := by
            rw [map_mul, _root_.mul_assoc]; rfl
        _ = φ a := by rw [← hc]; exact ht.symm
    have hu : IsUnit (iW c) := isUnit_iff_exists_inv.mpr ⟨t, mul_left_cancel₀ ha' e⟩
    obtain ⟨u, rfl⟩ := isUnit_of_map_unit iW c hu
    exact ⟨↑u⁻¹, by rw [hc, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩
  obtain ⟨c, hc⟩ := hdvd
  have hcK : algebraMap R K a = algebraMap R K b * (c : K) := congrArg Subtype.val hc
  rw [hcK, mul_div_cancel_left₀ _ hbK]
  exact c.2

end GlobalTheory.DvrDiv
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.DvrDom

theorem exists_cdvr_dominating : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R], ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (φ : R →+* V), GlobalTheory.LN.CDvr V ∧ Function.Injective φ ∧ IsLocalHom φ := by
  intro R _ _ _ _ _
  by_cases hR : IsField R
  · letI : Field R := hR.toField
    have hC : Function.Injective (PowerSeries.C (R := R)) := PowerSeries.C_injective
    have : CharZero (PowerSeries R) := charZero_of_injective_ringHom hC
    have hc : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries R)) (PowerSeries R) := by
      first
      | infer_instance
      | (rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance)
    have hl : IsLocalHom (PowerSeries.C (R := R)) := by
      constructor
      intro a ha
      by_cases h0 : a = 0
      · subst h0; simp at ha
      · exact isUnit_iff_ne_zero.mpr h0
    exact ⟨PowerSeries R, inferInstance, inferInstance, inferInstance, PowerSeries.C (R := R),
      (GlobalTheory.LN.cDvr_iff _).2 ⟨inferInstance, hc, this⟩, hC, hl⟩
  · obtain ⟨O, _, hO, hO', hO'', φ, h1, h2⟩ := GlobalTheory.exists_complete_discreteValuationRing_dominating (R := R) hR
    have : CharZero O := charZero_of_injective_ringHom h1
    exact ⟨O, inferInstance, hO, inferInstance, φ, (GlobalTheory.LN.cDvr_iff _).2 ⟨hO', hO'', this⟩, h1, h2⟩

end GlobalTheory.DvrDom
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lineBundleIso_pow_multiple_degree_descends_normal : ∀ (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra k Ω'] [IsScalarTower k Ω Ω'] [FiniteDimensional Ω Ω'] (M' : RatModel k Ω') (π : M'.Z ⟶ M.Z) (A B : LB M.Z) (d : ℕ), Geo.Tor.IsNormalScheme M.Z → IsFinite π → M'.pt ≫ π = spMap (algebraMap Ω Ω') ≫ M.pt → A.IsLB → B.IsLB → Module.finrank Ω Ω' ∣ d → LBIso (A.pull π) (B.pull π) → LBIso (lbPow A d) (lbPow B d) := by
  first | exact @GlobalTheory.UMin.NormIso.lbIso_lbPow_of_pull | exact GlobalTheory.UMin.NormIso.lbIso_lbPow_of_pull | (intros; apply GlobalTheory.UMin.NormIso.lbIso_lbPow_of_pull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

def openRatModel {k : Type} [Field k] {X : Scheme.{0}} (s : X ⟶ Sp k) (U : X.Opens) [IsIntegral U.toScheme]
    (hsep : IsSeparated s) (hlft : LocallyOfFiniteType s) (hqc : QuasiCompact (U.ι ≫ s)) :
    letI : Algebra k U.toScheme.functionField :=
      (Spec.preimage (U.toScheme.fromSpecStalk (genericPoint U.toScheme) ≫ U.ι ≫ s)).hom.toAlgebra
    RatModel k U.toScheme.functionField :=
  letI : Algebra k U.toScheme.functionField :=
    (Spec.preimage (U.toScheme.fromSpecStalk (genericPoint U.toScheme) ≫ U.ι ≫ s)).hom.toAlgebra
  { Z := U.toScheme
    s := U.ι ≫ s
    sep := inferInstance
    lft := inferInstance
    qc := hqc
    pt := U.toScheme.fromSpecStalk (genericPoint U.toScheme)
    pt_s := by
      unfold spMap
      rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
    gen := by
      refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, Scheme.fromSpecStalk_closedPoint⟩, ?_⟩
      rintro _ ⟨w, rfl⟩
      have : w = IsLocalRing.closedPoint U.toScheme.functionField :=
        Subsingleton.elim (α := PrimeSpectrum U.toScheme.functionField) _ _
      rw [this]
      exact Scheme.fromSpecStalk_closedPoint
    onto := fun x => by
      obtain ⟨V, h, a, rfl⟩ := U.toScheme.presheaf.germ_exist (x := genericPoint U.toScheme) x
      exact ⟨V, a, ⟨_, h⟩, GlobalTheory.FlagBundle.valF_fromSpecStalk h a⟩ }

theorem lbIso_of_ratModels : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) (s : X ⟶ Sp k) (A B : LB X), Geo.Tor.IsNormalScheme X → IsSeparated s → LocallyOfFiniteType s → QuasiCompact s → A.IsLB → B.IsLB → (∀ (Ω : Type) [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (io : M.Z ⟶ X), IsOpenImmersion io → io ≫ s = M.s → LBIso (A.pull io) (B.pull io)) → LBIso A B := by
  intro k _ _ X s A B hN hsep hlft hqc hA hB hM
  haveI : GlobalTheory.IsNormalScheme X := GlobalTheory.IsNormalScheme.of_pred hN
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  refine GlobalTheory.DisjointCoverLB.lbIso_of_disjoint_cover X (irreducibleComponents X) GlobalTheory.IsNormalScheme.component
    (fun a b y ha hb => Subtype.ext (GlobalTheory.IsNormalScheme.eq_of_mem_irreducibleComponents a.2 b.2 ha hb))
    (fun y => ⟨⟨_, irreducibleComponent_mem_irreducibleComponents y⟩, mem_irreducibleComponent⟩) A B hA hB ?_
  intro Z
  let U := GlobalTheory.IsNormalScheme.component Z
  letI : Algebra k U.toScheme.functionField :=
    (Spec.preimage (U.toScheme.fromSpecStalk (genericPoint U.toScheme) ≫ U.ι ≫ s)).hom.toAlgebra
  have hio : IsOpenImmersion U.ι := by infer_instance
  exact hM _ (openRatModel s U hsep hlft inferInstance) U.ι hio rfl

end GlobalTheory.UMin
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O
open GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh

namespace GlobalTheory.DivSec

theorem exists_affine_germ_eq : ∀ (Y : Scheme.{0}) (y : Y) (n : ℕ) (r : Fin n → Y.presheaf.stalk y),
    ∃ (V : Y.affineOpens) (hy : y ∈ V.1) (F : Fin n → Γ(Y, V.1)), ∀ j, Y.presheaf.germ V.1 y hy (F j) = r j := by
  intro Y y n r
  classical
  choose U hU s hs using fun j => TopCat.Presheaf.germ_exist Y.presheaf (r j)
  have hmem : ∀ t : Finset (Fin n), y ∈ t.inf U := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      rw [Finset.inf_insert]
      exact ⟨hU a, ih⟩
  obtain ⟨V, hV, hyV, hVO⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (hmem Finset.univ)
  have hle : ∀ j, V ≤ U j := fun j => le_trans hVO (Finset.inf_le (Finset.mem_univ j))
  refine ⟨⟨V, hV⟩, hyV, fun j => resG Y (hle j) (s j), fun j => ?_⟩
  rw [← hs j]
  exact Y.presheaf.germ_res_apply (homOfLE (hle j)) y hyV (s j)

theorem isCompatChart_of_holAlong : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (n : ℕ)
    (B : FinHolAtlas n (CxPts p σ)), IsAlgAtlas B → ∀ (e : OpenPartialHomeomorph (CxPts p σ) (Fin n → ℂ)),
    (∀ j, HolAlong e.source fun x => e x j) → IsHolTo e.target (fun z => (e.symm z).1) → IsCompatChart B e := by
  intro k _ Y p σ n B hB e hhol hsymm j
  obtain ⟨c, hcj⟩ := hB j
  rw [hcj]
  constructor
  · refine (c.analyticOnNhd_finChart_iff e.open_source e).2 ?_
    refine differentiableOn_pi.2 fun i => ?_
    have hO := GlobalTheory.ChartGlue.isOpen_over c.e e.open_source
    exact hhol i _ _ c.e.symm hO (GlobalTheory.ShFam.Hor.Sec.isHolTo_symm c hO Set.inter_subset_left) (fun b hb => hb.2)
  · have hO : IsOpen (e.target ∩ e.symm ⁻¹' c.finChart.source) := e.isOpen_inter_preimage_symm c.finChart.open_source
    refine (SCV.analyticOnNhd_iff_differentiableOn hO).2 ?_
    intro b hb
    have h1 := GlobalTheory.TrueCx.TorHolo.differentiableAt_chart e.open_target hsymm c hb.1 hb.2
    exact ((EuclideanSpace.equiv (Fin n) ℂ).differentiable.differentiableAt.comp b h1).differentiableWithinAt

end GlobalTheory.DivSec
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.algebraise_system_in_algebraising_closedSubscheme : ∀ (R : Type) [CommRing R] (I : Ideal R) (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (a : W.IdealSheafData), Alg (a.subschemeι ≫ f) I → ∀ t : ℕ → W.IdealSheafData, IsSystem f I t → (∀ e, IsProper ((t e).subschemeι ≫ f)) → ∃ T : W.IdealSheafData, IsProper (T.subschemeι ≫ f) ∧ Reduces f I T (fun e => t e ⊔ a) := by
  first | exact @GlobalTheory.FormalAlg.alg_of_closedSubscheme | exact GlobalTheory.FormalAlg.alg_of_closedSubscheme | (intros; apply GlobalTheory.FormalAlg.alg_of_closedSubscheme <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf : ∀ (R : Type) [CommRing R] (J : Ideal R) (W Y : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (b : Y ⟶ W) (q : Y ⟶ Spec (CommRingCat.of (R ⧸ J))), IsPullback b q f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) → IsClosedImmersion b ∧ b.ker = baseIdeal f J ∧ ∀ V : W.Opens, IsAffineOpen V → Function.Surjective (b.app V).hom ∧ RingHom.ker (b.app V).hom = J.map (cst f V) := by
  first | exact @GlobalTheory.FormalAlg.baseChange_quotient | exact GlobalTheory.FormalAlg.baseChange_quotient | (intros; apply GlobalTheory.FormalAlg.baseChange_quotient <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.idealSheaf_le_of_le_on_reductions_jacobson : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (V : Scheme.{0}) [IsLocallyNoetherian V] (p : V ⟶ Spec (CommRingCat.of R)) (a a' : V.IdealSheafData), UniversallyClosed (a'.subschemeι ≫ p) → (∀ e : ℕ, a ≤ a' ⊔ baseIdeal p (I ^ (e + 1))) → a ≤ a' := by
  first | exact @GlobalTheory.FormalAlg.le_of_le_reductions | exact GlobalTheory.FormalAlg.le_of_le_reductions | (intros; apply GlobalTheory.FormalAlg.le_of_le_reductions <;> assumption)
end
