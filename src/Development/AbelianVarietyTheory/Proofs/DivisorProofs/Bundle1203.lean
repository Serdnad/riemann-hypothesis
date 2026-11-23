module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle136
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Mathlib.AlgebraicGeometry.OrderOfVanishing.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle713
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ClosureFromSpecMemCompsH
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

noncomputable section

namespace GlobalTheory.UnrEuler.ConjFac

open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UnrEuler Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors TensorProduct
open Formalism.L2.Host (aboveF)
open GlobalTheory.CuspRep (conjSrc conjPl_conjSrc)

theorem absNorm_conjSrc {E : Type} [Field E] [NumberField E] (c : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) :
    Ideal.absNorm (conjSrc c w).asIdeal = Ideal.absNorm w.asIdeal := by
  rw [(GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc c w)]
  rw [Ideal.absNorm_eq_natCard, Ideal.absNorm_eq_natCard]
  exact Nat.card_congr (Ideal.quotientEquiv (w.asIdeal.comap (RingOfIntegers.mapRingEquiv c)) w.asIdeal
    (RingOfIntegers.mapRingEquiv c)
    (Ideal.map_comap_of_surjective _ (RingEquiv.surjective (RingOfIntegers.mapRingEquiv c)) _).symm).toEquiv

end GlobalTheory.UnrEuler.ConjFac
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory

theorem unitAt_fromSpec_fnOf_iff {X : Scheme.{0}} [IsIntegral X] {V : X.Opens} (hA : IsAffineOpen V)
    (hV : genericPoint X ∈ V) (Q : PrimeSpectrum Γ(X, V)) (r : Γ(X, V)) :
    UnitAt (hA.fromSpec Q) (fnOf V hV r) ↔ r ∉ Q.asIdeal := by
  have hz : hA.fromSpec Q ∈ V := by
    have h : hA.fromSpec Q ∈ Set.range hA.fromSpec := ⟨Q, rfl⟩
    rw [hA.range_fromSpec] at h
    exact h
  rw [unitAt_fnOf_iff hz]
  have h := hA.fromSpec_preimage_basicOpen r
  change Q ∈ hA.fromSpec ⁻¹ᵁ X.basicOpen r ↔ _
  rw [h]
  exact PrimeSpectrum.mem_basicOpen _ _

theorem exists_finite_points_regAt_div_of_affine :
    ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (V : X.Opens), IsAffineOpen V → ∀ (hV : genericPoint X ∈ V) (a : Γ(X, V)), fnOf V hV a ≠ 0 → ∃ T : Set X, T.Finite ∧ ∀ x ∈ V, ∀ τ g : X.functionField, RegAt x τ → (∀ z ∈ T, z ⤳ x → UnitAt z τ) → RegAt x g → RegAt x (g * τ / fnOf V hV a) → RegAt x (g / fnOf V hV a) := by
  intro X _ _ V hA hV a ha
  have : Nonempty V := ⟨⟨_, hV⟩⟩
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hA⟩
  have ha0 : a ≠ 0 := fun h => ha (by rw [h, map_zero])
  obtain ⟨S, hS, H⟩ := exists_finite_primes_dvd_of_dvd_mul_localization Γ(X, V) a ha0
  refine ⟨(fun Q : PrimeSpectrum Γ(X, V) => hA.fromSpec Q) '' S, hS.image _, ?_⟩
  rintro x hx _ _ ⟨τ, rfl⟩ hτ ⟨g, rfl⟩ ⟨c, hc⟩
  set P : PrimeSpectrum Γ(X, V) := hA.primeIdealOf ⟨x, hx⟩ with hP
  letI : Algebra Γ(X, V) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) P.asIdeal := hA.isLocalization_stalk ⟨x, hx⟩
  have hgerm : ∀ r : Γ(X, V), algebraMap (X.presheaf.stalk x) X.functionField
      (algebraMap Γ(X, V) (X.presheaf.stalk x) r) = fnOf V hV r := fun r => algebraMap_germ hx r
  let e : Localization.AtPrime P.asIdeal ≃ₐ[Γ(X, V)] X.presheaf.stalk x :=
    IsLocalization.algEquiv P.asIdeal.primeCompl _ _
  have hd : algebraMap Γ(X, V) (X.presheaf.stalk x) a ∣ g * τ := by
    refine ⟨c, IsFractionRing.injective (X.presheaf.stalk x) X.functionField ?_⟩
    rw [map_mul, map_mul, hgerm, hc, mul_div_cancel₀ _ ha]
  have key := H P (e.symm τ) (e.symm g) ?_ ?_
  · obtain ⟨d, hd⟩ := map_dvd e key
    rw [e.commutes, e.apply_symm_apply] at hd
    exact ⟨d, by rw [hd, map_mul, hgerm, mul_div_cancel_left₀ _ ha]⟩
  · intro Q hQ hQP hm
    have hsp : hA.fromSpec Q ⤳ x := by
      have h := ((PrimeSpectrum.le_iff_specializes Q P).1 hQP).map hA.fromSpec.continuous
      rwa [hP, hA.fromSpec_primeIdealOf] at h
    have hu := hτ _ ⟨Q, hQ, rfl⟩ hsp
    obtain ⟨⟨q, t⟩, hqt⟩ := (IsLocalization.mem_map_algebraMap_iff P.asIdeal.primeCompl _).1 hm
    have h1 := congrArg (fun y => algebraMap (X.presheaf.stalk x) X.functionField (e y)) hqt
    simp only [map_mul, e.commutes, e.apply_symm_apply, hgerm] at h1
    have ht := (unitAt_fromSpec_fnOf_iff hA hV Q t).2 fun h => t.2 (hQP h)
    have h2 := hu.mul ht
    rw [h1] at h2
    exact (unitAt_fromSpec_fnOf_iff hA hV Q q).1 h2 q.2
  · have h := map_dvd e.symm hd
    rwa [e.symm.commutes, map_mul] at h

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

variable {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W] {k : Type} [CommRing k]

theorem functionFieldMap_comp_constFn (p : W ⟶ Sp k) (f : M ⟶ W) [IsDominant f] :
    (functionFieldMap f).comp (Cartier.constFn p) = Cartier.constFn (f ≫ p) := by
  ext a
  simp only [RingHom.comp_apply, Cartier.constFn]
  have h1 := algebraMap_germ (X := W) (U := ⊤) (x := f (genericPoint M)) trivial (algX p ⊤ a)
  have h2 := algebraMap_germ (X := M) (U := ⊤) (x := genericPoint M) trivial (algX (f ≫ p) ⊤ a)
  rw [← h1, ← h2, functionFieldMap_algebraMap]
  congr 1
  have e : f.app ⊤ (algX p ⊤ a) = algX (f ≫ p) ⊤ a := by
    simp only [algX, RingHom.comp_apply, Scheme.Hom.appLE,
      ← CommRingCat.comp_apply, Scheme.Hom.comp_app, Category.assoc]
    rw [f.naturality]
    rfl
  rw [← e]
  exact Scheme.Hom.germ_stalkMap_apply f ⊤ _ trivial _

def ratPull (p : W ⟶ Sp k) (f : M ⟶ W) [IsDominant f] (n : ℕ) :
    RatForms p n →ₛₗ[functionFieldMap f] RatForms (f ≫ p) n :=
  TopForm.formMap n (functionFieldMap f) (functionFieldMap_comp_constFn p f)

end GlobalTheory.EtaleKlt
end
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.RegParPrime

open ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages

theorem exists_mul_eq_of_mem_span {A : Type} [CommRing A] [IsDomain A] (p : Ideal A) [p.IsPrime]
    (R : Type) [CommRing R] [Algebra A R] [IsLocalization.AtPrime R p] {b x : A}
    (h : algebraMap A R x ∈ Ideal.span {algebraMap A R b}) : ∃ t ∉ p, ∃ s, t * x = s * b := by
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h
  obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl (S := R) r
  refine ⟨t, t.2, s, ?_⟩
  apply IsLocalization.injective R (M := p.primeCompl) (Ideal.primeCompl_le_nonZeroDivisors p)
  rw [map_mul, map_mul, ← hr, ← mul_assoc, IsLocalization.mk'_spec']

theorem exists_primeDivisors_of_regularParams : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (y : Y) (U : Y.Opens) (hy : y ∈ U) (c : ℕ) (a : Fin c → Γ(Y, U)), IsRegularLocalRing (Y.presheaf.stalk y) → FinalTheorems.Rsp (Y.presheaf.stalk y) c (fun i => Y.presheaf.germ U y hy (a i)) → ∃ (w : Fin c → Y) (u : Fin c → Y.functionFieldˣ), Function.Injective w ∧ ∀ j, (u j : Y.functionField) = fnOf U (gen_mem hy) (a j) ∧ w j ⤳ y ∧ Order.coheight (w j) = 1 ∧ w j ∉ Y.basicOpen (a j) ∧ Scheme.ord (u j : Y.functionField) (w j) = 1 ∧ ∀ v, v ⤳ y → Order.coheight v = 1 → v ≠ w j → v ∈ Y.basicOpen (a j) := by
  intro Y _ _ y U hy c a hreg hrsp
  obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset hy
  have hVU' : V ≤ U := hVU
  let b : Fin c → Γ(Y, V) := fun i => resG Y hVU' (a i)
  have hgerm : ∀ i, Y.presheaf.germ V y hyV (b i) = Y.presheaf.germ U y hy (a i) := fun i =>
    Y.presheaf.germ_res_apply (homOfLE hVU') y hyV (a i)
  have hrsp' : FinalTheorems.Rsp (Y.presheaf.stalk y) c (fun i => Y.presheaf.germ V y hyV (b i)) := by
    simpa only [hgerm] using hrsp
  haveI := hreg
  obtain ⟨q, hq⟩ := exists_parPrimes hV hyV b hrsp'
  have hprime : ∀ i, Prime (Y.presheaf.germ V y hyV (b i)) :=
    prime_of_regular_params _ hrsp'.1 hrsp'.2
  haveI : Nonempty V := ⟨⟨y, hyV⟩⟩
  haveI : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hb0 : ∀ i, b i ≠ 0 := fun i h => (hprime i).ne_zero (by rw [h, map_zero])
  have hfn : ∀ i, fnOf U (gen_mem hy) (a i) = fnOf V (gen_mem hyV) (b i) := fun i =>
    (fnOf_resG hVU' (gen_mem hyV) (a i)).symm
  have ha0 : ∀ i, fnOf U (gen_mem hy) (a i) ≠ 0 := fun i h =>
    hb0 i (fnOf_injective V (gen_mem hyV) (by rw [← hfn, h, map_zero]))
  have hbas : ∀ i, Y.basicOpen (b i) ≤ Y.basicOpen (a i) := fun i => by
    have := Scheme.basicOpen_res Y (a i) (homOfLE hVU').op
    intro z hz
    have hz' : z ∈ V ⊓ Y.basicOpen (a i) := by rw [← this]; exact hz
    exact hz'.2

  have hq1 : ∀ j, (q j).asIdeal.height = 1 := by
    intro j
    have hmin : (q j).asIdeal ∈ (Ideal.span {b j}).minimalPrimes := by
      refine ⟨⟨(q j).2, (Ideal.span_singleton_le_iff_mem _).2 (hq.2.1 j)⟩, ?_⟩
      rintro Q ⟨hQp, hQb⟩ hQle
      exact (hq.2.2.1 j ⟨Q, hQp⟩ (le_trans (show (⟨Q, hQp⟩ : PrimeSpectrum Γ(Y, V)) ≤ q j from hQle)
        (hq.1 j))).mp (hQb (Ideal.mem_span_singleton_self _))
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin) ?_
    refine ENat.one_le_iff_ne_zero.2 fun h0 => hb0 j ?_
    have hmin0 := Ideal.height_eq_zero_iff.1 h0
    have hbot : (q j).asIdeal ≤ ⊥ := hmin0.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le
    exact hbot (hq.2.1 j)
  let w : Fin c → Y := fun j => hV.fromSpec (q j)
  have hwV : ∀ j, w j ∈ V := fun j => fromSpec_mem hV (q j)
  have hpw : ∀ j, hV.primeIdealOf ⟨w j, hwV j⟩ = q j := fun j => pOf_fromSpec hV (q j)
  have hcoh : ∀ j, Order.coheight (w j) = 1 := by
    intro j
    letI := Y.presheaf.algebra_section_stalk (⟨w j, hwV j⟩ : V)
    haveI := hV.isLocalization_stalk ⟨w j, hwV j⟩
    have := IsLocalization.AtPrime.ringKrullDim_eq_height (hV.primeIdealOf ⟨w j, hwV j⟩).asIdeal
      (Y.presheaf.stalk (w j))
    rw [ringKrullDim_stalk_eq_coheight, hpw, hq1] at this
    exact_mod_cast this
  refine ⟨w, fun j => Units.mk0 _ (ha0 j), ?_, fun j => ?_⟩
  · intro i j h
    have key : ∀ {z z' : Y} (hz : z ∈ V) (hz' : z' ∈ V), z = z' →
        hV.primeIdealOf ⟨z, hz⟩ = hV.primeIdealOf ⟨z', hz'⟩ := by
      rintro z z' hz hz' rfl
      rfl
    have h2 : q i = q j := (hpw i).symm.trans ((key (hwV i) (hwV j) h).trans (hpw j))
    exact (hq.2.2.2 i j (h2 ▸ hq.2.1 j)).symm
  have hwb : w j ∉ Y.basicOpen (b j) := by
    intro h'
    have h1 : q j ∈ hV.fromSpec ⁻¹ᵁ Y.basicOpen (b j) := h'
    rw [hV.fromSpec_preimage_basicOpen] at h1
    exact h1 (hq.2.1 j)
  refine ⟨rfl, fromSpec_specializes hq j, hcoh j, ?_, ?_, ?_⟩
  · intro h'
    exact hwb ((Y.basicOpen_res (a j) (homOfLE hVU').op).symm ▸ ⟨hwV j, h'⟩ : w j ∈ Y.basicOpen (b j))
  · letI := Y.presheaf.algebra_section_stalk (⟨w j, hwV j⟩ : V)
    haveI hloc0 := hV.isLocalization_stalk ⟨w j, hwV j⟩
    haveI hloc : IsLocalization.AtPrime (Y.presheaf.stalk (w j)) (q j).asIdeal := by
      rw [← hpw j]; exact hloc0
    have hgalg : Y.presheaf.germ V (w j) (hwV j) (b j) = algebraMap Γ(Y, V) (Y.presheaf.stalk (w j)) (b j) := rfl
    have hg0 : Y.presheaf.germ V (w j) (hwV j) (b j) ≠ 0 := fun h0 =>
      ha0 j (by rw [hfn, ← algebraMap_germ (hwV j), h0, map_zero])
    have hmax : Ideal.span {Y.presheaf.germ V (w j) (hwV j) (b j)} =
        IsLocalRing.maximalIdeal (Y.presheaf.stalk (w j)) := by
      refine le_antisymm ?_ ?_
      · rw [Ideal.span_singleton_le_iff_mem,
          ← IsLocalization.AtPrime.map_eq_maximalIdeal (q j).asIdeal (Y.presheaf.stalk (w j)), hgalg]
        exact Ideal.mem_map_of_mem _ (hq.2.1 j)
      · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (q j).asIdeal (Y.presheaf.stalk (w j)),
          Ideal.map_le_iff_le_comap]
        intro x hx
        rw [Ideal.mem_comap]
        letI := Y.presheaf.algebra_section_stalk (⟨y, hyV⟩ : V)
        haveI := hV.isLocalization_stalk ⟨y, hyV⟩
        haveI : (Ideal.span {Y.presheaf.germ V y hyV (b j)}).IsPrime :=
          (Ideal.span_singleton_prime (hprime j).ne_zero).2 (hprime j)
        let P : Ideal Γ(Y, V) := Ideal.comap (algebraMap Γ(Y, V) (Y.presheaf.stalk y))
          (Ideal.span {Y.presheaf.germ V y hyV (b j)})
        have hPp : P.IsPrime := Ideal.IsPrime.comap _
        have hPle : P ≤ (hV.primeIdealOf ⟨y, hyV⟩).asIdeal := by
          intro z hz
          have hz' : algebraMap Γ(Y, V) (Y.presheaf.stalk y) z ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) :=
            (Ideal.span_singleton_le_iff_mem _).2
              ((IsLocalRing.mem_maximalIdeal _).2 (hprime j).not_unit) hz
          exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Y.presheaf.stalk y)
            (hV.primeIdealOf ⟨y, hyV⟩).asIdeal z).1 hz'
        have hbP : b j ∈ P := Ideal.mem_span_singleton_self _
        have hqP : q j ≤ ⟨P, hPp⟩ := (hq.2.2.1 j ⟨P, hPp⟩ hPle).mp hbP
        obtain ⟨t, ht, s, hts⟩ := exists_mul_eq_of_mem_span (hV.primeIdealOf ⟨y, hyV⟩).asIdeal
          (Y.presheaf.stalk y) (hqP hx)
        have htq : t ∉ (q j).asIdeal := fun h => ht (hq.1 j h)
        have hu : IsUnit (algebraMap Γ(Y, V) (Y.presheaf.stalk (w j)) t) :=
          IsLocalization.map_units (Y.presheaf.stalk (w j)) (⟨t, htq⟩ : (q j).asIdeal.primeCompl)
        have e : algebraMap Γ(Y, V) (Y.presheaf.stalk (w j)) t * algebraMap Γ(Y, V) (Y.presheaf.stalk (w j)) x =
            algebraMap Γ(Y, V) (Y.presheaf.stalk (w j)) s * algebraMap Γ(Y, V) (Y.presheaf.stalk (w j)) (b j) := by
          rw [← map_mul, ← map_mul, hts]
        refine Ideal.mem_span_singleton'.2 ⟨↑hu.unit⁻¹ * algebraMap Γ(Y, V) (Y.presheaf.stalk (w j)) s, ?_⟩
        rw [hgalg, mul_assoc, ← e, ← mul_assoc, hu.val_inv_mul, one_mul]
    have hlen : Module.length (Y.presheaf.stalk (w j))
        (Y.presheaf.stalk (w j) ⧸ Ideal.span {Y.presheaf.germ V (w j) (hwV j) (b j)}) = 1 := by
      rw [hmax, Module.length_eq_one_iff, isSimpleModule_iff_isCoatom]
      exact Ideal.isMaximal_def.1 (IsLocalRing.maximalIdeal.isMaximal _)
    show Scheme.ord (fnOf U (gen_mem hy) (a j)) (w j) = 1
    rw [hfn, ← algebraMap_germ (hwV j), GlobalTheory.Cartier.ord_algebraMap (hcoh j) hg0, hlen]
    rfl
  · intro v hvy hv1 hvw
    by_contra hva
    have hvV : v ∈ V := hvy.mem_open V.isOpen hyV
    have hbQ : b j ∈ (hV.primeIdealOf ⟨v, hvV⟩).asIdeal := by
      by_contra hn
      apply hva
      have h1 : hV.primeIdealOf ⟨v, hvV⟩ ∈ hV.fromSpec ⁻¹ᵁ Y.basicOpen (b j) := by
        rw [hV.fromSpec_preimage_basicOpen]; exact hn
      have h3 : hV.fromSpec (hV.primeIdealOf ⟨v, hvV⟩) ∈ Y.basicOpen (b j) := h1
      rw [hV.fromSpec_primeIdealOf] at h3
      exact hbas j h3
    have hle : q j ≤ hV.primeIdealOf ⟨v, hvV⟩ :=
      (hq.2.2.1 j _ ((specializes_iff_pOf hV hvV hyV).mp hvy)).mp hbQ
    have hQv1 : (hV.primeIdealOf ⟨v, hvV⟩).asIdeal.height = 1 := by
      letI := Y.presheaf.algebra_section_stalk (⟨v, hvV⟩ : V)
      haveI := hV.isLocalization_stalk ⟨v, hvV⟩
      have := IsLocalization.AtPrime.ringKrullDim_eq_height (hV.primeIdealOf ⟨v, hvV⟩).asIdeal
        (Y.presheaf.stalk v)
      rw [ringKrullDim_stalk_eq_coheight, hv1] at this
      exact_mod_cast this.symm
    have heq : q j = hV.primeIdealOf ⟨v, hvV⟩ := by
      by_contra hne
      haveI : (q j).asIdeal.FiniteHeight :=
        (q j).asIdeal.finiteHeight_iff.mpr (Or.inr (by rw [hq1 j]; exact ENat.one_ne_top))
      have hlt : (q j).asIdeal < (hV.primeIdealOf ⟨v, hvV⟩).asIdeal :=
        lt_of_le_of_ne hle (fun h => hne (PrimeSpectrum.ext h))
      have := Ideal.height_strict_mono_of_isPrime hlt
      rw [hq1 j, hQv1] at this
      exact lt_irrefl _ this
    exact hvw (eq_of_pOf_eq hV hvV (hwV j) (by rw [hpw j]; exact heq.symm))

end GlobalTheory.RegParPrime
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Cartier

theorem ord_fnOf_eq_one_of_generates (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)
    (hU : IsAffineOpen U) (z : X) (hz : z ∈ U) (a t : Γ(X, U)) (h1 : Order.coheight z = 1)
    (ha : a ≠ 0) (haP : a ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal)
    (ht : t ∉ (hU.primeIdealOf ⟨z, hz⟩).asIdeal)
    (hg : ∀ g ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal, ∃ r, t * g = a * r) :
    Scheme.ord (fnOf U (gen_mem hz) a) z = 1 := by
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨z, hz⟩ : U)
  haveI := hU.isLocalization_stalk ⟨z, hz⟩
  set P := (hU.primeIdealOf ⟨z, hz⟩).asIdeal with hP
  have halg : ∀ b : Γ(X, U), algebraMap Γ(X, U) (X.presheaf.stalk z) b = X.presheaf.germ U z hz b :=
    fun b => rfl
  have hmax : IsLocalRing.maximalIdeal (X.presheaf.stalk z) =
      Ideal.span {X.presheaf.germ U z hz a} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P (X.presheaf.stalk z)]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro g hgP
      obtain ⟨r, hr⟩ := hg g hgP
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]
      obtain ⟨u, hu⟩ := (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk z) P t).2 ht
      refine ⟨algebraMap Γ(X, U) (X.presheaf.stalk z) r * ↑u⁻¹, ?_⟩
      have e := congrArg (algebraMap Γ(X, U) (X.presheaf.stalk z)) hr
      rw [map_mul, map_mul, ← hu] at e
      rw [← halg]
      calc algebraMap Γ(X, U) (X.presheaf.stalk z) g
          = ↑u⁻¹ * (↑u * algebraMap Γ(X, U) (X.presheaf.stalk z) g) := by simp
        _ = _ := by rw [e]; ring
    · rw [Ideal.span_le, Set.singleton_subset_iff, ← halg]
      exact Ideal.mem_map_of_mem _ haP
  have hne : X.presheaf.germ U z hz a ≠ 0 := fun h0 =>
    ha (fnOf_injective U (gen_mem hz) (by rw [← algebraMap_germ hz, h0, map_zero, map_zero]))
  rw [← algebraMap_germ hz a, ord_algebraMap h1 hne, ← hmax]
  haveI := (isSimpleModule_iff_isCoatom.2
    (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk z)).out :
      IsSimpleModule _ (X.presheaf.stalk z ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk z)))
  simp [Module.length_eq_one]

end GlobalTheory.Cartier
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

theorem GlobalTheory.Cartier.ord_fnOf_eq_zero_off_center : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens) (hU : IsAffineOpen U) (z : X) (hz : z ∈ U) (a t : Γ(X, U)), Order.coheight z = 1 → (∀ g ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal, ∃ r, t * g = a * r) → ∀ (v : X) (hv : v ∈ U), v ∈ X.basicOpen t → v ≠ z → Scheme.ord (fnOf U (gen_mem hv) a) v = 0 := by
  intro X _ _ U hU z hz a t hcz hdiv v hv ht hne
  by_cases ha : v ∈ X.basicOpen a
  · exact UnitAt.ord_eq_zero ((unitAt_fnOf_iff hv _ a).2 ha)
  refine Scheme.ord_eq_zero_of_coheight_neq_one (fun hcv => ?_) _
  have key : ∀ (w : X) (hw : w ∈ U) (f : Γ(X, U)),
      w ∈ X.basicOpen f ↔ f ∉ (hU.primeIdealOf ⟨w, hw⟩).asIdeal := by
    intro w hw f
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨w, hw⟩ : U)
    haveI := hU.isLocalization_stalk ⟨w, hw⟩
    rw [X.mem_basicOpen f w hw]
    exact IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk w) _ f
  have hle : (hU.primeIdealOf ⟨z, hz⟩).asIdeal ≤ (hU.primeIdealOf ⟨v, hv⟩).asIdeal := by
    intro g hg
    obtain ⟨r, hr⟩ := hdiv g hg
    have haP : a ∈ (hU.primeIdealOf ⟨v, hv⟩).asIdeal := by
      by_contra h
      exact ha ((key v hv a).2 h)
    have htP : t ∉ (hU.primeIdealOf ⟨v, hv⟩).asIdeal := (key v hv t).1 ht
    have htg : t * g ∈ (hU.primeIdealOf ⟨v, hv⟩).asIdeal := hr ▸ Ideal.mul_mem_right _ _ haP
    exact ((hU.primeIdealOf ⟨v, hv⟩).isPrime.mem_or_mem htg).resolve_left htP
  have hsp : z ⤳ v := by
    have h1 := ((PrimeSpectrum.le_iff_specializes _ _).mp hle).map hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at h1
  have hvz : v ≤ z := hsp
  have hlt : v < z := lt_of_le_not_ge hvz (fun h => hne (hsp.antisymm h).eq.symm)
  have h2 := Order.coheight_add_one_le hlt
  rw [hcz, hcv] at h2
  exact absurd h2 (by norm_num)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitDown

theorem exists_above {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v := by
  haveI := v.isMaximal
  obtain ⟨P, hPm, hP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hP.over, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))
  refine ⟨⟨P, hPm.isPrime, hne⟩, ?_⟩
  ext1
  rw [HeightOneSpectrum.under_asIdeal]
  exact hP.over.symm

theorem unit_down : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (b : Neutral.B1.Ideles (maximalRealSubfield E)),
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b ∈ GlobalTheory.Mem.Chr.unitIdl E → b ∈ GlobalTheory.Mem.Chr.unitIdl (maximalRealSubfield E) := by
  intro E _ _ _ b hb v
  obtain ⟨w, rfl⟩ := exists_above (E := E) v
  have h := hb w
  have e : ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b : AdeleRing (𝓞 E) E).2 w) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap (maximalRealSubfield E) E w
        ((b : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 (w.under _)) := rfl
  rw [e, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap] at h
  have he : (w.under (𝓞 (maximalRealSubfield E))).asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal (w.under _).ne_bot
  set x := Valued.v ((b : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 (w.under _))
  set n := (w.under (𝓞 (maximalRealSubfield E))).asIdeal.ramificationIdx' w.asIdeal
  have h' : x ^ n = 1 := h
  rcases lt_trichotomy x 1 with hx | hx | hx
  · exact absurd h' (pow_lt_one₀ zero_le' hx he).ne
  · exact hx
  · exact absurd h' (one_lt_pow₀ hx he).ne'

end GlobalTheory.UnitDown
end
