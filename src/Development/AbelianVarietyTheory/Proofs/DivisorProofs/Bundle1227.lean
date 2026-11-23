module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle978
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjSpaceStandardChartFubiniStudy
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle004
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SncForm

theorem ideal_vanishingIdeal_closure {X : Scheme.{0}} (U : X.affineOpens) {η : X} (hη : η ∈ U.1) :
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η})).ideal U =
      (U.2.primeIdealOf ⟨η, hη⟩).asIdeal := by
  have hU : IsAffineOpen U.1 := U.2
  have emb := hU.fromSpec.isOpenEmbedding
  have h1 : hU.fromSpec (hU.primeIdealOf ⟨η, hη⟩) = η := hU.fromSpec_primeIdealOf ⟨η, hη⟩
  have h2 : hU.fromSpec ⁻¹' ({η} : Set X) = {hU.primeIdealOf ⟨η, hη⟩} := by
    ext Q
    exact ⟨fun h => emb.injective (h.trans h1.symm), fun h => (congrArg _ h).trans h1⟩
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
  change PrimeSpectrum.vanishingIdeal (hU.fromSpec ⁻¹' closure ({η} : Set X)) = _
  have h3 := (emb.isOpenMap.preimage_closure_eq_closure_preimage emb.continuous {η}).trans
    (congrArg closure h2)
  exact (congrArg PrimeSpectrum.vanishingIdeal h3).trans
    ((PrimeSpectrum.vanishingIdeal_closure _).trans (PrimeSpectrum.vanishingIdeal_singleton _))

theorem exists_isLocalization_stalk {X : Scheme.{0}} (U : X.affineOpens) {y η : X} (hy : y ∈ U.1)
    (hη : η ∈ U.1) (hηy : η ⤳ y) (p : Ideal (X.presheaf.stalk y)) [p.IsPrime]
    (hp : FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η})) y = p) :
    ∃ _ : Algebra (X.presheaf.stalk y) (X.presheaf.stalk η),
      IsLocalization.AtPrime (X.presheaf.stalk η) p ∧ ∀ a : Γ(X, U.1),
        X.presheaf.germ U.1 η hη a =
          algebraMap (X.presheaf.stalk y) (X.presheaf.stalk η) (X.presheaf.germ U.1 y hy a) := by
  have hU : IsAffineOpen U.1 := U.2
  let yU : U.1 := ⟨y, hy⟩
  let algY : Algebra Γ(X, U.1) (X.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf yU
  have hlocY : IsLocalization.AtPrime (X.presheaf.stalk y) (hU.primeIdealOf yU).asIdeal :=
    hU.isLocalization_stalk yU
  set Py := hU.primeIdealOf yU with hPy
  let Pη := hU.primeIdealOf ⟨η, hη⟩
  have hfromη : hU.fromSpec Pη = η := hU.fromSpec_primeIdealOf ⟨η, hη⟩
  have hfromy : hU.fromSpec Py = y := hU.fromSpec_primeIdealOf yU
  have emb := hU.fromSpec.isOpenEmbedding
  have hspec : ∀ P Q : PrimeSpectrum Γ(X, U.1), hU.fromSpec P ⤳ hU.fromSpec Q ↔ P ≤ Q := by
    intro P Q
    rw [PrimeSpectrum.le_iff_specializes]
    exact emb.isInducing.specializes_iff
  have hle : Pη ≤ Py := (hspec _ _).mp (by rw [hfromη, hfromy]; exact hηy)
  have hdisj : Disjoint (Py.asIdeal.primeCompl : Set Γ(X, U.1)) Pη.asIdeal :=
    Set.disjoint_left.mpr fun x hx hx' => hx ((show Pη.asIdeal ≤ Py.asIdeal from hle) hx')
  rw [WMult.stalkId_eq_map_germ _ y U hy, ideal_vanishingIdeal_closure U hη] at hp
  have hPeq : Pη.asIdeal = p.comap (algebraMap Γ(X, U.1) (X.presheaf.stalk y)) := by
    rw [← hp]
    exact (IsLocalization.under_map_of_isPrime_disjoint Py.asIdeal.primeCompl
      (X.presheaf.stalk y) Pη.isPrime hdisj).symm
  let T := Localization.AtPrime p
  have hT : IsLocalization.AtPrime T (p.comap (algebraMap Γ(X, U.1) (X.presheaf.stalk y))) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (M := Py.asIdeal.primeCompl) (S := X.presheaf.stalk y) (T := T) p
  have hT' : IsLocalization Pη.asIdeal.primeCompl T := by
    have hsm : Pη.asIdeal.primeCompl =
        (Ideal.comap (algebraMap Γ(X, U.1) (X.presheaf.stalk y)) p).primeCompl := by
      ext x; rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hPeq]
    rw [hsm]; exact hT
  let ηU : U.1 := ⟨η, hη⟩
  let algη : Algebra Γ(X, U.1) (X.presheaf.stalk η) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ηU
  have hlocη : IsLocalization.AtPrime (X.presheaf.stalk η) Pη.asIdeal :=
    hU.isLocalization_stalk ηU
  let φ : X.presheaf.stalk η ≃ₐ[Γ(X, U.1)] T := IsLocalization.algEquiv Pη.asIdeal.primeCompl _ _
  let algYη : Algebra (X.presheaf.stalk y) (X.presheaf.stalk η) :=
    (φ.symm.toRingEquiv.toRingHom.comp (algebraMap (X.presheaf.stalk y) T)).toAlgebra
  refine ⟨algYη, (IsLocalization.isLocalization_iff_of_ringEquiv (M := p.primeCompl)
      (S := T) φ.symm.toRingEquiv).mp inferInstance, fun a => ?_⟩
  have h1 := (φ.symm.commutes a).symm
  rw [IsScalarTower.algebraMap_apply Γ(X, U.1) (X.presheaf.stalk y) T] at h1
  exact h1

theorem germ_eq_unit_mul_monomial : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (B : LB X) (hB : B.IsLB) (s : B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (r : ℕ) (z : Fin r → X), Function.Injective z → (∀ a, Order.coheight (z a) = 1) → ((nonzeroLocus s : Set X)ᶜ = ⋃ a, closure {z a}) → ∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x → ∀ (i : B.ι) (hi : x ∈ B.U i), ∃ (n : ℕ) (g : Fin n → X.presheaf.stalk x) (e : {a : Fin r // x ∈ (Closeds.closure {z a})} ↪ Fin n) (u : (X.presheaf.stalk x)ˣ) (_ : Fintype {a : Fin r // x ∈ (Closeds.closure {z a})}), FinalTheorems.Rsp (X.presheaf.stalk x) n g ∧ (∀ a, FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z a.1})) x = Ideal.span {g (e a)}) ∧ X.presheaf.germ _ x hi (s.f i) = u * ∏ a, g (e a) ^ ((divOfSec hB s hs).mult (z a.1)).toNat := by
  classical
  intro X _ _ B hB s hs r z _ hz hZ x hx i hi
  obtain ⟨hreg, n, g, e, hg, hI⟩ := hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVi⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hi (B.U i).isOpen
  let U : X.affineOpens := ⟨V, hV⟩
  have hVi' : V ≤ B.U i := hVi
  let t : Γ(X, V) := X.presheaf.map (homOfLE hVi').op (s.f i)
  have ht : ∀ (w : X) (hw : w ∈ V), X.presheaf.germ V w hw t =
      X.presheaf.germ _ w (hVi' hw) (s.f i) := fun w hw =>
    X.presheaf.germ_res_apply (homOfLE hVi') w hw _
  set γ := X.presheaf.germ _ x hi (s.f i) with hγ
  have hγ0 : γ ≠ 0 := fun h0 => fnOf_sec_ne_zero hs (gen_mem hi)
    ((algebraMap_germ hi (s.f i)).symm.trans ((congrArg _ h0).trans (map_zero _)))
  let J : Finset (Fin n) := Finset.univ.map e
  have hrad : (∏ j ∈ J, g j) ∈ (Ideal.span {γ}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro Q ⟨hQγ, hQ⟩
    let P : PrimeSpectrum Γ(X, V) := ⟨Q.comap (X.presheaf.germ V x hxV).hom, inferInstance⟩
    have htP : t ∈ P.asIdeal := by
      change X.presheaf.germ V x hxV t ∈ Q
      rw [ht]
      exact hQγ (Ideal.mem_span_singleton_self _)
    have hmem : hV.fromSpec P ∈ V := by
      have : hV.fromSpec P ∈ Set.range hV.fromSpec := ⟨P, rfl⟩
      rwa [hV.range_fromSpec] at this
    have hnz : hV.fromSpec P ∉ nonzeroLocus s := by
      rw [mem_nonzeroLocus_iff s i (hVi' hmem)]
      intro h
      have h' : hV.fromSpec P ∈ X.basicOpen t := by
        rw [Scheme.mem_basicOpen _ _ _ hmem, ht]
        exact (Scheme.mem_basicOpen _ _ _ _).1 h
      have h'' : P ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen t := h'
      rw [hV.fromSpec_preimage_basicOpen] at h''
      exact h'' htP
    have hc : hV.fromSpec P ∈ ((nonzeroLocus s : Set X)ᶜ) := hnz
    rw [hZ] at hc
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hc
    have hPx : hV.fromSpec P ⤳ x := by
      have h1 : hV.fromSpec (hV.primeIdealOf ⟨x, hxV⟩) = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
      have h2 : P ≤ hV.primeIdealOf ⟨x, hxV⟩ := by
        rw [hV.primeIdealOf_eq_map_closedPoint]
        exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ.ne_top)
      have h3 := ((PrimeSpectrum.le_iff_specializes _ _).1 h2).map hV.fromSpec.continuous
      rwa [h1] at h3
    have hxa : x ∈ Closeds.closure {z a} := hPx.mem_closed isClosed_closure ha
    have hsup : hV.fromSpec P ∈
        ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z a})).support : Set X) := by
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact ha
    rw [WMult.mem_support_fromSpec_iff _ U hV] at hsup
    have h3 : Ideal.span {g (e ⟨a, hxa⟩)} ≤ Q := by
      rw [← hI ⟨a, hxa⟩, WMult.stalkId_eq_map_germ _ x U hxV]
      exact Ideal.map_le_iff_le_comap.mpr hsup
    exact Q.mem_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_map_of_mem e (Finset.mem_univ _)))
      (h3 (Ideal.mem_span_singleton_self _))
  obtain ⟨u, m, -, hγu⟩ := eq_unit_mul_monomial g hg.1 hg.2 J hγ0 hrad
  refine ⟨n, g, e, u, inferInstance, hg, hI, ?_⟩
  have hord : ∀ a, ((divOfSec hB s hs).mult (z a.1)).toNat = m (e a) := by
    intro a
    have hsp : z a.1 ⤳ x := specializes_iff_mem_closure.2 a.2
    have hzV : z a.1 ∈ V := hsp.mem_open V.isOpen hxV
    have hpr : Prime (g (e a)) := prime_of_regular_params g hg.1 hg.2 _
    have hP : (Ideal.span {g (e a)}).IsPrime := (Ideal.span_singleton_prime hpr.ne_zero).mpr hpr
    obtain ⟨alg, hloc, hgerm⟩ := exists_isLocalization_stalk U hxV hzV hsp _ (hI a)
    have h := WMult.ord_isLocalization_eq_exponent g hg.1 hg.2 J u m (e a)
      (Finset.mem_map_of_mem e (Finset.mem_univ _)) (X.presheaf.stalk (z a.1))
    rw [← hγu, hγ, ← ht x hxV, ← hgerm t, ht] at h
    rw [mult_divOfSec (hz _) (hVi' hzV), Int.toNat_natCast]
    exact (congrArg ENat.toNat h).trans (ENat.toNat_natCast _)
  rw [hγu, Finset.prod_map]
  exact congrArg _ (Finset.prod_congr rfl fun a _ => by rw [hord])

end GlobalTheory.SncForm
end
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

theorem _root_.GlobalTheory.T.closed_subscheme_mod_l_projective : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] (l : ℕ) [Fact l.Prime] [Algebra (ZMod l) Γ(Z, ⊤)], IsProjOver (strHom (ZMod l) (X := Z)) := by
  first | exact @GlobalTheory.VertProj.isProjOver_strHom_zmod | exact GlobalTheory.VertProj.isProjOver_strHom_zmod | (intros; apply GlobalTheory.VertProj.isProjOver_strHom_zmod <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.RegCodimOne

theorem regAt_iff_ord_nonneg {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] {z : X} (hz : Order.coheight z = 1) {g : X.functionField} (hg : g ≠ 0) :
    RegAt z g ↔ 0 ≤ Scheme.ord g z := by
  haveI := IsNormalScheme.isDiscreteValuationRing_stalk hz
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk z)
  have h := le_ordTop_vw_iff (F := X.functionField) ht 0 g
  rw [ordTop_vw_of_ne_zero _ hg, WithTop.coe_le_coe] at h
  have e : Scheme.ord g z = WithZero.log (Ring.ordFrac (X.presheaf.stalk z) g) :=
    (Scheme.ord_eq_iff hz hg).2 (WithZero.exp_log ((map_ne_zero _).2 hg)).symm
  rw [e]
  refine Iff.trans ⟨fun ⟨a, ha⟩ => ⟨a, by simp [ha]⟩, fun ⟨a, ha⟩ => ⟨a, by simp [ha]⟩⟩ h.symm

theorem regularAt_iff_forall_specializes : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (D : CartierDiv X) (x : X) (f : X.functionFieldˣ), D.RegularAt x (f : X.functionField) ↔ ∀ z, z ⤳ x → 0 ≤ Scheme.ord (f : X.functionField) z + D.mult z := by
  intro X _ _ _ D x f
  obtain ⟨g, hg⟩ := D.exists_isEqn x
  obtain ⟨U, hU, hgU⟩ := hg.exists_nhds
  have hne : (f : X.functionField) * (g : X.functionField) ≠ 0 := mul_ne_zero f.ne_zero g.ne_zero
  have key : ∀ z, z ⤳ x → Scheme.ord (f : X.functionField) z + D.mult z =
      Scheme.ord ((f : X.functionField) * (g : X.functionField)) z := fun z hz => by
    rw [(hgU z (hz.mem_open U.isOpen hU)).mult_eq, Scheme.ord_mul f.ne_zero g.ne_zero]
  rw [hg.regularAt_iff]
  refine ⟨fun h z hz => ?_, fun h => regAt_of_forall_coheight_eq_one fun z hz h1 => ?_⟩
  · rw [key z hz]
    by_cases h1 : Order.coheight z = 1
    · exact (regAt_iff_ord_nonneg h1 hne).1 (GlobalTheory.Discrepancy.regAt_of_specializes hz h)
    · rw [Scheme.ord_eq_zero_of_coheight_neq_one h1]
  · exact (regAt_iff_ord_nonneg h1 hne).2 (key z hz ▸ h z hz)

end GlobalTheory.RegCodimOne
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

namespace GlobalTheory.VolBr

theorem exists_sec_finite_subset_nonzeroLocus : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M A : HermLB p), IsAmpleLB A.B → ∀ S : Set X, S.Finite → ∃ b : ℕ, 0 < b ∧ ∃ u : (M.tens (A.pow b)).B.Sec, S ⊆ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u := by
  intro k _ X _ p D hX M A hA S hS
  have := hX.isLocallyNoetherian
  have hEv : ∀ᶠ b : ℕ in atTop, ∀ (N : LB X) (hN : N.IsLB),
      CechPic.cls N hN = CechPic.cls M.B M.isLB + (b : ℤ) • CechPic.cls A.B hA.isLB →
        ∃ u : N.Sec, S ⊆ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u :=
    tendsto_natCast_atTop_atTop.eventually
      (hA.eventually_exists_finite_subset_nonzeroLocus M.isLB hS)
  obtain ⟨b, h₁, hb⟩ := (hEv.and (eventually_gt_atTop 0)).exists
  refine ⟨b, hb, ?_⟩
  have eA : CechPic.cls _ (A.pow b).isLB = (b : ℤ) • CechPic.cls A.B hA.isLB :=
    (CechPic.cls_lbPow hA.isLB b (A.pow b).isLB).trans (natCast_zsmul _ _).symm
  obtain ⟨u, hu⟩ := h₁ _ (M.tens (A.pow b)).isLB
    ((CechPic.cls_tens M.isLB (A.pow b).isLB (M.tens (A.pow b)).isLB).trans (congrArg _ eA))
  exact ⟨u, hu⟩

end GlobalTheory.VolBr
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BumpPts

theorem exists_finset_closure_eq_top {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k)
    [LocallyOfFiniteType p] {W : X.Opens} (hW : IsAffineOpen W) :
    ∃ s : Finset Γ(X, W), Subring.closure (Set.range (constFn p W) ∪ ↑s) = ⊤ := by
  have h := HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (fun _ _ => trivial)
  letI := (p.appLE ⊤ W (fun _ _ => trivial)).hom.toAlgebra
  haveI : Algebra.FiniteType Γ(Sp k, ⊤) Γ(X, W) := h
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := Γ(Sp k, ⊤)) (A := Γ(X, W))
  refine ⟨s, ?_⟩
  have e : Set.range (constFn p W) = Set.range (algebraMap Γ(Sp k, ⊤) Γ(X, W)) := by
    ext f
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨b, rfl⟩
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom b, ?_⟩
      have hb : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom b) = b := by
        rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
      show (p.appLE ⊤ W (fun _ _ => trivial)).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom b)) = _
      rw [hb]
      rfl
  rw [e, ← Algebra.adjoin_eq_ring_closure, hs]
  rfl

theorem exists_cInf_bump (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    (hp : IsProjOver p) (σ : k →+* ℂ) (y : CxPts p σ) (O : Set (CxPts p σ)) (hO : IsOpen O)
    (hy : y ∈ O) : ∃ χ : CxPts p σ → ℝ, (∀ z, CInfAt χ z) ∧ (∀ z, 0 ≤ χ z) ∧ 0 < χ y ∧
      tsupport χ ⊆ O := by
  haveI : IsProper p := CommonModel.isProper_of_isProjOver hp
  haveI : T2Space (CxPts p σ) := t2Space_cxPts_of_isProjOver σ hp
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_le y.1 (le_preimage_top y.1)
  have hyW' : y ∈ ptsIn p σ W := hyW
  obtain ⟨s, hs⟩ := exists_finset_closure_eq_top p hW
  let φ : CxPts p σ → (s → ℂ) := fun z a => ev p σ W a.1 z

  obtain ⟨S, hS, hSO⟩ : ∃ S ∈ 𝓝 (φ y), ∀ z ∈ ptsIn p σ W, φ z ∈ S → z ∈ O := by
    let l := Filter.comap φ (𝓝 (φ y)) ⊓ 𝓟 (ptsIn p σ W)
    have hφl : Tendsto φ l (𝓝 (φ y)) := tendsto_comap.mono_left inf_le_left
    have ht : Tendsto (fun z => z) l (𝓝 y) := by
      refine (PtsOver.tendsto_iff_of_generators hW hyW hs).2 ⟨?_, fun f hf => ?_⟩
      · exact mem_inf_of_right (mem_principal_self _)
      · exact ((continuous_apply (⟨f, hf⟩ : s)).tendsto _).comp hφl
    have h : O ∈ l := ht (hO.mem_nhds hy)
    rw [mem_inf_principal] at h
    obtain ⟨S, hS, hSO⟩ := mem_comap.1 h
    exact ⟨S, hS, fun z hz hzS => hSO hzS hz⟩
  obtain ⟨F, hFS, hFc, hFd, hFr, hF1⟩ := exists_contDiff_tsupport_subset (n := ⊤) hS
  let K : Set (CxPts p σ) := {z | z ∈ ptsIn p σ W ∧ φ z ∈ tsupport F}

  have hKc : IsCompact K := by
    refine isCompact_iff_ultrafilter_le_nhds.2 fun u hu => ?_
    have hKu : K ∈ u := le_principal_iff.1 hu
    have hWu : ∀ᶠ z in (u : Filter (CxPts p σ)), z ∈ ptsIn p σ W := mem_of_superset hKu fun z hz => hz.1
    obtain ⟨v, -, hv⟩ := hFc.ultrafilter_le_nhds (u.map φ)
      (le_principal_iff.2 (Ultrafilter.mem_map.2
        (mem_of_superset hKu fun z (hz : z ∈ K) => hz.2)))
    have hv' : Tendsto φ u (𝓝 v) := hv
    have hcst : ∀ a : k, ∀ z ∈ ptsIn p σ W, ev p σ W (constFn p W a) z = ev p σ W (constFn p W a) y :=
      fun a z hz => by
        show valR z.1 W _ = valR y.1 W _
        rw [valR_constFn p z.1 W hz, valR_constFn p y.1 W hyW, z.2, y.2]
    have hlim : ∀ f : Γ(X, W), ∃ c, Tendsto (fun z => ev p σ W f z) u (𝓝 c) := by
      intro f
      have hf : f ∈ Subring.closure (Set.range (constFn p W) ∪ ↑s) := hs ▸ Subring.mem_top f
      induction hf using Subring.closure_induction with
      | mem f hf =>
        rcases hf with ⟨a, rfl⟩ | hf
        · exact ⟨_, tendsto_const_nhds.congr' (hWu.mono fun z hz => (hcst a z hz).symm)⟩
        · exact ⟨v ⟨f, hf⟩, ((continuous_apply (⟨f, hf⟩ : s)).tendsto _).comp hv'⟩
      | zero =>
        exact ⟨0, tendsto_const_nhds.congr' (hWu.mono fun z hz => ((ev_eq hz 0).trans (map_zero _)).symm)⟩
      | one =>
        exact ⟨1, tendsto_const_nhds.congr' (hWu.mono fun z hz => ((ev_eq hz 1).trans (map_one _)).symm)⟩
      | add f g _ _ hf hg =>
        obtain ⟨c, hc⟩ := hf
        obtain ⟨d, hd⟩ := hg
        exact ⟨c + d, (hc.add hd).congr fun z => (ev_add f g z).symm⟩
      | neg f _ hf =>
        obtain ⟨c, hc⟩ := hf
        exact ⟨-c, hc.neg.congr' (hWu.mono fun z hz => by
          show -ev p σ W f z = ev p σ W (-f) z
          rw [ev_eq hz, ev_eq hz, map_neg])⟩
      | mul f g _ _ hf hg =>
        obtain ⟨c, hc⟩ := hf
        obtain ⟨d, hd⟩ := hg
        exact ⟨c * d, (hc.mul hd).congr fun z => (ev_mul f g z).symm⟩
    choose c hc using hlim
    let ψ : Γ(X, W) →+* ℂ :=
      { toFun := c
        map_one' := tendsto_nhds_unique (hc 1)
          (tendsto_const_nhds.congr' (hWu.mono fun z hz => ((ev_eq hz 1).trans (map_one _)).symm))
        map_mul' := fun f g => tendsto_nhds_unique (hc (f * g))
          (((hc f).mul (hc g)).congr fun z => (ev_mul f g z).symm)
        map_zero' := tendsto_nhds_unique (hc 0)
          (tendsto_const_nhds.congr' (hWu.mono fun z hz => ((ev_eq hz 0).trans (map_zero _)).symm))
        map_add' := fun f g => tendsto_nhds_unique (hc (f + g))
          (((hc f).add (hc g)).congr fun z => (ev_add f g z).symm) }
    have hψ : ∀ a, ψ (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W a) = σ a := fun a => tendsto_nhds_unique (hc _)
      (tendsto_const_nhds.congr' (hWu.mono fun z hz => (ev_algX hz a).symm))
    let z' : CxPts p σ := ofHom hW ψ hψ
    have hz'W : z' ∈ ptsIn p σ W := ofHom_mem hW ψ hψ
    have hz'ev : ∀ f, ev p σ W f z' = c f := fun f => ev_ofHom hW ψ hψ f
    have ht : Tendsto (fun z => z) (u : Filter (CxPts p σ)) (𝓝 z') := by
      refine (PtsOver.tendsto_iff_of_generators hW hz'W hs).2 ⟨hWu, fun f _ => ?_⟩
      have := hc f
      rw [← hz'ev f] at this
      exact this
    have hφz' : φ z' = v := funext fun a =>
      (hz'ev a.1).trans (tendsto_nhds_unique (hc a.1) (((continuous_apply a).tendsto _).comp hv'))
    refine ⟨z', ⟨hz'W, ?_⟩, ht⟩
    rw [hφz']
    exact hFc.isClosed.mem_of_tendsto hv' (mem_of_superset hKu fun z hz => hz.2)
  have hKcl : IsClosed K := hKc.isClosed
  let χ : CxPts p σ → ℝ := (ptsIn p σ W).indicator fun z => F (φ z)
  have hsupp : Function.support χ ⊆ K := fun z hz => by
    rw [Function.mem_support, Set.indicator_apply_ne_zero] at hz
    exact ⟨hz.1, subset_tsupport _ hz.2⟩
  refine ⟨χ, fun z => ?_, fun z => Set.indicator_nonneg (fun w _ => (hFr ⟨_, rfl⟩).1) z, ?_, ?_⟩
  · by_cases hz : z ∈ ptsIn p σ W
    · refine ⟨W, s, inferInstance, fun a => a.1, F, Set.univ, hz, isOpen_univ, trivial,
        hFd.contDiffOn, ?_⟩
      filter_upwards [(isOpen_ptsIn W).mem_nhds hz] with w hw
      exact Set.indicator_of_mem hw _
    · have hzK : z ∉ K := fun h => hz h.1
      refine (cInfAt_const 0 z).congr ?_
      filter_upwards [hKcl.isOpen_compl.mem_nhds hzK] with w hw
      exact Function.notMem_support.1 fun h => hw (hsupp h)
  · show 0 < (ptsIn p σ W).indicator (fun z => F (φ z)) y
    rw [Set.indicator_of_mem hyW', hF1]
    exact one_pos
  · exact (closure_minimal hsupp hKcl).trans fun z hz => hSO z hz.1 (hFS hz.2)

end GlobalTheory.BumpPts
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.exists_projSpace_standardChart_fubiniStudy : ∀ N : ℕ, ∃ (c : AlgChart (PSpace.str ℂ N) (RingHom.id ℂ) N) (i : (ProjSpace.hermitianTwistingSheaf ℂ N).B.ι), c.e.source = ptsIn (PSpace.str ℂ N) (RingHom.id ℂ) (ProjSpace.chart ℂ N 0) ∧ c.e.target = Set.univ ∧ c.e.source ⊆ ptsIn (PSpace.str ℂ N) (RingHom.id ℂ) ((ProjSpace.hermitianTwistingSheaf ℂ N).B.U i) ∧ ∀ v, ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).φ i (c.e.symm v) = Real.log (1 + ‖v‖ ^ 2) := by
  first | exact @GlobalTheory.StdProjChart.exists_stdChart | exact GlobalTheory.StdProjChart.exists_stdChart | (intros; apply GlobalTheory.StdProjChart.exists_stdChart <;> assumption)
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.mul_mem_range_norm_of_not_mem : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (x y : Fˣ), x ∉ (Units.map (Algebra.norm F : E →* F)).range → y ∉ (Units.map (Algebra.norm F : E →* F)).range → x * y ∈ (Units.map (Algebra.norm F : E →* F)).range := by
  first | exact @GlobalTheory.KSp.NormIndex.mul_mem_range_norm | exact GlobalTheory.KSp.NormIndex.mul_mem_range_norm | (intros; apply GlobalTheory.KSp.NormIndex.mul_mem_range_norm <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.asymptotic_riemannRoch_ample_coherent : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∀ L : LB X, IsAmpleLB L → ∃ C m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → |(d.factorial : ℤ) * (hdim k (twist F (lbPow L m)) 0 : ℤ) - interNum k F (fun _ : Fin d => L) * (m : ℤ) ^ d| ≤ C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) := by
  first | exact @GlobalTheory.abs_factorial_mul_hdim_zero_twist_sub_le_of_isAmpleLB | exact GlobalTheory.abs_factorial_mul_hdim_zero_twist_sub_le_of_isAmpleLB | (intros; apply GlobalTheory.abs_factorial_mul_hdim_zero_twist_sub_le_of_isAmpleLB <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.higherCohomology_twist_bound_of_two_cuts : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), L.IsLB → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → ∀ i, 2 ≤ i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  first | exact @GlobalTheory.hdim_twist_lbPow_le_of_two_le | exact GlobalTheory.hdim_twist_lbPow_le_of_two_le | (intros; apply GlobalTheory.hdim_twist_lbPow_le_of_two_le <;> assumption)
end
