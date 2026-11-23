module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle078
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle167
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCCovSelf
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle097
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle101
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle166
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

section

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {t : X ⟶ Sp ℤ}

theorem toZ_tens_isometric (L M : HermLB p) (hLM : ∀ τ, (wZ (L.tens M) t τ).IsCInf)
    (hL : ∀ τ, (wZ L t τ).IsCInf) (hM : ∀ τ, (wZ M t τ).IsCInf) :
    (toZ (L.tens M) t hLM).Isometric ((toZ L t hL).tens (toZ M t hM)) :=
  HermLB.isometric_of_eqOn fun _ _ _ _ => rfl

noncomputable def toZClass (t : X ⟶ Sp ℤ) (H : ∀ (L : HermLB p) (τ : ℤ →+* ℂ), (wZ L t τ).IsCInf) :
    HermLB.IsomClass p →+ HermLB.IsomClass t :=
  AddMonoidHom.mk' (M := HermLB.IsomClass p) (G := HermLB.IsomClass t)
    (Quotient.map (sa := HermLB.isometrySetoid p) (sb := HermLB.isometrySetoid t)
      (fun L => toZ L t (H L)) fun L M h => toZ_isometric k X p t L M (H L) (H M) h)
    (by
      rintro ⟨L⟩ ⟨M⟩
      exact HermLB.icls_eq_iff.2 (toZ_tens_isometric L M (H _) (H _) (H _)))

theorem toZClass_icls (H : ∀ (L : HermLB p) (τ : ℤ →+* ℂ), (wZ L t τ).IsCInf) (L : HermLB p) :
    toZClass t H L.icls = (toZ L t (H L)).icls := rfl

end

theorem toZ_pow_comb : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ)
    (H : ∀ (L : HermLB p) (τ : ℤ →+* ℂ), (wZ L t τ).IsCInf),
    (∀ (L : HermLB p) (m : ℕ), (toZ (L.pow m) t (H _)).Isometric ((toZ L t (H _)).pow m)) ∧
    ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ),
      (toZ (ArInt.comb L n) t (H _)).Isometric (ArInt.comb (fun i => toZ (L i) t (H _)) n) := by
  intro k _ X p t H
  refine ⟨fun L m => HermLB.icls_eq_iff.1 ?_, fun ι _ L n => HermLB.icls_eq_iff.1 ?_⟩
  · rw [← toZClass_icls H, HermLB.icls_pow, HermLB.icls_pow, map_nsmul, toZClass_icls H]

  · rw [← toZClass_icls H, ArInt.icls_comb, ArInt.icls_comb, map_sum]
    simp only [map_zsmul, toZClass_icls H]

end GlobalTheory.CompanionTheory.Ar.BaseZ
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

def sheetEquiv {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) :
    (Σ σ : k →+* ℂ, CxPts p σ) ≃ CxPts t τ where
  toFun s := sheet t τ s.2
  invFun y := ⟨emb p y, unsheet p y⟩
  left_inv := by
    rintro ⟨σ, y⟩
    have key : ∀ (σ' : k →+* ℂ) (_ : σ' = σ) (y' : CxPts p σ'), y'.1 = y.1 →
        (⟨σ', y'⟩ : Σ σ : k →+* ℂ, CxPts p σ) = ⟨σ, y⟩ := by
      rintro σ' rfl y' h
      rw [Subtype.ext h]
    exact key _ (emb_sheet t τ y) _ rfl
  right_inv y := sheet_unsheet p y

theorem finite_sigma_cxPts {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (hX : IsArithVar p 0) : Finite (Σ σ : k →+* ℂ, CxPts p σ) := by
  have : Finite (X.residueField (genericPoint X) →+* ℂ) := by
    by_cases h : Nonempty (X.residueField (genericPoint X) →+* ℂ)
    · obtain ⟨f⟩ := h
      have := SmallSecHeight.numberField hX f.charZero
      infer_instance
    · have := not_nonempty_iff.1 h
      infer_instance
  exact .of_equiv _ (SmallSecHeight.ptsEquiv hX).symm

theorem sum_logNorm_curve : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ), IsArithVar p 0 → ∀ (M : HermLB p) (ν : Weight t τ M.B), WOver M.φ ν → ∀ (r : M.B.ι → X.functionFieldˣ), IsRatSec M.B r → ∑ᶠ y : CxPts t τ, logNorm ν r y = ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts p σ, logNorm (M.φ σ) r y := by
  intro k _ X _ p t τ hX M ν hν r hr
  have hfin := finite_sigma_cxPts hX
  have (σ : k →+* ℂ) : Finite (CxPts p σ) := .of_injective _ (sigma_mk_injective (i := σ))
  have := hX.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  have (σ : k →+* ℂ) := Fintype.ofFinite (CxPts p σ)
  have h₁ (σ : k →+* ℂ) (y : CxPts p σ) : logNorm ν r (sheet t τ y) = logNorm (M.φ σ) r y :=
    GlobalTheory.T.logNorm_sheet_eq k X p t τ M.B M.φ ν hν r hr σ y (mem_offSupp.2 (by
      rw [hX.under_eq_genericPoint]
      exact CartierDiv.genericPoint_notMem_supp _))
  rw [← finsum_comp_equiv (sheetEquiv p t τ)]
  simp only [finsum_eq_sum_of_fintype]
  rw [Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun y _ => h₁ σ y

end GlobalTheory.CompanionTheory.Ar.BaseZ
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem _root_.GlobalTheory.T.toZ_pull_isometric : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (t : X ⟶ Sp ℤ) (t' : Y ⟶ Sp ℤ) (π : Y ⟶ X) (hπ : π ≫ p = q) (hπ' : π ≫ t = t') (L : HermLB p) (hL : ∀ τ, (wZ L t τ).IsCInf) (hL' : ∀ τ, (wZ (L.pull π hπ) t' τ).IsCInf), (toZ (L.pull π hπ) t' hL').Isometric ((toZ L t hL).pull π hπ') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BaseZ.isometric_toZ_pull | exact GlobalTheory.CompanionTheory.Ar.BaseZ.isometric_toZ_pull | (intros; apply GlobalTheory.CompanionTheory.Ar.BaseZ.isometric_toZ_pull <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.CompanionTheory.Ar.BaseZ.ChartDown

theorem etale_res_int {X : Scheme.{0}} (t : X ⟶ Sp ℤ) {U : X.Opens} (hU : IsAffineOpen U) (n : Γ(X, U))
    {D : ℕ} (x : Fin D → Γ(X, U)) (h : (MvPolynomial.eval₂Hom (algX t U) x).Etale) :
    (MvPolynomial.eval₂Hom (Int.castRingHom Γ(X, X.basicOpen n))
      fun a => resG X (X.basicOpen_le n) (x a)).Etale := by
  have hloc := hU.isLocalization_basicOpen n
  have hres : (resG X (X.basicOpen_le n)).Etale :=
    RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway n)
  have hcomp := RingHom.Etale.stableUnderComposition _ _ h hres
  rw [MvPolynomial.comp_eval₂Hom] at hcomp
  rwa [show (resG X (X.basicOpen_le n)).comp (algX t U) = Int.castRingHom _ from RingHom.ext_int _ _] at hcomp

theorem isUnit_natCast_basicOpen {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (N : ℕ) :
    IsUnit (N : Γ(X, X.basicOpen (N : Γ(X, U)))) := by
  have hloc := hU.isLocalization_basicOpen (N : Γ(X, U))
  have := IsLocalization.Away.algebraMap_isUnit (S := Γ(X, X.basicOpen (N : Γ(X, U)))) (N : Γ(X, U))
  simpa using this

theorem mem_ptsIn_basicOpen_natCast {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    {U : X.Opens} {N : ℕ} (hN : N ≠ 0) {y : CxPts p σ} (hy : y ∈ ptsIn p σ U) :
    y ∈ ptsIn p σ (X.basicOpen (N : Γ(X, U))) := by
  refine (mem_ptsIn_basicOpen hy _).2 ?_
  have h := ev_algX hy (N : k)
  rw [map_natCast, map_natCast] at h
  rw [h]
  exact_mod_cast hN

end GlobalTheory.CompanionTheory.Ar.BaseZ.ChartDown


open GlobalTheory.CompanionTheory.Ar.BaseZ.ChartDown in
theorem GlobalTheory.CompanionTheory.Ar.BaseZ.exists_chart_sheet : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) (D : ℕ) (c' : AlgChart t τ D), Nonempty (CxPts p σ) → ∃ c : AlgChart p σ D, c.e.source = sheet t τ ⁻¹' c'.e.source ∧ ∀ y ∈ c.e.source, c'.e (sheet t τ y) = c.e y := by
  intro k _ _ _ _ X p t τ σ D c' hne
  obtain ⟨N, hN0, hN⟩ := GlobalTheory.T.etale_over_integers_localization k
  obtain ⟨hemb, -⟩ := GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ
  have hle := X.basicOpen_le (N : Γ(X, c'.U))
  have hetZ := etale_res_int t c'.affine (N : Γ(X, c'.U)) c'.x c'.etale
  have hetk := (GlobalTheory.T.etale_polynomial_base_change_iff k _ N hN (algX p (X.basicOpen (N : Γ(X, c'.U))))
    (isUnit_natCast_basicOpen c'.affine N) D _).2 hetZ
  let s := IsOpenEmbedding.toOpenPartialHomeomorph (sheet t τ : CxPts p σ → CxPts t τ) hemb
  have hs : (s : CxPts p σ → CxPts t τ) = sheet t τ := IsOpenEmbedding.toOpenPartialHomeomorph_apply _ hemb
  have hss : s.source = Set.univ := IsOpenEmbedding.toOpenPartialHomeomorph_source _ hemb
  have hst : s.target = Set.range (sheet t τ : CxPts p σ → CxPts t τ) :=
    IsOpenEmbedding.toOpenPartialHomeomorph_target _ hemb
  have hsrc : (s.trans c'.e).source = sheet t τ ⁻¹' c'.e.source := by
    rw [OpenPartialHomeomorph.trans_source, hss, Set.univ_inter, hs]
  have happ : ∀ y, (s.trans c'.e) y = c'.e (sheet t τ y) := fun y => by
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hs]
  have hsym : ∀ v ∈ (s.trans c'.e).target, sheet t τ ((s.trans c'.e).symm v) = c'.e.symm v := by
    intro v hv
    rw [OpenPartialHomeomorph.trans_target] at hv
    have h2 : c'.e.symm v ∈ s.target := hv.2
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.coe_trans,
      Function.comp_apply, ← hs]
    exact s.right_inv h2
  refine ⟨{ e := s.trans c'.e
            U := X.basicOpen (N : Γ(X, c'.U))
            affine := c'.affine.basicOpen _
            x := fun a => resG X hle (c'.x a)
            etale := hetk
            source_subset := ?_
            apply_eq := ?_
            holo := ?_ }, hsrc, fun y _ => (happ y).symm⟩
  · intro y hy
    rw [hsrc] at hy
    have h1 : sheet t τ y ∈ ptsIn t τ c'.U := c'.source_subset hy
    exact mem_ptsIn_basicOpen_natCast hN0 (show y ∈ ptsIn p σ c'.U from h1)
  · intro y hy a
    rw [hsrc] at hy
    have h1 : sheet t τ y ∈ ptsIn t τ c'.U := c'.source_subset hy
    have hB := mem_ptsIn_basicOpen_natCast hN0 (show y ∈ ptsIn p σ c'.U from h1)
    rw [happ, c'.apply_eq _ hy a, ev_res hle hB]
    rfl
  · intro W f
    refine ((c'.holo W f).mono ?_).congr ?_
    · rintro v ⟨hv, hw⟩
      refine ⟨?_, ?_⟩
      · rw [OpenPartialHomeomorph.trans_target] at hv
        exact hv.1
      · show c'.e.symm v ∈ ptsIn t τ W
        rw [← hsym v hv]
        exact hw
    · rintro v ⟨hv, -⟩
      show ev p σ W f _ = ev t τ W f (c'.e.symm v)
      rw [← hsym v hv]
      rfl
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

private theorem valR_restrict_eq_valR {A : Type} [CommRing A] {X : Scheme.{0}} (y : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp A ⟶ X)
    {U V : X.Opens} (hVU : V ≤ U) (h : ⊤ ≤ (TopologicalSpace.Opens.map y.base).obj V)
    (f : X.presheaf.obj (Opposite.op U)) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR y V ((X.presheaf.map (homOfLE hVU).op).hom f) =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR y U f := by
  have hU : ⊤ ≤ (TopologicalSpace.Opens.map y.base).obj U := h.trans (fun z hz => hVU hz)
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR
  rw [dite_eq_left h, dite_eq_left hU]
  congr 1
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, AlgebraicGeometry.Scheme.Hom.map_appLE]

private theorem isUnit_natCast_sp_complex_sections (N : ℕ) (hN : N ≠ 0) (W : (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ).Opens) :
    IsUnit (N : (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ).presheaf.obj (Opposite.op W)) := by
  have h1 : IsUnit (N : ℂ) := IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hN)
  have h2 := h1.map
    (((ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom.comp
      (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom)
  simpa only [map_natCast] using h2

private theorem etale_eval2Hom_basicOpen {k : Type} [CommRing k] {X : Scheme.{0}} {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) (N : ℕ)
    (hNet : (Int.castRingHom (Localization.Away (N : k))).Etale)
    (φ : k →+* X.presheaf.obj (Opposite.op U)) {D : ℕ} (x : Fin D → X.presheaf.obj (Opposite.op U))
    (hx : (MvPolynomial.eval₂Hom φ x).Etale) :
    (MvPolynomial.eval₂Hom
      (Int.castRingHom (X.presheaf.obj (Opposite.op (X.basicOpen (N : X.presheaf.obj (Opposite.op U))))))
      (fun a => algebraMap (X.presheaf.obj (Opposite.op U))
        (X.presheaf.obj (Opposite.op (X.basicOpen (N : X.presheaf.obj (Opposite.op U))))) (x a))).Etale := by
  haveI := hU.isLocalization_basicOpen (N : X.presheaf.obj (Opposite.op U))
  have hres : (algebraMap (X.presheaf.obj (Opposite.op U))
      (X.presheaf.obj (Opposite.op (X.basicOpen (N : X.presheaf.obj (Opposite.op U)))))).Etale :=
    RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway (N : X.presheaf.obj (Opposite.op U)))
  have hcomp : ((algebraMap (X.presheaf.obj (Opposite.op U))
      (X.presheaf.obj (Opposite.op (X.basicOpen (N : X.presheaf.obj (Opposite.op U)))))).comp
        (MvPolynomial.eval₂Hom φ x)).Etale :=
    RingHom.Etale.stableUnderComposition (MvPolynomial.eval₂Hom φ x) (algebraMap _ _) hx hres
  rw [MvPolynomial.comp_eval₂Hom] at hcomp
  have hunit : IsUnit
      ((N : X.presheaf.obj (Opposite.op (X.basicOpen (N : X.presheaf.obj (Opposite.op U)))))) := by
    simpa only [map_natCast] using
      IsLocalization.Away.algebraMap_isUnit
        (S := X.presheaf.obj (Opposite.op (X.basicOpen (N : X.presheaf.obj (Opposite.op U)))))
        (N : X.presheaf.obj (Opposite.op U))
  exact (GlobalTheory.T.etale_polynomial_base_change_iff k _ N hNet _ hunit D _).mp hcomp

theorem algChart_toZ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) (D : ℕ) (c : AlgChart p σ D) :
    ∃ c' : AlgChart t τ D, c'.e.source = sheet t τ '' c.e.source ∧ ∀ y ∈ c.e.source, c'.e (sheet t τ y) = c.e y := by
  classical
  obtain ⟨N, hN0, hNet⟩ := GlobalTheory.T.etale_over_integers_localization k
  obtain ⟨hemb, -⟩ := GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ
  haveI : Nonempty (GlobalTheory.CxPts p σ) := ⟨c.e.symm (0 : EuclideanSpace ℂ (Fin D))⟩
  obtain ⟨E, hE, hEs, hEt⟩ : ∃ E : OpenPartialHomeomorph (GlobalTheory.CxPts p σ) (GlobalTheory.CxPts t τ),
      ⇑E = sheet t τ ∧ E.source = Set.univ ∧ E.target = Set.range (sheet t τ) :=
    ⟨_, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply _ hemb,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source _ hemb,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target _ hemb⟩
  have hleft : ∀ y : GlobalTheory.CxPts p σ, E.symm (sheet t τ y) = y := by
    intro y
    have h := E.left_inv (x := y) (by rw [hEs]; trivial)
    rwa [hE] at h
  have hsrc : (E.symm.trans c.e).source = sheet t τ '' c.e.source := by
    ext z
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, hEt]
    constructor
    · rintro ⟨⟨y, rfl⟩, hy⟩
      exact ⟨y, by simpa [Set.mem_preimage, hleft] using hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, rfl⟩, by simpa [Set.mem_preimage, hleft] using hy⟩
  have hin : ∀ y ∈ c.e.source, ⊤ ≤ (TopologicalSpace.Opens.map (y.1).base).obj
      (X.basicOpen (N : X.presheaf.obj (Opposite.op c.U))) := by
    intro y hy
    rw [AlgebraicGeometry.Scheme.preimage_basicOpen, AlgebraicGeometry.Scheme.basicOpen_of_isUnit]
    · exact c.source_subset hy
    · rw [map_natCast]
      exact isUnit_natCast_sp_complex_sections N hN0 _
  have het := etale_eval2Hom_basicOpen c.affine N hNet (algX p c.U) c.x c.etale
  refine ⟨⟨E.symm.trans c.e, X.basicOpen (N : X.presheaf.obj (Opposite.op c.U)),
      c.affine.basicOpen _, fun a => algebraMap (X.presheaf.obj (Opposite.op c.U)) _ (c.x a),
      ?_, ?_, ?_, ?_⟩, hsrc, ?_⟩
  · have hZ : algX t (X.basicOpen (N : X.presheaf.obj (Opposite.op c.U))) =
        Int.castRingHom _ := RingHom.ext_int _ _
    rw [hZ]
    exact het
  · intro z hz
    rw [hsrc] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact hin y hy
  · intro z hz a
    rw [hsrc] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hleft, c.apply_eq y hy a]
    exact (valR_restrict_eq_valR y.1 (X.basicOpen_le _) (hin y hy) (c.x a)).symm
  · intro W f
    rw [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.coe_trans_symm,
      OpenPartialHomeomorph.symm_symm, hE, OpenPartialHomeomorph.symm_target, hEs]
    refine ((c.holo W f).mono ?_).congr ?_
    · rintro v ⟨⟨hv1, -⟩, hv2⟩
      exact ⟨hv1, hv2⟩
    · intro v _
      rfl
  · intro y hy
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hleft]

end GlobalTheory.CompanionTheory.Ar.BaseZ
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem cInfAt_sheet_iff : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) (f : CxPts t τ → ℝ) (y : CxPts p σ), CInfAt f (sheet t τ y) ↔ CInfAt (fun z : CxPts p σ => f (sheet t τ z)) y := by
  intro k _ _ X p t τ σ f y
  have hE := (GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ).1
  constructor
  · rintro ⟨W, ι, i, g, F, O, h₁, h₂, h₃, h₄, h₅⟩
    exact ⟨W, ι, i, g, F, O, h₁, h₂, h₃, h₄, hE.continuous.continuousAt.eventually h₅⟩
  · rintro ⟨W, ι, i, g, F, O, h₁, h₂, h₃, h₄, h₅⟩
    refine ⟨W, ι, i, g, F, O, h₁, h₂, h₃, h₄, ?_⟩
    show ∀ᶠ w in 𝓝 (sheet t τ y), f w = F fun a => ev t τ W (g a) w
    rw [← hE.map_nhds_eq, eventually_map]
    exact h₅

end GlobalTheory.CompanionTheory.Ar.BaseZ
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem identity_cover : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), ∃ (Cv : FlagCover M M) (CR : CovReal FA Cv), Cv.deg = 1 ∧ (∀ p, CR.Re.ref p = FA.Re.ref (some p)) ∧ ∀ p t, CR.Re.line p t = FA.Re.line (some p) t := by
  exact @PositivityTheory.Xgp.t_c_cov_self

end GlobalTheory.CompanionTheory.Ar.PB
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem flagPt_mem_mcPts : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q), ∀ b ∈ BM.O l, ∀ h : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0) → FC.flagPt M (BM.F l) (FC.bvec BM l b) h ∈ mcPts (mCoordIdeal y) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM l b hb h hh
  obtain ⟨hmem, hgood, hnorm, -⟩ := FC.bvec_good K ι Φ y Ψ N j M n BM l b hb
  have e := basePart_flagPt M (BM.F l) (FC.bvec BM l b) h
  refine CPts.flag_back M (BM.isFrame l) (by rw [e]; exact hmem) (by rw [e]; exact hgood) (h := h)
    ⟨fun k => by rw [e]; exact hnorm k, hh, fun p k hp => ⟨1, one_ne_zero, fun m => ?_⟩⟩
  rw [e, one_mul]
  exact flagPt_step M (BM.F l) (FC.bvec BM l b) h hp m

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem _root_.GlobalTheory.T.base_vector_properties : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q), ∀ b ∈ BM.O l, FC.bvec BM l b ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt (BM.F l) (mCoordIdeal (FC.bvec BM l b)) ∧ (∀ k, FC.bvec BM l b ⟨k, (BM.F l).c k⟩ = 1) ∧ SameOrbit (FC.bvec BM l b) (BM.Rb.lift b b) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec_good | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec_good | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec_good <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem _root_.GlobalTheory.T.two_point_fibre_chart_fifth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ (p : Ψ × Fin N) (z : Fin (d + 1) → ℂ), Fin.tail z ∈ Un → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ((FA.S.comap some).potH p).φ (ΦYn z) (ΦYn z') = potAt BM l p (bp (Fin.tail z')) (flagAt H τ ca cb (z' 0) (Fin.tail z') p.1) + (Hh z').re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.fibre_member_potential | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.fibre_member_potential | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.fibre_member_potential <;> assumption)
end
