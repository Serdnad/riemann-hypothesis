module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle051
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle137
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle053
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle138
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle110
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle102
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle035
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.Bundle003
public import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle143
import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.divPowerEnvelope_mem_ainfAdjoinBeta : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), ϖ.untilt = ((l : ℕ) : Per.OC l) →
  ∀ a : Per.Acris0 l, (a : Per.AinfP l) ∈ Sa ϖ := by
  first | exact @GlobalTheory.Pst.StLat.acris0_le_sa | exact GlobalTheory.Pst.StLat.acris0_le_sa | (intros; apply GlobalTheory.Pst.StLat.acris0_le_sa <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.betaImageDeRhamPlus_dvd_of_lAdic_residues : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), Per.kerP l = Ideal.span {beta ϖ} →
  (∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n}) →
  ∀ y : Per.BdRp l, (∀ k : ℕ, ∃ s ∈ Sg ϖ, betaD ϖ ∣ y - ((l : ℕ) : Per.BdRp l) ^ k * s) → betaD ϖ ∣ y := by
  first | exact @GlobalTheory.Pst.StLat.betaD_dvd_of_res | exact GlobalTheory.Pst.StLat.betaD_dvd_of_res | (intros; apply GlobalTheory.Pst.StLat.betaD_dvd_of_res <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LocLanglands
namespace TemperedRec

theorem tempered_lpSum : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x y : WD h), x.tempered → y.tempered → (x.lpSum y).tempered := GlobalTheory.T.tempered_direct_sum

theorem tempered_lpChar_lpSp : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), x.mono0 → (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ x.eig φ, ‖α‖ = 1) → ∀ l : ℕ, (x.lpChar (WD.lpSp (h := h) l)).tempered := by
  apply GlobalTheory.WeilDeligne.WD.tempered_lpChar_lpSp_of_mono0 <;> assumption

theorem norm_eig_eq_of_isIrrWD : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), IsIrrWD x → ∀ φ : Weil h, deg φ = 1 → ∀ α ∈ x.eig φ, ∀ β ∈ x.eig φ, ‖α‖ = ‖β‖ := GlobalTheory.T.irreducible_wd_eigen_equal_norm

theorem prod_eig_lpChar_lpSp : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h) (l : ℕ) (σ : Weil h), ((x.lpChar (WD.lpSp (h := h) l)).eig σ).prod = ((x.eig σ).prod) ^ l := GlobalTheory.T.lp_character_eigen_product

theorem not_precedes_of_norm_eig : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRec h rc → ∀ Δ Δ' : Segment (w.adicCompletion E), (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).eig φ, ‖α‖ = 1) → (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ ((rc Δ'.first).lpTw (((Δ'.len : ℝ) - 1) / 2)).eig φ, ‖α‖ = 1) → ¬ Δ.Precedes Δ' := GlobalTheory.T.segment_sum_tempered

theorem monodromy_zero_of_irreducible_weilDeligne : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), IsIrrWD x → x.mono0 := by
  intro E Ω _ _ _ _ _ A w h x ⟨n, a, hx, hirr⟩
  subst hx
  rw [WD.monodromyZero_ofWeilDeligneRepClass_iff]
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans (one_lt_normV w)).ne'
  let S : Subrepresentation a.ρ := ⟨LinearMap.ker a.N, fun σ v hv => by
    have h1 := a.comm_apply σ v
    rw [LinearMap.mem_ker.1 hv, map_zero] at h1
    exact LinearMap.mem_ker.2 ((smul_eq_zero.1 h1.symm).resolve_left (zpow_ne_zero _ hq))⟩
  rcases hirr.eq_bot_or_eq_top S with hS | hS
  · exfalso
    have hinj : Function.Injective a.N := by
      rw [← LinearMap.ker_eq_bot]
      exact congrArg Subrepresentation.toSubmodule hS
    obtain ⟨m, hm⟩ := a.nilpotent
    have hinj' : Function.Injective (a.N ^ m) := by
      rw [FunLike.coe_pow_eq_iterate]; exact hinj.iterate m
    rw [hm] at hinj'
    have := Model.nontrivial_of_isIrreducible hirr
    obtain ⟨v, hv⟩ := exists_ne (0 : Fin n → ℂ)
    exact hv (hinj' (a₁ := v) (a₂ := 0) (by simp))
  · refine LinearMap.ext fun v => ?_
    have : v ∈ S.toSubmodule := by rw [hS]; trivial
    exact LinearMap.mem_ker.1 this

theorem tempered_lpZero {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) : (WD.lpZero (h := h)).tempered :=
  (WD.tempered_mk _).mpr ((WD.tempered_diag_iff _).mpr fun i => i.elim0)

theorem tempered_sumList {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} :
    ∀ l : List (WD h), (∀ y ∈ l, y.tempered) → (sumList l).tempered
  | [], _ => tempered_lpZero h
  | y :: l, H => tempered_lpSum E Ω A w h y (sumList l) (H y (by simp))
      (tempered_sumList l fun z hz => H z (by simp [hz]))

theorem norm_centralChar_eq_one {k : Type} [CommRing k] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    [Nontrivial V] {π : Representation ℂ (GL (Fin n) k) V} {ω : kˣ →* ℂˣ} (hu : IsUnitarisable π)
    (hω : HasCentralChar π ω) (z : kˣ) : ‖(ω z : ℂ)‖ = 1 := by
  obtain ⟨B, -, hpos, hinv⟩ := hu
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h1 := hinv (Matrix.GeneralLinearGroup.scalar (Fin n) z) v v
  rw [hω] at h1
  simp only [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul] at h1
  have hB : B v v ≠ 0 := fun h0 => by have := hpos v hv; rw [h0] at this; simp at this
  have h2 : ((ω z : ℂ) * starRingEnd ℂ (ω z : ℂ)) * B v v = 1 * B v v := by linear_combination h1
  have h3 := mul_right_cancel₀ hB h2
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h3
  have h4 : ‖(ω z : ℂ)‖ ^ 2 = 1 := by exact_mod_cast h3
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4

theorem norm_eq_one_of_norm_prod {s : Multiset ℂ} (hp : ‖s.prod‖ = 1) (hs : ∀ α ∈ s, ∀ β ∈ s, ‖α‖ = ‖β‖) {α : ℂ}
    (hα : α ∈ s) : ‖α‖ = 1 := by
  have hmap : s.map (fun β => ‖β‖) = Multiset.replicate (Multiset.card s) ‖α‖ := by
    rw [Multiset.eq_replicate]
    refine ⟨by simp, fun r hr => ?_⟩
    obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.1 hr
    exact (hs α hα β hβ).symm
  have h1 : ‖s.prod‖ = (s.map (fun β => ‖β‖)).prod := map_multiset_prod (normHom : ℂ →*₀ ℝ) s
  rw [hmap, Multiset.prod_replicate, hp] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Multiset.card_pos_iff_exists_mem.2 ⟨α, hα⟩).ne').1 h1.symm

theorem isCosocle_rep_cl {G : Type} [Group G] [TopologicalSpace G] (σ : IrrRep G) {V : Type} [AddCommGroup V]
    [Module ℂ V] {π : Representation ℂ G V} (e : σ.ρ.Equiv π) : IsCosocle σ.cl.rep.ρ π := by
  obtain ⟨f⟩ := σ.nonempty_equiv_rep
  exact (isCosocle_self σ.irr).of_equiv f.symm e

theorem norm_eig_segParam {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {rc : IrrGL (k := w.adicCompletion E) → WD h} (hrc : IsRec h rc) (δ : IrrGL (k := w.adicCompletion E))
    (Δ : Segment (w.adicCompletion E)) (hΔ : IsLSeg Δ δ.rep) (hu : IsUnitarisable δ.rep) :
    ∀ φ : Weil h, deg φ = 1 → ∀ α ∈ ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).eig φ, ‖α‖ = 1 := by
  obtain ⟨a, ha, ε, -, H⟩ := hrc
  intro φ hφ
  have hz : (rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2) = rc (Δ.first.nu ((((Δ.len : ℝ) - 1) / 2 : ℝ) : ℂ)) :=
    (H.nu_eq _ _).symm
  have hirr : IsIrrWD ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)) := by
    rw [hz]; exact (H.cusp _).1 (Δ.isCusp_first.nu _)
  have hδ : rc δ = ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len) := by
    have hL : IsL ((([Δ] : List (Segment (w.adicCompletion E))) : Multiset (Segment (w.adicCompletion E)))) δ.rep := by
      simpa using hΔ.isL
    rw [H.langlands [Δ] δ hL]
    exact WD.lpSum_zero _
  obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar δ.2.rep.smooth δ.2.rep.irr
  have : Nontrivial δ.2.rep.V := Model.nontrivial_of_isIrreducible δ.2.rep.irr
  have hc := H.central δ ω hω φ
  rw [hδ, prod_eig_lpChar_lpSp] at hc
  have hn : ‖((((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).eig φ).prod)‖ ^ Δ.len = 1 := by
    rw [← norm_pow, hc]; exact norm_centralChar_eq_one hu hω _
  have hp1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) Δ.len_pos.ne').1 hn
  intro α hα
  exact norm_eq_one_of_norm_prod hp1 (norm_eig_eq_of_isIrrWD E Ω A w h _ hirr φ hφ) hα

end TemperedRec


open TemperedRec in
theorem tempered_of_isTemperedGL : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRec h rc → ∀ (n : ℕ) (σ : IrrRep (GL (Fin n) (w.adicCompletion E))), GlobalTheory.LocGL.IsTemperedGL σ.ρ → (rc (cls σ)).tempered := by
  intro E Ω _ _ _ _ _ A w h rc hrc n σ hσ
  have hrc' := hrc
  obtain ⟨a, ha, ε, -, H⟩ := hrc'
  obtain ⟨m, δ, hd, hδ, ⟨e⟩⟩ := hσ
  choose Δ hΔ using fun i => (hδ i).1
  have hunit := fun i => norm_eig_segParam hrc (δ i) (Δ i) (hΔ i) (hδ i).2
  have hL : IsL (((List.ofFn Δ : List (Segment (w.adicCompletion E)))) : Multiset (Segment (w.adicCompletion E)))
      (cls σ).rep := by
    refine ⟨m, δ, hd, ⟨Δ, ⟨?_, fun i j _ hp => not_precedes_of_norm_eig E Ω A w h rc hrc (Δ i) (Δ j) (hunit i) (hunit j) hp⟩, hΔ⟩, ?_⟩
    · exact Fin.univ_val_map Δ
    · exact isCosocle_rep_cl σ e
  rw [H.langlands _ _ hL]
  refine tempered_sumList _ fun y hy => ?_
  obtain ⟨Γ, hΓ, rfl⟩ := List.mem_map.1 hy
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hΓ
  have hz : (rc (Δ i).first).lpTw ((((Δ i).len : ℝ) - 1) / 2) = rc ((Δ i).first.nu (((((Δ i).len : ℝ) - 1) / 2 : ℝ) : ℂ)) :=
    (H.nu_eq _ _).symm
  have hirr : IsIrrWD ((rc (Δ i).first).lpTw ((((Δ i).len : ℝ) - 1) / 2)) := by
    rw [hz]; exact (H.cusp _).1 ((Δ i).isCusp_first.nu _)
  exact tempered_lpChar_lpSp E Ω A w h _ (monodromy_zero_of_irreducible_weilDeligne E Ω A w h _ hirr) (hunit i) _

end GlobalTheory.LocLanglands
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitCoord

section General

variable {R T : Type} [CommRing R] [CommRing T] [Algebra R T]

theorem trace_mul_idem (hi : Function.Injective (algebraMap R T)) (c : T →+* T)
    (ht : ∀ z, algebraMap R T (Algebra.trace R T z) = z + c z) {e : T} (h1 : e * e = e) (h2 : e * c e = 0) (x y : T) :
    Algebra.trace R T (e * (x * y)) = Algebra.trace R T (e * x) * Algebra.trace R T (e * y) := by
  apply hi
  have hc : c e * c e = c e := by rw [← map_mul, h1]
  rw [RingHom.map_mul, ht, ht, ht]
  simp only [map_mul]
  linear_combination (-(x * y)) * h1 - (c x * c y) * hc - (x * c y + c x * y) * h2

theorem idem_mul_trace (c : T →+* T)
    (ht : ∀ z, algebraMap R T (Algebra.trace R T z) = z + c z) {e : T} (h1 : e * e = e) (h2 : e * c e = 0)
    {α : R} (h3 : e + c e = algebraMap R T α) (x : T) :
    e * algebraMap R T (α * Algebra.trace R T (e * x)) = e * x := by
  rw [map_mul, ht, ← h3, map_mul]
  linear_combination ((e + 1) * x) * h1 + (e * x + e * c x + c e * c x) * h2

theorem trace_idem_mul (hi : Function.Injective (algebraMap R T)) (c : T →+* T)
    (ht : ∀ z, algebraMap R T (Algebra.trace R T z) = z + c z) {e : T}
    {α : R} (h3 : e + c e = algebraMap R T α) (b : R) :
    Algebra.trace R T (e * algebraMap R T b) = b * α := by
  have : Algebra.trace R T e = α := hi (by rw [ht, h3])
  rw [mul_comm, ← Algebra.smul_def, map_smul, this, smul_eq_mul]

theorem exists_hom (hi : Function.Injective (algebraMap R T)) (c : T →+* T)
    (ht : ∀ z, algebraMap R T (Algebra.trace R T z) = z + c z) {e : T} (h1 : e * e = e) (h2 : e * c e = 0)
    {α : R} (h3 : e + c e = algebraMap R T α) {S K : Type} [CommRing S] [CommRing K] [Algebra S R] [Algebra S K]
    (φ : R →ₐ[S] K) (hα : φ α = 1) :
    ∃ π : T →+* K, ∀ x, π x = φ (Algebra.trace R T (e * x)) :=
  ⟨{ toFun := fun x => φ (Algebra.trace R T (e * x))
     map_one' := by
       have := trace_idem_mul hi c ht h3 1
       rw [RingHom.map_one, one_mul] at this
       rw [this, hα]
     map_mul' := fun x y => by rw [trace_mul_idem hi c ht h1 h2, map_mul]
     map_zero' := by rw [mul_zero, map_zero, map_zero]
     map_add' := fun x y => by rw [mul_add, map_add (f := _), map_add (f := _)] }, fun _ => rfl⟩

end General

section Single

variable {F : Type} [Field F] [NumberField F]

theorem evalV_single (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) : evalV F v (singleV F v a) = a := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v a

theorem evalV_single_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (a : Fv F v) : evalV F w (singleV F v a) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) a h

theorem single_evalV {v : HeightOneSpectrum (𝓞 F)} {α : Af F} (h1 : evalV F v α = 1)
    (h2 : ∀ w, w ≠ v → evalV F w α = 0) (b : Af F) : singleV F v (evalV F v b) = α * b := by
  refine RestrictedProduct.ext _ _ fun w => ?_
  change evalV F w (singleV F v (evalV F v b)) = evalV F w (α * b)
  by_cases hw : w = v
  · subst hw
    rw [evalV_single, map_mul, h1, one_mul]
  · rw [evalV_single_ne hw, map_mul, h2 w hw, zero_mul]

theorem single_mem {v : HeightOneSpectrum (𝓞 F)} {a : Fv F v} (ha : a ∈ v.adicCompletionIntegers F) :
    singleV F v a ∈ intAf F := by
  intro w
  by_cases hw : w = v
  · subst hw
    rw [evalV_single]; exact ha
  · rw [evalV_single_ne hw]; exact zero_mem _

end Single

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


variable (F E) in
def finT : AF F ⊗[F] E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom


variable (F E) in
def intT : AddSubgroup (Af F ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}

theorem alg_inj (R : Type) [CommRing R] [Algebra F R] : Function.Injective (algebraMap R (R ⊗[F] E)) :=
  Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective

theorem finT_sig (σ : E →ₐ[F] E) (z : AF F ⊗[F] E) : finT F E (sigR (AF F) σ z) = sigR (Af F) σ (finT F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add a b ha hb => simp only [RingHom.map_add (f := _), ha, hb]
  | tmul a e => rfl

theorem finT_alg (a : AF F) : finT F E (algebraMap (AF F) _ a) = algebraMap (Af F) _ (sndA F a) := rfl

theorem mul_mem_intT {x y : Af F ⊗[F] E} (hx : x ∈ intT F E) (hy : y ∈ intT F E) : x * y ∈ intT F E := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intT F E) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem trace_mem (v : HeightOneSpectrum (𝓞 F)) {x : Af F ⊗[F] E} (hx : x ∈ intT F E) :
    evalV F v (Algebra.trace (Af F) (Af F ⊗[F] E) x) ∈ v.adicCompletionIntegers F := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, y, rfl⟩ := hx
    have h1 : a ⊗ₜ[F] (y : E) = a • ((1 : Af F) ⊗ₜ[F] (y : E)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h3 : Algebra.trace (Af F) (Af F ⊗[F] E) (a ⊗ₜ[F] (y : E)) = a * algebraMap F _ (Algebra.trace F E y) := by
      rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
        LinearMap.trace_baseChange, smul_eq_mul]
    rw [h3, map_mul, AlgHom.commutes]
    refine mul_mem (ha v) ?_
    have hi : IsIntegral ℤ (Algebra.trace F E y) := Algebra.isIntegral_trace y.isIntegral_coe
    exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v (⟨_, hi⟩ : 𝓞 F)
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [map_add (f := _), map_add (f := _)]; exact add_mem h1 h2
  | neg x _ h => rw [map_neg, map_neg]; exact neg_mem h

theorem exists_coord_field (hd : Module.finrank F E = 2) (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e)
    (hf : ∀ e, σ e = e → ∃ f, algebraMap F E f = e) (hI : ∀ z : Af F ⊗[F] E, z * z = z → z ∈ intT F E)
    (e : AF F ⊗[F] E) (h1 : e * e = e) (h2 : e * sigR (AF F) σ e = 0) (v : HeightOneSpectrum (𝓞 F)) (α : Af F)
    (hv : evalV F v α = 1) (hv' : ∀ w, w ≠ v → evalV F w α = 0)
    (h3 : e + sigR (AF F) σ e = algebraMap (AF F) _ (pairA F 0 α)) :
    ∃ (π : Af F ⊗[F] E →+* Fv F v) (s : Fv F v → AF F ⊗[F] E), (∀ x, s (π (finT F E x)) = e * x) ∧
      (∀ a, π (finT F E (s a)) = a) ∧ (∀ x, finT F E (s (π x)) = finT F E e * x) ∧
      (∀ x, finT F E e * x ∈ intT F E ↔ π x ∈ Formalism.UG.Ov F v) ∧
      ∀ x : F, π (finT F E (inclR (F := F) (AF F) (algebraMap F E x))) = algebraMap F (Fv F v) x := by
  have tA := GlobalTheory.FockCompare.SymplVal.trace_tensor hd σ hσ hf (AF F)
  have tf := GlobalTheory.FockCompare.SymplVal.trace_tensor hd σ hσ hf (Af F)
  have tt : ∀ z, Algebra.trace (Af F) (Af F ⊗[F] E) (finT F E z) = sndA F (Algebra.trace (AF F) _ z) := fun z => by
    apply alg_inj (F := F) (E := E)
    rw [tf, ← finT_alg, tA, RingHom.map_add (f := _), finT_sig]
  have g1 : finT F E e * finT F E e = finT F E e := by rw [← RingHom.map_mul, h1]
  have g2 : finT F E e * sigR (Af F) σ (finT F E e) = 0 := by
    rw [← finT_sig, ← RingHom.map_mul, h2, RingHom.map_zero]
  have g3 : finT F E e + sigR (Af F) σ (finT F E e) = algebraMap (Af F) _ α := by
    rw [← finT_sig, ← RingHom.map_add (f := _), h3]; rfl
  have k := fun b => trace_idem_mul (alg_inj _) _ tf g3 b
  obtain ⟨π, hπ⟩ := exists_hom (alg_inj _) _ tf g1 g2 g3 (evalV F v) hv
  have p3 : ∀ x, finT F E e * algebraMap (Af F) _ (singleV F v (π x)) = finT F E e * x := fun x => by
    rw [hπ, single_evalV hv hv']
    exact idem_mul_trace _ tf g1 g2 g3 x
  refine ⟨π, fun a => e * algebraMap (AF F) _ (pairA F 0 (singleV F v a)), fun x => ?_,
    fun a => ?_, fun x => ?_, fun x => ⟨fun h => ?_, fun h => ?_⟩, fun x => ?_⟩
  · refine Eq.trans ?_ (idem_mul_trace _ tA h1 h2 h3 x)
    beta_reduce
    rw [hπ, single_evalV hv hv', ← RingHom.map_mul, tt]
    congr 2
    exact Prod.ext (zero_mul _).symm rfl
  · rw [hπ, RingHom.map_mul, ← mul_assoc, g1, finT_alg, k, map_mul, hv, mul_one]
    exact evalV_single v a
  · rw [RingHom.map_mul, finT_alg]
    exact p3 x
  · rw [hπ]; exact trace_mem v h
  · rw [← p3]
    exact mul_mem_intT (hI _ g1) (AddSubgroup.subset_closure ⟨_, single_mem h, 1, rfl⟩)
  · have : finT F E (inclR (F := F) (AF F) (algebraMap F E x)) = algebraMap (Af F) _ (algebraMap F (Af F) x) := by
      change (sndA F 1) ⊗ₜ[F] (algebraMap F E x) = (algebraMap F (Af F) x) ⊗ₜ 1
      rw [map_one, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    rw [this, hπ, k, map_mul, hv, mul_one, AlgHom.commutes]

end Field

theorem exists_coord : ∀ {D : D7} (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (π : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E →+* Fv D.host.F v) (s : Fv D.host.F v → Formalism.L2.Theta.AE D), (∀ x, s (π (finPart D x)) = e * x) ∧ (∀ a, π (finPart D (s a)) = a) ∧ (∀ x, finPart D (s (π x)) = finPart D e * x) ∧ (∀ x, finPart D e * x ∈ intAE D ↔ π x ∈ Formalism.UG.Ov D.host.F v) ∧ ∀ x : D.host.F, π (finPart D (incA D (algebraMap D.host.F D.host.E x))) = algebraMap D.host.F (Fv D.host.F v) x := by
  rintro D e ⟨h1, h2, v, ε, ⟨α, rfl, hv, hv'⟩, h3⟩
  exact ⟨v, exists_coord_field D.sp.cm.deg2 D.sp.cm.sig (fun e => star_star e) (fun e he => (D.sp.cm.fixed e).1 he)
    (GlobalTheory.AdIdem.idempotent_mem_intAE D) e h1 h2 v α hv hv' h3⟩

end GlobalTheory.SplitCoord

end
end

section


theorem _root_.GlobalTheory.T.unramifiedWeierstrassCurve_transform_coefficients_wellFormed : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]), W.a₁ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₂ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₃ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₄ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₆ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → ∀ s2 : ℂ_[p], s2 ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → Formalism.MainNotions.GL3Theta.CoefWf (Formalism.L2.Th1.B.phW W s2 : MvPowerSeries Unit ℂ_[p]) := by
  first | exact @GlobalTheory.CoefWfUnram.coefWf_phW | exact GlobalTheory.CoefWfUnram.coefWf_phW | (intros; apply GlobalTheory.CoefWfUnram.coefWf_phW <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.card_subspaces_ker_transpose_eq_card_range : ∀ (k : Type) [Field k] (m n j : ℕ) (z : Matrix (Fin m) (Fin n) k), Nat.card {W : Submodule k (Fin m → k) // Module.finrank k W + j = m ∧ W ≤ LinearMap.ker zᵀ.mulVecLin} = Nat.card {W' : Submodule k (Fin m → k) // Module.finrank k W' = j ∧ LinearMap.range z.mulVecLin ≤ W'} := by
  first | exact @GlobalTheory.SplitHecke.card_le_ker_transpose_eq_card_range_le | exact GlobalTheory.SplitHecke.card_le_ker_transpose_eq_card_range_le | (intros; apply GlobalTheory.SplitHecke.card_le_ker_transpose_eq_card_range_le <;> assumption)
end
