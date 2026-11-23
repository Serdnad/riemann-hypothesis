module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle476
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle474
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle433
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle466
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle417
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.Bundle007
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.Bundle006
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.Bundle008
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ParUniq
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.Bundle002
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.WDBasic
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CharZeroAdicCompletion
import GroundTheory.LocalFields.PadicLogSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {r : IrrGL (k := w.adicCompletion E) → WD h}

private theorem charPol_seg (H : CuspT a ha r) (Δ : Segment (w.adicCompletion E)) (σ : Weil h) :
    (((r Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len)).charPol σ
      = (Δ.ms.map fun y => (r y).charPol σ).prod := by
  have hspecial (x : WD h) (l : ℕ) :
      ((x.lpTw (((l : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) l)).charPol σ =
        ((Multiset.range l).map fun j : ℕ => (x.lpTw j).charPol σ).prod := by
    induction x using WD.ind with
    | hP n a =>
      have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ReciprocityTheory.Gal.one_lt_normV w).ne_bot
      rw [WD.lpSp, WD.lpTw_mk, WD.lpChar_mk, WD.charPol_mk, WDRep.tensor_ρ, WDRep.sp_ρ,
        GlobalTheory.WeilDeligne.SpCharpoly.charpoly_map_diagEnd]
      change _ = ∏ j ∈ Finset.range l, ((WD.mk a).lpTw (j : ℕ)).charPol σ
      rw [← Fin.prod_univ_eq_prod_range (fun j : ℕ => ((WD.mk a).lpTw (j : ℕ)).charPol σ)]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [WD.lpTw_mk, WD.charPol_mk, WDRep.tw_ρ, WDRep.tw_ρ, smul_smul, ← mul_zpow, WDRep.spEig,
        coe_qPow, ← Complex.cpow_add _ _ hq, ← Complex.ofReal_add, sub_add_cancel]
  rw [hspecial (r Δ.first) Δ.len, Segment.ms, Multiset.map_map]
  have h1 : ∀ j : Fin Δ.len, (r (Δ.term j)).charPol σ = ((r Δ.first).lpTw ((j : ℕ) : ℝ)).charPol σ := by
    intro j
    rw [Segment.term, show (((j : ℕ) : ℂ)) = ((((j : ℕ) : ℝ)) : ℂ) by push_cast; rfl, H.nu _ Δ.isCusp_first]
  change _ = ∏ j : Fin Δ.len, (fun y => (r y).charPol σ) (Δ.term j)
  simp only [h1]
  rw [Fin.prod_univ_eq_prod_range (fun j => ((r Δ.first).lpTw (j : ℝ)).charPol σ) Δ.len]
  rfl

private theorem dim_charPol {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : CuspT a ha r) (L : IsLExt r rc)
    (x : IrrGL (k := w.adicCompletion E)) :
    (rc x).lpDim = x.1 ∧ ∃ s, HasSupport x.rep s ∧ (∀ y ∈ s, y.IsCusp) ∧
      ∀ σ, (rc x).charPol σ = (s.map fun y => (r y).charPol σ).prod := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨𝔪, hm⟩ := Pr.exh (w.adicCompletion E) x
  have hs : HasSupport x.rep (msupp 𝔪) := GlobalTheory.LocGL.hasSupport_msupp_of_isL Pr.zel _ 𝔪 x hm
  have hcp : ∀ σ, (rc x).charPol σ = ((msupp 𝔪).map fun y => (r y).charPol σ).prod := by
    intro σ
    rw [L 𝔪.toList x (by rw [Multiset.coe_toList]; exact hm), segSum, CuspExt.charPol_sumList, List.map_map,
      msupp, Multiset.map_bind, Multiset.prod_bind]
    have hl : ∀ (l : List (Segment (w.adicCompletion E))) (F : Segment (w.adicCompletion E) → ℂ[X]),
        (l.map F).prod = ((l : Multiset _).map F).prod := fun l F => by rw [Multiset.map_coe, Multiset.prod_coe]
    rw [hl, Multiset.coe_toList]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun Δ _ => charPol_seg H Δ σ)
  refine ⟨?_, msupp 𝔪, hs, fun y hy => hs.isCusp hy, hcp⟩
  rw [← WD.charPol_natDegree (rc x) 1, hcp, Polynomial.natDegree_multiset_prod_of_monic _
    (fun f hf => by obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hf; exact WD.charPol_monic _ _), Multiset.map_map]
  have h2 : ((msupp 𝔪).map ((fun p : ℂ[X] => p.natDegree) ∘ fun y => (r y).charPol 1)) = (msupp 𝔪).map Sigma.fst :=
    Multiset.map_congr rfl fun y hy => by
      simp only [Function.comp_apply, WD.charPol_natDegree]
      exact H.dim y (hs.isCusp hy)
  rw [h2, hs.sum_fst, Fintype.card_fin]

end UpperTheory.Zero.LLC

theorem UpperTheory.Zero.LLC.extDim :
    UpperTheory.Zero.LLC.ExtDim := by
  intro E Ω _ _ _ _ _ A w h a ha r rc H L x
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨hd, s, hs, hc, hcp⟩ := dim_charPol H L x
  refine ⟨⟨hd, s, hs, hc, hcp⟩, fun ω hω σ => ?_⟩
  obtain ⟨f, hf, hprod⟩ := GlobalTheory.T.centralCharacter_eq_prod_supercuspidalSupport Pr.bz (w.adicCompletion E) x s ω hs hω
  have he : ((rc x).eig σ).prod = (s.map fun y => ((r y).eig σ).prod).prod := by
    rw [WD.eig, hcp, prod_roots_prod_of_monic s (fun y => (r y).charPol σ) fun y => WD.charPol_monic _ _]
    rfl
  have hw : ((ω (a σ) : ℂˣ) : ℂ) = (s.map fun y => ((f y (a σ) : ℂˣ) : ℂ)).prod := by
    rw [hprod, ← Units.coeHom_apply, map_multiset_prod, Multiset.map_map]
    rfl
  constructor
  · have hn : ∀ m : Multiset ℂ, ‖m.prod‖ = (m.map fun z => ‖z‖).prod :=
      fun m => map_multiset_prod (normHom (α := ℂ)) m
    rw [he, hw, hn, hn, Multiset.map_map, Multiset.map_map]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun y hy => H.absCentral y (hc y hy) (f y) (hf y hy) σ)
  · rintro ⟨s', hs', hg⟩
    obtain rfl := (goodSeg (w.adicCompletion E)).2.2 x _ _ hs' hs
    rw [he, hw]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun y hy => H.central y (hc y hy) (hg y hy) (f y) (hf y hy) σ)
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

section Classes

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]

private theorem tw_tw (y : IrrGL (k := k)) {χ χ' : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) (hχ' : IsSmoothChar χ')
    (h'' : IsSmoothChar (χ * χ')) : (y.tw χ hχ).tw χ' hχ' = y.tw (χ * χ') h'' :=
  ((clBasic k y).2.1 χ hχ).2.2.2.1 χ' hχ' h''

private theorem tw_one (y : IrrGL (k := k)) (h1 : IsSmoothChar (1 : kˣ →* ℂˣ)) : y.tw 1 h1 = y :=
  (clBasic k y).2.2.1 h1

private theorem tw_congr (y : IrrGL (k := k)) {χ χ' : kˣ →* ℂˣ} (e : χ = χ') (hχ : IsSmoothChar χ)
    (hχ' : IsSmoothChar χ') : y.tw χ hχ = y.tw χ' hχ' := by
  subst e; rfl

private theorem tw_tw_inv' (y : IrrGL (k := k)) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    (y.tw χ hχ).tw χ⁻¹ hχ.inv = y := by
  rw [tw_tw y hχ hχ.inv (hχ.mul hχ.inv), tw_congr y (mul_inv_cancel χ) _ isSmoothChar_one, tw_one]

private theorem eq_tw_of_tw_eq {y y' : IrrGL (k := k)} {χ χ' : kˣ →* ℂˣ} {hχ : IsSmoothChar χ}
    {hχ' : IsSmoothChar χ'} (e : y.tw χ hχ = y'.tw χ' hχ') :
    y' = y.tw (χ * χ'⁻¹) (hχ.mul hχ'.inv) := by
  rw [← tw_tw y hχ hχ'.inv, e, tw_tw_inv']

end Classes

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem lpOfChar_congr' {ξ ξ' : Weil h →* ℂˣ} (e : ξ = ξ') (hξ : IsSmooth ξ) (hξ' : IsSmooth ξ') :
    WD.lpOfChar h ξ hξ = WD.lpOfChar h ξ' hξ' := by
  subst e; rfl

private theorem lpTwist_congr' (V : WD h) {ξ ξ' : Weil h →* ℂˣ} (e : ξ = ξ') (hξ : IsSmooth ξ)
    (hξ' : IsSmooth ξ') : V.lpTwist ξ hξ = V.lpTwist ξ' hξ' := by
  subst e; rfl

private theorem lpTwist_lpTwist' (V : WD h) {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a)
    {χ χ' : (w.adicCompletion E)ˣ →* ℂˣ} (hχ : IsSmoothChar χ) (hχ' : IsSmoothChar χ')
    (h'' : IsSmoothChar (χ * χ')) :
    (V.lpTwist (χ.comp a) (ha.smooth hχ)).lpTwist (χ'.comp a) (ha.smooth hχ') =
      V.lpTwist ((χ * χ').comp a) (ha.smooth h'') := by
  have e : (χ * χ').comp a = χ.comp a * χ'.comp a := MonoidHom.mul_comp _ _ _
  exact (((wDBasic E Ω A w h V).2.2.2.2.2.2.2.2 (χ.comp a) (ha.smooth hχ)).2.2.2.1 (χ'.comp a)
    (ha.smooth hχ') (e ▸ ha.smooth h'')).trans (lpTwist_congr' V e.symm _ _)

private def Rel (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (x : IrrGL (k := w.adicCompletion E)) (V : WD h) : Prop :=
  (∃ χ hχ, x = .ofChar χ hχ ∧ V = WD.lpOfChar h (χ.comp a) (ha.smooth hχ)) ∨
  ((∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i) ∧
    ∃ (y₀ : IrrGL (k := w.adicCompletion E)) (V₀ : WD h) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ),
      y₀.IsCusp ∧ DZ y₀ ∧ Par a y₀ V₀ ∧ x = y₀.tw χ hχ ∧ V = V₀.lpTwist (χ.comp a) (ha.smooth hχ))

private theorem twist_eq_of_tw_eq {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a)
    (hq : ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i)
    {y₀ y₁ : IrrGL (k := w.adicCompletion E)} {V₀ V₁ : WD h} {χ χ₁ : (w.adicCompletion E)ˣ →* ℂˣ}
    {hχ : IsSmoothChar χ} {hχ₁ : IsSmoothChar χ₁}
    (c : y₀.IsCusp) (d : DZ y₀) (p : Par a y₀ V₀) (c₁ : y₁.IsCusp) (d₁ : DZ y₁) (p₁ : Par a y₁ V₁)
    (e : y₀.tw χ hχ = y₁.tw χ₁ hχ₁) :
    V₀.lpTwist (χ.comp a) (ha.smooth hχ) = V₁.lpTwist (χ₁.comp a) (ha.smooth hχ₁) := by
  obtain ⟨g, hg, i, hi⟩ := hq
  haveI := hg
  have hy := eq_tw_of_tw_eq e
  have hψ : IsSmoothChar (χ * χ₁⁻¹) := hχ.mul hχ₁.inv
  have pos : 0 < y₀.1 := (clBasic _ y₀).2.2.2.1 c
  have tame : TameChar (χ * χ₁⁻¹) := (twTame _ y₀ _ hψ pos d).1 (hy ▸ d₁)
  have pt := parTw E Ω A w h a ha g i hi y₀ c d V₀ p _ hψ tame
  have hV : V₀.lpTwist ((χ * χ₁⁻¹).comp a) (ha.smooth hψ) = V₁ :=
    (parUniq E Ω A w h a ha g i hi y₁ c₁ d₁ V₁ p₁).1 _ (hy ▸ pt)
  rw [← hV, lpTwist_lpTwist' V₀ ha hψ hχ₁ (hψ.mul hχ₁)]
  exact lpTwist_congr' V₀ (by rw [inv_mul_cancel_right]) _ _

private theorem ofChar_eq_of_tw_eq {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a)
    (hq : ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i)
    {ψ χ : (w.adicCompletion E)ˣ →* ℂˣ} {hψ : IsSmoothChar ψ} {hχ : IsSmoothChar χ}
    {y₀ : IrrGL (k := w.adicCompletion E)} {V₀ : WD h} (c : y₀.IsCusp) (d : DZ y₀) (p : Par a y₀ V₀)
    (e : IrrGL.ofChar ψ hψ = y₀.tw χ hχ) :
    WD.lpOfChar h (ψ.comp a) (ha.smooth hψ) = V₀.lpTwist (χ.comp a) (ha.smooth hχ) := by
  obtain ⟨g, hg, i, hi⟩ := hq
  haveI := hg
  have hψ' : IsSmoothChar (ψ * χ⁻¹) := hψ.mul hχ.inv
  have po := parOne E Ω A w h a ha (ψ * χ⁻¹) hψ'
  have hy : y₀ = .ofChar (ψ * χ⁻¹) hψ' := by
    have h1 := tw_tw_inv' y₀ hχ
    rw [← e] at h1
    rw [← h1]
    exact ((parOne E Ω A w h a ha ψ hψ).2.2.2.2.2.2.1 χ⁻¹ hχ.inv hψ').1
  have tame : TameChar (ψ * χ⁻¹) := po.2.2.2.2.1.1 (hy ▸ d)
  have hV : WD.lpOfChar h ((ψ * χ⁻¹).comp a) (ha.smooth hψ') = V₀ :=
    (parUniq E Ω A w h a ha g i hi y₀ c d V₀ p).1 _ (hy ▸ po.2.2.2.2.2.1 tame)
  rw [← hV, (po.2.2.2.2.2.2.1 χ hχ (hψ'.mul hχ)).2]
  exact lpOfChar_congr' (by rw [inv_mul_cancel_right]) _ _

private theorem rel_unique {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a)
    {x : IrrGL (k := w.adicCompletion E)} {V V' : WD h} (H : Rel a ha x V) (H' : Rel a ha x V') : V = V' := by
  rcases H with ⟨χ, hχ, e, rfl⟩ | ⟨hq, y₀, V₀, χ, hχ, c, d, p, e, rfl⟩ <;>
    rcases H' with ⟨χ', hχ', e', rfl⟩ | ⟨hq', y₁, V₁, χ₁, hχ₁, c₁, d₁, p₁, e', rfl⟩
  · have : χ = χ' := (parOne E Ω A w h a ha χ hχ).2.2.2.2.2.2.2.2 χ' hχ' (e.symm.trans e')
    subst this
    rfl
  · exact ofChar_eq_of_tw_eq ha hq' c₁ d₁ p₁ (e.symm.trans e')
  · exact (ofChar_eq_of_tw_eq ha hq c d p (e'.symm.trans e)).symm
  · exact twist_eq_of_tw_eq ha hq c d p c₁ d₁ p₁ (e.symm.trans e')

private theorem rel_tw {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a)
    {x : IrrGL (k := w.adicCompletion E)} {V : WD h} (H : Rel a ha x V)
    {χ : (w.adicCompletion E)ˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    Rel a ha (x.tw χ hχ) (V.lpTwist (χ.comp a) (ha.smooth hχ)) := by
  rcases H with ⟨ψ, hψ, rfl, rfl⟩ | ⟨hq, y₀, V₀, ψ, hψ, c, d, p, rfl, rfl⟩
  · have := (parOne E Ω A w h a ha ψ hψ).2.2.2.2.2.2.1 χ hχ (hψ.mul hχ)
    exact Or.inl ⟨ψ * χ, hψ.mul hχ, this.1, this.2⟩
  · exact Or.inr ⟨hq, y₀, V₀, ψ * χ, hψ.mul hχ, c, d, p, tw_tw y₀ hψ hχ (hψ.mul hχ),
      lpTwist_lpTwist' V₀ ha hψ hχ (hψ.mul hχ)⟩

private theorem rel_of_good {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a)
    {x : IrrGL (k := w.adicCompletion E)} (c : x.IsCusp) (gd : GoodCusp x) : ∃ V, Rel a ha x V := by
  rcases gd with h1 | ⟨hq, y₀, χ, hχ, hfix, rfl⟩
  · obtain ⟨-, χ, hχ, e⟩ := (clBasic _ x).2.2.2.2.1 h1
    exact ⟨_, Or.inl ⟨χ, hχ, e, rfl⟩⟩
  · have c₀ : y₀.IsCusp := (((clBasic _ y₀).2.1 χ hχ).2.1).1 c
    obtain ⟨g, hg, i, hi⟩ := id hq
    haveI := hg
    obtain ⟨V₀, p⟩ := parEx E Ω A w h a ha g i hi y₀ c₀ hfix
    exact ⟨_, Or.inr ⟨hq, y₀, V₀, χ, hχ, c₀, hfix, p, rfl, rfl⟩⟩

theorem goodMap : GoodMap := by
  intro E Ω _ _ _ _ _ A w h a ha
  haveI : Nonempty (WD h) := ⟨WD.lpOfChar h (MonoidHom.comp 1 a) (ha.smooth isSmoothChar_one)⟩
  have key : ∀ {x V}, Rel a ha x V → Classical.epsilon (Rel a ha x) = V := fun H =>
    rel_unique ha (Classical.epsilon_spec ⟨_, H⟩) H
  refine ⟨fun x => Classical.epsilon (Rel a ha x), ?_, ?_, ?_⟩
  · intro χ hχ
    exact key (Or.inl ⟨χ, hχ, rfl, rfl⟩)
  · intro x c gd χ hχ
    obtain ⟨V, hV⟩ := rel_of_good ha c gd
    show Classical.epsilon _ = (Classical.epsilon (Rel a ha x)).lpTwist _ _
    rw [key hV, key (rel_tw ha hV hχ)]
  · intro hq y c d
    obtain ⟨g, hg, i, hi⟩ := id hq
    haveI := hg
    obtain ⟨V, p⟩ := parEx E Ω A w h a ha g i hi y c d
    have hV : Rel a ha y V := Or.inr ⟨hq, y, V, 1, isSmoothChar_one, c, d, p, (tw_one y _).symm,
      (((wDBasic E Ω A w h V).2.2.2.2.2.2.2.2 _ _).2.2.2.2.1 (MonoidHom.one_comp a)).symm⟩
    show Par a y (Classical.epsilon (Rel a ha y))
    rw [key hV]
    exact p

end UpperTheory.Zero.LLC

end
end
