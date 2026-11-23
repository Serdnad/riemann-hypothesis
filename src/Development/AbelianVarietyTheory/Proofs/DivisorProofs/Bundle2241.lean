module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1289
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1986
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1835
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1445
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1636
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1525
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2076
public import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.NefEffectiveCones.EventuallyEvalNegOfCoeffNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2177
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1382
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
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
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal

namespace GlobalTheory.DblInt

theorem evDbl_schr {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1)
    {κ κ₁ : Type} [Fintype κ] [Fintype κ₁] (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ₁ → AF F) → ℂ))
    (A₁ B₁ A₂ B₂ : κ → AF F) (a₁ b₁ a₂ b₂ : κ₁ → AF F)
    (h1 : ∀ Φ ∈ schA F κ, T (schr ψ (A₁, B₁) Φ) = schr ψ (a₁, b₁) (T Φ))
    (h2 : ∀ Φ ∈ schA F κ, T (schr ψ (A₂, B₂) Φ) = schr ψ (a₂, b₂) (T Φ))
    (h3 : ∀ φ ∈ schA F (κ ⊕ κ), partR (conjMap T) φ ∈ schA F (κ ⊕ κ₁)) :
    ∀ φ ∈ schA F (κ ⊕ κ), evDbl T (schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ) =
      schr ψ (Sum.elim a₁ a₂, Sum.elim b₁ (-b₂)) (evDbl T φ) := by
  intro φ hφ
  have hconj : ∀ g ∈ schA F κ, conjMap T (schr ψ (A₂, -B₂) g) = schr ψ (a₂, -b₂) (conjMap T g) := by
    intro g hg
    have hs : star g ∈ schA F κ := GlobalTheory.SchAConj.star_mem_schA F κ g hg
    rw [conjMap_apply, conjMap_apply, GlobalTheory.DoublingEvLaw.star_schr' ψ hψ (A₂, B₂) g, h2 _ hs]
    have := GlobalTheory.DoublingEvLaw.star_schr' ψ hψ (a₂, -b₂) (T (star g))
    simpa only [neg_neg] using this
  funext s
  have hΨ := h3 φ hφ
  have hslice := GlobalTheory.DoublingEvLaw.sliceL hΨ (s ∘ Sum.inr + a₂)
  have hinner : (fun x₁ => conjMap T (fun x₂ => schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ (Sum.elim x₁ x₂))
      (s ∘ Sum.inr)) = ψ (-((s ∘ Sum.inr) ⬝ᵥ b₂) - ⅟(2 : AF F) * (a₂ ⬝ᵥ b₂)) •
        schr ψ (A₁, B₁) (fun x₁ => partR (conjMap T) φ (Sum.elim x₁ (s ∘ Sum.inr + a₂))) := by
    funext x₁
    have e1 : (fun x₂ => schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ (Sum.elim x₁ x₂)) =
        ψ (x₁ ⬝ᵥ B₁ + ⅟(2 : AF F) * (A₁ ⬝ᵥ B₁)) • schr ψ (A₂, -B₂) (fun x₂ => φ (Sum.elim (x₁ + A₁) x₂)) := by
      funext x₂
      simp only [schr, Pi.smul_apply, smul_eq_mul, GlobalTheory.DoublingEvLaw.elim_dot, Sum.elim_add_add]
      rw [← mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    rw [e1, map_smul, hconj _ (GlobalTheory.DoublingEvLaw.sliceR hφ _)]
    simp only [Pi.smul_apply, smul_eq_mul, schr, partR_apply, Sum.elim_comp_inl, Sum.elim_comp_inr]
    rw [dotProduct_neg, dotProduct_neg]
    rw [show ∀ p q r : ℂ, p * (q * r) = q * (p * r) from fun p q r => by ring]
    congr 2
    ring_nf
  rw [evDbl_apply, hinner, map_smul, h1 _ hslice]
  simp only [schr, Pi.smul_apply, smul_eq_mul, evDbl_apply, GlobalTheory.DoublingEvLaw.elim_dot, partR_apply, Sum.elim_comp_inl,
    Sum.elim_comp_inr, dotProduct_neg]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  have hs : s ⬝ᵥ Sum.elim b₁ (-b₂) = (s ∘ Sum.inl) ⬝ᵥ b₁ - (s ∘ Sum.inr) ⬝ᵥ b₂ := by
    rw [← Sum.elim_comp_inl_inr s, GlobalTheory.DoublingEvLaw.elim_dot, dotProduct_neg, Sum.elim_comp_inl, Sum.elim_comp_inr,
      sub_eq_add_neg]
  rw [hs]
  ring

theorem adm_congr {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {l l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ}
    (h : ∀ Φ ∈ schA F κ, l Φ = l' Φ) : l ∈ (adeleClass F).adm κ ↔ l' ∈ (adeleClass F).adm κ := by
  have key : ∀ {l l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ}, (∀ Φ ∈ schA F κ, l Φ = l' Φ) →
      l ∈ (adeleClass F).adm κ → l' ∈ (adeleClass F).adm κ := by
    intro l l' h hl g hg
    obtain ⟨T, hT⟩ := hl g hg
    exact ⟨T, fun f => (h _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)).symm.trans (hT f)⟩
  exact ⟨key h, key fun Φ hΦ => (h Φ hΦ).symm⟩

theorem hasDbl_of_tame {F : Type} [Field F] [NumberField F] {E : Type} [CommRing E] [Algebra (AF F) E]
    (c : E →ₐ[AF F] E) {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
    (ψ : AddChar (AF F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E)
    (d d₁ : Darboux (symp c ξ JA JB) κ) (T : ((κ → AF F) → ℂ) ≃ₗ[ℂ] ((κ → AF F) → ℂ))
    (hT : IsGoodInt (adeleClass F) ψ d d₁ T) (ht : IsTame F T.toLinearMap) (hti : IsTame F T.symm.toLinearMap) :
    HasDbl c (adeleClass F) ψ ξ JA JB d d₁ T := by
  intro dd hdd
  obtain ⟨hsp, hheis, hadm, hunit⟩ := hT
  have hS : IsTame F (conjMap T.toLinearMap) := GlobalTheory.DoublingEv.isTame_conjMap F κ κ _ ht
  have hSi : IsTame F (conjMap T.symm.toLinearMap) := GlobalTheory.DoublingEv.isTame_conjMap F κ κ _ hti
  have hR : IsTame F (partR (κ := κ) (conjMap T.toLinearMap)) := GlobalTheory.T.tame_part_right F κ κ κ _ hS
  have hL : IsTame F (partL (κ' := κ) T.toLinearMap) := GlobalTheory.T.tame_part_left F κ κ κ _ ht
  have hRi : IsTame F (partR (κ := κ) (conjMap T.symm.toLinearMap)) := GlobalTheory.T.tame_part_right F κ κ κ _ hSi
  have hLi : IsTame F (partL (κ' := κ) T.symm.toLinearMap) := GlobalTheory.T.tame_part_left F κ κ κ _ hti
  have hD : IsTame F (dblE T).toLinearMap := hR.comp hL
  have hDi : IsTame F (dblE T).symm.toLinearMap := hLi.comp hRi
  have hstar : ∀ φ : (κ → AF F) → ℂ, φ ∈ schA F κ → star φ ∈ schA F κ := fun φ hφ =>
    GlobalTheory.SchAConj.star_mem_schA F κ φ hφ
  have hSsp : ∀ φ, φ ∈ schA F κ ↔ conjE T φ ∈ schA F κ := fun φ => by
    rw [conjE_apply]
    constructor
    · intro h
      exact hstar _ ((hsp _).1 (hstar _ h))
    · intro h
      have h1 : T (star φ) ∈ schA F κ := by simpa using hstar _ h
      simpa using hstar _ ((hsp _).2 h1)
  have hTL : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖T.toLinearMap φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := hunit
  have hSL : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖conjMap T.toLinearMap φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
    intro μ hμ
    obtain ⟨c₀, hc₀⟩ := hunit μ hμ
    refine ⟨c₀, fun φ hφ => ?_⟩
    have h := hc₀ (star φ) (hstar φ hφ)
    simp only [conjMap_apply, Pi.star_apply, enorm_eq_nnnorm, nnnorm_star, LinearEquiv.coe_coe] at h ⊢
    exact h
  refine ⟨dblCo c d₁, dblE T, conjE T, dblCo_isDblCoord c d₁,
    ⟨fun φ => ⟨fun h => hD.mapsTo φ h, fun h => ?_⟩, fun w φ hφ => ?_, fun l => ⟨fun hl => hD.comp_adm hl, fun hl => ?_⟩,
      fun μ hμ => ?_⟩, hSsp, fun φ₁ _ φ₂ _ => evDbl_boxFun T.toLinearMap φ₁ φ₂⟩
  · have := hDi.mapsTo _ h
    rw [show (dblE T).symm.toLinearMap ((dblE T) φ) = φ from (dblE T).symm_apply_apply φ] at this
    exact this
  · obtain ⟨w₁, w₂, rfl⟩ : ∃ w₁ w₂, w = Matrix.fromCols w₁ w₂ := ⟨w.toCols₁, w.toCols₂, (Matrix.fromCols_toCols w).symm⟩
    have e1 : dd.rho ψ (Matrix.fromCols w₁ w₂) =
        schr ψ (Sum.elim (d.e w₁).1 (d.e w₂).1, Sum.elim (d.e w₁).2 (-(d.e w₂).2)) := by
      unfold Darboux.rho; rw [hdd]
    have e2 : (dblCo c d₁).rho ψ (Matrix.fromCols w₁ w₂) =
        schr ψ (Sum.elim (d₁.e w₁).1 (d₁.e w₂).1, Sum.elim (d₁.e w₁).2 (-(d₁.e w₂).2)) := by
      unfold Darboux.rho; rw [dblCo_isDblCoord]
    rw [e1, e2]
    exact evDbl_schr ψ hψ T.toLinearMap _ _ _ _ _ _ _ _ (fun Φ hΦ => hheis w₁ Φ hΦ) (fun Φ hΦ => hheis w₂ Φ hΦ)
      hR.mapsTo φ hφ
  · have := hDi.comp_adm hl
    convert this using 1
    ext φ
    simp
  · obtain ⟨c₁, hc₁⟩ := (GlobalTheory.T.weil_operator_haar_norm_proportional F κ κ T.toLinearMap ht hTL).1 μ hμ
    obtain ⟨c₂, hc₂⟩ := (GlobalTheory.T.weil_operator_haar_norm_proportional F κ κ (conjMap T.toLinearMap) hS hSL).2 μ hμ
    refine ⟨c₁ * c₂, fun Φ hΦ => ?_⟩
    show ∫⁻ x, ‖partL (κ' := κ) T.toLinearMap (partR (κ := κ) (conjMap T.toLinearMap) Φ) x‖ₑ ^ 2 ∂μ = _
    rw [hc₁ _ (hR.mapsTo Φ hΦ), hc₂ Φ hΦ, mul_assoc]

theorem main : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ T : Fn F n d ≃ₗ[ℂ] Fn F n d, (∀ Φ ∈ schA F (Fin n × Fin d), T Φ = e Φ) →
      HasDbl (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) M.co M₁.co T := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij T hTe
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hTs : ∀ x, x ∈ schA F (Fin n × Fin d) ↔ T x ∈ schA F (Fin n × Fin d) := fun x => by
    constructor
    · intro hx
      rw [hTe x hx]
      exact hbij.mapsTo hx
    · intro hx
      obtain ⟨y, hy, hyx⟩ := hbij.surjOn hx
      have : T y = T x := by rw [hTe y hy, hyx]
      rw [← T.injective this]
      exact hy
  have hgood : IsGoodInt (adeleClass F) B.ψ M.co M₁.co T := by
    refine ⟨hTs, fun w Φ hΦ => ?_, fun l => ?_, fun μ hμ => ?_⟩
    · have hm : M.co.rho B.ψ w Φ ∈ schA F (Fin n × Fin d) :=
        GlobalTheory.T.schroedinger_preserves_adelic_schwartz F B.ψ hpair.base.std _ (M.co.e w) Φ hΦ
      have := hev.Heisenberg₂ w Φ hΦ
      rw [h1, h1', Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at this
      rw [hTe _ hm, hTe _ hΦ, this]
    · refine (GlobalTheory.T.model_evaluation_bijective_schwartz hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij l).trans
        (adm_congr ?_)
      intro Φ hΦ
      simp [hTe Φ hΦ]
    · obtain ⟨c, hc⟩ := GlobalTheory.T.model_evaluation_preserves_admissible hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij μ hμ
      exact ⟨c, fun Φ hΦ => by rw [hTe Φ hΦ]; exact hc Φ hΦ⟩
  have ht : IsTame F T.toLinearMap := by
    intro g hg
    obtain ⟨ι, inst, P, g', hg', hPe⟩ := GlobalTheory.EvTame.isTame_of_isEv F E σ B n d n d X W X W M M₁ 1 1 ∅ e hpair.good hM₁ hev g hg
    refine ⟨ι, inst, P, g', hg', fun f => ?_⟩
    rw [← hPe f]
    exact hTe _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)
  have hti : IsTame F T.symm.toLinearMap :=
    GlobalTheory.T.good_model_evaluation_bijective_schwartz hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij T.symm.toLinearMap
      (fun Φ hΦ => by rw [← hTe Φ hΦ]; simp)
  exact hasDbl_of_tame (cA σ) B.ψ (GlobalTheory.StdCharFromIsStd.norm_psi hpair.base.std) (-1) _ _ M.co M₁.co T hgood ht hti

end GlobalTheory.DblInt
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem _root_.GlobalTheory.T.reducedEquation_pullback_unitLocus_divides_vanishing : ∀ (X Y : Scheme.{0}) [IsLocallyNoetherian X] (q : Y ⟶ X) (ι : Type) [Finite ι] (Vo : X.Opens) (U U' : X.affineOpens) (hU' : U'.1 ≤ U.1) (W : Y.Opens), IsAffineOpen W → ∀ (hWU : W ≤ q ⁻¹ᵁ U.1) (N : ι → Γ(Y, W)), (MvPolynomial.eval₂Hom (q.appLE U.1 W hWU).hom N).Etale → ∀ (δ : Γ(X, U.1)), (Scheme.IdealSheafData.vanishingIdeal Vo.compl).ideal U' = Ideal.span {resG X hU' δ} → (∀ (z : Y) (hz : z ∈ W), q z ∈ U'.1 → (IsUnit (ger z hz ((q.appLE U.1 W hWU).hom δ)) ↔ q z ∈ Vo)) ∧ ∀ (W' : Y.Opens) (hW' : W' ≤ W), W' ≤ q ⁻¹ᵁ U'.1 → ∀ f : Γ(Y, W'), (∀ (z : Y) (hz : z ∈ W'), q z ∉ Vo → ger z hz f ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk z)) → ∀ (z : Y) (hz : z ∈ W'), ger z (hW' hz) ((q.appLE U.1 W hWU).hom δ) ∣ ger z hz f := by
  first | exact @GlobalTheory.EtaleReducedEq.reducedEq_pullback_etale | exact GlobalTheory.EtaleReducedEq.reducedEq_pullback_etale | (intros; apply GlobalTheory.EtaleReducedEq.reducedEq_pullback_etale <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AV.AmpleTopPos

theorem inter_comp_equiv {K : Type} [Field K] (A : AbVar K) {J J' : Type} [Fintype J] [Fintype J']
    (e : J' ≃ J) (c : J → Pic A.X.left) : inter A (c ∘ e) = inter A c := by
  unfold inter
  rw [GlobalTheory.multiDiff_comp_equiv]

theorem inter_top_pos : ∀ (K : Type) [Field K] (A : AbVar K) (c : Pic A.X.left), IsAmpleCls c →
    ∀ (J : Type) [Fintype J], Fintype.card J = A.dim → 0 < inter A (fun _ : J => c) := by
  intro K _ A c hc J _ hJ
  obtain ⟨L, hL, hr, rfl⟩ := hc
  have hA : IsAmpleLB L := (GlobalTheory.AmpleClsIff.isAmpleCls_cls_iff K A L hL).1 ⟨L, hL, hr, rfl⟩
  have e : Fin A.dim ≃ J := (Fintype.equivFinOfCardEq hJ).symm
  have h1 : inter A (fun _ : J => cls L hL) = inter A (fun _ : Fin A.dim => cls L hL) :=
    (inter_comp_equiv A e (fun _ : J => cls L hL)).symm
  rw [h1, GlobalTheory.T.abelianVariety_intersection_eq_lineBundleIntersection K A (Fin A.dim) (fun _ => L) (fun _ => hL)]
  letI := A.algΓ
  obtain ⟨hI, -, -⟩ := GlobalTheory.AV.AbVar.isIntegral_isLocallyNoetherian_compactSpace K A
  obtain ⟨hs, hp⟩ := GlobalTheory.AV.AbVarProj.strHom_eq_and_isProjOver K A
  have hp' : IsProjOver (strHom K (X := A.X.left)) := by rw [hs]; exact hp
  exact GlobalTheory.CompanionTheory.NefKleiman.interNum_top_pos_of_isAmpleLB K A.X.left hp' A.dim
    (GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim K A) L hA

end GlobalTheory.AV.AmpleTopPos
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV

theorem isAmpleCls_add : ∀ (K : Type) [Field K] (A : AbVar K) (c d : Pic A.X.left),
    IsAmpleCls c → IsAmpleCls d → IsAmpleCls (c + d) := by
  intro K _ A c d hc hd
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨M, hM, rfl⟩ := cls_surj d
  have hA : IsAmpleLB L := (GlobalTheory.T.abelianVarietyAmpleClass_cechPicardClass_iff_ample K A L hL).1 hc
  have hB : IsAmpleLB M := (GlobalTheory.T.abelianVarietyAmpleClass_cechPicardClass_iff_ample K A M hM).1 hd
  have hN : (tens L M).IsLB := isLB_tens hL hM
  have hT : IsAmpleLB (tens L M) := by
    refine hA.tensor hB hN ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hN hL) hM)).1 ?_)
    rw [cls_div (LB.isLB_div hN hL) hM, cls_div hN hL, cls_tens hL hM]
    abel
  rw [← cls_tens hL hM hN]
  exact (GlobalTheory.T.abelianVarietyAmpleClass_cechPicardClass_iff_ample K A (tens L M) hN).2 hT

end GlobalTheory.AV
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AV.DimLe

section

attribute [local instance low] specializationOrder

theorem topologicalKrullDim_le_of_isFinite {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] :
    topologicalKrullDim X ≤ topologicalKrullDim Y := by
  have eX : topologicalKrullDim X = Order.krullDim X :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))
  have eY : topologicalKrullDim Y = Order.krullDim Y :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))
  rw [eX, eY]
  refine Order.krullDim_le_of_strictMono (f : X → Y) fun a b hab => ?_
  have h1 : f b ⤳ f a := Specializes.map hab.le f.continuous
  refine lt_of_le_of_ne h1 fun e => hab.ne ?_
  exact ((GlobalTheory.finite_fibre_and_eq_of_specializes_of_isFinite Y X f inferInstance (f a)).2 b a
    e.symm rfl hab.le).symm

theorem topologicalKrullDim_le_of_surjective_of_isClosedMap {X Y : Scheme.{0}} (f : X ⟶ Y)
    (hs : Function.Surjective f) (hc : IsClosedMap f) :
    topologicalKrullDim Y ≤ topologicalKrullDim X := by
  have eX : topologicalKrullDim X = Order.krullDim X :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))
  have eY : topologicalKrullDim Y = Order.krullDim Y :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))
  rw [eX, eY, Order.krullDim_eq_iSup_height]
  refine iSup_le fun y => ?_
  obtain ⟨x, rfl⟩ := hs y
  have h : Order.height (f x) ≤ Order.height x :=
    ENat.forall_natCast_le_iff_le.mp fun n hn =>
      GlobalTheory.GenFibreDim.le_height_of_specializingMap hc.specializingMap n x hn
  exact (WithBot.coe_le_coe.mpr h).trans (Order.height_le_krullDim x)

end

theorem dim_le : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B),
    (IsFinite f.hom.left → A.dim ≤ B.dim) ∧ (Surjective f.hom.left → B.dim ≤ A.dim) := by
  intro K _ A B f
  have hA := GlobalTheory.T.topologicalKrullDim_abVar_eq_dim K A
  have hB := GlobalTheory.T.topologicalKrullDim_abVar_eq_dim K B
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · have h := topologicalKrullDim_le_of_isFinite f.hom.left
    rw [hA, hB] at h
    exact_mod_cast h
  · have := A.ab.proper
    have := B.ab.proper
    have hw : f.hom.left ≫ B.X.hom = A.X.hom := Over.w f.hom
    have : UniversallyClosed (f.hom.left ≫ B.X.hom) := by rw [hw]; infer_instance
    have : UniversallyClosed f.hom.left := UniversallyClosed.of_comp_of_isSeparated f.hom.left B.X.hom
    have h := topologicalKrullDim_le_of_surjective_of_isClosedMap f.hom.left
      hf.surj f.hom.left.isClosedMap
    rw [hA, hB] at h
    exact_mod_cast h

end GlobalTheory.AV.DimLe
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.eq_zero_of_dim_eq_zero' : ∀ (K : Type) [Field K] (A B : AbVar K), (A.dim = 0 ∨ B.dim = 0) → ∀ f : A ⟶ B, f = 0 := by
  first | exact @GlobalTheory.AV.AbVar.eq_zero_of_dim_eq_zero | exact GlobalTheory.AV.AbVar.eq_zero_of_dim_eq_zero | (intros; apply GlobalTheory.AV.AbVar.eq_zero_of_dim_eq_zero <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem isAmpleCls_pull_of_isFinite : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (d : Pic B.X.left),
    IsFinite f.hom.left → IsAmpleCls d → IsAmpleCls (CechPic.pull f.hom.left d) := by
  intro K _ A B f d hf hd
  obtain ⟨L, hL, hrel, rfl⟩ := hd
  have hB : IsAmpleLB L := (GlobalTheory.T.abelianVarietyAmpleClass_cechPicardClass_iff_ample K B L hL).1 ⟨L, hL, hrel, rfl⟩
  have hA : IsAmpleLB (L.pull f.hom.left) := hB.pull_of_isAffineHom f.hom.left
  have h := (GlobalTheory.T.abelianVarietyAmpleClass_cechPicardClass_iff_ample K A (L.pull f.hom.left) hA.isLB).2 hA
  rwa [cls_pull hL f.hom.left hA.isLB] at h

end GlobalTheory.AV.AbVar
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianVarietyMumfordClass_bilinear : ∀ (K : Type) [Field K] (A : AbVar K) (c : Pic A.X.left) (Y : Over (Sp K)) (x y y' : Y ⟶ A.X) (n : ℤ), AbVar.lam c x (y * y') = AbVar.lam c x y + AbVar.lam c x y' ∧ AbVar.lam c 1 y = 0 ∧ AbVar.lam c x 1 = 0 ∧ AbVar.lam c (x ^ n) y = n • AbVar.lam c x y ∧ AbVar.lam c x (y ^ n) = n • AbVar.lam c x y := by
  first | (exact @GlobalTheory.AV.AbVar.lam_bilinear) | (exact GlobalTheory.AV.AbVar.lam_bilinear) | (intros; apply GlobalTheory.AV.AbVar.lam_bilinear  <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar.AdjCalc

variable {K : Type} [Field K]

theorem comp_zpow' {X Y G : Over (Sp K)} [GrpObj G] (f : X ⟶ Y) (g : Y ⟶ G) (m : ℤ) :
    f ≫ g ^ m = (f ≫ g) ^ m :=
  map_zpow (MonoidHom.mk' (fun g : Y ⟶ G => f ≫ g) (MonObj.comp_mul f)) g m

theorem isAdj_pt {A B : AbVar K} {c : Pic A.X.left} {d : Pic B.X.left} {f : A ⟶ B} {n : ℤ} {h : B ⟶ A}
    (H : IsAdj c d f n h) {Y : Over (Sp K)} (x : Y ⟶ A.X) (y : Y ⟶ B.X) :
    n • lam d (x ≫ f.hom) y = lam c x (y ≫ h.hom) := by
  have H' := congrArg (CechPic.pull (lift x y).left) H
  rw [map_zsmul, (GlobalTheory.T.abelianVarietyMumfordClass_symm_natural_additive K A A c c c (𝟙 A) _ Y (lift x y) _ _).2.1,
    (GlobalTheory.T.abelianVarietyMumfordClass_symm_natural_additive K B B d d d (𝟙 B) _ Y (lift x y) _ _).2.1] at H'
  simpa only [lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd] using H'

end GlobalTheory.AV.AbVar.AdjCalc
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AdjCancel

variable {K : Type} [Field K]

theorem evc_zpow {A A' : AbVar K} {P : LB (A.X ⊗ A'.X).left} (hP : AbDual.IsDual A.X A'.X P)
    {Y : Over (Sp K)} (a : Y ⟶ A.X) (b : Y ⟶ A'.X) (k : ℤ) :
    AbDual.evc hP.isLB a (b ^ k) = k • AbDual.evc hP.isLB a b ∧ AbDual.evc hP.isLB a 1 = 0 := by
  let F : (Y ⟶ A'.X) →* Multiplicative (Pic Y.left) :=
    MonoidHom.mk' (fun b => Multiplicative.ofAdd (AbDual.evc hP.isLB a b)) (fun b b' => by
      rw [GlobalTheory.T.poincareClass_additive_in_dual_variable K A A' P hP Y a b b']; rfl)
  refine ⟨?_, ?_⟩
  · have := map_zpow F b k
    exact this
  · have := map_one F
    exact this

end GlobalTheory.AdjCancel
end
