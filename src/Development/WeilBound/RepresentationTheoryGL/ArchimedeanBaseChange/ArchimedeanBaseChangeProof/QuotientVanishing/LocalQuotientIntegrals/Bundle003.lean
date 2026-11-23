module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.OneVanish
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle010
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish

@[expose] public section

section

noncomputable section

open MeasureTheory PositivityTheory.Rg.Tf.Loc
open scoped Pointwise ENNReal

namespace PositivityTheory.Rg.BcB.CV

namespace QuotientIntegral

theorem enorm_ofReal_toReal_le (r : ℝ≥0∞) : ‖((r.toReal : ℝ) : ℂ)‖ₑ ≤ r := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_toReal_le

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem lintegral_indicator_ne_top (μ : Measure G) [μ.IsHaarMeasure]
    (T : Subgroup G) (ν : Measure T) [ν.IsHaarMeasure] [ν.IsInvInvariant] {C : Set G}
    (hT : IsClosed (T : Set G)) (hC : IsCompact C) {ρ0 : G → ℝ≥0∞}
    (h0 : IsQuotNormaliser T ν ρ0) :
    ∫⁻ g, ((T : Set G) * C).indicator 1 g * ρ0 g ∂μ ≠ ⊤ := by
  classical
  have : LocallyCompactSpace T := hT.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology T := TopologicalSpace.Subtype.secondCountableTopology (T : Set G)
  have : SigmaCompactSpace T := inferInstance
  have : SFinite ν := inferInstance
  have hmcoe : Measurable (fun h : T => (h : G)) := measurable_subtype_coe
  have : ν.IsMulRightInvariant := by
    have : ν.inv.IsMulRightInvariant := inferInstance
    rwa [Measure.inv_eq_self] at this
  obtain ⟨U, hUc, hU1⟩ := exists_compact_mem_nhds (1 : G)
  set K : Set G := U * C with hKdef
  have hKc : IsCompact K := hUc.mul hC
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  set S : Set G := (T : Set G) * C with hSdef
  have hSm : MeasurableSet S := (hT.mul_right_of_isCompact hC).measurableSet
  have hSinv : ∀ t ∈ T, ∀ x, t * x ∈ S ↔ x ∈ S := by
    intro t ht x
    constructor
    · rintro ⟨s, hs, c, hc, hsc⟩
      exact ⟨t⁻¹ * s, T.mul_mem (T.inv_mem ht) hs, c, hc, by
        show t⁻¹ * s * c = x
        rw [mul_assoc, show s * c = t * x from hsc, inv_mul_cancel_left]⟩
    · rintro ⟨s, hs, c, hc, rfl⟩
      exact ⟨t * s, T.mul_mem ht hs, c, hc, mul_assoc _ _ _⟩
  have hKind : Measurable (K.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hKm
  set I : G → ℝ≥0∞ := fun g => ∫⁻ h : T, K.indicator 1 ((h : G) * g) ∂ν with hIdef
  have hIm : Measurable I := by
    have : Measurable (fun p : G × T => K.indicator (1 : G → ℝ≥0∞) ((p.2 : G) * p.1)) :=
      hKind.comp ((hmcoe.comp measurable_snd).mul measurable_fst)
    exact this.lintegral_prod_right'
  have hIT : ∀ t ∈ T, ∀ g, I (t * g) = I g := by
    intro t ht g
    have := lintegral_mul_right_eq_self (μ := ν)
      (fun h : T => K.indicator (1 : G → ℝ≥0∞) ((h : G) * g)) ⟨t, ht⟩
    simp only [hIdef]
    rw [← this]
    refine lintegral_congr fun h => ?_
    simp [mul_assoc]
  set V : Set T := (fun h : T => (h : G)) ⁻¹' interior U with hVdef
  have hVm : MeasurableSet V := hmcoe measurableSet_interior
  have hVpos : ν V ≠ 0 := by
    have hVo : IsOpen V := isOpen_interior.preimage continuous_subtype_val
    have h1 : (1 : T) ∈ V := by
      show ((1 : T) : G) ∈ interior U
      simpa using mem_interior_iff_mem_nhds.mpr hU1
    exact (hVo.measure_pos ν ⟨1, h1⟩).ne'
  have hIC : ∀ g ∈ S, ν V ≤ I g := by
    rintro _ ⟨t, ht, c, hc, rfl⟩
    rw [hIT t ht c, ← lintegral_indicator_one hVm]
    refine lintegral_mono fun h => ?_
    by_cases hh : h ∈ V
    · have hK : (h : G) * c ∈ K := Set.mul_mem_mul (interior_subset hh) hc
      simp [hh, hK]
    · simp [Set.indicator_apply, hh]
  have hIfin : ∀ g, I g ≠ ⊤ := by
    intro g
    have hemb : Topology.IsClosedEmbedding (fun h : T => (h : G) * g) :=
      (Homeomorph.mulRight g).isClosedEmbedding.comp hT.isClosedEmbedding_subtypeVal
    have hmeas : Measurable (fun h : T => (h : G) * g) := hmcoe.mul_const g
    have : I g = ν ((fun h : T => (h : G) * g) ⁻¹' K) := by
      rw [← lintegral_indicator_one (hmeas hKm)]
      rfl
    rw [this]
    exact ((hemb.isCompact_preimage hKc).measure_lt_top).ne
  set ρ : G → ℝ≥0∞ := S.piecewise (fun g => K.indicator 1 g * (I g)⁻¹) ρ0 with hρdef
  have hρ : IsQuotNormaliser T ν ρ := by
    refine ⟨Measurable.piecewise hSm (hKind.mul hIm.inv) h0.1, fun g => ?_⟩
    by_cases hg : g ∈ S
    · have hmem : ∀ h : T, (h : G) * g ∈ S := fun h => (hSinv _ h.2 g).2 hg
      calc ∫⁻ h : T, ρ ((h : G) * g) ∂ν = ∫⁻ h : T, K.indicator 1 ((h : G) * g) * (I g)⁻¹ ∂ν := by
            refine lintegral_congr fun h => ?_
            simp only [hρdef, Set.piecewise_eq_of_mem _ _ _ (hmem h), hIT _ h.2]
        _ = I g * (I g)⁻¹ := lintegral_mul_const _ (hKind.comp (hmcoe.mul_const g))
        _ = 1 := ENNReal.mul_inv_cancel
              (ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hVpos) (hIC g hg))) (hIfin g)
    · have hmem : ∀ h : T, (h : G) * g ∉ S := fun h hh => hg ((hSinv _ h.2 g).1 hh)
      rw [← h0.2 g]
      refine lintegral_congr fun h => ?_
      simp only [hρdef, Set.piecewise_eq_of_notMem _ _ _ (hmem h)]
  have hF1 : Measurable (S.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hSm
  have hFinv : ∀ h ∈ T, ∀ g, S.indicator (1 : G → ℝ≥0∞) (h * g) = S.indicator 1 g := by
    intro h hh g
    simp only [Set.indicator_apply, hSinv h hh g, Pi.one_apply]
  rw [lintegral_normaliser_eq hF1 hFinv h0 hρ]
  refine ne_of_lt (lt_of_le_of_lt (b := ∫⁻ g, K.indicator 1 g * (ν V)⁻¹ ∂μ)
    (lintegral_mono fun g => ?_) ?_)
  · by_cases hg : g ∈ S
    · simp only [Set.indicator_of_mem hg, Pi.one_apply, one_mul, hρdef,
        Set.piecewise_eq_of_mem _ _ _ hg]
      gcongr
      exact hIC g hg
    · simp [hg]
  · rw [lintegral_mul_const _ hKind, lintegral_indicator_one hKm]
    exact ENNReal.mul_lt_top hKc.measure_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hVpos))

theorem main (μ : Measure G) [μ.IsHaarMeasure] (T : Subgroup G) (ν : Measure T) [ν.IsHaarMeasure]
    [ν.IsInvInvariant] (C : Set G) (hT : IsClosed (T : Set G)) (hC : IsCompact C) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (F : G → ℂ) (B : ℝ), 0 ≤ B → Measurable F →
      (∀ t ∈ T, ∀ x, F (t * x) = F x) → (∀ x, F x ≠ 0 → x ∈ (T : Set G) * C) →
      (∀ x ∈ C, ‖F x‖ ≤ B) → quotLIntegral μ T ν (fun x => ‖F x‖ₑ) ≠ ⊤ ∧
        ‖quotIntegral μ T ν F‖ ≤ A * B := by
  classical
  by_cases hex : ∃ ρ, IsQuotNormaliser T ν ρ
  · have h0 : IsQuotNormaliser T ν hex.choose := hex.choose_spec
    set S : Set G := (T : Set G) * C with hSdef
    have hL : ∫⁻ g, S.indicator 1 g * hex.choose g ∂μ ≠ ⊤ :=
      lintegral_indicator_ne_top μ T ν hT hC h0
    refine ⟨(∫⁻ g, S.indicator 1 g * hex.choose g ∂μ).toReal, ENNReal.toReal_nonneg,
      fun F B hB hF hFT hFS hFC => ?_⟩
    have hbound : ∀ g, ‖F g‖ₑ ≤ ENNReal.ofReal B * S.indicator 1 g := by
      intro g
      by_cases hg : g ∈ S
      · rw [Set.indicator_of_mem hg, Pi.one_apply, mul_one]
        obtain ⟨t, ht, c, hc, rfl⟩ := hg
        rw [hFT t ht c, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hFC c hc)
      · have : F g = 0 := by
          by_contra h
          exact hg (hFS g h)
        simp [this]
    have hle : ∫⁻ g, ‖F g‖ₑ * hex.choose g ∂μ ≤
        ENNReal.ofReal B * ∫⁻ g, S.indicator 1 g * hex.choose g ∂μ := by
      calc ∫⁻ g, ‖F g‖ₑ * hex.choose g ∂μ
          ≤ ∫⁻ g, ENNReal.ofReal B * (S.indicator 1 g * hex.choose g) ∂μ :=
            lintegral_mono fun g => by
              rw [← mul_assoc]
              gcongr
              exact hbound g
        _ = ENNReal.ofReal B * ∫⁻ g, S.indicator 1 g * hex.choose g ∂μ :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    have hne : ENNReal.ofReal B * ∫⁻ g, S.indicator 1 g * hex.choose g ∂μ ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL
    have hfin : ∫⁻ g, ‖F g‖ₑ * hex.choose g ∂μ ≠ ⊤ := ne_top_of_le_ne_top hne hle
    refine ⟨by rw [quotLIntegral, dite_eq_left hex]; exact hfin, ?_⟩
    rw [quotIntegral, dite_eq_left hex]
    calc ‖∫ g, F g * ((hex.choose g).toReal : ℂ) ∂μ‖
        = ‖∫ g, F g * ((hex.choose g).toReal : ℂ) ∂μ‖ₑ.toReal := (toReal_enorm _).symm
      _ ≤ (∫⁻ g, ‖F g‖ₑ * hex.choose g ∂μ).toReal := by
          refine ENNReal.toReal_mono hfin ((enorm_integral_le_lintegral_enorm _).trans
            (lintegral_mono fun g => ?_))
          rw [enorm_mul]
          gcongr
          exact enorm_ofReal_toReal_le _
      _ ≤ (ENNReal.ofReal B * ∫⁻ g, S.indicator 1 g * hex.choose g ∂μ).toReal :=
          ENNReal.toReal_mono hne hle
      _ = (∫⁻ g, S.indicator 1 g * hex.choose g ∂μ).toReal * B := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB, mul_comm]
  · refine ⟨0, le_rfl, fun F B _ _ _ _ _ => ?_⟩
    simp [quotLIntegral, quotIntegral, hex]

end QuotientIntegral

theorem pf_QInt : QInt := by
  intro G _ _ _ _ _ _ _ _ μ _ T ν _ _ C hT hC
  exact QuotientIntegral.main μ T ν C hT hC

end PositivityTheory.Rg.BcB.CV
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc

namespace PositivityTheory.Rg.BcB.CV.FamilyAtPlace

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

theorem emb_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (v : InfinitePlace E) (x : E) :
    v.embedding (conjE E x) = starRingEnd ℂ (v.embedding x) :=
  IsCMField.complexEmbedding_complexConj E v.embedding x

theorem locGL_theta {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (v : InfinitePlace E)
    (d : GL (Fin n) E) : locGL v (thetaE E n d) = thC n (locGL v d) := by
  apply Units.ext
  have h1 : (locGL v (thetaE E n d)).val = ((thetaR (conjE E) n d).val).map v.embedding := rfl
  have h2 : (locGL v d⁻¹).val = (d⁻¹ : GL (Fin n) E).val.map v.embedding := rfl
  rw [h1, thetaR_val, thetaR_val, ← map_inv, h2]
  ext i j
  simp [emb_conj]

theorem locGL_nrm {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (v : InfinitePlace E)
    (d : GL (Fin n) E) : locGL v (nrm d) = locGL v d * thC n (locGL v d) := by
  rw [nrm, map_mul, locGL_theta]

theorem perp_anti {K : Type} [Field K] (σ : K →+* K) {n : ℕ} {W W' : Submodule K (Fin n → K)} (h : W ≤ W') :
    perp σ W' ≤ perp σ W := fun _ hy x hx => hy x (h hx)

theorem perpD_anti {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (d : GL (Fin n) K) {W W' : Submodule K (Fin n → K)}
    (h : W ≤ W') : perpD σ d W' ≤ perpD σ d W :=
  Submodule.map_mono (perp_anti σ h)

end PositivityTheory.Rg.BcB.CV.FamilyAtPlace

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.BcB.CV.FamilyAtPlace in
theorem PositivityTheory.Rg.BcB.CV.pf_FamAt : PositivityTheory.Rg.BcB.D4.LocFlag → PositivityTheory.Rg.BcB.CV.Ploc → PositivityTheory.Rg.BcB.CV.FamAt := by
  intro hLF hP E _ _ _ n m d Wof a V v hPar hV hemb
  refine ⟨?_, ?_⟩
  · rw [← locGL_nrm]
    have : (locGL v (nrm d)).val = (nrm d).val.map v.embedding := rfl
    rw [this, Matrix.charpoly_map]
    exact hPar.reg.map
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact continuous_pi fun e => (hP E n v (Wof e)).2.1
    · intro x
      exact ((hP E n v (Wof 0)).2.2.2.1 hPar.zero).1 x
    · intro x k hk
      funext e
      exact (hP E n v (Wof e)).2.2.1 x k hk
    · intro t ht x z
      have hs := hemb t ht
      have key : ∀ e, pAt Wof v (t * x) e = pAt Wof v x e - sdot e (a (embInf n v t)) := by
        intro e
        have h1 := (hP E n v (Wof e)).2.2.2.2.2.2.2 t (embInf n v x)
        rw [(hP E n v (Wof e)).2.2.2.2.1 x, hPar.degT _ hs] at h1
        simp only [pAt]
        linarith
      have : pAt Wof v (t * x) + z = fun e => (pAt Wof v x + z) e - sdot e (a (embInf n v t)) := by
        funext e
        simp only [Pi.add_apply, key]
        ring
      rw [this, hV _ hs]
    · intro e he
      have hW : Wof e ≠ ⊥ := by
        intro h
        obtain ⟨e0, _, hu⟩ := hPar.uniq ⊥ (hPar.zero ▸ hPar.iso 0)
        exact he ((hu e h).trans (hu 0 hPar.zero).symm)
      obtain ⟨h1, h2, h3, h4, h5⟩ := hLF E n d (Wof e) v (hPar.iso e) hW (hPar.perp e)
      refine ⟨_, _, ⟨h1, h2, h3, h4⟩, ?_⟩
      intro u hu x e' he'
      have hW' : Wof e' ≤ Wof e ∨ (Wof e ≤ Wof e' ∧ Wof e' ≤ perpD (conjE E) d (Wof e)) := by
        rcases he' with h | h
        · exact Or.inr ⟨hPar.mono _ _ h, (hPar.iso e').2.trans (perpD_anti _ _ (hPar.mono _ _ h))⟩
        · exact Or.inl (hPar.mono _ _ h)
      have c1 := (hP E n v (Wof e')).1 (embInf n v u * embInf n v x)
      have c2 := (hP E n v (Wof e')).1 (embInf n v x)
      rw [map_mul, (hP E n v (Wof e')).2.2.2.2.1 u, (hP E n v (Wof e')).2.2.2.2.1 x] at c1
      rw [(hP E n v (Wof e')).2.2.2.2.1 x] at c2
      simp only [pAt]
      rw [← c1, ← c2]
      exact h5 (embInf n v x) u hu (Wof e') hW'
end
end

section

noncomputable section

open MeasureTheory PositivityTheory.Rg.Tf.Loc

namespace PositivityTheory.Rg.BcB.CV.QuotientProduct

theorem exists_haar_inv (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (hc : ∀ a b : H, a * b = b * a) : ∃ ν : Measure H, ν.IsHaarMeasure ∧ ν.IsInvInvariant := by
  let inst : CommGroup H := { (inferInstance : Group H) with mul_comm := hc }
  exact ⟨Measure.haar, inferInstance,
    @Measure.IsHaarMeasure.isInvInvariant_of_regular H inst _ _ _ _ Measure.haar _ _ _⟩

noncomputable def prodE {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁] [Group G₂] [TopologicalSpace G₂]
    (T₁ : Subgroup G₁) (T₂ : Subgroup G₂) : T₁ × T₂ ≃ₜ* T₁.prod T₂ :=
  _root_.UpperTheory.Reformulated.B.DaGva8.prodE T₁ T₂

def swapE (G₁ G₂ : Type) [Group G₁] [TopologicalSpace G₁] [Group G₂] [TopologicalSpace G₂] :
    G₁ × G₂ ≃ₜ* G₂ × G₁ where
  toFun := Prod.swap
  invFun := Prod.swap
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_swap
  continuous_invFun := continuous_swap

theorem isClosed_prod {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁] [Group G₂] [TopologicalSpace G₂]
    {T₁ : Subgroup G₁} {T₂ : Subgroup G₂} (h₁ : IsClosed (T₁ : Set G₁)) (h₂ : IsClosed (T₂ : Set G₂)) :
    IsClosed ((T₁.prod T₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)) := by
  rw [Subgroup.coe_prod]; exact h₁.prod h₂

theorem left (hQP : PositivityTheory.Rg.BcB.D4.QuotProd) (hQM : QMap)
    (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [T2Space G₁]
    [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁]
    (G₂ : Type) [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂] [T2Space G₂]
    [SecondCountableTopology G₂] [MeasurableSpace G₂] [BorelSpace G₂] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure]
    (μ₂ : Measure G₂) [μ₂.IsHaarMeasure]
    (T₁ : Subgroup G₁) (T₂ : Subgroup G₂) (ν : Measure (T₁.prod T₂)) [ν.IsHaarMeasure] [ν.IsInvInvariant]
    (F : G₁ × G₂ → ℂ) (hT₁ : IsClosed (T₁ : Set G₁)) (hT₂ : IsClosed (T₂ : Set G₂))
    (hc₁ : ∀ s ∈ T₁, ∀ t ∈ T₁, s * t = t * s) (hc₂ : ∀ s ∈ T₂, ∀ t ∈ T₂, s * t = t * s)
    (hF : Measurable F) (hFT : ∀ t ∈ T₁.prod T₂, ∀ x, F (t * x) = F x)
    (h : ∀ (ν₁ : Measure T₁) [ν₁.IsHaarMeasure] [ν₁.IsInvInvariant] x₂,
      quotIntegral μ₁ T₁ ν₁ (fun x₁ => F (x₁, x₂)) = 0) :
    quotIntegral (μ₁.prod μ₂) (T₁.prod T₂) ν F = 0 := by
  have : LocallyCompactSpace T₁ := hT₁.locallyCompactSpace
  have : LocallyCompactSpace T₂ := hT₂.locallyCompactSpace
  have : SecondCountableTopology T₁ := inferInstanceAs (SecondCountableTopology (T₁ : Set G₁))
  have : SecondCountableTopology T₂ := inferInstanceAs (SecondCountableTopology (T₂ : Set G₂))
  obtain ⟨ν₁, _, _⟩ := exists_haar_inv T₁ (fun a b => Subtype.ext (hc₁ a a.2 b b.2))
  obtain ⟨ν₂, _, _⟩ := exists_haar_inv T₂ (fun a b => Subtype.ext (hc₂ a a.2 b b.2))
  set E := prodE T₁ T₂
  have hE : Measurable E := E.continuous.measurable
  have hinvP : Measure.map Inv.inv (ν₁.prod ν₂) = ν₁.prod ν₂ := by
    have : (Inv.inv : T₁ × T₂ → T₁ × T₂) = Prod.map Inv.inv Inv.inv := rfl
    rw [this, ← Measure.map_prod_map _ _ continuous_inv.measurable continuous_inv.measurable,
      Measure.map_inv_eq_self, Measure.map_inv_eq_self]
  have : (Measure.map E (ν₁.prod ν₂)).IsInvInvariant := by
    constructor
    show Measure.map Inv.inv (Measure.map E (ν₁.prod ν₂)) = Measure.map E (ν₁.prod ν₂)
    rw [Measure.map_map continuous_inv.measurable hE]
    have : (Inv.inv ∘ ⇑E) = ⇑E ∘ Inv.inv := funext fun p => (map_inv E p).symm
    rw [this, ← Measure.map_map hE continuous_inv.measurable, hinvP]
  have hmap : (Measure.map E (ν₁.prod ν₂)).map
      (fun t : T₁.prod T₂ => ((⟨t.1.1, (Subgroup.mem_prod.1 t.2).1⟩, ⟨t.1.2, (Subgroup.mem_prod.1 t.2).2⟩) : T₁ × T₂)) =
      ν₁.prod ν₂ := by
    have : (fun t : T₁.prod T₂ => ((⟨t.1.1, (Subgroup.mem_prod.1 t.2).1⟩, ⟨t.1.2, (Subgroup.mem_prod.1 t.2).2⟩) : T₁ × T₂))
      = ⇑E.symm := rfl
    rw [this, Measure.map_map (show Measurable ⇑E.symm from E.symm.continuous.measurable) hE]
    have : (⇑E.symm ∘ ⇑E) = id := funext fun p => E.symm_apply_apply p
    rw [this, Measure.map_id]
  have h0 := hQP G₁ G₂ μ₁ μ₂ T₁ T₂ ν₁ ν₂ (Measure.map E (ν₁.prod ν₂)) F hF hmap hFT (fun x₂ => h ν₁ x₂)
  refine hQM (G₁ × G₂) (G₁ × G₂) (ContinuousMulEquiv.refl _) (μ₁.prod μ₂) (μ₁.prod μ₂) (T₁.prod T₂) (T₁.prod T₂)
    ν (Measure.map E (ν₁.prod ν₂)) F (isClosed_prod hT₁ hT₂) ?_ hF hFT h0
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hy
  · intro hx; exact ⟨x, hx, rfl⟩

end PositivityTheory.Rg.BcB.CV.QuotientProduct

namespace PositivityTheory.Rg.BcB.CV

open QuotientProduct in
theorem pf_QProd : PositivityTheory.Rg.BcB.D4.QuotProd → PositivityTheory.Rg.BcB.CV.QMap → PositivityTheory.Rg.BcB.CV.QProd := by
  intro hQP hQM G₁ _ _ _ _ _ _ _ _ G₂ _ _ _ _ _ _ _ _ μ₁ _ μ₂ _ T₁ T₂ ν _ _ F hT₁ hT₂ hc₁ hc₂ hF hFT hcase
  rcases hcase with h | h
  · exact left hQP hQM G₁ G₂ μ₁ μ₂ T₁ T₂ ν F hT₁ hT₂ hc₁ hc₂ hF hFT h
  · have hcl := isClosed_prod hT₂ hT₁
    have : LocallyCompactSpace (T₂.prod T₁) := hcl.locallyCompactSpace
    have : SecondCountableTopology (T₂.prod T₁) :=
      inferInstanceAs (SecondCountableTopology ((T₂.prod T₁ : Subgroup (G₂ × G₁)) : Set (G₂ × G₁)))
    obtain ⟨ν', _, _⟩ := exists_haar_inv (T₂.prod T₁) (fun a b => Subtype.ext (Prod.ext
      (hc₂ _ (Subgroup.mem_prod.1 a.2).1 _ (Subgroup.mem_prod.1 b.2).1)
      (hc₁ _ (Subgroup.mem_prod.1 a.2).2 _ (Subgroup.mem_prod.1 b.2).2)))
    set S := swapE G₁ G₂
    have hFT' : ∀ t ∈ T₂.prod T₁, ∀ x, F (S.symm (t * x)) = F (S.symm x) := by
      intro t ht x
      rw [map_mul]
      exact hFT _ (Subgroup.mem_prod.2 ⟨(Subgroup.mem_prod.1 ht).2, (Subgroup.mem_prod.1 ht).1⟩) _
    have h0 := left hQP hQM G₂ G₁ μ₂ μ₁ T₂ T₁ ν' (fun y => F (S.symm y)) hT₂ hT₁ hc₂ hc₁
      (hF.comp S.symm.continuous.measurable) hFT' (fun ν₂ _ _ x₁ => h ν₂ x₁)
    refine hQM (G₁ × G₂) (G₂ × G₁) S (μ₁.prod μ₂) (μ₂.prod μ₁) (T₁.prod T₂) (T₂.prod T₁)
      ν ν' F (isClosed_prod hT₁ hT₂) ?_ hF hFT h0
    ext ⟨a, b⟩
    simp only [Subgroup.mem_map, Subgroup.mem_prod]
    constructor
    · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, hxy⟩
      change (y, x) = (a, b) at hxy
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨rfl, rfl⟩ := hxy
      exact ⟨hy, hx⟩
    · rintro ⟨ha, hb⟩
      exact ⟨(b, a), ⟨hb, ha⟩, rfl⟩

end PositivityTheory.Rg.BcB.CV
end
end
