module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle004
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle687
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle164
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle017
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle072
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase

open GlobalTheory.Points Filter Topology

section Transfer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) {X : Var F} {j : X.X ⟶ gen Z}
  (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str)

theorem isOpenEmbedding_cxOf [IsOpenImmersion j] : IsOpenEmbedding (cxOf e σ hj) := by
  have hc : Continuous (cxOf e σ hj) :=
    continuous_induced_rng.2 ((continuous_comp (C := ℂ) j).comp continuous_subtype_val)
  refine ⟨IsEmbedding.of_comp hc continuous_subtype_val
    (((isOpenEmbedding_comp (C := ℂ) j).isEmbedding).comp IsEmbedding.subtypeVal), ?_⟩
  have hr : Set.range (cxOf e σ hj) = Subtype.val ⁻¹' Set.range fun x : Sp ℂ ⟶ X.X => x ≫ j := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, rfl⟩
    · rintro ⟨x, hx⟩
      replace hx : x ≫ j = y.1 := hx
      refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
      rw [← hj, ← Category.assoc, hx, ← Category.assoc, y.2, ← Spec.map_comp]
      rfl
  rw [hr]
  exact (isOpenEmbedding_comp (C := ℂ) j).isOpen_range.preimage continuous_subtype_val

variable [IsOpenImmersion j]

theorem le_preimage_cxOf (W : X.X.Opens) {z : CxPts X.str (σ.comp e.toRingHom)}
    (hz : z ∈ ptsIn X.str (σ.comp e.toRingHom) W) : ⊤ ≤ (cxOf e σ hj z).1 ⁻¹ᵁ (j ''ᵁ W) :=
  le_preimage_comp z.1 j (j.preimage_image_eq W).ge hz

theorem ev_eq_valAt'_cxOf (W : X.X.Opens) (g : Γ(X.X, W)) {z : CxPts X.str (σ.comp e.toRingHom)}
    (hz : z ∈ ptsIn X.str (σ.comp e.toRingHom) W) :
    ev X.str (σ.comp e.toRingHom) W g z = valAt' (cxOf e σ hj z).1 (j ''ᵁ W) ((j.appIso W).inv.hom g) := by
  have hle : W ≤ j ⁻¹ᵁ j ''ᵁ W := (j.preimage_image_eq W).ge
  change valR z.1 W g = valR (z.1 ≫ j) (j ''ᵁ W) _
  rw [← valR_appLE z.1 j hle hz, ← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]
  exact (valR_res z.1 le_rfl hz g).symm

end Transfer

open GlobalTheory.Points Filter Topology

theorem finrank_eq_of_differentiableAt {E₁ E₂ : Type} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] (Φ : OpenPartialHomeomorph E₁ E₂) {x : E₁} (hx : x ∈ Φ.source)
    (h₁ : DifferentiableAt ℂ Φ x) (h₂ : DifferentiableAt ℂ Φ.symm (Φ x)) :
    Module.finrank ℂ E₁ = Module.finrank ℂ E₂ := by
  have hl : (fderiv ℂ Φ.symm (Φ x)).comp (fderiv ℂ Φ x) = ContinuousLinearMap.id ℂ E₁ :=
    ((h₂.hasFDerivAt.comp x h₁.hasFDerivAt).congr_of_eventuallyEq
      (EventuallyEq.symm (Φ.eventually_left_inverse hx : Φ.symm ∘ Φ =ᶠ[𝓝 x] id))).unique (hasFDerivAt_id x)
  have h₁' : HasFDerivAt Φ (fderiv ℂ Φ x) (Φ.symm (Φ x)) := by
    rw [Φ.left_inv hx]
    exact h₁.hasFDerivAt
  have hr : (fderiv ℂ Φ x).comp (fderiv ℂ Φ.symm (Φ x)) = ContinuousLinearMap.id ℂ E₂ :=
    ((h₁'.comp (Φ x) h₂.hasFDerivAt).congr_of_eventuallyEq
      (EventuallyEq.symm (Φ.eventually_right_inverse' hx : Φ ∘ Φ.symm =ᶠ[𝓝 (Φ x)] id))).unique (hasFDerivAt_id (Φ x))
  exact (ContinuousLinearEquiv.equivOfInverse (fderiv ℂ Φ x) (fderiv ℂ Φ.symm (Φ x))
    (fun v => DFunLike.congr_fun hl v) (fun v => DFunLike.congr_fun hr v)).toLinearEquiv.finrank_eq

section Transfer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ}

theorem differentiableAt_valAt'_symm {n g : ℕ} {ch₀ : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)}
    {ex : ExpMaps Z σ g} (h : IsExpChart ch₀ ex) (U : (gen Z).Opens) (f : Γ(gen Z, U)) {b : Fin n → ℂ}
    (hb : b ∈ ch₀.target) (hU : ⊤ ≤ (ch₀.symm b).1 ⁻¹ᵁ U) :
    DifferentiableAt ℂ (fun b => valAt' (ch₀.symm b).1 U f) b :=
  (h.2.2.1 U f).2.differentiableAt ((h.2.2.1 U f).1.mem_nhds ⟨hb, hU⟩)

end Transfer

theorem exists_holoChart_of_expChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (X : Var F) (j : X.X ⟶ gen T.Z) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → ∀ (y : GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) (n g : ℕ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g), IsExpChart ch₀ ex → cxOf e σ hj y ∈ ch₀.source → ch₀ (cxOf e σ hj y) = 0 → ∀ r : ℝ, 0 < r → ∃ (hn : n = X.dim) (r' : ℝ) (ch : OpenPartialHomeomorph (GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) (ReciprocityTheory.L2DbarEstimates.V X.dim)), 0 < r' ∧ r' < r ∧ r' < 1 ∧ IsHoloChart ch ∧ y ∈ ch.source ∧ ch y = 0 ∧ (∀ z ∈ ch.source, (ch z).ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc X.dim 1) ∧ ∀ z ∈ ch.source, cxOf e σ hj z ∈ ch₀.source ∧ ch₀ (cxOf e σ hj z) = fun k => (r' : ℂ) * (ch z).ofLp (Fin.cast hn k) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ X j hj hji y n g ch₀ ex hex hy0 hy00 r hr
  set κ := cxOf e σ hj with hκdef
  have hκ : IsOpenEmbedding κ := isOpenEmbedding_cxOf e σ hj
  haveI : Nonempty (GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) := ⟨y⟩
  set χ := (hκ.toOpenPartialHomeomorph κ).trans ch₀ with hχdef
  have hχ : ∀ u ∈ χ.target, κ (χ.symm u) = ch₀.symm u := fun u hu => by
    have h2 : ch₀.symm u ∈ Set.range κ := by
      have := hu.2
      rwa [Set.mem_preimage, IsOpenEmbedding.toOpenPartialHomeomorph_target] at this
    rw [OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply]
    exact hκ.toOpenPartialHomeomorph_right_inv κ h2
  have hyχ : y ∈ χ.source := ⟨trivial, hy0⟩
  have hχy : χ y = 0 := hy00
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.AlgChart.exists_mem_source (p := X.str) (σ := σ.comp e.toRingHom) (D := X.dim) y
  have hn : n = X.dim := by
    set Φ := χ.symm.trans c₁.e with hΦ
    have h0 : (0 : Fin n → ℂ) ∈ Φ.source := by
      refine ⟨?_, ?_⟩
      · rw [← hχy]
        exact χ.map_source hyχ
      · show χ.symm 0 ∈ c₁.e.source
        rw [← hχy, χ.left_inv hyχ]
        exact hc₁
    have h0t : (0 : Fin n → ℂ) ∈ χ.target := h0.1
    have h1 : DifferentiableAt ℂ Φ 0 := by
      rw [differentiableAt_euclidean]
      intro a
      have hev : (fun u => Φ u a) =ᶠ[𝓝 0]
          fun u => valAt' (ch₀.symm u).1 (j ''ᵁ c₁.U) ((j.appIso c₁.U).inv.hom (c₁.x a)) := by
        filter_upwards [Φ.open_source.mem_nhds h0] with u hu
        have hs : χ.symm u ∈ c₁.e.source := hu.2
        show c₁.e (χ.symm u) a = _
        rw [c₁.apply_eq _ hs a, ev_eq_valAt'_cxOf e σ hj _ _ (c₁.source_subset hs),
          show cxOf e σ hj (χ.symm u) = ch₀.symm u from hχ u hu.1]
      refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
      refine differentiableAt_valAt'_symm hex _ _ h0t.1 ?_
      rw [← hχ 0 h0t]
      exact le_preimage_cxOf e σ hj _ (c₁.source_subset h0.2)
    have h2 : DifferentiableAt ℂ Φ.symm (Φ 0) := by
      have hB : IsOpen Φ.target := Φ.open_target
      have hΦ0 : Φ 0 ∈ Φ.target := Φ.map_source h0
      have hsub : Φ.target ⊆ c₁.e.target := fun w hw => hw.1
      have hmaps : Set.MapsTo (fun w => κ (c₁.e.symm w)) Φ.target ch₀.source := fun w hw => hw.2.2
      have hhol : IsHolTo Φ.target (fun w => (κ (c₁.e.symm w)).1) := by
        intro U f
        have hset : {b ∈ Φ.target | ⊤ ≤ (κ (c₁.e.symm b)).1 ⁻¹ᵁ U} =
            Φ.target ∩ c₁.e.symm ⁻¹' ptsIn X.str (σ.comp e.toRingHom) (j ⁻¹ᵁ U) := rfl
        refine ⟨?_, ?_⟩
        · rw [hset]
          exact (c₁.e.continuousOn_symm.mono hsub).isOpen_inter_preimage hB (isOpen_ptsIn _)
        · rw [hset]
          refine ((c₁.holo (j ⁻¹ᵁ U) ((j.app U).hom f)).mono fun w (hw : w ∈ Φ.target ∩ c₁.e.symm ⁻¹' ptsIn X.str (σ.comp e.toRingHom) (j ⁻¹ᵁ U)) => ⟨hsub hw.1, hw.2⟩).congr
            fun w _ => ?_
          exact valR_comp (c₁.e.symm w).1 j U f
      rw [differentiableAt_pi]
      intro k
      have hd := (hex.2.1 k (ReciprocityTheory.L2DbarEstimates.V X.dim) Φ.target (fun w => κ (c₁.e.symm w)) hB hhol hmaps).differentiableAt
        (hB.mem_nhds hΦ0)
      exact hd
    have := finrank_eq_of_differentiableAt Φ h0 h1 h2
    simpa [finrank_euclideanSpace_fin] using this
  subst hn
  have hr1 : 0 < min r 1 := lt_min hr one_pos
  set r' : ℝ := min r 1 / 2 with hr'
  have hr'0 : 0 < r' := half_pos hr1
  have hr'r : r' < min r 1 := half_lt_self hr1
  have hr'c : (r' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr'0.ne'
  let L : (Fin X.dim → ℂ) ≃L[ℂ] ReciprocityTheory.L2DbarEstimates.V X.dim :=
    (ContinuousLinearEquiv.smulLeft (Units.mk0 ((r' : ℂ)⁻¹) (inv_ne_zero hr'c))).trans
      (EuclideanSpace.equiv (Fin X.dim) ℂ).symm
  have hL : ∀ u k, (L u).ofLp k = (r' : ℂ)⁻¹ * u k := by
    intro u k
    simp [L]
  let ch := (χ.trans (OpenPartialHomeomorph.ofSet (Metric.ball (0 : Fin X.dim → ℂ) r') Metric.isOpen_ball)).trans
    L.toHomeomorph.toOpenPartialHomeomorph
  have hchs : ∀ v, ch.symm v = χ.symm (L.symm v) := fun v => rfl
  have hch : ∀ z, ch z = L (χ z) := fun z => rfl
  have hsrc : ∀ z ∈ ch.source, z ∈ χ.source ∧ χ z ∈ Metric.ball (0 : Fin X.dim → ℂ) r' := fun z hz => hz.1
  have htgt : ∀ v ∈ ch.target, L.symm v ∈ χ.target := fun v hv => hv.2.2
  refine ⟨rfl, r', ch, hr'0, hr'r.trans_le (min_le_left _ _), hr'r.trans_le (min_le_right _ _), ?_,
    ⟨⟨hyχ, ?_⟩, trivial⟩, ?_, ?_, ?_⟩
  · intro W f v hv
    have hopen : IsOpen (ch.target ∩ ch.symm ⁻¹' ptsIn X.str (σ.comp e.toRingHom) W) :=
      ch.continuousOn_symm.isOpen_inter_preimage ch.open_target (isOpen_ptsIn W)
    refine DifferentiableAt.differentiableWithinAt ?_
    have hev : (ev X.str (σ.comp e.toRingHom) W f ∘ ch.symm) =ᶠ[𝓝 v]
        fun w => valAt' (ch₀.symm (L.symm w)).1 (j ''ᵁ W) ((j.appIso W).inv.hom f) := by
      filter_upwards [hopen.mem_nhds hv] with w hw
      rw [Function.comp_apply, ev_eq_valAt'_cxOf e σ hj W f hw.2, hchs,
        show cxOf e σ hj (χ.symm (L.symm w)) = ch₀.symm (L.symm w) from hχ _ (htgt w hw.1)]
    refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
    have hb := htgt v hv.1
    refine (differentiableAt_valAt'_symm hex (j ''ᵁ W) _ hb.1 ?_).comp v L.symm.differentiableAt
    rw [← hχ _ hb]
    exact le_preimage_cxOf e σ hj W hv.2
  · show χ y ∈ Metric.ball 0 r'
    rw [hχy]
    exact Metric.mem_ball_self hr'0
  · rw [hch, hχy, map_zero]
  · intro z hz
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc, Set.mem_setOf_eq]
    intro k
    rw [hch, hL, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr'0.le]
    have h1 := (hsrc z hz).2
    rw [mem_ball_zero_iff] at h1
    have h2 : ‖χ z k‖ < r' := (norm_le_pi_norm (χ z) k).trans_lt h1
    calc r'⁻¹ * ‖χ z k‖ < r'⁻¹ * r' := mul_lt_mul_of_pos_left h2 (inv_pos.2 hr'0)
      _ = 1 := inv_mul_cancel₀ hr'0.ne'
  · intro z hz
    refine ⟨hz.1.1.2, ?_⟩
    funext k
    show χ z k = _
    rw [hch, hL, Fin.cast_eq_self, ← mul_assoc, mul_inv_cancel₀ hr'c, one_mul]

end GlobalTheory.LieBase
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FibTors

open GlobalTheory.Models GlobalTheory.UU

theorem exists_relDim_fibre (X : Scheme.{0}) (G : Over X) [GrpObj G] (hG : IsSemiAbelian G) (y : Sp ℂ ⟶ X) :
    ∃ n, SmoothOfRelativeDimension n ((Over.pullback y).obj G).hom := by
  have hG' : IsSemiAbelian ((Over.pullback y).obj G) := IsSemiAbelian.pullback y G hG
  have := hG'.smooth
  have := hG'.geomConnected
  have : ConnectedSpace ((Over.pullback y).obj G).left :=
    GeometricallyConnected.connectedSpace_of_subsingleton ((Over.pullback y).obj G).hom
  exact exists_dim_of_preconnected _ (((1 : 𝟙_ (Over (Sp ℂ)) ⟶ (Over.pullback y).obj G).left) (default : PrimeSpectrum ℂ))

theorem lieBasis_card (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (y : Sp ℂ ⟶ X) (g n : ℕ)
    (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (hadd : ∀ z w, e (z + w) = e z * e w)
    (h1 : ∀ w, ∃! v : epsPt y ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left)
    (h2 : ∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)
    (v : Fin n → (epsR ℂ ⟶ (Over.pullback y).obj G)) (hv : IsLieBasis v) : n = g := by
  classical
  let G' := (Over.pullback y).obj G
  have h0 : e 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  let ρ : epsPt y ⟶ Over.mk ((epsR ℂ).hom ≫ y) := Over.homMk (𝟙 _) rfl
  let T : (epsR ℂ ⟶ G') →* (epsPt y ⟶ G) :=
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom ρ).comp (toBaseHom (toBase_mul_pullback G y) (epsR ℂ))
  have hT : ∀ a, (T a).left = a.left ≫ pullback.fst G.hom y := fun a => Category.id_comp _
  let U : Over (Sp ℂ) := 𝟙_ (Over (Sp ℂ))
  let ρ0 : Over.mk y ⟶ Over.mk (U.hom ≫ y) := Over.homMk (𝟙 _) rfl
  let φ : (U ⟶ G') →* (Over.mk y ⟶ G) :=
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom ρ0).comp (toBaseHom (toBase_mul_pullback G y) U)
  have hη : η[G'].left ≫ pullback.fst G.hom y = (1 : Over.mk y ⟶ G).left := by
    have h' : (φ 1).left = (1 : U ⟶ G').left ≫ pullback.fst G.hom y := Category.id_comp _
    rw [map_one] at h'
    rw [h']
    congr 2
  have hTb : Function.Bijective T := by
    refine ⟨fun a b h => Over.OverMorphism.ext (pullback.hom_ext ?_ ?_), fun p => ?_⟩
    · rw [← hT, ← hT, h]
    · exact (Over.w a).trans (Over.w b).symm
    · refine ⟨Over.homMk (pullback.lift p.left (epsR ℂ).hom (Over.w p)) (pullback.lift_snd _ _ _),
        Over.OverMorphism.ext ((hT _).trans (pullback.lift_fst _ _ _))⟩
  have htan : ∀ a : epsR ℂ ⟶ G', IsTangent a ↔
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (T a).left = (e 0).left := by
    intro a
    rw [h0, hT, ← hη]
    refine ⟨fun h => by rw [← Category.assoc, h], fun h => pullback.hom_ext ?_ ?_⟩
    · rw [Category.assoc]; exact h
    · have e1 : a.left ≫ pullback.snd G.hom y = (epsR ℂ).hom := Over.w a
      have e2 : η[G'].left ≫ pullback.snd G.hom y = 𝟙 _ := Over.w η[G']
      rw [Category.assoc, e1, e2]
      show spMap _ ≫ spMap _ = _
      rw [GlobalTheory.TanMod.spMap_comp']
      have : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ :=
        RingHom.ext fun _ => rfl
      rw [this]
      exact Spec.map_id _
  let Te := MulEquiv.ofBijective T hTb
  have hTe : ∀ a, Te a = T a := fun _ => rfl
  choose D hD _ using h1
  have hDmul : ∀ w w', D (w + w') = D w * D w' := fun w w' =>
    Over.OverMorphism.ext (GlobalTheory.VerticalDeriv.isDerivAt0_unique (hD (w + w'))
      (GlobalTheory.UnifCompare.isDerivAt0_mul (congrArg (·.left) h0) (hD w) (hD w')))
  have hDtan : ∀ w, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (D w).left = (e 0).left := fun w => (hD w).1
  let Dl : (Fin g → ℂ) → (epsR ℂ ⟶ G') := fun w => Te.symm (D w)
  have hTDl : ∀ w, T (Dl w) = D w := fun w => Te.apply_symm_apply (D w)
  have hDl_tan : ∀ w, IsTangent (Dl w) := fun w => (htan _).2 (by rw [hTDl]; exact hDtan w)
  have hDl_add : ∀ w w', Dl (w + w') = Dl w * Dl w' := fun w w' => by
    apply Te.injective
    rw [map_mul, hTe, hTe, hTe, hTDl, hTDl, hTDl, hDmul]
  have hDl_zero : Dl 0 = 1 := by
    have := hDl_add 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hDl_smul : ∀ (c : ℂ) w, (Dl (c • w)).left = spMap (epsScaleR c) ≫ (Dl w).left := by
    intro c w
    have hov : (spMap (epsScaleR c) ≫ (Dl w).left) ≫ G'.hom = (epsR ℂ).hom := by
      rw [Category.assoc, Over.w (Dl w)]
      show spMap _ ≫ spMap _ = spMap _
      rw [GlobalTheory.TanMod.spMap_comp']
      have hc : (epsScaleR c).comp (algebraMap ℂ (DualNumber ℂ)) = algebraMap ℂ (DualNumber ℂ) :=
        RingHom.ext fun a => by ext <;> simp [epsScaleR]
      rw [hc]
    let a : epsR ℂ ⟶ G' := Over.homMk (spMap (epsScaleR c) ≫ (Dl w).left) hov
    have ha : T a = D (c • w) := by
      refine Over.OverMorphism.ext (GlobalTheory.VerticalDeriv.isDerivAt0_unique ?_ (hD (c • w)))
      rw [hT]
      have := GlobalTheory.UnifCompare.isDerivAt0_smul (hD w) c
      rw [← hTDl w, hT] at this
      show IsDerivAt0 _ _ ((spMap (epsScaleR c) ≫ (Dl w).left) ≫ pullback.fst G.hom y)
      rw [Category.assoc]
      exact this
    have : a = Dl (c • w) := by
      apply Te.injective
      rw [hTe, hTe, ha, hTDl]
    rw [← this]
    rfl
  have hDl_inj : ∀ w w', Dl w = Dl w' → w = w' := by
    intro w w' h
    have h' : D w = D w' := by rw [← hTDl, ← hTDl, h]
    exact (h2 (D w) (hDtan w)).unique (hD w) (h' ▸ hD w')
  have hDl_onto : ∀ a, IsTangent a → ∃ w, Dl w = a := by
    intro a ha
    obtain ⟨w, hw, -⟩ := h2 (T a) ((htan a).1 ha)
    refine ⟨w, Te.injective ?_⟩
    rw [Te.apply_symm_apply, hTe]
    exact Over.OverMorphism.ext (GlobalTheory.VerticalDeriv.isDerivAt0_unique (hD w) hw)
  have hsum : ∀ (k : ℕ) (f : Fin k → Fin g → ℂ), Dl (∑ i, f i) = (List.ofFn fun i => Dl (f i)).prod := by
    intro k
    induction k with
    | zero => intro f; simp [hDl_zero]
    | succ k ih =>
      intro f
      rw [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons, hDl_add, ih]
  choose ws hws using fun i => hDl_onto (v i) (hv.1 i)
  have hcomb : ∀ c : Fin n → ℂ, IsLieComb c v (Dl (∑ i, c i • ws i)) := by
    intro c
    refine ⟨fun i => Dl (c i • ws i), fun i => ?_, hsum n _⟩
    rw [hDl_smul, hws]
  have hdet : ∀ (c : Fin n → ℂ) (a a' : epsR ℂ ⟶ G'), IsLieComb c v a → IsLieComb c v a' → a = a' := by
    rintro c a a' ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
    have : u = u' := funext fun i => Over.OverMorphism.ext ((hu i).trans (hu' i).symm)
    rw [this]
  have hli : LinearIndependent ℂ ws := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have e1 := hcomb c
    rw [hc] at e1
    have e2 := hcomb 0
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at e2
    have := (hv.2 (Dl 0) (hDl_tan 0)).unique e1 e2
    exact fun i => congrFun this i
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range ws) := by
    intro w _
    obtain ⟨c, hc, -⟩ := hv.2 (Dl w) (hDl_tan w)
    have := hDl_inj _ _ (hdet c _ _ hc (hcomb c))
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hb := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
  simpa using hb.symm

end GlobalTheory.FibTors


open GlobalTheory.FibTors GlobalTheory.Models GlobalTheory.UU in
theorem GlobalTheory.exists_toric_torsion_cubWeil_one_of_exp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (y : Sp ℂ ⟶ X) (g N : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)), 0 < N → IsExpAt t y e → Function.Surjective e → IsHolTo Set.univ (fun w => (e w).left) → ∃ T : Set (Over.mk y ⟶ t.G), (∀ τ ∈ T, τ ^ N = 1) ∧ (∀ τ ∈ T, ∀ x : Over.mk y ⟶ t.G, x ^ N = 1 → GlobalTheory.UU.CubWeil t.cub N τ x 1) ∧ Nat.card {p : Over.mk y ⟶ t.G // p ^ N = 1} * Nat.card T = N ^ (2 * g) := by
  intro E _ _ _ H X t y g N e hN hexp _ _
  obtain ⟨hadd, hd1, hd2⟩ := hexp
  have h0 : e 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have h1 : ∀ w, ∃! v : epsPt y ⟶ t.G, IsDerivAt0 (fun z => (e z).left) w v.left := by
    intro w
    obtain ⟨v, ⟨hv1, hv2⟩, hu⟩ := hd1 w
    refine ⟨Over.homMk v hv1.1, hv2, fun v' hv' => Over.OverMorphism.ext (hu v'.left ⟨⟨Over.w v', ?_⟩, hv'⟩)⟩
    refine hv'.1.trans ?_
    show (e 0).left = _
    rw [h0]
  have h2 : ∀ v : epsPt y ⟶ t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left := by
    intro v hv
    exact hd2 v.left ⟨Over.w v, by rw [hv, h0]⟩
  obtain ⟨n, hn⟩ := exists_relDim_fibre X t.G t.semi y
  obtain ⟨v, hv⟩ := GlobalTheory.KeyPow.exists_isLieBasis _ hn
  have hng := lieBasis_card X t.G y g n e hadd h1 h2 v hv
  subst hng
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  let G : Over X := t.G
  let x := y
  let k := ℂ
  have h3 := GlobalTheory.laws3
  let G' : Over (Sp k) := (Over.pullback x).obj G
  have hp : IsGrpPullback G' G x (pullback.fst G.hom x) := isGrpPullback_pullback G x
  have hG' : IsSemiAbelian G' := IsSemiAbelian.pullback x G t.semi
  have := hG'.comm
  have := hG'.smooth
  have := hG'.geomConnected
  have dG' : SmoothOfRelativeDimension n G'.hom := hn
  obtain ⟨E⟩ := t.semi.fibres k x
  let := E.addCommGroup
  let := E.grpB
  have := E.free
  have := E.finite
  have := E.i_hom
  obtain ⟨hL, hr, ⟨c', hc'⟩, -⟩ := h3.cubePull _ _ G G' (cubeMapOf hp) t.PP t.cub
  obtain ⟨σ⟩ := GlobalTheory.BiextTriv.main k E.X G' _ c' E.i E.i_hom
  have hw : pullback.fst G.hom x ≫ G.hom = G'.hom ≫ x := pullback.condition
  let U : Over (Sp k) := 𝟙_ (Over (Sp k))
  let ρ : Over.mk x ⟶ Over.mk (U.hom ≫ x) := Over.homMk (𝟙 _) rfl
  let φ : (U ⟶ G') →* (Over.mk x ⟶ G) := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom ρ).comp (toBaseHom (toBase_mul_pullback G x) U)
  have hφ : ∀ a : U ⟶ G', (φ a).left = a.left ≫ pullback.fst G.hom x := fun a => Category.id_comp _
  have hb : Function.Bijective φ := by
    refine ⟨fun a b h => Over.OverMorphism.ext (pullback.hom_ext ?_ ?_), fun p => ?_⟩
    · rw [← hφ, ← hφ, h]
    · exact (Over.w a).trans (Over.w b).symm
    · refine ⟨Over.homMk (pullback.lift p.left (𝟙 _) ((Over.w p).trans (Category.id_comp _).symm))
        (pullback.lift_snd _ _ _), Over.OverMorphism.ext ((hφ _).trans (pullback.lift_fst _ _ _))⟩
  let e' := MulEquiv.ofBijective φ hb
  have he : ∀ a : U ⟶ G', e' a ^ N = 1 ↔ a ^ N = 1 := fun a => by rw [← map_pow, e'.map_eq_one_iff]
  have hcount := GlobalTheory.card_torsion_mul_card_toric_torsion k G' E n N hG' dG' hN'
  refine ⟨e' '' {y | y ^ N = 1 ∧ ∃ t, y = t ≫ E.i}, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ⟨ha, -⟩, rfl⟩
    exact (he a).2 ha
  · rintro _ ⟨_, ⟨ha, s0, rfl⟩, rfl⟩ y hy
    obtain ⟨b, rfl⟩ := e'.surjective y
    have ht : s0 ^ N = 1 := E.isKernel.hom_ext
      (by rw [MonObj.pow_comp, ha, MonObj.one_comp]) (toUnit_unique _ _)
    have h1 := σ.cubWeil ht ((he b).1 hy)
    have h2 := (GlobalTheory.UU.cubWeil_of_isPullCubical _ _ x G G' (cubeMapOf hp) hw (toBase_mul_pullback G x) t.PP _ t.cub c' hc' N U _ _ _ h1).comp ρ
    rw [map_one] at h2
    exact h2
  · rw [← hcount]
    congr 1
    · exact (Nat.card_congr (e'.toEquiv.subtypeEquiv fun a => (he a).symm)).symm
    · exact Nat.card_image_of_injective e'.injective _
end
