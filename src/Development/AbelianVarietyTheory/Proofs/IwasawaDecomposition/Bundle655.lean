module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiAbelianExponentialAlongDisc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle626
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle640
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle641
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle648
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrivialMonodromyOrbitConvergesSymmetricDomain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle625
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle039
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle630
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle627
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArcsOnFlowLinesOfAnalyticModelOnOrbit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle637
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle642
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle643
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle813
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh

theorem isExpAt_homMk {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
    {g : ℕ} (y₁ y₂ : Sp ℂ ⟶ X) (hy : y₁ = y₂) (e : (Fin g → ℂ) → (Over.mk y₁ ⟶ t.G))
    (hw : ∀ w, (e w).left ≫ t.G.hom = y₂)
    (hadd : ∀ z w, e (z + w) = e z * e w)
    (h1 : ∀ w, ∃! v : epsPt y₁ ⟶ t.G, IsDerivAt0 (fun z => (e z).left) w v.left)
    (h2 : ∀ v : epsPt y₁ ⟶ t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left) :
    IsExpAt t y₂ (fun w => (Over.homMk (e w).left (hw w) : Over.mk y₂ ⟶ t.G)) := by
  subst hy
  have he : (fun w => (Over.homMk (e w).left (hw w) : Over.mk y₁ ⟶ t.G)) = e :=
    funext fun w => Over.OverMorphism.ext rfl
  rw [he]
  have hzero : e 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  refine ⟨hadd, fun w => ?_, fun v hv => ?_⟩
  · obtain ⟨V, hV, hVu⟩ := h1 w
    refine ⟨V.left, ⟨⟨V.w, ?_⟩, hV⟩, fun v hv => ?_⟩
    · rw [hV.1]; exact congrArg Over.Hom.left hzero
    · have := hVu (Over.homMk v hv.1.1) hv.2
      exact congrArg CommaMorphism.left this
  · exact h2 (Over.homMk v hv.1) (by rw [hzero]; exact hv.2)

end GlobalTheory.ShFam.Hor.LogCh

namespace GlobalTheory.ShFam.Hor.LogCh

theorem exists_expMaps_near_chart_centre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (n : ℕ) (e0 : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)), (0 : Fin n → ℂ) ∈ e0.target → IsHolTo e0.target (fun z => (e0.symm z).1) → ∃ (g : ℕ) (ρ : ℝ) (ex : ExpMaps Z σ g), 0 < ρ ∧ Metric.ball 0 ρ ⊆ e0.target ∧ IsHolTo (Metric.ball 0 ρ ×ˢ Set.univ) (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => (ex (e0.symm zw.1) zw.2).left) ∧ ∀ x ∈ e0.source, ‖e0 x‖ < ρ → Function.Surjective (ex x) ∧ IsExpAt Z.t (x.1 ≫ genι Z) (ex x) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ n e0 h0 hsy
  let y : (Fin n → ℂ) → (Sp ℂ ⟶ Z.X) := fun z => (e0.symm z).1 ≫ genι Z
  have hy : IsHolTo e0.target y := GlobalTheory.RelExp.isHolTo_of_holAt e0.open_target fun z hz =>
    GlobalTheory.RelExp.HolAt.post ⟨e0.target, e0.open_target, hz, hsy⟩ (genι Z)
  obtain ⟨g, B', e, hB', hb', hfib, -⟩ := GlobalTheory.RelExp.exists_relative_exp_of_smooth _ Z.t.G n e0.target y 0
    Z.t.semi.smooth Z.t.semi.geomConnected e0.open_target h0 hy
  obtain ⟨ρ, hρ, hρB⟩ := Metric.isOpen_iff.1 (hB'.inter e0.open_target) 0 ⟨hb', h0⟩
  have hyx : ∀ x ∈ e0.source, y (e0 x) = x.1 ≫ genι Z := fun x hx => by simp only [y, e0.left_inv hx]
  have hw : ∀ x (hx : x ∈ e0.source) w, (e (e0 x) w).left ≫ Z.t.G.hom = x.1 ≫ genι Z := fun x hx w =>
    (e (e0 x) w).w.trans (hyx x hx)
  classical
  let ex : ExpMaps Z σ g := fun x w =>
    if hx : x ∈ e0.source then Over.homMk (e (e0 x) w).left (hw x hx w) else 1
  refine ⟨g, ρ, ex, hρ, fun z hz => (hρB hz).2, ?_, fun x hx hxρ => ?_⟩
  · refine GlobalTheory.RelExp.isHolTo_of_holAt (Metric.isOpen_ball.prod isOpen_univ) fun q hq => ?_
    refine ((hfib q.1 (hρB hq.1).1).1 q.2).congr ?_
    filter_upwards [(Metric.isOpen_ball.prod isOpen_univ).mem_nhds hq] with q' hq'
    have hs : e0.symm q'.1 ∈ e0.source := e0.map_target (hρB hq'.1).2
    have hr : e0 (e0.symm q'.1) = q'.1 := e0.right_inv (hρB hq'.1).2
    simp only [ex, dif_pos hs, Over.homMk_left]
    rw [hr]
  · have hb : e0 x ∈ B' := (hρB (mem_ball_zero_iff.2 hxρ)).1
    obtain ⟨-, hadd, hsurj, -, h1, h2⟩ := hfib _ hb
    have hex : ex x = fun w => (Over.homMk (e (e0 x) w).left (hw x hx w) : Over.mk (x.1 ≫ genι Z) ⟶ Z.t.G) := funext fun w => dif_pos hx
    rw [hex]
    refine ⟨fun a => ?_, isExpAt_homMk Z.t _ _ (hyx x hx) _ (hw x hx) hadd h1 h2⟩
    obtain ⟨z, hz⟩ := hsurj (Over.homMk a.left (a.w.trans (hyx x hx).symm))
    have hzl := congrArg CommaMorphism.left hz
    exact ⟨z, Over.OverMorphism.ext hzl⟩

end GlobalTheory.ShFam.Hor.LogCh
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.BdArc

theorem exists_matches : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : A →+* ℂ), x ≫ genStr Z = spMap φ → ψ.comp φ = σ → (∀ s, (spMap ψ ≫ x) s ∉ genBd Z) → ∃ y : FrPt Xo c (CAt σ), Matches fr ψ y := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ A _ φ x fr ψ hx hψ hb
  subst hψ
  have := Z.jQ_open
  have : IsLocalRing (CAt (ψ.comp φ)) := inferInstanceAs (IsLocalRing ℂ)
  let ψ' : A →+* CAt (ψ.comp φ) := ψ
  obtain ⟨g, hg⟩ := GlobalTheory.ShFam.EigFrame.exists_baseChange E H Dw l Xo c O β Z A (CAt (ψ.comp φ)) φ (x ≫ genι Z) fr ψ'
  have hr : Set.range (spMap ψ' ≫ x) ⊆ Set.range Z.jQ := by
    rintro _ ⟨s, rfl⟩
    exact not_not.1 (hb s)
  let xF := IsOpenImmersion.lift Z.jQ _ hr
  have hxF : xF ≫ Z.jQ = spMap ψ' ≫ x := IsOpenImmersion.lift_fac _ _ _
  have hs : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F (CAt (ψ.comp φ))) := by
    rw [← Z.jQ_over, ← Category.assoc, hxF, Category.assoc]
    exact (congrArg (spMap ψ' ≫ ·) hx).trans (OpenReg.spMap_comp _ _)
  obtain ⟨y, w, hy, hw⟩ := OpenReg.exists_frPt_of_eigFrame (R := CAt (ψ.comp φ)) xF hs
    (x := spMap ψ' ≫ x ≫ genι Z) (by rw [← Category.assoc, hxF, Category.assoc]) g
  have hp : GlobalTheory.AllWt.ptF y = xF := by
    apply pullback.hom_ext
    · rw [← hy]; exact pullback.lift_fst _ _ _
    · rw [hs]; exact pullback.lift_snd _ _ _
  refine ⟨y, by rw [hp]; exact hxF, fun τ i => ⟨w τ i, by rw [hp]; exact (hw τ i).1, (hw τ i).2.1, ?_⟩⟩
  exact (hw τ i).2.2.trans (hg τ i)

end GlobalTheory.ShFam.BdArc
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.exists_universalTripleFibre_at_framedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (S : Type) [CommRing S] [Nontrivial S] [Algebra c.F S] (y : FrPt Xo c S), 1 ≤ Dw.p + Dw.q → ∃ Φ : FibKey Xo S y.x, Tied e y.s y.u Φ := by
  first | exact @GlobalTheory.KeyFourth.exists_tied | exact GlobalTheory.KeyFourth.exists_tied | (intros; apply GlobalTheory.KeyFourth.exists_tied <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.universal_triple_fibres_base_change_key_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (S S' : Type) [CommRing S] [Algebra c.F S] [CommRing S'] [Nontrivial S'] [Algebra c.F S'] (φ : S →ₐ[c.F] S') (y : FrPt Xo c S) (z : FrPt Xo c S') (Φ : FibKey Xo S y.x) (Φ' : FibKey Xo S' z.x), FrMap φ y z → Tied e y.s y.u Φ → Tied e z.s z.u Φ' → KeyPB Φ'.key Φ.key φ.toRingHom := by
  first | exact @GlobalTheory.KeyFourth.tied_keyPB | exact GlobalTheory.KeyFourth.tied_keyPB | (intros; apply GlobalTheory.KeyFourth.tied_keyPB <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.BdArc

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem tendsto_pow_mul_exp (C C' c c' T : ℝ) (B : ℕ) (hc : 0 < c) (hc' : 0 < c') :
    Tendsto (fun w : ℂ => C * Real.exp (-c * (c' * (w.im - T))) * (C' * w.im ^ B)) imTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => t ^ B * Real.exp (-(c * c') * t)) atTop (𝓝 0) := by
    have := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (B : ℝ) (c * c') (mul_pos hc hc')
    simpa only [Real.rpow_natCast] using this
  have h2 := (h1.const_mul (C * C' * Real.exp (c * c' * T))).comp (tendsto_comap (f := Complex.im))
  rw [mul_zero] at h2
  refine h2.congr fun w => ?_
  have : Real.exp (-c * (c' * (w.im - T))) = Real.exp (c * c' * T) * Real.exp (-(c * c') * w.im) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only [Function.comp, this]
  ring

theorem tendsto_cusp {N : ℕ} {X : Data E N} {T : ℝ} {x : ℂ → Frame X.Ψ N} {la : Wt X.Ψ N} {P : Frame X.Ψ N → ℂ}
    (hP : P ∈ X.SS la) (hd : ∀ w : ℂ, T < w.im → x w ∈ X.dom) {ξ : Fin N → E} {c' : ℝ} (hξ : X.IsIso ξ) (hc' : 0 < c')
    (ht : ∀ w : ℂ, T + 1 < w.im → ∀ τ, c' * (w.im - T) ≤ X.tt ξ (x w) τ) {C' : ℝ} {B : ℕ}
    (hn : ∀ᶠ w in imTop, 0 < X.nfac la (x w) ∧ (X.nfac la (x w))⁻¹ ≤ C' * w.im ^ B) :
    Tendsto (fun w => P (x w)) imTop (𝓝 0) := by
  obtain ⟨C, c, hc, hC⟩ := GlobalTheory.T.pnorm_le_exp_neg_of_mem_SS_of_isIso E N X la P ξ hP hξ
  refine squeeze_zero_norm' ?_ (tendsto_pow_mul_exp C C' c c' T B hc hc')
  have he : ∀ᶠ w in imTop, T + 1 + 1 / c' < w.im :=
    (tendsto_comap (f := Complex.im)).eventually (eventually_gt_atTop _)
  filter_upwards [hn, he] with w h1 h2
  have h0 : 0 < 1 / c' := by positivity
  have h3 : 1 ≤ c' * (w.im - T) := by
    have : 1 / c' ≤ w.im - T := by linarith
    rwa [div_le_iff₀' hc'] at this
  have h4 := hC (x w) (hd w (by linarith)) _ h3 (ht w (by linarith))
  have h5 : ‖P (x w)‖ = X.pnorm la P (x w) * (X.nfac la (x w))⁻¹ := by
    show _ = ‖P (x w)‖ * X.nfac la (x w) * _
    rw [mul_assoc, mul_inv_cancel₀ h1.1.ne', mul_one]
  have h6 : 0 ≤ X.pnorm la P (x w) := mul_nonneg (norm_nonneg _) h1.1.le
  rw [h5]
  exact mul_le_mul h4 h1.2 (inv_nonneg.2 h1.1.le) (h6.trans h4)

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type}
  [CommRing O] {β : O →+* c.F}

end GlobalTheory.ShFam.BdArc
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

theorem _root_.GlobalTheory.T.trivial_monodromy_orbit_converges_symmetric_domain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (T : ℝ) (M : ℕ) (x : ℂ → Frame X.Ψ N), IsOrbit X T M 1 x → ∃ x₀ ∈ X.dom, ∃ x' : ℂ → Frame X.Ψ N, Tendsto x' imTop (𝓝 x₀) ∧ ∀ᶠ w in imTop, x' w ∈ X.dom ∧ SamePos X (x w) (x' w) := by
  first | exact @GlobalTheory.ShFam.OrbitLimit.orbit_limit | exact GlobalTheory.ShFam.OrbitLimit.orbit_limit | (intros; apply GlobalTheory.ShFam.OrbitLimit.orbit_limit <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.LineNorm

section Closure

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

omit [NumberField F] in
theorem isEqn_sum {α : Type} (s : Finset α) {Δ : α → Y.Dv} {t : α → Y.Fnˣ} (y : Y.X)
    (h : ∀ a, (Δ a).IsEqn y (t a)) : (∑ a ∈ s, Δ a).IsEqn y (∏ a ∈ s, t a) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact CartierDiv.isEqn_zero y
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (h a).add ih

end Closure

section Steps

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {F : Type} [Field F] [NumberField F] {Y : Var F}


open Classical in
def mixLog (ρ : Y.X ⟶ X) {m : ℕ}
    (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (b : ℕ → Bool) (i : Fin m) : PtFn Y :=
  fun v ε y =>
    if hp : (resP v).Prime then
      haveI := Fact.mk hp
      let ψ : Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v] := (ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom
      (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
        Real.log (GlobalTheory.ShFam.Pad.grNorm t (spMap ψ ≫ stalkPt Y (below y.1) ≫ ρ)
          (lat t (resP v) (spMap ψ ≫ stalkPt Y (below y.1) ≫ ρ) (b (resP v)))
          (fun l => spMap (dualMap ψ) ≫ f (below y.1) l) i)
    else 0

end Steps

section Flags

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (C : FlagCpt Z e)

abbrev fr (y : C.Y.X) := (C.gr_spec y).choose_spec.choose

abbrev dg (y : C.Y.X) : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ := (C.gr_spec y).choose_spec.choose_spec.choose

omit [NumberField F] in
theorem fr_spec (y : C.Y.X) : (fr C y).Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 (dg C y) ∧
    ∀ τ i, (C.gr τ i).IsEqn y (dg C y τ i) := (C.gr_spec y).choose_spec.choose_spec.choose_spec





open Classical in
def symLog (b : ℕ → Bool) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) : PtFn C.Y := fun v ε y =>
  if hp : (resP v).Prime then
    haveI := Fact.mk hp
    let ψ : C.Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v] := (ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom
    (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
      lnStep Z.t (spMap ψ ≫ stalkPt C.Y (below y.1) ≫ C.π ≫ genι Z)
        (fun τ i => spMap (dualMap ψ) ≫ (C.gr_spec (below y.1)).choose_spec.choose.v τ i) (resP v) (b (resP v)) st
  else 0


open Classical in
def lgCopy (w : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt C.Y) : ℝ :=
  if hp : (resP v).Prime then
    haveI := Fact.mk hp
    let f := (C.gr_spec (below y.1)).choose_spec.choose
    let t := (C.gr_spec (below y.1)).choose_spec.choose_spec.choose
    let ψ : C.Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v] := (ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom
    Real.log (ε.w (valAt y.1 (((∏ x : Letter Dw, t x.1 x.2 ^ expo Dw w x) *
        (eqn (divOf C (expo Dw w)) (below y.1))⁻¹ : C.Y.Fnˣ) : C.Y.Fn))) +
      (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
        w.sum fun a n => (n : ℝ) * lnStep Z.t (spMap ψ ≫ stalkPt C.Y (below y.1) ≫ C.π ≫ genι Z)
          (fun τ i => spMap (dualMap ψ) ≫ f.v τ i) (resP v) (a.1 (resP v)) a.2.2
  else 0

theorem lgOf_eq_lgCopy : @lgOf = @lgCopy := rfl

theorem mul_finsupp_sum {α : Type} (w : α →₀ ℤ) (c : ℝ) (g : α → ℝ) :
    c * w.sum (fun a n => (n : ℝ) * g a) = ∑ a ∈ w.support, (w a : ℝ) * (c * g a) := by
  simp only [Finsupp.sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => mul_left_comm _ _ _

theorem lgCopy_eq (w : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt C.Y) :
    lgCopy C w v ε y = Real.log (ε.w (valAt y.1 (((∏ x : Letter Dw, dg C (below y.1) x.1 x.2 ^ expo Dw w x) *
      (eqn (divOf C (expo Dw w)) (below y.1))⁻¹ : C.Y.Fnˣ) : C.Y.Fn))) +
      ∑ a ∈ w.support, (w a : ℝ) * symLog C a.1 a.2.2 v ε y := by
  obtain ⟨hp, -⟩ := GlobalTheory.ShFam.Pad.ioOf_spec F v ε
  simp only [lgCopy, symLog, dif_pos hp]
  refine congrArg₂ (fun a b : ℝ => a + b) rfl ?_
  refine (mul_finsupp_sum _ _ _).trans ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  refine congrArg _ (congrArg _ ?_)
  rfl


end Flags

end GlobalTheory.LineNorm
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.arcs_on_flow_lines_of_analytic_model_on_orbit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (Λ : GtAn₀ aC), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → letI := H.starRing; ∀ (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] Λ.A.La) (ξ : Module.Dual ℤ Λ.A.X), OnOrbit Uw k ξ' x Λ.A gam ξ → ξ ≠ 0 → Module.finrank (𝓞 E) Λ.A.X = 1 → (∀ v, Λ.Lifts (aC.eta v) (gam (Uw.F.t (Uw.ik k) v))) → (∀ v, Λ.Lifts (aC.etaA v) (gam (Uw.F.t (Uw.ik k) v))) → ∀ (O : Type) [CommRing O] (β : O →+* c.F), FlowTie Uw (aC.restrict β) k ξ' x := by
  first | exact @GlobalTheory.CuspFrom.flowTie_of_onOrbit | exact GlobalTheory.CuspFrom.flowTie_of_onOrbit | (intros; apply GlobalTheory.CuspFrom.flowTie_of_onOrbit <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

theorem _root_.GlobalTheory.T.exists_graded_line_divisors_full_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (Y : GlobalTheory.ProjVar.Var F) (π : Y.X ⟶ gen Z) (f₀ : EigFrame Z (constF e Y) (genericPt Y ≫ π ≫ genι Z)) (S : Fr (ratOf Y) Dw.mult Dw.mult) (A₀ : Mat Dw.mult Y.Fn), Tied e Y π f₀ S A₀ → ∃ gr : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Dv, ∀ y : Y.X, ∃ (φ : c.F →+* Y.X.presheaf.stalk y) (f : EigFrame Z φ (stalkPt Y y ≫ π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Fnˣ), f.Tri (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField) f₀ t ∧ ∀ τ i, (gr τ i).IsEqn y (t τ i) := by
  first | exact @GlobalTheory.ShFam.GradedDiv.exists_gr | exact GlobalTheory.ShFam.GradedDiv.exists_gr | (intros; apply GlobalTheory.ShFam.GradedDiv.exists_gr <;> assumption)
end

section

open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom

theorem _root_.GlobalTheory.T.fourierJacobi_constant_term_eq_zero_of_flow_line : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (x : Frame X.Ψ r) (s : X.Ψ → ℂ) (d : X.Ψ → ℝ) (T : ℝ) (g : ℤ → ℂ), X.IsSec la P → FreqNonneg X la P → X.IsIso ξ → x ∈ X.dom → (∀ τ, 0 < d τ) → (∀ m ≤ 0, g m = 0) → (∀ w : ℂ, T < w.im → X.flow ξ (fun τ => s τ + w * (d τ : ℂ)) x ∈ X.dom ∧ HasSum (fun m : ℤ => g m * ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi w ^ m) (P (X.flow ξ (fun τ => s τ + w * (d τ : ℂ)) x))) → X.fj la ξ 0 P x = 0 := by
  first | exact @GlobalTheory.CuspLimit.fj_zero_eq_zero_of_line | exact GlobalTheory.CuspLimit.fj_zero_eq_zero_of_line | (intros; apply GlobalTheory.CuspLimit.fj_zero_eq_zero_of_line <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle GlobalTheory.ShFam.EigLoc GlobalTheory.ShFam.EigCoord GlobalTheory.LieLocBasis

theorem _root_.GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (R : Type) [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x) (R' : Type) [CommRing R'] (φ' : c.F →+* R') (x' : Sp R' ⟶ Z.X) (ψ : R →+* R'), IsLocalRing R' → f.Stable → x' = spMap ψ ≫ x → φ' = ψ.comp φ → (∀ g : EigFrame Z φ' x', (∃! A : Mat Dw.mult R', f.Coord ψ g A) ∧ ∀ A, f.Coord ψ g A → ∀ τ, IsUnit (A τ).det) ∧ ∀ A : Mat Dw.mult R', (∀ τ, IsUnit (A τ).det) → ∃ g : EigFrame Z φ' x', f.Coord ψ g A := by
  intro E _ _ _ H Dw l Xo c O _ β Z R _ φ x f R' _ φ' x' ψ _ hf hx' hφ'
  subst hx' hφ'
  obtain ⟨g₀, hg₀⟩ := hf R' ψ
  obtain ⟨n, xc, hx⟩ := exists_chart Z.t (spMap ψ ≫ x)
  choose B₀ hB₀ using exists_basis hx g₀
  have hv : ∀ τ, (fun k => spMap (dualMap ψ) ≫ f.v τ k) = g₀.v τ := fun τ => funext fun k => (hg₀ τ k).symm
  have key : ∀ (g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x))
      (B : ∀ τ, Module.Basis (Fin (Dw.mult τ)) R' (eig c (ψ.comp φ) hx τ)),
      (∀ τ i, g.v τ i = vec Z.t _ xc (B τ i)) → ∀ A : Mat Dw.mult R',
        f.Coord ψ g A ↔ ∀ τ i, B τ i = ∑ j, A τ i j • B₀ τ j := fun g B hB A => by
    simp only [EigFrame.Coord, true_and]
    refine forall_congr' fun τ => forall_congr' fun i => ?_
    rw [hv, hB, show g₀.v τ = fun j => vec Z.t _ xc (B₀ τ j) from funext (hB₀ τ), comb_iff hx, Subtype.ext_iff]
    simp
  refine ⟨fun g => ⟨?_, fun A hA τ => ?_⟩, fun A hA => ?_⟩
  · choose A hA hu using fun τ i => g₀.basis τ (g.v τ i) (g.tan τ i) (g.eig τ i)
    refine ⟨A, ⟨rfl, rfl, fun τ i => by rw [hv]; exact hA τ i⟩, fun A' hA' => ?_⟩
    funext τ i
    exact hu τ i _ (by have := hA'.2.2 τ i; rwa [hv] at this)
  · choose B hB using exists_basis hx g
    exact isUnit_det_of_basis (B₀ τ) (B τ) (A τ) ((key g B hB A).1 hA τ)
  · choose B hB using fun τ => exists_basis_of_isUnit (B₀ τ) (A τ) (hA τ)
    obtain ⟨g, hg⟩ := exists_frame hx B
    exact ⟨g, (key g B hg A).2 hB⟩
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.arc_framed_point_extends_to_model_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) [Algebra c.F ℂ⸨X⸩] (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (th : a.D₀.P.L.Sec) (y : FrPt Xo c ℂ⸨X⸩), (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → ArcBasis W (fun τ => σ.comp (embK c τ)) e → IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → χ (IsLocalRing.closedPoint (PowerSeries ℂ)) ∉ abLocus Y.t.G → BdExt Y ((PowerSeries.C (R := ℂ)).comp σ) y := by
  first | exact @GlobalTheory.CuspFrom.arc_bdExt | exact GlobalTheory.CuspFrom.arc_bdExt | (intros; apply GlobalTheory.CuspFrom.arc_bdExt <;> assumption)
end
