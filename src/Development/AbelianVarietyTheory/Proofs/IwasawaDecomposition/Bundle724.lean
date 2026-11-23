module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1103
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle668
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle711
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle716
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle718
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle638
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle399
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle046
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle708
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle388
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle028
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle699
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle667
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle669
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullLinInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealConeCoveredByStarAtPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle715
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle003
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle206
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532

@[expose] public section

section

set_option autoImplicit false

noncomputable section

section SlopeTestRemainingChoices

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam
open GlobalTheory.ArcQ GlobalTheory.FlagBundle Filter Topology

namespace GlobalTheory.FrameLift

open GlobalTheory.ShFam.Hor.LogCh

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {σ : c.F →+* ℂ} {r : ℕ}

theorem nonempty_unfWit {U : Formalism.L2.PjFree.Unf Xo c σ r} (hU : Formalism.L2.PjFree.IsUnf U) : Nonempty (UnfWit U) := by
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, hiso, hP⟩ := hU
  choose Pm h1 h2 h3 h4 h5 using hP
  exact ⟨⟨g, e, F, ik, φ, hiso, Pm, h1, h2, fun k x => ⟨h3 k x, h4 k x⟩, h5⟩⟩

theorem exists_transport {p q : CxPts (genStr Z) σ} (h : p = q) (G : EigFrame Z σ (p.1 ≫ genι Z)) :
    ∃ G' : EigFrame Z σ (q.1 ≫ genι Z), (∀ τ i, G'.v τ i = G.v τ i) ∧
      ∀ (M : EigMet Z σ) τ, M.gram q G' τ = M.gram p G τ := by
  subst h
  exact ⟨G, fun _ _ => rfl, fun _ _ => rfl⟩

theorem exists_coords {U : Formalism.L2.PjFree.Unf Xo c σ r} (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) {n : ℕ}
    {B : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hB : IsOpen B) {b₀ : ReciprocityTheory.L2DbarEstimates.V n} (hb₀ : b₀ ∈ B)
    {s : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ r} (hs : ∀ b ∈ B, s b ∈ (U.X k).dom)
    (hd : DifferentiableOn ℂ s B) (V : (gen Z).affineOpens) {φ : c.F →+* Γ(gen Z, V.1)}
    (Φ : EigFrame Z φ (LogKS.chart V ≫ genι Z))
    (hV : ∀ b (hb : b ∈ B), cxPt Z (U.un k ⟨s b, hs b hb⟩) ∈ ptsIn (genStr Z) σ V.1) :
    ∃ N : ReciprocityTheory.L2DbarEstimates.V n → Mat Dw.mult ℂ, (∀ τ a a', DifferentiableOn ℂ (fun b => N b τ a a') B) ∧
      ∀ b (hb : b ∈ B) (y : CxPts (genStr Z) σ), cxPt Z (U.un k ⟨s b, hs b hb⟩) = y →
        ∀ (hy : y ∈ ptsIn (genStr Z) σ V.1) (G f : EigFrame Z σ (y.1 ≫ genι Z)),
          (∀ τ i, G.v τ i = (cxFrame Z (U.un k ⟨s b, hs b hb⟩)).v τ i) → (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v Φ embτ basisIdx) (evHom hy) f →
            ∀ τ, G.co f τ = N b τ := by
  classical
  obtain ⟨W⟩ := nonempty_unfWit hU
  let L := EuclideanSpace.equiv (Fin n) ℂ
  set B₁ : Set (Fin n → ℂ) := L.symm ⁻¹' B with hB₁
  have hB₁o : IsOpen B₁ := hB.preimage L.symm.continuous
  let x : (Fin n → ℂ) → (U.X k).dom := fun v =>
    if h : L.symm v ∈ B then ⟨s (L.symm v), hs _ h⟩ else ⟨s b₀, hs _ hb₀⟩
  have hx : ∀ v ∈ B₁, (x v).1 = s (L.symm v) := fun v hv => by
    simp only [x, dif_pos (show L.symm v ∈ B from hv)]
  have hxL : ∀ b (hb : b ∈ B), x (L b) = ⟨s b, hs b hb⟩ := fun b hb =>
    Subtype.ext ((hx _ (by simpa [hB₁] using hb)).trans (by rw [ContinuousLinearEquiv.symm_apply_apply]))
  have hsd : DifferentiableOn ℂ (fun v => s (L.symm v)) B₁ := hd.comp L.symm.differentiableOn fun v hv => hv
  have hPd : ∀ a, DifferentiableOn ℂ (fun v => W.Pm k (x v) a) B₁ := fun a => differentiableOn_pi.2 fun j =>
    (GlobalTheory.TrueCx.TorHolo.differentiableOn_perFr (U.X k) (x := fun v => s (L.symm v)) (fun v hv => hs _ hv)
      (fun τ a a' => differentiableOn_pi.1 (differentiableOn_pi.1 (differentiableOn_pi.1 hsd τ) a) a') _ _ _).congr
      fun v hv => by rw [W.Pm_eq, hx v hv]
  let p : (Fin n → ℂ) → (Sp ℂ ⟶ Xo.XF c) := fun v => GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k (x v))
  have hu : ∀ v, W.F.u (W.ik k) (W.Pm k (x v)) =
      p v ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) :=
    fun v => (W.lie k (x v)).1.symm.trans (ptF_fst (U.un k (x v))).symm
  have hp : ∀ v, p v ≫ pullback.snd _ _ = spMap σ := fun v => ptF_snd (U.un k (x v))
  choose Y hY hYd using fun (a : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) =>
    GlobalTheory.ModelExpCoord.coord_holomorphic _ _ _ _ _ _ _ _ Z σ W.g _ W.F (W.ik k) n B₁ (fun v => W.Pm k (x v)) p hu V
      (Φ.v a.1 a.2) hB₁o (fun v => W.period k (x v)) hPd hp (Φ.tan a.1 a.2)
  refine ⟨fun b τ => of fun a a' => Y ⟨τ, a'⟩ (L b) (W.e.symm ⟨τ, a⟩), fun τ a a' => ?_, fun b hb y hq hy G f hG hf τ => ?_⟩
  · refine differentiableOn_pi.1 ((hY ⟨τ, a'⟩).comp L.differentiableOn fun b hb => ⟨by simpa [hB₁] using hb, ?_⟩) _
    show ⊤ ≤ (cxPt Z (U.un k (x (L b)))).1 ⁻¹ᵁ V.1
    rw [hxL b hb]
    exact hV b hb
  · ext a a'
    obtain ⟨w, hwt, hwm, hwc⟩ := GlobalTheory.HodgeSmooth.exists_lift_comb _ hq G f hG τ a'
    have h1 := hYd ⟨τ, a'⟩ (L b) (by simpa [hB₁] using hb) y hy (by
      show _ = (cxPt Z (U.un k (x (L b)))).1
      rw [hxL b hb, hq])
    have hfv : spMap (dualMap (evHom hy)) ≫ Φ.v τ a' = w ≫ Z.m.φ := by rw [hwm, hf τ a']
    rw [hfv] at h1
    have hbase : w ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ p (L b) := by
      show _ = _ ≫ GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k (x (L b)))
      rw [hxL b hb]
      exact hwt.1
    have h2 := isDerivAt0_ex_of_push Z W.F (p (L b)) (W.ik k) (W.Pm k (x (L b))) (W.period k _) (hu _) hbase h1
    rw [hxL b hb] at h2
    have per := W.period k ⟨s b, hs b hb⟩
    obtain ⟨hPx, hv⟩ := W.lie k ⟨s b, hs b hb⟩
    have h3 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ _ _ W.F _ _ per _ ((U.un k ⟨s b, hs b hb⟩).u τ) _ (hv τ) _
      _).1 (hPx ▸ hwc)
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ W.F _ _ per
    have h4 := congrFun ((tn.2.2 _ (tn.1 _ _ h2)).unique h2 h3) (W.e.symm ⟨τ, a⟩)
    have hi : ∀ j j' : Fin (Dw.mult τ), W.e.symm ⟨τ, j⟩ = W.e.symm ⟨τ, j'⟩ ↔ j = j' := fun j j' => by simp
    refine Eq.trans ?_ h4.symm
    simp [Finset.sum_apply, Pi.single_apply, hi]

variable {F : Type} [Field F] {X : Var F} {σ' : F →+* ℂ}

theorem eventually_regAt {y : CxPts X.str σ'} {g : X.Fn} (hg : RegAt (under y) g) : ∀ᶠ z in 𝓝 y, RegAt (under z) g := by
  obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
  filter_upwards [(isOpen_ptsIn W).mem_nhds (mem_ptsIn.2 hW)] with z hz
  exact regAt_fnOf (mem_ptsIn.1 hz) _ a

theorem eventually_mem {ι : Type} [Finite ι] {m : ι → ℕ} {S : Fr (ratOf X) m 0} {y : CxPts X.str σ'} {A : Mat m X.Fn}
    (hA : A ∈ S.S (under y)) : ∀ᶠ z in 𝓝 y, A ∈ S.S (under z) := by
  obtain ⟨U, B, hU, hB, hS⟩ := S.loc (under y)
  have hP := (hS _ hU A).1 hA
  have hU' : ∀ᶠ z in 𝓝 y, under z ∈ U := by
    filter_upwards [(isOpen_ptsIn U).mem_nhds (mem_ptsIn.2 hU)] with z hz
    exact mem_ptsIn.1 hz
  have h1 : ∀ᶠ z in 𝓝 y, ∀ τ, (∀ i j, RegAt (under z) ((A * B⁻¹) τ i j)) ∧ RegAt (under z) ((A * B⁻¹) τ).det⁻¹ :=
    Filter.eventually_all.2 fun τ => (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      eventually_regAt (mem_O_ratOf.1 ((hP τ).1 i j))).and (eventually_regAt (mem_O_ratOf.1 (hP τ).2.2.1))
  filter_upwards [hU', h1] with z hz hz1
  exact (hS _ hz A).2 fun τ => ⟨fun i j => mem_O_ratOf.2 ((hz1 τ).1 i j), (hP τ).2.1, mem_O_ratOf.2 (hz1 τ).2,
    fun i j hi => absurd hi (by simp)⟩

theorem analyticAt_ratVal {d : ℕ} (ch : AlgChart X.str σ' d) {y : CxPts X.str σ'} (hy : y ∈ ch.e.source) {g : X.Fn}
    (hg : RegAt (under y) g) : AnalyticAt ℂ (fun w => ratVal g (ch.e.symm w)) (ch.e y) := by
  obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
  refine GlobalTheory.SCV.analyticAt_of_differentiableOn ((ch.holo W a).congr fun w hw => ratVal_fnOf hw.2 _ a)
    ((GlobalTheory.ChartGlue.isOpen_over ch.e (isOpen_ptsIn W)).mem_nhds ⟨ch.e.map_source hy, ?_⟩)
  show ch.e.symm (ch.e y) ∈ ptsIn X.str σ' W
  rw [ch.e.left_inv hy]
  exact mem_ptsIn.2 hW

end GlobalTheory.FrameLift

end SlopeTestRemainingChoices

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

theorem GlobalTheory.FrameLift.exists_holomorphic_frame_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), ∀ (k' : U.Comp) (s : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q)), AnalyticAt ℂ s (c'.e y) → (∀ᶠ w in 𝓝 (c'.e y), ∃ hs : s w ∈ (U.X k').dom, cxPt T.Z (U.un k' ⟨s w, hs⟩) = cxOf e σ hj (c'.e.symm w)) → ∃ K : ReciprocityTheory.L2DbarEstimates.V X.dim → Mat Dw.mult ℂ, (∀ τ a b, AnalyticAt ℂ (fun w => K w τ a b) (c'.e y)) ∧ (∀ τ, IsUnit (K (c'.e y) τ).det) ∧ ∀ᶠ w in 𝓝 (c'.e y), (∃ g : EigFrame T.Z σ ((cxOf e σ hj (c'.e.symm w)).1 ≫ genι T.Z), FrameAt e f₀ A₀ A (c'.e.symm w) g) ∧ ∀ (hs : s w ∈ (U.X k').dom) (g : EigFrame T.Z σ ((cxOf e σ hj (c'.e.symm w)).1 ≫ genι T.Z)), FrameAt e f₀ A₀ A (c'.e.symm w) g → ∀ (M : EigMet T.Z σ) (τ : E →+* ℂ), M.gram (cxOf e σ hj (c'.e.symm w)) g τ = (K w τ)ᴴ * M.gram (cxPt T.Z (U.un k' ⟨s w, hs⟩)) (cxFrame T.Z (U.un k' ⟨s w, hs⟩)) τ * K w τ := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U _ hU X j f₀ Eb A₀ hj hoi hT y _ c' hyc A hA k' s hs hlift
  obtain ⟨V₀, hV₀, φ, Φ, hzV, hφ, -⟩ := EigSpread.exists_stable_eigFrame E H Dw l Xo c O β T.Z
    ((cxOf e σ hj y).1 (IsLocalRing.closedPoint ℂ))
  let V : (gen T.Z).affineOpens := ⟨V₀, hV₀⟩
  have hφ' : LogKS.chart V ≫ genStr T.Z = spMap φ := hφ
  have hyV : cxOf e σ hj y ∈ ptsIn (genStr T.Z) σ V.1 := mem_ptsIn.2 hzV
  obtain ⟨M, hM⟩ := GlobalTheory.T.frame_coordinates_eq_rational_matrix_values_chart E H Dw l Xo c O β T.Z σ F e X j f₀ Eb A₀ hj hoi hT V φ Φ hφ' A
  have hpre : ∀ z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom),
      z ∈ ptsIn X.str (σ.comp e.toRingHom) (j ⁻¹ᵁ V.1) ↔ cxOf e σ hj z ∈ ptsIn (genStr T.Z) σ V.1 :=
    fun z => mem_ptsIn_preimage (m := cxOf e σ hj) (f := j) (fun _ => rfl)
  have hVn : ∀ᶠ z in 𝓝 y, cxOf e σ hj z ∈ ptsIn (genStr T.Z) σ V.1 := by
    filter_upwards [(isOpen_ptsIn _).mem_nhds ((hpre y).2 hyV)] with z hz
    exact (hpre z).1 hz
  have htend : Tendsto c'.e.symm (𝓝 (c'.e y)) (𝓝 y) := c'.e.tendsto_symm hyc
  obtain ⟨B, hBall, hB, hb₀⟩ := eventually_nhds_iff.1 ((hlift.and hs.eventually_analyticAt).and
    (htend.eventually (hVn.and (GlobalTheory.FrameLift.eventually_mem hA))))
  choose hsB hpt using fun b hb => (hBall b hb).1.1
  obtain ⟨N, hN, hNco⟩ := GlobalTheory.FrameLift.exists_coords (Z := T.Z) hU k' hB hb₀ hsB
    (fun b hb => (hBall b hb).1.2.differentiableAt.differentiableWithinAt) V Φ
    (fun b hb => by rw [hpt b hb]; exact (hBall b hb).2.1)
  have key : ∀ b (hb : b ∈ B) (G g : EigFrame T.Z σ ((cxOf e σ hj (c'.e.symm b)).1 ≫ genι T.Z)),
      (∀ τ i, G.v τ i = (cxFrame T.Z (U.un k' ⟨s b, hsB b hb⟩)).v τ i) → FrameAt e f₀ A₀ A (c'.e.symm b) g →
        ∀ τ, G.co g τ = N b τ * (M τ).map fun r => ratVal r (c'.e.symm b) := by
    intro b hb G g hG hg τ
    obtain ⟨-, hzV, hzS⟩ := hBall b hb
    have hov : σ = (evHom hzV).comp φ := by
      generalize cxOf e σ hj (c'.e.symm b) = z at hzV
      exact GlobalTheory.ShFam.EigLoc.spMap_inj (z.2.symm.trans (by
        rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hφ', ← Category.assoc, GlobalTheory.LieMet.spMap_evHom hzV]))
    have hx : (cxOf e σ hj (c'.e.symm b)).1 ≫ genι T.Z = spMap (evHom hzV) ≫ LogKS.chart V ≫ genι T.Z := by
      rw [← Category.assoc, GlobalTheory.LieMet.spMap_evHom hzV]
    obtain ⟨f, hf⟩ := Φ.exists_isMap (evHom hzV) hov hx
    rw [← hNco b hb _ (hpt b hb) hzV G f hG hf τ, ← (hM _ hzS hzV).2.2 g hg f hf τ, EigFrame.co_mul]
  have hex : ∀ b ∈ B, ∃ g : EigFrame T.Z σ ((cxOf e σ hj (c'.e.symm b)).1 ≫ genι T.Z),
      FrameAt e f₀ A₀ A (c'.e.symm b) g := fun b hb => (hM _ (hBall b hb).2.2 (hBall b hb).2.1).2.1
  refine ⟨fun b τ => N b τ * (M τ).map fun r => ratVal r (c'.e.symm b), fun τ a a' => ?_, fun τ => ?_, ?_⟩
  · simp only [Matrix.mul_apply, Matrix.map_apply]
    exact Finset.analyticAt_fun_sum _ fun i _ =>
      (GlobalTheory.SCV.analyticAt_of_differentiableOn (hN τ a i) (hB.mem_nhds hb₀)).mul
        (GlobalTheory.FrameLift.analyticAt_ratVal c' hyc ((hM y hA hyV).1 τ i a'))
  · obtain ⟨g, hg⟩ := hex _ hb₀
    obtain ⟨G, hG, -⟩ := GlobalTheory.FrameLift.exists_transport (hpt _ hb₀) (cxFrame T.Z _)
    show IsUnit (N (c'.e y) τ * (M τ).map fun r => ratVal r (c'.e.symm (c'.e y))).det
    rw [← key _ hb₀ G g hG hg τ]
    exact G.isUnit_det_co g τ
  · filter_upwards [hB.mem_nhds hb₀] with b hb
    refine ⟨hex b hb, fun hsb g hg Me τ => ?_⟩
    obtain ⟨G, hG, hGm⟩ := GlobalTheory.FrameLift.exists_transport (hpt b hb) (cxFrame T.Z _)
    rw [← key b hb G g hG hg τ, ← hGm Me τ]
    exact Me.change _ G g τ

end
end

section

open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.HodgeSmooth
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false


theorem _root_.GlobalTheory.T.hodgeMetric_frame_eq_riemannForm_at_interior_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (W : UnfWit (unfFam U σ)), Function.Injective W.ik → ∀ (d : (unfFam U σ).Comp → (E →+* ℂ) → ℝ), (∀ (k : (unfFam U σ).Comp) (x : ((unfFam U σ).X k).dom), IsOrth ((unfFam U σ).X k) x.1 → ∀ τ : E →+* ℂ, 0 < Dw.mult τ → 0 < d k τ) → (∀ (k : (unfFam U σ).Comp) (x : ((unfFam U σ).X k).dom), IsOrth ((unfFam U σ).X k) x.1 → ∀ (i : Fin W.F.n) (P : (W.F.Di i).La →+ (Fin W.g → ℂ)), IsPeriod (W.F.Di i) (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1) P → ∀ (Hm : Matrix (Fin W.g) (Fin W.g) ℂ), (∀ v w, (hermForm Hm (P v) (P w)).im = (W.F.Di i).EF v w) → W.F.u i P = ((unfFam U σ).un k x).x → ∀ (τ τ' : E →+* ℂ) (zz : Fin (Dw.mult τ) → (Fin W.g → ℂ)) (zz' : Fin (Dw.mult τ') → (Fin W.g → ℂ)) (uu : Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (uu' : Fin (Dw.mult τ') → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (T' : Matrix (Fin (Dw.mult τ')) (Fin (Dw.mult τ')) ℂ), (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz b) (uu b)) → (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz' b) (uu' b)) → (∀ b, IsCombAt ((unfFam U σ).un k x).x (((unfFam U σ).un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => T b' b) (uu b)) → (∀ b, IsCombAt ((unfFam U σ).un k x).x (((unfFam U σ).un k x).u τ') (show Fin (Dw.mult τ') → CAt σ from fun b' => T' b' b) (uu' b)) → (of fun b b' => hermForm Hm (zz b') (zz b)) = ((d k τ : ℝ) : ℂ) • (Tᴴ * T) ∧ (τ' ≠ τ → ∀ b b', hermForm Hm (zz' b') (zz b) = 0)) → ∀ (g : ℕ) (x : GlobalTheory.CxPts (genStr Z) σ) (exx : (Fin g → ℂ) → (Over.mk (x.1 ≫ genι Z) ⟶ Z.t.G)), Inner x → IsExpAt Z.t (x.1 ≫ genι Z) exx → IsHolTo Set.univ (fun w => (exx w).left) → ∀ (k : (unfFam U σ).Comp) (x' : ((unfFam U σ).X k).dom), IsOrth ((unfFam U σ).X k) x'.1 → cxPt Z ((unfFam U σ).un k x') = x → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ v w : Fin g → ℂ, exx v = 1 → exx w = 1 → ∃ m : ℤ, (hermForm Hm v w).im = m) → (∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → exx v = 1 → exx w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil Z.t.cub k (exx ((k : ℂ)⁻¹ • v)) (exx ((k : ℂ)⁻¹ • w)) (unitOn ζ)) → ∀ (f : EigFrame Z σ (x.1 ≫ genι Z)) (Wd : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Fin g → ℂ), Dirs ⟨x, f⟩ (fun w => (exx w).left) Wd → (∀ τ, (hodgeMet Z U).gram x f τ = (((2 * Real.pi / d k τ : ℝ)) : ℂ) • Matrix.of fun b b' => hermForm Hm (Wd ⟨τ, b'⟩) (Wd ⟨τ, b⟩)) ∧ ∀ p q : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), p.1 ≠ q.1 → hermForm Hm (Wd p) (Wd q) = 0 := by
  first | exact @GlobalTheory.HodgeInteriorGram.gram_eq_riem | exact GlobalTheory.HodgeInteriorGram.gram_eq_riem | (intros; apply GlobalTheory.HodgeInteriorGram.gram_eq_riem <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase

theorem exists_analytic_frame_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∃ (k' : U.Comp) (s : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q)), AnalyticAt ℂ s (c'.e y) ∧ ∀ᶠ w in 𝓝 (c'.e y), ∃ hs : s w ∈ (U.X k').dom, cxPt T.Z (U.un k' ⟨s w, hs⟩) = cxOf e σ hj (c'.e.symm w) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU X j hj hjo y hy c' hyc
  rcases Nat.eq_zero_or_pos (Dw.p + Dw.q) with hr | hr
  · obtain ⟨W⟩ := GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf _ _ _ _ _ _ _ _ U hU
    obtain ⟨i, B, P, hB, hb₀, -, hper, -, hq⟩ := GlobalTheory.T.algebraicChart_lift_holomorphic_periodMaps E H Dw l Xo c O β Y T F e σ W.g _ W.F X j hj hjo y hy c' hyc
    obtain ⟨q₀, hq₀, hu₀⟩ := hq _ hb₀
    have hne : ¬ LiesIn (cxOf e σ hj y) (genBd T.Z) := by
      rw [← c'.e.left_inv hyc, ← hq₀]; exact not_liesIn_cxPt q₀
    obtain ⟨k, x, -, hkx⟩ := GlobalTheory.HodgeSmooth.exists_orth (Z := T.Z) hσ hU hne
    have hg : IsEmpty (Fin W.g) := by
      refine ⟨fun a => ?_⟩
      have := (W.e a).2.2
      simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult] at this
      split_ifs at this <;> omega
    refine ⟨k, fun _ => x.1, analyticAt_const, Filter.mem_of_superset (hB.mem_nhds hb₀) fun w hw => ⟨x.2, ?_⟩⟩
    obtain ⟨q, hq1, hq2⟩ := hq w hw
    have hfib : W.F.u i (P (c'.e y)) = W.F.u i (P w) :=
      (W.F.fibre i _ _ (hper _ hb₀) (hper w hw)).2 ⟨LinearEquiv.refl _ _, LinearEquiv.refl _ _, fun _ _ => rfl,
        fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩, fun a => funext fun t => (hg.false t).elim⟩
    have e1 : cxPt T.Z q₀ = cxPt T.Z q := cxPt_congr (hu₀.symm.trans (hfib.trans hq2))
    rw [← hq1, ← e1, hq₀, c'.e.left_inv hyc]
    exact hkx
  · obtain ⟨W, hinj⟩ := GlobalTheory.HodgeSmooth.exists_unfWit_inj hσ hU hr
    obtain ⟨i, B, P, hB, hb₀, -, hper, hdiff, hq⟩ := GlobalTheory.T.algebraicChart_lift_holomorphic_periodMaps E H Dw l Xo c O β Y T F e σ W.g _ W.F X j hj hjo y hy c' hyc
    obtain ⟨q₀, -, hu₀⟩ := hq _ hb₀
    obtain ⟨k, x₁, t, hbor⟩ := hU.2.2.1 q₀
    have hk : W.ik k = i := W.F.disj _ _ _ _ (W.period k x₁) (hper _ hb₀)
      (((W.lie k x₁).1.symm.trans hbor.1.symm).trans hu₀.symm)
    subst hk
    obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
    obtain ⟨hp0, hty⟩ := hU.2.1 k
    have hmult : ∀ τ : E →+* ℂ, Formalism.L2.PjFree.relab c σ τ ∉ (U.X k).Ψ → Dw.mult τ = (U.X k).p0 := by
      intro τ hτ
      rw [hp0]
      exact if_neg fun h => hτ ((hty _).2 ((hrt τ).2 h))
    have hrep : ∀ b ∈ B, ∀ q : FrPt Xo c (Formalism.L2.Pj.CAt σ), W.F.u (W.ik k) (P b) = q.x →
        ∃ x' : (U.X k).dom, (U.un k x').x = q.x ∧ ∃ h : (Fin W.g → ℂ) ≃ₗ[ℂ] (Fin W.g → ℂ), ∀ v, P b v =
          h (fun j => Formalism.L2.PjFree.perFr (U.X k) x'.1 (W.φ k v : Fin (Dw.p + Dw.q) → E)
            (Formalism.L2.PjFree.relab c σ (W.e j).1) ((W.e j).2 : ℕ)) := by
      intro b hb q hqu
      obtain ⟨x', hx', h, hh⟩ := GlobalTheory.T.periodMap_member_eq_frame_periodMap_linear_change E H Dw l Xo c σ _ U W hσ hU hinj k (P b) (hper b hb) q hqu
      exact ⟨x', hx', h, fun v => (hh v).trans (congrArg h (funext fun j => W.Pm_eq k x' v j))⟩
    obtain ⟨s, hs, hev⟩ := GlobalTheory.T.exists_analytic_frame_family_of_holomorphic_periodMaps E (Dw.p + Dw.q) (U.X k) _ (W.φ k) W.g (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1)
      (fun j => ((W.e j).2 : ℕ)) X.dim B P (c'.e y) hB hb₀ (fun b hb => (hper b hb).1) hdiff
      (fun ρ hρ m hm => by
        obtain ⟨τ', hτ'⟩ := hbij.2 (conjEmb ρ)
        have hn : Formalism.L2.PjFree.relab c σ τ' ∉ (U.X k).Ψ := by
          rw [hτ']
          exact ((U.X k).cmType ρ).1 hρ
        have hm' : m < Dw.mult τ' := by rw [hmult τ' hn]; exact hm
        exact ⟨W.e.symm ⟨τ', ⟨m, hm'⟩⟩, by rw [Equiv.apply_symm_apply]; exact hτ', by rw [Equiv.apply_symm_apply]⟩)
      (fun j j' h1 h2 => by
        have h1' := hbij.1 h1
        exact W.e.injective (Sigma.ext h1' ((Fin.heq_ext_iff (by rw [h1'])).2 h2)))
      (fun j hj' => by
        exact lt_of_lt_of_eq (W.e j).2.2 (hmult _ hj'))
      (fun b hb => by
        obtain ⟨q, -, hqu⟩ := hq b hb
        obtain ⟨x', -, h, hh⟩ := hrep b hb q hqu
        exact ⟨x'.1, x'.2, h, hh⟩)
    refine ⟨k, s, hs, (hev.and (hB.mem_nhds hb₀)).mono fun w hw => ⟨hw.1.1, ?_⟩⟩
    obtain ⟨q, hq1, hqu⟩ := hq w hw.2
    obtain ⟨x', hx', h, hh⟩ := hrep w hw.2 q hqu
    obtain ⟨h1, h2⟩ := hw.1.2 x'.1 x'.2 ⟨h, hh⟩
    rw [← hq1]
    exact cxPt_congr ((GlobalTheory.TrueCx.PointWell.pt_eq_of_block hU hσ k ⟨s w, hw.1.1⟩ x' h1 h2).trans hx')

end GlobalTheory.LieBase
end
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarCells

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X]

theorem inCone_of_strict {m' n : ℕ} {σ : Fin m' → LinearMap.BilinForm ℤ X} (hσs : IsStrict bar φ σ)
    (hσl : φ.LinearOn σ) {β : Fin n → LinearMap.BilinForm ℤ X} (hβ : ∀ i, β i ∈ balForms bar X)
    (hβp : ∀ i y, 0 ≤ β i y y) {a : Fin n → ℝ} {b : Fin m' → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hlin : evalR φ (∑ i, a i • toReal (β i)) = ∑ i, a i * φ.evalZ (β i))
    (hrel : ∑ i, a i • toReal (β i) = ∑ j, b j • toReal (σ j)) :
    ∀ i, a i ≠ 0 → ∃ (k : ℕ) (d : Fin m' → ℕ), 0 < k ∧ k • β i = ∑ j, d j • σ j := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hσs
  have hsum : ∑ i, a i * (ℓ (β i) : ℝ) = ∑ j, b j * (ℓ (σ j) : ℝ) := by
    have := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) ℓ
      (β := Sum.elim β σ) (c := Sum.elim a (-b)) (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hrel,
          add_neg_cancel])
    rw [Fintype.sum_sum_type] at this
    simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at this
    linarith
  have hφ : ∑ i, a i * φ.evalZ (β i) = ∑ j, b j * φ.evalZ (σ j) := by
    rw [← hlin, hrel]; exact (linearOn_iff φ σ).1 hσl b hb
  have hterm : ∑ i, a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hsum, show ∑ i, a i * (N * φ.evalZ (β i)) = N * ∑ i, a i * φ.evalZ (β i) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, hφ, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun j _ => by rw [h1]; ring
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) := fun i _ =>
    mul_nonneg (ha i) (sub_nonneg.2 (h2 _ (hβ i) (hβp i)))
  intro i hi
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hterm i (Finset.mem_univ _)
  have he : (N : ℝ) * φ.evalZ (β i) = ℓ (β i) := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hi
    · linarith
  exact h3 _ (hβ i) (hβp i) he


omit [Module O X] [Module.Finite O X] in
theorem inRCone_of_nsmul {m : ℕ} {σ : Fin m → LinearMap.BilinForm ℤ X} {β : LinearMap.BilinForm ℤ X} {k : ℕ}
    {d : Fin m → ℕ} (hk : 0 < k) (h : k • β = ∑ j, d j • σ j) : InRCone σ β := by
  refine ⟨fun j => (d j : ℝ) / k, fun j => by positivity, LinearMap.ext₂ fun a b => ?_⟩
  have e := LinearMap.congr_fun₂ h a b
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul] at e
  have e' : (k : ℝ) * (β a b : ℝ) = ∑ j, (d j : ℝ) * (σ j a b : ℝ) := by exact_mod_cast e
  have hk' : (k : ℝ) ≠ 0 := by positivity
  simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [show (β a b : ℝ) = (∑ j, (d j : ℝ) * (σ j a b : ℝ)) / k by rw [← e']; field_simp, Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.PolFan.StarCells

namespace GlobalTheory.PolFan.StarCells

theorem isStarOf_of_cover (hcover : ∀ (X : Type) [AddCommGroup X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (v : LinearMap.BilinForm ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), (∀ i y z, γ i y z = γ i z y) → (∀ i y, 0 ≤ γ i y y) → v ≠ 0 → InRCone γ v → B ∈ rcone γ → ∃ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h ∧ 0 < h v ∧ B ∈ rcone (Fin.cons v fun j => γ (s j))) :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w ψ' : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → IsCell H.bar ψ' γ) → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → IsCell H.bar ψ' (Fin.cons β₀ fun j => γ (s j))) → IsStarOf H.bar q ψ w ψ' := by
  intro E _ _ _ H q ψ w ψ' hψ hw h1 h2
  refine ⟨h1, h2, ?_⟩
  intro X _ _ _ _ hX n γ' hγ'
  set B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ := ∑ j, (1 : ℝ) • toReal (γ' j) with hBdef
  have hB : B ∈ psdCone (bar := H.bar) (X := X) :=
    ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X n γ' _ hγ'.mem hγ'.nonneg fun _ => zero_le_one
  obtain ⟨S, -, hfin⟩ := (hψ X hX).finite
  obtain ⟨e, m, γ, c, hγ, -, hc, he⟩ := hfin B hB
  set δ : Fin m → LinearMap.BilinForm ℤ X := fun i => pull e.symm.toLinearMap (γ i) with hδdef
  have hδ : IsCell H.bar ψ δ := CarDim.isCell_pull_equiv hγ e.symm
  have hBδ : B = ∑ i, c i • toReal (δ i) := by
    refine LinearMap.ext₂ fun a b => ?_
    have := LinearMap.congr_fun₂ he (e.symm a) (e.symm b)
    simp only [pullR_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, toReal_apply, smul_eq_mul] at this
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul, hδdef, pull_apply,
      LinearEquiv.coe_coe]
    exact this
  have key : ∀ (k : ℕ) (σ : Fin k → LinearMap.BilinForm ℤ X), IsCell H.bar ψ' σ → B ∈ rcone σ →
      ∀ j, InRCone σ (γ' j) := by
    rintro k σ hσ ⟨t, ht, hBt⟩ j
    obtain ⟨kk, d, hk, hkd⟩ := inCone_of_strict hσ.strict hσ.linear hγ'.mem hγ'.nonneg (a := fun _ => 1) (b := t)
      (fun _ => zero_le_one) ht ((linearOn_iff ψ' γ').1 hγ'.linear _ fun _ => zero_le_one) hBt j one_ne_zero
    exact inRCone_of_nsmul hk hkd
  by_cases hc0 : ∃ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) ∧ InRCone δ β ∧ w.evalZ β = 1
  · obtain ⟨β₀, hβ₀, hβ₀p, hin, hw1⟩ := hc0
    have hne : β₀ ≠ 0 := by
      intro h0
      have := (hw X hX).2.1 β₀ hβ₀ hβ₀p hw1 2 0 (by simp [h0])
      omega
    obtain ⟨m', s, h, hfc, hpos, hBc⟩ :=
      hcover X m δ β₀ B (fun i => (hδ.mem i).1) hδ.nonneg hne hin ⟨c, hc, hBδ⟩
    exact Or.inr ⟨m, δ, β₀, m', s, h, hδ, hβ₀, hβ₀p, hw1, hin, hfc, hpos,
      key _ _ (h2 X hX m δ hδ β₀ hβ₀ hβ₀p hw1 hin m' s h hfc hpos) hBc⟩
  · push_neg at hc0
    have h0 : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone δ β → w.evalZ β = 0 := fun β hβ hp hi =>
      ((hw X hX).1 β hβ hp).resolve_right (hc0 β hβ hp hi)
    exact Or.inl ⟨m, δ, hδ, h0, key _ _ (h1 X hX m δ hδ h0) ⟨c, hc, hBδ⟩⟩

end GlobalTheory.PolFan.StarCells
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

theorem _root_.GlobalTheory.T.realCone_covered_by_star_at_point : ∀ (X : Type) [AddCommGroup X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (v : LinearMap.BilinForm ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), (∀ i y z, γ i y z = γ i z y) → (∀ i y, 0 ≤ γ i y y) → v ≠ 0 → InRCone γ v → B ∈ rcone γ → ∃ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h ∧ 0 < h v ∧ B ∈ rcone (Fin.cons v fun j => γ (s j)) := by
  first | exact @GlobalTheory.StarCover.star_cover | exact GlobalTheory.StarCover.star_cover | (intros; apply GlobalTheory.StarCover.star_cover <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.exists_primitiveBalancedForm_fracCoords_of_cellMult : ∀ {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) (M : ℕ) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {m : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell bar φ M δ → 2 ≤ M →
  ∃ (v : LinearMap.BilinForm ℤ X) (hv : v ∈ balForms bar X), IsPrim bar (⟨v, hv⟩ : balForms bar X) ∧ (∀ y, 0 ≤ v y y) ∧
    ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i ∧ t i < 1) ∧ toReal v = ∑ i, t i • toReal (δ i) := by
  first | exact @GlobalTheory.PolFan.CentreChoice.exists_isPrim_frac | exact GlobalTheory.PolFan.CentreChoice.exists_isPrim_frac | (intros; apply GlobalTheory.PolFan.CentreChoice.exists_isPrim_frac <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.simplicialLabelling_of_barycentricStage_zero : ∀ (O : Type) [CommRing O] (bar : O → O) (q : ℕ) (ψ lab φ : InvFun O), IsCarrierDim bar q ψ lab → IsBaryStage bar q ψ lab φ 0 → SimpLab bar q φ lab := by
  first | exact @GlobalTheory.PolFan.BaryFin.simpLab_of_isBaryStage_zero | exact GlobalTheory.PolFan.BaryFin.simpLab_of_isBaryStage_zero | (intros; apply GlobalTheory.PolFan.BaryFin.simpLab_of_isBaryStage_zero <;> assumption)
end
