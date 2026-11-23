module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle703
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentOfCutSec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle732
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle711
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle729
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle699
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle736
public import Formalism.DegreeFormula.Statement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityBoundedDomainInvariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.FlagBundle GlobalTheory.ShFam GlobalTheory.CxPts GlobalTheory.ProjVar

namespace GlobalTheory.LieBase

open scoped ComplexOrder
open Matrix GlobalTheory GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.GoodMetric GlobalTheory.ProjVar.Var GlobalTheory.TrueGeo.Res

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {σ : c.F →+* ℂ} {e : F ≃+* c.F} {X : Var F} {j : X.X ⟶ gen Z}
  {f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)} {S : Fr (ratOf X) Dw.mult 0} {A₀ : Mat Dw.mult X.Fn}

theorem spMap_evStalk_eq (y : CxPts X.str (σ.comp e.toRingHom)) : y.1 = spMap (evStalk y) ≫ stalkPt X (under y) :=
  (Scheme.Spec_stalkClosedPointTo_fromSpecStalk y.1).symm

theorem exists_frameAt (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (hT : Tied e X j f₀ S A₀)
    (y : CxPts X.str (σ.comp e.toRingHom)) {A : Mat Dw.mult X.Fn} (hA : A ∈ S.S (under y)) :
    ∃ g : EigFrame Z σ ((cxOf e σ hj y).1 ≫ genι Z), FrameAt e f₀ A₀ A y g := by
  obtain ⟨φ, fz, hc⟩ := hT.2 (under y) A hA
  have hφ : σ = (evStalk y).comp φ := RingHom.ext fun a => by
    have h3 : φ a = algebraMap F _ (e.symm a) := IsFractionRing.injective _ X.X.functionField
      ((RingHom.congr_fun hc.2.1 a).symm.trans ((X.stalkIncl (under y)).commutes _).symm)
    show σ a = evStalk y (φ a)
    rw [h3]
    refine Eq.trans ?_ ((evStalk_germ (U := ⊤) trivial _).trans (ev_algX mem_ptsIn_top _)).symm
    simp
  have hx : (cxOf e σ hj y).1 ≫ genι Z = spMap (evStalk y) ≫ stalkPt X (under y) ≫ j ≫ genι Z := by
    show (y.1 ≫ j) ≫ genι Z = _
    rw [spMap_evStalk_eq y]
    exact Category.assoc _ _ _
  obtain ⟨g, hg⟩ := fz.exists_isMap (evStalk y) hφ hx
  exact ⟨g, φ, fz, evStalk y, spMap_evStalk_eq y, hc, hg⟩

theorem map_ratVal_eq_co (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (hT : Tied e X j f₀ S A₀)
    {y : CxPts X.str (σ.comp e.toRingHom)} {A A' : Mat Dw.mult X.Fn} (hA' : A' ∈ S.S (under y)) {g g' : EigFrame Z σ ((cxOf e σ hj y).1 ≫ genι Z)} (hg : FrameAt e f₀ A₀ A y g)
    (hg' : FrameAt e f₀ A₀ A' y g') (τ : E →+* ℂ) : (A' * A⁻¹).map (ratVal · y) τ = (g.co g' τ)ᵀ := by
  obtain ⟨φ, fz, ψ, hψ, hc, hm⟩ := hg
  obtain ⟨φ', fz', ψ', hψ', hc', hm'⟩ := hg'
  obtain rfl : ψ = evStalk y :=
    EigLoc.spMap_inj ((cancel_mono (X.X.fromSpecStalk (under y))).1 (hψ.symm.trans (spMap_evStalk_eq y)))
  obtain rfl : ψ' = evStalk y :=
    EigLoc.spMap_inj ((cancel_mono (X.X.fromSpecStalk (under y))).1 (hψ'.symm.trans (spMap_evStalk_eq y)))
  obtain rfl : φ' = φ := RingHom.ext fun a => IsFractionRing.injective _ X.X.functionField
    ((RingHom.congr_fun hc'.2.1 a).symm.trans (RingHom.congr_fun hc.2.1 a))
  have hx : (cxOf e σ hj y).1 ≫ genι Z = spMap (evStalk y) ≫ stalkPt X (under y) ≫ j ≫ genι Z := by
    show (y.1 ≫ j) ≫ genι Z = _
    rw [spMap_evStalk_eq y]
    exact Category.assoc _ _ _
  obtain ⟨k, hk⟩ := fz.exists_isMap (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField) hc.2.1 hc.1
  obtain ⟨k', hk'⟩ := fz'.exists_isMap (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField) hc.2.1 hc.1
  have h1 : k.co f₀ τ = ((A₀ * A⁻¹) τ)ᵀ := EigFrame.co_eq fun i => by rw [funext (hk τ)]; exact hc.2.2 τ i
  have h2 : k'.co f₀ τ = ((A₀ * A'⁻¹) τ)ᵀ := EigFrame.co_eq fun i => by rw [funext (hk' τ)]; exact hc'.2.2 τ i
  have h3 : k.co k' τ = (fz.co fz' τ).map (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField) :=
    hk.co τ hk' hc.1
  have h4 := k.co_mul k' f₀ τ
  rw [h1, h2, h3] at h4
  set M := (fz.co fz' τ).map (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField) with hM
  have u0 : IsUnit (A₀ τ).det := isUnit_iff_ne_zero.2 (Fr.det_ne hT.1 τ)
  have u' : IsUnit (A' τ).det := isUnit_iff_ne_zero.2 (Fr.det_ne hA' τ)
  have h5 : A' τ * (A τ)⁻¹ = Mᵀ := by
    have h6 := congrArg Matrix.transpose h4
    rw [transpose_mul, transpose_transpose, transpose_transpose] at h6
    change A₀ τ * (A' τ)⁻¹ * Mᵀ = A₀ τ * (A τ)⁻¹ at h6
    have h7 : A' τ * (A₀ τ)⁻¹ * (A₀ τ * (A' τ)⁻¹) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (A₀ τ)⁻¹, Matrix.nonsing_inv_mul _ u0, Matrix.one_mul,
        Matrix.mul_nonsing_inv _ u']
    calc A' τ * (A τ)⁻¹ = A' τ * (A₀ τ)⁻¹ * (A₀ τ * (A τ)⁻¹) := by
          rw [Matrix.mul_assoc, ← Matrix.mul_assoc (A₀ τ)⁻¹, Matrix.nonsing_inv_mul _ u0, Matrix.one_mul]
      _ = Mᵀ := by rw [← h6, ← Matrix.mul_assoc, h7, Matrix.one_mul]
  rw [hm.co τ hm' hx]
  change ((A' τ * (A τ)⁻¹)).map (ratVal · y) = _
  rw [h5]
  ext a b
  simp only [map_apply, transpose_apply, hM]
  rw [ratVal_eq_valAt y ⟨_, rfl⟩, valAt_algebraMap]
  rfl

theorem isMetricOn_gramOf (G : EigMet Z σ) (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (hT : Tied e X j f₀ S A₀)
    (Ω : X.X.Opens) (hs : ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) Ω, ∀ A ∈ S.S (under y), ∀ (τ : E →+* ℂ)
      (a b : Fin (Dw.mult τ)), CInfAt (fun z => (gramOf e G hj f₀ A₀ A z τ a b).re) y ∧
        CInfAt (fun z => (gramOf e G hj f₀ A₀ A z τ a b).im) y) :
    IsMetricOn S Ω (gramOf e G hj f₀ A₀) := by
  refine ⟨fun y _ A hA τ => ?_, fun y hy A hA τ a b => hs y hy A hA τ a b, fun y _ A hA A' hA' τ => ?_⟩
  · have h := exists_frameAt hj hT y hA
    rw [gramOf, dite_eq_left h]
    exact (G.pos _ _ τ).transpose
  · have h := exists_frameAt hj hT y hA
    have h' := exists_frameAt hj hT y hA'
    unfold gramOf
    rw [dite_eq_left h, dite_eq_left h']
    rw [G.change _ h.choose h'.choose τ, map_ratVal_eq_co hj hT hA' h.choose_spec h'.choose_spec τ]
    rw [transpose_mul, transpose_mul, Matrix.mul_assoc]
    congr 2

end GlobalTheory.LieBase

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.CxPts GlobalTheory.Cartier

theorem GlobalTheory.LieBase.isMetricOn_lieGram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (C : FlagCpt T.Z e), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : C.Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e C X j f f₀ Eb A₀ → IsMetricOn Eb (openPart j) (lieGram e U hj f₀ A₀) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU C X j f f₀ Eb A₀ hj hL
  have := T.smooth
  obtain ⟨hoi, -, hT⟩ := hL
  rw [lieGram_eq_gramOf]
  exact isMetricOn_gramOf (hodgeMet T.Z U) hj hT _
    (GlobalTheory.T.eigenMetricGram_smooth_in_familyFrames E H Dw l Xo c O β T.Z σ _ (GlobalTheory.T.hodgeMetric_uniformisation_smoothOn_interior E H Dw l Xo c O β T.Z σ U hσ hU) F e X j f₀ Eb A₀ hj hoi hT)
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.carries_exists_marked_form_in_cone : ∀ {O : Type} [CommRing O] (bar : O → O) (w0 : O) (c : FormFamily O) {X₀ : Type} [AddCommGroup X₀] [Module O X₀] [Module.Finite O X₀] {m : ℕ} (δ₀ : Fin m → LinearMap.BilinForm ℤ X₀) (v : LinearMap.BilinForm ℤ X₀) (t : Fin m → ℝ),
  v ∈ balForms bar X₀ → v ≠ 0 → (∀ y, 0 ≤ v y y) → c.Carries δ₀ → (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ X), c.Carries δ →
    ∃ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) ∧ (OrbMark.orbFun O w0 v).evalZ β = 1 ∧ InRCone δ β := by
  first | exact @GlobalTheory.PolFan.carries_exists_marked | exact GlobalTheory.PolFan.carries_exists_marked | (intros; apply GlobalTheory.PolFan.carries_exists_marked <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.exists_semilinear_pullback_of_markedOrbitIndicator : ∀ {O : Type} [CommRing O] (w0 : O) {X₀ : Type} [AddCommGroup X₀] [Module O X₀] (v : LinearMap.BilinForm ℤ X₀)
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X), (OrbMark.orbFun O w0 v).evalZ β = 1 →
  ∃ (τ : O ≃+* O) (f : X →+ X₀ ⧸ (CarDim.orad v : Submodule O X₀)), τ w0 = w0 ∧ Function.Surjective f ∧
    (∀ (a : O) (x : X), f (a • x) = τ a • f x) ∧
    ∀ (x y : X) (x₀ y₀ : X₀), Submodule.Quotient.mk x₀ = f x → Submodule.Quotient.mk y₀ = f y → β x y = v x₀ y₀ := by
  first | exact @GlobalTheory.PolFan.OrbMark.exists_semilinear_pull_of_evalZ_eq_one | exact GlobalTheory.PolFan.OrbMark.exists_semilinear_pull_of_evalZ_eq_one | (intros; apply GlobalTheory.PolFan.OrbMark.exists_semilinear_pull_of_evalZ_eq_one <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.exists_finite_rational_polyhedral_cells_upto_aut : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g q : ℕ) (φs : InvFun ℤ) (𝓜 : Finset ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], IsPolFan (id : ℤ → ℤ) g φs → Module.finrank ℚ E * q ≤ g → Module.finrank (𝓞 E) X ≤ q → HasRedCover H.bar X → ∃ S : Set (LinearMap.BilinForm ℤ X), S.Finite ∧ ∀ B ∈ psdCone (bar := H.bar) (X := X), ∃ (e : X ≃ₗ[𝓞 E] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell H.bar (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) γ ∧ (∀ i, γ i ∈ S) ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i) := by
  first | exact @GlobalTheory.PolCell.exists_cells | exact GlobalTheory.PolCell.exists_cells | (intros; apply GlobalTheory.PolCell.exists_cells <;> assumption)
end

section

open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped Matrix

theorem _root_.GlobalTheory.T.chern_density_frame_indep_chart_jacobian_factor : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} [Finite ι] {m : ι → ℕ} (E : Fr (ratOf X) m 0) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricOn E O H → ∀ (R : MvPolynomial (ι × ℕ) ℝ) {y : CxPts X.str σ}, y ∈ ptsIn X.str σ O → ∀ (c c' : AlgChart X.str σ X.dim), y ∈ c.e.source → y ∈ c'.e.source → ∀ {A A' : Mat m X.Fn}, A ∈ E.S (under y) → A' ∈ E.S (under y) → chernTop R (fun v => H A (c.e.symm v)) (c.e y) = ‖transDet c.e c'.e y‖ ^ 2 * chernTop R (fun v => H A' (c'.e.symm v)) (c'.e y) := by
  first | exact @GlobalTheory.GoodMetric.chernTop_frame_chart_trans | exact GlobalTheory.GoodMetric.chernTop_frame_chart_trans | (intros; apply GlobalTheory.GoodMetric.chernTop_frame_chart_trans <;> assumption)
end

section

open Formalism.DegreeFormula


theorem _root_.GlobalTheory.T.chernPolyTopDensity_bounded_domain_invariant : ∀ (ι : Type) [Fintype ι] (p q n : ℕ) (h : Fintype.card (ι × Fin p × Fin q) = n) (v : ReciprocityTheory.L2DbarEstimates.V n), GlobalTheory.UnifDens.flatL h v ∈ Formalism.DegreeFormula.DomFlat ι p q → GlobalTheory.GoodMetric.chernTop (m := fun _ : ι => p) (∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ q) (fun u τ => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) v = GlobalTheory.GoodMetric.chernTop (m := fun _ : ι => p) (∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ q) (fun u τ => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) 0 * ∏ i, ((Formalism.DegreeFormula.hQ (Formalism.DegreeFormula.unflat (GlobalTheory.UnifDens.flatL h v) i)).det.re) ^ (-((p + q : ℕ) : ℤ)) := by
  first | exact @GlobalTheory.DomDensInv.chernTop_model_moeb | exact GlobalTheory.DomDensInv.chernTop_model_moeb | (intros; apply GlobalTheory.DomDensInv.chernTop_model_moeb <;> assumption)
end
