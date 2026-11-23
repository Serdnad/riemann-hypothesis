module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle206
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricGramHolomorphicFrameForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle668
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle630
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle729
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle716
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle626
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle718
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle047
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle721
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle720
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle724
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicEigenFrameDirsInExpChart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle699
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle685
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle725
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532

@[expose] public section

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix


theorem _root_.GlobalTheory.T.hodgeMetric_gram_holomorphic_frame_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ k' : U.Comp, ∃ (G : ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q) → Mat Dw.mult ℂ) (z : ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q) → GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.q) ℂ) (cc : (E →+* ℂ) → ℝ), (∀ τ, 0 < cc τ) ∧ ∀ (x : ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q)) (hx : x ∈ (U.X k').dom), (∀ τ a b, AnalyticAt ℂ (fun x' => G x' τ a b) x) ∧ (∀ τ a b, AnalyticAt ℂ (fun x' => z x' τ a b) x) ∧ (∀ τ, IsUnit (G x τ).det) ∧ InDom (z x) ∧ ∀ τ, ((hodgeMet Z U).gram (cxPt Z (U.un k' ⟨x, hx⟩)) (cxFrame Z (U.un k' ⟨x, hx⟩)) τ)ᵀ = (cc τ : ℂ) • (G x τ * modelGram H Dw (z x) τ * (G x τ)ᴴ) := by
  first | exact @GlobalTheory.HodgeGramGen.hodge_gram_frame | exact GlobalTheory.HodgeGramGen.hodge_gram_frame | (intros; apply GlobalTheory.HodgeGramGen.hodge_gram_frame <;> assumption)
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

namespace OrbMark

theorem eval_pull_semilinear_of_isTwInv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)),
    IsTwInv H φ →
    ∀ {X Y : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [AddCommGroup Y] [Module (𝓞 E) Y]
      [Module.Finite (𝓞 E) Y] (τ : 𝓞 E ≃+* 𝓞 E), τ H.w0 = H.w0 → ∀ (f : X →+ Y), Function.Surjective f →
      (∀ (a : 𝓞 E) (x : X), f (a • x) = τ a • f x) →
      ∀ B : Y → Y → ℝ, φ.eval X (fun x y => B (f x) (f y)) = φ.eval Y B := by
  intro E _ _ _ H φ htw X Y _ _ _ _ _ _ τ hτ f hf hsm B
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' (𝓞 E) X
  let r₁ : (Fin n → 𝓞 E) →ₗ[𝓞 E] Y :=
    { toFun := fun a => f (r (twv τ.symm a))
      map_add' := fun a b => by
        have e : twv τ.symm (a + b) = twv τ.symm a + twv τ.symm b := funext fun _ => map_add τ.symm _ _
        rw [e, map_add (f := _), map_add (f := _)]
      map_smul' := fun c a => by
        rw [twv_smul, map_smul, hsm, RingEquiv.apply_symm_apply]
        rfl }
  have hr₁ : ∀ a, r₁ (twv τ a) = f (r a) := fun a => by
    show f (r (twv τ.symm (twv τ a))) = f (r a)
    rw [twv_symm_twv]
  have hs₁ : Function.Surjective r₁ := fun y => by
    obtain ⟨x, rfl⟩ := hf y
    obtain ⟨a, rfl⟩ := hr x
    exact ⟨twv τ a, hr₁ a⟩
  rw [φ.eval_eq hr, φ.eval_eq hs₁]
  have h := htw τ hτ n fun a b => B (r₁ a) (r₁ b)
  have e : (fun a b : Fin n → 𝓞 E => B (f (r a)) (f (r b))) = fun a b => B (r₁ (fun i => τ (a i))) (r₁ (fun i => τ (b i))) := by
    funext a b
    exact congrArg₂ B (hr₁ a).symm (hr₁ b).symm
  rw [e]
  exact h

end OrbMark

end GlobalTheory.PolFan
end
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory.PolFan.Mark

section Transport

variable {O : Type} [CommRing O] {bar : O → O} {ψ lab : InvFun O} {i : ℕ}
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
  {T : X ≃ X} {e : LinearMap.BilinForm ℤ X ≃+ LinearMap.BilinForm ℤ X}
  (he : ∀ β y z, e β y z = β (T y) (T z))
  (hbal : ∀ β, e β ∈ balForms bar X ↔ β ∈ balForms bar X)
  (hψ : ∀ β, ψ.evalZ (e β) = ψ.evalZ β) (hlab : ∀ β, lab.evalZ (e β) = lab.evalZ β)
include he hbal hψ hlab

theorem inFace_transport (β x : LinearMap.BilinForm ℤ X) :
    InFace bar ψ lab (e β) (e x) ↔ InFace bar ψ lab β x := by
  unfold InFace
  simp only [he]
  rw [hbal, ← map_add (f := _), hψ, hψ, hψ, hlab, hlab]
  refine and_congr Iff.rfl (and_congr ?_ (and_congr ?_ Iff.rfl))
  · exact ⟨fun h y => by simpa using h (T.symm y), fun h y => h (T y)⟩
  · exact ⟨fun h y => by simpa using h (T.symm y), fun h y => h (T y)⟩

theorem isIndec_transport (β x : LinearMap.BilinForm ℤ X) :
    IsIndec bar ψ lab (e β) (e x) ↔ IsIndec bar ψ lab β x := by
  unfold IsIndec
  rw [inFace_transport he hbal hψ hlab, e.map_ne_zero_iff]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h y z hy hz hy0 hz0 hs => ?_, fun h y z hy hz hy0 hz0 hs => ?_⟩)
  · refine h (e y) (e z) ((inFace_transport he hbal hψ hlab β y).2 hy) ((inFace_transport he hbal hψ hlab β z).2 hz)
      (e.map_ne_zero_iff.2 hy0) (e.map_ne_zero_iff.2 hz0) ?_
    rw [← map_add (f := _), hs]
  · refine h (e.symm y) (e.symm z) ?_ ?_ ?_ ?_ ?_
    · rw [← inFace_transport he hbal hψ hlab, e.apply_symm_apply]; exact hy
    · rw [← inFace_transport he hbal hψ hlab, e.apply_symm_apply]; exact hz
    · exact fun h0 => hy0 (by rw [← e.apply_symm_apply y, h0, map_zero])
    · exact fun h0 => hz0 (by rw [← e.apply_symm_apply z, h0, map_zero])
    · apply e.injective; rw [map_add (f := _), e.apply_symm_apply, e.apply_symm_apply, hs]

theorem isMarked_transport_of (β : LinearMap.BilinForm ℤ X) (h : IsMarked bar ψ lab i X β) :
    IsMarked bar ψ lab i X (e β) := by
  obtain ⟨hb, hn, hp, hl, S, hS, k, hk, hsum⟩ := h
  refine ⟨(hbal β).2 hb, fun y => by rw [he]; exact hn _, fun k' β' h' => hp k' (e.symm β') ?_, by rw [hlab]; exact hl,
    S.map e.toEquiv.toEmbedding, fun x => ?_, k, hk, ?_⟩
  · apply e.injective; rw [map_zsmul, e.apply_symm_apply, h']
  · rw [Finset.mem_map_equiv, hS, ← isIndec_transport he hbal hψ hlab]
    show IsIndec bar ψ lab (e β) (e (e.symm x)) ↔ _
    rw [e.apply_symm_apply]

  · rw [Finset.sum_map, ← map_zsmul, hsum, map_sum]; rfl

theorem isMarked_transport (β : LinearMap.BilinForm ℤ X) :
    IsMarked bar ψ lab i X (e β) ↔ IsMarked bar ψ lab i X β := by
  refine ⟨fun h => ?_, isMarked_transport_of he hbal hψ hlab β⟩
  have := isMarked_transport_of (T := T.symm) (e := e.symm) (fun β y z => ?_) (fun β => ?_) (fun β => ?_)
    (fun β => ?_) (e β) h
  · simpa using this
  · have := he (e.symm β) (T.symm y) (T.symm z); simp only [AddEquiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    exact this.symm
  · rw [← hbal, e.apply_symm_apply]
  · rw [← hψ, e.apply_symm_apply]
  · rw [← hlab, e.apply_symm_apply]

end Transport

section Twist

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def twPi (σ : 𝓞 E ≃+* 𝓞 E) (n : ℕ) : (Fin n → 𝓞 E) ≃+ (Fin n → 𝓞 E) :=
  AddEquiv.piCongrRight fun _ => σ.toAddEquiv

def twForm (σ : 𝓞 E ≃+* 𝓞 E) (n : ℕ) :
    LinearMap.BilinForm ℤ (Fin n → 𝓞 E) ≃+ LinearMap.BilinForm ℤ (Fin n → 𝓞 E) where
  toFun β := β.compl₁₂ (twPi σ n).toIntLinearEquiv.toLinearMap (twPi σ n).toIntLinearEquiv.toLinearMap
  invFun β := β.compl₁₂ (twPi σ.symm n).toIntLinearEquiv.toLinearMap (twPi σ.symm n).toIntLinearEquiv.toLinearMap
  left_inv β := LinearMap.ext₂ fun a b => by
    change β (fun j => σ (σ.symm (a j))) (fun j => σ (σ.symm (b j))) = β a b
    simp only [RingEquiv.apply_symm_apply]
  right_inv β := LinearMap.ext₂ fun a b => by
    change β (fun j => σ.symm (σ (a j))) (fun j => σ.symm (σ (b j))) = β a b
    simp only [RingEquiv.symm_apply_apply]
  map_add' _ _ := LinearMap.ext₂ fun a b => by simp

@[simp] theorem twForm_apply (σ : 𝓞 E ≃+* 𝓞 E) (n : ℕ) (β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E)) (a b : Fin n → 𝓞 E) :
    twForm σ n β a b = β (fun j => σ (a j)) (fun j => σ (b j)) := rfl

end Twist

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem twForm_mem_balForms (H : Host E) (σ : 𝓞 E ≃+* 𝓞 E) {n : ℕ} {β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E)}
    (h : β ∈ balForms H.bar (Fin n → 𝓞 E)) : twForm σ n β ∈ balForms H.bar (Fin n → 𝓞 E) := by
  refine ⟨fun y z => by simp only [twForm_apply]; exact h.1 _ _, fun a y z => ?_⟩
  simp only [twForm_apply]
  have e1 : (fun j => σ ((a • y) j)) = σ a • fun j => σ (y j) := funext fun j => by simp
  have e2 : (fun j => σ ((H.bar a • z) j)) = H.bar (σ a) • fun j => σ (z j) := funext fun j => by
    simp [host_bar_map_comm]
  rw [e1, e2]
  exact h.2 _ _ _

theorem twForm_symm_twForm (σ : 𝓞 E ≃+* 𝓞 E) {n : ℕ} (β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E)) :
    twForm σ.symm n (twForm σ n β) = β := LinearMap.ext₂ fun a b => by simp

theorem twForm_mem_balForms_iff (H : Host E) (σ : 𝓞 E ≃+* 𝓞 E) {n : ℕ} (β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E)) :
    twForm σ n β ∈ balForms H.bar (Fin n → 𝓞 E) ↔ β ∈ balForms H.bar (Fin n → 𝓞 E) :=
  ⟨fun h => by simpa [twForm_symm_twForm] using twForm_mem_balForms H σ.symm h, twForm_mem_balForms H σ⟩

theorem evalZ_twForm {H : Host E} {φ : InvFun (𝓞 E)} (hφ : IsTwInv H φ) {σ : 𝓞 E ≃+* 𝓞 E} (hσ : σ H.w0 = H.w0)
    {n : ℕ} (β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E)) : φ.evalZ (twForm σ n β) = φ.evalZ β := by
  unfold InvFun.evalZ
  rw [InvFun.eval_pi, InvFun.eval_pi]
  exact hφ σ hσ n fun a b => (β a b : ℝ)

theorem markVal_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ lab : InvFun (𝓞 E))
    (i : ℕ), IsTwInv H ψ → IsTwInv H lab → ∀ σ : 𝓞 E ≃+* 𝓞 E, σ H.w0 = H.w0 →
    ∀ (n : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ),
      markVal H.bar ψ lab i n (fun a b => B (fun j => σ (a j)) (fun j => σ (b j))) = markVal H.bar ψ lab i n B := by
  intro E _ _ _ H ψ lab i hψ hlab σ hσ n B
  classical
  unfold markVal
  by_cases h2 : ∃ β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E), ∀ a b, B a b = β a b
  · have h1 : ∃ β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E), ∀ a b, B (fun j => σ (a j)) (fun j => σ (b j)) = β a b :=
      ⟨twForm σ n h2.choose, fun a b => h2.choose_spec _ _⟩
    rw [dite_eq_left h1, dite_eq_left h2]
    have e : h1.choose = twForm σ n h2.choose := LinearMap.ext₂ fun a b => by
      have := (h1.choose_spec a b).symm.trans (h2.choose_spec _ _)
      exact_mod_cast this
    rw [e, isMarked_transport (T := (twPi σ n).toEquiv) (fun _ _ _ => rfl) (twForm_mem_balForms_iff H σ)
      (evalZ_twForm hψ hσ) (evalZ_twForm hlab hσ)]
  · have h1 : ¬ ∃ β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E), ∀ a b,
        B (fun j => σ (a j)) (fun j => σ (b j)) = β a b := fun ⟨β, hβ⟩ =>
      h2 ⟨twForm σ.symm n β, fun a b => by
        have := hβ (fun j => σ.symm (a j)) (fun j => σ.symm (b j))
        simpa using this⟩
    rw [dite_eq_right h1, dite_eq_right h2]

end Main

end GlobalTheory.PolFan.Mark
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

namespace GlobalTheory.LieBase.HoloFrame

theorem exists_un : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.IsUnf U → ∀ (y : CxPts (genStr T.Z) σ), ¬ LiesIn y (genBd T.Z) → ∃ (k : U.Comp) (x : (U.X k).dom), cxPt T.Z (U.un k x) = y := by
  intro E _ _ _ H Dw l Xo c O _ β Y T σ r U hU y hy
  have hr : Set.range y.1 ⊆ Set.range T.Z.jQ := by
    rintro _ ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst hp
    exact not_not.1 hy
  haveI := T.Z.jQ_open
  let xF := IsOpenImmersion.lift T.Z.jQ y.1 hr
  have hxF : xF ≫ T.Z.jQ = y.1 := IsOpenImmersion.lift_fac _ _ _
  have hs : xF ≫ Limits.pullback.snd _ _ = spMap (algebraMap c.F (CAt σ)) := by
    have h2 := y.2
    rw [← hxF, Category.assoc, T.Z.jQ_over] at h2
    exact h2
  have hover : (xF ≫ Limits.pullback.fst _ _) ≫ Xo.s = sOf c (CAt σ) := by
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hs]
    exact GlobalTheory.ShFam.OpenReg.spMap_comp _ _
  haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  obtain ⟨z, hz⟩ : ∃ z : FrPt Xo c (CAt σ), z.x = xF ≫ Limits.pullback.fst _ _ :=
    GlobalTheory.FlagTan.exists_frPt _ hover
  obtain ⟨k, f, t, hb⟩ := hU.2.2.1 z
  refine ⟨k, f, ?_⟩
  rw [cxPt_congr hb.1.symm]
  refine Subtype.ext ?_
  show GlobalTheory.AllWt.ptF (S := CAt σ) z ≫ T.Z.jQ = y.1
  rw [← hxF]
  congr 1
  apply Limits.pullback.hom_ext
  · exact (ptF_fst z).trans hz
  · exact (ptF_snd z).trans hs.symm

theorem exists_holo_frame_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z), IsOpenImmersion j → ∀ (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∃ (k : U.Comp) (Fr : V X.dim → Frame (U.X k).Ψ (Dw.p + Dw.q)), ∀ᶠ u in 𝓝 (c'.e y), ∃ h : Fr u ∈ (U.X k).dom, cxPt T.Z (U.un k ⟨Fr u, h⟩) = cxOf e σ hj (c'.e.symm u) ∧ ∀ τ' a b, DifferentiableAt ℂ (fun u => mat (Fr u) τ' a b) u := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU X j hjo hj y hy c' hyc
  have hnb : ¬ LiesIn (cxOf e σ hj y) (genBd T.Z) := by
    intro h
    have h1 : IsLocalRing.closedPoint ℂ ∈ y.1 ⁻¹ᵁ openPart j := hy (Set.mem_univ _)
    exact h1 h
  obtain ⟨k, x₀, hx₀⟩ := exists_un E H Dw l Xo c O β Y T σ _ U hU _ hnb
  have hn := GlobalTheory.T.dim_openly_immersed_variety_eq_cmType_card_mul_pq E H Dw l Xo c O β Y T F e σ U hσ hU X j hjo hj ⟨y, hy⟩ k
  obtain ⟨W, a, ψ, hWo, haW, hψd, hψh, hψa, hinj⟩ := GlobalTheory.T.exists_holomorphic_frame_slice_componentUniformisation E H Dw l Xo c σ U hσ hU k x₀ X.dim hn
  obtain ⟨q, hOo, hq, hqd⟩ := GlobalTheory.T.holomorphic_frameFamily_chart_coordinates_holomorphic E H Dw l Xo c O β Y T F e σ U hσ hU X j hjo hj c' k X.dim W ψ hWo hψd hψh
  haveI := T.Z.jQ_open
  have hxeq : ∀ {z z' : FrPt Xo c (CAt σ)}, cxPt T.Z z = cxPt T.Z z' → z.x = z'.x := by
    intro z z' h
    have h1 : GlobalTheory.AllWt.ptF (S := CAt σ) z = GlobalTheory.AllWt.ptF (S := CAt σ) z' :=
      (cancel_mono T.Z.jQ).1 (congrArg Subtype.val h)
    rw [← ptF_fst z, h1, ptF_fst]
  have hcxinj : Function.Injective (cxOf e σ hj) := by
    intro y1 y2 h
    apply Subtype.ext
    exact (cancel_mono j).1 (congrArg Subtype.val h)
  have hya : cxOf e σ hj y = cxPt T.Z (U.un k ⟨ψ a, hψd a haW⟩) := hx₀.symm.trans (cxPt_congr (hψa _).symm)
  have haO : a ∈ {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} := ⟨haW, hψd a haW, y, hyc, hya⟩
  have hqa : q a = y := hcxinj ((hq a haW _ ⟨y, hyc, hya⟩).2.trans hya.symm)
  have hinjg : Set.InjOn (fun w => c'.e (q w)) {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} := by
    rintro w ⟨hw, hwd, hw'⟩ w' ⟨hw2, hwd', hw2'⟩ hg
    have h1 := hq w hw hwd hw'
    have h2 := hq w' hw2 hwd' hw2'
    have hqq : q w = q w' := c'.e.injOn h1.1 h2.1 hg
    refine hinj w hw w' hw2 hwd hwd' (hxeq ?_)
    rw [← h1.2, ← h2.2, hqq]
  obtain ⟨h, hev⟩ := GlobalTheory.T.exists_holomorphic_local_inverse_of_injOn X.dim _ _ a hOo haO hqd hinjg
  refine ⟨k, fun u => ψ (h u), ?_⟩
  rw [show c'.e y = c'.e (q a) by rw [hqa]]
  filter_upwards [hev] with u ⟨⟨huW, hud, hux⟩, hgu, hdu⟩
  refine ⟨hψd _ huW, ?_, fun τ' i i' => ?_⟩
  · have h1 := hq _ huW (hψd _ huW) hux
    rw [← h1.2]
    congr 1
    exact (c'.e.left_inv h1.1).symm.trans (congrArg c'.e.symm hgu)
  · exact ((hψh τ' i i' _ huW).differentiableAt (hWo.mem_nhds huW)).comp u hdu

end GlobalTheory.LieBase.HoloFrame
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
noncomputable section

namespace GlobalTheory.HodgeChart

theorem hodgeMet_eq_riem_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (n a : ℕ) (ha : a ≤ n) (g : ℕ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g), IsExpChart ch₀ ex → Fintype.card ((Σ τ : E →+* ℂ, Fin (Dw.mult τ))) = g → (∀ x ∈ ch₀.source, Inner x ↔ ∀ i : Fin a, ch₀ x (Fin.castLE ha i) ≠ 0) → ∃ κ : (E →+* ℂ) → ℝ, (∀ τ, 0 < κ τ) ∧ ∀ x ∈ ch₀.source, Inner x → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, ((Hm).IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm (Hm) u u).re) ∧ (∀ v w : Fin g → ℂ, ex x v = 1 → ex x w = 1 → ∃ m : ℤ, (hermForm (Hm) v w).im = m) ∧ ∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → ex x v = 1 → ex x w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm (Hm) v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil T.Z.t.cub k (ex x ((k : ℂ)⁻¹ • v)) (ex x ((k : ℂ)⁻¹ • w)) (unitOn ζ)) → ∀ (f : EigFrame T.Z σ (x.1 ≫ genι T.Z)) (W : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Fin g → ℂ), Dirs ⟨x, f⟩ (fun w => (ex x w).left) W → (∀ τ, (hodgeMet T.Z U).gram x f τ = ((κ τ : ℝ) : ℂ) • Matrix.of fun b b' => hermForm Hm (W ⟨τ, b'⟩) (W ⟨τ, b⟩)) ∧ ∀ p q : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), p.1 ≠ q.1 → hermForm Hm (W p) (W q) = 0 := by
  intro E _ _ _ H Dw l Xo c O _ β Y T σ U hσ hU n a ha g ch₀ ex hEC _ hIn
  classical
  obtain ⟨htarget, -, hsymmHol, hadd, hjoint, htan⟩ := hEC
  have hsrc : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ch₀.symm z ∈ ch₀.source := fun z hz =>
    ch₀.map_target (by rw [htarget]; exact hz)
  set Ω : Set (Fin n → ℂ) := {z | z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0} with hΩ
  have hinΩ : ∀ x ∈ ch₀.source, Inner x → ch₀ x ∈ Ω := fun x hx hI =>
    ⟨by rw [← htarget]; exact ch₀.map_source hx, (hIn x hx).1 hI⟩
  have hΩin : ∀ z ∈ Ω, Inner (ch₀.symm z) := fun z hz =>
    (hIn _ (hsrc z hz.1)).2 (by rw [ch₀.right_inv (by rw [htarget]; exact hz.1)]; exact hz.2)
  by_cases h1 : 1 ≤ Dw.p + Dw.q
  swap
  · have hm : ∀ τ : E →+* ℂ, Dw.mult τ = 0 := fun τ => by unfold Datum.mult; split_ifs <;> omega
    refine ⟨fun _ => 1, fun _ => one_pos, fun x _ _ Hm _ f Wd _ => ⟨fun τ => ?_, fun p q _ => ?_⟩⟩
    · ext i
      have h0 := hm τ
      have h2 := i.2
      omega
    · have h0 := hm p.1
      have h2 := p.2.2
      omega
  set U' := unfFam U σ with hU'def
  have hU' : Formalism.L2.PjFree.IsUnf U' := by rw [hU'def, unfFam_self]; exact hU
  obtain ⟨W, hinj⟩ := exists_unfWit_inj hσ hU' h1
  obtain ⟨d, hdpos, hd⟩ := GlobalTheory.T.exists_diagonal_riemannForm_orthonormalFrame E H Dw l Xo c σ _ U' hσ hU' W
  have hreach : ∀ z ∈ Ω, ∃ (k : U'.Comp) (x : (U'.X k).dom), IsOrth (U'.X k) x.1 ∧
      cxPt T.Z (U'.un k x) = ch₀.symm z :=
    fun z hz => exists_orth (Z := T.Z) hσ hU' (hΩin z hz)
  by_cases hne : Ω.Nonempty
  swap
  · exact ⟨fun _ => 1, fun _ => one_pos, fun x hx hI => absurd ⟨ch₀ x, hinΩ x hx hI⟩ hne⟩
  obtain ⟨z₁, hz₁⟩ := hne
  have hreach' : ∀ z, ∃ k : U'.Comp, z ∈ Ω → ∃ x : (U'.X k).dom, IsOrth (U'.X k) x.1 ∧
      cxPt T.Z (U'.un k x) = ch₀.symm z := fun z => by
    by_cases h : z ∈ Ω
    · obtain ⟨k, x, hx⟩ := hreach z h
      exact ⟨k, fun _ => ⟨x, hx⟩⟩
    · exact ⟨(hreach z₁ hz₁).choose, fun h' => absurd h' h⟩
  choose comp hcomp using hreach'
  letI : TopologicalSpace U'.Comp := ⊥
  haveI : DiscreteTopology U'.Comp := ⟨rfl⟩
  have hcont : ContinuousOn comp Ω := by
    intro z hz
    obtain ⟨x₀, -, hx₀⟩ := hcomp z hz
    have hs0 : cxPt T.Z (U'.un (comp z) x₀) ∈ ch₀.source := by rw [hx₀]; exact hsrc z hz.1
    obtain ⟨B, hBo, hzB, hB⟩ := GlobalTheory.T.orthonormalFrames_same_component_near_chart E H Dw l Xo c O β T.Z σ _ U' hσ hU' h1 n ch₀ hsymmHol (comp z) x₀ hs0
    rw [hx₀, ch₀.right_inv (by rw [htarget]; exact hz.1)] at hzB
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hBo.mem_nhds hzB)] with w hw hwB
    obtain ⟨x, -, hx⟩ := hcomp w hw
    exact hB w hwB _ x hx
  have hconst : ∀ z ∈ Ω, comp z = comp z₁ := fun z hz =>
    (GlobalTheory.T.isPreconnected_ball_inter_coords_ne_zero n a ha).constant hcont hz hz₁
  refine ⟨fun τ => if 0 < d (comp z₁) τ then 2 * Real.pi / d (comp z₁) τ else 1, fun τ => ?_, ?_⟩
  · dsimp only
    split_ifs with h
    · exact div_pos Real.two_pi_pos h
    · exact one_pos
  intro x hx hI Hm hHm f Wd hW
  have hz := hinΩ x hx hI
  obtain ⟨x', hx'o, hx'⟩ := hcomp _ hz
  rw [ch₀.left_inv hx] at hx'
  have hk := hconst _ hz
  have hExpAt : IsExpAt T.Z.t (x.1 ≫ genι T.Z) (ex x) := ⟨hadd x hx, (htan x hx).1, (htan x hx).2⟩
  have hslice : IsHolTo Set.univ (fun w => (ex x w).left) := by
    have hmem : ch₀ x ∈ ch₀.target := ch₀.map_source hx
    have := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun w : Fin g → ℂ => (ch₀ x, w)) hjoint isOpen_univ
      ((differentiableOn_const (ch₀ x)).prodMk differentiableOn_id) fun w _ => Set.mk_mem_prod hmem (Set.mem_univ w)
    dsimp only at this
    rw [ch₀.left_inv hx] at this
    exact this
  obtain ⟨hg, ho⟩ := GlobalTheory.T.hodgeMetric_frame_eq_riemannForm_at_interior_point E H Dw l Xo c O β T.Z σ U hσ hU W hinj d hdpos hd g x (ex x) hI hExpAt hslice _ x' hx'o hx'
    Hm hHm.2.2.1 hHm.2.2.2 f Wd hW
  refine ⟨fun τ => ?_, ho⟩
  rw [hg τ]
  by_cases hm : Dw.mult τ = 0
  · ext i
    have h2 := i.2
    omega
  · have hpos := hdpos _ x' hx'o τ (Nat.pos_of_ne_zero hm)
    have e : d (comp (ch₀ x)) τ = d (comp z₁) τ := by rw [hk]
    rw [e] at hpos ⊢
    simp only [if_pos hpos]

end GlobalTheory.HodgeChart
end
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts


theorem _root_.GlobalTheory.T.exists_holomorphic_eigenFrame_dirs_in_expChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (C : FlagCpt T.Z e) (X : Var F) (j : X.X ⟶ gen T.Z) (f : C.Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e C X j f f₀ Eb A₀ → ∀ (y : GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) (n g : ℕ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g), IsExpChart ch₀ ex → cxOf e σ hj y ∈ ch₀.source → ch₀ (cxOf e σ hj y) = 0 → ∃ A ∈ Eb.S (GlobalTheory.Cartier.under y), ∃ r : ℝ, 0 < r ∧ ∃ W : (Fin n → ℂ) → (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Fin g → ℂ, (∀ p k, DifferentiableOn ℂ (fun u => W u p k) (Metric.ball 0 r)) ∧ LinearIndependent ℂ (W 0) ∧ ∀ z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom), cxOf e σ hj z ∈ ch₀.source → ch₀ (cxOf e σ hj z) ∈ Metric.ball 0 r → (∃ g' : EigFrame T.Z σ ((cxOf e σ hj z).1 ≫ genι T.Z), FrameAt e f₀ A₀ A z g') ∧ ∀ g' : EigFrame T.Z σ ((cxOf e σ hj z).1 ≫ genι T.Z), FrameAt e f₀ A₀ A z g' → Dirs ⟨cxOf e σ hj z, g'⟩ (fun w => (ex (cxOf e σ hj z) w).left) (W (ch₀ (cxOf e σ hj z))) := by
  first | exact @GlobalTheory.LieBase.exists_chart_dirs | exact GlobalTheory.LieBase.exists_chart_dirs | (intros; apply GlobalTheory.LieBase.exists_chart_dirs <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.exists_rescale_primitive_linearIndependent_cell : ∀ {O : Type} [CommRing O] [Module.Finite ℤ O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ δ → LinearIndependent ℤ δ →
    ∃ (δ' : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ'), LinearIndependent ℤ δ' ∧
      (∀ i, IsPrim bar (⟨δ' i, h.mem i⟩ : balForms bar X)) ∧ ∀ β, InRCone δ β → InRCone δ' β := by
  first | exact @GlobalTheory.PolFan.SmoothEnd.exists_rescale_prim | exact GlobalTheory.PolFan.SmoothEnd.exists_rescale_prim | (intros; apply GlobalTheory.PolFan.SmoothEnd.exists_rescale_prim <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.exists_multCellsAmong_of_isPolyFan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ : InvFun (𝓞 E)),
    IsPolyFan H.bar q φ → ∀ M : ℕ, ∃ n : ℕ, MultCellsAmong H.bar q φ M n := by
  first | exact @GlobalTheory.PolFan.CellClass.multCellsAmong_of_isPolyFan | exact GlobalTheory.PolFan.CellClass.multCellsAmong_of_isPolyFan | (intros; apply GlobalTheory.PolFan.CellClass.multCellsAmong_of_isPolyFan <;> assumption)
end
