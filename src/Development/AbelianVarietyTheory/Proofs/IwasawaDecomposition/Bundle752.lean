module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle192
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle225
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle694
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle665
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle387
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle744
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle244
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle668
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle699
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle630
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle696
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle739
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle748
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle716
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthCommonDenominatorRankLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthLeOnCentreCell
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle729
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle685
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionNewCellMultiplicityLt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionOldCellMultiplicityLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle750
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle745
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle447
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle749
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle720
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftAtReferenceTupleOverEnlargedBase
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532

@[expose] public section

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option autoImplicit false

theorem GlobalTheory.UnifImage.image_domFlat_eq_ptsIn_openPart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ψ '' DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) = ptsIn X.str (σ.comp e.toRingHom) (openPart j) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  obtain ⟨hjo, hfj, -⟩ := hL
  have hm : Mono j := inferInstance
  have hinj : Function.Injective (cxOf e σ hj) := fun a b h =>
    Subtype.ext ((cancel_mono j).1 (congrArg Subtype.val h))
  have hp0 : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by rw [(hU.2.1 k).1]; omega
  have hmem : ∀ y : CxPts X.str (σ.comp e.toRingHom),
      y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j) ↔ ¬ LiesIn (cxOf e σ hj y) (genBd T.Z) := by
    intro y
    constructor
    · intro h hb
      have h1 := h (show IsLocalRing.closedPoint ℂ ∈ (⊤ : (Sp ℂ).Opens) from trivial)
      exact h1 hb
    · intro h pt _
      obtain rfl : pt = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
      exact h
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨x, hx, hxv⟩ := GlobalTheory.TrueCx.FrameOnto.frame_onto E (Dw.p + Dw.q) Dw.p (U.X k) (Nat.le_add_right _ _)
      (U.X k).Ψ (Equiv.refl _) hp0 (unflat v) hv
    have hv' : v = flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x) := by
      rw [hxv]; rfl
    rw [hmem, hv', hψ ⟨x, hx⟩]
    exact not_liesIn_cxPt (Z := T.Z) _
  · intro hy
    rw [hmem] at hy
    obtain ⟨g⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c O β T.Z ℂ σ (cxOf e σ hj y).1 (cxOf e σ hj y).2
    obtain ⟨q, hq, -⟩ := exists_frPt_cxPt_of_eigFrame E H Dw l Xo c O β T.Z σ (cxOf e σ hj y) hy g
    obtain ⟨k', x', t, hB⟩ := hU.2.2.1 q
    have hq' : cxPt T.Z (U.un k' x') = cxOf e σ hj y := (cxPt_congr hB.1.symm).trans hq
    have hyχ : y.1 ≫ j ≫ genStr T.Z = spMap σ := by
      have h2 := (cxOf e σ hj y).2
      simpa [cxOf, Category.assoc] using h2
    obtain ⟨p, hp⟩ := GlobalTheory.FlagCptBase.exists_pt_over_base E H Dw l Xo c O β T.Z F e σ (Dw.p + Dw.q) U Φ k X j hjo hj f hfj
      (GlobalTheory.T.flagSpaceComponent_carries_every_frame_flag E H Dw l Xo c O β T.Z F e σ (Dw.p + Dw.q) U Φ)
      (fun i K _ χ p h => GlobalTheory.CarryAll.carry_some E H Dw l Xo c O β T.Z F e (Φ.C i) K χ p h) ℂ σ y.1 hyχ
    let s : Sp (CAt σ) := IsLocalRing.closedPoint ℂ
    obtain ⟨w', hw'⟩ := Φ.label k' x' s
    have hkk : k = k' := by
      refine GlobalTheory.FlagCptBase.eq_of_apply_eq Φ (GlobalTheory.T.flagSpaceComponent_carries_every_frame_flag E H Dw l Xo c O β T.Z F e σ (Dw.p + Dw.q) U Φ)
        (fun i K _ χ p h => GlobalTheory.CarryAll.carry_some E H Dw l Xo c O β T.Z F e (Φ.C i) K χ p h) (p s) w' ?_
      rw [hw']
      have h3 : (GlobalTheory.AllWt.ptF (U.un k' x') ≫ T.Z.jQ) = (cxOf e σ hj y).1 := congrArg Subtype.val hq'
      rw [h3]
      show (Φ.C k).π (p s) = (y.1 ≫ j) s
      rw [← hp, ← hfj]
      rfl
    subst hkk
    refine ⟨flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x'.1), ?_, hinj ?_⟩
    · exact GlobalTheory.TrueCx.domPt_mem (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) hp0 x'.2
    · rw [hψ x', hq']
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

open scoped ComplexOrder Topology
open GlobalTheory.PointFormSign Matrix
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.PointFormSign

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem chernTop_pointPoly_nonneg {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    {n : ℕ} (G : V n → Mat Dw.mult ℂ) (v : V n)
    (h : ∀ τ : GlobalTheory.AllWt.Psi H, IsNegSq (curv (fun u => G u τ.1) v) (Dw.p + Dw.q - Dw.mult τ.1)) :
    0 ≤ chernTop (pointPoly H Dw) G v := by
  choose S T hS hF using h
  have key : aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => G u x.1) v x.2) (pointPoly H Dw) =
      ∏ τ : GlobalTheory.AllWt.Psi H, (sqPoly (T τ)).det ^ (Dw.p + Dw.q - Dw.mult τ.1) := by
    rw [pointPoly, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_pow, map_mul, aeval_C, aeval_X, GlobalTheory.T.chernFormPolyCoeff_top_of_neg_hermitianSquare _ _ _ _ (hS τ) (hF τ)]
    congr 1
    simp only [map_pow, map_neg, map_one]
    rw [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  have h0 : 0 ≤ topCoeff (aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => G u x.1) v x.2) (pointPoly H Dw)) := by
    rw [key]; exact GlobalTheory.T.topDegreeFormCoeff_prod_det_hermitianSquare_pow_nonneg _ _ _ T
  have hre : 0 ≤ (topCoeff (aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => G u x.1) v x.2) (pointPoly H Dw))).re :=
    (Complex.nonneg_iff.1 h0).1
  unfold chernTop
  exact mul_nonneg (inv_nonneg.2 (pow_nonneg Real.pi_pos.le _)) hre

end GlobalTheory.PointFormSign

theorem GlobalTheory.PointFormSign.chernTop_pointPoly_lieGram_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), 0 ≤ chernTop (pointPoly H Dw) (fun w => lieGram e U hj f₀ A₀ A (c'.e.symm w)) (c'.e y) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL y hy c' hyc A hA
  refine GlobalTheory.PointFormSign.chernTop_pointPoly_nonneg H Dw _ _ fun τ => ?_
  obtain ⟨κ, W, Z, hκ, hG, hZ, hW, hWu, hZd⟩ := GlobalTheory.T.lieEigenspaceHodgeGram_local_holomorphic_model E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL y hy c' hyc A hA τ
  exact GlobalTheory.T.isNegHermitianSquare_curvature_of_holomorphic_frameChange _ _ W Z κ hκ hG hZ hW hWu hZd (GlobalTheory.T.isNegHermitianSquare_curvature_boundedDomainHodgeGram _ _ _ hZd)
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory.PolFan.Mark

theorem exists_markFun {O : Type} [CommRing O] (bar : O → O) (ψ lab : InvFun O) (i : ℕ) :
    ∃ w : InvFun O, ∀ n B, w.toFun n B = markVal bar ψ lab i n B := by
  classical
  refine ⟨{ toFun := markVal bar ψ lab i, inv := ?_, zero := ?_ }, fun _ _ => rfl⟩
  · intro n m r hr B
    obtain ⟨s, hs⟩ := Module.projective_lifting_property r LinearMap.id hr
    have hrs : ∀ a, r (s a) = a := fun a => LinearMap.congr_fun hs a
    unfold markVal
    by_cases h : ∃ β : LinearMap.BilinForm ℤ (Fin m → O), ∀ a b, B a b = β a b
    · have h' : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), ∀ a b, B (r a) (r b) = β a b :=
        ⟨pull r h.choose, fun a b => h.choose_spec _ _⟩
      rw [dite_eq_left h, dite_eq_left h']
      have e : h'.choose = pull r h.choose := LinearMap.ext₂ fun a b => by
        have h1 := h'.choose_spec a b
        have h2 := h.choose_spec (r a) (r b)
        rw [pull_apply]
        exact_mod_cast h1.symm.trans h2
      rw [e, GlobalTheory.T.isMarkedBalancedIntForm_pullback_iff_splitSurjection O bar ψ lab i _ _ r s hrs]
    · have h' : ¬ ∃ β : LinearMap.BilinForm ℤ (Fin n → O), ∀ a b, B (r a) (r b) = β a b := by
        rintro ⟨β, h3⟩
        exact h ⟨pull s β, fun a b => by rw [pull_apply, ← h3, hrs, hrs]⟩
      rw [dite_eq_right h, dite_eq_right h']
  · intro B
    unfold markVal
    split_ifs with h h2
    · exfalso
      have := h2.2.2.2.1
      rw [InvFun.evalZ, lab.eval_of_subsingleton] at this
      exact absurd this (by positivity)
    · rfl
    · rfl


open Classical in
theorem evalZ_markFun {O : Type} [CommRing O] {bar : O → O} {ψ lab : InvFun O} {i : ℕ} {w : InvFun O}
    (hw : ∀ n B, w.toFun n B = markVal bar ψ lab i n B) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    [Module.Projective O X] (β : LinearMap.BilinForm ℤ X) :
    w.evalZ β = if IsMarked bar ψ lab i X β then 1 else 0 := by
  classical
  obtain ⟨n, t, ht⟩ := Module.Finite.exists_fin' O X
  obtain ⟨u, hu⟩ := Module.projective_lifting_property t LinearMap.id ht
  have htu : ∀ a, t (u a) = a := fun a => LinearMap.congr_fun hu a
  rw [InvFun.evalZ, w.eval_eq ht, hw]
  have e := markVal_int (bar := bar) (ψ := ψ) (lab := lab) (i := i) n (pull t β)
  simp only [pull_apply] at e
  rw [e, GlobalTheory.T.isMarkedBalancedIntForm_pullback_iff_splitSurjection O bar ψ lab i _ _ t u htu]

theorem exists_markFun_props : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ lab : InvFun (𝓞 E)) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → IsTwInv H lab → IsCarrierDim H.bar q ψ lab → ∃ w : InvFun (𝓞 E), IsTwInv H w ∧ ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 0 ∨ w.evalZ β = 1) ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1) ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → lab.evalZ β = ((i + 1 : ℕ) : ℝ)) ∧ (∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ v → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms H.bar X, (∀ y, 0 ≤ β' y y) → w.evalZ β = 1 → w.evalZ β' = 1 → InRCone v β → InRCone v β' → β = β') ∧ (∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ v → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β = ((i + 1 : ℕ) : ℝ) → ∃ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) ∧ w.evalZ β₀ = 1 ∧ InRCone v β₀) := by
  intro E _ _ _ H q ψ lab i hD hψ htψ htlab hlab
  classical
  obtain ⟨w, hw⟩ := exists_markFun H.bar ψ lab i
  have ev := fun {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X]
    (β : LinearMap.BilinForm ℤ X) => evalZ_markFun hw (X := X) β
  have mk : ∀ {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X]
      (β : LinearMap.BilinForm ℤ X), w.evalZ β = 1 → IsMarked H.bar ψ lab i X β := fun β h => by
    rw [ev] at h
    split_ifs at h with h'
    · exact h'
    · norm_num at h
  refine ⟨w, fun σ hσ n B => by rw [hw, hw]; exact GlobalTheory.T.markedFormIndicatorValue_invariant_hostFixingAut E H ψ lab i htψ htlab σ hσ n B, ?_⟩
  intro X _ _ _ _ hX
  refine ⟨fun β _ _ => ?_, fun β _ _ h1 => (mk β h1).2.2.1, fun β _ _ h1 => (mk β h1).2.2.2.1,
    fun m v hv hle β _ _ β' _ _ h1 h1' hc hc' =>
      GlobalTheory.T.polFan_marked_form_unique_in_cell E H q ψ lab i hD hψ hlab X hX m v hv hle β β' (mk β h1) (mk β' h1') hc hc',
    fun m v hv β hβ hp hc hl => ?_⟩
  · rw [ev]
    split_ifs <;> simp
  · obtain ⟨β₀, h0, hc0⟩ := GlobalTheory.T.polFan_exists_marked_form_in_cell E H q ψ lab i hD hψ hlab X hX m v hv β hβ hp hc hl
    exact ⟨β₀, h0.1, h0.2.1, by rw [ev, if_pos h0], hc0⟩

end GlobalTheory.PolFan.Mark
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.starSubdivision_newCell_multiplicity_lt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab w ψ' : InvFun (𝓞 E)),
    SimpLab H.bar q φ lab → IsCentreSet H.bar q φ w →
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell H.bar φ δ),
          LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
          ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
          ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1) →
    ∀ M : ℕ, maxMult H.bar q φ ≤ M →
    ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∀ (n : ℕ) (γ' : Fin n → LinearMap.BilinForm ℤ X) (hγ' : IsCell H.bar ψ' γ'),
        LinearIndependent ℤ γ' → (∀ i, IsPrim H.bar (⟨γ' i, hγ'.mem i⟩ : balForms H.bar X)) →
        ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (β₀ : LinearMap.BilinForm ℤ X) (m' : ℕ) (s : Fin m' ↪ Fin m)
          (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell H.bar φ γ → β₀ ∈ balForms H.bar X → (∀ y, 0 ≤ β₀ y y) →
          w.evalZ β₀ = 1 → InRCone γ β₀ → IsFaceCut γ s h → 0 < h β₀ →
          IsCell H.bar ψ' (Fin.cons β₀ fun j => γ (s j)) → (∀ j, InRCone (Fin.cons β₀ fun j => γ (s j)) (γ' j)) →
          cellMult H.bar (fun i => (⟨γ' i, hγ'.mem i⟩ : balForms H.bar X)) < M := by
  first | exact @GlobalTheory.PolFan.cellMult_lt_of_star_new | exact GlobalTheory.PolFan.cellMult_lt_of_star_new | (intros; apply GlobalTheory.PolFan.cellMult_lt_of_star_new <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.starSubdivision_oldCell_multiplicity_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab w ψ' : InvFun (𝓞 E)),
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) →
    IsPolyFan H.bar q φ → SimpLab H.bar q φ lab → ∀ M : ℕ, maxMult H.bar q φ ≤ M →
    ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∀ (n : ℕ) (γ' : Fin n → LinearMap.BilinForm ℤ X) (hγ' : IsCell H.bar ψ' γ'),
        LinearIndependent ℤ γ' → (∀ i, IsPrim H.bar (⟨γ' i, hγ'.mem i⟩ : balForms H.bar X)) →
        ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar φ γ → IsCell H.bar ψ' γ →
          (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → (∀ j, InRCone γ (γ' j)) →
          ∃ hφ : IsCell H.bar φ γ', cellMult H.bar (fun i => (⟨γ' i, hφ.mem i⟩ : balForms H.bar X)) ≤ M ∧
            ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ' β → w.evalZ β ≠ 1 := by
  first | exact @GlobalTheory.PolFan.starOld_cell_mult_le | exact GlobalTheory.PolFan.starOld_cell_mult_le | (intros; apply GlobalTheory.PolFan.starOld_cell_mult_le <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

theorem _root_.GlobalTheory.T.starSubdivision_function_linearOn_cells : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)) (K D : ℕ), IsCentreSet H.bar q ψ w → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → (starFun H.bar ψ w K D).LinearOn γ) ∧ (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → (starFun H.bar ψ w K D).LinearOn (Fin.cons β₀ fun j => γ (s j))) := by
  first | exact @GlobalTheory.PolFan.starFun_linearOn | exact GlobalTheory.PolFan.starFun_linearOn | (intros; apply GlobalTheory.PolFan.starFun_linearOn <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

theorem _root_.GlobalTheory.T.starDepth_common_denominator_rank_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∃ D₀ : ℕ, 0 < D₀ ∧ ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, (D₀ : ℝ) * (starDepth H.bar ψ w).evalZ β = n := by
  first | exact @GlobalTheory.PolFan.StarDen.starDepth_den | exact GlobalTheory.PolFan.StarDen.starDepth_den | (intros; apply GlobalTheory.PolFan.StarDen.starDepth_den <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

theorem _root_.GlobalTheory.T.starDepth_le_on_centre_cell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → (h β₀ : ℝ) * (starDepth H.bar ψ w).evalZ β ≤ h β) ∧ (starDepth H.bar ψ w).evalZ β₀ = 1 ∧ (∀ j, (starDepth H.bar ψ w).evalZ (γ (s j)) = 0) ∧ ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → (h β₀ : ℝ) * (starDepth H.bar ψ w).evalZ β = h β → ∃ (k : ℕ) (c : Fin (m' + 1) → ℕ), 0 < k ∧ k • β = ∑ i, c i • (Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) i := by
  first | exact @GlobalTheory.PolFan.starDepth_on_cell | exact GlobalTheory.PolFan.starDepth_on_cell | (intros; apply GlobalTheory.PolFan.starDepth_on_cell <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.exists_markedForm_pieces_rays_of_simplicialCells : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)), IsTwInv H φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀] [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (h₀ : IsCell H.bar φ δ₀),
  LinearIndependent ℤ δ₀ → (∀ i, IsPrim H.bar (⟨δ₀ i, h₀.mem i⟩ : balForms H.bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), v ≠ 0 → (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (β : LinearMap.BilinForm ℤ X), (OrbMark.orbFun (𝓞 E) H.w0 v).evalZ β = 1 →
  ∃ p : Fin m₀ → LinearMap.BilinForm ℤ X, toReal β = ∑ i, t i • toReal (p i) ∧
    (∀ i, 0 < t i → p i ∈ balForms H.bar X ∧ (∀ y, 0 ≤ p i y y) ∧
      (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = p i → k = 1) ∧
      ∀ lab : InvFun (𝓞 E), IsTwInv H lab → lab.evalZ (p i) = lab.evalZ (δ₀ i)) ∧
    ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar φ δ → LinearIndependent ℤ δ →
      ∀ c : Fin m → ℝ, (∀ j, 0 ≤ c j) → toReal β = ∑ j, c j • toReal (δ j) →
        (∀ i, 0 < t i → ∃ j, 0 < c j ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j)) ∧
        (∀ j, 0 < c j → ∃ i, 0 < t i ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j) ∧ c j = t i * d) := by
  first | exact @GlobalTheory.PolFan.OrbMark.exists_pieces_match | exact GlobalTheory.PolFan.OrbMark.exists_pieces_match | (intros; apply GlobalTheory.PolFan.OrbMark.exists_pieces_match <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

theorem _root_.GlobalTheory.T.goodIdempotent_coefficients_agree_enlarged_base : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq f' f → HEq w'.px w.px → GrpTrue Z.N f → GrpTrue Z'.N f' → RSideW z Wt' R' →
  ∀ cG : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd, Keep R'.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).lv2 cG → IdemSame z Xg := by
  first | exact @GlobalTheory.Mem.R3.Rw.WeilExt.idemSame_of_keep | exact GlobalTheory.Mem.R3.Rw.WeilExt.idemSame_of_keep | (intros; apply GlobalTheory.Mem.R3.Rw.WeilExt.idemSame_of_keep <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

theorem _root_.GlobalTheory.T.thetaLift_at_reference_tuple_over_enlarged_base : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq w'.px w.px → z.R.toRealDat.ExAt → RSide z Wt' R' → IdemSame z Xg → LiftAt R'.toRealDat (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) := by
  first | exact @GlobalTheory.Mem.R3.Rw.LiftExt.liftAt_of_rSide | exact GlobalTheory.Mem.R3.Rw.LiftExt.liftAt_of_rSide | (intros; apply GlobalTheory.Mem.R3.Rw.LiftExt.liftAt_of_rSide <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

theorem _root_.GlobalTheory.T.liftCharacters_agree_over_enlarged_base : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq f' f → HEq w'.px w.px → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh → LevSame z Wt' R' := by
  first | exact @GlobalTheory.Mem.R3.Rw.LevExt.levSame_of_levOf | exact GlobalTheory.Mem.R3.Rw.LevExt.levSame_of_levOf | (intros; apply GlobalTheory.Mem.R3.Rw.LevExt.levSame_of_levOf <;> assumption)
end
