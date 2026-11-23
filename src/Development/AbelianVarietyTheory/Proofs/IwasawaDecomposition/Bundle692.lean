module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle656
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle012
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle447
public import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle680
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle650
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle386
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle388
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtOfFrameEqOfPointEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle665
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ValuativeCriterion
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

namespace GlobalTheory.CarrySpec

theorem upper_mul {n : ℕ} {R : Type} [CommRing R] {M N : Matrix (Fin n) (Fin n) R}
    (hM : ∀ a i, i < a → M a i = 0) (hN : ∀ a i, i < a → N a i = 0) :
    (∀ a i, i < a → (M * N) a i = 0) ∧ ∀ i, (M * N) i i = M i i * N i i := by
  first
  | exact @_root_.GlobalTheory.UpperTriangularMul.upperTriangular_mul
  | exact _root_.GlobalTheory.UpperTriangularMul.upperTriangular_mul
  | (apply _root_.GlobalTheory.UpperTriangularMul.upperTriangular_mul <;> assumption)
  | (intros; apply _root_.GlobalTheory.UpperTriangularMul.upperTriangular_mul <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UpperTriangularMul.upperTriangular_mul <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UpperTriangularMul.upperTriangular_mul ..)

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (ρ : R →+* R') (ψ : R' →+* R'') :
    spMap (ψ.comp ρ) = spMap ψ ≫ spMap ρ := by
  simp [spMap, Spec.map_comp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem isMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {φ'' : c.F →+* R''} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} {x'' : Sp R'' ⟶ Z.X} {f : EigFrame Z φ x}
    {f' : EigFrame Z φ' x'} {f'' : EigFrame Z φ'' x''} {ρ : R →+* R'} {ψ : R' →+* R''}
    (h1 : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f embτ basisIdx) ρ f') (h2 : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f' embτ basisIdx) ψ f'') : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f embτ basisIdx) (ψ.comp ρ) f'' := fun τ i => by
  rw [h2 τ i, h1 τ i, GlobalTheory.ShFam.CarriesAt.spMap_dualMap_comp, Category.assoc]

theorem tri_of_co {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {φ' : c.F →+* R'} {x : Sp R ⟶ Z.X}
    {x' : Sp R' ⟶ Z.X} {f : EigFrame Z φ x} {ψ : R →+* R'} {f' g : EigFrame Z φ' x'} (hf : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f embτ basisIdx) ψ f')
    (hx : x' = spMap ψ ≫ x) (hφ : φ' = ψ.comp φ) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R'ˣ)
    (hu : ∀ τ a i, i < a → f'.co g τ a i = 0) (hd : ∀ τ i, f'.co g τ i i = t τ i) : f.Tri ψ g t :=
  ⟨hx, hφ, fun τ i => ⟨fun a => f'.co g τ a i, hd τ i, fun k hk => hu τ k i hk, by
    have := f'.co_spec g τ i
    rwa [funext (hf τ)] at this⟩⟩

theorem tri_spec {R V L k : Type} [CommRing R] [CommRing V] [CommRing L] [CommRing k]
    {φ₁ : c.F →+* R} {x₁ : Sp R ⟶ Z.X} (f : EigFrame Z φ₁ x₁) (ρ : R →+* V) (ν : V →+* L)
    (hν : Function.Injective ν) (r : V →+* k) {φV : c.F →+* V} {xV : Sp V ⟶ Z.X} (hxV : xV = spMap ρ ≫ x₁)
    (gV : EigFrame Z φV xV) {φL : c.F →+* L} {xL : Sp L ⟶ Z.X} (gL : EigFrame Z φL xL)
    (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ) (hL : gV.Tri ν gL tL)
    (t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ) (hfL : f.Tri (ν.comp ρ) gL t')
    {φk : c.F →+* k} {xk : Sp k ⟶ Z.X} (gk : EigFrame Z φk xk) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ)
    (hk : gV.Tri r gk tk) : ∃ t'' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ, f.Tri (r.comp ρ) gk t'' := by
  have hφV : φV = ρ.comp φ₁ := RingHom.ext fun a => hν (by
    have := RingHom.congr_fun (hL.2.1.symm.trans hfL.2.1) a
    simpa using this)
  obtain ⟨h, hh⟩ := EigFrame.exists_isMap f ρ hφV hxV
  obtain ⟨gVL, hgVL⟩ := EigFrame.exists_isMap gV ν hL.2.1 hL.1
  obtain ⟨hLf, hhL⟩ := EigFrame.exists_isMap h ν hL.2.1 hL.1
  have hfhL : (_root_.GlobalTheory.ShFam.EigFrame.IsMap f) (ν.comp ρ) hLf := isMap_comp hh hhL

  have hA : ∀ τ, (∀ a i, i < a → h.co gV τ a i = 0) := fun τ a i hia => by
    obtain ⟨hU, -⟩ := EigFrame.Tri.co τ hfL hfhL
    obtain ⟨hW, -⟩ := EigFrame.Tri.co τ hL hgVL
    have hmap := EigFrame.IsMap.co τ hhL hgVL hL.1
    have hmul := EigFrame.co_mul hLf gVL gL τ
    have hWu := EigFrame.isUnit_det_co gVL gL τ
    set W := gVL.co gL τ
    have hWt : W.BlockTriangular id := fun a b h => hW a b h
    letI := Matrix.invertibleOfIsUnitDet W hWu
    have hWi : W⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hWt
    have hM : hLf.co gVL τ = hLf.co gL τ * W⁻¹ := by
      rw [← hmul, Matrix.mul_nonsing_inv_cancel_right _ _ hWu]
    have hP : (hLf.co gL τ * W⁻¹).BlockTriangular id :=
      Matrix.BlockTriangular.mul (fun a b h => hU a b h) hWi
    apply hν
    have := hP hia
    rw [← hM, hmap, Matrix.map_apply] at this
    rw [this, map_zero]
  have hAd : ∀ τ i, IsUnit (h.co gV τ i i) := fun τ i => by
    have hdet := EigFrame.isUnit_det_co h gV τ
    rw [Matrix.det_of_upperTriangular (fun a b hab => hA τ a b hab)] at hdet
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun j => h.co gV τ j j) (Finset.mem_univ i)) hdet

  obtain ⟨hkf, hhk⟩ := EigFrame.exists_isMap h r hk.2.1 hk.1
  obtain ⟨gVk, hgVk⟩ := EigFrame.exists_isMap gV r hk.2.1 hk.1
  have hfhk : (_root_.GlobalTheory.ShFam.EigFrame.IsMap f) (r.comp ρ) hkf := isMap_comp hh hhk
  have hco : ∀ τ, hkf.co gk τ = (h.co gV τ).map r * gVk.co gk τ := fun τ => by
    rw [← EigFrame.IsMap.co τ hhk hgVk hk.1, EigFrame.co_mul]
  have key : ∀ τ, (∀ a i, i < a → hkf.co gk τ a i = 0) ∧ ∀ i, hkf.co gk τ i i = r (h.co gV τ i i) * tk τ i := by
    intro τ
    obtain ⟨hN, hNd⟩ := EigFrame.Tri.co τ hk hgVk
    have hm := upper_mul (M := (h.co gV τ).map r) (fun a i hia => by rw [Matrix.map_apply, hA τ a i hia, map_zero]) hN
    rw [hco]
    exact ⟨hm.1, fun i => by rw [hm.2, Matrix.map_apply, hNd]⟩
  refine ⟨fun τ i => ((hAd τ i).map r).unit * tk τ i, tri_of_co hfhk ?_ ?_ _ (fun τ => (key τ).1) fun τ i => ?_⟩
  · rw [hk.1, hxV, spMap_comp, Category.assoc]
  · rw [hk.2.1, hφV, RingHom.comp_assoc]
  · rw [(key τ).2, Units.val_mul, IsUnit.unit_spec]

end GlobalTheory.CarrySpec

namespace GlobalTheory.CarrySpec

open MvPolynomial GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

theorem spec_of_anypoint (hany : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (k : Type) [Field k] (φ : c.F →+* k) (x : Sp k ⟶ Z.X) (g : EigFrame Z φ x) (p : Sp k ⟶ C.Y.X), C.Carries p g → ∀ (y : C.Y.X) (ψ : C.Y.X.presheaf.stalk y →+* k) (φ₁ : c.F →+* C.Y.X.presheaf.stalk y) (f : EigFrame Z φ₁ (stalkPt C.Y y ≫ C.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ), p = spMap ψ ≫ stalkPt C.Y y → f.Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 t → ∃ t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ, f.Tri ψ g t') : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (V : Type) [CommRing V] [IsLocalRing V] (L : Type) [Field L] (ν : V →+* L), Function.Injective ν → ∀ (k : Type) [Field k] (r : V →+* k), RingHom.ker r = IsLocalRing.maximalIdeal V → ∀ (q : Sp V ⟶ C.Y.X) (φV : c.F →+* V) (xV : Sp V ⟶ Z.X), xV = q ≫ C.π ≫ genι Z → ∀ (gV : EigFrame Z φV xV) (φL : c.F →+* L) (xL : Sp L ⟶ Z.X) (gL : EigFrame Z φL xL) (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ), gV.Tri ν gL tL → C.Carries (spMap ν ≫ q) gL → ∀ (φk : c.F →+* k) (xk : Sp k ⟶ Z.X) (gk : EigFrame Z φk xk) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ), gV.Tri r gk tk → C.Carries (spMap r ≫ q) gk := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C V _ _ L _ ν hν k _ r _ q φV xV hxV gV φL xL gL tL hL hcar φk xk gk tk hk
  set y₀ := q (IsLocalRing.closedPoint V)
  set ρ := (Scheme.stalkClosedPointTo (R := CommRingCat.of V) q).hom
  have hq : spMap ρ ≫ stalkPt C.Y y₀ = q := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of V) q
  obtain ⟨φ₁, f, t, hf, -⟩ := C.gr_spec y₀
  have hpL : spMap ν ≫ q = spMap (ν.comp ρ) ≫ stalkPt C.Y y₀ :=
    (congrArg (spMap ν ≫ ·) hq).symm.trans (by rw [spMap_comp, Category.assoc])
  obtain ⟨t', hfL⟩ := hany E H Dw l Xo c O β Z F e C L φL xL gL (spMap ν ≫ q) hcar y₀ (ν.comp ρ) φ₁ f t hpL hf
  have hxV' : xV = spMap ρ ≫ (stalkPt C.Y y₀ ≫ C.π ≫ genι Z) :=
    hxV.trans ((congrArg (· ≫ C.π ≫ genι Z) hq).symm.trans (Category.assoc _ _ _))
  obtain ⟨t'', htri⟩ := tri_spec f ρ ν hν r hxV' gV gL tL hL t' hfL gk tk hk
  exact ⟨y₀, r.comp ρ, φ₁, f, t, t'',
    (congrArg (spMap r ≫ ·) hq).symm.trans (by rw [spMap_comp, Category.assoc]), hf, htri⟩

end GlobalTheory.CarrySpec
end
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifSlice

open Matrix Formalism.DegreeFormula GlobalTheory.TrueCx ReciprocityTheory.ChartRestriction.G.FD

theorem locInj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ z₀ ∈ Formalism.DegreeFormula.DomI Tau j (r - j), ∃ O : Set (Tau → Matrix (Fin j) (Fin (r - j)) ℂ), IsOpen O ∧ z₀ ∈ O ∧ ∀ z ∈ O ∩ Formalism.DegreeFormula.DomI Tau j (r - j), ∀ z' ∈ O ∩ Formalism.DegreeFormula.DomI Tau j (r - j), ∀ γ ∈ X.Γ, z' = Formalism.DegreeFormula.moebI (GlobalTheory.TrueCx.toUpq X hj κ γ) z → z = z' := GlobalTheory.T.boundedDomain_arithmeticGroup_locally_injective

theorem domPt_rel_of_pt_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ r)
    (hU : Formalism.L2.PjFree.IsUnf U) (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (k : U.Comp) {j : ℕ} (hj : j ≤ r) (hp : (U.X k).p0 = r - j) {Tau : Type} [Fintype Tau] (κ : Tau ≃ (U.X k).Ψ)
    (x x' : (U.X k).dom) (h : (U.un k x).x = (U.un k x').x) :
    ∃ γ ∈ (U.X k).Γ, domPt (U.X k) hj κ x'.1 = moebI (toUpq (U.X k) hj κ γ) (domPt (U.X k) hj κ x.1) := by
  obtain ⟨b, hb, hb0, hm, t, ht⟩ := GlobalTheory.PointOfFrames.exists_frBor U hU hσ k x (U.un k x') h
  obtain ⟨γ, hγ, b', hb', e⟩ := (hU.2.2.2.1 k k ⟨_, hm⟩ x').1 ⟨t, ht⟩
  have e' : x'.1 = rmul (lact γ (rmul x.1 b)) b' := eq_of_heq (Sigma.mk.inj e).2
  refine ⟨γ, hγ, ?_⟩
  rw [e', domPt_rmul _ hj κ hb', domPt_lact _ hj κ hp γ hm,
    GlobalTheory.PointOfFrames.domPt_rmul_block _ hj κ _ b hb (by rw [← hp]; exact hb0)]

theorem flat_unflat {ι : Type} {p q : ℕ} (v : ι × Fin p × Fin q → ℂ) : flat (unflat v) = v := by
  funext ⟨i, a, b⟩; rfl

theorem unflat_flat {ι : Type} {p q : ℕ} (z : ι → Matrix (Fin p) (Fin q) ℂ) : unflat (flat z) = z := by
  funext i; ext a b; rfl

theorem continuous_unflat {ι : Type} {p q : ℕ} :
    Continuous (unflat : (ι × Fin p × Fin q → ℂ) → ι → Matrix (Fin p) (Fin q) ℂ) :=
  continuous_pi fun _ => continuous_matrix fun _ _ => continuous_apply _

theorem exists_slice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (x₀ : (U.X k).dom) (n : ℕ), n = (U.X k).Ψ.card * (Dw.p * Dw.q) → ∃ (W : Set (V n)) (a : V n) (ψ : V n → Frame (U.X k).Ψ (Dw.p + Dw.q)), IsOpen W ∧ a ∈ W ∧ (∀ w ∈ W, ψ w ∈ (U.X k).dom) ∧ (∀ τ i i', DifferentiableOn ℂ (fun w => mat (ψ w) τ i i') W) ∧ (∀ h : ψ a ∈ (U.X k).dom, (U.un k ⟨ψ a, h⟩).x = (U.un k x₀).x) ∧ ∀ w ∈ W, ∀ w' ∈ W, ∀ (h : ψ w ∈ (U.X k).dom) (h' : ψ w' ∈ (U.X k).dom), (U.un k ⟨ψ w, h⟩).x = (U.un k ⟨ψ w', h'⟩).x → w = w' := by
  intro E _ _ _ H Dw l Xo c σ U hσ hU k x₀ n hn
  classical
  have hj : Dw.p ≤ Dw.p + Dw.q := Nat.le_add_right _ _
  have hp : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by have := (hU.2.1 k).1; omega
  have hcard : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = n := by
    rw [hn, Fintype.card_prod, Fintype.card_prod, Fintype.card_coe, Fintype.card_fin, Fintype.card_fin,
      Nat.add_sub_cancel_left]
  let f : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let L : V n ≃L[ℂ] ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) :=
    (EuclideanSpace.equiv (Fin n) ℂ).trans (LinearEquiv.funCongrLeft ℂ ℂ f).toContinuousLinearEquiv
  set z₀ := domPt (U.X k) hj (Equiv.refl (U.X k).Ψ) x₀.1 with hz₀
  have hz₀D : z₀ ∈ DomI (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) := domPt_mem (U.X k) hj _ hp x₀.2
  obtain ⟨O, hO, hz₀O, hinj⟩ := locInj E (Dw.p + Dw.q) Dw.p (U.X k) hj (U.X k).Ψ (Equiv.refl _) hp z₀ hz₀D
  let ψ : V n → Frame (U.X k).Ψ (Dw.p + Dw.q) := fun w => SecFrame.frameAt (U.X k) hj (Equiv.refl _) (unflat (L w))
  have hdom : ∀ w, unflat (L w) ∈ DomI (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ψ w ∈ (U.X k).dom := fun w hw =>
    SecFrame.frameAt_mem (U.X k) hj _ hp hw
  have hpt : ∀ w, domPt (U.X k) hj (Equiv.refl (U.X k).Ψ) (ψ w) = unflat (L w) := fun w => SecFrame.domPt_frameAt (U.X k) hj _ _
  refine ⟨{w | unflat (L w) ∈ O} ∩ L ⁻¹' DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), L.symm (flat z₀), ψ,
    (hO.preimage (continuous_unflat.comp L.continuous)).inter
      (GlobalTheory.HodgeDomain.ActionDeriv.isOpen_domFlat.preimage L.continuous), ?_, fun w hw => hdom w hw.2,
    fun τ i i' => ((SecFrame.differentiable_frameAt (U.X k) hj (Equiv.refl _) τ i i').comp L.differentiable).differentiableOn,
    fun h => ?_, fun w hw w' hw' h h' e => ?_⟩
  · refine ⟨?_, ?_⟩
    · show unflat (L (L.symm (flat z₀))) ∈ O
      rw [L.apply_symm_apply, unflat_flat]; exact hz₀O
    · show unflat (L (L.symm (flat z₀))) ∈ DomI (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p)
      rw [L.apply_symm_apply, unflat_flat]; exact hz₀D
  · have e0 : domPt (U.X k) hj (Equiv.refl (U.X k).Ψ) (ψ (L.symm (flat z₀))) = domPt (U.X k) hj (Equiv.refl (U.X k).Ψ) x₀.1 := by
      rw [hpt, L.apply_symm_apply, unflat_flat]
    have h5 : ∀ τ, Formalism.MJ.moeb (frameCo (U.X k) hj (ψ (L.symm (flat z₀))) τ) 0 = Formalism.MJ.moeb (frameCo (U.X k) hj x₀.1 τ) 0 :=
      fun τ => congrFun e0 τ
    exact PointWell.pt_eq_of_block hU hσ k ⟨_, h⟩ x₀
      (fun τ => PointWell.block_of_moeb_eq (U.X k) hj hp h x₀.2 τ (h5 τ))
      (fun τ => PointWell.block_of_moeb_eq (U.X k) hj hp x₀.2 h τ (h5 τ).symm)
  · obtain ⟨γ, hγ, hγe⟩ := domPt_rel_of_pt_eq U hU hσ k hj hp (Equiv.refl (U.X k).Ψ) ⟨_, h⟩ ⟨_, h'⟩ e
    have hγe' : unflat (L w') = moebI (toUpq (U.X k) hj (Equiv.refl (U.X k).Ψ) γ) (unflat (L w)) := by
      rw [← hpt w', ← hpt w]; exact hγe
    have h1 := hinj _ ⟨hw.1, hw.2⟩ _ ⟨hw'.1, hw'.2⟩ γ hγ hγe'
    have h2 : L w = L w' := by rw [← flat_unflat (L w), h1, flat_unflat]
    exact L.injective h2

end GlobalTheory.UnifSlice
end
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCptLift

theorem exists_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (L : Type) [Field L] [Algebra V L] [IsFractionRing V L] (yV : Sp V ⟶ gen Z) (pL : Sp L ⟶ C.Y.X), pL ≫ C.π = spMap (algebraMap V L) ≫ yV → ∃ q : Sp V ⟶ C.Y.X, q ≫ C.π = yV ∧ spMap (algebraMap V L) ≫ q = pL := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C V _ _ _ L _ _ _ yV pL h
  have : IsProper Z.s := projProper O Z.X Z.s Z.proj
  have : IsProper (genStr Z) := inferInstance
  have : IsIso (spMap e.toRingHom) := by
    have : IsIso (CommRingCat.ofHom e.toRingHom) := e.toCommRingCatIso.isIso_hom
    infer_instance
  have : IsSeparated (genStr Z ≫ spMap e.toRingHom) := inferInstance
  have : IsProper (C.π ≫ genStr Z ≫ spMap e.toRingHom) := by rw [C.π_str]; infer_instance
  have : IsProper C.π := IsProper.of_comp C.π (genStr Z ≫ spMap e.toRingHom)
  have hv : ValuativeCriterion.Existence C.π := by
    have h' : UniversallyClosed C.π := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h'
    exact h'.1
  obtain ⟨⟨q, q1, q2⟩⟩ := (hv ⟨V, L, pL, yV, ⟨h⟩⟩).exists_lift
  exact ⟨q, q2, q1⟩

end GlobalTheory.FlagCptLift
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions
  Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle GlobalTheory.ProjVar GlobalTheory.GoodMetric GlobalTheory.LieBase

namespace GlobalTheory.ShFam.CarriesAt

theorem diag_mul_of_blockTriangular {R : Type} [CommRing R] {n : ℕ} {A B : Matrix (Fin n) (Fin n) R}
    (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)
  rcases lt_or_gt_of_ne hj with h | h
  · rw [hA h, zero_mul]
  · rw [hB h, mul_zero]

theorem isUnit_diag_of_blockTriangular {R : Type} [CommRing R] {n : ℕ} {A : Matrix (Fin n) (Fin n) R}
    (hA : A.BlockTriangular id) (hd : IsUnit A.det) (i : Fin n) : IsUnit (A i i) := by
  rw [Matrix.det_of_upperTriangular hA] at hd
  exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun j => A j j) (Finset.mem_univ i)) hd

theorem tri_of_carries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (k : Type) [Field k] (φ : c.F →+* k) (x : Sp k ⟶ Z.X) (g : EigFrame Z φ x) (p : Sp k ⟶ C.Y.X), C.Carries p g → ∀ (y : C.Y.X) (ψ : C.Y.X.presheaf.stalk y →+* k) (φ₁ : c.F →+* C.Y.X.presheaf.stalk y) (f : EigFrame Z φ₁ (stalkPt C.Y y ≫ C.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ), p = spMap ψ ≫ stalkPt C.Y y → f.Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 t → ∃ t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ, f.Tri ψ g t' := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C k _ φ x g p hC y ψ φ₁ f t hp hf
  obtain ⟨y₁, ψ₁, φ₂, f₁, t₁, t₁', hp₁, hf₁, hg₁⟩ := hC

  have hsp : p (IsLocalRing.closedPoint k) ⤳ y := by
    have : p (IsLocalRing.closedPoint k) ∈ Set.range (C.Y.X.fromSpecStalk y) := by
      rw [hp]
      exact ⟨spMap ψ (IsLocalRing.closedPoint k), rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hsp₁ : p (IsLocalRing.closedPoint k) ⤳ y₁ := by
    have : p (IsLocalRing.closedPoint k) ∈ Set.range (C.Y.X.fromSpecStalk y₁) := by
      rw [hp₁]
      exact ⟨spMap ψ₁ (IsLocalRing.closedPoint k), rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hψ : ψ = (Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom.comp (C.Y.X.presheaf.stalkSpecializes hsp).hom := by
    refine EigLoc.spMap_inj ((cancel_mono (C.Y.X.fromSpecStalk y)).1 ?_)
    have e1 := spMap_stalkClosedPointTo p
    have e2 : spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom ≫ C.Y.X.fromSpecStalk y = C.Y.X.fromSpecStalk _ :=
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
    have e3 : spMap ((Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom.comp (C.Y.X.presheaf.stalkSpecializes hsp).hom) =
        spMap (Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom ≫ spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom := by
      simp [spMap, Spec.map_comp]
    rw [e3, Category.assoc, e2, e1]
    exact hp.symm
  have hψ₁ : ψ₁ = (Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom.comp (C.Y.X.presheaf.stalkSpecializes hsp₁).hom := by
    refine EigLoc.spMap_inj ((cancel_mono (C.Y.X.fromSpecStalk y₁)).1 ?_)
    have e1 := spMap_stalkClosedPointTo p
    have e2 : spMap (C.Y.X.presheaf.stalkSpecializes hsp₁).hom ≫ C.Y.X.fromSpecStalk y₁ = C.Y.X.fromSpecStalk _ :=
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp₁
    have e3 : spMap ((Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom.comp (C.Y.X.presheaf.stalkSpecializes hsp₁).hom) =
        spMap (Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom ≫ spMap (C.Y.X.presheaf.stalkSpecializes hsp₁).hom := by
      simp [spMap, Spec.map_comp]
    rw [e3, Category.assoc, e2, e1]
    exact hp₁.symm
  set ψp := (Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom with hψpdef
  set ρ := (C.Y.X.presheaf.stalkSpecializes hsp).hom with hρdef
  set ρ₁ := (C.Y.X.presheaf.stalkSpecializes hsp₁).hom with hρ₁def
  set alg := algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint k))) C.Y.X.functionField with halgdef
  have hinj : Function.Injective alg := IsFractionRing.injective _ _
  have halg : algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField = alg.comp ρ := algebraMap_eq_comp_specializes hsp
  have halg₁ : algebraMap (C.Y.X.presheaf.stalk y₁) C.Y.X.functionField = alg.comp ρ₁ :=
    algebraMap_eq_comp_specializes hsp₁
  have hxp : spMap ρ ≫ stalkPt C.Y y = stalkPt C.Y (p (IsLocalRing.closedPoint k)) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
  have hxp₁ : spMap ρ₁ ≫ stalkPt C.Y y₁ = stalkPt C.Y (p (IsLocalRing.closedPoint k)) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp₁
  have hpp : spMap ψp ≫ stalkPt C.Y (p (IsLocalRing.closedPoint k)) = p := spMap_stalkClosedPointTo p

  have c1 : alg.comp (ρ.comp φ₁) = constF e C.Y := by rw [← RingHom.comp_assoc, ← halg, hf.2.1]
  have c2 : alg.comp (ρ₁.comp φ₂) = constF e C.Y := by rw [← RingHom.comp_assoc, ← halg₁, hf₁.2.1]
  have hρφ : ρ₁.comp φ₂ = ρ.comp φ₁ := RingHom.ext fun a => hinj
    ((RingHom.congr_fun c2 a).trans (RingHom.congr_fun c1 a).symm)
  have hgen : genericPt C.Y ≫ C.π ≫ genι Z = spMap alg ≫ stalkPt C.Y (p (IsLocalRing.closedPoint k)) ≫ C.π ≫ genι Z := by
    rw [hf.1, halg, ← hxp]
    simp [spMap, Spec.map_comp]
  have hx0 : x = p ≫ C.π ≫ genι Z := by rw [hg₁.1, hp₁, Category.assoc]
  have hxk : x = spMap ψp ≫ stalkPt C.Y (p (IsLocalRing.closedPoint k)) ≫ C.π ≫ genι Z := by
    rw [hx0, ← Category.assoc (spMap ψp), hpp]
  have hxψ : x = spMap ψ ≫ stalkPt C.Y y ≫ C.π ≫ genι Z := by
    rw [hx0, hp, Category.assoc]
  have hφk : φ = ψ.comp φ₁ := by
    rw [hg₁.2.1, hψ₁, hψ, RingHom.comp_assoc, RingHom.comp_assoc, hρφ]

  obtain ⟨f', hf'⟩ := f.exists_isMap ρ (x' := stalkPt C.Y (p (IsLocalRing.closedPoint k)) ≫ C.π ≫ genι Z) rfl
    (by rw [← hxp, Category.assoc])
  obtain ⟨f₁', hf₁'⟩ := f₁.exists_isMap ρ₁ (x' := stalkPt C.Y (p (IsLocalRing.closedPoint k)) ≫ C.π ≫ genι Z) hρφ.symm
    (by rw [← hxp₁, Category.assoc])
  obtain ⟨fF, hfF⟩ := f'.exists_isMap alg c1.symm hgen
  obtain ⟨f₁F, hf₁F⟩ := f₁'.exists_isMap alg c1.symm hgen
  obtain ⟨fk, hfk⟩ := f.exists_isMap ψ hφk hxψ
  obtain ⟨f₁k, hf₁k⟩ := f₁.exists_isMap ψ₁ hg₁.2.1 hg₁.1
  have iF : (_root_.GlobalTheory.ShFam.EigFrame.IsMap f) (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) fF := fun τ i => by
    rw [hfF τ i, hf' τ i, ← Category.assoc (spMap (Formalism.L2.Pj.dualMap alg)), ← spMap_dualMap_comp, ← halg]
  have i₁F : f₁.IsMap (algebraMap (C.Y.X.presheaf.stalk y₁) C.Y.X.functionField) f₁F := fun τ i => by
    rw [hf₁F τ i, hf₁' τ i, ← Category.assoc (spMap (Formalism.L2.Pj.dualMap alg)), ← spMap_dualMap_comp, ← halg₁]
  have ik : f'.IsMap ψp fk := fun τ i => by
    rw [hfk τ i, hf' τ i, ← Category.assoc (spMap (Formalism.L2.Pj.dualMap ψp)), ← spMap_dualMap_comp, ← hψ]
  have i₁k : f₁'.IsMap ψp f₁k := fun τ i => by
    rw [hf₁k τ i, hf₁' τ i, ← Category.assoc (spMap (Formalism.L2.Pj.dualMap ψp)), ← spMap_dualMap_comp, ← hψ₁]

  have key : ∀ τ, (fk.co g τ).BlockTriangular id ∧ ∀ i, IsUnit (fk.co g τ i i) := by
    intro τ
    have hU := EigFrame.Tri.co (τ := τ) hf iF
    have hU₁ := EigFrame.Tri.co (τ := τ) hf₁ i₁F
    have hU₁t : (f₁F.co C.f0 τ).BlockTriangular id := fun a i h => hU₁.1 a i h
    have hU₁d : IsUnit (f₁F.co C.f0 τ).det := f₁F.isUnit_det_co C.f0 τ
    have hW : fF.co f₁F τ = fF.co C.f0 τ * (f₁F.co C.f0 τ)⁻¹ := by
      rw [← fF.co_mul f₁F C.f0 τ, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU₁d, Matrix.mul_one]
    have hWt : (fF.co f₁F τ).BlockTriangular id := by
      haveI := Matrix.invertibleOfIsUnitDet _ hU₁d
      rw [hW]
      exact Matrix.BlockTriangular.mul (fun a i h => hU.1 a i h) (Matrix.blockTriangular_inv_of_blockTriangular hU₁t)
    have hM : fF.co f₁F τ = (f'.co f₁' τ).map alg := EigFrame.IsMap.co τ hfF hf₁F hgen
    have hMt : (f'.co f₁' τ).BlockTriangular id := fun a i h => hinj (by
      have := hWt h
      rw [hM, Matrix.map_apply] at this
      rw [this, map_zero])
    have hMu : ∀ i, IsUnit (f'.co f₁' τ i i) := isUnit_diag_of_blockTriangular hMt (f'.isUnit_det_co f₁' τ)
    have hN := EigFrame.Tri.co (τ := τ) hg₁ hf₁k
    have hNt : (f₁k.co g τ).BlockTriangular id := fun a i h => hN.1 a i h
    have hMk : fk.co f₁k τ = (f'.co f₁' τ).map ψp := EigFrame.IsMap.co τ ik i₁k hxk
    have hMkt : (fk.co f₁k τ).BlockTriangular id := fun a i h => by
      rw [hMk, Matrix.map_apply, hMt h, map_zero]
    have hQ : fk.co g τ = fk.co f₁k τ * f₁k.co g τ := (fk.co_mul f₁k g τ).symm
    refine ⟨hQ ▸ hMkt.mul hNt, fun i => ?_⟩
    rw [hQ, diag_mul_of_blockTriangular hMkt hNt, hMk, Matrix.map_apply, hN.2 i]
    exact ((hMu i).map ψp).mul (Units.isUnit _)
  refine ⟨fun τ i => ((key τ).2 i).unit, hxψ, hφk, fun τ i => ⟨fun a => fk.co g τ a i, ((key τ).2 i).unit_spec.symm,
    fun a ha => (key τ).1 ha, ?_⟩⟩
  rw [← funext (hfk τ)]
  exact fk.co_spec g τ i

end GlobalTheory.ShFam.CarriesAt
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.Rw

theorem exists_realDat_keep_rsideW : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) →
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      Formalism.L2.Pj.LawsCore core'.toCore → core'.Q.Canon → (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) → core'.pb = f'.P.pb →
      letI := alg'; ∃ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr₀ : TrI B' w'.px)
        (R₀ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀) core'.Q.c.F)
        (cG : G0 R₀.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R₀.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R₀.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R₀.eG.trans cG) Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R₀.mu R₀.twPl ∧
        IdemClass (D := (w'.st Z').toD7) (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).A ∧ R₀.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 ∧ R₀.IsInert ∧ R₀.IsTup ∧
        R₀.AllPlaces ∧ Keep R₀.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 cG ∧ BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀ R₀.toRealDat ∧
        RSideW z {v | B'.places.resChar v ∈ T'.pl} R₀) := by
  intro p1 p2 p3 p4 p5 p6 p7
  refine StepW.trans (StepW.and (GlobalTheory.T.exists_firstAnalyticData_enlargedColumnChoices p1 p2 p3 p4 p5 p6 p7) (GlobalTheory.T.reset_tuple_free_fields_keeps_clauses_comparison p1 p2 p3 p4 p5 p6 p7)) (StepW.of_all fun K B' f' T' w' _ _ H => ?_)
  intro B f T w e hf hp hpx Z hX Wt z g1 g2 fz hl Z' hX' g3 g4 vt core' alg' a1 a2 a3 hq lc cn dw pb
  obtain ⟨Xg, tr₀, R₀, cG, hc⟩ := H.1 B f T w e hf hp hpx Z hX Wt z g1 g2 fz hl Z' hX' g3 g4 vt core' alg' a1 a2 a3 hq lc cn dw pb
  obtain ⟨R₁, cG₁, hc1⟩ := H.2 B f T w e hf hp hpx Z hX Wt z g1 g2 fz hl Z' hX' g3 g4 vt core' alg' a1 a2 a3 hq lc cn dw pb Xg tr₀ R₀ cG hc
  exact ⟨Xg, tr₀, R₁, cG₁, hc1⟩

end GlobalTheory.Mem.R3.Rw

end
end
