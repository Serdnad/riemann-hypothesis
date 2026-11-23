module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetOfMemNhds
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentOfCutSec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLieEigenpartsFrameFamilyOverVariety
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle690
public import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiCoordinatesFourthPowerAssociated
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle206
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase


attribute [local instance] Over.cartesianMonoidalCategory in
theorem isCombAtG_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}
    {t : SAB H X0} {R : Type} [CommRing R] {x0 : Sp R ⟶ X0} {m : ℕ} {v : Fin m → (Sp (DualNumber R) ⟶ t.G.left)}
    {cf : Fin m → R} {w w' : Sp (DualNumber R) ⟶ t.G.left} (h : IsCombAtG t x0 v cf w)
    (h' : IsCombAtG t x0 v cf w') : w = w' := by
  obtain ⟨u, hu, rfl⟩ := h
  obtain ⟨u', hu', rfl⟩ := h'
  have : u = u' := funext fun k => Over.OverMorphism.ext ((hu k).trans (hu' k).symm)
  rw [this]

theorem frameAt_v_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (X : Var F) (j : X.X ⟶ gen Z) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (A₀ A : Mat Dw.mult X.Fn) (y : CxPts X.str (σ.comp e.toRingHom)) (x x' : Sp ℂ ⟶ Z.X) (g : EigFrame Z σ x) (g' : EigFrame Z σ x'), FrameAt e f₀ A₀ A y g → FrameAt e f₀ A₀ A y g' → ∀ τ i, g.v τ i = g'.v τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ X j f₀ A₀ A y x x' g g' h h' τ i
  obtain ⟨φ, fz, ψ, hy, hc, hg⟩ := h
  obtain ⟨φ', fz', ψ', hy', hc', hg'⟩ := h'
  have hψ : ψ = ψ' := EigLoc.spMap_inj ((cancel_mono (X.X.fromSpecStalk (under y))).1 (hy.symm.trans hy'))
  subst hψ
  have hι := IsFractionRing.injective (X.X.presheaf.stalk (under y)) X.X.functionField
  obtain rfl : φ = φ' := RingHom.ext fun a => hι ((RingHom.congr_fun hc.2.1 a).symm.trans (RingHom.congr_fun hc'.2.1 a))
  obtain ⟨fK, hK⟩ := fz.exists_isMap _ hc.2.1 hc.1
  obtain ⟨fK', hK'⟩ := fz'.exists_isMap _ hc.2.1 hc.1
  have e1 : fK.co f₀ τ = fK'.co f₀ τ := by
    rw [EigFrame.co_eq (T := Matrix.of fun a k => (A₀ * A⁻¹) τ k a) fun k => by
        rw [funext (hK τ)]; exact hc.2.2 τ k,
      EigFrame.co_eq (T := Matrix.of fun a k => (A₀ * A⁻¹) τ k a) fun k => by
        rw [funext (hK' τ)]; exact hc'.2.2 τ k]
  have e2 : fK.co fK' τ = 1 := by
    rw [← fK.co_mul f₀ fK' τ, e1, fK'.co_mul, fK'.co_self]
  have e3 : fz.co fz' τ = 1 := by
    have e := (hK.co τ hK' hc.1).symm.trans e2
    ext a b
    have e' := congrFun (congrFun e a) b
    rw [Matrix.map_apply] at e'
    apply hι
    rw [e', Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have e4 := fz.co_spec fz' τ i
  rw [e3] at e4
  have e5 : fz'.v τ i = fz.v τ i := isCombAtG_eq e4 (by
    convert isCombAtG_single Z.t _ (fz.tan τ) i using 2
    simp only [Matrix.one_apply, Pi.single_apply])
  rw [hg τ i, hg' τ i, e5]

end GlobalTheory.LieBase
end
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

namespace GlobalTheory.FlagBaseDim

theorem dims : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → (Φ.C k).Y.dim = Fintype.card (GlobalTheory.AllWt.Psi H) * ((Dw.p + Dw.q) * (Dw.p + Dw.q - 1) / 2) ∧ X.dim = Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U _ _ Φ k X j f f₀ Eb A₀ _ hL
  have hcard : Fintype.card (GlobalTheory.AllWt.Psi H) = Module.finrank ℚ E / 2 := by
    rw [← Nat.card_eq_fintype_card]; exact GlobalTheory.PeriodCoord.card_cmType H
  refine ⟨by rw [Φ.dim_eq k, hcard], ?_⟩
  obtain ⟨hj', -, -⟩ := hL
  obtain ⟨Uo, hUo, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.X.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top (genericPoint X.X))
  have h1 := GlobalTheory.SmoothDim.ringKrullDim_affineOpen F X.X X.str X.dim inferInstance Uo hUo ⟨_, hx⟩
  have h2 := GlobalTheory.SmoothDim.ringKrullDim_affineOpen c.F (gen T.Z) (genStr T.Z) Dw.dim T.smooth (j ''ᵁ Uo)
    (hUo.image_of_isOpenImmersion j) ⟨j (genericPoint X.X), ⟨_, hx, rfl⟩⟩
  rw [ringKrullDim_eq_of_ringEquiv (j.appIso Uo).commRingCatIsoToRingEquiv, h1] at h2
  have hd : X.dim = Dw.dim := by exact_mod_cast h2
  rw [hd, Datum.dim, hcard, mul_assoc]

end GlobalTheory.FlagBaseDim
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

namespace GlobalTheory.OpenBaseDim

theorem dim_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z), IsOpenImmersion j → ∀ (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), (∃ y, y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j)) → ∀ k : U.Comp, X.dim = (U.X k).Ψ.card * (Dw.p * Dw.q) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U _ _ X j hoi _ _ k
  haveI := hoi
  have hcard : (U.X k).Ψ.card = Module.finrank ℚ E / 2 := by
    rw [← Fintype.card_coe]; exact ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms.card_Psi (U.X k)
  obtain ⟨Uo, hUo, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.X.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top (genericPoint X.X))
  have h1 := GlobalTheory.SmoothDim.ringKrullDim_affineOpen F X.X X.str X.dim inferInstance Uo hUo ⟨_, hx⟩
  have h2 := GlobalTheory.SmoothDim.ringKrullDim_affineOpen c.F (gen T.Z) (genStr T.Z) Dw.dim T.smooth (j ''ᵁ Uo)
    (hUo.image_of_isOpenImmersion j) ⟨j (genericPoint X.X), ⟨_, hx, rfl⟩⟩
  rw [ringKrullDim_eq_of_ringEquiv (j.appIso Uo).commRingCatIsoToRingEquiv, h1] at h2
  have hd : X.dim = Dw.dim := by exact_mod_cast h2
  rw [hd, Datum.dim, hcard, mul_assoc]

end GlobalTheory.OpenBaseDim
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.FlagBundle GlobalTheory.ShFam GlobalTheory.CxPts GlobalTheory.ProjVar

namespace GlobalTheory.LieBase

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {σ : c.F →+* ℂ}


open Classical in
def gramOf (e : F ≃+* c.F) (G : EigMet Z σ) {X : Var F} {j : X.X ⟶ gen Z}
    (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z))
    (A₀ A : Mat Dw.mult X.Fn) (y : CxPts X.str (σ.comp e.toRingHom)) : Mat Dw.mult ℂ :=
  if h : ∃ g : EigFrame Z σ ((cxOf e σ hj y).1 ≫ genι Z), FrameAt e f₀ A₀ A y g then
    fun τ => (G.gram (cxOf e σ hj y) h.choose τ)ᵀ
  else 0

theorem lieGram_eq_gramOf (e : F ≃+* c.F) {r : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ r) {X : Var F} {j : X.X ⟶ gen Z}
    (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z))
    (A₀ : Mat Dw.mult X.Fn) : lieGram e U hj f₀ A₀ = gramOf e (hodgeMet Z U) hj f₀ A₀ := rfl

end GlobalTheory.LieBase
end
end

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase GlobalTheory.CxPts GlobalTheory.Cartier
open Filter Topology
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase.ChartCoords

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem co_congr {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} {f f' g : EigFrame Z φ x}
    (h : ∀ τ i, f'.v τ i = f.v τ i) (τ : E →+* ℂ) : f'.co g τ = f.co g τ :=
  EigFrame.co_eq fun i => by rw [funext (h τ)]; exact f.co_spec g τ i

theorem v_of_isMap_trans {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] {φ : c.F →+* R}
    {x : Sp R ⟶ Z.X} {φ₁ : c.F →+* R₁} {x₁ : Sp R₁ ⟶ Z.X} {φ₂ : c.F →+* R₂} {x₂ : Sp R₂ ⟶ Z.X}
    {f : EigFrame Z φ x} {f₁ : EigFrame Z φ₁ x₁} {f₂ f₂' : EigFrame Z φ₂ x₂} {ψ₁ : R →+* R₁} {ψ₂ : R₁ →+* R₂}
    {ψ : R →+* R₂} (h₁ : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f embτ basisIdx) ψ₁ f₁) (h₂ : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f₁ embτ basisIdx) ψ₂ f₂) (h : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f embτ basisIdx) ψ f₂') (hψ : ψ₂.comp ψ₁ = ψ)
    (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) : f₂.v τ i = f₂'.v τ i := by
  rw [h₂ τ i, h₁ τ i, GlobalTheory.GradedPieces.dual_comp, hψ, h τ i]

end GlobalTheory.LieBase.ChartCoords

open GlobalTheory.ProjVar.Var GlobalTheory.LieBase.ChartCoords

theorem GlobalTheory.LieBase.coords_eq_ratVal_of_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (F : Type) [Field F] (e : F ≃+* c.F) (X : Var F) (j : X.X ⟶ gen Z) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (S : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ S A₀ → ∀ (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (Φ : EigFrame Z φ (LogKS.chart V ≫ genι Z)), LogKS.chart V ≫ genStr Z = spMap φ → ∀ A : Mat Dw.mult X.Fn, ∃ M : Mat Dw.mult X.Fn, ∀ z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom), A ∈ S.S (under z) → ∀ hz : cxOf e σ hj z ∈ ptsIn (genStr Z) σ V.1, (∀ τ p q, RegAt (under z) (M τ p q)) ∧ (∃ g : EigFrame Z σ ((cxOf e σ hj z).1 ≫ genι Z), FrameAt e f₀ A₀ A z g) ∧ ∀ g : EigFrame Z σ ((cxOf e σ hj z).1 ≫ genι Z), FrameAt e f₀ A₀ A z g → ∀ f : EigFrame Z σ ((cxOf e σ hj z).1 ≫ genι Z), (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v Φ embτ basisIdx) (evHom hz) f → ∀ τ, f.co g τ = (M τ).map (fun r => ratVal r z) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ F _ e X j f₀ S A₀ hj _hoi hT V φ Φ hV A
  classical
  have hVa : IsAffineOpen V.1 := V.2
  haveI : Mono (LogKS.chart V) := inferInstanceAs (Mono hVa.fromSpec)
  have hmem : ∀ z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom), cxOf e σ hj z ∈ ptsIn (genStr Z) σ V.1 →
      under z ∈ j ⁻¹ᵁ V.1 := fun z hz => mem_ptsIn.1 hz
  by_cases hη : genericPoint X.X ∈ j ⁻¹ᵁ V.1
  swap
  · exact ⟨0, fun z _ hz => absurd (gen_mem (hmem z hz)) hη⟩
  have key : ∀ x : X.X, x ∈ j ⁻¹ᵁ V.1 → ∃ ψ : Γ(gen Z, V.1) →+* X.X.presheaf.stalk x,
      spMap ψ ≫ LogKS.chart V = stalkPt X x ≫ j := fun x hx =>
    TieBase.exists_affine_factor _ V.2 (by
      show j (X.X.fromSpecStalk x (IsLocalRing.closedPoint _)) ∈ V.1
      rw [Scheme.fromSpecStalk_closedPoint]; exact hx)
  have key' : ∀ (x : X.X) (ψ : Γ(gen Z, V.1) →+* X.X.presheaf.stalk x), spMap ψ ≫ LogKS.chart V = stalkPt X x ≫ j →
      spMap ((algebraMap (X.X.presheaf.stalk x) X.X.functionField).comp ψ) ≫ LogKS.chart V = genericPt X ≫ j :=
    fun x ψ h => by rw [TieBase.spMap_trans, Category.assoc, h, TieBase.genericPt_eq X x, Category.assoc]
  obtain ⟨ψη, hψη⟩ := key _ hη
  obtain ⟨ρ, h₀⟩ : ∃ ρ : Γ(gen Z, V.1) →+* X.X.functionField, spMap ρ ≫ LogKS.chart V = genericPt X ≫ j :=
    ⟨_, key' _ ψη hψη⟩
  have hφK : constF e X = ρ.comp φ := EigLoc.spMap_inj (by
    rw [← TieBase.genericPt_str e X j hj, ← h₀, Category.assoc, hV, ← TieBase.spMap_trans])
  obtain ⟨ΦK, hΦK⟩ := Φ.exists_isMap ρ hφK (x' := genericPt X ≫ j ≫ genι Z)
    (by rw [← Category.assoc, ← h₀, Category.assoc])
  refine ⟨fun τ => ΦK.co f₀ τ * (((A₀ * A⁻¹) τ)ᵀ)⁻¹, fun z hA hz => ?_⟩
  have hx := hmem z hz
  obtain ⟨φx, fz, hc⟩ := hT.2 (under z) A hA
  obtain ⟨ψx, hψx⟩ := key _ hx
  have hρx : (algebraMap _ X.X.functionField).comp ψx = ρ :=
    EigLoc.spMap_inj ((cancel_mono (LogKS.chart V)).1 ((key' _ ψx hψx).trans h₀.symm))
  have hφx : φx = ψx.comp φ := RingHom.ext fun a => IsFractionRing.injective (X.X.presheaf.stalk (under z))
    X.X.functionField (by
      have h1 := RingHom.congr_fun hc.2.1 a
      have h2 := RingHom.congr_fun hφK a
      rw [← hρx] at h2
      exact h1.symm.trans h2)
  obtain ⟨Φx, hΦx⟩ := Φ.exists_isMap ψx hφx (x' := stalkPt X (under z) ≫ j ≫ genι Z)
    (by rw [← Category.assoc, ← hψx, Category.assoc])
  have hM : ∀ fz' : EigFrame Z φx (stalkPt X (under z) ≫ j ≫ genι Z),
      fz'.Coord (algebraMap (X.X.presheaf.stalk (under z)) X.X.functionField) f₀ (A₀ * A⁻¹) → ∀ τ,
      ΦK.co f₀ τ * (((A₀ * A⁻¹) τ)ᵀ)⁻¹ = (Φx.co fz' τ).map (algebraMap _ X.X.functionField) := by
    intro fz' hc' τ
    obtain ⟨k, hk⟩ := fz'.exists_isMap _ hc'.2.1 hc'.1
    obtain ⟨Φk, hΦk⟩ := Φx.exists_isMap _ hc'.2.1 hc'.1
    have h1 : k.co f₀ τ = ((A₀ * A⁻¹) τ)ᵀ := EigFrame.co_eq fun i => by rw [funext (hk τ)]; exact hc'.2.2 τ i
    have h3 : Φk.co k τ = (Φx.co fz' τ).map (algebraMap _ X.X.functionField) := hΦk.co τ hk hc'.1
    have h4 : Φk.co f₀ τ = ΦK.co f₀ τ := co_congr (v_of_isMap_trans hΦx hΦk hΦK hρx) τ
    have h5 : f₀.co k τ = (k.co f₀ τ)⁻¹ := (Matrix.inv_eq_right_inv ((k.co_mul f₀ k τ).trans (k.co_self τ))).symm
    rw [← h3, ← Φk.co_mul f₀ k τ, h4, h5, h1]
  have hs : spMap (Scheme.stalkClosedPointTo z.1).hom ≫ stalkPt X (under z) = z.1 :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk z.1
  have hxz : (cxOf e σ hj z).1 ≫ genι Z = spMap (Scheme.stalkClosedPointTo z.1).hom ≫ stalkPt X (under z) ≫ j ≫ genι Z := by
    show (z.1 ≫ j) ≫ genι Z = _
    conv_lhs => rw [← hs]
    simp only [Category.assoc]
  refine ⟨fun τ p q => ?_, ?_, ?_⟩
  · beta_reduce
    rw [hM fz hc τ]
    exact ⟨Φx.co fz τ p q, rfl⟩
  · have hφ : σ = (Scheme.stalkClosedPointTo z.1).hom.comp φx := RingHom.ext fun a => by
      have h3 : φx a = algebraMap F _ (e.symm a) := IsFractionRing.injective _ X.X.functionField
        ((RingHom.congr_fun hc.2.1 a).symm.trans ((X.stalkIncl (under z)).commutes _).symm)
      show σ a = evStalk z (φx a)
      rw [h3]
      refine Eq.trans ?_ ((evStalk_germ (U := ⊤) trivial _).trans (ev_algX mem_ptsIn_top _)).symm
      simp
    obtain ⟨g, hg⟩ := fz.exists_isMap _ hφ hxz
    exact ⟨g, φx, fz, _, (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z.1).symm, hc, hg⟩
  · rintro g ⟨φ', fz', ψ', hψ', hc', hm'⟩ f hf τ
    obtain rfl : ψ' = (Scheme.stalkClosedPointTo z.1).hom :=
      EigLoc.spMap_inj ((cancel_mono (X.X.fromSpecStalk (under z))).1
        (hψ'.symm.trans (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z.1).symm))
    obtain rfl : φ' = φx := RingHom.ext fun a => IsFractionRing.injective _ X.X.functionField
      ((RingHom.congr_fun hc'.2.1 a).symm.trans (RingHom.congr_fun hc.2.1 a))
    have hev : (Scheme.stalkClosedPointTo z.1).hom.comp ψx = evHom hz :=
      EigLoc.spMap_inj ((cancel_mono (LogKS.chart V)).1 (by
        rw [TieBase.spMap_trans, Category.assoc, hψx, LieMet.spMap_evHom hz, ← Category.assoc, hs]
        rfl))
    have hfx : Φx.IsMap (Scheme.stalkClosedPointTo z.1).hom f := fun τ i => by
      rw [hf τ i, hΦx τ i, GlobalTheory.GradedPieces.dual_comp, hev]
    beta_reduce
    rw [hfx.co τ hm' hxz, hM fz' hc' τ]
    refine Matrix.ext fun a b => ?_
    simp only [Matrix.map_apply]
    rw [GlobalTheory.TrueGeo.Res.ratVal_eq_valAt z ⟨_, rfl⟩, GlobalTheory.TrueGeo.Res.valAt_algebraMap]
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.rigidified_symmetric_lineBundle_groupPullback : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] (B : Over S') [GrpObj B] (β : B.left ⟶ G.left), IsGrpPullback B G f β → ∀ (L : RigLB G) (σ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(GrpObj.inv : G ⟶ G).left, 𝟙 G.left] ![1, -1])), σ.IsGen → Rigidified B (L.L.pull β) ∧ Out.Sym B (L.L.pull β) := by
  first | exact @GlobalTheory.RigSymBaseChange.rigidified_and_sym_pull | exact GlobalTheory.RigSymBaseChange.rigidified_and_sym_pull | (intros; apply GlobalTheory.RigSymBaseChange.rigidified_and_sym_pull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.weightTwoFactor_sq_values_correspond : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], ∀ (D D' : DegData R (maximalIdeal R)), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), IsMonHom Φ.hom → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x))) → ∀ (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ (mu α : D.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D.toPre.P.A) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → sval (f (α + 2 • mu)) y.left z J = sval (f α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D.toPre (FractionRing R) 2 α (ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D.toPre (FractionRing R) 2 mu α) κ.left z J).val) → (∀ (mu α : D'.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D'.toPre.P.A) (z : T.left) (J : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D'.toPre.P.L z J → sval (f' (α + 2 • mu)) y.left z J = sval (f' α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D'.toPre (FractionRing R) 2 α (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D'.toPre (FractionRing R) 2 mu α) κ.left z J).val) → (∀ (β : D'.toPre.X) (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → sval (f (xe (2 • β))) (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB (2 • β) κ) ^ DegPre.famε 2 κ).val * sval (f' (2 • β)) ρ z J' ^ 2) → (∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → ∀ (Ω : (T ⟶ D'.toPre.P.A) → (T.left.presheaf.stalk z)ˣ), Ω = (fun x => ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) x.left) → ∀ (a b c : T ⟶ D'.toPre.P.A), cubV D.toPre.cub z J (a ≫ Φ.hom) (b ≫ Φ.hom) (c ≫ Φ.hom) ^ 2 = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ * cubV D'.toPre.cub z J' a b c ^ 2) → ∀ (y : D'.toPre.X) (z : (DegPre.BF D.toPre (FractionRing R)).left) (J : ((DegPre.BF D.toPre (FractionRing R)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((DegPre.BF D.toPre (FractionRing R)).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → IsDomain ((DegPre.BF D.toPre (FractionRing R)).left.presheaf.stalk z) → sval (f 0) (DegPre.prB D.toPre (FractionRing R)).left z J ≠ 0 → val (DegPre.famMult D'.toPre (FractionRing R) 2 (2 • y) 0) (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z J' ^ 2 = (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) (2 • y)).left * (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (1 : (DegPre.BF D.toPre (FractionRing R)) ⟶ D'.toPre.P.A).left)⁻¹) ^ 2 * val (DegPre.famMult D.toPre (FractionRing R) 2 (xe (2 • y)) 0) (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z J ^ 2 := by
  first | exact @GlobalTheory.PsiCompare.famMult_sq_corr | exact GlobalTheory.PsiCompare.famMult_sq_corr | (intros; apply GlobalTheory.PsiCompare.famMult_sq_corr <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.psi_coordinates_fourthPower_associated : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D D' : DegData R (maximalIdeal R)) (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → ∀ (nu : D.toPre.X) (mu : D'.toPre.X) (z : (DegPre.BF D.toPre (FractionRing R)).left), (∀ (J : ((DegPre.BF D.toPre (FractionRing R)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((DegPre.BF D.toPre (FractionRing R)).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → val (DegPre.famMult D'.toPre (FractionRing R) 2 (mu) 0) (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z J' ^ 2 = (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) (mu)).left * (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (1 : (DegPre.BF D.toPre (FractionRing R)) ⟶ D'.toPre.P.A).left)⁻¹) ^ 2 * val (DegPre.famMult D.toPre (FractionRing R) 2 (nu) 0) (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z J ^ 2) → ∀ (r r' : R), PsiCoord D.toPre nu r → PsiCoord D'.toPre mu r' → Associated (r ^ 4) (r' ^ 4) := by
  first | exact @GlobalTheory.psi_coord_fourth_associated | exact GlobalTheory.psi_coord_fourth_associated | (intros; apply GlobalTheory.psi_coord_fourth_associated <;> assumption)
end
