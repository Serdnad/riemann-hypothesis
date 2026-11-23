module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationAdjointEndomorphismsCommute
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3318
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3313
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3314
public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2817
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2648
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2649
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1637
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1823
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle935
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3081
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1653
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle048
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

open GlobalTheory.TorusExt GlobalTheory.Balanced

attribute [local instance] gtGroup



theorem pull_unif_tors : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (J : Ideal R), AdmBase R J → ∀ (D₀ : DegData R J) (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (U₀ : Unif J D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f : R →+* V, Function.Injective f → J.map f ≤ maximalIdeal V → ∃ (D : DegData V (maximalIdeal V)) (hD : IsPullDeg f D₀.toPre D.toPre) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A ((Over.pullback (specOf f)).obj G₀)), IsSemiAbelian ((Over.pullback (specOf f)).obj G₀) ∧ IsPullUnif f hD (Iso.refl _) U₀ U ∧ ∀ (F₀ : Type) [Field F₀] [IsAlgClosed F₀] [Algebra (FractionRing R) F₀] (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (j : F₀ →+* F), Ext f j → ∀ k : ℕ, 1 ≤ k → ∀ (p₀ : QkPt D₀.toPre F₀ k) (x₀ : TFK (R := R) F₀ ⟶ A₀.A), QkToAkU U₀.toUnifPre F₀ k p₀ x₀ → ∃ (p : QkPt D.toPre F k) (x : TFK (R := V) F ⟶ A.A), p.y = hD.xe.symm p₀.y ∧ Tr f hD j p₀.g p.g ∧ QkToAkU U.toUnifPre F k p x ∧ x.left ≫ U.gen.inv.left ≫ pullback.fst ((Over.pullback (specOf f)).obj G₀).hom (jK V) ≫ pullback.fst G₀.hom (specOf f) = spMap j ≫ x₀.left ≫ U₀.gen.inv.left ≫ pullback.fst G₀.hom (jK R) := by
  intro R _ _ _ J hR D₀ A₀ G₀ _ _ U₀ hG V _ _ _ _ hV f hf hJ
  have hL := GlobalTheory.firstFiveLaws
  have hR' : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  obtain ⟨D, hD, A, U, hG', hU, hpt, -⟩ := GlobalTheory.T.uniformisation_endomorphisms_to_complete_dvr hL R J hR D₀ A₀ G₀ hG U₀ V f hV hf hJ
  refine ⟨D, hD, A, U, hG', hU, ?_⟩
  intro F₀ _ _ _ F _ _ _ j hj k hk p₀ x₀ hx₀
  letI : Algebra (FractionRing R) F := (j.comp (algebraMap (FractionRing R) F₀)).toAlgebra
  let σ : F₀ →ₐ[FractionRing R] F := { j with commutes' := fun _ => rfl }
  have hB := D₀.tau_bimult
  have hF : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) =
      algebraMap (FractionRing V) F (algebraMap V _ (f r)) := hj
  obtain ⟨p₁, hp₁⟩ := qkExtExists R D₀.toPre F₀ F σ.toRingHom (fun r => σ.commutes r) k p₀
  let x₁ : TFK (R := R) F ⟶ A₀.A := extPt σ x₀
  have hx₁ : QkToAkU U₀.toUnifPre F k p₁ x₁ := (GlobalTheory.T.qkToAkU_iff_galois_equivariant hL R J hR D₀ A₀ G₀ hG U₀ F₀ F σ k hk p₀ p₁ x₀ x₁
    hp₁ rfl).1 hx₀
  obtain ⟨ex, -, io, ns⟩ := hpt F hF
  obtain ⟨g, hg, -⟩ := ex p₁.g
  let p : QkPt D.toPre F k := ⟨hD.xe.symm p₁.y, g, by
    obtain ⟨s, h1, h2⟩ := p₁.eq
    obtain ⟨s', hs', -⟩ := ex s
    exact ⟨s', (ns k _ _ _ _ hg hs').1 h1, (io _ _ _ hs').1 (by rwa [AddEquiv.apply_symm_apply])⟩⟩
  obtain ⟨x, hx⟩ := exists_toG_pull f U₀.toUnifPre U.toUnifPre hF x₁
  refine ⟨p, x, by simpa [p, hp₁.1], ⟨p₁.g, hp₁.2, hg⟩, ?_, ?_⟩
  · exact hL.2.2.2.2.qkBaseChange R V J _ hR hR' f D₀ A₀ G₀ U₀ _ (Iso.refl _) (inferInstanceAs (IsMonHom (𝟙 _))) A D
      hD U hU F hF k hk p₁ x₁ p x rfl hg
      (by simpa only [toG, Category.assoc, Iso.refl_hom, Over.id_left, Category.id_comp] using hx) hx₁
  · simpa only [toG, Category.assoc, x₁, extPt, Over.homMk_left] using hx

end GlobalTheory.TInj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.base_rigidity_tangent_vector_constant : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (k : Type) [Field k] (ρ : R →+* DualNumber k) (a : Fin C.m → k), GlobalTheory.RigChart.IsConstAlong C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) ρ a → ρ.comp (Cn.ψ.comp MvPolynomial.C) = GlobalTheory.RigChart.constHom (ρ.comp (Cn.ψ.comp MvPolynomial.C)) := by
  first | exact @GlobalTheory.RigBase.const_on_base | exact GlobalTheory.RigBase.const_on_base | (intros; apply GlobalTheory.RigBase.const_on_base <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.canonicalFamily_has_pointRigid_coordinates : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), HasRigidCoords C := by
  first | exact @GlobalTheory.UCanon.canon_hasRigidCoords | exact GlobalTheory.UCanon.canon_hasRigidCoords | (intros; apply GlobalTheory.UCanon.canon_hasRigidCoords <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianVarietyEndCharpoly_spec : ∀ (K : Type) [Field K] (A : AbVar K) (f : End A), IsCharpoly f (charpoly f) ∧ ∀ P, IsCharpoly f P → P = charpoly f := by
  first | (exact @GlobalTheory.AV.AbVar.charpoly_spec) | (exact GlobalTheory.AV.AbVar.charpoly_spec) | (intros; apply GlobalTheory.AV.AbVar.charpoly_spec  <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.end_isogeny_algebra_finite_finrank_le : ∀ (K : Type) [Field K] (A : AbVar K), Module.Finite ℚ (End0 A) ∧ Module.finrank ℚ (End0 A) ≤ 4 * A.dim * A.dim := by
  first | (exact @GlobalTheory.AV.AbVar.end_isogeny_algebra_finrank_le) | (exact GlobalTheory.AV.AbVar.end_isogeny_algebra_finrank_le) | (intros; apply GlobalTheory.AV.AbVar.end_isogeny_algebra_finrank_le  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical


theorem _root_.GlobalTheory.T.unitary_classical_trait_periods_bounded_below : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X' : USetup C) (p : ℕ) [Fact p.Prime], ∃ K : ℝ, ∀ (z' : X'.M.Z), IsClosed ({z'} : Set X'.M.Z) → ∀ t : UCTrait X' p z', X'.S.R ≤ X'.M.O ((gPt p ≫ t.y) (IsLocalRing.closedPoint (PadicAlgCl p))) → ∀ x : t.T.P.D.toPre.X, x ≠ 0 → ∃ h ∈ maximalIdeal (X'.M.Z.presheaf.stalk z'), Real.exp (-(K * (t.sc * t.T.be x x))) ≤ ‖t.val h‖ := by
  first | exact @GlobalTheory.UPoinc.ShortBound.main | exact GlobalTheory.UPoinc.ShortBound.main | (intros; apply GlobalTheory.UPoinc.ShortBound.main <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.translation_horizontal_of_commuting_heatOperators : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r)))  → ∀ (B' : Over (Sp (DualNumber k))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (y : P.D.toPre.X) (x : Sp (DualNumber k) ⟶ B'.left), x ≫ B'.hom = 𝟙 _ → x ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left → x ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left := by
  first | exact @GlobalTheory.PtsHoriz.transl_horizontal | exact GlobalTheory.PtsHoriz.transl_horizontal | (intros; apply GlobalTheory.PtsHoriz.transl_horizontal <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.heatOperator_symbol_unique_principalPolarisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (Λ₁ Λ₂ : Matrix (Fin n) (Fin n) (FractionRing Ω)) (d₁ d₂ : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u₁ u₂ : Fin n → (FractionRing Ω)) (p₁ p₁' p₂ p₂' : (FractionRing Ω)), Λ₁ᵀ = Λ₁ → Λ₂ᵀ = Λ₂ → (∀ r, d₁ ((algebraMap Ω (FractionRing Ω)) (φ r)) = d₂ ((algebraMap Ω (FractionRing Ω)) (φ r))) → (∀ (k : ℕ), 1 ≤ k → ∀ s : (FractionRing Ω), (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (s)) → (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (ringOp ⇑d₁ (fun a => ⇑(δL a)) Λ₁ u₁ p₁ p₁' k s))) → (∀ (k : ℕ), 1 ≤ k → ∀ s : (FractionRing Ω), (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (s)) → (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (ringOp ⇑d₂ (fun a => ⇑(δL a)) Λ₂ u₂ p₂ p₂' k s))) → Λ₁ = Λ₂ := by
  first | exact @GlobalTheory.HeatSym.symbol_unique | exact GlobalTheory.HeatSym.symbol_unique | (intros; apply GlobalTheory.HeatSym.symbol_unique <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatDefect

theorem shiftEq_add {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {k : ℕ} {mu α : Q.X}
    {σ σ' σ'' : Q.SecB k α} {σ₁ σ₁' : Q.SecB k (α + k • mu)} {c₁ c₂ : R}
    (h0 : ShiftEq Q k mu α σ σ₁ 0 σ₁) (h1 : ShiftEq Q k mu α σ'' σ₁' c₁ σ₁)
    (h2 : ∀ (T : Over (Sp R)) (x : T ⟶ Q.P.A) z J, Good Q.P.L z J →
      sval σ'' x.left z J = sval σ' x.left z J + gs (𝟙 _) z ⊤ (scal T.hom c₂) * sval σ x.left z J) :
    ShiftEq Q k mu α σ' σ₁' (c₁ + c₂) σ₁ := by
  intro u hu hc z J hJ
  have a := h1 u hu hc z J hJ
  have b := h0 u hu hc z J hJ
  have e := h2 _ (DegPre.trF Q (FractionRing R) mu ≫ DegPre.prB Q (FractionRing R)) z J hJ
  have hz : (𝟙 (DegPre.BF Q (FractionRing R)).left) z ∈ (⊤ : (DegPre.BF Q (FractionRing R)).left.Opens) := trivial
  have g0 : gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom (0 : R)) = 0 := by
    rw [gs_eq _ z ⊤ hz]; simp only [Out.scal, map_zero]
  have gadd : gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom (c₁ + c₂)) =
      gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom c₁) +
        gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom c₂) := by
    rw [← gs_add _ z ⊤ hz]; simp only [Out.scal, map_add (f := _)]
  rw [g0, zero_mul, add_zero] at b
  rw [a, e, gadd]
  linear_combination (-(gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom c₂))) * b

end GlobalTheory.HeatDefect

theorem GlobalTheory.HeatDefect.defect_polynomial : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∀ h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D, IsBasic Y h → ∃ (w : Dd.toPre.X → Dd.toPre.X →+ R) (π π' : Dd.toPre.X → R), HasDefect Y h (fun (k : ℕ) mu α => 2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hv m t gam hm ht D hD h hb
  have hA := fun mu => GlobalTheory.T.exists_conjugate_heatOperator_periodShift R Dd O oa Y n v dd hv m t gam hm ht D hD h hb mu
  choose h' w₁ π₁ π₁' hb' hΘ hu hrel using hA
  have hU := fun mu => GlobalTheory.T.exists_affine_scalar_torusInvariant_heatOperators R Dd.toPre O oa Y n v dd hv D h (h' mu) hb (hb' mu) (hΘ mu).symm (hu mu).symm
  choose ℓ π₂ π₂' hU using hU
  refine ⟨fun mu => w₁ mu + ℓ mu, fun mu => π₁ mu + π₂ mu, fun mu => π₁' mu + π₂' mu, ?_⟩
  intro k mu α σ σ' σ₁ σ₁' hk hs ht₀ ht₁
  obtain ⟨σ'', hσ'', hsh⟩ := hrel mu k α σ σ₁ σ₁' hk hs ht₁
  have key := GlobalTheory.HeatDefect.shiftEq_add hs hsh (hU mu k α σ σ' σ'' ht₀ hσ'')
  refine (congrArg (fun c => ShiftEq Dd.toPre k mu α σ' σ₁' c σ₁) ?_).mpr key
  simp only [AddMonoidHom.add_apply]
  ring
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnitsAlong

theorem alg {G : Type} [CommGroup G] (P T Rg Wy Wyz Wz W0 U2 E Pc Tc Rgc : G) (e : ℕ) (n n' : ℤ)
    (hA : P ^ e * T * Rg ^ e = Wy ^ n * Wyz * Wz⁻¹ * W0 ^ n' * (U2 * E) * Pc ^ e * Tc * Rgc ^ e)
    (hB : P ^ e * 1 * Rg ^ e = Wy ^ n * Wy * W0⁻¹ * W0 ^ n' * U2 * Pc ^ e * 1 * Rgc ^ e) :
    T = Wyz * Wy⁻¹ * Wz⁻¹ * W0 * E * Tc := by
  apply Additive.ofMul.injective
  have hA' := congrArg Additive.ofMul hA
  have hB' := congrArg Additive.ofMul hB
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow, ofMul_one, add_zero] at hA' hB' ⊢
  calc Additive.ofMul T = (e • Additive.ofMul P + Additive.ofMul T + e • Additive.ofMul Rg) -
        (e • Additive.ofMul P + e • Additive.ofMul Rg) := by abel
    _ = _ := by rw [hA', hB']; abel

theorem unitTau_along : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∃ c : ℚ, c ≠ 0 ∧ ∃ w : LB.Iso (P.D.toPre.P.L.pull π₁) (P.D.toPre.P.L.pull π₂), w.IsGen ∧ ∀ y z τ₀, IsUnitTau P.D.toPre (bdParam k m d) gam y z τ₀ → ∀ e : (DualNumber k)ˣ, (e : DualNumber k) = 1 + TrivSqZeroExt.inr (∑ i, (c : k) * MvPowerSeries.constantCoeff (q i) * gam i y z) → ∀ zz J, Good P.D.toPre.P.L zz J → val τ₀ (spMap ρ) zz J = gm (c' (y + z)) zz _ (w.s (fun _ => J (c' (y + z) ≫ π₂), fun _ => J (c' (y + z) ≫ π₁))) * (gm (c' (y)) zz _ (w.s (fun _ => J (c' (y) ≫ π₂), fun _ => J (c' (y) ≫ π₁))))⁻¹ * (gm (c' (z)) zz _ (w.s (fun _ => J (c' (z) ≫ π₂), fun _ => J (c' (z) ≫ π₁))))⁻¹ * gm (c' (0)) zz _ (w.s (fun _ => J (c' (0) ≫ π₂), fun _ => J (c' (0) ≫ π₁))) * gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn e) * val τ₀ (spMap (constHom ρ)) zz J := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab
  intro Y n' v' dd hdd D q hq h hB hdef hΘ ρ hρ B' _ π₁ π₂ c' h₁ h₂ hfib hc'
  obtain ⟨w, hw⟩ := GlobalTheory.ConstDefSym.lbIso_pull_of_const (ChartRing k m d) P.D.toPre k ρ B' inferInstance π₁ π₂ h₁ h₂ hfib
  obtain ⟨lam, hlam⟩ := GlobalTheory.T.unitPart_psi_tau_tangent_vector_variation E H k m d t P gam hmon hli hab Y n' v' dd hdd D q hq h hB hdef hΘ ρ hρ B' π₁ π₂ c' h₁ h₂ hfib hc' w hw
  refine ⟨-1, by norm_num, w, hw, ?_⟩
  intro y z τ₀ hτ ee hee zz J hJ
  obtain ⟨n, ψ₀, hψ⟩ := GlobalTheory.UnitPart.exists_isUnitPart P.D.toPre (bdParam k m d) gam hmon y
  obtain ⟨τ₁, hτ₁, hv₁⟩ := GlobalTheory.T.exists_unitPartPeriodTau_zero_value_one E H k m d t P gam y
  obtain ⟨e₁, he₁⟩ := hlam y z n ψ₀ τ₀ hψ hτ
  obtain ⟨e₂, he₂⟩ := hlam y 0 n ψ₀ τ₁ hψ hτ₁
  obtain ⟨u₂, hu₂⟩ : ∃ u : (DualNumber k)ˣ, (u : DualNumber k) = 1 + TrivSqZeroExt.inr (lam (max e₁ e₂) y -
      ∑ i, (((max e₁ e₂ : ℕ) : k) * (n i : k) + (gam i y 0 : k)) * MvPowerSeries.constantCoeff (q i)) :=
    ⟨⟨_, 1 - TrivSqZeroExt.inr (lam (max e₁ e₂) y -
      ∑ i, (((max e₁ e₂ : ℕ) : k) * (n i : k) + (gam i y 0 : k)) * MvPowerSeries.constantCoeff (q i)),
      by ext <;> simp, by ext <;> simp⟩, rfl⟩
  have hu₁ : ((u₂ * ee : (DualNumber k)ˣ) : DualNumber k) = 1 + TrivSqZeroExt.inr (lam (max e₁ e₂) y -
      ∑ i, (((max e₁ e₂ : ℕ) : k) * (n i : k) + (gam i y z : k)) * MvPowerSeries.constantCoeff (q i)) := by
    rw [Units.val_mul, hu₂, hee]
    have hs : ∀ i, (((max e₁ e₂ : ℕ) : k) * (n i : k) + (gam i y z : k)) * MvPowerSeries.constantCoeff (q i) =
        (((max e₁ e₂ : ℕ) : k) * (n i : k) + (gam i y 0 : k)) * MvPowerSeries.constantCoeff (q i) -
          (((-1 : ℚ) : k) * MvPowerSeries.constantCoeff (q i) * (gam i y z : k)) := by
      intro i
      simp only [map_zero, Int.cast_zero, add_zero, Rat.cast_neg, Rat.cast_one]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hs i), Finset.sum_sub_distrib]
    ext <;> simp
    ring
  have A := he₁ (max e₁ e₂) (le_max_left _ _) (u₂ * ee) hu₁ zz J hJ
  have B := he₂ (max e₁ e₂) (le_max_right _ _) u₂ hu₂ zz J hJ
  rw [hv₁ _ (spMap ρ) zz J hJ, hv₁ _ (spMap (constHom ρ)) zz J hJ] at B
  have hW : ∀ a : P.D.toPre.X, a = y →
      gm (c' a) zz _ (w.s (fun _ => J (c' a ≫ π₂), fun _ => J (c' a ≫ π₁))) =
        gm (c' y) zz _ (w.s (fun _ => J (c' y ≫ π₂), fun _ => J (c' y ≫ π₁))) := by
    rintro a rfl; rfl
  rw [hW (y + 0) (add_zero y)] at B
  have hG : gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn (u₂ * ee)) =
      gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn u₂) * gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn ee) := by
    rw [← map_mul]; congr 1; simp only [unitOn, map_mul]
  rw [hG] at A
  exact alg (hA := A) (hB := B)

end GlobalTheory.UnitsAlong
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.mem_dividingLabels_iff_class_zero : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (a : X₁.S.Gam), a ∈ X₁.S.HH X₁.M z₁ ↔ 𝔪.YY a 0 := by
  first | exact @GlobalTheory.GSep.mem_HH_iff_yy_zero | exact GlobalTheory.GSep.mem_HH_iff_yy_zero | (intros; apply GlobalTheory.GSep.mem_HH_iff_yy_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.Sep.ThetaTerms

theorem yK_ne_zero {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} {x₀ : X₁.S.Gam}
    (hd : X₁.M.Div X₁.S.th x₀ z₁) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    {ev : X₁.M.Z.presheaf.stalk z₁ →+* V} {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V}
    {δ : Fin m → LinearMap.BilinForm ℤ X} (𝔪 : UMem X₁ z₁ act V ev X t δ) :
    𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 := by
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  obtain ⟨a, ha⟩ := GlobalTheory.ThetaGeneric.exists_th_ne_zero hL.1 hL.2.1 _ _ X₁.S X₁.ρ (FractionRing V) 𝔪.yK
  intro h0
  apply ha
  set y := jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hy
  have hs : y (closedPoint (FractionRing V)) ⤳ z₁ := by
    have : y (closedPoint (FractionRing V)) ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hw : ∀ w, y w ⤳ y (closedPoint (FractionRing V)) := fun w => by
    rw [Subsingleton.elim (α := PrimeSpectrum (FractionRing V)) w (closedPoint _)]
  have e : X₁.S.th a = X₁.S.th a / X₁.S.th x₀ * X₁.S.th x₀ := (div_mul_cancel₀ _ hd.1).symm
  rw [𝔪.yK_eq] at h0 ⊢
  change X₁.M.val y (X₁.S.th a) = 0
  change X₁.M.val y (X₁.S.th x₀) = 0 at h0
  rw [e, RatModel.val_mul hw ((hd.of_specializes hs).2 a) (𝔪.reg _ (X₁.S.th_mem x₀)), h0, mul_zero]

theorem isThetaTerms₀_of_terms : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), Set.range lab = X₁.S.HH X₁.M z₁ → ∀ T : (Fin 8 → X) → C → V, 𝔪.Terms x₀ lab T → IsThetaTerms₀ 𝔪.D.toPre (X₁.S.r * X₁.S.N) 𝔪.e₈ T := by
  intro g n F W Z i X₁ z₁ act x₀ hd V _ _ _ ev X _ m t δ 𝔪 C lab hlab T hT
  obtain ⟨x, fr, th, w₀, s, g', w, hx, hfr, -, hw₀, -, hg, hT⟩ := hT
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    have := X₁.S.r_pos; have := X₁.S.N_ge
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hu : IsUnit ((X₁.S.r * X₁.S.N : ℕ) : V) := by
    have := X₁.S.unit.map (ev.comp ((X₁.M.stalkEquiv z₁).symm.toRingHom.comp (algebraMap X₁.o₁ (X₁.M.O z₁))))
    rwa [map_natCast] at this
  have h0 := yK_ne_zero hd 𝔪

  obtain ⟨ρ, hρ, Hr⟩ := GlobalTheory.ConstFam.exists_gen_through (K := PUnit) (φ' := fun _ => eSec 𝔪.A.A)
    (φ := fun _ => eSec X₁.ρ.P.A) (ε := fun _ => 1) (h := spMap 𝔪.yK) 𝔪.wl_gen X₁.ρ.P.isLB 𝔪.A.isLB
    (fun _ => PolBaseChange.eSec_comm 𝔪.cart) X₁.ρ.rig X₁.ρ.rig_gen
  have htf : ∀ a, IsTorsFrame 𝔪.A ρ (X₁.S.r * X₁.S.N) (x a) (fr a) := fun a =>
    GlobalTheory.FrameMove.isTorsFrame_move (T := baseOver (Sp X₁.S.R)) (T' := TFK (R := V) (FractionRing V)) (w := 𝔪.wl)
      (h := spMap 𝔪.yK) 𝔪.cart 𝔪.wl_gen
      (fun Z r z J J' hJ hJ' =>
        (Hr Z r z J J' hJ hJ').trans (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _))))
      (hx a) (X₁.ρ.fr_tors a) (hfr a).1 (fun z J J' hJ hJ' => ((hfr a).2 z J J' hJ hJ').symm)
  obtain ⟨ρ', c, hc, hN, hmove⟩ := GlobalTheory.T.exists_renormalization_rigidification_multiple V _ 𝔪.D 𝔪.A 𝔪.G 𝔪.U.toUnifPre w₀ hw₀ ρ hρ
  choose w' fr' hw' hfr' hov hco hval using fun a : C => liesOver_scale V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.U.toUnifPre (FractionRing V) w₀
    (g' a) (w a) (x (lab a)) (fr (lab a)) (hg a).2.1 (hfr _).1 (hg a).2.2 c hc
  have htors : ∀ a, (g' a).b ^ (X₁.S.r * X₁.S.N) = 1 := fun a => by
    obtain ⟨o, h₁, h₂⟩ := (hg a).1
    letI := GlobalTheory.TorusExt.gtGroup 𝔪.D.toPre (FractionRing V)
    have e := congrArg (GlobalTheory.TorusExt.gtProj 𝔪.D.toPre (FractionRing V)) ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 h₁)
    rw [map_nsmul] at e
    exact (congrArg Additive.toMul e).symm.trans ((isZero_iff o).1 h₂).1
  choose b hb₁ hb₂ using fun a => GlobalTheory.T.torsionPoint_extends_over_normal_domain hL.1 V 𝔪.cn.1 𝔪.cn.2.1 𝔪.D.toPre.P _ hk (g' a).b (htors a)
  refine ⟨(c / 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) • s + 0, g', b, w', hb₂, fun a => (hg a).1, ?_, fun a => ⟨hw' a, ?_⟩,
    fun mu a => ?_⟩
  · refine GlobalTheory.T.torsion_sections_exhaust_geometric_fibres hL.1 V 𝔪.cn.1 𝔪.D.toPre.P _ hk hu C b hb₁ fun p hp => ?_
    obtain ⟨a, ha⟩ := exhaust_of_labels hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ hk C g' (fun a => x (lab a)) (fun a => (hg a).1)
      (fun a a' e => by
        have h₁ := hg a
        have h₂ := hg a'
        generalize w a' = om at h₂
        generalize g' a' = ga at e om h₂
        subst e
        exact GlobalTheory.T.eq_of_framedPoint_lies_over_torus_extension hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ w₀ hw₀ _ _ _ _ _ _ _ h₁.2.1 h₂.2.1 (hfr _).1 (hfr _).1
          h₁.2.2 h₂.2.2)
      (fun q y hq hy => by
        have hyN : y ^ (X₁.S.r * X₁.S.N) = 1 := (hy w₀ hw₀).1
        have e : (TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK =
            spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) :=
          (Spec.map_comp (CommRingCat.ofHom 𝔪.yK) (CommRingCat.ofHom (algebraMap _ _))).symm
        obtain ⟨l, hl, -⟩ := X₁.ρ.pt_bij (AlgebraicClosure (FractionRing V)) _ (Geo.Tor.pushHom 𝔪.cart _ y)
          (by rw [← map_pow, hyN, map_one])
        have hl' : y.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫
            (X₁.ρ.pt l).left := by
          rw [← e]
          exact (congrArg (fun q => q.left) hl).symm
        have hH : l ∈ X₁.S.HH X₁.M z₁ := (GlobalTheory.T.dividingThetaConstants_generate_integral_torsion_labels g n F W Z i X₁ z₁ act x₀ hd V ev X m t δ 𝔪 l).2
          ⟨q, y, by rw [hq, map_zero], hy, hl'⟩
        obtain ⟨a, rfl⟩ : l ∈ Set.range lab := by rw [hlab]; exact hH
        refine ⟨a, 𝔪.cart.1.hom_ext ?_ ?_⟩
        · rw [hl', ← e]
          exact ((Category.assoc _ _ _).trans ((congrArg _ (hx _)).trans (Category.assoc _ _ _).symm)).symm
        · refine (Over.w y).trans (Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg _ (Over.w (x (lab a))))).symm)
          exact (Category.comp_id _).symm.trans (congrArg _ (Spec.map_id _).symm)) p hp
    refine ⟨a, Over.OverMorphism.ext ?_⟩
    rw [ha, hb₂ a, Over.comp_left, Over.comp_left, ← Category.assoc]
    congr 1
    change spMap _ ≫ spMap _ ≫ jK V = spMap _ ≫ jK V
    rw [Algebra.algebraMap_self, show spMap (RingHom.id (FractionRing V)) = 𝟙 _ from Spec.map_id _, Category.id_comp]
  · obtain ⟨o, h₁, h₂⟩ := (hg a).1
    exact GlobalTheory.T.torsion_frame_abelian_part_torsion_frame hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ w₀ ρ' hN _ hk _ o h₁ h₂ _ _ _ (hw' a) (hov a)
      (hmove _ _ _ _ _ (htf _) (hfr' a) (hval a))
  · have h₁ := ((CoefBasic.coef_basic V 𝔪.D.toPre (FractionRing V) 1 (g' a)).2.2 (w' a) (hw' a)).2.1
    have h₂ : coef (0 : Fam 𝔪.D.toPre (FractionRing V) 1) (g' a) (w' a) (𝔪.e₈ mu) = 0 := by
      have := h₁ 0 0 1 (𝔪.e₈ mu)
      rw [one_smul, add_zero, _root_.one_mul] at this
      exact left_eq_add.1 this
    have h₃ : algebraMap V (FractionRing V) (T mu a) =
        coef ((c / 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) • s + 0) (g' a) (w' a) (𝔪.e₈ mu) := by
      rw [h₁, h₂, add_zero, div_mul_eq_mul_div, hco, ← hT, mul_div_cancel_right₀ _ h0]
    rw [h₃]
    exact CoefBasic.isCoef_coef _ (hw' a) _ _

end GlobalTheory.Poinc.Sep.ThetaTerms
end
end
