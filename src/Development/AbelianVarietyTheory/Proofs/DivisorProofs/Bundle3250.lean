module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle197
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaShiftFourierTermTranslationGauge
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2996
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2771
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3219
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3139
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2692
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3184
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSysUOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2905
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3125
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.UTraitLab

theorem q_eq_of_isMonomial : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (lb : u.Lab) (ϖ : u.V) (be : LinearMap.BilinForm ℤ u.D.toPre.X), ϖ ≠ 0 → IsMonomial u.D.toPre ![ϖ] ![be] → ∀ χ, lb.q χ = -Real.log ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) ϖ)‖ * (be χ χ : ℝ) / 2 := by
  intro o Ω _ _ _ S ρ p _ y₀ u lb ϖ be hϖ hmono χ
  obtain ⟨v, n, hn, hc⟩ := hmono χ
  obtain ⟨jc, hjc, hval⟩ := GlobalTheory.Poinc.valF_psi_of_psiCoord u.V u.D.toPre χ _ hc
  have hq := lb.q_eq χ jc hjc
  rw [hval] at hq
  simp only [Fin.prod_univ_one, Matrix.cons_val_zero] at hq
  have hunit : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (v : u.V))‖ = 1 := by
    have h1 : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (v : u.V))‖ ≤ 1 := (u.norm_le _).2 ⟨_, rfl⟩
    have h2 : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ ((v⁻¹ : u.Vˣ) : u.V))‖ ≤ 1 :=
      (u.norm_le _).2 ⟨_, rfl⟩
    have h3 : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (v : u.V))‖ *
        ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ ((v⁻¹ : u.Vˣ) : u.V))‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
    nlinarith [norm_nonneg (algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (v : u.V))),
      norm_nonneg (algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ ((v⁻¹ : u.Vˣ) : u.V)))]
  rw [map_mul, map_mul, norm_mul, hunit, one_mul, map_pow, map_pow, norm_pow] at hq
  set a := ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) ϖ)‖ with ha
  have hapos : 0 < a := by
    rw [ha, norm_pos_iff]
    intro h0
    have h1 : algebraMap u.V (FractionRing u.V) ϖ = 0 :=
      (algebraMap (FractionRing u.V) (PadicAlgCl p)).injective (by rw [h0, map_zero])
    exact hϖ (IsFractionRing.injective u.V (FractionRing u.V) (by rw [h1, map_zero]))
  have hl : -lb.q χ = (n 0 : ℝ) * Real.log a := by
    rw [← Real.log_pow, hq, Real.log_exp]
  have hb : (be χ χ : ℝ) = 2 * (n 0 : ℝ) := by
    have := hn 0
    simp only [Matrix.cons_val_zero] at this
    rw [this]; push_cast; ring
  rw [hb]
  linarith

end GlobalTheory.UPoinc.UTraitLab

namespace GlobalTheory.UPoinc


open GlobalTheory.UPoinc.UTraitLab in
theorem uTraitLabels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (u' : Sp (ratHull S.R) ⟶ Xo.XF cf) (G : Over (Sp (ratHull S.R))) (_ : GrpObj G) (α : G.left ⟶ ρ.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ.P.A (spMap (toRat S.R)) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ.P.L.pull α) (Xo.univ.t.PP.L.pull β) → ∀ (p : ℕ) [Fact p.Prime] (y₁ : ratHull S.R →+* PadicAlgCl p) (T : UTrait Xo cf) (ι : FractionRing T.V →+* PadicAlgCl p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) → spMap y₁ ≫ u' = spMap ι ≫ T.y → (∀ a : o, ‖y₁ (toRat S.R (algebraMap o S.R a))‖ ≤ 1) → ∃ (u : ρ.UTest p (y₁.comp (toRat S.R))) (lb : u.Lab) (j : u.D.toPre.X ≃+ T.P.D.toPre.X), (∀ χ, lb.q χ = -Real.log ‖ι (algebraMap T.V (FractionRing T.V) T.ϖ)‖ * (T.be (j χ) (j χ) : ℝ) / 2) ∧ ∀ (m : ℕ) (a : 𝓞 E) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (w w' : Sp (PadicAlgCl p) ⟶ G.left), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → w ≫ α = x.left ≫ u.φ → w' ≫ α = x'.left ≫ u.φ → w' ≫ β = w ≫ β ≫ (Xo.univ.t.act.act a).left → CongMod m (j pk'.y) (a • j pk.y) := by
  intro E _ _ _ H Dw hpq l Xo cf o Ω _ _ _ _ S ρ u' G _ α β hα hβ hL p _ y₁ T ι hι hsp hint
  obtain ⟨T', ι', yK, e, k, hι', hfac, hy', hϖ, hbe⟩ := GlobalTheory.T.exists_unitaryTrait_finiteExtension_classicalPoint E H Dw l Xo cf o Ω S u' p y₁ T ι hι hsp
  obtain ⟨φ, cart, lb, hact⟩ := GlobalTheory.T.exists_unitaryTrait_pullback_thetaSystem E H Dw l Xo cf o Ω S ρ u' G inferInstance α β hα hβ hL T' yK hy'
  haveI : IsDiscreteValuationRing T'.V := T'.cdvr.1
  letI : Algebra (FractionRing T'.V) (PadicAlgCl p) := ι'.toAlgebra
  let u : ρ.UTest p (y₁.comp (toRat S.R)) :=
    { V := T'.V, complete := T'.cdvr.2.1, norm_le := hι', yK := yK.comp (toRat S.R),
      fac := by rw [← RingHom.comp_assoc, RingHom.algebraMap_toAlgebra, hfac],
      A := T'.P.A, φ := φ, cart := cart, lb := lb, G := T'.t.G, semi := T'.t.semi, D := T'.P.D, U := T'.P.U }
  obtain ⟨lab⟩ := GlobalTheory.ZH.labels_exist GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 GlobalTheory.ZH.uTors_closed o Ω S ρ p _ u
    hint
  refine ⟨u, lab, e.toAddEquiv, ?_, ?_⟩
  · intro χ
    have hq := q_eq_of_isMonomial o Ω S ρ p _ u lab T'.ϖ T'.be T'.irr.ne_zero T'.mono χ
    rw [hq]
    change -Real.log ‖ι' (algebraMap T'.V _ T'.ϖ)‖ * ((T'.be χ χ : ℤ) : ℝ) / 2 =
      -Real.log ‖ι (algebraMap T.V _ T.ϖ)‖ * ((T.be (e χ) (e χ) : ℤ) : ℝ) / 2
    rw [hϖ, Real.log_pow, hbe χ χ]
    push_cast
    ring
  · intro m a pk pk' x x' w w' hm h1 h2 hw hw' hww
    have hx : x' = x ≫ T'.P.oA.act a := hact _ x x' w w' a hw hw' hww
    obtain ⟨z, hz⟩ := GlobalTheory.T.torsionLattice_moves_by_ringAction_completeDVR E H T'.V T'.cdvr T'.t T'.P (PadicAlgCl p) m a pk pk' x x' hm h1 h2 hx
    exact ⟨e z, by simp [hz, map_add (f := _), map_nsmul]⟩

end GlobalTheory.UPoinc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.integerAction_semiAbelian_along_traits_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → ∃ f : 𝓞 E → (out.G ⟶ out.G), (∀ a, IsMonHom (f a)) ∧ (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ∃ β : T.t.G.left ⟶ out.G.left, IsGrpPullback T.t.G out.G ξ β ∧ LBIso T.t.PP.L (out.L.L.pull β) ∧ ∀ a, (T.t.act.act a).left ≫ β = β ≫ (f a).left) := by
  first | exact @GlobalTheory.UPoinc.oAct_along_traits | exact GlobalTheory.UPoinc.oAct_along_traits | (intros; apply GlobalTheory.UPoinc.oAct_along_traits <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.integerAction_semiAbelian_along_traits_over_moduli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (r : Y.Z ⟶ C.Z), X₁.S.Over₀ Y U₀ → Y.pt ≫ r = X₁.uΩ ≫ C.i → ∃ f : 𝓞 E → (out.G ⟶ out.G), (∀ a, IsMonHom (f a)) ∧ (∀ z : Y.Z, r z ∈ Set.range C.i → z ∈ abLocus out.G) ∧ (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ r = T.y ≫ C.i → ∃ β : T.t.G.left ⟶ out.G.left, IsGrpPullback T.t.G out.G ξ β ∧ LBIso T.t.PP.L (out.L.L.pull β) ∧ ∀ a, (T.t.act.act a).left ≫ β = β ≫ (f a).left) := by
  first | exact @GlobalTheory.UPoinc.oAct_along_traits_of_over | exact GlobalTheory.UPoinc.oAct_along_traits_of_over | (intros; apply GlobalTheory.UPoinc.oAct_along_traits_of_over <;> assumption)
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

namespace GlobalTheory.FormalPointG

theorem exists_point_sameDerivations : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ Y.H.left) (δ : Fin n → Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω → Function.Injective φ → ∀ (hx : x ≫ Y.H.hom = spMap φ), (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → ∃ (x' : Sp Ω ⟶ t.G.left) (hx' : x' ≫ t.G.hom = spMap φ) (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) ∧ (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) ∧ (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) ∧ GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx)) (Over.homMk x' hx') := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam _ _ _
  letI := H.starRing
  intro Y n vH dd hdd v' hv' Ω _ _ _ φ x δ hΩ hφ hx hδ hxd
  haveI := hΩ
  obtain ⟨x', hx'p, -⟩ :=
    GlobalTheory.FormalPoint.existsUnique_isPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx))
  choose dd' hdd' using fun a => GlobalTheory.T.exists_invariant_vectorField_semiAbelian_triple_affine E H R t (v' a)
  have hpt : GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx))
      (Over.homMk x'.left (Over.w x')) := hx'p
  have hder := GlobalTheory.T.uniformised_point_from_formal_raynaud_point_same_derivations E H R t P Y n (fun a => vH a) dd hdd v' hv' dd' hdd' Ω φ x δ hΩ hx hδ hxd x'.left
    (Over.w x') hpt
  obtain ⟨b, hb⟩ := GlobalTheory.T.uniformisedTangentBasis_of_raynaudBasis E H R t P Y n vH v' hv'
  refine ⟨x'.left, Over.w x', dd', hdd', hder, ?_, hpt⟩
  intro O f hO h0
  refine GlobalTheory.T.eq_zero_of_invariantDerivatives_vanish_semiAbelian R t.G t.semi n b dd' (fun a => (hb a).symm ▸ hdd' a) Ω φ hφ x'.left (Over.w x') O f hO
    fun l => ?_
  have key : ∀ l : List (Fin n), valR x'.left O (l.foldr (fun a g => dd' a O g) f) =
      l.foldr (fun a w => δ a w) (valR x'.left O f) := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => simp only [List.foldr_cons]; rw [hder a O _ hO, ih]
  rw [key, h0]
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons]; rw [ih, map_zero]

end GlobalTheory.FormalPointG
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

theorem _root_.GlobalTheory.T.thetaShift_fourierTerm_translation_gauge : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∀ mu : Dd.toPre.X, ∃ (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (e : LB.Gen (LB.LinComb Dd.toPre.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])) (β : Dd.toPre.X) (w : Dd.toPre.X →+ R) (π π' : R), e.IsGen ∧ (∀ (j : Fin 2 → Dd.toPre.P.L.ι) (V : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ LB.wchart Dd.toPre.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j → IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V))) ∧ ∀ (k : ℕ) (α : Dd.toPre.X), 1 ≤ k → ∃ a b : R, a ≠ 0 ∧ ∀ (σ : Dd.toPre.SecB k α) (σ₁ : Dd.toPre.SecB k (α + k • mu)) (τ τ₁ ρ : SecM Y.q.left Dd.toPre.P.L k), ShiftEq Dd.toPre k mu α σ σ₁ 0 σ₁ → IsTerm Y k α σ τ → IsTerm Y k (α + k • mu) σ₁ τ₁ → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Dd.toPre.P.A.left) → Dd.toPre.P.L.ι), Good Dd.toPre.P.L z J → sval ρ r z J = sval τ₁ (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J * ((val e r z J) ^ k).val) → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Dd.toPre.P.A.left) → Dd.toPre.P.L.ι), Good Dd.toPre.P.L z J → gs r z ⊤ (scal Y.H.hom a) * sval ρ r z J = gs r z ⊤ (scal Y.H.hom b) * sval τ r z J) ∧ ∀ (σ'' : Dd.toPre.SecB k α) (σ₁' : Dd.toPre.SecB k (α + k • mu)) (τ'' τ₁' ρ' : SecM Y.q.left Dd.toPre.P.L k), IsTerm Y k α σ'' τ'' → IsTerm Y k (α + k • mu) σ₁' τ₁' → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Dd.toPre.P.A.left) → Dd.toPre.P.L.ι), Good Dd.toPre.P.L z J → sval ρ' r z J = sval τ₁' (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J * ((val e r z J) ^ k).val) → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Dd.toPre.P.A.left) → Dd.toPre.P.L.ι), Good Dd.toPre.P.L z J → gs r z ⊤ (scal Y.H.hom a) * sval ρ' r z J + gs r z ⊤ (scal Y.H.hom (2 * (k : R) * D a)) * sval ρ r z J = gs r z ⊤ (scal Y.H.hom b) * sval τ'' r z J + gs r z ⊤ (scal Y.H.hom (2 * (k : R) * D b)) * sval τ r z J) → ShiftEq Dd.toPre k mu α σ'' σ₁' (2 * (k : R) * w α + 2 * (k : R) ^ 2 * π + 2 * (k : R) * π') σ₁ := by
  first | exact @GlobalTheory.HeatShift.shift_term | exact GlobalTheory.HeatShift.shift_term | (intros; apply GlobalTheory.HeatShift.shift_term <;> assumption)
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

theorem _root_.GlobalTheory.T.translation_carries_ratioDatum_remainder : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∀ (y : P.D.toPre.X) (N : ℕ), 1 ≤ N → ∀ (σ σ' σp σp' : P.D.toPre.SecB N 0) (U : P.D.toPre.P.A.left.Opens) (f g : Γ(P.D.toPre.P.A.left, U)), GlobalTheory.HeatRatio.IsRatio P.D.toPre σ σ' U f → TActs Y h N 0 σ σp → TActs Y h N 0 σ' σp' → GlobalTheory.HeatRatio.IsRem P.D.toPre σ' σp σp' U f g → ∃ (β : P.D.toPre.X) (s s' sp sp' : P.D.toPre.SecB N β), GlobalTheory.HeatRatio.IsRatio P.D.toPre s s' ((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left ⁻¹ᵁ U) (((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left.app U).hom f) ∧ TActs Y h N β s sp ∧ TActs Y h N β s' sp' ∧ GlobalTheory.HeatRatio.IsRem P.D.toPre s' sp sp' ((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left ⁻¹ᵁ U) (((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left.app U).hom f) (((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left.app U).hom g) := by
  first | exact @GlobalTheory.HeatShiftW.shift_ratio_rem | exact GlobalTheory.HeatShiftW.shift_ratio_rem | (intros; apply GlobalTheory.HeatShiftW.shift_ratio_rem <;> assumption)
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

theorem GlobalTheory.Heat.gc_symbol_vanishes : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (δ : Fin n → Derivation ℤ F F), (∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δ a (valR ξ O f)) → ∀ (j₀ : P₀.L.ι), ⊤ ≤ ξ ⁻¹ᵁ P₀.L.U j₀ → ∀ (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F), Λᵀ = Λ → (∀ r, δ₀ (ψ r) = 0) → (∀ (k : ℕ), 1 ≤ k → ∀ σ τ : SecM (𝟙 P₀.A.left) P₀.L k, ∃ ρ : SecM (𝟙 P₀.A.left) P₀.L (3 * k), ∀ b c : F, b = valR ξ _ (σ.f fun _ => j₀) → c = valR ξ _ (τ.f fun _ => j₀) → (k : F) * b * (b * δ₀ c - c * δ₀ b) - ∑ a, ∑ e, Λ a e * δ a b * (b * δ e c - c * δ e b) = valR ξ _ (ρ.f fun _ => j₀)) → Λ = 0 := by
  intro K _ _ P₀ n v dd hv F _ ψ ξ hξ hval δ hδ j₀ hj₀ δ₀ Λ hΛ hδ₀ hbr
  obtain ⟨k, I, s, hk, hcov, hai⟩ := GlobalTheory.T.exists_affine_cover_by_polarization_power_sections K P₀
  have haff : ∀ i, IsAffineOpen (Out.nonzeroLocus (s i)) := fun i => (hai i).1
  have hne := fun i => (hai i).2
  have hloc : ∀ i, ⊤ ≤ ξ ⁻¹ᵁ Out.nonzeroLocus (s i) := fun i =>
    GlobalTheory.T.top_le_preimage_nonempty_open_of_pointValue_injective K P₀ F ψ ξ hξ hval _ (hne i)
  have hL := fun i => GlobalTheory.T.heat_symbol_regular_on_section_nonvanishing_locus K P₀ n v dd hv F ψ ξ hξ hval δ hδ j₀ hj₀ δ₀ Λ hbr k hk (s i) (hloc i)
  have hreg : ∀ i a e, ∃ h : Γ(P₀.A.left, Out.nonzeroLocus (s i)), valR ξ _ h = Λ a e := fun i =>
    GlobalTheory.T.symbol_entries_regular_affineOpen K P₀ n v dd hv F ψ ξ hξ hval δ hδ Λ _ (haff i) (hloc i) (hL i).1
  have hc : ∀ a e, ∃ r : K, ψ r = Λ a e := fun a e =>
    GlobalTheory.T.exists_const_of_regular_on_cover_abelianVariety K P₀ F ψ ξ hξ hval I (fun i => Out.nonzeroLocus (s i)) hcov hloc (Λ a e) (fun i => hreg i a e)
  choose lam hlam using hc
  have hsym : lamᵀ = lam := by
    ext a e
    apply ψ.injective
    show ψ (lam e a) = ψ (lam a e)
    rw [hlam, hlam]
    exact congrFun (congrFun hΛ a) e
  have hks := GlobalTheory.T.kodairaSpencer_relation_zero_derivation_of_shifted K P₀ n v dd hv F ψ ξ hξ hval δ hδ j₀ hj₀ δ₀ lam hsym hδ₀ k hk I s hcov haff hloc
    (fun i f => by
      obtain ⟨f', hf'⟩ := (hL i).2 f
      exact ⟨f', by rw [hf']; simp only [hlam]⟩)
  have h0 := GlobalTheory.T.kodairaSpencer_matrix_zero_derivation_eq_zero K P₀ n v dd hv lam hks
  ext a e
  rw [← hlam a e, h0]
  simp
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

theorem _root_.GlobalTheory.T.invariantField_comb_kills_weightZero_of_coboundary : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Algebra ℚ R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (K : Type) (Wk : K → Y.H.left.Opens) (jk : K → Q.P.L.ι), (∀ k, ∃ V : Q.P.A.left.Opens, Wk k = Y.q.left ⁻¹ᵁ V) → ⨆ k, Wk k = ⊤ → (∀ k, Wk k ≤ Y.q.left ⁻¹ᵁ Q.P.L.U (jk k)) → ∀ (P : ∀ k, Γ(Y.H.left, Wk k)) (e : Fin n → R), (∀ k, IsWt Y 0 _ (P k)) → (∀ k k' (Wo : Y.H.left.Opens), Wo ≤ Wk k ⊓ Wk k' → rsT (P k') Wo - rsT (P k) Wo = ∑ a, constFn Y.H.hom Wo (e a) * dlg Y.H Y.q.left Q.P.L (dd a) (jk k) (jk k') Wo) → ∀ (V : Q.P.A.left.Opens) f, IsWt Y 0 (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = 0 := by
  first | exact @GlobalTheory.HeatUniq.comb_kills_weight_zero | exact GlobalTheory.HeatUniq.comb_kills_weight_zero | (intros; apply GlobalTheory.HeatUniq.comb_kills_weight_zero <;> assumption)
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

theorem _root_.GlobalTheory.T.exists_torusInvariant_derivationLifts_raynaudCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (D : Derivation ℤ R R), ∃ (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι) (d : J → Fld Y.H.left), ⨆ i, V i = ⊤ ∧ (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) ∧ (∀ i, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V i) (d i)) ∧ ∀ i, (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d i _ f)) := by
  first | exact @GlobalTheory.HeatInvLift.exists_invLift_cover | exact GlobalTheory.HeatInvLift.exists_invLift_cover | (intros; apply GlobalTheory.HeatInvLift.exists_invLift_cover <;> assumption)
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

namespace GlobalTheory.Heat.ConjGauge
open ReciprocityTheory.ChartRestriction.G.Semi

theorem oneGen_isGen {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := by
  intro i j
  have e : (LB.LinComb L (Y := Y) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim).g i j = 1 := by
    dsimp only [LB.LinComb]
    erw [Fintype.prod_empty]
    rfl
  show res _ (1 : Γ(Y, _)ˣ) = _ * res _ (1 : Γ(Y, _)ˣ)
  rw [map_one, map_one, e, _root_.one_mul]

theorem exists_pullSec {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) (m : Y ⟶ X) (T : Y ⟶ Y) (k : ℕ)
    (τ : SecM m L k) : ∃ σ : SecM (T ≫ m) L k, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι),
      Good L z J → sval σ r z J = sval τ (r ≫ T) z J := by
  have hF : FormEq (K := Fin 1 ⊕ PEmpty.{1}) (Sum.elim (fun _ : Fin 1 => T ≫ m) PEmpty.elim)
      (Sum.elim (fun _ : Fin 1 => (k : ℤ)) PEmpty.elim) (K' := Fin 1) (fun _ => T ≫ m) (fun _ => (k : ℤ)) := by
    intro U _ h
    simp [Fintype.prod_sum_type]
  obtain ⟨σ, hσ⟩ := exists_sec hL hF (pullMulSec τ T (LB.oneGen L (Y := Y)) (oneGen_isGen L))
  refine ⟨σ, fun Z r z J hJ => ?_⟩
  rw [hσ Z r z J hJ, sval_pullMulSec τ T _ _ r z hJ, val_one, Units.val_one, _root_.mul_one]

theorem conj_gauge : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra ℚ R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Q.P.L dd ⇑D), IsBasic Y h → ∀ (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])) (β : Q.X), e.IsGen → (∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j → IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V))) → ∃ h' : Heat Y.H Y.q.left Q.P.L dd ⇑D, IsBasic Y h' ∧ h'.Θ = h.Θ ∧ h'.u = h.u ∧ ∀ (k : ℕ) (τ τ' ρ ρ' : SecM Y.q.left Q.P.L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ r z J = sval τ (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J * ((val e r z J) ^ k).val) → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ' r z J = sval τ' (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J * ((val e r z J) ^ k).val) → h.Acts k τ τ' → h'.Acts k ρ ρ' := by
  intro R _ _ _ Q O _ _ _ oa Y n v dd hv D h hB x e β he hwt
  obtain ⟨h₁, hΘ₁, hu₁, hB₁, hA₁⟩ := GlobalTheory.T.exists_translated_torus_invariant_heat_operator R Q O oa Y n v dd hv D h hB x
  obtain ⟨h', hB', hΘ', hu', hA'⟩ := GlobalTheory.T.exists_gauged_torusInvariant_heatOperator R Q O oa Y n v dd hv D x h₁ hB₁ e β he hwt
  refine ⟨h', hB', hΘ'.trans hΘ₁, hu'.trans hu₁, fun k τ τ' ρ ρ' hρ hρ' hact => ?_⟩
  obtain ⟨σ, hσ⟩ := exists_pullSec Q.P.L Q.P.isLB Y.q.left (𝟙 Y.H * (toUnit Y.H ≫ x)).left k τ
  obtain ⟨σ', hσ'⟩ := exists_pullSec Q.P.L Q.P.isLB Y.q.left (𝟙 Y.H * (toUnit Y.H ≫ x)).left k τ'
  exact hA' k σ σ' ρ ρ' (fun Z r z J hJ => by rw [hσ Z r z J hJ]; exact hρ Z r z J hJ)
    (fun Z r z J hJ => by rw [hσ' Z r z J hJ]; exact hρ' Z r z J hJ) (hA₁ k τ τ' σ σ' hσ hσ' hact)

end GlobalTheory.Heat.ConjGauge
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

theorem _root_.GlobalTheory.T.exists_symmetric_kodairaSpencer_invariantLifts : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι) (d : J → Fld Y.H.left), ⨆ i, V i = ⊤ → (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) → (∀ i, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V i) (d i)) → (∀ i, (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d i _ f))) → ∀ C : Matrix (Fin n) (Fin n) R, (∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f, d i W f - d i' W f = ∑ a, ∑ b, constFn Y.H.hom W (C a b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W * dd a W f) → ∃ Θ : Matrix (Fin n) (Fin n) R, Θᵀ = Θ ∧ ∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f, d i W f - d i' W f = ∑ a, ∑ b, constFn Y.H.hom W (Θ a b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W * dd a W f := by
  first | exact @GlobalTheory.InvLiftSymm.exists_symm_invLift | exact GlobalTheory.InvLiftSymm.exists_symm_invLift | (intros; apply GlobalTheory.InvLiftSymm.exists_symm_invLift <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep
open GlobalTheory.UCovSep

namespace GlobalTheory.UCovSep



theorem exists_linked_cov : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ n : ℕ, n.Prime → Odd n → ∀ j₀ : ℕ, ∃ (j : ℕ) (Y : Scheme.{0}) (q : Y ⟶ Xo.XF c), j₀ ≤ j ∧ IsFinite q ∧ Surjective q ∧ ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z) (yM : Sp K ⟶ X₁.M.Z), GlobalTheory.GSep.ULink C X₁ act u π ∧ X₁.S.r * X₁.S.N = (n ^ j) ^ 2 ∧ (∃ (U : C.Z.Opens) (g' : X₁.M.Z ⟶ U.toScheme), IsFinite g' ∧ g' ≫ U.ι = π ∧ Set.range (pullback.fst C.z (spMap C.b)) ⊆ (U : Set C.Z)) ∧ yM ≫ π = y' ≫ q ≫ C.i ∧ ∀ a ∈ X₁.S.R, a ∈ X₁.M.O (yM (closedPoint K)) := by
  intro E _ _ _ H Dw hpq l Xo c C n hn ho j₀
  classical
  haveI : Finite (genericPoints (Xo.XF c)) := (GlobalTheory.T.genericPoints_finite_unitaryModuli_coefficientField E H Dw l Xo c).to_subtype
  letI : Fintype (genericPoints (Xo.XF c)) := Fintype.ofFinite _
  choose g₀ hA using fun τ : genericPoints (Xo.XF c) => GlobalTheory.T.exists_levelStructure_normalModel_unitaryModuliPoint E H Dw hpq l Xo c C τ.1 n hn ho
  choose k j₁ hk _hB hj₁ big using fun τ : genericPoints (Xo.XF c) =>
    GlobalTheory.UPoinc.GSetup.exists_big_level (g₀ τ) n hn.two_le 0
  set J := j₀ + ∑ τ, (k τ + j₁ τ) + 1 with hJ
  have hkJ : ∀ τ, k τ + j₁ τ + j₀ + 1 ≤ J := fun τ => by
    have := Finset.single_le_sum (f := fun τ => k τ + j₁ τ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ)
    omega
  choose o₁ Ω i₁ i₂ i₃ i₄ ze uτ A₁ lev M U g hAg hun hx hUO hpt hMn hMp hgf hrange using fun τ => hA τ (4 * J)
  obtain ⟨Y, q, hqf, hqs, hY⟩ := GlobalTheory.T.exists_finite_surjective_cover_from_opens (Xo.XF c) C.Z C.i (genericPoints (Xo.XF c)) (fun τ => (M τ).Z) U g hgf
    (fun τ => by
      rintro _ ⟨x, rfl⟩
      exact hrange τ ⟨C.iF x, rfl⟩)
    (fun x => by
      obtain ⟨τ, hτ, hsp⟩ := GlobalTheory.exists_mem_genericPoints_specializes x
      refine ⟨⟨τ, hτ⟩, (M ⟨τ, hτ⟩).pt (closedPoint (Ω ⟨τ, hτ⟩)), ?_⟩
      have h₁ : (g ⟨τ, hτ⟩ ≫ (U ⟨τ, hτ⟩).ι) ((M ⟨τ, hτ⟩).pt (closedPoint (Ω ⟨τ, hτ⟩))) = C.i τ := by
        refine (congrArg (fun χ : Sp (Ω ⟨τ, hτ⟩) ⟶ C.Z => χ (closedPoint (Ω ⟨τ, hτ⟩))) (hpt ⟨τ, hτ⟩)).trans ?_
        exact congrArg C.i (hx ⟨τ, hτ⟩ (closedPoint (Ω ⟨τ, hτ⟩)))
      rw [h₁]
      exact hsp.map C.i.continuous)
  refine ⟨J, Y, q, by omega, hqf, hqs, fun K _ y' => ?_⟩
  obtain ⟨t, yM, hyM⟩ := hY K y'
  letI := i₁ t
  letI := i₂ t
  letI := i₃ t
  haveI := i₄ t
  obtain ⟨R, P, act, u, 𝔭, hRfg, hfr, hPg, hS, ⟨levR⟩, hact, hUA, hu, h𝔭, hreg𝔭⟩ :=
    GlobalTheory.T.exists_local_spread_universal_abelian_scheme E H Dw hpq l Xo c C (o₁ t) (Ω t) (M t) (g t ≫ (U t).ι) (uτ t) (hMn t) (hpt t)
      (A₁ t) (n ^ (4 * J)) (ze t) (by rw [Nat.cast_pow]; exact (hun t).pow _) (hUO t) (lev t) K yM (y' ≫ q)
      (by rw [Category.assoc]; simpa only [Category.assoc] using hyM)
  have e : (n ^ (2 * J - 2 * k t) * (n ^ k t) ^ 2) ^ 2 = n ^ (4 * J) := by
    rw [← pow_mul, ← pow_add, ← pow_mul]
    congr 1
    have := hkJ t
    omega
  obtain ⟨S, ρ, hR, φ, hreg, -, hN, hr, hgS, hpb, hL, -⟩ := GlobalTheory.T.exists_thetaSystem_realisation_regular_at_prime (o₁ t) (Ω t) R hRfg hfr 𝔭 h𝔭 P n (k t)
    (2 * J - 2 * k t) (ze t) hn ho (hk t) (by have := hkJ t; omega) (hun t) hS (e ▸ levR)
  obtain ⟨act', hact', -, hUA'⟩ := GlobalTheory.T.unitaryAction_baseChange_subalgebra E H Dw l Xo c (o₁ t) (Ω t) R S.R hR P ρ.P φ hpb hL act u hact hUA
  have hu' : spMap (ratHull S.R).val.toRingHom ≫ spMap (Subalgebra.inclusion (ratHull_mono hR)).toRingHom ≫ u = uτ t := by
    rw [← hu, ← Category.assoc, ← Spec.map_comp]; rfl
  have hgen : ∀ w, (spMap (ratHull S.R).val.toRingHom ≫ spMap (Subalgebra.inclusion (ratHull_mono hR)).toRingHom ≫ u) w ∈
      genericPoints (Xo.XF c) := fun w => by rw [hu', hx t w]; exact t.2
  have hptS : (M t).pt ≫ (g t ≫ (U t).ι) =
      spMap (ratHull S.R).val.toRingHom ≫ (spMap (Subalgebra.inclusion (ratHull_mono hR)).toRingHom ≫ u) ≫ C.i := by
    rw [hpt t, ← hu', Category.assoc]
  have hbig : S.Big := big t _ (by have := hkJ t; omega) (o₁ t) (Ω t) S (hgS.trans (hPg.trans (hAg t))) hN hr
  let X₁ : GlobalTheory.GSep.GSet :=
    { o₁ := o₁ t, Ω₁ := Ω t, S := S, ρ := ρ, big := hbig, M := M t, normal := hMn t, projM := hMp t,
      div := C.thetaInt (o₁ t) (Ω t) S ρ _ hUA'.uOver hgen (M t) (g t ≫ (U t).ι)
        (hMn t) hptS }
  refine ⟨X₁, act', spMap (Subalgebra.inclusion (ratHull_mono hR)).toRingHom ≫ u, g t ≫ (U t).ι, yM,
    ⟨hact', hUA', hgen, hptS⟩, ?_, ⟨U t, g t, hgf t, rfl, hrange t⟩, by simpa only [Category.assoc] using hyM, ?_⟩
  · show S.r * S.N = _
    rw [hr, hN, ← pow_mul, ← pow_add, ← pow_mul]
    congr 1
    have := hkJ t
    omega
  · intro a ha
    obtain ⟨a', b', hb', rfl⟩ := hreg a ha
    exact hreg𝔭 a' b' hb'

end GlobalTheory.UCovSep
end
