module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2887
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2927
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle200
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcInTraceArc
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerDatumOfIsotropicSaturated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2929
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3058
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.finite_generation_integral_family_sections : ∀ {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) [IsLocallyNoetherian S] {r : ℕ} (V : Fin r → S.Opens)
    (t : ∀ i, Finset Γ(Sp K, gp ⁻¹ᵁ V i)), (⨆ i, V i) = ⊤ →
    (∀ i, ∀ y ∈ t i, (gp.app (V i)).hom.IsIntegralElem y) → ∀ W : S.Opens, IsAffineOpen W →
    ∃ s : Finset Γ(Sp K, gp ⁻¹ᵁ W), (∀ y ∈ s, y ∈ finFam gp V t W) ∧
      ∀ x ∈ finFam gp V t W, ∃ c : Γ(Sp K, gp ⁻¹ᵁ W) → Γ(S, W), x = ∑ y ∈ s, (gp.app W).hom (c y) * y := by
  first | exact @GlobalTheory.Mum.finFam_finite | exact GlobalTheory.Mum.finFam_finite | (intros; apply GlobalTheory.Mum.finFam_finite <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat

theorem exists_xfLevel_ext {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : GlobalTheory.Mum.Base R)
    (C : GlobalTheory.UChart.Fam Xo c R) (tK : SAB H (Sp (FractionRing R)))
    (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _))
    (I₀ : letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD (AlgebraicClosure (FractionRing R)))
    (hI₀ : GlobalTheory.LowDat.XFLevel C tK m1 m2 (AlgebraicClosure (FractionRing R)) I₀)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] :
    ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F), GlobalTheory.LowDat.XFLevel C tK m1 m2 F I ∧
      ∀ n a, (I.ev n a).y = (I₀.ev n a).y := by
  have hLL := GlobalTheory.firstFiveLaws
  have hL : Laws := hLL.1
  have hL₂ : Laws2 := hLL.2.1
  haveI : CharZero R := hR.2
  haveI : IsNoetherianRing R := hR.1.1
  haveI : CharZero (FractionRing R) := charZero_of_injective_ringHom (IsFractionRing.injective R (FractionRing R))
  haveI : CharZero (AlgebraicClosure (FractionRing R)) :=
    charZero_of_injective_ringHom (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))).injective
  have hB := C.P.D.tau_bimult
  have he := C.P.D.psi_even
  let s : AlgebraicClosure (FractionRing R) →ₐ[FractionRing R] F := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hs : s.toRingHom.comp (algebraMap (FractionRing R) _) = algebraMap (FractionRing R) F := s.comp_algebraMap
  have hj : spMap s.toRingHom ≫ jFK (R := R) (AlgebraicClosure (FractionRing R)) = jFK (R := R) F := by
    rw [jFK, jFK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hs]
  let I := GlobalTheory.ArcExt.tateExt s.toRingHom hs hB hL I₀ (GlobalTheory.ArcOfModel.weilQkIs_qkExt hL hL₂ he hB s.toRingHom hs)
  have hext : ∀ n a, QkExt s.toRingHom (I₀.ev n a) (I.ev n a) := fun n a =>
    (GlobalTheory.TorusExt.qkExt_iff hB _ hs _ _).2 rfl
  refine ⟨I, ⟨?_, ?_⟩, fun n a => (hext n a).1⟩
  · show ((Units.map s.toRingHom.toMonoidHom (I₀.ζ l.M') : Fˣ) : F) = _
    rw [Units.coe_map]
    show s.toRingHom ((I₀.ζ l.M' : AlgebraicClosure (FractionRing R))) = _
    rw [hI₀.1]
    simp only [toF, RingHom.comp_apply]
    exact s.commutes _
  · intro k a σ hk x hx
    have hk1 : 1 ≤ k := by
      rcases hk with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact l.A_pos
      · have := l.three_le; omega
    have hT := GlobalTheory.FlatTors.torsionIso_holds E H R (maximalIdeal R) hR.1 C.t C.P
    obtain ⟨f₀, f₀₁, -⟩ := hT (AlgebraicClosure (FractionRing R)) k hk1
    obtain ⟨fF, fF₁, -⟩ := hT F k hk1
    obtain ⟨g₀, hg₁, hg₂⟩ := hI₀.2 k a σ hk (f₀ (I₀.ev k a)) ((f₀₁ _ _).2 rfl)
    let x' : TFK (R := R) F ⟶ C.P.A.A :=
      (Over.homMk (spMap s.toRingHom) hj : TFK (R := R) F ⟶ TFK (R := R) (AlgebraicClosure (FractionRing R))) ≫
        f₀ (I₀.ev k a)
    have hx' : C.P.ToA F k (I.ev k a) x' :=
      (GlobalTheory.TorsionExt.qkToAkU_iff_of_qkExt hLL R (maximalIdeal R) hR.1 C.P.D C.P.A C.t.G C.t.semi C.P.U _ F s k hk1
        (I₀.ev k a) (I.ev k a) _ x' (hext k a) rfl).1 ((f₀₁ _ _).2 rfl)
    have hxx : x = x' := ((fF₁ _ _).1 hx).trans ((fF₁ _ _).1 hx').symm
    refine ⟨spMap s.toRingHom ≫ g₀, ?_, ?_⟩
    · rw [Category.assoc, hg₁, hxx]
      simp only [x', Over.comp_left, Over.homMk_left, Category.assoc]
    · rw [Category.assoc, hg₂, ← hj]
      simp only [Category.assoc]

end GlobalTheory.LowDat
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.levelPoints_compat_of_tateIsometries : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l)
  (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : GlobalTheory.UChart.Fam Xo c R)
  (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _))
  (F F' : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Field F'] [IsAlgClosed F'] [Algebra (FractionRing R) F']
  (σ : F →ₐ[FractionRing R] F')
  (I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F)) (I' : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F')),
  GlobalTheory.LowDat.XFLevel C tK m1 m2 F I → GlobalTheory.LowDat.XFLevel C tK m1 m2 F' I' →
  ∀ (a : Dw.La) (x : TFK (R := R) F ⟶ C.P.A.A) (x' : TFK (R := R) F' ⟶ C.P.A.A),
    C.P.ToA F l.M' (I.ev l.M' a) x → C.P.ToA F' l.M' (I'.ev l.M' a) x' → x'.left = spMap σ.toRingHom ≫ x.left := by
  first | exact @GlobalTheory.LowDat.level_points_compat | exact GlobalTheory.LowDat.level_points_compat | (intros; apply GlobalTheory.LowDat.level_points_compat <;> assumption)
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_gradedTateIso_lowerDatum : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw D' : Datum H) (Z : Submodule (𝓞 E) Dw.La)
  (f : GlobalTheory.LowDat.perp Dw Z →ₗ[𝓞 E] D'.La), GlobalTheory.LowDat.IsLower Dw D' Z f →
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R →
  ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
  Module.finrank ℤ D'.La = 2 * P.D.toPre.P.g →
  ∀ I : (letI := H.starRing; TateIsoQ Dw P.D.toPre P.oD F),
  (∀ n, 0 < n → ∀ a : GlobalTheory.LowDat.perp Dw Z, ∃ q : QkPt P.D.toPre F n, QkPt.Equiv P.D.toPre F (I.ev n a) q ∧ q.y = 0) →
  ∃ I' : TateIso D' F (TF (R := R) F ⟶ P.D.toPre.P.A) (fun a g => g ≫ (letI := H.starRing; P.oD.onB.act a))
      (fun n g g' z => Out.WeilIs P.D.toPre.P.A P.D.toPre.P.L n g g' (unitOn z)),
    (∀ n, I'.ζ n = I.ζ n) ∧ ∀ n, 0 < n → ∀ (a : GlobalTheory.LowDat.perp Dw Z) (q : QkPt P.D.toPre F n),
      QkPt.Equiv P.D.toPre F (I.ev n a) q → q.y = 0 → q.g.b = I'.ev n (f a) := by
  first | exact @GlobalTheory.LowDat.GradedTate.exists_gradedTateIso | exact GlobalTheory.LowDat.GradedTate.exists_gradedTateIso | (intros; apply GlobalTheory.LowDat.GradedTate.exists_gradedTateIso <;> assumption)
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_lower_datum_of_isotropic_saturated : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (Z : Submodule (𝓞 E) Dw.La),
  GlobalTheory.LowDat.IsIsoSat Dw Z → ∃ (D' : Datum H) (f : GlobalTheory.LowDat.perp Dw Z →ₗ[𝓞 E] D'.La), GlobalTheory.LowDat.IsLower Dw D' Z f ∧
    D'.p = Dw.p - Module.finrank (𝓞 E) Z ∧ D'.q = Dw.q - Module.finrank (𝓞 E) Z := by
  first | exact @GlobalTheory.LowDat.exists_lowerDatum | exact GlobalTheory.LowDat.exists_lowerDatum | (intros; apply GlobalTheory.LowDat.exists_lowerDatum <;> assumption)
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.weightPart_depends_on_label_mod : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∀ (p : ℕ) [Fact p.Prime] (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → ∀ a a' ν ν' κ, yy a = QuotientAddGroup.mk ν → yy a' = QuotientAddGroup.mk ν' → CongMod D.m ν ν' → GSum.part D z₁ z₂ a κ = GSum.part D z₁ z₂ a' κ := by
  first | exact @GlobalTheory.Poinc.GSum.part_eq_of_congMod | exact GlobalTheory.Poinc.GSum.part_eq_of_congMod | (intros; apply GlobalTheory.Poinc.GSum.part_eq_of_congMod <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.mumfordTensorData_factorInclusion_projection_props : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (i₀ : Fin r), IsMonHom (T.inc i₀) ∧ T.inc i₀ ≫ T.pr i₀ = 𝟙 _ ∧ T.pr i₀ ≫ T.inc i₀ = T.act (Matrix.single i₀ i₀ 1) ∧ ∀ y, D'.c (T.xi i₀ y) = D.c y ≫ T.inc i₀ := by
  first | exact @GlobalTheory.Mum.tens_inc_pr_facts | exact GlobalTheory.Mum.tens_inc_pr_facts | (intros; apply GlobalTheory.Mum.tens_inc_pr_facts <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.mumfordTensorData_matrixAction_ringHom_properties : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W), (∀ a, IsMonHom (T.act a)) ∧ T.act 1 = 𝟙 _ ∧ (∀ a b, T.act (a * b) = T.act b ≫ T.act a) ∧ ∀ a b, T.act (a + b) = padd D'.P.A (T.act a) (T.act b) := by
  first | exact @GlobalTheory.Mum.TensAct.act_ring | exact GlobalTheory.Mum.TensAct.act_ring | (intros; apply GlobalTheory.Mum.TensAct.act_ring <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.tensor_action_compatible_with_degeneration : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (s : SymUnit r), letI := T.mod s; ∀ (a : TensO s) (y : D'.X), D'.c (a • y) = D'.c y ≫ T.act (TensO.mat s a) := by
  first | exact @GlobalTheory.Mum.Tens.c_smul | exact GlobalTheory.Mum.Tens.c_smul | (intros; apply GlobalTheory.Mum.Tens.c_smul <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.integral_element_affine_section_generated : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S), Smooth G.hom → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)) (hpb : IsPullback α t G.hom M.gp) (W : G.left.Opens) (U : M.S.Opens) (hWU : W ≤ G.hom ⁻¹ᵁ U), IsAffineOpen W → IsAffineOpen U → ∀ f : Γ(Y, α ⁻¹ᵁ W), (α.app W).hom.IsIntegralElem f → ∃ (n : ℕ) (c : Fin n → Γ(G.left, W)) (b : Fin n → Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U)), (∀ m, (M.gp.app U).hom.IsIntegralElem (b m)) ∧ f = ∑ m, (α.app W).hom (c m) * (t.appLE (M.gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) (locInt_le_gen G.hom α t M.gp hpb.w W U hWU)).hom (b m) := by
  first | exact @GlobalTheory.Mum.eq_sum_of_isIntegral_genericChart | exact GlobalTheory.Mum.eq_sum_of_isIntegral_genericChart | (intros; apply GlobalTheory.Mum.eq_sum_of_isIntegral_genericChart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.mumfordTensorData_latticeFactor_props : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (s : SymUnit r) (i₀ : Fin r), letI := T.mod s; (∀ y, T.xp i₀ (T.xi i₀ y) = y) ∧ (∀ z, T.xi i₀ (T.xp i₀ z) = TensO.idem s i₀ • z) ∧ Function.Injective (fun y => star (TensO.idem s i₀) • TensO.binv s • T.xi i₀ y) ∧ ∀ z, ∃ y, star (TensO.idem s i₀) • z = star (TensO.idem s i₀) • TensO.binv s • T.xi i₀ y := by
  first | exact @GlobalTheory.Mum.tens_factor_latt | exact GlobalTheory.Mum.tens_factor_latt | (intros; apply GlobalTheory.Mum.tens_factor_latt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.rosatiAdj_mumfordTensorPower_of_posDef : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (T : Tens D.toPre D'.toPre W) (a : TensO (symUnitOf W h)), RosatiAdj D'.toPre.P.A D'.toPre.P.L (T.act (TensO.mat _ a)) (T.act (TensO.mat _ (star a))) := by
  first | exact @GlobalTheory.Mum.rosatiAdj_tens | exact GlobalTheory.Mum.rosatiAdj_tens | (intros; apply GlobalTheory.Mum.rosatiAdj_tens <;> assumption)
end
