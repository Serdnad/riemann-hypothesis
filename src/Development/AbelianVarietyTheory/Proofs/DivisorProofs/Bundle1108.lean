module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConductorSquareFlatBaseChangeSchemes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1056
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1074
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_local_generator_finite_cover_near_point : (∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (W : X.Opens), IsAffineOpen W → ∀ F : Set X, F.Finite → F ⊆ W → ∃ (V : X.Opens) (a : ∀ k, Γ(X, V ⊓ L.U k)ˣ), F ⊆ V ∧ GlobalTheory.Pinch.LocGen L V a) → ∀ (X X' : Scheme.{0}) (p : X' ⟶ X), IsFinite p → ∀ (L : LB X'), L.IsLB → ∀ x : X, ∃ (W : X.Opens) (a : ∀ k, Γ(X', p ⁻¹ᵁ W ⊓ L.U k)ˣ), x ∈ W ∧ GlobalTheory.Pinch.LocGen L (p ⁻¹ᵁ W) a := by
  first | exact @GlobalTheory.Pinch.locGen_near_fibre_of_finite | exact GlobalTheory.Pinch.locGen_near_fibre_of_finite | (intros; apply GlobalTheory.Pinch.locGen_near_fibre_of_finite <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.pinched_chart_off_closed_part_from_base : ∀ (R : Type) [CommRing R] (R' : Type) [CommRing R'] [Algebra R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (B' C Y : Scheme.{0}) (b' : B' ⟶ Sp R') (e : C ⟶ Sp (R ⧸ c)) (i : Y ⟶ B') (q : Y ⟶ C), SmoothOfRelativeDimension g b' → ∀ x : B', (b' ≫ spMap (algebraMap R R')) x ∉ Set.range (spMap (Ideal.Quotient.mk c)) → GlobalTheory.Pinch.Pinched g (spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) b' e i q x := by
  first | exact @GlobalTheory.Pinch.pinched_off | exact GlobalTheory.Pinch.pinched_off | (intros; apply GlobalTheory.Pinch.pinched_off <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.pinched_charts_restrict_matching_opens : ∀ (g : ℕ) (S S' Z B' C Y : Scheme.{0}) (s' : S' ⟶ S) (z : Z ⟶ S) (b' : B' ⟶ S') (e : C ⟶ Z) (i : Y ⟶ B') (q : Y ⟶ C), IsPullback i (q ≫ e) (b' ≫ s') z → IsPullback q (i ≫ b') (e ≫ z) s' → ∀ (V' : B'.Opens) (V : C.Opens), i ⁻¹ᵁ V' = q ⁻¹ᵁ V → ∃ (q₀ : (i ⁻¹ᵁ V').toScheme ⟶ V.toScheme), IsPullback (i ∣_ V') (q₀ ≫ V.ι ≫ e) ((V'.ι ≫ b') ≫ s') z ∧ IsPullback q₀ ((i ∣_ V') ≫ V'.ι ≫ b') ((V.ι ≫ e) ≫ z) s' ∧ ∀ x : V'.toScheme, GlobalTheory.Pinch.Pinched g s' z (V'.ι ≫ b') (V.ι ≫ e) (i ∣_ V') q₀ x → GlobalTheory.Pinch.Pinched g s' z b' e i q (V'.ι x) := by
  first | exact @GlobalTheory.Pinch.restrict_pinched | exact GlobalTheory.Pinch.restrict_pinched | (intros; apply GlobalTheory.Pinch.restrict_pinched <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.pinchingSquare_unitsPatch : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → GlobalTheory.Pinch.Cond p i → GlobalTheory.Pinch.UnitsPatch p i i' p' := by
  first | exact @GlobalTheory.Pinch.unitsPatch | exact GlobalTheory.Pinch.unitsPatch | (intros; apply GlobalTheory.Pinch.unitsPatch <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_unit_ratio_local_generators_common_pullback : ∀ (X' Z Z' : Scheme.{0}) (i' : Z' ⟶ X') (p' : Z' ⟶ Z) (L' : LB X') (N : LB Z), L'.IsLB → N.IsLB → ∀ (w : LB.Iso (L'.pull i') (N.pull p')), w.IsGen → ∀ (V' : X'.Opens) (V : Z.Opens) (a : ∀ k, Γ(X', V' ⊓ L'.U k)ˣ) (b : ∀ l, Γ(Z, V ⊓ N.U l)ˣ), GlobalTheory.Pinch.LocGen L' V' a → GlobalTheory.Pinch.LocGen N V b → ∀ O : Z'.Opens, O ≤ i' ⁻¹ᵁ V' → O ≤ p' ⁻¹ᵁ V → ∃ u : Γ(Z', O)ˣ, ∀ (z : Z') (k : L'.ι) (l : N.ι), z ∈ O → i' z ∈ L'.U k → p' z ∈ N.U l → gm p' z (V ⊓ N.U l) (b l) = gm (𝟙 Z') z ((N.pull p').U (fun _ ↦ l) ⊓ (L'.pull i').U (fun _ ↦ k)) (w.s (fun _ ↦ l, fun _ ↦ k)) * (gm (𝟙 Z') z O u * gm i' z (V' ⊓ L'.U k) (a k)) := by
  first | exact @GlobalTheory.Pinch.exists_ratio_unit | exact GlobalTheory.Pinch.exists_ratio_unit | (intros; apply GlobalTheory.Pinch.exists_ratio_unit <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lineBundle_iso_pullback_of_local_unit_generators : ∀ (X Y : Scheme.{0}) (f : Y ⟶ X) (L : LB Y) (J : Type) (W : J → X.Opens) (g : ∀ x y, Γ(X, W x ⊓ W y)ˣ) (s : ∀ x k, Γ(Y, L.U k ⊓ f ⁻¹ᵁ W x)ˣ), (∀ x, GlobalTheory.PinchLift.GenOn L (f ⁻¹ᵁ W x) (s x)) → (∀ x y (t : Y) (k : L.ι), f t ∈ W x → f t ∈ W y → t ∈ L.U k → gm f t (W x ⊓ W y) (g x y) = gm (𝟙 Y) t (L.U k ⊓ f ⁻¹ᵁ W y) (s y k) * (gm (𝟙 Y) t (L.U k ⊓ f ⁻¹ᵁ W x) (s x k))⁻¹) → LBIso L ((⟨J, W, g⟩ : LB X).pull f) := by
  first | exact @GlobalTheory.PinchLift.lbIso_pull_of_genOn | exact GlobalTheory.PinchLift.lbIso_pull_of_genOn | (intros; apply GlobalTheory.PinchLift.lbIso_pull_of_genOn <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_localUnitGenerator_of_lineBundleLocalSectionFamily : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (J : Type) (D : J → X.Opens) (k : J → L.ι) (hD : ∀ j, D j ≤ L.U (k j)) (e : ∀ j, Γ(X, D j)), GlobalTheory.Pinch.IsSecFam L D k hD e → ∃ (V : X.Opens) (a : ∀ i, Γ(X, V ⊓ L.U i)ˣ), (∀ j (x : X) (h : x ∈ D j), IsUnit ((X.presheaf.germ (D j) x h).hom (e j)) → x ∈ V) ∧ GlobalTheory.Pinch.LocGen L V a := by
  first | exact @GlobalTheory.Pinch.exists_locGen_of_secFam | exact GlobalTheory.Pinch.exists_locGen_of_secFam | (intros; apply GlobalTheory.Pinch.exists_locGen_of_secFam <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.conductorSquare_flat_baseChange_schemes : ∀ (R : Type) [CommRing R] (R' : Type) [CommRing R'] [Algebra R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (X X' Z : Scheme.{0}) (u : X ⟶ Sp R) (p : X' ⟶ X) (u' : X' ⟶ Sp R') (i : Z ⟶ X) (v : Z ⟶ Sp (R ⧸ c)), Flat u → IsPullback p u' u (spMap (algebraMap R R')) → IsPullback i v u (spMap (Ideal.Quotient.mk c)) → GlobalTheory.Pinch.Cond p i := by
  first | exact @GlobalTheory.Pinch.FlatSq.cond_of_flat | exact GlobalTheory.Pinch.FlatSq.cond_of_flat | (intros; apply GlobalTheory.Pinch.FlatSq.cond_of_flat <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

theorem _root_.GlobalTheory.T.cechTrivial_pullback_of_isPullbackGenerator : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y) (M : LB Y) (e : ∀ k, Γ(X, p ⁻¹ᵁ M.U k)ˣ), IsPullGen p M e → Triv (M.pull p) := by
  first | exact @GlobalTheory.CharKer.triv_pull_of_isPullGen | exact GlobalTheory.CharKer.triv_pull_of_isPullGen | (intros; apply GlobalTheory.CharKer.triv_pull_of_isPullGen <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

theorem _root_.GlobalTheory.T.character_eq_one_of_descended_lineBundle_trivial : ∀ (K : Type) [Field K] (A A' N T : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') (χ : Γ((N ⊗ T).left, ⊤)ˣ) (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ), IsAbelianScheme A → IsMonHom q → IsPullback i (toUnit N) q η[A'] → M.IsLB → IsEquivGen i q χ M e → Triv M → χ = 1 := by
  first | exact @GlobalTheory.CharKer.character_eq_one_of_triv | exact GlobalTheory.CharKer.character_eq_one_of_triv | (intros; apply GlobalTheory.CharKer.character_eq_one_of_triv <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.factors_fibreOverPoint_iff_factors_product : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left) {H : Over (Sp R)} (h : H ⟶ A ⊗ T) (Y : Over (Sp V)) (x : Y ⟶ GlobalTheory.TwistFlat.bc A φ), (∃ y : Y ⟶ GlobalTheory.TwistFlat.ker A φ h, y ≫ GlobalTheory.TwistFlat.kerι A φ h = x) ↔ ∃ z : GlobalTheory.TwistFlat.up φ Y ⟶ H, z ≫ h = lift (GlobalTheory.TwistFlat.upa φ x) (GlobalTheory.TwistFlat.upt φ Y) := by
  first | exact @GlobalTheory.TwistFlat.factor_ker_iff | exact GlobalTheory.TwistFlat.factor_ker_iff | (intros; apply GlobalTheory.TwistFlat.factor_ker_iff <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isClosedImmersion_fibreOverPointToBaseChange : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left) {H : Over (Sp R)} (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → IsClosedImmersion (GlobalTheory.TwistFlat.kerι A φ h).left := by
  first | exact @GlobalTheory.TwistFlat.isClosedImmersion_kerι | exact GlobalTheory.TwistFlat.isClosedImmersion_kerι | (intros; apply GlobalTheory.TwistFlat.isClosedImmersion_kerι <;> assumption)
end
