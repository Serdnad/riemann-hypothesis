module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCyclotomicBaseRingInvertingPrime
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModelFiniteOverModuliModelDescends
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapDegreeEqExpCharPowMulCardKernel
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle036
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomFromConstThickeningOfDerivation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle037
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle038
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
theorem _root_.GlobalTheory.T.exists_two_inert_odd_primes_coprime_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), (∃ n n' : ℕ, AuxiliaryInertOddPrime H n ∧ AuxiliaryInertOddPrime H n' ∧ n ≠ n') ∧ ∀ n : ℕ, AuxiliaryInertOddPrime H n → ∀ l : Level H, n.Coprime l.M := by
  first | exact @GlobalTheory.Models.exists_two_auxiliary_inert_odd_primes_coprime_level | exact GlobalTheory.Models.exists_two_auxiliary_inert_odd_primes_coprime_level | (intros; apply GlobalTheory.Models.exists_two_auxiliary_inert_odd_primes_coprime_level <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_cyclotomic_base_ring_inverting_prime : ∀ (n e p k : ℕ), n.Prime → p.Prime → n ≠ p → 1 ≤ e → k = n ^ e → ∃ (o : Type) (_ : CommRing o) (b : TBase o k) (em : o →+* ℂ) (j : o →+* ZP p k), ArBase em ∧ j (b.ζ : o) = zetaZP p k ∧ (∀ x, ((j x : ZP p k) : ℂ) = em x) ∧ ∀ (K : Type) [Field K] (y : Sp (DualNumber K) ⟶ Sp (ZP p k)), y = constPt y := by
  first | exact @GlobalTheory.ZM.CycBase.exists_base | exact GlobalTheory.ZM.CycBase.exists_base | (intros; apply GlobalTheory.ZM.CycBase.exists_base <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
theorem _root_.GlobalTheory.T.model_finite_over_moduliModel_descends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O₀ : Type) [CommRing O₀] (β₀ : O₀ →+* KA l) (C : Cpt Xo.s Xo.univ.t β₀) (b : O₀ →+* O) (_ : (ofModel Y).Above C b (pullback.fst _ _) Y.m0.toSABMap), IsDedFrac β₀ → IsDedFrac β → β.comp b = (IntermediateField.inclusion c.le).toRingHom.comp β₀ → Y.Descends := by
  first | exact @GlobalTheory.descends_of_above | exact GlobalTheory.descends_of_above | (intros; apply GlobalTheory.descends_of_above <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

theorem _root_.GlobalTheory.T.mapDegree_eq_expChar_pow_mul_card_kernel : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (α : P.A ⟶ P.A), IsMonHom α → IsFinite α.left → Finite {x : Out.baseOver (Sp K) ⟶ P.A // x ≫ α = 1} ∧ ∃ e : ℕ, MapDeg α.left (ringExpChar K ^ e * Nat.card {x : Out.baseOver (Sp K) ⟶ P.A // x ≫ α = 1}) := by
  first | exact @GlobalTheory.mapDeg_eq_pow_mul_card_ker | exact GlobalTheory.mapDeg_eq_pow_mul_card_ker | (intros; apply GlobalTheory.mapDeg_eq_pow_mul_card_ker <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
theorem _root_.GlobalTheory.T.finrank_symm_antilinear_comm_CM_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g p q : ℕ) (ρ₀ : ℂ) (Hm : Matrix (Fin g) (Fin g) ℂ) (F : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (S : Submodule ℂ (Matrix (Fin g) (Fin g) ℂ)), ρ₀ ^ 2 = -(H.d : ℂ) → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ τ : 𝓞 E →+* ℂ, Module.finrank ℂ ↥(⨅ a, Module.End.eigenspace (F a) (τ a)) = if τ H.rt = ρ₀ then p else q) → (∀ Θ ∈ S, IsSymm Hm Θ ∧ ∀ a, Comm Θ (F a)) → Module.finrank ℂ S ≤ Module.finrank ℚ E / 2 * p * q := by
  first | exact @GlobalTheory.KS.DimPEL.finrank_symm_comm_le | exact GlobalTheory.KS.DimPEL.finrank_symm_comm_le | (intros; apply GlobalTheory.KS.DimPEL.finrank_symm_comm_le <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
theorem _root_.GlobalTheory.T.exists_local_derivation_extension_of_affine : ∀ (R : Type) [CommRing R] (Y X : Scheme.{0}) (q : Y ⟶ Sp ℂ) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → ℂ) (W₀ : X.Opens), IsAffineOpen W₀ → ∀ d₀ : Γ(X, W₀) → Γ(Y, m ⁻¹ᵁ W₀), (∀ a b, d₀ (a + b) = d₀ a + d₀ b) → (∀ a b, d₀ (a * b) = (m.app W₀).hom a * d₀ b + (m.app W₀).hom b * d₀ a) → (∀ r, d₀ (constFn p W₀ r) = constFn q (m ⁻¹ᵁ W₀) (D r)) → ∃ d, LocDer q p m D W₀ d ∧ d W₀ = d₀ := by
  first | exact @GlobalTheory.LocDerExt.exists_locDer | exact GlobalTheory.LocDerExt.exists_locDer | (intros; apply GlobalTheory.LocDerExt.exists_locDer <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
theorem _root_.GlobalTheory.T.exists_goodUniformisation_kodairaSpencer : ThetaUnifAV → ∀ P₀ : Out.PolAV (Sp ℂ), ∃ (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ ∧ ∀ w : Fin P₀.g → ℂ, KSRel u P₀.A.hom (𝟙 _) (fun _ => 0) 0 (fun z W f => fderiv ℂ (fn u (𝟙 _) W f) z w) := by
  first | exact @GlobalTheory.KSInh.exists_goodU_ksRel | exact GlobalTheory.KSInh.exists_goodU_ksRel | (intros; apply GlobalTheory.KSInh.exists_goodU_ksRel <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
theorem _root_.GlobalTheory.T.existsUnique_section_of_locally_given_values : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (O : P₀.A.left.Opens) (h : (Fin P₀.g → ℂ) → ℂ), (∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → ∃ (O' : P₀.A.left.Opens) (a : Γ(P₀.A.left, O')), O' ≤ O ∧ ⊤ ≤ (u.ex z).left ⁻¹ᵁ O' ∧ ∀ z', ⊤ ≤ (u.ex z').left ⁻¹ᵁ O' → valAt' (u.ex z').left O' a = h z') → ∃! a : Γ(P₀.A.left, O), ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → valAt' (u.ex z).left O a = h z := by
  first | exact @GlobalTheory.existsUnique_section_of_locally_regular | exact GlobalTheory.existsUnique_section_of_locally_regular | (intros; apply GlobalTheory.existsUnique_section_of_locally_regular <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
theorem _root_.GlobalTheory.T.germDerivation_iff_dualNumberPoint : ∀ (X : Scheme.{0}) (y : Sp ℂ ⟶ X), (∀ δ, PtDer y δ → ∃! v : Sp (DualNumber ℂ) ⟶ X, (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ v = y ∧ ∀ (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)), TrivSqZeroExt.snd (show DualNumber ℂ from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.appLE W ⊤ h).hom f)) = δ W f) ∧ ∀ v : Sp (DualNumber ℂ) ⟶ X, (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ v = y → ∃ δ, PtDer y δ ∧ ∀ (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)), TrivSqZeroExt.snd (show DualNumber ℂ from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.appLE W ⊤ h).hom f)) = δ W f := by
  first | exact @GlobalTheory.KS.ptDer_iff_dualPoint | exact GlobalTheory.KS.ptDer_iff_dualPoint | (intros; apply GlobalTheory.KS.ptDer_iff_dualPoint <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.exists_hom_from_const_thickening_of_derivation : ∀ (Y Y' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → ∀ (R : Type) [CommRing R] (xD : R →+* DualNumber ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : Y ⟶ X) (d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)), m ≫ p = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ spMap xD → LocDer q p m (fun r => (xD r).snd) ⊤ d → ∃ Φ : Y' ⟶ X, j ≫ Φ = m ∧ Φ ≫ p = π ≫ spMap xD := by
  first | exact @GlobalTheory.KS.DerMor.exists_mor | exact GlobalTheory.KS.DerMor.exists_mor | (intros; apply GlobalTheory.KS.DerMor.exists_mor <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
theorem _root_.GlobalTheory.T.endo_constant_family_dualNumbers_eq_baseChange : Out.Laws → Out.Laws2 → ∀ (P₀ : Out.PolAV (Sp ℂ)), ∀ (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (ρ : A'.left ⟶ P₀.A.left) (j : P₀.A.left ⟶ A'.left), IsConst A' P₀.A ρ j → ∀ (f' : A' ⟶ A') (f₀ : P₀.A ⟶ P₀.A), IsAbelianScheme A' → IsMonHom f' → IsMonHom f₀ → j ≫ f'.left = f₀.left ≫ j → f'.left ≫ ρ = ρ ≫ f₀.left := by
  first | exact @GlobalTheory.ConstEndo.endo_comp_proj | exact GlobalTheory.ConstEndo.endo_comp_proj | (intros; apply GlobalTheory.ConstEndo.endo_comp_proj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.isSectionCoordinateVector_of_locally_on_ring : ∀ (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec) (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : I → R), M.IsLB → Ideal.span (Set.range v) = ⊤ → (∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R'), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ SecCoord M th (spMap φ ≫ x) (fun i => φ (v i))) → SecCoord M th x v := by
  first | exact @GlobalTheory.ZM.secCoord_of_locally | exact GlobalTheory.ZM.secCoord_of_locally | (intros; apply GlobalTheory.ZM.secCoord_of_locally <;> assumption)
end
