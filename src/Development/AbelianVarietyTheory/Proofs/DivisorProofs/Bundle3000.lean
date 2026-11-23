module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextensionSecondLawCommutativityValue
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2895
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle089
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2897
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle536
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.psiValue_isUnit_of_psiUnitOn_localRing : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (W : (Sp R).Opens) (χ : D.X), PsiUnitOn D χ W → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Subring F) [IsLocalRing T] (φ₁ : R →+* T), (∀ r, (φ₁ r : F) = algebraMap (FractionRing R) F (algebraMap R _ r)) → spMap φ₁ (closedPoint T) ∈ W → ∀ (J₀ : D.P.A.left → D.P.L.ι), (∀ x, x ∈ D.P.L.U (J₀ x)) → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), (∀ ψ : Sp T ⟶ D.P.A.left, J (spMap T.subtype ≫ ψ) = J₀ (ψ (closedPoint T))) → ∃ u : Tˣ, (GlobalTheory.BXOf.sig F (val (D.psi χ) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (closedPoint F) J) : F) = ((u : T) : F) := by
  first | exact @GlobalTheory.PsiValUnit.psi_val_unit_of_psiUnitOn | exact GlobalTheory.PsiValUnit.psi_val_unit_of_psiUnitOn | (intros; apply GlobalTheory.PsiValUnit.psi_val_unit_of_psiUnitOn <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_transported_generator_descend_bijective_app : ∀ {X X' Y Y' : Scheme.{0}} {K : Type} [Fintype K] {M : LB X} {L : LB X'} {F : X' ⟶ X} {w : LB.Iso L (M.pull F)}, PGen w → M.IsLB → L.IsLB → ∀ (π : Y' ⟶ Y), (∀ V : Y.Opens, Function.Bijective (π.app V).hom) → ∀ {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)}, (∀ k, φ' k ≫ F = π ≫ φ k) → ∀ {ε : K → ℤ} (a : LB.Gen (LB.LinComb L φ' ε)), a.IsGen → ∃ t : LB.Gen (LB.LinComb M φ ε), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (I : (Z ⟶ X) → M.ι) (J : (Z ⟶ X') → L.ι), Good M z I → Good L z J → val t (r ≫ π) z I = (∏ k, gw w (r ≫ φ' k) z (I ((r ≫ φ' k) ≫ F)) (J (r ≫ φ' k)) ^ ε k) * val a r z J := by
  first | exact @GlobalTheory.Mum.BijDescent.exists_descend_bij | exact GlobalTheory.Mum.BijDescent.exists_descend_bij | (intros; apply GlobalTheory.Mum.BijDescent.exists_descend_bij <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two


theorem _root_.GlobalTheory.T.generator_val_eq_one_of_generic_spec_domain : ∀ (R : Type) [CommRing R] [IsDomain R] {X : Scheme.{0}} (L : LB X), L.IsLB → ∀ {K : Type} [Fintype K] (φ : K → (Spec (CommRingCat.of R) ⟶ X)) (ε : K → ℤ), FormEq φ ε (PEmpty.elim : PEmpty → (Spec (CommRingCat.of R) ⟶ X)) (PEmpty.elim : PEmpty → ℤ) → ∀ t : LB.Gen (LB.LinComb L φ ε), t.IsGen → (∀ (z : (TK R).left) (J : ((TK R).left ⟶ X) → L.ι), Good L z J → val t (jK R) z J = 1) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J → val t r z J = 1 := by
  first | exact @GlobalTheory.Mum.GenOne.val_eq_one_of_generic | exact GlobalTheory.Mum.GenOne.val_eq_one_of_generic | (intros; apply GlobalTheory.Mum.GenOne.val_eq_one_of_generic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_linCombPullbackTransportIso_with_values : ∀ {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {K I : Type} [Fintype K] [Fintype I] (ψ : K → (X' ⟶ X)) (δ : K → ℤ) (w : LB.Iso L' (LB.LinComb L ψ δ)), w.IsGen → L.IsLB → L'.IsLB → ∀ (σ : I → (Y ⟶ X')) (e : I → ℤ), ∃ v : LB.Iso (LB.LinComb L' σ e) (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2)), v.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι), Good L z J → Good L' z J' → gm q z _ (v.s (fun p => J (q ≫ σ p.1 ≫ ψ p.2), fun i => J' (q ≫ σ i))) = ∏ i, gm (q ≫ σ i) z _ (w.s (fun k => J (q ≫ σ i ≫ ψ k), J' (q ≫ σ i))) ^ e i := by
  first | exact @GlobalTheory.Mum.exists_transIso_linComb | exact GlobalTheory.Mum.exists_transIso_linComb | (intros; apply GlobalTheory.Mum.exists_transIso_linComb <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

theorem _root_.GlobalTheory.T.thetaGroupAction_compat_fibreIso : ∀ {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} (hL : L.IsLB) (hL' : L'.IsLB) {T : Over S} {T' : Over S'} (f : (T' ⊗ A').left ⟶ (T ⊗ A).left) [IsIso f] (k : ℤ) (θ : ThetaGrp A L k T) (θ' : ThetaGrp A' L' k T') (Ψ : ∀ {Z : Scheme.{0}}, (Z ⟶ (T' ⊗ A').left) → ∀ z : Z, ((Z ⟶ A.left) → L.ι) → ((Z ⟶ A'.left) → L'.ι) → (Z.presheaf.stalk z)ˣ) (hT : f ≫ (translT A θ.pt).left = (translT A' θ'.pt).left ≫ f) (H : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ q z J' * (Ψ (q ≫ (translT A' θ'.pt).left) z J J' ^ k)⁻¹) (σ σ' : LB.Sec (LPow A' L' k T')) (τ τ' : LB.Sec (LPow A L k T)) (hσ : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) τ (q ≫ f) z J = (Ψ q z J J' ^ k).val * sval (L := L') (φ := fun _ : Fin 1 => (snd T' A').left) (ε := fun _ => k) σ q z J') (hσ' : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) τ' (q ≫ f) z J = (Ψ q z J J' ^ k).val * sval (L := L') (φ := fun _ : Fin 1 => (snd T' A').left) (ε := fun _ => k) σ' q z J') (hact : IsActOf A' L' k θ' σ σ'), IsActOf A L k θ τ τ' := by
  first | exact @GlobalTheory.ThetaMove.isActOf_of_fibreIso | exact GlobalTheory.ThetaMove.isActOf_of_fibreIso | (intros; apply GlobalTheory.ThetaMove.isActOf_of_fibreIso <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

theorem _root_.GlobalTheory.T.thetaGroup_powValue_eq_of_conjugate_torsion : ∀ {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {T : Over S} {T' : Over S'} (f : (T' ⊗ A').left ⟶ (T ⊗ A).left) (k : ℤ) (N : ℕ) (θ : ThetaGrp A L k T) (θ' : ThetaGrp A' L' k T') (Ψ : ∀ {Z : Scheme.{0}}, (Z ⟶ (T' ⊗ A').left) → ∀ z : Z, ((Z ⟶ A.left) → L.ι) → ((Z ⟶ A'.left) → L'.ι) → (Z.presheaf.stalk z)ˣ) (hT : ∀ i : ℕ, f ≫ (translT A (θ.pt ^ i)).left = (translT A' (θ'.pt ^ i)).left ≫ f) (hN : θ'.pt ^ N = 1) (H : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ q z J' * (Ψ (q ≫ (translT A' θ'.pt).left) z J J' ^ k)⁻¹) (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J' (hJ : Good L z J) (hJ' : Good L' z J'), val (powGen A L k θ N) (q ≫ f) z J = val (powGen A' L' k θ' N) q z J' := by
  first | exact @GlobalTheory.ThetaPowConj.val_powGen_transport | exact GlobalTheory.ThetaPowConj.val_powGen_transport | (intros; apply GlobalTheory.ThetaPowConj.val_powGen_transport <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

theorem _root_.GlobalTheory.T.thetaGroup_symmetryValue_eq_of_conjugate : ∀ {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] [IsCommMonObj A'] {L : LB A.left} {L' : LB A'.left} {T : Over S} {T' : Over S'} (f : (T' ⊗ A').left ⟶ (T ⊗ A).left) (k : ℤ) (θ : ThetaGrp A L k T) (θ' : ThetaGrp A' L' k T') (ν : LB.Gen (negLB A L k T)) (ν' : LB.Gen (negLB A' L' k T')) (Ψ : ∀ {Z : Scheme.{0}}, (Z ⟶ (T' ⊗ A').left) → ∀ z : Z, ((Z ⟶ A.left) → L.ι) → ((Z ⟶ A'.left) → L'.ι) → (Z.presheaf.stalk z)ˣ) (hT : f ≫ (translT A θ.pt⁻¹).left = (translT A' θ'.pt⁻¹).left ≫ f) (hneg : f ≫ (negT A T).left = (negT A' T').left ≫ f) (H : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ q z J' * (Ψ (q ≫ (translT A' θ'.pt).left) z J J' ^ k)⁻¹) (Hν : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) ν (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (snd T' A' ≫ (GrpObj.inv : A' ⟶ A')).left]) (ε := ![k, -k]) ν' q z J' * (Ψ (q ≫ (negT A' T').left) z J J' ^ k)⁻¹) (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J' (hJ : Good L z J) (hJ' : Good L' z J'), val (symGen A L k θ ν) (q ≫ f) z J = val (symGen A' L' k θ' ν') q z J' := by
  first | exact @GlobalTheory.ThetaSymTransport.val_symGen_eq | exact GlobalTheory.ThetaSymTransport.val_symGen_eq | (intros; apply GlobalTheory.ThetaSymTransport.val_symGen_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two


theorem _root_.GlobalTheory.T.rosatiGenerator_value_one_zero_first_factor : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), L.IsLB → IsAbelianScheme A → ∀ (f g : A ⟶ A) [IsMonHom f] [IsMonHom g] (u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)), u.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L) → ∀ (T : Over S) (y : T ⟶ A) (z : T.left) (J : (T.left ⟶ A.left) → L.ι), Good L z J → val u (lift (1 : T ⟶ A) y).left z J = 1 := by
  first | exact @GlobalTheory.RosZeroLeft.val_lift_one_left | exact GlobalTheory.RosZeroLeft.val_lift_one_left | (intros; apply GlobalTheory.RosZeroLeft.val_lift_one_left <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat.Gens

theorem res_ι_app {X : Scheme.{0}} (U : X.Opens) (V : U.toScheme.Opens) (x : Γ(X, U.ι ''ᵁ V))
    (hle : V ≤ U.ι ⁻¹ᵁ (U.ι ''ᵁ V)) :
    (U.toScheme.presheaf.map (homOfLE hle).op).hom ((U.ι.app (U.ι ''ᵁ V)).hom x) = x := by
  have h1 := Scheme.Hom.appIso_hom U.ι V
  rw [Scheme.Opens.ι_appIso] at h1
  have h3 := congrArg (fun f => f.hom x) h1
  simp only [Iso.refl_hom, CommRingCat.hom_comp, RingHom.comp_apply] at h3
  exact (congrArg (fun f => (U.toScheme.presheaf.map f).hom ((U.ι.app (U.ι ''ᵁ V)).hom x))
    (Subsingleton.elim (homOfLE hle).op _)).trans h3.symm

theorem gs_ι {X : Scheme.{0}} (U : X.Opens) (j : X ⟶ U.toScheme) (hj : j ≫ U.ι = 𝟙 X) (V : U.toScheme.Opens)
    (x : Γ(X, U.ι ''ᵁ V)) (y : X) (hy : j y ∈ V) : gs j y V x = gs (𝟙 X) y (U.ι ''ᵁ V) x := by
  have hle : V ≤ U.ι ⁻¹ᵁ (U.ι ''ᵁ V) := (Scheme.Hom.preimage_image_eq U.ι V).ge
  have e := gs_res j y hle hy ((U.ι.app (U.ι ''ᵁ V)).hom x)
  rw [res_ι_app] at e
  rw [e, gs_pull j U.ι y _ (hle hy), hj]

theorem gens : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R), ∃ N : ℕ, 1 ≤ N ∧ ∃ (Ix : Type) (U : Ix → Q.P.A.left.Opens) (M : Ix → Type) (r : ∀ i, M i → Γ(Q.P.A.left, U i)), (⨆ i, U i = ⊤) ∧ (∀ i, IsAffineOpen (U i)) ∧ (∀ i, Function.Surjective (MvPolynomial.eval₂Hom (Q.P.A.hom.appLE ⊤ (U i) (fun _ _ => trivial)).hom (r i))) ∧ ∀ i j, ∃ σ σ' : Q.SecB N 0, ∀ z ∈ U i, ∀ J, Good Q.P.L z J → IsUnit (sval σ' (𝟙 _) z J) ∧ sval σ (𝟙 _) z J = gs (𝟙 _) z (U i) (r i j) * sval σ' (𝟙 _) z J := by
  intro R _ _ Q
  obtain ⟨N, hN, M, s, hcov, hs⟩ := Q.P.ample ⊤ (isAffineOpen_top _)
  choose haff r hr hsurj using hs
  let ιU := (Q.P.A.hom ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens)).ι
  let j : Q.P.A.left ⟶ (Q.P.A.hom ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens)).toScheme := Q.P.A.left.topIso.inv
  have hj : j ≫ ιU = 𝟙 _ := by
    show Q.P.A.left.topIso.inv ≫ (⊤ : Q.P.A.left.Opens).ι = _
    rw [← Scheme.topIso_hom, Iso.inv_hom_id]
  have hιj : ιU ≫ j = 𝟙 _ := by
    show (⊤ : Q.P.A.left.Opens).ι ≫ Q.P.A.left.topIso.inv = _
    rw [← Scheme.topIso_hom, Iso.hom_inv_id]; rfl
  have hjι : ∀ w, j (ιU w) = w := fun w => by show (ιU ≫ j).base w = w; rw [hιj]; rfl
  have hfe : FormEq (K := Fin N) (fun _ => 𝟙 Q.P.A.left) (fun _ => (1 : ℤ)) (Q.famφB 0) (DegPre.famε N) := by
    intro U _ h
    refine Eq.trans ?_ (GlobalTheory.Mum.OriginSec.formEq_zero Q N U h)
    simp [Finset.prod_const, Fin.prod_univ_one]
  have hσ : ∀ a, ∃ σ : Q.SecB N 0, ∀ (z : Q.P.A.left) J, Good Q.P.L z J → sval σ (𝟙 _) z J = sval (s a) j z J := by
    intro a
    obtain ⟨s', hs'⟩ := GlobalTheory.UU.exists_pullSec_sval
      (s a : LB.Sec (LB.LinComb Q.P.L (K := Fin N) (fun _ => ιU) (fun _ => (1 : ℤ)))) j
      (fun _ : Fin N => 𝟙 Q.P.A.left) (fun _ => hj)
    obtain ⟨σ, hσ⟩ := exists_sec Q.P.isLB hfe s'
    exact ⟨σ, fun z J hJ => (hσ _ _ z J hJ).trans ((hs' _ _ z J hJ).trans (by rw [Category.id_comp]))⟩
  choose σ hσv using hσ
  refine ⟨N, hN, Fin (M + 1), fun a => ιU ''ᵁ nonzeroLocus (s a), fun _ => Fin (M + 1), fun a b => r a b, ?_, ?_, ?_, ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (show j y ∈ ⨆ a, nonzeroLocus (s a) by rw [hcov]; trivial)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, ⟨j y, ha, show (j ≫ ιU).base y = y by rw [hj]; rfl⟩⟩
  · exact fun a => (haff a).image_of_isOpenImmersion ιU
  · intro a
    have key : ∀ (U U' : (Spec (CommRingCat.of R)).Opens) (_ : U = U') (W : Q.P.A.left.Opens) e e'
        (rr : Fin (M + 1) → Γ(Q.P.A.left, W)),
        Function.Surjective (MvPolynomial.eval₂Hom (Q.P.A.hom.appLE U' W e').hom rr) →
        Function.Surjective (MvPolynomial.eval₂Hom (Q.P.A.hom.appLE U W e).hom rr) := by
      rintro _ _ rfl _ _ _ _ h; exact h
    have e2 := morphismRestrict_appLE Q.P.A.hom ⊤ ⊤ (nonzeroLocus (s a)) le_top
    have h' := (congrArg (fun g => Function.Surjective (MvPolynomial.eval₂Hom (CommRingCat.Hom.hom g) (r a))) e2).mp (hsurj a)
    exact key ⊤ ((⊤ : (Spec (CommRingCat.of R)).Opens).ι ''ᵁ ⊤) (Scheme.Opens.ι_image_top _).symm
      (ιU ''ᵁ nonzeroLocus (s a)) _ _ (r a) h'
  · intro a b
    refine ⟨σ b, σ a, fun z hz J hJ => ?_⟩
    obtain ⟨w, hw, rfl⟩ := hz
    rw [hσv _ _ _ hJ, hσv _ _ _ hJ]
    have hm := hJ.mem (fun _ : Fin N => ιU) j
    have hw' : j (ιU w) ∈ nonzeroLocus (s a) := by rw [hjι]; exact hw
    refine ⟨(GlobalTheory.Mum.OriginSec.isUnit_sval_iff' (s a) j (ιU w) hJ).2 hw', ?_⟩
    have hm' : j (ιU w) ∈ nonzeroLocus (s a) ⊓ (powOver Q.P.A Q.P.L ⊤ N).U (fun _ => J (j ≫ ιU)) := ⟨hw', hm⟩
    have e := congrArg (gs j (ιU w) _) (hr a b (fun _ => J (j ≫ ιU)))
    rw [gs_res _ _ _ hm', gs_mul _ _ _ hm', gs_res _ _ _ hm', gs_res _ _ _ hm'] at e
    rw [gs_ι _ j hj _ (r a b) _ hw'] at e
    exact e
end GlobalTheory.Heat.Gens
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_section_pullback_twoTorsion_translation : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L L₂ : LB G.left), L.IsLB → L₂.IsLB → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → ∀ wL : LB.Iso L₂ (L.pull ((toUnit G ≫ a) * 𝟙 G).left), wL.IsGen → ∀ σ : H0 L 1, ∃ σ₂ : H0 L₂ 1, (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → L.ι) (N' : (Z ⟶ G.left) → L₂.ι), Geo.Tor.Good L z N → Geo.Tor.Good L₂ z N' → Geo.Tor.sval σ (r ≫ ((toUnit G ≫ a) * 𝟙 G).left) z N = (Geo.Tor.gw wL r z (N (r ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' r)).val * Geo.Tor.sval σ₂ r z N') ∧ ((∀ j, σ₂.f j = 0) → ∀ j, σ.f j = 0) := by
  first | exact @GlobalTheory.twoTors_secPull | exact GlobalTheory.twoTors_secPull | (intros; apply GlobalTheory.twoTors_secPull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.sectionExpansion_scale_base_element : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU I D A G) (k : ℕ) (q : R) (σ τ : U.SecGT (𝟙_ _) k) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) k α), ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ G).hom q σ τ → (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) → U.ExpT (𝟙_ _) k τ g → U.ExpT (𝟙_ _) k σ f := by
  first | exact @GlobalTheory.UU.expT_scale | exact GlobalTheory.UU.expT_scale | (intros; apply GlobalTheory.UU.expT_scale <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.lineBundleSection_baseMul_cancel_flat_domain : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), Flat p → ∀ (L : LB X) (q : R), q ≠ 0 → ∀ s t t' : LB.Sec L, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p q s t → ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p q s t' → t = t' := by
  first | exact @GlobalTheory.Mum.secIsMul_cancel | exact GlobalTheory.Mum.secIsMul_cancel | (intros; apply GlobalTheory.Mum.secIsMul_cancel <;> assumption)
end
