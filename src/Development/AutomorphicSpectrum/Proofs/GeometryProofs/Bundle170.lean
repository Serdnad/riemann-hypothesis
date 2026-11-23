module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Order.CompletePartialOrder
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle044
public import Mathlib.RingTheory.DedekindDomain.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.WeilBound.CoreStatements.AmpleLineBundles.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle021
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle163
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle164
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle092
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle005
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.HtExists
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle165
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.StratLie

open GlobalTheory.CompanionTheory.Ar.TorusModel

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X]

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]
  rfl

theorem killed_of_eq {u : splitTorus S X ⟶ G} {Y : AddSubgroup X} {B : Type} [CommRing B] {b : Sp B ⟶ S}
    (h : KillsOver u Y b) {A : Type} [CommRing A] (g : B →+* A) {a : Sp A ⟶ S} (ha : a = spMap g ≫ b)
    (t : Over.mk a ⟶ splitTorus S X) (ht : ∀ y ∈ Y, charVal t y = 1) : t ≫ u = 1 := by
  subst ha
  exact h A g t ht

theorem killsOver_comp {u : splitTorus S X ⟶ G} {Y : AddSubgroup X} {B C : Type} [CommRing B] [CommRing C]
    (c : B →+* C) {b : Sp B ⟶ S} (h : KillsOver u Y b) : KillsOver u Y (spMap c ≫ b) := by
  intro A _ g t ht
  refine killed_of_eq h (g.comp c) ?_ t ht
  rw [← Category.assoc, spMap_comp_spMap]

theorem killsOver_descent [IsSeparated G.hom] {u : splitTorus S X ⟶ G} {Y : AddSubgroup X} {κ k : Type}
    [Field κ] [Field k] (c : κ →+* k) {b : Sp κ ⟶ S} (h : KillsOver u Y (spMap c ≫ b)) : KillsOver u Y b := by
  intro A _ g t ht
  letI := g.toAlgebra
  letI := c.toAlgebra
  let i : A →+* (A ⊗[κ] k) := Algebra.TensorProduct.includeLeftRingHom
  let j : k →+* (A ⊗[κ] k) := (Algebra.TensorProduct.includeRight : k →ₐ[κ] (A ⊗[κ] k)).toRingHom
  have hi : Function.Injective i :=
    Algebra.TensorProduct.includeLeft_injective (R := κ) (S := κ) (A := A) (B := k) c.injective
  have hij : i.comp g = j.comp c := by
    ext a
    change (algebraMap κ A a) ⊗ₜ[κ] (1 : k) = (1 : A) ⊗ₜ[κ] (algebraMap κ k a)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hw : spMap i ≫ spMap g ≫ b = spMap j ≫ spMap c ≫ b := by
    simp only [← Category.assoc, spMap_comp_spMap, hij]
  let φ : Over.mk (spMap j ≫ spMap c ≫ b) ⟶ Over.mk (spMap g ≫ b) := Over.homMk (spMap i) hw
  have h1 := h _ j (φ ≫ t) (fun y hy => by rw [charVal_comp i t (φ ≫ t) rfl, ht y hy, map_one])
  have h2 : φ ≫ (t ≫ u) = φ ≫ 1 :=
    (Category.assoc _ _ _).symm.trans (h1.trans (MonObj.comp_one φ).symm)
  have := GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom i) hi
  refine Over.OverMorphism.ext (GlobalTheory.ExtUnique.hom_ext_of_dominant G.hom ?_ (spMap i) ?_)
  · rw [Over.w, Over.w]
  · exact congr($(h2).left)

theorem false_of_killsOver {u : splitTorus S X ⟶ G} {K : Type} [Field K] (b : Sp K ⟶ S) {l : ℕ} (hl : l.Prime)
    (ψ : X →+ ZMod l) (hψ : Function.Surjective ψ) (hk : KillsOver u ψ.ker b)
    (hinj : ∀ (A : Type) [CommRing A] (g : K →+* A) (t : Over.mk (spMap g ≫ b) ⟶ splitTorus S X),
      t ≫ u = 1 → t = 1) : False := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨t, ht⟩ := exists_charVal (X := X) (spMap (algebraMap K (AddMonoidAlgebra K (ZMod l))) ≫ b)
    (MonoidHom.toHomUnits ((AddMonoidAlgebra.of K (ZMod l)).comp (AddMonoidHom.toMultiplicative ψ)))
  have ht' : ∀ χ, charVal t χ = AddMonoidAlgebra.single (ψ χ) 1 := ht
  have h1 := hk _ _ t fun y hy => by
    rw [ht', (AddMonoidHom.mem_ker).1 hy]; rfl
  have h2 := hinj _ _ t h1
  obtain ⟨χ, hχ⟩ := hψ 1
  have h3 := ht' χ
  rw [h2, charVal_one, AddMonoidAlgebra.one_def, hχ] at h3
  exact one_ne_zero (AddMonoidAlgebra.single_left_injective one_ne_zero h3).symm

theorem killsOver_of_residue [IsSeparated G.hom] {u : splitTorus S X ⟶ G} [IsMonHom u] {Y : AddSubgroup X}
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (b : Sp R ⟶ S)
    (h : KillsOver u Y (spMap (IsLocalRing.residue R) ≫ b)) : KillsOver u Y b := by
  refine GlobalTheory.T.killsOver_of_adic_completion S G X u Y R b fun n => ?_
  induction n with
  | zero =>
    let e : IsLocalRing.ResidueField R →+* R ⧸ (IsLocalRing.maximalIdeal R ^ (0 + 1)) :=
      Ideal.Quotient.lift _ (Ideal.Quotient.mk _) fun a ha =>
        Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using ha)
    have he : e.comp (IsLocalRing.residue R) = Ideal.Quotient.mk _ := by
      ext a; rfl
    have := killsOver_comp e h
    rwa [← Category.assoc, spMap_comp_spMap, he] at this
  | succ n ih =>
    set m := IsLocalRing.maximalIdeal R with hm
    have hne : m ^ (n + 1 + 1) ≠ ⊤ := fun htop =>
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top (Ideal.pow_eq_top_iff.1 htop |>.elim id (by simp))
    let q := Ideal.Quotient.mk (m ^ (n + 1 + 1))
    haveI : Nontrivial (R ⧸ m ^ (n + 1 + 1)) := Ideal.Quotient.nontrivial_iff.2 hne
    haveI : IsLocalRing (R ⧸ m ^ (n + 1 + 1)) :=
      IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
    let I : Ideal (R ⧸ m ^ (n + 1 + 1)) := (m ^ (n + 1)).map q
    have hI : I ^ 2 = ⊥ := by
      rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker, ← pow_mul]
      exact Ideal.pow_le_pow_right (by omega)
    refine GlobalTheory.T.killsOver_square_zero_lift S G X u Y _ (spMap q ≫ b) I hI ?_
    let e : R ⧸ m ^ (n + 1) →+* (R ⧸ m ^ (n + 1 + 1)) ⧸ I :=
      Ideal.Quotient.lift _ ((Ideal.Quotient.mk I).comp q) fun a ha =>
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha)
    have he : e.comp (Ideal.Quotient.mk (m ^ (n + 1))) = (Ideal.Quotient.mk I).comp q := by
      ext a; rfl
    have := killsOver_comp e ih
    rw [← Category.assoc, spMap_comp_spMap, he, ← spMap_comp_spMap, Category.assoc] at this
    exact this

theorem lie_injective : ∀ (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z] (G : Over Z) [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (u : splitTorus Z X ⟶ G) [IsMonHom u] (U : Z.Opens), (U : Set Z).Nonempty → (∀ (k : Type) [Field k] (x : Sp k ⟶ Z), ⊤ ≤ x ⁻¹ᵁ U → ∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z X), t ≫ u = 1 → t = 1) → ∀ (k : Type) [Field k] (x : Sp k ⟶ Z) (M : LieModel (splitTorus Z X) x (X →+ k)), IsCocharLie M → ∀ δ, M.pt δ ≫ u = 1 → δ = 0 := by
  intro Z _ _ G _ _ X _ _ u _ U hU hinj k _ x M hM δ hδ
  by_contra hne
  obtain ⟨l, hl, ψ, hψ, hk⟩ := GlobalTheory.T.torus_kernel_prime_quotient Z G X u k x M hM δ hne hδ
  obtain ⟨z, f, hx⟩ : ∃ (z : Z) (f : Z.residueField z ⟶ CommRingCat.of k),
      x = Spec.map f ≫ Z.fromSpecResidueField z :=
    ⟨_, _, ((Scheme.SpecToEquivOfField k Z).symm_apply_apply x).symm⟩
  by_cases hz : z ∈ U
  · have hU' : ⊤ ≤ x ⁻¹ᵁ U := fun p _ => by
      subst hx
      change (Z.fromSpecResidueField z) _ ∈ U
      rwa [Scheme.fromSpecResidueField_apply]
    exact false_of_killsOver x hl ψ hψ hk (hinj k x hU')
  have hgen : genericPoint Z ∈ U :=
    ((genericPoint_spec Z).mem_open_set_iff U.isOpen).2 (by simpa using hU)
  have hzg : z ≠ genericPoint Z := fun h => hz (h ▸ hgen)
  have hkκ : KillsOver u ψ.ker (Z.fromSpecResidueField z) :=
    killsOver_descent f.hom (hx ▸ hk)
  obtain ⟨V, hV, hA, hdom⟩ := GroundTheory.Heights₂.Heights.Model.DominatingDVRScheme.proof Z z hzg
  let jv : Z.presheaf.stalk z →+* V := (algebraMap (Z.presheaf.stalk z) Z.functionField).codRestrict V hA
  haveI : IsLocalHom jv := ⟨fun a ha => by
    by_contra hna
    exact ((hdom a).2 ((IsLocalRing.mem_maximalIdeal a).2 hna)) ha⟩
  let b : Sp V ⟶ Z := spMap jv ≫ Z.fromSpecStalk z
  let rm : IsLocalRing.ResidueField (Z.presheaf.stalk z) →+* IsLocalRing.ResidueField V :=
    IsLocalRing.ResidueField.map jv
  have e1 : spMap rm ≫ Z.fromSpecResidueField z = spMap (IsLocalRing.residue V) ≫ b := by
    have e0 : spMap rm ≫ Spec.map (Z.residue z) = spMap (IsLocalRing.residue V) ≫ spMap jv := by
      rw [spMap_comp_spMap, ← IsLocalRing.ResidueField.map_comp_residue jv, ← spMap_comp_spMap]
      rfl
    simp only [b, Scheme.fromSpecResidueField]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Z.fromSpecStalk z) e0).trans (Category.assoc _ _ _))
  have kres : KillsOver u ψ.ker (spMap (IsLocalRing.residue V) ≫ b) := e1 ▸ killsOver_comp rm hkκ
  have kV := killsOver_of_residue b kres
  have kK := killsOver_comp V.subtype kV
  have hU'' : ⊤ ≤ (spMap V.subtype ≫ b) ⁻¹ᵁ U := by
    have e2 : spMap V.subtype ≫ b = Z.fromSpecStalk (genericPoint Z) := by
      simp only [b]
      rw [← Category.assoc, spMap_comp_spMap]
      exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec Z).specializes trivial)
    intro p _
    change (spMap V.subtype ≫ b) p ∈ U
    rw [e2]
    have hp : (Z.fromSpecStalk (genericPoint Z)) p ∈ Set.range (Z.fromSpecStalk (genericPoint Z)) := ⟨p, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hp
    exact Specializes.mem_open hp U.isOpen hgen
  exact false_of_killsOver _ hl ψ hψ kK (hinj _ _ hU'')

end GlobalTheory.CompanionTheory.Ar.StratLie
end
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.EigVal

theorem values_eigen_sheaves : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (k K : Type) [Field k] [Field K] [Algebra k K] (z : Spec (CommRingCat.of K) ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (Vz : Type) [AddCommGroup Vz] [Module K Vz] (Mz : LieModel G z Vz) (h₀ : genPt ξ ⤳ centre z) (O S : Type) [CommRing O] [Fintype S] (act : O → (G ⟶ G)) (r : O →+* Module.End Ω V) (rz : O →+* Module.End K Vz) (σ : S → (O →+* Ω)) (χ : S → (O →+* k)), IsCptGen ξ → Smooth G.hom → (∀ a, IsMonHom (act a)) → M.IsActOf act r → Mz.IsActOf act rz → IsSplit χ → (∀ s a, ValAt ξ z (σ s a) (algebraMap k K (χ s a))) → M.lat ⟨centre z, h₀⟩ = ⨆ s, M.eigLat r (σ s) ⟨centre z, h₀⟩ → ∀ s, Submodule.span K {v | ∃ e ∈ M.eigLat r (σ s) ⟨centre z, h₀⟩, M.ValAt z e (Mz.pt v)} = eigSp rz ((algebraMap k K).comp (χ s)) :=
  @PositivityTheory.HtPt.Ci.eig_val

end GlobalTheory.CompanionTheory.Ar.EigVal
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_base_change_map : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (x : Spec (CommRingCat.of R) ⟶ S) (E E' : Type) [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E'] (M : LieModel G x E) (M' : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) E'), ∃ j : E →+ E', (∀ e, (M'.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫ (M.pt e).left) ∧ (∀ (a : R) e, j (a • e) = algebraMap R R' a • j e) ∧ (Smooth G.hom → ∀ (n : ℕ) (b : Module.Basis (Fin n) R E), LinearIndependent R' (fun k => j (b k)) ∧ Submodule.span R' (Set.range fun k => j (b k)) = ⊤) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieModel_baseChange | exact GlobalTheory.CompanionTheory.Ar.lieModel_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.lieModel_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT


theorem _root_.GlobalTheory.T.lie_model_base_change_span : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R R' : Type) [CommRing R] [CommRing R'] (c : R →+* R') (x : Spec (CommRingCat.of R) ⟶ S) (E E' : Type) [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E'] (M : LieModel G x E) (M' : LieModel G (Spec.map (CommRingCat.ofHom c) ≫ x) E') (j : E → E'), (∀ e, (M'.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap c)) ≫ (M.pt e).left) → Submodule.span R' (Set.range j) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieSpan.span_range_pullback | exact GlobalTheory.CompanionTheory.Ar.LieSpan.span_range_pullback | (intros; apply GlobalTheory.CompanionTheory.Ar.LieSpan.span_range_pullback <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem lieModel_lifts_of_local : ∀ (O K : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (S : Scheme.{0}) (x : Sp O ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (E : Type) [AddCommGroup E] [Module O E] (M : LieModel G x E) (v : epsAt (spMap (algebraMap O K) ≫ x) ⟶ G), IsTanAt G _ v → (∀ (P : Ideal O) [P.IsMaximal] (c : Localization.AtPrime P →+* K), c.comp (algebraMap O _) = algebraMap O K → ∃ w : epsAt (spMap (algebraMap O (Localization.AtPrime P)) ≫ x) ⟶ G, IsTanAt G _ w ∧ v.left = spMap (dualMap c) ≫ w.left) → ∃ e, (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap O K)) ≫ (M.pt e).left) :=
  @CoverDenseAlt.tangent_vector_extends_over_integers

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.PackLie

theorem lieModel_along_generic : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M₀ : LieModel G ξ Li) (B : Type) [CommRing B] (act : OAct B G) (ρ₀ : B →+* Module.End Ω Li), M₀.IsActOf act.act ρ₀ → ∀ (O : Type) [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) (x : Spec (CommRingCat.of R) ⟶ X), spMap (algebraMap R Ω) ≫ x = ξ → ∃ (L : Type) (_ : AddCommGroup L) (_ : Module R L) (M : LieModel G x L) (ρ : B →+* Module.End R L) (toLi : L →ₗ[R] Li), Module.Finite R L ∧ Module.Projective R L ∧ M.IsActOf act.act ρ ∧ IsBaseChange Ω toLi ∧ (∀ v, (M₀.pt (toLi v)).left = spMap (dualMap (algebraMap R Ω)) ≫ (M.pt v).left) ∧ ∀ a v, toLi (ρ a v) = ρ₀ a (toLi v) := by
  intro X G _ _ _ Ω _ ξ Li _ _ M₀ B _ act ρ₀ h₀ O _ _ R x hx
  subst hx
  obtain ⟨L, iL, mL, ⟨M⟩⟩ := lieModel_exists X G R x
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act X G R x L M B act.act act.hom act.one act.mul act.add
  have hsm : ∀ (a : R) (t : Li), a • t = algebraMap R Ω a • t := fun _ _ => rfl
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ x = spMap (algebraMap R Ω) ≫ x := rfl
  have ex : ∀ e, ∃ t, M₀.pt t = LieTangent.epsBase (algebraMap R Ω) hφ ≫ M.pt e :=
    fun e => M₀.onto _ (LieTangent.isTanAt_base _ hφ (M.tan e))
  choose f hf using ex
  let j : L →ₗ[R] Li :=
    { toFun := f
      map_add' := fun a b => M₀.inj (by rw [M₀.add, hf, hf, hf, M.add, comp_mul])
      map_smul' := fun c e => M₀.inj (by
        rw [RingHom.id_apply, hsm, LieModel.pt_smul, hf, hf, LieModel.pt_smul, ← Category.assoc,
          LieTangent.base_scale, Category.assoc]) }
  have hl : ∀ v, (M₀.pt (j v)).left = spMap (dualMap (algebraMap R Ω)) ≫ (M.pt v).left := fun v => by
    change (M₀.pt (f v)).left = _
    rw [hf]
    rfl
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.lie_model_finite_base_change X G R x L M
  refine ⟨L, iL, mL, M, ρ, j, h1, h2, hρ, h3 Ω Li M₀ j hl, hl, fun a v => M₀.inj ?_⟩
  change M₀.pt (f (ρ a v)) = M₀.pt (ρ₀ a (f v))
  rw [h₀ a, hf, hf, hρ a, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.PackLie
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem lieModel_isBaseChange : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (x : Sp R ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (E' : Type) [AddCommGroup E'] [Module R' E'] [Module R E'] [IsScalarTower R R' E'] (M : LieModel G x E) (M' : LieModel G (spMap (algebraMap R R') ≫ x) E') (j : E →ₗ[R] E'), (∀ e, ((M'.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap R R')) ≫ (M.pt e).left)) → IsBaseChange R' j := by
  intro S G _ _ R R' _ _ _ x E _ _ E' _ _ _ _ M M' j hj
  refine (GlobalTheory.T.lie_model_finite_base_change S G R x E M).2.2 R' E' M' j fun e => ?_
  have h := hj e
  change _ ≫ _ = _ ≫ _ at h
  rw [Category.comp_id] at h
  exact h

end GlobalTheory.CompanionTheory.Ar
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_finite_projective : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R : Type) [CommRing R] (x : Sp R ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G x E), Module.Finite R E ∧ Module.Projective R E := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieModel_finite_projective | exact GlobalTheory.CompanionTheory.Ar.lieModel_finite_projective | (intros; apply GlobalTheory.CompanionTheory.Ar.lieModel_finite_projective <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.btOrder_embedding_open_immersion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))), Γ.IsEmb (Γ.btOrder ⊤) j → IsOpenImmersion j ∧ Γ.TranslatesCover (Γ.btOrder ⊤) j ⊤ := by
  exact @GlobalTheory.CompanionTheory.Ar.BT.isOpenImmersion_emb_and_translatesCover
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_hodge_tate_functional : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T →* Rˣ), ∃ w : Module.Dual R L, Γ.IsHT i M N χ w := by
  first | exact @PositivityTheory.UnitarySelfGeneration.ht_exists | exact PositivityTheory.UnitarySelfGeneration.ht_exists
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_character_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (χ : T →* Rˣ), ∃ s : Γ(Γ.G.left, ⊤), Γ.HasValues s (fun t => ((χ t : Rˣ) : R)) := by
  first | exact @PositivityTheory.UnitarySelfGeneration.ht_char_section | exact PositivityTheory.UnitarySelfGeneration.ht_char_section
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.intersection_family_flat_twist : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (W : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (A : HermLine ι) (S : FlatHerm y φ A) (d : ℕ) (u : ((Σ k, ι k) → ℂ) → ℝ), IsIntersectionFamily I → IsArithVar (mCoordIdeal y) d → OverInt y φ → mCoordIdeal y ≤ W → IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsPlaceWeight y φ (fun σ => Real.log (S.κ σ)) u → I W (n + 1) (Fin.snoc L A) = -ptsIntegral W (pot L) u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FlatHerm.inter_eq_neg_integral | exact GlobalTheory.CompanionTheory.Ar.Flat.FlatHerm.inter_eq_neg_integral | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FlatHerm.inter_eq_neg_integral <;> assumption)
end
