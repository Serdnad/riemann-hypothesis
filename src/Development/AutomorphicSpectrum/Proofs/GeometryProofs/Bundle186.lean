module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle164
public import GroundTheory.HeightsAndTheta.Heights.HermitianLattice
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle170
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle180
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle179
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle064
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle177
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptIsoCompare
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem lieModel_liftBaseChange : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (x : Sp R ⟶ X) (V : Type) [AddCommGroup V] [Module R V] (M : LieModel G x V), ∃ (T : Type) (_ : AddCommGroup T) (_ : Module R' T) (_ : Module R T) (_ : IsScalarTower R R' T) (M' : LieModel G (spMap (algebraMap R R') ≫ x) T) (j : V →ₗ[R] T), (∀ e, ((M'.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap R R')) ≫ (M.pt e).left)) ∧ IsBaseChange R' j := by
  intro X G _ _ _ R R' _ _ _ x V _ _ M
  obtain ⟨T, iT, mT, ⟨M'⟩⟩ := lieModel_exists X G R' (spMap (algebraMap R R') ≫ x)
  letI mR : Module R T := Module.compHom T (algebraMap R R')
  have hsm : ∀ (a : R) (t : T), a • t = algebraMap R R' a • t := fun _ _ => rfl
  haveI tower : IsScalarTower R R' T :=
    ⟨fun a b t => by rw [Algebra.smul_def, hsm, mul_smul]⟩
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x = spMap (algebraMap R R') ≫ x := rfl
  have spec_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
      (f : A →+* B) (g : B →+* C) :
      Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
        Spec.map (CommRingCat.ofHom (g.comp f)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have spec_dual_alg :
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R' (DualNumber R'))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
    rw [spec_comp, spec_comp]
    congr 2
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have spec_fst_dual :
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R' R' R').toRingHom) ≫
        Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) =
      Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    rw [spec_comp, spec_comp]
    congr 2
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl']
  have spec_dual_eps (c : R) :
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫
        Spec.map (CommRingCat.ofHom (epsMul c)) =
      Spec.map (CommRingCat.ofHom (epsMul ((algebraMap R R') c))) ≫
        Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) := by
    rw [spec_comp, spec_comp]
    congr 2
    ext a <;> simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl']
  let b : epsAt (spMap (algebraMap R R') ≫ x) ⟶ epsAt x :=
    Over.homMk (Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R')))) (by
      change _ ≫ _ ≫ x = _ ≫ (spMap (algebraMap R R') ≫ x)
      rw [← Category.assoc, spec_dual_alg, Category.assoc])
  have hb : ∀ {v : epsAt x ⟶ G}, IsTanAt G x v →
      IsTanAt G (spMap (algebraMap R R') ≫ x) (b ≫ v) := by
    intro v hv
    change _ ≫ Spec.map _ ≫ v.left = _
    rw [← Category.assoc, spec_fst_dual, Category.assoc, hv]
    exact congrArg (·.left)
      (comp_one (M := G) (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R R'))) hφ :
        Over.mk (spMap (algebraMap R R') ≫ x) ⟶ Over.mk x))
  have hs (c : R) : b ≫ LieTangent.epsScale x c =
      LieTangent.epsScale (spMap (algebraMap R R') ≫ x) (algebraMap R R' c) ≫ b :=
    Over.OverMorphism.ext (spec_dual_eps c)
  have ex : ∀ e, ∃ t, M'.pt t = b ≫ M.pt e :=
    fun e => M'.onto _ (hb (M.tan e))
  choose f hf using ex
  let j : V →ₗ[R] T :=
    { toFun := f
      map_add' := fun a b => M'.inj (by rw [M'.add, hf, hf, hf, M.add, comp_mul])
      map_smul' := fun c e => M'.inj (by
        rw [RingHom.id_apply, hsm, LieModel.pt_smul, hf, hf, LieModel.pt_smul, ← Category.assoc,
          hs, Category.assoc]) }
  have hl : ∀ e, ((M'.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap R R')) ≫ (M.pt e).left) := fun e => by
    change (M'.pt (f e)).left ≫ 𝟙 G.left = _
    rw [hf, Category.comp_id]
    rfl
  exact ⟨T, iT, mT, mR, tower, M', j, hl, GlobalTheory.T.lie_model_isBaseChange X G R R' x V T M M' j hl⟩

end GlobalTheory.CompanionTheory.Ar.FlagFib
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorusSat

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem pt_zero {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {E : Type}
    [AddCommGroup E] [Module R E] (M : LieModel G x E) : M.pt 0 = 1 := by
  have h := M.add 0 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem exists_div {R X : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup X] {π : R}
    (hπ : Irreducible π) (δ : X →+ R) (h : ∀ χ, IsLocalRing.residue R (δ χ) = 0) :
    ∃ δ' : X →+ R, δ = π • δ' := by
  have hd : ∀ χ, ∃ r, δ χ = π * r := fun χ => by
    have hm : δ χ ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.residue_eq_zero_iff _).mp (h χ)
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ] at hm
    exact Ideal.mem_span_singleton'.mp hm |>.imp fun r hr => by rw [← hr, mul_comm]
  choose f hf using hd
  refine ⟨AddMonoidHom.mk' f fun a b => ?_, ?_⟩
  · apply mul_left_cancel₀ hπ.ne_zero
    rw [mul_add, ← hf, ← hf, ← hf, map_add (f := _)]
  · ext χ
    simp [hf]

theorem lie_torus_saturated : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (S : Scheme.{0}) (b : Sp R ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] [IsSeparated G.hom] [Smooth G.hom] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) [IsMonHom u], (∀ (A : Type) [CommRing A] (g : K →+* A) (t : Over.mk (spMap g ≫ spMap (algebraMap R K) ≫ b) ⟶ splitTorus S X), t ≫ u = 1 → t = 1) → ∀ (MT : LieModel (splitTorus S X) b (X →+ R)), IsCocharLie MT → ∀ (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G b E) (A : (X →+ R) →ₗ[R] E), (∀ δ, M.pt (A δ) = MT.pt δ ≫ u) → Function.Injective A ∧ ∀ (a : R) (y : E), a ≠ 0 → a • y ∈ LinearMap.range A → y ∈ LinearMap.range A := by
  intro R K _ _ _ _ _ _ S b G _ _ _ _ X _ _ _ u _ hgen MT hMT E _ _ M A hA
  obtain ⟨hEf, hEp⟩ := GlobalTheory.T.lie_model_finite_projective S G R b E M
  obtain ⟨Mk, hMk⟩ := GlobalTheory.T.exists_cocharacter_lie_model S X (IsLocalRing.ResidueField R) (spMap (IsLocalRing.residue R) ≫ b)
  obtain ⟨Ek, i1, i2, ⟨MG⟩⟩ := lieModel_exists S G (IsLocalRing.ResidueField R) (spMap (IsLocalRing.residue R) ≫ b)
  obtain ⟨j, hj, -⟩ := LieBaseChange.existsUnique_semilinear_lifts S G R _ (IsLocalRing.residue R) b E Ek M MG
  obtain ⟨jT, hjT, -⟩ := LieBaseChange.existsUnique_semilinear_lifts S (splitTorus S X) R _
    (IsLocalRing.residue R) b (X →+ R) (X →+ IsLocalRing.ResidueField R) MT Mk
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hcπ : IsLocalRing.residue R π = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact hπ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
  have key : ∀ δ, A δ ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R E) →
      δ ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (X →+ R)) := by
    intro δ hδ
    obtain ⟨z, hz⟩ := (GlobalTheory.CompanionTheory.CommAlg.SatOfInj.mem_max_smul_top_iff hπ _).mp hδ
    have h0 : j (A δ) = 0 := by
      rw [hz, map_smulₛₗ, hcπ, zero_smul]
    have a1 := hj (A δ)
    have a2 := hjT δ
    rw [Category.comp_id] at a1 a2
    rw [h0, pt_zero, hA, Over.comp_left] at a1
    have h1 : Mk.pt (jT δ) ≫ u = 1 := by
      apply Over.OverMorphism.ext
      rw [Over.comp_left, a2, Category.assoc, a1]
    have h2 : jT δ = 0 := GlobalTheory.T.torus_injective_lie_map R K S b G X u hgen Mk hMk _ h1
    have h3 : ∀ χ, IsLocalRing.residue R (δ χ) = 0 := by
      intro χ
      have e := GlobalTheory.CompanionTheory.Ar.TorusModel.charVal_comp (dualMap (IsLocalRing.residue R)) (MT.pt δ) (Mk.pt (jT δ)) a2 χ
      rw [hMk, hMT, h2] at e
      have e2 := congrArg TrivSqZeroExt.snd e
      simpa [dualMap] using e2.symm
    obtain ⟨δ', rfl⟩ := exists_div hπ δ h3
    exact (GlobalTheory.CompanionTheory.CommAlg.SatOfInj.mem_max_smul_top_iff hπ _).mpr ⟨δ', rfl⟩
  have e := addMonoidHomLequivInt (A := X) (B := R) R
  haveI : Module.Free R (X →+ R) := Module.Free.of_equiv e.symm
  haveI : Module.Finite R (X →+ R) := Module.Finite.equiv e.symm
  haveI : Module.IsTorsionFree R E := inferInstance
  exact GlobalTheory.CompanionTheory.CommAlg.SatOfInj.sat_of_inj_mod R (X →+ R) E A key

end GlobalTheory.CompanionTheory.Ar.TorusSat
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieSigma

variable {S : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

theorem dualMap_comp_algebraMap (φ : R →+* R') :
    (dualMap φ).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp φ := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_dualMap (φ : R →+* R') :
    (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (dualMap φ)
      = φ.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => ?_
  simp [GlobalTheory.CompanionTheory.Ar.dualMap]

theorem dualMap_comp_epsMul (φ : R →+* R') (a : R) :
    (dualMap φ).comp (epsMul a) = (epsMul (φ a)).comp (dualMap φ) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [GlobalTheory.CompanionTheory.Ar.dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, mul_comm]

theorem comp_one_over {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) : u ≫ (1 : X ⟶ M) = 1 := by
  exact comp_one u

theorem comp_mul_over {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) (p q : X ⟶ M) :
    u ≫ (p * q) = (u ≫ p) * (u ≫ q) := by
  exact comp_mul u p q

def pullEps (φ : R →+* R') (x : Sp R ⟶ S) : epsAt (spMap φ ≫ x) ⟶ epsAt x :=
  Over.homMk (spMap (dualMap φ)) (by
    simp only [Over.mk_hom, epsAt]
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      dualMap_comp_algebraMap])

def pullPt (φ : R →+* R') (x : Sp R ⟶ S) : Over.mk (spMap φ ≫ x) ⟶ Over.mk x :=
  Over.homMk (spMap φ) rfl

theorem isTanAt_pull (G : Over S) [GrpObj G] (φ : R →+* R') (x : Sp R ⟶ S) (v : epsAt x ⟶ G)
    (hv : IsTanAt G x v) : IsTanAt G (spMap φ ≫ x) (pullEps φ x ≫ v) := by
  unfold IsTanAt at hv ⊢
  rw [← comp_one_over (pullPt φ x), Over.comp_left, Over.comp_left, ← hv]
  have key : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R' R' R').toRingHom) ≫ spMap (dualMap φ)
      = spMap φ ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, fst_comp_dualMap]
  simp only [pullEps, pullPt, Over.homMk_left]
  rw [reassoc_of% key]

theorem exists_linear (G : Over S) [GrpObj G] (φ : R →+* R') (x : Sp R ⟶ S)
    {E E₀ : Type} [AddCommGroup E] [Module R E] [AddCommGroup E₀] [Module R' E₀] [Module R E₀]
    (hs : ∀ (a : R) (e : E₀), a • e = φ a • e) (M : LieModel G x E)
    (M₀ : LieModel G (spMap φ ≫ x) E₀) :
    ∃ j : E →ₗ[R] E₀, ∀ e, M₀.pt (j e) = pullEps φ x ≫ M.pt e := by
  choose j hj using fun e => M₀.onto _ (isTanAt_pull G φ x (M.pt e) (M.tan e))
  refine ⟨{ toFun := j, map_add' := ?_, map_smul' := ?_ }, hj⟩
  · intro e e'
    apply M₀.inj
    rw [M₀.add, hj, hj, hj, M.add, comp_mul_over]
  · intro c e
    apply M₀.inj
    rw [RingHom.id_apply, hs, hj]
    apply Over.OverMorphism.ext
    rw [M₀.smul, hj, Over.comp_left, Over.comp_left, M.smul]
    simp only [pullEps, Over.homMk_left, ← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, dualMap_comp_epsMul]

def transport {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {E E' : Type} [AddCommGroup E] [Module R E]
    [AddCommGroup E'] [Module R E'] (M : LieModel G x E) (f : E' ≃ₗ[R] E) : LieModel G x E' where
  pt e := M.pt (f e)
  tan e := M.tan _
  inj := M.inj.comp f.injective
  onto v hv := by
    obtain ⟨e, he⟩ := M.onto v hv
    exact ⟨f.symm e, by simpa using he⟩
  add e e' := by simp only [map_add (f := _)]; exact M.add _ _
  smul c e := by simp only [map_smul]; exact M.smul _ _


open GroundTheory.Heights₂.Heights in
theorem lieModel_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ S) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] (M : LieModel G z V) (σ : L →+* ℂ), ∃ Mσ : LieModel G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) (GroundTheory.Heights₂.Heights.Fibre σ V), ∀ e : V, M.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 G.left) e (Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)) := by
  intro S G _ _ _ L _ _ z V _ _ M σ
  classical
  let _ : Algebra (𝓞 L) ℂ := (σ.comp (algebraMap (𝓞 L) L)).toAlgebra
  obtain ⟨E₀, i1, i2, ⟨M₀⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists S G ℂ (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z)
  let _ : Module (𝓞 L) E₀ := Module.compHom E₀ (σ.comp (algebraMap (𝓞 L) L))
  have _ : IsScalarTower (𝓞 L) ℂ E₀ := ⟨fun a b e => by
    show ((σ.comp (algebraMap (𝓞 L) L)) a * b) • e = (σ.comp (algebraMap (𝓞 L) L)) a • b • e
    rw [mul_smul]⟩
  obtain ⟨j, hj⟩ := exists_linear G (σ.comp (algebraMap (𝓞 L) L)) z (fun a e => rfl) M M₀
  have hl : ∀ e, M.Lifts (algebraMap (𝓞 L) ℂ) (𝟙 G.left) e (M₀.pt (j e)) := by
    intro e
    unfold GlobalTheory.CompanionTheory.Ar.LieModel.Lifts
    rw [hj e, Over.comp_left, Category.comp_id]
    rfl
  have hb := GlobalTheory.T.lie_model_isBaseChange S G (𝓞 L) ℂ z V E₀ M M₀ j hl
  let f : GroundTheory.Heights₂.Heights.Fibre σ V ≃ₗ[ℂ] E₀ := hb.equiv
  refine ⟨transport M₀ f, fun e => ?_⟩
  have hf : f ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e) = j e := by
    show hb.equiv ((1 : ℂ) ⊗ₜ[𝓞 L] e) = j e
    rw [IsBaseChange.equiv_tmul, one_smul]
  unfold GlobalTheory.CompanionTheory.Ar.LieModel.Lifts
  show (M₀.pt (f ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e))).left ≫ 𝟙 _ = _
  rw [hf, hj e, Over.comp_left, Category.comp_id]
  rfl

end GlobalTheory.CompanionTheory.Ar.LieSigma
end
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.intersection_family_place_weight : PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (W : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (d : ℕ) (t : (F →+* ℂ) → ℝ) (u : ((Σ k, ι k) → ℂ) → ℝ), IsIntersectionFamily I → IsArithVar (mCoordIdeal y) d → OverInt y φ → mCoordIdeal y ≤ W → IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ σ, t (ComplexEmbedding.conjugate σ) = t σ) → (∀ σ z, PtOver y φ σ z → u z = t σ) → ptsIntegral W (pot L) u = meanEmb t * ptsIntegral W (pot L) (fun _ => 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ptsIntegral_eq_mean | exact GlobalTheory.CompanionTheory.Ar.Flat.ptsIntegral_eq_mean | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ptsIntegral_eq_mean <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.curve_lie_lattice_degree : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (G : Over X) [GrpObj G] [IsCommMonObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (Vz : Type) [AddCommGroup Vz] [Module K Vz] [FiniteDimensional K Vz] (Mz : LieModel G z Vz) (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)) (S : Set (Cpt ξ)) (L L' : Lat ξ V) (r r' : ℕ) (b₀ : Fin r → V) (U' : Submodule Ω V), IsCptGen ξ → Smooth G.hom → (⟨centre z, h₀⟩ : Cpt ξ) ∈ S → (∀ i, (⟨centre (Y.x i), h i⟩ : Cpt ξ) ∈ S) → LinearIndependent Ω b₀ → L.IsFlagVBOn S b₀ → L'.IsVBOn S r' U' → IsCompl (Submodule.span Ω (Set.range b₀)) U' → (∀ q ∈ S, M.lat q = L q ⊔ L' q) → ∃ W : ℕ → Submodule K Vz, W 0 = ⊥ ∧ W r = Submodule.span K {v | ∃ e ∈ L ⟨centre z, h₀⟩, M.ValAt z e (Mz.pt v)} ∧ ∀ s : Fin r, Y.IsDeg (L.gr b₀ s) (subDeg C (Y.lieLat Mz) (W (s + 1)) - subDeg C (Y.lieLat Mz) (W s)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GrDeg.grLine_deg_eq_sub | exact GlobalTheory.CompanionTheory.Ar.GrDeg.grLine_deg_eq_sub | (intros; apply GlobalTheory.CompanionTheory.Ar.GrDeg.grLine_deg_eq_sub <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

theorem _root_.GlobalTheory.T.lie_model_finite_generating_values : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (z₀ : Sp ℂ ⟶ X), IsCptGen ξ → genPt ξ ⤳ centre z₀ → ∃ (N : ℕ) (s : Fin N → Li), (∀ i, ∃ v : epsAt z₀ ⟶ G, M.ValAt z₀ (s i) v) ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel G z₀ V) (b : Fin N → V), (∀ i, M.ValAt z₀ (s i) (Mz.pt (b i))) → LinearIndependent ℂ b ∧ Submodule.span ℂ (Set.range b) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotUnif.lie_frame_values_basis | exact GlobalTheory.CompanionTheory.Ar.QuotUnif.lie_frame_values_basis | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotUnif.lie_frame_values_basis <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar Filter Topology Metric


theorem _root_.GlobalTheory.T.local_lie_model_extends : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (N : X.Opens) (J : Type) [Finite J] (c : J → E), p.1 ∈ N → (∀ i, c i ∈ M.lat p) → ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (_ : IsOpenImmersion x) (F : Type) (_ : AddCommGroup F) (_ : Module R F) (MR : LieModel G x F) (e : J → F), p.1 ∈ x.opensRange ∧ x.opensRange ≤ N ∧ ∀ (q : Cpt ξ) (ψ : R →+* X.presheaf.stalk q.1), spMap ψ ≫ x = X.fromSpecStalk q.1 → ∀ (i : J) (v : epsAt (R := X.presheaf.stalk q.1) (X.fromSpecStalk q.1) ⟶ G), v.left = spMap (dualMap ψ) ≫ (MR.pt (e i)).left → M.Extends q (c i) v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieLat_germs_eq_sections | exact GlobalTheory.CompanionTheory.Ar.lieLat_germs_eq_sections | (intros; apply GlobalTheory.CompanionTheory.Ar.lieLat_germs_eq_sections <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt

section Transport

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {R R' : Type} [CommRing R] [CommRing R']
  {E E' : Type} [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E']

theorem exists_lie_transport (c : R →+* R') {x : Sp R ⟶ S} {y : Sp R' ⟶ S} (h : spMap c ≫ x = y)
    (M : LieModel G x E) (M' : LieModel G y E') :
    ∃ j : E →ₛₗ[c] E', ∀ e, (M'.pt (j e)).left = spMap (dualMap c) ≫ (M.pt e).left := by
  subst h
  obtain ⟨j, hj, -⟩ := GlobalTheory.T.lie_model_existsUnique_semilinear S G R R' c x E E' M M'
  refine ⟨j, fun e => ?_⟩
  have := hj e
  rw [Category.comp_id] at this
  exact this

theorem lie_transport_induction [Smooth G.hom] (c : R →+* R') {x : Sp R ⟶ S} {y : Sp R' ⟶ S}
    (h : spMap c ≫ x = y) (M : LieModel G x E) (M' : LieModel G y E') (j : E →ₛₗ[c] E')
    (hj : ∀ e, (M'.pt (j e)).left = spMap (dualMap c) ≫ (M.pt e).left) {P : E' → Prop} (zero : P 0)
    (base : ∀ e, P (j e)) (smul : ∀ (s : R') n, P n → P (s • n))
    (add : ∀ n n', P n → P n' → P (n + n')) (n : E') : P n := by
  subst h
  letI : Algebra R R' := c.toAlgebra
  letI : Module R E' := Module.compHom E' c
  haveI : IsScalarTower R R' E' := ⟨fun a b v => by
    change (c a * b) • v = c a • (b • v)
    rw [mul_smul]⟩
  let jl : E →ₗ[R] E' :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun r e => j.map_smulₛₗ r e }
  have hb : IsBaseChange R' jl := GlobalTheory.T.lie_model_isBaseChange S G R R' x E E' M M' jl (fun e => by
    rw [Category.comp_id]
    exact hj e)
  exact hb.inductionOn n base smul add

end Transport

theorem lat_form_regular_generizes : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X)
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (f : Module.Dual Ω Li) (p q : Cpt ξ),
    IsCptGen ξ → q.1 ⤳ p.1 → (∀ e ∈ M.lat p, f e ∈ regAt ξ p) → ∀ e ∈ M.lat q, f e ∈ regAt ξ q := by
  intro X G _ _ _ Ω _ ξ Li _ _ M f p q _ hqp hf e he
  let c : X.presheaf.stalk p.1 →+* X.presheaf.stalk q.1 := (X.presheaf.stalkSpecializes hqp).hom
  have hc : spMap c ≫ X.fromSpecStalk p.1 = X.fromSpecStalk q.1 :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hqp
  have hgen : ∀ s, genMap ξ q (c s) = genMap ξ p s :=
    fun s => LieTangent.genMap_specializes p q.2 hqp s
  obtain ⟨E, _, _, ⟨Mp⟩⟩ := lieModel_exists X G (X.presheaf.stalk p.1) (X.fromSpecStalk p.1)
  obtain ⟨E', _, _, ⟨Mq⟩⟩ := lieModel_exists X G (X.presheaf.stalk q.1) (X.fromSpecStalk q.1)
  obtain ⟨j, hj⟩ := exists_lie_transport c hc Mp Mq
  obtain ⟨jp, hjp⟩ := exists_lie_transport (genMap ξ p) (LieTangent.spec_genMap ξ p) Mp M
  obtain ⟨jq, hjq⟩ := exists_lie_transport (genMap ξ q) (LieTangent.spec_genMap ξ q) Mq M

  have hcomp : ∀ e₀, jq (j e₀) = jp e₀ := by
    intro e₀
    refine M.inj (Over.OverMorphism.ext ?_)
    rw [hjq, hj, hjp, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    refine RingHom.ext fun a => ?_
    ext <;> simp [hgen]

  have hmem : ∀ e₀, jp e₀ ∈ M.lat p := fun e₀ =>
    (M.mem_lat_iff p _).2 ⟨Mp.pt e₀, Mp.tan e₀, hjp e₀⟩

  obtain ⟨v, hv⟩ := (M.mem_lat_iff q e).1 he
  obtain ⟨ε, rfl⟩ := Mq.onto v hv.1
  have he' : e = jq ε := M.inj (Over.OverMorphism.ext (hv.2.trans (hjq ε).symm))
  subst he'
  refine lie_transport_induction c hc Mp Mq j hj (P := fun n => f (jq n) ∈ regAt ξ q) ?_ ?_ ?_ ?_ ε
  · simpa using zero_mem (regAt ξ q)
  · intro e₀
    obtain ⟨s, hs⟩ := hf _ (hmem e₀)
    rw [hcomp]
    exact ⟨c s, (hgen s).trans hs⟩
  · intro s n hn
    have : f (jq (s • n)) = genMap ξ q s * f (jq n) := by
      rw [jq.map_smulₛₗ, map_smul, smul_eq_mul]
    change f (jq (s • n)) ∈ regAt ξ q
    rw [this]
    exact mul_mem ⟨s, rfl⟩ hn
  · intro n n' hn hn'
    change f (jq (n + n')) ∈ regAt ξ q
    rw [map_add (f := _), map_add (f := _)]
    exact add_mem hn hn'

end GlobalTheory.CompanionTheory.Ar.RootHt
end
end

section

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.hodge_cpt_iso_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y) (e : A'.X ≅ A.X) (φ : A.Li ≃ₗ[Ω] A'.Li) (Fl : A.Flag) (Fl' : A'.Flag) (τ τ' : CMType H) (i : Fin (D.p + D.q)) (e₀ e₀' : Ω) (L L' : HermLine ι), Birational y → A'.ξ ≫ e.hom = A.ξ → (∀ (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1) (v : A.Li), (v ∈ A.V (.inl τ) ⟨e.hom q.1, h⟩ ↔ φ v ∈ A'.V (.inl τ') q) ∧ (v ∈ A.V (.inr τ) ⟨e.hom q.1, h⟩ ↔ φ v ∈ A'.V (.inr τ') q)) → (∀ k, (flagStep Ω (Fl.b (.inl τ)) k).map (φ : A.Li →ₗ[Ω] A'.Li) = flagStep Ω (Fl'.b (.inl τ')) k ∧ (flagStep Ω (Fl.b (.inr τ)) k).map (φ : A.Li →ₗ[Ω] A'.Li) = flagStep Ω (Fl'.b (.inr τ')) k) → (∀ z : Sp ℂ ⟶ A'.X, (A'.Interior z ↔ A.Interior (z ≫ e.hom)) ∧ (A'.Interior z → ∀ (r : ℕ) (b : Fin r → A.Li) (Γ : Matrix (Fin r) (Fin r) ℂ), A.M.GramAt A.t.PP.L (z ≫ e.hom) b Γ ↔ A'.M.GramAt A'.t.PP.L z (fun i => φ (b i)) Γ)) → (Fl.rootLat (τ, i)).IsDegOn Set.univ y L.a e₀ → (Fl'.rootLat (τ', i)).IsDegOn Set.univ y L'.a e₀' → Fl.IsHodgeLine (τ, i) e₀ L → Fl'.IsHodgeLine (τ', i) e₀' L' → (∀ (z : Sp ℂ ⟶ A.X), A.Interior z → ∀ s, ∃ (h : genPt A.ξ ⤳ centre z) (b : Fin (labelRk D s) → A.Li) (Γ : Matrix (Fin (labelRk D s)) (Fin (labelRk D s)) ℂ), (∀ k, flagStep Ω b k = flagStep Ω (Fl.b s) k) ∧ (A.V s).IsFrameAt b ⟨centre z, h⟩ ∧ A.M.GramAt A.t.PP.L z b Γ ∧ Γ.PosDef) → IsoLineOn (mCoordIdeal y) {w | ∃ z : Sp ℂ ⟶ A.X, CoordsAt A.ξ y z w ∧ A.Interior z} L L' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.RootIso.rootLine_iso | exact GlobalTheory.CompanionTheory.Ar.Cmp.RootIso.rootLine_iso | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.RootIso.rootLine_iso <;> assumption)
end
