module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle013
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1652
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2100
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle106
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle007
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle014
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle507
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1802
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle720
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle763
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1684
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SmulOneSecEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2075
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Separation.CompletelyRegular
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle010
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.HomAlgAny

open MeasureTheory

theorem surjective_of_forall_sub_mem {g : ℕ} (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Λ : Submodule ℤ (Fin g → ℂ))
    (hΛ : DiscreteTopology Λ) (h : ∀ x, ∃ z, x - T z ∈ Λ) : Function.Surjective T := by
  by_contra hT
  have hV : (LinearMap.range T).restrictScalars ℝ ≠ ⊤ := by
    intro h'
    apply hT
    intro x
    have hx : x ∈ (LinearMap.range T).restrictScalars ℝ := h' ▸ Submodule.mem_top
    exact LinearMap.mem_range.1 ((Submodule.restrictScalars_mem ℝ _ x).1 hx)
  haveI : Countable Λ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hcov : (Set.univ : Set (Fin g → ℂ)) ⊆ ⋃ l : Λ,
      (fun y => y + -(l : Fin g → ℂ)) ⁻¹' (((LinearMap.range T).restrictScalars ℝ : Submodule ℝ (Fin g → ℂ)) : Set (Fin g → ℂ)) := by
    intro x _
    obtain ⟨z, hz⟩ := h x
    refine Set.mem_iUnion.2 ⟨⟨x - T z, hz⟩, ?_⟩
    simp only [Set.mem_preimage, SetLike.mem_coe, Submodule.restrictScalars_mem]
    exact ⟨z, by abel⟩
  have h0 : volume (Set.univ : Set (Fin g → ℂ)) = 0 :=
    measure_mono_null hcov (measure_iUnion_null fun l => by
      rw [measure_preimage_add_right]
      exact Measure.addHaar_submodule volume _ hV)
  exact (isOpen_univ.measure_ne_zero volume Set.univ_nonempty) h0

theorem sub_mem_of_ex_eq {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (a b : Fin g → ℂ)
    (h : u.ex a = u.ex b) : a - b ∈ u.Λ := by
  rw [← u.ker]
  have e := u.ex_add (a - b) b
  rw [sub_add_cancel, h] at e
  have e2 := congrArg (· * (u.ex b)⁻¹) e
  simpa using e2.symm

theorem exists_of_polAV (P P' : Out.PolAV (Sp ℂ)) (n n' : ℕ) (v : HolUnif P.A P.L n) (v' : HolUnif P'.A P'.L n')
    (F : (Fin n → ℂ) →ₗ[ℂ] (Fin n' → ℂ)) (hn : P.g = n) (hn' : P'.g = n') (hF : ∀ z ∈ v.Λ, F z ∈ v'.Λ) :
    ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, v'.ex (F z) = v.ex z ≫ f := by
  subst hn hn'
  obtain ⟨hL, hL2⟩ := abelianSchemeLaws_all
  obtain ⟨f, ⟨hf, hfe⟩, -⟩ := existsUnique_isMonHom_of_map_lattice hL hL2 AbLaw.CubeAssembly.cube_gen
    thetaUnifAV_all P P' P.L P'.L v v' F hF
  exact ⟨f, hf, hfe⟩


open GlobalTheory.HolUnifEnd GlobalTheory.HolUnifHom in
theorem exists_isMonHom_of_map_lattice (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (g g' : ℕ)
    (hA : IsAbelianScheme A) (hA' : IsAbelianScheme A') (hgA : SmoothOfRelativeDimension g A.hom)
    (hgA' : SmoothOfRelativeDimension g' A'.hom) (L : LB A.left) (L' : LB A'.left) (u : HolUnif A L g)
    (u' : HolUnif A' L' g') (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hM : ∀ x ∈ u.Λ, M x ∈ u'.Λ) :
    ∃ α : A ⟶ A', IsMonHom α ∧ ∀ w, u'.ex (M w) = u.ex w ≫ α := by
  obtain ⟨Q, v, i, r, J, R, m, hQ, hi, hr, hm, hJ, hR, hJΛ, hRΛ, hRJ⟩ := exists_linear_factor A g hA hgA L u
  obtain ⟨Q', v', i', r', J', R', m', hQ', hi', hr', hm', hJ', hR', hJΛ', hRΛ', hRJ'⟩ :=
    exists_linear_factor A' g' hA' hgA' L' u'
  obtain ⟨β, hβ, hβe⟩ := exists_of_polAV Q Q' (8 * g) (8 * g') v v' (J' ∘ₗ M ∘ₗ R) hQ hQ'
    (fun l hl => hJΛ' _ (hM _ (hRΛ _ hl)))
  haveI := hi; haveI := hr'; haveI := hβ
  have hφ : ∀ z, u.ex z ≫ i ≫ β ≫ r' = u'.ex ((m' * m) • M z) := by
    intro z
    have e := hβe (J z)
    simp only [LinearMap.comp_apply] at e
    rw [← Category.assoc, ← hJ, ← Category.assoc, ← e, ← hR', hRJ', hRJ, map_nsmul, smul_smul]
  have := hA'.proper
  obtain ⟨α, hα, hαφ⟩ := exists_factor_pow A A' hA (m' * m) (Nat.one_le_iff_ne_zero.2 (by positivity))
    (i ≫ β ≫ r') fun y hy => by
      obtain ⟨z, rfl⟩ := u.ex_onto y
      rw [← holUnif_ex_nsmul_eq_pow, u.ker] at hy
      rw [hφ, u'.ker, ← map_nsmul]
      exact hM _ hy
  refine ⟨α, hα, fun w => ?_⟩
  have hN0 : ((m' * m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show m' * m ≠ 0 by positivity)
  have hw : (m' * m) • (((m' * m : ℕ) : ℂ)⁻¹ • w) = w := by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
  calc u'.ex (M w) = u'.ex ((m' * m) • M (((m' * m : ℕ) : ℂ)⁻¹ • w)) := by rw [← map_nsmul, hw]
    _ = u.ex (((m' * m : ℕ) : ℂ)⁻¹ • w) ≫ i ≫ β ≫ r' := (hφ _).symm
    _ = u.ex (((m' * m : ℕ) : ℂ)⁻¹ • w) ≫ (𝟙 A ^ (m' * m)) ≫ α := by rw [hαφ]
    _ = u.ex w ≫ α := by
      rw [← Category.assoc, MonObj.comp_pow, Category.comp_id, ← holUnif_ex_nsmul_eq_pow, hw]

theorem existsUnique_isMonHom_of_map_ker : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (g g' : ℕ), IsAbelianScheme A → IsAbelianScheme A' → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g' A'.hom → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (e' : (Fin g' → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A')) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), IsExp (𝟙 (Sp ℂ)) e → IsExp (𝟙 (Sp ℂ)) e' → (∀ z, e z = 1 → e' (M z) = 1) → ∃! f : A ⟶ A', IsMonHom f ∧ ∀ z, e' (M z) = e z ≫ f := by
  intro A A' _ _ _ _ g g' hA hA' hg hg' e e' M he he' hM
  obtain ⟨L, ⟨u⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif A g hA hg
  obtain ⟨L', ⟨u'⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif A' g' hA' hg'
  obtain ⟨t1, t2⟩ := GlobalTheory.TorusTransfer.tangent_bijective u hg
  obtain ⟨t1', t2'⟩ := GlobalTheory.TorusTransfer.tangent_bijective u' hg'
  obtain ⟨T, hT, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo A hA L g g u t1 t2 e he.1 he.2.2.1
  obtain ⟨T', hT', -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo A' hA' L' g' g' u' t1' t2' e' he'.1 he'.2.2.1
  have hTs : Function.Surjective T := surjective_of_forall_sub_mem T u.Λ u.discrete fun x => by
    obtain ⟨z, hz⟩ := he.2.1 (u.ex x)
    exact ⟨z, sub_mem_of_ex_eq u _ _ (by rw [hT]; exact hz.symm)⟩
  have hTi : Function.Injective T := LinearMap.injective_iff_surjective.2 hTs
  let Te : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.ofBijective T ⟨hTi, hTs⟩
  have hTe : ∀ z, Te.symm (T z) = z := fun z => Te.symm_apply_apply z
  let F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ) := T' ∘ₗ M ∘ₗ Te.symm.toLinearMap
  have hFT : ∀ z, F (T z) = T' (M z) := fun z => by simp only [F, LinearMap.comp_apply, LinearEquiv.coe_coe, hTe]
  have hF : ∀ x ∈ u.Λ, F x ∈ u'.Λ := fun x hx => by
    obtain ⟨z, rfl⟩ := hTs x
    rw [hFT, ← u'.ker, hT']
    refine hM z ?_
    rw [← hT, u.ker]
    exact hx
  obtain ⟨α, hα, hαe⟩ := exists_isMonHom_of_map_lattice A A' g g' hA hA' hg hg' L L' u u' F hF
  have hex : ∀ z, e' (M z) = e z ≫ α := fun z => by
    rw [← hT', ← hFT, hαe, hT]
  refine ⟨α, ⟨hα, hex⟩, fun f hf => ?_⟩
  haveI := hA.smooth
  haveI := hA'.proper
  haveI : IsReduced A.left := GlobalTheory.isReduced_of_smooth_complex _ A.hom hA.smooth
  refine GlobalTheory.ComplexPoints.over_hom_ext_of_complexPoints fun x => ?_
  obtain ⟨z, rfl⟩ := he.2.1 x
  rw [← hf.2, hex]

end GlobalTheory.HomAlgAny
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.UPel.HT.LieType

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {g : ℕ} {e : (Fin g → ℂ) → (Over.mk y ⟶ G)}

def expDer (he : IsExp y e) (w : Fin g → ℂ) : epsPt y ⟶ G := (he.2.2.2.1 w).exists.choose

variable (he : IsExp y e)
include he

theorem expDer_spec (w : Fin g → ℂ) : IsDerivAt0 (fun z => (e z).left) w (expDer he w).left :=
  (he.2.2.2.1 w).exists.choose_spec

theorem exp_zero : e 0 = 1 := by
  have h := he.1 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem expDer_eq_iff (w : Fin g → ℂ) (v : epsPt y ⟶ G) :
    IsDerivAt0 (fun z => (e z).left) w v.left ↔ expDer he w = v :=
  ⟨fun hv => Over.OverMorphism.ext
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_unique (expDer_spec he w) hv), fun hv => hv ▸ expDer_spec he w⟩

theorem expDer_base (w : Fin g → ℂ) :
    spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (expDer he w).left = (1 : Over.mk y ⟶ G).left := by
  rw [(expDer_spec he w).1]; show (e 0).left = _; rw [exp_zero he]

theorem expDer_injective : Function.Injective (expDer he) := by
  intro w w' h
  have h1 := expDer_spec he w
  have h2 := expDer_spec he w'
  rw [← h] at h2
  have hb : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (expDer he w).left = (e 0).left := h1.1
  exact (he.2.2.2.2 _ hb).unique h1 h2

theorem expDer_surj (v : epsPt y ⟶ G)
    (hv : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (1 : Over.mk y ⟶ G).left) :
    ∃ w, expDer he w = v := by
  obtain ⟨w, hw, -⟩ := he.2.2.2.2 v (by rw [hv, exp_zero he])
  exact ⟨w, (expDer_eq_iff he w v).1 hw⟩

theorem expDer_add (w w' : Fin g → ℂ) : expDer he (w + w') = expDer he w * expDer he w' :=
  (expDer_eq_iff he _ _).1 (GlobalTheory.UnifCompare.isDerivAt0_mul (by rw [exp_zero he]) (expDer_spec he w)
    (expDer_spec he w'))

theorem expDer_zero : expDer he 0 = 1 := by
  have h := expDer_add he 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem expDer_smul (c : ℂ) (w : Fin g → ℂ) :
    (expDer he (c • w)).left = spMap (epsScale c) ≫ (expDer he w).left :=
  ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_unique (expDer_spec he _)
    (GlobalTheory.UnifCompare.isDerivAt0_smul (expDer_spec he w) c)

theorem expDer_prod {n : ℕ} (f : Fin n → Fin g → ℂ) :
    (List.ofFn fun j => expDer he (f j)).prod = expDer he (∑ j, f j) := by
  induction n with
  | zero => simp [expDer_zero he]
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, ih (fun j => f j.succ), Fin.sum_univ_succ, expDer_add he]

theorem expDer_mulVec (M : Matrix (Fin g) (Fin g) ℂ) (φ : G ⟶ G) (hM : ∀ z, e (M *ᵥ z) = e z ≫ φ)
    (w : Fin g → ℂ) : expDer he (M *ᵥ w) = expDer he w ≫ φ := by
  have h1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_comp_hom (expDer_spec he w) φ.left
  have h2 : (fun z => (e z).left ≫ φ.left) = fun z => (e (Matrix.mulVecLin M z)).left := by
    funext z; rw [Matrix.mulVecLin_apply, hM z, Over.comp_left]
  rw [h2, GlobalTheory.ThetaWitness.isDerivAt0_comp_linear_iff (fun z => (e z).left) he.2.2.1] at h1
  exact (expDer_eq_iff he _ _).1 h1

theorem expDer_eigen_iff (M : Matrix (Fin g) (Fin g) ℂ) (φ : G ⟶ G) (hM : ∀ z, e (M *ᵥ z) = e z ≫ φ)
    (c : ℂ) (w : Fin g → ℂ) :
    (expDer he w ≫ φ).left = spMap (epsScale c) ≫ (expDer he w).left ↔ M *ᵥ w = c • w := by
  rw [← expDer_mulVec he M φ hM, ← expDer_smul he]
  constructor
  · intro h
    exact expDer_injective he (Over.OverMorphism.ext h)
  · intro h
    rw [h]

end GlobalTheory.UPel.HT.LieType
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AbCoh.Axes

theorem exists_cover {K : Type} [Field K] {X : Scheme.{0}} (s : X ⟶ Sp K) [QuasiCompact s] :
    ∃ (n : ℕ) (D : Fin n → X.Opens), (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  obtain ⟨t, ht, hU⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
    ⟨(isCompact_univ : IsCompact (Set.univ : Set X)), isOpen_univ⟩
  haveI := ht.fintype
  refine ⟨Fintype.card t, fun i ↦ ((Fintype.equivFin t).symm i).1.1, fun i ↦ ((Fintype.equivFin t).symm i).1.2, ?_⟩
  refine eq_top_iff.2 fun x _ ↦ ?_
  have hx : x ∈ (Set.univ : Set X) := trivial
  rw [hU] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨i, hi, hxi⟩ := hx
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨Fintype.equivFin t ⟨i, hi⟩, ?_⟩
  simpa using hxi

theorem ho1_fin {K : Type} [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    FiniteDimensional K (HO1 A.hom) ∧ Module.finrank K (HO1 A.hom) = g := by
  haveI := hA.proper
  obtain ⟨n, D, hD, hcov⟩ := exists_cover A.hom
  obtain ⟨⟨e⟩, -⟩ := GlobalTheory.T.cech_cohomology_structure_sheaf_iso K A.left A.hom (Fin n) D inferInstance hD hcov
  obtain ⟨hf, h1, -⟩ := GlobalTheory.T.cech_cohomology_trivial_bundle_abelian K A g hA hg (Fin n) D hD hcov
  haveI := hf 1
  exact ⟨Module.Finite.equiv e.symm, e.finrank_eq.trans h1⟩

theorem smooth_sq {K : Type} [Field K] {A : Over (Sp K)} {g : ℕ} (hg : SmoothOfRelativeDimension g A.hom) :
    SmoothOfRelativeDimension (g + g) (A ⊗ A).hom := by
  have : SmoothOfRelativeDimension g (Limits.pullback.fst A.hom A.hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (IsPullback.of_hasPullback A.hom A.hom).flip hg
  rw [Over.tensorObj_hom]
  exact smoothOfRelativeDimension_comp g g _ _

theorem pO1_comp {K : Type} [Field K] {X Y Z : Over (Sp K)} (f : X ⟶ Y) (h : Y ⟶ Z) (a : HO1 Z.hom) :
    pO1 (f ≫ h) a = pO1 f (pO1 h a) :=
  ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.1 K K Z.left Y.left Z.hom Y.hom (RingHom.id K) h.left (ovw h) K X.left X.hom
    (RingHom.id K) f.left (ovw f) (RingHom.id K) (f ≫ h).left (ovw (f ≫ h)) (by simp)
    (fun _ ↦ rfl)).1 a).symm

theorem pO1_id {K : Type} [Field K] (X : Over (Sp K)) (a : HO1 X.hom) : pO1 (𝟙 X) a = a :=
  (GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.2.2 K X).1 a

theorem pO1_unit {K : Type} [Field K] {X Y : Over (Sp K)} (f : X ⟶ 𝟙_ (Over (Sp K))) (h : 𝟙_ (Over (Sp K)) ⟶ Y)
    (a : HO1 Y.hom) : pO1 (f ≫ h) a = 0 := by
  have : IsAffine (𝟙_ (Over (Sp K))).left := by
    show IsAffine (Spec _); infer_instance
  haveI := (GlobalTheory.AbCoh.Vanish.main.1 K _ (𝟙_ (Over (Sp K))).hom this).1
  rw [pO1_comp, Subsingleton.elim (pO1 h a) 0, map_zero]

def axesRes {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] : HO1 (A ⊗ A).hom →ₗ[K] HO1 A.hom × HO1 A.hom :=
  (pO1 (lift (𝟙 A) (toUnit A ≫ η[A]))).prod (pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)))

def projSum {K : Type} [Field K] (A : Over (Sp K)) : HO1 A.hom × HO1 A.hom →ₗ[K] HO1 (A ⊗ A).hom :=
  (pO1 (fst A A)).coprod (pO1 (snd A A))

theorem axesRes_projSum {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (x : HO1 A.hom × HO1 A.hom) :
    axesRes A (projSum A x) = x := by
  obtain ⟨a, b⟩ := x
  refine Prod.ext ?_ ?_ <;>
  simp only [axesRes, projSum, LinearMap.prod_apply, Function.prod, LinearMap.coprod_apply, map_add (f := _),
    ← pO1_comp, lift_fst, lift_snd, pO1_id, pO1_unit, Prod.fst_add, Prod.snd_add, add_zero, zero_add]

theorem axesRes_injective {K : Type} [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) : Function.Injective (axesRes A) := by
  obtain ⟨h1, h2⟩ := ho1_fin A g hA hg
  obtain ⟨h3, h4⟩ := ho1_fin (A ⊗ A) (g + g) (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) (smooth_sq hg)
  have hinj : Function.Injective (projSum A) := Function.LeftInverse.injective (axesRes_projSum A)
  have hsurj : Function.Surjective (projSum A) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Module.finrank_prod, h2, h4])).1 hinj
  intro y y' h
  obtain ⟨x, rfl⟩ := hsurj y
  obtain ⟨x', rfl⟩ := hsurj y'
  rw [axesRes_projSum, axesRes_projSum] at h
  rw [h]

theorem main : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.AxesVanishingStructureSheafDegOne A ∧ GlobalTheory.AbCoh.StructureSheafH1Primitive A ∧ Module.finrank K (HO1 A.hom) = g := by
  intro K _ _ A _ g hA hg
  have hN := axesRes_injective A g hA hg
  refine ⟨fun y h₁ h₂ ↦ ?_, fun x ↦ ?_, (ho1_fin A g hA hg).2⟩
  · refine hN ?_
    refine Prod.ext ?_ ?_ <;> simp only [axesRes, LinearMap.prod_apply, Function.prod, h₁, h₂, map_zero, Prod.fst_zero, Prod.snd_zero]
  · have := axesRes_projSum A (x, x)
    refine hN ?_
    rw [show pO1 (fst A A) x + pO1 (snd A A) x = projSum A (x, x) from rfl, this]
    refine Prod.ext ?_ ?_ <;> simp only [axesRes, LinearMap.prod_apply, Function.prod, ← pO1_comp, pO1_id, MonObj.lift_comp_one_left, MonObj.lift_comp_one_right]

end GlobalTheory.AbCoh.Axes
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

theorem GlobalTheory.JSW.MirPatch.exists_eq_on_mirS_of_slices : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ) (𝒲 : Submodule ℂ (GA E (m + 1) → ℂ)), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) → (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ W ∈ 𝒲, ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ W ∈ 𝒲, ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, (fun g => W (g * h)) ∈ 𝒲) → (∀ W ∈ 𝒲, ∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, W (g * finGL E (m + 1) u) = W g) → (∀ q ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GeneralLinearGroup.map (pInf E) q = 1 → ∃ W ∈ 𝒲, ∀ y : GL (Fin (m + 1)) (Cinf E), q * infGL E (m + 1) y ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) → W (q * infGL E (m + 1) y) = b (q * infGL E (m + 1) y)) → ∃ W ∈ 𝒲, ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), W p = b p := by
  intro E _ _ _ m S b 𝒲 hb ⟨C, hC, hbC⟩ ⟨Ub, hUbo, hUb⟩ hWe hWt hWU H
  classical
  have hsel : ∀ q : GA E (m + 1), ∃ W ∈ 𝒲, (q ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) ∧ GeneralLinearGroup.map (pInf E) q = 1 →
      ∀ y : GL (Fin (m + 1)) (Cinf E), q * infGL E (m + 1) y ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) →
        W (q * infGL E (m + 1) y) = b (q * infGL E (m + 1) y)) := by
    intro q
    by_cases hq : q ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) ∧ GeneralLinearGroup.map (pInf E) q = 1
    · obtain ⟨W, hW, h⟩ := H q hq.1 hq.2
      exact ⟨W, hW, fun _ => h⟩
    · exact ⟨0, 𝒲.zero_mem, fun h => absurd h hq⟩
  choose Wq hWq hWqb using hsel
  choose Uq hUqo hUq using fun q => hWU _ (hWq q)
  obtain ⟨K, R, j, hKo, hKc, hR, hcov, huniq⟩ :=
    GlobalTheory.T.exists_disjoint_unipotentCells_cover_compact_mirabolic E m S C hC (fun q => Ub ⊓ Uq q) (fun q => hUbo.inter (hUqo q))
  choose n hh c hhS hcutEq using GlobalTheory.T.exists_cutOperators_mirabolic_finitePlaces E m S K hKo hKc
  refine ⟨∑ x ∈ R, ∑ i, c x i • (fun g => Wq (j x) (g * hh x i)), ?_, ?_⟩
  · exact 𝒲.sum_mem fun x _ => 𝒲.sum_mem fun i _ => 𝒲.smul_mem _ (hWt _ (hWq _) _ (hhS x i))
  · intro p hp
    have e1 : (∑ x ∈ R, ∑ i, c x i • (fun g => Wq (j x) (g * hh x i))) p =
        ∑ x ∈ R, (GlobalTheory.JSW.MirPatch.cell K x).indicator (Wq (j x)) p := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun x hx => ?_
      refine hcutEq x (Wq (j x)) (hWe _ (hWq _)) (fun u hu g => hUq _ u ((hR x hx).2.2.1 hu).2 g) p hp
    have e2 : ∀ x ∈ R, (GlobalTheory.JSW.MirPatch.cell K x).indicator (Wq (j x)) p =
        (GlobalTheory.JSW.MirPatch.cell K x).indicator (fun _ => b p) p := by
      intro x hx
      by_cases hpx : p ∈ GlobalTheory.JSW.MirPatch.cell K x
      · rw [Set.indicator_of_mem hpx, Set.indicator_of_mem hpx]
        obtain ⟨hj1, hj2, -, hj4⟩ := hR x hx
        exact GlobalTheory.T.eq_on_doubleCoset_of_eq_on_archimedeanSlice E m S b (Wq (j x)) (Ub ⊓ Uq (j x)) (j x) hj1 hj2 hb (hWe _ (hWq _))
          (fun u hu g => hUb u hu.1 g) (fun u hu g => hUq _ u hu.2 g) (hWqb _ ⟨hj1, hj2⟩) p hp (hj4 hpx)
      · rw [Set.indicator_of_notMem hpx, Set.indicator_of_notMem hpx]
    rw [e1, Finset.sum_congr rfl e2]
    by_cases hbp : b p = 0
    · rw [hbp]; simp
    · obtain ⟨x0, hx0, hpx0⟩ := hcov p hp (hbC p hp hbp)
      rw [Finset.sum_eq_single x0 (fun x hx hne => Set.indicator_of_notMem
        (fun hpx => hne (huniq x hx x0 hx0 p hp hpx hpx0)) _) (fun h => absurd hx0 h),
        Set.indicator_of_mem hpx0]
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.FlatPointNe

theorem evR_sig_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → evR Xo c s.sig y ≠ 0 := by
  intro E _ _ _ H Dw l Xo c r U x _ Z τ s K _ _ _ y hy h0
  have ht : Tested y := GlobalTheory.FlagTan.fromTest_of_isLocalRing y
  have h1 : evR Xo c s.sig y * evR Xo c s.inv y = 1 := by
    rw [← CompSplitPfB.cspB_evR_mul, s.mul_inv, evR_idem hy ht]
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

end GlobalTheory.FlatPointNe
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU


theorem _root_.GlobalTheory.T.exists_translate_thetaPullback_ne_zero : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : KeyIn K) (m : ℕ), Odd m → 3 ≤ m →
    ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ x.P.A)), (∀ z : baseOver (Sp K) ⟶ x.P.A, z ^ (m ^ 2) = 1 → ∃ i, pt i = z) →
    ∀ (th : LB.Sec (LPow x.P.A x.P.L ((1 : ℕ) : ℤ) (baseOver (Sp K)))), IsPolAVSectionInverseImage x.P (baseOver (Sp K)) x.th th →
    ∀ (U : I → ThetaGrp x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))
      (t : I → LB.Sec (LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))),
    (∀ i, SymLift x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) (pt i) (U i) ∧ Tr x.P x.rig m th (U i) (t i)) →
    ∃ i, (SecMod.mk (fst (baseOver (Sp K)) x.P.A).left (t i) : EA x.P (𝟙 (Sp K)) (m ^ 2)) ≠ 0 := by
  first | exact @GlobalTheory.TransNZ.exists_ne | exact GlobalTheory.TransNZ.exists_ne | (intros; apply GlobalTheory.TransNZ.exists_ne <;> assumption)
end
