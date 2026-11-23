module

public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinalAll
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1269
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspLatticeAnyLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle013
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.LevelVectorSizeBounds
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UniformLevelMultiplicity
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle015
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle076
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle343
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1485
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LiftWeightComplexPointEqTwist
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotOntoOfCharAlone
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.IndefiniteTreeX
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.Bundle003
import GroundTheory.GlobalFields.KummerTheory.LocalIndex

@[expose] public section

section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.KFinStab

theorem kStab_iff_kStableOn : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D), CompleteSpace H → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsKMod ε σ D E → ∀ U : Submodule ℂ D, FiniteDimensional ℂ U → (KStab ε E U ↔ IsKStableOn ε σ (U.map D.subtype)) := by
  intro n ε H _ _ σ D E hc hσ hirr hK U hU
  obtain ⟨S, E', hS⟩ := CompanionTheory.D.DSIC.hSmMod n ε H σ hσ
  have hDS : D ≤ S := fun v hv =>
    (hS.mem v).2 (CompanionTheory.D.gk.admitted.kFin_mem_smoothVecs n ε H σ hσ hirr v ((hK.mem v).1 hv))
  set ι := Submodule.inclusion hDS with hι
  have hιinj : Function.Injective ι := Submodule.inclusion_injective hDS
  have hE : ∀ a b (v : D), E' a b (ι v) = ι (E a b v) := by
    intro a b v
    have key := GlobalTheory.realForm_spans n ε H (fun a b => (E a b v : H) - (E' a b (ι v) : H)) ?_ a b
    · apply Subtype.ext
      exact (sub_eq_zero.1 key).symm
    intro X hX
    have h1 := hK.real X hX v
    have h2 := hS.real X hX (ι v)
    have h3 : ((ι v : S) : H) = (v : H) := rfl
    rw [h3] at h2
    have h4 := h1.unique h2
    simp only [smul_sub, Finset.sum_sub_distrib, h4, sub_self]
  have hmap : (U.map ι).map S.subtype = U.map D.subtype := by
    rw [← Submodule.map_comp]
    rfl
  have : FiniteDimensional ℂ (U.map ι) := inferInstance
  have hL := CompanionTheory.D.DSIC.hStabLink n ε H σ S E' hσ hS (U.map ι) inferInstance
  rw [hmap] at hL
  refine Iff.trans ?_ hL
  constructor
  · intro h a b hab w hw
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
    rw [hE]
    exact Submodule.mem_map_of_mem (h a b hab v hv)
  · intro h a b hab v hv
    have := h a b hab (ι v) (Submodule.mem_map_of_mem hv)
    rw [hE] at this
    obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 this
    rwa [← hιinj hxe]

end GlobalTheory.KFinStab
end

section

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowTopBound

theorem idem_apply {G H : Type} [Group G] [Fintype G] [AddCommGroup H] [Module ℂ H] (ρ : Representation ℂ G H) {a : G → ℂ}
    (ha : GlobalTheory.IndefiniteRowSideFullHecke.GoodBasisCentralIdempotents.IsCentralIdem a) (u : H) :
    (∑ g, a g • ρ g : H →ₗ[ℂ] H) ((∑ g, a g • ρ g : H →ₗ[ℂ] H) u) = (∑ g, a g • ρ g : H →ₗ[ℂ] H) u := by
  have h1 : (∑ g, a g • ρ g : H →ₗ[ℂ] H) u = ∑ g, ∑ h, (a h * a (h⁻¹ * g)) • ρ g u := by
    simp only [← Finset.sum_smul, ha.2, LinearMap.sum_apply, LinearMap.smul_apply]
  have h2 : (∑ g, a g • ρ g : H →ₗ[ℂ] H) ((∑ g, a g • ρ g : H →ₗ[ℂ] H) u) = ∑ h, ∑ g, (a h * a g) • ρ h (ρ g u) := by

    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [h2, h1, Finset.sum_comm (f := fun g h => (a h * a (h⁻¹ * g)) • ρ g u)]
  refine Finset.sum_congr rfl fun h _ => Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
  simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, Module.End.mul_apply]

theorem le_eigenvalue {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (T S : X →ₗ[ℂ] Y) (e : Y →ₗ[ℂ] Y) (m l : ℝ)
    (hS : ∀ y, S y = e (T y)) (hee : ∀ y, e (e y) = e y) (hadj : ∀ x, e x = x → ∀ y, ⟪x, e y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hm : ∀ u, m * ‖u‖ ^ 2 ≤ ‖LinearMap.adjoint T u‖ ^ 2) (x : Y) (hx : x ≠ 0) (hl : 0 < l)
    (h : S (LinearMap.adjoint S x) = (l : ℂ) • x) : m ≤ l := by
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have hex : e x = x := by
    refine smul_right_injective Y hl' ?_
    show (l : ℂ) • e x = (l : ℂ) • x
    rw [← map_smul, ← h, hS, hee]
  have h1 : LinearMap.adjoint S x = LinearMap.adjoint T x := ext_inner_right ℂ fun f => by
    rw [LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left, hS, hadj x hex]
  have h2 : ‖LinearMap.adjoint T x‖ ^ 2 = l * ‖x‖ ^ 2 := by
    have h3 : ⟪LinearMap.adjoint S x, LinearMap.adjoint S x⟫_ℂ = (l : ℂ) * ⟪x, x⟫_ℂ := by
      rw [LinearMap.adjoint_inner_left, h, inner_smul_right]
    rw [h1, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h3
    have h4 : ((‖LinearMap.adjoint T x‖ ^ 2 : ℝ) : ℂ) = ((l * ‖x‖ ^ 2 : ℝ) : ℂ) := by
      push_cast; exact h3
    exact_mod_cast h4
  have h5 := hm x
  rw [h2] at h5
  exact le_of_mul_le_mul_right h5 (by positivity)

theorem scalar_of_ne_bot {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (T : X →ₗ[ℂ] Y) (U U' : Y →ₗ[ℂ] X)
    (hU : U' = U) (P P' : Submodule ℂ Y) (hP : P' = P) (m m' : ℝ) (hm : m ≤ m')
    (h : P' ≠ ⊥ → ∃ l : ℝ, 0 < l ∧ (∀ x ∈ P', T (U' x) = (l : ℂ) • x) ∧ m' ≤ Real.log l) :
    ∃ l : ℝ, Real.exp m ≤ l ∧ ∀ y ∈ P, T (U y) = (l : ℂ) • y := by
  subst hU hP
  by_cases hc : P' = ⊥
  · refine ⟨_, le_rfl, fun y hy => ?_⟩
    have h0 : y = 0 := (Submodule.eq_bot_iff _).1 hc y hy
    rw [h0, map_zero, map_zero, smul_zero]
  · obtain ⟨l, hl, h1, h2⟩ := h hc
    exact ⟨l, (Real.le_log_iff_exp_le hl).1 (hm.trans h2), h1⟩

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)


include R in
theorem hookPlus_le_mainTerm (i : Fin D.R.m) : GlobalTheory.LiftLower.hookPlus D i ≤ GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.mainTerm D i (sg0 D A) := by
  have hl : ∀ ρ, lab (sg0 D A) ρ = ρ := fun ρ => by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0]; exact GlobalTheory.IndefiniteRowSideFullHecke.LiftFormsMainTerm.lab_base ρ
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.mainTerm GlobalTheory.LiftLower.hookPlus GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.aPlAt
  simp only [hl]
  have hp : ∀ n a, (1 : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf n a : ℝ) := fun n a => by
    have : 0 < GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf n a := GlobalTheory.Survey.LevelVectorSizeBounds.hookProd_pos _
    exact_mod_cast this
  refine Finset.sum_le_sum fun ρ _ => Real.log_le_log (lt_of_lt_of_le one_pos (hp _ _)) ?_
  exact le_mul_of_one_le_right (zero_le_one.trans (hp _ _)) (hp _ _)

end GlobalTheory.LowTopBound

end
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StabInduce

section Abstract

variable {R L A : Type} [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup A]

theorem exists_induced (N : Submodule R L) (φ : L →+ A) (s : R → A →+ A) (H C : AddSubgroup A)
    (hφs : ∀ r a, φ (r • a) = s r (φ a)) (hs : ∀ r, ∀ z ∈ C, s r z ∈ C) (hφ : ∀ a, φ a ∈ H)
    (hN : ∀ a, φ a ∈ C ↔ a ∈ N) (hon : ∀ z ∈ H, ∃ a, z - φ a ∈ C)
    (k : A →+ A) (hks : ∀ r z, k (s r z) = s r (k z)) (hkH : ∀ z ∈ H, k z ∈ H) (hkC : ∀ z ∈ C, k z ∈ C) :
    ∃ f : (L ⧸ N) →ₗ[R] (L ⧸ N), ∀ a b, f (N.mkQ a) = N.mkQ b ↔ k (φ a) - φ b ∈ C := by
  choose g hg using fun a => hon (k (φ a)) (hkH _ (hφ a))
  have key : ∀ a b, N.mkQ (g a) = N.mkQ b ↔ k (φ a) - φ b ∈ C := by
    intro a b
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← hN, map_sub]
    constructor
    · intro h
      have := add_mem (hg a) h
      rwa [sub_add_sub_cancel] at this
    · intro h
      have := sub_mem h (hg a)
      rwa [sub_sub_sub_cancel_left] at this
  let g0 : L →ₗ[R] (L ⧸ N) :=
    { toFun := fun a => N.mkQ (g a)
      map_add' := fun a b => by
        rw [← map_add (f := _), key, map_add (f := _), map_add (f := _), map_add (f := _), add_sub_add_comm]
        exact add_mem (hg a) (hg b)
      map_smul' := fun r a => by
        rw [RingHom.id_apply, ← map_smul, key, hφs, hφs, hks, ← map_sub]
        exact hs r _ (hg a) }
  refine ⟨N.liftQ g0 fun a ha => ?_, fun a b => key a b⟩
  change N.mkQ (g a) = 0
  rw [← map_zero N.mkQ, key, map_zero, sub_zero]
  exact hkC _ ((hN a).2 ha)

theorem exists_induced_equiv (N : Submodule R L) (φ : L →+ A) (s : R → A →+ A) (H C : AddSubgroup A)
    (hφs : ∀ r a, φ (r • a) = s r (φ a)) (hs : ∀ r, ∀ z ∈ C, s r z ∈ C) (hφ : ∀ a, φ a ∈ H)
    (hN : ∀ a, φ a ∈ C ↔ a ∈ N) (hon : ∀ z ∈ H, ∃ a, z - φ a ∈ C)
    (k : A →+ A) (hks : ∀ r z, k (s r z) = s r (k z)) (hkH : ∀ z ∈ H, k z ∈ H) (hkC : ∀ z ∈ C, k z ∈ C)
    (k' : A →+ A) (hks' : ∀ r z, k' (s r z) = s r (k' z)) (hkH' : ∀ z ∈ H, k' z ∈ H) (hkC' : ∀ z ∈ C, k' z ∈ C)
    (h1 : ∀ z, k (k' z) = z) (h2 : ∀ z, k' (k z) = z) :
    ∃ γ : (L ⧸ N) ≃ₗ[R] (L ⧸ N), ∀ a b, γ (N.mkQ a) = N.mkQ b ↔ k (φ a) - φ b ∈ C := by
  obtain ⟨f, hf⟩ := exists_induced N φ s H C hφs hs hφ hN hon k hks hkH hkC
  obtain ⟨f', hf'⟩ := exists_induced N φ s H C hφs hs hφ hN hon k' hks' hkH' hkC'
  refine ⟨LinearEquiv.ofLinearMap f f' ?_ ?_, hf⟩
  · refine LinearMap.ext fun q => ?_
    obtain ⟨a, rfl⟩ := N.mkQ_surjective q
    obtain ⟨b, hb⟩ := N.mkQ_surjective (f' (N.mkQ a))
    have h := neg_mem (hkC _ ((hf' a b).1 hb.symm))
    rw [map_sub, h1, neg_sub] at h
    rw [LinearMap.comp_apply, ← hb]
    exact (hf b a).2 h
  · refine LinearMap.ext fun q => ?_
    obtain ⟨a, rfl⟩ := N.mkQ_surjective q
    obtain ⟨b, hb⟩ := N.mkQ_surjective (f (N.mkQ a))
    have h := neg_mem (hkC' _ ((hf a b).1 hb.symm))
    rw [map_sub, h2, neg_sub] at h
    rw [LinearMap.comp_apply, ← hb]
    exact (hf' b a).2 h

end Abstract

section Space

variable {D : D7} (V : HSp D)

noncomputable def halfHom (b : 𝓞 D.host.E) :
    (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddMonoidHom.mk' (halfVec V b) fun _ _ => funext fun _ => mul_add _ _ _

theorem halfVec_eq (b : 𝓞 D.host.E) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    halfVec V b z = ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • z := rfl

theorem mulVec_halfVec (m : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) (b : 𝓞 D.host.E)
    (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) : m *ᵥ halfVec V b z = halfVec V b (m *ᵥ z) := by
  rw [halfVec_eq, halfVec_eq, Matrix.mulVec_smul]

theorem map_closure_mem (I : Ideal (𝓞 D.host.E))
    (k : (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E))
    (hks : ∀ r z, k (halfVec V r z) = halfVec V r (k z)) (hk : ∀ z ∈ latGHat V 1, k z ∈ latGHat V 1) :
    ∀ z ∈ AddSubgroup.closure {u | ∃ b ∈ I, ∃ z ∈ latGHat V 1, u = halfVec V b z},
      k z ∈ AddSubgroup.closure {u | ∃ b ∈ I, ∃ z ∈ latGHat V 1, u = halfVec V b z} := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, z, hz, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨b, hb, k z, hk z hz, hks b z⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

end Space

theorem exists_levGrp_induced : ∀ (D : D7) (V : HSp D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), LatEmb V ι → ∀ κ ∈ GlobalTheory.IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V 1, ∃ γ : GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions.LevGrp Dw l, ∀ a : Dw.La, (finHom V κ).1.mulVec (finVec V (ι a)) - finVec V (ι (liftLa γ a)) ∈ AddSubgroup.closure {u | ∃ b ∈ l.Mb, ∃ z ∈ latGHat V 1, u = halfVec V b z} := by
  intro D V H Dw l ι hι κ hκ
  obtain ⟨hfg, hsp, -, -, hhat, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V 1
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hMmem : (l.M : 𝓞 D.host.E) ∈ l.Mb := by
    have h : (l.M : 𝓞 D.host.E) ∈ Ideal.span {(l.M : 𝓞 D.host.E)} := Ideal.mem_span_singleton_self _
    rw [← l.prod] at h
    exact Ideal.mul_le_left h
  have hMb : l.Mb ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hMmem
    exact hM0.ne' (Nat.cast_eq_zero.1 hMmem)
  have hκ1 : ∀ z ∈ latGHat V 1, (finHom V κ).1 *ᵥ z ∈ latGHat V 1 :=
    (GlobalTheory.Member.AALev.congruences_agree D V κ).1.2 hκ.2
  have hκ0 : ∀ z ∈ latHat V, (finHom V κ).1 *ᵥ z ∈ latHat V := by
    intro z hz
    obtain ⟨y, hy, e⟩ := hκ.2 z hz
    rw [one_smul, sub_eq_iff_eq_add] at e
    rw [e]
    exact add_mem hy hz
  have hκ2 : ∀ z ∈ latGHat V 1, (finHom V κ⁻¹).1 *ᵥ z ∈ latGHat V 1 :=
    (GlobalTheory.Member.AALev.congruences_agree D V κ⁻¹).1.2 fun z hz =>
      ⟨_, sub_mem (GlobalTheory.RecDict.finHom_inv_mulVec_mem V κ hκ0 z hz) hz, (one_smul _ _).symm⟩
  let φ : Dw.La →+ (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
    AddMonoidHom.mk' (fun a => finVec V (ι a)) fun a b => by
      rw [map_add (f := _)]
      exact GlobalTheory.Member.AALev.fv_add _ _
  have hmem : ∀ a, ι a ∈ latG V 1 := fun a => hι.2 ▸ LinearMap.mem_range_self ι a
  have hsH : ∀ r, ∀ z ∈ latGHat V 1, halfHom V r z ∈ latGHat V 1 := by
    intro r z hz
    rw [hhat] at hz ⊢
    exact GlobalTheory.Member.AALev.hat_smul_int (latG V 1) r hz
  obtain ⟨γ, hγ⟩ := exists_induced_equiv (l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) φ (halfHom V) (latGHat V 1)
    (AddSubgroup.closure {u | ∃ b ∈ l.Mb, ∃ z ∈ latGHat V 1, u = halfVec V b z})
    (fun r a => by
      change finVec V (ι (r • a)) = _
      rw [map_smul]
      exact GlobalTheory.Member.AALev.fv_smul (r : D.host.E) (ι a))
    (fun r => map_closure_mem V l.Mb (halfHom V r) (fun _ _ => funext fun _ => mul_left_comm _ _ _) (hsH r))
    (fun a => by
      rw [hhat]
      exact GlobalTheory.Member.AALev.fv_mem_hat _ (hmem a))
    (fun a => by
      refine (GlobalTheory.T.rationalVector_mem_ideal_completedLattice_iff D V l.Mb hMb (ι a)).trans ?_
      rw [← hι.2, LinearMap.range_eq_map, ← Submodule.map_smul'']
      constructor
      · rintro ⟨x, hx, e⟩
        exact hι.1 e ▸ hx
      · exact fun h => ⟨a, h, rfl⟩)
    (fun z hz => by
      rw [hhat] at hz
      obtain ⟨x, hx, w, hw, e⟩ :=
        (GlobalTheory.AdLat.hat_rational_points_and_approx _ _ _ _ hfg hsp).2.1 l.M hM0 z hz
      rw [← hι.2] at hx
      obtain ⟨a, rfl⟩ := hx
      rw [← hhat] at hw
      refine ⟨a, AddSubgroup.subset_closure ⟨_, hMmem, w, hw, ?_⟩⟩
      rw [e]
      refine (add_sub_cancel_left _ _).trans ?_
      rw [halfVec_eq, ← Nat.cast_smul_eq_nsmul (Af D.host.F ⊗[D.host.F] D.host.E)]
      congr 1
      exact (map_natCast ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := Af D.host.F)
        (B := D.host.E)).toRingHom.comp (algebraMap (𝓞 D.host.E) D.host.E)) l.M).symm)
    (Matrix.mulVecLin (finHom V κ).1).toAddMonoidHom (mulVec_halfVec V _) hκ1
    (map_closure_mem V l.Mb _ (mulVec_halfVec V _) hκ1)
    (Matrix.mulVecLin (finHom V κ⁻¹).1).toAddMonoidHom (mulVec_halfVec V _) hκ2
    (map_closure_mem V l.Mb _ (mulVec_halfVec V _) hκ2)
    (fun z => by
      change (finHom V κ).1 *ᵥ ((finHom V κ⁻¹).1 *ᵥ z) = z
      rw [Matrix.mulVec_mulVec, map_inv, Units.mul_inv, Matrix.one_mulVec])
    (fun z => by
      change (finHom V κ⁻¹).1 *ᵥ ((finHom V κ).1 *ᵥ z) = z
      rw [Matrix.mulVec_mulVec, map_inv, Units.inv_mul, Matrix.one_mulVec])
  exact ⟨γ, fun a => (hγ a _).1 (liftLa_spec γ a).symm⟩

end GlobalTheory.StabInduce
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.SiegelChar

theorem eq_one_of_siegel : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ε : ℤˣ), (∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j) → J.det ≠ 0 → ∀ c : UG (cA σ) (dbl (incM F J)) →* ℂˣ, Continuous c → (∀ (p : UG (cA σ) (dbl (incM F J))) (t : GL (Fin n) (AE F E)), (p.1.1 : Matrix _ _ (AE F E)) * diagCols (Fin n) = diagCols (Fin n) * t.1 → c p = 1) → c = 1) := by
  intro F E _ _ _ _ _ σ hCM n J ε hJ hdet c hc hP
  letI i2 : Invertible (2 : AE F E) :=
    (Invertible.map (algebraMap (AF F) (AE F E)) (2 : AF F)).copy 2 (map_ofNat _ 2).symm
  have hw1 : (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) *
      Matrix.fromBlocks 1 0 0 (-1) = 1 := by
    rw [Matrix.fromBlocks_multiply]; simp [Matrix.fromBlocks_one]
  let w0 : GL (Fin n ⊕ Fin n) (AE F E) := ⟨_, _, hw1, hw1⟩
  have hwm : w0 ∈ UG (cA σ) (dbl (incM F J)) := by
    show (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E))ᵀ * dbl (incM F J) *
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).map (cA σ) = dbl (incM F J)
    rw [dbl, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]
    simp [Matrix.fromBlocks_multiply, Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ)),
      Matrix.map_neg _ (map_neg (cA σ))]
  have hw0 : (w0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) = Matrix.fromBlocks 1 0 0 (-1) := rfl
  let w : UG (cA σ) (dbl (incM F J)) := ⟨w0, hwm⟩
  have hww : w * w = 1 := Subtype.ext (Units.ext hw1)
  have hwD : (w0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (1 : Matrix (Fin n) (Fin n) (AE F E)) = Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [hw0, Matrix.fromBlocks_mul_fromRows]; simp
  have hwN : (w0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) = Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [hw0, Matrix.fromBlocks_mul_fromRows]; simp
  have hq : ∀ (q : UG (cA σ) (dbl (incM F J))) (s : GL (Fin n) (AE F E)),
      ((q : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) =
        Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) * (s : Matrix (Fin n) (Fin n) (AE F E)) → c q = 1 := by
    intro q s hs
    have key : (w0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) *
        ((q : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) *
        (w0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (1 : Matrix (Fin n) (Fin n) (AE F E)) =
        Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (1 : Matrix (Fin n) (Fin n) (AE F E)) * (s : Matrix (Fin n) (Fin n) (AE F E)) := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hwD, hs, ← Matrix.mul_assoc, hwN]
    have h1 : c (w * q * w) = 1 := hP _ s key
    have h2 : c w * c w = 1 := by rw [← map_mul, hww, map_one]
    rw [map_mul, map_mul, mul_comm (c w), mul_assoc, h2, mul_one] at h1
    exact h1
  have hΩ : ∀ h : UG (cA σ) (dbl (incM F J)), (∃ (p : UG (cA σ) (dbl (incM F J))) (t : GL (Fin n) (AE F E)),
      (p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * diagCols (Fin n) = diagCols (Fin n) * t.1 ∧
      IsUnit (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) * ((h * p).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E))).det) →
      c h = 1 := by
    rintro h ⟨p, t, hp, hu⟩
    obtain ⟨p', q, t', s, hp', hq', e⟩ := GlobalTheory.T.bigCell_factorisation_doubledUnitaryGroup (AF F) (AE F E) (cA σ) (Fin n) (incM F J) (h * p) hu
    have h1 : c (h * p) = 1 := by rw [e, map_mul, hP p' t' hp', hq q s hq', one_mul]
    rwa [map_mul, hP p t hp, mul_one] at h1
  have hcl : IsClosed {g : UG (cA σ) (dbl (incM F J)) | c g = 1} := isClosed_eq hc continuous_const
  refine MonoidHom.ext fun g => ?_
  exact hcl.closure_subset_iff.2 (fun h hh => hΩ h hh) (GlobalTheory.T.dense_invertible_antidiagonal_corner_doubledUnitary F E σ hCM n J ε hJ hdet g)

end GlobalTheory.SiegelChar

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.matrix_adelic_decomposition_at_finite_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (X : Spc F E n)
    (Y : Spc F E d), X.L.IsFullLattice E → Y.L.IsFullLattice E → ∀ (v : Pl (F := F)) (z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    At (evFin F v) z → ∃ X₀ : Matrix (Fin n) (Fin d) E, z - GlobalTheory.EmbChart.atPlace v 1 • incM F X₀ ∈ latAtV X Y v := by
  first
  | exact @GlobalTheory.LatPtDecomp.decomp
  | intro F E _ _ _ _ _ n d X Y hX hY v z hz
    exact GlobalTheory.LatPtDecomp.decomp F E X Y hX.toIsLattice hY.toIsLattice v z hz
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

theorem _root_.GlobalTheory.T.exists_rational_sub_bounded_infinite_small_finite : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (U : Set (Af E)), U ∈ nhds (0 : Af E) → ∃ R : ℝ, 0 ≤ R ∧ ∀ x : Ad E, ∃ ξ : E, ‖pInf E (x - algebraMap E (Ad E) ξ)‖ ≤ R ∧ pFin E (x - algebraMap E (Ad E) ξ) ∈ U := by
  first | exact @GlobalTheory.AdeleApprox.exists_rat_sub_bounded_small | exact GlobalTheory.AdeleApprox.exists_rat_sub_bounded_small | (intros; apply GlobalTheory.AdeleApprox.exists_rat_sub_bounded_small <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

theorem _root_.GlobalTheory.T.lieDerivative_le_of_bound_on_finiteDirections : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ (B : Finset (Lie E a)) (C : ℝ), 0 ≤ C ∧ ∀ (ψ : GA E a → ℂ) (g : GA E a) (X : Lie E a) (M : ℝ), (∀ Y ∈ B, ‖lieD Y ψ g‖ ≤ M) → 0 ≤ M → ‖lieD X ψ g‖ ≤ C * ‖X‖ * M := by
  first | exact @GlobalTheory.CuspRapid.lieD_le_of_basis | exact GlobalTheory.CuspRapid.lieD_le_of_basis | (intros; apply GlobalTheory.CuspRapid.lieD_le_of_basis <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

theorem _root_.GlobalTheory.T.norm_sub_le_of_lieDerivative_unipotentSegment : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ψ : Sm E a) (g : GA E a) (n : Matrix (Fin a) (Fin a) (Cinf E)) (u : ℝ → GL (Fin a) (Cinf E)) (M : ℝ), n * n = 0 → (∀ τ : ℝ, (u τ).val = 1 + τ • n) → (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖lieD (toL n) ψ.1 (g * infGL E a (u τ))‖ ≤ M) → ‖ψ.1 (g * infGL E a (u 1)) - ψ.1 g‖ ≤ M := by
  first | exact @GlobalTheory.CuspRapid.norm_sub_le_of_lieD_unipotent_segment | exact GlobalTheory.CuspRapid.norm_sub_le_of_lieD_unipotent_segment | (intros; apply GlobalTheory.CuspRapid.norm_sub_le_of_lieD_unipotent_segment <;> assumption)
end
