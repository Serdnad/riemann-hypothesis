module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle003
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle017
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FundamentalDomainRiemannForm
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.RingHom.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle015
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle019
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
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
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
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle001
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Mathlib.RingTheory.Smooth.StandardSmooth

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.Strat

theorem preimage_le_of_finite_surjective : ∀ (Z Z' : Scheme.{0}) [IsIntegral Z] [IsIntegral Z'] (π : Z' ⟶ Z), IsFinite π → Surjective π → ∀ V : Z'.Opens, (V : Set Z').Nonempty → ∃ U : Z.Opens, (U : Set Z).Nonempty ∧ π ⁻¹ᵁ U ≤ V :=
  PositivityTheory.Xgn.finite_surjective_image_open

end GlobalTheory.CompanionTheory.Ar.Strat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.theta_functions_finite_dim : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (N : ℕ) (J : Type) (Θ : J → (Fin g → ℂ) → ℂ), Hm.IsHermitian → (∀ l, ‖χ l‖ = 1) → 0 < N → (∀ i, Differentiable ℂ (Θ i)) → (∀ i (l : Λ) z, Θ i (z + l) = (χ l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) ^ N * Θ i z) → (∃ i, Θ i ≠ 0) → (∀ w : Fin g → ℂ, w ≠ 0 → ¬ ∀ i (t : ℂ) z, Θ i (z + t • w) = Θ i z) → ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeFormAna.pos_of_theta_power | exact GlobalTheory.CompanionTheory.Ar.HodgeFormAna.pos_of_theta_power | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeFormAna.pos_of_theta_power <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl


theorem _root_.GlobalTheory.T.fundamental_domain_riemann_form : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ k : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = k) → (∀ w : Fin g → ℂ, (∀ l ∈ Λ, ∃ k : ℤ, (w ⬝ᵥ Hm.mulVec (star l)).im = k) → w ∈ Λ) → ∀ Fd : Set (Fin g → ℂ), IsAddFundamentalDomain Λ Fd volume → (volume Fd).toReal * ‖Hm.det‖ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.SelfDualCovol.volume_mul_norm_det_eq_one | exact GlobalTheory.CompanionTheory.Ar.Sl.SelfDualCovol.volume_mul_norm_det_eq_one | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.SelfDualCovol.volume_mul_norm_det_eq_one <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

namespace GlobalTheory.CompanionTheory.Ar.DualRev

theorem dotDualRevBasis (Ω : Type) [Field Ω] (r : ℕ) (w : Module.Basis (Fin r) Ω (Fin r → Ω)) :
    ∃ v : Module.Basis (Fin r) Ω (Fin r → Ω), ∀ i j, w i ⬝ᵥ v j = if i = j.rev then 1 else 0 := by
  classical
  set v : Fin r → Fin r → Ω := fun j t => w.dualBasis (Fin.rev j) (fun s => if t = s then 1 else 0) with hv
  have key : ∀ i j, w i ⬝ᵥ v j = if i = j.rev then 1 else 0 := by
    intro i j
    have h1 : w i ⬝ᵥ v j = w.dualBasis (Fin.rev j) (w i) := by
      rw [LinearMap.pi_apply_eq_sum_univ (w.dualBasis (Fin.rev j)) (w i)]
      simp [dotProduct, hv, smul_eq_mul]
    rw [h1, Module.Basis.dualBasis_apply, Module.Basis.repr_self, Finsupp.single_apply]
  have hli : LinearIndependent Ω v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j0
    have := congrArg (fun x => w (Fin.rev j0) ⬝ᵥ x) hg
    simp only [dotProduct_sum, dotProduct_smul, key, smul_eq_mul, dotProduct_zero] at this
    simpa [Fin.rev_inj, eq_comm] using this
  have hcard : Fintype.card (Fin r) = Module.finrank Ω (Fin r → Ω) := by
    rw [Fintype.card_fin, Module.finrank_fin_fun]
  by_cases hr : r = 0
  · subst hr
    exact ⟨w, fun i => i.elim0⟩
  haveI : Nonempty (Fin r) := ⟨⟨0, Nat.pos_of_ne_zero hr⟩⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, ?_⟩
  intro i j
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  exact key i j

end GlobalTheory.CompanionTheory.Ar.DualRev
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

namespace GlobalTheory.CompanionTheory.Ar.FlagStep.AdjoinLower

theorem adjoin_lower_eq_top : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] (S : Type) (r : S → ℕ)
    (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) Ω),
    (∀ σ k, u σ k k = 1) → (∀ σ l k, l < k → u σ l k = 0) →
    Module.finrank (IntermediateField.adjoin Ω₀
      (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2)) Ω = 1 →
    IntermediateField.adjoin Ω₀
      (Set.range fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) = ⊤ := by
  intro Ω₀ Ω _ _ _ S r u hdiag hup hfin
  rw [IntermediateField.finrank_eq_one_iff_eq_top] at hfin
  rw [← hfin]
  apply le_antisymm
  · apply IntermediateField.adjoin.mono
    rintro _ ⟨⟨σ, ⟨l, k⟩, _⟩, rfl⟩
    exact ⟨⟨σ, l, k⟩, rfl⟩
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨σ, l, k⟩, rfl⟩
    rcases lt_trichotomy l k with h | h | h
    · simp only [hup σ l k h]
      exact zero_mem _
    · subst h
      simp only [hdiag σ l]
      exact one_mem _
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨σ, ⟨l, k⟩, h⟩, rfl⟩

end GlobalTheory.CompanionTheory.Ar.FlagStep.AdjoinLower
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

namespace GlobalTheory.CompanionTheory.Ar.FlagStep

theorem exists_tensor_equiv_of_semilinear :
    ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] (V V' : Type) [AddCommGroup V]
    [Module Ω₀ V] [AddCommGroup V'] [Module Ω V'] (j : V →+ V'),
    (∀ (a : Ω₀) e, j (a • e) = algebraMap Ω₀ Ω a • j e) →
    (∀ (n : ℕ) (b : Fin n → V), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) →
    Submodule.span Ω (Set.range j) = ⊤ →
    ∃ Φ : TensorProduct Ω₀ Ω V ≃ₗ[Ω] V', ∀ e, Φ (TensorProduct.mk Ω₀ Ω V 1 e) = j e := by
  intro Ω₀ Ω _ _ _ V V' _ _ _ _ j hsemi hind hspan
  letI : Module Ω₀ V' := Module.compHom V' (algebraMap Ω₀ Ω)
  haveI : IsScalarTower Ω₀ Ω V' := ⟨fun a b x => by
    change (a • b) • x = algebraMap Ω₀ Ω a • (b • x)
    rw [Algebra.smul_def, mul_smul]⟩
  let jl : V →ₗ[Ω₀] V' :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun a e => hsemi a e }
  let L : TensorProduct Ω₀ Ω V →ₗ[Ω] V' := jl.liftBaseChange Ω
  have hL : ∀ e, L (TensorProduct.mk Ω₀ Ω V 1 e) = j e := by
    intro e
    change jl.liftBaseChange Ω (1 ⊗ₜ[Ω₀] e) = j e
    rw [LinearMap.liftBaseChange_tmul, one_smul]
    rfl
  have hsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨e, rfl⟩
    exact ⟨_, hL e⟩
  let B := Module.Basis.ofVectorSpace Ω₀ V
  let C := Algebra.TensorProduct.basis Ω B
  have hC : ∀ i, L (C i) = j (B i) := by
    intro i
    rw [Algebra.TensorProduct.basis_apply]
    exact hL (B i)
  have hli : LinearIndependent Ω (fun i => j (B i)) := by
    rw [linearIndependent_iff_finset_linearIndependent]
    intro s
    let e := s.equivFin
    have h1 : LinearIndependent Ω₀ (fun k : Fin s.card => B (e.symm k).1) :=
      B.linearIndependent.comp _ (Subtype.val_injective.comp e.symm.injective)
    have h2 := (hind _ _ h1).comp e e.injective
    convert h2 using 1
    funext i
    simp
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : Finsupp.linearCombination Ω (fun i => j (B i)) (C.repr x) = 0 := by
      rw [← hx]
      conv_rhs => rw [← C.linearCombination_repr x]
      rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, map_finsuppSum]
      simp [hC]
    have h1 : C.repr x = 0 := hli (h0.trans (map_zero _).symm)
    simpa using h1
  exact ⟨LinearEquiv.ofBijective L ⟨hinj, hsurj⟩, fun e => hL e⟩

end GlobalTheory.CompanionTheory.Ar.FlagStep
end

section

namespace GlobalTheory.CompanionTheory.Ar.LocalStep

theorem exists_away_basis (S T K L : Type) [CommRing S] [CommRing T] [Field K] [Field L] [Algebra S T] [Algebra S K]
    [Algebra S L] [Algebra T L] [Algebra K L] [IsScalarTower S T L] [IsScalarTower S K L]
    [IsFractionRing S K] [IsFractionRing T L] [Algebra ℚ S] [Algebra.Smooth S T] [Algebra.Smooth ℚ S]
    (e r : ℕ) (hr : Module.finrank L (KaehlerDifferential K L) = r) (z : Fin e → S)
    (hli : LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (z i)))
    (hsp : Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤)
    (P : Ideal T) [P.IsPrime] :
    ∃ g : T, g ∉ P ∧ ∀ (T' : Type) [CommRing T'] [IsDomain T'] [Algebra T T'] [IsLocalization.Away g T']
      [Algebra ℚ T'] [Algebra T' L] [IsScalarTower T T' L],
      Algebra.Smooth ℚ T' ∧ ∃ z' : Fin (e + r) → T',
        (∀ i, z' (Fin.castAdd r i) = algebraMap T T' (algebraMap S T (z i))) ∧
        LinearIndependent T' (fun i => KaehlerDifferential.D ℚ T' (z' i)) ∧
        Submodule.span T' (Set.range fun i => KaehlerDifferential.D ℚ T' (z' i)) = ⊤ := by
  haveI : Algebra.IsSmoothAt S P := inferInstance
  obtain ⟨g, hg, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth S P
  refine ⟨g, hg, ?_⟩
  intro T' _ _ _ _ _ _ _
  letI : Algebra S T' := ((algebraMap T T').comp (algebraMap S T)).toAlgebra
  haveI : IsScalarTower S T T' := .of_algebraMap_eq' rfl
  haveI : IsScalarTower ℚ S T' := .of_algebraMap_eq fun x =>
    DFunLike.congr_fun (Subsingleton.elim (algebraMap ℚ T') ((algebraMap S T').comp (algebraMap ℚ S))) x
  haveI : IsScalarTower S T' L := .of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply S T L, IsScalarTower.algebraMap_apply S T T',
      ← IsScalarTower.algebraMap_apply T T' L]
  let f : Localization.Away g ≃ₐ[T] T' := IsLocalization.algEquiv (Submonoid.powers g) _ _
  haveI : Algebra.IsStandardSmooth S T' := Algebra.IsStandardSmooth.of_algEquiv (f.restrictScalars S)
  haveI : Algebra.Smooth S T' := inferInstance
  have hsm : Algebra.Smooth ℚ T' := Algebra.Smooth.comp ℚ S T'
  refine ⟨hsm, ?_⟩
  obtain ⟨m, w, hli', hsp'⟩ : ∃ (m : ℕ) (w : Fin m → T'),
      LinearIndependent T' (fun i => KaehlerDifferential.D S T' (w i)) ∧
      Submodule.span T' (Set.range fun i => KaehlerDifferential.D S T' (w i)) = ⊤ := by
    obtain ⟨-, I, b, hb⟩ := (Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential
      (R := S) (S := T')).1 inferInstance
    haveI : Finite I := Module.Finite.finite_basis b
    cases nonempty_fintype I
    let b' := b.reindex (Fintype.equivFin I)
    have hb' : ∀ i, ∃ x, KaehlerDifferential.D S T' x = b' i := fun i => by
      obtain ⟨x, hx⟩ := hb ⟨(Fintype.equivFin I).symm i, rfl⟩
      exact ⟨x, by simpa [b'] using hx⟩
    choose w hw using hb'
    refine ⟨_, w, ?_, ?_⟩
    · simpa only [hw] using b'.linearIndependent
    · simpa only [hw] using b'.span_eq
  haveI : IsDomain T := (IsFractionRing.injective T L).isDomain (algebraMap T L)
  haveI : IsFractionRing T' L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers g) T' L
  have hm : Module.finrank L (KaehlerDifferential K L) = m := GlobalTheory.T.kaehler_finrank_fraction_field S T' K L m w hli' hsp'
  obtain rfl : r = m := hr.symm.trans hm
  obtain ⟨h1, h2⟩ := GlobalTheory.T.kaehler_basis_tower_alt ℚ S T' e r z w hli hsp hli' hsp'
  exact ⟨_, fun i => by rw [Fin.append_left]; rfl, h1, h2⟩

theorem local_step : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω] (σ σ' : Type) [Finite σ']
    (r₀ : σ → Ω₀) (r₁ : σ' → Ω) (v : σ → σ'), (∀ p, algebraMap Ω₀ Ω (r₀ p) = r₁ (v p)) →
    ∀ (e r : ℕ) (bd : Ideal (MvPolynomial σ ℤ)), Module.finrank Ω (KaehlerDifferential Ω₀ Ω) = r →
    ∀ (h : Ω₀), h ≠ 0 → ∀ (S : Subalgebra ℚ Ω₀) (T : Subalgebra ℚ Ω),
    S = Algebra.adjoin ℚ (insert h⁻¹ (Set.range r₀)) →
    T = Algebra.adjoin ℚ (insert (algebraMap Ω₀ Ω h)⁻¹ (Set.range r₁)) →
    ∀ ψ : S →+* T, (∀ s, ((ψ s : T) : Ω) = algebraMap Ω₀ Ω s) → ψ.Smooth →
    IsFractionRing S Ω₀ → IsFractionRing T Ω → Algebra.Smooth ℚ S →
    ∀ (z : Fin e → S) (n : ℕ), n ≤ e → LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (z i)) →
    Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ →
    (∀ q : Ideal S, q.IsPrime → ((∀ g ∈ bd, ∀ s : S, (s : Ω₀) = MvPolynomial.aeval r₀ g → s ∈ q) ↔
      ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)) →
    ∀ (P : Ideal (Algebra.adjoin ℚ (Set.range r₁))), P.IsPrime →
    ∀ h₁ : Algebra.adjoin ℚ (Set.range r₁), (h₁ : Ω) = algebraMap Ω₀ Ω h → h₁ ∉ P →
    ∃ t : Algebra.adjoin ℚ (Set.range r₁), t ∉ P ∧ ∀ S' : Subalgebra ℚ Ω,
      S' = Algebra.adjoin ℚ (insert (t : Ω)⁻¹ (Set.range r₁)) →
      Algebra.Smooth ℚ S' ∧ ∃ (z' : Fin (e + r) → S') (n' : ℕ), n' ≤ e + r ∧
        LinearIndependent S' (fun i => KaehlerDifferential.D ℚ S' (z' i)) ∧
        Submodule.span S' (Set.range fun i => KaehlerDifferential.D ℚ S' (z' i)) = ⊤ ∧
        ∀ q : Ideal S', q.IsPrime →
          ((∀ g ∈ bd.map (MvPolynomial.rename v), ∀ s : S', (s : Ω) = MvPolynomial.aeval r₁ g → s ∈ q) ↔
            ∃ i : Fin (e + r), (i : ℕ) < n' ∧ z' i ∈ q) := by
  intro Ω₀ Ω _ _ _ _ _ σ σ' _ r₀ r₁ v hv e r bd hr h hh S T hS hT ψ hψ hsm hfS hfT hsS z n hn hli hsp hq
    P hP h₁ hh₁ hh₁P
  letI : Algebra S T := ψ.toAlgebra
  haveI : Algebra.Smooth S T := hsm
  haveI : IsScalarTower S T Ω := .of_algebraMap_eq fun s => (hψ s).symm
  haveI : IsScalarTower S Ω₀ Ω := .of_algebraMap_eq fun s => rfl
  have hr₁T : ∀ p, r₁ p ∈ T := fun p => by
    rw [hT]; exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨p, rfl⟩)
  have hle₁ : Algebra.adjoin ℚ (Set.range r₁) ≤ T := Algebra.adjoin_le (by rintro _ ⟨p, rfl⟩; exact hr₁T p)
  letI : Algebra (Algebra.adjoin ℚ (Set.range r₁)) T := (Subalgebra.inclusion hle₁).toRingHom.toAlgebra
  have hne₁ : h₁ ≠ 0 := fun h0 => hh₁P (h0 ▸ P.zero_mem)
  haveI : IsLocalization.Away h₁ T :=
    GlobalTheory.T.adjoin_inverse_is_localization_away Ω _ T (Set.range r₁) rfl h₁ hne₁ (by rw [hT, hh₁]) hle₁
  have hdisj : Disjoint ((Submonoid.powers h₁ : Submonoid (Algebra.adjoin ℚ (Set.range r₁))) :
      Set (Algebra.adjoin ℚ (Set.range r₁))) (↑P : Set (Algebra.adjoin ℚ (Set.range r₁))) := by
    rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
  haveI hPT : (P.map (algebraMap _ T)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers h₁) T P hP hdisj
  have hcomap : (P.map (algebraMap _ T)).comap (algebraMap _ T) = P :=
    IsLocalization.under_map_of_isPrime_disjoint (.powers h₁) T hP hdisj
  obtain ⟨g, hgP, Hg⟩ := exists_away_basis S T Ω₀ Ω e r hr z hli hsp (P.map (algebraMap _ T))
  obtain ⟨k, g₀, hk⟩ := IsLocalization.Away.surj h₁ g
  have hg₀ : g₀ ∉ P := by
    intro hmem
    have h1 := Ideal.mem_map_of_mem (algebraMap _ T) hmem
    rw [← hk] at h1
    rcases hPT.mem_or_mem h1 with h2 | h2
    · exact hgP h2
    · have h3 := hPT.mem_of_pow_mem _ h2
      have h4 : h₁ ∈ (P.map (algebraMap _ T)).comap (algebraMap _ T) := h3
      rw [hcomap] at h4
      exact hh₁P h4
  refine ⟨g₀ * h₁, hP.mul_notMem hg₀ hh₁P, ?_⟩
  intro S' hS'
  have hk' : (g : Ω) * (h₁ : Ω) ^ k = (g₀ : Ω) := congrArg T.val hk
  have hg0 : g ≠ 0 := fun h0 => hgP (h0 ▸ Ideal.zero_mem _)
  have hgΩ : (g : Ω) ≠ 0 := fun h0 => hg0 (Subtype.ext h0)
  have hHΩ : (h₁ : Ω) ≠ 0 := fun h0 => hne₁ (Subtype.ext h0)
  have hg₀Ω : (g₀ : Ω) ≠ 0 := by rw [← hk']; exact mul_ne_zero hgΩ (pow_ne_zero _ hHΩ)
  have ht : (((g₀ * h₁ : Algebra.adjoin ℚ (Set.range r₁)) : _) : Ω) = (g₀ : Ω) * h₁ := rfl
  have hr₁S' : ∀ p, r₁ p ∈ S' := fun p => by
    rw [hS']; exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨p, rfl⟩)
  have hle' : Algebra.adjoin ℚ (Set.range r₁) ≤ S' := Algebra.adjoin_le (by rintro _ ⟨p, rfl⟩; exact hr₁S' p)
  have htS' : ((g₀ : Ω) * h₁)⁻¹ ∈ S' := by
    rw [hS', ht]; exact Algebra.subset_adjoin (Set.mem_insert _ _)
  have hTS' : T ≤ S' := by
    rw [hT]
    refine Algebra.adjoin_le (Set.insert_subset ?_ (by rintro _ ⟨p, rfl⟩; exact hr₁S' p))
    have : (algebraMap Ω₀ Ω h)⁻¹ = ((g₀ : Ω) * h₁)⁻¹ * (g₀ : Ω) := by
      rw [← hh₁]; field_simp
    rw [SetLike.mem_coe, this]
    exact S'.mul_mem htS' (hle' g₀.2)
  have hEq : S' = Algebra.adjoin ℚ (insert (g : Ω)⁻¹ (T : Set Ω)) := by
    refine le_antisymm ?_ (Algebra.adjoin_le (Set.insert_subset ?_ hTS'))
    · rw [hS']
      refine Algebra.adjoin_le (Set.insert_subset ?_ ?_)
      · have hinv : (h₁ : Ω)⁻¹ ∈ T := by
          rw [hT, hh₁]; exact Algebra.subset_adjoin (Set.mem_insert _ _)
        have : (((g₀ * h₁ : Algebra.adjoin ℚ (Set.range r₁)) : _) : Ω)⁻¹ = (g : Ω)⁻¹ * ((h₁ : Ω)⁻¹) ^ (k + 1) := by
          rw [ht, ← hk', inv_pow, ← mul_inv, mul_assoc, ← pow_succ]
        rw [SetLike.mem_coe, this]
        exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Set.mem_insert _ _))
          (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_insert_of_mem _ hinv)) _)
      · rintro _ ⟨p, rfl⟩
        exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ (hr₁T p))
    · have : (g : Ω)⁻¹ = ((g₀ : Ω) * h₁)⁻¹ * (h₁ : Ω) ^ (k + 1) := by
        rw [← hk', mul_assoc, ← pow_succ, mul_inv, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hHΩ), mul_one]
      rw [SetLike.mem_coe, this]
      exact S'.mul_mem htS' (S'.pow_mem (hle' h₁.2) _)
  letI : Algebra T S' := (Subalgebra.inclusion hTS').toRingHom.toAlgebra
  haveI : IsLocalization.Away g S' := GlobalTheory.T.adjoin_inverse_is_localization_away Ω T S' (T : Set Ω) (Algebra.adjoin_eq T).symm g hg0 hEq hTS'
  haveI : IsScalarTower T S' Ω := .of_algebraMap_eq fun _ => rfl
  obtain ⟨hsm', z', hz', hli', hsp'⟩ := Hg S'
  refine ⟨hsm', z', n, by omega, hli', hsp', ?_⟩
  intro q hq'
  let θ : S →+* S' := (algebraMap T S').comp ψ
  have hθ : ∀ s, ((θ s : S') : Ω) = algebraMap Ω₀ Ω s := fun s => hψ s
  have hr₀S : ∀ p, r₀ p ∈ S := fun p => by
    rw [hS]; exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨p, rfl⟩)
  rw [GlobalTheory.T.localization_kaehler_prime_ideal Ω₀ Ω σ σ' r₀ r₁ v hv bd S S' θ hθ hr₀S hr₁S' q, hq (q.comap θ) (hq'.comap θ)]
  constructor
  · rintro ⟨i, hi, hmem⟩
    refine ⟨Fin.castAdd r i, by simpa using hi, ?_⟩
    rw [hz']; exact hmem
  · rintro ⟨j, hj, hmem⟩
    have hje : (j : ℕ) < e := by omega
    refine ⟨⟨j, hje⟩, hj, ?_⟩
    have : j = Fin.castAdd r ⟨j, hje⟩ := Fin.ext rfl
    rw [this, hz'] at hmem
    exact hmem

end GlobalTheory.CompanionTheory.Ar.LocalStep
end
