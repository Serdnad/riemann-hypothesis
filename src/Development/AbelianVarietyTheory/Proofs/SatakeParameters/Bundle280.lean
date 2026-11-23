module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle187
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle346
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle220
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle254
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle257
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfJacquetConstituentEmptyBlock
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle258
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct ComplexOrder
open MeasureTheory Formalism.IndefR.Datum Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
namespace GlobalTheory.ThetaLiftGrowth

theorem modGrowth_thetaIntegral : ∀ {D : D7} (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ) (V W : Formalism.BasicNotions.TH.HSp D)
    (χS χT : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)),
    IsWeilDatumO ψ V W χS χT om → (∀ τ, (gramAt D V τ).PosDef) →
    ∀ (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 ν →
    ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO V W → ℂ)),
    (∀ x, IsThetaFunO ψ V W (L x)) → ∀ u : GA D V → X, Continuous u → (∀ γ ∈ GQ V, ∀ h, u (γ * h) = u h) →
    GlobalTheory.Grow.ModGrowth W (fun g => ∫ h in 𝓕, thetaKO om h g (L (u h)) ∂ν) := by
  intro D ψ V W χS χT om hom hV ν 𝓕 hν h𝓕 X _ _ _ L hL u hu hinv
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.definite_unitary_cocompact V hV
  obtain ⟨H, hH⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact V hK
  let b := Module.finBasis ℂ X
  have hgr := fun k => GlobalTheory.Core.Rk.ThetaGrowthBoth.thetaKO_modGrowth₂ D ψ V W χS χT om hom (L (b k)) (hL _)
  choose C A hCA using hgr
  have hM : ∀ k, ∃ M : ℝ, ∀ c ∈ K, ‖b.coord k (u c)‖ ≤ M := fun k =>
    hK.exists_bound_of_continuousOn ((b.coord k).continuous_of_finiteDimensional.comp hu).continuousOn
  choose M hM using hM
  have hfin := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V ν 𝓕 hν h𝓕
  have hdec : ∀ h g, thetaKO om h g (L (u h)) = ∑ k, b.coord k (u h) * thetaKO om h g (L (b k)) := by
    intro h g
    conv_lhs => rw [← b.sum_repr (u h)]

    simp only [thetaKO, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Module.Basis.coord_apply]
  have hθinv : ∀ γ ∈ GQ V, ∀ c g (f : WO V W → ℂ), IsThetaFunO ψ V W f → thetaKO om (γ * c) g f = thetaKO om c g f := by
    intro γ hγ c g f hf
    have e : (γ * c, g) = ((γ, 1) : GA D V × GA D W) * (c, g) := by rw [Prod.mk_mul_mk, one_mul]
    simp only [thetaKO]
    rw [e, map_mul]
    exact hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ hf)
  set H' := max H 1 with hH'
  set N := ∑ k, A k with hN
  set B := ∑ k, |M k| * |C k| with hB
  have hb : ∀ g h, ‖thetaKO om h g (L (u h))‖ ≤ B * (H' * GlobalTheory.Grow.height W g) ^ N := by
    intro g h
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
    rw [hdec, hB, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, hinv γ hγ c, hθinv γ hγ c g _ (hL _)]
    have h1c := GlobalTheory.Grow.one_le_height V c
    have h1g := GlobalTheory.Grow.one_le_height W g
    have hcH : GlobalTheory.Grow.height V c ≤ H' := (hH c hc).trans (le_max_left _ _)
    have hx1 : 1 ≤ GlobalTheory.Grow.height V c * GlobalTheory.Grow.height W g := one_le_mul_of_one_le_of_one_le h1c h1g
    have hxy : GlobalTheory.Grow.height V c * GlobalTheory.Grow.height W g ≤ H' * GlobalTheory.Grow.height W g :=
      mul_le_mul_of_nonneg_right hcH (by linarith)
    have hθ : ‖thetaKO om c g (L (b k))‖ ≤ |C k| * (H' * GlobalTheory.Grow.height W g) ^ N := by
      refine (hCA k c g).trans ?_
      refine mul_le_mul (le_abs_self _) ?_ (by positivity) (abs_nonneg _)
      calc (GlobalTheory.Grow.height V c * GlobalTheory.Grow.height W g) ^ A k
          ≤ (H' * GlobalTheory.Grow.height W g) ^ A k := pow_le_pow_left₀ (by linarith) hxy _
        _ ≤ (H' * GlobalTheory.Grow.height W g) ^ N :=
          pow_le_pow_right₀ (hx1.trans hxy) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))
    calc ‖b.coord k (u c)‖ * ‖thetaKO om c g (L (b k))‖
        ≤ |M k| * (|C k| * (H' * GlobalTheory.Grow.height W g) ^ N) :=
          mul_le_mul ((hM k c hc).trans (le_abs_self _)) hθ (norm_nonneg _) (abs_nonneg _)
      _ = |M k| * |C k| * (H' * GlobalTheory.Grow.height W g) ^ N := by ring
  refine ⟨B * H' ^ N * ν.real 𝓕, N, fun g => ?_⟩
  calc ‖∫ h in 𝓕, thetaKO om h g (L (u h)) ∂ν‖ ≤ B * (H' * GlobalTheory.Grow.height W g) ^ N * ν.real 𝓕 :=
        norm_setIntegral_le_of_norm_le_const hfin fun h _ => hb g h
    _ = B * H' ^ N * ν.real 𝓕 * GlobalTheory.Grow.height W g ^ N := by rw [mul_pow]; ring

end GlobalTheory.ThetaLiftGrowth
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.jacquet_rank_one_central : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin d) k) V) (ω : kˣ →* ℂˣ) (s' : ℕ) (b : Fin s' → ℕ) (f : (Σ j, Fin (b j)) ≃ Fin d) (j : Fin s'), d = 1 → b j = 1 → GlobalTheory.SmGL.HasCentralChar σ ω → ∀ (z : kˣ) (x : GlobalTheory.PRep.Jacquet σ (GlobalTheory.SmGL.unipRad k f)), GlobalTheory.SmGL.jac f σ (Pi.mulSingle j (Matrix.GeneralLinearGroup.scalar (Fin (b j)) z)) x = (ω z : ℂ) • x := by
  first | exact @GlobalTheory.JacGL1.jac_mulSingle_scalar | exact GlobalTheory.JacGL1.jac_mulSingle_scalar | (intros; apply GlobalTheory.JacGL1.jac_mulSingle_scalar <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.parabolicInduction_preserves_injective_and_exactness : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (X Y : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (ξ : Representation ℂ (Levi k m) X) (η : Representation ℂ (Levi k m) Y) (i : ξ.IntertwiningMap η), Function.Injective i → Function.Injective (parIndMap e i) ∧ ∀ (Z : Type) [AddCommGroup Z] [Module ℂ Z] (ζ : Representation ℂ (Levi k m) Z) (q : η.IntertwiningMap ζ), (∀ y, q y = 0 → ∃ x, i x = y) → ∀ φ, parIndMap e q φ = 0 → ∃ ψ, parIndMap e i ψ = φ := by
  first | exact @GlobalTheory.ParIndExact.parInd_exact | exact GlobalTheory.ParIndExact.parInd_exact | (intros; apply GlobalTheory.ParIndExact.parInd_exact <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.parabolicInduction_preserves_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ (Levi k m) W) (ρ' : Representation ℂ (Levi k m) W'), IsSmooth ρ' → IsSubquotient ρ ρ' → IsSubquotient (parInd e ρ) (parInd e ρ') := by
  first | exact @GlobalTheory.ParIndSubquot.parInd_isSubquotient | exact GlobalTheory.ParIndSubquot.parInd_isSubquotient | (intros; apply GlobalTheory.ParIndSubquot.parInd_isSubquotient <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.cuspidal_jacquet_subquotient_at_most_one_nonempty_block : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin d) k) V) (s' : ℕ) (b : Fin s' → ℕ) (f : (Σ j, Fin (b j)) ≃ Fin d) (X : Fin s' → Type) [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)] (ρ : ∀ j, Representation ℂ (GL (Fin (b j)) k) (X j)), GlobalTheory.SmGL.IsCuspidal σ → (∀ j, Nontrivial (X j)) → GlobalTheory.SmGL.IsSubquotient (GlobalTheory.SmGL.piTensor ρ) (GlobalTheory.SmGL.jac f σ) → ∀ j j', 0 < b j → 0 < b j' → j = j' := by
  first | exact @GlobalTheory.SmGL.CuspRow.block_unique_of_isCuspidal | exact GlobalTheory.SmGL.CuspRow.block_unique_of_isCuspidal | (intros; apply GlobalTheory.SmGL.CuspRow.block_unique_of_isCuspidal <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.irreducible_gl1_iso_det : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin d) k) V) (ω : kˣ →* ℂˣ), d = 1 → σ.IsIrreducible → GlobalTheory.SmGL.HasCentralChar σ ω → Nonempty (σ.Equiv (GlobalTheory.SmGL.detRep (Fin d) ω)) := by
  first | exact @GlobalTheory.GLOneChar.equiv_detRep_of_isIrreducible | exact GlobalTheory.GLOneChar.equiv_detRep_of_isIrreducible | (intros; apply GlobalTheory.GLOneChar.equiv_detRep_of_isIrreducible <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

theorem _root_.GlobalTheory.T.exists_levi_block_eigenvector_at_identity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α : Type) [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (n : Type) [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (X : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)) (χ : kˣ →* ℂˣ) (x : IndSp e (piTensor σ)), x ≠ 0 → (∀ g ∈ KO k n, multiProd e σ g x = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • x) → ∃ w : PiTensorProduct ℂ X, w ≠ 0 ∧ ∀ a, ∀ h ∈ KO k (m a), piTensor σ (Pi.mulSingle a h) w = (χ (Matrix.GeneralLinearGroup.det h) : ℂ) • w := by
  first | exact @GlobalTheory.SphBlock.exists_eigen_at_one | exact GlobalTheory.SphBlock.exists_eigen_at_one | (intros; apply GlobalTheory.SphBlock.exists_eigen_at_one <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.isSubquotient_parInd_products_flattened : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s n : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (X : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (X a b)] [∀ a b, Module ℂ (X a b)] (ρ : ∀ a b, Representation ℂ (GL (Fin (d' a b)) k) (X a b)), (∀ a b, IsSmooth (ρ a b)) → ∃ E : (Σ c : Fin (∑ a, t a), Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) ≃ Fin n, IsSubquotient (multiProd e fun a => multiProd (e' a) (ρ a)) (multiProd E fun c => ρ (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) := by
  first | exact @GlobalTheory.SmGL.Stages.isSubquotient_multiProd_multiProd | exact GlobalTheory.SmGL.Stages.isSubquotient_multiProd_multiProd | (intros; apply GlobalTheory.SmGL.Stages.isSubquotient_multiProd_multiProd <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

theorem _root_.GlobalTheory.T.isSpherical_twist_of_jacquet_constituent_empty_block : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin t) k) W) (c : Bool → ℕ) (f : (Σ j, Fin (c j)) ≃ Fin t) (s : ∀ j, IrrRep (GL (Fin (c j)) k)) (χ : kˣ →* ℂˣ) (z : (s true).V), IsSmooth π → π.IsIrreducible → c false = 0 → IsSubquotient (piTensor fun j => (s j).ρ) (_root_.GlobalTheory.SmGL.jac f π) → z ≠ 0 → (∀ g ∈ KO k (Fin (c true)), (s true).ρ g z = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • z) → IsSpherical (_root_.GlobalTheory.SmGL.twist π (detChar (Fin t) χ⁻¹)) := by
  first | exact @GlobalTheory.EmptyFirstBlock.isSpherical_twist_of_empty_block | exact GlobalTheory.EmptyFirstBlock.isSpherical_twist_of_empty_block | (intros; apply GlobalTheory.EmptyFirstBlock.isSpherical_twist_of_empty_block <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.exists_intertwining_of_central_filtration_step : ∀ {G V Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G V) (τ : Representation ℂ G Y) (N : ℕ) (S : Fin (N + 1) → Subrepresentation ρ),
    Monotone S → S 0 = ⊥ → S (Fin.last N) = ⊤ → ∀ (z : G), (∀ g, g * z = z * g) →
    ∀ (t₀ : Fin N) (c : ℂ) (c' : Fin N → ℂ), (∀ t, t ≠ t₀ → c' t ≠ c) →
    (∀ t, t ≠ t₀ → ∀ y, subQuot (S t.succ) (S t.castSucc) z y = c' t • y) →
    Nonempty ((subQuot (S t₀.succ) (S t₀.castSucc)).Equiv τ) → (∀ y, τ z y = c • y) → Nontrivial Y →
    ∃ (φ : ρ.IntertwiningMap τ) (v : V), φ v ≠ 0 := by
  first | exact @GlobalTheory.exists_intertwining_of_central_step | exact GlobalTheory.exists_intertwining_of_central_step | (intros; apply GlobalTheory.exists_intertwining_of_central_step <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.property_descends_finiteLength_to_irreducible_subquotient : ∀ (H : Type) [Group H] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V) (P : ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y], Representation ℂ H Y → Prop), HasFiniteLength ρ → (∀ (Y Y' : Type) [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Y'] [Module ℂ Y'] (σ : Representation ℂ H Y) (σ' : Representation ℂ H Y') (f : σ.IntertwiningMap σ'), Function.Injective f → P Y σ → P Y' σ') → (∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (σ : Representation ℂ H Y), P Y σ → Nontrivial Y) → (∀ A B : Subrepresentation ρ, B ≤ A → P _ A.toRepresentation → P _ B.toRepresentation ∨ P _ (subQuot A B)) → P V ρ → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (σ : Representation ℂ H Y), σ.IsIrreducible ∧ IsSubquotient σ ρ ∧ P Y σ := by
  first | exact @GlobalTheory.ExactIrr.main | exact GlobalTheory.ExactIrr.main | (intros; apply GlobalTheory.ExactIrr.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

theorem _root_.GlobalTheory.T.exists_irreducible_subquotient_common_eigenvector : ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (S : Set G) (θ : G → ℂ) (x : V), x ≠ 0 → (∀ g ∈ S, ρ g x = θ g • x) → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ G Y), τ.IsIrreducible ∧ IsSubquotient τ ρ ∧ ∃ y : Y, y ≠ 0 ∧ ∀ g ∈ S, τ g y = θ g • y := by
  first | exact @GlobalTheory.EigenSubquot.exists_irreducible_subquotient_eigen | exact GlobalTheory.EigenSubquot.exists_irreducible_subquotient_eigen | (intros; apply GlobalTheory.EigenSubquot.exists_irreducible_subquotient_eigen <;> assumption)
end
