module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle272
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle203
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle787
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle082
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle015
public import Formalism.LocalToGlobal.KernelLattices.Bundle004
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle134
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle199
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle158
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle141
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle268
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle252
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle018
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle253
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Bundle001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle010

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] GlobalTheory.NPin.ThetaMod.acg GlobalTheory.NPin.ThetaMod.mod

theorem _root_.GlobalTheory.T.finiteType_spanned_by_splitPlace_localComponent : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.FinTyp L n) (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS π.S s τ → ∀ (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → π.S ≤ ⨆ (T : τ.V →ₗ[ℂ] (GAf L n → ℂ)) (_ : (∀ v, T v ∈ π.S) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v, T (τ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v)), LinearMap.range T := by
  first | exact @GlobalTheory.FinTypSpanLoc.main | exact GlobalTheory.FinTypSpanLoc.main | (intros; apply GlobalTheory.FinTypSpanLoc.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] GlobalTheory.NPin.ThetaMod.acg GlobalTheory.NPin.ThetaMod.mod

theorem _root_.GlobalTheory.T.thetaPairing_of_invariant_trilinear_form : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r n : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (μ : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin n) k) W), IsAdmissible σ → IsUnitarisable σ → IsOpen (μ.ker : Set kˣ) → ∀ (b : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), b ≠ 0 → (∀ (g : GL (Fin r) k) (h : GL (Fin n) k) (Φ Φ' : SB (Matrix (Fin n) (Fin r) k)), (Φ' : Matrix (Fin n) (Fin r) k → ℂ) = om μ g h Φ → ∀ a c, b Φ' (π h a) (σ g c) = b Φ a c) → ThetaPair μ σ π := by
  first | exact @GlobalTheory.ThetaRiesz.thetaPair_of_invariant_form | exact GlobalTheory.ThetaRiesz.thetaPair_of_invariant_form | (intros; apply GlobalTheory.ThetaRiesz.thetaPair_of_invariant_form <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.inertiaInvariantUnderUnramifiedTwist_of_weilDeligne : ∀ (D : D7), GlobalTheory.RowTie.WDTie D.nd D.naut → IneUnr D := by
  first | exact @GlobalTheory.IneUnrTwist.main | exact GlobalTheory.IneUnrTwist.main | (intros; apply GlobalTheory.IneUnrTwist.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

noncomputable section

namespace GlobalTheory.EigTwist

open scoped Matrix

variable {Γ : Type} [Group Γ] {K : Type} [Field K]

def sumL (L : List (Σ m : ℕ, Γ →* GL (Fin m) K)) : Σ m : ℕ, Γ →* GL (Fin m) K :=
  L.foldr (fun p s => ⟨p.1 + s.1, Formalism.MainNotions.SumRepresentations.At.sumRep p.2 s.2⟩) ⟨0, 1⟩

theorem isSSRep_sumL : ∀ L : List (Σ m : ℕ, Γ →* GL (Fin m) K), (∀ p ∈ L, IsSSRep p.2) →
    IsSSRep (sumL L).2
  | [], _ => GlobalTheory.BCGal.ss_zero _
  | p :: L, h => GlobalTheory.BCGal.ss_sumRep _ _ (h p List.mem_cons_self)
      (isSSRep_sumL L fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem charpoly_sumRep {a b : ℕ} (ρ : Γ →* GL (Fin a) K) (ρ' : Γ →* GL (Fin b) K) (g : Γ) :
    ((Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ' g : GL _ _) : Matrix (Fin (a + b)) (Fin (a + b)) K).charpoly =
      ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) K).charpoly *
        ((ρ' g : GL _ _) : Matrix (Fin b) (Fin b) K).charpoly := by
  rw [GlobalTheory.BCGal.sumRep_val, Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₁₂]

theorem charpoly_sumL : ∀ (L : List (Σ m : ℕ, Γ →* GL (Fin m) K)) (g : Γ),
    (((sumL L).2 g : GL _ _) : Matrix (Fin (sumL L).1) (Fin (sumL L).1) K).charpoly =
      (L.map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) K).charpoly).prod
  | [], g => by
    rw [List.map_nil, List.prod_nil]
    exact Polynomial.eq_one_of_monic_natDegree_zero (Matrix.charpoly_monic _)
      (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; rfl)
  | p :: L, g => by
    rw [List.map_cons, List.prod_cons, ← charpoly_sumL L g]
    exact charpoly_sumRep p.2 (sumL L).2 g

theorem sumRep_mulVec_inl {a b : ℕ} (ρ : Γ →* GL (Fin a) K) (ρ' : Γ →* GL (Fin b) K) (g : Γ)
    (w : Fin (a + b) → K) (i : Fin a) :
    (((Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ' g : GL _ _) : Matrix (Fin (a + b)) (Fin (a + b)) K) *ᵥ w)
      (finSumFinEquiv (Sum.inl i)) =
      (((ρ g : GL _ _) : Matrix (Fin a) (Fin a) K) *ᵥ (w ∘ finSumFinEquiv ∘ Sum.inl)) i := by
  rw [GlobalTheory.BCGal.sumRep_val]
  simp [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, Function.comp_def]

theorem sumRep_mulVec_inr {a b : ℕ} (ρ : Γ →* GL (Fin a) K) (ρ' : Γ →* GL (Fin b) K) (g : Γ)
    (w : Fin (a + b) → K) (j : Fin b) :
    (((Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ' g : GL _ _) : Matrix (Fin (a + b)) (Fin (a + b)) K) *ᵥ w)
      (finSumFinEquiv (Sum.inr j)) =
      (((ρ' g : GL _ _) : Matrix (Fin b) (Fin b) K) *ᵥ (w ∘ finSumFinEquiv ∘ Sum.inr)) j := by
  rw [GlobalTheory.BCGal.sumRep_val]
  simp [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, Function.comp_def]

theorem eigen_pair (χ : Γ →* Kˣ) {a b : ℕ} (ρ : Γ →* GL (Fin a) K) (ρ' : Γ →* GL (Fin b) K)
    (w : Fin (a + b) → K) (hw : w ≠ 0)
    (he : ∀ g, ((Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ' g : GL _ _) : Matrix (Fin (a + b)) (Fin (a + b)) K) *ᵥ w =
      ((χ g : Kˣ) : K) • w) :
    (∃ v : Fin a → K, v ≠ 0 ∧ ∀ g, ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) K) *ᵥ v = ((χ g : Kˣ) : K) • v) ∨
    (∃ v : Fin b → K, v ≠ 0 ∧ ∀ g, ((ρ' g : GL _ _) : Matrix (Fin b) (Fin b) K) *ᵥ v = ((χ g : Kˣ) : K) • v) := by
  by_cases h1 : w ∘ finSumFinEquiv ∘ Sum.inl = 0
  · right
    refine ⟨w ∘ finSumFinEquiv ∘ Sum.inr, fun h2 => hw ?_, fun g => ?_⟩
    · funext j
      obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
      rcases s with i | i
      · exact congrFun h1 i
      · exact congrFun h2 i
    · funext j
      have h3 := congrFun (he g) (finSumFinEquiv (Sum.inr j))
      rw [sumRep_mulVec_inr] at h3
      rw [h3]
      simp
  · left
    refine ⟨w ∘ finSumFinEquiv ∘ Sum.inl, h1, fun g => ?_⟩
    funext i
    have h3 := congrFun (he g) (finSumFinEquiv (Sum.inl i))
    rw [sumRep_mulVec_inl] at h3
    rw [h3]
    simp

theorem eigen_sumL (χ : Γ →* Kˣ) : ∀ (L : List (Σ m : ℕ, Γ →* GL (Fin m) K)) (w : Fin (sumL L).1 → K),
    w ≠ 0 → (∀ g, (((sumL L).2 g : GL _ _) : Matrix (Fin (sumL L).1) (Fin (sumL L).1) K) *ᵥ w =
      ((χ g : Kˣ) : K) • w) →
    ∃ p ∈ L, ∃ v : Fin p.1 → K, v ≠ 0 ∧
      ∀ g, ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) K) *ᵥ v = ((χ g : Kˣ) : K) • v := by
  intro L
  induction L with
  | nil =>
    intro w hw _
    exact (hw (funext fun i => (Nat.not_lt_zero _ i.2).elim)).elim
  | cons p L ih =>
    intro w hw he
    rcases eigen_pair χ p.2 (sumL L).2 w hw he with ⟨v, hv0, hv⟩ | ⟨v, hv0, hv⟩
    · exact ⟨p, List.mem_cons_self, v, hv0, hv⟩
    · obtain ⟨q, hq, u, hu0, hu⟩ := ih v hv0 hv
      exact ⟨q, List.mem_cons_of_mem _ hq, u, hu0, hu⟩

theorem eigen_transfer {n m : ℕ} (ρ : Γ →* GL (Fin n) K) (σ : Γ →* GL (Fin m) K) (hρ : IsSSRep ρ)
    (hσ : IsSSRep σ)
    (hc : ∀ g, ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) K).charpoly =
      ((σ g : GL _ _) : Matrix (Fin m) (Fin m) K).charpoly)
    (χ : Γ →* Kˣ) (v : Fin n → K) (hv0 : v ≠ 0)
    (hv : ∀ g, ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) K) *ᵥ v = ((χ g : Kˣ) : K) • v) :
    ∃ w : Fin m → K, w ≠ 0 ∧ ∀ g, ((σ g : GL _ _) : Matrix (Fin m) (Fin m) K) *ᵥ w = ((χ g : Kˣ) : K) • w := by
  have hnm : n = m := by
    have h1 := congrArg Polynomial.natDegree (hc 1)
    rwa [Matrix.charpoly_natDegree_eq_dim, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
      Fintype.card_fin] at h1
  subst hnm
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix ρ σ hρ hσ hc
  refine ⟨((P⁻¹ : GL _ _) : Matrix (Fin n) (Fin n) K) *ᵥ v, fun h0 => hv0 ?_, fun g => ?_⟩
  · have h1 := congrArg (fun u => ((P : GL _ _) : Matrix (Fin n) (Fin n) K) *ᵥ u) h0
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h1
    rwa [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at h1
  · rw [Matrix.mulVec_mulVec, hP g]
    have e : ((P⁻¹ * ρ g * P : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((P⁻¹ : GL _ _) : Matrix (Fin n) (Fin n) K) =
        ((P⁻¹ : GL _ _) : Matrix (Fin n) (Fin n) K) * ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) K) := by
      rw [← Units.val_mul, ← Units.val_mul, mul_assoc, mul_inv_cancel, mul_one]
    rw [e, ← Matrix.mulVec_mulVec, hv g, Matrix.mulVec_smul]

end GlobalTheory.EigTwist


open GlobalTheory.EigTwist in
theorem GlobalTheory.eigenCharTwist_holds : EigenCharTwist := by
  intro K _ _ Γ _ n ρ L χ hρ hL hc hv
  obtain ⟨v, hv0, hv⟩ := hv
  have hS := isSSRep_sumL L hL
  have hcS : ∀ g, ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) K).charpoly =
      (((sumL L).2 g : GL _ _) : Matrix (Fin (sumL L).1) (Fin (sumL L).1) K).charpoly :=
    fun g => (hc g).trans (charpoly_sumL L g).symm
  obtain ⟨w, hw0, hw⟩ := eigen_transfer ρ (sumL L).2 hρ hS hcS χ v hv0 hv
  exact eigen_sumL χ L w hw0 hw
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst

noncomputable section

namespace GlobalTheory.AboveLRes

theorem exists_model_of_mem {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {a : ℕ} (T : FinExt l)
    (ρ : Γ →* GL (Fin a) (Om l))
    (hρ : ∀ g i k, ((ρ g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k ∈ T.1) :
    ∃ ρ' : Γ →* GL (Fin a) ↥T.1, mapRep (algebraMap ↥T.1 (Om l)) ρ' = ρ := by
  let f : GL (Fin a) ↥T.1 →* GL (Fin a) (Om l) := Units.map ((algebraMap ↥T.1 (Om l)).mapMatrix : Matrix (Fin a) (Fin a) ↥T.1 →+* Matrix (Fin a) (Fin a) (Om l)).toMonoidHom
  have hmi : Function.Injective ((algebraMap ↥T.1 (Om l)).mapMatrix : Matrix (Fin a) (Fin a) ↥T.1 → _) :=
    Matrix.map_injective (algebraMap ↥T.1 (Om l)).injective
  have hf : Function.Injective f := Units.map_injective hmi
  let lift : Γ → Matrix (Fin a) (Fin a) ↥T.1 := fun g => Matrix.of fun i k => ⟨_, hρ g i k⟩
  have hlift : ∀ g, (algebraMap ↥T.1 (Om l)).mapMatrix (lift g) = ((ρ g : GL (Fin a) (Om l)) : Matrix _ _ _) :=
    fun g => by ext i k; rfl
  have hm : ∀ g, ρ g ∈ f.range := by
    intro g
    refine ⟨⟨lift g, lift g⁻¹, hmi ?_, hmi ?_⟩, Units.ext (hlift g)⟩
    · rw [map_mul, hlift, hlift, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    · rw [map_mul, hlift, hlift, map_one, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  refine ⟨(MonoidHom.ofInjective hf).symm.toMonoidHom.comp (ρ.codRestrict f.range hm), ?_⟩
  exact MonoidHom.ext fun g => MonoidHom.apply_ofInjective_symm hf ⟨ρ g, hm g⟩

end GlobalTheory.AboveLRes

namespace GlobalTheory.AboveLRes

theorem exists_decRes_eq {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L]
    [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] {A : ValuationSubring Ω} (σ : ↥(_root_.ReciprocityTheory.Gal.Dec (F := K) A))
    (hσ : ∀ x : L, (σ : _root_.Formalism.ConjugateSelfDual.G K Ω) (algebraMap L Ω x) = algebraMap L Ω x) :
    ∃ σ' : ↥(_root_.ReciprocityTheory.Gal.Dec (F := L) A), decRes A σ' = σ := by
  let τ : _root_.Formalism.ConjugateSelfDual.G L Ω := { (σ : _root_.Formalism.ConjugateSelfDual.G K Ω).toRingEquiv with commutes' := hσ }
  have hτ : τ ∈ _root_.ReciprocityTheory.Gal.Dec (F := L) A := by
    have hg := mem_Dec.mp σ.2
    rw [mem_Dec]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    conv_rhs => rw [← hg, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  exact ⟨⟨τ, hτ⟩, Subtype.ext (AlgEquiv.ext fun _ => rfl)⟩

end GlobalTheory.AboveLRes

namespace GlobalTheory.AboveLRes


open GlobalTheory.AboveL in
theorem exists_model_dec {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) {l : ℕ}
    [Fact l.Prime] {a : ℕ} (r : _root_.Formalism.ConjugateSelfDual.G K Ω →* GL (Fin a) (Om l)) (LL' B : FinExt l)
    (r' : ↥(_root_.ReciprocityTheory.Gal.Dec (F := L) A) →* GL (Fin a) ↥LL'.1)
    (hm' : mapRep (algebraMap ↥LL'.1 (Om l)) r' = (resTo L r).comp (_root_.ReciprocityTheory.Gal.Dec (F := L) A).subtype) :
    ∃ (T : FinExt l) (r₁ : ↥(_root_.ReciprocityTheory.Gal.Dec (F := K) A) →* GL (Fin a) ↥T.1), B.1 ≤ T.1 ∧
      mapRep (algebraMap ↥T.1 (Om l)) r₁ = r.comp (_root_.ReciprocityTheory.Gal.Dec (F := K) A).subtype := by
  let M : IntermediateField K Ω := (IsScalarTower.toAlgHom K L Ω).fieldRange
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : FiniteDimensional K M :=
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K L Ω)).toLinearEquiv.finiteDimensional
  haveI : Finite (_root_.Formalism.ConjugateSelfDual.G K Ω ⧸ M.fixingSubgroup) := Subgroup.quotient_finite_of_isOpen _ M.fixingSubgroup_isOpen
  haveI : M.fixingSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  set H : Subgroup ↥(_root_.ReciprocityTheory.Gal.Dec (F := K) A) := M.fixingSubgroup.subgroupOf (_root_.ReciprocityTheory.Gal.Dec (F := K) A) with hH
  haveI : Finite (↥(_root_.ReciprocityTheory.Gal.Dec (F := K) A) ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  set S : Set (Om l) := Set.range fun x : (↥(_root_.ReciprocityTheory.Gal.Dec (F := K) A) ⧸ H) × Fin a × Fin a =>
    ((r (x.1.out : _root_.Formalism.ConjugateSelfDual.G K Ω) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) x.2.1 x.2.2 with hS
  have hSf : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] S) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  obtain ⟨T, hT⟩ : ∃ T : FinExt l, T.1 = IntermediateField.adjoin ℚ_[l] S ⊔ LL'.1 ⊔ B.1 :=
    ⟨supExt (supExt ⟨_, hSf⟩ LL') B, rfl⟩
  have hET : IntermediateField.adjoin ℚ_[l] S ≤ T.1 := hT ▸ le_sup_left.trans le_sup_left
  have hLT : LL'.1 ≤ T.1 := hT ▸ le_sup_right.trans le_sup_left
  have hBT : B.1 ≤ T.1 := hT ▸ le_sup_right
  have hfix : ∀ σ : ↥(_root_.ReciprocityTheory.Gal.Dec (F := K) A), σ ∈ H → ∀ i k,
      ((r (σ : _root_.Formalism.ConjugateSelfDual.G K Ω) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k ∈ LL'.1 := by
    intro σ hσ i k
    have hσ' : ∀ x : L, (σ : _root_.Formalism.ConjugateSelfDual.G K Ω) (algebraMap L Ω x) = algebraMap L Ω x := fun x =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Subgroup.mem_subgroupOf.1 hσ) _ ⟨x, rfl⟩
    obtain ⟨τ, hτ⟩ := exists_decRes_eq σ hσ'
    have e1 : (r (σ : _root_.Formalism.ConjugateSelfDual.G K Ω)) = ((resTo L r).comp (_root_.ReciprocityTheory.Gal.Dec (F := L) A).subtype) τ := by
      rw [← hτ]; rfl
    rw [e1, ← hm']
    exact ((r' τ : GL (Fin a) ↥LL'.1) : Matrix (Fin a) (Fin a) ↥LL'.1) i k |>.2
  have hent : ∀ (g : ↥(_root_.ReciprocityTheory.Gal.Dec (F := K) A)) i k,
      (((r.comp (_root_.ReciprocityTheory.Gal.Dec (F := K) A).subtype) g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k ∈ T.1 := by
    intro g i k
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
    have hg : g = (QuotientGroup.mk g : ↥(_root_.ReciprocityTheory.Gal.Dec (F := K) A) ⧸ H).out * ((h⁻¹ : H) : ↥(_root_.ReciprocityTheory.Gal.Dec (F := K) A)) := by
      rw [hh, Subgroup.coe_inv, mul_inv_cancel_right]
    rw [MonoidHom.comp_apply, hg, map_mul, map_mul, Units.val_mul, Matrix.mul_apply]
    refine sum_mem fun m _ => mul_mem (hET (IntermediateField.subset_adjoin _ _ ⟨⟨_, i, m⟩, rfl⟩)) ?_
    exact hLT (hfix _ (h⁻¹).2 m k)
  obtain ⟨r₁, hr₁⟩ := exists_model_of_mem T _ hent
  exact ⟨T, r₁, hBT, hr₁⟩

end GlobalTheory.AboveLRes

namespace GlobalTheory.AboveLRes


open GlobalTheory.AboveL in
theorem isPstAt_of_resTo : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (a : ℕ) (r : _root_.Formalism.ConjugateSelfDual.G K Ω →* GL (Fin a) (Om l)), Continuous r → ∀ (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw : LocBridge l K Ω (_root_.ReciprocityTheory.Gal.Dec (F := K) A) O) (Bw' : LocBridge l L Ω (_root_.ReciprocityTheory.Gal.Dec (F := L) A) O'), GlobalTheory.Pst.Induces Bw → GlobalTheory.Pst.Induces Bw' → IsPstAt P Bw' ((GlobalTheory.AboveL.resTo L r).comp (_root_.ReciprocityTheory.Gal.Dec (F := L) A).subtype) → IsPstAt P Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := K) A).subtype) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A l _ P AI hT a r hr O O' _ _ _ _ _ _ Bw Bw' hj hj' hL
  have hcL : Continuous fun g : ↥(_root_.ReciprocityTheory.Gal.Dec (F := L) A) =>
      ((((resTo L r).comp (_root_.ReciprocityTheory.Gal.Dec (F := L) A).subtype) g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) :=
    Units.continuous_val.comp ((hr.comp (UpperTheory.V.Af.continuous_restrictScalarsHom K L Ω)).comp continuous_subtype_val)
  obtain ⟨LL', r', hm', hV'⟩ := hL
  obtain ⟨T, r₁, hBT, hr₁⟩ := exists_model_dec A r LL' Bw.LL r' hm'.2

  obtain ⟨S'', Bw'', hjj, hTS, hle⟩ := exists_bridge (L := L) Bw hj T
  have hj'' : GlobalTheory.Pst.Induces Bw'' := fun x => by rw [hjj]; exact hj x
  obtain ⟨LL₃, r₃, hm₃, hV₃⟩ := GlobalTheory.Pst.PstBridge.isPstAt_indep_bridge l P AI hT L Ω A O' _ Bw' Bw'' hj' hj'' a _
    hcL ⟨LL', r', hm', hV'⟩
  have h1 : Bw''.LL.1 ≤ (supExt Bw''.LL LL₃).1 := le_sup_left
  have h3 : LL₃.1 ≤ (supExt Bw''.LL LL₃).1 := le_sup_right
  have hTT : T.1 ≤ (supExt Bw''.LL LL₃).1 := hTS.trans h1
  have hr₁' : mapRep (algebraMap ↥(supExt Bw''.LL LL₃).1 (Om l))
      (mapRep (IntermediateField.inclusion hTT).toRingHom r₁) = r.comp (_root_.ReciprocityTheory.Gal.Dec (F := K) A).subtype := by
    ext g i k
    exact congrArg (fun f : ↥(_root_.ReciprocityTheory.Gal.Dec (F := K) A) →* GL (Fin a) (Om l) =>
      ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hr₁
  have hmL : IsModel Bw'' ((resTo L r).comp (_root_.ReciprocityTheory.Gal.Dec (F := L) A).subtype) (supExt Bw''.LL LL₃)
      ((mapRep (IntermediateField.inclusion hTT).toRingHom r₁).comp (decRes A)) := by
    refine ⟨h1, ?_⟩
    ext g i k
    exact congrArg (fun f : ↥(_root_.ReciprocityTheory.Gal.Dec (F := K) A) →* GL (Fin a) (Om l) =>
      ((f (decRes A g) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hr₁'
  have hm₃' : IsModel Bw'' ((resTo L r).comp (_root_.ReciprocityTheory.Gal.Dec (F := L) A).subtype) (supExt Bw''.LL LL₃)
      (mapRep (IntermediateField.inclusion h3).toRingHom r₃) := by
    refine ⟨hm₃.1.trans h3, ?_⟩
    ext g i k
    exact congrArg (fun f : ↥(_root_.ReciprocityTheory.Gal.Dec (F := L) A) →* GL (Fin a) (Om l) =>
      ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hm₃.2
  have heq := IsModel.unique Bw'' _ hm₃' hmL
  have hp := GlobalTheory.PstExt.isPst_enlarge P Bw'' h3 r₃ hV₃
  rw [heq, repE_decRes Bw Bw'' hjj hle] at hp
  exact ⟨_, _, ⟨hBT.trans hTT, hr₁'⟩, (GlobalTheory.PstLaws.isPst_resTo_iff P _ hle).1 hp⟩

end GlobalTheory.AboveLRes
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Classical

theorem _root_.GlobalTheory.T.jetIntegralityBis_ofKer_of_hyp : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.Hyp → 3 ≤ D.host.splitBound → ∀ ep be sg, OrbitPlaces.JetIntegralityBis (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be sg) Y := by
  first | exact @GlobalTheory.Ggeo.AdmEntInt.kernelDatum_entries_integral_away_from_d | exact GlobalTheory.Ggeo.AdmEntInt.kernelDatum_entries_integral_away_from_d | (intros; apply GlobalTheory.Ggeo.AdmEntInt.kernelDatum_entries_integral_away_from_d <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Classical

namespace GlobalTheory.Ggeo.KerShapeD

theorem thetaKernelShapeAtD_ofKer_of_hyp_adapted : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D)
    (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.Hyp → t.Adapted →
    ∀ ep be sg, OrbitPlaces.ThetaKernelShapeAtD (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be sg) Y := by
  intro hIn D L hT Gi Gl K Y cX ex t hH hA ep be sg
  intro u μ w hlev hcls i hi c c'
  have hpd : D.what₂.places.resChar w = D.host.d := by
    have h := hcls
    simp only [Host.cls, primeClass] at h
    split_ifs at h with h1 h2 h3 <;> first | exact h3 | cases h
  have hAd : AdPl D w := Or.inr (Or.inr hcls)
  have hlev' : LevFree Y u μ w := hlev
  obtain ⟨Pm, hBas, -, hConj, hTh⟩ := hA w hAd u μ hlev'
  have hStd : ∀ j, j ≤ D.R.m → ∀ cl, GlobalTheory.KerStd.StdBases D (t.ent.lam w) ((t.O u μ).lat j cl).1 (Pm j cl) :=
    fun j hj cl => GlobalTheory.T.isStandardBasesLatticeAtPlace_of_adapted_bases D _ (t.ent.lam w) _ _ _ ((t.O u μ).lat j cl).2.1 (fun τ => hBas j hj cl τ)
      (fun τ τ' h => hConj j hj cl τ τ' h)
  have hcomb := GlobalTheory.Ggeo.KerComb.comb_of_tied hIn.algT D L hT Gi Gl K Y cX ex t hH u μ w hlev' i hi c c'
  have hdg : IsDgen D t.cD := by
    rw [← t.O_dgen u μ]
    exact (t.O u μ).dgen_gen
  have hnorm : ∀ τ, ‖(fun _ => (1 : ℂ_[D.what₂.places.resChar w])) τ‖ ≤ ‖TaylorLogMetric.lamC (t.ent.lam w) (t.cD τ)‖ := by
    intro τ
    rw [GlobalTheory.EigenGenerator.norm_dgen_eq_one D t.cD hdg _ (t.ent.lam w) hpd τ]
    simp
  show OrbitPlaces.ShapeD D _ (t.ent.Th u μ w i c c')
  rw [hTh i hi c c', GlobalTheory.atLin_adCoef_eq_stdSer]
  exact GlobalTheory.T.shape_normalisedThetaCombinations_dualBases_at_d hIn D t.cc t.δ t.cc_ok t.δ_ok t.B t.χ t.χ_ok t.X t.seam t.seam_ok _ _ _ _ hcomb.1 _ (t.ent.lam w) hpd
    t.cD hdg (Pm i c) (Pm (i + 1) c') _ (hStd i hi.le c) (hStd (i + 1) hi c') hnorm _ hcomb.2

end GlobalTheory.Ggeo.KerShapeD
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.matchE_of_chainStep_matches : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Chain.LiftInteg D → Core R F → SchurAll R → ∀ t P, Good R t P → FixAll R t P → ∀ (cX : List ℤ →₀ ℂ) (cs : ℕ → List ℤ →₀ ℂ), Match R.ψ (R.ωX t) P (cs (D.R.m - 1)) (dualC cX) → (∀ k, k + 1 < D.R.m → Match R.ψ (R.ωY t k) P (cs k) (dualC (cs (k + 1)))) → MatchE R t P cX (cs 0) := by
  first | exact @GlobalTheory.Hk3.ChainE.matchE_of_chain | exact GlobalTheory.Hk3.ChainE.matchE_of_chain | (intros; apply GlobalTheory.Hk3.ChainE.matchE_of_chain <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.theta_intertwines_matched_operators : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ SF, IsSF R SF → ∀ i t P, Good R t P → ∀ cV cW, MatchW R i t P cV cW → ∀ hV, IsOpsV R i t hV → (∀ h, IsOpsW R i h → ∀ y, R.thG i t (hV P cV y) = h P cW (R.thG i t y)) ∧ ∀ c, ∀ w ∈ Wcc R SF i c, hV P cV (LinearMap.adjoint (R.thG i t) w) = evC (Wc D i) P (c P) cW • LinearMap.adjoint (R.thG i t) w := by
  first | exact @GlobalTheory.SysW.matched_operators_theta_intertwine | exact GlobalTheory.SysW.matched_operators_theta_intertwine | (intros; apply GlobalTheory.SysW.matched_operators_theta_intertwine <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.sphericalHecke_scalarLabel_comp_eq_shiftDown_split : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), _root_.Formalism.DivisionValues.conjPl P ≠ P → ∀ (d : List ℤ) (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π P (Finsupp.single (splitLab V.rank V.rank) 1) (opOf π P (Finsupp.single d 1) u) = opOf π P (Finsupp.single (d.map fun x => x - 1) 1) u := by
  first | exact @GlobalTheory.CentralShift.central_shift | exact GlobalTheory.CentralShift.central_shift | (intros; apply GlobalTheory.CentralShift.central_shift <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_baseLevel_vector_in_goodAlgebraicForms_span : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → ∀ j c, R.Wc' j c ≠ ⊥ → ∃ w ∈ R.Wc' j c, w ≠ 0 ∧ w ∈ R.toRealDat.WS F.lv2 false j (sg0 D A3.A) := by
  first | exact @GlobalTheory.Hk3.exists_part_level_vector | exact GlobalTheory.Hk3.exists_part_level_vector | (intros; apply GlobalTheory.Hk3.exists_part_level_vector <;> assumption)
end
