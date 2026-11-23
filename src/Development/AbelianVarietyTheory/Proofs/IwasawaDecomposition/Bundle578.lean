module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle567
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueCharacterArtinTameGaloisEqTameValue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle188
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameValuesGaloisCharFormResidueUnitCharacter
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Algebraic.Defs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle569
import Formalism.LocalRingCardinality.DataHost
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCharDescent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.PtEquivApply
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.LevCmp

theorem exists_finset_eval_eq_zero {X K W : Type} [Field K] [AddCommGroup W] [Module K W]
    (V : Submodule K (X → W)) [FiniteDimensional K V] :
    ∃ P : Finset X, ∀ f ∈ V, (∀ x ∈ P, f x = 0) → f = 0 := by
  classical
  let N : Finset X → Submodule K V := fun P =>
    ⨅ x ∈ P, LinearMap.ker ((LinearMap.proj (R := K) (φ := fun _ : X => W) x).comp V.subtype)
  have hN : ∀ P (f : V), f ∈ N P ↔ ∀ x ∈ P, (f : X → W) x = 0 := by
    intro P f; simp [N, Submodule.mem_iInf]
  obtain ⟨_, ⟨P, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule K V)).has_min (Set.range N) ⟨_, ⟨∅, rfl⟩⟩
  refine ⟨P, fun f hf h0 => ?_⟩
  have key : ∀ x, N P ≤ N (insert x P) := by
    intro x
    have hle : N (insert x P) ≤ N P := fun g hg =>
      (hN _ _).2 fun y hy => (hN _ _).1 hg y (Finset.mem_insert_of_mem hy)
    by_contra hne
    exact hmin _ ⟨_, rfl⟩ (lt_of_le_of_ne hle fun h => hne h.ge)
  funext x
  exact (hN _ _).1 (key x ((hN P ⟨f, hf⟩).2 h0)) x (Finset.mem_insert_self x P)

section Omega
variable {K W W' ι : Type} [Field K] [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module ℂ W']
  [Fintype ι] [DecidableEq ι]

def coordCx (e : K →+* ℂ) (b : Module.Basis ι K W) (b' : Module.Basis ι ℂ W') : W →ₛₗ[e] W' where
  toFun w := b'.equivFun.symm fun i => e (b.equivFun w i)
  map_add' x y := b'.equivFun.injective (by
    simp only [map_add (f := _), LinearEquiv.apply_symm_apply]; funext i; simp only [Pi.add_apply, map_add (f := _)])
  map_smul' a x := b'.equivFun.injective (by
    simp only [map_smul, LinearEquiv.apply_symm_apply]; funext i; simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply])

theorem coordCx_coord (e : K →+* ℂ) (b : Module.Basis ι K W) (b' : Module.Basis ι ℂ W') (w : W) (i : ι) :
    b'.equivFun (coordCx e b b' w) i = e (b.equivFun w i) := by
  simp only [coordCx, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply]

end Omega

theorem finrank_typeSp_cx : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] (e : K →+* ℂ) (W W' : Type) [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation K (GQ L n) W) (ρ' : Representation ℂ (GQ L n) W') (J : Subgroup (GAf L n)) (χ : J →* Kˣ), WtMatch e ρ ρ' → (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → FiniteDimensional K (NX.TypeSpF L n K ρ J χ) → Module.finrank ℂ (NG.TypeSp ρ' J (cx e χ)) = Module.finrank K (NX.TypeSpF L n K ρ J χ) := by
  intro L _ _ _ n K _ e W W' _ _ _ _ ρ ρ' J χ hW hN hfin
  classical
  obtain ⟨ι, _, _, b, b', hM⟩ := hW
  letI : Algebra K ℂ := e.toAlgebra
  let β := Module.Basis.ofVectorSpace K ℂ
  let ω := coordCx e b b'
  have hωc : ∀ w i, b'.equivFun (ω w) i = e (b.equivFun w i) := fun w i => coordCx_coord e b b' w i
  have hρ : ∀ γ w i, b.equivFun (ρ γ w) i = ∑ k, LinearMap.toMatrix b b (ρ γ) i k * b.equivFun w k := by
    intro γ w i
    have := congrFun (LinearMap.toMatrix_mulVec_repr b b (ρ γ) w) i
    simp only [Module.Basis.equivFun_apply]; rw [← this]; rfl
  have hρ' : ∀ γ w i, b'.equivFun (ρ' γ w) i = ∑ k, e (LinearMap.toMatrix b b (ρ γ) i k) * b'.equivFun w k := by
    intro γ w i
    have := congrFun (LinearMap.toMatrix_mulVec_repr b' b' (ρ' γ) w) i
    rw [hM γ] at this
    simp only [Module.Basis.equivFun_apply]; rw [← this]; rfl
  have hωρ : ∀ γ w, ω (ρ γ w) = ρ' γ (ω w) := fun γ w =>
    b'.equivFun.injective (funext fun i => by rw [hωc, hρ, hρ', map_sum]; simp only [map_mul, hωc])
  have hβ1 : ∀ (y : K) (z : ℂ) α, β.repr (e y * z) α = y * β.repr z α := by
    intro y z α
    rw [show e y * z = y • z from rfl, map_smul, Finsupp.smul_apply, smul_eq_mul]
  let V := NX.TypeSpF L n K ρ J χ
  let v := Module.finBasis K V
  have hωV : ∀ f ∈ V, (fun g => ω (f g)) ∈ NG.TypeSp ρ' J (cx e χ) := by
    rintro f ⟨h1, h2⟩
    obtain ⟨N, hN0, hNc⟩ := hN
    refine ⟨⟨fun γ g => by simp only [h1, hωρ], N, hN0, fun κ hκ g => ?_⟩, fun κ => ?_⟩
    · obtain ⟨h, h1'⟩ := hNc κ hκ
      show ω (f (g * κ)) = ω (f g)
      have := h2 ⟨κ, h⟩ g
      rw [this, h1', Units.val_one, one_smul]
    · funext g
      show ω (f (g * κ)) = ((cx e χ κ : ℂˣ) : ℂ) • ω (f g)
      rw [h2, map_smulₛₗ, cx_apply]

  have hlinK : LinearIndependent K (fun j => ((v j : V) : GAf L n → W)) :=
    v.linearIndependent.map' V.subtype V.ker_subtype
  have hli : LinearIndependent ℂ (fun j => fun g => ω (((v j : V) : GAf L n → W) g)) := by
    rw [Fintype.linearIndependent_iff] at hlinK ⊢
    intro c hc j
    have hcoord : ∀ g i, ∑ j, c j * e (b.equivFun (((v j : V) : GAf L n → W) g) i) = 0 := by
      intro g i
      have := congrArg (fun F => b'.equivFun (F g) i) hc

      simpa only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, Pi.smul_apply, smul_eq_mul, hωc,
      Pi.zero_apply, map_zero] using this
    have hα : ∀ α, ∀ j, β.repr (c j) α = 0 := by
      intro α
      apply hlinK
      funext g
      apply b.equivFun.injective
      funext i
      have := congrArg (fun z => β.repr z α) (hcoord g i)

      simp only [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, mul_comm (c _), hβ1, map_zero,
      Finsupp.coe_zero, Pi.zero_apply] at this

      simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, smul_eq_mul, map_zero, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    exact β.repr.injective (by ext α; simp [hα α j])

  have hspanV : ∀ a : Fin (Module.finrank K V) → K,
      (fun g => ω ((∑ j, a j • ((v j : V) : GAf L n → W)) g)) ∈
        Submodule.span ℂ (Set.range fun j => fun g => ω (((v j : V) : GAf L n → W) g)) := by
    intro a
    have : (fun g => ω ((∑ j, a j • ((v j : V) : GAf L n → W)) g)) =
        ∑ j, e (a j) • fun g => ω (((v j : V) : GAf L n → W) g) := by
      funext g

      simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smulₛₗ]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hspan : NG.TypeSp ρ' J (cx e χ) = Submodule.span ℂ (Set.range fun j => fun g => ω (((v j : V) : GAf L n → W) g)) := by
    refine le_antisymm ?_ (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hωV _ (v j).2))
    rintro F ⟨⟨hF1, -⟩, hF2⟩
    have hFk : ∀ (κ : J) g, F (g * κ) = e (χ κ) • F g := fun κ g => congrFun (hF2 κ) g
    let fa : _ → GAf L n → W := fun α g => b.equivFun.symm fun i => β.repr (b'.equivFun (F g) i) α
    have hfa : ∀ α g i, b.equivFun (fa α g) i = β.repr (b'.equivFun (F g) i) α := by
      intro α g i; simp only [fa, LinearEquiv.apply_symm_apply]
    have hfaV : ∀ α, fa α ∈ V := by
      intro α
      refine ⟨fun γ g => b.equivFun.injective (funext fun i => ?_), fun κ g => b.equivFun.injective (funext fun i => ?_)⟩

      · rw [hfa, hF1, hρ', hρ, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
        simp only [hβ1, hfa]
      · rw [hfa, hFk]
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, hβ1, hfa]
    obtain ⟨P, hP⟩ := exists_finset_eval_eq_zero V
    let S := P.biUnion fun g => Finset.univ.biUnion fun i => (β.repr (b'.equivFun (F g) i)).support
    have hzero : ∀ α ∉ S, fa α = 0 := by
      intro α hα
      refine hP _ (hfaV α) fun g hg => b.equivFun.injective (funext fun i => ?_)
      rw [hfa, map_zero, Pi.zero_apply]
      by_contra h
      exact hα (Finset.mem_biUnion.2 ⟨g, hg, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finsupp.mem_support_iff.2 h⟩⟩)
    have hsub : ∀ g i, (β.repr (b'.equivFun (F g) i)).support ⊆ S := by
      intro g i α hα
      by_contra hS
      have := congrArg (fun f => b.equivFun (f g) i) (hzero α hS)
      simp only [hfa, Pi.zero_apply, map_zero] at this
      exact (Finsupp.mem_support_iff.1 hα) this
    have hFeq : F = ∑ α ∈ S, β α • fun g => ω (fa α g) := by
      funext g
      apply b'.equivFun.injective
      funext i

      simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, smul_eq_mul, hωc, hfa]
      conv_lhs => rw [← β.linearCombination_repr (b'.equivFun (F g) i)]
      rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ (hsub g i) (fun a c => c • β a) (fun _ _ => zero_smul _ _)]
      exact Finset.sum_congr rfl fun α _ => mul_comm _ _
    rw [hFeq]
    refine Submodule.sum_mem _ fun α _ => Submodule.smul_mem _ _ ?_
    have hrep := congrArg Subtype.val (v.sum_repr ⟨fa α, hfaV α⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hrep
    rw [← hrep]
    exact hspanV _
  rw [hspan, finrank_span_eq_card hli, Fintype.card_fin]

end GlobalTheory.LevCmp

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

open Formalism.L2.DIV GlobalTheory.CoefModel

namespace GlobalTheory.BcMatch

theorem bcmatch_main : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K K' : Type} [Field K] [Field K'] (f : K →+* K') (e : K' →+* ℂ) {W₀ W W' : Type} [AddCommGroup W₀] [Module K W₀] [AddCommGroup W] [Module K' W] [AddCommGroup W'] [Module ℂ W'] (ρ₀ : Representation K (GQ L n) W₀) (ρ : Representation K' (GQ L n) W) (ρ' : Representation ℂ (GQ L n) W'), (∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b₀ : Module.Basis ι K W₀) (b₁ : Module.Basis ι K' W), ∀ γ, LinearMap.toMatrix b₁ b₁ (ρ γ) = (LinearMap.toMatrix b₀ b₀ (ρ₀ γ)).map f) → GlobalTheory.LevCmp.WtMatch (e.comp f) ρ₀ ρ' → GlobalTheory.LevCmp.WtMatch e ρ ρ' := by
  intro L _ _ _ n K K' _ _ f e W₀ W W' _ _ _ _ _ _ ρ₀ ρ ρ' hb hm
  obtain ⟨ι, _, _, b₀, b₁, hb⟩ := hb
  obtain ⟨κ, _, _, c₀, c', hc⟩ := hm
  set P : Matrix ι κ K := b₀.toMatrix c₀ with hP
  set Q : Matrix κ ι K := c₀.toMatrix b₀ with hQ
  have hPQ : P * Q = 1 := Module.Basis.toMatrix_mul_toMatrix_flip b₀ c₀
  have hQP : Q * P = 1 := Module.Basis.toMatrix_mul_toMatrix_flip c₀ b₀
  have hPQf : P.map f * Q.map f = 1 := by rw [← Matrix.map_mul, hPQ, Matrix.map_one _ f.map_zero f.map_one]
  have hQPf : Q.map f * P.map f = 1 := by rw [← Matrix.map_mul, hQP, Matrix.map_one _ f.map_zero f.map_one]
  let std := Pi.basisFun K' κ
  let E : (κ → K') ≃ₗ[K'] W := LinearEquiv.ofLinear (Matrix.toLin std b₁ (P.map f)) (Matrix.toLin b₁ std (Q.map f))
    (by rw [← Matrix.toLin_mul, hPQf, Matrix.toLin_one])
    (by rw [← Matrix.toLin_mul, hQPf, Matrix.toLin_one])
  let d : Module.Basis κ K' W := std.map E
  have hd1 : b₁.toMatrix d = P.map f := by
    ext i j
    rw [Module.Basis.toMatrix_apply]
    have : d j = ∑ k, (P.map f) k j • b₁ k := by
      show E (std j) = _
      exact Matrix.toLin_self _ _ _ _
    rw [this, Module.Basis.repr_sum_self]
  have hd2 : d.toMatrix b₁ = Q.map f := by
    ext j i
    rw [Module.Basis.toMatrix_apply]
    simp [d, E, std, Matrix.toLin_self, Pi.single_apply]
  refine ⟨κ, inferInstance, inferInstance, d, c', fun γ => ?_⟩
  rw [hc γ, ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix d b₁ d b₁ (ρ γ), hd1, hd2, hb γ,
    ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix c₀ b₀ c₀ b₀ (ρ₀ γ), ← hP, ← hQ]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_map, Matrix.map_map, Matrix.map_map]
  rfl

end GlobalTheory.BcMatch
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.LevCmp

section Glue

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def compHom (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    GAf L n →* GL (Fin n) (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :=
  (Matrix.GeneralLinearGroup.map (compAt L v)).comp (ReciprocityTheory.Aut.GA L n).subtype

theorem compHom_eq_one_iff (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x : GAf L n) :
    compHom v x = 1 ↔ (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = 1 := by
  constructor
  · intro h
    have := congrArg Units.val h
    simpa [compHom] using this
  · intro h
    ext i j
    have := congrFun (congrFun h i) j
    simpa [compHom] using this

theorem compHom_eq_iff (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x y : GAf L n) :
    compHom v x = compHom v y ↔
      (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = (y.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) := by
  constructor
  · intro h
    have := congrArg Units.val h
    simpa [compHom] using this
  · intro h
    ext i j
    have := congrFun (congrFun h i) j
    simpa [compHom] using this

theorem mem_of_agree {J J' : Subgroup (GAf L n)} {χ : J →* ℂˣ} {χ' : J' →* ℂˣ}
    {S : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} (hS : S.Finite) (hJ : NG.IsProdLevel J)
    (hO : NG.HypOutside J χ S) (hO' : NG.HypOutside J' χ' S)
    (hloc : ∀ u ∈ S, ∀ κ, TrivOutside {u} κ → (κ ∈ J ↔ κ ∈ J') ∧ ∀ (h : κ ∈ J) (h' : κ ∈ J'), χ ⟨κ, h⟩ = χ' ⟨κ, h'⟩)
    (κ : GAf L n) (hκ : κ ∈ J) : ∃ h' : κ ∈ J', χ ⟨κ, hκ⟩ = χ' ⟨κ, h'⟩ := by

  have hone : ∀ u κ, TrivOutside {u} κ → ∀ hκ : κ ∈ J, ∃ h' : κ ∈ J', χ ⟨κ, hκ⟩ = χ' ⟨κ, h'⟩ := by
    intro u κ hu hκ
    by_cases huS : u ∈ S
    · obtain ⟨h1, h2⟩ := hloc u huS κ hu
      exact ⟨h1.mp hκ, h2 hκ (h1.mp hκ)⟩
    · have ht : TrivOutside Sᶜ κ := by
        intro v hv
        apply hu v
        rintro rfl
        exact huS (not_not.mp hv)
      obtain ⟨a1, a2⟩ := hO κ ht
      obtain ⟨b1, b2⟩ := hO' κ ht
      have h' : κ ∈ J' := b1.mpr (a1.mp hκ)
      exact ⟨h', by rw [a2 hκ, b2 h']⟩
  have key : ∀ T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L))), ∀ κ (hκ : κ ∈ J),
      TrivOutside (Sᶜ ∪ (T : Set _)) κ → ∃ h' : κ ∈ J', χ ⟨κ, hκ⟩ = χ' ⟨κ, h'⟩ := by
    intro T
    classical
    induction T using Finset.induction_on with
    | empty =>
      intro κ hκ ht
      have ht' : TrivOutside Sᶜ κ := by
        intro v hv
        exact ht v (by simpa using hv)
      obtain ⟨a1, a2⟩ := hO κ ht'
      obtain ⟨b1, b2⟩ := hO' κ ht'
      have h' : κ ∈ J' := b1.mpr (a1.mp hκ)
      exact ⟨h', by rw [a2 hκ, b2 h']⟩
    | insert u T huT ih =>
      intro κ hκ ht
      obtain ⟨κu, hκu, hu, hcomp⟩ := hJ κ hκ u
      have hκ1 : κ * κu⁻¹ ∈ J := J.mul_mem hκ (J.inv_mem hκu)
      have ht1 : TrivOutside (Sᶜ ∪ (T : Set _)) (κ * κu⁻¹) := by
        intro v hv
        rw [← compHom_eq_one_iff, map_mul, map_inv, mul_inv_eq_one]
        by_cases hvu : v = u
        · subst hvu
          exact ((compHom_eq_iff v κ κu).mpr hcomp.symm)
        · have e1 : compHom v κ = 1 := by
            rw [compHom_eq_one_iff]
            apply ht v
            simp only [Finset.coe_insert, Set.mem_union, Set.mem_insert_iff, not_or] at hv ⊢
            exact ⟨hv.1, hvu, hv.2⟩
          have e2 : compHom v κu = 1 := by
            rw [compHom_eq_one_iff]
            exact hu v (by simpa using hvu)
          rw [e1, e2]
      obtain ⟨h1', e1⟩ := ih (κ * κu⁻¹) hκ1 ht1
      obtain ⟨h2', e2⟩ := hone u κu hu hκu
      have hprod : κ = κ * κu⁻¹ * κu := by group
      have h' : κ ∈ J' := by
        rw [hprod]; exact J'.mul_mem h1' h2'
      refine ⟨h', ?_⟩
      have s1 : (⟨κ, hκ⟩ : J) = ⟨κ * κu⁻¹, hκ1⟩ * ⟨κu, hκu⟩ := Subtype.ext hprod
      have s2 : (⟨κ, h'⟩ : J') = ⟨κ * κu⁻¹, h1'⟩ * ⟨κu, h2'⟩ := Subtype.ext hprod
      rw [s1, s2, map_mul, map_mul, e1, e2]
  apply key hS.toFinset κ hκ
  intro v hv
  exfalso
  apply hv
  by_cases h : v ∈ S
  · right; simpa using h
  · left; exact h

theorem levEq_of_agree : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J J' : Subgroup (GAf L n)) (χ : J →* ℂˣ) (χ' : J' →* ℂˣ) (S : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))), S.Finite → NG.IsProdLevel J → NG.IsProdLevel J' → NG.HypOutside J χ S → NG.HypOutside J' χ' S → (∀ u ∈ S, ∀ κ, TrivOutside {u} κ → (κ ∈ J ↔ κ ∈ J') ∧ ∀ (h : κ ∈ J) (h' : κ ∈ J'), χ ⟨κ, h⟩ = χ' ⟨κ, h'⟩) → LevEq J χ J' χ' := by
  intro L _ _ _ n J J' χ χ' S hS hJ hJ' hO hO' hloc
  have hloc' : ∀ u ∈ S, ∀ κ, TrivOutside {u} κ → (κ ∈ J' ↔ κ ∈ J) ∧ ∀ (h : κ ∈ J') (h' : κ ∈ J), χ' ⟨κ, h⟩ = χ ⟨κ, h'⟩ :=
    fun u hu κ hκ => ⟨(hloc u hu κ hκ).1.symm, fun h h' => ((hloc u hu κ hκ).2 h' h).symm⟩
  refine ⟨le_antisymm (fun κ hκ => (mem_of_agree hS hJ hO hO' hloc κ hκ).1)
    (fun κ hκ => (mem_of_agree hS hJ' hO' hO hloc' κ hκ).1), fun κ h h' => ?_⟩
  obtain ⟨h'', e⟩ := mem_of_agree hS hJ hO hO' hloc κ h
  exact e

end Glue

end GlobalTheory.LevCmp

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp.ValQ

theorem tameVal_eq_locK (hGAR : GlobalTheory.Published.GlobalArtinReciprocity) (D : D7) (i : D.ntw.Tw) (k : ℕ)
    (e : NX.Kk D i k →+* ℂ) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (χ : HChar D.host.E)
    (hR : ReadsHecke e ψ χ) (hopen : IsOpen (ψ.ker : Set (G D.host.E D.nd.Om)))
    (hord : ∀ σ, ∃ N : ℕ, ψ σ ^ (D.ntw.l i ^ N) = 1) (P' : PlE D.host)
    (hl : ((D.ntw.l i : ℕ) : 𝓞 D.host.E) ∉ P'.asIdeal) (a : 𝓞 D.host.E) (y : D.host.Eˣ)
    (ha : a ∉ P'.asIdeal) (hy : (y : D.host.E) = (a : D.host.E)) :
    e (NX.ofOk D i k (NX.tameVal ψ P' 1 a).1) = ((χ.locK P' y : ℂˣ) : ℂ) := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  obtain ⟨art, hart, hH⟩ := hR
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver D.nd.Om P'
  obtain ⟨hq2, hq1⟩ := GlobalTheory.TameValChar.two_le_normV_and_not_mem P'
  obtain ⟨ϖ, hϖ1, hϖ2⟩ : ∃ ϖ0 : 𝓞 D.host.E, ϖ0 ∈ P'.asIdeal ∧ ϖ0 ∉ P'.asIdeal ^ 2 := by
    have hlt := Ideal.pow_succ_lt_pow (P := P'.asIdeal) P'.ne_bot 1
    rw [pow_one] at hlt
    obtain ⟨x, hx, hx'⟩ := SetLike.exists_of_lt hlt
    exact ⟨x, hx, hx'⟩
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap D.host.E D.nd.Om (ϖ : D.host.E))
    (show 0 < normV P' - 1 by omega)
  have hxu : IsUnitAt P' (atFin P' y) := by
    show Valued.v (((y : D.host.E) : P'.adicCompletion D.host.E)) = 1
    rw [hy, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem _).2 ha
  obtain ⟨σ, hσI, hσart, hσval⟩ := GlobalTheory.TameRecip.exists_ine_of_unit hGAR D.host.E D.nd.Om art hart
    P' A hA ϖ hϖ1 hϖ2 π hπ (atFin P' y) a hxu (by simp [atFin, hy])
  have hTR : NX.TameRep P' 1 σ a := ⟨A, hA, hσI, ϖ, π, hϖ1, hϖ2, hπ, by simpa using hσval⟩
  have hI : ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P' → ∀ σ ∈ Ine (F := D.host.E) A,
      ∃ N : ℕ, ψ σ ^ (D.ntw.l i ^ N) = 1 := fun _ _ σ _ => hord σ
  rw [GlobalTheory.TameResRead.tameVal_eq_of_tameRep ψ P' 1 (D.ntw.l i) hopen hl hI σ a ha hTR]
  have h1 := hH _ σ hσart.symm
  exact (congrArg (fun z : ℂˣ => (z : ℂ)) h1).symm

end GlobalTheory.LevCmp.ValQ
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finiteDimensional_subfield_complex_finitelyGenerated : ∀ (M : IntermediateField ℚ ℂ), FiniteDimensional ℚ M → ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ Lf : IntermediateField ℚ ℂ, (↑S : Set ℂ) ⊆ Lf → M ≤ Lf := by
  first | exact @GlobalTheory.finDimSubfield_finGen | exact GlobalTheory.finDimSubfield_finGen | (intros; apply GlobalTheory.finDimSubfield_finGen <;> assumption)
end
