module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle005
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PlainAtR
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.PromodularityCaseThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.Bundle001
public import Mathlib.Data.Rat.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle065
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.OverOf4
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.LocTrans
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycCOfCyclic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat

@[expose] public section

section

open UpperTheory.GalN.V UpperTheory.V.Z.Win.Birth

open NumberField IsDedekindDomain
open Neutral.B1 hiding IsPlaceOver
open Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd UpperTheory.V.Ws UpperTheory.V.Z.Bc UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

private theorem deg_two {Ω : Type} [Field Ω] [CharZero Ω] (A B M : IntermediateField ℚ Ω) [FiniteDimensional ℚ A]
    [FiniteDimensional ℚ B] (hM : M = A ⊔ B) (hA : Module.finrank ℚ A = 2) (hn : ¬ A ≤ B) [Algebra B M] [IsScalarTower ℚ B M] :
    Module.finrank B M = 2 := by
  have h1 : Module.finrank ℚ M ≤ Module.finrank ℚ A * Module.finrank ℚ B := hM ▸ IntermediateField.finrank_sup_le A B
  haveI : FiniteDimensional ℚ M := hM ▸ IntermediateField.finiteDimensional_sup A B
  haveI : Module.Free B M := Module.Free.of_divisionRing B M
  have h2 := Module.finrank_mul_finrank ℚ B M
  have h3 : 0 < Module.finrank ℚ B := Module.finrank_pos
  have h4 : 0 < Module.finrank ℚ M := Module.finrank_pos
  have h5 : Module.finrank ℚ B ≠ Module.finrank ℚ M := fun e =>
    hn (IntermediateField.eq_of_le_of_finrank_eq (hM ▸ le_sup_right : B ≤ M) e ▸ (hM ▸ le_sup_left : A ≤ M))
  generalize Module.finrank B M = n at h2 ⊢
  rw [hA, ← h2, mul_comm 2] at h1
  have h6 := Nat.le_of_mul_le_mul_left h1 h3
  rw [← h2] at h4 h5
  interval_cases n <;> simp_all

private theorem two_places {k : Type} [Field k] [NumberField k] [IsTotallyReal k] (h : Module.finrank ℚ k = 2)
    {v v' : InfinitePlace k} (hv : v ≠ v') (w : InfinitePlace k) : w = v ∨ w = v' := by
  classical
  by_contra hw
  push Not at hw
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank k
  have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces k
  have h3 : ({w, v, v'} : Finset (InfinitePlace k)).card = 3 := Finset.card_eq_three.2 ⟨w, v, v', hw.1, hw.2, hv, rfl⟩
  have h4 := Finset.card_le_univ ({w, v, v'} : Finset (InfinitePlace k))
  omega

private theorem two_emb {L M : Type} [Field L] [Field M] [CharZero L] [Algebra L M] (h : Module.finrank L M = 2) (φ : L →+* ℂ) :
    ∃ τ τ' : M →+* ℂ, τ ≠ τ' ∧ τ.comp (algebraMap L M) = φ ∧ τ'.comp (algebraMap L M) = φ := by
  letI : Algebra L ℂ := φ.toAlgebra
  letI : Module.Free L M := Module.Free.of_divisionRing L M
  letI : FiniteDimensional L M := Module.finite_of_finrank_pos (by omega)
  letI : Algebra.IsSeparable L M := ⟨fun x => (minpoly.irreducible (IsIntegral.of_finite L x)).separable⟩
  have hc := AlgHom.card L M ℂ
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (α := M →ₐ[L] ℂ) (by omega)
  exact ⟨a, b, fun e => hab (AlgHom.coe_ringHom_injective e), a.comp_algebraMap, b.comp_algebraMap⟩

private theorem hom_ext_sup {Ω : Type} [Field Ω] [CharZero Ω] (A B M : IntermediateField ℚ Ω) (hA : A ≤ M) (hB : B ≤ M)
    (hM : M ≤ A ⊔ B) (τ τ' : M →+* ℂ) (eA : ∀ x : A, τ ⟨x, hA x.2⟩ = τ' ⟨x, hA x.2⟩) (eB : ∀ x : B, τ ⟨x, hB x.2⟩ = τ' ⟨x, hB x.2⟩) :
    τ = τ' := by
  let S : IntermediateField ℚ M := (τ.eqLocusField τ').toIntermediateField fun q => by
    rw [RingHom.mem_eqLocusField]
    simp
  have h : M ≤ IntermediateField.lift S := hM.trans <| sup_le
    (fun x hx => (IntermediateField.mem_lift (⟨x, hA hx⟩ : M)).2 (eA ⟨x, hx⟩))
    (fun x hx => (IntermediateField.mem_lift (⟨x, hB hx⟩ : M)).2 (eB ⟨x, hx⟩))
  ext x
  exact (IntermediateField.mem_lift x).1 (h x.2)

private theorem inf_reg (m : Fin 2 → ℤ) (h : m 0 ≠ m 1) :
    (infOf m).Nodup ∧ ∀ z ∈ infOf m, ∃ n : ℤ, z = (n : ℂ) + (((2 : ℕ) : ℂ) - 1) / 2 := by
  refine ⟨Multiset.Nodup.map (fun i j e => ?_) Finset.univ.nodup, fun z hz => ?_⟩
  · have e' : m i = m j := by exact_mod_cast add_left_cancel e
    fin_cases i <;> fin_cases j <;> simp_all
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
    exact ⟨m i, add_comm _ _⟩

private theorem val_of_mem {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) (p : ℕ) : A.valuation (p : Ω) < 1 ↔ ((p : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have h := hA (p : 𝓞 F)
  change A.valuation (algebraMap F Ω (p : F)) < 1 ↔ (p : 𝓞 F) ∈ v.asIdeal at h
  rw [map_natCast] at h
  exact h
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2 UpperTheory.V.Sd.S3 UpperTheory.V.Cu

namespace UpperTheory.V.Z.Win.Birth

def PR {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ π : TR.CuspSub F n, π.IsRegAlg ∧ AttR ι r π ∧ PlainR π

def PrOrd : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (ξ : G F Ω →* (Qbar l)ˣ) s c m a (π : TR.CuspSub F 2) (r : G F Ω →* GL (Fin 2) (Qbar l)), OrdForm ι ξ s c m a π r → PR ι r

def PrTw : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : G F Ω →* GL (Fin 2) (Qbar l)) (κ : G F Ω →* (Qbar l)ˣ), Sd.IsAlgChar ι κ → PR ι r → PR ι (tw r κ)

def PrIso : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (n : ℕ) (r r' : G F Ω →* GL (Fin n) (Qbar l)), RepIso r r' → PR ι r → PR ι r'

def PropEGP : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω), Sd.IsCC c →
    ∀ (N w : ℕ) (φ θ : G ℚ Ω →* (Qbar l)ˣ), SlopeTestRemainingChoices N w θ → SplitAt N w φ → φ ≠ 1 → ∃ k₀ : ℕ, ∀ k ≥ k₀, φ c = (-1) ^ k →
      ∃ ρ, EisRep ι φ θ k ρ ∧ PR ι ρ

def MixSeedP : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    Even (Module.finrank ℚ F) → SplitL F l → ∀ (ι : Qbar l ≃+* ℂ) (ξ : G F Ω →* (Qbar l)ˣ), IsOpen (ξ.ker : Set (G F Ω)) →
    (∀ c, IsConjEl c → ξ c = -1) → (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Ine (F := F) A ≤ ξ.ker) →
    (∃ (u : Pl F) (A : ValuationSubring Ω), normV u = 2 ∧ IsPlaceOver A u ∧ ¬ Ine (F := F) A ≤ ξ.ker) → (∃ g, ¬ Cong (ξ g ^ 2) 1) →
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ σ ∈ Dec (F := F) A, ¬ Cong (ξ σ) 1) →
    ∀ P : Set (Pl F), (∃ w ∈ P, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) → (∃ w ∉ P, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) →
    ∃ (k t : ℕ) (π : TR.CuspSub F 2) (r : G F Ω →* GL (Fin 2) (Qbar l)), 2 ≤ k ∧ 2 ≤ t ∧ l - 1 ∣ k ∧ l - 1 ∣ t ∧
      Continuous r ∧ IrrOpen r ∧ AttR ι r π ∧ Matrix.GeneralLinearGroup.det.comp r = cycBar F Ω l ^ k * ξ ∧ ResSum r ![1, ξ] ∧
      (TypeAway r ![1, ξ] ∧ PR ι r) ∧ ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal →
        (w ∈ P → (∀ A, IsPlaceOver A w → OrdAt r ![(k : ℤ) + t, -(t : ℤ)] ![ξ, 1] A) ∧ ∀ τ : F →+* Qbar l, EmbAt w τ →
          π.HasInfChar (InfinitePlace.mk (ι.toRingHom.comp τ)) (infOf ![(k : ℤ) + t, -(t : ℤ)])) ∧
        (w ∉ P → (∀ A, IsPlaceOver A w → OrdAt r ![(k : ℤ), 0] ![1, ξ] A) ∧ ∀ τ : F →+* Qbar l, EmbAt w τ →
          π.HasInfChar (InfinitePlace.mk (ι.toRingHom.comp τ)) (infOf ![(k : ℤ), 0]))

def MixOfP : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D)
    (k₀ : IntermediateField ℚ Ω) [NumberField k₀] [IsTotallyReal k₀] (φ : G ℚ Ω →* (Qbar l)ˣ) (ι : Qbar l ≃+* ℂ),
    Hyp T k₀ φ → CharDat T k₀ φ → ∃ k t r, MixDat k₀ ι (up D.ξ) k t r ∧ PR ι r

def RhoExP : Prop :=
  PropEGP → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T₀ : Tower D),
    Ctx3 D → T₀.Ok → Four T₀ → ∀ (ι : Qbar l ≃+* ℂ) (B : ℕ) (c₀ : Coef l),
    ∃ (w : ℕ) (θ : G ℚ Ω →* (Qbar l)ˣ) (k : ℕ) (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)) (c₁ : Coef l) (h : c.O ≤ c₁.O)
      (ρ₁ : G ℚ Ω →* M2 c₁.O) (x : ValuationSubring Ω → c₁.O), w.Prime ∧ T₀.Splits w ∧ θ ^ l = 1 ∧ KillsMu w θ ∧ B ≤ k ∧
      k - 1 ≡ D.e [MOD l - 1] ∧ EisRep ι (toB (phi D T₀.pr)) θ k ρ ∧ (IrrOpen ρ ∧ PR ι ρ) ∧ c₀.O ≤ c₁.O ∧
      Mod4 D T₀.pr θ k (resQ T₀.F T₀.g0) ρ h ρ₁ x

end UpperTheory.V.Z.Win.Birth
end
end

section

open UpperTheory.GalN.V UpperTheory.V.Z.Win.Birth UpperTheory.V

open NumberField IsDedekindDomain
open Neutral.B1 hiding G
open Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

namespace UpperTheory.V.Cu.RankFourTensorSourceAtPrime

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]

private theorem toB_chi (c : Coef l) (g : G ℚ Ω) : toB (chiO ℚ Ω l c.O) g = cycBar ℚ Ω l g := by
  ext
  rfl

private theorem cont_emb (E : Type) [Field E] [NumberField E] [Algebra E Ω] : Continuous (galEmb ℚ E Ω) := by
  haveI : FaithfulSMul E Ω := (faithfulSMul_iff_algebraMap_injective E Ω).2 (algebraMap E Ω).injective
  haveI : Module.IsTorsionFree E Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) E⟩
  exact (galEmbTop ℚ E Ω).1.continuous

private theorem cont_res (F : IntermediateField ℚ Ω) [NumberField F] : Continuous (resQ F) := cont_emb F

private theorem cont_delta (d : UpperTheory.V.Cu.Dat Ω l) : Continuous (toB d.δ) := by
  have h : Continuous fun g => ((toB d.δ g : (Qbar l)ˣ) : Qbar l) := ((UpperTheory.integrality_of_norm_coefficients l).2 d.c _ _).1 d.tw.cont
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [Units.val_inv_eq_inv_val]
  exact h.inv₀ fun g => (toB d.δ g).ne_zero

end UpperTheory.V.Cu.RankFourTensorSourceAtPrime
end
