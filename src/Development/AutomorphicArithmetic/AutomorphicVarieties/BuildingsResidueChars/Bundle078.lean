module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle003
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle315
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle077
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle048
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwAbs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ComplexWhittaker.ExpEqOfHasDerivAt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace
open scoped NumberField.AdeleRing

theorem UpperTheory.finiteDimensional_span_maximalCompact_translates_of_fix :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (D : TypeDat K n) (f : G1 K n → ℂ), Continuous f → D.Fix f → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : KG K n => fun m => f (m * k))) := by
  intro K _ _ n D f hf hfix
  obtain ⟨-, -, 𝒜, hfd, -, hA⟩ := typeFin D
  haveI := hfd
  obtain ⟨O, hO, hUO⟩ := D.isOpen
  haveI : CompactSpace (KG K n) :=
    isCompact_iff_compactSpace.1 ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 n).1
  let W : Subgroup (KG K n) := D.U.subgroupOf (KG K n)
  have hWo : IsOpen (W : Set (KG K n)) := by
    have hW : (W : Set (KG K n)) = (fun k : KG K n => ((k : G1 K n) : AdelicGLn.AdelicGL K n)) ⁻¹' O := by
      ext k
      exact ⟨fun h => ((hUO k).1 h).1, fun h => (hUO k).2 ⟨h, k.2⟩⟩
    rw [hW]
    exact hO.preimage (continuous_subtype_val.comp continuous_subtype_val)
  haveI : Finite (KG K n ⧸ W) := Subgroup.quotient_finite_of_isOpen W hWo
  let B := Module.finBasis ℂ 𝒜
  let x : G1 K n → 𝒜 := fun m => ⟨fun u : D.U => f (m * u), hA f hf hfix m⟩
  let c : Fin (Module.finrank ℂ 𝒜) × (KG K n ⧸ W) → G1 K n → ℂ :=
    fun p m => B.repr (x (m * ((Quotient.out p.2 : KG K n) : G1 K n))) p.1
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range c)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range c)
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range c)) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul W k
  set q : KG K n ⧸ W := (k : KG K n ⧸ W) with hq
  let u : D.U := ⟨(((h : KG K n)⁻¹ : KG K n) : G1 K n), Subgroup.mem_subgroupOf.1 (W.inv_mem h.2)⟩
  have hk : (k : G1 K n) = ((Quotient.out q : KG K n) : G1 K n) * u := by
    have : k = Quotient.out q * (h : KG K n)⁻¹ := by
      rw [hh]; simp
    exact congrArg Subtype.val this
  have e : (fun m => f (m * k)) = ∑ i, ((B i : 𝒜) : D.U → ℂ) u • c (i, q) := by
    funext m
    have h1 := congrArg (fun y : 𝒜 => (y : D.U → ℂ) u)
      (B.sum_repr (x (m * ((Quotient.out q : KG K n) : G1 K n))))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hk, ← mul_assoc]
    change _ = ∑ i, ((B i : 𝒜) : D.U → ℂ) u * B.repr (x (m * ((Quotient.out q : KG K n) : G1 K n))) i
    simp only [mul_comm (((B _ : 𝒜) : D.U → ℂ) u)]
    exact h1.symm
  change (fun m => f (m * (k : G1 K n))) ∈ Submodule.span ℂ (Set.range c)
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, q), rfl⟩)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU

theorem UpperTheory.mem_iSup_automorphicReps_of_invariant_form :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (B : (UA E n → ℂ) →ₗ⋆[ℂ] (UA E n → ℂ) →ₗ[ℂ] ℂ), (∀ φ, IsAutFormU φ → B φ φ = 0 → φ = 0) → (∀ x φ ψ, IsAutFormU φ → IsAutFormU ψ → B (RU E n x φ) (RU E n x ψ) = B φ ψ) → ∀ φ : UA E n → ℂ, IsAutFormU φ → φ ∈ ⨆ σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ}, σ.1 := by
  intro E _ _ _ n B hdef hinv φ hφ
  classical
  haveI : FiniteDimensional ℂ (admitted.X φ) := hφ.kfin
  have hXA : admitted.X φ ≤ autU E n := Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact RU_mem_autU _ _ (mem_autU.2 hφ))
  have haut : ∀ v : admitted.X φ, IsAutFormU (v : UA E n → ℂ) := fun v => mem_autU.1 (hXA v.2)
  let Z : Subrepresentation ((RU E n).comp (infU E n).subtype) :=
    ⟨admitted.X φ, fun g v hv => admitted.RU_mem_X φ g hv⟩
  let ρ : Representation ℂ (infU E n) (admitted.X φ) := Z.toRepresentation
  have hρ : ∀ g (v : admitted.X φ), ((ρ g v : admitted.X φ) : UA E n → ℂ) = RU E n g v := fun _ _ => rfl
  let B' : admitted.X φ →ₗ⋆[ℂ] admitted.X φ →ₗ[ℂ] ℂ := (B.comp (admitted.X φ).subtype).compl₂ (admitted.X φ).subtype
  have hx := UpperTheory.mem_iSup_irreducible_of_admissible_unitary (infU E n) (admitted.X φ) ρ B'
    (fun v hv => Subtype.ext (hdef _ (haut v) hv))
    (fun g u v => hinv g _ _ (haut u) (haut v))
    (fun v => ⟨⊥, fun k hk => by rw [Subgroup.mem_bot.1 hk, map_one]; rfl, inferInstance,
      fun w => Set.finite_range _⟩)
    ⟨φ, admitted.self_mem_X φ⟩
  have hle : (⨆ U : {U : Submodule ℂ (admitted.X φ) // U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧
      ∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U}, U.1) ≤
      (⨆ σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ}, σ.1).comap (admitted.X φ).subtype := by
    refine iSup_le ?_
    rintro ⟨U, h0, hst, hirr⟩ u hu
    let Y : Subrepresentation ρ := ⟨U, fun g v hv => hst g v hv⟩
    let τ : Representation ℂ (infU E n) U := Y.toRepresentation
    have hτ : τ.IsIrreducible := by
      refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨Submodule.nontrivial_iff_ne_bot.2 h0, fun N hN => ?_⟩
      rcases hirr (N.map U.subtype) (Submodule.map_subtype_le _ _) (by
        rintro g _ ⟨w, hw, rfl⟩
        exact ⟨τ g w, hN g w hw, rfl⟩) with h | h
      · left
        exact Submodule.map_injective_of_injective U.injective_subtype (by rw [h, Submodule.map_bot])
      · right
        exact Submodule.map_injective_of_injective U.injective_subtype
          (by rw [h, Submodule.map_top, Submodule.range_subtype])
    exact UpperTheory.admissible_equivariantForms_representation E n B hdef hinv U τ
      (GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible _ _ τ hτ)
      ((admitted.X φ).subtype ∘ₗ U.subtype) (fun v => haut v.1) (fun _ _ => rfl) ⟨u, hu⟩
  exact hle hx
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

theorem UpperTheory.exists_splitPrime_cmDatum :
    UpperTheory.V.Sd.S3.SplitPrime := by
  intro Ω _ _ _ U hU hc M hM
  obtain ⟨N, hN, hNU⟩ := UpperTheory.V.CF.kwAbs Ω U hU hc
  obtain ⟨w, hw, hMw, hmod⟩ := Nat.exists_prime_gt_modEq_one M (Nat.mul_ne_zero hM.ne' hN.ne')
  have hwM : w ≡ 1 [MOD M] := Nat.ModEq.of_dvd (Dvd.intro N rfl) hmod
  have hwN : w ≡ 1 [MOD N] := Nat.ModEq.of_dvd (Dvd.intro_left M rfl) hmod
  refine ⟨w, hw, hMw, hwM, ?_⟩
  intro A hA g hg
  haveI : Fact (Nat.Prime w) := ⟨hw⟩
  have hcop : N.Coprime w := by
    have h := Nat.ModEq.gcd_eq hwN
    rw [Nat.gcd_one_left] at h
    exact Nat.Coprime.symm h
  obtain ⟨k, hk⟩ := UpperTheory.V.LDataCardLeFinrank.decActRoots ℚ Ω w A hA N hcop g hg
  apply hNU
  intro ζ hζ
  rw [hk ζ hζ]
  have hpow : w ^ k % N = 1 % N := by
    have h := Nat.ModEq.pow k hwN
    rwa [one_pow] at h
  rw [← Nat.div_add_mod (w ^ k) N, pow_add, pow_mul, hζ, one_pow, one_mul, hpow]
  rcases Nat.lt_or_ge 1 N with h1 | h1
  · rw [Nat.mod_eq_of_lt h1, pow_one]
  · have hN1 : N = 1 := by omega
    subst hN1
    simp only [pow_one] at hζ
    simp [hζ]
end
