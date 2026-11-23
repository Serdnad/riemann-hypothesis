module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AlgOfCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle067
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle062
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle085
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle061
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.AutomorphyRankFourPolarizedAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts
import Formalism.DoubleCosetMeasures.Statement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.PairGOps
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.PinNum

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af UpperTheory.V.Z.Gam
open UpperTheory.GalN.V GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win.Birth

private theorem exists_polarized {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {l : ℕ} [Fact l.Prime] {n : ℕ} (H : HypothesesH) {ι : Qbar l ≃+* ℂ} (hn : 1 ≤ n) {r : G K Ω →* GL (Fin n) (Qbar l)}
    {π : CuspSub K n} (hp : Sol.Pol ι r) (ha : AttC ι r π) : ∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ := by
  haveI : IsAlgClosure (maximalRealSubfield K) Ω :=
    ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.trans (maximalRealSubfield K) K Ω⟩
  obtain ⟨μ, χ, c, P, hμ, hs, hc, hP⟩ := UpperTheory.cyclotomicCharacter_plusPart (algOfCyc H) UpperTheory.cyclotomic_char_conj_invariant K Ω l ι n r hp
  have hdual := selfDualC H K Ω l ι n hn r π ha χ μ hμ c P hc hP
  have hsign := UpperTheory.sign_at_infinity_of_parallel_weight UpperTheory.adelicSolution_parallel _ Ω l ι χ μ hμ hs
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace (maximalRealSubfield K)) := inferInstance
  have hsq : ((χ.locInf v₀ (-1) : ℂˣ) : ℂ) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, neg_one_sq, map_one, Units.val_one]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ∀ v, χ.locInf v (-1) = (-1) ^ m := by
    rcases sq_eq_one_iff.1 hsq with e | e
    · exact ⟨0, fun u => (hsign u v₀).trans (Units.ext (by simpa using e))⟩
    · exact ⟨1, fun u => (hsign u v₀).trans (Units.ext (by simpa using e))⟩
  have hnorm : compNorm K (χ * quadChar K ^ (m + n)) = compNorm K χ := by
    rw [map_mul, map_pow, compNorm_quadChar, one_pow, mul_one]
  refine ⟨χ * quadChar K ^ (m + n), fun v => ?_, hnorm ▸ hdual⟩
  change χ.locInf v (-1) * (quadChar K ^ (m + n)).locInf v (-1) = (-1) ^ n
  rw [locInf_pow, hm, quadChar_locInf, ← pow_add, ← add_assoc, pow_add, ← two_mul, pow_mul]
  simp

private theorem unram_of_charPol {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion E)ˣ}
    (ha : IsLocalArtin h a) {n : ℕ} (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ))
    (H : ∀ g : Weil h, deg g = 0 → ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) = (X - 1 : ℂ[X]) ^ n) (j : Fin n)
    (x : (w.adicCompletion E)ˣ) (hx : ord (w.adicCompletion E) x = 0) : ξ j x = 1 := by
  obtain ⟨g, rfl⟩ := ha.surj x
  have h0 : deg g = 0 := by
    have := ha.ord_eq g
    rw [hx] at this
    omega
  have e := congrArg (Polynomial.eval ((ξ j (a g) : ℂˣ) : ℂ)) (H g h0)
  rw [Polynomial.eval_prod, Finset.prod_eq_zero (Finset.mem_univ j) (by simp)] at e
  have e2 : ((ξ j (a g) : ℂˣ) : ℂ) - 1 = 0 := by
    have := e.symm
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one] at this
    exact (pow_eq_zero_iff j.pos.ne').1 this
  exact Units.ext (by simpa [sub_eq_zero] using e2)

end UpperTheory.V.Z.Win.Birth
end
end

section

theorem UpperTheory.V.Z.Win.Birth.awOne :
    UpperTheory.V.Z.Win.Birth.AwOne := by
  intro F Ω _ _ _ _ _ _ l _ n hn ι r π hπ hwin π' _ hπ'
  obtain ⟨t, ht⟩ := hwin
  refine ⟨t, fun v => UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.suppSmo F n hn π π' ?_ t v (ht v)⟩
  filter_upwards [hπ.2, hπ'.2] with w h1 h2
  obtain ⟨B, hB, hE⟩ := h1
  obtain ⟨B', hB', hE'⟩ := h2
  have e : B = B' := (UpperTheory.hecke_eigenvalue_basic_properties F Ω l ι w).2.2 n r B B' hE hE'
  exact ⟨B, hB, e ▸ hB'⟩
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2 UpperTheory.V.Sd.S3 UpperTheory.V.Cu

namespace UpperTheory.V.Z.Win.Birth

theorem mkCsdW {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} [IsCMField F]
    {ι : Qbar l ≃+* ℂ} {r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)} (h : UpperTheory.GalN.V.AutCsd0 ι r) (_ : Continuous r → WitA ι r) : IsAutCsd ι r := h

theorem mkCsdW' {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} [IsCMField F]
    {ι : Qbar l ≃+* ℂ} {r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)} (h : UpperTheory.GalN.V.AutCsd0 ι r) (u : Continuous r → WitA ι r) : IsAutCsdA ι r := ⟨h, u⟩

def SphOfUnrW : Prop :=
  ∀ (M Ω : Type) [Field M] [NumberField M] [IsCMField M] [Field Ω] [Algebra M Ω] [IsAlgClosure M Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (r : _root_.Formalism.ConjugateSelfDual.G M Ω →* GL (Fin n) (Qbar l)) (π : CuspSub M n), Continuous r → Sol.Pol ι r →
    (CG.mk π).IsRegAlg → AttC ι r π → AllW ι r → ∀ w : HeightOneSpectrum (𝓞 M), ((l : ℕ) : 𝓞 M) ∉ w.asIdeal →
    ∀ A : ValuationSubring Ω, _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w → (∀ s ∈ Ine (F := M) A, r s = 1) → ∃ B, (CG.mk π).HasSat w B

def BadOfW : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (K' L M : IntermediateField ℚ Ω)
    [NumberField L] [NumberField M] [IsCMField M] [Algebra L M] [IsScalarTower L M Ω] [IsAlgClosure M Ω] [IsGalois L M], M = K' ⊔ L →
    ∀ (ρ : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* GL (Fin 2) (Qbar l)) (r : _root_.Formalism.ConjugateSelfDual.G M Ω →* GL (Fin 2) (Qbar l)) (π : CuspSub M 2), GoodAt K' L ρ → Continuous r → Af.Sol.Pol ι r →
    (CG.mk π).IsRegAlg → AttC ι r π → AllW ι r →
    (∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := M) A, ρ (resQ M s) = 1 → r s = 1) → Z.InvariantSubmoduleMonicPolynomial.E.SplitBad L π

def IndAutLP : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D)
    (k₀ : IntermediateField ℚ Ω) [NumberField k₀] [IsTotallyReal k₀] (φ : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* (Qbar l)ˣ) (ι : Qbar l ≃+* ℂ) (k t : ℕ)
    (r : _root_.Formalism.ConjugateSelfDual.G k₀ Ω →* GL (Fin 2) (Qbar l)) (α β : (Qbar l)ˣ) (R : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* GL (Fin 4) (Qbar l)) (δ : _root_.Formalism.ConjugateSelfDual.G T.F Ω →* (Qbar l)ˣ),
    IndDat T k₀ φ ι k t r α β R δ → PR ι r → IsAutC ι (R.comp (resQ T.L)) ∧ AllW ι (R.comp (resQ T.L))

def OffW {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (K' : IntermediateField ℚ Ω)
    (ρ : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* GL (Fin 2) (Qbar l)) (R : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* GL (Fin 4) (Qbar l)) : Prop :=
  ∀ (L : IntermediateField ℚ Ω) [NumberField L] [_root_.NumberField.IsTotallyComplex L], IsAbelianGalois ℚ L → ¬ K' ≤ L → GoodAt K' L ρ →
    IsIrr (R.comp (resQ L)) → AllW ι (R.comp (resQ L))

def RankFourAutomorphyOfTensor : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (K' : IntermediateField ℚ Ω) [NumberField K'], Module.finrank ℚ K' = 2 → IsTotallyComplex K' →
    ∀ ρ : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* GL (Fin 2) (Qbar l), Continuous ρ → IsAutR ι ρ → IrrOpen ρ → PR ι ρ →
    ∀ (g0 : _root_.Formalism.ConjugateSelfDual.G ℚ Ω) (m : ℕ) (c₁ : Coef l) (κ : _root_.Formalism.ConjugateSelfDual.G K' Ω →* (Qbar l)ˣ), g0 ∉ K'.fixingSubgroup →
    (∃ τ s, TauDat ι K' g0 (m * 1) c₁ τ s (κ ^ 1)) →
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ 9 ∧ ∀ (ρ₁ τ : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* M2 c₁.O) s, RepIso ρ (mapRep (algebraMap c₁.O (PadicAlgCl l)) ρ₁).toHomUnits →
      TauDat ι K' g0 (m * j) c₁ τ s (κ ^ j) → AutOffS ι K' ρ (tenB ρ₁ τ) ∧ OffW ι K' ρ (tenB ρ₁ τ)

def AwChain : Prop :=
  ∀ (F E M Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M]
    [Field Ω] [Algebra F E] [Algebra E M] [Algebra F Ω] [Algebra E Ω] [Algebra M Ω] [IsScalarTower F E Ω] [IsScalarTower E M Ω] [IsAlgClosure F Ω]
    [IsAlgClosure M Ω] [IsGalois E M] [Group.IsSolvable (M ≃ₐ[E] M)], Module.finrank F E = 2 → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin 2) (Qbar l)) (κ : _root_.Formalism.ConjugateSelfDual.G E Ω →* (Qbar l)ˣ), Continuous r → PR ι r → Sd.IsAlgChar ι κ →
    IsIrr ((r.comp (galEmb F E Ω)).comp (galEmb E M Ω)) → AllW ι ((tw (r.comp (galEmb F E Ω)) κ).comp (galEmb E M Ω))

def PotOrd : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)) (m : Fin n → ℤ) (ψ : Fin n → _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ) (κ : _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ), (∀ i j, m i ≠ m j + 1) →
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → OrdAt r m ψ A) →
    ∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → PotUnl (tw r κ) v

end UpperTheory.V.Z.Win.Birth
end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CuspRep GroundTheory.Global.SemiLocal UpperTheory.V.Z.Gam

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.Win.Birth

private theorem map_nm {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    {v : HeightOneSpectrum (𝓞 K)} (w : PlacesOver M v) (hs : Function.Surjective (completionMap v w.1))
    (x : (w.1.adicCompletion M)ˣ) : Units.map (completionMap v w.1).toMonoidHom (nm w x) = x := by
  have hb : Function.Bijective (Algebra.linearMap (v.adicCompletion K) (w.1.adicCompletion M)) :=
    ⟨(completionMap v w.1).injective, hs⟩
  have h1 : Module.finrank (v.adicCompletion K) (w.1.adicCompletion M) = 1 := by
    rw [← (LinearEquiv.ofBijective _ hb).finrank_eq, Module.finrank_self]
  obtain ⟨y, hy⟩ := hs (x : w.1.adicCompletion M)
  refine Units.ext ?_
  change completionMap v w.1 (Algebra.norm (v.adicCompletion K) (x : w.1.adicCompletion M)) = x
  rw [← hy]
  have h2 : Algebra.norm (v.adicCompletion K) (completionMap v w.1 y) = y ^ Module.finrank (v.adicCompletion K) (w.1.adicCompletion M) :=
    Algebra.norm_algebraMap y
  rw [h2, h1, pow_one]

private theorem thru_split {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    {v : HeightOneSpectrum (𝓞 K)} (w : PlacesOver M v) (hs : Function.Surjective (completionMap v w.1))
    (ζ : (w.1.adicCompletion M)ˣ →* ℂˣ) (hζ : IsSmoothChar ζ) :
    ∃ χ : (v.adicCompletion K)ˣ →* ℂˣ, IsSmoothChar χ ∧ IsUnram (ζ * χ.comp (nm w)) := by
  have hc : Continuous (Units.map (completionMap v w.1).toMonoidHom) :=
    Continuous.units_map _ (continuous_completionMap v w.1)
  refine ⟨(ζ.comp (Units.map (completionMap v w.1).toMonoidHom))⁻¹, ?_, fun x _ => ?_⟩
  · have he : (((ζ.comp (Units.map (completionMap v w.1).toMonoidHom))⁻¹).ker : Set (v.adicCompletion K)ˣ) =
        Units.map (completionMap v w.1).toMonoidHom ⁻¹' (ζ.ker : Set _) := by
      ext y
      simp [MonoidHom.mem_ker]
    change IsOpen _
    rw [he]
    exact hζ.preimage hc
  · change ζ x * (ζ (Units.map (completionMap v w.1).toMonoidHom (nm w x)))⁻¹ = 1
    rw [map_nm w hs x, mul_inv_cancel]

end UpperTheory.V.Z.Win.Birth

open UpperTheory.V.Z.Win.Birth in
theorem UpperTheory.V.Z.Win.Birth.thruBad :
    UpperTheory.V.Z.Win.Birth.ThruBad := by
  intro K M _ _ _ _ _ _ _ _ π hbad v w s hs ζ hζ hmem
  by_cases hsp : UpperTheory.ConvolutionTheory.GM.Split M v
  · exact thru_split w (hsp w) ζ hζ
  · have hw : w.1.under (𝓞 K) = v := HeightOneSpectrum.ext w.2.over.symm
    obtain ⟨B, hB⟩ := (hbad v hsp).2 w.1 hw
    obtain ⟨μ, hμ, e⟩ := (suppFacts M 2 (by norm_num) π w.1).2.2.2.1 s B hs hB _ hmem
    obtain rfl : ζ = μ := IrrGL.ofChar_inj.1 e
    exact ⟨1, isSmoothChar_one, by simpa using hμ⟩
end
end
