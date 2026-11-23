module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.NumberField
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.realSpan :
    RealSpan := by
  intro E M Ω F _ _ _ _ _ _ _ _ _ _ _ _ _ g hE hR
  have hnot : ∃ e : E, algebraMap E M e ∉ maximalRealSubfield M := by
    by_contra h
    push_neg at h
    obtain ⟨φ⟩ : Nonempty (M →+* ℂ) := inferInstance
    apply IsTotallyComplex.complexEmbedding_not_isReal (φ.comp (algebraMap E M))
    show ComplexEmbedding.conjugate _ = _
    ext x
    have := (mem_maximalRealSubfield_iff _).1 (h x) φ
    simpa [ComplexEmbedding.conjugate_coe_eq] using this
  obtain ⟨e, he⟩ := hnot
  set α := algebraMap E M e with hα
  have h2 : Module.finrank (maximalRealSubfield M) M = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have htop : IntermediateField.adjoin (maximalRealSubfield M) {α} = ⊤ := by
    have hd := IntermediateField.finrank_dvd_of_le_right
      (le_top : IntermediateField.adjoin (maximalRealSubfield M) {α} ≤ ⊤)
    rw [IntermediateField.finrank_top', h2, Nat.dvd_prime Nat.prime_two] at hd
    rcases hd with hd | hd
    · rw [IntermediateField.finrank_eq_one_iff] at hd
      have hmem := IntermediateField.mem_adjoin_simple_self (maximalRealSubfield M) α
      rw [hd, IntermediateField.mem_bot] at hmem
      obtain ⟨y, hy⟩ := hmem
      exact absurd (hy ▸ y.2) he
    · exact IntermediateField.eq_of_le_of_finrank_eq le_top
        (by rw [hd, IntermediateField.finrank_top', h2])
  intro x
  have hx : x ∈ IntermediateField.adjoin (maximalRealSubfield M) {α} := by
    rw [htop]
    exact IntermediateField.mem_top
  have hx' : x ∈ (IntermediateField.adjoin (maximalRealSubfield M) {α}).toSubfield := hx
  rw [IntermediateField.adjoin_toSubfield] at hx'
  have hle : Subfield.closure (Set.range (algebraMap (maximalRealSubfield M) M) ∪ {α}) ≤
      RingHom.eqLocusField ((g : Ω →+* Ω).comp (algebraMap M Ω)) (algebraMap M Ω) := by
    rw [Subfield.closure_le]
    rintro y (⟨z, rfl⟩ | hy)
    · exact hR z
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      have h1 := hE e
      rw [IsScalarTower.algebraMap_apply E M Ω] at h1
      exact h1
  exact hle hx'
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

def GroupStep : Prop :=
  ∀ (Γ : Type) [Group Γ] (Gd P : Subgroup Γ → Prop) (D : Set Γ) (Pl : Type) (Dc I : Pl → Set Γ), (∀ u, I u ⊆ Dc u) →
    (∀ H H', Gd H → Gd H' → Gd (H ⊓ H')) → (∀ H H', H ≤ H' → Gd H → Gd H') →
    (∀ U, Gd U → ∀ n : ℕ, 0 < n → ∃ ψ : Γ →* ℂˣ, Gd ψ.ker ∧ ψ ^ n = 1 ∧ (∀ g ∈ D, ψ g = 1) ∧
      ∃ u, Dc u ⊆ U ∧ ∃ τ ∈ I u, orderOf (ψ τ) = n) →
    (∀ H H' u, Gd H → Gd H' → P H → H' ≤ H → (H'.relIndex H).Prime → Dc u ⊆ H → (∃ τ ∈ I u, τ ∉ H') → P H') →
    ∀ (H₀ : Subgroup Γ) (r : Γ →* ℂˣ), Gd H₀ → P H₀ → Gd r.ker → ∀ n : ℕ, 0 < n → r ^ n = 1 →
      ∃ r' : Γ →* ℂˣ, Gd r'.ker ∧ (∀ g ∈ D, r' g = r g) ∧ P (H₀ ⊓ r'.ker)

def PowChar : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 0 < n → 2 * n ∣ p - 1 →
    ∃ lam : (ZMod p)ˣ →* ℂˣ, lam ^ n = 1 ∧ lam (-1) = 1 ∧ ∀ a, orderOf a = p - 1 → orderOf (lam a) = n

def InertiaGen : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (u : HeightOneSpectrum (𝓞 F)), IsPlaceOver A u →
    ∀ (p : ℕ) [Fact p.Prime], ((p : ℕ) : 𝓞 F) ∈ u.asIdeal → ((p : ℕ) : 𝓞 F) ∉ u.asIdeal ^ 2 →
    ∀ ζ : Ω, IsPrimitiveRoot ζ p →
    ∃ τ ∈ Ine (F := F) A, ∃ a : (ZMod p)ˣ, orderOf a = p - 1 ∧ τ ζ = ζ ^ (a : ZMod p).val

def DecPow : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (t : HeightOneSpectrum (𝓞 F)), IsPlaceOver A t →
    ∀ p : ℕ, p.Prime → ((p : ℕ) : 𝓞 F) ∉ t.asIdeal → ∀ ζ : Ω, IsPrimitiveRoot ζ p →
    (∀ g ∈ Dec (F := F) A, ∃ k : ℕ, g ζ = ζ ^ (normV t ^ k)) ∧ ∀ τ ∈ Ine (F := F) A, τ ζ = ζ

def SplitPlace : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (U : Subgroup (G F Ω)), IsOpen (U : Set (G F Ω)) →
    ∀ T : Set (HeightOneSpectrum (𝓞 F)), T.Finite →
    ∃ u ∉ T, (normV u).Prime ∧ ((normV u : ℕ) : 𝓞 F) ∈ u.asIdeal ∧ ((normV u : ℕ) : 𝓞 F) ∉ u.asIdeal ^ 2 ∧
      ∀ A : ValuationSubring Ω, IsPlaceOver A u → Dec (F := F) A ≤ U

def RootMod : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (u : HeightOneSpectrum (𝓞 F)), IsPlaceOver A u →
    ∀ p : ℕ, p.Prime → normV u = p → ∀ (y : Ω) (n : ℕ), 0 < n → (∀ g ∈ Dec (F := F) A, g y = y) →
    (∀ m : ℕ, y ^ n = (m : Ω) → ∃ b : ZMod p, b ^ n = (m : ZMod p)) ∧ (IsPrimitiveRoot y n → ¬ p ∣ n → n ∣ p - 1)

def FreshPrime : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (U : Subgroup (G F Ω)), IsOpen (U : Set (G F Ω)) →
    ∀ T : Set (HeightOneSpectrum (𝓞 F)), T.Finite → ∀ n : ℕ, 0 < n →
    ∃ u ∉ T, (normV u).Prime ∧ ((normV u : ℕ) : 𝓞 F) ∈ u.asIdeal ∧ ((normV u : ℕ) : 𝓞 F) ∉ u.asIdeal ^ 2 ∧
      (∀ A : ValuationSubring Ω, IsPlaceOver A u → Dec (F := F) A ≤ U) ∧ 2 * n ∣ normV u - 1 ∧
      ∀ t ∈ T, ((normV u : ℕ) : 𝓞 F) ∉ t.asIdeal ∧ ∃ b : ZMod (normV u), b ^ n = (normV t : ZMod (normV u))

def ExFld : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (H : Subgroup (G (maximalRealSubfield E) Ω)), Good H → ∃ X : Fld E Ω, Cuts X H

def InclOf : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (X Y : Fld E Ω), fixGrp E Ω Y.K ≤ fixGrp E Ω X.K →
    ∃ (_ : Algebra X.K Y.K) (_ : IsScalarTower E X.K Y.K) (_ : IsScalarTower X.K Y.K Ω), IsGalois X.K Y.K ∧
      Module.finrank X.K Y.K = (fixGrp E Ω Y.K).relIndex (fixGrp E Ω X.K)

def IndexComap : Prop :=
  ∀ (Γ Γ' : Type) [Group Γ] [Group Γ'] (f : Γ' →* Γ) (H H' : Subgroup Γ), commutator Γ ≤ H' → H' ≤ H → (H'.relIndex H).Prime →
    (∃ τ, f τ ∈ H ∧ f τ ∉ H') → (H'.comap f).relIndex (H.comap f) = H'.relIndex H

def LayerOf : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (S : Set (HeightOneSpectrum (𝓞 E))) (H H' : Subgroup (G (maximalRealSubfield E) Ω)), Good H' → H' ≤ H →
    (H'.relIndex H).Prime → ∀ X Y : Fld E Ω, Cuts X H → Cuts Y H' →
    ∀ u : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), (∀ s ∈ S, s.under (𝓞 (maximalRealSubfield E)) ≠ u) →
    (∀ A : ValuationSubring Ω, IsPlaceOver A u → ∀ g ∈ Dec (F := maximalRealSubfield E) A, Fixes E g ∧ g ∈ H) →
    (∃ A : ValuationSubring Ω, IsPlaceOver A u ∧ ∃ τ ∈ Ine (F := maximalRealSubfield E) A, τ ∉ H') →
    Layer S X Y ∧ ∀ (_ : Algebra X.K Y.K) (_ : IsScalarTower X.K Y.K Ω), Module.finrank X.K Y.K = H'.relIndex H

def DegOf : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω] [Algebra M Ω]
    [IsScalarTower K M Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 M)), IsPlaceOver A v → IsPlaceOver A w → (∀ τ ∈ Ine (F := K) A, Fixes M τ) →
    ∀ (φ : G K Ω) (d : ℕ), 0 < d → IsFrob A (normV v) φ → (∀ k : ℕ, Fixes M (φ ^ k) ↔ d ∣ k) → normV w = normV v ^ d

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

def RamSplit (E : Type) {Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (H : Subgroup (G (maximalRealSubfield E) Ω)) : Prop :=
  ∀ (t : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (A : ValuationSubring Ω), IsPlaceOver A t →
    Ine (F := maximalRealSubfield E) A ≤ H ∨ ∀ g ∈ Dec (F := maximalRealSubfield E) A, Fixes E g

def MoveRoot : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (U : Subgroup (G ℚ Ω)), IsOpen (U : Set (G ℚ Ω)) →
    ∀ ℓ : ℕ, ℓ.Prime → ∃ (b : ℕ) (σ : G ℚ Ω), σ ∈ U ∧ ∀ ζ : Ω, IsPrimitiveRoot ζ (ℓ ^ b) → σ ζ ≠ ζ

def NormVal : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (U : Subgroup (G ℚ Ω)), IsOpen (U : Set (G ℚ Ω)) →
    ∀ q : ℕ, 1 < q → ∃ D : ℕ, 0 < D ∧ ∀ (z : Ω) (n c : ℕ), (∀ τ ∈ U, τ z = z) → z ^ n * (q : Ω) ^ c = 1 → n ∣ c * D

def KumMove : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (U : Subgroup (G ℚ Ω)), IsOpen (U : Set (G ℚ Ω)) →
    ∀ ℓ q : ℕ, ℓ.Prime → 1 < q → ∃ j : ℕ, ∀ k, j ≤ k → ∀ ζ y : Ω, IsPrimitiveRoot ζ (ℓ ^ k) → y ^ ℓ ^ j = (q : Ω) →
      ∃ σ ∈ U, σ ζ = ζ ∧ σ y ≠ y

def OrdPrime : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (ℓ k q B : ℕ), ℓ.Prime → 1 < q →
    ∃ p : ℕ, p.Prime ∧ B < p ∧ ℓ ^ k ∣ orderOf (q : ZMod p) ∧ ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 →
      ∀ h : Ω ≃+* Ω, (∀ z, h z ∈ A ↔ z ∈ A) → ∀ y : E, h (algebraMap E Ω y) = algebraMap E Ω y

def CharOrd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ℓ k : ℕ) (a : (ZMod p)ˣ), ℓ.Prime → ℓ ^ (k + 1) ∣ orderOf a →
    ∃ lam : (ZMod p)ˣ →* ℂˣ, lam (-1) = 1 ∧ orderOf (lam a) = ℓ ^ k

def UnrCharAt (f : ℕ) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))),
    ∃ r : G (maximalRealSubfield E) Ω →* ℂˣ, Good r.ker ∧ RamSplit E r.ker ∧
      ∀ A : ValuationSubring Ω, IsPlaceOver A v → Ine (F := maximalRealSubfield E) A ≤ r.ker ∧
        ∀ φ : G (maximalRealSubfield E) Ω, IsFrob A (normV v) φ → orderOf (r φ) = f

def UnrCharPP : Prop := ∀ ℓ k : ℕ, ℓ.Prime → UnrCharAt (ℓ ^ k)

def FreshSplit : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (U : Subgroup (G (maximalRealSubfield E) Ω)),
    IsOpen (U : Set (G (maximalRealSubfield E) Ω)) →
    ∀ T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield E))), T.Finite → ∀ n : ℕ, 0 < n →
    ∃ ψ : G (maximalRealSubfield E) Ω →* ℂˣ, Good ψ.ker ∧ RamSplit E ψ.ker ∧ ψ ^ n = 1 ∧
      (∀ t ∈ T, ∀ A : ValuationSubring Ω, IsPlaceOver A t → ∀ g ∈ Dec (F := maximalRealSubfield E) A, ψ g = 1) ∧
      ∃ u ∉ T, ∀ A : ValuationSubring Ω, IsPlaceOver A u → Dec (F := maximalRealSubfield E) A ≤ U ∧
        ∃ τ ∈ Ine (F := maximalRealSubfield E) A, orderOf (ψ τ) = n

theorem RamSplit.inf {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {H H' : Subgroup (G (maximalRealSubfield E) Ω)} (h : RamSplit E H) (h' : RamSplit E H') : RamSplit E (H ⊓ H') := by
  intro t A hA
  rcases h t A hA with h1 | h1
  · rcases h' t A hA with h2 | h2
    · exact Or.inl (le_inf h1 h2)
    · exact Or.inr h2
  · exact Or.inr h1

theorem RamSplit.mono {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {H H' : Subgroup (G (maximalRealSubfield E) Ω)} (hle : H ≤ H') (h : RamSplit E H) : RamSplit E H' := by
  intro t A hA
  rcases h t A hA with h1 | h1
  · exact Or.inl (h1.trans hle)
  · exact Or.inr h1

theorem unrCharAt_of (h : UnrCharPP) (f : ℕ) (hf : 0 < f) : UnrCharAt f := by
  induction f using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp _ => exact h p n hp
  | zero => exact absurd hf (lt_irrefl 0)
  | one => simpa using h 2 0 Nat.prime_two
  | coprime a b ha hb hab iha ihb =>
    intro E Ω _ _ _ _ _ _ v
    obtain ⟨r, h1, h2, h3⟩ := iha (by omega) E Ω v
    obtain ⟨s, k1, k2, k3⟩ := ihb (by omega) E Ω v
    have hle : r.ker ⊓ s.ker ≤ (r * s).ker := fun g hg => by
      rw [MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.mem_ker.1 hg.1, MonoidHom.mem_ker.1 hg.2, one_mul]
    refine ⟨r * s, (h1.inf k1).mono hle, (h2.inf k2).mono hle, fun A hA =>
      ⟨(le_inf (h3 A hA).1 (k3 A hA).1).trans hle, fun φ hφ => ?_⟩⟩
    have e1 := (h3 A hA).2 φ hφ
    have e2 := (k3 A hA).2 φ hφ
    rw [MonoidHom.mul_apply, (Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime (by rwa [e1, e2]), e1, e2]

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end
