module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransferAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ArithmeticPointClassicality
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle009
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.Bundle001

@[expose] public section

section

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

theorem UpperTheory.V.Pr.marks_of_link :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
      {L : Type} [Field L] [NumberField L] [Algebra L Ω] {Φ : Fr.Frame l (ResidueField O)} (k : GalLink η Ψ σ g₁ B M L Φ) [CharP (ResidueField O) l] {C₀ : ℕ}, Φ.Ok C₀ → l ∣ M → σ * σ = 1 →
    Ψ σ = 1 → Marks η Ψ σ g₁ := by
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ Φ k _ C₀ ok _ hσ hΨ
  obtain ⟨hc, ec⟩ := k.c
  obtain ⟨hg, eg⟩ := k.g0
  refine ⟨hσ, ?_, hΨ, ?_, ?_⟩
  · have h := k.del ⟨σ, hc⟩
    rw [ec, ok.del_c] at h
    exact h.symm
  · have h := k.del ⟨g₁, hg⟩
    rw [eg] at h
    exact h.symm.trans Φ.g0.2
  · have h := k.psi ⟨g₁, hg⟩
    rw [eg] at h
    have h2 := ok.baseSubgroup_spec
    rw [h] at h2
    rw [← residue_ne_zero_iff_isUnit, map_sub, map_pow, map_one, sub_ne_zero]
    intro h3
    apply h2
    ext
    rw [Units.val_pow_eq_pow_val]
    exact h3
end

section

noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af

namespace UpperTheory.V.Pr

instance (priority := high) fieldTorsionFree (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] : Module.IsTorsionFree L Ω :=
  DivisionSemiring.to_moduleIsTorsionFree

def CoefIs : Prop := ∀ (l : ℕ) [Fact l.Prime] (c : Coef l), Fr.IsCoef l c.O

def CoefEx : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (ka ka' : G L Ω →* (Qbar l)ˣ), Continuous ka → Continuous ka' →
    ∃ c₁ : Coef l, c.O ≤ c₁.O ∧ W.Large L c₁ ∧ (∀ g, (ka g).val ∈ c₁.O) ∧ (∀ g, (ka' g).val ∈ c₁.O) ∧
      ∃ f : ResidueField c.O →+* ResidueField c₁.O, ∀ (a : c.O) (b : c₁.O), a.1 = b.1 → f (residue c.O a) = residue c₁.O b

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}


variable (σ M) in
structure IsKa (ι : Qbar l ≃+* ℂ) (n : ℕ) (ka : G L Ω →* (Qbar l)ˣ) : Prop where
  alg : Sd.IsAlgChar ι ka
  conj : ∀ s s' : G L Ω, galEmb ℚ L Ω s' = σ * galEmb ℚ L Ω s * σ⁻¹ → ka s * ka s' = cycBar L Ω l s ^ (1 - (n : ℤ))
  unr : ∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → ∀ s ∈ Ine (F := L) A, ka s = 1
  ord : ∃ m : ℕ, ¬ l ∣ m ∧ ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := L) A, ka s ^ m = 1

structure CReal (k : GalLink η Ψ σ g₁ B M L Φ) (c₁ : Coef l) [Fr.IsCoef l c₁.O]
    (f : ResidueField c.O →+* ResidueField c₁.O) (n : ℕ) (ka : G L Ω →* (Qbar l)ˣ) : Type 1 where
  n23 : n = 2 ∨ n = 3
  C₀ : ℕ
  ok : (Φ.ext f).Ok C₀
  big : (Φ.ext f).Big C₀
  le : c.O ≤ c₁.O
  hf : ∀ (a : c.O) (b : c₁.O), a.1 = b.1 → f (residue c.O a) = residue c₁.O b
  s : W.HidaSetting l L Ω
  V : s.Lev
  hV : V.S' = s.S
  r : W.Resid V.frame c₁.O n
  K : TwLink (Φ.ext f) r
  π_pr : ∀ g, K.π (V.pr g) = k.p0 g
  κ_pr : ∀ g, (K.κ (V.pr g)).val.1 = (ka g).val
  lam_j : ∀ (v : W.Vl l L) (g : Dec (F := L) (s.A v)), (k.j (K.e v) (K.lam v g)).1 = galEmb ℚ L Ω g
  A_pl : ∀ v : W.Vl l L, s.A v = k.pl (K.e v)
  v0 : r.V0ok
  v0M : ¬ (s.A s.v0).valuation (M : Ω) < 1
  B₀ : W.UniversalOrdinaryDeterminantRing r
  S : Fr.Space c₁.O (Φ.ext f) n

def CReal.T {k : GalLink η Ψ σ g₁ B M L Φ} {c₁ : Coef l} [Fr.IsCoef l c₁.O] {f : ResidueField c.O →+* ResidueField c₁.O}
    {n : ℕ} {ka : G L Ω →* (Qbar l)ˣ} (R : CReal k c₁ f n ka) : Setup (Φ.ext f) n :=
  ⟨R.n23, R.C₀, R.ok, R.big, Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero, R.V.frame, R.r, R.K, R.B₀, R.S⟩

end

structure LinkHyp {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l)
    (N e : ℕ) (η : G ℚ Ω →* ℤˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) : Prop where
  e_pos : 1 ≤ e
  dvd : l * N ∣ M
  M_pos : M ≠ 0
  ram : ∀ B' : ValuationSubring Ω, ¬ Ine (F := ℚ) B' ≤ η.ker → B'.valuation (M : Ω) < 1
  atl : B.valuation (l : Ω) < 1
  cc : Sd.IsCC σ

def KaOf : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ), IsKa σ M ι 3 (cycBar L Ω l)⁻¹ ∧
    ∀ (K : Type) [Field K] [NumberField K] [Algebra K Ω], η.ker = galOf ℚ K Ω → ∀ κ : G K Ω →* (Qbar l)ˣ, Sd.IsTwist ι σ κ →
      ∃ ka : G L Ω →* (Qbar l)ˣ, IsKa σ M ι 2 ka ∧ ∀ (s : G L Ω) (s' : G K Ω), galEmb ℚ L Ω s = galEmb ℚ K Ω s' → ka s = κ s'

def CRealEx : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O) (n : ℕ)
    (ka : G L Ω →* (Qbar l)ˣ) (C₀ : ℕ), (n = 2 ∨ n = 3) → Φ.Ok C₀ → Φ.Big C₀ → c.O ≤ c₁.O →
    (∀ (a : c.O) (b : c₁.O), a.1 = b.1 → f (residue c.O a) = residue c₁.O b) → IsKa σ M ι n ka → (∀ g, (ka g).val ∈ c₁.O) →
    Nonempty (CReal k c₁ f n ka)

def DegEq : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ), Φ.V → Φ.d = Module.finrank ℚ (W.Lp L) ∧ ¬ ∃ ζ : L, IsPrimitiveRoot ζ l

def EveryPointSatisfiesFrameCondition : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O) (n : ℕ)
    (ka : G L Ω →* (Qbar l)ˣ) (R : CReal k c₁ f n ka) (y : W.Point R.r), y.N4

def FinPtDown : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (c c₁ : Coef l) (f : ResidueField c.O →+* ResidueField c₁.O), c.O ≤ c₁.O →
    (∀ (a : c.O) (b : c₁.O), a.1 = b.1 → f (residue c.O a) = residue c₁.O b) →
    ∀ (Φ : Fr.Frame l (ResidueField c.O)) (n : ℕ), FinPt c₁.O (Φ.ext f) n → FinPt c.O Φ n

def DimOf : Prop :=
  ∀ (O Λ B : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing Λ] [Algebra O Λ] [CommRing B]
    [IsNoetherianRing B] (φ : Λ →+* B) (J : Ideal B) (m : ℕ), Nonempty (Λ ≃ₐ[O] MvPowerSeries (Fin m) O) →
    ((Ideal.Quotient.mk J).comp φ).Finite → (∀ a : Λ, a ≠ 0 → ∀ b : B, φ a * b ∈ J → b ∈ J) →
    ∀ Z ∈ J.minimalPrimes, qdim Z = ((1 + m : ℕ) : WithBot ℕ∞)

end UpperTheory.V.Pr

end
end
