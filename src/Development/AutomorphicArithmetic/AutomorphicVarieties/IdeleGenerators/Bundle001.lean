module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.IsCondAt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.SlopeTestRemainingChoices
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CyclicBaseChangeC
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix

namespace UpperTheory.V.Sd

abbrev Pl (F : Type) [Field F] : Type := HeightOneSpectrum (𝓞 F)


open Classical in
def levL {F : Type} [Field F] (l : ℕ) (c : Pl F → ℕ) (w : Pl F) : ℕ := if ((l : ℕ) : 𝓞 F) ∈ w.asIdeal then 1 else c w


open Classical in
def eisT {F : Type} [Field F] [NumberField F] (l : ℕ) (ω : HChar F) (c : Pl F → ℕ) (P : Set (Pl F)) (w : Pl F) : ℂ :=
  if ((l : ℕ) : 𝓞 F) ∈ w.asIdeal then (if w ∈ P then ((ω.val w : ℂˣ) : ℂ) else 1) else if c w = 0 then 1 + ((ω.val w : ℂˣ) : ℂ) else 1

def ExpUnique : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (φ : GA F 2 → ℂ) (k : ℕ) c₀ c₀' a a', HasExp φ k c₀ a → HasExp φ k c₀' a' →
    c₀ = c₀' ∧ ∀ 𝔪, 𝔪 ≠ ⊥ → a 𝔪 = a' 𝔪

def StrongApp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (K : Subgroup (GL (Fin 2) (Af F))), IsOpen (K : Set (GL (Fin 2) (Af F))) →
    ∀ g : GA F 2, ∃ (γ : GL (Fin 2) F) (h : GL (Fin 2) (TR.Rinf F)) (y : (Af F)ˣ) (u : GL (Fin 2) (Af F)), u ∈ K ∧
      (∀ v, 0 < (h : Matrix (Fin 2) (Fin 2) (TR.Rinf F)).det v) ∧ g = ratGL F 2 γ * (TR.infGL F 2 h * finGL F 2 (aff y 0 * u))

def ExpInj : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ), 1 ≤ k → ∀ (c : Pl F → ℕ) (ω : HChar F), IsOfFinOrder ω →
    ∀ φ : TR.Sm F 2, IsHol k c ω φ → ∀ c₀ a, HasExp φ.1 k c₀ a → (∀ 𝔪, 𝔪 ≠ ⊥ → a 𝔪 = 0) → φ = 0

def HolLin : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (c : Pl F → ℕ) (ω : HChar F),
    IsHol k c ω 0 ∧ HasExp (0 : GA F 2 → ℂ) k 0 0 ∧
    (∀ (φ ψ : TR.Sm F 2) (z : ℂ), IsHol k c ω φ → IsHol k c ω ψ → IsHol k c ω (φ + z • ψ)) ∧
    (∀ (φ ψ : GA F 2 → ℂ) (z : ℂ) c₀ a d₀ b, HasExp φ k c₀ a → HasExp ψ k d₀ b → HasExp (φ + z • ψ) k (c₀ + z • d₀) (a + z • b)) ∧
    ∀ (φ : TR.Sm F 2) (c' : Pl F → ℕ), c ≤ c' → IsHol k c ω φ → IsHol k c' ω φ

def HolMul : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (k k' : ℕ) (c : Pl F → ℕ)
    (ω : HChar F), IsOfFinOrder ω → ∀ (φ ψ : TR.Sm F 2) a d₀ b, IsHol k c ω φ → IsHol k' (fun _ => 0) 1 ψ → HasExp φ.1 k 0 a →
    HasExp ψ.1 k' d₀ b → (∀ 𝔪, 𝔪 ≠ ⊥ → ‖ι.symm (a 𝔪)‖ ≤ 1) → (∀ y, ‖ι.symm (d₀ y) - 1‖ < 1) → (∀ 𝔪, 𝔪 ≠ ⊥ → ‖ι.symm (b 𝔪)‖ < 1) →
    ∃ (χ : TR.Sm F 2) (a' : Ideal (𝓞 F) → ℂ), IsHol (k + k') c ω χ ∧ HasExp χ.1 (k + k') 0 a' ∧
      ∀ 𝔪, 𝔪 ≠ ⊥ → ‖ι.symm (a' 𝔪 - a 𝔪)‖ < 1


open Classical in
def HolB : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (c : Pl F → ℕ) (ω : HChar F) (φ : TR.Sm F 2) c₀ a (w : Pl F),
    IsHol k c ω φ → HasExp φ.1 k c₀ a → ∃ (ψ : TR.Sm F 2) (u : (Af F)ˣ), IsHol k (Function.update c w (c w + 1)) ω ψ ∧
      HasExp ψ.1 k (fun y => c₀ (y * u)) (coefDiv a w.asIdeal)

def UopSum : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (w : Pl F) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V) (c : ℕ) (v : V), v ∈ Hi.fixd ρ (K1 w c) →
    Uop w ρ c v ∈ Hi.fixd ρ (K1 w c) ∧
    ∀ S : Finset (w.adicCompletionIntegers F), Set.BijOn (IsLocalRing.residue _) (S : Set (w.adicCompletionIntegers F)) Set.univ →
      Uop w ρ c v = ∑ u ∈ S, ρ (aff (atFin w (unif w)) (u : w.adicCompletion F)) v +
        if c = 0 then ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w)) * (aff (atFin w (unif w)) 0)⁻¹) v else 0

def HolHk : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ), 1 ≤ k → ∀ (c : Pl F → ℕ) (ω : HChar F), IsOfFinOrder ω →
    ∀ φ : TR.Sm F 2, IsHol k c ω φ → ∀ w : Pl F, IsHol k c ω (hk k w (c w) φ) ∧
      (∀ w' : Pl F, hk k w (c w) (hk k w' (c w') φ) = hk k w' (c w') (hk k w (c w) φ)) ∧
      ∀ c₀ a, HasExp φ.1 k c₀ a → ∃ c₀', HasExp (hk k w (c w) φ).1 k c₀' (hkCoef k c ω w a)

def HolCap : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (c : Pl F → ℕ) (ω : HChar F), IsOfFinOrder ω →
    ∀ φ : TR.Sm F 2, IsHol k c ω φ → TR.lie F 2 (TR.oneL F 2) φ = 0 ∧
      ∀ v (u : ℂ), TR.cap v u φ = ((u + ((k : ℂ) - 1) / 2) * (u - ((k : ℂ) - 1) / 2)) • φ

def HolFin : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (c : Pl F → ℕ), {w | c w ≠ 0}.Finite → ∀ ω : HChar F, IsOfFinOrder ω →
    FiniteDimensional ℂ (Submodule.span ℂ {φ : TR.Sm F 2 | IsHol k c ω φ})

def HolLift : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (k : ℕ), 1 ≤ k →
    ∀ (c : Pl F → ℕ), {w | c w ≠ 0}.Finite → ∀ ω : HChar F, IsOfFinOrder ω → ∀ (φ : TR.Sm F 2) c₀ a (t : Pl F → ℂ), IsHol k c ω φ →
    HasExp φ.1 k c₀ a → (∀ 𝔪, 𝔪 ≠ ⊥ → ‖ι.symm (a 𝔪)‖ ≤ 1) → ‖ι.symm (a ⊤)‖ = 1 → (∀ w, ‖ι.symm (t w)‖ ≤ 1) →
    (∀ w 𝔪, 𝔪 ≠ ⊥ → ‖ι.symm (hkCoef k c ω w a 𝔪 - t w * a 𝔪)‖ < 1) →
    ∃ ψ lam, IsEigHol k c ω ψ lam ∧ ∀ w, ‖ι.symm (lam w - t w)‖ < 1

def Emix : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ω : HChar F) (c : Pl F → ℕ),
    IsOfFinOrder ω → (∀ v, ω.locInf v (-1) = -1) → (∀ w, IsCondAt w ω (c w)) → (∃ w, c w ≠ 0) →
    (∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → c w = 0) → ∀ P : Set (Pl F), (∃ w ∈ P, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) →
    ∃ (φ : TR.Sm F 2) (a : Ideal (𝓞 F) → ℂ), IsHol 1 (levL l c) ω φ ∧ HasExp φ.1 1 0 a ∧ a ⊤ = 1 ∧
      (∀ 𝔪, 𝔪 ≠ ⊥ → ‖ι.symm (a 𝔪)‖ ≤ 1) ∧ ∀ w 𝔪, 𝔪 ≠ ⊥ → hkCoef 1 (levL l c) ω w a 𝔪 = eisT l ω c P w * a 𝔪

def LocEig : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (w : Pl F) (μ₁ μ₂ : (w.adicCompletion F)ˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (Φ : GL (Fin 2) (w.adicCompletion F) → V), Φ ≠ 0 →
    (∀ (a d : (w.adicCompletion F)ˣ) (x : w.adicCompletion F) g,
      Φ (Matrix.GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) x * g) = ((μ₁ a * μ₂ d : ℂˣ) : ℂ) • Φ g) →
    ∀ (c : ℕ) (lam : ℂ), Φ ∈ Hi.fixd (Hi.rtr ℂ _ V) (K1 w c) → Uop w (Hi.rtr ℂ _ V) c Φ = lam • Φ →
    (c = 0 → (∀ x, IsUnitAt w x → μ₁ x = 1 ∧ μ₂ x = 1) ∧
      lam = (normV w : ℂ) * (μ₁ (atFin w (unif w)) : ℂ) + (μ₂ (atFin w (unif w)) : ℂ)) ∧
    (c ≠ 0 → lam = 0 ∨ ((∀ x, IsUnitAt w x → μ₁ x = 1) ∧ lam = (normV w : ℂ) * (μ₁ (atFin w (unif w)) : ℂ)) ∨
      ((∀ x, IsUnitAt w x → μ₂ x = 1) ∧ lam = (μ₂ (atFin w (unif w)) : ℂ)))

def HolEis : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ), 1 ≤ k → ∀ (c : Pl F → ℕ), {w | c w ≠ 0}.Finite →
    ∀ ω : HChar F, IsOfFinOrder ω → ∀ φ lam, IsEigHol k c ω φ lam → ¬ TR.IsCuspForm φ →
    ∃ η₁ η₂ : HChar F, IsOfFinOrder η₁ ∧ IsOfFinOrder η₂ ∧ η₁ * η₂ = ω ∧
      (∀ w, c w = 0 → η₁.UnrAt w ∧ η₂.UnrAt w ∧ lam w = (η₁.val w : ℂˣ) + (η₂.val w : ℂˣ) * (normV w : ℂ) ^ (k - 1)) ∧
      ∀ w, c w ≠ 0 → lam w = 0 ∨ (η₁.UnrAt w ∧ lam w = (η₁.val w : ℂˣ)) ∨
        (η₂.UnrAt w ∧ lam w = (η₂.val w : ℂˣ) * (normV w : ℂ) ^ (k - 1))

def PropMHol : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (ω : HChar F)
    (c : Pl F → ℕ), IsOfFinOrder ω → (∀ v, ω.locInf v (-1) = -1) → (∀ w, IsCondAt w ω (c w)) → (∃ w, c w ≠ 0) →
    (∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → c w = 0) → ∀ P : Set (Pl F),
    (∃ w ∈ P, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ ¬ ‖ι.symm (ω.val w : ℂˣ) - 1‖ < 1) →
    (∃ w ∉ P, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ ¬ ‖ι.symm (ω.val w : ℂˣ) - 1‖ < 1) →
    ∀ B : ℕ, ∃ k ≥ B, l - 1 ∣ k ∧ ∃ φ lam, IsEigHol (k + 1) (levL l c) ω φ lam ∧ TR.IsCuspForm φ ∧
      ∀ w, ‖ι.symm (lam w - eisT l ω c P w)‖ < 1

def HolRep : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ), 2 ≤ k → ∀ (c : Pl F → ℕ) (ω : HChar F), IsOfFinOrder ω →
    ∀ φ lam, IsEigHol k c ω φ lam → TR.IsCuspForm φ → ∃ π : TR.CuspSub F 2, π.IsRegAlg ∧ (∃ χ : HChar F, π.Polarized χ) ∧
      (∀ v, π.HasInfChar v (infOf ![0, 1 - (k : ℤ)])) ∧ (∀ w, HasU w (π.locRep w) (c w) (lam w)) ∧
      ∀ w, c w = 0 → ∃ B, π.HasSat w B ∧ ((algSat 2 (normV w) B).map fun b => X - C b).prod =
        X ^ 2 - C (lam w) * X + C ((ω.val w : ℂˣ) * (normV w : ℂ) ^ (k - 1))

def PropM : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    ∀ (ι : Qbar l ≃+* ℂ) (ξ : _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ), IsOpen (ξ.ker : Set (_root_.Formalism.ConjugateSelfDual.G F Ω)) → (∀ c, IsConjEl c → ξ c = -1) →
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Ine (F := F) A ≤ ξ.ker) → (∃ A : ValuationSubring Ω, ¬ Ine (F := F) A ≤ ξ.ker) →
    ∀ P : Set (Pl F),
    (∃ w ∈ P, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ ∃ A, _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w ∧ ∃ σ ∈ _root_.ReciprocityTheory.Gal.Dec (F := F) A, ¬ Cong (ξ σ) 1) →
    (∃ w ∉ P, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ ∃ A, _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w ∧ ∃ σ ∈ _root_.ReciprocityTheory.Gal.Dec (F := F) A, ¬ Cong (ξ σ) 1) →
    ∀ B : ℕ, ∃ k ≥ B, l - 1 ∣ k ∧ ∃ c a π r, OrdForm ι ξ (-(k : ℤ)) c (fun _ => ![0, -(k : ℤ)]) a π r ∧ ResSum r ![1, ξ] ∧
      ∀ (w : Pl F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ A, _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w → ∀ σ : _root_.Formalism.ConjugateSelfDual.G F Ω, IsFrob A (normV w) σ →
        (w ∈ P → a w = (ξ σ⁻¹ : (Qbar l)ˣ)) ∧ (w ∉ P → a w = 1)

def SplitL (F : Type) [Field F] [NumberField F] (l : ℕ) : Prop :=
  ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → Ideal.absNorm w.asIdeal = l ∧ ((l : ℕ) : 𝓞 F) ∉ w.asIdeal ^ 2

def WeightChange : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    Even (Module.finrank ℚ F) → SplitL F l → ∀ (ι : Qbar l ≃+* ℂ) (ξ : _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ) s c m a π r, OrdForm ι ξ s c m a π r →
    (∃ u, c u ≠ 0 ∧ normV u = 2) → ∀ m' : Pl F → Fin 2 → ℤ,
    (∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → m' w 1 + 2 ≤ m' w 0 ∧ m' w 0 + m' w 1 = s ∧ ((l : ℤ) - 1) ∣ m' w 0 - m w 0) →
    ∃ π' r', OrdForm ι ξ s c m' a π' r' ∧ ∀ g i, ‖(r' g : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.coeff i -
      (r g : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.coeff i‖ < 1

def JacqOfU : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (w : Pl F) (σ : SmIrr (GL (Fin 2) (w.adicCompletion F))) (c : ℕ) (lam : ℂˣ), c ≠ 0 →
    HasU w σ.ρ c lam → ∃ (μ₁ μ₂ : (w.adicCompletion F)ˣ →* ℂˣ) (L : σ.V →ₗ[ℂ] ℂ), L ≠ 0 ∧ (∀ x, IsUnitAt w x → μ₁ x = 1) ∧
      (normV w : ℂ) * (μ₁ (atFin w (unif w)) : ℂ) = lam ∧ ∀ (a d : (w.adicCompletion F)ˣ) (x : w.adicCompletion F) v,
        L (σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) x) v) = ((μ₁ a * μ₂ d : ℂˣ) : ℂ) * L v

def OrdAway : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (ξ : _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ) s c m a π r, OrdForm ι ξ s c m a π r → TypeAway r ![1, ξ]

def OrdAbove : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    SplitL F l → ∀ (ι : Qbar l ≃+* ℂ) (ξ : _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ) s c m a π r, OrdForm ι ξ s c m a π r →
    ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ A, _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w →
      ∃ κ : Fin 2 → ↥(_root_.ReciprocityTheory.Gal.Dec (F := F) A) →* (Qbar l)ˣ, IsFlagOn r (_root_.ReciprocityTheory.Gal.Dec (F := F) A) κ ∧
        (∀ i (g : ↥(_root_.ReciprocityTheory.Gal.Dec (F := F) A)), (g : _root_.Formalism.ConjugateSelfDual.G F Ω) ∈ Ine (F := F) A → κ i g = cycBar F Ω l g ^ m w i) ∧
        ∀ σ : ↥(_root_.ReciprocityTheory.Gal.Dec (F := F) A), IsFrob A (normV w) (σ : _root_.Formalism.ConjugateSelfDual.G F Ω) →
          ‖((κ 0 σ⁻¹ * cycBar F Ω l (σ : _root_.Formalism.ConjugateSelfDual.G F Ω) ^ m w 0 : (Qbar l)ˣ) : Qbar l) - a w‖ < 1

def OrdIrr : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    SplitL F l → ∀ (ι : Qbar l ≃+* ℂ) (ξ : _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ) s c m a π r, OrdForm ι ξ s c m a π r → IsIrr r

def FinCoef : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] (n : ℕ)
    (r : Γ →* GL (Fin n) (Qbar l)), Continuous r → ∃ E : IntermediateField ℚ_[l] (Qbar l), FiniteDimensional ℚ_[l] E ∧
      ∀ g i j, r g i j ∈ E

end UpperTheory.V.Sd
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published
open scoped Matrix

namespace UpperTheory.V.Sd

def EigAut : Prop :=
  ∀ (k N : ℕ) [NeZero N], 2 ≤ k → ∀ χ : DirichletCharacter ℂ N, χ.IsPrimitive → ∀ (g : Eigenform k N χ) (l : ℕ) [Fact l.Prime]
    (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (ρ : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* GL (Fin 2) (Qbar l)), Continuous ρ → IsIrr ρ →
    (∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∀ A : ValuationSubring Ω, _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w →
      (∀ s ∈ Ine (F := ℚ) A, ρ s = 1) ∧ ∀ σ : _root_.Formalism.ConjugateSelfDual.G ℚ Ω, IsFrob A (normV w) σ →
        (ρ σ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.map ι.toRingHom =
          X ^ 2 - C (g.a (normV w)) * X + C (χ (normV w : ZMod N) * (normV w : ℂ) ^ (k - 1))) → IsAutR ι ρ

def DirOf : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (N : ℕ), 0 < N →
    ∀ φ : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* (Qbar l)ˣ, KillsMu N φ → ∃ (M : ℕ) (_ : NeZero M) (χ : DirichletCharacter ℂ M), M ∣ N ∧ χ.IsPrimitive ∧
      φ = Chr.dirG ℚ Ω (χ.ringHomComp ι.symm.toRingHom)

def PropEG : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (c : _root_.Formalism.ConjugateSelfDual.G ℚ Ω), IsCC c →
    ∀ (N w : ℕ) (φ θ : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* (Qbar l)ˣ), SlopeTestRemainingChoices N w θ → SplitAt N w φ → φ ≠ 1 → ∃ k₀ : ℕ, ∀ k ≥ k₀, φ c = (-1) ^ k →
      ∃ ρ, EisRep ι φ θ k ρ

def SIabs : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Γ : Type) [Group Γ] (ρ : Γ →* GL (Fin 2) (Qbar l)) (Φ : Γ →* (Qbar l)ˣ),
    (∀ s, ‖(Φ s : Qbar l)‖ = 1) → IsIrr ρ → ResSum ρ ![1, Φ] → ∀ H : Subgroup Γ, H.Normal →
    (∃ s ∈ H, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.Separable) → ¬ IsIrr (ρ.comp H.subtype) →
      (∀ s ∈ H, Cong (Φ s) 1) ∧ ∀ s, Cong (Φ s ^ 2) 1

def EisReg : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (φ θ : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* (Qbar l)ˣ)
    (k : ℕ), 2 ≤ k → ∀ ρ, EisRep ι φ θ k ρ → ∀ H : Subgroup (_root_.Formalism.ConjugateSelfDual.G ℚ Ω), IsOpen (H : Set (_root_.Formalism.ConjugateSelfDual.G ℚ Ω)) →
    ∃ s ∈ H, ∃ a : (Qbar l)ˣ, ¬ IsOfFinOrder a ∧
      (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly = (X - C (a : Qbar l)) * (X - C 1)

def SI : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ)
    (φ θ : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* (Qbar l)ˣ) (k : ℕ), 2 ≤ k → IsOfFinOrder φ → ∀ ρ, EisRep ι φ θ k ρ →
    (∀ H : Subgroup (_root_.Formalism.ConjugateSelfDual.G ℚ Ω), IsOpen (H : Set (_root_.Formalism.ConjugateSelfDual.G ℚ Ω)) → H.Normal →
      (∃ s ∈ H, ¬ Cong ((cycBar ℚ Ω l ^ (k - 1) * φ) s) 1) → IsIrr (ρ.comp H.subtype)) ∧
    ((∃ s, ¬ Cong ((cycBar ℚ Ω l ^ (k - 1) * φ) s ^ 2) 1) → IrrOpen ρ)

def Ad0Irr : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (ρ : Γ →* GL (Fin 2) (Qbar l)),
    Continuous ρ → IrrOpen ρ → IrrOpen (ad0 ρ)

def IrrAb : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (n : ℕ) (r : Γ →* GL (Fin n) (Qbar l)),
    Continuous r → IrrOpen r → ∀ H H' : Subgroup Γ, IsOpen (H : Set Γ) → H' ≤ H → (∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ * b⁻¹ ∈ H') →
      IsIrr (r.comp H'.subtype)

def Ad0Facts : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Γ →* GL (Fin 2) (Qbar l)),
    (Continuous ρ → Continuous (ad0 ρ)) ∧
    (∃ P : GL (Fin 3) (Qbar l), (P : Matrix (Fin 3) (Fin 3) (Qbar l))ᵀ = P ∧ ∀ s,
      (ad0 ρ s : Matrix (Fin 3) (Fin 3) (Qbar l))ᵀ * (P : Matrix (Fin 3) (Fin 3) (Qbar l)) * (ad0 ρ s : Matrix (Fin 3) (Fin 3) (Qbar l)) = P) ∧
    (∀ (H : Subgroup Γ) (a b : Γ →* (Qbar l)ˣ), IsDiagOn ρ H ![a, b] → IsDiagOn (ad0 ρ) H ![b / a, 1, a / b]) ∧
    (∀ (H : Subgroup Γ) (κ : Fin 2 → ↥H →* (Qbar l)ˣ), IsFlagOn ρ H κ → IsFlagOn (ad0 ρ) H ![κ 0 / κ 1, 1, κ 1 / κ 0]) ∧
    (∀ s (a b : (Qbar l)ˣ), (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly = (X - C (a : Qbar l)) * (X - C (b : Qbar l)) →
      (ad0 ρ s : Matrix (Fin 3) (Fin 3) (Qbar l)).charpoly =
        (X - C ((a / b : (Qbar l)ˣ) : Qbar l)) * (X - C 1) * (X - C ((b / a : (Qbar l)ˣ) : Qbar l))) ∧
    ∀ a b : Γ →* (Qbar l)ˣ, (∀ s, ‖(a s : Qbar l)‖ = 1 ∧ ‖(b s : Qbar l)‖ = 1) → ResSum ρ ![a, b] → ResSum (ad0 ρ) ![b / a, 1, a / b]

def ShapeFacts : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (n : ℕ) (r : Γ →* GL (Fin n) (Qbar l)) (δ : Γ →* (Qbar l)ˣ),
    (∀ (H : Subgroup Γ) (χ : Fin n → Γ →* (Qbar l)ˣ), IsDiagOn r H χ → IsDiagOn (tw r δ) H fun i => χ i * δ) ∧
    (∀ (H : Subgroup Γ) (χ χ' : Fin n → Γ →* (Qbar l)ˣ) (e : Equiv.Perm (Fin n)), IsDiagOn r H χ → (∀ i, ∀ s ∈ H, χ' i s = χ (e i) s) →
      IsDiagOn r H χ') ∧
    (∀ (H : Subgroup Γ) (κ : Fin n → ↥H →* (Qbar l)ˣ), IsFlagOn r H κ → IsFlagOn (tw r δ) H fun i => κ i * δ.comp H.subtype) ∧
    (∀ χ : Fin n → Γ →* (Qbar l)ˣ, (∀ s, ‖(δ s : Qbar l)‖ = 1) → ResSum r χ → ResSum (tw r δ) fun i => χ i * δ) ∧
    (∀ (χ χ' : Fin n → Γ →* (Qbar l)ˣ) (e : Equiv.Perm (Fin n)), (∀ i s, ‖(χ i s : Qbar l)‖ = 1) → ResSum r χ →
      (∀ i s, Cong (χ' i s) (χ (e i) s)) → ResSum r χ') ∧
    (IsIrr r → IsIrr (tw r δ))

def ResFacts : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω]
    [IsScalarTower F E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)),
    Continuous (galEmb F E Ω) ∧ IsOpen (galOf F E Ω : Set (_root_.Formalism.ConjugateSelfDual.G F Ω)) ∧ (cycBar F Ω l).comp (galEmb F E Ω) = cycBar E Ω l ∧
    (IsIrr (r.comp (galOf F E Ω).subtype) ↔ IsIrr (r.comp (galEmb F E Ω))) ∧
    (IrrOpen r → IrrOpen (r.comp (galEmb F E Ω))) ∧
    (∀ τ, TypeAway r τ → TypeAway (r.comp (galEmb F E Ω)) fun i => (τ i).comp (galEmb F E Ω)) ∧
    ∀ m ψ A, OrdAt r m ψ A → OrdAt (r.comp (galEmb F E Ω)) m (fun i => (ψ i).comp (galEmb F E Ω)) A

def SelfTwGal : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)) (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop), (∀ v B B', sat v B → sat v B' → B = B') →
    Continuous r → AttachedSys ι r sat → ∀ (η : HChar F) (m : ℕ), 0 < m → η ^ m = 1 → η ≠ 1 → SelfTw sat η →
    ∃ δ : _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ, δ ≠ 1 ∧ IsOpen (δ.ker : Set (_root_.Formalism.ConjugateSelfDual.G F Ω)) ∧ RepIso r (tw r δ) ∧
      ∀ (E : Type) [Field E] [NumberField E] [Algebra F E] [Algebra E Ω] [IsScalarTower F E Ω], IsNormChar E η →
        δ.comp (galEmb F E Ω) = 1

def UpQuad : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra F E]
    [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
    Module.finrank F E = 2 → ∀ (n : ℕ) [Fact (n = 2)], 1 ≤ n → ∀ r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l), Continuous r → IsAutR ι r →
      IsIrr (r.comp (galEmb F E Ω)) → IsAutC ι (r.comp (galEmb F E Ω))

def UpCyc : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra F E]
    [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] [IsGalois F E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
    (Module.finrank F E).Prime → ∀ (n : ℕ), 1 ≤ n → ∀ r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l), Continuous r → IsAutC ι r →
      IsIrr (r.comp (galEmb F E Ω)) → IsAutC ι (r.comp (galEmb F E Ω))

def UpSol : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra F E]
    [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] [IsGalois F E] [Group.IsSolvable (E ≃ₐ[F] E)] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l), Continuous r → IsAutC ι r →
      IsIrr (r.comp (galEmb F E Ω)) → IsAutC ι (r.comp (galEmb F E Ω))

def TwC : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)) (κ : _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ), IsAlgChar ι κ → IsAutC ι r → IsAutC ι (tw r κ)

def TwR : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)) (κ : _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ), IsAlgChar ι κ → IsAutR ι r → IsAutR ι (tw r κ)

def AlgCyc : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
    (∀ (j : ℤ) (χ : _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ), IsOpen (χ.ker : Set (_root_.Formalism.ConjugateSelfDual.G F Ω)) → IsAlgChar ι (cycBar F Ω l ^ j * χ)) ∧
    (∀ κ κ' : _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ, IsAlgChar ι κ → IsAlgChar ι κ' → IsAlgChar ι (κ * κ')) ∧
    ∀ κ : _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ, IsAlgChar ι κ → IsAlgChar ι κ⁻¹

def AlgRes : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω]
    [IsScalarTower F E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (κ : _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ),
    IsAlgChar ι κ → IsAlgChar ι (κ.comp (galEmb F E Ω))

def Twist : Prop :=
  ∀ (K Ω : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω],
    Module.finrank ℚ K = 2 → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ (l : ℤ) ∣ discr K → ∀ (ι : Qbar l ≃+* ℂ) (c : _root_.Formalism.ConjugateSelfDual.G ℚ Ω), IsCC c →
    ∃ κ : _root_.Formalism.ConjugateSelfDual.G K Ω →* (Qbar l)ˣ, IsTwist ι c κ

def RibetLat : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ]
    (ρ : Γ →* GL (Fin 2) (Qbar l)) (a b : Γ →* (Qbar l)ˣ), Continuous ρ → IsIrr ρ → (∀ s, ‖(a s : Qbar l)‖ = 1 ∧ ‖(b s : Qbar l)‖ = 1) →
    ResSum ρ ![a, b] → ∀ g₀ : Γ, ¬ Cong (a g₀) (b g₀) → ∃ ρ' : Γ →* GL (Fin 2) (Qbar l), RepIso ρ ρ' ∧
      ρ' g₀ 0 1 = 0 ∧ ρ' g₀ 1 0 = 0 ∧ (∀ s, ‖ρ' s 0 0 - a s‖ < 1 ∧ ‖ρ' s 1 1 - b s‖ < 1 ∧ ‖ρ' s 1 0‖ < 1 ∧ ‖ρ' s 0 1‖ ≤ 1) ∧
      ∃ s, ‖ρ' s 0 1‖ = 1

end UpperTheory.V.Sd
end
end
