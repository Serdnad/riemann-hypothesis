module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle003
public import Mathlib.RingTheory.Ideal.Height
import Mathlib.Algebra.AffineMonoid.Basic
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module GlobalTheory.CompanionTheory.Ar.BT

abbrev LevGrp (La : Type) [AddCommGroup La] (p n : ℕ) : Type :=
  Multiplicative (La ⧸ LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La)))

def lev {La : Type} [AddCommGroup La] (p n : ℕ) (a : La) : LevGrp La p n :=
  Multiplicative.ofAdd (Submodule.Quotient.mk a)

structure OrdTower (p : ℕ) (O : Type) [CommRing O] (La : Type) [AddCommGroup La]
    (L : Type) [AddCommGroup L] [Module O L] where

  A : ∀ n, Subalgebra O (LevGrp La p n → O)
  hopf : ∀ n, IsHopfOrder (A n)
  res_iff : ∀ n (g : LevGrp La p n → O),
    g ∈ A n ↔ ∃ f ∈ A (n + 1), ∀ a : La, g (lev p n a) = f (lev p (n + 1) (p • a))
  ker_res : ∀ n (f : A (n + 1)), (∀ a : La, f.1 (lev p (n + 1) (p • a)) = 0) →
    f ∈ Ideal.span {g : A (n + 1) | ∃ h ∈ A (n + 1), ∀ t, g.1 t = h (t ^ p ^ n) - h 1}

  der : ∀ n, (LevGrp La p n → O) → Module.Dual O L → Prop
  der_ex : ∀ n, ∀ f ∈ A n, ∃ w, der n f w
  der_unique : ∀ n f w w', der n f w → (der n f w' ↔ ∃ u : Module.Dual O L, w' = w + (p ^ n) • u)
  der_onto : ∀ n w, ∃ f ∈ A n, der n f w
  der_add : ∀ n f g w w', der n f w → der n g w' → der n (f + g) (w + w')
  der_mul : ∀ n f g w w', der n f w → der n g w' → der n (f * g) (f 1 • w' + g 1 • w)
  der_const : ∀ n (r : O), der n (fun _ => r) 0
  der_zero : ∀ n (f : augIdeal (A n)), der n f.1.1 0 → (f : A n) ∈ augIdeal (A n) ^ 2
  der_res : ∀ n f g w, der (n + 1) f w → (∀ a : La, g (lev p n a) = f (lev p (n + 1) (p • a))) → der n g w

namespace OrdTower

variable {p : ℕ} {O : Type} [CommRing O] {La : Type} [AddCommGroup La]
  {L : Type} [AddCommGroup L] [Module O L] (X : OrdTower p O La L)

def Acts (φ : La →+ La) (dφ : L →ₗ[O] L) : Prop :=
  ∀ n (f g : LevGrp La p n → O), (∀ a, g (lev p n a) = f (lev p n (φ a))) →
    (f ∈ X.A n → g ∈ X.A n) ∧ ∀ w, X.der n f w → X.der n g (w ∘ₗ dφ)

def PairingExtends (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ) : Prop :=
  ∀ n, ∃ s ∈ prodSpan (X.A n), ∀ a b, s (lev p n a, lev p n b) = ((ζ n ^ B a b : Oˣ) : O)

structure Realises [Fact p.Prime] (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate) : Prop where
  res : ∀ n (f : G.A (n + 1)) (a : La), (e n (G.res n f)).1 (lev p n a) = (e (n + 1) f).1 (lev p (n + 1) (p • a))
  pt : ∀ (a : La) n (f : G.A n), (τ a).pt n f = (e n f).1 (lev p n a)

end OrdTower

end GlobalTheory.CompanionTheory.Ar.HT
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

structure HTChart (A K : Type) [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
    (c : E ≃+* E) (p R N : ℕ)
    (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] where

  om : Submodule A Ω
  om_lat : om.IsFullLattice K
  om_proj : Module.Projective A om

  ρΩ : 𝓞 E →+* Module.End K Ω
  om_stable : ∀ (a : 𝓞 E), ∀ x ∈ om, ρΩ a x ∈ om

  e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ R)
  alt : ∀ x, e x x = 0
  adj : ∀ (a : 𝓞 E) (x y : Fin N → 𝓞 E), e (a • x) y = e x (RingOfIntegers.mapRingEquiv c a • y)
  e_surj : ∀ φ : (Fin N → 𝓞 E) →+ ZMod (p ^ R), ∃ x, e x = φ
  e_inj : ∀ x, e x = 0 → ∃ x', x = (p ^ R) • x'

  h : (Fin N → 𝓞 E) →+ Ω
  h_mem : ∀ x, h x ∈ om
  h_lin : ∀ (a : 𝓞 E) (x : Fin N → 𝓞 E), ∃ y ∈ om, h (a • x) = ρΩ a (h x) + (p ^ R) • y

namespace HTChart

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  (D : HTChart A K c p R N Ω)

def om' : Submodule A Ω :=
  Submodule.span A (Set.range D.h) ⊔ D.om.map (((p : A) ^ R) • LinearMap.id)

def omHT (σ : E →+* K) : Submodule A Ω := eigQuot D.ρΩ σ D.om'

def q (σ : E →+* K) (x : Fin N → A) : Ω := ∑ i, x i • eigProj D.ρΩ σ (D.h (Pi.single i 1))

def gram (σ : E →+* K) (d : A) (i j : Fin N) : K :=
  ∑ k, algebraMap A K d * σ (dualInt E k) *
    ((D.e (Pi.single i (RingOfIntegers.basis E k)) (Pi.single j 1)).val : K)

def IsDualMap (σ : E →+* K) (d : A) (m : ℕ)
    (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)) : Prop :=
  ∀ (w : Module.Dual A (D.omHT (σ.comp c.toRingHom))) (j : Fin N)
    (y : D.omHT (σ.comp c.toRingHom)),
    (y : Ω) = eigProj D.ρΩ (σ.comp c.toRingHom) (D.h (Pi.single j 1)) →
      ∃ z : A, ∑ l, algebraMap A K (i w l) * D.gram σ d l j = algebraMap A K (w y + (p : A) ^ m * z)

def ExactMod (σ : E →+* K) (m : ℕ)
    (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)) : Prop :=
  (∃ r : (Fin N → A) →ₗ[A] Module.Dual A (D.omHT (σ.comp c.toRingHom)),
    ∀ w, ∃ w', r (i w) = w + ((p : A) ^ m) • w') ∧
  (∀ x : Fin N → A, (∃ y ∈ D.omHT σ, D.q σ x = ((p : A) ^ m) • y) ↔
    ∃ w, ∃ x' : Fin N → A, x = i w + ((p : A) ^ m) • x') ∧
  ∀ y ∈ D.omHT σ, ∃ x : Fin N → A, ∃ y' ∈ D.omHT σ, y = D.q σ x + ((p : A) ^ m) • y'

structure ReducesTo {C O : Type} [Field C] [CommRing O] [Algebra O C] {κ : O}
    {V Ω' : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
    [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω']
    (φ : A →+* O) (P : HTPoint C O c κ N V Ω') (ι : D.om →ₛₗ[φ] Ω') : Prop where
  span_eq : Submodule.span O (Set.range ι) = P.om
  rank_eq : Module.finrank K Ω = Module.finrank C Ω'
  lin : ∀ (a : 𝓞 E) (x : D.om), ι ⟨D.ρΩ a x, D.om_stable a x x.2⟩ = P.ρΩ a (ι x)
  ht_eq : ∀ x, ∃ y ∈ P.om, ι ⟨D.h x, D.h_mem x⟩ = P.ht (P.tate x) + (p ^ R) • y
  e_eq : ∀ x y, ∃ z : O, P.e (P.tate x) (P.tate y) =
    algebraMap O C (((D.e x y).val : O) + (p : O) ^ R * z)

def HasTestPoints (κ : A) : Prop :=
  ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → (p : A) ∈ 𝔮 →
    ∃ (C O : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : CharZero C) (_ : CommRing O) (_ : Algebra O C)
      (v : Valuation C NNReal) (φ : A →+* O)
      (V Ω' : Type) (_ : AddCommGroup V) (_ : Module C V) (_ : Module O V) (_ : IsScalarTower O C V)
      (_ : AddCommGroup Ω') (_ : Module C Ω') (_ : Module O Ω') (_ : IsScalarTower O C Ω')
      (P : HTPoint C O c (φ κ) N V Ω') (ι : D.om →ₛₗ[φ] Ω'),
      v.Integers O ∧ Function.Injective φ ∧ (∀ a, a ∈ 𝔮 ↔ v (algebraMap O C (φ a)) < 1) ∧
        D.ReducesTo φ P ι

end HTChart

def GeneratesDiff {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E]
    [NumberField E] (σ : E →+* K) (d : A) : Prop :=
  Submodule.span A {algebraMap A K d} =
    Submodule.span A {y : K | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)}

end GlobalTheory.CompanionTheory.Ar.HT
end
end

section

namespace GlobalTheory.CompanionTheory.Ar.Num

open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

variable (o : Type*) [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω V₁]
  [AddCommGroup V₂] [Module Ω V₂]

def IsLatFamily (x : (Σ k, ι k) → Ω) (Γ : (∀ k, ι k) → AddSubgroup V) : Prop :=
  (∀ s, mseg x s ≠ 0 → ∀ a ∈ chartRing o (mseg x) s, ∀ v ∈ Γ s, a • v ∈ Γ s) ∧
  ∀ s t, mseg x s ≠ 0 → mseg x t ≠ 0 → ∀ v ∈ Γ s, ∃ m : ℕ, (mseg x s / mseg x t) ^ m • v ∈ Γ t

def IsQuotHom (x : (Σ k, ι k) → Ω) (A A' : (∀ k, ι k) → AddSubgroup V)
    (B B' : (∀ k, ι k) → AddSubgroup V₁) (Γ : (∀ k, ι k) → AddSubgroup (V × V₁)) : Prop :=
  IsLatFamily o x Γ ∧ ∀ s, mseg x s ≠ 0 →
    (∀ v w, (v, w) ∈ Γ s → v ∈ A s ∧ w ∈ B s) ∧ (∀ v ∈ A s, ∃ w, (v, w) ∈ Γ s) ∧
    (∀ w, (0, w) ∈ Γ s ↔ w ∈ B' s) ∧ (∀ v ∈ A' s, (v, 0) ∈ Γ s)

def QuotEquiv (x : (Σ k, ι k) → Ω) (A A' : (∀ k, ι k) → AddSubgroup V)
    (B B' : (∀ k, ι k) → AddSubgroup V₁) : Prop :=
  ∃ Γ, IsQuotHom o x A A' B B' Γ ∧ ∀ s, mseg x s ≠ 0 →
    (∀ v, (v, 0) ∈ Γ s → v ∈ A' s) ∧ (∀ w ∈ B s, ∃ v, (v, w) ∈ Γ s)

def QuotExact (x : (Σ k, ι k) → Ω) (A A' : (∀ k, ι k) → AddSubgroup V)
    (B B' : (∀ k, ι k) → AddSubgroup V₁) (C C' : (∀ k, ι k) → AddSubgroup V₂) : Prop :=
  ∃ Γ Δ, IsQuotHom o x A A' B B' Γ ∧ IsQuotHom o x B B' C C' Δ ∧ ∀ s, mseg x s ≠ 0 →
    (∀ v, (v, 0) ∈ Γ s → v ∈ A' s) ∧ (∀ c ∈ C s, ∃ b, (b, c) ∈ Δ s) ∧
    (∀ b, (b, 0) ∈ Δ s ↔ ∃ a, (a, b) ∈ Γ s)

def IsScaled (x : (Σ k, ι k) → Ω) (c : Ω) (A A' : (∀ k, ι k) → AddSubgroup V) : Prop :=
  ∀ s, mseg x s ≠ 0 → ∀ v, v ∈ A' s ↔ ∃ e ∈ A s, v = c • e

def IsLine (x : (Σ k, ι k) → Ω) (u : Ω) (a : K → ℤ) (A : (∀ k, ι k) → AddSubgroup Ω) : Prop :=
  ∀ s, mseg x s ≠ 0 → ∀ v, v ∈ A s ↔ ∃ r ∈ chartRing o (mseg x) s, v = r * (u * chartMon x s a)

def IsDualLat (x : (Σ k, ι k) → Ω) (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω) (A : (∀ k, ι k) → AddSubgroup V)
    (B : (∀ k, ι k) → AddSubgroup V₁) : Prop :=
  Function.Bijective β.flip ∧
    ∀ s, mseg x s ≠ 0 → ∀ w, w ∈ B s ↔ ∀ v ∈ A s, β v w ∈ chartRing o (mseg x) s

def TrivFlagMod (ϖ : o) (x : (Σ k, ι k) → Ω) (N : ℕ) (b : Fin N → K → ℤ) : Prop :=
  ∃ g : (∀ k, ι k) → Matrix (Fin N) (Fin N) Ω,
    (∀ s, mseg x s ≠ 0 → (∀ i j, g s i j ∈ chartRing o (mseg x) s) ∧
      ∃ h ∈ chartRing o (mseg x) s, ∃ r ∈ chartRing o (mseg x) s,
        (g s).det * h = 1 + algebraMap o Ω ϖ * r) ∧
    ∀ s t, mseg x s ≠ 0 → mseg x t ≠ 0 → ∃ (m : ℕ) (U Z : Matrix (Fin N) (Fin N) Ω),
      (∀ i j, U i j ∈ chartRing o (mseg x) t) ∧ (∀ i j, Z i j ∈ chartRing o (mseg x) t) ∧
      (∀ i j, j < i → U i j = 0) ∧
      (∀ i, U i i = (mseg x s / mseg x t) ^ m * (chartMon x s (b i) / chartMon x t (b i))) ∧
      (∀ i j, (mseg x s / mseg x t) ^ m * g s i j ∈ chartRing o (mseg x) t) ∧
      (mseg x s / mseg x t) ^ m • g s = g t * U + algebraMap o Ω ϖ • Z

end GlobalTheory.CompanionTheory.Ar.Num
end
