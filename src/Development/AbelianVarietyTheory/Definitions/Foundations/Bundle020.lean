module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle017
public import Development.AbelianVarietyTheory.Definitions.Foundations.CycMOfNot
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsPrimitiveRootTopZeta
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Mathlib.GroupTheory.Nilpotent
public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagSingleSingle
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle275
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle256
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.GroupWithZero.Torsion
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle018
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle019
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsEqSubOfMemCob
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 PowerSeries

namespace GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def htv (j : Ω →+* Qbar l) (ζ : Ω) {ι : Type} [Fintype ι] (P : ι → Polynomial Ω) (o : ι → Qbar l) (b : ℕ) : Qbar l :=
  ∑ i, o i * j (ζ ^ b * (Polynomial.derivative (P i)).eval (ζ ^ b) / (P i).eval (ζ ^ b))

def HTPres (A : ValuationSubring Ω) (c : Coef l) (m : ℕ) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (ζ : Ω) {ι : Type}
    [Fintype ι] (P : ι → Polynomial Ω) (o : ι → Qbar l) : Prop :=
  IsPrimitiveRoot ζ (l ^ m) ∧ (∀ i, ∀ x ∈ (P i).coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) ∧ (∀ i, o i ∈ c.O) ∧
    GlobalTheory.Col.KumPres A m m ζ (Z m) (fun i => (P i).eval ζ) o

def tval (L : PowerSeries (Qbar l)) (N : ℕ) (z : Qbar l) : Qbar l := ∑ n ∈ Finset.range N, L.coeff n * (z - 1) ^ n

def mass (L : PowerSeries (Qbar l)) (r : ℕ) (ξ : Qbar l) (x : ℕ) : Qbar l :=
  ∑ k ∈ Finset.range (l ^ r), ξ ^ (l ^ r - (k * x) % l ^ r) * tval L (l ^ (3 * r)) (ξ ^ k)

def HTLawAt (A : ValuationSubring Ω) (c : Coef l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (j : Ω →+* Qbar l)
    (m₀ c₀ : ℕ) (Rhs : ∀ m : ℕ, DirichletCharacter (Qbar l) (l ^ m) → Qbar l → Qbar l) : Prop :=
  ∀ m, m₀ ≤ m → ∃ (ζ : Ω) (ι : Type) (_ : Fintype ι) (P : ι → Polynomial Ω) (o : ι → Qbar l), HTPres A c m Z ζ P o ∧
    ∀ ψ : DirichletCharacter (Qbar l) (l ^ m), ψ.IsPrimitive →
      Cg (m - c₀) (∑ b : (ZMod (l ^ m))ˣ, ψ b * htv j ζ P o (b : ZMod (l ^ m)).val) (Rhs m ψ (j ζ))

def Pin (e : ℕ) (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l) (ν : G ℚ Ω →* (Qbar l)ˣ)
    (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) : Prop :=
  ∃ (a a' κ : Qbar l) (v : ℕ → Qbar l) (j : Ω →+* Qbar l) (Rhs : ∀ m : ℕ, DirichletCharacter (Qbar l) (l ^ m) → Qbar l → Qbar l)
    (L : PowerSeries (Qbar l)) (φ : DirichletCharacter (Qbar l) l) (m₀ c₀ n₀ : ℕ),
    (∀ s ∈ Ine (F := ℚ) A, ν s = 1) ∧ (∃ σ ∈ Dec (F := ℚ) A, IsFrob A l σ ∧ (ν σ : Qbar l) = a) ∧
    ‖a‖ = 1 ∧ ‖a'‖ = 1 ∧ (∀ m, ‖v m‖ = 1 ∧ Cg m (v (m + 1)) (v m)) ∧ κ ≠ 0 ∧ (∀ x ∈ A, ‖j x‖ ≤ 1) ∧
    (∀ n, L.coeff n ∈ c.O) ∧ HTLawAt A c Z j m₀ c₀ Rhs ∧
    (∀ m, m₀ ≤ m → ∀ ψ : DirichletCharacter (Qbar l) (l ^ m), ψ.IsPrimitive → ∀ z : Qbar l, IsPrimitiveRoot z (l ^ m) →
      Cg (m - c₀) (Rhs m ψ z) (v m * κ * a' ^ m * ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval L (l ^ (3 * m)) (z ^ (b : ZMod (l ^ m)).val))) ∧
    ∀ r, 1 ≤ r → ∀ ξ : Qbar l, IsPrimitiveRoot ξ (l ^ r) →
      ¬ Cg (n₀ + r) (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x),
          φ (x : ZMod l) * ((x : Qbar l) ^ e) * mass L r ξ x) 0

end GlobalTheory.KZ
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.LambdaValuationPowers

namespace GlobalTheory.KummerEisensteinGalois

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} {l : ℕ} [Fact l.Prime]

def InChi (X : Tower Ω ε) (N w : ℕ) (χ : ℕ → ℤ_[l]) (b : X.Fn l) : Prop :=
  b ∈ X.B N l w ∧ ∀ d : ℕ, Nat.Coprime d N → X.diam N l d b = χ d • b

def IsLamFR (X : Tower Ω ε) (A : ValuationSubring Ω) (N w : ℕ) (χ : ℕ → ℤ_[l]) (j : Ω →+* Qbar l)
    (pr : X.Fn l → Fin 2 → Qbar l) (c : Coef l) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) : Prop :=
  FinSupp lam ∧ (∀ i : ℕ, FixIc c (lam (Pi.single i 1))) ∧
    ∃ (cL : ℕ) (per : ℕ → Qbar l), (∀ n, ‖per n‖ = 1 ∧ Cg n (per (n + 1)) (per n) ∧ FixIc c (per n)) ∧
      ∀ (n : ℕ), cL ≤ n → ∀ (b : X.Fn l), InChi X N w χ b → ∀ φ : HahnSeries ℚ Ω, IsThB X A N l n b φ →
        Cg (n - cL) (lam (seqN 1 j φ)) (per n * pr b 1)

section Induced

variable {X : Tower Ω ε} {A : ValuationSubring Ω} {N w : ℕ} {χ : ℕ → ℤ_[l]} {j : Ω →+* Qbar l}
  {pr : X.Fn l → Fin 2 → Qbar l} {c : Coef l} {lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l}

end Induced

end GlobalTheory.KummerEisensteinGalois

end
end

section

noncomputable section

open scoped MatrixGroups Matrix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV

namespace GlobalTheory.K4

open GlobalTheory.KZ GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def thK (l : ℕ) [Fact l.Prime] (e : ℕ) (ψ : ZMod l → Qbar l) (s : G ℚ Ω) : Qbar l :=
  (eps l s ^ e)⁻¹ * ψ ((((cycMod (F := ℚ) (Ω := Ω) l 1 s : ZMod (l ^ 1))).val : ℕ) : ZMod l)

def rhoK {l : ℕ} [Fact l.Prime] (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l) (s : G ℚ Ω) : Matrix (Fin 2) (Fin 2) (Qbar l) :=
  (thK l e ψ s)⁻¹ • mat W s


open Classical in
def nuD {l : ℕ} [Fact l.Prime] (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l) (s : G ℚ Ω) : (Qbar l)ˣ :=
  if h : rhoK W e ψ s 1 1 ≠ 0 then Units.mk0 _ h else 1

def Adm3 {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e : ℕ) (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l)
    (X : Tower Ω ε) (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ))
    (ψ : ZMod l → Qbar l) (cf : Coef l) : Prop :=
  1 < c ∧ 1 < d ∧ Nat.Coprime c (6 * l * N) ∧ Nat.Coprime d (6 * l * N) ∧ IsUnit x ∧
    (∀ b b', pr (b + b') = pr b + pr b') ∧
    (∀ (a : ℤ_[l]) b, pr (a • b) = algebraMap ℚ_[l] (Qbar l) (a : ℚ_[l]) • pr b) ∧
    (∀ b ∈ X.B N l (2 * e - 1), ∀ i, pr b i ∈ cf.O) ∧
    (∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l (2 * e - 1) → pr (X.galB l s b) = rhoK W e ψ s *ᵥ pr b) ∧
    (∃ δ : ℕ → Qbar l, ∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ∀ b, b ∈ X.B N l (2 * e - 1) →
      pr (X.heckeT N l q b) = ι.symm (gN.a q) • pr b ∧ pr (X.diam N l q b) = δ q • pr b) ∧
    (∀ r₀ : (ZMod l)ˣ, ∃ t : (ZMod l)ˣ,
      (![0, 1] : Fin 2 → ZMod l) ᵥ* ((gm r₀ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod l))) =
        (t : ZMod l) • ![(r₀ : ZMod l), -1]) ∧
    (∀ r₀ : (ZMod l)ˣ, (N : ℤ) ∣ (gm r₀ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) ∧
    ∃ χ : G ℚ Ω →* (Qbar l)ˣ, KillsMu l χ ∧
      (∀ s ∈ Ine (F := ℚ) A, mat W s 1 1 * (cycBar ℚ Ω l s : Qbar l) ^ (e : ℤ) * ((dt W s : Qbar l)⁻¹ * (χ s : Qbar l)) = 1) ∧
      ∀ s : G ℚ Ω, (χ s : Qbar l) = ψ ((((cycMod (F := ℚ) (Ω := Ω) l 1 s : ZMod (l ^ 1))).val : ℕ) : ZMod l)

def LiftB (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w n c0 : ℕ) (a b : X.Fn l) : Prop :=
  b ∈ X.B N l w ∧ ∀ u, AdicCompletion.eval (idl l) (X.Kl l) n (b u - ((l : ℤ_[l]) ^ c0) • a u) = 0

def YfB (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l) (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l)
    (n r N : ℕ) [NeZero N] (bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l) : (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l :=
  GlobalTheory.KA.push (redM l n r (N * N)) fun s y =>
    rhoK W e ψ (repM (topM l n r (N * N)) y) *ᵥ
      pr (bB ((repM (topM l n r (N * N)) y)⁻¹ * s * repM (topM l n r (N * N)) (y * (cycM (topM l n r (N * N)) s)⁻¹)))

attribute [local instance] algMdl

def topMu (l n r N : ℕ) : ℕ := l ^ (r + n) * (N * N)

def wkMu (X : Tower Ω ε) (l n r N : ℕ) (x : ZMod N) (c d : ℕ) (σ : Ω ≃ₐ[ℚ] Ω) : X.K :=
  let M := topMu l n r N
  let tt : ℤ := (topT l (r + n) N : ℤ)
  let u : X.K := GlobalTheory.Glue.sgN X c N (N * l ^ (r + n)) ((N : ℤ) + (x.val : ℤ) * tt * (l : ℤ) ^ (r + n), 0)
  let v : X.K := GlobalTheory.Glue.sgN X d N (N * l ^ (r + n)) (tt * (l : ℤ) ^ (r + n), (N : ℤ))
  ((topW (K := topL X M) (topZeta X M l n) (topChar X M l n u) (topChar X M l n v)
    (topEta X M (topChar X M l n u) (topChar X M l n v)) (topLift X M σ)⁻¹ : topL X M) : X.K)


open Classical in
def clsBmu (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n r N : ℕ) [NeZero N] (x : ZMod N) (c d k : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ))
    (σ : Ω ≃ₐ[ℚ] Ω) : X.Fn l :=
  let M : ℕ := topMu l n r N
  haveI : NeZero M := ⟨Nat.mul_ne_zero (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) (Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne N))⟩
  let f : X.Fn l := fun u => (u 0) ^ (k - 2) • clsK X l n (wkMu X l n r N x c d σ)
  ∑ r₀ : (ZMod l)ˣ, ∑ γ ∈ Finset.univ.filter (fun γ : SL(2, ZMod M) =>
      γ ∈ (Gam N l).map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)))),
    X.act l ((g r₀ * liftSL M γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) f

def topMT (l n r N l' : ℕ) : ℕ := l ^ (r + n) * (N * N) * l'

instance topMT.neZero (l n r N l' : ℕ) [Fact l.Prime] [NeZero N] [NeZero l'] : NeZero (topMT l n r N l') :=
  ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) (Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne N)))
    (NeZero.ne l')⟩

def wkTmu (X : Tower Ω ε) (l n r N l' : ℕ) (x : ZMod N) (c d : ℕ) (σ : Ω ≃ₐ[ℚ] Ω) : X.K :=
  let M := topMT l n r N l'
  let L : ℤ := (l : ℤ) ^ (r + n)
  let lb : ℤ := ((((l' : ZMod (N * l ^ (r + n)))⁻¹).val : ℕ) : ℤ)
  let tt : ℤ := (topT l (r + n) N : ℤ)
  let u : X.K := GlobalTheory.Glue.sgN X c N (N * l ^ (r + n) * l') (lb * ((N : ℤ) + (x.val : ℤ) * tt * L) * l' + N * L, 0)
  let v : X.K := GlobalTheory.Glue.sgN X d N (N * l ^ (r + n) * l') (lb * tt * L * l', lb * N * l' + N * L)
  ((topW (K := topL X M) (topZeta X M l n) (topChar X M l n u) (topChar X M l n v)
    (topEta X M (topChar X M l n u) (topChar X M l n v)) (topLift X M σ)⁻¹ : topL X M) : X.K)


open Classical in
def clsBTmu (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n r N l' : ℕ) [NeZero N] [NeZero l'] (x : ZMod N) (c d k : ℕ)
    (g : (ZMod l)ˣ → SL(2, ℤ)) (σ : Ω ≃ₐ[ℚ] Ω) : X.Fn l :=
  let M : ℕ := topMT l n r N l'
  let f : X.Fn l := fun u => (u 0) ^ (k - 2) • clsK X l n (wkTmu X l n r N l' x c d σ)
  ∑ r₀ : (ZMod l)ˣ, ∑ γ ∈ Finset.univ.filter (fun γ : SL(2, ZMod M) =>
      γ ∈ (Gam N l).map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)))),
    X.act l ((g r₀ * liftSL M γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) f

def redT (l n r N l' : ℕ) (y : (ZMod (topMT l n r N l'))ˣ) : (ZMod l')ˣ × (ZMod (l ^ r))ˣ :=
  (Units.map (ZMod.castHom (Dvd.intro_left _ rfl : l' ∣ topMT l n r N l') (ZMod l')).toMonoidHom y,
   Units.map (ZMod.castHom ((Dvd.dvd.mul_right (pow_dvd_pow l (Nat.le_add_right r n)) (N * N)).mul_right l')
     (ZMod (l ^ r))).toMonoidHom y)

def YfBT (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l) (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l)
    (n r N l' : ℕ) [NeZero N] [NeZero l'] (bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l) : (Ω ≃ₐ[ℚ] Ω) → (ZMod l')ˣ × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l :=
  GlobalTheory.KA.push (redT l n r N l') fun s y =>
    rhoK W e ψ (repM (topMT l n r N l') y) *ᵥ
      pr (bB ((repM (topMT l n r N l') y)⁻¹ * s * repM (topMT l n r N l') (y * (cycM (topMT l n r N l') s)⁻¹)))

def cycT (l r l' : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) : (ZMod l')ˣ × (ZMod (l ^ r))ˣ :=
  ((cycM l' s)⁻¹, (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹)


open Classical in
def lsqInv (l l' r : ℕ) : (ZMod l')ˣ :=
  if h : IsUnit ((l : ZMod l') ^ (2 * r)) then h.unit⁻¹ else 1

end GlobalTheory.K4
end
end

section

noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace Pre

variable (B : Pre)

theorem level_split_E : ∀ p ∈ B.host.levelPrimes, (placesOver B.host.E p).ncard = Module.finrank ℚ B.host.E := fun p hp =>
  (GlobalTheory.HostSplit.split_of_one_mod B.R B.host p (B.level_cond p hp).1 (B.level_cond p hp).2).1

theorem g_split : ∀ k, (placesOver B.host.E (B.host.g k)).ncard = Module.finrank ℚ B.host.E := fun k => B.level_split_E _ (B.host.g_level k)

theorem pde_split :
    (Ideal.primesOver (Ideal.span {(B.host.pde : ℤ)}) (𝓞 B.host.E)).ncard = Module.finrank ℚ B.host.E ∧
    (Ideal.primesOver (Ideal.span {(B.host.pde' : ℤ)}) (𝓞 B.host.E)).ncard = Module.finrank ℚ B.host.E := by
  constructor
  · rw [← GlobalTheory.HostSplit.ncard_placesOver _ B.host.pde_prime]
    exact B.level_split_E _ B.host.pde_level.1
  · rw [← GlobalTheory.HostSplit.ncard_placesOver _ B.host.pde'_prime]
    exact B.level_split_E _ B.host.pde_level.2

end Pre

section Spaces

open DiagSp

variable (R : Ranks) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] (cm : CMData F E) (T : ℕ) (hT : T.Prime) (pz : E) (hpz : star pz * pz = T)

def spacesNorm : Spaces R F E :=
  { spacesStd R cm T hT pz hpz (fun _ => false) with
    z := Pi.single (⟨R.rankY R.m, by rw [N_top]; omega⟩ : Fin (R.N R.m)) pz
    z_anis := by
      refine ne_of_eq_of_ne (diag_single_single _ (fun _ => false) _ _ pz pz) ?_
      rw [if_pos rfl]
      simp only [sgn, Bool.false_eq_true, if_false, mul_one, hpz]
      exact_mod_cast hT.ne_zero
    z_orth := fun x => diag_ext_single _ _ (fun _ => false) x _ pz le_rfl }

theorem spacesNorm_Y_sig (j : ℕ) (τ : E →+* ℂ) : ((spacesNorm R cm T hT pz hpz).Y j).sig τ = sigYD R j := spY_sig R j τ

theorem spacesNorm_z_norm : ((spacesNorm R cm T hT pz hpz).X R.m).hT (spacesNorm R cm T hT pz hpz).z
    (spacesNorm R cm T hT pz hpz).z = (T : E) := by
  refine (diag_single_single (R.N R.m) (fun _ => false)
    (⟨R.rankY R.m, by rw [N_top]; omega⟩ : Fin (R.N R.m)) _ pz pz).trans ?_
  rw [if_pos rfl]
  simp only [sgn, Bool.false_eq_true, if_false, mul_one, hpz]

end Spaces

theorem exists_finset_capitulation (E : Type) [Field E] [NumberField E] (τ : E →+* ℂ) :
    ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K],
      (∀ z ∈ S, z ∈ K) → (∀ x, τ x ∈ K) → ∀ 𝔞 : Ideal (𝓞 E), ∃ β : K,
        Submodule.span (𝓞 K) {β} = Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} := by
  classical
  have hpos : 0 < Fintype.card (ClassGroup (𝓞 E)) := Fintype.card_pos
  choose rep γ hrep hγ hpow using exists_rep_pow_classNumber E
  choose α hα using fun c : ClassGroup (𝓞 E) =>
    IsAlgClosed.exists_pow_nat_eq (τ (γ c : E)) hpos
  have hαint : ∀ c, IsIntegral ℤ (α c) := fun c =>
    IsIntegral.of_pow hpos (by rw [hα c]; exact (RingOfIntegers.isIntegral_coe (γ c)).map τ.toIntAlgHom)
  refine ⟨Finset.univ.image α, ?_, ?_⟩
  · intro z hz
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hz
    exact ((hαint c).tower_top (A := ℚ)).isAlgebraic
  intro K _ hS hτ 𝔞
  have : NumberField K := {}
  let f : E →+* K := τ.codRestrict K hτ
  have hset : {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} = {x : K | ∃ a ∈ 𝔞, x = f (a : E)} := by
    ext x
    constructor
    · rintro ⟨a, ha, e⟩
      exact ⟨a, ha, Subtype.ext e⟩
    · rintro ⟨a, ha, e⟩
      exact ⟨a, ha, congrArg Subtype.val e⟩
  rw [hset, span_image_eq_coeSubmodule_map f 𝔞]
  by_cases h0 : 𝔞 = ⊥
  · refine ⟨0, ?_⟩
    rw [h0, Ideal.map_bot, IsLocalization.coeSubmodule_bot, Submodule.span_singleton_eq_bot.mpr rfl]
  set φ := RingOfIntegers.mapRingHom f
  set c := ClassGroup.mk0 (⟨𝔞, mem_nonZeroDivisors_of_ne_zero h0⟩ : (Ideal (𝓞 E))⁰) with hc
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp (hrep c).symm
  have haK : α c ∈ K := hS _ (Finset.mem_image_of_mem _ (Finset.mem_univ c))
  have haint : IsIntegral ℤ (⟨α c, haK⟩ : K) :=
    (isIntegral_algHom_iff (K.val : K →+* ℂ).toIntAlgHom Subtype.val_injective).mp (hαint c)
  let aO : 𝓞 K := ⟨⟨α c, haK⟩, haint⟩
  have hφγ : φ (γ c) = aO ^ Fintype.card (ClassGroup (𝓞 E)) := by
    apply RingOfIntegers.ext
    apply Subtype.ext
    simp only [φ, RingOfIntegers.mapRingHom_apply, map_pow]
    exact (hα c).symm
  have hrepmap : Ideal.map φ (rep c : Ideal (𝓞 E)) = Ideal.span {aO} := by
    apply pow_left_injective hpos.ne'
    simp only
    rw [← Ideal.map_pow, hpow c, Ideal.map_span, Set.image_singleton, hφγ, Ideal.span_singleton_pow]
  have hmap := congrArg (fun I => IsLocalization.coeSubmodule K (Ideal.map φ I)) hxy
  simp only [Ideal.map_mul, hrepmap, Ideal.map_span, Set.image_singleton,
    IsLocalization.coeSubmodule_mul, IsLocalization.coeSubmodule_span_singleton] at hmap
  have hu : algebraMap (𝓞 K) K (φ x) ≠ 0 := by
    show f (x : E) ≠ 0
    rw [map_ne_zero]
    exact fun h => hx (RingOfIntegers.ext (by simpa using h))
  refine ⟨(algebraMap (𝓞 K) K (φ x))⁻¹ * (algebraMap (𝓞 K) K (φ y) * algebraMap (𝓞 K) K aO), ?_⟩
  have hone : Submodule.span (𝓞 K) {(algebraMap (𝓞 K) K (φ x))⁻¹} *
      Submodule.span (𝓞 K) {algebraMap (𝓞 K) K (φ x)} = 1 := by
    rw [Submodule.span_mul_span, Set.singleton_mul_singleton, inv_mul_cancel₀ hu,
      Submodule.one_eq_span]
  rw [← one_mul (IsLocalization.coeSubmodule K (Ideal.map φ 𝔞)), ← hone, mul_assoc, hmap,
    Submodule.span_mul_span, Set.singleton_mul_singleton, Submodule.span_mul_span,
    Set.singleton_mul_singleton]

end GlobalTheory.Mem

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.KZ

def ZetaSysUr2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
      ∃ (c : Coef l) (y : G ℚ Ω → Fin 2 → Qbar l) (S' : Finset Pl), Sys W c y S' ∧ NzAt W A y

theorem zetaElementsUnramifiedOrdinary_of_eulerSystem_inertia (h : ZetaSysUr2) : ZetaUr := fun l _ Ω _ _ _ ι e S A W g hN hS => es_of_sys (h l Ω ι e S A W g hN hS)

def ExistsZetaEulerSystemIwasawaData (Pin : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime], ℕ → (ValuationSubring Ω) → R2 Ω l → Coef l →
    (G ℚ Ω → (Qbar l)ˣ) → (∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) → (∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) → Prop) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
      ∃ (c : Coef l) (y : G ℚ Ω → Fin 2 → Qbar l) (S' : Finset Pl) (ν : G ℚ Ω → (Qbar l)ˣ)
        (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l),
        Sys W c y S' ∧ IwSys2 c A ν Z ∧ SpLink A e χ Z y ∧ Pin e A W c ν χ Z

def ZetaEulerSystemNonvanishing (Pin : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime], ℕ → (ValuationSubring Ω) → R2 Ω l → Coef l →
    (G ℚ Ω → (Qbar l)ˣ) → (∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) → (∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) → Prop) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
      ∀ (c : Coef l) (y : G ℚ Ω → Fin 2 → Qbar l) (S' : Finset Pl) (ν : G ℚ Ω → (Qbar l)ˣ)
        (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l),
        Sys W c y S' → IwSys2 c A ν Z → SpLink A e χ Z y → Pin e A W c ν χ Z → NzAt W A y

theorem zetaSysU_of_halves2 (Pin : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime], ℕ → (ValuationSubring Ω) →
    R2 Ω l → Coef l → (G ℚ Ω → (Qbar l)ˣ) → (∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) → (∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) → Prop)
    (hG : ExistsZetaEulerSystemIwasawaData Pin) (hL : ZetaEulerSystemNonvanishing Pin) : ZetaSysUr2 := by
  intro l _ Ω _ _ _ ι e S A W g hN hS
  obtain ⟨c, y, S', ν, χ, Z, h1, h2, h3, h4⟩ := hG l Ω ι e S A W g hN hS
  exact ⟨c, y, S', h1, hL l Ω ι e S A W g hN hS c y S' ν χ Z h1 h2 h3 h4⟩

theorem zetaUr_of_halves2 (Pin : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime], ℕ → (ValuationSubring Ω) →
    R2 Ω l → Coef l → (G ℚ Ω → (Qbar l)ˣ) → (∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) → (∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) → Prop)
    (hG : ExistsZetaEulerSystemIwasawaData Pin) (hL : ZetaEulerSystemNonvanishing Pin) : ZetaUr :=
  zetaElementsUnramifiedOrdinary_of_eulerSystem_inertia (zetaSysU_of_halves2 Pin hG hL)

end GlobalTheory.KZ

end
end
