module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.RingTheory.HahnSeries.PowerSeries
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.NumberTheory.Modular
public import Mathlib.NumberTheory.ModularForms.Petersson
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.KEdge

variable {Γ : Type*} [Group Γ] {N : ℕ}

def edge (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N) (σ h : Γ) : ZMod N :=
  η (σ * h * σ⁻¹) - η h - (x h).toAdd * (y σ).toAdd + (x σ).toAdd * (y h).toAdd

def CobOn (Δ : Subgroup Γ) (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N) : Prop :=
  ∀ g ∈ Δ, ∀ h ∈ Δ, (x g).toAdd * (y h).toAdd = η h - η (g * h) + η g

end GlobalTheory.KEdge
end
end

section

noncomputable section

namespace GlobalTheory.Mem.Gelf

open MvPolynomial

def rowE (R : Type) [CommRing R] (r n : ℕ) :
    Matrix (Fin r) (Fin r) (Module.End R (MvPolynomial (Fin r × Fin n) R)) :=
  Matrix.of fun a b => ∑ s : Fin n,
    (LinearMap.mulLeft R (X (a, s) : MvPolynomial (Fin r × Fin n) R)).comp (pderiv (R := R) (b, s)).toLinearMap

def GlRel {A : Type} [Ring A] {N : ℕ} (E : Matrix (Fin N) (Fin N) A) : Prop :=
  ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0)

def gelfA {R : Type} [CommRing R] {N : ℕ} (μ : Fin N → R) : Matrix (Fin N) (Fin N) R :=
  Matrix.of fun a b => if a = b then μ a + ((N - 1 - a.val : ℕ) : R) else if a < b then -1 else 0

def gelfC {R : Type} [CommRing R] {N : ℕ} (μ : Fin N → R) (k : ℕ) : R :=
  ∑ a, ∑ b, (gelfA μ ^ k) a b

end GlobalTheory.Mem.Gelf
end
end

section

noncomputable section

open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

def zerosIn {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) : Set ℂ :=
  {ρ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ T ∧ DirichletCharacter.LFunction χ ρ = 0}

def zmult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ

def zsum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) (f : ℂ → ℂ) : ℂ :=
  ∑ᶠ ρ ∈ zerosIn χ t T, (zmult χ ρ : ℂ) * f ρ

def zsumR {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) (f : ℂ → ℝ) : ℝ :=
  ∑ᶠ ρ ∈ zerosIn χ t T, (zmult χ ρ : ℝ) * f ρ

def psiChi {q : ℕ} (χ : DirichletCharacter ℂ q) (u : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)

def rayI {K : Type} [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)) : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Subgroup.closure {I | ∃ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔮 ∧
    (I : FractionalIdeal (𝓞 K)⁰ K) = (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K)}

def rayP {K : Type} [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)) : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Subgroup.closure {I | ∃ a : 𝓞 K, a - 1 ∈ 𝔮 ∧
    (I : FractionalIdeal (𝓞 K)⁰ K) = ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)}

def rayNo {K : Type} [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)) : ℕ := (rayP 𝔮).relIndex (rayI 𝔮)

def rayPrimes {K : Type} [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)) (X : ℝ) : Set (HeightOneSpectrum (𝓞 K)) :=
  {v | ¬ v.asIdeal ∣ 𝔮 ∧ (Ideal.absNorm v.asIdeal : ℝ) ≤ X ∧
    ∃ I ∈ rayP 𝔮, (I : FractionalIdeal (𝓞 K)⁰ K) = (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K)}

def NormOne (d M p : ℕ) : Prop :=
  ∃ A B : ℤ, A ^ 2 + (d : ℤ) * B ^ 2 = 4 * (p : ℤ) ∧ (M : ℤ) ∣ B ∧ (2 * (M : ℤ)) ∣ A - 2 - B


open Classical in
def normPrimes (d M : ℕ) (X Y : ℝ) : Finset ℕ := by
  classical
  exact (Ioc ⌊X⌋₊ ⌊Y⌋₊).filter (fun p => p.Prime ∧ NormOne d M p)

end GlobalTheory.Mem.An
end
end

section

noncomputable section

namespace GlobalTheory.SgAlg

variable {E : Type} [CommRing E]

def IsQA (σ : E →+* E) : Prop :=
  (∀ x, σ (σ x) = x) ∧ (∃ x, σ x ≠ x) ∧ IsReduced E ∧ IsUnit (2 : E) ∧
    ∀ x, σ x = x → x ≠ 0 → IsUnit x

def cT (σ : E →+* E) {a b : Type} (A : Matrix a b E) : Matrix b a E := (A.map σ).transpose

def IsHermU (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Prop := cT σ J = J ∧ IsUnit J.det

def form (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : E :=
  dotProduct (fun i => σ (y i)) (J.mulVec x)

def pairM (σ : E →+* E) {n : ℕ} {a b : Type} (J : Matrix (Fin n) (Fin n) E)
    (P' : Matrix (Fin n) b E) (P : Matrix (Fin n) a E) : Matrix a b E := cT σ P * J * P'

def IsUn (σ : E →+* E) {n : ℕ} (J g : Matrix (Fin n) (Fin n) E) : Prop := cT σ g * J * g = J

def Free {n : ℕ} {a : Type} [Fintype a] [DecidableEq a] (P : Matrix (Fin n) a E) : Prop :=
  ∃ L : Matrix a (Fin n) E, L * P = 1

def IsUp {m : ℕ} (u : Matrix (Fin m) (Fin m) E) : Prop :=
  ∀ i j, (j < i → u i j = 0) ∧ (i = j → u i j = 1)

def IsLo {m : ℕ} (u : Matrix (Fin m) (Fin m) E) : Prop :=
  ∀ i j, (i < j → u i j = 0) ∧ (i = j → u i j = 1)

def lead {m : ℕ} (Z : Matrix (Fin m) (Fin m) E) (l : ℕ) (hl : l ≤ m) : E :=
  (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det

def TF (r : ℕ) (T : E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  Matrix.diagonal fun a => if a = Fin.last r then -T else 0

def Gq (σ : E →+* E) {r : ℕ} (T T' : E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : E :=
  Z.det * σ Z.det - T * T' * (lead Z r (Nat.le_succ r) * σ (lead Z r (Nat.le_succ r)))

def IsFrame (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T : E)
    (P : Matrix (Fin n) (Fin (r + 1)) E) : Prop := Free P ∧ pairM σ J P P = TF r T

def eOf {n r : ℕ} (P : Matrix (Fin n) (Fin (r + 1)) E) : Matrix (Fin n) (Fin r) E :=
  P.submatrix id Fin.castSucc

def IsDual (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (P : Matrix (Fin n) (Fin (r + 1)) E) (f : Matrix (Fin n) (Fin r) E) : Prop :=
  pairM σ J f P = (Matrix.of fun a b => if a = Fin.castSucc b then 1 else 0) ∧ pairM σ J f f = 0

def InS (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E)
    (g : Matrix (Fin n) (Fin n) E) : Prop := IsUn σ J g ∧ ∃ ν, IsUp ν ∧ g * P = P * ν

def InN (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E)
    (g : Matrix (Fin n) (Fin n) E) : Prop :=
  IsUn σ J g ∧ (∃ ν, IsUp ν ∧ g * eOf P = eOf P * ν) ∧
    ∀ v : Fin n → E, (cT σ (eOf P) * J).mulVec v = 0 → ∃ c, g.mulVec v - v = (eOf P).mulVec c

def XZ (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T T' : E)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Set (Matrix (Fin n) (Fin (r + 1)) E × Matrix (Fin n) (Fin (r + 1)) E) :=
  {p | IsFrame σ J T p.1 ∧ IsFrame σ J T' p.2 ∧ pairM σ J p.2 p.1 = Z}

def PosOnPerp {n : ℕ} {a : Type} [Fintype a] (J : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin n) a ℂ) : Prop :=
  ∀ w : Fin n → ℂ, (cT (starRingEnd ℂ) A * J).mulVec w = 0 → w ≠ 0 →
    0 < (form (starRingEnd ℂ) J w w).re

end GlobalTheory.SgAlg
end
end

section

noncomputable section

open scoped MatrixGroups

namespace GlobalTheory.KZ

def Hs : Set ℂ := {z | 0 < z.im}

abbrev Mero : Type := Filter.Germ (Filter.codiscreteWithin Hs) ℂ

abbrev GQ : Type := ↥(Matrix.GLPos (Fin 2) ℚ)

def ent (g : GQ) (i j : Fin 2) : ℚ := ((g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j

def mob (g : GQ) (z : ℂ) : ℂ :=
  ((ent g 0 0 : ℂ) * z + (ent g 0 1 : ℂ)) / ((ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ))

def ofSL : SL(2, ℤ) →* GQ :=
  Matrix.SpecialLinearGroup.toGLPos.comp (Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ))

def en (γ : SL(2, ℤ)) (i j : Fin 2) : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) i j

def toGQ (m : Matrix (Fin 2) (Fin 2) ℤ) : GQ :=
  if h : 0 < m.det then
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (m.map (Int.castRingHom ℚ))
        (by
          have e := RingHom.map_det (Int.castRingHom ℚ) m
          simp only [RingHom.mapMatrix_apply] at e
          rw [← e, eq_intCast]; exact_mod_cast h.ne'),
      by
        show 0 < Matrix.det (m.map (Int.castRingHom ℚ))
        have e := RingHom.map_det (Int.castRingHom ℚ) m
        simp only [RingHom.mapMatrix_apply] at e
        rw [← e, eq_intCast]; exact_mod_cast h⟩
  else 1

def eOm {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) (x : ℚ) : Ω :=
  Function.invFun ε (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)))

structure Tower (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) where

  K : Type
  [fld : Field K]
  [alg : Algebra Ω K]

  exp : K →ₐ[Ω] HahnSeries ℚ Ω

  sl : GQ → (K ≃ₐ[Ω] K)

  sl_one : ∀ f, sl 1 f = f

  sl_mul : ∀ g h f, sl (g * h) f = sl h (sl g f)

  gal : (Ω ≃ₐ[ℚ] Ω) → (K ≃+* K)

  gal_exp : ∀ s f r, (exp (gal s f)).coeff r = s ((exp f).coeff r)

  an : K →+* Mero

  an_c : ∀ c : Ω, an (algebraMap Ω K c) = ((fun _ => ε c : ℂ → ℂ) : Mero)

  an_sl : ∀ (g : GQ) (f : K) (φ : ℂ → ℂ), an f = (φ : Mero) → an (sl g f) = ((fun z => φ (mob g z)) : Mero)

  an_mero : ∀ f : K, ∃ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs ∧ DifferentiableOn ℂ b Hs ∧ (b : Mero) ≠ 0 ∧
    an f * (b : Mero) = (a : Mero)

  an_exp : ∀ f : K, ∃ (φ : ℂ → ℂ) (C : ℝ), an f = (φ : Mero) ∧ ∀ z : ℂ, C < z.im →
    HasSum (fun r : ℚ => ε ((exp f).coeff r) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (φ z)

  level : ∀ f : K, ∃ M : ℕ, 0 < M ∧ ∀ γ ∈ CongruenceSubgroup.Gamma M, sl (ofSL γ) f = f

  exp_upper : ∀ (g : GQ), ent g 1 0 = 0 → ∀ (f : K) (r : ℚ),
    (exp (sl g f)).coeff (r * ent g 0 0 / ent g 1 1) = eOm ε (r * ent g 0 1 / ent g 1 1) * (exp f).coeff r

  recip : ∀ (M : ℕ) (f : K), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, sl (ofSL γ) f = f) →
    ∀ (ζ : Ω), IsPrimitiveRoot ζ M → ∀ (s : Ω ≃ₐ[ℚ] Ω) (d : ℤ), s ζ = ζ ^ d → ∀ γ γ' : SL(2, ℤ),
      ((en γ' 0 0 : ZMod M) = en γ 0 0 ∧ (en γ' 0 1 : ZMod M) = d * en γ 0 1 ∧
        (d : ZMod M) * en γ' 1 0 = en γ 1 0 ∧ (en γ' 1 1 : ZMod M) = en γ 1 1) →
      gal s (sl (ofSL γ) f) = sl (ofSL γ') (gal s f)

  jK : K

  j_inv : ∀ γ : SL(2, ℤ), sl (ofSL γ) jK = jK

  j_exp : (exp jK).coeff (-1) = 1 ∧ (∀ r : ℚ, r < -1 → (exp jK).coeff r = 0) ∧ ∀ r : ℚ, ∃ n : ℤ, (exp jK).coeff r = n

  j_hol : ∃ φ : ℂ → ℂ, an jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs

  alg_j : ∀ f : K, IsAlgebraic (IntermediateField.adjoin Ω {jK}) f

  bdd : ∀ f : K, ∃ D : ℕ, 0 < D ∧ ∀ r : ℚ, ∃ k : ℕ, IsIntegral ℤ ((D : Ω) ^ k * (exp f).coeff r)

  sat : ∀ (a b : ℂ → ℂ) (M : ℕ), 0 < M → DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (b : Mero) ≠ 0 →
    (∀ γ ∈ CongruenceSubgroup.Gamma M, ((fun z => a (mob (ofSL γ) z) * b z) : Mero) = ((fun z => a z * b (mob (ofSL γ) z)) : Mero)) →
    (∃ P : Polynomial K, P ≠ 0 ∧ P.eval₂ an (((a / b : ℂ → ℂ)) : Mero) = 0) →
    ∃ f : K, an f * (b : Mero) = (a : Mero)

  mem_q : ∀ (a : ℂ → ℂ) (M : ℕ), 0 < M → DifferentiableOn ℂ a Hs →
    (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ z ∈ Hs, a (mob (ofSL γ) z) = a z) →
    (∀ γ : SL(2, ℤ), ∃ (c : ℤ → Ω) (n0 : ℤ), (∀ n < n0, c n = 0) ∧ ∀ z ∈ Hs,
      HasSum (fun n : ℤ => ε (c n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z / M)) (a (mob (ofSL γ) z))) →
    ∃ f : K, an f = (a : Mero)

attribute [instance] Tower.fld Tower.alg

end GlobalTheory.KZ
end
end

section

noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm

namespace GlobalTheory.Hk

def lev (N l : ℕ) : Subgroup SL(2, ℤ) := Gamma1 N ⊓ Gamma0 l

def uOp (q : ℕ) (f : ℍ → ℂ) (τ : ℍ) : ℂ :=
  (q : ℂ)⁻¹ * ∑ j ∈ Finset.range q, f (ofComplex (((τ : ℂ) + j) / q))

def vOp (q : ℕ) (f : ℍ → ℂ) (τ : ℍ) : ℂ := f (ofComplex ((q : ℂ) * τ))

def IsDia (N l : ℕ) (d : ℤ) (σ : SL(2, ℤ)) : Prop :=
  ((σ 1 0 : ℤ) : ZMod (N * l)) = 0 ∧ ((σ 1 1 : ℤ) : ZMod N) = d

def dia (k : ℤ) (σ : SL(2, ℤ)) (f : ℍ → ℂ) : ℍ → ℂ := f ∣[k] σ

def heckeT (k : ℤ) (q : ℕ) (σ : SL(2, ℤ)) (f : ℍ → ℂ) : ℍ → ℂ :=
  uOp q f + ((q : ℂ) ^ (k - 1)) • vOp q (f ∣[k] σ)

def coef (f : ℍ → ℂ) (n : ℕ) : ℂ := (qExpansion 1 f).coeff n

def pet (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f g : ℍ → ℂ) : ℂ :=
  ∑ᶠ γ : SL(2, ℤ) ⧸ Γ, ∫ z in ModularGroup.fd, petersson k f g (γ.out⁻¹ • z)

def pmGrp (Γ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℤ) where
  carrier := {γ | γ ∈ Γ ∨ -γ ∈ Γ}
  one_mem' := Or.inl Γ.one_mem
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (Γ.mul_mem ha hb)
    · exact Or.inr (by simpa using Γ.mul_mem ha hb)
    · exact Or.inr (by simpa using Γ.mul_mem ha hb)
    · exact Or.inl (by simpa using Γ.mul_mem ha hb)
  inv_mem' := by
    rintro a (ha | ha)
    · exact Or.inl (Γ.inv_mem ha)
    · refine Or.inr ?_
      have h : -a⁻¹ = (-a)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]; simp
      rw [h]; exact Γ.inv_mem ha

theorem le_pmGrp (Γ : Subgroup SL(2, ℤ)) : Γ ≤ pmGrp Γ := fun _ h => Or.inl h

theorem neg_one_mem_pmGrp (Γ : Subgroup SL(2, ℤ)) : -1 ∈ pmGrp Γ :=
  Or.inr (by simpa using Γ.one_mem)

theorem pmGrp_eq_self {Γ : Subgroup SL(2, ℤ)} (h : -1 ∈ Γ) : pmGrp Γ = Γ := by
  apply le_antisymm _ (le_pmGrp Γ)
  rintro γ (hγ | hγ)
  · exact hγ
  · simpa using Γ.mul_mem h hγ

instance pmGrp_finiteIndex (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] : (pmGrp Γ).FiniteIndex :=
  Subgroup.finiteIndex_of_le (le_pmGrp Γ)

theorem relIndex_pmGrp_of_notMem {Γ : Subgroup SL(2, ℤ)} (h : -1 ∉ Γ) :
    Γ.relIndex (pmGrp Γ) = 2 := by
  unfold Subgroup.relIndex
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨-1, neg_one_mem_pmGrp Γ⟩, ?_⟩
  rintro ⟨b, hb⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, mul_neg, mul_one]
  have hne : ¬ (b ∈ Γ ∧ -b ∈ Γ) := fun ⟨h1, h2⟩ => h (by simpa using Γ.mul_mem h2 (Γ.inv_mem h1))
  rcases hb with hb | hb
  · exact Or.inr ⟨hb, fun h2 => hne ⟨hb, h2⟩⟩
  · exact Or.inl ⟨hb, fun h1 => hne ⟨h1, hb⟩⟩

theorem neg_one_notMem_lev {N : ℕ} (l : ℕ) (hN : 3 ≤ N) : -1 ∉ lev N l := by
  rintro ⟨h, -⟩
  have h1 := ((Gamma1_mem N _).1 h).1
  have h2 : (((-1 : ℤ) : ℤ) : ZMod N) = 1 := by simpa using h1
  have h3 : ((2 : ℕ) : ZMod N) = 0 := by
    push_cast at h2 ⊢
    linear_combination -h2
  rw [ZMod.natCast_eq_zero_iff] at h3
  have := Nat.le_of_dvd two_pos h3
  omega

def petProd (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f g : ℍ → ℂ) : ℂ :=
  ∑ᶠ γ : SL(2, ℤ) ⧸ pmGrp Γ, ∫ z in ModularGroup.fd, petersson k g f (γ.out⁻¹ • z)

theorem petProd_smul_left (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ) (c : ℂ) (f g : ℍ → ℂ) :
    petProd Γ k (c • f) g = c * petProd Γ k f g := by
  unfold petProd
  haveI : Fintype (SL(2, ℤ) ⧸ pmGrp Γ) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [← integral_const_mul]
  congr 1
  ext z
  simp [petersson]
  ring

theorem petProd_smul_right (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ) (c : ℂ) (f g : ℍ → ℂ) :
    petProd Γ k f (c • g) = (starRingEnd ℂ) c * petProd Γ k f g := by
  unfold petProd
  haveI : Fintype (SL(2, ℤ) ⧸ pmGrp Γ) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [← integral_const_mul]
  congr 1
  ext z
  simp [petersson]
  ring

theorem petProd_level_one (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ) {f g : ℍ → ℂ}
    (hf : ∀ γ : SL(2, ℤ), f ∣[k] γ = f) (hg : ∀ γ : SL(2, ℤ), g ∣[k] γ = g) :
    petProd Γ k f g = ((pmGrp Γ).index : ℂ) * ∫ z in ModularGroup.fd, petersson k g f z := by
  unfold petProd
  haveI : Fintype (SL(2, ℤ) ⧸ pmGrp Γ) := Fintype.ofFinite _
  simp only [← petersson_slash_SL, hf, hg]
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Subgroup.index, Nat.card_eq_fintype_card]
  simp

end GlobalTheory.Hk
end
end
