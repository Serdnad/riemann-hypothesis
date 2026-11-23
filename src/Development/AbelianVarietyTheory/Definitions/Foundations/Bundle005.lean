module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.NumberTheory.Modular
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Basic.Real.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Formalism.DegreeFormula.FlagDegFormula

@[expose] public section

section

noncomputable section

open scoped MatrixGroups
open Matrix

namespace GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def Tower.OverY (X : Tower Ω ε) (W : ValuationSubring X.K) : Prop :=
  (∀ c : Ω, algebraMap Ω X.K c ∈ W) ∧ X.jK ∈ W

def Tower.Un (X : Tower Ω ε) (m : ℕ) : Set X.Kˣ :=
  {f | ∀ W, X.OverY W → ∃ g : X.Kˣ, W.valuation ((f : X.K) / (g : X.K) ^ m) = 1}

abbrev Tower.Kl (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : Type := TensorProduct ℤ ℤ_[l] (Additive X.Kˣ)

abbrev idl (l : ℕ) [Fact l.Prime] : Ideal ℤ_[l] := Ideal.span {(l : ℤ_[l])}

abbrev Tower.Khat (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : Type := AdicCompletion (idl l) (X.Kl l)

def Tower.cls (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (f : X.Kˣ) :
    X.Kl l ⧸ ((idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Kl l))) :=
  Submodule.Quotient.mk ((1 : ℤ_[l]) ⊗ₜ Additive.ofMul f)

def Tower.ASet (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : Set (X.Khat l) :=
  {a | ∀ n : ℕ, ∃ f ∈ X.Un (l ^ n), AdicCompletion.eval (idl l) (X.Kl l) n a = X.cls l n f}

def Tower.A (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : Submodule ℤ_[l] (X.Khat l) := Submodule.span ℤ_[l] (X.ASet l)

def Tower.kmap (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ : X.K ≃+* X.K) : X.Khat l →ₗ[ℤ_[l]] X.Khat l :=
  AdicCompletion.map (idl l) (LinearMap.baseChange ℤ_[l]
    (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom))))

abbrev Tower.Fn (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : Type := (Fin 2 → ℤ_[l]) → X.Khat l

def Tower.Pol (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w : ℕ) : Set (X.Fn l) :=
  {b | ∃ c : Fin (w + 1) → X.Khat l, (∀ i, c i ∈ X.A l) ∧
    ∀ u, b u = ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i}

def mZl (l : ℕ) [Fact l.Prime] (m : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ_[l] := m.map (Int.castRingHom ℤ_[l])

def Tower.act (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (m : Matrix (Fin 2) (Fin 2) ℤ) :
    X.Fn l →ₗ[ℤ_[l]] X.Fn l where
  toFun b u := X.kmap l (X.sl (toGQ m)).toRingEquiv (b (mZl l m *ᵥ u))
  map_add' b b' := by funext u; simp
  map_smul' c b := by funext u; simp

def Gam (N l : ℕ) : Subgroup SL(2, ℤ) := CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma0 l

def Tower.BSet (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] : Set (X.Fn l) :=
  {b | b ∈ X.Pol l w ∧ ∀ γ ∈ Gam N l, X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b}

def Tower.B (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] : Submodule ℤ_[l] (X.Fn l) := Submodule.span ℤ_[l] (X.BSet N l w)

def IsDiam (N l d : ℕ) (γ : SL(2, ℤ)) : Prop :=
  γ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l ∧ (en γ 1 1 : ZMod N) = d

def sgD (N l d : ℕ) : SL(2, ℤ) := Classical.epsilon (IsDiam N l d)

def Tower.diam (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (d : ℕ) : X.Fn l →ₗ[ℤ_[l]] X.Fn l :=
  X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ)

def Tower.heckeT (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (q : ℕ) : X.Fn l →ₗ[ℤ_[l]] X.Fn l :=
  (∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)]) +
    X.act l ((sgD N l q : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])

def Tower.heckeU (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : X.Fn l →ₗ[ℤ_[l]] X.Fn l :=
  ∑ j ∈ Finset.range l, X.act l !![1, (j : ℤ); 0, (l : ℤ)]

def Tower.galB (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) : X.Fn l →ₗ[ℤ_[l]] X.Fn l where
  toFun b u := X.kmap l (X.gal s) (b ![u 0, (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * u 1])
  map_add' b b' := by funext u; simp
  map_smul' c b := by funext u; simp

inductive Letter
  | T (q : ℕ)
  | U
  | D (d : ℕ)

def Tower.op (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] : Letter → (X.Fn l →ₗ[ℤ_[l]] X.Fn l)
  | Letter.T q => X.heckeT N l q
  | Letter.U => X.heckeU l
  | Letter.D d => X.diam N l d

end GlobalTheory.KZ
end
end

section

noncomputable section

open Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois

variable {K : Type*} [Field K] [CharZero K]

def rowT (N p n : ℕ) (γ : GL (Fin 2) (ZMod (p ^ n))) (i : Fin 2) (w : ℤ × ℤ) : ℤ × ℤ :=
  ((N : ℤ) * ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i 0).val + (p : ℤ) ^ n * w.1,
   (N : ℤ) * ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i 1).val + (p : ℤ) ^ n * w.2)

def pieceT (N p n m k : ℕ) [NeZero p] (ψ : DirichletCharacter K (p ^ m)) (c d : ℤ) (w w' : ℤ × ℤ) (ζ : K)
    (X : Finset (GL (Fin 2) (ZMod (p ^ n)))) (r : ℕ) : K :=
  -((p : K) ^ ((n : ℤ) * ((k : ℤ) - 4))) * ∑ γ ∈ X,
    ψ (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))).det.val : ℕ) : ZMod (p ^ m)) *
      cmul (smF c (k - 1) (N * p ^ n) ζ (rowT N p n γ 0 w).1 (rowT N p n γ 0 w).2)
           (smF d 1 (N * p ^ n) ζ (rowT N p n γ 1 w').1 (rowT N p n γ 1 w').2) r

def pieceTRaw (N p n m k : ℕ) [NeZero p] (ψ : DirichletCharacter K (p ^ m)) (w w' : ℤ × ℤ) (ζ : K)
    (X : Finset (GL (Fin 2) (ZMod (p ^ n)))) (r : ℕ) : K :=
  -((p : K) ^ ((n : ℤ) * ((k : ℤ) - 4))) * ∑ γ ∈ X,
    ψ (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))).det.val : ℕ) : ZMod (p ^ m)) *
      cmul (eisF (k - 1) (N * p ^ n) ζ (rowT N p n γ 0 w).1 (rowT N p n γ 0 w).2)
           (eisF 1 (N * p ^ n) ζ (rowT N p n γ 1 w').1 (rowT N p n γ 1 w').2) r

end GlobalTheory.KummerEisensteinGalois
end
end

section

noncomputable section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup
open scoped MatrixGroups Real ComplexConjugate

namespace GlobalTheory.EisM

section Formal

variable {R : Type*} [CommRing R]

def Uo (l : ℕ) (a : ℕ → R) : ℕ → R := fun n => a (l * n)

def Vo (l : ℕ) (a : ℕ → R) : ℕ → R := fun n => if l ∣ n then a (n / l) else 0

def dep (l : ℕ) (a : ℕ → R) : ℕ → R := fun n => if l ∣ n then 0 else a n

def To (k : ℕ) (c : R) (q : ℕ) (a : ℕ → R) : ℕ → R := fun n => a (q * n) + c * (q : R) ^ (k - 1) * Vo q a n

def mul (a b : ℕ → R) : ℕ → R := fun n => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * b p.2

def eis (j : ℕ) (c : R) (a b : ℤ → R) : ℕ → R := fun n =>
  if n = 0 then c else ∑ p ∈ n.divisorsAntidiagonal, a p.1 * (p.1 : R) ^ (j - 1) * b p.2

def Zs (k l : ℕ) (u v : ℤ → R) (F : ℕ → ℕ → R) : ℕ → R := fun n =>
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ∑ x ∈ p.1.divisorsAntidiagonal, ∑ y ∈ p.2.divisorsAntidiagonal,
    if l ∣ p.1 ∨ l ∣ p.2 then 0 else (x.1 : R) ^ (k - 2) * u x.2 * v y.1 * F x.1 y.1

def quo {M : ℕ} (f : ZMod M → R) : ℕ → ℕ → R := fun x x' => f ((x : ZMod M) * (x' : ZMod M)⁻¹)

def lam (B : ℕ) (c a : ℕ → R) : R := ∑ n ∈ Finset.range B, c n * a n

end Formal

section Level

variable {K : Type*} [Field K]

def val (B : ℕ) (c : ℕ → K) (l : ℕ) (α : K) (r : ℕ) (a : ℕ → K) : K := (α ^ r)⁻¹ * lam B c ((Uo l)^[r] a)

def Fser (j M : ℕ) (ζ : K) (b : ℤ → K) (c : K) (u w : ZMod M) : ℕ → K := fun s =>
  if s = 0 then c else ∑ p ∈ s.divisorsAntidiagonal,
    ((if (p.1 : ZMod M) = u then ((p.1 : K) / M) ^ (j - 1) * ζ ^ (w.val * p.2) * b p.2 else 0) -
      (if -(p.1 : ZMod M) = u then (-(p.1 : K) / M) ^ (j - 1) * (ζ ^ (w.val * p.2))⁻¹ * b (-(p.2 : ℤ)) else 0))

end Level

section Bridge

variable {K : Type*} [Field K] [CharZero K]

theorem mul_eq_cmul (f g : ℕ → K) : mul f g = GlobalTheory.KummerEisensteinGalois.cmul f g := by
  funext n
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => f i * g j) n

end Bridge

def hat {N : ℕ} (φ : ZMod N → ℂ) (d : ℤ) : ℂ := ∑ y ∈ Finset.range N, φ y * cexp (2 * π * Complex.I * (y * d) / N)

def qs (a : ℕ → ℂ) (τ : ℍ) : ℂ := ∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * τ)

def PolyB (a : ℕ → ℂ) : Prop := ∃ (C : ℝ) (A : ℕ), ∀ n : ℕ, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ A

def Inv (k L : ℕ) (χ : ℤ → ℂ) (f : ℍ → ℂ) : Prop :=
  ∀ γ : SL(2, ℤ), (L : ℤ) ∣ γ 1 0 → ∀ τ : ℍ, f (γ • τ) = χ (γ 1 1) * (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ k * f τ

def MF (k L : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ) : Prop := PolyB a ∧ Inv k L χ (qs a)

def CF (k L : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ) : Prop := MF k L χ a ∧ ∃ C : ℝ, ∀ τ : ℍ, ‖qs a τ‖ ^ 2 * τ.im ^ k ≤ C

def ch {N : ℕ} (χ : DirichletCharacter ℂ N) : ℤ → ℂ := fun d => χ (d : ZMod N)

structure Prim (k N : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) : Prop where
  cf : CF k N (ch χ) g
  one : g 1 = 1
  zero : ∀ n : ℕ, ¬ n.Coprime N → g n = 0
  eig : ∀ q : ℕ, q.Prime → ¬ q ∣ N → To k (ch χ q) q g = fun n => g q * g n

structure Wt (L : ℕ) (ρ : ℍ → ℝ) : Prop where
  meas : Measurable ρ
  nonneg : ∀ τ, 0 ≤ ρ τ
  sum : ∀ τ, HasSum (fun γ : Gamma0 L => ρ ((γ : SL(2, ℤ)) • τ)) 1
  supp : ∃ S : Finset SL(2, ℤ), ∀ τ, ρ τ ≠ 0 → ∃ γ ∈ S, γ • τ ∈ ModularGroup.fd

def pet (k : ℕ) (ρ : ℍ → ℝ) (h f : ℍ → ℂ) : ℂ := ∫ τ : ℍ, (ρ τ : ℂ) * (conj (h τ) * f τ * (τ.im : ℂ) ^ k)

structure EigF (k N l : ℕ) (ε : DirichletCharacter ℂ N) (t : ℕ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) : Prop where
  T : ∀ a, MF k (N * l) (ch ε) a → ∀ q : ℕ, q.Prime → ¬ q ∣ N * l → lam B c (To k (ch ε q) q a) = t q * lam B c a
  U : ∀ a, MF k (N * l) (ch ε) a → lam B c (Uo l a) = α * lam B c a

def trm (j : ℕ) (s : ℝ) (z : ℂ) : ℂ := (z ^ j)⁻¹ * ((‖z‖ ^ (-2 * s) : ℝ) : ℂ)

def dif (L : ℕ) (v : ℤ × ℤ) (F : ℤ × ℤ → ℂ) : ℤ × ℤ → ℂ := fun x =>
  F x - (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L, F (x + (r : ℤ) • v)

def lat (j : ℕ) (s : ℝ) (L : ℕ) (v : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) (τ : ℍ) : ℂ :=
  ∑' x : ℤ × ℤ, Φ x * dif L v (dif L v fun y => trm j s ((y.1 : ℂ) * τ + y.2)) x

end GlobalTheory.EisM

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.PsType

section Abstract

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def IsEig (π : Representation ℂ G V) (H : Set G) (θ : G → ℂ) (v : V) : Prop := ∀ h ∈ H, π h v = θ h • v

def aug (π : Representation ℂ G V) (H : Set G) (θ : G → ℂ) : Submodule ℂ V :=
  Submodule.span ℂ {x | ∃ h ∈ H, ∃ w : V, x = π h w - θ h • w}

structure Datum [TopologicalSpace G] (H : Set G) (θ : G → ℂ) : Prop where
  one : (1 : G) ∈ H
  mul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H
  inv : ∀ a ∈ H, a⁻¹ ∈ H
  compact : IsCompact H
  val_one : θ 1 = 1
  val_mul : ∀ a ∈ H, ∀ b ∈ H, θ (a * b) = θ a * θ b
  near : ∃ U ∈ nhds (1 : G), ∀ g ∈ U, g ∈ H → θ g = 1

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def Triv (χ : kˣ →* ℂˣ) (x : k) : Prop :=
  ∀ u : kˣ, valuation k (u : k) = 1 → valuation k ((u : k) - 1) ≤ valuation k x → χ u = 1

def Ordered (ψ : Fin n → kˣ →* ℂˣ) : Prop :=
  ∀ i a b j : Fin n, i ≤ a → a ≤ b → b ≤ j → ∀ x : k, Triv (ψ i / ψ j) x → Triv (ψ a / ψ b) x

def grp (ψ : Fin n → kˣ →* ℂˣ) : Set (GL (Fin n) k) :=
  {g | g ∈ KO k (Fin n) ∧ ∀ i j : Fin n, i < j → Triv (ψ i / ψ j) (g.val i j)}


open Classical in
def ev (χ : kˣ →* ℂˣ) (x : k) : ℂ :=
  if h : valuation k x = 1 then (χ (Units.mk0 x fun h0 => by simp [h0] at h) : ℂ) else 1

def nxt (ψ : Fin n → kˣ →* ℂˣ) (m : Fin n) : kˣ →* ℂˣ :=
  if h : (m : ℕ) + 1 < n then ψ ⟨(m : ℕ) + 1, h⟩ else 1

def minor (g : GL (Fin n) k) (m : Fin n) : k := (g.val.toSquareBlockProp fun i => i ≤ m).det

def theta (ψ : Fin n → kˣ →* ℂˣ) (g : GL (Fin n) k) : ℂ := ∏ m, ev (ψ m / nxt ψ m) (minor g m)

def HasVec {V : Type} [AddCommGroup V] [Module ℂ V] (ψ : Fin n → kˣ →* ℂˣ) (π : Representation ℂ (GL (Fin n) k) V) : Prop :=
  ∃ v : V, v ≠ 0 ∧ IsEig π (grp ψ) (theta ψ) v

def Agree (ψ ω : Fin n → kˣ →* ℂˣ) : Prop := ∀ i (u : kˣ), valuation k (u : k) = 1 → ψ i u = ω i u

def strip (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k) (m : ℕ) : Set (GL (Fin n) k) :=
  {g | ∀ i j : Fin n, if (i : ℕ) < r ∧ r ≤ (j : ℕ) then
      valuation k (ϖ ^ m * g.val i j) ≤ 1 ∧ Triv (ψ i / ψ j) (ϖ ^ m * g.val i j)
    else g.val i j = (1 : Matrix (Fin n) (Fin n) k) i j}

def Cut (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) : Prop := ∀ i j : Fin n, (i : ℕ) < r → r ≤ (j : ℕ) → ¬ Triv (ψ i / ψ j) 1

end GlobalTheory.PsType
end
end

section

noncomputable section

namespace GlobalTheory.AlmostEt

section General

variable {A S M : Type*} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M]

structure IsDerOn (B : Subalgebra A S) (D : S → M) : Prop where
  add : ∀ x ∈ B, ∀ y ∈ B, D (x + y) = D x + D y
  mul : ∀ x ∈ B, ∀ y ∈ B, D (x * y) = x • D y + y • D x
  alg : ∀ a : A, D (algebraMap A S a) = 0

structure IsTrData (B C : Subalgebra A S) (tr : S → S) {n : ℕ} (a b : Fin n → S) (e : S) : Prop where
  le : B ≤ C
  e_mem : e ∈ B
  a_mem : ∀ i, a i ∈ C
  b_mem : ∀ i, b i ∈ C
  tr_mem : ∀ x ∈ C, tr x ∈ B
  tr_add : ∀ x ∈ C, ∀ y ∈ C, tr (x + y) = tr x + tr y
  tr_mul : ∀ β ∈ B, ∀ x ∈ C, tr (β * x) = β * tr x
  left : ∀ x ∈ C, ∑ i, a i * tr (b i * x) = e * x
  right : ∀ x ∈ C, ∑ i, b i * tr (a i * x) = e * x
  sum : ∑ i, a i * b i = e

end General

section Tower

open GlobalTheory.K5

variable {p : ℕ} [Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

theorem qq_pow (T : Tower p Ω) (n : ℕ) : T.qq n ^ (p ^ n) = algebraMap (O0 p) Ω (qO p) := by
  induction n with
  | zero => simpa using T.q0
  | succ n ih => rw [pow_succ', pow_mul, T.qpow, ih]

def zS (T : Tower p Ω) (n : ℕ) : integralClosure (O0 p) Ω :=
  ⟨T.ζ n, IsIntegral.of_pow (pow_pos (Fact.out : p.Prime).pos n) (by
    rw [(T.prim n).pow_eq_one]; exact isIntegral_one)⟩

def qS (T : Tower p Ω) (n : ℕ) : integralClosure (O0 p) Ω :=
  ⟨T.qq n, IsIntegral.of_pow (pow_pos (Fact.out : p.Prime).pos n) (by
    rw [qq_pow]; exact isIntegral_algebraMap)⟩

def levelAlg (T : Tower p Ω) (n : ℕ) : Subalgebra (O0 p) (integralClosure (O0 p) Ω) :=
  Algebra.adjoin (O0 p) {zS T n, qS T n}

def towerAlg (T : Tower p Ω) : Subalgebra (O0 p) (integralClosure (O0 p) Ω) :=
  Algebra.adjoin (O0 p) (Set.range (zS T) ∪ Set.range (qS T))

abbrev Frac (p : ℕ) [Fact p.Prime] (Ω : Type*) [Field Ω] [Algebra (O0 p) Ω] : Type _ :=
  Ω ⧸ LinearMap.range (Algebra.linearMap (integralClosure (O0 p) Ω) Ω)

end Tower

end GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt.Inhab

section General

variable {A S M : Type*} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M]

end General

section Examples

end Examples

section Tower

open GlobalTheory.K5

variable {p : ℕ} [Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

end Tower

end GlobalTheory.AlmostEt.Inhab
end
end

section

open MvPolynomial Formalism.DegreeFormula

noncomputable section

namespace GlobalTheory.FlagPoly

abbrev Pol (ι : Type) (N : ℕ) : Type := MvPolynomial (ι × Fin N) ℝ

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

def pLow (j : ℕ) (τ : ι) (k : ℕ) : Pol ι N :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), X (τ, i) ^ k

def pHigh (j : ℕ) (τ : ι) (k : ℕ) : Pol ι N :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => j ≤ (i : ℕ)), X (τ, i) ^ k

def ev (lam : ι → Fin N → ℝ) (P : Pol ι N) : ℝ := eval (fun x => lam x.1 x.2) P

def lamA (ι : Type) [Fintype ι] (N j : ℕ) : Pol ι N := ∑ τ : ι, (pHigh j τ 1 - pLow j τ 1)

def fibPt (ι : Type) [Fintype ι] (N j : ℕ) : Pol ι N :=
  ∏ x : ι × Fin N, (-X x) ^ (if (x.2 : ℕ) < j then j - 1 - (x.2 : ℕ) else N - 1 - (x.2 : ℕ))

def dimGr (ι : Type) [Fintype ι] (N j : ℕ) : ℕ := Fintype.card ι * (j * (N - j))

def curveCl (ι : Type) [Fintype ι] (N j : ℕ) : Pol ι N := lamA ι N j ^ (dimGr ι N j - 1) * fibPt ι N j

end GlobalTheory.FlagPoly
end
end
