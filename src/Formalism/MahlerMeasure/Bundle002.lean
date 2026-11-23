module

public import Formalism.MahlerMeasure.Bundle001
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.NumberTheory.Padics.PadicNumbers
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace Formalism.GM.M

open MvPolynomial Finset

noncomputable def fockK {k σ : Type} [Field k] (F G : MvPolynomial σ k) : k :=
  ∑ m ∈ F.support, F.coeff m * G.coeff m * (m.prod fun _ j => (j.factorial : k))

noncomputable def tieEh {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (zv sv : σ) :
    MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  LinearMap.mulLeft k (X zv * X sv + ∑ c, X (w c) * X (e c))

noncomputable def tieFh {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (zv sv : σ) :
    MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  (pderiv zv).toLinearMap ∘ₗ (pderiv sv).toLinearMap + Formalism.GM.tieF w e

noncomputable def tieP {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ)
    (y : MvPolynomial σ k) : MvPolynomial σ k :=
  ∑ l ∈ range (o + 1),
    (((-1 : k) ^ l) / (((l.factorial : k) ^ 2) * ((o + n + r + z - 1).choose l : k))) •
      ((tieEh w e zv sv) ^ l) (((Formalism.GM.tieF w e) ^ l) (X zv ^ z * y))

def TieVars {σ : Type} {r : ℕ} (w e : Fin r → σ) (zv sv : σ) : Prop :=
  Function.Injective w ∧ Function.Injective e ∧ (∀ c d, w c ≠ e d) ∧ (∀ c, w c ≠ zv ∧ w c ≠ sv ∧ e c ≠ zv ∧
    e c ≠ sv) ∧ zv ≠ sv

def ZSFree {k σ : Type} [Field k] (zv sv : σ) (y : MvPolynomial σ k) : Prop :=
  ∀ m ∈ y.support, m zv = 0 ∧ m sv = 0

end Formalism.GM.M
end

section

namespace Formalism.GM.M

open MvPolynomial Finset

structure Letters (N : ℕ) where
  vec : Fin N → Bool
  deg : Fin N → ℕ

def MultiDeg {N r : ℕ} (LL : Letters N) (m : Fin N × Fin r →₀ ℕ) : Prop :=
  ∀ i, ∑ c, m (i, c) = LL.deg i

noncomputable def Pol (p : ℕ) [Fact p.Prime] (r : ℕ) {N : ℕ} (LL : Letters N) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  MvPolynomial.restrictSupport ℚ_[p] {m | MultiDeg LL m}

noncomputable def IntPol (p : ℕ) [Fact p.Prime] (σ : Type) :
    Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]) :=
  LinearMap.range (MvPolynomial.mapAlgHom (Algebra.ofId ℤ_[p] ℚ_[p]) :
    MvPolynomial σ ℤ_[p] →ₐ[ℤ_[p]] MvPolynomial σ ℚ_[p]).toLinearMap

noncomputable def PolZ (p : ℕ) [Fact p.Prime] (r : ℕ) {N : ℕ} (LL : Letters N) :
    Submodule ℤ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  (Pol p r LL).restrictScalars ℤ_[p] ⊓ IntPol p (Fin N × Fin r)

noncomputable def glAct (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (j : ℕ) (c d : Fin r) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  ∑ i : Fin N,
    if (i : ℕ) < j then
      (if LL.vec i then (LinearMap.mulLeft ℚ_[p] (X (i, c))) ∘ₗ (pderiv (i, d)).toLinearMap
       else -((LinearMap.mulLeft ℚ_[p] (X (i, d))) ∘ₗ (pderiv (i, c)).toLinearMap))
    else 0

def wt {N r : ℕ} (LL : Letters N) (j : ℕ) (c : Fin r) (m : Fin N × Fin r →₀ ℕ) : ℤ :=
  ∑ i : Fin N, if (i : ℕ) < j then (if LL.vec i then (m (i, c) : ℤ) else -(m (i, c) : ℤ)) else 0

def GlStable (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (j : ℕ)
    (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) : Prop :=
  ∀ c d, ∀ x ∈ S, glAct p LL j c d x ∈ S

noncomputable def gSpan (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (j : ℕ)
    (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  sInf {S | F ∈ S ∧ GlStable p LL j S}

noncomputable def YCond (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (M : WithTop ℤ) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  sSup {S | S ≤ MvPolynomial.restrictSupport ℚ_[p] {m | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ M} ∧
    GlStable p LL j S}

noncomputable def Y (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (LL : Letters N) {q : ℕ}
    (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  Pol p r LL ⊓ ⨅ k, YCond p LL (J k) (M k)

noncomputable def YZ (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (LL : Letters N) {q : ℕ}
    (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) : Submodule ℤ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  (Y p LL J M).restrictScalars ℤ_[p] ⊓ PolZ p r LL

noncomputable def fock (p : ℕ) [Fact p.Prime] {σ : Type} (F G : MvPolynomial σ ℚ_[p]) : ℚ_[p] :=
  ∑ m ∈ F.support, F.coeff m * G.coeff m * (m.prod fun _ k => (k.factorial : ℚ_[p]))

noncomputable def fockN (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N)
    (F G : MvPolynomial (Fin N × Fin r) ℚ_[p]) : ℚ_[p] :=
  fock p F G / ∏ i, ((LL.deg i).factorial : ℚ_[p])

noncomputable def tiePhiAt (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (a : Fin N) (b : Fin N) (z : ℕ) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  Formalism.GM.tiePhi (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)) (LL.deg a) (LL.deg b) z

structure TieData where
  t : ℕ
  pos : Fin t → ℕ
  z : Fin t → ℕ
  q : ℕ
  J : Fin q → ℕ
  thr : Fin q → WithTop ℤ

def TieData.Admissible {N : ℕ} (LL : Letters N) (T : TieData) : Prop :=
  StrictMono T.pos ∧
  (∀ i, ∃ h : T.pos i + 1 < N, LL.vec ⟨T.pos i, by omega⟩ = true ∧ LL.vec ⟨T.pos i + 1, h⟩ = false) ∧
  (∀ i, ∃ k, T.J k = T.pos i + 1)

noncomputable def TieData.phi (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (T : TieData) (i : Fin T.t) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  if h : T.pos i + 1 < N then tiePhiAt p LL ⟨T.pos i, by omega⟩ ⟨T.pos i + 1, h⟩ (T.z i) else LinearMap.id

def TieData.S {N : ℕ} (LL : Letters N) (T : TieData) (i : Fin T.t) : ℕ :=
  ∑ a : Fin N, if (a : ℕ) ≤ T.pos i then LL.deg a else 0

noncomputable def goodCount (p : ℕ) [Fact p.Prime] {Vs : Type} [AddCommGroup Vs] [Module ℤ_[p] Vs]
    (be : Vs → Vs → ℚ_[p]) (L : Submodule ℤ_[p] Vs) (D : ℤ) : ℕ :=
  sSup {n | ∃ x y : Fin n → Vs, (∀ i, x i ∈ L) ∧ (∀ i, y i ∈ L) ∧
    ∀ i j, be (x i) (y j) = if i = j then (p : ℚ_[p]) ^ D else 0}

noncomputable def bad (p : ℕ) [Fact p.Prime] {Vs : Type} [AddCommGroup Vs] [Module ℤ_[p] Vs]
    (be : Vs → Vs → ℚ_[p]) (L : Submodule ℤ_[p] Vs) (D : ℤ) : ℕ :=
  Module.finrank ℤ_[p] L - goodCount p be L D

end Formalism.GM.M
end

section

namespace Formalism.GM

open Finset Polynomial

noncomputable def gaussR {K : Type} [NormedField K] (ρ : NNReal) (P : K[X]) : NNReal :=
  P.support.sup (fun k => ‖P.coeff k‖₊ * ρ ^ k)

def GaussMulRad : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ρ : NNReal) (P Q : K[X]), 0 < ρ →
    gaussR ρ (P * Q) = gaussR ρ P * gaussR ρ Q

noncomputable def binK (K : Type) [Field K] (k : ℕ) : K[X] :=
  Polynomial.C (((k.factorial : K))⁻¹) * descPochhammer K k

def MahlerK : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] (h k : ℕ) (t₀ : ℤ), k ≤ p ^ h →
    ∀ m : ℕ, ‖((binK K k).comp (Polynomial.C ((p : K) ^ h) * X + Polynomial.C (t₀ : K))).coeff m‖ ≤ 1

def SmithZp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ_[p]),
    ∃ (U V : Matrix (Fin n) (Fin n) ℤ_[p]) (d : Fin n → ℤ_[p]),
      IsUnit U.det ∧ IsUnit V.det ∧ M = U * Matrix.diagonal d * V

noncomputable def binMatK (K : Type) [Field K] {n : ℕ} (del₀ : ℕ) (c : Fin n → Fin n → ℕ → K) :
    Matrix (Fin n) (Fin n) K[X] :=
  fun i j => ∑ k ∈ range (del₀ + 1), Polynomial.C (c i j k) * binK K k


open Classical in
def ValuationWindowLowerBound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (n del₀ h : ℕ) (E : ℝ) (c : Fin n → Fin n → ℕ → K) (lead : K) (roots : Multiset K) (t₀ : ℤ)
    (U V : Matrix (Fin n) (Fin n) K) (d : Fin n → K),
    (∀ i j k, ‖c i j k‖ ≤ 1) → (∀ i j, ‖U i j‖ ≤ 1) → (∀ i j, ‖V i j‖ ≤ 1) →
    ‖U.det‖ = 1 → ‖V.det‖ = 1 → 0 ≤ E → del₀ ≤ p ^ h → lead ≠ 0 →
    (binMatK K del₀ c).det = Polynomial.C lead * (roots.map (fun ζ => X - Polynomial.C ζ)).prod →
    (binMatK K del₀ c).map (Polynomial.eval (t₀ : K)) = U * Matrix.diagonal d * V →
    ((univ.filter (fun i => ‖d i‖ ≤ (p : ℝ) ^ (-E))).card : ℝ) * E ≤
      (-Real.logb p ‖lead‖ + (roots.map (fun ζ => vmin p h ((t₀ : K) - ζ))).sum) +
        E * ((roots.filter (fun ζ => ‖(t₀ : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)))).card : ℝ)


end Formalism.GM
end

section

namespace Formalism.GM.M

open MvPolynomial Finset

def IsIntegral' {σ : Type} (p : ℕ) [Fact p.Prime] (u : MvPolynomial σ ℚ_[p]) : Prop :=
  ∀ m, ‖u.coeff m‖ ≤ 1

def PhiInt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (r : ℕ) (w e : Fin r → σ), Function.Injective w → Function.Injective e →
    (∀ c d, w c ≠ e d) → 1 ≤ r →
    ∀ (o n z : ℕ) (u : MvPolynomial σ ℚ_[p]), IsIntegral' p u →
      IsIntegral' p (((p : ℚ_[p]) ^ ((r + 1) * (Nat.log p (o + n + r + z) + 1))) • Formalism.GM.tiePhi w e o n z u)

end Formalism.GM.M
end
