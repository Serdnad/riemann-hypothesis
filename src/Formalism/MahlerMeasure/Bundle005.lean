module

public import Formalism.MahlerMeasure.Bundle003
import Formalism.MahlerMeasure.MahlerMeasureProofs.GaussRad
import Formalism.MahlerMeasure.MahlerMeasureProofs.LieMat
import Formalism.MahlerMeasure.MahlerMeasureProofs.LieRoots
import Formalism.MahlerMeasure.MahlerMeasureProofs.MahlerK
public import Formalism.MahlerMeasure.MahlerMeasureProofs.Bundle002
public import Formalism.MahlerMeasure.Bundle004
public import Formalism.MahlerMeasure.MahlerMeasureProofs.GamDeg
import Formalism.MahlerMeasure.MahlerMeasureProofs.GamLead
public import Formalism.MahlerMeasure.CsSaturated
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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

namespace Formalism.GM.Top
open Formalism.GM
theorem smithZp : SmithZp := smith_form_p_adic_integers
theorem lieMat : LieMat := lieMat_of mahler_binomial_unit_ball
theorem lieRoots : LieRoots := lieRoots_of gauss_norm_multiplicative
theorem valuation_window_lower_bound : ValuationWindowLowerBound := by
  intro p _ K _ _ _ n del₀ h E c lead roots t₀ U V d hc hU hV hUd hVd hE hdel hlead hdet hsm
  exact lieRoots p K h _ E _ lead roots t₀ hE hlead hdet
    (lieMat p K n del₀ h E c t₀ U V d hc hU hV hUd hVd hE hdel hsm)
end Formalism.GM.Top
end

section

namespace Formalism.GM.Top
open Formalism.GM
theorem gamDeg : M.GamDeg := gamma_degree_bound
theorem gamLead : M.GamLead := gamma_leading_term
end Formalism.GM.Top
end

section

namespace Formalism.GM.M

open MvPolynomial Finset

def Letters.takeD {N : ℕ} (LL : Letters N) (k : ℕ) : Letters k where
  vec := fun i => if h : (i : ℕ) < N then LL.vec ⟨i, h⟩ else false
  deg := fun i => if h : (i : ℕ) < N then LL.deg ⟨i, h⟩ else 0


open Classical in
noncomputable def Letters.setTies {N : ℕ} (LL : Letters N) (T : TieData) (n : Fin T.t → ℕ) : Letters N where
  vec := LL.vec
  deg := fun a => if h : ∃ i, T.pos i + 1 = (a : ℕ) then n (Classical.choose h) else LL.deg a

def TieData.thrUpTo (T : TieData) (i : Fin T.t) : Fin T.q → WithTop ℤ :=
  fun k => if T.J k ≤ T.pos i + 1 then T.thr k else ⊤

noncomputable def TieData.phis (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (T : TieData) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  (List.finRange T.t).foldr (fun i acc => (T.phi p LL i) ∘ₗ acc) LinearMap.id

noncomputable def TieData.Ffull (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero N] (LL : Letters N) (T : TieData) (i : Fin T.t)
    (ρ : Fin r) (n : ℕ) (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) : MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  rename (fun x : Fin (T.pos i + 1 + 1) × Fin r =>
      (if h : (x.1 : ℕ) < N then (⟨x.1, h⟩ : Fin N) else ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩, x.2))
    (freeze p (LL.takeD (T.pos i + 1)) ρ n f)

noncomputable def TieData.YYsp (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero N] [NeZero r] (LL : Letters N) (T : TieData)
    (i : Fin T.t) (ρ : Fin r) (n : Fin T.t → ℕ) (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  Y p (LL.setTies T n) T.J T.thr ⊓
    Submodule.span ℚ_[p] {x | ∃ g ∈ gSpan p (LL.setTies T n) (T.pos i + 2) (T.Ffull p (LL.setTies T n) i ρ (n i) f),
      ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | T.pos i + 2 ≤ (v.1 : ℕ)}, x = g * q}

def WeightSpaceDimMonotone : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r] (LL : Letters N) (T : TieData), T.Admissible LL →
    ∀ (ρ : Fin r), (ρ : ℕ) = r - 1 → 2 ≤ r → ∀ (i : Fin T.t) (n : Fin T.t → ℕ) (w : Fin r → ℤ)
      (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]),
      f ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w → f ≠ 0 →
      ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i →
      ∀ n' : ℕ, n i ≤ n' →
        Module.finrank ℚ_[p] (T.YYsp p LL i ρ n f) ≤
          Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i n') f)

def MonoCount : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r] (LL : Letters N) (T : TieData), T.Admissible LL →
    ∀ (ρ : Fin r), (ρ : ℕ) = r - 1 → 2 ≤ r → ∀ (i : Fin T.t) (n : Fin T.t → ℕ),
      ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i →
      ∀ fw : (Fin r → ℤ) → MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p],
        (∀ w, fw w ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ∧
          (MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ≠ ⊥ → fw w ≠ 0)) →
        ∑ᶠ w, Module.finrank ℚ_[p] (MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) *
            Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw w)) =
          Module.finrank ℚ_[p] (Y p (r := r) (LL.setTies T n) T.J T.thr)

end Formalism.GM.M
end

section

namespace Formalism.GM.M

open MvPolynomial Finset

def HypP (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (ρ : Fin r) (e1 : ℕ) : Prop :=
  (∀ j ≤ N, ∀ Cs : Finset (Fin r), (Cs = univ ∨ Cs = univ.erase ρ) → ∀ T : Set (Fin r → ℤ), CsSaturated Cs T →
    ∃ P, IsTypeProj p LL j Cs T P ∧ (∀ F G, fock p (P F) G = fock p F (P G)) ∧
      ∀ F ∈ PolZ p r LL, ((p : ℚ_[p]) ^ e1) • P F ∈ IntPol p (Fin N × Fin r)) ∧
  (∀ (j j' : ℕ) (Cs Cs' : Finset (Fin r)) (T T' : Set (Fin r → ℤ)) (P P'), j ≤ j' → Cs' ⊆ Cs →
    (Cs = univ ∨ Cs = univ.erase ρ) → (Cs' = univ ∨ Cs' = univ.erase ρ) →
    IsTypeProj p LL j Cs T P → IsTypeProj p LL j' Cs' T' P' → P ∘ₗ P' = P' ∘ₗ P)

def HypW (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (e1 : ℕ) : Prop :=
  ∀ j ≤ N, ∀ la : Fin r → ℤ, ∀ x ∈ IsoC p LL j univ la ⊓ Pol p r LL, x ∈ IntPol p (Fin N × Fin r) →
    ((p : ℚ_[p]) ^ e1) • x ∈ ⨆ (h : MvPolynomial (Fin N × Fin r) ℚ_[p])
      (_ : h ∈ HWC p LL j univ la ⊓ Pol p r LL ∧ h ∈ IntPol p (Fin N × Fin r)), WeylLat p LL j h

def HypE (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (ρ : Fin r) (e1 : ℕ) : Prop :=
  ∀ j ≤ N, ∀ la : Fin r → ℤ, ∃ P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p],
    P ∘ₗ P = P ∧ LinearMap.range P = HWC p LL j (univ.erase ρ) la ⊓ WtSpC p LL j univ la ∧
    LinearMap.ker P ⊓ WtSpC p LL j univ la =
      (⨆ (c : Fin r) (d : Fin r) (_ : c ∈ univ.erase ρ ∧ d ∈ univ.erase ρ ∧ d < c),
        Submodule.map (glAct p LL j c d) ⊤) ⊓ WtSpC p LL j univ la ∧
    (∀ F G, F ∈ WtSpC p LL j univ la → G ∈ WtSpC p LL j univ la → fock p (P F) G = fock p F (P G)) ∧
    ∀ F ∈ PolZ p r LL, F ∈ WtSpC p LL j univ la → ((p : ℚ_[p]) ^ e1) • P F ∈ IntPol p (Fin N × Fin r)

def GramDeterminantGradedHypothesis (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (κ : ℝ) : Prop :=
  ∀ (w : Fin r → ℤ) (e k : ℕ) (g : Fin k → MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]),
    LinearIndependent ℤ_[p] g → Submodule.span ℤ_[p] (Set.range g) = grLat p LLw J M ρ w (Fin.last K, ρ) e →
    (p : ℝ) ^ (-(κ * k)) ≤ ‖(Matrix.of fun a b => fock p (g a) (g b) / ∏ i, ((LLw.deg i).factorial : ℚ_[p])).det‖

def BadCrit : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Vs : Type) [AddCommGroup Vs] [Module ℚ_[p] Vs] [Module ℤ_[p] Vs]
    [IsScalarTower ℤ_[p] ℚ_[p] Vs]
    (be : Vs →ₗ[ℚ_[p]] Vs →ₗ[ℚ_[p]] ℚ_[p]) (L L₁ : Submodule ℤ_[p] Vs) (D : ℤ),
    Module.Finite ℤ_[p] L → L₁ ≤ L →
    (∀ (a : ℤ_[p]) (x : Vs), a ≠ 0 → x ∈ L → a • x ∈ L₁ → x ∈ L₁) →
    (∀ u ∈ L₁, (∀ (a : ℤ_[p]) (x : Vs), x ∈ L₁ → u = a • x → IsUnit a) →
      ∃ u' ∈ L, (p : ℝ) ^ (-D) ≤ ‖be u u'‖) →
    bad p (fun x y => be x y) L D ≤ Module.finrank ℤ_[p] L - Module.finrank ℤ_[p] L₁

end Formalism.GM.M
end
