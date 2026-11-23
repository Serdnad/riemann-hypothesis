module

public import Formalism.MahlerMeasure.Bundle003
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

def HasOrder {σ : Type} {p : ℕ} [Fact p.Prime] (v : σ) (e : ℕ) (f : MvPolynomial σ ℚ_[p]) : Prop :=
  (∀ m ∈ f.support, e ≤ m v) ∧ ∃ m ∈ f.support, m v = e

noncomputable def initPart {σ : Type} {p : ℕ} [Fact p.Prime] (v : σ) (e : ℕ) (f : MvPolynomial σ ℚ_[p]) :
    MvPolynomial σ ℚ_[p] :=
  ∑ m ∈ f.support, if m v = e then monomial m (f.coeff m) else 0

noncomputable def tieGam (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters (N + 1)) (ρ : Fin r) (z n : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) : ℚ_[p] :=
  (((LL.deg (Fin.last N) + n + r + z - 1).choose (LL.deg (Fin.last N)) : ℕ) : ℚ_[p]) *
    fock p (tiePhiAt p (LL.snoc n) (Fin.castSucc (Fin.last N)) (Fin.last (N + 1)) z (freeze p LL ρ n f))
      (freeze p LL ρ n f') /
    ((((n - LL.total).factorial * LL.total.factorial : ℕ) : ℚ_[p]) * ∏ i, ((LL.deg i).factorial : ℚ_[p]))

def GamDeg : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters (N + 1)) (ρ : Fin r) (z e e' : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]),
    1 ≤ r → LL.vec (Fin.last N) = true → f ∈ Pol p r LL → f' ∈ Pol p r LL →
    HasOrder (Fin.last N, ρ) e f → HasOrder (Fin.last N, ρ) e' f' →
    ∃ P : Polynomial ℚ_[p], P.natDegree ≤ LL.total + LL.deg (Fin.last N) - max e e' ∧
      ∀ n, LL.total ≤ n → tieGam p LL ρ z n f f' = P.eval (n : ℚ_[p])

def GamLead : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters (N + 1)) (ρ : Fin r) (z e : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) (P : Polynomial ℚ_[p]),
    1 ≤ r → LL.vec (Fin.last N) = true → f ∈ Pol p r LL → f' ∈ Pol p r LL →
    HasOrder (Fin.last N, ρ) e f → HasOrder (Fin.last N, ρ) e f' →
    (∀ n, LL.total ≤ n → tieGam p LL ρ z n f f' = P.eval (n : ℚ_[p])) →
    P.coeff (LL.total + LL.deg (Fin.last N) - e) =
      ((e.factorial * (z + e).choose e : ℕ) : ℚ_[p]) *
        fock p (initPart (Fin.last N, ρ) e f) (initPart (Fin.last N, ρ) e f') /
        ((((LL.deg (Fin.last N)).factorial * LL.total.factorial : ℕ) : ℚ_[p]) *
          ∏ i, ((LL.deg i).factorial : ℚ_[p]))

end Formalism.GM.M
end

section

namespace Formalism.GM.M

open MvPolynomial Finset

variable {N r : ℕ}

def BlockData.BlockOK (D : BlockData N) : Prop :=
  D.T.Admissible D.LL ∧ (∀ i, D.T.pos i + 1 < (D.uPos : ℕ)) ∧ D.LL.vec D.uPos = true ∧ (D.uPos : ℕ) + 1 = N

def BlockData.letterAt (D : BlockData N) (k : ℕ) : Fin N :=
  ⟨min k (N - 1), by
    rcases Nat.eq_zero_or_pos N with h | h
    · exact absurd D.uPos.2 (by omega)
    · omega⟩

noncomputable def BlockData.phiAll (p : ℕ) [Fact p.Prime] (D : BlockData N) (j : Fin D.T.t → ℕ) (jp : ℕ) :
    MvPolynomial (BVar N r D.T.t) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
  Formalism.GM.tiePhi (fun c => Sum.inl (Fin.castSucc D.uPos, c)) (fun c => xiVar N r D.T.t c)
            (D.LL.deg D.uPos - jp) (D.B - jp) D.zPlus ∘ₗ
    (List.finRange D.T.t).foldr (fun i acc =>
      Formalism.GM.tiePhi (fun c => Sum.inl (finPos N (D.T.pos i), c)) (fun c => Sum.inl (finPos N (D.T.pos i + 1), c))
        ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i))) ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1)))
        (D.T.z i) ∘ₗ acc) LinearMap.id

def SSDirect : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N), D.BlockOK → 1 ≤ r →
    iSupIndep (fun ij : {ij : (Fin D.T.t → ℕ) × ℕ // D.LevelOK ij.1 ij.2} =>
      Submodule.span ℚ_[p] (D.gens p (r := r) ij.1.1 ij.1.2)) ∧
    ∀ x, x ∈ Submodule.span ℚ_[p] (D.SSZ p (r := r) : Set (MvPolynomial (BVar N r D.T.t) ℚ_[p])) →
      x ∈ IntPol p (BVar N r D.T.t) → x ∈ D.SSZ p (r := r)

def LevelLattice : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N) (a : ℕ), D.BlockOK → 1 ≤ r → 1 ≤ a →
    (∀ x, D.LL.deg x ≤ 2 * a) → D.B ≤ 2 * a → (∀ i, D.T.z i ≤ 2 * a) → D.zPlus ≤ 2 * a →
    (∀ (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t), ∀ y ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
      Formalism.GM.tieF (fun c => (D.letterAt (D.T.pos i), c)) (fun c => (D.letterAt (D.T.pos i + 1), c)) y ∈
        Y p (r := r) (D.lettersAt (Function.update j i (j i + 1)) jp) D.T.J D.T.thr) →
    (∀ (j : Fin D.T.t → ℕ) (jp : ℕ) (c : Fin r), ∀ y ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
      pderiv (D.uPos, c) y ∈ Y p (r := r) (D.lettersAt j (jp + 1)) D.T.J D.T.thr) →
    Submodule.span ℚ_[p] (D.SSZ p (r := r) : Set (MvPolynomial (BVar N r D.T.t) ℚ_[p])) =
        Submodule.span ℚ_[p] (D.PSZ p (r := r) : Set (MvPolynomial (BVar N r D.T.t) ℚ_[p])) ∧
      (∀ x ∈ D.SSZ p (r := r),
        ((p : ℚ_[p]) ^ ((D.T.t + 1) * ⌈((r : ℝ) + 1) * lgV2 p a r⌉₊)) • x ∈ D.PSZ p (r := r)) ∧
      (∀ x ∈ D.PSZ p (r := r),
        ((p : ℚ_[p]) ^ ((D.T.t + 1) * ⌈((r : ℝ) + 1) * lgV2 p a r⌉₊)) • x ∈ D.SSZ p (r := r))

def FockBlocks : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N), D.BlockOK → 1 ≤ r →
    (∀ (j j' : Fin D.T.t → ℕ) (jp jp' : ℕ), D.LevelOK j jp → D.LevelOK j' jp' → (j, jp) ≠ (j', jp') →
      ∀ y ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr, ∀ y' ∈ Y p (r := r) (D.lettersAt j' jp') D.T.J D.T.thr,
      ∀ g ∈ XiPolZ p N r D.T.t (D.B - jp), ∀ g' ∈ XiPolZ p N r D.T.t (D.B - jp'),
        fockK ((∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
            D.Pall p (r := r) j jp (rename (chainEmb N r D.T.t) y * g))
          ((∏ i, D.Ehat p (r := r) i ^ j' i) * D.Eplus p (r := r) ^ jp' *
            D.Pall p (r := r) j' jp' (rename (chainEmb N r D.T.t) y' * g')) = 0) ∧
    (∀ (j : Fin D.T.t → ℕ) (jp : ℕ), D.LevelOK j jp →
      ∀ y ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr, ∀ y' ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
      ∀ g ∈ XiPolZ p N r D.T.t (D.B - jp), ∀ g' ∈ XiPolZ p N r D.T.t (D.B - jp),
        fockK ((((∏ i, ((j i).factorial : ℚ_[p])) * (jp.factorial : ℚ_[p]))⁻¹) •
            ((∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
              D.Pall p (r := r) j jp (rename (chainEmb N r D.T.t) y * g)))
          ((((∏ i, ((j i).factorial : ℚ_[p])) * (jp.factorial : ℚ_[p]))⁻¹) •
            ((∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
              D.Pall p (r := r) j jp (rename (chainEmb N r D.T.t) y' * g'))) =
          (∏ i, ((((D.lettersAt j jp).deg (D.letterAt (D.T.pos i)) +
                (D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1)) + r + D.T.z i + 1 + j i - 1).choose (j i) *
              (D.T.z i).factorial : ℕ) : ℚ_[p])) *
            ((((D.LL.deg D.uPos - jp) + (D.B - jp) + r + D.zPlus + 1 + jp - 1).choose jp *
              D.zPlus.factorial : ℕ) : ℚ_[p]) *
            fockK (rename (chainEmb N r D.T.t) y * g)
              (D.phiAll p (r := r) j jp (rename (chainEmb N r D.T.t) y' * g')))

end Formalism.GM.M
end
