module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle003
public import Formalism.FrobeniusBaseCase.Statement
public import Formalism.LocalToGlobal.CharacterGerms.Bundle004
public import Mathlib.Algebra.Field.ZMod
public import Formalism.LocalToGlobal.CharacterGerms.RowTieDefs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

variable {C : Type} [Field C]

section OneGroup

variable {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]

def LatticeInclusionFormsInjective (X : Cart V d I J) : Prop :=
  ∀ (S : Sys X) (c : I) (i : ℕ) (n : I ⊕ J), V.Ge (-(i : ℝ)) (S.cur c i n)

def Eq16 (X : Cart V d I J) : Prop :=
  ∀ (a : ZMod d) (u : I → C) (x : ℕ → I ⊕ J → C), X.Good a u x → ∀ i : ℕ, 1 ≤ i →
      (∀ k, V.Ge (-((i : ℝ) - 1)) (x i (Sum.inl k))) ∧
        ∀ κ, V.Ge (-(max 1 ((i : ℝ) - 1))) (x i (Sum.inr κ))

def TExistsUnique (X : Cart V d I J) : Prop := ∀ S : Sys X, ∃! t : I → MvPowerSeries I C, S.IsT t

def SysExists (X : Cart V d I J) : Prop :=
  ∀ u : I → I → C, (∀ c x, V.Ge 0 (u c x)) → (∀ c x, X.ty (Sum.inl x) ≠ X.ty (Sum.inl c) → u c x = 0) →
    V.v (Matrix.of u).det = 0 → ∃ S : Sys X, S.tan = u

end OneGroup

section Rows

variable {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
  [∀ g, Fintype (J g)]

def toW (g : Fin 2) (u : I g → C) : WV I → C := fun w => if h : w.1 = g then u (h ▸ w.2) else 0

def hPullW {ι ι' : Type} [Fintype ι] [Fintype ι'] (H : MvPowerSeries (WV I) C)
    (e : ι → WV I → C) (e' : ι' → WV I → C) : MvPowerSeries (ι ⊕ ι') C :=
  MvPowerSeries.subst (fun w : WV I =>
    (∑ c : ι, e c w • (MvPowerSeries.X (Sum.inl c) : MvPowerSeries (ι ⊕ ι') C)) +
      ∑ b : ι', e' b w • (MvPowerSeries.X (Sum.inr b) : MvPowerSeries (ι ⊕ ι') C)) H

def WtGe2 (V : VF C) (i : ℕ) (w : ℝ) {ι ι' : Type} [Fintype ι] [Fintype ι']
    (h : MvPowerSeries (ι ⊕ ι') C) : Prop :=
  ∀ μ : ι ⊕ ι' →₀ ℕ, ((w : ℝ) : WithTop ℝ) ≤ V.v (MvPowerSeries.coeff μ h) +
    ((((∑ c : ι, μ (Sum.inl c) : ℕ) : ℝ) * (r1 V.l i - del V.l i) +
      ((∑ b : ι', μ (Sum.inr b) : ℕ) : ℝ) * (r2 V.l - del V.l i) : ℝ) : WithTop ℝ)

def WtGe1 (V : VF C) (i : ℕ) (w : ℝ) {ι : Type} (h : MvPowerSeries ι C) : Prop :=
  ∀ μ : ι →₀ ℕ, ((w : ℝ) : WithTop ℝ) ≤ V.v (MvPowerSeries.coeff μ h) +
    (((μ.degree : ℝ) * (r1 V.l i - del V.l i) : ℝ) : WithTop ℝ)

def mainM (V : VF C) (i : ℕ) {ι ι' : Type} [Fintype ι] [Fintype ι'] (Φ : ι' → ι → C) :
    MvPowerSeries (ι ⊕ ι') C :=
  ((V.l : C) ^ expE V.l i)⁻¹ • ∑ b : ι', ∑ c : ι,
    Φ b c • (MvPowerSeries.X (Sum.inl c) ^ (V.l ^ i) * MvPowerSeries.X (Sum.inr b))

def hRows (n0 : ℕ) (H : MvPowerSeries (Fin n0 ⊕ Fin n0) C) : MvPowerSeries (PVar n0) C :=
  ∑ ρ : Fin n0, MvPowerSeries.subst
    (Sum.elim (fun c => (MvPowerSeries.X (Sum.inl (ρ, c)) : MvPowerSeries (PVar n0) C))
      (fun b => MvPowerSeries.X (Sum.inr (ρ, b)))) H

namespace RowData

variable (X : RowData C V d I J)

def SatIn (g : Fin 2) (a : ZMod d) {N : ℕ} (u : Fin N → I g → C) : Prop :=
  IsSat V u ∧ ∀ c x, (X.G g).ty (Sum.inl x) ≠ a → u c x = 0

def hM (g : Fin 2) (a : ZMod d) (i : ℕ) {ι ι' : Type} [Fintype ι] [Fintype ι'] (e : ι → I g → C)
    (v' : ι' → I (1 - g) → C) : MvPowerSeries (ι ⊕ ι') C :=
  hPullW (X.hL g a (a + (i : ZMod d))) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b))

def MConcl (g : Fin 2) (a : ZMod d) (i : ℕ) (U : Fin X.n → I g → C) (U' : Fin X.n → I (1 - g) → C)
    (n0 : ℕ) (e : Fin n0 → I g → C) (v' : Fin X.n → I (1 - g) → C) (Φ : Fin X.n → Fin n0 → C) :
    Prop :=
  (X.n ≤ n0 + (i + 1) * X.j' + X.j ∧ n0 ≤ X.n) ∧
  IsSat V e ∧
  (∃ A : Fin n0 → Fin X.n → C, (∀ c b, V.Ge 0 (A c b)) ∧ ∀ c x, e c x = ∑ b, A c b * U b x) ∧
  (∃ Y : Matrix (Fin X.n) (Fin X.n) C, (∀ b b', V.Ge 0 (Y b b')) ∧ V.v Y.det = 0 ∧
    ∀ b x, v' b x = ∑ b', Y b b' * U' b' x) ∧
  (∀ b c, V.Ge 0 (Φ b c)) ∧
  (∀ (b : Fin X.n) (c : Fin n0), b.val < n0 → Φ b c = if b.val = c.val then -1 else 0) ∧
  WtGe2 V i (1 / ((V.l : ℝ) - 1)) (X.hM g a i e v' - mainM V i Φ) ∧
  (∀ μ : Fin n0 ⊕ Fin X.n →₀ ℕ, (∀ b, μ (Sum.inr b) = 0) →
    MvPowerSeries.coeff μ (X.hM g a i e v' - mainM V i Φ) = 0)

def CurveSystemVanishing (g : Fin 2) (a : ZMod d) (i : ℕ) (n0 : ℕ) (e : Fin n0 → I g → C)
    (v' : Fin X.n → I (1 - g) → C) (Φ : Fin X.n → Fin n0 → C) : Prop :=
  ∃ (S : Sys (X.G g)) (t : I g → MvPowerSeries (I g) C) (em : Fin n0 ↪ I g)
    (Φt : Fin n0 → J g → C),
    S.IsT t ∧ (∀ c, S.tan (em c) = e c) ∧ (∀ c x, S.al (em c) 1 x = 0) ∧
    (∀ c κ, V.Ge 0 (Φt c κ)) ∧
    (∀ b c, Φ b c = ∑ κ : J g, ∑ k : I (1 - g), Φt c κ * X.pair g κ k * v' b k) ∧
    ∀ κ : J g, (X.G g).ty (Sum.inr κ) = a + (i : ZMod d) →
      WtGe1 V i 0
        (MvPowerSeries.subst (fun x : I g =>
            ∑ c : Fin n0, e c x • (MvPowerSeries.X c : MvPowerSeries (Fin n0) C)) (S.ze t κ) -
          ((V.l : C) ^ expE V.l i)⁻¹ • ∑ c : Fin n0,
            Φt c κ • (MvPowerSeries.X c : MvPowerSeries (Fin n0) C) ^ (V.l ^ i))

def MPlusConcl (g : Fin 2) (a : ZMod d) (n0 : ℕ) (e : Fin n0 → I g → C)
    (v' : Fin X.n → I (1 - g) → C) (Φ : Fin X.n → Fin n0 → C) : Prop :=
  ∀ μ : Fin n0 ⊕ Fin X.n →₀ ℕ, (∑ c, μ (Sum.inl c)) < V.l ^ 2 → (∑ b, μ (Sum.inr b)) < V.l →
    V.Ge 0 (MvPowerSeries.coeff μ (X.hM g a 1 e v' - mainM V 1 Φ))

def LemmaM : Prop :=
  X.Alt → 5 ≤ V.l → ∀ (g : Fin 2) (a : ZMod d), X.big g a → ∀ i : ℕ, Odd i → i < d →
    ∀ (U : Fin X.n → I g → C) (U' : Fin X.n → I (1 - g) → C), X.SatIn g a U →
      X.SatIn (1 - g) (a + (i : ZMod d)) U' →
      ∃ (n0 : ℕ) (e : Fin n0 → I g → C) (v' : Fin X.n → I (1 - g) → C) (Φ : Fin X.n → Fin n0 → C),
        X.MConcl g a i U U' n0 e v' Φ ∧ X.CurveSystemVanishing g a i n0 e v' Φ

def LemmaMPlus : Prop :=
  X.Alt → 5 ≤ V.l → 1 < d → ∀ (g : Fin 2) (a : ZMod d), X.big g a →
    ∀ (U : Fin X.n → I g → C) (U' : Fin X.n → I (1 - g) → C), X.SatIn g a U →
      X.SatIn (1 - g) (a + ((1 : ℕ) : ZMod d)) U' →
      ∃ (n0 : ℕ) (e : Fin n0 → I g → C) (v' : Fin X.n → I (1 - g) → C) (Φ : Fin X.n → Fin n0 → C),
        X.MConcl g a 1 U U' n0 e v' Φ ∧ X.CurveSystemVanishing g a 1 n0 e v' Φ ∧ X.MPlusConcl g a n0 e v' Φ

def hGood (g : Fin 2) (a : ZMod d) (i : ℕ) {n0 : ℕ} (hn : n0 ≤ X.n) (e : Fin n0 → I g → C)
    (v' : Fin X.n → I (1 - g) → C) : MvPowerSeries (Fin n0 ⊕ Fin n0) C :=
  X.hM g a i e (fun b : Fin n0 => v' (Fin.castLE hn b))

def restrictedCurveSystemSeries (g : Fin 2) (a : ZMod d) (i : ℕ) {n0 : ℕ} (hn : n0 ≤ X.n) (e : Fin n0 → I g → C)
    (v' : Fin X.n → I (1 - g) → C) : MvPowerSeries (PVar n0) C :=
  hRows n0 (X.hGood g a i hn e v' - mainM V i (fun b c : Fin n0 => if b = c then (-1 : C) else 0))

def MtoHM : Prop :=
  ∀ (g : Fin 2) (a : ZMod d) (i : ℕ) (U : Fin X.n → I g → C) (U' : Fin X.n → I (1 - g) → C)
    (n0 : ℕ) (e : Fin n0 → I g → C) (v' : Fin X.n → I (1 - g) → C) (Φ : Fin X.n → Fin n0 → C),
    X.MConcl g a i U U' n0 e v' Φ → ∀ hn : n0 ≤ X.n,
      hRows n0 (X.hGood g a i hn e v') = hP C V.l i n0 (X.restrictedCurveSystemSeries g a i hn e v') ∧
      HM1 V.v V.l i n0 (X.restrictedCurveSystemSeries g a i hn e v') ∧ HM2 (X.restrictedCurveSystemSeries g a i hn e v') ∧
      (i = 1 → X.MPlusConcl g a n0 e v' Φ → HSeparatedRowSum V.v V.l n0 (X.restrictedCurveSystemSeries g a i hn e v'))

def AdaptedChainData : Prop :=
  X.Alt → ∀ (g : Fin 2) (a : ZMod d), X.big g a → ∀ i : ℕ, Odd i → i < d →
    ∀ U : Fin X.n → I g → C, X.SatIn g a U →
      ∃ (S : Sys (X.G g)) (N1 : ℕ) (D : Formalism.BaseCaseIdentities.Data C (Fin N1) (I g)),
        D.v = V.v ∧ D.l = V.l ∧ D.i = i ∧
        (∀ c (k : ℕ) x, 1 ≤ k → S.al c k x = ∑ b, D.al c k b * S.al b 0 x) ∧
        (∀ c, D.lev c < Formalism.BaseCaseIdentities.Kn i →
          (X.G g).ty (Sum.inl c) = a + ((2 * D.lev c : ℕ) : ZMod d)) ∧
        X.n ≤ N1 + (Formalism.BaseCaseIdentities.Kn i + 1) * X.j' ∧
        ∃ A : Fin N1 → Fin X.n → C, (∀ δ b, V.Ge 0 (A δ b)) ∧
          ∀ δ x, S.al (D.ι δ) 0 x = ∑ b, A δ b * U b x

end RowData

end Rows

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section
open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.UnitaryBoundIntegral

def blockBd (l n m i y : ℕ) : ℝ :=
  if y = 0 then 0 else bdP l i n n y + ((i : ℝ) + 1) * m * ((l : ℝ) ^ i + 1) * y / ((l : ℝ) - 1)

def chBd (l n m u : ℕ) : ℝ := (u : ℝ) * (n * gam l + m / ((l : ℝ) - 1))

def Windows (S : ℕ) (G : Set ℕ) : Prop := 0 ∈ G ∧ ∀ Y0 : ℕ, ∃ y ∈ G, Y0 ≤ y ∧ y < Y0 + S

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

def _root_.Formalism.L2.FormalSeriesBounds.RowData.rkF (X : RowData C V d I J) (g : Fin 2) (a : ZMod d) : ℕ :=
  (Finset.univ.filter fun c : I g => (X.G g).ty (Sum.inl c) = a).card

structure Flag (X : RowData C V d I J) where
  en : ∀ g a, Fin (X.rkF g a) → I g
  en_inj : ∀ g a, Function.Injective (en g a)
  en_ty : ∀ g a c, (X.G g).ty (Sum.inl (en g a c)) = a

def Flag.letter {X : RowData C V d I J} (F : Flag X) (g : Fin 2) (a : ZMod d) {N : ℕ}
    (x : Fin N × Fin (X.rkF g a)) : Fin N × WV I := (x.1, ⟨g, F.en g a x.2⟩)

def bg (a : ZMod d) : Fin 2 := if Even a.val then 0 else 1

inductive GlobalTheory (d : ℕ) where

  | bi (g : Fin 2) (a : ZMod d) (i y : ℕ)

  | ch (g : Fin 2) (a : ZMod d) (u : ℕ)

  | mon (g : Fin 2) (e : ZMod d → ℕ → ℕ) (N : ℕ)

namespace GlobalTheory

def what₂ (n : ℕ) : GlobalTheory d → ℕ
  | bi _ _ _ _ => n
  | ch _ _ _ => n
  | mon _ _ N => N

variable (X : RowData C V d I J) (F : Flag X)

def poly : (b : GlobalTheory d) → MvPolynomial (Fin (b.what₂ X.n) × WV I) C
  | bi g a i y =>
      MvPolynomial.rename (F.letter g a) (minorK C X.n (X.rkF g a) X.n) ^ (V.l ^ i * y) *
        MvPolynomial.rename (F.letter (1 - g) (a + (i : ZMod d)))
          (minorK C X.n (X.rkF (1 - g) (a + (i : ZMod d))) X.n) ^ y
  | ch g a u => MvPolynomial.rename (F.letter g a) (minorK C X.n (X.rkF g a) X.n) ^ u
  | mon g e N => ∏ a : ZMod d, MvPolynomial.rename (F.letter g a) (monP C N (X.rkF g a) (e a))

def kind (n : ℕ) : (b : GlobalTheory d) → Fin (b.what₂ n) → Option (Fin 2 × ZMod d × ZMod d)
  | bi g a i _ => fun _ => some (g, a, a + (i : ZMod d))
  | ch _ _ _ => fun _ => none
  | mon _ _ _ => fun _ => none

def wt : GlobalTheory d → Fin 2 → ZMod d → ℕ → ℕ
  | bi g a i y => fun g' a' k =>
      (if g' = g ∧ a' = a ∧ k = X.n then V.l ^ i * y else 0) +
        (if g' = 1 - g ∧ a' = a + (i : ZMod d) ∧ k = X.n then y else 0)
  | ch g a u => fun g' a' k => if g' = g ∧ a' = a ∧ k = X.n then u else 0
  | mon g e N => fun g' a' k => if g' = g ∧ 1 ≤ k ∧ k ≤ min N (X.rkF g a') then e a' k else 0

def Attains (b : GlobalTheory d) (c : ℝ) : Prop :=
  ∃ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) ∧
    ∃ gr : Fin (b.what₂ X.n) → MvPowerSeries (WV I) C, (∀ ρ, gr ρ ∈ IntGerm V t) ∧
      V.v (ValOf X.hL (b.poly X F) (b.kind X.n) gr) ≤ ((c : ℝ) : WithTop ℝ)

end GlobalTheory

def BiSupply : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : Flag X), X.Alt → 5 ≤ V.l → 1 ≤ X.n →
    ∀ g a, X.big g a → ∀ i : ℕ, Odd i → i < d →
      Windows (S0 V.l i X.n) {y | (GlobalTheory.bi g a i y).Attains X F (blockBd V.l X.n X.m i y)}

def CHSupply : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : Flag X), ∀ g a, X.big g a → ∀ u : ℕ,
      (X.Alt → (GlobalTheory.ch g a u).Attains X F (chBd V.l X.n X.m u)) ∧
      ((∀ a, X.big g a) → (GlobalTheory.ch g a u).Attains X F ((u : ℝ) * (X.m / ((V.l : ℝ) - 1))))

def monDegAll (X : RowData C V d I J) (g : Fin 2) (e : ZMod d → ℕ → ℕ) (N : ℕ) : ℕ :=
  ∑ a : ZMod d, monDeg N (X.rkF g a) (e a)

def MONSupply : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : Flag X) (g : Fin 2) (e : ZMod d → ℕ → ℕ)
    (N : ℕ),
      (GlobalTheory.mon g e N).Attains X F ((monDegAll X g e N : ℝ) / ((V.l : ℝ) - 1)) ∧
      ((∀ a ρ, monAl N (X.rkF g a) (e a) ρ < V.l) → (GlobalTheory.mon g e N).Attains X F 0)

def ValBlocks {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
    [∀ o g, Fintype (J o g)] (X : ∀ o, RowData C V d (I o) (J o)) (F : ∀ o, Flag (X o))
    (Z : Finset Orb) (nW : ℕ) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) (ν : ℝ) : Prop :=
  ∀ L : Orb → List (GlobalTheory d × ℝ),
    (∀ o ∈ Z, ∀ p ∈ L o, p.1.Attains (X o) (F o) p.2) →
    (∑ o ∈ Z, ((L o).map fun p => p.1.what₂ (X o).n).sum) ≤ nW →
    (∀ o ∈ Z, ∀ g a k, ((L o).map fun p => p.1.wt (X o) g a k).sum = ga o g a k) →
    ν ≤ ∑ o ∈ Z, ((L o).map Prod.snd).sum

def restDeg (bgr : ZMod d → Fin 2) (n : ℕ) (ga : Fin 2 → ZMod d → ℕ → ℕ) (K : ℕ) : ℕ :=
  ∑ g : Fin 2, ∑ a : ZMod d, ∑ k ∈ Finset.Icc 1 K, if g = bgr a ∧ k = n then 0 else k * ga g a k

structure WtHyp {Orb : Type} (k K : ℕ) (Z : Finset Orb) (bgr : ZMod d → Fin 2)
    (rk : Orb → Fin 2 → ZMod d → ℕ) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) (Wa ea : Orb → ZMod d → ℕ)
    (rest : ℝ) : Prop where
  supp : ∀ z ∈ Z, ∀ g a k', ga z g a k' ≠ 0 → 1 ≤ k' ∧ k' ≤ rk z g a
  main : ∀ z ∈ Z, ∀ a, ga z (bgr a) a (k - 1) = Wa z a + ea z a
  rest_eq : rest = ∑ z ∈ Z, ((restDeg bgr (k - 1) (ga z) K : ℝ) +
    ∑ a, ((k : ℝ) - 1) * ((ea z a : ℕ) : ℝ))

def ValBlocksC {C : Type} [Field C] {V : VF C} {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type}
    [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)] (X : ∀ o, RowData C V 2 (I o) (J o))
    (F : ∀ o, Flag (X o)) (nW : ℕ) (gaC : Orb → ZMod 2 → ℕ → ℕ) (ν : ℝ) : Prop :=
  ∀ L : Orb → List (GlobalTheory 2 × ℝ),
    (∀ o, ∀ p ∈ L o, p.1.Attains (X o) (F o) p.2) →
    (∀ o, ∀ p ∈ L o, ∀ g e N, p.1 = GlobalTheory.mon g e N → ∃ s : ZMod 2, ∀ a k, a ≠ s → e a k = 0) →
    2 * (∑ o, ((L o).map fun p => p.1.what₂ (X o).n).sum) ≤ nW →
    (∀ o s k, ((L o).map fun p => p.1.wt (X o) 0 s k + p.1.wt (X o) 1 (s + 1) k).sum = gaC o s k) →
    ν ≤ ∑ o, ((L o).map Prod.snd).sum

end Formalism.L2.FormalSeriesBounds.RF
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace RawChart

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
  (X : RawChart C d I κ) {V : VF C}

theorem pairK_int (g : Fin 2) (q : JJ I g) (c : I (1 - g)) : V.Ge 0 (X.pairK g q c) := by
  unfold pairK
  split_ifs
  · exact (VF.ge_natCast X.k).neg
  · exact VF.Ge.zero 0

theorem k_ne_zero (hk : V.v (X.k : C) = 0) : (X.k : C) ≠ 0 := by
  intro h
  rw [h, V.v.map_zero] at hk
  exact WithTop.top_ne_zero hk

theorem k_inv_int (hk : V.v (X.k : C) = 0) : V.Ge 0 ((X.k : C)⁻¹) := by
  have h1 : V.v ((X.k : C) * (X.k : C)⁻¹) = 0 := by
    rw [mul_inv_cancel₀ (X.k_ne_zero hk), V.v.map_one]
  rw [V.v.map_mul, hk, zero_add] at h1
  unfold VF.Ge
  rw [h1]
  rfl

theorem pairK_onto (hk : V.v (X.k : C) = 0) (g : Fin 2) :
    ∃ s : I (1 - g) → JJ I g → C, (∀ c q, V.Ge 0 (s c q)) ∧
      ∀ q q' : JJ I g, ∑ c, X.pairK g q c * s c q' = if q = q' then 1 else 0 := by
  refine ⟨fun c q => if c = q then -(X.k : C)⁻¹ else 0, ?_, ?_⟩
  · intro c q
    dsimp only
    split_ifs
    · exact (X.k_inv_int hk).neg
    · exact VF.Ge.zero 0
  · intro q q'
    have hk0 := X.k_ne_zero hk
    simp only [pairK, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    split_ifs
    · field_simp
    · simp

theorem rk_fil (H : X.RankHyp) (g : Fin 2) (a : ZMod d) :
    (Finset.univ.filter fun q : I (1 - g) => X.ty (1 - g) q = a).card + 0 +
      (Finset.univ.filter fun c : I g => X.ty g c = a).card = X.n + X.j + X.j' := by
  by_cases hb : X.big g a
  · have h1 : ¬ X.big (1 - g) a := fun h => (H.big_compl g a).1 h hb
    rw [H.rk_big g a hb, H.rk_small (1 - g) a h1]
    omega
  · have h1 : X.big (1 - g) a := (H.big_compl g a).2 hb
    rw [H.rk_small g a hb, H.rk_big (1 - g) a h1]
    omega

theorem hLf_axes (H : X.AxesSt) (g : Fin 2) (a a' : ZMod d) (μ : WV I →₀ ℕ)
    (h : (∀ w ∈ μ.support, w.1 = g) ∨ (∀ w ∈ μ.support, w.1 = 1 - g)) :
    MvPowerSeries.coeff μ (X.hLf g a a') = 0 := by
  have h2 : (∀ w ∈ μ.support, w.1 = 0) ∨ (∀ w ∈ μ.support, w.1 = 1) := by
    fin_cases g
    · exact h
    · exact h.symm
  show (if ∀ w ∈ μ.support, X.OnLf g a a' w then MvPowerSeries.coeff μ X.hRow else 0) = 0
  rw [H μ h2]
  simp

def rowData [NeZero d] (H : X.Hyps V) : RowData C V d I (JJ I) where
  charZero := H.charZero
  algClosed := H.algClosed
  l_odd := H.l_odd
  G := fun g => cart (H.cartH g)
  n := X.n
  j := X.j
  j' := X.j'
  rh := 0
  r := X.n + X.j + X.j'
  r_eq := rfl
  big := X.big
  big_compl := H.rank.big_compl
  rk_big := H.rank.rk_big
  rk_small := H.rank.rk_small
  rk_fil := X.rk_fil H.rank
  pair := X.pairK
  pair_int := X.pairK_int
  pair_type := by
    intro g q c h
    unfold pairK
    rw [if_neg]
    rintro rfl
    exact h rfl
  pair_onto := X.pairK_onto H.k_unit
  R2 := H.R2
  R1 := fun hA g a hb N w x h1 h2 h3 => by simpa using H.R1 hA g a hb N w x h1 h2 h3
  G0 := H.G0
  hL := X.hLf
  hL_leaf := X.hLf_leaf
  hL_swap := X.hLf_swap
  hL_axes := X.hLf_axes H.axes
  C_eq := H.CEq
  CH := H.CH

end RawChart

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

variable {C : Type} [Field C]

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

def AllSet (V : VF C) (g : Fin 2) : Set (ℕ → I g ⊕ JJ I g → C) :=
  {L | ∃ (γ : κ → PowerSeries C) (lam : JJ I g → PowerSeries C), IsCv V γ ∧ IsCv V lam ∧
    (∀ i : κ, alongCv γ (X.lg i) = ∑ c : I g, X.u g c i • PowerSeries.mk (fun n => L n (Sum.inl c))) ∧
    ∀ q : JJ I g, PowerSeries.mk (fun n => L n (Sum.inr q)) =
      lam q - alongCv γ (X.sg (X.u (1 - g) q)) +
        ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • PowerSeries.mk (fun n => L n (Sum.inl c)) else 0}

end RawChart

end Formalism.L2.FormalSeriesBounds
end
end
