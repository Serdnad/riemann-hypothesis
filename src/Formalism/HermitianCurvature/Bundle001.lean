module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
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

namespace Formalism.FourierDecayAlt.I

open Finset Polynomial

noncomputable section

def Interlaces (k : ℕ) (u u' ρ : ℕ → ℝ) : Prop :=
  ∀ i ∈ Icc 1 (k - 1), ρ i + 1/2 ≤ u i ∧ ρ i + 1/2 ≤ u' i ∧
    u (i + 1) + 1/2 ≤ ρ i ∧ u' (i + 1) + 1/2 ≤ ρ i

def OnCut (u u' : ℕ → ℝ) (l : ℕ) (Y : ℝ) : Prop :=
  ((u l + 2 ≤ -Y ∧ -Y ≤ u' l - 2) ∨ (u' l + 2 ≤ -Y ∧ -Y ≤ u l - 2))

def xpoly (k : ℕ) (ρ : ℕ → ℝ) (Y : ℝ) : ℝ := ∏ i ∈ Icc 1 (k - 1), (Y + ρ i)

def qpoly (k : ℕ) (T T' : ℝ) (u u' : ℕ → ℝ) (Y : ℝ) : ℝ :=
  -(T * T') * ∏ i ∈ Icc 1 k, ((Y + 1/2 + u i) * (Y + 1/2 + u' i))

def InterlaceSign : Prop :=
  ∀ (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ), 1 ≤ l → l ≤ k → Interlaces k u u' ρ →
    OnCut u u' l Y → ∀ e ∈ ({-1, 0, 1} : Finset ℝ), 0 < (-1 : ℝ) ^ (k - l) * xpoly k ρ (Y + e)

def QPositive : Prop :=
  ∀ (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y T T' : ℝ), 1 ≤ l → l ≤ k → Interlaces k u u' ρ →
    OnCut u u' l Y → 0 < T → 0 < T' → 0 < qpoly k T T' u u' Y

def InterlaceRatio : Prop :=
  ∀ (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ), 1 ≤ l → l ≤ k → Interlaces k u u' ρ →
    OnCut u u' l Y →
    xpoly k ρ (Y + 1) ^ 2 * (|Y + 1/2 + u l| * |Y + 1/2 + u' l|) ≤
      |(∏ i ∈ Icc 1 k, (Y + 1/2 + u i)) * (∏ i ∈ Icc 1 k, (Y + 1/2 + u' i))|

def orderR {F : Type} [Field F] (o : Subring F) (q : F) : Set (F × F) :=
  {a | a.1 ∈ o ∧ a.2 ∈ o ∧ ∃ t ∈ o, a.1 - a.2 = q * t}

def SelfDualG : Prop :=
  ∀ (F : Type) [Field F] (o : Subring F) (q : F), q ∈ o → q ≠ 0 → ∀ a : F × F,
    (∀ b ∈ orderR o q, (a.1 * b.1 - a.2 * b.2) / q ∈ o) ↔ a ∈ orderR o q

end

end Formalism.FourierDecayAlt.I
end

section

namespace Formalism.FourierDecayAlt.TA

open Finset Filter Topology
open scoped InnerProductSpace ComplexConjugate

abbrev Pt (E : Type) := List (ℕ × E)

def lvl {E : Type} (p : Pt E) : ℕ := (p.map Prod.fst).sum

def IsPt {E : Type} [Zero E] (i : ℕ) (p : Pt E) : Prop :=
  lvl p = i ∧ ∀ b ∈ p, 1 ≤ b.1 ∧ b.2 ≠ 0

def ext {E : Type} (h : Pt E) (s : ℕ) (t : E) : Pt E := h ++ [(s, t)]

def PSDOn {α : Type} (P : Finset α) (k : α → α → ℂ) : Prop :=
  (∀ x ∈ P, ∀ y ∈ P, k y x = conj (k x y)) ∧
  ∀ a : α → ℂ, 0 ≤ (∑ x ∈ P, ∑ y ∈ P, conj (a x) * k x y * a y).re

section forms
variable {E : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

noncomputable def gram (k : Pt E → Pt E → ℂ) (V : Pt E → H) (P : Finset (Pt E)) : ℂ :=
  ∑ p ∈ P, ∑ p' ∈ P, k p p' * ⟪V p, V p'⟫_ℂ

end forms

def LatSum {E : Type} [AddCommGroup E] (L : AddSubgroup E) (c : E → ℝ) (ep : ℝ) : Prop :=
  (∀ x, 0 ≤ c x) ∧ ∀ S : Finset E, (∀ x ∈ S, x ∈ L ∧ x ≠ 0) → ∑ x ∈ S, c x ≤ ep

structure Data (E : Type) [Field E] where
  r : ℕ
  K : ℕ → Pt E → Pt E → ℂ
  Th : ℕ → ℕ → E → Pt E → Pt E → ℂ
  e : ℕ → ℝ
  La : ℕ → ℕ → AddSubgroup E
  Lf : ℕ → ℕ → AddSubgroup E
  Lv : ℕ → AddSubgroup E

section axioms
variable {E : Type} [Field E] [DecidableEq E]

def KernelSupport (D : Data E) : Prop :=
  ∀ i s, 1 ≤ s → s ≤ i → i ≤ D.r + 1 → ∀ (h h' : Pt E) (t t' : E),
    IsPt (i - s) h → IsPt (i - s) h' → t ≠ 0 → t' ≠ 0 →
    (1 / t - 1 / t' ∉ D.Lf i s ∨ (i = D.r + 1 ∧ s = 1 ∧ t ≠ t')) →
    D.K i (ext h s t) (ext h' s t') = 0

def ThetaDomination (D : Data E) : Prop :=
  ∀ i s, 1 ≤ s → s ≤ i → i ≤ D.r + 1 →
    (∀ (t : E) (Hd : Finset (Pt E)), (∀ h ∈ Hd, IsPt (i - s) h) → PSDOn Hd (D.Th i s t)) ∧
    (∀ t l : E, l ∈ D.La i s → D.Th i s (t + l) = D.Th i s t) ∧
    (∀ (t : E) (Hd : Finset (Pt E)), t ≠ 0 → (∀ h ∈ Hd, IsPt (i - s) h) →
      PSDOn Hd (fun h h' => D.Th i s t h h' - D.K i (ext h s t) (ext h' s t))) ∧
    (∀ (R : Finset E) (Hd : Finset (Pt E)), (∀ x ∈ R, ∀ y ∈ R, x - y ∈ D.La i s → x = y) →
      (∀ h ∈ Hd, IsPt (i - s) h) →
      PSDOn Hd (fun h h' => ((1 + D.e i : ℝ) : ℂ) * D.K (i - s) h h' - ∑ t ∈ R, D.Th i s t h h'))

end axioms

section estimates
variable {E : Type} [Field E] [DecidableEq E] {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {W : Type} [Fintype W]

end estimates

section levels
variable {E : Type} [Field E] [DecidableEq E] {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {W : Type} [Fintype W]


end levels

end Formalism.FourierDecayAlt.TA
end

section

namespace Formalism.FourierDecayAlt.E

open Real Polynomial MeasureTheory

def MiddleThird : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ) (α β Y : ℝ), 12 ≤ β - α → (∀ s, -lam s ∉ Set.Ioo α β) →
    α + (β - α) / 3 ≤ Y → Y ≤ β - (β - α) / 3 →
    |(∏ s, (Y + 1 + lam s)) / ∏ s, (Y + lam s)| ≤ Real.exp (3 * n / (β - α)) ∧
    |(∏ s, (Y + lam s)) / ∏ s, (Y + 1 + lam s)| ≤ Real.exp (4 * n / (β - α))

def CauchyTheta : Prop :=
  ∀ (σ ε : ℝ), 4 ≤ σ → 0 < ε → ∀ (p : ℕ) (u : ℝ),
    |iteratedDeriv p (fun v : ℝ => (1 + ε * Real.exp (-v)) ^ (-σ)) u| ≤
      Real.exp 1 * p.factorial * (4 * σ) ^ p * (1 + ε * Real.exp (-u)) ^ (-σ)

def AMarkov : Prop :=
  ∀ (p : ℝ[X]) (d : ℕ) (M : ℝ), p.natDegree ≤ d → (∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ M) →
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.derivative.eval x| ≤ (d : ℝ) ^ 2 * M

def MarkovVector : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] (d : ℕ) (a : Fin (d + 1) → H)
    (t₀ L M : ℝ), 0 < L →
    (∀ t ∈ Set.Icc t₀ (t₀ + L), ‖∑ k : Fin (d + 1), t ^ (k : ℕ) • a k‖ ≤ M) →
    ∀ (q : ℕ), ∀ t ∈ Set.Icc t₀ (t₀ + L),
      ‖iteratedDeriv q (fun s : ℝ => ∑ k : Fin (d + 1), s ^ (k : ℕ) • a k) t‖ ≤ (2 * (d : ℝ) ^ 2 / L) ^ q * M

def Bdd {Λ : Type} (f : Λ → ℂ) : Prop := ∃ B : ℝ, ∀ x, ‖f x‖ ≤ B

def MeanPosDef : Prop :=
  ∀ (Λ : Type) [AddCommGroup Λ] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (LIM : (Λ → ℂ) → ℂ),
    (∀ f g, Bdd f → Bdd g → LIM (f + g) = LIM f + LIM g) →
    (∀ (c : ℂ) f, Bdd f → LIM (c • f) = c * LIM f) →
    (∀ f, Bdd f → (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) → 0 ≤ (LIM f).re) →
    (∀ f (σ : Λ), Bdd f → LIM (fun x => f (x + σ)) = LIM f) →
    ∀ (u : Λ → H) (B : ℝ), (∀ x, ‖u x‖ ≤ B) → ∀ (S : Finset Λ) (c : Λ → ℂ),
      0 ≤ (∑ σ ∈ S, ∑ σ' ∈ S,
        LIM (fun x => inner ℂ (u x) (u (x + (σ - σ')))) * c σ * starRingEnd ℂ (c σ')).re

def HerglotzLSC : Prop :=
  ∀ (d : ℕ) (N : (Fin d → ℝ) → ℝ) (A : (Fin d → ℤ) → ℂ),
    (∀ z, 0 ≤ N z) → LowerSemicontinuous N → Integrable N →
    (∀ (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ),
        0 ≤ (∑ σ ∈ S, ∑ σ' ∈ S, A (σ - σ') * c σ * starRingEnd ℂ (c σ')).re) →
    Summable (fun σ : Fin d → ℤ =>
      ‖(∫ z, (N z : ℂ) * Complex.exp (2 * π * Complex.I * ∑ j, ((σ j : ℝ) : ℂ) * (z j : ℂ))) + A σ‖) →
    ∀ (z₀ : Fin d → ℝ) (S : Finset (Fin d → ℤ)),
      ∑ m ∈ S, N (fun j => z₀ j + (m j : ℝ)) ≤
        ∑' σ : Fin d → ℤ,
          ‖(∫ z, (N z : ℂ) * Complex.exp (2 * π * Complex.I * ∑ j, ((σ j : ℝ) : ℂ) * (z j : ℂ))) + A σ‖

end Formalism.FourierDecayAlt.E
end

section

namespace Formalism.FourierDecayAlt

open Finset Real NumberField

def RecursionSharp : Prop :=
  ∃ C : ℝ, ∀ (r : ℕ) (a ε : ℝ) (e σ : ℕ → ℝ),
    0 ≤ a → a ≤ 1/2 → 0 ≤ ε → ((r : ℝ) + 1) * (ε + a) ≤ 1 →
    (∀ i, 0 ≤ e i) → (∀ i, 0 ≤ σ i) →
    (∀ i, 1 ≤ i → i ≤ r + 1 →
      σ i ≤ (1 + ε) * √(1 + e i) * σ (i - 1) + ∑ t ∈ Icc 2 i, a ^ (t - 1) * σ (i - t)) →
    σ (r + 1) ^ 2 ≤
      (1 + C * ((r : ℝ) + 1) * (ε + a)) * (∏ i ∈ Icc 1 (r + 1), (1 + e i)) * σ 0 ^ 2

def RecursionText : Prop :=
  ∃ C : ℝ, ∀ (r : ℕ) (a ε : ℝ) (e σ : ℕ → ℝ),
    0 ≤ a → a ≤ 1/2 → 0 ≤ ε → ε ≤ a → (r : ℝ) * a ≤ 1 →
    (∀ i, 0 ≤ e i) → (∀ i, 0 ≤ σ i) →
    (∀ i, 1 ≤ i → i ≤ r + 1 →
      σ i ≤ (1 + ε) * √(1 + e i) * σ (i - 1) + ∑ t ∈ Icc 2 i, a ^ (t - 1) * σ (i - t)) →
    σ (r + 1) ^ 2 ≤
      (1 + C * ((r : ℝ) + 1) * a) * (∏ i ∈ Icc 1 (r + 1), (1 + e i)) * σ 0 ^ 2

end Formalism.FourierDecayAlt
end

section

namespace Formalism.FourierDecayAlt.K

open Matrix Finset Real

def JointTheoremA : Prop :=
  ∀ C₀ : ℝ, 1 ≤ C₀ → ∃ C' C : ℝ, ∀ (Kx Θ : ℝ) (f r : ℕ) (e σ : ℕ → ℝ),
    4 ≤ Kx → 1 ≤ f → C' ≤ Θ → (r : ℝ) * (C₀ / Θ) ^ f ≤ 1 →
    (∀ i, 0 ≤ e i) → (∀ i, 0 ≤ σ i) →
    (∀ i, 1 ≤ i → i ≤ r + 1 →
      σ i ≤ (1 + (C₀ * Θ ^ (-(Kx - 5/2))) ^ f) * √(1 + e i) * σ (i - 1) +
        ∑ t ∈ Icc 2 i, ((C₀ / Θ) ^ f) ^ (t - 1) * σ (i - t)) →
    σ (r + 1) ^ 2 ≤
      (1 + C * ((r : ℝ) + 1) * (C₀ / Θ) ^ f) * (∏ i ∈ Icc 1 (r + 1), (1 + e i)) * σ 0 ^ 2

end Formalism.FourierDecayAlt.K
end

section

namespace Formalism.FourierDecayAlt.R

open Matrix

structure LevelData (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) where
  p : Fin r → A
  pb : Fin r → A
  c : Fin r → A
  ci : Fin r → A
  cb : Fin r → A
  cbi : Fin r → A
  ζ : A
  ζi : A
  ζb : A
  ζbi : A
  GG : A
  GGi : A
  nab : A
  nabs : A
  TT : ℂ

  fns_comm : ∀ x ∈ Set.range c ∪ Set.range ci ∪ Set.range cb ∪ Set.range cbi ∪ {ζ, ζi, ζb, ζbi, GG, GGi},
    ∀ y ∈ Set.range c ∪ Set.range ci ∪ Set.range cb ∪ Set.range cbi ∪ {ζ, ζi, ζb, ζbi, GG, GGi},
    x * y = y * x
  c_ci : ∀ l, c l * ci l = 1
  ci_c : ∀ l, ci l * c l = 1
  cb_cbi : ∀ l, cb l * cbi l = 1
  cbi_cb : ∀ l, cbi l * cb l = 1
  ζ_ζi : ζ * ζi = 1
  ζi_ζ : ζi * ζ = 1
  ζb_ζbi : ζb * ζbi = 1
  ζbi_ζb : ζbi * ζb = 1
  GG_GGi : GG * GGi = 1
  GGi_GG : GGi * GG = 1
  GG_def : GG = ζ * ζb - algebraMap ℂ A TT
  p_c : ∀ l m, p l * c m = c m * p l + (if l = m then c m else 0)
  p_ci : ∀ l m, p l * ci m = ci m * p l - (if l = m then ci m else 0)
  p_cb : ∀ l m, p l * cb m = cb m * p l
  p_cbi : ∀ l m, p l * cbi m = cbi m * p l
  p_ζ : ∀ l, p l * ζ = ζ * p l
  p_ζi : ∀ l, p l * ζi = ζi * p l
  p_ζb : ∀ l, p l * ζb = ζb * p l
  p_ζbi : ∀ l, p l * ζbi = ζbi * p l
  p_GG : ∀ l, p l * GG = GG * p l
  p_GGi : ∀ l, p l * GGi = GGi * p l
  pb_cb : ∀ l m, pb l * cb m = cb m * pb l + (if l = m then cb m else 0)
  pb_cbi : ∀ l m, pb l * cbi m = cbi m * pb l - (if l = m then cbi m else 0)
  pb_c : ∀ l m, pb l * c m = c m * pb l
  pb_ci : ∀ l m, pb l * ci m = ci m * pb l
  pb_ζ : ∀ l, pb l * ζ = ζ * pb l
  pb_ζi : ∀ l, pb l * ζi = ζi * pb l
  pb_ζb : ∀ l, pb l * ζb = ζb * pb l
  pb_ζbi : ∀ l, pb l * ζbi = ζbi * pb l
  pb_GG : ∀ l, pb l * GG = GG * pb l
  pb_GGi : ∀ l, pb l * GGi = GGi * pb l
  p_p : ∀ l m, p l * p m = p m * p l
  p_pb : ∀ l m, p l * pb m = pb m * p l
  pb_pb : ∀ l m, pb l * pb m = pb m * pb l
  p_nab : ∀ l, p l * nab = nab * p l
  pb_nab : ∀ l, pb l * nab = nab * pb l
  p_nabs : ∀ l, p l * nabs = nabs * p l
  pb_nabs : ∀ l, pb l * nabs = nabs * pb l
  nab_ζ : nab * ζ = ζ * nab + 1
  nab_ζi : nab * ζi = ζi * nab - ζi * ζi
  nab_ζb : nab * ζb = ζb * nab
  nab_ζbi : nab * ζbi = ζbi * nab
  nab_GG : nab * GG = GG * nab + ζb
  nab_GGi : nab * GGi = GGi * nab - ζb * GGi * GGi
  nab_c : ∀ l, nab * c l = c l * nab
  nab_ci : ∀ l, nab * ci l = ci l * nab
  nab_cb : ∀ l, nab * cb l = cb l * nab
  nab_cbi : ∀ l, nab * cbi l = cbi l * nab
  nabs_ζb : nabs * ζb = ζb * nabs - 1
  nabs_ζbi : nabs * ζbi = ζbi * nabs + ζbi * ζbi
  nabs_ζ : nabs * ζ = ζ * nabs
  nabs_ζi : nabs * ζi = ζi * nabs
  nabs_GG : nabs * GG = GG * nabs - ζ
  nabs_GGi : nabs * GGi = GGi * nabs + ζ * GGi * GGi
  nabs_c : ∀ l, nabs * c l = c l * nabs
  nabs_ci : ∀ l, nabs * ci l = ci l * nabs
  nabs_cb : ∀ l, nabs * cb l = cb l * nabs
  nabs_cbi : ∀ l, nabs * cbi l = cbi l * nabs

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}

namespace LevelData

noncomputable section

variable (L : LevelData A r)

def fns : Set A :=
  Set.range L.c ∪ Set.range L.ci ∪ Set.range L.cb ∪ Set.range L.cbi ∪ {L.ζ, L.ζi, L.ζb, L.ζbi, L.GG, L.GGi}

def Tl (Y : ℂ) (l : Fin r) : Matrix (Fin 2) (Fin 2) A :=
  !![algebraMap ℂ A Y + L.p l, -L.c l; L.ci l, 0]

def Tvl (Y : ℂ) (l : Fin r) : Matrix (Fin 2) (Fin 2) A :=
  !![algebraMap ℂ A Y - L.pb l, -L.cb l; L.cbi l, 0]

def Tprod (Y : ℂ) : Matrix (Fin 2) (Fin 2) A := ((List.ofFn (L.Tl Y)).reverse).prod

def Tvprod (Y : ℂ) : Matrix (Fin 2) (Fin 2) A := ((List.ofFn (L.Tvl Y)).reverse).prod

def Ar (Y : ℂ) : A := L.Tprod Y 0 0
def Br (Y : ℂ) : A := L.Tprod Y 1 0
def Avr (Y : ℂ) : A := L.Tvprod Y 0 0
def Bvr (Y : ℂ) : A := L.Tvprod Y 1 0

def Dr : A := (List.ofFn L.c).prod
def Drb : A := (List.ofFn L.cb).prod
def Dri : A := (List.ofFn L.ci).prod
def Drbi : A := (List.ofFn L.cbi).prod

def l0 (Y : ℂ) : A := -L.nab - algebraMap ℂ A (Y + 1/2) * (L.ζb * L.GGi)
def m0 (Y : ℂ) : A := -L.nabs - algebraMap ℂ A (Y - 1/2) * (L.ζ * L.GGi)

def Ahat (Y : ℂ) : A := L.Dr * L.Ar Y
def R0 (Y : ℂ) : A := L.Drb * L.GG * (L.l0 Y * L.Ar Y + L.Br Y)
def Ahatv (Y : ℂ) : A := L.Drb * L.Avr Y
def R0v (Y : ℂ) : A := L.Dr * L.GG * (L.m0 Y * L.Avr Y + L.Bvr Y)

def D : A := L.Dr * L.ζ
def Di : A := L.ζi * L.Dri
def Db : A := L.Drb * L.ζb
def Dbi : A := L.ζbi * L.Drbi
def G : A := L.Dr * L.Drb * L.GG

end

end LevelData

open LevelData

def RuleG : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r) (s : ℂ) (Gs Gsi : A),
    Gs * Gsi = 1 → Gsi * Gs = 1 → (∀ x ∈ L.fns, x * Gs = Gs * x) →
    (∀ l, L.p l * Gs = Gs * L.p l + algebraMap ℂ A s * Gs) →
    (∀ l, L.pb l * Gs = Gs * L.pb l + algebraMap ℂ A s * Gs) →
    L.nab * Gs = Gs * L.nab + algebraMap ℂ A s * (L.ζb * L.GGi * Gs) →
    L.nabs * Gs = Gs * L.nabs - algebraMap ℂ A s * (L.ζ * L.GGi * Gs) →
    ∀ Y : ℂ, Gsi * L.Ahat Y * Gs = L.Ahat (Y + s) ∧ Gsi * L.R0 Y * Gs = L.R0 (Y + s) ∧
      Gsi * L.Ahatv Y * Gs = L.Ahatv (Y - s) ∧ Gsi * L.R0v Y * Gs = L.R0v (Y - s)

def RuleD : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r) (Y : ℂ),
    L.Di * L.Ahat Y * L.D = L.Ahat (Y + 1) ∧
    L.Di * L.R0 Y * L.D = L.R0 (Y + 1) + algebraMap ℂ A L.TT * (L.Drb * L.Di * L.Ahat (Y + 1)) ∧
    L.Dbi * L.Ahatv Y * L.Db = L.Ahatv (Y - 1) ∧
    L.Dbi * L.R0v Y * L.Db = L.R0v (Y - 1) - algebraMap ℂ A L.TT * (L.Dr * L.Dbi * L.Ahatv (Y - 1)) ∧
    (∀ x ∈ Set.range L.cb ∪ Set.range L.cbi ∪ {L.ζb, L.ζbi},
      x * L.Ahat Y = L.Ahat Y * x ∧ x * L.R0 Y = L.R0 Y * x) ∧
    (∀ x ∈ Set.range L.c ∪ Set.range L.ci ∪ {L.ζ, L.ζi},
      x * L.Ahatv Y = L.Ahatv Y * x ∧ x * L.R0v Y = L.R0v Y * x)

def RuleSS : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r) (SS SSs : A),
    (∀ x ∈ L.fns, x * SS = SS * x) → (∀ l, L.p l * SS = SS * L.p l) →
    (∀ l, L.pb l * SS = SS * L.pb l) →
    L.nab * SS = SS * L.nab - L.ζb * L.GGi * SS → L.nabs * SS = SS * L.nabs - L.ζ * L.GGi * SS →
    (∀ x ∈ L.fns, x * SSs = SSs * x) → (∀ l, L.p l * SSs = SSs * L.p l) →
    (∀ l, L.pb l * SSs = SSs * L.pb l) →
    L.nab * SSs = SSs * L.nab + L.ζb * L.GGi * SSs →
    L.nabs * SSs = SSs * L.nabs + L.ζ * L.GGi * SSs →
    ∀ Y : ℂ,
      L.Ahat Y * (L.Drb * L.Dri * SS) = (L.Drb * L.Dri * SS) * L.Ahat (Y - 1) ∧
      L.R0 Y * (L.Drb * L.Dri * SS) = (L.Drb * L.Dri * SS) * L.R0 (Y - 1) ∧
      L.Ahatv Y * (L.Drb * L.Dri * SS) = (L.Drb * L.Dri * SS) * L.Ahatv (Y - 1) ∧
      L.R0v Y * (L.Drb * L.Dri * SS) = (L.Drb * L.Dri * SS) * L.R0v (Y - 1) ∧
      L.Ahat Y * (SSs * (L.Dr * L.Drbi)) = (SSs * (L.Dr * L.Drbi)) * L.Ahat (Y + 1) ∧
      L.R0 Y * (SSs * (L.Dr * L.Drbi)) = (SSs * (L.Dr * L.Drbi)) * L.R0 (Y + 1) ∧
      L.Ahatv Y * (SSs * (L.Dr * L.Drbi)) = (SSs * (L.Dr * L.Drbi)) * L.Ahatv (Y + 1) ∧
      L.R0v Y * (SSs * (L.Dr * L.Drbi)) = (SSs * (L.Dr * L.Drbi)) * L.R0v (Y + 1)

def RuleInv : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r) (Y : ℂ),
    L.ζbi * L.Ahat Y = L.Ahat Y * L.ζbi ∧ L.ζbi * L.R0 Y = L.R0 Y * L.ζbi ∧
    L.ζbi * L.Ahatv Y = L.Ahatv Y * L.ζbi ∧
    L.R0v Y * L.ζbi - L.ζbi * L.R0v Y = -(L.G * L.Dbi * L.Dbi * L.Ahatv Y) ∧
    L.ζi * L.Ahat Y = L.Ahat Y * L.ζi ∧ L.ζi * L.Ahatv Y = L.Ahatv Y * L.ζi ∧
    L.ζi * L.R0v Y = L.R0v Y * L.ζi ∧
    L.R0 Y * L.ζi - L.ζi * L.R0 Y = L.G * L.Di * L.Di * L.Ahat Y

end Formalism.FourierDecayAlt.R
end

section

namespace Formalism.FourierDecayAlt.L

open NumberField

def DualIdealInclusion : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (dd : FractionalIdeal (nonZeroDivisors (𝓞 E)) E),
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = dd⁻¹ →
    ∀ (ν : ℤ) (g : ℤ), g ≠ 0 → ∀ La : FractionalIdeal (nonZeroDivisors (𝓞 E)) E,
      dd ^ ν * FractionalIdeal.spanSingleton _ ((g : E) ^ 2) ≤ La →
      FractionalIdeal.spanSingleton _ (g : E) * FractionalIdeal.dual ℤ ℚ La ≤
        dd ^ (-(ν + 1)) * FractionalIdeal.spanSingleton _ ((g : E)⁻¹)

def DualLatticeInclusion : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (dd : FractionalIdeal (nonZeroDivisors (𝓞 E)) E),
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = dd⁻¹ →
    ∀ (ν : ℤ) (g : ℤ), g ≠ 0 → ∀ La : Submodule ℤ E,
      (∀ y ∈ (dd ^ ν * FractionalIdeal.spanSingleton _ ((g : E) ^ 2) :
        FractionalIdeal (nonZeroDivisors (𝓞 E)) E), y ∈ La) →
      ∀ x : E, (∀ y ∈ La, Algebra.trace ℚ E (x * y / g) ∈ (algebraMap ℤ ℚ).range) →
        x ∈ (dd ^ (-(ν + 1)) * FractionalIdeal.spanSingleton _ ((g : E)⁻¹) :
          FractionalIdeal (nonZeroDivisors (𝓞 E)) E)

end Formalism.FourierDecayAlt.L
end
