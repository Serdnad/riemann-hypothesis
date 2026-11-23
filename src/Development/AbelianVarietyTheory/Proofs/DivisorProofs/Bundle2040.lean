module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle451
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle521
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqTower

theorem gbig_and {Q₁ Q₂ : GP} (h₁ : GBig Q₁) (h₂ : GBig Q₂) : GBig (fun G μ C x b => Q₁ G μ C x b ∧ Q₂ G μ C x b) := by
  obtain ⟨F1, h1⟩ := h₁
  obtain ⟨F2, h2⟩ := h₂
  refine ⟨max F1 F2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, k1⟩ := h1 ε CF (le_of_max_le_left hCF)
  obtain ⟨C2, x2, k2⟩ := h2 ε CF (le_of_max_le_right hCF)
  exact ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hR T Lc μ₀ hμ G =>
    ⟨k1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ₀ hμ G,
      k2 C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ₀ hμ G⟩⟩

theorem gbig_mono {Q₁ Q₂ : GP} (h : GBig Q₁)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Lc.Is μ₀ → Q₁ G μ₀ C x b → Q₂ G μ₀ C x b) : GBig Q₂ := by
  obtain ⟨F, h⟩ := h
  refine ⟨F, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, k⟩ := h ε CF hCF
  exact ⟨C0, x0, fun C hC D large₂ he hx hR T Lc μ₀ hμ G => H G μ₀ C _ _ hμ (k C hC D large₂ he hx hR T Lc μ₀ hμ G)⟩

section Units

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem isAwayUnit_inv {m : ℕ} {x : K} (h : GlobalTheory.Square.IsAwayUnit m x) (hx : x ≠ 0) : GlobalTheory.Square.IsAwayUnit m x⁻¹ := by
  obtain ⟨a, k, k', ⟨b, hb⟩, e⟩ := h
  refine ⟨(m : 𝓞 K) ^ k * b, k', k + k', ⟨a, by rw [pow_add, hb]; ring⟩, ?_⟩
  have e2 : ((m : 𝓞 K) : K) ^ k' = (a : K) * (b : K) := by
    rw [← map_pow, hb]; push_cast; ring
  have e3 : ((m : 𝓞 K) : K) = (m : K) := by simp
  rw [e3] at e2
  rw [e2, ← e]
  push_cast
  field_simp

theorem stepRatio_self {T' : Type} (σ₀ : K →+* ℂ) (Qn : ℕ) (S0 : Finset T') (cc qq : T' → ℕ) (x : ℂ) :
    GlobalTheory.Square.StepRatio σ₀ Qn S0 cc qq x x :=
  ⟨1, fun _ => 1, fun _ => 1, GlobalTheory.Square.IsAwayUnit.one Qn, fun _ _ => ⟨one_dvd _, one_dvd _⟩, by simp⟩

theorem stepRatio_div {T' : Type} {σ₀ : K →+* ℂ} {Qn : ℕ} {S0 : Finset T'} {cc qq : T' → ℕ} {y y₀ : ℂ}
    (h : GlobalTheory.Square.StepRatio σ₀ Qn S0 cc qq y y₀) (h₀ : y₀ ≠ 0) : GlobalTheory.Square.StepRatio σ₀ Qn S0 cc qq (y / y₀) 1 := by
  obtain ⟨b, g, g', hb, hg, e⟩ := h
  exact ⟨b, g, g', hb, hg, by rw [e, mul_div_assoc, div_self h₀]⟩

end Units

section Descent

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} {W : G.Weil} {μ₀ : T}

def FacIn (W : G.Weil) : Prop := ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), IsStageC W i j p q X →
  ∃ lam : T → ℂ, Factor X W.ψ W.θ lam

def SmallIn (W : G.Weil) (μ₀ : T) : Prop := ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ)
  (e : ℕ) (Lf : T → ℂ → ℂ), IsStageC W i j p (q + 1) X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
    (∀ t, IsHeckeL (nuH G t i j) (Lf t)) → ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c y : T → ℂ),
      IsStageC W i j p q Y ∧ Y.IsConst W.ψ W.θ c ∧ (∀ t, y t ≠ 0 ∧ lam t * Lf t ((e + 1 : ℕ) : ℂ) = y t * c t) ∧
      ∀ t, GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal) (y t) (y μ₀)

def BigIn (W : G.Weil) (μ₀ : T) : Prop := ∀ (i j : Fin D.R.m) (p : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ)
  (e : ℕ) (Lf : T → ℂ → ℂ), IsStageC W i j (p + 1) 0 X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
    (∀ t, IsHeckeL (nuH G t i j) (Lf t)) → ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c y : T → ℂ),
      IsStageC W i j p 0 Y ∧ Y.IsConst W.ψ W.θ c ∧ (∀ t, y t ≠ 0 ∧ lam t = y t * Lf t (e : ℂ) * c t) ∧
      ∀ t, GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal) (y t) (y μ₀)

def cons (y : T → ℂ) (u : ℕ → T → ℂ) : ℕ → T → ℂ
  | 0 => y
  | k + 1 => u k

theorem cons_zero (y : T → ℂ) (u : ℕ → T → ℂ) : cons y u 0 = y := rfl

theorem cons_succ (y : T → ℂ) (u : ℕ → T → ℂ) (k : ℕ) : cons y u (k + 1) = u k := rfl

theorem descent (hF : FacIn W) (hs : SmallIn W μ₀) (hb : BigIn W μ₀) (i j : Fin D.R.m) (Lf : T → ℂ → ℂ)
    (hL : ∀ t, IsHeckeL (nuH G t i j) (Lf t)) :
    ∀ (q p e : ℕ) {A A' WW : HSp D} (X : Tri T A A' WW) (c : T → ℂ), IsStageC W i j p q X → X.IsConst W.ψ W.θ c →
      A.rank = A'.rank + 2 * e → p ≤ e →
      ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (cY : T → ℂ) (u : ℕ → T → ℂ) (κ : ℂ),
        IsStageC W i j 0 0 Y ∧ Y.IsConst W.ψ W.θ cY ∧ κ ≠ 0 ∧ (∀ k t, u k t ≠ 0 ∧ GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal) (u k t) (u k μ₀)) ∧
        ∀ t, c t * ∏ k ∈ range q, Lf t ((e + k + 1 : ℕ) : ℂ) =
          κ * (∏ k ∈ range (p + q), u k t) * cY t * ∏ k ∈ range p, Lf t ((e + q - k : ℕ) : ℂ) := by
  intro q
  induction q with
  | zero =>
    intro p
    induction p with
    | zero =>
      intro e A A' WW X c hX hc _ _
      refine ⟨A, A', WW, X, c, fun _ _ => 1, 1, hX, hc, one_ne_zero, fun k t => ⟨one_ne_zero, stepRatio_self _ _ _ _ _ _⟩,
        fun t => by simp⟩
    | succ p ih =>
      intro e A A' WW X c hX hc he hpe
      obtain ⟨lam, hl⟩ := hF i j _ _ A A' WW X hX
      obtain ⟨κ₁, hκ₁, e1⟩ := hl.eq_mul hc
      obtain ⟨B, B', W₁, Y, cY', y, hY, hcY', hy, hyr⟩ := hb i j p A A' WW X lam e Lf hX hl he hL
      have hr : B.rank = B'.rank + 2 * (e - 1) := by
        obtain ⟨-, -, a1, a2, -⟩ := hX
        obtain ⟨-, -, b1, b2, -⟩ := hY
        omega
      obtain ⟨B₂, B₂', W₂, Y₂, cY, u, κ, hY₂, hcY, hκ, hu, hid⟩ := ih (e - 1) Y cY' hY hcY' hr (by omega)
      refine ⟨B₂, B₂', W₂, Y₂, cY, cons y u, κ₁ * κ, hY₂, hcY, mul_ne_zero hκ₁ hκ,
        fun k t => ?_, fun t => ?_⟩
      · rcases k with _ | k
        · exact ⟨(hy t).1, hyr t⟩
        · exact hu k t
      · have h1 := hid t
        have h2 := (hy t).2
        simp only [range_zero, prod_empty, mul_one, add_zero] at h1 ⊢
        simp only [prod_range_succ', cons_succ, cons_zero, Nat.sub_zero]
        have e3 : ∏ k ∈ range p, Lf t ((e - (k + 1) : ℕ) : ℂ) = ∏ k ∈ range p, Lf t ((e - 1 - k : ℕ) : ℂ) :=
          prod_congr rfl fun k _ => by rw [show e - (k + 1) = e - 1 - k by omega]
        rw [e3, e1 t]
        linear_combination κ₁ * h2 + (κ₁ * y t * Lf t (e : ℂ)) * h1
  | succ q ih =>
    intro p e A A' WW X c hX hc he hpe
    obtain ⟨lam, hl⟩ := hF i j _ _ A A' WW X hX
    obtain ⟨κ₁, hκ₁, e1⟩ := hl.eq_mul hc
    obtain ⟨B, B', W₁, Y, cY', y, hY, hcY', hy, hyr⟩ := hs i j p q A A' WW X lam e Lf hX hl he hL
    have hr : B.rank = B'.rank + 2 * (e + 1) := by
      obtain ⟨-, -, a1, a2, -⟩ := hX
      obtain ⟨-, -, b1, b2, -⟩ := hY
      omega
    obtain ⟨B₂, B₂', W₂, Y₂, cY, u, κ, hY₂, hcY, hκ, hu, hid⟩ := ih p (e + 1) Y cY' hY hcY' hr (by omega)
    refine ⟨B₂, B₂', W₂, Y₂, cY, cons y u, κ₁ * κ, hY₂, hcY, mul_ne_zero hκ₁ hκ,
      fun k t => ?_, fun t => ?_⟩
    · rcases k with _ | k
      · exact ⟨(hy t).1, hyr t⟩
      · exact hu k t
    · have h1 := hid t
      have h2 := (hy t).2
      rw [show p + (q + 1) = p + q + 1 by omega]
      simp only [prod_range_succ', cons_succ, cons_zero]
      have e3 : ∏ k ∈ range q, Lf t ((e + (k + 1) + 1 : ℕ) : ℂ) = ∏ k ∈ range q, Lf t ((e + 1 + k + 1 : ℕ) : ℂ) :=
        prod_congr rfl fun k _ => by rw [show e + (k + 1) + 1 = e + 1 + k + 1 by omega]
      have e4 : ∏ k ∈ range p, Lf t ((e + (q + 1) - k : ℕ) : ℂ) = ∏ k ∈ range p, Lf t ((e + 1 + q - k : ℕ) : ℂ) :=
        prod_congr rfl fun k _ => by rw [show e + (q + 1) - k = e + 1 + q - k by omega]
      simp only [add_zero] at e3 ⊢
      rw [e3, e4, e1 t]
      linear_combination (κ₁ * ∏ k ∈ range q, Lf t ((e + 1 + k + 1 : ℕ) : ℂ)) * h2 + (κ₁ * y t) * h1

end Descent

end GlobalTheory.SqTower

namespace GlobalTheory.SqTower

open GlobalTheory.SqTower

end GlobalTheory.SqTower
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqStepBig

open GlobalTheory.Square

theorem awayUnit_inv {K : Type} [Field K] {m : ℕ} {x : K} (hx : x ≠ 0) (h : IsAwayUnit m x) : IsAwayUnit m x⁻¹ := by
  obtain ⟨a, k, k', ⟨b, hb⟩, hxa⟩ := h
  refine ⟨(m : 𝓞 K) ^ k * b, k', k + k', ?_, ?_⟩
  · rw [pow_add, hb]
    exact mul_dvd_mul_left _ (dvd_mul_left _ _)
  · have hb' : (m : K) ^ k' = (a : K) * (b : K) := by exact_mod_cast congrArg (fun z : 𝓞 K => (z : K)) hb
    have : ((((m : 𝓞 K) ^ k * b : 𝓞 K)) : K) = (m : K) ^ k * (b : K) := by push_cast; ring
    rw [this, hb', ← hxa]
    field_simp

theorem stepRatio_swap {K P : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {m : ℕ} {S₀ : Finset P} {cc qq : P → ℕ} {u u₀ C : ℂ} {ζ : K}
    (h : StepRatio σ m S₀ cc qq u₀ u) (h0 : u₀ ≠ 0) (hζ : IsAwayUnit m ζ) :
    StepRatio σ m S₀ cc qq (C * σ ζ * u) (C * u₀) := by
  obtain ⟨b, g, g', hb, hg, e⟩ := h
  have h1 : b * ∏ v ∈ S₀, (g v : K) / (g' v : K) ≠ 0 := fun hz => h0 (by rw [e, hz, map_zero, zero_mul])
  refine ⟨ζ * b⁻¹, g', g, hζ.mul (awayUnit_inv (left_ne_zero_of_mul h1) hb), fun v hv => (hg v hv).symm, ?_⟩
  have h2 : ∏ v ∈ S₀, (g' v : K) / (g v : K) = (∏ v ∈ S₀, (g v : K) / (g' v : K))⁻¹ := by
    rw [← Finset.prod_inv_distrib]; simp only [inv_div]
  have h3 : σ (b * ∏ v ∈ S₀, (g v : K) / (g' v : K)) ≠ 0 := (map_ne_zero σ).2 h1
  rw [h2, mul_assoc ζ, ← mul_inv, map_mul, map_inv₀, e]
  field_simp

theorem gbig_of_three {Q1 Q2 Q3 Q : GP} (h1 : GBig Q1) (h2 : GBig Q2) (h3 : GBig Q3)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q1 G μ₀ C x b → Q2 G μ₀ C x b → Q3 G μ₀ C x b → Q G μ₀ C x b) : GBig Q := by
  obtain ⟨a1, h1⟩ := h1
  obtain ⟨a2, h2⟩ := h2
  obtain ⟨a3, h3⟩ := h3
  refine ⟨max a1 (max a2 a3), fun ε CF hCF => ?_⟩
  obtain ⟨c1, x1, g1⟩ := h1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨c2, x2, g2⟩ := h2 ε CF (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCF)
  obtain ⟨c3, x3, g3⟩ := h3 ε CF (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCF)
  refine ⟨max c1 (max c2 c3), max x1 (max x2 x3), fun C hC D large₂ hε hx hR T Lc μ₀ hμ G => H G μ₀ C _ _ ?_ ?_ ?_⟩
  · exact g1 C (le_trans (le_max_left _ _) hC) D large₂ hε (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hμ G
  · exact g2 C (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC) D large₂ hε
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hμ G
  · exact g3 C (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC) D large₂ hε
      (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hμ G

theorem two_le_half {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} {W : G.Weil}
    {i j : Fin D.R.m} {p q e : ℕ} {A A' WW : HSp D} {X : Tri T A A' WW} (h : GlobalTheory.SqTower.IsStageC W i j p q X)
    (he : A.rank = A'.rank + 2 * e) : 2 ≤ e := by
  obtain ⟨hp, hq, hA, hA', -⟩ := h
  obtain ⟨k, hk⟩ := D.R.k_even
  obtain ⟨m, hm⟩ := D.R.m_even
  obtain ⟨t, ht⟩ := D.R.t_odd
  have h2 := D.R.two_le_m
  have h3 := D.R.three_m_lt_t
  have e1 : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  have e2 : sLen D = D.R.k + D.R.m - 1 + 6 := rfl
  simp only [pp, qq] at *
  omega

end GlobalTheory.SqStepBig

end

noncomputable section

namespace GlobalTheory.SqStepBig

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LFun

section IndefiniteRowSideFullHecke

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem reS_congr {n : ℕ} {X X₂ : Spc F E n} (Y : Spc F E n) (h : X₂.J = X.J ∧ X₂.L = X.L) : reS X₂ Y = reS X Y := by
  cases X; cases X₂; obtain ⟨h1, h2⟩ := h; cases h1; cases h2; rfl

theorem isHerm_rebase {B₀ B : Base F E} (he : B.emb = B₀.emb) {n r s : ℕ} {Y Y' : Spc F E n} (h : Y.IsHerm σ B₀ r s)
    (hθ : Y'.θ = Y.θ) (hb : ∀ v : B.P, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Y.L (Y'.bas v)) : (reS Y Y').IsHerm σ B r s :=
  { herm := h.herm, sig := fun w => by rw [he]; exact h.sig w, lat := h.lat, dual := h.dual
    cartan := fun w => by rw [he]; show IsCartan _ (Y'.θ w); rw [hθ]; exact h.cartan w
    bas := hb }

theorem isSkew_rebase {B₀ B : Base F E} (he : B.emb = B₀.emb) {n r s : ℕ} {Y Y' : Spc F E n} (h : Y.IsSkew σ B₀ r s)
    (hθ : Y'.θ = Y.θ) (hb : ∀ v : B.P, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Y.L (Y'.bas v)) : (reS Y Y').IsSkew σ B r s :=
  { skew := h.skew, sig := fun w => by rw [he]; exact h.sig w, lat := h.lat, dual := h.dual
    cartan := fun w => by rw [he]; show IsCartan _ (Y'.θ w); rw [hθ]; exact h.cartan w
    bas := hb }

theorem isGood_reG {B : Base F E} {a a' : ℕ} {Γ : Geo σ a a'} (g : Γ.IsGood B) {V : Spc F E a} {V' : Spc F E a'}
    {Z : Spc F E (a + a')} (hV : (reS Γ.V V).IsHerm σ B (a - Γ.p) Γ.p) (hV' : (reS Γ.V' V').IsHerm σ B Γ.q (a' - Γ.q))
    (hZ : (reS Γ.W Z).IsSkew σ B (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q)) : (reG Γ V V' Z).IsGood B :=
  ⟨g.lt, g.even, g.kappa, g.eBig, g.aBig, hV, hV', hZ, ⟨g.hM.rat, g.hM.vac, g.hM.std, g.hM.haar, g.hM.dom⟩,
    ⟨g.hM'.rat, g.hM'.vac, g.hM'.std, g.hM'.haar, g.hM'.dom⟩⟩

theorem resEtaPow_quot {R K' : Type} [CommRing R] [CommRing K'] [Algebra R K'] {K : Subgroup Rˣ}
    {χ χ' : K'ˣ →* Circle} {n m : ℕ} (h : GlobalTheory.WeilM.ResEtaPow K χ n) (h' : GlobalTheory.WeilM.ResEtaPow K χ' m) :
    GlobalTheory.WeilM.ResEtaPow K (χ / χ') (n + m) := by
  intro a
  rw [MonoidHom.div_apply, Circle.coe_div, h a, h' a]
  split_ifs
  · simp
  · rw [div_eq_mul_inv, ← inv_pow, inv_neg, inv_one, ← pow_add]

theorem stepAlpha_cast {e₁ e₂ s : ℤˣ} (h : StepAlpha σ e₁ e₂ s) (B : Base F E) {a b a' e : ℕ} (hab : a = b + 2)
    (he : a = a' + 2 * e) (Γ : Geo σ a a') (Γ₁ : Geo σ b a') (H : Plane E a b) (H' : Plane E (a + a') (b + a'))
    (R : RealMaps F a a') (R₁ : RealMaps F b a') (h1 : Γ₁.V' = Γ.V') (h2 : Γ.q = 0) (h3 : Γ₁.q = 0) (h4 : Γ₁.p + 1 = Γ.p)
    (h5 : H.IsAdapted σ B Γ.V Γ₁.V 0 (b + 1)) (h6 : H'.IsAdapted σ B Γ.W Γ₁.W 0 (b + 1)) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ X om om' Rf om₁ om₁' Rf₁, IsMatched B Γ X om om' R Rf → IsMatched B Γ₁ X om₁ om₁' R₁ Rf₁ →
      ∀ c c₁, IsConst B Γ X om om' R Rf c → IsConst B Γ₁ X om₁ om₁' R₁ Rf₁ c₁ →
        c = C * stepFac B X e₁ e₂ s H.𝔟 H'.𝔟 (1 - (e : ℤ)) * charL X.ν (X.S₀ : Set (Pl F)) (e : ℂ) * c₁ := by
  subst hab
  have := h B b a' Γ Γ₁ H H' R R₁ h1 h2 h3 h4 h5 h6
  rwa [show (b + 2 - a') / 2 = e by omega] at this

end IndefiniteRowSideFullHecke

theorem gbig_both {Q₁ Q₂ : GP} (h₁ : GBig Q₁) (h₂ : GBig Q₂) : GBig fun G μ C x b => Q₁ G μ C x b ∧ Q₂ G μ C x b :=
  gbig_of_three h₁ h₂ h₂ fun _ _ _ _ _ a b _ => ⟨a, b⟩

end GlobalTheory.SqStepBig

end

noncomputable section

namespace GlobalTheory.SqStepBig

open GlobalTheory.Square

end GlobalTheory.SqStepBig

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.UnfoldLoss

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stairElt_diag (G : Grid k) (hs : 1 ≤ G.s) (ϖ : kˣ) (e : ℕ) (J : G.Level) (X : ℕ × ℕ) :
    ∃ n : Fin (G.rank X) → ℕ, (∀ a, n a ≤ e * (G.m - 1)) ∧
      (Reps.through hs J (stair G ϖ e)).elt (fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) X =
        diagGL fun a => ϖ ^ n a := by
  have h1 : ∀ Y : ℕ × ℕ, ∃ n : Fin (G.rank Y) → ℕ, (∀ a, n a ≤ e * (G.m - 1)) ∧
      (1 : GL (Fin (G.rank Y)) k) = diagGL fun a => ϖ ^ n a := fun Y =>
    ⟨fun _ => 0, fun _ => Nat.zero_le _, Units.ext (by simp)⟩
  have h2 : ∀ j : ℕ, ∃ n : Fin (G.rank (G.m, j)) → ℕ, (∀ a, n a ≤ e * (G.m - 1)) ∧
      stair G ϖ e j = diagGL fun a => ϖ ^ n a := fun j =>
    ⟨fun a => e * (a.val + 1 - topRank G j), fun a => Nat.mul_le_mul_left _ (by
      have := topRank_add hs j; have := a.2; omega), rfl⟩
  obtain ⟨i, j⟩ := X
  by_cases hi : i = G.m
  · subst hi
    by_cases hj : j + 2 ≤ G.m
    · borelize k
      rw [through_elt _ hj]; exact h2 j
    · rw [Reps.elt, onColumn_apply]
      cases j with
      | zero => exact h2 0
      | succ j =>
        have : ¬ j < G.m - 2 := by omega
        simp only [dif_neg this]
        exact h1 _
  · rw [Reps.elt, onColumn, dif_neg hi]
    exact h1 _

theorem valuation_fill_sub_le (G : Grid k) (hs : 1 ≤ G.s) (ϖ : kˣ) (n : ℕ) (x : ColArgs G) (y : RowArgs G)
    (v l : Vars G) (hl : l ∈ varLat G ϖ n) (b : Edge) (r : Fin (G.rank b.tgt)) (s : Fin (G.rank b.src)) :
    valuation k ((fill hs x y (v + l) - fill hs x y v) b r s) ≤ valuation k ((ϖ ^ n : kˣ) : k) := by
  rcases b with ⟨i, j⟩ | ⟨i, j⟩ <;> simp only [Pi.sub_apply, Matrix.sub_apply, fill] <;> split_ifs
  · simp only [Matrix.transpose_apply, Matrix.submatrix_apply, downMap]
    split_ifs with h
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, stepPt, Matrix.add_apply, Matrix.of_apply,
        add_sub_add_left_eq_sub]
      split_ifs
      · simp only [Pi.add_apply, add_sub_cancel_left]
        exact hl ⟨j, h⟩ _
      · simp
    · simp
    · simp
  all_goals simp

end

theorem moved_stair_periodic : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : Grid k) (hs : 1 ≤ G.s)
    (ϖ : kˣ), IsUnif ϖ → ∀ (e : ℕ) (T : G.Args → ℂ), G.IsTensor ϖ e (oppositePath G.m) T → ∀ (J : G.Level) (keep : Bool)
    (x : ColArgs G) (y : RowArgs G) (v l : Vars G), l ∈ varLat G ϖ (G.m * e) →
    moved G keep ((Reps.through hs J (stair G ϖ e)).elt fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) T (fill hs x y (v + l)) =
      moved G keep ((Reps.through hs J (stair G ϖ e)).elt fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) T (fill hs x y v) := by
  intro k _ _ _ _ G hs ϖ hϖ e T hT J keep x y v l hl
  rcases Nat.eq_zero_or_pos G.m with hm | hm
  · have : l = 0 := funext fun j => absurd j.2 (by omega)
    rw [this, add_zero]
  have hd := stairElt_diag G hs ϖ e J
  generalize (Reps.through hs J (stair G ϖ e)).elt (fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) = g at hd ⊢
  have hf := valuation_fill_sub_le G hs ϖ _ x y v l hl
  have hsum : G.moveArgs .one g (fill hs x y (v + l)) =
      G.moveArgs .one g (fill hs x y v) + G.moveArgs .one g (fill hs x y (v + l) - fill hs x y v) := by
    funext b
    simp only [Grid.moveArgs, Pi.add_apply, Pi.sub_apply, Matrix.mul_sub, Matrix.sub_mul, add_sub_cancel]
  simp only [moved, Grid.pathAct]
  rw [hsum, hT.2.2]
  intro b r
  generalize fill hs x y (v + l) - fill hs x y v = d at hf
  obtain ⟨n, -, hn⟩ := hd b.tgt
  obtain ⟨n', hn1, hn'⟩ := hd b.src
  have h0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 (by simp)
  have h1 : valuation k (ϖ : k) ≤ 1 := hϖ.mem
  rw [SplitFlip.stdLat, smul_diagLat, mem_diagLat]
  intro s
  have hv : (G.moveArgs .one g d b).row r s = (ϖ : k) ^ n r * d b r s * ((ϖ : k) ^ n' s)⁻¹ := by
    have hinv : ((diagGL fun a => ϖ ^ n' a : GL (Fin (G.rank b.src)) k)⁻¹).val =
        Matrix.diagonal fun a => ((ϖ : k) ^ n' a)⁻¹ := by
      rw [Matrix.coe_units_inv]
      refine Matrix.inv_eq_right_inv ?_
      simp [Matrix.diagonal_mul_diagonal]
    simp only [Grid.moveArgs, Assignment.read, invT_inv_val, invT_val, hn, hn', hinv, diagGL_val,
      Matrix.diagonal_transpose, Matrix.row, Matrix.mul_diagonal, Matrix.diagonal_mul, Units.val_pow_eq_pow_val]
  have h2 := hf b r s
  rw [hv]
  simp only [map_mul, map_inv₀, map_pow, Units.val_pow_eq_pow_val, Pi.one_apply, mul_one] at h2 ⊢
  rw [mul_inv_le_iff₀ (pow_pos h0 _), ← pow_add]
  refine (mul_le_of_le_one_left' (pow_le_one' h1 _)).trans (h2.trans (pow_le_pow_right_of_le_one' h1 ?_))
  have := hn1 s
  obtain ⟨m', hm'⟩ := Nat.exists_eq_add_of_le' hm
  rw [hm'] at this ⊢
  simp only [Nat.succ_eq_add_one, zero_add, Nat.add_sub_cancel] at this ⊢
  nlinarith

end GlobalTheory.UnfoldLoss
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw


theorem _root_.GlobalTheory.T.variablesUniformizerPowerLattice_basis_open_volume : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (G : Grid k) (ν : Measure k), IsUnitVol ν → ∀ ϖ : kˣ, IsUnif ϖ →
    (∀ s ∈ nhds (0 : Vars G), ∃ n : ℕ, (varLat G ϖ n : Set (Vars G)) ⊆ s) ∧
    ∀ n : ℕ, IsOpen (varLat G ϖ n : Set (Vars G)) ∧ varsVol G ν (varLat G ϖ n : Set (Vars G)) ≠ ⊤ ∧
      (varsVol G ν).real (varLat G ϖ n : Set (Vars G)) = ((resCard k : ℝ)⁻¹) ^ (n * varCount G) := by
  first | exact @GlobalTheory.UnfoldLoss.LatVol.varLat_basis_open_vol | exact GlobalTheory.UnfoldLoss.LatVol.varLat_basis_open_vol | (intros; apply GlobalTheory.UnfoldLoss.LatVol.varLat_basis_open_vol <;> assumption)
end
