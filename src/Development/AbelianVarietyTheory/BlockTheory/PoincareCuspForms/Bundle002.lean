module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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

namespace GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped Matrix ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def IsOrthonormalFrame (X : Data E r) (x0 : Frame X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x0 τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

def Base (X : Data E r) : Type := {x0 : Frame X.Ψ r // IsOrthonormalFrame X x0}

variable (X : Data E r)

def zBlock (z : V (nd X)) (τ : X.Ψ) :
    Matrix {a : Fin r // X.p0 ≤ (a : ℕ)} {b : Fin r // (b : ℕ) < X.p0} ℂ :=
  Matrix.of fun a b => nmat X z τ a.1 b.1

def zFrame (z : V (nd X)) : Frame X.Ψ r := fun τ a b =>
  if X.p0 ≤ (a : ℕ) ∧ (b : ℕ) < X.p0 then nmat X z τ a b else if a = b then 1 else 0

def leviFrame (z : V (nd X)) : Frame X.Ψ r := fun τ a b =>
  if X.p0 ≤ (a : ℕ) ∧ (b : ℕ) < X.p0 then 0 else nmat X z τ a b

def nFrame (z : V (nd X)) : Frame X.Ψ r := rmul (zFrame X z) (leviFrame X z)

def point (x0 : Base X) (z : V (nd X)) : Frame X.Ψ r := rmul x0.1 (nFrame X z)

def zNorm (z : V (nd X)) (τ : X.Ψ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (zBlock X z τ))‖

def Om : Set (V (nd X)) := {z | ∀ τ : X.Ψ, zNorm X z τ < 1}

def zDet (z : V (nd X)) (τ : X.Ψ) : ℝ := ((1 - (zBlock X z τ)ᴴ * zBlock X z τ).det).re

def rho (z : V (nd X)) : ℝ := ∑ τ : X.Ψ, -Real.log (zDet X z τ)

def density (x0 : Base X) (z : V (nd X)) : ℝ :=
  ∏ τ : X.Ψ, ∏ i : Fin r, (‖dmin X.Gm (point X x0 z) τ i.castSucc‖ ^ 2)⁻¹

def mu (x0 : Base X) : Measure (V (nd X)) :=
  (volume.restrict (Om X)).withDensity fun z => ENNReal.ofReal (density X x0 z)

theorem zDet_pos {z : V (nd X)} (hz : z ∈ Om X) (τ : X.Ψ) : 0 < zDet X z τ := by
  set Z := zBlock X z τ with hZ
  have hn : zNorm X z τ < 1 := hz τ
  have hquad : ∀ x, star x ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ x) = star x ⬝ᵥ x - star (Z *ᵥ x) ⬝ᵥ (Z *ᵥ x) := by
    intro x
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec,
      Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  have hsq : ∀ {ι : Type} [Fintype ι] (v : ι → ℂ), star v ⬝ᵥ v = ((‖WithLp.toLp 2 v‖ ^ 2 : ℝ) : ℂ) := by
    intro ι _ v
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 v)
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm] at h
    rw [Complex.ofReal_pow]
    exact h
  have hpd : (1 - Zᴴ * Z).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · simp [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
    · intro x hx
      rw [hquad, hsq, hsq, ← Complex.ofReal_sub, Complex.zero_lt_real, sub_pos]
      have hx0 : 0 < ‖WithLp.toLp 2 x‖ := norm_pos_iff.mpr (by simpa using hx)
      have hle : ‖WithLp.toLp 2 (Z *ᵥ x)‖ ≤ zNorm X z τ * ‖WithLp.toLp 2 x‖ :=
        (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Z)).le_opNorm (WithLp.toLp 2 x)
      have hlt : ‖WithLp.toLp 2 (Z *ᵥ x)‖ < ‖WithLp.toLp 2 x‖ :=
        lt_of_le_of_lt hle (by nlinarith [norm_nonneg (WithLp.toLp 2 (Z *ᵥ x))])
      exact pow_lt_pow_left₀ hlt (norm_nonneg _) two_ne_zero
  have hdet := hpd.det_pos
  exact (Complex.lt_def.mp hdet).1

end

end GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames
end

section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements

open NumberField ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def OpNormLe {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (A : Matrix (Fin r) (Fin r) E)
    (c : ℝ) : Prop :=
  ∀ u : Fin r → ℂ, X.maj x τ ((A.map τ.1).mulVec u) ≤ c ^ 2 * X.maj x τ u

def OpNormLtOne {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (A : Matrix (Fin r) (Fin r) E) :
    Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ OpNormLe X x τ A c

def IsLatEnd {r : ℕ} (L : Submodule (𝓞 E) (Fin r → E)) (N : Matrix (Fin r) (Fin r) E) : Prop :=
  ∀ v ∈ L, N.mulVec v ∈ L

def NoContraction {r : ℕ} (X : DataX E r) (x : Frame X.Ψ r) : Prop :=
  ∀ N : Matrix (Fin r) (Fin r) E, IsLatEnd X.L' N → (∀ τ : X.Ψ, OpNormLtOne X.toData x τ N) → N = 0

def NoShortVector {r : ℕ} (X : DataX E r) (x : Frame X.Ψ r) : Prop :=
  ∀ v ∈ X.L', v ≠ 0 → (fdeg E : ℝ) ≤ ∑ τ : X.Ψ, X.maj x τ (Data.emb τ.1 v)

def IsTotallySplitPrime (E : Type) [Field E] [NumberField E] (g : ℕ) : Prop :=
  g.Prime ∧ ((Ideal.span {(g : ℤ)}).primesOver (𝓞 E)).ncard = Module.finrank ℚ E

def IsUnipotentModOver {r : ℕ} (L : Submodule (𝓞 E) (Fin r → E)) (g : ℕ) (γ : GL (Fin r) E) : Prop :=
  ∀ P ∈ (Ideal.span {(g : ℤ)}).primesOver (𝓞 E), ∃ k : ℕ, ∀ v ∈ L,
    (((γ : Matrix (Fin r) (Fin r) E) - 1) ^ k).mulVec v ∈ P • L

def BalancedPointStatement (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : DataX E r), ∃ x ∈ X.dom, NoContraction X x ∧ NoShortVector X x

def SmallElementStatement (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (g : ℕ), IsTotallySplitPrime E g → 3 * r < g →
    ∀ Γo : Subgroup (GL (Fin r) E), (∀ γ ∈ Γo, IsUStab X.Gm X.L' γ) →
    (∀ γ ∈ Γo, IsUnipotentModOver X.L' g γ) →
    ∀ x ∈ X.dom, NoContraction X x →
    ∀ γ ∈ Γo, (∀ τ : X.Ψ, OpNormLe X.toData x τ (γ : Matrix (Fin r) (Fin r) E)
      (Real.exp (1 / (3 * (r : ℝ))))) → γ = 1

end

end GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements
end
