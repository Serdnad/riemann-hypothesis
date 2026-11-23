module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle111
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.FlagMeas.SatModel

open Formalism.MainNotions.S GlobalTheory.Count

theorem volU_pos (i : ℕ) : 0 < volU i := by
  unfold volU sphV
  have := Real.pi_pos
  refine mul_pos (Finset.prod_pos fun l _ => by positivity) (by positivity)

theorem cIw_pos (p q : ℕ) {a : ℕ} (j : Fin a → ℕ) : 0 < cIw p q j := by
  unfold cIw
  have := volU_pos
  refine div_pos (mul_pos (by positivity) (mul_pos (this _) (this _)))
    (mul_pos (mul_pos (Finset.prod_pos fun i _ => mul_pos (this _) (by positivity)) (this _)) (this _))

end GlobalTheory.FlagMeas.SatModel
end
end

section

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.GaussMean

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

def qEps {n : ℕ} (ε : Fin n → Bool) (y : Fin n → ℂ) : ℝ := ∑ i, (if ε i then 1 else -1) * ‖y i‖ ^ 2

def gauss {n : ℕ} (y : Fin n → ℂ) : ℝ := Real.exp (-∑ i, ‖y i‖ ^ 2)

def gaussDens {n : ℕ} (ε : Fin n → Bool) (β : ℝ) : ℝ :=
  deriv (fun t : ℝ => ∫ y in {y : Fin n → ℂ | qEps ε y ≤ t}, gauss y) β

def sgn (R : Type) [Ring R] (s : Bool) : R := if s then 1 else -1

def gaussSum (I : AutInst) (β : I.E) (x : I.GA) : ENNReal :=
  ∑' y : {y : Fin I.n → I.E // y ∈ lamX I x ∧ star y ⬝ᵥ (I.J *ᵥ y) = β},
    ENNReal.ofReal (∏ v, gauss (((uMat (x.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (y.1 i)))

def meanConst (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ) : ℝ :=
  (2 * Formalism.HermitianLatticesTheory.vInv E) ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) / 2) * (Formalism.HermitianLatticesTheory.vInv E ^ (M * Formalism.HermitianLatticesTheory.fDeg E))⁻¹ /
    Formalism.HermitianLatticesTheory.lValEta E M

def SiegelMean : Prop :=
  ∀ (I : AutInst), 3 ≤ I.n → ∀ (s : Bool) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
    (fund : Set I.GA), I.IsFundDom (I.muA μf) fund →
    I.muA μf fund < ⊤ ∧
    ∫⁻ x in fund, gaussSum I (sgn I.E s) x ∂(I.muA μf) =
      I.muA μf fund * ENNReal.ofReal (meanConst I.E I.n * ∏ v, gaussDens (I.ε v) (sgn ℝ s))

def IsPerpInst (I I' : AutInst) (e : I'.E ≃+* I.E) (s : Bool) (x : Fin I.n → I.E)
    (A : Matrix (Fin I.n) (Fin I'.n) I.E) (xf : I.Gf) : Prop :=
  (∀ y, e (star y) = star (e y)) ∧ I'.n + 1 = I.n ∧ star x ⬝ᵥ (I.J *ᵥ x) = sgn I.E s ∧
    star x ᵥ* (I.J * A) = 0 ∧ Aᴴ * I.J * A = I'.J.map e ∧ x ∈ lamX I (1, xf) ∧
    ∀ y : Fin I'.n → I'.E, y ∈ I'.L ↔ A *ᵥ (fun i => e (y i)) ∈ lamX I (1, xf)

def GaugeUnfold : Prop :=
  ∀ (I I' : AutInst) (e : I'.E ≃+* I.E) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E)
    (xf : I.Gf), 3 ≤ I.n → IsPerpInst I I' e s x A xf →
    ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
      (c' : InfinitePlace I'.F → ℝ) (μf' : Measure I'.Gf) [SigmaFinite μf'] [μf'.IsHaarMeasure]
      (fund : Set I.GA), IsGaugeAll I c → IsGaugeAll I' c' → I.IsFundDom (I.muA μf) fund →
      ENNReal.ofReal (∏ v, c v) * (∫⁻ g in fund, gaussSum I (sgn I.E s) g ∂(I.muA μf)) / μf I.Kset =
        gaugeVol I' c' μf' * ENNReal.ofReal (2 ^ (I.n * I.f) * ∏ v, gaussDens (I.ε v) (sgn ℝ s))

theorem gauss_pos {n : ℕ} (y : Fin n → ℂ) : 0 < gauss y := Real.exp_pos _

end GlobalTheory.GaussMean
end
end

section

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.FlagBase

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

def IsAdapted (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) {a : ℕ} (j : Fin a → ℕ)
    (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E))
    (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E) : Prop :=
  (∀ y, e (star y) = star (e y)) ∧ I.n = I₀.n + 2 * ∑ i, j i ∧ (∀ i, Submodule.IsFullLattice I.E (Λ i)) ∧
    (∀ i k, (T i)ᴴ * I.J * T k = 0 ∧ (T' i)ᴴ * I.J * T' k = 0 ∧ (i ≠ k → (T i)ᴴ * I.J * T' k = 0)) ∧
    (∀ i, (T i)ᴴ * I.J * T' i = 1 ∧ (T i)ᴴ * I.J * T₀ = 0 ∧ (T' i)ᴴ * I.J * T₀ = 0) ∧
    T₀ᴴ * I.J * T₀ = I₀.J.map e ∧
    (∀ z, z ∈ lamX I (1, xf) ↔ ∃ (u u' : ∀ i, Fin (j i) → I.E) (y : Fin I₀.n → I₀.E), (∀ i, u i ∈ Λ i) ∧
      (∀ i, ∀ t ∈ Λ i, star t ⬝ᵥ u' i ∈ (algebraMap (𝓞 I.E) I.E).range) ∧ y ∈ lamX I₀ (1, x₀) ∧
      z = ∑ i, T i *ᵥ u i + ∑ i, T' i *ᵥ u' i + T₀ *ᵥ fun l => e (y l)) ∧
    ∀ k z, z ∈ S k ↔ ∃ u : ∀ i, Fin (j i) → I.E, (∀ i, u i ∈ Λ i) ∧ (∀ i : Fin a, ¬ i.castSucc < k → u i = 0) ∧
      z = ∑ i, T i *ᵥ u i

def latGroup (I : AutInst) (xf : I.Gf) : Set I.Ginf :=
  {g | ∃ γ ∈ I.GFset, γ.1 = g ∧ xf⁻¹ * γ.2 * xf ∈ I.Kset}

def flagGroup (I : AutInst) (xf : I.Gf) {a : ℕ} (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) :
    Set I.Ginf :=
  {g | g ∈ latGroup I xf ∧ ∀ v k, ∀ y ∈ flagAt I S v k, uMat (g v) *ᵥ y ∈ flagAt I S v k}

def leviGroup (I : AutInst) (xf : I.Gf) {a : ℕ} (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) :
    Set I.Ginf :=
  {m | (∀ v, m v ∈ flagM (I.ε v) (flagAt I S v)) ∧
    ∃ g ∈ flagGroup I xf S, ∃ u : I.Ginf, (∀ v, u v ∈ flagN (I.ε v) (flagAt I S v)) ∧ g = u * m}

def sizesAt (I : AutInst) (xf : I.Gf) {a : ℕ} (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E))
    (g : I.Ginf) : Fin a → ℝ :=
  fun i => Formalism.HN.sizeQ (bas I) (frm I (g, xf)) (S i.succ) (S i.castSucc)

def slabVol (E : Type) [Field E] [NumberField E] (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)) : ENNReal :=
  covol (autGL E j Λ) (haarGL E j) {x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1}

section Mean

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

abbrev VecInf : Type := InfinitePlace E → Fin j → ℂ

def latAt (Λ : Submodule (𝓞 E) (Fin j → E)) (g : MatInf E j) : Submodule ℤ (VecInf E j) :=
  Submodule.span ℤ ((fun (y : Fin j → E) (w : InfinitePlace E) =>
    (Matrix.of (g w))⁻¹ *ᵥ fun a => w.embedding (y a)) '' (Λ : Set (Fin j → E)))

def dualAt (L : Submodule ℤ (VecInf E j)) : Submodule ℤ (VecInf E j) :=
  Submodule.span ℤ {y | ∀ x ∈ L, ∃ z : ℤ, ∑ w, (x w ⬝ᵥ y w).re = z}

def latMean (F : Submodule ℤ (VecInf E j) → ENNReal) : ENNReal :=
  ∑' c : Quot (fun Λ Λ' : {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsFullLattice E Λ} =>
      ∃ γ : GL (Fin j) E, ∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ'.1 ↔ y ∈ Λ.1),
    covol (autGL E j (Quot.out c).1) ((haarGL E j).withDensity fun g => F (latAt E j (Quot.out c).1 g))
      {g | 0 < detNorm E j g}

def covAt (L : Submodule ℤ (VecInf E j)) : ℝ := ZLattice.covolume L volume

def gaussV (x : VecInf E j) : ℝ := Real.exp (-Real.pi * ∑ w, ∑ a, ‖x w a‖ ^ 2)

end Mean

end GlobalTheory.FlagBase
end
end

section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

def Sg2 (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (x : Mat k r) : ℝ :=
  Finset.univ.fold max 1 fun a : Fin (r + 1) => max (lA k r z x a) (lA k r z x a)⁻¹

def Dj (k r : ℕ) {j : ℕ} (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) : ℝ :=
  ‖Dmin k r z z' γ ⟨j, by omega⟩‖

def Yj (k r : ℕ) {j : ℕ} (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ x : Mat k r) : ℝ :=
  gramProj (Ppos k r z z' γ x) (fun a : Fin j => x⁻¹ *ᵥ (γ⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj a)))) / Dj k r hj z z' γ

def XstJ (k r j : ℕ) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) :=
  Submodule.span ℂ (Set.range fun a : {a : Fin r // a.val < j} => bvec (esI k r a.1))

def XJ (k r j : ℕ) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) :=
  Submodule.span ℂ (Set.range fun a : {a : Fin r // a.val < j} => bvec (eI k r a.1))

def IsNormal0 (k r : ℕ) {j : ℕ} (hj : j ≤ r) (β : Fin r → ℕ) (c : ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) : Prop :=
  g ∈ GG k r ∧ ‖c‖ = 1 ∧ g *ᵥ z' = c • z ∧ Monotone β ∧
    (∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) ∧
    (∀ a : Fin r, a.val < j → g⁻¹ *ᵥ bvec (eI k r a) ∈ XstJ k r j ∧ g *ᵥ bvec (eI k r a) ∈ XstJ k r j) ∧
    (∀ a : Fin r, j ≤ a.val → g *ᵥ bvec (eI k r a) = c • bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = c • bvec (esI k r a)) ∧
    BlockAnti (fun a : Fin j => β (Fin.castLE hj a)) ((Zr k r g).submatrix (Fin.castLE hj) (Fin.castLE hj))

abbrev PTop (k r j : ℕ) :=
  ({a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ) × ({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ)

abbrev PSec (k r j : ℕ) :=
  ({a : Fin r // a.val < j} → Fin (k + 1) → ℂ) × ({p : UT r // p.1.1.val < j} → ℂ) × ({a : Fin r // a.val < j} → ℝ)

def pTop (k r j : ℕ) (q : PTop k r j) : Mat k r :=
  pOf k r (fun a => if h : j ≤ a.val then q.1 ⟨a, h⟩ else 0, fun p => if h : j ≤ p.1.1.val then q.2.1 ⟨p, h⟩ else 0,
    fun a => if h : j ≤ a.val then q.2.2 ⟨a, h⟩ else 0)

def pSec (k r j : ℕ) (q : PSec k r j) : Mat k r :=
  pOf k r (fun a => if h : a.val < j then q.1 ⟨a, h⟩ else 0, fun p => if h : p.1.1.val < j then q.2.1 ⟨p, h⟩ else 0,
    fun a => if h : a.val < j then q.2.2 ⟨a, h⟩ else 0)

def rEl (k r j : ℕ) (β : Fin r → ℕ) (q : (UTin β → ℂ) × PTop k r j) : Mat k r := uEmb k r (upperIn β q.1) * pTop k r j q.2

def sEl (k r j : ℕ) (β : Fin r → ℕ) (q : PSec k r j × (UToff β → ℂ)) : Mat k r := pSec k r j q.1 * uEmb k r (upperOff β q.2)

def lebR0 (k r j : ℕ) (β : Fin r → ℕ) : Measure (Mt k r) :=
  (volume : Measure ((UTin β → ℂ) × PTop k r j)).map fun q => Matrix.of.symm (rEl k r j β q)

def IsNormalFormStabilizerMeasure (k r : ℕ) {j : ℕ} (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) (s : ℝ) (μR : Measure (Mt k r)) : Prop :=
  inWb k r z ∧ inWb k r z' ∧ 0 < Tz k r z ∧
    ∃ n₁ ∈ Nset k r, ∃ n₂ ∈ Nset k r, ∃ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), IsNormal0 k r hj β c z z' g₀ ∧
      γ = n₁ * g₀ * n₂ ∧ μR = (ENNReal.ofReal s • lebR0 k r j β).map (conjM n₂⁻¹)

def Eset0 (k r : ℕ) {j : ℕ} (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) (R₀ y : ℝ) : Set (Mt k r) :=
  {x | Matrix.of x ∈ GG k r ∧ Sg2 k r z' (Matrix.of x) ≤ R₀ ∧ Sg2 k r z (γ * Matrix.of x) ≤ R₀ ∧
    y < Yj k r hj z z' γ (Matrix.of x) ∧ Yj k r hj z z' γ (Matrix.of x) ≤ 2 * y}

def fibVol0 (k r j : ℕ) (R₀ De y : ℝ) : ℝ :=
  (4 * r : ℝ) ^ (4 * r ^ 2) * (R₀ ^ (2 * r) * De) ^ (8 * r ^ 2) *
    (Real.pi * Real.exp 1 / ((k - 1 - j : ℕ) : ℝ)) ^ (j * (k - 1 - j)) * (2 * y) ^ (2 * (k - 1 - j))

def TailBd {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] (z : Fin (2 * r + k + 1) → ℂ) (νS : Measure (Mt k r))
    (Φ : Mat k r → Wp) (q : ℕ) (H₁ : ℝ) : Prop :=
  ∀ la : ℝ, 0 < la →
    ∫⁻ x, Set.indicator {x : Mt k r | ∃ a : Fin (r + 1), la * H₁ ≤ max (lA k r z (Matrix.of x) a) (lA k r z (Matrix.of x) a)⁻¹}
        (fun x => (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2) x ∂νS ≤
      ENNReal.ofReal (2 * (2 * r + 2 : ℝ) * la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ

def sgV (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) (H₁ : ℝ) : ℝ :=
  Finset.univ.fold max 1 fun l : Fin (r + 1) => ‖Dmin k r z z' γ l.castSucc‖ / (2 * H₁) ^ (2 * r)

def degBd (k r j q : ℕ) (H₁ De D sg : ℝ) : ℝ :=
  16 * (4 * r + 4 : ℝ) * (4 * r : ℝ) ^ (4 * r ^ 2) * (2 * H₁) ^ (16 * r ^ 3 + 4 * r) * De ^ (8 * r ^ 2 + 2) *
    (8 * Real.pi * Real.exp 1 / ((k - 1 - j : ℕ) : ℝ)) ^ (j * (k - 1 - j)) * (D ^ (k - 1 - j))⁻¹ *
    sg ^ (-(((q : ℝ) - 16 * r ^ 3 - 4 * r - 1) / r))

end GlobalTheory.Amp
end
end

section

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.GaussMean.Test

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.AutInhab

theorem lamX_one (I : AutInst) : lamX I (1, 1) = I.L := by
  refine le_antisymm (fun y hy => (I.L_dual y).2 fun z hz => ?_) (GlobalTheory.Count.Test.le_lamX_one I)
  exact ((GlobalTheory.PointLattice.lamX_selfDual I (1, 1)).2.2.2.1 y).1 hy z (GlobalTheory.Count.Test.le_lamX_one I hz)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

end GlobalTheory.GaussMean.Test
end
end

section

noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

variable (D : D7) (large₂ : SizeData₂ D)

def HypZ (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop := StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT ∧ StandingNumericalData D C0 ∧ 1 ≤ C0

def MomIn (C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C : ℝ) : Prop :=
  HypZ D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ A : LocS W, GoodS D lam' A →
      ∀ (a : Fin (D.R.rS + 1)) (q : ℕ), (q : ℝ) ≤ Cq * (D.R.rS : ℝ) ^ 3 →
        ∫⁻ x, ENNReal.ofReal (lA D.R.k D.R.rS W.z (Matrix.of x) a ^ (2 * q)) *
            (‖A.Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂W.νS ≤
          ENNReal.ofReal (large₂.sc.b ^ (2 * C * D.R.m * q)) * l2SG W.νS A.Φ

def SchurSt (C' Cl Cg cb Cu cT CT C0 C1 C : ℝ) : Prop :=
  HypZ D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ A : LocS W, GoodS D (lamD D τ) A →
      ∀ μsec, IsSection D.R.k D.R.rS W.z W.z' μsec →
        MMv D w w' A μsec ≤
          ENNReal.ofReal ((Tr D w * Tr D w') ^ (D.R.k - 1) *
            ((Module.finrank ℂ W.Wp : ℝ) * (Module.finrank ℂ W.Wq : ℝ) * volUn D.R.r * volUn (D.R.k - 1) /
              (A.deg * volUn D.R.k ^ 2 * (2 * D.host.v) ^ (2 * D.R.rS * D.R.k))) *
            large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2))

def ABSr (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  HypZ D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ S : LocS W, GoodS D lam' S →
      ∀ γ p, RelPt D W.z W.z' γ p → ∀ θ', normWin D large₂ C1 θ' → ∀ νR, RMeas D W γ θ' νR →
        DminN W.z W.z' γ D.R.rS ≠ 0 →
          Integrable (fun x => (innerSL ℂ (S.Φ' (Matrix.of x))).smulRight (S.Φ (γ * Matrix.of x))) νR ∧
          ‖S.J νR γ‖ ≤ lossP large₂.sc.b C D.R.m W.z W.z' γ p *
            (C / (D.R.k * D.host.v)) ^ (D.R.rS * (D.R.k - 2 - D.R.rS)) *
            (‖DminN W.z W.z' γ D.R.rS‖ ^ (D.R.k - 2 - D.R.rS))⁻¹

def LocIn (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  HypZ D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w' θ W, HypTT D w w' → GoodW D τ w w' θ W → ∀ A : LocS W, GoodS D (lamD D τ) A →
    MultOne W.z (psiS D W.z) A.σ W.π ∧ MultOne W.z' (psiS D W.z') A.σ W.π' ∧
      Decay A.σ (DD A.σ A.v0) (2 * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 5)

def Big (Cl m₀ : ℝ) : Prop := D.host.rdE ≤ large₂.sc.b ∧ 1 ≤ Cl * D.R.m ∧ m₀ ≤ D.R.m

def BSch (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  HypZ D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w' θ (W : LocW D.R.k D.R.rS), GoodW D τ w w' θ W → ∀ A : LocS W, GoodS D (lamD D τ) A → 0 < Tr D w →
    ∀ v ∈ smoothVecs (k := D.R.k) (r := D.R.rS) A.σ,
      l2SG W.νS (fun g => A.B (A.σ g v)) * (‖A.v0‖₊ : ℝ≥0∞) ^ 2 = l2SG W.νS A.Φ * (‖v‖₊ : ℝ≥0∞) ^ 2

def Sizes (Cl Cg CT : ℝ) : Prop :=
  1 < large₂.sc.L ∧ Real.log large₂.sc.b = large₂.sc.L ∧ Real.exp 1 < large₂.sc.b ∧ D.R.m = 2 * D.R.rS + 2 ∧
    D.R.r = 2 * D.R.rS + D.R.k + 1 ∧ Fintype.card D.what₂.Tau = D.R.f ∧ Cl ≤ D.R.m ∧ D.R.m ^ 4 ≤ D.R.k ∧
    1 ≤ D.host.v ∧ D.host.rdE = 2 * D.host.v ∧ D.host.ka = Real.pi / D.host.v ∧ 2 * D.host.v ≤ large₂.sc.b ∧
    1 ≤ gg D ∧ gg D ≤ large₂.sc.b ^ (2 * Cg) ∧ 8 ≤ Cg ∧ (D.R.k : ℝ) ≤ large₂.sc.b ^ Cg ∧
    (∀ w, Tr D w ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ))) ∧ (∀ w τ, 0 < Formalism.MainNotions.S.vand (uS D w τ) ∧ 0 < Tcrit D w τ) ∧
    ∀ τ (a c : Fin (2 * D.R.rS + D.R.k + 1)), a < c →
      Cl * D.R.k * (D.R.m : ℝ) ^ 4 < lamD D τ a - lamD D τ c

end GlobalTheory.Amp
end
end
