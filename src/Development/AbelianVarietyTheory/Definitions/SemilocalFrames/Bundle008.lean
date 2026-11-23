module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Formalism.LocalRingCardinality.Bundle001
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle004

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.FlagMeas

open Formalism.MainNotions.S GlobalTheory.Count

def sphV (i : ℕ) : ℝ := ∏ l ∈ Finset.Icc 1 i, 2 * Real.pi ^ l / ((l - 1).factorial : ℝ)

def volU (i : ℕ) : ℝ := sphV i * 2 ^ (i * (i - 1) / 2)

def dimN (n : ℕ) {a : ℕ} (j : Fin a → ℕ) : ℕ :=
  4 * (∑ i, ∑ k ∈ univ.filter (fun k => i < k), j i * j k) + 2 * (∑ i, j i) * (n - 2 * ∑ i, j i) + ∑ i, j i ^ 2

def zetaE (E : Type) [Field E] [NumberField E] (l : ℕ) : ℝ := (dedekindZeta E (l : ℂ)).re

def kapBd (E : Type) [Field E] [NumberField E] [StarRing E] (p q : ℕ) {a : ℕ} (j : Fin a → ℕ) : ℝ :=
  Formalism.HermitianLatticesTheory.vInv E ^ (-((Formalism.HermitianLatticesTheory.fDeg E : ℝ) * dimN (p + q) j / 2)) *
    (2 : ℝ) ^ (-((Formalism.HermitianLatticesTheory.fDeg E : ℝ) *
      (((p + q : ℕ) : ℝ) * (∑ i, j i : ℕ) - ((∑ i, j i : ℕ) : ℝ) ^ 2 + ((∑ i, j i : ℕ) : ℝ) / 2))) *
    (sphV p * sphV q / (sphV (p - ∑ i, j i) * sphV (q - ∑ i, j i) * ∏ i, sphV (j i))) ^ Formalism.HermitianLatticesTheory.fDeg E *
    dedekindZeta_residue E ^ a * (∏ i, ∏ l ∈ Finset.Icc 2 (j i), zetaE E l) /
    ∏ M ∈ Finset.Ioc (p + q - 2 * ∑ i, j i) (p + q), Formalism.HermitianLatticesTheory.lValEta E M

def simplexH (a : ℕ) : Set (Fin a → ℝ) := {τ | StrictMono τ ∧ ∀ i, 0 < τ i ∧ τ i < 1 / 2}

def dens (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (τ : Fin a → ℝ) : ℝ :=
  layerProd n f j τ id * ∏ i, 2 * (f : ℝ) * j i / τ i

def typeSet (I : AutInst) {a : ℕ} (j : Fin a → ℕ) (B : Set (Fin a → ℝ)) : Set I.GA :=
  {x | ∃ τ ∈ B, HasType I x j τ}

def covol {G : Type} [Mul G] [MeasurableSpace G] (Γ : Set G) (μ : Measure G) (A : Set G) : ENNReal :=
  ⨅ (D : Set G) (_ : MeasurableSet D) (_ : ∀ x ∈ A, ∃ γ ∈ Γ, γ * x ∈ D), μ D

def gaugeVol (I : AutInst) (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] : ENNReal :=
  ENNReal.ofReal (∏ v, c v) * covol I.GFset (I.muA μf) Set.univ / μf I.Kset

def SameField (I I' : AutInst) : Prop := ∃ e : I'.E ≃+* I.E, ∀ x, e (star x) = star (e x)

def HasSig (I : AutInst) (p q : ℕ) : Prop := ∀ v, I.pAt v = p ∧ I.qAt v = q

section Real

variable {n : ℕ} {ε : Fin n → Bool}

def IsGaugeSub (S : Set (Formalism.REAL.UJ ε)) (d : ℕ) (μ : Measure (Formalism.REAL.UJ ε)) : Prop :=
  μ Sᶜ = 0 ∧ (∀ s ∈ S, μ.map (fun g => s * g) = μ) ∧
    Filter.Tendsto
      (fun r : ℝ => μ {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} / ENNReal.ofReal (r ^ d))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)))

def IsIsoFlag (ε : Fin n → Bool) {a : ℕ} (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) : Prop :=
  W 0 = ⊥ ∧ Monotone W ∧
    (∀ i : Fin a, Module.finrank ℂ (W i.succ) = Module.finrank ℂ (W i.castSucc) + j i) ∧
    ∀ x ∈ W (Fin.last a), ∀ y ∈ W (Fin.last a), star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0

def flagN (ε : Fin n → Bool) {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) : Set (Formalism.REAL.UJ ε) :=
  {g | (∀ i : Fin a, ∀ y ∈ W i.succ, uMat g *ᵥ y - y ∈ W i.castSucc) ∧
    ∀ y : Fin n → ℂ, (∀ x ∈ W (Fin.last a), star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0) →
      uMat g *ᵥ y - y ∈ W (Fin.last a)}

def flagM (ε : Fin n → Bool) {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) : Set (Formalism.REAL.UJ ε) :=
  {g | ∀ i, ∀ y ∈ W i, uMat g *ᵥ y ∈ W i ∧ (uMat g)ᴴ *ᵥ y ∈ W i}

def maxK (ε : Fin n → Bool) : Set (Formalism.REAL.UJ ε) := {g | (uMat g)ᴴ * uMat g = 1}


open Classical in
def detOn (g : Matrix (Fin n) (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) : ℝ :=
  if h : ∀ y ∈ W, Matrix.toLin' g y ∈ W then ‖LinearMap.det ((Matrix.toLin' g).restrict h)‖ else 0

def locSize {a : ℕ} (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ))
    (g : Matrix (Fin n) (Fin n) ℂ) (i : Fin a) : ℝ :=
  (detOn g (W i.succ) / detOn g (W i.castSucc)) ^ (-(1 : ℝ) / j i)

end Real

section GenLin

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

def MatInf : Type := InfinitePlace E → Fin j → Fin j → ℂ

instance : MeasurableSpace (MatInf E j) := inferInstanceAs (MeasurableSpace (InfinitePlace E → Fin j → Fin j → ℂ))

instance : Mul (MatInf E j) := ⟨fun x y w a b => (Matrix.of (x w) * Matrix.of (y w)) a b⟩

def detNorm (x : MatInf E j) : ℝ := ∏ w, ‖(Matrix.of (x w)).det‖ ^ 2

def haarGL : Measure (MatInf E j) :=
  Measure.withDensity (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ))
    fun x => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j)

def autGL (Λ : Submodule (𝓞 E) (Fin j → E)) : Set (MatInf E j) :=
  {x | ∃ γ : GL (Fin j) E, (∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ ↔ y ∈ Λ) ∧
    ∀ w a b, x w a b = w.embedding ((γ : Matrix (Fin j) (Fin j) E) a b)}

def glVol : ENNReal :=
  ∑' c : Quot (fun Λ Λ' : {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsFullLattice E Λ} =>
      ∃ γ : GL (Fin j) E, ∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ'.1 ↔ y ∈ Λ.1),
    covol (autGL E j (Quot.out c).1) (haarGL E j) {x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1}

end GenLin

def defClassNum (E : Type) [Field E] [NumberField E] [StarRing E] (r : ℕ) : ENat :=
  ENat.card (Quot (fun X Y : {X : Matrix (Fin r) (Fin r) E × Submodule (𝓞 E) (Fin r → E) //
      X.1ᴴ = X.1 ∧ (∀ (φ : E →+* ℂ) (y : Fin r → E), y ≠ 0 → 0 < (φ (star y ⬝ᵥ (X.1 *ᵥ y))).re) ∧
      Submodule.IsLattice E X.2 ∧
      ∀ x, x ∈ X.2 ↔ ∀ y ∈ X.2, star y ⬝ᵥ (X.1 *ᵥ x) ∈ (algebraMap (𝓞 E) E).range} =>
    ∃ γ : GL (Fin r) E, (γ : Matrix (Fin r) (Fin r) E)ᴴ * Y.1.1 * (γ : Matrix (Fin r) (Fin r) E) = X.1.1 ∧
      ∀ y, (γ : Matrix (Fin r) (Fin r) E) *ᵥ y ∈ Y.1.2 ↔ y ∈ X.1.2))

end GlobalTheory.FlagMeas
end
end

section

noncomputable section

namespace GlobalTheory.SA

open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat

def ofHSpace {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) : HermSpace E S.V where
  B := S.hT.flip
  herm x y := S.herm.eq y x
  nondeg x h := S.nondeg.2 x h

variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] {H : HermSpace K V} {r : ℕ}

def xPlus (F : FlagD H r) : Submodule K V := F.X ⊔ Submodule.span K {F.z}

abbrev latX (F : FlagD H r) (Λ : Submodule R V) : Submodule R V := Λ ⊓ rs R F.X

def IsComp (F F' : FlagD H r) (u : V) (a a' : K) : Prop := u - a • F.z - a' • F'.z ∈ F.X ⊔ F'.X

def redLat (F : FlagD H r) (Λ : Submodule R V) : Submodule R V := (Λ ⊓ rs R (perp H F.X)) ⊔ rs R F.X

def IsPairMap (F F' F'' : FlagD H r) (Λ : Submodule R V) (g : R) (β : V ≃ₗ[K] V) : Prop :=
  F'.X.map (β : V →ₗ[K] V) = F''.X ∧ (perp H F'.X).map (β : V →ₗ[K] V) = perp H F''.X ∧
  (∀ x ∈ perp H F'.X, ∀ y ∈ perp H F'.X, H.B (β x) (β y) = H.B x y) ∧
  imLat β (redLat F' Λ) = redLat F'' Λ ∧ β F'.z - F''.z ∈ F''.X ∧
  ∀ l' ∈ Λ ⊓ rs R (perp H F'.X), ∀ l'' ∈ Λ ⊓ rs R (perp H F''.X), β l' - l'' ∈ F''.X →
    l'' - l' ∈ latX F Λ ⊔ smulLat g Λ

def fixSp (F F' F'' : FlagD H r) (β : V ≃ₗ[K] V) : Submodule K V where
  carrier := {x | x ∈ wSp F F' ∧ ∃ x'' ∈ wSp F F'', x - x'' ∈ F.X ∧ β x - x'' ∈ F''.X}
  zero_mem' := ⟨zero_mem _, 0, zero_mem _, by simp, by simp⟩
  add_mem' := by
    rintro x y ⟨hx, a, ha, h1, h2⟩ ⟨hy, b, hb, h3, h4⟩
    refine ⟨add_mem hx hy, a + b, add_mem ha hb, ?_, ?_⟩
    · rw [add_sub_add_comm]; exact add_mem h1 h3
    · rw [map_add (f := _), add_sub_add_comm]; exact add_mem h2 h4
  smul_mem' := by
    rintro c x ⟨hx, a, ha, h1, h2⟩
    refine ⟨Submodule.smul_mem _ c hx, c • a, Submodule.smul_mem _ c ha, ?_, ?_⟩
    · rw [← smul_sub]; exact Submodule.smul_mem _ c h1
    · rw [map_smul, ← smul_sub]; exact Submodule.smul_mem _ c h2

theorem perp_anti {S S' : Submodule K V} (h : S ≤ S') : perp H S' ≤ perp H S := fun y hy =>
  (mem_perp_iff H S y).2 fun x hx => (mem_perp_iff H S' y).1 hy x (h hx)

theorem perp_sup (S S' : Submodule K V) : perp H (S ⊔ S') = perp H S ⊓ perp H S' := by
  refine le_antisymm (le_inf (perp_anti le_sup_left) (perp_anti le_sup_right)) fun y hy => ?_
  refine (mem_perp_iff H _ y).2 fun x hx => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add (f := _), (mem_perp_iff H _ y).1 hy.1 a ha, (mem_perp_iff H _ y).1 hy.2 b hb, add_zero]

theorem mem_perp_span (s : Set V) (y : V) :
    y ∈ perp H (Submodule.span K s) ↔ ∀ x ∈ s, H.B y x = 0 := by
  rw [mem_perp_iff]
  refine ⟨fun h x hx => h x (Submodule.subset_span hx), fun h x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add a b _ _ ha hb => rw [map_add (f := _), ha, hb, add_zero]
  | smul c a _ ha => rw [LinearMap.map_smulₛₗ, ha, smul_zero]

theorem X_eq_span (F : FlagD H r) :
    F.X = Submodule.span K (Set.range fun a : Fin r => F.e a.castSucc) := by
  rw [FlagD.X, FlagD.Xa, ← Set.image_univ]
  congr 2
  ext b
  simp

theorem xPlus_eq_span (F : FlagD H r) : xPlus F = Submodule.span K (Set.range F.e) := by
  rw [xPlus, X_eq_span, ← Submodule.span_union]
  congr 1
  ext v
  simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff, Fin.exists_fin_succ', FlagD.z, eq_comm]

theorem mem_perp_xPlus (F : FlagD H r) (y : V) :
    y ∈ perp H (xPlus F) ↔ y ∈ perp H F.X ∧ H.B y F.z = 0 := by
  rw [xPlus, perp_sup, Submodule.mem_inf, mem_perp_span]
  simp



theorem xPlus_sup (F F' : FlagD H r) : xPlus F ⊔ xPlus F' = V0 F F' := by
  rw [xPlus, xPlus, V0, Submodule.span_insert, sup_sup_sup_comm]

theorem wSp_eq (F F' : FlagD H r) : wSp F F' = perp H (xPlus F) ⊓ perp H (xPlus F') := by
  rw [wSp, ← xPlus_sup, perp_sup]

section Pair

variable {F F' F'' : FlagD H r} {Λ : Submodule R V} {g : R} {β : V ≃ₗ[K] V}

end Pair

namespace FlagExample

open NumberField Formalism.BasicNotions.Examples₂

variable (E : Type) [Field E] [NumberField E] [StarRing E]

variable {m s : ℤ} (h1 : m * m = m) (h2 : s * s = m)

end FlagExample

end GlobalTheory.SA

end
end
