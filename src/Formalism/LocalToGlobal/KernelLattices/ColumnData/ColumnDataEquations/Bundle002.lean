module

public import Formalism.LocalToGlobal.KernelLattices.ColumnData
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitTripleEquations.MuOneOfSplit
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.Bundle001
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.Bundle001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle090
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.HenselQuad

@[expose] public section

section

noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H

variable {D : Car}

def gM {n : ℕ} (γ : Matrix (Fin n) (Fin n) D.host.E) (τ : D.what₂.Tau) : Matrix (Fin n) (Fin n) ℂ :=
  γ.map (TaylorLogMetric.embT D τ)

theorem embT_star' (τ : D.what₂.Tau) (x : D.host.E) :
    TaylorLogMetric.embT D τ (letI := D.host.cmStar; star x) = star (TaylorLogMetric.embT D τ x) := by
  rw [Formalism.L2.Ker.Cd.IntegralLatticeDensity.CU.star_conj, Formalism.L2.Ker.Cd.IntegralLatticeDensity.CU.emb_conj]
  rfl

theorem gM_conjTranspose {n : ℕ} (γ : Matrix (Fin n) (Fin n) D.host.E) (τ : D.what₂.Tau) :
    (gM γ τ)ᴴ = gM (letI := D.host.cmStar; star γ) τ := by
  letI := D.host.cmStar
  ext i j
  simp only [gM, conjTranspose_apply, map_apply, star_apply]
  rw [embT_star']

theorem gM_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) D.host.E) (τ : D.what₂.Tau) : gM (A * B) τ = gM A τ * gM B τ := by
  simp [gM, Matrix.map_mul]

theorem gM_one {n : ℕ} (τ : D.what₂.Tau) : gM (1 : Matrix (Fin n) (Fin n) D.host.E) τ = 1 := by
  simp [gM, Matrix.map_one]

theorem gM_unit {n : ℕ} (γ : Matrix (Fin n) (Fin n) D.host.E) (h : (letI := D.host.cmStar; star γ * γ) = 1)
    (τ : D.what₂.Tau) : (gM γ τ)ᴴ * gM γ τ = 1 := by
  rw [gM_conjTranspose, ← gM_mul, h, gM_one]

theorem gM_unit' {n : ℕ} (γ : Matrix (Fin n) (Fin n) D.host.E) (h : (letI := D.host.cmStar; γ * star γ) = 1)
    (τ : D.what₂.Tau) : gM γ τ * (gM γ τ)ᴴ = 1 := by
  rw [gM_conjTranspose, ← gM_mul, h, gM_one]

variable {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)

def phiL (h1 : (letI := D.host.cmStar; star γ * γ) = 1) (h2 : (letI := D.host.cmStar; γ * star γ) = 1)
    (h1' : (letI := D.host.cmStar; star γ' * γ') = 1) (h2' : (letI := D.host.cmStar; γ' * star γ') = 1) :
    TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N' where
  toFun z := fun τ => (gM γ' τ * Matrix.of (z τ) * (gM γ τ)ᴴ : Matrix _ _ ℂ)
  invFun z := fun τ => (Matrix.conjTranspose (γ'.map (TaylorLogMetric.embT D τ)) * (Matrix.of (z τ)) * γ.map (TaylorLogMetric.embT D τ) : Matrix _ _ ℂ)
  map_add' x y := by
    funext τ
    show gM γ' τ * (Matrix.of (x τ) + Matrix.of (y τ)) * (gM γ τ)ᴴ = _
    rw [Matrix.mul_add, Matrix.add_mul]; rfl
  map_smul' c x := by
    funext τ
    show gM γ' τ * (c • Matrix.of (x τ)) * (gM γ τ)ᴴ = c • (gM γ' τ * Matrix.of (x τ) * (gM γ τ)ᴴ)
    rw [Matrix.mul_smul, Matrix.smul_mul]
  left_inv z := by
    funext τ
    show (gM γ' τ)ᴴ * (gM γ' τ * Matrix.of (z τ) * (gM γ τ)ᴴ) * gM γ τ = Matrix.of (z τ)
    rw [Matrix.mul_assoc, Matrix.mul_assoc, gM_unit γ h1, Matrix.mul_one, ← Matrix.mul_assoc, gM_unit γ' h1',
      Matrix.one_mul]
  right_inv z := by
    funext τ
    show gM γ' τ * ((gM γ' τ)ᴴ * Matrix.of (z τ) * gM γ τ) * (gM γ τ)ᴴ = Matrix.of (z τ)
    rw [Matrix.mul_assoc, Matrix.mul_assoc, gM_unit' γ h2, Matrix.mul_one, ← Matrix.mul_assoc, gM_unit' γ' h2',
      Matrix.one_mul]

theorem sum_trace {m n : ℕ} (X Y : Matrix (Fin m) (Fin n) ℂ) :
    ∑ i, ∑ j, X i j * (starRingEnd ℂ) (Y i j) = Matrix.trace (X * Yᴴ) := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem trace_unit {m n : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) (hP : Pᴴ * P = 1)
    (hQ : Q * Qᴴ = 1) (Z W : Matrix (Fin m) (Fin n) ℂ) :
    Matrix.trace (P * Z * Q * (P * W * Q)ᴴ) = Matrix.trace (Z * Wᴴ) := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  have e : P * Z * Q * (Qᴴ * (Wᴴ * Pᴴ)) = P * (Z * Wᴴ) * Pᴴ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q Qᴴ, hQ, Matrix.one_mul]
  rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hP, Matrix.one_mul]

theorem phiL_isom (h1 h2 h1' h2') (A : ℝ) :
    IsIsom (Ker.formV A D.what₂.Tau N N') (Ker.formV A D.what₂.Tau N N')
      ((phiL γ γ' h1 h2 h1' h2' : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N') : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N') := by
  intro x y
  simp only [Ker.formV, LinearMap.mk₂'ₛₗ_apply]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  have e := sum_trace (gM γ' τ * Matrix.of (x τ) * (gM γ τ)ᴴ) (gM γ' τ * Matrix.of (y τ) * (gM γ τ)ᴴ)
  have e2 := sum_trace (Matrix.of (x τ)) (Matrix.of (y τ))
  rw [trace_unit _ _ (gM_unit γ' h1' τ) (by rw [Matrix.conjTranspose_conjTranspose]; exact gM_unit γ h1 τ)] at e
  exact e.trans e2.symm

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq
end
end

section

noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SquareSplitPairs

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

def SplitPair (D : Car) : Prop :=
  ∀ (N' : ℕ) (L' L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Even N' → SD D L' → SD D L'' →
    ∀ n : 𝓞 D.host.E, n ≠ 0 → ∃ e : Matrix (Fin N') (Fin N') D.host.E,
      (∀ y ∈ L', e *ᵥ y ∈ L') ∧ (∀ y ∈ L'', e *ᵥ y ∈ L'') ∧
      ∀ M ∈ ({e * e - e, (letI := D.host.cmStar; eᴴ) * e,
          (letI := D.host.cmStar; (1 - e)ᴴ) * (1 - e)} : Set (Matrix (Fin N') (Fin N') D.host.E)),
        ∀ y, (y ∈ L' ∨ y ∈ L'') → ∃ m, m ∈ L' ∧ m ∈ L'' ∧ M *ᵥ y = (n : D.host.E) • m

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SquareSplitPairs
end
end

section

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SquareSplitPairs

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

variable {D : Car}

theorem mul_smul_mem {N : ℕ} {L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {m k : 𝓞 D.host.E}
    {v : Fin N → D.host.E} (h : (k : D.host.E) • v ∈ L₁) : ((m * k : 𝓞 D.host.E) : D.host.E) • v ∈ L₁ := by
  have e : ((m * k : 𝓞 D.host.E) : D.host.E) • v = m • ((k : D.host.E) • v) := by
    rw [osmul, smul_smul]
    norm_cast
  rw [e]
  exact L₁.smul_mem m h

theorem exists_smul_mem {N : ℕ} {L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (hsp : Submodule.span D.host.E (L₁ : Set (Fin N → D.host.E)) = ⊤) (x : Fin N → D.host.E) :
    ∃ n : 𝓞 D.host.E, n ≠ 0 ∧ (n : D.host.E) • x ∈ L₁ := by
  first | exact UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem .. | (apply UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem <;> assumption) | (intros; apply UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem <;> assumption) | (apply @UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem <;> assumption) | (apply @UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem D N L₁ hsp x | exact @UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem D N L₁ hsp | exact @UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem D N L₁ | exact @UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem D N | exact @UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem D

theorem exists_n_one {N : ℕ} {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (hL : L.FG)
    (hsp : Submodule.span D.host.E (L₁ : Set (Fin N → D.host.E)) = ⊤) :
    ∃ n : 𝓞 D.host.E, n ≠ 0 ∧ ∀ u ∈ L, (n : D.host.E) • u ∈ L₁ := by
  obtain ⟨s, hs⟩ := hL
  choose f hf0 hf using exists_smul_mem hsp
  refine ⟨∏ g ∈ s, f g, Finset.prod_ne_zero_iff.2 fun g _ => hf0 g, ?_⟩
  intro u hu
  rw [← hs] at hu
  induction hu using Submodule.span_induction with
  | mem g hg =>
    rw [← Finset.prod_erase_mul s f hg]
    exact mul_smul_mem (hf g)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact L₁.add_mem hx hy
  | smul c x _ hx =>
    rw [osmul c x, smul_comm, ← osmul]
    exact L₁.smul_mem c hx

theorem exists_n {N : ℕ} {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (hL : SD D L) (hL1 : SD D L₁) :
    ∃ n : 𝓞 D.host.E, n ≠ 0 ∧ (∀ u ∈ L, (n : D.host.E) • u ∈ L₁) ∧ ∀ u ∈ L₁, (n : D.host.E) • u ∈ L := by
  obtain ⟨hfg, hsp, -⟩ := hL
  obtain ⟨hfg1, hsp1, -⟩ := hL1
  obtain ⟨a, ha, h1⟩ := exists_n_one hfg hsp1
  obtain ⟨b, hb, h2⟩ := exists_n_one hfg1 hsp
  refine ⟨b * a, mul_ne_zero hb ha, fun u hu => mul_smul_mem (h1 u hu), fun u hu => ?_⟩
  rw [mul_comm]
  exact mul_smul_mem (h2 u hu)

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SquareSplitPairs
end
end

section

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H

theorem formV_herm' (A : ℝ) (n : Type) [Fintype n] (N N' : ℕ) : IsHerm (Ker.formV A n N N') := by
  intro x y

  simp [Ker.formV, map_sum, mul_comm]

theorem mem_ThSp_of' (D : Car) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (La' : AddSubgroup (TaylorLogMetric.VC D N N'))
    (G : TaylorLogMetric.VC D N N' → ℂ)
    (h : G ∈ Formalism.L2.Th1.H.Th (Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N') (TaylorLogMetric.al D T) La') :
    G ∈ TaylorLogMetric.ThSp D T La' := by
  obtain ⟨ha, hf⟩ := h
  exact ⟨differentiableOn_univ.mp ha.differentiableOn, fun x hx z => hf x hx z⟩

theorem Iop_smul' (D : Car) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (La₁ La₂ : AddSubgroup (TaylorLogMetric.VC D N N'))
    (c : ℂ) (G : TaylorLogMetric.VC D N N' → ℂ) (z : TaylorLogMetric.VC D N N') :
    TaylorLogMetric.Iop D T La₁ La₂ (fun v => c * G v) z = c * TaylorLogMetric.Iop D T La₁ La₂ G z := by
  simp only [TaylorLogMetric.Iop, TaylorLogMetric.U]
  rw [mul_left_comm c, ← smul_eq_mul c (finsum _), smul_finsum]
  congr 1
  refine finsum_congr fun q => ?_
  simp only [smul_eq_mul]
  ring

def SmulSD (D : Car) : Prop :=
  letI := D.host.cmStar
  ∀ N (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (γ : Matrix.unitaryGroup (Fin N) D.host.E),
    SD D L → SD D (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L)

def NormOneUnitIdeal (D : Car) : Prop :=
  letI := D.host.cmStar
  ∀ z : unitary D.host.E, TaylorLogMetric.N1 D (Submodule.span (𝓞 D.host.E) {(z : D.host.E)})

section Paths

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Cd.Base D cc δ)

theorem admissible_of_integral_conj_le {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hN : Even N) (hN' : Even N') (h : SD D L) (h' : SD D L') :
    TaylorLogMetric.admitted D N N' L L' := ⟨hN, hN', h, h'⟩

theorem sd0 (N : ℕ) : SD D (StandardLatticesGL3.stdL D N) := Formalism.L2.Ker.Cd.Inhab.stdL_isSD D N

theorem mvTh (hL : B.LatAll) {N N' : ℕ} {L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (h1 : TaylorLogMetric.admitted D N N' L₁ L₁') (h2 : TaylorLogMetric.admitted D N N' L₂ L₂')
    {G : TaylorLogMetric.VC D N N' → ℂ}
    (hG : G ∈ Formalism.L2.Th1.H.Th (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor L₁ L₁')) :
    TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L₁ L₁') (TaylorLogMetric.La D B.tor L₂ L₂') G ∈
      Formalism.L2.Th1.H.Th (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
        (TaylorLogMetric.La D B.tor L₂ L₂') :=
  Formalism.L2.Th1.H.interTh _ _ (formV_herm' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') _ _ _
    (hL.1 N N' L₂ L₂' h2).2 (hL.2 N N' _ _ _ _ h1 h2).1 _ hG

variable {B}

theorem S1 (hSq : SqP D B.tor) (hL : B.LatAll) {N N' : ℕ} (hN : Even N) (hN' : Even N') (h0 : B.ThZeroMem N N')
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {X : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hLs : SD D L) (hX : SD D X) :
    B.thMoved N N' L X = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) X) (TaylorLogMetric.La D B.tor L X)
      (TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) X)
        (B.thZero N N')) :=
  hSq N N' (StandardLatticesGL3.stdL D N) L (StandardLatticesGL3.stdL D N') X hN hN' (sd0 N) hLs (sd0 N') hX (B.thZero N N')
    (mem_ThSp_of' _ _ _ _ h0)

theorem e1path (hSq : SqP D B.tor) (hR : Tr0R D B.tor) (hL : B.LatAll) {N N' : ℕ} (hN : Even N) (hN' : Even N')
    (h0 : B.ThZeroMem N N') {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hLs : SD D L) (h1 : SD D L') (h2 : SD D L'') :
    B.thMoved N N' L L'' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L L'') (B.thMoved N N' L L') := by
  have hΦ := mvTh B hL (admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N')) (admissible_of_integral_conj_le hN hN' (sd0 N) h1) h0
  rw [S1 hSq hL hN hN' h0 hLs h2, S1 hSq hL hN hN' h0 hLs h1,
    hSq N N' (StandardLatticesGL3.stdL D N) L L' L'' hN hN' (sd0 N) hLs h1 h2 _ (mem_ThSp_of' _ _ _ _ hΦ),
    hR N N' L' L'' hN hN' h1 h2 _ (mem_ThSp_of' _ _ _ _ h0)]

theorem e2path (hSq : SqP D B.tor) (hTL : Tr0L D B.tor) (hL : B.LatAll) {N N' : ℕ} (hN : Even N) (hN' : Even N')
    (h0 : B.ThZeroMem N N') {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hLs : SD D L) (hL1 : SD D L₁) (h1 : SD D L') :
    B.thMoved N N' L₁ L' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L₁ L') (B.thMoved N N' L L') := by
  have hθ : B.thZero N N' ∈ TaylorLogMetric.Th D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') :=
    mem_ThSp_of' D B.tor _ _ h0
  have hH : B.thHalf N N' L ∈ TaylorLogMetric.Th D B.tor L (StandardLatticesGL3.stdL D N') :=
    mem_ThSp_of' D B.tor _ _ (mvTh B hL (admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N'))
      (admissible_of_integral_conj_le hN hN' hLs (sd0 N')) (G := B.thZero N N') h0)
  have e : B.thHalf N N' L₁ = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N'))
      (TaylorLogMetric.La D B.tor L₁ (StandardLatticesGL3.stdL D N')) (B.thHalf N N' L) :=
    (hTL N N' L L₁ hN hN' hLs hL1 _ hθ).symm
  show TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L₁ (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L₁ L') (B.thHalf N N' L₁) =
    TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L₁ L')
      (TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L L') (B.thHalf N N' L))
  rw [e]
  exact hSq N N' L L₁ (StandardLatticesGL3.stdL D N') L' hN hN' hLs hL1 (sd0 N') h1 _ hH

end Paths

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq
end
end

section

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.Sq

open Formalism.L2.PairingIndexBounds.Eq.Sq Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

section Gen

variable {V : Type} [AddCommGroup V] [Module ℂ V]

structure PolFam (H : Sesq V) (α : V → ℂ) {ι : Type} (Y : ι → AddSubgroup V) (A A' : AddSubgroup V) : Prop where
  meet : ∀ x, x ∈ A → x ∈ A' → ∀ i, x ∈ Y i
  dec : ∀ i, ∀ x ∈ Y i, ∃ a ∈ A, ∃ b ∈ A', a ∈ Y i ∧ b ∈ Y i ∧ x = a + b
  semiA : ∀ x y, x ∈ A → y ∈ A → ∀ i j k, x ∈ Y i → y ∈ Y j → x + y ∈ Y k →
    α (x + y) = α x * α y * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ))
  semiA' : ∀ x y, x ∈ A' → y ∈ A' → ∀ i j k, x ∈ Y i → y ∈ Y j → x + y ∈ Y k →
    α (x + y) = α x * α y * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ))

theorem psiT_one {H : Sesq V} {α : V → ℂ} {Λ₂ Λ₃ : AddSubgroup V} (h2 : IsSemiChar H Λ₂ α) (h3 : IsSemiChar H Λ₃ α)
    {z y : V} (hz : z ∈ Λ₃) (hy : y ∈ Λ₂)
    (hlaw : α (z + y) = α z * α y * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H z y : ℂ))) :
    psiT H α z y = 1 := by
  have hz2 : α z * α z = 1 := by rcases h3.1 z hz with h | h <;> rw [h] <;> norm_num
  have hy2 : α y * α y = 1 := by rcases h2.1 y hy with h | h <;> rw [h] <;> norm_num
  have he : Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H z y : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H z y : ℂ)) = 1 := by
    rw [← Complex.exp_add, show (Real.pi : ℂ) * Complex.I * (altE H z y : ℂ) +
      -(Real.pi : ℂ) * Complex.I * (altE H z y : ℂ) = 0 by ring, Complex.exp_zero]
  unfold psiT
  rw [hlaw]
  calc _ = (α z * α z) * (α y * α y) * (Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H z y : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H z y : ℂ))) := by ring
    _ = 1 := by rw [hz2, hy2, he]; ring

theorem splitTri_of {H : Sesq V} {α : V → ℂ} {ι : Type} {Y : ι → AddSubgroup V} {A A' : AddSubgroup V}
    (hP : PolFam H α Y A A') (i₁ i₂ i₃ : ι) (hT : TripleData H α (Y i₁) (Y i₂) (Y i₃)) :
    SplitTri H α (Y i₁) (Y i₂) (Y i₃) A A' :=
  { meet := fun x h h' => ⟨hP.meet x h h' i₁, hP.meet x h h' i₂, hP.meet x h h' i₃⟩
    dec₁ := hP.dec i₁
    dec₂ := hP.dec i₂
    dec₃ := hP.dec i₃
    isoA := fun z y hz hy hz3 hy2 h1 =>
      psiT_one hT.sc₂ hT.sc₃ hz3 hy2 (hP.semiA z y hz hy i₃ i₂ i₁ hz3 hy2 h1)
    isoA' := fun z y hz hy hz3 hy2 h1 =>
      psiT_one hT.sc₂ hT.sc₃ hz3 hy2 (hP.semiA' z y hz hy i₃ i₂ i₁ hz3 hy2 h1) }

end Gen

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def sqFam (T : TaylorLogMetric.Tor D) {N N' : ℕ} (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : Bool × Bool → AddSubgroup (TaylorLogMetric.VC D N N') :=
  fun p => TaylorLogMetric.La D T (if p.1 then L₁ else L) (if p.2 then L'' else L')

def SqSplit (B : Cd.Base D cc δ) : Prop :=
  ∀ N N' (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    Even N → Even N' → SD D L → SD D L₁ → SD D L' → SD D L'' →
    ∃ A A' : AddSubgroup (TaylorLogMetric.VC D N N'),
      PolFam (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor) (sqFam B.tor L L₁ L' L'') A A'

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.Sq
end
end
