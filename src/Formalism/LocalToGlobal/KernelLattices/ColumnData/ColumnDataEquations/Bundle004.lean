module

public import Formalism.LocalToGlobal.KernelLattices.ColumnData
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.Bundle001
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.Bundle001
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.Bundle002
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseLinkOfNonzeroDelta
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.Bundle003
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Bundle001
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.SelfDualCovolume
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.HenselQuad

@[expose] public section

section

noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J

open Formalism.L2.PairingIndexBounds.Eq.J Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Car}

def rowE (D : Car) (N N' : ℕ) : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] (Fin N' → TaylorLogMetric.VC D N 1) where
  toFun z := fun i τ _ j => z τ i j
  invFun w := fun τ i j => w i τ 0 j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv w := by
    funext i τ a j
    rw [Subsingleton.elim a 0]

def colE (D : Car) (N N' : ℕ) : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] (Fin N → TaylorLogMetric.VC D N' 1) where
  toFun z := fun j τ _ i => z τ i j
  invFun w := fun τ i j => w j τ 0 i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv w := by
    funext i τ a j
    rw [Subsingleton.elim a 0]

theorem form_row (A : ℝ) (N N' : ℕ) (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' x y = ∑ i, Ker.formV A D.what₂.Tau N 1 (rowE D N N' x i) (rowE D N N' y i) := by
  simp only [Ker.formV, LinearMap.mk₂'ₛₗ_apply, rowE, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.univ_unique, Finset.sum_singleton]
  rw [← Finset.sum_div, Finset.sum_comm]

theorem form_col (A : ℝ) (N N' : ℕ) (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' x y = ∑ j, Ker.formV A D.what₂.Tau N' 1 (colE D N N' x j) (colE D N N' y j) := by
  simp only [Ker.formV, LinearMap.mk₂'ₛₗ_apply, colE, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.univ_unique, Finset.sum_singleton]
  rw [← Finset.sum_div]
  congr 1
  symm
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun τ _ => Finset.sum_comm

theorem formV_pos {A : ℝ} (hA : 0 < A) (n : Type) [Fintype n] (N N' : ℕ) : IsPosDef (Ker.formV A n N N') := by
  intro x hx
  have e : (Ker.formV A n N N' x x).re = (∑ τ, ∑ i, ∑ j, Complex.normSq (x τ i j)) / A := by
    simp only [Ker.formV, LinearMap.mk₂'ₛₗ_apply, Complex.mul_conj]
    rw [← Complex.ofReal_re ((∑ τ, ∑ i, ∑ j, Complex.normSq (x τ i j)) / A)]
    push_cast
    rfl
  rw [e]
  refine div_pos ?_ hA
  obtain ⟨τ, i, j, h⟩ : ∃ τ i j, x τ i j ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hx (funext fun τ => funext fun i => funext fun j => hno τ i j)
  calc 0 < Complex.normSq (x τ i j) := Complex.normSq_pos.mpr h
    _ ≤ ∑ j, Complex.normSq (x τ i j) :=
        Finset.single_le_sum (f := fun j => Complex.normSq (x τ i j)) (fun _ _ => Complex.normSq_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i, ∑ j, Complex.normSq (x τ i j) :=
        Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (x τ i j))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
    _ ≤ ∑ τ, ∑ i, ∑ j, Complex.normSq (x τ i j) :=
        Finset.single_le_sum (f := fun τ => ∑ i, ∑ j, Complex.normSq (x τ i j))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
          (Finset.mem_univ τ)

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Cd.Base D cc δ)

include B in
theorem area_pos' : 0 < TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂ := by
  have := B.areaOK
  unfold Cd.Base.AreaOK at this
  show 0 < TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)
  rw [this]
  exact Formalism.L2.Th1.F.areaPos_thm B.L

abbrev La0 (_B : Cd.Base D cc δ) (N N' : ℕ) : AddSubgroup (TaylorLogMetric.VC D N N') :=
  TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')

theorem mem_standardThetaLattice_iff_adelicIdeal (N N' : ℕ) (x : TaylorLogMetric.VC D N N') : x ∈ La0 B N N' ↔ ∀ i j, (fun τ => x τ i j) ∈ B.lamM := by
  have := B.lat0OK N N'
  unfold Cd.Base.Lat0OK at this
  show x ∈ TaylorLogMetric.La D B.tor _ _ ↔ _
  rw [this]
  rfl

theorem lat_row (N N' : ℕ) (x : TaylorLogMetric.VC D N N') : x ∈ La0 B N N' ↔ ∀ i, rowE D N N' x i ∈ La0 B N 1 := by
  simp only [mem_standardThetaLattice_iff_adelicIdeal]
  exact ⟨fun h i _ j => h i j, fun h i j => h i 0 j⟩

theorem lat_col (N N' : ℕ) (x : TaylorLogMetric.VC D N N') : x ∈ La0 B N N' ↔ ∀ j, colE D N N' x j ∈ La0 B N' 1 := by
  simp only [mem_standardThetaLattice_iff_adelicIdeal]
  exact ⟨fun h j _ i => h i j, fun h i j => h j 0 i⟩

theorem neg_one_zpow_sum {ι : Type} (s : Finset ι) (m : ι → ℤ) : (-1 : ℂ) ^ (∑ i ∈ s, m i) = ∏ i ∈ s, (-1 : ℂ) ^ m i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ (by norm_num), ih]

theorem al_prod {ι : Type} [Fintype ι] {N N' M M' : ℕ} (x : TaylorLogMetric.VC D N N') (y : ι → TaylorLogMetric.VC D M M')
    (hf : TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) x x = ∑ i, TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) (y i) (y i))
    (hq : ∀ i, ∃ m : ℤ, Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) (y i) (y i)).re = (m : ℝ)) :
    TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x = ∏ i, TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (y i) := by
  choose m hm using hq
  have h : Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) x x).re = ((∑ i, m i : ℤ) : ℝ) := by
    rw [hf, Complex.re_sum, Finset.mul_sum]
    push_cast
    exact Finset.sum_congr rfl fun i _ => hm i
  unfold TaylorLogMetric.al
  rw [h, round_intCast, neg_one_zpow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hm i, round_intCast]

theorem al_row (hS : B.StdOK) (N N' : ℕ) (x : TaylorLogMetric.VC D N N') (hx : x ∈ La0 B N N') :
    TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x = ∏ i, TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (rowE D N N' x i) :=
  al_prod x _ (form_row _ N N' x x) fun i => B.qInt0 hS N 1 _ ((lat_row B N N' x).1 hx i)

theorem al_col (hS : B.StdOK) (N N' : ℕ) (x : TaylorLogMetric.VC D N N') (hx : x ∈ La0 B N N') :
    TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x = ∏ j, TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (colE D N N' x j) :=
  al_prod x _ (form_col _ N N' x x) fun j => B.qInt0 hS N' 1 _ ((lat_col B N N' x).1 hx j)

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J
end
end

section

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def MuOneL (B : Cd.Base D cc δ) : Prop :=
  ∀ N N' (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Even N → Even N' → SD D L → SD D L₁ →
    ∃ S₂ S₃ : Finset (TaylorLogMetric.VC D N N'),
      IsReps (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N')) S₂ ∧
      IsReps (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L₁ (StandardLatticesGL3.stdL D N')) S₃ ∧
      Formalism.L2.Th1.H.tripleMu
        (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
        (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N'))
        (TaylorLogMetric.La D B.tor L₁ (StandardLatticesGL3.stdL D N')) S₂ S₃ = 1

def MuOneR (B : Cd.Base D cc δ) : Prop :=
  ∀ N N' (L' L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Even N → Even N' → SD D L' → SD D L'' →
    ∃ S₂ S₃ : Finset (TaylorLogMetric.VC D N N'),
      IsReps (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L') S₂ ∧
      IsReps (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L') (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L'') S₃ ∧
      Formalism.L2.Th1.H.tripleMu
        (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
        (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L')
        (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L'') S₂ S₃ = 1

theorem tripleData_of {B : Cd.Base D cc δ} (hL : B.LatAll) {N N' : ℕ}
    {L₁ L₂ L₃ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L₁' L₂' L₃' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (a1 : TaylorLogMetric.admitted D N N' L₁ L₁') (a2 : TaylorLogMetric.admitted D N N' L₂ L₂') (a3 : TaylorLogMetric.admitted D N N' L₃ L₃') :
    TripleData (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor L₁ L₁') (TaylorLogMetric.La D B.tor L₂ L₂') (TaylorLogMetric.La D B.tor L₃ L₃') :=
  { herm := formV_herm' _ _ _ _
    sd₁ := (hL.1 N N' _ _ a1).1
    sd₂ := (hL.1 N N' _ _ a2).1
    sd₃ := (hL.1 N N' _ _ a3).1
    sc₁ := (hL.1 N N' _ _ a1).2
    sc₂ := (hL.1 N N' _ _ a2).2
    sc₃ := (hL.1 N N' _ _ a3).2
    i₁₂ := (hL.2 N N' _ _ _ _ a1 a2).1
    i₂₁ := (hL.2 N N' _ _ _ _ a1 a2).2
    i₁₃ := (hL.2 N N' _ _ _ _ a1 a3).1
    i₃₁ := (hL.2 N N' _ _ _ _ a1 a3).2
    i₂₃ := (hL.2 N N' _ _ _ _ a2 a3).1
    i₃₂ := (hL.2 N N' _ _ _ _ a2 a3).2 }

theorem left_move_triangles_of_unit {B : Cd.Base D cc δ} (hL : B.LatAll) (hM : MuOneL B) : Tr0L D B.tor := by
  intro N N' L L₁ hN hN' hSL hSL1 G hG
  obtain ⟨S₂, S₃, h2, h3, hmu⟩ := hM N N' L L₁ hN hN' hSL hSL1
  have hA0 : TaylorLogMetric.admitted D N N' (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') := ⟨hN, hN', sd0 N, sd0 N'⟩
  have hA1 : TaylorLogMetric.admitted D N N' L (StandardLatticesGL3.stdL D N') := ⟨hN, hN', hSL, sd0 N'⟩
  have hA2 : TaylorLogMetric.admitted D N N' L₁ (StandardLatticesGL3.stdL D N') := ⟨hN, hN', hSL1, sd0 N'⟩
  have hT := tripleData_of hL hA0 hA1 hA2
  funext v
  have h5 := tripleFormula _ _ _ _ _ _ hT S₂ S₃ h2 h3 G hG.2 v
  rw [hmu, one_mul] at h5
  simp only [Cd.Iop_eq]
  exact h5

theorem right_move_triangles_of_unit {B : Cd.Base D cc δ} (hL : B.LatAll) (hM : MuOneR B) : Tr0R D B.tor := by
  intro N N' L' L'' hN hN' hSL hSL1 G hG
  obtain ⟨S₂, S₃, h2, h3, hmu⟩ := hM N N' L' L'' hN hN' hSL hSL1
  have hA0 : TaylorLogMetric.admitted D N N' (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') := ⟨hN, hN', sd0 N, sd0 N'⟩
  have hA1 : TaylorLogMetric.admitted D N N' (StandardLatticesGL3.stdL D N) L' := ⟨hN, hN', sd0 N, hSL⟩
  have hA2 : TaylorLogMetric.admitted D N N' (StandardLatticesGL3.stdL D N) L'' := ⟨hN, hN', sd0 N, hSL1⟩
  have hT := tripleData_of hL hA0 hA1 hA2
  funext v
  have h5 := tripleFormula _ _ _ _ _ _ hT S₂ S₃ h2 h3 G hG.2 v
  rw [hmu, one_mul] at h5
  simp only [Cd.Iop_eq]
  exact h5

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq
end
end

section

noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SquareSplitPairs

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq Formalism.L2.Th1.H

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem good3 {a b c t : ℝ} (h : t = a + b + c) (ha : ∃ k : ℤ, a = 2 * k) (hb : ∃ k : ℤ, b = 2 * k)
    (hc : ∃ k : ℤ, c = 2 * k) : ∃ k : ℤ, t = 2 * k := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  obtain ⟨l, rfl⟩ := hc
  exact ⟨i + j + l, by rw [h]; push_cast; ring⟩

theorem sqSplit_of (B : Cd.Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0)
    (hP : SplitPair D) : Sq.SqSplit B := by
  intro N N' L L₁ L' L'' hN hN' h1 h2 h3 h4
  obtain ⟨n, hn0, hnL, hnL1⟩ := exists_n h1 h2
  obtain ⟨e, heL', heL'', hM⟩ := hP N' L' L'' hN' h3 h4 n hn0
  have hAdm : ∀ i : Bool × Bool, TaylorLogMetric.admitted D N N' (if i.1 then L₁ else L) (if i.2 then L'' else L') := by
    rintro ⟨a, b⟩
    cases a <;> cases b
    · exact admissible_of_integral_conj_le hN hN' h1 h3
    · exact admissible_of_integral_conj_le hN hN' h1 h4
    · exact admissible_of_integral_conj_le hN hN' h2 h3
    · exact admissible_of_integral_conj_le hN hN' h2 h4
  have hq : ∀ i, ∀ z ∈ Sq.sqFam B.tor L L₁ L' L'' i, ∃ m : ℤ, qq D cc δ N N' z = m := fun i z hz =>
    Formalism.L2.Ker.Cd.IntegralLatticeDensity.rational_integrality_link D cc hcc δ hδ B N N' _ _ (hAdm i) z hz
  have hsc : ∀ i, IsSemiChar (HH D cc δ N N') (Sq.sqFam B.tor L L₁ L' L'' i) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) :=
    fun i => ((B.latAll hcc hδ hδ0).1 N N' _ _ (hAdm i)).2
  have hn : ∀ a c : Bool, ∀ u ∈ (if c then L₁ else L), (n : D.host.E) • u ∈ (if a then L₁ else L) := by
    intro a c u hu
    cases a <;> cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] at hu ⊢
    · rw [← osmul]; exact L.smul_mem n hu
    · exact hnL1 u hu
    · exact hnL u hu
    · rw [← osmul]; exact L₁.smul_mem n hu
  have hor : ∀ b : Bool, ∀ y ∈ (if b then L'' else L'), y ∈ L' ∨ y ∈ L'' := by
    intro b y hy
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hy
    · exact Or.inl hy
    · exact Or.inr hy
  have hin : ∀ d : Bool, ∀ m, m ∈ L' → m ∈ L'' → m ∈ (if d then L'' else L') := by
    intro d m hm1 hm2
    cases d <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact hm1
    · exact hm2
  have he : ∀ b : Bool, ∀ y ∈ (if b then L'' else L'), e *ᵥ y ∈ (if b then L'' else L') := by
    intro b y hy
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hy ⊢
    · exact heL' y hy
    · exact heL'' y hy
  have hpres : ∀ i, ∀ z ∈ Sq.sqFam B.tor L L₁ L' L'' i, phi e z ∈ Sq.sqFam B.tor L L₁ L' L'' i := by
    intro i z hz
    exact phi_La (yy_mul fun A hA => homL_mul_pres (he i.2) hA) z hz
  have hMin : ∀ M ∈ ({e * e - e, (letI := D.host.cmStar; eᴴ) * e,
      (letI := D.host.cmStar; (1 - e)ᴴ) * (1 - e)} : Set (Matrix (Fin N') (Fin N') D.host.E)),
      ∀ i j, ∀ z ∈ Sq.sqFam B.tor L L₁ L' L'' i, phi M z ∈ Sq.sqFam B.tor L L₁ L' L'' j := by
    intro M hMs i j z hz
    refine phi_La (yy_mul fun A hA => homL_mul_min hn0 (hn i.1 j.1) ?_ hA) z hz
    intro y hy
    obtain ⟨m, hm1, hm2, hm⟩ := hM M hMs y (hor i.2 y hy)
    exact ⟨m, hin j.2 m hm1 hm2, hm⟩
  have hM1 : e * e - e ∈ ({e * e - e, (letI := D.host.cmStar; eᴴ) * e,
      (letI := D.host.cmStar; (1 - e)ᴴ) * (1 - e)} : Set (Matrix (Fin N') (Fin N') D.host.E)) :=
    Set.mem_insert _ _
  have hM2 : (letI := D.host.cmStar; eᴴ) * e ∈ ({e * e - e, (letI := D.host.cmStar; eᴴ) * e,
      (letI := D.host.cmStar; (1 - e)ᴴ) * (1 - e)} : Set (Matrix (Fin N') (Fin N') D.host.E)) :=
    Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have hM3 : (letI := D.host.cmStar; (1 - e)ᴴ) * (1 - e) ∈ ({e * e - e, (letI := D.host.cmStar; eᴴ) * e,
      (letI := D.host.cmStar; (1 - e)ᴴ) * (1 - e)} : Set (Matrix (Fin N') (Fin N') D.host.E)) :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)

  have hidem : ∀ x : TaylorLogMetric.VC D N N', phi e x - phi e (phi e x) = -(phi (e * e - e) x) := by
    intro x
    rw [phi_sub, phi_mul]
    abel
  have hone : ∀ x : TaylorLogMetric.VC D N N', x - phi e x = phi (1 - e) x := by
    intro x
    rw [phi_sub, phi_one]
  refine ⟨AddSubgroup.comap (AddMonoidHom.id _ - phi e) (⨅ i, Sq.sqFam B.tor L L₁ L' L'' i),
    AddSubgroup.comap (phi e) (⨅ i, Sq.sqFam B.tor L L₁ L' L'' i), ?_⟩
  have hA : ∀ x, x ∈ AddSubgroup.comap (AddMonoidHom.id _ - phi e) (⨅ i, Sq.sqFam B.tor L L₁ L' L'' i) ↔
      ∀ i, x - phi e x ∈ Sq.sqFam B.tor L L₁ L' L'' i := by
    intro x
    simp [AddSubgroup.mem_iInf]
  have hA' : ∀ x, x ∈ AddSubgroup.comap (phi e) (⨅ i, Sq.sqFam B.tor L L₁ L' L'' i) ↔
      ∀ i, phi e x ∈ Sq.sqFam B.tor L L₁ L' L'' i := by
    intro x
    simp [AddSubgroup.mem_iInf]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hx' i
    have := (Sq.sqFam B.tor L L₁ L' L'' i).add_mem ((hA x).1 hx i) ((hA' x).1 hx' i)
    rwa [sub_add_cancel] at this
  · intro i x hx
    refine ⟨phi e x, (hA _).2 fun j => ?_, x - phi e x, (hA' _).2 fun j => ?_, hpres i x hx,
      (Sq.sqFam B.tor L L₁ L' L'' i).sub_mem hx (hpres i x hx), (add_sub_cancel _ _).symm⟩
    · rw [hidem]
      exact (Sq.sqFam B.tor L L₁ L' L'' j).neg_mem (hMin _ hM1 i j x hx)
    · rw [map_sub, hidem]
      exact (Sq.sqFam B.tor L L₁ L' L'' j).neg_mem (hMin _ hM1 i j x hx)
  · intro x y hx hy i j k hxi hyj hxy
    obtain ⟨mx, hmx⟩ := hq i x hxi
    obtain ⟨my, hmy⟩ := hq j y hyj
    obtain ⟨mxy, hmxy⟩ := hq k (x + y) hxy
    refine law_of_good hmx hmy hmxy ?_
    have key : bet D cc δ N N' x y = bet D cc δ N N' (phi e x) (phi e y) +
        bet D cc δ N N' (phi e x) (y - phi e y) + bet D cc δ N N' (x - phi e x) y := by
      have h := bet_add_left (cc := cc) (δ := δ) (phi e x) (x - phi e x) y
      have h' := bet_add_right (cc := cc) (δ := δ) (phi e x) (phi e y) (y - phi e y)
      rw [add_sub_cancel] at h h'
      rw [h, h']
    refine good3 key ?_ ?_ ?_
    · rw [bet_phi]
      exact good_of_lat (hsc i) (hq i) hxi (hMin _ hM2 j i y hyj)
    · exact good_of_lat (hsc i) (hq i) (hpres i x hxi) ((hA y).1 hy i)
    · exact good_of_lat (hsc j) (hq j) ((hA x).1 hx j) hyj
  · intro x y hx hy i j k hxi hyj hxy
    obtain ⟨mx, hmx⟩ := hq i x hxi
    obtain ⟨my, hmy⟩ := hq j y hyj
    obtain ⟨mxy, hmxy⟩ := hq k (x + y) hxy
    refine law_of_good hmx hmy hmxy ?_
    have key : bet D cc δ N N' x y = bet D cc δ N N' (x - phi e x) (y - phi e y) +
        bet D cc δ N N' (x - phi e x) (phi e y) + bet D cc δ N N' (phi e x) y := by
      have h := bet_add_left (cc := cc) (δ := δ) (x - phi e x) (phi e x) y
      have h' := bet_add_right (cc := cc) (δ := δ) (x - phi e x) (y - phi e y) (phi e y)
      rw [sub_add_cancel] at h h'
      rw [h, h']
    refine good3 key ?_ ?_ ?_
    · rw [hone x, hone y, bet_phi]
      exact good_of_lat (hsc i) (hq i) hxi (hMin _ hM3 j i y hyj)
    · exact good_of_lat (hsc i) (hq i) ((Sq.sqFam B.tor L L₁ L' L'' i).sub_mem hxi ((hA' x).1 hx i)) ((hA' y).1 hy i)
    · exact good_of_lat (hsc j) (hq j) ((hA' x).1 hx j) hyj

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SquareSplitPairs
end
end
