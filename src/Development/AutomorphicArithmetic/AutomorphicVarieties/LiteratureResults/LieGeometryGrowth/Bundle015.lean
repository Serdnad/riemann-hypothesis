module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsAppSz
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsChartSz
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

section

open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Geo.Cs UpperTheory.V.Lit.Dr
open scoped ContDiff

private theorem tp_contDiffOn {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] {Y : Set V} (hY : IsOpen Y) (A : V →L[ℝ] V) (B : F →L[ℝ] F)
    (hA : ∀ p ∈ Y, A p ∈ Y) {q : ℕ} {w : V → V [⋀^Fin q]→L[ℝ] F} (hw : ContDiffOn ℝ ∞ w Y) :
    ContDiffOn ℝ ∞ (tp A B w) Y := by
  intro z hz
  apply ContDiffAt.contDiffWithinAt
  refine altSmooth _ _ _ q _ z fun v => ?_
  have h1 : ContDiffAt ℝ ∞ (fun y : V => w (A y)) z :=
    (hw.contDiffAt (hY.mem_nhds (hA z hz))).comp z A.contDiff.contDiffAt
  have h2 : ContDiffAt ℝ ∞ (fun y : V => w (A y) fun i => A (v i)) z :=
    (ContinuousAlternatingMap.apply ℝ V F (fun i => A (v i))).contDiff.contDiffAt.comp z h1
  exact B.contDiff.contDiffAt.comp z h2

private theorem twOps_abs {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] {Y : Set V} (hY : IsOpen Y) (A A' : V →L[ℝ] V) (B : F →L[ℝ] F)
    (hA : ∀ p ∈ Y, A p ∈ Y) (hA' : ∀ p ∈ Y, A' p ∈ Y) (h1 : ∀ p, A (A' p) = p) (h2 : ∀ p, A' (A p) = p)
    {W : V → V} (hW : IsField Y W) :
    IsField Y (fun p => A' (W (A p))) ∧ (∀ t p, flow (fun p => A' (W (A p))) t p = A' (flow W t (A p))) ∧
    ∀ q : ℕ, (∀ w : V → V [⋀^Fin q]→L[ℝ] F, ∀ p ∈ Y,
        tp A B (pb (flow W 1) w) p = pb (flow (fun p => A' (W (A p))) 1) (tp A B w) p) ∧
      ∀ w : V → V [⋀^Fin (q + 1)]→L[ℝ] F, ContDiffOn ℝ ∞ w Y → ∀ p ∈ Y,
        tp A B (hom W w) p = hom (fun p => A' (W (A p))) (tp A B w) p := by
  have hf : ∀ t p, flow (fun p => A' (W (A p))) t p = A' (flow W t (A p)) := fun t p => by
    simp only [flow, map_add (f := _), map_smul, h2]
  have hZ : IsField Y (fun p => A' (W (A p))) :=
    ⟨A'.contDiff.comp_contDiffOn (hW.1.comp A.contDiff.contDiffOn hA), fun p hp t ht => by
      rw [hf]; exact hA' _ (hW.2 _ (hA p hp) t ht)⟩
  refine ⟨hZ, hf, fun q => ?_⟩
  have nat := pbNat V F Y hY A' B W _ hW hZ hA' (fun p _ => by simp only [h1]) q
  have rel : ∀ (n : ℕ) (w : V → V [⋀^Fin n]→L[ℝ] F), ∀ p ∈ Y, ∀ v : Fin n → V,
      tp A B w (A' p) (fun i => A' (v i)) = B (w p v) := fun n w p _ v => by
    simp only [tp_apply, h1]
  refine ⟨fun w p hp => ?_, fun w hw p hp => ?_⟩
  · refine ContinuousAlternatingMap.ext fun v => ?_
    have := nat.1 _ _ (rel q w) 1 ⟨zero_le_one, le_rfl⟩ _ (hA p hp) (fun i => A (v i))
    simp only [h2] at this
    exact this.symm
  · refine ContinuousAlternatingMap.ext fun v => ?_
    have := (nat.2 _ _ (rel (q + 1) w)).2 hw (tp_contDiffOn hY A B hA hw) _ (hA p hp) (fun i => A (v i))
    simp only [h2] at this
    exact this.symm

theorem UpperTheory.V.Lit.Geo.Cs.twOps :
    UpperTheory.V.Lit.Geo.Cs.TwOps := by
  intro E _ _ _ a ho U Ξ W hW g x
  have h1 : ∀ p : HV E a, sand g (sand g⁻¹ p) = p := fun p => by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  have h2 : ∀ p : HV E a, sand g⁻¹ (sand g p) = p := fun p => by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  obtain ⟨k1, k2, k3⟩ := twOps_abs ho (sand g) (sand g⁻¹) (mulVecL (Ξ.mat g⁻¹)) (fun p hp => sand_mem_cone g hp)
    (fun p hp => sand_mem_cone g⁻¹ hp) h1 h2 (hW.field (QuotientGroup.mk x))
  refine ⟨k1, k2, fun q => ?_⟩
  have app := omApply _ _ _ _ (geo ho U Ξ) W hW q
  refine ⟨fun w => ⟨tp_contDiffOn ho _ _ (fun p hp => sand_mem_cone g hp) (w.2 _).1, fun p hp => ?_⟩, fun w p hp => ?_⟩
  · refine Eq.trans ?_ ((k3 q).1 (w.1 _) p hp)
    refine ContinuousAlternatingMap.ext fun v => ?_
    rw [Tw, tp_apply, tp_apply, app.1 w _ _ (sand_mem_cone g hp)]
  · refine Eq.trans ?_ ((k3 q).2 (w.1 _) (w.2 _).1 p hp)
    refine ContinuousAlternatingMap.ext fun v => ?_
    rw [Tw, tp_apply, tp_apply, app.2 w _ _ (sand_mem_cone g hp)]
end

section

open UpperTheory.V.Lit.Geo

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct ContDiff Topology

namespace UpperTheory.V.Lit.Geo.Cs

private theorem term_sz {V W F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (k : ℕ) (τ : V → W) (Θ : V → F) (p : V)
    (hτ : ContDiffAt ℝ ∞ τ p) (hΘ : ContDiffAt ℝ ∞ Θ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : W → ℂ) (b : ℝ), ContDiffAt ℝ ∞ u (τ p) → Sz k u (τ p) b →
      Sz k (fun y => u (τ y) • Θ y) p (C * b) := by
  obtain ⟨c, hc⟩ := exists_sz k τ p
  obtain ⟨t, ht⟩ := exists_sz k Θ p
  obtain ⟨C, hC, H⟩ := compSz V W ℂ k c
  let L : ℂ →L[ℝ] F →L[ℝ] F := ContinuousLinearMap.lsmul ℝ ℂ
  refine ⟨2 ^ k * (‖L‖ * C) * t, by have := ht.nonneg; positivity, fun u b hu hb => ?_⟩
  have h1 := H u τ p b hτ hu (fun i _ hi => hc i hi) hb
  have s1 : ContDiffAt ℝ ∞ (fun y => u (τ y)) p := hu.comp p hτ
  have h2 := (appSz V ℂ (F →L[ℝ] F) k p).2.1 L _ _ s1 h1
  have s2 : ContDiffAt ℝ ∞ (fun y => L (u (τ y))) p := L.contDiff.contDiffAt.comp p s1
  have h3 := (appSz V F F k p).1 _ Θ _ _ s2 hΘ h2 ht
  exact h3.mono (le_of_eq (by ring))

private theorem val_sz (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (q : ℕ) (α : Co Ξ q) (w : Fm U Ξ q) (hw : Corr U Ξ α w) (ρ : GA E a → ℝ) (hρ : ∀ g, 0 ≤ ρ g)
    (hb : ∀ (X : Fin q → Herm E a) (j : Fin Ξ.d) (l : List (Lie E a)), ∃ M : ℝ, ∀ g,
      ‖((l.map (lie E a)).prod (Bor.cmp j (α X))).1 g‖ ≤ M * ρ g) (k : ℕ) (v : Fin q → HV E a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ g x, ContDiffAt ℝ ∞ (fun p => Tw U Ξ w g x p v) (hOne E a) ∧
      Sz k (fun p => Tw U Ξ w g x p v) (hOne E a) (M * ρ (pt g x)) := by
  obtain ⟨ι, _, X, j, Θ, τ, h1, hτ, hΘ, H⟩ := corrForm E a Ξ q v
  choose C hC HC using fun i => term_sz k τ (Θ i) (hOne E a) hτ (hΘ i)
  choose D hD HD using fun i => chartSz E a k ρ hρ (Bor.cmp (j i) (α (X i))) (hb (X i) (j i))
  refine ⟨∑ i, C i * D i, Finset.sum_nonneg fun i _ => mul_nonneg (hC i) (hD i), fun g x => ?_⟩
  have e := H U α w hw g x
  have su : ∀ i, ContDiffAt ℝ ∞ (chart (Bor.cmp (j i) (α (X i))).1 (pt g x)) (τ (hOne E a)) := fun i => by
    rw [h1]; exact contDiffAt_chart (Bor.cmp (j i) (α (X i))).2 _ isUnit_one
  have st : ∀ i, ContDiffAt ℝ ∞ (fun p => chart (Bor.cmp (j i) (α (X i))).1 (pt g x) (τ p) • Θ i p) (hOne E a) :=
    fun i => ((su i).comp _ hτ).smul (hΘ i)
  refine ⟨(ContDiffAt.sum fun i _ => st i).congr_of_eventuallyEq e, ?_⟩
  have := (appSz (HV E a) ℝ (Fin Ξ.d → ℂ) k (hOne E a)).2.2 ι Finset.univ _ _ (fun i _ => st i)
    (fun i _ => HC i _ (D i * ρ (pt g x)) (su i) (by rw [h1]; exact HD i _))
  refine (this.congr e.symm).mono (le_of_eq ?_)
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

end UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.corrSz :
    UpperTheory.V.Lit.Geo.Cs.CorrSz := by
  intro E _ _ _ a U Ξ q α w hw ρ hρ hb k
  obtain ⟨T, C, hC, H⟩ := Cs.altEv (HV E a) (Fin Ξ.d → ℂ) q k
  choose M hM HM using Cs.val_sz E a U Ξ q α w hw ρ hρ hb k
  have h0 : 0 ≤ ∑ v ∈ T, M v := Finset.sum_nonneg fun v _ => hM v
  refine ⟨C * ∑ v ∈ T, M v, mul_nonneg hC h0, fun g x => ?_⟩
  rw [mul_assoc]
  exact H _ _ _ (mul_nonneg h0 (hρ _)) (fun v _ => (HM v g x).1) fun v hv => (HM v g x).2.mono
    (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun v _ => hM v) hv) (hρ _))
end

section

open UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.homSz :
    HomSz := by
  intro V F _ _ _ _ _ _ q k c
  obtain ⟨C, hC, h⟩ := hkSz V F q k c
  refine ⟨C, hC, fun Y W w b hY hW hw p hp hc hb => ?_⟩
  obtain ⟨ho, hs, -, -⟩ := UpperTheory.V.Lit.Geo.hkSmooth V F Y hY W hW q w hw
  haveI : CompleteSpace F := FiniteDimensional.complete ℝ F
  refine intSz V (V [⋀^Fin q]→L[ℝ] F) k p _ (fun z : V × ℝ => UpperTheory.V.Lit.Geo.hk W z.2 w z.1) (C * b) ho
    (fun t ht => ⟨hp, hW.2 p hp t ht⟩) hs fun t ht => ?_
  exact h W t w p b (abs_le.2 ⟨by linarith [ht.1], ht.2⟩) (hW.1.contDiffAt (hY.mem_nhds hp)) hc
    (hw.contDiffAt (hY.mem_nhds (hW.2 p hp t ht))) (hb t ht)
end

section

open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Lit.Dr
open scoped ContDiff

private theorem tp_smooth {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : V →L[ℝ] V) (B : F →L[ℝ] F) {q : ℕ} (w : V → V [⋀^Fin q]→L[ℝ] F) (p : V) (hw : ContDiffAt ℝ ∞ w (A p)) :
    ContDiffAt ℝ ∞ (Cs.tp A B w) p := by
  have h1 : ContDiffAt ℝ ∞ (fun x => w (A x)) p := hw.comp p A.contDiff.contDiffAt
  have h2 := (ContinuousAlternatingMap.compContinuousLinearMapCLM A :
      (V [⋀^Fin q]→L[ℝ] F) →L[ℝ] (V [⋀^Fin q]→L[ℝ] F)).contDiff.contDiffAt.comp p h1
  exact (ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ V F F (Fin q) B).contDiff.contDiffAt.comp p h2

theorem UpperTheory.V.Lit.Geo.Cs.move :
    UpperTheory.V.Lit.Geo.Cs.Move := by
  intro E _ _ _ a ho U Ξ q k c
  obtain ⟨B, hB, hb⟩ := matBd E a Ξ c
  obtain ⟨D, hD, hd⟩ := Cs.tpSz (HV E a) (Fin Ξ.d → ℂ) q k B
  refine ⟨D, hD, fun w g x h b hh hs => ?_⟩
  obtain ⟨h1, -, h3⟩ := hb h hh.1 hh.2
  have e : sand h⁻¹ (sand h (hOne E a)) = hOne E a := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one, ContinuousLinearMap.one_apply]
  rw [Cs.Tw_eq U Ξ w.1 g h x]
  refine hd _ _ _ _ b (ContinuousLinearMap.opNorm_le_bound _ hB h3)
    (ContinuousLinearMap.opNorm_le_bound _ hB fun y => by rw [mulVecL_apply]; exact h1 y) ?_ (by rw [e]; exact hs)
  rw [e]
  exact tp_smooth _ _ _ _ ((w.2 _).1.contDiffAt (ho.mem_nhds (sand_mem_cone _ hOne_mem_cone)))
end
