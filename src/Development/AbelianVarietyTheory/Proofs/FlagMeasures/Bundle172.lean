module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle121
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle111
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle127
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle129
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle149
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle138
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle143
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DecGapOfFormula
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle098
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle154
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

theorem eq_top_of_map_lattice_mem {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ) {m : ℕ}
    (Λ : Submodule (𝓞 E) (Fin m → E)) (hΛ : Submodule.span E (Λ : Set (Fin m → E)) = ⊤)
    (W : Submodule ℂ (Fin m → ℂ)) (h : ∀ t ∈ Λ, (fun l => φ (t l)) ∈ W) : W = ⊤ := by

  have hall : ∀ x : Fin m → E, (fun l => φ (x l)) ∈ W := by
    intro x
    have hx : x ∈ Submodule.span E (Λ : Set (Fin m → E)) := by rw [hΛ]; trivial
    induction hx using Submodule.span_induction with
    | mem t ht => exact h t ht
    | zero =>
      have e1 : (fun l => φ ((0 : Fin m → E) l)) = 0 := by
        funext l; simp
      rw [e1]; exact W.zero_mem
    | add x y _ _ hx hy =>
      have e1 : (fun l => φ ((x + y) l)) = (fun l => φ (x l)) + (fun l => φ (y l)) := by
        funext l; simp
      rw [e1]; exact W.add_mem hx hy
    | smul c x _ hx =>
      have e1 : (fun l => φ ((c • x) l)) = φ c • (fun l => φ (x l)) := by
        funext l; simp
      rw [e1]; exact W.smul_mem _ hx

  have key : ∀ l, (Pi.single l (1 : ℂ) : Fin m → ℂ) ∈ W := by
    intro l
    convert hall (Pi.single l 1) using 1
    funext l'
    by_cases hl : l' = l
    · subst hl; simp
    · simp [hl]
  rw [eq_top_iff]
  intro w _
  have hw : w = ∑ l, w l • (Pi.single l (1 : ℂ) : Fin m → ℂ) := by
    funext l'; simp [Finset.sum_apply, Pi.single_apply]
  rw [hw]
  exact W.sum_mem fun l _ => W.smul_mem _ (key l)

theorem spansFlag_flagAt : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ v, SpansFlag (fun i => (I.P v)⁻¹ * (T i).map (I.φ v)) (flagAt I S v) := by
  intro I I₀ e xf a j S Λ x₀ T T' T₀ hA v k y
  obtain ⟨-, -, -, hiso, hpair, -, hlam, hS⟩ := hA

  have hspan (i : Fin a) : Submodule.span I.E (Λ i : Set (Fin (j i) → I.E)) = ⊤ := by
    -- The dual frame projects the ambient lattice onto the i-th coordinate block.
    let p := ((T' i)ᴴ * I.J).mulVecLin
    have hJ : I.Jᴴ = I.J := by
      ext r s
      simpa [Formalism.UG.cT, starRingEnd_apply] using congrFun (congrFun I.J_herm r) s
    have hswap (b : Fin a) : (T' i)ᴴ * I.J * T b = ((T b)ᴴ * I.J * T' i)ᴴ := by
      simp [hJ, Matrix.mul_assoc]
    have hpT (x : Fin (j i) → I.E) : p (T i *ᵥ x) = x := by
      simp only [p, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
      rw [hswap, (hpair i).1, Matrix.conjTranspose_one, Matrix.one_mulVec]
    have hple : Submodule.span I.E (lamX I (1, xf) : Set (Fin I.n → I.E)) ≤
        (Submodule.span I.E (Λ i : Set (Fin (j i) → I.E))).comap p := by
      refine Submodule.span_le.2 fun z hz => ?_
      obtain ⟨u, u', z₀, hu, -, -, rfl⟩ := (hlam z).1 hz
      have hsum : p (∑ b, T b *ᵥ u b) = u i := by
        rw [map_sum, Finset.sum_eq_single i, hpT]
        · intro b _ hbi
          simp only [p, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
          rw [hswap, (hiso b i).2.2 hbi, Matrix.conjTranspose_zero, Matrix.zero_mulVec]
        · simp
      have hsum' : p (∑ b, T' b *ᵥ u' b) = 0 := by
        rw [map_sum]
        refine Finset.sum_eq_zero fun b _ => ?_
        simp only [p, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
        rw [(hiso i b).2.1, Matrix.zero_mulVec]
      have hp₀ (x : Fin I₀.n → I.E) : p (T₀ *ᵥ x) = 0 := by
        simp only [p, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
        rw [(hpair i).2.2, Matrix.zero_mulVec]
      change p _ ∈ Submodule.span I.E (Λ i : Set (Fin (j i) → I.E))
      rw [map_add, map_add, hsum, hsum', hp₀, add_zero, add_zero]
      exact Submodule.subset_span (hu i)
    rw [(GlobalTheory.PointLattice.lamX_selfDual I (1, xf)).2.2.1] at hple
    refine eq_top_iff.2 fun x _ => ?_
    have hx := hple (Submodule.mem_top (x := T i *ᵥ x))
    rwa [Submodule.mem_comap, hpT] at hx

  have himg : ∀ u : ∀ i, Fin (j i) → I.E,
      ((I.P v)⁻¹ *ᵥ fun l => I.φ v ((∑ i, T i *ᵥ u i) l)) =
        ∑ i, ((I.P v)⁻¹ * (T i).map (I.φ v)) *ᵥ (fun l => I.φ v (u i l)) := by
    intro u
    have e1 : (fun l => I.φ v ((∑ i, T i *ᵥ u i) l)) =
        ∑ i, (T i).map (I.φ v) *ᵥ (fun l => I.φ v (u i l)) := by
      funext l

      simp only [Finset.sum_apply, map_sum, RingHom.map_mulVec, Function.comp_def]
    rw [e1, Matrix.mulVec_sum]
    exact Finset.sum_congr rfl fun i _ => Matrix.mulVec_mulVec _ _ _
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      obtain ⟨u, -, hk, rfl⟩ := (hS k z).1 hz
      refine ⟨fun i l => I.φ v (u i l), fun i hi => ?_, himg u⟩
      funext l
      simp [hk i hi]
    | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨u', hu', rfl⟩ := hy
      refine ⟨u + u', fun i hi => by simp [hu i hi, hu' i hi], ?_⟩
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => (Matrix.mulVec_add _ _ _).symm
    | smul c x _ hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      refine ⟨c • u, fun i hi => by simp [hu i hi], ?_⟩
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => (Matrix.mulVec_smul _ _ _).symm
  · rintro ⟨u, hu, rfl⟩
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hik : i.castSucc < k
    · have htop := eq_top_of_map_lattice_mem (I.φ v) (Λ i) (hspan i)
        ((flagAt I S v k).comap (Matrix.mulVecLin ((I.P v)⁻¹ * (T i).map (I.φ v)))) (by
          intro t ht
          rw [Submodule.mem_comap, Matrix.mulVecLin_apply]
          let w : ∀ i', Fin (j i') → I.E := Pi.single i t
          have hw1 : ∀ i', w i' ∈ Λ i' := by
            intro i'
            by_cases h' : i' = i
            · subst h'; simpa [w] using ht
            · simp [w, Pi.single_eq_of_ne h']
          have hw2 : ∀ i' : Fin a, ¬ i'.castSucc < k → w i' = 0 := by
            intro i' hi'
            have h' : i' ≠ i := by rintro rfl; exact hi' hik
            simp [w, Pi.single_eq_of_ne h']
          have hz : (∑ i', T i' *ᵥ w i') ∈ S k := (hS k _).2 ⟨w, hw1, hw2, rfl⟩
          have hmem := Submodule.subset_span (R := ℂ) (Set.mem_image_of_mem
            (fun y : Fin I.n → I.E => (I.P v)⁻¹ *ᵥ fun l => I.φ v (y l)) hz)
          have hsum := himg w
          rw [hsum, Finset.sum_eq_single i] at hmem
          · simp [w] at hmem
            exact hmem
          · intro i' _ h'
            simp [w, Pi.single_eq_of_ne h']
            exact Matrix.mulVec_zero _
          · simp)
      have : u i ∈ (flagAt I S v k).comap (Matrix.mulVecLin ((I.P v)⁻¹ * (T i).map (I.φ v))) := by
        rw [htop]; trivial
      simpa [Submodule.mem_comap, Matrix.mulVecLin_apply] using this
    · simp [hu i hik]

end GlobalTheory.LeviIso
end

section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.unipotentRadical_block_unitriangular_flag : ∀ (k r : ℕ), ∀ g ∈ Nset k r, ∀ i j : Fin (2 * r + k + 1), lev k r j ≤ lev k r i → g i j = (1 : Mat k r) i j := by
  first | exact @GlobalTheory.CellDens.nset_block_unitriangular | exact GlobalTheory.CellDens.nset_block_unitriangular | (intros; apply GlobalTheory.CellDens.nset_block_unitriangular <;> assumption)
end

section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate

theorem _root_.GlobalTheory.T.unitaryTubeProductChart_hasStrictFDerivAt_entry : ∀ (k : ℕ) (η : ℝ) (i j : Fin (k + 1)), ∃ D : Par k →L[ℝ] ℂ, HasStrictFDerivAt (fun x : Par k => chart η x i j) D 0 ∧ ∀ v, D v = tang η v i j := by
  first | exact @GlobalTheory.TubeDeriv.chart_hasStrictFDerivAt | exact GlobalTheory.TubeDeriv.chart_hasStrictFDerivAt | (intros; apply GlobalTheory.TubeDeriv.chart_hasStrictFDerivAt <;> assumption)
end

section

open Formalism.HermitianLatticeCounting.S6

namespace GlobalTheory.RowStab

theorem gen_comp_gen_neg {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (H : HermSpace K V) (J : Finset ι) (e ρ : ι → V) (c c' : ι → ι → K)
    (he : ∀ a b, H.B (e a) (e b) = 0) (hρe : ∀ a b, H.B (ρ a) (e b) = 0)
    (hc : ∀ a b, c a b + c' a b + H.B (ρ b) (ρ a) = 0) (v : V) :
    gen H J e ρ c (gen H J e (-ρ) c' v) = v := by
  have heρ : ∀ a b, H.B (e a) (ρ b) = 0 := fun a b => by rw [← H.herm, hρe, star_zero]
  set u := gen H J e (-ρ) c' v with hu
  have hue : ∀ b, H.B u (e b) = H.B v (e b) := by
    intro b
    rw [hu, gen_apply]
    simp [LinearMap.sum_apply, he, hρe]
  have huρ : ∀ b, H.B u (ρ b) = H.B v (ρ b) - ∑ d ∈ J, H.B v (e d) * H.B (ρ d) (ρ b) := by
    intro b
    rw [hu, gen_apply]
    simp [LinearMap.sum_apply, heρ, sub_eq_add_neg]
  have h4 : ∑ b ∈ J, (∑ d ∈ J, H.B v (e d) * H.B (ρ d) (ρ b)) • e b =
      ∑ b ∈ J, ∑ a ∈ J, (H.B (ρ b) (ρ a) * H.B v (e b)) • e a := by
    simp_rw [Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
  have key : (∑ b ∈ J, ∑ a ∈ J, (c' a b * H.B v (e b)) • e a) +
      (∑ b ∈ J, (∑ d ∈ J, H.B v (e d) * H.B (ρ d) (ρ b)) • e b) +
      ∑ b ∈ J, ∑ a ∈ J, (c a b * H.B v (e b)) • e a = 0 := by
    rw [h4, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [← add_smul, ← add_smul, ← add_mul, ← add_mul,
      show c' a b + H.B (ρ b) (ρ a) + c a b = 0 by linear_combination hc a b, zero_mul, zero_smul]
  rw [gen_apply H J e ρ c u]
  simp only [hue, huρ]
  rw [hu, gen_apply H J e (-ρ) c' v]
  simp only [map_neg, Pi.neg_apply, neg_smul, smul_neg, sub_smul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  linear_combination (norm := module) key

end GlobalTheory.RowStab
end

section

open Formalism.HermitianLatticeCounting.S6

namespace GlobalTheory.RowStab

theorem gen_isometry {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (J : Finset ι) (e ρ : ι → V) (c : ι → ι → K) (hee : ∀ a b, H.B (e a) (e b) = 0) (hρe : ∀ a b, H.B (ρ a) (e b) = 0) (hc : ∀ a b, star (c a b) + c b a + H.B (ρ a) (ρ b) = 0) (u v : V) : H.B (GlobalTheory.RowStab.gen H J e ρ c u) (GlobalTheory.RowStab.gen H J e ρ c v) = H.B u v := by
  have heρ : ∀ a b, H.B (e a) (ρ b) = 0 := fun a b => by rw [← H.herm, hρe, star_zero]
  have hX : ∀ w y, H.B (∑ b ∈ J, (H.B w (e b) • ρ b - H.B w (ρ b) • e b + ∑ a ∈ J, (c a b * H.B w (e b)) • e a)) y = ∑ b ∈ J, (H.B w (e b) * H.B (ρ b) y - H.B w (ρ b) * H.B (e b) y + ∑ a ∈ J, c a b * H.B w (e b) * H.B (e a) y) := by
    intro w y

    simp [map_sum, LinearMap.sum_apply, mul_assoc]
  have hXr : ∀ w y, H.B y (∑ b ∈ J, (H.B w (e b) • ρ b - H.B w (ρ b) • e b + ∑ a ∈ J, (c a b * H.B w (e b)) • e a)) = star (∑ b ∈ J, (H.B w (e b) * H.B (ρ b) y - H.B w (ρ b) * H.B (e b) y + ∑ a ∈ J, c a b * H.B w (e b) * H.B (e a) y)) := by
    intro w y; rw [← H.herm, hX]
  have hρv : ∀ b, H.B (ρ b) v = star (H.B v (ρ b)) := fun b => (H.herm _ _).symm
  have hev : ∀ b, H.B (e b) v = star (H.B v (e b)) := fun b => (H.herm _ _).symm
  have hρu : ∀ b, H.B (ρ b) u = star (H.B u (ρ b)) := fun b => (H.herm _ _).symm
  have heu : ∀ b, H.B (e b) u = star (H.B u (e b)) := fun b => (H.herm _ _).symm
  rw [GlobalTheory.RowStab.gen_apply, GlobalTheory.RowStab.gen_apply]
  simp only [map_add (f := _), LinearMap.add_apply, hX, hXr, hee, heρ, hρe, mul_zero, sub_zero, add_zero, Finset.sum_const_zero, star_zero, hρv, hev, hρu, heu, star_sum, star_add, star_sub, star_mul', star_star]
  have hρρ : ∀ a b, star (H.B (ρ a) (ρ b)) = H.B (ρ b) (ρ a) := fun a b => H.herm _ _
  simp only [hρρ]
  have h2 : ∑ x ∈ J, ∑ x1 ∈ J, star (c x1 x) * star (H.B v (e x)) * H.B u (e x1) = ∑ x ∈ J, ∑ x1 ∈ J, star (c x x1) * star (H.B v (e x1)) * H.B u (e x) := Finset.sum_comm
  have hS : ∑ x ∈ J, ∑ x1 ∈ J, c x1 x * H.B u (e x) * star (H.B v (e x1)) + ∑ x ∈ J, ∑ x1 ∈ J, star (c x1 x) * star (H.B v (e x)) * H.B u (e x1) + ∑ x ∈ J, H.B u (e x) * ∑ x1 ∈ J, star (H.B v (e x1)) * H.B (ρ x) (ρ x1) = 0 := by
    rw [h2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro x _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro x1 _
    linear_combination (H.B u (e x) * star (H.B v (e x1))) * hc x x1
  have hA : ∑ x ∈ J, star (H.B v (ρ x)) * H.B u (e x) = ∑ x ∈ J, H.B u (e x) * star (H.B v (ρ x)) := Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hB : ∑ x ∈ J, star (H.B v (e x)) * H.B u (ρ x) = ∑ x ∈ J, H.B u (ρ x) * star (H.B v (e x)) := Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  linear_combination hS - hA + hB

end GlobalTheory.RowStab
end

section

open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.KFinAvg

theorem sum_normSq_col {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) (i : Fin n) :
    ∑ j, ‖g j i‖ ^ 2 = 1 := by
  have h1 : star g * g = 1 := (Matrix.mem_unitaryGroup_iff').1 hg
  have h2 : (star g * g) i i = 1 := by rw [h1]; simp
  rw [Matrix.mul_apply] at h2
  have h3 : ((∑ j, ‖g j i‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h2]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.star_apply, Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  exact_mod_cast h3

theorem norm_entry_le_one {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) (j i : Fin n) :
    ‖g j i‖ ≤ 1 := by
  have h := sum_normSq_col hg i
  have h2 : ‖g j i‖ ^ 2 ≤ ∑ j, ‖g j i‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖g j i‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
  rw [h] at h2
  nlinarith [norm_nonneg (g j i)]

theorem re_trace_eq {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    (Matrix.trace g).re = ∑ i, (g i i).re := by
  simp [Matrix.trace, Complex.re_sum]

theorem eq_one_of_re_trace {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)))
    (ht : (Matrix.trace g).re = n) : g = 1 := by
  have hle : ∀ i, (g i i).re ≤ 1 := fun i =>
    (Complex.re_le_norm _).trans (norm_entry_le_one hg i i)
  have hsum : ∑ i : Fin n, (1 - (g i i).re) = 0 := by
    rw [Finset.sum_sub_distrib, ← re_trace_eq, ht]
    simp
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.2 (hle i))).1 hsum
  have hre : ∀ i, (g i i).re = 1 := fun i => by
    have := hz i (Finset.mem_univ i)
    linarith
  have hnorm : ∀ i, ‖g i i‖ = 1 := fun i => le_antisymm (norm_entry_le_one hg i i)
    (by simpa [hre i] using Complex.re_le_norm (g i i))
  have hdiag : ∀ i, g i i = 1 := fun i => by
    have h1 : ‖g i i‖ ^ 2 = (g i i).re ^ 2 + (g i i).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [hnorm i, hre i] at h1
    have him : (g i i).im = 0 := by nlinarith
    exact Complex.ext (by simpa using hre i) (by simpa using him)
  ext j i
  by_cases hji : j = i
  · subst hji
    simp [hdiag j]
  · have hs := sum_normSq_col hg i
    have h0 : ∑ k ∈ Finset.univ.erase i, ‖g k i‖ ^ 2 = 0 := by
      have := Finset.add_sum_erase Finset.univ (fun k => ‖g k i‖ ^ 2) (Finset.mem_univ i)
      rw [hs, hnorm i] at this
      linarith
    have hz2 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by positivity)).1 h0
    have := hz2 j (Finset.mem_erase.2 ⟨hji, Finset.mem_univ j⟩)
    have hn : ‖g j i‖ = 0 := by simpa using this
    rw [Matrix.one_apply_ne hji]
    exact norm_eq_zero.1 hn

theorem peak_continuous (n : ℕ) : Continuous (peak n) := by
  unfold peak
  have : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => (Matrix.trace g).re :=
    Complex.continuous_re.comp continuous_id.matrix_trace
  fun_prop

theorem peak_one {n : ℕ} (hn : 0 < n) : peak n 1 = 1 := by
  have : (n : ℝ) ≠ 0 := by positivity
  simp [peak, Matrix.trace_one, this]

theorem abs_re_trace_le {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) :
    |(Matrix.trace g).re| ≤ n := by
  rw [re_trace_eq]
  calc |∑ i, (g i i).re| ≤ ∑ i, |(g i i).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ =>
        (Complex.abs_re_le_norm _).trans (norm_entry_le_one hg i i)
    _ = n := by simp

theorem peak_mem_Icc {n : ℕ} (hn : 0 < n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) :
    0 ≤ peak n g ∧ peak n g ≤ 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := abs_le.1 (abs_re_trace_le hg)
  have h1 : -1 ≤ (Matrix.trace g).re / n := by
    rw [le_div_iff₀ hn']; linarith [h.1]
  have h2 : (Matrix.trace g).re / n ≤ 1 := by
    rw [div_le_iff₀ hn']; linarith [h.2]
  unfold peak
  constructor <;> linarith

theorem peak_lt_one {n : ℕ} (hn : 0 < n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) (h1 : g ≠ 1) :
    peak n g < 1 := by
  refine lt_of_le_of_ne (peak_mem_Icc hn hg).2 fun he => h1 (eq_one_of_re_trace hg ?_)
  have hn' : (n : ℝ) ≠ 0 := by positivity
  unfold peak at he
  have : (Matrix.trace g).re / n = 1 := by linarith
  field_simp at this
  linarith

theorem peak_properties : ∀ n : ℕ, 0 < n → Continuous (GlobalTheory.KFinAvg.peak n) ∧ GlobalTheory.KFinAvg.peak n 1 = 1 ∧
    (∀ g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)),
      0 ≤ GlobalTheory.KFinAvg.peak n g ∧ GlobalTheory.KFinAvg.peak n g ≤ 1) ∧
    ∀ U ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), ∃ δ < 1,
      ∀ g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)),
        g ∉ U → GlobalTheory.KFinAvg.peak n g ≤ δ := by
  intro n hn
  refine ⟨peak_continuous n, peak_one hn, fun g hg => peak_mem_Icc hn hg, fun U hU => ?_⟩
  have hK : IsCompact ((Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) ∩ (interior U)ᶜ) :=
    (GlobalTheory.isCompact_unitaryGroup (Fin n) ℂ).inter_right isOpen_interior.isClosed_compl
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ interior U := mem_interior_iff_mem_nhds.2 hU
  rcases Set.eq_empty_or_nonempty
      ((Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) ∩ (interior U)ᶜ) with he | hne
  · refine ⟨0, by norm_num, fun g hg hgU => ?_⟩
    have : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) ∩ (interior U)ᶜ :=
      ⟨hg, fun hi => hgU (interior_subset hi)⟩
    rw [he] at this
    exact this.elim
  · obtain ⟨g₀, hg₀, hmax⟩ := hK.exists_isMaxOn hne (peak_continuous n).continuousOn
    have hne1 : g₀ ≠ 1 := fun h => hg₀.2 (h ▸ h1)
    refine ⟨peak n g₀, peak_lt_one hn hg₀.1 hne1, fun g hg hgU => ?_⟩
    exact hmax ⟨hg, fun hi => hgU (interior_subset hi)⟩

end GlobalTheory.KFinAvg
end
end

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.DecGapBound

theorem decGap_of_formulaGap : FormulaGap → DecGap := by
  intro hF n ε lam H _ _ σ hlam hDS h hgap hh g hg u hu v hv
  have hU := hDS.2.2.1
  have h1 : ‖⟪v, σ g u⟫_ℂ‖ ≤ decHS h (rkR ε) (dHS g) * ‖u‖ * ‖v‖ := by
    obtain ⟨k, X, hk, hX, hgk⟩ := (polar_decomposition_holds n ε).1 g hg
    have hs' := GlobalTheory.LowKProj.mem_UJset_of_Kset (Kset_star ε hk)
    have hkk : star k * k = 1 := hk.1.1
    have e1 : σ (NormedSpace.exp X) u = σ (star k) (σ g u) := by
      have h := hU.1.2 (star k) hs' g hg
      rw [show star k * g = NormedSpace.exp X by rw [hgk, ← Matrix.mul_assoc, hkk, Matrix.one_mul]] at h
      exact congrArg (fun F : H →L[ℂ] H => F u) h
    let L : H →ₗᵢ[ℂ] H := ⟨(σ (star k) : H →ₗ[ℂ] H), hU.2.1 _ hs'⟩
    have e2 : ⟪σ (star k) v, σ (star k) (σ g u)⟫_ℂ = ⟪v, σ g u⟫_ℂ := L.inner_map_map v (σ g u)
    have hb := dec_exp hF n ε lam H σ hlam hDS h hgap hh X hX u hu (σ (star k) v)
      (GlobalTheory.LowKProj.lowKSub_stable ε lam σ _ (Kset_star ε hk) v hv)
    rw [e1, e2, hU.2.1 _ hs' v, ← (GlobalTheory.Count.Cartan.cartan_distances n ε).1 k X hk hX, ← hgk] at hb
    exact hb
  refine ⟨h1, h1.trans ?_⟩
  have h0 : 0 ≤ h := le_trans (by positivity) hh
  obtain ⟨h2, h3⟩ := dOp_facts hg
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (decHS_le_decE _ h0 h2 h3) (norm_nonneg u)) (norm_nonneg v)

end GlobalTheory.DecGapBound
end

section

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

theorem _root_.GlobalTheory.T.rational_unipotentRadical_mem_adelic : ∀ (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (γ : GL (Fin I.n) I.E), γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J → I.InUnipRad (starRingEnd I.E) I.J W (γ : Matrix (Fin I.n) (Fin I.n) I.E) → ∃ a ∈ I.GFset ∩ I.NA W, (∀ v, uMat (a.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) ∧ I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
  first | exact @GlobalTheory.Proof.rational_unipotentRadical_mem_adelic.rational_mem_adelic | exact GlobalTheory.Proof.rational_unipotentRadical_mem_adelic.rational_mem_adelic | (intros; apply GlobalTheory.Proof.rational_unipotentRadical_mem_adelic.rational_mem_adelic <;> assumption)
end
