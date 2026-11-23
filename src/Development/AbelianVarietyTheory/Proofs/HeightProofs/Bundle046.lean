module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle997
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeDensL
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

namespace GlobalTheory.TypeSum

theorem measurable_derFam_comp (n : ℕ) (ε : Fin n → Bool) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ)
    (hF : GlobalTheory.TypeSum.IsDerFam ε F) (h0 : ContinuousOn (F []) (UJset ε)) :
    ∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) →
    ∀ (T : Type) [TopologicalSpace T] [MeasurableSpace T] [OpensMeasurableSpace T] (φ : T → GlobalTheory.TypeSum.Mx n),
      Continuous φ → (∀ t, φ t ∈ UJset ε) → Measurable (fun t => F l (φ t)) := by
  intro l
  induction l with
  | nil =>
    intro _ T _ _ _ φ hφ hφU
    exact (h0.comp_continuous hφ hφU).measurable
  | cons X l ih =>
    intro hl T _ _ _ φ hφ hφU
    have hX : X ∈ lieSet ε := hl X (List.mem_cons_self ..)
    have hl' : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)

    let q : ℕ → T → ℂ := fun m t =>
      (((m : ℝ) + 1)⁻¹)⁻¹ • (F l (φ t * NormedSpace.exp ((((m : ℝ) + 1)⁻¹) • X)) - F l (φ t))
    have hq : ∀ m, Measurable (q m) := by
      intro m
      have h1 : Measurable (fun t => F l (φ t * NormedSpace.exp ((((m : ℝ) + 1)⁻¹) • X))) :=
        ih hl' T (fun t => φ t * NormedSpace.exp ((((m : ℝ) + 1)⁻¹) • X))
          (hφ.mul continuous_const) (fun t => mul_mem_UJ (hφU t) (exp_mem_UJ hX _))
      have h2 : Measurable (fun t => F l (φ t)) := ih hl' T φ hφ hφU
      exact (h1.sub h2).const_smul ((((m : ℝ) + 1)⁻¹)⁻¹ : ℝ)
    have hlim : ∀ t, Tendsto (fun m => q m t) atTop (𝓝 (F (X :: l) (φ t))) := by
      intro t
      have hd := hF l hl' X hX (φ t) (hφU t)
      have hs := hd.tendsto_slope_zero
      have hseq : Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹) atTop (𝓝[≠] (0 : ℝ)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun m => ?_⟩
        · simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; positivity
      have := hs.comp hseq
      refine this.congr fun m => ?_
      simp [q, Function.comp, zero_add]
    exact measurable_of_tendsto_metrizable hq (tendsto_pi_nhds.2 hlim)

end GlobalTheory.TypeSum
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

namespace GlobalTheory.TypeSum

theorem derFam_expand_words : ∀ (n : ℕ) (ε : Fin n → Bool) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ), GlobalTheory.TypeSum.IsDerFam ε F →
    ∀ (d : ℕ) (b : Fin d → GlobalTheory.TypeSum.Mx n) (c : Fin d → GlobalTheory.TypeSum.Mx n → ℝ), (∀ i, b i ∈ lieSet ε) →
    (∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ Z ∈ lieSet ε, ∀ g ∈ UJset ε,
      F (Z :: l) g = ∑ i, (c i Z : ℂ) * F (b i :: l) g) →
    ∀ (m : ℕ) (Y : Fin m → GlobalTheory.TypeSum.Mx n), (∀ j, Y j ∈ lieSet ε) → ∀ g ∈ UJset ε,
      F (List.ofFn Y) g = ∑ J : Fin m → Fin d, (∏ j, (c (J j) (Y j) : ℂ)) * F (List.ofFn fun j => b (J j)) g := by
  intro n ε F hF d b c hb hlin m
  induction m with
  | zero =>
    intro Y _ g _
    simp
  | succ m ih =>
    intro Y hY g hg
    have hwb : ∀ J : Fin m → Fin d, ∀ Z ∈ List.ofFn (fun j => b (J j)), Z ∈ lieSet ε := by
      intro J Z hZ
      obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hZ
      exact hb _
    have hwY : ∀ Z ∈ List.ofFn (fun j : Fin m => Y j.succ), Z ∈ lieSet ε := by
      intro Z hZ
      obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hZ
      exact hY _
    have key : ∀ i, F (b i :: List.ofFn (fun j : Fin m => Y j.succ)) g =
        ∑ J : Fin m → Fin d, (∏ j, (c (J j) (Y j.succ) : ℂ)) * F (b i :: List.ofFn fun j => b (J j)) g := by
      intro i
      have h1 := hF (List.ofFn fun j : Fin m => Y j.succ) hwY (b i) (hb i) g hg
      have h2 : HasDerivAt (fun t : ℝ => ∑ J : Fin m → Fin d, (∏ j, (c (J j) (Y j.succ) : ℂ)) *
          F (List.ofFn fun j => b (J j)) (g * NormedSpace.exp (t • b i)))
          (∑ J : Fin m → Fin d, (∏ j, (c (J j) (Y j.succ) : ℂ)) * F (b i :: List.ofFn fun j => b (J j)) g) 0 := by
        apply HasDerivAt.fun_sum
        intro J _
        exact (hF _ (hwb J) (b i) (hb i) g hg).const_mul _
      have heq : (fun t : ℝ => F (List.ofFn fun j : Fin m => Y j.succ) (g * NormedSpace.exp (t • b i))) =
          fun t : ℝ => ∑ J : Fin m → Fin d, (∏ j, (c (J j) (Y j.succ) : ℂ)) *
            F (List.ofFn fun j => b (J j)) (g * NormedSpace.exp (t • b i)) := by
        funext t
        exact ih (fun j => Y j.succ) (fun j => hY _) _ (mul_mem_UJ hg (exp_mem_UJ (hb i) t))
      rw [heq] at h1
      exact h1.unique h2
    rw [List.ofFn_succ, hlin _ hwY (Y 0) (hY 0) g hg]
    simp_rw [key, Finset.mul_sum]
    rw [← (Fin.consEquiv fun _ => Fin d).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun J _ => ?_
    simp [Fin.consEquiv, Fin.prod_univ_succ, List.ofFn_succ, mul_assoc]

end GlobalTheory.TypeSum
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.SecondKindChart

section Norm
open scoped Matrix.Norms.Operator ContDiff

variable {n : ℕ}

theorem ofFn_prod_single {M : Type*} [Monoid M] : ∀ {d : ℕ} (g : Fin d → M) (j : Fin d),
    (∀ i, i ≠ j → g i = 1) → (List.ofFn g).prod = g j := by
  first
  | exact @_root_.GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single
  | exact _root_.GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single
  | (apply _root_.GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single <;> assumption)
  | (intros; apply _root_.GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ProductOfFnSingle.prod_ofFn_eq_single ..)

def lc {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) : (Fin d → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  ∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (b i)

theorem lc_apply {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (v : Fin d → ℝ) : lc b v = ∑ i, v i • b i := by
  simp [lc, ContinuousLinearMap.sum_apply]

theorem expProd_line {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (j : Fin d) (r : ℝ) :
    (List.ofFn fun i => NormedSpace.exp ((r • Pi.single j (1 : ℝ) : Fin d → ℝ) i • b i)).prod =
      NormedSpace.exp (r • b j) := by
  rw [ofFn_prod_single _ j]
  · simp
  · intro i hi
    simp [Pi.single_apply, hi]

theorem hasStrictFDerivAt_expProd {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) :
    HasStrictFDerivAt (fun s : Fin d → ℝ => (List.ofFn fun i => NormedSpace.exp (s i • b i)).prod) (lc b) 0 := by
  set f := fun s : Fin d → ℝ => (List.ofFn fun i => NormedSpace.exp (s i • b i)).prod with hfdef
  have hcd : ContDiff ℝ ∞ f := GlobalTheory.GardingVec.contDiff_expProd b
  have hs : HasStrictFDerivAt f (fderiv ℝ f 0) 0 := hcd.contDiffAt.hasStrictFDerivAt_fderiv (by simp)
  suffices e : fderiv ℝ f 0 = lc b by rwa [e] at hs
  have hD : HasFDerivAt f (fderiv ℝ f 0) 0 := hs.hasFDerivAt
  have hj : ∀ j : Fin d, fderiv ℝ f 0 (Pi.single j 1) = b j := by
    intro j
    have h1 : HasDerivAt (fun r : ℝ => f (r • Pi.single j (1 : ℝ))) (fderiv ℝ f 0 (Pi.single j 1)) 0 := by
      have hl : HasDerivAt (fun r : ℝ => r • (Pi.single j (1 : ℝ) : Fin d → ℝ)) ((1 : ℝ) • Pi.single j 1) 0 :=
        (hasDerivAt_id (0 : ℝ)).smul_const _
      rw [one_smul] at hl
      exact hD.comp_hasDerivAt_of_eq 0 hl (by simp)
    have h2 : HasDerivAt (fun r : ℝ => f (r • Pi.single j (1 : ℝ))) (b j) 0 := by
      have h3 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (b j) (0 : ℝ)
      simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h3
      refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
      exact expProd_line b j r
    exact h1.unique h2
  ext1 v

  rw [pi_eq_sum_univ v, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : (fun k => if j = k then (1 : ℝ) else 0) = Pi.single j 1 := by
    ext k; simp [Pi.single_apply, eq_comm]
  rw [e1, map_smul, map_smul, hj, lc_apply]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi; simp [Pi.single_apply, hi]
  · simp

end Norm

section Chart
open scoped Matrix.Norms.Operator ContDiff

theorem exp_product_chart_local (n : ℕ) (ε : Fin n → Bool) (d : ℕ) (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hb : ∀ i, b i ∈ lieSet ε)
    (hli : LinearIndependent ℝ b) (hsp : ∀ Z ∈ lieSet ε, ∃ c : Fin d → ℝ, Z = ∑ i, c i • b i) (c : Fin d → ℝ) :
    ∃ τ : ℝ → (Fin d → ℝ), τ 0 = 0 ∧ HasDerivAt τ c 0 ∧
      ∀ᶠ t in nhds (0 : ℝ), NormedSpace.exp (t • ∑ i, c i • b i) =
        (List.ofFn fun i => NormedSpace.exp (τ t i • b i)).prod := by
  classical
  set A : (Fin d → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ := lc b with hA
  have hAinj : LinearMap.ker (A : (Fin d → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have hx' : ∑ i, x i • b i = 0 := by rw [← lc_apply]; exact hx
    funext i
    exact Fintype.linearIndependent_iff.1 hli x hx' i
  obtain ⟨C, hC⟩ := LinearMap.exists_leftInverse_of_injective _ hAinj
  let Cc : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin d → ℝ) := LinearMap.toContinuousLinearMap C
  have hCA : ∀ v, Cc (A v) = v := fun v => LinearMap.congr_fun hC v
  set f : (Fin d → ℝ) → Matrix (Fin n) (Fin n) ℂ :=
    fun s => (List.ofFn fun i => NormedSpace.exp (s i • b i)).prod with hfdef
  have hf : HasStrictFDerivAt f A 0 := hasStrictFDerivAt_expProd b
  have hf0 : f 0 = 1 := by simp [hfdef]
  have hlog : HasStrictFDerivAt (Formalism.MainNotions.S.Gauge.logM n) (ContinuousLinearMap.id ℝ _) (f 0) := by
    have h := (Formalism.MainNotions.S.Gauge.hasStrict_expM (n := n)).to_localInverse
    rw [NormedSpace.exp_zero] at h
    rw [hf0]
    exact h
  set ψ : (Fin d → ℝ) → (Fin d → ℝ) := fun s => Cc (Formalism.MainNotions.S.Gauge.logM n (f s)) with hψdef
  have hψ : HasStrictFDerivAt ψ ((ContinuousLinearEquiv.refl ℝ (Fin d → ℝ) : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) :
      (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) 0 := by
    have h := Cc.hasStrictFDerivAt.comp (0 : Fin d → ℝ) (hlog.comp (0 : Fin d → ℝ) hf)
    have e : (Cc.comp ((ContinuousLinearMap.id ℝ (Formalism.MainNotions.S.Gauge.MxC n)).comp A)) =
        ((ContinuousLinearEquiv.refl ℝ (Fin d → ℝ) : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) := by
      ext1 v
      simp [hCA]
    exact h.congr_fderiv e
  have hψ0 : ψ 0 = 0 := by simp [hψdef, hf0, Formalism.MainNotions.S.Gauge.logM_one]
  set g := hψ.localInverse ψ _ 0 with hgdef
  have hg : HasFDerivAt g (((ContinuousLinearEquiv.refl ℝ (Fin d → ℝ)).symm : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) :
      (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (ψ 0) := hψ.to_localInverse.hasFDerivAt
  have hg0 : g (ψ 0) = 0 := hψ.localInverse_apply_image
  refine ⟨fun t => g (t • c), ?_, ?_, ?_⟩
  · simp only [zero_smul]; simpa [hψ0] using hg0
  · have hl : HasDerivAt (fun t : ℝ => t • c) ((1 : ℝ) • c) 0 := (hasDerivAt_id (0 : ℝ)).smul_const _
    rw [one_smul] at hl
    have := hg.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp [hψ0])
    exact this
  ·
    have hlin : Filter.Tendsto (fun t : ℝ => t • c) (nhds 0) (nhds (ψ 0)) := by
      exact (continuous_id.smul continuous_const : Continuous fun t : ℝ => t • c).tendsto' 0 (ψ 0) (by simp [hψ0])
    have E1 : ∀ᶠ t in nhds (0 : ℝ), ψ (g (t • c)) = t • c := hlin.eventually hψ.eventually_right_inverse
    have hτc : ContinuousAt (fun t : ℝ => g (t • c)) 0 := by
      exact hg.continuousAt.comp_of_eq
        (continuous_id.smul continuous_const : Continuous fun t : ℝ => t • c).continuousAt (by simp [hψ0])
    have hfc : ContinuousAt (fun t : ℝ => f (g (t • c))) 0 :=
      (GlobalTheory.GardingVec.contDiff_expProd b).continuous.continuousAt.comp hτc
    have E2 : ∀ᶠ t in nhds (0 : ℝ), f (g (t • c)) ∈ Formalism.MainNotions.S.Gauge.tOne ε := by
      apply hfc.preimage_mem_nhds
      have h0 : f (g ((0 : ℝ) • c)) = 1 := by simp only [zero_smul]; rw [← hψ0, hg0, hf0]
      rw [h0]
      exact (Formalism.MainNotions.S.Gauge.isOpen_tOne ε).mem_nhds (Formalism.MainNotions.S.Gauge.one_mem_tOne ε)
    filter_upwards [E1, E2] with t h1 h2
    set y := f (g (t • c)) with hy
    have hU : Formalism.REAL.inUJ ε y := by
      have := GlobalTheory.LowTypeDetermined.expProd_mem (GlobalTheory.TypeSum.isUnit_Jm ε) (Xs := b) (fun i => hb i) (g (t • c))
      exact this
    obtain ⟨hG, hE⟩ := Formalism.MainNotions.S.Gauge.logM_inG h2 hU
    obtain ⟨c', hc'⟩ := hsp _ hG
    have hc'A : Formalism.MainNotions.S.Gauge.logM n y = A c' := by rw [hc', hA, lc_apply]
    have hψy : ψ (g (t • c)) = c' := by
      show Cc (Formalism.MainNotions.S.Gauge.logM n y) = c'
      rw [hc'A, hCA]
    have hcc : c' = t • c := by rw [← hψy, h1]
    have hL : Formalism.MainNotions.S.Gauge.logM n y = t • ∑ i, c i • b i := by
      rw [hc'A, hcc, map_smul, hA, lc_apply]
    rw [← hL, hE]

end Chart

theorem exp_eq_expProd_near_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (d : ℕ) (b : Fin d → GlobalTheory.TypeSum.Mx n), (∀ i, b i ∈ lieSet ε) →
    LinearIndependent ℝ b → (∀ Z ∈ lieSet ε, ∃ c : Fin d → ℝ, Z = ∑ i, c i • b i) →
    ∀ c : Fin d → ℝ, ∃ τ : ℝ → (Fin d → ℝ), τ 0 = 0 ∧ HasDerivAt τ c 0 ∧
      ∀ᶠ t in nhds (0 : ℝ), NormedSpace.exp (t • ∑ i, c i • b i) =
        (List.ofFn fun i => NormedSpace.exp (τ t i • b i)).prod :=
  fun n ε d b hb hli hsp c => exp_product_chart_local n ε d b hb hli hsp c

end GlobalTheory.SecondKindChart
end
end
