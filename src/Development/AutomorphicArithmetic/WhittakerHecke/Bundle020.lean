module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle002
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle001
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.SatakeEigenvalues
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
public import GroundTheory.IdeleRoots.TorusPowers.HeckeIdem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Lemma
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
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ConjInv

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private lemma nL_memK {K : Type} [Field K] [NumberField K] {v : H.P K} {c : H.Kv v} (hc : Valued.v c ≤ 1) :
    H.nL c ∈ GlobalTheory.LFun.KGL v (n := 2) := by
  have hc' : c ∈ v.adicCompletionIntegers K := hc
  have hn : -c ∈ v.adicCompletionIntegers K := neg_mem hc'
  rw [GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff]
  have h1 : (1 : H.Kv v) ∈ v.adicCompletionIntegers K := one_mem _
  have h0 : (0 : H.Kv v) ∈ v.adicCompletionIntegers K := zero_mem _
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · fin_cases i <;> fin_cases j
    · exact h1
    · exact hc'
    · exact h0
    · exact h1
  · fin_cases i <;> fin_cases j
    · exact h1
    · exact hn
    · exact h0
    · exact h1

private lemma fix_sum {K : Type} [Field K] [NumberField K] (φ : GL (Fin 2) (A K) → ℂ) (S : Finset (H.P K)) :
    (∀ w ∈ S, H.Fix w φ) → ∀ z : A K, z.1 = 0 → (∀ w, w ∉ S → H.cp w z = 0) → (∀ w, Valued.v (H.cp w z) ≤ 1) →
      ∀ g, φ (g * gl (nU z)) = φ g := by
  induction S using Finset.induction_on with
  | empty =>
    intro _ z h1 h2 _ g
    have hz : z = 0 := Prod.ext h1 (FiniteAdeleRing.ext K fun w => h2 w (Finset.notMem_empty w))
    have h : nU (0 : A K) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [nU]
    rw [hz, h, gl, map_one, mul_one]
  | insert w S hw ih =>
    intro hF z h1 h2 h3 g
    obtain ⟨-, -, hc, -, -, -, -, hs, -, -⟩ := H.sgLaws K w
    have hne : ∀ u, u ≠ w → H.cp u (H.sg w (H.cp w z)) = 0 := fun u hu => (hs _).2 u hu
    have e : z = (z - H.sg w (H.cp w z)) + H.sg w (H.cp w z) := (sub_add_cancel _ _).symm
    rw [e, nU_add, gl, map_mul, ← mul_assoc]
    have e2 : Matrix.SpecialLinearGroup.toGL (nU (H.sg w (H.cp w z))) = H.lc w (H.nL (H.cp w z)) :=
      ((H.lcLaws K w).1 _).symm
    rw [e2, hF w (Finset.mem_insert_self _ _) _ _ (nL_memK (h3 w))]
    refine ih (fun u hu => hF u (Finset.mem_insert_of_mem hu)) _ ?_ (fun u hu => ?_) (fun u => ?_) g
    · show z.1 - (H.sg w (H.cp w z)).1 = 0
      rw [h1, (hs _).1, sub_zero]
    · rw [map_sub]
      by_cases h : u = w
      · subst h
        rw [hc, sub_self]
      · rw [hne u h, sub_zero]
        exact h2 u (by simp [h, hu])
    · rw [map_sub]
      by_cases h : u = w
      · subst h
        rw [hc, sub_self, map_zero]
        exact zero_le'
      · rw [hne u h, sub_zero]
        exact h3 u

private lemma fin_over {E : Type} [Field E] [NumberField E] (v : H.P ℚ) :
    {w : H.P E | AdeleBaseChange.below ℚ w = v}.Finite := by
  have := v.isMaximal
  refine Set.Finite.of_finite_image (f := fun w : H.P E => w.asIdeal) ?_ fun a _ b _ h => HeightOneSpectrum.ext h
  refine (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).subset ?_
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w.isPrime, (AdeleBaseChange.below_eq_iff _ _).1 hw⟩

theorem UpperTheory.right_invariant_baseChangeUnipotent_of_places_above_fixed :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (φ : GL (Fin 2) (A E) → ℂ) (v : H.P ℚ), H.Gd D.δ v → (∀ w : H.P E, w.under (𝓞 ℚ) = v → H.Fix w φ) → ∀ c : H.Kv v, H.IsInt c → ∀ g, φ (g * Xg.nu D (H.sg v c)) = φ g := by
  intro E _ _ D φ v hG hF c hc g
  obtain ⟨-, -, hcp, -, -, -, -, hs, -, -⟩ := H.sgLaws ℚ v
  have hz : D.mkE 0 (H.sg v c) = AdeleBaseChange.adeleMap ℚ E (H.sg v c) * rt D.θ := by
    rw [Dat.mkE, map_zero, zero_add]
  have hoff : ∀ w : H.P E, AdeleBaseChange.below ℚ w ≠ v → H.cp w (D.mkE 0 (H.sg v c)) = 0 := fun w hw => by
    have h : H.cp w (AdeleBaseChange.adeleMap ℚ E (H.sg v c)) = 0 := by
      change SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w ((H.sg v c).2 (AdeleBaseChange.below ℚ w)) = 0
      rw [(hs c).2 _ hw, map_zero]
    rw [hz, map_mul, h, zero_mul]
  change φ (g * gl (nU (D.mkE 0 (H.sg v c)))) = φ g
  refine fix_sum φ (fin_over (E := E) v).toFinset (fun w hw => hF w ((fin_over v).mem_toFinset.1 hw)) _ ?_
    (fun w hw => hoff w fun h => hw ((fin_over v).mem_toFinset.2 h)) (fun w => ?_) g
  · rw [hz]
    change InfinitePlace.infiniteAdeleRingMap (H.sg v c).1 * _ = 0
    rw [(hs c).1, map_zero, zero_mul]
  · by_cases hw : AdeleBaseChange.below ℚ w = v
    · subst hw
      have hk : ∀ x : H.Kv (AdeleBaseChange.below ℚ w), Valued.v x ≤ 1 →
          Valued.v (SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w x) ≤ 1 := fun x hx => by
        rw [SemiLocal.valued_completionMap]
        exact pow_le_one' hx _
      have h1 : H.cp w (AdeleBaseChange.adeleMap ℚ E (H.sg _ c)) = SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w c :=
        congrArg (SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w) (hcp c)
      have h2 : H.cp w (rt D.θ) ^ 2 =
          SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w (D.δ : H.Kv (AdeleBaseChange.below ℚ w)) := by
        rw [← map_pow, ← map_pow, D.sq]
        have a := eq_ratCast (((H.cp w).comp (algebraMap E (A E))).comp (algebraMap ℚ E)) D.δ
        rw [map_ratCast]
        exact a
      have h3 : Valued.v (H.cp w (rt D.θ)) ≤ 1 := by
        have hd := hG.del
        rw [eq_ratCast] at hd
        have h := hk _ hd.le
        rw [← h2, map_pow] at h
        exact (pow_le_one_iff two_ne_zero).1 h
      rw [hz, map_mul, h1, map_mul]
      exact mul_le_one' (hk c hc) h3
    · rw [hoff w hw, map_zero]
      exact zero_le'
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

namespace UpperTheory.OrderAdditiveConjugation

variable {E : Type} [Field E] [NumberField E]

private theorem oh_zero : (0 : A E) ∈ Oh E := by
  refine ⟨rfl, fun v => ?_⟩
  have h : ((0 : A E).2 v) = 0 := rfl
  rw [h, map_zero]
  exact zero_le_one

private theorem oh_add {c d : A E} (hc : c ∈ Oh E) (hd : d ∈ Oh E) : c + d ∈ Oh E := by
  refine ⟨by show c.1 + d.1 = 0; rw [hc.1, hd.1, add_zero], fun v => ?_⟩
  have h : ((c + d).2 v) = c.2 v + d.2 v := rfl
  rw [h]
  exact (Valuation.map_add_le _ (hc.2 v) (hd.2 v))

private theorem oh_neg {c : A E} (hc : c ∈ Oh E) : -c ∈ Oh E := by
  refine ⟨by show -c.1 = 0; rw [hc.1, neg_zero], fun v => ?_⟩
  have h : ((-c).2 v) = -(c.2 v) := rfl
  rw [h, Valuation.map_neg]
  exact hc.2 v

private theorem oh_nat (n : ℕ) {c : A E} (hc : c ∈ Oh E) : (n : A E) * c ∈ Oh E := by
  induction n with
  | zero => simpa using oh_zero
  | succ n ih =>
    have : ((n + 1 : ℕ) : A E) * c = (n : A E) * c + c := by push_cast; ring
    rw [this]
    exact oh_add ih hc

private theorem oh_mul_of {T c : A E} (hT : ∀ w : H.P E, Valued.v (H.cp w T) ≤ 1) (hc : c ∈ Oh E) :
    T * c ∈ Oh E := by
  refine ⟨by show T.1 * c.1 = 0; rw [hc.1, mul_zero], fun v => ?_⟩
  have h : ((T * c).2 v) = H.cp v T * c.2 v := rfl
  rw [h, map_mul]
  exact mul_le_one' (hT v) (hc.2 v)

private theorem rt_mul_nat (L : ℕ) (θ : E) :
    (UpperTheory.ConvolutionTheory.R2.rt ((L : E) * θ) : A E) = (L : A E) * UpperTheory.ConvolutionTheory.R2.rt θ := by
  have : (UpperTheory.ConvolutionTheory.R2.rt ((L : E) * θ) : A E) = algebraMap E (A E) ((L : E) * θ) := rfl
  rw [this, map_mul, map_natCast]

private theorem nat_mul_iota (L : ℕ) (hL : 0 < L) : (L : A ℚ) * iota L = (0, 1) := by
  have hq : (L : ℚ) ≠ 0 := by exact_mod_cast hL.ne'
  refine Prod.ext ?_ ?_
  · show (L : A ℚ).1 * 0 = 0
    exact mul_zero _
  · show (L : A ℚ).2 * algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (L : ℚ)⁻¹ = 1
    have : (L : A ℚ).2 = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (L : ℚ) := by
      rw [map_natCast]; rfl
    rw [this, ← map_mul, mul_inv_cancel₀ hq, map_one]

private theorem unit_mul (L : ℕ) (hL : 0 < L) {r : A E} (hr : r ∈ Oh E) :
    ((L : A E) * am E (iota L)) * r = r := by
  have h1 : (L : A E) * am E (iota L) = am E ((L : A ℚ) * iota L) := by
    rw [map_mul, map_natCast]
  rw [h1, nat_mul_iota L hL]
  refine Prod.ext ?_ ?_
  · show (am E ((0, 1) : A ℚ)).1 * r.1 = r.1
    rw [hr.1, mul_zero]
  · show (am E ((0, 1) : A ℚ)).2 * r.2 = r.2
    have : (am E ((0, 1) : A ℚ)).2 = 1 := map_one (AdeleBaseChange.finiteAdeleMap ℚ E)
    rw [this, one_mul]

private theorem conj_entry {R : Type} [CommRing R] (O : Set R) (l t : R)
    (hadd : ∀ {c d : R}, c ∈ O → d ∈ O → c + d ∈ O) (hneg : ∀ {c : R}, c ∈ O → -c ∈ O)
    (P Q W : R → R) (hP : ∀ r ∈ O, P r ∈ O) (hQ : ∀ r ∈ O, Q r ∈ O) (hW : ∀ r ∈ O, W r ∈ O)
    (eP : ∀ r ∈ O, l ^ 5 * r = l * P r) (eQ : ∀ r ∈ O, t * (l ^ 5 * r) = l * Q r)
    (eW : ∀ r ∈ O, t * (t * (l ^ 5 * r)) = l * W r)
    (K : Matrix (Fin 2) (Fin 2) R)
    (hK : ∀ i j, ∃ c ∈ O, K i j - (1 : Matrix (Fin 2) (Fin 2) R) i j = l ^ 5 * c) :
    ∀ i j, ∃ c ∈ O, (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) i j - (1 : Matrix (Fin 2) (Fin 2) R) i j = l * c := by
  obtain ⟨c00, m00, h00⟩ := hK 0 0
  obtain ⟨c01, m01, h01⟩ := hK 0 1
  obtain ⟨c10, m10, h10⟩ := hK 1 0
  obtain ⟨c11, m11, h11⟩ := hK 1 1
  simp only [Matrix.one_apply_eq, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true, Matrix.one_apply_ne, sub_zero] at h00 h01 h10 h11
  have q00 := eQ c00 m00
  have q10 := eQ c10 m10
  have q11 := eQ c11 m11
  have p00 := eP c00 m00
  have p01 := eP c01 m01
  have p10 := eP c10 m10
  have p11 := eP c11 m11
  have w10 := eW c10 m10
  have a00 : (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 0 0 = K 0 0 - t * K 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]; ring
  have a01 : (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 0 1 = (K 0 0 - t * K 1 0) * t + (K 0 1 - t * K 1 1) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]; ring
  have a10 : (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 1 0 = K 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have a11 : (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 1 1 = K 1 0 * t + K 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  intro i j
  fin_cases i <;> fin_cases j
  · refine ⟨P c00 + -Q c10, hadd (hP _ m00) (hneg (hQ _ m10)), ?_⟩
    show (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 0 0 - (1 : Matrix (Fin 2) (Fin 2) R) 0 0 = _
    rw [a00, Matrix.one_apply_eq]
    linear_combination h00 - t * h10 + p00 - q10
  · refine ⟨Q c00 + P c01 + -W c10 + -Q c11, hadd (hadd (hadd (hQ _ m00) (hP _ m01)) (hneg (hW _ m10))) (hneg (hQ _ m11)), ?_⟩
    show (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 0 1 - (1 : Matrix (Fin 2) (Fin 2) R) 0 1 = _
    rw [a01, Matrix.one_apply_ne (by simp)]
    linear_combination t * h00 + h01 - t * t * h10 - t * h11 + q00 + p01 - w10 - q11
  · refine ⟨P c10, hP _ m10, ?_⟩
    show (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 1 0 - (1 : Matrix (Fin 2) (Fin 2) R) 1 0 = _
    rw [a10, Matrix.one_apply_ne (by simp)]
    linear_combination h10 + p10
  · refine ⟨Q c10 + P c11, hadd (hQ _ m10) (hP _ m11), ?_⟩
    show (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 1 1 - (1 : Matrix (Fin 2) (Fin 2) R) 1 1 = _
    rw [a11, Matrix.one_apply_eq]
    linear_combination t * h10 + h11 + q10 + p11

end UpperTheory.OrderAdditiveConjugation

open UpperTheory.OrderAdditiveConjugation in
theorem UpperTheory.unipotent_conj_congruence_of_pow_five :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (L a : ℕ), 0 < L → (∀ w : H.P E, Valued.v (H.cp w (rt ((L : E) * D.θ))) ≤ 1) → ∀ κ : GL (Fin 2) (A E), CongE (L ^ 5) κ → CongE L ((nu D ((a : A ℚ) * iota L))⁻¹ * κ * nu D ((a : A ℚ) * iota L)) := by
  intro E _ _ D L a hL hT κ hκ
  obtain ⟨t, htd⟩ : ∃ t, t = D.mkE 0 ((a : A ℚ) * iota L) := ⟨_, rfl⟩
  obtain ⟨ν, hνd⟩ : ∃ ν, ν = nu D ((a : A ℚ) * iota L) := ⟨_, rfl⟩
  rw [← hνd]
  have hν : (ν : Matrix (Fin 2) (Fin 2) (A E)) = !![1, t; 0, 1] := by rw [hνd, htd]; rfl
  have hνi : ((ν⁻¹ : GL (Fin 2) (A E)) : Matrix (Fin 2) (Fin 2) (A E)) = !![1, -t; 0, 1] := by
    rw [Matrix.coe_units_inv, hν]
    apply Matrix.inv_eq_right_inv
    simp [Matrix.one_fin_two]
  have ht : t = (a : A E) * am E (iota L) * UpperTheory.ConvolutionTheory.R2.rt D.θ := by
    rw [htd, Dat.mkE_def, map_zero, map_mul, map_natCast, zero_add]
  obtain ⟨T, hTd⟩ : ∃ T : A E, T = UpperTheory.ConvolutionTheory.R2.rt ((L : E) * D.θ) := ⟨_, rfl⟩
  have hT' : ∀ w : H.P E, Valued.v (H.cp w T) ≤ 1 := by rw [hTd]; exact hT
  have hTe : T = (L : A E) * UpperTheory.ConvolutionTheory.R2.rt D.θ := by rw [hTd, rt_mul_nat]
  have key : ∀ r ∈ Oh E, (L : A E) ^ 2 * t * r = (a : A E) * (T * r) := by
    intro r hr
    have hu := unit_mul L hL hr
    rw [ht, hTe]
    linear_combination ((a : A E) * ((L : A E) * UpperTheory.ConvolutionTheory.R2.rt D.θ)) * hu
  have main := conj_entry (Oh E) (L : A E) t oh_add oh_neg
    (fun r => ((L ^ 4 : ℕ) : A E) * r)
    (fun r => ((L ^ 2 * a : ℕ) : A E) * (T * r))
    (fun r => ((a ^ 2 : ℕ) : A E) * (T * (T * r)))
    (fun r hr => oh_nat _ hr)
    (fun r hr => oh_nat _ (oh_mul_of hT' hr))
    (fun r hr => oh_nat _ (oh_mul_of hT' (oh_mul_of hT' hr)))
    (fun r _ => by push_cast; ring)
    (fun r hr => by
      have := key r hr
      push_cast
      linear_combination (L : A E) ^ 3 * this)
    (fun r hr => by
      have h1 := key r hr
      have h2 := key (T * r) (oh_mul_of hT' hr)
      push_cast
      linear_combination ((L : A E) ^ 3 * t) * h1 + ((L : A E) * (a : A E)) * h2)
  have cast5 : ∀ {x : A E} {c : A E}, x = ((L ^ 5 : ℕ) : A E) * c → x = (L : A E) ^ 5 * c := by
    intro x c h; rw [h, Nat.cast_pow]
  have hinv : (ν⁻¹ * κ * ν)⁻¹ = ν⁻¹ * κ⁻¹ * ν := by group
  intro i j
  constructor
  · obtain ⟨c, hc, e⟩ := main (κ : Matrix (Fin 2) (Fin 2) (A E))
      (fun i j => by
        obtain ⟨c, hc, e⟩ := (hκ i j).1
        exact ⟨c, hc, cast5 e⟩) i j
    refine ⟨c, hc, ?_⟩
    rw [← e, Units.val_mul, Units.val_mul, hν, hνi]
  · obtain ⟨c, hc, e⟩ := main ((κ⁻¹ : GL (Fin 2) (A E)) : Matrix (Fin 2) (Fin 2) (A E))
      (fun i j => by
        obtain ⟨c, hc, e⟩ := (hκ i j).2
        exact ⟨c, hc, cast5 e⟩) i j
    refine ⟨c, hc, ?_⟩
    rw [← e, hinv, Units.val_mul, Units.val_mul, hν, hνi]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder
open scoped ValuativeRel

private theorem mem_int_iff {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (x : v.adicCompletion K) : x ∈ 𝒪[v.adicCompletion K] ↔ Valued.v x ≤ 1 := by
  rw [Valuation.mem_integer_iff]
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (v.adicCompletion K)) Valued.v).le_one_iff_le_one

private theorem inv_entry_int (v : H.P ℚ) (g : GL (Fin 2) (A ℚ)) (h : H.KAt v g) (i j : Fin 2) :
    Valued.v (((g⁻¹).val i j).2 v) ≤ 1 := by
  have h1 : Matrix.GeneralLinearGroup.map (H.cp v) g ∈ GroundTheory.Automorphic.GLnLocal.integralGL (v.adicCompletion ℚ) 2 := by
    rw [← PositivityTheory.JacquetShalikaLocal.SatakeEigenvalues.KGL_eq]
    exact h
  have h2 := ((GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff _ _).1 h1).2 i j
  rw [← map_inv] at h2
  exact (mem_int_iff v _).1 h2

private theorem div_of_dv (N : ℕ) (hN : 0 < N) (x : A ℚ) (h1 : x.1 = 0) (h2 : ∀ v, Dv N v x) :
    ∃ c ∈ Oh ℚ, x = (N : A ℚ) * c := by
  have hcp : ∀ v : H.P ℚ, ((N : A ℚ)).2 v = (N : H.Kv v) := fun v => map_natCast (H.cp v) N
  have hio : ∀ v : H.P ℚ, (iota N).2 v = (N : H.Kv v)⁻¹ := by
    intro v
    have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have h0 : (iota N).2 * (N : FiniteAdeleRing (𝓞 ℚ) ℚ) = 1 := by
      change algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (N : ℚ)⁻¹ * (N : FiniteAdeleRing (𝓞 ℚ) ℚ) = 1
      rw [← map_natCast (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)), ← map_mul, inv_mul_cancel₀ hN', map_one]
    have h3 := congrArg (pLoc ℚ v) h0
    rw [map_mul, map_natCast, map_one] at h3
    exact eq_inv_of_mul_eq_one_left h3
  have hne : ∀ v : H.P ℚ, (N : H.Kv v) ≠ 0 := by
    intro v
    have : CharZero (H.Kv v) := algebraRat.charZero _
    exact Nat.cast_ne_zero.2 hN.ne'
  refine ⟨x * iota N, ⟨?_, fun v => ?_⟩, ?_⟩
  · change x.1 * (iota N).1 = 0
    rw [h1, zero_mul]
  · change Valued.v (x.2 v * (iota N).2 v) ≤ 1
    rw [hio, map_mul, map_inv₀]
    have hv : Valued.v (N : H.Kv v) ≠ 0 := (Valuation.ne_zero_iff _).2 (hne v)
    exact mul_inv_le_one_of_le₀ (h2 v) zero_le'
  · refine Prod.ext ?_ (FiniteAdeleRing.ext (K := ℚ) fun v => ?_)
    · change x.1 = (N : A ℚ).1 * (x.1 * (iota N).1)
      rw [h1, zero_mul, mul_zero]
    · change x.2 v = (N : A ℚ).2 v * (x.2 v * (iota N).2 v)
      rw [hcp, hio]
      field_simp [hne v]

private theorem oh_add {K : Type} [Field K] [NumberField K] {a b : A K} (ha : a ∈ Oh K) (hb : b ∈ Oh K) :
    a + b ∈ Oh K := by
  refine ⟨?_, fun v => ?_⟩
  · change a.1 + b.1 = 0
    rw [ha.1, hb.1, add_zero]
  · change Valued.v (a.2 v + b.2 v) ≤ 1
    exact (Valuation.map_add _ _ _).trans (max_le (ha.2 v) (hb.2 v))

private theorem oh_neg {K : Type} [Field K] [NumberField K] {a : A K} (ha : a ∈ Oh K) : -a ∈ Oh K := by
  refine ⟨?_, fun v => ?_⟩
  · change -a.1 = 0
    rw [ha.1, neg_zero]
  · change Valued.v (-(a.2 v)) ≤ 1
    rw [Valuation.map_neg]
    exact ha.2 v

private theorem oh_mul (a c : A ℚ) (ha : ∀ v : H.P ℚ, Valued.v (a.2 v) ≤ 1) (hc : c ∈ Oh ℚ) : a * c ∈ Oh ℚ := by
  refine ⟨?_, fun v => ?_⟩
  · change a.1 * c.1 = 0
    rw [hc.1, mul_zero]
  · change Valued.v (a.2 v * c.2 v) ≤ 1
    rw [map_mul]
    exact mul_le_one' (ha v) (hc.2 v)

private theorem oh_map (E : Type) [Field E] [NumberField E] {c : A ℚ} (hc : c ∈ Oh ℚ) :
    AdeleBaseChange.adeleMap ℚ E c ∈ Oh E := by
  refine ⟨?_, fun w => ?_⟩
  · have : (AdeleBaseChange.adeleMap ℚ E c).1 =
        GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := ℚ) (L := E) c.1 := rfl
    rw [this, hc.1]
    exact map_zero _
  · rw [GroundTheory.BlockD.ThmBHecke.adeleMap_snd_apply, GroundTheory.Global.SemiLocal.valued_completionMap]
    exact pow_le_one' (hc.2 _) _

private theorem entry_map (E : Type) [Field E] [NumberField E] (N : ℕ) (g : GL (Fin 2) (A ℚ)) (i j : Fin 2)
    (h : ∃ c ∈ Oh ℚ, g.val i j - (1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j = (N : A ℚ) * c) :
    ∃ c ∈ Oh E, (em E g).val i j - (1 : Matrix (Fin 2) (Fin 2) (A E)) i j = (N : A E) * c := by
  obtain ⟨c, hc, h⟩ := h
  refine ⟨AdeleBaseChange.adeleMap ℚ E c, oh_map E hc, ?_⟩
  have h1 : (em E g).val i j = AdeleBaseChange.adeleMap ℚ E (g.val i j) := rfl
  have h2 : (1 : Matrix (Fin 2) (Fin 2) (A E)) i j =
      AdeleBaseChange.adeleMap ℚ E ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j) := by
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.one_apply_eq, map_one]
    · simp only [Matrix.one_apply_ne hij, map_zero]
  rw [h1, h2, ← map_sub, h, map_mul, map_natCast]

theorem UpperTheory.baseChangeGL2_congruence_of_level :
    ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 0 < N → ∀ k : GL (Fin 2) (A ℚ), Lev N k → CongE N (em E k) := by
  intro E _ _ N hN k hk
  have hk1 : ∀ i j, ∃ c ∈ Oh ℚ, k.val i j - (1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j = (N : A ℚ) * c := by
    intro i j
    refine div_of_dv N hN _ ?_ fun v => (hk.2 v).2 i j
    change (k.val i j).1 - ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j).1 = 0
    rw [hk.1 i j, sub_self]
  choose c hc hkc using hk1
  have hk2 : ∀ i j, ∃ d ∈ Oh ℚ, (k⁻¹).val i j - (1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j = (N : A ℚ) * d := by
    intro i j
    have hint : ∀ l, (k⁻¹).val i l * c l j ∈ Oh ℚ := fun l =>
      oh_mul _ _ (fun v => inv_entry_int v k (hk.2 v).1 i l) (hc l j)
    refine ⟨-((k⁻¹).val i 0 * c 0 j + (k⁻¹).val i 1 * c 1 j), oh_neg (oh_add (hint 0) (hint 1)), ?_⟩
    have hm : (k⁻¹).val * k.val = 1 := by
      have := congrArg Units.val (inv_mul_cancel k)
      simpa using this
    have hs : ((k⁻¹).val * (k.val - 1)) i j = (1 - (k⁻¹).val) i j := by
      rw [Matrix.mul_sub, hm, Matrix.mul_one]
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.sub_apply, Matrix.sub_apply,
      hkc 0 j, hkc 1 j] at hs
    linear_combination hs
  intro i j
  refine ⟨entry_map E N k i j ⟨c i j, hc i j, hkc i j⟩, ?_⟩
  rw [← map_inv]
  exact entry_map E N k⁻¹ i j (hk2 i j)
end
