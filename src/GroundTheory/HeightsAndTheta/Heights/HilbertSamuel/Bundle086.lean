module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle042
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle076
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle054
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SupBoundCountLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageHilb
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SupBoundCountIntegrals

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial BlockImageHilb

noncomputable section

namespace PullConeDegreeInt

section Lemmas

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem isWeightedHomogeneous_of_isMultiHomog {f : MRing ι} {a : K → ℕ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a := by
  intro m hm
  funext k
  rw [weight_blockWeight_apply]
  exact hf m (mem_support_iff.mpr hm) k

theorem isMultiHomog_of_isWeightedHomogeneous {f : MRing ι} {a : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a := by
  intro m hm k
  rw [← weight_blockWeight_apply, hf (mem_support_iff.mp hm)]

theorem mConeMap_eq (y : (Σ k, ι k) → Ω) {f : MRing ι} {a : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a) :
    mConeMap y f = MvPolynomial.C (aeval y f) * ∏ k, MvPolynomial.X k ^ a k := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]

  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hX : ∏ p : (Σ k, ι k), (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ μ p = ∏ k, MvPolynomial.X k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (MvPolynomial.X k : MvPolynomial K Ω) ^ μ ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, ← weight_blockWeight_apply, hf (mem_support_iff.mp hμ)]
  simp only [mConeMap, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow, MvPolynomial.algebraMap_apply]
  ring

theorem coeff_mConeMap (y : (Σ k, ι k) → Ω) (f : MRing ι) (n : K → ℕ) :
    AddMonoidAlgebra.coeff (mConeMap y f) (Finsupp.equivFunOnFinite.symm n) =
      aeval y (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) n f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial m r =>
    have hm := isWeightedHomogeneous_monomial (NumbersDVR.blockWeight ι) m r rfl
    rw [mConeMap_eq y hm, PullConeDegree.prod_X_pow_eq_monomial, C_mul_monomial, mul_one, coeff_monomial,
      weightedHomogeneousComponent_of_mem (n := Finsupp.weight (NumbersDVR.blockWeight ι) m) hm]
    by_cases h : n = Finsupp.weight (NumbersDVR.blockWeight ι) m
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun h' => h (Finsupp.equivFunOnFinite.symm.injective h').symm), map_zero]
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, hp, hq, map_add (f := _), map_add (f := _)]


omit [DecidableEq K] in
theorem exists_dvd_monomial (N : ℕ) (hne : ∀ k, Nonempty (ι k)) (μ : (Σ k, ι k) →₀ ℕ)
    (hμ : ∀ k, N * Fintype.card (ι k) ≤ ∑ i, μ ⟨k, i⟩) (r : ℤ) :
    ∃ c : ∀ k, ι k, (∏ k, (X ⟨k, c k⟩ : MRing ι)) ^ N ∣ monomial μ r := by
  have hc : ∀ k, ∃ i, N ≤ μ ⟨k, i⟩ := by
    intro k
    by_contra h
    simp only [not_exists, not_le] at h
    have hlt := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty (α := ι k)) (fun i _ => h i)
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm] at hlt
    exact absurd (hμ k) (not_le.mpr hlt)
  choose c hc using hc
  refine ⟨c, ?_⟩
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun i => by simp), Fintype.prod_sigma, ← Finset.prod_pow]
  refine Dvd.dvd.mul_left (Finset.prod_dvd_prod_of_dvd _ _ fun k _ => ?_) _
  exact (pow_dvd_pow _ (hc k)).trans
    (Finset.dvd_prod_of_mem (fun i => (X ⟨k, i⟩ : MRing ι) ^ μ ⟨k, i⟩) (Finset.mem_univ (c k)))

end Lemmas

theorem proof : PullConeDegreeInt.Statement := by
  classical
  intro K _ ι _ Ω _ y D e L N M hy hL hN d g hg hd
  have hne : ∀ k, Nonempty (ι k) := fun k => (hy k).elim fun i _ => ⟨i⟩
  have hg' := isWeightedHomogeneous_of_isMultiHomog hg

  have hgI : (M : MRing ι) * g ∈ coneNullIdealZ y L := by
    rw [g.as_sum, Finset.mul_sum]
    refine Ideal.sum_mem _ fun μ hμ => ?_
    obtain ⟨c, hc⟩ := exists_dvd_monomial N hne μ
      (fun k => by rw [hg μ hμ k]; have := hd k; omega) (AddMonoidAlgebra.coeff g μ)
    exact Ideal.mem_of_dvd _ (mul_dvd_mul_left _ hc) (hN c)
  have hI : coneNullIdealZ y L = RingHom.ker (mConeMap y) ⊔ Ideal.span (Set.range L) := by
    rw [coneNullIdealZ, Ideal.span_union, Ideal.span_eq]
    rfl
  rw [hI, Submodule.mem_sup] at hgI
  obtain ⟨u, hu, v, hv, huv⟩ := hgI
  obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp hv

  have hmapL : ∀ j, mConeMap y (L j) = monomial (Finsupp.equivFunOnFinite.symm e) (aeval y (L j)) := by
    intro j
    rw [mConeMap_eq y (isWeightedHomogeneous_of_isMultiHomog (hL j)), PullConeDegree.prod_X_pow_eq_monomial,
      C_mul_monomial, mul_one]
  have hMg : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) ((M : MRing ι) * g) d := by
    have h := (isWeightedHomogeneous_C (NumbersDVR.blockWeight ι) (M : ℤ)).mul hg'
    rw [zero_add, map_natCast] at h
    exact h
  have hψg : mConeMap y ((M : MRing ι) * g) =
      ∑ j, mConeMap y (b j) * monomial (Finsupp.equivFunOnFinite.symm e) (aeval y (L j)) := by

    rw [← huv, map_add (f := _), RingHom.mem_ker.mp hu, zero_add, ← hb, map_sum]
    simp only [map_mul, hmapL]

  refine ⟨fun j => weightedHomogeneousComponent (NumbersDVR.blockWeight ι) (d - e) (b j),
    fun j => isMultiHomog_of_isWeightedHomogeneous (weightedHomogeneousComponent_isWeightedHomogeneous _ _), ?_⟩
  have hc := congrArg (AddMonoidAlgebra.coeff · (Finsupp.equivFunOnFinite.symm d)) hψg
  rw [mConeMap_eq y hMg, PullConeDegree.prod_X_pow_eq_monomial, C_mul_monomial, mul_one,
    coeff_monomial, if_pos rfl, coeff_sum, map_mul, map_natCast] at hc
  rw [hc]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hle : Finsupp.equivFunOnFinite.symm e ≤ Finsupp.equivFunOnFinite.symm d :=
    Finsupp.le_def.mpr fun k => by simp only [Finsupp.coe_equivFunOnFinite_symm]; have := hd k; omega
  have hsub : Finsupp.equivFunOnFinite.symm d - Finsupp.equivFunOnFinite.symm e =
      Finsupp.equivFunOnFinite.symm (d - e) := by
    ext k
    simp
  rw [coeff_mul_monomial', if_pos hle, hsub, coeff_mConeMap]

end PullConeDegreeInt

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace ShiftDegreePolynomial

def toMultilinear {K : Type} {n : ℕ} (f : (Fin n → K → ℤ) → ℤ)
    (hadd : ∀ (bs : Fin n → K → ℤ) (j : Fin n) (x y : K → ℤ),
      f (Function.update bs j (x + y)) = f (Function.update bs j x) + f (Function.update bs j y)) :
    MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => K → ℤ) ℤ where
  toFun := f
  map_update_add' := by
    intro inst m i x y
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    exact hadd m i x y
  map_update_smul' := by
    intro inst m i c x
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    exact (AddMonoidHom.mk' (fun x => f (Function.update m i x)) (hadd m i)).map_zsmul c x

theorem expand {K : Type} {n : ℕ} (f : (Fin n → K → ℤ) → ℤ)
    (hadd : ∀ (bs : Fin n → K → ℤ) (j : Fin n) (x y : K → ℤ),
      f (Function.update bs j (x + y)) = f (Function.update bs j x) + f (Function.update bs j y))
    (q : ℤ) (a b : K → ℤ) :
    f (fun _ => q • a + b) =
      ∑ s : Finset (Fin n), q ^ s.card * f (s.piecewise (fun _ => a) (fun _ => b)) := by
  have h1 := (toMultilinear f hadd).map_add_univ (fun _ => q • a) (fun _ => b)
  refine h1.trans (Finset.sum_congr rfl fun s _ => ?_)
  have h2 := (toMultilinear f hadd).map_piecewise_smul (fun _ => q)
    (s.piecewise (fun _ => a) (fun _ => b)) s
  have h3 : s.piecewise (fun i => q • s.piecewise (fun _ => a) (fun _ => b) i)
      (s.piecewise (fun _ => a) (fun _ => b)) = s.piecewise (fun _ => q • a) (fun _ => b) := by
    funext i
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  rw [h3, Finset.prod_const, RingHom.id_apply, smul_eq_mul] at h2
  exact h2

theorem genericFibre {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {D : ℕ} (hP : IsArithVar P (D + 1)) :
    GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiProjPrime (P.map (MvPolynomial.map (Int.castRingHom ℚ))) ∧
      ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸ P.map (MvPolynomial.map (Int.castRingHom ℚ))) =
        ((D + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  obtain ⟨-, ⟨hPp, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  have : P.IsPrime := hPp
  have hchar : ∀ m : ℤ, (C m : MvPolynomial (Σ k, ι k) ℤ) ∈ P → m = 0 := by
    intro m hm
    have h1 : m ∈ P.comap (C : ℤ →+* MRing ι) := hm
    rw [show P.comap (C : ℤ →+* MRing ι) = ⊥ from hhor, Ideal.mem_bot] at h1
    exact h1
  obtain ⟨hqp, hcomap, hform⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hchar
  have hq : ReciprocityTheory.AnForm.R.extQ P = P.map (MvPolynomial.map (Int.castRingHom ℚ)) := rfl
  rw [← hq]
  refine ⟨⟨hqp, ?_, ?_⟩, ?_⟩
  · rw [GroundTheory.Heights₂.Heights.Bridge.isMultiHomogIdeal_iff]
    refine ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨b, hb⟩ := hS f hf
      exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
    · rw [hq, hPS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun hX => hi ?_⟩
    rw [← hcomap, Ideal.mem_comap, map_X]
    exact hX
  · rw [hdim] at hform
    refine GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreDim.eq_natCast_of_add_one_eq _ _ ?_
    rw [hform]
    push_cast
    ring

theorem proof (h : MixedNumberPolynomial.Statement.{0}) : ShiftDegreePolynomial.Statement := by
  classical
  intro K _ ι _ P D a b hP
  obtain ⟨hprime, hdimq⟩ := genericFibre hP
  set Q := P.map (MvPolynomial.map (Int.castRingHom ℚ)) with hQ
  have hadd := (h ℚ K ι Q D hprime hdimq).2
  let f : (Fin D → K → ℤ) → ℤ := fun bs => GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ Q bs
  let c : Finset (Fin D) → ℤ := fun s => f (s.piecewise (fun _ => a) (fun _ => b))
  refine ⟨∑ s : Finset (Fin D), Polynomial.C (c s : ℝ) * Polynomial.X ^ s.card, ?_, ?_, ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s _ => ?_
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    simpa using Finset.card_le_univ s
  · rw [Polynomial.finsetSum_coeff]
    simp_rw [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single Finset.univ]
    · simp [c, f, genDeg, hQ]
    · intro s _ hs
      rw [if_neg]
      intro hD
      apply hs
      rw [← Finset.card_eq_iff_eq_univ, Fintype.card_fin]
      exact hD.symm
    · intro hu
      exact absurd (Finset.mem_univ _) hu
  · intro q
    have hexp := expand f hadd (q : ℤ) a b
    have hg : genDeg P D ((q : ℤ) • a + b) = f (fun _ => (q : ℤ) • a + b) := rfl
    rw [hg, hexp, Polynomial.eval_finsetSum]
    push_cast
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [c, mul_comm]

end ShiftDegreePolynomial

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Matrix

noncomputable section

namespace SupBoundCount

theorem main {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (n : ℕ) {c : ℝ} (hc : 0 < c)
    (hsup : ∀ f : MRing ι, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f (blockDeg d.k₀ n) → ∀ z ∈ mcPts (mCoordIdeal d.y),
      ‖eval z (map (Int.castRingHom ℂ) f)‖ / d.A.h z ^ n ≤ c * blockL2Norm d n f)
    {r : ℕ} {b : Fin r → MvPolynomial (Σ k, ι k) ℚ} (hb : IsSecBasisM d.y d.k₀ n b) :
    (Module.finrank ℤ (secM d.y (blockDeg d.k₀ n)) : ℝ) ≤ 2 * c ^ 2 ∧
      -(1 / 2) * Real.log (blockGram d n b).det - (Module.finrank ℤ (secM d.y (blockDeg d.k₀ n)) : ℝ) *
          Real.log (c * Real.sqrt (Module.finrank ℤ (secM d.y (blockDeg d.k₀ n)))) ≤
        smallSectionCount (IsSmallH (mCoordIdeal d.y) d.y d.A) (fun τ => secM d.y (blockDeg d.k₀ τ)) n := by
  classical
  rw [finrank_secM hb]
  have hb' := hb
  choose f hf hbf using hb.1
  have hbe : b = fun j => map (Int.castRingHom ℚ) (f j) := funext hbf
  subst hbe
  have hli : LinearIndependent ℤ fun k => aeval d.y (f k) := by
    have := hb'.2.1
    simpa [aeval_map_int] using this
  have hG := gram_posDef d n f hf hli hc hsup
  refine ⟨rank_le d n f hf hli hc hsup, ?_⟩

  set Q : (Fin r → ℤ) → ℝ := fun m => (fun k => (m k : ℝ)) ⬝ᵥ
    (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ fun k => (m k : ℝ)) with hQ
  set P : (Fin r → ℤ) → Prop := fun m =>
    IsSmallH (mCoordIdeal d.y) d.y d.A n (aeval d.y (∑ k, m k • f k)) with hPdef
  have hP1 : ∀ m, Q m ≤ (1 / c) ^ 2 → P m := by
    intro m hm
    have hF := isMultiHomog_zsum f m hf
    refine (isSmallH_iff d n hF).2 fun z hz => ?_
    have h1 := hsup _ hF z hz
    rw [blockL2Norm_sum_eq_sqrt_gram d n f hf m] at h1
    have h2 : Real.sqrt (Q m) ≤ 1 / c := by
      calc Real.sqrt (Q m) ≤ Real.sqrt ((1 / c) ^ 2) := Real.sqrt_le_sqrt hm
        _ = 1 / c := Real.sqrt_sq (by positivity)
    have h3 : c * Real.sqrt (Q m) ≤ 1 := by
      calc c * Real.sqrt (Q m) ≤ c * (1 / c) := mul_le_mul_of_nonneg_left h2 hc.le
        _ = 1 := by field_simp
    have hp : 0 < d.A.h z ^ n := pow_pos (d.A.pos z hz.1) n
    exact (div_le_one hp).1 (h1.trans h3)
  have hP2 : ∀ m, P m → Q m ≤ 1 := by
    intro m hm
    have hF := isMultiHomog_zsum f m hf
    have h1 := blockL2Norm_le_one_of_sup_bound d n hF ((isSmallH_iff d n hF).1 hm)
    rw [blockL2Norm_sum_eq_sqrt_gram d n f hf m] at h1
    by_contra h
    push_neg at h
    have := Real.sqrt_lt_sqrt zero_le_one h
    rw [Real.sqrt_one] at this
    linarith
  obtain ⟨-, hcount⟩ := count_of_gram hG (by positivity : (0 : ℝ) < 1 / c) P hP1 hP2

  have hmem : ∀ m : Fin r → ℤ, aeval d.y (∑ k, m k • f k) ∈ secM d.y (blockDeg d.k₀ n) := by
    intro m
    rw [← hb'.2.2]

    simp only [map_sum, map_zsmul]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨k, by simp [aeval_map_int]⟩)
  have hinj : Function.Injective fun m : Fin r → ℤ => aeval d.y (∑ k, m k • f k) := by
    intro m m' h
    have h0 : ∑ k, (m k - m' k) • aeval d.y (f k) = 0 := by

      simp only [map_sum, map_zsmul] at h
      simp only [sub_smul, Finset.sum_sub_distrib]
      exact sub_eq_zero.2 h
    funext k
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h0 k)
  let E : {m // P m} → {s : secM d.y (blockDeg d.k₀ n) // IsSmallH (mCoordIdeal d.y) d.y d.A n (s : Ω)} :=
    fun m => ⟨⟨_, hmem m.1⟩, m.2⟩
  have hE : Function.Bijective E := by
    refine ⟨fun m m' h => Subtype.ext (hinj (congrArg (fun s => ((s.1 : secM d.y _) : Ω)) h)), ?_⟩
    rintro ⟨⟨s, hs⟩, hsm⟩
    have hs' := hs
    rw [← hb'.2.2] at hs'
    obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hs'
    have hms : aeval d.y (∑ k, m k • f k) = s := by
      rw [← hm]

      simp [map_sum, aeval_map_int]
    refine ⟨⟨m, ?_⟩, ?_⟩
    · show IsSmallH _ _ _ _ _
      rw [hms]
      exact hsm
    · exact Subtype.ext (Subtype.ext hms)
  have hcard := Nat.card_congr (Equiv.ofBijective E hE)
  simp only [smallSectionCount]
  rw [← hcard]

  have hV : (r : ℝ) * Real.log (2 / Real.sqrt r) ≤ Real.log (unitBallVolume r) := by
    have hpos : 0 < (2 / Real.sqrt r) ^ r := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · simp [h0]
      · exact pow_pos (div_pos two_pos (Real.sqrt_pos.2 (by exact_mod_cast h0))) r
    rw [← Real.log_pow]
    exact Real.log_le_log hpos (MinkowskiCount.cube_le_unitBallVolume r)
  have halg : (r : ℝ) * Real.log (2 / Real.sqrt r) + r * Real.log (1 / c / 2) =
      -((r : ℝ) * Real.log (c * Real.sqrt r)) := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · simp [h0]
    · have hs : 0 < Real.sqrt r := Real.sqrt_pos.2 (by exact_mod_cast h0)
      rw [← mul_add, ← Real.log_mul (by positivity) (by positivity)]
      have : 2 / Real.sqrt r * (1 / c / 2) = (c * Real.sqrt r)⁻¹ := by
        field_simp
      rw [this, Real.log_inv]
      ring
  linarith

end SupBoundCount

theorem SupBoundCount.proof : SupBoundCount.Statement := by
  intro D K _ _ ι _ Ω _ _ d n c hc hsup
  have hex := SupBoundCount.exists_isSecBasisM d.y d.k₀ n
  have h := SupBoundCount.main d n hc hsup hex.choose_spec
  refine ⟨h.1, ?_⟩
  rw [blockChi, dite_eq_left hex]
  exact h.2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
