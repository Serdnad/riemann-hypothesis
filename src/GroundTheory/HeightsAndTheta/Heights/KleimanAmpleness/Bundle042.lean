module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle034
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle026
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PHilbDegreeBound
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle044
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle039
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart CechC)

noncomputable section

section Lemmas

variable {F : Type} [Field F] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)]

attribute [local instance] MvPolynomial.weightedGradedAlgebra


omit [LinearOrder K] [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] in
theorem snapper_component_mul_X [DecidableEq K] (f : MvPolynomial (Σ k, ι k) F) (b : K → ℕ) (v : Σ k, ι k) :
    weightedHomogeneousComponent (NumbersDVR.blockWeight ι) (b + NumbersDVR.blockWeight ι v) (f * X v) =
      weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f * X v := by
  have h := DirectSum.coe_decompose_mul_add_of_right_mem
    (weightedHomogeneousSubmodule F (NumbersDVR.blockWeight ι)) (a := f) (i := b)
    (isWeightedHomogeneous_X F (NumbersDVR.blockWeight ι) v)
  have key : ∀ (φ : MvPolynomial (Σ k, ι k) F) (c : K → ℕ),
      (DirectSum.decompose (weightedHomogeneousSubmodule F (NumbersDVR.blockWeight ι)) φ c :
        MvPolynomial (Σ k, ι k) F) = weightedHomogeneousComponent (NumbersDVR.blockWeight ι) c φ :=
    fun φ c => weightedDecomposition.decompose'_apply F (NumbersDVR.blockWeight ι) φ c
  rw [key, key] at h
  exact h


omit [LinearOrder K] [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] in
theorem snapper_colon_X [DecidableEq K] {J : Ideal (MvPolynomial (Σ k, ι k) F)} (hJ : NumbersDVR.IsMultiHomogIdeal J)
    (v : Σ k, ι k) : NumbersDVR.IsMultiHomogIdeal (J.colon (Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)})) := by
  intro f hf b
  rw [Submodule.mem_colon_span_singleton, smul_eq_mul] at hf ⊢
  rw [← snapper_component_mul_X]
  exact hJ _ hf _


omit [Fintype K] [LinearOrder K] in
theorem snapper_eval_shift (p : MvPolynomial K ℚ) (e m : K → ℤ) :
    eval (fun k => ((m - e) k : ℚ)) p =
      eval (fun k => (m k : ℚ)) (bind₁ (fun j => X j - C ((e j : ℤ) : ℚ)) p) := by
  have hb : ∀ (x : K → ℚ) (g : K → MvPolynomial K ℚ), eval x (bind₁ g p) = eval (fun j => eval x (g j)) p :=
    fun x g => eval₂Hom_bind₁ _ _ _ _
  rw [hb]
  refine congrArg (fun x => eval x p) (funext fun j => ?_)
  simp

theorem snapper_top (V : Ideal (MvPolynomial (Σ k, ι k) F)) (m : K → ℤ) (n : ℕ)
    (hn : ∑ k, (Fintype.card (ι k) - 1) < n) : Subsingleton (cechHc ι (quotPart F V) m n) := by
  have hI : ∀ I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n, False := fun I => by
    have h1 : ∑ k, ((I.1 k).card - 1) ≤ ∑ k, (Fintype.card (ι k) - 1) :=
      Finset.sum_le_sum fun k _ => Nat.sub_le_sub_right (Finset.card_le_univ _) 1
    have := I.2.2
    omega
  have : Subsingleton (CechC F ι (MvPolynomial (Σ k, ι k) F ⧸ V) n) :=
    ⟨fun f g => funext fun I => (hI I).elim⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [Subsingleton.elim x y]

theorem snapper_finite (hS : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.TheoremSStatement) (V : Ideal (MvPolynomial (Σ k, ι k) F))
    (hV : NumbersDVR.IsMultiHomogIdeal V) (m : K → ℤ) (i : ℕ) :
    FiniteDimensional F (cechHc ι (quotPart F V) m i) :=
  (hS F K ι (MvPolynomial (Σ k, ι k) F ⧸ V) (quotPart F V) inferInstance inferInstance
    (HilbertSamuel.QuotPartGraded.proof F K ι V ((NumbersDVR.Objects.isMultiHomogIdeal_iff V).1 hV))).1 m i

end Lemmas

theorem EulerPoly.proof (hS : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.TheoremSStatement) (hE : EulerVar.Statement)
    (hD : PolyOfDiffsExact.Statement) : EulerPoly.Statement := by
  intro F _ K _ _ ι _ _ V hV
  have hfin : ∀ J : Ideal (MvPolynomial (Σ k, ι k) F), NumbersDVR.IsMultiHomogIdeal J →
      ∀ (m : K → ℤ) (i : ℕ), FiniteDimensional F (cechHc ι (quotPart F J) m i) :=
    fun J hJ => snapper_finite hS J hJ
  have key : ∀ J : Ideal (MvPolynomial (Σ k, ι k) F), NumbersDVR.IsMultiHomogIdeal J →
      ∃ p : MvPolynomial K ℚ, ∀ m, eulerChar F ι J m = eval (fun k => (m k : ℚ)) p := by
    intro J hJ
    refine IsNoetherian.induction (P := fun J : Ideal (MvPolynomial (Σ k, ι k) F) =>
      NumbersDVR.IsMultiHomogIdeal J → ∃ p : MvPolynomial K ℚ, ∀ m, eulerChar F ι J m = eval (fun k => (m k : ℚ)) p)
      (fun J ih hJ => ?_) J hJ
    have hlt2 : ∀ v : Σ k, ι k, (X v : MvPolynomial (Σ k, ι k) F) ∉ J →
        J < J ⊔ Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)} := fun v hvJ =>
      lt_of_le_of_ne le_sup_left fun h => hvJ (h ▸ Ideal.mem_sup_right (Ideal.subset_span rfl))
    have hSup : ∀ v : Σ k, ι k, NumbersDVR.IsMultiHomogIdeal (J ⊔ Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)}) :=
      fun v => FieldNumbers.isMultiHomogIdeal_sup_span hJ (isWeightedHomogeneous_X F (NumbersDVR.blockWeight ι) v)
    by_cases hA : ∃ v : Σ k, ι k, (X v : MvPolynomial (Σ k, ι k) F) ∉ J ∧
        J.colon (Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)}) ≠ J
    · obtain ⟨v, hvJ, hne⟩ := hA
      have hle : J ≤ J.colon (Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)}) := fun f hf => by
        rw [Submodule.mem_colon_span_singleton, smul_eq_mul]
        exact Ideal.mul_mem_right _ J hf
      obtain ⟨p1, hp1⟩ := ih _ (lt_of_le_of_ne hle (Ne.symm hne)) (snapper_colon_X hJ v)
      obtain ⟨p2, hp2⟩ := ih _ (hlt2 v hvJ) (hSup v)
      refine ⟨bind₁ (fun j => X j - C (((Pi.single v.1 1 : K → ℤ) j : ℤ) : ℚ)) p1 + p2, fun m => ?_⟩
      rw [hE F K ι J v hJ (hfin J hJ) (hfin _ (snapper_colon_X hJ v)) (hfin _ (hSup v)) m, hp1, hp2, map_add (f := _),
        ← snapper_eval_shift]
    · push Not at hA
      by_cases hB : ∃ k, ∀ i, (X ⟨k, i⟩ : MvPolynomial (Σ k, ι k) F) ∈ J
      · obtain ⟨k, hk⟩ := hB
        refine ⟨0, fun m => ?_⟩
        rw [map_zero, eulerChar]
        refine Finset.sum_eq_zero fun i _ => ?_
        have := cechHc_subsingleton_of_block hk m i
        rw [Module.finrank_zero_of_subsingleton]
        simp
      · push Not at hB
        refine hD K (eulerChar F ι J) fun k => ?_
        obtain ⟨i, hi⟩ := hB k
        obtain ⟨q, hq⟩ := ih _ (hlt2 ⟨k, i⟩ hi) (hSup ⟨k, i⟩)
        refine ⟨q, fun m => ?_⟩
        have h := hE F K ι J ⟨k, i⟩ hJ (hfin J hJ) (hfin _ (snapper_colon_X hJ _)) (hfin _ (hSup _)) m
        rw [hA _ hi] at h
        rw [← hq m]
        linarith
  obtain ⟨p, hp⟩ := key V hV
  exact ⟨∑ k, (Fintype.card (ι k) - 1), p, hfin V hV, fun m i hi => snapper_top V m i hi, hp⟩

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)

noncomputable section

namespace ChartKernel

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type}

abbrev blockDeg (e : (Σ k, ι k) →₀ ℕ) : K →₀ ℕ := e.mapDomain Sigma.fst

theorem prod_block_pow {R : Type} [CommMonoid R] (e : (Σ k, ι k) →₀ ℕ) (v : K → R) :
    (e.prod fun p n => v p.1 ^ n) = ∏ k, v k ^ blockDeg e k := by
  have h := Finsupp.prod_mapDomain_index (f := Sigma.fst) (s := e) (h := fun k n => v k ^ n)
    (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)
  exact h.symm.trans (Finsupp.prod_fintype _ _ (fun _ => pow_zero _))


omit [Fintype K] in
theorem blockDeg_le_totalDegree (g : MvPolynomial (Σ k, ι k) S) :
    ∀ e ∈ g.support, ∀ k, blockDeg e k ≤ g.totalDegree := by
  intro e he k
  refine le_trans ?_ (le_totalDegree he)
  rw [← Finsupp.sum_mapDomain_index (h := fun _ n => n) (fun _ => rfl) (fun _ _ _ => rfl)]
  by_cases hk : k ∈ (blockDeg e).support
  · exact Finset.single_le_sum (f := fun k => blockDeg e k) (fun _ _ => Nat.zero_le _) hk
  · rw [Finsupp.notMem_support_iff.mp hk]; exact Nat.zero_le _

def homog (c : ∀ k, ι k) (D : ℕ) (g : MvPolynomial (Σ k, ι k) S) : MvPolynomial (Σ k, ι k) S :=
  ∑ e ∈ g.support, monomial e (AddMonoidAlgebra.coeff g e) * ∏ k, X ⟨k, c k⟩ ^ (D - blockDeg e k)

variable {Ω : Type} [Field Ω] [Algebra S Ω]

theorem mConeMapOver_monomial (y : (Σ k, ι k) → Ω) (e : (Σ k, ι k) →₀ ℕ) (a : S) :
    mConeMapOver S y (monomial e a) = C (aeval y (monomial e a)) * ∏ k, X k ^ blockDeg e k := by
  simp only [mConeMapOver, aeval_monomial, mul_pow, Finsupp.prod_mul]
  rw [prod_block_pow e (fun k => (X k : MvPolynomial K Ω))]
  simp only [Finsupp.prod, map_mul, map_prod, map_pow, MvPolynomial.algebraMap_apply]
  ring

theorem mConeMapOver_homog (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {D : ℕ} {g : MvPolynomial (Σ k, ι k) S}
    (hD : ∀ e ∈ g.support, ∀ k, blockDeg e k ≤ D) :
    mConeMapOver S y (homog c D g) = C (aeval y (homog c D g)) * ∏ k, X k ^ D := by

  simp only [homog, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun e he => ?_
  have hX : ∏ k, (X k : MvPolynomial K Ω) ^ D =
      (∏ k, X k ^ blockDeg e k) * ∏ k, X k ^ (D - blockDeg e k) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [← pow_add, Nat.add_sub_cancel' (hD e he k)]
  rw [map_mul, mConeMapOver_monomial, hX]
  simp only [map_mul, map_prod, map_pow, mConeMapOver, aeval_X, mul_pow, Finset.prod_mul_distrib]
  ring

theorem aeval_homog (w : (Σ k, ι k) → Ω) {c : ∀ k, ι k} (hw : ∀ k, w ⟨k, c k⟩ ≠ 0) {D : ℕ}
    {g : MvPolynomial (Σ k, ι k) S} (hD : ∀ e ∈ g.support, ∀ k, blockDeg e k ≤ D) :
    aeval w (homog c D g) = (∏ k, w ⟨k, c k⟩ ^ D) * aeval (fun p => w p / w ⟨p.1, c p.1⟩) g := by
  conv_rhs => rw [g.as_sum]

  simp only [homog, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hP : ∏ k, w ⟨k, c k⟩ ^ D =
      (∏ k, w ⟨k, c k⟩ ^ (D - blockDeg e k)) * ∏ k, w ⟨k, c k⟩ ^ blockDeg e k := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [← pow_add, Nat.sub_add_cancel (hD e he k)]
  have hne : ∏ k, w ⟨k, c k⟩ ^ blockDeg e k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hw k)
  have hq : (e.prod fun p n => (w p / w ⟨p.1, c p.1⟩) ^ n) =
      (e.prod fun p n => w p ^ n) / ∏ k, w ⟨k, c k⟩ ^ blockDeg e k := by
    rw [← prod_block_pow e (fun k => w ⟨k, c k⟩)]
    simp only [Finsupp.prod, div_pow, Finset.prod_div_distrib]
  rw [map_mul, aeval_monomial, aeval_monomial, hq, hP]
  simp only [map_prod, map_pow, aeval_X]
  field_simp

end ChartKernel

theorem ChartKernel.proof : ChartKernel.Statement := by
  intro S _ K _ _ ι Ω _ _ y Ω' _ _ y' hle c hc g hg
  classical
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hc k (by
    have hm : (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) S) ∈ mIdealOver S y := by
      change mConeMapOver S y (X _) = 0
      simp [mConeMapOver, h0]
    have h' : mConeMapOver S y' (X ⟨k, c k⟩) = 0 := hle hm
    simpa [mConeMapOver, X_ne_zero] using h')
  have hD := ChartKernel.blockDeg_le_totalDegree g
  have h1 : aeval y (ChartKernel.homog c g.totalDegree g) = 0 := by
    rw [ChartKernel.aeval_homog y hyc hD, hg, mul_zero]
  have h2 : ChartKernel.homog c g.totalDegree g ∈ mIdealOver S y := by
    change mConeMapOver S y _ = 0
    rw [ChartKernel.mConeMapOver_homog y c hD, h1, map_zero, zero_mul]
  have h3 : mConeMapOver S y' (ChartKernel.homog c g.totalDegree g) = 0 := hle h2
  rw [ChartKernel.mConeMapOver_homog y' c hD] at h3
  have h4 : aeval y' (ChartKernel.homog c g.totalDegree g) = 0 := by
    rcases mul_eq_zero.mp h3 with h | h
    · exact C_eq_zero.mp h
    · exact absurd h (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k))
  rw [ChartKernel.aeval_homog y' hc hD] at h4
  exact (mul_eq_zero.mp h4).resolve_left (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k))

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
