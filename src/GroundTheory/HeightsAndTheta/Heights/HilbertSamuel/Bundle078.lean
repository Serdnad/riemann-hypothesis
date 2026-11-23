module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle054
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle037
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle069
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle072
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle057
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle053
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallGenTwist
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle032
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle064
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBoundedMul
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SmallSectionCountLeOfInjOn
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle045
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle034
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle058
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle071
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle065
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle066
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle015
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CSandwichStB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CSandwichStE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CSandwichStD

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem LiftAtPrime.proof (hC : GeneratedPow.Statement) (hA : FibreSectionLift.Statement)
    (hB : FibreRelLift.Statement) : LiftAtPrime.Statement := by
  classical
  intro K _ _ ι _ _ Ω _ _ y D N p hY hp hN
  obtain ⟨q, hq, hgen, hvan⟩ := hN
  obtain ⟨t₀, ht₀⟩ := hvan 0
  refine ⟨q, t₀, hq, fun t ht => ?_⟩
  have hga : KH.GeneratedV (ZMod p) (fibreIdeal p y) ((t * q) • N) := by
    have h := hC (ZMod p) K ι (fibreIdeal p y) (q • N) t hgen
    rwa [smul_smul] at h
  have hH1 : Subsingleton (KH.cechHc ι (KH.quotPart (ZMod p) (fibreIdeal p y)) ((t * q) • N) 1) := by
    have h := ht₀ t ht
    rwa [zero_add] at h
  have hfi : fibreIdeal p y = GenOnFibres.idealOver y (ZMod p) := rfl
  rw [hfi] at hga hH1
  choose r z u hz hu hrel using hga
  have hlift : ∀ I j, ∃ s ∈ chartLat y ((t * q) • N) 1,
      GenOnFibres.secCoch y (ZMod p) s ((t * q) • N) = z I j :=
    fun I j => hA K ι Ω y D p ((t * q) • N) hY hp hH1 (z I j) (hz I j)
  choose s hs hsz using hlift
  have : Finite (KH.Cell K ι 0) := by unfold KH.Cell; infer_instance
  have : Fintype (KH.Cell K ι 0) := Fintype.ofFinite _
  let e := (Fintype.equivFin (Σ I, Fin (r I))).symm
  refine ⟨Fintype.card (Σ I, Fin (r I)), fun j => s (e j).1 (e j).2, fun j => hs _ _, fun c hc => ?_⟩
  let J : KH.Cell K ι 0 := ⟨fun k => {c k}, fun k => Finset.singleton_nonempty _, by simp⟩
  have hJ : GenOnFibres.cellChart J = c :=
    funext fun k => Finset.mem_singleton.mp (GenOnFibres.cellChart_mem J k)
  have hrelJ : ∑ j, u J j * GenOnFibres.secCoch y (ZMod p) (s J j) ((t * q) • N) J = 1 := by
    rw [← hrel J]
    exact Finset.sum_congr rfl fun j _ => by rw [hsz J j]
  obtain ⟨u', v, hu', hv, hsum⟩ :=
    hB K ι Ω y p ((t * q) • N) (r J) (s J) J (u J) (hs J) (by rw [hJ]; exact hc) (hu J) hrelJ
  rw [hJ] at hu' hv hsum
  let U : (Σ I, Fin (r I)) → Ω := fun x => if h : x.1 = J then u' (Fin.cast (congrArg r h) x.2) else 0
  refine ⟨fun j => U (e j), v, fun j => ?_, hv, ?_⟩
  · simp only [U]
    split_ifs
    · exact hu' _
    · exact zero_mem _
  · rw [← hsum]
    congr 1
    rw [e.sum_comp (fun x => U x * (s x.1 x.2 * ∏ k, y ⟨k, c k⟩ ^ (-((t * q) • N) k))),
      Fintype.sum_sigma, Finset.sum_eq_single J]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp [U]
    · intro I _ hI
      exact Finset.sum_eq_zero fun j _ => by simp [U, hI]
    · intro h
      exact absurd (Finset.mem_univ J) h

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry SectionBoundedMul SmallGenTwist

noncomputable section

namespace PerturbedMonomialBound

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem chartMono_exponent (c : ∀ k, ι k) (d : K → ℕ) :
    ∃ μ : (Σ k, ι k) →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = d k) ∧
      ∀ z : (Σ k, ι k) → ℂ, ∏ p, z p ^ μ p = ∏ k, z ⟨k, c k⟩ ^ d k := by
  classical
  refine ⟨∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k), fun k => ?_, fun z => ?_⟩
  · simp only [Finsupp.finsetSum_apply]
    rw [Finset.sum_comm]
    simp only [sum_single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · have h : chartMono c d = monomial (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k)) (1 : ℤ) := by
      rw [chartMono, monomial_sum_one]
      exact Finset.prod_congr rfl fun k _ => X_pow_eq_monomial
    have e1 := eval_chartMono z c d
    rw [h, map_monomial, eval_monomial, Finsupp.prod_fintype _ _ (fun i => by simp)] at e1
    simpa using e1

theorem smallGen_of_monomialsBounded (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a : K → ℕ)
    (ha : A.a = fun k => (a k : ℤ)) (hB : MonomialsBounded (mCoordIdeal y) A a) : SmallGen y A := by
  classical
  set e := Fintype.equivFin (∀ k, ι k) with he_def
  refine ⟨Fintype.card (∀ k, ι k), fun j => aeval y (chartMono (e.symm j) a), fun j => ?_, ?_, fun j => ?_⟩
  · intro c hc
    beta_reduce
    rw [aeval_chartMono, ← Finset.prod_mul_distrib]
    refine prod_mem fun k _ => ?_
    have hmem : y ⟨k, (e.symm j) k⟩ / y ⟨k, c k⟩ ∈ chartRingZ y c :=
      Algebra.subset_adjoin ⟨⟨k, (e.symm j) k⟩, rfl⟩
    convert pow_mem hmem (a k) using 1
    simp [ha, div_eq_mul_inv, zpow_neg, zpow_natCast, mul_pow, inv_pow]
  · intro c hc
    refine ⟨fun j => if e.symm j = c then 1 else 0, fun j => by beta_reduce; split_ifs <;> simp, ?_⟩
    rw [Fintype.sum_equiv e.symm _ (fun i => (if i = c then (1 : Ω) else 0) *
      (aeval y (chartMono i a) * ∏ k, y ⟨k, c k⟩ ^ (-A.a k))) (fun _ => rfl)]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [aeval_chartMono, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => by
      simp [ha, zpow_neg, zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ (hc k))]
  · intro dg dh g h z hg hh hdeg he hz
    have hd : dg = a + dh := funext fun k => by
      have := hdeg k
      simp only [ha, Nat.cast_one, one_mul] at this
      simp only [Pi.add_apply]
      omega
    have hF : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (g - chartMono (e.symm j) a * h) dg :=
      isMultiHomog_sub hg (by rw [hd]; exact SectionBoundedMul.isMultiHomog_mul (isMultiHomog_chartMono _ a) hh)
    have h0 : aeval y (g - chartMono (e.symm j) a * h) = 0 := by
      rw [map_sub, map_mul, he, sub_self]
    have hz0 := hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hF h0)
    simp only [map_sub, map_mul, sub_eq_zero] at hz0
    rw [hz0, norm_mul, eval_chartMono, pow_one, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    obtain ⟨μ, hμ, hzμ⟩ := chartMono_exponent (e.symm j) a
    rw [← hzμ z]
    exact hB z hz μ hμ

end PerturbedMonomialBound


open PerturbedMonomialBound in
theorem PerturbMonomial.proof (hDeg : GenDegAmple.Statement) : PerturbMonomial.Statement := by
  intro K _ ι _ Ω _ y D a A P0 q _ hV _ ha hP0 hsemi hmono _
  have hBa : (HermLine.zcomb A (fsH ι) q 1).a = fun k => (q : ℤ) * a k + 1 := by
    funext k
    simp [HermLine.zcomb, ha, fsH_a]
  refine ⟨hP0, ?_, ?_, ?_⟩
  · exact PerturbSemipos.proof K ι P0 (mCoordIdeal y) A q 1 hsemi (by positivity) zero_le_one
  · rw [hBa]
    refine hDeg K ι Ω y D _ hV fun k => ?_
    have : (0 : ℤ) ≤ (q : ℤ) * a k := by positivity
    omega
  · have h := smallGen_zcomb y A (smallGen_of_monomialsBounded y A a ha hmono) q 1
    rw [Nat.cast_one] at h
    exact h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

namespace ScaledFSTopPos

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem geoNum_nonneg : ∀ (n : ℕ) (V : Ideal (MRing ι)) (a : Fin n → K → ℤ), (∀ j k, 0 ≤ a j k) →
    0 ≤ geoNum n V a
  | 0, V, a, _ => by
    unfold geoNum
    split_ifs <;> positivity
  | n + 1, V, a, ha => by
    unfold geoNum
    split_ifs with h
    · exact Finset.sum_nonneg fun k _ => mul_nonneg (ha _ _) (finsum_nonneg fun W => finsum_nonneg fun _ =>
        mul_nonneg (Nat.cast_nonneg _) (geoNum_nonneg n W _ fun j k => ha _ _))
    · exact le_rfl

theorem semipos_of_h_eq {P0 P : Ideal (MRing ι)} {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (h : A.h = B.h)
    (hA : IsSemipositiveRel P0 P A) : IsSemipositiveRel P0 P B := by
  unfold IsSemipositiveRel IsSmoothHerm at *
  rw [← h]
  exact hA

theorem semipos (P : Ideal (MRing ι)) : IsSemipositiveRel ⊥ P (scaledFSH ι) := by
  have hM : IsSemipositiveRel ⊥ P (constLine (ι := ι) 0) := by
    refine ⟨G5.isSmoothHerm_constLine 0, fun z _ w _ => ?_⟩
    simp [leviForm, constLine, HermLine.ofWeight]
  have hfs : IsSemipositiveRel ⊥ P (fsH ι) :=
    semipos_of_h_eq (funext fun z => by simp [HermLine.zcomb])
      (PerturbSemipos.proof K ι ⊥ P _ 0 1 hM le_rfl zero_le_one)
  exact semipos_of_h_eq rfl (Mono.semipos_constShift hfs (-1))

theorem logNorm_fsH_nonpos (c : ∀ k, ι k) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    logNorm (fsH ι) (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (fun _ : K => (1 : ℕ)) k) z ≤ 0 := by
  have hpos := (fsH ι).pos z hz
  have hH : ∏ k, ‖z ⟨k, c k⟩‖ ≤ (fsH ι).h z := by
    have hfs : (fsH ι).h z = ∏ k, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) := by
      rw [fsH, GroundTheory.Heights₂.Heights.Inter.ofMetrics_fs_h]
      simp
    rw [hfs]
    refine Finset.prod_le_prod₀ (fun k _ => norm_nonneg _) fun k _ => Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ (c k))
  unfold logNorm
  apply Real.log_nonpos (div_nonneg (norm_nonneg _) hpos.le)
  rw [div_le_one hpos]
  simpa [map_prod, norm_prod] using hH

theorem step (II : IntersectionSystem) (hII : IsIntersectionSystem II) (hG : FSGeomDegPos.Statement) (n : ℕ)
    (hlow : ∀ W : Ideal (MRing ι), IsArithVar W n → IsHorizontal W → 0 ≤ II K ι W n (fun _ => scaledFSH ι))
    (P : Ideal (MRing ι)) (hP : IsArithVar P (n + 1)) :
    0 < II K ι P (n + 1) (fun _ => scaledFSH ι) := by
  classical
  have hF := hII K ι
  set L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun _ => scaledFSH ι with hLdef
  have hHs : IsSmoothHerm (scaledFSH ι) := (semipos (ι := ι) ⊥).1
  have hFs : IsSmoothHerm (fsH ι) := GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs 1
  have hCs : IsSmoothHerm (constLine (ι := ι) (-1)) := G5.isSmoothHerm_constLine (-1)
  have hLs : ∀ j, IsSmoothHerm (L j) := fun _ => hHs
  have e0 : (fun _ : Fin (n + 1) => scaledFSH ι) = Fin.snoc L ((fsH ι).tensor (constLine (-1))) := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [L, scaledFSH]
  rw [e0, hF.2.1 P n L _ _ hP hLs hFs hCs]
  obtain ⟨c, hc⟩ : ∃ c : ∀ k, ι k, ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P :=
    ⟨fun k => (hP.2.1.2.2 k).choose, fun k => (hP.2.1.2.2 k).choose_spec⟩
  have hsH := GroundTheory.Heights₂.Heights.Inter.ThmIUnique.isMultiHomog_coordMonomial c (fun _ : K => (1 : ℕ))
  have hsP := GroundTheory.Heights₂.Heights.Inter.ThmIUnique.coordMonomial_not_mem hP.2.1.1 c hc (fun _ : K => (1 : ℕ))
  have hfa : ∀ k, (fsH ι).a k = ((fun _ : K => (1 : ℕ)) k : ℤ) := fun k => by simp [fsH, HermLine.ofMetrics]

  have hA : 0 ≤ II K ι P (n + 1) (Fin.snoc L (fsH ι)) := by
    rw [hF.2.2 P n L (fsH ι) _ _ hP hLs hFs hfa hsH hsP, recR_eq]
    refine sub_nonneg.mpr (le_trans ?_ (finsum_nonneg fun W => finsum_nonneg fun hW =>
      mul_nonneg (Nat.cast_nonneg _) ?_))
    · exact IntegralAgainstPositive.proof K ι P ⊥ n L _ bot_le (fun _ => semipos P)
        fun z hz => logNorm_fsH_nonpos c hz.1
    · split_ifs with hh
      · exact hlow W ((divSuppArith K ι P n (fsH ι) _ W hP ⟨_, hfa, hsH, hsP⟩ hW).1 hh) hh
      · exact mul_nonneg (by exact_mod_cast geoNum_nonneg n W _ fun j k => by simp [L, scaledFSH_a])
          (Real.log_natCast_nonneg _)

  have hone : (1 : MRing ι) ∉ P := fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  have hca : ∀ k, (constLine (ι := ι) (-1)).a k = ((0 : K → ℕ) k : ℤ) := fun k => by
    simp [constLine, HermLine.ofWeight]
  have hB : II K ι P (n + 1) (Fin.snoc L (constLine (-1))) = ptsIntegral P (pot L) (fun _ => 1) := by
    rw [hF.2.2 P n L _ 1 0 hP hLs hCs hca GroundTheory.Heights₂.Heights.Inter.ThmIUnique.isMultiHomog_one' hone, recR_eq]
    have hd : divSupp P (1 : MRing ι) = ∅ := by
      ext W
      simp only [divSupp, Ideal.span_singleton_one, le_top, sup_of_le_right, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false, iff_false, not_and]
      exact fun h => (h.1.1.ne_top (top_le_iff.mp h.1.2)).elim
    have hl : logNorm (constLine (ι := ι) (-1)) 1 = fun _ => -1 := by
      funext z
      simp [logNorm, constLine, HermLine.ofWeight]
    rw [cycR, hd, finsum_mem_empty, arInt, hl, G5.ptsIntegral_const]
    simp only [zero_sub, neg_mul, one_mul, neg_neg]
    rfl
  have heq : ptsIntegral P (pot L) (fun _ => 1) = ptsIntegral P (pot fun _ : Fin n => fsH ι) (fun _ => 1) :=
    G5.ptsIntegral_eq_of_add_const P _ _ (fun j => ⟨1, fun z hz => by
      show Real.log ((scaledFSH ι).h z) = Real.log ((fsH ι).h z) + 1
      rw [show (1 : ℝ) = -(-1) by norm_num]
      exact G5.log_tensor_constLine (fsH ι) (-1) z hz.1⟩) _
  have hpos := hG K ι P n hP
  linarith
end ScaledFSTopPos

theorem ScaledFSTopPos.proof (hG : FSGeomDegPos.Statement) : ScaledFSTopPos.Statement := by
  intro K _ ι _ P d II hII hd hP
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  clear hd
  induction n generalizing P with
  | zero =>
    exact ScaledFSTopPos.step II hII hG 0
      (fun W hW _ => absurd hW (GroundTheory.Heights₂.Heights.Inter.arithVarZero K ι W)) P hP
  | succ m ih => exact ScaledFSTopPos.step II hII hG (m + 1) (fun W hW _ => (ih W hW).le) P hP

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem chartLat_subset_chartLatQ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ) {s : Ω} (hs : s ∈ chartLat y a n) :
    s ∈ chartLatQ y a n := by
  intro c hc
  have hle : chartRingZ y c ≤ (chartRingQ y c).restrictScalars ℤ :=
    Algebra.adjoin_le (Algebra.subset_adjoin (R := ℚ))
  exact hle (hs c hc)

theorem ChartLatRank.proof (hfin : SectionLatticeFinite.Statement) : ChartLatRank.Statement := by
  intro K _ ι _ Ω _ _ y a n hy
  classical
  set M := AddSubgroup.toIntSubmodule (chartLat y a n) with hM
  have hfg : M.FG := (Submodule.fg_iff_addSubgroup_fg M).mpr (hfin K ι Ω y a n hy)
  have : Module.Finite ℤ M := Module.Finite.iff_fg.mpr hfg
  obtain ⟨r, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := M)
  set v : Fin r → Ω := fun i => ((b i : M) : Ω) with hv
  have hvZ : LinearIndependent ℤ v := b.linearIndependent.map' M.subtype M.ker_subtype
  have hvQ : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hvZ
  have hspan : Submodule.span ℚ (Set.range v) = chartLatQ y a n := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact chartLat_subset_chartLatQ y a n (b i).2
    · intro s hs
      obtain ⟨N, hN, hNs⟩ := ChartDenominator.proof K ι Ω y a n s hs
      have hmemM : (⟨(N : Ω) * s, hNs⟩ : M) ∈ Submodule.span ℤ (Set.range b) := b.mem_span _
      have hmemZ : (N : Ω) * s ∈ Submodule.span ℤ (Set.range v) := by
        have h := Submodule.mem_map_of_mem (f := M.subtype) hmemM
        rw [Submodule.map_span, ← Set.range_comp] at h
        exact h
      have hmemQ : (N : Ω) * s ∈ Submodule.span ℚ (Set.range v) :=
        Submodule.span_le_restrictScalars ℤ ℚ _ hmemZ
      have hN0 : (N : Ω) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
      have hs' : s = ((N : ℚ)⁻¹) • ((N : Ω) * s) := by
        rw [Rat.smul_def]
        push_cast
        field_simp
      rw [hs']
      exact Submodule.smul_mem _ _ hmemQ
  rw [Module.finrank_eq_card_basis b, ← hspan, finrank_span_eq_card hvQ]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open scoped Pointwise

noncomputable section

namespace VeroneseMonoBasis

theorem sec_x_eq (D n : ℕ) : sec ℤ (Veronese.x D) n = sec ℤ (Veronese.t D) (2 * n) := by
  rw [SectionsRank.sec_eq_span, SectionsRank.sec_eq_span, VeroneseGenDeg.range_alt, ← pow_mul]

theorem mono_mem_sec (D n : ℕ) (k : Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card) :
    (∏ i, Veronese.t D i ^ adtEnum D (2 * n) k i) ∈ sec ℤ (Veronese.x D) n := by
  rw [sec_x_eq]
  refine Submodule.mem_map.mpr ⟨monoZ (adtEnum D (2 * n) k),
    (mem_homogeneousSubmodule _ _).mpr (monoZ_isHomogeneous (adtEnum_sum D (2 * n) k)), ?_⟩
  rw [AlgHom.toLinearMap_apply, aeval_monoZ]

theorem linearIndependent_mono (D N : ℕ) :
    LinearIndependent ℤ (fun k : Fin (Finset.Nat.antidiagonalTuple (D + 1) N).card =>
      ∏ i, Veronese.t D i ^ adtEnum D N k i) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro u hu l
  set p : MvPolynomial (Fin (D + 1)) ℤ := ∑ k, u k • monoZ (adtEnum D N k) with hp
  have hpa : aeval (Veronese.t D) p = aeval (Veronese.t D) (0 : MvPolynomial (Fin (D + 1)) ℤ) := by

    rw [hp, map_sum, map_zero, ← hu]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, aeval_monoZ]
  have hp0 := VeroneseGenDeg.aeval_t_injective D hpa
  have hc := congrArg (AddMonoidAlgebra.coeff · (Finsupp.equivFunOnFinite.symm (adtEnum D N l))) hp0
  rw [hp, coeff_sum, MvPolynomial.coeff_zero, Finset.sum_eq_single l (fun k _ hkl => ?_) (by simp)] at hc
  · rwa [MvPolynomial.coeff_smul, monoZ, coeff_monomial, if_pos rfl, smul_eq_mul, mul_one] at hc
  · rw [MvPolynomial.coeff_smul, monoZ, coeff_monomial, if_neg, smul_zero]
    intro hE
    exact hkl (adtEnum_injective D N (by simpa using hE))

end VeroneseMonoBasis


open VeroneseMonoBasis in
theorem VeroneseMonoBasis.proof : VeroneseMonoBasis.Statement := by
  intro D n
  have hex : ∀ k : Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card,
      ∃ f : MvPolynomial (Ix (Veronese.Idx D)) ℤ, f.IsHomogeneous n ∧
        aeval (Veronese.x D) f = ∏ i, Veronese.t D i ^ adtEnum D (2 * n) k i := fun k => by
    obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.mp (mono_mem_sec D n k)
    exact ⟨f, (mem_homogeneousSubmodule _ _).mp hf, hfx⟩
  choose f hf hfx using hex
  have hb : ∀ k, aeval (Veronese.x D) (map (Int.castRingHom ℚ) (f k)) =
      ∏ i, Veronese.t D i ^ adtEnum D (2 * n) k i := fun k => by
    rw [aeval_map_intQ, hfx]
  refine ⟨fun k => map (Int.castRingHom ℚ) (f k), ⟨fun k => ⟨f k, hf k, rfl⟩, ?_, ?_⟩, hb⟩
  · simp only [hb]
    exact linearIndependent_mono D (2 * n)
  · simp only [hb]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact mono_mem_sec D n k
    · rw [sec_x_eq]
      rintro _ ⟨g, hg, rfl⟩
      rw [AlgHom.toLinearMap_apply, aeval_eq_sum_adt _ ((mem_homogeneousSubmodule _ _).mp hg)]
      refine Submodule.sum_mem _ fun a ha => ?_
      have hai : adtEnum D (2 * n) ((Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).equivFin ⟨a, ha⟩) = a := by
        simp [adtEnum]
      rw [← zsmul_eq_mul, ← hai]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
