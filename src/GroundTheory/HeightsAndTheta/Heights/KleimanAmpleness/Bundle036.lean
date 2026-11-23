module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThreeOnWGen
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeVanish
import Mathlib.Algebra.Lie.OfAssociative
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle016
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace RestrictGenerated

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {K' : Type w} [Field K'] [Algebra S K'] {y : Fin (N + 1) → K'}
  {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}


variable (y) in
def toChartY (I : Chart x) (h : ∀ i ∈ I.1, y i ≠ 0) : Chart y :=
  ⟨I.1, I.2.1, fun i hi => (mem_support y).mpr (h i hi)⟩

theorem liftChart_toChartY (I : Chart x) (h : ∀ i ∈ I.1, y i ≠ 0) :
    liftChart hxy (toChartY y I h) = I := rfl

theorem r_zero {Q : SubSystem S x Ω} {Q' : SubSystem S y K'} {r : Ω → K'}
    (h : RestrictData Q hxy Q' r) (J : Chart y) : r 0 = 0 := by
  have := h.add J 0 (Q.sub _).zero_mem 0 (Q.sub _).zero_mem
  rw [add_zero] at this
  simpa using this

theorem r_sub {Q : SubSystem S x Ω} {Q' : SubSystem S y K'} {r : Ω → K'}
    (h : RestrictData Q hxy Q' r) (J : Chart y) {u v : Ω}
    (hu : u ∈ Q.sub (liftChart hxy J)) (hv : v ∈ Q.sub (liftChart hxy J)) :
    r (u - v) = r u - r v := by
  have := h.add J (u - v) (sub_mem hu hv) v hv
  rw [sub_add_cancel] at this
  exact eq_sub_of_add_eq this.symm

theorem exists_of_mem {Q : SubSystem S x Ω} {Q' : SubSystem S y K'} {r : Ω → K'}
    (h : RestrictData Q hxy Q' r) (J : Chart y) {t : K'} (ht : t ∈ Q'.sub J) :
    ∃ w ∈ Q.sub (liftChart hxy J), r w = t := by
  rw [← h.span J] at ht
  induction ht using Submodule.span_induction with
  | mem t ht => obtain ⟨w, hw, rfl⟩ := ht; exact ⟨w, hw, rfl⟩
  | zero => exact ⟨0, zero_mem _, r_zero h J⟩
  | add t t' _ _ ht ht' =>
    obtain ⟨w, hw, rfl⟩ := ht
    obtain ⟨w', hw', rfl⟩ := ht'
    exact ⟨w + w', add_mem hw hw', h.add J w hw w' hw'⟩
  | smul b t _ ht =>
    obtain ⟨w, hw, rfl⟩ := ht
    obtain ⟨f, s, e, hs, hf, hse, hb⟩ := b.2
    let a : chartRing S x (liftChart hxy J) := ⟨aeval x f / aeval x s, f, s, e, hs, hf, hse, rfl⟩
    refine ⟨a • w, (Q.sub _).smul_mem a hw, ?_⟩
    show r (aeval x f / aeval x s * w) = (b : K') * r w
    rw [h.smul J w hw f s e hs hf hse, hb]

theorem sub_ne_bot (Q' : LineBundle S y) (J : Chart y) : Q'.toSubSystem.sub J ≠ ⊥ := by
  intro h0
  obtain ⟨Q'', hQ''⟩ := Q'.invertible J
  have h1 : (1 : K') ∈ (1 : Submodule (chartRing S y J) K') := Submodule.mem_one.mpr ⟨1, map_one _⟩
  rw [← hQ''] at h1
  change (1 : K') ∈ Q'.toSubSystem.sub J * Q'' at h1
  rw [h0, Submodule.bot_mul] at h1
  exact one_ne_zero ((Submodule.mem_bot _).mp h1)

theorem mem_twist_of_eq_zero (Q : LineBundle S x) (Q' : LineBundle S y) {r : Ω → K'}
    {pp : Ideal (Poly S N)} (hpp : primeOf (S := S) y = pp)
    (h : RestrictData Q.toSubSystem hxy Q'.toSubSystem r) (J : Chart y) {z : Ω}
    (hz : z ∈ Q.toSubSystem.sub (liftChart hxy J)) (hr : r z = 0) :
    z ∈ (Q.toSubSystem.twist (idealSys x pp)).sub (liftChart hxy J) := by
  obtain ⟨w₀, hw₀, hrw₀⟩ : ∃ w ∈ Q.toSubSystem.sub (liftChart hxy J), r w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply sub_ne_bot Q' J
    rw [← h.span J, Submodule.span_eq_bot]
    rintro _ ⟨w, hw, rfl⟩
    exact hcon w hw
  obtain ⟨Q'', hQ''⟩ := Q.invertible (liftChart hxy J)
  have hmulA : ∀ u ∈ Q.toSubSystem.sub (liftChart hxy J), ∀ v ∈ Q'',
      u * v ∈ chartRing S x (liftChart hxy J) := by
    intro u hu v hv
    have : u * v ∈ Q.toSubSystem.sub (liftChart hxy J) * Q'' := Submodule.mul_mem_mul hu hv
    change u * v ∈ Q.sub (liftChart hxy J) * Q'' at this
    rw [hQ''] at this
    obtain ⟨b, hb⟩ := Submodule.mem_one.mp this
    rw [← hb]; exact b.2
  have hkey : ∀ v ∈ Q'', z * v ∈ idealMod (x := x) pp (liftChart hxy J) := by
    intro v hv
    obtain ⟨f, s, e, hs, hf, hse, ha⟩ := hmulA z hz v hv
    obtain ⟨g, t, e', ht, hg, hte, hb⟩ := hmulA w₀ hw₀ v hv
    have h1 := h.smul J w₀ hw₀ f s e hs hf hse
    have h2 := h.smul J z hz g t e' ht hg hte
    have heq : aeval x f / aeval x s * w₀ = aeval x g / aeval x t * z := by
      rw [← ha, ← hb]; ring
    rw [heq, h2, hr, mul_zero] at h1
    have hs0 : aeval y s ≠ 0 := eval_ne_zero_of_mem_monos J hs
    have hfy : aeval y f = 0 :=
      (div_eq_zero_iff.mp ((mul_eq_zero.mp h1.symm).resolve_right hrw₀)).resolve_right hs0
    have hfp : f ∈ pp := by
      rw [← hpp]; exact (mem_primeOf_of_isHomogeneous y hf).mpr hfy
    rw [ha]
    exact Submodule.subset_span ⟨f, s, e, hfp, hs, hf, hse, rfl⟩
  have hall : ∀ m ∈ Q.sub (liftChart hxy J) * Q'',
      z * m ∈ (Q.toSubSystem.twist (idealSys x pp)).sub (liftChart hxy J) := by
    intro m hm
    induction hm using Submodule.mul_induction_on' with
    | mem_mul_mem q hq v hv =>
      refine Submodule.subset_span ⟨z * v, hkey v hv, q, hq, ?_⟩
      rw [smul_eq_mul]; ring
    | add m _ m' _ hm hm' => rw [mul_add]; exact add_mem hm hm'
  have h1 : (1 : Ω) ∈ Q.sub (liftChart hxy J) * Q'' := by
    rw [hQ'']; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  simpa using hall 1 h1

end RestrictGenerated


open RestrictGenerated in
theorem RestrictGenerated.proof : RestrictGenerated.Statement.{u, w} := by
  intro S _ Ω _ _ N x K' _ _ y hxy pp _ hyp Q Q' r h hgen I
  have hX : ∀ i, (X i : Poly S N) ∈ pp ↔ y i = 0 := fun i => by
    rw [← hyp, mem_primeOf_of_isHomogeneous y (isHomogeneous_X S i), aeval_X]
  have hQtw : ∀ (I' : Chart x) (i : Fin (N + 1)), i ∈ I'.1 → y i = 0 →
      Q.toSubSystem.sub I' ≤ (Q.toSubSystem.twist (idealSys x pp)).sub I' := fun I' i hi hyi =>
    StepThree.OnW.Gen.sub_le_twist_idealSys_of_mem _ I' hi ((hX i).mpr hyi)
  by_cases hI : ∀ i ∈ I.1, y i ≠ 0
  swap
  · push Not at hI
    obtain ⟨i, hi, hyi⟩ := hI
    exact le_sup_of_le_right (hQtw I i hi hyi)

  have hlift : ∀ t ∈ Q'.toSubSystem.secs, ∃ s : Chart x → Ω, (∀ I', s I' ∈ Q.toSubSystem.sub I') ∧
      (∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 →
        s I₁ - s I₂ ∈ (Q.toSubSystem.twist (idealSys x pp)).sub I₂) ∧
      ∀ (I' : Chart x) (hI' : ∀ i ∈ I'.1, y i ≠ 0), r (s I') = t := by
    intro t ht
    have ht' : ∀ J, t ∈ Q'.toSubSystem.sub J := fun J => (Submodule.mem_iInf _).mp ht J
    choose w hw hrw using fun J => exists_of_mem h J (ht' J)
    classical
    have hmem : ∀ I', (if hI' : ∀ i ∈ I'.1, y i ≠ 0 then w (toChartY y I' hI') else 0) ∈
        Q.toSubSystem.sub I' := by
      intro I'
      split_ifs with hI'
      · have := hw (toChartY y I' hI')
        rwa [liftChart_toChartY] at this
      · exact zero_mem _
    refine ⟨fun I' => if hI' : ∀ i ∈ I'.1, y i ≠ 0 then w (toChartY y I' hI') else 0, hmem,
      fun I₁ I₂ h12 => ?_, fun I' hI' => ?_⟩
    · by_cases h2 : ∀ i ∈ I₂.1, y i ≠ 0
      · have h1 : ∀ i ∈ I₁.1, y i ≠ 0 := fun i hi => h2 i (h12 hi)
        have hm1 := Q.toSubSystem.mono I₁ I₂ h12 _ (hw (toChartY y I₁ h1))
        have hm2 := hw (toChartY y I₂ h2)
        dsimp only
        rw [dite_eq_left h1, dite_eq_left h2]
        exact mem_twist_of_eq_zero Q Q' hyp h (toChartY y I₂ h2) (sub_mem hm1 hm2)
          (by rw [r_sub h (toChartY y I₂ h2) hm1 hm2, hrw, hrw, sub_self])
      · push Not at h2
        obtain ⟨i, hi, hyi⟩ := h2
        exact hQtw I₂ i hi hyi (sub_mem (Q.toSubSystem.mono I₁ I₂ h12 _ (hmem I₁)) (hmem I₂))
    · dsimp only
      rw [dite_eq_left hI']
      exact hrw _
  let J : Chart y := toChartY y I hI
  have hJ : ∀ t ∈ Q'.toSubSystem.sub J, ∃ u ∈ Submodule.span (chartRing S x I)
      {z | ∃ s : Chart x → Ω, (∀ I', s I' ∈ Q.toSubSystem.sub I') ∧
        (∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ (Q.toSubSystem.twist (idealSys x pp)).sub I₂) ∧
        z = s I}, u ∈ Q.toSubSystem.sub I ∧ r u = t := by
    intro t ht
    rw [← hgen J] at ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨s, hs, hc, hr⟩ := hlift t ht
      exact ⟨s I, Submodule.subset_span ⟨s, hs, hc, rfl⟩, hs I, hr I hI⟩
    | zero => exact ⟨0, zero_mem _, zero_mem _, r_zero h J⟩
    | add t t' _ _ ht ht' =>
      obtain ⟨u, hu, hu', rfl⟩ := ht
      obtain ⟨v, hv, hv', rfl⟩ := ht'
      exact ⟨u + v, add_mem hu hv, add_mem hu' hv', h.add J u hu' v hv'⟩
    | smul b t _ ht =>
      obtain ⟨u, hu, hu', rfl⟩ := ht
      obtain ⟨f, s, e, hs, hf, hse, hb⟩ := b.2
      let a : chartRing S x I := ⟨aeval x f / aeval x s, f, s, e, hs, hf, hse, rfl⟩
      refine ⟨a • u, Submodule.smul_mem _ a hu, Submodule.smul_mem _ a hu', ?_⟩
      show r (aeval x f / aeval x s * u) = (b : K') * r u
      rw [h.smul J u hu' f s e hs hf hse, hb]
  intro q hq
  obtain ⟨u, hu, hu', hru⟩ := hJ (r q) (h.mem J q hq)
  have hd : q - u ∈ (Q.toSubSystem.twist (idealSys x pp)).sub I :=
    mem_twist_of_eq_zero Q Q' hyp h J (sub_mem hq hu') (by rw [r_sub h J hq hu', hru, sub_self])
  rw [show q = u + (q - u) by abel]
  exact Submodule.add_mem_sup hu hd

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section ReadOnCharts

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  (M : FinGradedSub (S := S) (x := x) E) (c : ℤ)

def chartVal {n : ℕ} (y : Cech.Cochain (locSys S N M.coneSubE) n) (I : Cech.Idx (support x) n) : E :=
  coeffE S x E c (locConeE M I.1.1 I.1.2.2 (y ⟨⟨I.1.1, I.1.2.1, Finset.subset_univ _⟩, I.2⟩))

theorem chartVal_zero {n : ℕ} (I : Cech.Idx (support x) n) :
    chartVal M c (0 : Cech.Cochain (locSys S N M.coneSubE) n) I = 0 := by
  unfold chartVal
  rw [Pi.zero_apply, map_zero, map_zero]

theorem chartVal_add {n : ℕ} (y y' : Cech.Cochain (locSys S N M.coneSubE) n) (I : Cech.Idx (support x) n) :
    chartVal M c (y + y') I = chartVal M c y I + chartVal M c y' I := by
  unfold chartVal
  rw [Pi.add_apply, map_add (f := _), map_add (f := _)]

theorem chartVal_smul {n : ℕ} (a : S) (y : Cech.Cochain (locSys S N M.coneSubE) n)
    (I : Cech.Idx (support x) n) : chartVal M c (a • y) I = a • chartVal M c y I := by
  unfold chartVal
  rw [Pi.smul_apply, LinearMap.map_smul_of_tower, map_smul]

theorem chartVal_mem {n : ℕ} {y : Cech.Cochain (locSys S N M.coneSubE) n}
    (hy : y ∈ Cech.Cdeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) n) (I : Cech.Idx (support x) n) :
    chartVal M c y I ∈ (M.tildeSys c).sub I.1 := by
  obtain ⟨v, hv, hyv⟩ := locConeE_degLoc M c _ I.1.2.2
    (hy ⟨⟨I.1.1, I.1.2.1, Finset.subset_univ _⟩, I.2⟩ (Set.mem_univ _))
  unfold chartVal
  rw [hyv, coeffE_singleE_same]
  exact hv

theorem chartVal_d {n : ℕ} (y : Cech.Cochain (locSys S N M.coneSubE) n) (J : Cech.Idx (support x) (n + 1)) :
    chartVal M c (Cech.d (locSys S N M.coneSubE) locResS n y) J =
      ∑ j : J.1.1, Cech.sgn J.1.1 j • chartVal M c y (Cech.face J j) := by
  refine (congrArg (coeffE S x E c)
    (locConeE_d M y ⟨⟨J.1.1, J.1.2.1, Finset.subset_univ _⟩, J.2⟩ J.1.2.2)).trans ?_

  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  rfl

def toTildeC {n : ℕ} (y : Cech.Cochain (locSys S N M.coneSubE) n)
    (hy : y ∈ Cech.Cdeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) n) :
    Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) n :=
  fun I => ⟨chartVal M c y I, chartVal_mem M c hy I⟩

theorem coe_d_toTildeC {n : ℕ} (y : Cech.Cochain (locSys S N M.coneSubE) n)
    (hy : y ∈ Cech.Cdeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) n) (J : Cech.Idx (support x) (n + 1)) :
    ((Cech.d (fun I : Chart x => ↥((M.tildeSys c).sub I)) (M.tildeSys c).res n (toTildeC M c y hy) J : _) : E) =
      chartVal M c (Cech.d (locSys S N M.coneSubE) locResS n y) J := by
  rw [coe_d_sub, chartVal_d]
  rfl

def toTildeCocy (n : ℕ) :
    Cech.cocyDeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) locResS n →ₗ[S]
      LinearMap.ker (Cech.d (fun I : Chart x => ↥((M.tildeSys c).sub I)) (M.tildeSys c).res n) where
  toFun y := ⟨toTildeC M c y.1 y.2.2, LinearMap.mem_ker.mpr (funext fun J => Subtype.ext (by
    rw [coe_d_toTildeC, LinearMap.mem_ker.mp y.2.1, chartVal_zero]
    rfl))⟩
  map_add' y y' := Subtype.ext (funext fun I => Subtype.ext (chartVal_add M c y.1 y'.1 I))
  map_smul' a y := Subtype.ext (funext fun I => Subtype.ext (chartVal_smul M c a y.1 I))

set_option synthInstance.maxHeartbeats 200000 in
def toTildeH (n : ℕ) : cohom M.coneGradedE n c →ₗ[S] (M.tildeSys c).H n :=
  Submodule.liftQ _ ((Submodule.mkQ _).comp (toTildeCocy M c n)) (by
    intro y hy
    rw [Submodule.mem_comap] at hy
    refine LinearMap.mem_ker.mpr ((Submodule.Quotient.mk_eq_zero _).mpr ?_)
    cases n with
    | zero =>
      change (y : Cech.Cochain (locSys S N M.coneSubE) 0) ∈ (⊥ : Submodule S _) at hy
      rw [Submodule.mem_bot] at hy
      change toTildeC M c y.1 y.2.2 ∈ (⊥ : Submodule S _)
      rw [Submodule.mem_bot]
      funext I
      apply Subtype.ext
      change chartVal M c (y : Cech.Cochain (locSys S N M.coneSubE) 0) I = 0
      rw [hy, chartVal_zero]
    | succ k =>
      change (y : Cech.Cochain (locSys S N M.coneSubE) (k + 1)) ∈
        (Cech.Cdeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) k).map
          (Cech.d (locSys S N M.coneSubE) locResS k) at hy
      obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp hy
      change toTildeC M c y.1 y.2.2 ∈
        LinearMap.range (Cech.d (fun I : Chart x => ↥((M.tildeSys c).sub I)) (M.tildeSys c).res k)
      refine ⟨toTildeC M c z hz, funext fun J => Subtype.ext ?_⟩
      rw [coe_d_toTildeC]
      change _ = chartVal M c (y : Cech.Cochain (locSys S N M.coneSubE) (k + 1)) J
      rw [← hzy])

theorem d_liftCochain_any {n : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) n)
    (ht : Cech.d (fun I : Chart x => ↥((M.tildeSys c).sub I)) (M.tildeSys c).res n t = 0) :
    Cech.d (locSys S N M.coneSubE) locResS n (liftCochain M c t) = 0 := by
  funext K
  change _ = 0
  by_cases hK : K.1.1 ⊆ support x
  · apply locConeE_injective M K.1.1 hK
    rw [locConeE_d M (liftCochain M c t) K hK, map_zero]
    have h0 := coe_d_sub (M.tildeSys c) t ⟨⟨K.1.1, K.1.2.1, hK⟩, K.2⟩
    rw [ht] at h0
    calc ∑ j : K.1.1, Cech.sgn K.1.1 j • locConeE M (Cech.face K j).1.1
          ((Cech.face_subset K j).trans hK) (liftCochain M c t (Cech.face K j))
        = ∑ j : K.1.1, Cech.sgn K.1.1 j • singleE S x E c
            (t (Cech.face (⟨⟨K.1.1, K.1.2.1, hK⟩, K.2⟩ : Cech.Idx (support x) (n + 1)) j) : E) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [liftCochain_of M c t _ ((Cech.face_subset K j).trans hK)]
          congr 1
          exact locConeE_liftTilde M c _ _ _
      _ = singleE S x E c (∑ j : K.1.1, Cech.sgn K.1.1 j •
            (t (Cech.face (⟨⟨K.1.1, K.1.2.1, hK⟩, K.2⟩ : Cech.Idx (support x) (n + 1)) j) : E)) := by

          rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_zsmul]
      _ = 0 := by
          rw [← h0]
          exact map_zero _
  · have := locModE_subsingleton (S := S) M (Finset.not_subset.mp hK).choose_spec.1
      (by simpa [mem_support] using (Finset.not_subset.mp hK).choose_spec.2)
    exact Subsingleton.elim _ _

theorem chartVal_liftCochain {n : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) n)
    (I : Cech.Idx (support x) n) : chartVal M c (liftCochain M c t) I = (t I : E) := by
  have e1 := liftCochain_of M c t ⟨⟨I.1.1, I.1.2.1, Finset.subset_univ _⟩, I.2⟩ I.1.2.2
  have e2 := locConeE_liftTilde M c ⟨I.1.1, I.1.2.1, Finset.subset_univ _⟩ I.1.2.2 (t I)
  unfold chartVal
  rw [e1]
  exact (congrArg (coeffE S x E c) e2).trans (coeffE_singleE_same _ _)

set_option synthInstance.maxHeartbeats 200000 in
theorem toTildeH_surjective (n : ℕ) : Function.Surjective (toTildeH M c n) := by
  intro q
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  refine ⟨Submodule.Quotient.mk ⟨liftCochain M c t.1,
    d_liftCochain_any M c t.1 (LinearMap.mem_ker.mp t.2), liftCochain_mem M c t.1⟩, ?_⟩
  change Submodule.Quotient.mk (toTildeCocy M c n _) = Submodule.Quotient.mk t
  congr 1
  exact Subtype.ext (funext fun I => Subtype.ext (chartVal_liftCochain M c t.1 I))

end ReadOnCharts

theorem TildeFiniteE.proof (h : SerreFinite.Statement.{u, v}) : TildeFiniteE.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x E _ _ _ _ M i c
  have : Module.Finite S (cohom M.coneGradedE i c) :=
    h S N M.coneSubE M.coneGradedE M.coneSubE_finite i c
  exact Module.Finite.of_surjective (toTildeH M c i) (toTildeH_surjective M c i)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SnapperQuotFilt.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F₁ F₂ : SubFamily k x E), (∀ I, (F₁.sub I).FG) → (∀ I, F₂.sub I ≤ F₁.sub I) →
    ∀ J : Ideal (Poly k N), (∀ f ∈ J, ∀ d : ℕ, homogeneousComponent d f ∈ J) → primeOf (S := k) x ≤ J →
    (∀ I, (F₁.toSubSystem.twist (idealSys x J)).sub I ≤ F₂.sub I) →
    ∃ (r : ℕ) (G : ℕ → SubFamily k x E) (pp : Fin r → Ideal (Poly k N)) (a : Fin r → ℤ),
      (∀ m I, ((G m).sub I).FG) ∧ (G 0).toSubSystem = F₂.toSubSystem ∧
      (G r).toSubSystem = F₁.toSubSystem ∧ (∀ m < r, ∀ I, (G m).sub I ≤ (G (m + 1)).sub I) ∧
      (∀ m, (pp m).IsPrime ∧ (∀ f ∈ pp m, ∀ d : ℕ, homogeneousComponent d f ∈ pp m) ∧ J ≤ pp m) ∧
      ∀ (m : Fin r) (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ),
        Nonempty (QuotIso
          (((G (m + 1)).toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
          (((G m).toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
          (((twistSys k x (a m)).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
          ((((twistSys k x (a m)).twist (idealSys x (pp m))).twistPows t (fun j => (L j).toSubSystem) n).twist
            (twistSys k x c)))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def cellLocSys {S : Type} [CommRing S] {X : Type} {Ω : Type} [Field Ω] [Algebra S Ω] (G : X → Submodule S Ω)
    (f : Ω) : X → Submodule S Ω :=
  fun I => ⨆ n : ℕ, (G I).comap (LinearMap.mulLeft S (f ^ n))

def CellLocGlue.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
    (G : (∀ k, Finset (ι k)) → Submodule S Ω) (R : Subring Ω) (m : ℕ) (f u : Fin m → Ω),
    (∀ l, f l ∈ R) → (∀ l, u l ∈ R) → ∑ l, u l * f l = 1 →
    (∀ I, ∀ r ∈ R, ∀ a ∈ G I, r * a ∈ G I) →
    (∀ l, CellPosExact S y (cellLocSys G (f l))) →
    CellPosExact S y G

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart mIdealOver)

def CellLocEval.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (γ : K → ℤ) (n : ℕ),
    Nonempty (cellH S y γ n ≃ₗ[S] cechHc ι (quotPart S (mIdealOver S y)) γ n)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
