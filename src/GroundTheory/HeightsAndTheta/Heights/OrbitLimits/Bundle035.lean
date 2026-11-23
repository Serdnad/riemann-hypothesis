module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle040
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveAlgebraic
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCurveDivVertical
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalAmple
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CurveOrbitEmbedding
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CurveVerticalPointChart
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionsNonzero

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
  GroundTheory.Heights₂.Heights.Inter.FibreMultiHomogeneous

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem FibreMultiHomog.proof : FibreMultiHomog.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' G hv hP
  classical
  refine cyc_isMultiHomogIdeal_of_isHomogeneous fun k n f hf => ?_
  rw [show (DirectSum.decompose (weightedHomogeneousSubmodule G.Φ (cycBlockWt k)) f n : MvPolynomial _ G.Φ) =
    weightedHomogeneousComponent (cycBlockWt k) n f from MvPolynomial.decompose'_apply _ _ f n]
  obtain ⟨b, hb, F, e⟩ := exists_clear G f
  rw [_root_.ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker] at hf ⊢
  have hF : liftZ κ v F ∈ P' := by
    rw [← G.genericFibre_ker_target, RingHom.mem_ker, aeval_liftZ, ← e, map_mul, aeval_C]
    simp [hf]
  have hc : weightedHomogeneousComponent (cycBlockWt k.1) n (liftZ κ v F) ∈ P' := by
    have hH := cyc_isHomogeneous_of_isMultiHomogIdeal hP k.1
    have := hH n hF
    rwa [show (DirectSum.decompose (weightedHomogeneousSubmodule ℤ (cycBlockWt k.1)) (liftZ κ v F) n : MRing ι') =
      weightedHomogeneousComponent (cycBlockWt k.1) n (liftZ κ v F) from
        MvPolynomial.decompose'_apply _ _ (liftZ κ v F) n] at this
  rw [liftZ_component hv, ← G.genericFibre_ker_target, RingHom.mem_ker, aeval_liftZ, ← component_map, ← e,
    weightedHomogeneousComponent_C_mul, map_mul, aeval_C] at hc
  exact (mul_eq_zero.1 hc).resolve_left ((map_ne_zero _).2 hb)

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GroundTheory.Heights₂.Heights.Inter

namespace CurveEmbedOrbit

theorem sameOrbit_refl {K : Type} {ι : K → Type} (z : (Σ k, ι k) → ℂ) : SameOrbit z z :=
  ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩

theorem sameOrbit_symm {K : Type} {ι : K → Type} {z w : (Σ k, ι k) → ℂ} (h : SameOrbit z w) : SameOrbit w z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), funext fun p => ?_⟩
  rw [← mul_assoc, inv_mul_cancel₀ (hc p.1), one_mul]

theorem sameOrbit_trans {K : Type} {ι : K → Type} {z w u : (Σ k, ι k) → ℂ} (h1 : SameOrbit z w)
    (h2 : SameOrbit w u) : SameOrbit z u := by
  obtain ⟨c, hc, rfl⟩ := h1
  obtain ⟨d, hd, rfl⟩ := h2
  exact ⟨fun k => c k * d k, fun k => mul_ne_zero (hc k) (hd k), funext fun p => by simp only; ring⟩

theorem eq_of_sameOrbit {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} (hB : Birational y) {σ τ : Ω →+* ℂ}
    (hst : SameOrbit (fun p => σ (y p)) (fun p => τ (y p))) : σ = τ := by
  obtain ⟨c, hc, hcy⟩ := hst
  ext s
  obtain ⟨d, g, h, hg, hh, hh0, hgs⟩ := hB s
  have key : ∀ ρ : Ω →+* ℂ, ρ s * eval (fun p => ρ (y p)) (map (Int.castRingHom ℂ) h) =
      eval (fun p => ρ (y p)) (map (Int.castRingHom ℂ) g) := fun ρ => by
    rw [CurveOrbit.eval_comp, CurveOrbit.eval_comp, hgs, map_mul]
  have e1 := key σ
  have e2 := key τ
  rw [hcy, CurveOrbit.eval_smul _ _ hh, CurveOrbit.eval_smul _ _ hg] at e1
  have hE : eval (fun p => τ (y p)) (map (Int.castRingHom ℂ) h) ≠ 0 := by
    rw [CurveOrbit.eval_comp]
    exact (map_ne_zero τ).mpr hh0
  have hC : (∏ k, c k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  apply mul_right_cancel₀ (mul_ne_zero hC hE)
  linear_combination e1 - (∏ k, c k ^ d k) * e2

end CurveEmbedOrbit


open CurveEmbedOrbit in
theorem CurveEmbedOrbit.proof : CurveEmbedOrbit.Statement := by
  intro K _ ι _ Ω _ y R hP hB hR hRu
  classical
  obtain ⟨j, -, hj⟩ := exists_chart hP
  have hex : ∀ t : R, ∃ σ : Ω →+* ℂ, SameOrbit (t : (Σ k, ι k) → ℂ) (fun p => σ (y p)) :=
    fun t => CurveOrbit.exists_sameOrbit hP hB (hR t t.2)
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro t s hts
    have h1 : SameOrbit (t : (Σ k, ι k) → ℂ) s :=
      sameOrbit_trans (hf t) (by rw [hts]; exact sameOrbit_symm (hf s))
    exact Subtype.ext ((hRu t (hR t t.2)).unique ⟨t.2, sameOrbit_refl _⟩ ⟨s.2, h1⟩)
  have hsurj : Function.Surjective f := by
    intro τ
    obtain ⟨t, ⟨htR, hzt⟩, -⟩ := hRu _ (CurveOrbit.mem_mcPts τ y hj)
    exact ⟨⟨t, htR⟩, eq_of_sameOrbit hB
      (sameOrbit_trans (sameOrbit_symm (hf ⟨t, htR⟩)) (sameOrbit_symm hzt))⟩
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField IsDedekindDomain

noncomputable section

namespace CurveRingFiniteAlt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem mem_integer_of_mem_chartRingZ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (z : (Σ k, ι k) → F) (c : ∀ k, ι k)
    (hc : ∀ p : Σ k, ι k, v.valuation F (z p) ≤ v.valuation F (z ⟨p.1, c p.1⟩)) {b : F}
    (hb : b ∈ chartRingZ z c) : b ∈ (v.valuation F).integer := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    rw [Valuation.mem_integer_iff, map_div₀]
    rcases eq_or_ne (v.valuation F (z ⟨p.1, c p.1⟩)) 0 with h0 | h0
    · simp [h0]
    · exact (div_le_one₀ (zero_lt_iff.mpr h0)).mpr (hc p)
  | algebraMap r => rw [eq_intCast]; exact intCast_mem _ r
  | add x w _ _ hx hw => exact add_mem hx hw
  | mul x w _ _ hx hw => exact mul_mem hx hw


omit [Fintype K] in
theorem mem_integralClosure {F : Type} [Field F] [NumberField F] (z : (Σ k, ι k) → F) (c0 : ∀ k, ι k)
    (hc0 : ∀ k, z ⟨k, c0 k⟩ ≠ 0) {b : F}
    (hb : ∀ c : ∀ k, ι k, (∀ k, z ⟨k, c k⟩ ≠ 0) → b ∈ chartRingZ z c) :
    b ∈ integralClosure ℤ F := by
  suffices hv : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F b ≤ 1 by
    obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F b hv
    rw [← hr]
    exact r.2
  intro v
  have hmax : ∀ k, ∃ i, ∀ j, v.valuation F (z ⟨k, j⟩) ≤ v.valuation F (z ⟨k, i⟩) := fun k => by
    obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => v.valuation F (z ⟨k, j⟩))
      ⟨c0 k, Finset.mem_univ _⟩
    exact ⟨i, fun j => hi j (Finset.mem_univ _)⟩
  choose c hc using hmax
  have hcz : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k h0 => by
    have h1 := hc k (c0 k)
    rw [h0, map_zero] at h1
    exact hc0 k ((Valuation.zero_iff _).mp (le_antisymm h1 zero_le))
  exact mem_integer_of_mem_chartRingZ v z c (fun p => hc p.1 p.2) (hb c hcz)


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem charZero {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (hy : IsHorizontal (mCoordIdeal y)) :
    CharZero Ω := by
  refine charZero_of_injective_algebraMap (R := ℤ) ((injective_iff_map_eq_zero _).mpr fun m hm => ?_)
  have h : m ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_C,
      MvPolynomial.algebraMap_apply, hm, C_0]
  rwa [show (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ from hy, Ideal.mem_bot] at h

end CurveRingFiniteAlt


open CurveRingFiniteAlt IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree in
theorem CurveRingFinite.proof : CurveRingFinite.Statement := by
  intro K _ ι _ Ω _ y hy
  classical
  have := CurveRingFiniteAlt.charZero y hy.2.2.1
  choose c0 hc0 using hy.2.1.2.2
  have hy0 : ∀ k, y ⟨k, c0 k⟩ ≠ 0 := fun k h => hc0 k (X_mem_of_eq_zero h)
  let r : (Σ k, ι k) → Ω := fun p => y p / y ⟨p.1, c0 p.1⟩
  let κ : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ (Set.range r)
  have : FiniteDimensional ℚ κ := IntermediateField.finiteDimensional_adjoin fun x hx => by
    obtain ⟨p, rfl⟩ := hx
    exact (isAlgebraic_ratio hy c0 hy0 p).isIntegral
  have : NumberField κ :=
    { to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ κ).injective
      to_finiteDimensional := inferInstance }
  let z : (Σ k, ι k) → κ := fun p => ⟨r p, IntermediateField.subset_adjoin ℚ _ ⟨p, rfl⟩⟩
  have hzy : ∀ p q : Σ k, ι k, p.1 = q.1 → ((z p / z q : κ) : Ω) = y p / y q := by
    rintro ⟨k, i⟩ ⟨k', j⟩ h
    simp only at h
    subst h
    exact div_div_div_cancel_right₀ (hy0 k) _ _
  have hyz : ∀ p, z p ≠ 0 → y p ≠ 0 := fun p h hp => h (Subtype.ext (by
    show y p / y ⟨p.1, c0 p.1⟩ = 0
    rw [hp, zero_div]))
  let φ : κ →ₐ[ℤ] Ω := (IntermediateField.val κ).toRingHom.toIntAlgHom
  have hmap : ∀ c : ∀ k, ι k, chartRingZ y c = (chartRingZ z c).map φ := fun c => by
    rw [chartRingZ, chartRingZ, AlgHom.map_adjoin, ← Set.range_comp]
    congr 2
    funext p
    exact (hzy p ⟨p.1, c p.1⟩ rfl).symm
  have hκ : ∀ b ∈ curveRing y, b ∈ κ := fun b hb => by
    have h := mem_curveRing.mp hb c0 hy0
    rw [hmap, Subalgebra.mem_map] at h
    obtain ⟨x, -, rfl⟩ := h
    exact x.2
  have hint : ∀ b (hb : b ∈ curveRing y), (⟨b, hκ b hb⟩ : κ) ∈ integralClosure ℤ κ := fun b hb => by
    refine mem_integralClosure z c0 (fun k h => ?_) fun c hc => ?_
    · have h1 := congrArg (fun x : κ => (x : Ω)) h
      have h2 : y ⟨k, c0 k⟩ / y ⟨k, c0 k⟩ = 0 := h1
      exact one_ne_zero ((div_self (hy0 k)).symm.trans h2)
    · have h := mem_curveRing.mp hb c (fun k => hyz _ (hc k))
      rw [hmap, Subalgebra.mem_map] at h
      obtain ⟨x, hx, hxb⟩ := h
      have e : x = ⟨b, hκ b hb⟩ := Subtype.ext hxb
      exact e ▸ hx
  have : Module.Finite ℤ (integralClosure ℤ κ) := inferInstanceAs (Module.Finite ℤ (𝓞 κ))
  let f : curveRing y →ₗ[ℤ] integralClosure ℤ κ :=
    { toFun := fun b => ⟨⟨b, hκ b b.2⟩, hint b b.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_injective f fun a b h =>
    Subtype.ext (congrArg (fun w : integralClosure ℤ κ => ((w : κ) : Ω)) h)

end

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo CurveVerticalPointChart

noncomputable section

theorem CurveVertPointChart.proof (hF : CurveRingFinite.Statement) (hCP : CurveClosedPointChart.Statement) :
    CurveVertPointChart.Statement := by
  classical
  intro K _ ι _ Ω _ y s d hy hs hsP W hW c hc
  have hWp : W.IsPrime := hW.1.1.1
  have hPW : mCoordIdeal y ≤ W := le_sup_left.trans hW.1.1.2
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => ne_zero_of_X_notMem fun h => hc k (hPW h)

  have hv := IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical.full K ι (mCoordIdeal y) s d hy hs hsP W hW
  rw [IsHorizontal, ← Ne, Submodule.ne_bot_iff] at hv
  obtain ⟨n, hn, hn0⟩ := hv
  have hmax := chartPrimeB_isMaximal y (hF K ι Ω y hy) hPW hWp hc hyc hn0 (Ideal.mem_comap.mp hn)
  rw [curvePtIdeal_eq y hPW hWp hc hyc]
  have hmp : (chartPrimeB y c W hyc).IsPrime := hmax.isPrime

  have hrat : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ locSub y _ hmp := by
    obtain ⟨c', hyc', h'⟩ := hCP K ι Ω y hy _ hmax
    have hinv : ∀ k, y ⟨k, c' k⟩ / y ⟨k, c k⟩ ∈ locSub y _ hmp := by
      intro k
      obtain ⟨a, b, hb, hab⟩ := h' ⟨k, c k⟩
      have hab0 : (b : Ω) * (y ⟨k, c k⟩ / y ⟨k, c' k⟩) = a := hab
      have hab' : (a : Ω) * y ⟨k, c' k⟩ = b * y ⟨k, c k⟩ := by
        rw [← hab0]
        field_simp [hyc' k]
      refine mem_locSub.mpr ⟨b, a, ?_, ?_⟩
      · intro ha
        obtain ⟨e, g, hg, hgW, he⟩ := mem_chartPrimeB.mp ha
        obtain ⟨f, w, hw, hbw⟩ := exists_rep y hyc (mem_chart y hyc b)
        apply hb
        refine mem_chartPrimeB.mpr ⟨f, w, hw, ?_, hbw⟩
        have h1 : X ⟨k, c k⟩ * (HilbertSamuel.SmallSectionsNonzero.chartMono c e * w) ∈ W := by
          refine mem_of_aeval_eq y hPW
            (Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_mul hg
              (Inter.AvoidRing.isMultiHomog_X k (c' k)))
              (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c f))
            (Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_X k (c k))
              (Inter.AvoidRing.isMultiHomog_mul
                (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c e) hw))
            (by abel) ?_ (W.mul_mem_right _ (W.mul_mem_right _ hgW))
          simp only [map_mul, aeval_X, HilbertSamuel.SmallSectionsNonzero.aeval_chartMono]
          linear_combination (-(y ⟨k, c' k⟩ * ∏ k, y ⟨k, c k⟩ ^ f k)) * he +
            (y ⟨k, c k⟩ * ∏ k, y ⟨k, c k⟩ ^ e k) * hbw +
            ((∏ k, y ⟨k, c k⟩ ^ e k) * ∏ k, y ⟨k, c k⟩ ^ f k) * hab'
        exact mem_of_chartMono_mul hWp hc ((hWp.mem_or_mem h1).resolve_left (hc k))
      · rw [← hab0]
        field_simp [hyc' k, hyc k]
    intro p
    obtain ⟨a, b, hb, hab⟩ := h' p
    have hu : y p / y ⟨p.1, c' p.1⟩ ∈ locSub y _ hmp := mem_locSub.mpr ⟨a, b, hb, hab⟩
    have hprod := mul_mem hu (hinv p.1)
    have he : y p / y ⟨p.1, c' p.1⟩ * (y ⟨p.1, c' p.1⟩ / y ⟨p.1, c p.1⟩) = y p / y ⟨p.1, c p.1⟩ := by
      field_simp [hyc' p.1, hyc p.1]
    rwa [he] at hprod
  have hY : ∀ e : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ e k ≠ 0 := fun e =>
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hyc k)
  refine ⟨hmax, fun p => mem_locSub.mp (hrat p), fun e g hg => ⟨fun hgW => ?_, ?_⟩⟩
  · have hr : aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-(e k : ℤ)) ∈ chartRingZ y c :=
      (HilbertSamuel.LiftBirationalAmple.mem_chartLat_one y).mp
        (HilbertSamuel.LiftBirationalAmple.chartLat_form hg) c hyc
    have hinv : ∏ k, y ⟨k, c k⟩ ^ (-(e k : ℤ)) = (∏ k, y ⟨k, c k⟩ ^ e k)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun k _ => by rw [zpow_neg, zpow_natCast]
    rw [hinv] at hr
    obtain ⟨a, b, hb, hab⟩ := mem_locSub.mp (chart_le_locSub y _ hmp c hrat hr)
    have hab' : (b : Ω) * aeval y g = a * ∏ k, y ⟨k, c k⟩ ^ e k := by
      rw [← hab]
      field_simp [hY e]
    refine ⟨a, b, ?_, hb, hab'⟩
    obtain ⟨f, w, hw, hbw⟩ := exists_rep y hyc (mem_chart y hyc b)
    refine mem_chartPrimeB.mpr ⟨f + e, w * g, Inter.AvoidRing.isMultiHomog_mul hw hg, W.mul_mem_left _ hgW, ?_⟩
    rw [prod_pow_add, map_mul]
    linear_combination (-(∏ k, y ⟨k, c k⟩ ^ f k)) * hab' + (aeval y g) * hbw
  · rintro ⟨a, b, ha, hb, hab⟩
    obtain ⟨f, v, hv, hvW, hav⟩ := mem_chartPrimeB.mp ha
    obtain ⟨f', w, hw, hbw⟩ := exists_rep y hyc (mem_chart y hyc b)
    have hwW : w ∉ W := fun h => hb (mem_chartPrimeB.mpr ⟨f', w, hw, h, hbw⟩)
    have h1 : HilbertSamuel.SmallSectionsNonzero.chartMono c f * (w * g) ∈ W := by
      refine mem_of_aeval_eq y hPW
        (Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_mul
          (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c e)
          (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c f')) hv)
        (Inter.AvoidRing.isMultiHomog_mul (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c f)
          (Inter.AvoidRing.isMultiHomog_mul hw hg))
        (by abel) ?_ (W.mul_mem_left _ hvW)
      simp only [map_mul, HilbertSamuel.SmallSectionsNonzero.aeval_chartMono]
      linear_combination (-((∏ k, y ⟨k, c k⟩ ^ e k) * ∏ k, y ⟨k, c k⟩ ^ f' k)) * hav +
        ((∏ k, y ⟨k, c k⟩ ^ f k) * aeval y g) * hbw -
        ((∏ k, y ⟨k, c k⟩ ^ f k) * ∏ k, y ⟨k, c k⟩ ^ f' k) * hab
    exact (hWp.mem_or_mem (mem_of_chartMono_mul hWp hc h1)).resolve_left hwW

end

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

namespace CurveVerticalIndex

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem span_toAddSubgroup (y : (Σ k, ι k) → Ω) (x : Ω) :
    (Submodule.span (curveRing y) {x}).toAddSubgroup = curveMul y x := by
  ext z
  simp only [Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton, curveMul, AddSubgroup.mem_map,
    AddMonoidHom.coe_mulLeft, Subring.mem_toAddSubgroup]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b, b.2, by rw [Subring.smul_def, smul_eq_mul, mul_comm]⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, hb⟩, by rw [Subring.smul_def, smul_eq_mul, mul_comm]⟩


omit [∀ k, Fintype (ι k)] in
theorem genIndex_eq_card (y : (Σ k, ι k) → Ω) (a : K → ℤ) {x : Ω} (hx : x ∈ curveSectionMod y a) :
    genIndex (chartLat y a 1) (curveMul y x) = Nat.card (curveSectionQuot y a x) := by
  have hle : curveMul y x ≤ chartLat y a 1 := by
    rw [← span_toAddSubgroup]
    intro z hz
    exact (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx)) hz
  rw [genIndex, AddSubgroup.relIndex_eq_one.mpr hle, Nat.cast_one, div_one, ← span_toAddSubgroup]
  rfl

end CurveVerticalIndex

theorem CurveVertIndex.proof (hF : CurveSectionQuotFinite.Statement) (hV : CurveVertPointLength.Statement)
    (hR : CurveVertPointResidue.Statement) : CurveVertIndex.Statement := by
  intro K _ ι _ Ω _ y s d hP hs hsP
  have := hF K ι Ω y s d hP hs hsP
  obtain ⟨hbij, hmult⟩ := hV K ι Ω y s d hP hs hsP
  rw [CurveVerticalIndex.genIndex_eq_card y _ (HilbertSamuel.LiftBirationalAmple.chartLat_form hs),
    LogCardLength.proof (curveRing y) (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)), vertR]
  calc _ = ∑ᶠ W ∈ divSupp (mCoordIdeal y) s,
          (locLen (curvePtIdeal y W) (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) : ℝ) *
            Real.log (Nat.card (curveRing y ⧸ curvePtIdeal y W)) := by
        refine finsum_mem_congr rfl fun W hW => ?_
        rw [if_neg (IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical.full K ι _ s d hP hs hsP W hW), hmult W hW,
          ← hR K ι Ω y s d hP hs hsP W hW]
        congr 3
    _ = ∑ᶠ m ∈ {m : Ideal (curveRing y) |
          m.IsMaximal ∧ locLen m (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) ≠ 0},
          (locLen m (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) : ℝ) *
            Real.log (Nat.card (curveRing y ⧸ m)) :=
        finsum_mem_eq_of_bijOn _ hbij fun _ _ => rfl
    _ = _ := by
        refine finsum_mem_inter_support_eq _ _ {m : Ideal (curveRing y) | m.IsMaximal} ?_
        ext m
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Function.mem_support]
        exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, fun h0 => h2 (by simp [h0])⟩, h2⟩⟩

end

end GroundTheory.Heights₂.Heights.Targets
end
