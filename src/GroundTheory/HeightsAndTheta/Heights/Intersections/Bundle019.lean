module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteMapOpen
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle038
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
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.Height
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle011

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem LocRingDimOne.proof (hF : LocRingFrac.Statement) (hN : LocRingNoeth.Statement)
    (hL : LocRingLocal.Statement) (hPow : LocRingPow.Statement) : LocRingDimOne.Statement := by
  classical
  intro K _ ι _ P s a W hP hs hsP hW
  obtain ⟨hPp, hPh, -⟩ := hP
  have hWp : W.IsPrime := hW.1.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.1.2
  have hsW : s ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
  obtain ⟨hloc, hunit⟩ := hL K ι P W hPp hWp hPW
  have hNoeth := hN K ι P W hPp hWp hPW hW.2
  refine ⟨hNoeth, hloc, ?_⟩

  choose c hc using hW.2
  have ht := AvoidRing.isMultiHomog_coordProd (R := ℤ) c a
  have htW := AvoidRing.coordProd_not_mem hWp c hc a
  set t : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ a k
  have htP : Ideal.Quotient.mk P t ∈ nonZeroDivisors (MRing ι ⧸ P) :=
    mem_nonZeroDivisors_of_ne_zero fun h => htW (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))
  set x : FractionRing (MRing ι ⧸ P) := IsLocalization.mk' _ (Ideal.Quotient.mk P s) ⟨_, htP⟩
  have hxA : x ∈ locRing P W := Subring.subset_closure ⟨s, t, a, htP, htW, hs, ht, rfl⟩
  have hx : x * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P t) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) :=
    IsLocalization.mk'_spec _ _ _
  set x' : locRing P W := ⟨x, hxA⟩
  have hxu : ¬ IsUnit x' := fun h => (hunit x' s t a hs ht htW hx).mp h hsW
  have hx0 : x' ≠ 0 := by
    intro h
    have h0 : x = 0 := congrArg Subtype.val h
    rw [h0, zero_mul, eq_comm, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at hx
    exact hsP hx

  have hmin : IsLocalRing.maximalIdeal (locRing P W) ∈ (Ideal.span {x'}).minimalPrimes := by
    refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).mpr hxu⟩, fun Q hQ _ y hy => ?_⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy
    obtain ⟨u, v, b, hu, hv, hvW, hyuv⟩ := hF K ι P W hPp hWp hPW y y.2
    have huW : u ∈ W := by
      by_contra h
      exact hy ((hunit y u v b hu hv hvW hyuv).mpr h)
    obtain ⟨n, z, hz, hyn⟩ :=
      hPow K ι P s t a W x u v b y hPp hPh hs hsP hW ht htW hx hu hv huW hvW hyuv
    have hyn' : y ^ n = x' * ⟨z, hz⟩ := Subtype.ext (by simpa using hyn)
    have hyQ : y ^ n ∈ Q := hyn' ▸ Ideal.mul_mem_right _ _ (hQ.2 (Ideal.mem_span_singleton_self x'))
    exact hQ.1.mem_of_pow_mem n hyQ
  have hle := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  have hne : IsLocalRing.maximalIdeal (locRing P W) ≠ ⊥ := fun h =>
    hx0 (by simpa [h] using (IsLocalRing.mem_maximalIdeal x').mpr hxu)
  have h1 : (IsLocalRing.maximalIdeal (locRing P W)).height = 1 :=
    le_antisymm hle (Order.one_le_iff_ne_zero.mpr (fun h => hne (Ideal.height_eq_zero_iff_eq_bot.mp h)))
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h1]
  rfl

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityValuationCentre.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsMultiProjPrime P → ∀ (Γ : Type) [LinearOrderedCommGroupWithZero Γ] (v : Valuation (funField P) Γ) (n : ℤ),
    v (n : funField P) < 1 →
    ∃ W : Ideal (MRing ι), IsMultiProjPrime W ∧ P ≤ W ∧ C n ∈ W ∧
      ∀ z : funField P, (z : FractionRing (MRing ι ⧸ P)) ∈ locRing P W → v z ≤ 1

theorem RegularityValuationCentre.exists_int_valuation_lt_one {F : Type*} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    ∃ n : ℤ, n ≠ 0 ∧ v.valuation F (n : F) < 1 := by
  obtain ⟨x, hxv, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hc : v.asIdeal.comap (algebraMap ℤ (NumberField.RingOfIntegers F)) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hx0 hxv (Algebra.IsIntegral.isIntegral x)
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  refine ⟨n, hn0, ?_⟩
  have e : (n : F) = algebraMap (NumberField.RingOfIntegers F) F (algebraMap ℤ _ n) := by simp
  rw [e, IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
  exact hn

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

def VerticalEmbedding.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (f g : MRing ι) (a : K → ℕ) (x : funField P),
    IsArithVar P 1 → IsMultiHomog f a → IsMultiHomog g a → f ∉ P → g ∉ P →
    (x : FractionRing (MRing ι ⧸ P)) *
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P f) →
    vertR P (Fin.elim0 : Fin 0 → HermLine ι) f - vertR P (Fin.elim0 : Fin 0 → HermLine ι) g =
      ∑ᶠ σ : funField P →+* ℂ, Real.log ‖σ x‖

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory Filter

noncomputable section

theorem maDensity_fin_zero (φ : Fin 0 → (Fin 0 → ℂ) → ℝ) (y : Fin 0 → ℂ) : maDensity φ y = 1 := by
  simp [maDensity, mixedDisc]

theorem exists_isSheet_fin_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ)}
    {y : Fin 0 → ℂ} {w : ((k : K) → ι k) → ℂ} (hw : w ∈ fibre P Ψ y) : ∃ γ, IsSheet P Ψ y w γ := by
  obtain ⟨z, hz, rfl, hΨ⟩ := hw
  refine ⟨fun _ => z, rfl, Eventually.of_forall fun y' => ⟨differentiableAt_const _, hz, ?_⟩⟩
  rw [Subsingleton.elim y' y]
  exact hΨ

theorem regularityPointsSum_holds.proof : regularityPointsSum_holds.Statement := by
  classical
  intro K _ ι _ P hP
  obtain ⟨k₀⟩ := hP.1
  have hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ), IsGoodProj P Ψ :=
    goodProjExists K ι P 0 hP
  have hgood : IsGoodProj P hΨ.choose := hΨ.choose_spec
  have hF : (fibre P hΨ.choose (default : Fin 0 → ℂ)).Finite :=
    fibreFinite K ι P 0 hΨ.choose hP hgood default
  let pick : (((k : K) → ι k) → ℂ) → (Σ k, ι k) → ℂ := fun w =>
    if hγ : ∃ γ, IsSheet P hΨ.choose default w γ then hγ.choose default else 0
  have hpick : ∀ w ∈ fibre P hΨ.choose default, pick w ∈ mcPts P ∧ segre (pick w) = w := by
    intro w hw
    have hγ := exists_isSheet_fin_zero hw
    simp only [pick, dif_pos hγ]
    exact ⟨hγ.choose_spec.2.self_of_nhds.2.1, hγ.choose_spec.1⟩
  have hone : ∀ w ∈ fibre P hΨ.choose default, hΨ.choose w 0 = 1 := by
    rintro w ⟨_, _, _, h⟩
    rw [h]
    rfl
  have hR : ∀ t ∈ hF.toFinset.image pick, ∃ w ∈ fibre P hΨ.choose default, t = pick w := by
    intro t ht
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp ht
    exact ⟨w, hF.mem_toFinset.mp hw, rfl⟩
  refine ⟨hF.toFinset.image pick, fun t ht => ?_, fun z hz => ?_, fun h _ => ?_⟩
  · obtain ⟨w, hw, rfl⟩ := hR t ht
    exact (hpick w hw).1
  · have ha : hΨ.choose (segre z) 0 ≠ 0 := fun h0 =>
      hgood z hz (funext fun i => by rw [Fin.eq_zero i]; exact h0)
    set a := hΨ.choose (segre z) 0 with ha_def

    let c : K → ℂ := fun k => if k = k₀ then a⁻¹ else 1
    have hc : ∀ k, c k ≠ 0 := fun k => by by_cases h : k = k₀ <;> simp [c, h, ha]
    have hprod : ∏ k, c k = a⁻¹ := by
      rw [Finset.prod_eq_single k₀ (fun k _ hk => by simp [c, hk]) (by simp)]
      simp [c]
    have hw₁ : segre (fun p => c p.1 * z p) ∈ fibre P hΨ.choose default := by
      refine ⟨_, mcPts_smul hP.2.1.2.1 c hc hz, rfl, funext fun i => ?_⟩
      rw [Fin.eq_zero i, segre_smul, hprod, map_smul, Pi.smul_apply, smul_eq_mul,
        ← ha_def, inv_mul_cancel₀ ha]
      rfl
    have hseg₁ : segre (fun p => c p.1 * z p) = a⁻¹ • segre z := by rw [segre_smul, hprod]

    have horb : ∀ t ∈ hF.toFinset.image pick, SameOrbit z t → segre t = a⁻¹ • segre z := by
      intro t ht ⟨c', _, hzt⟩
      obtain ⟨w, hw, rfl⟩ := hR t ht
      have hs : segre z = (∏ k, c' k) • segre (pick w) := by rw [hzt, segre_smul]
      have h1 : a = ∏ k, c' k := by
        rw [ha_def, hs, map_smul, Pi.smul_apply, smul_eq_mul, (hpick w hw).2, hone w hw, mul_one]
      rw [hs, ← h1, smul_smul, inv_mul_cancel₀ ha, one_smul]
    refine ⟨pick (segre (fun p => c p.1 * z p)), ⟨Finset.mem_image_of_mem _ (hF.mem_toFinset.mpr hw₁), ?_⟩,
      fun t ⟨ht, hzt⟩ => ?_⟩
    · refine sameOrbit_of_segre (hpick _ hw₁).1.1 a ha ?_
      rw [(hpick _ hw₁).2, hseg₁, smul_smul, mul_inv_cancel₀ ha, one_smul]
    · obtain ⟨w, hw, rfl⟩ := hR t ht
      have hw' : w = segre (fun p => c p.1 * z p) := by
        rw [← (hpick w hw).2, horb _ ht hzt, hseg₁]
      rw [hw']
  · unfold ptsIntegral
    rw [dif_pos hΨ]
    unfold ptsIntegralAt
    rw [integral_unique]
    have hvol : (volume : Measure (Fin 0 → ℂ)).real Set.univ = 1 := by
      simp [Measure.real, MeasureTheory.volume_pi]
    rw [hvol, one_smul]
    refine (?_ : ∀ y : Fin 0 → ℂ, ∑ᶠ w ∈ fibre P hΨ.choose y,
      sheetDensity P hΨ.choose (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) h y w =
        ∑ t ∈ hF.toFinset.image pick, h t) _
    intro y
    rw [Subsingleton.elim y default, finsum_mem_eq_finite_toFinset_sum _ hF,
      Finset.sum_image fun x hx y hy hxy => by
        rw [← (hpick x (hF.mem_toFinset.mp hx)).2, hxy, (hpick y (hF.mem_toFinset.mp hy)).2]]
    refine Finset.sum_congr rfl fun w hw => ?_
    have hγ := exists_isSheet_fin_zero (hF.mem_toFinset.mp hw)
    unfold sheetDensity
    rw [dif_pos hγ, maDensity_fin_zero, mul_one]
    simp only [pick, dif_pos hγ]

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

namespace FibreIsolFinite

theorem isolated_finite (N : ℕ) (S : Set (MvPolynomial (Fin N) ℂ)) :
    {x : Fin N → ℂ | (∀ s ∈ S, eval x s = 0) ∧
      ∀ᶠ y in 𝓝 x, (∀ s ∈ S, eval y s = 0) → y = x}.Finite := by
  classical
  let m : (Fin N → ℂ) → Ideal (MvPolynomial (Fin N) ℂ) := fun x => RingHom.ker (eval x)
  have hinj : Function.Injective m := by
    intro x y hxy
    funext i
    have h1 : X i - C (x i) ∈ m y := by
      rw [← hxy]
      exact RingHom.mem_ker.mpr (by simp)
    have h2 : y i - x i = 0 := by simpa using RingHom.mem_ker.mp h1
    exact (sub_eq_zero.mp h2).symm
  refine ((Ideal.finite_minimalPrimes_of_isNoetherianRing _ (Ideal.span S)).preimage
    (fun a _ b _ h => hinj h)).subset ?_
  rintro x ⟨hx, hiso⟩
  have hIm : Ideal.span S ≤ m x := by
    rw [Ideal.span_le]
    exact fun s hs => RingHom.mem_ker.mpr (hx s hs)
  have : (m x).IsPrime := RingHom.ker_isPrime _
  obtain ⟨q, hq, hqm⟩ := Ideal.exists_minimalPrimes_le hIm
  have hmq : m x ≤ q := by
    intro f hf
    refine IndefiniteRowSideFullHecke.ComplexSets.VanishNearPoint.proof IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.proof N q f x hq.1.1
      (fun g hg => RingHom.mem_ker.mp (hqm hg)) ?_
    filter_upwards [hiso] with y hy hyq
    rw [hy fun s hs => hyq s (hq.1.2 (Ideal.subset_span hs))]
    exact RingHom.mem_ker.mp hf
  show m x ∈ (Ideal.span S).minimalPrimes
  rwa [le_antisymm hqm hmq] at hq

variable {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}

theorem sameOrbit_comp_smul {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hvb : ∀ p, (v p).1 = κ p.1) {z' : (Σ k', ι' k') → ℂ} {u : (Σ k, ι k) → ℂ}
    (h : SameOrbit (fun p => z' (v p)) u) (c : K' → ℂ) (hc : ∀ k', c k' ≠ 0) :
    SameOrbit (fun p => c (v p).1 * z' (v p)) u := by
  obtain ⟨c₀, hc₀, hz⟩ := h
  refine ⟨fun k => c (κ k) * c₀ k, fun k => mul_ne_zero (hc _) (hc₀ k), funext fun p => ?_⟩
  have h1 : z' (v p) = c₀ p.1 * u p := congrFun hz p
  show c (v p).1 * z' (v p) = c (κ p.1) * c₀ p.1 * u p
  rw [hvb p, h1, mul_assoc]

theorem minor_of_sameOrbit {w u : (Σ k, ι k) → ℂ} (h : SameOrbit w u) (j : ∀ k, ι k)
    (p : Σ k, ι k) : w p * u ⟨p.1, j p.1⟩ = w ⟨p.1, j p.1⟩ * u p := by
  obtain ⟨c, -, rfl⟩ := h
  show c p.1 * u p * u ⟨p.1, j p.1⟩ = c p.1 * u ⟨p.1, j p.1⟩ * u p
  ring

theorem sameOrbit_of_minor {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hκ : Function.Injective κ) (hvb : ∀ p, (v p).1 = κ p.1)
    (hvr : ∀ q : Σ k', ι' k', q.1 ∈ Set.range κ → q ∈ Set.range v)
    {b : (Σ k', ι' k') → ℂ} (i' : ∀ k', ι' k') (hb : ∀ k', b ⟨k', i' k'⟩ = 1)
    {u : (Σ k, ι k) → ℂ} (j : ∀ k, ι k) (hj : ∀ k, u ⟨k, j k⟩ ≠ 0)
    (hm : ∀ p, b (v p) * u ⟨p.1, j p.1⟩ = b (v ⟨p.1, j p.1⟩) * u p) :
    SameOrbit (fun p => b (v p)) u := by
  have hne : ∀ k, b (v ⟨k, j k⟩) ≠ 0 := by
    intro k h0
    obtain ⟨⟨k₀, i₀⟩, hp⟩ := hvr ⟨κ k, i' (κ k)⟩ ⟨k, rfl⟩
    have hk : k₀ = k := hκ (by simpa [hp] using (hvb ⟨k₀, i₀⟩).symm)
    subst hk
    have h1 := hm ⟨k₀, i₀⟩
    dsimp only at h1
    rw [hp, hb, h0, zero_mul, one_mul] at h1
    exact hj k₀ h1
  refine ⟨fun k => b (v ⟨k, j k⟩) / u ⟨k, j k⟩, fun k => div_ne_zero (hne k) (hj k),
    funext fun p => ?_⟩
  show b (v p) = b (v ⟨p.1, j p.1⟩) / u ⟨p.1, j p.1⟩ * u p
  rw [div_mul_eq_mul_div, ← hm p, mul_div_assoc, div_self (hj _), mul_one]

theorem proof : FibreIsolFinite.Statement := by
  classical
  intro K _ ι _ K' _ ι' _ κ v P' n hB hA u
  obtain ⟨hκ, -, hvb, hvr⟩ := hB
  have hP' : IsMultiHomogIdeal P' := hA.2.1.2.1
  by_cases hu : ∀ k, ∃ i, u ⟨k, i⟩ ≠ 0
  swap
  · refine ⟨∅, fun z' hz' ho _ => absurd ?_ hu⟩
    intro k
    obtain ⟨i', hi'⟩ := hz'.1 (κ k)
    obtain ⟨⟨k₀, i₀⟩, hp⟩ := hvr ⟨κ k, i'⟩ ⟨k, rfl⟩
    have hk : k₀ = k := hκ (by simpa [hp] using (hvb ⟨k₀, i₀⟩).symm)
    subst hk
    obtain ⟨c, -, hc⟩ := ho
    refine ⟨i₀, fun h0 => hi' ?_⟩
    have h1 : z' (v ⟨k₀, i₀⟩) = c k₀ * u ⟨k₀, i₀⟩ := congrFun hc ⟨k₀, i₀⟩
    rw [hp, h0, mul_zero] at h1
    exact h1
  choose j hj using hu
  obtain ⟨N, ⟨e⟩⟩ : ∃ N, Nonempty ((Σ k', ι' k') ≃ Fin N) := ⟨_, ⟨Fintype.equivFin _⟩⟩

  let S : (∀ k', ι' k') → Set (MvPolynomial (Fin N) ℂ) := fun i' =>
    {s | (∃ f ∈ P', s = rename e (map (Int.castRingHom ℂ) f)) ∨
      (∃ k', s = X (e ⟨k', i' k'⟩) - 1) ∨
      ∃ p : Σ k, ι k, s = X (e (v p)) * C (u ⟨p.1, j p.1⟩) - X (e (v ⟨p.1, j p.1⟩)) * C (u p)}
  have hS : ∀ i' (y : Fin N → ℂ), (∀ s ∈ S i', eval y s = 0) ↔
      ((∀ f ∈ P', eval (y ∘ e) (map (Int.castRingHom ℂ) f) = 0) ∧ (∀ k', y (e ⟨k', i' k'⟩) = 1) ∧
        ∀ p, y (e (v p)) * u ⟨p.1, j p.1⟩ = y (e (v ⟨p.1, j p.1⟩)) * u p) := by
    intro i' y
    constructor
    · intro h
      refine ⟨fun f hf => ?_, fun k' => ?_, fun p => ?_⟩
      · have h1 := h _ (Or.inl ⟨f, hf, rfl⟩)
        rwa [eval_rename] at h1
      · have h1 := h _ (Or.inr (Or.inl ⟨k', rfl⟩))
        simp only [map_sub, map_one, eval_X] at h1
        exact sub_eq_zero.mp h1
      · have h1 := h _ (Or.inr (Or.inr ⟨p, rfl⟩))
        simp only [map_sub, map_mul, eval_X, eval_C] at h1
        exact sub_eq_zero.mp h1
    · rintro ⟨h1, h2, h3⟩ s (⟨f, hf, rfl⟩ | ⟨k', rfl⟩ | ⟨p, rfl⟩)
      · rw [eval_rename]
        exact h1 f hf
      · simp only [map_sub, map_one, eval_X]
        rw [h2 k', sub_self]
      · simp only [map_sub, map_mul, eval_X, eval_C]
        rw [h3 p, sub_self]
  have hfin := fun i' => isolated_finite N (S i')
  let T : Finset ((Σ k', ι' k') → ℂ) :=
    Finset.univ.biUnion fun i' : (∀ k', ι' k') => (hfin i').toFinset.image fun y => y ∘ e
  refine ⟨T, fun z' hz' ho hiso => ?_⟩
  choose i' hi' using hz'.1
  obtain ⟨ε, hε, hball⟩ := hiso

  let d : K' → ℂ := fun k' => (z' ⟨k', i' k'⟩)⁻¹
  have hd : ∀ k', d k' ≠ 0 := fun k' => inv_ne_zero (hi' k')
  let a : (Σ k', ι' k') → ℂ := fun q => d q.1 * z' q
  have ha1 : ∀ k', a ⟨k', i' k'⟩ = 1 := fun k' => inv_mul_cancel₀ (hi' k')
  have haP : a ∈ mcPts P' := mcPts_smul hP' d hd hz'
  have hao : SameOrbit (fun p => a (v p)) u := sameOrbit_comp_smul hvb ho d hd
  let w₀ : Fin N → ℂ := a ∘ e.symm
  have hw₀ : w₀ ∘ e = a := funext fun q => by simp [w₀]
  have hw₀Z : ∀ s ∈ S i', eval w₀ s = 0 := by
    refine (hS i' w₀).mpr ⟨by rw [hw₀]; exact haP.2, fun k' => ?_, fun p => ?_⟩
    · simpa [w₀] using ha1 k'
    · simpa [w₀] using minor_of_sameOrbit hao j p
  have hw₀iso : ∀ᶠ y in 𝓝 w₀, (∀ s ∈ S i', eval y s = 0) → y = w₀ := by
    let g : (Fin N → ℂ) → (Σ k', ι' k') → ℂ := fun y q => z' ⟨q.1, i' q.1⟩ * y (e q)
    have hg : Continuous g := continuous_pi fun q => continuous_const.mul (continuous_apply _)
    have hgw : g w₀ = z' := funext fun q => by
      show z' ⟨q.1, i' q.1⟩ * (d (e.symm (e q)).1 * z' (e.symm (e q))) = z' q
      rw [Equiv.symm_apply_apply]
      exact mul_inv_cancel_left₀ (hi' q.1) (z' q)
    have hmem : g ⁻¹' Metric.ball z' ε ∈ 𝓝 w₀ :=
      hg.continuousAt.preimage_mem_nhds (by rw [hgw]; exact Metric.ball_mem_nhds _ hε)
    filter_upwards [hmem] with y hy hyS
    obtain ⟨h1, h2, h3⟩ := (hS i' y).mp hyS
    have hbP : y ∘ e ∈ mcPts P' := ⟨fun k' => ⟨i' k', by simp [h2 k']⟩, h1⟩
    have hbo : SameOrbit (fun p => (y ∘ e) (v p)) u :=
      sameOrbit_of_minor (b := y ∘ e) hκ hvb hvr i' (fun k' => h2 k') j hj h3
    have hgP : g y ∈ mcPts P' := mcPts_smul hP' (fun k' => z' ⟨k', i' k'⟩) hi' hbP
    have hgo : SameOrbit (fun p => g y (v p)) u :=
      sameOrbit_comp_smul hvb hbo (fun k' => z' ⟨k', i' k'⟩) hi'
    obtain ⟨c₁, -, hgz⟩ := hball (g y) hgP hgo hy
    have hc1 : ∀ k', c₁ k' = 1 := fun k' => by
      have h : z' ⟨k', i' k'⟩ * y (e ⟨k', i' k'⟩) = c₁ k' * z' ⟨k', i' k'⟩ := congrFun hgz ⟨k', i' k'⟩
      rw [h2 k', mul_one] at h
      exact mul_right_cancel₀ (hi' k') (h.symm.trans (one_mul _).symm)
    funext x
    have h : z' ⟨(e.symm x).1, i' (e.symm x).1⟩ * y (e (e.symm x)) = c₁ (e.symm x).1 * z' (e.symm x) :=
      congrFun hgz (e.symm x)
    rw [hc1, one_mul, Equiv.apply_symm_apply] at h
    show y x = (z' ⟨(e.symm x).1, i' (e.symm x).1⟩)⁻¹ * z' (e.symm x)
    rw [← h, ← mul_assoc, inv_mul_cancel₀ (hi' _), one_mul]
  refine ⟨w₀ ∘ e, Finset.mem_biUnion.mpr ⟨i', Finset.mem_univ _,
    Finset.mem_image.mpr ⟨w₀, (hfin i').mem_toFinset.mpr ⟨hw₀Z, hw₀iso⟩, rfl⟩⟩, ?_⟩
  rw [hw₀]
  exact ⟨fun k' => z' ⟨k', i' k'⟩, hi', funext fun q => (mul_inv_cancel_left₀ (hi' q.1) (z' q)).symm⟩

end FibreIsolFinite

end GroundTheory.Heights₂.Heights.Inter
end
end
