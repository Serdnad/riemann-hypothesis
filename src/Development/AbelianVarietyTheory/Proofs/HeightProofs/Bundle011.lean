module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.Topology.Separation.CompletelyRegular
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle009
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle007
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
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.CastAddNeNatAdd
import ReciprocityTheory.SemistableReduction.AeBlockSphereEvalNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle010
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

@[expose] public section

section

open MeasureTheory Metric NumberField ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.MultiplicativeHeights
open scoped TensorProduct

namespace GlobalTheory

theorem ae_eval_circleMap_ne_zero : ∀ (m : ℕ) (f : MvPolynomial (Fin m) ℂ), f ≠ 0 →
    ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)),
      MvPolynomial.eval (fun i => circleMap 0 1 (x i)) f ≠ 0 := by
  intro m
  induction m with
  | zero =>
    intro f hf
    refine Filter.Eventually.of_forall fun x => ?_
    rw [MvPolynomial.eq_C_of_isEmpty f] at hf ⊢
    simpa using hf
  | succ m ih =>
    intro f hf
    set P := MvPolynomial.finSuccEquiv ℂ m f with hPdef
    have hP : P ≠ 0 := by
      intro h
      apply hf
      exact (MvPolynomial.finSuccEquiv ℂ m).injective (by rw [← hPdef, h, map_zero])
    obtain ⟨k, hk⟩ : ∃ k, P.coeff k ≠ 0 := by
      by_contra h
      push Not at h
      exact hP (Polynomial.ext fun k => by simpa using h k)
    have h1 := ih _ hk
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
    have he : MeasurePreserving e volume volume := volume_preserving_piFinSuccAbove _ 0
    have hcont : Continuous fun (x : Fin (m + 1) → ℝ) =>
        MvPolynomial.eval (fun i => circleMap 0 1 (x i)) f :=
      (MvPolynomial.continuous_eval f).comp
        (continuous_pi fun i => (continuous_circleMap 0 1).comp (continuous_apply i))
    have hmeas : MeasurableSet {z : ℝ × (Fin m → ℝ) |
        MvPolynomial.eval (fun i => circleMap 0 1 (e.symm z i)) f ≠ 0} :=
      (hcont.measurable.comp e.symm.measurable) (measurableSet_singleton 0).compl
    have key : ∀ᵐ z ∂(volume : Measure (ℝ × (Fin m → ℝ))),
        MvPolynomial.eval (fun i => circleMap 0 1 (e.symm z i)) f ≠ 0 := by
      rw [Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae hmeas]
      rw [Measure.ae_ae_comm (p := fun y s =>
        MvPolynomial.eval (fun i => circleMap 0 1 (e.symm (y, s) i)) f ≠ 0) hmeas]
      filter_upwards [h1] with s hs
      set w : Fin m → ℂ := fun i => circleMap 0 1 (s i) with hw
      have hQ : Polynomial.map (MvPolynomial.eval w) P ≠ 0 := by
        intro h
        apply hs
        have := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q k) h
        simpa [Polynomial.coeff_map] using this
      have hfin : ({y : ℂ | Polynomial.eval y (Polynomial.map (MvPolynomial.eval w) P) = 0}).Finite :=
        Polynomial.finite_setOfPred_isRoot hQ
      have hnull := (hfin.countable.preimage_circleMap 0 one_ne_zero).measure_zero
        (volume : Measure ℝ)
      rw [measure_eq_zero_iff_ae_notMem] at hnull
      filter_upwards [hnull] with y hy
      have hc : (fun i => circleMap 0 1 ((e.symm (y, s) : Fin (m + 1) → ℝ) i)) =
          Fin.cons (circleMap 0 1 y) w := by
        have : (e.symm (y, s) : Fin (m + 1) → ℝ) = Fin.cons y s := by
          simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
        rw [this]
        funext i
        cases i using Fin.cases <;> simp [hw]
      rw [hc, MvPolynomial.eval_eq_eval_mv_eval']
      exact hy
    have := he.quasiMeasurePreserving.ae key
    filter_upwards [this] with x hx
    simpa using hx

theorem ae_eval₂_ne_zero_pi_toSphere (K : Type) [Field K] [Countable K] (sg : K →+* ℂ)
    (D N : ℕ) :
    ∀ᵐ t ∂(MeasureTheory.Measure.pi fun _ : Fin D =>
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℂ (Fin (N + 1)))).toSphere),
      ∀ p : MvPolynomial (Fin D × Fin (N + 1)) K, p ≠ 0 →
        MvPolynomial.eval₂ sg (fun q => (t q.1 : EuclideanSpace ℂ (Fin (N + 1))) q.2) p ≠ 0 := by
  have := NPB.countable_mvPoly (σ := Fin D × Fin (N + 1)) (R := K)
  set μ : Measure (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) :=
    Measure.pi fun _ : Fin D => (volume : Measure (EuclideanSpace ℂ (Fin (N + 1)))).toSphere with hμ
  have hgen : ∀ᵐ z ∂μ, ∀ (a : Fin D → ℕ) (p : MvPolynomial (Fin D × Fin (N + 1)) K),
      IsMultiHomogeneous a p → p ≠ 0 → MvPolynomial.eval₂ sg (blockPoint z) p ≠ 0 := by
    rw [ae_all_iff]; intro a
    rw [ae_all_iff]; intro p
    by_cases hp : IsMultiHomogeneous a p ∧ p ≠ 0
    · have hm : IsMultiHomogeneous a (MvPolynomial.map sg p) :=
        fun s hs => hp.1 s (MvPolynomial.support_map_subset _ _ hs)
      have hm0 : MvPolynomial.map sg p ≠ 0 := fun h0 =>
        hp.2 (MvPolynomial.map_injective sg sg.injective (by rw [h0, map_zero]))
      filter_upwards [ae_toSphere D (N + 1) a _ hm0 hm] with z hz _ _
      rwa [MvPolynomial.eval_map] at hz
    · exact Filter.Eventually.of_forall fun z h1 h2 => absurd ⟨h1, h2⟩ hp
  rw [ae_all_iff]; intro p
  by_cases hp : p = 0
  · exact Filter.Eventually.of_forall fun z h => absurd hp h
  set φ : (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) → ℂ := fun t =>
    MvPolynomial.eval₂ sg (fun q => (t q.1 : EuclideanSpace ℂ (Fin (N + 1))) q.2) p with hφ
  have hφc : Continuous φ := by
    have : φ = fun t => MvPolynomial.eval (fun q => (t q.1 : EuclideanSpace ℂ (Fin (N + 1))) q.2) (MvPolynomial.map sg p) := by
      funext t; rw [MvPolynomial.eval_map]
    rw [this]
    exact (MvPolynomial.continuous_eval _).comp (continuous_pi fun q => by fun_prop)
  set T : (Fin (N + 1 + D) → ℝ) → (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) → (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) :=
    fun θ t i => sphereRotation (θ (Fin.natAdd (N + 1) i)) (t i) with hT
  have hTc : Continuous fun x : (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) × (Fin (N + 1 + D) → ℝ) =>
      T x.2 x.1 := by
    refine continuous_pi fun i => ?_
    exact (continuous_sphereRotation (E := EuclideanSpace ℂ (Fin (N + 1)))).comp
      (f := fun x : (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) × (Fin (N + 1 + D) → ℝ) =>
        (x.2 (Fin.natAdd (N + 1) i), x.1 i)) (by fun_prop)
  have hTμ : ∀ θ, MeasurePreserving (T θ) μ μ := fun θ =>
    measurePreserving_pi _ _ fun i => measurePreserving_sphereRotation (volume : Measure (EuclideanSpace ℂ (Fin (N + 1)))) _
  set q : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K :=
    MvPolynomial.rename (fun r : Fin D × Fin (N + 1) => (r.1.succ, r.2)) p with hq
  have hq0 : q ≠ 0 := by
    intro h
    apply hp
    refine MvPolynomial.rename_injective (fun r : Fin D × Fin (N + 1) => (r.1.succ, r.2)) ?_
      (by rw [map_zero]; exact h)
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simpa using h
  have h1 : ∀ᵐ t ∂μ, ∀ᵐ θ ∂(volume : Measure (Fin (N + 1 + D) → ℝ)), φ (T θ t) ≠ 0 := by
    filter_upwards [hgen] with t ht
    have hq' : NPB.psi sg (blockPoint t) q ≠ 0 := fun h0 =>
      hq0 (NPB.psi_injective sg (blockPoint t) ht (by rw [h0, map_zero]))
    filter_upwards [ae_eval_circleMap_ne_zero _ _ hq'] with θ hθ
    rw [NPB.eval_psi, hq, MvPolynomial.eval₂_rename] at hθ
    convert hθ using 1
    simp only [hφ]
    congr 1
  rw [Measure.ae_ae_comm (p := fun t θ => φ (T θ t) ≠ 0)
    ((hφc.comp hTc).measurable (measurableSet_singleton 0).compl)] at h1
  have : (ae (volume : Measure (Fin (N + 1 + D) → ℝ))).NeBot := ae_neBot.2 (NeZero.ne _)
  obtain ⟨θ, hθ⟩ := h1.exists
  have h2 : ∀ᵐ t ∂μ, φ t ≠ 0 := by
    rw [← (hTμ θ).map_eq, ae_map_iff (p := fun x => φ x ≠ 0)
      (hTμ θ).measurable.aemeasurable
      (hφc.measurable (measurableSet_singleton 0).compl)]
    exact hθ
  filter_upwards [h2] with t ht _ using ht

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

open IsLocalRing

theorem gaussRing_isDVR {σ : Type} [Finite σ] (O₁ : Type) [CommRing O₁] [IsDomain O₁]
    [IsDiscreteValuationRing O₁] (P : Ideal (MvPolynomial σ O₁)) [P.IsPrime]
    (hP : P = Ideal.map MvPolynomial.C (maximalIdeal O₁))
    (O₂ : Type) [CommRing O₂] [IsLocalRing O₂] [Algebra (MvPolynomial σ O₁) O₂]
    [IsLocalization.AtPrime O₂ P] : ∃ _ : IsDomain O₂, IsDiscreteValuationRing O₂ := by
  have hd : IsDomain O₂ :=
    IsLocalization.isDomain_of_le_nonZeroDivisors O₂ P.primeCompl_le_nonZeroDivisors
  refine ⟨hd, ?_⟩
  have : IsNoetherianRing O₂ :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  have hinj := IsLocalization.injective O₂ (M := P.primeCompl) P.primeCompl_le_nonZeroDivisors
  obtain ⟨g, hg⟩ := IsPrincipalIdealRing.principal (maximalIdeal O₁)
  have hg' : maximalIdeal O₁ = Ideal.span {g} := hg
  have hmax : maximalIdeal O₂ =
      Ideal.span {algebraMap (MvPolynomial σ O₁) O₂ (MvPolynomial.C g)} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P O₂]
    conv_lhs => rw [hP]
    rw [hg', Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
  have hnf : ¬ IsField O₂ := by
    rw [isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]
    intro h
    have h1 := hinj (h.trans (map_zero _).symm)
    have h2 : g = 0 := by simpa using h1
    apply IsDiscreteValuationRing.not_a_field O₁
    rw [hg', h2]; simp
  refine ((IsDiscreteValuationRing.TFAE O₂ hnf).out 1 5).mpr ?_
  rw [hmax]
  exact ⟨⟨_, rfl⟩⟩

theorem exists_mvPolynomial_sub_map_mem {σ R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (I : Ideal S) (h : ∀ x : S, ∃ a : R, x - φ a ∈ I) (p : MvPolynomial σ S) :
    ∃ q : MvPolynomial σ R,
      p - MvPolynomial.map φ q ∈ Ideal.map (MvPolynomial.C : S →+* MvPolynomial σ S) I := by
  induction p using MvPolynomial.induction_on with
  | C x =>
    obtain ⟨a, ha⟩ := h x
    refine ⟨MvPolynomial.C a, ?_⟩
    rw [MvPolynomial.map_C, ← map_sub]
    exact Ideal.mem_map_of_mem _ ha
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    refine ⟨a + b, ?_⟩
    have := Ideal.add_mem _ ha hb
    convert this using 1
    rw [map_add (f := _)]; ring
  | mul_X p n hp =>
    obtain ⟨a, ha⟩ := hp
    refine ⟨a * MvPolynomial.X n, ?_⟩
    have := Ideal.mul_mem_right (MvPolynomial.X n) _ ha
    convert this using 1
    rw [map_mul, MvPolynomial.map_X]; ring

theorem gaussRing_completion :
    ∀ (K : Type) [Field K] [NumberField K] (D N : ℕ) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (O₁ : Type) [CommRing O₁] [IsDomain O₁] [IsDiscreteValuationRing O₁] [Algebra (𝓞 K) O₁], Function.Injective (algebraMap (𝓞 K) O₁) → Ideal.map (algebraMap (𝓞 K) O₁) la.asIdeal = IsLocalRing.maximalIdeal O₁ → (∀ x : O₁, ∃ a : 𝓞 K, x - algebraMap (𝓞 K) O₁ a ∈ IsLocalRing.maximalIdeal O₁) → ∀ (P : Ideal (MvPolynomial (TVar D N) O₁)) [P.IsPrime], P = Ideal.map MvPolynomial.C (IsLocalRing.maximalIdeal O₁) → ∀ (O₂ : Type) [CommRing O₂] [IsLocalRing O₂] [Algebra (MvPolynomial (TVar D N) O₁) O₂] [IsLocalization.AtPrime O₂ P], (∃ _ : IsDomain O₂, IsDiscreteValuationRing O₂) ∧ ∃ f : Op D N la →+* O₂, (∀ p : OT K D N, f (algebraMap (OT K D N) (Op D N la) p) = algebraMap (MvPolynomial (TVar D N) O₁) O₂ (MvPolynomial.map (algebraMap (𝓞 K) O₁) p)) ∧ f.Flat ∧ IsLocalHom f ∧ Ideal.map f (IsLocalRing.maximalIdeal (Op D N la)) = IsLocalRing.maximalIdeal O₂ ∧ ∀ x : O₂, ∃ a, x - f a ∈ IsLocalRing.maximalIdeal O₂ := by
  intro K _ _ D N la O₁ _ _ _ _ hinj hmap hres P _ hP O₂ _ _ _ _
  obtain ⟨hd, hdvr⟩ := gaussRing_isDVR O₁ P hP O₂
  refine ⟨⟨hd, hdvr⟩, ?_⟩
  have hcomap : (maximalIdeal O₁).comap (algebraMap (𝓞 K) O₁) = la.asIdeal := by
    symm
    apply la.isMaximal.eq_of_le
    · exact Ideal.IsPrime.ne_top inferInstance
    · rw [← hmap]; exact Ideal.le_comap_map
  have hmem : ∀ p : OT K D N,
      MvPolynomial.map (algebraMap (𝓞 K) O₁) p ∈ P ↔ p ∈ laT D N la := by
    intro p
    rw [hP, MvPolynomial.mem_map_C_iff]
    refine Iff.trans ?_ (MvPolynomial.mem_map_C_iff (I := la.asIdeal) (f := p)).symm
    refine forall_congr' fun m => ?_
    rw [MvPolynomial.coeff_map, ← hcomap, Ideal.mem_comap]
  let g : OT K D N →+* O₂ :=
    (algebraMap (MvPolynomial (TVar D N) O₁) O₂).comp (MvPolynomial.map (algebraMap (𝓞 K) O₁))
  have hu : ∀ y : (laT D N la).primeCompl, IsUnit (g y) := fun y =>
    IsLocalization.map_units (M := P.primeCompl) O₂
      ⟨MvPolynomial.map (algebraMap (𝓞 K) O₁) (y : OT K D N), fun h => y.2 ((hmem _).1 h)⟩
  let f : Op D N la →+* O₂ := IsLocalization.lift (M := (laT D N la).primeCompl) hu
  have hf : f.comp (algebraMap (OT K D N) (Op D N la)) = g := IsLocalization.lift_comp hu
  have hf' : ∀ p : OT K D N, f (algebraMap (OT K D N) (Op D N la) p) =
      algebraMap (MvPolynomial (TVar D N) O₁) O₂ (MvPolynomial.map (algebraMap (𝓞 K) O₁) p) :=
    fun p => IsLocalization.lift_eq hu p
  have hinj₂ := IsLocalization.injective O₂ (M := P.primeCompl) P.primeCompl_le_nonZeroDivisors
  have hginj : Function.Injective g := hinj₂.comp (MvPolynomial.map_injective _ hinj)
  have hfinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨p, s⟩, h⟩ := IsLocalization.surj (laT D N la).primeCompl x
    have h1 := congrArg f h
    rw [map_mul, hx, zero_mul, hf'] at h1
    have h2 : p = 0 := hginj (h1.symm.trans (map_zero g).symm)
    simp only [h2, map_zero] at h
    exact (IsLocalization.map_units (Op D N la) s).mul_left_eq_zero.mp h
  have hmax : Ideal.map f (maximalIdeal (Op D N la)) = maximalIdeal O₂ := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, hf,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal P O₂, ← Ideal.map_map]
    congr 1
    rw [hP, ← hmap, Ideal.map_map]
    change Ideal.map _ (Ideal.map MvPolynomial.C la.asIdeal) = _
    rw [Ideal.map_map]
    congr 1
    ext a
    simp
  refine ⟨f, hf', ?_, ?_, hmax, ?_⟩
  · haveI := Op_isDVR D N la
    algebraize [f]
    have : Module.IsTorsionFree (Op D N la) O₂ := by
      rw [Module.isTorsionFree_iff_algebraMap_injective]
      exact hfinj
    unfold RingHom.Flat
    infer_instance
  · refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : f a ∈ maximalIdeal O₂ := hmax ▸ Ideal.mem_map_of_mem f ((mem_maximalIdeal a).2 hna)
    exact (mem_maximalIdeal _).1 h1 ha
  · intro x
    obtain ⟨⟨p, s⟩, h⟩ := IsLocalization.surj P.primeCompl x
    obtain ⟨p₀, hp⟩ := exists_mvPolynomial_sub_map_mem (algebraMap (𝓞 K) O₁) _ hres p
    obtain ⟨s₀, hs⟩ := exists_mvPolynomial_sub_map_mem (algebraMap (𝓞 K) O₁) _ hres
      (s : MvPolynomial (TVar D N) O₁)
    rw [← hP] at hp hs
    have hs₀ : s₀ ∈ (laT D N la).primeCompl := by
      intro h0
      apply s.2
      have := P.add_mem hs ((hmem _).2 h0)
      simpa using this
    obtain ⟨u, hu'⟩ := IsLocalization.map_units (Op D N la) ⟨s₀, hs₀⟩
    refine ⟨algebraMap (OT K D N) (Op D N la) p₀ * ↑u⁻¹, ?_⟩
    have hm : ∀ q ∈ P, algebraMap (MvPolynomial (TVar D N) O₁) O₂ q ∈ maximalIdeal O₂ := by
      intro q hq
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P O₂]
      exact Ideal.mem_map_of_mem _ hq
    have h1 := hm _ hp
    have h2 := hm _ hs
    rw [map_sub, ← hf'] at h1 h2
    simp only at h hu'
    rw [← hu'] at h2
    have h3 : f u * f ↑u⁻¹ = 1 := by rw [← map_mul]; simp
    have h4 := Ideal.mul_mem_right (f ↑u⁻¹) _
      (Ideal.sub_mem _ h1 (Ideal.mul_mem_left _ x h2))
    convert h4 using 1
    rw [map_mul, ← h]
    linear_combination (-x) * h3

end GlobalTheory
end
