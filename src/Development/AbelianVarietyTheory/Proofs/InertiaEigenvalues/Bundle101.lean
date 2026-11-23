module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle058
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle080
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Field.ProperSpace
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.Int.Interval
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Congr

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.TransportSD

theorem map_map_equiv_left {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (e : α ≃ᵐ β) (g : β → γ) : (μ.map e).map g = μ.map (g ∘ e) := by
  by_cases hg : AEMeasurable g (μ.map e)
  · exact AEMeasurable.map_map_of_aemeasurable hg e.measurable.aemeasurable
  · have hg' : ¬ AEMeasurable (g ∘ e) μ := by rwa [← aemeasurable_map_equiv_iff e]
    by_cases hμ : μ = 0
    · simp [hμ]
    · have heμ : Measure.map e μ ≠ 0 := (Measure.map_ne_zero_iff e.measurable.aemeasurable).mpr hμ
      rw [Measure.map_of_not_aemeasurable_of_ne_zero hg heμ,
        Measure.map_of_not_aemeasurable_of_ne_zero hg' hμ]

open scoped Classical in
theorem map_map_equiv_right {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (T : α → β) (e : β ≃ᵐ γ) :
    (if AEMeasurable T μ then μ.map T else 0).map e =
      (if AEMeasurable (e ∘ T) μ then μ.map (e ∘ T) else 0) := by
  by_cases hT : AEMeasurable T μ
  · have hT' := e.measurable.comp_aemeasurable hT
    simpa only [if_pos hT, if_pos hT'] using
      AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable hT
  · have hT' : ¬ AEMeasurable (e ∘ T) μ := by
      intro h
      apply hT
      have := e.symm.measurable.comp_aemeasurable h
      simpa [Function.comp_def] using this
    simp only [if_neg hT, if_neg hT', Measure.map_zero]

end GlobalTheory.TransportSD

open GlobalTheory.TransportSD in
theorem GlobalTheory.transport_selfDual_fourB :
    ∀ {V V' : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [AddCommGroup V'] [TopologicalSpace V'] [MeasurableSpace V'] [BorelSpace V']
    (h : V' ≃+ V), Continuous h → Continuous h.symm → ∀ (μ : Measure V) (B : V → V → ℂ),
    (SelfDual μ B ∧ (∀ x : V, AEMeasurable (x + ·) μ) →
      SelfDual (Measure.map h.symm μ) (fun x y => B (h x) (h y)) ∧
        (∀ x : V', AEMeasurable (x + ·) (Measure.map h.symm μ))) ∧
    ∀ (f : V' → ℂ) (y : V'),
      fourB (Measure.map h.symm μ) (fun x y => B (h x) (h y)) f y =
        fourB μ B (fun v => f (h.symm v)) (h y) := by
  intro V V' _ _ _ _ _ _ _ _ h hc hs μ B
  let he : V ≃ₜ V' := { toEquiv := h.symm.toEquiv, continuous_toFun := hs, continuous_invFun := hc }
  let e : V ≃ᵐ V' := he.toMeasurableEquiv
  have he_eq : (e : V → V') = h.symm := rfl
  have hμ : Measure.map h.symm μ = Measure.map e μ := by rw [he_eq]
  have four : ∀ (f : V' → ℂ) (y : V'), fourB (Measure.map h.symm μ) (fun x y => B (h x) (h y)) f y = fourB μ B (fun v => f (h.symm v)) (h y) := by
    intro f y
    unfold fourB
    rw [hμ, integral_map_equiv]
    congr 1
    funext v
    rw [he_eq]
    simp
  -- The old zero fallback in `Measure.map` made left invariance imply AE measurability.
  refine ⟨fun ⟨hsd, hAe⟩ => ?_, four⟩
  have hcomp (x' : V') :
      (fun y' => x' + y') ∘ (e : V → V') = (e : V → V') ∘ (fun v => h x' + v) := by
    funext v; rw [he_eq]; simp
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · obtain ⟨hH, -⟩ := hsd
    rw [hμ]
    have h1 : IsFiniteMeasureOnCompacts (Measure.map e μ) := by
      refine ⟨fun K hK => ?_⟩
      rw [MeasurableEquiv.map_apply]
      have : (e : V → V') ⁻¹' K = h '' K := by
        ext v; rw [he_eq]; simp [Set.mem_image]
        constructor
        · intro hv; exact ⟨h.symm v, hv, by simp⟩
        · rintro ⟨w, hw, rfl⟩; simpa using hw
      rw [this]
      exact (hK.image hc).measure_lt_top
    have h2 : (Measure.map e μ).IsAddLeftInvariant := by
      refine ⟨fun x' => ?_⟩
      rw [map_map_equiv_left, hcomp,
        ← AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable (hAe (h x')),
        hH.toIsAddLeftInvariant.map_add_left_eq_self (h x')]
    have h3 : (Measure.map e μ).IsOpenPosMeasure := by
      refine ⟨fun U hU hne => ?_⟩
      rw [MeasurableEquiv.map_apply]
      have hU' : IsOpen ((e : V → V') ⁻¹' U) := hU.preimage (by rw [he_eq]; exact hs)
      have hne' : ((e : V → V') ⁻¹' U).Nonempty := by
        obtain ⟨u, hu⟩ := hne
        exact ⟨h u, by rw [he_eq]; simpa using hu⟩
      exact hU'.measure_ne_zero μ hne'
    exact { toIsFiniteMeasureOnCompacts := h1, toIsAddLeftInvariant := h2, toIsOpenPosMeasure := h3 }
  · intro f hf y
    have hf' : IsTest (fun v => f (h.symm v)) :=
      ⟨hf.1.comp_continuous hs, hf.2.comp_homeomorph he⟩
    rw [four]
    have : (fun v => fourB (Measure.map h.symm μ) (fun x y => B (h x) (h y)) f (h.symm v)) =
        fourB μ B (fun v => f (h.symm v)) := by
      funext v; rw [four]; simp
    rw [this, hsd.2 _ hf' (h y)]
    simp
  · intro x'
    rw [hμ, aemeasurable_map_equiv_iff e, hcomp]
    exact e.measurable.comp_aemeasurable (hAe (h x'))
end

section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem rho_pow_eq_card_box : ∀ (K : UQ) (B : InvAlg K) (a : K.O) (r : ℕ) (φ : B.T →* Multiplicative (Fin r → ℤ)) (c : Fin r → ℕ), Function.Surjective φ → (∀ t : B.T, φ t = 1 ↔ (t : B.Aˣ) ∈ intUnits K.O B.A) → (∀ (t : B.T) (k : ℕ), IsIntegral K.O ((((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) ↔ ∀ i, |Multiplicative.toAdd (φ t) i| ≤ ((k * c i : ℕ) : ℤ)) → ∀ k : ℕ, B.rho (algebraMap K.O B.A a ^ k) = ∏ i, (2 * k * c i + 1) := by
  intro K B a r φ c hφ hker hint k
  have hK : (intUnits K.O B.A).subgroupOf B.T = φ.ker := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hker]
  unfold InvAlg.rho
  rw [hK]
  let e := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  have he : ∀ q : B.T ⧸ φ.ker, e q = φ (Quotient.out q) := by
    intro q
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  have h1 : Nat.card {q : B.T ⧸ φ.ker //
      IsIntegral K.O ((((Quotient.out q : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A)} =
      Nat.card {v : Fin r → ℤ // ∀ i, v i ∈ Set.Icc (-((k * c i : ℕ) : ℤ)) ((k * c i : ℕ) : ℤ)} := by
    apply Nat.card_congr
    refine (e.toEquiv.trans Multiplicative.toAdd).subtypeEquiv ?_
    intro q
    simp only [MulEquiv.toEquiv_eq_coe, Equiv.trans_apply, MulEquiv.coe_toEquiv, he, Set.mem_Icc, ← abs_le]
    exact hint _ k
  rw [h1, Nat.card_congr (Equiv.subtypePiEquivPi), Nat.card_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h2 : Nat.card (Set.Icc (-((k * c i : ℕ) : ℤ)) ((k * c i : ℕ) : ℤ)) = 2 * k * c i + 1 := by
    rw [Nat.card_eq_card_toFinset, Set.toFinset_Icc, Int.card_Icc, show 2 * k * c i = 2 * (k * c i) by ring]
    omega
  exact h2

end GlobalTheory.UnitLemma
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.SqrtNearOne

theorem exists_sq_eq_inv_near_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), ∀ U ∈ 𝓝 (1 : A.K), ∀ᶠ v in 𝓝 (1 : A.K), ∃ s ∈ U, ∃ s' ∈ U, s * s' = 1 ∧ s ^ 2 = v := by
  intro F E _ _ _ _ hU A U hUm
  haveI : CharZero F := hU.charZero
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  let V := Fin (Module.finrank F A.K) → F
  let b := Module.finBasis F A.K
  let eL : A.K ≃ₗ[F] V := b.equivFun
  have hc : Continuous eL := IsModuleTopology.continuous_of_linearMap eL.toLinearMap
  have hcs : Continuous eL.symm := IsModuleTopology.continuous_of_linearMap eL.symm.toLinearMap
  let L₂ : V →ₗ[F] V →ₗ[F] V := LinearMap.mk₂ F (fun x y => eL (eL.symm x * eL.symm y))
    (by intros; simp [add_mul]) (by intros; simp [smul_mul_assoc])
    (by intros; simp [mul_add]) (by intros; simp [mul_smul_comm])
  let B : V →L[F] V →L[F] V :=
    LinearMap.toContinuousLinearMap ((LinearMap.toContinuousLinearMap : (V →ₗ[F] V) ≃ₗ[F] (V →L[F] V)).toLinearMap ∘ₗ L₂)
  have hB : ∀ x y, B x y = eL (eL.symm x * eL.symm y) := fun x y => rfl
  let H : V × V → V × V := fun p => (B p.1 p.1, B p.1 p.2)
  let p0 : V × V := (eL 1, eL 1)
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  let D : (V × V) ≃L[F] (V × V) := ContinuousLinearEquiv.equivOfInverse
    (((2 : F) • ContinuousLinearMap.fst F V V).prod (ContinuousLinearMap.fst F V V + ContinuousLinearMap.snd F V V))
    (((2 : F)⁻¹ • ContinuousLinearMap.fst F V V).prod (ContinuousLinearMap.snd F V V - (2 : F)⁻¹ • ContinuousLinearMap.fst F V V))
    (by intro p; ext1 <;> simp [smul_smul, h2])
    (by intro p; ext1 <;> simp [smul_smul, h2] <;> abel)
  have hd1 : HasStrictFDerivAt (fun p : V × V => B p.1 p.1)
      ((B p0.1).comp (ContinuousLinearMap.fst F V V) + ((B.comp (ContinuousLinearMap.fst F V V))).flip p0.1) p0 := by
    have := ((B.comp (ContinuousLinearMap.fst F V V))).hasStrictFDerivAt (x := p0)
    exact this.clm_apply (ContinuousLinearMap.fst F V V).hasStrictFDerivAt
  have hd2 : HasStrictFDerivAt (fun p : V × V => B p.1 p.2)
      ((B p0.1).comp (ContinuousLinearMap.snd F V V) + ((B.comp (ContinuousLinearMap.fst F V V))).flip p0.2) p0 := by
    have := ((B.comp (ContinuousLinearMap.fst F V V))).hasStrictFDerivAt (x := p0)
    exact this.clm_apply (ContinuousLinearMap.snd F V V).hasStrictFDerivAt
  have hd : HasStrictFDerivAt H (D : V × V →L[F] V × V) p0 := by
    refine (hd1.prodMk hd2).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun q => Prod.ext ?_ ?_
    · simp [D, p0, hB, two_smul]
    · simp [D, p0, hB]; exact add_comm _ _
  have hmap := hd.map_nhds_eq_of_equiv
  have hH0 : H p0 = p0 := by simp [H, p0, hB]
  rw [hH0] at hmap
  have hU' : eL.symm ⁻¹' U ∈ 𝓝 (eL 1) := hcs.continuousAt.preimage_mem_nhds (by simpa using hUm)
  have himg : H '' ((eL.symm ⁻¹' U) ×ˢ (eL.symm ⁻¹' U)) ∈ 𝓝 p0 := by
    rw [← hmap]; exact image_mem_map (prod_mem_nhds hU' hU')
  have hg : Continuous fun v : A.K => ((eL v, eL 1) : V × V) := hc.prodMk continuous_const
  have hev := hg.continuousAt (x := (1 : A.K)) |>.preimage_mem_nhds (t := H '' ((eL.symm ⁻¹' U) ×ˢ (eL.symm ⁻¹' U))) himg
  filter_upwards [hev] with v hv
  obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, hxy⟩ := hv
  simp only [H, hB, Prod.mk.injEq] at hxy
  refine ⟨eL.symm x, hx, eL.symm y, hy, eL.injective hxy.2, ?_⟩
  rw [sq]; exact eL.injective hxy.1

end GlobalTheory.JR.SqrtNearOne
end

section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.LinPair

theorem exists_smul_mem_of_mem_span (K : UQ) {V : Type} [AddCommGroup V] [Module K.E V] [Module K.O V]
    [IsScalarTower K.O K.E V] (M : Submodule K.O V) {x : V} (hx : x ∈ Submodule.span K.E (M : Set V)) :
    ∃ d : K.O, d ≠ 0 ∧ d • x ∈ M := by
  first
  | exact @_root_.GlobalTheory.ClearDenominatorsIntegral.main
  | exact _root_.GlobalTheory.ClearDenominatorsIntegral.main
  | (apply _root_.GlobalTheory.ClearDenominatorsIntegral.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClearDenominatorsIntegral.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClearDenominatorsIntegral.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClearDenominatorsIntegral.main ..)

end GlobalTheory.UnitLemma.LinPair

open GlobalTheory.UnitLemma.LinPair in
theorem GlobalTheory.UnitLemma.InvAlg.lin_fst_snd : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (M : Submodule K.O (B₁.A × B₂.A)),
    M ∈ (B₁.prod B₂).Lin →
    M.comap (LinearMap.inl K.O B₁.A B₂.A) ∈ B₁.Lin ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) ∈ B₂.Lin := by
  intro K B₁ B₂ M hM
  obtain ⟨⟨hfg, hspan⟩, hg, hσ⟩ := hM
  have hg' : ∀ y ∈ M, ((B₁.g * y.1, B₂.g * y.2) : B₁.A × B₂.A) ∈ M := fun y hy => hg y hy
  have hσ' : ∀ y ∈ M, ((B₁.σ y.1, B₂.σ y.2) : B₁.A × B₂.A) ∈ M := fun y hy => hσ y hy
  replace hspan : Submodule.span K.E (M : Set (B₁.A × B₂.A)) = ⊤ := hspan
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨⟨hfg.map _, ?_⟩, ?_, ?_⟩⟩
  ·
    apply Submodule.fg_of_fg_map_injective (LinearMap.inl K.O B₁.A B₂.A) LinearMap.inl_injective
    exact isNoetherian_submodule.1 (isNoetherian_of_fg_of_noetherian M hfg) _ (Submodule.map_comap_le _ _)
  · rw [Submodule.eq_top_iff']
    intro y
    have hy : (y, (0 : B₂.A)) ∈ Submodule.span K.E (M : Set (B₁.A × B₂.A)) := by
      rw [hspan]
      exact Submodule.mem_top
    obtain ⟨d, hd, hdy⟩ := exists_smul_mem_of_mem_span K M hy
    have hdE : algebraMap K.O K.E d ≠ 0 := by
      rw [Ne, ← (algebraMap K.O K.E).map_zero]
      exact fun h => hd (IsFractionRing.injective K.O K.E h)
    have hmem : d • y ∈ M.comap (LinearMap.inl K.O B₁.A B₂.A) := by
      simpa [Submodule.mem_comap] using hdy
    refine (Submodule.smul_mem_iff _ hdE).mp ?_
    rw [algebraMap_smul]
    exact Submodule.subset_span hmem
  · intro y hy
    have := hg' _ hy
    simpa [Submodule.mem_comap] using this
  · intro y hy
    have := hσ' _ hy
    simpa [Submodule.mem_comap] using this
  · rw [Submodule.map_coe]
    have : ⇑(LinearMap.snd K.O B₁.A B₂.A) = ⇑(LinearMap.snd K.E B₁.A B₂.A) := rfl
    rw [this, ← Submodule.map_span, hspan, Submodule.map_top, LinearMap.range_eq_top]
    exact LinearMap.snd_surjective
  · rintro _ ⟨m, hm, rfl⟩
    exact ⟨_, hg' m hm, rfl⟩
  · rintro _ ⟨m, hm, rfl⟩
    exact ⟨_, hσ' m hm, rfl⟩
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem finite_units_quot_sq_normed (F : Type) [NontriviallyNormedField F] [CompleteSpace F]
    [ProperSpace F] [CharZero F] (R : Type) [NormedCommRing R] [Nontrivial R] [NormedAlgebra F R]
    [Module.Finite F R] (hR : ∀ x : R, x ≠ 0 → IsUnit x) :
    Finite (Rˣ ⧸ (powMonoidHom 2 : Rˣ →* Rˣ).range) := by
  classical
  obtain ⟨-, hsq⟩ := isOpenUnits_and_eventually_sq_normed F R
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hsq
  obtain ⟨b, hb0, hb1⟩ := NormedField.exists_norm_lt_one F
  have hρ2 : 0 < ‖b‖ ^ 2 := by positivity
  have : ProperSpace R := FiniteDimensional.proper F R
  let C : Set R := {x | ‖b‖ ^ 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1}
  have hCc : IsCompact C := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    · exact (Metric.isBounded_closedBall (x := (0 : R)) (r := 1)).subset
        (fun x hx => by simpa using hx.2)
  have hCu : ∀ c ∈ C, IsUnit c := fun c hc => hR c (by
    intro h
    have h1 := hc.1
    rw [h, norm_zero] at h1
    linarith)
  obtain ⟨t, htC, hcov⟩ := hCc.elim_nhds_subcover
    (fun c => {x : R | dist (x * Ring.inverse c) 1 < ε}) (by
      intro c hc
      apply IsOpen.mem_nhds
      · exact isOpen_lt (by fun_prop) continuous_const
      · simp [Ring.mul_inverse_cancel _ (hCu c hc), hε])
  let f : R → Rˣ ⧸ (powMonoidHom 2 : Rˣ →* Rˣ).range := fun x =>
    if h : IsUnit x then QuotientGroup.mk h.unit else 1
  have hsurj : (Set.univ : Set (Rˣ ⧸ (powMonoidHom 2 : Rˣ →* Rˣ).range)) ⊆ f '' (t : Set R) := by
    rintro q -
    induction q using QuotientGroup.induction_on with | H u => ?_
    have hu0 : 0 < ‖(u : R)‖ := norm_pos_iff.mpr u.ne_zero
    have hy : 1 < (‖b‖ ^ 2)⁻¹ := (one_lt_inv₀ hρ2).mpr (by nlinarith [norm_nonneg b])
    obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hu0 hy
    have hb0' : b ≠ 0 := norm_pos_iff.mp hb0
    have hβ0 : b ^ (n + 1) ≠ 0 := zpow_ne_zero _ hb0'
    have hnv : ‖(b ^ (n + 1)) ^ 2 • (u : R)‖ = ‖(u : R)‖ / ((‖b‖ ^ 2)⁻¹) ^ (n + 1) := by
      rw [norm_smul, norm_pow, norm_zpow, _root_.inv_zpow, div_inv_eq_mul, mul_comm, ← zpow_natCast, ← zpow_natCast,
        ← _root_.zpow_mul, ← _root_.zpow_mul]
      rw [mul_comm (n + 1)]
    have hv : (b ^ (n + 1)) ^ 2 • (u : R) ∈ C := by
      have hpos : 0 < ((‖b‖ ^ 2)⁻¹) ^ n := zpow_pos (by positivity) n
      refine ⟨?_, ?_⟩
      · rw [hnv, zpow_add₀ (by positivity), zpow_one, le_div_iff₀ (by positivity)]
        calc ‖b‖ ^ 2 * (((‖b‖ ^ 2)⁻¹) ^ n * (‖b‖ ^ 2)⁻¹) = ((‖b‖ ^ 2)⁻¹) ^ n := by field_simp
          _ ≤ ‖(u : R)‖ := hn1.le
      · rw [hnv, div_le_one (by positivity)]
        exact hn2
    obtain ⟨c, hct, hcv⟩ := Set.mem_iUnion₂.mp (hcov hv)
    have hcu := hCu c (htC c hct)
    obtain ⟨s, hs⟩ := hball hcv
    have hsU : IsUnit s := by
      have : IsUnit (s ^ 2) := by
        have hic : Ring.inverse c = ↑(hcu.unit⁻¹) := by rw [← Ring.inverse_unit, IsUnit.unit_spec]
        rw [hs, Algebra.smul_def, hic]
        exact ((isUnit_iff_ne_zero.mpr (pow_ne_zero 2 hβ0)).map (algebraMap F R) |>.mul u.isUnit).mul
          (hcu.unit⁻¹).isUnit
      exact (isUnit_pow_iff two_ne_zero).mp this
    refine ⟨c, hct, ?_⟩
    simp only [f, dif_pos hcu]
    rw [QuotientGroup.eq, MonoidHom.mem_range]
    let bu : Rˣ := Units.map (algebraMap F R).toMonoidHom (Units.mk0 _ hβ0)
    have hs' : hsU.unit ^ 2 = bu ^ 2 * u * hcu.unit⁻¹ := by
      ext
      simp only [Units.val_pow_eq_pow_val, Units.val_mul, IsUnit.unit_spec, bu, Units.coe_map,
        Units.val_mk0]
      rw [hs, ← Ring.inverse_unit, IsUnit.unit_spec, Algebra.smul_def, map_pow]
      rfl
    refine ⟨hsU.unit * bu⁻¹, ?_⟩
    rw [powMonoidHom_apply, mul_pow, inv_pow, hs']
    simp only [mul_comm, mul_left_comm, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, mul_inv_cancel, mul_one]
  have hfin : (Set.univ : Set (Rˣ ⧸ (powMonoidHom 2 : Rˣ →* Rˣ).range)).Finite :=
    (t.finite_toSet.image f).subset hsurj
  exact Set.finite_univ_iff.mp hfin

end GlobalTheory

namespace GlobalTheory

theorem finite_units_quot_sq_field (F : Type) [NontriviallyNormedField F] [CompleteSpace F]
    [ProperSpace F] [CharZero F] (L : Type) [Field L] [Algebra F L] [Module.Finite F L] :
    Finite (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range) := by
  classical
  let b := Module.finBasis F L
  let : NormedRing (Matrix (Fin (Module.finrank F L)) (Fin (Module.finrank F L)) F) :=
    Matrix.linftyOpNormedRing
  let : NormedAlgebra F (Matrix (Fin (Module.finrank F L)) (Fin (Module.finrank F L)) F) :=
    Matrix.linftyOpNormedAlgebra
  let N : NormedCommRing L := NormedCommRing.induced L _ (Algebra.leftMulMatrix b)
    (Algebra.leftMulMatrix_injective b)
  let A : @NormedAlgebra F L _ N.toNormedRing.toSeminormedRing :=
    NormedAlgebra.induced F L _ (Algebra.leftMulMatrix b)
  exact @finite_units_quot_sq_normed F _ _ _ _ L N inferInstance A ‹_› (fun x hx => hx.isUnit)

theorem finite_units_quot_sq_reduced (F : Type) [NontriviallyNormedField F] [CompleteSpace F]
    [ProperSpace F] [CharZero F] (K : Type) [CommRing K] [Algebra F K] [Module.Finite F K]
    [IsReduced K] : Finite (Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range) := by
  classical
  have : IsArtinianRing K := IsArtinianRing.of_finite F K
  letI (I : MaximalSpectrum K) : Field (K ⧸ I.asIdeal) :=
    @Ideal.Quotient.field _ _ I.asIdeal I.isMaximal
  have hfin (I : MaximalSpectrum K) :
      Finite ((K ⧸ I.asIdeal)ˣ ⧸ (powMonoidHom 2 : (K ⧸ I.asIdeal)ˣ →* (K ⧸ I.asIdeal)ˣ).range) :=
    finite_units_quot_sq_field F (K ⧸ I.asIdeal)
  let φ : Kˣ →* ∀ I : MaximalSpectrum K,
      (K ⧸ I.asIdeal)ˣ ⧸ (powMonoidHom 2 : (K ⧸ I.asIdeal)ˣ →* (K ⧸ I.asIdeal)ˣ).range :=
    Pi.monoidHom fun I => (QuotientGroup.mk' _).comp
      (Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom)
  have hker : φ.ker = (powMonoidHom 2 : Kˣ →* Kˣ).range := by
    ext u
    simp only [MonoidHom.mem_ker, MonoidHom.mem_range, powMonoidHom_apply]
    constructor
    · intro hu
      have hI (I : MaximalSpectrum K) : ∃ s : (K ⧸ I.asIdeal)ˣ,
          s ^ 2 = Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom u := by
        have := congrFun hu I
        change ((Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom u : (K ⧸ I.asIdeal)ˣ) :
          (K ⧸ I.asIdeal)ˣ ⧸ (powMonoidHom 2 : (K ⧸ I.asIdeal)ˣ →* (K ⧸ I.asIdeal)ˣ).range) = 1 at this
        rw [QuotientGroup.eq_one_iff] at this
        obtain ⟨s, hs⟩ := this
        exact ⟨s, hs⟩
      choose s hs using hI
      let e := IsArtinianRing.equivPi K
      let x : K := e.symm fun I => (s I : K ⧸ I.asIdeal)
      let y : K := e.symm fun I => ((s I)⁻¹ : (K ⧸ I.asIdeal)ˣ)
      have hxy : x * y = 1 := e.injective (by
        rw [map_mul, map_one]
        funext I
        simp [x, y])
      refine ⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, ?_⟩
      ext
      apply e.injective
      funext I
      have := congrArg Units.val (hs I)
      simp only [Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe] at this
      simp [x, this] <;> rfl
    · rintro ⟨w, rfl⟩
      funext I
      change ((Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom (w ^ 2) : (K ⧸ I.asIdeal)ˣ) :
        (K ⧸ I.asIdeal)ˣ ⧸ (powMonoidHom 2 : (K ⧸ I.asIdeal)ˣ →* (K ⧸ I.asIdeal)ˣ).range) = 1
      rw [QuotientGroup.eq_one_iff, map_pow]
      exact ⟨_, rfl⟩
  have := Finite.of_injective _ (QuotientGroup.kerLift_injective φ)
  rw [hker] at this
  exact this

theorem Et.finite_units_quot_sq : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E),
    Finite (A.Kˣ ⧸ (powMonoidHom 2 : A.Kˣ →* A.Kˣ).range) := by
  intro F E _ _ _ _ hU A
  have : CharZero F := hU.charZero
  have : LocallyCompactSpace F := hU.lcF
  have : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  exact finite_units_quot_sq_reduced F A.K

end GlobalTheory
end
