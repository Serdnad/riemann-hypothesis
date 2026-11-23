module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle265
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeTwoMulOfForallScale
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle268
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle004
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix ValuativeRel
open scoped NNReal Topology Pointwise

namespace GlobalTheory.WeilM

theorem eq_zero_of_mul_invariant {X : Type} [TopologicalSpace X] (l : (X → ℂ) →ₗ[ℂ] ℂ) (S : Set (X → ℂ))
    (hS : ∀ f ∈ S, IsLocallyConstant f) (hl : ∀ f ∈ S, ∀ φ ∈ SB X, l (f * φ) = l φ)
    {φ : X → ℂ} (hφ : φ ∈ SB X) (h : ∀ x, φ x ≠ 0 → ∃ f ∈ S, f x ≠ 1) : l φ = 0 := by
  have hind : ∀ U : Set X, IsClopen U → ∀ φ ∈ SB X, U.indicator φ ∈ SB X := by
    intro U hU φ hφ
    have : U.indicator φ = U.indicator 1 * φ := by
      funext x; by_cases hx : x ∈ U <;> simp [hx]
    rw [this]
    exact ⟨(LocallyConstant.indicator (1 : LocallyConstant X ℂ) hU).isLocallyConstant.mul hφ.1, hφ.2.mul_left⟩
  have hsupp : IsClopen (Function.support φ) := (hφ.1.isClopen_fiber 0).compl
  have hc : IsCompact (Function.support φ) := by
    have := hφ.2
    rwa [HasCompactSupport, tsupport, hsupp.isClosed.closure_eq] at this
  have key : ∃ U : Set X, IsClopen U ∧ Function.support φ ⊆ U ∧
      ∀ φ' ∈ SB X, Function.support φ' ⊆ U → l φ' = 0 := by
    refine hc.induction_on (p := fun s => ∃ U : Set X, IsClopen U ∧ s ⊆ U ∧
      ∀ φ' ∈ SB X, Function.support φ' ⊆ U → l φ' = 0) ?_ ?_ ?_ ?_
    · refine ⟨∅, isClopen_empty, le_rfl, fun φ' _ h0 => ?_⟩
      rw [Set.subset_empty_iff, Function.support_eq_empty_iff] at h0
      rw [h0, map_zero]
    · rintro s t hst ⟨U, hU, htU, h'⟩
      exact ⟨U, hU, hst.trans htU, h'⟩
    · rintro s t ⟨U, hU, hsU, h1⟩ ⟨V, hV, htV, h2⟩
      refine ⟨U ∪ V, hU.union hV, Set.union_subset_union hsU htV, fun φ' hφ' hs => ?_⟩
      rw [← Set.indicator_self_add_compl U φ', map_add (f := _), h1 _ (hind U hU _ hφ') Set.support_indicator_subset,
        h2 _ (hind _ hU.compl _ hφ'), add_zero]
      rw [Set.support_indicator]
      rintro x ⟨hx, hx'⟩
      exact (hs hx').resolve_left hx
    · intro x hx
      obtain ⟨f, hf, hfx⟩ := h x hx
      have hU := (hS f hf).isClopen_fiber (f x)
      refine ⟨_, mem_nhdsWithin_of_mem_nhds (hU.isOpen.mem_nhds rfl), _, hU, le_rfl, fun φ' hφ' hs => ?_⟩
      have h1 : f * φ' = f x • φ' := by
        funext y
        by_cases hy : φ' y = 0
        · simp [hy]
        · have : f y = f x := hs hy
          simp [this]
      have h2 := hl f hf φ' hφ'
      rw [h1, map_smul, smul_eq_mul] at h2
      have h3 : (f x - 1) * l φ' = 0 := by rw [sub_mul, h2, one_mul, sub_self]
      exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hfx)
  obtain ⟨U, -, hU, h'⟩ := key
  exact h' φ hφ hU

theorem eq_one_of_forall_pow_near {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.PowerTwoNormLowerBound.main
  | exact _root_.GlobalTheory.PowerTwoNormLowerBound.main
  | (apply _root_.GlobalTheory.PowerTwoNormLowerBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerTwoNormLowerBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerTwoNormLowerBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerTwoNormLowerBound.main ..)

theorem isLocallyConstant_addChar {V : Type} [AddCommGroup V] [TopologicalSpace V] [NonarchimedeanAddGroup V]
    (ψ : AddChar V ℂ) (hψ : Continuous ψ) : IsLocallyConstant ψ := by
  have h0 : {x | ‖ψ x - 1‖ < 1 / 2} ∈ 𝓝 (0 : V) :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)
  obtain ⟨K, hK⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ h0
  have h1 : ∀ x ∈ K, ψ x = 1 := fun x hx => eq_one_of_forall_pow_near fun n => by
    rw [← AddChar.map_nsmul_eq_pow]
    exact hK (nsmul_mem hx n)
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  have : (fun z => -x + z) ⁻¹' (K : Set V) ∈ 𝓝 x :=
    (K.isOpen.preimage (by fun_prop)).mem_nhds (by simp)
  filter_upwards [this] with z hz
  have h2 : z = x + (-x + z) := by abel
  rw [h2, AddChar.map_add_eq_mul, h1 _ hz, mul_one]

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem nonarch_field : NonarchimedeanAddGroup F where
  is_nonarchimedean U hU := by
    obtain ⟨s, hs⟩ := SplitWeil.exists_cball_subset hU
    exact ⟨⟨⟨⟨⟨SplitWeil.cball s, SplitWeil.add_mem_cball⟩, by simp [SplitWeil.cball]⟩, SplitWeil.neg_mem_cball⟩,
      SplitWeil.isOpen_cball s⟩, hs⟩

theorem nonarch_pi (κ : Type) [Fintype κ] : NonarchimedeanAddGroup (κ → F) where
  is_nonarchimedean U hU := by
    haveI := nonarch_field F
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, -, t, ht, hs⟩ := hU
    choose K hK using fun i => NonarchimedeanAddGroup.is_nonarchimedean (G := F) (t i) (ht i)
    exact ⟨⟨AddSubgroup.pi Set.univ fun i => (K i : AddSubgroup F),
      isOpen_set_pi Set.finite_univ fun i _ => (K i).isOpen⟩, fun x hx => hs fun i _ => hK i (hx i trivial)⟩

section Cov

variable {F} [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
  {κ : Type} [Fintype κ] [DecidableEq κ]

theorem smul_map_mulVec_pi (M : Matrix κ κ F) (u : Fˣ) (hu : (u : F) = M.det) :
    (distribHaarChar F u : ENNReal) • Measure.map M.mulVec (Measure.pi fun _ : κ => ν) = Measure.pi fun _ : κ => ν := by
  haveI := SplitWeil.secondCountable F
  haveI := SplitWeil.t2Space F
  have hm : ∀ A : Matrix κ κ F, Measurable A.mulVec := fun A =>
    (continuous_const.matrix_mulVec continuous_id).measurable
  have hM : M.det ≠ 0 := hu ▸ u.ne_zero
  revert u
  apply diagonal_transvection_induction_of_det_ne_zero _ M hM
  · intro D hD u hu
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [det_diagonal] at hD hu
    have A : ∀ i, D i ≠ 0 := fun i => Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
    have hu' : u = ∏ i, Units.mk0 (D i) (A i) := Units.ext (by simp [hu])
    rw [Measure.smul_apply, Measure.map_apply (hm _) (MeasurableSet.univ_pi hs)]
    have : ((diagonal D).mulVec ⁻¹' Set.pi Set.univ fun i : κ => s i) =
        Set.pi Set.univ fun i : κ => (Units.mk0 (D i) (A i))⁻¹ • s i := by
      ext f
      simp only [Set.mem_preimage, Set.mem_univ_pi, mulVec_diagonal]
      exact forall_congr' fun i => (Set.mem_inv_smul_set_iff (a := Units.mk0 (D i) (A i))).symm
    rw [this, Measure.pi_pi, hu', map_prod, ENNReal.ofNNReal_finsetProd, smul_eq_mul, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [distribHaarChar_mul, smul_inv_smul]
  · intro t u hu
    have hu' : u = 1 := Units.ext (by simp [hu])
    rw [hu', map_one, ENNReal.coe_one, one_smul]
    refine (Measure.pi_eq fun s hs ↦ ?_).symm
    have h2s : MeasurableSet (Set.univ.pi s) := .pi Set.countable_univ fun i _ ↦ hs i
    simp_rw [← Measure.pi_pi, ← lintegral_indicator_one h2s]
    rw [lintegral_map (measurable_one.indicator h2s) (hm _)]
    refine lintegral_eq_of_lmarginal_eq {t.i} ((measurable_one.indicator h2s).comp (hm _))
      (measurable_one.indicator h2s) ?_
    simp_rw [lmarginal_singleton]
    ext x
    cases t with | mk t_i t_j t_hij t_c =>
    simp [transvection, add_mulVec, single_mulVec, t_hij.symm, ← Function.update_add,
      lintegral_add_right_eq_self fun xᵢ ↦ Set.indicator (Set.univ.pi s) 1 (Function.update x t_i xᵢ)]
  · intro A B hA hB IHA IHB u hu
    have hu' : u = Units.mk0 _ hA * Units.mk0 _ hB := Units.ext (by simp [hu])
    have e : (A * B).mulVec = A.mulVec ∘ B.mulVec := funext fun x => (mulVec_mulVec x A B).symm
    rw [hu', map_mul, ENNReal.coe_mul, mul_smul, e, ← Measure.map_map (hm _) (hm _), ← Measure.map_smul,
      IHB _ rfl, IHA _ rfl]
    exact (hm A).aemeasurable

theorem integral_comp_mulVec (g : GL κ F) (f : (κ → F) → ℂ) :
    ((distribHaarChar F (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) *
      ∫ x, f (g.val.mulVec x) ∂(Measure.pi fun _ : κ => ν) = ∫ x, f x ∂(Measure.pi fun _ : κ => ν) := by
  haveI := SplitWeil.secondCountable F
  have hm : ∀ A : Matrix κ κ F, Measurable A.mulVec := fun A =>
    (continuous_const.matrix_mulVec continuous_id).measurable
  let e : (κ → F) ≃ᵐ (κ → F) :=
    { toFun := g.val.mulVec, invFun := (g⁻¹).val.mulVec
      left_inv := fun x => by rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
      right_inv := fun x => by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
      measurable_toFun := hm _, measurable_invFun := hm _ }
  conv_rhs => rw [← smul_map_mulVec_pi ν g.val (Matrix.GeneralLinearGroup.det g) rfl, integral_smul_measure]
  rw [show g.val.mulVec = e from rfl, integral_map_equiv]
  simp

end Cov

end GlobalTheory.WeilM

end
end

section

open GlobalTheory.LKTrip

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.MaxIdealTensorPadic

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

theorem conjT_conjT (y : ℚ_[p] ⊗[ℚ] G.F) : conjT G.F ℚ_[p] (conjT G.F ℚ_[p] y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [conjT_tmul, NumberField.IsCMField.complexConj_apply_apply]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem eq_sigma_liftW (f : ℚ_[p] ⊗[ℚ] G.F →+* PadicAlgCl p)
    (hf : ∀ a : ℚ_[p], f (a ⊗ₜ 1) = algebraMap ℚ_[p] (PadicAlgCl p) a)
    (i : Fin G.m) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (h : ∀ x : G.F, f (1 ⊗ₜ x) = σ (G.emb i x)) (y : ℚ_[p] ⊗[ℚ] G.F) :
    f y = σ ((G.liftW i y : G.Fw i) : PadicAlgCl p) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have e : (a ⊗ₜ[ℚ] x : ℚ_[p] ⊗[ℚ] G.F) = (a ⊗ₜ 1) * (1 ⊗ₜ x) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [e, map_mul, hf, h, map_mul, MulMemClass.coe_mul, map_mul]
    congr 1
    · simp [HTGroup.liftW, Algebra.TensorProduct.lift_tmul, HTGroup.embW]
    · congr 1
      simp only [HTGroup.liftW, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      rfl
  | add x y hx hy => rw [map_add (f := _), hx, hy, map_add (f := _), AddMemClass.coe_add, map_add (f := _)]

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (M : Ideal (TensorProduct ℚ ℚ_[p] G.F)), M.IsMaximal →
    ∃ i : Fin G.m, M = RingHom.ker (G.liftW i) ∨
      M = RingHom.ker ((G.liftW i).toRingHom.comp (conjT G.F ℚ_[p])) := by
  intro p _ G M hM
  letI : Field ((ℚ_[p] ⊗[ℚ] G.F) ⧸ M) := Ideal.Quotient.field M
  haveI : Module.Finite ℚ_[p] ((ℚ_[p] ⊗[ℚ] G.F) ⧸ M) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℚ_[p] M).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Algebra.IsAlgebraic ℚ_[p] ((ℚ_[p] ⊗[ℚ] G.F) ⧸ M) := Algebra.IsAlgebraic.of_finite _ _
  let ι : ((ℚ_[p] ⊗[ℚ] G.F) ⧸ M) →ₐ[ℚ_[p]] PadicAlgCl p := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let f : ℚ_[p] ⊗[ℚ] G.F →+* PadicAlgCl p := (ι.comp (Ideal.Quotient.mkₐ ℚ_[p] M)).toRingHom
  have hker : ∀ y, y ∈ M ↔ f y = 0 := by
    intro y
    show y ∈ M ↔ ι (Ideal.Quotient.mk M y) = 0
    rw [map_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
  have hf : ∀ a : ℚ_[p], f (a ⊗ₜ 1) = algebraMap ℚ_[p] (PadicAlgCl p) a := fun a =>
    (ι.comp (Ideal.Quotient.mkₐ ℚ_[p] M)).commutes a
  let τ : G.F →+* PadicAlgCl p := f.comp (Algebra.TensorProduct.includeRight : G.F →ₐ[ℚ] _).toRingHom
  rcases GlobalTheory.T.padicEmbedding_liesOver_or_complexConj_liesOver p G τ with hτ | hτ
  · obtain ⟨i, σ, hσ⟩ := G.emb_all τ hτ
    refine ⟨i, Or.inl ?_⟩
    have h : ∀ x : G.F, f (1 ⊗ₜ x) = σ (G.emb i x) := fun x => RingHom.congr_fun hσ x
    ext y
    rw [hker, RingHom.mem_ker, eq_sigma_liftW G f hf i σ h y, map_eq_zero_iff _ σ.injective]
    exact ZeroMemClass.coe_eq_zero
  · obtain ⟨i, σ, hσ⟩ := G.emb_all _ hτ
    refine ⟨i, Or.inr ?_⟩
    let g : ℚ_[p] ⊗[ℚ] G.F →+* PadicAlgCl p := f.comp (conjT G.F ℚ_[p])
    have hg : ∀ a : ℚ_[p], g (a ⊗ₜ 1) = algebraMap ℚ_[p] (PadicAlgCl p) a := fun a => by
      simp only [g, RingHom.comp_apply, conjT_tmul, map_one, hf]
    have h : ∀ x : G.F, g (1 ⊗ₜ x) = σ (G.emb i x) := fun x => RingHom.congr_fun hσ x
    ext y
    have e : f y = g (conjT G.F ℚ_[p] y) := by simp only [g, RingHom.comp_apply, conjT_conjT]
    rw [hker, e, eq_sigma_liftW G g hg i σ h, map_eq_zero_iff _ σ.injective, RingHom.mem_ker]
    exact ZeroMemClass.coe_eq_zero

end GlobalTheory.MaxIdealTensorPadic
end
end

section

open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

noncomputable section

namespace GlobalTheory.ConnPointwise

variable {g : ℕ}

theorem gnorm_one_eq (v : Fin g → ℂ) : gnorm 1 v = √(∑ a, ‖v a‖ ^ 2) := by
  rw [gnorm, form_eq_sum]
  congr 1
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ofReal_re]

theorem opNorm_one_le_of_entry (M : Matrix (Fin g) (Fin g) ℂ) {E : ℝ} (hE : 0 ≤ E)
    (h : ∀ j k, ‖M j k‖ ≤ E) : opNorm 1 1 M ≤ g * E := by
  refine opNorm_le_of_bound (by positivity) fun v => ?_
  rw [gnorm_one_eq, gnorm_one_eq]
  set S := ∑ a, ‖v a‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hrw : (g : ℝ) * E * √S = √(((g : ℝ) * E) ^ 2 * S) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  rw [hrw]
  apply Real.sqrt_le_sqrt
  have hrow : ∀ j, ‖(M *ᵥ v) j‖ ^ 2 ≤ E ^ 2 * (g * S) := fun j => by
    have h1 : ‖(M *ᵥ v) j‖ ≤ E * ∑ k, ‖v k‖ := by
      rw [Finset.mul_sum]
      simp only [mulVec, dotProduct]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (h j k) (norm_nonneg _)
    have h2 : (∑ k, ‖v k‖) ^ 2 ≤ g * S := by
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k => ‖v k‖)
      simpa [hS] using this
    calc ‖(M *ᵥ v) j‖ ^ 2 ≤ (E * ∑ k, ‖v k‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = E ^ 2 * (∑ k, ‖v k‖) ^ 2 := by ring
      _ ≤ E ^ 2 * (g * S) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  calc ∑ j, ‖(M *ᵥ v) j‖ ^ 2 ≤ ∑ _j : Fin g, E ^ 2 * (g * S) := Finset.sum_le_sum fun j _ => hrow j
    _ = ((g : ℝ) * E) ^ 2 * S := by simp; ring

theorem inv_entry_le (Y : Matrix (Fin g) (Fin g) ℝ) {c : ℝ} (hc : 0 < c)
    (hY : ∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) : IsUnit Y.det ∧ ∀ j k, |Y⁻¹ j k| ≤ 1 / c := by
  have hdet : IsUnit Y.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨x, hx, hx0⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
    have h1 := hY x
    rw [hx0, dotProduct_zero] at h1
    have h2 : x ⬝ᵥ x ≤ 0 := by nlinarith [show 0 ≤ x ⬝ᵥ x from Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)]
    apply hx
    funext i
    have h3 : ∀ i ∈ Finset.univ, 0 ≤ x i * x i := fun i _ => mul_self_nonneg _
    have := (Finset.sum_eq_zero_iff_of_nonneg h3).1 (le_antisymm h2 (Finset.sum_nonneg h3)) i (Finset.mem_univ _)
    simpa using mul_self_eq_zero.1 this
  refine ⟨hdet, fun j k => ?_⟩
  set u := Y⁻¹ *ᵥ Pi.single k 1 with hu
  have hYu : Y *ᵥ u = Pi.single k 1 := by
    rw [hu, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have hentry : Y⁻¹ j k = u j := by
    rw [hu, mulVec_single_one]; rfl
  set N := u ⬝ᵥ u with hN
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun i _ => mul_self_nonneg (u i)
  have hcomp : ∀ i, u i ^ 2 ≤ N := fun i => by
    rw [hN, dotProduct, sq]
    exact Finset.single_le_sum (f := fun i => u i * u i) (fun i _ => mul_self_nonneg (u i)) (Finset.mem_univ i)
  have h1 : c * N ≤ u k := by
    have := hY u
    rwa [hYu, dotProduct_single, mul_one] at this
  have huk : 0 ≤ u k := le_trans (mul_nonneg hc.le hN0) h1
  have h2 : c ^ 2 * N ^ 2 ≤ N := by
    calc c ^ 2 * N ^ 2 = (c * N) ^ 2 := by ring
      _ ≤ u k ^ 2 := pow_le_pow_left₀ (mul_nonneg hc.le hN0) h1 2
      _ ≤ N := hcomp k
  have h3 : c ^ 2 * N ≤ 1 := by
    rcases hN0.eq_or_lt with h | h
    · rw [← h]; simp
    · nlinarith
  have h4 : (c * u j) ^ 2 ≤ 1 := by
    calc (c * u j) ^ 2 = c ^ 2 * u j ^ 2 := by ring
      _ ≤ c ^ 2 * N := mul_le_mul_of_nonneg_left (hcomp j) (sq_nonneg c)
      _ ≤ 1 := h3
  rw [hentry, le_div_iff₀ hc, mul_comm]
  have := (sq_le_one_iff_abs_le_one _).1 h4
  rwa [abs_mul, abs_of_pos hc] at this

end GlobalTheory.ConnPointwise

namespace GlobalTheory.ConnPointwise

variable {g : ℕ}

theorem entry_le_of_mulVec (P : Matrix (Fin g) (Fin g) ℝ) {W : ℝ} (hW : 0 ≤ W)
    (h : ∀ x, ‖P *ᵥ x‖ ≤ W * ‖x‖) (j k : Fin g) : |P j k| ≤ W := by
  have h1 := h (Pi.single k 1)
  have hs : ‖(Pi.single k (1 : ℝ) : Fin g → ℝ)‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
      by_cases hi : i = k
      · subst hi; simp
      · simp [Pi.single_apply, hi]
  rw [mulVec_single_one] at h1
  calc |P j k| = ‖Pᵀ k j‖ := by simp [Real.norm_eq_abs]
    _ ≤ ‖Pᵀ k‖ := norm_le_pi_norm _ j
    _ ≤ W * ‖(Pi.single k (1 : ℝ) : Fin g → ℝ)‖ := h1
    _ ≤ W := mul_le_of_le_one_right hW hs

end GlobalTheory.ConnPointwise

namespace GlobalTheory

open GlobalTheory.ConnPointwise

theorem connMatrix_opNorm_le : ∀ (g a : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (Bs : Fin a → Matrix (Fin g) (Fin g) ℝ) (Dm : Matrix (Fin g) (Fin g) ℂ) (s : Fin a → ℂ) (t : Fin a → ℝ) (c K W : ℝ), 0 < c → 0 ≤ K → 0 ≤ W → (∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) → (∀ i, 0 < t i) → (∀ i x, ‖(t i • (Y⁻¹ * Bs i)) *ᵥ x‖ ≤ W * ‖x‖) → (∀ j k, ‖Dm j k‖ ≤ K) → opNorm 1 1 ((Y.map Complex.ofReal)⁻¹ * ((1 / (2 * Complex.I)) • (Dm + ∑ i, s i • (Bs i).map Complex.ofReal))) ≤ g * (g * K / c + W * ∑ i, ‖s i‖ / t i) := by
  intro g a Y Bs Dm s t c K W hc hK hW hY ht hB hD
  obtain ⟨hdet, hinv⟩ := inv_entry_le Y hc hY
  have hmapinv : (Y.map Complex.ofReal)⁻¹ = (Y⁻¹).map Complex.ofReal := by
    apply inv_eq_left_inv
    show (Y⁻¹).map Complex.ofRealHom * Y.map Complex.ofRealHom = 1
    rw [← Matrix.map_mul, nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBe : ∀ i j k, |(Y⁻¹ * Bs i) j k| ≤ W / t i := fun i j k => by
    have := entry_le_of_mulVec _ hW (hB i) j k
    rw [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (ht i)] at this
    rw [le_div_iff₀ (ht i), mul_comm]; exact this
  have hE0 : 0 ≤ (g : ℝ) * K / c + W * ∑ i, ‖s i‖ / t i := by
    have : 0 ≤ ∑ i, ‖s i‖ / t i := Finset.sum_nonneg fun i _ => div_nonneg (norm_nonneg _) (ht i).le
    positivity
  refine opNorm_one_le_of_entry _ hE0 fun j k => ?_
  rw [hmapinv]
  have hexp : ((Y⁻¹).map Complex.ofReal * ((1 / (2 * Complex.I)) • (Dm + ∑ i, s i • (Bs i).map Complex.ofReal))) j k
      = (1 / (2 * Complex.I)) * (∑ l, ((Y⁻¹ j l : ℝ) : ℂ) * Dm l k + ∑ i, s i * (((Y⁻¹ * Bs i) j k : ℝ) : ℂ)) := by
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.sum_apply, map_apply, smul_eq_mul, ofReal_sum,
      ofReal_mul, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun l _ => by ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  rw [hexp, norm_mul]
  have hhalf : ‖(1 / (2 * Complex.I) : ℂ)‖ ≤ 1 := by simp; norm_num
  have hA : ‖∑ l, ((Y⁻¹ j l : ℝ) : ℂ) * Dm l k‖ ≤ g * K / c := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ l, ‖((Y⁻¹ j l : ℝ) : ℂ) * Dm l k‖ ≤ ∑ _l : Fin g, 1 / c * K :=
          Finset.sum_le_sum fun l _ => by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul (hinv j l) (hD l k) (norm_nonneg _) (by positivity)
      _ = g * K / c := by simp; ring
  have hBs : ‖∑ i, s i * (((Y⁻¹ * Bs i) j k : ℝ) : ℂ)‖ ≤ W * ∑ i, ‖s i‖ / t i := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖s i‖ * |(Y⁻¹ * Bs i) j k| ≤ ‖s i‖ * (W / t i) :=
          mul_le_mul_of_nonneg_left (hBe i j k) (norm_nonneg _)
      _ = W * (‖s i‖ / t i) := by ring
  calc ‖(1 / (2 * Complex.I) : ℂ)‖ * ‖∑ l, ((Y⁻¹ j l : ℝ) : ℂ) * Dm l k + ∑ i, s i * (((Y⁻¹ * Bs i) j k : ℝ) : ℂ)‖
      ≤ 1 * ((g : ℝ) * K / c + W * ∑ i, ‖s i‖ / t i) :=
        mul_le_mul hhalf ((norm_add_le _ _).trans (add_le_add hA hBs)) (norm_nonneg _) zero_le_one
    _ = (g : ℝ) * K / c + W * ∑ i, ‖s i‖ / t i := one_mul _

end GlobalTheory
end
end

section

open CategoryTheory GlobalTheory.CxCoh

theorem _root_.GlobalTheory.T.forget_positive_h1_bijective : ∀ (C : Type 1) [Category.{0} C] (K : Cx C), K.M1.Ac0 → K.M1.Ac1 → K.M2.Ac0 → Function.Bijective K.fnMap.h1 := by
  first | exact @GlobalTheory.CxCoh.Cx.fnMap_h1_bijective | exact GlobalTheory.CxCoh.Cx.fnMap_h1_bijective | (intros; apply GlobalTheory.CxCoh.Cx.fnMap_h1_bijective <;> assumption)
end

section

open CategoryTheory GlobalTheory.CxCoh

theorem _root_.GlobalTheory.T.vertical_h0_bijective_h1_injective_universes : VertHas.{1,1} (fun m ↦ Function.Bijective m.h0 ∧ Function.Injective m.h1) ∧ VertHas.{1,0} (fun m ↦ Function.Bijective m.h0 ∧ Function.Injective m.h1) ∧ VertHas.{0,0} (fun m ↦ Function.Bijective m.h0 ∧ Function.Injective m.h1) := by
  first | exact @GlobalTheory.CxCoh.vertical_bijective_h0_injective_h1 | exact GlobalTheory.CxCoh.vertical_bijective_h0_injective_h1 | (intros; apply GlobalTheory.CxCoh.vertical_bijective_h0_injective_h1 <;> assumption)
end
