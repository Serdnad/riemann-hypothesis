module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionOfGaussianPairings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle164
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle035
public import Formalism.RealPlaceAnalysis.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import ReciprocityTheory.DualLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle034
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

noncomputable section

open MeasureTheory Topology
open scoped Pointwise

namespace GlobalTheory.LocLanglands.InvInt

section General

variable {G : Type} [Group G] (H : Subgroup G)

def descend : (G → ℂ) →ₗ[ℂ] (G ⧸ H → ℂ) where
  toFun f q := f (q.out)⁻¹
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {H}

theorem descend_mk {f : G → ℂ} (hf : ∀ u ∈ H, ∀ g, f (u * g) = f g) (g : G) :
    descend H f (g : G ⧸ H) = f g⁻¹ := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  show f ((g : G ⧸ H).out)⁻¹ = _
  rw [hh, mul_inv_rev]
  exact hf _ (H.inv_mem h.2) _

theorem descend_mul_right {f : G → ℂ} (hf : ∀ u ∈ H, ∀ g, f (u * g) = f g) (x : G) :
    descend H (fun g => f (g * x)) = fun q => descend H f (x⁻¹ • q) := by
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [descend_mk (fun u hu g => by rw [mul_assoc, hf u hu]), MulAction.Quotient.smul_mk, descend_mk hf]
  simp

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem continuous_descend {f : G → ℂ} (hf : ∀ u ∈ H, ∀ g, f (u * g) = f g) (hc : Continuous f) :
    Continuous (descend H f) := by
  refine (QuotientGroup.isQuotientMap_mk H).continuous_iff.mpr ?_
  have : descend H f ∘ QuotientGroup.mk = fun g => f g⁻¹ := funext (descend_mk hf)
  rw [this]
  exact hc.comp continuous_inv

theorem hasCompactSupport_descend [T2Space (G ⧸ H)] {f : G → ℂ} (hf : ∀ u ∈ H, ∀ g, f (u * g) = f g)
    {C : Set G} (hC : IsCompact C) (hs : ∀ g, f g ≠ 0 → ∃ u ∈ H, ∃ c ∈ C, g = u * c) :
    HasCompactSupport (descend H f) := by
  refine HasCompactSupport.intro (hC.inv.image QuotientGroup.continuous_mk) fun q hq => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [descend_mk hf]
  by_contra h
  obtain ⟨u, hu, c, hc, e⟩ := hs _ h
  refine hq ⟨c⁻¹, by simpa using hc, QuotientGroup.eq.2 ?_⟩
  have : g = c⁻¹ * u⁻¹ := by rw [← mul_inv_rev, ← e, inv_inv]
  rw [this]
  simpa using hu

end General

open GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

theorem isClosed_unipB : IsClosed (unipB k (Fin m) : Set (GL (Fin m) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hc : ∀ i j, Continuous fun g : GL (Fin m) k => g.val i j := fun i j =>
    Units.continuous_val.matrix_elem i j
  have : (unipB k (Fin m) : Set (GL (Fin m) k)) =
      (⋂ i, ⋂ j, ⋂ _ : j < i, {g : GL (Fin m) k | g.val i j = 0}) ∩ ⋂ i, {g : GL (Fin m) k | g.val i i = 1} := by
    ext g
    simp only [SetLike.mem_coe, mem_unipB, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [this]
  exact (isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
    isClosed_eq (hc _ _) continuous_const).inter (isClosed_iInter fun _ => isClosed_eq (hc _ _) continuous_const)

end GlobalTheory.LocLanglands.InvInt
end
end

section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

namespace GlobalTheory.Mem.Lift.VacBd

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
  {om : V → V → ℝ} {ρ : V → B →L[ℂ] B}

theorem orbit_lip (h : IsHeis om ρ) {f : B} (hf : Sm ρ f) : ∃ C : ℝ, ∀ z, ‖ρ z f - f‖ ≤ C * ‖z‖ := by
  have hd := (ContDiff.differentiable hf (by simp) 0).hasFDerivAt.isBigO_sub
  obtain ⟨C, hC0, hC⟩ := hd.exists_pos
  obtain ⟨δ, hδ, hC⟩ := Metric.eventually_nhds_iff.1 hC.bound
  refine ⟨C + 2 * ‖f‖ / δ, fun z => ?_⟩
  have h0 : 0 ≤ 2 * ‖f‖ / δ * ‖z‖ := by positivity
  have h1 : 0 ≤ C * ‖z‖ := by positivity
  rw [add_mul]
  by_cases hz : ‖z‖ < δ
  · have := hC (y := z) (by simpa using hz)
    simp only [h.1, sub_zero] at this
    linarith
  · have h2 : ‖ρ z f - f‖ ≤ 2 * ‖f‖ := by
      have := norm_sub_le (ρ z f) f
      rw [h.2.2.1] at this
      linarith
    have h3 : 2 * ‖f‖ ≤ 2 * ‖f‖ / δ * ‖z‖ := by
      calc 2 * ‖f‖ = 2 * ‖f‖ / δ * δ := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (not_lt.1 hz) (by positivity)
    linarith

theorem dH_bound [CompleteSpace B] (h : IsHeis om ρ) (T : B →L[ℂ] B) (hT : ∀ x, Sm ρ (T x)) :
    ∃ C : ℝ, ∀ z x, ‖dH ρ z (T x)‖ ≤ C * ‖z‖ * ‖x‖ := by
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun z : V => ((‖z‖ : ℂ)⁻¹) • ((ρ z).comp T - T)) (fun x => by
    obtain ⟨C, hC⟩ := orbit_lip h (hT x)
    refine ⟨max C 0, fun z => ?_⟩
    by_cases hz : z = 0
    · simp [hz]
    · have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        norm_smul, norm_inv, Complex.norm_real, norm_norm]
      rw [inv_mul_le_iff₀ hz', mul_comm]
      exact (hC z).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hz'.le))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C, fun z x => ?_⟩
  have h1 : ‖fderiv ℝ (fun u => ρ u (T x)) 0‖ ≤ C * ‖x‖ := by
    refine (ContDiff.differentiable (hT x) (by simp) 0).hasFDerivAt.le_of_lip' (by positivity)
      (Filter.Eventually.of_forall fun w => ?_)
    by_cases hz : w = 0
    · simp [hz]
    · have hz' : 0 < ‖w‖ := norm_pos_iff.2 hz
      have := ContinuousLinearMap.le_of_opNorm_le _ (hC w) x
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        norm_smul, norm_inv, Complex.norm_real, norm_norm] at this
      rw [inv_mul_le_iff₀ hz', mul_comm] at this
      simpa only [h.1, sub_zero] using this
  have := ContinuousLinearMap.le_of_opNorm_le _ h1 z
  unfold dH
  linarith [mul_right_comm C ‖x‖ ‖z‖]

end General

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ : V → B →L[ℂ] B}

set_option linter.unusedSectionVars false

theorem heis_dH (h : IsHeis (omJ J) ρ) {f : B} (hf : Sm ρ f) (v w : V) :
    ρ w (dH ρ v f) = (π * I * (omJ J w v : ℂ)) • ρ w f + fderiv ℝ (fun u => ρ u f) w v := by
  have h1 := ((ρ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dH v hf)
  have h2 : HasDerivAt (fun t : ℝ => w + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add w
  have h3 : HasDerivAt (fun t : ℝ => ρ (w + t • v) f) (fderiv ℝ (fun u => ρ u f) w v) 0 :=
    (ContDiff.differentiable hf (by simp) w).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h2 (by simp)
  have h4 : HasDerivAt (fun t : ℝ => cexp ((π * I * (omJ J w v : ℂ)) * (t : ℂ))) (π * I * (omJ J w v : ℂ)) 0 := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := 0)).const_mul (π * I * (omJ J w v : ℂ))).cexp
  have h5 := h4.smul h3
  have e : ((ρ w).restrictScalars ℝ) ∘ (fun t : ℝ => ρ (t • v) f) =
      (fun t : ℝ => cexp ((π * I * (omJ J w v : ℂ)) * (t : ℂ))) • fun t : ℝ => ρ (w + t • v) f := by
    funext t
    simp only [Function.comp, ContinuousLinearMap.coe_restrictScalars', h.2.1, Pi.smul_apply', omJ, map_smul,
      real_inner_smul_right]
    congr 2
    push_cast
    ring
  rw [e] at h1
  have := h1.unique h5
  simpa [add_comm] using this

theorem contDiff_omJ (v : V) : ContDiff ℝ ∞ fun w : V => (π * I * (omJ J w v : ℂ)) := by
  unfold omJ
  exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_id.inner ℝ contDiff_const))

theorem sm_dH (h : IsHeis (omJ J) ρ) {f : B} (hf : Sm ρ f) (v : V) : Sm ρ (dH ρ v f) := by
  unfold Sm
  simp only [heis_dH h hf]
  exact ((contDiff_omJ v).smul hf).add
    ((ContDiff.fderiv_right (m := ∞) hf (by simp)).clm_apply contDiff_const)

theorem fderiv_compress (P : B →L[ℂ] B) {g y : B} (hg : Sm ρ g) {φ : V → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (e : ∀ w, P (ρ w g) = φ w • y) (w v : V) : P (fderiv ℝ (fun u => ρ u g) w v) = fderiv ℝ φ w v • y := by
  have h1 := (P.restrictScalars ℝ).hasFDerivAt.comp w (ContDiff.differentiable hg (by simp) w).hasFDerivAt
  have h2 := (hφ.differentiable (by simp) w).hasFDerivAt.smul_const y
  have e' : (P.restrictScalars ℝ) ∘ (fun u => ρ u g) = fun u => φ u • y := funext e
  rw [e'] at h1
  simpa using DFunLike.congr_fun (h1.unique h2) v

theorem vacuum_bound : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) → ∀ h : IsHeis (omJ J) ρ, (∃ C : ℝ, ∀ z x, ‖dH ρ z (proj h x)‖ ≤ C * ‖z‖ * ‖x‖) ∧ (∀ u v, ∃ C : ℝ, ∀ x, ‖dH ρ u (dH ρ v (proj h x))‖ ≤ C * ‖x‖) ∧ ∀ u v, ∃ lam : ℂ, ∀ x, proj h (dH ρ u (dH ρ v (proj h x))) = lam • proj h x := by
  intro V _ _ _ _ _ B _ _ _ J ρ hJ h
  have hs : ∀ x, Sm ρ (proj h x) := fun x => (Osc.good_proj hJ h x).sm hJ
  obtain ⟨C, hC⟩ := dH_bound h (proj h) hs
  refine ⟨⟨C, hC⟩, fun u v => ?_, fun u v => ?_⟩
  · let T : B →L[ℂ] B := LinearMap.mkContinuous
      { toFun := fun x => dH ρ v (proj h x)
        map_add' := fun x y => by rw [map_add (f := _), dH_add v (hs x) (hs y)]
        map_smul' := fun a x => by rw [map_smul, dH_smul v a (hs x), RingHom.id_apply] } (C * ‖v‖) (hC v)
    obtain ⟨D, hD⟩ := dH_bound h T fun x => sm_dH h (hs x) v
    exact ⟨D * ‖u‖, hD u⟩
  · have hg : ContDiff ℝ ∞ (gau : V → ℂ) := contDiff_gau
    have hφ : ContDiff ℝ ∞ fun w : V => (π * I * (omJ J w v : ℂ)) * gau w + fderiv ℝ gau w v :=
      ((contDiff_omJ v).mul hg).add ((ContDiff.fderiv_right (m := ∞) hg (by simp)).clm_apply contDiff_const)
    refine ⟨_, fun x => fderiv_compress (proj h) (sm_dH h (hs x) v) hφ (fun w => ?_) 0 u⟩
    rw [heis_dH h (hs x), map_add (f := _), map_smul, proj_heis_proj hJ h,
      fderiv_compress (proj h) (hs x) hg (fun w => proj_heis_proj hJ h w x), add_smul, mul_smul _ (gau w)]

end GlobalTheory.Mem.Lift.VacBd
end

section

open Matrix GlobalTheory.Mem.Lift

namespace GlobalTheory.Mem.Capelli

variable {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ}

def trAlg (M : Matrix (Fin n) (Fin n) A) : Subalgebra ℂ A :=
  Algebra.adjoin ℂ (Set.range fun k : ℕ => (M ^ (k + 1)).trace)

theorem trace_pow_mem (M : Matrix (Fin n) (Fin n) A) (k : ℕ) : (M ^ k).trace ∈ trAlg M := by
  cases k with
  | zero => simpa using natCast_mem (trAlg M) n
  | succ k => exact Algebra.subset_adjoin ⟨k, rfl⟩

theorem trAlg_le {M : Matrix (Fin n) (Fin n) A} {S : Subalgebra ℂ A} (h : ∀ k, (M ^ (k + 1)).trace ∈ S) :
    trAlg M ≤ S := Algebra.adjoin_le (by rintro _ ⟨k, rfl⟩; exact h k)

theorem trAlg_shift_le (M : Matrix (Fin n) (Fin n) A) (s c : ℂ) : trAlg (s • M + c • 1) ≤ trAlg M := by
  have key : ∀ k j : ℕ, (M ^ j * (s • M + c • 1) ^ k).trace ∈ trAlg M := by
    intro k
    induction k with
    | zero => intro j; simpa using trace_pow_mem M j
    | succ k ih =>
      intro j
      rw [pow_succ', ← mul_assoc, mul_add, add_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc,
        mul_one, ← pow_succ, trace_add, trace_smul, trace_smul]
      exact add_mem (Subalgebra.smul_mem _ (ih _) _) (Subalgebra.smul_mem _ (ih _) _)
  exact trAlg_le fun k => by simpa using key (k + 1) 0

theorem trAlg_shift (M : Matrix (Fin n) (Fin n) A) {s : ℂ} (hs : s ≠ 0) (c : ℂ) :
    trAlg (s • M + c • 1) = trAlg M := by
  refine le_antisymm (trAlg_shift_le M s c) ?_
  have h := trAlg_shift_le (s • M + c • (1 : Matrix (Fin n) (Fin n) A)) s⁻¹ (-(s⁻¹ * c))
  rwa [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hs, one_smul, neg_smul, add_neg_cancel_right] at h

theorem adjoin_gelfA (E : Fin n → Fin n → A) :
    Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA E)) = trAlg (Matrix.of E) := by
  rw [trAlg]
  congr 2
  funext k
  rw [GlobalTheory.SmoothForms.gelfA_eq_sum_pow]
  rfl

section CCR

variable (X : Matrix (Fin n) (Fin m) A) (D : Matrix (Fin m) (Fin n) A)
  (hdd : ∀ a l b j, D a l * D b j = D b j * D a l)
  (hdx : ∀ a l i b, D a l * X i b = X i b * D a l + if i = l ∧ b = a then 1 else 0)

omit [Algebra ℂ A] in
include hdd hdx in
theorem comm_one (a : Fin m) (l i j : Fin n) :
    D a l * (X * D) i j = (X * D) i j * D a l + if i = l then D a j else 0 := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, ← mul_assoc, hdx, add_mul, Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun b _ => by rw [mul_assoc, mul_assoc, hdd]
  · by_cases h : i = l <;> simp [h]

omit [Algebra ℂ A] in
include hdd hdx in
theorem comm_pow (p : ℕ) (a : Fin m) (l i j : Fin n) :
    D a l * ((X * D) ^ p) i j = ((X * D) ^ p) i j * D a l
      + ∑ r ∈ Finset.range p, ((X * D) ^ r) i l * (D * (X * D) ^ (p - (r + 1))) a j := by
  induction p generalizing i with
  | zero => by_cases h : i = j <;> simp [Matrix.one_apply, h]
  | succ p ih =>
    have h1 : ∀ k, D a l * ((X * D) i k * ((X * D) ^ p) k j) =
        (X * D) i k * ((X * D) ^ p) k j * D a l
        + (∑ r ∈ Finset.range p, (X * D) i k * ((X * D) ^ r) k l * (D * (X * D) ^ (p - (r + 1))) a j
          + if i = l then D a k * ((X * D) ^ p) k j else 0) := fun k => by
      rw [← mul_assoc, comm_one X D hdd hdx, add_mul, mul_assoc, ih, mul_add, Finset.mul_sum, add_assoc]
      simp only [mul_assoc, ite_mul, zero_mul]
    rw [pow_succ', Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, Finset.sum_range_succ']
    simp only [h1, Finset.sum_add_distrib]
    congr 2
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← Finset.sum_mul, ← Matrix.mul_apply, ← pow_succ', Nat.add_sub_add_right]
    · by_cases h : i = l <;> simp [h, Matrix.one_apply, Matrix.mul_apply]

omit [Algebra ℂ A] in
include hdd hdx in
theorem trace_rec (p : ℕ) :
    ((D * X) ^ (p + 1)).trace = ((X * D) ^ (p + 1)).trace + (m : A) * ((X * D) ^ p).trace
      + ∑ r ∈ Finset.range p, ((X * D) ^ r).trace * ((D * X) ^ (p - (r + 1) + 1)).trace := by
  have hN : ∀ q : ℕ, (D * X) ^ (q + 1) = D * (X * D) ^ q * X := fun q => by
    induction q with
    | zero => simp
    | succ q ih => rw [pow_succ, ih, pow_succ]; simp only [Matrix.mul_assoc]
  have hY : ∀ a j, (D * (X * D) ^ p) a j = ∑ u, ((X * D) ^ p) u j * D a u
      + ∑ r ∈ Finset.range p, ((X * D) ^ r).trace * (D * (X * D) ^ (p - (r + 1))) a j := fun a j => by
    rw [Matrix.mul_apply]
    simp only [comm_pow X D hdd hdx, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    simp only [trace, diag_apply, Finset.sum_mul]
  have hT : ∀ q : ℕ, ((D * X) ^ (q + 1)).trace = ∑ a, ∑ j, (D * (X * D) ^ q) a j * X j a := fun q => by
    rw [hN]; rfl
  have hE : ∀ u j, ∑ a, D a u * X j a = (X * D) j u + if j = u then (m : A) else 0 := fun u j => by
    simp only [hdx, Finset.sum_add_distrib, Matrix.mul_apply]
    by_cases h : j = u <;> simp [h]
  simp only [hT]
  simp only [hY, add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  congr 1
  · rw [Finset.sum_comm]
    have : ∀ j, ∑ a, ∑ u, ((X * D) ^ p) u j * (D a u * X j a)
        = ∑ u, ((X * D) ^ p) u j * (X * D) j u + (m : A) * ((X * D) ^ p) j j := fun j => by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, hE, mul_add, Finset.sum_add_distrib]
      simp [Nat.cast_comm]
    simp only [this, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm, pow_succ]; rfl
    · simp only [trace, diag_apply, Finset.mul_sum]
  · rw [Finset.sum_comm (s := Finset.range p)]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

include hdd hdx in
theorem trAlg_mul_comm : trAlg (X * D) = trAlg (D * X) := by
  apply le_antisymm
  · have key : ∀ p : ℕ, ((X * D) ^ p).trace ∈ trAlg (D * X) := fun p => by
      induction p using Nat.strong_induction_on with
      | _ p ih =>
        cases p with
        | zero => simpa using natCast_mem (trAlg (D * X)) n
        | succ p =>
          have h := trace_rec X D hdd hdx p
          rw [add_assoc, ← sub_eq_iff_eq_add] at h
          rw [← h]
          refine sub_mem (trace_pow_mem _ _) (add_mem (mul_mem (natCast_mem _ _) (ih p (by omega)))
            (sum_mem fun r hr => mul_mem (ih r ?_) (trace_pow_mem _ _)))
          have := Finset.mem_range.1 hr
          omega
    exact trAlg_le fun k => key _
  · refine trAlg_le fun p => ?_
    induction p using Nat.strong_induction_on with
    | _ p ih =>
      rw [trace_rec X D hdd hdx p]
      refine add_mem (add_mem (trace_pow_mem _ _) (mul_mem (natCast_mem _ _) (trace_pow_mem _ _)))
        (sum_mem fun r hr => mul_mem (trace_pow_mem _ _) (ih _ ?_))
      have := Finset.mem_range.1 hr
      omega

end CCR

theorem adjoin_gelfA_dual_pair : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n m : ℕ) (x d : Fin n × Fin m → A), IsCCR x d → ∀ c c' : ℂ, Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA fun i j : Fin n => ∑ a, x (i, a) * d (j, a) + if i = j then algebraMap ℂ A c else 0)) = Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA fun a b : Fin m => -∑ i, x (i, b) * d (i, a) + if a = b then algebraMap ℂ A c' else 0)) := by
  intro A _ _ n m x d h c c'
  obtain ⟨-, hdd, hdx⟩ := h
  let X : Matrix (Fin n) (Fin m) A := Matrix.of fun i a => x (i, a)
  let D : Matrix (Fin m) (Fin n) A := Matrix.of fun a i => d (i, a)
  have hdx' : ∀ a l i b, D a l * X i b = X i b * D a l + if i = l ∧ b = a then 1 else 0 := fun a l i b => by
    have := hdx (i, b) (l, a)
    rw [sub_eq_iff_eq_add'] at this
    simpa [X, D] using this
  have h1 : (Matrix.of fun i j : Fin n => ∑ a, x (i, a) * d (j, a) + if i = j then algebraMap ℂ A c else 0)
      = (1 : ℂ) • (X * D) + c • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [X, D, Matrix.mul_apply, Matrix.one_apply, hij, Algebra.algebraMap_eq_smul_one]
  have h2 : (Matrix.of fun a b : Fin m => -∑ i, x (i, b) * d (i, a) + if a = b then algebraMap ℂ A c' else 0)
      = (-1 : ℂ) • (D * X) + (c' + n) • 1 := by
    ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, hdx', Finset.sum_add_distrib]
    by_cases hab : a = b
    · subst hab
      simp [X, D, Algebra.algebraMap_eq_smul_one, add_smul, Nat.cast_smul_eq_nsmul]
      abel
    · simp [X, D, hab, Ne.symm hab]
  rw [adjoin_gelfA, adjoin_gelfA, h1, h2, trAlg_shift _ one_ne_zero, trAlg_shift _ (by norm_num)]
  exact trAlg_mul_comm X D (fun a l b j => hdd _ _) hdx'

end GlobalTheory.Mem.Capelli
end

section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

theorem _root_.GlobalTheory.T.heisenbergSmoothVector_derivative_calculus : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B), (∀ x, om x x = 0) → IsHeis (fun x y => om x y) ρ → ∀ f, Sm ρ f → (∀ v, Sm ρ (dH ρ v f)) ∧ (∀ w, Sm ρ (ρ w f)) ∧ (∀ w y, fderiv ℝ (fun u => ρ u f) w y = ρ w (dH ρ y f) - (π * I * (om w y : ℂ)) • ρ w f) ∧ (∀ v w, dH ρ v (ρ w f) = ρ w (dH ρ v f) + (2 * π * I * (om v w : ℂ)) • ρ w f) ∧ ∀ u v, dH ρ u (dH ρ v f) - dH ρ v (dH ρ u f) = (2 * π * I * (om u v : ℂ)) • f := by
  first | exact @GlobalTheory.Mem.Lift.DCalc.dH_calculus | exact GlobalTheory.Mem.Lift.DCalc.dH_calculus | (intros; apply GlobalTheory.Mem.Lift.DCalc.dH_calculus <;> assumption)
end

section

open Matrix GlobalTheory.Mem.Lift

theorem _root_.GlobalTheory.T.glRel_of_canonicalCommutationRelations : ∀ (A : Type) [Ring A] (n m : ℕ) (x d : Fin n × Fin m → A), IsCCR x d → Formalism.REAL.GlRel (fun i j : Fin n => ∑ a, x (i, a) * d (j, a)) ∧ Formalism.REAL.GlRel (fun a b : Fin m => -∑ i, x (i, b) * d (i, a)) := by
  first | exact @GlobalTheory.Mem.Lift.glRel_of_isCCR | exact GlobalTheory.Mem.Lift.glRel_of_isCCR | (intros; apply GlobalTheory.Mem.Lift.glRel_of_isCCR <;> assumption)
end

section

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_equivariant_piTensor_polynomialBilinear : ∀ (ι : Type) [Fintype ι] (N n : ℕ) (A B : ι → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)] [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)] (I : ∀ i, MvPolynomial (Fin N × Fin n) ℂ →ₗ[ℂ] A i →ₗ[ℂ] B i), (∀ i, I i ≠ 0) → ∃ It : MvPolynomial (ι × Fin N × Fin n) ℂ →ₗ[ℂ] (⨂[ℂ] i, A i) →ₗ[ℂ] ⨂[ℂ] i, B i, It ≠ 0 ∧ ∀ (c : ι → ℂ) (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ) (a : ∀ i, A i →ₗ[ℂ] A i) (b : ∀ i, B i →ₗ[ℂ] B i), (∀ i P v, I i (c i • subst2 (h i) (g i) P) (a i v) = b i (I i P v)) → ∀ P x, It ((∏ i, c i) • substF h g P) (PiTensorProduct.map a x) = PiTensorProduct.map b (It P x) := by
  first | exact @GlobalTheory.CompactHowe.PolyTensor.exists_tensor | exact GlobalTheory.CompactHowe.PolyTensor.exists_tensor | (intros; apply GlobalTheory.CompactHowe.PolyTensor.exists_tensor <;> assumption)
end

section

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_jointHighestWeight_leadingMinorProduct : ∀ (N n : ℕ) (hn : n ≤ N) (ν : Fin N → ℕ), Antitone ν → (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) → ∃ Δ : MvPolynomial (Fin N × Fin n) ℂ, Δ ≠ 0 ∧ (∀ h g, ReciprocityTheory.PGsh.IsUpperUnitri h → ReciprocityTheory.PGsh.IsUpperUnitri g → subst2 h g Δ = Δ) ∧ ∀ (d : Fin N → ℂ) (e : Fin n → ℂ), subst2 (Matrix.diagonal d) (Matrix.diagonal e) Δ = ((∏ b, d b ^ ν b) * ∏ a, e a ^ ν (Fin.castLE hn a)) • Δ := by
  first | exact @GlobalTheory.CompactHowe.Minors.exists_highestWeight | exact GlobalTheory.CompactHowe.Minors.exists_highestWeight | (intros; apply GlobalTheory.CompactHowe.Minors.exists_highestWeight <;> assumption)
end
