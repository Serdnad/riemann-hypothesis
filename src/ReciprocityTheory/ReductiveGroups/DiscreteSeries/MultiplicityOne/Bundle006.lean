module

public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Mathlib.Algebra.Group.MinimalAxioms
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle004
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroupA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.UHMulInv
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JFrameA

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace MatrixSubsetMeasurability

variable {k r : ℕ} {U : Set (Mat k r)}

def SG (_hU : IsClosedSubgroup U) : Type := {x : Mt k r // (Matrix.of x : Mat k r) ∈ U}

def mat {hU : IsClosedSubgroup U} (g : SG hU) : Mat k r := Matrix.of g.1

theorem mat_mem {hU : IsClosedSubgroup U} (g : SG hU) : mat g ∈ U := by
  exact g.2

def mk (hU : IsClosedSubgroup U) (A : Mat k r) (hA : A ∈ U) : SG hU := ⟨Matrix.of.symm A, hA⟩

theorem mat_mk (hU : IsClosedSubgroup U) (A : Mat k r) (hA : A ∈ U) : mat (mk hU A hA) = A := rfl

variable {hU : IsClosedSubgroup U}

instance : One (SG hU) := ⟨mk hU 1 hU.one_mem⟩
instance : Mul (SG hU) := ⟨fun a b => mk hU (mat a * mat b) (hU.mul_mem _ a.2 _ b.2)⟩
instance : Inv (SG hU) := ⟨fun a => mk hU (mat a)⁻¹ (hU.inv_mem _ a.2)⟩

theorem mat_one : mat (1 : SG hU) = 1 := rfl
theorem mat_mul (a b : SG hU) : mat (a * b) = mat a * mat b := rfl
theorem mat_inv (a : SG hU) : mat a⁻¹ = (mat a)⁻¹ := rfl

theorem ext' {a b : SG hU} (h : mat a = mat b) : a = b := by
  exact Subtype.ext (Matrix.of.injective h)

instance : Group (SG hU) :=
  Group.ofLeftAxioms (fun a b c => ext' (Matrix.mul_assoc (mat a) (mat b) (mat c)))
    (fun a => ext' (Matrix.one_mul (mat a)))
    (fun a => ext' (Matrix.nonsing_inv_mul (mat a) (hU.unit _ a.2)))

instance : TopologicalSpace (SG hU) := instTopologicalSpaceSubtype
instance : MeasurableSpace (SG hU) := Subtype.instMeasurableSpace
instance : BorelSpace (SG hU) :=
  inferInstanceAs (BorelSpace ({x : Mt k r | (Matrix.of x : Mat k r) ∈ U} : Set (Mt k r)))

private theorem continuous_matrix_of_Mt : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) :=
  continuous_matrix (fun i j => (continuous_apply j).comp (continuous_apply i))

theorem continuous_mat : Continuous (fun g : SG hU => mat g) := by
  exact continuous_matrix_of_Mt.comp continuous_subtype_val

instance : ContinuousMul (SG hU) := by
  refine ⟨Continuous.subtype_mk ?_ _⟩
  exact (continuous_mat.comp continuous_fst).matrix_mul (continuous_mat.comp continuous_snd)

instance : ContinuousInv (SG hU) := by
  refine ⟨Continuous.subtype_mk ?_ _⟩
  have h : (fun a : SG hU => (mat a)⁻¹) = fun a => (mat a).det⁻¹ • (mat a).adjugate := by
    funext a; rw [Matrix.inv_def, Ring.inverse_eq_inv]
  show Continuous fun a : SG hU => (mat a)⁻¹
  rw [h]
  exact ((continuous_mat.matrix_det).inv₀ fun a => (hU.unit _ a.2).ne_zero).smul continuous_mat.matrix_adjugate

instance : IsTopologicalGroup (SG hU) := {}

theorem measurableSet_U (hU : IsClosedSubgroup U) : MeasurableSet {x : Mt k r | (Matrix.of x : Mat k r) ∈ U} := by
  exact (hU.closed.preimage continuous_matrix_of_Mt).measurableSet

theorem me_val (hU : IsClosedSubgroup U) : MeasurableEmbedding (fun g : SG hU => g.1) := by
  exact MeasurableEmbedding.subtype_coe (measurableSet_U hU)

def nu (hU : IsClosedSubgroup U) (μ : Measure (Mt k r)) : Measure (SG hU) := μ.comap (fun g : SG hU => g.1)

theorem map_nu {μ : Measure (Mt k r)} (hμ : IsHaarOn U μ) : (nu hU μ).map (fun g : SG hU => g.1) = μ := by
  unfold nu
  rw [(me_val hU).map_comap]
  first | rw [Subtype.range_coe_subtype] | rw [Subtype.range_val_subtype] | skip
  have hae : ∀ᵐ x ∂μ, (Matrix.of x : Mat k r) ∈ U := ae_iff.mpr hμ.conc
  exact Measure.restrict_eq_self_of_ae_mem (hae.mono fun x hx => ⟨⟨x, hx⟩, rfl⟩)

theorem nu_left {μ : Measure (Mt k r)} (hμ : IsHaarOn U μ) : (nu hU μ).IsMulLeftInvariant := by
  constructor
  intro g
  have hc : Continuous (lmulM (k := k) (r := r) (mat g)) :=
    (continuous_const.mul continuous_matrix_of_Mt : Continuous fun x : Mt k r => (mat g * Matrix.of x : Mat k r))
  have hm : Measurable (fun x : SG hU => g * x) := by
    refine Measurable.subtype_mk ?_
    exact hc.measurable.comp measurable_subtype_coe
  have hval : (fun g : SG hU => g.1) ∘ (fun x : SG hU => g * x) = lmulM (mat g) ∘ (fun g : SG hU => g.1) := rfl
  have hmap : ((nu hU μ).map (fun x : SG hU => g * x)).map (fun g : SG hU => g.1)
      = (nu hU μ).map (fun g : SG hU => g.1) := by
    rw [Measure.map_map (me_val hU).measurable hm, hval,
      ← Measure.map_map hc.measurable (me_val hU).measurable, map_nu hμ, hμ.left _ (mat_mem g)]
  ext s hs
  have h1 := congrArg (fun m : Measure (Mt k r) => m ((fun g : SG hU => g.1) '' s)) hmap
  rwa [(me_val hU).map_apply, (me_val hU).map_apply,
    Set.preimage_image_eq s (me_val hU).injective] at h1

theorem nu_inv (HI : HaarInv) {μ : Measure (Mt k r)} (hμ : IsHaarOn U μ) : (nu hU μ).IsInvInvariant := by
  have hae : AEMeasurable invM μ := InvGrp.measurable_invM.aemeasurable
  constructor
  ext s hs
  have hset : (fun g : SG hU => g.1) '' (Inv.inv ⁻¹' s) =
      invM ⁻¹' ((fun g : SG hU => g.1) '' s) ∩
      {x : Mt k r | (Matrix.of x : Mat k r) ∈ U} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨(@id (SG hU) x)⁻¹, hx, rfl⟩, x.2⟩
    · rintro ⟨⟨x, hx, hxy⟩, hy⟩
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      have e : (@id (SG hU) ⟨y, hy⟩)⁻¹ = x := by
        apply ext'
        rw [mat_inv]
        show (Matrix.of y : Mat k r)⁻¹ = Matrix.of x.1
        rw [show x.1 = invM y from hxy]
        all_goals rfl
      show (@id (SG hU) ⟨y, hy⟩)⁻¹ ∈ s
      rw [e]
      exact hx
  rw [Measure.inv_def, Measure.map_apply measurable_inv hs]
  simp only [nu]
  rw [(me_val hU).comap_apply, (me_val hU).comap_apply, hset,
    measure_inter_conull (t := {x : Mt k r | (Matrix.of x : Mat k r) ∈ U}) hμ.conc,
    ← Measure.map_apply_of_aemeasurable hae ((me_val hU).measurableSet_image.mpr hs), HI k r U μ hU hμ]

end MatrixSubsetMeasurability

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

section

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.MixedNormBounds

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ConjugateNormInequalities

variable {k r : ℕ}

theorem gN_map_conj (M : Mat k r) : gN (M.map (starRingEnd ℂ)) = gN M := by
  simp only [gN, Matrix.map_apply, Complex.normSq_conj]

theorem gN_le_gbar {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hE : IsUnit (embWb k r γ).det) (y : Mat k r) :
    gN y ≤ (gN (embWb k r γ) * gN (embWb k r γ)⁻¹) ^ 2 * gN (gbar k r γ y) := by
  obtain ⟨y', hy'⟩ : ∃ y', y' = gbar k r γ y := ⟨_, rfl⟩
  have h1 : gN y = gN (gbar k r γ y') := by rw [hy', InvGrp.gbar_gbar hE]
  rw [h1, ← hy']
  unfold gbar
  set E := embWb k r γ
  have hE0 := gN_nonneg E
  have hEi0 := gN_nonneg E⁻¹
  calc gN (E * (E⁻¹ * y' * E).map (starRingEnd ℂ) * E⁻¹)
      ≤ gN E * gN ((E⁻¹ * y' * E).map (starRingEnd ℂ)) * gN E⁻¹ :=
        (gN_mul_le _ _).trans (mul_le_mul_of_nonneg_right (gN_mul_le _ _) hEi0)
    _ = gN E * gN (E⁻¹ * y' * E) * gN E⁻¹ := by rw [gN_map_conj]
    _ ≤ gN E * (gN E⁻¹ * gN y' * gN E) * gN E⁻¹ := by
        gcongr
        exact (gN_mul_le _ _).trans (mul_le_mul_of_nonneg_right (gN_mul_le _ _) hE0)
    _ = (gN E * gN E⁻¹) ^ 2 * gN y' := by ring

theorem rpow_bound {A B K a : ℝ} (hA : 0 < A) (hK : 0 < K) (ha : 0 ≤ a) (h : A ≤ K * B) :
    B ^ (-a) ≤ K ^ a * A ^ (-a) := by
  have hB : A / K ≤ B := by rw [div_le_iff₀ hK, mul_comm]; exact h
  have hAK : 0 < A / K := div_pos hA hK
  calc B ^ (-a) ≤ (A / K) ^ (-a) := Real.rpow_le_rpow_of_nonpos hAK hB (by linarith)
    _ = K ^ a * A ^ (-a) := by
      rw [Real.div_rpow hA.le hK.le, Real.rpow_neg hK.le, div_eq_mul_inv, inv_inv, mul_comm]

theorem inner_sig_sig (X : SigData k r) {h : Mat k r} (hh : h ∈ GV k r) (a b : X.Hs) :
    ⟪X.σ h a, X.σ h b⟫_ℂ = ⟪a, b⟫_ℂ := (⟨(X.σ h).toLinearMap, X.rep.2.1 h hh⟩ : X.Hs →ₗᵢ[ℂ] X.Hs).inner_map_map a b

theorem inner_sig_left (X : SigData k r) (hG : IsClosedSubgroup (GV k r)) {h : Mat k r} (hh : h ∈ GV k r)
    (a b : X.Hs) : ⟪X.σ h a, b⟫_ℂ = ⟪a, X.σ h⁻¹ b⟫_ℂ := by
  have hi : h⁻¹ ∈ GV k r := hG.inv_mem h hh
  have hb : X.σ h (X.σ h⁻¹ b) = b := by
    have e := X.rep.1.2 h hh h⁻¹ hi
    rw [Matrix.mul_nonsing_inv _ (hG.unit h hh), X.rep.1.1] at e
    have e2 := congrArg (fun T : X.Hs →L[ℂ] X.Hs => T b) e
    simpa using e2.symm
  conv_lhs => rw [← hb]
  exact inner_sig_sig X hh a _

theorem exists_inner_ne (X : SigData k r) (hG : IsClosedSubgroup (GV k r)) (v : X.Hs) (hv : v ≠ 0) :
    ∃ g ∈ GV k r, ⟪v, X.σ g X.w⟫_ℂ ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  let S : Submodule ℂ X.Hs :=
    { carrier := {u | ∀ g ∈ GV k r, ⟪v, X.σ g u⟫_ℂ = 0}
      add_mem' := by
        intro a b ha hb g hg
        rw [map_add (f := _), inner_add_right, ha g hg, hb g hg, add_zero]
      zero_mem' := by
        intro g hg
        rw [map_zero, inner_zero_right]
      smul_mem' := by
        intro c a ha g hg
        rw [map_smul, inner_smul_right, ha g hg, mul_zero] }
  have hSc : IsClosed (S : Set X.Hs) := by
    have e : (S : Set X.Hs) = ⋂ g ∈ GV k r, (fun u => ⟪v, X.σ g u⟫_ℂ) ⁻¹' {0} := by
      ext u
      show (∀ g ∈ GV k r, ⟪v, X.σ g u⟫_ℂ = 0) ↔ _
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    rw [e]
    exact isClosed_biInter fun g _ => isClosed_singleton.preimage (continuous_const.inner (X.σ g).continuous)
  have hSi : ∀ g ∈ GV k r, ∀ u ∈ S, X.σ g u ∈ S := by
    intro g hg u hu g' hg'
    have e := X.rep.1.2 g' hg' g hg
    have e2 : X.σ g' (X.σ g u) = X.σ (g' * g) u := by rw [e]; rfl
    show ⟪v, X.σ g' (X.σ g u)⟫_ℂ = 0
    rw [e2]
    exact hu _ (hG.mul_mem g' hg' g hg)
  have hw : X.w ∈ S := fun g hg => hcon g hg
  rcases X.irr S hSc hSi with h | h
  · have h0 : X.w = 0 := by
      rw [h] at hw
      exact (Submodule.mem_bot ℂ).mp hw
    have h1 := X.w_norm
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  · have hv' : v ∈ S := by rw [h]; exact Submodule.mem_top
    have h0 := hv' 1 hG.one_mem
    rw [X.rep.1.1, ContinuousLinearMap.one_apply, inner_self_eq_zero] at h0
    exact hv h0

end ReciprocityTheory.ChartRestriction.DS.Mult1.MixedNormBounds
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

theorem measurable_lmul_mt (a : Mat k r) :
    @Measurable (Mt k r) (Mt k r) _ _ (fun x => (a * Matrix.of x : Mat k r)) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem sigmaFinite_of_haarOn {U : Set (Mat k r)} {μ : Measure (Mt k r)} (hH : IsHaarOn U μ) : SigmaFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => hH.finite_compact K hK⟩
  infer_instance

theorem ae_mem_of_haarOn {U : Set (Mat k r)} {μ : Measure (Mt k r)} (hH : IsHaarOn U μ) :
    ∀ᵐ x ∂μ, (Matrix.of x : Mat k r) ∈ U := ae_iff.mpr hH.conc

theorem inner_sig_move (X : SigData k r) (g : Mat k r) (hg : g ∈ GV k r) (hgi : g⁻¹ ∈ GV k r)
    (hgg : g * g⁻¹ = 1) (a b : X.Hs) : ⟪X.σ g a, b⟫_ℂ = ⟪a, X.σ g⁻¹ b⟫_ℂ := by
  obtain ⟨h1, h2⟩ := X.rep.1
  have hσ : X.σ g (X.σ g⁻¹ b) = b := by
    have h3 := h2 g hg g⁻¹ hgi
    rw [hgg, h1] at h3
    have h4 := congrArg (fun L => L b) h3
    simpa using h4.symm
  let L : X.Hs →ₗᵢ[ℂ] X.Hs := ⟨(X.σ g : X.Hs →ₗ[ℂ] X.Hs), fun v => X.rep.2.1 g hg v⟩
  calc ⟪X.σ g a, b⟫_ℂ = ⟪L a, L (X.σ g⁻¹ b)⟫_ℂ := by rw [show L (X.σ g⁻¹ b) = b from hσ]; rfl
    _ = ⟪a, X.σ g⁻¹ b⟫_ℂ := L.inner_map_map a _

theorem psiD_norm {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) (m : Mat k r) :
    ‖psiD D m‖ = 1 := by
  unfold psiD psi
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem psiD_star_mul {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) (m : Mat k r) :
    star (psiD D m) * psiD D m = 1 := by
  rw [Complex.star_def, Complex.conj_mul', psiD_norm]
  simp

end ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

theorem gv_mul {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r) : a * b ∈ GV k r := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

private theorem hpk_sq_lemma : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single
    (⟨if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val, by split_ifs <;> omega⟩ :
      Fin (2 * r + k + 1))]
  · simp only [Hpk, Matrix.one_apply, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | (norm_num; done) | omega
  · intro l _ hl
    rw [Ne, Fin.ext_iff] at hl
    simp only [Hpk, Fin.ext_iff, Fin.val_mk] at hl ⊢
    split_ifs at hl ⊢ <;> first | (simp; done) | omega
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem isUnit_det_of_mem_GV' {a : Mat k r} (ha : a ∈ GV k r) : IsUnit a.det := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have h1 : (Hpk k r * aᴴ * Hpk k r) * a = 1 := by
    calc (Hpk k r * aᴴ * Hpk k r) * a = Hpk k r * (aᴴ * Hpk k r * a) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [ha', hpk_sq_lemma]
  exact Matrix.isUnit_det_of_left_inverse h1

theorem gv_inv {a : Mat k r} (ha : a ∈ GV k r) : a⁻¹ ∈ GV k r := by
  have h1 : a * a⁻¹ = 1 := ReciprocityTheory.ChartRestriction.DS.Xi.StepA.UH_mul_inv k r ha
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r
  calc (a⁻¹)ᴴ * Hpk k r * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * Hpk k r * a) * a⁻¹ := by rw [ha']
    _ = (a * a⁻¹)ᴴ * Hpk k r * (a * a⁻¹) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [h1]; simp

theorem gv_inv_mul {a : Mat k r} (ha : a ∈ GV k r) : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a (isUnit_det_of_mem_GV' ha)

theorem gv_mul_inv {a : Mat k r} (ha : a ∈ GV k r) : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a (isUnit_det_of_mem_GV' ha)

theorem gv_inv_inv {a : Mat k r} (ha : a ∈ GV k r) : a⁻¹⁻¹ = a := Matrix.nonsing_inv_nonsing_inv a (isUnit_det_of_mem_GV' ha)

theorem fix_inv {a : Mat k r} (ha : a ∈ GV k r) {v : Fin (2 * r + k + 1) → ℂ} (hv : a *ᵥ v = v) :
    a⁻¹ *ᵥ v = v := by
  calc a⁻¹ *ᵥ v = a⁻¹ *ᵥ (a *ᵥ v) := by rw [hv]
    _ = v := by rw [Matrix.mulVec_mulVec, gv_inv_mul ha, Matrix.one_mulVec]

theorem uw_inv {z : Fin (2 * r + k + 1) → ℂ} {a : Mat k r} (ha : a ∈ UWset k r z) : a⁻¹ ∈ UWset k r z := by
  simp only [UWset, Set.mem_setOf_eq] at ha ⊢
  obtain ⟨ha1, ha2, ha3⟩ := ha
  exact ⟨gv_inv ha1, fun i => ⟨fix_inv ha1 (ha2 i).1, fix_inv ha1 (ha2 i).2⟩, fix_inv ha1 ha3⟩

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

structure BEFacts (D : RealPlaceData k r Wp Wp) : Prop where
  nmul : ∀ a ∈ Nset k r, ∀ b ∈ Nset k r, a * b ∈ Nset k r
  ninv : ∀ a ∈ Nset k r, a⁻¹ ∈ Nset k r
  nrm : ∀ h ∈ UWset k r D.z, ∀ m ∈ Nset k r, h * m * h⁻¹ ∈ Nset k r ∧ psiD D (h * m * h⁻¹) = psiD D m
  pmul : ∀ a ∈ Nset k r, ∀ b ∈ Nset k r, psiD D (a * b) = psiD D a * psiD D b
  conj : ∀ h ∈ UWset k r D.z, D.μN.map (conjM h) = D.μN

theorem beFacts_of (h : UnitaryGroupStructuralFacts) (D : RealPlaceData k r Wp Wp) : BEFacts D := by
  obtain ⟨hB2, hBS, hR1, hBC, hUWb, hCH, hLB, hJ, hPh, hRB, hRA, hUn, hAe, hDJ, hIN, hUWN, hEll, hNS⟩ := h
  refine ⟨fun a ha b hb => (hNS k r).2.1 a ha b hb, fun a ha => (hNS k r).2.2 a ha, ?_, ?_, ?_⟩
  · intro g hg m hm
    obtain ⟨hmem, hell⟩ := hUWN k r D.z D.z_mem g hg m hm
    refine ⟨hmem, ?_⟩
    simp only [psiD, psi, hell]
  · intro a ha b hb
    simp only [psiD, psi, hEll k r D.z D.z_mem a ha b hb, mul_add, Complex.add_re, Complex.ofReal_add,
      Complex.exp_add]
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hCI, _⟩ := hB2
    have hc := hCI k r Wp Wp D
    exact fun g hg => hc g (Set.mem_union_left _ hg)

end ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv
end
end

section

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem stFrame : StFrame := by
  intro k r z _hk hz hT
  set T := Tz k r z with hTdef
  set s : ℝ := (Real.sqrt T)⁻¹ with hs

  have hTeq : T = ‖z (wI k r (Fin.last k))‖ ^ 2 - ∑ l : Fin k, ‖z (wI k r l.castSucc)‖ ^ 2 := by
    have h := frame_herm k r z hz
    simp only [frameMat_star_mul_self] at h
    rw [hTdef, Tz, h, ← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.ofReal_re]
    ring
  have hsT : s ^ 2 * T = 1 := by
    rw [hs, inv_pow, Real.sq_sqrt hT.le, inv_mul_cancel₀ hT.ne']
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  refine ⟨frameMat k (fun j => (s : ℂ) * z (wI k r j)), ?_⟩
  unfold IsZFrame
  constructor
  · apply frameMat_unitary
    simp only [frameMat_star_mul_self]
    have key : ∑ l : Fin k, ‖(s : ℂ) * z (wI k r l.castSucc)‖ ^ 2 =
        ‖(s : ℂ) * z (wI k r (Fin.last k))‖ ^ 2 - 1 := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0, mul_pow,
        ← Finset.mul_sum]
      linear_combination (-1 : ℝ) * hsT + s ^ 2 * hTeq
    rw [← Complex.ofReal_sum, key, Complex.ofReal_sub, Complex.ofReal_one]
  · have hlast : (wI k r (Fin.last k)).val = r + k := by simp [frame_wI_val]
    funext i
    simp only [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.smul_apply, smul_eq_mul]
    unfold embWb
    by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · rw [dite_eq_left ⟨hi, by omega, by omega⟩]
      rw [show ∀ p, (⟨(wI k r (Fin.last k)).val - r, p⟩ : Fin (k + 1)) = Fin.last k from
        fun p => Fin.ext (by simp only [Fin.val_last]; omega)]
      rw [frameMat_col]
      rw [show ∀ p, wI k r (⟨i.val - r, p⟩ : Fin (k + 1)) = i from
        fun p => Fin.ext (by rw [frame_wI_val]; show r + (i.val - r) = i.val; omega)]
    · rw [dite_eq_right (fun h => hi h.1)]
      have hne : ¬ (i = wI k r (Fin.last k) ∧ ¬ (r ≤ i.val ∧ i.val ≤ r + k)) := by
        rintro ⟨rfl, h⟩
        exact h ⟨by omega, by omega⟩
      rw [if_neg hne, hz i (by omega), mul_zero]

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end
