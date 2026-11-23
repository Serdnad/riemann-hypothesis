module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NGClosed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SynthesizedVectorZPairing
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact
import Formalism.RealPlaceAnalysis.FinalF
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.REAL Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames

variable {n r k : ℕ} {ε : Fin n → Bool} {e p : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℝ}

theorem hJ_syn_syn {w : Fin k → Fin n → ℂ} (F : Frm ε e p z w T) (α β : Fin r → ℂ) (γ : ℂ) (δ : Fin k → ℂ)
    (α' β' : Fin r → ℂ) (γ' : ℂ) (δ' : Fin k → ℂ) :
    hJ ε (syn e p z w T α β γ δ) (syn e p z w T α' β' γ' δ') =
      ∑ a, α' a * conj (β a) + ∑ a, β' a * conj (α a) + (-γ' / (T : ℂ)) * conj γ + ∑ j, δ' j * conj (δ j) := by
  rw [hJ_syn]
  have h1 : ∀ a, hJ ε (syn e p z w T α β γ δ) (e a) = conj (β a) := fun a => by rw [UnitaryIsometries.hJ_conj, syn_e F]
  have h2 : ∀ a, hJ ε (syn e p z w T α β γ δ) (p a) = conj (α a) := fun a => by rw [UnitaryIsometries.hJ_conj, syn_p F]
  have h3 : hJ ε (syn e p z w T α β γ δ) z = conj γ := by rw [UnitaryIsometries.hJ_conj, synthesized_vector_z_pairing F]
  have h4 : ∀ j, hJ ε (syn e p z w T α β γ δ) (w j) = conj (δ j) := fun j => by rw [UnitaryIsometries.hJ_conj, syn_w F]
  simp only [h1, h2, h3, h4]

def frL (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w y : Fin k → Fin n → ℂ) (T : ℝ) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun v := syn e p z y T (fun a => hJ ε (p a) v) (fun a => hJ ε (e a) v) (hJ ε z v) (fun j => hJ ε (w j) v)
  map_add' v v' := by
    simp only [syn, UnitaryIsometries.hJ_add_right, add_smul, Finset.sum_add_distrib, neg_add, add_div]
    abel
  map_smul' c v := by
    simp only [syn, UnitaryIsometries.hJ_smul_right, RingHom.id_apply, smul_add, Finset.smul_sum, smul_smul]
    rw [show -(c * hJ ε z v) / (T : ℂ) = c * (-hJ ε z v / T) by ring]

def frM (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w y : Fin k → Fin n → ℂ) (T : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix' (frL (ε := ε) e p z w y T)

theorem frM_apply (w y : Fin k → Fin n → ℂ) (v : Fin n → ℂ) :
    frM (ε := ε) e p z w y T *ᵥ v =
      syn e p z y T (fun a => hJ ε (p a) v) (fun a => hJ ε (e a) v) (hJ ε z v) (fun j => hJ ε (w j) v) := by
  rw [frM, LinearMap.toMatrix'_mulVec]
  rfl

theorem frM_isIsom {w y : Fin k → Fin n → ℂ} (Fw : Frm ε e p z w T) (Fy : Frm ε e p z y T)
    (hdim : n = 2 * r + 1 + k) : UnitaryIsometries.IsIsom ε (frM (ε := ε) e p z w y T) := by
  intro v v'
  rw [frM_apply, frM_apply, hJ_syn_syn Fy]
  conv_rhs => rw [recon Fw hdim v, recon Fw hdim v', hJ_syn_syn Fw]

theorem frM_fix {w y : Fin k → Fin n → ℂ} (Fw : Frm ε e p z w T) (hdim : n = 2 * r + 1 + k) {v : Fin n → ℂ}
    (hv : ∀ j, hJ ε (w j) v = 0) : frM (ε := ε) e p z w y T *ᵥ v = v := by
  rw [frM_apply]
  conv_rhs => rw [recon Fw hdim v]
  simp only [syn, hv, zero_smul, Finset.sum_const_zero]

theorem frM_w {w y : Fin k → Fin n → ℂ} (Fw : Frm ε e p z w T) (j : Fin k) :
    frM (ε := ε) e p z w y T *ᵥ w j = y j := by
  rw [frM_apply]
  simp only [syn, Fw.pw, Fw.ew, Fw.zw, Fw.ww, zero_smul, Finset.sum_const_zero, zero_add, neg_zero, zero_div,
    ite_smul, one_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem span_perp {w : Fin k → Fin n → ℂ} (F : Frm ε e p z w T) (a : ℕ) :
    ∀ x ∈ spanLt e a, ∀ j, hJ ε x (w j) = 0 := by
  intro x hx j
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, _, rfl⟩ := hy
    exact F.ew b j
  | zero => exact UnitaryIsometries.hJ_zero_left ε _
  | add x y _ _ hx hy => rw [UnitaryIsometries.hJ_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [UnitaryIsometries.hJ_smul_left, hx, mul_zero]

theorem spanLt_le (a : ℕ) (h : a ≤ r) : spanLt e a ≤ spanLt e r := by
  unfold spanLt
  refine Submodule.span_mono ?_
  rintro _ ⟨b, hb, rfl⟩
  exact ⟨b, b.2, rfl⟩

theorem mem_NH {w : Fin k → Fin n → ℂ} (Fw : Frm ε e p z w T) (hdim : n = 2 * r + 1 + k) {s : UJ ε}
    (hs : s ∈ UnitaryIsometries.RI.SG ε e z) : ∃ m ∈ NG ε e z, ∃ h ∈ HG ε e p z, s = m * h := by
  set M := Formalism.MainNotions.S.uMat s with hM
  have hsi : s⁻¹ ∈ UnitaryIsometries.RI.SG ε e z := (UnitaryIsometries.RI.SG ε e z).inv_mem hs
  have hiso := UnitaryIsometries.isIsom_uMat ε s
  have hback : ∀ v : Fin n → ℂ, M *ᵥ (Formalism.MainNotions.S.uMat s⁻¹ *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, hM, uMat_mul_inv, one_mulVec]
  have hMe : ∀ a j, hJ ε (e a) (M *ᵥ w j) = 0 := by
    intro a j
    rw [← hback (e a), hiso]
    have hx := hsi.1 a
    have hdec : Formalism.MainNotions.S.uMat s⁻¹ *ᵥ e a = e a + (Formalism.MainNotions.S.uMat s⁻¹ - 1) *ᵥ e a := by
      rw [Matrix.sub_mulVec, one_mulVec]; abel
    rw [hdec, UnitaryIsometries.hJ_add_left, Fw.ew, span_perp Fw a.1 _ hx j, add_zero]
  have hMz : ∀ j, hJ ε z (M *ᵥ w j) = 0 := by
    intro j
    rw [← hback z, hiso]
    have hx := hsi.2
    have hdec : Formalism.MainNotions.S.uMat s⁻¹ *ᵥ z = z + (Formalism.MainNotions.S.uMat s⁻¹ - 1) *ᵥ z := by
      rw [Matrix.sub_mulVec, one_mulVec]; abel
    rw [hdec, UnitaryIsometries.hJ_add_left, Fw.zw, span_perp Fw r _ hx j, add_zero]
  set y : Fin k → Fin n → ℂ := fun j => M *ᵥ w j - ∑ a, hJ ε (p a) (M *ᵥ w j) • e a with hy
  have hpe : ∀ a b, hJ ε (p a) (e b) = if b = a then 1 else 0 := fun a b => hJ_swapδ Fw.ep b a
  have hwe : ∀ j b, hJ ε (M *ᵥ w j) (e b) = 0 := fun j b => hJ_swap0 (hMe b j)
  have Fy : Frm ε e p z y T := by
    refine ⟨Fw.ee, Fw.ep, Fw.pp, Fw.ez, Fw.pz, Fw.zz, fun a j => ?_, fun a j => ?_, fun j => ?_, fun i j => ?_,
      Fw.T_ne⟩
    · simp only [hy, UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_sum_right, Fw.ee, mul_zero, Finset.sum_const_zero, sub_zero, hMe]
    · simp only [hy, UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_sum_right, hpe, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
    · have hze : ∀ b, hJ ε z (e b) = 0 := fun b => hJ_swap0 (Fw.ez b)
      simp only [hy, UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_sum_right, hze, mul_zero, Finset.sum_const_zero, sub_zero, hMz]
    · simp only [hy, UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_sub_left, UnitaryIsometries.hJ_sum_right, UnitaryIsometries.hJ_sum_left, hwe, Fw.ee, hMe,
        mul_zero, Finset.sum_const_zero, sub_zero]
      rw [hM]
      exact (hiso _ _).trans (Fw.ww i j)
  have hI := frM_isIsom Fw Fy hdim
  set hU := UnitaryIsometries.toUJ ε hI with hUdef
  have hUm : Formalism.MainNotions.S.uMat hU = frM (ε := ε) e p z w y T := UnitaryIsometries.uMat_toUJ ε hI
  have hUe : ∀ a, Formalism.MainNotions.S.uMat hU *ᵥ e a = e a := fun a => by
    rw [hUm]; exact frM_fix Fw hdim fun j => hJ_swap0 (Fw.ew a j)
  have hUp : ∀ a, Formalism.MainNotions.S.uMat hU *ᵥ p a = p a := fun a => by
    rw [hUm]; exact frM_fix Fw hdim fun j => hJ_swap0 (Fw.pw a j)
  have hUz : Formalism.MainNotions.S.uMat hU *ᵥ z = z := by
    rw [hUm]; exact frM_fix Fw hdim fun j => hJ_swap0 (Fw.zw j)
  have hUH : hU ∈ HG ε e p z := ⟨hUe, hUp, hUz⟩
  have hUw : ∀ j, Formalism.MainNotions.S.uMat hU⁻¹ *ᵥ y j = w j := fun j => by
    rw [← frM_w (y := y) Fw j, ← hUm, mulVec_mulVec, uMat_inv_mul, one_mulVec]
  refine ⟨s * hU⁻¹, ?_, hU, hUH, by group⟩
  have hmv : ∀ v, (Formalism.MainNotions.S.uMat (s * hU⁻¹) - 1) *ᵥ v = M *ᵥ (Formalism.MainNotions.S.uMat hU⁻¹ *ᵥ v) - v := fun v => by
    rw [uMat_mul, Matrix.sub_mulVec, one_mulVec, ← mulVec_mulVec]
  have hme : ∀ a, (Formalism.MainNotions.S.uMat (s * hU⁻¹) - 1) *ᵥ e a = (M - 1) *ᵥ e a := fun a => by
    rw [hmv, inv_fix ε (hUe a), Matrix.sub_mulVec, one_mulVec]
  have hmz : (Formalism.MainNotions.S.uMat (s * hU⁻¹) - 1) *ᵥ z = (M - 1) *ᵥ z := by
    rw [hmv, inv_fix ε hUz, Matrix.sub_mulVec, one_mulVec]
  have hmy : ∀ j, (Formalism.MainNotions.S.uMat (s * hU⁻¹) - 1) *ᵥ y j ∈ spanLt e r := fun j => by
    rw [hmv, hUw, hy, sub_sub_cancel]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, a.2, rfl⟩)
  refine ⟨⟨fun a => ?_, ?_⟩, fun v hv => ?_⟩
  · rw [hme]; exact hs.1 a
  · rw [hmz]; exact hs.2
  · rw [recon Fy hdim v]
    simp only [syn, mulVec_add, mulVec_sum, mulVec_smul, hv, zero_smul, Finset.sum_const_zero, add_zero]
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_)
      (Submodule.smul_mem _ _ ?_)) (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hmy j))
    · rw [hme]; exact spanLt_le a.1 (le_of_lt a.2) (hs.1 a)
    · rw [hmz]; exact hs.2

end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH
end
end

section

noncomputable section

open MeasureTheory Matrix Topology
open scoped ComplexConjugate ENNReal NNReal

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.REAL Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames

variable {n r k : ℕ} {ε : Fin n → Bool} {e p : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℝ}

theorem HG_compact {w : Fin k → Fin n → ℂ} (Fw : Frm ε e p z w T) (hdim : n = 2 * r + 1 + k) :
    IsCompact (HG ε e p z : Set (UJ ε)) := by
  set Q : Set (Matrix (Fin n) (Fin n) ℂ) := {g | gᴴ * Jm ε * g = Jm ε} ∩ ((⋂ a, {g | g *ᵥ e a = e a}) ∩
    ((⋂ a, {g | g *ᵥ p a = p a}) ∩ {g | g *ᵥ z = z})) with hQ
  have e1 : (HG ε e p z : Set (UJ ε)) = (fun g : UJ ε => Formalism.MainNotions.S.uMat g) ⁻¹' Q := by
    ext g
    simp only [coe_HG, HLoc, hQ, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨fun h => ⟨g.2, h.1, h.2.1, h.2.2⟩, fun h => ⟨h.2.1, h.2.2.1, h.2.2.2⟩⟩
  have hQc : IsClosed Q := by
    refine (isClosed_eq ((continuous_id.matrix_conjTranspose.mul continuous_const).mul continuous_id)
      continuous_const).inter ((isClosed_iInter fun a => isClosed_eq (continuous_id.matrix_mulVec continuous_const)
        continuous_const).inter ((isClosed_iInter fun a => isClosed_eq (continuous_id.matrix_mulVec continuous_const)
          continuous_const).inter (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const)))
  have hzz : hJ ε z z ≠ 0 := by
    rw [Fw.zz]; exact neg_ne_zero.2 (Complex.ofReal_ne_zero.2 Fw.T_ne)
  have hQk : IsCompact Q := Formalism.L2.SG.Pf.frame_compact ε e p z w Fw.ee Fw.pp Fw.ep Fw.ez Fw.pz hzz Fw.ww Fw.ew Fw.pw
    Fw.zw hdim.symm hQc (fun g hg => ⟨hg.1, fun a => Set.mem_iInter.1 hg.2.1 a,
      fun a => Set.mem_iInter.1 hg.2.2.1 a, hg.2.2.2⟩)
  rw [e1]
  exact ((Formalism.REAL.uJEmb n ε).1).isCompact_preimage hQk

def conjH (h : UJ ε) : UJ ε ≃ₜ UJ ε := (Homeomorph.mulLeft h).trans (Homeomorph.mulRight h⁻¹)

theorem conjH_apply (h x : UJ ε) : conjH h x = h * x * h⁻¹ := rfl

section Conj

theorem map_conj_isHaarS {μ : Measure (UJ ε)} (hμ : IsHaarS (NLoc ε e z) μ) {h : UJ ε}
    (hh : h ∈ HG ε e p z) : IsHaarS (NLoc ε e z) (μ.map (conjH h)) := by
  obtain ⟨⟨hσ, hne, hcompl, hinv⟩, hfin⟩ := hμ
  have hmeas : Measurable (conjH h) := (conjH h).continuous.measurable
  set E := (conjH h).toMeasurableEquiv with hE
  have hEe : ⇑E = ⇑(conjH h) := rfl
  refine ⟨⟨?_, ?_, ?_, fun t ht => ?_⟩, ?_⟩
  · rw [← hEe]; exact E.sigmaFinite_map
  · intro h0
    apply hne
    have := congrArg (fun m : Measure (UJ ε) => m Set.univ) h0
    simp only [Measure.map_apply hmeas MeasurableSet.univ, Set.preimage_univ, FunLike.coe_zero,
      Pi.zero_apply] at this
    exact Measure.measure_univ_eq_zero.1 this
  · rw [Measure.map_apply hmeas (show MeasurableSet (NLoc ε e z)ᶜ from (NG_closed ε e z).measurableSet.compl)]
    refine measure_mono_null (s := (conjH h) ⁻¹' (NLoc ε e z)ᶜ) (t := (NLoc ε e z)ᶜ)
      (fun x hx hxN => hx ?_) hcompl
    exact conj_mem ε e p z hh hxN
  · have ht' : h⁻¹ * t * h ∈ (NG ε e z) := by
      have := conj_mem ε e p z ((HG ε e p z).inv_mem hh) ht
      simpa using this
    have hcomm : (fun x => t * x) ∘ conjH h = conjH h ∘ (fun x => h⁻¹ * t * h * x) := by
      funext x; simp only [Function.comp_apply, conjH_apply]; group
    rw [Measure.map_map (measurable_const_mul t) hmeas, hcomm,
      ← Measure.map_map hmeas (measurable_const_mul _), hinv _ ht']
  · refine ⟨fun K hK => ?_⟩
    rw [Measure.map_apply hmeas hK.measurableSet]
    have : (conjH h) ⁻¹' K = (conjH h).symm '' K := (congrFun (conjH h).image_symm K).symm
    rw [this]
    exact (hK.image (conjH h).symm.continuous).measure_lt_top

theorem conj_haar_eq {w : Fin k → Fin n → ℂ} (Fw : Frm ε e p z w T) (hdim : n = 2 * r + 1 + k)
    {μ : Measure (UJ ε)} (hμ : IsHaarS (NLoc ε e z) μ) {h : UJ ε} (hh : h ∈ HG ε e p z) :
    μ.map (conjH h) = μ := by
  have : LocallyCompactSpace (NG ε e z) := (NG_closed ε e z).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (NG ε e z) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have hNm : MeasurableSet ((NG ε e z) : Set (UJ ε)) := (NG_closed ε e z).measurableSet
  have memb : MeasurableEmbedding (Subtype.val : (NG ε e z) → UJ ε) := MeasurableEmbedding.subtype_coe hNm
  set m0 : Measure (UJ ε) := (Measure.haar : Measure (NG ε e z)).map Subtype.val with hm0

  have huniq : ∀ ν : Measure (UJ ε), IsHaarS (NLoc ε e z) ν → ∃ c : ℝ≥0, ν = c • m0 := by
    intro ν hν
    obtain ⟨⟨hσ, hne, hcompl, hinv⟩, hfin⟩ := hν
    set ν' : Measure (NG ε e z) := ν.comap Subtype.val with hν'
    have hrestr : ν.restrict ((NG ε e z) : Set (UJ ε)) = ν := by
      apply Measure.restrict_eq_self_of_ae_mem
      rw [ae_iff]
      exact hcompl
    have hmapν : ν'.map Subtype.val = ν := by
      rw [hν', memb.map_comap, Subtype.range_coe, hrestr]
    have himg : ∀ (t : (NG ε e z)) (A : Set (NG ε e z)), Subtype.val '' ((fun x => t * x) ⁻¹' A) =
        (fun x => (t : UJ ε) * x) ⁻¹' (Subtype.val '' A) := by
      intro t A
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨t * y, hy, rfl⟩
      · rintro ⟨a, ha, hax⟩
        have hxS : x ∈ (NG ε e z) := by
          have : x = ((t⁻¹ * a : (NG ε e z)) : UJ ε) := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv, hax]; group
          rw [this]; exact (t⁻¹ * a).2
        refine ⟨⟨x, hxS⟩, ?_, rfl⟩
        show t * ⟨x, hxS⟩ ∈ A
        have : t * ⟨x, hxS⟩ = a := Subtype.ext (by simpa using hax.symm)
        rw [this]; exact ha
    have hνinv : ν'.IsMulLeftInvariant := by
      refine ⟨fun t => ?_⟩
      ext A hA
      rw [Measure.map_apply (measurable_const_mul t) hA, hν', memb.comap_apply, memb.comap_apply, himg,
        ← Measure.map_apply (measurable_const_mul _) (memb.measurableSet_image.2 hA), hinv _ t.2]
    have hνfin : IsFiniteMeasureOnCompacts ν' := by
      refine ⟨fun K hK => ?_⟩
      rw [hν', memb.comap_apply]
      exact (hK.image continuous_subtype_val).measure_lt_top
    have hνeq : ν' = ν'.haarScalarFactor Measure.haar • Measure.haar :=
      Measure.isMulLeftInvariant_eq_smul ν' Measure.haar
    refine ⟨ν'.haarScalarFactor Measure.haar, ?_⟩
    conv_lhs => rw [← hmapν, hνeq]
    rw [Measure.map_smul _ measurable_subtype_coe.aemeasurable]

  obtain ⟨C', hC'c, hC'n⟩ : ∃ C' : Set (NG ε e z), IsCompact C' ∧ C' ∈ 𝓝 (1 : (NG ε e z)) := by
    obtain ⟨C', h1, h2⟩ := exists_compact_mem_nhds (1 : (NG ε e z))
    exact ⟨C', h1, h2⟩
  have hC'pos : 0 < (Measure.haar : Measure (NG ε e z)) C' := Measure.measure_pos_of_mem_nhds _ hC'n
  set C : Set (UJ ε) := Subtype.val '' C' with hC
  have hHc := HG_compact Fw hdim
  set K : Set (UJ ε) := (fun q : UJ ε × UJ ε => q.1 * q.2 * q.1⁻¹) '' ((HG ε e p z : Set (UJ ε)) ×ˢ C) with hK
  have hKc : IsCompact K :=
    (hHc.prod (hC'c.image continuous_subtype_val)).image (by fun_prop)
  have hKN : K ⊆ ((NG ε e z) : Set (UJ ε)) := by
    rintro _ ⟨⟨h', x⟩, ⟨hh', ⟨x', _, rfl⟩⟩, rfl⟩
    exact conj_mem ε e p z hh' x'.2
  have hCK : C ⊆ K := fun x hx => ⟨(1, x), ⟨(HG ε e p z).one_mem, hx⟩, by simp⟩
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hm0K : m0 K = (Measure.haar : Measure (NG ε e z)) (Subtype.val ⁻¹' K) := by
    rw [hm0, Measure.map_apply measurable_subtype_coe hKm]
  have hm0pos : 0 < m0 K := by
    rw [hm0K]
    refine lt_of_lt_of_le hC'pos (measure_mono ?_)
    intro x hx
    exact hCK ⟨x, hx, rfl⟩
  have hm0fin : m0 K < ⊤ := by
    rw [hm0K]
    exact ((NG_closed ε e z).isClosedEmbedding_subtypeVal.isCompact_preimage hKc).measure_lt_top
  have hinvK : (conjH h) ⁻¹' K = K := by
    ext x
    constructor
    · rintro ⟨⟨h', x'⟩, ⟨hh', hx'⟩, hxe⟩
      refine ⟨(h⁻¹ * h', x'), ⟨(HG ε e p z).mul_mem ((HG ε e p z).inv_mem hh) hh', hx'⟩, ?_⟩
      have hxe' : h' * x' * h'⁻¹ = h * x * h⁻¹ := hxe
      show (h⁻¹ * h') * x' * (h⁻¹ * h')⁻¹ = x
      rw [show (h⁻¹ * h') * x' * (h⁻¹ * h')⁻¹ = h⁻¹ * (h' * x' * h'⁻¹) * h by group, hxe']
      group
    · rintro ⟨⟨h', x'⟩, ⟨hh', hx'⟩, rfl⟩
      refine ⟨(h * h', x'), ⟨(HG ε e p z).mul_mem hh hh', hx'⟩, ?_⟩
      simp only [conjH_apply]
      group

  obtain ⟨c1, h1⟩ := huniq μ hμ
  obtain ⟨c2, h2⟩ := huniq _ (map_conj_isHaarS hμ hh)
  have hK12 : (μ.map (conjH h)) K = μ K := by
    rw [Measure.map_apply (conjH h).continuous.measurable hKm, hinvK]
  have hc : (c2 : ℝ≥0∞) = c1 := by
    have e2 : (μ.map (conjH h)) K = c2 * m0 K := by
      conv_lhs => rw [h2]
      rfl
    have e1 : μ K = c1 * m0 K := by
      conv_lhs => rw [h1]
      rfl
    rw [e2, e1] at hK12
    exact (ENNReal.mul_left_inj hm0pos.ne' hm0fin.ne).1 hK12
  rw [h2, h1]
  congr 1
  exact_mod_cast hc

end Conj

end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH
end
end
