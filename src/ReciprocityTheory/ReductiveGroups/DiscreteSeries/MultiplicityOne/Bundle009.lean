module

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.UHMulInv
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle007
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Module.HahnBanach
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeConvA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle006
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroupA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JTransMA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JTransMB

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

namespace GroupMatrixMembership

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section hpk
variable (k r : ℕ)

theorem Hpk_out {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 :=
  ReciprocityTheory.ChartRestriction.DS.Xi.StepA.Hpk_out k r h j

theorem Hpk_mid {i : Fin (2 * r + k + 1)} (h : ¬(i.val < r ∨ r + k < i.val)) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = i.val then (if i.val = r + k then -1 else 1) else 0 :=
  ReciprocityTheory.ChartRestriction.DS.Xi.StepA.Hpk_mid k r h j

theorem Hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i :=
  ReciprocityTheory.ChartRestriction.DS.Xi.StepA.Hpk_mulVec k r v i

theorem Hpk_mulVec_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v :=
  ReciprocityTheory.ChartRestriction.DS.Xi.StepA.Hpk_mulVec_mulVec k r v

theorem mat_eq_of_mulVec {A B : Mat k r} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  simpa [Matrix.mulVec_single_one] using congrFun (h (Pi.single j 1)) i

theorem Hpk_sq : Hpk k r * Hpk k r = 1 :=
  ReciprocityTheory.ChartRestriction.DS.Xi.StepA.Hpk_sq k r

theorem UH_left_inv {g : Mat k r} (hg : g ∈ GV k r) : Hpk k r * gᴴ * Hpk k r * g = 1 :=
  ReciprocityTheory.ChartRestriction.DS.Xi.StepA.UH_left_inv k r hg

end hpk

variable {k r : ℕ}

theorem GV_inv_mul {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ * g = 1 :=
  ReciprocityTheory.ChartRestriction.DS.Xi.StepA.UH_inv_mul k r hg

theorem GV_mul_inv {g : Mat k r} (hg : g ∈ GV k r) : g * g⁻¹ = 1 :=
  ReciprocityTheory.ChartRestriction.DS.Xi.StepA.UH_mul_inv k r hg

theorem GV_mul_mem {g h : Mat k r} (hg : g ∈ GV k r) (hh : h ∈ GV k r) : g * h ∈ GV k r := by
  show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  calc (g * h)ᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hh']

theorem GV_inv_mem {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ ∈ GV k r := by
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hg']
    _ = ((g⁻¹)ᴴ * gᴴ) * Hpk k r * (g * g⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by
        rw [← Matrix.conjTranspose_mul, GV_mul_inv hg, Matrix.conjTranspose_one, Matrix.one_mul,
          Matrix.mul_one]

theorem sig_mul (X : SigData k r) {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r) :
    X.σ (a * b) = (X.σ a).comp (X.σ b) := X.rep.1.2 a ha b hb

theorem sig_inv (X : SigData k r) {a : Mat k r} (ha : a ∈ GV k r) :
    X.σ a⁻¹ = ContinuousLinearMap.adjoint (X.σ a) := by
  have h1 : ContinuousLinearMap.adjoint (X.σ a) ∘L X.σ a = 1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).1 (X.rep.2.1 a ha)
  have h2 : X.σ a ∘L X.σ a⁻¹ = 1 := by
    rw [← X.rep.1.2 a ha _ (GV_inv_mem ha), GV_mul_inv ha, X.rep.1.1]
  ext v
  have e1 := congrArg (fun T => T (X.σ a⁻¹ v)) h1
  have e2 := congrArg (fun T => T v) h2
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at e1 e2
  rw [← e1, e2]

theorem mc_conj (X : SigData k r) (x y : X.Hs) {s g s' : Mat k r} (hs : s ∈ GV k r) (hg : g ∈ GV k r)
    (hs' : s' ∈ GV k r) : mc X x y (s⁻¹ * g * s') = mc X (X.σ s' x) (X.σ s y) g := by
  have h1 : s⁻¹ * g ∈ GV k r := GV_mul_mem (GV_inv_mem hs) hg
  simp only [mc]
  rw [sig_mul X h1 hs', sig_mul X (GV_inv_mem hs) hg, sig_inv X hs]
  simp only [ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_right]

theorem sgs_eq (p : SS k r) (g : Mat k r) :
    sgs p g = (Matrix.of p.1.2 * Matrix.of p.1.1)⁻¹ * g * (Matrix.of p.2.2 * Matrix.of p.2.1) := by
  simp only [sgs, Matrix.mul_inv_rev, Matrix.mul_assoc]

section hs

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem hsVec_smul (c : ℂ) (A : Wp →L[ℂ] Wp) : hsVec (c • A) = c • hsVec A := rfl

theorem hsInner_smul_left (c : ℂ) (A B : Wp →L[ℂ] Wp) : hsInner (c • A) B = c * hsInner A B := by
  simp only [hsInner, hsVec_smul, inner_smul_right]

theorem hsInner_smul_right (c : ℂ) (A B : Wp →L[ℂ] Wp) : hsInner A (c • B) = conj c * hsInner A B := by
  simp only [hsInner, hsVec_smul, inner_smul_left]

theorem rho_scal (D : RealPlaceData k r Wp Wp) (p : SS k r) (f : Mat k r → ℂ) (g : Mat k r) :
    rho D p (scalF Wp f) g = f (sgs p g) • (D.π (Matrix.of p.1.1)).comp (D.π' (Matrix.of p.2.1)⁻¹) := by
  simp only [rho, scalF, ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp,
    ContinuousLinearMap.comp_smul]

end hs

end GroupMatrixMembership

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GroupMatrixMembership

theorem stCut1 (h : UnitaryGroupStructuralFacts) : StCut1 := by
  unfold StCut1
  intro k r Wp _ _ _ D X hD d hd f x y a₂ b₂ X₀ hf p hp
  obtain ⟨hh, hn, hh', hn'⟩ := hp
  have hs : Matrix.of p.1.2 * Matrix.of p.1.1 ∈ GV k r := GV_mul_mem hn.1 hh.1
  have hs' : Matrix.of p.2.2 * Matrix.of p.2.1 ∈ GV k r := GV_mul_mem hn'.1 hh'.1
  have hG : ∀ᵐ g ∂D.μG, (Matrix.of g : Mat k r) ∈ GV k r :=
    ae_iff.2 (measure_mono_null (fun g hg => hg) D.haarG.conc)
  have key : ∀ᵐ g ∂D.μG, hsInner (rho D p (scalF Wp f) (Matrix.of g)) (mc X a₂ b₂ (Matrix.of g) • X₀) =
      (mc X (X.σ (Matrix.of p.2.2 * Matrix.of p.2.1) x) (X.σ (Matrix.of p.1.2 * Matrix.of p.1.1) y)
          (Matrix.of g) * conj (mc X a₂ b₂ (Matrix.of g))) *
        hsInner ((D.π (Matrix.of p.1.1)).comp (D.π (Matrix.of p.2.1)⁻¹)) X₀ := by
    filter_upwards [hG] with g hg
    rw [rho_scal, hD.π_eq, hsInner_smul_left, hsInner_smul_right, sgs_eq,
      hf _ (GV_mul_mem (GV_mul_mem (GV_inv_mem hs) hg) hs'), mc_conj X x y hs hg hs']
    ring
  simp only [Ph]
  rw [integral_congr_ae key, integral_mul_const]
  have hS := (hd.2 (X.σ (Matrix.of p.2.2 * Matrix.of p.2.1) x) (X.σ (Matrix.of p.1.2 * Matrix.of p.1.1) y)
    a₂ b₂).2
  have e1 : ∫ g : Mt k r, mc X (X.σ (Matrix.of p.2.2 * Matrix.of p.2.1) x)
      (X.σ (Matrix.of p.1.2 * Matrix.of p.1.1) y) (Matrix.of g) * conj (mc X a₂ b₂ (Matrix.of g)) ∂D.μG =
      ⟪a₂, X.σ (Matrix.of p.2.2 * Matrix.of p.2.1) x⟫_ℂ * ⟪X.σ (Matrix.of p.1.2 * Matrix.of p.1.1) y, b₂⟫_ℂ /
        (d : ℂ) := hS
  have e2 : star (mc X y b₂ (Matrix.of p.1.2 * Matrix.of p.1.1)) =
      ⟪X.σ (Matrix.of p.1.2 * Matrix.of p.1.1) y, b₂⟫_ℂ := inner_conj_symm _ _
  have e3 : mc X x a₂ (Matrix.of p.2.2 * Matrix.of p.2.1) = ⟪a₂, X.σ (Matrix.of p.2.2 * Matrix.of p.2.1) x⟫_ℂ :=
    rfl
  rw [e1, e2, e3]
  ring

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem stSInt (h : UnitaryGroupStructuralFacts) : StSInt := by
  intro k r Wp _ _ _ D hD b hb
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hGL, -, -, -, hCG, -⟩, -⟩ := id h
  have sW := bc_isHaarOn_sigmaFinite D.haarW
  have sN := bc_isHaarOn_sigmaFinite D.haarN
  have hfin := bc_lintegral_S_pow_AB h D (by rw [hD.μW_eq])
  have hAB1 : 1 ≤ AB k r := by
    rw [AB]; have := Nat.cast_nonneg (α := ℝ) k; have := Nat.cast_nonneg (α := ℝ) r; nlinarith
  have hmeas : Measurable (fun p : Mt k r × Mt k r => gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b)) :=
    ((bc_gN_cont_mt.comp (bc_continuous_mulM.comp continuous_swap)).measurable).pow_const _
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun p => Real.rpow_nonneg (bc_gN_nonneg _) _)]
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) hfin
  have aeS : ∀ᵐ p1 ∂(D.μW.prod D.μN), (Matrix.of p1.1 : Mat k r) ∈ UWset k r D.z ∧
      (Matrix.of p1.2 : Mat k r) ∈ Nset k r :=
    bc_ae_prod_and (bc_isHaarOn_ae_mem D.haarW) (bc_isHaarOn_ae_mem D.haarN)
  filter_upwards [aeS] with p hp
  have hG : (Matrix.of p.2 : Mat k r) * Matrix.of p.1 ∈ GV k r := (hCG k r).mul_mem _ hp.2.1 _ hp.1.1
  change ENNReal.ofReal (gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b)) ≤
    ENNReal.ofReal (gN (Matrix.of p.2 * Matrix.of p.1) ^ (-AB k r))
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (hGL k r _ hG) (by linarith))

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SquareIntegrabilityOnOrbit

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv ReciprocityTheory.ChartRestriction.DS.Mult1.Fold

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem gnInt_of (h : UnitaryGroupStructuralFacts) : GNIntSharp := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hGI, -⟩, -⟩ := id h
  exact hGI

theorem closed_GV (h : UnitaryGroupStructuralFacts) : IsClosed {y : Mt k r | (Matrix.of y : Mat k r) ∈ GV k r} := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hCG, -⟩, -⟩ := id h
  exact (hCG k r).closed

theorem aesm_of_contOn (h : UnitaryGroupStructuralFacts) (D : RealPlaceData k r Wp Wp) {F : Type} [NormedAddCommGroup F]
    [SecondCountableTopologyEither (Mt k r) F] {f : Mat k r → F} (hf : ContinuousOn f (GV k r)) :
    AEStronglyMeasurable (fun y : Mt k r => f (Matrix.of y)) D.μG := by
  have hf' : ContinuousOn (fun y : Mt k r => f (Matrix.of y)) {y : Mt k r | (Matrix.of y : Mat k r) ∈ GV k r} := hf
  have hm := hf'.aestronglyMeasurable (μ := D.μG) (closed_GV h).measurableSet
  have hae : ∀ᵐ y ∂D.μG, y ∈ {y : Mt k r | (Matrix.of y : Mat k r) ∈ GV k r} := ae_mem_of_haarOn D.haarG
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at hm

end ReciprocityTheory.ChartRestriction.DS.Mult1.SquareIntegrabilityOnOrbit
end
end

section

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem stTransM (h : UnitaryGroupStructuralFacts) : StTransM := by
  obtain ⟨hB2, -, -, -, hUWb, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hCG, -⟩ := hB2
  intro k r Wp _ _ _ D X _ _ γ hγ y hy
  have hG := hCG k r
  have hEG : embWb k r γ ∈ GV k r := by
    have hmem : embWb k r γ ∈ UWb k r := by rw [(hUWb k r).1]; exact ⟨γ, hγ.1, rfl⟩
    exact hmem.1
  have hE := hG.unit _ hEG
  set E := embWb k r γ with hEdef
  have hEiG : E⁻¹ ∈ GV k r := hG.inv_mem _ hEG
  have hc : ∀ B : Mat k r, E⁻¹ * (E * B) = B := fun B => Matrix.nonsing_inv_mul_cancel_left E B hE
  have hEE : ∀ v, E⁻¹ *ᵥ (E *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hE, Matrix.one_mulVec]
  have hEfix : ∀ j, ¬ InvGrp.isW k r j → E *ᵥ bvec j = bvec j := fun j hj =>
    InvGrp.embWb_fix_offW γ _ (InvGrp.bvec_offW j hj)
  have hEifix : ∀ j, ¬ InvGrp.isW k r j → E⁻¹ *ᵥ bvec j = bvec j := fun j hj =>
    InvGrp.embWb_inv_fix_offW hE _ (InvGrp.bvec_offW j hj)
  have hwl : ¬ InvGrp.isW k r (wI k r (Fin.last k)) → False := fun h => h ⟨by simp [wI], by simp [wI]⟩
  set b := bvec (wI k r (Fin.last k)) with hbdef
  have hs0 : ((Real.sqrt (Tz k r D.z) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr D.T_pos).ne'
  have hzE : D.z = ((Real.sqrt (Tz k r D.z) : ℝ) : ℂ) • (E *ᵥ b) := by
    rw [hγ.2, smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ hs0, one_smul]

  set x := E⁻¹ * y * E with hxdef
  have hxG : x ∈ GV k r := hG.mul_mem _ (hG.mul_mem _ hEiG _ hy.1) _ hEG
  have hxv : ∀ v, x *ᵥ v = E⁻¹ *ᵥ (y *ᵥ (E *ᵥ v)) := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hxe : ∀ a : Fin r, x *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ x *ᵥ bvec (esI k r a) = bvec (esI k r a) := by
    intro a
    constructor
    · rw [hxv, hEfix _ (InvGrp.not_isW_eI a), (hy.2.1 a).1, hEifix _ (InvGrp.not_isW_eI a)]
    · rw [hxv, hEfix _ (InvGrp.not_isW_esI a), (hy.2.1 a).2, hEifix _ (InvGrp.not_isW_esI a)]
  have hxl : x *ᵥ b = b := by
    rw [hxv, hγ.2, Matrix.mulVec_smul, hy.2.2, ← hγ.2, hEE]
  have hxeq := TransM.eq_Qm x hxG hxe hxl
  set m := x.submatrix (Subtype.val : {i // TransM.pK k r i} → _) Subtype.val with hmdef
  have hm : mᴴ * m = 1 := TransM.unitary_of_Qm m (hxeq ▸ hxG)
  have hw : ∀ s : {i // TransM.pK k r i}, conj (bvec (wI k r 0) s.1) = bvec (wI k r 0) s.1 := by
    intro s
    simp only [bvec, Pi.single_apply]
    split_ifs <;> simp
  obtain ⟨U, hU1, hUw, hUc⟩ := TransM.exists_transpose_mat m hm (fun s => bvec (wI k r 0) s.1) hw
  set PU := TransM.Qm U 1 with hPUdef
  have hPUG : PU ∈ GV k r := TransM.Qm_mem_UH U hU1
  have hPUs : TransM.Qm Uᴴ 1 * PU = 1 := by
    rw [hPUdef, TransM.Qm_mul, hU1, Matrix.one_mul, TransM.Qm_one]
  have hPUs' : PU * TransM.Qm Uᴴ 1 = 1 := by
    rw [hPUdef, TransM.Qm_mul, mul_eq_one_comm.mp hU1, Matrix.one_mul, TransM.Qm_one]
  have hkey : x.map (starRingEnd ℂ) * PU * x = PU := by
    rw [hxeq, TransM.Qm_map, hPUdef, TransM.Qm_mul, TransM.Qm_mul, hUc]
    simp
  have hyx : y = E * x * E⁻¹ := by
    rw [hxdef]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left E _ hE, Matrix.mul_nonsing_inv _ hE, Matrix.mul_one]
  have hnotK : ∀ j, ¬ InvGrp.isW k r j → ¬ TransM.pK k r j := fun j hj hK =>
    hj ⟨hK.1, by have := hK.2; omega⟩
  have hnotKl : ¬ TransM.pK k r (wI k r (Fin.last k)) := fun hK => by
    have := hK.2; simp [wI] at this
  refine ⟨E * PU * E⁻¹, ⟨⟨hG.mul_mem _ (hG.mul_mem _ hEG _ hPUG) _ hEiG, fun a => ⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hEifix _ (InvGrp.not_isW_eI a),
      TransM.Qm_fix_off U _ (hnotK _ (InvGrp.not_isW_eI a)), hEfix _ (InvGrp.not_isW_eI a)]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hEifix _ (InvGrp.not_isW_esI a),
      TransM.Qm_fix_off U _ (hnotK _ (InvGrp.not_isW_esI a)), hEfix _ (InvGrp.not_isW_esI a)]
  · conv_lhs => rw [hzE]
    rw [Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hEE, TransM.Qm_fix_off U _ hnotKl, ← hzE]
  · show (E * PU * E⁻¹) *ᵥ (E *ᵥ bvec (wI k r 0)) = E *ᵥ bvec (wI k r 0)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hEE, TransM.Qm_fix_vec U _ hUw]
  · have hinv : (E * PU * E⁻¹)⁻¹ = E * TransM.Qm Uᴴ 1 * E⁻¹ := by
      apply Matrix.inv_eq_left_inv
      simp only [Matrix.mul_assoc, hc]
      rw [← Matrix.mul_assoc (TransM.Qm Uᴴ 1) PU, hPUs, Matrix.one_mul, Matrix.mul_nonsing_inv _ hE]
    have hgb : gbar k r γ y = E * x.map (starRingEnd ℂ) * E⁻¹ := rfl
    show (gbar k r γ y)⁻¹ = _
    rw [hinv, hgb]
    apply Matrix.inv_eq_right_inv
    rw [hyx]
    simp only [Matrix.mul_assoc, hc]
    rw [← Matrix.mul_assoc (x.map (starRingEnd ℂ)) PU, ← Matrix.mul_assoc (x.map (starRingEnd ℂ) * PU) x, hkey,
      ← Matrix.mul_assoc PU, hPUs', Matrix.one_mul, Matrix.mul_nonsing_inv _ hE]

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

section

noncomputable section

open MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace SmulConstantLinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem deriv_smul_const_all {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (h : ℝ → ℂ) (T : E) :
    deriv (fun t => h t • T) 0 = deriv h 0 • T := by
  by_cases hd : DifferentiableAt ℝ h 0
  · exact deriv_smul_const hd T
  by_cases hT : T = 0
  · simp [hT]
  have hnd : ¬ DifferentiableAt ℝ (fun t => h t • T) 0 := by
    intro hd'
    apply hd
    obtain ⟨g, -, hg⟩ := exists_dual_vector ℂ T (norm_ne_zero_iff.2 hT)
    have hT' : g T ≠ 0 := by
      rw [hg]; simpa using hT
    have heq : h = fun t => (g T)⁻¹ * g (h t • T) := by
      funext t
      rw [map_smul, smul_eq_mul, mul_comm, mul_assoc, mul_inv_cancel₀ hT', mul_one]
    rw [heq]
    exact ((g.restrictScalars ℝ).differentiableAt.comp 0 hd').const_mul _
  rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hnd, zero_smul]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem ldV_smul_const (X : Mat k r) (φ : Mat k r → ℂ) (T : E) :
    LdV X (fun g => φ g • T) = fun g => LdV X φ g • T := by
  funext g
  exact deriv_smul_const_all _ T

theorem rdV_smul_const (X : Mat k r) (φ : Mat k r → ℂ) (T : E) :
    RdV X (fun g => φ g • T) = fun g => RdV X φ g • T := by
  funext g
  exact deriv_smul_const_all _ T

theorem rw_smul_const (v : List (Mat k r)) (φ : Mat k r → ℂ) (T : E) :
    Rw v (fun g => φ g • T) = fun g => Rw v φ g • T := by
  induction v with
  | nil => rfl
  | cons X v ih =>
    show RdV X (Rw v (fun g => φ g • T)) = fun g => RdV X (Rw v φ) g • T
    rw [ih, rdV_smul_const]

theorem dLR_smul_const (u v : List (Mat k r)) (φ : Mat k r → ℂ) (T : E) :
    dLR u v (fun g => φ g • T) = fun g => dLR u v φ g • T := by
  induction u with
  | nil => exact rw_smul_const v φ T
  | cons X u ih =>
    show LdV X (dLR u v (fun g => φ g • T)) = fun g => LdV X (dLR u v φ) g • T
    rw [ih, ldV_smul_const]

theorem ccle_smul_const {A : ℝ} {m : ℕ} {f : Mat k r → ℂ} {c : ℝ} (T : E) (hf : CCle A m f c) :
    CCle A m (fun g => f g • T) (c * ‖T‖) := by
  obtain ⟨hCk, hb⟩ := hf
  refine ⟨fun g₀ hg₀ => ?_, fun u v hu hv hl g hg => ?_⟩
  · obtain ⟨U, f', hU, hgU, hcd, heq⟩ := hCk g₀ hg₀
    refine ⟨U, fun g => f' g • T, hU, hgU, hcd.smul contDiffOn_const, fun g hgU hgG => ?_⟩
    show f g • T = f' g • T
    rw [heq g hgU hgG]
  · have h1 := hb u v hu hv hl g hg
    have hd : dLR u v (fun g => f g • T) g = dLR u v f g • T := by
      rw [dLR_smul_const]
    rw [hd, norm_smul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg T)

end SmulConstantLinearity

theorem stCut1p (h : UnitaryGroupStructuralFacts) : StCut1p := by
  intro k r Wp _ _ _ A m f X₀ hf
  obtain ⟨c, hc⟩ := hf
  exact ⟨c * ‖X₀‖, SmulConstantLinearity.ccle_smul_const X₀ hc⟩

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end
