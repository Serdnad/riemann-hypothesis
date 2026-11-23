module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle004
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CompRevRev
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle007
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiMLocal
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.PsWord
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.TransferB
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.Bundle002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.ProdShiftEeVOfCapelli

@[expose] public section

section

noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

lemma tt_adW_neg (ε : Fin n → Bool) (k : KG ε) (D : List (Matrix (Fin n) (Fin n) ℂ)) :
    adW ε k (D.map Neg.neg) = (adW ε k D).map Neg.neg := by
  simp [adW, List.map_map, Function.comp_def, Matrix.mul_neg, Matrix.neg_mul]

lemma tt_rWord_local {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ)
    {U W : Set (Matrix (Fin n) (Fin n) ℂ)} {k₀ : KG ε} (hU : IsOpen U) (hW : IsOpen W)
    (hdiff : ∀ D, DifferentiableOn ℂ (lWord D (psM T μ)) U)
    (hWU : ∀ g ∈ W, IsUnit g ∧ g⁻¹ * toMK k₀ ∈ U)
    (hloc : ∀ g ∈ W, inUJ ε g → PsiM T μ g = T.op k₀ * psM T μ (g⁻¹ * toMK k₀))
    (D : List (Matrix (Fin n) (Fin n) ℂ)) :
    ∀ g ∈ W, inUJ ε g →
      rWord ε D (PsiM T μ) g = T.op k₀ * lWord (D.map Neg.neg) (psM T μ) (g⁻¹ * toMK k₀) := by
  induction D with
  | nil => exact hloc
  | cons Z D ih =>
    intro g hg hgu
    have hGd : HasFDerivAt (lWord (D.map Neg.neg) (psM T μ))
        (fderiv ℂ (lWord (D.map Neg.neg) (psM T μ)) (g⁻¹ * toMK k₀)) (g⁻¹ * toMK k₀) :=
      ((hdiff _).differentiableAt (hU.mem_nhds (hWU g hg).2)).hasFDerivAt
    have hc : HasFDerivAt (fun y => T.op k₀ * lWord (D.map Neg.neg) (psM T μ) y)
        ((ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V) (T.op k₀)).comp
          (fderiv ℂ (lWord (D.map Neg.neg) (psM T μ)) (g⁻¹ * toMK k₀))) (g⁻¹ * toMK k₀) :=
      (ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V) (T.op k₀)).hasFDerivAt.comp _ hGd
    show EcV ε Z (rWord ε D (PsiM T μ)) g =
      T.op k₀ * Lhol (-Z) (lWord (D.map Neg.neg) (psM T μ)) (g⁻¹ * toMK k₀)
    rw [ta_ecV_local ε (F := fun y => T.op k₀ * lWord (D.map Neg.neg) (psM T μ) y) hW hg hgu
      hc.differentiableAt ih Z]
    unfold Lhol
    rw [hc.fderiv]
    rfl

theorem transfer (n : ℕ) : TransferStatement n := by
  intro ε lam T μ _hlam hμ N D v hyp g₀ hg₀
  obtain ⟨U, hU, hpos, hconj, hword⟩ := psM_word n ε (lowK ε lam) T μ
  obtain ⟨W, k₀, hW, hg₀W, hWU, hloc⟩ := psiM_local T μ hμ U hU hpos hg₀
  have hcpt : CompactSpace (KG ε) := compactSpace_KG ε
  set x₀ := g₀⁻¹ * toMK k₀ with hx₀def
  have hx₀ : x₀ ∈ U := (hWU g₀ hg₀W).2
  have hA : ∀ i, rWord ε (D i) (PsiM T μ) g₀ (v i) =
      T.op k₀ (lWord ((D i).map Neg.neg) (psM T μ) x₀ (v i)) := fun i => by
    rw [tt_rWord_local T μ hU hW (fun D => (hword D).1) hWU hloc (D i) g₀ hg₀W hg₀]
    rfl

  rw [Finset.sum_congr rfl fun i _ => hA i, ← map_sum]
  suffices h : ∑ i, lWord ((D i).map Neg.neg) (psM T μ) x₀ (v i) = 0 by rw [h, map_zero]
  have hopc : Continuous fun k : KG ε => T.op k := continuous_subtype_val.comp T.cont
  have hAc : Continuous fun k : KG ε => T.op k * projW T * T.op k⁻¹ :=
    (hopc.mul continuous_const).mul (hopc.comp continuous_inv)
  have hint : ∀ i, Integrable (fun k : KG ε =>
      lWord (adW ε k ((D i).map Neg.neg)) (PhiM μ) (toMK k⁻¹ * x₀ * toMK k) •
        (T.op k * projW T * T.op k⁻¹)) (muK ε) := fun i =>
    integrableOn_univ.mp ((((hword _).2.1 x₀ hx₀).smul hAc).continuousOn.integrableOn_compact isCompact_univ)
  have hint' : ∀ i ∈ (univ : Finset (Fin N)), Integrable (fun k : KG ε =>
      lWord (adW ε k ((D i).map Neg.neg)) (PhiM μ) (toMK k⁻¹ * x₀ * toMK k) •
        (T.op k * projW T * T.op k⁻¹) (v i)) (muK ε) := fun i _ =>
    integrableOn_univ.mp ((((hword _).2.1 x₀ hx₀).smul (hAc.clm_apply continuous_const)).continuousOn.integrableOn_compact
      isCompact_univ)
  have hterm : ∀ i, lWord ((D i).map Neg.neg) (psM T μ) x₀ (v i) =
      ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
        ∫ k, lWord (adW ε k ((D i).map Neg.neg)) (PhiM μ) (toMK k⁻¹ * x₀ * toMK k) •
          (T.op k * projW T * T.op k⁻¹) (v i) ∂(muK ε) := by
    intro i
    rw [(hword _).2.2 x₀ hx₀, ContinuousLinearMap.smul_apply, ContinuousLinearMap.integral_apply (hint i)]
    rfl
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.smul_sum, ← MeasureTheory.integral_finsetSum _ hint']
  have hAv : ∀ (k : KG ε) (u : T.V), (T.op k * projW T * T.op k⁻¹) u = ⟪T.op k T.w, u⟫_ℂ • T.op k T.w := by
    intro k u
    simp only [ContinuousLinearMap.mul_apply, projW, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, map_smul, op_inv_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  have hzero : ∀ k : KG ε, ∑ i, lWord (adW ε k ((D i).map Neg.neg)) (PhiM μ) (toMK k⁻¹ * x₀ * toMK k) •
      (T.op k * projW T * T.op k⁻¹) (v i) = 0 := by
    intro k
    have hy : toMK k⁻¹ * x₀ * toMK k ∈ OmegaSet n := hconj x₀ hx₀ k
    have hyd : IsUnit (toMK k⁻¹ * x₀ * toMK k).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (tb_isUnit_of_omega hy)
    have hinv : (toMK k⁻¹ * x₀ * toMK k)⁻¹⁻¹ = toMK k⁻¹ * x₀ * toMK k :=
      Matrix.nonsing_inv_nonsing_inv _ hyd
    have hz : (toMK k⁻¹ * x₀ * toMK k)⁻¹ ∈ OmegaP n := by
      show (toMK k⁻¹ * x₀ * toMK k)⁻¹⁻¹ ∈ OmegaSet n
      rw [hinv]; exact hy
    have e : ∀ i, hWord (adW ε k (D i)) (PhiP μ) (toMK k⁻¹ * x₀ * toMK k)⁻¹ =
        lWord (adW ε k ((D i).map Neg.neg)) (PhiM μ) (toMK k⁻¹ * x₀ * toMK k) := fun i => by
      rw [tb_hWord_phiP μ _ _ hz, ← tt_adW_neg, hinv]
    have h := hyp k _ hz
    simp only [e] at h
    calc ∑ i, lWord (adW ε k ((D i).map Neg.neg)) (PhiM μ) (toMK k⁻¹ * x₀ * toMK k) •
          (T.op k * projW T * T.op k⁻¹) (v i)
        = (∑ i, ⟪T.op k T.w, v i⟫_ℂ * lWord (adW ε k ((D i).map Neg.neg)) (PhiM μ)
            (toMK k⁻¹ * x₀ * toMK k)) • T.op k T.w := by
          rw [Finset.sum_smul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hAv, smul_smul, mul_comm]
      _ = 0 := by rw [h, zero_smul]
  simp only [hzero, integral_zero, smul_zero]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

theorem scalar_genSub {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M)
    (A : Module.End ℂ M) (hA : ∀ a b, Commute (E a b) A) (c : ℂ) (V : Submodule ℂ M)
    (hV : ∀ y ∈ V, A y = c • y) : ∀ y ∈ genSub E V, A y = c • y := by
  intro y hy
  have hle : genSub E V ≤ LinearMap.ker (A - c • (1 : Module.End ℂ M)) := by
    refine sInf_le ⟨fun v hv => ?_, fun a b v hv => ?_⟩
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hV v hv,
        sub_self]
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hv ⊢
      rw [← Module.End.mul_apply, ← (hA a b).eq, Module.End.mul_apply, sub_eq_zero.1 hv, map_smul,
        sub_self]
  have hy' := hle hy
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    sub_eq_zero] at hy'
  exact hy'

theorem standardKType_of_centralChar (n : ℕ) (hCC : CentralCharStatement n) : LowestKTypeEulerTensorStandard n := by
  intro ε lam h H _ _ _ σ D E V hσ hD hV hcas hVK hint hanti hgap hp hq f hf

  have hcV : ∀ ω : ℂ, ∀ y ∈ V, Capelli.capelliC E ω y = (∏ t, (ω + ((thV lam t : ℝ) : ℂ))) • y :=
    fun ω y hy => hcV_of_centralChar n hCC ε lam h H σ D E V hσ hD hV hcas hVK hint hanti hgap hp hq ω y hy
  exact prodShift_eeV_of_capelli' E hD.glRep (thV lam) (genSub E V)
    (fun ω => scalar_genSub E _ (fun a b => Capelli.capelliC_central E hD.glRep ω a b) _ V (hcV ω)) f hf

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end

section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TwistedDualLemmas

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK

variable {n : ℕ}

def phiR : Matrix (Fin n) (Fin n) ℂ →+* Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.reindexRingEquiv (R := ℂ) (e := (Fin.revPerm : Fin n ≃ Fin n))).toRingHom.comp
    (starRingEnd ℂ).mapMatrix

theorem phiR_apply (g : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    phiR g i j = star (g (Fin.rev i) (Fin.rev j)) := by
  simp [phiR, Matrix.reindexRingEquiv, Fin.revPerm_symm]

theorem phiR_phiR (g : Matrix (Fin n) (Fin n) ℂ) : phiR (phiR g) = g := by
  ext i j; simp [phiR_apply]

theorem phiR_conjT (g : Matrix (Fin n) (Fin n) ℂ) : phiR gᴴ = (phiR g)ᴴ := by
  ext i j; simp [phiR_apply, conjTranspose_apply]

theorem phiR_J (ε : Fin n → Bool) : phiR (Jm (ε ∘ Fin.rev)) = Jm ε := by
  ext i j
  by_cases h : i = j
  · subst h; simp [phiR_apply, Jm]; split_ifs <;> simp
  · simp [phiR_apply, Jm, h]

theorem phiR_smul_real (t : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) :
    phiR ((t : ℂ) • X) = (t : ℂ) • phiR X := by
  ext i j; simp [phiR_apply]

theorem phiR_cont : Continuous (phiR : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) := by
  have : (phiR : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) =
      fun g => (g.submatrix Fin.rev Fin.rev).map star := by
    funext g; ext i j; simp [phiR_apply]
  rw [this]
  exact (continuous_id.matrix_submatrix _ _).matrix_map continuous_star

theorem phiR_exp (A : Matrix (Fin n) (Fin n) ℂ) : phiR (NormedSpace.exp A) = NormedSpace.exp (phiR A) := by
  simp only [NormedSpace.exp_eq_tsum_rat]
  rw [Function.LeftInverse.map_tsum (g := (phiR : Matrix (Fin n) (Fin n) ℂ →+* Matrix (Fin n) (Fin n) ℂ))
    _ phiR_cont phiR_cont phiR_phiR]
  simp only [map_rat_smul, map_pow]

theorem phiR_UJ {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset (ε ∘ Fin.rev)) :
    phiR g ∈ UJset ε := by
  have hg' : gᴴ * Jm (ε ∘ Fin.rev) * g = Jm (ε ∘ Fin.rev) := hg
  show (phiR g)ᴴ * Jm ε * phiR g = Jm ε
  rw [← phiR_conjT, ← phiR_J, ← map_mul, ← map_mul, hg']

theorem phiR_K {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset (ε ∘ Fin.rev)) :
    phiR k ∈ Kset ε := by
  obtain ⟨hu, hc⟩ := hk
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hu ⊢
    rw [← phiR_conjT, ← map_mul, hu, map_one]
  · rw [← phiR_J, ← map_mul, hc, map_mul]

theorem phiR_G {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG (ε ∘ Fin.rev) X) :
    inG ε (phiR X) := by
  have h : Xᴴ * Jm (ε ∘ Fin.rev) + Jm (ε ∘ Fin.rev) * X = 0 := hX
  show (phiR X)ᴴ * Jm ε + Jm ε * phiR X = 0
  rw [← phiR_conjT, ← phiR_J, ← map_mul, ← map_mul, ← map_add (f := _), h, map_zero]

theorem actM_tw {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
    (E : Fin n → Fin n → Module.End ℂ M) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG (ε ∘ Fin.rev) X) :
    actM E (phiR X) = actM (twE ε E) X := by
  have h : Xᴴ * Jm (ε ∘ Fin.rev) + Jm (ε ∘ Fin.rev) * X = 0 := hX
  have key : ∀ a b, star (X b a) = -(sg ε (Fin.rev a) * sg ε (Fin.rev b)) * X a b := by
    intro a b
    have e := congrFun (congrFun h a) b
    simp only [Jm, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.conjTranspose_apply, Matrix.zero_apply] at e
    change star (X b a) * sg ε (Fin.rev b) + sg ε (Fin.rev a) * X a b = 0 at e
    linear_combination (sg ε (Fin.rev b)) * e - star (X b a) * sg_sq ε (Fin.rev b)
  show ∑ a, ∑ b, (phiR X) a b • E a b = ∑ a, ∑ b, X a b • twE ε E a b
  calc ∑ a, ∑ b, (phiR X) a b • E a b
      = ∑ a, ∑ b, (phiR X) (Fin.rev a) (Fin.rev b) • E (Fin.rev a) (Fin.rev b) := by
        rw [← sum_rev (fun a => ∑ b, (phiR X) a b • E a b)]
        refine Finset.sum_congr rfl fun a _ => ?_
        exact (sum_rev (fun b => (phiR X) (Fin.rev a) b • E (Fin.rev a) b)).symm
    _ = ∑ b, ∑ a, (phiR X) (Fin.rev a) (Fin.rev b) • E (Fin.rev a) (Fin.rev b) := Finset.sum_comm
    _ = ∑ a, ∑ b, X a b • twE ε E a b := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [phiR_apply, Fin.rev_rev, Fin.rev_rev, key]
        simp only [twE, smul_smul]
        congr 1; ring

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem urep_tw {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) : IsURepOn (UJset (ε ∘ Fin.rev)) (fun g => σ (phiR g)) := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hσ
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg v => h3 _ (phiR_UJ hg) v, fun v => ?_⟩
  · simp only [map_one, h1]
  · simp only [map_mul]; exact h2 _ (phiR_UJ ha) _ (phiR_UJ hb)
  · exact (h4 v).comp phiR_cont.continuousOn (fun g hg => phiR_UJ hg)

theorem derived_tw {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hD : IsDerivedOn ε σ D E) :
    IsDerivedOn (ε ∘ Fin.rev) (fun g => σ (phiR g)) D (twE ε E) := by
  refine ⟨twE_gl hD.glRep, ?_, ?_⟩
  · intro k hk v hv
    exact hD.kStable (phiR k) (phiR_K hk) v hv
  · intro X hX v
    have := hD.deriv (phiR X) (phiR_G hX) v
    rw [actM_tw E hX] at this
    have hf : (fun t : ℝ => σ (phiR (NormedSpace.exp ((t : ℂ) • X))) (v : H)) =
        fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • phiR X)) (v : H) := by
      funext t; rw [phiR_exp, phiR_smul_real]
    show HasDerivAt (fun t : ℝ => σ (phiR (NormedSpace.exp ((t : ℂ) • X))) (v : H)) _ 0
    rw [hf]; exact this

end Rep

theorem dualLowestKType_of_standard (hK : EigenspaceWeightConeStandard n) : EigenspaceWeightConeDual n := by
  intro ε lam h H _ _ _ σ D E V s hσ hD hV hc hVK hint hanti hgap hp hq
  have hV' : IsKIrrHW (ε ∘ Fin.rev) (twE ε E) (lowK (ε ∘ Fin.rev) (fun a => -lam (Fin.rev a))) V := by
    rw [lowK_tw]; exact kirr_tw hV
  have hc' : ∀ v ∈ V, casimir (twE ε E) v = (casVal (fun a => -lam (Fin.rev a)) : ℂ) • v := by
    intro v hv; rw [casimir_twE, casVal_tw]; exact hc v hv
  have hint' : ∀ a, ∃ m : ℤ, (fun a => -lam (Fin.rev a)) a - ((n : ℝ) - 1) / 2 = (m : ℝ) := by
    intro a
    obtain ⟨m, hm⟩ := hint (Fin.rev a)
    refine ⟨-m - ((n : ℤ) - 1), ?_⟩
    push_cast
    linarith
  have hgap' := gapLap_tw hgap
  obtain ⟨K1, K2⟩ := hK (ε ∘ Fin.rev) (fun a => -lam (Fin.rev a)) h H (fun g => σ (phiR g)) D (twE ε E) V
    (Fin.rev s) (urep_tw hσ) (derived_tw hD) hV' hc' (fun k hk v hv => hVK _ (phiR_K hk) v hv) hint'
    hgap'.1 hgap' (by rwa [pOf_tw]) (by rwa [qOf_tw])
  have hθ : thV (fun a => -lam (Fin.rev a)) (Fin.rev s) = thVd lam s := by simp [thV, thVd]
  have hG : genSub (twE ε E) V = genSub E V := genSub_tw ε E V
  have hW : lowK (ε ∘ Fin.rev) ((fun a => -lam (Fin.rev a)) + Pi.single (Fin.rev s) 1) =
      fun a => -lowK ε (lam - Pi.single s 1) (Fin.rev a) := by
    rw [← lowK_tw]
    congr 1
    funext a
    have e : (a = Fin.rev s ↔ Fin.rev a = s) :=
      ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [← h, Fin.rev_rev]⟩
    simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply, e]
    ring
  refine ⟨fun μ f hf hf0 hμ => ?_, fun f₁ f₂ h1 h2 hw1 hw2 => ?_⟩
  · have hf' := xs_tw (ε := ε) hf
    rw [← hθ, ← hG] at hf'
    have := K1 (fun a => -μ (Fin.rev a)) (twT ε f) hf' (fun h0 => hf0 (twT_eq_zero h0)) (khwT_tw hμ)
    rw [hW] at this
    apply cone_rev
    convert this using 1
    funext a
    simp only [Pi.sub_apply]
    ring
  · have h1' := xs_tw (ε := ε) h1
    rw [← hθ, ← hG] at h1'
    have h2' := xs_tw (ε := ε) h2
    rw [← hθ, ← hG] at h2'
    have k1 := khwT_tw hw1
    rw [← hW] at k1
    have k2 := khwT_tw hw2
    rw [← hW] at k2
    obtain ⟨c₁, c₂, hne, heq⟩ := K2 _ _ h1' h2' k1 k2
    refine ⟨c₁, c₂, hne, twT_eq_zero (ε := ε) ?_⟩
    rw [map_add (f := _), map_smul, map_smul]
    exact heq

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TwistedDualLemmas
end
end
