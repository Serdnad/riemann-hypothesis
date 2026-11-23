module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ContinuousTrESymm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolTSt
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Bundle003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle009
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolUTr
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.VolV

open Formalism.L2.SG.Pf.NcVal Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def aL (g : Fv F v) (θ : Fv F v ⊗[F] E) : (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fv F v ⊗[F] E) :=
  LinearMap.id + (g - 1) • (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)).smulRight θ

theorem aL_apply (g : Fv F v) (θ z : Fv F v ⊗[F] E) :
    aL v g θ z = z + ((g - 1) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z) • θ := by
  simp [aL, LinearMap.smulRight_apply, smul_smul]

theorem trace_aL (g : Fv F v) (θ z : Fv F v ⊗[F] E) (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (aL v g θ z) = g * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z := by
  rw [aL_apply, map_add (f := _), map_smul, hθ, smul_eq_mul]
  ring

theorem det_aL (hfin : Module.finrank F E = 2) (g : Fv F v) (θ Δ : Fv F v ⊗[F] E)
    (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) (hΔ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) Δ = 0)
    (hΔ0 : Δ ≠ 0) : LinearMap.det (aL v g θ) = g := by
  classical
  have hrank : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2 := by
    rw [Module.finrank_baseChange, hfin]
  have hli : LinearIndependent (Fv F v) ![θ, Δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)) hst
    simp only [map_add (f := _), map_smul, hθ, hΔ, smul_eq_mul, mul_one, mul_zero, add_zero, map_zero] at h1
    subst h1
    rw [zero_smul, zero_add, smul_eq_zero] at hst
    exact ⟨rfl, hst.resolve_right hΔ0⟩
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by rw [hrank]; rfl)
  have hb0 : b 0 = θ := by simp [b]
  have hb1 : b 1 = Δ := by simp [b]
  have hf0 : aL v g θ (b 0) = g • b 0 := by
    rw [hb0, aL_apply, hθ, mul_one, sub_smul, one_smul]
    abel
  have hf1 : aL v g θ (b 1) = b 1 := by
    rw [hb1, aL_apply, hΔ, mul_zero, zero_smul, add_zero]
  rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, hf0, hf1, map_smul, b.repr_self, Finsupp.smul_apply,
    Finsupp.single_apply]
  simp

private theorem int_of_alg_lemma (z : Fv F v ⊗[F] E) (hz : z ∈ OEv (E := E) v) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z ∈ v.adicCompletionIntegers F := by
  change z ∈ Submodule.span (v.adicCompletionIntegers F) _ at hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, -, rfl⟩ := hy
    rw [PI.UnitaryGroupMassFormula.LocJacTyp.Sd.trace_inclR]
    have hint : IsIntegral ℤ (Algebra.trace F E (a : E)) :=
      Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe a)
    have := HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := F) (v := v) (⟨_, hint⟩ : 𝓞 F)
    convert this using 1
    exact (IsScalarTower.algebraMap_apply (𝓞 F) F (Fv F v) (⟨_, hint⟩ : 𝓞 F)).symm
  | zero => rw [map_zero]; exact zero_mem _
  | add y w _ _ hy hw => rw [map_add (f := _)]; exact add_mem hy hw
  | smul c y _ hy =>
    rw [show c • y = (c : Fv F v) • y from rfl, map_smul, smul_eq_mul]
    exact mul_mem c.2 hy

private theorem int_of_alg_lemma_2 (a : 𝓞 E) (z : Fv F v ⊗[F] E) (hz : z ∈ OEv (E := E) v) :
    inclR (Fv F v) (a : E) * z ∈ OEv (E := E) v := by
  change z ∈ Submodule.span (v.adicCompletionIntegers F) _ at hz
  change _ ∈ Submodule.span (v.adicCompletionIntegers F) _
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, -, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨a * b, Set.mem_univ _, ?_⟩
    show inclR (Fv F v) ((a * b : 𝓞 E) : E) = inclR (Fv F v) (a : E) * inclR (Fv F v) (b : E)
    rw [show ((a * b : 𝓞 E) : E) = (a : E) * (b : E) from rfl, map_mul]
  | zero => rw [mul_zero]; exact zero_mem _
  | add y w _ _ hy hw => rw [mul_add]; exact add_mem hy hw
  | smul c y _ hy =>
    rw [show c • y = (c : Fv F v) • y from rfl, mul_smul_comm]
    exact Submodule.smul_mem _ c hy

private theorem int_of_alg_lemma_3 (x z : Fv F v ⊗[F] E) (hx : x ∈ OEv (E := E) v) (hz : z ∈ OEv (E := E) v) :
    x * z ∈ OEv (E := E) v := by
  change x ∈ Submodule.span (v.adicCompletionIntegers F) _ at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, -, rfl⟩ := hy
    exact int_of_alg_lemma_2 v a z hz
  | zero => rw [zero_mul]; exact (Submodule.span _ _).zero_mem
  | add y w _ _ hy hw =>
    rw [add_mul]
    exact (Submodule.span (v.adicCompletionIntegers F) _).add_mem hy hw
  | smul c y _ hy =>
    rw [show c • y = (c : Fv F v) • y from rfl, smul_mul_assoc]
    exact (Submodule.span (v.adicCompletionIntegers F) _).smul_mem c hy

theorem int_of_alg {θ : Fv F v ⊗[F] E} (hθO : θ ∈ OEv (E := E) v)
    (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) {x : Fv F v}
    (hx : algebraMap (Fv F v) (Fv F v ⊗[F] E) x ∈ OEv (E := E) v) : x ∈ v.adicCompletionIntegers F := by
  have h := int_of_alg_lemma v _ (int_of_alg_lemma_3 v _ _ hx hθO)
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul, hθ, smul_eq_mul, mul_one] at h
  exact h

theorem mem_aL_image (σ : E →ₐ[F] E)
    (htr : ∀ w : Fv F v ⊗[F] E, algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w) =
      w + sigR (Fv F v) σ w)
    {g : ℕ} (hg0 : g ≠ 0) {θ : Fv F v ⊗[F] E} (hθO : θ ∈ OEv (E := E) v)
    (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) (y : Fv F v ⊗[F] E) :
    y ∈ aL v (g : Fv F v) θ '' OEv (E := E) v ↔
      y ∈ OEv (E := E) v ∧ (y + sigR (Fv F v) σ y) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v := by
  classical
  have hsc : ∀ c : Fv F v, sc (E := E) v c = algebraMap (Fv F v) (Fv F v ⊗[F] E) c := fun c => by
    rw [Algebra.algebraMap_eq_smul_one, ← Formalism.L2.SG.Pf.NcVal.VolTU.sc_mul_eq_smul, mul_one]
  have hcond : (y + sigR (Fv F v) σ y) * sc (E := E) v (g : Fv F v)⁻¹ =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y * (g : Fv F v)⁻¹) := by
    rw [← htr, hsc, map_mul]
  have hone : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
    have := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.inclR_mem (E := E) v 1
    simp only [OneMemClass.coe_one, map_one] at this
    exact this
  have hsmul : ∀ c ∈ v.adicCompletionIntegers F, ∀ x ∈ OEv (E := E) v, c • x ∈ OEv (E := E) v :=
    fun c hc x hx => by
      rw [← Formalism.L2.SG.Pf.NcVal.VolTU.sc_mul_eq_smul]
      exact Formalism.L2.SG.Pf.NcVal.VolTU.sc_mul_mem v hc hx
  have halg : ∀ c ∈ v.adicCompletionIntegers F, algebraMap (Fv F v) (Fv F v ⊗[F] E) c ∈ OEv (E := E) v :=
    fun c hc => by
      rw [Algebra.algebraMap_eq_smul_one]
      exact hsmul c hc 1 hone
  have hgO : (g : Fv F v) - 1 ∈ v.adicCompletionIntegers F :=
    sub_mem (Formalism.L2.SG.Pf.NcVal.VolTU.natCast_memO v g) (one_mem _)
  have hgne : (g : Fv F v) ≠ 0 := Formalism.L2.SG.Pf.NcVal.VolTU.natCast_ne_zero v hg0
  rw [hcond]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have htz := int_of_alg_lemma v z hz
    refine ⟨?_, ?_⟩
    · rw [aL_apply]
      exact add_mem hz (hsmul _ (mul_mem hgO htz) θ hθO)
    · rw [trace_aL v _ θ z hθ, mul_comm, ← mul_assoc, inv_mul_cancel₀ hgne, one_mul]
      exact halg _ htz
  · rintro ⟨hy, ht⟩
    have htO := int_of_alg v hθO hθ ht
    set t := Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y * (g : Fv F v)⁻¹ with ht_def
    refine ⟨y - (((g : Fv F v) - 1) * t) • θ, sub_mem hy (hsmul _ (mul_mem hgO htO) θ hθO), ?_⟩
    have htr' : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y = (g : Fv F v) * t := by
      rw [ht_def, mul_comm, mul_assoc, inv_mul_cancel₀ hgne, mul_one]
    rw [aL_apply]
    have : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (y - (((g : Fv F v) - 1) * t) • θ) = t := by
      rw [map_sub, map_smul, hθ, smul_eq_mul, mul_one, htr']
      ring
    rw [this, sub_add_cancel]

end Formalism.L2.SG.Pf.NcVal.VolV
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace VolUF

variable {D : D7} (X : HidaSetting D)

theorem star_eq (a : D.host.E) : star a = D.host.conj a := by
  apply D.host.φ₀.injective
  rw [show star a = IsCMField.complexConj D.host.E a from rfl, IsCMField.complexEmbedding_complexConj]
  exact (D.host.conjE_apply D.host.φ₀ a).symm

theorem sig_eq (b : X.B.I.E) : X.ιE (X.B.I.cm.sig b) = star (X.ιE b) := by
  have h1 : X.B.I.cm.sig b = star b := rfl
  rw [h1, X.ιE_conj, star_eq]

theorem hE_crd (x y : (VS D).V) :
    X.ιE (hE X.B.I.cm.sig X.B.I.J (crdOf X.B.I X.ιE X.bas x) (crdOf X.B.I X.ιE X.bas y)) = (VS D).hT x y := by
  unfold hE Formalism.UG.hform crdOf

  simp only [map_sum, map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe]
  simp only [sig_eq, X.J_eq, RingEquiv.apply_symm_apply]
  conv_rhs => rw [← X.bas.sum_repr x, ← X.bas.sum_repr y]

  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply,
  RingHom.id_apply, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gram_eq (w : D.what₂.Word) (i j : Fin (D.R.rS + 1)) :
    X.ιE (gramE X.B.I.cm.sig X.B.I.J (F0 (frameOf X w)) i j) =
      if i = Fin.last D.R.rS ∧ j = Fin.last D.R.rS then -(((D.mem w).A.T : ℕ) : D.host.E) else 0 := by
  unfold gramE
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last =>
      simp only [F0, Fin.snoc_last, frameOf]
      rw [hE_crd, X.zu_norm]
      simp
    | cast b =>
      simp only [F0, Fin.snoc_last, Fin.snoc_castSucc, frameOf]
      rw [hE_crd, ← LinearMap.isSymm_def.1 (VS D).herm (X.eX b) (X.zu w), (X.zu_orth w b).1, map_zero]
      simp [Fin.castSucc_ne_last]
  | cast a =>
    induction j using Fin.lastCases with
    | last =>
      simp only [F0, Fin.snoc_last, Fin.snoc_castSucc, frameOf]
      rw [hE_crd, (X.zu_orth w a).1]
      simp [Fin.castSucc_ne_last]
    | cast b =>
      simp only [F0, Fin.snoc_castSucc, frameOf]
      rw [hE_crd, X.ee]
      simp [Fin.castSucc_ne_last]

theorem gram_eq' (w : D.what₂.Word) (i j : Fin (D.R.rS + 1)) :
    gramE X.B.I.cm.sig X.B.I.J (F0 (frameOf X w)) i j =
      if i = Fin.last D.R.rS ∧ j = Fin.last D.R.rS then -(((D.mem w).A.T : ℕ) : X.B.I.E) else 0 := by
  apply X.ιE.injective
  rw [gram_eq]
  split_ifs <;> simp

theorem tf_diff (u u' : D.what₂.Word) (v : PlX X) (g : ℕ) (i j : Fin (D.R.rS + 1)) :
    (TFv X u' v i j - TFv X u v i j) * sc (E := X.B.I.E) v (g : Fv X.B.I.F v)⁻¹ =
      sc (E := X.B.I.E) v (if i = Fin.last D.R.rS ∧ j = Fin.last D.R.rS then
        ((((D.mem u).A.T : ℕ) : Fv X.B.I.F v) - (((D.mem u').A.T : ℕ) : Fv X.B.I.F v)) * (g : Fv X.B.I.F v)⁻¹
        else 0) := by
  unfold TFv
  simp only [Matrix.map_apply, gram_eq']
  split_ifs with h
  · rw [VolTU.sc_mul]
    congr 1
    rw [VolUTr.TrW.sc_eq, map_sub, map_natCast, map_natCast, map_neg, map_neg, map_natCast, map_natCast]
    ring
  · rw [sub_self, zero_mul, VolUTr.TrW.sc_eq, map_zero]

theorem sigR_sc (v : PlX X) (x : Fv X.B.I.F v) :
    sigR (Fv X.B.I.F v) X.B.I.cm.sig (sc (E := X.B.I.E) v x) = sc (E := X.B.I.E) v x := by
  simp [sigR, sc, Algebra.TensorProduct.map_tmul]

end VolUF

theorem volTTFCong_of {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (v : PlX X) (hv : TypAt X v) :
    VolTTFCong X u u' v := by
  obtain ⟨m, hm⟩ := tCongX X u u' ⟨v, hv⟩
  have hg0 : (gAt X v : Fv X.B.I.F v) ≠ 0 := VolTU.natCast_ne_zero v (gAt_prime X v).ne_zero
  have hk : ((((D.mem u).A.T : ℕ) : Fv X.B.I.F v) - (((D.mem u').A.T : ℕ) : Fv X.B.I.F v)) *
      (gAt X v : Fv X.B.I.F v)⁻¹ = (m : Fv X.B.I.F v) := by
    have hm' : ((((D.mem u).A.T : ℕ) : ℤ) : Fv X.B.I.F v) - ((((D.mem u').A.T : ℕ) : ℤ) : Fv X.B.I.F v) =
        ((gAt X v : ℤ) : Fv X.B.I.F v) * (m : Fv X.B.I.F v) := by
      rw [← Int.cast_sub, ← Int.cast_mul]
      exact congrArg _ hm
    push_cast at hm'
    rw [hm', mul_comm, ← mul_assoc, inv_mul_cancel₀ hg0, one_mul]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simp only
    rw [VolUF.tf_diff, VolUF.tf_diff, VolUF.sigR_sc]
    congr 1
    simp only [and_comm]
  · simp only
    rw [VolUF.tf_diff]
    split_ifs
    · rw [hk, VolUTr.TrW.sc_eq]
      exact VolUTr.TrW.alg_mem v (_root_.intCast_mem _ m)
    · rw [VolUTr.TrW.sc_eq, map_zero]
      exact Submodule.zero_mem _

end Formalism.L2.SG.Pf.NcVal
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.VolUH

open Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal TensorProduct

theorem haar_pre {G : Type*} [AddCommGroup G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (μ : Measure G) [μ.IsAddHaarMeasure] (φ : G ≃ₜ+ G) (K : Set G) (hK : μ K = 1) (S : Set G) :
    μ (φ ⁻¹' S) = μ (φ ⁻¹' K) * μ S := by
  have he : MeasurableEmbedding φ := φ.toHomeomorph.measurableEmbedding
  haveI : (μ.map φ).IsAddHaarMeasure :=
    μ.isAddHaarMeasure_map (φ : G →+ G) φ.continuous φ.surjective
      φ.toHomeomorph.isClosedEmbedding.tendsto_cocompact
  have h := Measure.isAddLeftInvariant_eq_smul (μ.map φ) μ
  have key : ∀ T : Set G, μ (φ ⁻¹' T) = (μ.map φ).addHaarScalarFactor μ * μ T := by
    intro T
    rw [← he.map_apply]
    conv_lhs => rw [h]
    simp
  rw [key S, key K, hK, mul_one]

section R

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem top_facts (ι : Type) [Fintype ι] :
    IsTopologicalAddGroup (ι → Fv F v ⊗[F] E) ∧ LocallyCompactSpace (ι → Fv F v ⊗[F] E) ∧
      SecondCountableTopology (ι → Fv F v ⊗[F] E) ∧ BorelSpace (ι → Fv F v ⊗[F] E) ∧
      IsModuleTopology (Fv F v) (ι → Fv F v ⊗[F] E) := by
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

def scMul {ι : Type} [Fintype ι] (z : ι → Fv F v) (hz : ∀ i, z i ≠ 0) :
    (ι → Fv F v ⊗[F] E) ≃ₜ+ (ι → Fv F v ⊗[F] E) where
  toFun w i := sc (E := E) v (z i) * w i
  invFun w i := sc (E := E) v (z i)⁻¹ * w i
  left_inv w := by
    funext i
    simp only
    rw [← mul_assoc, ← VolTU.sc_mul, inv_mul_cancel₀ (hz i), VolTU.sc_one, one_mul]
  right_inv w := by
    funext i
    simp only
    rw [← mul_assoc, ← VolTU.sc_mul, mul_inv_cancel₀ (hz i), VolTU.sc_one, one_mul]
  map_add' w w' := by
    funext i
    simp only [Pi.add_apply, mul_add]
  continuous_toFun := by
    obtain ⟨-, -, -, -, h⟩ := top_facts (E := E) v ι
    haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
    haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
    haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
    exact IsModuleTopology.continuous_of_linearMap
      (PI.UnitaryGroupMassFormula.LocJacTyp.BM.mulL v fun i => sc (E := E) v (z i))
  continuous_invFun := by
    obtain ⟨-, -, -, -, h⟩ := top_facts (E := E) v ι
    haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
    haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
    haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
    exact IsModuleTopology.continuous_of_linearMap
      (PI.UnitaryGroupMassFormula.LocJacTyp.BM.mulL v fun i => sc (E := E) v (z i)⁻¹)

theorem sc_pre (ι : Type) [Fintype ι] (μ : Measure (ι → Fv F v ⊗[F] E)) [μ.IsAddHaarMeasure]
    (hK : μ (VolTO (E := E) v ι) = 1) (z : ι → Fv F v) (hz : ∀ i, z i ≠ 0) (S : Set (ι → Fv F v ⊗[F] E)) :
    μ {w | (fun i => sc (E := E) v (z i) * w i) ∈ S} =
      μ {w | ∀ i, sc (E := E) v (z i) * w i ∈ OEv (E := E) v} * μ S := by
  exact haar_pre μ (scMul (E := E) v z hz) _ hK S

theorem sub_pre (ι : Type) [Fintype ι] (μ : Measure (ι → Fv F v ⊗[F] E)) [μ.IsAddHaarMeasure]
    (b : ι → Fv F v ⊗[F] E) (S : Set (ι → Fv F v ⊗[F] E)) :
    μ {w | (fun i => w i - b i) ∈ S} = μ S := by
  have h : {w | (fun i => w i - b i) ∈ S} = (fun w => w + -b) ⁻¹' S := by
    ext w
    simp [sub_eq_add_neg]
    rfl
  rw [h, measure_preimage_add_right]

end R

end Formalism.L2.SG.Pf.NcVal.VolUH
end
end
