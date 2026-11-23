module

public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittEmbeddingsCompatible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Formalism.LocalToGlobal.KernelLattices.Bundle003
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle001
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FieldIsoLatticesFormTaylorCorrespond
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.Bundle001
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle142
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntBasis
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.TransportFirstLevel
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedShiftFixedRatioConstDomain
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Bundle001
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle010
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle051
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open IsLocalRing

namespace GlobalTheory

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem nonempty_cEmb_of_pos_nV : ∀ (p : ℕ) [Fact p.Prime] (G : Formalism.MainNotions.G.GAtP p), 0 < G.P.nV →
    Nonempty (Formalism.L2.G.Pend.CEmb G) := by
  intro p _ G hV
  let v : Fin G.P.nV := ⟨0, hV⟩
  have S := G.P.setting v
  haveI := S.frac_alt
  haveI := S.frac_O
  haveI : IsAdicComplete (maximalIdeal G.O) G.O := S.complete_O

  haveI hW0 : CharZero (G.P.W v) := by
    obtain ⟨l, hl⟩ := CharP.exists (G.P.W v)
    rcases CharP.char_is_prime_or_zero (G.P.W v) l with hlp | hl0
    · exfalso
      by_cases hlpe : l = p
      · subst hlpe
        exact S.p_unif.ne_zero (CharP.cast_eq_zero _ l)
      · have hcop : Nat.Coprime p l := (Nat.coprime_primes (Fact.out) hlp).2 (Ne.symm hlpe)
        have h := Nat.gcd_eq_gcd_ab p l
        rw [hcop] at h
        have h' := congrArg (fun z : ℤ => (z : G.P.W v)) h
        simp only [Nat.cast_one, Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast,
          CharP.cast_eq_zero, zero_mul, add_zero] at h'
        exact S.p_unif.not_isUnit (IsUnit.of_mul_eq_one _ h'.symm)
    · subst hl0
      exact CharP.charP_to_charZero _
  haveI : CharZero (G.P.Qq v) :=
    (RingHom.charZero_iff (IsFractionRing.injective (G.P.W v) (G.P.Qq v))).1 hW0
  haveI : CharZero G.Kf := (RingHom.charZero_iff (G.P.ι v).injective).1 inferInstance

  letI : Algebra (G.P.W v) G.O := (G.P.j v).toAlgebra
  haveI : Module.Finite (G.P.W v) G.O := S.finite
  have hcomap : (maximalIdeal G.O).comap (algebraMap (G.P.W v) G.O) = Ideal.span {(p : G.P.W v)} := by
    have hmax : ((maximalIdeal G.O).comap (algebraMap (G.P.W v) G.O)).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := G.P.W v) _
    rw [IsLocalRing.eq_maximalIdeal hmax, S.p_unif.maximalIdeal_eq]
  have hpO : (p : G.O) ∈ maximalIdeal G.O := by
    have : (p : G.P.W v) ∈ (maximalIdeal G.O).comap (algebraMap (G.P.W v) G.O) :=
      hcomap ▸ Ideal.subset_span rfl
    simpa using this

  haveI : Finite (ResidueField (G.P.W v)) := by
    have h := S.res_card
    rw [← S.p_unif.maximalIdeal_eq] at h
    exact Nat.finite_of_card_ne_zero (h ▸ pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  haveI : Finite (ResidueField G.O) := by
    haveI : Module.Finite (G.P.W v) (ResidueField G.O) := inferInstance
    haveI : Algebra.IsIntegral (G.P.W v) (ResidueField G.O) := inferInstance
    exact Module.finite_of_finite (ResidueField (G.P.W v))

  obtain ⟨p', hp', K₀, e, e₀, hfd, he⟩ := exists_ringEquiv_integralClosure_padicInt G.O G.Kf
  have hpp : p' = p := by
    have h1 : e₀ (p : G.O) ∈ maximalIdeal (integralClosure ℤ_[p'] K₀) := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (mem_maximalIdeal _).1 hpO (by simpa using hu.map e₀.symm)
    rw [mem_maximalIdeal_integralClosure_iff, map_natCast] at h1
    have h2 : (((p : integralClosure ℤ_[p'] K₀) : K₀) : PadicAlgCl p') =
        algebraMap ℚ_[p'] (PadicAlgCl p') p := by simp
    rw [h2, PadicAlgCl.norm_extends, Padic.norm_natCast_lt_one_iff] at h1
    exact (Nat.prime_dvd_prime_iff_eq hp'.out Fact.out).1 h1
  subst hpp

  refine ⟨⟨(algebraMap (PadicAlgCl p') ℂ_[p']).comp (K₀.val.toRingHom.comp e.toRingHom), fun x => ?_⟩⟩
  have hx : ((e (algebraMap G.O G.Kf x) : K₀) : PadicAlgCl p') = (((e₀ x : integralClosure ℤ_[p'] K₀) : K₀) : PadicAlgCl p') := by
    rw [he x]
  simp only [RingHom.comp_apply]
  show ‖algebraMap (PadicAlgCl p') ℂ_[p'] ((e (algebraMap G.O G.Kf x) : K₀) : PadicAlgCl p')‖ ≤ 1
  rw [hx, ← PadicComplex.coe_eq, PadicComplex.norm_extends]
  exact (mem_integralClosure_padicInt_iff K₀ _).1 (e₀ x).2
end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DivDual

section Abstract

variable {R : Type} [CommRing R] {n : ℕ}

def Dv (Λ : (Fin n → R) → Prop) (O : R → Prop) (e : R) (u : Fin n → R) (A : Matrix (Fin n) (Fin n) R) : Prop :=
  ∃ B : Matrix (Fin n) (Fin n) R,
    (∀ z : Fin n → R, (∀ i, O (z i)) → Λ (e • B.mulVec z)) ∧
    (∀ y, Λ y → ∃ z : Fin n → R, (∀ i, O (z i)) ∧ e • y = e • B.mulVec z) ∧
    (∀ y, Λ y → ∃ z : Fin n → R, (∀ i, O (z i)) ∧ e • A.mulVec y = e • B.mulVec (fun i => u i * z i)) ∧
    (∀ z : Fin n → R, (∀ i, O (z i)) → ∃ y, Λ y ∧ e • A.mulVec y = e • B.mulVec (fun i => u i * z i))

theorem Dv.inv {Λ : (Fin n → R) → Prop} {O : R → Prop} {e : R} {u u' : Fin n → R}
    {A A' : Matrix (Fin n) (Fin n) R} (he : e * e = e) (hA : A' * A = 1)
    (hu : ∀ i, u i * u' i.rev = 1) (h : Dv Λ O e u A) : Dv Λ O e u' A' := by
  obtain ⟨B, h1, h2, h3, h4⟩ := h
  have hcancel : ∀ y, A'.mulVec (e • A.mulVec y) = e • y := fun y => by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
  let B' : Matrix (Fin n) (Fin n) R := Matrix.of fun a j => (A' * B) a j.rev * u j.rev
  have hB' : ∀ z, B'.mulVec z = A'.mulVec (B.mulVec fun i => u i * z i.rev) := fun z => by
    rw [Matrix.mulVec_mulVec]
    funext a
    simp only [B', Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [← Equiv.sum_comp Fin.revPerm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Fin.revPerm_apply, Fin.rev_rev]
    ring
  have hB'' : ∀ z : Fin n → R, B'.mulVec (fun i => u' i * z i) = A'.mulVec (B.mulVec fun i => z i.rev) := fun z => by
    rw [hB']
    congr 2
    funext i
    rw [← mul_assoc, hu, one_mul]
  refine ⟨B', fun z hz => ?_, fun y hy => ?_, fun y hy => ?_, fun z hz => ?_⟩
  · obtain ⟨y, hy, hyz⟩ := h4 (fun i => z i.rev) (fun i => hz _)
    rw [hB', ← Matrix.mulVec_smul, ← hyz, hcancel]
    obtain ⟨w, hw, hyw⟩ := h2 y hy
    rw [hyw]
    exact h1 w hw
  · obtain ⟨z, hz, hyz⟩ := h3 y hy
    refine ⟨fun i => z i.rev, fun i => hz _, ?_⟩
    rw [hB', ← Matrix.mulVec_smul]
    simp only [Fin.rev_rev]
    rw [← hyz, hcancel]
  · obtain ⟨z, hz, hyz⟩ := h2 y hy
    refine ⟨fun i => z i.rev, fun i => hz _, ?_⟩
    rw [hB'', ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, hyz]
    simp only [Fin.rev_rev]
  · refine ⟨e • B.mulVec (fun i => z i.rev), h1 _ (fun i => hz _), ?_⟩
    rw [hB'', Matrix.mulVec_smul, smul_smul, he]

theorem Dv.mul {Λ : (Fin n → R) → Prop} {O : R → Prop} {e : R} {u : Fin n → R}
    {A a a' b b' : Matrix (Fin n) (Fin n) R} (haa : a * a' = 1) (hbb : b * b' = 1)
    (ha : ∀ y, Λ y ↔ Λ (a.mulVec y)) (hb : ∀ y, Λ y ↔ Λ (b.mulVec y))
    (h : Dv Λ O e u A) : Dv Λ O e u (a * A * b) := by
  obtain ⟨B, h1, h2, h3, h4⟩ := h
  have ea : ∀ y, a.mulVec (a'.mulVec y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, haa, Matrix.one_mulVec]
  have eb : ∀ y, b.mulVec (b'.mulVec y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, hbb, Matrix.one_mulVec]
  refine ⟨a * B, fun z hz => ?_, fun y hy => ?_, fun y hy => ?_, fun z hz => ?_⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul]
    exact (ha _).1 (h1 z hz)
  · obtain ⟨z, hz, hyz⟩ := h2 (a'.mulVec y) ((ha _).2 (by rw [ea]; exact hy))
    refine ⟨z, hz, ?_⟩
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, ← hyz, Matrix.mulVec_smul, ea]
  · obtain ⟨z, hz, hyz⟩ := h3 (b.mulVec y) ((hb _).1 hy)
    refine ⟨z, hz, ?_⟩
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, hyz,
      Matrix.mulVec_smul]
  · obtain ⟨y, hy, hyz⟩ := h4 z hz
    refine ⟨b'.mulVec y, (hb _).2 (by rw [eb]; exact hy), ?_⟩
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, eb, ← Matrix.mulVec_smul, hyz,
      Matrix.mulVec_smul]

end Abstract

theorem getD_dualLab (d : List ℤ) {n : ℕ} (hd : d.length = n) (i : Fin n) :
    (dualLab d).getD i.rev.1 0 = -(d.getD i.1 0) := by
  subst hd
  have h1 : i.rev.1 < (dualLab d).length := by simp only [dualLab, List.length_reverse, List.length_map]; exact i.rev.2
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ i.2]
  simp only [dualLab, List.getElem_reverse, List.getElem_map, List.length_map, Fin.val_rev]
  have := i.2
  congr 2
  omega

theorem divAt_iff {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D) (ϖ : D.host.E) (d : List ℤ) (α : GA D V) :
    DivAt V e ϖ d α ↔ d.length = V.rank ∧ Dv (fun y => y ∈ LamHat V) (fun x => x ∈ intAE D) (finPart D e)
      (fun i => finPart D (incA D (ϖ ^ (d.getD i.1 0)))) (finMat D.sp.cm.sig V.gram α) := Iff.rfl

theorem divAt_inv_and_mul : ∀ {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D) (ϖ : D.host.E) (d : List ℤ) (α : GA D V), e * e = e → ϖ ≠ 0 → DivAt V e ϖ d α → DivAt V e ϖ (dualLab d) α⁻¹ ∧ ∀ a ∈ KsphC V ∅, ∀ b ∈ KsphC V ∅, DivAt V e ϖ d (a * α * b) := by
  intro D V e ϖ d α he hϖ h
  rw [divAt_iff] at h
  obtain ⟨hd, h⟩ := h
  have hm : ∀ g g' : GA D V, finMat D.sp.cm.sig V.gram (g * g') =
      finMat D.sp.cm.sig V.gram g * finMat D.sp.cm.sig V.gram g' := fun g g' =>
    Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul _ _ g g'
  have h1 : finMat D.sp.cm.sig V.gram (1 : GA D V) = 1 := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one _ _
  refine ⟨?_, fun a ha b hb => ?_⟩
  · rw [divAt_iff]
    refine ⟨by simpa [dualLab] using hd, h.inv (by rw [← map_mul, he]) ?_ fun i => ?_⟩
    · rw [← hm, inv_mul_cancel, h1]
    · rw [getD_dualLab d hd, ← map_mul, ← map_mul, zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ hϖ), map_one, map_one]
  · rw [divAt_iff, hm, hm]
    refine ⟨hd, h.mul (a' := finMat D.sp.cm.sig V.gram a⁻¹) (b' := finMat D.sp.cm.sig V.gram b⁻¹) ?_ ?_
      ha.2.1 hb.2.1⟩
    · rw [← hm, mul_inv_cancel, h1]
    · rw [← hm, mul_inv_cancel, h1]

end GlobalTheory.DivDual
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section

namespace GlobalTheory.FlatTaylorBridge

open MvPowerSeries

theorem coeff_taylorMv_flatV (D : D7) (X : Fields) (s : Seam D X) (N N' : ℕ) (G : TaylorLogMetric.VC D N N' → ℂ)
    (hG : AnalyticOnNhd ℂ G Set.univ) (m : DVar X.Tau N N' →₀ ℕ) :
    coeff m (taylorMv fun z => G (s.flatV N N' z)) =
      TaylorLogMetric.taylor D G (m.mapDomain fun v => (s.iT v.1, v.2)) := by
  have hc : ∀ k : ℕ, ContDiff ℂ k G := fun k => hG.contDiff
  let G' : VCx X.Tau N N' → ℂ := fun w => G fun τ => w (s.iT.symm τ)
  let L : VCx X.Tau N N' →L[ℂ] TaylorLogMetric.VC D N N' :=
    ContinuousLinearMap.pi fun τ => ContinuousLinearMap.proj (s.iT.symm τ)
  have hG' : AnalyticOnNhd ℂ G' Set.univ := by
    have : G' = G ∘ L := rfl
    rw [this]
    exact hG.comp (L.analyticOnNhd _) (fun _ _ => trivial)
  have h1 := Formalism.L2.AlgTh.taylor_jet_expansion X.Tau N N' G' hG' m
  have h2 := GlobalTheory.SeamTransport.deriv_transport s.iT G hc m
  rw [GlobalTheory.SeamTransport.taylor_eq] at h2
  have hfl : (fun z => G (s.flatV N N' z)) = fun z => G' (Formalism.L2.AlgTh.flat X.Tau N N' z) := rfl
  have hne : ((m.mapDomain fun v => (s.iT v.1, v.2)).prod fun _ n => (n.factorial : ℂ)) ≠ 0 := by
    rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hpr : ((m.mapDomain fun v => (s.iT v.1, v.2)).prod fun _ n => (n.factorial : ℂ)) =
      ((Formalism.DworkPowerSeriesWeights.mfact m : ℕ) : ℂ) := by
    rw [Finsupp.prod_mapDomain_index_inj]
    · simp [Formalism.DworkPowerSeriesWeights.mfact, Finsupp.prod]
    · intro v w h
      exact Prod.ext (s.iT.injective (Prod.ext_iff.1 h).1) (Prod.ext_iff.1 h).2
  apply mul_left_cancel₀ hne
  rw [← h2, hpr, hfl]
  convert h1 using 3

end GlobalTheory.FlatTaylorBridge

namespace GlobalTheory.FlatTaylorBridge
open MvPowerSeries

theorem subst_rename_lin {σ τ γ : Type} [Finite σ] [Finite τ] {R : Type} [CommRing R] (f : σ → τ)
    (a : τ → MvPowerSeries γ R) (ha : ∀ t, constantCoeff (a t) = 0) (Φ : MvPowerSeries σ R) :
    subst a (rename f Φ) = subst (fun s => a (f s)) Φ := by
  have hs := hasSubst_of_constantCoeff_zero ha
  rw [rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp f) hs Φ]
  congr 1
  funext x
  exact subst_X hs (f x)

theorem bridge : ∀ (D : D7) (X : Fields) (s : Seam D X) (N N' : ℕ) (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), Formalism.L2.KerInert.IotaExt lm ι → ∀ G : TaylorLogMetric.VC D N N' → ℂ, AnalyticOnNhd ℂ G Set.univ → TaylorLogMetric.CoefIn D G TaylorLogMetric.Qbar → ∀ (ν : Type) [Fintype ν] (M : D.what₂.Tau × Fin N' × Fin N → ν → ℂ_[p]), TaylorLogMetric.atLin M (fun j => MvPowerSeries.X j) (TaylorLogMetric.pSer D lm G) = Formalism.L2.Th1.G.linSub (fun (i : DVar X.Tau N N') x => M (s.iT i.1, i.2) x) (MvPowerSeries.map (ι : ℂ →+* ℂ_[p]) (taylorMv fun z => G (s.flatV N N' z))) := by
  intro D X s N N' p _ lm ι hι G hG hC ν _ M
  let eE : DVar X.Tau N N' ≃ D.what₂.Tau × Fin N' × Fin N := s.iT.prodCongr (Equiv.refl _)
  have hP : TaylorLogMetric.pSer D lm G =
      rename (eE : DVar X.Tau N N' → D.what₂.Tau × Fin N' × Fin N)
        (map (ι : ℂ →+* ℂ_[p]) (taylorMv fun z => G (s.flatV N N' z))) := by
    ext α
    obtain ⟨m, rfl⟩ := Finsupp.mapDomain_surjective eE.surjective α
    have h := coeff_embDomain_rename eE.toEmbedding
      (map (ι : ℂ →+* ℂ_[p]) (taylorMv fun z => G (s.flatV N N' z))) m
    rw [Finsupp.embDomain_eq_mapDomain] at h
    refine Eq.trans ?_ h.symm
    rw [coeff_map, coeff_taylorMv_flatV D X s N N' G hG m]
    change TaylorLogMetric.lamC lm (TaylorLogMetric.taylor D G _) = _
    unfold TaylorLogMetric.lamC
    rw [dite_eq_left (hC _)]
    exact (hι ⟨_, hC _⟩).symm
  rw [hP]
  unfold TaylorLogMetric.atLin Formalism.L2.Th1.G.linSub
  rw [subst_rename_lin]
  · congr 1
  · intro t

    rw [map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_mul, constantCoeff_X, mul_zero]

end GlobalTheory.FlatTaylorBridge
end
end

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.HypCoord

def toKur (p : ℕ) [Fact p.Prime] (x : ℂ_[p]) : MaximalUnramifiedExtension p := if h : x ∈ MaximalUnramifiedExtension p then ⟨x, h⟩ else 0

theorem coe_toKur {p : ℕ} [Fact p.Prime] {x : ℂ_[p]} (h : x ∈ MaximalUnramifiedExtension p) : ((toKur p x : MaximalUnramifiedExtension p) : ℂ_[p]) = x := by
  simp [toKur, h]

def rhoK (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (z : Bool × HH D) (y : D.host.E) : MaximalUnramifiedExtension p :=
  toKur p (tauEmb D lam (tauPl D z) y)

def gK (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' r : ℕ}
    (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (z : Bool × HH D) (a : Fin N) (b₀ : Fin N') (i : Fin r) : MaximalUnramifiedExtension p :=
  ∑ b₁ : Fin N', ∑ a₁ : Fin N, rhoK D lam z (D.host.conj (b i b₁ a₁)) * rhoK D lam z (P' (tauPl D z) b₁ b₀) *
    ((P (tauPl D z)).map (rhoK D lam z))⁻¹ a a₁

def hK (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' r : ℕ}
    (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (w : Bool × HH D) (a : Fin N) (b₀ : Fin N') (i : Fin r) : MaximalUnramifiedExtension p :=
  ∑ b₁ : Fin N', ∑ a₁ : Fin N, ((P' (tauPl D w)).map (rhoK D lam w))⁻¹ b₀ b₁ * rhoK D lam w (b i b₁ a₁) *
    rhoK D lam w (P (tauPl D w) a₁ a)

def fOf (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {N N' r : ℕ} (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p)
    (e : (R × Fin (nP D p / 2)) × Fin N × Fin N') (i : Fin r) : MaximalUnramifiedExtension p :=
  ∑ t : ZMod (nP D p), if t.val % 2 = 0 then σ^[t.val] (om e.1.2) * g (OrbitPlaces.orbMap D p e.1.1 t) e.2.1 e.2.2 i else 0

def fOf' (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {N N' r : ℕ} (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p)
    (e : (R × Fin (nP D p / 2)) × Fin N × Fin N') (i : Fin r) : MaximalUnramifiedExtension p :=
  ∑ t : ZMod (nP D p), if t.val % 2 = 0 then 0 else σ^[t.val] (oms e.1.2) * g (OrbitPlaces.orbMap D p e.1.1 t) e.2.1 e.2.2 i

theorem exists_ringHom_rhoK (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p)
    (hσ : UnrOK (MaximalUnramifiedExtension p) p σ) (hcl : IsResidueClassZero D p ∨ IsSg D p) (z : Bool × HH D) :
    ∃ ρ : D.host.E →+* MaximalUnramifiedExtension p, ∀ y, rhoK D lam z y = ρ y ∧ ((ρ y : MaximalUnramifiedExtension p) : ℂ_[p]) = tauEmb D lam (tauPl D z) y := by
  have hmem : ∀ y, tauEmb D lam (tauPl D z) y ∈ MaximalUnramifiedExtension p := fun y => by
    obtain ⟨a, ha, -⟩ := exists_kur_frob_tauEmb_posPl D p lam σ hσ hcl z y
    rw [← ha]; exact a.2
  let ρ0 : D.host.E →+* ℂ_[p] := lam.comp (Formalism.L2.KerInert.IntegralOrthonormalChange.embQ D (tauPl D z))
  have h0 : ∀ y, ρ0 y = tauEmb D lam (tauPl D z) y := fun y => by
    simp only [ρ0, RingHom.comp_apply, tauEmb, Formalism.L2.KerInert.IntegralOrthonormalChange.lamC_embT]
  refine ⟨ρ0.codRestrict (MaximalUnramifiedExtension p) (fun y => by rw [h0]; exact hmem y), fun y => ⟨?_, ?_⟩⟩
  · apply Subtype.ext
    rw [rhoK, coe_toKur (hmem y)]
    exact (h0 y).symm
  · exact h0 y

theorem coe_rhoK (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p)
    (hσ : UnrOK (MaximalUnramifiedExtension p) p σ) (hcl : IsResidueClassZero D p ∨ IsSg D p) (z : Bool × HH D) (y : D.host.E) :
    ((rhoK D lam z y : MaximalUnramifiedExtension p) : ℂ_[p]) = tauEmb D lam (tauPl D z) y := by
  obtain ⟨ρ, hρ⟩ := exists_ringHom_rhoK D lam σ hσ hcl z
  rw [(hρ y).1, (hρ y).2]

theorem sigma_rhoK (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p)
    (hσ : UnrOK (MaximalUnramifiedExtension p) p σ) (hcl : IsResidueClassZero D p ∨ IsSg D p) (z : Bool × HH D) (y : D.host.E) :
    σ (rhoK D lam z y) = rhoK D lam (posPl D p z 1) (D.host.conj y) := by
  obtain ⟨a, ha, hsa⟩ := exists_kur_frob_tauEmb_posPl D p lam σ hσ hcl z y
  have e1 : rhoK D lam z y = a := Subtype.ext (by rw [coe_rhoK D lam σ hσ hcl, ha])
  apply Subtype.ext
  rw [e1, coe_rhoK D lam σ hσ hcl, hsa]

theorem norm_sigma_eq (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (hσ : UnrOK (MaximalUnramifiedExtension p) p σ) (x : MaximalUnramifiedExtension p) :
    ‖σ x‖ = ‖x‖ :=
  Formalism.L2.Th1.D.sigmaIsom (MaximalUnramifiedExtension p) p σ hσ x

end GlobalTheory.KerStd.HypCoord
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.twistedShift_fixed_ratio_const_domain : ∀ {B G : Type} [CommRing B] [IsDomain B] [CharZero B] (σ : G → B ≃+* B) (τ : G → B),
  (∀ d d' : B, d ≠ 0 → ¬ ∀ g, d * σ g d' - σ g d * d' = d * σ g d * τ g) →
  ∀ p q : Polynomial B, q ≠ 0 →
  (∀ g, q * (p.map (σ g : B →+* B)).comp (X + C (τ g)) = (q.map (σ g : B →+* B)).comp (X + C (τ g)) * p) →
  ∃ d d' : B, d ≠ 0 ∧ C d * p = C d' * q ∧ ∀ g, d * σ g d' = σ g d * d' := by
  first | exact @GlobalTheory.InvRatFun.fixed_ratio_const | exact GlobalTheory.InvRatFun.fixed_ratio_const | (intros; apply GlobalTheory.InvRatFun.fixed_ratio_const <;> assumption)
end
