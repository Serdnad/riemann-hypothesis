module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
public import Formalism.LocalToGlobal.Columns.Adelic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle326
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValDetSubOneLt
public import Formalism.LocalToGlobal.Columns.RecLevelTop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Formalism.LocalRingCardinality.FactDelDualNabla
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JetMapFrameEqApplyQAdaptedCoordinates
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle353
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.FullDt

attribute [local instance] rlt_top rlt_topRing adeles_t2Space

variable {R : Ranks} {H : Formalism.BasicNotions.Host R} {SG SQ : Finset (HeightOneSpectrum (𝓞 H.E))}

theorem lift_mem_KDq (hl : LevOk H SG SQ) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) (b : GlobalTheory.Mem.Chr.Ideles H.E)
    (hb : IsDetLift (host_cmData R H) x.1 b) (c : 𝓞 H.E) (hc : ∀ P ∈ uSG SG SQ, c ∈ P.asIdeal) (s : AfE H.F H.E)
    (hs : s ∈ RInt H.F H.E)
    (hx : ((x.1 : GL (Fin 1) (AfE H.F H.E)) : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)) 0 0 =
      1 + iA H.F H.E (algebraMap (𝓞 H.E) H.E c) * s) : b ∈ KDq H SQ := by
  have hd : ((x.1 : GL (Fin 1) (AfE H.F H.E)) : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)).det =
      1 + iA H.F H.E (algebraMap (𝓞 H.E) H.E c) * s := by
    rw [Matrix.det_fin_one, hx]
  have hdd := DetLift.det_mul_conj_det _ _ x.2
  set d := ((x.1 : GL (Fin 1) (AfE H.F H.E)) : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)).det with hdef
  have hci : ∀ w : HeightOneSpectrum (𝓞 H.E), adAt H.F w (iA H.F H.E (algebraMap (𝓞 H.E) H.E c)) =
      algebraMap H.E _ (algebraMap (𝓞 H.E) H.E c) := fun w => adAt_inclE H.F w _
  have hsv : ∀ w : HeightOneSpectrum (𝓞 H.E), Valued.v (adAt H.F w s) ≤ 1 := (mem_rInt_iff H.F H.E s).1 hs
  have hle : ∀ w : HeightOneSpectrum (𝓞 H.E), Valued.v (adAt H.F w d) ≤ 1 := fun w => by
    rw [hd, map_add (f := _), map_one, map_mul, hci]
    refine Valuation.map_add_le _ (by rw [map_one]) ?_
    rw [map_mul, valued_algebraMap]
    exact mul_le_one' (HeightOneSpectrum.valuation_le_one _ _) (hsv w)
  have hv1 : ∀ w : HeightOneSpectrum (𝓞 H.E), Valued.v (adAt H.F w d) = 1 := fun w => by
    have e := congrArg (fun z => Valued.v (adAt H.F w z)) hdd
    simp only [map_mul, map_one] at e
    refine le_antisymm (hle w) ?_
    have e' : Valued.v (adAt H.F w d) * Valued.v (adAt H.F (conjPrime₂ w) d) = 1 := by
      rw [← valued_sigR (host_cmData R H) w d]
      exact e
    calc (1 : _) = Valued.v (adAt H.F w d) * Valued.v (adAt H.F (conjPrime₂ w) d) := e'.symm
      _ ≤ _ := mul_le_of_le_one_right' (hle _)
  have hcomp := fun w => DetSpec.compAt_eq hb w
  refine mem_KDq_of_conj hl b (fun w => ?_) fun P hP => ?_
  · rw [hcomp w, map_mul, hv1 w, one_mul, valued_sigR, adAt_finAf]
  · have h0 : adAt H.F P (Formalism.UG.sigR (host_cmData R H).sig _ (finAf H.F H.E b : AfE H.F H.E)) ≠ 0 := by
      rw [← (Valued.v : Valuation (P.adicCompletion H.E) _).ne_zero_iff, valued_sigR, adAt_finAf]
      exact DetSpec.val_compAt_ne _ _
    rw [hcomp P, mul_div_cancel_right₀ _ h0]
    show Valued.v (adAt H.F P d - 1) < 1
    rw [hd, map_add (f := _), map_one, add_sub_cancel_left, map_mul, hci, map_mul,
      valued_algebraMap]
    have hlt : P.valuation H.E (algebraMap (𝓞 H.E) H.E c) < 1 :=
      (HeightOneSpectrum.valuation_lt_one_iff_mem P c).2 (hc P hP)
    exact (mul_le_of_le_one_right' (hsv P)).trans_lt hlt

theorem isOpen_ker_u1Dt : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (SG SQ : Finset (HeightOneSpectrum (𝓞 H.E))), LevOk H SG SQ → letI := Formalism.BasicNotions.tensTopL (F := H.F) (E := H.E) (Formalism.L2.Herm.Af H.F); IsOpen {x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H) | u1Dt H SQ x = 1} := by
  intro R H SG SQ hl
  classical
  obtain ⟨a, ha0, ha⟩ := rlt_exists_a (uSG SG SQ)
  set c : AfE H.F H.E := iA H.F H.E (algebraMap (𝓞 H.E) H.E a)⁻¹ with hc'
  have hca : iA H.F H.E (algebraMap (𝓞 H.E) H.E a) * c = 1 := by
    rw [hc', ← map_mul, mul_inv_cancel₀ (by simpa using ha0), map_one]
  let W : Set (GL (Fin 1) (AfE H.F H.E)) :=
    {u | c * ((u : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)) 0 0 - 1) ∈ Formalism.L2.Herm.intAf H.F H.E}
  have hWo : IsOpen W := by
    exact rlt_isOpen_intAf.preimage
      (continuous_const.mul ((Units.continuous_val.matrix_elem 0 0).sub continuous_const))
  have hW1 : (1 : GL (Fin 1) (AfE H.F H.E)) ∈ W := by
    show c * (((1 : GL (Fin 1) (AfE H.F H.E)) : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)) 0 0 - 1) ∈ Formalism.L2.Herm.intAf H.F H.E
    simp
  have hsub : ∀ x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H), x.1 ∈ W → x ∈ (u1Dt H SQ).ker := by
    intro x hx
    obtain ⟨b, hb⟩ := exists_lift H x
    rw [MonoidHom.mem_ker, normOneFiniteAdeleDetClass_of_isDetLift H SQ x b hb]
    refine (QuotientGroup.eq_one_iff b).2 (lift_mem_KDq hl x b hb a ha _ hx ?_)
    rw [← mul_assoc, hca, one_mul]
    ring
  have hnh : (((u1Dt H SQ).ker : Subgroup _) : Set (Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H))) ∈ 𝓝 (1 : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) := by
    have hpre : (fun x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H) => x.1) ⁻¹' W ∈ 𝓝 (1 : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) :=
      (hWo.preimage continuous_subtype_val).mem_nhds hW1
    exact Filter.mem_of_superset hpre fun x hx => hsub x hx
  exact Subgroup.isOpen_of_mem_nhds _ hnh

end GlobalTheory.Mem.Col2.FullDt

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Isom.IsoMat

open Formalism.UG (cT cT_mul cT_one)

section Gen

variable {A : Type} [CommRing A] {k n m : ℕ}

theorem conj_right_zero {r : ℕ} {aP : Matrix (Fin m) (Fin n) A} {aQ : Matrix (Fin n) (Fin m) A} (hQP : aQ * aP = 1)
    {x : Matrix (Fin n) (Fin n) A} {c : Matrix (Fin n) (Fin r) A} (h : x * c = 0) : aP * x * aQ * (aP * c) = 0 := by
  calc _ = aP * (x * ((aQ * aP) * c)) := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hQP, Matrix.one_mul, h, Matrix.mul_zero]

theorem conj_left_zero {aP : Matrix (Fin m) (Fin n) A} {aQ : Matrix (Fin n) (Fin m) A} (hQP : aQ * aP = 1)
    {x : Matrix (Fin n) (Fin n) A} {y : Matrix (Fin k) (Fin n) A} (h : y * x = 0) : y * aQ * (aP * x * aQ) = 0 := by
  calc _ = (y * ((aQ * aP) * x)) * aQ := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hQP, Matrix.one_mul, h, Matrix.zero_mul]

theorem conj_mulVec {r : ℕ} (aP : Matrix (Fin m) (Fin n) A) (aQ : Matrix (Fin n) (Fin m) A)
    (x : Matrix (Fin n) (Fin n) A) (c : Matrix (Fin n) (Fin r) A) (v : Fin m → A) (a : Fin r → A)
    (h : x.mulVec (aQ.mulVec v) = c.mulVec a) : (aP * x * aQ).mulVec v = (aP * c).mulVec a := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_mulVec]

theorem conj_sub_one {aP : Matrix (Fin m) (Fin n) A} {aQ : Matrix (Fin n) (Fin m) A} (hPQ : aP * aQ = 1)
    (x : Matrix (Fin n) (Fin n) A) : aP * x * aQ - 1 = aP * (x - 1) * aQ := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ]

end Gen

variable {D : D7} {V V' : HSp D} (I : IsoMat V V')

theorem cT_P_gram : cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.P * V'.gram = V.gram * I.Q := by
  rw [← I.gram, Matrix.mul_assoc _ I.P, I.PQ, Matrix.mul_one]

theorem mat_kap_sub (g : GA D V) :
    (matHom V' (I.kap g)).1 - 1 = HMul.hMul (HMul.hMul I.aP ((matHom V g).1 - 1)) I.aQ :=
  conj_sub_one I.aP_aQ _

theorem kap_mem_NI {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) {x : GA D V} (hx : x ∈ NI V C) :
    I.kap x ∈ NI V' (I.P * C) := by
  have key : NI V C ≤ (NI V' (I.P * C)).comap I.kap.toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    intro g hg
    show I.kap g ∈ NI V' (I.P * C)
    obtain ⟨h1, h2, h3⟩ := hg
    refine Subgroup.subset_closure ?_
    have hm := I.mat_kap_sub g
    have hPC : (I.P * C).map (incA D) = I.aP * C.map (incA D) := Matrix.map_mul
    have hG : cT (D.sp.cm.sig : D.host.E →+* D.host.E) (I.P * C) * V'.gram =
        cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram * I.Q := by
      rw [cT_mul, Matrix.mul_assoc, I.cT_P_gram, Matrix.mul_assoc]
    have hGm : (cT (D.sp.cm.sig : D.host.E →+* D.host.E) (I.P * C) * V'.gram).map (incA D) =
        (cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).map (incA D) * I.aQ := by
      rw [hG, Matrix.map_mul]; rfl
    refine ⟨?_, ?_, fun x' hx' => ?_⟩
    · show HMul.hMul ((matHom V' (I.kap g)).1 - 1) ((I.P * C).map (incA D)) = 0
      rw [hm, hPC]
      exact conj_right_zero I.aQ_aP h1
    · show HMul.hMul ((cT (D.sp.cm.sig : D.host.E →+* D.host.E) (I.P * C) * V'.gram).map (incA D))
        ((matHom V' (I.kap g)).1 - 1) = 0
      rw [hGm, hm]
      exact conj_left_zero I.aQ_aP h2
    · have hx : (cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).mulVec (I.Q.mulVec x') = 0 := by
        rw [Matrix.mulVec_mulVec, ← hG]
        exact hx'
      obtain ⟨a, ha⟩ := h3 _ hx
      refine ⟨a, ?_⟩
      have hQx : I.aQ.mulVec (fun i => incA D (x' i)) = fun i => incA D (I.Q.mulVec x' i) :=
        funext fun i => (RingHom.map_mulVec (incA D) I.Q x' i).symm
      show ((matHom V' (I.kap g)).1 - 1).mulVec (fun i => incA D (x' i)) = ((I.P * C).map (incA D)).mulVec a
      rw [hm, hPC]
      refine conj_mulVec _ _ _ _ _ _ ?_
      rw [hQx]
      exact ha
  exact key hx

theorem isIsoFrame_Q {r : ℕ} {C' : Matrix (Fin V'.rank) (Fin r) D.host.E} (h : IsIsoFrame V' C') :
    IsIsoFrame V (I.Q * C') := by
  obtain ⟨hr, hli, hiso⟩ := h
  refine ⟨hr, ?_, ?_⟩
  · have e : (I.Q * C').transpose = (Matrix.mulVecLin I.Q) ∘ C'.transpose := by
      funext i j
      rfl
    rw [e]
    refine hli.map' _ (LinearMap.ker_eq_bot.2 fun a b hab => ?_)
    have := congrArg I.P.mulVec hab
    simpa [Matrix.mulVec_mulVec, I.PQ] using this
  · have hg : cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.Q * V.gram * I.Q = V'.gram := I.symm.gram
    rw [cT_mul]
    calc _ = cT (D.sp.cm.sig : D.host.E →+* D.host.E) C' *
          (cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.Q * V.gram * I.Q) * C' := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hg]; exact hiso

theorem kap_mem_NI' {r : ℕ} {C' : Matrix (Fin V'.rank) (Fin r) D.host.E} {x : GA D V} (hx : x ∈ NI V (I.Q * C')) :
    I.kap x ∈ NI V' C' := by
  have := I.kap_mem_NI (I.Q * C') hx
  rwa [← Matrix.mul_assoc, I.PQ, Matrix.one_mul] at this

theorem kap_symm_mem_NI {r : ℕ} {C' : Matrix (Fin V'.rank) (Fin r) D.host.E} {y : GA D V'} (hy : y ∈ NI V' C') :
    I.kap.symm y ∈ NI V (I.Q * C') :=
  I.symm.kap_mem_NI C' hy

end GlobalTheory.Mem.Isom.IsoMat


open GlobalTheory.Mem.Isom GlobalTheory.Mem.Isom.IsoMat in
theorem GlobalTheory.Mem.Isom.isCuspFun_tr : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (φ : GA D V → ℂ),
    IsCuspFun V φ → IsCuspFun V' (I.tr φ) := by
  intro D V V' I φ hφ r C' hC' μ 𝓕 hμ h𝓕 g
  haveI := GlobalTheory.AutFunCounterexample.borel_NI D V (I.Q * C')
  haveI := GlobalTheory.AutFunCounterexample.borel_NI D V' C'
  haveI := GlobalTheory.AutFunCounterexample.topGroup_GA D V
  haveI := GlobalTheory.AutFunCounterexample.topGroup_GA D V'
  let T : NI V (I.Q * C') ≃ₜ* NI V' C' :=
    { toFun := fun x => ⟨I.kap (x : GA D V), I.kap_mem_NI' x.2⟩
      invFun := fun y => ⟨I.kap.symm (y : GA D V'), I.kap_symm_mem_NI y.2⟩
      left_inv := fun x => Subtype.ext (I.kap.symm_apply_apply (x : GA D V))
      right_inv := fun y => Subtype.ext (I.kap.apply_symm_apply (y : GA D V'))
      map_mul' := fun x y => Subtype.ext (map_mul I.kap (x : GA D V) (y : GA D V))
      continuous_toFun := (I.continuous_kap.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (I.continuous_kap_symm.comp continuous_subtype_val).subtype_mk _ }
  let e : NI V (I.Q * C') ≃ᵐ NI V' C' := T.toHomeomorph.toMeasurableEquiv
  have hp : MeasurePreserving e (μ.map e.symm) μ :=
    (MeasurePreserving.symm e.symm ⟨e.symm.measurable, rfl⟩ :)
  have hH : (μ.map e.symm).IsHaarMeasure := T.symm.isHaarMeasure_map μ
  have hF : IsFundamentalDomain (NIQ V (I.Q * C')) (e ⁻¹' 𝓕) (μ.map e.symm) := by
    refine h𝓕.preimage_of_equiv hp.quasiMeasurePreserving
      (e := fun γ => ⟨T.symm γ, I.symm.kap_mem_GQ γ.2⟩) ⟨fun a b hab => ?_, fun b => ?_⟩ fun γ x => ?_
    · exact Subtype.ext (T.symm.injective (congrArg Subtype.val hab))
    · exact ⟨⟨T b.1, I.kap_mem_GQ b.2⟩, Subtype.ext (T.symm_apply_apply _)⟩
    · change T (T.symm γ * x) = γ * T x
      rw [map_mul, T.apply_symm_apply]
  have key := hφ r (I.Q * C') (I.isIsoFrame_Q hC') (μ.map e.symm) (e ⁻¹' 𝓕) hH hF (I.kap.symm g)
  rw [← hp.setIntegral_preimage_emb e.measurableEmbedding (fun n : NI V' C' => I.tr φ ((n : GA D V') * g)) 𝓕]
  refine Eq.trans ?_ key
  congr 1
  funext x
  show φ (I.kap.symm (I.kap (x : GA D V) * g)) = φ ((x : GA D V) * I.kap.symm g)
  rw [map_mul, MulEquiv.symm_apply_apply]
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Isom

theorem sum_norm_conj_le {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    (Q : Matrix (Fin n) (Fin m) ℂ) :
    ∑ i, ∑ j, ‖(P * A * Q) i j‖ ≤
      ((m : ℝ) * m * (∑ i, ∑ k, ‖P i k‖) * (∑ l, ∑ j, ‖Q l j‖)) * ∑ k, ∑ l, ‖A k l‖ := by
  set cP := ∑ i, ∑ k, ‖P i k‖
  set cQ := ∑ l, ∑ j, ‖Q l j‖
  set S := ∑ k, ∑ l, ‖A k l‖
  have hP : ∀ i k, ‖P i k‖ ≤ cP := fun i k =>
    (Finset.single_le_sum (f := fun k => ‖P i k‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ k)).trans
      (Finset.single_le_sum (f := fun i => ∑ k, ‖P i k‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.mem_univ i))
  have hQ : ∀ l j, ‖Q l j‖ ≤ cQ := fun l j =>
    (Finset.single_le_sum (f := fun j => ‖Q l j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun l => ∑ j, ‖Q l j‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.mem_univ l))
  have hcP : 0 ≤ cP := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcQ : 0 ≤ cQ := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hent : ∀ i j, ‖(P * A * Q) i j‖ ≤ cP * cQ * S := by
    intro i j
    have e : (P * A * Q) i j = ∑ l, ∑ k, P i k * A k l * Q l j := by
      simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [e]
    calc ‖∑ l, ∑ k, P i k * A k l * Q l j‖ ≤ ∑ l, ∑ k, ‖P i k‖ * ‖A k l‖ * ‖Q l j‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => (norm_sum_le _ _).trans (le_of_eq ?_))
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [norm_mul, norm_mul]
      _ ≤ ∑ l, ∑ k, cP * ‖A k l‖ * cQ := by
          refine Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun k _ => ?_
          exact mul_le_mul (mul_le_mul_of_nonneg_right (hP i k) (norm_nonneg _)) (hQ l j) (norm_nonneg _)
            (mul_nonneg hcP (norm_nonneg _))
      _ = cP * cQ * S := by
          rw [Finset.sum_comm]
          simp only [S, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          ring
  calc ∑ i, ∑ j, ‖(P * A * Q) i j‖ ≤ ∑ _i : Fin m, ∑ _j : Fin m, cP * cQ * S :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hent i j
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem normInf_kap_le : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (θ : InfF D), IsInfFam θ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : GA D V, normInf θ V' (I.kap g) ≤ C * normInf θ V g := by
  intro D V V' I θ hθ
  let K : D.what₂.Tau → ℝ := fun τ =>
    (V'.rank : ℝ) * V'.rank * (∑ i, ∑ k, ‖I.pT τ i k‖) * (∑ l, ∑ j, ‖I.qT τ l j‖)
  have hK : ∀ τ, 0 ≤ K τ := fun τ => by positivity
  refine ⟨∑ τ, K τ, Finset.sum_nonneg fun τ _ => hK τ, fun g => ?_⟩
  unfold normInf
  have key : ∀ τ, (∑ i, ∑ j, (‖infMat D.sp.cm.sig V'.gram (θ τ) (I.kap g) i j‖ +
      ‖infMat D.sp.cm.sig V'.gram (θ τ) (I.kap g)⁻¹ i j‖)) ≤
      K τ * ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖) := by
    intro τ
    rw [← map_inv I.kap g, I.infMat_kap hθ, I.infMat_kap hθ]
    simp only [Finset.sum_add_distrib, mul_add]
    exact add_le_add (sum_norm_conj_le _ _ _) (sum_norm_conj_le _ _ _)
  have hS : ∀ τ, 0 ≤ ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ +
      ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖) := fun τ => by positivity
  calc _ ≤ ∑ τ, K τ * ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ +
          ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖) := Finset.sum_le_sum fun τ _ => key τ
    _ ≤ ∑ τ, (∑ σ, K σ) * ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ +
          ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖) :=
        Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun σ _ => hK σ) (Finset.mem_univ τ)) (hS τ)
    _ = _ := by rw [← Finset.mul_sum]

end GlobalTheory.Mem.Isom
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Isom

theorem haar_fd_phi : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (S : HSp D) (μ : Measure (WO S V')) (𝓕 : Set (WO S V')), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL V' S) 𝓕 μ → ∃ (ν : Measure (WO S V)) (𝓖 : Set (WO S V)), ν.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratL V S) 𝓖 ν ∧ ∀ u : WO S V → ENNReal, ∫⁻ w in 𝓕, u ((I.phi S).symm w) ∂μ = ∫⁻ w in 𝓖, u w ∂ν := by
  intro D V V' I S μ 𝓕 hμ h𝓕
  haveI hB : BorelSpace (WO S V) := ⟨rfl⟩
  haveI hB' : BorelSpace (WO S V') := ⟨rfl⟩
  have hc := I.continuous_phi S
  have hcs := I.continuous_phi_symm S
  have hrat : ∀ x, I.phi S x ∈ ratL V' S ↔ x ∈ ratL V S := by
    intro x
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨I.Q * z, ?_⟩
      have h1 := I.symm.phi_ratW S z
      have h2 : ratW V' S z = I.phi S x := hz
      rw [h2, ← I.phi_symm_apply, AddEquiv.symm_apply_apply] at h1
      exact h1.symm
    · rintro ⟨z, hz⟩
      refine ⟨I.P * z, ?_⟩
      have h1 := I.phi_ratW S z
      have h2 : ratW V S z = x := hz
      rw [h2] at h1
      exact h1.symm
  let m : WO S V ≃ᵐ WO S V' :=
    { toEquiv := (I.phi S).toEquiv
      measurable_toFun := hc.measurable
      measurable_invFun := hcs.measurable }
  have hmp : MeasurePreserving m (μ.map m.symm) μ :=
    (MeasurePreserving.symm m.symm ⟨m.symm.measurable, rfl⟩)
  have hmp' : MeasurePreserving (I.phi S) (μ.map (I.phi S).symm) μ := hmp
  refine ⟨μ.map (I.phi S).symm, I.phi S ⁻¹' 𝓕, AddEquiv.isAddHaarMeasure_map μ (I.phi S).symm hcs (by simpa using hc), ?_, ?_⟩
  · let f : ratL V' S → ratL V S := fun y => ⟨(I.phi S).symm y, (hrat _).1 (by simpa using y.2)⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b hab
        exact Subtype.ext ((I.phi S).symm.injective (congrArg Subtype.val hab))
      · intro x
        exact ⟨⟨I.phi S x, (hrat _).2 x.2⟩, Subtype.ext (by simp [f])⟩
    refine h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hf ?_
    intro y x
    simp [f, AddSubgroup.vadd_def]
  · intro u
    have := hmp'.setLIntegral_comp_preimage_emb m.measurableEmbedding (fun b => u ((I.phi S).symm b)) 𝓕
    simpa using this.symm

end GlobalTheory.Mem.Isom
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section
namespace GlobalTheory.HeckeLocN

theorem exists_finExt_big (D : D7) (pl : PlSide D) (big : D.what₂.places.Pl → Finset ℂ) (w : D.what₂.places.Pl) :
    ∃ F0 : Loc.FinExt (D.what₂.places.resChar w), (∀ x, (plEmb pl).emb w x ∈ F0.1) ∧
      ∀ z ∈ big w, (pl.ι w).symm z ∈ F0.1 := by
  classical
  let c := (plEmb pl).emb w
  let S : Finset (Loc.Om (D.what₂.places.resChar w)) := (big w).image (fun z => (pl.ι w).symm z)
  have h1 := GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range c
  have h2 : FiniteDimensional ℚ_[D.what₂.places.resChar w]
      (IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (S : Set (Loc.Om (D.what₂.places.resChar w)))) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨⟨IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (Set.range c) ⊔
      IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (S : Set (Loc.Om (D.what₂.places.resChar w))),
      IntermediateField.finiteDimensional_sup _ _⟩, fun x => ?_, fun z hz => ?_⟩
  · exact (le_sup_left (a := IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (Set.range c)) (b := IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (S : Set (Loc.Om (D.what₂.places.resChar w))))) (IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩)
  · exact (le_sup_right (a := IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (Set.range c)) (b := IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (S : Set (Loc.Om (D.what₂.places.resChar w))))) (IntermediateField.subset_adjoin _ _ (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hz)))

end GlobalTheory.HeckeLocN
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open Classical

theorem _root_.GlobalTheory.T.jetMap_frame_eq_applyQ_adapted_coordinates : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (N0 N1 : ℕ) (hN : N0 ≤ N1)
    (T : MvPowerSeries (D.what₂.Tau × Fin N1 × Fin N0) ℂ_[p]) (s : D.what₂.Tau → ℂ_[p])
    (B : D.what₂.Tau → Matrix (Fin N0) (Fin N0) ℂ_[p]) (B' : D.what₂.Tau → Matrix (Fin N1) (Fin N1) ℂ_[p])
    (hB : ∀ τ, (B τ).det ≠ 0) (P : MvPolynomial (GL3Theta.FrV D N0) ℂ_[p]) (y' : D.what₂.Tau → Matrix (Fin N1) (Fin N1) ℂ_[p]), MvPolynomial.eval (fun k : GL3Theta.FrV D N1 => (B' k.1 * y' k.1) k.2.1 k.2.2)
      (jetMap (fun m => (m.prod fun k n => s k.1 ^ n) * (m.prod fun _ n => (n.factorial : ℂ_[p])) * MvPowerSeries.coeff m T)
        (fun _ => 0) P) =
    GL3Columns.applyQ p N0 N1
      (atLin (fun (k : D.what₂.Tau × Fin N1 × Fin N0) (j : (Bool × HH D) × Fin N0 × Fin N1) =>
          if tauPl D j.1 = k.1 then 1 * s k.1 * B' k.1 k.2.1 j.2.2 * (B k.1)⁻¹ j.2.1 k.2.2 else 0)
        (fun j => MvPowerSeries.X j) T)
      (MvPolynomial.aeval (fun k : GL3Theta.FrV D N0 => ∑ a : Fin N0,
          MvPolynomial.C (B k.1 k.2.1 a) * MvPolynomial.X ((Equiv.ofBijective (tauPl D) (tauPl_bij D)).symm k.1, a, (k.2.2 : ℕ))) P)
      (fun z => GL3Columns.colsOf (y' (tauPl D z))) := by
  first | exact @GlobalTheory.JetChain.jetMap_frame_eq_applyQ | exact GlobalTheory.JetChain.jetMap_frame_eq_applyQ | (intros; apply GlobalTheory.JetChain.jetMap_frame_eq_applyQ <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localBasis_and_embeddedBasis_differ_by_unimodular_integral : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (Bm : GL (Fin N) D.host.E) (M : Matrix (Fin N) (Fin N) ℂ_[p]), Formalism.L2.Forms.IsLocBasis p (L : Set (Fin N → D.host.E)) Bm → GL3Columns.BasR D lam τ L M → ∃ g : Matrix (Fin N) (Fin N) ℂ_[p], (∀ a b, ‖g a b‖ ≤ 1) ∧ ‖g.det‖ = 1 ∧ M = (Bm : Matrix (Fin N) (Fin N) D.host.E).map (TaylorLogMetric.tauEmb D lam τ) * g := by
  first | exact @GlobalTheory.LocBasisBasR.main | exact GlobalTheory.LocBasisBasR.main | (intros; apply GlobalTheory.LocBasisBasR.main <;> assumption)
end
