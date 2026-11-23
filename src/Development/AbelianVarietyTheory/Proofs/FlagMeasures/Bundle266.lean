module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle021
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle271
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle255
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle051
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle056
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfSS
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVSec
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushI
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushH
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle010
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.PolarHyp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle006
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Formalism.LocalToGlobal.GlobalTheory.GL2.ModEqOfNormOneMod
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ResidEvFree
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.Bundle002
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle228
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle109
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
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
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle042
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfCo

@[expose] public section

section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.exists_signature_blocks_of_vector_and_frame : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (s : Bool) (x₀ : Fin (n + 1) → ℂ) (B : Matrix (Fin (n + 1)) (Fin n) ℂ), GlobalTheory.GaussMean.qEps ε x₀ = GlobalTheory.GaussMean.sgn ℝ s → star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0 → Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε' → ∀ (P Q P' Q' : ℕ) (f : Fin P ⊕ Fin Q ≃ Fin (n + 1)) (f' : Fin P' ⊕ Fin Q' ≃ Fin n), Sorts ε f → Sorts ε' f' → ∃ e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q), SignCompat e ∧ sg (e none) = GlobalTheory.GaussMean.sgn ℝ s := by
  first | exact @GlobalTheory.SignCount.exists_signCompat | exact GlobalTheory.SignCount.exists_signCompat | (intros; apply GlobalTheory.SignCount.exists_signCompat <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.FrameExtend

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem hR_sub_sum_right {m : ℕ} (x w : Fin n → R ⊗[F] E) (c : Fin m → R ⊗[F] E)
    (u : Fin m → Fin n → R ⊗[F] E) :
    hR R σ J x (w - ∑ a, c a • u a) = hR R σ J x w - ∑ a, c a * hR R σ J x (u a) := by
  simp only [hR, Formalism.UG.hform, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

end Alg


open GlobalTheory.FrameGram in
theorem extend_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ y : Fin (r + 1) → Fin n → Fv F v ⊗[F] E, LinearIndependent (Fv F v ⊗[F] E) y → gramR (Fv F v) σ J y = (gramE σ J (F0 P)).map (inclR (Fv F v)) → ∃ f : Fin r → Fin n → Fv F v ⊗[F] E, gramR (Fv F v) σ J (Fin.append y f) = (gramE σ J (tupH P)).map (inclR (Fv F v)) := by
  intro F E _ _ _ _ _ σ hσ n J hJ v r P T hP y hy hgram
  have hinv : ∀ x, σ (σ x) = x := conj_invol hσ
  obtain ⟨_, hGh, _, hG0, _⟩ := std_frame_gram F E σ hσ n J hJ r P T hP
  have hPs := hP
  obtain ⟨_, hff0, hef, _, hfz, _, _⟩ := hPs
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsArtinianRing (Fv F v ⊗[F] E) := IsArtinianRing.of_finite (Fv F v) (Fv F v ⊗[F] E)
  have : IsReduced (Fv F v ⊗[F] E) := PI.VolStabS.isReduced_tens_field F E (Fv F v)
  have : IsSemisimpleRing (Fv F v ⊗[F] E) := IsArtinianRing.isSemisimpleRing_of_isReduced _
  let s := sigR (Fv F v) σ
  have hsw : ∀ x w, s (hR (Fv F v) σ J x w) = hR (Fv F v) σ J w x :=
    PI.VolStabS.hR_herm (Fv F v) σ hinv J hJ.1
  have hss : ∀ x, s (s x) = x := PI.VolStabS.sigR_invol (Fv F v) σ hinv

  let Z : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun i => Matrix.vecMul (fun l => s (y i l)) (JR (F := F) (Fv F v) J)
  have hZh : ∀ i w, hR (Fv F v) σ J (y i) w = ∑ k, Z i k * w k := by
    intro i w
    simp only [hR, Formalism.UG.hform, Z, Matrix.vecMul, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hZ : LinearIndependent (Fv F v ⊗[F] E) Z := by
    have hJu : IsUnit (JR (F := F) (Fv F v) J).det := by
      have e := RingHom.map_det (inclR (F := F) (E := E) (Fv F v)) J
      rw [RingHom.mapMatrix_apply] at e
      show IsUnit (J.map (inclR (Fv F v))).det
      rw [← e]
      exact (isUnit_iff_ne_zero.2 hJ.2).map _
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    let w : Fin n → Fv F v ⊗[F] E := fun l => ∑ i, g i * s (y i l)
    have hv0 : Matrix.vecMul w (JR (F := F) (Fv F v) J) = 0 := by
      funext j
      have := congrFun hg j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Z, Matrix.vecMul, dotProduct,
        Finset.mul_sum, Pi.zero_apply] at this
      simp only [Matrix.vecMul, dotProduct, w, Finset.sum_mul, Pi.zero_apply]
      rw [Finset.sum_comm]
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
    have hv : w = 0 := by
      have := congrArg (fun u => Matrix.vecMul u (JR (F := F) (Fv F v) J)⁻¹) hv0
      simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hJu, Matrix.vecMul_one,
        Matrix.zero_vecMul] at this
      exact this
    have hX0 : ∑ i, s (g i) • y i = 0 := by
      funext l
      have := congrArg s (congrFun hv l)

      simp only [w, map_sum, map_mul, hss, Pi.zero_apply, map_zero] at this
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    have := Fintype.linearIndependent_iff.1 hy _ hX0 i
    have e2 := congrArg s this
    simp only [hss, map_zero] at e2
    exact e2
  obtain ⟨q, hq⟩ := PI.VolStabS.exists_leftInv_of_linIndep Z hZ

  let f' : Fin r → Fin n → Fv F v ⊗[F] E := fun b k => q k b.castSucc
  have hyf' : ∀ i b, hR (Fv F v) σ J (y i) (f' b) = if i = b.castSucc then 1 else 0 := by
    intro i b
    rw [hZh]
    exact hq i b.castSucc
  have hyy : ∀ i j, hR (Fv F v) σ J (y i) (y j) =
      inclR (Fv F v) (if i = Fin.last r ∧ j = Fin.last r then algebraMap F E (-T) else 0) := by
    intro i j
    have := congrFun (congrFun hgram i) j
    simp only [Matrix.map_apply, hG0] at this
    exact this
  have hyy0 : ∀ i (a : Fin r), hR (Fv F v) σ J (y i) (y a.castSucc) = 0 := by
    intro i a
    rw [hyy]
    simp [Fin.castSucc_ne_last]
  let h2 : Fv F v ⊗[F] E := algebraMap F (Fv F v ⊗[F] E) (1 / 2)
  have hh : h2 + h2 = 1 := by
    rw [← map_add (f := _), show (1 / 2 : F) + 1 / 2 = 1 by norm_num, map_one]
  have hsh : s h2 = h2 := (Algebra.TensorProduct.map (AlgHom.id F (Fv F v)) σ).commutes _
  let c : Fin r → Fin r → Fv F v ⊗[F] E := fun a b => h2 * hR (Fv F v) σ J (f' a) (f' b)
  let f : Fin r → Fin n → Fv F v ⊗[F] E := fun b => f' b - ∑ a, c a b • y a.castSucc
  have hyf : ∀ i b, hR (Fv F v) σ J (y i) (f b) = if i = b.castSucc then 1 else 0 := by
    intro i b
    simp only [f]
    rw [GlobalTheory.FrameExtend.hR_sub_sum_right, hyf']
    simp [hyy0]
  have hfy : ∀ b i, hR (Fv F v) σ J (f b) (y i) = if i = b.castSucc then 1 else 0 := by
    intro b i
    rw [← hsw, hyf]
    split_ifs <;> simp
  have hf'y : ∀ b (d : Fin r), hR (Fv F v) σ J (f' b) (y d.castSucc) = if d = b then 1 else 0 := by
    intro b d
    rw [← hsw, hyf']
    split_ifs with h1 h2 h2 <;> simp_all [Fin.castSucc_inj]
  have hff : ∀ a b, hR (Fv F v) σ J (f a) (f b) = 0 := by
    intro a b
    have e1 : hR (Fv F v) σ J (f a) (f b) = hR (Fv F v) σ J (f a) (f' b) - c a b := by
      simp only [f]
      rw [GlobalTheory.FrameExtend.hR_sub_sum_right]
      congr 1
      have := fun d => hfy a (Fin.castSucc d)
      simp only [f] at this
      simp [this, Fin.castSucc_inj]
    have e2 : hR (Fv F v) σ J (f' b) (f a) = hR (Fv F v) σ J (f' b) (f' a) - c b a := by
      simp only [f]
      rw [GlobalTheory.FrameExtend.hR_sub_sum_right]
      congr 1
      simp [hf'y]
    have e3 : hR (Fv F v) σ J (f a) (f' b) = hR (Fv F v) σ J (f' a) (f' b) - h2 * hR (Fv F v) σ J (f' a) (f' b) := by
      rw [← hsw, e2, map_sub, hsw]
      simp only [c, map_mul, hsh, hsw]
    rw [e1, e3]
    simp only [c]
    linear_combination (-(hR (Fv F v) σ J (f' a) (f' b))) * hh
  refine ⟨f, ?_⟩
  have hTL : ∀ i (b : Fin r), gramE σ J (tupH P) (Fin.castAdd r i) (Fin.natAdd (r + 1) b) =
      if i = b.castSucc then 1 else 0 := by
    intro i b
    simp only [gramE, tupH, Fin.append_left, Fin.append_right, F0]
    refine Fin.lastCases ?_ (fun a => ?_) i
    · rw [Fin.snoc_last, ← hE_swap hinv hJ.1 P.z (P.f b), hfz, map_zero]
      exact (if_neg (Fin.castSucc_ne_last b).symm).symm
    · rw [Fin.snoc_castSucc, hef]
      simp only [Fin.castSucc_inj]
  funext i j
  simp only [Matrix.map_apply]
  show hR (Fv F v) σ J (Fin.append y f i) (Fin.append y f j) = _
  refine Fin.addCases (fun i => ?_) (fun a => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun b => ?_) j
  · rw [Fin.append_left, Fin.append_left, hyy, ← hG0]
    simp [gramE, tupH, Fin.append_left]
  · rw [Fin.append_left, Fin.append_right, hyf, hTL]
    split_ifs <;> simp
  · rw [Fin.append_right, Fin.append_left, hfy, ← hGh, hTL]
    split_ifs <;> simp
  · rw [Fin.append_right, Fin.append_right, hff]
    simp [gramE, tupH, Fin.append_right, hff0]

end GlobalTheory.FrameExtend
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace GlobalTheory.HyperboloidPolar

open PI.RhsWLim PI.RhsWLim.W

variable {k r : ℕ}

theorem opVec_inWb (p : (Fin k → ℂ) × ℂ) : inWb k r (opVec k r p) := by
  intro i hi
  unfold opVec
  rw [dif_neg (by omega), if_neg (by omega)]

theorem wbPart_opVec (p : (Fin k → ℂ) × ℂ) : wbPart k r (opVec k r p) = toW k p := by
  funext m
  have := m.isLt
  unfold wbPart opVec toW wI
  by_cases h : m.val < k
  · rw [dif_pos (by simp only; omega), dif_pos h]
    exact congrArg p.1 (Fin.ext (by simp))
  · rw [dif_neg (by simp only; omega), dif_neg h, if_pos (by simp only; omega)]

theorem opCo_eq (v : Fin (2 * r + k + 1) → ℂ) : opCo k r v = ofW k (wbPart k r v) := rfl

theorem opCo_opVec (p : (Fin k → ℂ) × ℂ) : opCo k r (opVec k r p) = p := by
  rw [opCo_eq, wbPart_opVec, ofW_toW]

theorem eq_of_wbPart {v w : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (hw : inWb k r w)
    (h : wbPart k r v = wbPart k r w) : v = w := by
  funext i
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [hv i hi, hw i hi]
  · have hm : MB.mid k r i := by constructor <;> omega
    have := congrFun h (MB.midx hm)
    simpa only [wbPart, MB.wI_midx] using this

theorem opVec_opCo {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) : opVec k r (opCo k r v) = v :=
  eq_of_wbPart (opVec_inWb _) hv (by rw [wbPart_opVec, opCo_eq, toW_ofW])

theorem inWb_uwb {s : Mat k r} (hs : s ∈ UWb k r) {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    inWb k r (s *ᵥ v) := by
  rw [op_uwb_eq_emb hs]
  exact RI.inWb_emb _ hv

theorem continuous_opVec : Continuous (opVec k r) := by
  refine continuous_pi fun i => ?_
  unfold opVec
  by_cases h : r ≤ i.val ∧ i.val < r + k
  · simp only [dif_pos h]
    exact (continuous_apply _).comp continuous_fst
  · simp only [dif_neg h]
    by_cases h' : i.val = r + k
    · simp only [if_pos h']
      exact continuous_snd
    · simp only [if_neg h']
      exact continuous_const

theorem continuous_opCo : Continuous (opCo k r) :=
  (continuous_pi fun i => continuous_apply (wI k r (Fin.castSucc i))).prodMk
    (continuous_apply (wI k r (Fin.last k)))

theorem herm_opVec (p : (Fin k → ℂ) × ℂ) :
    herm (Hpk k r) (opVec k r p) (opVec k r p) = (qf k p : ℂ) := by
  rw [herm_wb _ _ (opVec_inWb p), wbPart_opVec, qf_eq]
  rfl

theorem herm_self_eq {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    herm (Hpk k r) z z = ((-Tz k r z : ℝ) : ℂ) := by
  unfold Tz
  rw [neg_neg, herm_wb _ _ hz, hermHb_self, Complex.ofReal_re]

def hypAmb (k r : ℕ) (T' : ℝ) : Measure (Fin (2 * r + k + 1) → ℂ) := (hypM k T').map (opVec k r)

theorem hypAmb_sigmaFinite {T' : ℝ} (hT' : 0 < T') : SigmaFinite (hypAmb k r T') := by
  have : IsFiniteMeasureOnCompacts (hypAmb k r T') := by
    refine ⟨fun C hC => ?_⟩
    rw [hypAmb, Measure.map_apply continuous_opVec.measurable hC.measurableSet]
    refine lt_of_le_of_lt (measure_mono ?_) ((hypLF k T' hT').2 _ (hC.image continuous_opCo))
    intro p hp
    exact ⟨_, hp, opCo_opVec p⟩
  infer_instance

theorem hypAmb_inv (hk : 1 ≤ k) {T' : ℝ} (hT' : 0 < T') {s : Mat k r} (hs : s ∈ UWb k r) :
    (hypAmb k r T').map (fun v => s *ᵥ v) = hypAmb k r T' := by
  have hI := hypInv_of lebInvB (coneForm_of hypTh coneVol) k r T' hk hT' s hs
  have hm : Continuous (fun v : Fin (2 * r + k + 1) → ℂ => s *ᵥ v) :=
    continuous_const.matrix_mulVec continuous_id
  have hA : Continuous (opAct k r s) := continuous_opCo.comp (hm.comp continuous_opVec)
  have e : (fun v => s *ᵥ v) ∘ opVec k r = opVec k r ∘ opAct k r s := by
    funext p
    exact (opVec_opCo (inWb_uwb hs (opVec_inWb p))).symm
  rw [hypAmb, Measure.map_map hm.measurable continuous_opVec.measurable, e,
    ← Measure.map_map continuous_opVec.measurable hA.measurable, hI]

theorem hypAmb_conc {z' : Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z') (hT' : 0 < Tz k r z') :
    hypAmb k r (Tz k r z') {v | ¬ (inWb k r v ∧ herm (Hpk k r) v v = herm (Hpk k r) z' z')} = 0 := by
  have hc : IsClosed {v : Fin (2 * r + k + 1) → ℂ |
      inWb k r v ∧ herm (Hpk k r) v v = herm (Hpk k r) z' z'} := by
    change IsClosed ({v : Fin (2 * r + k + 1) → ℂ | inWb k r v} ∩
      {v : Fin (2 * r + k + 1) → ℂ | herm (Hpk k r) v v = herm (Hpk k r) z' z'})
    apply IsClosed.inter
    · have : {v : Fin (2 * r + k + 1) → ℂ | inWb k r v} =
          ⋂ i : Fin (2 * r + k + 1), ⋂ _ : (i.val < r ∨ r + k < i.val), {v | v i = 0} := by
        ext v
        simp only [inWb, Set.mem_iInter]
        rfl
      show IsClosed {v : Fin (2 * r + k + 1) → ℂ | inWb k r v}
      rw [this]
      exact isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_eq (continuous_apply i) continuous_const
    · apply isClosed_eq
      · unfold herm
        exact continuous_id.star.dotProduct (continuous_const.matrix_mulVec continuous_id)
      · exact continuous_const
  have hm : MeasurableSet {v : Fin (2 * r + k + 1) → ℂ |
      ¬ (inWb k r v ∧ herm (Hpk k r) v v = herm (Hpk k r) z' z')} := hc.measurableSet.compl
  rw [hypAmb, Measure.map_apply continuous_opVec.measurable hm]
  refine measure_mono_null ?_ (hypLF k _ hT').1
  intro p hp hS
  apply hp
  refine ⟨opVec_inWb p, ?_⟩
  rw [herm_opVec, herm_self_eq hz', (hypS_iff _ p).1 hS]

theorem hypAmb_polar (hk : 1 ≤ k) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {T' : ℝ} (hT' : 0 < T') (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ v, g (herm (Hpk k r) v z) ∂hypAmb k r T' =
      ENNReal.ofReal (2 * Real.pi ^ k / (k - 1).factorial / (2 * Tz k r z ^ k)) *
        ∫⁻ ζ, ENNReal.ofReal (zWeight k (Tz k r z) T' ζ) * g ζ := by
  obtain ⟨p, hp, hpz⟩ := transW k r z hz hT
  set s := Real.sqrt (Tz k r z) with hs
  have hs0 : (s : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact (Real.sqrt_pos.2 hT).ne'
  set zs := ((s : ℂ) • wLast k r) with hzs
  have hgm : Measurable fun v => g (herm (Hpk k r) v zs) := hg.comp (RI.cont_herm zs).measurable
  have hm : Measurable (fun v : Fin (2 * r + k + 1) → ℂ => p⁻¹ *ᵥ v) :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have step1 : ∫⁻ v, g (herm (Hpk k r) v z) ∂hypAmb k r T' = ∫⁻ v, g (herm (Hpk k r) v zs) ∂hypAmb k r T' := by
    calc ∫⁻ v, g (herm (Hpk k r) v z) ∂hypAmb k r T'
        = ∫⁻ v, (fun y => g (herm (Hpk k r) y zs)) (p⁻¹ *ᵥ v) ∂hypAmb k r T' := by
          refine lintegral_congr fun v => ?_
          rw [← hpz, herm_mulVec_right hp.1]
      _ = ∫⁻ y, g (herm (Hpk k r) y zs) ∂((hypAmb k r T').map (fun v => p⁻¹ *ᵥ v)) :=
          (lintegral_map hgm hm).symm
      _ = _ := by rw [hypAmb_inv hk hT' (HU.uwb_inv hp)]
  set f : (Fin k → ℂ) × ℂ → ℝ≥0∞ := fun v => g (-((s : ℂ) * v.2)) with hf
  have hfm : Measurable f := hg.comp (continuous_const.mul continuous_snd).neg.measurable
  have step2 : ∫⁻ v, g (herm (Hpk k r) v zs) ∂hypAmb k r T' = hypMeas k T' f := by
    rw [hypMeas_eq k T' hfm, hypAmb, lintegral_map hgm continuous_opVec.measurable]
    refine lintegral_congr fun q => ?_
    have e : opVec k r q (wI k r (Fin.last k)) = q.2 := congrArg Prod.snd (opCo_opVec (r := r) q)
    rw [hzs, herm_wLast, e]
  set G : ℝ → ℂ → ℝ≥0∞ := fun _ c => g (-((s : ℂ) * c)) with hGdef
  have hGm : Measurable (Function.uncurry G) :=
    hg.comp (continuous_const.mul continuous_snd).neg.measurable
  have step3 := polarHyp k (Tz k r z) T' hk hT hT' G hGm
  rw [← hs] at step3
  have hcancel : ∀ ζ : ℂ, -((s : ℂ) * -(ζ / (s : ℂ))) = ζ := by
    intro ζ; field_simp
  have e3 : hypMeas k T' f =
      hypMeas k T' (fun v => G ‖(WithLp.equiv 2 (Fin k → ℂ)).symm v.1‖ v.2) := rfl
  rw [step1, step2, e3, step3]
  simp only [hGdef, hcancel]

theorem hypQ : RI.HypQ := by
  intro k r z z' hk hz hz' hT hT'
  refine ⟨hypAmb k r (Tz k r z'), hypAmb_sigmaFinite hT', fun s hs => hypAmb_inv hk hT' hs,
    hypAmb_conc hz' hT', ENNReal.ofReal (2 * Real.pi ^ k / (k - 1).factorial / (2 * Tz k r z ^ k)),
    ?_, ENNReal.ofReal_ne_top, fun g hg => hypAmb_polar hk hz hT hT' g hg⟩
  have := Real.pi_pos
  exact (ENNReal.ofReal_pos.2 (by positivity)).ne'

end GlobalTheory.HyperboloidPolar
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory

theorem two_le_rdE_and_arithmeticConditionsS0 : ∀ D : D7, 2 ≤ D.host.rdE ∧ ArithmeticConditionsOfDatum D := fun D =>
  ⟨S.root_discriminant_ge_two _ (UnusedSlot33.ramification_two_and_conjugation_at_q_and_d _),
    fun u => S.splitsCompl_of_ncard _ _ (D.mem u).A.T_prime
      (Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion.split_clause _ Formalism.L2.SG.ResidEvFree.cycSplit_holds _ (D.mem u).A.T_prime (S.level_norm_one_mod_conductor _ u)).2,
    Formalism.L2.SG.ResidEvFree.splitsE_g _ 0, Formalism.L2.SG.ResidEvFree.splitsE_g _ 1, S.discriminant_eq_base_sq _ (UnusedSlot33.ramification_two_and_conjugation_at_q_and_d _)⟩

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory

theorem exact_ranks_of_record : ∀ D : D7, (∀ i, StandardLattice.SplitsF D (D.host.g i)) → StandardLattice.volY0 D = StandardLattice.massI D D.R.r → StandardLattice.FactDstar D → (∀ u, (D.duS u : ℝ) = StandardLattice.duStarU D u * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f) → letI := D.host.cmStar; ∀ (V : Type) [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V] [IsScalarTower (𝓞 D.host.E) D.host.E V] (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E) (L : Submodule (𝓞 D.host.E) V), h.IsSymm → (Formalism.HermitianLatticesTheory.IsOrthoLattice h L D.R.k → ∀ u : D.what₂.Word, (D.duS u : ℝ) = Formalism.HermitianLatticesTheory.mass h L * (∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal ∨ ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal}, ∏ i ∈ Finset.Icc 1 D.R.k, ((Ideal.absNorm p.asIdeal : ℝ) ^ i - 1)) * (∏ τ, Formalism.MainNotions.S.vand (fun i : Fin D.R.k => (((D.hcW u τ).u i : ℚ) : ℝ)) / ∏ i ∈ Finset.range D.R.k, (i.factorial : ℝ)) * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f) ∧ (Formalism.HermitianLatticesTheory.IsOrthoLattice h L D.R.r → D.what₂.Dstar = Formalism.HermitianLatticesTheory.mass h L * (∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal ∨ ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal}, (∏ i ∈ Finset.range D.R.r, ((Ideal.absNorm p.asIdeal : ℝ) ^ D.R.r - (Ideal.absNorm p.asIdeal : ℝ) ^ i)) / ((Ideal.absNorm p.asIdeal : ℝ) ^ (D.R.rS * (2 * D.R.k + 2 * D.R.rS + 1)) * (Ideal.absNorm p.asIdeal : ℝ) ^ (D.R.k * (D.R.k - 1) / 2))) * ∏ τ, D.dsig τ) := by
  intro D hsp hvol hD hdu V _ _ _ _ h L hs
  letI := D.host.cmStar
  have hmass : ∀ n, Formalism.HermitianLatticesTheory.IsOrthoLattice h L n → Formalism.HermitianLatticesTheory.mass h L = StandardLattice.massI D n :=
    fun n ho => StandardLattice.mass_ortho D.host.E D.sp.cm.cmUnram n V h L ho
  have hcol := GlobalTheory.T.finprod_places_over_typePrimes_split D (fun x : ℝ => ∏ i ∈ Finset.Icc 1 D.R.k, (x ^ i - 1)) hsp
  have hrow := GlobalTheory.T.finprod_places_over_typePrimes_split D (fun x : ℝ => (∏ i ∈ Finset.range D.R.r, (x ^ D.R.r - x ^ i)) /
    (x ^ (D.R.rS * (2 * D.R.k + 2 * D.R.rS + 1)) * x ^ (D.R.k * (D.R.k - 1) / 2))) hsp
  beta_reduce at hcol hrow
  obtain ⟨hc0, hr0⟩ := GlobalTheory.T.localIndices_column_row_levels_exact D 0
  obtain ⟨hc1, hr1⟩ := GlobalTheory.T.localIndices_column_row_levels_exact D 1
  refine ⟨fun ho u => ?_, fun ho => ?_⟩
  · rw [hdu u, hmass _ ho, hcol]
    unfold StandardLattice.duStarU StandardLattice.duStarP StandardLattice.idxPi
    rw [hc0, hc1]
    rfl
  · rw [show D.what₂.Dstar = StandardLattice.DstarD D from hD, hmass _ ho, hrow]
    unfold StandardLattice.DstarD StandardLattice.DstarP StandardLattice.idxSig
    rw [hvol, hr0, hr1]

end GlobalTheory
end
