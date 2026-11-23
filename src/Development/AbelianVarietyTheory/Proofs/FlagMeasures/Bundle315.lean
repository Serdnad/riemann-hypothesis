module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle161
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle310
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnitaryEquivHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle283
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
public import Formalism.PeriodIntegrals.Bundle024
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatsDiscStable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle031
public import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle312
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle302
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle150
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle075
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle311
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle298
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle026
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle002

@[expose] public section

section

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.ThA

private lemma inv_mul_comm_of_mul_comm {n : Type*} [Fintype n] [DecidableEq n] (a h : Matrix n n ℂ)
    (hah : a * h = h * a) : h⁻¹ * a = a * h⁻¹ := by
  by_cases hh : IsUnit h.det
  · calc h⁻¹ * a = h⁻¹ * (a * h) * h⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hh, Matrix.mul_one]
      _ = h⁻¹ * (h * a) * h⁻¹ := by rw [hah]
      _ = a * h⁻¹ := by rw [← Matrix.mul_assoc h⁻¹ h a, Matrix.nonsing_inv_mul _ hh, Matrix.one_mul]
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ hh, Matrix.zero_mul, Matrix.mul_zero]

private lemma inv_mul_conj_mul_conj_eq_conj_of_commute {n : Type*} [Fintype n] [DecidableEq n] (a H M g M' H' : Matrix n n ℂ)
    (ha : IsUnit a.det) (c1 : a * H = H * a) (c2 : a * H' = H' * a) :
    H⁻¹ * (a * M * a⁻¹)⁻¹ * g * (a * M' * a⁻¹) * H' =
      a * (H⁻¹ * M⁻¹ * (a⁻¹ * g * a) * M' * H') * a⁻¹ := by
  have e1 : (a * M * a⁻¹)⁻¹ = a * M⁻¹ * a⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ ha, Matrix.mul_assoc]
  have d1 : H⁻¹ * a = a * H⁻¹ := inv_mul_comm_of_mul_comm a H c1
  have d2 : a⁻¹ * H' = H' * a⁻¹ := inv_mul_comm_of_mul_comm H' a c2.symm
  rw [e1]
  simp only [Matrix.mul_assoc]
  rw [d2, ← Matrix.mul_assoc H⁻¹ a, d1, Matrix.mul_assoc]

theorem besselJ_conj {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c c' : ℂ)
    (π : B.Mat k r → (Wp →L[ℂ] Wp)) (π' : B.Mat k r → (Wq →L[ℂ] Wq))
    (μW μN μW' : Measure (Mt k r)) [SFinite μW] [SFinite μN] [SFinite μW']
    (hW : μW (UWset k r z)ᶜ = 0) (hN : μN (Nset k r)ᶜ = 0) (hW' : μW' (UWset k r z')ᶜ = 0)
    (a : B.Mat k r) (ha : IsUnit a.det)
    (hc : ∀ h ∈ UWset k r z, a * h = h * a) (hc' : ∀ h ∈ UWset k r z', a * h = h * a)
    (hp : ∀ n ∈ Nset k r, psi k r z c (a * n * a⁻¹) = psi k r z c' n)
    (hp' : ∀ n ∈ Nset k r, psi k r z' c (a * n * a⁻¹) = psi k r z' c' n)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    besselJ k r z z' c π π' μW (μN.map (conjM a)) μW' F g =
      besselJ k r z z' c' π π' μW μN μW' (fun x => F (a * x * a⁻¹)) (a⁻¹ * g * a) := by
  have hm : Measurable (conjM (k := k) (r := r) a) := (BesselUnitaryEquiv.conjE (k := k) (r := r) a ha).measurable
  let E : Mt k r ≃ᵐ Mt k r := BesselUnitaryEquiv.conjE (k := k) (r := r) a ha
  let Φ : (Mt k r × Mt k r) × (Mt k r × Mt k r) ≃ᵐ (Mt k r × Mt k r) × (Mt k r × Mt k r) :=
    ((MeasurableEquiv.refl (Mt k r)).prodCongr E).prodCongr ((MeasurableEquiv.refl (Mt k r)).prodCongr E)
  have hpm : ∀ (ν : Measure (Mt k r)) [SFinite ν],
      (ν.prod μN).map (Prod.map id (conjM a)) = ν.prod (μN.map (conjM a)) := by
    intro ν _
    rw [← Measure.map_prod_map _ _ measurable_id hm, Measure.map_id]
  have hμ : (μW.prod (μN.map (conjM a))).prod (μW'.prod (μN.map (conjM a))) =
      ((μW.prod μN).prod (μW'.prod μN)).map Φ := by
    rw [← hpm μW, ← hpm μW', Measure.map_prod_map _ _ (measurable_id.prodMap hm) (measurable_id.prodMap hm)]
    rfl
  have aW : ∀ᵐ x ∂μW, x ∈ UWset k r z := ae_iff.2 hW
  have aN : ∀ᵐ x ∂μN, x ∈ Nset k r := ae_iff.2 hN
  have aW' : ∀ᵐ x ∂μW', x ∈ UWset k r z' := ae_iff.2 hW'
  have q1 : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)), p.1.1 ∈ UWset k r z :=
    (Measure.quasiMeasurePreserving_fst (μ := μW.prod μN) (ν := μW'.prod μN)).ae
      ((Measure.quasiMeasurePreserving_fst (μ := μW) (ν := μN)).ae aW)
  have q2 : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)), p.1.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst (μ := μW.prod μN) (ν := μW'.prod μN)).ae
      ((Measure.quasiMeasurePreserving_snd (μ := μW) (ν := μN)).ae aN)
  have q3 : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)), p.2.1 ∈ UWset k r z' :=
    (Measure.quasiMeasurePreserving_snd (μ := μW.prod μN) (ν := μW'.prod μN)).ae
      ((Measure.quasiMeasurePreserving_fst (μ := μW') (ν := μN)).ae aW')
  have q4 : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)), p.2.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_snd (μ := μW.prod μN) (ν := μW'.prod μN)).ae
      ((Measure.quasiMeasurePreserving_snd (μ := μW') (ν := μN)).ae aN)
  unfold besselJ
  rw [hμ, integral_map_equiv]
  refine integral_congr_ae ?_
  filter_upwards [q1, q2, q3, q4] with p h1 h2 h3 h4
  have hΦ : Φ p = ((p.1.1, conjM a p.1.2), (p.2.1, conjM a p.2.2)) := rfl
  have e2 : Matrix.of (conjM a p.1.2) = a * Matrix.of p.1.2 * a⁻¹ := rfl
  have e4 : Matrix.of (conjM a p.2.2) = a * Matrix.of p.2.2 * a⁻¹ := rfl
  rw [hΦ]
  dsimp only
  rw [e2, e4, hp (Matrix.of p.1.2) h2, hp' (Matrix.of p.2.2) h4,
    inv_mul_conj_mul_conj_eq_conj_of_commute a (Matrix.of p.1.1) (Matrix.of p.1.2) g (Matrix.of p.2.2) (Matrix.of p.2.1) ha
      (hc (Matrix.of p.1.1) h1) (hc' (Matrix.of p.2.1) h3)]

theorem besselJ_smul {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (π : B.Mat k r → (Wp →L[ℂ] Wp)) (π' : B.Mat k r → (Wq →L[ℂ] Wq))
    (μW μN μW' : Measure (Mt k r)) [SFinite μW] [SFinite μN] [SFinite μW'] (t : ℝ≥0∞)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    besselJ k r z z' c π π' μW (t • μN) μW' F g =
      ((t.toReal ^ 2 : ℝ) : ℂ) • besselJ k r z z' c π π' μW μN μW' F g := by
  unfold besselJ
  rw [Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_smul_left,
    Measure.prod_smul_right, smul_smul,
    integral_smul_measure, ENNReal.toReal_mul, ← pow_two, Complex.coe_smul]

theorem besselJ_changeFrame : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (Bs : B.RealPlaceData k r L.Wp L.Wq) (cN : ℝ) (F : B.Mat k r → (L.Wq →L[ℂ] L.Wp)), IsStdOf L μsec Bs → IsRatioN k r cN → L.c ≠ 0 → L.κN ≠ 0 → L.κN ≠ ⊤ → ∀ g : B.Mat k r, L.J F g = ((lamN L cN ^ 2 : ℝ) : ℂ) • B.JF Bs (conjF (cStd / L.c) F) ((aT k r (cStd / L.c))⁻¹ * g * aT k r (cStd / L.c)) := by
  intro k r L μsec Bs cN F hstd hR hc hκ0 hκT g
  obtain ⟨hz, hz', hπ, hπ', hμW, hμW', hμN, -⟩ := hstd
  have hα : cStd / L.c ≠ 0 := div_ne_zero (by simp [cStd]) hc
  have hcα : L.c * (cStd / L.c) = cStd := by field_simp
  set α := cStd / L.c with hαdef
  obtain ⟨-, hT, -, -⟩ := GlobalTheory.T.besselTorusElement_properties k r α hα
  obtain ⟨hcz, hnz⟩ := hT L.z L.hz.1
  obtain ⟨hcz', hnz'⟩ := hT L.z' L.hz'.1
  have hmap := GlobalTheory.T.lebesgue_rootCoordinates_map_besselTorus_conj k r α hα
  have ha : IsUnit (aT k r α).det := by
    rw [aT, Matrix.det_diagonal]
    refine isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
    split_ifs
    · exact pow_ne_zero _ hα
    · exact one_ne_zero
    · exact inv_ne_zero (pow_ne_zero _ (star_ne_zero.mpr hα))
  have hp : ∀ w : Fin (2 * r + k + 1) → ℂ,
      (∀ n ∈ Nset k r, ell k r w (aT k r α * n * (aT k r α)⁻¹) = α * ell k r w n) →
      ∀ n ∈ Nset k r, psi k r w L.c (aT k r α * n * (aT k r α)⁻¹) = psi k r w cStd n := by
    intro w hw n hn
    simp only [psi, hw n hn, ← mul_assoc, hcα]
  haveI : IsFiniteMeasure L.μW := ⟨by rw [L.hμW.2]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure L.μW' := ⟨by rw [L.hμW'.2]; exact ENNReal.one_lt_top⟩
  have hNc : (D.muN k r) (Nset k r)ᶜ = 0 := by rw [← hμN]; exact Bs.haarN.conc
  haveI : IsFiniteMeasureOnCompacts (D.muN k r) :=
    ⟨fun K hK => by rw [← hμN]; exact Bs.haarN.finite_compact K hK⟩
  have hW : L.μW (UWset k r L.z)ᶜ = 0 := L.hμW.1.2.2.1
  have hW' : L.μW' (UWset k r L.z')ᶜ = 0 := L.hμW'.1.2.2.1
  have hx : 0 < ‖α‖ ^ B.kap k r := pow_pos (norm_pos_iff.mpr hα) _
  have hone : ENNReal.ofReal (‖α‖ ^ B.kap k r) * ENNReal.ofReal ((‖α‖ ^ B.kap k r)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul hx.le, mul_inv_cancel₀ hx.ne', ENNReal.ofReal_one]
  have hLμN : L.μN = (L.κN * ENNReal.ofReal cN * ENNReal.ofReal (‖α‖ ^ B.kap k r)) •
      (D.muN k r).map (conjM (aT k r α)) := by
    rw [hmap, smul_smul, mul_assoc (L.κN * ENNReal.ofReal cN), hone, mul_one, mul_smul, ← hR.2]
    simp only [Formalism.MainNotions.S.LocBessel.μN, Formalism.MainNotions.S.haarLie, one_smul]
  have ht : (L.κN * ENNReal.ofReal cN * ENNReal.ofReal (‖α‖ ^ B.kap k r)).toReal = lamN L cN := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hR.1.le, ENNReal.toReal_ofReal hx.le]
    rfl
  have step : L.J F g = ((lamN L cN ^ 2 : ℝ) : ℂ) •
      besselJ k r L.z L.z' L.c L.π L.π' L.μW ((D.muN k r).map (conjM (aT k r α))) L.μW' F g := by
    rw [← ht]
    show besselJ k r L.z L.z' L.c L.π L.π' L.μW L.μN L.μW' F g = _
    rw [hLμN]
    exact besselJ_smul k r L.z L.z' L.c L.π L.π' L.μW _ L.μW' _ F g
  rw [step, besselJ_conj k r L.z L.z' L.c cStd L.π L.π' L.μW (D.muN k r) L.μW' hW hNc hW' (aT k r α) ha
    hcz hcz' (hp L.z fun n hn => (hnz n hn).2.2) (hp L.z' fun n hn => (hnz' n hn).2.2) F g,
    Formalism.FourierDecayAlt.B.JF, hz, hz', hπ, hπ', hμW, hμW', hμN]
  rfl

end GlobalTheory.ThA
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.AutInhab

noncomputable section

namespace GlobalTheory.PerpInst

theorem exists_drop {n : ℕ} (ε : Fin n → Bool) (k : Fin n) :
    ∃ (m : ℕ) (f : Fin m → Fin n), m + 1 = n ∧ Function.Injective f ∧ (∀ i, f i ≠ k) ∧
      ∀ b, (univ.filter fun a => ε (f a) = b).card + (if ε k = b then 1 else 0) =
        (univ.filter fun a => ε a = b).card := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := k.2; omega⟩
  refine ⟨m, k.succAbove, rfl, Fin.succAbove_right_injective, k.succAbove_ne, fun b => ?_⟩
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succAbove _ k, add_comm]

theorem hform_eq {E : Type} [Field E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (y x : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J y x = star y ⬝ᵥ (J *ᵥ x) := by
  simp [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc, starRingEnd_apply]

theorem form_mulVec {E : Type} [Field E] [StarRing E] {n : ℕ} (J G : Matrix (Fin n) (Fin n) E)
    (y x : Fin n → E) : star (G *ᵥ y) ⬝ᵥ (J *ᵥ (G *ᵥ x)) = star y ⬝ᵥ ((Gᴴ * J * G) *ᵥ x) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]

theorem hasSignature_all (I : AutInst) {P Q : ℕ} (h : HasSig I P Q) (φ : I.E →+* ℂ) :
    Formalism.UG.HasSignature (I.J.map φ) P Q := by
  have key : ∃ v, φ = I.φ v ∨ φ = ComplexEmbedding.conjugate (I.φ v) := by
    refine ⟨(InfinitePlace.mk φ).comap (algebraMap I.F I.E), ?_⟩
    rcases GlobalTheory.Count.Test.embedding_cases I (InfinitePlace.mk φ) with h | h <;>
      rcases InfinitePlace.embedding_mk_eq φ with h' | h'
    · exact Or.inl (h'.symm.trans h)
    · right
      rw [← h, h']; simp
    · exact Or.inr (h'.symm.trans h)
    · left
      exact star_injective (h'.symm.trans h)
  obtain ⟨v, rfl | rfl⟩ := key
  · rw [← (h v).1, ← (h v).2]; exact hasSignature_inst I v
  · rw [← (h v).1, ← (h v).2]
    refine hasSignature_of_frame (P := (I.P v).map (starRingEnd ℂ)) ((I.P_unit v).map (starRingEnd ℂ).mapMatrix) ?_
    have h1 := congrArg (fun M => Matrix.map M (starRingEnd ℂ)) (I.P_spec v)
    simp only [Matrix.map_mul] at h1
    have h2 : (Formalism.REAL.Jm (I.ε v)).map (starRingEnd ℂ) = Formalism.REAL.Jm (I.ε v) := by
      rw [Formalism.REAL.Jm, Matrix.diagonal_map (map_zero _)]
      congr 1
      funext a
      split_ifs <;> simp
    rw [h2] at h1
    exact h1

theorem exists_point (I : AutInst) (ε : Fin I.n → Bool) (γ : GL (Fin I.n) I.E)
    (hγ : (γ : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ * I.J * (γ : Matrix (Fin I.n) (Fin I.n) I.E) = signMat I.E ε) :
    ∃ xf : I.Gf, ∀ z, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ z ∈ lamX I (1, xf) ↔ z ∈ intLat I.E I.n := by
  set G : Matrix (Fin I.n) (Fin I.n) I.E := γ.val with hG
  have hsur : Function.Surjective G.mulVec := Matrix.mulVec_surjective_iff_isUnit.2 γ.isUnit
  have hinj : Function.Injective G.mulVec := Matrix.mulVec_injective_iff_isUnit.2 γ.isUnit
  let Λ : Submodule (𝓞 I.E) (Fin I.n → I.E) := (intLat I.E I.n).map (G.mulVecLin.restrictScalars (𝓞 I.E))
  have hΛ : ∀ z, G *ᵥ z ∈ Λ ↔ z ∈ intLat I.E I.n := fun z =>
    ⟨fun ⟨w, hw, e⟩ => (hinj e : w = z) ▸ hw, fun hz => ⟨z, hz, rfl⟩⟩
  obtain ⟨xf, hxf⟩ := GlobalTheory.T.exists_finiteAdelicPoint_lattice_eq_selfDual I Λ (Submodule.IsLattice.of_fg I.E ((intLat_fg _).map _)) (by
      intro x
      obtain ⟨x, rfl⟩ := hsur x
      rw [hΛ, intLat_dual ε]
      constructor
      · rintro h _ ⟨y, hy, rfl⟩
        have := h y hy
        rw [hform_eq, ← hγ, ← form_mulVec, ← hform_eq] at this
        exact this
      · intro h y hy
        have := h _ ((hΛ y).2 hy)
        rwa [hform_eq, form_mulVec, hγ, ← hform_eq] at this)
  exact ⟨xf, fun z => hxf ▸ hΛ z⟩

theorem exists_isPerpInst : ∀ (I : AutInst) (P Q : ℕ), HasSig I P Q → 3 ≤ I.n → ∀ s : Bool, (if s then 1 ≤ P else 1 ≤ Q) → ∃ (I' : AutInst) (e : I'.E ≃+* I.E) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E) (xf : I.Gf), IsPerpInst I I' e s x A xf ∧ HasSig I' (if s then P - 1 else P) (if s then Q else Q - 1) := by
  intro I P Q h _ s hs
  obtain ⟨v⟩ : Nonempty (InfinitePlace I.F) := inferInstance
  set ε := I.ε v with hε
  have hP : (univ.filter fun a => ε a = true).card = P := (h v).1
  have hQ : (univ.filter fun a => ε a = false).card = Q := (h v).2
  obtain ⟨k, hk⟩ : ∃ k, ε k = s := by
    have : 0 < (univ.filter fun a => ε a = s).card := by
      cases s
      · rw [hQ]; exact hs
      · rw [hP]; exact hs
    obtain ⟨k, hk⟩ := Finset.card_pos.1 this
    exact ⟨k, (Finset.mem_filter.1 hk).2⟩
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.hermitian_spaces_same_signature_isometric I.E I.cm.cmUnram I.n I.J (signMat I.E ε) I.J_herm (signMat_isHerm ε)
    I.J_det (signMat_det ε) ⟨I.L, Submodule.IsLattice.of_fg I.E I.L_fg, fun x => by simpa only [hform_eq] using I.L_dual x⟩
    ⟨intLat I.E I.n, Submodule.IsLattice.of_fg I.E (intLat_fg _), fun x => by simpa only [hform_eq] using intLat_dual ε x⟩
    (fun φ => ⟨P, Q, hasSignature_all I h φ, by
      rw [signMat_map, ← hP, ← hQ]
      exact hasSignature_of_frame (P := 1) isUnit_one (by simp)⟩)
  obtain ⟨xf, hxf⟩ := exists_point I ε γ hγ
  obtain ⟨m, f, hm, hf, hfk, hcard⟩ := exists_drop ε k
  set G : Matrix (Fin I.n) (Fin I.n) I.E := γ.val with hG
  let C : Matrix (Fin I.n) (Fin m) I.E := (1 : Matrix (Fin I.n) (Fin I.n) I.E).submatrix id f
  refine ⟨ofSigns I.cm (fun a => ε (f a)), RingEquiv.refl I.E, G *ᵥ Pi.single k 1, G * C, xf,
    ⟨fun _ => rfl, hm, ?_, ?_, ?_, ?_, ?_⟩, fun w => ⟨?_, ?_⟩⟩
  · rw [form_mulVec, hγ]
    simp [signMat, sgn, hk]
  · have : star (G *ᵥ Pi.single k 1) ᵥ* (I.J * (G * C)) = star (Pi.single k 1) ᵥ* ((Gᴴ * I.J * G) * C) := by
      rw [star_mulVec, vecMul_vecMul]; simp only [Matrix.mul_assoc]
    refine this.trans ?_
    rw [hγ]
    funext j
    simp [signMat, C, vecMul, dotProduct, Pi.single_apply, Matrix.one_apply, hfk j]
    rfl
  · have : (G * C)ᴴ * I.J * (G * C) = Cᴴ * (Gᴴ * I.J * G) * C := by
      rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    refine this.trans ?_
    rw [hγ]
    change _ = signMat I.E fun a => ε (f a)
    ext i j
    rw [Matrix.mul_apply]
    simp [signMat, C, Matrix.one_apply, Matrix.diagonal_apply, hf.eq_iff]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  · exact (hxf _).2 (Submodule.subset_span ⟨k, by simp⟩)
  · change ∀ y : Fin m → I.E, y ∈ intLat I.E m ↔ (G * C) *ᵥ y ∈ lamX I (1, xf)
    intro y
    rw [← mulVec_mulVec, hxf, mem_intLat, mem_intLat]
    constructor
    · intro hy i
      change ∑ j, C i j * y j ∈ _
      refine sum_mem fun j _ => mul_mem ?_ (hy j)
      simp only [C, submatrix_apply, id, Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · intro hy j
      have := hy (f j)
      simpa [C, mulVec, dotProduct, Matrix.one_apply, hf.eq_iff] using this
  · change (univ.filter fun a => ε (f a) = true).card = _
    have := hcard true
    rw [hP, hk] at this
    cases s <;> simp at this ⊢ <;> omega
  · change (univ.filter fun a => ε (f a) = false).card = _
    have := hcard false
    rw [hQ, hk] at this
    cases s <;> simp at this ⊢ <;> omega

end GlobalTheory.PerpInst
end
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianDoubleCoset_secondType_family_ampSq_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ β J βJ : ℕ, S.ampSq (S.InFF β J βJ) ≤ ENNReal.ofReal (98 * S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * S.Hp ^ (4 * (r + 1))) * ((S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3))) ^ 2) * S.nn := by
  first | exact @GlobalTheory.HL.FamilyBound.family_bound | exact GlobalTheory.HL.FamilyBound.family_bound | (intros; apply GlobalTheory.HL.FamilyBound.family_bound <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem range_cuspidal_of_lowKType : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h → HBig B 40 h → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ y : B.I.L2 B.μf B.fund, (∀ f : B.I.GA → ℂ, IsContRep B (T y) f → ∀ W, B.I.IsIsot W → ∀ ν : Measure B.I.GA, B.I.IsNQuotMeas W ν → ∀ x, ∫ m, f (m * x) ∂ν = 0) ∧ B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (T y)) := by
  intro B d h hD hK hh hL hB hF T hT y
  have hv := GlobalTheory.T.realUnipotent_integral_discreteSeries_vanish B d h hD hK hL hh
  exact GlobalTheory.T.cuspidal_of_unipotent_fibre_integrals_vanish B d h hD hv hL hB hF T hT y

end GlobalTheory.Dec
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.besselMatrixCoeff_extends_bounded_equivariant : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ v ∈ DD σ w, ∀ ξ : Wp, ∃ T : H → Mat k r → Wp, (∀ u ∈ DD σ w, T u = Afun (psiGen k r z c) π μS σ u v ξ) ∧ (∀ u u' : H, (fun x : Mt k r => T (u + u') (Matrix.of x)) =ᵐ[μG] fun x => T u (Matrix.of x) + T u' (Matrix.of x)) ∧ (∀ (b : ℂ) (u : H), (fun x : Mt k r => T (b • u) (Matrix.of x)) =ᵐ[μG] fun x => b • T u (Matrix.of x)) ∧ (∀ K : Set (Mt k r), IsCompact K → ∃ C : ℝ, ∀ u : H, AEStronglyMeasurable (fun x : Mt k r => T u (Matrix.of x)) (μG.restrict K) ∧ ∫⁻ x in K, (‖T u (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μG ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) ∧ (∀ y ∈ GG k r, ∀ u : H, (fun x : Mt k r => T (σ y u) (Matrix.of x)) =ᵐ[μG] fun x => T u (Matrix.of x * y)) ∧ (∀ s ∈ Sset k r z, ∀ u : H, (fun x : Mt k r => T u (s * Matrix.of x)) =ᵐ[μG] fun x => PiS (psiGen k r z c) π s (T u (Matrix.of x))) := by
  first | exact @GlobalTheory.SgInf.bessel_ext_bounded | exact GlobalTheory.SgInf.bessel_ext_bounded | (intros; apply GlobalTheory.SgInf.bessel_ext_bounded <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.lintegral_hsNormSq_matrixCoeff_le_formalDegree : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ ν : Measure (Mt k r), IsDis (Greg k r z z') μG μS μS' ν → ∀ (l : H → Wp) (l' : H → Wq), IsEll z (psiGen k r z c) π μS σ (DD σ w) l → IsEll z' (psiGen k r z' c') π' μS' σ (DD σ w) l' → ∫⁻ γ, ENNReal.ofReal (hsNormSq ((d : ℂ) • OO μG (fun x => l (σ x w)) (fun x => l' (σ x w)) (Matrix.of γ))) ∂ν ≤ ENNReal.ofReal d⁻¹ := by
  first | exact @GlobalTheory.SgInf.EllBound.lintegral_hsNormSq_ell_le | exact GlobalTheory.SgInf.EllBound.lintegral_hsNormSq_ell_le | (intros; apply GlobalTheory.SgInf.EllBound.lintegral_hsNormSq_ell_le <;> assumption)
end

section

open BranchingSupport BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory

theorem eigDec_of_isKFinCoefT_gap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (f : B.Mat k r → (Wq →L[ℂ] Wp)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → (haveI := FiniteDimensional.complete ℂ Wp; PI.CapelliEig.IsKFinCoefT (k := k) (r := r) R.σ f) → EigDec f (aOf r h - 1) mu := by
  intro hH k r ε mu h R Wp Wq _ _ _ _ _ _ f hDS hgap hok hf
  have := FiniteDimensional.complete ℂ Wp
  have := FiniteDimensional.complete ℂ Wq
  have hsm : PI.KFinSmooth := hH.1.1.2.2.1
  have hDG : R.IsDG ε mu := ⟨hDS.1, hDS.2, h, hgap, hok⟩
  obtain ⟨s, hs⟩ := (GlobalTheory.isCoef_of_translate_smul_exists hsm k r ε mu R Wp Wq (fun _ => 0) (fun _ => 0) hDS).1 f hf
  obtain ⟨h1, h2⟩ := Gp91.GlobalTheory.T.smooth_and_inCC_of_isCoef_of_gap hH.1 k r ε mu h R Wp Wq (fun _ => 0) (fun _ => 0) f s hDG hgap hok hs
  refine ⟨h1, h2, fun y g hg => ?_⟩
  have hE := GlobalTheory.CapelliEigenvalue.capEig hsm GlobalTheory.capelliDiscreteSeriesInfChar k r ε mu R.H R.σ Wp Wq hDS.1 hDS.2 f hf (y : ℂ) g hg
  rw [(GlobalTheory.ThA.centredCapelli_forms_agree k r _ (y : ℂ) f).1, hE]
  simp only [Formalism.QuantumDeterminants.capP, Complex.ofReal_prod, Complex.ofReal_add]

end GlobalTheory

end
end

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mass.Transp

theorem orbSum_img : ∀ (K V V' : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K) (e : V ≃ₗ[K] V'), (∀ x y, h' (e x) (e y) = h x y) → ∀ φ : Submodule (𝓞 K) V' → ℝ≥0∞, (∀ (s : Formalism.HermitianLatticesTheory.isom h') (M : Submodule (𝓞 K) V'), φ (s • M) = φ M) → ∀ L : Submodule (𝓞 K) V, (∀ (s : Formalism.HermitianLatticesTheory.isom h) (M : Submodule (𝓞 K) V), φ (GlobalTheory.Mass.Transp.img e (s • M)) = φ (GlobalTheory.Mass.Transp.img e M)) ∧ (∀ M : Submodule (𝓞 K) V, GlobalTheory.Mass.Transp.img e M ∈ Formalism.HermitianLatticesTheory.genus h' (GlobalTheory.Mass.Transp.img e L) ↔ M ∈ Formalism.HermitianLatticesTheory.genus h L) ∧ GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom h') (Formalism.HermitianLatticesTheory.genus h' (GlobalTheory.Mass.Transp.img e L)) φ = GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom h) (Formalism.HermitianLatticesTheory.genus h L) (fun M => φ (GlobalTheory.Mass.Transp.img e M)) := by
  intro K V V' _ _ _ _ _ _ _ _ _ _ _ h h' e he φ hφ L
  have hinv : ∀ (s : Formalism.HermitianLatticesTheory.isom h) (M : Submodule (𝓞 K) V),
      φ (GlobalTheory.Mass.Transp.img e (s • M)) = φ (GlobalTheory.Mass.Transp.img e M) := by
    intro s M
    have hs := img_smul (R := 𝓞 K) e he s M
    erw [hs, hφ]
  have hgen : ∀ M : Submodule (𝓞 K) V,
      GlobalTheory.Mass.Transp.img e M ∈ Formalism.HermitianLatticesTheory.genus h' (GlobalTheory.Mass.Transp.img e L) ↔ M ∈ Formalism.HermitianLatticesTheory.genus h L := by
    intro M
    constructor
    · intro hM
      have := genus_img e.symm (symm_isom e he) _ _ hM
      rwa [img_symm_img, img_symm_img] at this
    · exact genus_img e he L M
  refine ⟨hinv, hgen, ?_⟩
  symm
  refine GlobalTheory.Mass.OrbTransport.main _ _ _ _ (conj e he) (img e) _ _ φ (genus_stable _) (genus_stable _) ?_
    (fun g x _ => img_smul e he g x) hφ
  refine ⟨fun M hM => (hgen M).2 hM, fun a _ b _ hab => ?_, fun M hM => ⟨img e.symm M, ?_, img_img_symm e M⟩⟩
  · rw [← img_symm_img e a, hab, img_symm_img]
  · rw [← hgen, img_img_symm]; exact hM

end GlobalTheory.Mass.Transp
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.mass_genus_cyclicDiscriminant_splitPrime : MaxMass → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → 1 ≤ Module.finrank K V → ∀ (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h' : V' →ₗ⋆[K] V' →ₗ[K] K), h'.IsSymm → ∀ I : Submodule (𝓞 K) V', IsOrthoLattice h' I (Module.finrank K V) → ∀ T : ℕ, T.Prime → (∀ P : Ideal (𝓞 K), P.IsMaximal → (T : 𝓞 K) ∈ P → Ideal.absNorm P = T ∧ (T : 𝓞 K) ∉ P ^ 2) → ∀ L : Submodule (𝓞 K) V, IsIntLat h L → Nonempty ((↥(dual h L) ⧸ L.comap (dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) → mass h L = mass h' I * (((T : ℝ) ^ Module.finrank K V - 1) / ((T : ℝ) - 1)) ^ fDeg K := by
  first | exact @GlobalTheory.Mass.CyclicDisc.main | exact GlobalTheory.Mass.CyclicDisc.main | (intros; apply GlobalTheory.Mass.CyclicDisc.main <;> assumption)
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.mass_integralLattices_discriminantOrder_le : MaxMass → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → 1 ≤ Module.finrank K V → ∀ (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h' : V' →ₗ⋆[K] V' →ₗ[K] K), h'.IsSymm → ∀ I : Submodule (𝓞 K) V', IsOrthoLattice h' I (Module.finrank K V) → ∀ n : ℕ, 1 ≤ n → orbMass (isom h) (latsDisc (R := 𝓞 K) h n) ≤ ENNReal.ofReal (mass h' I * (n : ℝ) ^ (((Module.finrank K V : ℝ) + Real.logb 2 (Module.finrank ℚ K)) / 2)) := by
  first | exact @GlobalTheory.Mass.SpaceMass.main | exact GlobalTheory.Mass.SpaceMass.main | (intros; apply GlobalTheory.Mass.SpaceMass.main <;> assumption)
end
