module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalInterConjugateClosedUnimodular
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsFolnerUWset
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle185
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle186
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle243
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle237
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle155
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle031
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle238
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianMovesTotalMeasureEstimates
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle006
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle239
import Formalism.FormalDegreeBessel.FinalG
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle042
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle271
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle021
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.StabMeas

variable {k r : ℕ}

theorem cont_conj (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) :=
  (continuous_const.matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const

theorem cont_lmul (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) :=
  continuous_const.matrix_mul (continuous_id (X := Mat k r))

theorem meas_conj (a : Mat k r) : Measurable (conjM a : Mt k r → Mt k r) :=
  (cont_conj a).measurable

theorem meas_lmul (a : Mat k r) : Measurable (lmulM a : Mt k r → Mt k r) :=
  (cont_lmul a).measurable

theorem conj_conj (a b : Mat k r) : (conjM a : Mt k r → Mt k r) ∘ conjM b = conjM (a * b) := by
  funext x
  show a * (b * Matrix.of x * b⁻¹) * a⁻¹ = a * b * Matrix.of x * (a * b)⁻¹
  rw [Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]

theorem conj_one (x : Mt k r) : conjM 1 x = x := by
  show (1 : Mat k r) * Matrix.of x * 1⁻¹ = Matrix.of x
  simp

theorem map_conj_conj (a b : Mat k r) (μ : Measure (Mt k r)) :
    (μ.map (conjM b)).map (conjM a) = μ.map (conjM (a * b)) := by
  rw [Measure.map_map (meas_conj a) (meas_conj b), conj_conj]

def conjEquiv {a : Mat k r} (ha : IsUnit a.det) : Mt k r ≃ᵐ Mt k r where
  toFun := conjM a
  invFun := conjM a⁻¹
  left_inv x := by
    have := congrFun (conj_conj a⁻¹ a) x
    rw [Matrix.nonsing_inv_mul _ ha, conj_one] at this
    exact this
  right_inv x := by
    have := congrFun (conj_conj a a⁻¹) x
    rw [Matrix.mul_nonsing_inv _ ha, conj_one] at this
    exact this
  measurable_toFun := meas_conj a
  measurable_invFun := meas_conj a⁻¹

theorem conj_back {a : Mat k r} (ha : IsUnit a.det) (s : Mat k r) : a * (a⁻¹ * s * a) * a⁻¹ = s := by
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv _ ha, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ ha]

theorem haar_conj {a : Mat k r} (ha : IsUnit a.det) {S S' : Set (Mat k r)} (hS : ∀ x, a * x * a⁻¹ ∈ S' ↔ x ∈ S)
    {μ : Measure (Mt k r)} (h : IsHaarOn S μ) (h' : IsUnimod S μ) :
    IsHaarOn S' (μ.map (conjM a)) ∧ IsUnimod S' (μ.map (conjM a)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨h5, h6⟩ := h'
  have hb : ∀ s ∈ S', a⁻¹ * s * a ∈ S := fun s hs => (hS _).1 (by rwa [conj_back ha])
  refine ⟨⟨?_, ?_, ?_, fun s hs => ?_⟩, fun s hs => ?_, ?_⟩
  · exact (conjEquiv ha).measurableEmbedding.sigmaFinite_map
  · intro h0
    exact h2 ((Measure.map_eq_zero_iff (meas_conj a).aemeasurable).1 h0)
  · have := (conjEquiv ha).map_apply (μ := μ) {x | Matrix.of x ∉ S'}
    refine this.trans ?_
    rw [← h3]
    congr 1
    ext x
    exact not_congr (hS (Matrix.of x))
  · conv_rhs => rw [← h4 _ (hb s hs)]
    rw [Measure.map_map (meas_lmul _) (meas_conj a), Measure.map_map (meas_conj a) (meas_lmul _)]
    congr 1
    funext x
    show s * (a * Matrix.of x * a⁻¹) = a * (a⁻¹ * s * a * Matrix.of x) * a⁻¹
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ ha]
  · conv_rhs => rw [← h5 _ (hb s hs)]
    rw [Measure.map_map (continuous_rmulM _).measurable (meas_conj a),
      Measure.map_map (meas_conj a) (continuous_rmulM _).measurable]
    congr 1
    funext x
    show (a * Matrix.of x * a⁻¹) * s = a * (Matrix.of x * (a⁻¹ * s * a)) * a⁻¹
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ ha, Matrix.mul_one]
  · conv_rhs => rw [← h6]
    rw [Measure.map_map measurable_invM (meas_conj a), Measure.map_map (meas_conj a) measurable_invM]
    congr 1
    funext x
    show (a * Matrix.of x * a⁻¹)⁻¹ = a * (Matrix.of x)⁻¹ * a⁻¹
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ ha, Matrix.mul_assoc]

theorem haar_smul {S : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn S μ) (h' : IsUnimod S μ) {s : ℝ} (hs : 0 < s) :
    IsHaarOn S (ENNReal.ofReal s • μ) ∧ IsUnimod S (ENNReal.ofReal s • μ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨h5, h6⟩ := h'
  refine ⟨⟨?_, ?_, ?_, fun s hs => ?_⟩, fun s hs => ?_, ?_⟩
  · exact inferInstanceAs (SigmaFinite (s.toNNReal • μ))
  · intro h0
    have := congrArg (fun m : Measure (Mt k r) => m Set.univ) h0
    simp only [Measure.smul_apply, smul_eq_mul, Measure.coe_zero, Pi.zero_apply, mul_eq_zero,
      ENNReal.ofReal_eq_zero, Measure.measure_univ_eq_zero] at this
    rcases this with h | h
    · exact absurd h (not_le.2 hs)
    · exact h2 h
  · rw [Measure.smul_apply, h3, smul_zero]
  · rw [Measure.map_smul _ (meas_lmul s).aemeasurable, h4 s hs]
  · rw [Measure.map_smul _ (continuous_rmulM s).measurable.aemeasurable, h5 s hs]
  · rw [Measure.map_smul _ measurable_invM.aemeasurable, h6]

theorem isClosedSub_Rset {γ : Mat k r} (hγ : γ ∈ GG k r) : IsClosedSub k r (Rset k r γ) := by
  apply _root_.GlobalTheory.UnipUnimod.isClosedSub_Rset <;> assumption

theorem conj_mem_Nset {n : Mat k r} (hn : n ∈ Nset k r) (x : Mat k r) : n * x * n⁻¹ ∈ Nset k r ↔ x ∈ Nset k r := by
  obtain ⟨n1, -, -, n4, n5⟩ := isClosedSub_Nset (k := k) (r := r)
  have hu := isUnit_det_of_mem_GG (n1 hn)
  refine ⟨fun h => ?_, fun h => n4 _ (n4 _ hn _ h) _ (n5 _ hn)⟩
  convert n4 _ (n4 _ (n5 _ hn) _ h) _ hn using 1
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul _ hu, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left _ _ hu]

theorem conj_mem_Rset {n₁ n₂ : Mat k r} (h₁ : n₁ ∈ Nset k r) (h₂ : n₂ ∈ Nset k r) (g x : Mat k r) :
    n₂⁻¹ * x * n₂⁻¹⁻¹ ∈ Rset k r (n₁ * g * n₂) ↔ x ∈ Rset k r g := by
  have hu := isUnit_det_of_mem_GG (isClosedSub_Nset.1 h₂)
  have e : n₁ * g * n₂ * (n₂⁻¹ * x * n₂⁻¹⁻¹) * (n₁ * g * n₂)⁻¹ = n₁ * (g * x * g⁻¹) * n₁⁻¹ := by
    rw [Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hu, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  show (_ ∧ _) ↔ (_ ∧ _)
  rw [e, conj_mem_Nset h₁, conj_mem_Nset (isClosedSub_Nset.2.2.2.2 _ h₂)]

theorem dmin_N {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') {n₁ n₂ : Mat k r}
    (h₁ : n₁ ∈ Nset k r) (h₂ : n₂ ∈ Nset k r) (g : Mat k r) (l : Fin (r + 2)) :
    Dmin k r z z' (n₁ * g * n₂) l = Dmin k r z z' g l :=
  Formalism.QuantumDeterminants.dInv k r z z' hz hz' n₁ ⟨1, (isClosedSub_UWset z).2.2.1, n₁, h₁, (Matrix.one_mul _).symm⟩
    n₂ ⟨1, (isClosedSub_UWset z').2.2.1, n₂, h₂, (Matrix.one_mul _).symm⟩ g l

theorem stabilizer_measure_normalisation : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (γ : Mat k r) (s : ℝ) (μR : Measure (Mt k r)), 0 < s → IsNormalFormStabilizerMeasure k r hj z z' γ s μR → γ ∈ GG k r ∧ IsClosedSub k r (Rset k r γ) ∧ IsHaarOn (Rset k r γ) μR ∧ IsUnimod (Rset k r γ) μR ∧ IsNormalFormStabilizerMeasure k r hj z' z γ⁻¹ s (μR.map (conjM γ)) ∧ 0 < Dj k r hj z z' γ ∧ Dj k r hj z' z γ⁻¹ = Dj k r hj z z' γ ∧ ∀ De, DeOK k r z z' γ De → DeOK k r z' z γ⁻¹ De := by
  rintro k r j hj z z' γ s μR hs ⟨hz, hz', hT, n₁, h₁, n₂, h₂, g₀, β, c, hg, rfl, rfl⟩
  obtain ⟨n1, -, -, n4, n5⟩ := isClosedSub_Nset (k := k) (r := r)
  obtain ⟨a1, -, a3, a4, -, a6, -⟩ := GlobalTheory.T.normalFormFlagZero_middle_inverse_minor_orthogonal k r j hj z z' g₀ β c hz hz' hT hg
  obtain ⟨b1, b2⟩ := GlobalTheory.T.stabilizer_haar_unimodular_normal k r j hj z z' g₀ β c hz hz' hT hg
  have c1 := GlobalTheory.T.map_conj_lebesgueCommonStabilizerNormalForm k r j hj z z' g₀ β c hz hz' hT hg
  have hγ : n₁ * g₀ * n₂ ∈ GG k r :=
    isClosedSub_GG.2.2.2.1 _ (isClosedSub_GG.2.2.2.1 _ (n1 h₁) _ hg.1) _ (n1 h₂)
  have hinv : (n₁ * g₀ * n₂)⁻¹ = n₂⁻¹ * g₀⁻¹ * n₁⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]
  obtain ⟨d1, d2⟩ := haar_smul b1 b2 hs
  obtain ⟨e1, e2⟩ := haar_conj (isUnit_det_of_mem_GG (n1 (n5 _ h₂))) (conj_mem_Rset h₁ h₂ g₀) d1 d2
  have hD : ∀ l, ‖Dmin k r z' z (n₁ * g₀ * n₂)⁻¹ l‖ = ‖Dmin k r z z' (n₁ * g₀ * n₂) l‖ := fun l => by
    rw [hinv, dmin_N hz' hz (n5 _ h₂) (n5 _ h₁), dmin_N hz hz' h₁ h₂, a6]
  refine ⟨hγ, isClosedSub_Rset hγ, e1, e2,
    ⟨hz', hz, a1 ▸ hT, n₂⁻¹, n5 _ h₂, n₁⁻¹, n5 _ h₁, g₀⁻¹, β, c⁻¹, a3, hinv, ?_⟩, ?_, hD _, fun De h => ⟨h.1, ?_⟩⟩
  · rw [map_conj_conj, Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_det_of_mem_GG (n1 h₂)), ← map_conj_conj,
      Measure.map_smul _ (meas_conj g₀).aemeasurable, c1, Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem_GG (n1 h₁))]
  · unfold Dj at a4 ⊢
    rwa [dmin_N hz hz' h₁ h₂]
  · intro l hl h0
    rw [hD]
    refine h.2 l hl fun h' => h0 ?_
    rw [← norm_eq_zero, hD, h', norm_zero]

end GlobalTheory.Amp.StabMeas
end
end

section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.lintegral_hermitianNormFibre_dilation : ∀ (P Q : ℕ) (fib : ℝ → Measure (Sp P Q)) (β t : ℝ), IsDxDq fib → β ≠ 0 → 0 < t → ∀ φ : Sp P Q → ℝ≥0∞, Measurable φ → ∫⁻ y, φ y ∂(fib (t * β)) = ENNReal.ofReal (t ^ (P + Q) / t) * ∫⁻ y, φ (Real.sqrt t • y) ∂(fib β) := by
  first | exact @GlobalTheory.FibreScaling.lintegral_fibre_scale | exact GlobalTheory.FibreScaling.lintegral_fibre_scale | (intros; apply GlobalTheory.FibreScaling.lintegral_fibre_scale <;> assumption)
end

section

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

theorem _root_.GlobalTheory.T.subquotient_covering_radius_real_places : ∀ (I : AutInst) (x : I.GA) (A S R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (lo hi : ℝ), A.FG → IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) A S → R.FG → 0 < lo → 0 < hi → (∀ N, S < N → N ≤ A → lo ≤ sizeQ (bas I) (frm I x) N S) → largestSize (bas I) (frm I x) R ≤ hi → ∀ T : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ, (∀ v, ∀ y ∈ S, T v *ᵥ (fun i => I.φ v (y i)) = 0) → (∀ v, ∀ y ∈ A, T v *ᵥ (fun i => I.φ v (y i)) ∈ spanAt I R v) → ∃ Φ : Matrix (Fin I.n) (Fin I.n) I.E, (∀ y ∈ S, Φ *ᵥ y = 0) ∧ (∀ y ∈ A, Φ *ᵥ y ∈ R) ∧ ∃ D : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ, (∀ v, ∀ u ∈ spanAt I A v, D v *ᵥ u = (T v - Φ.map (I.φ v)) *ᵥ u) ∧ normAt I x D ≤ ((rkK A : ℝ) - rkK S) * rkK R * Real.sqrt I.f * I.rd * hi / (2 * lo) := by
  first | exact @GlobalTheory.Count.SubquotFrame.subquot_frame | exact GlobalTheory.Count.SubquotFrame.subquot_frame | (intros; apply GlobalTheory.Count.SubquotFrame.subquot_frame <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

theorem _root_.GlobalTheory.T.term_datum_orbit_unique : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → ∀ (d d' : Datum P) (t : Term V M r), Over P d t → Over P d' t → Datum.Rel d d' := by
  first | exact @GlobalTheory.LocOver.orbit_over_unique | exact GlobalTheory.LocOver.orbit_over_unique | (intros; apply GlobalTheory.LocOver.orbit_over_unique <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

theorem _root_.GlobalTheory.T.unitriangular_change_frame_unipotent : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f)), ∀ A : Matrix (Fin (r + 1)) (Fin (r + 1)) E, Uni A → (∀ a b, A a b ∈ M.L.O) → ∃ n ∈ Fr.N, (∀ c : Fin r, n (Fr.f c.castSucc) = ∑ a, A a c.castSucc • Fr.f a) ∧ n (Fr.f (Fin.last r)) = Fr.f (Fin.last r) ∧ img n (Fr.LamStd L) = Fr.LamStd L := by
  first | exact @GlobalTheory.LocOver.UnipLevi.levi_integral | exact GlobalTheory.LocOver.UnipLevi.levi_integral | (intros; apply GlobalTheory.LocOver.UnipLevi.levi_integral <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordHeight

section Val

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)
  (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ)
include hϖ

theorem vE_one : vE L ϖ (algebraMap F E 1) = 0 := by
  have h := (GlobalTheory.UnramVal.vE_valuation L ϖ hϖ).1 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  omega

theorem vE_unit (x : F) (hx : x ≠ 0) (h1 : algebraMap F E x ∈ L.O)
    (h2 : ∃ y ∈ L.O, algebraMap F E x * y = 1) : vE L ϖ (algebraMap F E x) = 0 := by
  obtain ⟨hadd, -, hint, -⟩ := GlobalTheory.UnramVal.vE_valuation L ϖ hϖ
  obtain ⟨-, -, -, -, hO, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  obtain ⟨y, hy, hxy⟩ := h2
  have e : y = algebraMap F E x⁻¹ := by
    calc y = algebraMap F E (x⁻¹ * x) * y := by rw [inv_mul_cancel₀ hx, map_one, one_mul]
      _ = algebraMap F E x⁻¹ := by rw [map_mul, mul_assoc, hxy, mul_one]
  have a1 := (hint x hx).2 ((hO x).1 h1)
  have a2 := (hint x⁻¹ (inv_ne_zero hx)).2 ((hO _).1 (e ▸ hy))
  have a3 := hadd x x⁻¹ hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, vE_one L ϖ hϖ] at a3
  omega

theorem vE_pow (x : F) (hx : x ≠ 0) (n : ℕ) :
    vE L ϖ (algebraMap F E (x ^ n)) = n * vE L ϖ (algebraMap F E x) := by
  induction n with
  | zero => simpa using vE_one L ϖ hϖ
  | succ n ih =>
    rw [pow_succ, (GlobalTheory.UnramVal.vE_valuation L ϖ hϖ).1 _ _ (pow_ne_zero n hx) hx, ih]
    push_cast
    ring

theorem vE_neg_one : vE L ϖ (algebraMap F E (-1)) = 0 := by
  have h := vE_pow L ϖ hϖ (-1) (by simp) 2
  rw [neg_one_sq, vE_one L ϖ hϖ] at h
  omega

omit [IsNonarchimedeanLocalField F] [CharZero F] hϖ in
theorem norm_mem (x : E) (hx : IsUnit x) : ∃ c : F, c ≠ 0 ∧ x * L.cj x = algebraMap F E c := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)
  obtain ⟨c, hc⟩ := (L.cj_fix (x * L.cj x)).1 (by rw [map_mul, L.cj_cj, mul_comm])
  refine ⟨c, ?_, hc.symm⟩
  rintro rfl
  rw [map_zero] at hc
  exact (hx.mul (hx.map L.cj)).ne_zero hc.symm

end Val

section Transport

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)
include c

theorem Dm_eq (l : Fin (r + 2)) : P.Dm l = S.D l := by
  have hZ : H.Zhat P.A.f P.B.f = S.Zh := by
    ext a b
    simp only [HermSp.Zhat, Frames.Zh, Matrix.of_apply, c.f_eq, c.f'_eq, c.h_eq]
  unfold LocNG.FPair.Dm HermSp.Dl Frames.D lead
  rw [dite_eq_left (Nat.lt_succ_iff.mp l.2), hZ]

theorem Gv_eq : P.Gv = S.G := by
  have h1 := Dm_eq c (Fin.last (r + 1))
  have h2 := Dm_eq c (Fin.last r).castSucc
  unfold LocNG.FPair.Gv HermSp.Gdet HermSp.normE Frames.G
  rw [← h1, ← h2, c.T_eq, c.T'_eq]
  rfl

theorem theta_eq : LocNG.theta M = S.th := by
  unfold LocNG.theta Frames.th
  cases h : M.split with
  | none => simp [c.gg_none h]
  | some g =>
    obtain ⟨h1, h2⟩ := c.gg_some g h
    simp [h1, h2]

end Transport

theorem height_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), P.Hp = S.Hp ∧ LocNG.qF F = S.q ∧ (P.PrimeTo → S.gg = false ∧ vE M.L S.ϖ S.G = 0 ∧ ∀ l, S.D l ≠ 0 → vE M.L S.ϖ (S.D l * M.L.cj (S.D l)) = 0) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c
  have := hM.loc
  have := hM.char0
  obtain ⟨hq, hmod⟩ := GlobalTheory.BaseModule.modK_algebraMap M hM S.ϖ S.ϖ_irr
  obtain ⟨-, -, ⟨g, hg0, hg⟩, -, hD, hth, -⟩ := GlobalTheory.FrameBasic.main M.L r k S
  obtain ⟨hadd, hvp, -, -⟩ := GlobalTheory.UnramVal.vE_valuation M.L S.ϖ S.ϖ_irr
  obtain ⟨-, hcj, -, -, -, -, hq2, -⟩ := GlobalTheory.UnramOrder.order_facts M.L S.ϖ S.ϖ_irr
  have hnt : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [M.L.rank]; norm_num)
  have hgram := GlobalTheory.det_gram_frame_generators M hM H r k P
  rw [theta_eq c, Gv_eq c, hg] at hgram
  have hvth : vE M.L S.ϖ (algebraMap F E S.th) = S.vth := by
    unfold Frames.th Frames.vth
    split_ifs
    · exact hvp
    · exact vE_one M.L S.ϖ S.ϖ_irr
  have hends : ∀ l : Fin (r + 2), (l : ℕ) ∈ P.ends ↔ l ≠ 0 ∧ S.D l ≠ 0 := by
    intro l
    unfold LocNG.FPair.ends
    simp only [Finset.mem_filter, Finset.mem_range]
    rw [Dm_eq c]
    constructor
    · rintro ⟨-, h1, h2⟩
      refine ⟨?_, h2.ne_zero⟩
      rintro rfl
      simp at h1
    · rintro ⟨h1, h2⟩
      refine ⟨l.2, ?_, hD l h2⟩
      exact Nat.one_le_iff_ne_zero.mpr fun h => h1 (Fin.ext h)
  refine ⟨?_, hq, ?_⟩
  · have hq0 : (0 : ℝ) < (resQ S.ϖ : ℝ) := by
      have : 0 < resQ S.ϖ := by omega
      exact_mod_cast this
    set d : F := (-1) ^ (r + 1) * g * (S.th ^ (2 * (r + 1)))⁻¹ with hd
    have hp0 : S.th ^ (2 * (r + 1)) ≠ 0 := pow_ne_zero _ hth
    have hs0 : ((-1 : F) ^ (r + 1)) ≠ 0 := pow_ne_zero _ (by simp)
    have hd0 : d ≠ 0 := mul_ne_zero (mul_ne_zero hs0 hg0) (inv_ne_zero hp0)
    have hdet : (H.gram P.MMgen).det = algebraMap F E d := by
      calc (H.gram P.MMgen).det
          = (H.gram P.MMgen).det * algebraMap F E (S.th ^ (2 * (r + 1)) * (S.th ^ (2 * (r + 1)))⁻¹) := by
            rw [mul_inv_cancel₀ hp0, map_one, mul_one]
        _ = algebraMap F E d := by
            rw [map_mul, ← mul_assoc, map_pow, hgram, hd]
            simp only [map_mul, map_pow, map_neg, map_one]
    have hva : vE M.L S.ϖ (algebraMap F E d) = S.a := by
      have e : d * S.th ^ (2 * (r + 1)) = (-1) ^ (r + 1) * g := by
        rw [hd, mul_assoc, inv_mul_cancel₀ hp0, mul_one]
      have h1 := hadd _ _ hd0 hp0
      rw [e, hadd _ _ hs0 hg0, vE_pow M.L S.ϖ S.ϖ_irr _ hth, vE_pow M.L S.ϖ S.ϖ_irr _ (by simp),
        vE_neg_one M.L S.ϖ S.ϖ_irr, hvth] at h1
      unfold Frames.a
      rw [hg]
      push_cast at h1
      linarith
    have hprod : ∏ l ∈ P.ends, M.modK (P.Dm l * M.L.cj (P.Dm l)) = (resQ S.ϖ : ℝ) ^ (-(2 * S.vD)) := by
      have hsub : P.ends ⊆ Finset.range (r + 2) := by
        unfold LocNG.FPair.ends
        exact @Finset.filter_subset _ _ (_) _
      rw [← Finset.inter_eq_right.mpr hsub, ← Finset.prod_ite_mem, Finset.prod_range]
      unfold Frames.vD
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      have hz : ∀ (s : Finset (Fin (r + 2))) (f : Fin (r + 2) → ℤ),
          (resQ S.ϖ : ℝ) ^ (∑ i ∈ s, f i) = ∏ i ∈ s, (resQ S.ϖ : ℝ) ^ f i := by
        intro s f
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hq0.ne', ih]
      rw [hz]
      refine Finset.prod_congr rfl fun l _ => ?_
      by_cases hl : l ≠ 0 ∧ S.D l ≠ 0
      · rw [if_pos ((hends l).2 hl), if_pos hl, Dm_eq c]
        obtain ⟨n, hn0, hn⟩ := norm_mem M.L _ (hD l hl.2)
        rw [hn, hmod n hn0]
      · rw [if_neg (fun h => hl ((hends l).1 h)), if_neg hl]
        simp
    unfold LocNG.FPair.Hp Frames.Hp Frames.q
    rw [hprod, hdet, theta_eq c, hmod _ hth, hmod _ hd0, hvth, hva, ← zpow_add₀ hq0.ne',
      ← zpow_add₀ hq0.ne', ← Real.rpow_intCast, ← Real.rpow_mul hq0.le, ← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  · rintro ⟨h1, h2, h3⟩
    refine ⟨c.gg_none h1, ?_, fun l hl => ?_⟩
    · rw [Gv_eq c, hg] at h2
      rw [hg]
      exact vE_unit M.L S.ϖ S.ϖ_irr g hg0 h2.1 h2.2
    · have hu : LocNG.IsUnitO M (S.D l) := by
        by_cases h0 : l = 0
        · have : S.D l = 1 := by
            subst h0
            unfold Frames.D lead
            exact Matrix.det_isEmpty (n := Fin 0)
          rw [this]
          exact ⟨M.L.O.one_mem, 1, M.L.O.one_mem, mul_one 1⟩
        · have := h3 l ((hends l).2 ⟨h0, hl⟩)
          rwa [Dm_eq c] at this
      obtain ⟨n, hn0, hn⟩ := norm_mem M.L _ (hD l hl)
      obtain ⟨hm, y, hy, hxy⟩ := hu
      rw [hn]
      refine vE_unit M.L S.ϖ S.ϖ_irr n hn0 ?_ ⟨y * M.L.cj y, M.L.O.mul_mem hy (hcj y hy).1, ?_⟩
      · rw [← hn]
        exact M.L.O.mul_mem hm (hcj _ hm).1
      · rw [← hn, mul_mul_mul_comm, ← map_mul, hxy, map_one, mul_one]

end GlobalTheory.HL.CoordHeight
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianFramePair_tsum_reps_eq_const_mul_orbits : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), ∀ (R : LocNG.Reps P) (d0 : LocNG.Datum P), ∃ κ : ℝ, 0 ≤ κ ∧ ∀ φ : S.Datum → ℝ≥0∞, (∀ h ∈ S.H0, ∀ δ, φ (h • δ) = φ δ) → (∀ δ, (¬ ∃ Λ, S.IsTerm δ Λ) → φ δ = 0) → (∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * φ (c.dat d.1)) = ENNReal.ofReal κ * S.sumData φ := by
  first | exact @GlobalTheory.HL.CoordSum.tsum_reps_eq | exact GlobalTheory.HL.CoordSum.tsum_reps_eq | (intros; apply GlobalTheory.HL.CoordSum.tsum_reps_eq <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianMoves_total_measure_estimates : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → Nice (S.refA (j + 1) Λ) (ind (S.Mv (j + 1) d Λ)) ∧ Nice (S.refA (j + 1) Λ) (ind fun w => S.Mv (j + 1) d Λ w ∧ ¬ S.NoLeak Λ w.2.1) ∧ Nice (S.refA (j + 1) Λ) (fun w => ind (S.Mv (j + 1) d Λ) w * S.chiM j d Λ w.1 w.2.1) ∧ |S.cK β βJ * (cint (S.refA (j + 1) Λ) (ind (S.Mv (j + 1) d Λ))).re - 1| ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) ∧ S.cK β βJ * (cint (S.refA (j + 1) Λ) (ind fun w => S.Mv (j + 1) d Λ w ∧ ¬ S.NoLeak Λ w.2.1)).re ≤ 16 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) ∧ S.cK β βJ * ‖cint (S.refA (j + 1) Λ) (fun w => ind (S.Mv (j + 1) d Λ) w * S.chiM j d Λ w.1 w.2.1)‖ ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
  first | exact @GlobalTheory.HL.MoveTotal.total_moves | exact GlobalTheory.HL.MoveTotal.total_moves | (intros; apply GlobalTheory.HL.MoveTotal.total_moves <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Diag.PG

theorem _root_.GlobalTheory.T.hypotheses_of_global_rows_and_nodes : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C' Cl Cg : ℝ, 0 < Cl → Cl ≤ CD → ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (D : D7) (large₂ : SizeData₂ D) (cT CT : ℝ), large₂.sc.L = x ^ eps → 8 * large₂.CGam ≤ C' → Glob0 D x eps CD Cg → Nodes D x eps → (∀ u, large₂.sc.b ^ (cT * (D.R.m : ℝ)) ≤ Tr D u ∧ Tr D u ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ))) → StandingHypotheses D large₂ C' Cl Cg (1 / 4) 3 cT CT := by
  first | exact @GlobalTheory.Diag.PG.standingHypotheses_of_glob0_nodes_Tr_bounds | exact GlobalTheory.Diag.PG.standingHypotheses_of_glob0_nodes_Tr_bounds | (intros; apply GlobalTheory.Diag.PG.standingHypotheses_of_glob0_nodes_Tr_bounds <;> assumption)
end
