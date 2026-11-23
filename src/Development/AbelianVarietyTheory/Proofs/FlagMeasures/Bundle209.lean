module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle148
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle188
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle131
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselRootMeasureIndependentOfChoices
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle169
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivity
public import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
import Formalism.FormalDegreeBessel.FinalG
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentLebesgueMeasureIsHaarOn
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle045
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle189
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle121
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle162
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle190
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle165
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle111
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle126
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPoint
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.IntertwinerFrame

theorem exists_orthonormal_frame_of_le : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → ∀ S : Submodule ℂ (B.Hs →L[ℂ] B.I.L2 B.μf B.fund), S ≤ B.I.HomS B.σs B.μf B.fund B.R → FiniteDimensional ℂ S → ∃ T : Fin (Module.finrank ℂ S) → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund), (∀ i, T i ∈ S) ∧ (∀ i u, ‖T i u‖ = ‖u‖) ∧ ∀ i j, i ≠ j → ∀ u u', ⟪T i u, T j u'⟫_ℂ = 0 := by
  intro B d hd S hle hfin
  obtain ⟨hU, hirr, -, hw, -⟩ := GlobalTheory.Dec.tensorRep B d hd
  obtain ⟨-, -, hR, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  let σ : B.I.Ginf →* (B.Hs →L[ℂ] B.Hs) :=
    { toFun := B.σs
      map_one' := hU.1
      map_mul' := hU.2.1 }
  obtain ⟨T, h1, h2, h3, -⟩ := exists_frame S (B.tens B.w) fun T hT T' hT' u u' =>
    inner_intertwiners σ hU.2.2.1 hirr (fun g => B.R (g, 1)) (fun g => hR _) _ hw T T' (hle hT) (hle hT') u u'
  exact ⟨T, h1, h2, h3⟩

end GlobalTheory.IntertwinerFrame
end
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.lintegral_compact_le_quotientMeasure_bessel : ∀ (k r : ℕ) (S : Set (Mat k r)) (μG μS ν : Measure (Mt k r)) (K₀ : Set (Mt k r)), IsClosedSub k r S → IsHaarOn (GG k r) μG → IsHaarOn S μS → IsUnimod S μS → IsQuotMeas μG μS ν → IsCompact K₀ → ∃ C : ENNReal, C < ⊤ ∧ ∀ F : Mt k r → ENNReal, Measurable F → (∀ s ∈ S, ∀ x, F (lmulM s x) = F x) → ∫⁻ x in K₀, F x ∂μG ≤ C * ∫⁻ x, F x ∂ν := by
  first | exact @GlobalTheory.SgInf.lint_compact_le_quot | exact GlobalTheory.SgInf.lint_compact_le_quot | (intros; apply GlobalTheory.SgInf.lint_compact_le_quot <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.SnMass
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.besselRootMeasure_independent_of_choices : ∀ (D : Formalism.BasicNotions.D7) (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (γ : Mat D.R.k D.R.rS) (p p' : Point ℂ (D.R.rS + 1)) (μ μ' : Measure (Mt D.R.k D.R.rS)), inWb D.R.k D.R.rS z → inWb D.R.k D.R.rS z' → 0 < Tz D.R.k D.R.rS z → 0 < Tz D.R.k D.R.rS z' → γ ∈ GG D.R.k D.R.rS → Gf D.R.k D.R.rS z z' γ ≠ 0 → 0 < D.host.ka → Formalism.MainNotions.S.IsRootMeasR D z z' p γ μ → Formalism.MainNotions.S.IsRootMeasR D z z' p' γ μ' → p = p' ∧ μ = μ' ∧ IsHaarOn (Rset D.R.k D.R.rS γ) μ := by
  first | exact @GlobalTheory.SnMass.RootUniq.rootMeas_unique | exact GlobalTheory.SnMass.RootUniq.rootMeas_unique | (intros; apply GlobalTheory.SnMass.RootUniq.rootMeas_unique <;> assumption)
end

section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.YBound

open GlobalTheory.Amp.GramFlag (eucl_eq)

theorem det_upper {r : ℕ} (x : UT r → ℂ) : (upper x).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [upper]
  · intro a b h
    have h' : b < a := h
    simp [upper, not_lt.2 h'.le, h'.ne']

theorem det_change {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (B : V₁ →ₗ[ℂ] V₂ →ₗ⋆[ℂ] ℂ) {j : ℕ} (y : Fin j → V₁) (y' : Fin j → V₂) (U U' : Matrix (Fin j) (Fin j) ℂ)
    (hU : U.det = 1) (hU' : U'.det = 1) :
    (Matrix.of fun a b => B (∑ c, U c a • y c) (∑ c, U' c b • y' c)).det =
      (Matrix.of fun a b => B (y a) (y' b)).det := by
  have e : (Matrix.of fun a b => B (∑ c, U c a • y c) (∑ c, U' c b • y' c)) =
      Uᵀ * (Matrix.of fun a b => B (y a) (y' b)) * (U'ᴴ)ᵀ := by
    ext a b

    simp only [Matrix.of_apply, Matrix.mul_apply, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    LinearMap.map_smulₛₗ, Matrix.transpose_apply, Matrix.conjTranspose_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum]
    first
      | (refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_; simp; ring)
      | (rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_; simp; ring)
  rw [e]
  simp [Matrix.det_mul, Matrix.det_conjTranspose, hU, hU']

theorem prod_le_pow' {n : ℕ} (f : Fin n → ℝ) (R : ℝ) (h0 : ∀ i, 0 ≤ f i) (h : ∀ i, f i ≤ R) :
    ∏ i, f i ≤ R ^ n := by
  calc _ ≤ ∏ _a : Fin n, R := Finset.prod_le_prod₀ (fun i _ => h0 i) fun i _ => h i
    _ = _ := by simp

def formE {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) →ₗ⋆[ℂ] ℂ :=
  (innerₛₗ ℂ).flip ∘ₗ Matrix.toEuclideanLin H

theorem formE_apply {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    formE H (WithLp.toLp 2 v) (WithLp.toLp 2 w) = herm H v w := by
  show ⟪(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n)), WithLp.toLp 2 (H *ᵥ v)⟫_ℂ = _
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, herm]

theorem formE_le {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ * H = 1) (v w : EuclideanSpace ℂ (Fin n)) :
    ‖formE H v w‖ ≤ ‖v‖ * ‖w‖ := by
  have h1 : ‖Matrix.toEuclideanLin H v‖ = ‖v‖ := by
    have : ⟪Matrix.toEuclideanLin H v, Matrix.toEuclideanLin H v⟫_ℂ = ⟪v, v⟫_ℂ := by
      rw [← LinearMap.adjoint_inner_right, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      congr 1
      ext i
      simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec, hH]
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), this, ← norm_eq_sqrt_re_inner]
  show ‖⟪w, Matrix.toEuclideanLin H v⟫_ℂ‖ ≤ _
  rw [mul_comm, ← h1]
  exact norm_inner_le_norm _ _

theorem herm_mulVec {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH H) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  have h : gᴴ * H * g = H := hg
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

theorem gramProj_le {n r : ℕ} (P : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (v : Fin r → Fin n → ℂ)
    (U : Matrix (Fin r) (Fin r) ℂ) (hU : U.det = 1) (R : ℝ) (hR : ∀ a, eucl (∑ b, U b a • v b) ≤ R) :
    gramProj P v ≤ R ^ r := by
  have h := (Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.gramHadamard (EuclideanSpace ℂ (Fin n)) r
    (fun a => ∑ b, U b a • P.starProjection (WithLp.toLp 2 (v b)))).2 R (fun a => by
      refine le_trans ?_ (hR a)
      rw [eucl_eq, WithLp.toLp_sum]

      simp only [← map_smul, ← map_sum, WithLp.toLp_smul]
      exact P.norm_starProjection_apply_le _)
  have e : ∀ w : Fin r → EuclideanSpace ℂ (Fin n), (Matrix.gram ℂ w).det =
      (Matrix.of fun a b => (innerₛₗ ℂ).flip (w a) (w b)).det := by
    intro w
    rw [← Matrix.det_transpose]
    rfl
  unfold gramProj
  rw [e, det_change _ _ _ U U hU hU, ← e] at h
  exact h

theorem dr_y_le : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (γ : Mat k r), TwoFl k r z z' γ → ∀ x ∈ GG k r, Dr k r z z' γ ≤ Sg k r z' x ^ r * Sg k r z (γ * x) ^ r ∧ 0 ≤ Yv k r z z' γ x ∧ Yv k r z z' γ x ≤ Sg k r z (γ * x) ^ r / Dr k r z z' γ := by
  intro k r z z' γ hT x hx
  obtain ⟨hz, hz', -, -, hg, -, -⟩ := hT
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have hG := uHGroup _ _ hH
  have hgx : γ * x ∈ GG k r := hG.2.1 _ hg _ hx
  obtain ⟨u', hu', -⟩ := GramFlag.gramSchmidt_lengths k r z' x hx
  obtain ⟨u, hu, -⟩ := GramFlag.gramSchmidt_lengths k r z _ hgx
  have h1 : ∀ a, eucl (∑ b, upper u b a • ((γ * x)⁻¹ *ᵥ bvec (eI k r b))) ≤ Sg k r z (γ * x) := fun a => by
    rw [(hu a).1]; exact (((LInv.lengths_basic k r z hz).2.2 _).2.1 _).2
  have h2 : ∀ a, eucl (∑ b, upper u' b a • (x⁻¹ *ᵥ bvec (eI k r b))) ≤ Sg k r z' x := fun a => by
    rw [(hu' a).1]; exact (((LInv.lengths_basic k r z' hz').2.2 _).2.1 _).2
  have hD0 : 0 ≤ Dr k r z z' γ := norm_nonneg _
  refine ⟨?_, div_nonneg (Real.sqrt_nonneg _) hD0, ?_⟩
  · have h := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.wedgeHadamard _ _ (formE (Hpk k r))
      (formE_le _ (by rw [(hpkFacts k r).1, (hpkFacts k r).2.1])) r
      (fun a => ∑ b, upper u' b a • WithLp.toLp 2 (x⁻¹ *ᵥ bvec (eI k r b)))
      (fun a => ∑ b, upper u b a • WithLp.toLp 2 ((γ * x)⁻¹ *ᵥ bvec (eI k r b)))
    rw [det_change _ _ _ _ _ (det_upper u') (det_upper u)] at h
    have e : Dmin k r z z' γ ⟨r, by omega⟩ = (Matrix.of fun a b : Fin r => formE (Hpk k r)
        (WithLp.toLp 2 (x⁻¹ *ᵥ bvec (eI k r a))) (WithLp.toLp 2 ((γ * x)⁻¹ *ᵥ bvec (eI k r b)))).det := by
      unfold Dmin
      rw [← Matrix.det_transpose]
      congr 1
      ext a b
      have ha := a.2
      have hb := b.2
      simp only at ha hb
      simp only [Matrix.transpose_apply, Matrix.submatrix_apply,
        _root_.Formalism.QuantumDeterminants.Zhat, _root_.Formalism.QuantumDeterminants.fvec,
        Matrix.of_apply, formE_apply]
      rw [dite_eq_left (by simpa using ha), dite_eq_left (by simpa using hb),
        ← herm_mulVec (hG.2.2 _ hgx).2, Matrix.mulVec_mulVec, Matrix.mul_inv_rev,
        Matrix.nonsing_inv_mul_cancel_right _ _ (hG.2.2 _ hg).1]
      rfl
    unfold Dr
    rw [e]
    refine h.trans (mul_le_mul ?_ ?_ (Finset.prod_nonneg fun _ _ => norm_nonneg _) ?_)
    · refine prod_le_pow' _ _ (fun _ => norm_nonneg _) fun a => le_trans (le_of_eq ?_) (h2 a)
      rw [eucl_eq, WithLp.toLp_sum]; rfl
    · refine prod_le_pow' _ _ (fun _ => norm_nonneg _) fun a => le_trans (le_of_eq ?_) (h1 a)
      rw [eucl_eq, WithLp.toLp_sum]; rfl
    · exact pow_nonneg (zero_le_one.trans ((LInv.lengths_basic k r z' hz').2.2 _).1) _
  · unfold Yv
    refine div_le_div_of_nonneg_right ?_ hD0
    refine gramProj_le _ _ (upper u) (det_upper u) _ fun a => ?_
    simpa only [Matrix.mulVec_mulVec, Matrix.mul_inv_rev] using h1 a

end GlobalTheory.Amp.YBound
end
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.flagUnipotentLebesgueMeasure_isHaarOn : ∀ k r : ℕ, IsHaarOn (Nset k r) (lebN k r) := by
  first | exact @GlobalTheory.Amp.NHaar.isHaarOn_lebN | exact GlobalTheory.Amp.NHaar.isHaarOn_lebN | (intros; apply GlobalTheory.Amp.NHaar.isHaarOn_lebN <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.majorant_flag_lengths_invariance_torus_positivity : ∀ (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)), inWb k r z → (∀ x ∈ GG k r, ∀ s ∈ Sset k r z, ∀ κ ∈ (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))), (∀ a, lA k r z (s * x * κ) a = lA k r z x a) ∧ Sg k r z (s * x * κ) = Sg k r z x) ∧ (∀ (a : Fin r → ℝ), (∀ b, 0 < a b) → ∀ m ∈ UH (Hb k), ∀ b : Fin r, lA k r z (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) b.castSucc = (a b)⁻¹) ∧ (∀ x, 1 ≤ Sg k r z x ∧ (∀ a, 0 ≤ lA k r z x a ∧ lA k r z x a ≤ Sg k r z x) ∧ (Sg k r z x = 1 ∨ ∃ a, Sg k r z x = lA k r z x a)) := by
  first | exact @GlobalTheory.Amp.LInv.lengths_basic | exact GlobalTheory.Amp.LInv.lengths_basic | (intros; apply GlobalTheory.Amp.LInv.lengths_basic <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.covolume_inverseDifferentPow_mul_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∀ (t t' : ℕ) (c : ℝ), 0 < c → HasDom volume (ideLat (dInv E t * dInv E t') c : Set (InfinitePlace E → ℂ)) (ENNReal.ofReal ((2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * (t : ℝ) - 2 * (t' : ℝ)) * c ^ (2 * Fintype.card (InfinitePlace E)))) := by
  first | exact @GlobalTheory.SnMass.VolN.CovMul.hasDom_ideLat_dInv_mul | exact GlobalTheory.SnMass.VolN.CovMul.hasDom_ideLat_dInv_mul | (intros; apply GlobalTheory.SnMass.VolN.CovMul.hasDom_ideLat_dInv_mul <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.covolume_inverseDifferentPow_div_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∀ (t t' : ℕ) (c : ℝ), 0 < c → HasDom volume (ideLat (dInv E t * (dInv E t')⁻¹) c : Set (InfinitePlace E → ℂ)) (ENNReal.ofReal ((2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * (t : ℝ) + 2 * (t' : ℝ)) * c ^ (2 * Fintype.card (InfinitePlace E)))) := by
  first | exact @GlobalTheory.SnMass.VolN.hasDom_ideLat_dInv_div | exact GlobalTheory.SnMass.VolN.hasDom_ideLat_dInv_div | (intros; apply GlobalTheory.SnMass.VolN.hasDom_ideLat_dInv_div <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

theorem IsRadial.comp_measurableEquiv {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X}
    {ν : Measure Y} (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) {q : X → ℝ} {p : Y → ℝ} {d : ℕ}
    (hq : ∀ x, q x = p (e x)) (h : IsRadial ν p d) : IsRadial μ q d := by
  unfold IsRadial at *
  refine h.congr fun r => ?_
  rw [← he.measure_preimage_equiv]
  simp only [hq, Set.preimage_ofPred_eq]

theorem isRadial_pi : ∀ (a : ℕ) (X : Fin a → Type) [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, SigmaFinite (μ i)] (q : ∀ i, X i → ℝ) (d : Fin a → ℕ), (∀ i, Measurable (q i)) →
    (∀ i x, 0 ≤ q i x) → (∀ i, IsRadial (μ i) (q i) (d i)) →
    IsRadial (Measure.pi μ) (fun x => ∑ i, q i (x i)) (∑ i, d i) := by
  intro a
  induction a with
  | zero =>
    intro X _ μ _ q d _ _ _
    rw [Fin.sum_univ_zero]
    unfold IsRadial
    rw [volume_euclideanSpace_eq_dirac, Measure.dirac_apply_of_mem (Metric.mem_ball_self one_pos)]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : (0 : ℝ) ≤ r := le_of_lt hr
    rw [Measure.pi_of_empty, Measure.dirac_apply_of_mem (by simpa using hr')]
    simp
  | succ a ih =>
    intro X _ μ _ q d hm h0 hr
    have h := GlobalTheory.T.hasEuclideanBallVolumeSublevelAsymptotics_prod _ _ (μ 0) (Measure.pi fun j => μ (Fin.succAbove 0 j)) (q 0)
      (fun x => ∑ j, q (Fin.succAbove 0 j) (x j)) (d 0) (∑ j, d (Fin.succAbove 0 j)) (hm 0)
      (Finset.measurable_sum _ fun j _ => (hm _).comp (measurable_pi_apply j)) (h0 0)
      (fun y => Finset.sum_nonneg fun j _ => h0 _ _) (hr 0)
      (ih _ _ _ _ (fun j => hm _) (fun j => h0 _) fun j => hr _)
    rw [Fin.sum_univ_succAbove d 0]
    exact h.comp_measurableEquiv _ (measurePreserving_piFinSuccAbove μ 0)
      fun x => Fin.sum_univ_succAbove (fun i => q i (x i)) 0

end GlobalTheory.LeviIso
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

theorem _root_.GlobalTheory.T.levi_chart_map_haar_carried_invariant : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ → ∀ W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ), SpansFlag B W → ∀ θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ → Formalism.REAL.UJ ε, Measurable θ → (∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → uMat (θ z) = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2)) → ∀ c : ℝ, (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ) (flagM ε W)ᶜ = 0 ∧ ∀ s ∈ flagM ε W, (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ).map (fun g => s * g) = (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ) := by
  first | exact @GlobalTheory.LeviIso.map_chart_carried_and_invariant | exact GlobalTheory.LeviIso.map_chart_carried_and_invariant | (intros; apply GlobalTheory.LeviIso.map_chart_carried_and_invariant <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.MeanDual

theorem _root_.GlobalTheory.T.isLattice_traceDual_and_traceDual_traceDual : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)), Submodule.IsFullLattice E Λ → Submodule.IsFullLattice E (trDual E j Λ) ∧ trDual E j (trDual E j Λ) = Λ := by
  exact GlobalTheory.MeanDual.Alg.isLattice_trDual_and_trDual_trDual
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov

private theorem hform_eq_dotProduct_mulVec {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (s y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J s y = star s ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply,
    mul_assoc]

theorem pieceHt_dualFlag : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ), (∀ i, 1 ≤ j i) → ∀ (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∀ F : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E), IsDualFlag I.J F (2 * a + 1) → F (2 * a + 1) = lamX I (1, xf) → (∀ i : Fin (a + 1), F i = S i) → (∀ i : Fin a, 0 < Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ∧ pieceHt (frm I (1, xf)) F i = Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ^ (2 * I.f * j i) ∧ pieceHt (frm I (1, xf)) F (2 * a - i) = (Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ^ (2 * I.f * j i))⁻¹) ∧ pieceHt (frm I (1, xf)) F a = 1 ∧ ∀ b, 2 * a + 1 ≤ b → pieceHt (frm I (1, xf)) F b = 1 := by
  intro I xf a j hj S hS F hF hFm hFS
  have hmaj := GlobalTheory.Count.FrameMajorant.frames_give_majorants I (1, xf)
  haveI : IsTotallyComplex I.E := hmaj.1
  have hf : Formalism.HN.nPl I.E = I.f := hmaj.2.1
  have hX : ∀ w, IsUnit (frm I (1, xf) w).det := fun w => GlobalTheory.Count.FrameMajorant.frm_unit I (1, xf) w
  have hΛfg : (lamX I (1, xf)).FG := (GlobalTheory.PointLattice.lamX_selfDual I (1, xf)).2.1
  have hmain := GlobalTheory.Count.PerpStep.main I (1, xf)
  have hht1 : Formalism.HN.ht (bas I) (frm I (1, xf)) (lamX I (1, xf)) = 1 := hmain.1
  have hperp := hmain.2.2.2
  have hfg : ∀ N : Submodule (𝓞 I.E) (Fin I.n → I.E), N ≤ lamX I (1, xf) → N.FG := by
    intro N hN
    haveI := isNoetherian_of_fg_of_noetherian _ hΛfg
    have h1 : (N.comap (lamX I (1, xf)).subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map (lamX I (1, xf)).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hN] at h2

  have hrat : ∀ N T : Submodule (𝓞 I.E) (Fin I.n → I.E), N ≤ lamX I (1, xf) →
      Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I (1, xf))) N T →
      Formalism.HN.ht (bas I) (frm I (1, xf)) N / Formalism.HN.ht (bas I) (frm I (1, xf)) T =
        Formalism.HN.htQ (bas I) (frm I (1, xf)) N T := by
    intro N T hN hT
    rw [GlobalTheory.Count.PerpStep.ht_eq (bas I) (frm I (1, xf)) hX N (hfg N hN),
      GlobalTheory.Count.PerpStep.ht_eq (bas I) (frm I (1, xf)) hX T (hfg T (hT.1.trans hN)),
      GlobalTheory.Count.PerpStep.htQ_eq (bas I) (frm I (1, xf)) hX N T (hfg N hN) hT, ← Real.exp_sub]
    congr 1
    ring
  have hqpos : ∀ N T : Submodule (𝓞 I.E) (Fin I.n → I.E), N ≤ lamX I (1, xf) →
      Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I (1, xf))) N T →
      0 < Formalism.HN.htQ (bas I) (frm I (1, xf)) N T := by
    intro N T hN hT
    rw [GlobalTheory.Count.PerpStep.htQ_eq (bas I) (frm I (1, xf)) hX N T (hfg N hN) hT]
    exact Real.exp_pos _

  have hdual : ∀ b, b ≤ 2 * a + 1 → perpIn I (1, xf) (F b) = F (2 * a + 1 - b) := by
    intro b hb
    ext y
    rw [GlobalTheory.Count.PerpStep.perpIn_eq, GlobalTheory.Count.PerpStep.mem_perp, hF.2.2.2 b hb y, hFm]
    refine and_congr_right fun _ => forall₂_congr fun s _ => ?_
    rw [hform_eq_dotProduct_mulVec]

  have hsatS : ∀ i : Fin (a + 1),
      Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I (1, xf))) (lamX I (1, xf)) (S i) := by
    intro i
    have h := GlobalTheory.Count.PerpStep.sat_inf (bas I) (frm I (1, xf)) hX (lamX I (1, xf)) hΛfg
      (Submodule.span I.E (S i : Set (Fin I.n → I.E)))
    convert h using 1
    ext y
    rw [Submodule.mem_inf, Submodule.restrictScalars_mem]
    exact hS.2.2.2.1 i y
  have hsatF : ∀ b, b ≤ 2 * a + 1 →
      Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I (1, xf))) (lamX I (1, xf)) (F b) := by
    intro b hb
    by_cases hba : b ≤ a
    · have e : F b = S ⟨b, by omega⟩ := hFS ⟨b, by omega⟩
      rw [e]
      exact hsatS _
    · have e : F (2 * a + 1 - b) = S ⟨2 * a + 1 - b, by omega⟩ := hFS ⟨2 * a + 1 - b, by omega⟩
      have h := (hperp (F (2 * a + 1 - b)) (F (2 * a + 1 - b)) (by rw [e]; exact hsatS _)
        (by rw [e]; exact hsatS _) le_rfl).1
      rwa [hdual _ (by omega), show 2 * a + 1 - (2 * a + 1 - b) = b by omega] at h
  have hpiece : ∀ b, b + 1 ≤ 2 * a + 1 →
      pieceHt (frm I (1, xf)) F b = Formalism.HN.htQ (bas I) (frm I (1, xf)) (F (b + 1)) (F b) := by
    intro b hb
    unfold pieceHt
    exact hrat _ _ (hsatF _ hb).1
      (GlobalTheory.Count.PerpStep.sat_mono (bas I) (frm I (1, xf)) (hsatF b (by omega))
        (hF.1 (Nat.le_succ b)) (hsatF _ hb).1)
  have hsat' : ∀ b, b + 1 ≤ 2 * a + 1 →
      Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I (1, xf))) (F (b + 1)) (F b) := fun b hb =>
    GlobalTheory.Count.PerpStep.sat_mono (bas I) (frm I (1, xf)) (hsatF b (by omega))
      (hF.1 (Nat.le_succ b)) (hsatF _ hb).1
  refine ⟨fun i => ?_, ?_, fun b hb => ?_⟩
  · have hi := i.isLt
    have hFi : F i = S i.castSucc := by simpa using hFS i.castSucc
    have hFi1 : F (i + 1) = S i.succ := by simpa using hFS i.succ
    have hq := hqpos _ _ (hsatF _ (by omega)).1 (hsat' i (by omega))
    rw [hFi1, hFi] at hq
    have hrk : ((Formalism.HN.rkK (S i.succ) : ℝ) - Formalism.HN.rkK (S i.castSucc)) = j i := by
      rw [hS.2.2.1 i]
      push_cast
      ring
    have hjpos : (0 : ℝ) < j i := by exact_mod_cast hj i
    have hfpos : (0 : ℝ) < I.f := by
      rw [← hf]
      exact_mod_cast Fintype.card_pos
    have hsz : Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) =
        Formalism.HN.htQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ^
          ((1 : ℝ) / (2 * (I.f : ℝ) * (j i : ℝ))) := by
      unfold Formalism.HN.sizeQ
      rw [hrk, hf]
    have hpow : Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ^ (2 * I.f * j i) =
        Formalism.HN.htQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) := by
      rw [hsz, ← Real.rpow_natCast, ← Real.rpow_mul hq.le]
      have hc : (1 : ℝ) / (2 * (I.f : ℝ) * (j i : ℝ)) * ((2 * I.f * j i : ℕ) : ℝ) = 1 := by
        push_cast
        field_simp
      rw [hc, Real.rpow_one]
    have hpi : pieceHt (frm I (1, xf)) F i =
        Formalism.HN.htQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) := by
      rw [hpiece i (by omega), hFi1, hFi]
    refine ⟨by rw [hsz]; exact Real.rpow_pos_of_pos hq _, by rw [hpi, hpow], ?_⟩
    rw [hpow, hpiece (2 * a - i) (by omega)]
    have hPi := hdual i (by omega)
    have hPi1 := hdual (i + 1) (by omega)
    rw [show 2 * a + 1 - i = 2 * a - i + 1 by omega] at hPi
    rw [show 2 * a + 1 - (i + 1) = 2 * a - i by omega] at hPi1
    have h := (hperp (F i) (F (i + 1)) (hsatF _ (by omega)) (hsatF _ (by omega))
      (hF.1 (Nat.le_succ _))).2.2.2.2
    rw [hPi, hPi1, hFi1, hFi] at h
    exact h
  · have hPa := hdual a (by omega)
    have hPa1 := hdual (a + 1) (by omega)
    rw [show 2 * a + 1 - a = a + 1 by omega] at hPa
    rw [show 2 * a + 1 - (a + 1) = a by omega] at hPa1
    have h := (hperp (F a) (F (a + 1)) (hsatF _ (by omega)) (hsatF _ (by omega))
      (hF.1 (Nat.le_succ _))).2.2.2.2
    rw [hPa, hPa1] at h
    have hq := hqpos _ _ (hsatF _ (by omega)).1 (hsat' a (by omega))
    rw [hpiece a (by omega)]
    set q := Formalism.HN.htQ (bas I) (frm I (1, xf)) (F (a + 1)) (F a) with hqdef
    have hmul : q * q = 1 := by
      calc q * q = q⁻¹ * q := by rw [← h]
        _ = 1 := inv_mul_cancel₀ hq.ne'
    nlinarith
  · unfold pieceHt
    rw [hF.2.2.1 (b + 1) (by omega), hF.2.2.1 b hb, hFm, hht1]
    norm_num

end GlobalTheory.RadCov
end
