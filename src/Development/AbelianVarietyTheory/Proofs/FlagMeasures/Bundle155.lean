module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle131
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle132
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalSubspaceClosedRightTranslationStable
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle133
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle111
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle127
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle134
public import Mathlib.Analysis.Complex.Exponential
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle135
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Mathlib.Topology.UniformSpace.Matrix
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle129
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.unitaryJ_lieCoords_conj_linear : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → ∀ (g m : Formalism.REAL.UJ ε) (L : Matrix (Fin d) (Fin d) ℝ), uMat g - 1 ∈ A → uMat g⁻¹ - 1 ∈ A → (∀ k, uMat m * E k * uMat m⁻¹ = ∑ i, L i k • E i) → (fun i => (((uMat (m * g * m⁻¹) - 1) * (E i)ᴴ).trace).re) = L *ᵥ (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re) := by
  first | exact @GlobalTheory.UnitaryCoords.coords_conj | exact GlobalTheory.UnitaryCoords.coords_conj | (intros; apply GlobalTheory.UnitaryCoords.coords_conj <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.Dec.CuspFrame

theorem one_mem_Kg (I : AutInst) (g : ℕ) : (1 : I.Gf) ∈ I.Kg g := by
  refine ⟨?_, fun y _ => ⟨0, zero_mem _, ?_⟩⟩
  · simp [AutInst.Kset]
  · simp [AutInst.fmat]

theorem re_fixed (B : RowsAut) : ∀ k ∈ B.I.Kg B.g, (B.R (1, k)).comp B.Re = B.Re := by
  intro k hk
  obtain ⟨h1, hm, hn, -, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  have pm : ∀ a b : B.I.Gf, B.R (1, a * b) = B.R (1, a) * B.R (1, b) := fun a b => by
    have := hm (1, a) (1, b)
    rwa [Prod.mk_mul_mk, mul_one] at this
  have ir : ∀ (a : B.I.Gf) (x z : B.I.L2 B.μf B.fund), ⟪x, B.R (1, a) z⟫_ℂ = ⟪B.R (1, a⁻¹) x, z⟫_ℂ :=
    fun a x z => by
      have hback : B.R (1, a) (B.R (1, a⁻¹) x) = x := by
        have hident : B.R (1, 1) = 1 := h1
        have h := congrArg (fun S : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund => S x)
          (pm a a⁻¹)
        simpa [hident, mul_apply_eq_comp] using h.symm
      let U : B.I.L2 B.μf B.fund →ₗᵢ[ℂ] B.I.L2 B.μf B.fund :=
        ⟨(B.R (1, a)).toLinearMap, hn (1, a)⟩
      calc
        ⟪x, B.R (1, a) z⟫_ℂ = ⟪U (B.R (1, a⁻¹) x), U z⟫_ℂ := by
          change ⟪x, B.R (1, a) z⟫_ℂ = ⟪B.R (1, a) (B.R (1, a⁻¹) x), B.R (1, a) z⟫_ℂ
          rw [hback]
        _ = ⟪B.R (1, a⁻¹) x, z⟫_ℂ := U.inner_map_map _ _
  have he : ∀ x, B.e (k * x) = B.e x := fun x => by
    have := B.e_adm.2.2.2.2.2.1 x k hk 1 (one_mem_Kg B.I B.g)
    rwa [mul_one] at this
  refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.comp_apply, ir k, B.Re_spec.2, B.Re_spec.2,
    ← MeasureTheory.integral_mul_left_eq_self (fun g => B.e g * ⟪x, B.R (1, g) y⟫_ℂ) k]
  congr 1
  ext g
  rw [he, pm, mul_apply_eq_comp, ir k x]

end GlobalTheory.Dec.CuspFrame
end
end

section

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.exists_unipotentQuotient_invariant_probability : ∀ (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)), I.IsIsot W → ∃ ν : Measure I.GA, IsProbabilityMeasure ν ∧ I.IsNQuotMeas W ν ∧ ∃ Cp : Set I.GA, IsCompact Cp ∧ Cp ⊆ I.NA W ∧ ν Cpᶜ = 0 := by
  first | exact @GlobalTheory.UnipQuot.exists_quot_prob | exact GlobalTheory.UnipQuot.exists_quot_prob | (intros; apply GlobalTheory.UnipQuot.exists_quot_prob <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.invariantExtension_integrableOn_compact : ∀ (B : RowsAut) (C : Set B.I.GA), IsCompact C → ∃ M : ℝ, ∀ F : B.I.L2 B.μf B.fund, IntegrableOn (B.I.ext F) C (B.I.muA B.μf) ∧ ∫ y in C, ‖B.I.ext F y‖ ∂(B.I.muA B.μf) ≤ M * ‖F‖ := by
  first | exact @GlobalTheory.LocalL2Isometry.ext_integrableOn | exact GlobalTheory.LocalL2Isometry.ext_integrableOn | (intros; apply GlobalTheory.LocalL2Isometry.ext_integrableOn <;> assumption)
end

section

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.cuspidalSubspace_closed_rightTranslation_stable : ∀ B : RowsAut, ∃ S : Submodule ℂ (B.I.L2 B.μf B.fund), (∀ F, F ∈ S ↔ B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext F)) ∧ IsClosed (S : Set (B.I.L2 B.μf B.fund)) ∧ (∀ g, ∀ F ∈ S, B.R g F ∈ S) ∧ ∀ (F : B.I.L2 B.μf B.fund) (f : B.I.GA → ℂ), (∀ γ ∈ B.I.GFset, ∀ y, f (γ * y) = f y) → Continuous f → f =ᵐ[B.I.muA B.μf] B.I.ext F → (F ∈ S ↔ B.I.IsCuspFn (B.I.muA B.μf) f) := by
  first | exact @GlobalTheory.CuspSubspace.cuspidal_closed_stable | exact GlobalTheory.CuspSubspace.cuspidal_closed_stable | (intros; apply GlobalTheory.CuspSubspace.cuspidal_closed_stable <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.exists_blockDiag_unitary_product_hom : ∀ (n : ℕ) (ε : Fin n → Bool) (σ ι : Type) [Fintype σ] [Fintype ι] (π : σ → ι) (m : ι → ℕ) (T : ∀ s, Matrix (Fin n) (Fin (m (π s))) ℂ), Function.Surjective π → (∀ s, (T s)ᴴ * T s = 1) → (∀ s t, s ≠ t → (T s)ᴴ * T t = 0) → ∑ s, T s * (T s)ᴴ = 1 → (∀ k : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ, Formalism.REAL.Jm ε * ∑ s, T s * k (π s) * (T s)ᴴ = (∑ s, T s * k (π s) * (T s)ᴴ) * Formalism.REAL.Jm ε) → ∃ Φ : (∀ i, Formalism.REAL.UJ (allPos (m i))) →* Formalism.REAL.UJ ε, Continuous Φ ∧ Function.Injective Φ ∧ (∀ g, uMat (Φ g) = ∑ s, T s * uMat (g (π s)) * (T s)ᴴ) ∧ ∀ g, Formalism.REAL.hs (uMat (Φ g) - 1) = ∑ s, Formalism.REAL.hs (uMat (g (π s)) - 1) := by
  first | exact @GlobalTheory.BlockDiagEmb.exists_blockDiag_hom | exact GlobalTheory.BlockDiagEmb.exists_blockDiag_hom | (intros; apply GlobalTheory.BlockDiagEmb.exists_blockDiag_hom <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc

namespace GlobalTheory

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

private lemma hsub_left (x x' y : V) : H.h (x - x') y = H.h x y - H.h x' y := by
  rw [eq_sub_iff_add_eq, ← H.h_add_left, sub_add_cancel]

private lemma hsub_right (x y y' : V) : H.h x (y - y') = H.h x y - H.h x y' := by
  rw [H.h_herm (y - y') x, hsub_left, map_sub, ← H.h_herm, ← H.h_herm]

private lemma hsmul_right (c : F) (x y : V) :
    H.h x (algebraMap F E c • y) = algebraMap F E c * H.h x y := by
  rw [H.h_herm (algebraMap F E c • y) x, H.h_smul_left, map_mul, AlgEquiv.commutes, ← H.h_herm]

private lemma det_transpose_map_cj {ι : Type} [Fintype ι] [DecidableEq ι] (N : Matrix ι ι E) :
    (N.transpose.map M.L.cj).det = M.L.cj N.det := by
  have h1 := RingHom.map_det (M.L.cj : E →+* E) N.transpose
  rw [Matrix.det_transpose] at h1
  exact h1.symm

private lemma castLE_succ_eq_castSucc (r : ℕ) (h : r ≤ r + 1) :
    (Fin.castLE h : Fin r → Fin (r + 1)) = Fin.castSucc := by
  funext i
  rfl

theorem det_gram_sumElim_frames {r : ℕ} (P : LocNG.FPair H r) :
    (H.gram (Sum.elim P.A.f P.B.f)).det = (-1) ^ (r + 1) * P.Gv := by
  have diag : ∀ (Fr : LocNG.FrameD H r) (a b : Fin (r + 1)),
      H.h (Fr.f b) (Fr.f a) = Matrix.diagonal
        (fun i => if i = Fin.last r then -algebraMap F E Fr.T else 0) a b := by
    intro Fr a b
    rw [Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab
      by_cases ha : a = Fin.last r
      · subst ha
        simp [Fr.h_zz]
      · simp [ha, Fr.h_iso a a (Or.inl ha)]
    · rw [if_neg hab, Fr.h_iso b a ?_]
      by_contra hc
      simp only [not_or, not_not] at hc
      exact hab (hc.2.trans hc.1.symm)
  have hblk : H.gram (Sum.elim P.A.f P.B.f) = Matrix.fromBlocks
      (Matrix.diagonal fun i => if i = Fin.last r then -algebraMap F E P.A.T else 0)
      (H.Zhat P.A.f P.B.f)
      ((H.Zhat P.A.f P.B.f).transpose.map M.L.cj)
      (Matrix.diagonal fun i => if i = Fin.last r then -algebraMap F E P.B.T else 0) := by
    ext (a | a) (b | b)
    · exact diag P.A a b
    · rfl
    · exact H.h_herm _ _
    · exact diag P.B a b
  rw [hblk, GlobalTheory.det_gram_two_frames, det_transpose_map_cj]
  have hsub : ((H.Zhat P.A.f P.B.f).transpose.map M.L.cj).submatrix Fin.castSucc Fin.castSucc
      = ((H.Zhat P.A.f P.B.f).submatrix Fin.castSucc Fin.castSucc).transpose.map M.L.cj := rfl
  rw [hsub, det_transpose_map_cj]
  congr 1
  simp only [LocNG.FPair.Gv, HermSp.Gdet, HermSp.normE, HermSp.Dl, dif_pos le_rfl,
    dif_pos (Nat.le_succ r), Fin.castLE_rfl, Matrix.submatrix_id_id, castLE_succ_eq_castSucc, map_mul]

theorem det_gram_sumElim_smul_sub {n : ℕ} (f f' : Fin n → V) (c : F) :
    (H.gram (Sum.elim f fun a => algebraMap F E c • (f' a - f a))).det
      = algebraMap F E c ^ (2 * n) * (H.gram (Sum.elim f f')).det := by
  set c' := algebraMap F E c with hc'
  have hcs : ∀ x : E, c • x = algebraMap F E c * x := fun x => Algebra.smul_def c x
  have key : H.gram (Sum.elim f fun a => c' • (f' a - f a)) =
      Matrix.fromBlocks 1 0 (-c' • (1 : Matrix (Fin n) (Fin n) E)) (c' • 1) * H.gram (Sum.elim f f') *
        Matrix.fromBlocks 1 (-c' • (1 : Matrix (Fin n) (Fin n) E)) 0 (c' • 1) := by
    ext (a | a) (b | b) <;>
      simp [HermSp.gram, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, H.h_smul_left,
        hsub_left, hsub_right, hc', hsmul_right, hcs] <;> ring
  rw [key, Matrix.det_mul, Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁]
  simp only [Matrix.det_one, Matrix.det_smul, Fintype.card_fin, one_mul, two_mul, pow_add]
  ring

end

theorem det_gram_frame_generators :
    ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
      [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK →
      ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r _k : ℕ) (P : LocNG.FPair H r),
        (H.gram P.MMgen).det * algebraMap F E (LocNG.theta M) ^ (2 * (r + 1))
          = (-1) ^ (r + 1) * P.Gv := by
  intro F _ _ _ E _ _ _ _ M _ V _ _ H r _ P
  unfold LocNG.FPair.MMgen HermSp.MMfam LocNG.theta
  cases hs : M.split with
  | none =>
    simp only [map_one, one_pow, mul_one]
    exact det_gram_sumElim_frames H P
  | some g =>
    simp only
    rw [det_gram_sumElim_smul_sub H, det_gram_sumElim_frames H P, mul_comm _ (algebraMap F E _ ^ _),
      ← mul_assoc, ← mul_pow, ← map_mul]
    have hq : ((g.q : 𝒪[F]) : F) ≠ 0 := by
      intro h0
      exact g.q_irr.ne_zero (Subtype.ext h0)
    rw [mul_inv_cancel₀ hq, map_one, one_pow, one_mul]

end GlobalTheory
end

section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.TubeLie


open scoped Matrix.Norms.Operator in
theorem skew_of_mem_lieOf {N : ℕ} (H X : Matrix (Fin N) (Fin N) ℂ) (h : X ∈ lieOf (UH H)) :
    Xᴴ * H + H * X = 0 := by
  have hc : ∀ t : ℝ, (NormedSpace.exp ((t : ℂ) • X))ᴴ = NormedSpace.exp ((t : ℂ) • Xᴴ) := by
    intro t
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
  have key : ∀ t : ℝ, H * NormedSpace.exp (t • X) = NormedSpace.exp (t • -Xᴴ) * H := by
    intro t
    have ht : (NormedSpace.exp ((t : ℂ) • X))ᴴ * H * NormedSpace.exp ((t : ℂ) • X) = H := h t
    rw [hc t] at ht
    have e1 : NormedSpace.exp (-((t : ℂ) • Xᴴ)) * NormedSpace.exp ((t : ℂ) • Xᴴ) = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ (Commute.refl ((t : ℂ) • Xᴴ)).neg_left, neg_add_cancel,
        NormedSpace.exp_zero]
    have e2 : H * NormedSpace.exp ((t : ℂ) • X) = NormedSpace.exp (-((t : ℂ) • Xᴴ)) * H := by
      calc H * NormedSpace.exp ((t : ℂ) • X)
          = (NormedSpace.exp (-((t : ℂ) • Xᴴ)) * NormedSpace.exp ((t : ℂ) • Xᴴ)) * H *
              NormedSpace.exp ((t : ℂ) • X) := by rw [e1, one_mul]
        _ = NormedSpace.exp (-((t : ℂ) • Xᴴ)) *
              (NormedSpace.exp ((t : ℂ) • Xᴴ) * H * NormedSpace.exp ((t : ℂ) • X)) := by
            simp only [mul_assoc]
        _ = NormedSpace.exp (-((t : ℂ) • Xᴴ)) * H := by rw [ht]
    rw [← smul_neg, Complex.coe_smul, Complex.coe_smul] at e2
    exact e2
  have d1 : HasDerivAt (fun t : ℝ => H * NormedSpace.exp (t • X))
      (H * (NormedSpace.exp ((0 : ℝ) • X) * X)) 0 :=
    (hasDerivAt_exp_smul_const X (0 : ℝ)).const_mul H
  have d2 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • -Xᴴ) * H)
      (NormedSpace.exp ((0 : ℝ) • -Xᴴ) * -Xᴴ * H) 0 :=
    (hasDerivAt_exp_smul_const (-Xᴴ) (0 : ℝ)).mul_const H
  rw [show (fun t : ℝ => H * NormedSpace.exp (t • X)) =
      (fun t : ℝ => NormedSpace.exp (t • -Xᴴ) * H) from funext key] at d1
  have hu := d1.unique d2
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at hu
  rw [hu, neg_mul, add_neg_cancel]

private theorem conjTranspose_exp_mul_mul_exp_eq_of_skew {N : ℕ} (H X : Matrix (Fin N) (Fin N) ℂ) (h : Xᴴ * H + H * X = 0)
    (t : ℝ) : (NormedSpace.exp ((t : ℂ) • X))ᴴ * H * NormedSpace.exp ((t : ℂ) • X) = H := by
  have hx : H * X = -(Xᴴ * H) := by
    rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
    exact h
  have hs : SemiconjBy H ((t : ℂ) • X) (-((t : ℂ) • Xᴴ)) := by
    unfold SemiconjBy
    rw [mul_smul_comm, hx, smul_neg, neg_mul, smul_mul_assoc]
  have hc : (NormedSpace.exp ((t : ℂ) • X))ᴴ = NormedSpace.exp ((t : ℂ) • Xᴴ) := by
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
  let _ : NormedRing (Matrix (Fin N) (Fin N) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℚ (Matrix (Fin N) (Fin N) ℂ) := Matrix.linftyOpNormedAlgebra
  let _ : NormedAlgebra ℂ (Matrix (Fin N) (Fin N) ℂ) := Matrix.linftyOpNormedAlgebra
  have _ : CompleteSpace (Matrix (Fin N) (Fin N) ℂ) := FiniteDimensional.complete ℂ _
  have := hs.exp_neg_mul_mul_exp_eq_self
  rw [neg_neg] at this
  rw [hc]
  exact this

theorem mem_lieOf_of_skew {N : ℕ} (H X : Matrix (Fin N) (Fin N) ℂ) (h : Xᴴ * H + H * X = 0) :
    X ∈ lieOf (UH H) := by
  intro t
  exact conjTranspose_exp_mul_mul_exp_eq_of_skew H X h t

private theorem unrealify_equiv_symm_realifyFun {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) :
    unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) = X := by
  ext i j
  apply Complex.ext <;> simp [unrealify, realifyFun]

private theorem equiv_symm_realifyFun_unrealify_eq {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    (WithLp.equiv 2 _).symm (realifyFun (unrealify x)) = x := by
  ext ⟨i, j, b⟩
  cases b <;> simp [unrealify, realifyFun]

private theorem unrealify_map_add {m : ℕ} (x y : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (x + y) = unrealify x + unrealify y := by
  ext i j
  apply Complex.ext <;> simp [unrealify]

private theorem unrealify_map_smul {m : ℕ} (c : ℝ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (c • x) = (c : ℂ) • unrealify x := by
  ext i j
  apply Complex.ext <;> simp [unrealify]

private theorem unrealify_map_zero {m : ℕ} :
    unrealify (0 : EuclideanSpace ℝ (Fin m × Fin m × Bool)) = 0 := by
  ext i j
  apply Complex.ext <;> simp [unrealify]

theorem mem_lieE_UH (m : ℕ) (H : Matrix (Fin m) (Fin m) ℂ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    x ∈ lieE (UH H) ↔ (unrealify x)ᴴ * H + H * unrealify x = 0 := by
  have hL : lieOf (UH H) = {X : Matrix (Fin m) (Fin m) ℂ | Xᴴ * H + H * X = 0} := by
    ext X
    exact ⟨fun h => skew_of_mem_lieOf H X h, fun h => mem_lieOf_of_skew H X h⟩
  constructor
  · intro hx
    unfold lieE at hx
    rw [hL] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨X, hX, rfl⟩ := hy
      rw [unrealify_equiv_symm_realifyFun]
      exact hX
    | zero => simp [unrealify_map_zero]
    | add y z _ _ hy hz =>
      rw [unrealify_map_add, Matrix.conjTranspose_add, add_mul, mul_add]
      calc (unrealify y)ᴴ * H + (unrealify z)ᴴ * H + (H * unrealify y + H * unrealify z)
          = ((unrealify y)ᴴ * H + H * unrealify y) + ((unrealify z)ᴴ * H + H * unrealify z) := by
            abel
        _ = 0 := by rw [hy, hz, add_zero]
    | smul c y _ hy =>
      rw [unrealify_map_smul, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
        smul_mul_assoc, mul_smul_comm, ← smul_add, hy, smul_zero]
  · intro hx
    unfold lieE
    apply Submodule.subset_span
    refine ⟨unrealify x, ?_, equiv_symm_realifyFun_unrealify_eq x⟩
    rw [hL]
    exact hx

theorem mem_lieE_UH_of_sq : ∀ (m : ℕ) (H : Matrix (Fin m) (Fin m) ℂ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)),
    H * H = 1 → (x ∈ lieE (UH H) ↔ (unrealify x)ᴴ * H + H * unrealify x = 0) := by
  intro m H x _
  exact mem_lieE_UH m H x

end GlobalTheory.TubeLie
end
end

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder

theorem _root_.GlobalTheory.T.unitaryGroup_structures_perm_conj_invariant : ∀ (n : ℕ) (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)), (∀ g : Matrix (Fin n) (Fin n) ℂ, (g ∈ UJset (ε ∘ s) ↔ g.submatrix s.symm s.symm ∈ UJset ε) ∧ (g ∈ Kset (ε ∘ s) ↔ g.submatrix s.symm s.symm ∈ Kset ε) ∧ (inP (ε ∘ s) g ↔ inP ε (g.submatrix s.symm s.symm)) ∧ NormedSpace.exp (g.submatrix s.symm s.symm) = (NormedSpace.exp g).submatrix s.symm s.symm) ∧ ∀ (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (p : ENNReal), (MemLp (fun g : UJ ε => f (umat g)) p (muG ε) ↔ MemLp (fun g : UJ (ε ∘ s) => f ((umat g).submatrix s.symm s.symm)) p (muG (ε ∘ s))) ∧ (MemLp (fun g : UJ ε => f (umat g)) p (muG ε) ↔ MemLp (fun g : UJ ε => f ((umat g).map star)) p (muG ε)) := by
  first | exact @GlobalTheory.Dec.PermGroup.permGroup | exact GlobalTheory.Dec.PermGroup.permGroup | (intros; apply GlobalTheory.Dec.PermGroup.permGroup <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.kMap_lowestKTypeSubspace_eq_scalar : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → ∀ T : lowKSub ε lam σ →ₗ[ℂ] H, (∀ k ∈ Kset ε, ∀ s s' : lowKSub ε lam σ, (s' : H) = σ k s → T s' = σ k (T s)) → ∃ c : ℂ, ∀ s, T s = c • (s : H) := by
  first | exact @GlobalTheory.KMapInto.kMap_lowKSub_scalar | exact GlobalTheory.KMapInto.kMap_lowKSub_scalar | (intros; apply GlobalTheory.KMapInto.kMap_lowKSub_scalar <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.exists_orthonormal_basis_re_trace_mul_conjTranspose' : ∀ (n : ℕ) (U : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)), ∃ (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) ∧ LinearIndependent ℝ E ∧ U = Submodule.span ℝ (Set.range E) := by
  first | exact @GlobalTheory.exists_orthonormal_basis_re_trace_mul_conjTranspose | exact GlobalTheory.exists_orthonormal_basis_re_trace_mul_conjTranspose | (intros; apply GlobalTheory.exists_orthonormal_basis_re_trace_mul_conjTranspose <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.sum_two_pow_pred_mul_exp_neg_le_exp_neg_third : ∀ (q : ℕ) (x : ℝ), 15 ≤ x → ∑ J ∈ Finset.Icc 1 q, (2 : ℝ) ^ (J - 1) * Real.exp (-(1 / 2 * J * x)) ≤ Real.exp (-(1 / 3 * x)) := by
  first | exact @GlobalTheory.sum_two_pow_pred_mul_exp_neg_le | exact GlobalTheory.sum_two_pow_pred_mul_exp_neg_le | (intros; apply GlobalTheory.sum_two_pow_pred_mul_exp_neg_le <;> assumption)
end
