module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantMultilinearOfMatrixCoeffEqUnita
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegativeFrameDomainProductOpenPreconnectedStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialNonneg
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle037
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsKfin
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.Bundle005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.DiracSquareMemLayer

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_equivariant_multilinear_of_matrixCoeff_eq_unitaryProduct : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Hm : ι → Mt n) (H : ι → Type) [∀ τ, NormedAddCommGroup (H τ)] [∀ τ, InnerProductSpace ℂ (H τ)] [∀ τ, CompleteSpace (H τ)] (σ : ∀ τ, Mt n → (H τ →L[ℂ] H τ)) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ρ : (ι → Mt n) → (K →L[ℂ] K)) (v : ∀ τ, H τ) (k : K), (∀ τ, (Hm τ).det ≠ 0 ∧ IsURepOn (Formalism.QuantumDeterminants.UH (Hm τ)) (σ τ) ∧ IsIrredOn (Formalism.QuantumDeterminants.UH (Hm τ)) (σ τ) ∧ ‖v τ‖ = 1) → ρ 1 = 1 → (∀ u ∈ UG Hm, ∀ u' ∈ UG Hm, ρ (u * u') = ρ u * ρ u') → (∀ u ∈ UG Hm, ∀ y, ‖ρ u y‖ = ‖y‖) → (∀ u ∈ UG Hm, ⟪k, ρ u k⟫_ℂ = ((‖k‖ ^ 2 : ℝ) : ℂ) * ∏ τ, ⟪v τ, σ τ (u τ) (v τ)⟫_ℂ) → ∃ Φ : ContinuousMultilinearMap ℂ H K, Φ v = k ∧ (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (Hm τ), ∀ y, Φ (Function.update y τ (σ τ g (y τ))) = ρ (Pi.mulSingle τ g) (Φ y)) ∧ ∀ y, Φ y ∈ closure (Submodule.span ℂ {z | ∃ u ∈ UG Hm, z = ρ u k} : Set K) := by
  first | exact @GlobalTheory.exists_equivariant_multilinear_of_matrixCoeff_eq | exact GlobalTheory.exists_equivariant_multilinear_of_matrixCoeff_eq | (intros; apply GlobalTheory.exists_equivariant_multilinear_of_matrixCoeff_eq <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem flowInv_herm {n : ℕ} {Hm x₀ : Mt n} {q : ℕ} (h : OrthFr Hm q x₀) : Hmᴴ = Hm := by
  obtain ⟨-, hD⟩ := h
  have hdet : x₀.det ≠ 0 := by
    intro h0
    have hd := congrArg Matrix.det hD
    rw [det_mul, det_mul, h0, mul_zero, det_diagonal] at hd
    refine (Finset.prod_ne_zero_iff.mpr fun a _ => ?_) hd.symm
    unfold ReciprocityTheory.ChartRestriction.G.FD.sgn
    split_ifs <;> norm_num
  have hu : IsUnit x₀ := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have huH : IsUnit x₀ᴴ := by
    refine (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ?_)
    rw [det_conjTranspose]
    exact (star_ne_zero).mpr hdet
  have hself : (x₀ᴴ * Hm * x₀)ᴴ = x₀ᴴ * Hm * x₀ := by
    rw [hD, diagonal_conjTranspose]
    congr 1
    funext a
    simp [Complex.conj_ofReal]
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, ← Matrix.mul_assoc] at hself
  exact huH.mul_right_injective (hu.mul_left_injective hself)

theorem flowInv_sq {n : ℕ} {Hm : Mt n} {e : Fin n → ℂ} (he : star e ⬝ᵥ Hm.mulVec e = 0) :
    vecMulVec e (star e ᵥ* Hm) * vecMulVec e (star e ᵥ* Hm) = 0 := by
  rw [vecMulVec_mul_vecMulVec, ← dotProduct_mulVec, he, zero_smul]
  ext i j
  simp [vecMulVec_apply]

theorem flowInv_adj {n : ℕ} {Hm : Mt n} (hH : Hmᴴ = Hm) (e : Fin n → ℂ) :
    (vecMulVec e (star e ᵥ* Hm))ᴴ * Hm = Hm * vecMulVec e (star e ᵥ* Hm) := by
  rw [conjTranspose_vecMulVec, star_vecMul, star_star, hH, vecMulVec_mul, mul_vecMulVec]

private theorem one_sub_sub_smul_vecMulVec_eq_mul_of_isotropic {n : ℕ} {Hm : Mt n} {e : Fin n → ℂ} (he : star e ⬝ᵥ Hm.mulVec e = 0)
    (a b : ℂ) : (1 - (b - a) • vecMulVec e (star e ᵥ* Hm) : Mt n) =
      (1 + a • vecMulVec e (star e ᵥ* Hm)) * (1 - b • vecMulVec e (star e ᵥ* Hm)) := by
  have hS := flowInv_sq he
  rw [add_mul, one_mul, mul_sub, mul_one, smul_mul_assoc, mul_smul_comm, hS, smul_zero, smul_zero, sub_zero,
    sub_smul]
  abel

theorem flowInv_mem {n : ℕ} {Hm : Mt n} (hH : Hmᴴ = Hm) {e : Fin n → ℂ} (he : star e ⬝ᵥ Hm.mulVec e = 0)
    (s : ℝ) : (1 + ((s : ℂ) * Complex.I) • vecMulVec e (star e ᵥ* Hm) : Mt n) ∈ Formalism.QuantumDeterminants.UH Hm := by
  show (1 + ((s : ℂ) * Complex.I) • vecMulVec e (star e ᵥ* Hm))ᴴ * Hm *
    (1 + ((s : ℂ) * Complex.I) • vecMulVec e (star e ᵥ* Hm)) = Hm
  have hc : star ((s : ℂ) * Complex.I) = -((s : ℂ) * Complex.I) := by
    simp [Complex.conj_ofReal]
  have h1 : (1 + ((s : ℂ) * Complex.I) • vecMulVec e (star e ᵥ* Hm))ᴴ * Hm =
      Hm * (1 + (-((s : ℂ) * Complex.I)) • vecMulVec e (star e ᵥ* Hm)) := by
    rw [conjTranspose_add, conjTranspose_one, conjTranspose_smul, add_mul, one_mul, smul_mul_assoc,
      flowInv_adj hH e, hc, mul_add, mul_one, mul_smul_comm]
  have h2 := one_sub_sub_smul_vecMulVec_eq_mul_of_isotropic he (-((s : ℂ) * Complex.I)) (-((s : ℂ) * Complex.I))
  have h3 : (1 - (-((s : ℂ) * Complex.I)) • vecMulVec e (star e ᵥ* Hm) : Mt n) =
      1 + ((s : ℂ) * Complex.I) • vecMulVec e (star e ᵥ* Hm) := by
    rw [neg_smul, sub_neg_eq_add]
  rw [sub_self, zero_smul, sub_zero, h3] at h2
  rw [h1, Matrix.mul_assoc, ← h2, mul_one]

private theorem mul_mem_uh {n : ℕ} {Hm g₁ g₂ : Mt n} (h₁ : g₁ ∈ Formalism.QuantumDeterminants.UH Hm) (h₂ : g₂ ∈ Formalism.QuantumDeterminants.UH Hm) :
    g₁ * g₂ ∈ Formalism.QuantumDeterminants.UH Hm := by
  change g₁ᴴ * Hm * g₁ = Hm at h₁
  change g₂ᴴ * Hm * g₂ = Hm at h₂
  show (g₁ * g₂)ᴴ * Hm * (g₁ * g₂) = Hm
  rw [conjTranspose_mul]
  calc g₂ᴴ * g₁ᴴ * Hm * (g₁ * g₂) = g₂ᴴ * (g₁ᴴ * Hm * g₁) * g₂ := by simp only [Matrix.mul_assoc]
    _ = Hm := by rw [h₁, h₂]

theorem flowInv : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Hm : ι → Mt n) (q : ι → ℕ) (x₀ : ι → Mt n) (w : ι → Fin n → ℤ), (∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) → ∀ (P : (ι → Fin n → Fin n → ℂ) → ℂ) (e : ι → Fin n → ℂ), (∀ τ, star (e τ) ⬝ᵥ (Hm τ).mulVec (e τ) = 0) → HolSec Hm q w P → (∀ m : ι → Mt n, (∀ τ, InZe (Hm τ) (e τ) (m τ)) → ∀ u ∈ UG Hm, P (fun τ => (m τ * u τ * x₀ τ : Mt n)) = P (fun τ => (u τ * x₀ τ : Mt n))) → ∀ u ∈ UG Hm, ∀ t : ℝ, 0 ≤ t → P (fun τ => ((1 - (t : ℂ) • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ)) * u τ * x₀ τ : Mt n)) = P (fun τ => (u τ * x₀ τ : Mt n)) := by
  intro n ι _ _ Hm q x₀ w hO P e he hP hInv u hu t ht
  have hH : ∀ τ, (Hm τ)ᴴ = Hm τ := fun τ => flowInv_herm (hO τ)
  have hu' : ∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (Hm τ) := hu
  obtain ⟨hOpen, -, hStab, hBase⟩ := frDoms_open_preconnected_stable n ι Hm q x₀ hO
  let X : ℂ → (ι → Fin n → Fin n → ℂ) := fun z τ =>
    ((1 - z • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ)) * u τ * x₀ τ : Mt n)
  have hXaff : X = fun z τ i j => (u τ * x₀ τ) i j - z * (vecMulVec (e τ) (star (e τ) ᵥ* Hm τ) * u τ * x₀ τ) i j := by
    funext z τ i j
    simp only [X, sub_mul, one_mul, smul_mul_assoc, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  have hXd : Differentiable ℂ X := by
    rw [hXaff]
    refine differentiable_pi.2 fun τ => differentiable_pi.2 fun i => differentiable_pi.2 fun j => ?_
    exact (differentiable_const _).sub (differentiable_id.mul (differentiable_const _))
  have hHU : {z : ℂ | 0 ≤ z.re} ⊆ X ⁻¹' frDoms Hm q := by
    intro z hz
    have hGS := fun τ => FlowGS.flowGS n (Hm τ) (q τ) (x₀ τ) (hO τ) (w τ) (e τ) (he τ) (u τ) (hu' τ)
    choose C A hCA using hGS
    choose u' hu' b hbf using fun τ => hCA τ z.re hz
    have hmem := hStab (fun τ => (1 + (((-z.im : ℝ) : ℂ) * Complex.I) • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ)) * u' τ)
      (show ∀ τ, _ ∈ Formalism.QuantumDeterminants.UH (Hm τ) from fun τ => mul_mem_uh (flowInv_mem (hH τ) (he τ) (-z.im)) (hu' τ)) b (fun τ => (hbf τ).1)
      (fun τ => (x₀ τ : Mt n)) hBase
    suffices hXz : X z = fun τ => ((1 + (((-z.im : ℝ) : ℂ) * Complex.I) • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ)) * u' τ * x₀ τ * b τ : Mt n) by
      show X z ∈ frDoms Hm q
      rw [hXz]
      exact hmem
    funext τ
    have hfac := (hbf τ).2.1
    have hsplit := one_sub_sub_smul_vecMulVec_eq_mul_of_isotropic (he τ) (((-z.im : ℝ) : ℂ) * Complex.I) (z.re : ℂ)
    have hz' : (z.re : ℂ) - ((-z.im : ℝ) : ℂ) * Complex.I = z := by
      apply Complex.ext <;> simp
    rw [hz'] at hsplit
    show (1 - z • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ)) * u τ * x₀ τ = _
    simp only [Matrix.mul_assoc] at hfac ⊢
    rw [hsplit, Matrix.mul_assoc, hfac]
  let f : ℂ → ℂ := fun z => P (X z)
  have hfU : DifferentiableOn ℂ f (X ⁻¹' frDoms Hm q) :=
    hP.1.comp hXd.differentiableOn fun z hz => hz
  have hUo : IsOpen (X ⁻¹' frDoms Hm q) := hOpen.preimage hXd.continuous
  have h0 : (0 : ℂ) ∈ {z : ℂ | 0 ≤ z.re} := by simp
  have hVo := hUo.connectedComponentIn (x := (0 : ℂ))
  have hHV := (convex_halfSpace_re_ge (0 : ℝ)).isPreconnected.subset_connectedComponentIn h0 hHU
  have hfV : AnalyticOnNhd ℂ f (connectedComponentIn (X ⁻¹' frDoms Hm q) 0) :=
    (hfU.mono (connectedComponentIn_subset _ _)).analyticOnNhd hVo
  have eX0 : X 0 = fun τ => (u τ * x₀ τ : Mt n) := by
    funext τ
    show (1 - (0 : ℂ) • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ)) * u τ * x₀ τ = u τ * x₀ τ
    rw [zero_smul, sub_zero, one_mul]
  have hfreq : ∃ᶠ z in nhdsWithin (0 : ℂ) {0}ᶜ, f z = (fun _ => f 0) z := by
    have hT : Filter.Tendsto (fun s : ℝ => (s : ℂ) * Complex.I) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have hc : Continuous (fun s : ℝ => (s : ℂ) * Complex.I) := by fun_prop
        simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hs) Complex.I_ne_zero
    apply hT.frequently
    refine Filter.Eventually.frequently (Filter.Eventually.of_forall fun s => ?_)
    have h1 := hInv (fun τ => 1 + (((-s : ℝ) : ℂ) * Complex.I) • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ))
      (fun τ => by unfold InZe; exact ⟨-s, rfl⟩) u hu
    have eX : X ((s : ℂ) * Complex.I) =
        fun τ => ((1 + (((-s : ℝ) : ℂ) * Complex.I) • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ)) * u τ * x₀ τ : Mt n) := by
      funext τ
      simp only [X]
      congr 2
      push_cast
      simp only [neg_mul, neg_smul, sub_eq_add_neg]
    show P (X ((s : ℂ) * Complex.I)) = P (X 0)
    rw [eX, eX0]
    exact h1
  have hEq := hfV.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const
    isPreconnected_connectedComponentIn (mem_connectedComponentIn (hHU h0)) hfreq
  have ht' : (t : ℂ) ∈ {z : ℂ | 0 ≤ z.re} := by simpa using ht
  have key : f t = f 0 := hEq (hHV ht')
  show f t = _
  rw [key]
  show P (X 0) = _
  rw [eX0]

end GlobalTheory.HolDict
end

section

section

noncomputable section

namespace GlobalTheory.PsCo.PcEF.MatrixRepresentation

variable {n : ℕ} (ε : Fin n → Bool) {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

abbrev mat (g : Formalism.REAL.UJ ε) : Matrix (Fin n) (Fin n) ℂ :=
  ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

theorem mat_injective : Function.Injective (mat ε) := fun _ _ h => Subtype.ext (Units.ext h)

def rep (π : Formalism.REAL.UJ ε →* (X →L[ℂ] X)) (x : Matrix (Fin n) (Fin n) ℂ) : X →L[ℂ] X := by
  classical exact if h : ∃ g, mat ε g = x then π h.choose else 1

theorem rep_mat (π : Formalism.REAL.UJ ε →* (X →L[ℂ] X)) (g : Formalism.REAL.UJ ε) : rep ε π (mat ε g) = π g := by
  have h : ∃ g', mat ε g' = mat ε g := ⟨g, rfl⟩
  rw [rep, dite_eq_left h, mat_injective ε h.choose_spec]

theorem range_mat : Set.range (mat ε) = Formalism.MainNotions.S.UJset ε := (Formalism.REAL.isClosedEmbeddingMatrix n ε).2

theorem mat_mem (g : Formalism.REAL.UJ ε) : mat ε g ∈ Formalism.MainNotions.S.UJset ε := range_mat ε ▸ ⟨g, rfl⟩

theorem exists_mat {x : Matrix (Fin n) (Fin n) ℂ} (hx : x ∈ Formalism.MainNotions.S.UJset ε) : ∃ g, mat ε g = x := by
  rw [← range_mat ε] at hx; exact hx

theorem isEmbedding_mat : Topology.IsEmbedding (mat ε) := (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding

end GlobalTheory.PsCo.PcEF.MatrixRepresentation

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEF.MatrixRepresentation

theorem unitaryRep_upq_matrixFunction : MatRep := by
  intro n ε U _ _ π hπ hi
  refine ⟨rep ε π, ⟨⟨?_, fun a ha b hb => ?_⟩, fun a ha v => ?_, fun v => ?_⟩, fun S hS hinv => ?_, fun g => rep_mat ε π g⟩
  · have h1 : mat ε 1 = 1 := rfl
    rw [← h1, rep_mat, map_one]
  · obtain ⟨g, rfl⟩ := exists_mat ε ha
    obtain ⟨h, rfl⟩ := exists_mat ε hb
    have hm : mat ε g * mat ε h = mat ε (g * h) := rfl
    rw [hm, rep_mat, rep_mat, rep_mat, map_mul]
    rfl
  · obtain ⟨g, rfl⟩ := exists_mat ε ha
    rw [rep_mat]
    exact hπ.norm_apply g v
  · have hr : Formalism.MainNotions.S.UJset ε = Set.range (mat ε) := (range_mat ε).symm
    show ContinuousOn (fun g => rep ε π g v) (Formalism.MainNotions.S.UJset ε)
    rw [hr, continuousOn_iff_continuous_domRestrict]
    let E := (isEmbedding_mat ε).toHomeomorph
    have hE : ∀ y, (fun g => π g v) (E.symm y) = rep ε π (y : Matrix (Fin n) (Fin n) ℂ) v := by
      intro y
      obtain ⟨g, rfl⟩ := E.surjective y
      show π (E.symm (E g)) v = rep ε π (mat ε g) v
      rw [E.symm_apply_apply, rep_mat]
    exact ((hπ.continuous_apply v).comp E.symm.continuous).congr hE
  · exact hi.2 S ⟨hS, fun g v hv => by simpa [rep_mat] using hinv _ (mat_mem ε g) v hv⟩

end GlobalTheory.PsCo.PcEF

end
end
end

section

noncomputable section

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap
open Formalism.REAL (KG toMK muK)
open GlobalTheory.PsCo.Pc1 (Mat Poly ev)

namespace GlobalTheory.PsCo.PcEF

theorem polyAverages_finiteWeightStableSubspace : PolyAvg := by
  classical
  intro n ε d
  set Wm : Set (Fin n → ℝ) := wtM '' {m : EntIdx n →₀ ℕ | (m.sum fun _ e => e) ≤ d}
  refine ⟨Wm, (finite_monomials_of_degree_le d).image _, fun H _ _ _ σ hσ u => ?_⟩
  have hemb : Topology.IsEmbedding (fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  set φ : Formalism.REAL.KG ε → Matrix (Fin n) (Fin n) ℂ := fun k => Formalism.REAL.toMK k with hφdef
  have hφc : Continuous φ := hemb.continuous
  have hφK : ∀ g, φ g ∈ Kset ε := fun g => g.2
  have hφ1 : φ 1 = 1 := rfl
  have hφm : ∀ a b, φ (a * b) = φ a * φ b := fun a b => rfl
  have hφs : ∀ m ∈ Kset ε, ∃ g, φ g = m := by
    intro m hm
    have : m ∈ Set.range (fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k) := by
      rw [Formalism.REAL.range_toMK]
      exact hm
    obtain ⟨g, hg⟩ := this
    exact ⟨g, hg⟩
  have hinUJ : ∀ g, φ g ∈ UJset ε := fun g => smd_inUJ_of_Kset (hφK g)
  have horb : ∀ u : H, Continuous fun k => σ (φ k) u := fun u => (hσ.2.2 u).comp_continuous hφc hinUJ
  have hentc : Continuous fun k => entVar (φ k) := by
    refine continuous_pi fun i => ?_
    rcases i with x | x
    · exact (continuous_apply x.2).comp ((continuous_apply x.1).comp hφc)
    · exact continuous_star.comp ((continuous_apply x.2).comp ((continuous_apply x.1).comp hφc))
  have hpolyc : ∀ Q : MvPolynomial (EntIdx n) ℂ, Continuous fun k => eval (entVar (φ k)) Q :=
    fun Q => (MvPolynomial.continuous_eval Q).comp hentc
  have hint : ∀ (Q : MvPolynomial (EntIdx n) ℂ) (u : H),
      Integrable (fun k => eval (entVar (φ k)) Q • σ (φ k) u) (muK ε) := fun Q u =>
    ((hpolyc Q).smul (horb u)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let Xu : H → MvPolynomial (EntIdx n) ℂ →ₗ[ℂ] H := fun u =>
    { toFun := fun Q => ∫ k, eval (entVar (φ k)) Q • σ (φ k) u ∂(muK ε)
      map_add' := fun Q R => by
        simp only [map_add (f := _), add_smul]
        exact integral_add (hint Q u) (hint R u)
      map_smul' := fun c Q => by
        simp only [smul_eval, mul_smul, RingHom.id_apply]
        exact integral_smul c _ }
  have hXu : ∀ u Q, Xu u Q = ∫ k, eval (entVar (φ k)) Q • σ (φ k) u ∂(muK ε) := fun _ _ => rfl
  have htr : ∀ u Q g, σ (φ g) (Xu u Q) = Xu u (bind₁ (trF (φ g⁻¹)) Q) := by
    intro u Q g
    rw [hXu, hXu, ← (σ (φ g)).integral_comp_comm (hint Q u)]
    have e2 : ∫ k, σ (φ g) (eval (entVar (φ k)) Q • σ (φ k) u) ∂(muK ε) =
        ∫ k, eval (entVar (φ (g⁻¹ * (g * k)))) Q • σ (φ (g * k)) u ∂(muK ε) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [map_smul, inv_mul_cancel_left]
      rw [hφm g k, hσ.1.2 _ (hinUJ g) _ (hinUJ k)]
      rfl
    rw [e2, integral_mul_left_eq_self (fun k => eval (entVar (φ (g⁻¹ * k))) Q • σ (φ k) u) g]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [hφm, eval_mul_eq_bind₁]
  have hmono : ∀ (u : H) (m : EntIdx n →₀ ℕ),
      Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ (wtM m) (Xu u (monomial m 1)) := by
    intro u m θ hθ
    rw [mir_Kset_eq] at hθ
    obtain ⟨g, hg⟩ := hφs _ hθ
    have hginv : φ g⁻¹ = star (φ g) := by
      have h1 : φ g * star (φ g) = 1 := Unitary.mul_star_self_of_mem (hφK g).1
      calc φ g⁻¹ = φ g⁻¹ * (φ g * star (φ g)) := by rw [h1, Matrix.mul_one]
        _ = star (φ g) := by rw [← Matrix.mul_assoc, ← hφm, inv_mul_cancel, hφ1, Matrix.one_mul]
    rw [← hg, htr, hXu, hXu, ← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only
    rw [← eval_mul_eq_bind₁, hginv, hg, show Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) =
      dTor θ from rfl, eval_monomial_tor, mul_smul]
  let Sd : Submodule ℂ H := (restrictTotalDegree (EntIdx n) ℂ d).map (Xu u)
  refine ⟨Sd, Module.Finite.map _ _, ?_, ?_, ?_⟩
  · intro k hk x hx
    rw [mir_Kset_eq] at hk
    obtain ⟨g, rfl⟩ := hφs k hk
    obtain ⟨Q, hQ, rfl⟩ := hx
    rw [htr]
    refine Submodule.mem_map_of_mem ?_
    rw [SetLike.mem_coe, mem_restrictTotalDegree] at hQ
    rw [mem_restrictTotalDegree]
    exact (totalDegree_bind_le_of_linear _ (trF_totalDegree _) Q).trans hQ
  · intro P hP
    exact Submodule.mem_map_of_mem ((mem_restrictTotalDegree _ _ P).2 hP)
  · rintro μ s ⟨Q, hQ, rfl⟩ hs0 hsw
    by_contra hμ
    rw [SetLike.mem_coe, mem_restrictTotalDegree] at hQ
    have hsum : Xu u Q = ∑ m ∈ Q.support, AddMonoidAlgebra.coeff Q m • Xu u (monomial m 1) := by
      conv_lhs => rw [Q.as_sum]

      rw [map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← map_smul, smul_monomial, smul_eq_mul, mul_one]
    have horth : ∀ m ∈ Q.support, inner ℂ (Xu u Q) (Xu u (monomial m 1)) = 0 := by
      intro m hm
      refine kfin_wt_orth hσ hsw (hmono u m) fun h => hμ ?_
      exact ⟨m, (le_totalDegree hm).trans hQ, h.symm⟩
    apply hs0
    rw [← inner_self_eq_zero (𝕜 := ℂ)]
    calc inner ℂ (Xu u Q) (Xu u Q) = inner ℂ (Xu u Q) (∑ m ∈ Q.support, AddMonoidAlgebra.coeff Q m • Xu u (monomial m 1)) := by
          rw [← hsum]
      _ = 0 := by
          rw [inner_sum]
          exact Finset.sum_eq_zero fun m hm => by rw [inner_smul_right, horth m hm, mul_zero]

end GlobalTheory.PsCo.PcEF
end
end

section

open GlobalTheory.LKCount

namespace GlobalTheory

theorem massC_ne_zero_of_support {G : Type} [Group G] (Γ' T K : Subgroup G) (F : G → ℂ) (hΓT : Γ' ≤ T)
    (hF : ∀ t ∈ T, ∀ x, ∀ k ∈ K, F (t * x * k) = F x)
    (hfin : ∀ x : G, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite)
    (hsupp : {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}.Finite)
    (y : G) (hy : F y ≠ 0) :
    massC Γ' T (T ⊓ K.map (MulAut.conj y).toMonoidHom) ≠ 0 := by
  have memconj : ∀ (L : Subgroup G) (a x : G), x ∈ L.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ L := by
    intro L a x
    rw [Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  have memconjT : ∀ (L : Subgroup T) (a x : T), x ∈ L.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ L := by
    intro L a x
    rw [Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  set C := T ⊓ K.map (MulAut.conj y).toMonoidHom with hC
  set A : Subgroup T := Γ'.subgroupOf T
  set B : Subgroup T := C.subgroupOf T

  let φ : DoubleCoset.Quotient (A : Set T) (B : Set T) → DoubleCoset.Quotient (Γ' : Set G) (K : Set G) :=
    fun q => DoubleCoset.mk Γ' K (((Quotient.out q : T) : G) * y)
  have hφS : ∀ q, φ q ∈ {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0} := by
    intro q
    show F (Quotient.out (DoubleCoset.mk Γ' K (((Quotient.out q : T) : G) * y))) ≠ 0
    obtain ⟨h, hh, k, hk, he⟩ := DoubleCoset.mk_out_eq_mul Γ' K (((Quotient.out q : T) : G) * y)
    rw [he, hF h (hΓT hh) _ k hk]
    have := hF ((Quotient.out q : T) : G) (Quotient.out q).2 y 1 K.one_mem
    rw [mul_one] at this
    rw [this]; exact hy
  have hφinj : Function.Injective φ := by
    intro q1 q2 h12
    rw [← DoubleCoset.out_eq' (H := A) (K := B) q1, ← DoubleCoset.out_eq' (H := A) (K := B) q2]
    obtain ⟨g, hg, k, hk, he⟩ := (@DoubleCoset.eq _ _ Γ' K _ _).1 h12
    set t1 : T := Quotient.out q1
    set t2 : T := Quotient.out q2
    have hgT : g ∈ T := hΓT hg
    have hs : y * k * y⁻¹ = ((t1 : G))⁻¹ * g⁻¹ * (t2 : G) := by
      have ht2 : (t2 : G) = g * ((t1 : G) * y) * k * y⁻¹ := by rw [← he]; group
      rw [ht2]; group
    have hsT : y * k * y⁻¹ ∈ T := by
      rw [hs]; exact T.mul_mem (T.mul_mem (T.inv_mem t1.2) (T.inv_mem hgT)) t2.2
    have hsC : y * k * y⁻¹ ∈ C := by
      refine ⟨hsT, (memconj K y _).2 ?_⟩
      simpa [mul_assoc] using hk
    rw [DoubleCoset.eq]
    refine ⟨⟨g, hgT⟩, ?_, ⟨y * k * y⁻¹, hsT⟩, ?_, ?_⟩
    · simpa [A, Subgroup.mem_subgroupOf] using hg
    · simpa [B, Subgroup.mem_subgroupOf] using hsC
    · apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [hs]; group
  haveI : Finite {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0} := hsupp.to_subtype
  haveI hQ : Finite (DoubleCoset.Quotient (A : Set T) (B : Set T)) :=
    Finite.of_injective (fun q => (⟨φ q, hφS q⟩ : {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}))
      (fun a b h => hφinj (congrArg Subtype.val h))

  have hpos : ∀ q : DoubleCoset.Quotient (A : Set T) (B : Set T),
      0 < ((Nat.card (A ⊓ B.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup T) : ℕ) : ℚ)⁻¹ := by
    intro q
    set t : T := Quotient.out q
    haveI : Finite ↥(Γ' ⊓ K.map (MulAut.conj ((t : G) * y)).toMonoidHom) := (hfin ((t : G) * y)).to_subtype
    have hmem : ∀ x : ↥(A ⊓ B.map (MulAut.conj t).toMonoidHom),
        ((x : T) : G) ∈ Γ' ⊓ K.map (MulAut.conj ((t : G) * y)).toMonoidHom := by
      intro x
      have hx := x.2
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxA, hxB⟩ := hx
      rw [memconjT] at hxB
      have hxC : ((t⁻¹ * (x : T) * t : T) : G) ∈ C := hxB
      refine ⟨hxA, (memconj K _ _).2 ?_⟩
      have := (memconj K y _).1 hxC.2
      simpa [mul_assoc] using this
    haveI : Finite ↥(A ⊓ B.map (MulAut.conj t).toMonoidHom) :=
      Finite.of_injective (fun x => (⟨((x : T) : G), hmem x⟩ : ↥(Γ' ⊓ K.map (MulAut.conj ((t : G) * y)).toMonoidHom)))
        (by intro a b h; apply Subtype.ext; apply Subtype.ext; have h' := congrArg Subtype.val h; exact h')
    exact inv_pos.mpr (Nat.cast_pos.mpr Nat.card_pos)
  haveI := Fintype.ofFinite (DoubleCoset.Quotient (A : Set T) (B : Set T))
  unfold massC
  rw [finsum_eq_sum_of_fintype]
  exact ne_of_gt (Finset.sum_pos (fun q _ => hpos q) Finset.univ_nonempty)

end GlobalTheory
end
