module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IntegrableComplexContinuousBoundedSupport
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle002

@[expose] public section

section

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def IsSmoothL2 (ε : Fin n → Bool) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  Formalism.REAL.SmoothOnG ε F ∧ ∀ w : List (Fin n × Fin n),
    MemLp (fun g : Formalism.REAL.UJ ε => Formalism.REAL.Eword ε w F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)

theorem eword_append_Eab (ε : Fin n → Bool) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (p : Fin n × Fin n) :
    ∀ w : List (Fin n × Fin n),
      Formalism.REAL.Eword ε w (Formalism.REAL.Eab ε p.1 p.2 F) = Formalism.REAL.Eword ε (w ++ [p]) F
  | [] => rfl
  | q :: w => by
      simp only [List.cons_append, Formalism.REAL.Eword]
      rw [eword_append_Eab ε F p w]

theorem IsSmoothL2.Eab {ε : Fin n → Bool} {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : IsSmoothL2 ε F)
    (a b : Fin n) : IsSmoothL2 ε (Formalism.REAL.Eab ε a b F) := by
  refine ⟨Formalism.REAL.smooth_lie_derivative a b hF.1, fun w => ?_⟩
  have h := eword_append_Eab ε F (a, b) w
  simp only at h
  rw [h]
  exact hF.2 _

theorem isSmoothL2_of_casimir_eigen (ε : Fin n → Bool) (W : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ)) (c : ℂ)
    (hW : FiniteDimensional ℂ W) (hsm : ∀ w ∈ W, Formalism.REAL.SmoothOnG ε w)
    (hK : ∀ w ∈ W, ∀ i j : Fin n, ε i = ε j → ∃ w' ∈ W, ∀ g, Formalism.REAL.inUJ ε g → Formalism.REAL.Eab ε i j w g = w' g)
    (hc : ∀ w ∈ W, ∀ g, Formalism.REAL.inUJ ε g → Formalism.REAL.CasF ε w g = c * w g)
    (hL2 : ∀ w ∈ W, MemLp (fun g : Formalism.REAL.UJ ε => w (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) :
    ∀ w ∈ W, IsSmoothL2 ε w := by
  have hint : ∀ w ∈ W, Integrable (fun g : Formalism.REAL.UJ ε =>
      Real.exp (2 * (0:ℝ) * Formalism.REAL.hh (Formalism.REAL.toM g)) * ‖w (Formalism.REAL.toM g)‖ ^ 2) (Formalism.REAL.muG ε) := by
    intro w hw
    have := (hL2 w hw).integrable_norm_pow (by norm_num)
    simpa using this
  have key := r0bG n ε W c 0 hW le_rfl hsm hK hc hint
  intro f hf
  refine ⟨hsm f hf, fun w => ?_⟩
  obtain ⟨hs, hi, -⟩ := key w [] f f hf hf
  have hae : AEStronglyMeasurable (fun g : Formalism.REAL.UJ ε => Formalism.REAL.Eword ε w f (Formalism.MainNotions.S.umat g))
      (Formalism.REAL.muG ε) := (Formalism.REAL.continuous_smooth_on_group_eval hs).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hae]
  simpa using hi

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix MeasureTheory
open scoped ContDiff NNReal ENNReal

namespace ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Smooth

variable {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

end Smooth

theorem puniq_schur {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ) (A : T.V →ₗ[ℂ] T.V)
    (hA : ∀ (k : S7.KG ε) (v : T.V), A (T.op k v) = T.op k (A v)) : ∃ c : ℂ, ∀ v, A v = c • v := by
  letI := T.instNACG
  letI := T.instIPS
  letI := T.instFD
  haveI : Nontrivial T.V := ⟨⟨T.w, 0, fun h => by
    have hw := T.w_norm
    rw [h, norm_zero] at hw
    exact zero_ne_one hw⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue A
  refine ⟨c, fun v => ?_⟩
  have hinv : ∀ k : S7.KG ε, ∀ v ∈ Module.End.eigenspace A c,
      ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) v ∈ Module.End.eigenspace A c := by
    intro k v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have := hA k v
    simp only [S7.KType.op] at this
    rw [this, hv, map_smul]
  rcases T.irred _ hinv with h | h
  · exact absurd h (Module.End.hasEigenvalue_iff.mp hc)
  · have hv : v ∈ Module.End.eigenspace A c := by rw [h]; trivial
    exact Module.End.mem_eigenspace_iff.mp hv

theorem puniq_kset {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) :
    g ∈ UJset ε := by
  obtain ⟨hu, hc⟩ := hg
  have hu' : gᴴ * g = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hu
    simpa [Matrix.star_eq_conjTranspose] using this
  show gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, hu', Matrix.one_mul]

theorem puniq_isKTypeOf_map {ε : Fin n → Bool} {H₁ H₂ : Type*} [NormedAddCommGroup H₁]
    [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}
    (U : H₁ ≃ₗᵢ[ℂ] H₂) (hU : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, U (σ₁ g x) = σ₂ g (U x))
    {μ : Fin n → ℝ} {S : Submodule ℂ H₁} (hS : Formalism.MainNotions.S.IsKTypeOf ε σ₁ μ S) :
    Formalism.MainNotions.S.IsKTypeOf ε σ₂ μ (S.map (U.toLinearEquiv : H₁ →ₗ[ℂ] H₂)) := by
  obtain ⟨hfd, hst, hmin, ⟨v, hvS, hv0, hvw⟩, hdom⟩ := hS
  set f : H₁ →ₗ[ℂ] H₂ := (U.toLinearEquiv : H₁ →ₗ[ℂ] H₂) with hf
  have hfU : ∀ x, f x = U x := fun x => rfl
  have hback : ∀ g ∈ Formalism.REAL.Kset ε, ∀ y, σ₁ g (U.symm y) = U.symm (σ₂ g y) := by
    intro g hg y
    apply U.injective
    rw [hU g hg, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  have memS : ∀ x, f x ∈ S.map f → x ∈ S := by
    rintro x ⟨y, hy, hxy⟩
    rwa [← U.injective hxy]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · haveI := hfd
    exact (U.toLinearEquiv.submoduleMap S).finiteDimensional
  · rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨σ₁ g x, hst g hg x hx, hU g hg x⟩
  · intro S'' hle hst''
    have hc := hmin (S''.comap f) (fun x hx => memS x (hle hx)) (fun g hg x hx => by
      show f (σ₁ g x) ∈ S''
      rw [hfU, hU g hg]
      exact hst'' g hg _ hx)
    have hsurj : Function.Surjective f := U.surjective
    rcases hc with h | h
    · left
      rw [← Submodule.map_comap_eq_of_surjective hsurj S'', h, Submodule.map_bot]
    · right
      rw [← Submodule.map_comap_eq_of_surjective hsurj S'', h]
  · refine ⟨U v, ⟨v, hvS, rfl⟩, fun h => hv0 (U.injective (by rw [h, map_zero])), fun θ hθ => ?_⟩
    rw [← hU _ hθ, hvw θ hθ, map_smul]
  · intro μ' w hw hw0 hww
    refine hdom μ' (U.symm w) ?_ ?_ ?_
    · obtain ⟨x, hx, rfl⟩ := hw
      rw [hfU, LinearIsometryEquiv.symm_apply_apply]
      exact hx
    · intro h
      apply hw0
      rw [← U.apply_symm_apply w, h, map_zero]
    · intro θ hθ
      rw [hback _ hθ, hww θ hθ, map_smul]

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def bwtDiag (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a => (θ a : ℂ) * Complex.I

theorem bwtDiag_inG (ε : Fin n → Bool) (θ : Fin n → ℝ) : inG ε (bwtDiag θ) := by
  show (bwtDiag θ)ᴴ * Jm ε + Jm ε * bwtDiag θ = 0
  rw [bwtDiag, Jm, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, ← Matrix.diagonal_zero]
  congr 1
  funext i
  by_cases hε : ε i = true <;> simp [hε, Complex.conj_I] <;> ring_nf

theorem bwt_exp (θ : Fin n → ℝ) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • bwtDiag θ) =
      Matrix.diagonal (fun a => Complex.exp (((t * θ a : ℝ) : ℂ) * Complex.I)) := by
  have h : (t : ℂ) • bwtDiag θ = Matrix.diagonal (fun a => (t : ℂ) * ((θ a : ℂ) * Complex.I)) := by
    rw [bwtDiag]
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, h]
  rw [h, Matrix.exp_diagonal]
  congr 1
  funext a
  rw [Pi.exp_def]
  dsimp only
  rw [← Complex.exp_eq_exp_ℂ]
  congr 1
  push_cast
  ring

theorem bwt_diag_mem_Kset (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    simp only [Pi.star_apply]
    rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
    simp
  · rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem bwt_actM_diag (E : Fin n → Fin n → Module.End ℂ M) (d : Fin n → ℂ) :
    actM E (Matrix.diagonal d) = ∑ a, d a • E a a := by
  simp [actM, Matrix.diagonal_apply, ite_smul]

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem bwt_actM_apply (θ : Fin n → ℝ) (v : D) :
    ((actM E (bwtDiag θ) v : D) : H) = ∑ a, ((θ a : ℂ) * Complex.I) • ((E a a v : D) : H) := by
  rw [bwtDiag, bwt_actM_diag]
  simp

private theorem exp_smul_bwtDiag_mem_UJset (ε : Fin n → Bool) (θ : Fin n → ℝ) (s : ℝ) :
    NormedSpace.exp ((s : ℂ) • bwtDiag θ) ∈ UJset ε := by
  have hK := bwt_diag_mem_Kset ε (fun a => s * θ a)
  obtain ⟨hu, hc⟩ := hK
  rw [bwt_exp]
  have hu' := Matrix.mem_unitaryGroup_iff'.1 hu
  have hJJ : Jm ε = Formalism.REAL.Jm ε := rfl
  show inUJ ε _
  unfold inUJ
  rw [hJJ, Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, hu',
    Matrix.one_mul]

private theorem apply_one_eq_exp_smul_of_hasDerivAt_smul {F : ℝ → H} {c : ℂ} (hF : ∀ s, HasDerivAt F (c • F s) s) :
    F 1 = Complex.exp c • F 0 := by
  have hG : ∀ s : ℝ, HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * -c) • F t) 0 s := by
    intro s
    have h1 := (((hasDerivAt_id' s).ofReal_comp).mul_const (-c)).cexp
    refine (h1.smul (hF s)).congr_deriv ?_
    rw [smul_smul, ← add_smul]
    simp
  have hconst := is_const_of_deriv_eq_zero (fun s => (hG s).differentiableAt)
    (fun s => (hG s).deriv) 1 0
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, neg_zero,
    Complex.exp_zero, one_smul] at hconst
  rw [← hconst, smul_smul, ← Complex.exp_add]
  simp

private theorem hasDerivAt_of_shift_of_hasDerivAt_zero {G : ℝ → H} {L : H} (T : ℝ → (H →L[ℂ] H))
    (hG0 : HasDerivAt G L 0) (hshift : ∀ s t, G (s + t) = T s (G t)) (s : ℝ) :
    HasDerivAt G (T s L) s := by
  have h1 := ((T s).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hG0
  have h2 : HasDerivAt (fun t => G (s + t)) (T s L) 0 := by
    convert h1 using 1 <;> first | rfl | (funext t; exact hshift s t)
  have h3 : HasDerivAt (fun t => G (s + t)) (T s L) (s - s) := by rwa [sub_self]
  have h4 := HasDerivAt.scomp (h := fun x : ℝ => x - s) s h3 ((hasDerivAt_id' s).sub_const s)
  convert h4 using 1 <;> first | (funext x; simp) | simp

theorem isWtOn_iff (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (v : D) (μ : Fin n → ℝ) :
    Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ (v : H) ↔ ∀ a, E a a v = ((μ a : ℝ) : ℂ) • v := by
  constructor
  · intro hw a
    have hder := hD.deriv _ (bwtDiag_inG ε (Pi.single a 1)) v
    have hfun : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • bwtDiag (Pi.single a 1))) (v : H)) =
        fun t : ℝ => Complex.exp ((t : ℂ) * ((μ a : ℂ) * Complex.I)) • (v : H) := by
      funext t
      have h := hw (fun b => t * (Pi.single a (1 : ℝ) : Fin n → ℝ) b) (bwt_diag_mem_Kset ε _)
      rw [bwt_exp, h]
      congr 2
      simp [Pi.single_apply] <;> ring
    rw [hfun, bwt_actM_apply] at hder
    have hexp : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * ((μ a : ℂ) * Complex.I)) • (v : H))
        (((μ a : ℂ) * Complex.I) • (v : H)) 0 := by
      have := ((((hasDerivAt_id' (0 : ℝ)).ofReal_comp).mul_const
        ((μ a : ℂ) * Complex.I)).cexp).smul_const (v : H)
      convert this using 1
      simp
    have heq := hder.unique hexp
    rw [Finset.sum_eq_single a (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)] at heq
    simp only [Pi.single_eq_same, Complex.ofReal_one, one_mul] at heq
    apply Subtype.ext
    have h2 : Complex.I • ((E a a v : D) : H) = Complex.I • (((μ a : ℝ) : ℂ) • (v : H)) := by
      rw [heq, smul_smul, mul_comm]
    exact smul_right_injective H Complex.I_ne_zero h2
  · intro hE θ _
    have hlam : ((actM E (bwtDiag θ) v : D) : H) =
        (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • (v : H) := by
      rw [bwt_actM_apply]
      have hterm : ∀ a, ((θ a : ℂ) * Complex.I) • ((E a a v : D) : H) =
          (((θ a : ℂ) * Complex.I) * (μ a : ℂ)) • (v : H) := by
        intro a
        rw [hE a, Submodule.coe_smul, smul_smul]
      rw [Finset.sum_congr rfl fun a _ => hterm a, ← Finset.sum_smul]
      congr 1
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by ring
    have h0 := hD.deriv _ (bwtDiag_inG ε θ) v
    rw [hlam] at h0
    have hshift : ∀ s t : ℝ, σ (NormedSpace.exp (((s + t : ℝ) : ℂ) • bwtDiag θ)) (v : H) =
        σ (NormedSpace.exp ((s : ℂ) • bwtDiag θ)) (σ (NormedSpace.exp ((t : ℂ) • bwtDiag θ)) (v : H)) := by
      intro s t
      have hmul : NormedSpace.exp (((s + t : ℝ) : ℂ) • bwtDiag θ) =
          NormedSpace.exp ((s : ℂ) • bwtDiag θ) * NormedSpace.exp ((t : ℂ) • bwtDiag θ) := by
        rw [Complex.ofReal_add, add_smul]
        exact Matrix.exp_add_of_commute _ _ (((Commute.refl (bwtDiag θ)).smul_left _).smul_right _)
      rw [hmul, hσ.1.2 _ (exp_smul_bwtDiag_mem_UJset ε θ s) _ (exp_smul_bwtDiag_mem_UJset ε θ t)]
      rfl
    have hF : ∀ s : ℝ, HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • bwtDiag θ)) (v : H))
        ((((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) •
          σ (NormedSpace.exp ((s : ℂ) • bwtDiag θ)) (v : H)) s := by
      intro s
      have := hasDerivAt_of_shift_of_hasDerivAt_zero (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • bwtDiag θ))) h0 hshift s
      rwa [map_smul] at this
    have hode := apply_one_eq_exp_smul_of_hasDerivAt_smul hF
    have e1 : NormedSpace.exp (((1 : ℝ) : ℂ) • bwtDiag θ) =
        Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) := by
      rw [bwt_exp]
      simp
    have e0 : NormedSpace.exp (((0 : ℝ) : ℂ) • bwtDiag θ) = 1 := by simp
    rw [e1, e0, hσ.1.1] at hode
    simpa using hode

end Rep

end ReciprocityTheory.ChartRestriction.DS
end
end
