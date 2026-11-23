module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.LatticeVectorsBoundedBelow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.Imports

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open Matrix

open scoped ComplexOrder

namespace Formalism.L2.SG.Pf.Tau

theorem re_star_dotProduct_self {m : ℕ} (z : Fin m → ℂ) :
    (star z ⬝ᵥ z).re = ∑ i, ‖z i‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re]

theorem star_dotProduct_gram {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℂ) (z : Fin k → ℂ) :
    star z ⬝ᵥ ((Aᴴ * A) *ᵥ z) = star (A *ᵥ z) ⬝ᵥ (A *ᵥ z) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]

theorem det_bounds_of_rayleigh {j : ℕ} (M : Matrix (Fin j) (Fin j) ℂ) (hM : M.IsHermitian) (a b : ℝ)
    (ha : 0 ≤ a)
    (h : ∀ z : Fin j → ℂ, a * ∑ i, ‖z i‖ ^ 2 ≤ (star z ⬝ᵥ (M *ᵥ z)).re ∧
      (star z ⬝ᵥ (M *ᵥ z)).re ≤ b * ∑ i, ‖z i‖ ^ 2) :
    ∃ μ : ℝ, M.det = μ ∧ a ^ j ≤ μ ∧ μ ≤ b ^ j := by
  have key : ∀ i, a ≤ hM.eigenvalues i ∧ hM.eigenvalues i ≤ b := by
    intro i
    set v : Fin j → ℂ := (hM.eigenvectorBasis i).ofLp with hv_def
    have hnorm : ∑ k, ‖v k‖ ^ 2 = 1 := by
      have h1 := (hM.eigenvectorBasis).norm_eq_one i
      rw [EuclideanSpace.norm_eq] at h1
      have h2 := congrArg (fun t : ℝ => t ^ 2) h1
      simp only [one_pow] at h2
      rwa [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h2
    have e : (star v ⬝ᵥ (M *ᵥ v)).re = hM.eigenvalues i := by
      rw [hv_def, hM.mulVec_eigenvectorBasis i, dotProduct_smul, Complex.smul_re, smul_eq_mul,
        ← hv_def, re_star_dotProduct_self, hnorm, mul_one]
    have := h v
    rw [e, hnorm, mul_one, mul_one] at this
    exact this
  refine ⟨∏ i, hM.eigenvalues i, ?_, ?_, ?_⟩
  · rw [hM.det_eq_prod_eigenvalues]
    norm_cast
  · calc a ^ j = ∏ _i : Fin j, a := by simp
      _ ≤ ∏ i, hM.eigenvalues i := Finset.prod_le_prod₀ (fun _ _ => ha) (fun i _ => (key i).1)
  · calc ∏ i, hM.eigenvalues i ≤ ∏ _i : Fin j, b :=
          Finset.prod_le_prod₀ (fun i _ => ha.trans (key i).1) (fun i _ => (key i).2)
      _ = b ^ j := by simp

theorem exists_mul_mul_conjTranspose_eq_one {j : ℕ} {G : Matrix (Fin j) (Fin j) ℂ} (hG : G.PosDef) :
    ∃ S : Matrix (Fin j) (Fin j) ℂ, S * G * Sᴴ = 1 := by
  have hH := hG.isHermitian
  set U : Matrix (Fin j) (Fin j) ℂ := (hH.eigenvectorUnitary : Matrix (Fin j) (Fin j) ℂ) with hU_def
  have hU : star U * U = 1 := by simp [U]
  have hspec : G = U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U := by
    have := hH.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at this
  have hpos : ∀ i, 0 < hH.eigenvalues i := hG.eigenvalues_pos
  refine ⟨diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) * star U, ?_⟩
  rw [show (diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) * star U) * G *
      (diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) * star U)ᴴ =
      (diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) * star U) *
      (U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U) *
      (diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) * star U)ᴴ by rw [← hspec]]
  rw [conjTranspose_mul, Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose,
    ← Matrix.star_eq_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star U) U, hU, Matrix.one_mul, ← Matrix.mul_assoc (star U) U, hU, Matrix.one_mul,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  have hs : 0 < Real.sqrt (hH.eigenvalues i) := Real.sqrt_pos.2 (hpos i)
  have hsq : Real.sqrt (hH.eigenvalues i) ^ 2 = hH.eigenvalues i := Real.sq_sqrt (hpos i).le
  have h1 : (Real.sqrt (hH.eigenvalues i))⁻¹ * hH.eigenvalues i * (Real.sqrt (hH.eigenvalues i))⁻¹ = 1 := by
    rw [show (Real.sqrt (hH.eigenvalues i))⁻¹ * hH.eigenvalues i * (Real.sqrt (hH.eigenvalues i))⁻¹
        = hH.eigenvalues i * (Real.sqrt (hH.eigenvalues i) ^ 2)⁻¹ by ring, hsq, mul_inv_cancel₀ (hpos i).ne']
  simp only [Function.comp, Pi.star_apply, RCLike.star_def, Complex.conj_ofReal]
  rw [← mul_assoc]
  have h2 := congrArg (fun t : ℝ => (t : ℂ)) h1
  push_cast at h2
  simpa using h2

theorem det_gram_mul_eq_zero {n j : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin n) (Fin j) ℂ)
    (hd : (Cᴴ * C).det = 0) : ((Y * C)ᴴ * (Y * C)).det = 0 := by
  obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  have hCz : C *ᵥ z = 0 := by
    have h1 : star z ⬝ᵥ ((Cᴴ * C) *ᵥ z) = 0 := by rw [hz, dotProduct_zero]
    rw [star_dotProduct_gram] at h1
    exact dotProduct_star_self_eq_zero.mp h1
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨z, hz0, ?_⟩
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hCz, Matrix.mulVec_zero, Matrix.mulVec_zero]

theorem t5 : GramDistortionBound := by
  intro n j Y C a b ha hY
  by_cases hd : (Cᴴ * C).det = 0
  · rw [hd, det_gram_mul_eq_zero Y C hd]
    simp
  have hPS : (Cᴴ * C).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self C
  have hPD : (Cᴴ * C).PosDef := hPS.posDef_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd))
  obtain ⟨S, hS⟩ := exists_mul_mul_conjTranspose_eq_one hPD
  set V := C * Sᴴ with hV_def
  have hV : Vᴴ * V = 1 := by
    rw [hV_def, conjTranspose_mul, conjTranspose_conjTranspose]
    rw [show S * Cᴴ * (C * Sᴴ) = S * (Cᴴ * C) * Sᴴ by simp only [Matrix.mul_assoc]]
    exact hS
  set M := (Y * V)ᴴ * (Y * V) with hM_def
  have hMH : M.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self _
  have hray : ∀ z : Fin j → ℂ, a * ∑ i, ‖z i‖ ^ 2 ≤ (star z ⬝ᵥ (M *ᵥ z)).re ∧
      (star z ⬝ᵥ (M *ᵥ z)).re ≤ b * ∑ i, ‖z i‖ ^ 2 := by
    intro z
    have e1 : (star z ⬝ᵥ (M *ᵥ z)).re = ∑ i, ‖((Y * V) *ᵥ z) i‖ ^ 2 := by
      rw [hM_def, star_dotProduct_gram, re_star_dotProduct_self]
    have e2 : ∑ i, ‖(V *ᵥ z) i‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
      rw [← re_star_dotProduct_self, ← star_dotProduct_gram, hV, Matrix.one_mulVec, re_star_dotProduct_self]
    have := hY (V *ᵥ z)
    rw [Matrix.mulVec_mulVec, e2] at this
    rw [e1]
    exact this
  obtain ⟨μ, hμ, h1, h2⟩ := det_bounds_of_rayleigh M hMH a b ha hray
  have hMeq : M = S * ((Y * C)ᴴ * (Y * C)) * Sᴴ := by
    simp only [hM_def, hV_def, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hdet1 : S.det * (Cᴴ * C).det * Sᴴ.det = 1 := by
    rw [← det_mul, ← det_mul, hS, det_one]
  have hdY : ((Y * C)ᴴ * (Y * C)).det = μ * (Cᴴ * C).det := by
    calc ((Y * C)ᴴ * (Y * C)).det
        = ((Y * C)ᴴ * (Y * C)).det * (S.det * (Cᴴ * C).det * Sᴴ.det) := by rw [hdet1, mul_one]
      _ = (S.det * ((Y * C)ᴴ * (Y * C)).det * Sᴴ.det) * (Cᴴ * C).det := by ring
      _ = μ * (Cᴴ * C).det := by rw [← det_mul, ← det_mul, ← hMeq, hμ]
  have hG0 := hPS.det_nonneg
  rw [Complex.nonneg_iff] at hG0
  have hre : ((Y * C)ᴴ * (Y * C)).det.re = μ * (Cᴴ * C).det.re := by
    rw [hdY, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hre]
  exact ⟨mul_le_mul_of_nonneg_right h1 hG0.1, mul_le_mul_of_nonneg_right h2 hG0.1⟩

end Formalism.L2.SG.Pf.Tau
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem exists_ne_zero_mem_L (I : AutInst) (hn : 1 ≤ I.n) : ∃ l ∈ I.L, l ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have h := I.L_span
  have h0 : Submodule.span I.E (I.L : Set (Fin I.n → I.E)) = ⊥ := by
    rw [Submodule.span_eq_bot]
    exact hcon
  rw [h0] at h
  haveI : Nonempty (Fin I.n) := ⟨⟨0, hn⟩⟩
  exact bot_ne_top h

theorem third_estimate_of_first_two (h0 : LatticeCommensurable) (h1 : LatticeFinitelyGenerated) : SubmoduleExists := by
  intro I hn x
  obtain ⟨m, hm1, _, hLm⟩ := h0 I x
  obtain ⟨M, _, hM⟩ := h1 I x
  obtain ⟨l, hlL, hl0⟩ := exists_ne_zero_mem_L I hn
  have hml : ((m : I.E) • l) ∈ (M : Set (Fin I.n → I.E)) := by
    rw [hM]
    exact hLm l hlL
  have hm0 : ((m : I.E) • l) ≠ 0 := smul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) hl0
  obtain ⟨t, htM, hspan, hli⟩ := exists_linearIndependent I.E (M : Set (Fin I.n → I.E))
  have htfin : t.Finite := hli.setFinite
  have hne : t.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Submodule.span_empty] at hspan
    have h2 : ((m : I.E) • l) ∈ Submodule.span I.E (M : Set (Fin I.n → I.E)) := Submodule.subset_span hml
    rw [← hspan] at h2
    exact hm0 ((Submodule.mem_bot _).mp h2)
  haveI := htfin.fintype
  let e := (Fintype.equivFin t).symm
  refine ⟨⟨Fintype.card t, ?_, fun a => (e a : Fin I.n → I.E), ?_, M, ?_, ?_, ?_⟩⟩
  · exact Fintype.card_pos_iff.mpr hne.to_subtype
  · exact hli.comp _ e.injective
  · exact hM.le
  · intro a
    exact htM (e a).2
  · intro v hv
    have hr : Set.range (fun a => (e a : Fin I.n → I.E)) = t := by
      ext v
      constructor
      · rintro ⟨a, rfl⟩
        exact (e a).2
      · intro hv
        exact ⟨e.symm ⟨v, hv⟩, by simp⟩
    rw [hr, hspan]
    exact Submodule.subset_span hv

end Formalism.L2.SG.Pf.Tau
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem inclE_mem_intAf (I : AutInst) (c : 𝓞 I.E) :
    Formalism.UG.inclE (F := I.F) (Af I.F) (c : I.E) ∈ IntAf I.F I.E := by
  apply Subring.subset_closure
  left
  exact ⟨⟨(c : I.E), c, rfl⟩, rfl⟩

def latSubmodule (I : AutInst) (x : I.GA) : Submodule (𝓞 I.E) (Fin I.n → I.E) where
  carrier := latSet I x
  zero_mem' := by
    show (I.fmat x.2⁻¹) *ᵥ _ ∈ I.Lf
    have : (fun i : Fin I.n => Formalism.UG.inclE (F := I.F) (Af I.F) ((0 : Fin I.n → I.E) i)) = 0 := by
      funext i; simp
    rw [this, Matrix.mulVec_zero]
    exact I.Lf.zero_mem
  add_mem' := by
    intro u w hu hw
    show (I.fmat x.2⁻¹) *ᵥ _ ∈ I.Lf
    have h : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((u + w) i)) =
        (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (u i)) +
          (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (w i)) := by
      funext i; simp
    rw [h, Matrix.mulVec_add]
    exact I.Lf.add_mem hu hw
  smul_mem' := by
    intro c u hu
    show (I.fmat x.2⁻¹) *ᵥ _ ∈ I.Lf
    have h : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((c • u) i)) =
        Formalism.UG.inclE (F := I.F) (Af I.F) (c : I.E) •
          (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (u i)) := by
      funext i
      simp [Algebra.smul_def]
    rw [h, Matrix.mulVec_smul]
    have := I.Lf.smul_mem (⟨_, inclE_mem_intAf I c⟩ : IntAf I.F I.E) hu
    exact this

theorem coe_latSubmodule (I : AutInst) (x : I.GA) :
    ((latSubmodule I x : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (Fin I.n → I.E)) = latSet I x := rfl

theorem lattice_finitelyGenerated_of_commensurable (h0 : LatticeCommensurable) : LatticeFinitelyGenerated := by
  intro I x
  obtain ⟨m, hm1, hA, -⟩ := h0 I x
  refine ⟨latSubmodule I x, ?_, coe_latSubmodule I x⟩
  have hm0 : (m : I.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  let φ : (Fin I.n → I.E) →ₗ[𝓞 I.E] (Fin I.n → I.E) :=
    (((m : I.E)⁻¹ • LinearMap.id : (Fin I.n → I.E) →ₗ[I.E] (Fin I.n → I.E))).restrictScalars (𝓞 I.E)
  have hle : latSubmodule I x ≤ I.L.map φ := by
    intro u hu
    refine ⟨(m : I.E) • u, hA u hu, ?_⟩
    simp [φ, smul_smul, inv_mul_cancel₀ hm0]
  have hfg : (I.L.map φ).FG := I.L_fg.map φ
  haveI := isNoetherian_of_fg_of_noetherian _ hfg
  have h1 := IsNoetherian.noetherian ((latSubmodule I x).comap (I.L.map φ).subtype)
  have h2 := h1.map (I.L.map φ).subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.2 hle] at h2

end Formalism.L2.SG.Pf.Tau
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem kset_inv_mem (I : AutInst) {k : I.Gf} (hk : k ∈ I.Kset) : k⁻¹ ∈ I.Kset := by
  exact (Formalism.UG.stabGL I.Lf).inv_mem hk

theorem t4 : LatticeRightInvariant := by
  intro I x y k hk
  ext u
  show (I.fmat (x * (y, k)).2⁻¹) *ᵥ _ ∈ I.Lf ↔ (I.fmat x.2⁻¹) *ᵥ _ ∈ I.Lf
  have hk' : ∀ w, w ∈ I.Lf ↔ I.fmat k⁻¹ *ᵥ w ∈ I.Lf := kset_inv_mem I hk
  have e : I.fmat (x * (y, k)).2⁻¹ = I.fmat k⁻¹ * I.fmat x.2⁻¹ := by
    simp only [AutInst.fmat, Prod.snd_mul, _root_.mul_inv_rev, Subgroup.coe_mul, Units.val_mul]
  rw [e, ← Matrix.mulVec_mulVec]
  exact (hk' _).symm

end Formalism.L2.SG.Pf.Tau
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField

namespace Formalism.L2.SG.Pf.Tau

theorem t2 : ExistsBoundedBasis := by
  intro K _ _ n j M B b hM hBM hli hbB hBspan
  classical
  have hBfg : B.FG := by
    haveI := isNoetherian_of_fg_of_noetherian M hM
    have h1 : (B.comap M.subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map M.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hBM] at h2
  obtain ⟨s, hs⟩ := hBfg
  have hcoef : ∀ g ∈ s, ∃ c : Fin j → K, ∑ a, c a • b a = g := fun g hg =>
    (Submodule.mem_span_range_iff_exists_fun K).mp (hBspan (hs ▸ Submodule.subset_span hg))
  choose! c hc using hcoef
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    ((s ×ˢ Finset.univ).image (fun p : (Fin n → K) × Fin j => c p.1 p.2))
  have hyg : ∀ g ∈ s, (y : ℤ) • g ∈ Submodule.span (𝓞 K) (Set.range b) := by
    intro g hg
    rw [← hc g hg, Finset.smul_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    have hint : IsIntegral ℤ (y • c g a) :=
      hy _ (Finset.mem_image.mpr ⟨(g, a), Finset.mem_product.mpr ⟨hg, Finset.mem_univ a⟩, rfl⟩)
    have e : (y : ℤ) • (c g a • b a) = (⟨y • c g a, hint⟩ : 𝓞 K) • b a := by
      rw [← smul_assoc]
      rfl
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have hyB : ∀ v ∈ B, (y : ℤ) • v ∈ Submodule.span (𝓞 K) (Set.range b) := by
    rw [← hs]
    intro v hv
    refine Submodule.span_induction (fun g hg => hyg g hg) (by simp)
      (fun u w _ _ hu hw => by rw [smul_add]; exact add_mem hu hw)
      (fun o u _ hu => by rw [smul_comm]; exact Submodule.smul_mem _ o hu) hv
  haveI : Module.Finite (𝓞 K) B := Module.Finite.iff_fg.mpr ⟨s, hs⟩
  haveI : Module.Finite ℤ (B ⧸ (Submodule.span (𝓞 K) (Set.range b)).comap B.subtype) :=
    Module.Finite.trans (𝓞 K) _
  apply Module.finite_of_fg_torsion
  intro q
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective ((Submodule.span (𝓞 K) (Set.range b)).comap B.subtype) q
  refine ⟨⟨y, mem_nonZeroDivisors_of_ne_zero hy0⟩, ?_⟩
  show (y : ℤ) • (Submodule.Quotient.mk (p := (Submodule.span (𝓞 K) (Set.range b)).comap B.subtype) v) = 0
  have hz := map_zsmul (Submodule.mkQ ((Submodule.span (𝓞 K) (Set.range b)).comap B.subtype)) y v
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at hz
  rw [← hz, Submodule.Quotient.mk_eq_zero]
  exact hyB v v.2

end Formalism.L2.SG.Pf.Tau
end
end

section

set_option autoImplicit false

noncomputable section

open MeasureTheory Metric

namespace Formalism.L2.SG.Pf.Tau

theorem t8m : MinkowskiFirstTheorem := by
  intro d hd
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by simp
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (by rw [hfr]; omega)
  set v1 : ℝ := (volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal with hv1_def
  have hv1ne : volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hv1pos : 0 < v1 :=
    ENNReal.toReal_pos (measure_ball_pos _ _ one_pos).ne' hv1ne
  refine ⟨4 / v1 ^ ((2 : ℝ) / d), by positivity, ?_⟩
  intro L _ _
  let b := Module.Free.chooseBasis ℤ L
  have hF := ZLattice.isAddFundamentalDomain b (volume : Measure (EuclideanSpace ℝ (Fin d)))
  set F := ZSpan.fundamentalDomain (Module.Basis.ofZLatticeBasis ℝ L b) with hF_def
  have hcov : ZLattice.covolume L = volume.real F := ZLattice.covolume_eq_measure_fundamentalDomain L volume hF
  have hcov0 : 0 ≤ ZLattice.covolume L := by rw [hcov]; exact measureReal_nonneg
  have hFfin : volume F ≠ ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  set r : ℝ := 2 * (ZLattice.covolume L / v1) ^ ((1 : ℝ) / d) with hr_def
  have hr0 : 0 ≤ r := by positivity
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hq0 : 0 ≤ ZLattice.covolume L / v1 := by positivity
  have key : ∀ t : ℝ, 0 ≤ t → (t ^ ((1 : ℝ) / d)) ^ d = t := fun t ht => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht, one_div_mul_cancel hdpos.ne', Real.rpow_one]
  have key2 : ∀ t : ℝ, 0 ≤ t → (t ^ ((1 : ℝ) / d)) ^ 2 = t ^ ((2 : ℝ) / d) := fun t ht => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
    congr 1
    push_cast
    ring
  have hrd : r ^ d = 2 ^ d * (ZLattice.covolume L / v1) := by
    rw [hr_def, mul_pow, key _ hq0]
  have hvol : volume F * 2 ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin d))
      ≤ volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) r) := by
    rw [Measure.addHaar_closedBall volume 0 hr0, hfr, hrd, ← ENNReal.ofReal_toReal hv1ne, ← hv1_def,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_toReal hFfin]
    have : (volume F).toReal = ZLattice.covolume L := by rw [hcov]; rfl
    have e : (2 : ℝ) ^ d * (ZLattice.covolume L / v1) * v1 = ZLattice.covolume L * 2 ^ d := by
      field_simp
    rw [this, e, ENNReal.ofReal_mul hcov0, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_ofNat]
  haveI hcL : Countable L := Countable.of_equiv _ b.repr.toEquiv.symm
  haveI : Countable L.toAddSubgroup := hcL
  haveI : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
  obtain ⟨x, hx0, hxs⟩ := MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
    (L := L.toAddSubgroup) hF (fun y hy => by simpa using hy) (convex_closedBall _ _)
    (isCompact_closedBall _ _) hvol
  refine ⟨x, x.2, fun h => hx0 (Subtype.ext h), ?_⟩
  have hxr : ‖(x : EuclideanSpace ℝ (Fin d))‖ ≤ r := by simpa using hxs
  calc ‖(x : EuclideanSpace ℝ (Fin d))‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxr 2
    _ = 4 / v1 ^ ((2 : ℝ) / d) * ZLattice.covolume L ^ ((2 : ℝ) / d) := by
      rw [hr_def, mul_pow, key2 _ hq0, Real.div_rpow hcov0 hv1pos.le]
      ring
  exact le_rfl

end Formalism.L2.SG.Pf.Tau
end
end
