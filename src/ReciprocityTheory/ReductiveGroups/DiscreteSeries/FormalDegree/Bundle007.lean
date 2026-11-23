module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.PolarJmConjTranspose
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HasDerivAtMexpCommAddBracket
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Order
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarBasicA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.ProdSubLtEqFactorial
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.DetPbB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.JacobianLeExp

@[expose] public section

section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem exp_pmat_inUJ {ε : Fin n → Bool} (z : PCoord ε → ℂ) : inUJ ε (NormedSpace.exp (pmat z)) := by
  have h := inUJ_kexp (1 : KG ε) (pmat_inP z)
  have e : toMK (1 : KG ε) = 1 := rfl
  rwa [e, Matrix.one_mul] at h

theorem polarM_inUJ {ε : Fin n → Bool} (kz : KG ε × (PCoord ε → ℂ)) : inUJ ε (polarM kz) :=
  inUJ_kexp kz.1 (pmat_inP kz.2)

theorem pmat_injective (ε : Fin n → Bool) : Function.Injective (pmat (ε := ε)) := by
  intro z z' h
  funext ab
  have := congrFun (congrFun h ab.1.1) ab.1.2
  simpa [pmat, dif_pos ab.2] using this

theorem polarM_injective (ε : Fin n → Bool) : Function.Injective (polarM (ε := ε)) := by
  rintro ⟨k, z⟩ ⟨k', z'⟩ h
  obtain ⟨hk, hX⟩ := polar_unique (pmat_inP z) (pmat_inP z')
    (show toMK k * NormedSpace.exp (pmat z) = toMK k' * NormedSpace.exp (pmat z') from h)
  rw [hk, pmat_injective ε hX]

theorem polarM_surj {ε : Fin n → Bool} (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) :
    ∃ kz : KG ε × (PCoord ε → ℂ), polarM kz = g := by
  obtain ⟨k, X, hX, rfl⟩ := polar_exists hg
  refine ⟨(k, fun ab => X ab.1.1 ab.1.2), ?_⟩
  show toMK k * NormedSpace.exp (pmat fun ab : PCoord ε => X ab.1.1 ab.1.2) = _
  rw [pmat_coords X hX]

open scoped Matrix.Norms.L2Operator in
theorem polarL_continuousOn (ε : Fin n → Bool) :
    ContinuousOn (PolarDecomposition.polar_L (n := n)) {g | inUJ ε g} := by
  have h : ContinuousOn (fun g : Matrix (Fin n) (Fin n) ℂ => CFC.log (gᴴ * g)) {g | inUJ ε g} := by
    refine CFC.continuousOn_log.comp (by fun_prop) ?_
    intro g hg
    obtain ⟨hsa, hu, -⟩ := PolarDecomposition.polar_isSelfAdjoint_isUnit_spectrum_pos hg
    exact ⟨hsa, hu⟩
  exact h.const_smul (1 / 2 : ℝ)

section Emb

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem polarM_continuous (ε : Fin n → Bool) : Continuous (polarM (ε := ε)) := by
  unfold polarM
  exact ((continuous_toM ε).comp (continuous_subtype_val.comp continuous_fst)).mul
    (NormedSpace.exp_continuous.comp ((pmat_continuous ε).comp continuous_snd))

def polarInvK (ε : Fin n → Bool) (g : UJset ε) : KG ε :=
  Classical.choose (exists_toMK (PolarDecomposition.polar_k_mem (ε := ε) (g := g.1) g.2))

theorem toMK_polarInvK (ε : Fin n → Bool) (g : UJset ε) :
    toMK (polarInvK ε g) = g.1 * NormedSpace.exp (-PolarDecomposition.polar_L g.1) :=
  Classical.choose_spec (exists_toMK (PolarDecomposition.polar_k_mem (ε := ε) (g := g.1) g.2))

def polarInv (ε : Fin n → Bool) (g : UJset ε) : KG ε × (PCoord ε → ℂ) :=
  (polarInvK ε g, fun ab => PolarDecomposition.polar_L g.1 ab.1.1 ab.1.2)

theorem polarM_polarInv (ε : Fin n → Bool) (g : UJset ε) : polarM (polarInv ε g) = g.1 := by
  show toMK (polarInvK ε g) * NormedSpace.exp (pmat fun ab : PCoord ε => PolarDecomposition.polar_L g.1 ab.1.1 ab.1.2) = g.1
  rw [pmat_coords _ (PolarDecomposition.polar_L_inP (ε := ε) (g := g.1) g.2), toMK_polarInvK]
  exact PolarDecomposition.eq_mul_exp_neg_polar_L_mul_exp_polar_L.symm

theorem polarInv_continuous (ε : Fin n → Bool) : Continuous (polarInv ε) := by
  have hL : Continuous fun g : UJset ε => PolarDecomposition.polar_L g.1 :=
    (polarL_continuousOn ε).comp_continuous continuous_subtype_val (fun g => g.2)
  have hind : Topology.IsInducing (fun k : KG ε => toMK k) :=
    (isClosedEmbedding_toM ε).isInducing.comp Topology.IsInducing.subtypeVal
  have hK : Continuous (polarInvK ε) := by
    rw [hind.continuous_iff]
    have : (fun k : KG ε => toMK k) ∘ polarInvK ε =
        fun g : UJset ε => g.1 * NormedSpace.exp (-PolarDecomposition.polar_L g.1) := by
      funext g; exact toMK_polarInvK ε g
    rw [this]
    exact continuous_subtype_val.mul (NormedSpace.exp_continuous.comp hL.neg)
  exact hK.prodMk (continuous_pi fun ab => hL.matrix_elem ab.1.1 ab.1.2)

def polarHomeo (ε : Fin n → Bool) : KG ε × (PCoord ε → ℂ) ≃ₜ UJset ε where
  toFun kz := ⟨polarM kz, polarM_inUJ kz⟩
  invFun := polarInv ε
  left_inv kz := polarM_injective ε (polarM_polarInv ε ⟨polarM kz, polarM_inUJ kz⟩)
  right_inv g := Subtype.ext (polarM_polarInv ε g)
  continuous_toFun := (polarM_continuous ε).subtype_mk _
  continuous_invFun := polarInv_continuous ε

theorem polarM_isClosedEmbedding (ε : Fin n → Bool) : Topology.IsClosedEmbedding (polarM (ε := ε)) := by
  have h : Topology.IsClosedEmbedding ((Subtype.val : UJset ε → Matrix (Fin n) (Fin n) ℂ) ∘ polarHomeo ε) :=
    (isClosed_inUJ ε).isClosedEmbedding_subtypeVal.comp (polarHomeo ε).isClosedEmbedding
  exact h

end Emb

theorem jac_continuous (ε : Fin n → Bool) : Continuous (fun z : PCoord ε → ℂ => Jac z) :=
  pb_jac_continuous ε

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdS_strictAnti {lam : Fin n → ℝ} (hlam : StrictAnti lam) {c : Fin n → ℕ} (hc : Antitone c) :
    StrictAnti (lam + fun i => (c i : ℝ)) := by
  intro i j hij
  simp only [Pi.add_apply]
  exact add_lt_add_of_lt_of_le (hlam hij) (by exact_mod_cast hc hij.le)

theorem fdS_hc {lam : Fin n → ℝ} (hlam : IsHCParam lam) {c : Fin n → ℕ} (hc : Antitone c) :
    IsHCParam (lam + fun i => (c i : ℝ)) := by
  unfold IsHCParam at hlam ⊢
  refine ⟨fdS_strictAnti hlam.1 hc, fun a => ?_⟩
  obtain ⟨m, hm⟩ := hlam.2 a
  refine ⟨m + (c a : ℤ), ?_⟩
  simp only [Pi.add_apply]
  push_cast
  linarith

theorem fdS_gap {ε : Fin n → Bool} {h : ℝ} {lam : Fin n → ℝ} (hlam : StrictAnti lam)
    (hgap : GapAtLeast ε lam h) {c : Fin n → ℕ} (hc : Antitone c) :
    GapAtLeast ε (lam + fun i => (c i : ℝ)) h := by
  unfold GapAtLeast at hgap ⊢
  intro a b hab
  have h0 := hgap a b hab
  simp only [Pi.add_apply]
  rcases lt_trichotomy a b with hlt | heq | hgt
  · have h1 := hlam hlt
    have h2 : (c b : ℝ) ≤ c a := by exact_mod_cast hc hlt.le
    rw [abs_of_pos (by linarith)] at h0
    rw [abs_of_pos (by linarith)]
    linarith
  · exact absurd (congrArg ε heq) hab
  · have h1 := hlam hgt
    have h2 : (c a : ℝ) ≤ c b := by exact_mod_cast hc hgt.le
    rw [abs_of_neg (by linarith)] at h0
    rw [abs_of_neg (by linarith)]
    linarith

private theorem vand_ne_zero_of_strictAnti {μ : Fin n → ℝ} (hμ : StrictAnti μ) : Vand μ ≠ 0 := by
  unfold Vand
  refine Finset.prod_ne_zero_iff.mpr (fun a _ => Finset.prod_ne_zero_iff.mpr (fun b hb => ?_))
  have hab : a < b := (Finset.mem_filter.mp hb).2
  exact sub_ne_zero.mpr (hμ hab).ne'

theorem fdS_stepQ {ε : Fin n → Bool} {h : ℝ} (dfun : (Fin n → ℝ) → ℝ)
    (hstep : ∀ (μ : Fin n → ℝ) (s : Fin n), IsHCParam μ → GapAtLeast ε μ h → GapAtLeast ε (μ + Pi.single s 1) h →
      StrictAnti (μ + Pi.single s 1) → dfun (μ + Pi.single s 1) = dfun μ * ratioV μ s)
    {μ : Fin n → ℝ} (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h) (s : Fin n)
    (hg' : GapAtLeast ε (μ + Pi.single s 1) h) (hs : StrictAnti (μ + Pi.single s 1)) :
    dfun (μ + Pi.single s 1) / Vand (μ + Pi.single s 1) = dfun μ / Vand μ := by
  have hμ1 : StrictAnti μ := by unfold IsHCParam at hμ; exact hμ.1
  rw [hstep μ s hμ hg hg' hs, ratioV_eq_vand hμ1 s]
  have h1 := vand_ne_zero_of_strictAnti hμ1
  have h2 := vand_ne_zero_of_strictAnti hs
  field_simp

theorem fdS_main {ε : Fin n → Bool} {h : ℝ} (dfun : (Fin n → ℝ) → ℝ)
    (hstep : ∀ (μ : Fin n → ℝ) (s : Fin n), IsHCParam μ → GapAtLeast ε μ h → GapAtLeast ε (μ + Pi.single s 1) h →
      StrictAnti (μ + Pi.single s 1) → dfun (μ + Pi.single s 1) = dfun μ * ratioV μ s)
    {lam : Fin n → ℝ} (hlam : IsHCParam lam) (hgap : GapAtLeast ε lam h) :
    ∀ (N : ℕ) (c : Fin n → ℕ), Antitone c → ∑ i, c i = N →
      dfun (lam + fun i => (c i : ℝ)) / Vand (lam + fun i => (c i : ℝ)) = dfun lam / Vand lam := by
  have hlam1 : StrictAnti lam := by unfold IsHCParam at hlam; exact hlam.1
  intro N
  induction N with
  | zero =>
    intro c _ hsum
    have hc0 : ∀ i, c i = 0 := fun i => (Finset.sum_eq_zero_iff.mp hsum) i (Finset.mem_univ i)
    have hfun : (lam + fun i => (c i : ℝ)) = lam := by
      funext i
      simp [hc0 i]
    rw [hfun]
  | succ N ih =>
    intro c hc hsum
    have hne : (univ.filter (fun i => c i ≠ 0)).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hemp
      have h0 : ∑ i, c i = 0 := Finset.sum_eq_zero (fun i hi => by simpa using hemp hi)
      omega
    obtain ⟨s, hs_mem, hs_max⟩ : ∃ s ∈ univ.filter (fun i => c i ≠ 0), ∀ j ∈ univ.filter (fun i => c i ≠ 0), j ≤ s :=
      ⟨_, Finset.max'_mem _ hne, fun j hj => Finset.le_max' _ j hj⟩
    have hcs : c s ≠ 0 := (Finset.mem_filter.mp hs_mem).2
    have hbig : ∀ j, s < j → c j = 0 := by
      intro j hj
      by_contra hcj
      exact absurd hj (not_lt.mpr (hs_max j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcj⟩)))
    set c' : Fin n → ℕ := fun i => if i = s then c i - 1 else c i with hc'_def
    have hcc : ∀ i, c i = c' i + (if i = s then 1 else 0) := by
      intro i
      simp only [hc'_def]
      by_cases h : i = s
      · rw [if_pos h, if_pos h, h]; omega
      · rw [if_neg h, if_neg h]; rfl
    have hc' : Antitone c' := by
      intro i j hij
      simp only [hc'_def]
      rcases eq_or_ne i s with hi | hi <;> rcases eq_or_ne j s with hj | hj
      · rw [hi, hj]
      · have hsj : s < j := lt_of_le_of_ne (hi ▸ hij) (Ne.symm hj)
        rw [if_neg hj, hbig j hsj]
        exact Nat.zero_le _
      · have h' := hc hij
        rw [if_pos hj, if_neg hi]
        omega
      · rw [if_neg hj, if_neg hi]
        exact hc hij
    have hsum' : ∑ i, c' i = N := by
      have h' : ∑ i, c i = ∑ i, c' i + 1 := by
        rw [Finset.sum_congr rfl (fun i _ => hcc i), Finset.sum_add_distrib]
        simp
      omega
    have hfun : (lam + fun i => (c' i : ℝ)) + Pi.single s 1 = lam + fun i => (c i : ℝ) := by
      funext i
      simp only [Pi.add_apply, Pi.single_apply]
      rw [hcc i]
      push_cast
      split_ifs <;> ring
    have hQ := fdS_stepQ dfun hstep (fdS_hc hlam hc') (fdS_gap hlam1 hgap hc') s
      (by rw [hfun]; exact fdS_gap hlam1 hgap hc) (by rw [hfun]; exact fdS_strictAnti hlam1 hc)
    rw [hfun] at hQ
    rw [hQ, ih c' hc' hsum']

theorem fd_step {ε : Fin n → Bool} {h : ℝ} (dfun : (Fin n → ℝ) → ℝ)
    (hstep : ∀ (μ : Fin n → ℝ) (s : Fin n), IsHCParam μ → GapAtLeast ε μ h →
      GapAtLeast ε (μ + Pi.single s 1) h → StrictAnti (μ + Pi.single s 1) → dfun (μ + Pi.single s 1) = dfun μ * ratioV μ s)
    {lam : Fin n → ℝ} (hlam : IsHCParam lam) (hgap : GapAtLeast ε lam h) (t : ℕ) :
    dfun (lamT lam t) / Vand (lamT lam t) = dfun lam / Vand lam := by
  have hD : ∀ a : Fin n, ((n : ℝ) - 1) - ((a : ℕ) : ℝ) = ((n - 1 - (a : ℕ) : ℕ) : ℝ) := by
    intro a
    have ha := a.2
    rw [Nat.cast_sub (by omega : (a : ℕ) ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hc : Antitone (fun a : Fin n => t * (n - 1 - (a : ℕ))) := by
    intro i j hij
    have h' := Fin.le_iff_val_le_val.mp hij
    exact Nat.mul_le_mul le_rfl (by omega)
  have hfun : lamT lam t = lam + fun i => (((fun a : Fin n => t * (n - 1 - (a : ℕ))) i : ℕ) : ℝ) := by
    funext i
    simp only [lamT, Pi.add_apply, Pi.smul_apply, Dvec, smul_eq_mul]
    rw [hD i]
    push_cast
    ring
  rw [hfun]
  exact fdS_main dfun hstep hlam hgap _ _ hc rfl

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def detPaCj (P Q : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun W := P * W * Q
  map_add' A B := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by simp

def detPaRow (t : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.pi (fun j => (t j • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)).comp (LinearMap.proj j))

def detPaHad (s : Fin n → Fin n → ℂ) : (Fin n → Fin n → ℂ) →ₗ[ℂ] (Fin n → Fin n → ℂ) :=
  LinearMap.pi (fun i => (detPaRow (s i)).comp (LinearMap.proj i))

theorem detPaRow_det (t : Fin n → ℂ) : LinearMap.det (detPaRow t) = ∏ j, t j := by
  unfold detPaRow
  rw [LinearMap.det_pi]
  simp

theorem detPaHad_det (s : Fin n → Fin n → ℂ) : LinearMap.det (detPaHad s) = ∏ i, ∏ j, s i j := by
  unfold detPaHad
  rw [LinearMap.det_pi]
  simp [detPaRow_det]

theorem detPa {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    LinearMap.det ((fderiv ℝ (shcAd y) 0 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) =
      ∏ i, ∏ j, shc (pev y i - pev y j) ^ 2 := by
  set U : Matrix (Fin n) (Fin n) ℂ := ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  have hmem : U ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := ((pmat_isHermitian y).eigenvectorUnitary).2
  have hU2 : U * Uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem hmem
  set s : Fin n → Fin n → ℂ := fun i j => ((shc (pev y i - pev y j) : ℝ) : ℂ) with hs
  let H : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ := detPaHad s
  let T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    (detPaCj U Uᴴ).comp (H.comp (detPaCj Uᴴ U))
  have hT : ∀ W, T W = shcAd y W := by
    intro W
    simp only [T, H, LinearMap.comp_apply, detPaCj, LinearMap.coe_mk, AddHom.coe_mk, shcAd]
    congr 2
  have hC : shcAd y = ⇑(LinearMap.toContinuousLinearMap (T.restrictScalars ℝ)) := by
    funext W; exact (hT W).symm
  rw [hC, ContinuousLinearMap.fderiv, LinearMap.coe_toContinuousLinearMap, LinearMap.det_restrictScalars]
  have hAB : LinearMap.det (detPaCj U Uᴴ) * LinearMap.det (detPaCj Uᴴ U) = 1 := by
    rw [← LinearMap.det_comp]
    have : (detPaCj U Uᴴ).comp (detPaCj Uᴴ U) = LinearMap.id := by
      ext W : 1
      simp only [LinearMap.comp_apply, detPaCj, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_apply]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU2, Matrix.one_mul, Matrix.mul_assoc, hU2, Matrix.mul_one]
    rw [this, LinearMap.det_id]
  have hdet : LinearMap.det T = ∏ i, ∏ j, s i j := by
    simp only [T]
    rw [LinearMap.det_comp, LinearMap.det_comp]
    have hH : LinearMap.det H = ∏ i, ∏ j, s i j := detPaHad_det s
    rw [hH, mul_left_comm, hAB, mul_one]
  rw [hdet, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Algebra.norm_complex_apply, hs, Complex.normSq_ofReal, sq]

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def shcAdC {ε : Fin n → Bool} (y : PCoord ε → ℂ) (w : PCoord ε → ℂ) : PCoord ε → ℂ :=
  fun ab => shcAd y (pmat w) ab.1.1 ab.1.2

theorem detPb {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    LinearMap.det ((fderiv ℝ (shcAd y) 0 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) =
      (LinearMap.det ((fderiv ℝ (shcAdC y) 0 : (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) :
        (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ))) ^ 4 := by
  set U : Matrix (Fin n) (Fin n) ℂ := ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
    with hUdef
  have hU : Uᴴ * U = 1 := (pmat_isHermitian y).eigenvectorUnitary.2.1
  have hU' : U * Uᴴ = 1 := (pmat_isHermitian y).eigenvectorUnitary.2.2
  have hY : U * dpbD (pev y) * Uᴴ = pmat y := (pmat_isHermitian y).spectral_theorem.symm
  have e1 : shcAd y = LinearMap.toContinuousLinearMap (dpbL U (pev y) shc) := rfl
  have e2 : shcAdC y = LinearMap.toContinuousLinearMap (dpbP ε ∘ₗ dpbL U (pev y) shc ∘ₗ dpbE ε) := by
    funext w ab
    refine (dpbP_herm (W := dpbH U (pev y) shc (pmat w)) ?_ ab).symm
    rw [dpbH_conjTranspose U _ shc dpb_shc_neg, (pmat_isHermitian w).eq]
  rw [e1, e2, ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
  exact dpb_det hU hU' (by rw [hY]; exact dpb_JYJ y)

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem jac_le_exp {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    Jac z ≤ Real.exp (((n : ℝ) - 1) * Real.sqrt (2 * (q0 ε : ℝ)) * Real.sqrt (hs (pmat z))) := by
  have hpos : 0 < Jac z := lt_of_lt_of_le one_pos (jac_ge_one z)
  have h := log_jac_le_rho z
  rw [rhoP, ← mul_assoc] at h
  calc Jac z = Real.exp (Real.log (Jac z)) := (Real.exp_log hpos).symm
    _ ≤ _ := Real.exp_le_exp.mpr h

end ReciprocityTheory.ChartRestriction.DS
end
end
