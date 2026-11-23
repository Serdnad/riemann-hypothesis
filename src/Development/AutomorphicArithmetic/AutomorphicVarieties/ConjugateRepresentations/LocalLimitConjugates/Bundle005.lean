module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1398
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle424
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFiniteVectorsDense
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle323
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.GrpEqMemArchCompact
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.InfEmbGrpEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle001
public import GroundTheory.AutomorphicForms.AdelicDixmierMalliavinProduct
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl

@[expose] public section

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.clFacts :
    UpperTheory.V.Cj.H.ClFacts := by
  intro E _ _ _ a μ _ _
  refine ⟨fun φ ψ s t hφ hψ => ?_, fun φ hl hφ h0 => ?_, fun φ g hφ => ?_, fun ψ φ F hψ e => ?_⟩
  · have hm : InL μ (s • φ + t • ψ) := by
      refine ⟨fun γ hγ g => ?_, ?_⟩
      · change s • φ.1 (γ * g) + t • ψ.1 (γ * g) = s • φ.1 g + t • ψ.1 g
        rw [hφ.1 γ hγ g, hψ.1 γ hγ g]
      · exact (hφ.2.const_smul s).add (hψ.2.const_smul t)
    refine ⟨hm, ?_⟩
    rw [cl_eq hm, cl_eq hφ, cl_eq hψ]
    exact (MemLp.toLp_add (hφ.2.const_smul s) (hψ.2.const_smul t)).trans
      (congrArg₂ (· + ·) (MemLp.toLp_const_smul s hφ.2) (MemLp.toLp_const_smul t hψ.2))
  · by_contra hne
    rw [cl_eq hφ] at h0
    exact GlobalTheory.CuspRep.CuspidalL2GL.toL2_ne_zero hφ (ContAut.continuous_of_isOpen_stab E a φ hl)
      (fun h => hne (Subtype.ext h)) h0
  · have hm : InL μ (rt E a g φ) := hφ.mul_right g
    rw [cl_eq hm, cl_eq hφ]
    exact (GlobalTheory.AutomorphicL2Unitary.right_translate_toL2 hφ g).symm
  · obtain ⟨h, hh⟩ := UpperTheory.V.Cj.H.convolution_L2_class (GA E a) (latticeGL E a) μ ψ.1
      (ContAut.continuous_of_isOpen_stab E a ψ hψ.2) hψ.1 F
    have hm : InL μ φ := by
      unfold InL
      rw [e]
      exact h
    rw [cl_eq hm, ← hh]
    congr 1
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private def Bp (W S : Set (GA E a)) : Prop :=
  ∃ f : GA E a → ℝ, (fun g => (f g : ℂ)) ∈ Sm E a ∧ (∀ᶠ k in 𝓝 1, ∀ g, f (g * finGL E a k) = f g) ∧
    (∀ g, 0 ≤ f g) ∧ (∀ g ∈ S, 0 < f g) ∧ ∀ g ∉ W, f g = 0

private theorem tens_mem (β : Lie E a → ℂ) (hβ : ContDiff ℝ (⊤ : ℕ∞) β) (c : GL (Fin a) (Af E) → ℂ) (g₀ : GA E a) :
    (fun g => β (toL (GeneralLinearGroup.map (pInf E) (g₀ * g)).val) *
      c (GeneralLinearGroup.map (pFin E) (g₀ * g))) ∈ Sm E a := by
  intro g
  let L : Lie E a →L[ℝ] Lie E a := LinearMap.toContinuousLinearMap
    (LinearMap.mulLeft ℝ (GeneralLinearGroup.map (pInf E) (g₀ * g)).val :
      Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] Matrix (Fin a) (Fin a) (Cinf E))
  have h : ContDiff ℝ (⊤ : ℕ∞) fun x => β (L x) * c (GeneralLinearGroup.map (pFin E) (g₀ * g)) :=
    (hβ.comp L.contDiff).mul contDiff_const
  refine h.contDiffOn.congr fun x hx => ?_
  obtain ⟨u, hu⟩ := hx
  obtain rfl : x = toL u.val := hu.symm
  rw [chart_val, ← mul_assoc, map_mul, map_mul _ (g₀ * g), pInf_infGL, pFin_infGL, mul_one]
  rfl

private theorem bp_pt {W : Set (GA E a)} {g₀ : GA E a} (hW : W ∈ 𝓝 g₀) : ∃ S ∈ 𝓝 g₀, Bp W S := by
  set_option synthInstance.maxHeartbeats 200000 in
    classical
    obtain ⟨c1, c2, c3, c4⟩ := GlobalTheory.GLProj.continuous_proj_incl E a
    have hc : Continuous fun p : GL (Fin a) (Cinf E) × GL (Fin a) (Af E) => g₀ * (infGL E a p.1 * finGL E a p.2) :=
      continuous_const.mul ((c3.comp continuous_fst).mul (c4.comp continuous_snd))
    have hn := hc.continuousAt (x := (1, 1)).preimage_mem_nhds (t := W) (by simpa using hW)
    obtain ⟨N, hN, V, hV, hNV⟩ := mem_nhds_prod_iff.1 hn
    obtain ⟨U, hU, hUV⟩ := GlobalTheory.CompanionTheory.DenseKFin.exists_openSubgroup_GLAf hV
    obtain ⟨β, b0, b1, b2, -, b3⟩ := GlobalTheory.CompanionTheory.SmoothRep.exists_bump_conjInv E a N hN
    have bs : ContDiff ℝ (⊤ : ℕ∞) fun x => (β x : ℂ) := b2.1
    have bc : Continuous β := Complex.continuous_re.comp bs.continuous
    have d1 : Continuous fun g : GA E a => β (toL (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val) :=
      bc.comp ((Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))).comp
        (c1.comp (continuous_const.mul continuous_id)))
    have d2 : Continuous fun g : GA E a => GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g) :=
      c2.comp (continuous_const.mul continuous_id)
    refine ⟨{g | 0 < β (toL (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val)} ∩
      {g | GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g) ∈ U}, ?_,
      fun g => β (toL (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val) *
        if GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g) ∈ U then 1 else 0, ?_, ?_, ?_, ?_, ?_⟩
    · refine ((isOpen_lt continuous_const d1).inter (hU.preimage d2)).mem_nhds ⟨?_, ?_⟩
      · simp only [Set.mem_setOf_eq, inv_mul_cancel, map_one]
        exact b1
      · simp only [Set.mem_preimage, inv_mul_cancel, map_one]
        exact U.one_mem
    · have h := tens_mem _ bs (fun k => ((if k ∈ U then 1 else 0 : ℝ) : ℂ)) g₀⁻¹
      simpa only [Complex.ofReal_mul] using h
    · filter_upwards [hU.mem_nhds U.one_mem] with k hk g
      rw [← mul_assoc, map_mul, map_mul _ (g₀⁻¹ * g), pInf_finGL, pFin_finGL, mul_one]
      simp only [U.mul_mem_cancel_right hk]
    · intro g
      refine mul_nonneg (b0 _) ?_
      split_ifs <;> norm_num
    · rintro g ⟨h1, h2⟩
      exact mul_pos h1 ((if_pos h2).symm ▸ one_pos)
    · intro g hg
      by_contra h
      obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
      have h3 : GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g) ∈ U := by
        by_contra h3
        exact h2 (if_neg h3)
      obtain ⟨y, hy, e⟩ := b3 _ h1
      obtain rfl : y = GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) := Units.ext e
      have h4 := hNV (Set.mk_mem_prod hy (hUV h3))
      simp only [Set.mem_preimage, infGL_mul_finGL, mul_inv_cancel_left] at h4
      exact hg h4

private theorem bp_cpt {W C : Set (GA E a)} (hC : IsCompact C) (hW : IsOpen W) (h : C ⊆ W) : Bp W C := by
  set_option synthInstance.maxHeartbeats 200000 in
    refine hC.induction_on (p := Bp W) ?_ ?_ ?_ ?_
    · exact ⟨0, (Sm E a).zero_mem, by simp, by simp, by simp, by simp⟩
    · rintro s t hst ⟨f, h1, h2, h3, h4, h5⟩
      exact ⟨f, h1, h2, h3, fun g hg => h4 g (hst hg), h5⟩
    · rintro s t ⟨f, h1, h2, h3, h4, h5⟩ ⟨f', k1, k2, k3, k4, k5⟩
      refine ⟨fun g => f g + f' g, ?_, ?_, fun g => add_nonneg (h3 g) (k3 g), ?_,
        fun g hg => by simp only [h5 g hg, k5 g hg, add_zero]⟩
      · simp only [Complex.ofReal_add]
        exact (Sm E a).add_mem h1 k1
      · filter_upwards [h2, k2] with k e1 e2 g
        rw [e1, e2]
      · rintro g (hg | hg)
        · exact add_pos_of_pos_of_nonneg (h4 g hg) (k3 g)
        · exact add_pos_of_nonneg_of_pos (h3 g) (k4 g hg)
    · intro x hx
      obtain ⟨S, hS, hb⟩ := bp_pt (hW.mem_nhds (h hx))
      exact ⟨S, mem_nhdsWithin_of_mem_nhds hS, hb⟩

private theorem lev_of (φ : Sm E a) (h : ∀ᶠ k in 𝓝 1, ∀ g, φ.1 (g * finGL E a k) = φ.1 g) : HasLev φ := by
  refine isOpen_iff_mem_nhds.2 fun k₀ h₀ => ?_
  have e : ∀ g, φ.1 (g * finGL E a k₀) = φ.1 g := fun g => congrFun (congrArg Subtype.val h₀) g
  have ht : Tendsto (fun k => k₀⁻¹ * k) (𝓝 k₀) (𝓝 1) :=
    (continuous_const.mul continuous_id).tendsto' _ _ (inv_mul_cancel _)
  filter_upwards [ht.eventually h] with k hk
  refine Subtype.ext (funext fun g => ?_)
  change φ.1 (g * finGL E a k) = φ.1 g
  rw [← e g, ← hk (g * finGL E a k₀), mul_assoc, ← map_mul, mul_inv_cancel_left]

end

theorem UpperTheory.V.Cj.H.testBump :
    UpperTheory.V.Cj.H.TestBump := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro E _ _ _ a C W hC hW h
    obtain ⟨K, hK, hCK⟩ := exists_compact_superset hC
    obtain ⟨f, h1, h2, h3, h4, h5⟩ := bp_cpt hC (hW.inter isOpen_interior) (Set.subset_inter h hCK)
    refine ⟨⟨_, h1⟩, ⟨HasCompactSupport.intro hK fun g hg => ?_, lev_of _ ?_⟩, fun g => ⟨f g, h3 g, rfl⟩,
      fun g hg => Complex.ofReal_ne_zero.2 (h4 g hg).ne', fun g hg => ?_⟩
    · exact Complex.ofReal_eq_zero.2 (h5 g fun k => hg (interior_subset k.2))
    · filter_upwards [h2] with k hk g
      exact congrArg _ (hk g)
    · exact Complex.ofReal_eq_zero.2 (h5 g fun k => hg k.1)
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem norm_tsum_le_of_encard {I : Type} (u : I → ℂ) (S : Set I) (N : ℕ) (hS : S.encard ≤ N) (M : ℝ)
    (hM : ∀ i, ‖u i‖ ≤ M) (hM0 : 0 ≤ M) (h0 : ∀ i ∉ S, u i = 0) : ‖∑' i, u i‖ ≤ N * M := by
  have hfin : S.Finite := Set.finite_of_encard_le_coe hS
  rw [tsum_eq_sum (s := hfin.toFinset) fun i hi => h0 i (by simpa using hi)]
  have hcard : hfin.toFinset.card ≤ N := by
    rw [hfin.encard_eq_coe_toFinset_card] at hS
    exact_mod_cast hS
  refine (norm_sum_le_of_le _ fun i _ => hM i).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hM0

open scoped Pointwise in
theorem UpperTheory.V.Cj.H.orbConv :
    UpperTheory.V.Cj.H.OrbConv := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ f f' hf hc hf' hc'
  have hi : Integrable f μ := hf.integrable_of_hasCompactSupport hc
  have hq := GlobalTheory.AutomorphicL2KernelIntegral.integrable_descend_orbitSum (Γ := Γ) hi
  obtain ⟨N, hN⟩ := (locInt G Γ μ).2 (tsupport f) hc
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
  have hb : ∀ g, ‖GlobalTheory.AutomorphicL2Unitary.orbitSum Γ f g‖ ≤ N * M := fun g =>
    norm_tsum_le_of_encard _ _ N (hN g) M (fun _ => hM _) hM0 fun γ h => image_eq_zero_of_notMem_tsupport h
  have h : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient Γ μ (GlobalTheory.AutomorphicL2Unitary.orbitSum Γ f) := by
    refine ⟨GlobalTheory.AutomorphicL2Unitary.leftInv_orbitSum f, (memLp_two_iff_integrable_sq_norm hq.1).2 ?_⟩
    refine (hq.norm.const_mul (N * M)).mono' (hq.1.norm.pow 2) (Eventually.of_forall fun q => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), sq]
    exact mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _)
  refine ⟨h, funext fun x => ?_⟩
  have hae : ∀ᵐ g ∂μ, GlobalTheory.AutomorphicL2Unitary.lift Γ h.toL2 g = GlobalTheory.AutomorphicL2Unitary.orbitSum Γ f g := by
    filter_upwards [GlobalTheory.AutomorphicL2Unitary.ae_quotMeasure_iff.1 h.coeFn_toL2] with g hg
    exact hg.trans (h.1.descend_mk g)
  have hk : Continuous fun y : G => f' (y⁻¹ * x) := by fun_prop
  have hkc : HasCompactSupport fun y : G => f' (y⁻¹ * x) :=
    hc'.comp_homeomorph ((Homeomorph.inv G).trans (Homeomorph.mulRight x))
  have hint : ∀ γ : Γ, Integrable (fun y => f (γ * y) * f' (y⁻¹ * x)) μ := fun γ =>
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hkc.mul_left
  have hfin : {γ : Γ | (γ : G) ∈ tsupport f * (tsupport fun y : G => f' (y⁻¹ * x))⁻¹}.Finite :=
    GlobalTheory.AutomorphicL2Unitary.finite_mem_compact (IsCompact.mul hc (IsCompact.inv hkc))
  have hsum : Summable fun γ : Γ => ∫ y, ‖f (γ * y) * f' (y⁻¹ * x)‖ ∂μ := by
    refine summable_of_hasFiniteSupport (hfin.subset fun γ hγ => ?_)
    by_contra hn
    refine hγ ?_
    have : ∀ y, f (γ * y) * f' (y⁻¹ * x) = 0 := fun y => by
      by_contra hy
      exact hn ⟨_, subset_tsupport f (left_ne_zero_of_mul hy), y⁻¹,
        Set.inv_mem_inv.2 (subset_tsupport _ (right_ne_zero_of_mul hy)), by simp⟩
    simp [this]
  have e1 : ∀ γ : Γ, GlobalTheory.AutomorphicL2Unitary.conv μ f f' (γ * x) = ∫ y, f (γ * y) * f' (y⁻¹ * x) ∂μ := fun γ => by
    unfold GlobalTheory.AutomorphicL2Unitary.conv
    rw [← integral_mul_left_eq_self _ (γ : G)]
    simp [mul_assoc]
  unfold cv
  rw [GlobalTheory.AutomorphicL2Unitary.orbitSum, tsum_congr e1, integral_tsum_of_summable_integral_norm hint hsum]
  refine integral_congr_ae ?_
  filter_upwards [hae] with y hy
  rw [hy, tsum_mul_right, GlobalTheory.AutomorphicL2Unitary.orbitSum]
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

variable (E a) in
private noncomputable def spl : GA E a ≃ₜ* archGroup E a × GL (Fin a) (Af E) where
  toMulEquiv := (AdelicGLn.prodEquiv E a).toMulEquiv.trans
    (MulEquiv.prodCongr (archEquiv E a).toMulEquiv (MulEquiv.refl _))
  continuous_toFun := ((archEquiv E a).continuous.prodMap continuous_id).comp (AdelicGLn.prodEquiv E a).continuous
  continuous_invFun := (AdelicGLn.prodEquiv E a).symm.continuous.comp
    ((archEquiv E a).symm.continuous.prodMap continuous_id)

private theorem spl_symm (x : archGroup E a) (b : GL (Fin a) (Af E)) :
    (spl E a).symm (x, b) = finEmb E a b * infEmb E a x := by
  refine (AdelicGLn.prodEquiv E a).injective ?_
  rw [map_mul, prodEquiv_infEmb, prodEquiv_finEmb, Prod.mk_mul_mk, one_mul, mul_one]
  exact (AdelicGLn.prodEquiv E a).apply_symm_apply _

private theorem spl_fin (b : GL (Fin a) (Af E)) : (spl E a).symm (1, b) = finGL E a b := by
  rw [spl_symm, map_one, mul_one, UpperTheory.V.Fb.finEmb_eq]

private theorem arch_iff (φ : GA E a → ℂ) :
    IsArchSmooth φ ↔ ∀ b, (isExpLieAlgebra E a).IsSmoothFun fun x => φ ((spl E a).symm (x, b)) := by
  simp only [spl_symm]
  refine ⟨fun h b => h (finEmb E a b), fun h g => ?_⟩
  rw [← infEmb_mul_finEmb g, infEmb_mul_finEmb_comm, archSlice_mul]
  exact ((isExpLieAlgebra E a).leftTranslateEnd _ ⟨_, h _⟩).2

variable [_root_.NumberField.IsTotallyComplex E]

private def stab (φ : Sm E a) : Subgroup (GL (Fin a) (Af E)) where
  carrier := {k | ∀ g, φ.1 (g * finGL E a k) = φ.1 g}
  one_mem' := fun g => by rw [map_one, mul_one]
  mul_mem' := fun {k l} hk hl g => by rw [map_mul, ← mul_assoc, hl, hk]
  inv_mem' := fun {k} hk g => by
    rw [← hk (g * finGL E a k⁻¹), mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]

private theorem lev_iff (φ : Sm E a) : HasLev φ ↔ IsOpen (stab φ : Set (GL (Fin a) (Af E))) := by
  have : {k | act (.fin k) φ = φ} = (stab φ : Set (GL (Fin a) (Af E))) := by
    ext k
    exact ⟨fun h g => congrFun (congrArg Subtype.val h) g, fun h => Subtype.ext (funext h)⟩
  rw [HasLev, this]

private theorem smooth_of (φ : Sm E a) (h : HasLev φ) :
    ProdSmooth.IsSmooth (isExpLieAlgebra E a) (spl E a) φ.1 := by
  have ho : IsOpen ((stab φ ⊓ AdelicGLn.integralFiniteGL E a : Subgroup (GL (Fin a) (Af E))) :
      Set (GL (Fin a) (Af E))) := ((lev_iff φ).1 h).inter (AdelicGLn.isOpen_integralFiniteGL E a)
  refine ⟨(arch_iff φ.1).1 (UpperTheory.V.Cm.isArchSmooth_of_mem φ.2), _, ho,
    (AdelicGLn.isCompact_integralFiniteGL E a).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) fun _ h => h.2,
    fun x v hv => ?_⟩
  rw [spl_fin]
  exact hv.1 x

private theorem test_of (φ : CompactlySupportedContinuousMap (GA E a) ℂ)
    (h : ProdSmooth.IsSmooth (isExpLieAlgebra E a) (spl E a) φ) : ∃ u : Sm E a, IsTest u ∧ u.1 = φ := by
  obtain ⟨h1, V, hV, -, h2⟩ := h
  refine ⟨⟨φ, UpperTheory.V.Cm.mem_Sm_of ((arch_iff _).2 h1)⟩, ⟨φ.hasCompactSupport, ?_⟩, rfl⟩
  rw [lev_iff]
  refine Subgroup.isOpen_mono (H₁ := V) (fun v hv g => ?_) hV
  rw [← spl_fin]
  exact h2 g v hv

end

theorem UpperTheory.V.Cj.H.dmTest :
    UpperTheory.V.Cj.H.DmTest := by
  intro E _ _ _ a μ _ f hf
  let F : CompactlySupportedContinuousMap (GA E a) ℂ := ⟨⟨f.1, ((testOps E a f).1 hf.2).1⟩, hf.1⟩
  obtain ⟨n, φ, ψ, h, e⟩ := GroundTheory.Automorphic.ProdSmooth.exists_sum_conv _ (spl E a) μ F (smooth_of f hf.2)
  choose u hu eu using fun i => test_of (φ i) (h i).1
  choose v hv ev using fun i => test_of (ψ i) (h i).2
  refine ⟨n, u, v, fun i => ⟨hu i, hv i⟩, funext fun x => ?_⟩
  have := congrArg (fun G : CompactlySupportedContinuousMap (GA E a) ℂ => G x) e
  simp only [CompactlySupportedContinuousMap.sum_apply, GroundTheory.Automorphic.conv_apply] at this
  rw [Finset.sum_apply]
  simp only [eu, ev]
  exact this
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem rT_map_on {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (N : Submodule ℂ W) (T A : Module.End ℂ W)
    (B : Module.End ℂ (Fin d → ℂ)) (h : ∀ φ ∈ N, A (T φ) = T (A φ)) (m : W ⊗[ℂ] (Fin d → ℂ)) (hm : ∀ i, cmp i m ∈ N) :
    T.rTensor _ (TensorProduct.map A B m) = TensorProduct.map A B (T.rTensor _ m) := by
  rw [← sum_cmp m]

  simp only [map_sum, LinearMap.rTensor_tmul, TensorProduct.map_tmul]
  exact Finset.sum_congr rfl fun i _ => by rw [h _ (hm i)]

private theorem rT_smLie {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (Ξ : AlgRep E a)
    (N : Submodule ℂ (Sm E a)) (T : Module.End ℂ (Sm E a)) (hT : IsOp N T) (X : Lie E a)
    (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) (hm : ∀ i, cmp i m ∈ N) :
    smLie Ξ X (T.rTensor _ m) = T.rTensor _ (smLie Ξ X m) := by
  have h1 := rT_map_on N T (lie E a X) LinearMap.id (hT.lie X) m hm
  have h2 := rT_map_on N T LinearMap.id (Matrix.toLin' (Ξ.dmat X)) (fun _ _ => rfl) m hm
  change TensorProduct.map (lie E a X) LinearMap.id (T.rTensor _ m) +
      TensorProduct.map LinearMap.id (Matrix.toLin' (Ξ.dmat X)) (T.rTensor _ m) =
    T.rTensor _ (TensorProduct.map (lie E a X) LinearMap.id m + TensorProduct.map LinearMap.id (Matrix.toLin' (Ξ.dmat X)) m)
  rw [map_add (f := _), h1, h2]

theorem UpperTheory.V.Cj.H.appFacts :
    UpperTheory.V.Cj.H.AppFacts := by
  intro E _ _ _ a U Ξ r hr N hN T hT q ω hω hv
  obtain ⟨-, -, hl, hc⟩ := levLin E a U Ξ q
  have hone : ∀ X i, ∀ m : ℂ, Ξ.dmat (oneL E a) = m • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) →
      lie E a (oneL E a) (T (cmp i (ω X))) = -m • T (cmp i (ω X)) := fun X i m hm => by
    rw [hT.lie _ _ (hv X i), (hl ω hω X i).2.2 m hm, map_smul]
  have hsq : ∀ X i, IsSq r (T (cmp i (ω X))) := fun X i => hN.sq _ (hT.maps _ (hv X i)) (hone X i _ hr)
  refine ⟨⟨?_, fun X i h => ?_, fun X => mem_span_of_cmp fun i => ?_⟩, fun X i => ?_, fun X i => ?_, ?_⟩
  · intro k X
    rw [app_apply, app_apply, hω.equiv k X]
    exact rT_map_on N T _ _ (hT.rt _) _ (hv X)
  · rw [app_apply, hω.basic X i h, map_zero]
  · rw [hc]
    refine ⟨(hsq X i).left, fun u hu => ?_, hone X i⟩
    exact (hT.rt _ _ (hv X i)).trans (congrArg T ((hl ω hω X i).2.1 u hu))
  · rw [hc]
    exact hT.maps _ (hv X i)
  · rw [hc]
    exact Submodule.subset_span (hsq X i)
  · refine AlternatingMap.ext fun X => ?_
    rw [app_apply]

    simp only [dCo, AlternatingMap.alternatizeUncurryFin_apply, map_sum, map_zsmul]
    refine Finset.sum_congr rfl fun i _ => congrArg _ ?_
    exact rT_smLie Ξ N T hT _ _ (hv _)
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.autOf :
    UpperTheory.V.Cj.H.AutOf := by
  intro E _ _ _ a U hU Ξ m q ω hω X i hc hg
  have hl := (UpperTheory.V.Cj.H.levLin E a U Ξ q).2.2.1 ω hω X i
  obtain ⟨W, _, _, _, ρ, -, hρ⟩ := UpperTheory.V.Cj.H.kType E a Ξ q
  obtain ⟨T, w, hT, hw⟩ := hρ ω hω.equiv X i
  generalize cmp i (ω X) = φ at hc hg hl hw ⊢
  refine ⟨hl.1, ?_, ?_, ?_, hg⟩
  · exact Subgroup.isOpen_mono (H₁ := U)
      (H₂ := { carrier := {k | finRep E a k φ = φ}
               one_mem' := by simp
               mul_mem' := fun {x y} hx hy => by
                 rw [Set.mem_setOf_eq] at hx hy ⊢
                 rw [map_mul, Module.End.mul_apply, hy, hx]
               inv_mem' := fun {x} hx => by
                 rw [Set.mem_setOf_eq] at hx ⊢
                 conv_lhs => rw [← hx]
                 rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] })
      (fun u hu => hl.2.1 u hu) hU
  · refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range T) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨ρ k w, by rw [hT, hw]⟩
  · refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {φ}) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    have key : ∃ c : ℂ, z φ = c • φ := by
      induction hz using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨t, u, rfl⟩ := hx
        exact ⟨_, hc t u⟩
      | algebraMap c => exact ⟨c, rfl⟩
      | add x y _ _ hx hy =>
        obtain ⟨c, hx⟩ := hx
        obtain ⟨d, hy⟩ := hy
        exact ⟨c + d, by rw [LinearMap.add_apply, hx, hy, add_smul]⟩
      | mul x y _ _ hx hy =>
        obtain ⟨c, hx⟩ := hx
        obtain ⟨d, hy⟩ := hy
        exact ⟨d * c, by rw [Module.End.mul_apply, hy, map_smul, hx, mul_smul]⟩
    obtain ⟨c, h⟩ := key
    exact Submodule.mem_span_singleton.2 ⟨c, h.symm⟩
end
