module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle001
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle204
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemisimpleTraceForm.Bundle002
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.Padics.ValuativeRel
import GroundTheory.LocalFields.Bundle002
public import GroundTheory.LocalFields.Bundle001
public import Mathlib.GroupTheory.Nilpotent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle205
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlSpanImageContinuousRepFinite
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
import GroundTheory.LocalFields.Interface
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle192

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

namespace GlobalTheory.Per

theorem kerQ_eq_map_ker_theta (l : ℕ) [Fact l.Prime] :
    Formalism.Per.kerP l = (RingHom.ker (Formalism.Per.θ l)).map
      (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l)) := by
  refine le_antisymm (fun s hs => ?_)
    (Ideal.map_le_iff_le_comap.2 fun a ha => GlobalTheory.RingIface.alg_mem_kerP l ha)
  obtain ⟨k, a, h⟩ := IsLocalization.Away.surj ((l : ℕ) : Formalism.Per.Ainf l) s
  have hu := (IsLocalization.Away.algebraMap_isUnit (S := Formalism.Per.AinfP l)
    ((l : ℕ) : Formalism.Per.Ainf l)).pow k
  have h0 : Formalism.Per.θP l s = 0 := GlobalTheory.RingBasics.fontaineTheta_eq_zero_of_mem_ker l s (by rwa [pow_one])
  have h1 : Formalism.Per.θP l (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) a) = 0 := by
    rw [← h, map_mul, h0, zero_mul]
  rw [GlobalTheory.RingIface.fontaineTheta_algebraMap] at h1
  have h2 : Formalism.Per.θ l a = 0 := Subtype.ext h1
  rw [← Ideal.mul_unit_mem_iff_mem _ hu, h]
  exact Ideal.mem_map_of_mem _ h2

end GlobalTheory.Per
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem approx_algebraic_integer : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (S : Set (GQ l)) (x : ℂ_[l]) (a : GQ l → ℤ_[l]), (∀ σ ∈ S, ‖Formalism.Per.σC σ x - x - algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l])‖ ≤ ((l : ℝ)⁻¹) ^ r) → ∃ (y : Om l) (b : GQ l → ℤ), (∀ σ ∈ S, ‖σ y - y - (b σ : Om l)‖ ≤ ((l : ℝ)⁻¹) ^ r) ∧ ∀ σ, (l : ℤ) ^ r ∣ b σ → (l : ℤ_[l]) ^ r ∣ a σ := by
  intro l _ r S x a h
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hδ : (0 : ℝ) < ((l : ℝ)⁻¹) ^ r := by positivity
  obtain ⟨y, hy⟩ := (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl l)).exists_dist_lt x hδ
  have hdiff : ∀ σ : GQ l, (l : ℤ_[l]) ^ r ∣ a σ - (((a σ).appr r : ℕ) : ℤ_[l]) := by
    intro σ
    exact Ideal.mem_span_singleton.1 (PadicInt.appr_spec r (a σ))
  refine ⟨y, fun σ => (((a σ).appr r : ℕ) : ℤ), ?_, ?_⟩
  · intro σ hσ
    have hY : ‖(y : ℂ_[l]) - x‖ ≤ ((l : ℝ)⁻¹) ^ r := by
      rw [← dist_eq_norm, dist_comm]; exact hy.le
    have hAB : ‖algebraMap ℚ_[l] ℂ_[l] ((a σ - (((a σ).appr r : ℕ) : ℤ_[l]) : ℤ_[l]) : ℚ_[l])‖ ≤ ((l : ℝ)⁻¹) ^ r := by
      rw [norm_algebraMap', PadicInt.padic_norm_e_of_padicInt]
      obtain ⟨c, hc⟩ := hdiff σ
      rw [hc, norm_mul, norm_pow, PadicInt.norm_p]
      have := PadicInt.norm_le_one c
      have h0 : (0:ℝ) ≤ ((l : ℝ)⁻¹) ^ r := hδ.le
      calc ((l : ℝ)⁻¹) ^ r * ‖c‖ ≤ ((l : ℝ)⁻¹) ^ r * 1 := mul_le_mul_of_nonneg_left this h0
        _ = _ := mul_one _
    have key : (((σ y - y - ((((((a σ).appr r : ℕ) : ℤ)) : Om l))) : PadicAlgCl l) : ℂ_[l]) =
        (Formalism.Per.σC σ x - x - algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l])) +
        (Formalism.Per.σC σ ((y : ℂ_[l]) - x) - ((y : ℂ_[l]) - x)) +
        (algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l]) - ((((a σ).appr r : ℕ)) : ℂ_[l])) := by
      have h1 : ((σ y : PadicAlgCl l) : ℂ_[l]) = Formalism.Per.σC σ (y : ℂ_[l]) := (GlobalTheory.RingBasics.σC_coe σ y).symm
      generalize algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l]) = A
      rw [map_sub]
      push_cast
      rw [h1]
      ring
    have hAB' : ‖algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l]) - ((((a σ).appr r : ℕ)) : ℂ_[l])‖ ≤ ((l : ℝ)⁻¹) ^ r := by
      simpa only [PadicInt.coe_sub, PadicInt.coe_natCast, map_sub, map_natCast] using hAB
    rw [← PadicComplex.norm_extends, key]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h σ hσ) ?_)) hAB')
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [GlobalTheory.RingBasics.norm_σC]; exact hY
    · rw [norm_neg]; exact hY
  · intro σ _
    have : (a σ) = (a σ - (((a σ).appr r : ℕ) : ℤ_[l])) + (((a σ).appr r : ℕ) : ℤ_[l]) := by ring
    rw [this]
    refine dvd_add (hdiff σ) ?_
    have := map_dvd (Int.castRingHom ℤ_[l]) (by assumption : (l : ℤ) ^ r ∣ (((a σ).appr r : ℕ) : ℤ))
    simpa using this

end GlobalTheory.PMon.Ram
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.CrisPerFix

variable {l : ℕ} [Fact l.Prime]

def maxUnramifiedFrobenius (P : LocPrime l) (K : FinExt l) : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥(K0 K) :=
  AlgEquiv.ofBijective (P.PD K).σ (P.PD K).σ_bij

theorem frobK0_apply (P : LocPrime l) (K : FinExt l) (x : ↥(K0 K)) :
    maxUnramifiedFrobenius P K x = (P.PD K).σ x := rfl

theorem nontrivial_B (P : LocPrime l) (K : FinExt l) : Nontrivial P.R.B := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact (P.PD K).not_mem_filtration_two (by rw [Subsingleton.elim ((P.PD K).t) 0, map_zero]; exact Submodule.zero_mem _)

theorem ιB_algebraMap (P : LocPrime l) (K : FinExt l) (a : ↥(K0 K)) :
    P.ιB (algebraMap ↥(K0 K) P.R.B a) = algebraMap ↥(K0 K) P.R.BdR a := by
  rw [← P.PD_ι K]
  exact (P.PD K).ι.commutes a

theorem orderOf_frobK0 (P : LocPrime l) (K : FinExt l) :
    orderOf (maxUnramifiedFrobenius P K) = finrank ℚ_[l] ↥(K0 K) := by
  haveI := (P.PD K).finK₀
  haveI := nontrivial_B P K
  have hfix : IntermediateField.fixedField (Subgroup.zpowers (maxUnramifiedFrobenius P K)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hσ : (P.PD K).σ x = x := hx _ (Subgroup.mem_zpowers _)
    obtain ⟨q, hq⟩ := (P.PD K).fund (algebraMap ↥(K0 K) P.R.B x)
      (by rw [(P.PD K).φ_K₀, hσ])
      (by
        rw [(P.PD K).ι.commutes, Algebra.algebraMap_eq_smul_one]
        exact Submodule.smul_of_tower_mem _ x (P.PD K).one_mem)
    rw [IntermediateField.mem_bot]
    refine ⟨q, (algebraMap ↥(K0 K) P.R.B).injective ?_⟩
    rw [← IsScalarTower.algebraMap_apply]
    exact hq
  have h := IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers (maxUnramifiedFrobenius P K))
  rw [hfix, IntermediateField.finrank_bot', Nat.card_zpowers] at h
  exact h.symm

theorem iterate_φB_mul (P : LocPrime l) (K : FinExt l) (j : ℕ) (b : ↥(K0 K)) (x : P.R.B) :
    (⇑P.φB)^[j] (algebraMap ↥(K0 K) P.R.B b * x) =
      algebraMap ↥(K0 K) P.R.B ((maxUnramifiedFrobenius P K ^ j) b) * (⇑P.φB)^[j] x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, map_mul, ← P.PD_φ K (algebraMap _ _ _), (P.PD K).φ_K₀,
      Function.iterate_succ_apply', pow_succ', AlgEquiv.mul_apply, frobK0_apply]

theorem det_ne_zero (P : LocPrime l) (K : FinExt l)
    (bas : Module.Basis (Fin (finrank ℚ_[l] ↥(K0 K))) ℚ_[l] ↥(K0 K)) :
    (Matrix.of fun i j : Fin (finrank ℚ_[l] ↥(K0 K)) => (maxUnramifiedFrobenius P K ^ (j : ℕ)) (bas i)).det ≠ 0 := by
  set τ := maxUnramifiedFrobenius P K
  intro h
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  let L : ↥(K0 K) →ₗ[ℚ_[l]] ↥(K0 K) :=
    { toFun := fun x => ∑ j : Fin (finrank ℚ_[l] ↥(K0 K)), u j * (τ ^ (j : ℕ)) x
      map_add' := by intro x y; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r x
        rw [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← mul_smul_comm]
        congr 1
        exact (τ ^ (j : ℕ)).toLinearEquiv.map_smul r x }
  have hL : L = 0 := by
    refine bas.ext fun i => ?_
    have := congrFun hu i
    simpa [L, Matrix.mulVec, dotProduct, mul_comm] using this
  let f : Fin (finrank ℚ_[l] ↥(K0 K)) → (↥(K0 K) →* ↥(K0 K)) := fun j => ((τ ^ (j : ℕ)).toRingEquiv : _ ≃+* _).toMonoidHom
  have hf : Function.Injective f := by
    intro i j hij
    have h1 : τ ^ (i : ℕ) = τ ^ (j : ℕ) := AlgEquiv.ext fun x => DFunLike.congr_fun hij x
    have hi : (i : ℕ) ∈ Set.Iio (orderOf τ) := by rw [orderOf_frobK0]; exact i.2
    have hj : (j : ℕ) ∈ Set.Iio (orderOf τ) := by rw [orderOf_frobK0]; exact j.2
    exact Fin.ext (pow_injOn_Iio_orderOf hi hj h1)
  have li := (linearIndependent_monoidHom ↥(K0 K) ↥(K0 K)).comp f hf
  rw [Fintype.linearIndependent_iff] at li
  apply hu0
  funext j
  refine li u ?_ j
  funext x
  have := LinearMap.congr_fun hL x
  simpa [L, f, Finset.sum_apply, smul_eq_mul] using this

theorem mem_unramified_of_frobenius_iterate_fixed_fil_alt :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K : FinExt l) (c : P.R.B), (⇑P.φB)^[finrank ℚ_[l] ↥(K0 K)] c = c →
    (∀ j : ℕ, P.ιB ((⇑P.φB)^[j] c) ∈ (P.PD K).Fil 0) →
    ∃ a : ↥(K0 K), c = algebraMap ↥(K0 K) P.R.B a := by
  intro l _ P _ _ K c hn hF
  set n := finrank ℚ_[l] ↥(K0 K) with hn_def
  haveI := (P.PD K).finK₀
  set τ := maxUnramifiedFrobenius P K
  have hord : orderOf τ = n := orderOf_frobK0 P K
  have hn0 : 0 < n := Module.finrank_pos
  let bas := Module.finBasisOfFinrankEq ℚ_[l] ↥(K0 K) hn_def.symm
  let A : Matrix (Fin n) (Fin n) ↥(K0 K) := Matrix.of fun i j => (τ ^ (j : ℕ)) (bas i)
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.2 (det_ne_zero P K bas)
  have hs : ∀ b : ↥(K0 K), ∃ q : ℚ_[l], algebraMap ℚ_[l] P.R.B q =
      ∑ j ∈ Finset.range n, (⇑P.φB)^[j] (algebraMap ↥(K0 K) P.R.B b * c) := by
    intro b
    apply (P.PD K).fund

    · rw [P.PD_φ, map_sum]
      have e1 : ∀ j, P.φB ((⇑P.φB)^[j] (algebraMap ↥(K0 K) P.R.B b * c)) =
          (⇑P.φB)^[j + 1] (algebraMap ↥(K0 K) P.R.B b * c) :=
        fun j => (Function.iterate_succ_apply' _ _ _).symm
      simp_rw [e1]
      have hfn : (⇑P.φB)^[n] (algebraMap ↥(K0 K) P.R.B b * c) =
          (⇑P.φB)^[0] (algebraMap ↥(K0 K) P.R.B b * c) := by
        rw [iterate_φB_mul, hn, ← hord, pow_orderOf_eq_one, AlgEquiv.one_apply, Function.iterate_zero, id]
      have h := Finset.sum_range_succ' (fun j => (⇑P.φB)^[j] (algebraMap ↥(K0 K) P.R.B b * c)) n
      rw [Finset.sum_range_succ, hfn] at h
      exact (add_right_cancel h).symm

    · rw [P.PD_ι, map_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [iterate_φB_mul, map_mul, ιB_algebraMap, ← Algebra.smul_def]
      exact Submodule.smul_of_tower_mem _ _ (hF j)
  choose q hq using fun i => hs (bas i)
  let v : Fin n → P.R.B := fun j => (⇑P.φB)^[(j : ℕ)] c
  have hAv : Matrix.mulVec (A.map (algebraMap ↥(K0 K) P.R.B)) v =
      fun i => algebraMap ↥(K0 K) P.R.B (algebraMap ℚ_[l] ↥(K0 K) (q i)) := by
    funext i
    rw [← IsScalarTower.algebraMap_apply, hq i, Finset.sum_range]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, A, v, Matrix.of_apply, iterate_φB_mul]
    rfl
  have hinv : (A⁻¹.map (algebraMap ↥(K0 K) P.R.B)) * (A.map (algebraMap ↥(K0 K) P.R.B)) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hv : v = Matrix.mulVec (A⁻¹.map (algebraMap ↥(K0 K) P.R.B))
      (fun i => algebraMap ↥(K0 K) P.R.B (algebraMap ℚ_[l] ↥(K0 K) (q i))) := by
    rw [← hAv, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  refine ⟨∑ i, A⁻¹ ⟨0, hn0⟩ i * algebraMap ℚ_[l] ↥(K0 K) (q i), ?_⟩
  have h0 := congrFun hv ⟨0, hn0⟩
  simp only [v, Function.iterate_zero, id] at h0
  rw [h0]

  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

end GlobalTheory.CrisPerFix
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.TiedMu

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem zeta_pow (AI : LocAinf l P) (k n : ℕ) : AI.ζ (n + k) ^ l ^ n = AI.ζ k := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, Nat.add_right_comm, AI.ζ_succ, ih]

theorem untilt_eps (AI : LocAinf l P) : AI.ε.untilt = 1 := by
  refine Perfection.teichmuller_spec (I := Ideal.span {(l : Per.OC l)}) fun n => ?_
  refine ⟨AI.ζ n, (AI.ε_coeff n).symm, ?_⟩
  have h := zeta_pow AI 0 n
  rw [add_zero, AI.ζ_zero] at h
  rw [h]

theorem locAinf_untilt_epsOne_eq_zeta (AI : LocAinf l P) : AI.ε1.untilt = AI.ζ 1 := by
  refine Perfection.teichmuller_spec (I := Ideal.span {(l : Per.OC l)}) fun n => ?_
  refine ⟨AI.ζ (n + 1), ?_, ?_⟩
  · refine (AI.ε_coeff (n + 1)).symm.trans ?_
    have h : AI.ε = AI.ε1 ^ l := by rw [LocAinf.ε1, frobeniusEquiv_symm_pow_p]
    rw [h]
    exact Perfection.coeff_pow_p _ _
  · rw [zeta_pow AI 1 n]

theorem eps_ne_one (AI : LocAinf l P) : AI.ε ≠ 1 := by
  intro h
  apply AI.ζ_one
  rw [← locAinf_untilt_epsOne_eq_zeta, LocAinf.ε1, h, map_one, map_one]

theorem eps_pow_ne_one (AI : LocAinf l P) (j : ℕ) : AI.ε ^ l ^ j ≠ 1 := by
  induction j with
  | zero => simpa using eps_ne_one AI
  | succ j ih =>
    intro h
    apply ih
    apply (frobeniusEquiv (OCb l) l).injective
    rw [frobeniusEquiv_apply, frobeniusEquiv_apply, frobenius_def, frobenius_def, ← pow_mul,
      ← pow_succ, h, one_pow]

theorem eps_root_pow (AI : LocAinf l P) (s : ℕ) : AI.εroot s ^ l ^ s = AI.ε := by
  induction s with
  | zero => simp [LocAinf.εroot]
  | succ s ih =>
    rw [LocAinf.εroot, Function.iterate_succ_apply', pow_succ', pow_mul, frobeniusEquiv_symm_pow_p]
    exact ih

theorem isUnit_aB (e : Per.Fl l) (he : e.untilt = 1) (hne : e ≠ 1) :
    IsUnit (Per.aB l (Per.tm e - 1)) :=
  GlobalTheory.CrisLoc.unit_of_root_aB l e he hne

theorem isUnit_of_aB {AI : LocAinf l P} (T : LocTied l P AI) (a : Ainf l) (h : IsUnit (Per.aB l a)) :
    IsUnit (AI.ιA a) := by
  rw [← T.ιA] at h
  have h' := h.map T.eB.symm
  rwa [RingEquiv.symm_apply_apply] at h'

theorem tied_mu_units : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → (∀ s : ℕ, IsUnit (AI.ιA (WittVector.teichmuller l (AI.εroot s) - 1))) ∧ (∀ j : ℕ, IsUnit (AI.ιA (WittVector.teichmuller l (AI.ε ^ l ^ j) - 1))) ∧ IsUnit (AI.ιA AI.ξ) ∧ ∀ z : ℤ_[l], AI.ιA (algebraMap ℤ_[l] (Ainf l) z) = algebraMap ℚ_[l] P.R.B (z : ℚ_[l]) := by
  intro l _ P AI T
  have hj : ∀ j : ℕ, IsUnit (AI.ιA (WittVector.teichmuller l (AI.ε ^ l ^ j) - 1)) := fun j =>
    isUnit_of_aB T _ (isUnit_aB (AI.ε ^ l ^ j)
      (by rw [map_pow, untilt_eps, one_pow]) (eps_pow_ne_one AI j))
  have hμ : IsUnit (AI.ιA AI.μ) := by simpa [LocAinf.μ] using hj 0
  refine ⟨fun s => ?_, hj, ?_, fun z => ?_⟩
  · have h := geom_sum_mul (WittVector.teichmuller l (AI.εroot s)) (l ^ s)
    rw [← map_pow, eps_root_pow] at h
    rw [LocAinf.μ, ← h, map_mul] at hμ
    exact isUnit_of_mul_isUnit_right hμ
  · rw [AI.μ_eq, map_mul] at hμ
    exact isUnit_of_mul_isUnit_right hμ
  · apply T.eB.injective
    rw [T.ιA, T.zB]
    exact GlobalTheory.RingIface.aB_algebraMap_padicInt l z

end GlobalTheory.TiedMu
end

section

open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.TrFormNd

theorem eq_zero_of_trace_mul_eq_zero : ∀ (k Γ : Type) [Field k] [CharZero k] [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) k), IsSSRep r → ∀ M ∈ Submodule.span k (Set.range fun g => ((r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)), (∀ g, (M * ((r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)).trace = 0) → M = 0 := by
  intro k Γ _ _ _ a r hr M hM hg
  have hnd : PI.SSAscent.UnitaryGroupMassFormula.TrNondeg (PI.SSAscent.UnitaryGroupMassFormula.imAlg r) :=
    PI.SSAscent.UnitaryGroupMassFormula.downStep_of PI.SSAscent.UnitaryGroupMassFormula.trace_nilpotent_ascent k Γ a r hr
  refine hnd M ((GlobalTheory.SSCont.mem_imAlg_iff r M).2 hM) fun y hy => ?_
  have hy' := (GlobalTheory.SSCont.mem_imAlg_iff r y).1 hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, rfl⟩ := hy
    exact hg g
  | zero => simp
  | add y z _ _ hy hz => rw [mul_add, Matrix.trace_add, hy, hz, add_zero]
  | smul c y _ hy => rw [Matrix.mul_smul, Matrix.trace_smul, hy, smul_zero]

end GlobalTheory.TrFormNd
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem exists_galois_ker_le_range (l : ℕ) [Fact l.Prime] (U : Subgroup (GQ l)) (S : Set (Om l))
    (hU : IsOpen (U : Set (GQ l))) (hS : S.Finite) :
    ∃ (L : Type) (_ : Field L) (_ : ValuativeRel L) (_ : TopologicalSpace L) (_ : IsNonarchimedeanLocalField L)
      (_ : Algebra ℚ_[l] L) (_ : ValuativeExtension ℚ_[l] L) (_ : FiniteDimensional ℚ_[l] L)
      (_ : IsGalois ℚ_[l] L) (_ : Algebra L (Om l)) (_ : IsScalarTower ℚ_[l] L (Om l)),
      (AlgEquiv.restrictNormalHom L : GQ l →* (L ≃ₐ[ℚ_[l]] L)).ker ≤ U ∧
        S ⊆ Set.range (algebraMap L (Om l)) := by
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff ℚ_[l] (Om l) (U : Set (GQ l))).mp
    (hU.mem_nhds U.one_mem)
  haveI := hS.to_subtype
  haveI : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] S) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let F : IntermediateField ℚ_[l] (Om l) := E ⊔ IntermediateField.adjoin ℚ_[l] S
  let M : IntermediateField ℚ_[l] (Om l) := IntermediateField.normalClosure ℚ_[l] F (Om l)
  haveI : FiniteDimensional ℚ_[l] M := inferInstance
  haveI : Normal ℚ_[l] M := inferInstance
  haveI : IsGalois ℚ_[l] M := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  have hFM : F ≤ M := IntermediateField.le_normalClosure F
  obtain ⟨vr, top, hloc, hext⟩ := exists_isNonarchimedeanLocalField_valuativeExtension ℚ_[l] M
  refine ⟨M, inferInstance, vr, top, hloc, inferInstance, hext, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_, ?_⟩
  · rw [IntermediateField.restrictNormalHom_ker]
    intro σ hσ
    apply hEU
    exact (IntermediateField.fixingSubgroup_le (le_trans le_sup_left hFM)) hσ
  · intro x hx
    have : x ∈ M := hFM (le_sup_right (a := E) (IntermediateField.subset_adjoin ℚ_[l] S hx))
    exact ⟨⟨x, this⟩, rfl⟩

end GlobalTheory.PMon.Ram
end

section

open GlobalTheory.BI GlobalTheory.BrauerZero

theorem _root_.GlobalTheory.T.exists_gt_commutator_mem_of_ne_whole : ∀ {G : Type} [Group G] [Finite G] [Group.IsNilpotent G] (K : Subgroup G), K ≠ ⊤ → ∃ A : Subgroup G, K < A ∧ ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ K := by
  first | exact @GlobalTheory.exists_lt_commutator_mem_of_ne_top | exact GlobalTheory.exists_lt_commutator_mem_of_ne_top | (intros; apply GlobalTheory.exists_lt_commutator_mem_of_ne_top <;> assumption)
end

section

open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

theorem _root_.GlobalTheory.T.zlSpan_image_continuous_rep_finite : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (r : Γ →* GL (Fin a) (PadicAlgCl l)), Continuous r → ∃ t : Finset Γ, ∀ f : Γ →₀ ℤ_[l], ∃ f' : Γ →₀ ℤ_[l], f'.support ⊆ t ∧ (f.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) • ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) = (f'.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) • ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) := by
  first | exact @GlobalTheory.zl_span_image_finite | exact GlobalTheory.zl_span_image_finite | (intros; apply GlobalTheory.zl_span_image_finite <;> assumption)
end
