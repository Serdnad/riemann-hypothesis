module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle004
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasValK
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.InnerCrossOpEigEqZero
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.KhwWeightEqOfIrr
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Bundle002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerWeight
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.NcVOneDecomp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Numerics
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle004
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle013
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Integr
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LholClmEventually
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle008
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.TopCap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfCharData
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFCore
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle007
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FormulaF
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsEquiv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle005
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.RigidUniversal
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.StdGapOfGapLap

@[expose] public section

section

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

theorem psiDatum_std {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ)
    (T : S7.KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hlam : S7.IsHCParam lam) (hgap : GapAtLeast ε lam h)
    (hstd : StdGap ε lam) (h8 : 8 * (n : ℝ) * S7.q0 ε < h) (hq : 1 ≤ S7.q0 ε) (hμ : S7.IsMu lam μ) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H)
      (E : Fin n → Fin n → Module.End ℂ D) (V : Submodule ℂ D) (ι : V ≃ₗ[ℂ] T.V),
      IsURepOn (UJset ε) σ ∧ IsDerivedOn ε σ D E ∧ IsKIrrHW ε E (lowK ε lam) V ∧
      (∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) ∧
      (∀ k' ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k' v) ∧
      ∀ g ∈ UJset ε, ∀ v v' : V,
        ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', S7.PsiM T μ g (ι v)⟫_ℂ := by
  let Ψ := S7.PsiM T μ
  have hP : IsPsiFor ε lam T Ψ := (S7.isPsiFor_psiM ε lam h T μ hlam hμ hgap hq h8).1
  have hv₀ : T.w ≠ 0 := fun h0 => by
    have h1 := T.w_norm
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hN0 : ‖uniformisationL2 ε Ψ T.w T.w‖ ≠ 0 := norm_ne_zero_iff.mpr (datumEmbedding_highest_ne_zero hstd hP hv₀)
  set c : ℂ := ((‖uniformisationL2 ε Ψ T.w T.w‖⁻¹ : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := by rw [hc]; exact_mod_cast inv_ne_zero hN0
  let j : T.V →ₗ[ℂ] datumV ε Ψ T.w :=
    { toFun := fun v => ⟨⟨uniformisationL2 ε Ψ T.w (c • v), datumEmbedding_mem_smooth hP T.w _⟩,
        (mem_datumV_iff hP T.w _).2 ⟨c • v, rfl⟩⟩
      map_add' := fun v v' => Subtype.ext (Subtype.ext (by
        show uniformisationL2 ε Ψ T.w (c • (v + v')) = uniformisationL2 ε Ψ T.w (c • v) + uniformisationL2 ε Ψ T.w (c • v')
        rw [smul_add, datumEmbedding_add hP]))
      map_smul' := fun a v => Subtype.ext (Subtype.ext (by
        show uniformisationL2 ε Ψ T.w (c • (a • v)) = a • uniformisationL2 ε Ψ T.w (c • v)
        rw [smul_comm, datumEmbedding_smul hP])) }
  have hj : Function.Bijective j := by
    refine ⟨fun v v' hv => ?_, fun x => ?_⟩
    · have : uniformisationL2 ε Ψ T.w (c • v) = uniformisationL2 ε Ψ T.w (c • v') :=
        congrArg (fun x : datumV ε Ψ T.w => ((x : smD ε (rreg ε)) : L2 ε)) hv
      exact smul_right_injective _ hc0 (uniformisationL2_injective hP hv₀ this)
    · obtain ⟨v, hv⟩ := (mem_datumV_iff hP T.w x).1 x.2
      refine ⟨c⁻¹ • v, Subtype.ext (Subtype.ext ?_)⟩
      show uniformisationL2 ε Ψ T.w (c • c⁻¹ • v) = _
      rw [smul_smul, mul_inv_cancel₀ hc0, one_smul, hv]
  let e := LinearEquiv.ofBijective j hj
  refine ⟨L2 ε, inferInstance, inferInstance, inferInstance, rreg ε, smD ε (rreg ε), smE ε (rreg ε),
    datumV ε Ψ T.w, e.symm, rreg_isURepOn ε, isDerivedOn_smE (rreg_isURepOn ε),
    datumV_isKIrrHW hP hv₀, datumV_casimir hP T.w, datumV_kStable hP T.w, fun g hgm v v' => ?_⟩
  obtain ⟨x, rfl⟩ := e.surjective v
  obtain ⟨x', rfl⟩ := e.surjective v'
  rw [e.symm_apply_apply, e.symm_apply_apply]
  show ⟪uniformisationL2 ε Ψ T.w (c • x'), rreg ε g (uniformisationL2 ε Ψ T.w (c • x))⟫_ℂ = _
  have key : ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ c * c) = 1 := by
    rw [hc, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
    congr 1
    rw [pow_two, mul_mul_mul_comm, mul_inv_cancel₀ hN0, one_mul]
  rw [formulaF hstd hP hv₀ hgm, map_smul, inner_smul_left, inner_smul_right]
  linear_combination ⟪x', Ψ g x⟫_ℂ * key

theorem datum_link_std {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hlam : S7.IsHCParam lam) (hgap : GapAtLeast ε lam h) (hstd : StdGap ε lam)
    (h8 : 8 * (n : ℝ) * S7.q0 ε < h) (hq : 1 ≤ S7.q0 ε)
    (T : S7.KType ε (lowK ε lam)) {μ : Fin n → ℤ} (hμ : S7.IsMu lam μ) :
    ∃ ι : V ≃ₗ[ℂ] T.V,
      (∀ g ∈ UJset ε, ∀ v v' : V,
        ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', S7.PsiM T μ g (ι v)⟫_ℂ) ∧
      (∀ v v' : V, ⟪ι v', ι v⟫_ℂ = ⟪((v' : D) : H), ((v : D) : H)⟫_ℂ) ∧
      ∀ (k : S7.KG ε) (v w : V), ((w : D) : H) = σ (S7.toMK k) ((v : D) : H) →
        ι w = T.op k (ι v) := by
  obtain ⟨H₂, _, _, _, σ₂, D₂, E₂, V₂, ι₂, hσ₂, hD₂, hV₂, hc₂, hVK₂, hco⟩ :=
    psiDatum_std ε lam h T μ hlam hgap hstd h8 hq hμ
  obtain ⟨φ, hφK, hφI⟩ := KTypeIsomorphism.exists_phi hσ hD hV hσ₂ hD₂ hV₂
  obtain ⟨ψ, -, hψI⟩ := KTypeIsomorphism.exists_phi hσ₂ hD₂ hV₂ hσ hD hV
  have := hV.1
  have := hV₂.1
  have hφi : Function.Injective φ := (injective_iff_map_eq_zero φ).mpr fun v hv => by
    have h1 := hφI v v
    rw [hv] at h1
    simpa using h1.symm
  have hψi : Function.Injective ψ := (injective_iff_map_eq_zero ψ).mpr fun v hv => by
    have h1 := hψI v v
    rw [hv] at h1
    simpa using h1.symm
  have hrk : Module.finrank ℂ V = Module.finrank ℂ V₂ :=
    le_antisymm (LinearMap.finrank_le_finrank_of_injective hφi)
      (LinearMap.finrank_le_finrank_of_injective hψi)
  let e : V ≃ₗ[ℂ] V₂ := φ.linearEquivOfInjective hφi hrk
  have hU := rigid_universal hσ hD hV hc hVK hσ₂ hD₂ hV₂ hc₂ hVK₂ hstd φ hφK hφI
  have h1J : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
    show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * 1 = Jm ε
    simp
  have hcoef : ∀ g ∈ UJset ε, ∀ v v' : V, ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ =
      ⟪(e.trans ι₂) v', S7.PsiM T μ g ((e.trans ι₂) v)⟫_ℂ := fun g hgm v v' =>
    (hU g hgm v v').symm.trans (hco g hgm (φ v) (φ v'))
  have hiso : ∀ v v' : V, ⟪(e.trans ι₂) v', (e.trans ι₂) v⟫_ℂ =
      ⟪((v' : D) : H), ((v : D) : H)⟫_ℂ := fun v v' => by
    have := hcoef 1 h1J v v'
    rw [hσ.1.1, S7.psiM_one] at this
    exact this.symm
  refine ⟨e.trans ι₂, hcoef, hiso, fun k v w hw => ?_⟩
  have hk : S7.PsiM T μ (S7.toMK k) = T.op k := by
    have := S7.psiM_equiv T μ k 1 (g := 1) h1J
    rwa [S7.toMK_one', Matrix.mul_one, Matrix.mul_one, S7.psiM_one, S7.op_one', mul_one, mul_one] at this
  refine ext_inner_left ℂ fun x => ?_
  obtain ⟨v', rfl⟩ := (e.trans ι₂).surjective x
  rw [hiso, hw, hcoef _ k.1.2, hk]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

theorem centralChar (n : ℕ) : CentralCharStatement n := by
  intro ε lam h H _ _ _ σ D E V hσ hD hV hcas hVK hint hanti hgap hp hq ω y hy
  obtain ⟨hg, hnpq, h8, -⟩ := gapCentral n ε lam h hgap
  have hlam : S7.IsHCParam lam := ⟨hanti, hint⟩
  obtain ⟨T⟩ := HW.kType_exists ε lam hlam
  obtain ⟨μ, hμ⟩ := S7.exists_mu hlam
  have hq0 : 1 ≤ S7.q0 ε := le_min hp hq
  have hP : IsPsiFor ε lam T (S7.PsiM T μ) := by
    refine ⟨fun k₁ k₂ g hg' => S7.psiM_equiv T μ k₁ k₂ hg', S7.psiM_one T μ,
      S7.psiM_smooth T μ hμ, fun g hg' => S7.psiM_casimir T μ hμ hg', ?_⟩
    intro ν hν
    exact (S7.psiM_integrable T μ hμ hlam hg hq0 ν).2.1
      (by unfold S7.q0; push_cast; exact h8)
  have hstd : StdGap ε lam := ⟨hanti, h, hg, hnpq⟩
  have hV0 : V ≠ ⊥ := by
    obtain ⟨w, hw, hw0, -⟩ := hV.2.2.2
    intro hb
    rw [hb] at hw
    exact hw0 ((Submodule.mem_bot ℂ).1 hw)
  have key := capelli_data hstd hσ hD hV hcas hVK hV0 hP
    (fun Y g hg' => S7.psiCapelli (n := n) ε lam T μ hμ Y g hg') (ω - ((n : ℂ) - 1) / 2) y hy
  rw [sub_add_cancel] at key
  rw [capelliQdet.1 (Module.End ℂ D) n E ω, key, capelliQdet.{0}.2]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section No

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem sc_no_of_schmid (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) (hn : (n : ℝ) < h)
    (hS : ∀ x ∈ Wm ε E V, phi E 1 x = 0) :
    ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ w ∈ layer ε E V 1,
      IsKHWVec ε E (lowK ε lam - root a b) w → w = 0 := by
  intro a b hab hε w hw hμ
  by_contra hw0
  have : FiniteDimensional ℂ V := hV.1
  have hKU : IsKUnitary ε E := isKUnitary_of_isInfUnitary hU
  have hP : V.starProjection w = 0 := by
    by_contra hne
    have hkhw := isKHWVec_starProjection hKU hV.2.1 hμ
    have heq := khw_weight_eq_of_irr hE hV (Submodule.starProjection_apply_mem V w) hne hkhw
    have h2 := congr_fun heq a
    simp only [Pi.sub_apply, root, Pi.single_eq_same, Pi.single_eq_of_ne hab.ne] at h2
    linarith
  have hperp : ∀ u ∈ layer ε E V 0, inner ℂ u w = 0 := by
    intro u hu
    have hwo : w ∈ Vᗮ := by
      have := Submodule.sub_starProjection_mem_orthogonal (K := V) w
      rwa [hP, sub_zero] at this
    exact (Submodule.mem_orthogonal V w).1 hwo u hu
  obtain ⟨P, hPnc, hP0, hPμ, hPperp⟩ := lift_layer hE hU hV.1 hV.2.1 (k := 0) hw hperp hμ hw0
  obtain ⟨xm, hxm, xp, hxp, hsum⟩ := ncV_one_decomp hE hU hV hmono hh hbig hPnc
  have hxm0 : inner ℂ xm P = 0 :=
    hPperp xm (Wm_le_ncV hxm) (by rw [hS xm hxm]; exact zero_mem _)
  have hmp : inner ℂ xm xp = 0 := Wm_perp_Wp hU hxm hxp
  have hxm_eq : xm = 0 := by
    have h3 : inner ℂ xm xm = 0 := by
      rw [hsum, inner_add_right, hmp, add_zero] at hxm0
      exact hxm0
    exact inner_self_eq_zero.1 h3
  rw [hxm_eq, zero_add] at hsum
  have hPWp : P ∈ Wp ε E V := hsum ▸ hxp
  obtain ⟨r, s, -, -, hC⟩ := crossOp_khw hE hU hV hPnc hP0 hPμ
  have hroot : lowK ε lam - root a b = lowK ε lam + root b a := by
    ext x; simp only [Pi.sub_apply, Pi.add_apply, root]; ring
  have hneg := crossVal_neg hmono hh hab hε
  rw [← hroot] at hneg
  have hWp := Wp_bound hE hU hV hmono hh hbig hPWp
  set val : ℝ := casValK ε (lowK ε lam - root a b) - n - casValK ε (lowK ε lam) with hval
  have key : 2 * RCLike.re (inner ℂ (crossOp ε E 1 0 P) P) = val * ‖P‖ ^ 2 := by
    have e := congrArg (fun x => RCLike.re (inner ℂ x P)) hC
    have hre : ((‖P‖ : ℂ) ^ 2).re = ‖P‖ ^ 2 := by rw [← Complex.ofReal_pow, Complex.ofReal_re]
    simp only [inner_smul_left, inner_self_eq_norm_sq_to_K] at e
    simp at e
    rw [hre] at e
    exact e
  have hpos : 0 < ‖P‖ ^ 2 := by positivity
  have h4 : 2 * (h - n + 1) * ‖P‖ ^ 2 ≤ (-2 * h - 2) * ‖P‖ ^ 2 := by
    rw [key] at hWp
    exact hWp.trans (mul_le_mul_of_nonneg_right hneg hpos.le)
  have h5 := le_of_mul_le_mul_right h4 hpos
  linarith

end No

theorem schmid_casimir (n : ℕ) : SchmidCasimirStatement n := by
  intro ε ν h c N _ _ EN W hE hU hW hS hc hint hmono hgap hneed hp hq
  set lam : Fin n → ℝ := ν + rhoC ε - rhoN ε with hlam
  have hlow : lowK ε lam = ν := by
    ext a; simp only [lowK, hlam, Pi.add_apply, Pi.sub_apply]; ring
  have hW' : IsKIrrHW ε EN (lowK ε lam) W := by rw [hlow]; exact hW
  have hN1 : 2 + (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ)) ≤ hNeed ε := by
    unfold hNeed
    exact le_trans (by linarith [le_max_right (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ))])
      (le_max_left _ _)
  have hN2 : 2 + 3 * (n : ℝ) / 2 ≤ hNeed ε := by
    unfold hNeed
    exact le_trans (by linarith [le_max_left (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ))])
      (le_max_left _ _)
  have hN3 : 16 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) + 8 * Real.sqrt (2 * (min (pOf ε) (qOf ε) : ℝ)) + 2
      ≤ hNeed ε := (le_max_left _ _).trans (le_max_right _ _)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h := by linarith
  have hn : (n : ℝ) < h := by linarith
  have hstd : StdGap ε lam := ⟨hmono, h, hgap, hbig⟩
  have hHC : S7.IsHCParam lam := ⟨hmono, hint⟩
  obtain ⟨T⟩ := HW.kType_exists ε lam hHC
  obtain ⟨μ, hμ⟩ := S7.exists_mu hHC
  have hq0 : 1 ≤ S7.q0 ε := le_min hp hq
  have h8 : 8 * (n : ℝ) * (S7.q0 ε : ℝ) < h := by
    have e : ((S7.q0 ε : ℕ) : ℝ) = (min (pOf ε) (qOf ε) : ℝ) := by
      simp only [S7.q0, Nat.cast_min]
    have hm : 0 ≤ (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) := by positivity
    have hs := Real.sqrt_nonneg (2 * (min (pOf ε) (qOf ε) : ℝ))
    rw [e]
    nlinarith
  have hPsi := (S7.isPsiFor_psiM ε lam h T μ hHC hμ hgap hq0 h8).1
  have hv₀ : T.w ≠ 0 := by
    intro h0
    have h1 := T.w_norm
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hcas := casimir_eq_casVal_of_model hstd hE hU hW'
    (sc_no_of_schmid hE hU hW' hmono hgap hbig hn hS) hD.glRep (isInfUnitary_of_isDerivedOn hσ hD)
    (datumV_isKIrrHW hPsi hv₀) (datumV_casimir hPsi T.w)
  obtain ⟨w, hwW, hw0, -⟩ := hW.2.2.2
  have h1 := hc w hwW
  rw [hcas w hwW] at h1
  simpa using (smul_left_injective ℂ hw0 h1).symm

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

section

noncomputable section

open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

theorem psiDatum : PsiDatumStatement := by
  intro n ε lam h T μ hlam hgap hN hq hμ
  have hg : GapLap ε lam h := ⟨hlam.1, hgap, hN⟩
  have hstd := stdGap_of_gapLap hg
  have h8 : 8 * (n : ℝ) * S7.q0 ε < h := by
    have h1 := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hN
    have e : (min (pOf ε) (qOf ε) : ℝ) = (S7.q0 ε : ℝ) := by simp [S7.q0, Nat.cast_min]
    rw [e] at h1
    have : 0 ≤ (n : ℝ) * S7.q0 ε := by positivity
    nlinarith [Real.sqrt_nonneg (2 * (S7.q0 ε : ℝ))]
  have hP := S7.isPsiFor_psiM ε lam h T μ hlam hμ hgap hq h8
  set Ψ := S7.PsiM T μ with hΨ
  replace hP : IsPsiFor ε lam T Ψ := by first | exact hP | exact hP.1
  have hv₀ : T.w ≠ 0 := fun h0 => by
    have h1 := T.w_norm
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hN0 : ‖uniformisationL2 ε Ψ T.w T.w‖ ≠ 0 := norm_ne_zero_iff.mpr (datumEmbedding_highest_ne_zero hstd hP hv₀)
  set c : ℂ := ((‖uniformisationL2 ε Ψ T.w T.w‖⁻¹ : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := by rw [hc]; exact_mod_cast inv_ne_zero hN0
  let j : T.V →ₗ[ℂ] datumV ε Ψ T.w :=
    { toFun := fun v => ⟨⟨uniformisationL2 ε Ψ T.w (c • v), datumEmbedding_mem_smooth hP T.w _⟩,
        (mem_datumV_iff hP T.w _).2 ⟨c • v, rfl⟩⟩
      map_add' := fun v v' => Subtype.ext (Subtype.ext (by
        show uniformisationL2 ε Ψ T.w (c • (v + v')) = uniformisationL2 ε Ψ T.w (c • v) + uniformisationL2 ε Ψ T.w (c • v')
        rw [smul_add, datumEmbedding_add hP]))
      map_smul' := fun a v => Subtype.ext (Subtype.ext (by
        show uniformisationL2 ε Ψ T.w (c • (a • v)) = a • uniformisationL2 ε Ψ T.w (c • v)
        rw [smul_comm, datumEmbedding_smul hP])) }
  have hj : Function.Bijective j := by
    refine ⟨fun v v' hv => ?_, fun x => ?_⟩
    · have : uniformisationL2 ε Ψ T.w (c • v) = uniformisationL2 ε Ψ T.w (c • v') :=
        congrArg (fun x : datumV ε Ψ T.w => ((x : smD ε (rreg ε)) : L2 ε)) hv
      exact smul_right_injective _ hc0 (uniformisationL2_injective hP hv₀ this)
    · obtain ⟨v, hv⟩ := (mem_datumV_iff hP T.w x).1 x.2
      refine ⟨c⁻¹ • v, Subtype.ext (Subtype.ext ?_)⟩
      show uniformisationL2 ε Ψ T.w (c • c⁻¹ • v) = _
      rw [smul_smul, mul_inv_cancel₀ hc0, one_smul, hv]
  let e := LinearEquiv.ofBijective j hj
  refine ⟨L2 ε, inferInstance, inferInstance, inferInstance, rreg ε, smD ε (rreg ε), smE ε (rreg ε),
    datumV ε Ψ T.w, e.symm, rreg_isURepOn ε, isDerivedOn_smE (rreg_isURepOn ε),
    datumV_isKIrrHW hP hv₀, datumV_casimir hP T.w, datumV_kStable hP T.w, fun g hgm v v' => ?_⟩
  obtain ⟨x, rfl⟩ := e.surjective v
  obtain ⟨x', rfl⟩ := e.surjective v'
  rw [e.symm_apply_apply, e.symm_apply_apply]
  show ⟪uniformisationL2 ε Ψ T.w (c • x'), rreg ε g (uniformisationL2 ε Ψ T.w (c • x))⟫_ℂ = _
  have key : ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ c * c) = 1 := by
    rw [hc, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
    congr 1
    rw [pow_two, mul_mul_mul_comm, mul_inv_cancel₀ hN0, one_mul]
  rw [formulaF hstd hP hv₀ hgm, map_smul, inner_smul_left, inner_smul_right]
  linear_combination ⟪x', Ψ g x⟫_ℂ * key

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end
