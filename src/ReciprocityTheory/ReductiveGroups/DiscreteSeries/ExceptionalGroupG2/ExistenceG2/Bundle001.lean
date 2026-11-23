module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasValK
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothDefs
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.MultOne
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeKType
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle006
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.VNormSqLowKSubRootLt
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CasimirGapAtNoncompactWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle007
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FormulaFA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.FormulaFA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsEquiv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsEquivA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.ClosGenStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KSchur
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.IsInLieAlgebraISmulAddConjTranspose
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RigidUniversal
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.IrredA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.Bundle002

@[expose] public section

section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

section Data

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

theorem data_casValK_gap (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : 2 * (n : ℝ) < h) {μ : Fin n → ℝ} (S : Submodule ℂ H)
    (hS : S ≤ closGen E V) (hST : Formalism.MainNotions.S.IsKTypeOf ε σ μ S) (hμ : μ ≠ lowK ε lam) :
    casValK ε (lowK ε lam) + 2 * (h - n + 1) ≤ casValK ε μ := by
  obtain ⟨w, hwg, hw0, hwK⟩ := exists_khw_genSub_of_kType hσ hD hV.1 hV.2.1 hS hST
  obtain ⟨j, -, hpos, hle⟩ := casimir_gap_at_noncompact_weight hD.glRep (isInfUnitary_of_isDerivedOn hσ hD) hV hc hgap.1 hh hbig
    hwg hw0 hwK hμ
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith

theorem data_vogan (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {μ : Fin n → ℝ} (S : Submodule ℂ H) (hS : S ≤ closGen E V)
    (hST : Formalism.MainNotions.S.IsKTypeOf ε σ μ S) :
    Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam) ≤ Formalism.MainNotions.S.vNormSq ε μ := by
  obtain ⟨w, hwg, hw0, hwK⟩ := exists_khw_genSub_of_kType hσ hD hV.1 hV.2.1 hS hST
  exact vogan_min hD.glRep (isInfUnitary_of_isDerivedOn hσ hD) hV hc hgap hwg hw0 hwK

theorem data_isKTypeOf (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) : Formalism.MainNotions.S.IsKTypeOf ε σ (lowK ε lam) (V.map D.subtype) := by
  exact isKTypeOf_of_isKIrrHW hσ hD hV hVK fun μ x hx hx0 hμ =>
    weights_le_of_irr_hw hD.glRep (isInfUnitary_of_isDerivedOn hσ hD) hV hx hx0 hμ

theorem data_casU (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (x : D) (hx : x ∈ genSub E V) :
    casU ε σ (x : H) = ((casVal lam : ℝ) : ℂ) • (x : H) := by
  have hE := hD.glRep
  let T : Submodule ℂ D := LinearMap.ker (casimir E - ((casVal lam : ℝ) : ℂ) • LinearMap.id)
  have memT : ∀ v : D, v ∈ T ↔ casimir E v = ((casVal lam : ℝ) : ℂ) • v := by
    intro v
    simp only [T, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  have hT : genSub E V ≤ T := by
    apply sInf_le
    refine ⟨fun v hv => (memT v).2 (hc v hv), fun a b v hv => ?_⟩
    rw [memT] at hv ⊢
    have h1 := congrArg (fun f : Module.End ℂ D => f v) (casimir_comm hE a b)
    simp only [Module.End.mul_apply] at h1
    rw [h1, hv, map_smul]
  rw [casU_eq_casimir hD x, (memT x).1 (hT hx)]
  rfl

theorem data_closGen_eq_top (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hirr : Formalism.MainNotions.S.IsIrredOn (UJset ε) σ) (hV0 : V ≠ ⊥) :
    closGen E V = ⊤ := by
  rcases hirr (closGen E V) (Submodule.isClosed_topologicalClosure _)
      (closGen_stable hgap hσ hD hV hc hVK) with h | h
  · exfalso
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV0
    have h2 : ((v : D) : H) ∈ closGen E V := UnitaryGroupOfForm.mem_closGen (E := E) V v hv
    rw [h, Submodule.mem_bot] at h2
    exact hv0 (Subtype.ext h2)
  · exact h

end Data

section Two

variable {ε : Fin n → Bool} {lam : Fin n → ℝ}
  {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {D₁ : Submodule ℂ H₁}
  {E₁ : Fin n → Fin n → Module.End ℂ D₁} {V₁ : Submodule ℂ D₁}
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)} {D₂ : Submodule ℂ H₂}
  {E₂ : Fin n → Fin n → Module.End ℂ D₂} {V₂ : Submodule ℂ D₂}

end Two

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

section

noncomputable section

open Finset Matrix MeasureTheory Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ} {ε : Fin n → Bool}

section Main

variable {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
  {v₀ : T.V}

theorem formulaF (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (v v' : T.V) :
    inner ℂ (uniformisationL2 ε Ψ v₀ v') (rreg ε g (uniformisationL2 ε Ψ v₀ v)) =
      ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) * inner ℂ v' (Ψ g v) := by
  have hσ := rreg_isURepOn ε
  obtain ⟨q, hq⟩ := LinearMap.mem_range.1
    (Submodule.starProjection_apply_mem (LinearMap.range (ffaJ hP v₀)) (rreg ε g (uniformisationL2 ε Ψ v₀ v)))
  have hxo : rreg ε g (uniformisationL2 ε Ψ v₀ v) - uniformisationL2 ε Ψ v₀ q ∈ (LinearMap.range (ffaJ hP v₀))ᗮ := by
    rw [← ffaJ_apply hP v₀ q, hq]
    exact Submodule.sub_starProjection_mem_orthogonal (K := LinearMap.range (ffaJ hP v₀)) _
  have hxj : ∀ w, inner ℂ (rreg ε g (uniformisationL2 ε Ψ v₀ v) - uniformisationL2 ε Ψ v₀ q) (uniformisationL2 ε Ψ v₀ w) = 0 := fun w =>
    Submodule.inner_left_of_mem_orthogonal (LinearMap.mem_range_self (ffaJ hP v₀) w) hxo
  have hfH : rreg ε g (uniformisationL2 ε Ψ v₀ v) ∈ Hlam ε Ψ v₀ :=
    closGen_stable hgap hσ (isDerivedOn_smE hσ) (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀)
      (datumV_kStable hP v₀) g hg _ (datumEmbedding_mem_Hlam hP v)
  have hxH : rreg ε g (uniformisationL2 ε Ψ v₀ v) - uniformisationL2 ε Ψ v₀ q ∈ Hlam ε Ψ v₀ :=
    Submodule.sub_mem _ hfH (datumEmbedding_mem_Hlam hP q)
  have hRH : ∀ k : S7.KG ε, rreg ε (S7.toMK k) (rreg ε g (uniformisationL2 ε Ψ v₀ v) - uniformisationL2 ε Ψ v₀ q) ∈ Hlam ε Ψ v₀ :=
    fun k => closGen_stable hgap hσ (isDerivedOn_smE hσ) (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀)
      (datumV_kStable hP v₀) _ (ffa_toMK_mem k) _ hxH
  have horth : ∀ u v'' : T.V, inner ℂ (ffaB T (Ψ g v - q) (rreg ε g (uniformisationL2 ε Ψ v₀ v) - uniformisationL2 ε Ψ v₀ q) v'')
      (uniformisationL2 ε Ψ v₀ u) = 0 := by
    intro u v''
    have h0 : ∀ k : S7.KG ε, inner ℂ (uniformisationL2 ε Ψ v₀ u)
        (rreg ε (S7.toMK k) (rreg ε g (uniformisationL2 ε Ψ v₀ v) - uniformisationL2 ε Ψ v₀ q)) = 0 := by
      intro k
      rw [← inv_inv k, ← ffa_rreg_adj, rightRegular_datumEmbedding hP]
      exact inner_eq_zero_symm.1 (hxj _)
    rw [← inner_conj_symm, ffaB_inner]
    simp only [h0, mul_zero, integral_zero, map_zero]
  have hB0 := ffa_kmap_zero hgap hP hv₀ (ffaB T (Ψ g v - q) (rreg ε g (uniformisationL2 ε Ψ v₀ v) - uniformisationL2 ε Ψ v₀ q))
    (ffaB_equiv T _ _) (ffaB_mem T _ _ (Hlam ε Ψ v₀) hRH) horth
  have hBv : ∫ k, inner ℂ (T.op k (Ψ g v - q)) v₀ •
      rreg ε (S7.toMK k) (rreg ε g (uniformisationL2 ε Ψ v₀ v) - uniformisationL2 ε Ψ v₀ q) ∂(dk ε) = 0 := by
    have := LinearMap.congr_fun hB0 v₀
    rwa [ffaB_apply, LinearMap.zero_apply] at this
  obtain ⟨yg, hyg⟩ := ffa_UJ_lift hg
  have hxae : ((rreg ε g (uniformisationL2 ε Ψ v₀ v) - uniformisationL2 ε Ψ v₀ q : L2 ε) : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε]
      fun y => jfun Ψ v₀ v (Formalism.MainNotions.S.umat y * g) - jfun Ψ v₀ q (Formalism.MainNotions.S.umat y) := by
    have e1 := rreg_umat_ae ε yg (uniformisationL2 ε Ψ v₀ v)
    have e2 := (measurePreserving_mul_right ε yg).quasiMeasurePreserving.ae_eq_comp (uniformisationL2_ae_eq_jfun hP v₀ v)
    filter_upwards [Lp.coeFn_sub (rreg ε g (uniformisationL2 ε Ψ v₀ v)) (uniformisationL2 ε Ψ v₀ q), e1, e2, uniformisationL2_ae_eq_jfun hP v₀ q]
      with y h0 h1 h2 h3
    rw [h0, Pi.sub_apply, h3, ← hyg, h1]
    congr 1
  have hFc : ContinuousOn (fun y => jfun Ψ v₀ v (y * g) - jfun Ψ v₀ q y) (UJset ε) :=
    ((ffa_jfun_cont hP v₀ v).comp (continuousOn_id.mul continuousOn_const)
      (fun y hy => rq_UJ_mul hy hg)).sub (ffa_jfun_cont hP v₀ q)
  have hev := ffa_eval hFc hxae _ (ffa_cont_coef T (Ψ g v - q) v₀) hBv
  have hΨk : ∀ (k : S7.KG ε) (h : Matrix (Fin n) (Fin n) ℂ), h ∈ UJset ε →
      Ψ (S7.toMK k * h) = T.op k * Ψ h := by
    intro k h hh
    have e := hP.1 k 1 h hh
    rwa [show S7.toMK (1 : S7.KG ε) = 1 from rfl, mul_one, ffa_op_one, mul_one] at e
  have hΨk1 : ∀ k : S7.KG ε, Ψ (S7.toMK k) = T.op k := by
    intro k
    have e := hΨk k 1 (ffa_toMK_mem (1 : S7.KG ε))
    rwa [mul_one, hP.2.1, mul_one] at e
  have hint : ∀ k : S7.KG ε, inner ℂ (T.op k (Ψ g v - q)) v₀ *
      (jfun Ψ v₀ v (S7.toMK k * g) - jfun Ψ v₀ q (S7.toMK k)) =
        ((‖inner ℂ v₀ (T.op k (Ψ g v - q))‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    show inner ℂ (T.op k (Ψ g v - q)) v₀ *
      (inner ℂ v₀ (Ψ (S7.toMK k * g) v) - inner ℂ v₀ (Ψ (S7.toMK k) q)) = _
    rw [hΨk k g hg, hΨk1 k, ContinuousLinearMap.mul_apply, ← inner_sub_right, ← map_sub,
      ← inner_conj_symm, Complex.conj_mul', Complex.ofReal_pow]
  have hI : ∫ k, ‖inner ℂ v₀ (T.op k (Ψ g v - q))‖ ^ 2 ∂(dk ε) = 0 := by
    have e2 : ((∫ k, ‖inner ℂ v₀ (T.op k (Ψ g v - q))‖ ^ 2 ∂(dk ε) : ℝ) : ℂ) = 0 := by
      rw [← integral_complex_ofReal]
      refine Eq.trans ?_ hev
      congr 1
      funext k
      exact (hint k).symm
    exact_mod_cast e2
  have hD : Ψ g v - q = 0 := by
    have hk := kschur_coef T v₀ (Ψ g v - q)
    rw [hI, mul_zero] at hk
    have hv0 : ‖v₀‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hv₀)
    have h2 : ‖Ψ g v - q‖ ^ 2 = 0 := by
      rcases mul_eq_zero.1 hk.symm with h | h
      · exact h
      · exact absurd h hv0
    exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h2)
  have hqv : q = Ψ g v := (sub_eq_zero.1 hD).symm
  have hdec : rreg ε g (uniformisationL2 ε Ψ v₀ v) =
      (rreg ε g (uniformisationL2 ε Ψ v₀ v) - uniformisationL2 ε Ψ v₀ q) + uniformisationL2 ε Ψ v₀ q := (sub_add_cancel _ _).symm
  rw [hdec, inner_add_right, inner_eq_zero_symm.1 (hxj v'), zero_add, hqv, ffa_form hP]

theorem datumEmbedding_highest_ne_zero (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) : uniformisationL2 ε Ψ v₀ T.w ≠ 0 := by
  intro hz

  have hform := ffa_form (v₀ := v₀) hP v₀ v₀
  rw [hz, norm_zero] at hform
  have hJ : uniformisationL2 ε Ψ v₀ v₀ = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℂ)]
    simpa using hform
  have hF := ffa_jfun_cont hP v₀ v₀
  have hFk : Continuous fun k : S7.KG ε => jfun Ψ v₀ v₀ (S7.toMK k) :=
    hF.comp_continuous ffa_cont_toMK ffa_toMK_mem
  have hc : Continuous fun k : S7.KG ε => starRingEnd ℂ (jfun Ψ v₀ v₀ (S7.toMK k)) :=
    Complex.continuous_conj.comp hFk
  have hint := ffa_eval hF (uniformisationL2_ae_eq_jfun hP v₀ v₀) _ hc (by simp [hJ])

  have hG : Continuous fun k : S7.KG ε => Complex.normSq (jfun Ψ v₀ v₀ (S7.toMK k)) :=
    Complex.continuous_normSq.comp hFk
  have hGint : ∫ k, Complex.normSq (jfun Ψ v₀ v₀ (S7.toMK k)) ∂(dk ε) = 0 := by
    have h2 : ∫ k, ((Complex.normSq (jfun Ψ v₀ v₀ (S7.toMK k)) : ℝ) : ℂ) ∂(dk ε) = 0 := by
      rw [← hint]
      congr 1
      funext k
      rw [← Complex.mul_conj, mul_comm]
    rw [integral_complex_ofReal] at h2
    exact_mod_cast h2
  have ht : S7.toMK (1 : S7.KG ε) = 1 := by
    simp [S7.toMK]
  have h1 : Complex.normSq (jfun Ψ v₀ v₀ (S7.toMK (1 : S7.KG ε))) ≠ 0 := by
    simp [jfun, ht, hP.2.1, hv₀]
  have hI := ffa_intK (ε := ε) hG
  have hpos : 0 < ∫ k, Complex.normSq (jfun Ψ v₀ v₀ (S7.toMK k)) ∂(dk ε) := by
    rw [integral_pos_iff_support_of_nonneg (fun k => Complex.normSq_nonneg _) hI]
    delta dk S7.muK
    rw [smul_apply, smul_eq_mul]
    exact ENNReal.mul_pos (ENNReal.inv_ne_zero.2 (CompactHaarProbability.muK_univ_ne_top ε))
      (hG.isOpen_support.measure_pos (Measure.haar : Measure (S7.KG ε)) ⟨1, h1⟩).ne'
  linarith

private theorem inner_orthogonalProjection_of_mem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (a : E) (ha : a ∈ K) (y : E) :
    inner ℂ (⟨a, ha⟩ : K) (K.orthogonalProjectionOnto y) = inner ℂ a y := by
  rw [Submodule.coe_inner]
  first
  | exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left ⟨a, ha⟩ y
  | exact Submodule.inner_orthogonalProjection_eq_of_mem_left ⟨a, ha⟩ y
  | exact inner_orthogonalProjection_eq_of_mem_left ⟨a, ha⟩ y
  | simp

theorem formulaF_sigLam (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (v v' : T.V) :
    inner ℂ (⟨uniformisationL2 ε Ψ v₀ v', datumEmbedding_mem_Hlam hP v'⟩ : Hlam ε Ψ v₀)
        (sigLam ε Ψ v₀ g ⟨uniformisationL2 ε Ψ v₀ v, datumEmbedding_mem_Hlam hP v⟩) =
      ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) * inner ℂ v' (Ψ g v) := by
  rw [← formulaF hgap hP hv₀ hg v v']
  exact inner_orthogonalProjection_of_mem (Hlam ε Ψ v₀) _ (datumEmbedding_mem_Hlam hP v') _

end Main

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

namespace KTypeIsomorphism

section Gen

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

theorem closGen_le_span (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {ι : Type*} (y : ι → H)
    (hy : ∀ i, y i ∈ closGen E V) (hst : ∀ g ∈ UJset ε, ∀ i, ∃ j, σ g (y i) = y j)
    (hne : ∃ i, y i ≠ 0) :
    closGen E V ≤ (Submodule.span ℂ (Set.range y)).topologicalClosure := by
  have hSc : IsClosed ((Submodule.span ℂ (Set.range y)).topologicalClosure : Set H) :=
    Submodule.isClosed_topologicalClosure _
  have hcl : IsClosed (closGen E V : Set H) := Submodule.isClosed_topologicalClosure _
  have hspan : Submodule.span ℂ (Set.range y) ≤ closGen E V :=
    Submodule.span_le.2 (Set.range_subset_iff.2 hy)
  have hS : (Submodule.span ℂ (Set.range y)).topologicalClosure ≤ closGen E V :=
    Submodule.topologicalClosure_minimal _ hspan hcl
  have hSG : ∀ g ∈ UJset ε, ∀ x ∈ (Submodule.span ℂ (Set.range y)).topologicalClosure,
      σ g x ∈ (Submodule.span ℂ (Set.range y)).topologicalClosure := by
    intro g hg
    have hle : Submodule.span ℂ (Set.range y) ≤
        ((Submodule.span ℂ (Set.range y)).topologicalClosure).comap (σ g : H →ₗ[ℂ] H) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := hst g hg i
      show σ g (y i) ∈ (Submodule.span ℂ (Set.range y)).topologicalClosure
      rw [hj]
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨j, rfl⟩)
    have hc' : IsClosed ((((Submodule.span ℂ (Set.range y)).topologicalClosure).comap
        (σ g : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H) :=
      hSc.preimage (σ g).continuous
    exact fun x hx => Submodule.topologicalClosure_minimal _ hle hc' hx
  rcases rigid_irred hgap hσ hD hV hc hVK _ hS hSc hSG with h | h
  · exfalso
    obtain ⟨i, hi⟩ := hne
    have : y i ∈ (Submodule.span ℂ (Set.range y)).topologicalClosure :=
      Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)
    rw [h, Submodule.mem_bot] at this
    exact hi this
  · exact h.symm.le

end Gen

section Phi

variable {ε : Fin n → Bool}
  {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {D₁ : Submodule ℂ H₁}
  {E₁ : Fin n → Fin n → Module.End ℂ D₁} {V₁ : Submodule ℂ D₁}
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)} {D₂ : Submodule ℂ H₂}
  {E₂ : Fin n → Fin n → Module.End ℂ D₂} {V₂ : Submodule ℂ D₂}

end Phi

end KTypeIsomorphism

variable {ε : Fin n → Bool} {lam : Fin n → ℝ}
  {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {D₁ : Submodule ℂ H₁}
  {E₁ : Fin n → Fin n → Module.End ℂ D₁} {V₁ : Submodule ℂ D₁}
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)} {D₂ : Submodule ℂ H₂}
  {E₂ : Fin n → Fin n → Module.End ℂ D₂} {V₂ : Submodule ℂ D₂}

theorem data_unitary_equiv (hgap : StdGap ε lam)
    (hσ₁ : IsURepOn (UJset ε) σ₁) (hD₁ : IsDerivedOn ε σ₁ D₁ E₁) (hV₁ : IsKIrrHW ε E₁ (lowK ε lam) V₁)
    (hc₁ : ∀ v ∈ V₁, casimir E₁ v = (casVal lam : ℂ) • v)
    (hVK₁ : ∀ k ∈ Kset ε, ∀ v ∈ V₁, ∃ w ∈ V₁, (w : H₁) = σ₁ k v) (hV₁0 : V₁ ≠ ⊥)
    (hσ₂ : IsURepOn (UJset ε) σ₂) (hD₂ : IsDerivedOn ε σ₂ D₂ E₂) (hV₂ : IsKIrrHW ε E₂ (lowK ε lam) V₂)
    (hc₂ : ∀ v ∈ V₂, casimir E₂ v = (casVal lam : ℂ) • v)
    (hVK₂ : ∀ k ∈ Kset ε, ∀ v ∈ V₂, ∃ w ∈ V₂, (w : H₂) = σ₂ k v) (hV₂0 : V₂ ≠ ⊥) :
    ∃ U : closGen E₁ V₁ ≃ₗᵢ[ℂ] closGen E₂ V₂, ∀ g ∈ UJset ε, ∀ x y : closGen E₁ V₁,
      (x : H₁) = σ₁ g (y : H₁) → ((U x : closGen E₂ V₂) : H₂) = σ₂ g ((U y : closGen E₂ V₂) : H₂) := by
  obtain ⟨φ, hφK, hφI⟩ := KTypeIsomorphism.exists_phi hσ₁ hD₁ hV₁ hσ₂ hD₂ hV₂
  have huniv := rigid_universal hσ₁ hD₁ hV₁ hc₁ hVK₁ hσ₂ hD₂ hV₂ hc₂ hVK₂ hgap φ hφK hφI
  let y₁ : ↥(UJset ε) × ↥V₁ → H₁ := fun p => σ₁ p.1.1 ((p.2 : D₁) : H₁)
  let y₂ : ↥(UJset ε) × ↥V₁ → H₂ := fun p => σ₂ p.1.1 (((φ p.2 : V₂) : D₂) : H₂)
  have split : ∀ g ∈ UJset ε, ∀ g' ∈ UJset ε, ∃ h ∈ UJset ε,
      σ₁ g' = (σ₁ g).comp (σ₁ h) ∧ σ₂ g' = (σ₂ g).comp (σ₂ h) := by
    intro g hg g' hg'
    obtain ⟨gi, hgi, hggi⟩ := UnitaryGroupOfForm.inv_mem_UJ hg
    have hm : gi * g' ∈ UJset ε := mul_mem_unitaryJ hgi hg'
    have e1 : g * (gi * g') = g' := by rw [← Matrix.mul_assoc, hggi, Matrix.one_mul]
    exact ⟨gi * g', hm, by rw [← hσ₁.1.2 g hg _ hm, e1], by rw [← hσ₂.1.2 g hg _ hm, e1]⟩
  have hI : ∀ i j, inner ℂ (y₂ i) (y₂ j) = inner ℂ (y₁ i) (y₁ j) := by
    rintro ⟨⟨g, hg⟩, v⟩ ⟨⟨g', hg'⟩, v'⟩
    obtain ⟨h, hh, e₁, e₂⟩ := split g hg g' hg'
    show inner ℂ (σ₂ g (((φ v : V₂) : D₂) : H₂)) (σ₂ g' (((φ v' : V₂) : D₂) : H₂)) =
      inner ℂ (σ₁ g ((v : D₁) : H₁)) (σ₁ g' ((v' : D₁) : H₁))
    rw [e₁, e₂, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      UnitaryGroupOfForm.inner_map_map' hσ₂ hg, UnitaryGroupOfForm.inner_map_map' hσ₁ hg]
    exact huniv h hh v' v
  have h₁ : ∀ i, y₁ i ∈ closGen E₁ V₁ := fun p =>
    closGen_stable hgap hσ₁ hD₁ hV₁ hc₁ hVK₁ p.1.1 p.1.2 _ (UnitaryGroupOfForm.mem_closGen V₁ (p.2 : D₁) p.2.2)
  have h₂ : ∀ i, y₂ i ∈ closGen E₂ V₂ := fun p =>
    closGen_stable hgap hσ₂ hD₂ hV₂ hc₂ hVK₂ p.1.1 p.1.2 _
      (UnitaryGroupOfForm.mem_closGen V₂ ((φ p.2 : V₂) : D₂) (φ p.2).2)
  have hτ₁ : ∀ g (hg : g ∈ UJset ε) (p : ↥(UJset ε) × ↥V₁),
      σ₁ g (y₁ p) = y₁ (⟨g * p.1.1, mul_mem_unitaryJ hg p.1.2⟩, p.2) := by
    intro g hg p
    show σ₁ g (σ₁ p.1.1 _) = σ₁ (g * p.1.1) _
    rw [hσ₁.1.2 g hg _ p.1.2]
    rfl
  have hτ₂ : ∀ g (hg : g ∈ UJset ε) (p : ↥(UJset ε) × ↥V₁),
      σ₂ g (y₂ p) = y₂ (⟨g * p.1.1, mul_mem_unitaryJ hg p.1.2⟩, p.2) := by
    intro g hg p
    show σ₂ g (σ₂ p.1.1 _) = σ₂ (g * p.1.1) _
    rw [hσ₂.1.2 g hg _ p.1.2]
    rfl
  obtain ⟨v₀, hv₀V, hv₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV₁0
  have hne₁ : ∃ i, y₁ i ≠ 0 := by
    refine ⟨(⟨1, one_mem_unitaryJ ε⟩, ⟨v₀, hv₀V⟩), ?_⟩
    show σ₁ 1 ((v₀ : D₁) : H₁) ≠ 0
    rw [hσ₁.1.1]
    intro h
    have h' : ((v₀ : D₁) : H₁) = 0 := h
    exact hv₀ (Subtype.ext h')
  have hne₂ : ∃ i, y₂ i ≠ 0 := by
    refine ⟨(⟨1, one_mem_unitaryJ ε⟩, ⟨v₀, hv₀V⟩), ?_⟩
    show σ₂ 1 (((φ ⟨v₀, hv₀V⟩ : V₂) : D₂) : H₂) ≠ 0
    rw [hσ₂.1.1]
    intro h
    have h' : (((φ ⟨v₀, hv₀V⟩ : V₂) : D₂) : H₂) = 0 := h
    have hh := hφI ⟨v₀, hv₀V⟩ ⟨v₀, hv₀V⟩
    rw [h', inner_zero_left] at hh
    exact hv₀ (Subtype.ext (inner_self_eq_zero.1 hh.symm))
  have hd₁ := KTypeIsomorphism.closGen_le_span hgap hσ₁ hD₁ hV₁ hc₁ hVK₁ y₁ h₁
    (fun g hg i => ⟨_, hτ₁ g hg i⟩) hne₁
  have hd₂ := KTypeIsomorphism.closGen_le_span hgap hσ₂ hD₂ hV₂ hc₂ hVK₂ y₂ h₂
    (fun g hg i => ⟨_, hτ₂ g hg i⟩) hne₂
  obtain ⟨U, hU⟩ := KTypeIsomorphism.gns_extend y₁ y₂ hI (closGen E₁ V₁) (closGen E₂ V₂)
    (Submodule.isClosed_topologicalClosure _) (Submodule.isClosed_topologicalClosure _) h₁ h₂ hd₁ hd₂
  refine ⟨U, fun g hg x y hxy => ?_⟩
  exact KTypeIsomorphism.gns_intertwine y₁ y₂ _ _ h₁ hd₁ U hU (σ₁ g) (σ₂ g)
    (fun p => (⟨g * p.1.1, mul_mem_unitaryJ hg p.1.2⟩, p.2)) (hτ₁ g hg) (hτ₂ g hg)
    (closGen_stable hgap hσ₁ hD₁ hV₁ hc₁ hVK₁ g hg) x y hxy

end ReciprocityTheory.ChartRestriction.DS.G2
end
end
