module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.BlockAnti
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.DSymmHypsInhabited
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.DiracSquareMemLayer
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasValK
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.MultOne
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.FfExpWedgeHasDeriv
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.AdPhysApplySingle
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFPrimeB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle009
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFockE
public import Formalism.RealPlaceAnalysis.Bundle002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFockB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsKfin
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothDefs
public import Formalism.RealPlaceAnalysis.Bundle001
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.HasDerivAtRealOfComplex
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.Bundle001

@[expose] public section

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

theorem lf_dom_block {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : BlockAnti ε lam) :
    ∀ a b : Fin n, a < b → ε a = ε b →
      (lowK ε lam + (rhoHol ε - rhoN ε)) b ≤ (lowK ε lam + (rhoHol ε - rhoN ε)) a := by
  have key : ∀ d : ℕ, ∀ a b : Fin n, b.val - a.val = d → a < b → ε a = ε b →
      rhoC ε a - rhoC ε b ≤ lam a - lam b := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro a b hd hab he
      by_cases hc : ∃ c, a < c ∧ c < b ∧ ε c = ε a
      · obtain ⟨c, hac, hcb, hce⟩ := hc
        have hac' := Fin.lt_def.mp hac
        have hcb' := Fin.lt_def.mp hcb
        have e1 := ih (c.val - a.val) (by omega) a c rfl hac hce.symm
        have e2 := ih (b.val - c.val) (by omega) c b rfl hcb (hce.trans he)
        linarith
      · simp only [not_exists, not_and] at hc
        have h1 := HW.rhoC_consec ε hab he hc
        have h2 := hlam a b hab he
        linarith
  intro a b hab he
  have e := key _ a b rfl hab he
  have hh := lf_rhoHol_eq ε he
  simp only [lowK, Pi.add_apply, Pi.sub_apply]
  linarith

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem exists_nonzero_physical_highestWeight_vector_tensFock (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ N} (hE : IsGlRep E)
    {lam : Fin n → ℝ} (hlam : BlockAnti ε lam) {V : Submodule ℂ N} (hV : IsKIrrHW ε E (lowK ε lam) V) :
    ∃ x ∈ tensFock (n := n) V, x ∈ physicalSubspace ε ∧ x ≠ 0 ∧
      IsKHWVec ε (diagE ε (eT E) cpT cmT) (lam - rhoC ε + rhoHol ε) x := by
  classical
  have hF : Formalism.REAL.KRel ε E := fun a b c d _ _ => hE a b c d
  obtain ⟨x, hxV, hx0, hxw, hxh⟩ := HW.parthasarathy_tensor_matrix ε hF hV (lfMat_kRel ε)
    (fun a b h => lfMat_conjTranspose ε h) (ν := rhoHol ε - rhoN ε) (f := Pi.single (lowerWedgeAlt ε) 1)
    (fun h => by simpa using congrFun h (lowerWedgeAlt ε))
    (fun a => lfMat_mulVec_single ε a a (lowerWedgeAlt ε) _ (lowerWedge_weight ε a))
    (fun a b hba he => by
      simpa using lfMat_mulVec_single ε a b (lowerWedgeAlt ε) 0 (by rw [lowerWedge_killed_by_lowering ε hba he, zero_smul]))
    (lf_dom_block hlam)
  refine ⟨lfLift ε x, lfLift_mem_tensFock ε hxV, lfLift_mem_physSub ε x, lfLift_ne_zero ε hx0, ?_⟩
  have hμ : lam - rhoC ε + rhoHol ε = lowK ε lam + (rhoHol ε - rhoN ε) := by
    unfold lowK; abel
  rw [hμ]
  exact lfLift_isKHWVec ε hxw hxh

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

section

noncomputable section

open MeasureTheory MvPolynomial

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

theorem finite_monomials_of_degree_le (d : ℕ) : {m : EntIdx n →₀ ℕ | (m.sum fun _ e => e) ≤ d}.Finite := by
  have h1 : {f : EntIdx n →₀ ℕ | ∀ a, f a ≤ d}.Finite :=
    (Set.Finite.pi' fun _ ↦ Set.finite_le_nat _).preimage DFunLike.coe_injective.injOn
  exact h1.subset fun m hm i ↦ (eq_or_ne (m i) 0).elim
    (fun h ↦ h.trans_le d.zero_le) fun h ↦
      (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) <| Finsupp.mem_support_iff.mpr h).trans hm

theorem range_one_layer {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {lam : Fin n → ℝ}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}
    (hstd : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hdense : closGen E V = ⊤)
    {Kg : Type*} [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μK : Measure Kg) [IsFiniteMeasure μK] [μK.IsMulLeftInvariant]
    (φ : Kg → Matrix (Fin n) (Fin n) ℂ) (hφc : Continuous φ) (hφ1 : φ 1 = 1)
    (hφm : ∀ a b, φ (a * b) = φ a * φ b) (hφK : ∀ g, φ g ∈ Kset ε) (hφs : ∀ m ∈ Kset ε, ∃ g, φ g = m)
    (P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ) :
    ∃ j : ℕ, ∀ u : H,
      ∫ k, MvPolynomial.eval (entVar (φ k)) P • σ (φ k) u ∂μK ∈ (layer ε E V j).map D.subtype := by
  classical
  have hE := hD.glRep
  have hU : IsInfUnitary ε E := isInfUnitary_of_isDerivedOn hσ hD
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
      Integrable (fun k => eval (entVar (φ k)) Q • σ (φ k) u) μK := fun Q u =>
    ((hpolyc Q).smul (horb u)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let Xu : H → MvPolynomial (EntIdx n) ℂ →ₗ[ℂ] H := fun u =>
    { toFun := fun Q => ∫ k, eval (entVar (φ k)) Q • σ (φ k) u ∂μK
      map_add' := fun Q R => by
        simp only [map_add (f := _), add_smul]
        exact integral_add (hint Q u) (hint R u)
      map_smul' := fun c Q => by
        simp only [smul_eval, mul_smul, RingHom.id_apply]
        exact integral_smul c _ }
  have hXu : ∀ u Q, Xu u Q = ∫ k, eval (entVar (φ k)) Q • σ (φ k) u ∂μK := fun _ _ => rfl
  have htr : ∀ u Q g, σ (φ g) (Xu u Q) = Xu u (bind₁ (trF (φ g⁻¹)) Q) := by
    intro u Q g
    rw [hXu, hXu, ← (σ (φ g)).integral_comp_comm (hint Q u)]
    have e2 : ∫ k, σ (φ g) (eval (entVar (φ k)) Q • σ (φ k) u) ∂μK =
        ∫ k, eval (entVar (φ (g⁻¹ * (g * k)))) Q • σ (φ (g * k)) u ∂μK := by
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
  set d := P.totalDegree
  set Wm : Set (Fin n → ℝ) := wtM '' {m : EntIdx n →₀ ℕ | (m.sum fun _ e => e) ≤ d}
  have hWfin : Wm.Finite := (finite_monomials_of_degree_le d).image _
  let Sd : H → Submodule ℂ H := fun u => (restrictTotalDegree (EntIdx n) ℂ d).map (Xu u)
  have hSdfd : ∀ u, FiniteDimensional ℂ (Sd u) := fun u => Module.Finite.map _ _
  have hSK : ∀ u, ∀ k ∈ Kset ε, ∀ x ∈ Sd u, σ k x ∈ Sd u := by
    intro u k hk x hx
    obtain ⟨g, rfl⟩ := hφs k hk
    obtain ⟨Q, hQ, rfl⟩ := hx
    rw [htr]
    refine Submodule.mem_map_of_mem ?_
    rw [SetLike.mem_coe, mem_restrictTotalDegree] at hQ
    rw [mem_restrictTotalDegree]
    exact (totalDegree_bind_le_of_linear _ (trF_totalDegree _) Q).trans hQ
  have hWS : ∀ u μ, (∃ s ∈ Sd u, s ≠ 0 ∧ Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ s) → μ ∈ Wm := by
    rintro u μ ⟨s, ⟨Q, hQ, rfl⟩, hs0, hsw⟩
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
  choose kf hkf using fun μ => khw_mem_layer hE hU hV hc hstd μ
  refine ⟨hWfin.toFinset.sup kf, fun u => ?_⟩
  have := hSdfd u
  have hle := kfin_key hσ hD hV.1 hV.2.1 (Sd u) (by rw [hdense]; exact le_top) (hSK u) (hWfin.toFinset.sup kf)
    (fun μ w hw hwk hμS => layer_mono (Finset.le_sup ((hWfin.mem_toFinset).2 (hWS u μ hμS))) (hkf μ w hw hwk))
  exact hle (Submodule.mem_map_of_mem ((mem_restrictTotalDegree _ _ P).2 le_rfl))

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

section T

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem sgE_cpT (a b : Fin n) :
    sgE ε (cpT (N := N)) cmT a b = LinearMap.lTensor N (sgE ε (cpFock (n := n)) cmFock a b) := by
  have e : ∀ f : Module.End ℂ (Fock n), LinearMap.lTensor N f = Module.End.lTensorAlgHom ℂ (Fock n) N f :=
    fun f => rfl
  unfold sgE
  split_ifs <;> rw [e] <;> simp only [map_sum, map_mul, map_neg, map_zero] <;> rfl

theorem tcoef_eq_sum (φ : Module.Dual ℂ (Fock n)) (y : TensorProduct ℂ N (Fock n)) :
    tcoef φ y = ∑ s : Finset (Fin (n * n)), φ (fockBasis n s) • tcoef ((fockBasis n).coord s) y := by
  conv_lhs => rw [tcoef_expand y]

  simp only [map_sum, tcoef_tmul]

theorem tco_actDiag (E : Fin n → Fin n → Module.End ℂ N) (X : Matrix (Fin n) (Fin n) ℂ)
    (y : TensorProduct ℂ N (Fock n)) (s : Finset (Fin (n * n))) :
    tcoef ((fockBasis n).coord s) (actM (diagE ε (eT E) cpT cmT) X y) =
      actM E X (tcoef ((fockBasis n).coord s) y) + tcoef ((fockBasis n).coord s ∘ₗ sgX ε X) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul m f =>

    simp only [actM, diagE, sgE_cpT, eT, sgX, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply,
    TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.id_apply, map_sum, map_smul, map_add,
    tcoef_tmul, LinearMap.coe_comp, Function.comp_apply, smul_add, Finset.sum_add_distrib, smul_smul]
    rw [Finset.smul_sum, Finset.sum_smul]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [smul_smul, mul_comm]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [smul_eq_mul]
  | add y y' hy hy' =>
    rw [map_add (f := _), map_add (f := _), hy, hy', map_add (f := _), map_add (f := _), map_add (f := _)]
    abel

end T

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem tco_wK (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    (y : TensorProduct ℂ D (Fock n)) (s : Finset (Fin (n * n))) :
    tcoef ((fockBasis n).coord s) (wK hD hk y) =
      ∑ s', (fockBasis n).coord s (ff ε k (fockBasis n s')) • sigD hD hk (tcoef ((fockBasis n).coord s') y) := by
  conv_lhs => rw [tcoef_expand y]

  simp only [map_sum, wK, TensorProduct.map_tmul, tcoef_tmul, AlgHom.toLinearMap_apply]

theorem tco_wK_hasDeriv (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inK ε X) (y : TensorProduct ℂ D (Fock n)) (s : Finset (Fin (n * n))) :
    HasDerivAt (fun t : ℝ => ((tcoef ((fockBasis n).coord s)
        (wK hD (exp_mem_Kset (USum.inK_real_smul hX t)) y) : D) : H))
      ((tcoef ((fockBasis n).coord s) (actM (diagE ε (eT E) cpT cmT) X y) : D) : H) 0 := by
  have hXh : Xᴴ = -X := ((HW.inK_iff' ε X).1 hX).1
  have hfun : (fun t : ℝ => ((tcoef ((fockBasis n).coord s)
      (wK hD (exp_mem_Kset (USum.inK_real_smul hX t)) y) : D) : H)) =
      fun t : ℝ => ∑ s', (fockBasis n).coord s (ff ε (NormedSpace.exp ((t : ℂ) • X)) (fockBasis n s')) •
        σ (NormedSpace.exp ((t : ℂ) • X)) ((tcoef ((fockBasis n).coord s') y : D) : H) := by
    funext t
    rw [tco_wK, Submodule.coe_sum]
    rfl
  rw [hfun]
  have hc : ∀ s', HasDerivAt (fun t : ℝ => (fockBasis n).coord s (ff ε (NormedSpace.exp ((t : ℂ) • X))
      (fockBasis n s'))) ((fockBasis n).coord s (sgX ε X (fockBasis n s'))) 0 := by
    intro s'
    have := hasDerivAt_pi.1 (ff_exp_hasDeriv (ε := ε) hXh (fockBasis n s')) s
    simpa only [Module.Basis.equivFun_apply, Module.Basis.coord_apply] using this
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun s' _ =>
    (hc s').fun_smul (hD.deriv X hX.1 (tcoef ((fockBasis n).coord s') y))
  convert h using 1
  have h0 : NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1 := by simp
  simp only [h0, ff_one, AlgHom.id_apply, hσ.1.1, ContinuousLinearMap.one_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  rw [tco_actDiag, Submodule.coe_add, tcoef_eq_sum ((fockBasis n).coord s ∘ₗ sgX ε X) y, Submodule.coe_sum,
    Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_eq_single s (fun b _ hb => by simp [hb]) (by simp)]
    simp

def coordH : TensorProduct ℂ D (Fock n) →ₗ[ℂ] (Finset (Fin (n * n)) → H) :=
  LinearMap.pi fun s => D.subtype ∘ₗ tcoef ((fockBasis n).coord s)

theorem coordH_apply (y : TensorProduct ℂ D (Fock n)) (s : Finset (Fin (n * n))) :
    coordH y s = ((tcoef ((fockBasis n).coord s) y : D) : H) := rfl

theorem coordH_injective : Function.Injective (coordH (D := D) (n := n)) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro y hy
  rw [LinearMap.mem_ker] at hy
  rw [Submodule.mem_bot, tcoef_expand y]
  refine Finset.sum_eq_zero fun s _ => ?_
  have : ((tcoef ((fockBasis n).coord s) y : D) : H) = 0 := congrFun hy s
  rw [show tcoef ((fockBasis n).coord s) y = 0 from Subtype.ext this, TensorProduct.zero_tmul]

theorem actDiag_mem_of_wK (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (S' : Submodule ℂ (TensorProduct ℂ D (Fock n))) (hS : FiniteDimensional ℂ S')
    (hK : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ S', wK hD hk y ∈ S')
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) {y : TensorProduct ℂ D (Fock n)} (hy : y ∈ S') :
    actM (diagE ε (eT E) cpT cmT) X y ∈ S' := by
  let T := S'.map (coordH (D := D) (n := n))
  have : FiniteDimensional ℂ T := Module.Finite.map S' coordH
  have hTc : IsClosed (T : Set (Finset (Fin (n * n)) → H)) := Submodule.closed_of_finiteDimensional T
  have hder : HasDerivAt (fun t : ℝ => coordH (wK hD (exp_mem_Kset (USum.inK_real_smul hX t)) y))
      (coordH (actM (diagE ε (eT E) cpT cmT) X y)) 0 :=
    hasDerivAt_pi.2 fun s => tco_wK_hasDeriv hσ hD hX y s
  have h1 : ∀ t : ℝ, coordH (wK hD (exp_mem_Kset (USum.inK_real_smul hX t)) y) ∈ T :=
    fun t => Submodule.mem_map_of_mem (hK _ _ y hy)
  have hmem : coordH (actM (diagE ε (eT E) cpT cmT) X y) ∈ T :=
    hTc.mem_of_tendsto hder.tendsto_slope_zero (Filter.Eventually.of_forall fun t =>
      Submodule.smul_of_tower_mem _ _ (Submodule.sub_mem _ (h1 _) (h1 _)))
  obtain ⟨w, hw, hweq⟩ := Submodule.mem_map.1 hmem
  rwa [coordH_injective hweq] at hw

theorem diagE_mem_of_wK (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (S' : Submodule ℂ (TensorProduct ℂ D (Fock n))) (hS : FiniteDimensional ℂ S')
    (hK : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ S', wK hD hk y ∈ S')
    {a b : Fin n} (hab : ε a = ε b) {y : TensorProduct ℂ D (Fock n)} (hy : y ∈ S') :
    diagE ε (eT E) cpT cmT a b y ∈ S' := by
  have h1 := actDiag_mem_of_wK hσ hD S' hS hK (USum.inK_zM hab 1) hy
  have h2 := actDiag_mem_of_wK hσ hD S' hS hK (USum.inK_zM hab Complex.I) hy
  rw [USum.actM_zM] at h1 h2
  have gen : ∀ x y : TensorProduct ℂ D (Fock n),
      x = (1 / 2 : ℂ) • ((x - y) - Complex.I • (Complex.I • x - (-Complex.I) • y)) := by
    intro x y
    rw [smul_sub Complex.I, smul_smul, smul_smul, show Complex.I * Complex.I = -1 from Complex.I_mul_I,
      show Complex.I * -Complex.I = 1 by rw [mul_neg, Complex.I_mul_I, neg_neg]]
    module
  have key : diagE ε (eT E) cpT cmT a b y = (1 / 2 : ℂ) •
      ((((1 : ℂ) • diagE ε (eT E) cpT cmT a b - star (1 : ℂ) • diagE ε (eT E) cpT cmT b a) y) -
        Complex.I • (((Complex.I • diagE ε (eT E) cpT cmT a b - star Complex.I • diagE ε (eT E) cpT cmT b a)) y)) := by
    simp only [Complex.star_def, Complex.conj_I, map_one]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, one_smul]
    exact gen _ _
  rw [key]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ h1 (Submodule.smul_mem _ _ h2))

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end
