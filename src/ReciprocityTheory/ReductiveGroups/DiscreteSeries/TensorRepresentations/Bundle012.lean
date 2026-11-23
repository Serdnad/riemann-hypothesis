module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedEmbeddingToM
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaA
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CoefEmbed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle005
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigLamMemLpOfNe
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle008
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SqIntA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.ClosGenStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.RorthFunctionalEqZero
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothA

@[expose] public section

section

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

private theorem finiteMeasure_muG_of_zero {ε : Fin n → Bool} (hn : n = 0) :
    IsFiniteMeasure (Formalism.REAL.muG ε) := by
  subst n
  have : Subsingleton (Formalism.REAL.UJ ε) :=
    ⟨fun a b => Subtype.ext (Units.ext (Matrix.ext fun i => Fin.elim0 i))⟩
  have : CompactSpace (Formalism.REAL.UJ ε) := Finite.compactSpace
  infer_instance

private theorem memLp_of_weighted {ε : Fin n → Bool} {f : Formalism.REAL.UJ ε → ℂ}
    (hf : Continuous f) (C : ℝ) (hbound : ∀ g, ‖f g‖ ≤ C)
    (hweighted : MemLp (fun g =>
      (Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℂ) * f g)
      2 (Formalism.REAL.muG ε)) : MemLp f 2 (Formalism.REAL.muG ε) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have := finiteMeasure_muG_of_zero (ε := ε) hn
    exact MemLp.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hbound)
  · refine hweighted.of_le hf.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    have h1 : 1 ≤ Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) :=
      Real.one_le_sqrt.mpr (sigZeroDecay_one_le_hs (umat_mem_UJset ε g) ⟨0, hn⟩)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact le_mul_of_one_le_left (norm_nonneg _) h1

private theorem memLp_coefficients {G H : Type*} [Group G] [MeasurableSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {μ : Measure G} {ρ : G → (H →L[ℂ] H)}
    (hR : ∀ h : G, MeasurePreserving (fun g => g * h) μ μ)
    (hInv : MeasurePreserving (Inv.inv : G → G) μ μ)
    (hone : ρ 1 = 1) (hmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b))
    (hiso : ∀ g v, ‖ρ g v‖ = ‖v‖)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) →
      (∀ g, ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (y : H) (hy : y ≠ 0) (h0 : MemLp (fun g => inner ℂ y (ρ g y)) 2 μ) :
    ∀ v w : H, MemLp (fun g => inner ℂ w (ρ g v)) 2 μ := by
  intro v w
  by_cases hw : w = 0
  · simpa only [hw, inner_zero_left] using (MemLp.zero' : MemLp (fun _ : G => (0 : ℂ)) 2 μ)
  have hwy := GraphTrick.memLp_of_ne hR hone hmul hiso hirr y y hy h0 w
  have hInvCoeff : star ((fun g => inner ℂ y (ρ g w)) ∘ (Inv.inv : G → G)) =
      fun g => inner ℂ w (ρ g y) := by
    funext g
    have hs : star (ρ g⁻¹) = ρ g⁻¹⁻¹ := GraphTrick.star_eq hone hmul hiso g⁻¹
    simp only [Pi.star_apply, Function.comp_apply, RCLike.star_def, inner_conj_symm]
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint, hs, inv_inv]
  have hyw : MemLp (fun g => inner ℂ w (ρ g y)) 2 μ :=
    hInvCoeff ▸ (hwy.comp_measurePreserving hInv).star
  exact GraphTrick.memLp_of_ne hR hone hmul hiso hirr w y hy hyw v

theorem tf_sqInt_of_hW {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) :
    Formalism.MainNotions.S.IsSqIntOn ε (tfClRep σ (closGen E V)) := by
  have hU := tfClRep_isURepOn hgap hσ hD hV hc hVK
  have hst := closGen_stable hgap hσ hD hV hc hVK
  set ρ : Formalism.REAL.UJ ε → (closGen E V →L[ℂ] closGen E V) :=
    fun g => tfClRep σ (closGen E V) (Formalism.MainNotions.S.umat g) with hρ
  have hone : ρ 1 = 1 := by
    simp only [hρ]
    have e : Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε) = 1 := rfl
    rw [e]; exact hU.1.1
  have hmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b) := by
    intro a b
    simp only [hρ]
    have e : Formalism.MainNotions.S.umat (a * b) = Formalism.MainNotions.S.umat a * Formalism.MainNotions.S.umat b := rfl
    rw [e]; exact hU.1.2 _ (umat_mem_UJset ε a) _ (umat_mem_UJset ε b)
  have hiso : ∀ g v, ‖ρ g v‖ = ‖v‖ := fun g v => hU.2.1 _ (umat_mem_UJset ε g) v
  have hirr := Formalism.MainNotions.BridgeCSchur.irr_of (tfClRep_irred hgap hσ hD hV hc hVK)
  obtain ⟨y, hyV, hy0, -⟩ := hV.2.2.2
  have hyG : y ∈ genSub E V := rorth_le_genSub hyV
  let y0 : closGen E V := ⟨((y : D) : H), Submodule.le_topologicalClosure _ ⟨y, hyG, rfl⟩⟩
  have hy0 : y0 ≠ 0 := by
    intro h
    apply hy0
    have h2 : ((y : D) : H) = 0 := congrArg Subtype.val h
    exact Subtype.ext h2
  let f : Formalism.REAL.UJ ε → ℂ := fun g => inner ℂ (y : H) (σ (Formalism.MainNotions.S.umat g) (y : H))
  have hcont : Continuous f :=
    continuous_const.inner ((hσ.2.2 _).comp_continuous Formalism.MainNotions.BridgeCSchur.continuous_umat
      (fun g => umat_mem_UJset ε g))
  have hbound (g : Formalism.REAL.UJ ε) : ‖f g‖ ≤ ‖(y : H)‖ * ‖(y : H)‖ := by
    change ‖inner ℂ (y : H) (σ (Formalism.MainNotions.S.umat g) (y : H))‖ ≤ _
    calc
      _ ≤ ‖(y : H)‖ * ‖σ (Formalism.MainNotions.S.umat g) (y : H)‖ := norm_inner_le_norm _ _
      _ = _ := by rw [hσ.2.1 _ (umat_mem_UJset ε g)]
  have h0 : MemLp (fun g => inner ℂ y0 (ρ g y0)) 2 (Formalism.REAL.muG ε) := by
    have hcoe : (fun g => inner ℂ y0 (ρ g y0)) = f := by
      funext g
      change inner ℂ y0 (tfClRep σ (closGen E V) (Formalism.MainNotions.S.umat g) y0) =
        inner ℂ (y : H) (σ (Formalism.MainNotions.S.umat g) (y : H))
      rw [Submodule.coe_inner, tfClRep_coe σ _ (hst _ (umat_mem_UJset ε g))]
    rw [hcoe]
    exact memLp_of_weighted hcont _ hbound (hW y hyG y hyG)
  change ∀ v w : closGen E V, MemLp (fun g => inner ℂ w (ρ g v)) 2 (Formalism.REAL.muG ε)
  exact memLp_coefficients (ρ := ρ)
    (ReciprocityTheory.ChartRestriction.DS.measurePreserving_mul_right ε)
    (Measure.measurePreserving_inv (Formalism.REAL.muG ε)) hone hmul hiso hirr y0 hy0 h0

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

theorem tf_schur_transfer {n : ℕ} {ε : Fin n → Bool} {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [CompleteSpace H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}
    (S₁ : Submodule ℂ H₁) [S₁.HasOrthogonalProjection] (S₂ : Submodule ℂ H₂) (U : S₁ ≃ₗᵢ[ℂ] S₂)
    (hU : ∀ g ∈ UJset ε, ∀ x y : S₁, (x : H₁) = σ₁ g (y : H₁) → ((U x : S₂) : H₂) = σ₂ g ((U y : S₂) : H₂))
    (hS₁ : ∀ g ∈ UJset ε, ∀ x ∈ S₁, σ₁ g x ∈ S₁) {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) (tfClRep σ₁ S₁) d) :
    ∀ x ∈ S₂, ∀ v ∈ S₂, ∫ g : Formalism.REAL.UJ ε, ‖inner ℂ x (σ₂ (Formalism.MainNotions.S.umat g) v)‖ ^ 2 ∂(Formalism.REAL.muG ε) =
      ‖x‖ ^ 2 * ‖v‖ ^ 2 / d := by
  intro x hx v hv
  set x1 : S₁ := U.symm ⟨x, hx⟩ with hx1
  set v1 : S₁ := U.symm ⟨v, hv⟩ with hv1
  have ex : ((U x1 : S₂) : H₂) = x := by rw [hx1, LinearIsometryEquiv.apply_symm_apply]
  have ev : ((U v1 : S₂) : H₂) = v := by rw [hv1, LinearIsometryEquiv.apply_symm_apply]
  have hcoef : ∀ g : Formalism.REAL.UJ ε, inner ℂ x (σ₂ (Formalism.MainNotions.S.umat g) v) =
      Formalism.MainNotions.S.coefOn (tfClRep σ₁ S₁) v1 x1 g := by
    intro g
    have hg := umat_mem_UJset ε g
    set y : S₁ := ⟨σ₁ (Formalism.MainNotions.S.umat g) (v1 : H₁), hS₁ _ hg _ v1.2⟩ with hy
    have h1 := hU _ hg y v1 rfl
    rw [← ex, ← ev, ← h1, ← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]
    show inner ℂ x1 y = inner ℂ x1 (tfClRep σ₁ S₁ (Formalism.MainNotions.S.umat g) v1)
    congr 1
    exact Subtype.ext (tfClRep_coe σ₁ S₁ (hS₁ _ hg) v1).symm
  obtain ⟨-, hint, hval⟩ := hd.1, (hd.2 v1 x1 v1 x1).1, (hd.2 v1 x1 v1 x1).2
  have hnx : ‖x‖ = ‖x1‖ := by rw [← ex]; exact U.norm_map x1
  have hnv : ‖v‖ = ‖v1‖ := by rw [← ev]; exact U.norm_map v1
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have e : ∀ g : Formalism.REAL.UJ ε, ((‖inner ℂ x (σ₂ (Formalism.MainNotions.S.umat g) v)‖ ^ 2 : ℝ) : ℂ) =
      Formalism.MainNotions.S.coefOn (tfClRep σ₁ S₁) v1 x1 g * star (Formalism.MainNotions.S.coefOn (tfClRep σ₁ S₁) v1 x1 g) := by
    intro g
    rw [hcoef, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [e]
  have h1 : inner ℂ v1 v1 = ((‖v1‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have h2 : inner ℂ x1 x1 = ((‖x1‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [hval, h1, h2, hnx, hnv]
  push_cast
  ring

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

abbrev tfL2n (ε : Fin n → Bool) : Type := PiLp 2 (fun _ : Fin n => L2 ε)

def tfRdiag (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) : tfL2n ε →L[ℂ] tfL2n ε :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => L2 ε)).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.pi fun c => rreg ε g ∘L ContinuousLinearMap.proj c) ∘L
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => L2 ε)).toContinuousLinearMap

theorem tfRdiag_apply (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (v : tfL2n ε) (c : Fin n) :
    tfRdiag ε g v c = rreg ε g (v c) := rfl

theorem vectorL2_ext {ε : Fin n → Bool} {v w : tfL2n ε} (h : ∀ c, v c = w c) : v = w := by
  apply WithLp.ofLp_injective
  funext c
  exact h c

theorem tfRdiag_isURepOn (ε : Fin n → Bool) : IsURepOn (UJset ε) (tfRdiag ε) := by
  have hr := rreg_isURepOn ε
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · refine ContinuousLinearMap.ext fun v => vectorL2_ext fun c => ?_
    rw [tfRdiag_apply, hr.1.1]; rfl
  · intro a ha b hb
    refine ContinuousLinearMap.ext fun v => vectorL2_ext fun c => ?_
    rw [tfRdiag_apply, hr.1.2 a ha b hb, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      tfRdiag_apply, tfRdiag_apply]
  · intro g hg v
    have h1 := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => L2 ε) (tfRdiag ε g v)
    have h2 := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => L2 ε) v
    simp only [tfRdiag_apply, hr.2.1 g hg] at h1
    rw [← h2] at h1
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1
  · intro v
    have e : (fun g => tfRdiag ε g v) =
        fun g => (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => L2 ε)).symm (fun c => rreg ε g (v c)) := rfl
    rw [e]
    exact (PiLp.continuousLinearEquiv 2 ℂ _).symm.continuous.comp_continuousOn
      (continuousOn_pi.2 fun c => hr.2.2 _)

theorem tfRdiag_smooth {ε : Fin n → Bool} {v : tfL2n ε} (hv : ∀ c, v c ∈ smD ε (rreg ε)) :
    v ∈ smD ε (tfRdiag ε) := by
  rw [mem_smD_iff]
  have hc : ∀ c, S7.SmoothOnGV ε (fun g => rreg ε g (v c)) := fun c => (mem_smD_iff ε (rreg ε) _).1 (hv c)
  intro g₀ hg₀
  choose U F hU hg hF hEq using fun c => hc c g₀ hg₀
  refine ⟨⋂ c, U c, fun g => WithLp.toLp 2 (fun c => F c g), isOpen_iInter_of_finite hU,
    Set.mem_iInter.2 hg, ?_, ?_⟩
  · exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => L2 ε)).symm.contDiff.comp_contDiffOn
      (contDiffOn_pi.2 fun c => (hF c).mono (Set.iInter_subset _ c))
  · intro g hgU hgJ
    refine vectorL2_ext fun c => ?_
    exact hEq c g (Set.mem_iInter.1 hgU c) hgJ

theorem tfRdiag_hasDerivAt {ε : Fin n → Bool} {v : tfL2n ε} (hv : ∀ c, v c ∈ smD ε (rreg ε))
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    HasDerivAt (fun t : ℝ => tfRdiag ε (NormedSpace.exp ((t : ℂ) • X)) v)
      (WithLp.toLp 2 (fun c => dS (rreg ε) X (v c))) 0 := by
  have hd : ∀ c, HasDerivAt (fun t : ℝ => rreg ε (NormedSpace.exp ((t : ℂ) • X)) (v c))
      (dS (rreg ε) X (v c)) 0 := by
    intro c
    have h := (isDerivedOn_smE (rreg_isURepOn ε)).deriv X hX ⟨v c, hv c⟩
    rw [dS_eq_actM (isDerivedOn_smE (rreg_isURepOn ε)) hX ⟨v c, hv c⟩]
    exact h
  have hp : HasDerivAt (fun t : ℝ => fun c => rreg ε (NormedSpace.exp ((t : ℂ) • X)) (v c))
      (fun c => dS (rreg ε) X (v c)) 0 := hasDerivAt_pi.2 hd
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => L2 ε)).symm.hasFDerivAt.comp_hasDerivAt 0 hp

theorem tfRdiag_dS {ε : Fin n → Bool} {v : tfL2n ε} (hv : ∀ c, v c ∈ smD ε (rreg ε))
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (c : Fin n) :
    dS (tfRdiag ε) X v c = dS (rreg ε) X (v c) := by
  have h := (tfRdiag_hasDerivAt hv hX).deriv
  have h2 := congrArg (fun w : tfL2n ε => w c) h
  exact h2

theorem tfRdiag_smE {ε : Fin n → Bool} {v : tfL2n ε} (hv : ∀ c, v c ∈ smD ε (rreg ε)) (a b c : Fin n) :
    ((smE ε (tfRdiag ε) a b ⟨v, tfRdiag_smooth hv⟩ : smD ε (tfRdiag ε)) : tfL2n ε) c =
      ((smE ε (rreg ε) a b ⟨v c, hv c⟩ : smD ε (rreg ε)) : L2 ε) := by
  rw [smE_apply (tfRdiag_isURepOn ε), smE_apply (rreg_isURepOn ε)]
  simp only [PiLp.add_apply, PiLp.smul_apply]
  rw [tfRdiag_dS hv (SmDerA.inG_cpart1 ε _), tfRdiag_dS hv (SmDerA.inG_cpart2 ε _)]

def tfJ (ε : Fin n → Bool) : tfL2n ε →L[ℂ] tfL2n ε :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => L2 ε)).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.pi fun c => tfSgn ε c • ContinuousLinearMap.proj c) ∘L
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => L2 ε)).toContinuousLinearMap

theorem tfJ_apply (ε : Fin n → Bool) (v : tfL2n ε) (c : Fin n) : tfJ ε v c = tfSgn ε c • v c := rfl

theorem tfRdiag_tfJ (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (v : tfL2n ε) :
    tfRdiag ε g (tfJ ε v) = tfJ ε (tfRdiag ε g v) :=
  vectorL2_ext fun c => by rw [tfRdiag_apply, tfJ_apply, tfJ_apply, tfRdiag_apply, map_smul]

theorem toL2_congr_of_eq_on_UJset {ε : Fin n → Bool} {F F' : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ g ∈ UJset ε, F g = F' g) : toL2 ε F = toL2 ε F' := by
  have e : (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) = fun g => F' (Formalism.MainNotions.S.umat g) :=
    funext fun g => h _ (umat_mem_UJset ε g)
  unfold toL2
  simp only [e]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (e ▸ h1) h2
  · exact absurd (e.symm ▸ h2) h1
  · rfl

section Ph

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def tfPh (dual : Bool) (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (y : H)
    (ζ : Fin n → H) : tfL2n ε :=
  WithLp.toLp 2 (fun c => toL2 ε (coefMap dual σ (Pi.single c (tfSgn ε c • y)) ζ))

theorem tfPh_apply (dual : Bool) (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (y : H)
    (ζ : Fin n → H) (c : Fin n) :
    tfPh dual ε σ y ζ c = toL2 ε (coefMap dual σ (Pi.single c (tfSgn ε c • y)) ζ) := rfl

end Ph

end ReciprocityTheory.ChartRestriction.DS
end
end
