module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle005
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
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeG
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

namespace ModelFibreSumAlmostEverywhere

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}
  (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

theorem lift_mem (x : M.Xc) : modelLift M x x ∈ mcPts P :=
  ((modelLift_spec M x).1 x (mem_modelU M x)).1

theorem proj_lift (x : M.Xc) : M.proj (modelLift M x x) = x :=
  ((modelLift_spec M x).1 x (mem_modelU M x)).2

theorem lift_compat {x z : M.Xc} (hz : z ∈ modelU M x) :
    ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ modelLift M z z = fun p => c p.1 * modelLift M x z p := by
  have h1 := (modelLift_spec M x).1 z hz
  obtain ⟨c, hc, h⟩ := (M.fibre _ h1.1 _ (lift_mem M z)).mp (h1.2.trans (proj_lift M z).symm)
  exact ⟨c, hc, h⟩

theorem proj_eq_of_segre {x : M.Xc} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) (μ : ℂ) (hμ : μ ≠ 0)
    (h : segre z = μ • segre (modelLift M x x)) : M.proj z = x := by
  obtain ⟨c, hc, hzc⟩ := sameOrbit_of_segre (lift_mem M x).1 μ hμ h
  have := (M.fibre _ (lift_mem M x) _ hz).mpr ⟨c, hc, hzc⟩
  rw [← this, proj_lift]

theorem modelQ_eq_local {x z : M.Xc} (hz : z ∈ modelU M x) :
    modelQ M Ψ z = fun i => Ψ (segre (modelLift M x z)) i.succ / Ψ (segre (modelLift M x z)) 0 := by
  obtain ⟨c, hc, hzc⟩ := lift_compat M hz
  have hpc : ∏ k, c k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  funext i
  simp only [modelQ, hzc, segre_smul, map_smul, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hpc

theorem analyticAt_lift_chart (x : M.Xc) (j : Fin M.atlas.n) {u : Fin e → ℂ}
    (hu : u ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelU M x) :
    AnalyticAt ℂ (fun v => modelLift M x ((M.atlas.chart j).symm v)) u :=
  analyticAt_pi_iff.mpr fun p => (modelLift_spec M x).2 p j u hu

theorem analyticAt_segre_lift (x : M.Xc) (j : Fin M.atlas.n) {u : Fin e → ℂ}
    (hu : u ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelU M x) :
    AnalyticAt ℂ (fun v => Ψ (segre (modelLift M x ((M.atlas.chart j).symm v)))) u := by
  classical
  have hl := analyticAt_lift_chart M x j hu
  have hs : AnalyticAt ℂ (fun v => segre (modelLift M x ((M.atlas.chart j).symm v))) u := by
    refine analyticAt_pi_iff.mpr fun i => ?_
    simp only [segre]
    exact Finset.analyticAt_fun_prod _ fun k _ => analyticAt_pi_iff.mp hl _
  exact (LinearMap.toContinuousLinearMap Ψ).analyticAt _ |>.comp hs

theorem analyticAt_modelQ (x : M.Xc) (j : Fin M.atlas.n) (hj : x ∈ (M.atlas.chart j).source)
    (h0 : Ψ (segre (modelLift M x x)) 0 ≠ 0) :
    AnalyticAt ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) (M.atlas.chart j x) := by
  set u := M.atlas.chart j x
  have hsu : (M.atlas.chart j).symm u = x := (M.atlas.chart j).left_inv hj
  have hu : u ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelU M x :=
    ⟨(M.atlas.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact mem_modelU M x⟩
  have hH := analyticAt_segre_lift M Ψ x j hu
  have hH0 : AnalyticAt ℂ (fun v => Ψ (segre (modelLift M x ((M.atlas.chart j).symm v))) 0) u :=
    analyticAt_pi_iff.mp hH 0
  have hne : Ψ (segre (modelLift M x ((M.atlas.chart j).symm u))) 0 ≠ 0 := by rw [hsu]; exact h0
  have hF : AnalyticAt ℂ (fun v => fun i : Fin e =>
      Ψ (segre (modelLift M x ((M.atlas.chart j).symm v))) i.succ /
        Ψ (segre (modelLift M x ((M.atlas.chart j).symm v))) 0) u :=
    analyticAt_pi_iff.mpr fun i => (analyticAt_pi_iff.mp hH i.succ).div hH0 hne
  refine hF.congr ?_
  filter_upwards [((M.atlas.chart j).isOpen_inter_preimage_symm (modelU_isOpen M x)).mem_nhds hu,
    hH0.continuousAt.eventually_ne hne] with v hv hv0
  exact (modelQ_eq_local M Ψ hv.2).symm

theorem psi_zero_ne_of_not_mem_bad {E : Set M.Xc} {x : M.Xc} (hx : x ∉ modelBad M Ψ E) :
    Ψ (segre (modelLift M x x)) 0 ≠ 0 :=
  fun h => hx (Or.inr (Or.inl h))

theorem notMem_of_notMem_bad {E : Set M.Xc} {x : M.Xc} (hx : x ∉ modelBad M Ψ E) : x ∉ E :=
  fun h => hx (Or.inl h)

def modelW (x : M.Xc) : ((k : K) → ι k) → ℂ :=
  (Ψ (segre (modelLift M x x)) 0)⁻¹ • segre (modelLift M x x)

theorem modelW_mem_fibre (hK : Nonempty K) (hPh : IsMultiHomogIdeal P) {x : M.Xc}
    (h0 : Ψ (segre (modelLift M x x)) 0 ≠ 0) : modelW M Ψ x ∈ fibre P Ψ (modelQ M Ψ x) := by
  classical
  obtain ⟨k0⟩ := hK
  let c : K → ℂ := Function.update (fun _ => (1 : ℂ)) k0 (Ψ (segre (modelLift M x x)) 0)⁻¹
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp [c, h0]
    · simp [c, Function.update_of_ne hk]
  have hpc : ∏ k, c k = (Ψ (segre (modelLift M x x)) 0)⁻¹ := by
    simp [c, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  refine ⟨fun p => c p.1 * modelLift M x x p, mcPts_smul hPh c hc (lift_mem M x), ?_, ?_⟩
  · rw [segre_smul, hpc]; rfl
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [modelW, h0]
    · simp only [modelW, map_smul, Pi.smul_apply, smul_eq_mul, Fin.cons_succ, modelQ]
      rw [div_eq_inv_mul]

theorem modelW_injOn : Set.InjOn (modelW M Ψ) {x | Ψ (segre (modelLift M x x)) 0 ≠ 0} := by
  intro x hx x' hx' hw
  have h := congrArg (fun v => Ψ (segre (modelLift M x x)) 0 • v) hw
  simp only [modelW, smul_smul, mul_inv_cancel₀ (show Ψ (segre (modelLift M x x)) 0 ≠ 0 from hx),
    one_smul] at h
  have := proj_eq_of_segre M (lift_mem M x)
    (Ψ (segre (modelLift M x x)) 0 * (Ψ (segre (modelLift M x' x')) 0)⁻¹)
    (by simp [show Ψ (segre (modelLift M x x)) 0 ≠ 0 from hx,
      show Ψ (segre (modelLift M x' x')) 0 ≠ 0 from hx']) h
  rw [proj_lift] at this
  exact this

theorem mem_fibre_data {y : Fin e → ℂ} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P)
    (hΨz : Ψ (segre z) = Fin.cons 1 y) :
    Ψ (segre (modelLift M (M.proj z) (M.proj z))) 0 ≠ 0 ∧ modelQ M Ψ (M.proj z) = y ∧
      modelW M Ψ (M.proj z) = segre z := by
  obtain ⟨c, hc, hxc⟩ := (M.fibre _ hz _ (lift_mem M (M.proj z))).mp (proj_lift M _).symm
  have hseg : segre (modelLift M (M.proj z) (M.proj z)) = (∏ k, c k) • segre z := by
    rw [hxc]; exact segre_smul c z
  have hpc : ∏ k, c k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hΨx : Ψ (segre (modelLift M (M.proj z) (M.proj z))) = (∏ k, c k) • Fin.cons 1 y := by
    rw [hseg, map_smul, hΨz]
  have h0 : Ψ (segre (modelLift M (M.proj z) (M.proj z))) 0 = ∏ k, c k := by simp [hΨx]
  refine ⟨by rw [h0]; exact hpc, ?_, ?_⟩
  · funext i
    simp only [modelQ, hΨx, h0, Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
    field_simp
  · rw [modelW, h0, hseg, smul_smul, inv_mul_cancel₀ hpc, one_smul]

theorem image_bad_null {E : Set M.Xc}
    (hE : ∀ j, volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' E) = 0) :
    volume (modelQ M Ψ '' (modelBad M Ψ E ∩ {x | Ψ (segre (modelLift M x x)) 0 ≠ 0})) = 0 := by
  set A := M.atlas
  set G : Set M.Xc := {x | Ψ (segre (modelLift M x x)) 0 ≠ 0}
  set D : Fin A.n → Set (Fin e → ℂ) := fun j => {u | u ∈ (A.chart j).target ∧
    (A.chart j).symm u ∈ G ∧ ¬ (AnalyticAt ℂ (modelQ M Ψ ∘ (A.chart j).symm) u ∧
      LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (A.chart j).symm) u :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)}
  have han : ∀ j, ∀ u ∈ (A.chart j).target, (A.chart j).symm u ∈ G →
      AnalyticAt ℂ (modelQ M Ψ ∘ (A.chart j).symm) u := by
    intro j u hu hG
    have := analyticAt_modelQ M Ψ _ j ((A.chart j).map_target hu) hG
    rwa [(A.chart j).right_inv hu] at this
  have hsub : modelQ M Ψ '' (modelBad M Ψ E ∩ G) ⊆
      (⋃ j, (modelQ M Ψ ∘ (A.chart j).symm) ''
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (E ∩ G))) ∪
      ⋃ j, (modelQ M Ψ ∘ (A.chart j).symm) '' D j := by
    rintro _ ⟨x, ⟨hxb, hxG⟩, rfl⟩
    rcases hxb with hxE | hxc
    · obtain ⟨j, hj⟩ := A.cover x
      refine Or.inl (Set.mem_iUnion.mpr ⟨j, A.chart j x, ⟨(A.chart j).map_source hj, ?_⟩, ?_⟩)
      · rw [Set.mem_preimage, (A.chart j).left_inv hj]; exact ⟨hxE, hxG⟩
      · simp [(A.chart j).left_inv hj]
    · rcases hxc with h0 | ⟨j, hj, hbad⟩
      · exact absurd h0 hxG
      · refine Or.inr (Set.mem_iUnion.mpr ⟨j, A.chart j x, ⟨(A.chart j).map_source hj, ?_, hbad⟩, ?_⟩)
        · show (A.chart j).symm (A.chart j x) ∈ G
          rw [(A.chart j).left_inv hj]; exact hxG
        · simp [(A.chart j).left_inv hj]
  refine measure_mono_null hsub (measure_union_null (measure_iUnion_null fun j => ?_)
    (measure_iUnion_null fun j => ?_))
  · refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
      (measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_left))
        (hE j))
    intro u hu
    exact ((han j u hu.1 hu.2.2).differentiableAt.restrictScalars ℝ).differentiableWithinAt
  · refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun u => (fderiv ℂ (modelQ M Ψ ∘ (A.chart j).symm) u).restrictScalars ℝ) ?_ ?_
    · intro u hu
      exact ((han j u hu.1 hu.2.1).differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    · intro u hu
      have h0 : LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (A.chart j).symm) u :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0 := by
        by_contra h
        exact hu.2.2 ⟨han j u hu.1 hu.2.1, h⟩
      have := abs_det_restrictScalars (fderiv ℂ (modelQ M Ψ ∘ (A.chart j).symm) u)
      rw [h0, norm_zero, zero_pow two_ne_zero, abs_eq_zero] at this
      exact this

end ModelFibreSumAlmostEverywhere

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem HodgeFlagNeZero.proof : HodgeFlagNeZero.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl H B τ i
  classical

  let BE : Module.Basis (Fin D.N) Ω (E τ) := Module.Basis.mk (B.e_indep τ) (B.e_span τ).ge
  let w : ⋀[Ω]^((i : ℕ) + 1) (E τ) := exteriorPower.ιMulti Ω _ (B.e τ ∘ Fin.castLE (step_le i))
  have hw : w ≠ 0 := by
    have h := (BE.exteriorPower ((i : ℕ) + 1)).ne_zero
      (Set.powersetCard.ofFinEmbEquiv (Fin.castLEOrderEmb (step_le i)))
    rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, Equiv.symm_apply_apply] at h
    convert h using 2
    funext x
    simp [BE, Fin.castLEOrderEmb]

  choose cX hcX using D.arith.2.1.2.2
  have hy : ∀ k, D.y ⟨k, cX k⟩ ≠ 0 := by
    intro k h0
    apply hcX k
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]
  have hseg : segreCoord D.y cX ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy k
  obtain ⟨M, f, cc, -, -, hsum, hPr⟩ := Pl.generates τ i cX hseg
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h
      simp at hsum
    · exact h
  obtain ⟨b, -, hbspan, hA⟩ := hPr ⟨0, hM⟩
  have : Module.Finite Ω (E τ) := Module.Finite.of_basis BE
  have hbi : LinearIndependent Ω b :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hbspan.ge
      (by rw [Module.finrank_eq_card_basis BE])
  let Bw := (Module.Basis.mk hbi hbspan.ge).exteriorPower ((i : ℕ) + 1)

  have hm : ∃ m, Pl.gen τ i m w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hw
    refine Bw.forall_coord_eq_zero_iff.1 fun t => ?_
    obtain ⟨a, -, ha⟩ := hA _ (Set.powersetCard.ofFinEmbEquiv.symm t).strictMono
    let ψ : Module.Dual Ω (⋀[Ω]^((i : ℕ) + 1) (E τ)) :=
      ∑ m, (a m * chartMono D.y cX (-Pl.bdeg τ i)) • Pl.gen τ i m
    have hψ : ψ = Bw.coord t := by
      refine Bw.ext fun u => ?_
      have h1 := ha _ (Set.powersetCard.ofFinEmbEquiv.symm u).strictMono
      rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      simp only [Bw, exteriorPower.basis_apply, exteriorPower.ιMulti_family, ψ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Module.Basis.coe_mk]
      calc ∑ m, a m * chartMono D.y cX (-Pl.bdeg τ i) * Pl.gen τ i m (exteriorPower.ιMulti Ω _
              (b ∘ Set.powersetCard.ofFinEmbEquiv.symm u))
          = ∑ m, a m * (Pl.gen τ i m (exteriorPower.ιMulti Ω _
              (b ∘ Set.powersetCard.ofFinEmbEquiv.symm u)) * chartMono D.y cX (-Pl.bdeg τ i)) :=
            Finset.sum_congr rfl fun m _ => by ring
        _ = _ := h1
        _ = _ := by
          by_cases htu : t = u
          · subst htu
            simp
          · rw [if_neg fun h' =>
              htu (Set.powersetCard.ofFinEmbEquiv.symm.injective (DFunLike.coe_injective h')).symm]
            simp [Ne.symm htu]
    rw [← hψ]
    simp [ψ, hcon]
  obtain ⟨m0, hm0⟩ := hm

  refine ⟨m0, ?_⟩
  let c0 : Fin ((i : ℕ) + 1) → Fin D.N := Fin.castLE (step_le i)
  let v : (Fin ((i : ℕ) + 1) → Fin D.N) → Fin ((i : ℕ) + 1) → Ψ × Fin D.N × Fin D.N :=
    fun c a => (τ, headIdx (step_le i) a, c a)
  let μ : (Fin ((i : ℕ) + 1) → Fin D.N) → (Ψ × Fin D.N × Fin D.N) →₀ ℕ :=
    fun c => ∑ a, Finsupp.single (v c a) 1
  let g : (Fin ((i : ℕ) + 1) → Fin D.N) → Ω :=
    fun c => Pl.gen τ i m0 (exteriorPower.ιMulti Ω _ (B.e τ ∘ c))
  let z : (Fin ((i : ℕ) + 1) → Fin D.N) → Ω := fun c =>
    ∏ a, if ((headIdx (step_le i) a : ℕ) < D.j ∧ D.j ≤ (c a : ℕ)) then 0 else 1
  let P : MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω := ∑ c, monomial (μ c) (z c * g c)
  have hP : Pl.pluecker0 B τ i m0 = algebraMap _ Pl.ΩY P := by

    simp only [PlueckerData.pluecker0, PlueckerData.gvar0, PlueckerData.gvar, PlueckerData.ofΩ, P, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hfac : ∀ a, (if ((headIdx (step_le i) a : ℕ) < D.j ∧ D.j ≤ (c a : ℕ)) then (0 : Pl.ΩY)
        else algebraMap (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY (X (τ, headIdx (step_le i) a, c a))) =
        algebraMap (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY
          (C (if ((headIdx (step_le i) a : ℕ) < D.j ∧ D.j ≤ (c a : ℕ)) then 0 else 1) *
            X (τ, headIdx (step_le i) a, c a)) := by
      intro a
      split_ifs <;> simp
    rw [Finset.prod_congr rfl fun a _ => hfac a, ← map_prod, ← map_mul]
    congr 1
    rw [show monomial (μ c) (z c * g c) = C (z c * g c) * monomial (μ c) 1 by rw [C_mul_monomial, mul_one],
      monomial_sum_one, Finset.prod_mul_distrib]
    simp only [z, g, map_mul, map_prod, v, MvPolynomial.X]
    ring
  have hμ : ∀ c, μ c = μ c0 → c = c0 := by
    intro c h
    funext a
    have h2 := congrArg (fun φ : (Ψ × Fin D.N × Fin D.N) →₀ ℕ => φ (τ, headIdx (step_le i) a, c0 a)) h
    simp only [μ, v, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, Prod.mk.injEq,
      true_and, headIdx, Fin.castLE_inj] at h2
    rw [Finset.sum_eq_single a (fun a' _ h' => if_neg fun h'' => h' h''.1) (by simp),
      Finset.sum_eq_single a (fun a' _ h' => if_neg fun h'' => h' h''.1) (by simp)] at h2
    by_contra hne
    simp [hne] at h2
  have hz : z c0 = 1 :=
    Finset.prod_eq_one fun a _ => if_neg fun h => lt_irrefl _ (h.1.trans_le h.2)
  have hcoeff : AddMonoidAlgebra.coeff P (μ c0) = g c0 := by
    simp only [P, coeff_sum, coeff_monomial]
    rw [Finset.sum_eq_single c0 (fun c _ hc => if_neg fun h => hc (hμ c h)) (by simp), if_pos rfl, hz, one_mul]
  have hPne : P ≠ 0 := fun h => hm0 (by simpa [h, g, c0, w] using hcoeff.symm)
  rw [hP]
  exact fun h => hPne (IsFractionRing.injective (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY
    (by rw [h, map_zero]))

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem holoOn_comp_compatChart_symm {d : ℕ} {X : Type} [TopologicalSpace X]
    {A : ReciprocityTheory.AnForm.M.FinHolAtlas d X} {e : OpenPartialHomeomorph X (Fin d → ℂ)}
    (he : ReciprocityTheory.AnForm.M.IsCompatChart A e) {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g)
    {u : Fin d → ℂ} (hu : u ∈ e.target) (huU : e.symm u ∈ U) :
    DifferentiableAt ℂ (g ∘ e.symm) u := by
  obtain ⟨j, hj⟩ := A.cover (e.symm u)
  have h1 : AnalyticAt ℂ (A.chart j ∘ e.symm) u := (he j).2 u ⟨hu, hj⟩
  have h2 : AnalyticAt ℂ (g ∘ (A.chart j).symm) ((A.chart j ∘ e.symm) u) := by
    refine hg j _ ⟨(A.chart j).map_source hj, ?_⟩
    show (A.chart j).symm (A.chart j (e.symm u)) ∈ U
    rw [(A.chart j).left_inv hj]
    exact huU
  have h3 : g ∘ e.symm =ᶠ[𝓝 u] (g ∘ (A.chart j).symm) ∘ (A.chart j ∘ e.symm) := by
    have : ∀ᶠ u' in 𝓝 u, e.symm u' ∈ (A.chart j).source :=
      (e.continuousAt_symm hu).preimage_mem_nhds ((A.chart j).open_source.mem_nhds hj)
    filter_upwards [this] with u' hu'
    simp only [Function.comp, (A.chart j).left_inv hu']
  exact (h2.comp h1).differentiableAt.congr_of_eventuallyEq h3

theorem ProjHoloLocal.proof (hL : LocalOrbitChart.Statement)
    (hO : IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse.Statement) : ProjHoloLocal.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D M e he z hz hze

  obtain ⟨N, hNo, hzN, κ, hκ, hκt, hκs⟩ := hL K ι Ω D.y D.n D.arith D.smoothGeneric z hz

  obtain ⟨U, hUo, hxU, s, hs, hsh⟩ := M.sections (M.proj z)
  obtain ⟨c, hc, hcz⟩ := (M.fibre z hz _ (hs _ hxU).1).1 (hs _ hxU).2.symm
  have hsxN : s (M.proj z) ∈ N := by rw [hcz]; exact (hκt z hzN c hc).1
  have hκsx : κ (s (M.proj z)) = κ z := by rw [hcz]; exact (hκt z hzN c hc).2
  have hsd : ∀ u ∈ e.target, e.symm u ∈ U → DifferentiableAt ℂ (s ∘ e.symm) u := fun u hu huU =>
    differentiableAt_pi.2 fun p => holoOn_comp_compatChart_symm he (hsh p) hu huU

  have hex : e (M.proj z) ∈ e.target := e.map_source hze
  have hexU : e.symm (e (M.proj z)) ∈ U := by rw [e.left_inv hze]; exact hxU
  have hTn : e.target ∩ e.symm ⁻¹' U ∩ (s ∘ e.symm) ⁻¹' N ∈ 𝓝 (e (M.proj z)) := by
    refine Filter.inter_mem (Filter.inter_mem (e.open_target.mem_nhds hex) ?_) ?_
    · exact (e.continuousAt_symm hex).preimage_mem_nhds (hUo.mem_nhds hexU)
    · refine (hsd _ hex hexU).continuousAt.preimage_mem_nhds (hNo.mem_nhds ?_)
      show s (e.symm (e (M.proj z))) ∈ N
      rw [e.left_inv hze]
      exact hsxN
  obtain ⟨T, hTsub, hTo, hxT⟩ := mem_nhds_iff.1 hTn
  have hψd : DifferentiableOn ℂ (κ ∘ s ∘ e.symm) T := fun u hu =>
    ((hκ _ (hTsub hu).2).differentiableAt.comp u
      (hsd u (hTsub hu).1.1 (hTsub hu).1.2)).differentiableWithinAt
  have hψi : Set.InjOn (κ ∘ s ∘ e.symm) T := by
    intro u hu u' hu' h
    have h1 := hs _ (hTsub hu).1.2
    have h2 := hs _ (hTsub hu').1.2
    obtain ⟨c', hc', hcc⟩ := hκs _ ⟨(hTsub hu).2, h1.1⟩ _ ⟨(hTsub hu').2, h2.1⟩ h
    have hp : M.proj (s (e.symm u)) = M.proj (s (e.symm u')) :=
      (M.fibre _ h1.1 _ h2.1).2 ⟨c', hc', hcc⟩
    rw [h1.2, h2.2] at hp
    exact e.symm.injOn (hTsub hu).1.1 (hTsub hu').1.1 hp

  obtain ⟨hψo, g, hg, hgψ⟩ := hO D.n T (κ ∘ s ∘ e.symm) hTo hψd hψi

  obtain ⟨O, hOo, hOeq⟩ :=
    continuousOn_iff'.1 M.cont (e.source ∩ e ⁻¹' T) (e.isOpen_inter_preimage hTo)
  refine ⟨O ∩ (N ∩ κ ⁻¹' ((κ ∘ s ∘ e.symm) '' T)),
    hOo.inter (hκ.continuousOn.isOpen_inter_preimage hNo hψo), ?_, g ∘ κ, ?_, ?_⟩
  · refine ⟨?_, hzN, e (M.proj z), hxT, ?_⟩
    · have hz' : z ∈ M.proj ⁻¹' (e.source ∩ e ⁻¹' T) ∩ mcPts (mCoordIdeal D.y) := ⟨⟨hze, hxT⟩, hz⟩
      rw [hOeq] at hz'
      exact hz'.1
    · show κ (s (e.symm (e (M.proj z)))) = κ z
      rw [e.left_inv hze]
      exact hκsx
  · intro w hw
    exact ((hg.differentiableAt (hψo.mem_nhds hw.2.2)).comp w
      (hκ w hw.2.1).differentiableAt).differentiableWithinAt
  · rintro z' ⟨⟨hz'O, hz'N, -⟩, hz'⟩
    have hp : z' ∈ M.proj ⁻¹' (e.source ∩ e ⁻¹' T) ∩ mcPts (mCoordIdeal D.y) := by
      rw [hOeq]
      exact ⟨hz'O, hz'⟩
    obtain ⟨⟨hpe, hpT⟩, -⟩ := hp
    refine ⟨hpe, ?_⟩
    have hpU : M.proj z' ∈ U := by
      have h := (hTsub hpT).1.2
      rwa [Set.mem_preimage, e.left_inv hpe] at h
    obtain ⟨c', hc', hcc⟩ := (M.fibre z' hz' _ (hs _ hpU).1).1 (hs _ hpU).2.symm
    have hκ' : κ (s (M.proj z')) = κ z' := by rw [hcc]; exact (hκt z' hz'N c' hc').2
    have hψz : (κ ∘ s ∘ e.symm) (e (M.proj z')) = κ z' := by
      show κ (s (e.symm (e (M.proj z')))) = κ z'
      rw [e.left_inv hpe]
      exact hκ'
    show e (M.proj z') = g (κ z')
    rw [← hψz, hgψ _ hpT]

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
