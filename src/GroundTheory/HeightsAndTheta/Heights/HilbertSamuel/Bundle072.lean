module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle062
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PTorusInvLevi
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle063
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle064
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenOnFibres
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLevi
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 Filter Topology
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi (sqSum)
open GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi (levi_Phi leviForm_phi_nonneg isOpen_noZeroBlock blk)

namespace ScaledFSHProps

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isSmoothHerm : IsSmoothHerm (scaledFSH ι) :=
  (GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs (ι := ι) 1).mul
    (contDiffOn_const (c := Real.exp (-(-1 : ℝ))))

theorem log_h_eventuallyEq {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    (fun y => Real.log ((scaledFSH ι).h y)) =ᶠ[𝓝 z]
      fun y => (∑ k, Real.log ((fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩))) + 1 := by
  filter_upwards [isOpen_noZeroBlock.mem_nhds hz] with y hy
  have hρ : ∀ k, (fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩) ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hy k
    exact ((fsMetric (ι := ι k)).pos _ fun h0 => hi (congrFun h0 i)).ne'
  rw [scaledFSH_h, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => hρ k) (Real.exp_pos 1).ne',
    Real.log_exp, Real.log_prod fun k _ => hρ k]

theorem leviForm_log_h_nonneg {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (w : (Σ k, ι k) → ℂ) :
    0 ≤ leviForm (fun y => Real.log ((scaledFSH ι).h y)) z w := by
  have hd : fderiv ℝ (fun y => Real.log ((scaledFSH ι).h y)) =ᶠ[𝓝 z]
      fderiv ℝ (fun y => ∑ k, Real.log ((fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩))) := by
    filter_upwards [(log_h_eventuallyEq hz).fderiv (𝕜 := ℝ)] with y hy
    rw [hy]
    exact fderiv_add_const (1 : ℝ)
  have hL : leviForm (fun y => Real.log ((scaledFSH ι).h y)) z w =
      leviForm (fun y => ∑ k, Real.log ((fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩))) z w := by
    unfold leviForm
    rw [hd.fderiv_eq]
  rw [hL, levi_Phi hz w]
  refine Finset.sum_nonneg fun k _ => leviForm_phi_nonneg ?_ _
  obtain ⟨i, hi⟩ := hz k
  refine (lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hi) 2) ?_).ne'
  exact Finset.single_le_sum (f := fun j => ‖blk k z j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

theorem isSemipositiveRel (P0 P : Ideal (MRing ι)) : IsSemipositiveRel P0 P (scaledFSH ι) :=
  ⟨isSmoothHerm, fun _ hz w _ => leviForm_log_h_nonneg hz.1 w⟩

theorem isConjInvariantH : IsConjInvariantH (scaledFSH ι) := by
  intro z
  rw [scaledFSH_h, scaledFSH_h]
  simp [fsMetric, EuclideanSpace.norm_eq]

theorem norm_le_rho (z : (Σ k, ι k) → ℂ) (k : K) (i : ι k) :
    ‖z ⟨k, i⟩‖ ≤ (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩) := by
  show ‖z ⟨k, i⟩‖ ≤ ‖WithLp.toLp 2 (fun i => z ⟨k, i⟩)‖
  simpa using PiLp.norm_apply_le (WithLp.toLp 2 (fun i => z ⟨k, i⟩)) i

theorem monomialsBounded (P : Ideal (MRing ι)) : MonomialsBounded P (scaledFSH ι) (fun _ => 1) := by
  intro z _ μ hμ
  rw [scaledFSH_h, norm_prod, Fintype.prod_sigma]
  have hρ : ∀ k, 0 ≤ (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩) := fun k => norm_nonneg _
  have hblk : ∀ k, ∏ i, ‖z ⟨k, i⟩ ^ μ ⟨k, i⟩‖ ≤ (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩) := by
    intro k
    calc ∏ i, ‖z ⟨k, i⟩ ^ μ ⟨k, i⟩‖ ≤ ∏ i, (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩) ^ μ ⟨k, i⟩ := by
          refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_rho z k i) _
      _ = (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩) := by
          rw [Finset.prod_pow_eq_pow_sum, hμ k]
          exact pow_one _
  calc ∏ k, ∏ i, ‖z ⟨k, i⟩ ^ μ ⟨k, i⟩‖ ≤ ∏ k, (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩) :=
        Finset.prod_le_prod₀ (fun k _ => Finset.prod_nonneg fun i _ => norm_nonneg _) fun k _ => hblk k
    _ ≤ (∏ k, (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩)) * Real.exp 1 :=
        le_mul_of_one_le_right (Finset.prod_nonneg fun k _ => hρ k) (Real.one_le_exp zero_le_one)

end ScaledFSHProps

theorem ScaledFSHProps.proof : ScaledFSHProps.Statement := fun _ _ _ _ P P0 =>
  ⟨ScaledFSHProps.isSemipositiveRel P0 P, ScaledFSHProps.isConjInvariantH, ScaledFSHProps.monomialsBounded P⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

theorem BlockGraphImage.proof : BlockGraphImage.Statement := by
  intro K _ ι _ Ω _ _ κ _ y k₀ M N x hB

  let φ : MRing ι ⧸ mCoordIdeal y →+* MvPolynomial K Ω :=
    Ideal.Quotient.lift (mCoordIdeal y) (mConeMap y).toRingHom fun a ha => RingHom.mem_ker.1 ha
  have hφ : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun a ha => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact Ideal.Quotient.eq_zero_iff_mem.2 (RingHom.mem_ker.2 ha)

  let ψ : Polynomial Ω →+* MvPolynomial Unit (MvPolynomial K Ω) :=
    Polynomial.eval₂RingHom ((C : MvPolynomial K Ω →+* _).comp C) (C (X k₀) * X ())
  let ev : MvPolynomial Unit (MvPolynomial K Ω) →+* Polynomial Ω :=
    eval₂Hom (Polynomial.C.comp (MvPolynomial.eval fun _ => (1 : Ω))) fun _ => Polynomial.X
  have hev : ∀ p, ev (ψ p) = p := by
    have h : ev.comp ψ = RingHom.id _ := by
      apply Polynomial.ringHom_ext
      · intro c
        simp [ψ, ev]
      · simp [ψ, ev]
    exact fun p => RingHom.congr_fun h p

  have hcone : ∀ q, mConeMap y (blockForms k₀ M q) = C (x q) * X k₀ := by
    intro q

    simp only [blockForms, map_sum, map_mul, mConeMap, aeval_X, aeval_C, hB.1 q, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_assoc]
  let G : MRing (GlobalTheory κ) →+* MvPolynomial Unit (MvPolynomial K Ω) :=
    (MvPolynomial.map φ).comp ((graphMap (mCoordIdeal y) (blockForms k₀ M)).comp
      (rename (inrV (ι := ι) (ι₂ := GlobalTheory κ)) : MRing (GlobalTheory κ) →ₐ[ℤ] _).toRingHom)
  have hG : ∀ f, G f = ψ (coneMap ℤ x f) := by
    have h : G = ψ.comp (coneMap ℤ x).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro n
        exact RingHom.congr_fun (RingHom.ext_int (G.comp C) ((ψ.comp (coneMap ℤ x).toRingHom).comp C)) n
      · rintro ⟨u, j⟩
        cases u
        simp only [G, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X]
        rw [show (inrV (ι := ι) (ι₂ := GlobalTheory κ) ⟨(), j⟩) = ⟨Sum.inr (), j⟩ from rfl]
        rw [graphMap, eval₂Hom_X']
        simp only [map_mul, map_C, map_X, coneMap, aeval_X]
        rw [show φ (Ideal.Quotient.mk (mCoordIdeal y) (blockForms k₀ M ⟨(), j⟩)) = C (x ⟨(), j⟩) * X k₀ from
          (Ideal.Quotient.lift_mk _ _ _).trans (hcone _)]
        simp [ψ, mul_assoc]
    exact fun f => RingHom.congr_fun h f
  ext f
  show rename inrV f ∈ RingHom.ker (graphMap (mCoordIdeal y) (blockForms k₀ M)) ↔ f ∈ RingHom.ker (coneMap ℤ x)
  rw [RingHom.mem_ker, RingHom.mem_ker]
  constructor
  · intro h
    have h0 : G f = 0 := by
      show MvPolynomial.map φ (graphMap (mCoordIdeal y) (blockForms k₀ M) (rename inrV f)) = 0
      rw [h, map_zero]
    rw [hG] at h0
    rw [← hev (coneMap ℤ x f), h0, map_zero]
  · intro h
    apply MvPolynomial.map_injective φ hφ
    rw [map_zero]
    show G f = 0
    rw [hG, h, map_zero]

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory

noncomputable section

theorem L2GramLattice.proof : L2GramLattice.Statement := by
  intro E _ _ _ X _ μ _ w hmeas hbdd hind
  classical
  set n := Module.finrank ℤ E
  let b : Module.Basis (Fin n) ℤ E := Module.finBasis ℤ E
  have hmem : ∀ s, MemLp (w s) 2 μ := fun s => by
    obtain ⟨C, hC⟩ := hbdd s
    exact (memLp_top_of_bound (hmeas s) C hC).mono_exponent le_top
  let F : Fin n → Lp ℂ 2 μ := fun i => (hmem (b i)).toLp _
  let ψ : (Fin n → ℝ) →ₗ[ℝ] Lp ℂ 2 μ :=
    { toFun := fun c => ∑ i, c i • F i
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a c => by simp [Finset.smul_sum, smul_smul] }

  have hψ : ∀ c : Fin n → ℝ, (ψ c : X → ℂ) =ᵐ[μ] fun z => ∑ i, (c i : ℂ) * w (b i) z := by
    intro c
    show ((∑ i, c i • F i : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ] _
    induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      filter_upwards [Lp.coeFn_zero ℂ 2 μ] with z h
      rw [h]
      rfl
    | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (c i • F i) (∑ j ∈ s, c j • F j), Lp.coeFn_smul (c i) (F i),
        (hmem (b i)).coeFn_toLp, ih] with z h1 h2 h3 h4
      rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, Complex.real_smul]
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    apply hind n b b.linearIndependent c
    filter_upwards [hψ c, hc ▸ Lp.coeFn_zero ℂ 2 μ] with z h1 h2
    rw [← h1]
    exact h2

  have hcoord : ∀ s : E, ψ (fun i => (b.equivFun s i : ℝ)) = (hmem s).toLp _ := by
    intro s
    ext1
    filter_upwards [hψ (fun i => (b.equivFun s i : ℝ)), (hmem s).coeFn_toLp] with z h1 h2
    have hs : w s = ∑ i, b.repr s i • w (b i) := by
      conv_lhs => rw [← b.sum_repr s]

      rw [map_sum]
      simp only [map_zsmul]
    rw [h1, h2, hs, Finset.sum_apply]
    simp [zsmul_eq_mul]
  let W := LinearMap.range ψ
  let e₁ : (Fin n → ℝ) ≃ₗ[ℝ] W := LinearEquiv.ofInjective ψ hinj
  have hW : Module.finrank ℝ W = n := by
    rw [← e₁.finrank_eq, Module.finrank_fin_fun]
  let o := (stdOrthonormalBasis ℝ W).reindex (finCongr hW)
  let T : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) := e₁.trans o.repr.toLinearEquiv
  have hT : ∀ c, ‖T c‖ = ‖ψ c‖ := by
    intro c
    simp only [T, e₁, LinearEquiv.trans_apply, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.norm_map]
    rw [Submodule.coe_norm, LinearEquiv.ofInjective_apply]
  let cast : (Fin n → ℤ) →+ (Fin n → ℝ) := AddMonoidHom.compLeft (Int.castAddHom ℝ) (Fin n)
  let φ : E →+ EuclideanSpace ℝ (Fin n) :=
    (T.toLinearMap.toAddMonoidHom.comp cast).comp b.equivFun.toLinearMap.toAddMonoidHom
  have hφ : ∀ s, φ s = T (fun i => (b.equivFun s i : ℝ)) := fun s => rfl
  let v : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) := (Pi.basisFun ℝ (Fin n)).map T
  have hφb : ∀ i, φ (b i) = v i := by
    intro i
    rw [hφ]
    simp only [v, Module.Basis.map_apply, Pi.basisFun_apply, Module.Basis.equivFun_self]
    congr 1
    funext j
    by_cases h : i = j <;> simp [h, eq_comm]
  have hL : imageLattice φ = Submodule.span ℤ (Set.range v) := by
    apply le_antisymm
    · rintro _ ⟨s, rfl⟩

      rw [← b.sum_repr s, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [map_zsmul, hφb]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨b i, hφb i⟩
  have key : ∀ L : Submodule ℤ (EuclideanSpace ℝ (Fin n)), L = Submodule.span ℤ (Set.range v) →
      DiscreteTopology L ∧ ∀ [DiscreteTopology L], IsZLattice ℝ L := by
    rintro _ rfl
    exact ⟨inferInstance, by intro _; infer_instance⟩
  refine ⟨φ, ?_, (key _ hL).1, (key _ hL).2, ?_⟩
  · intro s t hst
    rw [hφ, hφ] at hst
    apply b.equivFun.injective
    funext i
    exact_mod_cast congrFun (T.injective hst) i
  · intro s
    rw [hφ, hT, hcoord, Lp.norm_toLp,
      MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top (hmem s),
      ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
    norm_num

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter MeasureTheory

noncomputable section

def TensorPowerL2Degree.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsSmallGeneratedDatum P0 y D A → IsConjInvariantH A →
    ∃ (μ : Measure ((Σ k, ι k) → ℂ)) (m : ℕ),
      IsProbabilityMeasure μ ∧ μ (mcPts (mCoordIdeal y))ᶜ = 0 ∧ IsZariskiDenseMeasure (mCoordIdeal y) μ ∧
      1 ≤ m ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ q : ℕ in atTop,
        ∀ (r : ℕ) (ψ : chartLat y A.a (m * q) →+ EuclideanSpace ℝ (Fin r)), Function.Injective ψ →
          (∀ s : chartLat y A.a (m * q), ‖ψ s‖ = sectionL2Norm μ y A (m * q) (s : Ω)) →
          ∀ [DiscreteTopology (imageLattice ψ)] [IsZLattice ℝ (imageLattice ψ)],
            -Real.log (ZLattice.covolume (imageLattice ψ)) ≤
              (II K ι (mCoordIdeal y) (D + 1) (fun _ => A) + ε) *
                (((m * q : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionPointValue.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι),
    IsRelevant (mCoordIdeal y) → ContinuousOn A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} →
    ∃ w : ∀ n : ℕ, chartLat y A.a n →+ (((Σ k, ι k) → ℂ) → ℂ),
      (∀ (n : ℕ) (s : chartLat y A.a n), ContinuousOn (w n s) (mcPts (mCoordIdeal y))) ∧
      (∀ (n : ℕ) (s : chartLat y A.a n) (dg dh : K → ℕ) (g h : MRing ι) (z : (Σ k, ι k) → ℂ),
        IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + n * A.a k) →
        aeval y g = (s : Ω) * aeval y h → z ∈ mcPts (mCoordIdeal y) →
        eval z (map (Int.castRingHom ℂ) g) =
          w n s z * eval z (map (Int.castRingHom ℂ) h) * (A.h z : ℂ) ^ n) ∧
      (∀ (n : ℕ) (s : chartLat y A.a n), ∀ z ∈ mcPts (mCoordIdeal y),
        secNormAt y A n (s : Ω) z = ‖w n s z‖) ∧
      (∀ (n k : ℕ) (s : chartLat y A.a n) (t : chartLat y A.a k) (st : chartLat y A.a (n + k)),
        (st : Ω) = s * t → ∀ z ∈ mcPts (mCoordIdeal y), w (n + k) st z = w n s z * w k t z) ∧
      ∀ (n r : ℕ) (s : Fin r → chartLat y A.a n),
        ∃ (e e' : K → ℕ) (h : MRing ι) (g : Fin r → MRing ι),
          IsMultiHomog h e' ∧ (∀ i, IsMultiHomog (g i) e) ∧ (∀ k, (e k : ℤ) = e' k + n * A.a k) ∧
          aeval y h ≠ 0 ∧ ∀ i, aeval y (g i) = (s i : Ω) * aeval y h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter MeasureTheory

noncomputable section

section Objects

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


variable (ι) in
def addIdx (N : ℕ) : Option K → Type := fun k => Option.elim k (Fin N) ι

instance addIdx.instFintype (N : ℕ) : ∀ k, Fintype (addIdx ι N k)
  | none => inferInstanceAs (Fintype (Fin N))
  | some k => inferInstanceAs (Fintype (ι k))

def addBlock {Ω : Type} (y : (Σ k, ι k) → Ω) {N : ℕ} (v : Fin N → Ω) : (Σ k, addIdx ι N k) → Ω
  | ⟨none, j⟩ => v j
  | ⟨some k, i⟩ => y ⟨k, i⟩

def basePart₂ {N : ℕ} (z : (Σ k, addIdx ι N k) → ℂ) : (Σ k, ι k) → ℂ := fun p => z ⟨some p.1, p.2⟩

end Objects

def PowerBlockDatum.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsSmallGeneratedDatum P0 y D A → IsConjInvariantH A →
    ∃ (m N : ℕ) (v : Fin N → Ω) (d : HSMBlockDatum D (Option K) (addIdx ι N) Ω)
      (μ : Measure ((Σ k, ι k) → ℂ)),
      1 ≤ m ∧ d.y = addBlock y v ∧ d.k₀ = none ∧
      (∀ j, v j ∈ chartLat y A.a m) ∧ KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v ∧
      (∀ z ∈ mcPts (mCoordIdeal d.y), ∀ j : Fin N,
        secNormAt y A m (v j) (basePart₂ z) * d.A.h z = ‖z ⟨none, j⟩‖) ∧
      (∀ᶠ q : ℕ in atTop, chartLat y A.a (m * q) = secM d.y (blockDeg (none : Option K) q)) ∧
      IsProbabilityMeasure μ ∧ μ (mcPts (mCoordIdeal y))ᶜ = 0 ∧ IsZariskiDenseMeasure (mCoordIdeal y) μ ∧
      ∀ (q : ℕ) (f : MRing (addIdx ι N)), IsMultiHomog f (blockDeg (none : Option K) q) →
        sectionL2Norm μ y A (m * q) (aeval d.y f) = blockL2Norm d q f

def PowerBlockTop.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (m N : ℕ) (v : Fin N → Ω)
    (B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (addIdx ι N))
    (I : AllFam),
    I.IsFamily → IsArithVar (mCoordIdeal y) (D + 1) → IsSmoothHerm A → 1 ≤ m →
    (∀ j, v j ∈ chartLat y A.a m) → KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v →
    B.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg (none : Option K) → IsSmoothHerm B →
    (∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ j : Fin N,
      secNormAt y A m (v j) (basePart₂ z) * B.h z = ‖z ⟨none, j⟩‖) →
    I (Option K) (addIdx ι N) (mCoordIdeal (addBlock y v)) (D + 1) (fun _ => B) =
      (m : ℝ) ^ (D + 1) * I K ι (mCoordIdeal y) (D + 1) (fun _ => A)

def BlockChiCovolume.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (n : ℕ) (E : AddSubgroup Ω), E = secM d.y (blockDeg d.k₀ n) →
    ∀ (r : ℕ) (ψ : E →+ EuclideanSpace ℝ (Fin r)), Function.Injective ψ →
      (∀ (s : E) (f : MRing ι), IsMultiHomog f (blockDeg d.k₀ n) → aeval d.y f = (s : Ω) →
        ‖ψ s‖ = blockL2Norm d n f) →
      ∀ [DiscreteTopology (imageLattice ψ)] [IsZLattice ℝ (imageLattice ψ)],
        -Real.log (ZLattice.covolume (imageLattice ψ)) = blockChi d n

open ProjLine

namespace PowerBlockProjectiveLine

end PowerBlockProjectiveLine

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def FibreRelLift.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (ℓ : ℕ) (a : K → ℤ) (r : ℕ) (s : Fin r → Ω)
    (J : KH.Cell K ι 0)
    (u : Fin r → LocalizedModule (KH.cellMon (ZMod ℓ) J.1) (MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ))),
    (∀ j, s j ∈ chartLat y a 1) → (∀ k, y ⟨k, GenOnFibres.cellChart J k⟩ ≠ 0) →
    (∀ j, u j ∈ KH.locPart ι (KH.quotPart (ZMod ℓ) (GenOnFibres.idealOver y (ZMod ℓ))) (KH.cellMon (ZMod ℓ) J.1) (-a)) →
    ∑ j, u j * GenOnFibres.secCoch (y := y) (S := ZMod ℓ) (s j) a J = 1 →
    ∃ (u' : Fin r → Ω) (v : Ω), (∀ j, u' j ∈ chartRingZ y (GenOnFibres.cellChart J)) ∧
      v ∈ chartRingZ y (GenOnFibres.cellChart J) ∧
      ∑ j, u' j * (s j * ∏ k, y ⟨k, GenOnFibres.cellChart J k⟩ ^ (-a k)) + ℓ * v = 1

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
