module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle034
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle035
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgeAnalytic
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle037
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle043
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle039
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeK
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace TwoBlockTop

variable {κ : Type}

theorem isPullHerm_blockLine [Fintype κ] (m : ConeMetric ℂ (Ix κ)) (b : Fin 2) :
    IsPullHerm (blkOf b) (blkV κ b) (HermLine.ofCone m) (blockLine m b) := by
  refine ⟨?_, fun z => rfl⟩
  funext k
  show (Pi.single b 1 : Fin 2 → ℤ) k = Function.extend (blkOf b) (fun _ : Unit => (1 : ℤ)) 0 k
  by_cases hk : k = b
  · subst hk
    rw [Pi.single_eq_same]
    exact (Function.Injective.extend_apply (f := blkOf k) (fun _ _ _ => Subsingleton.elim _ _)
      (fun _ => (1 : ℤ)) (0 : Fin 2 → ℤ) ()).symm
  · rw [Pi.single_eq_of_ne hk, Function.extend_apply' _ _ _ (fun ⟨_, hu⟩ => hk hu.symm)]
    rfl

theorem pair_comp_blkV_zero {Ω : Type} [Field Ω] (x x' : Ix κ → Ω) : pair x x' ∘ blkV κ 0 = x := by
  funext p
  obtain ⟨⟨⟩, i⟩ := p
  simp [pair, blkV]

theorem pair_comp_blkV_one {Ω : Type} [Field Ω] (x x' : Ix κ → Ω) : pair x x' ∘ blkV κ 1 = x' := by
  funext p
  obtain ⟨⟨⟩, i⟩ := p
  simp [pair, blkV]

end TwoBlockTop


open TwoBlockTop in
theorem TwoBlockTop.proof (hPF : PFCoordStatement) (hIm : ImageCoordStatement) (hA : CoordArithOfFnField.Statement)
    (hF : TwoBlockFnField.Statement) (hS : MetricTransportSmooth.Statement) : TwoBlockTop.Statement := by
  classical
  intro D Ω _ _ κ _ I x B m m' hI hx _ hB hm hm'
  obtain ⟨hFp, hFB⟩ := hF Ω κ x B hB
  have hxA : IsArithVar (mCoordIdeal (ι := GlobalTheory κ) x) (D + 1) := by
    rw [← coordIdeal_eq_mCoordIdeal]
    exact hx

  obtain ⟨i, hi⟩ := hx.2.1.2.2 ()
  have hx0 : x ≠ 0 := fun h => hi ((X_mem_coordIdeal_iff x _).mpr (by rw [h]; rfl))
  obtain ⟨B', -, hB'⟩ := isInvMat_mul hB
  have hBx0 : matAct B x ≠ 0 := fun h => hx0 ((matAct_eq_zero_iff hB' x).mp h)
  obtain ⟨⟨⟨⟩, i₀⟩, hi₀⟩ := Function.ne_iff.mp hx0
  obtain ⟨⟨⟨⟩, i₁⟩, hi₁⟩ := Function.ne_iff.mp hBx0

  have hpA : IsArithVar (mCoordIdeal (ι := FinTwoTypeFamily κ) (pair x (matAct B x))) (D + 1) :=
    hA Unit (GlobalTheory κ) (Fin 2) (FinTwoTypeFamily κ) Ω x (pair x (matAct B x)) (D + 1) ⟨0⟩
      (fun k => by
        fin_cases k
        · exact ⟨i₀, by simpa [pair] using hi₀⟩
        · exact ⟨i₁, by simpa [pair] using hi₁⟩) hFp.symm hxA
  have hBA : IsArithVar (mCoordIdeal (ι := GlobalTheory κ) (matAct B x)) (D + 1) :=
    hA Unit (GlobalTheory κ) Unit (GlobalTheory κ) Ω x (matAct B x) (D + 1) ⟨()⟩ (fun _ => ⟨i₁, hi₁⟩) hFB.symm hxA

  have key : ∀ (b : Fin 2) (z : Ix κ → Ω) (μ : ConeMetric ℂ (Ix κ)), pair x (matAct B x) ∘ blkV κ b = z →
      IsArithVar (mCoordIdeal (ι := GlobalTheory κ) z) (D + 1) →
      blockFnField (ι := GlobalTheory κ) z = blockFnField (ι := GlobalTheory κ) x → IsSmoothMetric μ →
      I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x (matAct B x)) (D + 1) (fun _ => blockLine μ b) = top I z μ D := by
    intro b z μ hz hzA hzF hμ
    have himg : imageZ (blkV κ b) (mCoordIdeal (ι := FinTwoTypeFamily κ) (pair x (matAct B x))) = coordIdeal ℤ z := by
      rw [hIm Unit (GlobalTheory κ) (Fin 2) (FinTwoTypeFamily κ) (blkOf b) (blkV κ b) Ω _ (isBlockMap_blkV κ b), hz,
        coordIdeal_eq_mCoordIdeal]
    have h := hPF I hI Unit (GlobalTheory κ) (Fin 2) (FinTwoTypeFamily κ) (blkOf b) (blkV κ b) Ω (pair x (matAct B x)) (D + 1)
      (fun _ => HermLine.ofCone μ) (fun _ => blockLine μ b) (isBlockMap_blkV κ b) hpA
      (by rw [himg, coordIdeal_eq_mCoordIdeal]; exact hzA)
      (fun _ => gbamix_smoothHerm_ofCone hμ) (fun _ => isPullHerm_blockLine μ b)
    rw [IntermediateField.relfinrank_eq_one_iff.mpr (by rw [hz, hzF, hFp]), Nat.cast_one, one_mul] at h
    rw [top, ← himg]
    exact h
  exact ⟨key 0 x m (pair_comp_blkV_zero _ _) hxA rfl hm,
    key 1 (matAct B x) m' (pair_comp_blkV_one _ _) hBA hFB (hS κ B m m' hB hm hm')⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge

open ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter Set

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ} (R : AnRes P J e)

theorem brFib_finite' (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (y : Fin e → ℂ) :
    (brQ R Ψ ⁻¹' {y} ∩ {x | R.lift x x ∉ mcPts J ∧ Ψ (segre (R.lift x x)) 0 ≠ 0}).Finite := by
  refine Set.Finite.of_finite_image (f := brW R Ψ) ((fibreFinite K ι P e Ψ hP hΨ y).subset ?_)
    ((brW_injOn R Ψ).mono fun x hx => hx.2)
  rintro _ ⟨x, hx, rfl⟩
  have := brW_mem_fibre R Ψ hP.1 hP.2.1.2.1 hx.2.2
  rwa [show brQ R Ψ x = y from hx.1] at this

theorem lift_mem_iff {x z : R.X} (hz : z ∈ R.U x) :
    R.lift z z ∈ mcPts J ↔ R.lift x z ∈ mcPts J := by
  obtain ⟨c, hc, hzc⟩ := R.compat z x z ⟨R.mem_U z, hz⟩
  constructor
  · intro h
    refine mem_mcPts_of_sameOrbit R.homog ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩ h
    funext p
    rw [hzc]
    field_simp [hc p.1]
  · intro h
    exact mem_mcPts_of_sameOrbit R.homog ⟨c, hc, hzc⟩ h

theorem psi_lift_eq {x z : R.X} (hz : z ∈ R.U x)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    ∃ μ : ℂ, μ ≠ 0 ∧ Ψ (segre (R.lift z z)) = μ • Ψ (segre (R.lift x z)) := by
  obtain ⟨c, hc, hzc⟩ := R.compat z x z ⟨R.mem_U z, hz⟩
  exact ⟨∏ k, c k, Finset.prod_ne_zero_iff.mpr fun k _ => hc k, by rw [hzc, segre_smul, map_smul]⟩

theorem isOpen_chart_notB (j : Fin R.A.n) :
    IsOpen ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | R.lift x x ∉ mcPts J}) := by
  rw [isOpen_iff_mem_nhds]
  rintro u1 ⟨hu1, hB1⟩
  set x1 := (R.A.chart j).symm u1
  have hV : (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x1 ∈ 𝓝 u1 :=
    ((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x1)).mem_nhds ⟨hu1, R.mem_U x1⟩
  have hnot : ¬ ∀ f ∈ J, eval (R.lift x1 x1) (map (Int.castRingHom ℂ) f) = 0 := fun h =>
    hB1 ⟨(R.mem x1 x1 (R.mem_U x1)).1, h⟩
  push Not at hnot
  obtain ⟨f, hfJ, hf0⟩ := hnot
  have hcont : ContinuousAt (fun u => eval (R.lift x1 ((R.A.chart j).symm u))
      (map (Int.castRingHom ℂ) f)) u1 :=
    (MvPolynomial.continuous_eval _).continuousAt.comp
      (analyticAt_lift_chart R x1 j ⟨hu1, R.mem_U x1⟩).continuousAt
  filter_upwards [hV, hcont.eventually_ne hf0] with u hu hne
  refine ⟨hu.1, fun hB => ?_⟩
  exact hne (((lift_mem_iff R hu.2).mp hB).2 f hfJ)

theorem not_flat (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) {O : Set (Fin e → ℂ)}
    (hO : IsOpen O) (hOt : O ⊆ (R.A.chart j).target) (hne : O.Nonempty)
    (h0 : ∀ u ∈ O, Ψ (segre (R.lift ((R.A.chart j).symm u) ((R.A.chart j).symm u))) 0 ≠ 0)
    (han : AnalyticOnNhd ℂ (brQ R Ψ ∘ (R.A.chart j).symm) O)
    (hdet : ∀ u ∈ O, LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) u :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0) : False := by
  set O' := O ∩ ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | R.lift x x ∉ mcPts J})
    with hO'def
  have hO' : IsOpen O' := hO.inter (isOpen_chart_notB R j)
  have hne' : O'.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    obtain ⟨u, hu⟩ := hne
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO u hu
    have hsub : Metric.ball u r ⊆
        (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | R.lift x x ∈ mcPts J} := by
      intro v hv
      have hvO := hball hv
      refine ⟨hOt hvO, ?_⟩
      by_contra hB
      have : v ∈ O' := ⟨hvO, hOt hvO, hB⟩
      rw [h] at this
      exact this
    exact (Metric.measure_ball_pos volume u hr).ne' (measure_mono_null hsub (R.null j))
  obtain ⟨y, hy⟩ := exists_infinite_fibre hO' hne' (han.mono inter_subset_left)
    (fun u hu => hdet u hu.1)
  refine (brFib_finite' R Ψ hP hΨ y).not_infinite ((Set.Infinite.image
    (((R.A.chart j).symm.injOn.mono (show O' ⊆ (R.A.chart j).target from
      fun u hu => hOt hu.1)).mono inter_subset_left) hy).mono ?_)
  rintro _ ⟨u, ⟨huO, hqu⟩, rfl⟩
  exact ⟨hqu, huO.2.2, h0 u huO.1⟩

theorem det_brQ_chart (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {x : R.X}
    {j k : Fin R.A.n} (hj : x ∈ (R.A.chart j).source) (hk : x ∈ (R.A.chart k).source)
    (h0 : Ψ (segre (R.lift x x)) 0 ≠ 0) :
    LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) =
      LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) *
      LinearMap.det (fderiv ℂ (R.A.chart k ∘ (R.A.chart j).symm) (R.A.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) := by
  set u := R.A.chart j x
  have hsu : (R.A.chart j).symm u = x := (R.A.chart j).left_inv hj
  set T := R.A.chart k ∘ (R.A.chart j).symm with hTdef
  have huk : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' (R.A.chart k).source :=
    ⟨(R.A.chart j).map_source hj, by rw [mem_preimage, hsu]; exact hk⟩
  have hT : AnalyticAt ℂ T u := R.A.holo j k u huk
  have hTu : T u = R.A.chart k x := by simp only [hTdef, Function.comp_apply, hsu]
  have hQk := analyticAt_brQ R Ψ x k hk h0
  have heq : brQ R Ψ ∘ (R.A.chart j).symm =ᶠ[𝓝 u] (brQ R Ψ ∘ (R.A.chart k).symm) ∘ T := by
    filter_upwards [((R.A.chart j).isOpen_inter_preimage_symm (R.A.chart k).open_source).mem_nhds
      huk] with v hv
    simp only [hTdef, Function.comp_apply, (R.A.chart k).left_inv hv.2]
  rw [heq.fderiv_eq, fderiv_comp u (by rw [hTu]; exact hQk.differentiableAt) hT.differentiableAt,
    hTu]
  exact LinearMap.det_comp _ _

end GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KoszulCech

noncomputable section

namespace GenKoszulStep

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)]

theorem subsingleton_cechHc_iff {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (c : K → ℤ) (n : ℕ) :
    Subsingleton (KH.cechHc ι 𝓜 c (n + 1)) ↔
      ∀ x ∈ KH.cechCc ι 𝓜 c (n + 1), KH.cechD S ι M (n + 1) x = 0 →
        ∃ y ∈ KH.cechCc ι 𝓜 c n, KH.cechD S ι M n y = x := by
  rw [KH.cechHc, Submodule.Quotient.subsingleton_iff, eq_top_iff]
  constructor
  · intro h x hx hdx
    have hZ : x ∈ KH.cechZc ι 𝓜 c (n + 1) := ⟨hx, hdx⟩
    obtain ⟨y, hy, hyx⟩ := h (Submodule.mem_top (x := ⟨x, hZ⟩))
    exact ⟨y, hy, hyx⟩
  · rintro h ⟨x, hx, hdx⟩ -
    obtain ⟨y, hy, hyx⟩ := h x hx hdx
    exact ⟨y, hy, hyx⟩

theorem gather {V : Ideal (MRingOver S ι)} {α : K → ℤ} (h : KH.GeneratedV S V α) :
    ∃ (R : ℕ) (z : Fin R → KH.CechC S ι (MRingOver S ι ⧸ V) 0),
      (∀ j, z j ∈ KH.cechZc ι (KH.quotPart S V) α 0) ∧
      ∀ I : KH.Cell K ι 0, ∃ u : Fin R → LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V),
        (∀ j, u j ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I.1) (-α)) ∧ ∑ j, u j * z j I = 1 := by
  classical
  choose r zz uu hz hu hs using h
  have : Finite (KH.Cell K ι 0) := by unfold KH.Cell; infer_instance
  let _ : Fintype (KH.Cell K ι 0) := Fintype.ofFinite _
  set e := Fintype.equivFin (Σ I : KH.Cell K ι 0, Fin (r I))
  let v : ∀ I : KH.Cell K ι 0, (Σ I' : KH.Cell K ι 0, Fin (r I')) →
      LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V) :=
    fun I σ => if h : σ.1 = I then h ▸ uu σ.1 σ.2 else 0
  refine ⟨Fintype.card (Σ I : KH.Cell K ι 0, Fin (r I)), fun j => zz (e.symm j).1 (e.symm j).2,
    fun j => hz _ _, fun I => ⟨fun j => v I (e.symm j), fun j => ?_, ?_⟩⟩
  · have hv : ∀ σ, v I σ ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I.1) (-α) := by
      rintro ⟨I', i⟩
      simp only [v]
      split_ifs with hI
      · subst hI
        exact hu _ i
      · exact Submodule.zero_mem _
    exact hv (e.symm j)
  · rw [Equiv.sum_comp e.symm (fun σ => v I σ * zz σ.1 σ.2 I), Fintype.sum_sigma,
      Finset.sum_eq_single I]
    · simp only [v, dif_pos rfl]
      exact hs I
    · intro I' _ hI'
      refine Finset.sum_eq_zero fun i _ => ?_
      simp only [v, dif_neg hI']
      exact zero_mul (zz I' i I)
    · simp

end GenKoszulStep

open GenKoszulStep

theorem GenKoszulStep.proof (hB : KoszulCechComplex.Statement) (hC : KoszulCechExact.Statement)
    (hD : DoubleComplexVanish.Statement) (hSq : KH.CechDSqStatement) (hDeg : KH.CechDDegStatement) :
    GenKoszulStep.Statement := by
  intro S _ K _ _ ι _ _ V α _ hα
  obtain ⟨R, z, hz, hu⟩ := gather hα
  refine ⟨R, fun c hc => ?_⟩
  have hB' := hB S K ι V α R z hz c
  have hC' := hC S K ι V α R z hu c
  have key := hD (fun p n => KosC S ι V R p n) (fun p n => kosPart S ι V R α c p n)
    (fun p n => kosCech S ι V R p n) (fun p n => kosD z p n) R
    (fun p n x hx J _ => hDeg S K ι _ _ _ n (x J) (hx J trivial))
    (fun p n x hx => (hB' p n).1 x hx)
    (fun p n x _ => funext fun J => LinearMap.congr_fun (hSq S K ι (MRingOver S ι ⧸ V) n) (x J))
    (fun p n x _ => (hB' p n).2.1 x)
    (fun p n x _ => (hB' p n).2.2 x)
    (fun n x hx => (hC' n).1 x hx)
    (fun p n x hx h0 => (hC' n).2 p x hx h0)
    (fun p n hp x _ => funext fun J => absurd ((J.2.symm.trans_le (J.1.card_le_univ)).trans_eq
      (Fintype.card_fin R)) (by omega))
    (fun p hp1 hpR n x hx h0 => by
      have hJ := fun J => (subsingleton_cechHc_iff _ _ n).mp (hc p hp1 hpR (n + 1) (by omega))
        (x J) (hx J trivial) (congrFun h0 J)
      choose y hy hdy using hJ
      exact ⟨y, fun J _ => hy J, funext hdy⟩)
  intro i hi
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  rw [subsingleton_cechHc_iff]
  intro x hx hdx
  obtain ⟨y, hy, hdy⟩ := key n (fun _ => x) (fun J _ => by simpa using hx) (funext fun _ => hdx)
  exact ⟨y ⟨∅, Finset.card_empty⟩, by simpa using hy _ trivial, congrFun hdy _⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace RelChartPoly

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

theorem chartMonomial_mem (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (e : K → ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ e k ∈ relSecM R y e := by
  classical
  have h := monomial_mem_relSecM R y (b := e) (fun q : Σ k, ι k => if q.2 = c q.1 then e q.1 else 0)
    (fun k => by simp)
  convert h using 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp [pow_ite]

theorem coord_mem (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Σ k, ι k) [DecidableEq K] :
    y p ∈ relSecM R y (Pi.single p.1 1) := by
  have h := chartMonomial_mem R y (Function.update c p.1 p.2) (Pi.single p.1 1)
  convert h using 1
  rw [Finset.prod_eq_single p.1]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

theorem generator_mem (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Σ k, ι k) :
    y p / y ⟨p.1, c p.1⟩ * ∏ k, y ⟨k, c k⟩ ∈ relSecM R y (fun _ => 1) := by
  classical
  by_cases h0 : y ⟨p.1, c p.1⟩ = 0
  · simp [h0]
  have hW : ∏ k, y ⟨k, c k⟩ = (∏ k, y ⟨k, c k⟩ ^ (Pi.single p.1 (1 : ℕ) : K → ℕ) k) *
      ∏ k, y ⟨k, c k⟩ ^ (if k = p.1 then 0 else 1) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← pow_add]
    by_cases hk : k = p.1
    · subst hk; simp
    · simp [hk]
  have h1 : ∏ k, y ⟨k, c k⟩ ^ (Pi.single p.1 (1 : ℕ) : K → ℕ) k = y ⟨p.1, c p.1⟩ := by
    rw [Finset.prod_eq_single p.1]
    · simp
    · intro k _ hk
      simp [hk]
    · simp
  have hmem := mul_mem_relSecM R y (coord_mem R y c p)
    (chartMonomial_mem R y c (fun k => if k = p.1 then 0 else 1))
  have hb : (Pi.single p.1 1 + fun k => if k = p.1 then 0 else 1 : K → ℕ) = fun _ => 1 := by
    funext k
    by_cases hk : k = p.1
    · subst hk; simp
    · simp [hk]
  rw [hb] at hmem
  rw [hW, h1, ← mul_assoc, div_mul_cancel₀ _ h0]
  exact hmem

end RelChartPoly

theorem RelChartPoly.proof : RelChartPoly.Statement := by
  intro K _ ι _ Ω _ R y c σ hσ
  have hW : ∀ M : ℕ, (∏ k, y ⟨k, c k⟩) ^ M ∈ relSecM R y (fun _ => M) := by
    intro M
    rw [← Finset.prod_pow]
    exact RelChartPoly.chartMonomial_mem R y c (fun _ => M)
  have hmul : ∀ {a b : ℕ} {x x' : Ω}, x ∈ relSecM R y (fun _ => a) → x' ∈ relSecM R y (fun _ => b) →
      x * x' ∈ relSecM R y (fun _ => a + b) := fun hx hx' => mul_mem_relSecM R y hx hx'
  induction hσ using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact ⟨1, by simpa using RelChartPoly.generator_mem R y c p⟩
  | algebraMap r =>
    refine ⟨0, ?_⟩
    rw [pow_zero, mul_one, Algebra.algebraMap_eq_smul_one]
    refine Submodule.smul_mem _ r ?_
    simpa using hW 0
  | add x x' _ _ hx hx' =>
    obtain ⟨N, hN⟩ := hx
    obtain ⟨M, hM⟩ := hx'
    refine ⟨N + M, ?_⟩
    rw [add_mul]
    refine add_mem ?_ ?_
    · have := hmul hN (hW M)
      convert this using 1
      ring
    · have := hmul hM (hW N)
      rw [add_comm N M]
      convert this using 1
      ring
  | mul x x' _ _ hx hx' =>
    obtain ⟨N, hN⟩ := hx
    obtain ⟨M, hM⟩ := hx'
    refine ⟨N + M, ?_⟩
    have := hmul hN hM
    convert this using 1
    ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
