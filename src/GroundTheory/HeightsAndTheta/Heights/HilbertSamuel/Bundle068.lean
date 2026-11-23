module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartNakayamaGenAgree
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartNakayamaGenLocal
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenSESStep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle032
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle034
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle052
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChangeOfLattice
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle035
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgeAnalytic
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle050
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle060
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle063
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle012
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle015

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace ChartNakayamaGen

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

theorem homog_unique {p : MRingOver S ι} {a b : K → ℕ} (ha : IsMultiHomog p a) (hb : IsMultiHomog p b)
    (h0 : p ≠ 0) : a = b := by
  obtain ⟨μ, hμ⟩ := Finset.nonempty_iff_ne_empty.mpr (mt MvPolynomial.support_eq_empty.mp h0)
  funext k
  exact (ha μ hμ k).symm.trans (hb μ hμ k)

theorem chartMon_ne_zero [Nontrivial S] (c : ∀ k, ι k) (e : K → ℕ) : chartMon (S := S) c e ≠ 0 := by
  have h : chartMon (S := S) c e = monomial (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (e k)) 1 := by
    rw [MvPolynomial.monomial_sum_one, chartMon]
    exact Finset.prod_congr rfl fun k _ => MvPolynomial.X_pow_eq_monomial
  rw [h, Ne, MvPolynomial.monomial_eq_zero]
  exact one_ne_zero

theorem chartMon_one_pow (c : ∀ k, ι k) (n : ℕ) :
    chartMon (S := S) c (fun _ => 1) ^ n = chartMon c (fun _ => n) := by
  simp only [chartMon, pow_one, ← Finset.prod_pow]

theorem smul_mk_cancel' {T : Submonoid (MRingOver S ι)} {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M]
    (w : MRingOver S ι) (y : M) {s : MRingOver S ι} (hs : s ∈ T) :
    (w * s) • LocalizedModule.mk y (⟨s, hs⟩ : T) = LocalizedModule.mk (w • y) 1 :=
  smul_mk_cancel w y ⟨s, hs⟩

theorem exists_kill_of_res_eq_zero {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] (c c' : ∀ k, ι k)
    (w : LocalizedModule (KH.cellMon S (chart c').1) M)
    (hw : KH.cellRes S M (chart c').1 (fun k => ({c k, c' k} : Finset (ι k))) w = 0) :
    ∃ e : ℕ, chartMon (S := S) c (fun _ => e) • w = 0 := by
  induction w using LocalizedModule.induction_on with
  | h m s =>
    have hsub : ∀ k, (chart c').1 k ⊆ ({c k, c' k} : Finset (ι k)) := fun k => by simp [chart]
    rw [GenTwistGenerated.cellRes_mk (GenTwistGenerated.cellMon_mono hsub)] at hw
    obtain ⟨v, hv⟩ := LocalizedModule.mk_eq.mp
      (hw.trans (LocalizedModule.zero_mk (1 : KH.cellMon S (fun k => ({c k, c' k} : Finset (ι k))))).symm)
    simp only [one_smul, smul_zero] at hv
    obtain ⟨e, w', hw'⟩ := dvd_of_mem_pair v.2
    have hz : (chartMon (S := S) c (fun _ => e) * chartMon c' (fun _ => e)) • m = 0 := by
      rw [hw', mul_comm, mul_smul, ← Submonoid.smul_def, hv, smul_zero]
    refine ⟨e, ?_⟩
    rw [LocalizedModule.smul'_mk, ← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
    refine ⟨⟨chartMon c' (fun _ => e), chartMon_mem c' _⟩, ?_⟩
    show chartMon (S := S) c' (fun _ => e) • (s : MRingOver S ι) • chartMon (S := S) c (fun _ => e) • m =
      chartMon (S := S) c' (fun _ => e) • (s : MRingOver S ι) • (0 : M)
    rw [smul_zero, smul_zero, smul_comm (chartMon c' (fun _ => e)) (s : MRingOver S ι),
      smul_smul (chartMon c' (fun _ => e)) (chartMon c (fun _ => e)) m,
      mul_comm (chartMon c' (fun _ => e)) (chartMon c (fun _ => e)), hz, smul_zero]

theorem genNear_of_chart [Nontrivial S] {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] {𝓜 : (K → ℤ) → Submodule S M} {d : K → ℤ} (h𝓜 : KH.IsMGraded S ι 𝓜)
    (c : ∀ k, ι k) {f₀ : MRingOver S ι} {δ₀ : K → ℕ} (hf₀ : IsMultiHomog f₀ δ₀)
    (hloc : ∀ x ∈ KH.locPart ι 𝓜 (KH.cellMon S (chart c).1) d, ∃ (t : MRingOver S ι) (a : K → ℕ) (r : ℕ)
        (p : Fin r → MRingOver S ι) (z : Fin r → KH.CechC S ι M 0),
        t ∈ KH.cellMon S (chart c).1 ∧ IsMultiHomog t a ∧ (∀ j, IsMultiHomog (p j) (a + δ₀)) ∧
        (∀ j, z j ∈ KH.cechZc ι 𝓜 d 0) ∧ (f₀ * t) • x = ∑ j, p j • z j (chart c)) :
    GenNear S ι 𝓜 d (f₀ * chartMon c (fun _ => 1)) (δ₀ + fun _ => 1) := by
  intro J
  obtain ⟨c', rfl⟩ : ∃ c', J = chart c' := ⟨_, eq_chart J⟩
  intro x hx
  obtain ⟨m, t, a, ht, hm, rfl⟩ := GenSESStep.locPart_normal h𝓜 hx

  have hy : LocalizedModule.mk m (⟨chartMon c a, chartMon_mem c a⟩ : KH.cellMon S (chart c).1) ∈
      KH.locPart ι 𝓜 (KH.cellMon S (chart c).1) d :=
    GenSESStep.mk_mem_locPart _ _ a (isMultiHomog_chartMon c a) hm
  obtain ⟨t₁, a₁, r, p, z, ht₁T, ht₁, hp, hz, he⟩ := hloc _ hy
  obtain ⟨α₁, rfl⟩ := exists_chartMon ht₁T
  obtain rfl : a₁ = α₁ := homog_unique ht₁ (isMultiHomog_chartMon c α₁) (chartMon_ne_zero c α₁)

  set U : ∀ k, Finset (ι k) := fun k => {c k, c' k} with hU
  have hsub : ∀ k, (chart c).1 k ⊆ U k := fun k => by simp [chart, hU]
  have hsub' : ∀ k, (chart c').1 k ⊆ U k := fun k => by simp [chart, hU]
  have hle := GenTwistGenerated.cellMon_mono (S := S) hsub
  have hle' := GenTwistGenerated.cellMon_mono (S := S) hsub'
  have hagree : ∀ j, KH.cellRes S M (chart c').1 U (z j (chart c')) =
      KH.cellRes S M (chart c).1 U (z j (chart c)) := fun j =>
    (res_agree (z j) (LinearMap.mem_ker.mp (hz j).2) c c' U (fun k => by simp [hU])
      (fun k => by simp [hU])).symm
  have hD : KH.cellRes S M (chart c').1 U ((f₀ * chartMon c a₁ * (t : MRingOver S ι)) • LocalizedModule.mk m t -
      ∑ j, (chartMon c a * p j) • z j (chart c')) = 0 := by
    have h2 : KH.cellRes S M (chart c').1 U (∑ j, (chartMon c a * p j) • z j (chart c')) =
        LocalizedModule.mk ((f₀ * chartMon c a₁) • m) 1 := by
      have e1 : KH.cellRes S M (chart c').1 U (∑ j, (chartMon c a * p j) • z j (chart c')) =
          chartMon (S := S) c a • KH.cellRes S M (chart c).1 U (∑ j, p j • z j (chart c)) := by

        rw [map_sum, map_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, hagree j, map_smul, mul_smul]
      rw [e1, ← he, map_smul, GenTwistGenerated.cellRes_mk hle, smul_smul,
        mul_comm (chartMon (S := S) c a) (f₀ * chartMon c a₁)]
      exact smul_mk_cancel' _ _ _
    rw [map_sub, h2, map_smul, GenTwistGenerated.cellRes_mk hle', sub_eq_zero]
    exact smul_mk_cancel' _ _ _
  obtain ⟨e, he0⟩ := exists_kill_of_res_eq_zero c c' _ hD
  rw [smul_sub, sub_eq_zero] at he0

  set E : ℕ := ∑ k, a₁ k with hE
  have haE : ∀ k, a₁ k ≤ E := fun k =>
    Finset.single_le_sum (f := a₁) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have hexp : (fun _ : K => e + E + 1) = (fun _ => 1) + (fun k => E - a₁ k) + (fun _ => e) + a₁ := by
    funext k
    simp only [Pi.add_apply]
    have := haE k
    omega
  have hring : (f₀ * chartMon c (fun _ => 1)) ^ (e + E + 1) * (t : MRingOver S ι) =
      (f₀ ^ (e + E) * chartMon c (fun _ => 1) * chartMon c (fun k => E - a₁ k)) *
        (chartMon c (fun _ => e) * (f₀ * chartMon c a₁ * (t : MRingOver S ι))) := by
    rw [mul_pow, chartMon_one_pow, hexp, chartMon_add, chartMon_add, chartMon_add]
    ring
  refine ⟨e + E + 1, t, a, r, fun j => f₀ ^ (e + E) * chartMon c (fun _ => 1) * chartMon c (fun k => E - a₁ k) *
    chartMon c (fun _ => e) * chartMon c a * p j, z, t.2, ht, fun j => ?_, hz, ?_⟩
  · have h := GenSESStep.isMultiHomog_mul (GenSESStep.isMultiHomog_mul (GenSESStep.isMultiHomog_mul
      (GenSESStep.isMultiHomog_mul (GenSESStep.isMultiHomog_mul (isMultiHomog_pow hf₀ (e + E))
        (isMultiHomog_chartMon c (fun _ => 1))) (isMultiHomog_chartMon c (fun k => E - a₁ k)))
        (isMultiHomog_chartMon c (fun _ => e))) (isMultiHomog_chartMon c a)) (hp j)
    convert h using 1
    funext k
    simp only [Pi.add_apply, Pi.mul_apply, Pi.natCast_apply, Pi.one_apply, nsmul_eq_mul]
    have := haE k
    zify [this] at *
    ring
  · rw [hring, mul_smul, mul_smul (chartMon (S := S) c (fun _ => e)), he0, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only
    simp only [smul_smul]
    congr 1
    ring

end ChartNakayamaGen

theorem ChartNakayamaGen.proof : ChartNakayamaGen.Statement := by
  intro S _ K _ _ ι _ _ M _ _ _ _ 𝓜 P d hS hM h𝓜 hP _ I hI hgen
  obtain ⟨c, rfl⟩ : ∃ c, I = ChartNakayamaGen.chart c := ⟨_, ChartNakayamaGen.eq_chart I⟩
  have h1 : (1 : S) ≠ 0 := fun h => hP.ne_top ((Ideal.eq_top_iff_one P).mpr (by
    have e : (1 : MRingOver S ι) = 0 := by rw [← C_1, h, C_0]
    rw [e]
    exact P.zero_mem))
  have : Nontrivial S := nontrivial_of_ne 1 0 h1
  have hc : ∀ k, (X ⟨k, c k⟩ : MRingOver S ι) ∉ P := fun k => hI k (c k) (Finset.mem_singleton_self _)
  obtain ⟨f₀, δ₀, hf₀, hf₀P, hloc⟩ := ChartNakayamaGen.chart_nakayama hS hM h𝓜 hP c hc hgen
  refine ⟨f₀ * ChartNakayamaGen.chartMon c (fun _ => 1), δ₀ + fun _ => 1,
    GenSESStep.isMultiHomog_mul hf₀ (ChartNakayamaGen.isMultiHomog_chartMon c _), fun h => ?_,
    ChartNakayamaGen.genNear_of_chart h𝓜 c hf₀ hloc⟩
  rcases hP.mem_or_mem h with h | h
  · exact hf₀P h
  · exact ChartNakayamaGen.cellMon_notMem hP hc (ChartNakayamaGen.chartMon_mem c _) h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

set_option linter.unusedSectionVars false

namespace ChangeOfLatticeNested

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem exists_mul_mem_sec_one (x : Ix κ → Ω) (B : Matrix (Ix κ) (Ix κ) ℚ) :
    ∃ M : ℕ, 0 < M ∧ ∀ s ∈ sec ℤ (matAct B x) 1, (M : Ω) * s ∈ sec ℤ x 1 := by
  obtain ⟨d, hd0, hdB⟩ := ChangeOfLattice.exists_clear_den B
  refine ⟨d, Nat.pos_of_ne_zero hd0, fun s hs => ?_⟩
  rw [sec_one'] at hs ⊢
  induction hs using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨i, rfl⟩ := hs
    have e : (d : Ω) * matAct B x i = matAct ((d : ℚ) • B) x i := by
      simp only [matAct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
      push_cast
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    exact ChangeOfLattice.matAct_mem_span (fun i j => by simpa [Matrix.smul_apply] using hdB i j) x i
  | zero => simp
  | add a b _ _ ha hb =>
    rw [mul_add]
    exact add_mem ha hb
  | smul k a _ ha =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ k ha

theorem latLogIndex_eq_sum (x : Ix κ → Ω) (B : Matrix (Ix κ) (Ix κ) ℚ)
    (hle : Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x))) (n : ℕ) :
    latLogIndex x (matAct B x) n = ∑ j ∈ Finset.range n, twoBlockStep x (matAct B x) (n - j - 1) j := by
  have h1 : sec ℤ x 1 ≤ sec ℤ (matAct B x) 1 := by
    rw [sec_one', sec_one']
    exact hle
  have one : (sec ℤ (matAct B x) n).toAddSubgroup.relIndex (sec ℤ x n).toAddSubgroup = 1 :=
    AddSubgroup.relIndex_eq_one.2 fun _ h => ChangeOfLattice.sec_mono hle n h
  unfold latLogIndex
  rw [one, Nat.cast_one, Real.log_one, sub_zero, log_relIndex_eq_sum x _ h1 (exists_mul_mem_sec_one x B) n]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  unfold twoBlockStep
  rw [show n - j - 1 + 1 = n - j by omega]

end ChangeOfLatticeNested

theorem ChangeOfLatticeNested.proof (hS : TwoBlockChainSum.Statement) (hT : TwoBlockTop.Statement) :
    ChangeOfLatticeNested.Statement := by
  intro D Ω _ _ κ _ I x B m m' hI hX hx hB hm hm' hsp
  obtain ⟨e0, e1⟩ := hT D Ω κ I x B m m' hI hX hx hB hm hm'
  have h := hS D Ω κ I x B m m' hI hX hx hB hm hm' hsp
  rw [e0, e1] at h
  refine h.congr_left fun n => ?_
  rw [ChangeOfLatticeNested.latLogIndex_eq_sum x B hsp n]

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

theorem ram_null' (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | Ψ (segre (R.lift x x)) 0 ≠ 0 ∧
      ∃ k, x ∈ (R.A.chart k).source ∧
        LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0}) = 0 := by
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, h00, -⟩
  set x0 := (R.A.chart j).symm u0
  set V := (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x0 with hVdef
  have hV : IsOpen V := (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)
  have hgc : ContinuousOn (fun u => Ψ (segre (R.lift x0 ((R.A.chart j).symm u))) 0) V :=
    fun u hu => (analyticAt_pi_iff.mp (analyticAt_segre_lift R Ψ x0 j hu) 0).continuousAt.continuousWithinAt
  set O := V ∩ (fun u => Ψ (segre (R.lift x0 ((R.A.chart j).symm u))) 0) ⁻¹' {0}ᶜ with hOdef
  have hO : IsOpen O := hgc.isOpen_inter_preimage hV isOpen_compl_singleton
  have hu0O : u0 ∈ O := ⟨⟨hu0, R.mem_U x0⟩, h00⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO u0 hu0O
  have h0 : ∀ u ∈ Metric.ball u0 r,
      Ψ (segre (R.lift ((R.A.chart j).symm u) ((R.A.chart j).symm u))) 0 ≠ 0 := by
    intro u hu
    obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq R (hball hu).1.2 Ψ
    rw [hμeq, Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero hμ (hball hu).2
  have hQa : AnalyticOnNhd ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (Metric.ball u0 r) := by
    intro u hu
    have := analyticAt_brQ R Ψ _ j ((R.A.chart j).map_target (hball hu).1.1) (h0 u hu)
    rwa [(R.A.chart j).right_inv (hball hu).1.1] at this
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, fun u => LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) u :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)), fun u hu => analyticAt_det_fderiv (hQa u hu), ?_, ?_⟩
  · by_contra hall
    push Not at hall
    exact not_flat R Ψ hP hΨ j Metric.isOpen_ball (fun u hu => (hball hu).1.1)
      ⟨u0, Metric.mem_ball_self hr⟩ h0 hQa hall
  · rintro w ⟨⟨hwt, hw0, k, hk, hdk⟩, -⟩
    have := det_brQ_chart R Ψ (j := j) ((R.A.chart j).map_target hwt) hk hw0
    rw [(R.A.chart j).right_inv hwt] at this
    show LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) w :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0
    rw [this, hdk, zero_mul]

theorem volume_projection_zeroSet_null (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩
      (R.A.chart j).symm ⁻¹' {x | Ψ (segre (R.lift x x)) 0 = 0}) = 0 := by
  classical
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, -⟩
  set x0 := (R.A.chart j).symm u0
  set V := (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x0 with hVdef
  have hV : IsOpen V := (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV u0 ⟨hu0, R.mem_U x0⟩
  set f : (Fin e → ℂ) → ℂ := fun u => Ψ (segre (R.lift x0 ((R.A.chart j).symm u))) 0 with hfdef
  have hfa : AnalyticOnNhd ℂ f V := fun u hu =>
    analyticAt_pi_iff.mp (analyticAt_segre_lift R Ψ x0 j hu) 0
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, f, hfa.mono hball, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    have hgood := hΨ _ (R.mem x0 x0 (R.mem_U x0))
    obtain ⟨i0, hi0⟩ : ∃ i0, Ψ (segre (R.lift x0 x0)) i0 ≠ 0 := by
      by_contra h
      push Not at h
      exact hgood (funext h)
    have hi0ne : i0 ≠ 0 := by
      rintro rfl
      exact hi0 (hall u0 (Metric.mem_ball_self hr))
    set m : Fin e := i0.pred hi0ne
    have hm : m.succ = i0 := Fin.succ_pred i0 hi0ne
    set Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) :=
      (LinearMap.funLeft ℂ ℂ (Equiv.swap (0 : Fin (e + 1)) i0)).comp Ψ with hΨ'def
    have hΨ'app : ∀ w i, Ψ' w i = Ψ w (Equiv.swap 0 i0 i) := fun w i => rfl
    have hΨ' : IsGoodProj P Ψ' := by
      intro z hz h
      refine hΨ z hz (funext fun i => ?_)
      have := congrFun h (Equiv.swap 0 i0 i)
      rw [hΨ'app, Equiv.swap_apply_self] at this
      exact this
    have hg'c : ContinuousOn (fun u => Ψ' (segre (R.lift x0 ((R.A.chart j).symm u))) 0)
        (Metric.ball u0 r) := fun u hu =>
      (analyticAt_pi_iff.mp (analyticAt_segre_lift R Ψ' x0 j (hball hu)) 0).continuousAt.continuousWithinAt
    set O := Metric.ball u0 r ∩
      (fun u => Ψ' (segre (R.lift x0 ((R.A.chart j).symm u))) 0) ⁻¹' {0}ᶜ with hOdef
    have hO : IsOpen O := hg'c.isOpen_inter_preimage Metric.isOpen_ball isOpen_compl_singleton
    have hu0O : u0 ∈ O := by
      refine ⟨Metric.mem_ball_self hr, ?_⟩
      show Ψ' (segre (R.lift x0 x0)) 0 ≠ 0
      rw [hΨ'app, Equiv.swap_apply_left]
      exact hi0
    have h0O : ∀ u ∈ O,
        Ψ' (segre (R.lift ((R.A.chart j).symm u) ((R.A.chart j).symm u))) 0 ≠ 0 := by
      intro u hu
      obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq R (hball hu.1).2 Ψ'
      rw [hμeq, Pi.smul_apply, smul_eq_mul]
      exact mul_ne_zero hμ hu.2
    have hanO : AnalyticOnNhd ℂ (brQ R Ψ' ∘ (R.A.chart j).symm) O := by
      intro u hu
      have := analyticAt_brQ R Ψ' _ j ((R.A.chart j).map_target (hball hu.1).1) (h0O u hu)
      rwa [(R.A.chart j).right_inv (hball hu.1).1] at this
    have hzero : ∀ u ∈ O, (brQ R Ψ' ∘ (R.A.chart j).symm) u m = 0 := by
      intro u hu
      simp only [Function.comp_apply, brQ]
      rw [hm, hΨ'app, Equiv.swap_apply_right]
      obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq R (hball hu.1).2 Ψ
      rw [hμeq, Pi.smul_apply, smul_eq_mul]
      have : f u = 0 := hall u hu.1
      simp only [hfdef] at this
      rw [this, mul_zero, zero_div]
    have hdetO : ∀ u ∈ O, LinearMap.det (fderiv ℂ (brQ R Ψ' ∘ (R.A.chart j).symm) u :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0 := by
      intro u hu
      have hcoord : (fun v => (brQ R Ψ' ∘ (R.A.chart j).symm) v m) =ᶠ[𝓝 u] fun _ => 0 := by
        filter_upwards [hO.mem_nhds hu] with v hv
        exact hzero v hv
      have hd : HasFDerivAt (fun v => (brQ R Ψ' ∘ (R.A.chart j).symm) v m)
          ((ContinuousLinearMap.proj m).comp (fderiv ℂ (brQ R Ψ' ∘ (R.A.chart j).symm) u)) u :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) m).hasFDerivAt.comp u
          (hanO u hu).differentiableAt.hasFDerivAt
      have hd0 : HasFDerivAt (fun v => (brQ R Ψ' ∘ (R.A.chart j).symm) v m)
          (0 : (Fin e → ℂ) →L[ℂ] ℂ) u :=
        (hasFDerivAt_const (0 : ℂ) u).congr_of_eventuallyEq hcoord
      have hrow := hd.unique hd0
      refine det_eq_zero_of_coord m fun v => ?_
      have := congrArg (fun T : (Fin e → ℂ) →L[ℂ] ℂ => T v) hrow
      simpa using this
    exact not_flat R Ψ' hP hΨ' j hO (fun u hu => (hball hu.1).1) ⟨u0, hu0O⟩ h0O hanO hdetO
  · rintro w ⟨⟨hwt, hw0⟩, hwb⟩
    obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq R (hball hwb).2 Ψ
    have := congrFun hμeq 0
    rw [Pi.smul_apply, smul_eq_mul] at this
    have hw0' : Ψ (segre (R.lift ((R.A.chart j).symm w) ((R.A.chart j).symm w))) 0 = 0 := hw0
    rw [hw0'] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hμ

end GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

def ShiftQuotientBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a b : K → ℤ) (c : ∀ k, ι k),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (∀ k, y ⟨k, c k⟩ ≠ 0) →
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + b) 1 ⧸ chartDivSec y c ((n : ℤ) • a + b)) : ℝ) ≤
        C * (n : ℝ) ^ (D - 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def BlockGraphFibreRatio.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (κ : Type) [Fintype κ] (y : (Σ k, ι k) → Ω) (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ)
    (N : Matrix (ι k₀) (Ix κ) ℤ) (x : Ix κ → Ω),
    IsArithVar (mCoordIdeal y) (D + 1) → BlockBirational y k₀ → IsBlockImage y k₀ M N x →
    ∀ (G : GenFibre (inrV (ι := ι) (ι₂ := GlobalTheory κ)) (graphIdeal (mCoordIdeal y) (blockForms k₀ M))) (k : K) (i j : ι k),
      G.x' ⟨Sum.inl k, j⟩ ≠ 0 → G.x' ⟨Sum.inl k, i⟩ / G.x' ⟨Sum.inl k, j⟩ ∈ (algebraMap G.Φ G.Φ').range

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
end
