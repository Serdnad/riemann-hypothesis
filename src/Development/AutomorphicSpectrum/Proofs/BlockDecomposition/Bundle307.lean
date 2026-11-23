module

public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Unimodular
import GroundTheory.AutomorphicForms.Bundle016
import GroundTheory.AutomorphicForms.Reduction
import GroundTheory.AutomorphicForms.ReductionFinite
public import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.GlobalFields.Adele.Topology
public import GroundTheory.GlobalFields.TateThesis.IdeleMeasureQuotient
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology Set
open GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing ENNReal Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.RSGlobal

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem exists_isHaarMeasure_isMulRightInvariant (hn : 0 < n) :
    ∃ μ : Measure (AdelicGLn.AdelicGL K n), μ.IsHaarMeasure ∧ μ.IsMulRightInvariant := by
  set Φ := glNormOneSplitting (K := K) hn with hΦ
  let ν : Measure (normOneGL (K := K) (n := n)) := Measure.haar
  let ρ : Measure {r : ℝ // 0 < r} := Measure.haar
  haveI : ν.IsMulRightInvariant := isMulRightInvariant_normOneGL ν
  let m : Measure (normOneGL (K := K) (n := n) × {r : ℝ // 0 < r}) := ν.prod ρ
  haveI : m.IsHaarMeasure := inferInstanceAs (ν.prod ρ).IsHaarMeasure
  haveI : m.IsMulRightInvariant := inferInstanceAs (ν.prod ρ).IsMulRightInvariant
  have hc : Measurable (Φ.symm : normOneGL (K := K) (n := n) × {r : ℝ // 0 < r} → AdelicGLn.AdelicGL K n) :=
    Φ.symm.continuous.measurable
  refine ⟨m.map Φ.symm, ContinuousMulEquiv.isHaarMeasure_map m Φ.symm, ⟨fun g => ?_⟩⟩
  rw [Measure.map_map (measurable_mul_const g) hc]
  have h : (· * g) ∘ (Φ.symm : normOneGL (K := K) (n := n) × {r : ℝ // 0 < r} → AdelicGLn.AdelicGL K n) =
      Φ.symm ∘ (· * Φ g) := by
    funext p
    simp only [Function.comp_apply, map_mul, ContinuousMulEquiv.symm_apply_apply]
  rw [h, ← Measure.map_map hc (measurable_mul_const (Φ g)), map_mul_right_eq_self]

theorem exists_measure_lt_top_slab (μ : Measure (AdelicGLn.AdelicGL K n)) [μ.IsHaarMeasure] :
    ∃ E : Set (AdelicGLn.AdelicGL K n), μ E < ⊤ ∧ ∀ g : AdelicGLn.AdelicGL K n,
      1 ≤ (ideleModule K (AdelicGLn.det K n g) : ℝ) → (ideleModule K (AdelicGLn.det K n g) : ℝ) ≤ Real.exp 1 →
        ∃ γ : GL (Fin n) K, AdelicGLn.diagonal K n γ * g ∈ E := by
  classical
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := exists_siegelSet (K := K) n
  choose c₁ c₂ hc₁ hbd using fun w => exists_norm_det_infAt_bounds (K := K) hω t w
  set S : ∀ w : InfinitePlace K, Set (GL (Fin n) w.Completion) :=
    fun w => localSiegel w (infAt w '' ω) t (c₁ w) (c₂ w) with hSdef
  have hS : ∀ w, (Measure.haar : Measure (GL (Fin n) w.Completion)) (S w) < ⊤ := fun w =>
    measure_localSiegel_lt_top w _ (hω.image (continuous_infAt w))
      (by rintro _ ⟨b, hb, rfl⟩; exact infAt_isUpperTriangular (hωB hb)) ht (hc₁ w)
  set p2 : AdelicGLn.AdelicGL K n → AdelicGLn.FiniteAdelicGL K n :=
    fun g => (AdelicGLn.prodEquiv K n g).2 with hp2
  have hp2c : Continuous p2 := continuous_snd.comp (AdelicGLn.prodEquiv K n).continuous
  set F : Set (AdelicGLn.FiniteAdelicGL K n) :=
    (p2 '' ω) * (p2 '' (maxCompact (K := K) (n := n) : Set (AdelicGLn.AdelicGL K n))) with hFdef
  have hF : IsCompact F := (hω.image hp2c).mul (isCompact_maxCompact.image hp2c)
  set E : Set (AdelicGLn.AdelicGL K n) := {g | g ∈ siegelSet n ω t ∧
    1 ≤ (ideleModule K (AdelicGLn.det K n g) : ℝ) ∧
      (ideleModule K (AdelicGLn.det K n g) : ℝ) ≤ Real.exp 1} with hEdef
  have hE : μ E < ⊤ := by
    refine measure_lt_top_of_forall_mem μ S hS hF fun g hg => ⟨fun w => ?_, ?_⟩
    · obtain ⟨hgs, h1, h2⟩ := hg
      have hb := hbd w g hgs h1 h2
      obtain ⟨b, hbω, _, ⟨r, hr, hratio, rfl⟩, k, hk, rfl⟩ := hgs
      refine ⟨hb.1, hb.2, infAt w b, ⟨b, hbω, rfl⟩, r, hr, hratio, infAt w k, hk.1 w, ?_⟩
      rw [infAt_mul, infAt_mul, infAt_diagUnits_posIdele w r hr]
    · obtain ⟨⟨b, hbω, _, ⟨r, hr, -, rfl⟩, k, hk, rfl⟩, -, -⟩ := hg
      refine ⟨p2 b, ⟨b, hbω, rfl⟩, p2 k, ⟨k, hk, rfl⟩, ?_⟩
      simp only [hp2, map_mul, Prod.snd_mul, prodEquiv_diagUnits_posIdele_snd r hr, mul_one]
  refine ⟨E, hE, fun g h1 h2 => ?_⟩
  obtain ⟨γ, hγ⟩ := hsieg g
  have hmod : (ideleModule K (AdelicGLn.det K n (AdelicGLn.diagonal K n γ * g)) : ℝ) =
      (ideleModule K (AdelicGLn.det K n g) : ℝ) := by
    have h0 : (ideleModule K (AdelicGLn.det K n (AdelicGLn.diagonal K n γ)) : ℝ) = 1 :=
      mem_normOneGL.1 (rationalGL_le_normOneGL ⟨γ, rfl⟩)
    rw [map_mul, map_mul, Positive.val_mul, h0, one_mul]
  exact ⟨γ, hγ, hmod ▸ h1, hmod ▸ h2⟩

instance countable_GL_rat : Countable (GL (Fin 2) ℚ) :=
  Function.Injective.countable
    (f := fun g : GL (Fin 2) ℚ => (fun i j => (g : Matrix (Fin 2) (Fin 2) ℚ) i j : Fin 2 → Fin 2 → ℚ))
    fun _ _ h => Units.ext (by ext i j; exact congrFun (congrFun h i) j)

theorem measure_inter_band_lt_top (μ : Measure Ad3.R.G2) [μ.IsHaarMeasure] {𝓕 : Set Ad3.R.G2}
    (hF : IsFundamentalDomain (AdelicGLn.diagonal ℚ 2).range 𝓕 μ) : μ (𝓕 ∩ Ad3.R.band) < ⊤ := by
  obtain ⟨E, hE, hcov⟩ := exists_measure_lt_top_slab (K := ℚ) (n := 2) μ
  haveI : Countable (AdelicGLn.diagonal ℚ 2).range :=
    Function.Surjective.countable (AdelicGLn.diagonal ℚ 2).rangeRestrict_surjective
  refine lt_of_le_of_lt ?_ hE
  calc μ (𝓕 ∩ Ad3.R.band) ≤ μ (⋃ γ : (AdelicGLn.diagonal ℚ 2).range, γ • E ∩ 𝓕) := by
        refine measure_mono fun x hx => ?_
        have h2 : (2 : ℝ) ≤ Real.exp 1 := by
          have := Real.exp_one_gt_d9
          linarith
        obtain ⟨γ, hγ⟩ := hcov x hx.2.1 (hx.2.2.le.trans h2)
        refine mem_iUnion.2 ⟨⟨AdelicGLn.diagonal ℚ 2 γ, ⟨γ, rfl⟩⟩⁻¹, ?_, hx.1⟩
        rw [Set.mem_inv_smul_set_iff]
        exact hγ
    _ ≤ ∑' γ : (AdelicGLn.diagonal ℚ 2).range, μ (γ • E ∩ 𝓕) := measure_iUnion_le _
    _ = μ E := by
      set_option synthInstance.maxHeartbeats 200000 in
        exact (hF.measure_eq_tsum E).symm

theorem exists_probability_haar :
    ∃ m : Measure Ad3.R.KA, m.IsHaarMeasure ∧ IsProbabilityMeasure m := by
  haveI : CompactSpace Ad3.R.KA := isCompact_iff_compactSpace.1 isCompact_maxCompact
  haveI : WeaklyLocallyCompactSpace Ad3.R.KA := by
    set_option synthInstance.maxHeartbeats 200000 in
      exact inferInstance
  let K₀ : TopologicalSpace.PositiveCompacts Ad3.R.KA := ⊤
  set_option synthInstance.maxHeartbeats 200000 in
    refine ⟨Measure.haarMeasure K₀, inferInstance, ⟨?_⟩⟩
  have h := by
    set_option synthInstance.maxHeartbeats 200000 in
      exact Measure.haarMeasure_self (K₀ := K₀)
  simpa [K₀] using h

theorem setup_of_ideleDomain : Ad3.R.D0 → Ad3.R.G0 := by
  rintro ⟨𝓓, h1, h2, h3⟩
  obtain ⟨μ, hμ, hr⟩ := exists_isHaarMeasure_isMulRightInvariant (K := ℚ) (n := 2) (by norm_num)
  obtain ⟨mK, hK, hP⟩ := exists_probability_haar
  haveI : DiscreteTopology (AdelicGLn.rationalGL ℚ 2) := AdelicGLn.discreteTopology_rationalGL ℚ 2
  have hF : IsFundamentalDomain (AdelicGLn.diagonal ℚ 2).range
      (RightCosetSpace.fundamentalDomain (AdelicGLn.rationalGL ℚ 2)) μ :=
    RightCosetSpace.isFundamentalDomain_fundamentalDomain (AdelicGLn.rationalGL ℚ 2) μ
  exact ⟨μ, _, mK, 𝓓, ⟨hμ, hr, hF, RightCosetSpace.measurableSet_fundamentalDomain _,
    measure_inter_band_lt_top μ hF, hK, hP, h1, h2, h3⟩⟩

end GlobalTheory.CompanionTheory.RSGlobal

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical

namespace GlobalTheory.CompanionTheory.FundamentalDomainCentralCharacter
open Ad3.R Ad3

theorem countable_range : Countable (AdelicGLn.diagonal ℚ 2).range := by
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℚ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℚ))
  haveI : Countable (GL (Fin 2) ℚ) := Function.Injective.countable (f := fun u : GL (Fin 2) ℚ => (u.val, u.inv)) (fun a b h => Units.ext (congrArg Prod.fst h))
  exact (Set.countable_range (AdelicGLn.diagonal ℚ 2)).to_subtype

theorem md_pos (a : Jd) : 0 < md a := (IdeleGroup.ideleModule ℚ a).2
theorem md_mul (a b : Jd) : md (a * b) = md a * md b := by
  simp [md, map_mul]
theorem md_one : md 1 = 1 := by simp [md]
theorem continuous_md : Continuous md := continuous_subtype_val.comp IdeleGroup.continuous_ideleModule
theorem continuous_Dt : Continuous Dt := continuous_md.comp (AdelicGLn.continuous_det ℚ 2)
theorem Dt_pos (g : G2) : 0 < Dt g := md_pos _
theorem Dt_mul (g h : G2) : Dt (g * h) = Dt g * Dt h := by
  simp [Dt, map_mul, md_mul]
theorem Dt_inv (g : G2) : Dt g⁻¹ = (Dt g)⁻¹ := by
  have := Dt_mul g g⁻¹
  have h1 : Dt (1 : G2) = 1 := by simp [Dt, md_one]
  rw [mul_inv_cancel, h1] at this
  exact eq_inv_of_mul_eq_one_right this.symm
theorem Dt_dia (γ : GL (Fin 2) ℚ) : Dt (dia2 γ) = 1 := by
  have := Reduction.rationalGL_le_normOneGL (K := ℚ) (n := 2) ⟨γ, rfl⟩
  rw [Reduction.mem_normOneGL] at this
  exact this
theorem Dt_central (z : Jd) : Dt (dg2 z z) = md z ^ 2 := by
  have : GeneralLinearGroup.det (dg2 z z) = z * z := by
    ext
    simp [dg2, Matrix.det_fin_two]
  rw [Dt, this, md_mul, sq]

theorem exists_ne_one {η : HeckeCharacter ℚ} (h : η ≠ 1) : ∃ z : Jd, η.toIdele z ≠ 1 := by
  by_contra hc
  push_neg at hc
  apply h
  ext x
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective x
  have := hc z
  rw [HeckeCharacter.toIdele_apply] at this
  show ((η (IdeleClassGroup.mk ℚ z) : Circle) : ℂ) = ((1 : Circle) : ℂ)
  rw [this]

open scoped Pointwise

theorem measurableSet_band : MeasurableSet band := by
  have : band = Dt ⁻¹' Set.Ico 1 2 := by
    ext g; simp [band]
  rw [this]
  exact continuous_Dt.measurable measurableSet_Ico

theorem mem_band_dia {γ : GL (Fin 2) ℚ} {g : G2} : dia2 γ * g ∈ band ↔ g ∈ band := by
  simp [band, Dt_mul, Dt_dia]

theorem fundamental_domain_integral_central_vanishing : Ad3.R.G1a → Ad3.R.G1 := by
  intro hA μ 𝓕 mK 𝓓 hS F hF hB hL
  haveI := hS.haar
  haveI := hS.right
  obtain ⟨-, hz, hT⟩ := hA μ 𝓕 mK 𝓓 hS
  have hbM := measurableSet_band
  have Fm : Measurable F := hF.measurable
  have hIndL : LInv (band.indicator F) := by
    intro γ g
    by_cases hg : g ∈ band
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (mem_band_dia.2 hg), hL]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (mem_band_dia.1 h))]
  have hIndM : Measurable (band.indicator F) := Fm.indicator hbM
  have hI : ∀ f : G2 → ℂ, ∫ g in 𝓕 ∩ band, f g ∂μ = ∫ g in 𝓕, band.indicator f g ∂μ :=
    fun f => (setIntegral_indicator hbM).symm
  refine ⟨?_, ?_, ?_⟩
  · intro hC h
    obtain ⟨z, hz1, -⟩ := hz (Dt h)⁻¹ (inv_pos.2 (Dt_pos h))
    set Bh : Set G2 := {g | g * h⁻¹ ∈ band} with hBh
    have hBhM : MeasurableSet Bh :=
      hbM.preimage (continuous_id.mul continuous_const).measurable
    have hBhL : LInv (Bh.indicator F) := by
      intro γ g
      have hm : dia2 γ * g ∈ Bh ↔ g ∈ Bh := by
        simp only [hBh, Set.mem_setOf_eq, mul_assoc, mem_band_dia]
      by_cases hg : g ∈ Bh
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hm.2 hg), hL]
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hm.1 h))]
    have e1 : ∀ g, Bh.indicator F (g * h) = band.indicator (fun g => F (g * h)) g := by
      intro g
      have hm : g * h ∈ Bh ↔ g ∈ band := by simp [hBh]
      by_cases hg : g ∈ band
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hm.2 hg)]
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hm.1 h))]
    have e2 : ∀ g, band.indicator F (dg2 z z * g) = Bh.indicator F g := by
      intro g
      have hm : dg2 z z * g ∈ band ↔ g ∈ Bh := by
        have : Dt (dg2 z z * g) = Dt (g * h⁻¹) := by
          rw [Dt_mul, Dt_mul, Dt_central, hz1, Dt_inv, mul_comm]
        simp only [hBh, Set.mem_setOf_eq, band, this]
      by_cases hg : g ∈ Bh
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hm.2 hg), hC]
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hm.1 h))]
    rw [hI, hI]
    simp_rw [← e1]
    rw [(hT (fun g => g * h) (Or.inr (Or.inl ⟨h, rfl⟩))).2 _ (Fm.indicator hBhM) hBhL]
    simp_rw [← e2]
    exact (hT (fun g => dg2 z z * g) (Or.inr (Or.inr ⟨z, rfl⟩))).2 _ hIndM hIndL
  · intro η hη hc hne
    obtain ⟨z0, h0⟩ := exists_ne_one hne
    obtain ⟨z1, hz1, hz1'⟩ := hz ((md z0) ^ 2)⁻¹ (inv_pos.2 (pow_pos (md_pos _) 2))
    set z : Jd := z0 * z1 with hzdef
    have hmd : md z ^ 2 = 1 := by
      rw [hzdef, md_mul, mul_pow, hz1]
      exact mul_inv_cancel₀ (pow_pos (md_pos _) 2).ne'
    have hηz : η.toIdele z ≠ 1 := by
      rw [hzdef, map_mul, hz1' η hη, mul_one]
      exact h0
    have hηz' : (η.toIdele z : ℂ) ≠ 1 := fun h => hηz (Circle.ext (by simpa using h))
    have e : ∀ g, band.indicator F (dg2 z z * g) = (η.toIdele z : ℂ) * band.indicator F g := by
      intro g
      have hm : dg2 z z * g ∈ band ↔ g ∈ band := by
        have : Dt (dg2 z z * g) = Dt g := by rw [Dt_mul, Dt_central, hmd, one_mul]
        simp only [band, Set.mem_setOf_eq, this]
      by_cases hg : g ∈ band
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hm.2 hg), hc]
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hm.1 h)), mul_zero]
    have key := (hT (fun g => dg2 z z * g) (Or.inr (Or.inr ⟨z, rfl⟩))).2 _ hIndM hIndL
    simp_rw [e] at key
    rw [integral_const_mul] at key
    rw [hI]
    have : ((η.toIdele z : ℂ) - 1) * ∫ g in 𝓕, band.indicator F g ∂μ = 0 := by
      rw [sub_mul, one_mul, key, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hηz')
  · intro hC hne hI0
    apply hne
    have hn : ∀ g, F g * conj (F g) = ((Complex.normSq (F g) : ℝ) : ℂ) := fun g => Complex.mul_conj _
    simp_rw [hn] at hI0
    rw [integral_complex_ofReal] at hI0
    have hI1 : ∫ g in 𝓕 ∩ band, Complex.normSq (F g) ∂μ = 0 := by exact_mod_cast hI0
    obtain ⟨C, hCb⟩ := hB
    have hmeas : MeasurableSet (𝓕 ∩ band) := hS.meas.inter hbM
    have hint : IntegrableOn (fun g => Complex.normSq (F g)) (𝓕 ∩ band) μ := by
      refine Measure.integrableOn_of_bounded (M := C ^ 2) hS.vol.ne
        (Complex.continuous_normSq.comp hF).aestronglyMeasurable ?_
      refine Eventually.of_forall fun g => ?_
      rw [Real.norm_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) (hCb g) 2
    have hae := (setIntegral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun g => Complex.normSq_nonneg (F g)) hint).1 hI1
    set t : Set G2 := band ∩ {g | F g ≠ 0} with ht
    have h0 : μ (t ∩ 𝓕) = 0 := by
      have h1 := (ae_iff.1 ((ae_restrict_iff' hmeas).1 hae))
      refine measure_mono_null ?_ h1
      rintro g ⟨⟨hb, hf⟩, hg⟩
      simp only [Set.mem_setOf_eq, not_forall]
      exact ⟨⟨hg, hb⟩, by simpa using hf⟩
    have hinv : ∀ γ ∈ (AdelicGLn.diagonal ℚ 2).range, ∀ x : G2, γ * x ∈ t ↔ x ∈ t := by
      rintro _ ⟨δ, rfl⟩ x
      have e1 := hL δ x
      simp only [ht, Set.mem_inter_iff, Set.mem_setOf_eq]
      rw [show AdelicGLn.diagonal ℚ 2 δ * x = dia2 δ * x from rfl, mem_band_dia, e1]
    have hts : ∀ γ : (AdelicGLn.diagonal ℚ 2).range, γ • t = t := by
      intro γ
      ext x
      rw [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, smul_eq_mul]
      exact hinv _ (γ⁻¹).2 x
    haveI := countable_range
    set_option synthInstance.maxHeartbeats 200000 in
    have hμt : μ t = 0 := hS.fd.measure_zero_of_invariant t hts h0
    set U : Set G2 := {g | 1 < Dt g ∧ Dt g < 2 ∧ F g ≠ 0} with hU
    have hUo : IsOpen U := by
      refine (isOpen_lt continuous_const continuous_Dt).inter
        ((isOpen_lt continuous_Dt continuous_const).inter (isOpen_ne_fun hF continuous_const))
    have hU0 : U = ∅ := hUo.eq_empty_of_measure_zero
      (measure_mono_null (show U ⊆ t from fun g hg => ⟨⟨hg.1.le, hg.2.1⟩, hg.2.2⟩) hμt)
    funext g
    by_contra hg
    obtain ⟨z, hz1, -⟩ := hz (3 / 2 / Dt g) (div_pos (by norm_num) (Dt_pos g))
    have hD : Dt (dg2 z z * g) = 3 / 2 := by
      rw [Dt_mul, Dt_central, hz1, div_mul_cancel₀ _ (Dt_pos g).ne']
    have hmem : dg2 z z * g ∈ U := by
      refine ⟨by rw [hD]; norm_num, by rw [hD]; norm_num, ?_⟩
      rw [hC]
      exact hg
    rw [hU0] at hmem
    exact hmem

end GlobalTheory.CompanionTheory.FundamentalDomainCentralCharacter
end
end

section

open NumberField MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain

open Ad3.R

theorem pri_eq_diagonal (α : ℚˣ) : pri α = diagonal ℚ α := rfl

theorem md_eq (a : Jd) : md a = (ideleModule ℚ a : ℝ) := rfl

theorem lintegral_posReal_weight_lt_top (τ : ℝ) (M : ℕ) (h0 : 0 < τ) (h1 : τ < M) :
    ∫⁻ t : {r : ℝ // 0 < r}, ENNReal.ofReal (min 1 (t : ℝ)⁻¹ ^ M * (t : ℝ) ^ τ) ∂posRealMeasure < ∞ := by
  have hF : Measurable (fun t : {r : ℝ // 0 < r} => ENNReal.ofReal (min 1 (t : ℝ)⁻¹ ^ M * (t : ℝ) ^ τ)) := by
    fun_prop
  rw [posRealMeasure_eq_map_expPos, lintegral_map hF measurable_expPos]
  simp only [coe_expPos]
  rw [← lintegral_add_compl _ (measurableSet_Iic (a := (0 : ℝ))), Set.compl_Iic]
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · refine (setLIntegral_mono (g := fun x => ENNReal.ofReal (Real.exp (τ * x))) (by fun_prop)
      fun x hx => ?_).trans_lt ?_
    · apply ENNReal.ofReal_le_ofReal
      have hm : min 1 (Real.exp x)⁻¹ ^ M ≤ 1 :=
        pow_le_one₀ (le_min zero_le_one (inv_nonneg.2 (Real.exp_pos x).le)) (min_le_left _ _)
      calc min 1 (Real.exp x)⁻¹ ^ M * Real.exp x ^ τ ≤ 1 * Real.exp x ^ τ :=
            mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg (Real.exp_pos x).le _)
        _ = Real.exp (τ * x) := by rw [one_mul, mul_comm, Real.exp_mul]
    · exact Integrable.lintegral_lt_top (integrableOn_exp_mul_Iic h0 0)
  · refine (setLIntegral_mono (g := fun x => ENNReal.ofReal (Real.exp (-((M : ℝ) - τ) * x))) (by fun_prop)
      fun x hx => ?_).trans_lt ?_
    · apply ENNReal.ofReal_le_ofReal
      have hm : min 1 (Real.exp x)⁻¹ ^ M ≤ (Real.exp x)⁻¹ ^ M :=
        pow_le_pow_left₀ (le_min zero_le_one (inv_nonneg.2 (Real.exp_pos x).le)) (min_le_right _ _) M
      calc min 1 (Real.exp x)⁻¹ ^ M * Real.exp x ^ τ ≤ (Real.exp x)⁻¹ ^ M * Real.exp x ^ τ :=
            mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg (Real.exp_pos x).le _)
        _ = Real.exp (-((M : ℝ) - τ) * x) := by
          rw [← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_add]
          congr 1
          ring
    · exact Integrable.lintegral_lt_top (exp_neg_integrableOn_Ioi 0 (sub_pos.2 h1))

def fundD (w : InfinitePlace ℚ) : Set Jd :=
  (fun a => (normOneSplitting w a).1) ⁻¹' normOneFundamentalDomain ℚ

theorem measurableSet_fundD (w : InfinitePlace ℚ) : MeasurableSet (fundD w) := by
  exact (measurableSet_normOneFundamentalDomain ℚ).preimage (measurePreserving_normOneSplitting w).measurable.fst

theorem split_pri_mul (w : InfinitePlace ℚ) (α : ℚˣ) (a : Jd) :
    (normOneSplitting w (pri α * a)).1 = (normOneSplitting w a).1 * diagonalToNormOne ℚ α := by
  have hp : pri α = (normOneSplitting w).symm (diagonalToNormOne ℚ α, 1) := by
    simp only [normOneSplitting_symm_apply, map_one, mul_one, coe_diagonalToNormOne, pri_eq_diagonal]
  have key : normOneSplitting w (pri α) = (diagonalToNormOne ℚ α, 1) := by
    rw [hp]
    exact (normOneSplitting w).apply_symm_apply _
  rw [map_mul, Prod.fst_mul, key]
  exact mul_comm _ _

theorem existsUnique_pri_mul_mem (w : InfinitePlace ℚ) (a : Jd) :
    ∃! α : ℚˣ, pri α * a ∈ fundD w := by
  have h : ∀ α : ℚˣ, pri α * a ∈ fundD w ↔
      (normOneSplitting w a).1 * diagonalToNormOne ℚ α ∈ normOneFundamentalDomain ℚ := by
    intro α
    show (normOneSplitting w (pri α * a)).1 ∈ normOneFundamentalDomain ℚ ↔ _
    rw [split_pri_mul]
  exact (existsUnique_congr h).2 (existsUnique_mul_mem_normOneFundamentalDomain ℚ _)

theorem lintegral_fundD_lt_top (w : InfinitePlace ℚ) (τ : ℝ) (M : ℕ) (h0 : 0 < τ) (h1 : τ < M) :
    ∫⁻ a in fundD w, ENNReal.ofReal (min 1 (md a)⁻¹ ^ M * md a ^ τ) ∂ideleMeasure ℚ < ∞ := by
  have hφm : Measurable (fun t : {r : ℝ // 0 < r} => ENNReal.ofReal (min 1 (t : ℝ)⁻¹ ^ M * (t : ℝ) ^ τ)) := by
    fun_prop
  have hIm : Measurable ((normOneFundamentalDomain ℚ).indicator (1 : normOneSubgroup ℚ → ℝ≥0∞)) :=
    measurable_one.indicator (measurableSet_normOneFundamentalDomain ℚ)
  have hpt : ∀ a : Jd, (fundD w).indicator (fun a => ENNReal.ofReal (min 1 (md a)⁻¹ ^ M * md a ^ τ)) a =
      (fun p : normOneSubgroup ℚ × {r : ℝ // 0 < r} => (normOneFundamentalDomain ℚ).indicator 1 p.1 *
        ENNReal.ofReal (min 1 (p.2 : ℝ)⁻¹ ^ M * (p.2 : ℝ) ^ τ)) (normOneSplitting w a) := by
    intro a
    by_cases ha : a ∈ fundD w
    · have ha' : (normOneSplitting w a).1 ∈ normOneFundamentalDomain ℚ := ha
      simp [Set.indicator_of_mem ha, Set.indicator_of_mem ha', normOneSplitting_apply_snd, md_eq]
    · have ha' : (normOneSplitting w a).1 ∉ normOneFundamentalDomain ℚ := ha
      simp [ha, ha']
  rw [← lintegral_indicator (measurableSet_fundD w), lintegral_congr hpt,
    (measurePreserving_normOneSplitting w).lintegral_comp
      (f := fun p : normOneSubgroup ℚ × {r : ℝ // 0 < r} => (normOneFundamentalDomain ℚ).indicator 1 p.1 *
        ENNReal.ofReal (min 1 (p.2 : ℝ)⁻¹ ^ M * (p.2 : ℝ) ^ τ))
      ((hIm.comp measurable_fst).mul (hφm.comp measurable_snd)),
    lintegral_prod_mul hIm.aemeasurable hφm.aemeasurable, lintegral_indicator_one (measurableSet_normOneFundamentalDomain ℚ)]
  exact ENNReal.mul_lt_top (normOneMeasure_normOneFundamentalDomain_lt_top ℚ)
    (lintegral_posReal_weight_lt_top τ M h0 h1)

theorem exists_idele_fundamentalDomain : Ad3.R.D0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace ℚ) := inferInstance
  unfold Ad3.R.D0
  exact ⟨fundD w, measurableSet_fundD w, existsUnique_pri_mul_mem w,
    fun τ M h0 h1 => lintegral_fundD_lt_top w τ M h0 h1⟩

end GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain

end
end
