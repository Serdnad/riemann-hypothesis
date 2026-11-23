module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.InfEmbGrpEq
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.Poisson
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.Bundle001

@[expose] public section

section

open UpperTheory.V.Lit.Geo

private theorem moment_pt (k : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (1 + x) ^ k * Real.exp (-Real.pi * x) ≤
      (k.factorial * Real.exp 1) * Real.exp (-Real.pi * (1 / 2 * x)) := by
  have h1 : (1 + x) ^ k / (k.factorial : ℝ) ≤ Real.exp (1 + x) :=
    Real.pow_div_factorial_le_exp (1 + x) (by linarith) k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have h2 : (1 + x) ^ k ≤ k.factorial * Real.exp (1 + x) := by
    rw [div_le_iff₀ hf] at h1
    linarith
  calc (1 + x) ^ k * Real.exp (-Real.pi * x)
      ≤ k.factorial * Real.exp (1 + x) * Real.exp (-Real.pi * x) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = (k.factorial * Real.exp 1) * Real.exp (x + -Real.pi * x) := by
        rw [Real.exp_add, Real.exp_add]
        ring
    _ ≤ (k.factorial * Real.exp 1) * Real.exp (-Real.pi * (1 / 2 * x)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.2
        nlinarith [Real.pi_gt_three]

theorem UpperTheory.moment_bound_of_pointwise_moments :
    Moment := by
  intro N k
  refine ⟨k.factorial * Real.exp 1 * 2 ^ N, by positivity, fun ι q hq => ?_⟩
  obtain ⟨hs1, hle⟩ := hq.2 (1 / 2) 1 (by norm_num) (by norm_num)
  have hnn : ∀ i, 0 ≤ (1 + q i) ^ k * Real.exp (-Real.pi * q i) := fun i => by
    have := hq.1 i
    positivity
  have hpt : ∀ i, (1 + q i) ^ k * Real.exp (-Real.pi * q i) ≤
      (k.factorial * Real.exp 1) * Real.exp (-Real.pi * (1 / 2 * q i)) := fun i => moment_pt k (q i) (hq.1 i)
  have hsum : Summable fun i => (1 + q i) ^ k * Real.exp (-Real.pi * q i) :=
    Summable.of_nonneg_of_le hnn hpt (hs1.mul_left _)
  refine ⟨hsum, ?_⟩
  calc ∑' i, (1 + q i) ^ k * Real.exp (-Real.pi * q i)
      ≤ ∑' i, (k.factorial * Real.exp 1) * Real.exp (-Real.pi * (1 / 2 * q i)) :=
        hsum.tsum_le_tsum hpt (hs1.mul_left _)
    _ = (k.factorial * Real.exp 1) * ∑' i, Real.exp (-Real.pi * (1 / 2 * q i)) := tsum_mul_left
    _ ≤ (k.factorial * Real.exp 1) * ((1 / (1 / 2)) ^ N * ∑' i, Real.exp (-Real.pi * (1 * q i))) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = k.factorial * Real.exp 1 * 2 ^ N * ∑' i, Real.exp (-Real.pi * q i) := by
        rw [show (1 : ℝ) / (1 / 2) = 2 by norm_num]
        simp only [one_mul]
        ring
end

section

open UpperTheory.V.Lit.Geo

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem mult_two (w : InfinitePlace E) : w.mult = 2 := by
  simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)]

private theorem rank_eq : (Module.finrank ℚ E : ℝ) = 2 * Fintype.card (InfinitePlace E) := by
  rw [← InfinitePlace.sum_mult_eq]
  simp [mult_two, mul_comm]

private theorem mod_inf (h : GL (Fin a) (Cinf E)) :
    (Reduction.detModule E a (infGL E a h) : ℝ) = ∏ w : InfinitePlace E, ‖h.val.det w‖ ^ 2 := by
  have e1 : pInf E (infGL E a h).val.det = h.val.det := by
    rw [RingHom.map_det]
    exact congrArg (fun y : GL (Fin a) (Cinf E) => y.val.det) (pInf_infGL h)
  have e2 : pFin E (infGL E a h).val.det = 1 := by
    rw [RingHom.map_det]
    exact (congrArg (fun y : GL (Fin a) (Af E) => y.val.det) (pFin_infGL h)).trans Matrix.det_one
  have h1 : ∀ v : InfinitePlace E, ‖((infGL E a h).val.det : Ad E).1 v‖ = ‖h.val.det v‖ := fun v => by
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _)]
    exact congrArg norm (congrFun e1 v)
  have h2 : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ‖((infGL E a h).val.det : Ad E).2 v‖ = 1 := fun v => by
    change ‖pFin E (infGL E a h).val.det v‖ = 1
    rw [e2]
    exact norm_one
  change (IdeleGroup.ideleModule E (AdelicGLn.det E a (infGL E a h)) : ℝ) = _
  rw [IdeleGroup.ideleModule_eq]
  change (∏ v : InfinitePlace E, ‖((infGL E a h).val.det : Ad E).1 v‖ ^ v.mult) *
    ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ‖((infGL E a h).val.det : Ad E).2 v‖ = _
  simp only [h1, h2, finprod_one, mul_one, mult_two]

private theorem sect_inv (ha : 1 ≤ a) (h : GL (Fin a) (Cinf E)) :
    (Reduction.centralSection E a (Reduction.detModule E a (infGL E a h)))⁻¹ =
      splitCentre E a (Real.log (sc h.val)) := by
  rw [UpperTheory.V.KernelIndexFullLattice.splitEq_holds E a, ← map_inv (Reduction.centralSection E a)]
  refine congrArg _ (Subtype.ext ?_)
  have hne : ∀ w : InfinitePlace E, ‖h.val.det w‖ ≠ 0 := fun w =>
    norm_ne_zero_iff.2 (((Matrix.isUnit_iff_isUnit_det _).1 h.isUnit).map (Pi.evalRingHom _ w)).ne_zero
  have h1 : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h2 : (Fintype.card (InfinitePlace E) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hp := (Reduction.detModule E a (infGL E a h)).2
  change (Reduction.detModule E a (infGL E a h) : ℝ)⁻¹ = Real.exp _
  rw [← Real.exp_log hp, ← Real.exp_neg, mod_inf, Real.log_prod fun w _ => pow_ne_zero _ (hne w), sc,
    Real.log_exp, rank_eq]
  congr 1
  simp only [Real.log_pow, ← Finset.mul_sum]
  field_simp
  push_cast
  ring

private theorem pInf_split (t : ℝ) (x : Fin a → Cinf E) :
    x ᵥ* (GeneralLinearGroup.map (pInf E) (splitCentre E a t)).val = Real.exp t • x := by
  rw [splitCentre, pInf_infGL]
  change x ᵥ* Matrix.diagonal (fun _ => (fun _ : InfinitePlace E => Complex.exp (t : ℂ))) = _
  ext i w
  rw [Matrix.vecMul_diagonal]
  simp [mul_comm]

end

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum in
theorem UpperTheory.cmDatum_infinitePlaces_complex_split :
    RtInf := by
  intro E _ _ _ a ha g h v
  have e : rt (g * infGL E a h) = rt g * infGL E a h * splitCentre E a (Real.log (sc h.val)) := by
    rw [← sect_inv ha h, UpperTheory.V.Lit.Geo.rt, UpperTheory.V.Lit.Geo.rt, coe_retractOne, coe_retractOne, map_mul, map_mul, _root_.mul_inv_rev,
      mul_assoc g _⁻¹, ← map_inv (Reduction.centralSection E a) (Reduction.detModule E a g),
      Reduction.centralSection_mul_comm, ← Reduction.centralSection_mul_comm _ _⁻¹]
    simp only [mul_assoc]
  rw [e]
  change vInf v ᵥ* _ = sc h.val • ((vInf v ᵥ* _) ᵥ* _)
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, pInf_split,
    pInf_infGL, Real.exp_log (show 0 < sc h.val from Real.exp_pos _)]
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.V UpperTheory.V.Lit.Geo

section

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem hom_one {G : Type} [Group G] [TopologicalSpace G] (U : Subgroup G) (hU : IsCompact (U : Set G))
    (φ : G →* {r : ℝ // 0 < r}) (hc : Continuous φ) : ∀ u ∈ U, φ u = 1 := by
  obtain ⟨m, hmU, hmax⟩ := hU.exists_isMaxOn ⟨1, U.one_mem⟩ hc.continuousOn
  have hle : ∀ u ∈ U, φ u ≤ 1 := fun u hu => by
    have h : φ (u * m) ≤ φ m := hmax (U.mul_mem hu hmU)
    rw [map_mul, mul_comm] at h
    exact (mul_le_iff_le_one_right' _).1 h
  intro u hu
  have h2 := hle _ (U.inv_mem hu)
  rw [map_inv, inv_le_one'] at h2
  exact le_antisymm (hle u hu) h2

private theorem ptF_rat (γ : GL (Fin a) E) (g : GA E a) (v : Fin a → E) :
    ptF (ratGL E a γ * g) v = ptF g (v ᵥ* γ.val) := by
  have h : vFin (v ᵥ* γ.val) = vFin v ᵥ* (GeneralLinearGroup.map (pFin E) (ratGL E a γ)).val :=
    funext fun j => RingHom.map_vecMul (algebraMap E (Af E)) γ.val v j
  change vFin v ᵥ* _ = vFin (v ᵥ* γ.val) ᵥ* _
  rw [h, map_mul, Units.val_mul, Matrix.vecMul_vecMul]

variable [_root_.NumberField.IsTotallyComplex E]

private theorem pt_rat (γ : GL (Fin a) E) (g : GA E a) (v : Fin a → E) :
    pt (ratGL E a γ * g) v = pt g (v ᵥ* γ.val) := by
  have h : vInf (v ᵥ* γ.val) = vInf v ᵥ* (GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val :=
    funext fun j => RingHom.map_vecMul ((pInf E).comp (algebraMap E (Ad E))) γ.val v j
  change vInf v ᵥ* _ = vInf (v ᵥ* γ.val) ᵥ* _
  rw [h, map_mul, Units.val_mul, Matrix.vecMul_vecMul]

private theorem rt_left (γ : GL (Fin a) E) (t : ℝ) (g : GA E a) :
    rt (ratGL E a γ * splitCentre E a t * g) = ratGL E a γ * rt g := by
  let y : KernelIndexFullLattice.G1 E a := ⟨ratGL E a γ, Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩⟩
  change (retractOne ((y : GA E a) * splitCentre E a t * g) : KernelIndexFullLattice.G1 E a).1 = _
  rw [mul_assoc, retractOne_coe_mul, retractOne_mul, KernelIndexFullLattice.splitEq_holds E a t, retractOne_centralSection, one_mul]
  rfl

private theorem retract_rt (g : GA E a) : retractOne (rt g) = retractOne g := retractOne_coe _

private theorem ptF_rt (g : GA E a) : ptF (rt g) = ptF g := by
  have h : GeneralLinearGroup.map (pFin E) (rt g) = GeneralLinearGroup.map (pFin E) g := finPart_retract g
  refine AddMonoidHom.ext fun v => ?_
  change vFin v ᵥ* _ = vFin v ᵥ* _
  rw [h]

private theorem rt_fin (U : Subgroup (GL (Fin a) (Af E))) (hU : IsCompact (U : Set (GL (Fin a) (Af E))))
    (u : GL (Fin a) (Af E)) (hu : u ∈ U) (g : GA E a) : rt (g * finGL E a u) = rt g * finGL E a u := by
  have h1 : Reduction.detModule E a (finGL E a u) = 1 := by
    rw [← Fb.finEmb_eq]
    exact hom_one U hU ((Reduction.detModule E a).comp (finEmb E a))
      (Reduction.continuous_detModule.comp continuous_finEmb) u hu
  unfold Lit.Geo.rt
  rw [coe_retractOne, coe_retractOne, map_mul, h1, mul_one, mul_assoc, ← centralSection_inv_mul_comm, ← mul_assoc]

end

theorem UpperTheory.rationalPoint_retraction_exists_cmDatum :
    RtFacts := by
  intro E _ _ _ a _
  refine ⟨rt_left, fun g => ⟨congrArg Subtype.val (retract_rt g), ?_, ptF_rt g⟩,
    fun γ g v => ⟨ptF_rat γ g v, pt_rat γ g v⟩, rt_fin⟩
  unfold qht
  rw [retract_rt]
end

section

open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr

theorem UpperTheory.unitarySimilitudeGroup_isSmooth_cmDatum :
    RootEx := by
  intro E _ _ a
  obtain ⟨τ, -, hτ⟩ := locSec E a (hOne E a) hOne_mem_cone
  obtain ⟨ε, hε, hball⟩ := Metric.nhds_basis_closedBall.eventually_iff.1 hτ
  have hK : Metric.closedBall (hOne E a) ε ⊆ cone E a := fun p hp => ⟨τ p, hball hp⟩
  obtain ⟨C, hC⟩ := boundInf E a _ hK (isCompact_closedBall _ _)
  refine ⟨ε, C, hε, fun Y hY => ?_⟩
  have h1 : hOne E a ∈ Metric.closedBall (hOne E a) ε := Metric.mem_closedBall_self hε.le
  have hp : hOne E a + hv Y ∈ Metric.closedBall (hOne E a) ε := by
    rw [mem_closedBall_iff_norm, add_sub_cancel_left]
    exact hY
  have hs := hball hp
  refine ⟨τ (hOne E a + hv Y), ?_, hC _ _ h1 (by rw [hs]; exact hp), hC _ _ hp ?_⟩
  · have h2 := sand_val (τ (hOne E a + hv Y)) (hOne E a)
    rw [hs, hOne_val, mul_one] at h2
    exact h2.symm
  · have h3 : sand (τ (hOne E a + hv Y))⁻¹ (sand (τ (hOne E a + hv Y)) (hOne E a)) = hOne E a := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
    rw [hs] at h3
    rw [h3]; exact h1
end

section

open UpperTheory.V.Lit.Geo

theorem UpperTheory.geometric_side_estimate :
    ScaleFull := by
  unfold ScaleFull Scale
  intro V _ _ _ Λ _ _
  obtain ⟨hsum1, hsum2, c, hc, hP⟩ := PI.Tr.poissonGauss V Λ
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = (Module.finrank ℝ V : ℝ) / 2 := ⟨_, rfl⟩
  have e1 : -(Module.finrank ℝ V : ℝ) / 2 = -α := by rw [hα]; ring
  have key : ∀ r : ℝ, 0 < r → ∑' x : Λ, Real.exp (-Real.pi * (r * ‖(x : V)‖ ^ 2)) =
      c * r ^ (-α) * ∑' y : PI.Tr.dualLat Λ, Real.exp (-Real.pi * ‖(y : V)‖ ^ 2 / r) := by
    intro r hr
    have h := hP r hr 0
    simp only [add_zero, inner_zero_right, mul_zero, Real.cos_zero, mul_one] at h
    rw [← e1, ← h]
    refine tsum_congr (fun x => ?_)
    congr 1
    ring
  refine ⟨fun x => sq_nonneg _, fun s t hs hst => ?_⟩
  have ht : 0 < t := lt_of_lt_of_le hs hst
  refine ⟨by simpa [mul_assoc] using hsum1 s hs 0, ?_⟩
  rw [key s hs, key t ht]
  have hD : ∑' y : PI.Tr.dualLat Λ, Real.exp (-Real.pi * ‖(y : V)‖ ^ 2 / s) ≤
      ∑' y : PI.Tr.dualLat Λ, Real.exp (-Real.pi * ‖(y : V)‖ ^ 2 / t) := by
    refine Summable.tsum_le_tsum (fun y => Real.exp_le_exp.mpr ?_) (hsum2 s hs) (hsum2 t ht)
    have h0 : 0 ≤ Real.pi * ‖(y : V)‖ ^ 2 := by positivity
    have h3 : Real.pi * ‖(y : V)‖ ^ 2 / t ≤ Real.pi * ‖(y : V)‖ ^ 2 / s :=
      div_le_div_of_nonneg_left h0 hs hst
    rw [neg_mul, neg_div, neg_div]
    linarith
  have hD0 : 0 ≤ ∑' y : PI.Tr.dualLat Λ, Real.exp (-Real.pi * ‖(y : V)‖ ^ 2 / t) :=
    tsum_nonneg (fun y => (Real.exp_pos _).le)
  have hα0 : 0 ≤ α := by rw [hα]; positivity
  have hS : s ^ α ≤ t ^ α := Real.rpow_le_rpow hs.le hst hα0
  have hSpos : 0 < s ^ α := Real.rpow_pos_of_pos hs α
  have hTpos : 0 < t ^ α := Real.rpow_pos_of_pos ht α
  have hpow : (t / s) ^ Module.finrank ℝ V = (t ^ α) ^ 2 / (s ^ α) ^ 2 := by
    rw [← div_pow, ← Real.div_rpow ht.le hs.le, ← Real.rpow_mul_natCast (div_nonneg ht.le hs.le),
      ← Real.rpow_natCast]
    congr 1
    rw [hα]
    push_cast
    ring
  have hcD : 0 ≤ c * ∑' y : PI.Tr.dualLat Λ, Real.exp (-Real.pi * ‖(y : V)‖ ^ 2 / t) :=
    mul_nonneg hc.le hD0
  have h1 : (s ^ α)⁻¹ ≤ (t ^ α) ^ 2 / (s ^ α) ^ 2 * (t ^ α)⁻¹ := by
    rw [show (t ^ α) ^ 2 / (s ^ α) ^ 2 * (t ^ α)⁻¹ = t ^ α / (s ^ α) ^ 2 by
      field_simp]
    rw [inv_eq_one_div, div_le_div_iff₀ hSpos (by positivity)]
    nlinarith
  rw [Real.rpow_neg hs.le, Real.rpow_neg ht.le, hpow]
  calc c * (s ^ α)⁻¹ * ∑' y : PI.Tr.dualLat Λ, Real.exp (-Real.pi * ‖(y : V)‖ ^ 2 / s)
      ≤ c * (s ^ α)⁻¹ * ∑' y : PI.Tr.dualLat Λ, Real.exp (-Real.pi * ‖(y : V)‖ ^ 2 / t) :=
        mul_le_mul_of_nonneg_left hD (mul_nonneg hc.le (inv_nonneg.mpr hSpos.le))
    _ = (c * ∑' y : PI.Tr.dualLat Λ, Real.exp (-Real.pi * ‖(y : V)‖ ^ 2 / t)) * (s ^ α)⁻¹ := by ring
    _ ≤ (c * ∑' y : PI.Tr.dualLat Λ, Real.exp (-Real.pi * ‖(y : V)‖ ^ 2 / t)) *
          ((t ^ α) ^ 2 / (s ^ α) ^ 2 * (t ^ α)⁻¹) := mul_le_mul_of_nonneg_left h1 hcD
    _ = _ := by ring
end
