module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Bundle001
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.V.Lit.Geo

namespace UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem retr_left (γ : GL (Fin a) E) (t : ℝ) (g : GA E a) :
    (retractOne (ratGL E a γ * splitCentre E a t * g) : KernelIndexFullLattice.G1 E a).1 = ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1 := by
  let y : KernelIndexFullLattice.G1 E a := ⟨ratGL E a γ, Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩⟩
  change (retractOne ((y : GA E a) * splitCentre E a t * g) : KernelIndexFullLattice.G1 E a).1 = _
  rw [mul_assoc, retractOne_coe_mul, retractOne_mul, KernelIndexFullLattice.splitEq_holds E a t, retractOne_centralSection, one_mul]
  rfl

private theorem split_eq (s : {r : ℝ // 0 < r}) :
    splitCentre E a (Real.log s.1 / (a * Module.finrank ℚ E)) = Reduction.centralSection E a s := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact Units.ext (Subsingleton.elim _ _)
  have h1 : (0 : ℝ) < a := Nat.cast_pos.2 ha
  have h2 : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
  rw [KernelIndexFullLattice.splitEq_holds E a]
  refine congrArg (Reduction.centralSection E a) (Subtype.ext ?_)
  change Real.exp _ = _
  rw [mul_div_cancel₀ _ (mul_pos h1 h2).ne', Real.exp_log s.2]

private theorem retr_split (g : GA E a) : ∃ t : ℝ, (retractOne g : KernelIndexFullLattice.G1 E a).1 = splitCentre E a t * g :=
  ⟨_, by rw [split_eq (Reduction.detModule E a g)⁻¹, coe_retractOne, ← centralSection_inv_mul_comm, map_inv]⟩

private theorem split_retr (g : GA E a) :
    splitCentre E a (Real.log (Reduction.detModule E a g).1 / (a * Module.finrank ℚ E)) *
      (retractOne g : KernelIndexFullLattice.G1 E a).1 = g := by
  rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm, split_eq, coe_retractOne, inv_mul_cancel_right]

private theorem cont_inf : Continuous (infGL E a) := by
  have hs : Continuous (sInf E) :=
    ((continuous_infEq E).prodMk continuous_const :
      Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  exact Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))

private theorem compact_box (C : ℝ) :
    IsCompact {h : GL (Fin a) (Cinf E) | ‖toL h.val‖ ≤ C ∧ ‖toL (h⁻¹).val‖ ≤ C} := by
  have hB : IsCompact {x : Matrix (Fin a) (Fin a) (Cinf E) | ‖toL x‖ ≤ C} := by
    have h := isCompact_closedBall (0 : Lie E a) C
    have e : Metric.closedBall (0 : Lie E a) C = {x : Lie E a | ‖x‖ ≤ C} := Set.ext fun _ => mem_closedBall_zero_iff
    rw [e] at h
    exact h
  have h := Units.isClosedEmbedding_embedProduct.isCompact_preimage (hB.prod (hB.image MulOpposite.continuous_op))
  convert h using 1
  ext x
  refine and_congr Iff.rfl ⟨fun hx => ⟨_, hx, rfl⟩, ?_⟩
  rintro ⟨y, hy, e⟩
  have e' : y = (x⁻¹).val := MulOpposite.op_injective e
  rwa [e'] at hy

end UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.retrFacts :
    RetrFacts := by
  intro E _ _ _ a
  refine ⟨retr_split, retr_left, fun C => ?_⟩
  have hc : Continuous fun h : GL (Fin a) (Cinf E) =>
      Real.log (Reduction.detModule E a (infGL E a h)).1 / (a * Module.finrank ℚ E) :=
    ((continuous_subtype_val.comp (Reduction.continuous_detModule.comp cont_inf)).log
      fun h => (Reduction.detModule E a (infGL E a h)).2.ne').div_const _
  obtain ⟨T, hT⟩ := (compact_box (E := E) (a := a) C).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨T, fun g h h1 h2 => ⟨_, hT h ⟨h1, h2⟩, ?_⟩⟩
  rw [retractOne_mul, Subgroup.coe_mul, ← mul_assoc, GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm, mul_assoc, split_retr]
end

section

open UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.altEv :
    AltEv := by
  classical
  intro V F _ _ _ _ _ _ q k
  let bs := Module.finBasis ℝ V
  let L : (V [⋀^Fin q]→L[ℝ] F) →ₗ[ℝ] ((Fin q → Fin (Module.finrank ℝ V)) → F) :=
    { toFun := fun g σ => g (fun i => bs (σ i))
      map_add' := fun g h => by ext σ; simp
      map_smul' := fun c g => by ext σ; simp }
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro g hg
    have e : g.toAlternatingMap = (0 : V [⋀^Fin q]→L[ℝ] F).toAlternatingMap :=
      Module.Basis.ext_alternating bs (fun v _ => by simpa [L] using congrFun hg v)
    ext m
    simpa using DFunLike.congr_fun e m
  obtain ⟨M, hM⟩ := L.exists_leftInverse_of_injective hker
  let A : (Fin q → Fin (Module.finrank ℝ V)) → F →L[ℝ] (V [⋀^Fin q]→L[ℝ] F) := fun σ =>
    LinearMap.toContinuousLinearMap (M.comp (LinearMap.single ℝ (fun _ => F) σ))
  refine ⟨Finset.univ.image (fun σ : Fin q → Fin (Module.finrank ℝ V) => fun i => bs (σ i)),
    ∑ σ, ‖A σ‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_⟩
  intro f x b hb hcd hsz
  have mem : ∀ σ : Fin q → Fin (Module.finrank ℝ V),
      (fun i => bs (σ i)) ∈ Finset.univ.image (fun σ : Fin q → Fin (Module.finrank ℝ V) =>
        fun i => bs (σ i)) :=
    fun σ => Finset.mem_image_of_mem _ (Finset.mem_univ σ)
  have hrep : f = fun y => ∑ σ, A σ (f y (fun i => bs (σ i))) := by
    funext y
    calc f y = M (L (f y)) := (LinearMap.congr_fun hM (f y)).symm
      _ = M (∑ σ, Pi.single σ (L (f y) σ)) := by rw [Finset.univ_sum_single]
      _ = ∑ σ, A σ (f y (fun i => bs (σ i))) := by

        rw [map_sum]
        rfl
  intro i hi
  have hcdi : ∀ σ : Fin q → Fin (Module.finrank ℝ V),
      ContDiffAt ℝ i (fun y => f y (fun i => bs (σ i))) x :=
    fun σ => (hcd _ (mem σ)).of_le (by exact_mod_cast le_top)
  have hsum := iteratedFDeriv_fun_sum_apply (𝕜 := ℝ) (n := i) (x := x) (u := Finset.univ)
    (f := fun σ y => A σ (f y (fun i => bs (σ i))))
    (fun σ _ => (A σ).contDiff.contDiffAt.comp x (hcdi σ))
  rw [hrep, hsum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
  refine ((A σ).norm_iteratedFDeriv_comp_left (hcdi σ) le_rfl).trans ?_
  exact mul_le_mul_of_nonneg_left (hsz _ (mem σ) i hi) (norm_nonneg _)
end

section

open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff Topology

theorem UpperTheory.V.Lit.Geo.Cs.compSz :
    CompSz := by
  intro V W F _ _ _ _ _ _ k c
  have hD1 : (1 : ℝ) ≤ max 1 c := le_max_left _ _
  have hD0 : (0 : ℝ) ≤ max 1 c := zero_le_one.trans hD1
  refine ⟨(k.factorial : ℝ) * (max 1 c) ^ k, by positivity, ?_⟩
  intro g f x b hf hg hc hb i hi
  have hb0 : 0 ≤ b := hb.nonneg
  have hk : ((k : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hne : ((k : ℕ) : WithTop ℕ∞) ≠ ∞ := by exact_mod_cast ENat.coe_ne_top k
  have hf' := (hf.of_le hk).eventually hne
  have hg' := (hg.of_le hk).eventually hne
  obtain ⟨t, ht, hto, hxt⟩ := eventually_nhds_iff.1 hg'
  have hpre : ∀ᶠ y in 𝓝 x, f y ∈ t := hf.continuousAt.preimage_mem_nhds (hto.mem_nhds hxt)
  obtain ⟨s, hs, hso, hxs⟩ := eventually_nhds_iff.1 (hf'.and hpre)
  have hgt : ContDiffOn ℝ k g t := fun y hy => (ht y hy).contDiffWithinAt
  have hfs : ContDiffOn ℝ k f s := fun y hy => (hs y hy).1.contDiffWithinAt
  have key := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (n := i) (C := b) (D := max 1 c) hgt hfs
    (by exact_mod_cast hi) hto.uniqueDiffOn hso.uniqueDiffOn (fun y hy => (hs y hy).2) hxs
    (fun j hj => by
      rw [iteratedFDerivWithin_of_isOpen j hto hxt]
      exact hb j (hj.trans hi))
    (fun j hj1 hj => by
      rw [iteratedFDerivWithin_of_isOpen j hso hxs]
      exact ((hc j hj1 (hj.trans hi)).trans (le_max_right 1 c)).trans
        (le_self_pow₀ hD1 (by omega)))
  rw [iteratedFDerivWithin_of_isOpen i hso hxs] at key
  refine key.trans ?_
  have h1 : (i.factorial : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_le hi
  have h2 : (max 1 c) ^ i ≤ (max 1 c) ^ k := pow_le_pow_right₀ hD1 hi
  calc (i.factorial : ℝ) * b * (max 1 c) ^ i = ((i.factorial : ℝ) * (max 1 c) ^ i) * b := by ring
    _ ≤ _ := by gcongr
end

section

open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff Topology

theorem UpperTheory.V.Lit.Geo.Cs.geoCut :
    GeoCut := by
  intro Γ V S _ _ _ _ d G Φ hΦ R q η hη hinv
  classical
  set χ : ℝ → ℝ := fun t => Real.smoothTransition (2 * (t - R) - 1) with hχ
  have hχc : ContDiff ℝ ∞ χ :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul (contDiff_id.sub contDiff_const)).sub contDiff_const)
  have hχ0 : ∀ t, t ≤ R + 1 / 2 → χ t = 0 := fun t ht =>
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hχ1 : ∀ t, R + 1 ≤ t → χ t = 1 := fun t ht =>
    Real.smoothTransition.one_of_one_le (by linarith)
  let f : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ) :=
    fun s p => if p ∈ G.Y ∧ R < Φ s p then χ (Φ s p) • η s p else 0
  have hf : f ∈ G.Om q := by
    show ∀ s, ContDiffOn ℝ ∞ (f s) G.Y ∧ ∀ p ∉ G.Y, f s p = 0
    refine fun s => ⟨?_, fun p hp => by simp [f, hp]⟩
    apply contDiffOn_of_locally_contDiffOn
    intro p hp
    by_cases hR : R < Φ s p
    · refine ⟨G.Y ∩ Φ s ⁻¹' Set.Ioi R, (hΦ.1 s).continuousOn.isOpen_inter_preimage G.isOpen isOpen_Ioi,
        ⟨hp, hR⟩, ?_⟩
      have hsm : ContDiffOn ℝ ∞ (fun x => χ (Φ s x) • η s x) (G.Y ∩ (G.Y ∩ Φ s ⁻¹' Set.Ioi R)) :=
        ((hχc.comp_contDiffOn (hΦ.1 s)).mono (fun x (hx : x ∈ G.Y ∩ (G.Y ∩ Φ s ⁻¹' Set.Ioi R)) => hx.1)).smul
          ((hη s).mono (fun x (hx : x ∈ G.Y ∩ (G.Y ∩ Φ s ⁻¹' Set.Ioi R)) => ⟨hx.2.1, hx.2.2⟩))
      refine hsm.congr (fun x hx => ?_)
      have hx' : x ∈ G.Y ∧ R < Φ s x := ⟨hx.2.1, hx.2.2⟩
      simp only [f, if_pos hx']
    · push_neg at hR
      refine ⟨G.Y ∩ Φ s ⁻¹' Set.Iio (R + 1 / 2),
        (hΦ.1 s).continuousOn.isOpen_inter_preimage G.isOpen isOpen_Iio,
        ⟨hp, show Φ s p < R + 1 / 2 by linarith⟩, ?_⟩
      refine (contDiffOn_const (c := (0 : V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)))).congr (fun x hx => ?_)
      have hx2 : Φ s x < R + 1 / 2 := hx.2.2
      simp only [f]
      split_ifs with h
      · rw [hχ0 _ hx2.le, zero_smul]
      · rfl
  refine ⟨⟨f, hf⟩, ?_, ?_⟩
  · intro γ
    apply Subtype.ext
    funext s p
    show G.tr q γ (f (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p)) = f s p
    have hρ : ∀ x, G.ρ γ (G.ρ γ⁻¹ x) = x := by
      intro x
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    by_cases hp : p ∈ G.Y
    · have hp' : G.ρ γ⁻¹ p ∈ G.Y := G.maps _ _ hp
      have hΦ' : Φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) = Φ s p := hΦ.2.1 γ⁻¹ s p hp
      by_cases hR : R < Φ s p
      · have h1 : G.ρ γ⁻¹ p ∈ G.Y ∧ R < Φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) := ⟨hp', by rw [hΦ']; exact hR⟩
        have h2 : p ∈ G.Y ∧ R < Φ s p := ⟨hp, hR⟩
        simp only [f, if_pos h1, if_pos h2]
        rw [hΦ', map_smul, hinv γ s p hp hR]
      · have h1 : ¬ (G.ρ γ⁻¹ p ∈ G.Y ∧ R < Φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p)) := by
          rw [hΦ']
          exact fun h => hR h.2
        have h2 : ¬ (p ∈ G.Y ∧ R < Φ s p) := fun h => hR h.2
        simp only [f, if_neg h1, if_neg h2, map_zero]
    · have hp' : G.ρ γ⁻¹ p ∉ G.Y := fun h => hp (by simpa [hρ] using G.maps γ _ h)
      have h1 : ¬ (G.ρ γ⁻¹ p ∈ G.Y ∧ R < Φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p)) := fun h => hp' h.1
      have h2 : ¬ (p ∈ G.Y ∧ R < Φ s p) := fun h => hp h.1
      simp only [f, if_neg h1, if_neg h2, map_zero]
  · intro s p hp h1
    have h2 : p ∈ G.Y ∧ R < Φ s p := ⟨hp, by linarith⟩
    show f s p = η s p
    simp only [f, if_pos h2, hχ1 _ h1, one_smul]
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr
open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Geo.Cs

section

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem exists_unitary {g h : GL (Fin a) (Cinf E)} (e : sand g (hOne E a) = sand h (hOne E a)) :
    ∃ k : Kinf E a, h = g * Unitary.toUnits k := by
  have comp : ∀ (g h : GL (Fin a) (Cinf E)) (v : HV E a), sand g (sand h v) = sand (g * h) v := fun g h v => by
    rw [map_mul]; rfl
  have h1 : sand (g⁻¹ * h) (hOne E a) = hOne E a := by
    rw [← comp, ← e, comp, inv_mul_cancel, map_one]; rfl
  have h2 : (g⁻¹ * h).val * star (g⁻¹ * h).val = 1 := by
    have h3 := sand_val (g⁻¹ * h) (hOne E a)
    rw [h1, hOne_val, mul_one] at h3
    exact h3.symm
  refine ⟨⟨(g⁻¹ * h).val, Matrix.mem_unitaryGroup_iff.2 h2⟩, ?_⟩
  rw [← inv_mul_eq_iff_eq_mul]
  exact Units.ext rfl

end

theorem UpperTheory.V.Lit.Geo.Cs.descEx :
    DescEx := by
  classical
  intro E _ _ _ a U f Y C c f₀ hf
  refine ⟨fun s p => if h : p ∈ cone E a then f (pt h.choose s.out) else 0, fun g x => ?_⟩
  have hp : sand g (hOne E a) ∈ cone E a := ⟨g, rfl⟩
  obtain ⟨k, hk⟩ := exists_unitary hp.choose_spec.symm
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U x
  beta_reduce
  rw [dite_eq_left hp, hk, pt_mul, hf.f_cpt, hu, pt, pt, map_mul (finGL E a), ← mul_assoc, hf.f_lev _ u.2]
end
end

section

open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff

private theorem norm_id_le (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (j : ℕ) (p : V) :
    ‖iteratedFDeriv ℝ (j + 1) (fun x : V => x) p‖ ≤ 1 := by
  rw [← norm_iteratedFDeriv_fderiv]
  have e : fderiv ℝ (fun x : V => x) = fun _ => ContinuousLinearMap.id ℝ V := by
    funext x
    exact fderiv_id
  rw [e]
  rcases j with _ | j
  · simpa using ContinuousLinearMap.norm_id_le
  · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j)]
    simp

theorem UpperTheory.V.Lit.Geo.Cs.flowSz :
    FlowSz := by
  intro V _ _ k c W t p ht hW hS
  have e : UpperTheory.V.Lit.Geo.flow W t = (fun x : V => x) + t • W := rfl
  have h1 : ContDiffAt ℝ ∞ (UpperTheory.V.Lit.Geo.flow W t) p := by
    rw [e]
    exact contDiffAt_id.add (hW.const_smul t)
  have h4 : ∀ i, 1 ≤ i → i ≤ k + 1 → ‖iteratedFDeriv ℝ i (UpperTheory.V.Lit.Geo.flow W t) p‖ ≤ 1 + c := by
    intro i h1i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hWj : ContDiffAt ℝ ((j + 1 : ℕ) : WithTop ℕ∞) W p := hW.of_le (by exact_mod_cast le_top)
    have hid : ContDiffAt ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (fun x : V => x) p := contDiffAt_id
    have htW : ContDiffAt ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (t • W) p := hWj.const_smul t
    rw [e, iteratedFDeriv_add_apply hid htW, iteratedFDeriv_const_smul_apply hWj]
    refine (norm_add_le _ _).trans (add_le_add (norm_id_le V j p) ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht).trans (hS _ hi)
  refine ⟨h1, h1.fderiv_right (by simp), fun i hi => ?_, h4⟩
  rw [norm_iteratedFDeriv_fderiv]
  exact h4 _ (by omega) (by omega)
end

section

open UpperTheory.V.Lit.Geo.Cs
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct

section
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem one_comm (X : Lie E a) (φ : Sm E a) :
    lie E a (oneL E a) (lie E a X φ) = lie E a X (lie E a (oneL E a) φ) := by
  have h := lie_comm (oneL E a) X
  have e : Matrix.of (oneL E a) * Matrix.of X = Matrix.of X * Matrix.of (oneL E a) :=
    (one_mul (Matrix.of X)).trans (mul_one (Matrix.of X)).symm
  rw [e, sub_self, sub_eq_zero] at h
  exact LinearMap.congr_fun h φ

private theorem eig_prod (c : ℂ) (φ : Sm E a) (h : lie E a (oneL E a) φ = c • φ) (l : List (Lie E a)) :
    lie E a (oneL E a) ((l.map (lie E a)).prod φ) = c • (l.map (lie E a)).prod φ := by
  induction l with
  | nil => simpa using h
  | cons X l ih => rw [List.map_cons, List.prod_cons, Module.End.mul_apply, one_comm, ih, map_smul]

private theorem cmp_rTensor {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (j : Fin d) (T : Module.End ℂ W)
    (m : W ⊗[ℂ] (Fin d → ℂ)) : Bor.cmp j (T.rTensor _ m) = T (Bor.cmp j m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul φ v => rw [LinearMap.rTensor_tmul, cmp_tmul, cmp_tmul, map_smul]

private theorem cmp_prod (Ξ : AlgRep E a) (j : Fin Ξ.d) (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) (l : List (Lie E a)) :
    Bor.cmp j ((l.map (smA Ξ)).prod m) = (l.map (lie E a)).prod (Bor.cmp j m) := by
  induction l with
  | nil => simp
  | cons X l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, smA_apply, cmp_rTensor, ih, List.map_cons, List.prod_cons,
      Module.End.mul_apply]

private theorem ev_eq {d : ℕ} (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) (g : GA E a) : ev m g j = (Bor.cmp j m).1 g := by
  induction m using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero]
    rfl
  | tmul φ v => simp [mul_comm]
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), Pi.add_apply, Pi.add_apply, Submodule.coe_add, Pi.add_apply, hx, hy]

end

theorem UpperTheory.V.Lit.Geo.Cs.rapidEig :
    RapidEig := by
  intro E _ _ _ a U Ξ r hr q α hα X j l
  refine ⟨eig_prod _ _ ?_ l, fun g => by rw [ev_eq, cmp_prod]⟩
  have h : Bor.cmp j (α X) ∈ LinearMap.eqLocus (lie E a (oneL E a)) (-(r : ℂ) • LinearMap.id) :=
    mem_tens.1 (span_le_tens (fun φ hφ => hφ.2.2 _ hr) (hα.val X)) j
  exact h
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.Cs.supp :
    UpperTheory.V.Lit.Geo.Cs.Supp := by
  intro E _ _ _ a U Ξ f Y C c f₀ hs Φ hΦ q α w R hc hw
  refine ⟨Real.exp (|C| * (1 + |R|)), fun X g hg => ?_⟩
  have hf : R < f g := by
    by_contra hle
    have hle' : f g ≤ R := not_lt.1 hle
    have h1 : |C| * (1 + |R|) < Real.log (qht g) :=
      (Real.lt_log_iff_exp_lt ((Real.exp_pos _).trans hg)).2 hg
    have h0 := hs.f_nonneg g
    have h2 : C * (1 + f g) ≤ |C| * (1 + |R|) :=
      mul_le_mul (le_abs_self C) (by linarith [le_abs_self R]) (by linarith) (abs_nonneg C)
    linarith [hs.le_f g]
  obtain ⟨y, x, rfl⟩ : ∃ y x, infGL E a y * finGL E a x = g := ⟨_, _, infGL_mul_finGL g⟩
  have hz := hw (x : GL (Fin a) (Af E) ⧸ U) _ (sand_mem_cone y hOne_mem_cone) (by rw [hΦ y x]; exact hf)
  have h := hc y x X
  rw [hz] at h
  have h2 := congrArg (fun z => Ξ.mat y⁻¹ *ᵥ z) h
  simpa only [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec,
    ContinuousAlternatingMap.coe_zero, Pi.zero_apply, Matrix.mulVec_zero] using h2.symm
end

section

open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff

private theorem sz_ball {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : X → Y) (hf : ContDiff ℝ ∞ f) (k : ℕ) (c : ℝ) :
    ∃ C : ℝ, ∀ x : X, ‖x‖ ≤ c → Sz k f x C := by
  have hc : Continuous fun x => ∑ i ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ i f x‖ :=
    continuous_finsetSum _ fun i _ => (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : X) c).bddAbove_image hc.continuousOn
  refine ⟨C, fun x hx i hi => ?_⟩
  refine le_trans ?_ (hC ⟨x, mem_closedBall_zero_iff.2 hx, rfl⟩)
  exact Finset.single_le_sum (f := fun i => ‖iteratedFDeriv ℝ i f x‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

private theorem alt_fin (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] (q : ℕ) : FiniteDimensional ℝ (V [⋀^Fin q]→L[ℝ] F) := by
  let b := Module.finBasis ℝ V
  let E : (V [⋀^Fin q]→L[ℝ] F) →ₗ[ℝ] ((Fin q → Fin (Module.finrank ℝ V)) → F) :=
    { toFun := fun a k => a fun i => b (k i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective E fun a a' h => ?_
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  exact Module.Basis.ext_alternating b fun k _ => congrFun h k

theorem UpperTheory.V.Lit.Geo.Cs.altSz :
    AltSz := by
  intro V F _ _ _ _ _ _ q k c
  have h : ContDiff ℝ ∞ (fun L : V →L[ℝ] V => (ContinuousAlternatingMap.compContinuousLinearMapCLM L :
      (V [⋀^Fin q]→L[ℝ] F) →L[ℝ] (V [⋀^Fin q]→L[ℝ] F))) := by
    haveI := alt_fin V F q
    rw [contDiff_clm_apply_iff]
    intro w
    rw [contDiff_iff_contDiffAt]
    intro L
    refine UpperTheory.V.Lit.Dr.altSmooth _ V F q _ L fun v => ?_
    exact UpperTheory.V.Lit.Dr.applySmooth (V →L[ℝ] V) V F q (fun _ => w) (fun i L => L (v i)) L contDiffAt_const
      fun i => (contDiffAt_id.clm_apply contDiffAt_const)
  exact ⟨h, sz_ball _ h k c⟩
end
