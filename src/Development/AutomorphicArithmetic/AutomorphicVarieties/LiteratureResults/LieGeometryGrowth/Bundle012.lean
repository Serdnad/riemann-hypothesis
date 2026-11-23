module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsAppSz
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
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

@[expose] public section

section

noncomputable section

open scoped ContDiff Topology

namespace UpperTheory.V.Lit.Geo

section

variable {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]

private def tot (W : V → V) (z : V × ℝ) : V := flow W z.2 z.1

private theorem tot_diff {W : V → V} {x : V} (hW : DifferentiableAt ℝ W x) (r : ℝ) :
    DifferentiableAt ℝ (tot W) (x, r) := by
  have h : DifferentiableAt ℝ (fun z : V × ℝ => W z.1) (x, r) :=
    DifferentiableAt.comp (x, r) (g := W) (f := Prod.fst) hW differentiableAt_fst
  exact differentiableAt_fst.add (differentiableAt_snd.smul h)

private theorem tot_smooth {W : V → V} {x : V} (hW : ContDiffAt ℝ ∞ W x) (r : ℝ) :
    ContDiffAt ℝ ∞ (tot W) (x, r) := by
  unfold tot flow
  exact contDiffAt_fst.add (contDiffAt_snd.smul (hW.comp (x, r) contDiffAt_fst))

private theorem tot_inl {W : V → V} {x : V} (hW : DifferentiableAt ℝ W x) (r : ℝ) (v : V) :
    fderiv ℝ (tot W) (x, r) (v, 0) = fderiv ℝ (flow W r) x v := by
  have h1 := (tot_diff hW r).hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x r)
  have h2 : flow W r = tot W ∘ fun y => (y, r) := rfl
  rw [h2, h1.fderiv]
  rfl

private theorem tot_inr {W : V → V} {x : V} (hW : DifferentiableAt ℝ W x) (r : ℝ) :
    fderiv ℝ (tot W) (x, r) (0, 1) = W x := by
  have h1 := (tot_diff hW r).hasFDerivAt.comp_hasDerivAt r ((hasDerivAt_const r x).prodMk (hasDerivAt_id r))
  have h2 : HasDerivAt (tot W ∘ fun s => (x, s)) ((1 : ℝ) • W x) r :=
    ((hasDerivAt_id r).smul_const (W x)).const_add x
  simpa using h1.unique h2

private theorem pb_tot {W : V → V} {x : V} (hW : DifferentiableAt ℝ W x) (r : ℝ) {q : ℕ}
    (w : V → V [⋀^Fin q]→L[ℝ] F) :
    (pb (tot W) w (x, r)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ) = pb (flow W r) w x := by
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, pb_apply, Function.comp_apply,
    ContinuousLinearMap.inl_apply, tot_inl hW]
  rfl

private theorem hk_tot {W : V → V} {x : V} (hW : DifferentiableAt ℝ W x) (r : ℝ) {q : ℕ}
    (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F) :
    ((pb (tot W) w (x, r)).curryLeft (0, 1)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ) = hk W r w x := by
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousAlternatingMap.curryLeft_apply_apply,
    pb_apply, hk_apply]
  congr 1
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [tot_inr hW]
  · simp [tot_inl hW]

end

theorem homPt : HomPt := by
  intro V F _ _ _ _ _ _ W p t hW
  have hd : DifferentiableAt ℝ W p := hW.differentiableAt (by simp)
  have hfl : ∀ (q : ℕ) (w : V → V [⋀^Fin q]→L[ℝ] F), (fun r => pb (flow W r) w p) =
      fun r => (pb (tot W) w (p, r)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ) :=
    fun q w => funext fun r => (pb_tot hd r w).symm
  have key : ∀ (q : ℕ) (w : V → V [⋀^Fin q]→L[ℝ] F), ContDiffAt ℝ ∞ w (flow W t p) →
      DifferentiableAt ℝ (pb (tot W) w) (p, t) ∧
        extDeriv (pb (tot W) w) (p, t) = pb (tot W) (extDeriv w) (p, t) := by
    intro q w hw
    obtain ⟨h1, h2⟩ := pbD (V × ℝ) V F q (tot W) w (p, t) (tot_smooth hW t) hw
    exact ⟨h1.differentiableAt (by simp), h2⟩
  refine ⟨fun w hw => ?_, fun q w hw => ?_⟩
  · obtain ⟨hD, hE⟩ := key 0 w hw
    rw [hfl, ← hk_tot hd t (extDeriv w), ← hE]
    exact (prodDer V F p t).1 _ hD
  · obtain ⟨hD, hE⟩ := key (q + 1) w hw
    have hev : (fun y => ((pb (tot W) w (y, t)).curryLeft (0, 1)).compContinuousLinearMap
        (ContinuousLinearMap.inl ℝ V ℝ)) =ᶠ[𝓝 p] hk W t w := by
      have h1 : ∀ᶠ y in 𝓝 p, ContDiffAt ℝ 1 W y := (hW.of_le (by simp)).eventually (by simp)
      filter_upwards [h1] with y hy
      exact hk_tot (hy.differentiableAt (by simp)) t w
    rw [hfl, ← hk_tot hd t (extDeriv w), ← hE, ← hev.extDeriv_eq]
    exact (prodDer V F p t).2 q _ hD

end UpperTheory.V.Lit.Geo
end
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.V.Lit.Geo.Cs

namespace UpperTheory.V.Lit.Geo.Cs

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private noncomputable def lam0 (g : GA E a) : ℝ :=
  Real.log (Reduction.detModule E a g).1 / (a * Module.finrank ℚ E)

private theorem deg_pos (ha : 1 ≤ a) : (0 : ℝ) < a * Module.finrank ℚ E :=
  mul_pos (Nat.cast_pos.2 ha) (Nat.cast_pos.2 Module.finrank_pos)

private theorem central_log_mul (g h : GA E a) : lam0 (g * h) = lam0 g + lam0 h := by
  unfold lam0
  rw [map_mul, ← add_div, ← Real.log_mul (Reduction.detModule E a g).2.ne' (Reduction.detModule E a h).2.ne']
  rfl

private theorem central_split_mul_retract (ha : 1 ≤ a) (g : GA E a) :
    splitCentre E a (lam0 g) * (retractOne g : KernelIndexFullLattice.G1 E a).1 = g := by
  have e : splitCentre E a (lam0 g) = Reduction.centralSection E a (Reduction.detModule E a g) := by
    rw [KernelIndexFullLattice.splitEq_holds E a]
    refine congrArg (Reduction.centralSection E a) (Subtype.ext ?_)
    change Real.exp _ = _
    rw [lam0, mul_div_cancel₀ _ (deg_pos ha).ne', Real.exp_log (Reduction.detModule E a g).2]
  rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm, e, coe_retractOne, inv_mul_cancel_right]

private theorem central_log_eq_zero_on_norm_one (x : KernelIndexFullLattice.G1 E a) : lam0 (x.1 : GA E a) = 0 := by
  rw [lam0, (Reduction.mem_normOneGL_iff_detModule).1 x.2]
  simp

private theorem central_log_split (ha : 1 ≤ a) (t : ℝ) : lam0 (splitCentre E a t) = t := by
  rw [lam0, KernelIndexFullLattice.splitEq_holds E a, Reduction.detModule_centralSection (by omega)]
  change Real.log (Real.exp _) / _ = _
  rw [Real.log_exp, mul_div_cancel_left₀ _ (deg_pos ha).ne']

end UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.lamEx :
    LamEx := by
  intro E _ _ _ a ha
  refine ⟨lam0, central_log_mul, central_split_mul_retract ha, fun c => ?_⟩
  obtain ⟨T, hT⟩ := (UpperTheory.V.Lit.Geo.retrFacts E a).2.2 c
  refine ⟨T, fun h hh => ?_⟩
  obtain ⟨t, ht, e⟩ := hT 1 h hh.1 hh.2
  have e' := congrArg lam0 e
  rw [central_log_mul, central_log_mul, central_log_eq_zero_on_norm_one, central_log_eq_zero_on_norm_one, central_log_split ha, zero_add, add_zero] at e'
  rwa [e']
end

section

open UpperTheory.V.Lit.Geo.Cs
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct ContDiff Topology

private theorem ev_eq_cmp {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a d : ℕ}
    (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) (g : GA E a) : ev m g j = (UpperTheory.V.Lit.Bor.cmp j m).1 g := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul φ v => simp [mul_comm]

private theorem alt_expand {V W M : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup M] [Module ℝ M] {q n : ℕ} (α : V [⋀^Fin q]→ₗ[ℝ] M) (e : V ≃ₗ[ℝ] W) (b : Module.Basis (Fin n) ℝ W)
    (u : Fin q → W) :
    α (fun i => e.symm (u i)) = ∑ I : Fin q → Fin n, (∏ i, b.repr (u i) (I i)) • α fun i => e.symm (b (I i)) := by
  have h : (fun i => e.symm (u i)) = fun i => ∑ k, b.repr (u i) k • e.symm (b k) := by
    funext i
    conv_lhs => rw [← b.sum_repr (u i)]

    simp only [map_sum, map_smul]
  rw [h]
  refine (α.toMultilinearMap.map_sum (fun i k => b.repr (u i) k • e.symm (b k))).trans ?_
  exact Finset.sum_congr rfl fun I _ => α.map_smul_univ _ _

theorem UpperTheory.V.Lit.Geo.Cs.corrForm :
    CorrForm := by
  intro E _ _ _ a Ξ q v
  classical
  obtain ⟨τ, h1, hτ, -, -, hi, hs⟩ := secOne E a
  let b := Module.finBasis ℝ (HV E a)
  let u : HV E a → Fin q → HV E a := fun p i => (2 : ℝ)⁻¹ • sand (τ p)⁻¹ (v i)
  refine ⟨(Fin q → Fin (Module.finrank ℝ (HV E a))) × Fin Ξ.d, inferInstance,
    fun I i => hv.symm (b (I.1 i)), fun I => I.2,
    fun I p k => ((∏ i, b.repr (u p i) (I.1 i) : ℝ) : ℂ) * Ξ.mat (τ p) k I.2,
    fun p => toL (τ p).val, by simp only [h1]; rfl, hτ, fun I => ?_, fun U α w hc g x => ?_⟩
  · refine contDiffAt_pi.2 fun k => ContDiffAt.mul ?_ ?_
    · refine Complex.ofRealCLM.contDiff.contDiffAt.comp (hOne E a)
        (f := fun p => ∏ i, b.repr (u p i) (I.1 i)) ?_
      refine contDiffAt_prod fun i _ => ?_
      have hu : ContDiffAt ℝ ∞ (fun p => u p i) (hOne E a) := (hi.clm_apply contDiffAt_const).const_smul _
      exact (LinearMap.toContinuousLinearMap (b.coord (I.1 i))).contDiff.contDiffAt.comp (hOne E a) hu
    · have := (((matSmooth E a Ξ k I.2).1).contDiffAt
          (isOpen_invSet.mem_nhds (val_mem_invSet (τ (hOne E a))))).comp (hOne E a) hτ
      simpa only [Function.comp_def, extGL_val] using this
  · refine hs.mono fun p hp => ?_
    have e1 : sand (g * τ p) (hOne E a) = sand g p := by
      rw [map_mul, ContinuousLinearMap.mul_apply, hp]
    have e2 : ∀ i, (2 : ℝ) • sand (g * τ p) (u p i) = sand g (v i) := fun i => by
      simp only [u, map_smul, smul_smul]
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel_right]
      simp
    have h := hc (g * τ p) x fun i => hv.symm (u p i)
    simp only [LinearEquiv.apply_symm_apply, e1, e2] at h
    have e3 : infGL E a (g * τ p) * finGL E a x = pt g x * infGL E a (τ p) := pt_mul g (τ p) x
    simp only [Tw, tp_apply, mulVecL_apply, h, e3, Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel_left, chart_val]
    rw [alt_expand α hv b (u p)]
    funext k
    have e4 : ∀ (I : Fin q → Fin (Module.finrank ℝ (HV E a))) (r : ℝ) (y : GA E a),
        ev (r • α fun i => hv.symm (b (I i))) y = (r : ℂ) • ev (α fun i => hv.symm (b (I i))) y := fun I r y => by
      rw [← algebraMap_smul ℂ r, map_smul]; rfl

    rw [map_sum]
    simp only [Finset.sum_apply, e4, Matrix.mulVec, dotProduct, Pi.smul_apply, ← ev_eq_cmp,
      Fintype.sum_prod_type, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun j _ => ?_
    ring
end

section

open UpperTheory.V.Lit.Geo.Cs
open scoped Topology ContDiff

theorem UpperTheory.V.Lit.Geo.Cs.geoSum :
    GeoSum := by
  intro Γ V S _ _ _ _ d G Φ hΦ R q y w hy hdy hsz hw
  have hopen : ∀ s, IsOpen {p | p ∈ G.Y ∧ R < Φ s p} := fun s =>
    (hΦ.1 s).continuousOn.isOpen_inter_preimage G.isOpen isOpen_Ioi
  have hmem : ∀ j s, ContDiffOn ℝ ∞ ((y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) G.Y :=
    fun j s => ((y j).2 s).1
  have hsm : ∀ s,
      ContDiffOn ℝ ∞ (fun x => ∑' j, (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x)
        {p | p ∈ G.Y ∧ R < Φ s p} ∧
      ∀ p ∈ {p | p ∈ G.Y ∧ R < Φ s p},
        HasSum (fun j => fderiv ℝ ((y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) p)
          (fderiv ℝ (fun x => ∑' j, (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x) p) :=
    fun s => sumSm V _ _ (hopen s) (fun j x => (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x)
      (fun j => (hmem j s).mono (fun p hp => hp.1)) (fun k p hp => hsz k s p hp.1 hp.2)
  have hsumv : ∀ s, ∀ p ∈ G.Y, R < Φ s p →
      Summable (fun j => (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p) := by
    intro s p hp hR
    obtain ⟨N, hN, b, hb, hbd⟩ := hsz 0 s p hp hR
    refine Summable.of_norm_bounded hb (fun j => ?_)
    have h0 := hbd j p (mem_of_mem_nhds hN) 0 le_rfl
    simpa using h0
  obtain ⟨z, hzinv, hz⟩ := geoCut Γ V S d G Φ hΦ R q
    (fun s p => -∑' j, (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p)
    (fun s => (hsm s).1.neg) (by
      intro γ s p hp hR
      have hp2 : (G.ρ γ⁻¹) p ∈ G.Y := G.maps _ p hp
      have hR2 : R < Φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) := by rw [hΦ.2.1 γ⁻¹ s p hp]; exact hR
      simp only [map_neg]
      congr 1
      rw [ContinuousLinearMap.map_tsum _ (hsumv _ _ hp2 hR2)]
      congr 1
      funext j
      exact congrFun (congrFun (congrArg Subtype.val (hy j γ)) s) p)
  refine ⟨z, hzinv, fun s p hp hR => ?_⟩
  have hev : (z : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s =ᶠ[𝓝 p]
      (fun x => -∑' j, (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x) := by
    have hc : ContinuousAt (Φ s) p := (hΦ.1 s).continuousOn.continuousAt (G.isOpen.mem_nhds hp)
    filter_upwards [G.isOpen.mem_nhds hp, Filter.Tendsto.eventually hc (lt_mem_nhds hR)]
      with x hx hx'
    exact hz s x hx hx'.le
  have hp' : p ∈ {p | p ∈ G.Y ∧ R < Φ s p} := ⟨hp, by linarith⟩
  have hD := ((hsm s).2 p hp').mapL (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V (Fin d → ℂ))
  have hterm : ∀ j, ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V (Fin d → ℂ)
      (fderiv ℝ ((y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) p) =
      (w (j + 1) : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p -
        (w j : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p := by
    intro j
    have h1 := congrFun (congrFun (congrArg Subtype.val (hdy j)) s) p
    rw [ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
    change _ = ((w (j + 1) - w j : G.Om (q + 1)) : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p
    rw [← h1]
    show _ = G.Y.indicator (extDeriv ((y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s)) p
    rw [Set.indicator_of_mem hp]
    rfl
  have hL : ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V (Fin d → ℂ)
      (fderiv ℝ (fun x => ∑' j, (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x) p) =
      -(w 0 : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p := by
    have ht := hD.tendsto_sum_nat
    simp_rw [hterm, Finset.sum_range_sub
      (fun j => (w j : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p)] at ht
    have ht2 := (hw s p hp (by linarith)).sub_const
      ((w 0 : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p)
    rw [zero_sub] at ht2
    exact tendsto_nhds_unique ht ht2
  show G.Y.indicator (extDeriv ((z : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s)) p = _
  rw [Set.indicator_of_mem hp, hev.extDeriv_eq]
  show ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ
    (-(fun x => ∑' j, (y j : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x)) p) = _
  rw [fderiv_neg, ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply, map_neg, hL, neg_neg]
end

section

open UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.pbSz :
    PbSz := by
  intro V F _ _ _ _ _ _ q k c
  obtain ⟨hAcd, C2, hC2⟩ := altSz V F q k (1 + c)
  obtain ⟨C1, hC1, hcomp1⟩ := compSz V V (V [⋀^Fin q]→L[ℝ] F) k (1 + c)
  obtain ⟨C3, hC3, hcomp3⟩ := compSz V (V →L[ℝ] V)
    ((V [⋀^Fin q]→L[ℝ] F) →L[ℝ] (V [⋀^Fin q]→L[ℝ] F)) k (1 + c)
  refine ⟨2 ^ k * (C3 * max C2 0) * C1, by positivity, ?_⟩
  intro W t w p b ht hW hWs hw hws
  obtain ⟨hF1, hF2, hF3, hF4⟩ := flowSz V k c W t p ht hW hWs
  have hg := hcomp1 w (UpperTheory.V.Lit.Geo.flow W t) p b hF1 hw
    (fun i h1 h2 => hF4 i h1 (by omega)) hws
  have hL : ‖fderiv ℝ (UpperTheory.V.Lit.Geo.flow W t) p‖ ≤ 1 + c := by
    simpa using hF3 0 (Nat.zero_le _)
  have hA : Sz k _ (fderiv ℝ (UpperTheory.V.Lit.Geo.flow W t) p) (max C2 0) :=
    fun i hi => (hC2 _ hL i hi).trans (le_max_left _ _)
  have hf := hcomp3 _ (fderiv ℝ (UpperTheory.V.Lit.Geo.flow W t)) p (max C2 0) hF2
    hAcd.contDiffAt (fun i h1 h2 => hF3 i h2) hA
  have hprod := (appSz V (V [⋀^Fin q]→L[ℝ] F) (V [⋀^Fin q]→L[ℝ] F) k p).1 _ _ _ _
    (hAcd.contDiffAt.comp p hF2) (hw.comp p hF1) hf hg
  have e : 2 ^ k * (C3 * max C2 0) * C1 * b = 2 ^ k * (C3 * max C2 0) * (C1 * b) := by ring
  rw [e]
  exact hprod
end
