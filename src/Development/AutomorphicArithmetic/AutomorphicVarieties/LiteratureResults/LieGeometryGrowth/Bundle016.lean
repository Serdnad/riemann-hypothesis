module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SkewLieActionL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsZwSz
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle011
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle008
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

section

open UpperTheory.V.Lit.Geo
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep UpperTheory.V.Af GlobalTheory.UnitaryBC
open scoped GlobalTheory.CuspRep.CuspidalL2GL

private theorem one_mem {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} :
    (fun _ => (1 : ℂ)) ∈ Sm E a := fun g =>
  (contDiffOn_const (c := (1 : ℂ))).congr fun x hx => by
    have hx' : IsUnit (Matrix.of x) := hx
    simp [chart, hx']

private theorem lie_one {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (X : Lie E a) :
    lie E a X ⟨fun _ => (1 : ℂ), one_mem⟩ = 0 := by
  obtain ⟨c, c0, -, -, cder, -⟩ := UpperTheory.V.Lit.Bor.oneParam E a X
  refine Subtype.ext (funext fun g => ?_)
  exact (hasDerivAt_curve (⟨fun _ => (1 : ℂ), one_mem⟩ : Sm E a) g c X c0 cder).unique (hasDerivAt_const (0 : ℝ) (1 : ℂ))

theorem UpperTheory.V.Lit.Geo.Pf.stokesFn :
    UpperTheory.V.Lit.Geo.Pf.StokesFn := by
  intro E _ _ _ a μ _ θ X hθ hc
  let u : Sm E a := ⟨fun _ => (1 : ℂ), one_mem⟩
  have hu : IsOpen {k | act (.fin k) u = u} := by
    have e : {k | act (.fin k) u = u} = Set.univ := Set.eq_univ_of_forall fun k => rfl
    rw [e]
    exact isOpen_univ
  obtain ⟨h1, h2⟩ := Pf.invLie E a θ hθ
  have h3 := (Pf.invLie E a _ (h2 X)).1
  have m1 := (Pf.bddInt E a μ _ h1 (Pf.csBdd E a _ h1 (.inl hc))).2
  have m2 := (Pf.bddInt E a μ _ h3 (Pf.csBdd E a _ h3 (.inl (Pf.csLie E a θ X hc)))).2
  have m3 := (Pf.bddInt E a μ u.1 ⟨continuous_const, fun _ _ => rfl, fun _ _ => rfl⟩ ⟨1, fun _ => norm_one.le⟩).2
  have e0 : (lie E a X u).1 = fun _ => 0 := congrArg Subtype.val (lie_one X)
  have m4 : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (latticeGL E a) μ (lie E a X u).1 := by
    rw [e0]
    exact (Pf.bddInt E a μ _ ⟨continuous_const, fun _ _ => rfl, fun _ _ => rfl⟩ ⟨0, fun _ => norm_zero.le⟩).2
  have h := UpperTheory.V.Lit.Bor.skew_lie_action_L2 E a μ X u θ hu hθ.level m3 m1 m4 m2
  rw [GlobalTheory.AutomorphicL2Unitary.MemL2Quotient.inner_toL2_eq_theta_pairing, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient.inner_toL2_eq_theta_pairing, e0] at h
  simpa [GlobalTheory.AutomorphicL2Unitary.pet, GlobalTheory.AutomorphicL2Unitary.descend, Pf.qint, u] using h
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo

private theorem norm_hom_le {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (W : V → V) {q : ℕ} (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F) (p : V) (v : Fin q → V) (A : F →L[ℝ] F) (K : ℝ)
    (hc : ContinuousOn (fun t => hk W t w p) (Set.Icc 0 1))
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖A (hk W t w p v)‖ ≤ K) : ‖A (hom W w p v)‖ ≤ K := by
  have hi : IntervalIntegrable (fun t => hk W t w p) MeasureTheory.volume 0 1 :=
    hc.intervalIntegrable_of_Icc zero_le_one
  have e := (A.comp (ContinuousAlternatingMap.apply ℝ V F v)).intervalIntegral_comp_comm hi
  have e' : A (hom W w p v) = ∫ t in (0 : ℝ)..1, A (hk W t w p v) := e.symm
  rw [e']
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := K)
    (f := fun t => A (hk W t w p v)) fun t ht => hb t (by
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact Set.Ioc_subset_Icc_self ht)
  simpa using this

theorem UpperTheory.V.Lit.Geo.homBd :
    HomBd := by
  intro E _ _ _ a ho U Ξ Y C hY W hW q
  obtain ⟨B₁, hB₁, h₁⟩ := corrBd E a U Ξ C (q + 1)
  obtain ⟨B₂, hB₂, h₂⟩ := fieldDer E a U Y C hY
  obtain ⟨B₃, hB₃, h₃⟩ := fieldBd E a U Y C hY W hW
  obtain ⟨hfl, hfe⟩ := fieldFlow E a ho U Ξ Y C hY W hW
  refine ⟨B₁ * B₂ * (B₃ * 2) ^ q, by positivity, fun α α' w hα hw hw' g M hM hb X => ?_⟩
  obtain ⟨y, x, hyx⟩ : ∃ (y : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)),
      (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1 = infGL E a y * finGL E a x :=
    ⟨_, _, (infGL_mul_finGL _).symm⟩
  have hYg : Y (infGL E a y * finGL E a x) = Y g := by
    obtain ⟨t, ht⟩ := (retrFacts E a).1 g
    have := hY.left 1 t g
    rw [map_one, one_mul] at this
    rw [← hyx, ht, this]
  have hp : sand y (hOne E a) ∈ (geo ho U Ξ).Y := ⟨y, rfl⟩
  have e1 := hw' y x X
  rw [(omApply _ _ _ _ (geo ho U Ξ) W hfl q).2 w _ _ hp] at e1
  have e2 : ev (α' X) (infGL E a y * finGL E a x) = mulVecL (Ξ.mat y⁻¹)
      (hom (W (x : GL (Fin a) (Af E) ⧸ U)) (w.1 (x : GL (Fin a) (Af E) ⧸ U)) (sand y (hOne E a))
        fun i => (2 : ℝ) • sand y (hv (X i))) := by
    rw [e1, mulVecL_apply, Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
  rw [hyx, e2]
  refine norm_hom_le _ _ _ _ _ _
    ((hkSmooth _ _ _ (geo ho U Ξ).isOpen _ (hfl.field _) q _ (w.2 _).1).2.2.1 _ hp) fun t ht => ?_
  have ht' : |t| ≤ 1 := abs_le.2 ⟨by linarith [ht.1], ht.2⟩
  obtain ⟨h, hh, hC, hC'⟩ := hY.root g t ht'
  choose v' hv' hv'' using h₃ y x t ht'
  have key := h₁ α w.1 hα hw g y h x M hyx hC hC' hM (hb t ht h hh)
    (Matrix.vecCons (hv (Y g)) fun i => v' ((2 : ℝ) • hv (X i)))
  have e3 : (Matrix.vecCons (W (x : GL (Fin a) (Af E) ⧸ U) (sand y (hOne E a))) fun i =>
      fderiv ℝ (flow (W (x : GL (Fin a) (Af E) ⧸ U)) t) (sand y (hOne E a)) ((2 : ℝ) • sand y (hv (X i)))) =
      fun i => sand y (Matrix.vecCons (hv (Y g)) (fun i => v' ((2 : ℝ) • hv (X i))) i) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Matrix.cons_val_zero]
      rw [hW y x, hYg]
    · simp only [Matrix.cons_val_succ]
      rw [← hv'', map_smul (sand y)]
  rw [mulVecL_apply, hk_apply, e3, hfe y h x t (by rw [hYg]; exact hh)]
  refine key.trans ?_
  rw [Fin.prod_univ_succ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ]
  have b1 : ∏ i, ‖v' ((2 : ℝ) • hv (X i))‖ ≤ (B₃ * 2) ^ q * ∏ i, ‖hv (X i)‖ := by
    calc ∏ i, ‖v' ((2 : ℝ) • hv (X i))‖ ≤ ∏ i : Fin q, (B₃ * 2) * ‖hv (X i)‖ :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => (hv' _).trans_eq (by
            rw [norm_smul, Real.norm_ofNat, mul_assoc])
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have b2 := mul_le_mul (h₂ g).1 b1 (Finset.prod_nonneg fun _ _ => norm_nonneg _) hB₂
  calc _ ≤ B₁ * M * (B₂ * ((B₃ * 2) ^ q * ∏ i, ‖hv (X i)‖)) := mul_le_mul_of_nonneg_left b2 (mul_nonneg hB₁ hM)
    _ = _ := by ring
end
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.pbBd :
    PbBd := by
  intro E _ _ _ a ho U Ξ Y C hY W hW q
  obtain ⟨B₁, hB₁, hc⟩ := corrBd E a U Ξ C q
  obtain ⟨B₂, hB₂, hf⟩ := fieldBd E a U Y C hY W hW
  obtain ⟨hfl, hflow⟩ := fieldFlow E a ho U Ξ Y C hY W hW
  refine ⟨B₁ * (2 * B₂) ^ q, by positivity, fun α α' w hα hw hw' g M hM hb X => ?_⟩
  obtain ⟨y, x, hyx⟩ : ∃ (y : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)),
      (retractOne g : KernelIndexFullLattice.G1 E a).1 = infGL E a y * finGL E a x :=
    ⟨_, _, (GlobalTheory.CuspRep.infGL_mul_finGL _).symm⟩
  have hYg : Y (infGL E a y * finGL E a x) = Y g := by
    obtain ⟨t, ht⟩ := (retrFacts E a).1 g
    rw [← hyx, ht, ← hY.left 1 t g, map_one, one_mul]
  obtain ⟨h, hh, h1, h2⟩ := hY.root g 1 (by simp)
  have hbd := hb h (by rw [hh, one_smul])
  have hpt := hflow y h x 1 (by rw [hYg]; exact hh)
  choose v' hv' hv'' using hf y x 1 (by simp)
  have hmem : sand y (hOne E a) ∈ (geo ho U Ξ).Y := sand_mem_cone y hOne_mem_cone
  have e1 := hw' y x X
  rw [(omApply _ _ _ _ (geo ho U Ξ) W hfl q).1 w _ _ hmem, pb_apply, hpt] at e1
  have e2 : (fun i => fderiv ℝ (flow (W (x : GL (Fin a) (Af E) ⧸ U)) 1) (sand y (hOne E a))
      ((2 : ℝ) • sand y (hv (X i)))) = fun i => sand y (v' ((2 : ℝ) • hv (X i))) := by
    funext i
    rw [← hv'', map_smul (sand y)]
  rw [e2] at e1
  have e3 := hc α w.1 hα hw g y h x M hyx h1 h2 hM hbd (fun i => v' ((2 : ℝ) • hv (X i)))
  have e4 : Ξ.mat y⁻¹ * Ξ.mat y = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  rw [e1, Matrix.mulVec_mulVec, e4, Matrix.one_mulVec, ← hyx] at e3
  refine e3.trans ?_
  have e5 : ∏ i, ‖v' ((2 : ℝ) • hv (X i))‖ ≤ (2 * B₂) ^ q * ∏ i, ‖hv (X i)‖ := by
    calc ∏ i, ‖v' ((2 : ℝ) • hv (X i))‖ ≤ ∏ i, (2 * B₂) * ‖hv (X i)‖ := by
          refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => (hv' _).trans (le_of_eq ?_)
          rw [norm_smul, Real.norm_ofNat]
          ring
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc B₁ * M * ∏ i, ‖v' ((2 : ℝ) • hv (X i))‖ ≤ B₁ * M * ((2 * B₂) ^ q * ∏ i, ‖hv (X i)‖) :=
        mul_le_mul_of_nonneg_left e5 (mul_nonneg hB₁ hM)
    _ = _ := by ring
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Geo.Cs
open scoped Topology

theorem UpperTheory.V.Lit.Geo.Cs.loc :
    UpperTheory.V.Lit.Geo.Cs.Loc := by
  intro E _ _ _ a ho U Ξ f lam hf hl Φ hD hΦ q k A B R hA hB s p hp hR
  obtain ⟨c, hc⟩ := UpperTheory.V.Lit.Geo.Cs.locBd E a p hp
  obtain ⟨D, hD0, hmv⟩ := UpperTheory.V.Lit.Geo.Cs.move E a ho U Ξ q k c
  obtain ⟨B₀, hB₀⟩ := hl.bdd c
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective s
  have hcont : ContinuousAt (Φ (y : GL (Fin a) (Af E) ⧸ U)) p :=
    ((hΦ.1 _).continuousOn.continuousAt (ho.mem_nhds hp))
  have hev : ∀ᶠ x in 𝓝 p, R < Φ (y : GL (Fin a) (Af E) ⧸ U) x := hcont.eventually (lt_mem_nhds hR)
  refine ⟨_, hc.and hev, D * Real.exp (B * (B₀ + |lam (finGL E a y)|)), fun M hM w hw x hx => ?_⟩
  obtain ⟨⟨h, hh, rfl⟩, hx⟩ := hx
  rw [hD h y] at hx
  have h1 := hw h y hx.le
  have h2 := hmv w 1 y h _ hh (by rw [one_mul]; exact h1)
  rw [Tw_one] at h2
  refine h2.mono ?_
  rw [mul_assoc, mul_comm _ M]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hM) hD0
  have h3 : |lam (pt h y)| ≤ B₀ + |lam (finGL E a y)| := by
    rw [pt, hl.add]
    exact (abs_add_le _ _).trans (add_le_add (hB₀ h hh) le_rfl)
  have h4 := mul_nonneg hA (hf (pt h y))
  have h5 := mul_le_mul_of_nonneg_left h3 hB
  linarith
end
end

section

open UpperTheory.V.Lit.Geo

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor in
open scoped ContDiff Topology in
theorem UpperTheory.V.Lit.Geo.Cs.decP :
    UpperTheory.V.Lit.Geo.Cs.DecP := by
  intro E _ _ _ a ho U Ξ f Y C c f₀ hS W hW lam hl q k B hB
  obtain ⟨hfl, hflow⟩ := fieldFlow E a ho U Ξ Y C hS.fld W hW
  obtain ⟨c₁, hc₁⟩ := Cs.zwSz E a U Y C hS.fld W hW (k + 1)
  obtain ⟨C₁, hC₁, hpb⟩ := Cs.pbSz (HV E a) (Fin Ξ.d → ℂ) q k c₁
  obtain ⟨D₁, hD₁, hmv⟩ := Cs.move E a ho U Ξ q k C
  obtain ⟨B₁, hB₁⟩ := hl.bdd C
  refine ⟨C₁ * D₁ * Real.exp (B * B₁), by positivity, fun A M hA hM w hw g x hg => ?_⟩
  obtain ⟨hF, hfe, hops⟩ := Cs.twOps E a ho U Ξ W hfl g x
  obtain ⟨hsm, hpe⟩ := (hops q).1 w
  obtain ⟨h, hh, hb⟩ := hS.root (Cs.pt g x) 1 (by simp)
  have hone : hOne E a ∈ cone E a := hOne_mem_cone
  have hpt : flow (Cs.Zw U W g x) 1 (hOne E a) = sand h (hOne E a) := by
    rw [hfe, hflow g h x 1 hh, ← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel_left]
  have hup : f (Cs.pt g x) + c ≤ f (Cs.pt (g * h) x) := by
    rw [Cs.pt_mul]
    exact hS.up _ h hg (by rw [hh, one_smul])
  have hlam : |lam (Cs.pt (g * h) x)| ≤ |lam (Cs.pt g x)| + B₁ := by
    rw [Cs.pt_mul, hl.add]
    exact (abs_add_le _ _).trans (add_le_add le_rfl (hB₁ h hb))
  have h1 := hmv w g x h _ hb (hw (g * h) x (by linarith [hS.c_pos]))
  rw [← hpt] at h1
  have hmem : flow (Cs.Zw U W g x) 1 (hOne E a) ∈ cone E a := hF.2 _ hone 1 ⟨zero_le_one, le_rfl⟩
  have h2 := hpb (Cs.Zw U W g x) 1 (Cs.Tw U Ξ w.1 g x) (hOne E a) _ (by simp)
    (hF.1.contDiffAt (ho.mem_nhds hone)) (hc₁ g x) (hsm.contDiffAt (ho.mem_nhds hmem)) h1
  refine (h2.congr (Filter.eventuallyEq_of_mem (ho.mem_nhds hone) fun p hp => (hpe p hp).symm)).mono ?_
  have he : Real.exp (B * |lam (Cs.pt (g * h) x)| - A * f (Cs.pt (g * h) x)) ≤
      Real.exp (B * B₁) * Real.exp (-(A * c)) * Real.exp (B * |lam (Cs.pt g x)| - A * f (Cs.pt g x)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith [mul_le_mul_of_nonneg_left hlam hB, mul_le_mul_of_nonneg_left hup hA]
  calc _ = C₁ * D₁ * M * Real.exp (B * |lam (Cs.pt (g * h) x)| - A * f (Cs.pt (g * h) x)) := by ring
    _ ≤ C₁ * D₁ * M * (Real.exp (B * B₁) * Real.exp (-(A * c)) *
        Real.exp (B * |lam (Cs.pt g x)| - A * f (Cs.pt g x))) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped Topology
open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.Cs.decK :
    UpperTheory.V.Lit.Geo.Cs.DecK := by
  intro E _ _ _ a ho U Ξ f Y C c f₀ hS W hW lam hl q k A B hA hB
  obtain ⟨hfl, hflow⟩ := fieldFlow E a ho U Ξ Y C hS.fld W hW
  obtain ⟨z, hz⟩ := zwSz E a U Y C hS.fld W hW (k + 1)
  obtain ⟨C₁, hC₁, hhom⟩ := homSz (HV E a) (Fin Ξ.d → ℂ) q k z
  obtain ⟨D₁, hD₁, hmv⟩ := move E a ho U Ξ (q + 1) k C
  obtain ⟨L, hL⟩ := hl.bdd C
  refine ⟨C₁ * D₁ * Real.exp (B * L + A * C), by positivity, fun M hM w hw g x hg => ?_⟩
  obtain ⟨hfield, hfz, hq⟩ := twOps E a ho U Ξ W hfl g x
  have hsm := ((hq (q + 1)).1 w).1
  have heq := (hq q).2 w
  have key : ∀ t ∈ Set.Icc (0 : ℝ) 1, Sz k (Tw U Ξ w.1 g x) (flow (Zw U W g x) t (hOne E a))
      (D₁ * (M * (Real.exp (B * L + A * C) * Real.exp (B * |lam (pt g x)| - A * f (pt g x))))) := by
    intro t ht
    have ht' : |t| ≤ 1 := abs_le.2 ⟨by linarith [ht.1], ht.2⟩
    obtain ⟨h, hh, h1, h2⟩ := hS.root (pt g x) t ht'
    have hn := abs_le.1 (hS.near (pt g x) t h ht' hh)
    have e : flow (Zw U W g x) t (hOne E a) = sand h (hOne E a) := by
      rw [hfz, hflow g h x t hh, ← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel_left]
    rw [e]
    refine hmv w g x h _ ⟨h1, h2⟩ ((hw (g * h) x (by rw [pt_mul]; linarith [hn.1])).mono ?_)
    refine mul_le_mul_of_nonneg_left ?_ hM
    rw [← Real.exp_add, pt_mul, hl.add]
    refine Real.exp_le_exp.2 ?_
    have b1 : |lam (pt g x) + lam (infGL E a h)| ≤ L + |lam (pt g x)| := by
      linarith [abs_add_le (lam (pt g x)) (lam (infGL E a h)), hL h ⟨h1, h2⟩]
    have b2 := mul_le_mul_of_nonneg_left b1 hB
    have b3 := mul_le_mul_of_nonneg_left hn.1 hA
    linarith
  have main := hhom (cone E a) (Zw U W g x) (Tw U Ξ w.1 g x) _ ho hfield hsm (hOne E a) hOne_mem_cone (hz g x) key
  refine (main.congr ?_).mono (le_of_eq (by ring))
  filter_upwards [ho.mem_nhds hOne_mem_cone] with p hp
  exact (heq p hp).symm
end
