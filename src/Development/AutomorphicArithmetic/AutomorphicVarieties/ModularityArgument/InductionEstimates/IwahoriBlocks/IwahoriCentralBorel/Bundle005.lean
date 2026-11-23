module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.LevBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.ParLaw
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.PiHomExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.IndProdG
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle091
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSConjSpaceR

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem finite_projection_one {K : Type} [Field K] [NumberField K] {n : ℕ} : fin1 (1 : FA K n) = 1 :=
  map_one (MultiplicityOne.finProj K n)

private theorem finite_adele_inclusion_mul {K : Type} [Field K] [NumberField K] {n : ℕ} (a b : FA K n) : fin1 (a * b) = fin1 a * fin1 b :=
  map_mul (MultiplicityOne.finProj K n) a b

private theorem zt0 {K : Type} [Field K] [NumberField K] : zt K 0 = 1 := by
  have h : (⟨Real.exp 0, Real.exp_pos 0⟩ : {r : ℝ // 0 < r}) = 1 := Subtype.ext (by simp)
  rw [zt, h, map_one]

private theorem lv0 {K : Type} [Field K] [NumberField K] (a b : G1 K 2) :
    ((lv a b 0 : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) =
      blk (a : AdelicGLn.AdelicGL K 2) (b : AdelicGLn.AdelicGL K 2) := by
  rw [blkLaws.1, neg_zero, zt0, mul_one, mul_one]

private theorem hh0 {K : Type} [Field K] [NumberField K] (a b : G1 K 2) (x : G1 K (2 + 2)) :
    HH (lv a b 0 * x) = HH x := by
  have h := (hpSpec (K := K)).1 0 a b 0 x
  have h0 : (nn 0 : G1 K (2 + 2)) = 1 := unipOne_zero 2
  rwa [h0, one_mul, zero_add] at h

private theorem sec_ray {K : Type} [Field K] [NumberField K] {μ₂ : Measure (G1 K 2)} {τ₁ τ₂ : Submodule ℂ (L2 μ₂)}
    {f : G1 K (2 + 2) → ℂ} (hs : IsSec τ₁ τ₂ f) (t : ℝ) (g : G1 K (2 + 2)) : f (lv 1 1 t * g) = f g := by
  refine hs.ray ⟨Real.exp t, Real.exp_pos t⟩ _ g ?_
  have h : (⟨Real.exp (-t), Real.exp_pos (-t)⟩ : {r : ℝ // 0 < r}) = (⟨Real.exp t, Real.exp_pos t⟩ : {r : ℝ // 0 < r})⁻¹ := by
    apply Subtype.ext
    change Real.exp (-t) = (Real.exp t)⁻¹
    rw [Real.exp_neg]
  rw [Subgroup.coe_mul, blkLaws.1, zt, zt, h]
  simp

private theorem reps_comb {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    (τ : Submodule ℂ (L2 μ)) {ι : Type} (s : Finset ι) (φ : ι → G1 K n → ℂ) (c : ι → ℂ)
    (h : ∀ i, ∃ v ∈ τ, Reps μ v (φ i)) : ∃ v ∈ τ, Reps μ v (fun y => ∑ i ∈ s, c i * φ i y) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, τ.zero_mem, ?_⟩
    filter_upwards [MeasureTheory.QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam K n) μ) (Lp.coeFn_zero ℂ 2 (quotientMeasure (Gam K n) μ))] with y hy
    simpa only [Finset.sum_empty, Pi.zero_apply] using hy
  | insert i s hi ih =>
    obtain ⟨v, hv, hr⟩ := ih
    obtain ⟨u, hu, hq⟩ := h i
    refine ⟨c i • u + v, τ.add_mem (τ.smul_mem _ hu) hv, ?_⟩
    filter_upwards [MeasureTheory.QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam K n) μ) (Lp.coeFn_add (c i • u) v),
      MeasureTheory.QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam K n) μ) (Lp.coeFn_smul (c i) u), hr, hq] with y e₁ e₂ e₃ e₄
    rw [e₁, Pi.add_apply, e₂, Pi.smul_apply, e₃, e₄, Finset.sum_insert hi, smul_eq_mul]

private theorem flat_lv {K : Type} [Field K] [NumberField K] (f : G1 K (2 + 2) → ℂ) (a b : G1 K 2) (x : G1 K (2 + 2)) :
    flat 0 f (lv a b 0 * x) = Complex.exp (2 * (HH x : ℂ)) * f (lv a b 0 * x) := by
  simp only [flat, zero_add]
  rw [show HP 2 2 (lv a b 0 * x) = HH x from hh0 a b x]

private theorem val_mem {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {μ₂ : Measure (G1 K 2)} [μ₂.IsHaarMeasure]
    {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {κ : Measure (archCompact K (2 + 2))} {e : archCompact K (2 + 2) → ℂ} {κ₂ p₁ p₂ k₀}
    (hL : ArchLine τ₁ τ₂ κ e κ₂ p₁ p₂ k₀) {r : ℕ} (w : Fin r → Pl K) (ι₄ : GS (2 + 2) w →* FA K (2 + 2))
    (hw : Function.Injective w) (h₄ : IsEmb w ι₄) {f : G1 K (2 + 2) → ℂ} (hs : IsSec τ₁ τ₂ f) (hfa : FixA κ e f)
    {U : ∀ v : Pl K, Subgroup (Gw (2 + 2) v)} (hU : Lev U) (hfU : FixF (levOn (im w) U) f) (g : GS (2 + 2) w) :
    (fun m : G1 K 2 × G1 K 2 => flat 0 f (lv m.1 m.2 0 * arc1 k₀ * fin1 (ι₄ g))) ∈
      tensFn (Xs μ₂ τ₁ κ₂ p₁ (im w)) (Xs μ₂ τ₂ κ₂ p₂ (im w)) := by
  obtain ⟨d, φ, ψ, hφ, hψ, hx⟩ := hs.levi (arc1 k₀ * fin1 (ι₄ g))
  have hx' : ∀ a b, f (lv a b 0 * arc1 k₀ * fin1 (ι₄ g)) = ∑ i, φ i a * ψ i b := fun a b =>
    hx a b _ (by rw [mul_assoc, Subgroup.coe_mul (x := lv a b 0), lv0])
  obtain ⟨U₂, hU₂, hlev⟩ := levBlock w ι₄ hw h₄ U hU g
  have hv := hL.val f hs hfa (ι₄ g)
  have hcl : Continuous fun p : G1 K 2 × G1 K 2 => f (lv p.1 p.2 0 * arc1 k₀ * fin1 (ι₄ g)) :=
    hs.cont.comp (((blkLaws (K := K)).2.2.2.1.comp
      (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))).mul continuous_const |>.mul continuous_const)
  have hsplit₁ : ∀ a b (u : G1 K 2), lv (a * u) b 0 = lv a b 0 * lv u 1 0 := fun a b u => by
    rw [blkLaws.2.1]; simp
  have hsplit₂ : ∀ a b (u : G1 K 2), lv a (b * u) 0 = lv a b 0 * lv 1 u 0 := fun a b u => by
    rw [blkLaws.2.1]; simp
  have hF : (fun m : G1 K 2 × G1 K 2 => flat 0 f (lv m.1 m.2 0 * arc1 k₀ * fin1 (ι₄ g))) =
      Complex.exp (2 * (HH (arc1 k₀ * fin1 (ι₄ g)) : ℂ)) • fun m : G1 K 2 × G1 K 2 => f (lv m.1 m.2 0 * arc1 k₀ * fin1 (ι₄ g)) := by
    funext m
    rw [mul_assoc, flat_lv]
    simp [mul_assoc]
  rw [hF]
  refine Submodule.smul_mem _ _ ((tensLaws _ _).2 _ d φ ψ (fun x => hx' x.1 x.2) (fun b => ?_) (fun a => ?_))
  · refine Submodule.subset_span ⟨hcl.comp (continuous_id.prodMk continuous_const), ?_, hv.1 b, U₂, hU₂, fun u hu a => ?_⟩
    · have h := reps_comb μ₂ τ₁ Finset.univ φ (fun i => ψ i b) (fun i => let ⟨v, hv, hr⟩ := (hφ i).2; ⟨v, hv, hr⟩)
      simpa only [hx', mul_comm] using h
    · obtain ⟨u', hu', hk⟩ := hlev u hu 1 (one_mem _)
      have h1 := hk k₀
      rw [finite_projection_one] at h1
      have h2 : lv (a * fin1 u) b 0 * arc1 k₀ * fin1 (ι₄ g) = lv a b 0 * arc1 k₀ * fin1 (ι₄ g) * fin1 u' := by
        rw [hsplit₁, mul_assoc (lv a b 0), mul_assoc (lv a b 0), h1]
        simp only [mul_assoc]
      show f (lv (a * fin1 u) b 0 * arc1 k₀ * fin1 (ι₄ g)) = f (lv a b 0 * arc1 k₀ * fin1 (ι₄ g))
      rw [h2]
      exact hfU u' hu' _
  · refine Submodule.subset_span ⟨hcl.comp (continuous_const.prodMk continuous_id), ?_, hv.2 a, U₂, hU₂, fun u hu b => ?_⟩
    · have h := reps_comb μ₂ τ₂ Finset.univ ψ (fun i => φ i a) (fun i => let ⟨v, hv, hr⟩ := (hψ i).2; ⟨v, hv, hr⟩)
      simpa only [hx'] using h
    · obtain ⟨u', hu', hk⟩ := hlev 1 (one_mem _) u hu
      have h1 := hk k₀
      rw [finite_projection_one] at h1
      have h2 : lv a (b * fin1 u) 0 * arc1 k₀ * fin1 (ι₄ g) = lv a b 0 * arc1 k₀ * fin1 (ι₄ g) * fin1 u' := by
        rw [hsplit₂, mul_assoc (lv a b 0), mul_assoc (lv a b 0), h1]
        simp only [mul_assoc]
      show f (lv a (b * fin1 u) 0 * arc1 k₀ * fin1 (ι₄ g)) = f (lv a b 0 * arc1 k₀ * fin1 (ι₄ g))
      rw [h2]
      exact hfU u' hu' _

private theorem law_eq {K : Type} [Field K] [NumberField K] {μ₂ : Measure (G1 K 2)}
    {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {r : ℕ} (w : Fin r → Pl K) (ι₂ : GS 2 w →* FA K 2) (ι₄ : GS (2 + 2) w →* FA K (2 + 2))
    (hw : Function.Injective w) (h₂ : IsEmb w ι₂) (h₄ : IsEmb w ι₄) {f : G1 K (2 + 2) → ℂ} (hs : IsSec τ₁ τ₂ f)
    (k₀ : archCompact K (2 + 2)) (p : ∀ i, PW (w i)) (g : GS (2 + 2) w) (m : G1 K 2 × G1 K 2) :
    flat 0 f (lv m.1 m.2 0 * arc1 k₀ * fin1 (ι₄ (piIncl (fun i => PW (w i)) p * g))) =
      (dS w p : ℂ) * flat 0 f (lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) 0 * arc1 k₀ * fin1 (ι₄ g)) := by
  obtain ⟨hA, hB⟩ := parLaw w ι₂ ι₄ hw h₂ h₄
  obtain ⟨X, t, hX, ht⟩ := hB p
  obtain ⟨X', hX'⟩ := hA m.1 m.2 0 X
  have hc : Commute (arc1 k₀) (fin1 (ι₄ (piIncl (fun i => PW (w i)) p))) := (levLaws (K := K) (2 + 2) (im w)).2.2.1 k₀ _
  have key : lv m.1 m.2 0 * arc1 k₀ * fin1 (ι₄ (piIncl (fun i => PW (w i)) p * g)) =
      nn X' * lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t * (arc1 k₀ * fin1 (ι₄ g)) := by
    have hl : lv m.1 m.2 0 * lv (blocks ι₂ p).1 (blocks ι₂ p).2 t = lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t := by
      rw [blkLaws.2.1, zero_add]
    rw [map_mul, finite_adele_inclusion_mul, ← hl]
    calc lv m.1 m.2 0 * arc1 k₀ * (fin1 (ι₄ (piIncl (fun i => PW (w i)) p)) * fin1 (ι₄ g))
        = lv m.1 m.2 0 * (arc1 k₀ * fin1 (ι₄ (piIncl (fun i => PW (w i)) p))) * fin1 (ι₄ g) := by simp only [mul_assoc]
      _ = lv m.1 m.2 0 * (fin1 (ι₄ (piIncl (fun i => PW (w i)) p)) * arc1 k₀) * fin1 (ι₄ g) := by rw [hc.eq]
      _ = (lv m.1 m.2 0 * nn X) * lv (blocks ι₂ p).1 (blocks ι₂ p).2 t * (arc1 k₀ * fin1 (ι₄ g)) := by
          rw [hX]; simp only [mul_assoc]
      _ = _ := by rw [hX']; simp only [mul_assoc]
  have hray : lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t =
      lv 1 1 t * lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) 0 := by
    rw [blkLaws.2.1]; simp
  have hf : f (nn X' * lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t * (arc1 k₀ * fin1 (ι₄ g))) =
      f (lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) 0 * (arc1 k₀ * fin1 (ι₄ g))) := by
    rw [mul_assoc, hs.unip, hray, mul_assoc, sec_ray hs]
  have hh := (hpSpec (K := K)).1 X' (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t (arc1 k₀ * fin1 (ι₄ g))
  rw [key, mul_assoc (lv _ _ 0), flat_lv, ← ht]
  simp only [flat, zero_add]
  rw [show HP 2 2 (nn X' * lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t * (arc1 k₀ * fin1 (ι₄ g))) = t + HH (arc1 k₀ * fin1 (ι₄ g)) from hh, hf]
  push_cast
  rw [mul_add, Complex.exp_add]
  ring

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.evMem :
    ∀ {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (κ : Measure (archCompact K (2 + 2))) (e : archCompact K (2 + 2) → ℂ) κ₂ p₁ p₂ k₀, Pair μ₂ τ₁ τ₂ → ArchLine τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ →
      ∀ {r : ℕ} (w : Fin r → Pl K) (ι₂ : GS 2 w →* FA K 2) (ι₄ : GS (2 + 2) w →* FA K (2 + 2)), Function.Injective w → IsEmb w ι₂ → IsEmb w ι₄ →
      ∀ φ ∈ Zs τ₁ τ₂ κ e (im w), ev ι₄ k₀ φ ∈ IndF (piIncl fun i => PW (w i)) (xS ι₂) (tensFn (Xs μ₂ τ₁ κ₂ p₁ (im w)) (Xs μ₂ τ₂ κ₂ p₂ (im w))) := by
  intro K _ _ _ μ₂ _ τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ _ hL r w ι₂ ι₄ hw h₂ h₄ φ hφ
  obtain ⟨hiff, hsm⟩ := zMem μ₂ τ₁ τ₂ κ e hL.idem
  have hop := (hsm w ι₄ hw h₄ φ hφ).1
  obtain ⟨f, hs, hfa, ⟨U, hU, hfU⟩, rfl⟩ := (hiff _ φ).1 hφ
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · refine ⟨fun g => val_mem hL w ι₄ hw h₄ hs hfa hU hfU g, fun p g => ?_⟩
    funext m
    have h := law_eq (τ₁ := τ₁) (τ₂ := τ₂) w ι₂ ι₄ hw h₂ h₄ hs k₀ p g m
    simpa [ev, xS, twist, rightReg, LinearMap.funLeft] using h
  · have hst : ∀ g, rS ι₄ g (flat 0 f) = flat 0 f →
        rightReg ℂ (GS (2 + 2) w) (G1 K 2 × G1 K 2 → ℂ) g (ev ι₄ k₀ (flat 0 f)) = ev ι₄ k₀ (flat 0 f) := by
      intro g hg
      conv_rhs => rw [← hg]
      funext x m
      simp [ev, rS, rightReg, LinearMap.funLeft, mul_assoc]
    show IsOpen {g | rightReg ℂ (GS (2 + 2) w) (G1 K 2 × G1 K 2 → ℂ) g (ev ι₄ k₀ (flat 0 f)) = ev ι₄ k₀ (flat 0 f)}
    refine isOpen_iff_mem_nhds.2 fun g₀ hg₀ => ?_
    have h1 : (1 : GS (2 + 2) w) ∈ {g | rS ι₄ g (flat 0 f) = flat 0 f} := by simp
    have hn : (fun x => g₀⁻¹ * x) ⁻¹' {g | rS ι₄ g (flat 0 f) = flat 0 f} ∈ 𝓝 g₀ :=
      ((continuous_const.mul continuous_id).continuousAt (x := g₀)).preimage_mem_nhds
        (hop.mem_nhds (by simpa using h1))
    filter_upwards [hn] with x hx
    have h2 := hst _ hx
    have h3 : x = g₀ * (g₀⁻¹ * x) := by group
    show rightReg ℂ (GS (2 + 2) w) (G1 K 2 × G1 K 2 → ℂ) x _ = _
    rw [h3, map_mul, Module.End.mul_apply, h2]
    exact hg₀
end

section

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem ray_lv {K : Type} [Field K] [NumberField K] {μ₂ : Measure (G1 K 2)} {τ₁ τ₂ : Submodule ℂ (L2 μ₂)}
    {f : G1 K (2 + 2) → ℂ} (hf : IsSec τ₁ τ₂ f) (t : ℝ) (g : G1 K (2 + 2)) : f (lv 1 1 t * g) = f g := by
  refine hf.ray ⟨Real.exp t, Real.exp_pos t⟩ ?_ g ?_
  have h : (⟨Real.exp (-t), Real.exp_pos _⟩ : {r : ℝ // 0 < r}) = (⟨Real.exp t, Real.exp_pos t⟩ : {r : ℝ // 0 < r})⁻¹ :=
    Subtype.ext (Real.exp_neg t)
  rw [Subgroup.coe_mul, blkLaws.1, Subgroup.coe_one, one_mul, one_mul, zt, zt, h]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.evInj :
    ∀ {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (κ : Measure (archCompact K (2 + 2))) (e : archCompact K (2 + 2) → ℂ) κ₂ p₁ p₂ k₀, ArchLine τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ →
      ∀ {r : ℕ} (w : Fin r → Pl K) (ι₄ : GS (2 + 2) w →* FA K (2 + 2)), Function.Injective w → IsEmb w ι₄ →
      ∀ φ ∈ Zs τ₁ τ₂ κ e (im w), ev ι₄ k₀ φ = 0 → φ = 0 := by
  intro K _ _ _ μ₂ _ τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ hA r w ι₄ hw hι φ hφ h0
  obtain ⟨f, hf, hfa, ⟨U, -, hU⟩, rfl⟩ := ((zMem μ₂ τ₁ τ₂ κ e hA.idem).1 _ φ).1 hφ
  have h1 : ∀ g m₁ m₂, f (lv m₁ m₂ 0 * arc1 k₀ * fin1 (ι₄ g)) = 0 := fun g m₁ m₂ =>
    (mul_eq_zero.1 (congrFun (congrFun h0 g) (m₁, m₂))).resolve_left (Complex.exp_ne_zero _)
  obtain ⟨ι₂, hι₂⟩ := (embEx (K := K) 2 w hw).1
  have hz : f = 0 := by
    refine hA.inj f hf hfa fun h m₁ m₂ => ?_
    obtain ⟨X, a₁, a₂, t, g, u, hu, hd⟩ := finIwa w ι₄ hw hι h k₀
    obtain ⟨X', hX⟩ := (parLaw w ι₂ ι₄ hw hι₂ hι).1 m₁ m₂ 0 X
    have hl : lv m₁ m₂ 0 * lv a₁ a₂ t = lv 1 1 t * lv (m₁ * a₁) (m₂ * a₂) 0 := by
      rw [blkLaws.2.1, blkLaws.2.1, one_mul, one_mul, zero_add, add_zero]
    have he : lv m₁ m₂ 0 * arc1 k₀ * fin1 h =
        nn X' * (lv 1 1 t * (lv (m₁ * a₁) (m₂ * a₂) 0 * arc1 k₀ * fin1 (ι₄ g))) * fin1 u := by
      rw [mul_assoc, hd]
      simp only [← mul_assoc]
      rw [hX, mul_assoc (nn X'), hl, ← mul_assoc (nn X')]
    rw [he, hU u (hu U), hf.unip, ray_lv hf, h1]
  funext x
  rw [hz]
  exact mul_zero _
end

section

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem indF_stable {G H Y : Type} [Group G] [Group H] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace G]
    [IsTopologicalGroup G] (j : H →* G) (y : Representation ℂ H Y) (X : Submodule ℂ Y) (g : G) (f : G → Y)
    (hf : f ∈ IndF j y X) : rightReg ℂ G Y g f ∈ IndF j y X := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hf
  refine ⟨⟨fun x => h1 (x * g), fun h x => ?_⟩, ?_⟩
  · show f (j h * x * g) = y h (f (x * g))
    rw [mul_assoc, h2]
  · have h4 : IsOpen {a : G | rightReg ℂ G Y a f = f} := h3
    have h5 := h4.preimage (f := fun a : G => g⁻¹ * a * g) (by fun_prop)
    show IsOpen {a : G | rightReg ℂ G Y a (rightReg ℂ G Y g f) = rightReg ℂ G Y g f}
    convert h5 using 1
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · intro h
      funext x
      have := congrFun h (x * g⁻¹)
      change f (x * g⁻¹ * a * g) = f (x * g⁻¹ * g) at this
      change f (x * (g⁻¹ * a * g)) = f x
      simpa [mul_assoc] using this
    · intro h
      funext x
      have := congrFun h (x * g)
      change f (x * g * (g⁻¹ * a * g)) = f (x * g) at this
      change f (x * a * g) = f (x * g)
      simpa [mul_assoc] using this

private theorem simple_of_sub {G H Y : Type} [Group G] [Group H] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace G]
    [IsTopologicalGroup G] (j : H →* G) (y : Representation ℂ H Y) (X : Submodule ℂ Y) (y' : Representation ℂ H X)
    (hy : ∀ h v, (y' h v : Y) = y h v)
    (H' : ∀ Q ≤ IndF j y' ⊤, (∀ g, ∀ f ∈ Q, rightReg ℂ G X g f ∈ Q) → Q = ⊥ ∨ Q = IndF j y' ⊤) :
    SimpleIn (rightReg ℂ G Y) (IndF j y X) := by
  refine ⟨fun g f hf => indF_stable j y X g f hf, fun Q hQ hst => ?_⟩
  let Φ : (G → X) →ₗ[ℂ] (G → Y) := X.subtype.compLeft G
  have hΦ : ∀ f x, Φ f x = (f x : Y) := fun _ _ => rfl
  have hmem : ∀ f, f ∈ IndF j y' ⊤ ↔ Φ f ∈ IndF j y X := by
    intro f
    have hs : {a : G | rightReg ℂ G X a f = f} = {a : G | rightReg ℂ G Y a (Φ f) = Φ f} := by
      ext a
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h
        funext x
        exact congrArg Subtype.val (congrFun h x)
      · intro h
        funext x
        exact Subtype.ext (congrFun h x)
    constructor
    · rintro ⟨⟨-, h2⟩, h3⟩
      refine ⟨⟨fun x => (f x).2, fun h x => ?_⟩, ?_⟩
      · rw [hΦ, hΦ, h2, hy]
      · have h4 : IsOpen {a : G | rightReg ℂ G X a f = f} := h3
        rw [hs] at h4
        exact h4
    · rintro ⟨⟨-, h2⟩, h3⟩
      refine ⟨⟨fun x => trivial, fun h x => Subtype.ext ?_⟩, ?_⟩
      · rw [hy]
        exact h2 h x
      · have h4 : IsOpen {a : G | rightReg ℂ G Y a (Φ f) = Φ f} := h3
        rw [← hs] at h4
        exact h4
  have hsurj : ∀ F ∈ IndF j y X, ∃ f, Φ f = F := fun F hF => ⟨fun x => ⟨F x, hF.1.1 x⟩, rfl⟩
  rcases H' (Q.comap Φ) (fun f hf => (hmem f).2 (hQ hf)) (fun g f hf => hst g (Φ f) hf) with h | h
  · left
    rw [eq_bot_iff]
    intro F hF
    obtain ⟨f, rfl⟩ := hsurj F (hQ hF)
    have : f ∈ Q.comap Φ := hF
    rw [h, Submodule.mem_bot] at this
    rw [this, map_zero]
    exact Submodule.zero_mem _
  · right
    refine le_antisymm hQ fun F hF => ?_
    obtain ⟨f, rfl⟩ := hsurj F hF
    have : f ∈ Q.comap Φ := by
      rw [h]
      exact (hmem f).2 hF
    exact this

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.indAmb :
    ∀ {r : ℕ} {G : Fin r → Type} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] (P : ∀ i, Subgroup (G i)) {Y : Type} [AddCommGroup Y] [Module ℂ Y]
      (y : Representation ℂ (∀ i, P i) Y) (X : Submodule ℂ Y), SimpleIn y X → (∀ v ∈ X, IsOpen {p : ∀ i, P i | y p v = v}) →
      (∀ i, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (P i) V) (f : V →ₗ[ℂ] Y), LocOk (P i) ρ ∧ f ≠ 0 ∧ (∀ v, f v ∈ X) ∧
        ∀ p v, f (ρ p v) = y (Pi.mulSingle i p) (f v)) →
      SimpleIn (rightReg ℂ (∀ i, G i) Y) (IndF (piIncl P) y X) := by
  intro r G _ _ _ P Y _ _ y X hX hop hloc
  by_cases h0 : X = ⊥
  · refine ⟨fun g f hf => indF_stable _ y X g f hf, fun Q hQ _ => Or.inl ?_⟩
    rw [eq_bot_iff]
    intro F hF
    rw [Submodule.mem_bot]
    funext x
    have := (hQ hF).1.1 x
    rw [h0, Submodule.mem_bot] at this
    exact this
  let y' : Representation ℂ ((∀ i, P i) × PUnit.{1}) X := (GlobalTheory.PRep.sub y X hX.1).comp (MonoidHom.fst _ _)
  have hy : ∀ a (v : X), (y' a v : Y) = y a.1 v := fun _ _ => rfl
  have hirr : y'.IsIrreducible := by
    have : Nontrivial X := Submodule.nontrivial_iff_ne_bot.2 h0
    refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
    · exact bot_ne_top (α := Submodule ℂ X) (congrArg Subrepresentation.toSubmodule h)
    · rcases hX.2 (S.toSubmodule.map X.subtype) (Submodule.map_subtype_le _ _) (by
        rintro g _ ⟨v, hv, rfl⟩
        exact ⟨y' (g, 1) v, S.apply_mem_toSubmodule _ hv, rfl⟩) with h | h
      · left
        apply Subrepresentation.toSubmodule_injective
        apply Submodule.map_injective_of_injective X.injective_subtype
        rw [h]
        exact (Submodule.map_bot _).symm
      · right
        apply Subrepresentation.toSubmodule_injective
        apply Submodule.map_injective_of_injective X.injective_subtype
        rw [h]
        exact (Submodule.map_subtype_top _).symm
  have key := indProdG r P y' hirr (fun v => by
      convert hop v v.2 using 2 with p
      exact funext fun p => propext Subtype.ext_iff) (fun i => by
      obtain ⟨V, _, _, ρ, f, h1, h2, h3, h4⟩ := hloc i
      refine ⟨V, inferInstance, inferInstance, ρ, f.codRestrict X h3, h1, fun h => h2 ?_, fun p v => Subtype.ext (h4 p v)⟩
      ext v
      exact congrArg Subtype.val (LinearMap.congr_fun h v))
  refine simple_of_sub (piIncl P) y X (y'.comp (MonoidHom.inl _ _)) (fun _ _ => rfl) fun Q hQ hst => key Q hQ hst fun c f hf => ?_
  have : (fun x => y' (1, c) (f x)) = f := by
    funext x
    apply Subtype.ext
    rw [hy]
    simp
  rw [this]
  exact hf
end

section

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

section SlopeTestRemainingChoices

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.xMem :
    ∀ {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (μ : Measure (G1 K 2)) [μ.IsHaarMeasure] (τ : Submodule ℂ (L2 μ)) (κ : Measure (archCompact K 2)) (p : archCompact K 2 → ℂ), IdemA κ p → (∀ S φ, φ ∈ Xs μ τ κ p S ↔ IsX μ τ κ p S φ) ∧ (CuspIrr μ τ →
      ∀ {r : ℕ} (w : Fin r → Pl K) (ι : GS 2 w →* FA K 2), Function.Injective w → IsEmb w ι → ∀ φ ∈ Xs μ τ κ p (im w), IsOpen {g | rS ι g φ = φ} ∧ ∀ g, rS ι g φ ∈ Xs μ τ κ p (im w)) :=
  _root_.UpperTheory.Reformulated.B.Gul4.xMem
end
