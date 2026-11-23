module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsAppSz
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
import Mathlib.RingTheory.PiTensorProduct
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

@[expose] public section

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

namespace UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private def pol0 (A B : Matrix (Fin a) (Fin a) (Cinf E)) : HV E a →L[ℝ] HV E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => ⟨toL (A * Matrix.of v.1 * star B + B * Matrix.of v.1 * star A), by
        have hv : star (Matrix.of v.1) = Matrix.of v.1 := v.2
        change star (A * Matrix.of v.1 * star B + B * Matrix.of v.1 * star A) =
          A * Matrix.of v.1 * star B + B * Matrix.of v.1 * star A
        simp only [star_add, star_mul, star_star, hv, mul_assoc]
        exact add_comm _ _⟩
      map_add' := fun p p' => Subtype.ext (by
        change A * (Matrix.of p.1 + Matrix.of p'.1) * star B + B * (Matrix.of p.1 + Matrix.of p'.1) * star A =
          (A * Matrix.of p.1 * star B + B * Matrix.of p.1 * star A) +
            (A * Matrix.of p'.1 * star B + B * Matrix.of p'.1 * star A)
        simp only [mul_add, add_mul]; abel)
      map_smul' := fun c p => Subtype.ext (by
        change A * (c • Matrix.of p.1) * star B + B * (c • Matrix.of p.1) * star A =
          c • (A * Matrix.of p.1 * star B + B * Matrix.of p.1 * star A)
        simp only [mul_smul_comm, smul_mul_assoc, smul_add]) }

private theorem polarization_val (A B : Matrix (Fin a) (Fin a) (Cinf E)) (v : HV E a) :
    Matrix.of (pol0 A B v).1 = A * Matrix.of v.1 * star B + B * Matrix.of v.1 * star A := rfl

private theorem hv_ext {v w : HV E a} (h : Matrix.of v.1 = Matrix.of w.1) : v = w := Subtype.ext h

private theorem polarization_comm (A B : Matrix (Fin a) (Fin a) (Cinf E)) : pol0 A B = pol0 B A :=
  ContinuousLinearMap.ext fun v => hv_ext (by rw [polarization_val, polarization_val, add_comm])

private theorem polarization_add (A A' B : Matrix (Fin a) (Fin a) (Cinf E)) : pol0 (A + A') B = pol0 A B + pol0 A' B :=
  ContinuousLinearMap.ext fun v => hv_ext (by
    change _ = Matrix.of (pol0 A B v).1 + Matrix.of (pol0 A' B v).1
    simp only [polarization_val, star_add, mul_add, add_mul]; abel)

private theorem polarization_smul (c : ℝ) (A B : Matrix (Fin a) (Fin a) (Cinf E)) : pol0 (c • A) B = c • pol0 A B :=
  ContinuousLinearMap.ext fun v => hv_ext (by
    change _ = c • Matrix.of (pol0 A B v).1
    simp only [polarization_val, star_smul, star_trivial c, mul_smul_comm, smul_mul_assoc, smul_add])


variable (E a) in
private def pol : Lie E a →L[ℝ] Lie E a →L[ℝ] HV E a →L[ℝ] HV E a :=
  LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ
    LinearMap.mk₂ ℝ (fun A B : Lie E a => pol0 (Matrix.of A) (Matrix.of B)) (fun A A' B => polarization_add _ _ _)
      (fun c A B => polarization_smul c _ _)
      (fun A B B' => (polarization_comm _ _).trans ((polarization_add _ _ _).trans (congrArg₂ (· + ·) (polarization_comm _ _) (polarization_comm _ _))))
      (fun c A B => (polarization_comm _ _).trans ((polarization_smul c _ _).trans (congrArg (c • ·) (polarization_comm _ _)))))

private theorem pol_sand (g : GL (Fin a) (Cinf E)) :
    sand g = (2⁻¹ : ℝ) • pol E a (toL g.val) (toL g.val) :=
  ContinuousLinearMap.ext fun v => hv_ext (by
    change g.val * Matrix.of v.1 * star g.val =
      (2⁻¹ : ℝ) • (g.val * Matrix.of v.1 * star g.val + g.val * Matrix.of v.1 * star g.val)
    rw [← two_smul ℝ, smul_smul]; norm_num)

private theorem sand_der (c : ℝ → GL (Fin a) (Cinf E)) (X : Lie E a) (h0 : c 0 = 1)
    (hX : HasDerivAt (fun t => toL (c t).val) X 0) :
    HasDerivAt (fun t => sand (c t)) (pol E a X (toL 1)) 0 := by
  have h1 := (((pol E a).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hX).clm_apply hX).const_smul (2⁻¹ : ℝ)
  simp only [Function.comp, h0, Units.val_one] at h1
  have e : pol E a (toL 1) X = pol E a X (toL 1) := polarization_comm _ _
  rw [e, ← two_smul ℝ, smul_smul, show (2⁻¹ : ℝ) * 2 = 1 by norm_num, one_smul] at h1
  exact h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => pol_sand _)

private theorem pol_one (v : HV E a) : pol E a ((2⁻¹ : ℝ) • v.1) (toL 1) (hOne E a) = v := by
  rw [map_smul]
  refine hv_ext ?_
  have hv : star (Matrix.of v.1) = Matrix.of v.1 := v.2
  change (2⁻¹ : ℝ) • (Matrix.of v.1 * 1 * star 1 + 1 * 1 * star (Matrix.of v.1)) = _
  rw [hv, star_one, mul_one, mul_one, one_mul, one_mul, ← two_smul ℝ, smul_smul]; norm_num

private theorem flow_der {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {W : V → V} {p : V}
    (h : DifferentiableAt ℝ W p) (t : ℝ) (v : V) : fderiv ℝ (flow W t) p v = v + t • fderiv ℝ W p v := by
  have h4 : HasFDerivAt (flow W t) (ContinuousLinearMap.id ℝ V + t • fderiv ℝ W p) p :=
    (hasFDerivAt_id p).add (h.hasFDerivAt.const_smul t)
  rw [h4.fderiv]
  rfl

theorem fieldBd : FieldBd := by
  intro E _ _ _ a U Y C hY W hW
  obtain ⟨B, hB, hD⟩ := fieldDer E a U Y C hY
  have ho : IsOpen (cone E a) := isOpen_iff_mem_nhds.2 fun p hp => by
    obtain ⟨τ, -, hτ⟩ := locSec E a p hp
    exact hτ.mono fun x hx => ⟨τ x, hx⟩
  set K : ℝ := ‖(pol E a).flip (toL 1)‖ with hK
  have hK0 : 0 ≤ K := norm_nonneg _
  refine ⟨1 + (K * B + B), by positivity, fun g x t ht v => ?_⟩
  obtain ⟨c, h0, -, -, hX, -⟩ := oneParam E a ((2⁻¹ : ℝ) • v.1)
  obtain ⟨hb, hz⟩ := hD (infGL E a g * finGL E a x)
  obtain ⟨Z, hZ, hd⟩ := hz c _ h0 hX
  have hn : ‖(2⁻¹ : ℝ) • v.1‖ ≤ ‖v‖ := by
    rw [norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) (by norm_num)
  have hs := sand_der c _ h0 hX
  set P := pol E a ((2⁻¹ : ℝ) • v.1) (toL 1) with hP
  set y := hv (Y (infGL E a g * finGL E a x)) with hy
  have hPn : ‖P‖ ≤ K * ‖v‖ :=
    (((pol E a).flip (toL 1)).le_opNorm _).trans (mul_le_mul_of_nonneg_left hn hK0)
  have hWd : DifferentiableAt ℝ (W (x : GL (Fin a) (Af E) ⧸ U)) (sand g (hOne E a)) :=
    ((fieldSm E a U Y C hY W hW x).contDiffAt (ho.mem_nhds ⟨g, rfl⟩)).differentiableAt (by simp)
  have h1 : HasDerivAt (fun r => sand g (sand (c r) (hOne E a))) (sand g v) 0 := by
    have h := (sand g).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hs.clm_apply (hasDerivAt_const (0 : ℝ) (hOne E a)))
    rwa [map_zero, add_zero, hP, pol_one] at h
  have h2 : HasDerivAt (fun r => W (x : GL (Fin a) (Af E) ⧸ U) (sand g (sand (c r) (hOne E a)))) (sand g (P y + Z)) 0 := by
    have h := (sand g).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hs.clm_apply hd)
    simp only [h0, map_one, mul_one, ContinuousLinearMap.one_apply] at h
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
    have e : infGL E a (g * c r) * finGL E a x = infGL E a g * finGL E a x * infGL E a (c r) := by
      rw [map_mul, mul_assoc, mul_assoc, infGL_comm]
    have e2 := hW (g * c r) x
    rw [e, map_mul] at e2
    exact e2
  have h3 : fderiv ℝ (W (x : GL (Fin a) (Af E) ⧸ U)) (sand g (hOne E a)) (sand g v) = sand g (P y + Z) :=
    (hWd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by rw [h0, map_one]; rfl)).unique h2
  refine ⟨v + t • (P y + Z), ?_, ?_⟩
  · have h4 : ‖P y‖ ≤ K * ‖v‖ * B :=
      (P.le_opNorm y).trans (mul_le_mul hPn hb (norm_nonneg _) (by positivity))
    have h5 : ‖Z‖ ≤ B * ‖v‖ := hZ.trans (mul_le_mul_of_nonneg_left hn hB)
    have h6 : ‖t • (P y + Z)‖ ≤ ‖P y‖ + ‖Z‖ := by
      rw [norm_smul]
      exact (mul_le_of_le_one_left (norm_nonneg _) ht).trans (norm_add_le _ _)
    have h7 := norm_add_le v (t • (P y + Z))
    nlinarith
  · rw [flow_der hWd, h3, map_add (sand g) v, map_smul]

end UpperTheory.V.Lit.Geo
end
end

section

open UpperTheory.V.Lit.Geo
open scoped ContDiff

private theorem pbNat_flow {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Y : Set V} (hY : IsOpen Y)
    (ρ : V →L[ℝ] V) {W W' : V → V} (hW : IsField Y W) (hW' : IsField Y W') (hρ : ∀ p ∈ Y, ρ p ∈ Y)
    (he : ∀ p ∈ Y, W' (ρ p) = ρ (W p)) (t : ℝ) {p : V} (hp : p ∈ Y) :
    flow W' t (ρ p) = ρ (flow W t p) ∧ ∀ v, fderiv ℝ (flow W' t) (ρ p) (ρ v) = ρ (fderiv ℝ (flow W t) p v) := by
  have hd : ∀ (U : V → V) (x : V), DifferentiableAt ℝ U x → ∀ v : V,
      fderiv ℝ (flow U t) x v = v + t • fderiv ℝ U x v := by
    intro U x hU v
    have h := (hasFDerivAt_id x).add (hU.hasFDerivAt.const_smul t)
    have hfl : flow U t = id + t • U := by
      funext y
      simp [flow]
    rw [hfl, h.fderiv]
    simp
  constructor
  · simp only [flow]
    rw [he p hp]
    simp [map_add (f := _), map_smul]
  · intro v
    have hWd : DifferentiableAt ℝ W p :=
      (hW.1.contDiffAt (hY.mem_nhds hp)).differentiableAt (by simp)
    have hW'd : DifferentiableAt ℝ W' (ρ p) :=
      (hW'.1.contDiffAt (hY.mem_nhds (hρ p hp))).differentiableAt (by simp)
    have heq : (fun x => W' (ρ x)) =ᶠ[nhds p] (fun x => ρ (W x)) := by
      filter_upwards [hY.mem_nhds hp] with x hx using he x hx
    have hder : fderiv ℝ W' (ρ p) (ρ v) = ρ (fderiv ℝ W p v) := by
      have h1 := heq.fderiv_eq (𝕜 := ℝ)
      have c1 : fderiv ℝ (fun x => W' (ρ x)) p = (fderiv ℝ W' (ρ p)).comp ρ :=
        (hW'd.hasFDerivAt.comp p ρ.hasFDerivAt).fderiv
      have c2 : fderiv ℝ (fun x => ρ (W x)) p = ρ.comp (fderiv ℝ W p) :=
        (ρ.hasFDerivAt.comp p hWd.hasFDerivAt).fderiv
      have h3 := congrArg (fun L => L v) (c1.symm.trans (h1.trans c2))
      simpa using h3
    rw [hd W' (ρ p) hW'd, hd W p hWd, hder]
    simp [map_add (f := _), map_smul]

theorem UpperTheory.V.Lit.Geo.pbNat :
    PbNat := by
  unfold PbNat
  intro V F _ _ _ _ _ _ Y hY ρ A W W' hW hW' hρ he q
  constructor
  · intro w w' hww t ht p hp v
    obtain ⟨h1, h2⟩ := pbNat_flow hY ρ hW hW' hρ he t hp
    rw [pb_apply, pb_apply, h1]
    simp only [h2]
    exact hww _ (hW.2 p hp t ht) _
  · intro w w' hww
    have hb1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ Y, ∀ v : Fin q → V,
        (hk W' t w' (ρ p)) (fun i => ρ (v i)) = A ((hk W t w p) v) := by
      intro t ht p hp v
      obtain ⟨h1, h2⟩ := pbNat_flow hY ρ hW hW' hρ he t hp
      rw [hk_apply, hk_apply, h1, he p hp]
      simp only [h2]
      convert hww (flow W t p) (hW.2 p hp t ht)
        (Matrix.vecCons (W p) fun i => fderiv ℝ (flow W t) p (v i)) using 2
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    refine ⟨hb1, fun hwc hw'c p hp v => ?_⟩
    have hk1 := (hkSmooth V F Y hY W hW q w hwc).2.2.1 p hp
    have hk2 := (hkSmooth V F Y hY W' hW' q w' hw'c).2.2.1 (ρ p) (hρ p hp)
    have i1 : IntervalIntegrable (fun t => hk W t w p) MeasureTheory.volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le zero_le_one]
      exact hk1
    have i2 : IntervalIntegrable (fun t => hk W' t w' (ρ p)) MeasureTheory.volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le zero_le_one]
      exact hk2
    have i3 : IntervalIntegrable (fun t => (hk W t w p) v) MeasureTheory.volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le zero_le_one]
      exact (ContinuousAlternatingMap.apply ℝ V F v).continuous.comp_continuousOn hk1
    have e1 : (∫ t in (0 : ℝ)..1, hk W' t w' (ρ p)) (fun i => ρ (v i)) =
        ∫ t in (0 : ℝ)..1, (hk W' t w' (ρ p)) (fun i => ρ (v i)) :=
      ((ContinuousAlternatingMap.apply ℝ V F (fun i => ρ (v i))).intervalIntegral_comp_comm i2).symm
    have e2 : (∫ t in (0 : ℝ)..1, hk W t w p) v = ∫ t in (0 : ℝ)..1, (hk W t w p) v :=
      ((ContinuousAlternatingMap.apply ℝ V F v).intervalIntegral_comp_comm i1).symm
    unfold hom
    rw [e1, e2, ← A.intervalIntegral_comp_comm i3]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact hb1 t ht p hp v
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr

namespace UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem rat_split (γ : GL (Fin a) E) (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) :
    infGL E a (GeneralLinearGroup.map (pInf E) (ratGL E a γ) * g) *
        finGL E a (GeneralLinearGroup.map (algebraMap E (Af E)) γ * x) =
      ratGL E a γ * (infGL E a g * finGL E a x) := by
  refine ga_ext ?_ ?_
  · simp only [map_mul, pInf_infGL, pInf_finGL, mul_one]
  · simp only [map_mul, pFin_infGL, pFin_finGL, one_mul]
    rfl

private theorem centre_zero : splitCentre E a 0 = 1 := by
  have h : (expU fun _ : InfinitePlace E => ((0 : ℝ) : ℂ)) = 1 := by
    ext w
    simp [expU]
  rw [splitCentre, h, map_one, map_one]

private theorem scal_ex (r : ℝ) (hr : 0 < r) : ∃ (t : ℝ) (c : GL (Fin a) (Cinf E)),
    infGL E a c = splitCentre E a t ∧ ∀ p : HV E a, sand c p = r • p := by
  refine ⟨Real.log r / 2, _, rfl, fun p => Subtype.ext ?_⟩
  have h : (Units.map (Matrix.scalar (Fin a)).toMonoidHom
      (expU fun _ : InfinitePlace E => ((Real.log r / 2 : ℝ) : ℂ)) : GL (Fin a) (Cinf E)).val =
      Real.exp (Real.log r / 2) • (1 : Matrix (Fin a) (Fin a) (Cinf E)) := by
    ext i j w
    by_cases hij : i = j <;> simp [expU, hij, Matrix.one_apply]
  have e : Real.exp (Real.log r / 2) * Real.exp (Real.log r / 2) = r := by
    rw [← Real.exp_add, add_halves, Real.exp_log hr]
  change Matrix.of (sand _ p).1 = r • Matrix.of p.1
  rw [sand_val, h, star_smul, star_one, star_trivial, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, e]

private theorem flow_eq {U : Subgroup (GL (Fin a) (Af E))} {Y : GA E a → Herm E a}
    {W : (GL (Fin a) (Af E) ⧸ U) → HV E a → HV E a} (hW : FCorr U Y W) (g h : GL (Fin a) (Cinf E))
    (x : GL (Fin a) (Af E)) (t : ℝ) (hh : h.val * star h.val = 1 + t • (Y (infGL E a g * finGL E a x)).1) :
    flow (W (x : GL (Fin a) (Af E) ⧸ U)) t (sand g (hOne E a)) = sand (g * h) (hOne E a) := by
  rw [flow, hW, ← map_smul, ← map_add (f := _), map_mul, ContinuousLinearMap.mul_apply]
  congr 1
  refine Subtype.ext ?_
  change (1 : Matrix (Fin a) (Fin a) (Cinf E)) + t • (Y (infGL E a g * finGL E a x)).1 = h.val * 1 * star h.val
  rw [mul_one, hh]

end UpperTheory.V.Lit.Geo

open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.fieldFlow :
    FieldFlow := by
  intro E _ _ _ a ho U Ξ Y C hY W hW
  refine ⟨⟨fun s => ⟨fieldSm E a U Y C hY W hW s, ?_⟩, ?_, ?_⟩, flow_eq hW⟩
  · rintro p ⟨g, rfl⟩ t ht
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    obtain ⟨h, hh, -⟩ := hY.root (infGL E a g * finGL E a x) t (abs_le.2 ⟨by linarith [ht.1], ht.2⟩)
    rw [flow_eq hW g h x t hh]
    exact ⟨_, rfl⟩
  · rintro γ s p ⟨g, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    have hs : ∀ p : HV E a, (geo ho U Ξ).ρ γ (sand g p) =
        sand (GeneralLinearGroup.map (pInf E) (ratGL E a γ.1) * g) p := fun p => by
      rw [geo_ρ, map_mul]; rfl
    have hσ : (geo ho U Ξ).σ γ (x : GL (Fin a) (Af E) ⧸ U) =
        ((GeneralLinearGroup.map (algebraMap E (Af E)) γ.1 * x : GL (Fin a) (Af E)) : GL (Fin a) (Af E) ⧸ U) := rfl
    have hl := hY.left γ.1 0 (infGL E a g * finGL E a x)
    rw [centre_zero, mul_one] at hl
    rw [hσ, hs, hW, hW, hs, rat_split, hl]
  · rintro s r hr p ⟨g, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    obtain ⟨t, c, hc, hp⟩ := scal_ex (E := E) (a := a) r hr
    have hl := hY.left 1 t (infGL E a g * finGL E a x)
    rw [map_one, one_mul, ← hc, ← mul_assoc, ← map_mul] at hl
    have hs : ∀ p : HV E a, r • sand g p = sand (c * g) p := fun p => by
      rw [map_mul, ContinuousLinearMap.mul_apply, hp]
    rw [hs, hW, hW, hs, hl]
end
end

section

open UpperTheory.V.Lit.Geo
open scoped ContDiff

theorem UpperTheory.V.Lit.Geo.omApply :
    OmApply := by
  intro Γ V S _ _ _ _ d G W hW q
  refine ⟨fun w s p hp => ?_, fun w s p hp => ?_⟩
  · refine toOm_apply G (z := fun s => pb (flow (W s) 1) (w.1 s)) (fun s x hx => ?_) s hp
    have hx' : flow (W s) 1 x ∈ G.Y := (hW.field s).2 x hx 1 ⟨zero_le_one, le_rfl⟩
    have h1 : ContDiffAt ℝ ∞ (W s) x := (hW.field s).1.contDiffAt (G.isOpen.mem_nhds hx)
    have h2 : ContDiffAt ℝ ∞ (flow (W s) 1) x := contDiffAt_id.add (h1.const_smul (1 : ℝ))
    have h3 : ContDiffAt ℝ ∞ (w.1 s) (flow (W s) 1 x) := (w.2 s).1.contDiffAt (G.isOpen.mem_nhds hx')
    exact (pbD V V (Fin d → ℂ) q _ _ x h2 h3).1.contDiffWithinAt
  · exact toOm_apply G (z := fun s => hom (W s) (w.1 s))
      (fun s => (hkSmooth V (Fin d → ℂ) G.Y G.isOpen (W s) (hW.field s) q (w.1 s) (w.2 s).1).2.2.2) s hp
end

section

open UpperTheory.V.Lit.Geo

private theorem absBd {V W F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W] [NormedAddCommGroup F] [NormedSpace ℝ F] (e : W ≃ₗ[ℝ] V) (q : ℕ) :
    ∃ (T : Finset (Fin q → W)) (B : ℝ), 0 ≤ B ∧ ∀ (m : (Fin q → W) →ₘₗ[ℝ] F) (M : ℝ), 0 ≤ M →
      (∀ X ∈ T, ‖m X‖ ≤ M) → ∀ X, ‖m X‖ ≤ B * M * ∏ i, ‖e (X i)‖ := by
  classical
  let b := Module.finBasis ℝ V
  let c : Fin (Module.finrank ℝ V) → (V →L[ℝ] ℝ) := fun j => LinearMap.toContinuousLinearMap (b.coord j)
  refine ⟨Finset.univ.image fun I : Fin q → Fin (Module.finrank ℝ V) => fun i => e.symm (b (I i)),
    ∑ I : Fin q → Fin (Module.finrank ℝ V), ∏ i, ‖c (I i)‖, by positivity, fun m M hM hT X => ?_⟩
  have hX : X = fun i => ∑ j, c j (e (X i)) • e.symm (b j) := by
    funext i
    apply e.injective

    simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply]
    exact (b.sum_repr _).symm
  have h1 : m X = ∑ I : Fin q → Fin (Module.finrank ℝ V),
      (∏ i, c (I i) (e (X i))) • m fun i => e.symm (b (I i)) := by
    conv_lhs => rw [hX]

    rw [m.map_sum]
    exact Finset.sum_congr rfl fun I _ => m.map_smul_univ _ _
  rw [h1, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun I _ => ?_)
  rw [norm_smul, norm_prod, mul_right_comm, ← Finset.prod_mul_distrib]
  refine mul_le_mul (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => (c (I i)).le_opNorm _)
    (hT _ (Finset.mem_image_of_mem _ (Finset.mem_univ I))) (norm_nonneg _) (by positivity)

theorem UpperTheory.V.Lit.Geo.bdBasis :
    BdBasis := by
  intro E _ _ _ a Ξ q
  obtain ⟨T, B, hB, h⟩ := absBd (F := Fin Ξ.d → ℂ) (UpperTheory.V.Lit.Dr.hv (E := E) (a := a)) q
  refine ⟨T, B, hB, fun α g M hM hT X => ?_⟩
  exact h ((((LinearMap.proj _).comp UpperTheory.V.Lit.Dr.ev).restrictScalars ℝ).compMultilinearMap α.toMultilinearMap) M hM hT X
end

section

open UpperTheory.V.Lit.Geo

private theorem aux {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] {q : ℕ} (A : F) (u : ℂ) (l : Fin (q + 1) → ℂ)
    (B : Fin (q + 1) → F) (n : Fin (q + 1) → ℝ) (s b M M' : ℝ) (hn : ∀ i, 0 ≤ n i) (hM : 0 ≤ M) (hb : 0 ≤ b)
    (hs : ‖1 - u‖ ≤ s) (hl : ∀ i, ‖l i‖ ≤ b * n i)
    (hB : b = 0 ∨ ∀ i, ‖B i‖ ≤ M * ∏ j, n (i.succAbove j)) (hA : ‖A‖ ≤ M' * ∏ i, n i) :
    ‖A - (u • A + ∑ i : Fin (q + 1), ((-1 : ℂ) ^ (i : ℕ) * l i) • B i)‖ ≤ (s * M' + (q + 1) * b * M) * ∏ i, n i := by
  have hP : 0 ≤ ∏ i, n i := Finset.prod_nonneg fun i _ => hn i
  have e : A - (u • A + ∑ i : Fin (q + 1), ((-1 : ℂ) ^ (i : ℕ) * l i) • B i) =
      (1 - u) • A - ∑ i : Fin (q + 1), ((-1 : ℂ) ^ (i : ℕ) * l i) • B i := by
    rw [sub_smul, one_smul, sub_sub]
  have h1 : ‖(1 - u) • A‖ ≤ s * (M' * ∏ i, n i) := by
    rw [norm_smul]
    exact mul_le_mul hs hA (norm_nonneg _) ((norm_nonneg _).trans hs)
  have h2 : ∀ i : Fin (q + 1), ‖((-1 : ℂ) ^ (i : ℕ) * l i) • B i‖ ≤ b * M * ∏ i, n i := fun i => by
    rw [norm_smul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rcases hB with h | h
    · have h0 : ‖l i‖ = 0 := le_antisymm (by simpa [h] using hl i) (norm_nonneg _)
      simp [h, h0]
    · refine (mul_le_mul (hl i) (h i) (norm_nonneg _) (mul_nonneg hb (hn i))).trans_eq ?_
      rw [Fin.prod_univ_succAbove n i]
      ring
  have h3 : ‖∑ i : Fin (q + 1), ((-1 : ℂ) ^ (i : ℕ) * l i) • B i‖ ≤ (q + 1) * (b * M * ∏ i, n i) := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => h2 i).trans_eq ?_)
    simp
  rw [e]
  refine (norm_sub_le _ _).trans ((add_le_add h1 h3).trans_eq ?_)
  ring

theorem UpperTheory.V.Lit.Geo.cutBd :
    CutBd := by
  intro E _ _ _ a Ξ q u η ζ h g s b M M' hM _ hb hs hl hη hd X
  rw [AlternatingMap.sub_apply, map_sub, Pi.sub_apply, h]
  exact aux _ _ _ _ (fun i => ‖UpperTheory.V.Lit.Dr.hv (X i)‖) s b M M' (fun _ => norm_nonneg _) hM hb hs
    (fun i => hl _) (hη.imp id fun hη i => hη _) (hd X)
end

section

open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff

theorem UpperTheory.V.Lit.Geo.Cs.hkSz :
    HkSz := by
  intro V F _ _ _ _ _ _ q k c
  obtain ⟨hA, C₁, hC₁⟩ := altSz V F q k (1 + c)
  obtain ⟨C₂, h₂, hC₂⟩ := compSz V (V →L[ℝ] V) ((V [⋀^Fin q]→L[ℝ] F) →L[ℝ] (V [⋀^Fin q]→L[ℝ] F)) k (1 + c)
  obtain ⟨C₃, h₃, hC₃⟩ := compSz V V (V [⋀^Fin (q + 1)]→L[ℝ] F) k (1 + c)
  let L : (V [⋀^Fin (q + 1)]→L[ℝ] F) →L[ℝ] (V →L[ℝ] V [⋀^Fin q]→L[ℝ] F) :=
    (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := V) (F := F) (n := q)).toContinuousLinearMap
  refine ⟨2 ^ k * (C₂ * |C₁|) * (2 ^ k * (‖L‖ * C₃) * |c|), by positivity, ?_⟩
  intro W t w p b ht hW hWs hw hws
  obtain ⟨f1, f2, f3, f4⟩ := flowSz V k c W t p ht hW hWs
  have a1 : Sz k (fun y => w (UpperTheory.V.Lit.Geo.flow W t y)) p (C₃ * b) :=
    hC₃ w _ p b f1 hw (fun i h1 h2 => f4 i h1 (h2.trans (Nat.le_succ k))) hws
  have s1 : ContDiffAt ℝ ∞ (fun y => w (UpperTheory.V.Lit.Geo.flow W t y)) p := hw.comp p f1
  have a2 := (appSz V _ _ k p).2.1 L _ _ s1 a1
  have s2 : ContDiffAt ℝ ∞ (fun y => L (w (UpperTheory.V.Lit.Geo.flow W t y))) p := L.contDiff.contDiffAt.comp p s1
  have a3 := (appSz V _ _ k p).1 _ W _ _ s2 hW a2 ((hWs.of_le (Nat.le_succ k)).mono (le_abs_self c))
  have s3 : ContDiffAt ℝ ∞ (fun y => L (w (UpperTheory.V.Lit.Geo.flow W t y)) (W y)) p := s2.clm_apply hW
  have a4 := hC₂ _ _ p _ f2 hA.contDiffAt (fun i _ h2 => f3 i h2) ((hC₁ _ f3.norm_le).mono (le_abs_self C₁))
  have s4 := hA.contDiffAt.comp p f2
  have a5 := (appSz V _ _ k p).1 _ _ _ _ s4 s3 a4 a3
  have e : 2 ^ k * (C₂ * |C₁|) * (2 ^ k * (‖L‖ * C₃) * |c|) * b =
      2 ^ k * (C₂ * |C₁|) * (2 ^ k * (‖L‖ * (C₃ * b)) * |c|) := by ring
  rw [e]
  exact a5
end
