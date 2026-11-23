module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle003
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemPuncturedRingIffPowerSeriesPart
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle028
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfForallExistsLsumETwoPi
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle026
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLetterRingOverDVRPolynomialDenominators
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle117
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsChartLoc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle050
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle025
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle074
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcQ

section Ring

variable {K : Type} [Field K] (σ : K →+* ℂ) [Algebra K ℂ⸨X⸩]
  (hK : ∀ x : K, algebraMap K ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x)))
  {v : ℂ} (hv : v ≠ 0)


include hK in
theorem hasSum_algebraMap_const (v : ℂ) (x : K) :
    HasSum (fun n : ℤ => (algebraMap K ℂ⸨X⸩ x).coeff n * v ^ n) (σ x) := by
  rw [hK, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply]
  simpa using GlobalTheory.Conv.hasSum_single_laurent 0 (σ x) v

def ptRing : Subalgebra K ℂ⸨X⸩ where
  carrier := {s | Summable fun n : ℤ => s.coeff n * v ^ n}
  mul_mem' hf hg := (GlobalTheory.Conv.hasSum_mul_laurent hv hf hg).summable
  add_mem' hf hg := by simpa [add_mul] using Summable.add hf hg
  algebraMap_mem' x := (hasSum_algebraMap_const σ hK v x).summable

def ptEv : ptRing σ hK hv →ₐ[K] CAt σ where
  toFun s := (GlobalTheory.Conv.lsum s v : ℂ)
  map_one' := by
    have := (hasSum_algebraMap_const σ hK v 1).tsum_eq
    rw [map_one, map_one] at this
    exact this
  map_mul' f g := (GlobalTheory.Conv.hasSum_mul_laurent hv f.2 g.2).tsum_eq
  map_zero' := by
    have := (hasSum_algebraMap_const σ hK v 0).tsum_eq
    rw [map_zero, map_zero] at this
    exact this
  map_add' f g := by
    have := Summable.tsum_add f.2 g.2
    show GlobalTheory.Conv.lsum (f + g : ℂ⸨X⸩) v = GlobalTheory.Conv.lsum f v + GlobalTheory.Conv.lsum g v
    simpa [GlobalTheory.Conv.lsum, add_mul] using this
  commutes' x := (hasSum_algebraMap_const σ hK v x).tsum_eq

theorem hasSum_ptEv (s : ptRing σ hK hv) :
    HasSum (fun n : ℤ => (s : ℂ⸨X⸩).coeff n * v ^ n) (_root_.Formalism.L2.PjFree.toC (ptEv σ hK hv s)) :=
  Summable.hasSum s.2

theorem ptEv_eq (s : ptRing σ hK hv) {x : CAt σ}
    (h : HasSum (fun n : ℤ => (s : ℂ⸨X⸩).coeff n * v ^ n) (_root_.Formalism.L2.PjFree.toC x)) : ptEv σ hK hv s = x :=
  h.tsum_eq

theorem isUnit_ptRing (s : ptRing σ hK hv) (h0 : (s : ℂ⸨X⸩) ≠ 0)
    (h : Summable fun n : ℤ => ((s : ℂ⸨X⸩)⁻¹).coeff n * v ^ n) : IsUnit s :=
  IsUnit.of_mul_eq_one ⟨_, h⟩ (Subtype.ext (mul_inv_cancel₀ h0))

end Ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem frMap_of_frChg_map {R A T : Type} [CommRing R] [Algebra c.F R] [CommRing A] [Algebra c.F A]
    [CommRing T] [Algebra c.F T] (φ : R →ₐ[c.F] A) (κ : A →ₐ[c.F] T)
    (G : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A) (s : A)
    {y₀ : FrPt Xo c R} {u₁ u : FrPt Xo c A} {y₁ y : FrPt Xo c T} (h₁ : FrMap φ y₀ u₁) (hu : FrChg G s u₁ u)
    (h₂ : FrMap (κ.comp φ) y₀ y₁) (hy : FrChg (fun τ => (G τ).map κ) (κ s) y₁ y) : FrMap κ u y :=
  ((GlobalTheory.Frames.frChg_calculus E H Dw l Xo c A).2.2.1 T κ G s u₁ u y₁ y hu
    (Formalism.L2.Pj.frMap_cancel R A T φ κ y₀ u₁ y₁ h₁ h₂)).2 hy

theorem hasSum_evR_of_chart (hL : GlobalTheory.Reg.EvLaws Xo c) (σ : c.F →+* ℂ) [Algebra c.F ℂ⸨X⸩]
    (hK : ∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x)))
    {v : ℂ} (hv : v ≠ 0) {R : Type} [CommRing R] [Algebra c.F R] (φ : R →ₐ[c.F] ℂ⸨X⸩) (ψ : R →ₐ[c.F] CAt σ)
    (G : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ⸨X⸩) (s : ℂ⸨X⸩)
    (Gw : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) (sw : CAt σ)
    {y₀ : FrPt Xo c R} {y₁ y : FrPt Xo c ℂ⸨X⸩} {yw₁ yw : FrPt Xo c (CAt σ)}
    (h₁ : FrMap φ y₀ y₁) (hy : FrChg G s y₁ y) (hw₁ : FrMap ψ y₀ yw₁) (hyw : FrChg Gw sw yw₁ yw)
    (hφ : ∀ f, HasSum (fun n : ℤ => (φ f).coeff n * v ^ n) (_root_.Formalism.L2.PjFree.toC (ψ f)))
    (hG : ∀ τ i k, HasSum (fun n : ℤ => (G τ i k).coeff n * v ^ n) (_root_.Formalism.L2.PjFree.toC (Gw τ i k)))
    (hs : HasSum (fun n : ℤ => s.coeff n * v ^ n) (_root_.Formalism.L2.PjFree.toC sw))
    (hG' : ∀ τ, Summable fun n : ℤ => ((G τ).det⁻¹).coeff n * v ^ n)
    (hs' : Summable fun n : ℤ => (s⁻¹).coeff n * v ^ n)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c) (hF : F ∈ sec Xo c a n) :
    HasSum (fun m : ℤ => (evR Xo c F y).coeff m * v ^ m) (_root_.Formalism.L2.PjFree.toC (evR Xo c F yw)) := by
  let A := ptRing σ hK hv
  let φA : R →ₐ[c.F] A := φ.codRestrict A fun f => (hφ f).summable
  let GA : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A :=
    fun τ i k => ⟨G τ i k, (hG τ i k).summable⟩
  let sA : A := ⟨s, hs.summable⟩
  obtain ⟨hu1, hu2⟩ := (frChg_exists_unique_units E H Dw l Xo c _ G s y₁).2.2.1 y hy
  have hdet : ∀ τ, ((GA τ).det : ℂ⸨X⸩) = (G τ).det := fun τ => A.val.map_det (GA τ)
  obtain ⟨u₁, hu₁⟩ := hL.bc _ _ φA y₀
  obtain ⟨u, hu⟩ := (frChg_exists_unique_units E H Dw l Xo c A GA sA u₁).1
    (fun τ => isUnit_ptRing σ hK hv _ (by rw [hdet]; exact (hu1 τ).ne_zero) (by rw [hdet]; exact hG' τ))
    (isUnit_ptRing σ hK hv sA hu2.ne_zero hs')
  have e₁ : FrMap A.val u y := frMap_of_frChg_map φA A.val GA sA hu₁ hu h₁ hy
  have eψ : (ptEv σ hK hv).comp φA = ψ := AlgHom.ext fun f => ptEv_eq σ hK hv _ (hφ f)
  have eG : (fun τ => (GA τ).map (ptEv σ hK hv)) = Gw := by
    funext τ
    ext i k
    exact ptEv_eq σ hK hv _ (hG τ i k)
  have es : ptEv σ hK hv sA = sw := ptEv_eq σ hK hv _ hs
  have e₂ : FrMap (ptEv σ hK hv) u yw :=
    frMap_of_frChg_map φA (ptEv σ hK hv) GA sA hu₁ hu (by rw [eψ]; exact hw₁) (by rw [eG, es]; exact hyw)
  have nat := (evR_natural_weight_scaling E H Dw l Xo c hL a n F hF A).1
  rw [nat _ _ u y e₁, nat _ _ u yw e₂]
  exact hasSum_ptEv σ hK hv _

theorem exists_algHom_of_mem_range {R L : Type} [CommRing R] [Algebra c.F R] [Field L] [Algebra c.F L]
    (j : Sp R ⟶ Xo.XF c) [IsOpenImmersion j] (hj : j ≫ pullback.snd _ _ = spMap (algebraMap c.F R))
    (z : Sp L ⟶ Xo.XF c) (hz : z ≫ pullback.snd _ _ = spMap (algebraMap c.F L))
    (h : z (IsLocalRing.closedPoint L) ∈ Set.range j) :
    ∃ φ : R →ₐ[c.F] L, spMap φ.toRingHom ≫ j = z := by
  have hr : Set.range z ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    have : x = IsLocalRing.closedPoint L := Subsingleton.elim (α := PrimeSpectrum L) _ _
    exact this ▸ h
  let f : R →+* L := (Spec.preimage (IsOpenImmersion.lift j z hr)).hom
  have hf : spMap f ≫ j = z := by
    show Spec.map (Spec.preimage (IsOpenImmersion.lift j z hr)) ≫ j = z
    rw [Spec.map_preimage, IsOpenImmersion.lift_fac]
  have hc : f.comp (algebraMap c.F R) = algebraMap c.F L := by
    have : spMap (f.comp (algebraMap c.F R)) = spMap (algebraMap c.F L) := by
      rw [← hz, ← hf, Category.assoc, hj]
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  exact ⟨{ f with commutes' := fun x => DFunLike.congr_fun hc x }, hf⟩

theorem hasSum_evR_arc : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) [Algebra c.F ℂ⸨X⸩] (y : FrPt Xo c ℂ⸨X⸩) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin g → ℂ)), GlobalTheory.Reg.EvLaws Xo c → (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → PushInvertible Y.t.G Y.t.PP.L → ThNZ th → IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → (∀ τ k, AnVec Ha (e τ k) (z τ k)) → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ∀ a' n (F : Rul Xo c), F ∈ sec Xo c a' n → HasSum (fun m : ℤ => (evR Xo c F y).coeff m * eTwoPi w ^ m) (_root_.Formalism.L2.PjFree.toC (evR Xo c F yw)) := by
  intro hL1 hL2 E _ _ _ H Dw l Xo c σ _ _ O _ β Y a χ W g ty Fu Ha _ y e th Θ z hL hK hχ hβ hP hth hy hz
  obtain ⟨pt, -, -, -, -, hpt1, hpt2, -⟩ := id hy
  have hpt3 : pt ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ⸨X⸩) := by
    rw [← cancel_mono (spMap β), Category.assoc, ← Y.jQ_over, Category.assoc, ← pullback.condition,
      ← Category.assoc Y.jQ, ← Category.assoc]
    show (pt ≫ Y.j) ≫ Y.s = _
    rw [hpt1, Category.assoc, hχ]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun x => (hK (β x)).symm
  obtain ⟨p, j, y₀, hch, hmem⟩ := GlobalTheory.T.exists_openChart_framedPoint_testRing hL1.secBaseChange E H Dw l Xo c (pt (IsLocalRing.closedPoint ℂ⸨X⸩))
  haveI := hch.1
  obtain ⟨φ, hφ⟩ := exists_algHom_of_mem_range j hch.2.2 pt hpt3 hmem
  obtain ⟨y₁, hy₁⟩ := hL.bc _ _ φ y₀
  obtain ⟨G, s, hGs⟩ := (frChg_exists_unique_units E H Dw l Xo c _ (fun _ => 1) 1 y₁).2.2.2 y
    (by rw [hy₁.1, ← hch.2.1, ← Category.assoc, hφ, hpt2])
  obtain ⟨T₁, h₁⟩ := GlobalTheory.T.holArc_chart_coordinates_hasSum E H Dw l Xo c σ O β Y a χ W g ty Fu Ha p j φ hK hχ hβ hch.1 hch.2.2
    (by rw [← Category.assoc, hφ, hpt1])
  obtain ⟨T₂, h₂⟩ := GlobalTheory.T.frame_matrix_hasSum_alt hL1 hL2 E H Dw l Xo c σ O β Y a χ W g ty Fu Ha y e th z p j y₀ φ y₁ G s
    hK hχ hβ hy hz hch hy₁ hGs
  obtain ⟨T₃, h₃⟩ := GlobalTheory.T.hasSum_thetaGenerator_chart_ratio hL1 hL2 E H Dw l Xo c σ O β Y a χ W g ty Fu Ha y e th Θ p j y₀ φ y₁ G s
    hK hχ hβ hP hth hy hch hy₁ hGs
  have key : ∀ w : ℂ, max T₁ (max T₂ T₃) < w.im → ∀ yw, AnFr Ha Θ z w yw →
      ∃ (ψ : p.R →ₐ[c.F] CAt σ) (yw₁ : FrPt Xo c (CAt σ))
        (Gw : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) (sw : CAt σ),
        FrMap ψ y₀ yw₁ ∧ FrChg Gw sw yw₁ yw ∧
        (∀ f, HasSum (fun n : ℤ => (φ f).coeff n * eTwoPi w ^ n) (_root_.Formalism.L2.PjFree.toC (ψ f))) ∧
        (∀ τ i k, HasSum (fun n : ℤ => (G τ i k).coeff n * eTwoPi w ^ n) (_root_.Formalism.L2.PjFree.toC (Gw τ i k))) ∧
        HasSum (fun n : ℤ => s.coeff n * eTwoPi w ^ n) (_root_.Formalism.L2.PjFree.toC sw) := by
    intro w hw yw hyw
    rw [max_lt_iff, max_lt_iff] at hw
    obtain ⟨ψ, hψ1, hψ2⟩ := h₁ w hw.1
    obtain ⟨yw₁, hyw₁⟩ := hL.bc _ _ ψ y₀
    obtain ⟨Gw, sw, hw'⟩ := (frChg_exists_unique_units E H Dw l Xo c _ (fun _ => 1) 1 yw₁).2.2.2 yw
      (by rw [hyw₁.1, ← hch.2.1, hψ1]; exact hyw.1.1)
    exact ⟨ψ, yw₁, Gw, sw, hyw₁, hw', hψ2, h₂ w hw.2.1 ψ yw₁ yw Gw sw hψ2 hyw₁ hyw.1 hw',
      h₃ w hw.2.2 ψ yw₁ yw Gw sw hψ2 hyw₁ hyw.1.1 hyw.2 hw'⟩
  by_cases hex : ∃ w : ℂ, max T₁ (max T₂ T₃) < w.im ∧ ∃ yw, AnFr Ha Θ z w yw
  · obtain ⟨w₀, hw₀, yw₀, hyw₀⟩ := hex
    obtain ⟨-, -, Gw₀, sw₀, -, -, -, hG₀, hs₀⟩ := key w₀ hw₀ yw₀ hyw₀
    have hv₀ := GlobalTheory.Conv.eTwoPi_ne_zero w₀
    have cs : s⁻¹ ∈ GlobalTheory.Conv.convLaurent :=
      inv_mem (GlobalTheory.Conv.mem_convLaurent_of_summable hv₀ hs₀.summable)
    have cG : ∀ τ, (G τ).det⁻¹ ∈ GlobalTheory.Conv.convLaurent := fun τ => by
      refine inv_mem ?_
      rw [Matrix.det_apply']
      exact sum_mem fun π _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ =>
        GlobalTheory.Conv.mem_convLaurent_of_summable hv₀ (hG₀ τ _ _).summable)
    obtain ⟨T₄, h₄⟩ := GlobalTheory.Conv.exists_forall_mem_halfRing
      (S := insert s⁻¹ (Set.range fun τ => (G τ).det⁻¹)) ((Set.finite_range _).insert _)
      (by rintro _ (rfl | ⟨τ, rfl⟩); exacts [cs, cG τ])
    refine ⟨max T₄ (max T₁ (max T₂ T₃)), fun w hw yw hyw a' n F hF => ?_⟩
    rw [max_lt_iff] at hw
    obtain ⟨ψ, yw₁, Gw, sw, k₁, k₂, k₃, k₄, k₅⟩ := key w hw.2 yw hyw
    exact hasSum_evR_of_chart hL σ hK (GlobalTheory.Conv.eTwoPi_ne_zero w) φ ψ G s Gw sw hy₁ hGs k₁ k₂ k₃ k₄ k₅
      (fun τ => h₄ _ (Or.inr ⟨τ, rfl⟩) w hw.1) (h₄ _ (Or.inl rfl) w hw.1) a' n F hF
  · exact ⟨_, fun w hw yw hyw => absurd ⟨w, hw, yw, hyw⟩ hex⟩

end GlobalTheory.ArcQ
end
end

section

noncomputable section

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

section Units

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem arcιR_isUnit_mul (Dw : Datum H) (V : Type) [CommRing V] (ϖ : V) :
    IsUnit (arcιR Dw V ϖ (PowerSeries.C ϖ * PowerSeries.X)) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := ArcSR Dw V ϖ)
    (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw V)
  rw [map_mul (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ))] at h
  exact isUnit_of_mul_isUnit_left h

theorem letMR_det_isUnit (Dw : Datum H) (V : Type) [CommRing V] (ϖ : V) (τ : E →+* ℂ) :
    IsUnit (letMR Dw V ϖ τ).det := by
  classical
  have h := IsLocalization.Away.algebraMap_isUnit (S := ArcSR Dw V ϖ)
    (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw V)
  rw [map_mul (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ))] at h
  have h2 := isUnit_of_mul_isUnit_right h
  have h3 := isUnit_of_dvd_unit (map_dvd (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ))
    (Finset.dvd_prod_of_mem (fun τ : E →+* ℂ => Matrix.det (Matrix.of fun i k : Fin (Dw.mult τ) =>
      (MvPolynomial.X (⟨τ, i, k⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) (PowerSeries V)))) (Finset.mem_univ τ))) h2
  rw [RingHom.map_det] at h3
  exact h3

theorem arcιR_C_isUnit (Dw : Datum H) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) {v : V} (hv : v ≠ 0) : IsUnit (arcιR Dw V ϖ (PowerSeries.C v)) := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hv hϖ
  have h := arcιR_isUnit_mul Dw V ϖ
  rw [map_mul (arcιR Dw V ϖ)] at h
  rw [map_mul (PowerSeries.C (R := V)), map_pow (PowerSeries.C (R := V)), map_mul (arcιR Dw V ϖ),
    map_pow (arcιR Dw V ϖ)]
  exact ((u.isUnit.map _).map _).mul ((isUnit_of_mul_isUnit_left h).pow n)

end Units

theorem exists_lift_open {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    {S : Type} [CommRing S] (g : c.F →+* S) (χ : Sp S ⟶ Y.X) (hcond : χ ≫ Y.s = spMap g ≫ spMap β)
    (hj : ∀ q : Sp S, χ q ∈ Set.range Y.j) :
    ∃ z : Sp S ⟶ Xo.XF c, z ≫ Y.j = χ ∧ z ≫ pullback.snd _ _ = spMap g := by
  let p : Sp S ⟶ pullback Y.s (spMap β) := pullback.lift χ (spMap g) hcond
  have hr : Set.range p ⊆ Set.range Y.jQ := by
    rintro _ ⟨q, rfl⟩
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst]
    obtain ⟨w, hw⟩ := hj q
    rw [← hw]
    have h2 : Y.jQ w ∈ (pullback.fst Y.s (spMap β)) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]; exact ⟨w, rfl⟩
    simpa only [Model.j, Scheme.Hom.comp_apply, Set.mem_preimage] using h2
  have := Y.jQ_open
  refine ⟨IsOpenImmersion.lift Y.jQ p hr, ?_, ?_⟩
  · show IsOpenImmersion.lift Y.jQ p hr ≫ Y.jQ ≫ pullback.fst _ _ = _
    rw [← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]
  · rw [← Y.jQ_over, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_snd]

theorem exists_dvr_frPt : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Tv : CDVR) (ϖ : Tv.V) (f : c.F →+* Tv.Fr) (b : O →+* Tv.V) (a : ArcIn Dw l β Tv.V b) (χ : Sp (PowerSeries Tv.V) ⟶ Y.X) (W : Wit Y a χ) (ρ : (E →+* ℂ) → (𝓞 E →+* Tv.V)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR Tv.V)) (th : a.D₀.P.L.Sec), Irreducible ϖ → f.comp β = (algebraMap Tv.V Tv.Fr).comp b → (∀ τ x, algebraMap Tv.V Tv.Fr (ρ τ x) = f (embK c τ x)) → χ ≫ Y.s = spMap (PowerSeries.C (R := Tv.V)) ≫ spMap b → (∀ x : Sp (PowerSeries Tv.V), PowerSeries.C ϖ * PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → Mono (spMap β) → PushInvertible Y.t.G Y.t.PP.L → ArcBasis W ρ e → ThNZ th → ∃ (_ : Algebra c.F (ArcSR Dw Tv.V ϖ)), (∀ (x : c.F) (v : Tv.V) (n : ℕ), f x * algebraMap Tv.V Tv.Fr ϖ ^ n = algebraMap Tv.V Tv.Fr v → algebraMap c.F (ArcSR Dw Tv.V ϖ) x * arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) ϖ) ^ n = arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) v)) ∧ ∃ y₀ yR : FrPt Xo c (ArcSR Dw Tv.V ϖ), IsArcFr W e th (arcιR Dw Tv.V ϖ) y₀ ∧ FrChg (letMR Dw Tv.V ϖ) 1 y₀ yR := by
  intro L1 L2 E _ _ _ H Dw l Xo c O _ β Y Tv ϖ f b a χ W ρ e th hϖ hfb hρ hχ hj _ hpush hbasis hth
  let ι := arcιR Dw Tv.V ϖ
  let κ : Tv.V →+* ArcSR Dw Tv.V ϖ := ι.comp (PowerSeries.C (R := Tv.V))
  have hκ : ∀ y : nonZeroDivisors Tv.V, IsUnit (κ y) := fun y =>
    arcιR_C_isUnit Dw Tv.V hϖ (nonZeroDivisors.ne_zero y.2)
  let g : Tv.Fr →+* ArcSR Dw Tv.V ϖ := IsLocalization.lift hκ
  have hg : ∀ v, g (algebraMap Tv.V Tv.Fr v) = κ v := fun v => IsLocalization.lift_eq hκ v
  letI alg : Algebra c.F (ArcSR Dw Tv.V ϖ) := (g.comp f).toAlgebra
  have halg : ∀ x, algebraMap c.F (ArcSR Dw Tv.V ϖ) x = g (f x) := fun _ => rfl
  refine ⟨alg, ?_, ?_⟩
  · intro x v n h
    have h2 := congrArg g h
    rw [map_mul, map_pow, hg, hg] at h2
    exact h2
  · have hcomp : (algebraMap c.F (ArcSR Dw Tv.V ϖ)).comp β = ι.comp ((PowerSeries.C (R := Tv.V)).comp b) := by
      ext1 x
      have h1 : f (β x) = algebraMap Tv.V Tv.Fr (b x) := RingHom.congr_fun hfb x
      show g (f (β x)) = κ (b x)
      rw [h1, hg]
    have hcond : (spMap ι ≫ χ) ≫ Y.s = spMap (algebraMap c.F (ArcSR Dw Tv.V ϖ)) ≫ spMap β := by
      rw [Category.assoc, hχ, ← spMap_comp, ← spMap_comp, ← spMap_comp, hcomp]
    obtain ⟨z, hz1, hz2⟩ := exists_lift_open Y (algebraMap c.F (ArcSR Dw Tv.V ϖ)) (spMap ι ≫ χ) hcond (by
      intro q
      rw [Scheme.Hom.comp_apply]
      refine hj _ fun h => ?_
      have h' : ι (PowerSeries.C ϖ * PowerSeries.X) ∈ q.asIdeal := h
      exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' (arcιR_isUnit_mul Dw Tv.V ϖ)))
    have hflat := (GlobalTheory.LetterDenom.main E H Dw Tv ϖ hϖ.ne_zero).2.2.1
    obtain ⟨y₀, -, hy₀⟩ := exists_isArcFr L1 L2 E H Dw l Xo c O β Y Tv.V b a χ W ρ e th hbasis hth (Or.inr hpush)
      (ArcSR Dw Tv.V ϖ) ι z hflat hz1
      (by rw [pullback.condition, ← Category.assoc, hz2, ← spMap_comp]; rfl)
      (fun τ x => by rw [halg, ← hρ, hg]; rfl)
    obtain ⟨yR, hyR⟩ := (frChg_exists_unique_units E H Dw l Xo c (ArcSR Dw Tv.V ϖ) (letMR Dw Tv.V ϖ) 1 y₀).1
      (letMR_det_isUnit Dw Tv.V ϖ) isUnit_one
    exact ⟨y₀, yR, hy₀, hyR⟩

end GlobalTheory.ArcQ
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem _root_.GlobalTheory.T.arcFrame_change_by_constants : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (e e' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) (th th' : a.D₀.P.L.Sec) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A) (r : A), ThNZ th → (∀ τ k, GtComb (g τ k) (e τ) (e' τ k)) → ThMul r th th' → ∀ (S : Type) [CommRing S] [Algebra c.F S] (ι : PowerSeries A →+* S) (y y' : FrPt Xo c S), Mono Y.j → IsArcFr W e th ι y → FrChg (fun τ => (g τ).map (ι.comp (PowerSeries.C (R := A)))) (ι (PowerSeries.C (R := A) r)) y y' → IsArcFr W e' th' ι y' := by
  exact GlobalTheory.ArcQ.isArcFr_of_frChg_const
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem arc_rigidity_two_models_of_mono : Laws → Laws2 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ') (y y' : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c), y ≫ Y.j = jK (PowerSeries k) ≫ χ → y' ≫ Y'.j = jK (PowerSeries k) ≫ χ' → y ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF → y' ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF → y = y' ∧ (Mono Y.j → ∃ ψ : W.t.G ≅ W'.t.G, W.Agree W' ψ) :=
  rigidArc_of_mono

end GlobalTheory
end

section

noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem chain_levelPt_of_section (h1 : Out.Laws) (h2 : Out.Laws2) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (C : Chain W Λ)
    (k : ℕ) [NeZero k] (p₀ : Out.QkPt a.D₀ (FractionRing ℂ) k) (ξ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G)
    (ξ₀ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (la : Λ.A.La)
    (hξ : ξ.left ≫ Y.m0.toSABMap.φ = pullback.fst _ _ ≫ ξ₀.left)
    (hk : (k = l.A ∧ ∃ v, HEq p₀ (a.etaA v) ∧ ξ = Y.oF.etaA v) ∨
      (k = l.M ∧ ∃ v ∈ idealPart D l, HEq p₀ (a.eta v) ∧ ξ = Y.oF.eta v))
    (hrep : Λ.Rep k p₀ la) : C.Φ.LevelPt k (toUnit _ ≫ ξ₀) la := by
  have hξw : ξ.left ≫ Y.oF.t.G.hom = 𝟙 _ := Over.w ξ
  have hY : (C.yF ≫ ξ.left ≫ Y.m.φ) ≫ Y.t.G.hom = gen ≫ χ := by
    have := Y.m.cart.1.w
    rw [Category.assoc, Category.assoc, this, ← Category.assoc ξ.left, hξw, Category.id_comp]
    exact C.yF_j
  let p : Over.mk gen ⟶ W.t.G :=
    Over.homMk (W.m.cart.1.lift (C.yF ≫ ξ.left ≫ Y.m.φ) gen hY) (W.m.cart.1.lift_snd _ _ _)
  have hp : p.left ≫ W.m.φ = C.yF ≫ ξ.left ≫ Y.m.φ := W.m.cart.1.lift_fst _ _ _
  let pY : Over.mk (gen ≫ χ) ⟶ Y.t.G := Over.homMk (C.yF ≫ ξ.left ≫ Y.m.φ) hY
  let pF : Over.mk C.yF ⟶ Y.oF.t.G := toUnit _ ≫ ξ
  have hpF : pF.left = C.yF ≫ ξ.left := rfl
  have hW := GlobalTheory.T.levelPoints_of_arc_eq_period_div_level h1 h2 E H D l Xo c O β Y (bF.comp β) a χ W Λ C.Ξ C.ΦW C.yF k p₀ ξ la p C.isGen C.yF_j
    hk hrep hp
  have h₂ := (GlobalTheory.T.arcLevelPoint_tangentVector_transport_iff E H _ _ Λ.A _ _ _ W.m C.w₂ _ _ C.ΦW C.ΦY C.rig₂.1 C.rel₂).1 k p pY la hp
  have h₁ := (GlobalTheory.T.arcLevelPoint_tangentVector_transport_iff E H _ _ Λ.A _ _ _ Y.m C.w₁ _ _ C.ΦF C.ΦY C.rig₁.1 C.rel₁).1 k pF pY la
    (by rw [hpF, Category.assoc]; rfl)
  have h₀ := (GlobalTheory.T.arcLevelPoint_tangentVector_transport_iff E H _ _ Λ.A _ _ _ Y.m0.toSABMap C.w₀ _ _ C.ΦF C.Φ C.rig₀.1 C.rel₀).1 k pF
    (toUnit _ ≫ ξ₀) la (by rw [hpF, Category.assoc, hξ, ← Category.assoc]; rfl)
  exact h₀.1 (h₁.2 (h₂.1 hW))

theorem chain_levels : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (C : Chain W Λ) (laA laM : D.La → Λ.A.La), (∀ v, Λ.Rep l.A (a.etaA v) (laA v)) → (∀ v, Λ.Rep l.M (a.eta v) (laM v)) → (∀ v, C.Φ.LevelPt l.A (toUnit _ ≫ Xo.univ.etaA v) (laA v)) ∧ ∀ v ∈ idealPart D l, C.Φ.LevelPt l.M (toUnit _ ≫ Xo.univ.eta v) (laM v) := by
  intro h1 h2 E _ _ _ H _ D l Xo c O _ β Y _ _ bF a χ W Λ C laA laM hA hM
  haveI : NeZero l.A := ⟨l.A_pos.ne'⟩
  haveI : NeZero l.M := ⟨by have := l.three_le; omega⟩
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · exact chain_levelPt_of_section h1 h2 E H D l Xo c O β Y bF a χ W Λ C l.A (a.etaA v) (Y.oF.etaA v)
      (Xo.univ.etaA v) (laA v) (Y.m0.etaA v) (Or.inl ⟨rfl, v, HEq.rfl, rfl⟩) (hA v)
  · exact chain_levelPt_of_section h1 h2 E H D l Xo c O β Y bF a χ W Λ C l.M (a.eta v) (Y.oF.eta v)
      (Xo.univ.eta v) (laM v) (Y.m0.eta v) (Or.inr ⟨rfl, v, hv, HEq.rfl, rfl⟩) (hM v)

end GlobalTheory.ArcPts
end
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.GenericPoints

theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : _root_.GlobalTheory.ArcPts.GtAn a) (Ξ : ConstPts W Λ) , ∃ Φ : GenPts Λ.A W.t gen, Ξ.IsGen Φ := by
  intro h₁ h₂ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ
  have g := GlobalTheory.ArcPts.constPts_add_smul h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ
  have f := GlobalTheory.T.constantPointFrame_isFrame_with_rigidification h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ
  exact exists_genPts Λ.A W.t W.P.U.LG W.P.bundle Ξ.x Ξ.τ g.1 g.2 f.1 f.2
    (fun j _ α th hth => GlobalTheory.T.exists_section_values_formalThetaSum h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ j α th hth)
    (fun j _ σ => GlobalTheory.ConstSpan.main h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ j σ)
    (fun k hk s => exists_clear W.P.U k hk s)

end GlobalTheory.GenericPoints
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.isTangent_constant_coords_generic_fibre : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : _root_.GlobalTheory.ArcPts.GtAn a) (Ξ : ConstPts W Λ) (Φ : GenPts Λ.A W.t gen) (g : ℕ) (h : Λ.A.V ≃L[ℂ] (Fin g → ℂ)) (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (v : epsR (PowerSeries ℂ) ⟶ W.t.G) (ρ : DualNumber ℂ⟦X⟧ →+* DualNumber ℂ⸨X⸩) (νK : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback W.t.G.hom gen), Ξ.IsGen Φ → DiffHyp W (fun z => Λ.ex0 (h.symm z)) z₀ ν v → (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (algebraMap ℂ⟦X⟧ ℂ⸨X⸩ r)) → ρ DualNumber.eps = DualNumber.eps → νK ≫ pullback.fst _ _ = spMap ρ ≫ v.left → νK ≫ pullback.snd _ _ = spMap (algebraMap ℂ⸨X⸩ (DualNumber ℂ⸨X⸩)) → Φ.IsTan (h.symm z₀) νK := by
  first | exact @GlobalTheory.ConstTan.isTan_of_diffHyp | exact GlobalTheory.ConstTan.isTan_of_diffHyp | (intros; apply GlobalTheory.ConstTan.isTan_of_diffHyp <;> assumption)
end
