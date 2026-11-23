module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle872
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle901
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle896
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle588
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle885
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import GroundTheory.AutomorphicForms.Bundle012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle875
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle895
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle086
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle078
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle084
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

variable {D : D7}

theorem cflip_flipElt_add {a b : AE D} (m : ℕ) (h1 : a * b = 0) (h2 : a * cA D b = 0) (h3 : cA D a * b = 0)
    (h4 : cA D a * cA D b = 0) : flipElt (a + b) m = flipElt a m * flipElt b m := by
  unfold flipElt
  rw [map_add (f := _)]
  linear_combination (-((m : AE D) - 1) ^ 2) * h1 - ((m : AE D) - 1) * (incA D ((m : D.host.E)⁻¹) - 1) * h2
    - ((m : AE D) - 1) * (incA D ((m : D.host.E)⁻¹) - 1) * h3 - (incA D ((m : D.host.E)⁻¹) - 1) ^ 2 * h4

theorem cflip_sum_idem {S : Finset (Formalism.L2.DIV.Pl D.host.E)} {es : Formalism.L2.DIV.Pl D.host.E → AE D}
    (hes : ∀ PP ∈ S, Formalism.L2.NTheta.IsIdemAt (es PP) PP) : (∑ PP ∈ S, es PP) * (∑ PP ∈ S, es PP) = ∑ PP ∈ S, es PP := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun PP hPP => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single_of_mem PP hPP]
  · exact (hes PP hPP).1.1
  · intro Q hQ hne
    exact GlobalTheory.Tow.idemAt_orth (hes PP hPP) (hes Q hQ) (Ne.symm hne)

theorem cflip_mul_cA_eq_zero {e u v : AE D} (he : e * cA D e = 0) (hu : e * u = u) (hv : e * v = v) : u * cA D v = 0 := by
  rw [← hu, ← hv, map_mul]
  linear_combination (u * cA D v) * he

theorem cflip_isHalf_mono {m n : ℕ} {e u : AE D} (hu : e * u = u) {y : Mx D m n} (hy : Formalism.IndefR.Datum.IsHalf (cA D u) y) :
    Formalism.IndefR.Datum.IsHalf (cA D e) y := by
  intro i j
  rw [← hy i j, ← mul_assoc, ← map_mul, hu]

theorem cflip_det_split {R : Type*} [CommRing R] {a b t x : R} (hab : a * b = 0)
    (hx : x * ((a + b) * t + (1 - (a + b))) = 1) : x * ((a * t + (1 - a)) * (b * t + (1 - b))) = 1 := by
  linear_combination hx + (x * (t - 1) ^ 2) * hab

theorem cflip_smul_one_mul {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] (c d : R)
    (X : Matrix n n R) : ((c * d) • (1 : Matrix n n R)) * X = c • ((d • (1 : Matrix n n R)) * X) := by
  rw [mul_smul, Matrix.smul_mul]

theorem cflip_unit_split {R : Type*} [CommRing R] {x u v : R} (h : x * (u * v) = 1) : x = x * v * (x * u) := by
  linear_combination (-x) * h


theorem centralFlip_phase : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D) (m : ℕ) (z : GA D V) (x : (AE D)ˣ) (ℓ : (WO V W → ℂ) →ₗ[ℂ] ℂ), IsIdemSum eT T → m ≠ 0 → Formalism.L2.Theta.mt V z = flipElt eT m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → IsFlipDet V eT m x → (∀ y : WO V W, IsHalf (cA D eT) y → ∀ φ : WO V W → ℂ, IsThetaFunO ψ V W φ → ℓ (heisO ψ V W y φ) = ℓ φ) → ∃ r : ℝ, 0 < r ∧ ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → ℓ (om (z⁻¹, 1) f) = (r : ℂ) * ((χW x : Circle) : ℂ)⁻¹ * ℓ f := by
  intro D ψ V W χV χW om hW T
  induction T using Finset.induction_on with
  | empty =>
    intro eT m z x ℓ hS hm hz hx hℓ
    obtain ⟨⟨es, -, he⟩, -⟩ := hS
    rw [Finset.sum_empty] at he
    subst he
    have h1 : flipElt (0 : AE D) m = 1 := by unfold flipElt; simp
    have hz1 : z = 1 := GlobalTheory.IdemSupport.mt_inj V (by rw [hz, h1, one_smul, GlobalTheory.IdemSupport.mt_one])
    have hx1 : x = 1 := by simpa [IsFlipDet] using hx
    subst hz1 hx1
    refine ⟨1, one_pos, fun f hf => ?_⟩
    simp only [inv_one, Circle.coe_one, map_one, inv_one, Complex.ofReal_one, one_mul]
    show ℓ ((om 1) f) = ℓ f
    rw [map_one]
    rfl
  | @insert P T' hP ih =>
    intro eT m z x ℓ hS hm hz hx hℓ
    obtain ⟨⟨es, hes, heT⟩, hT⟩ := hS
    have hesP := hes P (Finset.mem_insert_self P T')
    have hes' : ∀ Q ∈ T', Formalism.L2.NTheta.IsIdemAt (es Q) Q := fun Q hQ => hes Q (Finset.mem_insert_of_mem hQ)
    have heT' : eT = es P + ∑ Q ∈ T', es Q := by rw [heT, Finset.sum_insert hP]
    have hab : es P * ∑ Q ∈ T', es Q = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun Q hQ => GlobalTheory.Tow.idemAt_orth hesP (hes' Q hQ) (fun h => hP (h ▸ hQ))
    have hbb := cflip_sum_idem hes'
    have heA : eT * es P = es P := by
      rw [heT', add_mul, hesP.1.1, mul_comm, hab, add_zero]
    have heB : eT * ∑ Q ∈ T', es Q = ∑ Q ∈ T', es Q := by
      rw [heT', add_mul, hab, hbb, zero_add]
    have hSa : IsIdemSum (es P) {P} :=
      ⟨⟨es, by simpa using hesP, by simp⟩, cflip_mul_cA_eq_zero hT heA heA⟩
    have hSb : IsIdemSum (∑ Q ∈ T', es Q) T' := ⟨⟨es, hes', rfl⟩, cflip_mul_cA_eq_zero hT heB heB⟩
    have hflip : flipElt eT m = flipElt (es P) m * flipElt (∑ Q ∈ T', es Q) m := by
      rw [heT']
      refine cflip_flipElt_add m hab (cflip_mul_cA_eq_zero hT heA heB) ?_ (by rw [← map_mul, hab, map_zero])
      rw [mul_comm]
      exact cflip_mul_cA_eq_zero hT heB heA
    obtain ⟨zP, -, -, hzP⟩ := GlobalTheory.T.exists_central_conjugateFlipScalar_finiteAdelic D V {P} m (es P) hSa hm

    have h1 : Formalism.L2.Theta.mt V zP * Formalism.L2.Theta.mt V zP⁻¹ = 1 := by
      rw [← GlobalTheory.IdemSupport.mt_mul, mul_inv_cancel, GlobalTheory.IdemSupport.mt_one]
    have hz' : Formalism.L2.Theta.mt V (z * zP⁻¹) =
        flipElt (∑ Q ∈ T', es Q) m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
      rw [hzP] at h1
      calc Formalism.L2.Theta.mt V (z * zP⁻¹)
          = (flipElt (∑ Q ∈ T', es Q) m * flipElt (es P) m) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) *
              Formalism.L2.Theta.mt V zP⁻¹ := by
            rw [GlobalTheory.IdemSupport.mt_mul, hz, hflip, mul_comm (flipElt (es P) m)]
        _ = flipElt (∑ Q ∈ T', es Q) m • (flipElt (es P) m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) *
              Formalism.L2.Theta.mt V zP⁻¹) := cflip_smul_one_mul _ _ _
        _ = _ := by rw [h1]

    have hx0 : (x : AE D) * ((es P * (m : AE D) ^ V.rank + (1 - es P)) * ((∑ Q ∈ T', es Q) * (m : AE D) ^ V.rank + (1 - ∑ Q ∈ T', es Q))) = 1 := by
      rw [heT'] at hx
      exact cflip_det_split hab hx
    have hxa : (x : AE D) * ((∑ Q ∈ T', es Q) * (m : AE D) ^ V.rank + (1 - ∑ Q ∈ T', es Q)) * (es P * (m : AE D) ^ V.rank + (1 - es P)) = 1 := by
      rw [mul_assoc, mul_comm ((∑ Q ∈ T', es Q) * (m : AE D) ^ V.rank + _)]; exact hx0
    have hxb : (x : AE D) * (es P * (m : AE D) ^ V.rank + (1 - es P)) * ((∑ Q ∈ T', es Q) * (m : AE D) ^ V.rank + (1 - ∑ Q ∈ T', es Q)) = 1 := by
      rw [mul_assoc]; exact hx0
    let xa : (AE D)ˣ := ⟨_, _, hxa, by rw [mul_comm]; exact hxa⟩
    let xb : (AE D)ˣ := ⟨_, _, hxb, by rw [mul_comm]; exact hxb⟩
    have hxx : x = xa * xb := by
      apply Units.ext
      simp only [xa, xb, Units.val_mul]
      exact cflip_unit_split hx0
    have hxaD : IsFlipDet V (es P) m xa := hxa
    have hxbD : IsFlipDet V (∑ Q ∈ T', es Q) m xb := hxb
    obtain ⟨rP, hrP, hPstep⟩ := GlobalTheory.T.weilOperator_inv_centralFlip_invariantForm_eq D ψ V W χV χW om hW P (es P) m zP xa ℓ hesP hm hzP hxaD
      (fun y hy φ hφ => hℓ y (cflip_isHalf_mono heA hy) φ hφ)
    obtain ⟨r', hr', hrest⟩ := ih (∑ Q ∈ T', es Q) m (z * zP⁻¹) xb ℓ hSb hm hz' hxbD
      (fun y hy φ hφ => hℓ y (cflip_isHalf_mono heB hy) φ hφ)
    refine ⟨rP * r', mul_pos hrP hr', fun f hf => ?_⟩
    have hsplit : ((z⁻¹ : GA D V), (1 : GA D W)) = (zP⁻¹, 1) * ((z * zP⁻¹)⁻¹, 1) := by
      ext <;> simp
    rw [hsplit, map_mul, Module.End.mul_apply, hPstep _ (hW.om_pres _ _ hf), hrest f hf, hxx, map_mul]
    push_cast
    ring

end GlobalTheory.LevelSeries

end
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
noncomputable section

namespace GlobalTheory.RSnmUnfProps

open GroundTheory.Automorphic.FourierWhittaker (blockGL blockMat blockMat_apply coe_blockGL)

theorem superDiag_blockGL {R : Type} [CommRing R] {j n : ℕ} (hj : j ≤ n) (g : GL (Fin j) R) :
    GlobalTheory.Whittaker.superDiag (blockGL hj g) = GlobalTheory.Whittaker.superDiag g := by
  unfold GlobalTheory.Whittaker.superDiag
  simp only [Finset.sum_filter]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hj) (Fin.castLE_injective hj) _ _ ?_ ?_
  · intro i hi
    have hij : ¬ (i : ℕ) < j := fun h => hi ⟨⟨i, h⟩, rfl⟩
    refine Finset.sum_eq_zero fun b _ => ?_
    split_ifs with hb
    · rw [coe_blockGL, blockMat_apply, dite_eq_right hij, if_neg]
      intro h; rw [h] at hb; omega
    · rfl
  · intro i
    refine Fintype.sum_of_injective (Fin.castLE hj) (Fin.castLE_injective hj) _ _ ?_ ?_
    · intro b hb
      have hbj : ¬ (b : ℕ) < j := fun h => hb ⟨⟨b, h⟩, rfl⟩
      split_ifs
      · rw [coe_blockGL, blockMat_apply, dite_eq_left (by simp), dite_eq_right hbj]
      · rfl
    · intro b
      simp only [Fin.coe_castLE]
      split_ifs
      · rw [coe_blockGL, blockMat_apply, dite_eq_left (by simp), dite_eq_left (by simp)]
        rfl
      · rfl

variable {E : Type} [Field E] [NumberField E]

theorem psiN_blockGL {j n : ℕ} (hj : j ≤ n) (g : GA E j) :
    GlobalTheory.JSW.psiN (blockGL hj g : GA E n) = GlobalTheory.JSW.psiN g := by
  unfold GlobalTheory.JSW.psiN
  rw [superDiag_blockGL]

theorem norm_psiN {a : ℕ} (u : GA E a) : ‖GlobalTheory.JSW.psiN u‖ = 1 := by
  simp [GlobalTheory.JSW.psiN, Circle.norm_coe]

theorem blockGL_mem_NA {j n : ℕ} (hj : j ≤ n) {u : GA E j} (hu : u ∈ GlobalTheory.JSW.NA (E := E) (a := j)) :
    (blockGL hj u : GA E n) ∈ GlobalTheory.JSW.NA (E := E) (a := n) := by
  obtain ⟨h1, h2⟩ := hu
  refine ⟨fun i k hik => ?_, fun i => ?_⟩
  · rw [coe_blockGL, blockMat_apply]
    split_ifs with ha hb hc
    · exact h1 _ _ (by rw [Fin.lt_def] at hik ⊢; exact hik)
    · rfl
    · exact absurd hik (by rw [hc]; exact lt_irrefl _)
    · rfl
  · rw [coe_blockGL, blockMat_apply]
    split_ifs with ha hb
    · exact h2 _
    · rfl
    · exact absurd rfl hb

theorem detAbs_unip {a : ℕ} {u : GA E a} (hu : u ∈ GlobalTheory.CellDec.NA E a) : GlobalTheory.RSnm.detAbs u = 1 := by
  have hd : Matrix.GeneralLinearGroup.det u = 1 := Units.ext (GlobalTheory.RSLocalPart.det_eq_one hu)
  rw [GlobalTheory.RSnm.detAbs, hd, map_one]; rfl

end GlobalTheory.RSnmUnfProps


open GroundTheory.Automorphic.FourierWhittaker (blockGL) in
theorem GlobalTheory.RSnmUnfProps.uIntNM_props : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ) (F : (Fin (m + 1) → Ad E) → ℂ),
    Continuous (GlobalTheory.JSW.whit φ) → Continuous (GlobalTheory.JSW.whit φ') →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g) →
    Continuous (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F) →
    Continuous (fun g : GA E (m + 1) => GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) g)) ∧
    Continuous (fun g : GA E (m + 1) => GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)) ∧
    (∀ x : ℝ, Measurable (GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x)) ∧
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g : GA E (m + 1),
      ‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (u * g))‖ = ‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) g)‖ ∧
      ‖GlobalTheory.JSW.whit φ' (u * g)‖ = ‖GlobalTheory.JSW.whit φ' g‖ ∧
      GlobalTheory.ZEul.lastRow (u * g) = GlobalTheory.ZEul.lastRow g ∧ GlobalTheory.RSnm.detAbs (u * g) = GlobalTheory.RSnm.detAbs g ∧
      ∀ x : ℝ, GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x (u * g) = GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x g) ∧
    ∀ (x : ℝ) (g : GA E (m + 1)), ‖GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x g‖ ≤
      (‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) g)‖ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)‖ * GlobalTheory.RSnm.detAbs g ^ (x - ((r : ℝ) + 1)) +
        ‖GlobalTheory.JSW.whit φ' g‖ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)‖ * GlobalTheory.RSnm.detAbs g ^ x) / 2 := by
  intro E _ _ _ m r S φ φ' F hW hW' hl hl' hF
  have hmn : m + 1 ≤ m + r + 1 + 1 := by omega
  have cW : Continuous (fun g : GA E (m + 1) => GlobalTheory.JSW.whit φ (blockGL hmn g)) :=
    hW.comp (GlobalTheory.RSnm.continuous_blockGL hmn)
  have cF : Continuous (fun g : GA E (m + 1) => GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)) :=
    hF.comp GlobalTheory.ZUnfTheta.continuous_lastRow
  have cD : ∀ y : ℂ, Continuous (fun g : GA E (m + 1) => ((GlobalTheory.RSnm.detAbs g : ℝ) : ℂ) ^ y) := fun y =>
    (Complex.continuous_ofReal.comp GlobalTheory.RSnm.continuous_detAbs).cpow continuous_const
      fun h => Complex.ofReal_mem_slitPlane.2 (GlobalTheory.RSnm.detAbs_pos h)
  have hwu : ∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g : GA E (m + 1),
      GlobalTheory.JSW.whit φ (blockGL hmn (u * g)) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ (blockGL hmn g) := by
    intro u hu g
    have hu' : u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)) := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
    rw [map_mul, hl _ (GlobalTheory.RSnmUnfProps.blockGL_mem_NA hmn hu'), GlobalTheory.RSnmUnfProps.psiN_blockGL]
  refine ⟨cW, cF, fun x => ?_, fun u hu g => ?_, fun x g => ?_⟩
  · unfold GlobalTheory.RSnmUnf.uIntNM
    exact (((cW.mul (Complex.continuous_conj.comp hW')).mul cF).mul (cD _)).measurable
  · have hu' : u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)) := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
    have hlr := GlobalTheory.ZEulProps.lastRow_unip hu g
    have hd : GlobalTheory.RSnm.detAbs (u * g) = GlobalTheory.RSnm.detAbs g := by
      rw [GlobalTheory.RSnm.detAbs_mul, GlobalTheory.RSnmUnfProps.detAbs_unip hu, one_mul]
    refine ⟨?_, ?_, hlr, hd, fun x => ?_⟩
    · rw [hwu u hu g, norm_mul, GlobalTheory.RSnmUnfProps.norm_psiN, one_mul]
    · rw [hl' u hu' g, norm_mul, GlobalTheory.RSnmUnfProps.norm_psiN, one_mul]
    · unfold GlobalTheory.RSnmUnf.uIntNM
      rw [hwu u hu g, hl' u hu' g, hlr, hd, map_mul]
      have h1 := GlobalTheory.ZEulProps.psiN_mul_conj u
      linear_combination (GlobalTheory.JSW.whit φ (blockGL hmn g) * conj (GlobalTheory.JSW.whit φ' g) *
        GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g) *
        ((GlobalTheory.RSnm.detAbs g : ℝ) : ℂ) ^ ((x : ℂ) - (((m + r + 1 + 1 : ℕ) : ℂ) - ((m + 1 : ℕ) : ℂ)) / 2)) * h1

  · have hdp := GlobalTheory.RSnm.detAbs_pos g
    have hre : ((x : ℂ) - (((m + r + 1 + 1 : ℕ) : ℂ) - ((m + 1 : ℕ) : ℂ)) / 2).re = (x - ((r : ℝ) + 1)) / 2 + x / 2 := by
      push_cast
      simp only [Complex.sub_re, Complex.div_re, Complex.add_re, Complex.ofReal_re, Complex.natCast_re,
        Complex.one_re, Complex.natCast_im, Complex.one_im, Complex.add_im, Complex.ofReal_im]
      norm_num
      ring
    unfold GlobalTheory.RSnmUnf.uIntNM
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_cpow_eq_rpow_re_of_pos hdp, hre,
      Real.rpow_add hdp]
    have hA : GlobalTheory.RSnm.detAbs g ^ (x - ((r : ℝ) + 1)) = (GlobalTheory.RSnm.detAbs g ^ ((x - ((r : ℝ) + 1)) / 2)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hdp.le]; norm_num
    have hB : GlobalTheory.RSnm.detAbs g ^ x = (GlobalTheory.RSnm.detAbs g ^ (x / 2)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hdp.le]; norm_num
    rw [hA, hB]
    set a := ‖GlobalTheory.JSW.whit φ (blockGL hmn g)‖
    set b := ‖GlobalTheory.JSW.whit φ' g‖
    set c := ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)‖
    set α := GlobalTheory.RSnm.detAbs g ^ ((x - ((r : ℝ) + 1)) / 2)
    set β := GlobalTheory.RSnm.detAbs g ^ (x / 2)
    have hc : 0 ≤ c := norm_nonneg _
    nlinarith [mul_nonneg hc (sq_nonneg (a * α - b * β))]
end
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum


open scoped ComplexOrder Topology
noncomputable section
namespace GlobalTheory.SmoothVac
variable {D : D7}

theorem comm_compAt_one (W : HSp D) (θ : InfFam D) (τ : D.what₂.Tau) (s : Matrix (Fin W.rank) (Fin W.rank) ℂ) :
    s * compAt θ τ (Formalism.L2.Theta.mt W 1) = compAt θ τ (Formalism.L2.Theta.mt W 1) * s := by
  have h1 : Formalism.L2.Theta.mt W 1 = 1 := by simp [Formalism.L2.Theta.mt]
  rw [h1, compAt, Matrix.map_one _ (by simp) (by simp), Matrix.one_mul, Matrix.mul_one]

theorem isCartanInv_one (V : HSp D) (hV : V.gram = 1) (τ : D.what₂.Tau) : IsCartanInv (gramAt D V τ) 1 := by
  have : gramAt D V τ = 1 := by rw [gramAt, hV, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [this]
  exact ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩

theorem exists_ne_zero_of_isVacO {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {f : WO S T → ℂ}
    (hf : IsVacO ψ θ S T sS sT LS LT f) : ∃ w, f w ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
  have := hn p hp
  have h0 : f = 0 := funext h
  rw [h0] at this
  simp [nrm2] at this

theorem finCong_of_mul_left {a b : ℕ} {V : HSp D} {k : GA D V} (h : GlobalTheory.Member.FinCong V (a * b) k) :
    GlobalTheory.Member.FinCong V a k := by
  intro z hz
  obtain ⟨y, hy, e⟩ := h z hz
  exact ⟨b • y, nsmul_mem hy b, by rw [e, mul_smul]⟩

theorem finCong_of_mul_right {a b : ℕ} {V : HSp D} {k : GA D V} (h : GlobalTheory.Member.FinCong V (a * b) k) :
    GlobalTheory.Member.FinCong V b k := by
  intro z hz
  obtain ⟨y, hy, e⟩ := h z hz
  exact ⟨a • y, nsmul_mem hy a, by rw [e, mul_comm, mul_smul]⟩

theorem isOpen_comap_St (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) :
    IsOpen (((Formalism.L2.DIV.St β).comap ((Formalism.UG.bc (Lev.swapAE D)).comp (Bridge.Gf V).subtype) :
      Subgroup (Bridge.Gf V)) : Set (Bridge.Gf V)) := by
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsModuleTopology (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : IsTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) _
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ_mat β ∅ (continuous_subtype_val (p := fun x => x ∈ Bridge.Gf V)) rfl]
    with x hh
  exact hh.1



theorem isOpen_map_levelGroup (V : HSp D) {N : ℕ} (hN : 0 < N) :
    IsOpen (((GlobalTheory.Member.PrincLevel.levelGroup V N).map (finHom V).rangeRestrict : Subgroup (Bridge.Gf V)) :
      Set (Bridge.Gf V)) := by
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsModuleTopology (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : IsTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) _
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨hop, -, -⟩ := GlobalTheory.Member.latHat_open_and_continuous D V
  have hc : Continuous fun x : Bridge.Gf V => ((x : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) :
      Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) :=
    Units.continuous_val.comp continuous_subtype_val
  obtain ⟨S, hS⟩ := h3.restrictScalars (R := ℤ)
  have hLS : (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) ⊆
      (AddSubgroup.closure (S : Set (Fin V.rank → D.host.E)) : AddSubgroup (Fin V.rank → D.host.E)) := by
    intro x hx
    have hx' : x ∈ Submodule.span ℤ (S : Set (Fin V.rank → D.host.E)) := by rw [hS]; exact hx
    rw [← Submodule.span_int_eq_addSubgroupClosure]
    exact hx'
  have hU : (⋂ x ∈ S, {k : Bridge.Gf V | ∃ y ∈ latHat V,
      ((k : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) :
        Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) *ᵥ GlobalTheory.AdLat.fv D.host.F x -
        GlobalTheory.AdLat.fv D.host.F x = N • y}) ∈ 𝓝 (1 : Bridge.Gf V) := by
    refine (Filter.biInter_finset_mem S).2 fun x _ => ?_
    have hcx := GlobalTheory.Member.PrincLevel.continuous_mulVec_sub hc (GlobalTheory.AdLat.fv D.host.F x)
    refine ((hop N hN).preimage hcx).mem_nhds ⟨0, zero_mem _, by simp⟩
  refine Filter.mem_of_superset hU fun x hx => ?_
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hx
  obtain ⟨g, hg⟩ := x.2
  refine ⟨GlobalTheory.LevelNbhd.finPartG V g, ⟨GlobalTheory.LevelNbhd.finPartG_mem_GfC V g, ?_⟩, ?_⟩
  · unfold GlobalTheory.Member.FinCong
    rw [GlobalTheory.LevelNbhd.finHom_finPartG, hg]
    rw [h1] at hx ⊢
    exact GlobalTheory.Member.PrincLevel.cong_of_gen _ _ hLS _ N fun s hs => hx s hs
  · exact Subtype.ext (by rw [MonoidHom.coe_rangeRestrict, GlobalTheory.LevelNbhd.finHom_finPartG, hg])

theorem om_pow_eq {V W : HSp D} (ω : PairRep V W) (k : GA D V) (f : WO V W → ℂ) (c : ℂ) (hc : ω (k, 1) f = c • f) :
    ∀ m : ℕ, ω (k ^ m, 1) f = c ^ m • f := by
  intro m
  induction m with
  | zero => rw [pow_zero, pow_zero, Prod.mk_one_one, map_one, Module.End.one_apply, one_smul]
  | succ m ih =>
    have e : ((k ^ (m + 1), (1 : GA D W)) : GA D V × GA D W) = (k ^ m, 1) * (k, 1) := by
      rw [pow_succ, Prod.mk_mul_mk, mul_one]
    rw [e, map_mul, Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ, mul_comm]

end GlobalTheory.SmoothVac
end
end
