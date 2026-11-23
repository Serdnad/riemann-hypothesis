module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleWordLengthLe
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleOfUnitWords
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SplLen
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle027
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle049
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle079
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle078
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationScalesHeisenbergMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFactor
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle069
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RankOneEmbeddings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section ube

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def UBL (f : Mat k r → E) (S : Set (Mat k r)) (n e γ : ℕ) : Prop :=
  (∃ C : ℝ, 0 ≤ C ∧ UB f S n C e γ) ∧ LSS f S

lemma ubl_mono {f : Mat k r → E} {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {n e γ e' γ' : ℕ}
    (h : UBL f S n e γ) (he : e ≤ e') (hγ : γ ≤ γ') : UBL f S n e' γ' := by
  obtain ⟨⟨C, hC, hub⟩, hl⟩ := h
  exact ⟨⟨C, hC, ub_mono hSG hub hC he hγ⟩, hl⟩

lemma ubl_const (c : E) {S : Set (Mat k r)} (hSG : S ⊆ GV k r) (n γ : ℕ) : UBL (fun _ : Mat k r => c) S n 0 γ := by
  exact ⟨⟨‖c‖, norm_nonneg _, ub_const c S hSG n γ⟩, lss_of_contDiff contDiff_const S⟩

lemma ubl_clm {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] (L : E →L[ℝ] E') {f : Mat k r → E}
    {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {n e γ : ℕ} (h : UBL f S n e γ) : UBL (fun g => L (f g)) S n e γ := by
  obtain ⟨⟨C, hC, hub⟩, hl⟩ := h
  exact ⟨⟨‖L‖ * C, mul_nonneg (norm_nonneg _) hC, ub_clm L hSG hl hub⟩, lss_clm L hl⟩

lemma ubl_app {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] {S : Set (Mat k r)} (hSG : S ⊆ GV k r)
    {a : Mat k r → (F →L[ℂ] E)} {b : Mat k r → F} {n ea eb γ : ℕ} (ha : UBL a S n ea γ) (hb : UBL b S n eb γ) :
    UBL (fun g => a g (b g)) S n (ea + eb) γ := by
  obtain ⟨⟨Ca, hCa, hua⟩, hla⟩ := ha
  obtain ⟨⟨Cb, hCb, hub⟩, hlb⟩ := hb
  exact ⟨⟨2 ^ n * (Ca * Cb), by positivity, ub_app hSG hla hlb hCa hCb hua hub⟩, lss_app hla hlb⟩

lemma ubl_congr {f f₂ : Mat k r → E} {S V : Set (Mat k r)} (hV : IsOpen V) (hSV : S ⊆ V) (hSG : S ⊆ GV k r)
    (he : ∀ g ∈ GV k r, g ∈ V → f g = f₂ g) {n e γ : ℕ} (h : UBL f₂ S n e γ) : UBL f S n e γ := by
  obtain ⟨⟨C, hC, hub⟩, hl⟩ := h
  exact ⟨⟨C, hC, ub_congr hV hSV hSG he hub⟩, lss_congr hV hSV he hl⟩

lemma ubl_sub {f : Mat k r → E} {S S' : Set (Mat k r)} (hS : S' ⊆ S) {n e γ : ℕ} (h : UBL f S n e γ) :
    UBL f S' n e γ := by
  obtain ⟨⟨C, hC, hub⟩, hl⟩ := h
  exact ⟨⟨C, hC, fun w hw g hg => hub w hw g (hS hg)⟩, lss_mono hl hS⟩

end ube

lemma ubl_mul {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {a b : Mat k r → ℂ} {n ea eb γ : ℕ}
    (ha : UBL a S n ea γ) (hb : UBL b S n eb γ) : UBL (fun g => a g * b g) S n (ea + eb) γ := by
  have ha' : UBL (fun g => ((ContinuousLinearMap.mul ℂ ℂ).restrictScalars ℝ) (a g)) S n ea γ :=
    ubl_clm _ hSG ha
  have h := ubl_app hSG ha' hb
  convert h using 2
  simp

lemma ubl_prod {ι : Type*} [DecidableEq ι] {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {n γ : ℕ} (s : Finset ι)
    (f : ι → Mat k r → ℂ) (h : ∀ i ∈ s, UBL (f i) S n 0 γ) : UBL (fun g => ∏ i ∈ s, f i g) S n 0 γ := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact ubl_const 1 hSG n γ
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    have h1 := ubl_mul hSG (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa using h1

lemma ubl_poly {d : ℕ} {P : Mat k r → ℂ} (hP : U.IsPolyDeg d P) (S : Set (Mat k r)) (hSG : S ⊆ GV k r) (n γ : ℕ) :
    UBL P S n d γ := by
  obtain ⟨hcd, C, hC, hb⟩ := Formalism.FourierDecayAlt.P.poly_adm (n := n) hP
  refine ⟨⟨C, hC, fun w hw g hg => ?_⟩, lss_of_contDiff hcd S⟩
  refine le_trans (hb w hw g (hSG hg)) (mul_le_mul_of_nonneg_left ?_ hC)
  exact pow_le_pow_right₀ (gN_ge_one (hSG hg)) (Nat.le_add_right _ _)

lemma poly_H {d : ℕ} {P : Mat k r → ℂ} (hP : U.IsPolyDeg d P) (n : ℕ) :
    ∃ M : ℝ, ∀ w, admitted n w → w ≠ [] → ∀ g ∈ GV k r, ‖Dw w P g‖ ≤ M * gN g ^ (d * w.length) := by
  obtain ⟨-, C, hC, hb⟩ := Formalism.FourierDecayAlt.P.poly_adm (n := n) hP
  refine ⟨C, fun w hw hne g hg => le_trans (hb w hw g hg) (mul_le_mul_of_nonneg_left ?_ hC)⟩
  have hl : 1 ≤ w.length := List.length_pos_iff.2 hne
  exact pow_le_pow_right₀ (gN_ge_one hg) (Nat.le_mul_of_pos_right d hl)

lemma ubl_fdb {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (ψ : Mat k r → F) (hψ : ContDiff ℝ ∞ ψ) (S : Set (Mat k r)) (hSG : S ⊆ GV k r) (K : Set F)
    (hK : ∀ g ∈ S, ψ g ∈ K) (α n : ℕ) (M : ℝ)
    (H : ∀ w, admitted n w → w ≠ [] → ∀ g ∈ GV k r, ‖Dw w ψ g‖ ≤ M * gN g ^ (α * w.length))
    (Φ : F → E) (hΦ : ContDiff ℝ ∞ Φ) (hB : ∀ j : ℕ, ∃ B : ℝ, ∀ y ∈ K, ‖iteratedFDeriv ℝ j Φ y‖ ≤ B) :
    UBL (fun g => Φ (ψ g)) S n 0 α := by
  obtain ⟨C, hC, hb⟩ := fdb ψ hψ S K hK gN (fun g hg => gN_ge_one (hSG hg)) α 0 M n
    (fun w hw hne g hg => by simpa using H w hw hne g (hSG hg)) n E Φ hΦ hB
  refine ⟨⟨C, hC, fun w hw g hg => ?_⟩, lss_of_contDiff (hΦ.comp hψ) S⟩
  have hlen : w.length ≤ n := by
    obtain ⟨u, v, -, -, hl, rfl⟩ := hw
    simpa [wL, wR] using hl
  simpa using hb w hw hlen g hg

lemma normSq_cd : ContDiff ℝ ∞ (fun z : ℂ => Complex.normSq z) := by
  have h : (fun z : ℂ => Complex.normSq z) = fun z => ‖z‖ ^ 2 :=
    funext fun z => Complex.normSq_eq_norm_sq z
  rw [h]
  exact contDiff_norm_sq ℝ

def zinv (c : ℝ) (m : ℕ) (z : ℂ) : ℂ := (sc c (Complex.normSq z) : ℂ) * z⁻¹ ^ m

lemma zinv_cd {c : ℝ} (hc : 0 < c) (m : ℕ) : ContDiff ℝ ∞ (zinv c m) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · have hev : zinv c m =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
      have hopen : IsOpen {w : ℂ | Complex.normSq w < c / 4} :=
        isOpen_lt normSq_cd.continuous continuous_const
      have hmem : z ∈ {w : ℂ | Complex.normSq w < c / 4} := by
        show Complex.normSq z < c / 4
        rw [hz, map_zero]
        positivity
      filter_upwards [hopen.mem_nhds hmem] with w hw
      unfold zinv
      rw [sc_zero hc (le_of_lt hw)]
      simp
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · unfold zinv
    have h1 : ContDiffAt ℝ ∞ (fun w : ℂ => ((sc c (Complex.normSq w) : ℝ) : ℂ)) z :=
      (Complex.ofRealCLM.contDiff.comp ((sc_cd c).comp normSq_cd)).contDiffAt
    have h2 : ContDiffAt ℝ ∞ (fun w : ℂ => w⁻¹ ^ m) z :=
      ((contDiffAt_inv ℂ hz).pow m).restrict_scalars ℝ
    exact h1.mul h2

lemma zinv_eq {c : ℝ} (hc : 0 < c) (m : ℕ) {z : ℂ} (hz : c / 2 ≤ Complex.normSq z) : zinv c m z = z⁻¹ ^ m := by
  unfold zinv
  rw [sc_one hc hz]
  simp

lemma zinv_bound {c : ℝ} (hc : 0 < c) (m j : ℕ) :
    ∃ B : ℝ, ∀ z ∈ {z : ℂ | c ≤ Complex.normSq z}, ‖iteratedFDeriv ℝ j (zinv c m) z‖ ≤ B := by
  refine ⟨‖∏ i ∈ Finset.range j, ((((-(m : ℤ)) : ℤ) : ℂ) - (i : ℂ))‖ * (Real.sqrt c)⁻¹ ^ (m + j),
    fun z hz => ?_⟩
  have hz' : c ≤ Complex.normSq z := hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [map_zero] at hz'
    linarith
  have hev : zinv c m =ᶠ[𝓝 z] fun w : ℂ => w⁻¹ ^ m := by
    have hopen : IsOpen {w : ℂ | c / 2 < Complex.normSq w} :=
      isOpen_lt continuous_const normSq_cd.continuous
    have hmem : z ∈ {w : ℂ | c / 2 < Complex.normSq w} := by
      show c / 2 < Complex.normSq z
      linarith
    filter_upwards [hopen.mem_nhds hmem] with w hw
    exact zinv_eq hc m (le_of_lt hw)
  have hcd : ContDiffAt ℂ ∞ (zinv c m) z :=
    ((contDiffAt_inv ℂ hz0).pow m).congr_of_eventuallyEq hev
  have hR : ‖iteratedFDeriv ℝ j (zinv c m) z‖ = ‖iteratedFDeriv ℂ j (zinv c m) z‖ := by
    rw [← (contDiffAt_infty.1 hcd j).restrictScalars_iteratedFDeriv, Function.comp_apply,
      ContinuousMultilinearMap.norm_restrictScalars]
  have hfz : (fun w : ℂ => w⁻¹ ^ m) = fun w : ℂ => w ^ (-(m : ℤ)) := by
    funext w
    rw [_root_.zpow_neg, zpow_natCast, inv_pow]
  rw [hR, norm_iteratedFDeriv_eq_norm_iteratedDeriv, hev.iteratedDeriv_eq, hfz, iteratedDeriv_eq_iterate,
    iter_deriv_zpow, norm_mul, norm_zpow]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hzn : Real.sqrt c ≤ ‖z‖ := by
    rw [← Real.sqrt_sq (norm_nonneg z), ← Complex.normSq_eq_norm_sq]
    exact Real.sqrt_le_sqrt hz'
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  rw [show (-(m : ℤ) - (j : ℤ)) = -((m + j : ℕ) : ℤ) by push_cast; ring, _root_.zpow_neg, zpow_natCast, ← inv_pow]
  exact pow_le_pow_left₀ (inv_nonneg.2 (norm_nonneg _)) (inv_anti₀ hsc hzn) _

lemma ubl_invpow {d : ℕ} {P : Mat k r → ℂ} (hP : U.IsPolyDeg d P) {S : Set (Mat k r)} (hSG : S ⊆ GV k r)
    {c : ℝ} (hc : 0 < c) (hS : ∀ g ∈ S, c ≤ Complex.normSq (P g)) (m n : ℕ) :
    UBL (fun g => (P g)⁻¹ ^ m) S n 0 d := by
  obtain ⟨hPc, -⟩ := Formalism.FourierDecayAlt.P.poly_adm (n := n) hP
  obtain ⟨M, hM⟩ := poly_H hP n
  have hV : IsOpen {g : Mat k r | c / 2 < Complex.normSq (P g)} :=
    isOpen_lt continuous_const (normSq_cd.continuous.comp hPc.continuous)
  have hSV : S ⊆ {g : Mat k r | c / 2 < Complex.normSq (P g)} := fun g hg => by
    show c / 2 < Complex.normSq (P g)
    linarith [hS g hg]
  refine ubl_congr hV hSV hSG (f₂ := fun g => zinv c m (P g)) (fun g _ hgV => (zinv_eq hc m (le_of_lt hgV)).symm) ?_
  exact ubl_fdb P hPc S hSG {z : ℂ | c ≤ Complex.normSq z} hS d n M hM (zinv c m) (zinv_cd hc m)
    (fun j => zinv_bound hc m j)

end Formalism.FourierDecayAlt.P.AdmissibleLieWords
end
end

section

open Matrix Finset Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace PCommPf

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq]

theorem isOpen_slice {Dc : (Fin r → ℂ) → Set (Q.Mx k r)}
    (ho : IsOpen {x : (Fin r → ℂ) × Q.Mx k r | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1}) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    IsOpen (Dc c) := by
  have h := ho.preimage (continuous_const.prodMk continuous_id : Continuous (fun g : Q.Mx k r => (c, g)))
  convert h using 1
  ext g
  exact ⟨fun hg => ⟨hc, hg⟩, fun hg => hg.2⟩

theorem tL_crd_comm (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (Dc : (Fin r → ℂ) → Set (Q.Mx k r))
    (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) (ho : IsOpen {x : (Fin r → ℂ) × Q.Mx k r | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1})
    (hΨ : Q.SmoothFam k r i {x | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1} Ψ) (l : Fin r) (Y : ℂ) (a b : Fin 2)
    {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r i) (hgD : g ∈ Dc c) :
    Q.crd (pOp l) (Q.QL k r z z' i Y a b Ψ) c g = Q.QL k r z z' i Y a b (Q.crd (pOp l) Ψ) c g ∧
    Q.crd (pbOp l) (Q.QL k r z z' i Y a b Ψ) c g = Q.QL k r z z' i Y a b (Q.crd (pbOp l) Ψ) c g := by
  have hO : IsOpen (Dc c) := isOpen_slice ho hc
  have hgG : g ∈ Q.Glev k r i ∩ Dc c := ⟨hg, hgD⟩
  have hx : ((c, g) : Qx8.XX k r) ∈ Qx8.UU Dc := ⟨hc, hgD⟩
  have hcd := Qx8.cd_tL (E := Wq →L[ℂ] Wp) (i := i) (U₀ := Qx8.UU Dc) ho z z' Y a b
  have hder : ∀ s s₂ : ℂ,
      s • ((1 / 2 : ℂ) • (Qx8.dv (Pi.single l 1) (fun c' => Q.tL k r z z' i Y a b (Ψ c')) c g +
        s₂ • Qx8.dv (Pi.single l Complex.I) (fun c' => Q.tL k r z z' i Y a b (Ψ c')) c g)) =
      Q.tL k r z z' i Y a b (fun g' => s • ((1 / 2 : ℂ) • (Qx8.dv (Pi.single l 1) Ψ c g' +
        s₂ • Qx8.dv (Pi.single l Complex.I) Ψ c g'))) g := by
    intro s s₂
    rw [hcd.comm _ Ψ hΨ (c, g) hx hg, hcd.comm _ Ψ hΨ (c, g) hx hg, smul_smul]
    have := Qx8.tl_comb (z := z) (z' := z') (i := i) Formalism.FourierDecayAlt.P.transfer_linear_local hO Y a b (s * (1 / 2)) s₂
      (Qx8.sf_slice (Qx8.sf_dv (Pi.single l 1) hΨ) hc)
      (Qx8.sf_slice (Qx8.sf_dv (Pi.single l Complex.I) hΨ) hc) hgG
    rw [← this]
    simp only [smul_smul]
  refine ⟨?_, ?_⟩
  · show pOp l (fun c' => Q.tL k r z z' i Y a b (Ψ c') g) c =
      Q.tL k r z z' i Y a b (fun g' => pOp l (fun c' => Ψ c' g') c) g
    have h := hder (c l) (-Complex.I)
    simp only [pOp, if_pos hc, wirt]
    simp only [Qx8.dv, neg_smul, ← sub_eq_add_neg] at h
    exact h
  · show pbOp l (fun c' => Q.tL k r z z' i Y a b (Ψ c') g) c =
      Q.tL k r z z' i Y a b (fun g' => pbOp l (fun c' => Ψ c' g') c) g
    have h := hder (star (c l)) Complex.I
    simp only [pbOp, if_pos hc, wirtBar]
    simp only [Qx8.dv] at h
    exact h

end PCommPf

theorem residue_projection_commutation : JDRPComm := by
  intro Wp Wq _ _ _ _ k r z z' π π' Dc Ψ _ _ ho hΨ l Y a b c hc g hg hgD
  exact (PCommPf.tL_crd_comm z z' (Fin.last r) Dc Ψ ho hΨ.1 l Y a b hc hg hgD).1

theorem crd_pbOp_QL_last_comm :
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (Dc : (Fin r → ℂ) → Set (Q.Mx k r)) (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)), inWb k r z → inWb k r z' →
    IsOpen {x : (Fin r → ℂ) × Q.Mx k r | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1} →
    Q.FamFF k r z z' π π' (Fin.last r) Dc Ψ →
    ∀ (l : Fin r) (Y : ℂ) (a b : Fin 2), ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), g ∈ Dc c →
      Q.crd (Formalism.QuantumDeterminants.pbOp l) (Q.QL k r z z' (Fin.last r) Y a b Ψ) c g =
        Q.QL k r z z' (Fin.last r) Y a b (Q.crd (Formalism.QuantumDeterminants.pbOp l) Ψ) c g := by
  intro Wp Wq _ _ _ _ k r z z' π π' Dc Ψ _ _ ho hΨ l Y a b c hc g hg hgD
  exact (PCommPf.tL_crd_comm z z' (Fin.last r) Dc Ψ ho hΨ.1 l Y a b hc hg hgD).2

end Formalism.FourierDecayAlt.P.CutMP

end
end

section

open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.En

theorem inCC_wordSum {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m n : ℕ}
    {F : B.Mat k r → E} (hF : B.InCC A (m + n) F) :
    ∀ L : List (ℂ × List (B.Mat k r)), (∀ cw ∈ L, (∀ X ∈ cw.2, B.unitLie k r X) ∧ cw.2.length ≤ n) →
      B.InCC A m (fun g => (L.map fun cw => cw.1 • B.Rw cw.2 F g).sum) := by
  intro L
  induction L with
  | nil =>
    intro _
    exact ⟨0, by simpa using (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_zero (k := k) (r := r) (E := E) (A := A) (m := m))⟩
  | cons cw L ih =>
    intro hL
    have h1 : B.InCC A m (fun g => cw.1 • B.Rw cw.2 F g) := by
      have hw := hL cw (by simp)
      have h0 : B.InCC A (m + cw.2.length) F :=
        Formalism.FourierDecayAlt.P.BetaSesquilinearity.sInCC_mono le_rfl (by omega) hF
      obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.BetaSesquilinearity.InCC_Rw (fun X hX => (hw.1 X hX).1) h0
      exact ⟨_, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul cw.1 hc⟩
    have h2 := ih (fun cw' hcw' => hL cw' (List.mem_cons_of_mem cw hcw'))
    obtain ⟨c₁, hc₁⟩ := h1
    obtain ⟨c₂, hc₂⟩ := h2
    refine ⟨c₁ + c₂, ?_⟩
    simpa [List.map_cons, List.sum_cons] using Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hc₁ hc₂

theorem coefficient_vector_in_L2_class : CVInCC := by
  intro k r E _ _ A m F Y s hF
  obtain ⟨L, hLw, hCV⟩ := Formalism.FourierDecayAlt.P.capelli_word_sum k r Y
  have hck : B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (B.GV k r) F := by
    obtain ⟨c, hc⟩ := hF
    exact Formalism.FourierDecayAlt.P.B5.ckOn_mono (by exact_mod_cast Nat.le_add_left _ _) hc.1
  obtain ⟨c, hc⟩ := inCC_wordSum hF L hLw
  refine ⟨_, Formalism.FourierDecayAlt.P.Qx8.CCle_congr (f := fun g => s • (L.map fun cw => cw.1 • B.Rw cw.2 F g).sum) ?_
    (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul s hc)⟩
  intro g hg
  rw [Pi.smul_apply, hCV E (B.GV k r) F hck g hg hg]

end Formalism.FourierDecayAlt.P.CutMP.En
end

section

open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField

namespace Formalism.FourierDecayAlt.P.CutMP.En

theorem om_sub' {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ JF.Om k r z z') :
    g ∈ Q.Glev k r 0 ∩ {g | 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := by
  obtain ⟨hG, hD, hGf⟩ := hg
  refine ⟨⟨hG, fun a ha => by simp at ha⟩, hGf, fun a => hD _ (by show (a : ℕ) + 1 ≤ r; omega)⟩

theorem stab_fix_gq {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (q : (Fin r → ℂ) × ℂ) {p : Q.Mx k r × Q.Mx k r} (hp : p ∈ NF.Stab k r z z' μsec q.2) :
    p.1 * bigCell k r q.1 (μsec q.2) * p.2 = bigCell k r q.1 (μsec q.2) := by
  obtain ⟨h1, -, h3⟩ := hp
  obtain ⟨-, hsub, hcomm⟩ := Formalism.FourierDecayAlt.P.TwoByOneBlock.uWbFacts k r
  have hc := hcomm q.1 p.1 (hsub z h1)
  have hf := (Formalism.FourierDecayAlt.P.TwoByOneBlock.bigCellFactor k r q.1 (μsec q.2)).1
  have h3' : p.1 * B2.embWb k r (μsec q.2) * p.2 = B2.embWb k r (μsec q.2) := h3
  rw [hf]
  calc p.1 * (bigCell k r q.1 1 * B2.embWb k r (μsec q.2)) * p.2
      = (p.1 * bigCell k r q.1 1) * B2.embWb k r (μsec q.2) * p.2 := by simp only [Matrix.mul_assoc]
    _ = bigCell k r q.1 1 * (p.1 * B2.embWb k r (μsec q.2) * p.2) := by rw [hc]; simp only [Matrix.mul_assoc]
    _ = bigCell k r q.1 1 * B2.embWb k r (μsec q.2) := by rw [h3']

theorem fibre_membership_holds : FibMem := by
  unfold FibMem
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T v hP J hJ q hq
  simp only [NF.Fib, Set.mem_setOf_eq]
  intro p hp
  have hdom : q ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := by
    obtain ⟨hq1, hq2⟩ := hq
    refine ⟨hq1, ?_⟩
    rw [hP.2.2.2.1, hP.2.2.2.2.1]
    exact hq2
  have hg := om_sub' (Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hdom)
  have hfix := stab_fix_gq (T v).base.μsec q hp
  have hJe := hJ.2.2.2 (B.gq (T v).base q) ⟨hg.1, hg.2⟩ p.1 hp.1 p.2 hp.2.1
  exact hJe.symm.trans (congrArg J hfix)

end Formalism.FourierDecayAlt.P.CutMP.En
end

section

namespace Formalism.FourierDecayAlt.P

theorem integration_formula_constant : Formalism.FourierDecayAlt.B2.IntConst :=
  integration_formula_of_parts iterated_integration_formula rank_one_integration_formula b2_conjInvRaw_proof opposite_weyl_haar_exists
    bruhat_big_cell_factorization unipotent_weyl_properties weight_factorization

theorem integration_formula_normalisation_unique : Formalism.FourierDecayAlt.B2.IntNorm :=
  integral_normalisation_from_constant integration_formula_constant

theorem normalisation_unique_every_setting : Formalism.FourierDecayAlt.B2.IntNormB :=
  normalisation_every_setting integration_formula_normalisation_unique

theorem norm_power_integrable_sharp : Formalism.FourierDecayAlt.B2.GNIntSharp :=
  norm_power_integrable_sharp_of_volume spherical_shell_integral matrix_norm_ge_one norm_ball_volume_sharp

theorem matrix_coefficient_integrable_all : Formalism.FourierDecayAlt.B2.CCIntAll :=
  matrix_coefficient_integrable_of_parts matrix_coefficient_bound_by_norm norm_power_integrable_sharp

namespace IntegrationFormulaNormalisation

theorem exists_both : Formalism.FourierDecayAlt.B2.RealPlaceDataExists ∧ Formalism.FourierDecayAlt.B2.RealPlaceDataNonempty :=
  Formalism.FourierDecayAlt.P.SettingConstruction.setting_exists_of_haar_normalisation Formalism.FourierDecayAlt.P.unitary_group_haar_exists Formalism.FourierDecayAlt.P.weyl_haar_exists
    Formalism.FourierDecayAlt.P.unipotent_haar_exists Formalism.FourierDecayAlt.P.integration_formula_normalisation_unique

end IntegrationFormulaNormalisation

theorem setting_with_prescribed_data_exists : Formalism.FourierDecayAlt.B2.RealPlaceDataExists :=
  Formalism.FourierDecayAlt.P.IntegrationFormulaNormalisation.exists_both.1

theorem lemma_b_from_xi : Formalism.FourierDecayAlt.B2.LemmaBFromXi :=
  Formalism.FourierDecayAlt.P.BesselScaling.lemmaBFromXi_of conjugation_invariance_every_setting dilation_jacobian_every_setting matrix_coefficient_integrable_all normalisation_unique_every_setting

end Formalism.FourierDecayAlt.P
end
