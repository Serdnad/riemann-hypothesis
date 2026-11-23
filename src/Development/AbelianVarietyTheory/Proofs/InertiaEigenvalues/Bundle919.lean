module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle872
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle911
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle879
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle890
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle777
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle909
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle885
public import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle849
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2302
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1562
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle908
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle529
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle576
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle649
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle699
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle907
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle912
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001

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


theorem _root_.GlobalTheory.T.centralFlip_splitPlaces_invariantForm_phase : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D) (m : ℕ) (z : GA D V) (x : (AE D)ˣ) (ℓ : (WO V W → ℂ) →ₗ[ℂ] ℂ), IsIdemSum eT T → m ≠ 0 → Formalism.L2.Theta.mt V z = flipElt eT m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → IsFlipDet V eT m x → (∀ y : WO V W, IsHalf (cA D eT) y → ∀ φ : WO V W → ℂ, IsThetaFunO ψ V W φ → ℓ (heisO ψ V W y φ) = ℓ φ) → ∃ r : ℝ, 0 < r ∧ ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → ℓ (om (z⁻¹, 1) f) = (r : ℂ) * ((χW x : Circle) : ℂ)⁻¹ * ℓ f := by
  first | exact @GlobalTheory.LevelSeries.centralFlip_phase | exact GlobalTheory.LevelSeries.centralFlip_phase | (intros; apply GlobalTheory.LevelSeries.centralFlip_phase <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.CellPw

variable {E : Type} [Field E] [NumberField E]

theorem rowInf_tl [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (g : GA E n) (r : Fin n) :
    (fun i => pInf E ((GlobalTheory.CellDec.tl n ϖ l * g).val r i)) = fun i => pInf E (g.val r i) := by
  have h : GeneralLinearGroup.map (pInf E) (GlobalTheory.CellDec.tl n ϖ l * g) = GeneralLinearGroup.map (pInf E) g := by
    rw [map_mul, GlobalTheory.CellDec.tl, pInf_finGL, one_mul]
  funext i
  exact congrArg (fun M : GL (Fin n) (Cinf E) => M.val r i) h

theorem bInt_of_not_mem [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (ℓ : Fin a) (F : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (x : ℝ) (h : GA E a)
    (hm : (fun i => pFin E (h.val ℓ i)) - η ∉ GlobalTheory.ThetaPoisson.latt a J) :
    GlobalTheory.RSCell.bInt ℓ F Φ J η x h = 0 := by
  simp [GlobalTheory.RSCell.bInt, GlobalTheory.RSTheta.rsPsi, GlobalTheory.ThetaPoisson.thetaFn, Set.indicator_of_notMem hm]

theorem bInt_of_mem [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (ℓ : Fin a) (F : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (x : ℝ) (h : GA E a)
    (hm : (fun i => pFin E (h.val ℓ i)) - η ∈ GlobalTheory.ThetaPoisson.latt a J) :
    GlobalTheory.RSCell.bInt ℓ F Φ J η x h =
      ENNReal.ofReal (‖GlobalTheory.JSW.whit F (h * (infGL E a (GlobalTheory.RSTheta.rowGL ℓ (fun i => pInf E (h.val ℓ i))))⁻¹)‖ ^ 2 *
        ‖Φ (fun i => pInf E (h.val ℓ i))‖ * (ideleModule E (GeneralLinearGroup.det h) : ℝ) ^ x) := by
  rw [GlobalTheory.RSCell.bInt, GlobalTheory.RSTheta.rsPsi, GlobalTheory.ThetaPoisson.thetaFn, GlobalTheory.RSTheta.rsInf, Set.indicator_of_mem hm,
    ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  congr 1
  simp only [Pi.one_apply, mul_one, norm_mul, Complex.norm_conj]
  ring

theorem prod_supp_add {n : ℕ} (q : HeightOneSpectrum (𝓞 E) → ℝ) (hq : ∀ v, q v ≠ 0) (f : (Fin n → ℤ) →+ ℤ)
    (a b : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) :
    ∏ v ∈ (a + b).support, q v ^ f ((a + b) v) =
      (∏ v ∈ a.support, q v ^ f (a v)) * ∏ v ∈ b.support, q v ^ f (b v) := by
  have := Finsupp.prod_add_index' (f := a) (g := b) (h := fun v y => q v ^ f y) (fun v => by simp)
    (fun v y₁ y₂ => by simp [zpow_add₀ (hq v)])
  simpa [Finsupp.prod] using this

def wtSHom (n : ℕ) : (Fin n → ℤ) →+ ℤ where
  toFun := GlobalTheory.CellDec.wtS n
  map_zero' := by simp [GlobalTheory.CellDec.wtS]
  map_add' a b := by
    simp only [GlobalTheory.CellDec.wtS, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp <;> ring

def negSumHom (n : ℕ) : (Fin n → ℤ) →+ ℤ where
  toFun a := -∑ i, a i
  map_zero' := by simp
  map_add' a b := by simp [Finset.sum_add_distrib]; ring


omit [Field E] [NumberField E] in
theorem cell_identity : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂ) (F : GA E (m + 1) → ℂ) (l₀ : GlobalTheory.CellDec.abelian₂ E (m + 1) T)
      (U : Subgroup (GL (Fin (m + 1)) (Af E))) (Φ : (Fin (m + 1) → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
    (∀ w, l₀.1 w (Fin.last m) = 0) → (∀ u ∈ U, ∀ g, GlobalTheory.JSW.whit F (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit F g) →
    (∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
      (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, GlobalTheory.JSW.whit F (g * k) = GlobalTheory.JSW.whit F g) →
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖) →
    (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) T ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T, (∀ w, 0 ≤ l.1 w (Fin.last m)) →
      GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ (l₀.1 + l.1)) = GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) *
        ∏ w ∈ l.1.support, (if h : w ∈ T then 1 else GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (α ⟨w, h⟩) (l.1 w))) →
    tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) → (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    (∀ y : Fin (m + 1) → Af E, y - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J →
      ∃ κ ∈ U, (∀ w ∉ T, GeneralLinearGroup.map (pLoc E w) κ = 1) ∧
        ∀ w ∈ T, ∀ j, (GeneralLinearGroup.map (pLoc E w) κ : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j =
          pLoc E w (y j)) →
    ∀ (x : ℝ), ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) T, ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T,
      ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) * GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) =
        ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) * GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * g) *
          GlobalTheory.RSCell.cellProd T α x (l.1 - l₀.1) := by
  intro E _ _ _ m T ϖ hϖ α F l₀ U Φ J hl₀ hU hK hN hprof hΦ hJ horb x g hg l
  have hνT : ∀ v ∈ T, (l.1 - l₀.1) v = 0 := fun v hv => by simp [l.2 v hv, l₀.2 v hv]
  let ν : GlobalTheory.CellDec.abelian₂ E (m + 1) T := ⟨l.1 - l₀.1, hνT⟩
  have hνl : l₀.1 + ν.1 = l.1 := by simp [ν]
  have hνw : ∀ w, ν.1 w (Fin.last m) = l.1 w (Fin.last m) := fun w => by simp [ν, hl₀ w]
  by_cases hneg : ∃ w, l.1 w (Fin.last m) < 0
  · obtain ⟨w, hw⟩ := hneg
    have hwT : w ∉ T := fun h => by simp [l.2 w h] at hw
    rw [bInt_of_not_mem _ _ _ _ _ _ _ (GlobalTheory.T.lastRow_sub_single_not_mem_lattice_of_neg_exponent E m T ϖ hϖ J hJ g hg l w hw)]
    have h2 : GlobalTheory.RSCell.cellProd T α x (l.1 - l₀.1) = 0 := by
      refine Finset.prod_eq_zero (i := w) ?_ ?_
      · rw [Finsupp.mem_support_iff]
        intro h
        have := congrFun h (Fin.last m)
        simp [hl₀ w] at this
        omega
      · rw [dite_eq_right hwT]
        exact GlobalTheory.RSCell.locFac_of_neg _ _ _ (i := Fin.last m) (by simp [hl₀ w]; exact hw)
    rw [h2]
    simp
  push_neg at hneg
  have hl₀n : ∀ w, 0 ≤ l₀.1 w (Fin.last m) := fun w => (hl₀ w).ge
  have hposl := GlobalTheory.T.lastRow_diagonal_mul_mem_lattice_iff E m T ϖ hϖ J hJ g hg l hneg
  have hposl₀ := GlobalTheory.T.lastRow_diagonal_mul_mem_lattice_iff E m T ϖ hϖ J hJ g hg l₀ hl₀n
  by_cases hI : (fun i => pFin E (g.val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J
  swap
  · rw [bInt_of_not_mem _ _ _ _ _ _ _ (fun h => hI (hposl.1 h)),
      bInt_of_not_mem _ _ _ _ _ _ _ (fun h => hI (hposl₀.1 h))]
    simp
  rw [bInt_of_mem _ _ _ _ _ _ _ (hposl.2 hI), bInt_of_mem _ _ _ _ _ _ _ (hposl₀.2 hI),
    rowInf_tl, rowInf_tl]
  set u : Fin (m + 1) → Cinf E := fun i => pInf E (g.val (Fin.last m) i) with hu
  by_cases hΦu : Φ u = 0
  · simp [hΦu]
  have hunit : IsUnit (pInf E (g.val (Fin.last m) (Fin.last m))) :=
    GlobalTheory.RSTheta.isUnit_of_mem_rowSet (hΦ (subset_tsupport _ hΦu))
  obtain ⟨p, hp, hpl⟩ := GlobalTheory.T.exists_mirabolic_whittaker_reduction_cell E m T ϖ F U J hU hK hN horb g hg hunit hI
  rw [hpl l, hpl l₀, GlobalTheory.T.ideleModule_det_diagonalUniformiser_mul E (m + 1) ϖ hϖ l.1 g, GlobalTheory.T.ideleModule_det_diagonalUniformiser_mul E (m + 1) ϖ hϖ l₀.1 g]
  have hpr := hprof p hp ν (fun w => by rw [hνw]; exact hneg w)
  rw [hνl] at hpr
  rw [hpr]

  have hq : ∀ v : HeightOneSpectrum (𝓞 E), (qV E v : ℝ) ≠ 0 := fun v => by
    rw [qV, Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hqpos : ∀ v : HeightOneSpectrum (𝓞 E), 0 < (qV E v : ℝ) := fun v =>
    lt_of_le_of_ne (Nat.cast_nonneg _) (hq v).symm
  have hcell : GlobalTheory.RSCell.cellProd T α x (l.1 - l₀.1) = ENNReal.ofReal (∏ w ∈ ν.1.support,
      ((qV E w : ℝ) ^ GlobalTheory.CellDec.wtS (m + 1) (ν.1 w) * (qV E w : ℝ) ^ (-((∑ i, (ν.1 w i : ℝ)) * x)) *
        ‖(if h : w ∈ T then 1 else GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (α ⟨w, h⟩) (ν.1 w))‖ ^ 2)) := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun w _ => by positivity)]
    refine Finset.prod_congr rfl fun w hw => ?_
    have hwT : w ∉ T := fun h => (Finsupp.mem_support_iff.1 hw) (hνT w h)
    rw [dite_eq_right hwT, dite_eq_right hwT, ← GlobalTheory.T.spherical_local_factor_norm_sq (Ideal.absNorm w.asIdeal) (Nat.pos_of_ne_zero (by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot)) m (α ⟨w, hwT⟩) x (ν.1 w) (by rw [hνw]; exact hneg w),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm_eq_enorm]
    rfl
  have hd0 : ∀ k : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℤ), 0 ≤ GlobalTheory.CellDec.dinv (m + 1) k := fun k =>
    Finset.prod_nonneg fun v _ => (zpow_pos (hqpos v) _).le
  rw [hcell, ← ENNReal.ofReal_mul (hd0 _), ← ENNReal.ofReal_mul (hd0 _), ← ENNReal.ofReal_mul (mul_nonneg (hd0 _) <| mul_nonneg (mul_nonneg (by positivity) (norm_nonneg _))
    (Real.rpow_nonneg (mul_nonneg (Finset.prod_nonneg fun v _ => (inv_pos.2 (zpow_pos (hqpos v) _)).le)
      ((ideleModule E (GeneralLinearGroup.det g)).2.le)) _))]
  congr 1
  have hd : GlobalTheory.CellDec.dinv (m + 1) l.1 = GlobalTheory.CellDec.dinv (m + 1) l₀.1 *
      ∏ w ∈ ν.1.support, (qV E w : ℝ) ^ GlobalTheory.CellDec.wtS (m + 1) (ν.1 w) := by
    rw [← hνl]
    exact prod_supp_add (fun v => (qV E v : ℝ)) hq (wtSHom (m + 1)) l₀.1 ν.1
  have hQ : ∀ k : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℤ),
      ∏ v ∈ k.support, ((qV E v : ℝ) ^ ∑ i, k v i)⁻¹ = ∏ v ∈ k.support, (qV E v : ℝ) ^ negSumHom (m + 1) (k v) := by
    intro k
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← _root_.zpow_neg]; rfl
  have hQl : ∏ v ∈ l.1.support, ((qV E v : ℝ) ^ ∑ i, l.1 v i)⁻¹ =
      (∏ v ∈ l₀.1.support, ((qV E v : ℝ) ^ ∑ i, l₀.1 v i)⁻¹) * ∏ v ∈ ν.1.support, ((qV E v : ℝ) ^ ∑ i, ν.1 v i)⁻¹ := by
    rw [hQ, hQ, hQ, ← hνl]
    exact prod_supp_add (fun v => (qV E v : ℝ)) hq (negSumHom (m + 1)) l₀.1 ν.1
  have hQν : (∏ v ∈ ν.1.support, ((qV E v : ℝ) ^ ∑ i, ν.1 v i)⁻¹) ^ x =
      ∏ v ∈ ν.1.support, (qV E v : ℝ) ^ (-((∑ i, (ν.1 v i : ℝ)) * x)) := by
    have hprod : ∀ s : Finset (HeightOneSpectrum (𝓞 E)),
        (∏ v ∈ s, ((qV E v : ℝ) ^ ∑ i, ν.1 v i)⁻¹) ^ x =
          ∏ v ∈ s, (((qV E v : ℝ) ^ ∑ i, ν.1 v i)⁻¹) ^ x := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha,
          Real.mul_rpow (inv_pos.2 (zpow_pos (hqpos a) _)).le
            (Finset.prod_nonneg fun v _ => (inv_pos.2 (zpow_pos (hqpos v) _)).le), ih]
    rw [hprod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← Real.rpow_intCast, ← Real.rpow_neg (hqpos v).le, ← Real.rpow_mul (hqpos v).le]
    push_cast
    ring_nf
  have hD := ((ideleModule E (GeneralLinearGroup.det g)).2 : (0 : ℝ) < _)
  have hQ₀ : 0 ≤ ∏ v ∈ l₀.1.support, ((qV E v : ℝ) ^ ∑ i, l₀.1 v i)⁻¹ :=
    Finset.prod_nonneg fun v _ => (inv_pos.2 (zpow_pos (hqpos v) _)).le
  have hQν0 : 0 ≤ ∏ v ∈ ν.1.support, ((qV E v : ℝ) ^ ∑ i, ν.1 v i)⁻¹ :=
    Finset.prod_nonneg fun v _ => (inv_pos.2 (zpow_pos (hqpos v) _)).le
  rw [hd, hQl, Real.mul_rpow (mul_nonneg hQ₀ hQν0) hD.le, Real.mul_rpow hQ₀ hQν0, hQν, Real.mul_rpow hQ₀ hD.le,
    norm_mul, norm_prod, mul_pow, ← Finset.prod_pow, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

end GlobalTheory.CellPw
end
end

section

section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open Matrix


theorem _root_.GlobalTheory.Tx.exists_unipotentInvariant_compactlySupported_weight : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (x₀ : GA E (m + 1)),
    ∃ κ : GA E (m + 1) → ℝ, Continuous κ ∧ (∀ h, 0 ≤ κ h) ∧ (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ h, κ (u * h) = κ h) ∧
      (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h, κ h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) ∧
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ h, κ (h * finGL E (m + 1) u) = κ h) ∧
      (∀ g, ContDiffOn ℝ ∞ (chart (fun h => (κ h : ℂ)) g) (invSet E (m + 1))) ∧ 0 < κ x₀ := by
  first
  | exact @GlobalTheory.KappaCut.exists_kappa
  | exact GlobalTheory.KappaCut.exists_kappa
  | (intros; apply GlobalTheory.KappaCut.exists_kappa <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open Matrix


theorem _root_.GlobalTheory.Tx.contDiffOn_chart_globalWhittakerCoefficient : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    IsAutForm φ → ∀ g, ContDiffOn ℝ ∞ (chart (GlobalTheory.JSW.whit φ.1) g) (invSet E a) := by
  first | (exact @GlobalTheory.JSW.WhitSmooth.whit_contDiffOn) | (exact GlobalTheory.JSW.WhitSmooth.whit_contDiffOn) | (intros; apply GlobalTheory.JSW.WhitSmooth.whit_contDiffOn  <;> assumption)
end

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open Matrix

namespace GlobalTheory.JSW.MatchedVec

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem mem_mspanR_of_mem (π : CuspSub E a) {φ : Sm E a} (hφ : φ ∈ π.V) : φ.1 ∈ GlobalTheory.JSW.mspanR π :=
  Submodule.mem_sInf.2 fun _ hS => hS.1 φ hφ

def stab (φ : Sm E a) : Subgroup (GL (Fin a) (Af E)) where
  carrier := {k | finRep E a k φ = φ}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hy, hx]
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem exists_level (φ : Sm E a) (hφ : IsAutForm φ) :
    ∃ U : Subgroup (GL (Fin a) (Af E)), IsOpen (U : Set (GL (Fin a) (Af E))) ∧
      ∀ u ∈ U, ∀ g, φ.1 (g * finGL E a u) = φ.1 g :=
  ⟨stab φ, hφ.level, fun u hu g => congrArg (fun ψ : Sm E a => ψ.1 g) (show finRep E a u φ = φ from hu)⟩

theorem chart_mul (f f' : GA E a → ℂ) (g : GA E a) (x : Lie E a) :
    chart (fun h => f h * f' h) g x = chart f g x * chart f' g x := by
  unfold chart
  split_ifs <;> simp

end GlobalTheory.JSW.MatchedVec


open GlobalTheory.JSW.MatchedVec in
theorem GlobalTheory.JSW.MatchedVec.matched_vectors : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) →
    ∀ (π : CuspSub E (m + r + 1 + 1)) (π' : CuspSub E (m + 1)), π.IsUnitary → π'.IsUnitary →
    ∀ (α : HeightOneSpectrum (𝓞 E) → Fin (m + r + 1 + 1) → ℂˣ) (β : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ),
    (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) →
    (∀ w ∉ S, HasSatGL w (π'.locRep w) (Finset.univ.val.map (β w))) →
    ∃ (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ) (κ : GA E (m + 1) → ℝ),
      φ ∈ GlobalTheory.JSW.mspanR π ∧ φ' ∈ GlobalTheory.JSW.mspanR π' ∧
      (∃ U : Subgroup (GL (Fin (m + r + 1 + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + r + 1 + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, φ (g * finGL E (m + r + 1 + 1) u) = φ g) ∧
      (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + r + 1 + 1)), ∀ g,
        φ (g * finGL E (m + r + 1 + 1) (locGL E (m + r + 1 + 1) w k)) = φ g) ∧
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, φ' (g * finGL E (m + 1) u) = φ' g) ∧
      (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), ∀ g, φ' (g * finGL E (m + 1) (locGL E (m + 1) w k)) = φ' g) ∧
      (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
        ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
        ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
          GlobalTheory.JSW.whit φ' (h * GlobalTheory.JSW.tl ϖ l) =
            (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (β w i : ℂ)) (l w)) * GlobalTheory.JSW.whit φ' h) ∧
      (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
        ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
        ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
          GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1)
                       (h * GlobalTheory.JSW.tl ϖ l)) =
            (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (GlobalTheory.RSnmUnf.padNat (l w))) *
              GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)) ∧
      (∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
        GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) =
          (κ h : ℂ) * GlobalTheory.JSW.whit φ' h) ∧
      Continuous κ ∧ (∀ h, 0 ≤ κ h) ∧ (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ h, κ (u * h) = κ h) ∧
      (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, κ h ≠ 0 →
        ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) ∧
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ h, κ (h * finGL E (m + 1) u) = κ h) ∧
      ∃ h₀ ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, 0 < κ h₀ ∧ GlobalTheory.JSW.whit φ' h₀ ≠ 0 := by
  intro E _ _ _ m r S hcond π π' hπu hπ'u α β hα hβ
  obtain ⟨φ', hφ'V, hφ'K, x₀, hx₀S, hx₀⟩ := GlobalTheory.T.exists_spherical_cuspForm_whittaker_ne_zero E m S hcond π' β hβ
  obtain ⟨φ₀, hφ₀V, hφ₀K, x₁, hx₁S, hx₁⟩ := GlobalTheory.T.exists_spherical_cuspForm_whittaker_ne_zero E (m + r + 1) S hcond π α hα
  obtain ⟨κ, hκc, hκ0, hκN, ⟨C, hC, hκC⟩, ⟨Uκ, hUκo, hUκ⟩, hκsm, hκx₀⟩ := GlobalTheory.Tx.exists_unipotentInvariant_compactlySupported_weight E m x₀
  have haut' : IsAutForm φ' := (π'.cusp φ' hφ'V).1
  obtain ⟨U', hU'o, hU'⟩ := exists_level φ' haut'
  have hWN : ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ'.1 (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ'.1 g :=
    fun u hu g => GlobalTheory.JSW.WhitModel.whit_mul haut'.continuous (fun γ g => haut'.left γ g) hu g
  have hWU : ∀ u ∈ U', ∀ g, GlobalTheory.JSW.whit φ'.1 (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit φ'.1 g := by
    intro u hu g
    rw [← GlobalTheory.JSW.KirSemi.whit_rt]
    congr 1
    funext y
    exact hU' u hu y
  have hWsm := GlobalTheory.Tx.contDiffOn_chart_globalWhittakerCoefficient E (m + 1) φ' haut'
  set βf : GA E (m + 1) → ℂ := fun h => (κ h : ℂ) * GlobalTheory.JSW.whit φ'.1 h with hβf
  have hβN : ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, βf (u * g) = GlobalTheory.JSW.psiN u * βf g := by
    intro u hu g
    simp only [hβf, hκN u hu g, hWN u hu g]
    ring
  have hβC : ∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, βf h ≠ 0 →
      ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C := by
    refine ⟨C, hC, fun h _ hne => hκC h ?_⟩
    intro h0
    apply hne
    simp [hβf, h0]
  have hβU : ∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
      ∀ u ∈ U, ∀ g, βf (g * finGL E (m + 1) u) = βf g := by
    refine ⟨Uκ ⊓ U', hUκo.inter hU'o, fun u hu g => ?_⟩
    simp only [hβf, hUκ u hu.1 g, hWU u hu.2 g]
  have hβsm : ∀ g, ContDiffOn ℝ ∞ (chart βf g) (invSet E (m + 1)) := by
    intro g
    have e : chart βf g = fun x => chart (fun h => (κ h : ℂ)) g x * chart (GlobalTheory.JSW.whit φ'.1) g x :=
      funext fun x => chart_mul _ _ g x
    rw [e]
    exact (hκsm g).mul (hWsm g)
  obtain ⟨b, hbN, hbC, hbU, hbsm, hbblk⟩ := GlobalTheory.T.exists_whittaker_bump_extension_schur_complement E m r S βf hβN hβC hβU hβsm
  obtain ⟨F, hFspan, hFb, hFU, hFinv, hFeig⟩ :=
    GlobalTheory.T.kirillov_semilocal_smooth_bump E (m + r + 1) S b hbN hbC hbU hbsm π φ₀ hφ₀V ⟨x₁, hx₁S, hx₁⟩
  refine ⟨F, φ'.1, κ, hFspan, mem_mspanR_of_mem π' hφ'V, hFU, ?_, ⟨U', hU'o, hU'⟩, ?_, ?_, ?_, ?_,
    hκc, hκ0, hκN, ⟨C, hC, fun h _ hne => hκC h hne⟩, ⟨Uκ, hUκo, hUκ⟩, ⟨x₀, hx₀S, hκx₀, hx₀⟩⟩
  · intro w hw k hk g
    refine hFinv _ (pInf_finGL _) ?_ ?_ g
    · intro w' hw'
      have hne : w' ≠ w := fun h => hw (h ▸ hw')
      rw [GlobalTheory.JSW.BumpShintani.map_comp_eq, pFin_finGL]
      exact pLoc_locGL_of_ne hne _
    · intro g'
      exact congrArg (fun ψ : Sm E (m + r + 1 + 1) => ψ.1 g') (hφ₀K w hw k hk)
  · intro w hw k hk g
    exact congrArg (fun ψ : Sm E (m + 1) => ψ.1 g) (hφ'K w hw k hk)
  · intro ϖ hϖ l hl h hh
    exact GlobalTheory.T.whittaker_mul_torus_iterated_factorisation E (m + 1) S hcond π' β hβ φ' hφ'V hφ'K ϖ hϖ l hl h hh
  · intro ϖ hϖ l hl h hh
    set l' : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + r + 1 + 1) → ℕ) :=
      l.mapRange GlobalTheory.RSnmUnf.padNat GlobalTheory.RSnmUnf.padNat_zero with hl'
    have hsupp : l'.support = l.support := by
      ext w
      simp only [hl', Finsupp.mem_support_iff, Finsupp.mapRange_apply, ne_eq]
      constructor
      · intro h1 h2
        apply h1
        rw [h2, GlobalTheory.RSnmUnf.padNat_zero]
      · intro h1 h2
        apply h1
        funext i
        have := congrFun h2 ⟨i, by omega⟩
        simpa [GlobalTheory.RSnmUnf.padNat, i.2] using this
    have hl's : ∀ w ∈ l'.support, w ∉ S := fun w hw => hl w (hsupp ▸ hw)
    have hC := GlobalTheory.T.whittaker_mul_torus_iterated_factorisation E (m + r + 1 + 1) S hcond π α hα φ₀ hφ₀V hφ₀K ϖ hϖ l' hl's
    have hS : ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (GlobalTheory.JSW.tl ϖ l') = 1 :=
      fun w hw => GlobalTheory.JSW.BumpShintani.loc_tl ϖ l' w (fun h => hl's w h hw)
    have hmir := GlobalTheory.T.blockGL_supported_mem_mirabolic_supported E m r S h hh
    rw [map_mul, GlobalTheory.T.blockEmbeddingGL_torus_element_zero_padded E m r ϖ l, hFeig _ _ (GlobalTheory.JSW.BumpShintani.pInf_tl ϖ l') hS hC _ hmir.1, hsupp]
    rfl
  · intro h hh
    clear hβsm hβU hβC hβN hWsm hWU hWN hFeig hFinv
    exact (hFb _ (GlobalTheory.T.blockGL_supported_mem_mirabolic_supported E m r S h hh)).trans (hbblk h hh)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.exists_conjugateHalf_prescribed_adjoint_frameMatrix : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D), e * e = e → ∀ z : Matrix (Fin S.rank) (Fin T.rank) (EAf D), (∀ i j, toEAf D e * z i j = z i j) → ∃ y : WO S T, IsHalf (cA D e) y ∧ (∀ i j, infPart D (y i j) = 0) ∧ frMapAdj S T βS βT y = z := by
  first | exact @GlobalTheory.AdjHalfLift.exists_half_frMapAdj | exact GlobalTheory.AdjHalfLift.exists_half_frMapAdj | (intros; apply GlobalTheory.AdjHalfLift.exists_half_frMapAdj <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.reduction_adjointFrame_conj_half_two_parts : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Pg Q : Finset (Pl D.host.E)) (eg eQ : AE D), IsIdemSum eg Pg → IsIdemSum eQ Q → Disjoint Pg Q → IsIdemSum (eg + eQ) (Pg ∪ Q) → ∀ x : WO S T, IsHalf (cA D (eg + eQ)) x → IsIntM (frMapAdj S T βS βT x) → (∀ PP ∈ Pg, redM PP (frMapAdj S T βS βT (cA D eg • x)) = redM PP (frMapAdj S T βS βT x)) ∧ (∀ PP ∈ Q, redM PP (frMapAdj S T βS βT (cA D eQ • x)) = redM PP (frMapAdj S T βS βT x)) := by
  first | exact @GlobalTheory.TwoStepRed.redM_twoStep | exact GlobalTheory.TwoStepRed.redM_twoStep | (intros; apply GlobalTheory.TwoStepRed.redM_twoStep <;> assumption)
end
