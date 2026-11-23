module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle872
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle074
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlacePairMovesLatticeVacuumReading
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1142
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle920
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle911
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle876
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBddFormsOfWithSmoothings
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle542
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableInfMeasure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumRsPsiEqTsumNeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle879
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle885
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle919
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle898
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle884
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle889
public import GroundTheory.AutomorphicForms.Bundle012
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle921
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854

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

namespace GlobalTheory.VacTransFix

theorem nsmul_cancel {D : D7} {V W : HSp D} {M : ℕ} (hM : M ≠ 0) {x x' : WO V W} (h : M • x = M • x') : x = x' := by
  set a : AE D := algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) ((M : D.host.F)⁻¹)) with ha_def
  have ha : a * (M : AE D) = 1 := by
    have e : (M : AE D) = algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (M : D.host.F)) := by
      simp [map_natCast]
    rw [e, ha_def, ← map_mul, ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hM), map_one, map_one]
  have key : ∀ z : WO V W, a • (M • z) = z := fun z => by
    rw [← Nat.cast_smul_eq_nsmul (AE D), smul_smul, ha, one_smul]
  rw [← key x, h, key]

theorem fix_trans : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ M : ℕ, M ≠ 0 → ∃ J : Subgroup (Bridge.Gf V), IsOpen (J : Set (Bridge.Gf V)) ∧ ∀ k ∈ GfC V, fin V k ∈ J → ∀ y : WO V W, M • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → om (k, 1) (heisO ψ V W y f₀) = heisO ψ V W y f₀ := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP M hM
  obtain ⟨hpair, -, -, -, hsdV, hsdW, -, hcart, hvac⟩ := hP
  obtain ⟨J₁, hJ₁o, hJ₁⟩ := GlobalTheory.VacFixOpen.exists_open_fix_vacO D ψ θ V W χV χW om hpair.weil hpair.sigV hpair.sigW
    (fun _ => 1) sW (fun τ => GlobalTheory.SmoothVac.isCartanInv_one V hpair.std τ) hcart ΛV ΛW hsdV hsdW f₀ hvac
  obtain ⟨J₂, hJ₂o, hJ₂⟩ := GlobalTheory.LatFixMod.exists_open_keep_cong D V W ΛV ΛW hsdV hsdW (2 * M * M)
    (Nat.mul_pos (Nat.mul_pos two_pos (Nat.pos_of_ne_zero hM)) (Nat.pos_of_ne_zero hM))
  refine ⟨J₁ ⊓ J₂, by rw [Subgroup.coe_inf]; exact hJ₁o.inter hJ₂o, fun k hk hkJ y hy => ?_⟩
  have hθ : IsThetaFunO ψ V W f₀ := hvac.2.theta
  rw [hpair.weil.om_heis k 1 y f₀ hθ, hJ₁ k hk hkJ.1]
  obtain ⟨l, hl, e⟩ := (hJ₂ k hk hkJ.2).2 (M • y) hy
  have hlin : actO V W k 1 (M • y) = M • actO V W k 1 y :=
    (AddMonoidHom.mk' (actO V W k 1) (GlobalTheory.LatNhds.actO_add k 1)).map_nsmul M y
  have e2 : M • actO V W k 1 y = M • (y + 2 • (M • l)) := by
    rw [← hlin, e, smul_add, smul_smul, smul_smul, show 2 * M * M = M * 2 * M by ring]
  rw [nsmul_cancel hM e2]
  refine GlobalTheory.AdForm.SplitGen.heisO_add_two ψ (hvac.2.lat.1 _ (AddSubgroup.nsmul_mem _ hl M)) ?_
  rw [GlobalTheory.RatSelfDual.symplO_nsmul]
  exact GlobalTheory.LatVac.char_sympl_eq_one hvac.1 hsdV hsdW hy hl

end GlobalTheory.VacTransFix

end
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.FlipScal

open MeasureTheory

theorem nrm2_const_smul {D : D7} {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (c : ℂ) (f : Mx D m n → ℂ) :
    nrm2 μ 𝓕 (c • f) = ‖c‖ ^ 2 * nrm2 μ 𝓕 f := by
  unfold nrm2
  rw [← integral_const_mul]
  congr 1
  funext w
  rw [Pi.smul_apply, norm_smul, mul_pow]

theorem moved_vacuum_factor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D) (z : GA D V) (x : (AE D)ˣ) (lam : ℂ) (Y : Finset (WO V W)), IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → z ∈ GfC V → Formalism.L2.Theta.mt V z = flipElt eT m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → IsFlipDet V eT m x → (∀ y ∈ Y, IsHalf (cA D eT) y ∧ m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) → (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → y = y') → Y.card = flipIdx V W T m → om (z⁻¹, 1) f₀ = lam • ∑ y ∈ Y, heisO ψ V W y f₀ → lam = flipScal χW V W T m x := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT z x lam Y hT hm hcop hTm hz hmt hx hY hYu hcard hom
  have hm0 : m ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hm
  have hW := hP.1.weil
  have hf := hP.2.2.2.2.2.2.2.2
  obtain ⟨ℓ, hℓ0, hℓ⟩ := GlobalTheory.T.exists_conjHalfInvariant_form_idemSum_vacuum_ne_zero D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T eT hT
  obtain ⟨r, hr, hrℓ⟩ := GlobalTheory.T.centralFlip_splitPlaces_invariantForm_phase D ψ V W χV χW om hW T eT m z x ℓ hT hm0 hmt hx hℓ
  have hth := hf.2.theta
  have h1 := hrℓ f₀ hth
  have hsum : ℓ (∑ y ∈ Y, heisO ψ V W y f₀) = (Y.card : ℂ) * ℓ f₀ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_congr rfl fun y hy => hℓ y (hY y hy).1 f₀ hth, Finset.sum_const, nsmul_eq_mul]
  rw [hom, map_smul, hsum, smul_eq_mul] at h1
  have h2 : lam * Y.card = r * ((χW x : Circle) : ℂ)⁻¹ := mul_right_cancel₀ hℓ0 (by rw [← h1]; ring)
  obtain ⟨p, hp⟩ := hf.2.norm.1
  have hn := GlobalTheory.T.weil_representation_preserves_norm D ψ V W χV χW om hW p.1 p.2 hp (z⁻¹, 1) f₀ hth (hf.2.norm.2 p hp)
  rw [hom, nrm2_const_smul, GlobalTheory.T.vacuumTranslates_conjHalf_sq_norm_eq_card D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T eT hT Y (fun y hy => (hY y hy).1) hYu p.1 p.2
    hp] at hn
  have hχ : ‖((χW x : Circle) : ℂ)⁻¹‖ = 1 := by rw [norm_inv, Circle.norm_coe, inv_one]
  have h3 : ‖lam‖ * Y.card = r := by
    have := congrArg norm h2
    rwa [norm_mul, norm_mul, hχ, mul_one, Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg hr.le] at this
  have hN : (0 : ℝ) < Y.card := by
    rcases (Nat.eq_zero_or_pos Y.card) with h | h
    · rw [h, Nat.cast_zero, mul_zero] at h3; exact absurd h3 hr.ne
    · exact_mod_cast h
  have h4 : r = Real.sqrt (Y.card : ℝ) := by
    rw [← h3]
    have : ‖lam‖ ^ 2 = (Y.card : ℝ)⁻¹ := eq_inv_of_mul_eq_one_left hn
    rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq hN.le (by positivity),
      show ‖lam‖ * (Y.card : ℝ) * (‖lam‖ * Y.card) = ‖lam‖ ^ 2 * Y.card * Y.card by ring, this,
      inv_mul_cancel₀ hN.ne', one_mul]
  have hNc : (Y.card : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold flipScal
  rw [← hcard]
  have hs : Real.sqrt (Y.card : ℝ) ≠ 0 := (Real.sqrt_pos.2 hN).ne'
  have h5 : lam = r * ((χW x : Circle) : ℂ)⁻¹ / Y.card := by rw [← h2]; field_simp
  rw [h5, h4]
  have hsq : ((Real.sqrt (Y.card : ℝ) : ℝ) : ℂ) * ((Real.sqrt (Y.card : ℝ) : ℝ) : ℂ) = Y.card := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hN.le]; push_cast; rfl
  have hsc : ((Real.sqrt (Y.card : ℝ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs
  field_simp
  rw [← hsq]
  ring

end GlobalTheory.FlipScal

end
end

section

noncomputable section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open GlobalTheory.RSTheta GlobalTheory.ShortVecDecay GlobalTheory.Petersson GlobalTheory.CuspQuot GlobalTheory.ThetaPoisson GroundTheory.Global GlobalTheory.RSThetaLow
open GroundTheory.Automorphic.GJMatrix
open scoped nonZeroDivisors ComplexConjugate

namespace GlobalTheory.RSResidue

theorem continuous_integral_of_compact {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasureOnCompacts ν] {K : Set Y} (hK : IsCompact K)
    {F : X → Y → ℂ} (hF : Continuous fun p : X × Y => F p.1 p.2) (h0 : ∀ x, ∀ y ∉ K, F x y = 0) :
    Continuous fun x => ∫ y, F x y ∂ν := by
  have hI : (fun x => ∫ y, F x y ∂ν) = fun x => ∫ y in K, F x y ∂ν :=
    funext fun x => (setIntegral_eq_integral_of_forall_compl_eq_zero (h0 x)).symm
  rw [hI]
  have hc : ∀ x, Continuous (F x) := fun x => hF.comp (continuous_const.prodMk continuous_id)
  have hint : ∀ x, IntegrableOn (F x) K ν := fun x => (hc x).continuousOn.integrableOn_compact hK
  set m : ℝ := ν.real K with hm
  have hm0 : 0 ≤ m := measureReal_nonneg
  refine continuous_iff_continuousAt.2 fun x₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hδ : 0 < ε / (m + 1) := by positivity
  have hev : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ K, dist (F x y) (F x₀ y) < ε / (m + 1) := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have h1 := Metric.tendsto_nhds.1 (hF.continuousAt (x := (x₀, y))) (ε / (m + 1) / 2) (by positivity)
    have h2 := Metric.tendsto_nhds.1 ((hc x₀).comp continuous_snd |>.continuousAt (x := (x₀, y)))
      (ε / (m + 1) / 2) (by positivity)
    filter_upwards [h1, h2] with z hz1 hz2
    calc dist (F z.1 z.2) (F x₀ z.2) ≤ dist (F z.1 z.2) (F x₀ y) + dist (F x₀ z.2) (F x₀ y) :=
          dist_triangle_right _ _ _
      _ < ε / (m + 1) / 2 + ε / (m + 1) / 2 := add_lt_add hz1 hz2
      _ = ε / (m + 1) := by ring
  filter_upwards [hev] with x hx
  rw [dist_eq_norm, ← integral_sub (hint x) (hint x₀)]
  have h3 : ‖∫ y in K, (F x y - F x₀ y) ∂ν‖ ≤ ε / (m + 1) * m :=
    norm_setIntegral_le_of_norm_le_const hK.measure_lt_top fun y hy => by
      rw [← dist_eq_norm]; exact (hx y hy).le
  refine h3.trans_lt ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem rsHat_zero_eq {ℓ : Fin a} {Φ : (Fin a → Cinf E) → ℂ} (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E)
    (F F' : Sm E a) (hΦ : IsTest (rowSet E ℓ) Φ) : ∃ c : ℂ, ∀ g : GA E a,
      adelicFourierPi E (rsPsi ℓ F.1 F'.1 Φ J η g) 0 = (∫ u, rsInf ℓ F.1 F'.1 Φ g u ∂infMeasure E a) * c := by
  refine ⟨(finiteAdelicChar E (∑ i, η i * pFin E ((0 : Fin a → Ad E) i)) : ℂ) *
        (latt a (traceDualIdeal E J)).indicator 1 (fun i => pFin E ((0 : Fin a → Ad E) i)) *
        ((finiteMeasurePi E (latt a J)).toReal : ℂ), fun g => ?_⟩
  have h := rsHat_eq (ℓ := ℓ) J η F F' hΦ g 0
  have e : (fun i => pInf E ((0 : Fin a → Ad E) i)) = 0 := funext fun _ => map_zero _
  have hF : infFourier (rsInf ℓ F.1 F'.1 Φ g) (fun i => pInf E ((0 : Fin a → Ad E) i)) =
      ∫ u, rsInf ℓ F.1 F'.1 Φ g u ∂infMeasure E a := by
    rw [e, infFourier]
    simp
  change rsHat ℓ F.1 F'.1 Φ J η g 0 = _
  rw [h, hF]
  ring

variable {ω : HChar E}

theorem rsHat_zero_props (hω : ω.IsUnitary) {φ φ' : Sm E a} (h : φ.1 ∈ bddForms E a ω) (h' : φ'.1 ∈ bddForms E a ω)
    {ℓ : Fin a} {Φ : (Fin a → Cinf E) → ℂ} (hΦ : IsTest (rowSet E ℓ) Φ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) :
    Continuous (fun g : GA E a => adelicFourierPi E (rsPsi ℓ φ.1 φ'.1 Φ J η g) 0) ∧
    (∃ C : ℝ, ∀ g : GA E a, ‖adelicFourierPi E (rsPsi ℓ φ.1 φ'.1 Φ J η g) 0‖ ≤ C) ∧
    ∀ γ ∈ latticeGL E a, ∀ g : GA E a,
      adelicFourierPi E (rsPsi ℓ φ.1 φ'.1 Φ J η (γ * g)) 0 = adelicFourierPi E (rsPsi ℓ φ.1 φ'.1 Φ J η g) 0 := by
  obtain ⟨c, hc⟩ := rsHat_zero_eq J η φ φ' hΦ
  have hj : Continuous fun p : GA E a × (Fin a → Cinf E) => rsInf ℓ φ.1 φ'.1 Φ p.1 p.2 :=
    continuous_rsInf h.1 h'.1 hΦ.1.continuous hΦ.2.2
  have h0 : ∀ g, ∀ u ∉ tsupport Φ, rsInf ℓ φ.1 φ'.1 Φ g u = 0 := fun g u hu => by
    rw [rsInf, image_eq_zero_of_notMem_tsupport hu, mul_zero]
  refine ⟨?_, ?_, ?_⟩
  · simp only [hc]
    exact (continuous_integral_of_compact (infMeasure E a) hΦ.2.1 hj h0).mul continuous_const
  · obtain ⟨C, hC⟩ := h.2.2.2
    obtain ⟨C', hC'⟩ := h'.2.2.2
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
    have hi : Integrable (fun u => C * C' * ‖Φ u‖) (infMeasure E a) :=
      (integrable_infMeasure hΦ.1.continuous hΦ.2.1).norm.const_mul _
    refine ⟨(∫ u, C * C' * ‖Φ u‖ ∂infMeasure E a) * ‖c‖, fun g => ?_⟩
    rw [hc, norm_mul]
    refine mul_le_mul_of_nonneg_right (norm_integral_le_of_norm_le hi (.of_forall fun u => ?_)) (norm_nonneg _)
    rw [rsInf, norm_mul, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hC _) (hC' _) (norm_nonneg _) hC0) (norm_nonneg _)
  · intro γ hγ g
    have hL : ∀ x, φ.1 (γ * x) * conj (φ'.1 (γ * x)) = φ.1 x * conj (φ'.1 x) := fun x =>
      leftInv_mul_conj hω h h' γ hγ x
    have e : rsInf ℓ φ.1 φ'.1 Φ (γ * g) = rsInf ℓ φ.1 φ'.1 Φ g := funext fun u => by
      rw [rsInf, rsInf, mul_assoc γ g, hL]
    have e' : rsPsi ℓ φ.1 φ'.1 Φ J η (γ * g) = rsPsi ℓ φ.1 φ'.1 Φ J η g := funext fun y => by
      rw [rsPsi, rsPsi, e]
    rw [e']

end GlobalTheory.RSResidue

namespace GlobalTheory.RSResidue

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

end GlobalTheory.RSResidue

namespace GlobalTheory.RSResidue

end GlobalTheory.RSResidue

end
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

theorem _root_.GlobalTheory.T.cell_identity_rankinSelberg_torus_translate : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
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
  first | exact @GlobalTheory.CellPw.cell_identity | exact GlobalTheory.CellPw.cell_identity | (intros; apply GlobalTheory.CellPw.cell_identity <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

theorem _root_.GlobalTheory.T.exists_matchedWhittakerVectors_shintaniRelations : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
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
  first | (exact @GlobalTheory.JSW.MatchedVec.matched_vectors) | (exact GlobalTheory.JSW.MatchedVec.matched_vectors) | (intros; apply GlobalTheory.JSW.MatchedVec.matched_vectors  <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors

open GlobalTheory.RSTheta GlobalTheory.ThetaPoisson GlobalTheory.RSThetaLow GroundTheory.Automorphic.GJMatrix GroundTheory.Global
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.RSResidue

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem rsHat_zero {ℓ : Fin a} {Φ : (Fin a → Cinf E) → ℂ} (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E)
    (F F' : Sm E a) (hΦ : GlobalTheory.CuspQuot.IsTest (rowSet E ℓ) Φ) (g : GA E a) :
    adelicFourierPi E (rsPsi ℓ F.1 F'.1 Φ J η g) 0 =
      (∫ x, rsInf ℓ F.1 F'.1 Φ g x ∂infMeasure E a) * ((finiteMeasurePi E (latt a J)).toReal : ℂ) := by
  have h := rsHat_eq J η F F' hΦ g 0
  simp only [rsHat] at h
  rw [h]
  have h0 : (fun i => pFin E ((0 : Fin a → Ad E) i)) = 0 := funext fun _ => map_zero _
  have h1 : (fun i => pInf E ((0 : Fin a → Ad E) i)) = 0 := funext fun _ => map_zero _
  have h2 : (latt a (traceDualIdeal E J)).indicator (1 : (Fin a → Af E) → ℂ) 0 = 1 :=
    Set.indicator_of_mem (s := latt a (traceDualIdeal E J)) (show (0 : Fin a → Af E) ∈ latt a (traceDualIdeal E J) from
      fun i => (idealFiniteAdeles (traceDualIdeal E J)).zero_mem) _
  rw [h0, h1, h2]
  simp [infFourier]

theorem setIntegral_mul_right {μ : Measure (GA E a)} [μ.IsHaarMeasure] {𝓕 : Set (GA E a)}
    (h𝓕 : IsFundamentalDomain (latticeGL E a) 𝓕 μ) {f : GA E a → ℂ}
    (hf : ∀ γ ∈ latticeGL E a, ∀ g, f (γ * g) = f g) (h : GA E a) :
    ∫ g in 𝓕, f (g * h) ∂μ = ∫ g in 𝓕, f g ∂μ := by
  haveI := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  have hmp : MeasurePreserving (fun g => g * h) μ μ := measurePreserving_mul_right μ h
  have e1 := hmp.setIntegral_preimage_emb (measurableEmbedding_mulRight h) f ((fun g => g * h⁻¹) ⁻¹' 𝓕)
  have e2 : (fun g => g * h) ⁻¹' ((fun g => g * h⁻¹) ⁻¹' 𝓕) = 𝓕 := by ext; simp
  rw [e2] at e1
  rw [e1]
  have h2 : IsFundamentalDomain (latticeGL E a) ((fun g => g * h⁻¹) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv (measurePreserving_mul_right μ h⁻¹).quasiMeasurePreserving (e := id)
      Function.bijective_id (fun γ x => by simp [Subgroup.smul_def, mul_assoc])
  haveI : DiscreteTopology (latticeGL E a) := GlobalTheory.CuspRep.CuspidalL2GL.discreteTopology_latticeGL
  haveI : SecondCountableTopology (GA E a) := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E a
  have hI : GlobalTheory.AutomorphicL2Unitary.LeftInv (latticeGL E a) f := hf
  have A := (GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h2 (GlobalTheory.AutomorphicL2Unitary.descend (latticeGL E a) f)).trans
    (integral_congr_ae (Eventually.of_forall hI.descend_mk))
  have B := (GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕 (GlobalTheory.AutomorphicL2Unitary.descend (latticeGL E a) f)).trans
    (integral_congr_ae (Eventually.of_forall hI.descend_mk))
  exact A.symm.trans B

end GlobalTheory.RSResidue
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.howeDuality_compactPair_realPlaces_irreducible : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (M : Submodule ℂ ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)), (∀ ψ ∈ M, (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (ψ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (ψ w')))) → (∀ ψ ∈ M, ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∀ ψ' : ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), (∀ w z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t (ψ w)) z) (R.ptP i t (ψ' w) z) 0) → ψ' ∈ M) → M ≠ ⊥ → ∀ φ : ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (φ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (φ w'))) → φ ∈ M := by
  first | exact @GlobalTheory.HoweIrrCompact.howe_irr | exact GlobalTheory.HoweIrrCompact.howe_irr | (intros; apply GlobalTheory.HoweIrrCompact.howe_irr <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_nonzero_dominant_section_each_component : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ n : ℕ, Even n → ∃ a : (D.host.E →+* ℂ) × ℕ → ℕ, Dom a n ∧ ∀ k : (T.U j σ).Comp, ∃ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∃ x ∈ ((T.U j σ).X k).dom, rdU (T.U j σ) f k x ≠ 0 := by
  first | exact @GlobalTheory.CoverNZ.exists_sec_ne_zero_each_comp | exact GlobalTheory.CoverNZ.exists_sec_ne_zero_each_comp | (intros; apply GlobalTheory.CoverNZ.exists_sec_ne_zero_each_comp <;> assumption)
end
