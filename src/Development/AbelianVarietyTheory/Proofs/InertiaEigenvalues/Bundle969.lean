module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle965
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle872
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle076
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NotLinearIndependentStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle070
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle082
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle080
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle036
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle882
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle906
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle964
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle911
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle892
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle898
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle186
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle632
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.flatVector_eq_unit_mul_centralTranslate_liftVector : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ f, IsFlatVec R i t f → ∃ (z : GA D (Vc D i)) (c : ℂ), IsCentAt i (R.Q t) z ∧ UnitOff (GlobalTheory.TwistField.tupPrime R t) c ∧ f = c • R.ωP i t (z, 1) (R.vP i t) := by
  first | exact @GlobalTheory.FlatLift.flat_eq_unit_smul_om | exact GlobalTheory.FlatLift.flat_eq_unit_smul_om | (intros; apply GlobalTheory.FlatLift.flat_eq_unit_smul_om <;> assumption)
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

open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries



open MeasureTheory GlobalTheory.VacUnique GlobalTheory.FockCompare in
theorem eq_smul_vacuum {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {S T : HSp D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hΛS : IsSelfDualC S ΛS) (hΛT : IsSelfDualC T ΛT) {f f' : WO S T → ℂ}
    (hf : IsVacO ψ θ S T sS sT ΛS ΛT f) (hth : IsThetaFunO ψ S T f')
    (hlat' : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) f')
    (hfock : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f') : ∃ a : ℂ, f' = a • f := by
  classical
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hψ hΛS hΛT
  have hden := GlobalTheory.T.scaled_finite_matrix_mem_lattice D S T ΛS ΛT
    (GlobalTheory.ProjXCols.selfDual_isFullLattice S ΛS hΛS)
    (GlobalTheory.ProjXCols.selfDual_isFullLattice T ΛT hΛT)
  have hlat := hf.2.lat
  have hinf := fun u => latO_inf (u := u) S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    fun _ => True
  generalize latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) = Λ
    at h1 h2 h3 hden hlat hlat' hinf
  choose ε hε1 hε2 using h3 f hlat
  have det : ∀ (g g' : WO S T → ℂ) (c : ℂ), IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' →
      IsLatVac (heisO ψ S T) Λ g → IsLatVac (heisO ψ S T) Λ g' →
      (∀ z, g' (iotaW σ T S z) = c * g (iotaW σ T S z)) → g' = c • g := by
    intro g g' c hg hg' hl hl' hz
    funext w
    obtain ⟨γ, z, u, hu, rfl⟩ := exists_decomp h h2 w
    rw [Pi.smul_apply, smul_eq_mul, hg.quasi, hg'.quasi, apply_real_add h hψ (hinf u hu) (hε2 u hu g hl),
      apply_real_add h hψ (hinf u hu) (hε2 u hu g' hl'), hz]
    ring
  obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
  have n1 : nrm2 p.1 p.2 f = 1 := hn p hp
  have hne : (fun z : RW T S => f (iotaW σ T S z)) ≠ 0 := by
    intro h0
    have e := det f f 0 hf.2.theta hf.2.theta hlat hlat fun z => by rw [zero_mul]; exact congrFun h0 z
    rw [e] at n1
    simp [nrm2] at n1
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.T.realSymplecticForm_alternating_invariant_definite D S T sS sT hS hT
  have hsp : Submodule.span ℝ (Set.range (infRat S T)) = ⊤ := by
    have := span_piW_ratW_eq_top D θ σ h T S
    simpa only [piW_ratW hθ] using this
  have a1 := GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ h ψ hψ S T sS sT f hf.2.theta hf.2.fock
  have a2 := GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ h ψ hψ S T sS sT f' hth hfock
  let c : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ := fun v =>
    if hv : finRat S T (-v) ∈ Λ then ψ (-symplOH S T (ratW T S v) (finRat S T (-v))) * ε _ hv else 1
  have hc : ∀ v, ‖c v‖ = 1 := fun v => by
    simp only [c]
    split_ifs with hv
    · rw [norm_mul, hψ.1.2.1]
      rcases hε1 _ hv with e | e <;> rw [e] <;> simp
    · exact norm_one
  have law : ∀ g : WO S T → ℂ, IsThetaFunO ψ S T g → IsLatVac (heisO ψ S T) Λ g →
      ∀ v ∈ Λ.comap (finRat S T), ∀ z, g (iotaW σ T S (z + infRat S T v)) =
        c v * Complex.exp (-(Real.pi * Complex.I) * (omO S T z (infRat S T v) : ℂ)) * g (iotaW σ T S z) := by
    intro g hg hl v hv z
    have hv' : finRat S T (-v) ∈ Λ := (Λ.comap (finRat S T)).neg_mem hv
    rw [apply_add_infRat h hψ hg v (hε2 _ hv' g hl) z, ← j2]
    simp only [c, dif_pos hv']
  have hli := GlobalTheory.T.not_linearIndependent_alt (RW T S) (jO S T sS sT) (omO S T) j1 j2 j3 j4 (Matrix (Fin T.rank) (Fin S.rank) D.host.E)
    (infRat S T) (infRat_injective S T) hsp (Λ.comap (finRat S T))
    (fun x => by
      obtain ⟨N, hN, hx⟩ := hden x
      exact ⟨N, hN, by rwa [AddSubgroup.mem_comap, AddMonoidHom.map_nsmul]⟩)
    (GlobalTheory.T.rationalPoints_finitePart_selfDual_lattice_iff D S T ψ Λ hψ hinf h1 h2 hden) c hc
    ![fun z => f (iotaW σ T S z), fun z => f' (iotaW σ T S z)]
    (fun k => by fin_cases k; exacts [a1.1, a2.1]) (fun k => by fin_cases k; exacts [a1.2, a2.2])
    (fun k => by fin_cases k; exacts [law f hf.2.theta hlat, law f' hth hlat'])
  rw [LinearIndependent.pair_iff' hne] at hli
  push_neg at hli
  obtain ⟨a, ha⟩ := hli
  exact ⟨a, det f f' a hf.2.theta hth hlat hlat' fun z => (congrFun ha z).symm⟩

end GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem moved_vacuum_eq_mean : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D) (z : GA D V), IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → z ∈ GfC V → Formalism.L2.Theta.mt V z = flipElt eT m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → ∃ (lam : ℂ) (Y : Finset (WO V W)), (∀ y ∈ Y, IsHalf (cA D eT) y ∧ m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) ∧ (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → y = y') ∧ Y.card = flipIdx V W T m ∧ om (z⁻¹, 1) f₀ = lam • ∑ y ∈ Y, heisO ψ V W y f₀ := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT z hT hm hcop hmT hz hmt
  obtain ⟨Y, hY1, hY2, hY3, hYc⟩ := GlobalTheory.T.exists_levelPoint_reps_conjugate_half_mod_lattice D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT hT hm hcop hmT
  set G := ∑ y ∈ Y, heisO ψ V W y f₀ with hG
  obtain ⟨hGth, hGf⟩ := GlobalTheory.T.conjugateHalf_vacuum_translate_sum_isThetaFockVacuum D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT hT hm hcop hmT Y fun y hy => (hY1 y hy).1
  obtain ⟨hfix2, hfixh⟩ := GlobalTheory.T.vacuum_translate_sum_fixed_by_flipped_lattice D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT hT hm hcop hmT Y hY1 hY2 hY3
  have hne := GlobalTheory.T.vacuum_translate_sum_conjugateHalf_ne_zero D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT hT hm hcop hmT Y hY1 hY2 hY3
  have hW := hP.1.weil

  have hmove : ∀ u : WO V W, actO V W z 1 (flipElt eT m • u) = u := by
    intro u
    have e := GlobalTheory.AdelicLatMove.actO_actO_inv V W z 1 u
    have e2 : actO V W z⁻¹ 1⁻¹ u = flipElt eT m • u := by
      simp only [actO, inv_inv, hmt]
      have h1 : Formalism.L2.Theta.mt W (1 : GA D W)⁻¹ = 1 := by
        rw [inv_one]; unfold Formalism.L2.Theta.mt; rw [map_one]; rfl
      rw [h1, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
    rw [← e2]; exact e
  set H := om (z, 1) G with hH
  have hHth : IsThetaFunO ψ V W H := hW.om_pres _ _ hGth
  have hHh : ∀ u, heisO ψ V W u H = om (z, 1) (heisO ψ V W (flipElt eT m • u) G) := by
    intro u
    rw [hW.om_heis z 1 _ G hGth, hmove]
  have hzf : z ∈ GfC V := hz
  have hHf : ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) (sW τ)) H := by
    intro τ z'
    have c1 : compAt θ τ (Formalism.L2.Theta.mt W (1 : GA D W)) = 1 :=
      GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ W (one_mem _) τ
    have c2 : compAt θ τ (Formalism.L2.Theta.mt V z⁻¹) = 1 :=
      GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ V (inv_mem hzf) τ
    have e1 := GlobalTheory.OrientedHeis.om_dRho hW hP.1.inf z 1 τ z' hGth
    have e2 := GlobalTheory.OrientedHeis.om_dRho hW hP.1.inf z 1 τ (cplxO (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) (sW τ) z') hGth
    rw [c1, c2, Matrix.one_mul, Matrix.mul_one] at e1 e2
    have h0 := hGf τ z'
    unfold annih at h0 ⊢
    rw [hH, ← e1, ← e2, ← map_smul, ← map_add (f := _), h0, map_zero]
  have hHl : IsLatVac (heisO ψ V W) (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) H := by
    refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
    · rw [hHh, hfix2 u hu]
    · rw [hHh, hfixh e he u hu hh]
  obtain ⟨c, hc⟩ := eq_smul_vacuum hP.2.2.2.2.2.2.2.2.1 hP.1.inf (fun τ => GlobalTheory.SmoothVac.isCartanInv_one V hP.1.std τ)
    hP.2.2.2.2.2.2.2.1 hP.2.2.2.2.1 hP.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.2 hHth hHl hHf
  have hback : om (z⁻¹, 1) H = G := by
    rw [hH, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, one_mul, ← Prod.one_eq_mk, map_one,
      Module.End.one_apply]
  have hGc : G = c • om (z⁻¹, 1) f₀ := by rw [← hback, hc, map_smul]
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hne (by rw [← hG, hGc, zero_smul])
  refine ⟨c⁻¹, Y, hY1, hY2, hYc, ?_⟩
  rw [← hG, hGc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
end GlobalTheory.LevelSeries
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct

set_option autoImplicit false
noncomputable section



namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem nrm_le_one_of_mem_locBall_pts : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), ∀ f ∈ locBall YS fw iC b j, ∀ y : (Rl.FW j).Pt (placeC YS iC b), (Rl.FW j).nrm (placeC YS iC b) y ⟨(YS.fi j).e (show ↥(S.A ((j : ℕ) + 1)).WK from f).1, ((YS.fi j).wk _).1 (show ↥(S.A ((j : ℕ) + 1)).WK from f).2⟩ ≤ 1 := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC _ b j f hf y
  have h := nrm_le_one_of_mem_locBall YS fw iC b j hf y
  have he : fw.e j (cuspOf YS fw j f) = ⟨(YS.fi j).e (show ↥(S.A ((j : ℕ) + 1)).WK from f).1,
      ((YS.fi j).wk _).1 (show ↥(S.A ((j : ℕ) + 1)).WK from f).2⟩ :=
    Subtype.ext (e_cuspOf YS fw j f)
  rw [he] at h
  exact h

end GlobalTheory.GeoTie
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct

theorem _root_.GlobalTheory.T.one_tmul_mem_supLattice_of_mem_localUnitBall : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), ∀ f ∈ locBall YS fw iC b j, (show NX.Fm S i ((j : ℕ) + 1) b from (1 : NX.KB S i b) ⊗ₜ[S.Ks] f) ∈ NX.Bsup S i ((j : ℕ) + 1) b := by
  first | exact @GlobalTheory.GeoTie.one_tmul_mem_Bsup | exact GlobalTheory.GeoTie.one_tmul_mem_Bsup | (intros; apply GlobalTheory.GeoTie.one_tmul_mem_Bsup <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct

theorem _root_.GlobalTheory.T.weight_vector_realization_exists : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), (∀ f : NX.FmK S ((j : ℕ) + 1), (show ↥(S.A ((j : ℕ) + 1)).WK from f).1 ∈ (S.A ((j : ℕ) + 1)).MK → f ∈ locBall YS fw iC b j) → (∀ f : NX.FmK S ((j : ℕ) + 1), ∃ c : S.Ks, c ≠ 0 ∧ c • f ∈ locBall YS fw iC b j) := by
  first | exact @GlobalTheory.GeoTie.exists_smul_mem_locBall | exact GlobalTheory.GeoTie.exists_smul_mem_locBall | (intros; apply GlobalTheory.GeoTie.exists_smul_mem_locBall <;> assumption)
end
