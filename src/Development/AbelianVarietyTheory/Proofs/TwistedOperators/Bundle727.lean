module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle390
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle817
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle723
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle714
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle701
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle719
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsDetRoot
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle076
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle626
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle435
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle546
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle146
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle174
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle365
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2180
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1844
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle154
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle671
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle691
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle725
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVacTw

theorem circ_id (A B A' B' : Circle) : A'⁻¹ * B' = (A⁻¹ * B) * ((A' * A⁻¹)⁻¹ * (B' * B⁻¹)) := by
  apply Circle.ext
  have := Circle.coe_ne_zero A
  have := Circle.coe_ne_zero B
  have := Circle.coe_ne_zero A'
  have := Circle.coe_ne_zero B'
  simp only [Circle.coe_mul, Circle.coe_inv]
  field_simp



theorem vacTw : Big fun ch => VacTw ch := by
  obtain ⟨C, h⟩ := Big.and (Big.and GlobalTheory.T.exists_vacuumBasePointFamily_every_tuple GlobalTheory.T.vacuumBasePoint_unique_all_tuples) (Big.and GlobalTheory.T.twistCharacter_mem_twistFiniteValueProductSubgroup GlobalTheory.T.unfoldingJointData_twist_ratio_at_detRoots)
  refine ⟨C, fun ε CF hC => ?_⟩
  obtain ⟨x₀, h⟩ := h ε CF hC
  refine ⟨x₀, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi ha => ?_⟩
  obtain ⟨⟨hex, hun⟩, hxv, hcon⟩ := h D large₂ he hx Γ Pl0 T A Ks R F s ch hi ha
  have hL := s.core.lev
  classical
  let xr : ∀ k, GA D (ch.G.V (.grid D.R.m k)) → (AE D)ˣ := fun k g => (GlobalTheory.RecDict.exists_isDetRoot D _ g).choose
  have hxr : ∀ k g, IsDetRoot _ g (xr k g) := fun k g => (GlobalTheory.RecDict.exists_isDetRoot D _ g).choose_spec
  let bb : T → Pts ch.G := fun t => (hex t).choose
  have hbb : ∀ t, IsBase t ch.S.B (bb t) := fun t => (hex t).choose_spec
  let w : T → ℕ → Circle := fun t j =>
    (R.toLevCh.xi t (xr j (bb t j)))⁻¹ * R.toLevCh.xi t (xr (j + 2) (bb t (j + 2)))
  refine ⟨hex, fun t j => Circle.toUnits (w t j), fun t j => ?_, ?_⟩
  · simp only [w, map_mul, map_inv]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hxv t _)) (hxv t _)
  intro t t' M M' hM hM' b b' hb hb' P p hp j hj hjm
  have e1 : b = bb t := hun t t b (bb t) hb (hbb t)
  have e2 : b' = bb t := hun t' t b' (bb t) hb' (hbb t)
  have e3 : bb t' = bb t := hun t' t _ _ (hbb t') (hbb t)
  subst e1 e2
  have hfin : ∀ k, ∃ y : (AE D)ˣ, finPart D (y : AE D) = 1 ∧ IsDetRoot _ (p k) y := fun k =>
    GlobalTheory.TwistFinPart.exists_isDetRoot_finPart_one _ (p k) (hp.1 k) _ (hxr k (p k))
  choose y hy1 hy using hfin
  have hx : ∀ k, IsDetRoot _ ((p * bb t) k) (y k * xr k (bb t k)) := fun k =>
    GlobalTheory.ExtCore.isDetRoot_mul _ _ _ _ _ (hy k) (hxr k (bb t k))
  have hm2 := D.R.two_le_m
  have hmi : D.R.m ∉ idx D := fun h' => by
    simp only [idx, List.mem_range'_1] at h'
    omega
  have hm : (p * bb t) D.R.m = 1 := by
    rw [Pi.mul_apply, hp.2 _ hmi, (hbb t).2.2 _ (by omega) hmi, one_mul]
  rw [hcon t t' M M' hM hM' P (p * bb t) _ hx hm j hj hjm, smul_smul]
  congr 1
  obtain ⟨n, hn0, hn⟩ := hL.xi_fin t
  obtain ⟨n', hn0', hn'⟩ := hL.xi_fin t'
  have h1 : ∀ k, R.toLevCh.xi t (y k) = 1 := fun k => GlobalTheory.TupRoot.eq_one_of_finPart (hL.xi t) hn0 hn _ (hy1 k)
  have h1' : ∀ k, R.toLevCh.xi t' (y k) = 1 := fun k => GlobalTheory.TupRoot.eq_one_of_finPart (hL.xi t') hn0' hn' _ (hy1 k)
  have hw : w t' j = w t j * (((R.toLevCh.xi t' * (R.toLevCh.xi t)⁻¹) (y j * xr j (bb t j)))⁻¹ *
      (R.toLevCh.xi t' * (R.toLevCh.xi t)⁻¹) (y (j + 2) * xr (j + 2) (bb t (j + 2)))) := by
    simp only [w, e3, MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, h1, h1', inv_one, one_mul]
    exact circ_id _ _ _ _
  show ((Circle.toUnits (w t' j) : ℂˣ) : ℂ) = ((Circle.toUnits (w t j) : ℂˣ) : ℂ) * _
  rw [hw, map_mul, Units.val_mul]
  rfl

end GlobalTheory.RowVacTw

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MovedComb

open GlobalTheory.FinPl (Moves Lat)

variable {D : D7}

theorem moves_of_hat (V : HSp D) (g : GA D V) (Λ M : Lat V)
    (h : ∀ z, z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔ (Lev.finE V g).val *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) M) :
    Moves V g Λ M (fun _ => True) := by
  intro y hy
  have hy' : ∀ i, (mt V g *ᵥ y) i ∈ GlobalTheory.FinPl.idAt D (fun _ => True) := fun i => GlobalTheory.VacMove.mulVec_mem_idAt _ hy i
  constructor
  · intro hyΛ
    refine GlobalTheory.HatLatV.mem_latV_of_hatL D V M _ _ hy' ?_
    rw [GlobalTheory.Core.Mi.FrameMove.finE_mulVec_hat]
    exact (h _).1 (GlobalTheory.LatVHat.latV_mem_hatL D V Λ _ y hyΛ)
  · intro hyM
    refine GlobalTheory.HatLatV.mem_latV_of_hatL D V Λ _ y hy ?_
    refine (h _).2 ?_
    rw [← GlobalTheory.Core.Mi.FrameMove.finE_mulVec_hat]
    exact GlobalTheory.LatVHat.latV_mem_hatL D V M _ _ hyM

theorem negGA_mem_GfC (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) : negGA V g ∈ GfC (negSp V) := by
  rw [GfC, MonoidHom.mem_ker] at hg ⊢
  exact hg

theorem datum_fixed {S T : HSp D} {e a a' : AE D} (ha : e * (a + cA D a) = 0) (ha' : e * (a' + cA D a') = 0)
    {b : GA D S} {b' : GA D T} (hb : SuppAt a S b) (hb' : SuppAt a' T b') {Φ : WO S T → ℂ} (hΦ : ∀ x, Φ x ≠ 0 → IsHalf e x) :
    (fun x => Φ (actO S T b⁻¹ b'⁻¹ x)) = Φ := by
  funext x
  by_cases hx : IsHalf e x
  · rw [GlobalTheory.StdHalfLat.actO_eq_self_of_half ha ha' (GlobalTheory.StdHalfLat.suppAt_inv' hb) (GlobalTheory.StdHalfLat.suppAt_inv' hb') hx]
  · have h0 : Φ x = 0 := by
      by_contra hne
      exact hx (hΦ x hne)
    rw [h0]
    by_contra hne
    exact hx (GlobalTheory.MovedVac.halfBack D S T _ _ e x (hΦ _ hne))

private theorem actO_actO_inv_inv (S T : HSp D) (g : GA D S) (h : GA D T) (u : WO S T) :
    actO S T g h (actO S T g⁻¹ h⁻¹ u) = u := by
  have h1 : mt T h * mt T h⁻¹ = 1 := by
    rw [← GlobalTheory.VacMove.mt_mul₀, mul_inv_cancel, GlobalTheory.VacMove.mt_one₀]
  have h2 : mt S g * mt S g⁻¹ = 1 := by
    rw [← GlobalTheory.VacMove.mt_mul₀, mul_inv_cancel, GlobalTheory.VacMove.mt_one₀]
  rw [GlobalTheory.VacMove.actO_eq, GlobalTheory.VacMove.actO_eq, inv_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul,
    Matrix.mul_assoc, h2, Matrix.mul_one]

private theorem actO_two_nsmul' (S T : HSp D) (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h (2 • x) = 2 • actO S T g h x := by
  rw [two_nsmul, two_nsmul, GlobalTheory.VacMove.actO_eq, GlobalTheory.VacMove.actO_eq, Matrix.mul_add, Matrix.add_mul]

theorem isLatVac_move {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {Λ M : Lat S} {Λ' M' : Lat T} (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M)
    (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M') {b : GA D S} {b' : GA D T} (hb : Moves S b Λ M fun _ => True)
    (hb' : Moves T b' Λ' M' fun _ => True) {f₀ : WO S T → ℂ} (hf : IsThetaFunO ψ S T f₀)
    (hv : IsLatVac (heisO ψ S T) (latO S T (Λ : Set _) (Λ' : Set _) fun _ => True) f₀) :
    IsLatVac (heisO ψ S T) (latO S T (M : Set _) (M' : Set _) fun _ => True) (om (b, b') f₀) := by
  obtain ⟨hv1, hv2⟩ := hv
  have key : ∀ w c : WO S T, actO S T b b' c = w → heisO ψ S T c f₀ = f₀ →
      heisO ψ S T w (om (b, b') f₀) = om (b, b') f₀ := by
    intro w c hc hfix
    rw [← hc, ← hW.om_heis b b' c f₀ hf, hfix]
  refine ⟨fun u hu => ?_, fun e he u hu hue => ?_⟩
  · have hu0 := GlobalTheory.VacMove.actO_mem_latO hM hΛ hM' hΛ' (GlobalTheory.VacMove.moves_inv hb) (GlobalTheory.VacMove.moves_inv hb') hu
    refine key _ (2 • actO S T b⁻¹ b'⁻¹ u) ?_ (hv1 _ hu0)
    rw [actO_two_nsmul', actO_actO_inv_inv]
  · have hu0 := GlobalTheory.VacMove.actO_mem_latO hM hΛ hM' hΛ' (GlobalTheory.VacMove.moves_inv hb) (GlobalTheory.VacMove.moves_inv hb') hu
    have hc : IsHalf e (actO S T b⁻¹ b'⁻¹ u) := by
      apply GlobalTheory.MovedVac.halfBack D S T b b' e
      rw [actO_actO_inv_inv]
      exact hue
    exact key u _ (actO_actO_inv_inv S T b b' u) (hv2 e he _ hu0 hc)

theorem om_eq_of_isThetaAt {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {Λ M : Lat S} {Λ' M' : Lat T} (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M)
    (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M') {b : GA D S} {b' : GA D T} (hbf : b ∈ GfC S) (hbf' : b' ∈ GfC T)
    (hb : Moves S b Λ M fun _ => True) (hb' : Moves T b' Λ' M' fun _ => True) {e a a' : AE D} {P : Finset (Pl D.host.E)}
    (he : IsIdemSum e P) (ha : e * (a + cA D a) = 0) (ha' : e * (a' + cA D a') = 0) (hs : SuppAt a S b) (hs' : SuppAt a' T b')
    {Φ f₀ f g : WO S T → ℂ} (hΦ : IsSBHalf e (latO S T (M : Set _) (M' : Set _) fun _ => True) Φ) (hf₀ : IsThetaFunO ψ S T f₀)
    (hf : IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (Λ : Set _) (Λ' : Set _) fun _ => True) 1 f₀ Φ f)
    (hg : IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 (om (b, b') f₀) Φ g) :
    om (b, b') f = g := by
  have hstd : IsStdChar D ψ (-1) := hW.std
  obtain ⟨θ, hθ⟩ := hstd.2.1
  have hfT : IsThetaFunO ψ S T f := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hstd hθ hf hf₀
  have hth := GlobalTheory.VacMove.isThetaAt_moveLat D ψ S T χS χT om hW Λ M Λ' M' hΛ hM hΛ' hM' b hbf b' hbf' hb hb' e Φ f₀ f
    (GlobalTheory.PlaceDatum.idemSum_mul_self he) (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.infPart_of_idemSum he) hf₀ hfT hf
  rw [datum_fixed ha ha' hs hs' hΦ.1] at hth
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hth
  rw [hall Tm hTm, hg.2 Tm hTm]

private theorem isThetaFunO_and_isLatVac_of_isVacO {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Set (Fin S.rank → D.host.E)} {ΛT : Set (Fin T.rank → D.host.E)} {f : WO S T → ℂ}
    (h : IsVacO ψ θ S T sS sT ΛS ΛT f) :
    IsThetaFunO ψ S T f ∧ IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f := by
  exact ⟨h.2.theta, h.2.lat⟩

private theorem moves_negSp_negGA_of_moves {V : HSp D} {g : GA D V} {Λ M : Lat V} (h : Moves V g Λ M fun _ => True) :
    Moves (negSp V) (negGA V g) Λ M fun _ => True := by
  intro y hy
  rw [GlobalTheory.ChiGrid.mt_negGA]
  exact h y hy

private theorem suppAt_negSp_negGA_of_suppAt {V : HSp D} {a : AE D} {g : GA D V} (h : SuppAt a V g) :
    SuppAt a (negSp V) (negGA V g) := by
  intro i j
  rw [GlobalTheory.ChiGrid.mt_negGA]
  exact h i j

private theorem moved_core_lemma_3 {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {Λ M : Lat S} {Λ' M' : Lat T} (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M)
    (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M') {b : GA D S} {b' : GA D T} (hbf : b ∈ GfC S) (hbf' : b' ∈ GfC T)
    (hb : Moves S b Λ M fun _ => True) (hb' : Moves T b' Λ' M' fun _ => True) {e : AE D} {P : Finset (Pl D.host.E)}
    (he : IsIdemSum e P) (hk : ∃ a, e * (a + cA D a) = 0 ∧ SuppAt a S b)
    (hk' : ∃ a', e * (a' + cA D a') = 0 ∧ SuppAt a' T b') {Φ f₀ f : WO S T → ℂ}
    (hΦ : IsSBHalf e (latO S T (M : Set _) (M' : Set _) fun _ => True) Φ) (hf₀ : IsThetaFunO ψ S T f₀)
    (hv : IsLatVac (heisO ψ S T) (latO S T (Λ : Set _) (Λ' : Set _) fun _ => True) f₀)
    (hf : IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (Λ : Set _) (Λ' : Set _) fun _ => True) 1 f₀ Φ f)
    (c : WO S T →₀ ℂ)
    (hc : ∀ g₀, IsThetaFunO ψ S T g₀ → IsLatVac (heisO ψ S T) (latO S T (M : Set _) (M' : Set _) fun _ => True) g₀ →
      IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 g₀ Φ (comb ψ S T c g₀)) :
    om (b, b') f = comb ψ S T c (om (b, b') f₀) := by
  obtain ⟨a, ha, hs⟩ := hk
  obtain ⟨a', ha', hs'⟩ := hk'
  exact om_eq_of_isThetaAt hW hΛ hM hΛ' hM' hbf hbf' hb hb' he ha ha' hs hs' hΦ hf₀ hf
    (hc _ (hW.om_pres _ _ hf₀) (isLatVac_move hW hΛ hM hΛ' hM' hb hb' hf₀ hv))

theorem movedVec_eq_comb : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∀ (t : T) (p : Pair T), DefPair D.R.m p → ∀ (d : FinDatum ch.G t p) (c : WO (ch.G.pS p) (ch.G.pT p) →₀ ℂ), d.z = 1 → ch.S.Z.HasVec d → IsCombOf ch.W d c → movedVec t ch.S.toGridChoice d = comb ch.W.ψ _ _ c (ch.W.om p (ch.G.toPair p (ch.S.N.u p.small).1 (ch.S.N.u p.big).1) (ch.S.Z.vac p)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R large₂ F hset ch _ t p hp d c hz hvec hcomb
  have hL := hset.core.lev
  have hnodes := GlobalTheory.FunObj.DefPair.nodes hp
  obtain ⟨f, hf⟩ := hvec
  have hvd : ch.S.Z.vec d = f := by
    unfold GlobalTheory.FunObj.Normal.vec
    rw [GlobalTheory.FunObj.FinDatum.vec_eq ch.W hf, hz, ← Prod.one_eq_mk, map_one]
    rfl
  unfold movedVec
  rw [hvd]
  cases p with
  | chi i j =>
    have hX := hnodes.1
    have hY := hnodes.2
    obtain ⟨hf₀, hv⟩ := isThetaFunO_and_isLatVac_of_isVacO (ch.S.Z.vac_is (.chi i j) hp)
    exact moved_core_lemma_3 (ch.W.om_is (.chi i j) (by simp only [DefPair, Pair.InRange, Node.InRange] at hp ⊢; omega))
      (GlobalTheory.ChiGrid.isSelfDualC_neg (GlobalTheory.FunObj.Std.selfDual ch.S.N hY))
      (GlobalTheory.ChiGrid.isSelfDualC_neg (GlobalTheory.FunObj.DefNode.selfDual ch.G hL hY))
      (GlobalTheory.FunObj.Std.selfDual ch.S.N hX) (GlobalTheory.FunObj.DefNode.selfDual ch.G hL hX)
      (negGA_mem_GfC _ (ch.S.N.u _).2) (ch.S.N.u _).2
      (moves_negSp_negGA_of_moves (moves_of_hat _ _ _ _ (ch.S.N.u_lat _ hY))) (moves_of_hat _ _ _ _ (ch.S.N.u_lat _ hX))
      d.e_is
      (by
        obtain ⟨a, ha, hs⟩ := GlobalTheory.StdHalfLat.exists_kill ch.S.N (Set.mem_univ t) d hY
        exact ⟨a, ha, suppAt_negSp_negGA_of_suppAt hs⟩)
      (GlobalTheory.StdHalfLat.exists_kill ch.S.N (Set.mem_univ t) d hX)
      d.sb hf₀ hv hf c hcomb.2.2
  | mu t' i j => exact False.elim hp
  | core i => exact False.elim hp
  | top t' j =>
    have hX := hnodes.1
    have hY := hnodes.2
    obtain ⟨hf₀, hv⟩ := isThetaFunO_and_isLatVac_of_isVacO (ch.S.Z.vac_is (.top t' j) hp)
    exact moved_core_lemma_3 (ch.W.om_is (.top t' j) (by simp only [DefPair, Pair.InRange, Node.InRange] at hp ⊢; omega))
      (GlobalTheory.FunObj.Std.selfDual ch.S.N hX) (GlobalTheory.FunObj.DefNode.selfDual ch.G hL hX)
      (GlobalTheory.FunObj.Std.selfDual ch.S.N hY) (GlobalTheory.FunObj.DefNode.selfDual ch.G hL hY)
      (ch.S.N.u _).2 (ch.S.N.u _).2
      (moves_of_hat _ _ _ _ (ch.S.N.u_lat _ hX)) (moves_of_hat _ _ _ _ (ch.S.N.u_lat _ hY))
      d.e_is (GlobalTheory.StdHalfLat.exists_kill ch.S.N (Set.mem_univ t) d hX)
      (GlobalTheory.StdHalfLat.exists_kill ch.S.N (Set.mem_univ t) d hY)
      d.sb hf₀ hv hf c hcomb.2.2

end GlobalTheory.MovedComb

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv GlobalTheory.LastVertexMove
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.LastRowLat

open GlobalTheory.FinPl (Moves Lat)
open Matrix

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}


variable (G) in
theorem givenLevel_inner (t : T) (w : Pl D.host.E) : ∀ X : ℕ × ℕ, 1 ≤ X.1 → 1 ≤ X.2 →
    givenLevel G t w X = GlobalTheory.SplitWeil.KO (Kw w) _
  | (_ + 1, _ + 1), _, _ => rfl
  | (0, _), h, _ => absurd h (by omega)
  | (_ + 1, 0), _, h => absurd h (by omega)

theorem inBasis_KO {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E)
    (K : Subgroup (GL (Fin n') (Kw w))) (hK : K = GlobalTheory.SplitWeil.KO (Kw w) (Fin n')) (hx : inBasis h β w x ∈ K) :
    inBasis rfl β w x ∈ GlobalTheory.SplitWeil.KO (Kw w) (Fin n) := by
  subst h; subst hK; exact hx

theorem isFrame_grid (S : GridChoice W U) : ∀ {i : ℕ}, 1 ≤ i → i ≤ D.R.m → IsFrame (S.B.β i D.R.m) (G.Λ (.grid i D.R.m))
  | 0, h, _ => absurd h (by omega)
  | i + 1, _, hi => S.B.isFrame (i + 1) D.R.m (by omega) hi le_rfl

theorem isSelfDual_grid : ∀ {i : ℕ}, 1 ≤ i → i ≤ D.R.m → IsSelfDualC (G.V (.grid i D.R.m)) (G.Λ (.grid i D.R.m))
  | 0, h, _ => absurd h (by omega)
  | i + 1, _, hi => (G.sp.V_is (i + 1) D.R.m (by omega) hi le_rfl).sd

theorem levRow_mem_St (S : GridChoice W U) (t : T) (k : FinPt G (.grid D.R.m D.R.m))
    (hk : finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl) :
    finG (G.V (.grid D.R.m D.R.m)) k ∈ St (S.B.β D.R.m D.R.m) := by
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hfr := isFrame_grid S hm le_rfl
  have hsd := isSelfDual_grid (G := G) hm le_rfl
  have hU : finG (G.V (.grid D.R.m D.R.m)) k ∈ UA D.sp.cm (G.V (.grid D.R.m D.R.m)).gram := GlobalTheory.LevSplit.finE_mem_UA _ _
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hk
  have hP : ∀ w0 ∈ locPl G t, inBasis rfl (S.B.β D.R.m D.R.m) w0 (finG (G.V (.grid D.R.m D.R.m)) k) ∈ GlobalTheory.SplitWeil.KO (Kw w0) _ := fun w0 hw0 =>
    inBasis_KO _ _ _ _ _ (givenLevel_inner G t w0 (D.R.m, D.R.m) hm hm) (Subgroup.mem_iInf.1 h1 ⟨w0, hw0⟩)
  refine GlobalTheory.Adopt.mem_latticeStabilizer_of_local_integral_inBasis _ _ fun w => ?_
  by_cases hw : ∃ w0 ∈ locPl G t, w.under (𝓞 D.host.F) = w0.under (𝓞 D.host.F)
  · obtain ⟨w0, hw0, e⟩ := hw
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e with rfl | rfl
    · exact hP w hw0
    · exact GlobalTheory.T.unitaryInBasis_integral_at_conjugatePlace _ _ _ hfr (GlobalTheory.AdIsom.dualL_eq hsd) _ hU w0 (hP w0 hw0)
  · push_neg at hw
    exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h2 w) hw

theorem hat_stab_of_St {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (β M : GL (Fin n) (Lev.EAf D))
    (hβ : IsFrame β Λ) (hM : M ∈ St β) (z : Fin n → Lev.EAf D) :
    z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔ M.val *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  refine ⟨GlobalTheory.LatStab.mulVec_mem_of_mem_St Λ β M hβ hM z, fun h => ?_⟩
  have e : (M⁻¹).val *ᵥ (M.val *ᵥ z) = z := by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  rw [← e]
  exact GlobalTheory.LatStab.mulVec_mem_of_mem_St Λ β M⁻¹ hβ (inv_mem hM) _ h

theorem hat_stab_conj (V : HSp D) (u k : GA D V) (Λ M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hu : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) M ↔ (Lev.finE V u).val *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (hk : ∀ z, z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔ (Lev.finE V k).val *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (v : Fin V.rank → Lev.EAf D) :
    v ∈ Formalism.L2.Herm.hatL (F := D.host.F) M ↔
      (Lev.finE V (u⁻¹ * k * u)).val *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) M := by
  have e : (Lev.finE V u).val *ᵥ ((Lev.finE V (u⁻¹ * k * u)).val *ᵥ v) =
      (Lev.finE V k).val *ᵥ ((Lev.finE V u).val *ᵥ v) := by
    rw [map_mul, map_mul, map_inv, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  refine (hu v).trans ((hk _).trans ?_)
  rw [← e]
  exact (hu _).symm

theorem moves_of_hat (V : HSp D) (g : GA D V) (Λ : Lat V)
    (h : ∀ z, z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔ (Lev.finE V g).val *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    Moves V g Λ Λ (fun _ => True) := by
  intro y hy
  have hy' : ∀ i, (Formalism.L2.Theta.mt V g *ᵥ y) i ∈ GlobalTheory.FinPl.idAt D (fun _ => True) :=
    GlobalTheory.Core.Mi.FrameMove.mulVec_mem_ideal _ hy
  constructor
  · intro h1
    refine GlobalTheory.HatLatV.mem_latV_of_hatL D V Λ _ _ hy' ?_
    rw [GlobalTheory.Core.Mi.FrameMove.finE_mulVec_hat]
    exact (h _).1 (GlobalTheory.LatVHat.latV_mem_hatL D V Λ _ y h1)
  · intro h1
    refine GlobalTheory.HatLatV.mem_latV_of_hatL D V Λ _ _ hy ?_
    have h2 := GlobalTheory.LatVHat.latV_mem_hatL D V Λ _ _ h1
    rw [GlobalTheory.Core.Mi.FrameMove.finE_mulVec_hat] at h2
    exact (h _).2 h2

theorem moves_neg (V : HSp D) (g : GA D V) (Λ : Lat V) {P : GlobalTheory.FinPl.Pl D → Prop} (h : Moves V g Λ Λ P) :
    Moves (negSp V) (negGA V g) Λ Λ P := h

theorem moves_cast (S : GridChoice W U) : ∀ (i : ℕ) (e : D.R.m = i) (g : FinPt G (.grid D.R.m D.R.m)),
    Moves (G.V (.grid D.R.m D.R.m)) g.1 (colLat (S.N.fr (.grid D.R.m D.R.m))) (colLat (S.N.fr (.grid D.R.m D.R.m)))
      (fun _ => True) →
    Moves (G.V (.grid i D.R.m)) (e ▸ g : FinPt G (.grid i D.R.m)).1 (colLat (S.N.fr (.grid i D.R.m)))
      (colLat (S.N.fr (.grid i D.R.m))) (fun _ => True) := by
  rintro i rfl g h
  exact h

end GlobalTheory.LastRowLat

namespace GlobalTheory.LastRowLat

open GlobalTheory.FinPl (Moves Lat)
open Matrix

theorem rowPt_mem_stdLat : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}, t ∈ U → ∀ k : FinPt G (.grid D.R.m D.R.m),
    finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl →
    ∀ x : WO (G.pS (.chi (lastIx D) D.R.m : Pair T)) (G.pT (.chi (lastIx D) D.R.m : Pair T)),
    actO _ _ (rowPt S k).1⁻¹ (rowPt S k).2⁻¹ x ∈ stdLat S (.chi (lastIx D) D.R.m) ↔ x ∈ stdLat S (.chi (lastIx D) D.R.m) := by
  intro D T L sc G W U S t _ k hk x
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hX : DefNode D.R.m (.grid D.R.m D.R.m) := ⟨le_rfl, rfl⟩
  have hk' := hat_stab_of_St _ _ _ (isFrame_grid S hm le_rfl) (levRow_mem_St S t k hk)
  have hg := hat_stab_conj (G.V (.grid D.R.m D.R.m)) (S.N.u (.grid D.R.m D.R.m)).1 k.1 _ _
    (S.N.u_lat _ hX) hk'
  have mv : Moves (G.V (.grid D.R.m D.R.m)) ((S.N.u (.grid D.R.m D.R.m))⁻¹ * k * S.N.u (.grid D.R.m D.R.m)).1
      (colLat (S.N.fr (.grid D.R.m D.R.m))) (colLat (S.N.fr (.grid D.R.m D.R.m))) (fun _ => True) :=
    moves_of_hat _ _ _ hg
  have mv2 := moves_cast S _ (lastIx_succ D) _ mv
  have mvS : Moves (G.pS (.chi (lastIx D) D.R.m : Pair T)) (rowPt S k).1⁻¹ (S.N.latS (.chi (lastIx D) D.R.m))
      (S.N.latS (.chi (lastIx D) D.R.m)) (fun _ => True) :=
    GlobalTheory.VacMove.moves_inv (moves_neg _ _ _ mv2)
  have mvT : Moves (G.pT (.chi (lastIx D) D.R.m : Pair T)) (rowPt S k).2⁻¹ (S.N.latT (.chi (lastIx D) D.R.m))
      (S.N.latT (.chi (lastIx D) D.R.m)) (fun _ => True) := by
    have e2 : (rowPt S k).2 = 1 := rfl
    rw [e2, inv_one]
    intro y _
    rw [GlobalTheory.VacMove.mt_one₀, Matrix.one_mulVec]
  have hl := (lastIx D).2
  have sdS : IsSelfDualC (G.pS (.chi (lastIx D) D.R.m : Pair T)) (S.N.latS (.chi (lastIx D) D.R.m)) :=
    isSelfDualC_neg (OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on _ ⟨by omega, rfl⟩))
  have sdT : IsSelfDualC (G.pT (.chi (lastIx D) D.R.m : Pair T)) (S.N.latT (.chi (lastIx D) D.R.m)) :=
    OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on _ ⟨by omega, rfl⟩)
  exact (GlobalTheory.VacMove.mem_latO_iff_actO sdS sdS sdT sdT mvS mvT x).symm

end GlobalTheory.LastRowLat
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.localPureTensor_product_expansion_all_places : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (s : ℤˣ) (t : T) (β : CosFam ch.G t) (ζ : locPl ch.G t → ℂ), (∀ w : locPl ch.G t, GlobalTheory.LocAsm.PlaceCl ch s t w (β w) (ζ w)) → ∀ (M : Vol ch.G) (hM : M.Is t) (b b₀ : Pts ch.G), IsRep t ch.S.B s β b → IsBase t ch.S.B b₀ → ∀ e : AE D, IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)), (∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ w b)) → ∀ (fd : SchDown ch.G t) (fr : SchRow ch.G), (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fd j)) → (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fr i)) → ∃ σ : (PureDat ch.G t × Combs ch.G) →₀ ℂ, (∀ k ∈ σ.support, (∀ j : Fin D.R.m, (k.1.1 j).e = e ∧ IsCombOf ch.W (k.1.1 j) (k.2.1 j)) ∧ ∀ n, (k.1.2 n).e = e ∧ IsCombOf ch.W (k.1.2 n) (k.2.2 n)) ∧ (∀ (u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))) (y : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))), (∀ j, IsHalf e (u j)) → (∀ i, IsHalf e (y i)) → (σ.sum fun k x => x * ((∏ j, (k.1.1 j).fn (u j)) * ∏ n, (k.1.2 n).fn (y n))) = ∏ w : locPl ch.G t, flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (φ w))) (ch.S.colAt t w.1 u) (ch.S.rowAt t w.1 y)) ∧ ∀ (P : PolDown ch.G) (p : Pts ch.G), IsRealPt p → ∀ (u : ColPt ch.G) (y : RowPt ch.G), evT (conAt ch.W hM (fockD ch.W t fd P) (p * b)) fr u y = (∏ w, ζ w) * σ.sum fun k x => x * evT (combC ch.W k.2 (conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b₀))) (combR ch.rm k.2) u y := by
  first | exact @GlobalTheory.LocAsm.oneProduct | exact GlobalTheory.LocAsm.oneProduct | (intros; apply GlobalTheory.LocAsm.oneProduct <;> assumption)
end
