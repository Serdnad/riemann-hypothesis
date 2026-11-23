module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfOrbitAlg
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermCarrierStability.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictK
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermCarrierStability.TermStableHolds
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AdmNPf

@[expose] public section

section

noncomputable section

open scoped Classical ComplexConjugate ENNReal NNReal
open MeasureTheory

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp
open Formalism.L2.SG.HidaSetting Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full

section TermCarSec

def RatIsoC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (γ : X.B.I.GA), γ ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I →
    ∃ σ : (VS D).V ≃ₗ[D.host.E] (VS D).V, RatLink X γ σ ∧ σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT

def ModGOfAtC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (g1 : X.B.I.Gf) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    (∀ y, y ∈ Λ ↔ X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf) →
    ∀ v, InAt X.B.I X.B.g X.B.g (X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd v)) → ModG (VS D) Λ (gS D) v

def FrameCongC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (ρ : (Y.cs u).Cl) (ρ' : (Y.cs u').Cl) (γ : X.B.I.GA) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    RatLink X γ σ → kOf X u u' ((Y.cs u).h ρ : X.B.I.Gf) ((Y.cs u').h ρ' : X.B.I.Gf) γ ∈ X.K2 →
    ∃ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E),
      (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧
      ∀ b, InAt X.B.I X.B.g X.B.g (X.B.I.fmat (aC (Y.cs u) ρ)⁻¹ *ᵥ
        incl X.B.I (X.crd (σ (frame (lf D (X.Fu u')) b) - frameAct (frame (lf D (X.Fu u))) ξ b)))

section Tr2

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
  {γ : S.V ≃ₗ[E] S.V} {T' : E} {x F₂ : LFlag S r T'}

theorem transport_x_lattice (Λ₂ Λ : Submodule (𝓞 E) S.V) (hΛ : PI.TCS.Tr γ Λ₂ Λ) (he : ∀ k, F₂.fl.e k = γ (x.fl.e k)) :
    PI.TCS.Tr γ (XLam Λ₂ F₂) (XLam Λ x) :=
  PI.TCS.Tr.inf hΛ (PI.TCS.trE_Xsp he).toO

theorem transport_lattice_sub (Λ₂ Λ : Submodule (𝓞 E) S.V) (hΛ : PI.TCS.Tr γ Λ₂ Λ) (he : ∀ k, F₂.fl.e k = γ (x.fl.e k))
    (hiso : ∀ a b, S.hT (γ a) (γ b) = S.hT a b) : PI.TCS.Tr γ (Lsub Λ₂ F₂) (Lsub Λ x) :=
  PI.TCS.Tr.inf (PI.TCS.Tr.sup (PI.TCS.Tr.inf hΛ ((PI.TCS.trE_Xsp he).perp hiso).toO) (PI.TCS.trE_Xsp he).toO)
    ((PI.TCS.trE_Xsp he).perp hiso).toO

theorem fixed_conv_transport (Λ₂ Λ : Submodule (𝓞 E) S.V) (g : ℕ) (hΛ : PI.TCS.Tr γ Λ₂ Λ)
    (he : ∀ k, F₂.fl.e k = γ (x.fl.e k)) (hz : F₂.fl.z = γ x.fl.z) (hiso : ∀ a b, S.hT (γ a) (γ b) = S.hT a b)
    (hx : IsFixedConv Λ g x) : IsFixedConv Λ₂ g F₂ := by
  refine ⟨fun P => ?_, fun c hc => ?_⟩
  · obtain ⟨c, hc0, hc1, heq⟩ := hx.1 P
    refine ⟨c, hc0, hc1, ?_⟩
    have := P.isPrime
    refine PI.TCS.Tr.eq (transport_x_lattice Λ₂ Λ hΛ he).localization₂ (PI.TCS.Tr.span ?_).localization₂ heq
    rw [← Set.range_comp]
    congr 1
    funext a
    simp [he a, map_smul]
  · apply hx.2 c
    have := ((transport_lattice_sub Λ₂ Λ hΛ he hiso) _).mp hc
    simpa [hz, map_smul] using this

end Tr2

section Main

variable {D : D7}

theorem frame_ok_transport {T' : D.host.E} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {x F₂ : LFlag (D.sp.Y 0) D.R.rS T'} (Λ₂ Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : PI.TCS.Tr γ Λ₂ Λ)
    (he : ∀ k, F₂.fl.e k = γ (x.fl.e k)) (hz : F₂.fl.z = γ x.fl.z)
    (hiso : ∀ a b, (VS D).hT (γ a) (γ b) = (VS D).hT a b) (hx : FrameOK D Λ x) : FrameOK D Λ₂ F₂ :=
  ⟨fixed_conv_transport Λ₂ Λ (gS D) hΛ he hz hiso hx.1, PI.TCS.Tr.eq (transport_x_lattice Λ₂ Λ hΛ he) (PI.TCS.tr_XS D he) hx.2⟩

theorem pd_of_tr {T : D.host.E} (u' : D.what₂.Word) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V)
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hiso : σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hTr : PI.TCS.Tr σ Λ Λ')
    (hL : IsLift Λ' F') (hOK : FrameOK D Λ' F')
    (hA : ∃ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E),
      (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧
      ∀ b, ModG (VS D) Λ (gS D) (σ (frame F' b) - frameAct (frame F) ξ b)) :
    TermDef.PD D Λ F u' (mapLF σ F') := by
  have hmap : mapLF σ F' = ⟨mapFlag σ hiso F'.fl, σ F'.zt⟩ := by
    unfold mapLF; rw [dite_eq_left hiso]
  have hisoT : ∀ a b, (VS D).hT (σ a) (σ b) = (VS D).hT a b := fun a b => hiso a b
  have hfr : ∀ b, frame (mapLF σ F') b = σ (frame F' b) := Formalism.L2.SG.NormCut.frame_mapLF hiso F'
  change IsLift Λ (mapLF σ F') ∧ IsAdmissible Λ (gS D) F (mapLF σ F') ∧ FrameOK D Λ (mapLF σ F')
  refine ⟨?_, ?_, ?_⟩
  · rw [hmap]
    refine ⟨(hTr _).mpr ?_, ?_⟩
    · show σ.symm (σ F'.fl.z) ∈ Λ'
      simpa using hL.1
    · show σ F'.zt = σ F'.fl.z
      rw [hL.2]
  · obtain ⟨ξ, hl, hd, hc⟩ := hA
    refine ⟨ξ, hl, hd, fun b => ?_⟩
    rw [hfr b]
    exact hc b
  · rw [hmap]
    exact frame_ok_transport Λ Λ' hTr (fun j => rfl) rfl hisoT hOK

theorem termCarC_of (h1 : RatIsoC) (h2 : ModGOfAtC) (h3 : FrameCongC) : TermCarC := by
  intro D X Y u u' hH ρ ρ' γ hγ
  obtain ⟨hγr, hk⟩ := hγ
  obtain ⟨σ, hRL, hiso⟩ := h1 D X γ hγr
  have hK := Y.hK
  set k := kOf X u u' ((Y.cs u).h ρ : X.B.I.Gf) ((Y.cs u').h ρ' : X.B.I.Gf) γ with hkdef
  have hkK : k ∈ X.B.I.Kset := hk.1
  have hkK' : k⁻¹ ∈ X.B.I.Kset := (hK.2.2.1 k hk).1

  have hTr : PI.TCS.Tr σ ((Y.cs u).lamOf ρ) ((Y.cs u').lamOf ρ') := by
    intro v
    rw [(Y.cs u).lat_eq ρ v, (Y.cs u').lat_eq ρ' (σ.symm v), ← LatDictK.ratLink_incl_inv X hRL v,
      mulVec_mulVec, ← LatDictK.fmatK_mul]
    have e : (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')⁻¹ * γ.2⁻¹ =
        k⁻¹ * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ := by
      rw [hkdef]; unfold kOf; group
    rw [e, LatDictK.fmatK_mul, ← mulVec_mulVec]
    constructor
    · intro hw
      exact unitaryCongruence.K_mv X.B.I hkK' hw
    · intro hw
      have := unitaryCongruence.K_mv X.B.I hkK hw
      rwa [mulVec_mulVec, ← LatDictK.fmatK_mul, mul_inv_cancel, show X.B.I.fmat 1 = 1 by
        simp [AutInst.fmat], one_mulVec] at this
  have hgm : Formalism.HermitianLatticesTheory.gmap σ ((Y.cs u').lamOf ρ') = (Y.cs u).lamOf ρ := by
    ext v
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hTr _).mpr (by simpa using hy)
    · intro hv
      exact ⟨σ.symm v, (hTr v).mp hv, by simp⟩

  obtain ⟨-, ⟨-, -, hLift, hFC⟩, hXL⟩ := (Y.rowsOK u').1 _ ((Y.cs u').lam_mem ρ')
  refine ⟨⟨(γ, σ), hRL, hiso, hgm, ?_⟩, rfl⟩
  refine pd_of_tr u' _ _ (lf D (X.Fu u)) (lf D (X.Fu u')) σ hiso hTr hLift ⟨hFC, hXL⟩ ?_
  obtain ⟨ξ, hl, hd, hc⟩ := h3 D X Y u u' ρ ρ' γ σ hRL hk
  exact ⟨ξ, hl, hd, fun b => h2 D X (aC (Y.cs u) ρ) _ ((Y.cs u).lat_eq ρ) _ (hc b)⟩

end Main

end TermCarSec

end Formalism.L2.SG.Pf.RegroupPf
end
end

section

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut

namespace Formalism.L2.SG.Pf.VanishNConj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

theorem chiN_mul {x y : X.B.I.Gf} (hx : x ∈ X.K2) (hy : y ∈ X.K2) :
    chiN X (x * y) = chiN X x * chiN X y := by
  obtain ⟨hfe, hfz, -, -⟩ := reference_frame_congruences X
  have hf0 : ∀ a, X.f0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).2
  have hg := modulus_g_ne_zero X
  unfold chiN
  refine unitaryCongruence.psi_mul_of_Z X.B.I X.B.g X.psiEf_add X.psiEf_int hg ?_
  have h : (∑ a, hA X.B.I (X.f0 a) (X.B.I.fmat (x * y) *ᵥ nxt X.e0 X.z0 a)) -
      (∑ a, hA X.B.I (X.f0 a) (X.B.I.fmat x *ᵥ nxt X.e0 X.z0 a)) -
      (∑ a, hA X.B.I (X.f0 a) (X.B.I.fmat y *ᵥ nxt X.e0 X.z0 a)) =
      ∑ a, (hA X.B.I (X.f0 a) (X.B.I.fmat (x * y) *ᵥ nxt X.e0 X.z0 a) -
        hA X.B.I (X.f0 a) (X.B.I.fmat x *ᵥ nxt X.e0 X.z0 a) -
        hA X.B.I (X.f0 a) (X.B.I.fmat y *ᵥ nxt X.e0 X.z0 a)) := by
    simp only [Finset.sum_sub_distrib]
  rw [h]
  exact unitaryCongruence.Z_sum X.B.I X.B.g _ _ fun a _ =>
    unitaryCongruence.term_Z X.B.I X.B.g _ _ (unitaryCongruence.nxt_Z X.B.I X.B.g X.e0 X.f0 X.z0 hfe hfz a)
      (unitaryCongruence.Me_Q X.B.I X.B.g X.e0 X.f0 hf0 hfe a
        (unitaryCongruence.e_step X.B.I X.B.g X.e0 X.z0 X.bw hx.1 hx.2 a _
          (unitaryCongruence.nxt_cong X.B.I X.B.g X.e0 X.z0 X.bw hy.2 a)))

theorem chiL_conj {u : D.what₂.Word} {n : X.B.I.Gf} (hn : n ∈ X.NfinU u) (hnK : n ∈ X.B.I.Kset) :
    chiL X ((X.xu u)⁻¹ * n * X.xu u) = 1 := by
  unfold chiL
  exact unitaryCongruence.psi_Z X.B.I X.B.g X.psiEf_add X.psiEf_int (modulus_g_ne_zero X)
    (unitaryCongruence.Z_sum X.B.I X.B.g _ _ fun i _ => Z_bw hn hnK i)

theorem chiN_conj {u : D.what₂.Word} {n : X.B.I.Gf} (hn : n ∈ X.NfinU u) (hnK : n ∈ X.B.I.Kset) :
    chiN X ((X.xu u)⁻¹ * n * X.xu u) = X.chi2 ((X.xu u)⁻¹ * n * X.xu u) := by
  rw [level_char_eq_mul, chiL_conj X hn hnK, mul_one]

theorem kappa_Kset {Λ : Submodule (𝓞 D.host.E) (VS D).V} (a : X.B.I.Gf)
    (hlat : ∀ y : (VS D).V, y ∈ Λ ↔ X.B.I.fmat a⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf)
    {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hmap : Formalism.HermitianLatticesTheory.gmap n Λ = Λ) {x : X.B.I.GA}
    (hx : RatLink X x n) : a⁻¹ * x.2 * a ∈ X.B.I.Kset := by
  have key : a⁻¹ * (x.2 * a) ∈ X.B.I.Kset := by
    refine LatDictK.dict_K X _ _ {y | y ∈ Λ} (fun y => hlat y) (fun y => ?_)
    show y ∈ Λ ↔ _
    have e1 : y ∈ Λ ↔ n.symm y ∈ Λ := by
      conv_lhs => rw [← hmap]
      constructor
      · rintro ⟨z, hz, hzy⟩
        have : n.symm y = z := by rw [← hzy]; simp
        rw [this]; exact hz
      · intro h
        exact ⟨n.symm y, h, by simp⟩
    rw [e1, hlat, show (x.2 * a)⁻¹ = a⁻¹ * x.2⁻¹ from _root_.mul_inv_rev _ _,
      LatDictK.fmatK_mul, ← mulVec_mulVec, LatDictK.ratLink_incl_inv X hx]
  rwa [mul_assoc]

theorem core (u : D.what₂.Word) (hNK : UnipotentConjugateInLevel X u) (h : Hfin X u) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hlat : ∀ y : (VS D).V, y ∈ Λ ↔
      X.B.I.fmat ((h : X.B.I.Gf) * X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf)
    {x : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NLam Λ (lf D (X.Fu u)))
    (hx : RatLink X x n) :
    ((h : X.B.I.Gf) * X.xu u)⁻¹ * x.2 * ((h : X.B.I.Gf) * X.xu u) ∈ X.K2 ∧
    X.chi2 (((h : X.B.I.Gf) * X.xu u)⁻¹ * x.2 * ((h : X.B.I.Gf) * X.xu u)) = X.psiFinU u x.2 ∧
    ∀ k ∈ X.K2,
      chiN X (((h : X.B.I.Gf) * X.xu u)⁻¹ * x.2 * ((h : X.B.I.Gf) * X.xu u) * k) =
          X.psiFinU u x.2 * chiN X k ∧
      chiN X (k * (((h : X.B.I.Gf) * X.xu u)⁻¹ * x.2 * ((h : X.B.I.Gf) * X.xu u))) =
          chiN X k * X.psiFinU u x.2 := by
  have hxN : x.2 ∈ X.NfinU u := nLamNfin_holds D X u Λ x n hx hn
  have hc := nfinConj_holds X u h⁻¹ x.2 hxN
  have ec : ((h⁻¹ : Hfin X u) : X.B.I.Gf) * x.2 * ((h⁻¹ : Hfin X u) : X.B.I.Gf)⁻¹ =
      (h : X.B.I.Gf)⁻¹ * x.2 * (h : X.B.I.Gf) := by
    rw [Subgroup.coe_inv, inv_inv]
  rw [ec] at hc
  have hκK := kappa_Kset X ((h : X.B.I.Gf) * X.xu u) hlat hn.1.2 hx
  have eκ : ((h : X.B.I.Gf) * X.xu u)⁻¹ * x.2 * ((h : X.B.I.Gf) * X.xu u) =
      (X.xu u)⁻¹ * ((h : X.B.I.Gf)⁻¹ * x.2 * (h : X.B.I.Gf)) * X.xu u := by group
  have en : (h : X.B.I.Gf)⁻¹ * x.2 * (h : X.B.I.Gf) =
      X.xu u * (((h : X.B.I.Gf) * X.xu u)⁻¹ * x.2 * ((h : X.B.I.Gf) * X.xu u)) * (X.xu u)⁻¹ := by group
  have hnK : (h : X.B.I.Gf)⁻¹ * x.2 * (h : X.B.I.Gf) ∈ X.B.I.Kset := by
    rw [en]
    exact unitaryCongruence.K_mul X.B.I (unitaryCongruence.K_mul X.B.I (X.xu_K u) hκK) (unitaryCongruence.K_inv X.B.I (X.xu_K u))
  obtain ⟨hK2, hchi⟩ := hNK _ hc.1 hnK
  rw [hc.2] at hchi
  have hN : chiN X (((h : X.B.I.Gf) * X.xu u)⁻¹ * x.2 * ((h : X.B.I.Gf) * X.xu u)) = X.psiFinU u x.2 := by
    rw [eκ, chiN_conj X hc.1 hnK, hchi]
  rw [eκ] at hN ⊢
  refine ⟨hK2, hchi, fun k hk => ⟨?_, ?_⟩⟩
  · rw [chiN_mul X hK2 hk, hN]
  · rw [chiN_mul X hk hK2, hN]

end Formalism.L2.SG.Pf.VanishNConj

namespace Formalism.L2.SG.Pf

theorem nilradical_conj_level_of_mem (hN : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), UnipotentConjugateInLevel X u) :
    Formalism.L2.SG.TermOp.Vanish.NilradicalConjLevel := by
  intro D X Y u ρ x n hn hx
  exact VanishNConj.core X u (hN D X u) ((Y.cs u).h ρ) ((Y.cs u).lat_eq ρ) hn hx

end Formalism.L2.SG.Pf
end
end
