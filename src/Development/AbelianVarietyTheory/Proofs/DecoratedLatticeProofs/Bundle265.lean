module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSI
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle240
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle259
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle371
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle220
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle239
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle206
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle243
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019

@[expose] public section

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.holomorphicContinuationValue_nnrealPow_factor : ∀ (h h' : ℂ → ℂ) (s₀ c : ℂ) (r : ℝ≥0) (σ : ℝ), 0 < r → HolValueAt h s₀ c → (∀ s : ℂ, σ < s.re → h' s = npow r (s₀ - s) * h s) → HolValueAt h' s₀ c := by
  first | exact @GlobalTheory.StdUnn.holValueAt_npow_sub_mul | exact GlobalTheory.StdUnn.holValueAt_npow_sub_mul | (intros; apply GlobalTheory.StdUnn.holValueAt_npow_sub_mul <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

noncomputable section

namespace GlobalTheory.Core.Rk.RealCoef

open scoped ComplexConjugate ComplexOrder

theorem petersson_conj {D : D7} {V : HSp D} (m : Measure (GA D V)) (φ ψ : GA D V → ℂ) :
    GlobalTheory.Cusp.petersson V m φ ψ = conj (GlobalTheory.Cusp.petersson V m ψ φ) := by
  simp only [GlobalTheory.Cusp.petersson, GlobalTheory.AutomorphicL2Unitary.pet]
  rw [← integral_conj]
  congr 1
  funext q
  simp [mul_comm]

theorem rcoef_of_fun {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) (m : Measure (GA D V)) (hm : m.IsHaarMeasure)
    (Y : GA D V → c.W) (hYc : Continuous Y) (hYi : ∀ γ ∈ GQ V, ∀ h, Y (γ * h) = Y h) {K : Set (GA D V)}
    (hK : IsCompact K) (hKc : ∀ h, ∃ γ ∈ GQ V, ∃ k ∈ K, h = γ * k)
    (hsh : ∀ b ∈ GinfC V, ∀ g, Y (g * b) = c.ρ b⁻¹ (Y g)) :
    ∃ z : ℂ, (∀ w : c.W, ∀ b ∈ GinfC V,
      GlobalTheory.Core.Rk.IP.rcoef m (fun g => ⟪w, Y g⟫_ℂ) (fun g => ⟪w, Y g⟫_ℂ) b = z * ⟪c.ρ b w, w⟫_ℂ) ∧ (Y ≠ 0 → z ≠ 0) := by
  haveI := hm
  haveI : m.IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds V m hm
  let φ : c.W → GA D V → ℂ := fun x g => ⟪x, Y g⟫_ℂ
  have hφL : ∀ x, GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) (φ x) := fun x γ hγ g => by
    simp only [φ, hYi γ hγ g]
  have hφc : ∀ x, Continuous (φ x) := fun x => continuous_const.inner hYc
  have hφ2 : ∀ x, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GQ V) m (φ x) := fun x => by
    obtain ⟨C, hCb⟩ := hK.exists_bound_of_continuousOn (hφc x).continuousOn
    refine GlobalTheory.Cusp.memL2_of_bounded_continuous_invariant (hφL x) (hφc x) (C := C) fun h => ?_
    obtain ⟨γ, hγ, k, hk, e⟩ := hKc h
    rw [e, hφL x γ hγ k]
    exact hCb k hk
  have hshift : ∀ b ∈ GinfC V, ∀ x, rTr V b (φ x) = φ (c.ρ b x) := by
    intro b hb x
    funext g
    show ⟪x, Y (g * b)⟫_ℂ = ⟪c.ρ b x, Y g⟫_ℂ
    rw [hsh b hb g, ← hc.2.1 b x (c.ρ b⁻¹ (Y g)), GlobalTheory.DefiniteEnd.rho_inv_cancel]
  have hadd : ∀ x x', φ (x + x') = φ x + φ x' := fun x x' => funext fun g => inner_add_left _ _ _
  have hsmul : ∀ (a : ℂ) x, φ (a • x) = (starRingEnd ℂ a) • φ x := fun a x => funext fun g => inner_smul_left _ _ _
  let B : c.W →ₗ⋆[ℂ] c.W →ₗ[ℂ] ℂ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun x x' => GlobalTheory.Cusp.petersson V m (φ x) (φ x'))
    (fun x x' y => by rw [hadd]; exact GlobalTheory.Cusp.petersson_add_left (hφ2 x) (hφ2 x') (hφ2 y))
    (fun a x y => by rw [hsmul]; exact GlobalTheory.Cusp.petersson_smul_left _ _ _)
    (fun x y y' => by
      rw [petersson_conj m (φ x) (φ (y + y')), hadd, GlobalTheory.Cusp.petersson_add_left (hφ2 y) (hφ2 y') (hφ2 x), map_add (f := _),
        ← petersson_conj m (φ x) (φ y), ← petersson_conj m (φ x) (φ y')])
    (fun a x y => by
      rw [petersson_conj m (φ x) (φ (a • y)), hsmul, GlobalTheory.Cusp.petersson_smul_left, map_mul,
        ← petersson_conj m (φ x) (φ y), Complex.conj_conj, RingHom.id_apply, smul_eq_mul])
  have hB : ∀ x x', B x x' = GlobalTheory.Cusp.petersson V m (φ x) (φ x') := fun _ _ => rfl
  have hinv : ∀ u ∈ GinfC V, ∀ x x', B (c.ρ u x) (c.ρ u x') = B x x' := by
    intro u hu x x'
    rw [hB, hB, ← hshift u hu, ← hshift u hu]
    exact GlobalTheory.Cusp.petersson_rTr (hφ2 x) (hφ2 x') u
  obtain ⟨z, hz⟩ := GlobalTheory.T.real_invariant_sesquilinear_form_eq_smul_inner D V c hc B hinv
  refine ⟨z, fun w b hb => ?_, fun hY hz0 => ?_⟩
  · show GlobalTheory.Cusp.petersson V m (rTr V b (φ w)) (φ w) = _
    rw [hshift b hb, ← hB]
    exact hz _ _
  · apply hY
    have h0 : ∀ x, φ x = 0 := by
      intro x
      by_contra hne
      have hpos := GlobalTheory.Cusp.petersson_self_pos (hφ2 x) (hφc x) hne
      have h1 : GlobalTheory.Cusp.petersson V m (φ x) (φ x) = 0 := by
        rw [← hB, hz x x, hz0, zero_mul]
      rw [h1, Complex.zero_re] at hpos
      exact lt_irrefl _ hpos
    funext g
    exact inner_self_eq_zero.1 (congrFun (h0 (Y g)) g)



theorem rcoef_scalar : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (m : Measure (GA D (Vc D i))), m.IsHaarMeasure → ∃ z : ℂ, (∀ (w : (R.cV i).W), ∀ b ∈ GinfC (Vc D i), GlobalTheory.Core.Rk.IP.rcoef m (fun g => ⟪w, R.extV i t y g⟫_ℂ) (fun g => ⟪w, R.extV i t y g⟫_ℂ) b = z * ⟪(R.cV i).ρ b w, w⟫_ℂ) ∧ (y ≠ 0 → z ≠ 0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC i t y m hm
  have hmod := hC.models
  have hc : (R.cV i).Is := hmod.cV i
  have hx := (hmod.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have hp : (Vc D i).IsPosDef := hmod.vpos i
  have hpd : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ =>
    GlobalTheory.RepsObj.gramAt_posDef hp (D.sp.V_sig ((i : ℕ) + 1)) τ
  obtain ⟨K, hK, hKc⟩ := GlobalTheory.definite_unitary_cocompact (Vc D i) hpd
  have hYc : Continuous (R.extV i t y) := GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) hc (R.βV i) (R.datVt i t) hx
  have hYi : ∀ γ ∈ GQ (Vc D i), ∀ h, R.extV i t y (γ * h) = R.extV i t y h := GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hx
  have hsh : ∀ b ∈ GinfC (Vc D i), ∀ g, R.extV i t y (g * b) = (R.cV i).ρ b⁻¹ (R.extV i t y g) :=
    fun b hb g => GlobalTheory.DownLift.DefiniteComp.extV_mul_inf R i t y hb g
  have key := rcoef_of_fun (R.cV i) hc m hm (R.extV i t y) hYc hYi hK hKc hsh
  refine ⟨key.choose, key.choose_spec.1, fun hy => key.choose_spec.2 fun hY0 => hy ?_⟩
  have hf0 : (R.HV i t).e y = 0 := by
    funext k
    obtain ⟨g, rfl⟩ := (finHom (Vc D i)).rangeRestrict_surjective k
    have e : (R.cV i).ρ g⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict g)) = 0 := congrFun hY0 g
    have e2 := congrArg ((R.cV i).ρ g) e
    rw [GlobalTheory.DefiniteEnd.rho_inv_cancel] at e2
    exact e2.trans (LinearMap.map_zero _)
  exact (hmod.HV i t).1 (hf0.trans ((R.HV i t).e.map_zero).symm)

end GlobalTheory.Core.Rk.RealCoef
end
end

section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop

noncomputable section

namespace GlobalTheory.MiTop.PairingL2

open Formalism.L2.SG.JoinSI Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowsJoinPinned

variable {D : D7}

theorem inner_sp {St : Formalism.L2.SG.HidaSetting.HidaSetting D} (s : Bool) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs}
    (Dc : DefCols Df) (hK : St.LevelSubgroupCharacter) (Gd : GoodOp St) (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW St hK (wdD x))
    (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram) (Sp : SPer Dc) (hSp : Sp = spOf s Dc hK Gd wdD pw bR)
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (sEE : E →ₗ⋆[ℂ] Sp.HH) (sEEc : E →ₗ⋆[ℂ] Tw s (HHX St)) (h : HEq sEE sEEc) (e : E) (m : Dc.Mem)
    (c : Fin (Dc.a m) → ℂ) :
    ⟪sEE e, Sp.Pu m (cjv s c)⟫_ℂ = cj s ⟪Tw.out (sEEc e), (pw m).op (ramCrd (bR m) c)⟫_ℂ := by
  subst hSp
  obtain rfl := eq_of_heq h
  exact inner_spOf s Dc hK Gd wdD pw bR m _ c

theorem inner_join {St : Formalism.L2.SG.HidaSetting.HidaSetting D} (s : Bool) {Bs : DefBase D.what₂.LL} {Z : Type}
    {sd : Z → DefSide Bs} (Dcf : ∀ z, DefCols (sd z)) (Spf : ∀ z, SPer (Dcf z)) (z0 z1 : Z) (hz : z0 = z1)
    (Dc : DefCols (sd z1)) (hdc : Dcf z1 = Dc) (hK : St.LevelSubgroupCharacter) (Gd : GoodOp St)
    (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW St hK (wdD x)) (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram)
    (hsp : HEq (Spf z1) (spOf s Dc hK Gd wdD pw bR))
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (sEE : E →ₗ⋆[ℂ] (Spf z0).HH) (sEEc : E →ₗ⋆[ℂ] Tw s (HHX St)) (h : HEq sEE sEEc) (e : E)
    (m : (Dcf z0).Mem) (m' : Dc.Mem) (hm : HEq m m') (c : Fin ((Dcf z0).a m) → ℂ) (c' : Fin (Dc.a m') → ℂ)
    (hc : HEq c c') :
    ⟪sEE e, (Spf z0).Pu m (cjv s c)⟫_ℂ = cj s ⟪Tw.out (sEEc e), (pw m').op (ramCrd (bR m') c')⟫_ℂ := by
  subst hz
  subst hdc
  obtain rfl := eq_of_heq hm
  obtain rfl := eq_of_heq hc
  exact inner_sp s (Dcf z0) hK Gd wdD pw bR (Spf z0) (eq_of_heq hsp) sEE sEEc h e m c

theorem iota_symm_eq {I : Formalism.MainNotions.S.AutInst} (h : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ι : GA D (D.sp.Y 0) ≃* I.GA) (hι : HEq ι (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv) (x : I.GA) :
    ι.symm x = ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)).symm x := by
  subst h
  obtain rfl := eq_of_heq hι
  rfl

end GlobalTheory.MiTop.PairingL2

namespace GlobalTheory.MiTop.PairingL2

open Formalism.L2.SG.JoinSI Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowsJoinPinned

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

theorem op_eq {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {hK : X.LevelSubgroupCharacter} {u : D.what₂.Word} (p : PerW X hK u) (y : (D.mem u).A.Mu0)
    (T : Cu X u hK) (hT : Formalism.L2.SG.ColDict.colDictL X p.Tr hK T = (y : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)) :
    ((p.op y : HHX X) : L2X X) = PuFun X u hK p.Dt T := by
  have hd : (Formalism.L2.SG.ColDict.colDict X p.Tr hK p.hI p.hB).symm y = T := by
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext hT.symm
  show ((Formalism.L2.SG.PoincareInHH.PoincareSetting.Pu X u hK p.Dt p.hD p.hin p.hlin
    ((Formalism.L2.SG.ColDict.colDict X p.Tr hK p.hI p.hB).symm y) : HHX X) : L2X X) = _
  rw [hd]
  rfl

end GlobalTheory.MiTop.PairingL2

namespace GlobalTheory.MiTop.PairingL2

open Formalism.L2.SG.JoinSI Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowsJoinPinned

theorem exists_eval {D : D7} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))}
    {𝓕 : Set (GA D (D.sp.Y 0))} {E : Submodule ℂ (MMap M)} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} {Gd : GoodOp St}
    {ι : GA D (D.sp.Y 0) ≃* St.B.I.GA} {t : GA D (D.sp.Y 0)} {c : ℝ} (hE : EvalTieT M μ 𝓕 E St Gd ι t c)
    (h : St.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hι : HEq ι (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv) :
    ∃ v₀ : M.Vec, (∀ τ, ‖(v₀ τ : M.H τ)‖ = 1) ∧ ∀ T : E, ∃ F : L2X St,
      ((F : St.B.I.GA → ℂ) =ᵐ[muX St] evS St h t (PiTensorProduct.lift (T : MMap M) (PiTensorProduct.tprod ℂ v₀))) ∧
      star F ∈ HHX St ∧ ((sEEofTT M μ 𝓕 E St Gd ι t c T : HHX St) : L2X St) = star F := by
  refine ⟨hE.choose, hE.choose_spec.1, fun T => ⟨(hE.choose_spec.2.choose T : EEC St Gd), ?_, ?_, ?_⟩⟩
  · refine (hE.choose_spec.2.choose_spec T).1.trans (Filter.Eventually.of_forall fun x => ?_)
    have h1 : ι.symm x = (iotaX St h).symm x := iota_symm_eq h ι hι x
    show (T : MMap M) hE.choose (ι.symm x * t) =
      PiTensorProduct.lift (T : MMap M) (PiTensorProduct.tprod ℂ hE.choose) ((iotaX St h).symm x * t)
    rw [h1]
    exact (congrFun (PiTensorProduct.lift.tprod (φ := (T : MMap M)) hE.choose) _).symm
  · exact ((mem_EEC St Gd _).1 (hE.choose_spec.2.choose T).2).1
  · unfold sEEofTT
    simp only [dif_pos hE]
    rfl

theorem inner_smul_star {D : D7} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} (h : St.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (t : GA D (D.sp.Y 0)) (f g : GA D (D.sp.Y 0) → ℂ) (l a : ℂ) (hfg : f = l • g) (F φ P : L2X St)
    (hF : (F : St.B.I.GA → ℂ) =ᵐ[muX St] evS St h t f) (hφ : (φ : St.B.I.GA → ℂ) =ᵐ[muX St] evS St h t g)
    (y z : HHX St) (hy : (y : L2X St) = star F) (hz : (z : L2X St) = P) :
    ⟪a • y, z⟫_ℂ = starRingEnd ℂ a * l * ⟪star φ, P⟫_ℂ := by
  have h1 : F = l • φ := by
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [hF, hφ, MeasureTheory.Lp.coeFn_smul l φ] with x h1 h2 h3
    rw [h1, h3, Pi.smul_apply, h2, hfg]
    rfl
  have h2 : star (l • φ) = starRingEnd ℂ l • star φ := (Formalism.L2.SG.RowDict.conjL (muX St)).map_smulₛₗ l φ
  rw [inner_smul_left, Submodule.coe_inner, hy, hz, h1, h2, inner_smul_left, starRingEnd_self_apply, mul_assoc]

end GlobalTheory.MiTop.PairingL2

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

theorem _root_.GlobalTheory.T.thetaLiftPair_definite_place_character_data : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), (∃ cA a, Defin R.θ (Vc D i) cA a) ∧ Places (Vc D i) (R.βV i) (R.Pg ∪ R.Q t) ∧ under (R.Pg ∪ R.Q t) = GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t ∧ GlobalTheory.LFun.UnrOff (F := D.host.F) (E := D.host.E) (chiV R i t) (↑(under (D := D) (R.Pg ∪ R.Q t))) ∧ (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) ∧ (Wc D i).SigOK ∧ (Wc D i).rank = D.R.r ∧ 0 < D.R.r ∧ (Vc D i).rank = D.R.r + D.R.t ∧ D.R.r + 5 ≤ D.R.t ∧ R.ΛV i = GlobalTheory.AdelicU.frameLat (Vc D i) ∧ R.ΛW i = GlobalTheory.AdelicU.frameLat (Wc D i) := by
  exact @GlobalTheory.DownPair.pair_data
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section General

variable {K : Type} [Field K] [NumberField K]

theorem locL_finsetSum {ι : Type} (s : Finset ι) (d : ι → GlobalTheory.LFun.Fam K) (w : HeightOneSpectrum (𝓞 K)) (x : ℂ) :
    GlobalTheory.LFun.locL (∑ i ∈ s, d i) w x = ∏ i ∈ s, GlobalTheory.LFun.locL (d i) w x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [GlobalTheory.LFun.locL]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha, GlobalTheory.LFun.locL_add, ih]

theorem bounded_single (T : Set (HeightOneSpectrum (𝓞 K))) (z : HeightOneSpectrum (𝓞 K) → ℂˣ)
    (hz : ∀ w, ‖(z w : ℂ)‖ = 1) : GlobalTheory.LFun.Bounded T (fun w => {z w}) 1 0 := fun w _ =>
  ⟨by simp, fun b hb => by rw [Multiset.mem_singleton.1 hb, Real.rpow_zero, hz]⟩

theorem eulerProd_add_segFam {ι : Type} (T : Set (HeightOneSpectrum (𝓞 K))) (A : GlobalTheory.LFun.Fam K) (s : Finset ι)
    (z : ι → HeightOneSpectrum (𝓞 K) → ℂˣ) (t : ℕ) (x : ℂ) (hA : GlobalTheory.LFun.Converges T A x)
    (hz : ∀ i ∈ s, ∀ l < t, GlobalTheory.LFun.Converges T (fun w => {z i w}) (x + ((t : ℂ) - 1) / 2 - l)) :
    GlobalTheory.LFun.eulerProd T (A + ∑ i ∈ s, GlobalTheory.LFun.segFam (z i) t) x = GlobalTheory.LFun.eulerProd T A x *
      ∏ i ∈ s, ∏ l ∈ Finset.range t, GlobalTheory.LFun.eulerProd T (fun w => {z i w}) (x + ((t : ℂ) - 1) / 2 - l) := by
  have h1 : HasProd (fun w : {w // w ∉ T} => ∏ i ∈ s, ∏ l ∈ Finset.range t,
      GlobalTheory.LFun.locL (fun u => {z i u}) w (x + ((t : ℂ) - 1) / 2 - l))
      (∏ i ∈ s, ∏ l ∈ Finset.range t, GlobalTheory.LFun.eulerProd T (fun w => {z i w}) (x + ((t : ℂ) - 1) / 2 - l)) :=
    hasProd_prod fun i hi => hasProd_prod fun l hl => (hz i hi l (Finset.mem_range.1 hl)).hasProd
  have h2 := hA.hasProd.mul h1
  show ∏' w : {w // w ∉ T}, _ = _
  refine HasProd.tprod_eq ?_
  convert h2 using 1
  funext w
  rw [GlobalTheory.LFun.locL_add, locL_finsetSum]
  simp only [GlobalTheory.LFun.locL_segFam']

end General

theorem chainLW_holds : ∀ D : D7, ChainLW D := by
  intro D c hc B hB k hk
  set T := GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) with hT
  have hrt : D.R.r + 5 ≤ D.R.t := D.R.rank_add_five_le
  have hrt' : (D.R.r : ℝ) + 5 ≤ D.R.t := by exact_mod_cast hrt
  have hΛ : ∀ i : ℕ, ∃ Λ : ℂ → ℂ, i ∈ Finset.Icc 1 k → Differentiable ℂ Λ ∧
      (∀ z : ℂ, 1 < z.re → Λ z = GlobalTheory.LFun.eulerProd T
        (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹) w}) z) ∧
      ∀ n : ℕ, 1 ≤ n → n ≤ D.R.t → Λ n ≠ 0 := by
    intro i
    by_cases hi : i ∈ Finset.Icc 1 k
    · have h1 := (Finset.mem_Icc.1 hi).1
      have h2 := (Finset.mem_Icc.1 hi).2
      obtain ⟨Λ, h⟩ := GlobalTheory.T.thetaChain_char_quotient_LFunction_entire_ne_zero D c hc i (k + 1) h1 (by omega) (by omega)
      exact ⟨Λ, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose Λ hΛ using hΛ
  set A := GlobalTheory.LFun.twist B (GlobalTheory.LFun.val (F := D.host.F) (c.μ (k + 1)))⁻¹ with hA
  have hAb : GlobalTheory.LFun.Bounded T A D.R.r ((D.R.r : ℝ) / 2) :=
    hB.twist fun w _ => by simp [GlobalTheory.LFun.norm_val]
  let z : ℕ → HeightOneSpectrum (𝓞 D.host.E) → ℂˣ := fun i => GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹)
  have hzc : ∀ i, ∀ y : ℂ, 1 < y.re → GlobalTheory.LFun.Converges T (fun w => {z i w}) y := fun i y hy =>
    (bounded_single T (z i) fun w => GlobalTheory.LFun.norm_val _ _).converges (by simpa using hy)
  let H : ℂ → ℂ := fun x => GlobalTheory.LFun.eulerProd T A (x + 1 / 2) *
    ∏ i ∈ Finset.Icc 1 k, ∏ l ∈ Finset.range D.R.t, Λ i (x + 1 / 2 + ((D.R.t : ℂ) - 1) / 2 - l)
  have hEq : ∀ x : ℂ, ((D.R.r : ℝ) + D.R.t + 2) < x.re →
      H x = GlobalTheory.LFun.LSD D c.S (chainPar c B k) (c.chT (k + 1)) (x + 1 / 2) := by
    intro x hx
    have hre : ∀ l : ℕ, l < D.R.t → 1 < (x + 1 / 2 + ((D.R.t : ℂ) - 1) / 2 - l).re := by
      intro l hl
      have : (l : ℝ) + 1 ≤ D.R.t := by exact_mod_cast hl
      have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
      simp
      linarith
    show _ = GlobalTheory.LFun.eulerProd T (GlobalTheory.LFun.twist (chainPar c B k)
      (GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)))⁻¹) (x + 1 / 2)
    rw [GlobalTheory.T.thetaLiftChainHeckeParameter_twist_next_target_char D c B k, ← hA, eulerProd_add_segFam T A (Finset.Icc 1 k) z D.R.t (x + 1 / 2)
      (hAb.converges (by have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _; simp; linarith))
      (fun i _ l hl => hzc i _ (hre l hl))]
    refine congrArg (GlobalTheory.LFun.eulerProd T A (x + 1 / 2) * ·) (Finset.prod_congr rfl fun i hi => Finset.prod_congr rfl fun l hl => ?_)
    exact (hΛ i hi).2.1 _ (hre l (Finset.mem_range.1 hl))
  have hU : IsOpen (GlobalTheory.Cont.rightOf (((D.R.r : ℝ) + 1) / 2)) := GlobalTheory.Cont.isOpen_rightOf _
  have hD : DifferentiableOn ℂ H (GlobalTheory.Cont.rightOf (((D.R.r : ℝ) + 1) / 2)) := by
    refine DifferentiableOn.mul ?_ (Differentiable.differentiableOn ?_)
    · refine hAb.differentiableOn.comp (differentiableOn_id.add_const _) fun x hx => ?_
      simp only [GlobalTheory.Cont.mem_rightOf] at hx
      simp
      linarith
    · exact Differentiable.fun_finsetProd fun i hi => Differentiable.fun_finsetProd fun l _ =>
        (hΛ i hi).1.comp (by fun_prop)
  have hAn := hD.analyticOnNhd hU
  have hmem : ((D.R.t : ℂ) / 2) ∈ GlobalTheory.Cont.rightOf (((D.R.r : ℝ) + 1) / 2) := by
    simp only [GlobalTheory.Cont.mem_rightOf]
    simp
    linarith
  refine ⟨H ((D.R.t : ℂ) / 2), ?_, H, ⟨_, hmem, GlobalTheory.Cont.isRightDomain_rightOf _, hAn.meromorphicOn,
    (D.R.r : ℝ) + D.R.t + 2, fun x hx => hEq x hx⟩, hAn _ hmem, rfl⟩
  refine mul_ne_zero ((hAb.converges ?_).ne_zero) ?_
  · simp
    linarith
  · refine Finset.prod_ne_zero_iff.2 fun i hi => Finset.prod_ne_zero_iff.2 fun l hl => ?_
    have hl' := Finset.mem_range.1 hl
    have e : (D.R.t : ℂ) / 2 + 1 / 2 + ((D.R.t : ℂ) - 1) / 2 - l = ((D.R.t - l : ℕ) : ℂ) := by
      rw [Nat.cast_sub hl'.le]
      ring
    rw [e]
    exact (hΛ i hi).2.2 _ (by omega) (by omega)

end GlobalTheory.ChainOnto

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaLiftChain_surjective_of_adjoint_nonvanishing : ∀ D : D7, FinDim D → MetEx D → EigSpan D → ParIndep D → ChainUp D → OntoAll D := by
  first | exact @GlobalTheory.ChainOnto.ontoAll_of_chainUp | exact GlobalTheory.ChainOnto.ontoAll_of_chainUp | (intros; apply GlobalTheory.ChainOnto.ontoAll_of_chainUp <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaIntegral_conjCuspForm_parameterTransfer : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, TransferOn D (fun _ => True) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ t : ℕ, T.rank = S.rank + t → ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → UnrAt χS w' ∧ UnrAt χT w') → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (f : WO S T → ℂ), VacFin ψ S T v f → ∀ (y : GA D S → ℂ) (B : Multiset ℂˣ), IsAutFunSm θ S y → IsCuspFun S y → IsParamVec D.sp.cm.sig S.gram (frameLat S) h ((rightReg ℂ (GA D S) ℂ).comp (embV S v)) (fun g => conj (y g)) B → (fun x => ∫ g in 𝓕, thetaKO om g x f * conj (y g) ∂ν) ≠ 0 → IsParamVec D.sp.cm.sig T.gram (frameLat T) h ((rightReg ℂ (GA D T) ℂ).comp (embV T v)) (fun x => ∫ g in 𝓕, thetaKO om g x f * conj (y g) ∂ν) (stepPar χS χT t (fun _ => B) w) := by
  first | exact @GlobalTheory.ChainOnto.thetaIntegral_param | exact GlobalTheory.ChainOnto.thetaIntegral_param | (intros; apply GlobalTheory.ChainOnto.thetaIntegral_param <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

theorem _root_.GlobalTheory.T.linearForm_extV_mem_A0_and_prin_invariant : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t cA a, Defin R.θ (Vc D i) cA a → ∀ (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ), (fun g => l (R.extV i t y g)) ∈ GlobalTheory.Cusp.A0 R.θ (Vc D i) cA ∧ ∀ κ ∈ prin (Vc D i) (R.βV i) (R.Pg ∪ R.Q t), ∀ g, l (R.extV i t y (g * κ)) = l (R.extV i t y g) := by
  first | exact @GlobalTheory.DownLift.DefiniteComp.definiteScalarComponent_isCusp_and_congruence_fixed | exact GlobalTheory.DownLift.DefiniteComp.definiteScalarComponent_isCusp_and_congruence_fixed | (intros; apply GlobalTheory.DownLift.DefiniteComp.definiteScalarComponent_isCusp_and_congruence_fixed <;> assumption)
end
