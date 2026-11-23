module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PhaseAtPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictK
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfOrbitAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellBru
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

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf.ChiNMul

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem gB_ne_zero : X.B.g ≠ 0 := by
  rw [X.g_eq]; exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero

theorem hfe : ∀ a b : Fin D.R.rS, a ≠ b → ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) (X.e0 b)) := by
  intro a b hab
  rw [hA_symm]
  have := (X.gramIntegral b a).2.2
  rw [if_neg (Ne.symm hab), sub_zero] at this
  exact Z_sig X.B.I X.B.g this

theorem hfz : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) X.z0) := fun a => ((X.formsAtZero).2 a).2

theorem e_step' {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset)
    (hc1 : ∀ a : Fin D.R.rS, (X.B.I.fmat x - 1) *ᵥ X.e0 a ∈ Mo X.B.I X.B.g (X.e0 '' {b | b.1 < a.1}))
    (a : Fin D.R.rS) : ∀ v ∈ Mo X.B.I X.B.g (X.e0 '' {b | b.1 < a.1 + 1}),
      (X.B.I.fmat x - 1) *ᵥ v ∈ Mo X.B.I X.B.g (X.e0 '' {b | b.1 < a.1}) :=
  pres1 X.B.I hx X.B.g _ _ (by
    rintro _ ⟨b, hb, rfl⟩
    have hb' : b.1 < a.1 + 1 := hb
    exact Mo_mono X.B.I (Set.image_mono (lt_sub (by omega))) (hc1 b)) (mL_Mo X.B.I)

theorem nxt_cong' {y : X.B.I.Gf} (hcy : Formalism.L2.SG.NormCut.NCong X y) (a : Fin D.R.rS) :
    (X.B.I.fmat y - 1) *ᵥ nxt X.e0 X.z0 a ∈ Mo X.B.I X.B.g (X.e0 '' {b | b.1 < a.1 + 1}) := by
  unfold nxt
  split_ifs with h
  · exact hcy.1 ⟨a.1 + 1, h⟩
  · refine Mo_mono X.B.I ?_ hcy.2
    rintro _ ⟨b, rfl⟩
    have := b.2
    exact ⟨b, show b.1 < a.1 + 1 by omega, rfl⟩

theorem chiN_mul {x y : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hcx : Formalism.L2.SG.NormCut.NCong X x)
    (hcy : Formalism.L2.SG.NormCut.NCong X y) : chiN X (x * y) = chiN X x * chiN X y := by
  unfold chiN
  refine psi_mul_of_Z X.B.I X.B.g X.psiEf_add X.psiEf_int (gB_ne_zero X) ?_
  have hf0 : ∀ a, X.f0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).2
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Z_sum X.B.I X.B.g _ _ fun a _ => ?_
  exact term_Z X.B.I X.B.g _ _ (nxt_Z X.B.I X.B.g X.e0 X.f0 X.z0 (hfe X) (hfz X) a)
    (Me_Q X.B.I X.B.g X.e0 X.f0 hf0 (hfe X) a (e_step' X hx hcx.1 a _ (nxt_cong' X hcy a)))

theorem chiN_one : chiN X 1 = 1 := by
  unfold chiN
  refine psi_Z X.B.I X.B.g X.psiEf_add X.psiEf_int (gB_ne_zero X) ?_
  simp only [show X.B.I.fmat 1 = 1 from rfl, Matrix.one_mulVec]
  exact Z_sum X.B.I X.B.g _ _ fun a _ => nxt_Z X.B.I X.B.g X.e0 X.f0 X.z0 (hfe X) (hfz X) a

end Formalism.L2.SG.Pf.ChiNMul

namespace Formalism.L2.SG.NormCut

section ChiNOut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows')

theorem chiN_colDiff (w : D.what₂.Word) (h h' : Hfin X w)
    (hk : ((h : X.B.I.Gf) * X.xu w)⁻¹ * ((h' : X.B.I.Gf) * X.xu w) ∈ X.B.I.Kset) :
    chiN X (((h : X.B.I.Gf) * X.xu w)⁻¹ * ((h' : X.B.I.Gf) * X.xu w)) = 1 := by
  have s := colStab X w h h' hk
  unfold chiN
  refine psi_Z X.B.I X.B.g X.psiEf_add X.psiEf_int (Formalism.L2.SG.Pf.ChiNMul.gB_ne_zero X) ?_
  refine Z_sum X.B.I X.B.g _ _ fun a _ => ?_
  have hf0 : X.f0 a ∈ X.B.I.Lf := (X.vectorsInLattice.1 a).2
  have hd : X.B.I.fmat (((h : X.B.I.Gf) * X.xu w)⁻¹ * ((h' : X.B.I.Gf) * X.xu w)) *ᵥ nxt X.e0 X.z0 a -
      nxt X.e0 X.z0 a ∈ mL X.B.I X.B.g := by
    unfold nxt; split_ifs
    · exact s.1 _
    · exact s.2
  rw [show X.B.I.fmat (((h : X.B.I.Gf) * X.xu w)⁻¹ * ((h' : X.B.I.Gf) * X.xu w)) *ᵥ nxt X.e0 X.z0 a =
    nxt X.e0 X.z0 a + (X.B.I.fmat (((h : X.B.I.Gf) * X.xu w)⁻¹ * ((h' : X.B.I.Gf) * X.xu w)) *ᵥ nxt X.e0 X.z0 a -
      nxt X.e0 X.z0 a) by abel, hA_add_right]
  exact Z_add X.B.I X.B.g (nxt_Z X.B.I X.B.g X.e0 X.f0 X.z0 (Formalism.L2.SG.Pf.ChiNMul.hfe X)
    (Formalism.L2.SG.Pf.ChiNMul.hfz X) a) (mL_Qs X.B.I X.B.g hf0 hd)

theorem chiNIndep_of_frameTie (hTF : FrameTie X u u' F0 F0') : ChiNIndep F0 F0' cs cs' := by
  intro t ρ ρ' hρ hρ' _
  have hb : cs.lamOf (cs.base t.lam) = t.lam := cs.base_lam _ t.mem
  have hb' : cs'.lamOf (cs'.base t.lam') = t.lam' := cs'.base_lam _ t.mem'
  have k1K := Formalism.L2.SG.Pf.colLatK X cs ρ (cs.base t.lam) (hρ.trans hb.symm)
  have k2K := Formalism.L2.SG.Pf.colLatK X cs' (cs'.base t.lam') ρ' (hb'.trans hρ'.symm)
  have κK := Formalism.L2.SG.Pf.termK X cs cs' (F0 := F0) (F0' := F0') t
  have κN := adm_norm_of_fixed_frames cs cs' hTF (Formalism.L2.SG.Pf.termK X cs cs') (Formalism.L2.SG.Pf.modGAt X) t
  have k1N := ncong_colDiff u _ _ k1K
  have k2N := ncong_colDiff u' _ _ k2K
  have hκ : kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt =
      (((cs.h ρ : X.B.I.Gf) * X.xu u)⁻¹ * ((cs.h (cs.base t.lam) : X.B.I.Gf) * X.xu u)) *
        kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) t.pt *
        (((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u')⁻¹ * ((cs'.h ρ' : X.B.I.Gf) * X.xu u')) := by
    unfold kOf; group
  rw [hκ, Formalism.L2.SG.Pf.ChiNMul.chiN_mul X (K_mul X.B.I k1K κK) (ncong_mul X k1K k1N κN) k2N,
    Formalism.L2.SG.Pf.ChiNMul.chiN_mul X k1K k1N κN, chiN_colDiff u _ _ k1K, chiN_colDiff u' _ _ k2K, one_mul,
    mul_one]

end ChiNOut

end Formalism.L2.SG.NormCut
end
end

section

noncomputable section

open scoped Classical ComplexConjugate ENNReal NNReal
open MeasureTheory

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full

section StabNSec

open Matrix
open scoped TensorProduct

def StabLatC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Hyps X Y u u' →
    ∀ (ρ' : (Y.cs u').Cl) (s : X.B.I.GA) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X s σ →
      σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → s ∈ Srat X u' →
      (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')⁻¹ * s.2 * (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u') ∈ X.K2 →
      Formalism.HermitianLatticesTheory.gmap σ ((Y.cs u').lamOf ρ') = (Y.cs u').lamOf ρ'

def StabFlagC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Hyps X Y u u' →
    ∀ (s : X.B.I.GA) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X s σ →
      σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → s ∈ Srat X u' →
      ∀ j, ∀ x ∈ Xflag (lf D (X.Fu u')) (j + 1), σ x - x ∈ Xflag (lf D (X.Fu u')) j

def StabOrthC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Hyps X Y u u' →
    ∀ (ρ' : (Y.cs u').Cl) (s : X.B.I.GA) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X s σ →
      σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → s ∈ Srat X u' →
      (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')⁻¹ * s.2 * (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u') ∈ X.K2 →
      ∀ x ∈ orth (VS D) (Xsp (lf D (X.Fu u'))), σ x - x ∈ Xsp (lf D (X.Fu u'))

theorem stabNC_of (hL : StabLatC) (hF : StabFlagC) (hO : StabOrthC) : StabNC := by
  intro D X Y u u' hH ρ' s σ hs hσ hS hk
  exact ⟨⟨hσ, hL D X Y u u' hH ρ' s σ hs hσ hS hk⟩, hF D X Y u u' hH s σ hs hσ hS,
    hO D X Y u u' hH ρ' s σ hs hσ hS hk⟩

theorem lattice_stabilizer_holds : StabLatC := by
  intro D X Y u u' hH ρ' s σ hs hσ hS hk
  obtain ⟨M, -, -, h2, h3⟩ := hs
  set a : X.B.I.Gf := ((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u' with ha
  have hkK : a⁻¹ * s.2 * a ∈ X.B.I.Kset := hH.1.2.1 _ hk
  have hfm : ∀ x y : X.B.I.Gf, X.B.I.fmat (x * y) = X.B.I.fmat x * X.B.I.fmat y := by
    intro x y; simp [Formalism.MainNotions.S.AutInst.fmat]
  have key : ∀ y : (VS D).V, σ y ∈ (Y.cs u').lamOf ρ' ↔ y ∈ (Y.cs u').lamOf ρ' := by
    intro y
    rw [(Y.cs u').lat_eq, (Y.cs u').lat_eq, h3, ← Formalism.L2.SG.Pf.Level.incl_mulVec X, ← h2]
    have e : X.B.I.fmat a⁻¹ *ᵥ (X.B.I.fmat s.2 *ᵥ Formalism.L2.SG.HidaSetting.incl X.B.I (X.crd y)) =
        X.B.I.fmat (a⁻¹ * s.2 * a) *ᵥ (X.B.I.fmat a⁻¹ *ᵥ Formalism.L2.SG.HidaSetting.incl X.B.I (X.crd y)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hfm, ← hfm]
      congr 2
      group
    rw [e]
    exact (hkK _).symm
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (key x).2 hx
  · intro hy
    refine Submodule.mem_map.2 ⟨σ.symm y, (key _).1 (by simpa using hy), by simp⟩

def StabOrthDescC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (s : X.B.I.GA)
    (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X s σ → σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → s.2 ∈ X.NfinU u' →
      ∀ x ∈ orth (VS D) (Xsp (lf D (X.Fu u'))), σ x - x ∈ Xsp (lf D (X.Fu u'))

theorem stab_nfin (hN : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u : D.what₂.Word), X.LevelSubgroupNormalized →
      Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK)
    {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (Y : Full X) (u' : D.what₂.Word) (hKL : X.LevelSubgroupNormalized)
    (ρ' : (Y.cs u').Cl) (s : X.B.I.GA) (hS : s ∈ Srat X u')
    (hk : (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')⁻¹ * s.2 * (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u') ∈ X.K2) :
    s.2 ∈ X.NfinU u' := by
  have hK := Y.hK
  obtain ⟨h1, h2⟩ := Formalism.L2.SG.PoincareInHH.Cut.sratComp_holds X u' s hS
  obtain ⟨ν, η, rfl, hνr, hν1, hν2, hη⟩ := Formalism.L2.SG.Pf.ratLevi_holds X u' _ (Subgroup.mem_inf.1 hS).1 h1 h2
  have hηp := Subgroup.mem_prod.1 (Subgroup.mem_inf.1 hη).2
  set hh : Hfin X u' := (Y.cs u').h ρ' with hhh
  have hn' : (hh : X.B.I.Gf)⁻¹ * ν.2 * hh ∈ X.NfinU u' := by
    have := (Formalism.L2.SG.PoincareInHH.Cut.nfinConj_holds X u' hh⁻¹ ν.2 hν2).1
    simpa using this
  let g2 : Hfin X u' := hh⁻¹ * ⟨η.2, hηp.2⟩ * hh
  have hLD := Formalism.L2.SG.PoincareInHH.Cut.levelDec_of X u' hK (Formalism.L2.SG.Pf.ksetSplit_holds X u')
    (Formalism.L2.SG.Pf.unipotent_in_level X u') _ hn' g2 (by
      have e : (X.xu u')⁻¹ * ((hh : X.B.I.Gf)⁻¹ * ν.2 * hh * (g2 : X.B.I.Gf)) * X.xu u' =
          ((hh : X.B.I.Gf) * X.xu u')⁻¹ * (ν * η).2 * ((hh : X.B.I.Gf) * X.xu u') := by
        simp only [g2, Subgroup.coe_mul, Subgroup.coe_inv, Prod.snd_mul]
        group
      rw [e]; exact hk)
  have hη1 : (⟨η, hη⟩ : Gam X u') = 1 := by
    refine hN D X Y u' hKL hh ⟨η, hη⟩ ?_
    show (X.xu u')⁻¹ * ((hh⁻¹ * Formalism.L2.SG.PoincareInHH.PoincareSetting.iotaF X u' ⟨η, hη⟩ * hh : Hfin X u') : X.B.I.Gf) *
      X.xu u' ∈ X.K2
    exact hLD.1
  have hη1' : η = 1 := congrArg Subtype.val hη1
  rw [hη1', mul_one]
  exact hν2

theorem stabOrthC_of (hD : StabOrthDescC)
    (hN : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u : D.what₂.Word), X.LevelSubgroupNormalized →
      Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK) : StabOrthC := by
  intro D X Y u u' hH ρ' s σ hs hσ hS hk
  exact hD D X u' s σ hs hσ (stab_nfin hN Y u' hH.1 ρ' s hS hk)

theorem incl_descent (I : Formalism.MainNotions.S.AutInst) [Nontrivial (Af I.F)] (S : Set (Fin I.n → I.E)) (w : Fin I.n → I.E)
    (hw : Formalism.L2.SG.HidaSetting.incl I w ∈
      Submodule.span (I.E ⊗[I.F] Af I.F) (Formalism.L2.SG.HidaSetting.incl I '' S)) :
    w ∈ Submodule.span I.E S := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap I.E (I.E ⊗[I.F] Af I.F)) (by
    rw [LinearMap.ker_eq_bot]
    intro a b h
    exact Algebra.TensorProduct.includeLeft_injective (S := I.F) (algebraMap I.F (Af I.F)).injective h)
  have hgc : ∀ c : I.E, g (Formalism.UG.inclE (F := I.F) (Af I.F) c) = c := fun c => LinearMap.congr_fun hg c
  have hgm : ∀ (r : I.E ⊗[I.F] Af I.F) (c : I.E), g (r * Formalism.UG.inclE (F := I.F) (Af I.F) c) = c * g r := by
    intro r c
    have e : r * Formalism.UG.inclE (F := I.F) (Af I.F) c = c • r := by
      rw [Algebra.smul_def, mul_comm]; rfl
    rw [e, map_smul, smul_eq_mul]
  obtain ⟨m, f, t, hsum⟩ := Submodule.mem_span_set'.1 hw
  have ht : ∀ i, ∃ s ∈ S, Formalism.L2.SG.HidaSetting.incl I s = (t i : Formalism.L2.SG.HidaSetting.VA I) := fun i => (t i).2
  choose s hs hst using ht
  have e : w = ∑ i, g (f i) • s i := by
    funext k
    have hk := congrFun hsum k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← hst] at hk ⊢
    have hk2 := congrArg g hk

    simp only [Formalism.L2.SG.HidaSetting.incl, map_sum, hgm, hgc] at hk2
    rw [← hk2]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hs i))

theorem crd_inj' {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {y y' : (VS D).V} (h : X.crd y = X.crd y') : y = y' := by
  apply X.bas.repr.injective
  ext i
  have := congrFun h i
  simp only [Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf] at this
  exact X.ιE.symm.injective this

theorem crd_descent {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (v : (VS D).V)
    (hv : X.crd v ∈ Submodule.span X.B.I.E (Set.range X.eR)) :
    v ∈ Submodule.span D.host.E (Set.range X.eX) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun X.B.I.E).1 hv
  have e : v = ∑ a, X.ιE (c a) • X.eX a := by
    apply crd_inj' X
    rw [← hc]
    change _ = Formalism.L2.SG.Pf.Vanish2.crdHom X (∑ a, X.ιE (c a) • X.eX a)

    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    show _ = X.crd (X.ιE (c a) • X.eX a)
    rw [Formalism.L2.SG.Pf.crd_smul X, RingEquiv.symm_apply_apply]
    rfl
  rw [e]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem orthogonal_stabilizer_descent : StabOrthDescC := by
  intro D X u' s σ hs hσ hn x hx
  obtain ⟨M, -, -, h2, h3⟩ := hs
  have : Nontrivial (Af X.B.I.F) := Formalism.L2.SG.Pf.Level.af_ntriv X.B.I.F
  have hx0 : ∀ a, Formalism.L2.SG.HidaSetting.hA X.B.I (Formalism.L2.SG.HidaSetting.incl X.B.I (X.eR a)) (Formalism.L2.SG.HidaSetting.incl X.B.I (X.crd x)) = 0 := by
    intro a
    rw [Formalism.L2.SG.PoincareInHH.Cut.hA_incl X]
    have hmem : X.eX a ∈ Xsp (lf D (X.Fu u')) := by
      show X.eX a ∈ Submodule.span D.host.E (Set.range (X.Fu u').e)
      rw [X.Fu_e]
      exact Submodule.subset_span ⟨a, rfl⟩
    have h0 : (VS D).hT (X.eX a) x = 0 := (mem_orth_iff _ _).1 hx _ hmem
    have h1 : Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.eR a) (X.crd x) = 0 := by
      apply X.ιE.injective
      rw [map_zero, show X.eR a = X.crd (X.eX a) from rfl, Formalism.L2.SG.PoincareInHH.Cut.hform_crd X]
      exact h0
    rw [h1, map_zero]
  have hmem := hn.2.2 _ hx0
  have e : (X.B.I.fmat s.2 - 1) *ᵥ Formalism.L2.SG.HidaSetting.incl X.B.I (X.crd x) =
      Formalism.L2.SG.HidaSetting.incl X.B.I (X.crd (σ x - x)) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, h2, Formalism.L2.SG.Pf.Level.incl_mulVec X, ← h3,
      Formalism.L2.SG.Pf.Vanish2.crd_sub' X]
    funext i
    simp [Formalism.L2.SG.HidaSetting.incl]
  rw [e] at hmem
  have hd := incl_descent X.B.I (Set.range X.eR) _ (by rw [← Set.range_comp]; exact hmem)
  show σ x - x ∈ Submodule.span D.host.E (Set.range (X.Fu u').e)
  rw [X.Fu_e]
  exact crd_descent X _ hd

theorem orthogonal_stabilizer_of_neat
    (hN : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u : D.what₂.Word), X.LevelSubgroupNormalized →
      Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK) : StabOrthC :=
  stabOrthC_of orthogonal_stabilizer_descent hN

end StabNSec

end Formalism.L2.SG.Pf.RegroupPf
end
end

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.UnitriangularPhases

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal Formalism.L2.SG.Pf

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def epsConj (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  fun c b => (-1) ^ (r - c.val) * M c b * (-1) ^ (r - b.val)

theorem zhatOM_mul (A Z M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    ZhatOM (A * Z * M) = A * ZhatOM Z * epsConj M := by
  ext a b
  simp only [ZhatOM, epsConj, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.sum_congr rfl fun d _ => ?_
  have h : ((-1 : E) ^ (r - c.val)) * (-1) ^ (r - c.val) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  linear_combination (-(A a d * Z d c * M c b * (-1 : E) ^ (r - b.val))) * h

theorem isUpUni_epsConj {M : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (h : IsUpUni M) : IsUpUni (epsConj M) := by
  intro i j
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · simp only [epsConj]; rw [(h i j).1 hij]; ring
  · subst hij
    simp only [epsConj]
    rw [(h i i).2 rfl, mul_one, ← pow_add, ← two_mul, pow_mul]
    simp

theorem sgUp_epsConj (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : sgUp (epsConj M) = -sgUp M := by
  unfold sgUp
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · simp only [epsConj]
    have e : r - a.val = (r - (a.val + 1)) + 1 := by omega
    rw [e, pow_succ]
    have hsq : ((-1 : E) ^ (r - (a.val + 1))) * (-1) ^ (r - (a.val + 1)) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; simp
    linear_combination (-(M a ⟨a.val + 1, h⟩)) * hsq
  · simp

theorem isLoUni_conjT {M : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (h : IsUpUni M) : IsLoUni M.conjTranspose := by
  intro i j
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · rw [Matrix.conjTranspose_apply, (h j i).1 hij, star_zero]
  · subst hij; rw [Matrix.conjTranspose_apply, (h i i).2 rfl, star_one]

theorem sgLo_conjT (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : sgLo M.conjTranspose = star (sgUp M) := by
  unfold sgLo sgUp
  rw [star_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · rfl
  · simp

theorem zhat_nm (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (Fs F2 : LFlag S r T')
    {n m : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ Fs) (hF2 : ∀ b, frame F2 b = n (m (frame Fs b))) :
    ∃ vn um : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUpUni vn ∧ IsUpUni um ∧
      (∀ b, n⁻¹ (frame F b) = ∑ c, vn c b • frame F c) ∧ (∀ b, m (frame Fs b) = ∑ c, um c b • frame Fs c) ∧
      ZhatL F F2 = vn.conjTranspose * ZhatL F Fs * um := by
  have hni := Formalism.L2.SG.Pf.nlam_inv hn
  obtain ⟨vn, hvn, hvnF⟩ := nlam_frame Λ F hni
  obtain ⟨um, hum, humF⟩ := nlam_frame Λ Fs hm
  refine ⟨vn, um, hvn, hum, hvnF, humF, ?_⟩
  ext a b
  have hiso : ∀ x y, S.hT (n⁻¹ x) (n⁻¹ y) = S.hT x y := hni.1.1
  have hnn : ∀ y, n⁻¹ (n y) = y := fun y => by
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
  have lhs : ZhatL F F2 a b = S.hT (frame F a) (frame F2 b) := rfl
  rw [lhs, hF2, ← hiso, hnn, hvnF, humF]

  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ₂, map_smul, Matrix.mul_apply,
  Matrix.conjTranspose_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  simp only [show ∀ x y, ZhatL F Fs x y = S.hT (frame F x) (frame Fs y) from fun _ _ => rfl, starRingEnd_apply,
    RingHom.id_apply]
  ring

theorem phase_move (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (Fs F2 : LFlag S r T')
    {n m : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ Fs) (hF2 : ∀ b, frame F2 b = n (m (frame Fs b)))
    (w : Point E (r + 1)) {Ls Us L2 U2 : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hLs : IsLoUni Ls) (hUs : IsUpUni Us)
    (hL2 : IsLoUni L2) (hU2 : IsUpUni U2) (hs : ZhatOM (ZhatL F Fs) = Ls * ptMat w * Us)
    (h2 : ZhatOM (ZhatL F F2) = L2 * ptMat w * U2) :
    ∃ vn um : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUpUni vn ∧ IsUpUni um ∧
      (∀ b, n⁻¹ (frame F b) = ∑ c, vn c b • frame F c) ∧ (∀ b, m (frame Fs b) = ∑ c, um c b • frame Fs c) ∧
      sgLo L2 + sgUp U2 = sgLo Ls + sgUp Us + star (sgUp vn) - sgUp um := by
  obtain ⟨vn, um, hvn, hum, hvF, humF, hZ⟩ := zhat_nm Λ F Fs F2 hn hm hF2
  refine ⟨vn, um, hvn, hum, hvF, humF, ?_⟩
  have e : (vn.conjTranspose * Ls) * ptMat w * (Us * epsConj um) = L2 * ptMat w * U2 := by
    rw [← h2, hZ, zhatOM_mul, hs]; simp only [Matrix.mul_assoc]
  have hds := simple_decomposition_holds E (r + 1) w _ _ _ _
    (Formalism.MainNotions.BridgeLemma.bru_lo_mul (isLoUni_conjT hvn) hLs) (Formalism.MainNotions.BridgeLemma.bru_up_mul hUs (isUpUni_epsConj hum))
    hL2 hU2 e
  rw [sgLo_mul (isLoUni_conjT hvn) hLs, sgUp_mul hUs (isUpUni_epsConj hum), sgLo_conjT, sgUp_epsConj] at hds
  linear_combination -hds

end Gen

end Formalism.L2.SG.Pf.UnitriangularPhases
end
end
