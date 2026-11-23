module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle330
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle232
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle013
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle325
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle333
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle324
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle331
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle336
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MemMatch

variable {D : D7}

theorem st_of_kset (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) (hβ : Formalism.L2.DIV.IsFrame β (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0))
    (κ : GA D (D.sp.Y 0)) (hκ : (iotaX X h κ).2 ∈ X.B.I.Kset) : Lev.finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β := by
  have key : ∀ (I : AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D),
      (castGA hI.symm (Formalism.IndefR.RationalEmbedding.iota D κ)).2 ∈ I.Kset → Lev.finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β := by
    intro I hI hx
    subst hI
    have hL : (Formalism.L2.SG.InstExistsPf.instOf D).L = Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0 :=
      Formalism.L2.SG.InstExistsPf.Lv_eq_map D
    have e := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D κ)
    have e2 : Lev.finE (D.sp.Y 0) κ = ((Formalism.IndefR.RationalEmbedding.iota D κ).2.1 : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) :=
      (congrArg (Lev.finE (D.sp.Y 0)) ((Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply κ)).symm.trans e
    have hx' := (GlobalTheory.FlagBasis.kset_iff (Formalism.L2.SG.InstExistsPf.instOf D) (β := β) (hL ▸ hβ) _).1 hx
    rw [e2]
    exact hx'
  exact key X.B.I h hκ

theorem exists_generic (Pg : Finset (Pl D.host.E)) : ∃ ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, IsGenericPsi Pg ψ := by
  have h : ∀ PP : Pl D.host.E, ∃ ψ : AddChar (kP PP) ℂ, ψ ≠ 1 := fun PP => by
    haveI : Finite (kP PP) := Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
    haveI : Nontrivial (kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
    obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (α := kP PP) (a := 1)).2 one_ne_zero
    exact ⟨ψ, fun e => hψ (by rw [e]; rfl)⟩
  choose ψ hψ using h
  exact ⟨ψ, fun PP _ => hψ PP⟩

theorem isIdentityOffFreePositions_rightBlock_iff {K : Type} [CommRing K] {r n : ℕ} (ρ k : ℕ) (hr : r ≤ n) (hn : n ≤ r) (g : GL (Fin n) K) :
    GlobalTheory.SymRes.IsPat ρ k (upperLeftBlock hr g) ↔ GlobalTheory.SymRes.IsPat ρ k g := by
  obtain rfl : r = n := le_antisymm hr hn
  rw [GlobalTheory.SeeConjRead.restrictedBlock_self_apply]

theorem reductionBlock_injective_of_eq {K : Type} [CommRing K] {r n : ℕ} (hr : r ≤ n) (hn : n ≤ r) (g g' : GL (Fin n) K)
    (h : upperLeftBlock hr g = upperLeftBlock hr g') : g = g' := by
  obtain rfl : r = n := le_antisymm hr hn
  rwa [GlobalTheory.SeeConjRead.restrictedBlock_self_apply, GlobalTheory.SeeConjRead.restrictedBlock_self_apply] at h

theorem conj_mem_GfC (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (s k : GA D (D.sp.Y 0)) (hk : k ∈ GfC (D.sp.Y 0)) : s * k * s⁻¹ ∈ GfC (D.sp.Y 0) := by
  rw [← GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff X h] at hk ⊢
  rw [map_mul, map_mul, map_inv, Prod.fst_mul, Prod.fst_mul, hk, mul_one, Prod.fst_inv, mul_inv_cancel]

theorem exists_read (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (Pg : Finset (Pl D.host.E)) (hTP : IsTypePlaces Pg) (hsp : ∃ e, IsIdemSum e Pg)
    (hid : ∀ PP : Pg, ∃ e, Formalism.L2.NTheta.IsIdemAt (D := D) e PP.1)
    (β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) (Λ) (N : ℕ) (hβ : Lev.IsBaseFrame (D.sp.Y 0) β Λ N) (s : GA D (D.sp.Y 0))
    (hSt : ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) s * β)) ↔
      ((iotaX X h κ).1 = 1 ∧ (iotaX X h κ).2 ∈ X.B.I.Kset)) :
    ∃ m : ∀ PP : Pg, GL (Fin (D.sp.Y 0).rank) (kP PP.1), ∀ k ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) k ∈ St β →
      ((iotaX X h (s * k * s⁻¹)).2 ∈ X.K2 ↔ ∀ PP : Pg, m PP * redFn β PP.1 (finE (D.sp.Y 0) k) * (m PP)⁻¹ ∈
        unipSym (kP PP.1) (D.sp.Y 0).rank D.R.rS D.R.k) := by
  obtain ⟨ψ0, hψ⟩ := exists_generic Pg
  obtain ⟨β₀, hβ₀, hK⟩ := GlobalTheory.SeeConjRead.read_fin X h Pg hTP (GlobalTheory.T.genusTypePlaceSet_not_conjugatePlaces Pg hTP hsp) ψ0 hψ
  have hfe : ∀ k : GA D (D.sp.Y 0), finE (D.sp.Y 0) (s * k * s⁻¹) =
      finE (D.sp.Y 0) s * finE (D.sp.Y 0) k * (finE (D.sp.Y 0) s)⁻¹ := fun k => by rw [map_mul, map_mul, map_inv]
  obtain ⟨β₂, rfl⟩ : ∃ β₂, β₀ = finE (D.sp.Y 0) s * β₂ := ⟨(finE (D.sp.Y 0) s)⁻¹ * β₀, by group⟩
  have h12 : ∀ k ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) k ∈ St β → finE (D.sp.Y 0) k ∈ St β₂ := by
    intro k hk hS
    have h1 := ((hSt (s * k * s⁻¹)).1 ⟨conj_mem_GfC X h s k hk, by
      rw [hfe, GlobalTheory.FrameConj.conj_mem_St_iff]; exact hS⟩).2
    have h2 := st_of_kset X h _ hβ₀ _ h1
    rwa [hfe, GlobalTheory.FrameConj.conj_mem_St_iff] at h2
  have hm := fun PP : Pg => (hid PP).elim fun e he => GlobalTheory.T.splitPlaceReductions_conj_of_nestedFrameStabilisers D (D.sp.Y 0) β β₂ Λ N hβ e PP.1 he h12
  choose m hm using hm
  refine ⟨m, fun k hk hS => ?_⟩
  rw [(hK _).1, hfe, GlobalTheory.FrameConj.conj_mem_St_iff]
  simp only [GlobalTheory.FrameConj.redFn_conj]
  refine ⟨fun hh PP => ?_, fun hh => ⟨h12 k hk hS, fun PP hPP => ?_⟩⟩
  · rw [← hm PP _ hS (h12 k hk hS)]; exact hh.2 PP.1 PP.2
  · rw [hm ⟨PP, hPP⟩ _ hS (h12 k hk hS)]; exact hh ⟨PP, hPP⟩

end GlobalTheory.MemMatch

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LevelComb
open GlobalTheory.FinPl (MxAt idAt)

variable {D : D7} {u : D.what₂.Word} {d : Dat D u} {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E}

section Red
variable {PP : Formalism.L2.DIV.Pl D.host.E} (G : GAt d τ PP)

end Red

section Grp
variable (G : ∀ PP : d.c.Pg, GAt d τ PP.1)

end Grp

end GlobalTheory.LevelComb

noncomputable section
namespace GlobalTheory.LevelComb
open GlobalTheory.FinPl (MxAt idAt)

section Comb
variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D}

theorem comb_single_zero (f : WO S T → ℂ) : comb ψ S T (Finsupp.single 0 1) f = f := by
  funext w
  simp [comb, Finsupp.support_single_ne_zero, heisO, symplOH, symplO, hO]

end Comb

variable {D : D7} {u : D.what₂.Word} {d : Dat D u} {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E}

end GlobalTheory.LevelComb

namespace GlobalTheory.LevelComb

end GlobalTheory.LevelComb
end
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_unit_weight_real_center_action_fock_monomial : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ k : KerDat S T, k.Is ψ θ x y → ∃ wt : (FVar D T.rank S.rank →₀ ℕ) → GA D S → ℂ, (∀ α, ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ‖wt α z‖ = 1 ∧ ∀ c : WO S T →₀ ℂ, IsFinComb c → k.om (z, 1) (pureTensorO ψ θ S T x.s y.s x.B y.B (comb ψ S T c k.vac) (MvPolynomial.monomial α 1)) = wt α z • pureTensorO ψ θ S T x.s y.s x.B y.B (comb ψ S T c k.vac) (MvPolynomial.monomial α 1)) ∧ ∀ χ : GA D S → ℂ, {α | ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → wt α z = χ z}.Finite := by
  first | exact @GlobalTheory.CenFockWt.central_wt | exact GlobalTheory.CenFockWt.central_wt | (intros; apply GlobalTheory.CenFockWt.central_wt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.VacSign

theorem af_ext' {D : D7} {x y : Af D.host.F} (h : ∀ w, evalV D.host.F w x = evalV D.host.F w y) : x = y :=
  Subtype.ext (funext fun w => h w)

theorem latO_acts_by_signs : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ x ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P, ∃ ε : ℂ, ε * ε = 1 ∧ ∀ f, Vac ψ S T LS LT P f → heisO ψ S T x f = ε • f := by
  intro D k _ _ _ _ ι p I P hP ψ hψ S T LS LT hS hT x hx
  classical
  have hΛ : ∀ u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P,
      ∀ u' ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P,
        ψ (symplO S T u u') = 1 := fun u hu u' hu' =>
    (GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ S T LS LT hS hT P u (GlobalTheory.FinPl.LatMem.latO_mxAt hu)).1 hu u' hu'
  let G := GlobalTheory.LatVac.signGroup ψ _ hΛ
    (IsLatVac (heisO ψ S T) (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P))
  have half : ∀ e, IsSplitIdem D e →
      ∀ u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P, IsHalf e u → u ∈ G :=
    fun e he u hu hh => ⟨hu, 1, one_mul _, fun f hf => by rw [hf.2 e he u hu hh, one_smul]⟩
  have splitC : ∀ e, IsSplitIdem D e → IsSplitIdem D (cA D e) := by
    rintro e ⟨he1, he2, v, ε, hpl, he3⟩
    exact ⟨by rw [← RingHom.map_mul, he1], by rw [GlobalTheory.LatVac.cA_cA, mul_comm, he2], v, ε, hpl,
      by rw [GlobalTheory.LatVac.cA_cA, add_comm, he3]⟩
  have hsub : ∀ i, latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = (p i).v) ≤
      latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P := by
    intro i
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hs, rest⟩
    exact ⟨α, hα, fun v hv => hs v fun h => hv ((hP.mem v).2 ⟨i, h⟩), rest⟩
  have piece : ∀ i, ∀ w ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = (p i).v),
      w ∈ G := by
    intro i w hw
    obtain ⟨h1, h2⟩ := GlobalTheory.SplitVac.idem_latO D k (p i) S T LS LT w hw
    have he := (p i).split
    have hee : (p i).e * (p i).e = (p i).e := he.1
    have hz : (Matrix.of fun a b => cA D (p i).e * w a b : WO S T) = w - Matrix.of fun a b => (p i).e * w a b := by
      ext a b
      rw [Matrix.of_apply, Matrix.sub_apply, Matrix.of_apply, eq_sub_iff_add_eq', ← add_mul, h2]
    have hyG : (Matrix.of fun a b => (p i).e * w a b : WO S T) ∈ G :=
      half _ he _ (hsub i h1) fun a b => by rw [Matrix.of_apply, ← mul_assoc, hee]
    have hzG : (Matrix.of fun a b => cA D (p i).e * w a b : WO S T) ∈ G := by
      refine half _ (splitC _ he) _ ?_ fun a b => ?_
      · rw [hz]; exact sub_mem (hsub i hw) (hsub i h1)
      · rw [Matrix.of_apply, ← mul_assoc, ← RingHom.map_mul, hee]
    rw [hz] at hzG
    simpa using add_mem hyG hzG
  have hxG : x ∈ G := by
    induction hx using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, hsupp, a, ha, s, hs, t, ht, rfl⟩ := hw
      have hdec : α = ∑ i ∈ I.toFinset, GlobalTheory.FinPl.LatMem.indP D.host.F (· = (p i).v) * α := by
        apply af_ext'
        intro v

        rw [map_sum]
        simp only [map_mul, GlobalTheory.FinPl.LatMem.evalV_indP]
        by_cases hv : P v
        · obtain ⟨i, rfl⟩ := (hP.mem v).1 hv
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hj
            rw [if_neg (fun h => hj (hP.inj h).symm), zero_mul]
          · intro h
            exact absurd (List.mem_toFinset.2 (hP.all i)) h
        · rw [hsupp v hv]
          simp
      rw [hdec]
      refine Finset.sum_induction _ (fun β : Af D.host.F => (Matrix.of fun i j =>
          (pairA D.host.F 0 β) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) ∈ G)
        (fun β γ hβ hγ => ?_) ?_ (fun i _ => ?_)
      · have e : (Matrix.of fun i j => (pairA D.host.F 0 (β + γ)) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) :
            WO S T) = (Matrix.of fun i j => (pairA D.host.F 0 β) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) +
            Matrix.of fun i j => (pairA D.host.F 0 γ) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) := by
          ext i j
          rw [Matrix.add_apply, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply, GlobalTheory.LatVac.pair_add,
            TensorProduct.add_tmul]
        rw [e]
        exact add_mem hβ hγ
      · have e : (Matrix.of fun i j => (pairA D.host.F 0 (0 : Af D.host.F)) ⊗ₜ[D.host.F]
            (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) = 0 := by
          ext i j
          rw [Matrix.of_apply, Matrix.zero_apply]
          exact TensorProduct.zero_tmul _ _
        rw [e]
        exact zero_mem _
      · refine piece i _ (AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.mul_mem_intAf
          (GlobalTheory.FinPl.LatMem.indicatorAdele_mem_integralAdeles' D.host.F _) hα, fun v hv => ?_, a, ha, s, hs, t, ht, rfl⟩)
        rw [map_mul, GlobalTheory.FinPl.LatMem.indicatorAdele_supported D.host.F _ v hv, zero_mul]
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
  obtain ⟨-, ε, hε, h⟩ := hxG
  exact ⟨ε, hε, fun f hf => h f hf.2⟩

end GlobalTheory.FinPl.VacSign

end
end

section

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.FirstTermCompare

variable {D : D7}

theorem hasIw_of_good {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) {l : Lvl T} (hl : l.Good) :
    HasIw d l.K ∧ IsCompact (l.K : Set (GA D T)) := by
  have h := GlobalTheory.T.goodMajorantLevel_conj_unitaryAdelicMaximalCompact D T T₀ r d l.c hl.2.2
    (GlobalTheory.T.adelic_iwasawa_decomposition_wittIsotropicStabilizer D T T₀ r d l.c GlobalTheory.Core.Rk.IP.Model.isSplit_two hl.2.2) l hl
  exact ⟨h.1, h.2.1⟩

end GlobalTheory.RegSch.FirstTermCompare

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

variable {D : D7}

theorem sum_support_comb {Y Z G : Type*} [AddCommMonoid G] [Module ℂ G] (n : ℕ) (a : Fin n → Y →₀ ℂ)
    (b : Fin n → Y → Z →₀ ℂ) (R : Z → G) :
    ∑ z ∈ (∑ i, ∑ y ∈ (a i).support, a i y • b i y).support, (∑ i, ∑ y ∈ (a i).support, a i y • b i y) z • R z =
      ∑ i, ∑ y ∈ (a i).support, a i y • ∑ z ∈ (b i y).support, b i y z • R z := by
  change Finsupp.sum _ (fun z r => r • R z) = _
  rw [← Finsupp.sum_finsetSum_index (by simp) (by intros; exact add_smul _ _ _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finsupp.sum_finsetSum_index (by simp) (by intros; exact add_smul _ _ _)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finsupp.sum_smul_index' (by simp)]
  simp only [Finsupp.sum, Finset.smul_sum, smul_smul, smul_eq_mul]

theorem twoX_of_laws : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), BiAct D → CenFock D → LiftSum D → c.Is →
    (∀ s, (t s).Is) → RealEq t → KerX t → RdX t → TwoX t := by
  intro D c 𝒯 t hBi hCen hLS hc ht hreal hker hrd
  intro j hj C hC y
  have hj0 : j < D.R.m := by omega
  have hj1 : j + 1 < D.R.m := by omega
  obtain ⟨χ, hχ⟩ := hrd j (by omega)
  have step1 : ∃ (n : ℕ) (P : Fin n → PolF D (c.X (j + 1)).rank (c.X j).rank)
      (P' : Fin n → PolF D (c.X (j + 1 + 1)).rank (c.X (j + 1)).rank), ∀ s, ∀ ψ ∈ (t s).Ram j, ∀ β,
        (t s).two j (fun α => (t s).rd j α ψ y) C β = ∑ i, ∑ γ,
          ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1)) (P' i)
            (∑ α, ((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y)) := by
    by_cases hex : ∃ (s : 𝒯) (_ : (t s).Ch j) (γ : (t s).Ch (j + 1)) (_ : (t s).Ch (j + 1 + 1)), True
    · obtain ⟨s₀, α₀, γ₀, β₀, -⟩ := hex
      obtain ⟨n, P, P', hF⟩ := GlobalTheory.T.doubleLift_reduction_to_fockVectors_uniform D hBi hCen hLS c.ψ c.θ hc.inf (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))
        (c.x j) (c.x (j + 1)) (c.x (j + 1 + 1)) (hc.x j (by omega)) (hc.x (j + 1) (by omega)) (hc.x (j + 1 + 1) (by omega))
        ((t s₀).ker j α₀ γ₀) ((t s₀).ker (j + 1) γ₀ β₀) ((ht s₀).ker j hj0 α₀ γ₀) ((ht s₀).ker (j + 1) hj1 γ₀ β₀) χ C hC.1 hC.2
      refine ⟨n, P, P', fun s ψ hψ β => ?_⟩
      have hrdψ := fun α => hχ s ψ hψ α y
      have e1 : ∀ α γ, biLift ((t s).kom j) ((t s).kom (j + 1)) (c.x j).vol (c.x (j + 1)).vol ((t s).rd j α ψ y)
          (biComb c.ψ _ _ _ ((t s).dd j α γ) ((t s).dd (j + 1) γ β) C) =
          ∑ i, ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1)) (P' i)
            (((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y)) := fun α γ =>
        hF ((t s).ker j α γ) ((t s).ker (j + 1) γ β) ((ht s).ker j hj0 α γ) ((ht s).ker (j + 1) hj1 γ β) rfl rfl
          (fun a ha b hb f hf => hreal j hj0 s s₀ a ha b hb f hf)
          (fun a ha b hb f hf => hreal (j + 1) hj1 s s₀ a ha b hb f hf) _ (hrdψ α).1 (hrdψ α).2
      have e2 : ∀ i γ, ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1)) (P' i)
            (∑ α, ((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y)) =
          ∑ α, ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1)) (P' i)
            (((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y)) := by
        intro i γ
        have h := (hLS c.ψ c.θ hc.inf _ _ (c.x (j + 1)) (c.x (j + 1 + 1)) (hc.x _ (by omega)) (hc.x _ (by omega)) _
          ((ht s).ker (j + 1) hj1 γ β) (P' i)).2.2 ((t s).Ch j) Finset.univ (fun _ => 1)
          (fun α => ((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y))
          (fun α _ => (hLS c.ψ c.θ hc.inf _ _ (c.x j) (c.x (j + 1)) (hc.x _ (by omega)) (hc.x _ (by omega)) _
            ((ht s).ker j hj0 α γ) (P i)).2.1 _ (hrdψ α).1)
        simpa using h
      simp only [Tup.two, e1, e2]
      rw [Finset.sum_comm]
      calc _ = ∑ γ, ∑ i, ∑ α, ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1)) (P' i)
            (((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y)) :=
            Finset.sum_congr rfl fun γ _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
    · push Not at hex
      refine ⟨0, Fin.elim0, Fin.elim0, fun s ψ _ β => ?_⟩
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      refine Finset.sum_eq_zero fun α _ => Finset.sum_eq_zero fun γ _ => ?_
      exact ((hex s α γ β).elim)
  obtain ⟨n, P, P', hstep⟩ := step1
  choose a ha using fun i : Fin n => hker j hj0 y (P i)
  choose b hb using fun (i : Fin n) (y' : c.Fr (j + 1)) => hker (j + 1) hj1 y' (P' i)
  obtain ⟨χ', hχ'⟩ := hrd (j + 1) (by omega)
  refine ⟨∑ i, ∑ y' ∈ (a i).support, a i y' • b i y', fun s ψ hψ β => ?_⟩
  rw [hstep s ψ hψ β, sum_support_comb]
  have hKψ := (ht s).stabK j hj0 ψ hψ
  have e3 : ∀ i γ, ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1)) (P' i)
        (∑ α, ((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y)) =
      ∑ y' ∈ (a i).support, ((t s).cK j * a i y') • ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1))
        (P' i) ((t s).rd (j + 1) γ ((t s).K j ψ) y') := by
    intro i γ
    rw [ha i s ψ hψ γ, Finset.smul_sum]
    simp only [smul_smul]
    exact (hLS c.ψ c.θ hc.inf _ _ (c.x (j + 1)) (c.x (j + 1 + 1)) (hc.x _ (by omega)) (hc.x _ (by omega)) _
      ((ht s).ker (j + 1) hj1 γ β) (P' i)).2.2 _ _ _ _ (fun y' _ => (hχ' s _ hKψ γ y').1)
  simp only [e3]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [← Finset.smul_sum, hb i y' s _ hKψ β, smul_smul, smul_smul]
  congr 1
  ring

end GlobalTheory.SeeSaw

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf


theorem _root_.GlobalTheory.T.weil_operator_target_summand_preserves_theta_functions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (T A B S : HSp D) (o : OrthDec T A B) (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om S A), IsWeilDatumO ψ S A χ χ' om → ∀ p, IsThetaFunO ψ S T fun x => om p (fun u => F ((o.resT S).symm (u, (o.resT S x).2))) (o.resT S x).1 := by
  first | exact @GlobalTheory.SliceTarget.main | exact GlobalTheory.SliceTarget.main | (intros; apply GlobalTheory.SliceTarget.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.weil_operator_commutes_superposition_slices_source : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om A T), IsWeilDatumO ψ A T χ χ' om → ∀ (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (k : Ω → WO B T) (a : Ω → ℂ), Measurable k → Integrable a μ → ∀ p, IsThetaFunO ψ S T (fun x => om p (fun u => F ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1) ∧ ∀ u₀, om p (fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂μ) u₀ = ∫ w, a w * om p (fun u => F ((o.resS T).symm (u, k w))) u₀ ∂μ := by
  first | exact @GlobalTheory.WeilSuperpos.weil_comm_superpos | exact GlobalTheory.WeilSuperpos.weil_comm_superpos | (intros; apply GlobalTheory.WeilSuperpos.weil_comm_superpos <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.weil_operator_one_variable_preserves_sq_norm_orthogonal_sum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om A T), IsWeilDatumO ψ A T χ χ' om → ∀ p, ∫⁻ x in 𝓕, ‖om p (fun u => f ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1‖ₑ ^ 2 ∂μ = ∫⁻ x in 𝓕, ‖f x‖ₑ ^ 2 ∂μ) ∧ ∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om B T), IsWeilDatumO ψ B T χ χ' om → ∀ p, ∫⁻ x in 𝓕, ‖om p (fun v => f ((o.resS T).symm ((o.resS T x).1, v))) (o.resS T x).2‖ₑ ^ 2 ∂μ = ∫⁻ x in 𝓕, ‖f x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.WeilSliceUnit.main | exact GlobalTheory.WeilSliceUnit.main | (intros; apply GlobalTheory.WeilSliceUnit.main <;> assumption)
end
