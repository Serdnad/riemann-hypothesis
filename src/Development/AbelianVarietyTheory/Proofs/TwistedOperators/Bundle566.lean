module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle326
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle501
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle305
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle500
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle554
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2227
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle413
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle562
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOMemFinSub
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertVac

variable {D : D7} {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
  {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}

theorem placeIdem_smul_eq (hε : IsPlaceIdem D v ε) {u : WO S T} (hu : u ∈ latO S T LS LT fun w => w = v) :
    algebraMap (AF D.host.F) (AE D) ε • u = u := by
  obtain ⟨β, rfl, h1, h0⟩ := hε
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    have hβα : β * α = α := GlobalTheory.SplitIdem.af_ext _ fun w => by
      rw [map_mul]
      by_cases hw : w = v
      · subst hw; rw [h1, one_mul]
      · rw [hP w hw, mul_zero]
    ext i j
    change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (_ ⊗ₜ _) = _ ⊗ₜ _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    exact Prod.ext (mul_zero _) hβα
  | zero => rw [smul_zero]
  | add x x' _ _ h h' => rw [smul_add, h, h']
  | neg x _ h => rw [smul_neg, h]

theorem mem_latO_place_iff (hε : IsPlaceIdem D v ε) (u : WO S T) :
    u ∈ (latO S T LS LT fun w => w = v) ↔
      u ∈ (latO S T LS LT fun _ => True) ∧ algebraMap (AF D.host.F) (AE D) ε • u = u :=
  ⟨fun h => ⟨GlobalTheory.PlaceModel.latO_le_top _ h, placeIdem_smul_eq hε h⟩,
    fun h => h.2 ▸ GlobalTheory.PlaceModel.placeIdem_smul_mem hε h.1⟩

theorem actO_inv_actO (g : GA D S) (h : GA D T) (u : WO S T) : actO S T g⁻¹ h⁻¹ (actO S T g h u) = u := by
  unfold actO
  rw [inv_inv, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, ← GlobalTheory.FinWeilO.mt_mul, inv_mul_cancel,
    GlobalTheory.FinWeilO.mt_one, Matrix.mul_one, ← Matrix.mul_assoc, ← GlobalTheory.FinWeilO.mt_mul, inv_mul_cancel,
    GlobalTheory.FinWeilO.mt_one, Matrix.one_mul]

theorem actO_injective (g : GA D S) (h : GA D T) : Function.Injective (actO S T g h) :=
  Function.LeftInverse.injective (actO_inv_actO g h)

theorem om_fixes_latVac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), NonSplitAt D v ε → UnramAt ε χS → UnramAt ε χT → ∀ (g : GA D S) (h : GA D T), SuppPl ε S g → SuppPl ε T h → (∀ u, u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔ actO S T g h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) → ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f₀ → om (g, h) f₀ = f₀ := by
  intro D ψ S T χS χT om hW ΛS ΛT hS hT v ε hv uS uT g h hg hh hst f₀ hf hvac
  obtain ⟨η, e1, e2, e3, e4⟩ := GlobalTheory.T.exists_unramifiedHeckeChar_halfExponent_restrict_quadratic D
  refine GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified D ψ hW.std S T ΛS ΛT hS hT χS χT om ⟨η, e1, e4, e3, e2⟩ hW v ε hv uS uT g h hg hh
    (fun u => ?_) f₀ hf fun u hu => ?_
  · rw [mem_latO_place_iff hv.1, mem_latO_place_iff hv.1, ← hst, ← GlobalTheory.FinWeilO.actO_smul,
      (actO_injective g h).eq_iff]
  · obtain ⟨a, ha, ha2⟩ := GlobalTheory.FinWeilO.exists_half_of_nonSplit hv
    have h1 : 2 • (a • u) = u := by
      rw [two_nsmul, ← add_smul, ← two_mul, ha2, placeIdem_smul_eq hv.1 hu]
    have h2 := hvac.1 (a • u)
      (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a ha u (GlobalTheory.PlaceModel.latO_le_top _ hu))
    rwa [h1] at h2

end GlobalTheory.InertVac

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VecInvInert

variable {D : D7} {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
  {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}

theorem idem_smul_eq (hε : IsPlaceIdem D v ε) {u : WO S T} (hu : u ∈ latO S T LS LT fun w => w = v) :
    algebraMap (AF D.host.F) (AE D) ε • u = u := by
  obtain ⟨β, rfl, h1, h0⟩ := hε
  have hβα : ∀ α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F, (∀ w, ¬ w = v → evalV D.host.F w α = 0) → β * α = α := by
    intro α hα
    apply RestrictedProduct.ext
    intro w
    show β w * α w = α w
    by_cases hw : w = v
    · subst hw
      have : β w = 1 := h1
      rw [this, one_mul]
    · have : α w = 0 := hα w hw
      rw [this, mul_zero]
  unfold latO at hu
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
      obtain ⟨α, -, hα, a, -, s, -, t, -, rfl⟩ := hw
      funext i j
      show algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β) * _ = _
      rw [Algebra.TensorProduct.algebraMap_apply]
      simp only [Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      congr 1
      show ((0 * 0, β * α) : AF D.host.F) = (0, α)
      rw [mul_zero, hβα α hα]
  | zero => exact smul_zero _
  | add x y _ _ hx hy => rw [smul_add, hx, hy]
  | neg x _ hx => rw [smul_neg, hx]

theorem mem_place_iff (hε : IsPlaceIdem D v ε) (u : WO S T) :
    u ∈ (latO S T LS LT fun w => w = v) ↔
      u ∈ (latO S T LS LT fun _ => True) ∧ algebraMap (AF D.host.F) (AE D) ε • u = u := by
  constructor
  · intro hu
    exact ⟨GlobalTheory.PlaceModel.latO_le_top _ hu, idem_smul_eq hε hu⟩
  · rintro ⟨hu, he⟩
    have := GlobalTheory.PlaceModel.placeIdem_smul_mem hε hu
    rwa [he] at this

theorem act_injective (g : GA D S) (h : GA D T) : Function.Injective (actO S T g h) := by
  intro x y hxy
  unfold actO at hxy
  have hT : Formalism.L2.Theta.mt T h⁻¹ * Formalism.L2.Theta.mt T h = 1 := by
    rw [← GlobalTheory.AdelicLatMove.mt_mul, inv_mul_cancel, GlobalTheory.AdelicLatMove.mt_one]
  have hS : Formalism.L2.Theta.mt S g⁻¹ * Formalism.L2.Theta.mt S g = 1 := by
    rw [← GlobalTheory.AdelicLatMove.mt_mul, inv_mul_cancel, GlobalTheory.AdelicLatMove.mt_one]
  calc x = (Formalism.L2.Theta.mt T h⁻¹ * Formalism.L2.Theta.mt T h) * x * (Formalism.L2.Theta.mt S g⁻¹ * Formalism.L2.Theta.mt S g) := by
        rw [hT, hS, Matrix.one_mul, Matrix.mul_one]
    _ = Formalism.L2.Theta.mt T h⁻¹ * (Formalism.L2.Theta.mt T h * x * Formalism.L2.Theta.mt S g⁻¹) * Formalism.L2.Theta.mt S g := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.L2.Theta.mt T h⁻¹ * (Formalism.L2.Theta.mt T h * y * Formalism.L2.Theta.mt S g⁻¹) * Formalism.L2.Theta.mt S g := by
        rw [hxy]
    _ = (Formalism.L2.Theta.mt T h⁻¹ * Formalism.L2.Theta.mt T h) * y * (Formalism.L2.Theta.mt S g⁻¹ * Formalism.L2.Theta.mt S g) := by
        simp only [Matrix.mul_assoc]
    _ = y := by
        rw [hT, hS, Matrix.one_mul, Matrix.mul_one]

theorem om_fixes_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∃ η, IsEtaTilde D η) → ∀ v ε, NonSplitAt D v ε → UnramAt ε χS → UnramAt ε χT → ∀ g h, SuppPl ε S g → SuppPl ε T h → (∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) → ∀ f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f → om (g, h) f = f := by
  intro D ψ S T ΛS ΛT χS χT om hW hS hT hη v ε hns hχS hχT g h hg hh hlat f hf hvac
  have hε : IsPlaceIdem D v ε := hns.1
  have key := GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified D ψ hW.std S T ΛS ΛT hS hT χS χT om hη hW v ε hns hχS hχT
  have hc : ∀ (c : AE D) (x : WO S T), actO S T g h (c • x) = c • actO S T g h x := by
    intro c x
    unfold actO
    rw [Matrix.mul_smul, Matrix.smul_mul]
  refine key g h hg hh ?_ f hf ?_
  · intro u
    rw [mem_place_iff hε, mem_place_iff hε]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(hlat u).1 h1, by rw [← hc, h2]⟩
    · rintro ⟨h1, h2⟩
      refine ⟨(hlat u).2 h1, ?_⟩
      apply act_injective g h
      rw [hc]
      exact h2
  · intro u hu
    obtain ⟨a, ha, h2a⟩ := GlobalTheory.FinWeilO.exists_half_of_nonSplit hns
    have hu' := (mem_place_iff hε u).1 hu
    have hau := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a ha u hu'.1
    have e2 : 2 • (a • u) = u := by
      rw [two_nsmul, ← add_smul, ← two_mul, h2a]
      exact hu'.2
    have := hvac.1 (a • u) hau
    rwa [e2] at this

end GlobalTheory.VecInvInert

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThPVecNe



theorem thPVec_ne_zero : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), T.rank ≤ S.rank → ∀ (B : C.Bas), C.IsB B → ∀ ΛT : Lt D.host.E T.rank, IsSelfDualC T ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (f₀ f : WO S T → ℂ), IsThPVecOf C.ψ C.θ S T (fun _ => 1) (C.sB B) (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) βS βT Pg Q ξ f₀ f → f ≠ 0 := by
  intro D S T C hn B hB ΛT hΛT βS βT hβS hβT Pg Q ξ f₀ f hf
  obtain ⟨hv, e, he, hth⟩ := hf
  have hS := GlobalTheory.Ker.Base.selfDualC_stdL (S := S) C.m.gS
  have hinf := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  have hidem : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he]
  have hce : cA D e * cA D (cA D e) = 0 := by rw [← RingHom.map_mul, he.2, map_zero]
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hth
  have hf0 : f₀ ≠ 0 := by
    intro h0
    obtain ⟨⟨p, hp⟩, hn1⟩ := hv.2.norm
    have h1 := hn1 p hp
    rw [h0] at h1
    simp [nrm2] at h1
  have hSB := GlobalTheory.PlaceVec.isSBHalf_of_red (GlobalTheory.PlaceVec.selfDual_isFullLattice S _ hS)
    (GlobalTheory.PlaceVec.selfDual_isFullLattice T _ hΛT) hinf (frMapAdj S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)
    (GlobalTheory.PlaceVec.frMapAdj_up S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_down S T βS βT) (Pg ∪ Q)
    (fun y => omegaK Pg y * omegaQ Q T.rank ξ (-1) y) fun y y' h => by
      rw [GlobalTheory.PlaceVec.omegaK_congr Pg fun PP hPP => h PP (Finset.mem_union_left _ hPP),
        GlobalTheory.PlaceVec.omegaQ_congr Q _ ξ _ fun PP hPP => h PP (Finset.mem_union_right _ hPP)]
  obtain ⟨x, hx1, hx2, hx3⟩ := GlobalTheory.AdjDatumNe.exists_datum_ne_zero D S T βS βT Pg Q (Pg ∪ Q) ξ e hn he
    (fun PP hPP => Finset.mem_union_left _ hPP) (fun PP hPP => Finset.mem_union_right _ hPP)
  rw [hall Tm hTm]
  refine GlobalTheory.PlaceModelInj.placeModel_ne_zero D C.ψ S T (stdL D.host.E S.rank) ΛT (cA D e) f₀ _ Tm hv.1 hS hΛT hidem hce
    hinf hTm hf0 hSB ?_
  intro h0
  have := congrFun h0 x
  simp only [Pi.zero_apply] at this
  rw [if_pos ⟨hx1, hx2⟩] at this
  exact hx3 this

end GlobalTheory.ThPVecNe

end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.AdjRedOnto

open Formalism.IndefR.Datum GlobalTheory.AdelicLatMove GlobalTheory.PlaceVec

theorem exists_half_redM_eq : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, GlobalTheory.LiftRows.IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) → ∀ z : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP),
  ∃ x : WO (Vc D i) (Wc D i), IsHalf (cA D e) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) ∧ ∀ PP ∈ R.Pg ∪ R.Q t, redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) = z PP := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ i t σ s P cμ cη m ω BW f₀ f c io _ e he z
  have he2 := idemSum_mul_self he
  obtain ⟨hi, hres⟩ := GlobalTheory.AdjDatumNe.idemSum_res he
  obtain ⟨⟨es, h1, h2⟩, -⟩ := he
  have hk : ∀ PP ∈ R.Pg ∪ R.Q t, toEAf D (es PP) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun PP hPP => (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (h1 PP hPP)).1
  have hdel : ∀ PP ∈ R.Pg ∪ R.Q t, ∀ PP' (hPP' : PP' ∈ R.Pg ∪ R.Q t),
      Formalism.L2.DIV.resS D.host.F PP ⟨toEAf D (es PP'), hk PP' hPP'⟩ = if PP' = PP then 1 else 0 := by
    intro PP hPP PP' hPP'
    by_cases hq : PP' = PP
    · subst hq
      rw [if_pos rfl]
      exact (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (h1 PP' hPP')).2
    · rw [if_neg hq]
      have hne : PP ≠ PP' := fun h => hq h.symm
      have horth : es PP * es PP' = 0 :=
        (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (h1 PP hPP).1 (h1 PP' hPP').1).resolve_left fun h => by
          have h' := h1 PP' hPP'
          rw [← h] at h'
          exact hne (isIdemAt_inj (h1 PP hPP) h')
      have h4 : (⟨toEAf D (es PP), hk PP hPP⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨toEAf D (es PP'), hk PP' hPP'⟩ = 0 :=
        Subtype.ext (by change toEAf D (es PP) * toEAf D (es PP') = 0; rw [← RingHom.map_mul, horth, RingHom.map_zero])
      have h5 := congrArg (Formalism.L2.DIV.resS D.host.F PP) h4
      rwa [RingHom.map_mul, RingHom.map_zero, (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (h1 PP hPP)).2, one_mul] at h5
  choose a ha using fun (PP : Formalism.L2.DIV.Pl D.host.E) (j : Fin (Vc D i).rank) (k : Fin (Wc D i).rank) =>
    Ideal.Quotient.mk_surjective (I := PP.asIdeal) (z PP j k)
  set L : Formalism.L2.DIV.Pl D.host.E → Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (Formalism.IndefR.Datum.EAf D) :=
    fun PP j k => ((Formalism.L2.DIV.oToS D.host.F D.host.E (a PP j k) : Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Datum.EAf D) with hL
  obtain ⟨x, hx, hx'⟩ := GlobalTheory.AdjDatumNe.exists_half_frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) he2
    (∑ PP ∈ R.Pg ∪ R.Q t, toEAf D (es PP) • L PP)
  have hent : ∀ j k, frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x j k =
      ((⟨toEAf D e, hi⟩ * ∑ PP ∈ (R.Pg ∪ R.Q t).attach,
        ⟨toEAf D (es PP.1), hk PP.1 PP.2⟩ * Formalism.L2.DIV.oToS D.host.F D.host.E (a PP.1 j k) :
          Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Datum.EAf D) := by
    intro j k
    rw [hx', Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Subring.coe_mul, AddSubmonoidClass.coe_finsetSum]
    congr 1
    rw [← Finset.sum_attach]
    rfl
  refine ⟨x, hx, fun j k => ?_, fun PP hPP => ?_⟩
  · rw [hent]; exact Subtype.prop _
  · funext j k
    unfold redM
    rw [dite_eq_left (by rw [hent]; exact Subtype.prop _)]
    have hsub : (⟨frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x j k, by rw [hent]; exact Subtype.prop _⟩ :
        Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨toEAf D e, hi⟩ * ∑ PP ∈ (R.Pg ∪ R.Q t).attach,
        ⟨toEAf D (es PP.1), hk PP.1 PP.2⟩ * Formalism.L2.DIV.oToS D.host.F D.host.E (a PP.1 j k) := Subtype.ext (hent j k)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsub, RingHom.map_mul, hres PP hPP, one_mul, map_sum]
    simp_rw [RingHom.map_mul, Formalism.L2.DIV.resS_oToS]
    rw [Finset.sum_eq_single ⟨PP, hPP⟩]
    · rw [hdel PP hPP PP hPP, if_pos rfl, one_mul, ha]
    · intro b _ hb
      rw [hdel PP hPP b.1 b.2, if_neg (fun h => hb (Subtype.ext h)), zero_mul]
    · intro h; exact absurd (Finset.mem_attach _ _) h

end GlobalTheory.AdjRedOnto
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.LineZero

variable {D : D7}

theorem rat_mul_mem_latO_neg {V T T' : HSp D} {LS : Set (Fin V.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {LT' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)} {P : HeightOneSpectrum (𝓞 D.host.F) → Prop}
    (q : Matrix (Fin T'.rank) (Fin T.rank) D.host.E) (hq : ∀ t ∈ LT, q *ᵥ t ∈ LT') :
    ∀ x ∈ latO (negSp V) T LS LT P, rat q ⬝ x ∈ latO V T' LS (LT' : Set _) P := by
  intro x hx
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, hv, a, ha, s, hs, t, ht, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨α, hα, hv, a, ha, s, hs, -(q *ᵥ t), neg_mem (hq t ht), ?_⟩
    ext i j
    simp only [Matrix.mul_apply, rat, Matrix.map_apply, Matrix.of_apply]
    have e : ∀ (e : D.host.E) (u : AF D.host.F) (c : D.host.E), incA D e * (u ⊗ₜ[D.host.F] c) = u ⊗ₜ[D.host.F] (e * c) := by
      intro e u c
      show (Algebra.TensorProduct.includeRight e : AF D.host.F ⊗[D.host.F] D.host.E) * _ = _
      rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    simp only [e, ← TensorProduct.tmul_sum]
    congr 1
    have hX : ∑ k, star (s k) * (negSp V).gram k j = -∑ k, star (s k) * V.gram k j := by
      simp only [negSp_gram, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib]
    rw [hX]
    generalize (∑ k, star (s k) * V.gram k j) = X
    simp only [Matrix.mulVec, dotProduct, Pi.neg_apply, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  | zero => rw [Matrix.mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg]; exact neg_mem hx

theorem exists_vacG_lineLat_zero : OnStd fun {D} _ _ _ {G} W F => ∃ Φ₀, VacG W.ψ _ _ (lineLat F 0) Φ₀ ∧ Φ₀ ≠ 0 := by
  intro D hq T L μ0 hL sc G W M hM F hF
  have hq0 : ∀ t ∈ (G.Λ (.core 0) : Set (Fin (G.V (.core 0)).rank → D.host.E)),
      F.oz.qB *ᵥ t ∈ Submodule.span (𝓞 D.host.E) {F.ζ 0} := by
    intro t ht
    have ht' : t ∈ G.sp.dec0.lat (L.ΛY 0) fun _ => 1 := by rw [← G.sp.lat0]; exact ht
    obtain ⟨y, -, u, hu, rfl⟩ := ht'
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 (hu 0)
    have ha : G.sp.dec0.a *ᵥ u = u 0 • (F.oz.iB *ᵥ F.ζ 0) := by
      rw [hF.zB]
      funext i
      simp [Matrix.mulVec, dotProduct, mul_comm]
    rw [Matrix.mulVec_add, ha, Matrix.mulVec_smul, ← hF.zA, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, F.oz.qB_iA,
      F.oz.qB_iB, Matrix.one_mulVec, Matrix.zero_mulVec, zero_add, ← hr, algebraMap_smul]
    exact Submodule.smul_mem _ r (Submodule.mem_span_singleton_self _)
  have hLT : IsSelfDualC (negSp F.Lz) (Submodule.span (𝓞 D.host.E) {F.ζ 0}) := by
    have hs : Subsingleton (Fin F.Lz.rank) := by rw [F.rk]; infer_instance
    have hne : Nonempty (Fin F.Lz.rank) := ⟨⟨0, by rw [F.rk]; omega⟩⟩
    let B : Matrix (Fin F.Lz.rank) (Fin F.Lz.rank) D.host.E := Matrix.of fun i _ => F.ζ 0 i
    let f : Fin F.Lz.rank → Fin 1 := fun _ => 0
    have hiB : F.oz.iB * B = G.sp.dec0.a.submatrix id f := by
      refine Matrix.ext fun i j => ?_
      have := congrFun hF.zB i
      simp only [Matrix.mulVec, dotProduct] at this
      simp only [Matrix.mul_apply, B, Matrix.of_apply, Matrix.submatrix_apply, id, f]
      exact this
    have hB : Bᴴ * F.Lz.gram * B = 1 := by
      rw [← F.oz.isoB]
      have e : Bᴴ * (F.oz.iBᴴ * (G.V (.core 0)).gram * F.oz.iB) * B =
          (F.oz.iB * B)ᴴ * (G.V (.core 0)).gram * (F.oz.iB * B) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [e, hiB]
      refine (G.sp.dec0.gram_sub f f).trans (Matrix.ext fun i j => ?_)
      rw [Subsingleton.elim i j]
      simp [antiDiagonalSignGramMatrix, f]
    have hB' : B * (Bᴴ * F.Lz.gram) = 1 := mul_eq_one_comm.1 hB
    let Bg : GL (Fin F.Lz.rank) D.host.E := ⟨B, Bᴴ * F.Lz.gram, hB', hB⟩
    have hc : IsSelfDualC F.Lz (Formalism.L2.DIV.colLat Bg) :=
      GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal F.Lz Bg hB
    have hcs : Formalism.L2.DIV.colLat Bg = Submodule.span (𝓞 D.host.E) {F.ζ 0} := by
      unfold Formalism.L2.DIV.colLat
      congr 1
      ext v
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨j, rfl⟩; rfl
      · rintro rfl; exact ⟨Classical.arbitrary _, rfl⟩
    rw [hcs] at hc
    exact isSelfDualC_neg hc
  have hLS : IsSelfDualC (G.V (.core 1)) (G.Λ (.core 1)) := (G.sp.P_is 1 (by have := D.R.two_le_m; omega)).sd
  have hle : lineLat F 0 ≤ latO (G.V (.core 1)) (negSp F.Lz) (G.Λ (.core 1) : Set _)
      (Submodule.span (𝓞 D.host.E) {F.ζ 0} : Set _) (fun _ => True) := by
    intro b hb
    rw [lineLat] at hb
    have hb' : F.oz.jA ⬝ (0 : WO (G.V (.core 1)) (Yc D 0)) + F.oz.jB ⬝ b ∈ latCore G 0 := hb
    have e : b = rat F.oz.qB ⬝ (F.oz.jA ⬝ (0 : WO (G.V (.core 1)) (Yc D 0)) + F.oz.jB ⬝ b) := by
      rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
      change b = F.oz.pB ⬝ F.oz.jA ⬝ (0 : WO (G.V (.core 1)) (Yc D 0)) + F.oz.pB ⬝ F.oz.jB ⬝ b
      rw [OrthDec.pB_jA, OrthDec.pB_jB, Matrix.mul_zero, zero_add, Matrix.one_mul]
    rw [e]
    exact rat_mul_mem_latO_neg (V := G.V (.core 1)) F.oz.qB hq0 _ hb'.1
  exact GlobalTheory.AscFin.VacSub.exists_vacG_ne_zero D W.ψ W.ψ_std _ _ _ _ hLS hLT _ hle

end GlobalTheory.AscFin.LineZero
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_frame_conjugate_level_symmetricLevel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, IsGenericPsi R.Pg ψ0 → ∃ β₃ : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β₃ (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) ∧ ∀ κ : GA D (Yc D 0), (κ ∈ (iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2} ↔ κ ∈ levS (Yc D 0) β₃ (R.dat0 (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0))) ∧ (κ ∈ levS (Yc D 0) β₃ (R.dat0 (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0)) → star (X.chi2 ((iotaX X h).toMulEquiv κ).2) = levChi (Yc D 0) β₃ (R.dat0 (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0)) κ) := by
  first | exact @GlobalTheory.SeeConj.exists_frame_symLevel | exact GlobalTheory.SeeConj.exists_frame_symLevel | (intros; apply GlobalTheory.SeeConj.exists_frame_symLevel <;> assumption)
end
