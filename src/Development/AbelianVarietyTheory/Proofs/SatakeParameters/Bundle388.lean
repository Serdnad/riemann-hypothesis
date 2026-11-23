module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
public import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacteristicFunctionIntegralApply
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalCongruenceLevelContained
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle086
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RankTw

open GlobalTheory.RowCopy GlobalTheory.NRows

theorem used_loc (D : D7) (i : D.nd.Loc) : D.nd.mu i = D.what₂.mu0 ∨ ∃ w, D.nd.mu i = D.what₂.muAt w :=
  Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩

theorem lamPos_of_used {D : D7} (h : LamUsed D) {μ} (hμ : μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) {j : ℕ}
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : _root_.GlobalTheory.RowCopy.LamPos D μ j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  exact h μ hμ ⟨k, by omega⟩

theorem lamLoc {D : D7} (h : LamUsed D) (i : D.nd.Loc) : _root_.GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i) :=
  lamPos_of_used h (used_loc D i) (D.nd.j_range i).1 (D.nd.j_range i).2

theorem up_injective {D : D7} {μ} {j : ℕ} (h : _root_.GlobalTheory.RowCopy.LamPos D μ j) (hI : DirectSum.IsInternal (D.what₂.isot j)) :
    Function.Injective (D.what₂.thetaT μ j) := by
  have hs : Function.Surjective (D.what₂.thetaP μ j ∘ₗ D.what₂.thetaT μ j) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hI.submodule_iSup_eq_top, iSup_le_iff]
    intro σ f hf
    by_cases h0 : D.what₂.isot j σ = ⊥
    · rw [h0] at hf
      rw [(Submodule.mem_bot ℂ).1 hf]
      exact zero_mem _
    · have hl : ((D.what₂.lamP μ j σ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ((h σ).2 h0).ne'
      refine ⟨((D.what₂.lamP μ j σ : ℝ) : ℂ)⁻¹ • f, ?_⟩
      rw [map_smul, LinearMap.comp_apply, (h σ).1 f hf, smul_smul, inv_mul_cancel₀ hl, one_smul]
  have hi := LinearMap.injective_iff_surjective.2 hs
  rw [LinearMap.coe_comp] at hi
  exact hi.of_comp

theorem rank_of {D : D7} (hI : SumRepresentations.adm8 D) (h : LamUsed D) (L : SizeData₂ D) : TwistedPlaces.adm3 L := by
  intro j hj w hw
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  have e : D.what₂.muTw w = D.what₂.muAt w := ((D.what₂.muAt_or w).resolve_left hw).symm
  have a := up_injective (lamPos_of_used h (Or.inr ⟨w, e⟩) h1 h2) (hI j h1 h2)
  have b := up_injective (lamPos_of_used h (Or.inl rfl) h1 h2) (hI j h1 h2)
  unfold SizeData₂.zeroSpaceRankAtPlace SizeData₂.dZ0 Rows.Data.Zj
  rw [LinearMap.finrank_range_of_inj a, LinearMap.finrank_range_of_inj b]

theorem main : ∀ D : D7, Formalism.MainNotions.SumRepresentations.adm8 D → GlobalTheory.NRows.LamUsed D →
    (∀ i : D.nd.Loc, GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i)) ∧ ∀ L : SizeData₂ D, Formalism.MainNotions.TwistedPlaces.adm3 L :=
  fun _ hI h => ⟨GlobalTheory.RankTw.lamLoc h, GlobalTheory.RankTw.rank_of hI h⟩

end GlobalTheory.RankTw

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct ComplexOrder
open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace GlobalTheory.ThetaFormV

open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR GlobalTheory.ThetaTri
open scoped Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Frame

variable {D : D7} {V : HSp D} {n : ℕ}

theorem fin_preF (PV : principalLevelFrame.RowPsi V n) (k : Bridge.Gf V) :
    (finHom V).rangeRestrict (PV.ψ (preF PV k)) = k := by
  have hex : ∃ κ, (finHom V).rangeRestrict (PV.ψ κ) = k := by
    obtain ⟨κ, hκ, e⟩ := Formalism.IndefR.Eqv.Act.exists_finLift V k
    obtain ⟨h, rfl⟩ := PV.onto κ hκ
    exact ⟨h, Subtype.ext e⟩
  unfold preF
  rw [dite_eq_left hex]
  exact hex.choose_spec

theorem preF_fin (PV : principalLevelFrame.RowPsi V n) (x : Formalism.AUTREP.GAf D.host.E n) :
    preF PV ((finHom V).rangeRestrict (PV.ψ x)) = x := by
  apply PV.inj
  have e1 : finHom V (PV.ψ (preF PV ((finHom V).rangeRestrict (PV.ψ x)))) = finHom V (PV.ψ x) :=
    congrArg Subtype.val (fin_preF PV _)
  refine inv_mul_eq_one.1 (GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V
    ((GfC V).mul_mem ((GfC V).inv_mem (PV.into _)) (PV.into _)) ?_)
  show finHom V _ = 1
  rw [map_mul, map_inv, e1, inv_mul_cancel]

theorem preF_mul (PV : principalLevelFrame.RowPsi V n) (k₁ k₂ : Bridge.Gf V) :
    preF PV (k₁ * k₂) = preF PV k₁ * preF PV k₂ := by
  have h := preF_fin PV (preF PV k₁ * preF PV k₂)
  rwa [map_mul, map_mul, fin_preF, fin_preF] at h

theorem ext_apply (c : CoefA V) (f : Bridge.Gf V → c.W) (h : GA D V) :
    c.ext f h = c.ρ h⁻¹ (f ((finHom V).rangeRestrict h)) := rfl

theorem mem_adForms_one (c : CoefA V) (f : Bridge.Gf V → c.W)
    (hf : ∀ γ ∈ GQ V, ∀ k, f ((finHom V).rangeRestrict γ * k) = c.ρ γ (f k))
    (J : Subgroup (Bridge.Gf V)) (hJ : ∀ q ∈ J, ∀ k, f (k * q) = f k) :
    f ∈ Bridge.AdForms ((finHom V).rangeRestrict.comp (GQ V).subtype) (c.ρ.comp (GQ V).subtype) J 1 := by
  intro γ h k
  have e1 := hJ k k.2 ((finHom V).rangeRestrict (γ : GA D V) * h)
  have e2 := hf γ γ.2 h
  simp only [MonoidHom.one_apply, Units.val_one, one_smul, MonoidHom.comp_apply, Subgroup.coe_subtype]
  exact e1.trans e2

end Frame

section Forms

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {P : Pin hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}

end Forms

section Main

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {P : Pin hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}

end Main

theorem eventually_cong_preF {D : D7} {V : HSp D} {n : ℕ} (PV : principalLevelFrame.RowPsi V n)
    (hF : D.host.F = maximalRealSubfield D.host.E) (hstd : GlobalTheory.NJoin.StdFrame hF PV) {N : ℕ} (hN : 0 < N) :
    ∀ᶠ κ in 𝓝 (1 : GA D V), NG.Cong D.host.E n N (preF PV ((finHom V).rangeRestrict κ)) := by
  obtain ⟨N', hN', himg⟩ := GlobalTheory.LatCongImage.finCong_mem_levN D V n PV hF hstd N hN
  filter_upwards [GlobalTheory.Member.PrincLevel.finCong_mem_nhds V hN'] with κ hκ
  obtain ⟨κ', hκ', e⟩ := Formalism.IndefR.Eqv.Act.exists_finLift V ((finHom V).rangeRestrict κ)
  have hc : GlobalTheory.Member.FinCong V N' κ' := by
    intro z hz
    have e' : finHom V κ' = finHom V κ := e
    rw [e']
    exact hκ z hz
  obtain ⟨x, hx, hxe⟩ := himg κ' hκ' hc
  have e2 : (finHom V).rangeRestrict κ = (finHom V).rangeRestrict (PV.ψ x) := by
    rw [hxe]; exact (Subtype.ext e).symm
  rw [e2, GlobalTheory.ThetaFormV.preF_fin]
  exact hx

section Cont

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {P : Pin hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}

end Cont

end GlobalTheory.ThetaFormV

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ThetaTri
open scoped TensorProduct
open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ThetaLoc Formalism.L2.Theta

theorem thetaKO_act {D : D7} {V W : Formalism.BasicNotions.TH.HSp D}
    (om : Formalism.L2.Theta.GA D V × Formalism.L2.Theta.GA D W →* Module.End ℂ (WO V W → ℂ))
    (h' : Formalism.L2.Theta.GA D V) (g' : Formalism.L2.Theta.GA D W) (p : Formalism.L2.Theta.GA D V × Formalism.L2.Theta.GA D W)
    (f : WO V W → ℂ) : thetaKO om h' g' (om p f) = thetaKO om (h' * p.1) (g' * p.2) f := by
  simp only [thetaKO]
  rw [← Module.End.mul_apply, ← map_mul]
  rfl

theorem fin_frame_surj {D : D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n)
    (k : ↥(Formalism.IndefR.Bridge.Gf V)) : ∃ y, (Formalism.L2.Theta.finHom V).rangeRestrict (PV.ψ y) = k := by
  obtain ⟨g, hg, rfl⟩ := GlobalTheory.SplitHeckeAdj.fin_lift V k
  obtain ⟨y, rfl⟩ := PV.onto g hg
  exact ⟨y, rfl⟩

theorem preF_frame {D : D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n)
    (y : Formalism.AUTREP.GAf D.host.E n) : preF PV ((Formalism.L2.Theta.finHom V).rangeRestrict (PV.ψ y)) = y := by
  classical
  have h : ∃ x, (Formalism.L2.Theta.finHom V).rangeRestrict (PV.ψ x) = (Formalism.L2.Theta.finHom V).rangeRestrict (PV.ψ y) :=
    ⟨y, rfl⟩
  unfold preF
  rw [dite_eq_left h]
  exact PV.inj (GlobalTheory.SplitHeckeAdj.fin_inj V (PV.into _) (PV.into _) h.choose_spec)

theorem preF_mul {D : D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n)
    (k : ↥(Formalism.IndefR.Bridge.Gf V)) (y : Formalism.AUTREP.GAf D.host.E n) :
    preF PV (k * (Formalism.L2.Theta.finHom V).rangeRestrict (PV.ψ y)) = preF PV k * y := by
  obtain ⟨z, rfl⟩ := fin_frame_surj PV k
  rw [← map_mul, ← map_mul, preF_frame, preF_frame]

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {P : Pin hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}

theorem eW_cast_symm_wt (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (h' : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) (γ : GA D (Vc D j))
    (hγ : γ ∈ GQ (Vc D j)) (he : finHom (Vc D j) γ = finHom (Vc D j) ((A.PV j).ψ ((A.a j)⁻¹ * h' * A.a j)))
    (k : ℕ) (hk : j.1 + 1 = k) (p1 : 1 ≤ k) (p2 : k ≤ D.R.m) (w : (P.M (D.nd.mu i) k p1 p2).wt.W) :
    (Eq.ndrec (motive := fun k => (p1 : 1 ≤ k) → (p2 : k ≤ D.R.m) →
        (X.R.cV j).W ≃ₗ[ℂ] (P.M (D.nd.mu i) k p1 p2).wt.W) (fun _ _ => A.eW (D.nd.mu i) hμ j) hk p1 p2).symm
        ((P.M (D.nd.mu i) k p1 p2).wt.ρ h' w) =
      (X.R.cV j).ρ γ ((Eq.ndrec (motive := fun k => (p1 : 1 ≤ k) → (p2 : k ≤ D.R.m) →
        (X.R.cV j).W ≃ₗ[ℂ] (P.M (D.nd.mu i) k p1 p2).wt.W) (fun _ _ => A.eW (D.nd.mu i) hμ j) hk p1 p2).symm w) := by
  subst hk
  apply (A.eW _ hμ j).injective
  simp only [LinearEquiv.apply_symm_apply]
  rw [A.wt _ hμ j h' γ hγ he]
  simp

theorem eWloc_symm_wt (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (h' : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) (γ : GA D (Vc D j))
    (hγ : γ ∈ GQ (Vc D j)) (he : finHom (Vc D j) γ = finHom (Vc D j) ((A.PV j).ψ ((A.a j)⁻¹ * h' * A.a j)))
    (w : (P.M.loc i).wt.W) :
    (eWloc A i j hj hμ).symm ((P.M.loc i).wt.ρ h' w) = (X.R.cV j).ρ γ ((eWloc A i j hj hμ).symm w) :=
  eW_cast_symm_wt A i j hμ h' γ hγ he (D.nd.j i) hj _ _ w

theorem fV_rt (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (hcv : (X.R.cV j).Is) (h : Formalism.AUTREP.GAf D.host.E D.R.nV)
    (F F' : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ))
    (hF : (F' : Formalism.AUTREP.GAf D.host.E D.R.nV → (P.M.loc i).wt.W) = NG.rt D.host.E D.R.nV h F)
    (x : GA D (Vc D j)) : fV A i j hj hμ F' x = fV A i j hj hμ F (x * (A.PV j).ψ h) := by
  show (X.R.cV j).ext _ x = (X.R.cV j).ext _ (x * (A.PV j).ψ h)
  rw [GlobalTheory.DefLiftHecke.ext_mul _ hcv _ ((A.PV j).into h) x]
  show (X.R.cV j).ρ x⁻¹ _ = _
  simp only [LinearMap.coe_mk, AddHom.coe_mk, preF_mul, hF, NG.rt, mul_assoc]

theorem fV_rat (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ))
    (γ : GA D (Vc D j)) (hγ : γ ∈ GQ (Vc D j)) (x : GA D (Vc D j)) :
    fV A i j hj hμ F (γ * x) = fV A i j hj hμ F x := by
  obtain ⟨y, hy⟩ := fin_frame_surj (A.PV j) ((finHom (Vc D j)).rangeRestrict γ)
  obtain ⟨z, hz⟩ := fin_frame_surj (A.PV j) ((finHom (Vc D j)).rangeRestrict x)
  have hh' : A.a j * y * (A.a j)⁻¹ ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV := by
    refine (A.rat j _).2 ⟨γ, hγ, ?_⟩
    have : (A.a j)⁻¹ * (A.a j * y * (A.a j)⁻¹) * A.a j = y := by group
    rw [this]
    exact (congrArg Subtype.val hy).symm
  have he : finHom (Vc D j) γ = finHom (Vc D j) ((A.PV j).ψ ((A.a j)⁻¹ *
      ((⟨_, hh'⟩ : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) : Formalism.AUTREP.GAf D.host.E D.R.nV) * A.a j)) := by
    have : (A.a j)⁻¹ * (A.a j * y * (A.a j)⁻¹) * A.a j = y := by group
    simp only [this]
    exact (congrArg Subtype.val hy).symm
  show (X.R.cV j).ρ (γ * x)⁻¹ ((eWloc A i j hj hμ).symm ((F : Formalism.AUTREP.GAf D.host.E D.R.nV → (P.M.loc i).wt.W)
      (A.a j * preF (A.PV j) ((finHom (Vc D j)).rangeRestrict (γ * x))))) =
    (X.R.cV j).ρ x⁻¹ ((eWloc A i j hj hμ).symm ((F : Formalism.AUTREP.GAf D.host.E D.R.nV → (P.M.loc i).wt.W)
      (A.a j * preF (A.PV j) ((finHom (Vc D j)).rangeRestrict x))))
  have hprod : (finHom (Vc D j)).rangeRestrict γ * (finHom (Vc D j)).rangeRestrict x =
      (finHom (Vc D j)).rangeRestrict ((A.PV j).ψ (y * z)) :=
    (congrArg₂ (· * ·) hy.symm hz.symm).trans
      ((map_mul (finHom (Vc D j)).rangeRestrict _ _).symm.trans
        (congrArg (finHom (Vc D j)).rangeRestrict (map_mul (A.PV j).ψ y z).symm))
  have key : preF (A.PV j) ((finHom (Vc D j)).rangeRestrict (γ * x)) = y * z :=
    (congrArg (preF (A.PV j)) ((map_mul (finHom (Vc D j)).rangeRestrict γ x).trans hprod)).trans (preF_frame _ _)
  have hz' : preF (A.PV j) ((finHom (Vc D j)).rangeRestrict x) = z :=
    (congrArg (preF (A.PV j)) hz.symm).trans (preF_frame _ _)
  rw [key, hz']
  have e1 : A.a j * (y * z) = (A.a j * y * (A.a j)⁻¹) * (A.a j * z) := by group
  rw [e1, F.2.1 ⟨_, hh'⟩ (A.a j * z), eWloc_symm_wt A i j hj hμ ⟨_, hh'⟩ γ hγ he, _root_.mul_inv_rev,
    map_mul, Module.End.mul_apply, ← Module.End.mul_apply ((X.R.cV j).ρ γ⁻¹), ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply]

theorem lift_actM {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} {Sp : D.what₂.Tau → Formalism.BasicNotions.TH.SPar}
    (PW : Formalism.IndefR.principalLevelFrame.RowPsi V n) (M : Formalism.IndefR.Mult.DSModel V Sp) (g : Formalism.AUTREP.GAf D.host.E n)
    (T : Formalism.IndefR.Mult.MMap M) (u : PiTensorProduct ℂ fun τ => ↥(M.sm τ)) (x : GA D V) :
    PiTensorProduct.lift (Formalism.IndefR.principalLevelFrame.actM PW M g T) u x = PiTensorProduct.lift T u (x * PW.ψ g) := by
  induction u using PiTensorProduct.induction_on with
  | smul_tprod r f => simp [PiTensorProduct.lift.tprod, Formalism.IndefR.principalLevelFrame.actM_apply]
  | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb]

theorem lift_left {V : Formalism.BasicNotions.TH.HSp D} {Sp : D.what₂.Tau → Formalism.BasicNotions.TH.SPar}
    (M : Formalism.IndefR.Mult.DSModel V Sp) (T : Formalism.IndefR.Mult.MMap M)
    (hT : ∀ v, ∀ γ ∈ GQ V, ∀ x, T v (γ * x) = T v x) (u : PiTensorProduct ℂ fun τ => ↥(M.sm τ))
    (γ : GA D V) (hγ : γ ∈ GQ V) (x : GA D V) :
    PiTensorProduct.lift T u (γ * x) = PiTensorProduct.lift T u x := by
  induction u using PiTensorProduct.induction_on with
  | smul_tprod r f => simp [PiTensorProduct.lift.tprod, hT f γ hγ x]
  | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb]

def LeftInvM {V : Formalism.BasicNotions.TH.HSp D} {Sp : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} (M : Formalism.IndefR.Mult.DSModel V Sp) :
    Submodule ℂ (Formalism.IndefR.Mult.MMap M) where
  carrier := {T | ∀ v, ∀ γ ∈ GQ V, ∀ x, T v (γ * x) = T v x}
  add_mem' := by
    intro T T' hT hT' v γ hγ x
    simp only [MultilinearMap.add_apply, Pi.add_apply, hT v γ hγ x, hT' v γ hγ x]
  zero_mem' := by intro v γ hγ x; rfl
  smul_mem' := by
    intro c T hT v γ hγ x
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, hT v γ hγ x]

theorem minf_le_leftInv {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} {Sp : D.what₂.Tau → Formalism.BasicNotions.TH.SPar}
    (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (PW : Formalism.IndefR.principalLevelFrame.RowPsi V n) (M : Formalism.IndefR.Mult.DSModel V Sp) :
    Formalism.IndefR.principalLevelFrame.Minf θ PW M ≤ LeftInvM M := by
  refine iSup_le fun N => Submodule.span_le.2 fun T hT v γ hγ x => ?_
  exact (hT.aut v).left γ hγ x

theorem yv_apply {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y)
    (y : ↥Y.C) (x : GA D (Wc D j)) :
    yv hc y x = PiTensorProduct.lift (eC hc (y : Y.A)) (PiTensorProduct.map
      (fun τ => (lowT (X.R.MW j (sg0 D X.A)) τ).subtype) (kUnit (X.R.MW j (sg0 D X.A)))) x := rfl

theorem yv_rt {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y)
    (g : Formalism.AUTREP.GAf D.host.E D.R.r) (y y' : ↥Y.C) (hy : (y' : Y.A) = Y.ρ g y) (x : GA D (Wc D j)) :
    yv hc y' x = yv hc y (x * (X.PW j).ψ g) := by
  have he : eC hc (y' : Y.A) = Formalism.IndefR.principalLevelFrame.actM (X.PW j) (X.R.MW j (sg0 D X.A)) g (eC hc (y : Y.A)) := by
    rw [hy]; exact (Classical.choose_spec (Classical.choose_spec hc)).2.2.2.1 g y
  rw [yv_apply, yv_apply, he, lift_actM]

theorem yv_rat {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y)
    (y : ↥Y.C) (γ : GA D (Wc D j)) (hγ : γ ∈ GQ (Wc D j)) (x : GA D (Wc D j)) :
    yv hc y (γ * x) = yv hc y x := by
  have hm : eC hc (y : Y.A) ∈ LeftInvM (X.R.MW j (sg0 D X.A)) := by
    apply minf_le_leftInv X.R.θ (X.PW j)
    rw [← (Classical.choose_spec (Classical.choose_spec hc)).2.2.1]
    exact Submodule.mem_map_of_mem y.2
  rw [yv_apply, yv_apply]
  exact lift_left _ _ hm _ γ hγ x

end GlobalTheory.ThetaTri

end
end
