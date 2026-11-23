module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle026
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle027
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle021
public import Formalism.LocalToGlobal.HermitianForms.Bundle011
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle371
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle321
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle383
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2532
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2516
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle316
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongruenceLevelMapsIntoLatticeCongruence
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle078
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle086
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.AllTuples

theorem joints_all_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (C : ColsTiedSym (I.rec7 l Z)) (full : ColsFullS C) (g : Formalism.L2.G.GroupCompatibilityAll (I.rec7 l Z) hT ex.cmp), I.IsTw → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → ex.errX.piT = X.piT → I.StdKer l Z t → GlobalTheory.Pdv.StdRd I l Z t → (∀ (u : B.Word) (a : I.ι) (i : ℕ) (c : ((I.rec7 l Z).chTw u a).cls i), (t.rd u a).pin i c ↔ (i + 1 ≤ B.R.m ∨ ∃ d, OverRow (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d ((I.stp u a i).rep c).1.1)) → I.StdC l Z C → I.StdDt l Z full.1.base.dt → g.herm = full.1.to0 → (g.forms = fun u => (C.forms u).to0) → (∀ z : (I.rec7 l Z).Dt, ∃ r : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL r = (((I.rec7 l Z).chiD z : ℂˣ) : ℂ)) → G.LatTied hT Gi Gl → (∀ a : I.ι, GlobalTheory.TwV.JointsAt t a) ∧ ∀ u, ex.tw.e0 u (I.rec7 l Z).what₂.mu0 = ex.tw.eMu0 u 0 (Nat.zero_le _) := by
  intro B X I hOk hP l Z l0 L hT Gi Gl K Y cX ex t C full g hTw hJ htw hpi hK hRd hpin hC hDt hh hf hchi hLat
  refine ⟨fun a => ?_, fun u => ?_⟩
  · exact GlobalTheory.T.jointsAtSplitUnramifiedPlaces_of_chainCharts t a hLat (fun u =>
      GlobalTheory.T.trueColumn_exists_chainCharts_kernelData_forms I hOk hP l Z l0 L hT Gi Gl K Y cX ex t C full g hTw hJ htw hpi hK hRd hpin hC hDt hh hf hchi u a)
  · rw [htw]
    exact GlobalTheory.T.tw_e0_mu0_eq_eMu0_zero I hOk hP l Z l0 u

end GlobalTheory.TwU.AllTuples
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

theorem _root_.GlobalTheory.T.jointData_at_p_and_adelicDatum_nonempty : Lt.CurveEx → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), Nonempty (J.At std) := by
  first | exact @GlobalTheory.TwV.joint_at_nonempty | exact GlobalTheory.TwV.joint_at_nonempty | (intros; apply GlobalTheory.TwV.joint_at_nonempty <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TypeNZJoin

open Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.RecTie



theorem inj_at {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    (hT : ∀ j t, GlobalTheory.DownLift.TypeNZ X.R j t) (i : D.nd.Loc) (hS : GlobalTheory.NJoin.EigString X i)
    (hG : GlobalTheory.NJoin.EigGood X i) (hμ : Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (x : D.nd.X i) (hx : x ∈ ZgoodN D.nd D.naut i) (f : D.what₂.Mt (D.nd.mu i) (j.1 + 1))
    (hf : (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x)
    (h0 : D.what₂.thetaP (D.nd.mu i) (j.1 + 1) f = 0) : f = 0 := by
  have hC := X.given.core
  have hfm := (X.IL.jMt _ hμ j f).2
  obtain ⟨y, hy⟩ : ∃ y, (LinearEquiv.ofInjective _ (X.hinj j (X.tupT (D.nd.mu i)))).symm
      ⟨((X.IL.jMt _ hμ j f).1 : Formalism.L2.Theta.GA D (Vc D j) → (X.R.cV j).W), hfm.1⟩ = y := ⟨_, rfl⟩
  have hyf : X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f := by
    rw [← hy]
    exact congrArg Subtype.val ((LinearEquiv.ofInjective _ (X.hinj j (X.tupT (D.nd.mu i)))).apply_symm_apply _)
  have hthG : X.R.thG j (X.tupT (D.nd.mu i)) y = 0 := by
    have hM := GlobalTheory.ThetaLevelP.thF_mem_level X.R X.F hC.lev hC.models hC.thP X.R.hv0 false j (X.tupT (D.nd.mu i)) y
      (by rw [hyf]; exact hfm.2)
    obtain ⟨w, hw1, hw2, hw3⟩ := X.fire.2.1 (D.nd.mu i) hμ j f
    have hw' : PiTensorProduct.lift (X.R.thF j (X.tupT (D.nd.mu i)) y) ∘ₗ
        (toLiftReal X.R X.F X.tupT X.hm X.hTop X.hinj).embK j =
        (toLiftReal X.R X.F X.tupT X.hm X.hTop X.hinj).thC _ j (X.IL.jMt _ hμ j f) := by
      rw [← hy]; rfl
    have hwe : w = PiTensorProduct.lift (X.R.thF j (X.tupT (D.nd.mu i)) y) := by
      refine sub_eq_zero.1 (X.fire.2.2 j _ (sub_mem hw1 (Submodule.mem_map_of_mem hM)) ?_)
      exact (LinearMap.sub_comp _ _ _).trans (by rw [hw2]; exact sub_eq_zero.2 hw'.symm)
    have hth := X.recR.tied.lift.theta (D.nd.mu i) hμ j f w (X.fire.1 _ hμ j) hw1 hw2 hw3
    rw [h0, map_zero, ZeroMemClass.coe_zero, hwe] at hth
    have h2 : PiTensorProduct.lift (postOn _ (X.R.eWf j (sg0 D X.A)) (X.R.thF j (X.tupT (D.nd.mu i)) y)) = 0 := by
      rw [GlobalTheory.ThetaFireLift.lift_postOn]; exact hth.symm
    have h3 : (X.R.HW j (sg0 D X.A)).e (X.R.thG j (X.tupT (D.nd.mu i)) y) = 0 := by
      rw [hC.thP.thG]; exact (LinearEquiv.map_eq_zero_iff _).1 h2
    exact (hC.models.HW j _).1 (h3.trans (map_zero _).symm)
  have hy0 : y = 0 := by
    by_contra hne
    obtain ⟨h, hh⟩ := GlobalTheory.LiftOntoCompare.exists_opsV hC.lev hC.models j (X.tupT (D.nd.mu i))
    obtain ⟨s, hs1, hs2⟩ := hS hμ j hj x hx f hf y hyf hne h hh
    exact hne (hT j _ h hh s hs1 y hs2 (hG hμ j hj x hx f hf y hyf) hthG)
  have h4 : X.IL.jMt _ hμ j f = 0 := by
    apply Subtype.ext
    show X.fn hμ j f = 0
    rw [← hyf, hy0, map_zero]
  exact (LinearEquiv.map_eq_zero_iff _).1 h4

theorem of_cast {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) (S : Submodule ℂ (D.what₂.Mt μ b))
    (H : ∀ f : D.what₂.Mt μ a, (h ▸ f : D.what₂.Mt μ b) ∈ S → D.what₂.thetaP μ a f = 0 → f = 0) :
    ∀ F ∈ S, D.what₂.thetaP μ b F = 0 → F = 0 := by
  subst h
  exact H

end GlobalTheory.TypeNZJoin
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.SplitComp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem exists_integralSection_splitPlace_componentMap_cast {E : Type} [Field E] [NumberField E] [IsCMField E] (F1 : Subfield E)
    (hF : F1 = maximalRealSubfield E) (sp : SplitPlace E) :
    ∃ sec : sp.v.adicCompletion (maximalRealSubfield E) → FiniteAdeleRing (𝓞 F1) F1 ⊗[F1] E,
      (∀ t, sp.proj (Formalism.IndefR.principalLevelFrame.tensCastR hF (sec t)) = t) ∧
      (∀ t ∈ sp.v.adicCompletionIntegers (maximalRealSubfield E),
        sec t ∈ AddSubgroup.closure {y | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F1, ∃ x : 𝓞 E, y = a ⊗ₜ[F1] (x : E)}) ∧
      (∀ x ∈ AddSubgroup.closure {y | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F1, ∃ x : 𝓞 E, y = a ⊗ₜ[F1] (x : E)},
        sp.proj (Formalism.IndefR.principalLevelFrame.tensCastR hF x) ∈ sp.v.adicCompletionIntegers (maximalRealSubfield E)) ∧
      ∀ x : E, sp.proj (Formalism.IndefR.principalLevelFrame.tensCastR hF ((1 : FiniteAdeleRing (𝓞 F1) F1) ⊗ₜ[F1] x)) = sp.i x := by
  classical
  subst hF
  have hc : ∀ (a : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) (x : E),
      Formalism.IndefR.principalLevelFrame.tensCastR (rfl : maximalRealSubfield E = maximalRealSubfield E)
        (a ⊗ₜ[maximalRealSubfield E] x) = x ⊗ₜ[maximalRealSubfield E] a := fun a x => rfl
  have hp : ∀ (a : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) (x : E),
      sp.proj (x ⊗ₜ[maximalRealSubfield E] a) = sp.i x * a sp.v := fun a x => rfl
  refine ⟨fun t => singleV (maximalRealSubfield E) sp.v t ⊗ₜ[maximalRealSubfield E] (1 : E), ?_, ?_, ?_, ?_⟩
  · intro t
    rw [hc, hp, map_one, one_mul]
    exact RestrictedProduct.single_eq_same _ _ _
  · intro t ht
    apply AddSubgroup.subset_closure
    refine ⟨singleV (maximalRealSubfield E) sp.v t, ?_, 1, by simp⟩
    intro w
    show (singleV (maximalRealSubfield E) sp.v t) w ∈ _
    by_cases h : w = sp.v
    · subst h
      have e : (singleV (maximalRealSubfield E) sp.v t) sp.v = t := RestrictedProduct.single_eq_same _ _ _
      rw [e]
      exact ht
    · have e : (singleV (maximalRealSubfield E) sp.v t) w = 0 := RestrictedProduct.single_eq_of_ne _ _ h
      rw [e]
      exact zero_mem _
  · intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, z, rfl⟩ := hy
      rw [hc, hp]
      refine mul_mem ?_ (ha sp.v)
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (sp.split_le_one z)
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add (f := _), map_add (f := _)]
      exact add_mem hy hz
    | neg y _ hy =>
      rw [map_neg, map_neg]
      exact neg_mem hy
  · intro x
    rw [hc, hp]
    show sp.i x * 1 = sp.i x
    exact mul_one _

theorem proj_tensCast_section : ∀ (D : D7) (sp : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E),
    ∃ sec : sp.v.adicCompletion (maximalRealSubfield D.host.E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
      (∀ t, sp.proj (GlobalTheory.NJoin.tensCast hF (sec t)) = t) ∧
      (∀ t ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E), sec t ∈ Formalism.L2.Theta.intAE D) ∧
      (∀ x ∈ Formalism.L2.Theta.intAE D,
        sp.proj (GlobalTheory.NJoin.tensCast hF x) ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) ∧
      ∀ x : D.host.E, sp.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D (Formalism.L2.Theta.incA D x))) = sp.i x := by
  intro D sp hF
  obtain ⟨sec, h1, h2, h3, h4⟩ := exists_integralSection_splitPlace_componentMap_cast D.host.F hF sp
  refine ⟨sec, h1, h2, h3, fun x => ?_⟩
  have e : Formalism.L2.Theta.finPart D (Formalism.L2.Theta.incA D x) = (1 : Af D.host.F) ⊗ₜ[D.host.F] x := by
    simp [Formalism.L2.Theta.finPart, Formalism.L2.Theta.incA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.map_tmul]
  rw [e]
  exact h4 x

end GlobalTheory.SplitComp
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EigSplit

open Formalism.IndefR.Links in
theorem cast_add {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) (x y : D.what₂.Mt μ a) :
    (h ▸ (x + y) : D.what₂.Mt μ b) = (h ▸ x : D.what₂.Mt μ b) + (h ▸ y : D.what₂.Mt μ b) := by
  subst h; rfl

theorem cast_zero {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) :
    (h ▸ (0 : D.what₂.Mt μ a) : D.what₂.Mt μ b) = 0 := by
  subst h; rfl

theorem cast_inj {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) {x y : D.what₂.Mt μ a}
    (hxy : (h ▸ x : D.what₂.Mt μ b) = (h ▸ y : D.what₂.Mt μ b)) : x = y := by
  subst h; exact hxy

theorem cast_symm {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) (m : D.what₂.Mt μ b) :
    (h ▸ (h.symm ▸ m : D.what₂.Mt μ a) : D.what₂.Mt μ b) = m := by
  subst h; rfl

theorem fn_zero {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) : X.fn hμ j 0 = 0 := by
  unfold GlobalTheory.NJoin.RealAt.fn; simp; rfl

theorem fn_add {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (x y : D.what₂.Mt μ (j.1 + 1)) :
    X.fn hμ j (x + y) = X.fn hμ j x + X.fn hμ j y := by
  unfold GlobalTheory.NJoin.RealAt.fn; simp; rfl

theorem rep_mem {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (Pp : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ)
    {γ : Formalism.L2.Theta.GA D V} (hγ : γ ∈ GlobalTheory.Hk3.rep V Pp d) : γ ∈ Formalism.L2.Theta.GfC V := by
  unfold GlobalTheory.Hk3.rep at hγ
  split_ifs at hγ with hl
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hR⟩ := hl.choose_spec
    exact (hR.1 γ hγ).1
  · simp at hγ

theorem twist_eq {G H W : Type*} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] (ρ : G →* Module.End ℂ W)
    (rr : G →* H) (F : H → W) (g γ : G) (h1 : ρ γ⁻¹ = 1) :
    ρ (g * γ)⁻¹ (F (rr (g * γ))) = ρ g⁻¹ (F (rr g * rr γ)) := by
  rw [mul_inv_rev, map_mul, map_mul, h1, one_mul]

theorem sum_single_one {W : Type*} [AddCommGroup W] [Module ℂ W] (d : List ℤ) (S : List ℤ → W) :
    (Finsupp.single d (1 : ℂ)).sum (fun d z => z • S d) = S d := by
  rw [Finsupp.sum_single_index (h := fun d (z : ℂ) => z • S d) (zero_smul ℂ _), one_smul]

theorem transport {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    (j : Fin D.R.m) (t : X.T) (h : DIV.Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (X.R.HV j t).H)
    (hh : GlobalTheory.Hk3.IsOpsV X.R j t h) (Pp : DIV.Pl D.host.E) (hG : GlobalTheory.Hk3.Good X.R t Pp) (d : List ℤ)
    (y : (X.R.HV j t).H) (c : ℂ)
    (hc : ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.R.extV j t y (g * γ) = c • X.R.extV j t y g) :
    h Pp (Finsupp.single d 1) y = c • y := by
  have hcv := (X.given.core.models.cV j).1
  apply X.hinj j t
  funext g
  have e1 : X.R.extV j t (c • y) g = c • X.R.extV j t y g :=
    congrFun ((X.R.extV j t).map_smul c y) g
  have e3 : ∀ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.R.extV j t y (g * γ) =
      (X.R.cV j).ρ g⁻¹ ((X.R.HV j t).e y ((Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict g *
        (Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict γ)) := by
    intro γ hγ
    exact twist_eq (X.R.cV j).ρ (Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict ((X.R.HV j t).e y) g γ
      (hcv γ⁻¹ (inv_mem (rep_mem _ Pp d hγ)))
  have e2 : X.R.extV j t (h Pp (Finsupp.single d 1) y) g =
      ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.R.extV j t y (g * γ) := by
    refine Eq.trans ?_ (Finset.sum_congr rfl e3).symm
    show (X.R.cV j).ρ g⁻¹ ((X.R.HV j t).e (h Pp (Finsupp.single d 1) y)
      ((Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict g)) = _
    refine Eq.trans (congrArg ((X.R.cV j).ρ g⁻¹) (congrFun (hh Pp hG (Finsupp.single d 1) y)
      ((Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict g))) ?_
    unfold GlobalTheory.Hk3.hkF
    exact (congrArg ((X.R.cV j).ρ g⁻¹) (sum_single_one d _)).trans (map_sum ((X.R.cV j).ρ g⁻¹) _ _)
  exact e2.trans ((hc g).trans e1.symm)

theorem eig_zero {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (Pp : DIV.Pl D.host.E) (d : List ℤ) (c : ℂ) :
    ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j 0 (g * γ) = c • X.fn hμ j 0 g := by
  intro g
  rw [fn_zero]
  simp

theorem eig_add {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (Pp : DIV.Pl D.host.E) (d : List ℤ) (c : ℂ)
    (f₁ f₂ : D.what₂.Mt μ (j.1 + 1)) (h₁ : ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f₁ (g * γ) = c • X.fn hμ j f₁ g) (h₂ : ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f₂ (g * γ) = c • X.fn hμ j f₂ g) :
    ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j (f₁ + f₂) (g * γ) = c • X.fn hμ j (f₁ + f₂) g := by
  intro g
  rw [fn_add]
  simp only [Pi.add_apply, Finset.sum_add_distrib, smul_add, h₁ g, h₂ g]

theorem alongEig {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (x : D.nd.X i) (Pp : DIV.Pl D.host.E) (d : List ℤ) (c : ℂ)
    (hc : ∀ Q : D.naut.AV i, D.naut.ptV i Q = some x → ∀ f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1),
      (hj ▸ f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q → ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' (g * γ) = c • X.fn hμ j f' g) :
    ∀ m ∈ eigC D.nd D.naut i x, ∀ f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1),
      (hj ▸ f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) = m → ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' (g * γ) = c • X.fn hμ j f' g := by
  intro m hm
  unfold eigC at hm
  refine Submodule.iSup_induction (fun Q => ⨆ (_ : Q ∈ {P | D.naut.ptV i P = some x}), D.naut.typeV i Q)
    (motive := fun m => ∀ f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1),
      (hj ▸ f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) = m → ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' (g * γ) = c • X.fn hμ j f' g) hm ?_ ?_ ?_
  · intro Q m' hm' f' hf'
    by_cases hQ : D.naut.ptV i Q = some x
    · rw [iSup_pos (show Q ∈ {P | D.naut.ptV i P = some x} from hQ)] at hm'
      exact hc Q hQ f' (hf' ▸ hm')
    · rw [iSup_neg (show Q ∉ {P | D.naut.ptV i P = some x} from hQ), Submodule.mem_bot] at hm'
      have : f' = 0 := cast_inj hj (hf'.trans (hm'.trans (cast_zero hj).symm))
      subst this
      exact eig_zero X hμ j Pp d c
  · intro f' hf'
    have : f' = 0 := cast_inj hj (hf'.trans (cast_zero hj).symm)
    subst this
    exact eig_zero X hμ j Pp d c
  · intro m1 m2 ih1 ih2 f' hf'
    have hsplit : f' = (hj.symm ▸ m1 : D.what₂.Mt (D.nd.mu i) (j.1 + 1)) + (hj.symm ▸ m2) := by
      apply cast_inj hj
      rw [hf', cast_add, cast_symm, cast_symm]
    subst hsplit
    exact eig_add X hμ j Pp d c _ _ (ih1 _ (cast_symm hj m1)) (ih2 _ (cast_symm hj m2))

end GlobalTheory.EigSplit
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Theta
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VFormCong

theorem redFn_eq_one_of_finCong {D : D7} {V : TH.HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) {N : ℕ} {k : GA D V}
    (hΛ : IsSDFrame V β Λ 1) (hN : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (hk : GlobalTheory.Member.FinCong V N k) :
    ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → Formalism.L2.DIV.redFn β PP (Lev.finE V k) = 1 := by
  have hfr : Formalism.L2.DIV.IsFrame β Λ := by obtain ⟨c, h, -⟩ := hΛ; exact h
  have hl : Formalism.L2.Pj.latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hΛ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  have hc : ∀ a : GA D V, GlobalTheory.Member.FinCong V N a → ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ,
      ∃ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, (Lev.finE V a).1 *ᵥ z - z = N • y := by
    intro a ha
    unfold GlobalTheory.Member.FinCong at ha
    rw [hl] at ha
    exact GlobalTheory.PrincInLevel.cong_swap Λ N _ ha
  have hc' := hc _ (GlobalTheory.Member.PrincLevel.finCong_inv hk)
  rw [map_inv] at hc'
  obtain ⟨y, hy, hred⟩ := GlobalTheory.PrincInLevel.exists_int (Formalism.L2.Herm.intAf D.host.F D.host.E) β (Lev.finE V k)
    (Formalism.L2.Herm.hatL (F := D.host.F) Λ) N hfr (hc k hk) hc'
  have hy' : Formalism.L2.DIV.frGL β y = Lev.finE V k := hy
  intro PP hP
  rw [← hy', Formalism.L2.DIV.redFn_frGL]
  refine hred _ _ ?_
  rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (hN PP hP)

theorem levFn_eq_one {D : D7} {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ n)
    (x : GL (Fin n) (Lev.EAf D)) (h3 : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → Formalism.L2.DIV.redFn β PP x = 1) :
    Formalism.L2.DIV.levFn β L x = 1 := by
  have e : Formalism.L2.DIV.levFn β L x = Formalism.L2.DIV.levFn β L 1 := by
    have hr : Formalism.L2.DIV.rTup β L x = Formalism.L2.DIV.rTup β L 1 := by
      funext PP
      show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn β PP.1 x) = Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn β PP.1 1)
      rw [h3 PP.1 (Or.inl PP.2), Formalism.L2.DIV.redFn_one]
    unfold Formalism.L2.DIV.levFn
    rw [hr]
    congr 1
    · congr 1
      exact Finset.prod_congr rfl fun PP hPP => Finset.prod_congr rfl fun c _ => by
        rw [h3 PP (Or.inl hPP), Formalism.L2.DIV.redFn_one]
    · exact Finset.prod_congr rfl fun PP hPP => by
        rw [h3 PP (Or.inr hPP), Formalism.L2.DIV.redFn_one]
  rw [e]
  exact (Formalism.L2.DIV.levChar D.sp.cm (1 : Matrix (Fin n) (Fin n) D.host.E) β L).map_one

end GlobalTheory.VFormCong



theorem GlobalTheory.VFormCong.exists_cong_levEnv : ∀ (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (X : GlobalTheory.NJoin.RealAt D cf nch tp) (M : MtFam D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (hA : GlobalTheory.NJoin.Agree X M rep) (j : Fin D.R.m) (t : X.T), ∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : (finHom (Vc D j)).rangeRestrict ((hA.PV j).ψ κ) ∈ (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).J, (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).χ ⟨_, h⟩ = 1 := by
  intro D cf nch tp X M rep hA j t
  classical
  obtain ⟨N, hN0, hNmem⟩ : ∃ N : ℕ, 0 < N ∧ ∀ PP, PP ∈ (X.R.datVt j t).Pg ∨ PP ∈ (X.R.datVt j t).Q →
      ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    refine ⟨∏ PP ∈ (X.R.datVt j t).Pg ∪ (X.R.datVt j t).Q, Ideal.absNorm PP.asIdeal, Finset.prod_pos fun PP _ =>
      Nat.pos_of_ne_zero fun h => PP.ne_bot (Ideal.absNorm_eq_zero_iff.1 h), fun PP hPP => ?_⟩
    obtain ⟨u, hu⟩ := Finset.dvd_prod_of_mem (fun PP => Ideal.absNorm (IsDedekindDomain.HeightOneSpectrum.asIdeal PP))
      (Finset.mem_union.2 hPP)
    rw [hu, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  obtain ⟨N', hN', hcong⟩ :=
    GlobalTheory.StdFrameCong.exists_cong_finCong D (Vc D j) D.R.nV (hA.PV j) hA.hF (hA.stdV j) N hN0
  refine ⟨N', hN', fun κ hκ => ?_⟩
  have hk := hcong κ hκ
  have hβ := X.given.core.lev.βV j
  refine ⟨GlobalTheory.PrincInLevel.finCong_mem_levEnv D (Vc D j) (X.R.βV j) (X.R.ΛV j) (X.R.datVt j t) N _ hβ hNmem hk, ?_⟩
  apply Units.ext
  change ((Formalism.L2.DIV.levFn (X.R.βV j) (Lev.flag1L (X.R.datVt j t)) (Lev.finE (Vc D j) ((hA.PV j).ψ κ)) : ℂˣ) : ℂ) = 1
  rw [GlobalTheory.VFormCong.levFn_eq_one (X.R.βV j) (Lev.flag1L (X.R.datVt j t)) _
    (fun PP hP => GlobalTheory.VFormCong.redFn_eq_one_of_finCong (X.R.datVt j t) hβ hNmem hk PP hP)]
  rfl
end
end
