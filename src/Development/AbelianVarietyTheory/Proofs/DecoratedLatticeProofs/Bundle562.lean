module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle555
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle551
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle025
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle558
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartW
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle008
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle108
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle561
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle493
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle322
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle304
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle560
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle553
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1881
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle356
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle250
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle249
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle612
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle265
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSawAll

variable {D : D7}

theorem real_pos_of_open_compact {X : Type} [TopologicalSpace X] [MeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts μ] {S : Set X} (ho : IsOpen S) (hc : IsCompact S) (hn : S.Nonempty) : 0 < μ.real S :=
  ENNReal.toReal_pos (ho.measure_ne_zero μ hn) hc.measure_lt_top.ne

theorem level_open_compact (V : HSp D) (L : Lat V) (hL : IsSelfDualC V L) (gP : Finset (Pl D)) (JG : Subgroup (GA D V))
    (hJ : JG ≤ grpAt V (· ∈ gP)) (hJc : IsCompact (JG : Set (GA D V)))
    (hJo : IsOpen (((JG.subgroupOf (grpAt V (· ∈ gP))) : Subgroup _) : Set (grpAt V (· ∈ gP)))) :
    IsOpen {g : GfC V | ∃ κ, InK V L (· ∉ gP) κ ∧ ∃ k ∈ JG, g.1 = κ * k} ∧
      IsCompact {g : GfC V | ∃ κ, InK V L (· ∉ gP) κ ∧ ∃ k ∈ JG, g.1 = κ * k} ∧
      (1 : GfC V) ∈ {g : GfC V | ∃ κ, InK V L (· ∉ gP) κ ∧ ∃ k ∈ JG, g.1 = κ * k} := by
  obtain ⟨-, -, -, -, hcomm, ⟨e, he⟩, -, -, hK, -⟩ := GlobalTheory.FinPl.SetCut.grp_split D V gP
  obtain ⟨⟨K₁, hK₁, hK₁c, hK₁o⟩, -⟩ := hK L hL (· ∉ gP)
  have hS : {g : GfC V | ∃ κ, InK V L (· ∉ gP) κ ∧ ∃ k ∈ JG, g.1 = κ * k} =
      e '' ((((JG.subgroupOf (grpAt V (· ∈ gP))) : Subgroup _) : Set (grpAt V (· ∈ gP))) ×ˢ
        (((K₁.subgroupOf (grpAt V (· ∉ gP))) : Subgroup _) : Set (grpAt V (· ∉ gP)))) := by
    ext g
    constructor
    · rintro ⟨κ, hκ, k, hk, hg⟩
      have hκ' : κ ∈ grpAt V (· ∉ gP) := hκ.1
      refine ⟨(⟨k, hJ hk⟩, ⟨κ, hκ'⟩), ⟨Subgroup.mem_subgroupOf.2 hk, Subgroup.mem_subgroupOf.2 ((hK₁ κ).2 hκ)⟩, ?_⟩
      apply Subtype.ext
      rw [he, hg, hcomm k (hJ hk) κ hκ']
    · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
      refine ⟨p.2.1, (hK₁ _).1 (Subgroup.mem_subgroupOf.1 hp2), p.1.1, Subgroup.mem_subgroupOf.1 hp1, ?_⟩
      rw [he, hcomm p.1.1 p.1.2 p.2.1 p.2.2]
  have hAc : IsCompact (((JG.subgroupOf (grpAt V (· ∈ gP))) : Subgroup _) : Set (grpAt V (· ∈ gP))) := by
    have h1 : ((JG.subgroupOf (grpAt V (· ∈ gP)) : Subgroup _) : Set (grpAt V (· ∈ gP))) =
        Subtype.val ⁻¹' (JG : Set (GA D V)) := rfl
    rw [h1, Topology.IsInducing.subtypeVal.isCompact_preimage_iff]
    · exact hJc
    · intro x hx; exact ⟨⟨x, hJ hx⟩, rfl⟩
  have hBc : IsCompact (((K₁.subgroupOf (grpAt V (· ∉ gP))) : Subgroup _) : Set (grpAt V (· ∉ gP))) := by
    have h1 : ((K₁.subgroupOf (grpAt V (· ∉ gP)) : Subgroup _) : Set (grpAt V (· ∉ gP))) =
        Subtype.val ⁻¹' (K₁ : Set (GA D V)) := rfl
    rw [h1, Topology.IsInducing.subtypeVal.isCompact_preimage_iff]
    · exact hK₁c
    · intro x hx; exact ⟨⟨x, ((hK₁ x).1 hx).1⟩, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hS]; exact e.isOpenMap _ (hJo.prod hK₁o)
  · rw [hS]; exact (hAc.prod hBc).image e.continuous
  · exact ⟨1, (hK₁ 1).1 (one_mem _), 1, one_mem _, by simp⟩

variable {c : Comm D}

theorem vr_ne_zero (v : VCom c) (hv : v.Is) (j : ℕ) (hj : j < D.R.m) (hμ : (c.μf j).IsHaarMeasure)
    (R : Subgroup (GA D (c.V j))) (hR : IsClosed (R : Set (GA D (c.V j))))
    (ρ : Measure (R.subgroupOf (GfC (c.V j)))) (hρ : ρ.IsHaarMeasure) : v.vr j R ρ ≠ 0 := by
  obtain ⟨hJle, hJc, hJo⟩ := hv.JG j hj
  obtain ⟨hSo, hSc, hS1⟩ := level_open_compact (c.V j) (v.N j) (hv.sd j hj) v.gP (v.JG j) hJle hJc hJo
  have h1 : 0 < (c.μf j).real {g | g.1 ∈ v.K j} := by
    exact real_pos_of_open_compact (c.μf j) hSo hSc ⟨1, hS1⟩
  have hT : IsClosed (((R.subgroupOf (GfC (c.V j))) : Subgroup _) : Set (GfC (c.V j))) :=
    hR.preimage continuous_subtype_val
  have h2 : 0 < ρ.real {g | g.1.1 ∈ v.K j} := by
    exact real_pos_of_open_compact ρ (hSo.preimage continuous_subtype_val)
      (hT.isClosedEmbedding_subtypeVal.isCompact_preimage hSc) ⟨1, hS1⟩
  unfold VCom.vr
  exact_mod_cast (div_pos h1 h2).ne'

theorem kap_ne_zero (v : VCom c) (hc : c.Is) (hv : v.Is) : ∀ j σ h, v.kap j σ h ≠ 0 := by
  intro j σ h
  unfold VCom.kap
  refine mul_ne_zero ?_ ?_
  · exact vr_ne_zero v hv (j + 1) (by omega) (hc.μf _) _ (GlobalTheory.jacGrp_isClosed _ _ _ _ _) _ (hc.ρJ _ _ _)
  · exact vr_ne_zero v hv (j + 1 + 1) (by omega) (hc.μf _) _ (GlobalTheory.BesClosed.besGrp_isClosed _ _ _ _ _ _ _ _) _ (hc.ρB _ _ _)

theorem is_withCG (v : VCom c) (a : ℕ → ℂ) (h : v.Is) : (v.withCG a).Is :=
  ⟨h.disj, h.sd, h.sdT, h.b, h.bT, h.Ψ, h.ΨT, h.JG, h.atG, h.atT, h.ram⟩

theorem weilOK_of_tau {t : Tup c} (v v' : VCom c) (hτ : v'.τ = v.τ) (h : WeilOK (t := t) v) : WeilOK (t := t) v' := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, by rw [hτ]; exact h3⟩

theorem unrOn_mono {t : Tup c} {P P' : Pl D → Prop} (h : t.UnrOn P) (hPP : ∀ x, P' x → P x) : t.UnrOn P' := by
  refine ⟨fun j ρ hh x hx => h.bf j ρ hh x (hPP x hx),
    fun j σ hh x hx => h.fb j σ hh x (hPP x hx), ?_⟩
  intro j hh
  obtain ⟨χS, χT, h1, h2⟩ := h.top j hh
  exact ⟨χS, χT, h1, fun x hx => h2 x (hPP x hx)⟩

end GlobalTheory.SeeSawAll

namespace GlobalTheory.SeeSaw

theorem pins_finiteIntegrals : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι) (n : ℕ) (G : Fin n → GLoc v), c.Is → c.VolLast → v.Is → ShapeOff v o → GPin G → ∃ (ε : ℕ → ι → 𝓀[k]ˣ) (op : ∀ j, BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) (r : ℕ → ι → ℝ) (e : ℕ → ι → ℤ) (a : ℕ → ℂ), (∀ j i, 0 < r j i) ∧ (∀ j, a j ≠ 0) ∧ (∀ j σ h, v.kap j σ h ≠ 0) ∧ ((v.withT (o.S ε) op).withCG a).Is ∧ ∀ (𝒯 : Type) (t : 𝒯 → Tup c) (w : ∀ s, VTup (t s)), (∀ s, (t s).Is ∧ VForm ((v.withT (o.S ε) op).withCG a) (w s) ∧ WeilOK (t := t s) v ∧ TopSph (t := t s) v ∧ (t s).UnrOn (offP v (w s)) ∧ (t s).UnrK (· ∈ v.tP) ∧ (∀ i, (G i).Chars (t s)) ∧ QLaw v (w s) ∧ QLast v (w s) ∧ QFin v (w s) ∧ (∀ j ρ h, (w s).cT j = o.mono (r j) (e j) ((t s).sBF j ρ h).χW) ∧ CVEq ((v.withT (o.S ε) op).withCG a) (w s)) → (∀ s, (t s).LocFin) ∧ ValX t ∧ ValLastX t := by
  intro D c v k _ _ _ _ ι o n G hc hvl hv hsh hG
  obtain ⟨ε, op, r, e, hr, hvT, hT⟩ := GlobalTheory.T.seesaw_levelPrime_law_all_tuples D c v k ι o hc hv hsh
  obtain ⟨a, ha, hGa⟩ := GlobalTheory.T.seeSawUnfolded_support_and_value_at_fixed_level D c v n G hc hv hG
  have hv' : ((v.withT (o.S ε) op).withCG a).Is := GlobalTheory.SeeSawAll.is_withCG _ a hvT
  refine ⟨ε, op, r, e, a, hr, ha, GlobalTheory.SeeSawAll.kap_ne_zero v hc hv, hv', ?_⟩
  intro 𝒯 t w hw
  refine GlobalTheory.T.seesaw_place_laws_give_finite_integral_laws D c ((v.withT (o.S ε) op).withCG a) 𝒯 t w hc hvl hv' (fun s => (hw s).1) (fun s => ?_)
  obtain ⟨hts, hform, hweil, hsph, hunr, hunrK, hch, hql, hqlast, hqfin, hcT, hcv⟩ := hw s
  have hdisjT : Disjoint (w s).Q v.tP := hform.disjT
  have hoff : OffLaw v (w s) := GlobalTheory.T.seesaw_support_off_level_of_lattice_shape D c v k ι o hc hv hsh (t s) (w s) hts hdisjT hunr
  have hvac : VacLaw (t := t s) v := GlobalTheory.T.seeSawUnfoldedVacuaOfShape_proof D c v k ι o hc hv hsh (t s)
  have hunrT : (t s).UnrOn (· ∈ v.tP) := GlobalTheory.SeeSawAll.unrOn_mono hunr fun x hx =>
    ⟨fun hg => Finset.disjoint_left.mp hv.disj hg hx, fun hq => Finset.disjoint_left.mp hdisjT hq hx⟩
  have htl : TLaw (v.withT (o.S ε) op) (w s) := hT (t s) (w s) hts hweil hunrT hunrK hcT
  obtain ⟨hgs, hgv⟩ := hGa (t s) hts hweil hch
  exact ⟨hform, GlobalTheory.SeeSawAll.weilOK_of_tau v _ rfl hweil, hoff, hgs, hgv, hvac, htl, hql, hqlast, hqfin, hcv, hsph⟩

end GlobalTheory.SeeSaw

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QTw

theorem laws_of_pin_resc : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → t.Is → v.Is → WeilOK (t := t) v → QPinU v w → QLaw v w ∧ QLast v w ∧ QFin v w :=
  fun D c v t w hc ht hv hW h =>
    GlobalTheory.QTw.RescTest.laws_of_qpinU v (fun w₀ h₀ =>
      ⟨GlobalTheory.T.seeSawIteratedIntegralLaw_at_twist_of_factorisation D c v t w₀ hc ht hv hW h₀, GlobalTheory.T.seeSawIteratedIntegralLawLastSteps_of_localFactorisation D c v t w₀ hc ht hv hW h₀, GlobalTheory.T.seeSawFiniteCells_at_twistPlaces_of_localFactorisation D c v t w₀ hc ht hv hW h₀⟩) w h

end GlobalTheory.QTw
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.besselPeriod_double_step_unfolding_of_descent : ∀ D : D7, Descent D → DoubleStep D := by
  first | exact @GlobalTheory.Unf.doubleStep_of_descent | exact GlobalTheory.Unf.doubleStep_of_descent | (intros; apply GlobalTheory.Unf.doubleStep_of_descent <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalAll

theorem scal_matchUp_upInj : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilSiegelFormulaUnitary → (∀ D' : Formalism.BasicNotions.D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D') → GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → D.host.ccK = ⊤ → R.Sb = R.Pg → (∀ t P, GlobalTheory.Hk3.Good R t P → Formalism.DivisionValues.conjPl P = P → GlobalTheory.Hk3.FixAll R t P) → ∀ SF, GlobalTheory.Hk3.IsSF R SF → GlobalTheory.TrCopy.TRLev R F SF → Scal R SF ∧ MatchUp R SF ∧ UpInj R ∧ UpInjW R := by
  intro hDS hHCF hHCM hCW hCRD hHowe hWS hSWU hSEC hUD hBZ D G _ _ Pl0 T A Ks _ _ _ R F hG hcc hSb hfix SF hSF hTR
  have hA : AForm R SF := GlobalTheory.T.thetaInnerProduct_eq_const_mul_LValue hDS hHCM hCRD hWS hSEC hUD hBZ R F hG hcc SF hSF
  obtain ⟨hB, hUp⟩ := GlobalTheory.T.thetaLift_adjoint_scalarFormula_injective hDS hHCF hHCM hCW hCRD hHowe hWS hSWU hSEC hUD R F hG hcc hSb hfix SF hSF
  have hM : MatchUp R SF := GlobalTheory.MatchUpProof.matchUp_of_tr R F hG.core SF hTR
  have hS : Scal R SF := scal_of_aForm_bForm R SF hA hB hM
  exact ⟨hS, hM, hUp, (upInj_of_scal R F hG.core (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCRD R) hG.irr SF hSF hS).2⟩

end GlobalTheory.ScalAll

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
namespace GlobalTheory.ThmAFinal

theorem pThmA_short
    (hDS : GlobalTheory.Published.DiscreteSeriesCover) (hHCF : GlobalTheory.Published.HarishChandraFinite)
    (hHCM : GlobalTheory.Published.HarishChandraModules) (hCW : GlobalTheory.Published.CasselmanWallach)
    (hCusp : GlobalTheory.Published.CuspRapidDecay) (hHowe : GlobalTheory.Hk3.HoweUnram)
    (hWS : GlobalTheory.Published.WeilSiegelFormulaUnitary) (hHk : ∀ D' : Formalism.BasicNotions.D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D')
    (hSE : GlobalTheory.Published.SiegelEisensteinContinuation) (hUD : GlobalTheory.Published.UnramifiedDoublingGL)
    (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) :
    ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → HostHyp D → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → D.host.ccK = ⊤ → FWT.QGuard R.toRealDat → GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R.toRealDat → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → R.PThmA := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hCh hEx hHost hLed hcc hQ hGT hInert
  obtain ⟨hCore, hSF, hE, hW⟩ := GlobalTheory.T.core_clauses_of_weak_characterisation R F hCh hEx
  have hGiven := GlobalTheory.T.scalarHypotheses_of_topRows R F hOk hCh hEx hHost hLed hcc hQ hGT
  have hFix := GlobalTheory.T.hyperspecial_fixes_vacua_good_inert_place R F hCh hEx
  have hA := GlobalTheory.T.thetaInnerProduct_eq_const_mul_LValue hDS hHCM hCusp hWS hSE hUD hBZ R.toRealDat F.lv2 hGiven hcc R.SF hSF
  have hU := (GlobalTheory.T.thetaLift_adjoint_scalarFormula_injective hDS hHCF hHCM hCW hCusp hHowe hWS hHk hSE hUD R.toRealDat F.lv2 hGiven hcc hCh.allPl hFix R.SF hSF).2
  have hC := GlobalTheory.T.finiteType_carriesOnePart hHowe hCusp R F hOk hCh hEx hInert hU
  exact GlobalTheory.T.thetaAdjoint_scalar_theorem_of_scalar_formula R F hOk hCh hEx hA hC

end GlobalTheory.ThmAFinal
end
