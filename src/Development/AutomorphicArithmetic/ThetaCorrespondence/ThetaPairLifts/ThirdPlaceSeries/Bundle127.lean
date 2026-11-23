module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointLogKodairaSpencerFrameChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2492
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2497

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle447
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjIdealEqCP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle111
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle077
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle378
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2438
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle548
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle893
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2244
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle910
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle004
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.SerBase
theorem traceOfAt_alt : _root_.GlobalTheory.BigOn.Exp.SerBase.TraceAt' := by
  refine _root_.GlobalTheory.BigOn.Exp.TwistConditions.of_forall fun Fm x hx i p hR hM w hw j => ?_
  intro ρ hρ hpin hlev h P
  have hL := _root_.GlobalTheory.BigOn.links2_of_rows_alt _ _ _ _ _ _ _ _ _ _ p hR hM.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hBo : BaseOf (R2 p) j (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) := by
    have h0 := baseOf_of_realPin_at (cG := p.cG) hC.lev hρ hpin ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
    exact { h0 with }
  have key := GlobalTheory.T.thetaTraceLevelCompatible_proof _ _ _ _ _ _ (R2 p) (F2 p) hC j _ (hρ.base _ j _) hBo (F2 p).P0 (F2 p).ψ0⁻¹
    ((p.R.eG.trans p.cG).trans (ρ.eG ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)))
    ?_ ?_ ?_ _ (hρ.weil_base _ j _) h P
  · exact key.symm
  · intro g Q hQ hQ' a c
    have e := hpin.grp ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) ((p.R.eG.trans p.cG) g) Q hQ hQ' a c
    rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at e
    exact e
  · intro g
    exact mem_level_iff hM.2.2 hlev _ j _ g
  · intro u hu
    refine (level_chi hM.2.2 hρ hlev _ j _ u hu).1.trans ?_
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀]
    rfl
end GlobalTheory.BigOn.Exp.SerBase
end
end
end

section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open GlobalTheory.BigOn.Exp.SerBase
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
section GenericCmp
variable {O : Type} [CommRing O] [IsDomain O] {M : Type} [AddCommGroup M] [Module (FractionRing O) M] [Module O M]
  [IsScalarTower O (FractionRing O) M] [FiniteDimensional (FractionRing O) M]
  {L : Type} [Field L] [Algebra O L] {eK : FractionRing O →+* ℂ} {G : Type}
variable (rd : M →ₛₗ[eK] (G → ℂ)) (eL : L →+* ℂ)
  (hL : ∀ c : O, eL (algebraMap O L c) = eK (algebraMap O (FractionRing O) c))
end GenericCmp
end GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp.SerBase

theorem readCmpAt_alt : _root_.GlobalTheory.BigOn.Exp.SerBase.ReadComparisonAt := by
  unfold _root_.GlobalTheory.BigOn.Exp.SerBase.ReadComparisonAt
  refine _root_.GlobalTheory.BigOn.Exp.TwistConditions.of_forall fun Fm x hx i p hr hm w _ j => ?_
  intro ρ hρ e he1 he2 ν hν rd hcan u hu f y a hfa
  obtain ⟨Z⟩ := hm.2.2.series
  have hU : p.R.toRealDat.LUnif := hr.prim.unif
  have hW : p.R.toRealDat.models_HW := p.charW.base.models.HW
  have hK : (p.Sx.A ((j : ℕ) + 1)).IsKsForm := GlobalTheory.isKsForm_of_formsIso _ _ (p.nexp.fi j) (p.fw.ks j)
  have hF : Faithful (rdAt p w j hρ ν) := GlobalTheory.SeriesTie.realRd_faithful _ _ _ _ _ _ _ p.R p.cG p.Sx p.nexp p.v₀ ρ hρ
    ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) ν hν hU hW (Z.vec j) hK
  have hL : ∀ c : (Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w),
      e (algebraMap _ (FractionRing ((Fm.ex x hx i).nch.Oe w)) c) =
        ρ.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) (algebraMap _ (FractionRing _) c) := fun c => by
    rw [IsScalarTower.algebraMap_apply _ ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)),
      IsScalarTower.algebraMap_apply _ ((Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w)) ((Fm.ex x hx i).nch.Oe w),
      he2, hρ.ek_e]
    rfl
  set R := readExt (rdAt p w j hρ ν) e hL with hRdef
  have hgen : ∀ f : NX.FmK p.Sx ((j : ℕ) + 1), R (rd ((p.nexp.fi j).e (Subtype.val f))) =
      ν⁻¹ • adForm (R2 p) j ((p.nexp.fi j).e (Subtype.val f)) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun f => by
    rw [hcan f, hRdef, readExt_tmul, map_one, one_smul]
    erw [realRd_tmul]
    erw [map_one, mul_one]
    rfl
  have hA0 : adForm (R2 p) j 0 (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) = 0 := by
    change ((R2 p).HW j _).e (((R2 p).FW j).j _ 0) (p.v₀ j _) = 0
    rw [map_zero, map_zero]
    rfl
  have hAadd : ∀ u v, adForm (R2 p) j (u + v) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) =
      adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) + adForm (R2 p) j v (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun u v => by
    change ((R2 p).HW j _).e (((R2 p).FW j).j _ (u + v)) (p.v₀ j _) = _
    rw [map_add (f := _), map_add (f := _)]
    rfl
  have hs : sg0 (Fm.D x i) p.P.A3.A = (Fm.D x i).what₂.embLL := sgAt_mk _ (R2 p).hv0
  have hAsmul : ∀ (c : (Fm.D x i).what₂.LL) u, adForm (R2 p) j (c • u) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) =
      (Fm.D x i).what₂.embLL c • adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun c u => by
    change ((R2 p).HW j _).e (((R2 p).FW j).j _ (c • u)) (p.v₀ j _) = _
    rw [LinearMap.map_smulₛₗ, map_smul]
    exact congrArg (fun s : ℂ => s • adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A))) (DFunLike.congr_fun hs c)
  have hrd : ∀ u ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _)),
      R (rd u) = ν⁻¹ • adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun u hu => by
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨f, hf, rfl⟩ := hu
      exact hgen ⟨f, hf⟩
    | zero =>
      erw [LinearMap.map_zero rd]
      rw [AddMonoidHom.map_zero R]
      erw [hA0]
      rw [smul_zero]
    | add u v _ _ hu hv =>
      erw [LinearMap.map_add rd]
      rw [AddMonoidHom.map_add R, hu, hv]
      erw [hAadd]
      rw [smul_add]
    | smul c u _ hu =>
      erw [LinearMap.map_smulₛₗ rd]
      rw [hRdef, readExt_smul, ← hRdef, hu, he1]
      erw [hAsmul]
      rw [smul_comm]
  have htop : ∀ y, y ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _)) := fun y => by
    obtain ⟨n, b, hmem, -, -, -, hLs⟩ := hK
    have h2 : (p.nexp.fi j).e.symm y ∈ Submodule.span (Fm.D x i).what₂.LL (Set.range b) := hLs ▸ Submodule.mem_top
    have h3 := Submodule.mem_map_of_mem (f := (p.nexp.fi j).e.toLinearMap) h2
    rw [Submodule.map_span] at h3
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h3
    refine Submodule.span_mono ?_ h3
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨b k, hmem k, rfl⟩
  have hv : (fun τ => (u τ : ((R2 p).MW j (sg0 (Fm.D x i) p.P.A3.A)).sm τ)) = p.v₀ j (sg0 (Fm.D x i) p.P.A3.A) := funext hu
  have h1 : R ((1 : FractionRing ((Fm.ex x hx i).nch.Oe w)) ⊗ₜ f) = a • R (rd y) := by
    rw [hRdef, readExt_tmul, map_one, one_smul, hfa, ← hRdef, hrd y (htop y), hv]
  by_cases hf : f = 0
  · exact Or.inl hf
  · refine Or.inr (readExt_eq_smul_of_read _ e hL hF _ _ a h1 ?_)
    rw [readExt_tmul, map_one, one_smul]
    exact fun h0 => hf (hF.injective (h0.trans (map_zero _).symm))
end GlobalTheory.BigOn.Exp.SerBase
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
namespace GlobalTheory.Fc.RL
theorem rowE_dcPt_linked_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (Q : V4.Slot) :
    RowE Q (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ => _root_.GlobalTheory.Fc.R1.DecompositionPointBundle) := by
  refine RowE.of_all fun κ K β c b _ _ hl => ?_
  obtain ⟨q, b', ⟨w⟩, he⟩ := hl
  have hBundle := congrArg
    (fun s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c =>
      _root_.GlobalTheory.Fc.R1.DecompositionPointBundle s.1 s.2.1 c s.2.2) he
  refine cast hBundle.symm ?_
  change GlobalTheory.Cp.DcPtG b'.P
  have hP : b'.P = R3.divisionPairOfAdelicFormsFaceColumnsData w.x := congrArg _root_.GlobalTheory.Mem.Top.Bl.RealPackage.P w.y.eq
  rw [hP]
  exact (GlobalTheory.Mem.R3.rowConditions_at_companion_from_readings _ _ _ _ _ _ _ _ _ w.x).2.2.1
theorem linkedAt_hDcPtG : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP),
    _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotDecompositionPointCondition := by
  intro hL N S Γ
  exact _root_.GlobalTheory.Fc.RL.LinkedAt.of_row (RowE.row (_root_.GlobalTheory.Fc.RL.rowE_dcPt_linked_alt _ _))
end GlobalTheory.Fc.RL
end
end
end

section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
theorem scaleRoot_of_hypothesis_alt (_ : GlobalTheory.Published.CuspRapidDecay) (_ : GlobalTheory.Published.GlobalArtinReciprocity) (_ : GlobalTheory.Published.RayClassFieldSt)
    (_ : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat) : _root_.GlobalTheory.BigOn.Exp.ScaleRootAltBis := by
  unfold _root_.GlobalTheory.BigOn.Exp.ScaleRootAltBis _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ?_⟩⟩
  refine ⟨0, fun x hx _ i p _ _ w _ j ρ ρ' hρ hρ' ν ν' _ _ hSB hN hN' _ _ s h P _ _ _ => ?_⟩
  obtain ⟨-, c, hc, n, hn, hνn⟩ := hN
  obtain ⟨-, c', hc', m, hm, hν'm⟩ := hN'
  rw [hSB.2.2.2.1] at hc'
  obtain ⟨k, hk, hkk⟩ := isScale_pow_eq p.R p.v₀ _ hc hc'
  refine ⟨n * m * k, Nat.mul_ne_zero (Nat.mul_ne_zero hn hm) hk, ?_⟩
  have e1 : ν' ^ (n * m * k) = (ν' ^ m) ^ (n * k) := by rw [← pow_mul]; ring_nf
  have e2 : ν ^ (n * m * k) = (ν ^ n) ^ (m * k) := by rw [← pow_mul]; ring_nf
  have e3 : c' ^ (n * m * k) = c ^ (n * m * k) := by
    rw [show n * m * k = k * (n * m) by ring, pow_mul c', pow_mul c, hkk]
  rw [e1, e2, hν'm, hνn, ← pow_mul, ← pow_mul, mul_pow, mul_pow,
    show m * (n * k) = n * m * k by ring, show n * (m * k) = n * m * k by ring, e3]
end GlobalTheory.BigOn.Exp
end
end
end

section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
open GlobalTheory.BigOn.Exp.TwConj GlobalTheory.IdemSupport
open Formalism.L2.Host (HChar IsDelta IsPsi)


attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.TwConj.LevAt
section Places
variable {D : D7}
end Places
section Transfer
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end Transfer
section Chars
variable {D : D7}
variable {q l : ℕ} {δ ψ : HChar D.host.E} {Q : Finset (Pl D.host.E)}
end Chars
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {w : D.what₂.places.Pl}
end Point
end GlobalTheory.BigOn.Exp.TwConj.LevAt
namespace GlobalTheory.BigOn.Exp.TwConj
open LevAt in
theorem twLevAt_holds_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter →
    _root_.GlobalTheory.BigOn.Exp.TwConj.TwLevAtAlt := fun _ _ _ hA hC => by
  refine _root_.GlobalTheory.BigOn.Exp.TwistConditions.imp (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hA (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hC _root_.GlobalTheory.BigOn.Exp.lowAt_holds_alt)) fun Fm x hx i p hr hm w hw j H => ?_
  obtain ⟨⟨a1, -, -⟩, a2, a3⟩ := H
  intro ρ ρ' hρ hρ' hp hs hA
  have hl := ((Fm.D x i).ntw.lPrime ((Fm.ex x hx i).nch.twI w)).out
  have hlow : ∀ P ∈ (Fm.ex x hx i).nch.Q w,
      (((Fm.D x i).host.pde * (Fm.D x i).host.pde' : ℕ) : 𝓞 (Fm.D x i).host.E) ∉ P.asIdeal := fun P hP h => by
    refine Finset.disjoint_left.1 a1.2.1 hP (a3 P ?_)
    rw [mul_assoc _ (Fm.D x i).host.pde, ← mul_assoc, Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ h
  have pw : ∀ σ σ' : Setup (Fm.D x i).ntw, σ.Good → Adapted p w σ → σ'.rc = σ.rc →
      ∃ a : ℕ, (a + 1).Coprime ((Fm.D x i).ntw.l ((Fm.ex x hx i).nch.twI w)) ∧
        ChrEq (twW (Fm.ex x hx i) w σ').chi (p.Tp.psi w ^ (a + 1)) := fun σ σ' hσ hσA e => by
    obtain ⟨a, ha, h⟩ := exists_pow e ((Fm.ex x hx i).nch.sd w) a1
    rcases a with _ | a
    · exact absurd (Nat.coprime_zero_left _ |>.1 ha) hl.one_lt.ne'
    · exact ⟨a, ha, by rw [twW, h]; exact chrEq_pow (a2 σ hσ hσA).1 a⟩
  obtain ⟨⟨a, ha, hc⟩, a', ha', hc'⟩ : (∃ a : ℕ, (a + 1).Coprime ((Fm.D x i).ntw.l ((Fm.ex x hx i).nch.twI w)) ∧
        ChrEq (twW (Fm.ex x hx i) w ρ).chi (p.Tp.psi w ^ (a + 1))) ∧
      ∃ a : ℕ, (a + 1).Coprime ((Fm.D x i).ntw.l ((Fm.ex x hx i).nch.twI w)) ∧
        ChrEq (twW (Fm.ex x hx i) w ρ').chi (p.Tp.psi w ^ (a + 1)) :=
    hA.elim (fun h => ⟨pw ρ ρ hρ h rfl, pw ρ ρ' hρ h hs.1⟩) fun h => ⟨pw ρ' ρ hρ' h hs.1.symm, pw ρ' ρ' hρ' h rfl⟩
  obtain ⟨xiR, h1⟩ := twLev_pow hm.2.2 p.charW.base.fam p.qGuard hw j hlow hρ hp ha hc
  obtain ⟨xiR', h2⟩ := twLev_pow hm.2.2 p.charW.base.fam p.qGuard hw j hlow hρ hp ha' hc'
  have hQ : (twW (Fm.ex x hx i) w ρ').Q = half (ρ.ch ((Fm.ex x hx i).nch.twI w)) ((Fm.ex x hx i).nch.Q w) := by
    simp only [Setup.tw, twistOf, hs.2.1]
  obtain ⟨q, hq, hδ, -⟩ := exists_delta p.R.C ((Fm.ex x hx i).nch.twI w)
  obtain ⟨v, hv⟩ := exists_over (D := Fm.D x i) hq
  have hψ := p.Tp.psi_is w ((p.tw_iff w).1 hw)
  rw [← (Fm.ex x hx i).nch.twI_l] at hψ
  have hne : ∀ n : ℕ, p.R.C.delAt ((Fm.D x i).ntw.l ((Fm.ex x hx i).nch.twI w)) * p.Tp.psi w ^ n ≠ 1 := fun n e =>
    not_unr hδ hψ hl n hv (by rw [e]; exact fun _ _ => rfl)
  refine ⟨_, _, xiR, xiR', h1, hQ ▸ h2, hne _, hne _, or_iff_not_imp_left.2 fun e => ?_⟩
  rw [Ne, not_not] at e
  exact GlobalTheory.ChrEqUnique.idc_unique _ _ _ _ h1.xi (e ▸ h2.xi)
end GlobalTheory.BigOn.Exp.TwConj
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.Mem.AtPtTransport
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
theorem overNE_of_NEb_alt {N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL}
    (hN : ∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) :
    _root_.GlobalTheory.NRows.AtPt.OverNEAlt N :=
  fun K B f T w Z Wt p0 t nch n xd c h => (hN K B f T w Z Wt p0 t nch n xd c h).elim fun x => ⟨x.1⟩
theorem atMem_at_wit_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), WitMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s →
    (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) →
    (∀ p : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) fun Q L => RowE Q L fun κ D O _ _ => ∃ K : Ctx, κ.Of K ∧ O.L.sc = K.s ∧
      Val K.C K.cD K.ch O.L ∧ ∃ q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K, q.Is D O ∧
        p K q.B q.f q.T q.w q.Z q.x.Wt _ q.x.what₂ _ q.x.n (_root_.GlobalTheory.Mem.Top.Bl.WPt.core_data_of_point (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) q)) ∧
    ∀ P : ∀ D : D7, NChoice D → Prop, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL (fun _ _ _ _ w Z _ _ _ nch _ _ => P (w.D Z) nch) →
      _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) fun Q L => RowE Q L fun _ D O _ _ => P D O.ex.nch := by
  intro hL N S Γ H hN
  have hN' := _root_.GlobalTheory.Mem.AtPtTransport.overNE_of_NEb_alt hN
  refine ⟨fun p hp => ?_, fun P hP => ?_⟩
  · refine GlobalTheory.NRows.AtPt.linkedBundleProperty_after_largeBaseCoreProperty (_root_.GlobalTheory.NRows.AtPt.lgSlotG_memSlot' hp _) ?_
    refine RowE.of_all fun κ K β c b hk hβ _ => ?_
    obtain ⟨q, hq, _, hw⟩ := _root_.GlobalTheory.NRows.AtPt.exists_wPt_entC_atWit hN' H β hβ
    exact ⟨K, hk, β.sc, β.p.pt_val β.val, q, hq, hw⟩
  · exact _root_.GlobalTheory.NRows.AtPt.lg1_entry_of_atWit hP hN' H (r := fun D O => P D O.ex.nch) (fun K q _ t => t) _
end GlobalTheory.Mem.AtPtTransport
end
end
end

section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
end GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
def SerAlgAlt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ),
  RealPin p.R p.cG ρ →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  RatBase (rdAt p w j hρ ν) →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
      ∃ (n : ℕ) (z : Fin n → ℂ) (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)), (∀ k, IsAlgebraic ℚ (z k)) ∧
        ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P = ∑ k, z k • evW p.nexp p.v₀ j (g k).val
end GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
theorem expAlg_of_serAlg_alt (hS : _root_.GlobalTheory.BigOn.Exp.SerAlgAlt) : _root_.GlobalTheory.BigOn.Exp.ExpAlgAlt := by
  unfold _root_.GlobalTheory.BigOn.Exp.ExpAlgAlt _root_.GlobalTheory.BigOn.Exp.SerAlgAlt _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt at *
  refine hS.imp fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := h
  refine ⟨x0, fun x hx hle i p hp hm w hw j ρ hρ ν hpin hN hR0 s h P hd hP f hf => ?_⟩
  obtain ⟨n, z, g, hz, hsum⟩ := hx0 x hx hle i p hp hm w hw j ρ hρ ν hpin hN hR0 s h P hd hP
  obtain ⟨Z⟩ := hm.2.2.series
  have hU : p.R.toRealDat.LUnif := hp.prim.unif
  have hW : p.R.toRealDat.models_HW := p.charW.base.models.HW
  have hK : (p.Sx.A ((j : ℕ) + 1)).IsKsForm := GlobalTheory.isKsForm_of_formsIso _ _ (p.nexp.fi j) (p.fw.ks j)
  refine exists_algExp p.nexp p.v₀ hρ _ j _ hU hW (Z.vec j) hK _ z g hz ?_
  rw [← hsum, ← hf]
  exact (smul_inv_smul₀ hN.1 _).symm
end GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
def SerRefAlt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ),
  RealPin p.R p.cG ρ →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  RatBase (rdAt p w j hρ ν) →
  ∃ ν₀ : ℂ, IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν₀ ∧ RatBase (rdAt p w j hρ ν₀) ∧
    ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
      P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
        ∃ (n : ℕ) (z : Fin n → ℂ) (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)), (∀ k, IsAlgebraic ℚ (z k)) ∧
          ν₀ • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P = ∑ k, z k • evW p.nexp p.v₀ j (g k).val
theorem serAlg_of_serRef_scaleRoot (hR : _root_.GlobalTheory.BigOn.Exp.SerRefAlt) (hS : _root_.GlobalTheory.BigOn.Exp.ScaleRootAltBis) : _root_.GlobalTheory.BigOn.Exp.SerAlgAlt := by
  unfold _root_.GlobalTheory.BigOn.Exp.SerAlgAlt _root_.GlobalTheory.BigOn.Exp.SerRefAlt _root_.GlobalTheory.BigOn.Exp.ScaleRootAltBis _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt at *
  refine (Formalism.MainNotions.Closed.and hR hS).imp fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := h.1.and h.2
  refine ⟨x0, fun x hx hle i p hp hm w hw j ρ hρ ν hpin hN hR0 s h P hd hP => ?_⟩
  obtain ⟨a1, a2⟩ := hx0 x hx hle i p hp
  obtain ⟨ν₀, hN₀, hR₀, hexp⟩ := a1 hm w hw j ρ hρ ν hpin hN hR0
  obtain ⟨n, z, g, hz, hsum⟩ := hexp s h P hd hP
  by_cases hθ : ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P = 0
  · refine ⟨0, Fin.elim0, Fin.elim0, fun k => Fin.elim0 k, ?_⟩
    rw [hθ, smul_zero, Finset.univ_eq_empty, Finset.sum_empty]
  · obtain ⟨m, hm0, hpow⟩ := a2 hm w hw j ρ ρ hρ hρ ν₀ ν hpin hpin ⟨rfl, rfl, rfl, rfl, rfl⟩ hN₀ hN hR₀ hR0 s h P hd hP hθ
    have h0 : ν₀ ≠ 0 := hN₀.1
    have hζ : (ν / ν₀) ^ m = 1 := by rw [div_pow, hpow, div_self (pow_ne_zero _ h0)]
    refine ⟨n, fun k => ν / ν₀ * z k, g, fun k => ?_, ?_⟩
    · have hmem : ∀ y : ℂ, y ∈ algebraicClosure ℚ ℂ ↔ IsAlgebraic ℚ y := fun y => mem_algebraicClosure_iff
      exact (hmem _).1 (mul_mem ((hmem _).2 (isAlgebraic_of_pow_eq_one hm0 hζ)) ((hmem _).2 (hz k)))
    · conv_lhs => rw [← div_mul_cancel₀ ν h0]
      rw [mul_smul, hsum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul]
end GlobalTheory.BigOn.Exp
end
end
end

section



section
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain
open NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links (PolF labLL)
open Formalism.L2.Host (embLL0)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SmallSpan
variable {D : D7} {m n : ℕ}
theorem smallSt_alt : _root_.GlobalTheory.BigOn.Exp.TupLe.SmallnessCondition := by
  intro D _ _ _ _ _ _ _ _ _ p j _ _ B hB _ O O' _ hO' h P hP
  exact harmLat_le_span D.LL0.val.toRingHom D.what₂.embLL (labLL0 D) O O' hO'.int B.w B.F.BS hB.wt
    (GlobalTheory.CoefLatConj.pq_le hB) (isLattice_latAt hB.frame _) hP
end GlobalTheory.SmallSpan
end
end
end
