module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle018
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Formalism.LocalToGlobal.Divisibility.InertPartitionLePartF
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1881
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle337
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle357
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle243
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2117
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle594
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle024
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle021
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle027
public import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteContractionIdentityOperatorHalf
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle003
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle378
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle380
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle011
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3.HeckeClose

theorem heckeClose : HoweUnram → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), ∀ s, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → InertJunk A3 → (∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod (D.host.g k))) (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k)) C), ∀ f, D.ntypes.eSer k f = Formalism.L2.NT.eSerO O D.R.r f) → ((∃ tr, R.TrISem F tr ∧ TrISepWith A3 tr) → R.TrISem F A3.trI ∧ A3.fam3.TrISep) → R.toRealDat.LUnif → R.PGUnit F → R.PGEquiv F → R.PLevW F → R.PThmA → R.PThmB → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → (R.toCx3 F).PartsW false → ((∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) ∧ (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint)) ∧ R.PHecke F ∧ A3.fam3.TypesSep3 ∧ ∃ tr, R.TrISem F tr ∧ TrISepWith A3 tr := by
  intro hH hHC hCD D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hEx hJ hSer hPass hU hGU hGE hLW hA hB hPos hParts
  have hLI : GlobalTheory.Chain.LiftInteg D := GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hCD D
  have hS : SchurAll R.toRealDat := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCD R.toRealDat
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  obtain ⟨tr, htr⟩ := GlobalTheory.T.exists_separating_inert_eigenvalue_passage hH R F hLI hC hEx hS hJ hX hB hPos
  have hTS : A3.fam3.TypesSep3 :=
    GlobalTheory.T.finite_types_separated_by_inert_places hCD hH R F hLI hOk hC hEx ⟨fun t k => hJ.R t k.1 k.2, fun j t k => hJ.L j t k.1 k.2⟩ hPass hPos hB
  have hG : GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ := (GlobalTheory.GoodGenericSer.goodGenericCharacter_of_seriesTypes R F hC s hOk hSer).2
  have hR := GlobalTheory.T.exists_hecke_operators_rows_intertwine_theta_lifts hH hHC hCD R F hLI hC hEx hJ hB hPos
  have hL := GlobalTheory.T.heckeTheta_level3_exists hH hHC hCD R F hLI hC hEx hJ s hOk hG hU hGU hGE hLW hA hPos hB hParts hTS hPass
  exact ⟨GlobalTheory.T.okH_inertRationalAdjoint_of_weakCharacterisation_inertJunk R F hC hJ, ⟨hR, hL⟩, hTS, tr, htr⟩

end GlobalTheory.Hk3.HeckeClose

end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL GlobalTheory.CongL

namespace GlobalTheory.CongL.UnitLim

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem finite_not_sph (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)) (hU : IsAutRepU U) :
    {w : HeightOneSpectrum (𝓞 E) | IsSplitAt w ∧ ¬ ∃ B, SatU U w B}.Finite := by
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU.ne_bot
  let L : Subgroup (finU (E := E) (n := a)) :=
    { carrier := {k | RU E a k φ = φ}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at *
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := by
        intro x hx
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hLo : IsOpen (L : Set (finU (E := E) (n := a))) := (hU.aut φ hφ).level
  have hev : ∀ᶠ w in Filter.cofinite, IsSplitAt w → ∃ B, SatU U w B := by
    filter_upwards [GlobalTheory.BCT.GlobLev.eventually_locU_mem E a L hLo] with w hw hs
    obtain ⟨σ, B, hc, hB, -⟩ := GlobalTheory.FrameAut.exists_locComp_hasSatGL_heckeVec E a U hU w hs φ hφ hφ0
      fun x hx hxK => hw x hx hxK hx.1
    exact ⟨B, σ, hc, hB⟩
  exact (Filter.eventually_cofinite.1 hev).subset fun w hw h => hw.2 (h hw.1)

theorem dense_frob_usable_off (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (l : ℕ) (hl : l.Prime) (d : ℕ) (hd : ImQ E d) (X : Finset (HeightOneSpectrum (𝓞 E))) :
    Dense {g : _root_.Formalism.ConjugateSelfDual.G E Ω | ∃ w : HeightOneSpectrum (𝓞 E), w ∉ X ∧ UsPl d w ∧ ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧ ApartAll X w ∧
      ∃ A : ValuationSubring Ω, _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w ∧ IsFrob A (normV w) g} := by
  classical
  set M : ℕ := l * (2 * d) * ∏ u ∈ X, Ideal.absNorm u.asIdeal with hM
  have hM0 : M ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero hl.ne_zero (mul_ne_zero two_ne_zero hd.1.ne')) ?_
    rw [Finset.prod_ne_zero_iff]
    intro u _
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact u.ne_bot
  have hS1 : {w : HeightOneSpectrum (𝓞 E) | w.asIdeal ∣ Ideal.span {((M : ℕ) : 𝓞 E)}}.Finite := by
    refine Ideal.finite_factors ?_
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hM0
  have hS3 := (GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).2
  set S := {w : HeightOneSpectrum (𝓞 E) | w.asIdeal ∣ Ideal.span {((M : ℕ) : 𝓞 E)}} ∪
    {P : HeightOneSpectrum (𝓞 E) | P.asIdeal.ramificationIdx ℤ ≠ 1} with hSdef
  have hS : S.Finite := hS1.union hS3
  have hdense := GlobalTheory.Published.chebotarevDegreeOne'.dense (F := E) (Ω := Ω) hS
  refine hdense.mono ?_
  rintro g ⟨w, hwS, hdeg, A, hA, hg⟩
  simp only [hSdef, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hwS
  obtain ⟨hM', hram⟩ := hwS
  have hMw : ((M : ℕ) : 𝓞 E) ∉ w.asIdeal := fun h => hM' (Ideal.dvd_span_singleton.2 h)
  have hp := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 w).2 hdeg
  have hX : ∀ u ∈ X, ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 E) ∉ w.asIdeal := fun u hu h =>
    hMw (GlobalTheory.DenseUsable.natCast_mem_of_dvd w (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hu) _) h)
  refine ⟨w, fun hwX => hX w hwX (Ideal.absNorm_mem _), ?_, ?_, ?_, A, hA, hg⟩
  · refine GlobalTheory.DenseUsable.usPl_of_absNorm_prime hd w hp hram fun h => hMw ?_
    exact GlobalTheory.DenseUsable.natCast_mem_of_dvd w (Dvd.dvd.mul_right (dvd_mul_left _ _) _) h
  · exact fun h => hMw (GlobalTheory.DenseUsable.natCast_mem_of_dvd w (Dvd.dvd.mul_right (dvd_mul_right _ _) _) h)
  · intro u hu hwu
    exact hX u hu (GlobalTheory.DenseUsable.absNorm_mem_of_under_eq w u hwu)

end GlobalTheory.CongL.UnitLim
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL
namespace GlobalTheory.CongL.SatConj

theorem exists_satU_of_under_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∀ w u : HeightOneSpectrum (𝓞 E), IsSplitAt w → u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → (∃ B, SatU U w B) → ∃ B, SatU U u B := by
  intro E _ _ _ a U hU w u hw hu ⟨B, σ, ⟨hirr, f, hf0, hfm, hf⟩, hS⟩
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS.1
  have hf' : ∀ g x, f (σ.ρ g x) = RU E a (GlobalTheory.SplitPts.locPt hw g).1 (f x) := fun g x => by
    have := hf (GlobalTheory.SplitPts.locPt hw g) x
    simpa [GlobalTheory.SplitPts.cLoc_locPt hw g] using this
  have hinj : Function.Injective f := by
    have hk := ((GlobalTheory.CuspRep.isIrreducible_iff _).1 hirr).2 (LinearMap.ker f) (fun g x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [hf', hx, map_zero])
    rcases hk with h | h
    · exact LinearMap.ker_eq_bot.1 h
    · exact absurd (LinearMap.ker_eq_top.1 h) hf0
  have hloc : locU a u = locU a w := by
    unfold locU
    rw [hu]
  have hsu : IsSplitAt u := by
    by_cases h : u = w
    · exact h ▸ hw
    · exact ⟨w, Ne.symm h, hu.symm⟩
  have hKw : ∀ x : UA E a, cLoc u x ∈ GlobalTheory.LFun.KGL u (n := a) → cLoc w x ∈ GlobalTheory.LFun.KGL w (n := a) := by
    intro x hx
    rcases GlobalTheory.BCT.GlobLev.eq_or_eq_conjSrc hu with rfl | rfl
    · exact hx
    · have := GlobalTheory.BCT.GlobLev.integral_conjSrc x _ hx
      rwa [GlobalTheory.SplitPts.conjSrc_conjSrc_cm] at this
  have hfix : ∀ x ∈ locU a u, cLoc u x ∈ GlobalTheory.LFun.KGL u (n := a) → RU E a x (f v) = f v := by
    intro x hx hk
    have hx' : x ∈ locU a w := hloc ▸ hx
    have h1 : σ.ρ (cLoc w x) v = v := by simpa using hv ⟨_, hKw x hk⟩
    have h2 := hf ⟨x, hx'⟩ v
    rw [← h2]
    exact congrArg f h1
  obtain ⟨σ', S, hloc', hS', -⟩ := GlobalTheory.FrameAut.exists_locComp_hasSatGL_heckeVec E a U hU u hsu (f v) (hfm v)
    (fun h => hv0 (hinj (h.trans (map_zero f).symm))) hfix
  exact ⟨S, σ', hloc', hS'⟩

end GlobalTheory.CongL.SatConj
end

section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc GlobalTheory.Mem.Top GlobalTheory.AtG

theorem _root_.GlobalTheory.T.typePrimePeriodRow_of_constructedPointChains : JetSplitAmb → ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd), RowE Q Lk (fun _ D O _ _ => ∀ μ, (μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) → TiesAt D O.ex.errX O.X μ) → Row Q Lk fun 𝒜 _ => Closed (W3 𝒜) fun Fm _ => ∃ C1, (∃ x0, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i, Formalism.L2.G.Adm2InU.UsedTuplesBoundByConstant (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1) ∧ WeightDegreeSizes.familySizeBoundAtTypePrime Fm C1 := by
  first | exact @GlobalTheory.AtG.row_atG_of_jetSplitAmb | exact GlobalTheory.AtG.row_atG_of_jetSplitAmb | (intros; apply GlobalTheory.AtG.row_atG_of_jetSplitAmb <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.conditions_at_standardKernelComparison_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.Pdv.ColNorm I → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → I.StdKer l Z t → GlobalTheory.Pdv.IsEntC t → GlobalTheory.Pdv.Duty t := by
  first | exact @GlobalTheory.Pdv.duty_of_std | exact GlobalTheory.Pdv.duty_of_std | (intros; apply GlobalTheory.Pdv.duty_of_std <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernelSite_away_of_positive_pair : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => KIn t → S.Pos → S.Pair → S.Away) := by
  first | exact @GlobalTheory.TwV.Xc.AwayInd.away_of_pos_pair | exact GlobalTheory.TwV.Xc.AwayInd.away_of_pos_pair | (intros; apply GlobalTheory.TwV.Xc.AwayInd.away_of_pos_pair <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernelSite_contractionIdentity_operatorHalf : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Law → ∀ (d : Dec J std), ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (Φ₀ : ∀ j, MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ →ₛₗ[ι] XspC ((sysS H X std).Pj (j + 1)) ℂ_[D.what₂.places.resChar w]) (τ : ∀ j, (sysS H X std).Lv.comp (j + 1) → ((sysS H X std).Pj (j + 1)).Tup → XspC ((sysS H X std).Pj (j + 1)) ℂ_[D.what₂.places.resChar w] →ₗ[ℂ_[D.what₂.places.resChar w]] XspC ((sysS H X std).Pj (j + 1)) ℂ_[D.what₂.places.resChar w]) (sc : ∀ j, (sysS H X std).Lv.comp (j + 1) → ((sysS H X std).Pj (j + 1)).Tup → ℂ_[D.what₂.places.resChar w]) (sO : ∀ j, (sysS H X std).Lt j → ℂ_[D.what₂.places.resChar w]) (Gm : ∀ j, (sysS H X std).Lt j → ((ex.tw.fm u μ).lat j).V → ((sysS H X std).Pj j).Xsp), ∀ j < D.R.m, ∀ (cK : ℂ_[D.what₂.places.resChar w]) (hN : RankTie (sysS H X std) D j), MoveH S.Y u μ (kaAt X H hT).cmp (fun j La => glInv (sysS H X std) j (BOf d.fd2 j La)) Gm j → TieOpS (Y := S.Y) t u μ (clsAt X H) Gm sO j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN) (ι := ι) (Φ₀ j) → KernelEntryDegreeCondition (Y := S.Y) t u μ (clsAt X H) j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN) → DelYEqH S.Y (fun j La' => VOf ℂ_[D.what₂.places.resChar w] d.fd2 (ltC S.g S.hLT) j La') τ j → (∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → cK * (Formalism.L2.G.Pend.cA (sysS H X std) ℂ_[D.what₂.places.resChar w] j (BOf d.fd2 j La) * sO j La) * ι (d.uS S j La) * ι (d.uT S j La') = sc j La'.1 La'.2) → DelPolAt (Y := S.Y) t u μ (clsAt X H) (kaAt X H hT).cmp (fun j => clsAt X H (j + 1)) (phiH D Φ₀ τ sc) (srOf S.Y) j cK) := by
  first | exact @GlobalTheory.TwV.DelB.delPolAt_site | exact GlobalTheory.TwV.DelB.delPolAt_site | (intros; apply GlobalTheory.TwV.DelB.delPolAt_site <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.trueColumnChoice_stepZero_charts_good : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.StdF l Z u F → ∃ Kc : Fam I l Z u a 0 (Nat.zero_le _) (badQ (I.rec7 l Z) Q) (fun _ => ()), (ReadsOne I l Z u a 0 (Nat.zero_le _) (fun _ => ()) Kc ∧ ∀ β, FunKilled (Kc β).lev (X.piT u) ∧ ∃ n : ℕ, 0 < n ∧ ∀ κ, (Kc β).lev.chi κ ^ n = 1) ∧ (∀ β, (Kc β).lev.Lb = F.to0.cls0.lev.Lb ∧ (Kc β).lev.Uloc = F.to0.cls0.lev.Uloc ∧ (Kc β).lev.U = F.to0.cls0.lev.U ∧ ∀ (κ : (Kc β).lev.U) (κ' : F.to0.cls0.lev.U), κ.1 = κ'.1 → (Kc β).lev.chi κ = F.to0.cls0.lev.chi κ') ∧ ∀ c, ∃ κ : F.to0.cls0.lev.U, ((Kc ((fun _ : (I.stp u a 0).Cl => ()) (I.eCls0 l u a c))).y ⟨I.eCls0 l u a c, rfl⟩).1 = (F.to0.cls0.y c).1 * κ.1 ∧ F.to0.cls0.lev.chi κ = 1 ∧ ∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1 := by
  first | exact @GlobalTheory.TwU.AtTrue.charts_zero_good | exact GlobalTheory.TwU.AtTrue.charts_zero_good | (intros; apply GlobalTheory.TwU.AtTrue.charts_zero_good <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts

theorem _root_.GlobalTheory.T.infinityType_etaTilde_at_cmTypeEmbeddings_eq_half : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C), NCharTied D cf C tp → ∀ t, D.naut.infG D.naut.etaT (Formalism.L2.embT D t) = {(1 / 2 : ℂ)} := by
  first | exact @GlobalTheory.EtaInfType.main | exact GlobalTheory.EtaInfType.main | (intros; apply GlobalTheory.EtaInfType.main <;> assumption)
end
