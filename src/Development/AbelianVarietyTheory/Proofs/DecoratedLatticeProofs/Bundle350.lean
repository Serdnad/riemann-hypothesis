module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle272
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle328
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle330
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle331
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle332
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceSchwartzBruhatActsAsSupportedCombinati
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle335
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle333
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
import Mathlib.RingTheory.PiTensorProduct
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
public import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.DoubledUnramifiedFrames
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.StepData (XIx Ix latOf box LatFrame)
open GlobalTheory.LocMod (GAt PinGBy ofSplit MovedTo)
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastPair lastKer)
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedLocalFrameSequences (IsFockOver StepsAll vec atW IsMoved InAt InvOnUnits IsBesFrame IsJacFrame FrameMapsPrefix jacLat ptBF ptFB)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.Isom

namespace GlobalTheory.OverTgt

variable {D : D7}

def colRow (S T : HSp D) (r : Fin S.rank → AE D) : (Fin T.rank → AE D) →+ WO S T where
  toFun y := Matrix.of fun i j => y i * r j
  map_zero' := by ext i j; simp
  map_add' y y' := by ext i j; simp [add_mul]

theorem mul_colRow {S T T' : HSp D} (M : Mx D T'.rank T.rank) (r : Fin S.rank → AE D) (y : Fin T.rank → AE D) :
    HMul.hMul M (colRow S T r y) = colRow S T' r (M *ᵥ y) := by
  ext i j
  simp [colRow, Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

theorem gen_eq_colRow {S T : HSp D} (α : AF D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    (Matrix.of fun i j => α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) =
      colRow S T (fun j => incA D (a * ∑ k, star (s k) * S.gram k j)) (fun i => α ⊗ₜ[D.host.F] (1 * t i)) := by
  ext i j
  simp only [colRow, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.of_apply]
  change _ = (α ⊗ₜ[D.host.F] (1 * t i)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] _)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  congr 1
  ring

theorem colRow_mem_latO {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Lat T} {P : GlobalTheory.FinPl.Pl D → Prop}
    {a : D.host.E} (ha : a ∈ D.host.AA) {s : Fin S.rank → D.host.E} (hs : s ∈ LS) {y : Fin T.rank → AE D}
    (hy : y ∈ latV T LT P) :
    colRow S T (fun j => incA D (a * ∑ k, star (s k) * S.gram k j)) y ∈ latO S T LS (LT : Set _) P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    rw [← gen_eq_colRow]
    exact AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, s, hs, x, hx, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [map_add]; exact add_mem hz hz'
  | neg z _ hz => rw [map_neg]; exact neg_mem hz

theorem mul_mem_latO {S T T' : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Lat T} {LT' : Lat T'}
    {P : GlobalTheory.FinPl.Pl D → Prop} (M : Mx D T'.rank T.rank) (hM : ∀ y ∈ latV T LT P, M *ᵥ y ∈ latV T' LT' P) {w : WO S T}
    (hw : w ∈ latO S T LS (LT : Set _) P) : HMul.hMul M w ∈ latO S T' LS (LT' : Set _) P := by
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩ := hz
    rw [gen_eq_colRow, mul_colRow]
    exact colRow_mem_latO ha hs (hM _ (AddSubgroup.subset_closure ⟨α, hαi, hα, 1, rfl, t, ht, rfl⟩))
  | zero => rw [Matrix.mul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mul_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mul_neg]; exact neg_mem hz

section Isometry

variable {V V' : HSp D} (I : IsoMat V V') (S : HSp D)

variable {Λ : AddSubgroup (WO S V)} {Λ' : AddSubgroup (WO S V')} (hΛ : ∀ u, u ∈ Λ ↔ I.phi S u ∈ Λ')
include hΛ

end Isometry

section Frames

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {S T T₀ : HSp D} (d : HypDec T T₀ 0) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  (α : GlobalTheory.FinPl.Frame p S n') (β : GlobalTheory.FinPl.Frame p T n) (β₀ : GlobalTheory.FinPl.Frame p T₀ n)

end Frames

end GlobalTheory.OverTgt
end
end

section

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.SplitProj

open Formalism.IndefR.Datum Formalism.L2.Theta

section Base

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_near (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletion F) (n : ℕ) :
    ∃ k : F, Valued.v (c - algebraMap F _ k) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  set r : v.adicCompletion F := algebraMap F _ (π ^ n) with hr_def
  have hr : Valued.v r = WithZero.exp (-(n : ℤ)) := by
    rw [hr_def]
    refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (π ^ n)).trans ?_
    rw [map_pow, hπ]
    rw [← WithZero.exp_nsmul]
    congr 1
    simp
  have hr0 : Valued.v r ≠ 0 := by rw [hr]; exact WithZero.exp_ne_zero
  have hN : {y : v.adicCompletion F | Valued.v (c - y) < Valued.v r} ∈ nhds c := by
    have ho := (Valued.isOpen_ball (v.adicCompletion F) (Valued.v.restrict r)).preimage
      (continuous_const.sub continuous_id : Continuous fun y : v.adicCompletion F => c - y)
    simp only [Set.preimage_setOf_eq, Valuation.restrict_lt_iff] at ho
    refine ho.mem_nhds ?_
    show Valued.v (c - c) < _
    rw [sub_self, map_zero]
    exact zero_lt_iff.2 hr0
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := F) v).mem_nhds hN
  exact ⟨k, (le_of_lt hk).trans_eq hr⟩

theorem afIso_one_tmul_apply (a : FiniteAdeleRing (𝓞 F) F) (P : HeightOneSpectrum (𝓞 E)) :
    GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P = GlobalTheory.AdeleBaseChange.adMap F E a P := by
  have key : ∀ n : ℕ, Valued.v (GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P - GlobalTheory.AdeleBaseChange.adMap F E a P) ≤
      WithZero.exp (-(n : ℤ)) := fun n => by
    obtain ⟨k, hk⟩ := exists_near (P.under (𝓞 F)) (a (P.under (𝓞 F))) n
    have h1 := (GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E).choose_spec.2.2.2 a k P n hk
    have h2 : Valued.v (GlobalTheory.AdeleBaseChange.adMap F E a P - algebraMap E _ (algebraMap F E k)) ≤
        WithZero.exp (-(n : ℤ)) := by
      rw [GlobalTheory.AdeleBaseChange.adMap_apply, ← GlobalTheory.AdeleBaseChange.locMap_algebraMap, ← map_sub]
      exact GlobalTheory.AdeleBaseChange.locMap_valued P n _ hk
    have e : GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P - GlobalTheory.AdeleBaseChange.adMap F E a P =
        (GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P - algebraMap E _ (algebraMap F E k)) -
          (GlobalTheory.AdeleBaseChange.adMap F E a P - algebraMap E _ (algebraMap F E k)) := by ring
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le h1 h2)
  by_contra hne
  have h0 : Valued.v (GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P - GlobalTheory.AdeleBaseChange.adMap F E a P) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact sub_ne_zero.2 hne
  have h2 := key (1 - WithZero.log (Valued.v (GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P -
    GlobalTheory.AdeleBaseChange.adMap F E a P))).toNat
  conv_lhs at h2 => rw [← WithZero.exp_log h0]
  rw [WithZero.exp_le_exp] at h2
  omega

end Base

variable {D : Formalism.BasicNotions.D7}

theorem toAd_eq_afIso (w : GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.Ef D) :
    GlobalTheory.StdFrames.toAd D w = GlobalTheory.Mem.Col2.afIso D.host.F D.host.E w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul x a =>
    rw [GlobalTheory.StdFrames.toAd_spec]
    have e : (x ⊗ₜ[D.host.F] a : Formalism.L2.DIV.AfE D.host.F D.host.E) =
        (x ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] a) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, map_mul, GlobalTheory.Mem.Col2.afIso_tmul_one]
    congr 1
    exact FiniteAdeleRing.ext _ fun P => (afIso_one_tmul_apply a P).symm
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem cpt_eq_adAt (Q : HeightOneSpectrum (𝓞 D.host.E)) (w : GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.Ef D) :
    GlobalTheory.StdFrames.cpt Q w = GlobalTheory.Mem.Col2.adAt D.host.F Q w := by
  show Formalism.UG.evalV D.host.E Q (GlobalTheory.StdFrames.toAd D w) = Formalism.UG.evalV D.host.E Q (GlobalTheory.Mem.Col2.afIso D.host.F D.host.E w)
  rw [toAd_eq_afIso]

theorem pr_eq_of_adAt : ∀ {D : Formalism.BasicNotions.D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (z : Formalism.L2.Theta.AE D) (x : D.host.E), GlobalTheory.Mem.Col2.adAt D.host.F PP (Formalism.IndefR.Datum.toEAf D z) = algebraMap D.host.E (PP.adicCompletion D.host.E) x → q.pr z = q.pr (Formalism.L2.Theta.incA D x) := by
  intro D k _ _ _ _ q PP he z x hz
  have hx : GlobalTheory.StdFrames.cpt PP (toEAf D (incA D x)) = algebraMap D.host.E (PP.adicCompletion D.host.E) x :=
    (cpt_eq_adAt PP _).trans (GlobalTheory.Mem.Col2.adAt_inclE D.host.F PP x)
  have hz' : GlobalTheory.StdFrames.cpt PP (toEAf D z) = algebraMap D.host.E (PP.adicCompletion D.host.E) x :=
    (cpt_eq_adAt PP _).trans hz
  have h1 : toEAf D (q.e * z) = toEAf D (q.e * incA D x) := by
    rw [RingHom.map_mul, RingHom.map_mul]
    refine GlobalTheory.StdFrames.cpt_ext fun Q => ?_
    rw [RingHom.map_mul, RingHom.map_mul]
    by_cases hQ : Q = PP
    · rw [hQ, hx, hz']
    · rw [(GlobalTheory.StdFrames.cpt_of_isIdemAt he).2 Q hQ, zero_mul, zero_mul]
  have h2 : q.pr (q.e * z - q.e * incA D x) = 0 :=
    q.pr_eq_zero_of_toEAf he _ (by rw [RingHom.map_sub, h1, sub_self])
  rw [RingHom.map_sub, sub_eq_zero, ← q.sec_pr, ← q.sec_pr, q.pr_sec, q.pr_sec] at h2
  exact h2

end GlobalTheory.SplitProj

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl




namespace GlobalTheory.FinPl.Patch

open GlobalTheory.FinPlLoc

variable {D : D7}

theorem mul_eq_zero_of_ne {x w : Pl D} (h : w ≠ x) {a b : AE D} (ha : a ∈ idAt D (· = x)) (hb : b ∈ idAt D (· = w)) :
    a * b = 0 := by
  apply eq_zero_of_comp
  · rw [map_mul, infPart_of_idAt ha, zero_mul]
  · intro v
    rw [map_mul]
    by_cases hv : v = x
    · rw [compAt_of_idAt hb (w := v) (fun h' => h (h'.symm.trans hv)), mul_zero]
    · rw [compAt_of_idAt ha (w := v) hv, zero_mul]

theorem mulVec_eq_of_ne {S : HSp D} {x w : Pl D} (h : w ≠ x) {g : GA D S} (hg : g ∈ grpAt S (· = x))
    {y : Fin S.rank → AE D} (hy : ∀ i, y i ∈ idAt D (· = w)) : mt S g *ᵥ y = y := by
  have hg' := (mem_congGrp _ g).1 hg
  have h0 : (mt S g - 1) *ᵥ y = 0 := by
    funext i
    show ∑ j, (mt S g - 1) i j * y j = 0
    exact Finset.sum_eq_zero fun j _ => mul_eq_zero_of_ne h (hg' i j) (hy j)
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
  exact h0

theorem latV_eq_off {S : HSp D} {x w : Pl D} (h : w ≠ x) {g : GA D S} (hg : g ∈ grpAt S (· = x)) {L M : Lat S}
    (hm : Moves S g L M (· = w)) : latV S M (· = w) = latV S L (· = w) := by
  ext y
  constructor
  · intro hy
    have hid := latV_idAt hy
    rw [hm y hid, mulVec_eq_of_ne h hg hid]
    exact hy
  · intro hy
    have hid := latV_idAt hy
    have := (hm y hid).1 hy
    rwa [mulVec_eq_of_ne h hg hid] at this

theorem latV_le_of_moves {S : HSp D} {P : Pl D → Prop} {g : GA D S} {L M M' : Lat S} (hm : Moves S g L M P)
    (hm' : Moves S g L M' P) : latV S M P ≤ latV S M' P := by
  intro y hy
  have hid := latV_idAt hy
  have hz : ∀ i, (mt S g⁻¹ *ᵥ y) i ∈ idAt D P := fun i => by
    show ∑ j, mt S g⁻¹ i j * y j ∈ idAt D P
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hid j)
  have he : mt S g *ᵥ (mt S g⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, ← FinPlLoc.mt_mul, mul_inv_cancel, FinPlLoc.mt_one, Matrix.one_mulVec]
  have h1 := (hm _ hz).2 (by rw [he]; exact hy)
  have h2 := (hm' _ hz).1 h1
  rwa [he] at h2

theorem patch : ∀ (D : D7) (S : HSp D) (L L' : Lat S), IsSelfDualC S L → IsSelfDualC S L' → ∀ Z : Finset (Pl D),
    ∃ M : Lat S, IsSelfDualC S M ∧ (∀ x ∈ Z, latV S M (· = x) = latV S L' (· = x)) ∧
      ∀ x, x ∉ Z → latV S M (· = x) = latV S L (· = x) := by
  classical
  intro D S L L' hL hL' Z
  induction Z using Finset.induction_on with
  | empty => exact ⟨L, hL, fun x hx => absurd hx (Finset.notMem_empty x), fun _ _ => rfl⟩
  | insert x Z hx ih =>
    obtain ⟨M, hM, h1, h2⟩ := ih
    obtain ⟨g, hg, hgm⟩ := GlobalTheory.T.selfDualLattices_conjugate_at_finitePlace D S M L' hM hL' x
    obtain ⟨M', hM', hmv⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D S M hM).1 g
    refine ⟨M', hM', fun w hw => ?_, fun w hw => ?_⟩
    · by_cases hwx : w = x
      · subst hwx
        exact le_antisymm (latV_le_of_moves (hmv _) hgm) (latV_le_of_moves hgm (hmv _))
      · rw [latV_eq_off hwx hg (hmv _)]
        exact h1 w ((Finset.mem_insert.1 hw).resolve_left hwx)
    · rw [Finset.mem_insert, not_or] at hw
      rw [latV_eq_off hw.1 hg (hmv _)]
      exact h2 w hw.2

end GlobalTheory.FinPl.Patch
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel


theorem _root_.GlobalTheory.T.splitPlaceIdempotent_mul_eq_zero_of_ne_place : ∀ (D : D7) (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (q : SplitPt D k) (q' : SplitPt D k'), q.v ≠ q'.v → q.e * q'.e = 0 := by
  first | exact @GlobalTheory.SplitOrth.split_mul_split | exact GlobalTheory.SplitOrth.split_mul_split | (intros; apply GlobalTheory.SplitOrth.split_mul_split <;> assumption)
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.wittLeviDiagonal_mem_latticeStabilizer_of_units : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), IsSelfDualC S L → MonoAt d L L₀ v → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → d.levi t ∈ grpAt S (· = v) → (∀ i, t.1 i i - 1 ∈ intAt D (· = v) ∧ (t⁻¹).1 i i - 1 ∈ intAt D (· = v)) → InK S L (· = v) (d.levi t) := by
  first | exact @GlobalTheory.FinPl.LeviUnitK.inK_levi | exact GlobalTheory.FinPl.LeviUnitK.inK_levi | (intros; apply GlobalTheory.FinPl.LeviUnitK.inK_levi <;> assumption)
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.completed_hom_lattice_stable_split_idempotent : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S T : HSp D) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T) (u : WO S T), u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) → (Matrix.of fun i j => q.e * u i j : WO S T) ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) ∧ ∀ i j, (q.e + cA D q.e) * u i j = u i j := by
  first | exact @GlobalTheory.SplitVac.idem_latO | exact GlobalTheory.SplitVac.idem_latO | (intros; apply GlobalTheory.SplitVac.idem_latO <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel


theorem _root_.GlobalTheory.T.homLatticeAtPlaces_congr_localLattices : ∀ (D : D7) (S T : HSp D) (N M : Lat S) (N' M' : Lat T), IsSelfDualC S N → IsSelfDualC S M → IsSelfDualC T N' → IsSelfDualC T M' → ∀ (P : Pl D → Prop), (∀ p, P p → latV S N (· = p) = latV S M (· = p) ∧ latV T N' (· = p) = latV T M' (· = p)) → latO S T (N : Set _) (N' : Set _) P = latO S T (M : Set _) (M' : Set _) P := by
  first | exact @GlobalTheory.FinPl.LatCong.latO_congr | exact GlobalTheory.FinPl.LatCong.latO_congr | (intros; apply GlobalTheory.FinPl.LatCong.latO_congr <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SBHalfAt

theorem isSBHalf_extFun_latO : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S T : HSp D) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT →
    ∀ Ψ ∈ SB (Matrix n n' k),
      IsSBHalf p.e (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v))
        (extFun α β Ψ) := by
  intro D k _ _ _ _ p S T n n' _ _ _ _ α β LS LT hS hT Ψ hΨ
  exact GlobalTheory.FinPl.CombProof.isSBHalf_extFun D k p n n' S T α β LS LT hS hT Ψ hΨ

end GlobalTheory.FinPl.SBHalfAt
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OffPlaceRed

theorem pr_add_conj_eq_zero {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (a : Formalism.L2.Theta.AE D)
    (h : a * (q.e + cA D q.e) = 0) : q.pr a = 0 := by
  have h1 : q.pr q.e = 1 := by
    have h2 := q.pr_sec 1
    have h3 := q.sec_pr 1
    rw [map_one, mul_one] at h3
    rwa [h3] at h2
  have h4 : q.pr (cA D q.e) = 0 := by
    have := congrArg q.pr q.split.2.1
    rwa [map_mul, h1, one_mul, map_zero] at this
  have := congrArg q.pr h
  rwa [map_mul, map_add, h1, h4, add_zero, mul_one, map_zero] at this

theorem bc_eq_one_of_isRed {S κ k : Type} [CommRing S] [CommRing κ] [Field k] [ValuativeRel k] {φ : S →+* κ}
    {ψ : S →+* k} (hred : GlobalTheory.FunObj.Comparison₂.IsRed φ ψ) {n : ℕ} (m : GL (Fin n) S) (h : Formalism.UG.bc ψ m = 1) :
    Formalism.UG.bc φ m = 1 := by
  apply Units.ext
  ext i j
  have h6 : ψ (m.val i j) = (1 : Matrix (Fin n) (Fin n) k) i j :=
    congrArg (fun x : GL (Fin n) k => x.val i j) h
  show φ (m.val i j) = (1 : Matrix (Fin n) (Fin n) κ) i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq] at h6 ⊢
    have h7 := (hred.ker (m.val i i - 1)).2 (by
      rw [map_sub, map_one, h6, sub_self, map_zero]; exact zero_lt_one)
    rwa [map_sub, map_one, sub_eq_zero] at h7
  · rw [Matrix.one_apply_ne hij] at h6 ⊢
    refine (hred.ker (m.val i j)).2 ?_
    rw [h6, map_zero]; exact zero_lt_one

theorem bc_comp_eq_one {S A k : Type} [CommRing S] [CommRing A] [CommRing k] (ι : S →+* A) (π : A →+* k) {n : ℕ}
    (m : GL (Fin n) S) (β x : GL (Fin n) A) (hx : β * Formalism.UG.bc ι m * β⁻¹ = x) (h : Formalism.UG.bc π x = 1) :
    Formalism.UG.bc (π.comp ι) m = 1 := by
  rw [← hx, map_mul, map_mul, map_inv, mul_inv_eq_one, mul_eq_left] at h
  exact h

theorem redFn_eq_one_of_suppAt : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (e : Formalism.L2.Theta.AE D), (e + cA D e) * (q.e + cA D q.e) = 0 → ∀ (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (g : GA D V), Formalism.L2.Theta.SuppAt e V g → finE V g ∈ St β → redFn β PP (finE V g) = 1 := by
  intro D k _ _ _ _ q PP hq e he V β g hg hst
  obtain ⟨π', hπ, hred, -, -⟩ := GlobalTheory.FinPl.SplitPt.exists_lift_isRed D k q PP hq
  obtain ⟨m, hm⟩ := hst
  have h0 : q.pr (e + cA D e) = 0 := pr_add_conj_eq_zero q _ he
  have h1 : (finE V g).val.map π' = 1 := by
    ext i j
    have h2 : q.pr ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
      rw [← hg i j, map_mul, h0, zero_mul]
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h2
    show π' (toEAf D (Formalism.L2.Theta.mt V g i j)) = _
    rw [hπ, h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h3 : Formalism.UG.bc π' (finE V g) = 1 := Units.ext h1
  rw [← hm, redFn_frGL]
  exact bc_eq_one_of_isRed hred m (bc_comp_eq_one _ π' m β _ hm h3)

end GlobalTheory.OffPlaceRed

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seeSawTuple_kernelBack_of_classKernelData : ∀ (D : D7) (c : Comm D) (t : Tup c) (ρ : RealD c) (A : ClsK ρ t), c.Is → t.Is → ρ.Is → A.Is → (∀ j, j < D.R.m → t.cK j ≠ 0) → t.KBack := by
  first | exact @GlobalTheory.SeeSaw.kBack_of_classData | exact GlobalTheory.SeeSaw.kBack_of_classData | (intros; apply GlobalTheory.SeeSaw.kBack_of_classData <;> assumption)
end
