module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle271
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle473
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle341
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle340
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle416
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle474
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle440
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagLiftTranslationMemTypeLevelCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle463
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle027
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle475
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle061
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle087
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle476
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle290
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle022
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle477
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle480
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelContainsDeepCongruenceAtBadPrime
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeFunctionalsEqMovedLevelFunctionals
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
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.stdFrameLevelSubgroup_bounded_open_hyperspecial : ∀ (D : D7) (n : ℕ) (Ld : Formalism.L2.DIV.LevDat D.host.E ℂ n), stdJ Ld ≤ ReciprocityTheory.Aut.Umax D.host.E n ∧ (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E n N κ → ∃ h : κ ∈ stdJ Ld, stdX Ld ⟨κ, h⟩ = 1) ∧ ∀ B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))), (∀ PP, PP ∈ Ld.Pg ∨ PP ∈ Ld.Q → ∀ v, NG.OverPl PP v → v ∈ B) → NG.HypOutside (stdJ Ld) (stdX Ld) B := by
  first | exact @GlobalTheory.MtIn.OpenLev.stdJ_open | exact GlobalTheory.MtIn.OpenLev.stdJ_open | (intros; apply GlobalTheory.MtIn.OpenLev.stdJ_open <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.match_tupleChart_memberChart : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 B.host.F))) (i : ℕ), i ≤ B.R.m → 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → ∃ (c0f : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → (I.stp u I.mu0 i).Cl) (t : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → GA B (B.R.N i)), (∀ β, ∃ p : DecoF B.fields.E (B.R.N i) ∅ ∅ ∅, PtOf (t β) p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N i)) ∧ (∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), ((B.T u : 𝓞 B.host.F) ∈ v.asIdeal ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) → bc (prV (E := B.host.E) v) (t β) = 1) ∧ (a = I.mu0 → ∀ β, t β = 1) ∧ ∀ β, ∃ c, GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = β ∧ ∀ s : GA B (B.R.N i), (∀ v ∈ Q, bc (prV (E := B.host.E) v) s = 1) → (∀ κ, GlobalTheory.Mem.Col2.TC.ChTw.LocMv I u a i c ((t β)⁻¹ * s * t β) κ → ∃ κ0, GlobalTheory.Mem.Col2.TC.ChTw.LocMv I u I.mu0 i (c0f β) s κ0 ∧ (I.stp u a i).chr c.1 κ = (I.stp u I.mu0 i).chr (c0f β).1 κ0) ∧ (∀ κ0, GlobalTheory.Mem.Col2.TC.ChTw.LocMv I u I.mu0 i (c0f β) s κ0 → ∃ κ, GlobalTheory.Mem.Col2.TC.ChTw.LocMv I u a i c ((t β)⁻¹ * s * t β) κ) := by
  first | exact @GlobalTheory.Mem.Col2.TC.ChTw.Match.match_idx | exact GlobalTheory.Mem.Col2.TC.ChTw.Match.match_idx | (intros; apply GlobalTheory.Mem.Col2.TC.ChTw.Match.match_idx <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.decoratedRowLattices_flagLevel_rightTranslation : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r),
    I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG →
    ∀ (t : TupU I U) (q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q),
    ∃ u : ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp,
      (∀ h : Bridge.Gf X.toD7.sp.X', RowAd.decoAd X I t (h * (q : Bridge.Gf X.toD7.sp.X')) =
        ((1 : Formalism.L2.Col.UF X.B.fields.E (X.B.R.N X.B.R.m - 1)),
          (u : Formalism.L2.Col.GLG (E := X.B.fields.E) (n := X.B.R.N X.B.R.m - 1) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)) *
            (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R)
              (eG.symm (rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _)))))⁻¹) •
          RowAd.decoAd X I t h) ∧
      X.toD7.what₂.embLL (((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv.chr u : X.B.fields.Kˣ) : X.B.fields.K) =
        (((levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch q : ℂˣ) : ℂ) := by
  exact @GlobalTheory.Mem.R3.RowDeco.deco_tie
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.exists_equiv_rowStage_unitary_standard_adelic : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), I.Ok →
    ∃ e : Formalism.L2.Col.UAd X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ≃* Bridge.Gf X.toD7.sp.X',
      ∀ x, RowAd.ptE X (e x) = x.1 := by
  first | exact @GlobalTheory.Mem.R3.RowStdGrp.ptE_equiv | exact GlobalTheory.Mem.R3.RowStdGrp.ptE_equiv | (intros; apply GlobalTheory.Mem.R3.RowStdGrp.ptE_equiv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.flagLift_translation_mem_typeLevel_character : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k →
    ∀ κ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q,
      ∃ hh : (LiftBrg.ActQ.redZ X I U L i t A k κ)⁻¹ *
          Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_nV X.B.R) (LiftBrg.ActQ.redQ X I U L eG i t κ) ∈
          (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp,
        X.toD7.what₂.embLL (((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.chr ⟨_, hh⟩ : X.B.fields.Kˣ) : X.B.fields.K) =
          (((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).ch κ : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.ActQ.inv_redZ_mul_g0Hat_type | exact GlobalTheory.Mem.R3.LiftBrg.ActQ.inv_redZ_mul_g0Hat_type | (intros; apply GlobalTheory.Mem.R3.LiftBrg.ActQ.inv_redZ_mul_g0Hat_type <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.AdT

section Split

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S Q : Finset (HeightOneSpectrum (𝓞 E))}


open Classical in
def compVal (Λ : LevFam E K n S) (Θ : LevQFam E K n Q) (k1 : ↥Λ.grp) (k2 : ↥Θ.grp) (p : HeightOneSpectrum (𝓞 E)) : Kˣ :=
  if h : p ∈ S then (Λ ⟨p, h⟩).lam ⟨k1.1 ⟨p, h⟩, k1.2 _ (Set.mem_univ _)⟩
  else if h' : p ∈ Q then (Θ ⟨p, h'⟩).lam ⟨k2.1 ⟨p, h'⟩, k2.2 _ (Set.mem_univ _)⟩ else 1

theorem compVal_left (Λ : LevFam E K n S) (Θ : LevQFam E K n Q) (k1 : ↥Λ.grp) (k2 : ↥Θ.grp) {p : HeightOneSpectrum (𝓞 E)} (h : p ∈ S) :
    compVal Λ Θ k1 k2 p = (Λ ⟨p, h⟩).lam ⟨k1.1 ⟨p, h⟩, k1.2 _ (Set.mem_univ _)⟩ := by
  unfold compVal
  rw [dif_pos h]

theorem compVal_right (Λ : LevFam E K n S) (Θ : LevQFam E K n Q) (k1 : ↥Λ.grp) (k2 : ↥Θ.grp) {p : HeightOneSpectrum (𝓞 E)} (h : p ∉ S)
    (h' : p ∈ Q) : compVal Λ Θ k1 k2 p = (Θ ⟨p, h'⟩).lam ⟨k2.1 ⟨p, h'⟩, k2.2 _ (Set.mem_univ _)⟩ := by
  unfold compVal
  rw [dif_neg h, dif_pos h']


open Classical in
theorem prod_compVal (hd : Disjoint S Q) (Λ : LevFam E K n S) (Θ : LevQFam E K n Q) (k1 : ↥Λ.grp) (k2 : ↥Θ.grp) :
    ∏ p ∈ S ∪ Q, compVal Λ Θ k1 k2 p = Λ.chr k1 * Θ.chr k2 := by
  have e1 : Λ.chr k1 = _ := piChar_apply (fun w => (Λ w).H) (fun w => (Λ w).lam) k1
  have e2 : Θ.chr k2 = _ := piChar_apply (fun w => (Θ w).H) (fun w => (Θ w).lam) k2
  rw [e1, e2, Finset.prod_union hd, ← Finset.prod_coe_sort S, ← Finset.prod_coe_sort Q]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun w _ => ?_) (Finset.prod_congr rfl fun w _ => ?_)
  · exact dif_pos w.2
  · exact (dif_neg (Finset.disjoint_right.1 hd w.2)).trans (dif_pos w.2)

end Split
end GlobalTheory.Mem.Col2.AdT

namespace GlobalTheory.Mem.Col2.AdT

section Cong

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem congE_mul_one {P : HeightOneSpectrum (𝓞 E)} {c : ℕ} {k g g' : Sp E n ≃ₗ[E] Sp E n}
    (hk : k ∈ GLint E n P) (hkg : k * g' = 1) (h : CongE P c g g') : CongE P c (k * g) 1 := by
  intro x hx
  have e1 : (k * g) x - (1 : Sp E n ≃ₗ[E] Sp E n) x = k (g x - g' x) := by
    rw [map_sub, ← LinearEquiv.mul_apply k g', hkg]
    rfl
  rw [e1, ← map_smul]
  exact (hk _).2 (h x hx)

end Cong
end GlobalTheory.Mem.Col2.AdT

namespace GlobalTheory.Mem.Col2.AdT

variable {B : Base} {X : PreX B.toPre}

theorem chiInv_at_type (I : TC B X) (hOk : I.Ok) (a : I.ι) (i : ℕ) (al : (I.idx a).β i) (P : SBof I a)
    (hP : P.1 ∈ (B.primes X).vGs) (gP g'P : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (r : AutY B.fields B.R i)
    (hr : r ∈ Loc.Cbe (Jat (Pr := B.primes X) (I.cst a).sharp i P.1) ((I.idx a).h i al P))
    (hrx : ∀ x, r (Loc.inX B.fields.E (B.R.N i) (cOf B.R i) x) = Loc.inX B.fields.E (B.R.N i) (cOf B.R i) (gP x))
    (κw : GL (Fin (B.R.N i)) (𝓞 B.fields.E ⧸ P.1.asIdeal)) (hκw : κw ∈ (((I.idx a).levG i al) ⟨P.1, hP⟩).H)
    (hred' : ∀ x ∈ stdAt B.fields.E (B.R.N i) P.1, redV P.1 (g'P x) = (κw⁻¹).1.mulVec (redV P.1 x))
    (hcong : CongE P.1 ((I.cst a).D P) gP g'P) :
    chiInv I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P) r =
      (((((I.idx a).levG i al) ⟨P.1, hP⟩).lam ⟨κw, hκw⟩ : B.fields.Kˣ) : B.fields.K)⁻¹ := by
  have hL := hOk.idx_ok a
  have hD : (I.cst a).D P = 1 := hL.depthG P hP
  have hred : ∀ x ∈ stdAt B.fields.E (B.R.N i) P.1, redV P.1 (gP x) = (κw⁻¹).1.mulVec (redV P.1 x) := by
    intro x hx
    rw [← hred' x hx]
    have h1 := (mem_localization_standardLattice _ _).1 (hcong x hx)
    rw [hD, pow_one] at h1
    have hq0 : ((qOf P.1 : ℕ) : B.fields.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P.1
    funext l
    have e1 : gP x l = g'P x l + (qOf P.1 : B.fields.E) * (((qOf P.1 : ℕ) : B.fields.E)⁻¹ • (gP x - g'P x)) l := by
      rw [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
      field_simp
      ring
    show redP P.1 (gP x l) = redP P.1 (g'P x l)
    rw [e1]
    exact GlobalTheory.LastSteps.redP_add_q (h1 l)
  have hc := hL.chrG i al ⟨P.1, hP⟩ (⟨κw, hκw⟩)⁻¹ gP r hr hrx hred
  exact hc.symm.trans ((congrArg Units.val (map_inv (((I.idx a).levG i al) ⟨P.1, hP⟩).lam _)).trans (Units.val_inv_eq_inv_val _))

end GlobalTheory.Mem.Col2.AdT

namespace GlobalTheory.Mem.Col2.AdT

variable {B : Base} {X : PreX B.toPre}

theorem chiInv_at_twist (I : TC B X) (hOk : I.Ok) (a : I.ι) (i : ℕ) (hi : i < B.R.m) (al : (I.idx a).β i) (P : SBof I a)
    (hQ : P.1 ∈ I.Q a) (gP g'P : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (r : AutY B.fields B.R i)
    (hr : r ∈ Loc.Cbe (Jat (Pr := B.primes X) (I.cst a).sharp i P.1) ((I.idx a).h i al P))
    (hrx : ∀ x, r (Loc.inX B.fields.E (B.R.N i) (cOf B.R i) x) = Loc.inX B.fields.E (B.R.N i) (cOf B.R i) (gP x))
    (κQ : ↥(GLint B.fields.E (B.R.N i) P.1)) (hκQ : κQ ∈ (((I.idx a).levQ i al) ⟨P.1, hQ⟩).H)
    (hg' : g'P = (κQ⁻¹).1) (hcong : CongE P.1 ((I.cst a).D P) gP g'P) :
    chiInv I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P) r =
      (((((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam ⟨κQ, hκQ⟩ : B.fields.Kˣ) : B.fields.K)⁻¹ := by
  have hL := hOk.idx_ok a
  have hg : gP ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp i P.1 ((I.idx a).h i al P) := ⟨r, hr, hrx⟩
  let gI : ↥(GLint B.fields.E (B.R.N i) P.1) := ⟨gP, hL.int i al P hg⟩
  have hH : gI ∈ (((I.idx a).levQ i al) ⟨P.1, hQ⟩).H := by
    rw [hL.grpQ i al ⟨P.1, hQ⟩]
    exact Subgroup.mem_subgroupOf.2 hg
  have hc := hL.chrQ i al ⟨P.1, hQ⟩ ⟨gI, hH⟩ r hr hrx
  have hkg : κQ.1 * g'P = 1 := by
    rw [hg']
    exact congrArg Subtype.val (mul_inv_cancel κQ)
  have hcd : CongE P.1 ((I.cst a).D P) (κQ * gI).1 1 := congE_mul_one (g := gP) κQ.2 hkg hcong
  obtain ⟨hdH, hdl⟩ := levQ_deep I hOk a i hi al P hQ (κQ * gI) hcd
  have e2 : (⟨gI, hH⟩ : ↥(((I.idx a).levQ i al) ⟨P.1, hQ⟩).H) = (⟨κQ, hκQ⟩)⁻¹ * ⟨κQ * gI, hdH⟩ :=
    Subtype.ext (by show gI = κQ⁻¹ * (κQ * gI); group)
  have h4 : (((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam ((⟨κQ, hκQ⟩)⁻¹ * ⟨κQ * gI, hdH⟩) = ((((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam ⟨κQ, hκQ⟩)⁻¹ :=
    ((map_mul (((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam _ _).trans ((congrArg _ hdl).trans (mul_one _))).trans (map_inv (((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam _)
  exact hc.symm.trans ((congrArg Units.val ((congrArg (((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam e2).trans h4)).trans (Units.val_inv_eq_inv_val _))

end GlobalTheory.Mem.Col2.AdT

namespace GlobalTheory.Mem.Col2.AdT


open Classical in
theorem chr_mul_prod_midAt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m) (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (g g' : SBof I a → Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : SBof I a → B.fields.K), (∀ P, MidAt I hi b P (g P) (z P) ∧ LiftsInv I κ P (g' P) ∧ CongE P.1 ((I.cst a).D P) (g P) (g' P)) → (((I.stp u a i).chr b κ : B.fields.Kˣ) : B.fields.K) * ∏ P, z P = 1 := by
  intro B X I hOk u a i hi b κ g g' z H
  obtain ⟨al, rfl⟩ : ∃ al, b = Idx.of al hi := ⟨_, (Idx.of_get b hi hi).symm⟩
  let k1 : ↥((I.idx a).levG i al).grp := κ.2.1
  let k2 : ↥((I.idx a).levQ i al).grp := κ.2.2
  have e : (((I.stp u a i).chr (Idx.of al hi) κ : B.fields.Kˣ) : B.fields.K) =
      ((((I.idx a).levG i al).chr k1 * ((I.idx a).levQ i al).chr k2 : B.fields.Kˣ) : B.fields.K) := rfl
  rw [e]
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_right.2 fun {P} hP => GlobalTheory.Mem.Col2.TC.Q_notMem_of_ok hOk a P hP
  have hprod : ∏ P : SBof I a, compVal ((I.idx a).levG i al) ((I.idx a).levQ i al) k1 k2 P.1 =
      ((I.idx a).levG i al).chr k1 * ((I.idx a).levQ i al).chr k2 := by
    rw [Finset.prod_coe_sort (SBof I a) (compVal ((I.idx a).levG i al) ((I.idx a).levQ i al) k1 k2)]
    exact prod_compVal hd _ _ k1 k2
  have hz : ∀ P : SBof I a, z P = ((compVal ((I.idx a).levG i al) ((I.idx a).levQ i al) k1 k2 P.1 : B.fields.Kˣ) : B.fields.K)⁻¹ := by
    intro P
    obtain ⟨⟨r, hr, hrx, hzr⟩, hlift, hcong⟩ := H P
    rw [hzr]
    by_cases hP : P.1 ∈ (B.primes X).vGs
    · refine (chiInv_at_type I hOk a i al P hP (g P) (g' P) r hr hrx (k1.1 ⟨P.1, hP⟩) (k1.2 _ (Set.mem_univ _))
        (hlift.2.1 hP) hcong).trans ?_
      rw [compVal_left _ _ k1 k2 hP]
    · have hQ : P.1 ∈ I.Q a := (Finset.mem_union.mp P.2).resolve_left hP
      refine (chiInv_at_twist I hOk a i hi al P hQ (g P) (g' P) r hr hrx (k2.1 ⟨P.1, hQ⟩) (k2.2 _ (Set.mem_univ _))
        (hlift.2.2 hQ) hcong).trans ?_
      exact congrArg (fun x : B.fields.Kˣ => (x : B.fields.K)⁻¹) (compVal_right _ _ k1 k2 hP hQ).symm
  rw [← hprod, Finset.prod_congr rfl fun P _ => hz P, Units.coe_prod, Finset.prod_inv_distrib]
  letI : Nontrivial B.fields.K := B.fields.fieldK.toNontrivial
  exact mul_inv_cancel₀ (Finset.prod_ne_zero_iff.2 fun P _ => Units.ne_zero _)

end GlobalTheory.Mem.Col2.AdT

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localConstantWeilCharacter_values_isIntegral : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → I.IsTw → ∀ (a : I.ι) (P : SBof I a) (x : B.fields.E), IsIntegral ℤ ((I.cst a).psi P x) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.psi_isIntegral | exact GlobalTheory.Mem.Col2.AdT.psi_isIntegral | (intros; apply GlobalTheory.Mem.Col2.AdT.psi_isIntegral <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.OnePrime

section Local

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem exists_bound {m : ℕ} (A : Matrix (Fin m) (Fin m) K) :
    ∃ k : ℕ, ∀ r s, Valued.v (A r s) ≤ WithZero.exp (k : ℤ) := by
  first
  | exact @_root_.GlobalTheory.EntriesExpBound.exists_entries_le_exp
  | exact _root_.GlobalTheory.EntriesExpBound.exists_entries_le_exp
  | (apply _root_.GlobalTheory.EntriesExpBound.exists_entries_le_exp <;> assumption)
  | (intros; apply _root_.GlobalTheory.EntriesExpBound.exists_entries_le_exp <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EntriesExpBound.exists_entries_le_exp <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EntriesExpBound.exists_entries_le_exp ..)

theorem mul_bound {m : ℕ} {A C : Matrix (Fin m) (Fin m) K} {a c : WithZero (Multiplicative ℤ)}
    (hA : ∀ r s, Valued.v (A r s) ≤ a) (hC : ∀ r s, Valued.v (C r s) ≤ c) (r s : Fin m) :
    Valued.v ((A * C) r s) ≤ a * c := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_mul' (hA r j) (hC j s)

end Local

theorem exists_root_rat (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (m n N : ℕ) (hn : 0 < n)
    (q : P.adicCompletion E) (hq : Valued.v q = WithZero.exp (-1 : ℤ)) (G₁ G₂ : GL (Fin m) (P.adicCompletion E)) :
    ∃ (M : GL (Fin m) (P.adicCompletion E)) (γ : GL (Fin m) E),
      (∀ r s, Valued.v (M.1 r s - (1 : Matrix (Fin m) (Fin m) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(N : ℤ))) ∧
      (∀ r s, Valued.v ((M ^ n).1 r s - (1 : Matrix (Fin m) (Fin m) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(N : ℤ))) ∧
      G₁ * M ^ n * G₂ = Matrix.GeneralLinearGroup.map (algebraMap E (P.adicCompletion E)) γ := by
  haveI : CharZero (P.adicCompletion E) := algebraRat.charZero _
  have hc : Valued.v (q ^ (N + 1)) = WithZero.exp (-((N : ℤ) + 1)) := by
    rw [map_pow, hq, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hn1 : Valued.v (n : P.adicCompletion E) ≤ 1 := by
    clear hn
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ]
      exact Valuation.map_add_le _ ih (by simp)
  have hcN : Valued.v (q ^ (N + 1)) ≤ WithZero.exp (-(N : ℤ)) := by
    rw [hc]
    exact WithZero.exp_le_exp.2 (by omega)
  have hε : Valued.v ((n : P.adicCompletion E) ^ 2 * q ^ (N + 1)) ≠ 0 := by
    rw [map_mul, hc]
    refine mul_ne_zero ?_ WithZero.exp_ne_zero
    rw [Valuation.ne_zero_iff]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 hn.ne')
  obtain ⟨k₁, hk₁⟩ := exists_bound G₂.1
  obtain ⟨k₂, hk₂⟩ := exists_bound (G₂⁻¹).1
  set e := WithZero.log (Valued.v ((n : P.adicCompletion E) ^ 2 * q ^ (N + 1))) with he
  obtain ⟨γ, hγ⟩ := GlobalTheory.DenseGL.dense_two_sided E P m (k₁ + k₂ + (-e).toNat) (G₁ * G₂)
  let γ' : GL (Fin m) (P.adicCompletion E) := Matrix.GeneralLinearGroup.map (algebraMap E (P.adicCompletion E)) γ
  have hγ' : γ'.1 = γ.1.map (algebraMap E (P.adicCompletion E)) := rfl
  let B₀ : GL (Fin m) (P.adicCompletion E) := G₁⁻¹ * γ' * G₂⁻¹
  have hB : B₀.1 - 1 = G₂.1 * (((G₁ * G₂)⁻¹).1 * γ.1.map (algebraMap E (P.adicCompletion E)) - 1) * (G₂⁻¹).1 := by
    rw [← hγ', mul_sub, _root_.sub_mul, mul_one, Units.mul_inv, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul]
    congr 2
    simp only [B₀]
    group
  have hB2 : ∀ r s, Valued.v ((B₀.1 - 1) r s) ≤ Valued.v ((n : P.adicCompletion E) ^ 2 * q ^ (N + 1)) := fun r s => by
    rw [hB]
    refine (mul_bound (mul_bound hk₁ fun r s => (hγ r s).1) hk₂ r s).trans ?_
    rw [← WithZero.exp_log hε, ← he, ← WithZero.exp_add, ← WithZero.exp_add]
    refine WithZero.exp_le_exp.2 ?_
    push_cast
    omega
  obtain ⟨M, hM1, hM2⟩ := GlobalTheory.MatNthRoot.exists_nthRoot E P m n (q ^ (N + 1)) B₀.1 hn
    (by rw [hc, ← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by omega)) hB2
  have hu : IsUnit M := (isUnit_pow_iff hn.ne').1 (hM2 ▸ B₀.isUnit)
  obtain ⟨M, rfl⟩ := hu
  have hM3 : M ^ n = B₀ := Units.ext (by rw [Units.val_pow_eq_pow_val, hM2])
  refine ⟨M, γ, fun r s => (hM1 r s).trans ?_, fun r s => ?_, ?_⟩
  · rw [map_mul]
    exact (mul_le_of_le_one_left' hn1).trans hcN
  · rw [hM3]
    refine (hB2 r s).trans ?_
    rw [map_mul, map_pow]
    exact (mul_le_of_le_one_left' (pow_le_one' hn1 2)).trans hcN
  · rw [hM3]
    show _ = γ'
    simp only [B₀]
    group



theorem exists_level_elt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad), ChiFin I l Z S → ∀ (P : SBof I a), P.1 ∈ I.Q a → ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ (N : ℕ) (g₁ g₂ : GA B (B.R.N i)), ∃ z : S.U, S.chi z = 1 ∧ (∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') z.1 = 1) ∧ GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) N z.1 ∧ ∃ γ : GL (Fin (B.R.N i)) B.fields.E, ∀ r s, adAt B.host.F P.1 (((g₁ * (show GA B (B.R.N i) from z.1) * g₂ : GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = algebraMap B.fields.E (P.1.adicCompletion B.fields.E) ((γ : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E) r s) := by
  intro B X I hI hPin l Z a T i hi bad S hS P hP v hv N g₁ g₂
  obtain ⟨n, hn, hchi⟩ := hS
  obtain ⟨N₀, hN₀⟩ := GlobalTheory.Mem.Col2.AdT.Opn.level_contains_deep I hI hPin l Z a T i hi bad S P v hv
  have hd := fun N z => GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main I hI l Z a ((I.rec7 l Z).R.N i) N P z
  obtain ⟨hs, hq, -⟩ := hd 0 1
  let φ : AfE B.host.F B.host.E →+* P.1.adicCompletion B.fields.E := adAt B.host.F P.1
  obtain ⟨M, γ, hM1, hM2, hM3⟩ := exists_root_rat B.fields.E P.1 (B.R.N i) n (N + N₀) hn _ hq
    (Matrix.GeneralLinearGroup.map φ g₁) (Matrix.GeneralLinearGroup.map φ g₂)
  obtain ⟨w, hwU, hwv, hwP⟩ := GlobalTheory.Mem.Col2.AdLift.exists_lift I hI hPin l Z a i hi P v hv M
  have hw : w ∈ S.U := hN₀ w hwU hwv (((hd N₀ w).2.2).2 fun r s => by
    rw [hwP]
    exact (hM1 r s).trans (WithZero.exp_le_exp.2 (by omega)))
  let w' : GA B (B.R.N i) := w
  have hw' : Matrix.GeneralLinearGroup.map φ w' = M := Units.ext (Matrix.ext hwP)
  have hz : Matrix.GeneralLinearGroup.map φ (w' ^ n) = M ^ n := by rw [map_pow, hw']
  have hz' : ∀ r s, φ ((w' ^ n).1 r s) = (M ^ n).1 r s := fun r s =>
    congrArg (fun g : GL (Fin (B.R.N i)) (P.1.adicCompletion B.fields.E) => g.1 r s) hz
  have hbad : v ∉ badG (I.rec7 l Z) := by
    have key : ∀ j : Fin 2, (((B.primes X).g j : ℕ) : 𝓞 B.fields.E) ∉ P.1.asIdeal := fun j =>
      GlobalTheory.Proof.NarrowJetMoments.notMem_of_mem_QE hI.sel_ok hP ((base_fields_primes_ok B X).2.1.g_prime j) (hI.g_mem j)
    rw [hs] at hv
    have key2 : ∀ j : Fin 2, (((B.primes X).g j : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal := fun j h => by
      rw [hv, Ideal.mem_comap, map_natCast] at h
      exact key j h
    rintro (h | h)
    · exact key2 0 h
    · exact key2 1 h
  refine ⟨⟨w, hw⟩ ^ n, ?_, fun v' hv' => ?_, ((hd N _).2.2).2 fun r s => ?_, γ, fun r s => ?_⟩
  · rw [map_pow]
    exact hchi ⟨w, hw⟩ fun v' hv' => hwv v' fun e => hbad (e ▸ hv')
  · show bc (prV (E := (I.rec7 l Z).host.E) v') (w ^ n) = 1
    calc
      bc (prV (E := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) v') (w ^ n) =
          (bc (prV (E := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) v') w) ^ n := map_pow _ _ _
      _ = 1 := (congrArg (fun x => x ^ n) (hwv v' hv')).trans (one_pow n)
  · have e := hz' r s
    have h2 := hM2 r s
    rw [← e] at h2
    exact h2.trans (WithZero.exp_le_exp.2 (by omega))
  · have e : Matrix.GeneralLinearGroup.map φ (g₁ * w' ^ n * g₂) =
        Matrix.GeneralLinearGroup.map φ g₁ * M ^ n * Matrix.GeneralLinearGroup.map φ g₂ := by
      rw [map_mul, map_mul, hz]
    exact congrArg (fun g : GL (Fin (B.R.N i)) (P.1.adicCompletion B.fields.E) => g.1 r s) (e.trans hM3)

end GlobalTheory.Mem.Col2.AdT.OnePrime

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.levelPrimeFunctionals_eq_moved_level_functionals : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ β : Ch, FunKilled (K β).lev (X.piT u) → ∀ (P : (B.primes X).vT u) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∃ ι : (K β).lev.fM v h →+ 𝓞 B.fields.E ⧸ P.1.asIdeal, ∀ c, chOf c = β → GlobalTheory.TwU.FunMoved (sm I l Z) (K β).lev P v h ι ((K (chOf c)).y ⟨c, rfl⟩).1 ((I.stp u a i).rep c).1.1.deco.1 := by
  first | exact @GlobalTheory.Mem.Col2.TC.funMoved_charts | exact GlobalTheory.Mem.Col2.TC.funMoved_charts | (intros; apply GlobalTheory.Mem.Col2.TC.funMoved_charts <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_middleStep_level_inverse_lifts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m) (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (P : SBof I a), ∃ g z, MidAt I hi b P g z ∧ LiftsInv I κ P g := by
  first | exact @GlobalTheory.Mem.Col2.AdT.exists_midAt_liftsInv | exact GlobalTheory.Mem.Col2.AdT.exists_midAt_liftsInv | (intros; apply GlobalTheory.Mem.Col2.AdT.exists_midAt_liftsInv <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (n N : ℕ) (P : SBof I a) (z : GL (Fin n) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)), GlobalTheory.TwU.seamP (sm I l Z) P.1 = P.1 ∧ Valued.v ((qOf P.1 : ℕ) : P.1.adicCompletion B.fields.E) = WithZero.exp (-1 : ℤ) ∧ (GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) N z ↔ ∀ r s, Valued.v (adAt B.host.F P.1 (z.1 r s) - (1 : Matrix (Fin n) (Fin n) (P.1.adicCompletion B.fields.E)) r s) ≤ WithZero.exp (-(N : ℤ))) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main | exact GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main | (intros; apply GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.couplingCosetInFrames_preimage_under_lift : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (p : (I.stp u a i).D b) (P : SBof I a) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), (I.stp u a i).gam b κ = 1 → LiftsInv I κ P g → ∀ z, z ∈ cosetIn ((I.stp u a i).act b κ p) P ↔ g z ∈ cosetIn p P := by
  first | exact @GlobalTheory.Mem.Col2.AdT.cosetIn_act_of_liftsInv | exact GlobalTheory.Mem.Col2.AdT.cosetIn_act_of_liftsInv | (intros; apply GlobalTheory.Mem.Col2.AdT.cosetIn_act_of_liftsInv <;> assumption)
end
