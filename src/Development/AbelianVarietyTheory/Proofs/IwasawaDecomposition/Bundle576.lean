module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle562
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFiniteTypesIsotypicPartsSpanOrthogonal
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle024
import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalHeckeScalars
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle179
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle568
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SignAtBasePlaceEqEmbedding
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle432
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle430
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle022
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

noncomputable section

namespace GlobalTheory.RowTypeReps



theorem reps_exist : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat), ∃ (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F.lv2 rep := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hI hP _ y
  have hB := hP.char.base
  have h0 := hB.models.ν0
  have hD : ∀ b, principalLevelFrame.IsotDecomp R.θ y.PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)))
      (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) R.e0 R.ν0 R.fd0 := by
    intro b
    obtain ⟨h1, h2⟩ := GlobalTheory.FinTypesRows.isotL_span_orth D (Yc D 0) _ R.θ (R.MY 0) y.PY y.hF (R.βY 0)
      (R.dat0 (R.toRealDat.levR F.lv2 b)) R.e0 _ _ hI (D.sp.Y_sig _) hB.models.inf y.stdPsi.1 h0.1.1 h0.2
      (GlobalTheory.Mem.R3.IsotIndep.gaL_finSum _ _ _ _ _)
    exact ⟨h1.symm, h2⟩

  have hp : ∀ b, PeterssonHilbertSpace.IsHermPos (Mult.goodPart R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)))
      (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) R.e0) (Mult.ipM (R.MY 0) R.ν0 R.fd0) := by
    intro b
    have h1 := hermPos_mono (GlobalTheory.HilbertLevels.herm_lev hI hB.models.inf (D.sp.Y_sig _) (R.MY 0) (R.βY 0)
      (R.dat0 (R.toRealDat.levR F.lv2 b)) h0.1.1 h0.2) (Submodule.map_mono (Mult.goodPart_le R.θ (R.MY 0) _ _ R.e0))
    have h2 := h1.map_equiv (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).symm
    convert h2 using 1
    · ext x
      rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
    · funext x x'
      simp only [ipMT, LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply]
  haveI := principalLevelFrame.finite_FTR R.θ y.PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)))
    (fun b => levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) (fun _ => R.e0) (fun _ => R.ν0) (fun _ => R.fd0) hD hp
  refine ⟨principalLevelFrame.FTR R.θ y.PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)))
    (fun b => levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) (fun _ => R.e0), principalLevelFrame.rowRepR R.θ,
    ⟨inferInstance, fun π => principalLevelFrame.rowRepR_occ R.θ π, fun π π' h => principalLevelFrame.rowRepR_inj R.θ π π' h, ?_⟩⟩
  intro ρ hρ
  exact ⟨Quotient.mk _ ⟨ρ, hρ⟩, Formalism.L2.Col.finTypRep_mk_iso ⟨ρ, hρ⟩⟩

end GlobalTheory.RowTypeReps
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section




namespace GlobalTheory.HeightCounting.RatSide.HeckeAtState

open Formalism.BasicNotions.TH Formalism.IndefR.Mult

theorem isDC_one' {G : Type} [Group G] (J : Subgroup G) : Formalism.IndefR.Bridge.IsDC J 1 {1} := by
  refine ⟨fun a ha => ⟨1, 1, by simpa using ha⟩, ?_⟩
  rintro g ⟨k, k', rfl⟩
  exact ⟨1, ⟨Finset.mem_singleton_self _, by simpa using J.mul_mem k.2 k'.2⟩, fun a ha => Finset.mem_singleton.1 ha.1⟩

theorem isHeckeAt_zero_one' {D : D7} (V : HSp D) {P : PlE D.host} (hP : Formalism.BasicNotions.IsSplitPl D.host P) :
    IsHeckeAt V P 0 1 := by
  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt P ((GlobalTheory.HeckeTieCompare.isSplitPl_iff P).1 hP)
  obtain ⟨ϖ, h1, h2⟩ := SetLike.exists_of_lt (Ideal.pow_lt_self P.asIdeal P.ne_bot P.isPrime.ne_top 2 le_rfl)
  exact ⟨e, ϖ, he, h1, h2, GlobalTheory.HeckeParts.isHeckeElt_one V he.1 ϖ⟩

section
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem heckeScalar_eq (R : RealDat3 D A3 Ks) (i : Fin D.R.m) (P : PlE D.host) (k : ℕ) :
    GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar R.toRealDat i P k = hkNorm R i k P := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar, hkNorm, zpow_neg, zpow_natCast, inv_pow]
end

theorem heckeOn_one {D : D7} {V : HSp D} {S} (M : DSModel V S) (F : MMap M) : heckeOn M {1} F = F := by
  ext v g
  simp [heckeOn, postOn, heckeLin]

end GlobalTheory.HeightCounting.RatSide.HeckeAtState

namespace GlobalTheory.HeightCounting.RatSide.HeckeAtState

open Formalism.BasicNotions.TH Formalism.IndefR.Mult

section Gen
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


open Classical in
def famOf (R : RealDat3 D A3 Ks) (hq : ∀ i : Fin D.R.m, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R.toRealDat i) (j : ℕ) (k : ℕ)
    (Pl : PlE D.host) : Module.End D.what₂.LL (Fin (R.nW (idxOf D j)) → D.what₂.LL) :=
  if h : k ≠ 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace R.toRealDat Pl ∧ k ≤ D.R.r then
    Classical.choose (hq (idxOf D j) Pl h.2.1 k h.2.2)
  else 1

theorem famOf_zero (R : RealDat3 D A3 Ks) (hq : ∀ i : Fin D.R.m, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R.toRealDat i) (j : ℕ)
    (Pl : PlE D.host) : famOf R hq j 0 Pl = 1 := by
  unfold famOf
  rw [dite_eq_right (fun h => h.1 rfl)]

theorem exists_heckeRd (R : RealDat3 D A3 Ks) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0)
    (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) (Sb : Finset (PlE D.host))
    (hq : ∀ i : Fin D.R.m, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R.toRealDat i)
    (hg : ∀ v : PlE D.host, IsSplitPl D.host v → v ∉ Sb → GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace R.toRealDat v) :
    ∃ hL' : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL ((ratDatR R cG kKs hk).WL j),
      StabC (ratDatR R cG kKs hk) hL' ∧ (∀ j Pl, hL' j 0 Pl = 1) ∧ HeckeRd R cG kKs hk Sb hL' := by
  refine ⟨famOf R hq, ?_, fun j Pl => famOf_zero R hq j Pl, ?_⟩
  · intro j _ _ k Pl y hy
    change famOf R hq j k Pl y ∈ (R.FW (idxOf D j)).WK
    unfold famOf
    split_ifs with h
    · exact (Classical.choose_spec (hq (idxOf D j) Pl h.2.1 k h.2.2)).2 y hy
    · exact hy
  · intro j k Pl α Rr _ _ hd y
    have hg' : GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace R.toRealDat Pl := hg Pl hd.split hd.offS
    by_cases hk0 : k = 0
    · subst hk0
      have hr := (Classical.choose_spec (hq (idxOf D j) Pl hg' 0 (Nat.zero_le _))).1
      have e1 := (GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.readAs_iff _ _ _ _ _ _).1 (hr Rr ⟨α, hd.elt, hd.reps⟩) y
      have e2 := (GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.readAs_iff _ _ _ _ _ _).1
        (hr {1} ⟨1, isHeckeAt_zero_one' _ hd.split, isDC_one' _⟩) y
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar_zero, one_smul] at e1 e2
      have e4 := (e2.trans (heckeOn_one _ _)).symm.trans e1
      have hn : hkNorm R (idxOf D j) 0 Pl = 1 := by simp [hkNorm]
      rw [famOf_zero, hn, one_smul]
      exact e4
    · have h : k ≠ 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace R.toRealDat Pl ∧ k ≤ D.R.r := ⟨hk0, hg', hd.le⟩
      have e1 := (GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.readAs_iff _ _ _ _ _ _).1
        ((Classical.choose_spec (hq (idxOf D j) Pl h.2.1 k h.2.2)).1 Rr ⟨α, hd.elt, hd.reps⟩) y
      have h1 : famOf R hq j k Pl = Classical.choose (hq (idxOf D j) Pl h.2.1 k h.2.2) := by
        unfold famOf
        rw [dite_eq_left h]
      rw [h1, ← heckeScalar_eq]
      exact e1
end Gen

end GlobalTheory.HeightCounting.RatSide.HeckeAtState

namespace GlobalTheory.HeightCounting.RatSide.HeckeAtState

end GlobalTheory.HeightCounting.RatSide.HeckeAtState

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up

open GlobalTheory.Mem.Top.TwChar

theorem addValuation_pos_iff_valuation_lt_one {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    0 < Examples₂.PlacesToy.valW w x ↔ w.valuation K x < 1 := by
  by_cases hx : x = 0
  · simp [hx]
  have h0 : w.valuation K x ≠ 0 := by simpa using hx
  rw [Examples₂.PlacesToy.valW_of_ne w hx, vAdd, ← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.log_exp]
  norm_cast
  exact neg_pos

theorem addValuation_pos_iff_mem_asIdeal {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    0 < Examples₂.PlacesToy.valW w (x : K) ↔ x ∈ w.asIdeal := by
  rw [addValuation_pos_iff_valuation_lt_one, ← w.valuation_lt_one_iff_mem (K := K)]

theorem addVal_pos_iff {K : Type} [Field K] (v : AddValuation K (WithTop ℤ)) {x : K} (hx : x ≠ 0) :
    0 < v x ↔ ¬ 0 ≤ v x⁻¹ := by
  have h : v x + v x⁻¹ = 0 := by rw [← v.map_mul, mul_inv_cancel₀ hx, v.map_one]
  generalize v x = a at h
  generalize v x⁻¹ = b at h
  cases a with
  | top => simp at h
  | coe a =>
    cases b with
    | top => simp at h
    | coe b =>
      norm_cast at h ⊢
      omega

theorem overOne_plUnder (X : Stages) {B' : Base} (h : Enl X.B B') (v v' : B'.places.Pl)
    (hv : ∀ x ∈ B'.LL0, 0 ≤ B'.places.val v x ↔ 0 ≤ B'.places.val v' x) :
    OverOne X.toD7 (plUnder h v) (plUnder h v') := by
  intro x
  let y : 𝓞 X.B.LL := algebraMap (𝓞 ↥X.B.LL0) (𝓞 X.B.LL) x
  have key : ∀ u : B'.places.Pl, 0 < Examples₂.PlacesToy.valW (K := X.B.LL) (plUnder h u) (y : X.B.LL) ↔
      0 < Examples₂.PlacesToy.valW (K := B'.LL) u (incl h (y : X.B.LL)) := fun u =>
    (addValuation_pos_iff_mem_asIdeal _ y).trans ((mem_plUnder h u y).trans
      (addValuation_pos_iff_mem_asIdeal (K := B'.LL) u (RingOfIntegers.mapRingHom (incl h) y)).symm)
  have hm : incl h (y : X.B.LL) ∈ B'.LL0 := by
    have h1 : X.B.embLL (y : X.B.LL) ∈ B'.embLL '' ↑B'.LL0 := h.2.2.1 ▸ ⟨_, (x : ↥X.toD7.LL0).2, rfl⟩
    obtain ⟨z, hz, e⟩ := h1
    rw [← B'.embLL.injective (e.trans (embLL_incl h _).symm)]
    exact hz
  refine (key v).trans (Iff.trans ?_ (key v').symm)
  by_cases h0 : incl h (y : X.B.LL) = 0
  · rw [h0, AddValuation.map_zero, AddValuation.map_zero]
  · rw [addVal_pos_iff _ h0, addVal_pos_iff _ h0]
    exact not_congr (hv _ (B'.LL0.inv_mem hm))

theorem Seed.psiOk {D : D7} {A : D.ntw.Tw → Finset (PlE D.host)} (σ : Seed D A) {v : D.what₂.places.Pl} (hv : TwistedAt D v) :
    BlochKatoReduction.Gen.PsiOk (σ.s v) (A (σ.s v)) (σ.Q (σ.s v)) (σ.k (σ.s v)) (σ.ψ (σ.s v)) := by
  classical
  have h := ((σ.good v hv).2 1 (by simp)).1
  rw [zpow_one] at h
  obtain ⟨h1, h2, h3⟩ := h
  simp only [Finset.disjoint_union_right] at h2
  exact ⟨h1, by simp only [Finset.disjoint_union_right]; exact ⟨h2.1, h2.2.2⟩, h3⟩

end GlobalTheory.HeightCounting.Up

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up

open GlobalTheory.Mem.Top.TwChar (plUnder incl embLL_incl mem_plUnder)

theorem readsAt_of_plUnder (X X' : Stages) (h : Enl X.B X'.B) (hc : Carried X.toD7 X'.toD7) (v' : X'.B.places.Pl)
    (i : X.toD7.ntw.Tw) (i' : X'.toD7.ntw.Tw) (b : Bool) (hi : HEq i i')
    (hr : ReadsAt (D := X.toD7) i b (plUnder h v')) : ReadsAt (D := X'.toD7) i' b v' := by
  intro x'

  have hx : X'.B.embLL ((x' : ↥X'.toD7.LL0) : X'.toD7.what₂.LL) ∈ X'.B.embLL '' (X'.B.LL0 : Set X'.B.LL) :=
    ⟨_, (x' : ↥X'.toD7.LL0).2, rfl⟩
  rw [h.2.2.1] at hx
  obtain ⟨y, hy, hye⟩ := hx
  have hint' : IsIntegral ℤ (X.B.embLL y) := by
    rw [hye]
    exact (RingOfIntegers.isIntegral_coe x').map
      ((X'.toD7.what₂.embLL.comp (algebraMap ↥X'.toD7.LL0 X'.toD7.what₂.LL)).toIntAlgHom)
  have hint : IsIntegral ℤ (⟨y, hy⟩ : ↥X.toD7.LL0) := by
    refine (isIntegral_algHom_iff ((X.toD7.what₂.embLL.comp (algebraMap ↥X.toD7.LL0 X.toD7.what₂.LL)).toIntAlgHom) ?_).1 (by exact hint')
    exact X.toD7.what₂.embLL.injective.comp (algebraMap ↥X.toD7.LL0 X.toD7.what₂.LL).injective
  let x : 𝓞 ↥X.toD7.LL0 := ⟨⟨y, hy⟩, hint⟩
  have e : X.toD7.what₂.embLL ((x : ↥X.toD7.LL0) : X.toD7.what₂.LL) =
      X'.toD7.what₂.embLL ((x' : ↥X'.toD7.LL0) : X'.toD7.what₂.LL) := hye

  obtain ⟨h1, h2⟩ := hc.emb i i' hi x x' e
  have hside : HEq (sideEmb i b (x : ↥X.toD7.LL0)) (sideEmb i' b (x' : ↥X'.toD7.LL0)) := by
    cases b
    · simpa [sideEmb] using h2
    · simpa [sideEmb] using h1
  have hleft := ((same_basic hc.exp.gal hc.exp.set hc.exp.frm).2.2.2.2 i i' hi).2.2 _ _ hside

  have hmap : RingOfIntegers.mapRingHom (incl h) (algebraMap (𝓞 ↥X.toD7.LL0) (𝓞 X.toD7.what₂.LL) x) =
      algebraMap (𝓞 ↥X'.toD7.LL0) (𝓞 X'.toD7.what₂.LL) x' := by
    apply RingOfIntegers.ext
    apply X'.B.embLL.injective
    exact (embLL_incl h ((x : ↥X.toD7.LL0) : X.toD7.what₂.LL)).trans e
  have hright : 0 < X.toD7.what₂.places.val (plUnder h v') ((x : ↥X.toD7.LL0) : X.toD7.what₂.LL) ↔
      0 < X'.toD7.what₂.places.val v' ((x' : ↥X'.toD7.LL0) : X'.toD7.what₂.LL) := by
    refine (TwistChoice.val_pos_iff_mem X.toD7 (plUnder h v') x).trans
      (Iff.trans ?_ (TwistChoice.val_pos_iff_mem X'.toD7 v' x').symm)
    have hm := mem_plUnder h v' (algebraMap (𝓞 ↥X.toD7.LL0) (𝓞 X.toD7.what₂.LL) x)
    rw [hmap] at hm
    exact hm
  exact hleft.symm.trans ((hr x).trans hright)

end GlobalTheory.HeightCounting.Up
end

section

noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure CopyN (D : D7) {D' : D7} (N : TwNew D') (ι : D.what₂.LL →+* D'.what₂.LL) (e : ↥D'.LL0 ≃+* ↥D.LL0) : Prop where
  cp : GlobalTheory.TwInputs.Move.CopyTw D N.toD7 ι e
  ThetaPsi : HEq D.ntw.ThetaPsi N.tw.ThetaPsi
  topO : HEq D.ntw.topO N.tw.topO
  finLam : HEq D.ntw.finLam N.tw.finLam
  jL : HEq D.ntw.jL N.tw.jL
  s2 : HEq D.ntw.s2 N.tw.s2
  lamG : HEq D.ntw.lamG N.tw.lamG
  Xv : HEq D.ntw.Xv N.tw.Xv
  qs : HEq D.ntw.qs N.tw.qs
  res : HEq D.ntw.res N.tw.res
  eLL0 : ∀ g g', HEq g g' → e (N.ex.eLL0 g') = D.nexp.eLL0 g
  twPsi : HEq D.nexp.twPsi N.ex.twPsi
  twDel : HEq D.nexp.twDel N.ex.twDel
  eH : HEq D.nexp.eH N.ex.eH

theorem CopyN.carried {D D' : D7} {N : TwNew D'} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyN D N ι e) :
    Carried D N.toD7 := by
  refine ⟨h.cp.toSameExport, fun i i' hi x x' hx => ?_⟩
  have hx' : x = e x' := Subtype.ext (D.what₂.embLL.injective
    (hx.trans ((congrArg N.toD7.what₂.embLL (h.cp.LL0 x')).symm.trans (h.cp.embLL _))))
  subst hx'
  exact ⟨h.cp.emb0 i i' hi x', h.cp.emb0b i i' hi x'⟩

end GlobalTheory.HeightCounting.Up

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
open GlobalTheory.Mem.Top.TwChar (plUnder RootIso FrobPick avoidPlaces subset_avoidPlaces)

attribute [local instance] Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory.HeightCounting.Up

theorem pass_of {Q : V4.Slot} {p q r : AtP} (hp : Step KPx (fun _ _ _ _ => True) p) (hq : Step KPx (fun _ _ _ _ => True) q)
    (h : EvG fun K => ∀ B f T, K.Over B.toPre → KPx B f → T = TwDat.untw B T.pl → p K B f T →
      ∀ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W)
        (N : NStage B C W) (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c →
        ExportAt (assemble B C W V S N G) c.O.nch c.O.xd →
        ∀ (A : ℕ → Finset ℕ) (S₂ : ∀ P : Pre, Fr P → Set (HChar P.host.E) → Finset ℂ), (∀ P g Ξ, ∀ z ∈ S₂ P g Ξ, IsAlgebraic ℚ z) →
          ∃ (B' : Base) (f' : Fr B'.toPre) (T' : TwDat B'), Enl B B' ∧ HEq f' f ∧ T'.pl = T.pl ∧ T'.Avoids A ∧
            (∀ z ∈ S₂ B'.toPre f' (T'.set f'), ∃ x : B'.LL, B'.embLL x = z) ∧ KPx B' f' ∧ (q K B' f' T' → r K B' f' T')) :
    Pass KPx Q r := by
  classical
  refine (EvG.inter (EvG.inter hp hq) h).imp fun K _ _ _ _ H => ?_
  obtain ⟨⟨hp, hq⟩, hr⟩ := H
  have hs' : large₂ K fun B f T => KPx B f → q K B f T :=
    (hq.inter (lg_forced K)).imp fun _ _ _ _ G a => G.1 a G.2 trivial
  obtain ⟨S₁, P₁, A₀, S₂₀, a₁, a₂, hlg⟩ := hs'
  have hb : large₂ K fun B f T => (∀ z ∈ S₁ B.toPre f B.KsC, z ∈ B.fixedCoefficientFieldInComplex) ∧ P₁ B.toPre f B.KsC B.fixedCoefficientFieldInComplex ⊆ T.pl :=
    ⟨S₁, P₁, fun _ _ _ _ _ => ∅, S₂₀, a₁, a₂, fun _ _ _ _ h p _ => ⟨h.1, p⟩⟩
  refine (hp.inter hb).imp ?_
  rintro B f T hO ⟨hp, h₁, hpl₁⟩ hKP hT C W V S N G c q hx A S₂ hS₂
  obtain ⟨B', f', T', e, hf, hpl, hAv, hS', hK', hfin⟩ := hr B f T hO hKP hT (hp hKP c.forced trivial) C W V S N G c q hx
    (fun l => A l ∪ A₀ B.toPre f B.KsC B.fixedCoefficientFieldInComplex l) (fun P g Ξ => S₂ P g Ξ ∪ S₂₀ P g B.KsC B.fixedCoefficientFieldInComplex Ξ)
    (fun P g Ξ z hz => (Finset.mem_union.1 hz).elim (hS₂ P g Ξ z) (a₂ P g _ _ Ξ z))
  have hP : B'.toPre = B.toPre := e.1
  have hk : B'.KsC = B.KsC := e.KsC_eq
  have hl : B'.fixedCoefficientFieldInComplex = B.fixedCoefficientFieldInComplex := e.fixedCoefficientField_eq
  have hO' : K.Over B'.toPre := hP ▸ hO
  have hLL : ∀ z ∈ S₂₀ B'.toPre f' B'.KsC B'.fixedCoefficientFieldInComplex (T'.set f'), z ∈ B'.LLC := by
    intro z hz
    rw [hk, hl] at hz
    obtain ⟨x, rfl⟩ := hS' z (Finset.mem_union_right _ hz)
    exact ⟨x, rfl⟩
  have hq' := hlg B' f' T' hO'
    ⟨by rw [hk, hl, secondG_congr S₁ hP hf]; exact h₁, hLL⟩
    (by rw [hk, hl, secondG_congr P₁ hP hf, hpl]; exact hpl₁)
    (fun w v hv hA => hAv w v hv (Finset.mem_union_right _ (by
      rw [hk, hl, secondG_congr A₀ hP hf] at hA; exact hA))) hK'
  exact ⟨B', f', T', e, hf, hpl, fun w v hv hA => hAv w v hv (Finset.mem_union_left _ hA),
    fun z hz => hS' z (Finset.mem_union_left _ hz), hfin hq'⟩

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}

theorem muIsW_st {P : Pre2 K w} (x : St P) : V4.MuIsW (w.st x.o.Z) f T P.Wt w.I.xi :=
  { inj := w.ok.xi_inj
    range := w.xi_range
    mu0 := w.l.xi0
    star := by
      show w.I.xi w.I.muStar = f.del
      rw [w.ok.xi_star, w.C_eq]
    star' := by
      show w.I.xi w.I.muStar' = f.del'
      rw [w.ok.xi_star', w.C_eq]
    tw := P.q.mu.tw
    on := P.q.mu.on
    off := P.q.mu.off
    sub := P.sub
    supp := P.supp }

theorem twisted_st {P : Pre2 K w} (x : St P) (v : B.places.Pl) : TwistedAt (Dof x) v ↔ v ∈ P.Wt :=
  (TupTieW.tupTied_of_muIsW (w.st x.o.Z) f T P.Wt w.I.xi (muIsW_st x)).1 v

theorem below_plUnder {B' : Base} {f' : Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'} (h : Enl B B') (Z : w.Lt) (Z' : w'.Lt)
    (v' : B'.places.Pl) : Below (w.D Z) (w'.D Z') (plUnder h v') v' := by
  intro x x' e
  have : x' = RingOfIntegers.mapRingHom (TwChar.incl h) x :=
    RingOfIntegers.ext (B'.embLL.injective (e.symm.trans (TwChar.embLL_incl h _).symm))
  subst this
  exact TwChar.mem_plUnder h v' x

theorem overOne_plUnder_of {B' : Base} {f' : Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'} (h : Enl B B') (Z : w.Lt) (Z' : w'.Lt)
    {v₁ v₂ : B'.places.Pl} (ho : OverOne (w'.D Z') v₁ v₂) : OverOne (w.D Z) (plUnder h v₁) (plUnder h v₂) := by
  have hm : ∀ x : B.LL0, TwChar.incl h (x : B.LL) ∈ B'.LL0 := fun x => by
    obtain ⟨y, hy, e⟩ : B.embLL (x : B.LL) ∈ B'.embLL '' (B'.LL0 : Set B'.LL) := h.2.2.1 ▸ ⟨x, x.2, rfl⟩
    rwa [← B'.embLL.injective (e.trans (TwChar.embLL_incl h _).symm)]
  let j : B.LL0 →+* B'.LL0 := ((TwChar.incl h).comp B.LL0.val.toRingHom).codRestrict B'.LL0 hm
  intro x
  let x' : 𝓞 ↥(w'.D Z').LL0 := RingOfIntegers.mapRingHom j x
  have key : ∀ v : B'.places.Pl, 0 < (w.D Z).what₂.places.val (plUnder h v) ((x : ↥(w.D Z).LL0) : (w.D Z).what₂.LL) ↔
      0 < (w'.D Z').what₂.places.val v ((x' : ↥(w'.D Z').LL0) : (w'.D Z').what₂.LL) :=
    fun v => (val_pos_iff_mem (w.D Z) _ x).trans (((TwChar.mem_plUnder h v _).trans (iff_of_eq (congrArg
      (· ∈ HeightOneSpectrum.asIdeal v) (RingOfIntegers.ext rfl)))).trans (val_pos_iff_mem (w'.D Z') v x').symm)
  exact (key v₁).trans ((ho x').trans (key v₂).symm)

theorem exists_of_position {P : CP} {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B} {c : V4.Core K X f T} (h : positionOf P K X f T c) :
    ExportAt X.toD7 c.O.nch c.O.xd → ∃ (w : ColW X.B f T) (Z : w.Lt) (c' : V4.Core K (w.st Z) f T), P K X.B f T w Z c' ∧
      ExportAt (w.st Z).toD7 c'.O.nch c'.O.xd :=
  positionOf_ind (R := fun K X f T c => ExportAt X.toD7 c.O.nch c.O.xd → ∃ (w : ColW X.B f T) (Z : w.Lt)
    (c' : V4.Core K (w.st Z) f T), P K X.B f T w Z c' ∧ ExportAt (w.st Z).toD7 c'.O.nch c'.O.xd)
    (fun _ _ _ _ w Z c h e => ⟨w, Z, c, h, e⟩) h

theorem SameGal.trans {D D' D'' : D7} (h : SameGal D D') (h' : SameGal D' D'') : SameGal D D'' :=
  ⟨⟨h.gal.R.trans h'.gal.R, h.gal.host.trans h'.gal.host, h.gal.loc.trans h'.gal.loc, h.gal.Om.trans h'.gal.Om,
    h.gal.instOm.trans h'.gal.instOm, h.gal.algOm.trans h'.gal.algOm, h.gal.plOm.trans h'.gal.plOm, h.gal.PlG.trans h'.gal.PlG⟩,
    h.pl.trans h'.pl⟩

theorem enl_refl (B : Base) : Enl B B := ⟨rfl, rfl, rfl, subset_rfl⟩

theorem avPrimes_st (Z Z' : w.Lt) : avPrimes (w.st Z).toD7 = avPrimes (w.st Z').toD7 := rfl

end GlobalTheory.HeightCounting.Up
end
