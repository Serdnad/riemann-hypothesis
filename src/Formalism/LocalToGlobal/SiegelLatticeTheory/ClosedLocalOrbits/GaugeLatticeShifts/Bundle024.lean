module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DistinctWordsDistinctParameters
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActRRep
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActL
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfOrbitAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle022
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOpInhab
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActR
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle012
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open scoped Classical ComplexConjugate ENNReal NNReal
open MeasureTheory

namespace Formalism.L2.SG.Pf.SlabCount

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LeviStabFinC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u' : D.what₂.Word), ∀ Λ ∈ Y.what₂ u',
    ∃ T : Finset ((VS D).V ≃ₗ[D.host.E] (VS D).V),
      (∀ τ ∈ T, τ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ Formalism.HermitianLatticesTheory.gmap τ Λ = Λ ∧ ∃ t : X.B.I.GA, RatLink X t τ ∧ t ∈ Srat X u') ∧
      ∀ (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (s : X.B.I.GA), RatLink X s σ → σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
        s ∈ Srat X u' → Formalism.HermitianLatticesTheory.gmap σ Λ = Λ →
        ∃ τ ∈ T, ∀ x ∈ orth (VS D) (Xsp (lf D (X.Fu u'))), (τ⁻¹ * σ) x - x ∈ Xsp (lf D (X.Fu u'))

def Usp {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) : Submodule D.host.E (VS D).V :=
  Submodule.span D.host.E (Set.range X.eX ∪ Set.range X.fY ∪ {X.zu u'})

def Wsp {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) : Submodule D.host.E (VS D).V :=
  orth (VS D) (Usp X u')

def LeviPosC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word), ∀ w ∈ Wsp X u', w ≠ 0 →
    0 < Algebra.trace ℚ D.host.E ((VS D).hT w w)

def SratZC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (s : X.B.I.GA)
    (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X s σ → s ∈ Srat X u' →
      σ (X.zu u') - X.zu u' ∈ Xsp (lf D (X.Fu u'))

def piWL {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) :
    (VS D).V →ₗ[D.host.E] (VS D).V :=
  LinearMap.id - ∑ a, ((VS D).hT (X.fY a)).smulRight (X.eX a) - ∑ a, ((VS D).hT (X.eX a)).smulRight (X.fY a) -
    ((VS D).hT (X.zu u')).smulRight (((VS D).hT (X.zu u') (X.zu u'))⁻¹ • X.zu u')

def hW {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) :
    Wsp X u' →ₗ⋆[D.host.E] Wsp X u' →ₗ[D.host.E] D.host.E :=
  ((VS D).hT.comp (Wsp X u').subtype).compl₂ (Wsp X u').subtype

def LW {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Submodule (𝓞 D.host.E) (Wsp X u') :=
  ((Λ ⊓ (orth (VS D) (Xsp (lf D (X.Fu u')))).restrictScalars (𝓞 D.host.E)).map
    ((piWL X u').restrictScalars (𝓞 D.host.E))).comap ((Wsp X u').subtype.restrictScalars (𝓞 D.host.E))

def LeviWFinC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u' : D.what₂.Word), ∀ Λ ∈ Y.what₂ u',
    Set.Finite {g : Wsp X u' ≃ₗ[D.host.E] Wsp X u' | g ∈ Formalism.HermitianLatticesTheory.isom (hW X u') ∧ Formalism.HermitianLatticesTheory.gmap g (LW X u' Λ) = LW X u' Λ}

theorem srat_flag {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {u' : D.what₂.Word} {s : X.B.I.GA}
    {σ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hs : RatLink X s σ) (hS : s ∈ Srat X u') :
    ∀ j, ∀ x ∈ Xflag (lf D (X.Fu u')) (j + 1), σ x - x ∈ Xflag (lf D (X.Fu u')) j := by
  have hX : ∀ j : ℕ, Xflag (lf D (X.Fu u')) j = Submodule.span D.host.E (X.eX '' {b | b.1 < j}) := by
    intro j
    unfold Formalism.MainNotions.S.Lat.Xflag Formalism.MainNotions.S.FlagG.Xa
    simp only [Formalism.MainNotions.S.lf, X.Fu_e]
  intro j x hx
  rw [hX (j + 1)] at hx
  rw [hX j]
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, rfl⟩ := hy
    have h := Formalism.L2.SG.Pf.RegroupPf.StabFlagPf.flag_e (X := X) hs hS b
    refine Submodule.span_mono ?_ h
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c, lt_of_lt_of_le hc (Nat.lt_succ_iff.mp hb), rfl⟩
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add (f := _), add_sub_add_comm]
    exact Submodule.add_mem _ hy hz
  | smul a y _ hy =>
    rw [map_smul, ← smul_sub]
    exact Submodule.smul_mem _ a hy

private theorem gmap_mul_lemma {D : D7} (a b : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (L : Submodule (𝓞 D.host.E) (VS D).V) :
    Formalism.HermitianLatticesTheory.gmap (a * b) L = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b L) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    LinearEquiv.mul_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨b y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

private theorem gmap_one_explicit_D {D : D7} (L : Submodule (𝓞 D.host.E) (VS D).V) :
    Formalism.HermitianLatticesTheory.gmap (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) L = L := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    LinearEquiv.coe_one, id_eq, exists_eq_right]

private theorem gmap_inv_of_gmap_eq {D : D7} (a : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (L M : Submodule (𝓞 D.host.E) (VS D).V) (h : Formalism.HermitianLatticesTheory.gmap a L = M) :
    Formalism.HermitianLatticesTheory.gmap a⁻¹ M = L := by
  rw [← h, ← gmap_mul_lemma, inv_mul_cancel, gmap_one_explicit_D]

theorem leviFinC_of (h : LeviStabFinC) : LeviFinC := by
  intro D X Y u'
  let P : Submodule (𝓞 D.host.E) (VS D).V → Submodule (𝓞 D.host.E) (VS D).V → Prop := fun Λ₁ Λ₂ =>
    Λ₂ ∈ Y.what₂ u' ∧ ∃ (σ₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (s₀ : X.B.I.GA), RatLink X s₀ σ₀ ∧
      σ₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ s₀ ∈ Srat X u' ∧ Formalism.HermitianLatticesTheory.gmap σ₀ Λ₂ = Λ₁
  refine ⟨fun Λ₁ Λ₂ => if hP : P Λ₁ Λ₂ then
      (h D X Y u' Λ₂ hP.1).choose.image (fun τ => hP.2.choose * τ) else ∅, ?_⟩
  intro Λ₁ _ Λ₂ hΛ₂ σ s hs hσ hS hmap
  have hP : P Λ₁ Λ₂ := ⟨hΛ₂, σ, s, hs, hσ, hS, hmap⟩
  simp only [dif_pos hP]
  obtain ⟨s₀, hs₀, hσ₀, hS₀, hmap₀⟩ := hP.2.choose_spec
  obtain ⟨hT1, hT2⟩ := (h D X Y u' Λ₂ hP.1).choose_spec
  generalize hP.2.choose = σ₀ at hs₀ hσ₀ hmap₀ ⊢
  generalize (h D X Y u' Λ₂ hP.1).choose = T at hT1 hT2 ⊢

  have hρL : RatLink X (s₀⁻¹ * s) (σ₀⁻¹ * σ) :=
    Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X hs₀) hs
  have hρI : σ₀⁻¹ * σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    (Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hσ₀) hσ
  have hρS : s₀⁻¹ * s ∈ Srat X u' := (Srat X u').mul_mem ((Srat X u').inv_mem hS₀) hS
  have hρΛ : Formalism.HermitianLatticesTheory.gmap (σ₀⁻¹ * σ) Λ₂ = Λ₂ := by
    rw [gmap_mul_lemma, hmap]
    exact gmap_inv_of_gmap_eq σ₀ Λ₂ Λ₁ hmap₀
  obtain ⟨τ, hτ, hτo⟩ := hT2 (σ₀⁻¹ * σ) (s₀⁻¹ * s) hρL hρI hρS hρΛ
  obtain ⟨hτI, hτΛ, t, ht, htS⟩ := hT1 τ hτ
  refine ⟨σ₀ * τ, Finset.mem_image.mpr ⟨τ, hτ, rfl⟩, ?_⟩
  have heq : (σ₀ * τ)⁻¹ * σ = τ⁻¹ * (σ₀⁻¹ * σ) := by
    rw [mul_inv_rev, mul_assoc]
  rw [heq]
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hτI) hρI, ?_⟩, ?_, hτo⟩
  · rw [gmap_mul_lemma, hρΛ]
    exact gmap_inv_of_gmap_eq τ Λ₂ Λ₂ hτΛ
  · exact srat_flag X (Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X ht) hρL)
      ((Srat X u').mul_mem ((Srat X u').inv_mem htS) hρS)

end Formalism.L2.SG.Pf.SlabCount
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.Cut

section Gen

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem nlam_iff_of_rel {Λ : Submodule (𝓞 D.host.E) (VS D).V} {p q : GCar X u u F0 F0 Λ Λ}
    (h : GRel X u u F0 F0 Λ Λ p q) : p.1.2 ∈ NLam Λ (lf D F0) ↔ q.1.2 ∈ NLam Λ (lf D F0) := by
  obtain ⟨n, hn, n', hn', hq⟩ := h
  let H := NLamSub Λ (lf D F0)
  rw [hq]
  constructor
  · intro hp
    exact H.mul_mem (H.mul_mem hn hp) hn'
  · intro hq'
    have e : p.1.2 = n⁻¹ * (n * p.1.2 * n') * n'⁻¹ := by group
    rw [e]
    exact H.mul_mem (H.mul_mem (H.inv_mem hn) hq') (H.inv_mem hn')

theorem nlam_out_iff {Λ : Submodule (𝓞 D.host.E) (VS D).V} (p : GCar X u u F0 F0 Λ Λ) :
    (Quot.out (Quot.mk (GRel X u u F0 F0 Λ Λ) p)).1.2 ∈ NLam Λ (lf D F0) ↔ p.1.2 ∈ NLam Λ (lf D F0) := by
  have key : ∀ a b : GCar X u u F0 F0 Λ Λ, Relation.EqvGen (GRel X u u F0 F0 Λ Λ) a b →
      (a.1.2 ∈ NLam Λ (lf D F0) ↔ b.1.2 ∈ NLam Λ (lf D F0)) := by
    intro a b hab
    induction hab with
    | rel a b h => exact nlam_iff_of_rel h
    | refl a => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  exact key _ _ (Quot.eqvGen_exact (Quot.out_eq (Quot.mk (GRel X u u F0 F0 Λ Λ) p)))

theorem isId_of_lin {t : GTerm X u u F0 F0 what₂ what₂} (h : t.lin ∈ NLam t.lam (lf D F0)) : t.isId := by
  unfold GTerm.isId Formalism.L2.SG.FourParts.termIsId Formalism.L2.SG.FourParts.IsIdT
  refine ⟨t.frame, ⟨t.rep.2.2.2.2, rfl⟩, ?_⟩
  unfold Formalism.L2.SG.FourParts.IsIdF
  have hi : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hf : mapLF t.lin (lf D F0) = _ := dif_pos hi
  rw [show t.frame = mapLF t.lin (lf D F0) from rfl, hf]
  refine ⟨t.lin, h, fun a => rfl, ?_⟩
  have hz : (mapFlag t.lin hi (lf D F0).fl).z = t.lin (lf D F0).fl.z := rfl
  show t.lin (lf D F0).fl.z - (mapFlag t.lin hi (lf D F0).fl).z ∈ _
  rw [hz, sub_self]
  exact zero_mem _

end Gen

theorem idMeetOneC_of (hK : IdMeetKeyC) : IdMeetOneC := by
  intro D X Y u hneat _
  refine ⟨fun ρ ρ' t hid hm => (hK D X Y u hneat ρ ρ' t hid hm).1, ?_, ?_⟩
  · intro ρ t t' hid hid' hm hm'
    have h1 := (hK D X Y u hneat ρ ρ t hid hm).2
    have h2 := (hK D X Y u hneat ρ ρ t' hid' hm').2
    obtain ⟨hl, hl', -⟩ := hm
    obtain ⟨hr, hr', -⟩ := hm'
    obtain ⟨lam, mem, lam', mem', cls⟩ := t
    obtain ⟨lam₂, mem₂, lam₂', mem₂', cls₂⟩ := t'
    simp only at hl hl' hr hr'
    subst hl hl' hr hr'
    have h1' : (Quot.out cls).1.2 ∈ Formalism.L2.SG.Pf.NLamSub ((Y.cs u).lamOf ρ) (lf D (X.Fu u)) := h1
    have h2' : (Quot.out cls₂).1.2 ∈ Formalism.L2.SG.Pf.NLamSub ((Y.cs u).lamOf ρ) (lf D (X.Fu u)) := h2
    have hrel : GRel X u u (X.Fu u) (X.Fu u) ((Y.cs u).lamOf ρ) ((Y.cs u).lamOf ρ) (Quot.out cls) (Quot.out cls₂) :=
      ⟨(Quot.out cls₂).1.2 * ((Quot.out cls).1.2)⁻¹,
        Subgroup.mul_mem _ h2' (Subgroup.inv_mem _ h1'), 1, Formalism.L2.SG.Pf.nlam_one _ _, by group⟩
    have hs := Quot.sound hrel
    have hc : cls = cls₂ := (Quot.out_eq cls).symm.trans (hs.trans (Quot.out_eq cls₂))
    subst hc
    rfl
  · intro ρ
    have hΛ := (Y.cs u).lam_mem ρ
    let t : GTerm X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u) :=
      idGTerm X ((Y.cs u).lamOf ρ) hΛ ((Y.rowsOK u).1 _ hΛ)
    have hlin : t.lin ∈ NLam ((Y.cs u).lamOf ρ) (lf D (X.Fu u)) :=
      (nlam_out_iff _).2 (Formalism.L2.SG.Pf.nlam_one _ _)
    refine ⟨t, isId_of_lin hlin, rfl, rfl, ?_⟩
    exact (Formalism.L2.SG.Pf.nilradical_conj_level' D X Y u ρ t.pt t.lin hlin t.rep.2.1).1

end Formalism.L2.SG.Pf.IdMeet
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full

theorem idMeetPhaseC_of (hK : IdMeetKeyC) : IdMeetPhaseC := by
  intro D X Y u hneat _ ρ t hid hmeet
  obtain ⟨-, hlin⟩ := hK D X Y u hneat ρ ρ t hid hmeet
  have hR : RatLink X t.pt t.lin := t.rep.2.1
  have hN : t.pt.1 ∈ X.NinfU u := Formalism.L2.SG.Pf.nLamNinf_holds D X u _ t.pt t.lin hR hlin
  have hNf : t.pt.2 ∈ X.NfinU u := Formalism.L2.SG.Pf.nLamNfin_holds D X u _ t.pt t.lin hR hlin
  obtain ⟨h1, hmul, hinv⟩ := Formalism.L2.SG.Pf.psiInfChar_holds D X u
  obtain ⟨-, hchi, -⟩ := Formalism.L2.SG.Pf.nilradical_conj_level' D X Y u ρ t.pt t.lin hlin hR
  have hprod := Formalism.L2.SG.Pf.psiProd_all D X u t.pt (ratLink_mem X hR) hN hNf
  refine ⟨hinv _ hN, ?_⟩
  have hψ1 : X.psiInfU u 1 = 1 := by
    have h11 := (hmul 1 h1 1 h1).2
    rw [mul_one] at h11
    have hn := Formalism.L2.SG.RealObj.InfCut.norm_psiInfU X u 1
    have h0 : X.psiInfU u 1 ≠ 0 := by
      intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
    exact mul_left_cancel₀ h0 (h11.symm.trans (mul_one _).symm)
  have hinvψ : X.psiInfU u t.pt.1⁻¹ * X.psiInfU u t.pt.1 = 1 := by
    rw [← (hmul _ (hinv _ hN) _ hN).2, inv_mul_cancel, hψ1]
  have hconj : starRingEnd ℂ (X.psiInfU u t.pt.1⁻¹) = X.psiInfU u t.pt.1 := by
    have hn := Formalism.L2.SG.RealObj.InfCut.norm_psiInfU X u t.pt.1⁻¹
    have hz : starRingEnd ℂ (X.psiInfU u t.pt.1⁻¹) = (X.psiInfU u t.pt.1⁻¹)⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]; simp
    rw [hz, inv_eq_of_mul_eq_one_right hinvψ]
  show X.chi2 ((((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * t.pt.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)) *
    starRingEnd ℂ (X.psiInfU u t.pt.1⁻¹) = 1
  rw [hchi, hconj, mul_comm]
  exact hprod

end Formalism.L2.SG.Pf.IdMeet
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.SatGramActL

theorem left_action_of_local_data (hPD : ∀ D : D7, Formalism.L2.SG.Saturated.PDIso D)
    (hGen : ∀ D : D7, Formalism.L2.SG.Saturated.GenIso (VS D) D.R.rS (gS D))
    (hIR : Formalism.L2.SG.Pf.SatGramRep.IotaRepC) (hAR : Formalism.L2.SG.Pf.SatGramRep.AmpRepNC) (hCB : ChiNBiAll) :
    LeftActC' :=
  left_action_three_families hPD betaLift_holds (sMemLeft_holds hGen hPD) iotaLeft_holds (chiNLeft_holds hCB) ooLeft_holds
    fundConj_holds hIR hAR

end Formalism.L2.SG.Pf.SatGramActL
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.NormCut

theorem satGramC'_of (hL : Formalism.L2.SG.Pf.SatGramActL.LeftActC') (hR : Formalism.L2.SG.Pf.SatGramActR.RightActC') :
    SatGramC' := by
  intro D X Y u u' hI hA hF
  have h1 := Set.mem_insert (Y.tO u u').genSet {(Y.tO u u').ngSet, (Y.tO u u').degSet}
  have h2 : (Y.tO u u').ngSet ∈ ({(Y.tO u u').genSet, (Y.tO u u').ngSet, (Y.tO u u').degSet} :
      Set (Set (GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')))) :=
    Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  exact ⟨Formalism.L2.SG.Pf.SatGram.satGram_of (hL := hL D X Y u u' hI hA hF _ h1) (hR := hR D X Y u u' hI hA hF _ h1),
    Formalism.L2.SG.Pf.SatGram.satGram_of (hL := hL D X Y u u' hI hA hF _ h2) (hR := hR D X Y u u' hI hA hF _ h2)⟩

theorem leviOntoC_holds : LeviOntoC := fun _ _ Y u => Formalism.L2.SG.Pf.NormSteps.levi_onto_reduction Y.TR (Y.cs u)

theorem normExpSatC'_of_acts (hN : NeatC) (hM : MassAC) (hL : Formalism.L2.SG.Pf.SatGramActL.LeftActC')
    (hR : Formalism.L2.SG.Pf.SatGramActR.RightActC') : NormExpSatC' :=
  normExpSatC'_of hN leviOntoC_holds hM (satGramC'_of hL hR)

end Formalism.L2.SG.NormCut
end
end

section

noncomputable section

open NumberField
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.PlaceEmbeddingTraceSums

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def embOf (φ : InfinitePlace F → (E →+* ℂ)) (p : InfinitePlace F × Bool) : E →+* ℂ :=
  if p.2 then (starRingEnd ℂ).comp (φ p.1) else φ p.1

theorem embOf_injective [IsTotallyReal F] [IsTotallyComplex E] (φ : InfinitePlace F → (E →+* ℂ))
    (hφ : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a) : Function.Injective (embOf φ) := by
  have hre : ∀ (v : InfinitePlace F) (a : F), starRingEnd ℂ (v.embedding a) = v.embedding a := by
    intro v a
    have h := ComplexEmbedding.isReal_iff.1 (InfinitePlace.isReal_iff.1 (IsTotallyReal.isReal v))
    exact RingHom.congr_fun h a
  have hres : ∀ p : InfinitePlace F × Bool, (embOf φ p).comp (algebraMap F E) = p.1.embedding := by
    rintro ⟨v, b⟩
    ext a
    cases b <;> simp [embOf, hφ, hre]
  have hnr : ∀ v, (starRingEnd ℂ).comp (φ v) ≠ φ v := by
    intro v h
    have hc := IsTotallyComplex.isComplex (InfinitePlace.mk (φ v))
    rw [InfinitePlace.isComplex_mk_iff, ComplexEmbedding.isReal_iff] at hc
    exact hc (RingHom.ext fun x => RingHom.congr_fun h x)
  rintro ⟨v, b⟩ ⟨v', b'⟩ h
  have hv : v = v' := by
    have := congrArg (fun σ => σ.comp (algebraMap F E)) h
    simp only [hres] at this
    rw [← InfinitePlace.mk_embedding v, ← InfinitePlace.mk_embedding v', this]
  subst hv
  cases b <;> cases b' <;> simp [embOf] at h ⊢
  · exact hnr v h.symm
  · exact hnr v h

theorem embOf_bijective [IsTotallyReal F] [IsTotallyComplex E] (h2 : Module.finrank F E = 2)
    (φ : InfinitePlace F → (E →+* ℂ)) (hφ : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a) :
    Function.Bijective (embOf φ) := by
  classical
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨embOf_injective φ hφ, ?_⟩
  rw [Fintype.card_prod, Fintype.card_bool, Embeddings.card E ℂ,
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, add_zero,
    ← Module.finrank_mul_finrank ℚ F E, h2]
  have h := InfinitePlace.card_add_two_mul_card_eq_rank F
  rw [IsTotallyReal.nrComplexPlaces_eq_zero, mul_zero, add_zero] at h
  rw [h]

theorem trace_eq_sum_places [IsTotallyReal F] [IsTotallyComplex E] (h2 : Module.finrank F E = 2)
    (φ : InfinitePlace F → (E →+* ℂ)) (hφ : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a) (x : E) :
    ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ v, (φ v x + starRingEnd ℂ (φ v x)) := by
  classical
  have h1 : algebraMap ℚ ℂ (Algebra.trace ℚ E x) = ∑ τ : E →ₐ[ℚ] ℂ, τ x := trace_eq_sum_embeddings ℂ
  have h3 : ∑ σ : E →+* ℂ, σ x = ∑ τ : E →ₐ[ℚ] ℂ, τ x :=
    Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun f => f x) (fun τ => τ x)
      (fun _ => by simp [RingHom.equivRatAlgHom_apply])
  have h4 : ∑ p : InfinitePlace F × Bool, embOf φ p x = ∑ σ : E →+* ℂ, σ x :=
    (embOf_bijective h2 φ hφ).sum_comp (fun σ => σ x)
  rw [show ((Algebra.trace ℚ E x : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ E x) from rfl, h1, ← h3, ← h4,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fintype.sum_bool]
  simp [embOf, add_comm]

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem TraceSum_holds : Formalism.L2.SG.RealObj.RootCoordinateFrames.TraceSum := by
  intro D X g x
  have : IsTotallyReal X.B.I.F := X.B.I.cm.totReal
  have : IsTotallyComplex X.B.I.E := X.B.I.cm.cmUnram.1
  have htr : ((Algebra.trace ℚ D.host.E (X.ιE x) : ℚ) : ℂ) = ((Algebra.trace ℚ X.B.I.E x : ℚ) : ℂ) := by
    rw [show X.ιE x = X.ιE.toRatAlgEquiv x from rfl, Algebra.trace_eq_of_algEquiv]
  unfold Formalism.L2.SG.PairVal.psiInf
  rw [htr, trace_eq_sum_places X.B.I.cm.deg2 X.B.I.φ X.B.I.φ_over x, ← Complex.exp_sum]
  congr 1
  rw [← Finset.mul_sum, Finset.sum_div]
  rfl

end Formalism.L2.SG.RealObj.PlaceEmbeddingTraceSums
end
end

section

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.BasicNotions Formalism.L2.SG.Full

theorem stabilizer_of_neat_level
    (hN : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u : D.what₂.Word), X.LevelSubgroupNormalized →
      Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK) : StabNC :=
  stabNC_of lattice_stabilizer_holds flag_stabilizer_holds (orthogonal_stabilizer_of_neat hN)

end Formalism.L2.SG.Pf.RegroupPf
end

section

namespace Formalism.L2.SG.Pf.RegroupPf

theorem orbit_algebra_of_stabilizer (hC : TermCarC) (hS : StabNC) : OrbitAlgC :=
  orbitAlgC_of Formalism.L2.SG.Pf.nilradical_conj_level' hC hS

end Formalism.L2.SG.Pf.RegroupPf
end
