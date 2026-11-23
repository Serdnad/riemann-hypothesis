module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LUnifOfRhoGeoEquivAll
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle121
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle447
public import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle271
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.FramesExistOfDiagonalTypePlaces
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeOperatorKeepsRationalIntegralLevelForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle463
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle517
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.LiftInj

section Conc

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem baseLevelComplexPoints_injective_of_independent (R : RealDat3 D A3 Ks) (F : Face3 D A3) (b : Bool) (i : Fin D.R.m)
    (hU : ∀ (n : ℕ) (c : Fin n → (Fin (R.nW i) → D.what₂.LL)), LinearIndependent D.what₂.LL c →
      LinearIndependent ℂ fun k => (R.FW i).j (sg0 D A3.A) (c k)) :
    Function.Injective ((R.toCx3 F).w0C b i) := by
  have hb : LinearIndependent D.what₂.LL (R.toRealDat.bL F.lv2 b i) :=
    (Module.finBasis D.what₂.LL (R.toRealDat.WL F.lv2 b i)).linearIndependent.map' (R.toRealDat.WL F.lv2 b i).subtype
      (Submodule.ker_subtype _)
  refine (injective_iff_map_eq_zero _).2 fun c hc => funext fun l => ?_
  have h1 := Fintype.linearIndependent_iff.1 (hU _ _ hb) _ ((Formalism.IndefR.FWT.principal_form_tensor_expansion R F b i c).symm.trans hc) l
  have h2 := congrArg (Links.cj (twAt D.what₂.embLL A3.A.v0)) h1
  rwa [cj_cj, map_zero] at h2

end Conc



theorem baseLevelComplexPoints_injective_extendedData : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        Function.Injective ((z'.R.toCx3 z'.F).w0C false j')) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ => ?_
  intro B f T w _ _ _ _ Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' hF _ _ j' _ _ _
  exact baseLevelComplexPoints_injective_of_independent z'.R z'.F false j'
    (GlobalTheory.TiedUnif.indep_span_of_tie z'.geo.fw z'.pins.char.base.models.HW z'.geo.bar hF.2.1.jUnif j' _).1

end GlobalTheory.Mem.R3.LiftInj
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.DefLatBC

section GoodTransport

open Formalism.L2.DIV

theorem absIrr_one_ne_zero {K G : Type} [Field K] [CharZero K] [Group G] [Fintype G] {χ : G → K}
    (h : IsAbsIrrChar χ) : χ 1 ≠ 0 := by
  obtain ⟨n, ρ, hρ, hχ⟩ := h
  intro h0
  have h1 : ρ.character 1 = (n : AlgebraicClosure K) := by
    rw [Representation.char_one]; simp
  rw [hχ, h0, map_zero] at h1
  have hn : n = 0 := by exact_mod_cast h1.symm
  subst hn
  obtain ⟨a, b, hab⟩ := hρ.toNontrivial.exists_pair_ne
  apply hab
  apply Subrepresentation.toSubmodule_injective
  exact Subsingleton.elim _ _

theorem eq_of_idemOf_eq {K G : Type} [Field K] [CharZero K] [Group G] [Fintype G] {X Y : Finset (G → K)}
    (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (hYX : Y ⊆ X) (h : idemOf Y = idemOf X) : X = Y := by
  classical
  by_contra hne
  obtain ⟨χ, hχX, hχY⟩ : ∃ χ ∈ X, χ ∉ Y := by
    by_contra hc
    push_neg at hc
    exact hne (Finset.Subset.antisymm hc hYX)
  have hsplit : idemOf (X \ Y) + idemOf Y = idemOf X := by
    unfold idemOf
    exact Finset.sum_sdiff hYX
  have h0 : idemOf (X \ Y) = 0 := by
    rw [h] at hsplit
    simpa using hsplit
  have hmem : χ ∈ X \ Y := Finset.mem_sdiff.2 ⟨hχX, hχY⟩
  have hprod : chiIdem χ * idemOf (X \ Y) = chiIdem χ := by
    unfold idemOf
    rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun χ' hχ' =>
      chiIdem_mul (hX χ hχX) (hX χ' (Finset.mem_sdiff.1 hχ').1)]
    rw [Finset.sum_ite_eq, if_pos hmem]
  rw [h0, mul_zero] at hprod
  have hc := congrArg (fun a : MonoidAlgebra K G => a.coeff 1) hprod
  simp only [coeff_chiIdem, inv_one] at hc
  have hne1 := absIrr_one_ne_zero (hX χ hχX)
  have hcard : ((Fintype.card G : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have : χ 1 / (Fintype.card G : K) * χ 1 ≠ 0 := mul_ne_zero (div_ne_zero hne1 hcard) hne1
  exact this (by simpa using hc.symm)

theorem good_transport {K K' G G' : Type} [Field K] [Field K'] [CharZero K] [CharZero K'] [Group G] [Fintype G]
    [Group G'] [Fintype G'] (σ : K →+* ℂ) (σ' : K' →+* ℂ) (φ : K →+* K') (hφ : ∀ x, σ' (φ x) = σ x) (e : G ≃* G')
    (c : G → ℂ) (c' : G' → ℂ) (hc : ∀ g, c' (e g) = c g) (X : Finset (G → K)) (X' : Finset (G' → K'))
    (hX : ∀ χ, χ ∈ X ↔ IsAbsIrrChar χ ∧ ∑ g, c g * σ (χ g) = σ (χ 1)) (hX2 : ∀ g, σ ((idemOf X).coeff g) = c g)
    (hX' : ∀ χ, χ ∈ X' ↔ IsAbsIrrChar χ ∧ ∑ g, c' g * σ' (χ g) = σ' (χ 1)) (hX2' : ∀ g, σ' ((idemOf X').coeff g) = c' g)
    (χ' : G' → K') : χ' ∈ X' ↔ ∃ χ ∈ X, χ' = fun g => φ (χ (e.symm g)) := by
  classical
  have sup : ∀ χ ∈ X, (fun g => φ (χ (e.symm g))) ∈ X' := by
    intro χ hχ
    obtain ⟨hirr, hsum⟩ := (hX χ).1 hχ
    refine (hX' _).2 ⟨isAbsIrrChar_comp e.symm (GlobalTheory.T.isAbsIrrChar_map_ringHom φ χ hirr), ?_⟩
    rw [← Equiv.sum_comp e.toEquiv]
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulEquiv.symm_apply_apply, hc, hφ, map_one]
    exact hsum
  refine ⟨fun hχ' => ?_, fun ⟨χ, hχ, he⟩ => he ▸ sup χ hχ⟩
  set F : (G → K) → (G' → K') := fun χ g => φ (χ (e.symm g)) with hF
  have hinj : Function.Injective F := by
    intro χ₁ χ₂ h12
    funext g
    have := congrFun h12 (e g)
    simp only [hF, MulEquiv.symm_apply_apply] at this
    exact φ.injective this
  have hYX : X.image F ⊆ X' := by
    intro ψ hψ
    obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.1 hψ
    exact sup χ hχ
  have hcard : (Fintype.card G' : ℂ) = (Fintype.card G : ℂ) := by
    rw [Fintype.card_congr e.toEquiv]
  have hid : idemOf (X.image F) = idemOf X' := by
    apply MonoidAlgebra.ext
    ext t
    apply σ'.injective

    rw [hX2', coeff_idemOf, Finset.sum_image fun a _ b _ h => hinj h, map_sum]
    have := hX2 (e.symm t)

    rw [coeff_idemOf, map_sum] at this
    rw [← hc (e.symm t), MulEquiv.apply_symm_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun χ _ => ?_
    simp only [hF, map_mul, map_div₀, map_natCast, hφ, map_one, map_inv, hcard]
  have := eq_of_idemOf_eq (fun ψ hψ => ((hX' ψ).1 hψ).1) hYX hid
  rw [this] at hχ'
  obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.1 hχ'
  exact ⟨χ, hχ, rfl⟩

end GoodTransport

end GlobalTheory.Mem.R3.DefLatBC

namespace GlobalTheory.Mem.R3.DefLatBC

theorem bc_eq_of_heq {X : Type} [Group X] {E : Type} [Field E] [NumberField E] {r m : ℕ} {P P' : Finset (Pl E)} (hP : P' = P)
    (a : X ≃* Formalism.L2.DIV.G0 P r) (a' : X ≃* Formalism.L2.DIV.G0 P' r) (h : HEq a' a) (g : X) (Q : P) (Q' : P')
    (hQ : (Q' : Pl E) = Q) (i : ZMod m ≃+* kP Q.1) (i' : ZMod m ≃+* kP Q'.1) (x x' : GL (Fin r) (ZMod m))
    (hx : a g Q = Formalism.UG.bc (i : ZMod m →+* kP Q.1) x) (hx' : a' g Q' = Formalism.UG.bc (i' : ZMod m →+* kP Q'.1) x') : x' = x := by
  subst hP
  cases h
  obtain ⟨Q, hQm⟩ := Q
  obtain ⟨Q', hQm'⟩ := Q'
  dsimp only at hQ
  subst hQ
  have hi : (i' : ZMod m →+* kP Q') = (i : ZMod m →+* kP Q') := Subsingleton.elim _ _
  rw [hi] at hx'
  have h2 : Formalism.UG.bc (i : ZMod m →+* kP Q') x' = Formalism.UG.bc (i : ZMod m →+* kP Q') x := hx'.symm.trans hx
  have hinj : Function.Injective (i : ZMod m →+* kP Q') := i.injective
  apply Units.ext
  apply Matrix.ext
  intro s t
  have := congrArg (fun y : GL (Fin r) (kP Q') => (y : Matrix (Fin r) (Fin r) (kP Q')) s t) h2
  exact hinj (by simpa [Formalism.UG.bc] using this)

end GlobalTheory.Mem.R3.DefLatBC

namespace GlobalTheory.Mem.R3.DefLatBC



theorem goodIdempotents_agree_extendedData {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
    {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
    {Wt' : Set B'.places.Pl} (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt')
    (hB : B'.toPre = B.toPre) (hf : HEq f' f) (hp : HEq w'.px w.px) (hG : GrpTrue Z.N f) (hG' : GrpTrue Z'.N f')
    (hx : ExtN z z') (e : Gc B w.px ≃* Gc B' w'.px) (he : ∀ g, HEq (e g) g) (g : Gc B w.px) :
    (w'.st Z').toD7.ntypes.e0.coeff ((z'.R.eG.trans z'.cG) (e g)) =
      (w.st Z).toD7.ntypes.e0.coeff ((z.R.eG.trans z.cG) g) := by
  cases B
  cases B'
  dsimp only at hB
  subst hB
  cases hf
  have hpx : w'.px = w.px := eq_of_heq hp
  cases w'
  dsimp only at hpx
  subst hpx
  have heg : e g = g := eq_of_heq (he g)
  rw [heg]
  obtain ⟨plg, iso, hpl, -, -, hbc⟩ := z.pins.keep.grp
  obtain ⟨plg', iso', hpl', -, -, hbc'⟩ := z'.pins.keep.grp
  refine Eq.trans ?_ (TypesTrue.typeIdempotent_coeff_across_layers hG hG' ((z.R.eG.trans z.cG) g))
  congr 1
  funext kv'
  obtain ⟨k, v'⟩ := kv'
  obtain ⟨v, rfl⟩ : ∃ v, v' = plEquiv Z.N.naut Z'.N.naut k v := ⟨_, (Equiv.apply_symm_apply _ v').symm⟩
  show _ = ((z.R.eG.trans z.cG) g) ⟨k, (plEquiv Z.N.naut Z'.N.naut k).symm (plEquiv Z.N.naut Z'.N.naut k v)⟩
  rw [Equiv.symm_apply_apply]
  have hP : z'.R.Pg = z.R.Pg := eq_of_heq hx.Pg
  have hQ : (plg' ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩).1 = (plg ⟨k, v⟩).1 := by
    rw [hpl', hpl]
    exact TypesTrue.plGw_plEquiv hG hG' k v
  exact bc_eq_of_heq hP z.R.eG z'.R.eG hx.eG g _ _ hQ (iso ⟨k, v⟩) (iso' ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩) _ _
    (hbc g ⟨k, v⟩) (hbc' g ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩)

end GlobalTheory.Mem.R3.DefLatBC

theorem GlobalTheory.Mem.R3.DefLatBC.good_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (e : Gc B w.px ≃* Gc B' w'.px), (∀ g, HEq (e g) g) → ∀ χ' : Gc B' w'.px → (w'.st Z').toD7.what₂.LL, χ' ∈ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.lvlA z'.F.P0 z'.F.ψ0).X ↔ ∃ χ ∈ ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.lvlA z.F.P0 z.F.ψ0).X, χ' = fun g => φ (χ (e.symm g))) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE hf _ hp Z hX Wt z hG _ _ _ Z' hX' hG' _ _ z' _ hx j j' hj φ hφ e he χ' => ?_
  show χ' ∈ z'.Xg ↔ ∃ χ : Gc B w.px → (w.st Z).toD7.what₂.LL, χ ∈ z.Xg ∧ χ' = fun g => φ (χ (e.symm g))
  have g1 := (goodSet_iff _ _ _).1 z.good
  have g2 := (goodSet_iff _ _ _).1 z'.good
  exact GlobalTheory.Mem.R3.DefLatBC.good_transport (w.st Z).toD7.what₂.embLL (w'.st Z').toD7.what₂.embLL φ hφ e
    (fun g => (w.st Z).toD7.ntypes.e0.coeff ((z.R.eG.trans z.cG) g))
    (fun g => (w'.st Z').toD7.ntypes.e0.coeff ((z'.R.eG.trans z'.cG) g))
    (GlobalTheory.Mem.R3.DefLatBC.goodIdempotents_agree_extendedData z z' hE.1 hf hp hG hG' hx e he) z.Xg z'.Xg g1.1 g1.2 g2.1 g2.2 χ'
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem GlobalTheory.Mem.R3.Rw.frame_pb_heq {P P' : Pre} (e : P' = P) {g' : Fr P'} {g : Fr P} (h : HEq g' g) : HEq g'.P.pb g.P.pb := by
  subst e; cases h; rfl


set_option maxHeartbeats 8000000 in
theorem GlobalTheory.Mem.R3.Rw.datExt_rest_of_parts :
    (GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) →
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      Formalism.L2.Pj.LawsCore core'.toCore → core'.Q.Canon → (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) → core'.pb = f'.P.pb →
      letI := alg'; ∃ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr₀ : TrI B' w'.px)
        (R₀ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀) core'.Q.c.F)
        (cG : G0 R₀.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R₀.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R₀.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R₀.eG.trans cG) Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R₀.mu R₀.twPl ∧
        IdemClass (D := (w'.st Z').toD7) (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).A ∧ R₀.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 ∧ R₀.IsInert ∧ R₀.IsTup ∧
        R₀.AllPlaces ∧ Keep R₀.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 cG ∧ BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀ R₀.toRealDat ∧
        RSideW z {v | B'.places.resChar v ∈ T'.pl} R₀)) →
    (GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) →
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      Formalism.L2.Pj.LawsCore core'.toCore → core'.Q.Canon → (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) → core'.pb = f'.P.pb →
      letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr₀ : TrI B' w'.px)
        (R₀ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀) core'.Q.c.F)
        (cG : G0 R₀.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R₀.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R₀.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R₀.eG.trans cG) Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R₀.mu R₀.twPl ∧
        IdemClass (D := (w'.st Z').toD7) (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).A ∧ R₀.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 ∧ R₀.IsInert ∧ R₀.IsTup ∧
        R₀.AllPlaces ∧ Keep R₀.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 cG ∧ BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀ R₀.toRealDat ∧
        RSideW z {v | B'.places.resChar v ∈ T'.pl} R₀ →
        ∃ (tr : TrI B' w'.px)
        (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr) core'.Q.c.F)
        (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr) cG' ∧
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R'.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R'.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R'.eG.trans cG') Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R'.mu R'.twPl ∧
        BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr R'.toRealDat ∧ R'.toRealDat.ExAt ∧ RSide z {v | B'.places.resChar v ∈ T'.pl} R')) →
    (GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) →
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      Formalism.L2.Pj.LawsCore core'.toCore → core'.Q.Canon → (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) → core'.pb = f'.P.pb →
      letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
        (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr) core'.Q.c.F)
        (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr) cG' ∧
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R'.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R'.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R'.eG.trans cG') Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R'.mu R'.twPl ∧
        BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr R'.toRealDat ∧ R'.toRealDat.ExAt ∧ RSide z {v | B'.places.resChar v ∈ T'.pl} R' →
        ∃ geo : GlobalTheory.RealGeo.GeoHalf core' R'.toRealDat (fun _ => 1), GlobalTheory.RealGeo.InGeo geo ∧
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
          HEq (geo.v₀ i' (w'.st Z').toD7.what₂.embLL) (z.geo.v₀ i (w.st Z).toD7.what₂.embLL) ∧
          (∀ φ φ', HEq φ' φ → HEq ((R'.FW i').j (w'.st Z').toD7.what₂.embLL (geo.fw.e i' φ' : (R'.FW i').WK).1)
            ((z.R.FW i).j (w.st Z).toD7.what₂.embLL (z.geo.fw.e i φ : (z.R.FW i).WK).1)) ∧
          (HEq (geo.κ i').aP (z.geo.κ i).aP ∧ HEq (geo.κ i').aM (z.geo.κ i).aM ∧ (geo.κ i').n = (z.geo.κ i).n)) ∧
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
          ∀ (k : Fin (z.R.nW i)) (k' : Fin (R'.nW i')), (k : ℕ) = k' →
          (w'.st Z').toD7.what₂.embLL ((geo.fw.e i' φ' : (R'.FW i').WK).1 k') = (w.st Z).toD7.what₂.embLL ((z.geo.fw.e i φ : (z.R.FW i).WK).1 k)))) →
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) →
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      Formalism.L2.Pj.LawsCore core'.toCore → core'.Q.Canon → (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) → core'.pb = f'.P.pb →
      ∃ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, z'.core = core' ∧
        z'.R.toRealDat.ExAt ∧ GlobalTheory.RealGeo.InGeo z'.geo ∧ z'.Std ∧ ExtN z z') := by
  intro k1 k2 k3 h1 h2 h3 h4 h5 h6 h7
  refine (((k1 h1 h2 h3 h4 h5 h6 h7).and (k2 h1 h2 h3 h4 h5 h6 h7)).and (k3 h1 h2 h3 h4 h5 h6 h7)).trans
    (Step.of_all fun K B' f' T' _ _ _ _ w' hw => ?_)
  have ha := hw.1.1
  have hb := hw.1.2
  have hd := hw.2
  intro B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV core' alg' ha1 ha2 ha3 hc hL hC hD hpb
  obtain ⟨Xg, tr₀, R₀, cG, s0⟩ :=
    ha B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV core' alg' ha1 ha2 ha3 hc hL hC hD hpb
  obtain ⟨tr, R', cG', s1⟩ :=
    hb B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV core' alg' ha1 ha2 ha3 hc hL hC hD hpb Xg tr₀ R₀ cG s0
  obtain ⟨geo, hg⟩ :=
    hd B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV core' alg' ha1 ha2 ha3 hc hL hC hD hpb Xg tr R' cG' s1
  -- Project the conjuncts directly to avoid carrying the dependent goal through case splits.
  have sStd := s1.2.2.2.2.2
  have realSide := sStd.2.2
  have rW := realSide.1
  have rT := realSide.2
  let z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl} :=
    @Dat.mk (w'.st Z') w'.px w'.I hX' T' _ Xg tr core' alg' ha1 R' cG' geo
      s1.1 s1.2.1 s1.2.2.1 s1.2.2.2.1 s1.2.2.2.2.1 ha2 ha3
  refine ⟨z', rfl, sStd.2.1, hg.1, sStd.1, ?_⟩
  have hcRest := hc.2.2.2.2.2
  have hcLast := hcRest.2.2.2.2.2
  have rGroups := rW.2.2.2.2.2.2
  have rPlaces := rGroups.2.2.2.2.2.2
  have rI := rPlaces.1
  have rMW := fun i i' hi => (rI i i' hi).2.2.2.2.2.2.2
  have geoAt := hg.2.1
  exact
    { H := hc.1, l := hc.2.1, c := hc.2.2.1, Dw := hc.2.2.2.1, Xo := hc.2.2.2.2.1
      U := hcRest.1, V := hcRest.2.1, dict := hcRest.2.2.1, mu := hcRest.2.2.2.1, Kf := hcRest.2.2.2.2.1
      cE := hcLast.1, chiW := hcLast.2.1, x₀ := hcLast.2.2.1, iota := hcLast.2.2.2
      ψ := rW.1, θ := rW.2.1, βW := rW.2.2.1, βY := rW.2.2.2.1, nW := rW.2.2.2.2.2.1
      βV := rGroups.1, ΛV := rGroups.2.1, ΛW := rGroups.2.2.1
      Pg := rGroups.2.2.2.1, eG := rGroups.2.2.2.2.1, Sb := rGroups.2.2.2.2.2.1
      BV := fun i i' hi =>
        have h := rI i i' hi
        have hv := h.2.2.2.2
        ⟨h.1, h.2.1, hv.1, hv.2.1, (rT i i' hi).1, hv.2.2.1⟩
      MW := fun i i' hi =>
        have h := rMW i i' hi
        have hLast := h.2.2.2.2.2
        have hGeo := geoAt i i' hi
        ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
          hLast.1, hLast.2.1, hLast.2.2.1, hLast.2.2.2.1, hGeo.1, hGeo.2.1⟩
      forms := hg.2.2
      cV := fun i i' hi =>
        have h := (rI i i' hi).2.2
        ⟨h.1, h.2.1⟩
      pb := (heq_of_eq hpb).trans ((GlobalTheory.Mem.R3.Rw.frame_pb_heq hE.1 hf).trans (heq_of_eq hF.2.2.1.2.2.2.symm))
      ΛY := rW.2.2.2.2.1
      κ := fun i i' hi => (geoAt i i' hi).2.2
      ref := fun i i' hi =>
        have hT := (rT i i' hi).2
        have hRef := (rMW i i' hi).2.2.2.2.2.2.2.2.2
        ⟨hT.1, hT.2.1, hT.2.2.1, hT.2.2.2.1, hT.2.2.2.2.1, hT.2.2.2.2.2, hRef.1, hRef.2.1⟩
      jL := rPlaces.2 }
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.heckeOperator_keeps_rational_integral_levelForms : ∀ (D : D7) (V : HSp D) (hr : D.R.r ≤ V.rank) (Pg Q : Finset (Pl D.host.E)) (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (c : CoefA V) (P : principalLevelFrame.RowPsi V V.rank) (e : ReciprocityTheory.Aut.GQ D.host.E V.rank ≃* Formalism.L2.Theta.GQ V), V.gram = 1 → Seed.FrmC.StdLat V → UnitFr P → RatIso P e → Formalism.AUTREP.IsAlgWeight D.host.E V.rank (wtRep c e) → (wtRep c e).IsIrreducible → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (S : CSD D.what₂.LL) (act : Representation D.what₂.LL G₀ S.Forms) (pres : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL c.coef.ρ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).J (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).χ) (tie : Bridge.ActTie (Bridge.ratF V) pres (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).ch act) (eG : G₀ ≃* G0 Pg D.R.r) (P₀ : Subgroup G₀) (ψ₀ : P₀ →* D.what₂.LLˣ), (∀ q : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q, eG (tie.red q) = rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _))) → ∀ (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) pair del, Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam) → Bridge.CoefTie V c.coef pres lam c0 pair (nabAtr (labLL D) lam) del → (∀ k : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).J, ∃ z : 𝓞 D.what₂.LL, D.what₂.embLL (z : D.what₂.LL) = ((levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).χ k : ℂ)) → ∀ B, NG.HypOutside (stdJ (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi)) (stdX (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi)) B → ∀ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ), s.v ∉ B → Formalism.AUTREP.IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ V.rank → ∀ x, ∃ x', (fun g => pres.ext (lvlForm S act P₀ ψ₀⁻¹ x').1 (toGf P g)) = NG.tN (stdJ (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi)) s ϖ k (fun g => pres.ext (lvlForm S act P₀ ψ₀⁻¹ x).1 (toGf P g)) ∧ ∀ 𝔴 : HeightOneSpectrum (𝓞 D.what₂.LL), (∀ p : ℕ, p.Prime → s.Above p → (p : 𝓞 D.what₂.LL) ∉ 𝔴.asIdeal) → x ∈ S.lvlNab act P₀ ψ₀⁻¹ → ∃ d : 𝓞 D.what₂.LL, d ∉ 𝔴.asIdeal ∧ d • x' ∈ S.lvlNab act P₀ ψ₀⁻¹ := by
  first | exact @GlobalTheory.MtInHecke.tN_lvlForm | exact GlobalTheory.MtInHecke.tN_lvlForm | (intros; apply GlobalTheory.MtInHecke.tN_lvlForm <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stepNearLifts_component_mem_localChartGroup : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), FrNear I l Z a (k (chOf c)) fb → ∀ (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ κ ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), ∀ g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb (I.cst a).D P κ g → (∀ g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, CongE P.1 ((I.cst a).D P) g g' → ∃ κ' : (I.stp u a i).G c.1, Keeps I κ' ((I.stp u a i).rep c) ∧ LiftsInv I κ' P g' ∧ ∀ P', P' ≠ P → LiftsInv I κ' P' 1) → bc (prV (E := (I.rec7 l Z).host.E) v) κ ∈ (K (chOf c)).lev.Uloc v := by
  first | exact @GlobalTheory.Mem.Col2.AdT.LevGe.mem_uloc | exact GlobalTheory.Mem.Col2.AdT.LevGe.mem_uloc | (intros; apply GlobalTheory.Mem.Col2.AdT.LevGe.mem_uloc <;> assumption)
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

theorem _root_.GlobalTheory.T.baseLevelComplexPoints_injective_extendedData_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        Function.Injective ((z'.R.toCx3 z'.F).w0C false j')) := by
  first | exact @GlobalTheory.Mem.R3.LiftInj.baseLevelComplexPoints_injective_extendedData | exact GlobalTheory.Mem.R3.LiftInj.baseLevelComplexPoints_injective_extendedData | (intros; apply GlobalTheory.Mem.R3.LiftInj.baseLevelComplexPoints_injective_extendedData <;> assumption)

end
end

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

theorem _root_.GlobalTheory.T.goodCharacters_extendedData_eq_map_smallerData : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (e : Gc B w.px ≃* Gc B' w'.px), (∀ g, HEq (e g) g) → ∀ χ' : Gc B' w'.px → (w'.st Z').toD7.what₂.LL, χ' ∈ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.lvlA z'.F.P0 z'.F.ψ0).X ↔ ∃ χ ∈ ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.lvlA z.F.P0 z.F.ψ0).X, χ' = fun g => φ (χ (e.symm g))) := by
  exact @GlobalTheory.Mem.R3.DefLatBC.good_ext

end
end
