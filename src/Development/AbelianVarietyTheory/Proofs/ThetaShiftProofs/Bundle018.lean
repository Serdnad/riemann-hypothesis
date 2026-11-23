module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle011
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormalThetaSumShiftPeriodDiv
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumLocallyUniformlyOnTerm
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSymplecticCoordinatesOfIsPeriod
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusProjPeriodZeroEqReal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle001
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj

namespace GlobalTheory.FibreFrame

variable {K R R' : Type} [CommRing K] [CommRing R] [CommRing R'] {X Y Z : Scheme.{0}} {L : LB Z} {m : ℕ}

theorem le_wchart {π : X ⟶ Z} {q : Sp R ⟶ X} {j : L.ι} (h : ⊤ ≤ (q ≫ π) ⁻¹ᵁ L.U j) :
    ⊤ ≤ q ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => π) (fun _ => j) :=
  fun _ hz => Set.mem_iInter.2 fun _ => h hz

theorem sval_spMap {π : X ⟶ Z} (s : SecP L π m) (ρ : R →+* R') (q : Sp R ⟶ X) {j : L.ι}
    (h : ⊤ ≤ (q ≫ π) ⁻¹ᵁ L.U j) : ArcPts.sval s (spMap ρ ≫ q) j = ρ (ArcPts.sval s q j) :=
  HolHom.valR_spMap ρ q _ (le_wchart h) _

theorem exists_pull {π : X ⟶ Z} (s : SecP L π m) (h : Y ⟶ X) {π' : Y ⟶ Z} (e : h ≫ π = π') :
    ∃ s' : SecP L π' m, (∀ j (le : LB.wchart L (fun _ : Fin 1 => π') j ≤ h ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => π) j),
        s'.f j = (Y.presheaf.map (homOfLE le).op).hom ((h.app _).hom (s.f j))) ∧
      ∀ (R : Type) [CommRing R] (q : Sp R ⟶ Y) (j : L.ι), ⊤ ≤ (q ≫ π') ⁻¹ᵁ L.U j →
        ArcPts.sval s' q j = ArcPts.sval s (q ≫ h) j := by
  subst e
  refine ⟨DVR.pullSec L (fun _ : Fin 1 => π) (fun _ => (m : ℤ)) s h, fun _ _ => rfl, fun R _ q j hj => ?_⟩
  exact (HolHom.valR_res q _ _ (le_wchart hj)).trans (HolHom.valR_comp q h _ _).symm

theorem res_constFn (p : X ⟶ Sp K) {U V : X.Opens} (h : V ≤ U) (a : K) :
    (X.presheaf.map (homOfLE h).op).hom (constFn p U a) = constFn p V a :=
  congrArg (fun q : Γ(Sp K, ⊤) ⟶ Γ(X, V) => q.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
    (p.appLE_map (U := ⊤) (V := U) le_top (homOfLE h).op)

theorem valR_constFn (p : X ⟶ Sp K) (f : K →+* R) (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) (U : X.Opens)
    (h : ⊤ ≤ q ⁻¹ᵁ U) (a : K) : valR q U (constFn p U a) = f a := by
  refine (HolHom.valR_appLE q p ⊤ U le_top _ h).trans ?_
  rw [hq, Conv.valR_spMap_top]

def comb (p : X ⟶ Sp K) {M : LB X} {n : ℕ} (r : Fin n → K) (σ : Fin n → M.Sec) : M.Sec where
  f j := ∑ i, constFn p _ (r i) * (σ i).f j
  compat j k := by

    rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, res_constFn, res_constFn, (σ i).compat j k]
    ring

theorem valR_comb (p : X ⟶ Sp K) {M : LB X} {n : ℕ} (r : Fin n → K) (σ : Fin n → M.Sec) (f : K →+* R)
    (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) (j : M.ι) (h : ⊤ ≤ q ⁻¹ᵁ M.U j) :
    valR q _ ((comb p r σ).f j) = ∑ i, f (r i) * valR q _ ((σ i).f j) := by

  simp only [← valR_constFn p f q hq _ h, HolHom.valR_eq _ _ h, comb, map_sum, map_mul]

theorem sval_comb {π : X ⟶ Z} (p : X ⟶ Sp K) {n : ℕ} (r : Fin n → K) (σ : Fin n → SecP L π m) (f : K →+* R)
    (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) {j : L.ι} (h : ⊤ ≤ (q ≫ π) ⁻¹ᵁ L.U j) :
    ArcPts.sval (comb p r σ : SecP L π m) q j = ∑ i, f (r i) * ArcPts.sval (σ i) q j := by
  exact valR_comb p r σ f q hq (fun _ => j) (le_wchart h)

theorem ext_sval {π : X ⟶ Z} {s s' : SecP L π m}
    (h : ∀ (R : Type) [CommRing R] (q : Sp R ⟶ X) (j : L.ι), ⊤ ≤ (q ≫ π) ⁻¹ᵁ L.U j →
      ArcPts.sval s q j = ArcPts.sval s' q j) (j : Fin 1 → L.ι) : s.f j = s'.f j := by
  obtain ⟨j, rfl⟩ : ∃ k, j = fun _ => k := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim _ _)⟩
  refine TopCat.Presheaf.section_ext X.sheaf _ _ _ fun x hx => ?_
  obtain ⟨V, hV, hxV, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X) hx
  obtain ⟨q, hq, hv⟩ := Conv.exists_point_of_ringHom hV (RingHom.id _)
  have hle' : V ≤ LB.wchart L (fun _ : Fin 1 => π) (fun _ => j) := hle
  have e := h _ q j fun z hz => LB.wchart_le L (fun _ : Fin 1 => π) (fun _ => j) 0 (hle' (hq hz))
  have e1 := (hv _).symm.trans (HolHom.valR_res q hle' (s.f fun _ => j) hq)
  have e2 := (hv _).symm.trans (HolHom.valR_res q hle' (s'.f fun _ => j) hq)
  exact X.presheaf.germ_ext V hxV (homOfLE hle') (homOfLE hle') (e1.trans (e.trans e2.symm))

def Rep {π : X ⟶ Z} (p : X ⟶ Sp K) {n : ℕ} (σ : Fin n → SecP L π m) (s : SecP L π m) (c : Fin n → K) : Prop :=
  ∀ (R : Type) [CommRing R] (f : K →+* R) (q : Sp R ⟶ X) (j : L.ι), q ≫ p = spMap f → ⊤ ≤ (q ≫ π) ⁻¹ᵁ L.U j →
    ArcPts.sval s q j = ∑ i, f (c i) * ArcPts.sval (σ i) q j

theorem rep_comb {π : X ⟶ Z} (p : X ⟶ Sp K) {n : ℕ} (σ : Fin n → SecP L π m) (c : Fin n → K) :
    Rep p σ (comb p c σ) c := fun _ _ f q _ hq h => sval_comb p c σ f q hq h

theorem rep_iff {π : X ⟶ Z} (p : X ⟶ Sp K) {n : ℕ} (σ : Fin n → SecP L π m) (s : SecP L π m) (c : Fin n → K) :
    Rep p σ s c ↔ ∀ j, s.f j = (comb p c σ).f j := by
  refine ⟨fun H => ext_sval fun R _ q j hj => ?_, fun H R _ f q j hq hj => ?_⟩
  · have hq : q ≫ p = spMap (Spec.preimage (q ≫ p)).hom := (Spec.map_preimage _).symm
    exact (H R _ q j hq hj).trans (sval_comb p c σ _ q hq hj).symm
  · exact (congrArg (valR q _) (H _)).trans (sval_comb p c σ f q hq hj)

theorem rep_transport {π : X ⟶ Z} {p : X ⟶ Sp K} {n : ℕ} {σ : Fin n → SecP L π m} (e : Y ≅ X) {π' : Y ⟶ Z}
    {p' : Y ⟶ Sp K} (hπ : e.hom ≫ π = π') (hp : e.hom ≫ p = p') {σ' : Fin n → SecP L π' m}
    (hσ : ∀ i (R : Type) [CommRing R] (q : Sp R ⟶ Y) (j : L.ι), ⊤ ≤ (q ≫ π') ⁻¹ᵁ L.U j →
      ArcPts.sval (σ' i) q j = ArcPts.sval (σ i) (q ≫ e.hom) j)
    (H : ∀ s, ∃! c, Rep p σ s c) (s' : SecP L π' m) : ∃! c, Rep p' σ' s' c := by
  subst hπ hp
  obtain ⟨s, -, hs⟩ := exists_pull s' e.inv (π' := π) (e.inv_hom_id_assoc π)
  have key : ∀ c, Rep (e.hom ≫ p) σ' s' c ↔ Rep p σ s c := fun c => by
    constructor
    · intro h R _ f q j hq hj
      have hj' : ⊤ ≤ ((q ≫ e.inv) ≫ e.hom ≫ π) ⁻¹ᵁ L.U j := by simpa using hj
      rw [hs R q j hj, h R f _ j (by simpa using hq) hj']
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hσ i R _ j hj', Category.assoc, e.inv_hom_id, Category.comp_id]
    · intro h R _ f q j hq hj
      have hj' : ⊤ ≤ ((q ≫ e.hom) ≫ π) ⁻¹ᵁ L.U j := by simpa using hj
      have := h R f (q ≫ e.hom) j (by simpa using hq) hj'
      rw [hs R _ j hj', Category.assoc, e.hom_inv_id, Category.comp_id] at this
      rw [this]
      exact Finset.sum_congr rfl fun i _ => by rw [hσ i R _ j hj]
  simp only [key]
  exact H s


open Out in
theorem exists_frame (hS : SecBaseChangeSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ)
    (hn : 1 ≤ n) (x : S) : ∃ V : S.Opens, x ∈ V ∧ ∃ (N : ℕ) (β : ∀ (R : Type) [CommRing R] (y : Sp R ⟶ S),
      ⊤ ≤ y ⁻¹ᵁ V → Fin N → SecP P.L (pullback.fst P.A.hom y) n),
      (∀ (R : Type) [CommRing R] (y : Sp R ⟶ S) (hy : ⊤ ≤ y ⁻¹ᵁ V) (R' : Type) [CommRing R'] (y' : Sp R' ⟶ S)
        (hy' : ⊤ ≤ y' ⁻¹ᵁ V) (C : Type) [CommRing C] (q : Sp C ⟶ pullback P.A.hom y) (q' : Sp C ⟶ pullback P.A.hom y')
        (i : Fin N) (j : P.L.ι), q ≫ pullback.fst _ _ = q' ≫ pullback.fst _ _ →
        ⊤ ≤ (q ≫ pullback.fst _ _) ⁻¹ᵁ P.L.U j → ArcPts.sval (β R y hy i) q j = ArcPts.sval (β R' y' hy' i) q' j) ∧
      ∀ (R : Type) [CommRing R] (y : Sp R ⟶ S) (hy : ⊤ ≤ y ⁻¹ᵁ V) (s : SecP P.L (pullback.fst P.A.hom y) n),
        ∃! c, Rep (pullback.snd P.A.hom y) (β R y hy) s c := by
  obtain ⟨V, hV, b, hb⟩ := hS S P n hn x
  let W := overRes (T := baseOver S) V
  have key : ∀ (R : Type) [CommRing R] (y : Sp R ⟶ S), ⊤ ≤ y ⁻¹ᵁ V →
      ∃ (k : pullback P.A.hom y ⟶ (W ⊗ P.A).left) (β : Fin (n ^ P.g) → SecP P.L (pullback.fst P.A.hom y) n),
        k ≫ (snd W P.A).left = pullback.fst _ _ ∧
        (∀ i (C : Type) [CommRing C] (q : Sp C ⟶ pullback P.A.hom y) (j : P.L.ι),
          ⊤ ≤ (q ≫ pullback.fst _ _) ⁻¹ᵁ P.L.U j →
          ArcPts.sval (β i) q j = ArcPts.sval (m := n) (p := (snd W P.A).left) (b i) (q ≫ k) j) ∧
        ∀ s, ∃! c, Rep (pullback.snd P.A.hom y) β s c := by
    intro R _ y hy
    let t : Sp R ⟶ W.left := IsOpenImmersion.lift V.ι y (by
      rintro _ ⟨z, rfl⟩
      exact V.range_ι.ge (hy (x := z) trivial))
    have ht : (baseAt t).hom = y := by
      show t ≫ V.ι ≫ 𝟙 _ = y
      rw [Category.comp_id]
      exact IsOpenImmersion.lift_fac _ _ _
    have hp : IsPullback (pullback.snd P.A.hom y) (pullback.fst P.A.hom y) (baseAt t).hom P.A.hom :=
      ht ▸ (IsPullback.of_hasPullback P.A.hom y).flip
    let e : pullback P.A.hom y ≅ (baseAt t ⊗ P.A).left := hp.isoPullback
    have e₁ : e.hom ≫ (snd (baseAt t) P.A).left = pullback.fst _ _ := hp.isoPullback_hom_snd
    have e₂ : e.hom ≫ (fst (baseAt t) P.A).left = pullback.snd _ _ := hp.isoPullback_hom_fst
    have e₃ : (homAt t ▷ P.A).left ≫ (snd W P.A).left = (snd (baseAt t) P.A).left :=
      congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A)
    choose b' hb0 hb' using fun i => exists_pull (π := (snd W P.A).left) (m := n) (b i) (homAt t ▷ P.A).left e₃
    choose β _ hβ using fun i => exists_pull (b' i) e.hom e₁
    obtain ⟨hli, hsp⟩ := hb R t b' (fun i j => hb0 i j _)
    refine ⟨e.hom ≫ (homAt t ▷ P.A).left, β, (Category.assoc _ _ _).trans ((congrArg _ e₃).trans e₁), fun i C _ q j hj => ?_,
      rep_transport (p := (fst (baseAt t) P.A).left) e e₁ e₂ hβ fun s => ?_⟩
    · rw [hβ i C q j hj, hb' i C _ j (by rw [Category.assoc, e₁]; exact hj), Category.assoc]
    have bij := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv
    have key : ∀ c : Fin (n ^ P.g) → R, Rep (fst (baseAt t) P.A).left b' s c ↔
        ∑ i, (show Γ((baseAt t).left, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c i)) •
          (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t)) = SecM.ofSec P.A s := fun c => by
      have ev : ∀ j, (∑ i, (show Γ((baseAt t).left, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c i)) •
          (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t))).1 j =
          (comb (K := R) (fst (baseAt t) P.A).left c b').f j := fun j => by
        rw [Submodule.coe_sum, Finset.sum_apply]
        rfl
      rw [rep_iff]
      exact ⟨fun h => Subtype.ext (funext fun j => (ev j).trans (h j).symm),
        fun h j => (congrFun (congrArg Subtype.val h) j).symm.trans (ev j)⟩
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
      (hsp.ge (Submodule.mem_top : SecM.ofSec P.A s ∈ ⊤))
    choose a ha using fun i => bij.2 (r i)
    obtain rfl : (fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a i)) = r := funext ha
    refine ⟨a, (key a).2 hr, fun a' ha' => funext fun i => bij.1 ?_⟩
    exact Fintype.linearIndependent_iffₛ.1 hli _ _ (((key a').1 ha').trans hr.symm) i
  choose k β hk hβ hr using key
  refine ⟨V, hV, _, β, fun R _ y hy R' _ y' hy' C _ q q' i j hq hj => ?_, hr⟩
  have hm : Mono (snd W P.A).left := by
    have : Mono W.hom := inferInstanceAs (Mono (V.ι ≫ 𝟙 S))
    exact inferInstanceAs (Mono (pullback.snd W.hom P.A.hom))
  rw [hβ R y hy i C q j hj, hβ R' y' hy' i C q' j (hq ▸ hj)]
  congr 1
  rw [← cancel_mono (snd W P.A).left, Category.assoc, Category.assoc, hk, hk, hq]

end GlobalTheory.FibreFrame
end
end

section

noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem exists_isFactor : ∀ (O : Type) [CommRing O] [StarRing O] (A : AnArc O), ∃ (lin : ℂ → A.La → A.V →ₗ[ℂ] ℂ) (cst : ℂ → A.La → ℂ), IsFactor A lin cst ∧ ∀ w la la', lin w la (A.Pw w la') - lin w la' (A.Pw w la) = -(2 * Real.pi * Complex.I) * A.EF la la' := by
  intro O _ _ A
  refine ⟨fun _ la => A.lin la, A.logConst, fun w la v j α th h m => ?_, fun w la la' => ?_⟩
  · rw [A.term_add_period h w la m v, A.perFactor_eq_exp, A.L_apply]
  · rw [A.lin_Pw_sub]; ring

end GlobalTheory.ArcPts
end
end

section

noncomputable section

namespace GlobalTheory.ArcPts

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

section
variable {O : Type} [CommRing O] [StarRing O] {A : AnArc O} {T : ℝ} (hT : A.IsConvLine T) {j : ℕ} [NeZero j]
include hT

theorem fsum_mem_halfRing {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α) (v : A.V) :
    ∃ hm : A.FSum j α th v ∈ Conv.halfRing T, ∀ w hw, Conv.ev T w hw ⟨_, hm⟩ = A.Sum j α th w v :=
  ⟨fun _ hw => (AnArc.hasSum_coeff_FSum hT h hw v).summable,
    fun _ hw => Conv.ev_eq_of_hasSum hw _ (AnArc.hasSum_coeff_FSum hT h hw v)⟩

theorem exists_dfsum_halfRing {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α) (z₀ : A.V) :
    ∃ F : Conv.halfRing T, IsDFSum A j α th z₀ F ∧
      ∀ w hw, Conv.ev T w hw F = fderiv ℂ (A.Sum j α th w) 0 z₀ := by
  let S : ℂ⸨X⸩ := HahnSeries.ofSuppBddBelow (fun n => fderiv ℂ (fun v => (A.FSum j α th v).coeff n) 0 z₀)
    ⟨-A.be α α, fun n hn => by
      by_contra hlt
      exact hn (by simp only [AnArc.fderiv_coeff_FSum_eq_zero (not_le.1 hlt), zero_apply])⟩
  exact ⟨⟨S, fun _ hw => (AnArc.hasSum_fderiv_coeff_FSum hT h hw 0 z₀).summable⟩, fun _ => rfl,
    fun _ hw => Conv.ev_eq_of_hasSum hw _ (AnArc.hasSum_fderiv_coeff_FSum hT h hw 0 z₀)⟩

theorem differentiable_ev_comb (f : A.V → Conv.halfRing T) (hf : IsComb A j (Conv.halfRing T) (fun v => f v))
    (w : ℂ) (hw : T < w.im) : Differentiable ℂ (fun v => Conv.ev T w hw (f v)) := by
  obtain ⟨n, r, α, th, h1, h2⟩ := hf
  have key : (fun v => Conv.ev T w hw (f v)) =
      fun v => ∑ i, Conv.ev T w hw ⟨r i, (h1 i).1⟩ * A.Sum j (α i) (th i) w v := by
    funext v
    choose hm hv using fun i => fsum_mem_halfRing hT (h1 i).2 v
    have e : f v = ∑ i, (⟨r i, (h1 i).1⟩ : Conv.halfRing T) * ⟨_, hm i⟩ := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      exact h2 v

    rw [e, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hv i w hw]
  rw [key]
  exact Differentiable.fun_sum fun i _ =>
    (AnArc.differentiable_Sum hT (NeZero.ne j) (h1 i).2 hw).const_mul _

end

theorem exists_formal_convergence : ∀ (O : Type) [CommRing O] [StarRing O] (A : AnArc O), ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ (j : ℕ) [NeZero j], (∀ α, ∀ th ∈ A.Theta j α, (∀ v, ∃ h : A.FSum j α th v ∈ Conv.halfRing T, ∀ w hw, Conv.ev T w hw ⟨_, h⟩ = A.Sum j α th w v) ∧ ∀ z₀, ∃ F : Conv.halfRing T, IsDFSum A j α th z₀ F ∧ ∀ w hw, Conv.ev T w hw F = fderiv ℂ (A.Sum j α th w) 0 z₀) ∧ ∀ f : A.V → Conv.halfRing T, IsComb A j (Conv.halfRing T) (fun v => f v) → ∀ w hw, Differentiable ℂ (fun v => Conv.ev T w hw (f v)) := by
  intro O _ _ A
  obtain ⟨T₀, h₀⟩ := A.exists_isConvLine
  refine ⟨T₀, fun T hT j _ => ?_⟩
  have h := h₀.mono hT
  exact ⟨fun α th hth => ⟨fsum_mem_halfRing h hth, exists_dfsum_halfRing h hth⟩, differentiable_ev_comb h⟩

end GlobalTheory.ArcPts
end
end

section

noncomputable section

namespace GlobalTheory.TauTwist

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorusExt

theorem exists_ratio {F : Type} [Field F] {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Sp F ⟶ X)} {ε : K → ℤ} {φ' : K' → (Sp F ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')} (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ x : Fˣ, ∀ y J, Good L y J → val t (𝟙 _) y J = unitAt (𝟙 _) y x * val t' (𝟙 _) y J := by
  let y : Sp F := IsLocalRing.closedPoint F
  choose I hI using fun q : Sp F ⟶ X => exists_chart hL (q y)
  refine ⟨(stalkUnits y).symm (val t (𝟙 _) y I * (val t' (𝟙 _) y I)⁻¹), fun y' J hJ => ?_⟩
  obtain rfl : y = y' := Subsingleton.elim (α := PrimeSpectrum F) y y'
  refine (val_eq_of_val_eq hF ht (scaleGen_isGen _ _ ht') hI hJ (Eq.trans ?_ (val_scale _ t' _ hI).symm)).trans
    (val_scale _ t' _ hJ)
  rw [unitAt_apply, gm_unitOn, MulEquiv.apply_symm_apply, inv_mul_cancel_right]

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

section Values

variable {T : Over (Sp R)} (κ : T ⟶ TK R) {z : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J)
include hJ

theorem val_tau_symm (a b : D.X) : val (D.tau a b) κ.left z J = val (D.tau b a) κ.left z J := by
  rw [val_tau D a b _ hJ, val_tau D b a _ hJ, add_comm b a, mul_right_comm (val (D.psi (a + b)) _ z J)]

variable (hB : D.TauBimult)
include hB

theorem val_tau_add (a a' b : D.X) :
    val (D.tau (a + a') b) κ.left z J * th D z J (cP D T a) (cP D T a') (cP D T b) =
      val (D.tau a b) κ.left z J * val (D.tau a' b) κ.left z J := by
  have := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB a a' b) κ.left).trans (val_mul hJ _ _ _))
  refine Eq.trans (congrArg₂ (· * ·) rfl ?_) this
  refine Eq.trans ?_ (val_cub D.cub κ hJ (cP D _ a) (cP D _ a') (cP D _ b)).symm
  rw [comp_cP, comp_cP, comp_cP]

theorem val_tau_nsmul (k : ℕ) (a b : D.X) :
    val (D.tau (k • a) b) κ.left z J * cubN (th D z J) k 1 (cP D T a) (cP D T b) = val (D.tau a b) κ.left z J ^ k := by
  have C : IsCub (th D (T := T) z J) := isCub_cubV D.cub hJ
  induction k with
  | zero =>
    have e := val_tau_add κ hJ hB 0 0 b
    rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at e
    rw [zero_nsmul, pow_zero, mul_eq_left.1 e.symm]
    exact _root_.mul_one _
  | succ k ih =>
    have e := val_tau_add κ hJ hB (k • a) a b
    rw [cPoint_nsmul] at e
    rw [succ_nsmul, cubN, Finset.prod_range_succ, mul_comm (∏ _ ∈ _, _), ← _root_.mul_assoc, _root_.one_mul, e, pow_succ,
      ← ih, cubN, mul_right_comm]

end Values


variable (D) in
def canφ (y y' : D.X) : Fin 4 → ((𝟙_ (Over (Sp R))).left ⟶ D.P.A.left) :=
  ![(D.c y * D.c y').left, (D.c y).left, (D.c y').left, (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A).left]

def canε (n : ℕ) : Fin 4 → ℤ := ![-(n ^ 2 : ℕ), (n ^ 2 : ℕ), (n ^ 2 : ℕ), -(n ^ 2 : ℕ)]

variable {n : ℕ} (hc : ∀ y, D.c y ^ n = 1)
include hc

theorem exists_canGen (y y' : D.X) : ∃ t : LB.Gen (LB.LinComb D.P.L (canφ D y y') (canε n)), t.IsGen ∧
    ∀ (T : Over (Sp R)) (z : T.left) (J), Good D.P.L z J →
      val t (toUnit T).left z J = cubN (th D z J) n 1 (cP D T y) (cP D T y') ^ n := by
  obtain ⟨t, ht, hv⟩ := exists_cubN D.cub 1 (D.c y) (D.c y') n
  obtain ⟨t', ht', hv'⟩ := exists_gen D.P.isLB (φ' := canφ D y y') (ε' := canε n) (fun U _ h => by
      rw [hc y]
      apply Additive.ofMul.injective
      simp [canφ, canε, Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module) (GeneratorPullback.powGen D.P.L _ _ t n) (powGen_isGen _ _ _ _ ht n)
  refine ⟨t', ht', fun T z J hJ => (hv' _ _ z J hJ).trans ((val_powGen _ _ _ _ _).trans (congrArg (· ^ n) ?_))⟩
  refine (hv T (toUnit T) z J hJ).trans ?_
  rw [MonObj.comp_one]
  rfl

def canGen (y y' : D.X) : LB.Gen (LB.LinComb D.P.L (canφ D y y') (canε n)) := (exists_canGen hc y y').choose

theorem val_canGen (y y' : D.X) (T : Over (Sp R)) {z : T.left} {J} (hJ : Good D.P.L z J) :
    val (canGen hc y y') (toUnit T).left z J = cubN (th D z J) n 1 (cP D T y) (cP D T y') ^ n :=
  (exists_canGen hc y y').choose_spec.2 T z J hJ

def canK (y y' : D.X) := LB.pullGen D.P.L _ _ (canGen hc y y') (toUnit (TK R)).left

theorem val_canK (y y' : D.X) {T : Over (Sp R)} (κ : T ⟶ TK R) {z : T.left} {J} (hJ : Good D.P.L z J) :
    val (canK hc y y') κ.left z J = cubN (th D z J) n 1 (cP D T y) (cP D T y') ^ n := by
  refine (val_pull hJ _ _ _).trans ?_
  rw [← Over.comp_left, comp_toUnit]
  exact val_canGen hc y y' T hJ

theorem cPoint_nsmul_eq_one (T : Over (Sp R)) (y : D.X) : cP D T (n • y) = 1 := by
  rw [cPoint_nsmul, cP, ← MonObj.comp_pow, hc, MonObj.comp_one]

theorem val_tau_pow (hB : D.TauBimult) (a b : D.X) {T : Over (Sp R)} (κ : T ⟶ TK R) {z : T.left} {J}
    (hJ : Good D.P.L z J) :
    val (D.tau a b) κ.left z J ^ n ^ 2 = val (D.tau (n • a) (n • b)) κ.left z J * val (canK hc a b) κ.left z J := by
  have C : IsCub (th D (T := T) z J) := isCub_cubV D.cub hJ
  have e := val_tau_nsmul κ hJ hB n b (n • a)
  rw [cPoint_nsmul_eq_one hc, C.N_one, _root_.mul_one, val_tau_symm κ hJ, val_tau_symm κ hJ b] at e
  rw [val_canK hc a b κ hJ, e, ← mul_pow, val_tau_nsmul κ hJ hB, ← pow_mul, sq]

theorem exists_tau_const (a b : D.X) : ∃ x : (FractionRing R)ˣ, ∀ y J, Good D.P.L y J →
    val (D.tau (n • a) (n • b)) (𝟙 (TK R).left) y J = unitAt (𝟙 (TK R).left) y x := by
  obtain ⟨x, hx⟩ := exists_ratio (F := FractionRing R) D.P.isLB (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
    have a₁ : ∀ w : D.X, ptK (D.c (n • w)) = (1 : TK R ⟶ D.P.A).left := fun w =>
      congrArg (fun q => q.left) (cPoint_nsmul_eq_one hc (TK R) w)
    have a₀ : (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TK R ⟶ D.P.A).left := rfl
    simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, neg_neg, zpow_neg, zpow_one,
      ← nsmul_add, a₁, a₀, Fintype.prod_empty]
    simp) (tau_isGen D (n • a) (n • b)) oneGen_isGen
  exact ⟨x, fun y J hJ => (hx y J hJ).trans ((congrArg₂ (· * ·) rfl (val_one _)).trans (_root_.mul_one _))⟩

def kappa (a b : D.X) : (FractionRing R)ˣ := (exists_tau_const hc a b).choose

theorem unitAt_kappa (a b : D.X) {y : (TK R).left} {J} (hJ : Good D.P.L y J) :
    unitAt (𝟙 (TK R).left) y (kappa hc a b) = val (D.tau (n • a) (n • b)) (𝟙 (TK R).left) y J :=
  ((exists_tau_const hc a b).choose_spec y J hJ).symm

variable {O : Type} [CommRing O] [StarRing O] [Module O D.X]

end GlobalTheory.TauTwist
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory

theorem fibre_comparison : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (A : AnArc (𝓞 E)) (lin : ℂ → A.La → A.V →ₗ[ℂ] ℂ) (cst : ℂ → A.La → ℂ) , (∀ w la la', lin w la (A.Pw w la') - lin w la' (A.Pw w la) = -(2 * Real.pi * Complex.I) * A.EF la la') → Module.finrank ℂ A.V = g → ∃ T₀ : ℝ, ∀ (w : ℂ) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (y₀ : Sp ℂ ⟶ Xo.X) (π : A.V → (Over.mk y₀ ⟶ Xo.univ.t.G)) fr, T₀ < w.im → IsPeriod (Fu.Di i) ty P → Fu.u i P = y₀ → IsFibAt A Xo.univ.t lin cst w y₀ π fr → Function.Surjective π ∧ ∃ (h : A.V ≃L[ℂ] (Fin g → ℂ)) (gam : (Fu.Di i).La ≃ₗ[𝓞 E] A.La), (∀ v, (Fu.ex i P (h v)).left = (π v).left) ∧ (∀ u, P u = h (A.Pw w (gam u))) ∧ (∀ u v, A.EF (gam u) (gam v) = (Fu.Di i).EF u v) ∧ ∀ (e : 𝓞 E) v k, h (A.actV e v) k = ty k (e : E) * h v k := by
  intro _ _ E _ _ _ H _ D l Xo σ g ty Fu A lin cst halt hdim
  refine ⟨0, fun w i P y₀ π fr _ hP hy hF => ?_⟩
  subst hy
  have hrk : Module.finrank ℤ A.La = 2 * g := by
    rw [A.finrank_La, ← Module.finrank_mul_finrank ℝ ℂ A.V, Complex.finrank_real_complex, hdim]
  obtain ⟨h, gam, h1, h2, h3, -, h5⟩ := fibre_hom_eq_exponential Fu i hP hdim hrk A.EF A.EF_bijective (A.Pw w) π
    hF.add hF.hol hF.per fr hF.fr_hol (fun j v hv => ((hF.frm v).1 j hv).ne_zero)
    (fun j j' v hv => (hF.frm v).2 j j' hv) (lin w) (cst w) (fun a j v hv => hF.fac a v j hv) (halt w)
  obtain ⟨h6, gamO, h7⟩ := h5 (fun e => A.actV e) hF.act (A.Pw_smul w)
  refine ⟨fun y => ?_, h.toContinuousLinearEquiv, gamO.symm, fun v => ?_, fun u => ?_, fun u v => ?_, h6⟩
  · obtain ⟨z, rfl⟩ := Fu.ex_onto i P hP y
    exact ⟨h.symm z, by rw [h1, h.apply_symm_apply]⟩
  · rw [h1]; rfl
  · change P u = h _
    rw [h2, ← h7, gamO.apply_symm_apply]
  · rw [← h3, ← h7, ← h7, gamO.apply_symm_apply, gamO.apply_symm_apply]

end GlobalTheory
end
end
