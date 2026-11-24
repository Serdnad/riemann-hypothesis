module

import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfSec
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenHopfOrder
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDenominatorRegular
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinitePartLePreimageOfClosedFibreSubset
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFinOpenSubOfFinite
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwpairAlg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
public import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.SubOrder

noncomputable section

namespace PositivityTheory.HtPt.Twpair

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

theorem isFinOpenSub [IsLocalRing R] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (hfin : IsFinite (U.ι ≫ Γ.G.hom))
    (hU : ∀ x : Γ.G.left, Γ.G.hom x = IsLocalRing.closedPoint R → x ∈ U) : Γ.IsFinOpenSub U := by
  intros
  apply _root_.GlobalTheory.CompanionTheory.Ar.BT.QFGroup.isFinOpenSub_of_closedFibre <;> assumption

theorem regularAt_generic [Finite T] (Γ : QFGroup R T) (f : T → FractionRing R) (g : Γ.G.left)
    (hg : (Γ.G.hom g).asIdeal = ⊥) : Γ.RegularAt f g := by
  apply _root_.PositivityTheory.HtPt.Twhopf.regularAt_generic <;> assumption

theorem valHom_top_comp {B C : Type} [CommRing B] [CommRing C] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X)
    (φ : B →+* C) (s : Γ(X, ⊤)) :
    valAt (Spec.map (CommRingCat.ofHom φ) ≫ x) ⊤ le_top s = φ (valAt x ⊤ le_top s) := by
  have e : (x.appLE ⊤ ⊤ le_top).hom s =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (valAt x ⊤ le_top s) := by
    simp [valAt]
  have e1 := valHom_appLE (Spec.map (CommRingCat.ofHom φ)) x (V := ⊤) (W := ⊤) le_top le_top le_top s
  have e2 := valHom_spec_top φ le_top (valAt x ⊤ le_top s)
  exact e1.symm.trans ((congrArg _ e).trans e2)

section sec

variable {Γ : QFGroup R T} {U : Γ.G.left.Opens} {hU : IsAffineOpen U}
variable [Algebra R Γ(Γ.G.left, U)]
  (hρ : hU.fromSpec ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R Γ(Γ.G.left, U))))

include hρ

theorem exists_tensor_of_prod (s : Γ((Γ.G ⊗ Γ.G).left, ⊤)) :
    ∃ c : Γ(Γ.G.left, U) ⊗[R] Γ(Γ.G.left, U), ∀ (a b : T) (ha : ⊤ ≤ (Γ.pt a).left ⁻¹ᵁ U)
      (hb : ⊤ ≤ (Γ.pt b).left ⁻¹ᵁ U),
      valAt (lift (Γ.pt a) (Γ.pt b)).left ⊤ le_top s =
        Algebra.TensorProduct.productMap (valAlg hρ a ha) (valAlg hρ b hb) c := by
  let B := Γ(Γ.G.left, U)
  let Q : Over (Spec (CommRingCat.of R)) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (B ⊗[R] B))))
  let iL : B →+* B ⊗[R] B := (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B).toRingHom
  let iR : B →+* B ⊗[R] B := (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B).toRingHom
  let x : Q ⟶ Γ.G := Over.homMk (Spec.map (CommRingCat.ofHom iL) ≫ hU.fromSpec) (by
    simp only [Category.assoc, Q, Over.mk_hom]
    rw [hρ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2)
  let y : Q ⟶ Γ.G := Over.homMk (Spec.map (CommRingCat.ofHom iR) ≫ hU.fromSpec) (by
    simp only [Category.assoc, Q, Over.mk_hom]
    rw [hρ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp [iR, Algebra.TensorProduct.algebraMap_apply'])
  refine ⟨valAt (lift x y).left ⊤ le_top s, ?_⟩
  intro a b ha hb
  let φ : B ⊗[R] B →+* FractionRing R :=
    (Algebra.TensorProduct.productMap (valAlg hρ a ha) (valAlg hρ b hb)).toRingHom
  let w : genPt R ⟶ Q := Over.homMk (Spec.map (CommRingCat.ofHom φ)) (by
    simp only [Q, Over.mk_hom, genPt]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp [φ])
  have hwx : w ≫ x = Γ.pt a := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, w, x, Over.homMk_left]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : φ.comp iL = valHom (Γ.pt a).left U ha := by
      ext r
      simp [φ, iL]
      try rfl
    rw [this]
    exact spec_valHom_fromSpec _ hU ha
  have hwy : w ≫ y = Γ.pt b := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, w, y, Over.homMk_left]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : φ.comp iR = valHom (Γ.pt b).left U hb := by
      ext r
      simp [φ, iR]
      try rfl
    rw [this]
    exact spec_valHom_fromSpec _ hU hb
  have hw : w ≫ lift x y = lift (Γ.pt a) (Γ.pt b) := by
    rw [comp_lift, hwx, hwy]
  have e : (lift (Γ.pt a) (Γ.pt b)).left = Spec.map (CommRingCat.ofHom φ) ≫ (lift x y).left := by
    rw [← hw]; rfl
  have e2 := valHom_congr e ⊤ le_top le_top
  exact (DFunLike.congr_fun e2 s).trans (valHom_top_comp (lift x y).left φ s)

end sec

theorem exists_order [ValuationRing R] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (hF : Γ.IsFinOpenSub U) :
    ∃ A : Subalgebra R (subH Γ hF → R), IsHopfOrder A ∧
      (∀ f ∈ A, ∃ s : Γ(Γ.G.left, U), ∀ (t : subH Γ hF) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U),
        valAt (Γ.pt t).left U h s = algebraMap R _ (f t)) ∧
      ∀ (s : Γ((Γ.G ⊗ Γ.G).left, ⊤)) (g : subH Γ hF × subH Γ hF → R),
        (∀ z : subH Γ hF × subH Γ hF, valAt (lift (Γ.pt z.1) (Γ.pt z.2)).left ⊤ le_top s = algebraMap R _ (g z)) →
        g ∈ prodSpan A := by
  have hU := isAffineOpen_of_fin Γ hF
  letI : Algebra R Γ(Γ.G.left, U) := (secRho Γ hU).toAlgebra
  have hρ : hU.fromSpec ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R Γ(Γ.G.left, U))) :=
    fromSpec_hom Γ hU
  have hfin := sec_finite hρ hF
  have inj : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R _
  have hval : ∀ (t : subH Γ hF) (s : Γ(Γ.G.left, U)),
      ∃ r : R, algebraMap R (FractionRing R) r = valAlg hρ t t.2 s := by
    intro t s
    have h1 : IsIntegral R s := Algebra.IsIntegral.isIntegral s
    exact IsIntegrallyClosed.isIntegral_iff.1 (h1.map (valAlg hρ t t.2))
  choose Φf hΦf using hval
  let Φ : Γ(Γ.G.left, U) →ₐ[R] (subH Γ hF → R) :=
    { toFun := fun s t => Φf t s
      map_one' := funext fun t => inj (by simp [hΦf])
      map_mul' := fun a b => funext fun t => inj (by simp [hΦf])
      map_zero' := funext fun t => inj (by simp [hΦf])
      map_add' := fun a b => funext fun t => inj (by simp [hΦf])
      commutes' := fun r => funext fun t => inj (by
        rw [hΦf, AlgHom.commutes]; rfl) }
  have hΦ : ∀ (s : Γ(Γ.G.left, U)) (t : subH Γ hF) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U),
      valAt (Γ.pt t).left U h s = algebraMap R _ (Φ s t) := fun s t h => (hΦf t s).symm
  have key : ∀ c' : Γ(Γ.G.left, U) ⊗[R] Γ(Γ.G.left, U), ∃ g ∈ prodSpan Φ.range, ∀ z : subH Γ hF × subH Γ hF,
      algebraMap R (FractionRing R) (g z) =
        Algebra.TensorProduct.productMap (valAlg hρ z.1 z.1.2) (valAlg hρ z.2 z.2.2) c' := by
    intro c'
    induction c' with
    | tmul a b =>
      refine ⟨fun z => Φ a z.1 * Φ b z.2, Submodule.subset_span ⟨Φ a, ⟨a, rfl⟩, Φ b, ⟨b, rfl⟩, rfl⟩, fun z => ?_⟩
      simp only [map_mul, Algebra.TensorProduct.productMap_apply_tmul]
      exact congrArg₂ (· * ·) (hΦ a z.1 z.1.2).symm (hΦ b z.2 z.2.2).symm
    | add a b ha hb =>
      obtain ⟨g, hg, hg'⟩ := ha
      obtain ⟨g₂, hg₂, hg₂'⟩ := hb
      exact ⟨g + g₂, Submodule.add_mem _ hg hg₂, fun z => by simp [hg', hg₂']⟩
  have hfinA : Module.Finite R Φ.range :=
    Module.Finite.of_surjective Φ.rangeRestrict.toLinearMap Φ.rangeRestrict_surjective
  refine ⟨Φ.range, ⟨hfinA, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · have htf : Module.IsTorsionFree R Φ.range :=
      Function.Injective.moduleIsTorsionFree Φ.range.val.toLinearMap Subtype.val_injective (fun _ _ => rfl)
    have : Module.Flat R Φ.range := by
      rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
      exact htf
    have : Module.Free R Φ.range := Module.free_of_flat_of_isLocalRing
    infer_instance
  · classical
    have := Fintype.ofFinite (subH Γ hF)
    let v : subH Γ hF → Γ(Γ.G.left, U) →+* FractionRing R := fun t => RegDenom.valHom (Γ.pt t.1).left U t.2
    have hv : Function.Injective v := by
      intro s t e
      have hst := RegDenom.eq_of_valHom_eq hU s.2 t.2 e
      obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := inferInstance
      exact Subtype.ext (Γ.pt_inj s.1 t.1 x x (by rw [hst]))
    have h1 : ∀ h : subH Γ hF, ∃ d : R, d ≠ 0 ∧ d • (Pi.single h 1 : subH Γ hF → R) ∈ Φ.range := by
      intro h
      obtain ⟨d, hd, b, hb⟩ := RegDenom.exists_denom_of_injective (algebraMap R Γ(Γ.G.left, U)) v hv
        (fun t r => val_algebraMap hρ t.1 t.2 r) (fun t => algebraMap R _ ((Pi.single h 1 : subH Γ hF → R) t))
      refine ⟨d, hd, b, funext fun t => inj ?_⟩
      refine (hΦ b t t.2).symm.trans ((hb t).trans ?_)
      rw [← map_mul]
      rfl
    choose d hd hdA using h1
    refine ⟨∏ h, d h, Finset.prod_ne_zero_iff.2 fun h _ => hd h, fun f => ?_⟩
    have e : (∏ h, d h) • f =
        ∑ h, (f h * ∏ h' ∈ Finset.univ.erase h, d h') • (d h • (Pi.single h 1 : subH Γ hF → R)) := by
      funext t
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      rw [Finset.sum_eq_single t]
      · rw [Pi.single_eq_same, ← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ t)]
        ring
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb.symm]
      · simp
    rw [e]
    exact Subalgebra.sum_mem _ fun h _ => Subalgebra.smul_mem _ (hdA h) _
  · rintro _ ⟨s, rfl⟩
    obtain ⟨c, hc⟩ := exists_tensor hρ hF s
    obtain ⟨g, hg, hg'⟩ := key c
    have : (fun z : subH Γ hF × subH Γ hF => (Φ s) (z.1 * z.2)) = g := by
      funext z
      apply inj
      rw [hg' z, ← hc z.1 z.2 z.1.2 z.2.2 (z.1 * z.2).2]
      exact (hΦ s (z.1 * z.2) (z.1 * z.2).2).symm
    change (fun z : subH Γ hF × subH Γ hF => (Φ s) (z.1 * z.2)) ∈ prodSpan Φ.range
    rw [this]
    exact hg
  · rintro _ ⟨s, rfl⟩
    obtain ⟨c, hc⟩ := exists_inv hρ hF s
    refine ⟨c, funext fun x => inj ?_⟩
    have e1 := hc x x.2 (x⁻¹).2
    have e2 := hΦ s x⁻¹ (x⁻¹).2
    have e3 := hΦ c x x.2
    exact e3.symm.trans (Eq.trans (valAlg_apply hρ _ _ _).symm (e1.symm.trans e2))
  · rintro _ ⟨s, rfl⟩
    exact ⟨s, fun t h => hΦ s t h⟩
  · intro s g hg
    obtain ⟨c, hc⟩ := exists_tensor_of_prod hρ s
    obtain ⟨g', hg1, hg2⟩ := key c
    have : g = g' := funext fun z => inj (by rw [hg2 z, ← hc z.1 z.2 z.1.2 z.2.2, hg z])
    rw [this]
    exact hg1

theorem bichar_mem_prodSpan [ValuationRing R] (hH : HenselianLocalRing R)
    (hdim : ∀ P : PrimeSpectrum R, P.asIdeal = ⊥ ∨ P = IsLocalRing.closedPoint R) [Finite T] (Γ : QFGroup R T)
    (β : T →* T →* Rˣ) (s : Γ((Γ.G ⊗ Γ.G).left, ⊤))
    (hs : ∀ a b, valAt (lift (Γ.pt a) (Γ.pt b)).left ⊤ le_top s = algebraMap R _ ((β a b : Rˣ) : R)) :
    (fun z : T × T => ((β z.1 z.2 : Rˣ) : R)) ∈ prodSpan (Γ.btOrder ⊤) := by
  have := Γ.quasiFinite
  have := Γ.separated
  have := Γ.quasiCompact
  have := Γ.finPres
  let U := GlobalTheory.finitePart Γ.G.hom
  have hU : ∀ x : Γ.G.left, Γ.G.hom x = IsLocalRing.closedPoint R → x ∈ U :=
    GlobalTheory.mem_finitePart_of_eq_closedPoint (R := CommRingCat.of R) Γ.G.hom
  have hF := isFinOpenSub Γ U (GlobalTheory.isFinite_finitePart (R := CommRingCat.of R) Γ.G.hom) hU
  obtain ⟨A, hA, hsec, hprod⟩ := exists_order Γ U hF
  have h1 := pair_ind R T (subH Γ hF) A β hA (hprod s _ fun z => hs z.1 z.2)
  have hle : indOrder (subH Γ hF).subtype A ≤ Γ.btOrder ⊤ := by
    intro f hf
    refine Algebra.subset_adjoin fun t g _ => ?_
    rcases hdim (Γ.G.hom g) with hg | hg
    · exact regularAt_generic Γ _ g hg
    · obtain ⟨σ, hσ⟩ := hsec _ (hf t)
      exact ⟨U, hU g hg, σ, fun h hh => hσ ⟨h, hh⟩ hh⟩
  refine Submodule.span_mono ?_ h1
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact ⟨a, hle ha, b, hle hb, rfl⟩

end PositivityTheory.HtPt.Twpair
