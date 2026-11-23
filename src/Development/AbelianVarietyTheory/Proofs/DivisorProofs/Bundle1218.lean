module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1188
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle024
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle036
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle975
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsLocalRingDual
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanExp

open IsLocalRing GlobalTheory.FormalValue

theorem isLocalRing_dualNumber (V : Type) [CommRing V] [IsLocalRing V] : IsLocalRing (DualNumber V) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact isUnit_or_isUnit_one_sub_self _

theorem thick_closedPoint (V : Type) [CommRing V] [IsLocalRing V] [IsLocalRing (V ⧸ maximalIdeal V ^ (0 + 1))] :
    thick V (maximalIdeal V) 0 (closedPoint (V ⧸ maximalIdeal V ^ (0 + 1))) = closedPoint V := by
  show PrimeSpectrum.comap (Ideal.Quotient.mk (maximalIdeal V ^ (0 + 1))) (closedPoint _) = closedPoint V
  refine PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal ?_)
  haveI : (closedPoint (V ⧸ maximalIdeal V ^ (0 + 1))).asIdeal.IsMaximal := IsLocalRing.maximalIdeal.isMaximal _
  exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective

theorem pow_map_le_ker (V : Type) [CommRing V] (m : Ideal V) (e : ℕ) :
    (m.map (algebraMap V (DualNumber V))) ^ (e + 1) ≤
      RingHom.ker ((Ideal.Quotient.mk (m ^ (e + 1))).comp (TrivSqZeroExt.fstHom V V V).toRingHom) := by
  rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
  intro a ha
  simp only [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    TrivSqZeroExt.fstHom_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl,
    Ideal.Quotient.eq_zero_iff_mem]
  exact ha

theorem ker_dualMap_le (V : Type) [CommRing V] (m : Ideal V) (e : ℕ) :
    RingHom.ker (dualMap (Ideal.Quotient.mk (m ^ (e + 1)))) ≤ (m.map (algebraMap V (DualNumber V))) ^ (e + 1) := by
  intro z hz
  rw [RingHom.mem_ker] at hz
  have h₁ : Ideal.Quotient.mk (m ^ (e + 1)) z.fst = 0 := by
    have := congrArg TrivSqZeroExt.fst hz
    simpa [dualMap] using this
  have h₂ : Ideal.Quotient.mk (m ^ (e + 1)) z.snd = 0 := by
    have := congrArg TrivSqZeroExt.snd hz
    simpa [dualMap] using this
  rw [Ideal.Quotient.eq_zero_iff_mem] at h₁ h₂
  rw [← Ideal.map_pow]
  have hz' : z = algebraMap V (DualNumber V) z.fst + algebraMap V (DualNumber V) z.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [hz']
  exact Ideal.add_mem _ (Ideal.mem_map_of_mem _ h₁) (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ h₂))

theorem dualMap_surjective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Surjective f) :
    Function.Surjective (dualMap f) := by
  intro w
  obtain ⟨a, ha⟩ := hf w.fst
  obtain ⟨b, hb⟩ := hf w.snd
  refine ⟨(TrivSqZeroExt.inl a + TrivSqZeroExt.inr b : DualNumber A), ?_⟩
  ext <;> simp [dualMap, ha, hb]

theorem value_mul_sumI : AllV fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (y : epsR V ⟶ G) (gm₀ : GtPt D.toPre (epsR V)), IsTangent y → TanRel U.toUnifPre y gm₀ → ∀ (k : ℕ) (jG : U.LG.L.ι) (J : (Sp (DualNumber V) ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), ⊤ ≤ y.left ⁻¹ᵁ U.LG.L.U jG → (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.toPre.P.L.U (J ψ)) → ∃ W : (DualNumber V)ˣ, (W : DualNumber V).fst * GlobalTheory.MBLow.TanExp.rigVal U.LG jG = GlobalTheory.MBLow.TanExp.rigValD D.toPre (J gm₀.b.left) ∧ ∀ (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ e, U.toUnifPre.ExpandsAt e k σ f) → GlobalTheory.UT.SumI (IsLocalRing.maximalIdeal V) (fun α => GlobalTheory.MBLow.TanExp.termV J gm₀ (f α)) ((W : DualNumber V) ^ k * valR y.left (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => jG) (σ.f fun _ => jG)) := by
  intro V _ _ _ _ hV D A G _ _ _ U y gm₀ hy hT k jG J hjG hJ
  haveI : IsLocalRing (DualNumber V) := isLocalRing_dualNumber V
  haveI : Module.Finite V (DualNumber V) := inferInstanceAs (Module.Finite V (V × V))
  haveI : IsAdicComplete (maximalIdeal V) V := hV
  haveI hJd : IsAdicComplete ((maximalIdeal V).map (algebraMap V (DualNumber V))) (DualNumber V) :=
    InertNorm.isAdicComplete_map_of_finite (maximalIdeal V) (DualNumber V)
  have hx : IsFormalPt U.toUnifPre ((maximalIdeal V).map (algebraMap V (DualNumber V))) gm₀ y.left :=
    isFormalPt_of_surjective _ fun e => by
      obtain ⟨ye, h₁, h₂, h₃⟩ := hT e
      exact ⟨DualNumber (V ⧸ maximalIdeal V ^ (e + 1)), inferInstance, dualMap (Ideal.Quotient.mk _), ye,
        dualMap_surjective _ Ideal.Quotient.mk_surjective, ker_dualMap_le V _ e, h₁, h₂, h₃⟩
  have hL : ⊤ ≤ y.left ⁻¹ᵁ U.LG.L.U jG := hjG
  have hM : ⊤ ≤ basePt gm₀ ⁻¹ᵁ D.toPre.P.L.U (J gm₀.b.left) := hJ _
  refine ⟨(tau U.toUnifPre ((maximalIdeal V).map (algebraMap V (DualNumber V))) y.left jG (J gm₀.b.left))⁻¹,
    ?_, fun σ f hE => ?_⟩
  · obtain ⟨g₀, hg₀⟩ := exists_isZero D.toPre (Over.mk (spMap (RingHom.id V)))
    haveI : IsAdicComplete ((maximalIdeal V).map (RingHom.id V)) V := by rw [Ideal.map_id]; exact hV
    have h₀ := isFormalPt_zero U.toUnifPre (RingHom.id V) hg₀
    have hid : spMap (RingHom.id V) = 𝟙 (Sp V) := by
      show Spec.map (CommRingCat.ofHom (RingHom.id V)) = _
      rw [CommRingCat.ofHom_id, Spec.map_id]
    have hb₀ : basePt g₀ = spMap (RingHom.id V) ≫ eSec D.toPre.P.A := by
      refine (congrArg Over.Hom.left hg₀.1).trans ?_
      exact congrArg (· ≫ eSec D.toPre.P.A)
        ((Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk (spMap (RingHom.id V))))))
    have hyE : spMap (TrivSqZeroExt.fstHom V V V).toRingHom ≫ y.left = eSec G := hy
    have hL₀ : ⊤ ≤ (spMap (RingHom.id V) ≫ eSec G) ⁻¹ᵁ U.LG.L.U jG := by
      rw [← hyE, ← Category.assoc]; exact top_le_comp hL _
    have hxe : ∀ e, eSec (thickObj V (maximalIdeal V) e G) ≫ (fstG (maximalIdeal V) e G).left =
        spMap ((Ideal.Quotient.mk (maximalIdeal V ^ (e + 1))).comp (TrivSqZeroExt.fstHom V V V).toRingHom) ≫
          y.left := fun e => by
      rw [ExpansionValueZero.eSec_fstG, ← hyE]
      show _ = Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk (maximalIdeal V ^ (e + 1))).comp
        (TrivSqZeroExt.fstHom V V V).toRingHom)) ≫ _
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have hM₀ : ⊤ ≤ basePt g₀ ⁻¹ᵁ D.toPre.P.L.U (J gm₀.b.left) := by
      haveI : IsLocalRing (V ⧸ maximalIdeal V ^ (0 + 1)) :=
        isLocalRing_quotient_pow (IsLocalRing.maximalIdeal.isMaximal V).ne_top 0
      have HC := hx.hasCoords (e := 0) _ (pow_map_le_ker V _ 0) (hxe 0)
      have h₂ : thick V (maximalIdeal V) 0 ≫ eSec D.toPre.P.A = spMap _ ≫ gm₀.b.left :=
        (ExpansionValueZero.eSec_pG _ (U.gt 0)).symm.trans HC.2.1
      have h₃ : ⊤ ≤ (thick V (maximalIdeal V) 0 ≫ eSec D.toPre.P.A) ⁻¹ᵁ D.toPre.P.L.U (J gm₀.b.left) := by
        rw [h₂]; exact top_le_comp hM _
      have h₄ : eSec D.toPre.P.A (thick V (maximalIdeal V) 0 (closedPoint (V ⧸ maximalIdeal V ^ (0 + 1)))) ∈
          D.toPre.P.L.U (J gm₀.b.left) := h₃ (Set.mem_univ _)
      rw [thick_closedPoint] at h₄
      rw [hb₀]
      exact top_le_comp (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of V) _ h₄).ge _
    have hfst : (tau U.toUnifPre ((maximalIdeal V).map (algebraMap V (DualNumber V))) y.left jG
        (J gm₀.b.left) : DualNumber V).fst =
        (tau U.toUnifPre ((maximalIdeal V).map (RingHom.id V)) (spMap (RingHom.id V) ≫ eSec G) jG
          (J gm₀.b.left) : V) := by
      refine eq_of_forall_mk_eq (maximalIdeal V) fun e => ?_
      have a₁ := map_tau_mul_wVal hx hL hM _ (pow_map_le_ker V _ e) (hxe e)
      have a₂ := map_tau_mul_wVal h₀ hL₀ hM₀ (Ideal.Quotient.mk (maximalIdeal V ^ (e + 1)))
        (by rw [Ideal.map_id, Ideal.mk_ker]) (xe := eSec (thickObj V (maximalIdeal V) e G))
        (by rw [hid, Category.id_comp]; exact ExpansionValueZero.eSec_fstG _ e G)
      exact (IsUnit.of_mul_eq_one_right _ a₂).mul_right_cancel (a₁.trans a₂.symm)
    have r₀ := tau_rig h₀ hb₀ hL₀ hM₀
    have hv : ∀ (U' : (Sp V).Opens) (f : Γ(Sp V, U')),
        valR (spMap (RingHom.id V)) U' f = valR (𝟙 (Sp V)) U' f := fun _ _ => by rw [hid]
    rw [hv, hv] at r₀
    have hW : (((tau U.toUnifPre ((maximalIdeal V).map (algebraMap V (DualNumber V))) y.left jG
        (J gm₀.b.left))⁻¹ : (DualNumber V)ˣ) : DualNumber V).fst *
        (tau U.toUnifPre ((maximalIdeal V).map (algebraMap V (DualNumber V))) y.left jG
          (J gm₀.b.left) : DualNumber V).fst = 1 := by
      rw [← TrivSqZeroExt.fst_mul, Units.inv_mul, TrivSqZeroExt.fst_one]
    unfold rigVal rigValD
    rw [← r₀, ← _root_.mul_assoc, ← hfst, hW, _root_.one_mul]
    rfl
  · refine ⟨⊤, Module.Finite.fg_top, Submodule.mem_top, fun _ => Submodule.mem_top, fun n => ?_⟩
    haveI : IsLocalRing (DualNumber V ⧸ ((maximalIdeal V).map (algebraMap V (DualNumber V))) ^ (n + 1)) :=
      isLocalRing_quotient_pow (ne_top_of_isHausdorff _) n
    obtain ⟨F, hF⟩ := map_secVal_eq U.toUnifPre (hE n)
    obtain ⟨-, h₁⟩ := hF (DualNumber V) ((maximalIdeal V).map (algebraMap V (DualNumber V))) _ gm₀ y.left hx _
      (Ideal.Quotient.mk (((maximalIdeal V).map (algebraMap V (DualNumber V))) ^ (n + 1))) (by rw [Ideal.mk_ker])
    refine ⟨F, fun T hT => ?_⟩
    have hc : ∀ α ∈ T, CohCharts gm₀ α (J gm₀.b.left) (fun i => J (gm₀.b.left ≫ D.toPre.famφB α i))
        (fun i => J (D.toPre.gtφT (epsR V) gm₀.b α i)) := fun α _ => by
      refine ⟨fun p _ => Set.mem_iInter.2 fun i => hJ (gm₀.b.left ≫ D.toPre.famφB α i) (Set.mem_univ p),
        fun p _ => Set.mem_iInter.2 fun i => hJ (D.toPre.gtφT (epsR V) gm₀.b α i) (Set.mem_univ p), ?_⟩
      have c : ∀ a, Sum.elim (fun _ : PUnit.{1} => J gm₀.b.left) (Sum.elim (fun i => J (gm₀.b.left ≫ D.toPre.famφB α i))
          (fun i => J (D.toPre.gtφT (epsR V) gm₀.b α i))) a = J (Sum.elim (fun _ : PUnit.{1} => basePt gm₀)
            (Sum.elim (fun a => basePt gm₀ ≫ D.toPre.famφB α a) (coordφ gm₀ α)) a) := by
        rintro (a | a | a) <;> rfl
      exact fun a b hab => (c a).trans ((congrArg J hab).trans (c b).symm)
    have e := h₁ T jG (J gm₀.b.left) (fun α i => J (gm₀.b.left ≫ D.toPre.famφB α i))
      (fun α i => J (D.toPre.gtφT (epsR V) gm₀.b α i)) hT hL hM hc
    rw [Ideal.Quotient.eq] at e
    have key := Ideal.mul_mem_left _
      (((tau U.toUnifPre ((maximalIdeal V).map (algebraMap V (DualNumber V))) y.left jG (J gm₀.b.left))⁻¹ :
        (DualNumber V)ˣ) ^ k : DualNumber V) e
    rw [mul_sub, ← _root_.mul_assoc, ← mul_pow, Units.inv_mul, one_pow, _root_.one_mul] at key
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow]
    exact Ideal.pow_le_pow_right (Nat.le_succ n) key

end GlobalTheory.MBLow.TanExp

end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mix

theorem nonzeroLocus_prodSec {X : Scheme.{0}} {A B : LB X} (s : A.Sec) (t : B.Sec) :
    nonzeroLocus (EffBound.tensSec s t) = nonzeroLocus s ⊓ nonzeroLocus t := by
  have e (c : A.ι × B.ι) : X.basicOpen ((EffBound.tensSec s t).f c) =
      (A.U c.1 ⊓ B.U c.2) ⊓ X.basicOpen (s.f c.1) ⊓ ((A.U c.1 ⊓ B.U c.2) ⊓ X.basicOpen (t.f c.2)) :=
    (X.basicOpen_mul _ _).trans (congrArg₂ (· ⊓ ·) (X.basicOpen_res _ _) (X.basicOpen_res _ _))
  refine le_antisymm (iSup_le fun c => (e c).le.trans (inf_le_inf
    (inf_le_right.trans (le_iSup (fun i => X.basicOpen (s.f i)) c.1))
    (inf_le_right.trans (le_iSup (fun i => X.basicOpen (t.f i)) c.2)))) fun x hx => ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx.1
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 hx.2
  have h : x ∈ A.U i ⊓ B.U j := ⟨X.basicOpen_le _ hi, X.basicOpen_le _ hj⟩
  exact Opens.mem_iSup.2 ⟨(i, j), (e (i, j)).ge ⟨⟨h, hi⟩, h, hj⟩⟩

theorem secVal_prodSec {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (σ : k →+* ℂ) {A B : LB X}
    (s : A.Sec) (t : B.Sec) :
    secVal p σ (EffBound.tensSec s t) = secTens (secVal p σ s) (secVal p σ t) := by
  funext c y
  by_cases h : y ∈ ptsIn p σ (A.U c.1 ⊓ B.U c.2)
  · exact (ev_mul _ _ y).trans (congrArg₂ (· * ·) (ev_res inf_le_left h _) (ev_res inf_le_right h _))
  · exact (ev_of_notMem h _).trans ((secTens_mem (secVal_mem s) (secVal_mem t)).2 c y h).symm

theorem mult_prodSec {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {A B : LB X} (hA : A.IsLB)
    (hB : B.IsLB) (hAB : (tens A B).IsLB) (s : A.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : B.Sec)
    (ht : genericPoint X ∈ nonzeroLocus t) (h : genericPoint X ∈ nonzeroLocus (EffBound.tensSec s t)) (z : X) :
    (divOfSec hAB _ h).mult z = (divOfSec hA s hs).mult z + (divOfSec hB t ht).mult z := by
  obtain ⟨i, hi⟩ := Geo.Tor.exists_chart hA z
  obtain ⟨j, hj⟩ := Geo.Tor.exists_chart hB z
  have hij : z ∈ (tens A B).U (i, j) := ⟨hi, hj⟩
  rw [((presents_divOfRatSec hAB _).isEqn (i, j) z hij).mult_eq,
    ((presents_divOfRatSec hA _).isEqn i z hi).mult_eq, ((presents_divOfRatSec hB _).isEqn j z hj).mult_eq,
    val_ratOfSec (gen_mem hij), val_ratOfSec (gen_mem hi), val_ratOfSec (gen_mem hj),
    ← Scheme.ord_mul (fnOf_sec_ne_zero hs (gen_mem hi)) (fnOf_sec_ne_zero ht (gen_mem hj))]
  exact congrArg (Scheme.ord · z) ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (fnOf_resG inf_le_left _ _) (fnOf_resG inf_le_right _ _)))

theorem exists_sec_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (σ : k →+* ℂ) (M A : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (a : A.B.Sec) (ha : genericPoint X ∈ nonzeroLocus a), ∃ (s₁ : (M.tens A).B.Sec) (h₁ : genericPoint X ∈ nonzeroLocus s₁), nonzeroLocus s₁ = nonzeroLocus s ⊓ nonzeroLocus a ∧ (∀ z, (divOfSec (M.tens A).φ.isLB s₁ h₁).mult z = (divOfSec M.φ.isLB s hs).mult z + (divOfSec A.φ.isLB a ha).mult z) ∧ ∀ y ∈ ptsIn p σ (nonzeroLocus s₁), (M.tens A).logSec s₁ y = M.logSec s y + A.logSec a y := by
  intro k _ X _ _ p σ M A s hs a ha
  have e := nonzeroLocus_prodSec s a
  refine ⟨EffBound.tensSec s a, e.ge ⟨hs, ha⟩, e, mult_prodSec _ _ _ s hs a ha _, fun y hy => ?_⟩
  have hy' : y ∈ ptsIn p σ (nonzeroLocus s ⊓ nonzeroLocus a) := ptsIn_mono e.le hy
  have h0 (N : MLine p σ) (u : N.B.Sec) (hu : y ∈ ptsIn p σ (nonzeroLocus u)) : N.φ.nsq (secVal p σ u) y ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.2 ((secVal_ne_zero_iff u (mem_pick _ y)).2 hu)))
      (Real.exp_ne_zero _)
  have h : (M.φ.tens A.φ).nsq (secVal p σ (EffBound.tensSec s a)) y =
      M.φ.nsq (secVal p σ s) y * A.φ.nsq (secVal p σ a) y := by
    rw [secVal_prodSec]
    exact Weight.nsq_tens _ _ (secVal_mem s) (secVal_mem a) y
  refine (congrArg (Real.log · / 2) h).trans ?_
  rw [Real.log_mul (h0 M s (mem_ptsIn_inf.1 hy').1) (h0 A a (mem_ptsIn_inf.1 hy').2), add_div]
  rfl

end GlobalTheory.Mix
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TrAdapt

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) :=
  RingHom.ext fun z => TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

variable {R : Type} [CommRing R] [IsDomain R] {F F' : Type} [Field F] [Field F'] [Algebra (FractionRing R) F]
  [Algebra (FractionRing R) F'] (e : F ≃+* F')
  (he : ∀ x, e (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) F' x)

include he in
theorem toF_comp : (e : F →+* F').comp (toF R F) = toF R F' :=
  RingHom.ext fun r => by simp [toF, he]


include he in
def rhoE : TE R F' ⟶ TE R F :=
  Over.homMk (spMap (dualMap (e : F →+* F'))) (by
    show spMap (dualMap (e : F →+* F')) ≫ spMap (algebraMap F (DualNumber F)) ≫
        spMap (algebraMap (FractionRing R) F) ≫ spMap (algebraMap R (FractionRing R)) =
      spMap (algebraMap F' (DualNumber F')) ≫ spMap (algebraMap (FractionRing R) F') ≫
        spMap (algebraMap R (FractionRing R))
    simp only [← spMap_comp']
    apply congrArg spMap
    ext r <;> simp [dualMap, he, TrivSqZeroExt.algebraMap_eq_inl])


include he in
def sigE : TF (R := R) F' ⟶ TF (R := R) F :=
  Over.homMk (spMap (e : F →+* F')) (by
    show spMap (e : F →+* F') ≫ spMap (algebraMap (FractionRing R) F) ≫ spMap (algebraMap R (FractionRing R)) =
      spMap (algebraMap (FractionRing R) F') ≫ spMap (algebraMap R (FractionRing R))
    simp only [← spMap_comp']
    congr 1
    exact RingHom.ext fun r => by simp [he])

theorem rhoE_left : (rhoE e he).left = spMap (dualMap (e : F →+* F')) := rfl

theorem sigE_left : (sigE e he).left = spMap (e : F →+* F') := rfl

theorem red_comm : (sigE e he).left ≫ redE F = redE F' ≫ (rhoE e he).left := by
  rw [sigE_left, rhoE_left]
  show spMap _ ≫ spMap _ = spMap _ ≫ spMap _
  rw [← spMap_comp', ← spMap_comp']
  congr 1
  exact RingHom.ext fun z => by simp [dualMap]

include he in
theorem bKey_map (κ : Rule) (hκ : Funct κ) [CharZero F] [CharZero F'] (D : DegPre R) {N : NumD F} (ν : NumOf D F N)
    {N' : NumD F'} (ν' : NumOf D F' N') (I : NumD.Hom (e : F →+* F') N N') (hh : ∀ x, I.h x = 1) (hl : I.lam = 1)
    (hth : ν'.th = ν.th) (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (k : F) (hk : BKey κ ν vB k) :
    BKey κ ν' vB (e k) := by
  refine ⟨fun h0 => ?_, fun hg hr th hth' hv x' hres hpb => ?_⟩
  · have h1 := I.th_eq 1
    rw [map_one, hh, hl] at h1
    rw [h1, Units.val_mul, Units.val_one, _root_.one_mul, _root_.one_mul, ← map_pow, RingEquiv.coe_toRingHom, ← map_mul, hk.1 h0,
      map_one]
  · obtain ⟨x, hx⟩ := GlobalTheory.KeyPow.exists_keyPB x' (e.symm : F' →+* F)
    have hc : (e.symm : F' →+* F).comp ((algebraMap (FractionRing R) F').comp (algebraMap R (FractionRing R))) =
        (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)) :=
      RingHom.ext fun r => by simp [← he]
    have hpb' := GlobalTheory.keyPB_trans _ _ _ _ x' x _ _ hpb hx
    rw [hc] at hpb'
    have hkx := hk.2 hg hr th hth' hv x (by rw [← hth]; exact hres) hpb'
    have hf := hκ F' F (e.symm : F' →+* F) x' x hx
    rw [hkx] at hf
    rw [hf]
    simp

include he in
theorem adapted_map [CharZero F] [CharZero F'] (D : DegPre R) {N : NumD F} (ν : NumOf D F N)
    {N' : NumD F'} (ν' : NumOf D F' N') (I : NumD.Hom (e : F →+* F') N N') (heX : ∀ χ, ν'.eX (I.e χ) = ν.eX χ)
    (hpull : ∀ (gm : GtPt D (TE R F)) (gm' : GtPt D (TE R F')), GtPt.IsPull (spMap (dualMap (e : F →+* F'))) gm gm' →
      ∀ χ, vE (gm'.s χ) (𝟙 _) ν'.J = dualMap (e : F →+* F') (vE (gm.s χ) (𝟙 _) ν.J))
    (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (r g : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin g ≃ Fin D.P.g ⊕ Fin r)
    (gm : Fin g → GtPt D (TE R F)) (had : Adapted ν vB bX σ gm) :
    ∃ gm' : Fin g → GtPt D (TE R F'), (∀ j, GtPt.IsPull (spMap (dualMap (e : F →+* F'))) (gm j) (gm' j)) ∧
      Adapted ν' vB (bX.map I.e.toIntLinearEquiv) σ gm' := by
  obtain ⟨hv, hz, hb, ht⟩ := had
  choose gm' hgm' using fun j => GlobalTheory.ConstLie.exists_isPullGt (rhoE e he) (gm j)
  have hzT : rhoE e he ≫ DegPre.zeroT D (TE R F) = DegPre.zeroT D (TE R F') := by
    simp only [DegPre.zeroT, ← Category.assoc, comp_toUnit]
  have hzF : sigE e he ≫ DegPre.zeroF D F = DegPre.zeroF D F' := by
    simp only [DegPre.zeroF, ← Category.assoc, comp_toUnit]
  refine ⟨gm', hgm', hv, fun j => ?_, fun i => ?_, fun l => ⟨?_, fun χ => ?_⟩⟩
  · obtain ⟨o, ho, hpo⟩ := hz j
    obtain ⟨o', ho'⟩ := GlobalTheory.ConstLie.exists_isPullGt (sigE e he)
      (⟨o.b, o.s, o.isGen, o.s_zero, o.mult⟩ : GtPt D (TF (R := R) F))
    refine ⟨⟨o'.b, o'.s, o'.isGen, o'.s_zero, o'.mult⟩, ⟨?_, fun χ => ?_⟩, ?_, fun χ => ?_⟩
    · exact Over.OverMorphism.ext (ho'.1.trans ((congrArg (fun q => (sigE e he).left ≫ q.left) ho.1).trans
        (congrArg Over.Hom.left hzF)))
    · refine corr_of_val D.P.isLB fun y J hJ => ?_
      exact ((val_corr hJ (ho'.2 χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (ho.2 χ) _).trans
        (val_one _)))).trans (val_one _).symm
    · refine ho'.1.trans ((congrArg ((sigE e he).left ≫ ·) hpo.1).trans ?_)
      rw [← Category.assoc, red_comm, Category.assoc, ← (hgm' j).1]
    · refine corr_of_val D.P.isLB fun y J hJ => ?_
      refine ((val_corr hJ (ho'.2 χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (hpo.2 χ) _).trans
        (val_pull hJ _ _ _)))).trans (Eq.trans ?_ ((val_pull hJ _ _ _).trans ((val_corr hJ ((hgm' j).2 χ) _).trans
        (val_pull hJ _ _ _))).symm)
      rw [Category.id_comp, Category.id_comp, red_comm]
  · refine (hgm' _).1.trans ?_
    rw [hb i, ← Category.assoc, rhoE_left, ← spMap_comp', dualMap_comp, toF_comp e he]
  · exact Over.OverMorphism.ext ((hgm' _).1.trans ((congrArg (fun q => (rhoE e he).left ≫ q.left) (ht l).1).trans
      (congrArg Over.Hom.left hzT)))
  · obtain ⟨χ₀, rfl⟩ := I.e.surjective χ
    rw [heX, hpull _ _ (hgm' _), (ht l).2 χ₀, Module.Basis.map_repr]
    simp [dualMap]

end GlobalTheory.MBLow.TrAdapt

theorem GlobalTheory.MBLow.bKey_adapted_map : ∀ κ : Rule, Funct κ → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F F' : Type) [Field F] [Field F'] [CharZero F] [CharZero F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (e : F ≃+* F'), (∀ x, e (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) F' x) → ∀ (N : NumD F) (ν : NumOf D F N) (N' : NumD F') (ν' : NumOf D F' N') (I : NumD.Hom (e : F →+* F') N N'), (∀ x, I.h x = 1) → I.lam = 1 → (∀ χ, ν'.eX (I.e χ) = ν.eX χ) → ν'.th = ν.th → (∀ (gm : GtPt D (TE R F)) (gm' : GtPt D (TE R F')), GtPt.IsPull (spMap (dualMap (e : F →+* F'))) gm gm' → ∀ χ, vE (gm'.s χ) (𝟙 _) ν'.J = dualMap (e : F →+* F') (vE (gm.s χ) (𝟙 _) ν.J)) → ∀ (vB : Fin D.P.g → (epsR R ⟶ D.P.A)), (∀ k, BKey κ ν vB k → BKey κ ν' vB (e k)) ∧ ∀ (r g : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin g ≃ Fin D.P.g ⊕ Fin r) (gm : Fin g → GtPt D (TE R F)), Adapted ν vB bX σ gm → ∃ gm' : Fin g → GtPt D (TE R F'), (∀ j, GtPt.IsPull (spMap (dualMap (e : F →+* F'))) (gm j) (gm' j)) ∧ Adapted ν' vB (bX.map I.e.toIntLinearEquiv) σ gm' := by
  intro κ hκ R _ _ D F F' _ _ _ _ _ _ e he N ν N' ν' I hh hl heX hth hpull vB
  exact ⟨fun k hk => GlobalTheory.MBLow.TrAdapt.bKey_map e he κ hκ D ν ν' I hh hl hth vB k hk,
    fun r g bX σ gm had => GlobalTheory.MBLow.TrAdapt.adapted_map e he D ν ν' I heX hpull vB r g bX σ gm had⟩
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TorVec

theorem exists_torus_tangent : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (l : D.X →+ R), ∃ gm : GtPt D (epsR R), GtTan gm ∧ gm.b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (gm.s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (l χ))) := by
  intro R _ _ D l
  obtain ⟨ν, hb, hv⟩ := GlobalTheory.TorusTangent.exists_pt (D := D) (T := epsR R)
    (fun x => GlobalTheory.TorusTangent.oneAdd (l x)) fun x y => by rw [map_add (f := _), GlobalTheory.TorusTangent.oneAdd_add]
  refine ⟨ν, ?_, hb, fun χ Z q z J hJ => ?_⟩
  · obtain ⟨g₀, h₀, v₀⟩ := GlobalTheory.TorusTangent.exists_pt (D := D) (T := baseOver (Sp R)) (fun _ => 1)
      fun _ _ => (_root_.mul_one _).symm
    refine ⟨g₀, ⟨h₀, fun x => corr_of_val D.P.isLB fun y J hJ => ?_⟩, ?_, fun x => corr_of_val D.P.isLB fun y J hJ => ?_⟩
    · rw [v₀ x _ _ y J hJ, map_one, val_one]
    · rw [h₀, hb, GlobalTheory.TorusTangent.zeroT_left, GlobalTheory.TorusTangent.zeroT_left, ← Category.assoc]
      exact congrArg (· ≫ eSec D.P.A) GlobalTheory.TorusTangent.fst_inl.symm
    · refine (v₀ x _ _ y J hJ).trans (Units.ext (Eq.trans ?_
        (GlobalTheory.TorusTangent.hasVal_spMap (hv x) (TrivSqZeroExt.fstHom R R R).toRingHom hJ).symm))
      rw [GlobalTheory.TorusTangent.valR_oneAdd, map_one]
      simp
  · rw [hv χ Z q z J hJ, ← gs_unit q z ⊤ trivial]
    rfl

end GlobalTheory.MBLow.TorVec

end
end

section

open Filter Topology GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem isBallFam_mono_neg_add :
    ∀ (G : Type) [AddCommGroup G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B →
      (∀ r r', r ≤ r' → B r ⊆ B r') ∧ (∀ r x, x ∈ B r → -x ∈ B r) ∧
        (∀ r r' x y, x ∈ B r → y ∈ B r' → x + y ∈ B (r + r')) := by
  intro G _ Λ B hB
  have hneg : ∀ r x, x ∈ B r → -x ∈ B r := by
    intro r x hx
    have h := hB.sub_mem 0 r 0 x (hB.zero_mem 0 le_rfl) hx
    simpa using h
  refine ⟨?_, hneg, ?_⟩
  · intro r r' hrr' x hx
    have h := hB.sub_mem r (r' - r) x 0 hx (hB.zero_mem _ (sub_nonneg.mpr hrr'))
    simpa using h
  · intro r r' x y hx hy
    have h := hB.sub_mem r r' x (-y) hx (hneg r' y hy)
    simpa using h

end GlobalTheory.VolBr
end
