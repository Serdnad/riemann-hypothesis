module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle109
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle115
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle077
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle079
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFourierJacobiExpansionOverField
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle086
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle114
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle083
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle053
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle100
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle096
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSmoothAtOfSmoothQuotientPow
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProportionalRaw
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle106
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAutomorphismInducingFrobeniusAllDegrees
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isAbelianScheme_of_thickenings : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) [∀ e, GrpObj (Y e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsGrpPullback (Y e) (Y (e + 1)) (thickTrans V _ e) (β e)) → ∀ (B : Over (Spec (CommRingCat.of V))) (b : ∀ e, (Y e).left ⟶ B.left), (∀ e, IsAbelianScheme (Y e)) → (∀ e, IsCommMonObj (Y e)) → IsProjBy B.hom → (∀ e, IsPullback (b e) (Y e).hom B.hom (thick V (IsLocalRing.maximalIdeal V) e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∃ _ : GrpObj B, IsCommMonObj B ∧ IsAbelianScheme B ∧ ∀ e, IsGrpPullback (Y e) B (thick V _ e) (b e) := by
  intro V _ _ _ _ Y _ β hβ B b hA hc hP hb hβb
  have hprop : IsProper B.hom := GlobalTheory.AbLaw.isProper_of_isProjBy V B.left B.hom hP
  have hsm : Smooth B.hom := by
    refine GlobalTheory.SmoothLimit.main V B fun e ↦ ?_
    have h : Smooth (Y e).hom := (hA e).smooth
    have he : (thickObj V (IsLocalRing.maximalIdeal V) e B).hom =
        (hb e).isoPullback.inv ≫ (Y e).hom := ((hb e).isoPullback_inv_snd).symm
    have h' : Smooth ((hb e).isoPullback.inv ≫ (Y e).hom) := inferInstance
    exact he ▸ h'
  have hconn : GeometricallyConnected B.hom :=
    GlobalTheory.ConnFibre.geometricallyConnected_of_closedFibre V B hsm hP (Y 0) (b 0) (hb 0)
      (hA 0).geomConnected
  obtain ⟨mu, io, un, H⟩ := GlobalTheory.T.exists_algebraization_group_operations_cdvr V Y β hβ B b hP inferInstance hb hβb
  obtain ⟨G, hG, hcomm⟩ := GlobalTheory.grpObj_of_thickenings V Y β hβ B b hb hβb mu io un H
  exact ⟨G, hcomm hc, ⟨hcomm hc, hsm, hprop, hconn⟩, hG⟩

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EndAlg

variable {X X' : Scheme.{0}} {κ : Type}

theorem eval₂_scale {σ R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) (c : A) (x : σ → A)
    {P : MvPolynomial σ R} {e : ℕ} (hP : P.IsHomogeneous e) :
    MvPolynomial.eval₂ φ (fun j => x j * c) P = MvPolynomial.eval₂ φ x P * c ^ e := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' := hP (MvPolynomial.mem_support_iff.mp hd)
  simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, _root_.mul_one, Finsupp.sum] at hd'
  rw [← hd']
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, _root_.mul_assoc]

theorem gs_eval {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) (φ : X' ⟶ X) (z : X') (U : X.Opens)
    (h : φ z ∈ U) (x : κ → Γ(X, U)) (P : MvPolynomial κ R) :
    gs φ z U (MvPolynomial.eval₂Hom (cst f U) x P) =
      MvPolynomial.eval₂ ((X'.presheaf.germ ⊤ z trivial).hom.comp (cst (φ ≫ f) ⊤)) (fun j => gs φ z U (x j)) P := by
  rw [gs_eq φ z U h, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left]
  congr 1
  · ext r
    simp only [RingHom.comp_apply]
    rw [← gs_eq φ z U h]
    simp only [GlobalTheory.AbLaw.cst, rs, RingHom.comp_apply]
    rw [gs_res φ z le_top h, gs_eq φ z ⊤ trivial]
    have hid : X'.presheaf.map (homOfLE (le_top : (⊤ : X'.Opens) ≤ ⊤)).op = 𝟙 _ := by
      rw [show (homOfLE (le_top : (⊤ : X'.Opens) ≤ ⊤)) = 𝟙 _ from Subsingleton.elim _ _]
      exact X'.presheaf.map_id _
    rw [hid]
    simp only [CommRingCat.hom_id, RingHom.id_apply]
    rfl
  · funext j
    simp only [Function.comp_apply]
    exact (gs_eq φ z U h _).symm

theorem isUnit_gs_iff (r : X' ⟶ X) (z : X') (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ X.basicOpen a := by
  rw [gs_eq r z U h a]
  refine (X'.mem_basicOpen (U := r ⁻¹ᵁ U) ((r.app U).hom a) z h).symm.trans ?_
  rw [← Scheme.Hom.preimage_basicOpen]
  rfl

theorem exists_pull {M : LB X} (s : LB.Sec M) (π : X' ⟶ X) :
    ∃ t : LB.Sec (M.pull π), ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (J), Good M z J →
      sval t r z J = gs (r ≫ π) z _ (s.f (J (r ≫ π))) := by
  have hle : ∀ j : PUnit → M.ι, LB.wchart M (fun _ : PUnit => π) j ≤ π ⁻¹ᵁ M.U (j ⟨⟩) :=
    fun _ _ hy => Set.mem_iInter.1 hy ⟨⟩
  refine ⟨⟨fun j => (X'.presheaf.map (homOfLE (hle j)).op).hom ((π.app (M.U (j ⟨⟩))).hom (s.f (j ⟨⟩))),
    fun i j => ?_⟩, ?_⟩
  · refine ReciprocityTheory.ChartRestriction.G.DVR.app_compat_generic π (hle i) (hle j) (s.f _) (s.f _) _ (s.compat _ _) _ ?_
    show (∏ k : PUnit, _) = _
    rw [Fintype.prod_unique, zpow_one]
  · intro Z r z J hJ
    have hm := hJ.mem (fun _ : PUnit => π) r
    have hz : (r ≫ π) z ∈ M.U (J (r ≫ π)) := hJ (r ≫ π)
    show gs r z _ ((X'.presheaf.map (homOfLE (hle _)).op).hom ((π.app _).hom (s.f _))) = _
    rw [gs_res r z (hle _) hm, gs_pull r π z _ hz]

theorem exists_prod {H : LB X} (hH : H.IsLB) (p g : X' ⟶ X) (t : ℤ) (s : LB.Sec H)
    (u : LB.Sec (LB.LinComb H (K := Fin 2) ![p, g] ![t, -1])) :
    ∃ w : LB.Sec (LB.LinComb H (K := PUnit) (fun _ => p) (fun _ => t)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (J), Good H z J →
        sval w r z J = gs (r ≫ g) z _ (s.f (J (r ≫ g))) * sval u r z J := by
  obtain ⟨t0, ht0⟩ := exists_pull s g
  have hF : FormEq (Sum.elim (fun _ : PUnit => g) ![p, g]) (Sum.elim (fun _ : PUnit => (1 : ℤ)) ![t, -1])
      (fun _ : PUnit => p) (fun _ => t) := by
    intro U _ h
    simp [Fintype.prod_sum_type, Fin.prod_univ_two]
  obtain ⟨w, hw⟩ := exists_sec hH hF (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.mulSec t0 u)
  refine ⟨w, fun Z r z J hJ => ?_⟩
  rw [hw Z r z J hJ, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_mulSec t0 u r z hJ, ht0 Z r z J hJ]

private theorem gs_sec_chart_transition {X Z : Scheme.{0}} {H : LB X} (s : LB.Sec H) (ψ : Z ⟶ X) (z : Z) (k k' : H.ι)
    (hk : ψ z ∈ H.U k) (hk' : ψ z ∈ H.U k') :
    gs ψ z (H.U k) (s.f k) = gs ψ z (H.U k ⊓ H.U k') (H.g k k' : Γ(X, H.U k ⊓ H.U k')) * gs ψ z (H.U k') (s.f k') := by
  have hkk : ψ z ∈ H.U k ⊓ H.U k' := TopologicalSpace.Opens.mem_inf.2 ⟨hk, hk'⟩
  rw [← gs_res ψ z (inf_le_left : H.U k ⊓ H.U k' ≤ H.U k) hkk, s.compat k k', gs_mul ψ z _ hkk,
    gs_res ψ z inf_le_right hkk]

theorem exists_end_of_thickenings : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : Over (Spec (CommRingCat.of R))), Smooth Y.hom → IsProjBy Y.hom → ∀ f : ∀ e, (thickObj R I e Y).left ⟶ Y.left, (∀ e, f e ≫ Y.hom = pullback.fst Y.hom (thick R I e) ≫ Y.hom) → (∀ e, thickMap R I e Y ≫ f (e + 1) = f e) → ∃ g : Y ⟶ Y, ∀ e, pullback.fst Y.hom (thick R I e) ≫ g.left = f e := by
  intro R _ _ _ I hI Y hsm hpr f hf hfc
  obtain ⟨H, hH, n, s, hva⟩ := id hpr
  obtain ⟨t, m, u, hcov, hu⟩ := GlobalTheory.T.exists_compatible_generatingSections_all_thickenings R I Y H n s hsm hH hva f hfc
  have hw0 : ∀ e (i : Fin (n + 1)) (j : Fin (m + 1)), ∃ w : LB.Sec (LB.LinComb H (K := PUnit)
      (fun _ => pullback.fst Y.hom (thick R I e)) (fun _ => t)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e Y).left) (z : Z) (J), Good H z J →
        sval w r z J = gs (r ≫ f e) z _ ((s i).f (J (r ≫ f e))) * sval (u e j) r z J :=
    fun e i j => exists_prod hH (pullback.fst Y.hom (thick R I e)) (f e) t (s i) (u e j)
  choose w hw using hw0
  have hS0 : ∀ (i : Fin (n + 1)) (j : Fin (m + 1)), ∃ S : LB.Sec (LB.LinComb H (K := PUnit)
      (fun _ => 𝟙 Y.left) (fun _ => t)),
      ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e Y).left) (z : Z) (J), Good H z J →
        sval S (r ≫ pullback.fst Y.hom (thick R I e)) z J = sval (w e i j) r z J := by
    intro i j
    refine GlobalTheory.T.exists_section_linearCombination_of_compatible_thickenings R I hI Y hsm hpr Y.left H PUnit (fun _ => 𝟙 Y.left) (fun _ => t)
      (fun e _ => pullback.fst Y.hom (thick R I e)) hH (fun e k => Category.comp_id _) (fun e => w e i j) ?_
    intro e z J hJ
    rw [hw (e + 1) i j _ _ z J hJ, hw e i j _ _ z J hJ, hfc e, Category.id_comp, hu e j z J hJ]
  choose S hS using hS0
  have hN : (LB.LinComb H (K := PUnit) (fun _ => 𝟙 Y.left) (fun _ => t)).IsLB := LB.isLB_linComb hH _ _
  have key : ∀ e (z : (thickObj R I e Y).left) (k' : PUnit → H.ι),
      pullback.fst Y.hom (thick R I e) z ∈ H.U (k' ⟨⟩) →
      ∃ J, Good H z J ∧ f e z ∈ H.U (J (f e)) ∧ ∀ i j,
        gs (pullback.fst Y.hom (thick R I e)) z
            ((LB.LinComb H (K := PUnit) (fun _ => 𝟙 Y.left) (fun _ => t)).U k') ((S i j).f k') =
          gs (f e) z (H.U (J (f e))) ((s i).f (J (f e))) * sval (u e j) (𝟙 _) z J := by
    intro e z k' hz
    obtain ⟨J, hJ, hJk⟩ := exists_good H hH z (fun _ : PUnit => 𝟙 _ ≫ pullback.fst Y.hom (thick R I e))
      (fun _ => k' ⟨⟩) (fun _ _ _ => rfl) (fun _ => by simpa using hz)
    refine ⟨J, hJ, hJ (f e), fun i j => ?_⟩
    have h1 := (hS i j e _ (𝟙 _) z J hJ).trans (hw e i j _ (𝟙 _) z J hJ)
    rw [sval_of (S i j) _ z J k' (fun k => by cases k; simpa using hJk ⟨⟩)] at h1
    rw [Category.id_comp, Category.id_comp] at h1
    exact h1
  have hcov' : (⨆ i, ⨆ j, nonzeroLocus (S i j)) = ⊤ := by
    have hjac : I ≤ (⊥ : Ideal R).jacobson := by have := hI; exact IsAdicComplete.le_jacobson_bot (I := I)
    have : IsProper Y.hom := GlobalTheory.AbLaw.isProper_of_isProjBy R Y.left Y.hom hpr
    refine GlobalTheory.T.open_eq_top_of_contains_special_part_universallyClosed R I hjac Y _ fun z => ?_
    have hz1 : z ∈ ⨆ j, nonzeroLocus (u 0 j) := by rw [hcov]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hz1
    unfold nonzeroLocus at hj
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hj
    have hz2 : f 0 z ∈ ⨆ i, nonzeroLocus (s i) := by rw [hva.1]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz2
    unfold nonzeroLocus at hi
    obtain ⟨kk0, hkk0⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
    have hkU : z ∈ LB.wchart H ![pullback.fst Y.hom (thick R I 0), f 0] k := Scheme.basicOpen_le _ _ hk
    have hq : pullback.fst Y.hom (thick R I 0) z ∈ H.U (k 0) := Set.mem_iInter.1 hkU 0
    obtain ⟨J, hJ, hJe, hv⟩ := key 0 z (fun _ => k 0) hq
    have hqN : pullback.fst Y.hom (thick R I 0) z ∈
        (LB.LinComb H (K := PUnit) (fun _ => 𝟙 Y.left) (fun _ => t)).U (fun _ => k 0) :=
      Set.mem_iInter.2 fun _ => hq
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, TopologicalSpace.Opens.mem_iSup.2 ⟨j, ?_⟩⟩
    unfold nonzeroLocus
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => k 0, ?_⟩
    rw [← isUnit_gs_iff _ _ _ hqN, hv i j]
    refine IsUnit.mul ?_ ?_
    · have hm0 : f 0 z ∈ H.U kk0 := Scheme.basicOpen_le _ _ hkk0
      have hu0 := (isUnit_gs_iff (f 0) z (H.U kk0) hm0 ((s i).f kk0)).2 hkk0
      rw [gs_sec_chart_transition (s i) (f 0) z kk0 (J (f 0)) hm0 hJe] at hu0
      exact isUnit_of_mul_isUnit_right hu0
    · have hm := hJ.mem ![pullback.fst Y.hom (thick R I 0), f 0] (𝟙 _)
      rw [sval_of (u 0 j) (𝟙 _) z J _ (fun _ => rfl), sec_trans (u 0 j) (𝟙 _) z hm hkU]
      exact (Units.isUnit _).mul ((isUnit_gs_iff _ _ _ hkU _).2 hk)
  have hrel : ∀ i i' j j' k, (S i j).f k * (S i' j').f k = (S i j').f k * (S i' j).f k := by
    intro i i' j j' k
    have hF : (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.X 2 * MvPolynomial.X 3 :
        MvPolynomial (Fin 4) R).IsHomogeneous 2 :=
      ((MvPolynomial.isHomogeneous_X R 0).mul (MvPolynomial.isHomogeneous_X R 1)).sub
        ((MvPolynomial.isHomogeneous_X R 2).mul (MvPolynomial.isHomogeneous_X R 3))
    have h := GlobalTheory.T.homogeneousForm_sections_eq_zero_of_thickenings R I hI Y hsm hpr _ (Fin 4) ![S i j, S i' j', S i j', S i' j] 2 _ hN hF ?_ k
    · simpa [sub_eq_zero] using h
    · intro e z k hz
      obtain ⟨J, hJ, hJe, hv⟩ := key e z k (Set.mem_iInter.1 hz ⟨⟩)
      rw [gs_eval Y.hom _ z _ hz]
      simp [hv]
      ring
  have hhom : ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous d →
      (∀ k, MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst Y.hom (H.U k)) (fun i => (s i).f k) F = 0) →
      ∀ j k, MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst Y.hom ((LB.LinComb H (K := PUnit) (fun _ => 𝟙 Y.left) (fun _ => t)).U k))
        (fun i => (S i j).f k) F = 0 := by
    intro d F hF h0 j
    refine GlobalTheory.T.homogeneousForm_sections_eq_zero_of_thickenings R I hI Y hsm hpr _ (Fin (n + 1)) (fun i => S i j) d F hN hF ?_
    intro e z k hz
    obtain ⟨J, hJ, hJe, hv⟩ := key e z k (Set.mem_iInter.1 hz ⟨⟩)
    rw [gs_eval Y.hom _ z _ hz]
    simp only [hv]
    have h2 := gs_eval Y.hom (f e) z (H.U (J (f e))) hJe (fun i => (s i).f (J (f e))) F
    rw [h0, hf e] at h2
    have hz0 : gs (f e) z (H.U (J (f e))) 0 = 0 := by rw [gs_eq _ _ _ hJe, map_zero, map_zero]
    rw [eval₂_scale _ (sval (u e j) (𝟙 _) z J) (fun i => gs (f e) z (H.U (J (f e))) ((s i).f (J (f e)))) hF,
      ← h2, hz0, zero_mul]
  obtain ⟨φ, hφ, huniq⟩ := GlobalTheory.T.exists_morphism_to_projective_of_rank_one_sections R Y.left Y.hom H n s hH hva Y.left Y.hom _ m S hN hcov' hrel hhom
  refine ⟨Over.homMk φ hφ, fun e => ?_⟩
  refine huniq _ (pullback.fst Y.hom (thick R I e)) (f e) (hf e) ?_
  intro z k k' i i' j hzk hzk'
  obtain ⟨J, hJ, hJe, hv⟩ := key e z k' (Set.mem_iInter.1 hzk' ⟨⟩)
  rw [hv, hv, gs_sec_chart_transition (s i) (f e) z k (J (f e)) hzk hJe, gs_sec_chart_transition (s i') (f e) z k (J (f e)) hzk hJe]
  ring

end GlobalTheory.EndAlg
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_weightBundle_torusQuotientTower_algebraisation : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (χ : s.X), ∃ O : LB a.B.left, O.IsLB ∧ (∃ u : LB.Gen (abelian₂ a.B O), u.IsGen) ∧ ∀ e, ∃ u : LB.Gen (O.pull ((t.l e).Q.q.left ≫ a.b e)), u.IsGen ∧ ∀ j, IsWt (t.l e).Q.i _ (u.s j).val χ := by
  first | exact @GlobalTheory.WtTower.exists_weight_bundle_alg | exact GlobalTheory.WtTower.exists_weight_bundle_alg | (intros; apply GlobalTheory.WtTower.exists_weight_bundle_alg <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.kTriv_torusQuotientTower_algebraisation : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → Laws → AllSet fun s => ∀ (t : Tower s) (a : t.Alg), KTriv a.B a.M.L.L := by
  first | exact @GlobalTheory.UU.Principal.kTriv_alg | exact GlobalTheory.UU.Principal.kTriv_alg | (intros; apply GlobalTheory.UU.Principal.kTriv_alg <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.UU.SchurComp



theorem components_proportional : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => ∀ N : ℕ, 1 ≤ N → ∀ (α mu : D.X) (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D (Kbar V) N α mu) (DegPre.deltaε N))), u.IsGen → U.Supp (Kbar V) N α → ∃ a : Kbar V, ∀ t s, U.ExpF (Kbar V) N t s → ∀ z J, Good D.P.L z J → sval (s (α + N • mu)) (𝟙 _) z J = gs (𝟙 _) z ⊤ (DegPre.constBF D (Kbar V) a ⊤) * (sval (s α) (DegPre.trF D (Kbar V) mu).left z J * (val u (𝟙 _) z J).val)) := by
  intro hL hL2 V _ _ _ hV D A G _ _ U N hN α mu u hu hS
  have := hV.1
  have := hV.2.2
  have hN0 : N ≠ 0 := by omega
  have hNF : (N : Kbar V) ≠ 0 := Nat.cast_ne_zero.2 hN0
  obtain ⟨Φ, e, hfr, hθ, hmul, hcomm, hnd⟩ :=
    GlobalTheory.ThetaRep.exists_projective_rep hL hL2 _ A (Kbar V) (jFK (R := V) (Kbar V)) N hNF
  obtain ⟨m, hm, hact, -⟩ := GlobalTheory.UU.Eqv.main hL hL2 V hV D A G U N hN
  obtain ⟨hw1, hw2, hw3⟩ := GlobalTheory.T.lineBundleSections_torusTorsion_weightSpaces hL hL2 V hV D A G U N hN
  have huniq := GlobalTheory.UU.ExpFUniq.main V hV D A G U (Kbar V) N
  choose xp hxp using GlobalTheory.UU.ExpTotal.expF_total hL hL2 V hV D A G U (Kbar V) N hN
  have hcA := (hL.mulN _ A N hN).2.2.2.2 (Kbar V) (jFK (R := V) (Kbar V)) hNF
  have hcH := (GlobalTheory.GtCount.card_gtTors hL hL2 V D (Kbar V) N hNF).1
  have hg : A.g = D.P.g + D.rank := GlobalTheory.UU.PreU.dim_eq V hV D A G U
  have hlinF := ExpLin.expF_linear V hV D A G U (Kbar V) N
  have hbas := exists_basis_twist_field hL hL2 V D (Kbar V) N hN
  clear * - hL hN0 hu hS Φ e hfr hθ hmul hcomm hnd m hm hact hw1 hw2 hw3 huniq xp hxp hcA hcH hg hlinF hbas
  have := A.isAb.comm
  let iso := (Scheme.ΓSpecIso (CommRingCat.of (Kbar V))).commRingCatIsoToRingEquiv
  let S : Subgroup (TFK (R := V) (Kbar V) ⟶ A.A) := (powMonoidHom N).ker
  have hcS : Nat.card S = N ^ (2 * A.g) := hcA
  have : Finite S := Nat.finite_of_card_ne_zero (hcS ▸ pow_ne_zero _ hN0)
  obtain ⟨x, hx⟩ : ∃ x : SecM A.A A.L N (TFK (R := V) (Kbar V)) → Raw D (Kbar V) N,
    ∀ v, U.ExpF (Kbar V) N (SecM.toSec A.A v) (x v) := ⟨_, fun v => hxp _⟩
  have hxe : ∀ t s, U.ExpF (Kbar V) N t s → x (SecM.ofSec A.A t) = s := fun t s h => (huniq _ _ _ _ (hx _) h).1 rfl
  have hsupp : ∀ β, U.Supp (Kbar V) N β ↔ ∃ v j, (x v β).f j ≠ 0 := fun β =>
    ⟨fun ⟨t, s, h, hj⟩ => ⟨SecM.ofSec A.A t, by rwa [hxe t s h]⟩, fun ⟨v, hv⟩ => ⟨_, _, hx v, hv⟩⟩
  refine (proportional_raw (D := D) (k := Γ((TFK (R := V) (Kbar V)).left, ⊤)) (A := S)
    (E := SecM A.A A.L N (TFK (R := V) (Kbar V))) hL.globalFns iso e Φ ?_ ?_ ?_ ?_ hN0 (fun g => ⟨m g, (hact g).1⟩)
    ?_ ?_ (n := N ^ D.P.g) ?_ x ?_ ?_ ?_ ?_ ?_ ?_ ?_ α mu u hu ((hsupp _).1 hS)).elim fun a ha => ?_
  · rw [hcS, mul_comm, pow_mul]; exact congrArg (· ^ 2) hfr
  · exact fun a b => hmul a b (a * b : S) rfl
  · exact fun a b => (hcomm a b).2
  · exact fun a h => Subtype.ext (hnd a h)
  · exact fun g g' h => hm (congrArg Subtype.val h)
  · rw [hcS, hcH, hg, ← pow_add]; exact le_of_eq (congrArg _ (by ring))
  · rw [← pow_add, add_comm, ← hg]; exact hfr.ge
  · intro c v v' β
    obtain ⟨c, rfl⟩ := iso.symm.surjective c
    choose s hs using fun β => exists_comb ((fst (TF (R := V) (Kbar V)) D.P.A).left.appTop.hom (iso.symm c))
      (x v β) (x v' β)
    have := hlinF _ _ (SecM.toSec A.A (iso.symm c • v + v' :)) _ _ s c (hx v) (hx v') (fun _ => rfl) hs
    rw [(huniq _ _ _ _ (hx _) this).1 rfl, iso.apply_symm_apply]
    exact hs β
  · exact fun v v' h => congrArg (SecM.ofSec A.A) ((huniq _ _ _ _ (hx v) (hx v')).2 h)
  · intro χ v
    obtain ⟨t', s', h, H⟩ := hw1 χ _ _ (hx v)
    exact ⟨SecM.ofSec A.A t', by rwa [hxe _ _ h]⟩
  · exact fun χ => (hw2 χ).imp fun ν h => (hsupp _).1 h
  · exact fun χ hχ v h h' => Subtype.ext (funext (hw3 χ ((hsupp _).2 hχ) _ _ (hx v) h h'))
  · exact fun β => (hbas β).imp fun b hb s => (hb s).exists
  · intro g
    obtain ⟨θ, hθ₁, hθ₂⟩ := hθ ⟨m g, (hact g).1⟩
    obtain ⟨w, hw, H⟩ := (hact g).2 θ hθ₁
    exact ⟨w, hw, fun v => H _ _ _ _ (hx _) (hx _) (hθ₂ v)⟩
  · refine ⟨a, fun t s h => ?_⟩
    rw [← hxe t s h]
    exact ha _

end GlobalTheory.UU.SchurComp

end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

theorem _root_.GlobalTheory.T.exists_automorphism_inducing_frobenius_all_degrees : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ p : QkPt D.toPre F k, ∃ ψ : (TFK (R := R) F ⊗ A.A) ≅ (TFK (R := R) F ⊗ A.A), ∀ (n N : ℕ), 1 ≤ n → N = k * n → ∀ q : QkPt D.toPre F N, q.y = n • p.y → q.g = p.g → IndAt U.toUnifPre F N q ψ.hom := by
  first | exact @GlobalTheory.InducingAut.exists_aut | exact GlobalTheory.InducingAut.exists_aut | (intros; apply GlobalTheory.InducingAut.exists_aut <;> assumption)
end
