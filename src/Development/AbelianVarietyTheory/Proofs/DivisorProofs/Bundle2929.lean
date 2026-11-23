module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle129
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle094
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle807
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle152
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle183
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2808
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.SameChain

theorem spec_endo_eq_id {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    (frac : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) (g : Sp Ω ⟶ Sp Ω)
    (h : g ≫ spMap R.val.toRingHom = spMap R.val.toRingHom) : g = 𝟙 _ := by
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  have h2 : CommRingCat.ofHom R.val.toRingHom ≫ ψ = CommRingCat.ofHom R.val.toRingHom :=
    Spec.map_injective (by rw [Spec.map_comp]; exact h)
  have e : ∀ c ∈ R, ψ.hom c = c := fun c hc => congrArg (fun f => f.hom (⟨c, hc⟩ : R)) h2
  have hψ : ψ = 𝟙 _ := by
    ext x
    obtain ⟨a, ha, b, hb, rfl⟩ := frac x
    simp [map_div₀, e a ha, e b hb]
  rw [hψ, Spec.map_id]

theorem sec_of_pt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) {G : Over (Sp Ω)}
    (a : G.left ⟶ ρ.P.A.left) (h : IsPullback a G.hom ρ.P.A.hom (spMap S.R.val.toRingHom)) (w : Sp Ω ⟶ G.left)
    (x : S.Gam) (hw : w ≫ a = spMap S.R.val.toRingHom ≫ (ρ.pt x).left) : w ≫ G.hom = 𝟙 _ := by
  refine spec_endo_eq_id S.R S.frac _ ?_
  rw [Category.assoc, ← h.w, ← Category.assoc, hw, Category.assoc, Over.w (ρ.pt x)]
  simp

end GlobalTheory.Poinc.SameChain


open GlobalTheory.Poinc.SameChain in
theorem GlobalTheory.Poinc.same_chain_deep : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (D : Deep X₁ ε₁)
  (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A))
  (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)),
  Same X₁.ρ ε₁ ρ' ε' (fun x => x) (RingHom.id _) → Same D.X.ρ D.ε ρ₂ ε₂ (fun x => x) (RingHom.id _) →
  Same ρ' ε' ρ₂ ε₂ (fun a => D.lab a) (algebraMap X₁.Ω₁ D.X.Ω₁) := by
  intro g n F W Z i X₁ ε₁ D c₀ hc R' fg frac hth hev ρ' ε' c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂ ρ₂ ε₂ h1 h3
  obtain ⟨P₁, a₁, a₁', e₁, pa₁, pa₁', L₁, L₁', E₁, T₁⟩ := h1
  obtain ⟨P₀, b, b', e₀, pb, pb', L₀, L₀', E₀, T₀⟩ := D.same
  obtain ⟨P₃, c, c', e₃, pc, pc', L₃, L₃', E₃, T₃⟩ := h3
  have pa₁c : IsGrpPullback P₁.A X₁.ρ.P.A (spMap X₁.S.R.val.toRingHom) a₁ := pa₁.congr (by rw [RingHom.id_comp]) rfl
  have pcc : IsGrpPullback P₃.A D.X.ρ.P.A (spMap D.X.S.R.val.toRingHom) c := pc.congr (by rw [RingHom.id_comp]) rfl
  have hspc := Geo.Tor.spMap_comp X₁.S.R.val.toRingHom (algebraMap X₁.Ω₁ D.X.Ω₁)
  have pbc : IsGrpPullback P₀.A X₁.ρ.P.A (spMap (algebraMap X₁.Ω₁ D.X.Ω₁) ≫ spMap X₁.S.R.val.toRingHom) b :=
    pb.congr hspc rfl
  have wm : b ≫ X₁.ρ.P.A.hom = (P₀.A.hom ≫ spMap (algebraMap X₁.Ω₁ D.X.Ω₁)) ≫ spMap X₁.S.R.val.toRingHom := by
    rw [pbc.1.w, Category.assoc]
  set m := pa₁c.1.lift b (P₀.A.hom ≫ spMap (algebraMap X₁.Ω₁ D.X.Ω₁)) wm with hmdef
  have hm1 : m ≫ a₁ = b := pa₁c.1.lift_fst _ _ wm
  have hm2 : m ≫ P₁.A.hom = P₀.A.hom ≫ spMap (algebraMap X₁.Ω₁ D.X.Ω₁) := pa₁c.1.lift_snd _ _ wm
  have pm : IsGrpPullback P₀.A P₁.A (spMap (algebraMap X₁.Ω₁ D.X.Ω₁)) m := pa₁c.cancel (pbc.congr rfl hm1.symm) hm2
  obtain ⟨e, he_mon, he⟩ := grpPullback_iso pb' pcc
  haveI := he_mon
  have pe := isGrpPullback_of_iso e
  refine ⟨P₀, m ≫ a₁', e.hom.left ≫ c', e₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (pm.comp pa₁').congr (Geo.Tor.spMap_comp R'.val.toRingHom (algebraMap X₁.Ω₁ D.X.Ω₁)).symm rfl
  · exact (pe.comp pc').congr (Category.id_comp _) rfl
  · have A : LBIso (X₁.ρ.P.L.pull b) (P₁.L.pull m) :=
      LBIso.chartPull (chartPullSame X₁.ρ.P.L (K := PUnit) (fun _ => b) (fun _ => a₁) (fun _ => 1) m
        (fun _ => hm1.symm)) (chartPullPull P₁.L m) L₁.symm
    have B : LBIso (P₁.L.pull m) (ρ'.P.L.pull (m ≫ a₁')) :=
      LBIso.chartPull (chartPullPull P₁.L m) (chartPullSame ρ'.P.L (K := PUnit) (fun _ => m ≫ a₁') (fun _ => a₁')
        (fun _ => 1) m (fun _ => rfl)) L₁'
    exact LBIso.trans P₀.isLB (pull_isLB P₁.isLB m) (pull_isLB ρ'.P.isLB _)
      (LBIso.trans P₀.isLB (pull_isLB X₁.ρ.P.isLB b) (pull_isLB P₁.isLB m) L₀ A) B
  · have A : LBIso (D.X.ρ.P.L.pull b') (P₃.L.pull e.hom.left) :=
      LBIso.chartPull (chartPullSame D.X.ρ.P.L (K := PUnit) (fun _ => b') (fun _ => c) (fun _ => 1) e.hom.left
        (fun _ => he.symm)) (chartPullPull P₃.L e.hom.left) L₃.symm
    have B : LBIso (P₃.L.pull e.hom.left) (ρ₂.P.L.pull (e.hom.left ≫ c')) :=
      LBIso.chartPull (chartPullPull P₃.L e.hom.left) (chartPullSame ρ₂.P.L (K := PUnit)
        (fun _ => e.hom.left ≫ c') (fun _ => c') (fun _ => 1) e.hom.left (fun _ => rfl)) L₃'
    exact LBIso.trans P₀.isLB (pull_isLB P₃.isLB _) (pull_isLB ρ₂.P.isLB _)
      (LBIso.trans P₀.isLB (pull_isLB D.X.ρ.P.isLB b') (pull_isLB P₃.isLB _) L₀' A) B
  · intro E
    have k1 : (e₀ E).left ≫ m = m ≫ (e₁ E).left := by
      apply pa₁c.1.hom_ext
      · rw [Category.assoc, hm1, (E₀ E).1, Category.assoc, (E₁ E).1, ← Category.assoc, hm1]
      · rw [Category.assoc, hm2, ← Category.assoc, Over.w (e₀ E), Category.assoc, Over.w (e₁ E), hm2]
    have k3 : (e₀ E).left ≫ e.hom.left = e.hom.left ≫ (e₃ E).left := by
      apply pcc.1.hom_ext
      · rw [Category.assoc, he, (E₀ E).2, Category.assoc, (E₃ E).1, ← Category.assoc, he]
      · rw [Category.assoc, Over.w e.hom, Over.w (e₀ E), Category.assoc, Over.w (e₃ E), Over.w e.hom]
    refine ⟨?_, ?_⟩
    · rw [← Category.assoc, k1, Category.assoc, (E₁ E).2, Category.assoc]
    · rw [← Category.assoc, k3, Category.assoc, (E₃ E).2, Category.assoc]
  · intro x
    obtain ⟨w, hw, hw'⟩ := T₀ x
    obtain ⟨w₁, hw₁, hw₁'⟩ := T₁ x
    obtain ⟨w₃, hw₃, hw₃'⟩ := T₃ (D.lab x)
    have s0 : w ≫ P₀.A.hom = 𝟙 _ := sec_of_pt D.X.ρ b' pb'.1 w _ hw'
    have s1 : w₁ ≫ P₁.A.hom = 𝟙 _ := sec_of_pt ρ' a₁' pa₁'.1 w₁ _ hw₁'
    have s3 : w₃ ≫ P₃.A.hom = 𝟙 _ := sec_of_pt ρ₂ c' pc'.1 w₃ _ hw₃'
    have hwm : w ≫ m = spMap (algebraMap X₁.Ω₁ D.X.Ω₁) ≫ w₁ := by
      apply pa₁c.1.hom_ext
      · rw [Category.assoc, hm1, hw, Category.assoc, hw₁, hspc, Category.assoc, RingHom.id_comp]
      · rw [Category.assoc, hm2, ← Category.assoc, s0, Category.id_comp, Category.assoc, s1, Category.comp_id]
    have hwe : w ≫ e.hom.left = w₃ := by
      apply pcc.1.hom_ext
      · rw [Category.assoc, he, hw', hw₃, RingHom.id_comp]
      · rw [Category.assoc, Over.w e.hom, s0, s3]
    refine ⟨w, ?_, ?_⟩
    · rw [← Category.assoc, hwm, Category.assoc, hw₁', Geo.Tor.spMap_comp R'.val.toRingHom (algebraMap X₁.Ω₁ D.X.Ω₁),
        Category.assoc]
    · rw [← Category.assoc, hwe, hw₃']
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem isLab_onto_and_ker : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (yy : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy → Function.Surjective yy ∧ yy.ker = X₁.S.HH X₁.M z₁ := by
  intro g n F W Z i X₁ _ _ _ _ _ _ _ ε₁ _ p _ z₁ c yy hl
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, -, hR', y₀, hy₀, u, l, j, -, hyy, -⟩ := hl
  have hm : NeZero (X₁.S.r * X₁.S.N) :=
    ⟨Nat.mul_ne_zero (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega)⟩
  refine ⟨?_, ?_⟩
  · intro m
    obtain ⟨χ', rfl⟩ := QuotientAddGroup.mk_surjective m
    obtain ⟨a, ha⟩ := l.yy_onto (QuotientAddGroup.mk (j.symm χ'))
    exact ⟨a, by rw [hyy a _ ha, j.apply_symm_apply]⟩
  have hker : yy.ker = l.yy.ker := by
    ext a
    simp only [AddMonoidHom.mem_ker]
    obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (l.yy a)
    rw [hyy a χ hχ.symm, ← hχ, QuotientAddGroup.eq_zero_iff, QuotientAddGroup.eq_zero_iff]
    constructor
    · rintro ⟨v, hv⟩
      refine ⟨j.symm v, ?_⟩
      simp only [nsmulAddMonoidHom_apply] at hv ⊢
      rw [← map_nsmul, hv, j.symm_apply_apply]
    · rintro ⟨v, hv⟩
      refine ⟨j v, ?_⟩
      simp only [nsmulAddMonoidHom_apply] at hv ⊢
      rw [← map_nsmul, hv]
  have hint : ∀ a : X₁.o₁, ‖y₀ (algebraMap X₁.o₁ R' a)‖ ≤ 1 := fun a => by
    rw [hy₀]
    exact RatModel.norm_val_le_one c.cen ((X₁.M.O z₁).algebraMap_mem a)
  have hcl := GlobalTheory.UnitTheta.closure_unit_theta GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2
    GlobalTheory.ZH.uTors_closed _ _ _ ρ' p y₀ u l hint
  rw [hker, ← hcl.2]

  obtain ⟨x₀, hx₀⟩ := X₁.div z₁
  set val := X₁.M.val (gPt p ≫ c.y) with hval
  have hsp : ∀ w, (gPt p ≫ c.y) w ⤳ (gPt p ≫ c.y) (IsLocalRing.closedPoint (PadicAlgCl p)) :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)
  have hgz : (gPt p ≫ c.y) (IsLocalRing.closedPoint (PadicAlgCl p)) ⤳ z₁ :=
    RatModel.gPt_specializes c.cen _
  have hy : ∀ x, y₀ ⟨c₀ * X₁.S.th x, hth x⟩ = val (c₀ * X₁.S.th x) := fun x => hy₀ _
  have hmul : ∀ x, ‖val (c₀ * X₁.S.th x)‖ = ‖val (X₁.S.th x / X₁.S.th x₀)‖ * ‖val (c₀ * X₁.S.th x₀)‖ := by
    intro x
    rw [← norm_mul, hval, ← RatModel.val_mul hsp (RatModel.O_le_of_specializes hgz (hx₀.2 x)) (hR' (hth x₀))]
    congr 2
    have := hx₀.1
    field_simp
  have hδ : ‖val (c₀ * X₁.S.th x₀)‖ = (X₁.S.rechart c₀ hc R' fg frac hth hev).delta y₀ := by
    apply le_antisymm
    · rw [← hy]
      exact le_ciSup (f := fun x => ‖y₀ ⟨c₀ * X₁.S.th x, hth x⟩‖) (Set.finite_range _).bddAbove x₀
    · obtain ⟨x₁, hx₁⟩ := exists_eq_ciSup_of_finite (f := fun x => ‖y₀ ⟨c₀ * X₁.S.th x, hth x⟩‖)
      change ⨆ x, ‖y₀ ⟨c₀ * X₁.S.th x, hth x⟩‖ ≤ _
      rw [← hx₁, hy, hmul x₁]
      exact mul_le_of_le_one_left (norm_nonneg _) (RatModel.norm_val_le_one c.cen (hx₀.2 x₁))
  have key : ∀ x, x ∈ X₁.S.supI X₁.M z₁ ↔
      ‖y₀ ⟨c₀ * X₁.S.th x, hth x⟩‖ = (X₁.S.rechart c₀ hc R' fg frac hth hev).delta y₀ := by
    intro x
    change X₁.M.Div X₁.S.th x z₁ ↔ _
    rw [hx₀.div_iff_isUnit x, ← RatModel.norm_val_eq_one_iff c.cen (hx₀.2 x), hy, hmul x, hδ]
    exact (mul_eq_right₀ hcl.1.ne').symm
  rw [ThetaSys.HH]
  congr 1
  ext x
  exact (key x).symm

end GlobalTheory.Poinc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.LabBC

open GlobalTheory GlobalTheory.ArcPull GlobalTheory.TorusExt

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem qkExt_id' {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {C : Type} [Field C]
    [Algebra (FractionRing R) C] {k : ℕ} (p : QkPt D C k) : QkExt (RingHom.id C) p p := by
  have e : spMap (RingHom.id C) = 𝟙 _ := Spec.map_id _
  refine ⟨rfl, by rw [e, Category.id_comp], fun χ => ?_⟩
  rw [e]
  exact corr_of_val D.P.isLB fun y J hJ =>
    ((val_pull hJ _ _ _).trans (congrArg (fun r => val (p.g.s χ) r y J) (Category.id_comp _))).symm

theorem isAlgebraic_kb {R R₁ : Type} [CommRing R] [IsDomain R] [CommRing R₁] [IsDomain R₁] (ρ : R →+* R₁)
    (hρ : ρ.Finite) [Algebra (FractionRing R) (Kb R₁)]
    (hc : ∀ r, algebraMap (FractionRing R) (Kb R₁) (algebraMap R _ r) =
      algebraMap (FractionRing R₁) (Kb R₁) (algebraMap R₁ _ (ρ r))) :
    Algebra.IsAlgebraic (FractionRing R) (Kb R₁) := by
  letI : Algebra R R₁ := ρ.toAlgebra
  have h1 : ∀ r : R, algebraMap R (Kb R₁) r = algebraMap R₁ (Kb R₁) (ρ r) := fun r => by
    rw [IsScalarTower.algebraMap_apply R (FractionRing R₁) (Kb R₁), IsScalarTower.algebraMap_apply R R₁ (FractionRing R₁),
      IsScalarTower.algebraMap_apply R₁ (FractionRing R₁) (Kb R₁)]
    rfl
  haveI : IsScalarTower R R₁ (Kb R₁) := IsScalarTower.of_algebraMap_eq fun r => h1 r
  haveI : IsScalarTower R (FractionRing R) (Kb R₁) := IsScalarTower.of_algebraMap_eq fun r => by
    rw [h1, hc, IsScalarTower.algebraMap_apply R₁ (FractionRing R₁) (Kb R₁)]
  haveI : Module.Finite R R₁ := hρ
  haveI : Algebra.IsAlgebraic R R₁ := Algebra.IsAlgebraic.of_finite R R₁
  haveI : Algebra.IsAlgebraic R₁ (Kb R₁) :=
    (IsFractionRing.comap_isAlgebraic_iff (A := R₁) (K := FractionRing R₁)).2 inferInstance
  haveI : Algebra.IsAlgebraic R (Kb R₁) := Algebra.IsAlgebraic.trans R R₁ (Kb R₁)
  exact (IsFractionRing.comap_isAlgebraic_iff (A := R) (K := FractionRing R)).1 inferInstance

theorem galEqN_of_rel {R R₁ : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₁] [IsDomain R₁]
    [IsLocalRing R₁] (ρ : R →+* R₁) (hρ : FinExt ρ) (D : DegData R (maximalIdeal R))
    (D₁ : DegData R₁ (maximalIdeal R₁)) (hD : IsPullDeg ρ D.toPre D₁.toPre) (A : PolAV (Sp (FractionRing R)))
    (A₁ : PolAV (Sp (FractionRing R₁))) (a : A₁.A.left ⟶ A.A.left) (hfib : IsFib ρ A A₁ a) (lab : Labels D.toPre A)
    (n : ℕ) (hn : 1 ≤ n) (hGal : GalEqN n lab) [Algebra (FractionRing R) (Kb R₁)]
    (em : Kb R →ₐ[FractionRing R] Kb R₁) (lab₁ : Labels D₁.toPre A₁)
    (hc : ∀ r, algebraMap (FractionRing R) (Kb R₁) (algebraMap R _ r) =
      algebraMap (FractionRing R₁) (Kb R₁) (algebraMap R₁ _ (ρ r)))
    (hrel : ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre (Kb R) k) (p₁ : QkPt D.toPre (Kb R₁) k)
      (p' : QkPt D₁.toPre (Kb R₁) k), QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y →
      IsPullGtF ρ hD (Kb R₁) p₁.g p'.g → (lab₁ k p').left ≫ a = spMap em.toRingHom ≫ (lab k p).left) :
    GalEqN n lab₁ := by
  obtain ⟨ga, hga, hpb, -⟩ := hfib
  have hK : algebraMap (FractionRing R) (Kb R₁) = (algebraMap (FractionRing R₁) (Kb R₁)).comp ga :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => by
      simp only [RingHom.comp_apply, hga, hc])
  haveI : Algebra.IsAlgebraic (FractionRing R) (Kb R₁) := isAlgebraic_kb ρ hρ.2.2 hc
  let mu : Kb R₁ →ₐ[FractionRing R] Kb R := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hsurj : Function.Surjective em := fun z => by
    obtain ⟨w, hw⟩ := (Algebra.IsAlgebraic.algHom_bijective (em.comp mu)).2 z
    exact ⟨mu w, hw⟩
  let τ : Kb R ≃ₐ[FractionRing R] Kb R₁ := AlgEquiv.ofBijective em ⟨em.toRingHom.injective, hsurj⟩
  obtain ⟨hL, -⟩ := GlobalTheory.firstFiveLaws
  have hG := hL.globalFns
  have hB := D.tau_bimult
  have hB₁ := D₁.tau_bimult
  have hF : Compat ρ (Kb R₁) := hc
  intro σ₁ j P P' hPP'
  have hk : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn
  set e : Kb R →+* Kb R₁ := em.toRingHom with he_def
  set e' : Kb R₁ →+* Kb R := τ.symm.toAlgHom.toRingHom with he'_def
  set s₁ : Kb R₁ →+* Kb R₁ := σ₁.toRingHom with hs₁_def
  have hee' : e.comp e' = RingHom.id _ := RingHom.ext fun x => τ.apply_symm_apply x
  have hfσ : s₁.comp (algebraMap (FractionRing R) (Kb R₁)) = algebraMap (FractionRing R) (Kb R₁) := by
    rw [hK, ← RingHom.comp_assoc]
    exact congrArg (fun f => f.comp ga) σ₁.comp_algebraMap
  have hfσ₁ : s₁.comp (algebraMap (FractionRing R₁) (Kb R₁)) = algebraMap (FractionRing R₁) (Kb R₁) :=
    σ₁.comp_algebraMap
  have hfe : e.comp (algebraMap (FractionRing R) (Kb R)) = algebraMap (FractionRing R) (Kb R₁) := em.comp_algebraMap
  have hfe' : e'.comp (algebraMap (FractionRing R) (Kb R₁)) = algebraMap (FractionRing R) (Kb R) :=
    τ.symm.toAlgHom.comp_algebraMap
  have hfid : (RingHom.id (Kb R₁)).comp (algebraMap (FractionRing R) (Kb R₁)) = algebraMap (FractionRing R) (Kb R₁) :=
    RingHom.id_comp _

  let σ : Kb R →ₐ[FractionRing R] Kb R :=
    τ.symm.toAlgHom.comp ((({ σ₁.toRingHom with commutes' := fun x => RingHom.congr_fun hfσ x } : Kb R₁ →ₐ[FractionRing R] Kb R₁)).comp em)
  have hσ_def : σ.toRingHom = e'.comp (s₁.comp e) := rfl
  have hfσR : σ.toRingHom.comp (algebraMap (FractionRing R) (Kb R)) = algebraMap (FractionRing R) (Kb R) :=
    σ.comp_algebraMap
  have hes : e.comp σ.toRingHom = s₁.comp e := by
    rw [hσ_def, ← RingHom.comp_assoc, hee', RingHom.id_comp]
  obtain ⟨q, rfl⟩ := pullQk_surjective hD hG hF hB hB₁ P
  obtain ⟨q', rfl⟩ := pullQk_surjective hD hG hF hB hB₁ P'
  have hq' : q' = qkExt hB s₁ hfσ q := by
    apply GlobalTheory.QkPullEquiv.pullQk_injective hD hG hF hB hB₁
    rw [(qkExt_iff hB₁ s₁ hfσ₁ _ _).1 hPP',
      (qkExt_iff hB₁ s₁ hfσ₁ _ _).1 (GlobalTheory.QkRationalExt.qkExt_pullQk hD hG hB hB₁ hF hF s₁ hfσ hfσ₁ q)]
  have hid : ∀ z : QkPt D.toPre (Kb R₁) (n ^ j), qkExt hB (RingHom.id _) hfid z = z := fun z =>
    ((qkExt_iff hB _ hfid z z).1 (qkExt_id' z)).symm

  have hpq : ∀ z : QkPt D.toPre (Kb R₁) (n ^ j), QkExt e (qkExt hB e' hfe' z) z := fun z => by
    rw [qkExt_iff hB e hfe, GlobalTheory.QkRationalExt.qkExt_qkExt hB e' hfe' e hfe (RingHom.id _) hfid hee', hid]
  have hσpp : QkExt σ.toRingHom (qkExt hB e' hfe' q) (qkExt hB e' hfe' q') := by
    rw [qkExt_iff hB _ hfσR, GlobalTheory.QkRationalExt.qkExt_qkExt hB e' hfe' σ.toRingHom hfσR (e'.comp s₁)
      (by rw [RingHom.comp_assoc, hfσ, hfe']) (by rw [hσ_def, RingHom.comp_assoc, RingHom.comp_assoc, hee',
        RingHom.comp_id]), hq', GlobalTheory.QkRationalExt.qkExt_qkExt hB s₁ hfσ e' hfe' (e'.comp s₁) _ rfl]
  have hgal := hGal σ j _ _ hσpp
  have h₁ := hrel _ hk _ _ _ (hpq q) ((eq_pullQk_iff hD hG hF hB hB₁ q _).1 rfl).1
    ((eq_pullQk_iff hD hG hF hB hB₁ q _).1 rfl).2
  have h₂ := hrel _ hk _ _ _ (hpq q') ((eq_pullQk_iff hD hG hF hB hB₁ q' _).1 rfl).1
    ((eq_pullQk_iff hD hG hF hB hB₁ q' _).1 rfl).2
  apply hpb.1.hom_ext
  · rw [h₂, Category.assoc, h₁, hgal, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', hes]
  · rw [Category.assoc, Over.w (lab₁ (n ^ j) (pullQk hD hG hF hB hB₁ q')), Over.w (lab₁ (n ^ j) (pullQk hD hG hF hB hB₁ q))]
    show jFK (R := R₁) (Kb R₁) = spMap s₁ ≫ jFK (R := R₁) (Kb R₁)
    rw [spMap_comp', hfσ₁]

end GlobalTheory.Mum.LabBC
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.EndoHom

theorem isMonHom_of_prod_pow {S : Scheme.{0}} {A C : Over S} [GrpObj A] [GrpObj C] [IsCommMonObj C]
    (pr : Fin 8 → (A ⟶ C)) (hpr : ∀ a, IsMonHom (pr a))
    (huniq : ∀ (T' : Over S) (y : Fin 8 → (T' ⟶ C)), ∃! x : T' ⟶ A, ∀ a, x ≫ pr a = y a)
    (f : A ⟶ A) (e : Fin 8 → Fin 8 → ℤ)
    (hf : ∀ a, f ≫ pr a = ((List.finRange 8).map fun b => pr b ^ e a b).prod) : IsMonHom f := by
  refine isMonHom_of_mul f fun T x y => ?_
  obtain ⟨z, -, hu⟩ := huniq T (fun a => ((x * y) ≫ f) ≫ pr a)
  refine (hu ((x * y) ≫ f) fun a => rfl).trans (hu ((x ≫ f) * (y ≫ f)) fun a => ?_).symm
  have hpre : ∀ {T : Over S} (w : T ⟶ A) (a : Fin 8),
      w ≫ f ≫ pr a = ((List.finRange 8).map fun b => (w ≫ pr b) ^ e a b).prod := fun {T} w a => by
    let φ : (A ⟶ C) →* (T ⟶ C) := MonoidHom.mk' (w ≫ ·) fun g₁ g₂ => MonObj.comp_mul w g₁ g₂
    have h := map_list_prod φ ((List.finRange 8).map fun b => pr b ^ e a b)
    rw [List.map_map] at h
    rw [hf a]
    refine h.trans (congrArg List.prod (List.map_congr_left fun b _ => ?_))
    exact map_zpow φ (pr b) (e a b)
  have := hpr
  rw [MonObj.mul_comp, Category.assoc, Category.assoc, Category.assoc, hpre, hpre, hpre]
  simp only [MonObj.mul_comp, mul_zpow]
  exact (List.prod_map_mul).symm

theorem isMonHom_of_isGrpPullback_endo {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {b : S' ⟶ S} {φ : G'.left ⟶ G.left} (hg : IsGrpPullback G' G b φ) (f : G ⟶ G) (hf : IsMonHom f)
    (f₀ : G' ⟶ G') (h : f₀.left ≫ φ = φ ≫ f.left) : IsMonHom f₀ := by
  obtain ⟨f', hf', he⟩ := GlobalTheory.Ex.Arch.exists_pull_endo hg f hf
  have : f' = f₀ := Over.OverMorphism.ext (hg.1.hom_ext (he.trans h.symm) ((Over.w f').trans (Over.w f₀).symm))
  exact this ▸ hf'

end GlobalTheory.Poinc.EndoHom


open GlobalTheory.Poinc.EndoHom in
theorem GlobalTheory.Poinc.isMonHom_of_same_rechart : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R') (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X.ρ ε ρ' ε' (fun x => x) (RingHom.id _) → ∀ E, IsMonHom (ε' E) := by
  intro g n F W Z i X ε hD c₀ hc R' fg frac hth hev ρ' ε' hS E
  obtain ⟨c, -, pr, hpr, huniq, -, hε⟩ := hD
  have hE : IsMonHom (ε E) := isMonHom_of_prod_pow pr hpr huniq (ε E) E (hε E)
  obtain ⟨P₀, a, a', ε₀, h₁, h₂, -, -, hε₀, -⟩ := hS
  have h₀ : IsMonHom (ε₀ E) := isMonHom_of_isGrpPullback_endo h₁ (ε E) hE (ε₀ E) (hε₀ E).1
  have : IsSchemeTheoreticallyDominant (spMap (X.S.rechart c₀ hc R' fg frac hth hev).R.val.toRingHom) :=
    GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ Subtype.val_injective
  have := ρ'.P.isAb.smooth
  have := ρ'.P.isAb.proper
  exact GlobalTheory.ExtUnique.isMonHom_of_isGrpPullback h₂ h₂ (ε₀ E) (ε' E) (hε₀ E).2
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GSum

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}


open Classical in
def base (X₁ : Setup F W i) (z₁ : X₁.M.Z) : X₁.S.Gam :=
  if h : (X₁.S.supI X₁.M z₁).Nonempty then h.some else 0

def wtChar (D : Deep X₁ ε₁) (T : AddSubgroup D.X.S.Gam) (a : D.X.S.Gam) : T →+ ZMod D.X.S.N where
  toFun t := ZMod.castHom (dvd_mul_left D.X.S.N D.X.S.r) (ZMod D.X.S.N) (eStd D.X.S.g _ (t : D.X.S.Gam) (D.m • a))
  map_zero' := by simp [eStd]
  map_add' := by
    intro s t
    rw [← map_add (f := _)]
    congr 1
    simp only [eStd, AddSubgroup.coe_add, Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring


open Classical in
def lift (D : Deep X₁ ε₁) (z₂ : D.X.M.Z) (κ : X₁.S.Gam) : D.X.S.Gam :=
  if h : ∃ h' ∈ D.X.S.HH D.X.M z₂, D.m • h' = D.lab κ then h.choose else 0

def part (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z) (a : D.X.S.Gam) (κ : X₁.S.HH X₁.M z₁) : D.X.Ω₁ :=
  (∑ j, algebraMap D.X.o₁ D.X.Ω₁ (D.X.S.proj (D.X.S.TT D.X.M z₂) (wtChar D _ a) j D.X.ρ.i₀) *
      D.X.S.ev (lift D z₂ (κ : X₁.S.Gam)) j) / D.X.S.th (D.lab (base X₁ z₁))

end GlobalTheory.Poinc.GSum
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.volume_complexPoints_properClosed_chart_field : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (Z : Set X), IsClosed Z → genericPoint X ∉ Z → ∀ c : AlgChart p σ D, volume (c.e '' (c.e.source ∩ {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z})) = 0 := by
  first | exact @GlobalTheory.ChernNull.chart_null_field | exact GlobalTheory.ChernNull.chart_null_field | (intros; apply GlobalTheory.ChernNull.chart_null_field <;> assumption)
end
