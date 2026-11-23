module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle777
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2845
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionMapWelldefinedAdditiveCharacters
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointActionPullbackData
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2847
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle787
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2848
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2850
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2896
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

noncomputable section

namespace GlobalTheory.Mum.Two.GlueLevel

section General

variable {X₁ X₂ B₁ B₂ H₁ H₂ : Scheme.{0}} {M₁ : LB B₁} {M₂ : LB B₂} {L₁ : LB H₁} {L₂ : LB H₂}

theorem map_inl_apply (f₁ : X₁ ⟶ B₁) (f₂ : X₂ ⟶ B₂) (x : X₁) :
    (coprod.map f₁ f₂) ((coprod.inl : X₁ ⟶ X₁ ⨿ X₂) x) = (coprod.inl : B₁ ⟶ B₁ ⨿ B₂) (f₁ x) := by
  change ((coprod.inl : X₁ ⟶ X₁ ⨿ X₂) ≫ coprod.map f₁ f₂) x = _
  rw [coprod.inl_map]; rfl

theorem map_inr_apply (f₁ : X₁ ⟶ B₁) (f₂ : X₂ ⟶ B₂) (x : X₂) :
    (coprod.map f₁ f₂) ((coprod.inr : X₂ ⟶ X₁ ⨿ X₂) x) = (coprod.inr : B₂ ⟶ B₁ ⨿ B₂) (f₂ x) := by
  change ((coprod.inr : X₂ ⟶ X₁ ⨿ X₂) ≫ coprod.map f₁ f₂) x = _
  rw [coprod.inr_map]; rfl

theorem mem_pull_inl (M₁ : LB B₁) (M₂ : LB B₂) (f₁ : X₁ ⟶ B₁) (f₂ : X₂ ⟶ B₂) (x : X₁)
    (J : PUnit → (join M₁ M₂).ι) :
    (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) x ∈ ((join M₁ M₂).pull (coprod.map f₁ f₂)).U J ↔
      x ∈ (M₁.pull f₁).U (fun _ => (J PUnit.unit).1) := by
  rw [mem_pull, mem_pull, map_inl_apply]
  exact (isPart_inl M₁ M₂).mem _ _

theorem mem_pull_inr (M₁ : LB B₁) (M₂ : LB B₂) (f₁ : X₁ ⟶ B₁) (f₂ : X₂ ⟶ B₂) (x : X₂)
    (J : PUnit → (join M₁ M₂).ι) :
    (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) x ∈ ((join M₁ M₂).pull (coprod.map f₁ f₂)).U J ↔
      x ∈ (M₂.pull f₂).U (fun _ => (J PUnit.unit).2) := by
  rw [mem_pull, mem_pull, map_inr_apply]
  exact (isPart_inr M₁ M₂).mem _ _

end General

section Glue

variable {X₁ X₂ B₁ B₂ H₁ H₂ : Scheme.{0}} {M₁ : LB B₁} {M₂ : LB B₂} {L₁ : LB H₁} {L₂ : LB H₂}
  {p₁ : X₁ ⟶ B₁} {p₂ : X₂ ⟶ B₂} {f₁ : X₁ ⟶ H₁} {f₂ : X₂ ⟶ H₂}

theorem gm_div_inl (x : X₁) (i j : (PUnit → (join M₁ M₂).ι) × (PUnit → (join L₁ L₂).ι))
    (hi : (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) x ∈
      (LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U i)
    (hj : (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) x ∈
      (LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U j) :
    gm coprod.inl x _
        ((LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).g i j) =
      gm (𝟙 X₁) x _ ((LB.div (M₁.pull p₁) (L₁.pull f₁)).g
        (fun _ => (i.1 PUnit.unit).1, fun _ => (i.2 PUnit.unit).1)
        (fun _ => (j.1 PUnit.unit).1, fun _ => (j.2 PUnit.unit).1)) := by
  obtain ⟨I₁, K₁⟩ := i
  obtain ⟨I₂, K₂⟩ := j
  have a₁ := mem_pull.1 hi.1
  have a₂ := mem_pull.1 hj.1
  have b₁ := mem_pull.1 hi.2
  have b₂ := mem_pull.1 hj.2
  rw [map_inl_apply] at a₁ a₂ b₁ b₂
  have a₁' := ((isPart_inl M₁ M₂).mem _ _).1 a₁
  have a₂' := ((isPart_inl M₁ M₂).mem _ _).1 a₂
  have b₁' := ((isPart_inl L₁ L₂).mem _ _).1 b₁
  have b₂' := ((isPart_inl L₁ L₂).mem _ _).1 b₂
  have d := gm_div_g (L := join M₁ M₂) (F := coprod.map p₁ p₂) (L' := (join L₁ L₂).pull (coprod.map f₁ f₂))
    coprod.inl x (I₁ PUnit.unit) (I₂ PUnit.unit) K₁ K₂ (mem_pull.1 hi.1) (mem_pull.1 hj.1) hi.2 hj.2
  have d₁ := gm_div_g (L := M₁) (F := p₁) (L' := L₁.pull f₁) (𝟙 X₁) x (I₁ PUnit.unit).1 (I₂ PUnit.unit).1
    (fun _ => (K₁ PUnit.unit).1) (fun _ => (K₂ PUnit.unit).1) a₁' a₂' (mem_pull.2 b₁') (mem_pull.2 b₂')
  refine d.trans (Eq.trans ?_ d₁.symm)
  rw [gm_pull_g (join L₁ L₂) (coprod.map f₁ f₂) coprod.inl x K₁ K₂ hi.2 hj.2,
    gm_pull_g L₁ f₁ (𝟙 X₁) x _ _ (mem_pull.2 b₁') (mem_pull.2 b₂'), coprod.inl_map, coprod.inl_map,
    (isPart_inl M₁ M₂).g _ p₁ x _ _ a₁' a₂', (isPart_inl L₁ L₂).g _ f₁ x _ _ b₁' b₂', Category.id_comp,
    Category.id_comp]

theorem gm_div_inr (x : X₂) (i j : (PUnit → (join M₁ M₂).ι) × (PUnit → (join L₁ L₂).ι))
    (hi : (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) x ∈
      (LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U i)
    (hj : (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) x ∈
      (LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U j) :
    gm coprod.inr x _
        ((LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).g i j) =
      gm (𝟙 X₂) x _ ((LB.div (M₂.pull p₂) (L₂.pull f₂)).g
        (fun _ => (i.1 PUnit.unit).2, fun _ => (i.2 PUnit.unit).2)
        (fun _ => (j.1 PUnit.unit).2, fun _ => (j.2 PUnit.unit).2)) := by
  obtain ⟨I₁, K₁⟩ := i
  obtain ⟨I₂, K₂⟩ := j
  have a₁ := mem_pull.1 hi.1
  have a₂ := mem_pull.1 hj.1
  have b₁ := mem_pull.1 hi.2
  have b₂ := mem_pull.1 hj.2
  rw [map_inr_apply] at a₁ a₂ b₁ b₂
  have a₁' := ((isPart_inr M₁ M₂).mem _ _).1 a₁
  have a₂' := ((isPart_inr M₁ M₂).mem _ _).1 a₂
  have b₁' := ((isPart_inr L₁ L₂).mem _ _).1 b₁
  have b₂' := ((isPart_inr L₁ L₂).mem _ _).1 b₂
  have d := gm_div_g (L := join M₁ M₂) (F := coprod.map p₁ p₂) (L' := (join L₁ L₂).pull (coprod.map f₁ f₂))
    coprod.inr x (I₁ PUnit.unit) (I₂ PUnit.unit) K₁ K₂ (mem_pull.1 hi.1) (mem_pull.1 hj.1) hi.2 hj.2
  have d₁ := gm_div_g (L := M₂) (F := p₂) (L' := L₂.pull f₂) (𝟙 X₂) x (I₁ PUnit.unit).2 (I₂ PUnit.unit).2
    (fun _ => (K₁ PUnit.unit).2) (fun _ => (K₂ PUnit.unit).2) a₁' a₂' (mem_pull.2 b₁') (mem_pull.2 b₂')
  refine d.trans (Eq.trans ?_ d₁.symm)
  rw [gm_pull_g (join L₁ L₂) (coprod.map f₁ f₂) coprod.inr x K₁ K₂ hi.2 hj.2,
    gm_pull_g L₂ f₂ (𝟙 X₂) x _ _ (mem_pull.2 b₁') (mem_pull.2 b₂'), coprod.inr_map, coprod.inr_map,
    (isPart_inr M₁ M₂).g _ p₂ x _ _ a₁' a₂', (isPart_inr L₁ L₂).g _ f₂ x _ _ b₁' b₂', Category.id_comp,
    Category.id_comp]

theorem exists_iso_glue (w₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)) (w₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂))
    (hw₁ : w₁.IsGen) (hw₂ : w₂.IsGen) :
    ∃ W : LB.Iso ((join L₁ L₂).pull (coprod.map f₁ f₂)) ((join M₁ M₂).pull (coprod.map p₁ p₂)), W.IsGen ∧
      (∀ (Z : Scheme.{0}) (r : Z ⟶ X₁) (z : Z) (j : (join M₁ M₂).ι) (k : (join L₁ L₂).ι), p₁ (r z) ∈ M₁.U j.1 →
        f₁ (r z) ∈ L₁.U k.1 → gw W (r ≫ coprod.inl) z j (fun _ => k) = gw w₁ r z j.1 (fun _ => k.1)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X₂) (z : Z) (j : (join M₁ M₂).ι) (k : (join L₁ L₂).ι), p₂ (r z) ∈ M₂.U j.2 →
        f₂ (r z) ∈ L₂.U k.2 → gw W (r ≫ coprod.inr) z j (fun _ => k) = gw w₂ r z j.2 (fun _ => k.2) := by
  have key : ∀ p : (PUnit → (join M₁ M₂).ι) × (PUnit → (join L₁ L₂).ι),
      ∃ a : Γ(X₁ ⨿ X₂,
        (LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U p)ˣ,
      (∀ (Z : Scheme.{0}) (ψ : Z ⟶ X₁) (z : Z), (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) (ψ z) ∈
          (LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U p →
        gm (ψ ≫ coprod.inl) z _ a =
          gm ψ z _ (w₁.s (fun _ => (p.1 PUnit.unit).1, fun _ => (p.2 PUnit.unit).1))) ∧
      ∀ (Z : Scheme.{0}) (ψ : Z ⟶ X₂) (z : Z), (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) (ψ z) ∈
          (LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U p →
        gm (ψ ≫ coprod.inr) z _ a =
          gm ψ z _ (w₂.s (fun _ => (p.1 PUnit.unit).2, fun _ => (p.2 PUnit.unit).2)) := fun p =>
    exists_glue ((LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U p)
      ((LB.div (M₁.pull p₁) (L₁.pull f₁)).U (fun _ => (p.1 PUnit.unit).1, fun _ => (p.2 PUnit.unit).1))
      ((LB.div (M₂.pull p₂) (L₂.pull f₂)).U (fun _ => (p.1 PUnit.unit).2, fun _ => (p.2 PUnit.unit).2))
      (fun x hx => ⟨(mem_pull_inl M₁ M₂ p₁ p₂ x _).1 hx.1, (mem_pull_inl L₁ L₂ f₁ f₂ x _).1 hx.2⟩)
      (fun x hx => ⟨(mem_pull_inr M₁ M₂ p₁ p₂ x _).1 hx.1, (mem_pull_inr L₁ L₂ f₁ f₂ x _).1 hx.2⟩) _ _
  choose s hs₁ hs₂ using key
  let W : LB.Iso ((join L₁ L₂).pull (coprod.map f₁ f₂)) ((join M₁ M₂).pull (coprod.map p₁ p₂)) := ⟨s⟩
  refine ⟨W, fun i j => unit_ext_coprod (fun x hx => ?_) (fun x hx => ?_), fun Z r z j k hj hk => ?_,
    fun Z r z j k hj hk => ?_⟩
  · have e₁ := hs₁ i X₁ (𝟙 _) x hx.1
    have e₂ := hs₁ j X₁ (𝟙 _) x hx.2
    rw [Category.id_comp] at e₁ e₂
    have m₁ : x ∈ (LB.div (M₁.pull p₁) (L₁.pull f₁)).U
        (fun _ => (i.1 PUnit.unit).1, fun _ => (i.2 PUnit.unit).1) :=
      ⟨(mem_pull_inl M₁ M₂ p₁ p₂ x _).1 hx.1.1, (mem_pull_inl L₁ L₂ f₁ f₂ x _).1 hx.1.2⟩
    have m₂ : x ∈ (LB.div (M₁.pull p₁) (L₁.pull f₁)).U
        (fun _ => (j.1 PUnit.unit).1, fun _ => (j.2 PUnit.unit).1) :=
      ⟨(mem_pull_inl M₁ M₂ p₁ p₂ x _).1 hx.2.1, (mem_pull_inl L₁ L₂ f₁ f₂ x _).1 hx.2.2⟩
    have h := congrArg (gm (𝟙 X₁) x _) (hw₁ (fun _ => (i.1 PUnit.unit).1, fun _ => (i.2 PUnit.unit).1)
      (fun _ => (j.1 PUnit.unit).1, fun _ => (j.2 PUnit.unit).1))
    have m : x ∈ (LB.div (M₁.pull p₁) (L₁.pull f₁)).U (fun _ => (i.1 PUnit.unit).1, fun _ => (i.2 PUnit.unit).1) ⊓
        (LB.div (M₁.pull p₁) (L₁.pull f₁)).U (fun _ => (j.1 PUnit.unit).1, fun _ => (j.2 PUnit.unit).1) := ⟨m₁, m₂⟩
    rw [map_mul, gm_res _ x _ m, gm_res _ x _ m] at h
    rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, gm_div_inl x i j hx.1 hx.2]
    exact e₁.trans (h.trans (congrArg _ e₂.symm))
  · have e₁ := hs₂ i X₂ (𝟙 _) x hx.1
    have e₂ := hs₂ j X₂ (𝟙 _) x hx.2
    rw [Category.id_comp] at e₁ e₂
    have m₁ : x ∈ (LB.div (M₂.pull p₂) (L₂.pull f₂)).U
        (fun _ => (i.1 PUnit.unit).2, fun _ => (i.2 PUnit.unit).2) :=
      ⟨(mem_pull_inr M₁ M₂ p₁ p₂ x _).1 hx.1.1, (mem_pull_inr L₁ L₂ f₁ f₂ x _).1 hx.1.2⟩
    have m₂ : x ∈ (LB.div (M₂.pull p₂) (L₂.pull f₂)).U
        (fun _ => (j.1 PUnit.unit).2, fun _ => (j.2 PUnit.unit).2) :=
      ⟨(mem_pull_inr M₁ M₂ p₁ p₂ x _).1 hx.2.1, (mem_pull_inr L₁ L₂ f₁ f₂ x _).1 hx.2.2⟩
    have h := congrArg (gm (𝟙 X₂) x _) (hw₂ (fun _ => (i.1 PUnit.unit).2, fun _ => (i.2 PUnit.unit).2)
      (fun _ => (j.1 PUnit.unit).2, fun _ => (j.2 PUnit.unit).2))
    have m : x ∈ (LB.div (M₂.pull p₂) (L₂.pull f₂)).U (fun _ => (i.1 PUnit.unit).2, fun _ => (i.2 PUnit.unit).2) ⊓
        (LB.div (M₂.pull p₂) (L₂.pull f₂)).U (fun _ => (j.1 PUnit.unit).2, fun _ => (j.2 PUnit.unit).2) := ⟨m₁, m₂⟩
    rw [map_mul, gm_res _ x _ m, gm_res _ x _ m] at h
    rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, gm_div_inr x i j hx.1 hx.2]
    exact e₁.trans (h.trans (congrArg _ e₂.symm))
  · exact hs₁ (fun _ => j, fun _ => k) Z r z
      ⟨(mem_pull_inl M₁ M₂ p₁ p₂ _ _).2 (mem_pull.2 hj), (mem_pull_inl L₁ L₂ f₁ f₂ _ _).2 (mem_pull.2 hk)⟩
  · exact hs₂ (fun _ => j, fun _ => k) Z r z
      ⟨(mem_pull_inr M₁ M₂ p₁ p₂ _ _).2 (mem_pull.2 hj), (mem_pull_inr L₁ L₂ f₁ f₂ _ _).2 (mem_pull.2 hk)⟩

end Glue

theorem exists_iso_level : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ), ∃ W : LB.Iso ((join U₁.LG.L U₂.LG.L).pull (coprod.map (fstG I e G₁).left (fstG I e G₂).left)) ((JN D₁.toPre D₂.toPre).pull (coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left)), W.IsGen ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₁).left) (z : Z) (j : (JN D₁.toPre D₂.toPre).ι) (k : (join U₁.LG.L U₂.LG.L).ι), (U₁.gt e).pG.left (r z) ∈ D₁.toPre.P.L.U j.1 → (fstG I e G₁).left (r z) ∈ U₁.LG.L.U k.1 → gw W (r ≫ coprod.inl) z j (fun _ => k) = gw (U₁.w e) r z j.1 (fun _ => k.1)) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₂).left) (z : Z) (j : (JN D₁.toPre D₂.toPre).ι) (k : (join U₁.LG.L U₂.LG.L).ι), (U₂.gt e).pG.left (r z) ∈ D₂.toPre.P.L.U j.2 → (fstG I e G₂).left (r z) ∈ U₂.LG.L.U k.2 → gw W (r ≫ coprod.inr) z j (fun _ => k) = gw (U₂.w e) r z j.2 (fun _ => k.2)) := by
  intro R _ _ I D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ e
  exact exists_iso_glue (U₁.w e) (U₂.w e) (U₁.w_gen e) (U₂.w_gen e)

end GlobalTheory.Mum.Two.GlueLevel
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

theorem _root_.GlobalTheory.T.exists_abelianPart_hom_uniformisedGroups : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂), IsMonHom a → ∃ b : D₁.toPre.P.A ⟶ D₂.toPre.P.A, IsMonHom b ∧ Over₀ U₁ U₂ a b := by
  first | exact @GlobalTheory.Mum.Two.exists_abelian_hom | exact GlobalTheory.Mum.Two.exists_abelian_hom | (intros; apply GlobalTheory.Mum.Two.exists_abelian_hom <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

theorem _root_.GlobalTheory.T.uniformisedGroupHom_pullback_maps : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : Unif I D₁ A₁ G₁) (U₂ : Unif I D₂ A₂ G₂) (D₁' D₂' : DegData R' I') (A₁' A₂' : PolAV (Sp (FractionRing R'))) (hD₁ : IsPullDeg φ D₁.toPre D₁'.toPre) (hD₂ : IsPullDeg φ D₂.toPre D₂'.toPre) (U₁' : Unif I' D₁' A₁' ((Over.pullback (specOf φ)).obj G₁)) (U₂' : Unif I' D₂' A₂' ((Over.pullback (specOf φ)).obj G₂)), IsPullUnif φ hD₁ (Iso.refl _) U₁ U₁' → IsPullUnif φ hD₂ (Iso.refl _) U₂ U₂' → ∀ (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), Lin U₁.toUnifPre U₂.toUnifPre a b h → ∃ (b' : D₁'.toPre.P.A ⟶ D₂'.toPre.P.A) (h' : D₂'.toPre.X →+ D₁'.toPre.X), Lin U₁'.toUnifPre U₂'.toUnifPre ((Over.pullback (specOf φ)).map a) b' h' ∧ b' ≫ hD₂.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf φ)).map b ∧ ∀ χ, hD₁.xe (h' χ) = h (hD₂.xe χ) := by
  first | exact @GlobalTheory.Mum.Two.PullLin.linPull | exact GlobalTheory.Mum.Two.PullLin.linPull | (intros; apply GlobalTheory.Mum.Two.PullLin.linPull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

theorem _root_.GlobalTheory.T.cubeBundleIso_uniformisedGroup_genericFibre : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (f g : G₁ ⟶ G₂) (f' g' : G₁ ⟶ G₁) (fA gA : A₁.A ⟶ A₂.A) (fA' gA' : A₁.A ⟶ A₁.A), Gen₀ U₁ U₂ f fA → Gen₀ U₁ U₂ g gA → Gen₀ U₁ U₁ f' fA' → Gen₀ U₁ U₁ g' gA' → LBIso (cubeLB G₂ ![fst G₁ G₁ ≫ f, snd G₁ G₁ ≫ g] U₂.LG.L) (cubeLB G₁ ![fst G₁ G₁ ≫ f', snd G₁ G₁ ≫ g'] U₁.LG.L) → LBIso (cubeLB A₂.A ![fst A₁.A A₁.A ≫ fA, snd A₁.A A₁.A ≫ gA] A₂.L) (cubeLB A₁.A ![fst A₁.A A₁.A ≫ fA', snd A₁.A A₁.A ≫ gA'] A₁.L) := by
  first | exact @GlobalTheory.Mum.Two.lbIso_cubeLB_generic | exact GlobalTheory.Mum.Two.lbIso_cubeLB_generic | (intros; apply GlobalTheory.Mum.Two.lbIso_cubeLB_generic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

theorem _root_.GlobalTheory.T.exists_crossRelation_sections_ample_source_power : ∀ (R : Type) [CommRing R] [IsDomain R] (A₁ A₂ : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (c : A₁.A ⟶ A₂.A), IsMonHom c → ∀ (j k : ℕ), 1 ≤ k → ∃ n, 1 ≤ n ∧ ∀ t₁ t₂ : SecA A₂ F j, ∃ t₁' t₂' : SecA A₁ F (k * n), CrossH c t₁ t₂ t₁' t₂' ∧ ((∀ z J, Good A₂.L z J → sA t₂ (ptSecT A₂.A 1).left z J ≠ 0) → (∀ z J, Good A₁.L z J → sA t₂' (ptSecT A₁.A 1).left z J ≠ 0)) := by
  first | exact @GlobalTheory.Mum.Two.exists_crossH | exact GlobalTheory.Mum.Two.exists_crossH | (intros; apply GlobalTheory.Mum.Two.exists_crossH <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

theorem _root_.GlobalTheory.T.thetaSectionCrossRelation_iff_of_thetaAction : ∀ (R : Type) [CommRing R] [IsDomain R] (A₁ A₂ : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (c : A₁.A ⟶ A₂.A), IsMonHom c → ∀ (j j' : ℕ) (θ : ThetaGrp A₂.A A₂.L (j : ℤ) (TFK (R := R) F)) (θ' : ThetaGrp A₁.A A₁.L (j' : ℤ) (TFK (R := R) F)), θ.pt = θ'.pt ≫ c → ∀ (t₁ t₂ T₁ T₂ : SecA A₂ F j) (t₁' t₂' T₁' T₂' : SecA A₁ F j'), IsActOf A₂.A A₂.L j θ t₁ T₁ → IsActOf A₂.A A₂.L j θ t₂ T₂ → IsActOf A₁.A A₁.L j' θ' t₁' T₁' → IsActOf A₁.A A₁.L j' θ' t₂' T₂' → (CrossH c t₁ t₂ t₁' t₂' ↔ CrossH c T₁ T₂ T₁' T₂') := by
  first | exact @GlobalTheory.crossH_iff_of_isActOf | exact GlobalTheory.crossH_iff_of_isActOf | (intros; apply GlobalTheory.crossH_iff_of_isActOf <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two


theorem _root_.GlobalTheory.T.torusExtensionPointAction_period_value_fractionField : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ D' : DegPre R) (pr : D'.P.A ⟶ D₀.P.A) (h : D₀.X →+ D'.X) (F : Type) [Field F] [Algebra (FractionRing R) F] (y : D'.X) (y₀ : D₀.X) (g : GtPtF D' F) (g' : GtPtF D₀ F), GtPtF.IsIota y g → GtPtF.IsIota y₀ g' → Act D' D₀ pr h g g' → ∀ (χ : D₀.X) (u : LB.Gen (CmpLB D' D₀ pr (h χ) χ)), Nrm u → ∀ (z : (TK R).left) (J : ((TK R).left ⟶ (D'.P.A.left ⨿ D₀.P.A.left : Scheme.{0})) → (JN D' D₀).ι), Good (JN D' D₀) z J → val (D₀.tau y₀ χ) (𝟙 _) z (rr J) = val (D'.tau y (h χ)) (𝟙 _) z (rl J) * val u (ptK (D'.c y)) z J := by
  first | exact @GlobalTheory.Mum.Two.act_val_frac | exact GlobalTheory.Mum.Two.act_val_frac | (intros; apply GlobalTheory.Mum.Two.act_val_frac <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

theorem _root_.GlobalTheory.T.torusExtensionMap_welldefined_additive_characters : ∀ (R : Type) [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (b : D₁.P.A ⟶ D₂.P.A) (h : D₂.X →+ D₁.X), IsMonHom b → (∀ χ, ∃ u : LB.Gen (CmpLB D₁ D₂ b (h χ) χ), Nrm u) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], (∀ g : GtPtF D₁ F, ∃! g' : GtPtF D₂ F, Act D₁ D₂ b h g g') ∧ (∀ (g₁ g₂ g₃ : GtPtF D₁ F) (g₁' g₂' g₃' : GtPtF D₂ F), g₁.IsAdd g₂ g₃ → Act D₁ D₂ b h g₁ g₁' → Act D₁ D₂ b h g₂ g₂' → Act D₁ D₂ b h g₃ g₃' → g₁'.IsAdd g₂' g₃') ∧ ∀ (t : Multiplicative D₁.X →* Fˣ) (g : GtPtF D₁ F) (g' : GtPtF D₂ F), IsTor t g → Act D₁ D₂ b h g g' → IsTor (t.comp (AddMonoidHom.toMultiplicative h)) g' := by
  first | exact @GlobalTheory.Mum.Two.act_two_hom | exact GlobalTheory.Mum.Two.act_two_hom | (intros; apply GlobalTheory.Mum.Two.act_two_hom <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

theorem _root_.GlobalTheory.T.torusExtensionPointAction_pullback_data : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D₁ D₂ : DegPre R) (D₁' D₂' : DegPre R') (hD₁ : IsPullDeg φ D₁ D₁') (hD₂ : IsPullDeg φ D₂ D₂') (b : D₁.P.A ⟶ D₂.P.A) (h : D₂.X →+ D₁.X) (b' : D₁'.P.A ⟶ D₂'.P.A) (h' : D₂'.X →+ D₁'.X), IsMonHom b → IsMonHom b' → b' ≫ hD₂.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf φ)).map b → (∀ χ, hD₁.xe (h' χ) = h (hD₂.xe χ)) → (∀ χ, ∃ u : LB.Gen (CmpLB D₁ D₂ b (h χ) χ), Nrm u) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (g₁ : GtPtF D₁ F) (g₂ : GtPtF D₂ F) (g₁' : GtPtF D₁' F) (g₂' : GtPtF D₂' F), IsPullGtF φ hD₁ F g₁ g₁' → IsPullGtF φ hD₂ F g₂ g₂' → (Act D₁ D₂ b h g₁ g₂ ↔ Act D₁' D₂' b' h' g₁' g₂') := by
  first | exact @GlobalTheory.Mum.Two.ActPull.main | exact GlobalTheory.Mum.Two.ActPull.main | (intros; apply GlobalTheory.Mum.Two.ActPull.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange GlobalTheory.Mum.Two.Mix
namespace GlobalTheory.Mum.Two.Mix
open GlobalTheory.UT.MixedConv

theorem val_mixed_eval : ∀ (R : Type) [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (b : D₁.P.A ⟶ D₂.P.A) (h : D₂.X →+ D₁.X) (g : GtPtF D₁ F) (g' : GtPtF D₂ F), Act D₁ D₂ b h g g' → ∀ (j j' : ℕ) (w : Frm D₂ F j g'.b) (w' : Frm D₁ F j' g.b) (χ : D₂.X) (δ : D₁.X) (u : LB.Gen (CmpLB D₁ D₂ b (h χ) χ)), Nrm u → ∀ (f : D₂.SecB j χ) (f' : D₁.SecB j' δ) (y y' : F), MixedConv.IsCoefB j g' w χ f y → MixedConv.IsCoefB j' g w' δ f' y' → ∀ (z : (TF (R := R) F).left) (J), Good (JN D₁ D₂) z J → sval f (g.b.left ≫ b.left) z (rr J) * sval f' g.b.left z (rl J) * (val u g.b.left z J * val (MixedConv.cubB D₁ (h χ) δ) g.b.left z (rl J)).val = cst F z (y * y') * (rigV D₂ (TF (R := R) F).hom z (rr J) ^ j * rigV D₁ (TF (R := R) F).hom z (rl J) ^ j' * (val (g.s (h χ + δ)) (𝟙 _) z (rl J) * (val w (𝟙 _) z (rr J) * val w' (𝟙 _) z (rl J)))⁻¹).val := by
  intro R _ _ D₁ D₂ F _ _ b h g g' hg j j' w w' χ δ u hu f f' y y' hy hy' z J hJ
  have h₁ : Good D₁.P.L z (rl J) := (isPart_inl D₁.P.L D₂.P.L).good hJ
  have h₂ : Good D₂.P.L z (rr J) := (isPart_inr D₁.P.L D₂.P.L).good hJ
  have c₂ : val (MixedConv.cubB D₁ (h χ) δ) g.b.left z (rl J) =
      th D₁ z (rl J) (cP D₁ _ (h χ)) (cP D₁ _ δ) g.b := by
    refine (val_cub D₁.cub g.b h₁ _ _ _).trans ?_
    rw [comp_cP, comp_cP, Category.comp_id]
  have c₃ := gt_mul (𝟙 (TF (R := R) F)) h₁ g (h χ) δ
  have c₄ := hy z (rr J) h₂
  have c₅ := hy' z (rl J) h₁
  have c₆ : g.b.left ≫ b.left = g'.b.left := (congrArg (fun q => q.left) hg.1).symm
  have c₉ := hg.2 χ u hu z J hJ
  rw [Category.id_comp, Over.id_left] at c₃
  rw [c₉, CoefBasic.cst_eq] at c₄
  rw [CoefBasic.cst_eq] at c₅
  rw [c₂, c₆, CoefBasic.cst_eq, map_mul, eq_comm, Units.val_mul, ← _root_.mul_assoc, Units.mul_inv_eq_iff_eq_mul]
  have c₇ := congrArg Units.val c₃
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at c₄ c₅ c₇ ⊢
  have c₈ := congrArg₂ (· * ·) c₄ c₅
  linear_combination c₈ - sval f (Over.Hom.left g'.b) z (rr J) * sval f' g.b.left z (rl J) * (val u g.b.left z J).val *
    (val w (𝟙 _) z (rr J)).val * (val w' (𝟙 _) z (rl J)).val * c₇

end GlobalTheory.Mum.Two.Mix
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange

theorem _root_.GlobalTheory.T.carriedSections_crossRelation_of_hom : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A), Gen₀ U₁ U₂ a c → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (w₁ : W0 U₁) (w₂ : W0 U₂), w₁.IsGen → w₂.IsGen → ∀ (j j' : ℕ) (t₁ t₂ : SecA A₂ F j) (t₁' t₂' : SecA A₁ F j') (σ₁ σ₂ : U₂.SecGF F j) (σ₁' σ₂' : U₁.SecGF F j'), MixedConv.Carried w₂ j t₁ σ₁ → MixedConv.Carried w₂ j t₂ σ₂ → MixedConv.Carried w₁ j' t₁' σ₁' → MixedConv.Carried w₁ j' t₂' σ₂' → CrossH c t₁ t₂ t₁' t₂' → ∀ (y : (UnifPre.GF (G := G₁) F).left) (J₁ J₂), Good U₁.LG.L y J₁ → Good U₂.LG.L y J₂ → sval σ₁ (TFK (R := R) F ◁ (Over.pullback (jK R)).map a).left y J₂ * sval σ₂' (𝟙 _) y J₁ = sval σ₂ (TFK (R := R) F ◁ (Over.pullback (jK R)).map a).left y J₂ * sval σ₁' (𝟙 _) y J₁ := by
  first | exact @GlobalTheory.Mum.Two.carried_cross_of_hom | exact GlobalTheory.Mum.Two.carried_cross_of_hom | (intros; apply GlobalTheory.Mum.Two.carried_cross_of_hom <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR


theorem _root_.GlobalTheory.T.section_value_integral_point_congruent_term_sum : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (h : 𝟙_ (Over (Sp R)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U h g → ∀ (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1))) (t : LB.Gen (LB.LinComb D.toPre.P.L ![(η[D.toPre.P.A]).left, g.b.left] (DegPre.lineε 1))) (e k : ℕ), GlobalTheory.Poinc.IntEval.TRel U h g.b f t e → ∀ (σ : H0 U.LG.L k) (fs : ∀ α : D.toPre.X, D.toPre.SecB k α), U.ExpandsAt e k σ fs → ∀ x : R, (∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι), Good U.LG.L z J → sval σ (r ≫ h.left) z J = Geo.Tor.cst r z x * (val f r z J ^ k).val) → ∀ a : D.toPre.X → R, (∀ (α : D.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L z J → sval (fs α) (r ≫ g.b.left) z J * (val (g.s α) r z J).val * (val t r z J ^ k).val = Geo.Tor.cst r z (a α) * (val (L := D.toPre.P.L) D.toPre.rig r z J ^ k).val) → ∃ S : Finset D.toPre.X, ∀ T : Finset D.toPre.X, S ⊆ T → x - ∑ α ∈ T, a α ∈ I ^ (e + 1) := by
  first | exact @GlobalTheory.Poinc.IntEval.value_sub_sum_mem_hRed | exact GlobalTheory.Poinc.IntEval.value_sub_sum_mem_hRed | (intros; apply GlobalTheory.Poinc.IntEval.value_sub_sum_mem_hRed <;> assumption)
end
