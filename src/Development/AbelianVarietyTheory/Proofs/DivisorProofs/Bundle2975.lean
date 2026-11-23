module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle925
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2849
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2895
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2850
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantFieldConstCoeffs
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2851
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2864
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2847
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle002
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2729
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.exists_harrisTaylorObject_over_lieTate_locus : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∀ (X : Scheme.{0}) (πX : X ⟶ S) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (φX : AX.left ⟶ c.A.left) (φ₂X : (G2 AX).left ⟶ (G2 c.A).left) (actX : OActN D.O AX) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)), IsGrpPullback AX c.A πX φX → IsSquare φX φ₂X → RosatiFor D actX (c.P.pull φ₂X) → EtaOK D N actX ηX → ∀ (Z : Scheme.{0}) (j : Z ⟶ X), (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Z), x ≫ j ≫ πX ≫ t = spMap β → LieHer b actX β (x ≫ j)) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Z) (β : R →+* k), x ≫ j ≫ πX ≫ t = spMap β → GeomAt D N actX (c.P.pull φ₂X) ηX k (x ≫ j)) → ∃ (u : Obj b N ((j ≫ πX) ≫ t)) (ψ : u.A.left ⟶ AX.left) (ψ₂ : (G2 u.A).left ⟶ (G2 c.A).left), IsGrpPullback u.A AX j ψ ∧ IsSquare (ψ ≫ φX) ψ₂ ∧ LBIso u.P (c.P.pull ψ₂) ∧ (∀ a : D.O, (u.act.act a).left ≫ ψ = ψ ≫ (actX.act a).left) ∧ ∀ y, (u.eta y).left ≫ ψ = j ≫ (ηX y).left := by
  first | (exact @GlobalTheory.HTMkObj.exists_obj_of_locus) | (exact GlobalTheory.HTMkObj.exists_obj_of_locus) | (intros; apply GlobalTheory.HTMkObj.exists_obj_of_locus <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two


theorem _root_.GlobalTheory.T.exists_lineBundleIso_pullback_of_coprodJoin : ∀ {X₁ X₂ : Scheme.{0}} (M : LB X₁) (M' : LB X₂), M.IsLB → M'.IsLB → Nonempty X₁ → Nonempty X₂ → ∀ (F : X₂ ⟶ X₁) (t : LB.Gen (LB.LinComb (join M' M) (Sum.elim (fun _ : PUnit => F ≫ coprod.inr) (fun _ : PUnit => coprod.inl)) (Sum.elim (fun _ => (1 : ℤ)) (fun _ => (-1 : ℤ))))), t.IsGen → ∃ w : LB.Iso M' (M.pull F), w.IsGen ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ X₂) (z : Z) (J : (Z ⟶ X₂ ⨿ X₁) → (join M' M).ι), Good (join M' M) z J → gw w f z (rr J (f ≫ F)) (rl J f) = val t f z J := by
  first | exact @GlobalTheory.JoinPull.exists_iso_of_joinGen | exact GlobalTheory.JoinPull.exists_iso_of_joinGen | (intros; apply GlobalTheory.JoinPull.exists_iso_of_joinGen <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.IsoPullIdComp

theorem exists_comp_val : ∀ {Y X₀ X : Scheme.{0}} {A : LB Y} {L₀ : LB X₀} {M : LB X} {K₀ K : Type} [Fintype K₀] [Fintype K] (φ₀ : K₀ → (Y ⟶ X₀)) (ε₀ : K₀ → ℤ) (φ : K → (Y ⟶ X)) (ε : K → ℤ), A.IsLB → L₀.IsLB → M.IsLB → ∀ (u : LB.Iso A (LB.LinComb L₀ φ₀ ε₀)), u.IsGen → ∀ (v : LB.Iso (LB.LinComb L₀ φ₀ ε₀) ((LB.LinComb M φ ε).pull (𝟙 Y))), v.IsGen → ∃ w : LB.Iso A (LB.LinComb M φ ε), w.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → M.ι) (J₀ : (Z ⟶ X₀) → L₀.ι) (a : A.ι), q z ∈ A.U a → Good M z J → Good L₀ z J₀ → gm q z _ (w.s (fun k => J (q ≫ φ k), a)) = gm q z _ (u.s (fun k => J₀ (q ≫ φ₀ k), a)) * GlobalTheory.Mum.Two.isoVal v q z J J₀ := by
  intro Y X₀ X A L₀ M K₀ K _ _ φ₀ ε₀ φ ε hA hL₀ hM u hu v hv
  have eu := GlobalTheory.LinCombComp.gm_iso_linComb φ₀ ε₀ u hu
  have ev : ∀ (y : Y) (j j' : K → M.ι) (j₀ j₀' : K₀ → L₀.ι), y ∈ LB.wchart M φ j → y ∈ LB.wchart L₀ φ₀ j₀ →
      y ∈ LB.wchart M φ j' → y ∈ LB.wchart L₀ φ₀ j₀' →
      gm (𝟙 Y) y ((LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j, j₀))
          (v.s (fun _ => j, j₀)) =
        (trF φ ε (𝟙 Y) y j j' * (trF φ₀ ε₀ (𝟙 Y) y j₀ j₀')⁻¹) *
          gm (𝟙 Y) y ((LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j', j₀'))
            (v.s (fun _ => j', j₀')) := by
    intro y j j' j₀ j₀' h h0 h' h0'
    have hp : (𝟙 Y : Y ⟶ Y) y ∈
        (LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j, j₀) := ⟨mem_pull.2 h, h0⟩
    have hq : (𝟙 Y : Y ⟶ Y) y ∈
        (LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j', j₀') := ⟨mem_pull.2 h', h0'⟩
    have e1 := GlobalTheory.LinCombComp.gm_gen hv (𝟙 Y) y hp hq
    rw [GlobalTheory.Mum.Two.gm_div_pull (𝟙 Y) y _ _ hp hq, Category.comp_id] at e1
    exact e1
  have glue : ∀ (j : K → M.ι) (a : A.ι), ∃ s : Γ(Y, LB.wchart M φ j ⊓ A.U a)ˣ,
      ∀ (Z' : Scheme.{0}) (q : Z' ⟶ Y) (z : Z') (j₀ : K₀ → L₀.ι), q z ∈ LB.wchart M φ j → q z ∈ A.U a →
        q z ∈ LB.wchart L₀ φ₀ j₀ →
        gm q z (LB.wchart M φ j ⊓ A.U a) s =
          gm q z ((LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j, j₀))
              (v.s (fun _ => j, j₀)) *
            gm q z (LB.wchart L₀ φ₀ j₀ ⊓ A.U a) (u.s (j₀, a)) := by
    intro j a
    obtain ⟨W, hW⟩ : ∃ W : (K₀ → L₀.ι) → Y.Opens, ∀ j₀, W j₀ = LB.wchart M φ j ⊓ A.U a ⊓ LB.wchart L₀ φ₀ j₀ :=
      ⟨_, fun _ => rfl⟩
    have memW : ∀ y j₀, y ∈ W j₀ ↔ (y ∈ LB.wchart M φ j ∧ y ∈ A.U a) ∧ y ∈ LB.wchart L₀ φ₀ j₀ := fun y j₀ => by
      rw [hW]; exact Iff.rfl
    have l₀ : ∀ j₀, W j₀ ≤ LB.wchart M φ j ⊓ A.U a := fun j₀ y hy => ((memW y j₀).1 hy).1
    have l₁ : ∀ j₀, W j₀ ≤ (LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j, j₀) :=
      fun j₀ y hy => ⟨mem_pull.2 ((memW y j₀).1 hy).1.1, ((memW y j₀).1 hy).2⟩
    have l₂ : ∀ j₀, W j₀ ≤ LB.wchart L₀ φ₀ j₀ ⊓ A.U a := fun j₀ y hy =>
      ⟨((memW y j₀).1 hy).2, ((memW y j₀).1 hy).1.2⟩
    obtain ⟨uu, hu'⟩ : ∃ uu : ∀ j₀, Γ(Y, W j₀)ˣ, ∀ (Z' : Scheme.{0}) (q : Z' ⟶ Y) (z : Z') (j₀ : K₀ → L₀.ι),
        q z ∈ W j₀ → gm q z (W j₀) (uu j₀) =
          gm q z ((LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j, j₀))
              (v.s (fun _ => j, j₀)) *
            gm q z (LB.wchart L₀ φ₀ j₀ ⊓ A.U a) (u.s (j₀, a)) :=
      ⟨fun j₀ => res (l₁ j₀) (v.s (fun _ => j, j₀)) * res (l₂ j₀) (u.s (j₀, a)), fun Z' q z j₀ h =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res q z (l₁ j₀) h _) (gm_res q z (l₂ j₀) h _))⟩
    obtain ⟨s, hs⟩ := glue_unit (LB.wchart M φ j ⊓ A.U a) W l₀ (fun y hy => by
        choose j₀ hj₀ using fun k => exists_chart hL₀ (φ₀ k y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨j₀, (memW y j₀).2 ⟨hy, Set.mem_iInter.2 hj₀⟩⟩) uu
      (fun j₀ j₀' y hy => by
        obtain ⟨⟨h1, ha⟩, h0⟩ := (memW y j₀).1 hy.1
        obtain ⟨-, h0'⟩ := (memW y j₀').1 hy.2
        refine (hu' Y (𝟙 Y) y j₀ hy.1).trans (Eq.trans ?_ (hu' Y (𝟙 Y) y j₀' hy.2).symm)
        rw [ev y j j j₀ j₀' h1 h0 h1 h0', eu y j₀ j₀' a a h0 ha h0' ha,
          GlobalTheory.LinCombComp.trF_self hM φ ε (𝟙 Y) y j h1, gm_self hA (𝟙 Y) y ha]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_one]
        abel)
    refine ⟨s, fun Z' q z j₀ h1 ha h0 => ?_⟩
    have hy : q z ∈ W j₀ := (memW _ j₀).2 ⟨⟨h1, ha⟩, h0⟩
    exact (gm_res q z (l₀ j₀) hy s).symm.trans ((congrArg (gm q z (W j₀)) (hs j₀)).trans (hu' Z' q z j₀ hy))
  choose s hs using glue
  refine ⟨⟨fun p => s p.1 p.2⟩, fun p p' => unit_ext fun y hy => ?_, fun Z q z J J₀ a ha hJ hJ₀ => ?_⟩
  · obtain ⟨⟨h1, ha⟩, h1', ha'⟩ := hy
    choose j₀ hj₀ using fun k => exists_chart hL₀ (φ₀ k y)
    have h0 : y ∈ LB.wchart L₀ φ₀ j₀ := Set.mem_iInter.2 hj₀
    have key : gm (𝟙 Y) y (LB.wchart M φ p.1 ⊓ A.U p.2) (s p.1 p.2) =
        (trF φ ε (𝟙 Y) y p.1 p'.1 * (gm (𝟙 Y) y (A.U p.2 ⊓ A.U p'.2) (A.g p.2 p'.2))⁻¹) *
          gm (𝟙 Y) y (LB.wchart M φ p'.1 ⊓ A.U p'.2) (s p'.1 p'.2) := by
      rw [hs p.1 p.2 Y (𝟙 Y) y j₀ h1 ha h0, hs p'.1 p'.2 Y (𝟙 Y) y j₀ h1' ha' h0,
        ev y p.1 p'.1 j₀ j₀ h1 h0 h1' h0, eu y j₀ j₀ p.2 p'.2 h0 ha h0 ha',
        GlobalTheory.LinCombComp.trF_self hL₀ φ₀ ε₀ (𝟙 Y) y j₀ h0]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel
    have hm : y ∈ (LB.div (LB.LinComb M φ ε) A).U p ⊓ (LB.div (LB.LinComb M φ ε) A).U p' :=
      ⟨⟨h1, ha⟩, h1', ha'⟩
    have ed := (GlobalTheory.LinCombComp.gm_div _ _ (𝟙 Y) y p p' hm.1 hm.2).trans
      (congrArg (· * _) (gm_linComb M φ ε (𝟙 Y) y p.1 p'.1 h1 h1'))
    exact (gm_res _ y _ hm _).trans (key.trans ((congrArg₂ (· * ·) ed.symm (gm_res _ y _ hm _).symm).trans
      (map_mul _ _ _).symm))
  · refine (hs _ a Z q z (fun k => J₀ (q ≫ φ₀ k)) (hJ.mem φ q) ha (hJ₀.mem φ₀ q)).trans
      ((mul_comm _ _).trans (congrArg _ ?_))
    have e : ∀ b b', b = b' → gm q z _ (v.s b) = gm q z _ (v.s b') := by rintro _ _ rfl; rfl
    exact e _ _ (Prod.ext (funext fun _ => funext fun k => by simp only [Category.id_comp]) rfl)

end GlobalTheory.IsoPullIdComp
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange

theorem _root_.GlobalTheory.T.sectionValue_eq_zero_weightIndependence_level : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (Y : Over (Spec (CommRingCat.of R))) (p : Y ⟶ D.P.A) (X : Scheme.{0}) (N : LB X), N.IsLB → ∀ (ι₀ : D.P.A.left ⟶ X) (π : N.ι → D.P.L.ι), IsPart N D.P.L ι₀ π → ∀ (K : Type) [Fintype K] (φ : D.X → K → (Y.left ⟶ X)) (ε : K → ℤ) (d : ∀ α, LB.Sec (LB.LinComb N (φ α) ε)) (s : Finset D.X), (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left → ∀ (z : Z) (J), Good N z J → ∑ α ∈ s, sval (d α) r z J * (val (g.t α) x z (rs ι₀ π J)).val = 0) → ∀ α ∈ s, ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left → ∀ (z : Z) (J), Good N z J → sval (d α) r z J = 0 := by
  first | exact @GlobalTheory.sval_eq_zero_of_sum_mul_coord_part | exact GlobalTheory.sval_eq_zero_of_sum_mul_coord_part | (intros; apply GlobalTheory.sval_eq_zero_of_sum_mul_coord_part <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn
open GlobalTheory.HeatConn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatConn.LogDerDesc

theorem exists_app_mul_eq_dE : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) (ν : R), (∀ a (α : Q.X) (V : Y.H.left.Opens) f, IsWt Y α V f → IsWt Y α V (dd a V f)) → IsBasic Y h → ∀ (i : h.J) (α : Q.X) (U : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ U ≤ h.W i → ∀ x : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U), IsUnit x → IsWt Y α _ x → ∃ A : Γ(Q.P.A.left, U), (Y.q.left.app U).hom A * x = dE h ν i _ x := by
  intro R _ _ Q O _ _ _ oa Y n dd D h ν hdd hB i α U hU x hx hxw

  have h1 : IsWt Y α _ (dE h ν i _ x) := by
    unfold dE
    refine WtAlg.isWt_add ((hB i).2.2.2 α U hU x hxw) (WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (WtAlg.isWt_constFn _ _) ?_)
    exact WtAlg.isWt_sum _ _ fun a _ => WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (WtAlg.isWt_constFn _ _) (hdd a α _ x hxw)

  have h2 : IsWt Y 0 _ (dE h ν i _ x * ((hx.unit⁻¹ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U)ˣ) : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U))) := by
    intro S _ φ y y' c a a' ha ha' hV hV' hq hc
    have one : ∀ (b : Sp S ⟶ Y.H.left) (hb : ⊤ ≤ b ⁻¹ᵁ (Y.q.left ⁻¹ᵁ U)),
        valR b _ x * valR b _ ((hx.unit⁻¹ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U)ˣ) : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U)) = 1 := by
      intro b hb
      rw [← WtAlg.valR_mul'' _ _ hb, IsUnit.mul_val_inv, WtAlg.valR_eq' _ _ hb, map_one, map_one]
    have e1 := h1 S φ y y' c a a' ha ha' hV hV' hq hc
    have ex := hxw S φ y y' c a a' ha ha' hV hV' hq hc
    have o := one a hV
    have o' := one a' hV'
    rw [WtAlg.valR_mul'' _ _ hV', WtAlg.valR_mul'' _ _ hV, e1, WtAlg.c_zero y y' c hc, Units.val_one, _root_.one_mul]
    rw [ex] at o'
    linear_combination (-((c α : S)) * valR a _ (dE h ν i _ x) * valR a' _ ((hx.unit⁻¹ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U)ˣ) : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U))) * o
      + (valR a _ (dE h ν i _ x) * valR a _ ((hx.unit⁻¹ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U)ˣ) : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U))) * o'

  obtain ⟨A, hA⟩ := AbConst.exists_app_eq Y h2
  refine ⟨A, ?_⟩
  rw [hA, _root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]

end GlobalTheory.HeatConn.LogDerDesc
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn

set_option autoImplicit false

namespace GlobalTheory.HeatConn.CoordWt

theorem isWt_xc : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (α : Q.X) (t : Fin 4 → Q.P.L.ι) (W : Y.H.left.Opens), W ≤ xU Y α t → IsWt Y α W (rsT (xc Y α t).val W) := by
  intro R _ _ Q O _ _ _ oa Y α t W hW
  intro S _ φ x x' c a a' ha ha' hV₁ hV₂ hq hc
  subst ha ha'
  have germ : ∀ (b : Sp S ⟶ Y.H.left), ⊤ ≤ b ⁻¹ᵁ W → ∀ z,
      gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (valR b W (rsT (xc Y α t).val W))) =
        gs b z (xU Y α t) (xc Y α t).val := by
    intro b hb z
    rw [valR, dite_eq_left hb, Iso.hom_inv_id_apply, rsT, dite_eq_left hW]
    refine (gs_res (𝟙 _) z hb trivial _).trans ((gs_pull (𝟙 _) b z W (hb trivial) _).trans ?_)
    rw [Category.id_comp]
    exact gs_res b z hW (hb trivial) _
  have key : ∀ (xx : Over.mk (spMap φ) ⟶ Y.H), ⊤ ≤ xx.left ⁻¹ᵁ W → ∀ z J, Good Q.P.L z J →
      gs xx.left z (xU Y α t) (xc Y α t).val =
        (trF (DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α) DegPre.gtε xx.left z (fun k => t (![1, 2, 0, 3] k))
          (fun k => J (xx.left ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k))).val *
        (val ((Y.Φ _ xx).s α) (𝟙 _) z J).val := by
    intro xx hb z J hJ
    have hp := ((GlobalTheory.TorusModel.isPull_iff xx _ _).1 (Y.rep.1 _ _ xx (𝟙 _))).2 α z J hJ
    rw [Category.comp_id] at hp
    have hmem : xx.left z ∈ xU Y α t := hW (hb trivial)
    rw [gs_unit xx.left z _ hmem, gen_trans ((Y.Φ Y.H (𝟙 _)).isGen α) xx.left z hmem (hJ.mem _ xx.left), Units.val_mul]
    congr 1
    exact congrArg Units.val hp.symm
  have hqq : x'.left ≫ Y.q.left = x.left ≫ Y.q.left := congrArg CommaMorphism.left hq
  have hφ : ∀ k, x'.left ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k = x.left ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k :=
    fun k => by rw [gtφT_eq, ← Category.assoc, hqq, Category.assoc]
  have htr : ∀ z (J : (Sp S ⟶ Q.P.A.left) → Q.P.L.ι),
      trF (DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α) DegPre.gtε x'.left z (fun k => t (![1, 2, 0, 3] k))
          (fun k => J (x'.left ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k)) =
        trF (DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α) DegPre.gtε x.left z (fun k => t (![1, 2, 0, 3] k))
          (fun k => J (x.left ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k)) := by
    intro z J
    unfold trF
    refine Finset.prod_congr rfl fun k _ => ?_
    beta_reduce
    rw [hφ k]
  apply (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.symm.injective
  refine fn_ext fun z _ => ?_
  obtain ⟨J, hJ, -⟩ := exists_good Q.P.L Q.P.isLB z (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun a _ _ => a.elim) (fun k => k.elim)
  show gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom _) =
    gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom _)
  rw [map_mul, gs_mul (𝟙 _) z ⊤ trivial, germ _ hV₂ z, germ _ hV₁ z, key x' hV₂ z J hJ, key x hV₁ z J hJ, htr,
    hc α z J hJ, show (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (c α : S) = (unitOn (c α)).val from rfl,
    gs_unit (𝟙 _) z ⊤ trivial, Units.val_mul]
  exact _root_.mul_left_comm _ _ _

end GlobalTheory.HeatConn.CoordWt
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatMod.TorField

open TrivSqZeroExt (inl inr)
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (coord coord_comp)

theorem exists_torTan_of_q : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (p : epsR R ⟶ Y.H), IsTangent p → p ≫ Y.q = 1 → ∃ ℓ : Q.X →+ R, p = GlobalTheory.HeatMod.TorField.torTan ℓ ≫ Y.i := by
  intro R _ _ Q O _ _ _ oa Y p hp hq
  have hmono : ∀ {T : Over (Sp R)} (a b : T ⟶ splitTorus (Sp R) (RayEv.Chr Q)), a ≫ Y.i = b ≫ Y.i → a = b :=
    fun a b h => Y.isKernel.hom_ext h (toUnit_unique _ _)
  have hw : p ≫ Y.q = toUnit _ ≫ η[Q.P.A] := by rw [hq, Hom.one_def]
  let t := Y.isKernel.lift p (toUnit _) hw
  have ht : t ≫ Y.i = p := Y.isKernel.lift_fst _ _ _
  have := Y.i_linear.isMonHom
  have htan : Chart.spMap (Chart.fstD R) ≫ t = 1 := hmono _ _ (by
    rw [Category.assoc, ht, MonObj.one_comp]; exact (Chart.isTan_iff p).2 hp)
  let a : RayEv.Chr Q → DualNumber R := fun χ =>
    (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).hom.hom ((coord t).hom (AddMonoidAlgebra.single χ 1))
  have hfst : ∀ χ, (a χ).fst = 1 := fun χ => by
    have e := congrArg (fun f => (coord f).hom (AddMonoidAlgebra.single χ 1)) htan
    simp only at e
    rw [coord_comp, Diag.coord_one, CommRingCat.hom_comp, RingHom.comp_apply, Chart.spMap_left] at e
    have nat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Chart.fstD R).toRingHom)
    have k := congrArg (fun f => f.hom ((coord t).hom (AddMonoidAlgebra.single χ 1))) nat
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at k
    rw [e, map_one] at k
    exact k.symm
  have h0 : a 0 = 1 := by
    show (Scheme.ΓSpecIso _).hom.hom ((coord t).hom (AddMonoidAlgebra.single 0 1)) = 1
    rw [Diag.coord_single_zero, map_one]
  have hadd : ∀ x y, a (x + y) = a x * a y := fun x y => by
    show (Scheme.ΓSpecIso _).hom.hom ((coord t).hom (AddMonoidAlgebra.single (x + y) 1)) = _
    rw [Diag.coord_single_add, map_mul]
  have hform : ∀ χ, a χ = 1 + inr (a χ).snd := fun χ => by
    ext
    · rw [hfst χ]; simp
    · simp
  let ℓ : Q.X →+ R :=
    { toFun := fun χ => (a χ).snd
      map_zero' := (congrArg TrivSqZeroExt.snd h0).trans TrivSqZeroExt.snd_one
      map_add' := fun x y => (congrArg TrivSqZeroExt.snd (hadd x y)).trans (by
        rw [hform x, hform y]
        simp only [mul_add, add_mul, _root_.one_mul, _root_.mul_one, TrivSqZeroExt.inr_mul_inr, add_zero,
          TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_one, TrivSqZeroExt.snd_inr, zero_add]) }
  refine ⟨ℓ, ?_⟩
  rw [← ht]
  refine congrArg (· ≫ Y.i) (Diag.hom_ext fun χ => ?_)
  rw [torTan, Diag.coord_ofChar]
  show _ = (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + inr (a χ).snd)
  rw [← hform χ]
  show _ = (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).hom.hom ((coord t).hom (AddMonoidAlgebra.single χ 1)))
  rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]

end GlobalTheory.HeatMod.TorField
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8


theorem _root_.GlobalTheory.T.exists_trait_spreading_torusPart_of_specialisation : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (G : Over Y) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ w w' : Y, w ⤳ w' → w ≠ w' → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (ξ : Sp V ⟶ Y) (G₁ : Over (Sp V)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (φ₁ : G₁.left ⟶ G.left) (X₁ : Type) (_ : AddCommGroup X₁) (_ : Module.Free ℤ X₁) (_ : Module.Finite ℤ X₁) (j : splitTorus (Sp V) X₁ ⟶ G₁) (GK : Over (Sp (FractionRing V))) (_ : GrpObj GK) (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap (algebraMap V (FractionRing V))) ψ), ξ (closedPoint V) = w' ∧ (spMap (algebraMap V (FractionRing V)) ≫ ξ) (closedPoint (FractionRing V)) = w ∧ IsGrpPullback G₁ G ξ φ₁ ∧ IsMonHom j ∧ IsTorPart (pullTorus hψ j) := by
  first | exact @GlobalTheory.Poinc.FibLat.exists_trait_torusPart | exact GlobalTheory.Poinc.FibLat.exists_trait_torusPart | (intros; apply GlobalTheory.Poinc.FibLat.exists_trait_torusPart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8


theorem _root_.GlobalTheory.T.torusCompat_of_compat_closedPoint : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → ζ ^ L = 1 → IsUnit (L : o) → (∀ e, IsMonHom (f e)) → (∀ t, gγ t ^ L = 1) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (m : I → X →+ X) (c : T → X →+ ZMod L) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ξ : Sp V ⟶ M.Z) (a : o →+* V) (G₁ : Over (Sp V)) [GrpObj G₁] (φ₁ : G₁.left ⟶ G.left), IsGrpPullback G₁ G ξ φ₁ → ∀ (j : splitTorus (Sp V) X ⟶ G₁), IsMonHom j → (∀ t, ExtNear (gγ t) (ξ (closedPoint V))) → ∀ (GK : Over (Sp (FractionRing V))) [GrpObj GK] (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap (algebraMap V (FractionRing V))) ψ), IsTorPart (pullTorus hψ j) → ∀ (κ : Type) [Field κ] (b : V →+* κ), IsLocalHom b → ∀ (G₀ : Over (Sp κ)) [GrpObj G₀] (ψ₀ : G₀.left ⟶ G₁.left) (hψ₀ : IsGrpPullback G₀ G₁ (spMap b) ψ₀), IsTorPart (pullTorus hψ₀ j) → Compat f gγ ζ L m c (spMap b ≫ ξ) (b.comp a) (ψ₀ ≫ φ₁) (pullTorus hψ₀ j) → Compat f gγ ζ L m c ξ a φ₁ j := by
  first | exact @GlobalTheory.Poinc.FibLat.ClosedLift.compat_of_closed | exact GlobalTheory.Poinc.FibLat.ClosedLift.compat_of_closed | (intros; apply GlobalTheory.Poinc.FibLat.ClosedLift.compat_of_closed <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8


theorem _root_.GlobalTheory.T.torusCompat_of_compat_over_field : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → ζ ^ L = 1 → ∀ (X : Type) [AddCommGroup X] (m : I → X →+ X) (c : T → X →+ ZMod L) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ξ : Sp V ⟶ M.Z) (a : o →+* V) (G₁ : Over (Sp V)) [GrpObj G₁] (φ₁ : G₁.left ⟶ G.left), IsGrpPullback G₁ G ξ φ₁ → ∀ (j : splitTorus (Sp V) X ⟶ G₁), (∀ t, ExtNear (gγ t) (ξ (closedPoint V))) → ∀ (K : Type) [Field K] (b : V →+* K), Function.Injective b → ∀ (GK : Over (Sp K)) [GrpObj GK] (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap b) ψ), Compat f gγ ζ L m c (spMap b ≫ ξ) (b.comp a) (ψ ≫ φ₁) (pullTorus hψ j) → Compat f gγ ζ L m c ξ a φ₁ j := by
  first | exact @GlobalTheory.Poinc.FibLat.compat_of_compat_field | exact GlobalTheory.Poinc.FibLat.compat_of_compat_field | (intros; apply GlobalTheory.Poinc.FibLat.compat_of_compat_field <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8


theorem _root_.GlobalTheory.T.genericFibre_iso_specialises_to_fieldPoints : ∀ (o Ω : Type) [CommRing o] [IsNoetherianRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω), IsNormalScheme M.Z → ∀ (G : Over M.Z) [GrpObj G], IsSemiAbelian G → ∀ (R' : Subalgebra o Ω) (B : Over (Sp R')) [GrpObj B], IsSemiAbelian B → ∀ (A₀ : Over (Sp Ω)) [GrpObj A₀] (a' : A₀.left ⟶ B.left) (ψ : A₀.left ⟶ G.left), IsGrpPullback A₀ B (spMap R'.val.toRingHom) a' → IsGrpPullback A₀ G M.pt ψ → ∀ (K : Type) [Field K] (s : Sp K ⟶ M.Z), R' ≤ M.O (s (closedPoint K)) → ∀ (yK : R' →+* K), (∀ x : R', yK x = M.val s x) → ∀ (AK : Over (Sp K)) [GrpObj AK] (φK : AK.left ⟶ B.left), IsGrpPullback AK B (spMap yK) φK → ∃ Ψ : AK.left ⟶ G.left, IsGrpPullback AK G s Ψ ∧ (∀ (e : B ⟶ B) (F : G ⟶ G) (e₀ : A₀ ⟶ A₀), e₀.left ≫ a' = a' ≫ e.left → e₀.left ≫ ψ = ψ ≫ F.left → ∀ eK : AK ⟶ AK, eK.left ≫ φK = φK ≫ e.left → eK.left ≫ Ψ = Ψ ≫ F.left) ∧ ∀ (b : Sp R' ⟶ B.left) (gγ : Over.mk M.pt ⟶ G) (w : Sp Ω ⟶ A₀.left), b ≫ B.hom = 𝟙 _ → w ≫ A₀.hom = 𝟙 _ → w ≫ a' = spMap R'.val.toRingHom ≫ b → w ≫ ψ = gγ.left → ∀ (T : Scheme.{0}) (x : T ⟶ AK.left) (v : T ⟶ G.left), x ≫ φK = x ≫ AK.hom ≫ spMap yK ≫ b → ValAt gγ (x ≫ AK.hom ≫ s) v → x ≫ Ψ = v := by
  first | exact @GlobalTheory.Poinc.Spread.spread_fibre | exact GlobalTheory.Poinc.Spread.spread_fibre | (intros; apply GlobalTheory.Poinc.Spread.spread_fibre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8


theorem _root_.GlobalTheory.T.splitTorusPart_generic_fibre_closed_fibre_dvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G₁ : Over (Sp V)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (X₁ : Type) [AddCommGroup X₁] [Module.Free ℤ X₁] [Module.Finite ℤ X₁] (j : splitTorus (Sp V) X₁ ⟶ G₁), IsMonHom j → ∀ (GK : Over (Sp (FractionRing V))) [GrpObj GK] (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap (algebraMap V (FractionRing V))) ψ), IsTorPart (pullTorus hψ j) → ∀ (κ : Type) [Field κ] (b : V →+* κ), IsLocalHom b → ∀ (G₀ : Over (Sp κ)) [GrpObj G₀] (ψ₀ : G₀.left ⟶ G₁.left) (hψ₀ : IsGrpPullback G₀ G₁ (spMap b) ψ₀) (X₀ : Type) [AddCommGroup X₀] [Module.Free ℤ X₀] [Module.Finite ℤ X₀] (t₀ : splitTorus (Sp κ) X₀ ⟶ G₀), IsTorPart t₀ → Module.finrank ℤ X₀ = Module.finrank ℤ X₁ → IsTorPart (pullTorus hψ₀ j) := by
  first | exact @GlobalTheory.Poinc.FibClosed.isTorPart_pullTorus_closed | exact GlobalTheory.Poinc.FibClosed.isTorPart_pullTorus_closed | (intros; apply GlobalTheory.Poinc.FibClosed.isTorPart_pullTorus_closed <;> assumption)
end
