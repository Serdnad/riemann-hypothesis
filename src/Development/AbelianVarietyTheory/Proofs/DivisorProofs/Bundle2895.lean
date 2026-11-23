module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2692
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextensionSecondLawCommutativityValue
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2767
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle002
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001

@[expose] public section

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

theorem _root_.GlobalTheory.T.uniformisedTriple_abelianLocus_proper_relAmple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R), (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (S : Scheme.{0}) (x : S ⟶ Sp R) (t' : SAB H S), (∀ s : S, ∏ i, tt i ∉ (x s).asIdeal) → Nonempty (SABMap t' t x) → IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L := by
  first | exact @GlobalTheory.AbLocusPol.isProper_relAmple_kTriv_of_abLocus | exact GlobalTheory.AbLocusPol.isProper_relAmple_kTriv_of_abLocus | (intros; apply GlobalTheory.AbLocusPol.isProper_relAmple_kTriv_of_abLocus <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.PsiValUnit
open GlobalTheory.BXOf

theorem psi_val_unit_of_psiUnitOn : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (W : (Sp R).Opens) (χ : D.X), PsiUnitOn D χ W → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Subring F) [IsLocalRing T] (φ₁ : R →+* T), (∀ r, (φ₁ r : F) = algebraMap (FractionRing R) F (algebraMap R _ r)) → spMap φ₁ (closedPoint T) ∈ W → ∀ (J₀ : D.P.A.left → D.P.L.ι), (∀ x, x ∈ D.P.L.U (J₀ x)) → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), (∀ ψ : Sp T ⟶ D.P.A.left, J (spMap T.subtype ≫ ψ) = J₀ (ψ (closedPoint T))) → ∃ u : Tˣ, (GlobalTheory.BXOf.sig F (val (D.psi χ) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (closedPoint F) J) : F) = ((u : T) : F) := by
  intro R _ _ D W χ hW F _ _ T _ φ₁ hφ hP J₀ h₀ J hJ
  have hmem : spMap φ₁ (closedPoint T) ∈ W ⊓ (D.c χ).left ⁻¹ᵁ D.P.L.U (J₀ ((D.c χ).left (spMap φ₁ (closedPoint T)))) :=
    ⟨hP, h₀ _⟩
  obtain ⟨V, hVa, hPV, hVle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Sp R).isBasis_affineOpens) hmem
  set j₀ := J₀ ((D.c χ).left (spMap φ₁ (closedPoint T))) with hj₀
  have hxK : D.xK χ = jK R ≫ (D.c χ).left := by
    show (toUnit (TK R) ≫ D.c χ).left = _
    rw [Over.comp_left]
    congr 1
  have hwch : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U (fun _ => j₀) :=
    fun x hx => Set.mem_iInter.2 fun _ => by
      show D.xK χ x ∈ D.P.L.U j₀
      rw [hxK]
      exact (hVle hx).2
  obtain ⟨r, hr, hre⟩ := hW (fun _ => j₀) V hVa (fun x hx => (hVle hx).1) (fun x hx => (hVle hx).2) hwch
  have hcomp : ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) ≫ jK R = spMap T.subtype ≫ spMap φ₁ := by
    rw [Over.id_left, Category.id_comp]
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (RingHom.ext hφ).symm
  have hch : J (((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) ≫ D.xK χ) = j₀ := by
    have e : ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) ≫ D.xK χ = spMap T.subtype ≫ (spMap φ₁ ≫ (D.c χ).left) := by
      rw [hxK, ← Category.assoc, hcomp, Category.assoc]
    rw [e, hJ]
    rfl
  have e1 := val_of (D.psi χ) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (closedPoint F) J (fun _ => j₀) (fun _ => hch)
  have hin : jK R (((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (closedPoint F)) ∈ V := by
    show (((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) ≫ jK R) (closedPoint F) ∈ V
    rw [hcomp]
    exact top_le_of_mem (spMap φ₁) hPV trivial
  have e2 : res hwch ((D.psi χ).s fun _ => j₀) = pullU (jK R) V hr.unit := Units.ext hre.symm
  have e3 := gm_res ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (closedPoint F) hwch hin ((D.psi χ).s fun _ => j₀)
  rw [e2, gm_pull ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (jK R) (closedPoint F) V hin hr.unit, hcomp] at e3
  have e4 := sig_nat T.subtype (spMap φ₁) hPV hr.unit
  refine ⟨sig T (gm (spMap φ₁) (closedPoint T) V hr.unit), ?_⟩
  exact (congrArg (fun u => (sig F u : F)) (e1.trans e3.symm)).trans (congrArg Units.val e4).symm

end GlobalTheory.PsiValUnit
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.LinCombComp

variable {X Y Z : Scheme.{0}}

theorem gm_gen {M : LB Y} {t : LB.Gen M} (ht : t.IsGen) (f : Z ⟶ Y) (z : Z) {i j : M.ι}
    (hi : f z ∈ M.U i) (hj : f z ∈ M.U j) :
    gm f z (M.U i) (t.s i) = gm f z (M.U i ⊓ M.U j) (M.g i j) * gm f z (M.U j) (t.s j) := by
  have hm : f z ∈ M.U i ⊓ M.U j := ⟨hi, hj⟩
  exact (gm_res f z _ hm _).symm.trans ((congrArg (gm f z _) (ht i j)).trans ((map_mul _ _ _).trans
    (congrArg _ (gm_res f z _ hm _))))

theorem gm_div (M N : LB Y) (f : Z ⟶ Y) (z : Z) (p q : (LB.div M N).ι)
    (hp : f z ∈ (LB.div M N).U p) (hq : f z ∈ (LB.div M N).U q) :
    gm f z ((LB.div M N).U p ⊓ (LB.div M N).U q) ((LB.div M N).g p q) =
      gm f z (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) * (gm f z (N.U p.2 ⊓ N.U q.2) (N.g p.2 q.2))⁻¹ := by
  have hm : f z ∈ (LB.div M N).U p ⊓ (LB.div M N).U q := ⟨hp, hq⟩
  show gm f z _ (res _ (M.g p.1 q.1) * (res _ (N.g p.2 q.2))⁻¹) = _
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f z _ hm _)
    ((map_inv _ _).trans (congrArg _ (gm_res f z _ hm _))))

theorem trF_self {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y)
    (z : Z) (j : K → L.ι) (hj : r z ∈ LB.wchart L φ j) : trF φ ε r z j j = 1 :=
  Finset.prod_eq_one fun k _ => by
    rw [gm_self hL (r ≫ φ k) z (Set.mem_iInter.1 hj k), one_zpow]

theorem trF_sum {L : LB X} {K K₁ : Type} [Fintype K] [Fintype K₁] (φ₀ : K → (Y ⟶ X)) (ε₀ : K → ℤ)
    (φ₁ : K₁ → (Y ⟶ X)) (ε₁ : K₁ → ℤ) (r : Z ⟶ Y) (z : Z) (j₁ j₁' : K₁ → L.ι) (j₀ j₀' : K → L.ι) :
    trF (Sum.elim φ₁ φ₀) (Sum.elim ε₁ (fun k => -ε₀ k)) r z (Sum.elim j₁ j₀) (Sum.elim j₁' j₀') =
      trF φ₁ ε₁ r z j₁ j₁' * (trF φ₀ ε₀ r z j₀ j₀')⁻¹ := by
  rw [trF, trF, trF, Fintype.prod_sum_type, ← Finset.prod_inv_distrib]
  congr 1
  exact Finset.prod_congr rfl fun k _ => zpow_neg _ _

theorem wchart_sum_le (L : LB X) {K K₁ : Type} [Fintype K] [Fintype K₁] (φ₀ : K → (Y ⟶ X))
    (φ₁ : K₁ → (Y ⟶ X)) (j₁ : K₁ → L.ι) (j₀ : K → L.ι) :
    LB.wchart L φ₁ j₁ ⊓ LB.wchart L φ₀ j₀ ≤ LB.wchart L (Sum.elim φ₁ φ₀) (Sum.elim j₁ j₀) :=
  fun _ hy => Set.mem_iInter.2 fun k => by
    cases k with
    | inl k => exact Set.mem_iInter.1 hy.1 k
    | inr k => exact Set.mem_iInter.1 hy.2 k

end GlobalTheory.LinCombComp

namespace GlobalTheory.LinCombComp

theorem gm_iso_linComb {X Y : Scheme.{0}} {L : LB X} {A : LB Y} {K : Type} [Fintype K]
    (φ₀ : K → (Y ⟶ X)) (ε₀ : K → ℤ) (u : LB.Iso A (LB.LinComb L φ₀ ε₀)) (hu : u.IsGen)
    (y : Y) (j₀ j₀' : K → L.ι) (a a' : A.ι) (h0 : y ∈ LB.wchart L φ₀ j₀) (ha : y ∈ A.U a)
    (h0' : y ∈ LB.wchart L φ₀ j₀') (ha' : y ∈ A.U a') :
    gm (𝟙 Y) y (LB.wchart L φ₀ j₀ ⊓ A.U a) (u.s (j₀, a)) =
      (trF φ₀ ε₀ (𝟙 Y) y j₀ j₀' * (gm (𝟙 Y) y (A.U a ⊓ A.U a') (A.g a a'))⁻¹) *
        gm (𝟙 Y) y (LB.wchart L φ₀ j₀' ⊓ A.U a') (u.s (j₀', a')) := by
  have hp : (𝟙 Y) y ∈ (LB.div (LB.LinComb L φ₀ ε₀) A).U (j₀, a) := ⟨h0, ha⟩
  have hq : (𝟙 Y) y ∈ (LB.div (LB.LinComb L φ₀ ε₀) A).U (j₀', a') := ⟨h0', ha'⟩
  have e1 := gm_gen hu (𝟙 Y) y hp hq
  have e2 := gm_div (LB.LinComb L φ₀ ε₀) A (𝟙 Y) y (j₀, a) (j₀', a') hp hq
  have e3 : gm (𝟙 Y) y (LB.wchart L φ₀ j₀ ⊓ LB.wchart L φ₀ j₀') ((LB.LinComb L φ₀ ε₀).g j₀ j₀') =
      trF φ₀ ε₀ (𝟙 Y) y j₀ j₀' := gm_linComb L φ₀ ε₀ (𝟙 Y) y j₀ j₀' h0 h0'
  rw [e2] at e1
  exact e1.trans (congrArg (fun t => t * (gm (𝟙 Y) y (A.U a ⊓ A.U a') (A.g a a'))⁻¹ *
    gm (𝟙 Y) y (LB.wchart L φ₀ j₀' ⊓ A.U a') (u.s (j₀', a'))) e3)

end GlobalTheory.LinCombComp

namespace GlobalTheory.LinCombComp

theorem gm_gen_sum {X Y : Scheme.{0}} {L : LB X} {K K₁ : Type} [Fintype K] [Fintype K₁]
    (φ₀ : K → (Y ⟶ X)) (ε₀ : K → ℤ) (φ₁ : K₁ → (Y ⟶ X)) (ε₁ : K₁ → ℤ)
    (c : LB.Gen (LB.LinComb L (Sum.elim φ₁ φ₀) (Sum.elim ε₁ (fun k => -ε₀ k)))) (hc : c.IsGen)
    (y : Y) (j₁ j₁' : K₁ → L.ι) (j₀ j₀' : K → L.ι) (h1 : y ∈ LB.wchart L φ₁ j₁) (h0 : y ∈ LB.wchart L φ₀ j₀)
    (h1' : y ∈ LB.wchart L φ₁ j₁') (h0' : y ∈ LB.wchart L φ₀ j₀') :
    gm (𝟙 Y) y (LB.wchart L (Sum.elim φ₁ φ₀) (Sum.elim j₁ j₀)) (c.s (Sum.elim j₁ j₀)) =
      (trF φ₁ ε₁ (𝟙 Y) y j₁ j₁' * (trF φ₀ ε₀ (𝟙 Y) y j₀ j₀')⁻¹) *
        gm (𝟙 Y) y (LB.wchart L (Sum.elim φ₁ φ₀) (Sum.elim j₁' j₀')) (c.s (Sum.elim j₁' j₀')) := by
  rw [← trF_sum]
  exact gen_trans hc (𝟙 Y) y (wchart_sum_le L φ₀ φ₁ j₁ j₀ ⟨h1, h0⟩) (wchart_sum_le L φ₀ φ₁ j₁' j₀' ⟨h1', h0'⟩)

end GlobalTheory.LinCombComp

namespace GlobalTheory.LinCombComp

theorem exists_iso_comp_val {X Y : Scheme.{0}} {L : LB X} {A : LB Y} {K K₁ : Type} [Fintype K] [Fintype K₁]
    (φ₀ : K → (Y ⟶ X)) (ε₀ : K → ℤ) (φ₁ : K₁ → (Y ⟶ X)) (ε₁ : K₁ → ℤ) (hL : L.IsLB) (hA : A.IsLB)
    (u : LB.Iso A (LB.LinComb L φ₀ ε₀)) (hu : u.IsGen)
    (c : LB.Gen (LB.LinComb L (Sum.elim φ₁ φ₀) (Sum.elim ε₁ (fun k => -ε₀ k)))) (hc : c.IsGen) :
    ∃ u' : LB.Iso A (LB.LinComb L φ₁ ε₁), u'.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z)
      (J : (Z ⟶ X) → L.ι) (a : A.ι), q z ∈ A.U a → Good L z J →
      gm q z _ (u'.s (fun k => J (q ≫ φ₁ k), a)) = gm q z _ (u.s (fun k => J (q ≫ φ₀ k), a)) * val c q z J := by
  have eu := gm_iso_linComb φ₀ ε₀ u hu
  have ec := gm_gen_sum φ₀ ε₀ φ₁ ε₁ c hc
  have glue : ∀ (j₁ : K₁ → L.ι) (a : A.ι), ∃ s : Γ(Y, LB.wchart L φ₁ j₁ ⊓ A.U a)ˣ,
      ∀ (Z' : Scheme.{0}) (q : Z' ⟶ Y) (z : Z') (j₀ : K → L.ι), q z ∈ LB.wchart L φ₁ j₁ → q z ∈ A.U a →
        q z ∈ LB.wchart L φ₀ j₀ →
        gm q z (LB.wchart L φ₁ j₁ ⊓ A.U a) s =
          gm q z (LB.wchart L (Sum.elim φ₁ φ₀) (Sum.elim j₁ j₀)) (c.s (Sum.elim j₁ j₀)) *
            gm q z (LB.wchart L φ₀ j₀ ⊓ A.U a) (u.s (j₀, a)) := by
    intro j₁ a
    obtain ⟨W, hW⟩ : ∃ W : (K → L.ι) → Y.Opens, ∀ j₀, W j₀ = LB.wchart L φ₁ j₁ ⊓ A.U a ⊓ LB.wchart L φ₀ j₀ :=
      ⟨_, fun _ => rfl⟩
    have l₀ : ∀ j₀, W j₀ ≤ LB.wchart L φ₁ j₁ ⊓ A.U a := fun j₀ => (hW j₀).le.trans inf_le_left
    have l₁ : ∀ j₀, W j₀ ≤ LB.wchart L (Sum.elim φ₁ φ₀) (Sum.elim j₁ j₀) := fun j₀ y hy => by
      rw [hW] at hy; exact wchart_sum_le L φ₀ φ₁ j₁ j₀ ⟨hy.1.1, hy.2⟩
    have l₂ : ∀ j₀, W j₀ ≤ LB.wchart L φ₀ j₀ ⊓ A.U a := fun j₀ y hy => by
      rw [hW] at hy; exact ⟨hy.2, hy.1.2⟩
    obtain ⟨uu, hu'⟩ : ∃ uu : ∀ j₀, Γ(Y, W j₀)ˣ, ∀ (Z' : Scheme.{0}) (q : Z' ⟶ Y) (z : Z') (j₀ : K → L.ι),
        q z ∈ W j₀ → gm q z (W j₀) (uu j₀) =
          gm q z (LB.wchart L (Sum.elim φ₁ φ₀) (Sum.elim j₁ j₀)) (c.s (Sum.elim j₁ j₀)) *
            gm q z (LB.wchart L φ₀ j₀ ⊓ A.U a) (u.s (j₀, a)) :=
      ⟨fun j₀ => res (l₁ j₀) (c.s (Sum.elim j₁ j₀)) * res (l₂ j₀) (u.s (j₀, a)), fun Z' q z j₀ h =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res q z (l₁ j₀) h _) (gm_res q z (l₂ j₀) h _))⟩
    have memW : ∀ y j₀, y ∈ W j₀ ↔ (y ∈ LB.wchart L φ₁ j₁ ∧ y ∈ A.U a) ∧ y ∈ LB.wchart L φ₀ j₀ := fun y j₀ => by
      rw [hW]; exact Iff.rfl
    obtain ⟨s, hs⟩ := glue_unit (LB.wchart L φ₁ j₁ ⊓ A.U a) W l₀ (fun y hy => by
        choose j₀ hj₀ using fun k => exists_chart hL (φ₀ k y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨j₀, (memW y j₀).2 ⟨hy, Set.mem_iInter.2 hj₀⟩⟩) uu (fun j₀ j₀' y hy => by
        obtain ⟨⟨h1, ha⟩, h0⟩ := (memW y j₀).1 hy.1
        obtain ⟨-, h0'⟩ := (memW y j₀').1 hy.2
        refine (hu' Y (𝟙 Y) y j₀ hy.1).trans (Eq.trans ?_ (hu' Y (𝟙 Y) y j₀' hy.2).symm)
        rw [ec y j₁ j₁ j₀ j₀' h1 h0 h1 h0', eu y j₀ j₀' a a h0 ha h0' ha, trF_self hL φ₁ ε₁ (𝟙 Y) y j₁ h1,
          gm_self hA (𝟙 Y) y ha, _root_.one_mul, _root_.inv_one, _root_.mul_one, _root_.mul_mul_mul_comm, _root_.inv_mul_cancel, _root_.one_mul])
    refine ⟨s, fun Z' q z j₀ h1 ha h0 => ?_⟩
    have hy : q z ∈ W j₀ := (memW _ j₀).2 ⟨⟨h1, ha⟩, h0⟩
    exact (gm_res q z (l₀ j₀) hy s).symm.trans ((congrArg (gm q z (W j₀)) (hs j₀)).trans (hu' Z' q z j₀ hy))
  choose s hs using glue
  refine ⟨⟨fun p => s p.1 p.2⟩, fun p p' => unit_ext fun y hy => ?_, fun Z q z J a ha hJ => ?_⟩
  · obtain ⟨⟨h1, ha⟩, h1', ha'⟩ := hy
    choose j₀ hj₀ using fun k => exists_chart hL (φ₀ k y)
    have h0 : y ∈ LB.wchart L φ₀ j₀ := Set.mem_iInter.2 hj₀
    have key : gm (𝟙 Y) y (LB.wchart L φ₁ p.1 ⊓ A.U p.2) (s p.1 p.2) =
        (trF φ₁ ε₁ (𝟙 Y) y p.1 p'.1 * (gm (𝟙 Y) y (A.U p.2 ⊓ A.U p'.2) (A.g p.2 p'.2))⁻¹) *
          gm (𝟙 Y) y (LB.wchart L φ₁ p'.1 ⊓ A.U p'.2) (s p'.1 p'.2) := by
      rw [hs p.1 p.2 Y (𝟙 Y) y j₀ h1 ha h0, hs p'.1 p'.2 Y (𝟙 Y) y j₀ h1' ha' h0,
        ec y p.1 p'.1 j₀ j₀ h1 h0 h1' h0, eu y j₀ j₀ p.2 p'.2 h0 ha h0 ha', trF_self hL φ₀ ε₀ (𝟙 Y) y j₀ h0,
        _root_.inv_one, _root_.mul_one, _root_.one_mul, _root_.mul_mul_mul_comm, _root_.mul_assoc]
    have hm : y ∈ (LB.div (LB.LinComb L φ₁ ε₁) A).U p ⊓ (LB.div (LB.LinComb L φ₁ ε₁) A).U p' :=
      ⟨⟨h1, ha⟩, h1', ha'⟩
    have ed := (gm_div _ _ (𝟙 Y) y p p' hm.1 hm.2).trans
      (congrArg (· * _) (gm_linComb L φ₁ ε₁ (𝟙 Y) y p.1 p'.1 h1 h1'))
    exact (gm_res _ y _ hm _).trans (key.trans ((congrArg₂ (· * ·) ed.symm (gm_res _ y _ hm _).symm).trans
      (map_mul _ _ _).symm))
  · have h1 := hJ.mem φ₁ q
    have h0 := hJ.mem φ₀ q
    refine (hs _ a Z q z (fun k => J (q ≫ φ₀ k)) h1 ha h0).trans ((mul_comm _ _).trans (congrArg _ ?_))
    exact (val_of c q z J _ (fun k => by cases k <;> rfl)).symm

end GlobalTheory.LinCombComp
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem gs_eq_map_gs {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) :
    gs f y U a = (f.stalkMap y).hom (gs (𝟙 X) (f y) U a) := by
  rw [gs_eq f y U h, gs_eq (𝟙 X) (f y) U h]
  have := congrArg (fun q => q.hom a) (f.germ_stalkMap U y h)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this.symm

def IsSecOver {X : Scheme.{0}} (L : LB X) (W : X.Opens) (s : ∀ k, Γ(X, W ⊓ L.U k)) : Prop :=
  ∀ (z : X) (k k' : L.ι), z ∈ W → z ∈ L.U k → z ∈ L.U k' →
    gs (𝟙 X) z (W ⊓ L.U k) (s k) =
      (gm (𝟙 X) z (L.U k ⊓ L.U k') (L.g k k') : X.presheaf.stalk z) * gs (𝟙 X) z (W ⊓ L.U k') (s k')

def SecCarriedOver {X : Scheme.{0}} (L : LB X) (W : X.Opens) (s : ∀ k, Γ(X, W ⊓ L.U k)) (f : X ⟶ X)
    (w : LB.Iso L (L.pull f)) : Prop :=
  ∀ (z : X) (j k : L.ι), z ∈ W → f z ∈ W → z ∈ L.U k → f z ∈ L.U j →
    gs f z (W ⊓ L.U j) (s j) = (gw w (𝟙 X) z j k : X.presheaf.stalk z) * gs (𝟙 X) z (W ⊓ L.U k) (s k)

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.GenOne

theorem unit_eq_one_of_generic (R : Type) [CommRing R] [IsDomain R] (V : (Spec (CommRingCat.of R)).Opens) (hV : V = ⊤)
    (a : Γ(Spec (CommRingCat.of R), V)ˣ) (h : ∀ z, gm (jK R) z V a = 1) : a = 1 := by
  subst hV
  have h1 : pullU (jK R) ⊤ a = 1 := by
    refine unit_ext fun x _ => ?_
    rw [map_one, gm_pull (𝟙 _) (jK R) x ⊤ trivial, Category.id_comp]
    exact h x
  have h2 : (jK R).appTop.hom (a : Γ(Spec (CommRingCat.of R), ⊤)) = 1 := congrArg Units.val h1
  have h3 := congrArg (fun f => f.hom (a : Γ(Spec (CommRingCat.of R), ⊤)))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h3
  rw [h2, map_one] at h3
  have h4 : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (a : Γ(Spec (CommRingCat.of R), ⊤)) = 1 :=
    IsFractionRing.injective R (FractionRing R) (by rw [map_one]; exact h3.symm)
  apply Units.ext
  apply (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective
  rw [Units.val_one, map_one]
  exact h4

theorem val_eq_one_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] {X : Scheme.{0}} (L : LB X), L.IsLB → ∀ {K : Type} [Fintype K] (φ : K → (Spec (CommRingCat.of R) ⟶ X)) (ε : K → ℤ), FormEq φ ε (PEmpty.elim : PEmpty → (Spec (CommRingCat.of R) ⟶ X)) (PEmpty.elim : PEmpty → ℤ) → ∀ t : LB.Gen (LB.LinComb L φ ε), t.IsGen → (∀ (z : (TK R).left) (J : ((TK R).left ⟶ X) → L.ι), Good L z J → val t (jK R) z J = 1) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J → val t r z J = 1 := by
  intro R _ _ X L hL K _ φ ε hF t ht hgen Z r z J hJ
  obtain ⟨t', -, hv⟩ := exists_gen hL hF t ht
  have htop : ∀ j : PEmpty → L.ι,
      L.wchart (PEmpty.elim : PEmpty → (Spec (CommRingCat.of R) ⟶ X)) j = ⊤ := by
    intro j
    simp [LB.wchart]
  have key : ∀ j, t'.s j = 1 := by
    intro j
    refine unit_eq_one_of_generic R _ (htop j) _ fun y => ?_
    choose J' hJ' using fun ψ : (TK R).left ⟶ X => exists_chart hL (ψ y)
    have h1 := (hv _ (jK R) y J' hJ').trans (hgen y J' hJ')
    have e : j = fun k => J' (jK R ≫ (PEmpty.elim : PEmpty → (Spec (CommRingCat.of R) ⟶ X)) k) :=
      funext fun k => k.elim
    subst e
    exact h1
  rw [← hv Z r z J hJ]
  exact (congrArg (gm r z _) (key _)).trans (map_one _)

end GlobalTheory.Mum.GenOne
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.UU GlobalTheory.UU.PackageDescent

noncomputable section
namespace GlobalTheory.Mum.BijDescent

variable {X X' Y Y' : Scheme.{0}} {K : Type} [Fintype K]

theorem exists_gen_descend_val_bij {L : LB X} (π : Y' ⟶ Y)
    (hπ : ∀ V : Y.Opens, Function.Bijective (π.app V).hom) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (u : LB.Gen (LB.LinComb L (fun k => π ≫ φ k) ε)) (hu : u.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J → val t (r ≫ π) z J = val u r z J := by
  have le : ∀ j : K → L.ι, π ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => π ≫ φ k) j :=
    fun j y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have desc : ∀ j : K → L.ι, ∃ a : Γ(Y, LB.wchart L φ j),
      (π.app _).hom a = (res (le j) (u.s j)).val := fun j => (hπ _).2 _
  choose a ha using desc
  have hun : ∀ j, IsUnit (a j) := by
    intro j
    obtain ⟨b, hb⟩ := (hπ (LB.wchart L φ j)).2 ((res (le j) (u.s j))⁻¹).val
    refine IsUnit.of_mul_eq_one b ((hπ _).1 ?_)
    rw [map_mul, map_one, ha j, hb]
    exact Units.mul_inv _
  have hv : ∀ j (Z : Scheme.{0}) (r : Z ⟶ Y') (y : Z), π (r y) ∈ LB.wchart L φ j →
      gm (r ≫ π) y (LB.wchart L φ j) (hun j).unit =
      gm r y (LB.wchart L (fun k => π ≫ φ k) j) (u.s j) := by
    intro j Z r y hy
    have e : pullU π _ (hun j).unit = res (le j) (u.s j) := Units.ext (ha j)
    exact (gm_pull r π y _ hy _).symm.trans ((congrArg (gm r y _) e).trans (gm_res r y (le j) hy _))
  refine ⟨⟨fun j => (hun j).unit⟩, fun j j' => Units.ext
    ((hπ (LB.wchart L φ j ⊓ LB.wchart L φ j')).1 ?_), fun Z r z J hJ => ?_⟩
  · refine congrArg Units.val (unit_ext (a := pullU π _ _) (b := pullU π _ _) fun y hy => ?_)
    have hy' : π y ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' := hy
    refine (gm_pull (𝟙 Y') π y _ hy' _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') π y _ hy' _).symm)
    refine ((gm_res (𝟙 Y' ≫ π) y _ hy' _).trans ((hv j _ _ y hy'.1).trans
      (gen_trans hu (𝟙 Y') y (le j hy'.1) (le j' hy'.2)))).trans (Eq.symm ?_)
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L φ ε (𝟙 Y' ≫ π) y j j' hy'.1 hy'.2).trans ?_)
      ((gm_res (𝟙 Y' ≫ π) y _ hy' _).trans (hv j' _ _ y hy'.2)))
    simp only [trF, Category.id_comp]
  · rw [val_of _ (r ≫ π) z J (fun k => J (r ≫ π ≫ φ k)) (fun k => by rw [Category.assoc])]
    exact hv _ Z r z (Set.mem_iInter.2 fun k => hJ (r ≫ π ≫ φ k))

theorem exists_descend_bij {M : LB X} {L : LB X'} {F : X' ⟶ X} {w : LB.Iso L (M.pull F)} (hw : PGen w)
    (hM : M.IsLB) (hL : L.IsLB) (π : Y' ⟶ Y) (hπ : ∀ V : Y.Opens, Function.Bijective (π.app V).hom)
    {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} (hc : ∀ k, φ' k ≫ F = π ≫ φ k) {ε : K → ℤ}
    (a : LB.Gen (LB.LinComb L φ' ε)) (ha : a.IsGen) :
    ∃ t : LB.Gen (LB.LinComb M φ ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (I : (Z ⟶ X) → M.ι) (J : (Z ⟶ X') → L.ι), Good M z I → Good L z J →
        val t (r ≫ π) z I = (∏ k, gw w (r ≫ φ' k) z (I ((r ≫ φ' k) ≫ F)) (J (r ≫ φ' k)) ^ ε k) * val a r z J := by
  obtain ⟨t₁, ht₁, v₁⟩ := exists_up hw hM hL a ha
  obtain ⟨u, hu, vu⟩ := exists_gen hM (φ' := fun k => π ≫ φ k) (ε' := ε)
    (fun U _ h => Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ ε k) (hc k)) t₁ ht₁
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (I J), Good M z I → Good L z J → val u r z I =
      (∏ k, gw w (r ≫ φ' k) z (I ((r ≫ φ' k) ≫ F)) (J (r ≫ φ' k)) ^ ε k) * val a r z J := by
    intro Z r z I J hI hJ
    rw [vu Z r z I hI, val_of t₁ r z I (fun k => I ((r ≫ φ' k) ≫ F)) (fun k => by rw [Category.assoc])]
    exact v₁ Z r z _ _ (Set.mem_iInter.2 fun k => hI ((r ≫ φ' k) ≫ F)) (hJ.mem φ' r)
  obtain ⟨t, ht, vt⟩ := exists_gen_descend_val_bij π hπ φ ε u hu
  exact ⟨t, ht, fun Z r z I J hI hJ => (vt Z r z I hI).trans (key Z r z I J hI hJ)⟩

end GlobalTheory.Mum.BijDescent
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.iso_preserves_rigidification_at_origin : ∀ (V : Type) [CommRing V] [IsDomain V] (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G]
    (A : Over (Sp (FractionRing V))) [GrpObj A] [IsCommMonObj A] (θ : (Over.pullback (jK V)).obj G ⟶ A) [IsMonHom θ]
    (φ : A.left ⟶ G.left), θ.left ≫ φ = pullback.fst G.hom (jK V) →
    ∀ (he : eSec A ≫ φ = spMap (algebraMap V (FractionRing V)) ≫ eSec G)
    (LP : LB A.left) (LL LM : LB G.left), LP.IsLB → LL.IsLB → LM.IsLB →
    ∀ (rA : LB.Gen (LP.pull (eSec A))) (rL : LB.Gen (LL.pull (eSec G))) (rM : LB.Gen (LM.pull (eSec G)))
      (ψ : LB.Iso LP (LL.pull φ)) (e : LB.Iso LM LL) (w₀ : LB.Iso (LP.pull θ.left) (LM.pull (pullback.fst G.hom (jK V)))),
      (∀ (Z : Scheme.{0}) (r : Z ⟶ ((Over.pullback (jK V)).obj G).left) (z : Z) (i : LL.ι) (j : LM.ι) (k : LP.ι),
        pullback.fst G.hom (jK V) (r z) ∈ LL.U i → pullback.fst G.hom (jK V) (r z) ∈ LM.U j → θ.left (r z) ∈ LP.U k →
        gw w₀ r z j (fun _ => k) =
          (gm (r ≫ pullback.fst G.hom (jK V)) z (LL.U i ⊓ LM.U j) (e.s (i, j)))⁻¹ * gw ψ (r ≫ θ.left) z i k) →
      LB.Gen.Maps (LB.linCombIso ψ (K := PUnit) (fun _ => eSec A) (fun _ => 1)) rA
        (rigPullOf φ (spMap (algebraMap V (FractionRing V))) he LL rL) →
      LB.Gen.Maps (LB.linCombIso e (K := PUnit) (fun _ => eSec G) (fun _ => 1)) rM rL →
      ∀ (z : Sp (FractionRing V)) (JA : (Sp (FractionRing V) ⟶ A.left) → LP.ι) (JG : (Sp (FractionRing V) ⟶ G.left) → LM.ι),
        Good LP z JA → Good LM z JG →
        gw w₀ (eSec ((Over.pullback (jK V)).obj G)) z (JG (jK V ≫ eSec G)) (fun _ => JA (eSec A)) *
            val (L := LP) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rA (𝟙 _) z JA =
          val (L := LM) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) rM (jK V) z JG := by
  first | exact @GlobalTheory.normW_origin | exact GlobalTheory.normW_origin | (intros; apply GlobalTheory.normW_origin <;> assumption)
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

theorem _root_.GlobalTheory.T.secB_eq_everywhere_of_generic_agree_const : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (k : ℕ) (β : Q.X) (s s' : Q.SecB k β) (c : R), c ≠ 0 → (∀ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * sval s (DegPre.prB Q (FractionRing R)).left z J = gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * sval s' (DegPre.prB Q (FractionRing R)).left z J) → ∀ (Z : Scheme.{0}) (x : Z ⟶ Q.P.A.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval s x z J = sval s' x z J := by
  first | exact @GlobalTheory.SecBGenericAgree.main | exact GlobalTheory.SecBGenericAgree.main | (intros; apply GlobalTheory.SecBGenericAgree.main <;> assumption)
end
