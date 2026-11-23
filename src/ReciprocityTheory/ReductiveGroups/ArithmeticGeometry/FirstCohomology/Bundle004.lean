module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

def OneCStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), P.TorsionIso →
    letI := H.starRing
    ∀ (α : 𝓞 E) (N : ℕ), 1 ≤ N → α * star α = (N : 𝓞 E) → (∃ u u' : 𝓞 E, u * α + u' * star α = 1) →
      IsUnit ((N : ℕ) : V) →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)),
      ValOver ϖ F v →
    ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := V) F ⟶ P.A.A) (fun a g => g ≫ P.oA.act a)
        (fun n g g' c => WeilIs P.A.A P.A.L n g g' (unitOn c))),
    ∀ θ : Fam P.D.toPre F 1, NuGe P.D Q F v 1 θ 0 →
      (∃ (σ : P.D.toPre.SecB 1 0)
        (σF : LB.Sec (LB.LinComb P.D.toPre.P.L (DegPre.famφ P.D.toPre F 0) (DegPre.famε 1))),
        GeneratorPullback.SecScal P.D.toPre.P.L (DegPre.famφ P.D.toPre F 0) (DegPre.famε 1) σF
          (P.D.toPre.famφB 0) (DegPre.famε 1) σ (DegPre.prB P.D.toPre F).left 1 ∧
        (∀ j, (θ.s 0).f j = σF.f j) ∧
        ¬ ∃ σ' : P.D.toPre.SecB 1 0, ∀ j, σ.f j = constFn P.D.toPre.P.A.hom _ ϖ * σ'.f j) →
    ∀ θα : Fam P.D.toPre F (1 * N), PullAl P.D F P.oD α 1 N θ θα →
    ∀ s : Fam P.D.toPre F (1 * N), NuGe P.D Q F v (1 * N) s 0 →
      ∃ (m : ℕ) (p : Fin m → QkPt P.D.toPre F (1 * N)) (x : Fin m → (TFK (R := V) F ⟶ P.A.A))
        (w : ∀ i, LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F (p i).g.b)
          (DegPre.lineε (1 * N))))
        (ζ : Fin m → F) (t : Fin m → Fam P.D.toPre F (1 * N)) (a : Fin m → F),
        (∀ i, P.ToA F (1 * N) (p i) (x i)) ∧
        (∀ i, x i ≫ P.oA.act (star α) = 1) ∧
        (∀ i, (w i).IsGen ∧ ζ i ≠ 0 ∧ FinOrd P.D F (1 * N) (p i) (w i) (ζ i)) ∧
        (∀ i, ∃ t' : Fam P.D.toPre F (1 * N),
          PhiRel P.D.toPre F (1 * N) (p i) (w i) θα t' ∧ Fam.IsSmul P.D.toPre F (ζ i) t' (t i)) ∧
        (∀ i, (0 : WithTop ℚ) ≤ v (a i)) ∧
        s = ∑ i, a i • t i

end ReciprocityTheory.ChartRestriction.G.H1
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TopologicalSpace Opposite

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1.SquareUnits

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic

variable {X Y Z : Scheme.{0}}

def UnitAt (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (y : Y) : Prop :=
  ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ J, Good L y J → IsUnit (sval s (𝟙 Y) y J)

variable {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem UnitAt.mul {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} {y : Y}
    (h : UnitAt L φ ε y) (h' : UnitAt L φ' ε' y) : UnitAt L (Sum.elim φ φ') (Sum.elim ε ε') y := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨s', hs'⟩ := h'
  exact ⟨mulSec s s', fun J hJ => by rw [sval_mulSec s s' _ y hJ]; exact (hs J hJ).mul (hs' J hJ)⟩

theorem UnitAt.congr (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} {y : Y}
    (hf : FormEq φ ε φ' ε') (h : UnitAt L φ ε y) : UnitAt L φ' ε' y := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨s', hs'⟩ := exists_sec hL hf s
  exact ⟨s', fun J hJ => by rw [hs' Y (𝟙 Y) y J hJ]; exact hs J hJ⟩

theorem formEq_of_add {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (H : ∀ (U : Type) [AddCommGroup U] (h : (Y ⟶ X) → U), ∑ k, ε k • h (φ k) = ∑ k, ε' k • h (φ' k)) :
    FormEq φ ε φ' ε' := by
  intro U _ h
  apply Additive.ofMul.injective
  simpa only [ofMul_prod, ofMul_zpow] using H (Additive U) (fun ψ => Additive.ofMul (h ψ))

theorem exists_sec_of_pullGen {Y' : Scheme.{0}} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y)
    (c : LB.Gen ((LB.LinComb L φ ε).pull h)) (hc : c.IsGen) :
    ∃ s : LB.Sec (LB.LinComb L (fun k => h ≫ φ k) ε), ∀ (r : Z ⟶ Y') (z : Z) (J : (Z ⟶ X) → L.ι),
      Good L z J → IsUnit (sval s r z J) := by
  have l : ∀ j : K → L.ι, LB.wchart L (fun k => h ≫ φ k) j ≤
      LB.wchart (LB.LinComb L φ ε) (K := PUnit) (fun _ => h) (fun _ => j) :=
    fun _ _ hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have e1 : ∀ (j : K → L.ι) (y : Y'), y ∈ LB.wchart L (fun k => h ≫ φ k) j →
      gs (𝟙 Y') y _ (res (l j) (c.s (fun _ => j))).val =
        (gm (𝟙 Y') y (LB.wchart (LB.LinComb L φ ε) (K := PUnit) (fun _ => h) (fun _ => j)) (c.s (fun _ => j))).val :=
    fun j y hj => (gs_unit _ y _ hj _).trans (congrArg Units.val (gm_res _ y (l j) hj _))
  refine ⟨⟨fun j => (res (l j) (c.s (fun _ => j))).val, fun j j' => fn_ext fun y hy => ?_⟩, ?_⟩
  · refine ((gs_res (𝟙 Y') y _ hy _).trans (e1 j y hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y') y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_unit (𝟙 Y') y _ hy _).trans
        (congrArg Units.val (gm_linComb L _ _ (𝟙 Y') y j j' hy.1 hy.2))) ((gs_res (𝟙 Y') y _ hy _).trans
          (e1 j' y hy.2)))).symm)
    have m : ∀ j : K → L.ι, y ∈ LB.wchart L (fun k => h ≫ φ k) j → (𝟙 Y' ≫ h) y ∈ LB.wchart L φ j :=
      fun j hj => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hj k
    rw [gen_trans hc (𝟙 Y') y (l j hy.1) (l j' hy.2), Units.val_mul]
    congr 2
    simp only [trF, Finset.univ_unique, Finset.prod_singleton, zpow_one]
    exact (gm_linComb L φ ε (𝟙 Y' ≫ h) y j j' (m j hy.1) (m j' hy.2)).trans (by simp only [Category.assoc])
  · intro r z J hJ
    have hm := hJ.mem (fun k => h ≫ φ k) r
    exact (congrArg IsUnit (gs_unit r z _ hm _)).mpr (Units.isUnit _)

section Square

variable {k : Type} [Field k]

theorem spec_pt_eq (q q' : Spec (CommRingCat.of k)) : q = q' := by
  have h1 : PrimeSpectrum.asIdeal (R := k) q = ⊥ := @Ideal.eq_bot_of_prime k _ _ (PrimeSpectrum.isPrime (R := k) q)
  have h2 : PrimeSpectrum.asIdeal (R := k) q' = ⊥ := @Ideal.eq_bot_of_prime k _ _ (PrimeSpectrum.isPrime (R := k) q')
  exact PrimeSpectrum.ext (h1.trans h2.symm)

theorem unitAt_square (hsq : SquareSt) (P : PolAV (Spec (CommRingCat.of k)))
    (x₁ x₂ : baseOver (Spec (CommRingCat.of k)) ⟶ P.A) (y : (baseOver (Spec (CommRingCat.of k)) ⊗ P.A).left) :
    UnitAt P.L ![(translPt P.A (x₁ * x₂)).left, (snd (baseOver (Spec (CommRingCat.of k))) P.A).left,
      (translPt P.A x₁).left, (translPt P.A x₂).left] ![1, 1, -1, -1] y := by
  obtain ⟨V, hpV, c, hc⟩ := hsq (Spec (CommRingCat.of k)) P (baseOver (Spec (CommRingCat.of k))) x₁ x₂
    (IsLocalRing.closedPoint k)
  have hV : V = ⊤ := eq_top_iff.2 fun q _ => by rw [spec_pt_eq q (IsLocalRing.closedPoint k)]; exact hpV
  subst hV
  obtain ⟨s, hs⟩ := exists_sec_of_pullGen (Z := (baseOver (Spec (CommRingCat.of k)) ⊗ P.A).left)
    ((fst (baseOver (Spec (CommRingCat.of k))) P.A).left ⁻¹ᵁ ⊤).ι c hc
  let e := IsOpenImmersion.lift ((fst (baseOver (Spec (CommRingCat.of k))) P.A).left ⁻¹ᵁ ⊤).ι (𝟙 _)
    (by rintro _ ⟨q, rfl⟩; rw [Scheme.Opens.range_ι]; trivial)
  have he : e ≫ ((fst (baseOver (Spec (CommRingCat.of k))) P.A).left ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    IsOpenImmersion.lift_fac _ _ _
  refine UnitAt.congr P.isLB ?_ ⟨pullSec s e, fun J hJ => ?_⟩
  · refine formEq_of_add fun U _ hh => ?_
    simp only [← Category.assoc, he, Category.id_comp]
  · rw [sval_pullSec s e (𝟙 _) y hJ]
    exact hs _ y J hJ

theorem unitAt_iter (hsq : SquareSt) (P : PolAV (Spec (CommRingCat.of k)))
    (b : baseOver (Spec (CommRingCat.of k)) ⟶ P.A) (y : (baseOver (Spec (CommRingCat.of k)) ⊗ P.A).left) :
    ∀ n : ℕ, UnitAt P.L ![(translPt P.A (b ^ (n + 2))).left, (snd (baseOver (Spec (CommRingCat.of k))) P.A).left,
      (translPt P.A b).left] ![1, (n : ℤ) + 1, -((n : ℤ) + 2)] y
  | 0 => by
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_) (unitAt_square hsq P b b y)
    simp [Fin.sum_univ_succ, pow_two]
    module
  | n + 1 => by
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_)
      ((unitAt_iter hsq P b y n).mul (unitAt_square hsq P (b ^ (n + 2)) b y))
    have e : b ^ (n + 2) * b = b ^ (n + 1 + 2) := by rw [← pow_succ]
    simp [Fin.sum_univ_succ, e]
    module

end Square

end ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
end
end
