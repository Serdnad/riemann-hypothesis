module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2339
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2900
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3179
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2911
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3284
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2783
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationProductOfUniformisedGroups
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3170
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3295
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3296
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3297
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

namespace GlobalTheory.Poinc.Sep.LiesCube

theorem alternating_alg {M : Type} [CommGroup M] (u e w f t : Finset (Fin 3) → M) (a b c : M)
    (v : ∀ S, u S * e S * w S = f S * t S)
    (c₁ : f {0, 1, 2} * f {0} * f {1} * f {2} * (t {0, 1, 2} * t {0} * t {1} * t {2}) * b =
      a * (f {0, 1} * f {0, 2} * f {1, 2} * f ∅) * (t {0, 1} * t {0, 2} * t {1, 2} * t ∅))
    (c₂ : u {0, 1, 2} * u {0} * u {1} * u {2} * c = a * (u {0, 1} * u {0, 2} * u {1, 2} * u ∅)) :
    e {0, 1, 2} * e {0} * e {1} * e {2} * (w {0, 1, 2} * w {0} * w {1} * w {2}) * b =
      c * (e {0, 1} * e {0, 2} * e {1, 2} * e ∅) * (w {0, 1} * w {0, 2} * w {1, 2} * w ∅) := by
  have E := fun {p q : M} (e : p = q) => congrArg Additive.ofMul e
  have v₀ := E (v ∅); have v₁ := E (v {0}); have v₂ := E (v {1}); have v₃ := E (v {2})
  have v₄ := E (v {0, 1}); have v₅ := E (v {0, 2}); have v₆ := E (v {1, 2}); have v₇ := E (v {0, 1, 2})
  have d₁ := E c₁; have d₂ := E c₂
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at *
  linear_combination (norm := abel) v₁ + v₂ + v₃ + v₇ - v₀ - v₄ - v₅ - v₆ + d₁ - d₂

theorem cube_of_liesOver : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ N : ℕ, 1 ≤ N → ∀ (ρ : LB.Gen (A.L.pull (eSec A.A))) (hρ : ρ.IsGen) (c : CubicalStr A.A ⟨A.L, ρ, A.isLB, hρ⟩) (g : Finset (Fin 3) → GtPtF D.toPre (FractionRing V)) (w : ∀ S, Frm D.toPre (FractionRing V) 1 (g S).b) (x : Finset (Fin 3) → (TFK (R := V) (FractionRing V) ⟶ A.A)) (e : ∀ S, FrAt (x S)), x ∅ = 1 → x {0, 1} = x {0} * x {1} → x {0, 2} = x {0} * x {2} → x {1, 2} = x {1} * x {2} → x {0, 1, 2} = x {0} * x {1} * x {2} → (∀ S, (∃ o, GtPtF.IsNsmul N (g S) o ∧ o.IsZero) ∧ (w S).IsGen ∧ (e S).IsGen ∧ LiesOver U.toUnifPre w₀ (g S) (w S) (x S) (e S)) → ∀ (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JB : ((TF (R := V) (FractionRing V)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good A.L z JA → Good D.toPre.P.L z JB → @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {0, 1, 2}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {0}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {1}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {2}) (𝟙 _) z JA) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {0, 1, 2}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {0}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {1}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {2}) (𝟙 _) z JB)) * cubV D.toPre.cub z JB (g {0}).b (g {1}).b (g {2}).b = @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (cubV c (T := TFK (R := V) (FractionRing V)) z JA (x {0}) (x {1}) (x {2})) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {0, 1}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {0, 2}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {1, 2}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e ∅) (𝟙 _) z JA)) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {0, 1}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {0, 2}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {1, 2}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w ∅) (𝟙 _) z JB)) := by
  intro V _ _ _ hV D A G _ _ hG U w₀ hw₀ N hN ρ hρ c g w x e hx₀ hx₁ hx₂ hx₃ hx₄ hS z JA JB hJA hJB
  choose h g' f t hF hE hP hf ht hT using fun S => GlobalTheory.T.exists_integral_data_framed_torsion_point_torus_ext V hV D A G hG U w₀ hw₀ N hN (g S) (w S) (x S) (e S)
    (hS S).1 (hS S).2.1 (hS S).2.2.1 (hS S).2.2.2
  have hm : ∀ S T S', x S' = x S * x T → h S' = h S * h T ∧ (g' S').b = (g' S).b * (g' T).b := fun S T S' hx => by
    have a := GlobalTheory.T.uniformisation_sections_extending_points_multiply V hV D A G hG U (x S) (x T) (h S) (h T) (h S') (hE S) (hE T) (hx ▸ hE S')
    exact ⟨a, GlobalTheory.T.formal_points_abelian_parts_multiply V hV D A G hG U (h S) (h T) (g' S) (g' T) (g' S') (hF S) (hF T) (a ▸ hF S')⟩
  have m₀ := hm ∅ ∅ ∅ (by rw [hx₀, _root_.mul_one])
  have m₁ := hm _ _ _ hx₁
  have m₂ := hm _ _ _ hx₂
  have m₃ := hm _ _ _ hx₃
  have m₄ := hm {0, 1} {2} {0, 1, 2} (by rw [hx₄, hx₁])
  have a₀ : h ∅ = 1 := mul_eq_left.1 m₀.1.symm
  have b₀ : (g' ∅).b = 1 := mul_eq_left.1 m₀.2.symm
  have a₄ : h {0, 1, 2} = h {0} * h {1} * h {2} := m₄.1.trans (by rw [m₁.1])
  have b₄ : (g' {0, 1, 2}).b = (g' {0}).b * (g' {1}).b * (g' {2}).b := m₄.2.trans (by rw [m₁.2])
  obtain ⟨JG, hJG⟩ : ∃ J, Good U.LG.L z J := by
    choose I hI using fun χ : _ ⟶ G.left => exists_chart U.LG.isLB (χ z)
    exact ⟨I, hI⟩
  have v := fun S => GlobalTheory.T.torsionPointFrame_mul_eq_integralGenerators V hV D A G hG U w₀ hw₀ N hN (g S) (w S) (x S) (e S)
    (hS S).1 (hS S).2.1 (hS S).2.2.1 (hS S).2.2.2 (h S) (g' S) (f S) (t S) (hF S) (hE S) (hP S) (hf S) (ht S) (hT S)
    z JA JG JB hJA hJG hJB
  have c₁ := GlobalTheory.T.integral_frames_respect_cubical_structures V hV D A G hG U h g' f t a₀ m₁.1 m₂.1 m₃.1 a₄ b₀ m₁.2 m₂.2 m₃.2 b₄ hF hf ht hT z JG JB hJG hJB
  have c₂ := GlobalTheory.T.uniformisation_cubical_structure_generic_fibre V hV D A G hG U w₀ hw₀ ρ hρ c x h hx₀ hx₁ hx₂ hx₃ hx₄ a₀ m₁.1 m₂.1 m₃.1 a₄ hE z JA JG hJA hJG
  have hb : ∀ S, toUnit (TF (R := V) (FractionRing V)) ≫ (g' S).b = (g S).b := fun S =>
    Over.OverMorphism.ext (hP S).1.symm
  rw [hb, hb, hb] at c₁
  exact alternating_alg (M := ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ) _
    (fun S => val (Z := (TF (R := V) (FractionRing V)).left) (e S) (𝟙 _) z JA) (fun S => val (w S) (𝟙 _) z JB)
    (fun S => val (f S) (toUnit (TF (R := V) (FractionRing V))).left z JG)
    (fun S => val (t S) (toUnit (TF (R := V) (FractionRing V))).left z JB) _ _ _ v c₁ c₂

end GlobalTheory.Poinc.Sep.LiesCube
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

theorem _root_.GlobalTheory.T.integral_squaredThetaTerms_torusCoordinates : ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ →
    (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.PsiEven → D.TauBimult →
    ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁),
    (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D N₁ e (fun mu c => u mu c * mo mu) →
    ∀ (τ₀ : GlobalTheory.UChart.Gens D) (m N : ℕ) (s : Fin m ⊕ Fin N → V₁) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ D.X)
      (hs : ∀ k, IsUnit (s (.inr k))),
    GlobalTheory.UChart.TauIn D τ₀ (fun k => s (finSumFinEquiv.symm k)) (fun k => ε (finSumFinEquiv.symm k)) →
    (∀ mu, algebraMap V₁ (FractionRing V₁) (mo mu) ^ 2 =
      ∏ k, algebraMap V₁ (FractionRing V₁) (s (.inl k)) ^ ε (.inl k) (e mu) (e mu)) →
    ∃ (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
      (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A))
      (t : ∀ c, LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1)))
      (χt : ∀ (mu : X) (c : C), LB.Gen (LB.LinComb D.P.L
        ![(D.c (e mu) * b c).left, (D.c (e mu)).left, (b c).left, (η[D.P.A]).left] DegPre.gtε))
      (s₀ : V₁) (G : X → C → V₁),
      (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
        IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
        GlobalTheory.Poinc.ThetaOne.OneBasisAt D f θ') ∧
      (∀ c, b c ^ N₁ = 1) ∧
      (∀ c, (t c).IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N₁) (N₁ ^ 2) 1), Normd κ →
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
          val (t c) r z J ^ (N₁ ^ 2) * val κ (r ≫ (b c).left) z J = 1) ∧
      (∀ mu c, (χt mu c).IsGen ∧ ∀ (T : Over (Sp V₁)) (z : T.left) J, Good D.P.L z J →
        ∏ i ∈ Finset.range N₁, cubV D.cub z J (toUnit T ≫ D.c (e mu)) (toUnit T ≫ b c ^ i) (toUnit T ≫ b c) =
          val (χt mu c) T.hom z J ^ N₁) ∧
      IsUnit s₀ ∧
      (∀ mu c, u mu c ^ 2 * s₀ = ((∏ k, (hs k).unit ^ ε (.inr k) (e mu) (e mu) : V₁ˣ) : V₁) * G mu c) ∧
      ∀ mu c (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
        gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom (G mu c)) =
          sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b c * D.c (e mu)).left) z J ^ 2 *
            (val (t c) r z J ^ 2 * val (χt mu c) r z J ^ 2 * val D.sym (r ≫ (D.c (e mu)).left) z J *
              (val (τ₀ (e mu) (-e mu)) r z J)⁻¹ * (rigV D r z J ^ 2)⁻¹).val := by
  first | exact @GlobalTheory.Poinc.Sep.CoefInt.integral_sq_terms | exact GlobalTheory.Poinc.Sep.CoefInt.integral_sq_terms | (intros; apply GlobalTheory.Poinc.Sep.CoefInt.integral_sq_terms <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

theorem _root_.GlobalTheory.T.integral_expression_values_at_descended_point : ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ →
    (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X)
    (τ₀ : GlobalTheory.UChart.Gens D) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))),
    (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
      IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
      GlobalTheory.Poinc.ThetaOne.OneBasisAt D f θ') →
    ∀ (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A)), (∀ c, b c ^ N₁ = 1) →
    ∀ (t : ∀ c, LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1))),
      (∀ c, (t c).IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N₁) (N₁ ^ 2) 1), Normd κ →
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
          val (t c) r z J ^ (N₁ ^ 2) * val κ (r ≫ (b c).left) z J = 1) →
    ∀ (χt : ∀ (mu : X) (c : C), LB.Gen (LB.LinComb D.P.L
        ![(D.c (e mu) * b c).left, (D.c (e mu)).left, (b c).left, (η[D.P.A]).left] DegPre.gtε)),
      (∀ mu c, (χt mu c).IsGen ∧ ∀ (T : Over (Sp V₁)) (z : T.left) J, Good D.P.L z J →
        ∏ i ∈ Finset.range N₁, cubV D.cub z J (toUnit T ≫ D.c (e mu)) (toUnit T ≫ b c ^ i) (toUnit T ≫ b c) =
          val (χt mu c) T.hom z J ^ N₁) →
    ∀ (G : X → C → V₁),
      (∀ mu c (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
        gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom (G mu c)) =
          sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b c * D.c (e mu)).left) z J ^ 2 *
            (val (t c) r z J ^ 2 * val (χt mu c) r z J ^ 2 * val D.sym (r ≫ (D.c (e mu)).left) z J *
              (val (τ₀ (e mu) (-e mu)) r z J)⁻¹ * (rigV D r z J ^ 2)⁻¹).val) →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
    ∀ (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁), GlobalTheory.UChart.FromBase D τ₀ ib → (∀ a, ev (ib a) ∈ k₀) →
    ∃ Λ : K, ∀ mu c, ∃ r ∈ k₀, ev (G mu c) = Λ * r := by
  first | exact @GlobalTheory.USep.EvG.ev_values | exact GlobalTheory.USep.EvG.ev_values | (intros; apply GlobalTheory.USep.EvG.ev_values <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TensBal

theorem transpose_mul_eq {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det)
    (a : TensO (symUnitOf W h)) :
    (TensO.mat _ a).transpose * (W + W.transpose) = (W + W.transpose) * TensO.mat _ (star a) := by
  have hb : ((symUnitOf W h).1 : Matrix (Fin r) (Fin r) ℤ) = W + W.transpose := rfl
  rw [TensO.star_def]
  show _ = (W + W.transpose) * (((((symUnitOf W h).1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
    (TensO.mat _ a).transpose * ((symUnitOf W h).1 : Matrix (Fin r) (Fin r) ℤ)))
  rw [hb.symm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

theorem tauBal_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (T : Tens D.toPre D'.toPre W), letI := T.mod (symUnitOf W h); ∀ a : TensO (symUnitOf W h), D'.toPre.TauBal (T.act (TensO.mat _ a)) (T.act (TensO.mat _ (star a))) (fun y => a • y) (fun y => star a • y) := by
  intro R _ _ _ _ D D' r W h _ T a
  exact GlobalTheory.T.tensorDegeneration_tauBalanced_of_adjointIntMatrices R _ D D' W T (TensO.mat _ a) (TensO.mat _ (star a)) (transpose_mul_eq W h a)

end GlobalTheory.Mum.TensBal
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor


theorem _root_.GlobalTheory.T.tensorQuotientTorsion_orderAction_matrix : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → ∀ (g : ℕ) (ev : ∀ n : ℕ, ((Fin g → ℤ) × (Fin g → ℤ)) → QkPt D.toPre F n), (∀ n, 0 < n → ∀ a b, QkAdd (ev n a) (ev n b) (ev n (a + b))) → (∀ n, 0 < n → ∀ a b, QkPt.Equiv D.toPre F (ev n a) (ev n b) ↔ ∃ e, a = b + n • e) → ∀ n, 0 < n → ∀ (x : 𝓞 E) (a : Fin r → (Fin g → ℤ) × (Fin g → ℤ)) (p' q' : QkPt D'.toPre F n), PtRel T ν ν' p' (fun j => ev n (a j)) → PtRel T ν ν' q' (fun i => ev n (∑ j, ρ x i j • a j)) → (letI := H.starRing; QkAct o x p' q') := by
  first | exact @GlobalTheory.Mum.TensAct.qkAct_tens | exact GlobalTheory.Mum.TensAct.qkAct_tens | (intros; apply GlobalTheory.Mum.TensAct.qkAct_tens <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.MumMult

theorem gs_pow_mul_pull {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (v u : Y ⟶ X) (N k : ℕ)
    (τ : LB.Sec (LB.LinComb L (K := Fin 2) ![v, u] ![(N : ℤ), -1])) (s : H0 L k) (i i' : Fin 1 → L.ι)
    (hle : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ LB.wchart L ![v, u] ![i' 0, i 0])
    (z : Y) (J' : (Y ⟶ X) → L.ι) (hz : z ∈ u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i') (hJ : Good L z J')
    (hv : J' (𝟙 Y ≫ v) = i' 0) :
    gs (𝟙 Y) z (u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i')
      ((Y.presheaf.map (homOfLE hle).op).hom (τ.f ![i' 0, i 0]) ^ k *
        (Y.presheaf.map (homOfLE (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤
          u ⁻¹ᵁ secChart L i)).op).hom ((u.app (secChart L i)).hom (s.f i))) =
      sval τ (𝟙 Y) z J' ^ k * sval s (𝟙 Y ≫ u) z J' := by
  have hm : (𝟙 Y : Y ⟶ Y) z ∈ LB.wchart L ![v, u] ![i' 0, i 0] := hle hz
  have hu : (𝟙 Y ≫ u) z ∈ secChart L i := hz.1
  have hv' : (𝟙 Y ≫ v) z ∈ L.U (i' 0) := Set.mem_iInter.1 hz.2 0
  have a0 : ∀ x y : Γ(Y, u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i'),
      gs (𝟙 Y) z _ (x ^ k * y) = gs (𝟙 Y) z _ x ^ k * gs (𝟙 Y) z _ y := fun x y => by
    rw [gs_eq _ _ _ hz, gs_eq _ _ _ hz, gs_eq _ _ _ hz, map_mul, map_mul, map_pow, map_pow]
  have a1 := gs_res (𝟙 Y) z hle hz (τ.f ![i' 0, i 0])
  have a2 := (gs_res (𝟙 Y) z (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤
          u ⁻¹ᵁ secChart L i) hz ((u.app (secChart L i)).hom (s.f i))).trans (gs_pull (𝟙 Y) u z _ hu (s.f i))
  rw [a0, a1, a2, sec_trans τ (𝟙 Y) z hm (hJ.mem _ (𝟙 Y)), sec_trans s (𝟙 Y ≫ u) z hu (hJ.mem _ _)]
  have e1 : trF (L := L) ![v, u] ![(N : ℤ), -1] (𝟙 Y) z ![i' 0, i 0] (fun k => J' (𝟙 Y ≫ (![v, u] : Fin 2 → _) k)) =
      (gm (𝟙 Y ≫ u) z _ (L.g (i 0) (J' (𝟙 Y ≫ u))))⁻¹ := by
    rw [trF, Fin.prod_univ_two]
    change gm (𝟙 Y ≫ v) z (L.U (i' 0) ⊓ L.U (J' (𝟙 Y ≫ v))) (L.g (i' 0) (J' (𝟙 Y ≫ v))) ^ (N : ℤ) *
      gm (𝟙 Y ≫ u) z (L.U (i 0) ⊓ L.U (J' (𝟙 Y ≫ u))) (L.g (i 0) (J' (𝟙 Y ≫ u))) ^ (-1 : ℤ) = _
    have gself : ∀ c : L.ι, c = i' 0 → gm (𝟙 Y ≫ v) z (L.U (i' 0) ⊓ L.U c) (L.g (i' 0) c) = 1 := by
      rintro c rfl; exact gm_self hL _ _ hv'
    rw [gself _ hv, one_zpow, _root_.one_mul, zpow_neg, zpow_one]
  have e2 : trF (L := L) (fun _ : Fin 1 => 𝟙 X) (fun _ => (k : ℤ)) (𝟙 Y ≫ u) z i
      (fun k => J' ((𝟙 Y ≫ u) ≫ (fun _ : Fin 1 => 𝟙 X) k)) =
      (gm (𝟙 Y ≫ u) z _ (L.g (i 0) (J' (𝟙 Y ≫ u)))) ^ k := by
    simp only [trF, Fin.prod_univ_one]
    have gid : ∀ f : Y ⟶ X, f = 𝟙 Y ≫ u →
        gm f z (L.U (i 0) ⊓ L.U (J' f)) (L.g (i 0) (J' f)) = gm (𝟙 Y ≫ u) z _ (L.g (i 0) (J' (𝟙 Y ≫ u))) := by
      rintro f rfl; rfl
    rw [gid _ (Category.comp_id _), zpow_natCast]
  rw [e1, e2]
  unfold sval
  generalize gm (𝟙 Y ≫ u) z _ (L.g (i 0) (J' (𝟙 Y ≫ u))) = A
  have hA : ((A⁻¹ : _ˣ) : Y.presheaf.stalk z) ^ k * ((A ^ k : _ˣ) : Y.presheaf.stalk z) = 1 := by
    rw [Units.val_pow_eq_pow_val, ← mul_pow, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_pow]
  rw [mul_pow, _root_.mul_mul_mul_comm, hA, _root_.one_mul]

private theorem isUnit_gs_iff_mem {X Y : Scheme.{0}} (r : Y ⟶ X) (z : Y) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ X.basicOpen a := by
  rw [gs_eq r z U h]
  refine ((Y.mem_basicOpen ((r.app U).hom a) z h).symm).trans ?_
  rw [← Scheme.Hom.preimage_basicOpen]
  rfl

theorem exists_mult_of_posN : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∀ N : ℕ, 1 ≤ N → GlobalTheory.MumMult.PosN D a h h' N → ∀ (σ₀ : LB.Sec (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1])) (x : D.toPre.P.A.left), D.toPre.P.A.hom x = (IsLocalRing.closedPoint R : PrimeSpectrum R) → GlobalTheory.MumMult.NonzeroAt D a N σ₀ x → ∃ m : ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι), Γ((thickObj R (maximalIdeal R) e G).left, GlobalTheory.MumMult.multW U b e i i'), GlobalTheory.MumMult.MultAct U b N m ∧ GlobalTheory.MumMult.LeadPt U b m := by
  intro R _ _ _ hR D A G _ _ hG U a a' h h' hE b hb N hN hP σ₀ x hx hnz
  obtain ⟨g, gsm, gtfe, gvan, g0⟩ := GlobalTheory.T.exists_mumford_formal_section_coefficient_family R hR.1 D a a' h h' hE N hN hP σ₀
  choose τ hτ using fun e => GlobalTheory.TwFamGlue.glue R hR.1 D a A G hG U e (b e) (hb.2.2.1 e) (N : ℤ) (-1) D.toPre.X id g gsm
  have hle : ∀ e (i i' : Fin 1 → U.LG.L.ι), multW U b e i i' ≤ LB.wchart U.LG.L
      ![(fstG (maximalIdeal R) e G).left, (b e).left ≫ (fstG (maximalIdeal R) e G).left] ![i' 0, i 0] := by
    intro e i i' y hy
    refine Set.mem_iInter.2 fun k => ?_
    fin_cases k
    · simpa using Set.mem_iInter.1 hy.2 0
    · simpa using Set.mem_iInter.1 hy.1 0
  refine ⟨fun e i i' => ((thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (hle e i i')).op).hom
    ((τ e).f ![i' 0, i 0]), ?_, ?_⟩
  · intro k hk f s hs
    obtain ⟨ρ, ρsm, ρtfe, hρ⟩ := GlobalTheory.T.exists_pullback_integralExpansion_formalEndomorphism R hR.1 D a a' h h' hE A G hG U b hb k s f hs
    obtain ⟨F, Fsm, Ftfe, hF⟩ := GlobalTheory.T.multiplier_power_mul_pullback_small_family R hR.1 D a a' h h' hE A G hG U b hb N k g ρ gsm ρsm gtfe ρtfe
    obtain ⟨Φ, hΦ⟩ := GlobalTheory.TwBack.exists_intFam R hR.1 D a h h' (N * k) F Fsm Ftfe
    refine ⟨Φ, fun e i i' => ?_⟩
    obtain ⟨τ', hτ'1, hτ'2⟩ := hρ e
    obtain ⟨τ'', h1, h2⟩ := hF e (τ e) τ' (hτ e) hτ'2
    refine GlobalTheory.MumMult.chartExpOn_of_tExp R hR.1 D a A G hG U e (b e) (N * k) F Φ.f τ'' Fsm hΦ h2 i' _ _ ?_
    intro z J' hz hJ' hv
    rw [h1 _ _ z J' hJ', hτ'1 _ _ z J' hJ']
    exact gs_pow_mul_pull U.LG.isLB _ _ N k (τ e) s i i' (hle e i i') z J' hz hJ' hv
  · refine ⟨x, hx, fun y hy i i' hyW => ?_⟩
    choose J hJ using fun χ : (thickObj R (maximalIdeal R) 0 G).left ⟶ D.toPre.P.A.left =>
      exists_chart D.toPre.P.isLB (χ y)
    choose J' hJ' using fun χ : (thickObj R (maximalIdeal R) 0 G).left ⟶ G.left => exists_chart U.LG.isLB (χ y)
    have hx0 : IsUnit (sval σ₀ (𝟙 _ ≫ (U.gt 0).pG.left) y J) := by
      have hm := Good.mem (L := D.toPre.P.L) hJ
        (![𝟙 D.toPre.P.A.left, a.left] : Fin 2 → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)) (𝟙 _ ≫ (U.gt 0).pG.left)
      have hyx : (𝟙 _ ≫ (U.gt 0).pG.left : (thickObj R (maximalIdeal R) 0 G).left ⟶ D.toPre.P.A.left) y = x := hy
      refine (isUnit_gs_iff_mem _ y _ hm _).2 ?_
      rw [hyx] at hm ⊢
      exact hnz _ hm
    have hg0 : sval (g 0) (𝟙 _ ≫ (U.gt 0).pG.left) y J = sval σ₀ (𝟙 _ ≫ (U.gt 0).pG.left) y J :=
      g0 _ (𝟙 _ ≫ (U.gt 0).q.left) y J hJ
    have hexp := hτ 0 {0} (fun β hβ => gvan β (by simpa using hβ)) _ (𝟙 _) y J J' hJ hJ'
    rw [Finset.sum_singleton] at hexp
    have hu : IsUnit (evalE U.toUnifPre (τ 0) (𝟙 _) y J J') := by
      rw [hexp]
      exact (hg0 ▸ hx0 : IsUnit (sval (g 0) (𝟙 _ ≫ (U.gt 0).pG.left) y J)).mul (Units.isUnit _)
    have hs : IsUnit (sval (τ 0) (𝟙 _) y J') := isUnit_of_mul_isUnit_right hu
    refine (isUnit_gs_iff_mem (𝟙 _) y _ hyW _).1 ?_
    have e := (gs_res (𝟙 _) y (hle 0 i i') hyW ((τ 0).f ![i' 0, i 0])).trans
      (sec_trans (τ 0) (𝟙 _) y (hle 0 i i' hyW) (Good.mem (L := U.LG.L) hJ' _ (𝟙 _)))
    exact e ▸ (Units.isUnit _).mul hs

end GlobalTheory.MumMult
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.isIntegralSection_everywhere_of_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (k : ℕ) (s : SecK L α k), (∀ x : G.left, M.π (G.hom x) = closedPoint R → IntAt L α s x) → ∀ x : G.left, IntAt L α s x := by
  first | exact @GlobalTheory.Mum.intAt_of_closedFibre | exact GlobalTheory.Mum.intAt_of_closedFibre | (intros; apply GlobalTheory.Mum.intAt_of_closedFibre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

theorem _root_.GlobalTheory.T.uniformisation_product_of_uniformisedGroups : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ : DegData R (maximalIdeal R)) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (D₂ : DegData R (maximalIdeal R)) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → IsSumPolAV A A₁ A₂ a₁ a₂ → ∃ U : Unif (maximalIdeal R) D A (G₁ ⊗ G₂), IsProdUnif U₁.toUnifPre U₂.toUnifPre U.toUnifPre p₁ p₂ q₁ q₂ a₁ a₂ := by
  first | exact @GlobalTheory.ProdUnifExists.main | exact GlobalTheory.ProdUnifExists.main | (intros; apply GlobalTheory.ProdUnifExists.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic
open GlobalTheory.GSep GlobalTheory.GSep.TransTerms

namespace GlobalTheory.GSep.TransTerms

theorem transExp_of_frExp : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ), ∀ a ∈ X₁.S.HH X₁.M z₁, ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ e : ℕ, GlobalTheory.GSep.TransTerms.FrExp 𝔪 a τ e → GlobalTheory.GSep.TransTerms.TransExp 𝔪 x₀ a τ e := by
  have huniq := GlobalTheory.T.thetaMember_terms_coefficients_unique
  intro I X₁ z₁ act x₀ hdiv V _ _ _ ev Y _ t δ 𝔪 a _ τ _ e hF
  obtain ⟨-, x, fr, th, w₀, s, g', w, hx, hfr, hth, hw₀, hs, htor, hw, hov, htr⟩ := hF
  intro χ hχ C lab T hT c hc C' lab' T' hT' c' hc' mu
  letI := GlobalTheory.TorusExt.gtGroup 𝔪.D.toPre (FractionRing V)
  set g₀ := GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ) with hg₀def
  have hg₀ : IsTor χ g₀ := (GlobalTheory.UT.isTor_iff _ _).2 (GlobalTheory.TorusExt.isTorusPtF_torusPt χ)
  have hadd : g'.IsAdd g₀ (g' + g₀) := (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 rfl
  have hb : (g' + g₀).b = g'.b := (GlobalTheory.UT.ThetaAverage.val_translate hg₀ hadd).1
  set c₀ : FractionRing V := 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) with hc₀def
  have hc₀ : c₀ ≠ 0 :=
    ((((X₁.S.prim.isUnit (by have := X₁.S.r_pos; have := X₁.S.N_ge; positivity)).pow e).map
      (algebraMap X₁.o₁ X₁.S.R)).map 𝔪.yK).ne_zero
  obtain ⟨w₁, hw₁, hv₁⟩ := GlobalTheory.UT.TorsionValue.exists_frm_scale w hw (inv_ne_zero hc₀)
  obtain ⟨w'', hw'', hv''⟩ : ∃ w'' : Frm 𝔪.D.toPre (FractionRing V) 1 (g' + g₀).b, w''.IsGen ∧
      ∀ z J, val w'' (𝟙 _) z J = val w₁ (𝟙 _) z J := by
    rw [hb]; exact ⟨w₁, hw₁, fun _ _ => rfl⟩
  have hvs : ∀ z J, Good 𝔪.D.toPre.P.L z J → (val w'' (𝟙 _) z J).val = cstH z c₀⁻¹ * (val w (𝟙 _) z J).val :=
    fun z J hJ => by rw [hv'' z J, hv₁ z J hJ, GlobalTheory.UT.CoefBasic.cst_eq]
  have hvw : ∀ z J, Good 𝔪.D.toPre.P.L z J → (val w (𝟙 _) z J).val = cstH (R := V) z c₀ * (val w'' (𝟙 _) z J).val :=
    fun z J hJ => by rw [hvs z J hJ, ← _root_.mul_assoc, ← map_mul, mul_inv_cancel₀ hc₀, map_one, _root_.one_mul]
  have hov'' := htr χ hχ g₀ hg₀ (g' + g₀) hadd w'' hw'' hvw
  have htor'' : ∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g' + g₀) o ∧ o.IsZero := by
    obtain ⟨o, ho, hoz⟩ := htor
    refine ⟨0, (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 ?_, (GlobalTheory.TorusExt.isZero_iff_eq _).2 rfl⟩
    rw [smul_add, ← (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 ho, (GlobalTheory.TorusExt.isZero_iff_eq _).1 hoz, zero_add, hg₀def,
      ← map_nsmul, ← ofMul_pow, hχ.1, ofMul_one, map_zero]
  obtain ⟨x₁, fr₁, th₁, w₀₁, s₁, G₁, W₁, hx₁, hfr₁, hth₁, hw₀₁, hs₁, hc₁, hT₁⟩ := hT
  obtain ⟨x₂, fr₂, th₂, w₀₂, s₂, G₂, W₂, hx₂, hfr₂, hth₂, hw₀₂, hs₂, hc₂, hT₂⟩ := hT'
  obtain ⟨ht₁, hW₁, ho₁⟩ := hc₁ c
  obtain ⟨ht₂, hW₂, ho₂⟩ := hc₂ c'
  rw [hc] at ho₁
  rw [hc'] at ho₂
  have u₁ := huniq I X₁ z₁ act V ev Y t δ 𝔪 a x x₁ fr fr₁ th th₁ w₀ w₀₁ s s₁ g' (G₁ c) w (W₁ c)
    hx hfr hth hw₀ hs htor hw hov hx₁ hfr₁ hth₁ hw₀₁ hs₁ ht₁ hW₁ ho₁ (𝔪.e₈ mu)
  have u₂ := huniq I X₁ z₁ act V ev Y t δ 𝔪 (a + τ) x x₂ fr fr₂ th th₂ w₀ w₀₂ s s₂ (g' + g₀) (G₂ c') w'' (W₂ c')
    hx hfr hth hw₀ hs htor'' hw'' hov'' hx₂ hfr₂ hth₂ hw₀₂ hs₂ ht₂ hW₂ ho₂ (𝔪.e₈ mu)
  have co := GlobalTheory.UT.ThetaAverage.coef_translate hg₀ hadd hw hvs s (𝔪.e₈ mu)
  have hθ := GlobalTheory.GSep.GMem.yK_th_ne_zero I X₁ z₁ act V ev Y t δ 𝔪 x₀ hdiv
  apply mul_right_cancel₀ hθ
  rw [_root_.mul_assoc, _root_.mul_assoc, hT₁ mu c, hT₂ mu c', ← u₁, ← u₂, co]
  field_simp

end GlobalTheory.GSep.TransTerms
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumSumSnd

theorem adj_snd : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₁ D₂ : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (i₂ : D₂.toPre.P.A ⟶ D.toPre.P.A) (j₂ : D₂.toPre.X →+ D.toPre.X), i₂ ≫ p₁ = toUnit _ ≫ η[D₁.toPre.P.A] → i₂ ≫ p₂ = 𝟙 _ → (∀ y, q₁ (j₂ y) = 0) → (∀ y, q₂ (j₂ y) = y) → Adj (pol D₂) (pol D) i₂ p₂ j₂ q₂ :=
  GlobalTheory.MumProdSwap.adj_snd

end GlobalTheory.MumSumSnd
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

theorem _root_.GlobalTheory.T.eigenframe_specialization_uniform_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsOrbit (U.X k) T M γ xx → IsLift U k y T xx → ∀ (v : Fin N → E) (R : ℝ), ∃ (C : ℝ) (B : ℕ), ∀ᶠ w in imTop, |w.re| ≤ R → ∀ (ρ : E →+* ℂ) (i : ℕ), ‖perFr (U.X k) (xx w) v ρ i‖ ≤ C * w.im ^ B := by
  first | exact @GlobalTheory.ShFam.PerPoly.periods_le_pow | exact GlobalTheory.ShFam.PerPoly.periods_le_pow | (intros; apply GlobalTheory.ShFam.PerPoly.periods_le_pow <;> assumption)
end
