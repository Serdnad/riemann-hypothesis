module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle025
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemicharacterSqEqOneOfSymmetric
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle010
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsConstOfCover
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle011
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle004
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle101
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle039
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HermFormSwapOfIsHermitian
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsThetaSeriesApplyNeZeroOfLargeForm
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle007
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.SectionsPowThetaFunctions
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.WeilIsExpRiemannForm
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFibreSimplyTransitive
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGrpPullbackOfLoc

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.AnyAppellHumbert

theorem hermForm_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hermForm Hm w z = star (hermForm Hm z w) := by
  unfold hermForm
  rw [← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, h.eq, Matrix.dotProduct_mulVec]

theorem semicharacter_add {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (hL : L.IsLB) (u : HolUnif A L g)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (h : u.IsAH Hm χ) (l m : u.Λ) (n : ℤ)
    (hn : (n : ℝ) = (hermForm Hm l m).im) : χ (l + m) = χ l * χ m * (-1) ^ n := by
  obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex 0).left hL
  have hi' : ⊤ ≤ (u.ex (0 + l)).left ⁻¹ᵁ L.U i := by rwa [SectionTheta.ex_add_lattice]
  have hi'' : ⊤ ≤ (u.ex (0 + l + m)).left ⁻¹ᵁ L.U i := by rwa [SectionTheta.ex_add_lattice]
  have h1 := h.2.2.2 l i 0 hi
  have h2 := h.2.2.2 m i _ hi'
  have h3 := h.2.2.2 (l + m) i 0 hi
  have hs := hermForm_swap h.1 (l : Fin g → ℂ) m
  have hne := u.fr_ne i _ hi''
  rw [h2, h3] at h1
  simp only [zero_add, Submodule.coe_add, star_add, Matrix.mulVec_add, dotProduct_add, add_dotProduct,
    zero_dotProduct, mul_zero] at h1 hne
  unfold hermForm at hs hn
  rw [hs] at h1
  generalize (l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)) = a at h1
  generalize (m : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ)) = b at h1
  generalize (l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ)) = c at h1 hn
  have hc : c = star c + 2 * n * Complex.I := by
    have := Complex.sub_conj c
    rw [← hn] at this
    push_cast at this
    rw [Complex.star_def]
    linear_combination this
  have he : Complex.exp (Real.pi / 2 * a) * Complex.exp (Real.pi * c + Real.pi / 2 * b) =
      (-1) ^ n * Complex.exp (Real.pi / 2 * (a + star c + (c + b))) := by
    rw [← Complex.exp_pi_mul_I, ← Complex.exp_int_mul, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    linear_combination (Real.pi / 2 : ℂ) * hc
  refine mul_right_cancel₀ (mul_ne_zero (Complex.exp_ne_zero (Real.pi / 2 * (a + star c + (c + b)))) hne) ?_
  linear_combination h1 + χ l * χ m * u.fr i (l + m) * he

theorem isAH_properties :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ → ∃ Ef : LinearMap.BilinForm ℤ u.Λ, (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef ∧ (∀ l, χ l = 1 ∨ χ l = -1) ∧ (∀ l m, χ (l + m) = χ l * χ m * (-1) ^ Ef l m) ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧ (∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn Hm χ n θ ∧ u.IsFnPow n s θ) ∧ ∀ θ, u.IsThetaFn Hm χ n θ → ∃! s, u.IsFnPow n s θ) ∧ ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k) → Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ))) (u.ex ((k : ℂ)⁻¹ • (b : Fin P.g → ℂ))) (unitOn c) := by
  intro hlaw _ _ hU P u Hm χ hA
  obtain ⟨ht1, ht2, hE⟩ := AnyUnif.tangent_and_unimodular hU P u
  obtain ⟨Ef, hEf, hb⟩ := hE Hm χ hA
  have hval := @valAt'_rules
  have hvalaff := @existsUnique_point_of_ringHom
  have hvalext := @eq_of_valAt'_eq hval hvalaff
  have hsmred := @isReduced_of_smooth_complex
  have hholprod := @holFamily_lift hval
  have hthg := @ThetaGroupFrame.thetaGrp_in_frame hval hholprod
  have hweil := @WeilExp.weilIs_exp_riemannForm hlaw.weil hval hvalext hsmred hthg
  have hsecfn := @sections_pow_theta_functions hval hvalext hsmred
  have hfshift := @fourierCoeff_unitCube_translate_of_entire_periodic
  have hfvan := @entire_periodic_eq_zero_of_fourierCoeff_eq_zero hfshift
  have hdimcl := @ClassicalTheta.card_le_pow_of_linearIndependent hfshift hfvan
  have hnormform := @SiegelNormalForm.exists_normal_form
  have hdim := @card_le_pow_of_linearIndependent_theta_principal hnormform hdimcl
  have hindep := @PowSec.exists_indep_sections hlaw.globalSectionsRank
  have hseconto := @ThetaOnto.theta_from_section hval hdim hindep hsecfn
  have h7 := hsecfn P u Hm χ Ef ⟨hA.1, hA.2.2.1, hEf, hA.2.2.2⟩
  refine ⟨Ef, hEf, hb, fun l => sq_eq_one_iff.1 (semicharacter_sq_eq_one_of_symmetric P u Hm χ hA l), fun l m => semicharacter_add P.isLB u hA l m _ (hEf l m),
    ht1, ht2, fun n => ⟨(h7 n).1, fun θ hθ => ?_⟩, hweil P u Hm χ Ef ⟨hA.1, hA.2.2.1, hEf, hA.2.2.2⟩⟩
  obtain ⟨s, hs⟩ := hseconto P u Hm χ Ef hA ⟨hA.1, hA.2.2.1, hEf, hA.2.2.2⟩ hb n θ hθ
  exact ⟨s, hs, fun s' hs' => (h7 n).2 θ s' s hs' hs⟩

end GlobalTheory.AnyAppellHumbert
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory


open LatticeHom in
theorem existsUnique_isMonHom_of_map_lattice :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P P' : Out.PolAV (Sp ℂ)) (L : LB P.A.left) (L' : LB P'.A.left) (u : HolUnif P.A L P.g) (u' : HolUnif P'.A L' P'.g) (F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ)), (∀ z ∈ u.Λ, F z ∈ u'.Λ) → ∃! f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F z) = u.ex z ≫ f := by
  intro hlaws _ _ hT P P' L L' u u' F hF
  obtain ⟨rig, hrig⟩ := P.8
  obtain ⟨rig', hrig'⟩ := P'.8
  obtain ⟨v, Hm, χ, Ef, hAH, -, -, -, -, hth, -⟩ := hT P rig hrig
  obtain ⟨v', Hm', χ', Ef', hAH', -, -, -, -, hth', -⟩ := hT P' rig' hrig'
  obtain ⟨T, hTu⟩ := exists_linearEquiv_of_holUnif hlaws.6 P u v
  obtain ⟨T', hTu'⟩ := exists_linearEquiv_of_holUnif hlaws.6 P' u' v'
  set F₀ : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ) :=
    T'.toLinearMap ∘ₗ F ∘ₗ T.symm.toLinearMap
  have hF₀T : ∀ z, F₀ (T z) = T' (F z) := fun z => by simp [F₀]
  have hF₀ : ∀ l ∈ v.Λ, F₀ l ∈ v'.Λ := by
    intro l hl
    have h1 : u.ex (T.symm l) = 1 := by
      rw [← hTu, T.apply_symm_apply]
      exact (v.5 l).2 hl
    have h2 : u'.ex (F (T.symm l)) = 1 := (u'.5 _).2 (hF _ ((u.5 _).1 h1))
    refine (v'.5 _).1 ?_
    have h3 : F₀ l = T' (F (T.symm l)) := by simp [F₀]
    rw [h3, hTu']
    exact h2
  obtain ⟨d, hd⟩ := exists_complementary_theta ThetaLarge.exists_theta_apply_ne_zero v v' P.7 P'.7
    hAH hAH' F₀ hF₀ 4
  obtain ⟨f, hf, hfF⟩ := exists_isMonHom_of_complementary hlaws.3 P P' v v'
    (fun k θ hθ => ((hth k).2 θ hθ).exists) (fun k s => ((hth' k).1 s).exists) F₀ hF₀ d hd
  have hfu : ∀ z, u'.ex (F z) = u.ex z ≫ f := by
    intro z
    rw [← hTu' (F z), ← hTu z, ← hfF, hF₀T]
  refine ⟨f, ⟨hf, hfu⟩, ?_⟩
  rintro f' ⟨-, hf'⟩
  have := P.5
  have : Smooth P.A.hom := SmoothOfRelativeDimension.smooth P.g P.A.hom
  have : IsReduced P.A.left := isReduced_of_smooth_complex P.A.left P.A.hom inferInstance
  have := P'.3
  have : IsSeparated P'.A.hom := inferInstance
  apply ComplexPoints.over_hom_ext_of_complexPoints
  intro x
  obtain ⟨z, rfl⟩ := u.3 x
  rw [← hf' z, hfu z]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory


open LatticeHom in
theorem exists_isMonHom_of_map_lattice :
    ThetaUnifAV → Out.Laws → ∀ (P P' : Out.PolAV (Sp ℂ)) (g : ℕ) (u : HolUnif P.A P.L g) (u' : HolUnif P'.A P'.L g) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), P.g = g → P'.g = g → (∀ z ∈ u.Λ, F z ∈ u'.Λ) → ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F z) = u.ex z ≫ f := by
  intro hT hL P P' g u u' F hg hg' hF
  have key : ∀ (Q : Out.PolAV (Sp ℂ)) (w : HolUnif Q.A Q.L g), Q.g = g →
      ∃ (v : HolUnif Q.A Q.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : v.Λ → ℂ) (T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
        v.IsAH Hm χ ∧ (∀ (k : ℕ) θ, v.IsThetaFn Hm χ k θ → ∃ s, v.IsFnPow k s θ) ∧
        (∀ (k : ℕ) s, ∃ θ, v.IsThetaFn Hm χ k θ ∧ v.IsFnPow k s θ) ∧ ∀ z, v.ex (T z) = w.ex z := by
    rintro Q w rfl
    obtain ⟨rig, hrig⟩ := Q.rigid
    obtain ⟨v, Hm, χ, -, hAH, -, -, -, -, hsec, -⟩ := hT Q rig hrig
    obtain ⟨T, hTv⟩ := exists_linearEquiv_of_holUnif hL.mulN Q w v
    exact ⟨v, Hm, χ, T, hAH, fun k θ h => ((hsec k).2 θ h).exists, fun k s => ((hsec k).1 s).exists, hTv⟩
  obtain ⟨v, Hm, χ, T, hAH, hsec, -, hv⟩ := key P u hg
  obtain ⟨v', Hm', χ', T', hAH', -, hfn, hv'⟩ := key P' u' hg'
  let F₀ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := T'.toLinearMap ∘ₗ F ∘ₗ T.symm.toLinearMap
  have hF₀ : ∀ z, F₀ (T z) = T' (F z) := fun z => by simp [F₀]
  have hΛ : ∀ l ∈ v.Λ, F₀ l ∈ v'.Λ := fun l hl => by
    obtain ⟨z, rfl⟩ := T.surjective l
    rw [hF₀, ← v'.ker, hv', u'.ker]
    refine hF z ?_
    rwa [← u.ker, ← hv, v.ker]
  obtain ⟨d, hd⟩ := exists_complementary_theta ThetaLarge.exists_theta_apply_ne_zero v v' P.isLB P'.isLB hAH hAH'
    F₀ hΛ 4
  obtain ⟨f, hf, hfe⟩ := exists_isMonHom_of_complementary hL.ample P P' v v' hsec hfn F₀ hΛ d hd
  exact ⟨f, hf, fun z => by rw [← hv', ← hF₀, hfe, hv]⟩

end GlobalTheory
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.ObjPull

theorem objPull_of_lie_of_ample : (∀ (O : Type) [CommRing O] (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (a : OAct O G) (a' : OAct O G'), IsGrpPullback G' G f φ → (∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S') (τ : O →+* k) (n : ℕ), LieMult a' x τ n ↔ LieMult a (x ≫ f) τ n) → (∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsAbelianScheme G → IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → IsAbelianScheme G' ∧ (Out.RelAmple G L → Out.RelAmple G' L') ∧ (Out.KTriv G L → Out.KTriv G' L')) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap o' o f) := by
  intro _ hAb
  exact objPull_of_pol hAb

end GlobalTheory.ObjPull

namespace GlobalTheory

theorem obj_rigid_of_laws : Out.Laws → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (o : Obj D l b s) (o' : Obj D l b' s') (f : S' ⟶ S), (IsReduced S' ∨ IsLocallyNoetherian S') → ∀ m m' : SABMap o'.t o.t f, (∀ a, ∃ σ, (o'.eta a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ := by
  intro hL hpol E _ _ _ H D l B B' _ _ b b' S S' s s' o o' f _
  exact obj_rigid_of_pol hL hpol E H D l B B' b b' S S' s s' o o' f

end GlobalTheory

namespace GlobalTheory.LevelFibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

section Main

theorem exists_tate_push_comm
    {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f) {k : Type} [Field k]
    (x : Sp k ⟶ S') (z : Sp k ⟶ S) (hz : x ≫ f = z) (e : (Over.mk x ⟶ t'.G) ≃* (Over.mk z ⟶ t.G))
    (he : ∀ p, (e p).left = p.left ≫ m.φ)
    (I : TateIso D k (Over.mk x ⟶ t'.G) (fun a g => g ≫ t'.act.act a)
      (fun n g g' c => Out.WeilIs t'.G t'.PP.L n g g' (unitOn c))) :
    ∃ J : TateIso D k (Over.mk z ⟶ t.G) (fun a g => g ≫ t.act.act a)
      (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)), J.ζ = I.ζ ∧ ∀ n a, J.ev n a = e (I.ev n a) := by
  exact exists_tate_push m x z hz e he I

variable {l l₂ : Level H} {Xo : Moduli D l} {Xo₂ : Moduli D l₂}

theorem exists_sim_of_fibre_comm
    (hPull : ∀ (k : Type) [Field k] (z : Sp k ⟶ Xo₂.X), ∃ o' : Obj D l₂ (baseKA l₂) (z ≫ Xo₂.s), Nonempty (ObjMap o' Xo₂.univ z))
    {k : Type} [Field k] [IsAlgClosed k]
    (hDiff : ∀ (z : Sp k ⟶ Xo.X) (I I' : TateIso D k (Over.mk z ⟶ Xo.univ.t.G) (fun a g => g ≫ Xo.univ.t.act.act a)
      (fun n g g' c => Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L n g g' (unitOn c))),
      ∃ g : Sim D, ∀ n, 0 < n → (∀ a, I'.ev n a = I.ev n (g.f n a)) ∧ I'.ζ n = I.ζ n ^ g.ν n)
    (hd : l.Dvd l₂) (r : Xo₂.X ⟶ Xo.X) (m : SABMap Xo₂.univ.t Xo.univ.t r)
    (hm : ∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left)
    (hmA : ∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left)
    (hLev : ∀ g : Sim D, g.InGam l l₂ → ∃ ρ : Xo₂.X ≅ Xo₂.X, Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r)
    (x x' : Sp k ⟶ Xo₂.X) (hr : x ≫ r = x' ≫ r) (hs : x ≫ Xo₂.s = x' ≫ Xo₂.s) :
    ∃ (g : Sim D) (ρ : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ ∧ Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r ∧ x' = x ≫ ρ.hom := by
  obtain ⟨β, hβ⟩ := exists_spMap (x ≫ Xo₂.s)
  obtain ⟨-, I, hIζ, hIA, hI⟩ := Xo₂.univ.geom k x β hβ
  obtain ⟨-, I', hIζ', hIA', hI'⟩ := Xo₂.univ.geom k x' β (hs.symm.trans hβ)
  obtain ⟨e, he⟩ := exists_ptEquiv m.cart x _ rfl
  obtain ⟨e', he'⟩ := exists_ptEquiv m.cart x' _ hr.symm
  obtain ⟨J, hJζ, hJ⟩ := exists_tate_push_comm m x _ rfl e he I
  obtain ⟨J', hJζ', hJ'⟩ := exists_tate_push_comm m x' _ hr.symm e' he' I'
  obtain ⟨g, hg⟩ := hDiff _ J J'
  have key : ∀ (σ : 𝟙_ (Over Xo₂.X) ⟶ Xo₂.univ.t.G) (τ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (d : ℕ),
      (σ ^ d).left ≫ m.φ = r ≫ τ.left → e (toUnit _ ≫ σ) ^ d = e' (toUnit _ ≫ σ) ^ d := fun σ τ d h => by
    apply Over.OverMorphism.ext
    rw [← map_pow, ← map_pow, ← MonObj.comp_pow, ← MonObj.comp_pow, he, he', unit_left, unit_left, Category.assoc,
      Category.assoc]
    exact (congrArg _ h).trans (((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ τ.left) hr).trans
      (Category.assoc _ _ _))).trans (congrArg _ h.symm))
  obtain ⟨hin, hη⟩ := inGam_of_diff l l₂ hd J J' g hg
    (by rw [hJζ, hJζ']; exact Units.ext (hIζ'.trans hIζ.symm))
    (fun a => e (toUnit _ ≫ Xo₂.univ.eta a)) (fun a => e' (toUnit _ ≫ Xo₂.univ.eta a))
    (fun a b => by rw [Xo₂.univ.eta_add, MonObj.comp_mul, map_mul])
    (fun a b => by rw [Xo₂.univ.eta_add, MonObj.comp_mul, map_mul])
    (fun a ha => by rw [Xo₂.univ.eta_ker a ha, MonObj.comp_one, map_one])
    (fun a ha => by rw [Xo₂.univ.eta_ker a ha, MonObj.comp_one, map_one])
    (fun a ha => by rw [hJ, hI a ha]) (fun a ha => by rw [hJ', hI' a ha])
    (fun a => key _ _ _ (hm a)) (fun a => by rw [hJ, hJ', ← hIA, ← hIA']; exact key _ _ _ (hmA a))
  have hηA : ∀ a, e' (toUnit _ ≫ Xo₂.univ.etaA a) = e (toUnit _ ≫ Xo₂.univ.etaA (g.f l₂.A a)) := fun a => by
    rw [hIA, hIA', ← hJ, ← hJ', (hg _ l₂.A_pos).1]
  obtain ⟨ρ, hρ, hρr⟩ := hLev g hin
  refine ⟨g, ρ, hin, hρ, hρr, ?_⟩
  obtain ⟨hρs, ν, hν, hνA⟩ := hρ
  obtain ⟨o, ⟨p⟩⟩ := hPull k x'
  obtain ⟨n₁, hn₁⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m p.toSABMap
  obtain ⟨n₂, hn₂⟩ := sab_cast hr.symm n₁
  obtain ⟨n, hn⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ r x m n₂
  obtain ⟨n₃, hn₃⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν n
  have lev : ∀ (s : 𝟙_ (Over (Sp k)) ⟶ o.t.G) (σ τ : 𝟙_ (Over Xo₂.X) ⟶ Xo₂.univ.t.G),
      s.left ≫ p.toSABMap.φ = x' ≫ σ.left → e' (toUnit _ ≫ σ) = e (toUnit _ ≫ τ) → τ.left ≫ ν.φ = ρ.hom ≫ σ.left →
      s.left ≫ n₃.φ = (x ≫ ρ.hom) ≫ σ.left := fun s σ τ h₁ h₂ h₃ => by
    have h₄ : s.left ≫ n.φ = x ≫ τ.left := by
      apply m.cart.1.hom_ext
      · have := congrArg (fun w => w.left) h₂
        simp only [he, he', unit_left] at this
        refine Eq.trans ?_ this
        rw [← h₁, Category.assoc, Category.assoc]
        exact congrArg _ (hn.symm.trans (hn₂.trans hn₁))
      · rw [Category.assoc, Category.assoc, n.cart.1.w, ← Category.assoc, sec_w, sec_w]
        exact (Category.id_comp x).trans (Category.comp_id x).symm
    rw [hn₃, ← Category.assoc, h₄, Category.assoc, Category.assoc]
    exact congrArg _ h₃
  obtain ⟨f, -, hf⟩ := Xo₂.rep (Sp k) (x' ≫ Xo₂.s) inferInstance o
  rw [hf x' ⟨rfl, ⟨p⟩⟩]
  refine (hf _ ⟨by rw [Category.assoc, hρs, hs], ⟨⟨n₃, fun a => ?_, fun a => ?_⟩⟩⟩).symm
  · exact lev _ _ _ (p.eta a) (hη a) (hν a)
  · exact lev _ _ _ (p.etaA a) (hηA a) (hνA a)

end Main

theorem levelMap_fibre_simply_transitive_of_laws :
    Out.Laws → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l
        : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (j
        : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f
        : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap
        o' o f)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D
        : Datum H) (l : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b
        : Base l B) (b' : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s'
        : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o''
        : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f'
        : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫
        f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫
        f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ)) → (∀ (E
        : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B
        : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
        : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 *
        (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → (∀ (E
        : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂
        : Level H) (B : Type) [CommRing B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s
        : S ⟶ Sp B) (o₂ : Obj D l₂ b₂ s), l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (o
        : Obj D l b s) (m : SABMap o₂.t o.t (𝟙 S)), (∀ a, (o₂.eta a ^ (l₂.M /
        l.M)).left ≫ m.φ = 𝟙 S ≫ (o.eta a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A /
        l.A)).left ≫ m.φ = 𝟙 S ≫ (o.etaA a).left)) → (∀ (E : Type) [Field E] [NumberField
        E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing
        B] [CommRing B'] (b : Base l B) (b' : Base l B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s'
        : S' ⟶ Sp B') (o : Obj D l b s) (o' : Obj D l b' s') (f : S' ⟶ S), (IsReduced S' ∨
        IsLocallyNoetherian S') → ∀ m m' : SABMap o'.t o.t f, (∀ a, ∃ σ, (o'.eta
        a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ) → (∀ (E : Type) [Field
        E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo
        : Moduli D l) (B : Type) [CommRing B] (b : Base l B) (j : KA l →+* B) (S : Scheme.{0}) (s
        : S ⟶ Sp B) (o : Obj D l b s), IsReduced S → j (baseKA l).ρ = b.ρ → j (baseKA
        l).ζ = b.ζ → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ
        f)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (k
        : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e
        : ℕ → Q → Q → kˣ → Prop), (∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c') → ∀ I I' : TateIso D k Q act e, ∃ g : Sim D, ∀ n, 0 < n → (∀ a, I'.ev n a = I.ev n (g.f
        n a)) ∧ I'.ζ n = I.ζ n ^ g.ν n) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H
        : Host E) (D : Datum H), 1 ≤ D.p + D.q → (∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n
        : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n
        : ℤ)) ∧ (∃ g : Sim D, ∀ n, g.f n = LinearMap.id ∧ g.ν n = 1) ∧ (∀ g g' : Sim D, ∃ g'' : Sim D, ∀ n, g''.f n = g.f n ∘ₗ g'.f n ∧ g''.ν n = g.ν n * g'.ν n) ∧ (∀ g : Sim D, ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f
        n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧ (n : ℤ) ∣ g.ν n * g'.ν n - 1)) → (∀ (E
        : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂
        : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r
        : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x
        : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^
        (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A /
        l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA
        a).left) → ∀ g : Sim D, g.InGam l l₂ → ∃ ρ : Xo₂.X ≅ Xo₂.X, Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r) → ∀ (E
        : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂
        : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r
        : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x
        : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^
        (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A /
        l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) → ∀ (c : Coeff l) (c₂ : Coeff l₂) (hc
        : c.F = c₂.F) (rF
        : Xo₂.XF c₂ ⟶ Xo.XF c), rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r → rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion
        hc.le).toRingHom → ∀ (k : Type) [Field k] [IsAlgClosed k] (y y'
        : Sp k ⟶ Xo₂.XF c₂), y ≫ rF = y' ≫ rF → (∃ (g : Sim D) (ρ
        : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ ∧ Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r ∧ y' ≫ pullback.fst _ _ = y ≫ pullback.fst _ _ ≫ ρ.hom) ∧ ∀ (g
        : Sim D) (ρ
        : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ → Xo₂.LevAut g ρ → y ≫ pullback.fst _ _ ≫ ρ.hom = y ≫ pullback.fst _ _ → g.TrivAt l₂ := by
  intro hL hPull _ hPol _ hRig _ hDiff _ hLev E _ _ _ H D l l₂ Xo Xo₂ hpq hd r jK m hm c c₂ hc rF hF₁ hF₂ k _ _ y y' hy
  have pull : ∀ (l : Level H) (Xo : Moduli D l) (k : Type) [Field k] (z : Sp k ⟶ Xo.X),
      ∃ o' : Obj D l (baseKA l) (z ≫ Xo.s), Nonempty (ObjMap o' Xo.univ z) := fun l Xo k _ z =>
    hPull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (z ≫ Xo.s) z rfl rfl
      (by rw [spMap_id', Category.comp_id]) Xo.univ
  constructor
  · have hr : (y ≫ pullback.fst _ _) ≫ r = (y' ≫ pullback.fst _ _) ≫ r := by
      rw [Category.assoc, Category.assoc, ← hF₁, ← Category.assoc, ← Category.assoc, hy]
    have hbij : Function.Bijective (IntermediateField.inclusion hc.le).toRingHom :=
      ⟨(IntermediateField.inclusion hc.le).toRingHom.injective, fun a => ⟨⟨a.1, hc.ge a.2⟩, rfl⟩⟩
    have : IsIso (CommRingCat.ofHom (IntermediateField.inclusion hc.le).toRingHom) :=
      (ConcreteCategory.isIso_iff_bijective _).2 hbij
    have hsnd : y ≫ pullback.snd _ _ = y' ≫ pullback.snd _ _ := by
      rw [← cancel_mono (spMap (IntermediateField.inclusion hc.le).toRingHom), Category.assoc, Category.assoc, ← hF₂,
        ← Category.assoc, ← Category.assoc, hy]
    have hs : (y ≫ pullback.fst _ _) ≫ Xo₂.s = (y' ≫ pullback.fst _ _) ≫ Xo₂.s := by
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc, hsnd]
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hPol E H D l _ (baseKA l) _ Xo.s Xo.univ
    have := Xo.smooth
    have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
    have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
    let P : Out.PolAV Xo.X :=
      { A := Xo.univ.t.G, isAb := h₁, g := _, smoothDim := h₂, L := Xo.univ.t.PP.L, isLB := Xo.univ.t.PP.isLB,
        rigid := h₃, sym := h₄, ample := Xo.univ.ample, ktriv := Xo.univ.ktriv }
    obtain ⟨g, ρ, a₁, a₂, a₃, a₄⟩ := exists_sim_of_fibre_comm (pull l₂ Xo₂) (k := k)
      (fun z => hDiff E H D k _ _ _ fun n p q a b _ hp hq ha hb =>
        unitOn_injective (((hL.weil _ P n (Over.mk z)).1 p q hp hq).unique ha hb))
      hd r m hm.2.2.1 hm.2.2.2 (hLev E H D l l₂ Xo Xo₂ hpq hd r jK m hm) _ _ hr hs
    exact ⟨g, ρ, a₁, a₂, a₃, a₄.trans (Category.assoc _ _ _)⟩
  · intro g ρ hg hρ hx
    exact trivAt_of_fixed (pull l Xo) (fun k _ z o' => hRig E H D l _ _ _ _ _ _ _ _ Xo.univ o' z (Or.inl inferInstance))
      hd r m hm.2.2.1 _ g ρ hg hρ ((Category.assoc _ _ _).trans hx)

end GlobalTheory.LevelFibre
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SiegUnram

open GlobalTheory.FamRep

section Group

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] [IsCommMonObj G] [IsCommMonObj G']
  {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {L : LB G.left} {L' : LB G'.left}



end Group

variable {o : Type} [CommRing o] {S S' : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
  {s' : S' ⟶ Sp o}

theorem locallyOfFiniteType_of_isQProjOver (h : IsQProjOver s) : LocallyOfFiniteType s := by
  obtain ⟨N, i, hi, -, rfl⟩ := h
  have := isProper_str o N
  infer_instance

end GlobalTheory.SiegUnram
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem obj_rigid_any_base : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (o : Obj D l b s) (o' : Obj D l b' s') (f : S' ⟶ S), ∀ m m' : SABMap o'.t o.t f, (∀ a, ∃ σ, (o'.eta a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ :=
  fun hL => obj_rigid_of_pol hL obj_isAbelianScheme_dim_rigidified_sym

end GlobalTheory
end
