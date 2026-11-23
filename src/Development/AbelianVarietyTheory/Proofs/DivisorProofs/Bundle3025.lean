module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2934
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2935
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiIsEven
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPreDataCubicalStructureEqProdPulledBack
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle019
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2982
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2802
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2806
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2983
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianSchemeAway
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle072
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2796
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFrameIsUnitAlongSection
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle068
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenMove

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.realisations_same_genericFibre_agree_at_points : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y)
  (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), R' ≤ X₁.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X₁.M.val (gPt p ≫ c.y) a) →
  ∀ (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)), Same ρ' ε' ρ₂ ε₂ (fun a => D.lab a) (algebraMap X₁.Ω₁ D.X.Ω₁) → R₂ ≤ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) → ∀ (y₂ : R₂ →+* PadicAlgCl p), (∀ a : R₂, y₂ a = D.X.M.val (gPt p ≫ y) a) →
  ∀ (K : Type) [Field K] (j : K →+* PadicAlgCl p) (f' : R' →+* K), j.comp f' = y₀ → (∀ a ∈ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))), D.X.M.val (gPt p ≫ y) a ∈ j.range) →
  ∀ (A₁ : PolAV (Sp K)) (a₁ : A₁.A.left ⟶ ρ'.P.A.left), IsGrpPullback A₁.A ρ'.P.A (spMap f') a₁ → LBIso A₁.L (ρ'.P.L.pull a₁) →
  ∃ (f₂ : R₂ →+* K) (φ₂ : A₁.A.left ⟶ ρ₂.P.A.left), j.comp f₂ = y₂ ∧ IsGrpPullback A₁.A ρ₂.P.A (spMap f₂) φ₂ ∧ LBIso A₁.L (ρ₂.P.L.pull φ₂) ∧
    (∀ (x : Sp (PadicAlgCl p) ⟶ A₁.A.left) (a : X₁.S.Gam), x ≫ A₁.A.hom = spMap j → (x ≫ φ₂ = spMap y₂ ≫ (ρ₂.pt (D.lab a)).left ↔ x ≫ a₁ = spMap y₀ ≫ (ρ'.pt a).left)) ∧
    (∀ (x x' : Sp (PadicAlgCl p) ⟶ A₁.A.left) (E : Matrix (Fin 8) (Fin 8) ℤ), x ≫ A₁.A.hom = spMap j → x' ≫ A₁.A.hom = spMap j → (x' ≫ φ₂ = x ≫ φ₂ ≫ (ε₂ E).left ↔ x' ≫ a₁ = x ≫ a₁ ≫ (ε' E).left)) := by
  first | exact @GlobalTheory.Poinc.special_transport | exact GlobalTheory.Poinc.special_transport | (intros; apply GlobalTheory.Poinc.special_transport <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.theta_value_product_formula_degeneration : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (a b : D'.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((TK R).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = (∏ K : ULift.{0} (Finset (Fin 2)), gm ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left) z _ (T.w.s (fun k => J ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left ≫ tensφ T.pr k), J' ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left))) ^ ((-1 : ℤ) ^ (2 - K.down.card))) * (∏ i, ∏ j, (cubV D.toPre.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr i) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr i) ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) * (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr j)) * cubV D.toPre.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr i) * cubV D.toPre.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr i)) ^ (-W i j)) * ∏ i, ∏ j, val (D.toPre.tau (T.xe a i) (T.xe b j)) (𝟙 _) z J ^ ((W + W.transpose) i j) := by
  first | exact @GlobalTheory.Mum.Tens.tau_periods | exact GlobalTheory.Mum.Tens.tau_periods | (intros; apply GlobalTheory.Mum.Tens.tau_periods <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.torsionLabels_galois_all_levels_of_squares : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → (∃ i₀ : ℕ, ∀ i : ℕ, i₀ ≤ i → ∀ (σ : Kb R →ₐ[FractionRing R] Kb R) (p p' : QkPt D.toPre (Kb R) ((n ^ i) ^ 2)), QkExt σ.toRingHom p p' → (lab ((n ^ i) ^ 2) p').left = spMap σ.toRingHom ≫ (lab ((n ^ i) ^ 2) p).left) → GalEqN n lab := by
  first | exact @GlobalTheory.Mum.galEqN_of_squares | exact GlobalTheory.Mum.galEqN_of_squares | (intros; apply GlobalTheory.Mum.galEqN_of_squares <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.tensorData_psi_isEven : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), Tens D.toPre D' W → D'.PsiEven := by
  first | exact @GlobalTheory.TensEven.main | exact GlobalTheory.TensEven.main | (intros; apply GlobalTheory.TensEven.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.tensorPreData_cubicalStructure_eq_prod_pulled_back : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (S : Over (Spec (CommRingCat.of R))) (z : S.left) (J : (S.left ⟶ D.P.A.left) → D.P.L.ι) (J' : (S.left ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → ∀ x x' y : S ⟶ D'.P.A, (let om := fun p : S ⟶ D'.P.A => gm p.left z _ (T.w.s (fun k => J (p.left ≫ tensφ T.pr k), J' p.left)); cubV D'.cub z J' x x' y * (om (x * x' * y) * (om (x * x'))⁻¹ * (om (x * y))⁻¹ * (om (x' * y))⁻¹ * om x * om x' * om y * (om 1)⁻¹) = ∏ k : (Fin r × Fin r) × Fin 4, cubV D.cub z J (x ≫ ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2) (x' ≫ ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2) (y ≫ ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2) ^ tensε W k) := by
  first | exact @GlobalTheory.TensCub.cubV_tens | exact GlobalTheory.TensCub.cubV_tens | (intros; apply GlobalTheory.TensCub.cubV_tens <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical

namespace GlobalTheory.Mum.CoverPull

theorem pt_mem_abLocus : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → ∀ (Z : GlobalTheory.ZH.ZHOut ρS M U₀ EE) (w : Sp Ω), M.pt w ∈ abLocus Z.G := by
  intro o Ω _ _ _ _ S ρS M U₀ EE hO Z w
  haveI : IsProper ρS.P.A.hom := ρS.P.isAb.proper
  haveI : IsProper ((Over.pullback Z.u₀).obj ρS.P.A).hom := by
    show IsProper (pullback.snd ρS.P.A.hom Z.u₀)
    infer_instance
  refine GlobalTheory.range_subset_abLocus_of_isProper (G' := (Over.pullback Z.u₀).obj ρS.P.A) (f := U₀.ι) (φ := Z.φ) Z.semi Z.cart.1 ?_
  have hm : M.pt w ∈ U₀ := M.top_le_preimage_pt hO.ne (x := w) trivial
  exact ⟨⟨_, hm⟩, rfl⟩

theorem exists_unif_pullback : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Z : GlobalTheory.ZH.ZHOut ρS M U₀ EE) (T : Scheme.{0}) (h : T ⟶ M.Z) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ ξ : Sp W ⟶ T, ((ξ ≫ h) ⁻¹' abLocus Z.G).Nonempty → ∃ (G' : Over (Sp W)) (_ : GrpObj G') (_ : IsCommMonObj G') (β : G'.left ⟶ ((Over.pullback h).obj Z.G).left) (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G'), IsGrpPullback G' ((Over.pullback h).obj Z.G) ξ β ∧ LBIso U'.LG.L ((Z.L.L.pull (pullback.fst Z.G.hom h)).pull β) := by
  intro o Ω _ _ _ S ρS M U₀ EE Z T h W _ _ _ hW ξ hab
  have pull_isLB : ∀ {X Y : Scheme.{0}} {L : LB X}, L.IsLB → ∀ F : Y ⟶ X, (L.pull F).IsLB := by
    intro X Y L hL F
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
        gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  obtain ⟨hdvr, hc, hch⟩ := (GlobalTheory.LN.cDvr_iff W).1 hW
  haveI := hch
  obtain ⟨D, A, U, hl, -⟩ := Z.unif W inferInstance inferInstance hc (ξ ≫ h) hab
  have hpt : (pullback.snd Z.G.hom (ξ ≫ h) ≫ ξ) ≫ h = pullback.snd Z.G.hom (ξ ≫ h) ≫ ξ ≫ h := Category.assoc _ _ _
  let β : pullback Z.G.hom (ξ ≫ h) ⟶ pullback Z.G.hom h :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ ξ) (pullback.condition.trans hpt.symm)
  have hβf : β ≫ pullback.fst Z.G.hom h = pullback.fst Z.G.hom (ξ ≫ h) := pullback.lift_fst _ _ _
  have hβs : β ≫ pullback.snd Z.G.hom h = pullback.snd Z.G.hom (ξ ≫ h) ≫ ξ := pullback.lift_snd _ _ _
  refine ⟨(Over.pullback (ξ ≫ h)).obj Z.G, inferInstance, inferInstance, β, D, A, U, ?_, ?_⟩
  · refine (isGrpPullback_pullback Z.G h).cancel ?_ hβs
    exact (isGrpPullback_pullback Z.G (ξ ≫ h)).congr rfl hβf.symm
  · exact LBIso.trans U.LG.isLB (pull_isLB Z.L.isLB _) (pull_isLB (pull_isLB Z.L.isLB _) _) hl
      (GlobalTheory.GenSpread.lbIso_pull_pull Z.L.isLB β hβf.symm)

end GlobalTheory.Mum.CoverPull

namespace GlobalTheory.Mum

theorem exists_uCover_of_zhOut : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → GlobalTheory.ZH.ZHOut ρS M U₀ EE → ∀ (b : o →+* R₁) (e : Ω →+* FractionRing R₁), (∀ x : o, e (algebraMap o Ω x) = algebraMap R₁ (FractionRing R₁) (b x)) → ∀ (A₁ : PolAV (Sp (FractionRing R₁))) (φ : A₁.A.left ⟶ ρS.P.A.left), IsGrpPullback A₁.A ρS.P.A (spMap (e.comp S.R.val.toRingHom)) φ → LBIso A₁.L (ρS.P.L.pull φ) → ∃ C : UCover R₁, C.A = A₁ := by
  intro R₁ _ _ _ o Ω _ _ _ _ S ρS M U₀ EE hO Z b e hb A₁ φ hcart hlb
  have pull_isLB : ∀ {X Y : Scheme.{0}} {L : LB X}, L.IsLB → ∀ F : Y ⟶ X, (L.pull F).IsLB := by
    intro X Y L hL F
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
        gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  have hs : IsProper M.s := GlobalTheory.SpreadAb.isProper_of_isProjOver hO.proj
  have hy : (spMap e ≫ M.pt) ≫ M.s = jK R₁ ≫ spMap b := by
    rw [Category.assoc, M.pt_s, jK, spMap, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact hb x
  obtain ⟨M', h, hgp, -⟩ := GlobalTheory.T.exists_modification_closure_of_graph R₁ o b M.Z M.s hs _ hy
  obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.exists_cubicalStructure_semiAbelianExtension o Ω S ρS M U₀ EE hO Z
  have hw : pullback.fst Z.G.hom h ≫ Z.G.hom = ((Over.pullback h).obj Z.G).hom ≫ h := pullback.condition
  have mul : ∀ (T : Over M'.S) (x y : T ⟶ (Over.pullback h).obj Z.G), toBase hw (x * y) = toBase hw x * toBase hw y := by
    intro T x y
    exact Over.OverMorphism.ext ((isGrpPullback_pullback Z.G h).2 T x y (toBase hw x) (toBase hw y) rfl rfl).symm
  obtain ⟨rig, hr, c, s, h₁, h₂, h₃, -⟩ := GlobalTheory.UU.exists_isCPMap P₀ mul _ (pull_isLB P₀.L.isLB _) _
    (GlobalTheory.UU.pullIso_isGen P₀.L.isLB _)
  obtain ⟨α, hα, hαl⟩ := GlobalTheory.T.genericFibre_pulled_semiAbelian_eq_abelianVariety R₁ o Ω S ρS M U₀ EE hO Z e M' h hgp A₁ φ hcart hlb
  refine ⟨{ toModif := M'
            G := (Over.pullback h).obj Z.G
            semi := by
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
              · have := Z.semi.comm; infer_instance
              · have := Z.semi.smooth; change Smooth (pullback.snd Z.G.hom h); infer_instance
              · have := Z.semi.separated; change IsSeparated (pullback.snd Z.G.hom h); infer_instance
              · have := Z.semi.quasiCompact; change QuasiCompact (pullback.snd Z.G.hom h); infer_instance
              · have := Z.semi.geomConnected; change GeometricallyConnected (pullback.snd Z.G.hom h); infer_instance
              · intro K _ _ q
                obtain ⟨E⟩ := Z.semi.fibres K (q ≫ h)
                let em : (Over.pullback (q ≫ h)).mapMon.obj (Mon.mk Z.G) ≅
                    (Over.pullback q).mapMon.obj ((Over.pullback h).mapMon.obj (Mon.mk Z.G)) :=
                  (Functor.mapMonNatIso (Over.pullbackComp q h) ≪≫ Functor.mapMonCompIso).app (Mon.mk Z.G)
                let e : (Over.pullback (q ≫ h)).obj Z.G ≅ (Over.pullback q).obj ((Over.pullback h).obj Z.G) :=
                  (Mon.forget _).mapIso em
                haveI : IsMonHom e.hom := by
                  show IsMonHom em.hom.hom
                  infer_instance
                haveI := E.grpB
                haveI := E.q_hom
                haveI := E.i_hom
                haveI : IsIso e.inv.left := Functor.map_isIso (Over.forget _) e.inv
                refine ⟨{ X := E.X
                          addCommGroup := E.addCommGroup
                          free := E.free
                          finite := E.finite
                          B := E.B
                          grpB := E.grpB
                          isAbelian := E.isAbelian
                          q := e.inv ≫ E.q
                          q_hom := inferInstance
                          q_flat := by rw [Over.comp_left]; have := E.q_flat; infer_instance
                          q_surjective := by rw [Over.comp_left]; have := E.q_surjective; infer_instance
                          q_quasiCompact := by rw [Over.comp_left]; have := E.q_quasiCompact; infer_instance
                          i := E.i ≫ e.hom
                          i_hom := inferInstance
                          isKernel := ?_ }⟩
                refine IsPullback.of_iso E.isKernel (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp
            P := ⟨⟨_, rig, pull_isLB P₀.L.isLB _, hr⟩, c, s, h₁, h₂, h₃⟩
            A := A₁
            α := α
            α_cart := hα
            α_lb := by
              show LBIso A₁.L ((P₀.L.L.pull (pullback.fst Z.G.hom h)).pull α)
              rw [hP₀]; exact hαl
            trait := ?_ }, rfl⟩
  intro W _ _ _ hW φW ξ hφ hξ
  obtain ⟨w, k, hk⟩ := GlobalTheory.T.exists_genericPoint_of_lies_over_generic R₁ M' W φW ξ hφ hξ
  have hab : ((ξ ≫ h) ⁻¹' abLocus Z.G).Nonempty := by
    refine ⟨w, ?_⟩
    have e1 : (ξ ≫ h) w = M.pt ((spMap e) k) := by
      rw [Scheme.Hom.comp_apply, hk, ← Scheme.Hom.comp_apply, hgp, Scheme.Hom.comp_apply]
    show (ξ ≫ h) w ∈ abLocus Z.G
    rw [e1]
    exact CoverPull.pt_mem_abLocus o Ω S ρS M U₀ EE hO Z _
  obtain ⟨G', iG, cG, β, D', A', U', hβ, hl⟩ := CoverPull.exists_unif_pullback o Ω S ρS M U₀ EE Z M'.S h W hW ξ hab
  have hid : spMap (RingHom.id W) ≫ ξ = ξ := by
    rw [spMap, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  refine ⟨W, _, inferInstance, inferInstance, RingHom.id W, G', iG, cG, β, D', A', U', hW, Function.injective_id,
    RingHom.Finite.id W, hid.symm ▸ hβ, ?_⟩
  show LBIso U'.LG.L ((P₀.L.L.pull (pullback.fst Z.G.hom h)).pull β)
  rw [hP₀]; exact hl

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart

def isoVal {S S₁ S' : Scheme.{0}} {B : Over S} {B₁ : Over S₁} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B₁]
    [IsCommMonObj B₁] [GrpObj B'] {M : LB B.left} {M₁ : LB B₁.left} {β₂ : (G2 B').left ⟶ (G2 B).left}
    {β₂' : (G2 B').left ⟶ (G2 B₁).left} (w : LB.Iso ((abelian₂ B M).pull β₂) ((abelian₂ B₁ M₁).pull β₂'))
    {Z : Scheme.{0}} (p : Z ⟶ (G2 B').left) (z : Z) (J : (Z ⟶ B₁.left) → M₁.ι) (J' : (Z ⟶ B.left) → M.ι) :
    (Z.presheaf.stalk z)ˣ :=
  gm p z _ (w.s (fun _ I => J (p ≫ β₂' ≫ (psum B₁ (x2 B₁) I.down).left),
    fun _ I => J' (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)))

def IsNormIso {R : Type} [CommRing R] [IsDomain R] {S S₁ : Scheme.{0}} {B : Over S} {B₁ : Over S₁} {B' : Over (Sp R)}
    [GrpObj B] [IsCommMonObj B] [GrpObj B₁] [IsCommMonObj B₁] [GrpObj B'] {M : LB B.left} {M₁ : LB B₁.left}
    {β₂ : (G2 B').left ⟶ (G2 B).left} {β₂' : (G2 B').left ⟶ (G2 B₁).left}
    (w : LB.Iso ((abelian₂ B M).pull β₂) ((abelian₂ B₁ M₁).pull β₂')) : Prop :=
  ∀ z J J', Good M₁ z J → Good M z J' → isoVal w (lift (1 : TK R ⟶ B') (1 : TK R ⟶ B')).left z J J' = 1

def PeriodRel {o V V₁ W : Type} [CommRing o] [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [CommRing W]
    [IsLocalRing W] (D : DegPre V) (T : TautBase o W) (f₁ : V →+* V₁) (κ₁ : W →+* V₁) {B' : Over (Sp V₁)} [GrpObj B']
    {β₂ : (G2 B').left ⟶ (G2 D.P.A).left} {β₂' : (G2 B').left ⟶ (G2 T.B).left}
    (w : LB.Iso ((abelian₂ D.P.A D.P.L).pull β₂) ((abelian₂ T.B T.M.L).pull β₂')) (c : (Fin T.r → ℤ) ≃+ D.X)
    (x : (Fin T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')) (n : ℕ) (q : (Fin T.r → ℤ) → (Fin T.r → ℤ) → (FractionRing V₁)ˣ) :
    Prop :=
  ∀ κK : (TK V₁).left ⟶ (TK V).left, κK ≫ jK V = jK V₁ ≫ spMap f₁ → ∀ a b z J J', Good T.M.L z J → Good D.P.L z J' →
    val (D.tau (c a) (c b)) κK z J' = gm (𝟙 (TK V₁).left) z ⊤ (unitOn (q a b)) *
      (isoVal w (lift (toUnit (TK V₁) ≫ x a) (toUnit (TK V₁) ≫ x b)).left z J J' *
        val (T.τ₀ ((n : ℤ) • a) ((n : ℤ) • b)) ((TK V₁).hom ≫ spMap κ₁) z J)

end GlobalTheory.TChart
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem spMap_comp_tfk {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]
    (em : Kb R →ₐ[FractionRing R] F) :
    spMap em.toRingHom ≫ (TFK (R := R) (Kb R)).hom = (TFK (R := R) F).hom := by
  simp only [TFK, Over.mk_hom, jFK]
  rw [← Spec.map_comp]
  congr 1
  ext x
  simp

theorem Trait.exists_lab_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∃ lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A), (∀ p', QkToAkU T.U.toUnifPre F (C.n ^ j) p' (lab' p')) ∧ ∀ (p : QkPt D.toPre (Kb R) (C.n ^ j)) (p₁ : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), QkExt em.toRingHom p p₁ → p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g → (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = spMap em.toRingHom ≫ (C.lab j p).left ≫ C.α := by
  intro R _ _ _ hR D C j W _ _ _ T F _ _ _ _ em hF f hfi hf1 hf2
  have : CharZero R := hR.2
  have hN : 1 ≤ C.n ^ j := Nat.one_le_pow _ _ C.n_prime.pos
  have hbij := qkPt_algClosure_bijective R D.toPre F em (C.n ^ j) hN
  have hpull : ∀ p' : QkPt T.D'.toPre F (C.n ^ j), ∃ p₁ : QkPt D.toPre F (C.n ^ j),
      p'.y = T.hD.xe.symm p₁.y ∧ IsPullGtF T.φ T.hD F p₁.g p'.g := fun p' =>
    qkPullExists GlobalTheory.globalFns_holds R W T.φ D.toPre T.D'.toPre T.hD F hF (C.n ^ j) p'
  have huniq : ∀ (p' : QkPt T.D'.toPre F (C.n ^ j)) (p₁ p₂ : QkPt D.toPre F (C.n ^ j)),
      p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g →
      p'.y = T.hD.xe.symm p₂.y → IsPullGtF T.φ T.hD F p₂.g p'.g → p₁ = p₂ :=
    fun p' p₁ p₂ h₁ g₁ h₂ g₂ => GlobalTheory.TorusExt.qk_ext (T.hD.xe.symm.injective (h₁.symm.trans h₂))
      (GlobalTheory.ArcPull.pullGt_unique' T.hD g₁ g₂)
  choose P₁ hP₁ using hpull
  choose P hP using fun p' => (hbij.2 (P₁ p')).exists

  let y : QkPt D.toPre (Kb R) (C.n ^ j) → (TFK (R := R) F ⟶ C.A.A) := fun p =>
    Over.homMk (spMap em.toRingHom ≫ (C.lab j p).left) (by
      rw [Category.assoc, Over.w, spMap_comp_tfk])
  let g : QkPt D.toPre (Kb R) (C.n ^ j) → (TFK (R := R) F ⟶ TFK (R := R) F ⊗ C.A.A) := fun p => lift (𝟙 _) (y p)
  have hg1 : ∀ p, (g p).left ≫ (fst (TFK (R := R) F) C.A.A).left = 𝟙 _ := fun p => by
    rw [← Over.comp_left, lift_fst]; rfl
  have hg2 : ∀ p, (g p).left ≫ (snd (TFK (R := R) F) C.A.A).left = spMap em.toRingHom ≫ (C.lab j p).left := fun p => by
    rw [← Over.comp_left, lift_snd]; rfl
  have hfst : inv f ≫ (fst (TFK (R := W) F) T.A.A).left = (fst (TFK (R := R) F) C.A.A).left := by
    rw [← hf1, IsIso.inv_hom_id_assoc]
  let lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A) := fun p' =>
    Over.homMk ((g (P p')).left ≫ inv f ≫ (snd (TFK (R := W) F) T.A.A).left) (by
      rw [Category.assoc, Category.assoc, Over.w (snd (TFK (R := W) F) T.A.A), ← Over.w (fst (TFK (R := W) F) T.A.A),
        reassoc_of% hfst, reassoc_of% (hg1 (P p'))])
  have heq : ∀ p', (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β =
      spMap em.toRingHom ≫ (C.lab j (P p')).left ≫ C.α := fun p' => by
    simp only [lab', Over.homMk_left, Category.assoc]
    rw [← hf2, IsIso.inv_hom_id_assoc, reassoc_of% (hg2 (P p'))]
  refine ⟨lab', fun p' => T.lab F em hF j (P p') (P₁ p') p' (lab' p') (hP p') (hP₁ p').1 (hP₁ p').2 (heq p'), ?_⟩
  intro p p₁ p' hE hy hgp
  obtain rfl : p₁ = P₁ p' := huniq p' p₁ (P₁ p') hy hgp (hP₁ p').1 (hP₁ p').2
  obtain rfl : p = P p' := (hbij.2 (P₁ p')).unique hE (hP p')
  exact heq p'

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Trait.bijective_appTop {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) :
    Function.Bijective T.G.hom.appTop.hom := by
  have hd : IsDiscreteValuationRing W := T.cdvr.1
  have := T.U.smooth
  have := T.U.separated
  have := C.semi.quasiCompact
  have : QuasiCompact T.G.hom := MorphismProperty.of_isPullback (P := @QuasiCompact) T.cart.1 this
  exact GlobalFunctionsDvrGeneric.bij_of_generic T.G
    (GlobalFunctionsDvrPowers.bijective_of_iso T.U.gen (GlobalTheory.allSixLaws.1.globalFns _ T.A.A T.A.isAb))

theorem Trait.exists_unit_scal {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (c : Γ(T.G.left, ⊤)ˣ) :
    ∃ v : Wˣ, scal T.G.hom (v : W) = c.val := by
  let e : W ≃+* Γ(T.G.left, ⊤) := RingEquiv.ofBijective
    (T.G.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom)
    (T.bijective_appTop.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of W)).inv))
  exact ⟨Units.map e.symm.toMonoidHom c, e.apply_symm_apply c.val⟩

theorem Trait.carries_mulPull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (m : ℕ)
    (u : LB.Gen (LB.LinComb C.P.L.L (K := Fin 2) ![𝟙 C.G.left, (mulA C.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])),
    u.IsGen →
    ∀ (uG : LB.Gen (LB.LinComb T.U.LG.L (K := Fin 2) ![𝟙 T.G.left, (mulA T.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])),
    uG.IsGen → ∀ (b : W) (σ' : H0 T.U.LG.L 1) (σ : SecK C.P.L.L T.β 1), T.Carries b σ' σ →
    ∀ (σ₂ : SecK C.P.L.L T.β (m ^ 2)) (σ'' : H0 T.U.LG.L (m ^ 2)),
    (∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J →
      sval σ₂ r z J = (val u (r ≫ T.β) z J).val * sval σ (r ≫ (mulA T.G m).left) z J) →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) (J : (Z ⟶ T.G.left) → T.U.LG.L.ι), Good T.U.LG.L z J →
      sval σ'' r z J = (val uG (r ≫ 𝟙 _) z J).val * sval σ' (r ≫ (mulA T.G m).left) z J) →
    ∃ v : Wˣ, T.Carries (b * v) σ'' σ₂ := by
  intro R _ _ _ _ D C W _ _ _ T m u hu uG huG b σ' σ hcar σ₂ σ'' h₂ h''
  have hm := GlobalTheory.ZH.TorsFrame.mulA_comm T.cart m
  obtain ⟨a, ha, hP⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_gen_move C.P.L.isLB T.U.LG.isLB T.ℓ ((isGen_iff _).1 T.ℓ_gen)
    (K := Fin 2) ![𝟙 C.G.left, (mulA C.G m).left] ![𝟙 T.G.left, (mulA T.G m).left]
    ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)] T.β (fun k => by
      fin_cases k
      · exact (Category.id_comp _).trans (Category.comp_id _).symm
      · exact hm) u hu
  obtain ⟨c, hc⟩ := GlobalTheory.ZM.Coord.exists_global_unit (DVR.linComb_isLB _ T.U.LG.isLB _ _) ha huG
  obtain ⟨v, hv⟩ := T.exists_unit_scal c
  refine ⟨v, fun Z r z J J' hJ hJ' => ?_⟩
  have e₁ : (r ≫ T.β) ≫ (mulA C.G m).left = (r ≫ (mulA T.G m).left) ≫ T.β := by
    rw [Category.assoc, Category.assoc, hm]
  have hp : val u (r ≫ T.β) z J = (gw T.ℓ r z (J (r ≫ T.β)) (J' r) ^ (m ^ 2) *
      (gw T.ℓ (r ≫ (mulA T.G m).left) z (J ((r ≫ (mulA T.G m).left) ≫ T.β)) (J' (r ≫ (mulA T.G m).left)))⁻¹) *
      val a r z J' := by
    refine (hP Z r z _ _ (fun k => ?_) (fun k => hJ' (r ≫ _))).trans ?_
    · fin_cases k
      · exact hJ ((r ≫ T.β) ≫ 𝟙 _)
      · have := hJ ((r ≫ T.β) ≫ (mulA C.G m).left)
        exact (congrArg (fun q => q z ∈ C.P.L.L.U (J ((r ≫ T.β) ≫ (mulA C.G m).left))) e₁).mp this
    · refine congrArg (· * val a r z J') ?_
      rw [Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, e₁, zpow_natCast, zpow_neg, pow_one]
  have hq : val a r z J' = gm r z ⊤ c * val uG r z J' := by
    have hm' := hJ'.mem ![𝟙 T.G.left, (mulA T.G m).left] r
    exact (congrArg (gm r z _) (hc _)).trans ((map_mul _ _ _).trans (congrArg (· * val uG r z J') (gm_res r z _ hm' _)))
  have hs : gs (r ≫ (mulA T.G m).left) z ⊤ (scal T.G.hom b) = gs r z ⊤ (scal T.G.hom b) := by
    refine (gs_pull r (mulA T.G m).left z ⊤ trivial _).symm.trans (congrArg (gs r z ⊤) ?_)
    show ((mulA T.G m).left ≫ T.G.hom).appTop.hom _ = _
    rw [Over.w]; rfl
  have hbv : gs r z ⊤ (scal T.G.hom (b * v)) = gs r z ⊤ (scal T.G.hom b) * (gm r z ⊤ c).val := by
    rw [← gs_unit r z ⊤ trivial, ← hv, ← gs_mul r z ⊤ trivial, scal, scal, scal, map_mul, map_mul]
  rw [h₂ Z r z J hJ, h'' Z r z J' hJ', hcar Z _ z J J' hJ hJ', hp, hq, hs, hbv, Category.comp_id, pow_one]
  generalize gw T.ℓ (r ≫ (mulA T.G m).left) z _ _ = g
  simp only [Units.val_mul]
  linear_combination (gs r z ⊤ (scal T.G.hom b) * (gm r z ⊤ c).val * (gw T.ℓ r z (J (r ≫ T.β)) (J' r) ^ (m ^ 2)).val *
    (val uG r z J').val * sval σ' (r ≫ (mulA T.G m).left) z J') * g.inv_mul

end GlobalTheory.Mum
end
