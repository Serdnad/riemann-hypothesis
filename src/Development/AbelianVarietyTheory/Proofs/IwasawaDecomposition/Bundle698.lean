module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle206
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle687
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle684
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle688
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle658
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008

@[expose] public section

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

namespace GlobalTheory.PointChern

open GlobalTheory.HermFrame Matrix
open scoped ComplexOrder

theorem mContDiffAt_coordOf {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {n : ℕ}
    (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (σ : GlobalTheory.AllWt.Psi H) (w : ReciprocityTheory.L2DbarEstimates.V n) :
    MContDiffAt 2 (fun u => coordOf ix u σ) w := fun a b => by
  have : (fun u : ReciprocityTheory.L2DbarEstimates.V n => coordOf ix u σ a b) =
      ((EuclideanSpace.proj (𝕜 := ℂ) (ix.symm (σ, a, b))).restrictScalars ℝ) := by
    funext u; rfl
  rw [this]
  exact ContinuousLinearMap.contDiff _ |>.contDiffAt

theorem one_sub_map_conj_mul_transpose {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) :
    (1 - z.map (starRingEnd ℂ) * zᵀ) = (1 - z * zᴴ)ᵀ := by
  ext a b
  simp [Matrix.mul_apply, Matrix.one_apply, Matrix.sub_apply, eq_comm, mul_comm]

theorem isUnit_det_one_sub_map_conj {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) (h : (1 - zᴴ * z).PosDef) :
    IsUnit (1 - z.map (starRingEnd ℂ) * zᵀ).det := by
  rw [one_sub_map_conj_mul_transpose, det_transpose, det_one_sub_mul_comm]
  exact (h.det_pos.ne').isUnit

theorem isUnit_det_one_sub_conjTranspose {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) (h : (1 - zᴴ * z).PosDef) :
    IsUnit (1 - zᴴ * z).det :=
  (h.det_pos.ne').isUnit

theorem MContDiffAt.map_conj {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {m n : Type*} {k : WithTop ℕ∞}
    {A : V → Matrix m n ℂ} {z : V} (h : MContDiffAt k A z) :
    MContDiffAt k (fun x => (A x).map (starRingEnd ℂ)) z :=
  fun a b => Complex.conjCLE.contDiff.contDiffAt.comp z (h a b)

end GlobalTheory.PointChern

namespace GlobalTheory.PointChern
open GlobalTheory.HermFrame Matrix
open scoped ComplexOrder

theorem modelGram_smooth_isUnit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (w : ReciprocityTheory.L2DbarEstimates.V n), InDom (coordOf ix w) → ∀ τ, MContDiffAt 2 (fun u => modelGram H Dw (coordOf ix u) τ) w ∧ IsUnit (modelGram H Dw (coordOf ix w) τ).det := by
  intro E _ _ _ H Dw n ix w hw τ
  by_cases h : τ (H.rt : E) = H.rt0
  · have hZ := mContDiffAt_coordOf ix ⟨τ, h⟩ w
    have hA : MContDiffAt 2 (fun u => 1 - (coordOf ix u ⟨τ, h⟩).map (starRingEnd ℂ) * (coordOf ix u ⟨τ, h⟩)ᵀ) w :=
      (mContDiffAt_const 1).sub ((GlobalTheory.PointChern.MContDiffAt.map_conj hZ).mul hZ.transpose)
    have hu := isUnit_det_one_sub_map_conj _ (hw ⟨τ, h⟩)
    simp only [modelGram, dif_pos h]
    refine ⟨?_, ?_⟩
    · simp only [reindex_apply]
      exact (hA.inv hu).submatrix _ _
    · rw [det_reindex_self]
      exact isUnit_nonsing_inv_det_iff.mpr hu
  · by_cases h' : conjEmb τ (H.rt : E) = H.rt0
    · have hZ := mContDiffAt_coordOf ix ⟨conjEmb τ, h'⟩ w
      have hA : MContDiffAt 2 (fun u => 1 - (coordOf ix u ⟨conjEmb τ, h'⟩)ᴴ * coordOf ix u ⟨conjEmb τ, h'⟩) w :=
        (mContDiffAt_const 1).sub (hZ.conjTranspose.mul hZ)
      have hu := isUnit_det_one_sub_conjTranspose _ (hw ⟨conjEmb τ, h'⟩)
      simp only [modelGram, dif_neg h, dif_pos h']
      refine ⟨?_, ?_⟩
      · simp only [reindex_apply]
        exact (hA.inv hu).submatrix _ _
      · rw [det_reindex_self]
        exact isUnit_nonsing_inv_det_iff.mpr hu
    · simp only [modelGram, dif_neg h, dif_neg h']
      exact ⟨mContDiffAt_const 1, by simp⟩

end GlobalTheory.PointChern
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_bundleSquare_section_weightZero_nonzero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), ∃ (σ : H0 U.LG.L 2) (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α), (∀ e : ℕ, U.ExpandsAt e 2 σ f) ∧ ¬ ∀ j, (f 0).f j = 0 := by
  first | exact @GlobalTheory.SquareSectionWeightZero.main | exact GlobalTheory.SquareSectionWeightZero.main | (intros; apply GlobalTheory.SquareSectionWeightZero.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_uniformisation_baseChange_with_coordinates : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN R → IsCN V → ∀ ψ : R →+* V, IsLocalHom ψ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (W : Set (Sp R)), IsOpen W → (∀ y, PsiUnitOn D.toPre y W) → (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum R) ∈ W → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap ψ) β → IsAbelianScheme ((Over.pullback (jK V)).obj G') → Rigidified ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → Out.Sym ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → RelAmple ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → KTriv ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → ∃ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (ε : D'.toPre.X ≃+ D.toPre.X), LBIso (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) (U'.LG.L.pull (pullback.fst G'.hom (jK V))) ∧ ∀ y r, PsiCoord D.toPre (ε y) r → ∃ u : Vˣ, PsiCoord D'.toPre y (u * ψ r) := by
  first | exact @GlobalTheory.UnifCoordPull.exists_unif_psiCoord | exact GlobalTheory.UnifCoordPull.exists_unif_psiCoord | (intros; apply GlobalTheory.UnifCoordPull.exists_unif_psiCoord <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.abelianPart_section_sq_eq_of_thickening_points : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) → ∀ (α : D.toPre.X) (α' : D'.toPre.X), (∀ κ, D'.toPre.famφB α' κ ≫ Φ.hom.left = Φ.hom.left ≫ D.toPre.famφB α κ) → ∀ (s : D.toPre.SecB 2 α) (s' : D'.toPre.SecB 2 α'), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → sval s (r ≫ (U.gt e).pG.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left ≫ D'.toPre.famφB α' κ) ^ DegPre.famε 2 κ).val * sval s' (r ≫ (U'.gt e).pG.left) z J' ^ 2) → ∀ (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → sval s (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB α' κ) ^ DegPre.famε 2 κ).val * sval s' ρ z J' ^ 2 := by
  first | exact @GlobalTheory.sq_corr_of_thickenings | exact GlobalTheory.sq_corr_of_thickenings | (intros; apply GlobalTheory.sq_corr_of_thickenings <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.cubicalStructure_square_transport : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (D D' : DegData R (maximalIdeal R)), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → ∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → ∀ (Ω : (T ⟶ D'.toPre.P.A) → (T.left.presheaf.stalk z)ˣ), Ω = (fun x => ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) x.left) → ∀ (a b c : T ⟶ D'.toPre.P.A), cubV D.toPre.cub z J (a ≫ Φ.hom) (b ≫ Φ.hom) (c ≫ Φ.hom) ^ 2 = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ * cubV D'.toPre.cub z J' a b c ^ 2 := by
  first | exact @GlobalTheory.cube_sq_transport | exact GlobalTheory.cube_sq_transport | (intros; apply GlobalTheory.cube_sq_transport <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.polarisedAbelianPart_iso_of_bundleSquare_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) → ∃ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)) (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen ∧ wL.IsGen ∧ IsMonHom Φ.hom ∧ ∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left (r z) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U'.LG.L.U jL' → gw w (r ≫ (U'.gt e).pG.left) z (fun _ => jM) (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 = gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL') := by
  first | exact @GlobalTheory.unif_sq_polarised_iso | exact GlobalTheory.unif_sq_polarised_iso | (intros; apply GlobalTheory.unif_sq_polarised_iso <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_bundleSquare_section_transport_expansion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen → ∀ (σ : H0 U.LG.L 2), ∃ (σ' : H0 U'.LG.L 2) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ e : ℕ, U'.ExpandsAt e 2 σ' f') ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι) (J' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z J → Good U'.LG.L z J' → sval σ r z J = (gv wL r z (fun _ => J r) (fun _ => J' r)).val * sval σ' r z J') := by
  first | exact @GlobalTheory.SqTransport.exists_transport_expansion | exact GlobalTheory.SqTransport.exists_transport_expansion | (intros; apply GlobalTheory.SqTransport.exists_transport_expansion <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.degenerationCharMap_eq_on_even_characters : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) → ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → ∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x)) := by
  first | exact @GlobalTheory.SqCompare.c_two_comp | exact GlobalTheory.SqCompare.c_two_comp | (intros; apply GlobalTheory.SqCompare.c_two_comp <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem eq_on_ball_of_eq_on_logExp_image : ∀ (n a : ℕ) (ρ₁ : ℝ) (X : Type) [TopologicalSpace X] [T2Space X] (f h : (Fin n → ℂ) → X), ρ₁ ≤ 1 → ContinuousOn f (Metric.ball 0 ρ₁) → ContinuousOn h (Metric.ball 0 ρ₁) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → f (logExp a s) = h (logExp a s)) → ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, f z = h z := by
  intro n a ρ₁ X _ _ f h hρ hf hh hagree
  set U := Metric.ball (0 : Fin n → ℂ) ρ₁ with hUdef
  set D : Set (Fin n → ℂ) := {z | z ∈ U ∧ ∀ k : Fin n, (k:ℕ) < a → z k ≠ 0} with hDdef
  have hD : Set.EqOn f h D := by
    rintro z ⟨hzU, hz0⟩
    set s : Fin n → ℂ := fun k => if (k:ℕ) < a then Complex.log (z k) else z k with hsdef
    have hexp : logExp a s = z := by
      funext k
      simp only [logExp, s]
      split_ifs with hk
      · exact Complex.exp_log (hz0 k hk)
      · rfl
    have hz1 : ‖z‖ < ρ₁ := by simpa [U] using hzU
    have hnorm : ∀ k, ‖z k‖ < 1 := fun k =>
      lt_of_le_of_lt (norm_le_pi_norm z k) (lt_of_lt_of_le hz1 hρ)
    have hs : s ∈ logDom n a := by
      intro k
      simp only [s]
      split_ifs with hk
      · rw [Complex.log_re]
        exact Real.log_neg (norm_pos_iff.mpr (hz0 k hk)) (hnorm k)
      · exact hnorm k
    have := hagree s hs (by rw [hexp]; exact hzU)
    rwa [hexp] at this
  have hsub : U ⊆ closure D := by
    intro z hz
    let g : ℂ → (Fin n → ℂ) := fun t k => if (k:ℕ) < a then z k + t else z k
    have hg : Continuous g := by
      refine continuous_pi fun k => ?_
      by_cases hk : (k:ℕ) < a
      · simp only [g, hk, if_true]; fun_prop
      · simp only [g, hk, if_false]; fun_prop
    let T : Set ℂ := Set.range (fun k : Fin n => - z k)
    have hT : T.Finite := Set.finite_range _
    have hS : Dense (Set.univ \ T) := dense_univ.diff_finite hT
    have h0 : g 0 = z := by funext k; simp [g]
    have h1 : z ∈ closure (g '' (Set.univ \ T)) := by
      rw [← h0]
      exact image_closure_subset_closure_image hg
        (Set.mem_image_of_mem g (by rw [hS.closure_eq]; exact Set.mem_univ _))
    have h2 : U ∩ g '' (Set.univ \ T) ⊆ D := by
      rintro _ ⟨hU, t, ⟨-, htT⟩, rfl⟩
      refine ⟨hU, fun k hk => ?_⟩
      simp only [g, hk, if_true]
      intro heq
      exact htT ⟨k, by linear_combination -heq⟩
    exact closure_mono h2 (Metric.isOpen_ball.inter_closure ⟨hz, h1⟩)
  exact fun z hz => hD.of_subset_closure hf hh (fun x hx => hx.1) hsub hz

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodFrame

private theorem differentiableOn_finsetProd' {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {Idx : Type}
    (u : Finset Idx) (f : Idx → E → ℂ) {S : Set E} (h : ∀ i ∈ u, DifferentiableOn ℂ (f i) S) :
    DifferentiableOn ℂ (fun s => ∏ i ∈ u, f i s) S := by
  classical
  revert h
  refine Finset.induction_on u ?_ ?_
  · intro _
    simp only [Finset.prod_empty]
    exact differentiableOn_const _
  · intro a u ha ih h
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a u)).fun_mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem differentiableOn_det_of_entries {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
    {M : E → Matrix (Fin g) (Fin g) ℂ} {S : Set E} (h : ∀ i j, DifferentiableOn ℂ (fun s => M s i j) S) :
    DifferentiableOn ℂ (fun s => (M s).det) S := by
  have hdet : (fun s => (M s).det) = fun s => ∑ σ : Equiv.Perm (Fin g),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M s (σ i) i := by
    funext s
    exact Matrix.det_apply' (M s)
  rw [hdet]
  apply DifferentiableOn.fun_sum
  intro σ _
  apply DifferentiableOn.const_mul
  exact differentiableOn_finsetProd' Finset.univ (fun i s => M s (σ i) i) (fun i _ => h (σ i) i)

theorem differentiableOn_inv_of_entries {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
    {M : E → Matrix (Fin g) (Fin g) ℂ} {S : Set E} (h : ∀ i j, DifferentiableOn ℂ (fun s => M s i j) S)
    (hu : ∀ s ∈ S, IsUnit (M s).det) (i j : Fin g) :
    DifferentiableOn ℂ (fun s => (M s)⁻¹ i j) S := by
  have hdet : DifferentiableOn ℂ (fun s => (M s).det) S := differentiableOn_det_of_entries h
  have hadj : DifferentiableOn ℂ (fun s => (M s).adjugate i j) S := by
    have hupd : ∀ k l, DifferentiableOn ℂ (fun s => ((M s).updateRow j (Pi.single i 1)) k l) S := by
      intro k l
      by_cases hk : k = j
      · subst hk
        simp only [Matrix.updateRow_self]
        exact differentiableOn_const _
      · simp only [Matrix.updateRow_ne hk]
        exact h k l
    have := differentiableOn_det_of_entries hupd
    simpa only [Matrix.adjugate_apply] using this
  have hinv : DifferentiableOn ℂ (fun s => ((M s).det)⁻¹) S :=
    hdet.fun_inv fun s hs => (hu s hs).ne_zero
  have heq : (fun s => (M s)⁻¹ i j) = fun s => ((M s).det)⁻¹ * (M s).adjugate i j := by
    funext s
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [heq]
  exact hinv.fun_mul hadj

theorem differentiableOn_combMat_of_entries {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g r : ℕ}
    {l : E → Fin r → Fin g → ℂ} {S : Set E} (ε : Matrix (Fin g) (Fin r) ℚ)
    (h : ∀ m k, DifferentiableOn ℂ (fun s => l s m k) S) (i j : Fin g) :
    DifferentiableOn ℂ (fun s => combMat (l s) ε i j) S := by
  simp only [combMat, Matrix.of_apply]
  apply DifferentiableOn.fun_sum
  intro m _
  exact (h m i).const_mul _

theorem differentiableOn_combMat_perTau : ∀ (n a g r₀ r : ℕ) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (D : ℕ), AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ (j : Fin r) (k : Fin g), DifferentiableOn ℂ (fun s => lam s j k) (logDom n a)) → (∀ s ∈ logDom n a, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det) → (∀ i j, DifferentiableOn ℂ (fun z => GlobalTheory.PeriodFrame.combMat (ζ z) α i j) (Metric.ball 0 1)) ∧ ∀ i j, DifferentiableOn ℂ (fun s => GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1} := by
  intro n a g r₀ r ζ lam α φ D hζ hlam hunit
  have hζd : DifferentiableOn ℂ ζ (Metric.ball 0 1) := hζ.differentiableOn
  have hζe : ∀ m k, DifferentiableOn ℂ (fun z => ζ z m k) (Metric.ball 0 1) := by
    intro m k
    have h1 := differentiableOn_pi.1 hζd m
    exact differentiableOn_pi.1 h1 k
  have hA : ∀ i j, DifferentiableOn ℂ (fun z => combMat (ζ z) α i j) (Metric.ball 0 1) :=
    fun i j => differentiableOn_combMat_of_entries α hζe i j
  refine ⟨hA, ?_⟩
  intro i j
  set T : Set (Fin n → ℂ) := {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1} with hT
  have hexp : Differentiable ℂ (fun s : Fin n → ℂ => logExp a s) := by
    refine differentiable_pi.2 fun k => ?_
    simp only [logExp]
    split_ifs
    · exact (differentiable_apply k).cexp
    · exact differentiable_apply k
  have hAT : ∀ i j, DifferentiableOn ℂ (fun s => combMat (ζ (logExp a s)) α i j) T := by
    intro i j
    exact (hA i j).comp hexp.differentiableOn (fun s hs => hs.2)
  have hinvT : ∀ i j, DifferentiableOn ℂ (fun s => (combMat (ζ (logExp a s)) α)⁻¹ i j) T :=
    differentiableOn_inv_of_entries hAT (fun s hs => hunit s hs.1)
  have hBT : ∀ i j, DifferentiableOn ℂ (fun s => combMat (lam s) φ i j) T := by
    intro i j
    exact (differentiableOn_combMat_of_entries φ hlam i j).mono (fun s hs => hs.1)
  simp only [perTau, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
  apply DifferentiableOn.const_mul
  apply DifferentiableOn.fun_sum
  intro k _
  exact (hinvT i k).fun_mul (hBT k j)

end GlobalTheory.PeriodFrame
end
