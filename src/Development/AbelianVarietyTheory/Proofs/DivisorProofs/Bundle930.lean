module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle904
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle882
public import GroundTheory.ProfiniteCohomology.CohomologicalDimension.PrimaryComponentCohomologyEqBotOfScdpLt
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CdpGaloisLeOneOfAlgebraicRatFunc
public import Mathlib.Algebra.Group.Irreducible.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle905
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RingKrullDimLeOfQuasiFinite
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Mathlib.Data.Matrix.Mul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle906
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle907
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveDivisorUnitDecomposition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle865
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle876
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle120

@[expose] public section

section

noncomputable section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta
open scoped nonZeroDivisors

namespace GlobalTheory.ZetaDenom
variable {F : Type} [Field F] [NumberField F]


open Classical in
def cls (I : Ideal (𝓞 F)) : ClassGroup (𝓞 F) := if h : I ∈ (Ideal (𝓞 F))⁰ then ClassGroup.mk0 ⟨I, h⟩ else 1


open Classical in
def wideInd (C : ClassGroup (𝓞 F)) : Ideal (𝓞 F) → ℚ := fun I => if cls I = C then 1 else 0

theorem cls_of_ne_bot {I : Ideal (𝓞 F)} (h : I ≠ ⊥) :
    cls I = ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero h⟩ := by
  rw [cls, dite_eq_left]

theorem cls_mul {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) : cls (I * J) = cls I * cls J := by
  rw [cls_of_ne_bot hI, cls_of_ne_bot hJ, cls_of_ne_bot (mul_ne_zero hI hJ), ← map_mul]
  rfl

theorem cls_span {a : 𝓞 F} (ha : a ≠ 0) : cls (Ideal.span {a}) = 1 := by
  have h : Ideal.span {a} ≠ ⊥ := by simpa using ha
  rw [cls_of_ne_bot h, ClassGroup.mk0_eq_one_iff]
  exact ⟨⟨a, rfl⟩⟩

theorem cls_span_mul {a : 𝓞 F} (ha : a ≠ 0) {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : cls (Ideal.span {a} * I) = cls I := by
  rw [cls_mul (by simpa using ha) hI, cls_span ha, one_mul]

theorem isRayFun_wideInd (𝔣 : Ideal (𝓞 F)) (C : ClassGroup (𝓞 F)) : IsRayFun 𝔣 (wideInd C) := by
  intro I J hI hJ e
  obtain ⟨a, b, ha, hb, -, -, -, e⟩ := e
  have : cls I = cls J := by rw [← cls_span_mul ha hI.1, e, cls_span_mul hb hJ.1]
  unfold wideInd
  rw [this]

theorem translate_wideInd {a : 𝓞 F} (ha : a ≠ 0) (C : ClassGroup (𝓞 F)) :
    GlobalTheory.RayZeta.translate (Ideal.span {a}) (wideInd C) = wideInd C := by
  funext I
  by_cases hI : I = ⊥
  · simp [GlobalTheory.RayZeta.translate, hI]
  · simp only [GlobalTheory.RayZeta.translate, wideInd]
    rw [cls_span_mul ha hI]

end GlobalTheory.ZetaDenom
end
end

section

open Formalism.L2.DIV NumberField

theorem _root_.GlobalTheory.T.exists_goodFamily_given_characters_multiplicityOne : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) → ∀ (P0 : Subgroup G) [Fintype P0] (ψ0 : P0 →* Kˣ), (∀ χ ∈ X, ∑ h : P0, χ (h : G) * (((ψ0 h)⁻¹ : Kˣ) : K) = (Fintype.card P0 : K)) → ∃ (S : Type) (_ : Fintype S) (Ws : S → Type) (_ : ∀ s, AddCommGroup (Ws s)) (_ : ∀ s, Module K (Ws s)) (_ : ∀ s, FiniteDimensional K (Ws s)) (τ : ∀ s, Representation K G (Ws s)), Formalism.IndefR.TransferLatticeStatement.IsGood τ ∧ (∀ χ : G → K, χ ∈ X ↔ ∃ s, Formalism.IndefR.TransferLatticeStatement.charOf (τ s) = χ) ∧ Formalism.IndefR.IndefiniteEpsilonOperator.M1 τ ⟨P0, ψ0⟩ := by
  first | exact @GlobalTheory.GoodFamilyOfChars.exists_goodFamily | exact GlobalTheory.GoodFamilyOfChars.exists_goodFamily | (intros; apply GlobalTheory.GoodFamilyOfChars.exists_goodFamily <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.isIntegral_weierstrassP_torsion_nonreal_multiplier : ∀ (L : PeriodPair) (β Ω : ℂ) (M : ℕ), MulStable L β → β.im ≠ 0 → Ω ^ 12 = latDisc L → 0 < M → (∀ P, (M : ℂ) * P ∈ L.lattice → IsIntegral ℤ (12 * (M : ℂ) ^ 2 * L.weierstrassP P / Ω ^ 2) ∧ IsIntegral ℤ ((M : ℂ) ^ 3 * L.derivWeierstrassP P / Ω ^ 3)) ∧ ∀ P Q, P ∉ L.lattice → Q ∉ L.lattice → (M : ℂ) * P ∈ L.lattice → (M : ℂ) * Q ∈ L.lattice → IsIntegral ℤ ((M : ℂ) ^ 2 * (L.weierstrassP P - L.weierstrassP Q) / Ω ^ 2) := by
  first | exact @GlobalTheory.WpFam.LatTorsVal.main | exact GlobalTheory.WpFam.LatTorsVal.main | (intros; apply GlobalTheory.WpFam.LatTorsVal.main <;> assumption)
end

section

open GroundTheory.ProfCoh

theorem _root_.GlobalTheory.T.cdp_galois_le_one_of_isAlgebraic_ratFunc : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra (RatFunc k) K] [Algebra.IsAlgebraic (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (p : ℕ), p.Prime → GroundTheory.ProfCoh.cdp p (Ω ≃ₐ[K] Ω) ≤ 1 := by
  first | (exact @GlobalTheory.TsenCD.cdp_galois_le_one_of_algebraic_ratFunc) | (exact GlobalTheory.TsenCD.cdp_galois_le_one_of_algebraic_ratFunc) | (intros; apply GlobalTheory.TsenCD.cdp_galois_le_one_of_algebraic_ratFunc  <;> assumption)
end

section

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

theorem _root_.GlobalTheory.T.natDegree_divisors_prod_distinct_monic_irreducible : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (P : ι → k[X]), (∀ c, (P c).Monic ∧ Irreducible (P c)) → Function.Injective P → (∀ a : ℕ, (∃ q : k[X], q ∣ ∏ c, P c ∧ q.natDegree = a) ↔ ∃ A : Finset ι, ∑ c ∈ A, (P c).natDegree = a) ∧ ∀ Q : ℕ → Prop, (∃ q : k[X], Irreducible q ∧ q ∣ ∏ c, P c ∧ Q q.natDegree) ↔ ∃ c, Q (P c).natDegree := by
  first | exact @GlobalTheory.Div.natDegree_divisors_prod_distinct_monic_irreducible.natDegree_divisors_prod | exact GlobalTheory.Div.natDegree_divisors_prod_distinct_monic_irreducible.natDegree_divisors_prod | (intros; apply GlobalTheory.Div.natDegree_divisors_prod_distinct_monic_irreducible.natDegree_divisors_prod <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.mem_unitComponent_of_mul_mem : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ (U : G.left.Opens) (y : G.left), (∀ z ∈ U, G.hom z = G.hom y → z ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))}) → y ∈ {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y} → y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  first | exact @GlobalTheory.mem_identityComponents_of_mul_inv | exact GlobalTheory.mem_identityComponents_of_mul_inv | (intros; apply GlobalTheory.mem_identityComponents_of_mul_inv <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_open_nbhd_section_fiber_isPreirreducible : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X), Smooth f → e ≫ f = 𝟙 _ → ∀ s : S, ∃ (U : X.Opens) (V₀ V : S.Opens) (I : Finset Γ(S, V)), V₀ ≤ V ∧ s ∈ V₀ ∧ e s ∈ U ∧ (∀ c ∈ I, s ∉ S.basicOpen c) ∧ ∀ t ∈ V₀, (∀ c ∈ I, t ∉ S.basicOpen c) → IsPreirreducible ((U : Set X) ∩ f ⁻¹' {t}) := by
  first | exact @GlobalTheory.exists_open_nbhd_section_fibre_isPreirreducible | exact GlobalTheory.exists_open_nbhd_section_fibre_isPreirreducible | (intros; apply GlobalTheory.exists_open_nbhd_section_fibre_isPreirreducible <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.WeierstrassCurve (scheme toSpec chartZ)
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ProjHol

theorem valuationRing_stalk {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Sp K)
    [hf : SmoothOfRelativeDimension 1 f] (x : X) : ValuationRing (X.presheaf.stalk x) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : GlobalTheory.IsNormalScheme X := GlobalTheory.isNormalScheme_of_smooth f
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have h : Order.coheight x ≤ 1 := by simpa using GlobalTheory.AffineCover.coheight_le_of_smooth f hf x
  rcases h.eq_or_lt with h | h
  · have := GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk h
    infer_instance
  · have h0 : Order.coheight x = 0 := by simpa using h
    have : Ring.KrullDimLE 0 (X.presheaf.stalk x) := krullDimLE_of_coheight_le h0.le
    letI := (Ring.KrullDimLE.isField_of_isDomain (R := X.presheaf.stalk x)).toField
    exact ValuationRing.of_field _

end GlobalTheory.ProjHol
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_openSubgroupScheme_of_isOpen_stable : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (Z : Set G.left), IsOpen Z → (∀ s : S, (η[G]).left s ∈ Z) → (∀ w : (G ⊗ G).left, (fst G G).left w ∈ Z → (snd G G).left w ∈ Z → (μ[G]).left w ∈ Z) → (∀ y ∈ Z, (ι[G]).left y ∈ Z) → ∃ (G₀ : Over S) (_ : GrpObj G₀) (j : G₀ ⟶ G), IsMonHom j ∧ IsOpenImmersion j.left ∧ Set.range j.left = Z := by
  first | exact @GlobalTheory.OpenSubgroup.exists_open_subgroup | exact GlobalTheory.OpenSubgroup.exists_open_subgroup | (intros; apply GlobalTheory.OpenSubgroup.exists_open_subgroup <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_nat_posDef_add_nsmul_posDef_hermitian : ∀ (g : ℕ) (H₀ Hm : Matrix (Fin g) (Fin g) ℂ),
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₀.mulVec (star z)).re) →
    ∃ n : ℕ, ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ (Hm + n • H₀).mulVec (star z)).re := by
  first | exact @GlobalTheory.posn_main | exact GlobalTheory.posn_main | (intros; apply GlobalTheory.posn_main <;> assumption)
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.torsionPoint_locally_constant_complexAbelian : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (N : ℕ), 1 ≤ N → ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ^ N = 1 →
    ∀ t : T.left, ∃ (U : T.left.Opens) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A), t ∈ U ∧ U.ι ≫ x.left = U.ι ≫ T.hom ≫ y.left := by
  first | exact @GlobalTheory.TorsionLocal.locally_eq_const_of_pow_eq_one | exact GlobalTheory.TorsionLocal.locally_eq_const_of_pow_eq_one | (intros; apply GlobalTheory.TorsionLocal.locally_eq_const_of_pow_eq_one <;> assumption)
end
end

section

open GlobalTheory.EtC

theorem _root_.GlobalTheory.T.smoothAffineCurve_divisor_unit_decomposition : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ b : B, b ≠ 0 → ∀ m : ℕ, ∃ g : B, g ≠ 0 ∧ IsCoprime f g ∧ ∃ u : (Localization.Away (f * g))ˣ, ∃ n d t n' d' : B, IsCoprime f n ∧ IsCoprime f d ∧ IsCoprime g n' ∧ IsCoprime g d' ∧ algebraMap B (Localization.Away (f * g)) (b * d) = (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (n * f ^ m) ∧ (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (t ^ q * d') = algebraMap B (Localization.Away (f * g)) n' := by
  first | (exact @GlobalTheory.KummerDiv.divisor_step) | (exact GlobalTheory.KummerDiv.divisor_step) | (intros; apply GlobalTheory.KummerDiv.divisor_step  <;> assumption)
end
