module

public import Formalism.SatakeDualWeyl.Bundle001
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle576
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle525
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle528
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle238
public import GroundTheory.AutomorphicForms.MacdonaldWhittakerHecke
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import GroundTheory.AutomorphicForms.Bundle008
import GroundTheory.AutomorphicForms.MacdonaldHecke
import GroundTheory.LocalFields.LocalFourierHaar
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle979
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle980
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle035
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Mathlib.RingTheory.DividedPowers.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm

@[expose] public section

section

open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp Formalism.UG Matrix GlobalTheory.BorelUMod
open scoped NNReal Pointwise

noncomputable section
namespace GlobalTheory.LineUMod

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem locCompact_secondCountable [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) :
    LocallyCompactSpace L ∧ SecondCountableTopology L := by
  obtain ⟨-, hv, -, hϖ, -, hq, hcard⟩ := h
  haveI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial :=
    ⟨ϖ, by rw [hϖ]; exact WithZero.coe_ne_zero, by rw [hϖ, ← WithZero.coe_one, ne_eq, WithZero.coe_inj]; decide⟩
  letI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (e := 2) (by norm_num)
  have hp := (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
    (K := L)).2 ⟨inferInstance, (Valued.v : Valuation L _).valuationSubring_isDiscreteValuationRing,
      Nat.finite_of_card_ne_zero (by
        refine ne_of_eq_of_ne hcard (pow_ne_zero _ (by omega)))⟩
  constructor
  · open scoped Valued in exact inferInstance
  · open scoped Valued in exact inferInstance


open UpLatIndex in
theorem distribHaarChar_eq [CompleteSpace L] [LocallyCompactSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ}
    (h : IsUnramInv ϖ σ q) (u : Lˣ) : (distribHaarChar L u : ℝ) = (q : ℝ) ^ (-2 * ordL (u : L)) := by
  have hq : q ≠ 0 := by have := h.2.2.2.2.2.1; omega
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  haveI := (locCompact_secondCountable h).2
  borelize L
  let μ : Measure L := Measure.addHaar
  have key : ∀ k K : ℤ, k ≤ K → μ.real (ordBall L k) = (q : ℝ) ^ (2 * (K - k)) * μ.real (ordBall L K) := by
    intro k K hk
    have e := relIndex_ordBall h hk
    haveI : ((ordBall L K).addSubgroupOf (ordBall L k)).FiniteIndex :=
      ⟨ne_of_eq_of_ne e (pow_ne_zero _ (pow_ne_zero _ hq))⟩
    have := GlobalTheory.BaseModule.addRelIndex_mul_measure (ordBall L K) (ordBall L k) (ordBall_mono hk)
      (isOpen_vball h.2.2.2.1 K).measurableSet μ
    rw [Measure.real, ← this, e, ENNReal.toReal_mul, ENNReal.toReal_natCast, ← pow_mul, Nat.cast_pow, ← zpow_natCast,
      Measure.real]
    congr 2
    omega
  have hs : u • (ordBall L 0 : Set L) = ordBall L (ordL (u : L)) := by
    ext x
    obtain ⟨y, rfl⟩ := MulAction.surjective u x
    beta_reduce
    rw [Set.smul_mem_smul_set_iff, SetLike.mem_coe, SetLike.mem_coe, mem_ordBall, mem_ordBall, Units.smul_def,
      smul_eq_mul, map_mul, v_eq_exp u.ne_zero, neg_zero, WithZero.exp_zero]
    exact (mul_le_iff_le_one_right WithZero.exp_pos).symm
  have h1 := congrArg ENNReal.toReal (distribHaarChar_mul μ u (ordBall L 0 : Set L))
  rw [hs, ENNReal.toReal_mul, ENNReal.coe_toReal, ← Measure.real, ← Measure.real,
    key 0 |ordL (u : L)| (abs_nonneg _), key (ordL (u : L)) _ (le_abs_self _), ← mul_assoc] at h1
  have hpos : μ.real (ordBall L |ordL (u : L)|) ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨(isOpen_vball h.2.2.2.1 _).measure_ne_zero μ ⟨0, zero_mem (ordBall L _)⟩,
      (isCompact_vball h _).measure_ne_top⟩
  have h2 := mul_right_cancel₀ hpos h1
  rw [eq_comm, ← mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ hq'), ← _root_.zpow_neg, ← zpow_add₀ hq'] at h2
  rw [← h2]
  congr 1
  ring

section Mat
omit [Valued L (WithZero (Multiplicative ℤ))]

variable (x y : Fin n → L) (z : L)

end Mat

variable {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x) (hc : Continuous σ)



variable {θ d : L} (hθ : θ + σ θ = 1) (hd : σ d = -d) (hd0 : d ≠ 0)



end GlobalTheory.LineUMod
end
end

section

noncomputable section

open NumberField IsDedekindDomain Polynomial MeasureTheory GroundTheory.Automorphic UpperTheory.V.Af GlobalTheory.HenQ
open scoped ValuativeRel Pointwise

namespace GlobalTheory.HenQ.ShellOp

section General

open GroundTheory.Automorphic.Spherical GLnLocal Iwasawa HeckeAlgebra

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}


end General

end GlobalTheory.HenQ.ShellOp

namespace GlobalTheory.HenQ.ShellOp

section Series

end Series

end GlobalTheory.HenQ.ShellOp

namespace GlobalTheory.HenQ.ShellOp

section Hecke

open GroundTheory.Automorphic.Spherical GLnLocal Iwasawa HeckeAlgebra

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}

theorem esymm_eq (z : Fin n → ℂˣ) (r : ℕ) :
    evalAt z (esymmL n r) = ((Finset.univ.val.map z).map fun b : ℂˣ => (b : ℂ)).esymm r := by
  rw [evalAt_esymmL, Multiset.map_map, Finset.esymm_map_val]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [monomialChar_apply]
  simp only [lamS, Function.comp_apply]
  rw [← Finset.prod_subset (Finset.subset_univ S) (fun i _ hi => by simp [hi])]
  exact Finset.prod_congr rfl fun i hi => by simp [hi]

theorem lamS_univ' : lamS (Finset.univ : Finset (Fin n)) = fun _ => 1 := by
  funext i
  simp [lamS]

theorem gMat_univ' (c : Pairs (Finset.univ : Finset (Fin n)) → 𝓀[F]) :
    gMat Finset.univ c = torusPow F n (fun _ => 1) := by
  have h : unipC (F := F) Finset.univ c = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [coe_unipC, Matrix.add_apply, cMat_apply_of_not c (fun h => h.2.1 (Finset.mem_univ _)), add_zero]
    rfl
  rw [gMat, h, one_mul, lamS_univ']

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

theorem central_mem_of_top (z : Fin n → ℂˣ) {f : GL (Fin n) F → ℂ}
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g)
    (hT : minusculeHecke μ n ∈ eigenSubalgebra μ z f hf) : centralHecke μ ∈ eigenSubalgebra μ z f hf := by
  classical
  have hK : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)).ne'
  have hp : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
    have := Finset.powersetCard_self (Finset.univ : Finset (Fin n))
    rwa [Finset.card_univ, Fintype.card_fin] at this
  have h1 : ∀ g, f (g * torusPow F n (fun _ => 1)) = monomialChar (fun _ : Fin n => 1) z * f g := by
    intro g
    have h := hT g
    haveI : IsEmpty (Pairs (Finset.univ : Finset (Fin n))) := ⟨fun p => p.2.2.1 (Finset.mem_univ _)⟩
    have hc : ∀ I : Fintype (Pairs (Finset.univ : Finset (Fin n)) → 𝓀[F]), (@Finset.univ _ I).card = 1 := by
      intro I
      rw [Subsingleton.elim I Unique.fintype]
      rfl
    rw [integral_minusculeHecke_mul hf, evalAt_satakeTransform_minusculeHecke z le_rfl, evalAt_esymmL, hp,
      Finset.sum_singleton, Finset.sum_singleton, Finset.sum_congr rfl (fun c _ => by rw [gMat_univ' c]),
      Finset.sum_const, hc, one_smul, lamS_univ', Nat.sub_self, mul_zero,
      pow_zero, mul_one, mul_assoc] at h
    exact mul_left_cancel₀ hK h
  have h2 : ∀ g, f (g * torusPow F n (fun _ => -1)) = monomialChar (fun _ : Fin n => -1) z * f g := by
    intro g
    have h := h1 (g * torusPow F n (fun _ => -1))
    have e : (fun _ : Fin n => (-1 : ℤ)) + (fun _ => 1) = 0 := by funext i; simp
    have e' : torusPow F n (fun _ => -1) * torusPow F n (fun _ => 1) = 1 := by
      have : (fun _ : Fin n => (-1 : ℤ)) = -(fun _ => 1) := rfl
      rw [this, torusPow_neg, inv_mul_cancel]
    rw [mul_assoc, e', mul_one] at h
    rw [h, ← mul_assoc, ← monomialChar_add, e, monomialChar_zero, one_mul]
  intro g
  set g₀ := torusPow F n (fun _ : Fin n => (-1 : ℤ))
  have e := integral_mul_left_eq_self (μ := μ)
    (fun x => (centralHecke μ : HeckeAlgebra μ) x * f (g * x)) g₀
  rw [← e]
  have hpt : (fun y => (centralHecke μ : HeckeAlgebra μ) (g₀ * y) *
      f (g * (g₀ * y))) = (integralGL F n : Set (GL (Fin n) F)).indicator (fun _ => f (g * g₀)) := by
    funext y
    rw [centralHecke_apply]
    have hiff : g₀ * y ∈ centralSet F n ↔ y ∈ (integralGL F n : Set (GL (Fin n) F)) := by
      rw [mem_centralSet, inv_mul_cancel_left]
      rfl
    by_cases hy : y ∈ (integralGL F n : Set (GL (Fin n) F))
    · rw [Set.indicator_of_mem (hiff.2 hy), Set.indicator_of_mem hy, one_mul, ← mul_assoc, hf _ _ hy]
    · rw [Set.indicator_of_notMem (mt hiff.1 hy), Set.indicator_of_notMem hy, zero_mul]
  rw [hpt, integral_indicator (isOpen_integralGL F n).measurableSet, setIntegral_const,
    Complex.real_smul, h2, satakeTransform_centralHecke, map_smul,
    Spherical.monomial, evalAt_single, one_mul, smul_eq_mul]
  ring

theorem minuscule_mem_of (z : Fin n → ℂˣ) {f : GL (Fin n) F → ℂ}
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g) {r : ℕ} (hr : r ≤ n)
    (h : ∀ g, ∑ᶠ c : GL (Fin n) F ⧸ integralGL F n,
      (minusculeSet F n r).indicator (fun _ => (1 : ℂ)) c.out * f (g * c.out) =
        sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r) * f g) :
    minusculeHecke μ r ∈ eigenSubalgebra μ z f hf := by
  intro g
  have hcs : HasCompactSupport fun x => (minusculeHecke μ r : HeckeAlgebra μ) x * f (g * x) := by
    refine HasCompactSupport.intro (isCompact_minusculeSet r) fun x hx => ?_
    simp only [minusculeHecke_apply, Set.indicator_of_notMem hx, zero_mul]
  rw [integral_eq_smul_finsum_coset μ (integralOpen F n) (isCompact_integralGL F n) hcs (fun x k hk => by
      rw [(HeckeAlgebraLevel.val_mem _ _ (minusculeHecke μ r) k hk x).2, ← mul_assoc, hf _ k hk]),
    Complex.real_smul, evalAt_satakeTransform_minusculeHecke z hr, mul_assoc, mul_assoc, ← mul_assoc (sqrtQ F ^ _), ← h g]
  rfl

end Hecke

end GlobalTheory.HenQ.ShellOp

namespace GlobalTheory.HenQ.ShellOp

section Global

open GroundTheory.Automorphic.Spherical GLnLocal Iwasawa HeckeAlgebra

variable {K : Type} [Field K] [NumberField K]

end Global

end GlobalTheory.HenQ.ShellOp

namespace GlobalTheory.HenQ

open GroundTheory.Automorphic.Spherical GLnLocal Iwasawa HeckeAlgebra

end GlobalTheory.HenQ
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShearLift

theorem eq_of_fst_snd_left {C : Type*} [Category C] [Limits.HasPullbacks C] {B : C} {Y : Over B} {T : C}
    {a b : T ⟶ (Y ⊗ Y).left} (h₁ : a ≫ (fst Y Y).left = b ≫ (fst Y Y).left)
    (h₂ : a ≫ (snd Y Y).left = b ≫ (snd Y Y).left) : a = b := by
  rw [Over.fst_left] at h₁
  rw [Over.snd_left] at h₂
  exact Limits.pullback.hom_ext h₁ h₂

theorem eq_of_shear : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀] (X : Over (Sp R)) (i : A₀.left ⟶ X.left), IsPullback i A₀.hom X.hom (spMap π) →
    ∀ (l : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left), l ≫ (fst X X).left = (fst A₀ A₀).left ≫ i → l ≫ (snd X X).left = (snd A₀ A₀).left ≫ i →
    ∀ (m : X ⊗ X ⟶ X), l ≫ m.left = (μ[A₀]).left ≫ i → IsIso (lift (fst X X) m) →
    ∀ (P : Over (Sp R)) (P₀ : Over (Sp R₀)) (k : P₀.left ⟶ P.left), IsPullback k P₀.hom P.hom (spMap π) →
    Smooth P.hom → IsProper P.hom → GeometricallyConnected P.hom →
    ∀ (ε : Sp R ⟶ P.left), ε ≫ P.hom = 𝟙 _ → ∀ (f f' : P ⟶ X), k ≫ f.left = k ≫ f'.left → ε ≫ f.left = ε ≫ f'.left → f = f' := by
  intro R R₀ _ _ π hπ hnil A₀ _ X i hi l hl1 hl2 m hm hσ P P₀ k hk hsm hpr hgc ε hε f f' hk' hε'
  have hσl : IsIso (lift (fst X X) m).left := Functor.map_isIso (Over.forget (Sp R)) (lift (fst X X) m)

  have hsq : (k ≫ f.left) ≫ X.hom = P₀.hom ≫ spMap π := by
    rw [Category.assoc, Over.w f]; exact hk.w
  let f₀ : P₀ ⟶ A₀ := Over.homMk (hi.lift (k ≫ f.left) P₀.hom hsq) (hi.lift_snd _ _ _)
  have hf₀i : f₀.left ≫ i = k ≫ f.left := hi.lift_fst _ _ _

  have hlσ : l ≫ (lift (fst X X) m).left = (lift (fst A₀ A₀) μ).left ≫ l := by
    apply eq_of_fst_snd_left
    · simp only [Category.assoc, ← Over.comp_left, lift_fst]
      rw [hl1, ← Category.assoc, ← Over.comp_left, lift_fst]
    · simp only [Category.assoc, ← Over.comp_left, lift_snd]
      rw [hm, hl2, ← Category.assoc, ← Over.comp_left, lift_snd]
  have hred : k ≫ (lift f f).left = (lift f₀ f₀).left ≫ l := by
    apply eq_of_fst_snd_left
    · simp only [Category.assoc, ← Over.comp_left, lift_fst]
      rw [hl1, ← Category.assoc, ← Over.comp_left, lift_fst, hf₀i]
    · simp only [Category.assoc, ← Over.comp_left, lift_snd]
      rw [hl2, ← Category.assoc, ← Over.comp_left, lift_snd, hf₀i]
  let h₀ : P₀ ⟶ A₀ ⊗ A₀ := lift f₀ (toUnit P₀ ≫ η)
  have hh₀ : h₀ ≫ lift (fst A₀ A₀) μ = lift f₀ f₀ := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [h₀]
    · simp only [h₀, Category.assoc, lift_snd]
      exact lift_comp_one_right _ _
  obtain ⟨gu, hgu_def⟩ : ∃ g, g = lift f f' ≫ inv (lift (fst X X) m) := ⟨_, rfl⟩
  obtain ⟨gv, hgv_def⟩ : ∃ g, g = lift f f ≫ inv (lift (fst X X) m) := ⟨_, rfl⟩
  have eu : gu.left ≫ (lift (fst X X) m).left = (lift f f').left := by
    rw [← Over.comp_left, hgu_def, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have ev : gv.left ≫ (lift (fst X X) m).left = (lift f f).left := by
    rw [← Over.comp_left, hgv_def, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hgv : k ≫ gv.left = h₀.left ≫ l := by
    rw [← cancel_mono (lift (fst X X) m).left, Category.assoc, ev, hred, Category.assoc, hlσ,
      ← Category.assoc, ← Over.comp_left, hh₀]
  have hpair_k : k ≫ (lift f f').left = k ≫ (lift f f).left := by
    apply eq_of_fst_snd_left
    · simp only [Category.assoc, ← Over.comp_left, lift_fst]
    · simp only [Category.assoc, ← Over.comp_left, lift_snd]; exact hk'.symm
  have hpair_ε : ε ≫ (lift f f').left = ε ≫ (lift f f).left := by
    apply eq_of_fst_snd_left
    · simp only [Category.assoc, ← Over.comp_left, lift_fst]
    · simp only [Category.assoc, ← Over.comp_left, lift_snd]; exact hε'.symm
  have hgu_k : k ≫ gu.left = k ≫ gv.left := by
    rw [← cancel_mono (lift (fst X X) m).left, Category.assoc, Category.assoc, eu, ev, hpair_k]
  have hgu_ε : ε ≫ gu.left = ε ≫ gv.left := by
    rw [← cancel_mono (lift (fst X X) m).left, Category.assoc, Category.assoc, eu, ev, hpair_ε]

  have e2 : (h₀ ≫ snd A₀ A₀).left = P₀.hom ≫ (η : 𝟙_ (Over (Sp R₀)) ⟶ A₀).left := by
    simp only [h₀, lift_snd, Over.comp_left, Over.toUnit_left]
  have hv₀ : k ≫ (gv ≫ snd X X).left = P₀.hom ≫ ((η : 𝟙_ (Over (Sp R₀)) ⟶ A₀).left ≫ i) := by
    calc k ≫ (gv ≫ snd X X).left = (k ≫ gv.left) ≫ (snd X X).left := by
          rw [Over.comp_left, Category.assoc]
      _ = h₀.left ≫ (l ≫ (snd X X).left) := by rw [hgv, Category.assoc]
      _ = (h₀ ≫ snd A₀ A₀).left ≫ i := by rw [hl2, Over.comp_left, Category.assoc]
      _ = _ := by rw [e2, Category.assoc]
  have hu₀ : k ≫ (gu ≫ snd X X).left = P₀.hom ≫ ((η : 𝟙_ (Over (Sp R₀)) ⟶ A₀).left ≫ i) := by
    rw [Over.comp_left, ← Category.assoc, hgu_k, Category.assoc, ← Over.comp_left]; exact hv₀
  have cu := GlobalTheory.T.eq_comp_section_of_proper_smooth_nilpotent_rigidity R R₀ π hπ hnil P X P₀ k hk hsm hpr hgc ε hε _ _ hu₀
  have cv := GlobalTheory.T.eq_comp_section_of_proper_smooth_nilpotent_rigidity R R₀ π hπ hnil P X P₀ k hk hsm hpr hgc ε hε _ _ hv₀
  have huv : gu ≫ snd X X = gv ≫ snd X X := by
    apply Over.OverMorphism.ext
    rw [cu, cv, Over.comp_left, Over.comp_left, ← Category.assoc ε gu.left, hgu_ε, Category.assoc]
  have hinvfst : inv (lift (fst X X) m) ≫ fst X X = fst X X := by
    rw [IsIso.inv_comp_eq, lift_fst]
  have hg : gu = gv := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [hgu_def, hgv_def, Category.assoc, Category.assoc, hinvfst, lift_fst, lift_fst]
    · exact huv
  rw [hgu_def, hgv_def] at hg
  have hff : lift f f' = lift f f := (cancel_mono (inv (lift (fst X X) m))).1 hg
  have := congrArg (· ≫ snd X X) hff
  simp only [lift_snd] at this
  exact this.symm

end GlobalTheory.ShearLift
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.existsUnique_isMonHom_lift_of_grpPullback_abelian : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (i : A₀.left ⟶ A.left) (j : B₀.left ⟶ B.left),
    IsGrpPullback A₀ A (spMap π) i → IsGrpPullback B₀ B (spMap π) j → IsAbelianScheme A → IsAbelianScheme B →
    ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀] (φ : A ⟶ B), i ≫ φ.left = f₀.left ≫ j → ∃! f : A ⟶ B, IsMonHom f ∧ i ≫ f.left = f₀.left ≫ j := by
  first | exact @GlobalTheory.HomLift.existsUnique_isMonHom_lift | exact GlobalTheory.HomLift.existsUnique_isMonHom_lift | (intros; apply GlobalTheory.HomLift.existsUnique_isMonHom_lift <;> assumption)
end

section

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.Obj

theorem holUnif_dim_eq_of_linear {A : Over (Sp ℂ)} [GrpObj A] {L L' : LB A.left} {g g' : ℕ} (u : HolUnif A L g)
    (u' : HolUnif A L' g') (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hF : ∀ z, u'.ex (F z) = u.ex z) : g = g' := by
  haveI := u.discrete
  haveI := u'.discrete
  have hinj := AnyUnif.injective_of_ker_le_discrete u.Λ F fun z hz => by
    rw [← u.ker, ← hF, hz]
    exact (u'.ker 0).2 u'.Λ.zero_mem
  have hsurj : LinearMap.range F = ⊤ := GlobalTheory.AHWeil.eq_top_of_add_discrete u'.Λ _ fun w => by
    obtain ⟨z, hz⟩ := u.ex_onto (u'.ex w)
    refine ⟨⟨w - F z, (u'.ker _).1 ?_⟩, z, by simp⟩
    have h := u'.ex_add (w - F z) (F z)
    rw [sub_add_cancel, hF, hz] at h
    exact (mul_eq_right.1 h.symm)
  simpa using (LinearEquiv.ofBijective F ⟨hinj, LinearMap.range_eq_top.1 hsurj⟩).finrank_eq

end GlobalTheory.RealMult.Obj
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.OpenPartUnit

section General

variable {X Y Y' G B Z : Scheme.{0}}

theorem gs_appLE (r : Z ⟶ Y) (f : Y ⟶ X) (z : Z) (U : X.Opens) (W : Y.Opens) (e : W ≤ f ⁻¹ᵁ U) (h : r z ∈ W)
    (a : Γ(X, U)) : gs r z W ((f.appLE U W e).hom a) = gs (r ≫ f) z U a :=
  (gs_res r z e h _).trans (gs_pull r f z U (e h) a)

end General

end GlobalTheory.OpenPartUnit
end
