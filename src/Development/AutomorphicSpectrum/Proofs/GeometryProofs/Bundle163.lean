module

import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionRegularLocalRing
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.MemConePtsIffChartIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle006
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.DeterminantLatticeGradedTensor
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionHiddenFirst
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle042
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle154
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TorusUniformizationCompare
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSubMemEigW
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle087

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.ChartDehom

theorem den_mul_algebraMap {F : Type} [Field F] [CharZero F] (q : ℚ) :
    (q.den : F) * algebraMap ℚ F q = (q.num : F) := by
  have hd : (q.den : F) ≠ 0 := by exact_mod_cast q.den_nz
  rw [eq_ratCast, Rat.cast_def]
  field_simp

theorem exists_homog {K : Type} [Fintype K] {J : K → Type} {Ω : Type} [Field Ω] [CharZero Ω]
    (y : (Σ k, J k) → Ω) (c : (k : K) → J k) (hy : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {Q : Type} [CommRing Q] (ρ : MvPolynomial (Σ k, J k) ℤ →+* Q)
    (τ : MvPolynomial (Σ k, J k) ℚ →+* Q)
    (hρ : ∀ k, ρ (X ⟨k, c k⟩) = 1) (hX : ∀ p, ρ (X p) = τ (X p))
    (hQ : ∀ q : ℚ, (q.den : Q) * τ (MvPolynomial.C q) = (q.num : Q))
    (G : MvPolynomial (Σ k, J k) ℚ) :
    ∃ (N : ℤ) (D : K → ℕ) (H : MvPolynomial (Σ k, J k) ℤ), N ≠ 0 ∧
      mConeMap y H = MvPolynomial.C (N : Ω) *
        (∏ k, (MvPolynomial.C (y ⟨k, c k⟩) * X k : MvPolynomial K Ω) ^ D k) *
        MvPolynomial.C (aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) G) ∧
      ρ H = (N : Q) * τ G := by
  classical
  set u : (Σ k, J k) → Ω := fun p => y p / y ⟨p.1, c p.1⟩ with hu
  set w : K → MvPolynomial K Ω := fun k => MvPolynomial.C (y ⟨k, c k⟩) * X k with hw
  let M : (K → ℕ) → MvPolynomial (Σ k, J k) ℤ := fun D => ∏ k, X ⟨k, c k⟩ ^ D k
  have hXc : ∀ p, mConeMap y (X p) = MvPolynomial.C (y p) * X p.1 := by
    intro p; simp [mConeMap]
  have hMc : ∀ D, mConeMap y (M D) = ∏ k, w k ^ D k := by
    intro D
    simp only [M, map_prod, map_pow, hXc, hw]
  have hMρ : ∀ D, ρ (M D) = 1 := by
    intro D
    simp only [M, map_prod, map_pow, hρ, one_pow, Finset.prod_const_one]
  have hW : ∀ D E : K → ℕ, (∏ k, w k ^ D k) * ∏ k, w k ^ E k = ∏ k, w k ^ (D + E) k := by
    intro D E
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  have hS : ∀ a, ∏ k, w k ^ (Pi.single a 1 : K → ℕ) k = w a := by
    intro a
    rw [Finset.prod_eq_single a (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
    simp
  have hCc : ∀ n : ℤ, mConeMap y (MvPolynomial.C n) = MvPolynomial.C (n : Ω) := by
    intro n
    have h := (mConeMap y).commutes n
    simpa [MvPolynomial.algebraMap_eq] using h
  have hCρ : ∀ n : ℤ, ρ (MvPolynomial.C n) = (n : Q) := fun n =>
    eq_intCast (ρ.comp MvPolynomial.C) n
  induction G using MvPolynomial.induction_on with
  | C q =>
    refine ⟨q.den, 0, MvPolynomial.C q.num, by exact_mod_cast q.den_nz, ?_, ?_⟩
    · rw [hCc, aeval_C]
      simp only [Pi.zero_apply, pow_zero, Finset.prod_const_one]
      rw [_root_.mul_one, ← map_mul]
      congr 1
      have := den_mul_algebraMap (F := Ω) q
      push_cast
      exact this.symm
    · rw [hCρ]
      have := hQ q
      push_cast
      exact this.symm
  | add f g hf hg =>
    obtain ⟨N₁, D₁, H₁, h₁, c₁, r₁⟩ := hf
    obtain ⟨N₂, D₂, H₂, h₂, c₂, r₂⟩ := hg
    refine ⟨N₁ * N₂, D₁ + D₂,
      MvPolynomial.C N₂ * H₁ * M D₂ + MvPolynomial.C N₁ * H₂ * M D₁, mul_ne_zero h₁ h₂, ?_, ?_⟩
    · rw [map_add (f := _), map_mul, map_mul, map_mul, map_mul, c₁, c₂, hMc, hMc, hCc, hCc, ← hW, map_add (f := _),
        map_add]
      push_cast
      rw [MvPolynomial.C_mul]
      ring
    · rw [map_add (f := _), map_mul, map_mul, map_mul, map_mul, r₁, r₂, hMρ, hMρ, hCρ, hCρ, map_add (f := _)]
      push_cast
      ring
  | mul_X f p hf =>
    obtain ⟨N, D, H, h, c₁, r₁⟩ := hf
    refine ⟨N, D + Pi.single p.1 1, H * X p, h, ?_, ?_⟩
    · have hp : MvPolynomial.C (y p) * X p.1 = MvPolynomial.C (u p) * w p.1 := by
        rw [hw]
        simp only
        rw [← _root_.mul_assoc, ← MvPolynomial.C_mul, hu]
        simp only
        rw [div_mul_cancel₀ _ (hy p.1)]
      rw [map_mul, c₁, hXc, hp, ← hW, hS, map_mul, aeval_X, MvPolynomial.C_mul]
      ring
    · rw [map_mul, map_mul, r₁, hX]
      ring

theorem map_mem_chartIdeal : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, J k) → Ω) (c : (k : K) → J k), (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ G : MvPolynomial (Σ k, J k) ℚ,
    aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) G = (0 : Ω) →
    map (algebraMap ℚ ℂ) G ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c := by
  apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.ker_le_chart <;> assumption

end GlobalTheory.CompanionTheory.Ar.ChartDehom
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flag

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

private theorem div_mem_of_mem_span_singleton {R : Subring Ω} {x y : Ω} (hy : y ≠ 0)
    (h : x ∈ Submodule.span R {y}) : x / y ∈ R := by
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp h
  have e : r • y = (r : Ω) * y := rfl
  rw [← hr, e, mul_div_assoc, div_self hy, mul_one]
  exact r.2

private theorem zpow_mem_lemma_2 {R : Subring Ω} {x : Ω} (hx : x ∈ R) (hxi : x⁻¹ ∈ R) (n : ℤ) :
    x ^ n ∈ R := by
  cases n with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast]; exact pow_mem hx n
  | negSucc n => rw [zpow_negSucc, ← inv_pow]; exact pow_mem hxi _

theorem tens_gen {I : Type} [Fintype I] (Λ : I → Lat ξ Ω) (a : I → ℤ) (p : Cpt ξ) (s : I → Ω)
    (hs : ∀ i, (Λ i).IsGenAt p (s i)) : (Lat.tens Λ a).IsGenAt p (∏ i, s i ^ a i) := by
  apply LevelTowerAlt.N1.tens_gen <;> assumption

variable {E : Type} [AddCommGroup E] [Module Ω E]

theorem step_succ {r : ℕ} (b : Fin r → E) (i : Fin r) : flagStep Ω b (i+1) = flagStep Ω b i ⊔ Submodule.span Ω {b i} := by
  unfold flagStep
  have hset : {k : Fin r | (k : ℕ) < (i : ℕ) + 1} = {k : Fin r | (k : ℕ) < i} ∪ {i} := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · intro h
      by_cases h' : (k : ℕ) = i
      · exact Or.inr (Fin.ext h')
      · exact Or.inl (by omega)
    · rintro (h | h)
      · omega
      · subst h
        omega
  rw [hset, Set.image_union, Set.image_singleton, Submodule.span_union]

private theorem eq_zero_of_sum_smul_mem_span_lt {r : ℕ} {b : Fin r → E} (hli : LinearIndependent Ω b) (g : Fin r → Ω)
    (n : ℕ) (hg : ∑ k, g k • b k ∈ Submodule.span Ω (b '' {k | (k : ℕ) < n})) (k : Fin r)
    (hk : n ≤ (k : ℕ)) : g k = 0 := by
  classical
  have hhi : ∑ j : Fin r, (if (j : ℕ) < n then 0 else g j) • b j ∈
      Submodule.span Ω (b '' {k | (k : ℕ) < n}ᶜ) := by
    apply Submodule.sum_mem
    intro j _
    by_cases hj : (j : ℕ) < n
    · simp [hj]
    · rw [if_neg hj]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  have hlo : ∑ j : Fin r, (if (j : ℕ) < n then g j else 0) • b j ∈
      Submodule.span Ω (b '' {k | (k : ℕ) < n}) := by
    apply Submodule.sum_mem
    intro j _
    by_cases hj : (j : ℕ) < n
    · rw [if_pos hj]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · simp [hj]
  have hsplit : ∑ j : Fin r, (if (j : ℕ) < n then 0 else g j) • b j =
      ∑ j : Fin r, g j • b j - ∑ j : Fin r, (if (j : ℕ) < n then g j else 0) • b j := by
    rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : (j : ℕ) < n <;> simp [hj]
  have hzero : ∑ j : Fin r, (if (j : ℕ) < n then 0 else g j) • b j = 0 := by
    have hmem : ∑ j : Fin r, (if (j : ℕ) < n then 0 else g j) • b j ∈
        Submodule.span Ω (b '' {k | (k : ℕ) < n}) := by
      rw [hsplit]
      exact Submodule.sub_mem _ hg hlo
    exact (Submodule.disjoint_def.mp (hli.disjoint_span_image disjoint_compl_right)) _ hmem hhi
  have := Fintype.linearIndependent_iff.mp hli _ hzero k
  simpa [show ¬ (k : ℕ) < n by omega] using this

theorem gr_gen (L : Lat ξ E) {r : ℕ} (b b₀ : Fin r → E) (p : Cpt ξ) (h : ∀ i, flagStep Ω b i = flagStep Ω b₀ i)
    (hb : L.IsFrameAt b p) (i : Fin r) : ∃ t, (L.gr b₀ i).IsGenAt p t := by
  obtain ⟨hli, hLp⟩ := hb
  have hbi : b i ∈ flagStep Ω b₀ i ⊔ Submodule.span Ω {b₀ i} := by
    rw [← step_succ, ← h]
    unfold flagStep
    exact Submodule.subset_span ⟨i, show (i : ℕ) < (i : ℕ) + 1 by omega, rfl⟩
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hbi
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have hc : c ≠ 0 := by
    rintro rfl
    rw [zero_smul, add_zero] at hyz
    rw [← h, hyz] at hy
    unfold flagStep at hy
    exact hli.notMem_span_image (by simp) hy
  refine ⟨c, hc, ?_⟩
  show Submodule.span (regAt ξ p) {t | ∃ e ∈ L p, e - t • b₀ i ∈ flagStep Ω b₀ i} =
    Submodule.span (regAt ξ p) {c}
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro t ⟨e, he, hte⟩
    rw [hLp] at he
    obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp he
    have hsm : ∀ k, g k • b k = (g k : Ω) • b k := fun k => rfl
    have hsum : ∑ k, (c * (g k : Ω) - (if k = i then t else 0)) • b k =
        c • ∑ k, g k • b k - t • b i := by
      simp only [hsm, sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte, mul_smul, Finset.smul_sum]
    have hx : c • (∑ k, g k • b k - t • b₀ i) - t • y ∈ flagStep Ω b₀ i :=
      Submodule.sub_mem _ (Submodule.smul_mem _ c hte) (Submodule.smul_mem _ t hy)
    have heq : ∑ k, (c * (g k : Ω) - (if k = i then t else 0)) • b k =
        c • (∑ k, g k • b k - t • b₀ i) - t • y := by
      rw [hsum, ← hyz, smul_add, smul_sub, smul_smul, smul_smul, mul_comm t c]
      abel
    have key : ∑ k, (c * (g k : Ω) - (if k = i then t else 0)) • b k ∈ flagStep Ω b i := by
      rw [h, heq]
      exact hx
    unfold flagStep at key
    have hci := eq_zero_of_sum_smul_mem_span_lt hli _ i key i le_rfl
    rw [if_pos rfl, sub_eq_zero] at hci
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨g i, ?_⟩
    show (g i : Ω) * c = t
    rw [mul_comm]
    exact hci
  · apply Submodule.span_mono
    rw [Set.singleton_subset_iff]
    refine ⟨b i, ?_, ?_⟩
    · rw [hLp]
      exact Submodule.subset_span ⟨i, rfl⟩
    · rw [← hyz, add_sub_cancel_right]
      exact hy

theorem gr_gen_of_isFlagVBOn {L : Lat ξ E} {T : Set (Cpt ξ)} {r : ℕ} {b₀ : Fin r → E} (h : L.IsFlagVBOn T b₀)
    {p : Cpt ξ} (hp : p ∈ T) (i : Fin r) : ∃ t, (L.gr b₀ i).IsGenAt p t := by
  obtain ⟨U, hU, b, hflag, hframe⟩ := h p hp
  exact gr_gen L b b₀ p hflag (hframe p hp hU) i

end GlobalTheory.CompanionTheory.Ar.Flag
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.torus_extension_split_map : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (Z' : Scheme.{0}) [IsIntegral Z'] [AlgebraicGeometry.IsNoetherian Z'], IsNormalScheme Z' → ∀ (G : Over Z') [GrpObj G], IsSemiAbelian G → ∀ (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → ∀ τ : TorusExtension ((Over.pullback j).obj G), letI := τ.addCommGroup; ∃ u : splitTorus Z' τ.X ⟶ G, IsMonHom u ∧ ∀ (A : Type) [CommRing A] (g : L' →+* A) (t : Over.mk (spMap g ≫ j) ⟶ splitTorus Z' τ.X), t ≫ u = 1 → t = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.torus_extension_generic | exact GlobalTheory.CompanionTheory.Ar.torus_extension_generic | (intros; apply GlobalTheory.CompanionTheory.Ar.torus_extension_generic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.finite_normal_cover_generic_point : ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℚ) [LocallyOfFiniteType s] [QuasiCompact s] (L : Type) [Field L] (z : Sp L ⟶ Z), GlobalTheory.IsGenericPointHom z → ∀ (L' : Type) [Field L'] [Algebra L L'] [FiniteDimensional L L'], ∃ (Z' : Scheme.{0}) (_ : IsIntegral Z') (π : Z' ⟶ Z) (j : Sp L' ⟶ Z'), IsFinite π ∧ Surjective π ∧ IsNormalScheme Z' ∧ GlobalTheory.IsGenericPointHom j ∧ j ≫ π = spMap (algebraMap L L') ≫ z := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.normalisation_finite_cover | exact GlobalTheory.CompanionTheory.Ggeo.normalisation_finite_cover | (intros; apply GlobalTheory.CompanionTheory.Ggeo.normalisation_finite_cover <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.torus_kernel_trivial_open : ∀ (Z' : Scheme.{0}) [IsIntegral Z'] (G : Over Z') [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus Z' X ⟶ G) [IsMonHom u] (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → (∀ (A : Type) [CommRing A] (g : L' →+* A) (t : Over.mk (spMap g ≫ j) ⟶ splitTorus Z' X), t ≫ u = 1 → t = 1) → ∃ V : Z'.Opens, (V : Set Z').Nonempty ∧ ∀ (A : Type) [CommRing A] (a : Sp A ⟶ Z'), ⊤ ≤ a ⁻¹ᵁ V → ∀ t : Over.mk a ⟶ splitTorus Z' X, t ≫ u = 1 → t = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.KerSpread.injective_on_points_of_generic | exact GlobalTheory.CompanionTheory.Ar.KerSpread.injective_on_points_of_generic | (intros; apply GlobalTheory.CompanionTheory.Ar.KerSpread.injective_on_points_of_generic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.two_torsion_spread_open : ∀ (Z' S : Scheme.{0}) [IsIntegral Z'] (c : Z' ⟶ S) (G : Over S) [GrpObj G] [IsSeparated G.hom] [LocallyOfFiniteType G.hom] (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → ∀ (m : ℕ) (P : Fin m → (Over.mk (j ≫ c) ⟶ G)), Function.Injective P → (∀ i, P i ^ 2 = 1) → ∃ V : Z'.Opens, (V : Set Z').Nonempty ∧ ∀ (k : Type) [Field k] (x : Sp k ⟶ Z'), ⊤ ≤ x ⁻¹ᵁ V → ∃ Q : Fin m → (Over.mk (x ≫ c) ⟶ G), Function.Injective Q ∧ ∀ i, Q i ^ 2 = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.pts_spread | exact GlobalTheory.CompanionTheory.Ar.pts_spread | (intros; apply GlobalTheory.CompanionTheory.Ar.pts_spread <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ

theorem _root_.GlobalTheory.T.intersection_first : ∀ (R S : Type) [CommRing R] [CommRing S] (f : R →+* S) (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B B₂ : Germ.FB R d O) (C C₂ : Germ.FB S d O) (φ ψ : Germ.Pt R 1 d) (lam : Germ.PS R 2 d), IsMapOf f B C → IsMapOf f B₂ C₂ → IsIso B B₂ φ ψ lam → IsIso C C₂ (fun i => MvPowerSeries.map f (φ i)) (fun i => MvPowerSeries.map f (ψ i)) (MvPowerSeries.map f lam) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.DegZ.isIso_map | exact GlobalTheory.CompanionTheory.Ar.Flat.DegZ.isIso_map | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.DegZ.isIso_map <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.LieSpan

theorem span_range_pullback : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R R' : Type) [CommRing R] [CommRing R'] (c : R →+* R') (x : Spec (CommRingCat.of R) ⟶ S) (E E' : Type) [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E'] (M : LieModel G x E) (M' : LieModel G (Spec.map (CommRingCat.ofHom c) ≫ x) E') (j : E → E'), (∀ e, (M'.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap c)) ≫ (M.pt e).left) → Submodule.span R' (Set.range j) = ⊤ := by
  intro S G _ _ R R' _ _ c x E E' _ _ _ _ M M' j hj
  letI : Algebra R R' := c.toAlgebra
  letI : Module R E' := Module.compHom E' c
  haveI : IsScalarTower R R' E' :=
    ⟨fun r r' e => by
      show (c r * r') • e = c r • (r' • e)
      exact mul_smul _ _ _⟩
  let h : GlobalTheory.CompanionTheory.Ar.epsAt (Spec.map (CommRingCat.ofHom c) ≫ x) ⟶ GlobalTheory.CompanionTheory.Ar.epsAt x :=
    Over.homMk (Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap c))) (by
      show Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap c)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x =
        Spec.map (CommRingCat.ofHom (algebraMap R' (DualNumber R'))) ≫
          Spec.map (CommRingCat.ofHom c) ≫ x
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
      congr 2
      ext r <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl, CommRingCat.hom_comp,
        CommRingCat.hom_ofHom])
  have hl : h.left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap c)) := rfl
  have hpt : ∀ e, M'.pt (j e) = h ≫ M.pt e := fun e =>
    Over.OverMorphism.ext (by rw [Over.comp_left, hl]; exact hj e)
  have hadd : ∀ a b, j (a + b) = j a + j b := by
    intro a b
    apply M'.inj
    rw [M'.add, hpt, hpt, hpt, M.add, MonObj.comp_mul]
  have hsmul : ∀ (r : R) (e : E), j (r • e) = c r • j e := by
    intro r e
    apply M'.inj
    apply Over.OverMorphism.ext
    rw [M'.smul, hpt, hpt, Over.comp_left, Over.comp_left, M.smul, hl,
      ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    ext a <;>
      simp [GlobalTheory.CompanionTheory.Ar.dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, smul_eq_mul, TrivSqZeroExt.algebraMap_eq_inl, CommRingCat.hom_comp,
        CommRingCat.hom_ofHom]
  let β : E →ₗ[R] E' :=
    { toFun := j, map_add' := hadd, map_smul' := fun r e => hsmul r e }
  obtain ⟨-, -, hbc⟩ := GlobalTheory.CompanionTheory.Ar.LieProj.lie_finite_projective_baseChange S G R x E M
  have hb : IsBaseChange R' β := hbc R' E' M' β (fun e => hj e)
  rw [eq_top_iff]
  rintro y -
  obtain ⟨t, rfl⟩ := hb.equiv.surjective y
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul s e =>
    rw [hb.equiv_tmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, rfl⟩)
  | add a b ha hb' =>
    rw [map_add (f := _)]
    exact Submodule.add_mem _ ha hb'

end GlobalTheory.CompanionTheory.Ar.LieSpan
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_finite_base_change : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L), Module.Finite R L ∧ Module.Projective R L ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'] (L' : Type) [AddCommGroup L'] [Module R' L'] [Module R L'] [IsScalarTower R R' L'] (M' : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) L') (β : L →ₗ[R] L'), (∀ e, (M'.pt (β e)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫ (M.pt e).left) → IsBaseChange R' β := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieProj.lie_finite_projective_baseChange | exact GlobalTheory.CompanionTheory.Ar.LieProj.lie_finite_projective_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.LieProj.lie_finite_projective_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem lieModel_baseChange : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (x : Spec (CommRingCat.of R) ⟶ S) (E E' : Type) [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E'] (M : LieModel G x E) (M' : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) E'), ∃ j : E →+ E', (∀ e, (M'.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫ (M.pt e).left) ∧ (∀ (a : R) e, j (a • e) = algebraMap R R' a • j e) ∧ (Smooth G.hom → ∀ (n : ℕ) (b : Module.Basis (Fin n) R E), LinearIndependent R' (fun k => j (b k)) ∧ Submodule.span R' (Set.range fun k => j (b k)) = ⊤) :=
  PositivityTheory.HtPt.Htat.lie_bc

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

theorem torus_stratum_cocharacters_compare : ∀ (X Z' : Scheme.{0}) (G : Over X) [GrpObj G] (G' : Over Z') [GrpObj G'] (ρ : Z' ⟶ X)
    (Φ : G'.left ⟶ G.left), IsGrpPullback G' G ρ Φ → ∀ (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc]
    (u : splitTorus Z' Xc ⟶ G') [IsMonHom u] (L k : Type) [Field L] [Field k] [Algebra L k] (x : Sp k ⟶ Z') (zL : Sp L ⟶ X),
    x ≫ ρ = spMap (algebraMap L k) ≫ zL → ∀ (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left),
    IsGrpPullback GK G zL φ → ∀ τ : TorusExtension GK,
    (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' Xc), t ≫ u = 1 → t = 1) →
    (∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G'.left), IsGrpPullback Gk G' x ψ → ∀ τ' : TorusExtension Gk,
      letI := τ'.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk),
        p ≫ τ'.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' Xc, (t ≫ u).left = p.left ≫ ψ) →
    letI := τ.addCommGroup
    ∃ e : τ.X ≃+ Xc, ∀ (A : Type) [CommRing A] (g : k →+* A) (b : Sp A ⟶ Z') (_ : spMap g ≫ x = b) (b' : Sp A ⟶ Sp L)
      (_ : spMap (g.comp (algebraMap L k)) = b') (t : Over.mk b ⟶ splitTorus Z' Xc) (t' : Over.mk b' ⟶ splitTorus (Sp L) τ.X),
      (∀ χ, charVal t' χ = charVal t (e χ)) → (t ≫ u).left ≫ Φ = (t' ≫ τ.i).left ≫ φ := by
  exact @PositivityTheory.Xgn.torus_uniformization_compare

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end
