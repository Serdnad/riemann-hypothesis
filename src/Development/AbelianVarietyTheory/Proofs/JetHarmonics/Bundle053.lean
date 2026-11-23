module

public import Formalism.HermitianCurvature.StatementQ
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.PeriodIntegrals.Bundle004
public import Formalism.PeriodIntegrals.Bundle018
public import Formalism.PeriodIntegrals.Bundle020
public import Formalism.PeriodIntegrals.UpqRep
public import Formalism.RealPlaceAnalysis.Bundle002
public import Formalism.RealPlaceAnalysis.Bundle003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle047
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle051
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle048
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Mathlib.Tactic.ReduceModChar
import Formalism.HermitianCurvature.Bundle001

@[expose] public section

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.quantumMinor_block_linearMap_intertwine : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (n m : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (w : Fin m → Fin n) (Pop : Fin m → Fin m → Wp → Wp), Function.Injective w → (∀ i j v, l (E (w i) (w j) v) = Pop i j (l v)) → ∀ u v, l (Formalism.REAL.qminor E w w u v) = Formalism.FourierDecayAlt.Q.qmF Pop id id u (l v) := by
  first | exact @GlobalTheory.qminor_block_intertwine | exact GlobalTheory.qminor_block_intertwine | (intros; apply GlobalTheory.qminor_block_intertwine <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Pj

namespace GlobalTheory.PlaceSum

variable {K : Type} [Field K] [NumberField K]

theorem liesOver_resChar (la : HeightOneSpectrum (𝓞 K)) :
    la.asIdeal.LiesOver (Ideal.span {((resCharOf la : ℕ) : ℤ)}) := by
  refine ⟨?_⟩
  ext n
  rw [Ideal.mem_span_singleton, Ideal.under_def, Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
  have h : (Ideal.Quotient.mk la.asIdeal) (algebraMap ℤ (𝓞 K) n) = (n : 𝓞 K ⧸ la.asIdeal) := by simp
  rw [h]
  exact (CharP.intCast_eq_zero_iff (𝓞 K ⧸ la.asIdeal) (ringChar (𝓞 K ⧸ la.asIdeal)) n).symm

theorem span_ne_bot {p : ℕ} (hp : p.Prime) : Ideal.span {(p : ℤ)} ≠ ⊥ := by
  simpa using hp.ne_zero

theorem span_isMaximal {p : ℕ} (hp : p.Prime) : (Ideal.span {(p : ℤ)}).IsMaximal :=
  ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2
    (Nat.prime_iff_prime_int.mp hp)).isMaximal (span_ne_bot hp)

theorem mem_primesOverFinset {p : ℕ} (hp : p.Prime) (la : HeightOneSpectrum (𝓞 K)) (h : resCharOf la = p) :
    la.asIdeal ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K) := by
  haveI := span_isMaximal hp
  refine (IsDedekindDomain.mem_primesOverFinset_iff (span_ne_bot hp) _).mpr ⟨la.isPrime, ?_⟩
  rw [← h]
  exact liesOver_resChar la

theorem finite_resChar_eq {p : ℕ} (hp : p.Prime) :
    {la : HeightOneSpectrum (𝓞 K) | resCharOf la = p}.Finite := by
  refine Set.Finite.of_finite_image (f := fun la => la.asIdeal) ?_
    (fun a _ b _ h => HeightOneSpectrum.ext h)
  refine (IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K)).finite_toSet.subset ?_
  rintro _ ⟨la, hla, rfl⟩
  exact mem_primesOverFinset hp la hla


set_option linter.deprecated false in
theorem sum_ram_log_le {p : ℕ} (hp : p.Prime) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ la ∈ T, resCharOf la = p) :
    ∑ la ∈ T, (ramOverZ la : ℝ) * Real.log (Ideal.absNorm la.asIdeal) ≤
      (Module.finrank ℚ K : ℝ) * Real.log p := by
  classical
  haveI := span_isMaximal hp
  have hs := Ideal.sum_ramification_inertia (R := ℤ) (𝓞 K) ℚ K (span_ne_bot hp)
  have h1 : ∀ la ∈ T, (ramOverZ la : ℝ) * Real.log (Ideal.absNorm la.asIdeal) =
      ((Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) la.asIdeal *
        Ideal.inertiaDeg' (Ideal.span {(p : ℤ)}) la.asIdeal : ℕ) : ℝ) * Real.log p := by
    intro la hla
    have h := hT la hla
    haveI : la.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by rw [← h]; exact liesOver_resChar la
    rw [Ideal.absNorm_eq_pow_inertiaDeg' la.asIdeal hp, ramOverZ, h]
    push_cast
    rw [Real.log_pow]
    ring
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg p)
  rw [← Nat.cast_sum, Nat.cast_le, ← hs]
  rw [← Finset.sum_image (s := T) (g := fun la => la.asIdeal)
    (f := fun P : Ideal (𝓞 K) => Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) P *
        Ideal.inertiaDeg' (Ideal.span {(p : ℤ)}) P) (fun a _ b _ h => HeightOneSpectrum.ext h)]
  refine Finset.sum_le_sum_of_subset ?_
  intro P hP
  obtain ⟨la, hla, rfl⟩ := Finset.mem_image.1 hP
  exact mem_primesOverFinset hp la (hT la hla)

theorem finsum_le_sum_primes (K : Type) [Field K] [NumberField K] (φ : ℕ → ℝ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hφ : ∀ p, 0 ≤ φ p) (ν : HeightOneSpectrum (𝓞 K) → ℝ) (h0 : ∀ la, 0 ≤ ν la)
    (hle : ∀ la, ν la ≤ (ramOverZ la : ℝ) * φ (resCharOf la)) (hz : ∀ la, resCharOf la ∉ S → ν la = 0) :
    (Function.support ν).Finite ∧
      (∑ᶠ la, |ν la| * (Real.log (Ideal.absNorm la.asIdeal) / Module.finrank ℚ K)) ≤
        ∑ p ∈ S, φ p * Real.log p := by
  classical
  have hsub : Function.support ν ⊆ ⋃ p ∈ S, {la : HeightOneSpectrum (𝓞 K) | resCharOf la = p} := by
    intro la hla
    simp only [Set.mem_iUnion]
    exact ⟨resCharOf la, by by_contra h; exact hla (hz la h), rfl⟩
  have hfin : (Function.support ν).Finite :=
    (Set.Finite.biUnion S.finite_toSet fun p hp => finite_resChar_eq (hS p hp)).subset hsub
  refine ⟨hfin, ?_⟩
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
  · have hmap : ∀ la ∈ hfin.toFinset, resCharOf la ∈ S := by
      intro la hla
      by_contra h
      exact (hfin.mem_toFinset.1 hla) (hz la h)
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    refine Finset.sum_le_sum fun p hp => ?_
    have hb := sum_ram_log_le (K := K) (hS p hp) (hfin.toFinset.filter fun la => resCharOf la = p)
      (fun la hla => (Finset.mem_filter.1 hla).2)
    calc _ ≤ ∑ la ∈ hfin.toFinset.filter (fun la => resCharOf la = p),
          (φ p / Module.finrank ℚ K) * ((ramOverZ la : ℝ) * Real.log (Ideal.absNorm la.asIdeal)) := by
          refine Finset.sum_le_sum fun la hla => ?_
          have h := (Finset.mem_filter.1 hla).2
          have h2 := hle la
          rw [h] at h2
          rw [abs_of_nonneg (h0 la)]
          have h3 : 0 ≤ Real.log (Ideal.absNorm la.asIdeal) / Module.finrank ℚ K :=
            div_nonneg (Real.log_natCast_nonneg _) hn.le
          refine (mul_le_mul_of_nonneg_right h2 h3).trans (le_of_eq ?_)
          ring
      _ ≤ (φ p / Module.finrank ℚ K) * ((Module.finrank ℚ K : ℝ) * Real.log p) := by
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left hb (div_nonneg (hφ p) hn.le)
      _ = φ p * Real.log p := by field_simp
  · intro la hla
    rw [Set.Finite.coe_toFinset]
    intro h
    exact hla (by simp [h])

end GlobalTheory.PlaceSum
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.lintegral_inv_eq_of_biInvariant_matGroup : ∀ (m : ℕ) (S : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (PI.MtM m)), PI.IsMatGroup S → PI.IsHaarOnM S μ → PI.IsRightInvM S μ → ∀ f : PI.MtM m → ℝ≥0∞, Measurable f → ∫⁻ s, f (fun i j => (Matrix.of s)⁻¹ i j) ∂μ = ∫⁻ s, f s ∂μ := by
  first | exact @GlobalTheory.HaarInversion.lintegral_inv_eq | exact GlobalTheory.HaarInversion.lintegral_inv_eq | (intros; apply GlobalTheory.HaarInversion.lintegral_inv_eq <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.matGroupHaar_unique_finite_compact_openPos : ∀ (m : ℕ) (G : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (PI.MtM m)), PI.IsMatGroup G → PI.IsHaarOnM G μ → (∀ μ' : Measure (PI.MtM m), PI.IsHaarOnM G μ' → ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧ μ' = c • μ) ∧ (∀ K : Set (PI.MtM m), IsCompact K → (∀ x ∈ K, Matrix.of x ∈ G) → μ K < ⊤) ∧ ∀ U : Set (PI.MtM m), IsOpen U → (∃ x ∈ U, Matrix.of x ∈ G) → 0 < μ U := by
  first | exact @GlobalTheory.MatHaar.haar_unique_locFinite_openPos | exact GlobalTheory.MatHaar.haar_unique_locFinite_openPos | (intros; apply GlobalTheory.MatHaar.haar_unique_locFinite_openPos <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.weil_formula_integrable_complex : ∀ (k r : ℕ) (μG μS νq : Measure (Formalism.QuantumDeterminants.Mt k r)) [SFinite μS] (f : Formalism.QuantumDeterminants.Mt k r → ℂ), PI.BesselPeriodGGP.IsQuotMeas μG μS νq → Measurable f → Integrable f μG → (∀ᵐ x ∂νq, Integrable (fun s => f (fun i j => (Matrix.of s * Matrix.of x) i j)) μS) ∧ Integrable (fun x => ∫ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) νq ∧ ∫ x, f x ∂μG = ∫ x, (∫ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) ∂νq := by
  first | exact @GlobalTheory.weil_formula_integrable | exact GlobalTheory.weil_formula_integrable | (intros; apply GlobalTheory.weil_formula_integrable <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.freeAlgebraAction_capelliDeterminant_eq_operator : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ S), (∀ a b (v : S), ((E a b v : S) : H) = PI.DSInfCharCap.dsigC ε σ (PI.DSInfCharCap.unitM (a, b)) v) → ∀ (u : ℂ) (v : S), PI.DSInfCharCap.actU ε σ (Formalism.REAL.qdet (PI.DSInfCharCap.Egl n) u) v = ((Formalism.REAL.qdet E u v : S) : H) := by
  first | exact @GlobalTheory.CapelliFreeAction.actU_qdet | exact GlobalTheory.CapelliFreeAction.actU_qdet | (intros; apply GlobalTheory.CapelliFreeAction.actU_qdet <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.weight_compactDominance_of_mem_highestWeightSpan : ∀ (k : ℕ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (E : Fin k → Fin k → Module.End ℂ W) (Λ μ : Fin k → ℝ) (x v : W), Formalism.REAL.GlRel E → Formalism.REAL.IsUnitary (PI.UpqRep.allPos k) E → Formalism.REAL.KHighest (PI.UpqRep.allPos k) E Λ x → v ∈ Formalism.REAL.kSpan (PI.UpqRep.allPos k) E x → v ≠ 0 → Formalism.REAL.IsWeight E μ v → PI.UpqRep.CDom (PI.UpqRep.allPos k) μ Λ := by
  first | exact @GlobalTheory.weight_cdom_of_mem_kSpan | exact GlobalTheory.weight_cdom_of_mem_kSpan | (intros; apply GlobalTheory.weight_cdom_of_mem_kSpan <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.quantumMinor_eq_unit_smul_of_range_eq : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (a a₂ b b₂ : Fin t → Fin n), Formalism.REAL.GlRel E → Function.Injective a → Function.Injective a₂ → Function.Injective b → Function.Injective b₂ → Set.range a = Set.range a₂ → Set.range b = Set.range b₂ → ∃ e : ℂ, ‖e‖ = 1 ∧ ∀ u, Formalism.REAL.qminor E a b u = e • Formalism.REAL.qminor E a₂ b₂ u := by
  first | exact @GlobalTheory.qminor_eq_smul_of_range_eq | exact GlobalTheory.qminor_eq_smul_of_range_eq | (intros; apply GlobalTheory.qminor_eq_smul_of_range_eq <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.quantumMinor_column_expansion_under_linearMap : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (n t : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (a b : Fin (t + 1) → Fin n) (a' b' : Fin t → Fin n) (a0 b0 : Fin n) (p : ℂ), Formalism.REAL.GlRel E → Function.Injective a → Function.Injective b → Function.Injective a' → Function.Injective b' → Set.range a = insert a0 (Set.range a') → a0 ∉ Set.range a' → Set.range b = insert b0 (Set.range b') → b0 ∉ Set.range b' → b0 ∉ Set.range a → (∀ j v, l (E (a j) b0 v) = (if a j = a0 then p else 0) • l v) → ∃ e : ℂ, ‖e‖ = 1 ∧ ∀ u v, l (Formalism.REAL.qminor E a b u v) = (e * p) • l (Formalism.REAL.qminor E a' b' (u - 1) v) := by
  first | exact @GlobalTheory.CapStepCol.cap_step_col | exact GlobalTheory.CapStepCol.cap_step_col | (intros; apply GlobalTheory.CapStepCol.cap_step_col <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SplitExtComm

theorem isCommMonObj_of_dominant {S S' : Scheme.{0}} {f : S' ⟶ S} [QuasiCompact f]
    [IsSchemeTheoreticallyDominant f] {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
    [Flat A.hom] [IsSeparated A.hom] {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ)
    [IsCommMonObj A'] : IsCommMonObj A := by
  have := ExtUnique.flat_tensorObj A A
  have key : ∀ (T : Over S') (t : Over.mk (T.hom ≫ f) ⟶ A ⊗ A),
      t ≫ (β_ A A).hom ≫ μ[A] = t ≫ μ[A] := fun T t => by
    obtain ⟨x, hx⟩ := GrpDense.pushPt_surjective h.1 T (t ≫ fst _ _)
    obtain ⟨y, hy⟩ := GrpDense.pushPt_surjective h.1 T (t ≫ snd _ _)
    obtain rfl : t = lift (pushPt h.1.w x) (pushPt h.1.w y) :=
      CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, hx]) (by rw [lift_snd, hy])
    rw [lift_braiding_hom_assoc]
    exact Over.OverMorphism.ext ((h.2 T y x _ _ rfl rfl).trans
      ((congrArg (fun z => z.left ≫ φ) (_root_.mul_comm y x)).trans (h.2 T x y _ _ rfl rfl).symm))
  refine ⟨?_⟩
  refine ExtUnique.over_hom_ext_of_isPullback (IsPullback.of_hasPullback (A ⊗ A).hom f) ?_
  exact congrArg (fun z => z.left) (key (Over.mk (pullback.snd (A ⊗ A).hom f))
    (Over.homMk (pullback.fst (A ⊗ A).hom f) (by simpa using pullback.condition)))

end GlobalTheory.SplitExtComm
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.factorisation_of_conjHomogeneous_and_homogeneous : ∀ (T Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] (l : T → Wp) (l' : T → Wq) (J : T → T → (Wq →L[ℂ] Wp) → (Wq →L[ℂ] Wp)) (A : T → Wq → Wq → Wp) (Bb : T → Wp → Wq → Wp), (∀ y a c (t : ℂ), A y (t • a) c = star t • A y a c) → (∀ x b c (t : ℂ), Bb x (t • b) c = t • Bb x b c) → (∀ x y X c, J x y X c = A y (ContinuousLinearMap.adjoint X (l x)) c) → (∀ x y X c, J x y X c = Bb x (X (l' y)) c) → ∃ OO : Wq →L[ℂ] Wp, ∀ x y X, J x y X = ⟪l x, X (l' y)⟫_ℂ • OO := by
  first | exact @GlobalTheory.factorisation_of_two_partial_integrations | exact GlobalTheory.factorisation_of_two_partial_integrations | (intros; apply GlobalTheory.factorisation_of_two_partial_integrations <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.positive_rank_one_proportional : ∀ (T W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] (l₀ La : T → W), (∀ v w, ContinuousLinearMap.adjoint ((innerSL ℂ (La v)).smulRight (l₀ w)) = (innerSL ℂ (La w)).smulRight (l₀ v)) → (∀ v ξ, (⟪ξ, ((innerSL ℂ (La v)).smulRight (l₀ v)) ξ⟫_ℂ).im = 0 ∧ 0 ≤ (⟪ξ, ((innerSL ℂ (La v)).smulRight (l₀ v)) ξ⟫_ℂ).re) → (∃ v, l₀ v ≠ 0) → ∃ c : ℝ, 0 ≤ c ∧ ∀ v, La v = (c : ℂ) • l₀ v := by
  first | exact @GlobalTheory.hermitian_rankOne_kernel_shape | exact GlobalTheory.hermitian_rankOne_kernel_shape | (intros; apply GlobalTheory.hermitian_rankOne_kernel_shape <;> assumption)
end
