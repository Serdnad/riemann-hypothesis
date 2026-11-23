module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
public import Formalism.HermitianLattices.FinalMass
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle959
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle960
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle961
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle955
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Mathlib.RingTheory.DividedPowers.Basic
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Localization.Integer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory NumberField IsDedekindDomain
open GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts GlobalTheory.BlockSizes

namespace GlobalTheory.StdMassLower

section
variable {E : Type} [Field E] [NumberField E]

theorem eq_zero_of_norm_lt_one (z : 𝓞 E) (h : ∀ φ : E →+* ℂ, ‖φ (z : E)‖ < 1) : z = 0 := by
  classical
  by_contra hz
  have h0 : Algebra.norm ℤ z ≠ 0 := Algebra.norm_ne_zero_iff.2 hz
  have h1 : (1 : ℝ) ≤ |((Algebra.norm ℤ z : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs h0
  have h2 := congrArg norm (Algebra.norm_eq_prod_embeddings ℚ ℂ (z : E))
  rw [← Algebra.coe_norm_int, norm_prod] at h2
  have h3 : ∏ σ : E →ₐ[ℚ] ℂ, ‖σ (z : E)‖ < 1 := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    calc ∏ σ : E →ₐ[ℚ] ℂ, ‖σ (z : E)‖ ≤ ‖τ.toRatAlgHom (z : E)‖ := by
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ.toRatAlgHom)]
          exact mul_le_of_le_one_right (norm_nonneg _)
            (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun σ _ => (h σ.toRingHom).le)
      _ < 1 := h τ
  rw [← h2] at h3
  simp only [eq_ratCast, Rat.cast_intCast, Complex.norm_intCast] at h3
  linarith

theorem eq_of_mk_eq (x y : 𝓞 E) (hx : ∀ φ : E →+* ℂ, ‖φ (x : E)‖ ≤ 1) (hy : ∀ φ : E →+* ℂ, ‖φ (y : E)‖ ≤ 1)
    (h : Ideal.Quotient.mk (Ideal.span {(3 : 𝓞 E)}) x = Ideal.Quotient.mk _ y) : x = y := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
  obtain ⟨z, hz⟩ := h
  have : z = 0 := eq_zero_of_norm_lt_one z fun φ => by
    have e : φ (x : E) - φ (y : E) = 3 * φ (z : E) := by
      have := congrArg (fun t : 𝓞 E => φ (algebraMap (𝓞 E) E t)) hz
      simpa only [map_sub, map_mul, map_ofNat] using this
    have e2 := norm_sub_le (φ (x : E)) (φ (y : E))
    rw [e, norm_mul] at e2
    have := hx φ
    have := hy φ
    simp only [Complex.norm_ofNat] at e2
    linarith
  rw [this, mul_zero] at hz
  exact sub_eq_zero.1 hz

theorem card_quot_three :
    Nat.card (𝓞 E ⧸ Ideal.span {(3 : 𝓞 E)}) = 3 ^ Module.finrank ℚ E := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]
  have : (3 : 𝓞 E) = algebraMap ℤ (𝓞 E) 3 := by simp
  rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
  simp

theorem coord_of_mem {n : ℕ} {x : Fin n → E} (hx : x ∈ Formalism.MainNotions.StandardLattice.stdLat E n) (i : Fin n) :
    ∃ a : 𝓞 E, (a : E) = x i := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    by_cases h : i = j
    · exact ⟨1, by simp [h]⟩
    · exact ⟨0, by simp [h]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp [← ha, ← hb]⟩
  | smul r x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨r * a, by simp [← ha, Algebra.smul_def]⟩

theorem isLattice_std (n : ℕ) : Submodule.IsFullLattice E (Formalism.MainNotions.StandardLattice.stdLat E n) := by
  have : Submodule.IsLattice E (Formalism.MainNotions.StandardLattice.stdLat E n) :=
    Submodule.IsLattice.of_fg E (Submodule.fg_span (Set.finite_range _))
  refine { span_eq_top := ?_ }
  rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨j, rfl⟩
  rw [Pi.basisFun_apply]
  exact Submodule.subset_span ⟨j, rfl⟩

variable [StarRing E]

omit [NumberField E] in
theorem re_form (hφ : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) {n : ℕ} (x : Fin n → E)
    (τ : E →+* ℂ) : (τ (Formalism.MainNotions.StandardLattice.stdForm E n x x)).re = ∑ i, Complex.normSq (τ (x i)) := by
  change (τ (∑ i, star (x i) * x i)).re = _

  rw [map_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, hφ, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

theorem trace_pos (hφ : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) {n : ℕ} (x : Fin n → E)
    (hx : x ≠ 0) : 0 < Algebra.trace ℚ E (Formalism.MainNotions.StandardLattice.stdForm E n x x) := by
  have h1 := congrArg Complex.re
    (trace_eq_sum_embeddings ℂ (K := ℚ) (L := E) (x := Formalism.MainNotions.StandardLattice.stdForm E n x x))
  rw [Complex.re_sum] at h1
  have h2 : 0 < ∑ σ : E →ₐ[ℚ] ℂ, (σ (Formalism.MainNotions.StandardLattice.stdForm E n x x)).re := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine Finset.sum_pos (fun σ _ => ?_) ⟨τ.toRatAlgHom, Finset.mem_univ _⟩
    refine lt_of_lt_of_eq ?_ (re_form hφ x σ.toRingHom).symm
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
    refine Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, ?_⟩
    exact Complex.normSq_pos.2 ((map_ne_zero σ.toRingHom).2 hi)
  rw [← h1] at h2
  simpa using h2

omit [NumberField E] in
theorem isSymm_std (n : ℕ) : (Formalism.MainNotions.StandardLattice.stdForm E n).IsSymm := by
  constructor
  intro x y
  change starRingEnd _ (∑ i, star (x i) * y i) = ∑ i, star (y i) * x i

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [starRingEnd_apply, star_mul, star_star]


omit [NumberField E] in
theorem norm_entry_le (hφ : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) {n : ℕ}
    {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} (hg : g ∈ Formalism.HermitianLatticesTheory.isom (Formalism.MainNotions.StandardLattice.stdForm E n)) (j i : Fin n)
    (τ : E →+* ℂ) : ‖τ (g (Pi.single j 1) i)‖ ≤ 1 := by
  have e : Formalism.MainNotions.StandardLattice.stdForm E n (g (Pi.single j 1)) (g (Pi.single j 1)) = 1 := by
    rw [hg]
    change ∑ i, star ((Pi.single j (1 : E) : Fin n → E) i) * (Pi.single j (1 : E) : Fin n → E) i = 1
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
    simp
  have h1 := re_form hφ (g (Pi.single j 1)) τ
  rw [e, map_one, Complex.one_re] at h1
  have h2 := Finset.single_le_sum (f := fun i => Complex.normSq (τ (g (Pi.single j 1) i)))
    (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  rw [← h1, Complex.normSq_eq_norm_sq] at h2
  exact (sq_le_one_iff₀ (norm_nonneg _)).1 h2

theorem card_aut_std (hφ : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) (n : ℕ) :
    Finite (Formalism.ThetaLiftIndependence.autL (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n)) ∧
    Nat.card (Formalism.ThetaLiftIndependence.autL (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n)) ≤
      3 ^ (Module.finrank ℚ E * n ^ 2) := by
  have hm : ∀ (g : Formalism.ThetaLiftIndependence.autL (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n)) (j i : Fin n),
      ∃ a : 𝓞 E, (a : E) = g.1 (Pi.single j 1) i := fun g j i => by
    refine coord_of_mem ?_ i
    exact g.2.2.le ⟨_, Submodule.subset_span ⟨j, rfl⟩, rfl⟩
  choose a ha using hm
  have hq := card_quot_three (E := E)
  haveI : Finite (𝓞 E ⧸ Ideal.span {(3 : 𝓞 E)}) := Nat.finite_of_card_ne_zero (by rw [hq]; positivity)
  have hinj : Function.Injective fun g j i => Ideal.Quotient.mk (Ideal.span {(3 : 𝓞 E)}) (a g j i) := by
    intro g g' h
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    refine (Pi.basisFun E (Fin n)).ext fun j => ?_
    funext i
    rw [Pi.basisFun_apply]
    change g.1 _ i = g'.1 _ i
    rw [← ha, ← ha, eq_of_mk_eq (a g j i) (a g' j i) (fun φ => ?_) (fun φ => ?_) (congrFun (congrFun h j) i)]
    · rw [ha]; exact norm_entry_le hφ g.2.1 j i φ
    · rw [ha]; exact norm_entry_le hφ g'.2.1 j i φ
  refine ⟨Finite.of_injective _ hinj, (Nat.card_le_card_of_injective _ hinj).trans_eq ?_⟩
  rw [Nat.card_fun, Nat.card_fun, hq, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul, ← pow_mul, sq]

end

theorem card_aut_gmap {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (N : Submodule (𝓞 K) V) :
    Nat.card (Formalism.ThetaLiftIndependence.autL h N) = Nat.card (Formalism.ThetaLiftIndependence.autL h (Formalism.HermitianLatticesTheory.gmap g N)) := by
  have hmul : ∀ (a b : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V),
      Formalism.HermitianLatticesTheory.gmap (a * b) M = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b M) := fun a b M => by
    unfold Formalism.HermitianLatticesTheory.gmap
    rw [← Submodule.map_comp]
    rfl
  have hone : ∀ M : Submodule (𝓞 K) V, Formalism.HermitianLatticesTheory.gmap (1 : V ≃ₗ[K] V) M = M := fun M => Submodule.map_id M
  refine Nat.card_congr
    { toFun := fun u => ⟨g * u.1 * g⁻¹, mul_mem (mul_mem hg u.2.1) (inv_mem hg), ?_⟩
      invFun := fun u => ⟨g⁻¹ * u.1 * g, mul_mem (mul_mem (inv_mem hg) u.2.1) hg, ?_⟩
      left_inv := fun u => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc]) }
  · rw [← hmul, inv_mul_cancel_right, hmul, u.2.2]
  · rw [hmul, hmul, u.2.2, ← hmul, inv_mul_cancel, hone]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing E], (∀ x : E, star x = IsCMField.complexConj E x) → ∀ n : ℕ, ((3 : ℝ) ^ (Module.finrank ℚ E * n ^ 2))⁻¹ ≤ Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n) := by
  intro E _ _ _ _ hst n
  have hφ : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a) := fun φ a => by
    rw [hst, IsCMField.complexEmbedding_complexConj]
  obtain ⟨⟨s, hs⟩, hm, -⟩ := Formalism.HermitianLatticesTheory.final_massBasic E (Fin n → E) _ (isSymm_std n) (trace_pos hφ) _
    (isLattice_std n)
  obtain ⟨N, ⟨hN, g, hg, e⟩, -⟩ := hs.2 (Formalism.MainNotions.StandardLattice.stdLat E n)
    ⟨isLattice_std n, fun p _ => ⟨1, one_mem _, Submodule.map_id _⟩⟩
  obtain ⟨hf, hc⟩ := card_aut_std hφ n
  haveI : Nonempty (Formalism.ThetaLiftIndependence.autL (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n)) :=
    ⟨⟨1, one_mem _, Submodule.map_id _⟩⟩
  have hp : 0 < Nat.card (Formalism.ThetaLiftIndependence.autL (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n)) := Nat.card_pos
  rw [hm s hs]
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun M => ((Nat.card (Formalism.ThetaLiftIndependence.autL (Formalism.MainNotions.StandardLattice.stdForm E n) M) : ℝ))⁻¹) (fun _ _ => by positivity) hN)
  beta_reduce
  rw [card_aut_gmap _ hg N, e]
  exact inv_anti₀ (by exact_mod_cast hp) (by exact_mod_cast hc)

end GlobalTheory.StdMassLower
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isCompl_of_agree_mod_sqZero_ideal : ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = 0 → ∀ (C : Type 1) [AddCommGroup C] [Module R C] (F K N : Submodule R C), IsCompl F N → K ⊔ I • ⊤ = F ⊔ I • ⊤ → ((K ⊓ I • ⊤ = F ⊓ I • ⊤ → IsCompl K N) ∧ ((∃ N', IsCompl K N') → K ⊓ I • ⊤ = F ⊓ I • ⊤ ∧ ∃ u : F →ₗ[R] C, (∀ c, u c ∈ I • (⊤ : Submodule R C) ∧ u c ∈ N ∧ c.1 - u c ∈ K) ∧ (∀ c : F, c.1 ∈ I • (⊤ : Submodule R C) → u c = 0) ∧ ∀ k ∈ K, ∃ c : F, k = c.1 - u c)) := by
  first | exact @GlobalTheory.SqZeroSummand.summand_of_agree_mod_sqZero | exact GlobalTheory.SqZeroSummand.summand_of_agree_mod_sqZero | (intros; apply GlobalTheory.SqZeroSummand.summand_of_agree_mod_sqZero <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.eq_comp_section_of_proper_smooth_nilpotent_rigidity : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (P X : Over (Sp R)) (P₀ : Over (Sp R₀)) (l : P₀.left ⟶ P.left), IsPullback l P₀.hom P.hom (spMap π) →
    Smooth P.hom → IsProper P.hom → GeometricallyConnected P.hom →
    ∀ (ε : Sp R ⟶ P.left), ε ≫ P.hom = 𝟙 _ → ∀ (f : P ⟶ X) (s₀ : Sp R₀ ⟶ X.left), l ≫ f.left = P₀.hom ≫ s₀ →
    f.left = P.hom ≫ ε ≫ f.left := by
  first | exact @GlobalTheory.Rigidity.eq_comp_section | exact GlobalTheory.Rigidity.eq_comp_section | (intros; apply GlobalTheory.Rigidity.eq_comp_section <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.isProper_geometricallyConnected_smooth_nilpotent_lift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    IsProper X₀.hom → GeometricallyConnected X₀.hom → IsProper X.hom ∧ GeometricallyConnected X.hom := by
  first | exact @GlobalTheory.NilLift.isProper_and_geometricallyConnected_of_smooth_lift | exact GlobalTheory.NilLift.isProper_and_geometricallyConnected_of_smooth_lift | (intros; apply GlobalTheory.NilLift.isProper_and_geometricallyConnected_of_smooth_lift <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

theorem _root_.GlobalTheory.T.smoothOfRelDim_geomConnected_descend_fieldExtension : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → ∀ D : ℕ, Nonempty X → SmoothOfRelativeDimension D q → GeometricallyConnected q → SmoothOfRelativeDimension D p ∧ GeometricallyConnected p := by
  first | exact @GlobalTheory.FieldDescentSm.smoothOfRelativeDimension_and_geometricallyConnected_descend | exact GlobalTheory.FieldDescentSm.smoothOfRelativeDimension_and_geometricallyConnected_descend | (intros; apply GlobalTheory.FieldDescentSm.smoothOfRelativeDimension_and_geometricallyConnected_descend <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_smooth_proper_model_finitelyGenerated_subring : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (f : X ⟶ Sp k), Smooth f → IsProper f → ∃ (R : Subring k) (X₀ : Scheme.{0}) (f₀ : X₀ ⟶ Sp R) (π : X ⟶ X₀), Algebra.FiniteType ℤ R ∧ Smooth f₀ ∧ IsProper f₀ ∧ IsPullback π f f₀ (spMap R.subtype) := by
  first | exact @GlobalTheory.SmoothProperModel.exists_smooth_proper_model | exact GlobalTheory.SmoothProperModel.exists_smooth_proper_model | (intros; apply GlobalTheory.SmoothProperModel.exists_smooth_proper_model <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_integral_clopen_cover_of_smooth_quasiCompact_field : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k) [Smooth f] [QuasiCompact f], ∃ (κ : Type) (U : κ → X.Opens), ⨆ c, U c = ⊤ ∧ (Pairwise fun a b => Disjoint (U a) (U b)) ∧ ∀ c, IsIntegral (U c).toScheme ∧ IsClosedImmersion (U c).ι := by
  first | exact @GlobalTheory.exists_integral_clopen_cover_of_smooth_field | exact GlobalTheory.exists_integral_clopen_cover_of_smooth_field | (intros; apply GlobalTheory.exists_integral_clopen_cover_of_smooth_field <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_section_lift_smooth_nilpotent_thickening : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    ∀ e₀ : Sp R₀ ⟶ X₀.left, e₀ ≫ X₀.hom = 𝟙 _ → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ e₀ ≫ i = spMap π ≫ e := by
  first | exact @GlobalTheory.SecLift.exists_section_lift | exact GlobalTheory.SecLift.exists_section_lift | (intros; apply GlobalTheory.SecLift.exists_section_lift <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.universallyClosed_open_containing_fibre_contains_nearby : ∀ (R k : Type) [CommRing R] [Field k] (φ : R →+* k) (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp k) (π : X' ⟶ X) [UniversallyClosed f] (W : X.Opens), IsPullback π f' f (spMap φ) → π ⁻¹ᵁ W = ⊤ → ∃ a : R, φ a ≠ 0 ∧ ∀ (T : Type) [CommRing T] (χ : R →+* T), IsUnit (χ a) → ∀ (Z : Scheme.{0}) (g : Z ⟶ Sp T) (ρ : Z ⟶ X), IsPullback ρ g f (spMap χ) → ρ ⁻¹ᵁ W = ⊤ := by
  first | exact @GlobalTheory.tube_of_universallyClosed | exact GlobalTheory.tube_of_universallyClosed | (intros; apply GlobalTheory.tube_of_universallyClosed <;> assumption)
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM

namespace GlobalTheory.PolFan

theorem eq_zero_of_linearIndependent_int_rat {Y ι : Type} [Fintype ι] {f : ι → Y → ℤ}
    (hf : LinearIndependent ℤ f) (q : ι → ℚ) (hq : ∀ y, ∑ i, q i * (f i y : ℚ) = 0) : q = 0 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) q
  have hb' : ∀ i, ∃ r : ℤ, (r : ℚ) = ((b : ℤ) : ℚ) * q i := fun i => by
    obtain ⟨r, hr⟩ := hb i
    exact ⟨r, by simpa [Algebra.smul_def] using hr⟩
  choose n hn using hb'
  have h0 : n = 0 := by
    rw [Fintype.linearIndependent_iff] at hf
    funext i
    refine hf n ?_ i
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have : ((∑ i, n i * f i y : ℤ) : ℚ) = ((b : ℤ) : ℚ) * ∑ i, q i * (f i y : ℚ) := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hn i]; ring
    rw [hq y, mul_zero] at this
    exact_mod_cast this
  funext i
  have hbne : ((b : ℤ) : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero b
  have h := hn i
  rw [h0] at h
  simp only [Pi.zero_apply, Int.cast_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hbne

theorem eq_zero_of_linearIndependent_int {Y ι : Type} [Fintype ι] {f : ι → Y → ℤ}
    (hf : LinearIndependent ℤ f) (k : Type) [Field k] [CharZero k] (a : ι → k)
    (ha : ∀ y, ∑ i, a i * (f i y : k) = 0) : a = 0 := by
  classical
  let B := Module.Basis.ofVectorSpace ℚ k
  have key : ∀ j, (fun i => B.coord j (a i)) = 0 := fun j =>
    eq_zero_of_linearIndependent_int_rat hf _ fun y => by
      have h := congrArg (B.coord j) (ha y)

      rw [map_sum, map_zero] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm (a i), ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, mul_comm]
  funext i
  apply B.repr.injective
  ext j
  have := congrFun (key j) i
  simpa [Module.Basis.coord_apply] using this

end GlobalTheory.PolFan

namespace GlobalTheory.PolFan

end GlobalTheory.PolFan
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_abelianScheme_restrict_openImmersion : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → Out.Rigidified A L → Out.RelAmple A L → ∀ (V : Scheme.{0}) (j : V ⟶ S), IsOpenImmersion j → ∃ (A' : Over V) (_ : GrpObj A') (_ : IsCommMonObj A') (φ : A'.left ⟶ A.left), IsGrpPullback A' A j φ ∧ IsAbelianScheme A' ∧ (L.pull φ).IsLB ∧ Out.Rigidified A' (L.pull φ) ∧ Out.RelAmple A' (L.pull φ) := by
  first | exact @GlobalTheory.OpenRestrictPol.exists_restrict_open | exact GlobalTheory.OpenRestrictPol.exists_restrict_open | (intros; apply GlobalTheory.OpenRestrictPol.exists_restrict_open <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_intermediate_grpPullback_abelianScheme : ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (ρ : R →+* R₁) (π₁ : R₁ →+* R₀) (g : ℕ)
    (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left),
    IsGrpPullback A₀ A (spMap (π₁.comp ρ)) i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∃ (A₁ : Over (Sp R₁)) (_ : GrpObj A₁) (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left),
      IsGrpPullback A₀ A₁ (spMap π₁) i₁ ∧ IsGrpPullback A₁ A (spMap ρ) i₂ ∧ i₁ ≫ i₂ = i ∧ IsAbelianScheme A₁ ∧
      SmoothOfRelativeDimension g A₁.hom := by
  first | exact @GlobalTheory.SqLift.exists_intermediate_grpPullback | exact GlobalTheory.SqLift.exists_intermediate_grpPullback | (intros; apply GlobalTheory.SqLift.exists_intermediate_grpPullback <;> assumption)
end
