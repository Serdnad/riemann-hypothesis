module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Semisimple
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle017
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle019
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle009
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
public import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
import Formalism.FrobeniusOrbits.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

@[expose] public section

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.sUnits_union_sup_powers_eq_top_at_places : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [DecidableEq (HeightOneSpectrum (𝓞 F))] (S T : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → AdmP p F S → Disjoint S T → (∀ v ∈ T, ∃ u ∈ sUnits F S, u ∉ powSub p (algebraMap F (v.adicCompletion F)) ∧ ∀ v' ∈ T, v' ≠ v → u ∈ powSub p (algebraMap F (v'.adicCompletion F))) → sUnits F (S ∪ T) ⊔ finPow p F T = ⊤ := by
  first | exact @GlobalTheory.CNorm.sUnits_union_sup_finPow_eq_top | exact GlobalTheory.CNorm.sUnits_union_sup_finPow_eq_top | (intros; apply GlobalTheory.CNorm.sUnits_union_sup_finPow_eq_top <;> assumption)
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

theorem _root_.GlobalTheory.T.lattice_sum_dilate_haar_asymptotic : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (f : V → ℂ), ContDiff ℝ ∞ f → HasCompactSupport f → ∀ A : ℕ, ∃ C : ℝ, ∀ (x₀ : V) (t : ℝ), 0 < t → t ≤ 1 → ‖∑' l : L, f (t • ((l : V) + x₀)) - (∫ x, f x ∂μ) / ((ZLattice.covolume L μ * t ^ Module.finrank ℝ V : ℝ) : ℂ)‖ ≤ C * t ^ A := by
  exact @GlobalTheory.lattice_sum_dilate_haar
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem span_range_toMatrix_eq_top_of_isIrreducible {ι : Type} [Fintype ι] [DecidableEq ι]
    {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (b : Module.Basis ι ℂ V) (h : ρ.IsIrreducible) :
    Submodule.span ℂ (Set.range
      ((LinearMap.toMatrixAlgEquiv b : Module.End ℂ V →* Matrix ι ι ℂ).comp ρ)) = ⊤ := by
  have : FiniteDimensional ℂ V := Module.Finite.of_basis b
  have h1 := span_range_eq_top_of_isIrreducible G V ρ h
  have h2 : Set.range ((LinearMap.toMatrixAlgEquiv b : Module.End ℂ V →* Matrix ι ι ℂ).comp ρ) =
      (LinearMap.toMatrix b b).toLinearMap '' Set.range ρ := by
    rw [← Set.range_comp]; rfl
  rw [h2, ← Submodule.map_span, h1, Submodule.map_top, LinearMap.range_eq_top]
  exact (LinearMap.toMatrix b b).surjective

theorem isSemisimpleRepresentation_tprod_of_isIrreducible :
    ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ' : Representation ℂ G W) [FiniteDimensional ℂ V] [FiniteDimensional ℂ W], ρ.IsIrreducible → ρ'.IsIrreducible → (ρ.tprod ρ').IsSemisimpleRepresentation := by
  intro G _ V _ _ ρ W _ _ ρ' _ _ h h'
  let b := Module.finBasis ℂ V
  let b' := Module.finBasis ℂ W
  have key := GlobalTheory.T.isCompletelyReducible_kronecker_of_span_eq_top _ _ G _ _ (span_range_toMatrix_eq_top_of_isIrreducible ρ b h)
    (span_range_toMatrix_eq_top_of_isIrreducible ρ' b' h')
  rw [← ss_range_toMatrix_iff_isSemisimpleRepresentation _ G _ _ (b.tensorProduct b')]
  convert key using 3 with g
  rw [Representation.tprod_apply, TensorProduct.toMatrix_map]
  rfl

end GlobalTheory.ClassFin
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.IntegralFinAdele

variable (F : Type) [Field F] [NumberField F]

theorem t2Space_finiteAdeleRing' : T2Space (FiniteAdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))

theorem natCast_apply (M : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    (M : FiniteAdeleRing (𝓞 F) F) v = ((algebraMap (𝓞 F) F (M : 𝓞 F) : F) : v.adicCompletion F) := by
  rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)), FiniteAdeleRing.algebraMap_apply,
    map_natCast (algebraMap (𝓞 F) F)]

theorem mul_apply' (a b : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    (a * b) v = a v * b v := rfl

theorem pow_apply' (a : FiniteAdeleRing (𝓞 F) F) (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    (a ^ n) v = a v ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ n ih => rw [pow_succ, pow_succ, mul_apply', ih]

theorem eq_zero_of_forall_mul (a : FiniteAdeleRing (𝓞 F) F)
    (h : ∀ M : ℕ, 0 < M → ∃ c : FiniteAdeleRing (𝓞 F) F,
      (∀ v, c v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧
        a = (M : FiniteAdeleRing (𝓞 F) F) * c) : a = 0 := by
  refine FiniteAdeleRing.ext F fun v => ?_
  change a v = 0
  by_contra h0
  set N := Ideal.absNorm v.asIdeal with hN
  have hNpos : 0 < N := Nat.pos_of_ne_zero (by
    rw [hN, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  have hlt : Valued.v ((N : FiniteAdeleRing (𝓞 F) F) v) < 1 := by
    rw [natCast_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact Ideal.absNorm_mem _
  have hv0 : Valued.v (a v) ≠ 0 := by simpa using h0
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hlt (Units.mk0 _ hv0)
  obtain ⟨c, hc, hac⟩ := h (N ^ n) (pow_pos hNpos n)
  have hc' : Valued.v (c v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hc v)
  have : Valued.v (a v) ≤ Valued.v ((N : FiniteAdeleRing (𝓞 F) F) v) ^ n := by
    conv_lhs => rw [hac]
    rw [mul_apply', Nat.cast_pow, pow_apply', map_mul, map_pow]
    exact mul_le_of_le_one_right' hc'
  exact absurd hn (not_lt.2 this)

theorem exists_nat_mul_integral (a : FiniteAdeleRing (𝓞 F) F) :
    ∃ M : ℕ, 0 < M ∧ ∀ v, ((M : FiniteAdeleRing (𝓞 F) F) * a) v ∈
      HeightOneSpectrum.adicCompletionIntegers F v := by
  obtain ⟨x, b, hb, hab⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F 1 one_pos a
  haveI : Algebra.IsAlgebraic ℤ F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := F)).2 inferInstance
  obtain ⟨m, y, hm, hmx⟩ := IsAlgebraic.exists_nsmul_eq (𝓞 F)
    (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) x)
  refine ⟨m, Nat.pos_of_ne_zero hm, fun v => ?_⟩
  have h : (m : FiniteAdeleRing (𝓞 F) F) * a =
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F y) +
        (m : FiniteAdeleRing (𝓞 F) F) * b := by
    rw [hab, ← hmx, one_smul, map_nsmul, nsmul_eq_mul, mul_add]
  rw [h]
  refine add_mem (HeightOneSpectrum.coe_mem_adicCompletionIntegers v y) (mul_mem ?_ (hb v))
  exact natCast_apply F m v ▸ HeightOneSpectrum.coe_mem_adicCompletionIntegers v (m : 𝓞 F)

theorem integral_finiteAdele_properties : ∀ (F : Type) [Field F] [NumberField F], IsCompact {a : FiniteAdeleRing (𝓞 F) F | (∀ v, (a : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v)} ∧ (∀ M : ℕ, 0 < M → IsClosed {a : FiniteAdeleRing (𝓞 F) F | ∃ c : FiniteAdeleRing (𝓞 F) F, (∀ v, (c : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ a = (M : FiniteAdeleRing (𝓞 F) F) * c}) ∧ (∀ a : FiniteAdeleRing (𝓞 F) F, (∀ M : ℕ, 0 < M → ∃ c : FiniteAdeleRing (𝓞 F) F, (∀ v, (c : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ a = (M : FiniteAdeleRing (𝓞 F) F) * c) → a = 0) ∧ (∀ x : F, (∀ v, (algebraMap F (FiniteAdeleRing (𝓞 F) F) x : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) → ∃ y : 𝓞 F, x = y) ∧ (∀ a : FiniteAdeleRing (𝓞 F) F, ∃ M : ℕ, 0 < M ∧ (∀ v, (((M : FiniteAdeleRing (𝓞 F) F) * a) : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v)) ∧ IsReduced (FiniteAdeleRing (𝓞 F) F) := by
  intro F _ _
  refine ⟨GlobalTheory.AdeleCocompact.isCompact_integral F, fun M _ => ?_, eq_zero_of_forall_mul F,
    fun x hx => ?_, exists_nat_mul_integral F, ⟨fun a ⟨n, hn⟩ => ?_⟩⟩
  · haveI := t2Space_finiteAdeleRing' F
    have h := ((GlobalTheory.AdeleCocompact.isCompact_integral F).image
      (continuous_const_mul (M : FiniteAdeleRing (𝓞 F) F))).isClosed
    convert h using 1
    ext a
    simp only [Set.mem_image, Set.mem_setOf_eq, eq_comm]
  · obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F x fun v => by
      have := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hx v)
      rwa [FiniteAdeleRing.algebraMap_apply,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
    exact ⟨y, hy.symm⟩
  · refine FiniteAdeleRing.ext F fun v => ?_
    have : a v ^ n = 0 := by rw [← pow_apply', hn]; rfl
    exact eq_zero_of_pow_eq_zero this

end GlobalTheory.IntegralFinAdele
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory.AdeleBaseChange

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.L2.DIV Formalism.UG Formalism.UG.P

theorem exists_tensor_finiteAdele_equiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ ι : FiniteAdeleRing (𝓞 F) F ⊗[F] E ≃+* FiniteAdeleRing (𝓞 E) E, (∀ x : E, ι (1 ⊗ₜ[F] x) = algebraMap E _ x) ∧ (∀ y, y ∈ AddSubgroup.closure {y : FiniteAdeleRing (𝓞 F) F ⊗[F] E | ∃ a ∈ {a : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F}, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} ↔ ∀ P, Valued.v (ι y P) ≤ 1) ∧ ∀ (v : HeightOneSpectrum (𝓞 F)) (α : FiniteAdeleRing (𝓞 F) F), α v = 1 → (∀ v', v' ≠ v → α v' = 0) → ∀ P : HeightOneSpectrum (𝓞 E), ι (α ⊗ₜ[F] 1) P = if P.under (𝓞 F) = v then 1 else 0 := by
  intro F E _ _ _ _ _
  obtain ⟨ι, hι⟩ := exists_toAd F E
  let c : FiniteAdeleRing (𝓞 F) F ⊗[F] E ≃+* AfE F E :=
    (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).toRingEquiv
  have hc : ∀ a x, c (a ⊗ₜ[F] x) = x ⊗ₜ[F] a := fun a x => rfl
  have hc' : ∀ a x, c.symm (x ⊗ₜ[F] a) = a ⊗ₜ[F] x := fun a x => rfl
  let j := c.trans (RingEquiv.ofBijective ι ⟨map_injective hι, map_surjective hι⟩)
  have hj : ∀ y, j y = ι (c y) := fun y => rfl
  refine ⟨j, fun x => ?_, fun y => ⟨fun hy => ?_, fun hy => ?_⟩, fun v α h1 h0 P => ?_⟩
  · rw [hj, hc, map_tmul_one hι]
  · have : j y ∈ intAd E := by
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, ha, x, rfl⟩ := hy
        rw [hj, hc]
        exact map_mem_int hι (levelaf_tmul_mem x ha)
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | neg x _ hx => rw [map_neg]; exact neg_mem hx
    exact this
  · have h : c y ∈ RInt F E := mem_int_of_map hι hy
    obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
    obtain ⟨r, hr, e⟩ := levelaf_decomp g hg h
    have e' : y = c.symm (c y) := (c.symm_apply_apply y).symm

    rw [e', e, map_sum]
    refine sum_mem fun i _ => AddSubgroup.subset_closure ⟨r i, hr i, g i, ?_⟩
    rw [hc']
  · rw [hj, hc, hι, map_one, one_mul, adMap_apply]
    split_ifs with h
    · subst h
      rw [h1, map_one]
    · rw [h0 _ h, map_zero]

end GlobalTheory.AdeleBaseChange
end

section

open NumberField IsDedekindDomain MeasureTheory Polynomial

namespace GlobalTheory.GLIntegral

section general

variable {A : Type} [CommRing A] {ι : Type} [Fintype ι] [DecidableEq ι]

def glSub (S : Subring A) : Subgroup (GL ι A) where
  carrier := {g | (∀ i j, (g : Matrix ι ι A) i j ∈ S) ∧ ∀ i j, ((g⁻¹ : GL ι A) : Matrix ι ι A) i j ∈ S}
  one_mem' := by
    have h : ∀ i j, (1 : Matrix ι ι A) i j ∈ S := fun i j => by
      rw [Matrix.one_apply]; split_ifs
      exacts [S.one_mem, S.zero_mem]
    exact ⟨h, by simpa using h⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [Units.val_mul, Matrix.mul_apply]
      exact S.sum_mem fun k _ => S.mul_mem (ha _ _) (hb _ _)
    · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
      exact S.sum_mem fun k _ => S.mul_mem (hb' _ _) (ha' _ _)
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨ha', by rw [inv_inv]; exact ha⟩

variable [TopologicalSpace A] [IsTopologicalRing A]

omit [IsTopologicalRing A] in
theorem isOpen_glSub (S : Subring A) (hS : IsOpen (S : Set A)) :
    IsOpen (glSub (ι := ι) S : Set (GL ι A)) := by
  have h : IsOpen {m : Matrix ι ι A | ∀ i j, m i j ∈ S} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hS.preimage (continuous_id.matrix_elem i j)
  exact (h.preimage Units.continuous_val).inter (h.preimage Units.continuous_coe_inv)

theorem isCompact_glSub [T2Space A] (S : Subring A) (hS : IsCompact (S : Set A)) :
    IsCompact (glSub (ι := ι) S : Set (GL ι A)) := by
  have h : IsCompact {m : Matrix ι ι A | ∀ i j, m i j ∈ S} := by
    have := isCompact_univ_pi fun _ : ι => isCompact_univ_pi fun _ : ι => hS
    have e : {m : Matrix ι ι A | ∀ i j, m i j ∈ S} =
        Set.pi Set.univ fun _ : ι => Set.pi Set.univ fun _ : ι => (S : Set A) :=
      Set.ext fun m => ⟨fun hm i _ j _ => hm i j, fun hm i j => hm i trivial j trivial⟩
    rw [e]; exact this
  have h2 := (Units.isClosedEmbedding_embedProduct (α := Matrix ι ι A)).isCompact_preimage
    (h.prod (h.image MulOpposite.continuous_op))
  convert h2 using 1
  ext g
  constructor
  · rintro ⟨h1, h1'⟩
    exact ⟨h1, _, h1', rfl⟩
  · rintro ⟨h1, m, hm, hm'⟩
    refine ⟨h1, ?_⟩
    have : m = ((g⁻¹ : GL ι A) : Matrix ι ι A) := MulOpposite.op_injective hm'
    rw [← this]; exact hm

end general

def intSubring (F : Type) [Field F] [NumberField F] : Subring (FiniteAdeleRing (𝓞 F) F) where
  carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers F}
  mul_mem' := fun ha hb v => mul_mem (ha v) (hb v)
  one_mem' := fun v => one_mem (v.adicCompletionIntegers F)
  add_mem' := fun ha hb v => add_mem (ha v) (hb v)
  zero_mem' := fun v => zero_mem (v.adicCompletionIntegers F)
  neg_mem' := fun ha v => neg_mem (ha v)

theorem exists_isOpen_isCompact : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), ∃ U : Subgroup (GL (Fin n) (FiniteAdeleRing (𝓞 F) F)), IsOpen (U : Set (GL (Fin n) (FiniteAdeleRing (𝓞 F) F))) ∧ IsCompact (U : Set (GL (Fin n) (FiniteAdeleRing (𝓞 F) F))) := by
  intro F _ _ n
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))
  refine ⟨glSub (intSubring F), isOpen_glSub _ ?_,
    isCompact_glSub _ (GlobalTheory.AdeleCocompact.isCompact_integral F)⟩
  exact RestrictedProduct.isOpen_forall_mem
    (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _)

end GlobalTheory.GLIntegral
end
