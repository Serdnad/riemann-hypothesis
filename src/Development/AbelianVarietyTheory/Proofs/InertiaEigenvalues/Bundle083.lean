module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle026
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle007
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle028
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle021
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle029
public import Mathlib.GroupTheory.Index
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle027
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNotXPowDvdAdjugateOfFirstOrderKernel
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
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

section

open scoped BigOperators

theorem _root_.GlobalTheory.T.prime_pow_sub_dvd_choose_prime_pow_of_lt : ∀ (l a c i : ℕ), l.Prime → 1 ≤ i → i < l ^ (c + 1) → l ^ (a - c) ∣ (l ^ a).choose i := by
  first | exact @GlobalTheory.pow_sub_dvd_choose_prime_pow_of_lt | exact GlobalTheory.pow_sub_dvd_choose_prime_pow_of_lt | (intros; apply GlobalTheory.pow_sub_dvd_choose_prime_pow_of_lt <;> assumption)
end

section

open Function

theorem _root_.GlobalTheory.T.finite_of_bijective_pairing_zmod : ∀ (n : ℕ) [NeZero n] (A B C : Type) [AddCommGroup A] [Module (ZMod n) A] [AddCommGroup B] [Module (ZMod n) B] [AddCommGroup C] [Module (ZMod n) C] [Finite C] (b : A →ₗ[ZMod n] B →ₗ[ZMod n] C), Nonempty (C ≃ₗ[ZMod n] ZMod n) → Bijective b → Bijective b.flip → Finite A ∧ Finite B := by
  first | exact @GlobalTheory.finite_of_perfect_pairing_zmod | exact GlobalTheory.finite_of_perfect_pairing_zmod | (intros; apply GlobalTheory.finite_of_perfect_pairing_zmod <;> assumption)
end

section


theorem _root_.GlobalTheory.T.eq_zero_of_sum_map_mul_eq_zero_of_linearIndependent : ∀ (k Ω D : Type) [Field k] [Field Ω] [Field D] [Algebra k Ω] [IsGalois k Ω] (o : Ω →+* D) (F : Subfield D), (∀ x : Ω, o x ∈ F ↔ x ∈ (algebraMap k Ω).range) → ∀ (m : ℕ) (x : Fin m → Ω), LinearIndependent k x → ∀ b : Fin m → D, (∀ i, b i ∈ F) → ∑ i, o (x i) * b i = 0 → ∀ i, b i = 0 := by
  first | exact @GlobalTheory.GalDisj.galois_linearDisjoint | exact GlobalTheory.GalDisj.galois_linearDisjoint | (intros; apply GlobalTheory.GalDisj.galois_linearDisjoint <;> assumption)
end

section


theorem _root_.GlobalTheory.T.eq_zero_of_sum_mul_embeddings_eq_zero' : ∀ (F Ω L : Type) [Field F] [CharZero F] [Field Ω] [IsAlgClosed Ω] [Algebra F Ω] [Field L] [Algebra F L] [FiniteDimensional F L] (m : ℕ) (e : Fin m → Ω), LinearIndependent F e → (∀ t, IsAlgebraic F (e t)) → ∀ a : Fin m → L, (∀ σ : L →ₐ[F] Ω, ∑ t, e t * σ (a t) = 0) → a = 0 := by
  first | exact @GlobalTheory.eq_zero_of_sum_mul_embeddings_eq_zero | exact GlobalTheory.eq_zero_of_sum_mul_embeddings_eq_zero | (intros; apply GlobalTheory.eq_zero_of_sum_mul_embeddings_eq_zero <;> assumption)
end

section

open scoped NNReal

theorem _root_.GlobalTheory.T.exists_valuationSubring_algClosed_not_isUnit : ∀ (S : Type) [CommRing S] (u : S), ¬ IsUnit u → ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (V : ValuationSubring L) (f : S →+* ↥V), ¬ IsUnit (f u) ∧ ∀ s ∈ nonZeroDivisors S, f s ≠ 0 := by
  first | exact @GlobalTheory.exists_valuationSubring_not_isUnit_and_nonZeroDivisors_ne_zero | exact GlobalTheory.exists_valuationSubring_not_isUnit_and_nonZeroDivisors_ne_zero | (intros; apply GlobalTheory.exists_valuationSubring_not_isUnit_and_nonZeroDivisors_ne_zero <;> assumption)
end

section

open scoped NNReal

theorem _root_.GlobalTheory.T.adicCompletion_principal_perfect : ∀ (l : ℕ) [Fact l.Prime] (V : Type) [CommRing V] [CharP V l] [PerfectRing V l] (x : V), ((l : ℕ) : AdicCompletion (Ideal.span {x}) V) = 0 ∧ Function.Bijective fun y : AdicCompletion (Ideal.span {x}) V => y ^ l := by
  first | exact @GlobalTheory.PerfectCompletion.perfect | exact GlobalTheory.PerfectCompletion.perfect | (intros; apply GlobalTheory.PerfectCompletion.perfect <;> assumption)
end

section

open scoped NNReal

theorem _root_.GlobalTheory.T.ringHom_eq_of_perfect_of_dvd_sub_adicSeparated : ∀ (l : ℕ) [Fact l.Prime] (R O : Type) [CommRing R] [CharP R l] [PerfectRing R l] [CommRing O] [CharP O l] (x : O) (e : ℕ), 0 < e → IsHausdorff (Ideal.span {x}) O → ∀ ψ ψ' : R →+* O, (∀ y, x ^ e ∣ ψ y - ψ' y) → ψ = ψ' := by
  first | exact @GlobalTheory.ringHom_eq_of_perfect_of_dvd_sub | exact GlobalTheory.ringHom_eq_of_perfect_of_dvd_sub | (intros; apply GlobalTheory.ringHom_eq_of_perfect_of_dvd_sub <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial Module

namespace GlobalTheory.IntClosureSep

theorem isRoot_minpoly_of_isRoot_charpoly {E A L : Type} [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] [Field L] [Algebra E L] (g : A) {α : L}
    (hα : ((LinearMap.mulLeft E g).charpoly.map (algebraMap E L)).IsRoot α) :
    ((minpoly E g).map (algebraMap E L)).IsRoot α := by
  classical
  let b := Module.finBasis E A
  set M := Algebra.leftMulMatrix b g with hM
  have hQ : (LinearMap.mulLeft E g).charpoly = M.charpoly := by
    rw [← LinearMap.charpoly_toMatrix (LinearMap.mulLeft E g) b]; rfl
  set M' := M.map (algebraMap E L) with hM'
  have h1 : Module.End.HasEigenvalue (Matrix.toLin' M') α := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', Matrix.charpoly_map,
      ← hQ]
    exact hα
  obtain ⟨v, hv⟩ := h1.exists_hasEigenvector
  have h2 : aeval M (minpoly E g) = 0 := by
    rw [hM, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have h3 : aeval M' ((minpoly E g).map (algebraMap E L)) = 0 := by
    rw [aeval_map_algebraMap]
    have : M' = (Algebra.ofId E L).mapMatrix M := rfl
    rw [this, Polynomial.aeval_algHom_apply, h2, map_zero]
  have h4 := Module.End.aeval_apply_of_hasEigenvector (p := (minpoly E g).map (algebraMap E L)) hv
  have h5 : aeval (Matrix.toLin' M') ((minpoly E g).map (algebraMap E L)) = 0 := by
    have : Matrix.toLin' M' = Matrix.toLinAlgEquiv' M' := rfl
    rw [this, Polynomial.aeval_algEquiv, AlgHom.comp_apply, h3, map_zero]
  rw [h5, LinearMap.zero_apply] at h4
  exact (smul_eq_zero.mp h4.symm).resolve_right hv.2

theorem integralClosure_fg_of_separable_charpoly : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → (Subalgebra.toSubmodule (integralClosure O A)).FG := by
  intro O E A _ _ _ _ _ _ _ _ _ _ _ g hsep
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · rw [Subsingleton.elim (Subalgebra.toSubmodule (integralClosure O A)) ⊥]
    exact Submodule.fg_bot
  let L := AlgebraicClosure E
  set Q := (LinearMap.mulLeft E g).charpoly with hQ
  set n := finrank E A with hn
  have hQdeg : Q.natDegree = n := LinearMap.charpoly_natDegree _
  set R := (Q.map (algebraMap E L)).roots with hR
  have hRnodup : R.Nodup := nodup_roots (hsep.map)
  have hRcard : Multiset.card R = n := by
    rw [hR, IsAlgClosed.card_roots_eq_natDegree, natDegree_map, hQdeg]
  set m := minpoly E g with hm
  have hsub : ∀ α ∈ R, aeval α m = 0 := fun α hα => by
    have := isRoot_minpoly_of_isRoot_charpoly g (isRoot_of_mem_roots hα)
    rwa [IsRoot, eval_map_algebraMap] at this
  have hm_ne : m ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral g)
  have hdeg_ge : n ≤ m.natDegree := by
    have hle : R ≤ (m.map (algebraMap E L)).roots := (Multiset.le_iff_subset hRnodup).mpr
      fun α hα => by
        rw [mem_roots (Polynomial.map_ne_zero hm_ne), IsRoot, eval_map_algebraMap]
        exact hsub α hα
    calc n = Multiset.card R := hRcard.symm
      _ ≤ _ := Multiset.card_le_card hle
      _ ≤ (m.map (algebraMap E L)).natDegree := card_roots' _
      _ = m.natDegree := natDegree_map _
  have hdeg_le : m.natDegree ≤ n := by
    simpa using (linearIndependent_pow (K := E) g).fintype_card_le_finrank
  have hdeg : m.natDegree = n := le_antisymm hdeg_le hdeg_ge
  haveI : Nonempty (Fin m.natDegree) := ⟨⟨0, by rw [hdeg, hn]; exact Module.finrank_pos⟩⟩
  let pb : PowerBasis E A :=
    { gen := g, dim := m.natDegree
      basis := basisOfLinearIndependentOfCardEqFinrank (linearIndependent_pow g) (by simp [hdeg, m, n])
      basis_eq_pow := fun i => by rw [coe_basisOfLinearIndependentOfCardEqFinrank] }
  let ι : Type := ↥R.toFinset
  have hcard : Fintype.card ι = n := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup hRnodup, hRcard]
  let P : ι → (A →ₐ[E] L) := fun α => pb.lift α.1 (hsub α.1 (Multiset.mem_toFinset.mp α.2))
  have hP : Function.Injective P := fun a b h => Subtype.ext (by
    have h' : (P a) pb.gen = (P b) pb.gen := congrArg (fun f : A →ₐ[E] L => f pb.gen) h
    simpa only [P, PowerBasis.lift_gen] using h')
  let b0 : Basis ι E A := (Module.finBasisOfFinrankEq E A hcard.symm).reindex (Fintype.equivFin ι).symm
  have hex : ∀ i, ∃ c : nonZeroDivisors O, IsIntegral O ((c : O) • b0 i) := fun i =>
    IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors O) (b0 i)
      (Algebra.IsIntegral.isIntegral (R := E) (b0 i))
  choose c hc using hex
  let e : Basis ι E A := b0.isUnitSMul (w := fun i => algebraMap O E (c i))
    (fun i => (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (c i).2).isUnit)
  have he : ∀ i, e i = (c i : O) • b0 i := fun i => by
    simp [e, Basis.isUnitSMul_apply, algebraMap_smul]
  have he_int : ∀ i, IsIntegral O (e i) := fun i => (he i) ▸ hc i
  have hdisc : Algebra.discr E e ≠ 0 := fun h =>
    GlobalTheory.algebraMap_discr_basis_ne_zero e hP (by rw [h, map_zero])
  have hnd : (Algebra.traceForm E A).Nondegenerate := by
    have hT : LinearMap.BilinForm.toMatrix e (Algebra.traceForm E A) = Algebra.traceMatrix E e := by
      ext i j
      rw [Algebra.traceForm_toMatrix, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero e, hT]
    exact hdisc
  have htr : ∀ x : A, IsIntegral O x → ∃ r : O, algebraMap O E r = Algebra.trace E A x := by
    intro x hx
    have h1 : IsIntegral O (algebraMap E L (Algebra.trace E A x)) := by
      rw [GlobalTheory.algebraMap_trace_eq_sum_algHom_of_card hcard hP x]
      refine IsIntegral.sum _ fun j _ => ?_
      exact hx.map ((P j).restrictScalars O)
    have h2 : IsIntegral O (Algebra.trace E A x) :=
      (isIntegral_algHom_iff ((Algebra.ofId E L).restrictScalars O)
        (algebraMap E L).injective).mp h1
    exact IsIntegrallyClosed.isIntegral_iff.mp h2
  set d := (Algebra.traceForm E A).dualBasis hnd e
  have hle : Subalgebra.toSubmodule (integralClosure O A) ≤ Submodule.span O (Set.range d) := by
    intro x hx
    have hx' : IsIntegral O x := hx
    rw [← d.sum_repr x]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
    obtain ⟨r, hr⟩ := htr _ (hx'.mul (he_int i))
    rw [← hr, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact Submodule.FG.of_le (Submodule.fg_span (Set.finite_range d)) hle

end GlobalTheory.IntClosureSep
end

section

open Polynomial

theorem _root_.GlobalTheory.T.charpoly_mulLeft_separable_of_adjoin_eq_of_reduced : ∀ (E A : Type) [Field E] [CharZero E] [CommRing A] [Algebra E A] [Module.Finite E A] (y : A), Algebra.adjoin E ({y} : Set A) = ⊤ → IsReduced A → (LinearMap.mulLeft E y).charpoly.Separable := by
  first | exact @GlobalTheory.charpoly_mulLeft_separable_of_adjoin_eq_top | exact GlobalTheory.charpoly_mulLeft_separable_of_adjoin_eq_top | (intros; apply GlobalTheory.charpoly_mulLeft_separable_of_adjoin_eq_top <;> assumption)
end

section


theorem _root_.GlobalTheory.T.finite_image_of_trivial_on_inf_finiteIndex : ∀ (G Q : Type) [Group G] [Group Q] (ρ : G →* Q) (J H : Subgroup G), H.FiniteIndex → (∀ g ∈ J, g ∈ H → ρ g = 1) → (ρ '' (J : Set G)).Finite := by
  first | exact @GlobalTheory.image_finite_of_trivial_on_inf_finiteIndex | exact GlobalTheory.image_finite_of_trivial_on_inf_finiteIndex | (intros; apply GlobalTheory.image_finite_of_trivial_on_inf_finiteIndex <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.charpoly_mulLeft_eq_map_of_span_range_eq : ∀ (R F A S : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field F] [Algebra R F] [IsFractionRing R F] [CommRing A] [Algebra F A] [Algebra R A] [IsScalarTower R F A] [Module.Finite F A] [CommRing S] [Algebra R S] [Module.Finite R S] (ι : S →ₐ[R] A), Function.Injective ι → Submodule.span F (Set.range ι) = ⊤ → ∃ (n : ℕ) (b : Module.Basis (Fin n) R S), ∀ x : S, (LinearMap.mulLeft F (ι x)).charpoly = ((LinearMap.toMatrix b b (LinearMap.mulLeft R x)).charpoly).map (algebraMap R F) := by
  first | exact @GlobalTheory.charpoly_mulLeft_eq_map_of_spanning_lattice | exact GlobalTheory.charpoly_mulLeft_eq_map_of_spanning_lattice | (intros; apply GlobalTheory.charpoly_mulLeft_eq_map_of_spanning_lattice <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.exists_not_X_pow_dvd_adjugate_of_first_order_kernel : ∀ (K : Type) [Field K] (a m : ℕ) (Ψ : Matrix (Fin a) (Fin a) (Polynomial K)), (∀ x0 x1 : Fin (1 + 1) → Fin a → K, (∀ j, (Ψ.map fun p => p.coeff 0).mulVec (x0 j) = 0 ∧ (Ψ.map fun p => p.coeff 1).mulVec (x0 j) + (Ψ.map fun p => p.coeff 0).mulVec (x1 j) = 0) → ¬ LinearIndependent K x0) → Module.finrank K (LinearMap.ker (Ψ.map fun p => p.coeff 0).mulVecLin) ≤ m + 1 → a ≠ 0 → ∃ b c, ¬ (Polynomial.X : Polynomial K) ^ (2 * m + 1) ∣ Ψ.adjugate b c := by
  first | exact @GlobalTheory.exists_not_X_pow_dvd_adjugate_of_firstOrderKernel | exact GlobalTheory.exists_not_X_pow_dvd_adjugate_of_firstOrderKernel | (intros; apply GlobalTheory.exists_not_X_pow_dvd_adjugate_of_firstOrderKernel <;> assumption)
end
