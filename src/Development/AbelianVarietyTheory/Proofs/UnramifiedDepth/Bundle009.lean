module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
public import ReciprocityTheory.DualLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DetFrobeniusSubPowSupport
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
public import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace GlobalTheory

open Polynomial IsLocalRing

theorem exists_finite_dvr_algHom_mem_range {B K : Type} [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [IsAdicComplete (maximalIdeal B) B] [Field K] [Algebra B K]
    [IsLocalHom (algebraMap B K)] [Module.Finite B K] (θ : K) :
    ∃ (B' : Type) (_ : CommRing B') (_ : IsDomain B') (_ : IsDiscreteValuationRing B')
      (_ : IsAdicComplete (maximalIdeal B') B') (_ : Algebra B B'), Module.Finite B B' ∧
      Function.Injective (algebraMap B B') ∧
      ∃ e : B' →ₐ[B] K, IsLocalHom (e : B' →+* K) ∧ θ ∈ Set.range e := by
  let k := ResidueField B
  letI : Algebra k K := (ResidueField.lift (algebraMap B K)).toAlgebra
  have : IsScalarTower B k K := .of_algebraMap_eq fun b =>
    (ResidueField.lift_residue_apply (algebraMap B K) b).symm
  have hθ : IsIntegral k θ := (Algebra.IsIntegral.isIntegral (R := B) θ).tower_top
  obtain ⟨μ, hμ, -, hμm⟩ := lifts_and_natDegree_eq_and_monic (f := algebraMap B k)
    (p := minpoly k θ) (map_surjective _ residue_surjective _) (minpoly.monic hθ)
  let B' := AdjoinRoot μ
  have hμθ : aeval θ μ = 0 := by
    rw [← aeval_map_algebraMap k]
    exact (congrArg (aeval θ) hμ).trans (minpoly.aeval k θ)
  let e : B' →ₐ[B] K := AdjoinRoot.liftAlgHom μ (Algebra.ofId B K) θ hμθ
  have he₀ : e (AdjoinRoot.root μ) = θ := AdjoinRoot.liftAlgHom_root ..
  have he : ∀ g : B[X], e (AdjoinRoot.mk μ g) = aeval θ g := fun g => by
    rw [← AdjoinRoot.aeval_eq, ← aeval_algHom_apply, he₀]
  have hu : ∀ y : B', e y ≠ 0 → IsUnit y := fun y hy => by
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective y
    exact isUnit_adjoinRoot_mk_of_aeval_ne_zero hθ hμm hμ (he g ▸ hy)
  have : Nontrivial B' := e.toRingHom.domain_nontrivial
  have : IsLocalRing B' := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun y => by
    by_cases hy : e y = 0
    · exact Or.inr (hu _ (by simp [hy]))
    · exact Or.inl (hu _ hy)
  have hm : ∀ y : B', y ∈ maximalIdeal B' ↔ e y = 0 := fun y =>
    ⟨fun hy => by_contra fun h => hy (hu y h), fun hy h => (h.map e).ne_zero hy⟩
  have hfin : Module.Finite B B' := hμm.finite_adjoinRoot
  have : Module.Free B B' := hμm.free_adjoinRoot
  have hmap : (maximalIdeal B).map (algebraMap B B') = maximalIdeal B' := by
    refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun b hb => ?_) fun y hy => ?_
    · rw [Ideal.mem_comap, hm, AlgHom.commutes, algebraMap_eq_zero_iff_mem_maximalIdeal (K := K)]
      exact hb
    · obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective y
      rw [hm, he, ← aeval_map_algebraMap k] at hy
      obtain ⟨c, hc⟩ := minpoly.dvd k θ hy
      obtain ⟨c, rfl⟩ := map_surjective (algebraMap B k) residue_surjective c
      have h₀ : (g - μ * c).map (algebraMap B k) = 0 := by
        rw [Polynomial.map_sub, Polynomial.map_mul, hμ, hc, sub_self]
      have h₁ : AdjoinRoot.mk μ (g - μ * c) ∈ (maximalIdeal B).map (algebraMap B B') := by

        rw [(g - μ * c).as_sum_support_C_mul_X_pow, map_sum]
        refine Ideal.sum_mem _ fun i _ => ?_
        rw [map_mul]
        refine Ideal.mul_mem_right _ _ ?_
        change algebraMap B B' _ ∈ _
        refine Ideal.mem_map_of_mem _ ?_
        rw [← residue_eq_zero_iff]
        change algebraMap B k _ = 0
        rw [← coeff_map, h₀, coeff_zero]
      rwa [map_sub, map_mul, AdjoinRoot.mk_self, zero_mul, sub_zero] at h₁
  have : IsNoetherianRing B' := IsNoetherianRing.of_finite B B'
  obtain ⟨_, _⟩ := exists_isDiscreteValuationRing_of_flat B B' hmap
    (Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal B').ne_top)
  have hc := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isAdicComplete_finite_algebra (R := B) B'
  rw [hmap] at hc
  exact ⟨B', inferInstance, inferInstance, inferInstance, hc, inferInstance, hfin,
    FaithfulSMul.algebraMap_injective B B', e, ⟨fun y hy => hu y hy.ne_zero⟩,
    AdjoinRoot.root μ, he₀⟩

theorem exists_finite_dvr_algHom_subset_range {B K : Type} [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [IsAdicComplete (maximalIdeal B) B] [Field K] [Algebra B K]
    [IsLocalHom (algebraMap B K)] [Module.Finite B K] (s : Finset K) :
    ∃ (B' : Type) (_ : CommRing B') (_ : IsDomain B') (_ : IsDiscreteValuationRing B')
      (_ : IsAdicComplete (maximalIdeal B') B') (_ : Algebra B B'), Module.Finite B B' ∧
      Function.Injective (algebraMap B B') ∧
      ∃ e : B' →ₐ[B] K, IsLocalHom (e : B' →+* K) ∧ (s : Set K) ⊆ Set.range e := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, fun _ _ h => h, Algebra.ofId B K, ‹IsLocalHom (algebraMap B K)›, by simp⟩
  | insert θ s _ ih =>
    obtain ⟨C, _, _, _, _, _, hfin, hinj, e, hloc, hs⟩ := ih
    letI : Algebra C K := (e : C →+* K).toAlgebra
    have : IsScalarTower B C K := .of_algebraMap_eq fun b => (e.commutes b).symm
    have : IsLocalHom (algebraMap C K) := hloc
    have : Module.Finite C K := .of_restrictScalars_finite B C K
    obtain ⟨D, _, _, _, _, _, hfin', hinj', e', hloc', hθ⟩ :=
      exists_finite_dvr_algHom_mem_range (B := C) θ
    letI : Algebra B D := ((algebraMap C D).comp (algebraMap B C)).toAlgebra
    have : IsScalarTower B C D := .of_algebraMap_eq fun _ => rfl
    refine ⟨D, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      Module.Finite.trans C D, hinj'.comp hinj, e'.restrictScalars B, hloc', ?_⟩
    rw [Finset.coe_insert]
    refine Set.insert_subset hθ fun x hx => ?_
    obtain ⟨c, rfl⟩ := hs hx
    exact ⟨algebraMap C D c, e'.commutes c⟩

theorem exists_finite_dvr_residueField_ringHom :
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W] (k' : Type) [Field k'] [Algebra (ResidueField W) k'] [FiniteDimensional (ResidueField W) k'], ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsDiscreteValuationRing W') (_ : IsAdicComplete (maximalIdeal W') W') (_ : Algebra W W'), Module.Finite W W' ∧ Function.Injective (algebraMap W W') ∧ ∃ e : k' →+* ResidueField W', ∀ v : W, e (algebraMap (ResidueField W) k' (residue W v)) = residue W' (algebraMap W W' v) := by
  intro W _ _ _ _ K _ _ _
  letI : Algebra W K := ((algebraMap (ResidueField W) K).comp (residue W)).toAlgebra
  have : IsScalarTower W (ResidueField W) K := .of_algebraMap_eq fun _ => rfl
  have : IsLocalHom (algebraMap W K) := ⟨fun b hb => by
    by_contra hn
    exact hb.ne_zero ((algebraMap_eq_zero_iff_mem_maximalIdeal (K := K) b).mpr hn)⟩
  have hfin : Module.Finite W K := Module.Finite.trans (ResidueField W) K
  obtain ⟨s, hs⟩ := hfin.fg_top
  obtain ⟨W', _, _, _, _, _, hfin', hinj, e, hloc, hsub⟩ :=
    exists_finite_dvr_algHom_subset_range (B := W) s
  have hsurj : Function.Surjective e := fun x => by
    have : x ∈ LinearMap.range e.toLinearMap := by
      have h : Submodule.span W (s : Set K) ≤ LinearMap.range e.toLinearMap :=
        Submodule.span_le.mpr hsub
      exact h (hs ▸ Submodule.mem_top)
    exact this
  let f : ResidueField W' →+* K := ResidueField.lift (e : W' →+* K)
  have hf : ∀ w, f (residue W' w) = e w := fun w => ResidueField.lift_residue_apply _ w
  have hbij : Function.Bijective f := ⟨f.injective, fun x => by
    obtain ⟨w, rfl⟩ := hsurj x
    exact ⟨_, hf w⟩⟩
  refine ⟨W', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hfin',
    hinj, (RingEquiv.ofBijective f hbij).symm, fun v => ?_⟩
  refine (RingEquiv.symm_apply_eq _).mpr ?_
  rw [RingEquiv.ofBijective_apply, hf, e.commutes]
  rfl

end GlobalTheory
end

section

open ReciprocityTheory.PGsh

noncomputable section

namespace GlobalTheory.DetPowPairing

open MvPolynomial

variable {σ : Type} {C : Type} [CommRing C]

def wt (C : Type) [CommRing C] (A : σ →₀ ℕ) : C := A.prod fun _ e => (e.factorial : C)

def pair : MvPolynomial σ C →ₗ[C] MvPolynomial σ C →ₗ[C] C :=
  (basisMonomials σ C).constr C fun A => wt C A • lcoeff C A

theorem pair_monomial (A : σ →₀ ℕ) (c : C) (Q : MvPolynomial σ C) :
    pair (monomial A c) Q = c * wt C A * AddMonoidAlgebra.coeff Q A := by
  have h : monomial A c = c • (basisMonomials σ C) A := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, pair, Module.Basis.constr_basis, LinearMap.smul_apply, LinearMap.smul_apply, lcoeff_apply,
    smul_eq_mul, smul_eq_mul, mul_assoc]

theorem pair_eq (P Q : MvPolynomial σ C) :
    pair P Q = ∑ A ∈ P.support, AddMonoidAlgebra.coeff P A * wt C A * AddMonoidAlgebra.coeff Q A := by
  conv_lhs => rw [P.as_sum]

  rw [map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun A _ => pair_monomial A (AddMonoidAlgebra.coeff P A) Q

theorem wt_add_single (A : σ →₀ ℕ) (j : σ) :
    wt C (A + Finsupp.single j 1) = wt C A * ((A j : C) + 1) := by
  classical
  set s := A.support ∪ {j} with hs
  have hA : wt C A = ∏ i ∈ s, ((A i).factorial : C) :=
    Finsupp.prod_of_support_subset A Finset.subset_union_left _ (fun _ _ => by simp)
  have hsupp : (A + Finsupp.single j 1).support ⊆ s := by
    intro i hi
    rw [Finsupp.mem_support_iff] at hi
    by_cases h : i = j
    · simp [s, h]
    · have hAi : A i ≠ 0 := by simpa [Finsupp.single_apply, Ne.symm h] using hi
      simp [s, Finsupp.mem_support_iff, hAi]
  have hB : wt C (A + Finsupp.single j 1) = ∏ i ∈ s, (((A + Finsupp.single j 1 : σ →₀ ℕ) i).factorial : C) :=
    Finsupp.prod_of_support_subset _ hsupp _ (fun _ _ => by simp)
  have hj : j ∈ s := by simp [s]
  have hrest : ∏ i ∈ s.erase j, (((A + Finsupp.single j 1 : σ →₀ ℕ) i).factorial : C) =
      ∏ i ∈ s.erase j, ((A i).factorial : C) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    simp [Ne.symm hij]
  rw [hA, hB, ← Finset.mul_prod_erase s _ hj, ← Finset.mul_prod_erase s _ hj, hrest]
  simp [Nat.factorial_succ]
  ring

theorem coeff_pderiv' (j : σ) (A : σ →₀ ℕ) (Q : MvPolynomial σ C) :
    AddMonoidAlgebra.coeff (pderiv j Q) A = AddMonoidAlgebra.coeff Q (A + Finsupp.single j 1) * ((A j : C) + 1) :=
  coeff_pderiv Q A

theorem pair_X_mul (j : σ) (P Q : MvPolynomial σ C) :
    pair (P * X j) Q = pair P (pderiv j Q) := by
  conv_lhs => rw [P.as_sum]

  rw [pair_eq P, Finset.sum_mul, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [show (X j : MvPolynomial σ C) = monomial (Finsupp.single j 1) 1 from rfl, monomial_mul, mul_one,
    pair_monomial, coeff_pderiv', wt_add_single]
  ring

theorem pair_list {ι : Type} (f : ι → σ) (l : List ι) (P Q : MvPolynomial σ C) :
    pair (P * (l.map fun j => X (f j)).prod) Q =
      pair P (((l.map fun j => ((pderiv (f j) : Derivation C _ _) :
        MvPolynomial σ C →ₗ[C] MvPolynomial σ C)).prod : Module.End C (MvPolynomial σ C)) Q) := by
  induction l generalizing P with
  | nil => simp
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ← mul_assoc, ih, pair_X_mul]
    rfl

theorem pair_det (n : ℕ) (P Q : MvPolynomial (Fin n × Fin n) C) :
    pair (P * cayDet n C) Q = pair P (cayOp n C Q) := by
  have hdet : cayDet n C = ∑ s : Equiv.Perm (Fin n),
      (Equiv.Perm.sign s : ℤ) • ((List.finRange n).map fun i => (X (s i, i) : MvPolynomial _ C)).prod := by
    rw [cayDet, Matrix.det_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Units.smul_def, Fin.prod_univ_def]
    rfl

  rw [hdet, cayOp, Finset.mul_sum, map_sum, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_smul_comm, map_zsmul, LinearMap.smul_apply, LinearMap.smul_apply, map_zsmul]
  exact congrArg (fun t => (Equiv.Perm.sign s : ℤ) • t) (pair_list (fun i => (s i, i)) (List.finRange n) P Q)

theorem pair_pow (n x : ℕ) :
    (∏ c ∈ Finset.range n, (c.factorial : C)) * pair (cayDet n C ^ x) (cayDet n C ^ x) =
      ∏ c ∈ Finset.range n, ((x + c).factorial : C) := by
  induction x with
  | zero =>
    have h1 : pair (1 : MvPolynomial (Fin n × Fin n) C) 1 = 1 := by
      rw [show (1 : MvPolynomial (Fin n × Fin n) C) = monomial 0 1 from rfl, pair_monomial]
      simp [wt]
    simp [h1]
  | succ x ih =>
    have hc := cayley n C (x + 1)
    rw [Nat.add_sub_cancel] at hc
    have hp : pair (cayDet n C ^ (x + 1)) (cayDet n C ^ (x + 1)) =
        pair (cayDet n C ^ x) (cayOp n C (cayDet n C ^ (x + 1))) := by
      rw [← pair_det, ← pow_succ]
    rw [hp, hc, map_nsmul, nsmul_eq_mul, Nat.cast_prod, mul_left_comm, ih,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [show x + 1 + c = (x + c) + 1 by ring, Nat.factorial_succ]
    push_cast
    ring

theorem main :
    (∀ (C : Type) [Field C] [CharZero C] (n₀ x : ℕ), (∏ c ∈ Finset.range n₀, (c.factorial : C)) * (∑ A ∈ (cayDet n₀ C ^ x).support, AddMonoidAlgebra.coeff (cayDet n₀ C ^ x) A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff (cayDet n₀ C ^ x) A) = ∏ c ∈ Finset.range n₀, ((x + c).factorial : C)) := by
  intro C _ _ n₀ x
  have h := pair_pow (C := C) n₀ x
  rw [pair_eq] at h
  exact h

end GlobalTheory.DetPowPairing
end
end

section

open ReciprocityTheory.PGsh

theorem _root_.GlobalTheory.T.det_frobenius_sub_pow_support_bounds : (∀ (l i E n₀ s : ℕ), l.Prime → 1 ≤ i → ∀ ψ : MvPolynomial ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) ℤ,
    ψ = (Matrix.of fun b c : Fin n₀ => (MvPolynomial.X (Sum.inl (b, c)) ^ (l ^ i) - MvPolynomial.C ((l : ℤ) ^ E) * MvPolynomial.X (Sum.inr (b, c)) : MvPolynomial ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) ℤ)).det -
      MvPolynomial.rename Sum.inl (cayDet n₀ ℤ) ^ (l ^ i) →
    ∀ m ∈ (ψ ^ s).support, (∑ q, m (Sum.inr q)) ≤ n₀ * s ∧ (∑ q, m (Sum.inl q)) + l ^ i * ∑ q, m (Sum.inr q) = n₀ * l ^ i * s ∧
      (l : ℤ) ^ (E * (∑ q, m (Sum.inr q)) + (s - ∑ q, m (Sum.inr q))) ∣ AddMonoidAlgebra.coeff (ψ ^ s) m) := by
  first | exact @GlobalTheory.det_frobenius_sub_pow_support | exact GlobalTheory.det_frobenius_sub_pow_support | (intros; apply GlobalTheory.det_frobenius_sub_pow_support <;> assumption)
end
