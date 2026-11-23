module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle005
public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.DividedPowers.DPMorphism
public import Mathlib.RingTheory.Flat.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle404
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle436
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle013
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle437
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle140
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.IsPrecompleteOfBasis
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
public import Mathlib.RingTheory.Nilpotent.Basic
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle005

@[expose] public section

section

open IsLocalRing Polynomial

namespace GlobalTheory.MonicRootExtension

section
variable {A : Type} [CommRing A] [IsLocalRing A] (M : A[X]) (hM : M.Monic)
  (hirr : Irreducible (M.map (residue A)))

include hM hirr

theorem map_maximalIdeal_isMaximal :
    ((maximalIdeal A).map (algebraMap A (AdjoinRoot M))).IsMaximal := by
  haveI : Fact (Irreducible (M.map (residue A))) := ⟨hirr⟩
  have hR : IsField (AdjoinRoot (M.map (residue A))) := Field.toIsField _
  rw [AdjoinRoot.algebraMap_eq]
  exact Ideal.Quotient.maximal_of_isField _
    (MulEquiv.isField hR (AdjoinRoot.quotEquivQuotMap M (maximalIdeal A)).toRingEquiv.toMulEquiv)

theorem isLocalRing : IsLocalRing (AdjoinRoot M) := by
  have : Module.Finite A (AdjoinRoot M) := .of_basis (AdjoinRoot.powerBasis' hM).basis
  refine IsLocalRing.of_unique_max_ideal ⟨_, map_maximalIdeal_isMaximal M hM hirr, fun P hP => ?_⟩
  have hc : (P.comap (algebraMap A (AdjoinRoot M))).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
  have h1 : P.comap (algebraMap A (AdjoinRoot M)) = maximalIdeal A := IsLocalRing.eq_maximalIdeal hc
  have hle : (maximalIdeal A).map (algebraMap A (AdjoinRoot M)) ≤ P :=
    Ideal.map_le_iff_le_comap.2 h1.ge
  exact ((map_maximalIdeal_isMaximal M hM hirr).eq_of_le hP.ne_top hle).symm

theorem maximalIdeal_eq [IsLocalRing (AdjoinRoot M)] :
    (maximalIdeal A).map (algebraMap A (AdjoinRoot M)) = maximalIdeal (AdjoinRoot M) :=
  IsLocalRing.eq_maximalIdeal (map_maximalIdeal_isMaximal M hM hirr)

theorem isLocalHom [IsLocalRing (AdjoinRoot M)] : IsLocalHom (algebraMap A (AdjoinRoot M)) := by
  constructor
  intro x hx
  by_contra h
  have h2 : algebraMap A (AdjoinRoot M) x ∈ maximalIdeal (AdjoinRoot M) := by
    rw [← maximalIdeal_eq M hM hirr]; exact Ideal.mem_map_of_mem _ h
  exact h2 hx

end

section
variable {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  (M : A[X]) (hM : M.Monic) (hirr : Irreducible (M.map (residue A)))
include hM hirr

theorem isAdicComplete [IsLocalRing (AdjoinRoot M)] [IsAdicComplete (maximalIdeal A) A] :
    IsAdicComplete (maximalIdeal (AdjoinRoot M)) (AdjoinRoot M) := by
  have : Module.Finite A (AdjoinRoot M) := .of_basis (AdjoinRoot.powerBasis' hM).basis
  rw [← maximalIdeal_eq M hM hirr, IsAdicComplete.map_algebraMap_iff]
  haveI : IsPrecomplete (maximalIdeal A) (AdjoinRoot M) :=
    ReciprocityTheory.ChartRestriction.G.Semi.Nb.isPrecomplete_of_basis _ (AdjoinRoot.powerBasis' hM).basis
  exact { toIsHausdorff := inferInstance, toIsPrecomplete := inferInstance }

end

theorem exists_extension : ∀ (A Ω : Type) [CommRing A] [IsRegularLocalRing A] [Field Ω]
    (u : A →+* Ω) (p : Polynomial A) (α : Ω),
    RingHom.ker u = maximalIdeal A → IsAdicComplete (maximalIdeal A) A → p.Monic →
    (p.map u).eval α = 0 → (p.map u).derivative.eval α ≠ 0 →
    ∃ (E : Type) (_ : CommRing E) (_ : IsRegularLocalRing E) (a : A →+* E) (v : E →+* Ω),
      a.Flat ∧ (maximalIdeal A).map a = maximalIdeal E ∧ IsAdicComplete (maximalIdeal E) E ∧
      RingHom.ker v = maximalIdeal E ∧ v.comp a = u ∧ α ∈ v.range := by
  intro A Ω _ _ _ u p α hker hcpl hp hroot _

  let ub : ResidueField A →+* Ω := Ideal.Quotient.lift (maximalIdeal A) u
    (fun x hx => (RingHom.mem_ker).1 (hker ▸ hx))
  have hub : ∀ x, ub (residue A x) = u x := fun x => rfl
  letI : Algebra (ResidueField A) Ω := ub.toAlgebra
  have hpu : p.map u = (p.map (residue A)).map ub := by
    rw [Polynomial.map_map]; congr 1
  have hint : IsIntegral (ResidueField A) α := by
    refine ⟨p.map (residue A), hp.map _, ?_⟩
    rw [← Polynomial.eval_map]; change eval α ((p.map (residue A)).map ub) = 0
    rw [← hpu]; exact hroot
  set m := minpoly (ResidueField A) α
  obtain ⟨q, hq⟩ := Polynomial.map_surjective _ (residue_surjective (R := A)) m
  obtain ⟨M, hMm, -, hM⟩ := lifts_and_natDegree_eq_and_monic ((mem_lifts _).2 ⟨q, hq⟩)
    (minpoly.monic hint)
  have hirr : Irreducible (M.map (residue A)) := hMm ▸ minpoly.irreducible hint
  haveI := isLocalRing M hM hirr
  haveI : Module.Finite A (AdjoinRoot M) := .of_basis (AdjoinRoot.powerBasis' hM).basis
  haveI : Module.Free A (AdjoinRoot M) := .of_basis (AdjoinRoot.powerBasis' hM).basis
  haveI : IsNoetherianRing (AdjoinRoot M) := isNoetherian_of_tower A inferInstance
  haveI := isLocalHom M hM hirr
  haveI : IsRegularLocalRing (AdjoinRoot M) :=
    GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.of_flat_of_map_maximalIdeal (maximalIdeal_eq M hM hirr)
  have hev : M.eval₂ u α = 0 := by
    have h1 : M.eval₂ u α = (M.map (residue A)).eval₂ ub α := by
      rw [Polynomial.eval₂_map]; rfl
    rw [h1, hMm]; exact minpoly.aeval (ResidueField A) α
  let v : AdjoinRoot M →+* Ω := AdjoinRoot.lift u α hev
  have hva : v.comp (algebraMap A (AdjoinRoot M)) = u := by
    ext x; simp [v, AdjoinRoot.algebraMap_eq]
  refine ⟨AdjoinRoot M, inferInstance, inferInstance, algebraMap A (AdjoinRoot M), v, ?_,
    maximalIdeal_eq M hM hirr, isAdicComplete M hM hirr, ?_, hva, ⟨AdjoinRoot.root M, by simp [v]⟩⟩
  · rw [RingHom.flat_algebraMap_iff]; infer_instance
  · apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top v)
    · rw [← maximalIdeal_eq M hM hirr, Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hva, ← RingHom.mem_ker, hker]
      exact hx

end GlobalTheory.MonicRootExtension
end

section

open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra

theorem _root_.GlobalTheory.T.comap_map_eq_self_of_injective_finiteHopf : ∀ (k A B : Type) [Field k] [CommRing A] [CommRing B] [HopfAlgebra k A] [HopfAlgebra k B] [Module.Finite k A] (f : B →ₐc[k] A), Function.Injective f → ∀ J : Ideal B, Ideal.comap (f : B →ₐ[k] A) (Ideal.map (f : B →ₐ[k] A) J) = J := by
  first | exact @GlobalTheory.PDiv.comap_map_eq_self_of_hopf_injective | exact GlobalTheory.PDiv.comap_map_eq_self_of_hopf_injective | (intros; apply GlobalTheory.PDiv.comap_map_eq_self_of_hopf_injective <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.DPFlat

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {I : Ideal R} (κ : DividedPowers I)

def expS (z : R) (y : A) : PowerSeries A :=
  PowerSeries.mk fun n ↦ y ^ n * algebraMap R A (κ.dpow n z)

theorem expS_add_right {z : R} (hz : z ∈ I) (y y' : A) :
    expS κ z (y + y') = expS κ z y * expS κ z y' := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_mul]
  have h : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n, y ^ p.1 * algebraMap R A (κ.dpow p.1 z) *
      (y' ^ p.2 * algebraMap R A (κ.dpow p.2 z)) =
      y ^ p.1 * y' ^ p.2 * (n.choose p.1 : A) * algebraMap R A (κ.dpow n z) := by
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have h := κ.mul_dpow (m := p.1) (n := p.2) hz
    rw [hp] at h
    calc _ = y ^ p.1 * y' ^ p.2 * algebraMap R A (κ.dpow p.1 z * κ.dpow p.2 z) := by
            rw [map_mul]; ring
      _ = _ := by rw [h, map_mul, map_natCast]; ring
  rw [Finset.sum_congr rfl h, ← Finset.sum_mul, add_pow, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

theorem expS_add_left {z z' : R} (hz : z ∈ I) (hz' : z' ∈ I) (y : A) :
    expS κ (z + z') y = expS κ z y * expS κ z' y := by
  ext n

  simp only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_mul, κ.dpow_add hz hz', map_sum, map_mul,
  Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, pow_add]; ring

theorem expS_smul {z : R} (hz : z ∈ I) (a : R) (y : A) :
    expS κ z (algebraMap R A a * y) = expS κ (a * z) y := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, κ.dpow_mul hz, map_mul, map_pow]
  ring

theorem expS_zero_left (y : A) : expS κ 0 y = 1 := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [κ.dpow_zero I.zero_mem]
  · simp [κ.dpow_eval_zero hn, hn]

theorem expS_zero_right (z : R) (hz : z ∈ I) : expS κ z (0 : A) = 1 := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [κ.dpow_zero hz]
  · simp [hn]

theorem expS_sum_right {z : R} (hz : z ∈ I) {K : Type} (s : Finset K) (f : K → A) :
    expS κ z (∑ k ∈ s, f k) = ∏ k ∈ s, expS κ z (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expS_zero_right κ z hz]
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.prod_insert hk, expS_add_right κ hz, ih]

theorem expS_sum_left {K : Type} (s : Finset K) (f : K → R) (hf : ∀ k ∈ s, f k ∈ I) (y : A) :
    expS κ (∑ k ∈ s, f k) y = ∏ k ∈ s, expS κ (f k) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expS_zero_left κ y]
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.prod_insert hk,
      expS_add_left κ (hf k (Finset.mem_insert_self k s))
        (Ideal.sum_mem _ fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)),
      ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)]

theorem prod_expS_eq_one [Module.Flat R A] (c : I →₀ A)
    (hc : (c.sum fun i a ↦ a * algebraMap R A i) = 0) :
    (c.prod fun i a ↦ PowerSeries.mk fun n ↦ a ^ n * algebraMap R A (κ.dpow n i)) = 1 := by
  have h : ∑ i : ↥c.support, ((i : I) : R) • (c (i : I) : A) = (0 : A) := by
    rw [Finset.sum_coe_sort c.support (fun i : I ↦ ((i : R)) • (c i : A)), ← hc, Finsupp.sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.smul_def, mul_comm]
  obtain ⟨k, a, y, hx, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := A) h
  simp only at hx ha
  change (∏ i ∈ c.support, expS κ (i : R) (c i)) = 1
  rw [← Finset.prod_coe_sort]
  calc ∏ i : c.support, expS κ ((i.1 : I) : R) (c i.1)
      = ∏ i : c.support, ∏ j, expS κ (a i j * ((i.1 : I) : R)) (y j) := by
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        rw [hx i, expS_sum_right κ (i.1 : I).2]
        refine Finset.prod_congr rfl fun j _ ↦ ?_
        rw [Algebra.smul_def, expS_smul κ (i.1 : I).2]
    _ = ∏ j, ∏ i : c.support, expS κ (a i j * ((i.1 : I) : R)) (y j) := Finset.prod_comm
    _ = ∏ j, expS κ (∑ i : c.support, a i j * ((i.1 : I) : R)) (y j) := by
        refine Finset.prod_congr rfl fun j _ ↦ ?_
        rw [expS_sum_left κ _ _ fun i _ ↦ I.mul_mem_left _ (i.1 : I).2]
    _ = 1 := by
        refine Finset.prod_eq_one fun j _ ↦ ?_
        have : ∑ i : c.support, a i j * ((i.1 : I) : R) = 0 := by
          rw [← ha j]; exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
        rw [this, expS_zero_left]

theorem exists_isDPMorphism_of_flat : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] (I : Ideal R) (κ : DividedPowers I),
    ∃ δ : DividedPowers (I.map (algebraMap R A)), IsDPMorphism κ δ (algebraMap R A) := by
  intro R A _ _ _ _ I κ
  let x : I → A := fun i ↦ algebraMap R A i
  have hspan : Ideal.span (Set.range x) = I.map (algebraMap R A) := by
    rw [Ideal.map]; congr 1; ext b; simp [x]
  obtain ⟨γ, hγ, hγx⟩ := GlobalTheory.T.exists_isPreDividedPowers_of_generators A I x (fun i n ↦ algebraMap R A (κ.dpow n i))
    (fun i ↦ by simp [κ.dpow_zero i.2]) (fun i ↦ by simp [x, κ.dpow_one i.2])
    (fun i n hn ↦ Ideal.subset_span ⟨⟨κ.dpow n i, κ.dpow_mem hn i.2⟩, rfl⟩)
    (fun i m n ↦ by rw [← map_mul, κ.mul_dpow i.2, map_mul, map_natCast])
    (prod_expS_eq_one κ)
  rw [hspan] at hγ
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.exists_dividedPowers_of_comp_on_generators A _ γ (Set.range x) hγ hspan.symm (by
    rintro _ ⟨i, rfl⟩ m n hn
    rw [hγx, show algebraMap R A (κ.dpow n i) = x ⟨κ.dpow n i, κ.dpow_mem hn i.2⟩ from rfl, hγx]
    simp only [κ.dpow_comp hn i.2, map_mul, map_natCast]
    rw [← hγx])
  exact ⟨δ, ⟨le_rfl, fun a ha ↦ by rw [hδ]; exact hγx ⟨a, ha⟩ _⟩⟩

end GlobalTheory.DPFlat
end
end

section

open IsLocalRing

namespace GlobalTheory

set_option synthInstance.maxHeartbeats 400000 in
theorem ann_of_directed_essEtale : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (Q : Ideal B) [Q.IsPrime] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] (C : ι → Subalgebra R B), Monotone C → (∀ b : B, ∃ i, b ∈ C i) → (∀ i, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime (Q.comap ((C i).val : C i →ₐ[R] B))))) → ∀ i, ∀ c ∈ C i, ∀ t : B, t ∉ Q → t * c = 0 → ∃ s ∈ C i, s ∉ Q ∧ s * c = 0 := by
  intro R B _ _ _ Q _ ι _ _ C hmono hcov hess i c hc t ht htc
  obtain ⟨j, hj⟩ := hcov t
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  have hck : c ∈ C k := hmono hik hc
  have htk : t ∈ C k := hmono hjk hj
  set Qi := Q.comap ((C i).val : C i →ₐ[R] B) with hQi
  set Qk := Q.comap ((C k).val : C k →ₐ[R] B) with hQk
  let f : C i →+* C k := (Subalgebra.inclusion (hmono hik)).toRingHom
  have hf : Qi = Qk.comap f := by ext x; rfl
  let g : Localization.AtPrime Qi →+* Localization.AtPrime Qk := Localization.localRingHom Qi Qk f hf
  letI : Algebra (Localization.AtPrime Qi) (Localization.AtPrime Qk) := g.toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime Qi) (Localization.AtPrime Qk) := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    change algebraMap R (Localization.AtPrime Qk) r = g (algebraMap R (Localization.AtPrime Qi) r)
    rw [IsScalarTower.algebraMap_apply R (C i) (Localization.AtPrime Qi), IsScalarTower.algebraMap_apply R (C k) (Localization.AtPrime Qk)]
    simp only [g, Localization.localRingHom_to_map]
    congr 1
  haveI : Module.Flat (Localization.AtPrime Qi) (Localization.AtPrime Qk) :=
    GlobalTheory.T.flat_of_essentiallyEtale_local_algebras R _ _ (hess i) (hess k)
  haveI : IsLocalHom (algebraMap (Localization.AtPrime Qi) (Localization.AtPrime Qk)) :=
    (inferInstance : IsLocalHom g)
  haveI : Module.FaithfullyFlat (Localization.AtPrime Qi) (Localization.AtPrime Qk) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj := RingHom.FaithfullyFlat.injective (RingHom.faithfullyFlat_algebraMap_iff.mpr this)
  have h0 : algebraMap (C k) (Localization.AtPrime Qk) ⟨c, hck⟩ = 0 := by
    rw [IsLocalization.map_eq_zero_iff Qk.primeCompl]
    refine ⟨⟨⟨t, htk⟩, ht⟩, ?_⟩
    exact Subtype.ext htc
  have h1 : algebraMap (C i) (Localization.AtPrime Qi) ⟨c, hc⟩ = 0 := by
    apply hinj
    rw [map_zero]
    change g _ = 0
    simp only [g, Localization.localRingHom_to_map]
    exact h0
  rw [IsLocalization.map_eq_zero_iff Qi.primeCompl] at h1
  obtain ⟨⟨⟨s, hs⟩, hsQ⟩, hsc⟩ := h1
  exact ⟨s, hs, hsQ, congrArg Subtype.val hsc⟩

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.exists_conductor_ne_zero_finiteType_charZero : ∀ (K R B : Type) [Field K] [CharZero K] [CommRing R] [IsDomain R] [Algebra K R] [Algebra.FiniteType K R] [CommRing B] [IsDomain B] [Algebra R B], Function.Injective (algebraMap R B) → ∃ c : R, c ≠ 0 ∧ ∀ x : B, IsIntegral R x → (∃ r s : R, r ≠ 0 ∧ algebraMap R B r * x = algebraMap R B s) → ∃ s : R, algebraMap R B c * x = algebraMap R B s := by
  first | exact @GlobalTheory.exists_ne_zero_mul_mem_of_isIntegral_of_fraction | exact GlobalTheory.exists_ne_zero_mul_mem_of_isIntegral_of_fraction | (intros; apply GlobalTheory.exists_ne_zero_mul_mem_of_isIntegral_of_fraction <;> assumption)
end

section

open IsLocalRing

namespace GlobalTheory


open IsLocalRing in
theorem _root_.GlobalTheory.injective_of_finite_of_ringKrullDim_eq_of_local_domain :
    ∀ (B R : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [CommRing R]
      [IsLocalRing R] (ψ : B →+* R), ψ.Finite → ringKrullDim R = ringKrullDim B →
      Function.Injective ψ := by
  intro B R _ _ _ _ _ _ ψ hψ hdim
  letI : Algebra B R := ψ.toAlgebra
  haveI : Module.Finite B R := hψ
  have hlt : ringKrullDim B < ⊤ := ringKrullDim_lt_top
  have hne : ringKrullDim B ≠ ⊥ := fun h =>
    (WithBot.bot_lt_coe (0 : ℕ∞)).not_ge (h ▸ (ringKrullDim_nonneg_of_nontrivial (R := B)))
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hne
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℕ∞) = m := by
    refine ENat.ne_top_iff_exists.mp ?_
    rintro rfl
    exact hlt.ne hm.symm
  exact _root_.GlobalTheory.CohenStructure.injective_of_ringKrullDim_eq (A := B) (S := R) hm.symm
    (hdim.trans hm.symm)

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.nonZeroDivisor_localization_general_of_noetherian : (∀ (A B : Type) [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (b g : B) (u : PrimeSpectrum B), g * b = 0 →
    (∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes, Q ≤ u.asIdeal → g ∉ Q) →
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0) →
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (b g : B) (u : PrimeSpectrum B), g * b = 0 →
    (∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes, Q ≤ u.asIdeal → g ∉ Q) →
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0 := by
  first | exact @GlobalTheory.NzdDescent.of_noetherian | exact GlobalTheory.NzdDescent.of_noetherian | (intros; apply GlobalTheory.NzdDescent.of_noetherian <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem mvPowerSeries_algHom_isNilpotent_of_constantCoeff_zero :
    ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A],
      ∀ φ : MvPowerSeries σ k →ₐ[k] A, (∀ i, IsNilpotent (φ (X i))) →
        ∀ a : MvPowerSeries σ k, constantCoeff a = 0 → IsNilpotent (φ a) := by
  intro k _ σ _ A _ _ φ hφ a ha
  classical
  haveI := Fintype.ofFinite σ
  have hc : ∀ α : σ →₀ ℕ, ∃ o : Option σ, (α = 0 ∧ o = none) ∨ ∃ i, o = some i ∧ α i ≠ 0 := by
    intro α
    by_cases h : α = 0
    · exact ⟨none, Or.inl ⟨h, rfl⟩⟩
    · obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 h
      exact ⟨some i, Or.inr ⟨i, rfl, by simpa using hi⟩⟩
  choose c hc using hc
  let g : σ → MvPowerSeries σ k := fun i α => if c α = some i then coeff α a else 0
  have hg : ∀ i α, coeff α (g i) = if c α = some i then coeff α a else 0 := fun _ _ => rfl
  have hsum : a = ∑ i, g i := by
    ext α

    rw [map_sum]
    simp only [hg]
    rcases hc α with ⟨h0, h1⟩ | ⟨i, h1, -⟩
    · rw [h1, h0]
      simpa using ha
    · rw [h1]
      simp

  rw [hsum, map_sum]
  refine isNilpotent_sum fun i _ => ?_
  have hd : (X i : MvPowerSeries σ k) ∣ g i := by
    rw [X_dvd_iff]
    intro m hm
    rw [hg, if_neg]
    intro h
    rcases hc m with ⟨-, h1⟩ | ⟨j, h1, h2⟩
    · rw [h1] at h; cases h
    · rw [h1] at h
      cases h
      exact h2 hm
  obtain ⟨b, hb⟩ := hd
  rw [hb, map_mul]
  exact (Commute.all _ _).isNilpotent_mul_right (hφ i)

end GlobalTheory
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.coeff_subst_leading_of_agree_degree_one : ∀ (R : Type) [CommRing R] (σ τ : Type) [Finite σ] (u v : σ → MvPowerSeries τ R) (N : ℕ) (f : MvPowerSeries σ R), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ i (γ : τ →₀ ℕ), γ.degree = 1 → coeff γ (u i) = coeff γ (v i)) → (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → ∀ γ : τ →₀ ℕ, (γ.degree < N → coeff γ (subst u f) = 0) ∧ (γ.degree ≤ N → coeff γ (subst u f) = coeff γ (subst v f)) := by
  first | exact @GlobalTheory.coeff_subst_leading | exact GlobalTheory.coeff_subst_leading | (intros; apply GlobalTheory.coeff_subst_leading <;> assumption)
end
