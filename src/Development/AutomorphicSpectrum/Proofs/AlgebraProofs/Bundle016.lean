module

public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.IsTensorProduct
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle012
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle004
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle005
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle005
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects

@[expose] public section

section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
private theorem norm_intCast_padicAlgCl_lt_one_iff_dvd (p : ℕ) [Fact p.Prime] (k : ℤ) :
    ‖(k : PadicAlgCl p)‖ < 1 ↔ (p : ℤ) ∣ k := by
  rw [← map_intCast (algebraMap ℚ_[p] (PadicAlgCl p)) k, PadicAlgCl.norm_extends]
  exact Padic.norm_intCast_lt_one_iff

private theorem norm_intCast_cp_lt_one_iff_dvd (p : ℕ) [Fact p.Prime] (k : ℤ) :
    ‖(k : ℂ_[p])‖ < 1 ↔ (p : ℤ) ∣ k := by
  rw [← map_intCast (algebraMap (PadicAlgCl p) ℂ_[p]) k, ← PadicComplex.coe_eq,
    PadicComplex.norm_extends]
  exact norm_intCast_padicAlgCl_lt_one_iff_dvd p k

private theorem not_dvd_den_of_norm_le_one_padicAlgCl (p : ℕ) [Fact p.Prime] (q : ℚ) (hq : ‖(q : PadicAlgCl p)‖ ≤ 1) :
    ¬ p ∣ q.den := by
  intro hd
  have hp : p.Prime := Fact.out
  have hnum : ¬ (p : ℤ) ∣ q.num := by
    intro hn
    have h1 : p ∣ q.num.natAbs := Int.natCast_dvd.mp hn
    have h2 : p ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd h1 hd
    rw [Nat.Coprime.gcd_eq_one q.reduced] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  have hnum1 : ‖(q.num : PadicAlgCl p)‖ = 1 :=
    le_antisymm (IsUltrametricDist.norm_intCast_le_one _ _)
      (not_lt.mp fun h => hnum ((norm_intCast_padicAlgCl_lt_one_iff_dvd p _).mp h))
  have hden : ‖(q.den : PadicAlgCl p)‖ < 1 := by
    rw [← Int.cast_natCast, norm_intCast_padicAlgCl_lt_one_iff_dvd]
    exact Int.natCast_dvd_natCast.mpr hd
  have hden0 : 0 < ‖(q.den : PadicAlgCl p)‖ := by
    rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends]
    exact norm_pos_iff.mpr (Nat.cast_ne_zero.mpr q.den_nz)
  rw [Rat.cast_def, norm_div, hnum1, div_le_iff₀ hden0, one_mul] at hq
  linarith

private theorem norm_multiset_prod_le_one_of_forall_norm_le_one {K : Type*} [NormedField K] (s : Multiset K) :
    (∀ y ∈ s, ‖y‖ ≤ 1) → ‖s.prod‖ ≤ 1 := by
  refine Multiset.induction_on s ?_ ?_
  · intro _
    simp
  · intro a s ih h
    rw [Multiset.prod_cons, norm_mul]
    exact mul_le_one₀ (h a (by simp)) (norm_nonneg _) (ih fun y hy => h y (by simp [hy]))

private theorem norm_multiset_sum_le_one_of_ultrametric {K : Type*} [NormedField K] [IsUltrametricDist K] (s : Multiset K) :
    (∀ y ∈ s, ‖y‖ ≤ 1) → ‖s.sum‖ ≤ 1 := by
  refine Multiset.induction_on s ?_ ?_
  · intro _
    simp
  · intro a s ih h
    rw [Multiset.sum_cons]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (h a (by simp)) (ih fun y hy => h y (by simp [hy])))

private theorem norm_esymm_le_one_of_forall_norm_le_one {K : Type*} [NormedField K] [IsUltrametricDist K] (s : Multiset K)
    (h : ∀ y ∈ s, ‖y‖ ≤ 1) (k : ℕ) : ‖s.esymm k‖ ≤ 1 := by
  rw [Multiset.esymm]
  apply norm_multiset_sum_le_one_of_ultrametric
  intro y hy
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hy
  apply norm_multiset_prod_le_one_of_forall_norm_le_one
  intro z hz
  exact h z (Multiset.mem_of_le (Multiset.mem_powersetCard.mp ht).1 hz)


theorem _root_.GlobalTheory.CompanionTheory.Relay.padic_integral_iff_denominator : ∀ (E : Type) [Field E] [NumberField E] (p : Nat.Primes) (x : E), ((∀ j : E →+* ℂ_[p], ‖j x‖ ≤ 1) ↔ ∃ (n : ℕ) (a : 𝓞 E), ¬ (p : ℕ) ∣ n ∧ (n : E) * x = a) := by
  intro E _ _ p x
  constructor
  · intro h
    have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    have hmon : (minpoly ℚ x).Monic := minpoly.monic hint
    have hroot : ∀ r ∈ ((minpoly ℚ x).map (algebraMap ℚ (PadicAlgCl (p : ℕ)))).roots,
        ‖r‖ ≤ 1 := by
      intro r hr
      have hr' : r ∈ (minpoly ℚ x).rootSet (PadicAlgCl (p : ℕ)) := by
        refine Polynomial.mem_rootSet.mpr ⟨minpoly.ne_zero hint, ?_⟩
        rw [Polynomial.aeval_def, ← Polynomial.eval_map]
        exact (Polynomial.mem_roots'.mp hr).2
      rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly (PadicAlgCl (p : ℕ)) x] at hr'
      obtain ⟨ψ, rfl⟩ := hr'
      have h1 := h ((algebraMap (PadicAlgCl (p : ℕ)) ℂ_[p]).comp (ψ : E →+* PadicAlgCl (p : ℕ)))
      rw [RingHom.comp_apply, ← PadicComplex.coe_eq, PadicComplex.norm_extends] at h1
      exact h1
    have hcard : ((minpoly ℚ x).map (algebraMap ℚ (PadicAlgCl (p : ℕ)))).roots.card =
        ((minpoly ℚ x).map (algebraMap ℚ (PadicAlgCl (p : ℕ)))).natDegree :=
      IsAlgClosed.card_roots_eq_natDegree
    have hmon' : ((minpoly ℚ x).map (algebraMap ℚ (PadicAlgCl (p : ℕ)))).Monic := hmon.map _
    have hcoeff : ∀ k, ‖(((minpoly ℚ x).coeff k : ℚ) : PadicAlgCl (p : ℕ))‖ ≤ 1 := by
      intro k
      have e1 : (((minpoly ℚ x).coeff k : ℚ) : PadicAlgCl (p : ℕ)) =
          ((minpoly ℚ x).map (algebraMap ℚ (PadicAlgCl (p : ℕ)))).coeff k := by
        rw [Polynomial.coeff_map]
        exact (eq_ratCast _ _).symm
      rw [e1]
      by_cases hk : k ≤ ((minpoly ℚ x).map (algebraMap ℚ (PadicAlgCl (p : ℕ)))).natDegree
      · rw [Polynomial.coeff_eq_esymm_roots_of_card hcard hk, hmon'.leadingCoeff, one_mul,
          norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        exact norm_esymm_le_one_of_forall_norm_le_one _ hroot _
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.mp hk), norm_zero]
        exact zero_le_one
    obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = ∏ k ∈ Finset.range ((minpoly ℚ x).natDegree + 1),
        ((minpoly ℚ x).coeff k).den := ⟨_, rfl⟩
    have hm : ¬ (p : ℕ) ∣ m := by
      rw [hmdef, Prime.dvd_finsetProd_iff p.2.prime]
      rintro ⟨k, -, hk⟩
      exact not_dvd_den_of_norm_le_one_padicAlgCl _ _ (hcoeff k) hk
    have hlift : Polynomial.C (m : ℚ) * minpoly ℚ x ∈ Polynomial.lifts (algebraMap ℤ ℚ) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro k
      rw [Polynomial.coeff_C_mul]
      by_cases hk : k ≤ (minpoly ℚ x).natDegree
      · have hd : ((minpoly ℚ x).coeff k).den ∣ m := by
          rw [hmdef]
          exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
        obtain ⟨t, ht⟩ := hd
        refine ⟨(t : ℤ) * ((minpoly ℚ x).coeff k).num, ?_⟩
        simp only [eq_intCast]
        rw [ht]
        push_cast
        rw [← Rat.den_mul_eq_num]
        ring
      · exact ⟨0, by rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.mp hk), mul_zero,
          map_zero]⟩
    obtain ⟨g, hg⟩ := (Polynomial.mem_lifts _).mp hlift
    have hlc : g.leadingCoeff = (m : ℤ) := by
      have h1 := Polynomial.leadingCoeff_map_of_injective (RingHom.injective_int (algebraMap ℤ ℚ)) g
      rw [hg, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hmon.leadingCoeff, mul_one,
        eq_intCast] at h1
      exact_mod_cast h1.symm
    have hg0 : Polynomial.aeval x g = 0 := by
      rw [← Polynomial.aeval_map_algebraMap ℚ x g, hg, map_mul, Polynomial.aeval_C, minpoly.aeval,
        mul_zero]
    have hI := isIntegral_leadingCoeff_smul g x hg0
    rw [hlc] at hI
    have hI' : IsIntegral ℤ ((m : E) * x) := by
      simpa [zsmul_eq_mul, nsmul_eq_mul] using hI
    exact ⟨m, ⟨(m : E) * x, hI'⟩, hm, rfl⟩
  · rintro ⟨n, a, hpn, hna⟩ j
    have hn : ‖((n : ℕ) : ℂ_[p])‖ = 1 := by
      have h1 := IsUltrametricDist.norm_natCast_le_one ℂ_[p] n
      have h2 : ¬ ‖((n : ℕ) : ℂ_[p])‖ < 1 := by
        rw [← Int.cast_natCast, norm_intCast_cp_lt_one_iff_dvd]
        exact fun h => hpn (Int.natCast_dvd_natCast.mp h)
      linarith [not_lt.mp h2]
    have ha : ‖j (a : E)‖ ≤ 1 := by
      have h1 := GlobalTheory.CompanionTheory.Ar.HT.LatBasic.val_le_one (NormedField.valuation (K := ℂ_[p])) j a
      rw [NormedField.valuation_apply] at h1
      exact_mod_cast h1
    have hj : j ((n : E) * x) = (n : ℂ_[p]) * j x := by
      rw [map_mul, map_natCast]
    rw [hna] at hj
    calc ‖j x‖ = ‖(n : ℂ_[p])‖ * ‖j x‖ := by rw [hn, one_mul]
      _ = ‖(n : ℂ_[p]) * j x‖ := (norm_mul _ _).symm
      _ = ‖j (a : E)‖ := by rw [hj]
      _ ≤ 1 := ha
end

section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.ideal_padic_generator_log_norm : ∀ (F : Type) [Field F] [NumberField F] (I : Ideal (𝓞 F)) (p : Nat.Primes), I ≠ ⊥ → ∃ δ ∈ I, δ ≠ 0 ∧ (∃ n : ℕ, ¬ (p : ℕ) ∣ n ∧ ∀ a ∈ I, (n : 𝓞 F) * a ∈ Ideal.span {δ}) ∧ ∀ j : F →+* ℂ_[p], Real.log ‖j (δ : F)‖ = logIdeal (j.comp (algebraMap (𝓞 F) F)) I := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.ideal_local_generator | exact GlobalTheory.CompanionTheory.Ar.Fl.ideal_local_generator | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.ideal_local_generator <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

theorem _root_.GlobalTheory.T.extension_order_eq_span : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (R' : Type) [CommRing R'] (φ : R →+* R') (A : Subalgebra R (T → R)) (g : T → R'), g ∈ extOrder φ A ↔ g ∈ Submodule.span R' {g : T → R' | ∃ f ∈ A, g = fun t => φ (f t)} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.ExtSpan.extOrder_eq_span | exact GlobalTheory.CompanionTheory.Ar.BT.ExtSpan.extOrder_eq_span | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.ExtSpan.extOrder_eq_span <;> assumption)
end

section

open NumberField TensorProduct GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.pro_isometry_of_local_isometries : ∀ (O : Type) [CommRing O] (L L' : Type) [AddCommGroup L] [Module O L] [AddCommGroup L'] [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L'), (∀ p : ℕ, p.Prime → Nonempty (ProIsoAt p O B B')) → Nonempty (ProIso O B B') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ProIso.nonempty_of_forall_prime | exact GlobalTheory.CompanionTheory.Ar.ProIso.nonempty_of_forall_prime | (intros; apply GlobalTheory.CompanionTheory.Ar.ProIso.nonempty_of_forall_prime <;> assumption)
end

section

open NumberField TensorProduct GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.padic_isometry_equivariance : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (L L' : Type) [AddCommGroup L] [Module O L] [AddCommGroup L'] [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L') [Module.Projective O L] [Module.Finite ℤ L] [Module.Free ℤ L] [Module.Finite ℤ L'] [Module.Free ℤ L'] (φ : (ℤ_[p] ⊗[ℤ] L) ≃ₗ[ℤ_[p]] (ℤ_[p] ⊗[ℤ] L')), (∀ (a : O) (x : L), φ (1 ⊗ₜ (a • x)) = LinearMap.baseChange ℤ_[p] (LinearMap.lsmul O L' a).toAddMonoidHom.toIntLinearMap (φ (1 ⊗ₜ x))) → (∀ u v, B'.baseChange ℤ_[p] (φ u) (φ v) = B.baseChange ℤ_[p] u v) → Nonempty (ProIsoAt p O B B') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.proIsoAt_of_padic_isometry | exact GlobalTheory.CompanionTheory.Ar.proIsoAt_of_padic_isometry | (intros; apply GlobalTheory.CompanionTheory.Ar.proIsoAt_of_padic_isometry <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Num TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Num.LocFreeKernel

theorem isBaseChange_of_split {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M₁ M M₂ E₁ E E₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M] [Module R M]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup E₁] [Module R E₁] [Module S E₁]
    [IsScalarTower R S E₁] [AddCommGroup E] [Module R E] [Module S E] [IsScalarTower R S E]
    [AddCommGroup E₂] [Module R E₂] [Module S E₂] [IsScalarTower R S E₂]
    (j : M₁ →ₗ[R] M) (p : M →ₗ[R] M₁) (π : M →ₗ[R] M₂) (s : M₂ →ₗ[R] M)
    (hpj : p ∘ₗ j = LinearMap.id) (hsum : j ∘ₗ p + s ∘ₗ π = LinearMap.id)
    (f₁ : M₁ →ₗ[R] E₁) (f : M →ₗ[R] E) (f₂ : M₂ →ₗ[R] E₂)
    (i : E₁ →ₗ[S] E) (q : E →ₗ[S] E₂) (hi : Function.Injective i) (hqi : ∀ x, q (i x) = 0)
    (h₁ : ∀ x, i (f₁ x) = f (j x)) (h₂ : ∀ x, q (f x) = f₂ (π x))
    (hf : IsBaseChange S f) (hf₂ : IsBaseChange S f₂) : IsBaseChange S f₁ := by
  let φ : S ⊗[R] M₁ →ₗ[S] E₁ := LinearMap.liftBaseChange S f₁
  have c₁ : ∀ t, i (φ t) = hf.equiv (j.baseChange S t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [φ, IsBaseChange.equiv_tmul, h₁]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have c₂ : ∀ t, q (hf.equiv t) = hf₂.equiv (π.baseChange S t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [IsBaseChange.equiv_tmul, h₂]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have c₃ : ∀ t, p.baseChange S (j.baseChange S t) = t := by
    intro t
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hpj, LinearMap.baseChange_id]
    rfl
  have c₄ : ∀ t, j.baseChange S (p.baseChange S t) + s.baseChange S (π.baseChange S t) = t := by
    intro t
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      ← LinearMap.baseChange_comp, ← LinearMap.add_apply, ← LinearMap.baseChange_add, hsum,
      LinearMap.baseChange_id]
    rfl
  have hinj : Function.Injective φ := by
    intro a b hab
    have : j.baseChange S a = j.baseChange S b := by
      apply hf.equiv.injective
      rw [← c₁, ← c₁, hab]
    rw [← c₃ a, this, c₃]
  have hsurj : Function.Surjective φ := by
    intro e
    obtain ⟨t, ht⟩ := hf.equiv.surjective (i e)
    have h0 : π.baseChange S t = 0 := by
      apply hf₂.equiv.injective
      rw [← c₂, ht, hqi, map_zero]
    refine ⟨p.baseChange S t, hi ?_⟩
    have := c₄ t
    rw [h0, map_zero, add_zero] at this
    rw [c₁, this, ht]
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩) (by
    intro x
    show φ (1 ⊗ₜ[R] x) = f₁ x
    rw [LinearMap.liftBaseChange_tmul, one_smul])

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E E₁ E₂ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω E₁] [AddCommGroup E₂] [Module Ω E₂] (i : E₁ →ₗ[Ω] E) (q : E →ₗ[Ω] E₂), Function.Injective i → Function.Surjective q → LinearMap.range i = LinearMap.ker q → ∀ (L : AddSubgroup E) (r₁ r₂ : ℕ), LocFree R (r₁ + r₂) L → LocFree R r₂ (L.map q.toAddMonoidHom) → LocFree R r₁ (L.comap i.toAddMonoidHom) := by
  intro o Ω _ _ _ R E E₁ E₂ _ _ _ _ _ _ i q hi hq hex L r₁ r₂ hL hL₂
  let M : Submodule R E :=
    { L with smul_mem' := fun a e he => hL.1 a a.2 e he }
  let M₁ : Submodule R E₁ := M.comap (i.restrictScalars R)
  let M₂ : Submodule R E₂ := M.map (q.restrictScalars R)
  obtain ⟨hfin, hproj, hrk, hbc⟩ := GlobalTheory.T.locally_free_finite_projective_base_change R (r₁ + r₂) M hL
  obtain ⟨hfin₂, hproj₂, hrk₂, hbc₂⟩ := GlobalTheory.T.locally_free_finite_projective_base_change R r₂ M₂ hL₂
  have hqi : ∀ x, q (i x) = 0 := fun x => by
    rw [← LinearMap.mem_ker, ← hex]; exact LinearMap.mem_range_self i x
  let j : M₁ →ₗ[R] M := (i.restrictScalars R).restrict (fun x hx => hx)
  let π : M →ₗ[R] M₂ := (q.restrictScalars R).restrict (fun x hx => ⟨x, hx, rfl⟩)
  have hπ : Function.Surjective π := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hj : Function.Injective j := by
    intro a b hab
    exact Subtype.ext (hi (congrArg Subtype.val hab))
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hmem : ∀ x : M, (LinearMap.id - s ∘ₗ π : M →ₗ[R] M) x ∈ LinearMap.range j := by
    intro x
    have h0 : π (x - s (π x)) = 0 := by
      have := LinearMap.congr_fun hs (π x)
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
      rw [map_sub, this, sub_self]
    have h1 : ((x - s (π x) : M) : E) ∈ LinearMap.range i := by
      rw [hex]; exact congrArg Subtype.val h0
    obtain ⟨y, hy⟩ := h1
    refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
    show i y ∈ M
    rw [hy]; exact (x - s (π x) : M).2
  let p : M →ₗ[R] M₁ := (LinearEquiv.ofInjective j hj).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict _ (LinearMap.id - s ∘ₗ π : M →ₗ[R] M) hmem
  have hjp : ∀ x, j (p x) = x - s (π x) := by
    intro x
    exact congrArg Subtype.val ((LinearEquiv.ofInjective j hj).apply_symm_apply
      (LinearMap.codRestrict _ (LinearMap.id - s ∘ₗ π : M →ₗ[R] M) hmem x))
  have hπj : ∀ x, π (j x) = 0 := fun x => Subtype.ext (hqi x)
  have hpj : p ∘ₗ j = LinearMap.id := by
    ext1 x
    apply hj
    rw [LinearMap.comp_apply, hjp, hπj, map_zero, sub_zero, LinearMap.id_apply]
  have hsum : j ∘ₗ p + s ∘ₗ π = LinearMap.id := by
    ext1 x
    simp only [LinearMap.add_apply, LinearMap.comp_apply, hjp, LinearMap.id_apply, sub_add_cancel]
  have hbc₁ : IsBaseChange Ω M₁.subtype :=
    isBaseChange_of_split j p π s hpj hsum M₁.subtype M.subtype M₂.subtype i q hi hqi
      (fun _ => rfl) (fun _ => rfl) hbc hbc₂
  have hfin₁ : Module.Finite R M₁ :=
    Module.Finite.of_surjective p (fun x => ⟨j x, LinearMap.congr_fun hpj x⟩)
  have hproj₁ : Module.Projective R M₁ := Module.Projective.of_split j p hpj
  have : Module.Finite Ω E := Module.Finite.equiv hbc.equiv
  have hrk₁ : Module.finrank Ω E₁ = r₁ := by
    have h1 := LinearMap.finrank_range_add_finrank_ker q
    rw [LinearMap.range_eq_top.2 hq, finrank_top, ← hex, LinearMap.finrank_range_of_inj hi,
      hrk, hrk₂] at h1
    omega
  exact GlobalTheory.T.locally_free_of_finite_projective R r₁ M₁ hfin₁ hproj₁ hrk₁ hbc₁

end GlobalTheory.CompanionTheory.Ar.Num.LocFreeKernel
end

section

open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.GraphRestrict

theorem main : ∀ {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ {V Vc : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup Vc] [Module C Vc] [Module Ω Vc] [IsScalarTower Ω C Vc] {Z Zc : Type} [AddCommGroup Z] [Module Ω Z] [AddCommGroup Zc] [Module C Zc] [Module Ω Zc] [IsScalarTower Ω C Zc] (b : V →ₗ[Ω] Vc) (b' : Z →ₗ[Ω] Zc), IsBaseChange C b → IsBaseChange C b' → ∀ (Δ : AddSubgroup (V × Z)) (H : AddSubgroup V) (N : ℕ), (∀ a ∈ R, ∀ v ∈ Δ, a • v ∈ Δ) → LocFree R N (Δ.map (AddMonoidHom.fst V Z)) → H ≤ Δ.map (AddMonoidHom.fst V Z) → (∀ a ∈ R, ∀ v ∈ H, a • v ∈ H) → spanOver RC (Prod.map b b' '' Δ) ⊓ (spanOver RC (b '' H)).prod ⊤ = spanOver RC (Prod.map b b' '' (Δ ⊓ H.prod ⊤ : AddSubgroup (V × Z))) ∧ (spanOver RC (Prod.map b b' '' Δ)).comap (AddMonoidHom.inr Vc Zc) = spanOver RC (b' '' Δ.comap (AddMonoidHom.inr V Z)) :=
  @PositivityTheory.Xgn.t_graph_restrict_bc

end GlobalTheory.CompanionTheory.Ar.GraphRestrict
end

section

open GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.dual_lattice_coordinate_generator : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (n : ℕ) (L : AddSubgroup (Fin n → Ω)), LocFree R n L → (∀ i, Summand L (annSub Ω n i)) → ∀ (i : Fin n) (u : Ω), u ≠ 0 → (∀ c, c ∈ (L ⊓ (annSub Ω n i).toAddSubgroup).map (Pi.evalAddMonoidHom (fun _ => Ω) i) ↔ ∃ a ∈ R, c = a * u) → ∀ t : Ω, (∃ v ∈ dotDual R L, (∀ j, i < j → v j = 0) ∧ v i = t) ↔ ∃ a ∈ R, t = a * u⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.HhGraded.main | exact GlobalTheory.CompanionTheory.Ar.Num.HhGraded.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.HhGraded.main <;> assumption)
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem glue_gamdel_graphs : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (w : Ω), w ∈ R → w ≠ 0 → ∀ (r s n : ℕ) (W : AddSubgroup (Fin r → Ω)) (om : AddSubgroup (Fin s → Ω)), (∀ a ∈ R, ∀ v ∈ W, a • v ∈ W) → (∀ a ∈ R, ∀ v ∈ om, a • v ∈ om) → ∀ (i : (Fin r → Ω) →ₗ[Ω] (Fin n → Ω)) (q : (Fin n → Ω) →ₗ[Ω] (Fin s → Ω)), (∀ a ∈ W, i a ∈ stdLat R (Fin n)) → (∀ b ∈ stdLat R (Fin n), q b ∈ om) → (∀ a ∈ W, i a ∈ mulLat w (stdLat R (Fin n)) → a ∈ mulLat w W) → (∀ b ∈ stdLat R (Fin n), q b ∈ mulLat w om ↔ ∃ a ∈ W, b - i a ∈ mulLat w (stdLat R (Fin n))) → (∀ c ∈ om, ∃ b ∈ stdLat R (Fin n), c - q b ∈ mulLat w om) → ∃ (Gam : AddSubgroup ((Fin r → Ω) × (Fin n → Ω))) (Del : AddSubgroup ((Fin n → Ω) × (Fin s → Ω))), (∀ a b, (a, b) ∈ Gam ↔ w • a ∈ W ∧ b - i a ∈ stdLat R (Fin n)) ∧ (∀ b c, (b, c) ∈ Del ↔ w • b ∈ stdLat R (Fin n) ∧ c - q b ∈ om) ∧ (∀ a ∈ R, (∀ v ∈ Gam, a • v ∈ Gam) ∧ ∀ v ∈ Del, a • v ∈ Del) ∧ ((∀ a, (∃ b, (a, b) ∈ Gam) ↔ w • a ∈ W) ∧ (∀ b, (0, b) ∈ Gam ↔ b ∈ stdLat R (Fin n)) ∧ ∀ a, (a, 0) ∈ Gam ↔ a ∈ W) ∧ ((∀ b, (∃ c, (b, c) ∈ Del) ↔ w • b ∈ stdLat R (Fin n)) ∧ (∀ c, (∃ b, (b, c) ∈ Del) ↔ w • c ∈ om) ∧ (∀ c, (0, c) ∈ Del ↔ c ∈ om) ∧ ∀ b, (b, 0) ∈ Del ↔ ∃ a, (a, b) ∈ Gam) :=
  PositivityTheory.HtPt.Gamdel.glue_gamdel

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem summand_baseChange : ∀ {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ {V Vc : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup Vc] [Module C Vc] [Module Ω Vc] [IsScalarTower Ω C Vc] (b : V →ₗ[Ω] Vc), IsBaseChange C b → ∀ (L : AddSubgroup V) (U : Submodule Ω V), (∀ a ∈ R, ∀ v ∈ L, a • v ∈ L) → Summand L U → Summand (spanOver RC (b '' L)) (Submodule.span C (b '' U)) ∧ spanOver RC (b '' L) ⊓ (Submodule.span C (b '' U)).toAddSubgroup = spanOver RC (b '' (L ⊓ U.toAddSubgroup : AddSubgroup V)) :=
  @PositivityTheory.Xgn.t_summand_bc

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem powSpan_locFree_baseChange : ∀ {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ (p : ℕ) (X : AddSubgroup Ω), LocFree R 1 X → LocFree R 1 (powSpan R p X) ∧ powSpan RC p (spanOver RC (algebraMap Ω C '' X)) = spanOver RC (algebraMap Ω C '' powSpan R p X) :=
  @PositivityTheory.Xgn.t_powspan

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem summand_of_locFree_quot : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {V : Type} [AddCommGroup V] [Module Ω V] (U : Submodule Ω V) (N m : ℕ) (L : AddSubgroup V), LocFree R N L → (LocFree R m (L.map U.mkQ.toAddMonoidHom) → Summand L U) ∧ (Summand L U → LocFree R (Module.finrank Ω U) (L.comap U.subtype.toAddMonoidHom) ∧ LocFree R (N - Module.finrank Ω U) (L.map U.mkQ.toAddMonoidHom)) :=
  @PositivityTheory.Xgn.summand_iff_locFree_quot

end GlobalTheory.CompanionTheory.Ar.Num
end
