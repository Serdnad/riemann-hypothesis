module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle005
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle013
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle015
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle008
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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
public import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.AdicCompletion.Completeness
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002

@[expose] public section

section

open IsLocalRing

namespace GlobalTheory.DirectedNoeth

variable {S : Type} [CommRing S] [IsLocalRing S]

theorem mem_of_forall_mem_sup_pow (T : Subring S) [IsNoetherianRing T]
    (hmax : ((maximalIdeal S).comap T.subtype).map T.subtype = maximalIdeal S)
    (hpure : ∀ J : Ideal T, (J.map T.subtype).comap T.subtype = J)
    (A : Ideal T) (x : T) (hx : ∀ n : ℕ, (x : S) ∈ A.map T.subtype ⊔ maximalIdeal S ^ n) :
    x ∈ A := by
  set m : Ideal T := (maximalIdeal S).comap T.subtype with hm
  have hjac : m ≤ Ideal.jacobson ⊥ := by
    intro y hy
    rw [Ideal.mem_jacobson_bot]
    intro z
    have hu : T.subtype (y * z + 1) ∉ maximalIdeal S := by
      intro h
      have h1 : T.subtype (y * z) ∈ maximalIdeal S := by
        rw [map_mul]; exact Ideal.mul_mem_right _ _ hy
      have h2 := Ideal.sub_mem _ h h1
      rw [map_add (f := _), add_sub_cancel_left, map_one] at h2
      exact (maximalIdeal.isMaximal S).ne_top ((Ideal.eq_top_iff_one _).mpr h2)
    have hunit : IsUnit (T.subtype (y * z + 1)) := by
      by_contra h
      exact hu ((mem_maximalIdeal _).mpr h)
    have h2 : Ideal.span {y * z + 1} = (⊤ : Ideal T) := by
      rw [← hpure (Ideal.span {y * z + 1}), Ideal.map_span, Set.image_singleton,
        Ideal.span_singleton_eq_top.mpr hunit, Ideal.comap_top]
    exact Ideal.span_singleton_eq_top.mp h2
  have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := T ⧸ A) m
    (by simpa only [Ideal.jacobson_bot] using hjac)
  have hxn : ∀ n : ℕ, x ∈ A ⊔ m ^ n := by
    intro n
    have h := hx n
    rw [← hmax, ← Ideal.map_pow, ← Ideal.map_sup] at h
    rw [← hpure (A ⊔ m ^ n)]
    exact h
  have h0 : Ideal.Quotient.mk A x ∈ (⨅ i : ℕ, m ^ i • ⊤ : Submodule T (T ⧸ A)) := by
    rw [Submodule.mem_iInf]
    intro n
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hxn n)
    have : Ideal.Quotient.mk A x = b • (1 : T ⧸ A) := by
      rw [← hab, map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add, Algebra.smul_def,
        mul_one, Ideal.Quotient.algebraMap_eq]
    rw [this]
    exact Submodule.smul_mem_smul hb trivial
  rw [hK, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at h0
  exact h0

theorem mem_sup_pow_of_algebraMap_mem (K : Ideal S) (x : S)
    (hx : algebraMap S (AdicCompletion (maximalIdeal S) S) x ∈
      K.map (algebraMap S (AdicCompletion (maximalIdeal S) S))) (n : ℕ) :
    x ∈ K ⊔ maximalIdeal S ^ n := by
  have h := Ideal.mem_map_of_mem (AdicCompletion.evalₐ (maximalIdeal S) n).toRingHom hx
  rw [Ideal.map_map] at h
  have hc : (AdicCompletion.evalₐ (maximalIdeal S) n).toRingHom.comp
      (algebraMap S (AdicCompletion (maximalIdeal S) S)) = Ideal.Quotient.mk _ := by
    ext y
    simp [AlgHom.commutes, Ideal.Quotient.algebraMap_eq]
  rw [hc] at h
  have h' : Ideal.Quotient.mk (maximalIdeal S ^ n) x ∈ K.map (Ideal.Quotient.mk _) := by
    have e : (AdicCompletion.evalₐ (maximalIdeal S) n).toRingHom
        (algebraMap S (AdicCompletion (maximalIdeal S) S) x) = Ideal.Quotient.mk _ x := by
      rw [← RingHom.comp_apply, hc]
    rw [← e]; exact h
  rw [Ideal.mem_quotient_iff_mem_sup] at h'
  exact h'

theorem isNoetherianRing_completion (hfg : (maximalIdeal S).FG) :
    IsNoetherianRing (AdicCompletion (maximalIdeal S) S) := by
  refine GlobalTheory.AdicNoeth.isNoetherianRing_of_isAdicComplete _
    ((maximalIdeal S).map (algebraMap S (AdicCompletion (maximalIdeal S) S))) (hfg.map _)
    (AdicCompletion.isAdicComplete_self _ hfg) ?_
  rw [← AdicCompletion.ker_evalOneₐ_eq_map _ hfg]
  letI := Ideal.Quotient.field (maximalIdeal S)
  haveI : IsNoetherianRing (S ⧸ maximalIdeal S) := inferInstance
  exact isNoetherianRing_of_ringEquiv _
    (RingHom.quotientKerEquivOfSurjective (f := (AdicCompletion.evalOneₐ (maximalIdeal S)).toRingHom)
      (AdicCompletion.evalOneₐ_surjective _)).symm

end GlobalTheory.DirectedNoeth

namespace GlobalTheory


open GlobalTheory.DirectedNoeth in
theorem isNoetherianRing_of_directed_pure_union : ∀ (S : Type) [CommRing S] [IsLocalRing S] (ι : Type)
    [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (R : ι → Subring S), Monotone R →
    (∀ x : S, ∃ i, x ∈ R i) → (∀ i, IsNoetherianRing (R i)) →
    (∀ i, ((maximalIdeal S).comap (R i).subtype).map (R i).subtype = maximalIdeal S) →
    (∀ i (J : Ideal (R i)), (J.map (R i).subtype).comap (R i).subtype = J) → IsNoetherianRing S := by
  intro S _ _ ι _ _ _ R hmono hcov hnoeth hmax hpure
  obtain ⟨i₁⟩ := ‹Nonempty ι›
  have hfg : (maximalIdeal S).FG := by
    haveI := hnoeth i₁
    rw [← hmax i₁]
    exact (Ideal.fg_of_isNoetherianRing _).map _
  haveI := isNoetherianRing_completion hfg
  set f := algebraMap S (AdicCompletion (maximalIdeal S) S) with hf
  refine ⟨fun (I : Ideal S) => ?_⟩
  let E : ι → Ideal S := fun i => (I.comap (R i).subtype).map (R i).subtype
  have hEI : ∀ i, E i ≤ I := fun i => Ideal.map_comap_le
  have hEmono : Monotone E := by
    intro i j hij
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    have hyj : (y : S) ∈ R j := hmono hij y.2
    have : (⟨y, hyj⟩ : R j) ∈ I.comap (R j).subtype := hy
    exact Ideal.mem_map_of_mem (R j).subtype this
  obtain ⟨_, ⟨i₀, rfl⟩, hmaxl⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian (AdicCompletion (maximalIdeal S) S) (AdicCompletion (maximalIdeal S) S))
    (Set.range fun i => (E i).map f) (Set.range_nonempty _)
  have hfg0 : (E i₀).FG := by
    haveI := hnoeth i₀
    exact (Ideal.fg_of_isNoetherianRing _).map _
  suffices hle : I ≤ E i₀ by rw [le_antisymm hle (hEI i₀)]; exact hfg0
  intro x hx
  obtain ⟨k, hk⟩ := hcov x
  obtain ⟨j, hkj, hij⟩ := directed_of (· ≤ ·) k i₀
  have hxj : x ∈ R j := hmono hkj hk
  have hEj : (E j).map f = (E i₀).map f := by
    by_contra hne
    exact hmaxl _ ⟨j, rfl⟩ (lt_of_le_of_ne (Ideal.map_mono (hEmono hij)) (Ne.symm hne))
  have hfx : f x ∈ (E i₀).map f := by
    rw [← hEj]
    apply Ideal.mem_map_of_mem
    exact Ideal.mem_map_of_mem (R j).subtype (show (⟨x, hxj⟩ : R j) ∈ I.comap (R j).subtype from hx)
  have hij' : R i₀ ≤ R j := hmono hij
  let A : Ideal (R j) := (I.comap (R i₀).subtype).map (Subring.inclusion hij')
  have hA : A.map (R j).subtype = E i₀ := by
    simp only [A, E, Ideal.map_map]
    rfl
  have hxA : (⟨x, hxj⟩ : R j) ∈ A := by
    haveI := hnoeth j
    apply mem_of_forall_mem_sup_pow (R j) (hmax j) (hpure j) A
    intro n
    rw [hA]
    exact mem_sup_pow_of_algebraMap_mem (E i₀) x hfx n
  have := Ideal.mem_map_of_mem (R j).subtype hxA
  rwa [hA] at this

end GlobalTheory
end

section

namespace GlobalTheory

theorem ks_cancel_submodule (R P : Type) [Ring R] [AddCommGroup P] [Module R P] [IsArtinian R P]
    [IsNoetherian R P] (N : Submodule R P) :
    ∀ (M M' : Type) [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'],
      Nonempty ((M × N) ≃ₗ[R] (M' × N)) → Nonempty (M ≃ₗ[R] M') := by
  induction N using WellFoundedLT.induction with
  | _ N ih =>
  intro M M' _ _ _ _ e
  by_cases hind : ∀ A B : Submodule R N, IsCompl A B → A = ⊥ ∨ B = ⊥
  · exact GlobalTheory.T.cancel_prod_summand_nilpotent_or_bijective R M M' N (GlobalTheory.T.endomorphism_indecomposable_nilpotent_or_bijective R N hind) e
  · push_neg at hind
    obtain ⟨A, B, hAB, hA, hB⟩ := hind
    have hAlt : A.map N.subtype < N := by
      have h1 : A < ⊤ := lt_top_iff_ne_top.mpr (fun h => hB (by
        have := hAB.inf_eq_bot; rw [h, top_inf_eq] at this; exact this))
      have := Submodule.map_strictMono_of_injective N.injective_subtype h1
      rwa [Submodule.map_subtype_top] at this
    have hBlt : B.map N.subtype < N := by
      have h1 : B < ⊤ := lt_top_iff_ne_top.mpr (fun h => hA (by
        have := hAB.inf_eq_bot; rw [h, inf_top_eq] at this; exact this))
      have := Submodule.map_strictMono_of_injective N.injective_subtype h1
      rwa [Submodule.map_subtype_top] at this
    let eA : A ≃ₗ[R] A.map N.subtype := Submodule.equivMapOfInjective _ N.injective_subtype A
    let eB : B ≃ₗ[R] B.map N.subtype := Submodule.equivMapOfInjective _ N.injective_subtype B
    let eN : N ≃ₗ[R] (A.map N.subtype × B.map N.subtype) :=
      (Submodule.prodEquivOfIsCompl A B hAB).symm ≪≫ₗ LinearEquiv.prodCongr eA eB
    obtain ⟨e⟩ := e
    let f : ((M × A.map N.subtype) × B.map N.subtype) ≃ₗ[R]
        ((M' × A.map N.subtype) × B.map N.subtype) :=
      (LinearEquiv.prodAssoc R M _ _) ≪≫ₗ (LinearEquiv.prodCongr (LinearEquiv.refl R M) eN).symm ≪≫ₗ e ≪≫ₗ
        (LinearEquiv.prodCongr (LinearEquiv.refl R M') eN) ≪≫ₗ (LinearEquiv.prodAssoc R M' _ _).symm
    obtain ⟨g⟩ := ih _ hBlt _ _ ⟨f⟩
    exact ih _ hAlt M M' ⟨g⟩

theorem ks_cancel : ∀ (R M M' P : Type) [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R M'] [AddCommGroup P] [Module R P] [IsArtinian R P] [IsNoetherian R P],
    Nonempty ((M × P) ≃ₗ[R] (M' × P)) → Nonempty (M ≃ₗ[R] M') := by
  intro R M M' P _ _ _ _ _ _ _ _ _ ⟨e⟩
  let t : (⊤ : Submodule R P) ≃ₗ[R] P := Submodule.topEquiv
  exact ks_cancel_submodule R P ⊤ M M'
    ⟨(LinearEquiv.prodCongr (LinearEquiv.refl R M) t) ≪≫ₗ e ≪≫ₗ
      (LinearEquiv.prodCongr (LinearEquiv.refl R M') t).symm⟩

end GlobalTheory
end

section

open NumberField IsDedekindDomain

open WithZero

namespace GlobalTheory.DenseCompl

section DVR

variable {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [IsFractionRing W Qq]

noncomputable def closedPoint (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] :
    HeightOneSpectrum W :=
  ⟨IsLocalRing.maximalIdeal W, inferInstance, IsDiscreteValuationRing.not_a_field W⟩

theorem asIdeal_eq_span {π : W} (hπ : Irreducible π) (v : HeightOneSpectrum W) :
    v.asIdeal = Ideal.span {π} := by
  rw [← hπ.maximalIdeal_eq]
  exact IsLocalRing.eq_maximalIdeal v.isMaximal

theorem valuation_uniformiser {π : W} (hπ : Irreducible π) (v : HeightOneSpectrum W) :
    v.valuation Qq (algebraMap W Qq π) = exp (-1) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact v.intValuation_singleton hπ.ne_zero (asIdeal_eq_span hπ v)

theorem exists_eq_pow_mul_iff {π : W} (hπ : Irreducible π) (v : HeightOneSpectrum W) (q : Qq) (n : ℕ) :
    (∃ w : W, q = algebraMap W Qq (π ^ n * w)) ↔ v.valuation Qq q ≤ exp (-(n : ℤ)) := by
  constructor
  · rintro ⟨w, rfl⟩
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem,
      asIdeal_eq_span hπ v, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact dvd_mul_right _ _
  · intro h
    have hπ0 : algebraMap W Qq π ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective W Qq)]
      exact hπ.ne_zero
    obtain ⟨w, hw⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one Qq
      (q / algebraMap W Qq π ^ n) fun v' => by
        have hv : v' = v :=
          HeightOneSpectrum.ext ((asIdeal_eq_span hπ v').trans (asIdeal_eq_span hπ v).symm)
        subst hv
        rw [map_div₀, map_pow, valuation_uniformiser hπ v', ← WithZero.exp_nsmul, smul_neg, nsmul_one,
          div_le_iff₀ exp_pos, one_mul]
        exact h
    refine ⟨w, ?_⟩
    rw [map_mul, map_pow, hw, mul_div_cancel₀ _ (pow_ne_zero _ hπ0)]

end DVR

theorem le_of_forall_le_exp {a b : ℤᵐ⁰} (hb : b ≤ 1)
    (h : ∀ n : ℕ, b ≤ exp (-(n : ℤ)) → a ≤ exp (-(n : ℤ))) : a ≤ b := by
  rcases eq_or_ne b 0 with rfl | hb0
  · by_contra ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact ha le_rfl
    obtain ⟨n, hn⟩ := GlobalTheory.Idele.exists_exp_neg_lt ha0
    exact absurd (h n zero_le') (not_le.2 hn)
  · have hl : log b ≤ 0 := by
      rw [← exp_le_exp, exp_log hb0, exp_zero]
      exact hb
    have hn : (((-log b).toNat : ℕ) : ℤ) = -log b := Int.toNat_of_nonneg (by omega)
    have he : exp (-(((-log b).toNat : ℕ) : ℤ)) = b := by
      rw [hn, neg_neg, exp_log hb0]
    exact (h _ he.ge).trans he.le

theorem eq_zero_of_forall_le_exp {a : ℤᵐ⁰} (h : ∀ n : ℕ, a ≤ exp (-(n : ℤ))) : a = 0 :=
  le_antisymm (le_of_forall_le_exp zero_le' fun n _ => h n) zero_le'

theorem continuous_of_valued_eq {A B Γ : Type*} [Ring A] [Ring B] [LinearOrderedCommGroupWithZero Γ]
    [Valued A Γ] [Valued B Γ] (hs : Function.Surjective (Valued.v : A → Γ)) (f : A →+* B)
    (hf : ∀ x, Valued.v (f x) = Valued.v x) : Continuous f := by
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero A _).tendsto_iff (Valued.hasBasis_nhds_zero B _)]
  intro γ _
  obtain ⟨a, ha⟩ := hs (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  have ha0 : (Valued.v : Valuation A Γ).restrict a ≠ 0 := by
    simp [ha]
  refine ⟨Units.mk0 _ ha0, trivial, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hx
  simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
  rw [hf, ← ha]
  exact hx


open scoped WithZeroTopology in
theorem exists_extension {K : Type} [Field K] [NumberField K] {R L : Type} [CommRing R] [IsDedekindDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L]
    (w : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum R) (f : K →+* u.adicCompletion L)
    (hf : ∀ x, Valued.v (f x) = w.valuation K x) :
    ∃ φ : w.adicCompletion K →+* u.adicCompletion L, Continuous φ ∧
      (∀ x : K, φ (algebraMap K _ x) = f x) ∧ ∀ y, Valued.v (φ y) = Valued.v y := by
  first
  | exact @_root_.GlobalTheory.ValuationExtensionContinuous.exists_extension
  | exact _root_.GlobalTheory.ValuationExtensionContinuous.exists_extension
  | (apply _root_.GlobalTheory.ValuationExtensionContinuous.exists_extension <;> assumption)
  | (intros; apply _root_.GlobalTheory.ValuationExtensionContinuous.exists_extension <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ValuationExtensionContinuous.exists_extension <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ValuationExtensionContinuous.exists_extension ..)

end GlobalTheory.DenseCompl
end

section

open GlobalTheory.Cong

namespace GlobalTheory.CongTorsion

open Finset

variable {R : Type} [CommRing R] {a : ℕ}

lemma one_add_smul_pow (t : R) (z : Matrix (Fin a) (Fin a) R) (n : ℕ) :
    (1 + t • z) ^ n = 1 + t • ∑ m ∈ range n, t ^ m • ((n.choose (m + 1)) • z ^ (m + 1)) := by
  rw [add_comm, (Commute.one_right (t • z)).add_pow, sum_range_succ', add_comm]
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one]
  congr 1
  rw [smul_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [← nsmul_eq_mul', smul_pow, smul_smul, ← pow_succ', smul_comm]

lemma dvd_entries_of_pow_eq_one [IsDomain R] [IsLocalRing R] [CharZero R] {l p : ℕ} (hl : l.Prime)
    (hlu : ¬ IsUnit (l : R)) (hp : p.Prime) {t : R} (ht : (l : R) ^ 2 ∣ t) (ht0 : t ≠ 0)
    {z : Matrix (Fin a) (Fin a) R} (hz : (1 + t • z) ^ p = 1) (i j : Fin a) : (l : R) ∣ z i j := by
  have h := one_add_smul_pow t z p
  rw [hz] at h
  have hS : t • ∑ m ∈ range p, t ^ m • ((p.choose (m + 1)) • z ^ (m + 1)) = 0 := by
    have := congrArg (fun A => A - 1) h
    simpa using this.symm
  rw [smul_eq_zero] at hS
  have hS := hS.resolve_left ht0
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  rw [sum_range_succ'] at hS
  have he := congrFun (congrFun hS i) j
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    pow_zero, one_smul, zero_add, Nat.choose_one_right, pow_one, Matrix.zero_apply] at he
  simp only [nsmul_eq_mul] at he
  have hdiv : (l : R) ^ 2 ∣ ((q + 1 : ℕ) : R) * z i j := by
    have : ((q + 1 : ℕ) : R) * z i j = -(∑ m ∈ range q, t ^ (m + 1) *
        (((q + 1).choose (m + 1 + 1) : R) * (z ^ (m + 1 + 1)) i j)) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact he
    rw [this, dvd_neg]
    exact dvd_sum fun m _ => dvd_mul_of_dvd_left (ht.trans (dvd_pow_self t (Nat.succ_ne_zero m))) _
  have hl0 : (l : R) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  by_cases hpl : q + 1 = l
  · rw [hpl, pow_two] at hdiv
    exact (mul_dvd_mul_iff_left hl0).mp hdiv
  · have hcop : Nat.Coprime (q + 1) l := (Nat.coprime_primes hp hl).mpr hpl
    have hc : IsCoprime ((q + 1 : ℕ) : R) (l : R) := by
      have := (Nat.isCoprime_iff_coprime.mpr hcop).map (Int.castRingHom R)
      simpa using this
    obtain ⟨u, v, huv⟩ := hc
    have hpu : IsUnit ((q + 1 : ℕ) : R) := by
      rcases IsLocalRing.isUnit_or_isUnit_of_add_one huv with h1 | h1
      · exact isUnit_of_mul_isUnit_right h1
      · exact absurd (isUnit_of_mul_isUnit_right h1) hlu
    exact (dvd_pow_self (l : R) two_ne_zero).trans ((hpu.dvd_mul_left).mp hdiv)

lemma pow_dvd_entries_of_pow_eq_one [IsDomain R] [IsLocalRing R] [CharZero R] {l p : ℕ}
    (hl : l.Prime) (hlu : ¬ IsUnit (l : R)) (hp : p.Prime) (N : ℕ) :
    ∀ (t : R) (z : Matrix (Fin a) (Fin a) R), (l : R) ^ 2 ∣ t → t ≠ 0 → (1 + t • z) ^ p = 1 →
      ∀ i j, (l : R) ^ N ∣ z i j := by
  have hl0 : (l : R) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  induction N with
  | zero => intro t z _ _ _ i j; simp
  | succ N ih =>
    intro t z ht ht0 hz i j
    have hd := dvd_entries_of_pow_eq_one hl hlu hp ht ht0 hz
    choose w hw using hd
    have hzz : z = (l : R) • Matrix.of w := by ext i j; simp [hw i j]
    have htz : t • z = (t * l) • Matrix.of w := by rw [hzz, smul_smul]
    have h' := ih (t * l) (Matrix.of w) (dvd_mul_of_dvd_left ht _) (mul_ne_zero ht0 hl0)
      (by rw [← htz]; exact hz) i j
    rw [hw i j, pow_succ']
    exact mul_dvd_mul_left _ (by simpa using h')

lemma eq_zero_of_forall_pow_dvd [IsDomain R] [IsDiscreteValuationRing R] {c b : R}
    (hc : ¬ IsUnit c) (h : ∀ N, c ^ N ∣ b) : b = 0 := by
  by_contra hb
  obtain ⟨n, hn⟩ := FiniteMultiplicity.of_not_isUnit hc hb
  exact hn (h _)

end GlobalTheory.CongTorsion

namespace GlobalTheory


open GlobalTheory.CongTorsion in
theorem principalCongruence_torsionFree :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (l m a : ℕ),
      l.Prime → ¬ IsUnit (l : R) → 2 ≤ m → ∀ (x : Matrix (Fin a) (Fin a) R) (n : ℕ), 0 < n →
        (1 + ((l : R) ^ m) • x) ^ n = 1 → x = 0 := by
  intro R _ _ _ _ l m a hl hlu hm x n hn hx
  have hl0 : (l : R) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  have hc0 : (l : R) ^ m ≠ 0 := pow_ne_zero _ hl0
  have hc2 : (l : R) ^ 2 ∣ (l : R) ^ m := pow_dvd_pow _ hm
  induction n using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    by_cases h1 : n = 1
    · subst h1
      rw [pow_one, add_eq_left, smul_eq_zero] at hx
      exact hx.resolve_left hc0
    · set p := n.minFac with hpdef
      have hp : p.Prime := Nat.minFac_prime h1
      obtain ⟨k, hk⟩ := Nat.minFac_dvd n
      have hkpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · rw [h, mul_zero] at hk; omega
        · exact h
      have hklt : k < n := by
        rw [hk]; exact lt_mul_left hkpos hp.one_lt
      have he := one_add_smul_pow ((l : R) ^ m) x p
      rw [hk, pow_mul, he] at hx
      have hx' := ih k hklt _ hkpos hx
      rw [hx', smul_zero, add_zero] at he
      ext i j
      exact eq_zero_of_forall_pow_dvd hlu
        (fun N => pow_dvd_entries_of_pow_eq_one hl hlu hp N _ x hc2 hc0 he i j)

end GlobalTheory
end
