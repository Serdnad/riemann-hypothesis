module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Module.PID
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.LinearAlgebra.FreeProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Filtration

@[expose] public section

section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem dvr_matrix_proj_preimage (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] (n : Type) [Fintype n] [DecidableEq n]
    (S : Submodule K (n → K)) :
    ∃ P : Matrix n n O, (∀ v : n → O, (fun i => algebraMap O K ((P.mulVec v) i)) ∈ S) ∧
      ∀ u : n → O, (fun i => algebraMap O K (u i)) ∈ S → P.mulVec u = u := by
  classical
  let f : (n → O) →ₗ[O] (n → K) := LinearMap.compLeft (Algebra.linearMap O K) n
  let U : Submodule O (n → O) := (S.restrictScalars O).comap f
  have hmem : ∀ v : n → O, v ∈ U ↔ (fun i => algebraMap O K (v i)) ∈ S := fun v => Iff.rfl
  have htf : NoZeroSMulDivisors O ((n → O) ⧸ U) := by
    constructor
    intro c x hcx
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective U x
    by_cases hc : c = 0
    · left; exact hc
    right
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hcx
    rw [Submodule.Quotient.mk_eq_zero]
    rw [hmem] at hcx ⊢
    have e : (fun i => algebraMap O K ((c • v) i)) = algebraMap O K c • (fun i => algebraMap O K (v i)) := by
      funext i; simp [Algebra.smul_def]
    rw [e] at hcx
    have hc' : algebraMap O K c ≠ 0 := by
      intro h; exact hc ((IsFractionRing.injective O K) (by rw [h, map_zero]))
    have := S.smul_mem (algebraMap O K c)⁻¹ hcx
    rwa [smul_smul, inv_mul_cancel₀ hc', one_smul] at this
  haveI : Module.Free O ((n → O) ⧸ U) := Module.free_of_finite_type_torsion_free'
  haveI : Module.Projective O ((n → O) ⧸ U) := Module.Projective.of_free
  obtain ⟨s, hs⟩ := Module.projective_lifting_property U.mkQ LinearMap.id (Submodule.mkQ_surjective U)
  let π : (n → O) →ₗ[O] (n → O) := LinearMap.id - s ∘ₗ U.mkQ
  have hπU : ∀ v, π v ∈ U := by
    intro v
    rw [← Submodule.Quotient.mk_eq_zero]
    have := LinearMap.congr_fun hs (U.mkQ v)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, Submodule.Quotient.mk_sub]
    rw [← Submodule.mkQ_apply U (s _), this, Submodule.mkQ_apply, sub_self]
  have hπfix : ∀ u ∈ U, π u = u := by
    intro u hu
    have h0 : U.mkQ u = 0 := (Submodule.Quotient.mk_eq_zero U).mpr hu
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h0, map_zero, sub_zero]
  refine ⟨LinearMap.toMatrix' π, ?_, ?_⟩
  · intro v
    rw [LinearMap.toMatrix'_mulVec]
    exact hπU v
  · intro u hu
    rw [LinearMap.toMatrix'_mulVec]
    exact hπfix u hu

end GlobalTheory
end

section

open Module

noncomputable section

namespace GlobalTheory.DVRQuotCount

open scoped TensorProduct DirectSum

theorem card_quot_smul_top_of_flat' {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Flat R N] (I : Ideal R) [Finite (R ⧸ I)] :
    Nat.card (N ⧸ (I • ⊤ : Submodule R N)) = Nat.card (R ⧸ I) ^ Module.finrank R N := by
  have : IsArtinianRing (R ⧸ I) := isArtinian_of_finite
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N) (Module.finrank R N)
    (fun P => by
      have := P.isMaximal
      let : Field ((R ⧸ I) ⧸ P.asIdeal) := Ideal.Quotient.field _
      rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal)
        ((R ⧸ I) ⧸ P.asIdeal) N).finrank_eq]
      have h1 := Module.rankAtStalk_baseChange (R := R) (M := N) (S := (R ⧸ I) ⧸ P.asIdeal) ⊥
      rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at h1
      exact h1)
  rw [← Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul N I).toEquiv,
    Nat.card_congr b.equivFun.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]

theorem rank_prod_of_rank_zero {R A B : Type} [CommRing R] [IsDomain R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (hB : ∀ x : B, ∃ a : R, a ≠ 0 ∧ a • x = 0) :
    Module.rank R (A × B) = Module.rank R A := by
  have h := LinearMap.rank_range_add_rank_ker (LinearMap.fst R A B)
  have hk : Module.rank R (LinearMap.ker (LinearMap.fst R A B)) = 0 := by
    rw [rank_eq_zero_iff]
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, hax⟩ := hB x.2
    refine ⟨a, ha, ?_⟩
    ext
    · simpa using congrArg (a • ·) (show x.1 = 0 from hx)
    · simpa using hax
  rw [LinearMap.range_eq_top.2 (fun a => ⟨(a, 0), rfl⟩), rank_top, hk, add_zero] at h
  exact h.symm

theorem irreducible_dvd {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p t : O}
    (hp : Irreducible p) (ht : t ≠ 0) (htu : ¬ IsUnit t) : p ∣ t := by
  obtain ⟨q, hq, hqt⟩ := WfDvdMonoid.exists_irreducible_factor htu ht
  exact (IsDiscreteValuationRing.associated_of_irreducible O hp hq).dvd.trans hqt

theorem card_quot_pow_smul_bounds : ∀ (O M : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup M] [Module O M] [Module.Finite O M] (t : O), t ≠ 0 → ¬ IsUnit t →
    (∀ r : ℕ, Finite (O ⧸ Ideal.span {t ^ r})) → ∃ C : ℕ, 0 < C ∧ ∀ r : ℕ,
      Nat.card (O ⧸ Ideal.span {t ^ r}) ^ finrank O M ≤
        Nat.card (M ⧸ (Ideal.span {t ^ r} • ⊤ : Submodule O M)) ∧
      Nat.card (M ⧸ (Ideal.span {t ^ r} • ⊤ : Submodule O M)) ≤
        C * Nat.card (O ⧸ Ideal.span {t ^ r}) ^ finrank O M := by
  intro O M _ _ _ _ _ _ t ht htu hfin
  obtain ⟨n, ι, _, p, hp, e, ⟨eqv⟩⟩ := Module.equiv_free_prod_directSum O M
  set T := ⨁ i : ι, O ⧸ O ∙ p i ^ e i
  set F := Fin n →₀ O

  have hTi : ∀ i, Finite (O ⧸ O ∙ p i ^ e i) := by
    intro i
    have hle : Ideal.span {t ^ e i} ≤ Ideal.span {p i ^ e i} := by
      rw [Ideal.span_singleton_le_span_singleton]
      exact pow_dvd_pow_of_dvd (irreducible_dvd (hp i) ht htu) _
    haveI := hfin (e i)
    exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)
  haveI : Finite T := Finite.of_equiv _ (DirectSum.linearEquivFunOnFintype O ι _).toEquiv.symm

  have hkill : ∀ x : T, ∃ a : O, a ≠ 0 ∧ a • x = 0 := by
    intro x
    refine ⟨∏ i, p i ^ e i, Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hp i).ne_zero, ?_⟩
    ext i
    rw [DirectSum.smul_apply, DirectSum.zero_apply]
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (x i)
    rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul,
      Submodule.mem_span_singleton]
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun j => p j ^ e j) (Finset.mem_univ i)
    exact ⟨c * y, by rw [hc, smul_eq_mul]; ring⟩
  have hrank : finrank O M = n := by
    rw [eqv.finrank_eq]
    unfold Module.finrank
    rw [rank_prod_of_rank_zero hkill]
    change finrank O F = n
    simp [F]
  refine ⟨Nat.card T, Nat.card_pos, fun r => ?_⟩
  set I : Ideal O := Ideal.span {t ^ r}
  haveI := hfin r
  have hcard : Nat.card (M ⧸ (I • ⊤ : Submodule O M)) =
      Nat.card (O ⧸ I) ^ n * Nat.card (T ⧸ (I • ⊤ : Submodule O T)) := by
    rw [← Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul M I).toEquiv,
      Nat.card_congr (TensorProduct.congr (LinearEquiv.refl O (O ⧸ I)) eqv).toEquiv,
      Nat.card_congr (TensorProduct.prodRight O O (O ⧸ I) F T).toEquiv, Nat.card_prod,
      Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul F I).toEquiv,
      Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul T I).toEquiv,
      card_quot_smul_top_of_flat']
    simp [F]
  haveI : Finite (T ⧸ (I • ⊤ : Submodule O T)) := Finite.of_surjective _ (Submodule.mkQ_surjective _)
  have h1 : 1 ≤ Nat.card (T ⧸ (I • ⊤ : Submodule O T)) := Nat.card_pos
  have h2 : Nat.card (T ⧸ (I • ⊤ : Submodule O T)) ≤ Nat.card T :=
    Nat.card_le_card_of_surjective _ (Submodule.mkQ_surjective _)
  rw [hcard, hrank]
  constructor
  · exact Nat.le_mul_of_pos_right _ h1
  · rw [mul_comm]; exact Nat.mul_le_mul_right _ h2

end GlobalTheory.DVRQuotCount
end
end

section

open Polynomial

namespace GlobalTheory

theorem finite_quot_span_singleton_of_dvr_sandwich (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [hF : Finite (IsLocalRing.ResidueField O)] (c : O) (hc : c ≠ 0) :
    Finite (O ⧸ Ideal.span {c}) := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hne : Ideal.span {c} ≠ ⊥ := by simpa using hc
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hp
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {p} := hp.maximalIdeal_eq
  rw [hn, ← Ideal.span_singleton_pow, ← hm]
  haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) := hF
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n

theorem finite_submodules_between_smul_and_self :
    ∀ (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [AddCommGroup A] [Module O A] (C : Submodule O A), C.FG → ∀ c : O, c ≠ 0 → {N : Submodule O A | N ≤ C ∧ ∀ x ∈ C, c • x ∈ N}.Finite := by
  intro O A _ _ _ _ _ _ C hC c hc
  haveI := finite_quot_span_singleton_of_dvr_sandwich O c hc
  haveI : Module.Finite O C := Module.Finite.iff_fg.mpr hC
  let K : Submodule O C := (Ideal.span {c}) • (⊤ : Submodule O C)
  haveI : Finite (C ⧸ K) := Submodule.finite_quotient_smul (Ideal.span {c}) Module.Finite.fg_top
  let f : Submodule O A → Set (C ⧸ K) := fun N => K.mkQ '' {x : C | (x : A) ∈ N}
  have key : ∀ N M : Submodule O A, (N ≤ C ∧ ∀ x ∈ C, c • x ∈ N) → (M ≤ C ∧ ∀ x ∈ C, c • x ∈ M) →
      f N = f M → N ≤ M := by
    intro N M hN hM h x hx
    have h1 : K.mkQ ⟨x, hN.1 hx⟩ ∈ f M := h ▸ ⟨⟨x, hN.1 hx⟩, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := h1
    have h2 : y - ⟨x, hN.1 hx⟩ ∈ K := (Submodule.Quotient.eq K).mp hxy
    have h3 : ∀ z ∈ K, (z : A) ∈ M := by
      intro z hz
      refine Submodule.smul_induction_on hz ?_ ?_
      · intro r hr n _
        obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hr
        rw [Submodule.coe_smul, mul_smul]
        exact M.smul_mem a (hM.2 n n.2)
      · intro a b ha hb
        exact M.add_mem ha hb
    have h4 := M.sub_mem hy (h3 _ h2)
    simpa using h4
  refine Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_
  intro N hN M hM h
  exact le_antisymm (key N M hN hM h) (key M N hM hN h.symm)

end GlobalTheory
end

section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory.GenUnr

theorem finite_classes_mod_pow (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K]
    (r t : ℕ) (ϖ : O) (hϖ : Irreducible ϖ) (N : ℕ) :
    ∃ T : Finset (Matrix (Fin r ⊕ Fin t) (Fin r) K),
      ∀ (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O),
        algebraMap O K (ϖ ^ N) • x = z.map (algebraMap O K) →
        ∃ y ∈ T, ∃ z' : Matrix (Fin r ⊕ Fin t) (Fin r) O,
          x = y + (ϖ ^ N • z').map (algebraMap O K) := by
  classical
  have hfin : Finite (O ⧸ Ideal.span {ϖ ^ (2 * N)}) :=
    IsLocalRing.finite_quotient_iff.mpr
      ⟨2 * N, by rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]⟩
  haveI := Fintype.ofFinite (Matrix (Fin r ⊕ Fin t) (Fin r) (O ⧸ Ideal.span {ϖ ^ (2 * N)}))
  have hϖK : algebraMap O K ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr hϖ.ne_zero
  let lift : O ⧸ Ideal.span {ϖ ^ (2 * N)} → O := fun c => (Ideal.Quotient.mk_surjective c).choose
  have hlift : ∀ c, Ideal.Quotient.mk _ (lift c) = c := fun c =>
    (Ideal.Quotient.mk_surjective c).choose_spec
  let rep : Matrix (Fin r ⊕ Fin t) (Fin r) (O ⧸ Ideal.span {ϖ ^ (2 * N)}) →
      Matrix (Fin r ⊕ Fin t) (Fin r) K :=
    fun c => (algebraMap O K (ϖ ^ N))⁻¹ • (c.map lift).map (algebraMap O K)
  refine ⟨Finset.univ.image rep, fun x z hxz => ?_⟩
  have hdiff : ∀ i j, ∃ a : O, a * ϖ ^ (2 * N) = z i j - lift (Ideal.Quotient.mk _ (z i j)) :=
    fun i j => Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp (hlift _).symm)
  choose w hw using hdiff
  refine ⟨rep (z.map (Ideal.Quotient.mk _)), Finset.mem_image_of_mem _ (Finset.mem_univ _), Matrix.of w, ?_⟩
  ext i j
  have hx := congrFun (congrFun hxz i) j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, map_pow] at hx
  have hz : lift (Ideal.Quotient.mk _ (z i j)) = z i j - w i j * ϖ ^ (2 * N) := by
    rw [hw]; ring
  simp only [rep, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, hz, map_sub,
    map_mul, map_pow, Matrix.of_apply, ← hx]
  field_simp
  ring

end GlobalTheory.GenUnr
end

section

open scoped BigOperators

namespace GlobalTheory

open PowerSeries


open scoped BigOperators in
open PowerSeries in
theorem _root_.GlobalTheory.exists_low_coeff_not_dvd_of_congr_mul : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (D g f : PowerSeries O) (m₀ v nT MT : ℕ), (∃ m ≤ m₀, IsUnit (PowerSeries.coeff m D)) → ¬ ϖ ^ (v + 1) ∣ PowerSeries.coeff 0 g → v + 1 ≤ nT → (v + 1) * m₀ ≤ MT → (∀ i ≤ MT, ϖ ^ nT ∣ PowerSeries.coeff i (f - D * g)) → ∃ i ≤ (v + 1) * m₀, ¬ ϖ ^ (v + 1) ∣ PowerSeries.coeff i f := by
  intro O _ _ _ ϖ hϖ D g f m₀ v nT MT hD hg hv hM hf
  classical
  have hnu : ∀ x : O, ¬ IsUnit x → ϖ ∣ x := fun x hx => by
    have hmax : x ∈ IsLocalRing.maximalIdeal O := hx
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ,
      Ideal.mem_span_singleton] at hmax
    exact hmax
  by_contra hcon
  push_neg at hcon
  have hDg : ∀ i ≤ (v + 1) * m₀, ϖ ^ (v + 1) ∣ PowerSeries.coeff i (D * g) := by
    intro i hi
    have h1 := dvd_trans (pow_dvd_pow ϖ hv) (hf i (hi.trans hM))
    have h2 := hcon i hi
    have : PowerSeries.coeff i (D * g) = PowerSeries.coeff i f - PowerSeries.coeff i (f - D * g) := by
      simp
    rw [this]
    exact dvd_sub h2 h1
  have hD' : ∃ m, m ≤ m₀ ∧ IsUnit (PowerSeries.coeff m D) := hD
  set m₁ := Nat.find hD' with hm₁
  have hm₁le : m₁ ≤ m₀ := (Nat.find_spec hD').1
  have hm₁u : IsUnit (PowerSeries.coeff m₁ D) := (Nat.find_spec hD').2
  have hlow : ∀ a < m₁, ϖ ∣ PowerSeries.coeff a D := fun a ha =>
    hnu _ fun hu => Nat.find_min hD' ha ⟨(ha.trans_le hm₁le).le, hu⟩
  have claim : ∀ j ≤ v + 1, ∀ i, i + j * m₁ ≤ (v + 1) * m₀ → ϖ ^ j ∣ PowerSeries.coeff i g := by
    intro j
    induction j with
    | zero => intro _ i _; simp
    | succ j ihj =>
      intro hj i
      induction i using Nat.strong_induction_on with
      | _ i ihi =>
        intro hi
        have hsplit := (Finset.add_sum_erase (Finset.HasAntidiagonal.antidiagonal (i + m₁))
          (fun p : ℕ × ℕ => PowerSeries.coeff p.1 D * PowerSeries.coeff p.2 g)
          (a := (m₁, i)) (by simp [add_comm])).symm
        rw [← PowerSeries.coeff_mul] at hsplit
        have hrest : ϖ ^ (j + 1) ∣ ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal (i + m₁)).erase (m₁, i),
            PowerSeries.coeff p.1 D * PowerSeries.coeff p.2 g := by
          apply Finset.dvd_sum
          rintro ⟨a, b⟩ hp
          simp only [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal, ne_eq, Prod.mk.injEq] at hp
          obtain ⟨hne, hab⟩ := hp
          rcases lt_trichotomy a m₁ with h | h | h
          · rw [pow_succ, mul_comm (ϖ ^ j)]
            exact mul_dvd_mul (hlow a h) (ihj (by omega) b (by nlinarith))
          · exact absurd ⟨h, by omega⟩ hne
          · exact dvd_mul_of_dvd_right (ihi b (by omega) (by nlinarith)) _
        have htot : ϖ ^ (j + 1) ∣ PowerSeries.coeff (i + m₁) (D * g) :=
          dvd_trans (pow_dvd_pow ϖ hj) (hDg _ (by nlinarith))
        rw [hsplit] at htot
        have := (dvd_add_left hrest).1 htot
        exact (hm₁u.dvd_mul_left).1 this
  exact hg (by simpa using claim (v + 1) le_rfl 0 (by simpa using Nat.mul_le_mul_left (v + 1) hm₁le))

end GlobalTheory
end

section

namespace GlobalTheory

theorem compact_dvr_complete_separated : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (ϖ : O), Irreducible ϖ → (∀ x : ℕ → O, ∃ a : O, ∀ n : ℕ, ∃ b : O, a - ∑ j ∈ Finset.range n, ϖ ^ j * x j = ϖ ^ n * b) ∧ (∀ a : O, (∀ n : ℕ, ∃ b : O, a = ϖ ^ n * b) → a = 0) := by
  intro O _ _ _ _ _ _ _ _ ϖ hϖ
  refine ⟨fun x => ?_, fun a ha => ?_⟩
  · set s : ℕ → O := fun n => ∑ j ∈ Finset.range n, ϖ ^ j * x j with hs
    let C : ℕ → Set O := fun n => Set.range (fun b : O => s n + ϖ ^ n * b)
    have hcpt : ∀ n, IsCompact (C n) := fun n =>
      isCompact_range (continuous_const.add (continuous_const.mul continuous_id))
    have hdec : ∀ n, C (n + 1) ⊆ C n := by
      intro n y ⟨b, hb⟩
      refine ⟨x n + ϖ * b, ?_⟩
      rw [← hb]
      simp only [hs, Finset.sum_range_succ, pow_succ]
      ring
    have hne : ∀ n, (C n).Nonempty := fun n => ⟨_, ⟨0, rfl⟩⟩
    obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hdec hne
      (hcpt 0) (fun n => (hcpt n).isClosed)
    refine ⟨a, fun n => ?_⟩
    obtain ⟨b, hb⟩ := Set.mem_iInter.mp ha n
    exact ⟨b, by rw [← hb]; simp [hs]⟩
  · have hne : Ideal.span {ϖ} ≠ (⊤ : Ideal O) := by
      rw [Ne, Ideal.span_singleton_eq_top]; exact hϖ.not_isUnit
    have h := Ideal.iInf_pow_eq_bot_of_isLocalRing (Ideal.span {ϖ}) hne
    have : a ∈ ⨅ i, (Ideal.span {ϖ}) ^ i := by
      rw [Submodule.mem_iInf]
      intro i
      obtain ⟨b, hb⟩ := ha i
      rw [Ideal.span_singleton_pow, hb]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [h] at this
    exact (Submodule.mem_bot O).mp this

end GlobalTheory
end

section

namespace GlobalTheory

open IsLocalRing

theorem finite_free_compact_adic_dvr
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O] (hadic : IsAdic (IsLocalRing.maximalIdeal O))
    {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul O M] [T2Space M] [Module.Free O M] [Module.Finite O M]
    (ϖ : O) (hϖ : Irreducible ϖ) :
    CompactSpace M ∧ IsOpen (LinearMap.range (LinearMap.lsmul O M ϖ) : Set M) ∧
      Topology.IsClosedEmbedding (fun m : M => ϖ • m) := by
  classical
  let b := Module.Free.chooseBasis O M
  have hΦ : Continuous (b.equivFun.symm : (Module.Free.ChooseBasisIndex O M → O) → M) := by
    have : (b.equivFun.symm : (Module.Free.ChooseBasisIndex O M → O) → M) =
        fun v => ∑ i, v i • b i := by
      funext v; simp
    rw [this]
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  let H : (Module.Free.ChooseBasisIndex O M → O) ≃ₜ M :=
    hΦ.homeoOfEquivCompactToT2 (f := b.equivFun.symm.toEquiv)
  have hH : ∀ v, H v = b.equivFun.symm v := fun v => rfl
  have hcpt : CompactSpace M := by
    refine ⟨?_⟩
    have := isCompact_univ.image H.continuous
    rwa [Set.image_univ, H.surjective.range_eq] at this
  refine ⟨hcpt, ?_, ?_⟩
  · have hm : IsOpen ((IsLocalRing.maximalIdeal O : Ideal O) : Set O) := by
      have := (isAdic_iff.mp hadic).1 1
      simpa using this
    let S : Set (Module.Free.ChooseBasisIndex O M → O) :=
      ⋂ i, (fun v => v i) ⁻¹' ((IsLocalRing.maximalIdeal O : Ideal O) : Set O)
    have hS : IsOpen S := isOpen_iInter_of_finite fun i => hm.preimage (continuous_apply i)
    have heq : (LinearMap.range (LinearMap.lsmul O M ϖ) : Set M) = H '' S := by
      ext m
      simp only [SetLike.mem_coe, LinearMap.mem_range, LinearMap.lsmul_apply, S,
        Set.mem_image, Set.mem_iInter, Set.mem_preimage, hϖ.maximalIdeal_eq,
        Ideal.mem_span_singleton', hH]
      constructor
      · rintro ⟨x, rfl⟩
        refine ⟨b.equivFun (ϖ • x), fun i => ⟨b.equivFun x i, ?_⟩, by simp⟩
        simp [mul_comm]
      · rintro ⟨v, hv, rfl⟩
        choose c hc using hv
        refine ⟨b.equivFun.symm c, ?_⟩
        rw [← LinearEquiv.map_smul]
        congr 1
        funext i
        simp [← hc i, mul_comm]
    rw [heq]
    exact H.isOpenMap S hS
  · refine (continuous_const_smul ϖ).isClosedEmbedding ?_
    exact smul_right_injective M hϖ.ne_zero

end GlobalTheory
end
