module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
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
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Filtration
public import Mathlib.Algebra.Exact.Basic

@[expose] public section

section

namespace GlobalTheory.FixedPointApproximation

noncomputable def approx {B : Type} [CommRing B] (q : B) (σ : B →+* B) (w : B) : ℕ → B
  | 0 => 0
  | n + 1 => -w + q * σ (approx q σ w n)

theorem approx_step {B : Type} [CommRing B] (q : B) (σ : B →+* B) (hq : σ q = q) (w : B) (n : ℕ) :
    q ^ n ∣ approx q σ w (n + 1) - approx q σ w n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨σ t, ?_⟩
    have e : approx q σ w (n + 1 + 1) - approx q σ w (n + 1) =
        q * σ (approx q σ w (n + 1) - approx q σ w n) := by
      rw [map_sub]
      show -w + q * σ (approx q σ w (n + 1)) - (-w + q * σ (approx q σ w n)) = _
      ring
    rw [e, ht, map_mul, map_pow, hq]
    ring

theorem approx_dvd {B : Type} [CommRing B] (q : B) (σ : B →+* B) (hq : σ q = q) (w : B)
    (m n : ℕ) (h : m ≤ n) : q ^ m ∣ approx q σ w m - approx q σ w n := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    have h2 : q ^ m ∣ approx q σ w (n + 1) - approx q σ w n :=
      (pow_dvd_pow q hmn).trans (approx_step q σ hq w n)
    have e : approx q σ w m - approx q σ w (n + 1) =
        (approx q σ w m - approx q σ w n) - (approx q σ w (n + 1) - approx q σ w n) := by ring
    rw [e]
    exact dvd_sub ih h2

theorem smodEq_iff {B : Type} [CommRing B] (q : B) (n : ℕ) (x y : B) :
    x ≡ y [SMOD ((Ideal.span {q}) ^ n • ⊤ : Submodule B B)] ↔ q ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

theorem exists_fixed {B : Type} [inst : CommRing B] (q : B)
    [h : IsAdicComplete (Ideal.span {q}) B] (σ : B →+* B) (hq : σ q = q) (w : B) :
    ∃ c : B, c = -w + q * σ c := by
  obtain ⟨c, hc⟩ := h.toIsPrecomplete.prec (f := approx q σ w) fun {m n} hmn =>
    (smodEq_iff q m _ _).mpr (approx_dvd q σ hq w m n hmn)
  refine ⟨c, ?_⟩
  have hd : ∀ n, q ^ n ∣ c - (-w + q * σ c) := by
    intro n
    have h1 : q ^ n ∣ approx q σ w n - c := (smodEq_iff q n _ _).mp (hc n)
    have h2 : q ^ (n + 1) ∣ approx q σ w (n + 1) - c := (smodEq_iff q (n + 1) _ _).mp (hc (n + 1))
    obtain ⟨t, ht⟩ := h1
    have e : c - (-w + q * σ c) = -(approx q σ w (n + 1) - c) + q * σ (approx q σ w n - c) := by
      rw [map_sub]
      show _ = -((-w + q * σ (approx q σ w n)) - c) + q * (σ (approx q σ w n) - σ c)
      ring
    rw [e, ht, map_mul, map_pow, hq]
    exact dvd_add (dvd_neg.mpr ((pow_dvd_pow q (Nat.le_succ n)).trans h2)) ⟨q * σ t, by ring⟩
  have h0 := h.toIsHausdorff.haus (c - (-w + q * σ c)) fun n =>
    (smodEq_iff q n _ _).mpr (by simpa using hd n)
  exact sub_eq_zero.mp h0

end GlobalTheory.FixedPointApproximation
end

section

namespace GlobalTheory.InfimumSupPowerIdeal

theorem iInf_sup_pow_eq (C : Type) [CommRing C] (J : Ideal C) (hJ : IsAdicComplete J C)
    (u : ℕ → Ideal C) (hu : ∀ e : ℕ, u e = u (e + 1) ⊔ J ^ (e + 1)) (e : ℕ) :
    (⨅ l : ℕ, u l) ⊔ J ^ (e + 1) = u e := by

  have hsm : ∀ m : ℕ, (J ^ m • ⊤ : Submodule C C) = J ^ m := fun m => by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]

  have hanti : Antitone u := antitone_nat_of_succ_le fun k => by
    rw [hu k]; exact le_sup_left
  have hJle : ∀ k, J ^ (k + 1) ≤ u k := fun k => by
    rw [hu k]; exact le_sup_right
  apply le_antisymm
  · exact sup_le (iInf_le u e) (hJle e)
  · intro x hx

    have step : ∀ (k : ℕ) (a : u k), ∃ b : u (k + 1), (a : C) - b ∈ J ^ (k + 1) := by
      intro k a
      have ha : (a : C) ∈ u (k + 1) ⊔ J ^ (k + 1) := by rw [← hu k]; exact a.2
      obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.1 ha
      refine ⟨⟨b, hb⟩, ?_⟩
      have : (a : C) - b = c := by rw [← hbc]; ring
      rw [this]; exact hc
    choose g hg using step
    let s : ∀ n : ℕ, u (e + n) := fun n =>
      Nat.rec (motive := fun n => ↥(u (e + n))) ⟨x, hx⟩ (fun n a => g (e + n) a) n
    have hs0 : (s 0 : C) = x := rfl
    have hss : ∀ n, (s n : C) - s (n + 1) ∈ J ^ (e + n + 1) := fun n => hg (e + n) (s n)
    have hchain : ∀ m n, m ≤ n → (s m : C) - s n ∈ J ^ (e + m + 1) := by
      intro m n hmn
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ n hmn ih =>
        have h1 : (s n : C) - s (n + 1) ∈ J ^ (e + m + 1) :=
          Ideal.pow_le_pow_right (by omega) (hss n)
        have hsum : (s m : C) - s (n + 1) = ((s m : C) - s n) + ((s n : C) - s (n + 1)) := by ring
        rw [hsum]; exact add_mem ih h1

    obtain ⟨L, hL⟩ := IsPrecomplete.prec hJ.toIsPrecomplete (f := fun n => (s n : C)) (by
      intro m n hmn
      rw [hsm, SModEq.sub_mem]
      exact Ideal.pow_le_pow_right (by omega) (hchain m n hmn))
    have hL' : ∀ n, (s n : C) - L ∈ J ^ n := fun n => by
      have h := hL n
      rw [hsm, SModEq.sub_mem] at h
      exact h

    have hLu : L ∈ ⨅ l, u l := by
      rw [Submodule.mem_iInf]
      intro l
      have h1 : (s (l + 1) : C) ∈ u l := hanti (by omega : l ≤ e + (l + 1)) (s (l + 1)).2
      have h2 : (s (l + 1) : C) - L ∈ u l := hJle l (hL' (l + 1))
      have h3 := Submodule.sub_mem _ h1 h2
      rwa [sub_sub_cancel] at h3

    have hxL : x - L ∈ J ^ (e + 1) := by
      have h1 : (s 0 : C) - s (e + 1) ∈ J ^ (e + 1) := by simpa using hchain 0 (e + 1) (by omega)
      have hsum : x - L = ((s 0 : C) - s (e + 1)) + ((s (e + 1) : C) - L) := by rw [hs0]; ring
      rw [hsum]; exact add_mem h1 (hL' (e + 1))
    exact Submodule.mem_sup.2 ⟨L, hLu, x - L, hxL, by ring⟩

end GlobalTheory.InfimumSupPowerIdeal
end

section

namespace GlobalTheory

theorem isAdicComplete_of_le_of_isNoetherianRing (R : Type) [CommRing R] [IsNoetherianRing R]
    (I J : Ideal R) (hIJ : I ≤ J) (hJ : IsAdicComplete J R) : IsAdicComplete I R := by
  have hle : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R R) ≤ J ^ n • ⊤ := fun n =>
    Submodule.smul_mono_left (Ideal.pow_right_mono hIJ n)
  have hH : IsHausdorff I R :=
    ⟨fun x hx => hJ.toIsHausdorff.haus x fun n => (hx n).mono (hle n)⟩
  have hP : IsPrecomplete I R := by
    refine ⟨fun f hf => ?_⟩
    obtain ⟨L, hL⟩ := hJ.toIsPrecomplete.prec (f := f) fun {m n} h => (hf h).mono (hle m)
    refine ⟨L, fun n => ?_⟩
    set N : Submodule R R := I ^ n • ⊤ with hN
    have hK : (⨅ m : ℕ, J ^ m • ⊤ : Submodule R (R ⧸ N)) = ⊥ :=
      Ideal.iInf_pow_smul_eq_bot_of_le_jacobson J (by
        simpa only [Ideal.jacobson_bot] using IsAdicComplete.le_jacobson_bot J)
    rw [SModEq.sub_mem, ← Submodule.Quotient.mk_eq_zero, ← Submodule.mem_bot R, ← hK,
      Submodule.mem_iInf]
    intro m
    have h1 : f n - f (max n m) ∈ N := SModEq.sub_mem.1 (hf (le_max_left n m))
    have h2 : f (max n m) - L ∈ (J ^ m • ⊤ : Submodule R R) :=
      Submodule.smul_mono_left (Ideal.pow_le_pow_right (le_max_right n m))
        (SModEq.sub_mem.1 (hL (max n m)))
    have h3 : N.mkQ (f (max n m) - L) ∈ (J ^ m • ⊤ : Submodule R (R ⧸ N)) := by
      have := Submodule.mem_map_of_mem (f := N.mkQ) h2
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    have h4 : (Submodule.Quotient.mk (f n - L) : R ⧸ N) = N.mkQ (f (max n m) - L) := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.eq]
      convert h1 using 1
      ring
    rw [h4]
    exact h3
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }

end GlobalTheory
end

section

namespace GlobalTheory.LinearMapDifferenceFormula

open AdicCompletion

theorem map_sub_apply {A : Type} [CommRing A] (J : Ideal A) {M P : Type} [AddCommGroup M] [Module A M]
    [AddCommGroup P] [Module A P] (h k : M →ₗ[A] P) (y : AdicCompletion J M) :
    AdicCompletion.map J (h - k) y = AdicCompletion.map J h y - AdicCompletion.map J k y := by
  induction y using AdicCompletion.induction_on with
  | h a =>
    ext n
    simp

theorem main : ∀ (A : Type) [inst : CommRing A] [IsNoetherianRing A] (J : Ideal A) (N M : Type) [inst_2 : AddCommGroup N] [inst_3 : Module A N] [inst_4 : AddCommGroup M] [inst_5 : Module A M] [Module.Finite A M] (f : N →ₗ[A] M) (Γ : Type) [Finite Γ] (g : Γ → M →ₗ[A] M), Function.Injective (⇑f : N → M) → (∀ (x : M), x ∈ LinearMap.range f ↔ ∀ (σ : Γ), (g σ : M → M) x = x) → Function.Injective (⇑(AdicCompletion.map J f) : AdicCompletion J N → AdicCompletion J M) ∧ ∀ (y : AdicCompletion J M), y ∈ LinearMap.range (AdicCompletion.map J f) ↔ ∀ (σ : Γ), (AdicCompletion.map J (g σ) : AdicCompletion J M → AdicCompletion J M) y = y := by
  intro A _ _ J N M _ _ _ _ _ f Γ _ g hf hfix
  classical
  haveI : Fintype Γ := Fintype.ofFinite Γ
  refine ⟨AdicCompletion.map_injective J hf, ?_⟩

  let φ : M →ₗ[A] (Γ → M) := LinearMap.pi (fun σ => g σ - LinearMap.id)
  let ψ : M →ₗ[A] LinearMap.range φ := φ.rangeRestrict
  have hψs : Function.Surjective ψ := LinearMap.surjective_rangeRestrict φ
  have hφ0 : ∀ x, φ x = 0 ↔ ∀ σ, g σ x = x := by
    intro x
    simp only [φ, funext_iff, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply,
      Pi.zero_apply, sub_eq_zero]
  have hex : Function.Exact f ψ := by
    intro x
    have : ψ x = 0 ↔ φ x = 0 := by
      simp [ψ, Subtype.ext_iff]
    rw [this, hφ0, ← hfix]
    rfl
  have hE := AdicCompletion.map_exact (I := J) hf hex hψs
  have hinj : Function.Injective (AdicCompletion.map J (LinearMap.range φ).subtype) :=
    AdicCompletion.map_injective J (Submodule.injective_subtype _)
  have hcomp : (LinearMap.range φ).subtype ∘ₗ ψ = φ := by
    ext x; simp [ψ]
  intro y
  rw [LinearMap.mem_range, ← Set.mem_range, ← hE y]
  have h1 : AdicCompletion.map J ψ y = 0 ↔ AdicCompletion.map J φ y = 0 := by
    have e : AdicCompletion.map J φ y = AdicCompletion.map J (LinearMap.range φ).subtype (AdicCompletion.map J ψ y) := by
      rw [AdicCompletion.map_comp_apply, hcomp]
    rw [e]
    constructor
    · intro h; rw [h, _root_.map_zero]
    · intro h; exact hinj (by rw [h, _root_.map_zero])
  rw [h1]
  have hpi : AdicCompletion.map J φ y = 0 ↔ ∀ σ, AdicCompletion.map J (LinearMap.proj σ) (AdicCompletion.map J φ y) = 0 := by
    constructor
    · intro h σ; rw [h, _root_.map_zero]
    · intro h
      apply (AdicCompletion.piEquivOfFintype J (fun _ : Γ => M)).injective
      rw [_root_.map_zero, AdicCompletion.piEquivOfFintype_apply]
      funext σ
      exact h σ
  rw [hpi]
  refine forall_congr' fun σ => ?_
  rw [AdicCompletion.map_comp_apply]
  have : (LinearMap.proj σ : (Γ → M) →ₗ[A] M) ∘ₗ φ = g σ - LinearMap.id := by
    ext x; simp [φ]
  rw [this, map_sub_apply, AdicCompletion.map_id, LinearMap.id_apply, sub_eq_zero]

end GlobalTheory.LinearMapDifferenceFormula
end

section

open IsLocalRing TensorProduct

namespace GlobalTheory.AdicSurj

open AdicCompletion

variable (B : Type) {A : Type} [CommRing A] [CommRing B] [Algebra A B] (J : Ideal A)

theorem mem_smul_top_iff (n : ℕ) (b : B) :
    b ∈ (J ^ n • ⊤ : Submodule A B) ↔ b ∈ (J.map (algebraMap A B)) ^ n := by
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow]

theorem pow_le_comap (n : ℕ) :
    J ^ n ≤ ((J.map (algebraMap A B)) ^ n).comap (algebraMap A B) := by
  rw [← Ideal.map_pow]; exact Ideal.le_comap_map

noncomputable def lev (n : ℕ) :
    AdicCompletion J A →+* B ⧸ (J.map (algebraMap A B)) ^ n :=
  (Ideal.quotientMap _ (algebraMap A B) (pow_le_comap B J n)).comp (evalₐ J n).toRingHom

theorem lev_mk (n : ℕ) (s : AdicCauchySequence J A) :
    lev B J n (AdicCompletion.mk J A s) = Ideal.Quotient.mk _ (algebraMap A B (s n)) := by
  simp [lev, evalₐ_mk, Ideal.quotientMap_mk]

theorem lev_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow _ hle).comp (lev B J n) = lev B J m := by
  ext x
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J A x
  have h1 := s.property hle
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  simp only [RingHom.comp_apply, lev_mk]
  rw [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.Quotient.eq, ← map_sub]
  have h3 : s n - s m ∈ J ^ m := by rw [← neg_sub]; exact neg_mem h1
  exact Ideal.mem_comap.mp (pow_le_comap B J m h3)

noncomputable def psi : AdicCompletion J A →+* AdicCompletion (J.map (algebraMap A B)) B :=
  AdicCompletion.liftRingHom _ (lev B J) (fun hle ↦ lev_compat B J hle)

theorem evalₐ_psi (n : ℕ) (x : AdicCompletion J A) :
    evalₐ _ n (psi B J x) = lev B J n x := by
  simp [psi]

theorem psi_algebraMap (a : A) :
    psi B J (algebraMap A (AdicCompletion J A) a) =
      algebraMap A (AdicCompletion (J.map (algebraMap A B)) B) a := by
  refine ext_evalₐ fun n ↦ ?_
  rw [evalₐ_psi, lev, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
    Ideal.Quotient.algebraMap_eq, Ideal.quotientMap_mk, AdicCompletion.algebraMap_apply, evalₐ_of]

theorem map_val_mk_eq_iff (s : AdicCauchySequence J A) (n : ℕ) (c : B) :
    (map J (Algebra.linearMap A B) (AdicCompletion.mk J A s)).val n = Submodule.Quotient.mk c ↔
      lev B J n (AdicCompletion.mk J A s) = Ideal.Quotient.mk _ c := by
  rw [map_val_apply, mk_apply_coe, lev_mk, Submodule.mkQ_apply, LinearMap.reduceModIdeal_apply,
    Submodule.Quotient.eq, Ideal.Quotient.eq, mem_smul_top_iff]
  rfl

theorem psi_surjective [IsNoetherianRing A] (hs : Function.Surjective (algebraMap A B)) :
    Function.Surjective (psi B J) := by
  intro y
  obtain ⟨t, rfl⟩ := AdicCompletion.mk_surjective _ _ y
  let t' : AdicCauchySequence J B := ⟨t.val, fun {m n} hmn ↦ by
    have h := t.property hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
    rw [SModEq.sub_mem, mem_smul_top_iff]; exact h⟩
  obtain ⟨x, hx⟩ := map_surjective J (f := Algebra.linearMap A B) hs (AdicCompletion.mk J _ t')
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J A x
  refine ⟨AdicCompletion.mk J A s, ext_evalₐ fun n ↦ ?_⟩
  rw [evalₐ_psi, evalₐ_mk]
  refine (map_val_mk_eq_iff B J s n (t n)).mp ?_
  rw [hx]; rfl

theorem ker_psi [IsNoetherianRing A] (hs : Function.Surjective (algebraMap A B)) :
    RingHom.ker (psi B J) =
      Ideal.map (algebraMap A (AdicCompletion J A)) (LinearMap.ker (Algebra.linearMap A B)) := by
  set q := LinearMap.ker (Algebra.linearMap A B)
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    have hz : map J (Algebra.linearMap A B) x = 0 := by
      obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J A x
      ext n
      have := (map_val_mk_eq_iff B J s n 0).mpr
        (by rw [← evalₐ_psi, hx, _root_.map_zero, _root_.map_zero])
      simpa using this
    obtain ⟨y, rfl⟩ := ((AdicCompletion.map_exact (I := J) (f := q.subtype) (g := Algebra.linearMap A B)
      Subtype.val_injective (LinearMap.exact_subtype_ker_map _) hs) x).mp hz
    obtain ⟨t, rfl⟩ := ofTensorProduct_surjective_of_finite J q y
    clear hx hz
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      rw [ofTensorProduct_tmul, map_smul, map_of, smul_eq_mul]
      have hm : (of J A) (q.subtype m) = algebraMap A (AdicCompletion J A) (m : A) := by
        rw [AdicCompletion.algebraMap_apply]; rfl
      rw [hm]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ m.2)
    | add a b ha hb => rw [map_add (f := _), map_add (f := _)]; exact add_mem ha hb
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, psi_algebraMap, AdicCompletion.algebraMap_apply]
    have : algebraMap A B a = 0 := LinearMap.mem_ker.mp ha
    rw [this, _root_.map_zero]

end GlobalTheory.AdicSurj

namespace GlobalTheory.AdicSurj

open AdicCompletion

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (J : Ideal A)

instance isScalarTower_adic :
    IsScalarTower A B (AdicCompletion (J.map (algebraMap A B)) B) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

noncomputable def psiₐ :
    AdicCompletion J A →ₐ[A] AdicCompletion (J.map (algebraMap A B)) B :=
  { psi B J with commutes' := psi_algebraMap B J }

noncomputable def theta :
    B ⊗[A] AdicCompletion J A →ₐ[B] AdicCompletion (J.map (algebraMap A B)) B :=
  Algebra.TensorProduct.lift (Algebra.ofId B _) (psiₐ J) fun _ _ ↦ Commute.all _ _

theorem theta_bijective [IsNoetherianRing A] (hs : Function.Surjective (algebraMap A B)) :
    Function.Bijective (theta (B := B) J) := by
  let e := RingHom.quotientKerEquivOfSurjective (psi_surjective B J hs)
  have hker : RingHom.ker (psi B J) ≤
      RingHom.ker (Algebra.TensorProduct.includeRight (R := A) (A := B)
        (B := AdicCompletion J A)).toRingHom := by
    rw [ker_psi B J hs, Ideal.map_le_iff_le_comap]
    intro a ha
    have h0 : algebraMap A B a = 0 := LinearMap.mem_ker.mp ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change (1 : B) ⊗ₜ[A] algebraMap A (AdicCompletion J A) a = 0
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, h0, zero_mul,
      TensorProduct.zero_tmul]
  let σ : AdicCompletion (J.map (algebraMap A B)) B →+* B ⊗[A] AdicCompletion J A :=
    (Ideal.Quotient.lift _ _ hker).comp e.symm.toRingHom
  have hσ : ∀ x, σ (psi B J x) = 1 ⊗ₜ[A] x := by
    intro x
    have : e.symm (psi B J x) = Ideal.Quotient.mk _ x := e.symm_apply_eq.mpr rfl
    simp only [σ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, this,
      Ideal.Quotient.lift_mk]
    rfl
  have hleft : ∀ t, σ (theta J t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
    | tmul b x =>
      obtain ⟨a, rfl⟩ := hs b
      rw [theta, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply,
        ← IsScalarTower.algebraMap_apply, ← psi_algebraMap B J a]
      change σ (psi B J _ * psi B J x) = _
      rw [← map_mul, hσ, ← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  refine ⟨Function.LeftInverse.injective hleft, fun y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := psi_surjective B J hs y
  refine ⟨1 ⊗ₜ[A] x, ?_⟩
  rw [theta, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

theorem tensor_ringEquiv [IsNoetherianRing A] (hs : Function.Surjective (algebraMap A B))
    (I : Ideal B) (hI : I = J.map (algebraMap A B)) (K : Type) [CommRing K] [Algebra B K] [Algebra A K]
    [IsScalarTower A B K] :
    Nonempty (AdicCompletion I B ⊗[B] K ≃+* AdicCompletion J A ⊗[A] K) := by
  subst hI
  let θ := AlgEquiv.ofBijective (theta (B := B) J) (theta_bijective J hs)
  exact ⟨(Algebra.TensorProduct.comm B _ K).toRingEquiv.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[B] K) θ.symm).toRingEquiv.trans
    ((Algebra.TensorProduct.cancelBaseChange A B B K (AdicCompletion J A)).toRingEquiv.trans
    (Algebra.TensorProduct.comm A K (AdicCompletion J A)).toRingEquiv))⟩

end GlobalTheory.AdicSurj

theorem GlobalTheory.adicCompletion_tensor_quotient_ringEquiv :
    ∀ (R₀ R K : Type) [CommRing R₀] [IsLocalRing R₀] [IsNoetherianRing R₀] [CommRing R] [IsLocalRing R]
      [Algebra R₀ R] [CommRing K] [Algebra R K] [Algebra R₀ K] [IsScalarTower R₀ R K],
      Function.Surjective (algebraMap R₀ R) →
        Nonempty (AdicCompletion (maximalIdeal R) R ⊗[R] K ≃+*
          AdicCompletion (maximalIdeal R₀) R₀ ⊗[R₀] K) := by
  intro R₀ R K _ _ _ _ _ _ _ _ _ _ hs
  have hk : RingHom.ker (algebraMap R₀ R) ≤ maximalIdeal R₀ :=
    le_maximalIdeal (RingHom.ker_ne_top _)
  have hmax : ((maximalIdeal R₀).map (algebraMap R₀ R)).IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (hf := hs) (H := maximalIdeal.isMaximal R₀) with h | h
    · exfalso
      have h1 : (1 : R) ∈ (maximalIdeal R₀).map (algebraMap R₀ R) := h ▸ Submodule.mem_top
      obtain ⟨a, ha, hfa⟩ := (Ideal.mem_map_iff_of_surjective _ hs).mp h1
      have h2 : 1 - a ∈ maximalIdeal R₀ := hk (by rw [RingHom.mem_ker, map_sub, hfa, map_one, sub_self])
      have h3 : (1 : R₀) ∈ maximalIdeal R₀ := by simpa using add_mem h2 ha
      exact (maximalIdeal.isMaximal R₀).ne_top ((Ideal.eq_top_iff_one _).mpr h3)
    · exact h
  exact GlobalTheory.AdicSurj.tensor_ringEquiv (maximalIdeal R₀) hs _ (eq_maximalIdeal hmax).symm K
end
