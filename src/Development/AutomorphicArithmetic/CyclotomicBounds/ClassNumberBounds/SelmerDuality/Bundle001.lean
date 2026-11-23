module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Valuation.ValuationRing
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.RingTheory.SimpleModule.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace KStar.Selmer

open Matrix Module

variable {N : ℕ} [NeZero N] {M M' : Type*} [AddCommGroup M] [Module (ZMod N) M] [AddCommGroup M']
  [Module (ZMod N) M']

private theorem zmod_dbl_ann (d y : ZMod N) (h : ∀ r : ZMod N, r * d = 0 → r * y = 0) :
    ∃ c : ZMod N, y = c * d := by
  obtain ⟨a, rfl⟩ := ZMod.natCast_zmod_surjective d
  obtain ⟨b, rfl⟩ := ZMod.natCast_zmod_surjective y
  obtain ⟨m, hm⟩ := Nat.gcd_dvd_right a N
  obtain ⟨a', ha'⟩ := Nat.gcd_dvd_left a N
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exact absurd (by rw [hm, h0, mul_zero]) (NeZero.ne N)
    · exact h0
  have h1 : (m : ZMod N) * a = 0 := by
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    refine ⟨a', ?_⟩
    calc m * a = m * (a.gcd N * a') := by rw [← ha']
      _ = (a.gcd N * m) * a' := by ring
      _ = N * a' := by rw [← hm]
  have h2 := h _ h1
  rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h2
  have h3 : a.gcd N * m ∣ b * m := by rw [← hm, mul_comm]; exact h2
  obtain ⟨k, hk⟩ := Nat.dvd_of_mul_dvd_mul_right hm0 h3
  have h4 : ((a.gcd N : ℕ) : ZMod N) = (a : ZMod N) * ((Nat.gcdA a N : ℤ) : ZMod N) := by
    have := congrArg (fun t : ℤ => (t : ZMod N)) (Nat.gcd_eq_gcd_ab a N)
    simpa using this
  refine ⟨((Nat.gcdA a N : ℤ) : ZMod N) * k, ?_⟩
  rw [hk, Nat.cast_mul, h4]
  ring

omit [NeZero N] in
private theorem zmod_ideal_gen (I : Ideal (ZMod N)) :
    ∃ d ∈ I, ∀ x ∈ I, ∃ r : ZMod N, x = r * d := by
  have : IsPrincipalIdealRing (ZMod N) :=
    IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod N)) (ZMod.ringHom_surjective _)
  obtain ⟨d, hd⟩ := (IsPrincipalIdealRing.principal I).principal
  refine ⟨d, hd ▸ Submodule.mem_span_singleton_self d, fun x hx => ?_⟩
  rw [hd, Submodule.mem_span_singleton] at hx
  obtain ⟨r, rfl⟩ := hx
  exact ⟨r, rfl⟩

theorem zmod_baer : Module.Baer (ZMod N) (ZMod N) := by
  intro I g
  obtain ⟨d, hd, hI⟩ := zmod_ideal_gen I
  obtain ⟨c, hc⟩ := zmod_dbl_ann d (g ⟨d, hd⟩) (fun r hr => by
    have : r • (⟨d, hd⟩ : I) = 0 := Subtype.ext hr
    rw [← smul_eq_mul, ← map_smul, this, map_zero])
  refine ⟨LinearMap.toSpanSingleton _ _ c, fun x hx => ?_⟩
  obtain ⟨r, rfl⟩ := hI x hx
  have : (⟨r * d, hx⟩ : I) = r • (⟨d, hd⟩ : I) := rfl
  rw [this, map_smul, hc, LinearMap.toSpanSingleton_apply, smul_eq_mul, smul_eq_mul]
  ring

private theorem zmod_extend {A B : Type*} [AddCommGroup A] [Module (ZMod N) A] [AddCommGroup B]
    [Module (ZMod N) B] (φ : A →ₗ[ZMod N] B) (c : A →ₗ[ZMod N] ZMod N)
    (h : ∀ a, φ a = 0 → c a = 0) : ∃ t : B →ₗ[ZMod N] ZMod N, ∀ a, t (φ a) = c a := by
  obtain ⟨t, ht⟩ := (zmod_baer (N := N)).extension_property
    ((LinearMap.ker φ).liftQ φ le_rfl)
    (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl))
    ((LinearMap.ker φ).liftQ c (fun a ha => h a ha))
  refine ⟨t, fun a => ?_⟩
  exact LinearMap.congr_fun ht (Submodule.Quotient.mk a)

theorem exists_form_ne_zero (I : Submodule (ZMod N) M) {z : M} (hz : z ∉ I) :
    ∃ f : M →ₗ[ZMod N] ZMod N, (∀ x ∈ I, f x = 0) ∧ f z ≠ 0 := by
  obtain ⟨d, hd, hI⟩ :=
    zmod_ideal_gen (LinearMap.ker (LinearMap.toSpanSingleton (ZMod N) (M ⧸ I) (I.mkQ z)))
  have hw : ∃ w : ZMod N, w * d = 0 ∧ w ≠ 0 := by
    by_contra hne
    push Not at hne
    obtain ⟨c, hc⟩ := zmod_dbl_ann d 1 (fun r hr => by rw [hne r hr, zero_mul])
    have h0 : d • I.mkQ z = 0 := hd
    have h1 : I.mkQ z = 0 := by
      rw [← one_smul (ZMod N) (I.mkQ z), hc, mul_smul, h0, smul_zero]
    exact hz (by simpa using h1)
  obtain ⟨w, hw, hw0⟩ := hw
  obtain ⟨t, ht⟩ := zmod_extend (LinearMap.toSpanSingleton (ZMod N) (M ⧸ I) (I.mkQ z))
    (LinearMap.toSpanSingleton (ZMod N) (ZMod N) w) (fun a ha => by
      obtain ⟨r, rfl⟩ := hI a ha
      rw [LinearMap.toSpanSingleton_apply, smul_eq_mul, mul_assoc, mul_comm d w, hw, mul_zero])
  refine ⟨t ∘ₗ I.mkQ, fun x hx => ?_, ?_⟩
  · have : I.mkQ x = 0 := by simpa using hx
    rw [LinearMap.comp_apply, this, map_zero]
  · have := ht 1
    rw [LinearMap.toSpanSingleton_apply, LinearMap.toSpanSingleton_apply, one_smul, one_smul] at this
    rw [LinearMap.comp_apply, this]
    exact hw0

end KStar.Selmer
end

section

namespace KStar.Selmer

open Matrix Module

variable {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [Fintype n]

private theorem exists_annihilator_of_maximal [Finite R] (p : Ideal R) (hp : p.IsMaximal) :
    ∃ a : R, a ≠ 0 ∧ ∀ x ∈ p, x * a = 0 := by
  have hfin : Finite (Ideal R) := Finite.of_injective _ SetLike.coe_injective
  obtain ⟨I, hI, hmin⟩ := (wellFounded_lt (α := Ideal R)).has_min
    {I : Ideal R | ∀ t : R, (∀ x ∈ I, t * x = 0) → t ∈ p}
    ⟨⊤, fun t ht => by
      have : t = 0 := by simpa using ht 1 trivial
      simp [this]⟩
  by_cases h : ∀ t : R, (∀ x ∈ p • I, t * x = 0) → t ∈ p
  · exfalso
    have hle : p • I ≤ I := Submodule.smul_le_right
    have heq : p • I = I := by
      by_contra hne
      exact hmin _ h (lt_of_le_of_ne hle hne)
    obtain ⟨e, he1, he⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul p I
      (IsNoetherian.noetherian I) heq.ge
    have hep : e ∈ p := hI e he
    have h1 : (1 : R) ∈ p := by simpa using p.sub_mem hep he1
    exact hp.ne_top ((Ideal.eq_top_iff_one p).2 h1)
  · push Not at h
    obtain ⟨t, ht, htp⟩ := h
    have h2 : ¬ ∀ x ∈ I, t * x = 0 := fun h => htp (hI t h)
    push Not at h2
    obtain ⟨b, hb, hb0⟩ := h2
    refine ⟨t * b, hb0, fun x hx => ?_⟩
    have := ht (x • b) (Submodule.smul_mem_smul hx hb)
    rw [← this, smul_eq_mul]
    ring

private theorem finite_module_dual_of_finite [Finite R] (M : Type*) [AddCommGroup M] [Module R M] [Finite M] :
    Finite (Module.Dual R M) :=
  Finite.of_injective (fun f : Module.Dual R M => (f : M → R)) DFunLike.coe_injective

private theorem card_dual_mul_quotient (hR : Module.Baer R R) {M : Type*} [AddCommGroup M] [Module R M]
    (N : Submodule R M) : Nat.card (Module.Dual R M) =
      Nat.card (Module.Dual R (M ⧸ N)) * Nat.card (Module.Dual R N) := by
  have hs : Function.Surjective N.dualRestrict := fun g =>
    hR.extension_property N.subtype N.injective_subtype g
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker N.dualRestrict),
    Nat.card_congr (N.dualRestrict.quotKerEquivOfSurjective hs).toEquiv,
    Submodule.dualRestrict_ker_eq_dualAnnihilator,
    Nat.card_congr N.dualQuotEquivDualAnnihilator.toEquiv]

private theorem card_le_card_dual_of_simple [Finite R] (M : Type*) [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] : Nat.card M ≤ Nat.card (Module.Dual R M) := by
  obtain ⟨p, hp, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 ‹IsSimpleModule R M›
  rw [Nat.card_congr e.toEquiv, ← Nat.card_congr e.dualMap.toEquiv]
  obtain ⟨a, ha, hpa⟩ := exists_annihilator_of_maximal p hp
  have hle : p ≤ LinearMap.ker (LinearMap.toSpanSingleton R R a) := fun x hx => hpa x hx
  have hge : LinearMap.ker (LinearMap.toSpanSingleton R R a) ≤ p := by
    refine (hp.eq_of_le ?_ hle).ge
    intro h
    have : (1 : R) ∈ LinearMap.ker (LinearMap.toSpanSingleton R R a) := h ▸ trivial
    exact ha (by simpa using this)
  let ι : (R ⧸ p) →ₗ[R] R := Submodule.liftQ p (LinearMap.toSpanSingleton R R a) hle
  have hι : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hge
  have : Finite (R ⧸ p) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  have := finite_module_dual_of_finite (R := R) (R ⧸ p)
  refine Nat.card_le_card_of_injective
    (fun y : R ⧸ p => (ι ∘ₗ LinearMap.mulLeft R y : Module.Dual R (R ⧸ p))) ?_
  intro y z hyz
  simpa using hι (LinearMap.congr_fun hyz 1)

private theorem card_le_card_dual [Finite R] (hR : Module.Baer R R) (k : ℕ) :
    ∀ (M : Type*) [AddCommGroup M] [Module R M] [Finite M], Nat.card M = k →
      Nat.card M ≤ Nat.card (Module.Dual R M) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro M _ _ _ hk
    have := finite_module_dual_of_finite (R := R) M
    rcases subsingleton_or_nontrivial M with hM | hM
    · rw [Nat.card_unique]
      exact Nat.card_pos
    by_cases h : ∀ N : Submodule R M, N = ⊥ ∨ N = ⊤
    · have : IsSimpleModule R M := { eq_bot_or_eq_top := h }
      exact card_le_card_dual_of_simple M
    push Not at h
    obtain ⟨N, h0, h1⟩ := h
    have hq : Finite (M ⧸ N) := Finite.of_surjective _ N.mkQ_surjective
    have hN : Nontrivial N := Submodule.nontrivial_iff_ne_bot.2 h0
    have hQ : Nontrivial (M ⧸ N) := Submodule.Quotient.nontrivial_iff.2 h1
    have a1 : 1 < Nat.card N := Finite.one_lt_card
    have a2 : 1 < Nat.card (M ⧸ N) := Finite.one_lt_card
    have hc := Submodule.card_eq_card_quotient_mul_card N
    have b1 := ih (Nat.card N) (by rw [← hk, hc]; nlinarith) N rfl
    have b2 := ih (Nat.card (M ⧸ N)) (by rw [← hk, hc]; nlinarith) (M ⧸ N) rfl
    rw [card_dual_mul_quotient hR N, hc, mul_comm]
    exact Nat.mul_le_mul b2 b1

theorem card_dual_of_baer [Finite R] (hR : Module.Baer R R) (M : Type*) [AddCommGroup M]
    [Module R M] [Finite M] : Nat.card (Module.Dual R M) = Nat.card M := by
  classical
  refine le_antisymm ?_ (card_le_card_dual hR _ M rfl)
  have := Fintype.ofFinite M
  let g : (M → R) →ₗ[R] M := Fintype.linearCombination R id
  have hg : Function.Surjective g := fun x => ⟨Pi.single x 1, by simp [g]⟩
  have e := g.quotKerEquivOfSurjective hg
  have h1 := card_dual_mul_quotient hR (LinearMap.ker g)
  rw [← Nat.card_congr (dotProductEquiv R M).toEquiv,
    Submodule.card_eq_card_quotient_mul_card (LinearMap.ker g), Nat.card_congr e.toEquiv,
    ← Nat.card_congr e.dualMap.toEquiv, mul_comm] at h1
  have h2 := card_le_card_dual hR _ (LinearMap.ker g) rfl
  have h3 : 0 < Nat.card (LinearMap.ker g) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ h3
  rw [h1]
  exact Nat.mul_le_mul_left _ h2

end KStar.Selmer
end

section

namespace KStar.Selmer

open Matrix Module

section Minors

variable {R : Type*} [CommRing R] {m n : Type*}

def minorIdeal (k : ℕ) (A : Matrix m n R) : Ideal R :=
  Ideal.span {x | ∃ (r : Fin k → m) (c : Fin k → n), x = (A.submatrix r c).det}

end Minors

section Complex

variable {R : Type*} [CommRing R] {m n m' n' : Type*}

def coefMap [Fintype n] (Φ : Matrix m n R) (M : Type*) [AddCommGroup M] [Module R M] :
    (n → M) →ₗ[R] (m → M) :=
  LinearMap.pi fun i => ∑ j, Φ i j • LinearMap.proj j

theorem coefMap_apply [Fintype n] (Φ : Matrix m n R) (M : Type*) [AddCommGroup M] [Module R M]
    (v : n → M) (i : m) : coefMap Φ M v i = ∑ j, Φ i j • v j := by
  simp [coefMap, LinearMap.sum_apply]

def H1c [Fintype n] (Φ : Matrix m n R) (M : Type*) [AddCommGroup M] [Module R M] :
    Submodule R (n → M) :=
  LinearMap.ker (coefMap Φ M)

abbrev H2 [Fintype n] (Φ : Matrix m n R) : Type _ :=
  (m → R) ⧸ LinearMap.range Φ.mulVecLin

def IsMinimal (Φ : Matrix m n R) : Prop :=
  ∀ i j, Φ i j ∈ Ideal.jacobson (⊥ : Ideal R)

def IsHtpyEquiv [Fintype m] [Fintype n] [Fintype m'] [Fintype n'] [DecidableEq m] [DecidableEq n]
    [DecidableEq m'] [DecidableEq n'] (Φ : Matrix m n R) (Φ' : Matrix m' n' R)
    (f₁ : Matrix n' n R) (f₂ : Matrix m' m R) : Prop :=
  Φ' * f₁ = f₂ * Φ ∧ ∃ (g₁ : Matrix n n' R) (g₂ : Matrix m m' R) (h : Matrix n m R)
    (h' : Matrix n' m' R), Φ * g₁ = g₂ * Φ' ∧ g₁ * f₁ = 1 + h * Φ ∧ g₂ * f₂ = 1 + Φ * h ∧
      f₁ * g₁ = 1 + h' * Φ' ∧ f₂ * g₂ = 1 + Φ' * h'

end Complex

section Special

variable {Λ O : Type*} [CommRing Λ] [CommRing O] {m n : Type*}

abbrev FracMod (O K : Type*) [CommRing O] [Field K] [Algebra O K] : Type _ :=
  K ⧸ (1 : Submodule O K)

end Special

section Koszul

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

end Koszul

section Lagrangian

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

def IsHalfIsotropic (B : LinearMap.BilinForm k V) (L : Submodule k V) : Prop :=
  (∀ x ∈ L, ∀ y ∈ L, B x y = 0) ∧ 2 * finrank k L = finrank k V

variable {H H' : Type*} [AddCommGroup H] [Module k H] [AddCommGroup H'] [Module k H']

def hyperbolic (β : H →ₗ[k] H' →ₗ[k] k) : LinearMap.BilinForm k (H × H') :=
  β.compl₁₂ (LinearMap.fst k H H') (LinearMap.snd k H H') +
    β.flip.compl₁₂ (LinearMap.snd k H H') (LinearMap.fst k H H')

theorem hyperbolic_apply (β : H →ₗ[k] H' →ₗ[k] k) (v w : H × H') :
    hyperbolic β v w = β v.1 w.2 + β w.1 v.2 := by
  simp [hyperbolic]

end Lagrangian

end KStar.Selmer
end

section

namespace KStar.Selmer

open Matrix Module

variable {R : Type*} [CommRing R]

private def HasSmith {a : ℕ} (Φ : Matrix (Fin a) (Fin a) R) : Prop :=
  ∃ (U V : Matrix (Fin a) (Fin a) R) (d : Fin a → R), IsUnit U.det ∧ IsUnit V.det ∧
      Φ = U * diagonal d * V ∧ ∀ i j, i ≤ j → d i ∣ d j

private theorem HasSmith.smul {a : ℕ} {Φ : Matrix (Fin a) (Fin a) R} (h : HasSmith Φ) (x : R) :
    HasSmith (x • Φ) := by
  obtain ⟨U, V, d, hU, hV, rfl, hd⟩ := h
  refine ⟨U, V, x • d, hU, hV, ?_, fun i j hij => ?_⟩
  · rw [diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
  · exact mul_dvd_mul_left x (hd i j hij)

private theorem HasSmith.perm {a : ℕ} {Φ : Matrix (Fin a) (Fin a) R} (h : HasSmith Φ)
    (σ τ : Equiv.Perm (Fin a)) : HasSmith (Φ.submatrix σ τ) := by
  obtain ⟨U, V, d, hU, hV, rfl, hd⟩ := h
  refine ⟨U.submatrix σ id, V.submatrix id τ, d, ?_, ?_, ?_, hd⟩
  · rw [det_permute]
    exact ((Equiv.Perm.sign σ).isUnit.map (Int.castRingHom R)).mul hU
  · rw [det_permute']
    exact ((Equiv.Perm.sign τ).isUnit.map (Int.castRingHom R)).mul hV
  · ext i j
    simp [Matrix.mul_apply]

private def consEquiv (a : ℕ) : Fin (a + 1) ≃ Unit ⊕ Fin a where
  toFun := Fin.cases (Sum.inl ()) Sum.inr
  invFun := Sum.elim (fun _ => 0) Fin.succ
  left_inv i := by cases i using Fin.cases <;> simp
  right_inv i := by rcases i with _ | i <;> simp

private theorem hasSmith_of_one {a : ℕ} (ih : ∀ Ψ : Matrix (Fin a) (Fin a) R, HasSmith Ψ)
    (M : Matrix (Fin (a + 1)) (Fin (a + 1)) R) (h : M 0 0 = 1) : HasSmith M := by
  set e := consEquiv a with he
  set N := M.submatrix e.symm e.symm with hN
  have h11 : N.toBlocks₁₁ = 1 := by
    ext i j
    have : N (Sum.inl i) (Sum.inl j) = M 0 0 := rfl
    simp [toBlocks₁₁, this, h]
  obtain ⟨U, V, d, hU, hV, hΨ, hd⟩ := ih (N.toBlocks₂₂ - N.toBlocks₂₁ * N.toBlocks₁₂)
  have key : N = fromBlocks 1 0 N.toBlocks₂₁ U * diagonal (Sum.elim (fun _ => 1) d) *
      fromBlocks 1 N.toBlocks₁₂ 0 V := by
    rw [← fromBlocks_diagonal, fromBlocks_multiply, fromBlocks_multiply]
    conv_lhs => rw [← fromBlocks_toBlocks N, h11]
    simp [← hΨ]
  refine ⟨(fromBlocks 1 0 N.toBlocks₂₁ U).submatrix e e,
    (fromBlocks 1 N.toBlocks₁₂ 0 V).submatrix e e, Sum.elim (fun _ => 1) d ∘ e, ?_, ?_, ?_, ?_⟩
  · rw [det_submatrix_equiv_self, det_fromBlocks_zero₁₂]; simpa using hU
  · rw [det_submatrix_equiv_self, det_fromBlocks_zero₂₁]; simpa using hV
  · rw [← submatrix_diagonal_equiv, submatrix_mul_equiv, submatrix_mul_equiv, ← key, hN]
    simp
  · intro i j hij
    cases i using Fin.cases with
    | zero => exact one_dvd _
    | succ i =>
      cases j using Fin.cases with
      | zero => exact absurd hij (by simp)
      | succ j => exact hd i j (by simpa using hij)

private theorem exists_dvd_all [PreValuationRing R] {ι : Type*} (f : ι → R) (s : Finset ι)
    (hs : s.Nonempty) : ∃ p ∈ s, ∀ i ∈ s, f p ∣ f i := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => exact ⟨a, by simp, by simp⟩
  | cons a s ha hs ih =>
    obtain ⟨p, hp, h⟩ := ih
    obtain ⟨c, hc | hc⟩ := PreValuationRing.cond (f a) (f p)
    · refine ⟨a, by simp, fun i hi => ?_⟩
      rcases Finset.mem_cons.1 hi with rfl | hi
      · exact dvd_rfl
      · exact (Dvd.intro c hc).trans (h i hi)
    · refine ⟨p, by simp [hp], fun i hi => ?_⟩
      rcases Finset.mem_cons.1 hi with rfl | hi
      · exact Dvd.intro c hc
      · exact h i hi

private theorem hasSmith_all [PreValuationRing R] (a : ℕ) (Φ : Matrix (Fin a) (Fin a) R) :
    HasSmith Φ := by
  classical
  induction a with
  | zero =>
    exact ⟨1, 1, fun _ => 1, by simp, by simp, Subsingleton.elim _ _, fun _ _ _ => dvd_rfl⟩
  | succ a ih =>
    obtain ⟨⟨p, q⟩, -, h⟩ := exists_dvd_all (fun ij : Fin (a + 1) × Fin (a + 1) => Φ ij.1 ij.2)
      Finset.univ Finset.univ_nonempty
    have h' : ∀ i j, ∃ c, Φ i j = Φ p q * c ∧ (i = p → j = q → c = 1) := by
      intro i j
      by_cases hij : i = p ∧ j = q
      · obtain ⟨rfl, rfl⟩ := hij
        exact ⟨1, by simp, by simp⟩
      · obtain ⟨c, hc⟩ := h (i, j) (Finset.mem_univ _)
        exact ⟨c, hc, fun h1 h2 => absurd ⟨h1, h2⟩ hij⟩
    choose M hM hM1 using h'
    have h1 : HasSmith ((Matrix.of M).submatrix (Equiv.swap 0 p) (Equiv.swap 0 q)) :=
      hasSmith_of_one ih _ (by simp [hM1 p q rfl rfl])
    have h2 := (h1.perm (Equiv.swap 0 p) (Equiv.swap 0 q)).smul (Φ p q)
    convert h2 using 1
    ext i j
    simpa using hM i j

theorem exists_smith [PreValuationRing R] (a : ℕ) (Φ : Matrix (Fin a) (Fin a) R) :
    ∃ (U V : Matrix (Fin a) (Fin a) R) (d : Fin a → R), IsUnit U.det ∧ IsUnit V.det ∧
      Φ = U * diagonal d * V ∧ ∀ i j, i ≤ j → d i ∣ d j :=
  hasSmith_all a Φ

end KStar.Selmer
end
