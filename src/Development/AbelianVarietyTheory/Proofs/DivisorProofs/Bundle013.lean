module

public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Basic.Finite.Defs
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieFaithful

open IsLocalRing

theorem map_sub_two_pow_mul_mem {R : Type} [CommRing R] (m : Ideal R) (φ : R →+* R)
    (h : ∀ x ∈ m, φ x - 2 * x ∈ m ^ 2) (n : ℕ) :
    ∀ y ∈ m ^ (n + 1), φ y - 2 ^ (n + 1) * y ∈ m ^ (n + 2) := by
  have hφ : ∀ x ∈ m, φ x ∈ m := fun x hx => by
    have h1 := Ideal.pow_le_self (two_ne_zero) (h x hx)
    have h2 := m.add_mem h1 (m.mul_mem_left 2 hx)
    simpa using h2
  induction n with
  | zero =>
    intro y hy
    simpa using h y (by simpa using hy)
  | succ n ih =>
    intro y hy
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro a ha b hb
      have e : φ (a * b) - 2 ^ (n + 1 + 1) * (a * b) =
          (φ a - 2 ^ (n + 1) * a) * φ b + (2 ^ (n + 1) * a) * (φ b - 2 * b) := by
        rw [map_mul]; ring
      rw [e]
      refine Ideal.add_mem _ ?_ ?_
      · have := Ideal.mul_mem_mul (ih a ha) (hφ b hb)
        rwa [← pow_succ] at this
      · have := Ideal.mul_mem_mul (Ideal.mul_mem_left _ (2 ^ (n + 1)) ha) (h b hb)
        rw [← pow_add] at this
        exact this
    · intro a b ha hb
      have e : φ (a + b) - 2 ^ (n + 1 + 1) * (a + b) =
          (φ a - 2 ^ (n + 1 + 1) * a) + (φ b - 2 ^ (n + 1 + 1) * b) := by
        rw [map_add (f := _)]; ring
      rw [e]
      exact Ideal.add_mem _ ha hb

theorem map_eq_zero_of_commute_doubling {k RA RB : Type} [Field k] [CharZero k] [CommRing RA]
    [IsLocalRing RA] [IsNoetherianRing RA] [Algebra k RA] [CommRing RB] (mB : Ideal RB)
    (φA : RA →+* RA) (φB : RB →+* RB) (ψ : RB →+* RA) (hc : ∀ x, ψ (φB x) = φA (ψ x))
    (h1 : ∀ x ∈ mB, ψ x ∈ maximalIdeal RA ^ 2)
    (hA : ∀ x ∈ maximalIdeal RA, φA x - 2 * x ∈ maximalIdeal RA ^ 2)
    (hB : ∀ x ∈ mB, φB x - 2 * x ∈ mB ^ 2) (x : RB) (hx : x ∈ mB) : ψ x = 0 := by
  have key : ∀ n : ℕ, ∀ x ∈ mB, ψ x ∈ maximalIdeal RA ^ (n + 2) := by
    intro n
    induction n with
    | zero => simpa using h1
    | succ n ih =>
      intro x hx
      set m := maximalIdeal RA with hm
      have hy := ih x hx
      have hle : Ideal.map ψ mB ≤ m ^ (n + 2) := Ideal.map_le_iff_le_comap.2 ih
      have hz : ψ (φB x - 2 * x) ∈ m ^ (n + 3) := by
        have h2 : ψ (φB x - 2 * x) ∈ Ideal.map ψ (mB ^ 2) := Ideal.mem_map_of_mem _ (hB x hx)
        rw [Ideal.map_pow] at h2
        have h3 : (Ideal.map ψ mB) ^ 2 ≤ (m ^ (n + 2)) ^ 2 := Ideal.pow_right_mono hle 2
        have h4 := h3 h2
        rw [← pow_mul] at h4
        exact Ideal.pow_le_pow_right (by omega) h4
      have hd := map_sub_two_pow_mul_mem m φA hA (n + 1) _ hy
      have e : (2 ^ (n + 2) - 2 : RA) * ψ x = ψ (φB x - 2 * x) - (φA (ψ x) - 2 ^ (n + 2) * ψ x) := by
        rw [map_sub, map_mul, hc, map_ofNat]; ring
      have h5 : (2 ^ (n + 2) - 2 : RA) * ψ x ∈ m ^ (n + 3) := by
        rw [e]; exact Ideal.sub_mem _ hz hd
      have hne : (2 ^ (n + 2) - 2 : k) ≠ 0 := by
        have : ((2 ^ (n + 2) - 2 : ℤ) : k) ≠ 0 := by
          rw [Int.cast_ne_zero]
          have : (2 : ℤ) ^ (n + 2) = 4 * 2 ^ n := by ring
          have h6 : (0 : ℤ) < 2 ^ n := by positivity
          omega
        simpa using this
      have h7 := Ideal.mul_mem_left _ (algebraMap k RA (2 ^ (n + 2) - 2 : k)⁻¹) h5
      have e2 : algebraMap k RA (2 ^ (n + 2) - 2 : k)⁻¹ * ((2 ^ (n + 2) - 2 : RA) * ψ x) = ψ x := by
        have : (2 ^ (n + 2) - 2 : RA) = algebraMap k RA (2 ^ (n + 2) - 2 : k) := by
          rw [map_sub, map_pow, map_ofNat]
        rw [this, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hne, map_one, one_mul]
      rwa [e2] at h7
  have hinf := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal RA) (Ideal.IsPrime.ne_top inferInstance)
  have : ψ x ∈ (⨅ i : ℕ, maximalIdeal RA ^ i) := by
    refine (Submodule.mem_iInf _).2 fun i => ?_
    exact Ideal.pow_le_pow_right (by omega) (key i x hx)
  rw [hinf] at this
  simpa using this

section Tan

variable {k R : Type} [Field k] [CommRing R] [Algebra k R] (ev : R →ₐ[k] k)

def kerPart (x : R) : RingHom.ker ev :=
  ⟨x - algebraMap k R (ev x), by simp [RingHom.mem_ker]⟩

def cotPart (x : R) : (RingHom.ker ev).Cotangent := (RingHom.ker ev).toCotangent (kerPart ev x)

theorem cotPart_add (x y : R) : cotPart ev (x + y) = cotPart ev x + cotPart ev y := by
  rw [cotPart, cotPart, cotPart, ← map_add (f := _)]
  congr 1
  apply Subtype.ext
  simp only [kerPart, map_add (f := _), Submodule.coe_add]
  ring

theorem cotPart_algebraMap (a : k) : cotPart ev (algebraMap k R a) = 0 := by
  have : kerPart ev (algebraMap k R a) = 0 := Subtype.ext (by simp [kerPart])
  rw [cotPart, this, map_zero]

theorem cotPart_mul (x y : R) : cotPart ev (x * y) = ev x • cotPart ev y + ev y • cotPart ev x := by
  rw [← algebraMap_smul R (ev x), ← algebraMap_smul R (ev y), cotPart, cotPart, cotPart, ← map_smul,
    ← map_smul, ← map_add, Ideal.toCotangent_eq]
  have e : ((kerPart ev (x * y) : R) - (algebraMap k R (ev x) • kerPart ev y + algebraMap k R (ev y) • kerPart ev x :
      RingHom.ker ev)) = (kerPart ev x : R) * (kerPart ev y : R) := by
    simp only [kerPart, Submodule.coe_add, Submodule.coe_smul, smul_eq_mul, map_mul]
    ring
  rw [e, pow_two]
  exact Ideal.mul_mem_mul (kerPart ev x).2 (kerPart ev y).2

def tanHom (lam : (RingHom.ker ev).Cotangent →ₗ[k] k) : R →ₐ[k] DualNumber k where
  toFun x := TrivSqZeroExt.inl (ev x) + TrivSqZeroExt.inr (lam (cotPart ev x))
  map_one' := by
    have := cotPart_algebraMap ev 1
    rw [map_one] at this
    ext <;> simp [this]
  map_mul' x y := by
    ext
    · simp
    · simp [cotPart_mul, mul_comm]
  map_zero' := by
    have := cotPart_algebraMap ev 0
    rw [map_zero] at this
    ext <;> simp [this]
  map_add' x y := by
    ext
    · simp
    · simp [cotPart_add]
  commutes' a := by
    ext
    · simp [TrivSqZeroExt.algebraMap_eq_inl]
    · simp [cotPart_algebraMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem tanHom_fst (lam : (RingHom.ker ev).Cotangent →ₗ[k] k) (x : R) : (tanHom ev lam x).fst = ev x := by
  simp [tanHom]

theorem tanHom_snd (lam : (RingHom.ker ev).Cotangent →ₗ[k] k) (x : R) :
    (tanHom ev lam x).snd = lam (cotPart ev x) := by
  simp [tanHom]

theorem mem_sq_of_tanHom_eq_zero (x : R) (h : ∀ lam, tanHom ev lam x = 0) : x ∈ RingHom.ker ev ^ 2 := by
  have h0 : ev x = 0 := by rw [← tanHom_fst ev 0, h]; rfl
  have h1 : cotPart ev x = 0 := by
    refine (Module.forall_dual_apply_eq_zero_iff k _).1 fun lam => ?_
    rw [← tanHom_snd ev lam, h]; rfl
  rw [cotPart, Ideal.toCotangent_eq_zero] at h1
  simpa [kerPart, h0] using h1

theorem ker_eq_maximalIdeal_of_algHom [IsLocalRing R] : RingHom.ker ev = maximalIdeal R :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective (ev : R →+* k)
    (fun a => ⟨algebraMap k R a, by simp⟩))

end Tan

end GlobalTheory.LieFaithful
end
end

section

open TrivSqZeroExt

namespace GlobalTheory

theorem finrank_kaehler_eq_of_universal_tangent :
    ∀ (R A k : Type) [CommRing R] [CommRing A] [Algebra R A] [Field k] (n d : ℕ)
    [Module.Free A (Ω[A⁄R])] [Module.Finite A (Ω[A⁄R])], Module.finrank A (Ω[A⁄R]) = n →
    ∀ (φ : A →+* k) (ψ : A →+* TrivSqZeroExt k (Fin d → k)),
    (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom.comp ψ = φ →
    ψ.comp (algebraMap R A) = (algebraMap k (TrivSqZeroExt k (Fin d → k))).comp (φ.comp (algebraMap R A)) →
    (∀ v : A →+* DualNumber k, (TrivSqZeroExt.fstHom k k k).toRingHom.comp v = φ →
      v.comp (algebraMap R A) = (algebraMap k (DualNumber k)).comp (φ.comp (algebraMap R A)) →
      ∃! c : (Fin d → k) →ₗ[k] k, v = (TrivSqZeroExt.map c).toRingHom.comp ψ) → d = n := by
  intro R A k _ _ _ _ n d _ _ hn φ ψ hfst hR huniv
  classical
  haveI : Nontrivial A := φ.domain_nontrivial
  letI : Algebra A k := φ.toAlgebra
  letI : Algebra R k := (φ.comp (algebraMap R A)).toAlgebra
  haveI : IsScalarTower R A k := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  have hψf : ∀ a, (ψ a).fst = φ a := fun a => by
    simpa using RingHom.congr_fun hfst a
  have hψR : ∀ r, (ψ (algebraMap R A r)).snd = 0 := fun r => by
    have := congrArg TrivSqZeroExt.snd (RingHom.congr_fun hR r)
    simpa [TrivSqZeroExt.algebraMap_eq_inl] using this
  have hsA : ∀ (a : A) (x : k), a • x = φ a * x := fun a x => rfl
  have hsR : ∀ (r : R) (x : k), r • x = φ (algebraMap R A r) * x := fun r x => rfl

  let E : Derivation R A (Fin d → k) := Derivation.mk'
    { toFun := fun a => (ψ a).snd
      map_add' := fun a b => by simp
      map_smul' := fun r a => by
        funext i
        simp [Algebra.smul_def, hψR, hψf, hsR, RingHom.algebraMap_toAlgebra] }
    (fun a b => by
      funext i
      simp [hψf, hsA, mul_comm])
  have hE : ∀ a, E a = (ψ a).snd := fun a => rfl
  let El : Ω[A⁄R] →ₗ[A] (Fin d → k) := E.liftKaehlerDifferential
  have hEl : ∀ a, El (KaehlerDifferential.D R A a) = (ψ a).snd := fun a => by
    simp [El, hE]
  let b : Module.Basis (Fin n) A (Ω[A⁄R]) := Module.finBasisOfFinrankEq A _ hn
  have hcA : ∀ (c : (Fin d → k) →ₗ[k] k) (a : A) (x : Fin d → k), c (a • x) = a • c x :=
    fun c a x => by
      have : a • x = φ a • x := rfl
      rw [this, c.map_smul]; rfl
  let cA : ((Fin d → k) →ₗ[k] k) → ((Fin d → k) →ₗ[A] k) := fun c =>
    { toFun := c, map_add' := c.map_add, map_smul' := hcA c }
  have hcA' : ∀ c x, cA c x = c x := fun _ _ => rfl
  have hc1 : ∀ c : (Fin d → k) →ₗ[k] k,
      (TrivSqZeroExt.fstHom k k k).toRingHom.comp ((TrivSqZeroExt.map c).toRingHom.comp ψ) = φ :=
    fun c => by
      ext a
      simp [hψf]
  have hc2 : ∀ c : (Fin d → k) →ₗ[k] k,
      ((TrivSqZeroExt.map c).toRingHom.comp ψ).comp (algebraMap R A) =
        (algebraMap k (DualNumber k)).comp (φ.comp (algebraMap R A)) := fun c => by
    ext r
    · simp [hψf, TrivSqZeroExt.algebraMap_eq_inl]
    · simp [hψR, TrivSqZeroExt.algebraMap_eq_inl]
  let L : ((Fin d → k) →ₗ[k] k) →ₗ[k] (Fin n → k) :=
    LinearMap.pi (fun i => LinearMap.applyₗ (R := k) (El (b i)))
  have hL : ∀ c i, L c i = c (El (b i)) := fun _ _ => rfl
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have h0 : (cA c).comp El = 0 := b.ext fun i => by
      simpa [hL, hcA'] using congrFun hc i
    have h0' : ∀ a, c (ψ a).snd = 0 := fun a => by
      have := LinearMap.congr_fun h0 (KaehlerDifferential.D R A a)
      simpa [hEl, hcA'] using this
    have heq : (TrivSqZeroExt.map c).toRingHom.comp ψ = (TrivSqZeroExt.map 0).toRingHom.comp ψ := by
      ext a
      · simp
      · simp [h0']
    exact (huniv _ (hc1 c) (hc2 c)).unique rfl heq
  have hsurj : Function.Surjective L := by
    intro f
    let g : Ω[A⁄R] →ₗ[A] k := b.constr A f
    let Df : Derivation R A k := g.compDer (KaehlerDifferential.D R A)
    let v : A →+* DualNumber k :=
      { toFun := fun a => TrivSqZeroExt.inl (φ a) + TrivSqZeroExt.inr (Df a)
        map_one' := by ext <;> simp
        map_mul' := fun a a' => by ext <;> simp [hsA, mul_comm, add_comm]
        map_zero' := by ext <;> simp
        map_add' := fun a a' => by ext <;> simp [add_add_add_comm] }
    have hv1 : (TrivSqZeroExt.fstHom k k k).toRingHom.comp v = φ := by
      ext a
      simp [v]
    have hv2 : v.comp (algebraMap R A) = (algebraMap k (DualNumber k)).comp (φ.comp (algebraMap R A)) := by
      ext r
      · simp [v, TrivSqZeroExt.algebraMap_eq_inl]
      · simp [v, TrivSqZeroExt.algebraMap_eq_inl]
    obtain ⟨c, hc, -⟩ := huniv v hv1 hv2
    have key : ∀ a, Df a = c (ψ a).snd := fun a => by
      have := congrArg TrivSqZeroExt.snd (RingHom.congr_fun hc a)
      simpa [v] using this
    have hg : (cA c).comp El = g := Derivation.liftKaehlerDifferential_unique _ _
      (Derivation.ext fun a => by simp [hEl, hcA', ← key, Df])
    refine ⟨c, funext fun i => ?_⟩
    rw [hL, ← hcA' c, ← LinearMap.comp_apply, hg]
    simp [g]
  have e := (LinearEquiv.ofBijective L ⟨hinj, hsurj⟩).finrank_eq
  rw [Module.finrank_linearMap, Module.finrank_fin_fun, Module.finrank_fin_fun, Module.finrank_self] at e
  simpa using e

end GlobalTheory
end

section

namespace GlobalTheory.SecondComponentSum

theorem snd_eq_sum {k A : Type} [CommRing k] [CommRing A] [Algebra k A] {D : ℕ}
    (f : Fin D → A) (B : Module.Basis (Fin D) A Ω[A⁄k])
    (hB : ∀ i : Fin D, B i = KaehlerDifferential.D k A (f i))
    {K : Type} [Field K] (θ : A →+* DualNumber K)
    (hθ : ∀ a : k, TrivSqZeroExt.snd (θ (algebraMap k A a)) = (0 : K)) (s : A) :
    TrivSqZeroExt.snd (θ s) = ∑ b : Fin D, TrivSqZeroExt.snd (θ (f b)) *
      TrivSqZeroExt.fst (θ ((LinearMap.compDer (Module.Basis.coord B b)
        (KaehlerDifferential.D k A)) s)) := by
  classical

  let φ : A →+* K := (TrivSqZeroExt.fstHom K K K).toRingHom.comp θ
  let _ : Module A K := Module.compHom K φ
  let _ : Module k K := Module.compHom K (φ.comp (algebraMap k A))
  have : IsScalarTower k A K := ⟨fun c a x => by
    change φ (c • a) * x = φ (algebraMap k A c) * (φ a * x)
    rw [Algebra.smul_def, map_mul, mul_assoc]⟩
  have hsmul : ∀ (a : A) (x : K), a • x = TrivSqZeroExt.fst (θ a) * x := fun _ _ => rfl
  have hsndmul : ∀ a b : A, TrivSqZeroExt.snd (θ (a * b)) =
      TrivSqZeroExt.fst (θ a) * TrivSqZeroExt.snd (θ b) +
        TrivSqZeroExt.snd (θ a) * TrivSqZeroExt.fst (θ b) := by
    intro a b
    rw [map_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, op_smul_eq_mul]
  let ℓ : A →ₗ[k] K :=
    { toFun := fun a => TrivSqZeroExt.snd (θ a)
      map_add' := fun a b => by
        simp only [map_add (f := _), TrivSqZeroExt.snd_add]
      map_smul' := fun c a => by
        change TrivSqZeroExt.snd (θ (c • a)) = φ (algebraMap k A c) * TrivSqZeroExt.snd (θ a)
        rw [Algebra.smul_def, hsndmul, hθ, zero_mul, add_zero]
        rfl }
  let d : Derivation k A K := Derivation.mk' ℓ fun a b => by
    change TrivSqZeroExt.snd (θ (a * b)) = TrivSqZeroExt.fst (θ a) * TrivSqZeroExt.snd (θ b) +
      TrivSqZeroExt.fst (θ b) * TrivSqZeroExt.snd (θ a)
    rw [hsndmul, mul_comm (TrivSqZeroExt.snd (θ a))]

  have key := congrArg d.liftKaehlerDifferential (B.sum_repr (KaehlerDifferential.D k A s))

  rw [Derivation.liftKaehlerDifferential_comp_D, map_sum] at key
  change d s = _
  rw [← key]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [LinearMap.map_smul, hB, Derivation.liftKaehlerDifferential_comp_D, hsmul, mul_comm]
  rfl

end GlobalTheory.SecondComponentSum
end

section

namespace GlobalTheory

def dualNumberRingHomMap {S S' : Type} [CommRing S] [CommRing S'] (f : S →+* S') :
    DualNumber S →+* DualNumber S' where
  toFun x := TrivSqZeroExt.inl (f x.fst) + TrivSqZeroExt.inr (f x.snd)
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext <;> simp [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul, mul_comm] <;> ring
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp <;> ring

theorem dualNumber_deformation_extends_away :
    ∀ {S S' : Type} [CommRing S] [CommRing S'] [Algebra S S'] (g : S) [IsLocalization.Away g S']
      (d : S →+* DualNumber S), (∀ s, (d s).fst = s) →
      ∃ d' : S' →+* DualNumber S', (∀ s, (d' s).fst = s) ∧
        ∀ s, (d' (algebraMap S S' s)).snd = algebraMap S S' (d s).snd := by
  intro S S' _ _ _ g _ d hd
  let ψ : S →+* DualNumber S' := (dualNumberRingHomMap (algebraMap S S')).comp d
  have hψ : ∀ s, ψ s = TrivSqZeroExt.inl (algebraMap S S' (d s).fst)
      + TrivSqZeroExt.inr (algebraMap S S' (d s).snd) := fun s => rfl
  have hu : IsUnit (ψ g) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hψ]
    simpa [hd] using IsLocalization.Away.algebraMap_isUnit (S := S') g
  refine ⟨IsLocalization.Away.lift g hu, ?_, ?_⟩
  · have h : (TrivSqZeroExt.fstHom S' S' S').toRingHom.comp (IsLocalization.Away.lift g hu)
        = RingHom.id S' := by
      apply IsLocalization.ringHom_ext (Submonoid.powers g)
      ext s
      simp [IsLocalization.Away.lift, IsLocalization.lift_eq, hψ, hd]
    intro s
    exact congrArg (fun F : S' →+* S' => F s) h
  · intro s
    simp [IsLocalization.Away.lift, IsLocalization.lift_eq, hψ]
    rw [Algebra.smul_def, mul_one]

end GlobalTheory
end

section

namespace GlobalTheory.FieldCaseReduction

open Polynomial

theorem field_case (F : Type) [Field F] [Finite F] (t m f : F) (hD : t ^ 2 - 4 * m ≠ 0) :
    ∃ a b : F, a ^ 2 + t * a * b + m * b ^ 2 = f := by
  classical
  by_cases h2 : ringChar F = 2
  · obtain ⟨a, ha⟩ := FiniteField.isSquare_of_char_two h2 f
    exact ⟨a, 0, by rw [ha]; ring⟩
  · haveI := Fintype.ofFinite F
    have hodd : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two h2
    have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero h2
    have hp : (X ^ 2 : F[X]).degree = 2 := by simp
    have hq : (C (-(t ^ 2 - 4 * m)) * X ^ 2 + C 0 * X + C (-(4 * f)) : F[X]).degree = 2 :=
      degree_quadratic (neg_ne_zero.mpr hD)
    obtain ⟨x, b, hxb⟩ := FiniteField.exists_root_sum_quadratic hp hq hodd
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at hxb
    refine ⟨(x - t * b) / 2, b, ?_⟩
    field_simp
    linear_combination hxb

theorem main (S : Type) [inst : CommRing S] [Finite S] [IsReduced S] (t m f : S)
    (hD : IsUnit (t ^ (2 : ℕ) - (4 : S) * m)) (_hf : IsUnit f) :
    ∃ (a : S) (b : S), a ^ (2 : ℕ) + t * a * b + m * b ^ (2 : ℕ) = f := by
  classical
  haveI : IsArtinianRing S := isArtinian_of_finite
  let e := (IsArtinianRing.equivPi S).toRingEquiv
  have key : ∀ I : MaximalSpectrum S, ∃ a b : S ⧸ I.asIdeal,
      a ^ 2 + e t I * a * b + e m I * b ^ 2 = e f I := by
    intro I
    haveI := I.isMaximal
    letI : Field (S ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : Finite (S ⧸ I.asIdeal) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
    apply field_case
    have h := (hD.map ((Pi.evalRingHom (fun J : MaximalSpectrum S => S ⧸ J.asIdeal) I).comp
      e.toRingHom)).ne_zero
    simp only [map_sub, map_mul, map_pow, map_ofNat] at h
    exact h
  choose a b hab using key
  refine ⟨e.symm a, e.symm b, e.injective ?_⟩
  simp only [map_add (f := _), map_mul, map_pow, RingEquiv.apply_symm_apply]
  funext I
  exact hab I

end GlobalTheory.FieldCaseReduction
end
