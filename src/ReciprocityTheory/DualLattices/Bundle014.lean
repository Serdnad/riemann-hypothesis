module

public import ReciprocityTheory.DualLattices.Bundle006
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReciprocityTheory.DualLattices.Bundle007
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReciprocityTheory.DualLattices.DiscriminantColengthStatement
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.DualLattices.Bundle001
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.Valuation.Integers
import ReciprocityTheory.DualLattices.Bundle002

@[expose] public section

section

noncomputable section

open Polynomial

namespace ReciprocityTheory.PGsh

namespace DualNum

variable {R₀ : Type} [CommRing R₀] (R : LAlg R₀)

abbrev DN := (R : Type)[X] ⧸ Ideal.span {(X : (R : Type)[X]) ^ 2}

def ev : DN R →+* (R : Type) :=
  Ideal.Quotient.lift _ (Polynomial.evalRingHom 0) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp)

lemma ev_mk (f : (R : Type)[X]) : ev R (Ideal.Quotient.mk _ f) = f.eval 0 := rfl

lemma ev_surj : Function.Surjective (ev R) := fun r => ⟨Ideal.Quotient.mk _ (C r), by rw [ev_mk, eval_C]⟩

def eta : DN R := Ideal.Quotient.mk _ X

lemma eta_sq : eta R * eta R = 0 := by
  unfold eta
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← pow_two]
  exact Ideal.mem_span_singleton_self _

lemma ker_ev : RingHom.ker (ev R) = Ideal.span {eta R} := by
  apply le_antisymm
  · intro y hy
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [RingHom.mem_ker, ev_mk] at hy
    have hX : (X : (R : Type)[X]) ∣ f := by
      rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
      exact hy
    obtain ⟨g, rfl⟩ := hX
    rw [map_mul]
    exact Ideal.mem_span_singleton.2 (dvd_mul_right (eta R) _)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    show ev R (eta R) = 0
    rw [eta, ev_mk, eval_X]

lemma isLocal : IsLocalRing (DN R) := by
  have hnt : Nontrivial (DN R) := (ev R).domain_nontrivial
  have hunit : ∀ y : DN R, IsUnit (ev R y) → IsUnit y := by
    intro y hy
    obtain ⟨u, hu⟩ : ∃ u : DN R, u = Ideal.Quotient.mk _ (C (ev R y)) := ⟨_, rfl⟩
    have hev : ev R u = ev R y := by rw [hu, ev_mk, eval_C]
    have hk : y - u ∈ RingHom.ker (ev R) := by rw [RingHom.mem_ker, map_sub, hev, sub_self]
    rw [ker_ev, Ideal.mem_span_singleton] at hk
    obtain ⟨c, hc⟩ := hk
    have hn : IsNilpotent (y - u) := ⟨2, by rw [hc, mul_pow, pow_two (eta R), eta_sq, zero_mul]⟩
    have hu' : IsUnit u := by
      have e : u = ((Ideal.Quotient.mk _).comp Polynomial.C) (ev R y) := hu
      rw [e]
      exact hy.map _
    have h := hn.isUnit_add_left_of_commute hu' (Commute.all _ _)
    rwa [add_sub_cancel] at h
  exact IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a =>
    (IsLocalRing.isUnit_or_isUnit_one_sub_self (ev R a)).imp (hunit a)
      fun h => hunit (1 - a) (by rwa [map_sub, map_one])

lemma ev_algebraMap (r : (R : Type)) : ev R (algebraMap (R : Type) (DN R) r) = r := by
  rw [← Ideal.Quotient.mk_algebraMap, ev_mk]
  simp

def evAlg : DN R →ₐ[R₀] (R : Type) :=
  { ev R with
    commutes' := fun r => by
      show ev R (algebraMap R₀ (DN R) r) = _
      rw [← Ideal.Quotient.mk_algebraMap, ev_mk, Polynomial.algebraMap_apply, eval_C] }

def D : LAlg R₀ := { carrier := DN R, loc := isLocal R }

def dualPair : DualPair R where
  D := D R
  π := ⟨evAlg R, TowerExample.isLocalHom_of_surj _ (ev_surj R)⟩
  σ := ⟨IsScalarTower.toAlgHom R₀ (R : Type) (DN R),
    ⟨fun r hr => by
      have h := hr.map (ev R)
      have e : ev R ((IsScalarTower.toAlgHom R₀ (R : Type) (DN R) : (R : Type) →+* DN R) r) = r :=
        ev_algebraMap R r
      convert h using 1
      exact e.symm⟩⟩
  η := eta R
  sect r := ev_algebraMap R r
  η_sq := eta_sq R
  ker_eq := ker_ev R
  free r h := by
    change algebraMap (R : Type) (DN R) r * eta R = 0 at h
    rw [← Ideal.Quotient.mk_algebraMap, eta, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton, X_pow_dvd_iff] at h
    have h1 := h 1 (by norm_num)
    simpa [Polynomial.algebraMap_apply] using h1

end DualNum

end ReciprocityTheory.PGsh
end
end

section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up.PullbackHopfOrder

open ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem mem_augIdeal {X : Type} [AddCommGroup X] {M : Submodule R (X → C)} {f : X → C} :
    f ∈ augIdeal M ↔ f ∈ M ∧ f 0 = 0 := by
  exact Iff.rfl

theorem sqIdeal_le {X Y : Type} (F : (X → C) →ₗ[R] (Y → C))
    (hF : ∀ f g, F (f * g) = F f * F g) {I : Submodule R (X → C)} {J : Submodule R (Y → C)}
    (hIJ : ∀ f ∈ I, F f ∈ J) : sqIdeal I ≤ (sqIdeal J).comap F := by
  refine Submodule.span_le.2 ?_
  rintro h ⟨f, hf, f', hf', rfl⟩
  show F (f * f') ∈ sqIdeal J
  rw [hF]
  exact Submodule.subset_span ⟨_, hIJ f hf, _, hIJ f' hf', rfl⟩

theorem smulTop_le (q : ℕ) {a b : ℕ} (G : Matrix (Fin a) (Fin b) R) :
    (Ideal.span {(q : R)} • (⊤ : Submodule R (Fin b → R))) ≤
      (Ideal.span {(q : R)} • (⊤ : Submodule R (Fin a → R))).comap G.mulVecLin := by
  refine Submodule.smul_le.2 fun r hr n _ => ?_
  rw [Submodule.mem_comap, map_smul]
  exact Submodule.smul_mem_smul hr Submodule.mem_top

def mq (q : ℕ) {a b : ℕ} (G : Matrix (Fin a) (Fin b) R) :
    LieDualModP q R b →ₗ[R] LieDualModP q R a :=
  Submodule.mapQ _ _ G.mulVecLin (smulTop_le q G)

theorem mq_mk (q : ℕ) {a b : ℕ} (G : Matrix (Fin a) (Fin b) R) (x : Fin b → R) :
    mq q G (Submodule.Quotient.mk x) = Submodule.Quotient.mk (G *ᵥ x) := rfl

def qPi (q d : ℕ) : LieDualModP q R d ≃ₗ[R] ((i : Fin d) → R ⧸ Ideal.span {(q : R)}) := by
  let πd : (Fin d → R) →ₗ[R] ((i : Fin d) → R ⧸ Ideal.span {(q : R)}) :=
    LinearMap.pi fun i => (Ideal.span {(q : R)}).mkQ ∘ₗ LinearMap.proj i
  have hπ : ∀ x i, πd x i = Submodule.Quotient.mk (x i) := fun _ _ => rfl
  have hsurj : Function.Surjective πd := by
    intro y
    choose x hx using fun i => Submodule.Quotient.mk_surjective _ (y i)
    exact ⟨x, funext fun i => by rw [hπ, hx]⟩
  have hker : Ideal.span {(q : R)} • (⊤ : Submodule R (Fin d → R)) = LinearMap.ker πd := by
    ext x
    rw [LinearMap.mem_ker]
    constructor
    · intro hx
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro r hr n _
        funext i
        rw [hπ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero, Pi.smul_apply, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ hr
      · intro x y hx hy
        rw [map_add (f := _), hx, hy, add_zero]
    · intro hx
      have : ∀ i, ∃ s, s * (q : R) = x i := fun i => by
        have := congrFun hx i
        rw [hπ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero] at this
        exact Ideal.mem_span_singleton'.1 this
      choose s hs using this
      have hx' : x = (q : R) • s := funext fun i => by
        rw [Pi.smul_apply, smul_eq_mul, mul_comm, hs]
      rw [hx']
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  exact (Submodule.quotEquivOfEq _ _ hker).trans (πd.quotKerEquivOfSurjective hsurj)

variable {X N : Type} [AddCommGroup X] [AddCommGroup N]

theorem omega_pull (q : ℕ) {g d : ℕ} (ψ : X →+ N) (χ : N →+ X) (hχψ : ∀ x, χ (ψ x) = x)
    (A : Submodule R (N → C)) (hA : ∀ f ∈ A, (fun n => f (ψ (χ n))) ∈ A)
    (φ : augIdeal A →ₗ[R] LieDualModP q R g) (hsurj : Function.Surjective φ)
    (hker : LinearMap.ker φ = (sqIdeal (augIdeal A)).comap (augIdeal A).subtype)
    (F : Matrix (Fin g) (Fin g) R) (P1 : Matrix (Fin g) (Fin d) R) (P2 : Matrix (Fin d) (Fin g) R)
    (hF : P1 * P2 = F) (h21 : P2 * P1 = 1)
    (hlin : ∀ (f f' : augIdeal A) (l : Fin g → R),
      (∀ n, (f' : N → C) n = (f : N → C) (ψ (χ n))) →
      φ f = Submodule.Quotient.mk l → φ f' = Submodule.Quotient.mk (F *ᵥ l)) :
    Nonempty (OmAA (A.map (LinearMap.funLeft R C ψ)) ≃ₗ[R] LieDualModP q R d) := by
  classical
  have hM : P2 * F * P1 = 1 := by
    rw [← hF, ← Matrix.mul_assoc P2 P1 P2, h21, Matrix.one_mul, h21]
  have hψI : ∀ f ∈ augIdeal A,
      LinearMap.funLeft R C ψ f ∈ augIdeal (A.map (LinearMap.funLeft R C ψ)) := by
    intro f hf
    rw [mem_augIdeal] at hf ⊢
    refine ⟨Submodule.mem_map_of_mem hf.1, ?_⟩
    rw [LinearMap.funLeft_apply, map_zero]
    exact hf.2
  have hχI : ∀ g ∈ augIdeal (A.map (LinearMap.funLeft R C ψ)),
      LinearMap.funLeft R C χ g ∈ augIdeal A := by
    intro g hg
    rw [mem_augIdeal] at hg ⊢
    obtain ⟨⟨f, hf, rfl⟩, h0⟩ := hg
    refine ⟨hA f hf, ?_⟩
    rw [LinearMap.funLeft_apply, map_zero]
    exact h0
  let Φ0 : augIdeal (A.map (LinearMap.funLeft R C ψ)) →ₗ[R] augIdeal A :=
    ((LinearMap.funLeft R C χ).comp (augIdeal (A.map (LinearMap.funLeft R C ψ))).subtype).codRestrict
      (augIdeal A) (fun g => hχI g.1 g.2)
  let Φ : augIdeal (A.map (LinearMap.funLeft R C ψ)) →ₗ[R] LieDualModP q R d :=
    mq q P2 ∘ₗ φ ∘ₗ Φ0
  have hΦ : ∀ g, Φ g = mq q P2 (φ (Φ0 g)) := fun _ => rfl
  have hsurjΦ : Function.Surjective Φ := by
    intro y
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨f, hf⟩ := hsurj (Submodule.Quotient.mk (P1 *ᵥ w))
    refine ⟨⟨LinearMap.funLeft R C ψ f, hψI f f.2⟩, ?_⟩
    have h1 := hlin f (Φ0 ⟨LinearMap.funLeft R C ψ f, hψI f f.2⟩) (P1 *ᵥ w) (fun n => rfl) hf
    rw [hΦ, h1, mq_mk, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]
  have hkerΦ : LinearMap.ker Φ = (sqIdeal (augIdeal (A.map (LinearMap.funLeft R C ψ)))).comap
      (augIdeal (A.map (LinearMap.funLeft R C ψ))).subtype := by
    ext u
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, hΦ]
    constructor
    · intro h0
      obtain ⟨l, hl⟩ := Submodule.Quotient.mk_surjective _ (φ (Φ0 u))
      have hfix := hlin (Φ0 u) (Φ0 u) l (fun n => by
        show (u : X → C) (χ n) = (u : X → C) (χ (ψ (χ n)))
        rw [hχψ]) hl.symm
      rw [← hl, mq_mk] at h0
      have hφ0 : φ (Φ0 u) = 0 := by
        rw [hfix, ← hF, ← Matrix.mulVec_mulVec,
          show (Submodule.Quotient.mk (P1 *ᵥ (P2 *ᵥ l)) : LieDualModP q R g) =
            mq q P1 (Submodule.Quotient.mk (P2 *ᵥ l)) from rfl, h0, map_zero]
      have hmem : ((Φ0 u : augIdeal A) : N → C) ∈ sqIdeal (augIdeal A) := by
        have := LinearMap.mem_ker.2 hφ0
        rw [hker, Submodule.mem_comap] at this
        exact this
      have := Submodule.mem_comap.1
        (sqIdeal_le (LinearMap.funLeft R C ψ) (fun _ _ => rfl) hψI hmem)
      convert this using 1
      funext x
      show (u : X → C) x = (u : X → C) (χ (ψ x))
      rw [hχψ]
    · intro hu
      have h1 := Submodule.mem_comap.1
        (sqIdeal_le (LinearMap.funLeft R C χ) (fun _ _ => rfl) hχI hu)
      have hφ0 : φ (Φ0 u) = 0 := by
        rw [← LinearMap.mem_ker, hker, Submodule.mem_comap]
        exact h1
      rw [hφ0, map_zero]
  exact ⟨(Submodule.quotEquivOfEq _ _ hkerΦ.symm).trans (Φ.quotKerEquivOfSurjective hsurjΦ)⟩

end ReciprocityTheory.PGsh.Up.PullbackHopfOrder
end
end

section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

abbrev cokE {g : ℕ} {R : Type} [CommRing R] {m : ℕ} (Ht : Matrix (Fin g) (Ix g) R)
    (εT : Fin m → Matrix (Ix g) (Ix g) R) (εL : Fin m → Matrix (Fin g) (Fin g) R) (i j : Fin m) :=
  LinearMap.range (Matrix.mulVecLin (εL i)ᵀ) ⧸
    ((LinearMap.range (Matrix.mulVecLin (εT j))).map (Matrix.mulVecLin Ht)).comap
      (LinearMap.range (Matrix.mulVecLin (εL i)ᵀ)).subtype

structure UnramData (p : ℕ) [Fact p.Prime] (g : ℕ) {C : Type} [Field C] (v : Valuation C NNReal)
    (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] (O : Type) [CommRing O]
    [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R) (H : HodgeTateDatum p g v R O σ cp) where
  m : ℕ
  sg : Fin m → (O →+* R)
  εT : Fin m → Matrix (Ix g) (Ix g) R
  εL : Fin m → Matrix (Fin g) (Fin g) R
  cj : Equiv.Perm (Fin m)
  φ : Equiv.Perm (Fin m)
  r : Fin m → ℕ
  noPad : H.P = 0 ∧ H.PL = 0
  εT_orth : ∀ i j, εT i * εT j = if i = j then εT i else 0
  εT_sum : ∑ i, εT i = 1
  εL_orth : ∀ i j, εL i * εL j = if i = j then εL i else 0
  εL_sum : ∑ i, εL i = 1
  εT_eig : ∀ a i, (H.ρ a).map (algebraMap ℤ_[p] R) * εT i = sg i a • εT i
  εL_eig : ∀ a i, H.ρL a * εL i = sg i a • εL i
  conj : ∀ i a, sg (cj i) a = sg i (σ a)
  frob : ∀ i a, v (algebraMap R C (sg (φ i) a - sg i a ^ p)) < 1
  distinct : ∀ i j, i ≠ j → ∃ a, v (algebraMap R C (sg i a - sg j a)) = 1
  rank : ∀ i, Nonempty (LinearMap.range (Matrix.mulVecLin (εL i)) ≃ₗ[R] (Fin (r i) → R))

def frobSum {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal}
    {R : Type} [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O]
    [Algebra ℤ_[p] O] {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H) (i : Fin U.m) : ℝ :=
  ∑' n : ℕ, (p : ℝ) ^ (-((n : ℝ) + 1)) * U.r ((U.φ ^ (n + 1)) i)

def UnramifiedCokernelLengthStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    p ≠ 2 → HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (i : Fin U.m) (V1 V2 : NNReal),
    HasLen v R (cokE H.Ht U.εT U.εL i (U.cj i)) V1 →
    HasLen v R (cokE H.Ht U.εT U.εL (U.cj i) i) V2 →
    (V1 : ℝ) = V2 * (v (algebraMap R C (p : R)) : ℝ) ^
      ((U.r i : ℝ) / (p - 1) - frobSum U i)

end ReciprocityTheory.PGsh.Up
end
end

section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {v : Valuation C NNReal}

theorem freePts_integral {n h : ℕ} {a : Fin n → C} (ha : ∀ τ, v (a τ) ≤ 1)
    (F : Lat v (Fin n × Fin h)) (hF : F.B = freeMat a h) {w : Fin n × Fin h → C} (hw : w ∈ F.pts)
    (y : Fin n × Fin h) : v (w y) ≤ 1 := by
  obtain ⟨c, hc, rfl⟩ := hw
  rw [hF]
  simp only [Matrix.mulVec, dotProduct]
  refine v.map_sum_le fun x _ => ?_
  rw [map_mul]
  refine mul_le_one₀ ?_ (zero_le) (hc x)
  simp only [freeMat, Matrix.of_apply]
  split_ifs
  · rw [map_pow]
    exact pow_le_one₀ (zero_le) (ha _)
  · simp

def fder {n : ℕ} (a : Fin n → C) (τ : Fin n) : C := ∏ τ' ∈ Finset.univ.erase τ, (a τ - a τ')

theorem prod_fder {n : ℕ} (a : Fin n → C) : ∏ τ, fder a τ = discr a := rfl

private lemma valuation_coeff_prod_X_sub_C_le_one {n : ℕ} {a : Fin n → C} (ha : ∀ τ, v (a τ) ≤ 1)
    (s : Finset (Fin n)) (k : ℕ) :
    v ((∏ τ' ∈ s, (Polynomial.X - Polynomial.C (a τ'))).coeff k) ≤ 1 := by
  have h : (∏ τ' ∈ s, (Polynomial.X - Polynomial.C (a τ'))) =
      (∏ τ' ∈ s, (Polynomial.X - Polynomial.C (⟨a τ', ha τ'⟩ : v.integer))).map v.integer.subtype := by
    simp [Polynomial.map_prod]
  rw [h, Polynomial.coeff_map]
  exact (Valuation.mem_integer_iff _ _).1 (Subtype.prop _)

theorem conductor_mem {n h : ℕ} {a : Fin n → C} (ha : ∀ τ, v (a τ) ≤ 1)
    (F : Lat v (Fin n × Fin h)) (hF : F.B = freeMat a h) (τ : Fin n) (u : Fin h → C)
    (hu : ∀ l, v (u l) ≤ 1) :
    (fun y : Fin n × Fin h => if y.1 = τ then fder a τ * u y.2 else 0) ∈ F.pts := by
  classical
  have hdeg : (∏ τ' ∈ Finset.univ.erase τ, (Polynomial.X - Polynomial.C (a τ'))).natDegree < n := by
    rw [Polynomial.natDegree_finsetProd_X_sub_C_eq_card, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
    exact Nat.sub_lt (Fin.pos τ) one_pos
  have heval : ∀ τ', (∏ τ'' ∈ Finset.univ.erase τ, (Polynomial.X - Polynomial.C (a τ''))).eval (a τ') =
      if τ' = τ then fder a τ else 0 := by
    intro τ'
    rw [Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    split_ifs with h
    · subst h
      rfl
    · exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩) (sub_self _)
  refine ⟨fun x => (∏ τ' ∈ Finset.univ.erase τ, (Polynomial.X - Polynomial.C (a τ'))).coeff x.1 * u x.2,
    fun x => ?_, ?_⟩
  · rw [map_mul]
    exact mul_le_one₀ (valuation_coeff_prod_X_sub_C_le_one ha _ _) (zero_le) (hu _)
  · rw [hF]
    funext y
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, freeMat, Matrix.of_apply, ite_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hsum : ∑ k : Fin n, a y.1 ^ (k : ℕ) *
        ((∏ τ' ∈ Finset.univ.erase τ, (Polynomial.X - Polynomial.C (a τ'))).coeff k * u y.2) =
        (∏ τ' ∈ Finset.univ.erase τ, (Polynomial.X - Polynomial.C (a τ'))).eval (a y.1) * u y.2 := by
      rw [Polynomial.eval_eq_sum_range' hdeg, Finset.sum_mul,
        ← Fin.sum_univ_eq_sum_range (fun i => _ * a y.1 ^ i * u y.2)]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsum, heval]
    split_ifs <;> simp

end ReciprocityTheory.PGsh.Up
end
end
