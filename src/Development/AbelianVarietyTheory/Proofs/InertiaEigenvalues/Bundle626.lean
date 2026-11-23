module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsGenIsUnitSub
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle062
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential

@[expose] public section

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

section Defs

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]


variable (l) in
def LTo0 {ι : Type} (w : ι → Wq l a) : Prop := ∀ r : ℕ, ∀ᶠ n in cofinite, (l : Wq l a) ^ r ∣ w n

variable (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  (e : ℕ)

def SdSet : Set (ZMod a → K⟦X⟧) :=
  {F | ∃ w : ℕ → Wq l a, LTo0 l w ∧
    ∀ τ n, ((n / e).factorial : K) * coeff n (F τ) = algebraMap O K (emb t τ (w n))}

def Sd : Subring (ZMod a → K⟦X⟧) := Subring.closure (SdSet t K e)

def PPSet : Set (ZMod a → K⟦X⟧⟦X⟧) :=
  {F | ∃ w : ℕ × ℕ → Wq l a, LTo0 l w ∧
    ∀ τ i n, ((i.factorial * (n / e).factorial : ℕ) : K) * coeff n (coeff i (F τ)) =
      algebraMap O K (emb t τ (w (i, n)))}

def PPd : Subring (ZMod a → K⟦X⟧⟦X⟧) := Subring.closure (PPSet t K e)

def inclS : (Wq l a)⟦X⟧ →+* (ZMod a → K⟦X⟧) :=
  Pi.ringHom fun τ => (A O K).val.toRingHom.comp ((Pi.evalRingHom (fun _ : ZMod a => A O K) τ).comp (toAc t K))

theorem inclS_apply (x : (Wq l a)⟦X⟧) (τ : ZMod a) : inclS t K x τ = (toAc t K x τ : K⟦X⟧) := rfl

variable {K}

def frob2 (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧) : (ZMod a → K⟦X⟧⟦X⟧) →+* (ZMod a → K⟦X⟧⟦X⟧) :=
  Pi.ringHom fun τ => φ₂.comp (Pi.evalRingHom (fun _ : ZMod a => K⟦X⟧⟦X⟧) (τ - 1))


variable (a K) in
def constP : (ZMod a → K⟦X⟧) →+* (ZMod a → K⟦X⟧⟦X⟧) :=
  Pi.ringHom fun τ => (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).comp (Pi.evalRingHom (fun _ : ZMod a => K⟦X⟧) τ)


variable (a) in
def shP (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) : (ZMod a → K⟦X⟧) →+* (ZMod a → K⟦X⟧⟦X⟧) :=
  Pi.ringHom fun τ => sh.comp (Pi.evalRingHom (fun _ : ZMod a => K⟦X⟧) τ)


variable (a K) in
def diag : (ZMod a → K⟦X⟧⟦X⟧) →+* (ZMod a → K⟦X⟧) :=
  Pi.ringHom fun τ => (constantCoeff : K⟦X⟧⟦X⟧ →+* K⟦X⟧).comp (Pi.evalRingHom (fun _ : ZMod a => K⟦X⟧⟦X⟧) τ)

end Defs

theorem tf_pi {R : Type} [CommRing R] [IsDomain R] {n a : ℕ} (hn : (n : R) ≠ 0) (x : ZMod a → R)
    (h : (n : ZMod a → R) * x = 0) : x = 0 := funext fun τ => by
  have h1 := congrFun h τ
  simp only [Pi.mul_apply, Pi.natCast_apply, Pi.zero_apply] at h1
  exact (mul_eq_zero.1 h1).resolve_left hn

theorem natCast_ne_zero_ps {R : Type} [CommRing R] {n : ℕ} (h : (n : R) ≠ 0) : (n : R⟦X⟧) ≠ 0 := fun h' =>
  h (by simpa using congrArg (constantCoeff : R⟦X⟧ →+* R) h')

theorem tf_sub {R : Type} [CommRing R] {n : ℕ} (s : Subring R) (htf : ∀ x : R, (n : R) * x = 0 → x = 0)
    (x : ↥s) (h : (n : ↥s) * x = 0) : x = 0 := Subtype.ext (htf _ (by simpa using congrArg Subtype.val h))

theorem nzd_of_tf {R : Type} [CommRing R] {n : ℕ} (htf : ∀ x : R, (n : R) * x = 0 → x = 0) :
    (n : R) ∈ nonZeroDivisors R :=
  mem_nonZeroDivisors_iff.2 ⟨htf, fun x hx => htf x (by rw [mul_comm]; exact hx)⟩

theorem bdd_self {R : Type} [CommRing R] (n : ℕ) : ∃ m : ℕ, ∀ x : R ⧸ Ideal.span {(n : R)},
    (∃ k : ℕ, (n : R ⧸ Ideal.span {(n : R)}) ^ k * x = 0) → (n : R ⧸ Ideal.span {(n : R)}) ^ m * x = 0 := by
  refine ⟨1, fun x _ => ?_⟩
  have h : (n : R ⧸ Ideal.span {(n : R)}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(n : R)})), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  rw [h, pow_one, zero_mul]

variable {l : ℕ} [hl : Fact l.Prime]

theorem isUnit_delta_l {A : Type} [CommRing A] (D : Delta l A) (htf : ∀ x : A, (l : A) * x = 0 → x = 0)
    [IsAdicComplete (Ideal.span {(l : A)}) A] : IsUnit (D.δ l) := by
  have h1 : D.δ l = 1 - (l : A) ^ (l - 1) := by
    rw [← sub_eq_zero]
    apply htf
    have h := D.φ_eq (l : A)
    rw [map_natCast] at h
    have h2 : (l : A) ^ l = (l : A) * (l : A) ^ (l - 1) := by
      rw [← pow_succ']; congr 1; have := hl.out.one_lt; omega
    linear_combination -h - h2
  rw [h1]
  have hm : -(l : A) ^ (l - 1) ∈ Ideal.span {(l : A)} := (Ideal.neg_mem_iff _).2
    (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ (by have := hl.out.one_lt; omega))
  have := Ideal.mem_jacobson_bot.1 (IsAdicComplete.le_jacobson_bot _ hm) 1
  rwa [mul_one, neg_add_eq_sub] at this

section Sh

variable {K : Type} [NormedField K] [CharZero K] (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
  (hsh : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f)
include hsh

theorem constantCoeff_sh (f : K⟦X⟧) : constantCoeff (sh f) = f := by
  simpa using hsh f 0

theorem sh_X : sh X = C X + X := by
  ext i : 1
  have h := hsh X i
  rcases i with _ | _ | i
  · simpa using h
  · simp [coeff_C, coeff_X]
    simpa [derivative_X] using h
  · have h3 : ((i + 2).factorial : K⟦X⟧) ≠ 0 := natCast_ne_zero_ps (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
    have h4 : (PowerSeries.derivative (R := K))^[i + 2] X = 0 := by
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, derivative_X]
      rw [derivative_one]
      exact iterate_derivative_zero
    rw [h4] at h
    rw [(mul_eq_zero.1 h).resolve_left h3]
    simp [coeff_C, coeff_X]

theorem constantCoeff_φ₂ (l : ℕ) [Fact l.Prime] (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hφC : ∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f))
    (hφsh : ∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) (G : K⟦X⟧⟦X⟧) :
    constantCoeff (φ₂ G) = frob K l (constantCoeff G) := by
  have hX : φ₂ X = sh (X ^ l) - C (X ^ l) := by
    have h : (X : K⟦X⟧⟦X⟧) = sh X - C X := by rw [sh_X sh hsh]; ring
    rw [h, map_sub, hφsh, hφC, frob_X]
  conv_lhs => rw [eq_shift_mul_X_add_const G]
  rw [map_add (f := _), map_mul, hX, hφC, map_add (f := _), map_mul, map_sub, constantCoeff_sh sh hsh, constantCoeff_C,
    constantCoeff_C, sub_self, mul_zero, zero_add]

end Sh

section Maps

variable {a : ℕ} [NeZero a] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (t : Wq l a →ₐ[ℤ_[l]] O) (e : ℕ)

theorem frob_toAc (x : (Wq l a)⟦X⟧) (τ : ZMod a) :
    frob K l (toAc t K x (τ - 1) : K⟦X⟧) = (toAc t K (frobS l a x) τ : K⟦X⟧) := by
  ext n
  have : coeff n (frobS l a x) = if l ∣ n then sigma l a (coeff (n / l) x) else 0 := by
    simp only [frobS, RingHom.comp_apply, coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coeff_expand]
    split_ifs <;> simp
  rw [coeff_frob, coeff_toAc, coeff_toAc, this]
  split_ifs
  · rw [emb_sigma]
  · simp

theorem constP_mem {F : ZMod a → K⟦X⟧} (hF : F ∈ SdSet t K e) : constP a K F ∈ PPSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  refine ⟨fun p => if p.1 = 0 then w p.2 else 0, fun r => ?_, fun τ i n => ?_⟩
  · have h := hw r
    rw [Filter.eventually_cofinite] at h ⊢
    refine (h.image fun n => ((0 : ℕ), n)).subset ?_
    rintro ⟨i, n⟩ hin
    by_cases hi : i = 0
    · subst hi; exact ⟨n, by simpa using hin, rfl⟩
    · simp [hi] at hin
  · change ((i.factorial * (n / e).factorial : ℕ) : K) * coeff n (coeff i (C (F τ))) = _
    rw [coeff_C]
    by_cases hi : i = 0
    · subst hi; simpa using hF τ n
    · simp [hi]

theorem diag_mem {F : ZMod a → K⟦X⟧⟦X⟧} (hF : F ∈ PPSet t K e) : diag a K F ∈ SdSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  refine ⟨fun n => w (0, n), fun r => ?_, fun τ n => ?_⟩
  · have h := hw r
    rw [Filter.eventually_cofinite] at h ⊢
    exact h.preimage (fun _ _ _ _ h => by simpa using h)
  · have h := hF τ 0 n
    simp only [Nat.factorial_zero, one_mul, coeff_zero_eq_constantCoeff] at h
    exact h

end Maps

end GlobalTheory.CrysPrism
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.CrysEps

theorem shift_C {K : Type} [Field K] [CharZero K] (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (h : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f)
    (k : K) : sh (PowerSeries.C k) = PowerSeries.C (PowerSeries.C k) := by
  refine PowerSeries.ext fun i => ?_
  cases i with
  | zero => simpa using h (PowerSeries.C k) 0
  | succ n =>
    have h1 := h (PowerSeries.C k) (n + 1)
    rw [Function.iterate_succ_apply, PowerSeries.derivative_C,
      PowerSeries.iterate_derivative_zero] at h1
    have h2 : ((n + 1).factorial : K⟦X⟧) ≠ 0 := by
      rw [← map_natCast (PowerSeries.C : K →+* K⟦X⟧), Ne,
        map_eq_zero_iff _ PowerSeries.C_injective]
      exact Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    rw [(mul_eq_zero.1 h1).resolve_left h2, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero n)]

theorem bc_induction {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) (p : N → Prop)
    (h0 : p 0) (hadd : ∀ y z, p y → p z → p (y + z)) (hs : ∀ (r : B) y, p y → p (r • y))
    (hu : ∀ x, p (u x)) (y : N) : p y := by
  first
  | (rename_i h_4 h_5 h_6 h_7 h_8 h_9; revert A B M N h_4 h_5 h_6 h_7 h_8 h_9 f u h p h0 hadd hs hu y; exact @_root_.GlobalTheory.BaseChangeInduction.baseChange_induction)
  | exact @_root_.GlobalTheory.BaseChangeInduction.baseChange_induction
  | exact _root_.GlobalTheory.BaseChangeInduction.baseChange_induction
  | (apply _root_.GlobalTheory.BaseChangeInduction.baseChange_induction <;> assumption)
  | (intros; apply _root_.GlobalTheory.BaseChangeInduction.baseChange_induction <;> assumption)
  | (intros; apply @_root_.GlobalTheory.BaseChangeInduction.baseChange_induction <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.BaseChangeInduction.baseChange_induction ..)

theorem exists_crystalline_epsilon_combination {l : ℕ} [Fact l.Prime] {a e : ℕ} {O K : Type} [CommRing O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [CharZero K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {R : Type} [CommRing R] (Q : Obj l R) (toA : Q.A → ZMod a → K⟦X⟧) {J : Type} [Fintype J] (o : J → O)
    (hspan : ∀ f : ZMod a → K⟦X⟧, (∀ τ, f τ ∈ A O K) → ∃ w : J → Q.A, ∀ τ,
      f τ = ∑ k, PowerSeries.C (algebraMap O K (o k)) * toA (w k) τ)
    (P : PhiMod O K l e a ι) (EE : FCrys l R) (c : EE.M Q →+ Vec K a ι) (hinj : Function.Injective c)
    (hmem : ∀ x, c x ∈ P.M) (hsurj : ∀ m ∈ P.M, ∃ x, c x = m)
    (hw : ∀ (w : Q.A) (x : EE.M Q), c (w • x) = fun τ i => toA w τ * c x τ i)
    (hU : ∀ o : O, ∃ U : FHom EE EE, ∀ x,
      c (U.u Q x) = fun τ i => PowerSeries.C (algebraMap O K o) * c x τ i)
    (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hsh : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f)
    (PP : Obj l R) (p₀ p₁ : GlobalTheory.Prism.Hom Q PP) (j : ZMod a → PP.A →+* K⟦X⟧⟦X⟧)
    (lam₀ lam₁ : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧))
    (hl₀ : ∀ (r : PP.A) (y : EE.M PP) τ i, lam₀ (r • y) τ i = j τ r * lam₀ y τ i)
    (hl₁ : ∀ (r : PP.A) (y : EE.M PP) τ i, lam₁ (r • y) τ i = j τ r * lam₁ y τ i)
    (ht₀ : ∀ x τ i, lam₀ (EE.tr p₀ x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i)))
    (ht₁ : ∀ x τ i, lam₁ (EE.tr p₁ x) τ i = sh (frob K l (c x (τ - 1) i))) :
    ∃ ε : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧, ∀ y τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ := by
  have hb : ∀ k : ι, (fun _ => Pi.single k 1 : Vec K a ι) ∈ P.M := fun k => mem_tot.2 fun τ i => by
    rcases eq_or_ne i k with rfl | h
    · simp only [Pi.single_eq_same]; exact one_mem _
    · simp only [Pi.single_eq_of_ne h]; exact zero_mem _
  choose b hb using fun k => hsurj _ (hb k)
  choose U hU using hU
  refine ⟨fun τ => Matrix.of fun i k => lam₀ (EE.tr p₁ (b k)) τ i, ?_⟩
  set ε : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧ := fun τ => Matrix.of fun i k => lam₀ (EE.tr p₁ (b k)) τ i with hε

  have hU₀ : ∀ o y τ i, lam₀ ((U o).u PP y) τ i =
      PowerSeries.C (PowerSeries.C (algebraMap O K o)) * lam₀ y τ i := by
    intro o y
    refine bc_induction (EE.tr_bc p₀) (fun y => ∀ τ i, lam₀ ((U o).u PP y) τ i =
      PowerSeries.C (PowerSeries.C (algebraMap O K o)) * lam₀ y τ i) ?_ ?_ ?_ ?_ y
    · intro τ i; simp
    · intro y z hy hz τ i
      simp only [map_add (f := _), Pi.add_apply, hy, hz, mul_add]
    · intro r y hy τ i
      rw [map_smul, hl₀, hl₀, hy]; ring
    · intro x τ i
      rw [(U o).u_tr, ht₀, ht₀, hU]
      simp only [map_mul, frob_C]
  have hU₁ : ∀ o x τ i, lam₁ ((U o).u PP (EE.tr p₁ x)) τ i =
      PowerSeries.C (PowerSeries.C (algebraMap O K o)) * lam₁ (EE.tr p₁ x) τ i := by
    intro o x τ i
    rw [(U o).u_tr, ht₁, ht₁, hU]
    simp only [map_mul, frob_C, shift_C sh hsh]
  have hS0 : ∀ τ, lam₀ 0 τ = ε τ *ᵥ lam₁ 0 τ := by intro τ; simp
  have hSadd : ∀ y z, (∀ τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ) → (∀ τ, lam₀ z τ = ε τ *ᵥ lam₁ z τ) →
      ∀ τ, lam₀ (y + z) τ = ε τ *ᵥ lam₁ (y + z) τ := by
    intro y z hy hz τ
    simp only [map_add (f := _), Pi.add_apply, hy, hz, Matrix.mulVec_add]
  have hSs : ∀ (r : PP.A) y, (∀ τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ) →
      ∀ τ, lam₀ (r • y) τ = ε τ *ᵥ lam₁ (r • y) τ := by
    intro r y hy τ
    have e0 : lam₀ (r • y) τ = j τ r • lam₀ y τ := funext fun i => hl₀ r y τ i
    have e1 : lam₁ (r • y) τ = j τ r • lam₁ y τ := funext fun i => hl₁ r y τ i
    rw [e0, e1, hy, Matrix.mulVec_smul]
  have hSU : ∀ o x, (∀ τ, lam₀ (EE.tr p₁ x) τ = ε τ *ᵥ lam₁ (EE.tr p₁ x) τ) →
      ∀ τ, lam₀ (EE.tr p₁ ((U o).u _ x)) τ = ε τ *ᵥ lam₁ (EE.tr p₁ ((U o).u _ x)) τ := by
    intro o x hx τ
    rw [← (U o).u_tr]
    have e0 : lam₀ ((U o).u PP (EE.tr p₁ x)) τ =
        (PowerSeries.C (PowerSeries.C (algebraMap O K o)) : K⟦X⟧⟦X⟧) • lam₀ (EE.tr p₁ x) τ :=
      funext fun i => hU₀ o _ τ i
    have e1 : lam₁ ((U o).u PP (EE.tr p₁ x)) τ =
        (PowerSeries.C (PowerSeries.C (algebraMap O K o)) : K⟦X⟧⟦X⟧) • lam₁ (EE.tr p₁ x) τ :=
      funext fun i => hU₁ o _ τ i
    rw [e0, e1, hx, Matrix.mulVec_smul]
  have hSb : ∀ k τ, lam₀ (EE.tr p₁ (b k)) τ = ε τ *ᵥ lam₁ (EE.tr p₁ (b k)) τ := by
    intro k τ
    have e1 : lam₁ (EE.tr p₁ (b k)) τ = Pi.single k 1 := funext fun i => by
      rw [ht₁, hb]
      rcases eq_or_ne i k with rfl | h
      · simp only [Pi.single_eq_same, map_one]
      · simp only [Pi.single_eq_of_ne h, map_zero]
    rw [e1, Matrix.mulVec_single_one]
    rfl
  refine bc_induction (EE.tr_bc p₁) (fun y => ∀ τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ) hS0 hSadd hSs fun x => ?_
  choose w hwx using fun i => hspan (fun τ => c x τ i) fun τ => mem_tot.1 (hmem x) τ i
  have hx : x = ∑ i, ∑ k, (U (o k)).u _ (w i k • b i) := by
    apply hinj
    funext τ i

    simp only [map_sum, Finset.sum_apply, hU, hw, hb]
    rw [Finset.sum_eq_single i]
    · simp only [Pi.single_eq_same, mul_one]
      exact hwx i τ
    · intro i' _ h
      simp only [Pi.single_eq_of_ne h.symm, mul_zero, Finset.sum_const_zero]
    · simp

  rw [hx, map_sum]
  refine Finset.sum_induction _ (fun y => ∀ τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ) hSadd hS0 fun i _ => ?_

  rw [map_sum]
  refine Finset.sum_induction _ (fun y => ∀ τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ) hSadd hS0 fun k _ => ?_
  refine hSU _ _ ?_
  rw [LinearMap.map_smulₛₗ]
  exact hSs _ _ (hSb i)

theorem exists_eps : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), Function.Injective c → (∀ x, c x ∈ P.M) → (∀ m ∈ P.M, ∃ x, c x = m) → (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → (∀ o : O, ∃ U : FHom EE EE, ∀ x, c (U.u (ϖ.prism a) x) = fun τ i => PowerSeries.C (algebraMap O K o) * c x τ i) → ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (j : ZMod a → PP.A →+* K⟦X⟧⟦X⟧), (∀ τ (x : (Wq l a)⟦X⟧), j τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧) ∧ j τ (p₁.f x) = sh (toAc t K (frobS l a x) τ : K⟦X⟧)) → ∀ (lam₀ lam₁ : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧)), (∀ (r : PP.A) (y : EE.M PP) τ i, lam₀ (r • y) τ i = j τ r * lam₀ y τ i) → (∀ (r : PP.A) (y : EE.M PP) τ i, lam₁ (r • y) τ i = j τ r * lam₁ y τ i) → (∀ x τ i, lam₀ (EE.tr p₀ x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i))) → (∀ x τ i, lam₁ (EE.tr p₁ x) τ i = sh (frob K l (c x (τ - 1) i))) → ∃ ε : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧, ∀ y τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P EE c hinj hmem hsurj hw hU sh hsh PP p₀ p₁ j _
    lam₀ lam₁ hl₀ hl₁ ht₀ ht₁
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  refine exists_crystalline_epsilon_combination (ϖ.prism a) (fun w τ => (toAc t K w τ : K⟦X⟧)) (Module.Free.chooseBasis ℤ_[l] O) ?_
    P EE c hinj hmem hsurj hw hU sh hsh PP p₀ p₁ j lam₀ lam₁ hl₀ hl₁ ht₀ ht₁
  intro f hf
  obtain ⟨w, hw⟩ := exists_eq_sum_toAc t K (Module.Free.chooseBasis ℤ_[l] O) fun τ => ⟨f τ, hf τ⟩
  refine ⟨w, fun τ => ?_⟩
  refine (congrArg Subtype.val (congrFun hw τ)).trans ?_
  rw [Finset.sum_apply, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, Subalgebra.coe_smul, Algebra.smul_def, algebraMap_eq_C]

end GlobalTheory.BKGal.CrysEps
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory

theorem phiModuleHom_shortExact_split_wittTilt {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {G : Type}
    [Group G] [TopologicalSpace G] {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype μ] [DecidableEq μ] {P₀ : PhiMod O K l e a ι} {P₁ : PhiMod O K l e a κ} {P₂ : PhiMod O K l e a μ}
    {T₀ T₁ T₂ : LocLat G ℚ_[l] K O} {I₀ : Ident t ϖ P₀ T₀} {I₁ : Ident t ϖ P₁ T₁} {I₂ : Ident t ϖ P₂ T₂}
    {f : LatHom T₀.L T₁.L} {g : LatHom T₁.L T₂.L} {F : GlobalTheory.BK.Hom P₀ P₁} {H : GlobalTheory.BK.Hom P₁ P₂}
    (hS : IsSESLat (Qp := ℚ_[l]) f g) (hF : IsMapOf I₀ I₁ f F) (hH : IsMapOf I₁ I₂ g H) :
    (∃ Z : Matrix κ μ (OW l O), (homMat t ϖ H).map (inclO l O) * Z = 1) ∧
      (∃ Y : Matrix ι κ (OW l O), Y * (homMat t ϖ F).map (inclO l O) = 1) := by
  classical

  let g₁ : ↥T₁.L.T →ₗ[O] ↥T₂.L.T := (g.f.restrictScalars O).restrict g.T_le
  let f₁ : ↥T₀.L.T →ₗ[O] ↥T₁.L.T := (f.f.restrictScalars O).restrict f.T_le
  have hg₁s : Function.Surjective g₁ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := hS.2.2.1 y hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  haveI : Module.Free O ↥T₂.L.T := T₂.L.free
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g₁ LinearMap.id hg₁s
  have hs' : ∀ y, g₁ (s y) = y := fun y => LinearMap.congr_fun hs y
  have hf₁i : Function.Injective f₁ := fun x y h => Subtype.ext (hS.1 (congrArg Subtype.val h))
  have hgf : ∀ y, g₁ (f₁ y) = 0 := fun y => Subtype.ext ((hS.2.2.2.1 _).2 ⟨y, rfl⟩)
  let p : ↥T₁.L.T →ₗ[O] ↥T₁.L.T := LinearMap.id - s ∘ₗ g₁
  have hp : ∀ x, p x ∈ LinearMap.range f₁ := by
    intro x
    have h0 : g₁ (p x) = 0 := by
      simp only [p, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, hs', sub_self]
    obtain ⟨y, hy⟩ := (hS.2.2.2.1 _).1 (congrArg Subtype.val h0)
    have hy0 : y ∈ T₀.L.T := hS.2.2.2.2 y (hy ▸ (p x).2)
    exact ⟨⟨y, hy0⟩, Subtype.ext hy⟩
  let r : ↥T₁.L.T →ₗ[O] ↥T₀.L.T :=
    (LinearEquiv.ofInjective f₁ hf₁i).symm.toLinearMap ∘ₗ p.codRestrict (LinearMap.range f₁) hp
  have hr : ∀ y, r (f₁ y) = y := by
    intro y
    have h1 : p.codRestrict (LinearMap.range f₁) hp (f₁ y) = LinearEquiv.ofInjective f₁ hf₁i y := by
      apply Subtype.ext
      simp [p, hgf]
    simp only [r, LinearMap.comp_apply, h1, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

  let Sw := s.baseChange (OW l O)
  let Rw := r.baseChange (OW l O)
  have hSw : ∀ x, latW g (Sw x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c y =>
      simp only [Sw, LinearMap.baseChange_tmul, latW, TensorProduct.map_tmul, LinearMap.id_apply]
      exact congrArg _ (hs' y)
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hRw : ∀ x, Rw (latW f x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c y =>
      simp only [Rw, LinearMap.baseChange_tmul, latW, TensorProduct.map_tmul, LinearMap.id_apply]
      exact congrArg _ (hr y)
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

  let SL : (μ → OW l O) →ₗ[OW l O] (κ → OW l O) := I₁.j.symm.toLinearMap ∘ₗ Sw ∘ₗ I₂.j.toLinearMap
  let RL : (κ → OW l O) →ₗ[OW l O] (ι → OW l O) := I₀.j.symm.toLinearMap ∘ₗ Rw ∘ₗ I₁.j.toLinearMap
  have hSL : homW t ϖ H ∘ₗ SL = LinearMap.id := by
    refine LinearMap.ext fun v => I₂.j.injective ?_
    rw [LinearMap.comp_apply, hH]
    simp only [SL, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hSw,
      LinearMap.id_apply]
  have hRL : RL ∘ₗ homW t ϖ F = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    change I₀.j.symm (Rw (I₁.j (homW t ϖ F v))) = v
    rw [hF, hRw, LinearEquiv.symm_apply_apply]
  have hM : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (M : Matrix α β (OW l O)), LinearMap.toMatrix' M.mulVecLin = M := fun M => LinearMap.toMatrix'_toLin' M
  refine ⟨⟨LinearMap.toMatrix' SL, ?_⟩, ⟨LinearMap.toMatrix' RL, ?_⟩⟩
  · have h := congrArg LinearMap.toMatrix' hSL
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at h
    rw [← h, homW, hM]
  · have h := congrArg LinearMap.toMatrix' hRL
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at h
    rw [← h, homW, hM]

end GlobalTheory
end
