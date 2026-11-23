module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.KZ GlobalTheory.Glue

namespace GlobalTheory.KummerEisensteinGalois

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} {l : ℕ} [Fact l.Prime]

def seqN (N : ℕ) (j : Ω →+* Qbar l) (φ : HahnSeries ℚ Ω) : ℕ → Qbar l := fun s => j (φ.coeff ((s : ℚ) / N))

def FinSupp (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) : Prop :=
  ∃ S : Finset ℕ, ∀ f : ℕ → Qbar l, (∀ s ∈ S, f s = 0) → lam f = 0

def IsLamOf (X : Tower Ω ε) (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l) (pr : X.Fn l → Fin 2 → Qbar l)
    (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) : Prop :=
  FinSupp lam ∧ ∃ (c : ℕ) (per : ℕ → Qbar l), (∀ n, ‖per n‖ = 1 ∧ Cg n (per (n + 1)) (per n)) ∧
    ∀ (n : ℕ) (b : X.Fn l), b ∈ X.B N l w → ∀ φ : HahnSeries ℚ Ω, IsThB X A N l n b φ →
      Cg (n - c) (lam (seqN N j φ)) (per n * pr b 1)


def IsLamOfL (X : Tower Ω ε) (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l) (pr : X.Fn l → Fin 2 → Qbar l)
    (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) : Prop :=
  FinSupp lam ∧ ∃ (c : ℕ) (per : ℕ → Qbar l), (∀ n, ‖per n‖ = 1 ∧ Cg n (per (n + 1)) (per n)) ∧
    ∀ (n : ℕ), c ≤ n → ∀ (b : X.Fn l), b ∈ X.B N l w → ∀ φ : HahnSeries ℚ Ω, IsThB X A N l n b φ →
      Cg (n - c) (lam (seqN N j φ)) (per n * pr b 1)


theorem norm_l_pow (n : ℕ) : ‖((l : ℕ) : Qbar l) ^ n‖ = ((l : ℝ)⁻¹) ^ n := by
  have : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
  rw [norm_pow, this, norm_algebraMap', Padic.norm_p]

theorem cg_mono {m n : ℕ} (h : m ≤ n) {x y : Qbar l} (hxy : Cg n x y) : Cg m x y := by
  unfold Cg at *
  refine hxy.trans ?_
  rw [norm_l_pow, norm_l_pow]
  have h1 : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_le
  exact pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ h1) h

theorem exists_le_l_pow (l : ℕ) [Fact l.Prime] (t : ℝ) : ∃ k : ℕ, t ≤ (l : ℝ) ^ k := by
  have h1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt t h1
  exact ⟨k, hk.le⟩

theorem l_pow_mul_norm {k m : ℕ} (h : k ≤ m) :
    (l : ℝ) ^ k * ‖((l : ℕ) : Qbar l) ^ m‖ = ‖((l : ℕ) : Qbar l) ^ (m - k)‖ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have h0 : (l : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  rw [norm_l_pow, norm_l_pow, Nat.add_sub_cancel_left, pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ h0, one_pow, one_mul]

theorem cg_sub_iff {c n : ℕ} (h : c ≤ n) (x y : Qbar l) :
    Cg (n - c) x y ↔ ‖x - y‖ ≤ (l : ℝ) ^ c * ‖((l : ℕ) : Qbar l) ^ n‖ := by
  rw [l_pow_mul_norm h]; rfl

theorem cg_mul_left {k m : ℕ} (h : k ≤ m) {a x y : Qbar l} (ha : ‖a‖ ≤ (l : ℝ) ^ k) (hxy : Cg m x y) :
    Cg (m - k) (a * x) (a * y) := by
  rw [cg_sub_iff h, ← mul_sub, norm_mul]
  exact mul_le_mul ha hxy (norm_nonneg _) (by positivity)

theorem seqN_single {N : ℕ} (hN : N ≠ 0) (j : Ω →+* Qbar l) (s : ℕ) (a : Ω) :
    seqN N j (HahnSeries.single ((s : ℚ) / N) a) = Pi.single s (j a) := by
  funext t
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  by_cases h : t = s
  · subst h; simp [seqN]
  · have : (t : ℚ) / N ≠ (s : ℚ) / N := fun e => h (by exact_mod_cast (div_left_inj' hN').1 e)
    simp [seqN, HahnSeries.coeff_single_of_ne this, h]

theorem finSupp_proj (s : ℕ) : FinSupp (LinearMap.proj (R := Qbar l) (φ := fun _ : ℕ => Qbar l) s) :=
  ⟨{s}, fun f hf => hf s (Finset.mem_singleton_self s)⟩

theorem FinSupp.smul {lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l} (h : FinSupp lam) (a : Qbar l) : FinSupp (a • lam) := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, fun f hf => by simp [hS f hf]⟩

theorem FinSupp.add {lam lam' : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l} (h : FinSupp lam) (h' : FinSupp lam') :
    FinSupp (lam + lam') := by
  obtain ⟨S, hS⟩ := h
  obtain ⟨T, hT⟩ := h'
  exact ⟨S ∪ T, fun f hf => by
    simp [hS f fun s hs => hf s (Finset.mem_union_left _ hs), hT f fun s hs => hf s (Finset.mem_union_right _ hs)]⟩

theorem FinSupp.exists_sum {lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l} (h : FinSupp lam) :
    ∃ S : Finset ℕ, ∀ f : ℕ → Qbar l, lam f = ∑ s ∈ S, lam (Pi.single s 1) * f s := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S, fun f => ?_⟩
  have h0 := hS (f - ∑ s ∈ S, f s • (Pi.single s 1 : ℕ → Qbar l)) (fun t ht => by
    simp [Finset.sum_apply, Pi.single_apply, ht])

  rw [map_sub, map_sum, sub_eq_zero] at h0
  rw [h0]
  exact Finset.sum_congr rfl fun s _ => by rw [map_smul, smul_eq_mul, mul_comm]

theorem FinSupp.exists_loss {lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l} (h : FinSupp lam) :
    ∃ c : ℕ, ∀ n, c ≤ n → ∀ f g : ℕ → Qbar l, (∀ s, Cg n (f s) (g s)) → Cg (n - c) (lam f) (lam g) := by
  obtain ⟨S, hS⟩ := h.exists_sum
  obtain ⟨c, hc⟩ := exists_le_l_pow l (∑ s ∈ S, ‖lam (Pi.single s 1)‖)
  refine ⟨c, fun n hn f g hfg => ?_⟩
  rw [cg_sub_iff hn, hS f, hS g, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun s _ => ?_
  rw [← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left (hfg s) (norm_nonneg _)

section Induced

variable {X : Tower Ω ε} {A : ValuationSubring Ω} {N w : ℕ} {j : Ω →+* Qbar l} {pr : X.Fn l → Fin 2 → Qbar l}
  {lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l}

end Induced

end GlobalTheory.KummerEisensteinGalois

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV
open scoped Matrix

namespace GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def SrcL (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : R2 Ω l) : Prop :=
  (∃ (g : Newform (2 * e + 1)) (χ : G ℚ Ω →* (Qbar l)ˣ) (A : ValuationSubring Ω)
      (κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ),
    ¬ l ∣ g.M ∧ ‖ι.symm (g.a l)‖ = 1 ∧ KillsMu l χ ∧
    g.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ)) * (dt W)⁻¹ * χ)) ∧ OverL l A ∧ IsFlagOn W (Dec (F := ℚ) A) κ ∧
    ∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A →
      (κ 1 s : Qbar l) * (cycBar ℚ Ω l (s : G ℚ Ω) : Qbar l) ^ (e : ℤ) * ((dt W (s : G ℚ Ω) : Qbar l)⁻¹ * (χ (s : G ℚ Ω) : Qbar l)) = 1) ∧
  ∀ (A : ValuationSubring Ω) (κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ), OverL l A → IsFlagOn W (Dec (F := ℚ) A) κ →
    ∃ s : ↥(Dec (F := ℚ) A), κ 0 s ≠ cycBar ℚ Ω l s

def VanishOrdL : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ), 1 ≤ e →
    ∀ W : R2 Ω l, admitted ι e W → SrcL ι e W → BlochKatoSelmerVanishes l (Loc.colRep W)

end GlobalTheory.Ord2

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 PowerSeries

namespace GlobalTheory.Col

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def KumVal (n : ℕ) (ζ u : Ω) (s : G ℚ Ω) (k : ZMod (l ^ n)) : Prop :=
  ∃ v : Ω, v ^ (l ^ n) = u ∧ s v = ζ ^ k.val * v

def KumPres (A : ValuationSubring Ω) (n r : ℕ) (ζ : Ω) (Z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) {ι : Type} [Fintype ι]
    (u : ι → Ω) (o : ι → Qbar l) : Prop :=
  IsPrimitiveRoot ζ (l ^ n) ∧ n ≤ r ∧ (∀ i, u i ∈ A ∧ u i ≠ 0 ∧ (u i)⁻¹ ∈ A) ∧ (∀ i, ‖o i‖ ≤ 1) ∧
    ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l r s = 1 → s ζ = ζ →
      ∃ k : ι → ZMod (l ^ n), (∀ i, KumVal n ζ (u i) s (k i)) ∧ Cg n (Z s 1) (∑ i, o i * ((k i).val : Qbar l))

theorem kumVal_unique {n : ℕ} {ζ u : Ω} {s : G ℚ Ω} {k k' : ZMod (l ^ n)} (hζ : IsPrimitiveRoot ζ (l ^ n)) (hs : s ζ = ζ)
    (hu : u ≠ 0) (hk : KumVal n ζ u s k) (hk' : KumVal n ζ u s k') : k = k' := by
  obtain ⟨v, hv, hsv⟩ := hk
  obtain ⟨w, hw, hsw⟩ := hk'
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  haveI : NeZero (l ^ n) := ⟨hpos.ne'⟩
  have hv0 : v ≠ 0 := by rintro rfl; exact hu (by rw [← hv, zero_pow hpos.ne'])
  have hw0 : w ≠ 0 := by rintro rfl; exact hu (by rw [← hw, zero_pow hpos.ne'])
  have h1 : (w / v) ^ (l ^ n) = 1 := by rw [div_pow, hv, hw, div_self hu]
  obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one h1
  have hwv : w = ζ ^ j * v := by rw [hj]; field_simp
  have e1 : s w = ζ ^ k.val * w := by
    rw [hwv, map_mul, map_pow, hs, hsv]; ring
  have e2 : ζ ^ k.val = ζ ^ k'.val := by
    have := e1.symm.trans hsw
    exact mul_right_cancel₀ hw0 this
  exact ZMod.val_injective _ (hζ.pow_inj (ZMod.val_lt k) (ZMod.val_lt k') e2)

theorem kumVal_one (n : ℕ) (ζ : Ω) (s : G ℚ Ω) : KumVal (l := l) n ζ 1 s 0 :=
  ⟨1, one_pow _, by simp⟩

theorem kumPres_empty (A : ValuationSubring Ω) {n r : ℕ} {ζ : Ω} (hζ : IsPrimitiveRoot ζ (l ^ n)) (hnr : n ≤ r)
    (Z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (hZ : ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l r s = 1 → Z s 1 = 0) :
    KumPres A n r ζ Z (ι := Empty) (fun i => i.elim) (fun i => i.elim) := by
  refine ⟨hζ, hnr, fun i => i.elim, fun i => i.elim, fun s hs hc _ => ⟨fun i => i.elim, fun i => i.elim, ?_⟩⟩
  rw [Cg, hZ s hs hc, Finset.sum_eq_zero (fun i _ => i.elim), sub_zero, norm_zero]
  exact norm_nonneg _

theorem fix_of_cycMod [∀ i, HasEnoughRootsOfUnity Ω (l ^ i)] {n r : ℕ} (hnr : n ≤ r) {s : G ℚ Ω}
    (hs : cycMod ℚ Ω l r s = 1) {t : Ω} (ht : t ^ (l ^ n) = 1) : s t = t := by
  have ht' : t ^ (l ^ r) = 1 := by
    obtain ⟨d, hd⟩ := pow_dvd_pow l hnr
    rw [hd, pow_mul, ht, one_pow]
  have h1 := cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) t ht'
  have h2 : (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s)).val.toZModPow r = 1 := by
    have := congrArg Units.val hs
    simpa [cycMod, cycZ] using this
  rw [h2, ZMod.val_one_eq_one_mod] at h1
  have h3 : t ^ (1 % l ^ r) = t := by
    rcases Nat.lt_or_ge 1 (l ^ r) with h | h
    · rw [Nat.mod_eq_of_lt h, pow_one]
    · have e : l ^ r = 1 := le_antisymm h (Nat.one_le_pow _ _ (Fact.out : l.Prime).pos)
      rw [e, Nat.mod_self, pow_zero]
      rw [e, pow_one] at ht'
      exact ht'.symm
  exact h1.trans h3

end GlobalTheory.Col
end
end

section

noncomputable section

open scoped MatrixGroups Matrix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV

namespace GlobalTheory.K4

open GlobalTheory.KZ GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def admitted {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e : ℕ) (gN : Newform (2 * e + 1)) (W : R2 Ω l) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) : Prop :=
  1 < c ∧ 1 < d ∧ Nat.Coprime c (6 * l * N) ∧ Nat.Coprime d (6 * l * N) ∧ IsUnit x ∧
    (∀ b b', pr (b + b') = pr b + pr b') ∧
    (∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l (2 * e - 1) → pr (X.galB l s b) = mat W s *ᵥ pr b) ∧
    ∃ δ : ℕ → Qbar l, ∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ∀ b, b ∈ X.B N l (2 * e - 1) →
      pr (X.heckeT N l q b) = ι.symm (gN.a q) • pr b ∧ pr (X.diam N l q b) = δ q • pr b

def psiCyc {l : ℕ} [Fact l.Prime] (ψ : ZMod l → Qbar l) (s : Ω ≃ₐ[ℚ] Ω) : Qbar l :=
  ψ ((((cycMod (F := ℚ) (Ω := Ω) l 1 s : ZMod (l ^ 1))).val : ℕ) : ZMod l)

def AdmT {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e : ℕ) (gN : Newform (2 * e + 1)) (W : R2 Ω l) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (_gm : (ZMod l)ˣ → SL(2, ℤ))
    (ψ : ZMod l → Qbar l) : Prop :=
  1 ≤ e ∧ 1 < c ∧ 1 < d ∧ Nat.Coprime c (6 * l * N) ∧ Nat.Coprime d (6 * l * N) ∧ IsUnit x ∧
    (ψ 1 = 1 ∧ ∀ a b : (ZMod l)ˣ, ψ ((a * b : (ZMod l)ˣ) : ZMod l) = ψ a * ψ b) ∧
    (∀ b b', pr (b + b') = pr b + pr b') ∧
    (∀ (a : ℤ_[l]) b, pr (a • b) = algebraMap ℚ_[l] (Qbar l) (a : ℚ_[l]) • pr b) ∧
    (∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l (2 * e - 1) →
      pr (X.galB l s b) = ((cycBar ℚ Ω l s : Qbar l) ^ e * (psiCyc ψ s)⁻¹) • (mat W s *ᵥ pr b)) ∧
    ∃ δ : ℕ → Qbar l, ∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ∀ b, b ∈ X.B N l (2 * e - 1) →
      pr (X.heckeT N l q b) = ι.symm (gN.a q) • pr b ∧ pr (X.diam N l q b) = δ q • pr b

def unTw {l : ℕ} [Fact l.Prime] (W : R2 Ω l) (e : ℕ) (χ : G ℚ Ω →* (Qbar l)ˣ) : R2 Ω l :=
  tw W (cycBar ℚ Ω l ^ e * χ⁻¹)

end GlobalTheory.K4
end
end
