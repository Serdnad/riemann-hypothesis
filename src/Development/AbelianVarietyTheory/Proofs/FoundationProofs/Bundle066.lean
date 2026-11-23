module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle026
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.EqZeroOrSingleOfDegreeLtTwo
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle030
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle032
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem apply_eq_one_of_triv_one_unit {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {χ : kˣ →* ℂˣ} (h : Triv χ 1) (u : kˣ) (hu : valuation k (u : k) = 1) : χ u = 1 := by
  apply h u hu
  calc valuation k ((u : k) - 1) ≤ max (valuation k (u : k)) (valuation k 1) := Valuation.map_sub _ _ _
    _ = valuation k 1 := by simp [hu]

theorem cut_or_const : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → (∃ r : ℕ, 0 < r ∧ r < n ∧ Cut ψ r) ∨ ∃ χ : kˣ →* ℂˣ, ((∀ i, IsSmoothChar (ψ i)) → IsSmoothChar χ) ∧ Agree ψ (fun _ => χ) := by
  intro k _ _ _ _ n ψ hord
  by_cases hc : ∃ m : ℕ, ∃ h : m + 1 < n, ¬ Triv (ψ ⟨m, by omega⟩ / ψ ⟨m + 1, h⟩) 1
  · obtain ⟨m, hm, hnt⟩ := hc
    refine Or.inl ⟨m + 1, by omega, hm, ?_⟩
    intro i j hi hj htr
    have h1 : i ≤ (⟨m, by omega⟩ : Fin n) := by rw [Fin.le_def]; simp; omega
    have h2 : (⟨m, by omega⟩ : Fin n) ≤ ⟨m + 1, hm⟩ := by rw [Fin.le_def]; simp
    have h3 : (⟨m + 1, hm⟩ : Fin n) ≤ j := by rw [Fin.le_def]; simp; omega
    exact hnt (hord i _ _ j h1 h2 h3 1 htr)
  · push_neg at hc
    right
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      refine ⟨1, fun _ => ?_, fun i => i.elim0⟩
      show IsOpen ((1 : kˣ →* ℂˣ).ker : Set kˣ)
      simp
    · refine ⟨ψ ⟨0, hn⟩, fun hs => hs _, ?_⟩
      have key : ∀ m (hm : m < n) (u : kˣ), valuation k (u : k) = 1 → ψ ⟨m, hm⟩ u = ψ ⟨0, hn⟩ u := by
        intro m
        induction m with
        | zero => intro _ _ _; rfl
        | succ m ih =>
          intro hm u hu
          have h1 := apply_eq_one_of_triv_one_unit (hc m hm) u hu
          rw [MonoidHom.div_apply, div_eq_one] at h1
          rw [← h1, ih (by omega) u hu]
      intro i u hu
      exact key i.1 i.2 u hu

end GlobalTheory.PsType
end

section

open GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt

theorem isDerOn_iSup_glue (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M]
    [Module S M] (B : ℕ → Subalgebra A S) (hB : Monotone B) (D : ℕ → S → M)
    (hDer : ∀ m, IsDerOn (B m) (D m)) (hcomp : ∀ m, ∀ x ∈ B m, D (m + 1) x = D m x) :
    ∃ D' : S → M, IsDerOn (⨆ m, B m) D' ∧ ∀ m, ∀ x ∈ B m, D' x = D m x := by
  classical
  have hD : ∀ m k, m ≤ k → ∀ x ∈ B m, D k x = D m x := by
    intro m k hmk
    induction k, hmk using Nat.le_induction with
    | base => intro x _; rfl
    | succ k hmk ih =>
      intro x hx
      rw [hcomp k x (hB hmk hx), ih x hx]
  let D' : S → M := fun x => if h : ∃ m, x ∈ B m then D (Nat.find h) x else 0
  have hD' : ∀ m, ∀ x ∈ B m, D' x = D m x := by
    intro m x hx
    have h : ∃ m, x ∈ B m := ⟨m, hx⟩
    simp only [D', dif_pos h]
    exact (hD _ m (Nat.find_min' h hx) x (Nat.find_spec h)).symm
  have hmem : ∀ x ∈ (⨆ m, B m), ∃ m, x ∈ B m := fun x hx =>
    by
    have := hx
    rw [← SetLike.mem_coe, Subalgebra.coe_iSup_of_directed hB.directed_le, Set.mem_iUnion] at this
    exact this
  refine ⟨D', ⟨?_, ?_, ?_⟩, hD'⟩
  · intro x hx y hy
    obtain ⟨m, hm⟩ := hmem x hx
    obtain ⟨n, hn⟩ := hmem y hy
    have hx' : x ∈ B (max m n) := hB (le_max_left m n) hm
    have hy' : y ∈ B (max m n) := hB (le_max_right m n) hn
    rw [hD' _ _ (add_mem hx' hy'), hD' _ _ hx', hD' _ _ hy', (hDer _).add x hx' y hy']
  · intro x hx y hy
    obtain ⟨m, hm⟩ := hmem x hx
    obtain ⟨n, hn⟩ := hmem y hy
    have hx' : x ∈ B (max m n) := hB (le_max_left m n) hm
    have hy' : y ∈ B (max m n) := hB (le_max_right m n) hn
    rw [hD' _ _ (mul_mem hx' hy'), hD' _ _ hx', hD' _ _ hy', (hDer _).mul x hx' y hy']
  · intro a
    rw [hD' 0 _ ((B 0).algebraMap_mem a), (hDer 0).alg a]

end GlobalTheory.AlmostEt
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem exists_int_exponent_cyclotomic {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (l : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) (n M : ℕ) (hM : 0 < M) (hd : l ^ n ∣ M) :
    ∃ e : ℤ, (∀ ζ : Ω, IsPrimitiveRoot ζ M → s ζ = ζ ^ e) ∧
      (e : ℤ_[l]) - (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) ∈ (idl l) ^ n := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : CharZero Ω := algebraRat.charZero Ω
  have : NeZero M := ⟨hM.ne'⟩
  have : NeZero (M : Ω) := ⟨Nat.cast_ne_zero.mpr hM.ne'⟩
  have : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨e, he⟩ := rootsOfUnity.integer_power_of_ringEquiv M s.toRingEquiv
  have hs : ∀ ζ : Ω, IsPrimitiveRoot ζ M → s ζ = ζ ^ e := by
    intro ζ hζ
    have h := he hζ.toRootsOfUnity
    simpa [Units.val_zpow_eq_zpow_val] using h
  refine ⟨e, hs, ?_⟩
  obtain ⟨k, hk⟩ := hd
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  have hη : IsPrimitiveRoot (ζ ^ k) (l ^ n) := hζ.pow hM (by rw [hk, mul_comm])
  have hsη : s (ζ ^ k) = (ζ ^ k) ^ e := by
    rw [map_pow, hs ζ hζ, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]
  set c := (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) with hc
  have hpow : (ζ ^ k) ^ (l ^ n) = 1 := hη.pow_eq_one
  have hspec := cyclotomicCharacter.spec (L := Ω) l s.toRingEquiv (ζ ^ k) hpow
  have heq : (ζ ^ k) ^ e = (ζ ^ k) ^ (((cyclotomicCharacter Ω l s.toRingEquiv).val.toZModPow n).val : ℤ) := by
    rw [← hsη, zpow_natCast]
    exact hspec
  have hdvd : ((l ^ n : ℕ) : ℤ) ∣ e - (((cyclotomicCharacter Ω l s.toRingEquiv).val.toZModPow n).val : ℤ) := by
    rw [← hη.zpow_eq_one_iff_dvd, zpow_sub₀ (hη.ne_zero (NeZero.ne _)), heq, div_self]
    exact zpow_ne_zero _ (pow_ne_zero _ (hζ.ne_zero (NeZero.ne _)))
  have hz : (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)) ((e : ℤ_[l]) - c) = 0 := by
    rw [map_sub, map_intCast, hc]
    rw [sub_eq_zero]
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (l ^ n)).mpr hdvd
    rw [Int.cast_sub, sub_eq_zero] at this
    rw [this]
    simp
  have hmem : (e : ℤ_[l]) - c ∈ RingHom.ker (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)) := hz
  rw [PadicInt.ker_toZModPow, ← Ideal.span_singleton_pow] at hmem
  exact hmem

end GlobalTheory.KZ
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.UnClosure

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem one_mem (X : Tower Ω ε) (m : ℕ) : 1 ∈ X.Un m := by
  intro W _
  exact ⟨1, by simp⟩

theorem mul_mem (X : Tower Ω ε) (m : ℕ) (f g : X.Kˣ) (hf : f ∈ X.Un m) (hg : g ∈ X.Un m) :
    f * g ∈ X.Un m := by
  intro W hW
  obtain ⟨a, ha⟩ := hf W hW
  obtain ⟨b, hb⟩ := hg W hW
  refine ⟨a * b, ?_⟩
  have e : ((f * g : X.Kˣ) : X.K) / ((a * b : X.Kˣ) : X.K) ^ m
      = ((f : X.K) / (a : X.K) ^ m) * ((g : X.K) / (b : X.K) ^ m) := by
    push_cast; rw [mul_pow]; field_simp
  rw [e, map_mul, ha, hb, one_mul]

theorem inv_mem (X : Tower Ω ε) (m : ℕ) (f : X.Kˣ) (hf : f ∈ X.Un m) : f⁻¹ ∈ X.Un m := by
  intro W hW
  obtain ⟨a, ha⟩ := hf W hW
  refine ⟨a⁻¹, ?_⟩
  have e : ((f⁻¹ : X.Kˣ) : X.K) / ((a⁻¹ : X.Kˣ) : X.K) ^ m = ((f : X.K) / (a : X.K) ^ m)⁻¹ := by
    push_cast; rw [inv_pow]; field_simp
  rw [e, map_inv₀, ha, inv_one]

theorem pow_mem_self (X : Tower Ω ε) (m : ℕ) (g : X.Kˣ) : g ^ m ∈ X.Un m := by
  intro W _
  refine ⟨g, ?_⟩
  have e : ((g ^ m : X.Kˣ) : X.K) / (g : X.K) ^ m = 1 := by
    push_cast; exact div_self (pow_ne_zero _ g.ne_zero)
  rw [e, map_one]

theorem mem_of_mem_mul (X : Tower Ω ε) (m k : ℕ) (f : X.Kˣ) (hf : f ∈ X.Un (m * k)) : f ∈ X.Un m := by
  intro W hW
  obtain ⟨a, ha⟩ := hf W hW
  refine ⟨a ^ k, ?_⟩
  have e : ((a ^ k : X.Kˣ) : X.K) ^ m = (a : X.K) ^ (m * k) := by
    push_cast; rw [← pow_mul, mul_comm]
  rw [e]; exact ha

theorem pow_mem (X : Tower Ω ε) (m k : ℕ) (f : X.Kˣ) (hf : f ∈ X.Un m) : f ^ k ∈ X.Un m := by
  intro W hW
  obtain ⟨a, ha⟩ := hf W hW
  refine ⟨a ^ k, ?_⟩
  have e : ((f ^ k : X.Kˣ) : X.K) / ((a ^ k : X.Kˣ) : X.K) ^ m = ((f : X.K) / (a : X.K) ^ m) ^ k := by
    push_cast; rw [div_pow, ← pow_mul, ← pow_mul, mul_comm m k]
  rw [e, map_pow, ha, one_pow]

theorem val_eq_one_of_pow {K : Type} [Field K] (W : ValuationSubring K) (x : K) (m : ℕ) (hm : 0 < m)
    (h : W.valuation (x ^ m) = 1) : W.valuation x = 1 := by
  rw [map_pow] at h
  exact (pow_eq_one_iff.1 h).resolve_right hm.ne'

theorem mem_of_pow_mem (X : Tower Ω ε) (m k : ℕ) (g : X.Kˣ) (hm : 0 < m) (hg : g ^ m ∈ X.Un (m * k)) :
    g ∈ X.Un k := by
  intro W hW
  obtain ⟨a, ha⟩ := hg W hW
  refine ⟨a, val_eq_one_of_pow W _ m hm ?_⟩
  have e : ((g : X.K) / (a : X.K) ^ k) ^ m = ((g ^ m : X.Kˣ) : X.K) / (a : X.K) ^ (m * k) := by
    push_cast; rw [div_pow, ← pow_mul, mul_comm k m]
  rw [e]; exact ha

end GlobalTheory.KZ.UnClosure

namespace GlobalTheory.KZ.UnClosure

theorem un_closure : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ (m : ℕ), 1 ∈ X.Un m ∧ (∀ f g, f ∈ X.Un m → g ∈ X.Un m → f * g ∈ X.Un m) ∧ (∀ f, f ∈ X.Un m → f⁻¹ ∈ X.Un m) ∧
      (∀ g : X.Kˣ, g ^ m ∈ X.Un m) ∧ (∀ (k : ℕ) f, f ∈ X.Un (m * k) → f ∈ X.Un m) ∧
      (∀ (k : ℕ) f, f ∈ X.Un m → f ^ k ∈ X.Un m) ∧
      ∀ (k : ℕ) (g : X.Kˣ), 0 < m → g ^ m ∈ X.Un (m * k) → g ∈ X.Un k := by
  intro Ω _ _ _ ε X _ _ m
  exact ⟨one_mem X m, mul_mem X m, inv_mem X m, pow_mem_self X m, fun k f hf => mem_of_mem_mul X m k f hf,
    fun k f hf => pow_mem X m k f hf, fun k g hm hg => mem_of_pow_mem X m k g hm hg⟩

end GlobalTheory.KZ.UnClosure
end

section

noncomputable section

open Finset
open scoped Classical
open GlobalTheory.KummerEisensteinGalois GlobalTheory.KummerEisensteinGalois.Smoothing

namespace GlobalTheory.TameSmoothing

variable {K : Type*} [Field K] [CharZero K]

theorem modEq_scale_tame {N q : ℕ} [NeZero q] (e : ℤ) (y : ZMod q) (s : ℤ) :
    e * ((N : ℤ) * y.val + (q : ℤ) * s) ≡ (N : ℤ) * ((e : ZMod q) * y).val + (q : ℤ) * (e * s)
      [ZMOD ((N * q : ℕ) : ℤ)] := by
  have h : ((e * (y.val : ℤ) : ℤ) : ZMod q) = (((((e : ZMod q) * y).val : ℕ) : ℤ) : ZMod q) := by
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  obtain ⟨w, hw⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h
  rw [Int.modEq_iff_dvd]
  exact ⟨w, by push_cast; linear_combination (N : ℤ) * hw⟩

theorem eisF_scale_tame {j N p n : ℕ} [NeZero p] (hN : 0 < N) {ζ : K} (hζ : ζ ^ (N * p ^ n) = 1) (e : ℤ)
    (γ δ : GL (Fin 2) (ZMod (p ^ n))) (i : Fin 2) (w : ℤ × ℤ)
    (h : ∀ l, (δ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i l =
      (e : ZMod (p ^ n)) * (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i l) :
    eisF j (N * p ^ n) ζ (e * (rowT N p n γ i w).1) (e * (rowT N p n γ i w).2) =
      eisF j (N * p ^ n) ζ (rowT N p n δ i (e * w.1, e * w.2)).1 (rowT N p n δ i (e * w.1, e * w.2)).2 := by
  have hM : 0 < N * p ^ n := Nat.mul_pos hN (Nat.pos_of_ne_zero (NeZero.ne _))
  refine eisF_congr_mod hM hζ ?_ ?_
  · have := modEq_scale_tame (N := N) e ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i 0) w.1
    simpa only [rowT, h, Nat.cast_pow] using this
  · have := modEq_scale_tame (N := N) e ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i 1) w.2
    simpa only [rowT, h, Nat.cast_pow] using this

theorem sum_scaled_tame (p : ℕ) [hp : Fact p.Prime] (N n m k : ℕ) (ψ : DirichletCharacter K (p ^ m))
    (c d : ℤ) (w w' : ℤ × ℤ) (ζ : K) (hζ : IsPrimitiveRoot ζ (N * p ^ n)) (hN : 0 < N) (hm : 1 ≤ m) (hmn : m ≤ n)
    (hpc : ¬ (p : ℤ) ∣ c) (hpd : ¬ (p : ℤ) ∣ d) (r : ℕ) :
    ∑ γ ∈ unitSet p n, ψ (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))).det.val : ℕ) : ZMod (p ^ m)) *
      cmul (eisF (k - 1) (N * p ^ n) ζ (c * (rowT N p n γ 0 w).1) (c * (rowT N p n γ 0 w).2))
           (eisF 1 (N * p ^ n) ζ (d * (rowT N p n γ 1 w').1) (d * (rowT N p n γ 1 w').2)) r =
    ψ⁻¹ (c : ZMod (p ^ m)) * ψ⁻¹ (d : ZMod (p ^ m)) *
      ∑ γ ∈ unitSet p n, ψ (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))).det.val : ℕ) : ZMod (p ^ m)) *
      cmul (eisF (k - 1) (N * p ^ n) ζ (rowT N p n γ 0 (c * w.1, c * w.2)).1 (rowT N p n γ 0 (c * w.1, c * w.2)).2)
           (eisF 1 (N * p ^ n) ζ (rowT N p n γ 1 (d * w'.1, d * w'.2)).1
             (rowT N p n γ 1 (d * w'.1, d * w'.2)).2) r := by
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have huc : IsUnit (c : ZMod (p ^ n)) := isUnit_intCast_of_not_dvd hpc
  have hud : IsUnit (d : ZMod (p ^ n)) := isUnit_intCast_of_not_dvd hpd
  have hψ : ∀ e : ℤ, ¬ (p : ℤ) ∣ e → ψ⁻¹ (e : ZMod (p ^ m)) * ψ (e : ZMod (p ^ m)) = 1 := by
    intro e he
    rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply (isUnit_intCast_of_not_dvd he)]
  have hcast : ∀ y : ZMod (p ^ n), ((y.val : ℕ) : ZMod (p ^ m)) =
      ZMod.castHom (pow_dvd_pow p hmn) (ZMod (p ^ m)) y := by
    intro y
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (fun γ => diagGL huc.unit hud.unit * γ)
    (fun γ => (diagGL huc.unit hud.unit)⁻¹ * γ) ?_ ?_ ?_ ?_ ?_
  · intro γ hγ
    exact (diagGL_mul_mem hn _ _ γ).mpr hγ
  · intro γ hγ
    refine (diagGL_mul_mem hn huc.unit hud.unit _).mp ?_
    rwa [mul_inv_cancel_left]
  · intro γ _
    exact inv_mul_cancel_left _ _
  · intro γ _
    exact mul_inv_cancel_left _ _
  · intro γ _
    rw [eisF_scale_tame hN hζ.pow_eq_one c γ (diagGL huc.unit hud.unit * γ) 0 w
        (fun l => diagGL_mul_zero _ _ _ l),
      eisF_scale_tame hN hζ.pow_eq_one d γ (diagGL huc.unit hud.unit * γ) 1 w'
        (fun l => diagGL_mul_one _ _ _ l),
      diagGL_mul_det, hcast, hcast, IsUnit.unit_spec, IsUnit.unit_spec,
      map_mul (ZMod.castHom (pow_dvd_pow p hmn) (ZMod (p ^ m))),
      map_mul (ZMod.castHom (pow_dvd_pow p hmn) (ZMod (p ^ m))),
      map_intCast (ZMod.castHom (pow_dvd_pow p hmn) (ZMod (p ^ m))),
      map_intCast (ZMod.castHom (pow_dvd_pow p hmn) (ZMod (p ^ m))), map_mul ψ, map_mul ψ]
    have h1 := hψ c hpc
    have h2 := hψ d hpd
    generalize ψ⁻¹ (c : ZMod (p ^ m)) = A at h1 ⊢
    generalize ψ⁻¹ (d : ZMod (p ^ m)) = B at h2 ⊢
    generalize ψ (c : ZMod (p ^ m)) = A' at h1 ⊢
    generalize ψ (d : ZMod (p ^ m)) = B' at h2 ⊢
    generalize cmul (K := K) _ _ r = T
    generalize ψ (ZMod.castHom _ _ _) = S
    linear_combination (-(S * T)) * h1 - (A * A' * S * T) * h2

theorem pieceT_unitSet_eq_four_pieceTRaw :
    ∀ (p : ℕ) [Fact p.Prime] (N n m k : ℕ) (K : Type) [Field K] [CharZero K] (ψ : DirichletCharacter K (p ^ m)) (c d : ℤ) (w w' : ℤ × ℤ) (ζ : K), IsPrimitiveRoot ζ (N * p ^ n) → 0 < N → ¬ p ∣ N → 1 ≤ m → m ≤ n → 3 ≤ k → ¬ (p : ℤ) ∣ c → ¬ (p : ℤ) ∣ d → ∀ r : ℕ, pieceT N p n m k ψ c d w w' ζ (unitSet p n) r = (c : K) ^ 2 * (d : K) ^ 2 * pieceTRaw N p n m k ψ w w' ζ (unitSet p n) r - (c : K) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (p ^ m)) * (d : K) ^ 2 * pieceTRaw N p n m k ψ (c * w.1, c * w.2) w' ζ (unitSet p n) r - (c : K) ^ 2 * (d : K) * ψ⁻¹ (d : ZMod (p ^ m)) * pieceTRaw N p n m k ψ w (d * w'.1, d * w'.2) ζ (unitSet p n) r + (c : K) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (p ^ m)) * (d : K) * ψ⁻¹ (d : ZMod (p ^ m)) * pieceTRaw N p n m k ψ (c * w.1, c * w.2) (d * w'.1, d * w'.2) ζ (unitSet p n) r := by
  intro p hp N n m k K _ _ ψ c d w w' ζ hζ hN _ hm hmn hk hpc hpd r
  have hp1 : ¬ (p : ℤ) ∣ 1 := (Nat.prime_iff_prime_int.mp hp.out).not_dvd_one
  have h2 := sum_scaled_tame p N n m k ψ 1 d w w' ζ hζ hN hm hmn hp1 hpd r
  have h3 := sum_scaled_tame p N n m k ψ c 1 w w' ζ hζ hN hm hmn hpc hp1 r
  have h4 := sum_scaled_tame p N n m k ψ c d w w' ζ hζ hN hm hmn hpc hpd r
  simp only [one_mul, Int.cast_one, map_one, mul_one, Prod.mk.eta] at h2 h3
  have e1 : (2 : ℤ) - ((k - 1 : ℕ) : ℤ) = 3 - k := by omega
  have e2 : (2 : ℤ) - ((1 : ℕ) : ℤ) = 1 := by norm_num
  have hs : ∀ (e : ℤ) (j M : ℕ) (a b : ℤ), smF e j M ζ a b =
      fun i => (e : K) ^ 2 * eisF j M ζ a b i - (e : K) ^ ((2 : ℤ) - j) * eisF j M ζ (e * a) (e * b) i :=
    fun _ _ _ _ _ => rfl
  unfold pieceT pieceTRaw
  simp only [hs, cmul_expand, e1, e2, zpow_one, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  simp only [mul_left_comm (ψ _), ← Finset.mul_sum]
  rw [h2, h3, h4]
  ring

end GlobalTheory.TameSmoothing
end
end

section

open MvPowerSeries ReciprocityTheory.PGsh

namespace GlobalTheory.FGDepth

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

private theorem jacobian_logFGL_lg_eq_one {d : ℕ} (G : LogFGL v d) :
    FormalSeries.jacobian G.lg = 1 := by
  ext i j
  rw [FormalSeries.jacobian_apply, G.lg_lin i j, Matrix.one_apply]

private theorem exists_subst_inverse_logFGL_lg {d : ℕ} (G : LogFGL v d) :
    ∃ w : Fin d → MvPowerSeries (Fin d) C, (∀ j, constantCoeff (w j) = 0) ∧
      (∀ i, subst w (G.lg i) = X i) ∧ ∀ j, subst G.lg (w j) = X j :=
  FormalSeries.exists_subst_inverse G.lg_const (B := 1)
    (by rw [jacobian_logFGL_lg_eq_one, Matrix.mul_one]) (by rw [jacobian_logFGL_lg_eq_one, Matrix.one_mul])

theorem isExp_expOf {d : ℕ} (G : LogFGL v d) : IsExp G (expOf G) := by
  obtain ⟨w, hw0, hw1, -⟩ := exists_subst_inverse_logFGL_lg G
  exact Classical.epsilon_spec (p := IsExp G) ⟨w, hw0, hw1⟩

theorem isExp_eq_of_subst_lg {d : ℕ} (G : LogFGL v d) {w : Fin d → MvPowerSeries (Fin d) C}
    (h2 : ∀ j, subst G.lg (w j) = X j) {e : Fin d → MvPowerSeries (Fin d) C} (he : IsExp G e) :
    e = w := by
  obtain ⟨he0, he1⟩ := he
  have hlg : HasSubst G.lg := hasSubst_of_constantCoeff_zero G.lg_const
  have hes : HasSubst e := hasSubst_of_constantCoeff_zero he0
  funext j
  calc e j = subst e (X j : MvPowerSeries (Fin d) C) := (subst_X hes j).symm
    _ = subst e (subst G.lg (w j)) := by rw [h2 j]
    _ = subst (fun s => subst e (G.lg s)) (w j) := subst_comp_subst_apply hlg hes (w j)
    _ = subst (X : Fin d → MvPowerSeries (Fin d) C) (w j) := by simp only [he1]
    _ = w j := by rw [subst_self]; rfl

theorem isExp_unique {d : ℕ} (G : LogFGL v d) {e : Fin d → MvPowerSeries (Fin d) C}
    (he : IsExp G e) : e = expOf G := by
  obtain ⟨w, -, -, hw2⟩ := exists_subst_inverse_logFGL_lg G
  rw [isExp_eq_of_subst_lg G hw2 he, isExp_eq_of_subst_lg G hw2 (isExp_expOf G)]

theorem subst_lg_expOf {d : ℕ} (G : LogFGL v d) (a : Fin d) :
    subst G.lg (expOf G a) = (X a : MvPowerSeries (Fin d) C) := by
  obtain ⟨w, -, -, hw2⟩ := exists_subst_inverse_logFGL_lg G
  rw [isExp_eq_of_subst_lg G hw2 (isExp_expOf G)]
  exact hw2 a

theorem expOf_spec {d : ℕ} (G : LogFGL v d) :
    IsExp G (expOf G) ∧ (∀ e, IsExp G e → e = expOf G) ∧
      ∀ a, subst G.lg (expOf G a) = (X a : MvPowerSeries (Fin d) C) :=
  ⟨isExp_expOf G, fun _ he => isExp_unique G he, subst_lg_expOf G⟩

end GlobalTheory.FGDepth
end

section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.derivation_eq_zero_of_isAlgebraicOverPadicIntegers : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ E : Derivation ℤ Ω Ω, (∀ r : ℤ_[p], E (algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) r)) = 0) →
    ∀ x : Ω, IsAlgZp (p := p) x → E x = 0 := by
  first | exact @GlobalTheory.K5.DerAlg.der_algZp | exact GlobalTheory.K5.DerAlg.der_algZp | (intros; apply GlobalTheory.K5.DerAlg.der_algZp <;> assumption)
end

section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.exists_mul_mem_span_algebraicOverPadicIntegers : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ b ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp (p := p) x}),
    ∃ g : O0 p, g ≠ 0 ∧ algebraMap (O0 p) Ω g * b ∈ Submodule.span (O0 p) {x : Ω | IsAlgZp (p := p) x} := by
  first | exact @GlobalTheory.K5.ReprSpan.exists_mul_mem_span | exact GlobalTheory.K5.ReprSpan.exists_mul_mem_span | (intros; apply GlobalTheory.K5.ReprSpan.exists_mul_mem_span <;> assumption)
end

section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.exists_qRoot_poly_of_fixed_geometric_stabilizer_tau : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo (p := p) Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (N : ℕ) (z : Ω), (∀ g ∈ Ggeo (p := p) Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g z = z) →
  ∃ c : ℕ → Ω, (∀ j, ∀ g ∈ Ggeo (p := p) Ω, g (c j) = c j) ∧ z = ∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j :=
  GlobalTheory.K5.Span.span
end

section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.exists_eq_prime_pow_mul_not_dvd_O0 : ∀ (p : ℕ) [Fact p.Prime], ∀ x : O0 p, x ≠ 0 → ∃ (k : ℕ) (y : O0 p), x = (p : O0 p) ^ k * y ∧ ¬ (p : O0 p) ∣ y := by
  first | exact @GlobalTheory.K5.Basic.exists_eq_prime_pow_mul_not_dvd_completedLaurent | exact GlobalTheory.K5.Basic.exists_eq_prime_pow_mul_not_dvd_completedLaurent | (intros; apply GlobalTheory.K5.Basic.exists_eq_prime_pow_mul_not_dvd_completedLaurent <;> assumption)
end
