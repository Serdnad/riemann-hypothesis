module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisAdaptedLatticeSubspace
public import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingCoeffNonnegOfEventuallyEvalNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2071
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2072
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2073
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle862
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle014
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem

@[expose] public section

section

set_option autoImplicit false

open GlobalTheory.HTLat

namespace GlobalTheory

theorem exists_pow_prime_root_of_card_torsion {M : Type} [CommGroup M] {l : ℕ} [Fact l.Prime]
    {c : ℕ} (hcard : ∀ k : ℕ, Nat.card {x : M // x ^ (l ^ k) = 1} = l ^ (c * k)) (k : ℕ) (y : M)
    (hy : y ^ (l ^ k) = 1) : ∃ z : M, z ^ (l ^ (k + 1)) = 1 ∧ z ^ l = y := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  let T : ℕ → Subgroup M := fun n => (powMonoidHom (l ^ n)).ker
  have hT : ∀ n, Nat.card (T n) = l ^ (c * n) := fun n => by
    rw [← hcard n]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [T, MonoidHom.mem_ker])
  let φ : T (k + 1) →* M := (powMonoidHom l).comp (T (k + 1)).subtype
  have hker : Nat.card φ.ker = l ^ c := by
    rw [← mul_one c, ← hT 1]
    refine Nat.card_congr
      { toFun := fun y => ⟨y.1.1, ?_⟩
        invFun := fun z => ⟨⟨z.1, ?_⟩, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · have := y.2
      simp only [T, φ, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
        powMonoidHom_apply, Subgroup.coe_subtype] at this
      simpa [T, MonoidHom.mem_ker] using this
    · have hz : (z : M) ^ l = 1 := by simpa [T] using MonoidHom.mem_ker.1 z.2
      simp only [T, MonoidHom.mem_ker, powMonoidHom_apply]
      rw [pow_succ' l k, pow_mul, hz, one_pow]
    · have := z.2
      simpa [T, φ, MonoidHom.mem_ker] using this
  have hrange : Nat.card φ.range = l ^ (c * k) := by
    have h1 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker, hker, hT (k + 1), mul_add, mul_one, pow_add, mul_comm] at h1
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hl c) h1
  have hfin : Finite (T k) := Nat.finite_of_card_ne_zero (by rw [hT k]; exact (pow_pos hl _).ne')
  have hle : φ.range ≤ T k := by
    rintro _ ⟨z, rfl⟩
    have := z.2
    simp only [T, MonoidHom.mem_ker, powMonoidHom_apply] at this ⊢
    simp only [φ, MonoidHom.coe_comp, Function.comp_apply, powMonoidHom_apply,
      Subgroup.coe_subtype]
    rw [← pow_mul, ← pow_succ', this]
  have heq : φ.range = T k := Subgroup.eq_of_le_of_card_ge hle (by rw [hrange, hT k])
  have hyT : y ∈ T k := by simpa [T, MonoidHom.mem_ker] using hy
  rw [← heq] at hyT
  obtain ⟨z, hz⟩ := hyT
  exact ⟨z.1, MonoidHom.mem_ker.1 z.2, hz⟩

theorem exists_tate_lev_eq_of_card_torsion :
    ∀ (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime] (c : ℕ),
      (∀ k : ℕ, Nat.card {x : M // x ^ (l ^ k) = 1} = l ^ (c * k)) →
      ∀ (N : ℕ) (x : M), x ^ (l ^ N) = 1 → ∃ t : Tate l M, t.lev N = x := by
  intro M _ l _ c hcard N x hx
  have h := exists_pow_prime_root_of_card_torsion hcard
  choose r hr1 hr2 using h
  let g : (n : ℕ) → {y : M // y ^ (l ^ (N + n)) = 1} := fun n =>
    Nat.rec ⟨x, hx⟩ (fun n y => ⟨r (N + n) y.1 y.2, hr1 (N + n) y.1 y.2⟩) n
  have hg0 : (g 0).1 = x := rfl
  have hgs : ∀ n, (g (n + 1)).1 ^ l = (g n).1 := fun n => hr2 (N + n) (g n).1 (g n).2
  have hgk : ∀ n k, (g (n + k)).1 ^ (l ^ k) = (g n).1 := fun n k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', pow_mul]
      show ((g (n + k + 1)).1 ^ l) ^ (l ^ k) = _
      rw [hgs, ih]
  let s : ℕ → M := fun n => (g n).1 ^ (l ^ N)
  have hs : ∀ n, s n ^ l ^ n = 1 ∧ s (n + 1) ^ l = s n := fun n => by
    refine ⟨?_, ?_⟩
    · simp only [s]
      rw [← pow_mul, ← pow_add, (g n).2]
    · simp only [s]
      rw [← pow_mul, mul_comm, pow_mul, hgs]
  refine ⟨Tate.mk s hs, ?_⟩
  rw [Tate.lev_mk]
  simp only [s]
  have := hgk 0 N
  rw [zero_add] at this
  rw [this, hg0]

end GlobalTheory
end

section

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HTLat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLat.TatePerfect

theorem lev_nsmul {p : ℕ} {M : Type} [CommGroup M] (t : Tate p M) (k n : ℕ) :
    (k • t).lev n = t.lev n ^ k := by
  induction k with
  | zero => rw [zero_nsmul, pow_zero, Tate.lev_zero]
  | succ k ih => rw [succ_nsmul, Tate.lev_add, ih, pow_succ]

theorem lev_congr {p : ℕ} [Fact p.Prime] {M M' : Type} [CommGroup M] [CommGroup M']
    (h2 : ∀ (n : ℕ) (t : Tate p M), t.lev n = 1 ↔ ∃ s : Tate p M, t = (p : ℤ_[p]) ^ n • s)
    (φ : Tate p M →ₗ[ℤ_[p]] Tate p M') {n : ℕ} {t t' : Tate p M} (h : t.lev n = t'.lev n) :
    (φ t).lev n = (φ t').lev n := by
  have e : t = t' + (t - t') := by abel
  have h3 : (t - t').lev n = 1 := by
    have := congrArg (·.lev n) e
    simp only [Tate.lev_add] at this
    rw [h] at this
    exact left_eq_mul.1 this
  obtain ⟨s, hs⟩ := (h2 n _).1 h3
  rw [e, hs, map_add (f := _), map_smul, Tate.lev_add, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, lev_nsmul,
    Tate.lev_pow, _root_.mul_one]

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  (A : Out.PolAV (Sp C))

theorem weilT_flip_surjective
    (h1 : ∀ (n : ℕ) (x : GlobalTheory.ChTor.Pts A.A), x ^ p ^ n = 1 → ∃ t : TateA A p, t.lev n = x)
    (h2 : ∀ (n : ℕ) (t : TateA A p), t.lev n = 1 ↔ ∃ s : TateA A p, t = (p : ℤ_[p]) ^ n • s)
    (φ : TateA A p →ₗ[ℤ_[p]] Tate p Cˣ) : ∃ s : TateA A p, ∀ t, weilT A p t s = φ t := by
  choose! τ hτ using h1
  let κ : ℕ → GlobalTheory.ChTor.Pts A.A → Cˣ := fun n x => (φ (τ n x)).lev n
  have hκ : ∀ n (t : TateA A p), κ n (t.lev n) = (φ t).lev n := fun n t =>
    lev_congr h2 φ (hτ n _ (t.lev_pow n))
  have hm : ∀ n z z', z ^ p ^ n = 1 → z' ^ p ^ n = 1 → κ n (z * z') = κ n z * κ n z' := by
    intro n z z' hz hz'
    have e : z * z' = (τ n z + τ n z').lev n := by rw [Tate.lev_add, hτ n z hz, hτ n z' hz']
    rw [e, hκ, map_add (f := _), Tate.lev_add]
  have hp := fun n => weil_perfect (A := A) (one_le_ppow p n) (κ n) (hm n)
  choose s hs hu using hp
  have hc : ∀ n, s (n + 1) ^ p = s n := by
    intro n
    refine hu n _ ⟨?_, fun z hz => ?_⟩
    · rw [← pow_mul, ← pow_succ']; exact (hs (n + 1)).1
    · have hz' : z ^ p ^ (n + 1) = 1 := by rw [pow_succ, pow_mul, hz, one_pow]
      rw [← weil_level (one_le_ppow p n) (Fact.out : p.Prime).pos hz
        (by rw [← pow_succ]; exact (hs (n + 1)).1), ← pow_succ, (hs (n + 1)).2 z hz']
      have e : z = (p • τ n z).lev (n + 1) := by rw [lev_nsmul, Tate.lev_succ, hτ n z hz]
      conv_lhs => rw [e, hκ, map_nsmul, lev_nsmul, Tate.lev_succ]
  refine ⟨Tate.mk s fun n => ⟨(hs n).1, hc n⟩, fun t => Tate.ext fun n => ?_⟩
  rw [lev_weilT, Tate.lev_mk, (hs n).2 _ (t.lev_pow n), hκ]

theorem eq_zero_of_weilT
    (h1 : ∀ (n : ℕ) (x : GlobalTheory.ChTor.Pts A.A), x ^ p ^ n = 1 → ∃ t : TateA A p, t.lev n = x)
    (s : TateA A p) (hs : ∀ t, weilT A p t s = 0) : s = 0 := by
  refine Tate.ext fun n => ?_
  have hp := weil_perfect (A := A) (one_le_ppow p n) (fun _ => 1) (fun _ _ _ _ => (_root_.mul_one _).symm)
  refine hp.unique ⟨s.lev_pow n, fun z hz => ?_⟩ ⟨(0 : TateA A p).lev_pow n, fun z hz => ?_⟩
  · obtain ⟨t, rfl⟩ := h1 n z hz
    rw [← lev_weilT, hs, Tate.lev_zero]
  · obtain ⟨t, rfl⟩ := h1 n z hz
    rw [← lev_weilT, map_zero, Tate.lev_zero]

end GlobalTheory.HTLat.TatePerfect

namespace GlobalTheory.HTLat

theorem bijective_pairT_of_lev : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (A : Out.PolAV (Sp C)) (ε : Eps p C), (∀ (n : ℕ) (x : GlobalTheory.ChTor.Pts A.A), x ^ p ^ n = 1 → ∃ t : TateA A p, t.lev n = x) → (∀ (n : ℕ) (t : TateA A p), t.lev n = 1 ↔ ∃ s : TateA A p, t = (p : ℤ_[p]) ^ n • s) → Function.Bijective (pairT A ε).flip ∧ Function.Bijective (pairT A ε) := by
  intro p _ C _ _ _ A ε h1 h2
  have hb : Function.Bijective (pairT A ε).flip := by
    constructor
    · refine (injective_iff_map_eq_zero _).2 fun s hs => TatePerfect.eq_zero_of_weilT A h1 s fun t => ?_
      have : ε.equiv.symm (weilT A p t s) = 0 := LinearMap.congr_fun hs t
      exact ε.equiv.symm.map_eq_zero_iff.1 this
    · intro l
      obtain ⟨s, hs⟩ := TatePerfect.weilT_flip_surjective A h1 h2 (ε.equiv.toLinearMap ∘ₗ l)
      refine ⟨s, LinearMap.ext fun t => ?_⟩
      change ε.equiv.symm (weilT A p t s) = l t
      rw [hs]
      exact ε.equiv.symm_apply_apply _
  refine ⟨hb, ?_⟩
  have e : ⇑(pairT A ε) = Neg.neg ∘ ⇑(pairT A ε).flip := by
    funext s
    exact LinearMap.ext fun t => ((isAlt_pairT A ε).neg_eq t s).symm
  rw [e]
  exact (Equiv.neg _).bijective.comp hb

end GlobalTheory.HTLat
end

section

open GlobalTheory.HTLat

namespace GlobalTheory.TateRel

theorem lev_sum {M : Type} [CommGroup M] {l : ℕ} {ι : Type} (s : Finset ι) (f : ι → Tate l M) (N : ℕ) :
    (∑ i ∈ s, f i).lev N = ∏ i ∈ s, (f i).lev N := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, Tate.lev_add, ih]

theorem prod_pow_eq_one (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (φ : Fin n → (M →* M)) (c : Fin n → ℤ_[l]) (h : ∑ i, c i • Tate.map l (φ i) = 0) (N : ℕ)
    (m : Fin n → ℤ) (hm : ∀ i, PadicInt.toZModPow N (c i) = (m i : ZMod (l ^ N)))
    (t : Tate l M) : ∏ i, φ i (t.lev N) ^ m i = 1 := by
  have h0 : ((∑ i, c i • Tate.map l (φ i)) t).lev N = 1 := by rw [h]; rfl
  rw [LinearMap.sum_apply, lev_sum] at h0
  rw [← h0]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, Tate.lev_smul, Tate.lev_map]
  set y := φ i (t.lev N)
  have hy : y ^ ((l ^ N : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast, ← map_pow, Tate.lev_pow, map_one]
  have hc : ((GlobalTheory.PDiv.digit N (c i) : ℕ) : ZMod (l ^ N)) = ((m i : ℤ) : ZMod (l ^ N)) := by
    rw [GlobalTheory.PDiv.cast_digit, hm i]
  have hc' : (((GlobalTheory.PDiv.digit N (c i) : ℕ) : ℤ) : ZMod (l ^ N)) = ((m i : ℤ) : ZMod (l ^ N)) := by
    rw [Int.cast_natCast]; exact hc
  rw [ZMod.intCast_eq_intCast_iff'] at hc'
  rw [zpow_eq_zpow_emod (m i) hy, ← hc', ← zpow_eq_zpow_emod _ hy, zpow_natCast]

end GlobalTheory.TateRel
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HTLat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem tate_free_of_card :
    ∀ (p : ℕ) [Fact p.Prime] (M : Type) [CommGroup M] (r : ℕ), (∀ n : ℕ, Nat.card {x : M // x ^ p ^ n = 1} = p ^ (r * n)) → Nonempty (Tate p M ≃ₗ[ℤ_[p]] (Fin r → ℤ_[p])) ∧ (∀ (n : ℕ) (x : M), x ^ p ^ n = 1 → ∃ t : Tate p M, t.lev n = x) ∧ ∀ (n : ℕ) (t : Tate p M), t.lev n = 1 ↔ ∃ s : Tate p M, t = (p : ℤ_[p]) ^ n • s := by
  intro p _ M _ r h
  obtain ⟨T, _, _, π, hfree, hfin, hrk, hs, h0, hsm, hon, hker, huniq⟩ :=
    GlobalTheory.exists_tateModule_of_card (Additive M) p r (fun n => by
      rw [← h n]
      exact Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun x => Iff.rfl))
  have hkill : ∀ n x, p ^ n • π n x = 0 := fun n x => by
    induction n with
    | zero => simp [h0]
    | succ n ih => rw [pow_succ, mul_smul, hs, ih]
  let f : T →ₗ[ℤ_[p]] Tate p M :=
    { toFun := fun x => Tate.mk (fun n => Additive.toMul (π n x)) fun n =>
        ⟨congrArg Additive.toMul (hkill n x), congrArg Additive.toMul (hs n x)⟩
      map_add' := fun x y => Tate.ext fun n => congrArg Additive.toMul (map_add (π n) x y)
      map_smul' := fun a x => Tate.ext fun n => congrArg Additive.toMul (hsm n a x) }
  have hf : ∀ x n, (f x).lev n = Additive.toMul (π n x) := fun _ _ => rfl
  have hu : ∀ t : Tate p M, ∃! x, ∀ n, π n x = Additive.ofMul (t.lev n) := fun t =>
    huniq (fun n => Additive.ofMul (t.lev n))
      (by have := t.lev_pow 0
          rw [pow_zero, pow_one] at this
          rw [this]; rfl)
      (fun n => congrArg Additive.ofMul (t.lev_succ n))
  have hsurj : Function.Surjective f := fun t => by
    obtain ⟨x, hx, -⟩ := hu t
    exact ⟨x, Tate.ext fun n => by rw [hf, hx]; rfl⟩
  have hinj : Function.Injective f := fun x y hxy =>
    (hu (f y)).unique (fun n => by rw [← hxy]; rfl) (fun n => rfl)
  refine ⟨⟨(LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).symm.trans
    (LinearEquiv.ofFinrankEq _ _ (by simpa using hrk))⟩, fun n x hx => ?_, fun n t => ?_⟩
  · obtain ⟨y, hy⟩ := hon n (Additive.ofMul x) (congrArg Additive.ofMul hx)
    exact ⟨f y, by rw [hf, hy]; rfl⟩
  · obtain ⟨x, rfl⟩ := hsurj t
    have key : ∀ y : T, f (p ^ n • y) = (p : ℤ_[p]) ^ n • f y := fun y => by
      rw [map_nsmul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    refine Iff.trans (hker n x) ⟨?_, ?_⟩
    · rintro ⟨y, rfl⟩
      exact ⟨f y, key y⟩
    · rintro ⟨s, hs'⟩
      obtain ⟨y, rfl⟩ := hsurj s
      exact ⟨y, hinj (hs'.trans (key y).symm)⟩

end GlobalTheory
end

section

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt GlobalTheory.DegCmp Filter
open scoped ENNReal

theorem _root_.GlobalTheory.T.mem_linearSystemConeAlgebra_iff_coeff : ∀ (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (p : Polynomial Ω), p ∈ coneAlg ev ↔ ∀ d : ℕ, p.coeff d ∈ ((LinearMap.range ev) ^ d : Submodule K Ω) := by
  first | exact @GlobalTheory.DegCmp.mem_coneAlg_iff_coeff | exact GlobalTheory.DegCmp.mem_coneAlg_iff_coeff | (intros; apply GlobalTheory.DegCmp.mem_coneAlg_iff_coeff <;> assumption)
end

section

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt GlobalTheory.DegCmp Filter
open scoped ENNReal

theorem _root_.GlobalTheory.T.linearSystemHilbertFunction_eq_finrank_conePiece : ∀ (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (N : ℕ) (b : Module.Basis (Fin N) K V) (τ : ℕ), hilb ev τ = ((Module.finrank K (GlobalTheory.quotPiece (imageIdeal ev b) (τ : ℤ)) : ℕ) : ℕ∞) := by
  first | exact @GlobalTheory.DegCmp.hilb_eq_finrank_quotPiece | exact GlobalTheory.DegCmp.hilb_eq_finrank_quotPiece | (intros; apply GlobalTheory.DegCmp.hilb_eq_finrank_quotPiece <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.unramifiedVector_gives_localComponent_sphericalVector : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ (w : Pl E) (σ : SmIrr (UL n w)), IsCompU π w σ → IsUnramU π w → fixed σ.ρ (KL n w) ≠ ⊥ := by
  first | exact @GlobalTheory.BCT.LocUnr.fixed_KL_ne_bot | exact GlobalTheory.BCT.LocUnr.fixed_KL_ne_bot | (intros; apply GlobalTheory.BCT.LocUnr.fixed_KL_ne_bot <;> assumption)
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

theorem _root_.GlobalTheory.T.moduliLaws_coefficientFieldChange : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j Xo c' (unfBC hle U) (fun σ => dict (σ.comp (incF c c' hle))) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f : cuspW Xo c U (wtZ a n), ∃ h : rulBC hle (f : Rul Xo c) ∈ cuspW Xo c' (unfBC hle U) (wtZ a n), ∀ σ : c'.F →+* ℂ, normW (unfBC hle U) (xiR D) (fun _ => D.sp.W j) (fun σ => dict (σ.comp (incF c c' hle))) (wtZ a n) σ ⟨_, h⟩ = normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) (σ.comp (incF c c' hle)) f := by
  first | exact @GlobalTheory.LawsFieldChange.laws_fieldChange | exact GlobalTheory.LawsFieldChange.laws_fieldChange | (intros; apply GlobalTheory.LawsFieldChange.laws_fieldChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_cmEllipticCurve_galois_torsion_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (n : ℕ), 0 < n → ∃ (N : IntermediateField ℚ ℂ) (_ : NumberField N) (_ : IsGalois ℚ N) (ω : 𝓞 N) (C : GlobalTheory.CM.Ell H (𝓞 N) ω) (C₀ : GlobalTheory.CompRat.Curve H) (ψ : C₀.P.A.left ⟶ C.P.A.left), (2 * ω - 1) ^ 2 = -(H.d : 𝓞 N) ∧ IsGrpPullback C₀.P.A C.P.A (spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N))) ψ ∧ ∀ a : ℤ × ℤ, ∃ y : Over.mk (𝟙 (Sp (𝓞 N))) ⟶ C.P.A, y ^ n = 1 ∧ C₀.pt (GlobalTheory.CompRat.wC H a / n) ≫ ψ = spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) ≫ y.left := by
  first | exact @GlobalTheory.TorsionModel.exists_ell_torsion_sections | exact GlobalTheory.TorsionModel.exists_ell_torsion_sections | (intros; apply GlobalTheory.TorsionModel.exists_ell_torsion_sections <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G GlobalTheory.Frames GlobalTheory.HTLat
open scoped NNReal

namespace GlobalTheory.FlatFrameLaw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}


open Classical in
theorem exOf_flatWt_some (τ : Psi H) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    exOf Dw (flatWt Dw τ) 0 (some ⟨σ, i⟩) =
      if σ = τ.1 then -1 else if σ = conjEmb τ.1 then 1 else 0 := by
  by_cases h1 : σ = τ.1
  · subst h1
    have hi : (i : ℕ) < Dw.p := by
      have := i.2; simp only [Datum.mult, if_pos τ.2] at this; exact this
    rw [if_pos rfl]
    show (wtOf Dw (flatWt Dw τ) 0).1 (τ.1, i) = -1
    rw [wtOf_big _ _ τ i hi]; simp [flatWt, parWt]
  · rw [if_neg h1]
    by_cases h2 : σ = conjEmb τ.1
    · subst h2
      have hi : (i : ℕ) < Dw.q := by
        have := i.2; simp only [Datum.mult, if_neg (conj_not_mem τ)] at this; exact this
      rw [if_pos rfl]
      show (wtOf Dw (flatWt Dw τ) 0).1 (conjEmb τ.1, i) = 1
      rw [wtOf_small _ _ τ i hi]; simp [flatWt, parWt]
    · rw [if_neg h2]
      show (wtOf Dw (flatWt Dw τ) 0).1 (σ, i) = 0
      simp only [wtOf]
      split_ifs with h h' h''
      · have hne : (⟨σ, h⟩ : Psi H) ≠ τ := fun e => h1 (congrArg Subtype.val e)
        simp [flatWt, parWt, hne]
      · rfl
      · have hne : (⟨conjEmb σ, h''⟩ : Psi H) ≠ τ := fun e => h2 (by
          rw [← congrArg Subtype.val e, GlobalTheory.AllWt.conjEmb_conjEmb])
        simp [flatWt, parWt, hne]
      · rfl
      · rfl

theorem exOf_flatWt_none (τ : Psi H) : exOf Dw (flatWt Dw τ) 0 none = 0 := by
  simp [exOf, exZ, wtOf]

theorem ne_conjEmb (τ : Psi H) : τ.1 ≠ conjEmb τ.1 := fun e => conj_not_mem τ (e ▸ τ.2)

end GlobalTheory.FlatFrameLaw

namespace GlobalTheory.FlatFrameLaw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem evR_flat_frChg {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (τ : Psi H) {f : Rul Xo c}
    (hf : f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0)) {C : Type} [Field C] [Algebra c.F C]
    (g : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) C) (a : C)
    (z y : FrPt Xo c C) (hch : FrChg g a z y) (hg : ∀ σ i j, i < j → g σ i j = 0)
    (hdet : ∀ σ, IsUnit (g σ).det) (ha : a ≠ 0) :
    evR Xo c f y = ((g τ.1).det)⁻¹ * (g (conjEmb τ.1)).det * evR Xo c f z := by
  classical
  have hdiag : ∀ σ, (g σ).det = ∏ i, g σ i i := fun σ =>
    Matrix.det_of_lowerTriangular _ fun i j hij => hg σ i j hij
  have hd : ∀ σ i, g σ i i ≠ 0 := fun σ i => by
    have hu := (hdet σ).ne_zero
    rw [hdiag σ] at hu
    exact Finset.prod_ne_zero_iff.1 hu i (Finset.mem_univ i)
  obtain ⟨h1, h2, pm, h3, h4, h5⟩ := hch
  let t : Ix Dw → Cˣ := fun i => Option.rec (Units.mk0 a ha) (fun s => Units.mk0 _ (hd s.1 s.2)) i
  have hb : FrBor t z y := by
    refine ⟨h1, fun σ i => ⟨g σ i, rfl, hg σ i, h2 σ i⟩, pm, h3, ?_, h5⟩
    rw [h4, show spMap (RingHom.id C) = 𝟙 _ from Spec.map_id _]
    exact Category.comp_id _
  rw [GlobalTheory.FlagTan.evR_frBor hf hb]
  congr 1
  rw [Units.coe_prod, Fintype.prod_option, Fintype.prod_sigma]
  have hF : ∀ σ, ∏ i : Fin (Dw.mult σ), ((t (some ⟨σ, i⟩) ^ exOf Dw (flatWt Dw τ) 0 (some ⟨σ, i⟩) : Cˣ) : C) =
      if σ = τ.1 then ((g σ).det)⁻¹ else if σ = conjEmb τ.1 then (g σ).det else 1 := fun σ => by
    simp only [exOf_flatWt_some, t, Units.val_zpow_eq_zpow_val, Units.val_mk0]
    by_cases e1 : σ = τ.1
    · simp only [if_pos e1, zpow_neg_one, Finset.prod_inv_distrib, hdiag]
    · by_cases e2 : σ = conjEmb τ.1
      · simp only [if_neg e1, if_pos e2, zpow_one, hdiag]
      · simp only [if_neg e1, if_neg e2, zpow_zero, Finset.prod_const_one]
  simp only [hF, exOf_flatWt_none, zpow_zero, Units.val_one, one_mul]
  rw [Fintype.prod_eq_mul τ.1 (conjEmb τ.1) (ne_conjEmb τ) fun σ hσ => by rw [if_neg hσ.1, if_neg hσ.2],
    if_pos rfl, if_neg (ne_conjEmb τ).symm, if_pos rfl]

end GlobalTheory.FlatFrameLaw
end
end

section

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

theorem _root_.GlobalTheory.T.framePointsOverComponent_open_set : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ), IsUnf (U σ) → ∀ (Z : Comp Xo c) (k : (U σ).Comp) (y y' : Frame ((U σ).X k).Ψ r), y' ∈ ((U σ).X k).dom → (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z → (⟨k, y'⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z := by
  first | exact @GlobalTheory.FramesUnion.framesOn_of_mem | exact GlobalTheory.FramesUnion.framesOn_of_mem | (intros; apply GlobalTheory.FramesUnion.framesOn_of_mem <;> assumption)
end
