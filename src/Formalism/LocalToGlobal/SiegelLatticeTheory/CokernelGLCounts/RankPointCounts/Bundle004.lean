module

import Development.AutomorphicArithmetic.WeightCongruences.TorsionOrderLeTwoMulFinrankSq
public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle001
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.MeasureTheory.Constructions.Pi
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle002
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
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
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

@[expose] public section

section

noncomputable section

open NumberField

namespace Formalism.L2.SG.NGCut.TorsionTotientBound

theorem le_mul_totient_sq (n : ℕ) : n ≤ (if Even n then 2 else 1) * n.totient ^ 2 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    rw [Nat.totient_prime_pow hp hk]
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rcases hp.eq_two_or_odd' with rfl | hodd
    · have he : Even (2 ^ (m + 1)) := Nat.even_pow.mpr ⟨even_two, by omega⟩
      rw [if_pos he]
      have h1 : 2 ^ m ≤ 2 ^ m * 2 ^ m := Nat.le_mul_of_pos_right _ (by positivity)
      rw [pow_succ]
      nlinarith
    · have hne : ¬ Even (p ^ (m + 1)) := by
        rw [Nat.not_even_iff_odd]
        exact hodd.pow
      rw [if_neg hne, one_mul]
      have h3 : 3 ≤ p := by
        have := hp.two_le
        rcases hodd with ⟨j, hj⟩
        omega
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have hP : 1 ≤ (q + 1) ^ m := Nat.one_le_pow _ _ (by omega)
      have hq : q + 1 ≤ q ^ 2 := by nlinarith
      calc (q + 1) ^ (m + 1) = (q + 1) ^ m * (q + 1) := pow_succ _ _
        _ ≤ (q + 1) ^ m * q ^ 2 := Nat.mul_le_mul_left _ hq
        _ ≤ ((q + 1) ^ m) ^ 2 * q ^ 2 := Nat.mul_le_mul_right _ (by nlinarith)
        _ = ((q + 1) ^ m * q) ^ 2 := by ring
  | zero => simp
  | one => simp
  | coprime a b ha hb hab iha ihb =>
    rw [Nat.totient_mul hab, mul_pow]
    have hce : (if Even (a * b) then 2 else 1) =
        (if Even a then 2 else 1) * (if Even b then 2 else 1) := by
      by_cases ea : Even a <;> by_cases eb : Even b <;> simp [ea, eb, Nat.even_mul]
      have h2 : 2 ∣ Nat.gcd a b := Nat.dvd_gcd (even_iff_two_dvd.mp ea) (even_iff_two_dvd.mp eb)
      rw [hab.gcd_eq_one] at h2
      norm_num at h2
    calc a * b ≤ ((if Even a then 2 else 1) * a.totient ^ 2) *
          ((if Even b then 2 else 1) * b.totient ^ 2) := Nat.mul_le_mul iha ihb
      _ = _ := by rw [hce]; ring

theorem le_two_totient_sq (n : ℕ) : n ≤ 2 * n.totient ^ 2 := by
  have := le_mul_totient_sq n
  split_ifs at this <;> nlinarith [Nat.zero_le (n.totient ^ 2)]

theorem torsionOrder_le (E : Type) [Field E] [NumberField E] :
    Units.torsionOrder E ≤ 2 * (Module.finrank ℚ E) ^ 2 := by
  apply UpperTheory.torsionOrder_le_two_mul_finrank_sq <;> assumption

end Formalism.L2.SG.NGCut.TorsionTotientBound
end
end

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.CountAb

variable {G 𝒳 : Type} [Group G] [MulAction G 𝒳]
variable (W : 𝒳) (S N' K : Subgroup G) (π : G →* G) (g : G)

def Ak : Subgroup K := S.subgroupOf K

def πk (hD : Data W S N' K π) : K →* Ak S K where
  toFun k := ⟨⟨π k, hD.kπ k k.2⟩, by show π k ∈ S; exact hD.mem k⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

theorem πk_id (hD : Data W S N' K π) (a : Ak S K) : πk W S N' K π hD a = a := by
  obtain ⟨⟨x, hxK⟩, hxS⟩ := a
  have hxS' : x ∈ S := by simpa [Ak, Subgroup.mem_subgroupOf] using hxS
  ext
  simp [πk, hD.id x hxS']

def Hk : Subgroup K := (Hs W K g).subgroupOf K

theorem cellRel_iff (hD : Data W S N' K π) (k₁ k₂ : K) :
    (cellRel W N' K g).r (toCell W S N' K π g hD k₁) (toCell W S N' K π g hD k₂) ↔
      ∃ n ∈ (πk W S N' K π hD).ker, ∃ h ∈ Hk W K g, k₂ = n * k₁ * h := by
  show cell π ((k₂ : G) * g) * (cell π ((k₁ : G) * g))⁻¹ ∈ K ⊓ N' ↔ _
  constructor
  · rintro ⟨hK, hN⟩
    set x := cell π ((k₂ : G) * g) * (cell π ((k₁ : G) * g))⁻¹ with hx
    refine ⟨⟨x, hK⟩, ?_, k₁⁻¹ * ⟨x, hK⟩⁻¹ * k₂, ?_, ?_⟩
    · rw [MonoidHom.mem_ker]
      have h1 : π x = 1 := (hD.ker x).1 hN
      ext
      simp [πk, h1]
    · rw [Hk, Subgroup.mem_subgroupOf, Hs, Subgroup.mem_inf]
      refine ⟨(k₁⁻¹ * ⟨x, hK⟩⁻¹ * k₂).2, ?_⟩
      rw [MulAction.mem_stabilizer_iff]
      have e2 := cell_smul W S N' K π hD ((k₂ : G) * g)
      have e1 := cell_smul W S N' K π hD ((k₁ : G) * g)
      calc ((k₁⁻¹ * ⟨x, hK⟩⁻¹ * k₂ : K) : G) • g • W
          = ((k₁ : G)⁻¹ * cell π ((k₁ : G) * g)) • ((cell π ((k₂ : G) * g))⁻¹ • (((k₂ : G) * g) • W)) := by
            rw [← mul_smul, ← mul_smul, ← mul_smul]
            congr 1
            push_cast
            rw [hx]
            group
        _ = ((k₁ : G)⁻¹ * cell π ((k₁ : G) * g)) • W := by rw [← e2, inv_smul_smul]
        _ = g • W := by rw [mul_smul, e1, ← mul_smul]; simp
    · ext
      push_cast
      group
  · rintro ⟨n, hn, h, hh, rfl⟩
    have hπn : π (n : G) = 1 := by
      rw [MonoidHom.mem_ker] at hn
      have := congrArg (fun a : Ak S K => ((a : K) : G)) hn
      simpa [πk] using this
    have hh' : (h : G) • g • W = g • W := by
      rw [Hk, Subgroup.mem_subgroupOf, Hs, Subgroup.mem_inf] at hh
      exact hh.2
    have hs : g⁻¹ * (h : G) * g ∈ S := by
      rw [← hD.stab]
      rw [mul_smul, mul_smul, hh', ← mul_smul]
      simp
    have key : cell π (((n * k₁ * h : K) : G) * g) = (n : G) * cell π ((k₁ : G) * g) := by
      have e : ((n * k₁ * h : K) : G) * g = (n : G) * ((k₁ : G) * g) * (g⁻¹ * (h : G) * g) := by
        push_cast
        group
      simp only [cell]
      rw [e, map_mul, map_mul, hπn, hD.id _ hs]
      group
    rw [key, mul_inv_cancel_right]
    exact ⟨n.2, (hD.ker n).2 hπn⟩

end Formalism.L2.SG.Pf.CountAb
end
end

section

noncomputable section

open MeasureTheory

namespace Formalism.L2.SG.NGCut.SplitEmbedding

section TriT

variable {P : Type} [Fintype P] [DecidableEq P] {α : P → Type} [∀ p, AddCommGroup (α p)]
  (h : P → ℕ) (B : ∀ p, (∀ q, α q) → (∀ q, α q) → α p)
  (hBd : ∀ p (x x' y y' : ∀ q, α q), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → B p x y = B p x' y')
  (τ : ∀ p, (∀ q, α q) → α p) (hτ : ∀ p (x x' : ∀ q, α q), (∀ q, h q < h p → x q = x' q) → τ p x = τ p x')
  (A : ∀ p, AddSubgroup (α p)) (F : ∀ p, Set (α p)) (hFd : ∀ p (v : α p), ∃! a : A p, (a : α p) + v ∈ F p)

include hBd hτ hFd in

include hBd hτ hFd in
theorem box_fundT (g : ∀ q, α q) :
    ∃! γ : ∀ q, α q, (∀ p, γ p - τ p γ ∈ A p) ∧ ∀ p, mlaw B γ g p ∈ F p := by
  let c : (∀ q, α q) → ∀ p, A p := fun x p => (hFd p (τ p x + g p + B p x g)).exists.choose
  have hc : ∀ x p, ((c x p : A p) : α p) + (τ p x + g p + B p x g) ∈ F p :=
    fun x p => (hFd p (τ p x + g p + B p x g)).exists.choose_spec
  let Φ : (∀ q, α q) → ∀ q, α q := fun x p => τ p x + (c x p : α p)
  have hΦ : ∀ (k : ℕ) (x x' : ∀ q, α q), (∀ q, h q < k → x q = x' q) →
      ∀ p, h p < k + 1 → Φ x p = Φ x' p := by
    intro k x x' hxx p hp
    have e1 : ∀ q, h q < h p → x q = x' q := fun q hq => hxx q (by omega)
    have h1 : τ p x = τ p x' := hτ p x x' e1
    have h2 : B p x g = B p x' g := hBd p x x' g g fun q hq => ⟨e1 q hq, rfl⟩
    show τ p x + ((hFd p (τ p x + g p + B p x g)).exists.choose : α p) =
      τ p x' + ((hFd p (τ p x' + g p + B p x' g)).exists.choose : α p)
    rw [h1, h2]
  have hit : ∀ (n : ℕ) p, h p < n → Φ (Φ^[n] 0) p = (Φ^[n] 0) p := by
    intro n
    induction n with
    | zero => intro p hp; exact absurd hp (Nat.not_lt_zero _)
    | succ k ih =>
      intro p hp
      rw [Function.iterate_succ_apply']
      exact hΦ k _ _ ih p hp
  have uniq : ∀ x y : ∀ q, α q, ((∀ p, x p - τ p x ∈ A p) ∧ ∀ p, mlaw B x g p ∈ F p) →
      ((∀ p, y p - τ p y ∈ A p) ∧ ∀ p, mlaw B y g p ∈ F p) → x = y := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    have step : ∀ (n : ℕ) p, h p < n → x p = y p := by
      intro n
      induction n with
      | zero => intro p hp; exact absurd hp (Nat.not_lt_zero _)
      | succ k ih =>
        intro p hp
        have e1 : ∀ q, h q < h p → x q = y q := fun q hq => ih q (by omega)
        have ht : τ p x = τ p y := hτ p x y e1
        have hb : B p x g = B p y g := hBd p x y g g fun q hq => ⟨e1 q hq, rfl⟩
        have hx2' : ((⟨x p - τ p x, hx1 p⟩ : A p) : α p) + (τ p x + g p + B p x g) ∈ F p := by
          have hm : x p + g p + B p x g ∈ F p := hx2 p
          rw [show ((⟨x p - τ p x, hx1 p⟩ : A p) : α p) = x p - τ p x from rfl,
            show x p - τ p x + (τ p x + g p + B p x g) = x p + g p + B p x g by abel]
          exact hm
        have hy2' : ((⟨y p - τ p y, hy1 p⟩ : A p) : α p) + (τ p x + g p + B p x g) ∈ F p := by
          have hm : y p + g p + B p y g ∈ F p := hy2 p
          rw [ht, hb, show ((⟨y p - τ p y, hy1 p⟩ : A p) : α p) = y p - τ p y from rfl,
            show y p - τ p y + (τ p y + g p + B p y g) = y p + g p + B p y g by abel]
          exact hm
        have h3 : x p - τ p x = y p - τ p y :=
          congrArg Subtype.val ((hFd p _).unique hx2' hy2')
        rw [ht] at h3
        exact sub_left_injective h3
    funext p
    exact step _ p (Nat.lt_succ_self _)
  have hfix : ∀ p, τ p (Φ^[Finset.univ.sup h + 1] 0) + (c (Φ^[Finset.univ.sup h + 1] 0) p : α p) =
      (Φ^[Finset.univ.sup h + 1] 0) p :=
    fun p => hit _ p (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ p)))
  have hsol : (∀ p, (Φ^[Finset.univ.sup h + 1] 0) p - τ p (Φ^[Finset.univ.sup h + 1] 0) ∈ A p) ∧
      ∀ p, mlaw B (Φ^[Finset.univ.sup h + 1] 0) g p ∈ F p := by
    constructor
    · intro p
      rw [← hfix p, add_sub_cancel_left]
      exact (c _ p).2
    · intro p
      show (Φ^[Finset.univ.sup h + 1] 0) p + g p + B p (Φ^[Finset.univ.sup h + 1] 0) g ∈ F p
      rw [← hfix p]
      rw [show τ p (Φ^[Finset.univ.sup h + 1] 0) + (c (Φ^[Finset.univ.sup h + 1] 0) p : α p) + g p +
          B p (Φ^[Finset.univ.sup h + 1] 0) g = (c (Φ^[Finset.univ.sup h + 1] 0) p : α p) +
          (τ p (Φ^[Finset.univ.sup h + 1] 0) + g p + B p (Φ^[Finset.univ.sup h + 1] 0) g) by abel]
      exact hc _ p
  exact ⟨_, hsol, fun y hy => uniq y _ hy hsol⟩

end TriT

theorem triFundT (P : Type) [Fintype P] [DecidableEq P] (α : P → Type) [∀ p, AddCommGroup (α p)]
    [∀ p, MeasurableSpace (α p)] [∀ p, MeasurableAdd₂ (α p)]
    (μ : ∀ p, Measure (α p)) [∀ p, SigmaFinite (μ p)] [∀ p, (μ p).IsAddRightInvariant]
    (h : P → ℕ) (B : ∀ p, (∀ q, α q) → (∀ q, α q) → α p)
    (hBm : ∀ p, Measurable (fun z : (∀ q, α q) × (∀ q, α q) => B p z.1 z.2))
    (hBd : ∀ p (x x' y y' : ∀ q, α q), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → B p x y = B p x' y')
    (hB0 : ∀ p (x : ∀ q, α q), B p x 0 = 0)
    (τ : ∀ p, (∀ q, α q) → α p) (hτ : ∀ p (x x' : ∀ q, α q), (∀ q, h q < h p → x q = x' q) → τ p x = τ p x')
    (A : ∀ p, AddSubgroup (α p)) [∀ p, Countable (A p)]
    (hinv : ∀ γ : ∀ q, α q, (∀ p, γ p - τ p γ ∈ A p) → ∃ γ' : ∀ q, α q, (∀ p, γ' p - τ p γ' ∈ A p) ∧
      ∀ g, mlaw B γ' (mlaw B γ g) = g ∧ mlaw B γ (mlaw B γ' g) = g)
    (F : ∀ p, Set (α p)) (hF : ∀ p, MeasurableSet (F p)) (hFd : ∀ p (v : α p), ∃! a : A p, (a : α p) + v ∈ F p)
    (K : Set (∀ p, α p)) (hK : MeasurableSet K)
    (hKd : ∀ g, ∃! γ : ∀ q, α q, (∀ p, γ p - τ p γ ∈ A p) ∧ mlaw B γ g ∈ K) :
    Measure.pi μ K = ∏ p, μ p (F p) := by
  classical
  set T : (∀ q, α q) → (∀ q, α q) → (∀ q, α q) := fun γ g => mlaw B γ g with hTdef
  have hT : ∀ γ, MeasurePreserving (T γ) (Measure.pi μ) (Measure.pi μ) := by
    intro γ
    have := shear_mp (Fintype.card P) P rfl α μ h (fun p g => γ p + B p γ g)
      (fun p => measurable_const.add ((hBm p).comp (measurable_const.prodMk measurable_id)))
      (fun p x x' hxx => by rw [hBd p γ γ x x' fun q hq => ⟨rfl, hxx q hq⟩])
    convert this using 1
    funext g p
    simp only [hTdef, mlaw]
    abel
  have hTm : ∀ γ, Measurable (T γ) := fun γ => (hT γ).measurable
  have hT0 : ∀ γ, T γ 0 = γ := by
    intro γ; funext p; simp [hTdef, mlaw, hB0]
  let Γs := {x : ∀ q, α q // ∀ p, x p - τ p x ∈ A p}
  have hcount : Countable Γs := by
    have hinj : Function.Injective (fun x : Γs => fun p => (⟨x.1 p - τ p x.1, x.2 p⟩ : A p)) := by
      intro x y hxy
      apply Subtype.ext
      funext p
      suffices H : ∀ n, ∀ p, h p < n → x.1 p = y.1 p from H (h p + 1) p (by omega)
      intro n
      induction n with
      | zero => intro p hp; omega
      | succ k ih =>
        intro p hp
        have hl : ∀ q, h q < h p → x.1 q = y.1 q := fun q hq => ih q (by omega)
        have e := congrArg Subtype.val (congrFun hxy p)
        simp only at e
        rw [hτ p x.1 y.1 hl] at e
        simpa using e
    exact hinj.countable
  choose inv hinvA hinvT using hinv
  let iv : Γs → Γs := fun γ => ⟨inv γ.1 γ.2, hinvA γ.1 γ.2⟩
  have hiv1 : ∀ (γ : Γs) g, T (iv γ).1 (T γ.1 g) = g := fun γ g => (hinvT γ.1 γ.2 g).1
  have hiv2 : ∀ (γ : Γs) g, T γ.1 (T (iv γ).1 g) = g := fun γ g => (hinvT γ.1 γ.2 g).2
  have hivv : ∀ γ : Γs, iv (iv γ) = γ := by
    intro γ
    apply Subtype.ext
    have e : ∀ g, T (iv (iv γ)).1 g = T γ.1 g := by
      intro g
      calc T (iv (iv γ)).1 g = T (iv (iv γ)).1 (T (iv γ).1 (T γ.1 g)) := by rw [hiv1 γ g]
        _ = T γ.1 g := hiv1 (iv γ) (T γ.1 g)
    rw [← hT0 (iv (iv γ)).1, ← hT0 γ.1, e]
  let ivE : Γs ≃ Γs := ⟨iv, iv, hivv, hivv⟩
  let R : Set (∀ p, α p) := Set.pi Set.univ F
  have hR : MeasurableSet R := MeasurableSet.univ_pi hF
  have hRd := box_fundT h B hBd τ hτ A F hFd
  have hK1 : Measure.pi μ K = ∑' γ : Γs, Measure.pi μ (K ∩ T γ.1 ⁻¹' R) := by
    have hU : K = ⋃ γ : Γs, K ∩ T γ.1 ⁻¹' R := by
      ext g; constructor
      · intro hg
        obtain ⟨γ, ⟨hγA, hγF⟩, -⟩ := hRd g
        exact Set.mem_iUnion.2 ⟨⟨γ, hγA⟩, hg, fun p _ => hγF p⟩
      · intro hg
        obtain ⟨γ, hg, -⟩ := Set.mem_iUnion.1 hg
        exact hg
    conv_lhs => rw [hU]
    refine measure_iUnion ?_ fun γ => hK.inter (hTm γ.1 hR)
    intro γ δ hγδ
    rw [Function.onFun, Set.disjoint_left]
    rintro g ⟨-, hg1⟩ ⟨-, hg2⟩
    apply hγδ
    apply Subtype.ext
    exact (hRd g).unique ⟨γ.2, fun p => hg1 p (Set.mem_univ p)⟩ ⟨δ.2, fun p => hg2 p (Set.mem_univ p)⟩
  have hR1 : Measure.pi μ R = ∑' γ : Γs, Measure.pi μ (R ∩ T γ.1 ⁻¹' K) := by
    have hU : R = ⋃ γ : Γs, R ∩ T γ.1 ⁻¹' K := by
      ext g; constructor
      · intro hg
        obtain ⟨γ, ⟨hγA, hγK⟩, -⟩ := hKd g
        exact Set.mem_iUnion.2 ⟨⟨γ, hγA⟩, hg, hγK⟩
      · intro hg
        obtain ⟨γ, hg, -⟩ := Set.mem_iUnion.1 hg
        exact hg
    conv_lhs => rw [hU]
    refine measure_iUnion ?_ fun γ => hR.inter (hTm γ.1 hK)
    intro γ δ hγδ
    rw [Function.onFun, Set.disjoint_left]
    rintro g ⟨-, hg1⟩ ⟨-, hg2⟩
    apply hγδ
    apply Subtype.ext
    exact (hKd g).unique ⟨γ.2, hg1⟩ ⟨δ.2, hg2⟩
  have hterm : ∀ γ : Γs, Measure.pi μ (K ∩ T γ.1 ⁻¹' R) = Measure.pi μ (R ∩ T (iv γ).1 ⁻¹' K) := by
    intro γ
    have e : K ∩ T γ.1 ⁻¹' R = T γ.1 ⁻¹' (R ∩ T (iv γ).1 ⁻¹' K) := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      rw [hiv1 γ g]
      tauto
    rw [e]
    exact (hT γ.1).measure_preimage (hR.inter (hTm _ hK)).nullMeasurableSet
  rw [hK1, tsum_congr hterm, show (∑' γ : Γs, Measure.pi μ (R ∩ T (iv γ).1 ⁻¹' K)) =
      ∑' γ : Γs, Measure.pi μ (R ∩ T γ.1 ⁻¹' K) from ivE.tsum_eq (fun γ => Measure.pi μ (R ∩ T γ.1 ⁻¹' K)),
    ← hR1]
  exact Measure.pi_pi μ F

end Formalism.L2.SG.NGCut.SplitEmbedding
end
end

section

noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

section Lift

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  (M : Formalism.MainNotions.S.Loc.Model F E) {m : ℕ}

def mu (Z : M.Mat (m + 1)) (v : Fin (m + 1) → M.R) : E :=
  ((Z.Z.map M.R.subtype)⁻¹.mulVec fun i => (v i : E)) (Fin.last m)

theorem mu_add (Z : M.Mat (m + 1)) (v w : Fin (m + 1) → M.R) : mu M Z (v + w) = mu M Z v + mu M Z w := by
  unfold mu
  have e : (fun i => ((v + w) i : E)) = (fun i => (v i : E)) + fun i => (w i : E) := by
    funext i
    simp
  rw [e, Matrix.mulVec_add]
  rfl

theorem mu_smul (Z : M.Mat (m + 1)) (a : M.R) (v : Fin (m + 1) → M.R) : mu M Z (a • v) = (a : E) * mu M Z v := by
  unfold mu
  have e : (fun i => ((a • v) i : E)) = (a : E) • fun i => (v i : E) := by
    funext i
    simp
  rw [e, Matrix.mulVec_smul]
  rfl

theorem mu_sum (Z : M.Mat (m + 1)) {ι : Type} (s : Finset ι) (f : ι → Fin (m + 1) → M.R) :
    mu M Z (∑ i ∈ s, f i) = ∑ i ∈ s, mu M Z (f i) := by
  exact map_sum (AddMonoidHom.mk' (mu M Z) (mu_add M Z)) f s

theorem coe_mulVec (Z : M.Mat (m + 1)) (x : Fin (m + 1) → M.R) :
    (fun i => ((Z.Z.mulVec x) i : E)) = (Z.Z.map M.R.subtype).mulVec fun j => (x j : E) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.map_apply]

theorem mu_Z (Z : M.Mat (m + 1)) (x : Fin (m + 1) → M.R) : mu M Z (Z.Z.mulVec x) = (x (Fin.last m) : E) := by
  unfold mu
  rw [coe_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ Z.unit, Matrix.one_mulVec]

theorem mulVec_inj (Z : M.Mat (m + 1)) {x y : Fin (m + 1) → M.R} (h : Z.Z.mulVec x = Z.Z.mulVec y) : x = y := by
  have h1 := congrArg (fun v => fun i => ((v i : M.R) : E)) h
  rw [coe_mulVec, coe_mulVec] at h1
  have h2 := congrArg (fun v => (Z.Z.map M.R.subtype)⁻¹.mulVec v) h1
  simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ Z.unit, Matrix.one_mulVec] at h2
  funext i
  exact Subtype.ext (congrFun h2 i)

theorem lam_mk (Z : M.Mat (m + 1)) (v : Fin (m + 1) → M.R) :
    M.lam Z (Submodule.Quotient.mk v) = M.Rsub.mkQ (mu M Z v) := rfl

theorem mu_e (Z : M.Mat (m + 1)) :
    mu M Z (Pi.single (Fin.last m) 1) = (Z.Z.map M.R.subtype)⁻¹ (Fin.last m) (Fin.last m) := by
  unfold mu
  have e : (fun i => (((Pi.single (Fin.last m) (1 : M.R) : Fin (m + 1) → M.R) i : M.R) : E)) =
      (Pi.single (Fin.last m) (1 : E) : Fin (m + 1) → E) := by
    funext i
    by_cases h : i = Fin.last m <;> simp [h]
  rw [e, Matrix.mulVec_single]
  simp

def headK (Z : M.Mat (m + 1)) : Submodule M.R (Fin (m + 1) → M.R) :=
  (LinearMap.ker (LinearMap.proj (R := M.R) (φ := fun _ : Fin (m + 1) => M.R) (Fin.last m))).map Z.Z.mulVecLin

theorem mem_headK (Z : M.Mat (m + 1)) {y : Fin (m + 1) → M.R} :
    y ∈ headK M Z ↔ ∃ x, x (Fin.last m) = 0 ∧ Z.Z.mulVec x = y := by
  simp [headK, Submodule.mem_map, LinearMap.mem_ker]

end Lift

def LiftOrb : Prop :=
  ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Formalism.MainNotions.S.Loc.Model F E), M.OK → ∀ (m : ℕ) (Z Z' : M.Mat (m + 1)), Nonempty (M.Iso Z Z') →
    (Z.Z.map M.R.subtype)⁻¹ (Fin.last m) (Fin.last m) = (Z'.Z.map M.R.subtype)⁻¹ (Fin.last m) (Fin.last m) →
    ∃ l ρ : Matrix (Fin (m + 1)) (Fin (m + 1)) M.R, IsUnit l.det ∧ IsUnit ρ.det ∧
      (∀ i, l i (Fin.last m) = if i = Fin.last m then 1 else 0) ∧
      (∀ j, ρ (Fin.last m) j = if j = Fin.last m then 1 else 0) ∧ Z'.Z = l * Z.Z * ρ

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end
