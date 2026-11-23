module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.Real
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Instances.ENNReal.Lemmas

@[expose] public section

section

open NumberField

namespace GlobalTheory.SmallIntegerVanishing

theorem eq_zero_of_small (E : Type) [Field E] [NumberField E] (x : RingOfIntegers E)
    (h : ∀ w : InfinitePlace E, w (x : E) < 1) : x = 0 := by
  classical
  by_contra hx
  have hnn : ∀ (w : InfinitePlace E) (y : E), 0 ≤ w y := fun w y => w.1.nonneg y
  have hne : Algebra.norm ℤ x ≠ 0 := by
    rwa [Ne, Algebra.norm_eq_zero_iff]
  have h1 : (1 : ℝ) ≤ ((|Algebra.norm ℚ (x : E)| : ℚ) : ℝ) := by
    rw [← Algebra.coe_norm_int]
    have : (1 : ℤ) ≤ |Algebra.norm ℤ x| := Int.one_le_abs hne
    exact_mod_cast this
  rw [← NumberField.InfinitePlace.prod_eq_abs_norm] at h1
  obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace E))
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w0)] at h1
  have hle : ∏ w ∈ Finset.univ.erase w0, w (x : E) ^ w.mult ≤ 1 :=
    Finset.prod_le_one₀ (fun w _ => pow_nonneg (hnn w _) _) fun w _ => pow_le_one₀ (hnn w _) (h w).le
  have hlt : w0 (x : E) ^ w0.mult < 1 :=
    pow_lt_one₀ (hnn w0 _) (h w0) NumberField.InfinitePlace.mult_ne_zero
  have h3 : w0 (x : E) ^ w0.mult * ∏ w ∈ Finset.univ.erase w0, w (x : E) ^ w.mult ≤ w0 (x : E) ^ w0.mult :=
    mul_le_of_le_one_right (pow_nonneg (hnn w0 _) _) hle
  linarith

theorem exists_denominator (E : Type) [Field E] [NumberField E] (j : ℕ)
    (Λ : Submodule (RingOfIntegers E) (Fin j → E)) (hΛ : Λ.FG) :
    ∃ d : RingOfIntegers E, d ≠ 0 ∧ ∀ y ∈ Λ, ∀ a, ∃ x : RingOfIntegers E,
      (x : E) = (d : E) * y a := by
  classical
  obtain ⟨S, hS⟩ := hΛ
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    (S.biUnion fun g => Finset.univ.image fun a => g a)
  refine ⟨(y : RingOfIntegers E), by exact_mod_cast hy0, ?_⟩
  intro v hv
  rw [← hS] at hv
  induction hv using Submodule.span_induction with
  | mem g hg =>
    intro a
    have hint := hy (g a) (Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩)
    refine ⟨⟨y • g a, hint⟩, ?_⟩
    simp [zsmul_eq_mul]
  | zero =>
    intro a
    exact ⟨0, by simp⟩
  | add u w _ _ hu hw =>
    intro a
    obtain ⟨x1, h1⟩ := hu a
    obtain ⟨x2, h2⟩ := hw a
    refine ⟨x1 + x2, ?_⟩
    calc ((x1 + x2 : RingOfIntegers E) : E) = (x1 : E) + (x2 : E) := rfl
      _ = _ := by rw [h1, h2, Pi.add_apply, mul_add]
  | smul r u _ hu =>
    intro a
    obtain ⟨x1, h1⟩ := hu a
    refine ⟨r * x1, ?_⟩
    calc ((r * x1 : RingOfIntegers E) : E) = (r : E) * (x1 : E) := rfl
      _ = (r : E) * (((y : RingOfIntegers E) : E) * u a) := by rw [h1]
      _ = ((y : RingOfIntegers E) : E) * (r • u) a := by
        rw [Pi.smul_apply, Algebra.smul_def]
        show _ = _ * ((r : E) * u a)
        ring

theorem main (E : Type) [Field E] [NumberField E] (j : ℕ)
    (Λ : Submodule (RingOfIntegers E) (Fin j → E)) (hΛ : Λ.FG) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ Λ,
      (∀ (w : InfinitePlace E) (a : Fin j), w (y a) < δ) → y = 0 := by
  classical
  obtain ⟨d, hd0, hd⟩ := exists_denominator E j Λ hΛ
  have hdE : (d : E) ≠ 0 := by exact_mod_cast hd0
  have hnn : ∀ (w : InfinitePlace E) (z : E), 0 ≤ w z := fun w z => w.1.nonneg z
  set M : ℝ := ∑ w : InfinitePlace E, w (d : E) with hM
  have hwM : ∀ w : InfinitePlace E, w (d : E) ≤ M := fun w =>
    Finset.single_le_sum (f := fun w : InfinitePlace E => w (d : E)) (fun w _ => hnn w _) (Finset.mem_univ w)
  have hMpos : 0 < M := by
    obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace E))
    exact lt_of_lt_of_le (NumberField.InfinitePlace.pos_iff.mpr hdE) (hwM w0)
  refine ⟨1 / M, by positivity, fun y hy hsmall => ?_⟩
  funext a
  obtain ⟨x, hx⟩ := hd y hy a
  have hx0 : x = 0 := eq_zero_of_small E x fun w => by
    rw [hx, map_mul]
    calc w (d : E) * w (y a) ≤ M * w (y a) := mul_le_mul_of_nonneg_right (hwM w) (hnn w _)
      _ < M * (1 / M) := mul_lt_mul_of_pos_left (hsmall w a) hMpos
      _ = 1 := by field_simp
  have hza : (d : E) * y a = 0 := by rw [← hx, hx0]; rfl
  simpa [hdE] using hza

end GlobalTheory.SmallIntegerVanishing
end

section

namespace GlobalTheory.SaturatedSublatticeComplement

universe u_1 u_2

open Module

theorem saturated_has_complement {R : Type u_1} {V : Type u_2} [CommRing R] [IsDedekindDomain R]
    [AddCommGroup V] [Module R V] (N M : Submodule R V) (hNM : N ≤ M) (hM : M.FG)
    (hsat : ∀ (r : R) (y : V), r ≠ 0 → y ∈ M → r • y ∈ N → y ∈ N) :
    ∃ A : Submodule R V, A ⊓ N = ⊥ ∧ A ⊔ N = M := by
  classical
  let N' : Submodule R M := N.comap M.subtype
  haveI : Module.Finite R M := Module.Finite.iff_fg.mpr hM
  haveI : IsTorsionFree R (M ⧸ N') := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro r q hq
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    obtain ⟨m, rfl⟩ := N'.mkQ_surjective q
    have h1 : r • m ∈ N' := by
      rw [← Submodule.Quotient.mk_eq_zero]
      simpa using hq
    have h2 : (m : V) ∈ N := hsat r m hr m.2 (by simpa [N'] using h1)
    exact (Submodule.Quotient.mk_eq_zero N').mpr (by simpa [N'] using h2)
  haveI : Module.FinitePresentation R (M ⧸ N') := Module.finitePresentation_of_finite R _
  haveI : Module.Projective R (M ⧸ N') := Module.Flat.projective_of_finitePresentation
  obtain ⟨g, hg⟩ := Module.projective_lifting_property N'.mkQ LinearMap.id N'.mkQ_surjective
  have hg' : ∀ q, N'.mkQ (g q) = q := fun q => LinearMap.congr_fun hg q
  refine ⟨(LinearMap.range g).map M.subtype, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxA, hxN⟩
    obtain ⟨_, ⟨q, rfl⟩, rfl⟩ := hxA
    have hmem : g q ∈ N' := by simpa [N'] using hxN
    have hq0 : q = 0 := by
      rw [← hg' q]
      exact (Submodule.Quotient.mk_eq_zero N').mpr hmem
    simp [hq0]
  · apply le_antisymm
    · exact sup_le (by
        rintro x ⟨y, -, rfl⟩
        exact y.2) hNM
    · intro x hx
      let m : M := ⟨x, hx⟩
      have hd : m - g (N'.mkQ m) ∈ N' := by
        rw [← Submodule.Quotient.mk_eq_zero]
        have := hg' (N'.mkQ m)
        simp only [Submodule.mkQ_apply] at this ⊢
        rw [Submodule.Quotient.mk_sub, this, sub_self]
      have hx' : x = (g (N'.mkQ m) : V) + ((m - g (N'.mkQ m) : M) : V) := by simp [m]
      rw [hx']
      exact Submodule.add_mem_sup ⟨g (N'.mkQ m), ⟨_, rfl⟩, rfl⟩ (by simpa [N'] using hd)

theorem main : ∀ {R : Type u_1} {V : Type u_2} [inst : CommRing R] [IsDedekindDomain R]
    [inst_2 : AddCommGroup V] [inst_3 : Module R V] (N M : Submodule R V), N ≤ M →
    Submodule.FG M → (∀ (r : R) (y : V), r ≠ (0 : R) → y ∈ M → r • y ∈ N → y ∈ N) →
    ∃ (A : Submodule R V), A ⊓ N = ⊥ ∧ A ⊔ N = M :=
  fun N M h1 h2 h3 => saturated_has_complement N M h1 h2 h3

end GlobalTheory.SaturatedSublatticeComplement
end

section

namespace GlobalTheory.PowSmulMem

theorem exists_pow_smul_mem {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V]
    {O : Subring E} {p : E} (hp : p ∈ O) (hO : ∀ e : E, ∃ a : ℕ, p ^ a * e ∈ O)
    (Λ' : Submodule O V) (hsp : Submodule.span E (Λ' : Set V) = ⊤) (v : V) :
    ∃ a : ℕ, ∀ b, a ≤ b → p ^ b • v ∈ Λ' := by
  have hv : v ∈ Submodule.span E (Λ' : Set V) := hsp ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx =>
    refine ⟨0, fun b _ => ?_⟩
    exact Λ'.smul_mem (⟨p ^ b, O.pow_mem hp b⟩ : O) hx
  | zero => exact ⟨0, fun b _ => by rw [smul_zero]; exact Λ'.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨c, hc⟩ := hy
    refine ⟨max a c, fun b hb => ?_⟩
    rw [smul_add]
    exact Λ'.add_mem (ha b (le_trans (le_max_left _ _) hb)) (hc b (le_trans (le_max_right _ _) hb))
  | smul e x _ hx =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨c, hc⟩ := hO e
    refine ⟨a + c, fun b hb => ?_⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hb
    have h : p ^ (a + c + d) • e • x = (p ^ c * e) • (p ^ (a + d) • x) := by
      rw [smul_smul, smul_smul]; congr 1; ring
    rw [h]
    exact Λ'.smul_mem (⟨p ^ c * e, hc⟩ : O) (ha _ (Nat.le_add_right _ _))

theorem main : ∀ {E : Type} [inst : CommRing E] {V : Type} [inst_1 : AddCommGroup V] [inst_2 : Module E V] {O : Subring E} {p : E}, p ∈ O → (∀ (e : E), ∃ (a : ℕ), p ^ a * e ∈ O) → ∀ (Λ Λ' : Submodule (↥O) V), Submodule.FG Λ → Submodule.span E (↑Λ' : Set V) = ⊤ → ∃ (a : ℕ), ∀ v ∈ Λ, p ^ a • v ∈ Λ' := by
  intro E _ V _ _ O p hp hO Λ Λ' hfg hsp
  classical
  obtain ⟨s, rfl⟩ := hfg
  choose f hf using exists_pow_smul_mem hp hO Λ' hsp
  refine ⟨s.sup f, fun v hv => ?_⟩
  induction hv using Submodule.span_induction with
  | mem x hx => exact hf x _ (Finset.le_sup (Finset.mem_coe.mp hx))
  | zero => rw [smul_zero]; exact Λ'.zero_mem
  | add x y _ _ hx hy => rw [smul_add]; exact Λ'.add_mem hx hy
  | smul e x _ hx =>
    have h : p ^ s.sup f • e • x = e • (p ^ s.sup f • x) := by
      change p ^ s.sup f • (e : E) • x = (e : E) • (p ^ s.sup f • x)
      exact smul_comm _ _ _
    rw [h]
    exact Λ'.smul_mem e hx

end GlobalTheory.PowSmulMem
end

section

open scoped Classical

namespace GlobalTheory

theorem prod_sum_of_local_choices {ι Q R : Type} {O : ι → Type} [CommSemiring R] [TopologicalSpace R] [∀ p, Nonempty (O p)]
    (s : Finset ι) (Φ : Q → ∀ p, O p) (Tq : Set Q) (U : ∀ p, Set (O p))
    (hU : ∀ p ∈ s, (U p).Finite)
    (hinj : ∀ c ∈ Tq, ∀ c' ∈ Tq, (∀ p ∈ s, Φ c p = Φ c' p) → c = c')
    (hmem : ∀ c ∈ Tq, ∀ p ∈ s, Φ c p ∈ U p)
    (hsurj : ∀ x : ∀ p, O p, (∀ p ∈ s, x p ∈ U p) → ∃ c ∈ Tq, ∀ p ∈ s, Φ c p = x p)
    (g : ∀ p, O p → R) :
    Tq.Finite ∧ (∑' c : Q, if c ∈ Tq then ∏ p ∈ s, g p (Φ c p) else 0)
      = ∏ p ∈ s, ∑' o : O p, if o ∈ U p then g p o else 0 := by
  have hT : Tq.Finite := by
    let e : Q → ∀ p : s, O p := fun c p => Φ c p
    have hfin : (Set.pi Set.univ (fun p : s => U p)).Finite :=
      Set.Finite.pi (fun p => hU p p.2)
    refine Set.Finite.of_finite_image (f := e) (hfin.subset ?_) ?_
    · rintro _ ⟨c, hc, rfl⟩ p _
      exact hmem c hc p p.2
    · intro c hc c' hc' h
      exact hinj c hc c' hc' (fun p hp => congrFun h ⟨p, hp⟩)
  refine ⟨hT, ?_⟩
  let t : ∀ p, Finset (O p) := fun p => if h : p ∈ s then (hU p h).toFinset else ∅
  have ht : ∀ p ∈ s, ∀ o, o ∈ t p ↔ o ∈ U p := by
    intro p hp o; simp [t, hp]
  rw [tsum_eq_sum (s := hT.toFinset) (fun c hc => by
    rw [Set.Finite.mem_toFinset] at hc; simp [hc])]
  have hR : ∀ p ∈ s, (∑' o : O p, if o ∈ U p then g p o else 0) = ∑ o ∈ t p, g p o := by
    intro p hp
    rw [tsum_eq_sum (s := t p) (fun o ho => by rw [ht p hp] at ho; simp [ho])]
    refine Finset.sum_congr rfl (fun o ho => ?_)
    rw [ht p hp] at ho; simp [ho]
  rw [Finset.prod_congr rfl hR, Finset.prod_sum]
  have hL : (∑ c ∈ hT.toFinset, if c ∈ Tq then ∏ p ∈ s, g p (Φ c p) else 0)
      = ∑ c ∈ hT.toFinset, ∏ p ∈ s, g p (Φ c p) :=
    Finset.sum_congr rfl (fun c hc => by rw [Set.Finite.mem_toFinset] at hc; simp [hc])
  rw [hL]
  refine Finset.sum_bij (fun c _ => fun p _ => Φ c p) ?_ ?_ ?_ ?_
  · intro c hc
    rw [Set.Finite.mem_toFinset] at hc
    rw [Finset.mem_pi]
    intro p hp
    exact (ht p hp _).2 (hmem c hc p hp)
  · intro c hc c' hc' h
    rw [Set.Finite.mem_toFinset] at hc hc'
    exact hinj c hc c' hc' (fun p hp => congrFun (congrFun h p) hp)
  · intro x hx
    rw [Finset.mem_pi] at hx
    let y : ∀ p, O p := fun p => if h : p ∈ s then x p h else Classical.arbitrary (O p)
    obtain ⟨c, hc, hcy⟩ := hsurj y (fun p hp => by
      simp only [y, dif_pos hp]; exact (ht p hp _).1 (hx p hp))
    refine ⟨c, (Set.Finite.mem_toFinset hT).2 hc, ?_⟩
    funext p hp
    rw [hcy p hp]; simp [y, hp]
  · intro c _
    exact (Finset.prod_attach s (fun p => g p (Φ c p))).symm

end GlobalTheory
end

section

open Filter Topology Set

namespace GlobalTheory.IwConst

theorem tendsto_scale_div_pow (b : ℝ → ENNReal) (d : ℕ) (v : ENNReal) (s : ℝ) (hs : 0 < s)
    (c : ℝ) (hc : 0 ≤ c)
    (hb : Tendsto (fun r : ℝ => b r / ENNReal.ofReal (r ^ d)) (𝓝[>] (0 : ℝ)) (𝓝 v))
    (hv : v ≠ ⊤) :
    Tendsto (fun r : ℝ => ENNReal.ofReal c * b (s * r) / ENNReal.ofReal (r ^ d)) (𝓝[>] (0 : ℝ))
      (𝓝 (ENNReal.ofReal (c * s ^ d) * v)) := by
  have hs' : Tendsto (fun r : ℝ => s * r) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h0 : Tendsto (fun r : ℝ => s * r) (𝓝 (0 : ℝ)) (𝓝 (s * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hs hr
  have h1 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (s ^ d)) (hb.comp hs')
    (Or.inr ENNReal.ofReal_ne_top)
  have h2 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal c) h1 (Or.inr ENNReal.ofReal_ne_top)
  rw [← mul_assoc, ← ENNReal.ofReal_mul hc] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hsd : ENNReal.ofReal (s ^ d) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact pow_pos hs d
  simp only [Function.comp]
  rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hs.le d), ← mul_div_assoc,
    ENNReal.mul_div_mul_left _ _ hsd ENNReal.ofReal_ne_top, mul_div_assoc]

theorem tendsto_ofReal_mul_of_one (g : ℝ → ℝ) (v : ENNReal) (hv : v ≠ ⊤)
    (hg : ContinuousAt g 0) (h0 : g 0 = 1) :
    Tendsto (fun η : ℝ => ENNReal.ofReal (g η) * v) (𝓝[>] (0 : ℝ)) (𝓝 v) := by
  have h1 : Tendsto (fun η : ℝ => ENNReal.ofReal (g η)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := (ENNReal.continuous_ofReal.tendsto (g 0)).comp hg.tendsto
    rw [h0, ENNReal.ofReal_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h2 := ENNReal.Tendsto.mul_const (b := v) h1 (Or.inr hv)
  rw [one_mul] at h2
  exact h2

theorem tendsto_div_pow_of_squeeze (f : ℝ → ENNReal) (d : ℕ) (v : ENNReal) (hv : v ≠ ⊤)
    (h : ∀ η : ℝ, 0 < η → ∃ b : ℝ → ENNReal,
      Tendsto (fun r : ℝ => b r / ENNReal.ofReal (r ^ d)) (𝓝[>] (0 : ℝ)) (𝓝 v) ∧
      ∀ᶠ r in 𝓝[>] (0 : ℝ), b (r / (1 + η)) ≤ ENNReal.ofReal (1 + η) * f r ∧
        f r ≤ ENNReal.ofReal (1 + η) * b ((1 + η) * r)) :
    Tendsto (fun r : ℝ => f r / ENNReal.ofReal (r ^ d)) (𝓝[>] (0 : ℝ)) (𝓝 v) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have hg : ContinuousAt (fun η : ℝ => (1 + η)⁻¹ * ((1 + η)⁻¹) ^ d) 0 := by
      fun_prop (disch := norm_num)
    have hg0 : (fun η : ℝ => (1 + η)⁻¹ * ((1 + η)⁻¹) ^ d) 0 = 1 := by simp
    have hT := tendsto_ofReal_mul_of_one _ v hv hg hg0
    obtain ⟨η, hη, hηpos⟩ := ((tendsto_order.1 hT).1 a ha |>.and self_mem_nhdsWithin).exists
    have hη0 : (0 : ℝ) < η := hηpos
    have h1η : (0 : ℝ) < 1 + η := by linarith
    obtain ⟨b, hb, hev⟩ := h η hη0
    have hL := tendsto_scale_div_pow b d v ((1 + η)⁻¹) (inv_pos.2 h1η) ((1 + η)⁻¹)
      (inv_nonneg.2 h1η.le) hb hv
    filter_upwards [(tendsto_order.1 hL).1 a hη, hev] with r hr1 hr2
    refine lt_of_lt_of_le hr1 (ENNReal.div_le_div_right ?_ _)
    calc ENNReal.ofReal ((1 + η)⁻¹) * b ((1 + η)⁻¹ * r)
        ≤ ENNReal.ofReal ((1 + η)⁻¹) * (ENNReal.ofReal (1 + η) * f r) := by
          gcongr
          rw [← div_eq_inv_mul]
          exact hr2.1
      _ = f r := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 h1η.le), inv_mul_cancel₀ h1η.ne',
            ENNReal.ofReal_one, one_mul]
  · have hg : ContinuousAt (fun η : ℝ => (1 + η) * (1 + η) ^ d) 0 := by fun_prop
    have hg0 : (fun η : ℝ => (1 + η) * (1 + η) ^ d) 0 = 1 := by simp
    have hT := tendsto_ofReal_mul_of_one _ v hv hg hg0
    obtain ⟨η, hη, hηpos⟩ := ((tendsto_order.1 hT).2 a ha |>.and self_mem_nhdsWithin).exists
    have hη0 : (0 : ℝ) < η := hηpos
    obtain ⟨b, hb, hev⟩ := h η hη0
    have hU := tendsto_scale_div_pow b d v (1 + η) (by linarith) (1 + η) (by linarith) hb hv
    filter_upwards [(tendsto_order.1 hU).2 a hη, hev] with r hr1 hr2
    exact lt_of_le_of_lt (ENNReal.div_le_div_right hr2.2 _) hr1

end GlobalTheory.IwConst
end
