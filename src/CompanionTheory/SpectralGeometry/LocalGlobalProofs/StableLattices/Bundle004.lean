module

public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
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
public import Mathlib.Analysis.Normed.Group.Ultra

@[expose] public section

section

open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.FrameTorus

variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]

def gens {l : ℕ} (e f : Fin l → V) (W : Submodule L V) : Set V :=
  Set.range e ∪ Set.range f ∪ (W : Set V)

theorem span_gens {h : V → V → L} {δ : L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}
    (hF : IsFrame h δ e f W) : Submodule.span L (gens e f W) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, b, w, hw, rfl⟩ := hF.2.2.2.2.2 x
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) (Submodule.subset_span (Or.inr hw))
  · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inl (Or.inl ⟨i, rfl⟩)))
  · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inl (Or.inr ⟨i, rfl⟩)))

theorem gens_induction {h : V → V → L} {δ : L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}
    (hF : IsFrame h δ e f W) {P : V → Prop} (hg : ∀ x ∈ gens e f W, P x) (h0 : P 0)
    (ha : ∀ x y, P x → P y → P (x + y)) (hm : ∀ (a : L) x, P x → P (a • x)) (x : V) : P x := by
  have hx : x ∈ Submodule.span L (gens e f W) := by
    rw [span_gens hF]
    trivial
  induction hx using Submodule.span_induction with
  | mem x h => exact hg x h
  | zero => exact h0
  | add x y _ _ hx hy => exact ha x y hx hy
  | smul a x _ hx => exact hm a x hx

def pair {s : L →+* L} {h : V → V → L} (hH : IsHerm s h) (x : V) : V →ₗ[L] L where
  toFun := h x
  map_add' := hH.1 x
  map_smul' a y := by simp [hH.2.1]

theorem add_left {s : L →+* L} {h : V → V → L} (hH : IsHerm s h) (x x' y : V) :
    h (x + x') y = h x y + h x' y := by
  rw [hH.2.2.1 y (x + x'), hH.1, map_add (f := _), ← hH.2.2.1, ← hH.2.2.1]

theorem smul_left {s : L →+* L} {h : V → V → L} (hH : IsHerm s h) (a : L) (x y : V) :
    h (a • x) y = s a * h x y := by
  rw [hH.2.2.1 y (a • x), hH.2.1, map_mul, ← hH.2.2.1]

def tor {s : L →+* L} {h : V → V → L} (hH : IsHerm s h) (δ : L) {l : ℕ} (e f : Fin l → V)
    (u : Fin l → L) : V →ₗ[L] V :=
  LinearMap.id + (∑ i, ((u i - 1) * (s δ)⁻¹) • (pair hH (f i)).smulRight (e i)) +
    ∑ i, (((s (u i))⁻¹ - 1) * δ⁻¹) • (pair hH (e i)).smulRight (f i)

theorem tor_apply {s : L →+* L} {h : V → V → L} (hH : IsHerm s h) (δ : L) {l : ℕ} (e f : Fin l → V)
    (u : Fin l → L) (x : V) :
    tor hH δ e f u x = x + (∑ i, ((u i - 1) * (s δ)⁻¹) • (h (f i) x • e i)) +
      ∑ i, (((s (u i))⁻¹ - 1) * δ⁻¹) • (h (e i) x • f i) := by
  simp [tor, pair, LinearMap.add_apply, LinearMap.sum_apply]

section Frame

variable {s : L →+* L} {h : V → V → L} {δ : L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}

theorem pair_fe (hH : IsHerm s h) (hF : IsFrame h δ e f W) (i j : Fin l) :
    h (f i) (e j) = if i = j then s δ else 0 := by
  rw [hH.2.2.1 (e j) (f i), hF.2.2.1 j i]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, Ne.symm hij]

theorem tor_e (hH : IsHerm s h) (hF : IsFrame h δ e f W) (hδ : δ ≠ 0) (u : Fin l → L) (j : Fin l) :
    tor hH δ e f u (e j) = u j • e j := by
  have hs : s δ ≠ 0 := (map_ne_zero s).2 hδ
  rw [tor_apply]
  simp only [pair_fe hH hF, hF.1, zero_smul, smul_zero, Finset.sum_const_zero, add_zero, ite_smul,
    smul_ite, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [smul_smul, mul_assoc, inv_mul_cancel₀ hs, mul_one, sub_smul, one_smul]
  abel

theorem tor_f (hH : IsHerm s h) (hF : IsFrame h δ e f W) (hδ : δ ≠ 0) (u : Fin l → L) (j : Fin l) :
    tor hH δ e f u (f j) = (s (u j))⁻¹ • f j := by
  rw [tor_apply]
  simp only [hF.2.1, hF.2.2.1, zero_smul, smul_zero, Finset.sum_const_zero, add_zero, ite_smul,
    smul_ite, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [smul_smul, mul_assoc, inv_mul_cancel₀ hδ, mul_one, sub_smul, one_smul]
  abel

theorem tor_w (hH : IsHerm s h) (hF : IsFrame h δ e f W) (u : Fin l → L) {w : V} (hw : w ∈ W) :
    tor hH δ e f u w = w := by
  rw [tor_apply]
  simp [(hF.2.2.2.1 w hw _).1, (hF.2.2.2.1 w hw _).2]

theorem tor_inv (hH : IsHerm s h) (hF : IsFrame h δ e f W) (hδ : δ ≠ 0) (u : Fin l → L)
    (hu : ∀ i, u i ≠ 0) :
    (tor hH δ e f u).comp (tor hH δ e f fun i => (u i)⁻¹) = LinearMap.id := by
  refine LinearMap.ext_on (span_gens hF) ?_
  rintro x ((⟨i, rfl⟩ | ⟨i, rfl⟩) | hx)
  · simp [tor_e hH hF hδ, hu i]
  · have : s (u i) ≠ 0 := (map_ne_zero s).2 (hu i)
    simp [tor_e hH hF hδ, tor_f hH hF hδ, this]
  · simp [tor_w hH hF _ hx]

theorem tor_iso_gens (hs : ∀ x, s (s x) = x) (hH : IsHerm s h) (hF : IsFrame h δ e f W) (hδ : δ ≠ 0)
    (u : Fin l → L) (hu : ∀ i, u i ≠ 0) {x y : V} (hx : x ∈ gens e f W) (hy : y ∈ gens e f W) :
    h (tor hH δ e f u x) (tor hH δ e f u y) = h x y := by
  have hsu : ∀ i, s (u i) ≠ 0 := fun i => (map_ne_zero s).2 (hu i)
  have hwe : ∀ {w : V}, w ∈ W → ∀ i, h w (e i) = 0 := fun hw i => by
    rw [hH.2.2.1 (e i) _, (hF.2.2.2.1 _ hw i).1, map_zero]
  have hwf : ∀ {w : V}, w ∈ W → ∀ i, h w (f i) = 0 := fun hw i => by
    rw [hH.2.2.1 (f i) _, (hF.2.2.2.1 _ hw i).2, map_zero]
  rcases hx with (⟨i, rfl⟩ | ⟨i, rfl⟩) | hx <;> rcases hy with (⟨j, rfl⟩ | ⟨j, rfl⟩) | hy
  · simp [tor_e hH hF hδ, smul_left hH, hH.2.1, hF.1]
  · rw [tor_e hH hF hδ, tor_f hH hF hδ, smul_left hH, hH.2.1, hF.2.2.1]
    by_cases hij : i = j
    · subst hij
      simp [hsu i]
    · simp [hij]
  · rw [tor_e hH hF hδ, tor_w hH hF u hy, smul_left hH, (hF.2.2.2.1 _ hy i).1, mul_zero]
  · rw [tor_f hH hF hδ, tor_e hH hF hδ, smul_left hH, hH.2.1, pair_fe hH hF]
    by_cases hij : i = j
    · subst hij
      simp [hs, hu i]
    · simp [hij]
  · simp [tor_f hH hF hδ, smul_left hH, hH.2.1, hF.2.1]
  · rw [tor_f hH hF hδ, tor_w hH hF u hy, smul_left hH, (hF.2.2.2.1 _ hy i).2, mul_zero]
  · rw [tor_w hH hF u hx, tor_e hH hF hδ, hH.2.1, hwe hx, mul_zero]
  · rw [tor_w hH hF u hx, tor_f hH hF hδ, hH.2.1, hwf hx, mul_zero]
  · rw [tor_w hH hF u hx, tor_w hH hF u hy]

theorem tor_iso (hs : ∀ x, s (s x) = x) (hH : IsHerm s h) (hF : IsFrame h δ e f W) (hδ : δ ≠ 0)
    (u : Fin l → L) (hu : ∀ i, u i ≠ 0) (x y : V) :
    h (tor hH δ e f u x) (tor hH δ e f u y) = h x y := by
  have hz : ∀ z, h z 0 = 0 := fun z => by simpa using hH.2.1 0 z 0
  have hz' : ∀ z, h 0 z = 0 := fun z => by simpa using smul_left hH 0 0 z
  have step : ∀ g ∈ gens e f W, ∀ y, h (tor hH δ e f u g) (tor hH δ e f u y) = h g y := by
    intro g hg
    refine gens_induction hF (fun y hy => tor_iso_gens hs hH hF hδ u hu hg hy) ?_ ?_ ?_
    · simp [hz]
    · intro y y' hy hy'
      simp only [map_add (f := _), hH.1, hy, hy']
    · intro a y hy
      simp only [map_smul, hH.2.1, hy]
  refine gens_induction hF (P := fun x => ∀ y, h (tor hH δ e f u x) (tor hH δ e f u y) = h x y)
    step ?_ ?_ ?_ x y
  · simp [hz']
  · intro x x' hx hx' y
    rw [map_add (f := _), add_left hH, hx, hx', add_left hH]
  · intro a x hx y
    simp only [map_smul, smul_left hH, hx]

end Frame

theorem stTor : StTor := by
  unfold StTor ForAll
  intro L _ _ _ _ s hs δ hδ V _ _ _ h hH l e f W hF u hu
  have hδ0 : δ ≠ 0 := hδ.1
  have hui : ∀ i, (u i)⁻¹ ≠ 0 := fun i => inv_ne_zero (hu i)
  let t : V ≃ₗ[L] V := LinearEquiv.ofLinear (tor hH δ e f u) (tor hH δ e f fun i => (u i)⁻¹)
    (tor_inv hH hF hδ0 u hu)
    (by simpa using tor_inv hH hF hδ0 (fun i => (u i)⁻¹) hui)
  refine ⟨t, fun x y => tor_iso hs.1 hH hF hδ0 u hu x y, ⟨fun i => tor_e hH hF hδ0 u i,
    fun i => tor_f hH hF hδ0 u i, fun w hw => tor_w hH hF u hw⟩, ?_⟩
  rintro t' ⟨h1, h2, h3⟩
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.ext_on (span_gens hF) ?_
  rintro x ((⟨i, rfl⟩ | ⟨i, rfl⟩) | hx)
  · exact (h1 i).trans (tor_e hH hF hδ0 u i).symm
  · exact (h2 i).trans (tor_f hH hF hδ0 u i).symm
  · exact (h3 x hx).trans (tor_w hH hF u hx).symm

end GlobalTheory.CompanionTheory.FrameTorus

end
end

section

open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.HermLat

section Lat

variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]

theorem smul_mem_of_isLat {Λ : AddSubgroup V} (hΛ : IsLat L Λ) {a : L} (ha : ‖a‖ ≤ 1) {x : V}
    (hx : x ∈ Λ) : a • x ∈ Λ := by
  obtain ⟨m, b, hb⟩ := hΛ
  rw [hb] at hx ⊢
  intro i
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) (hx i)

theorem exists_smul_mem_of_isLat {Λ : AddSubgroup V} (hΛ : IsLat L Λ) (v : V) :
    ∃ a : L, a ≠ 0 ∧ a • v ∈ Λ := by
  obtain ⟨m, b, hb⟩ := hΛ
  obtain ⟨a, ha0, ha⟩ := NormedField.exists_norm_lt L
    (show (0 : ℝ) < 1 / (1 + ∑ i, ‖b.repr v i‖) by positivity)
  refine ⟨a, norm_pos_iff.mp ha0, (hb _).2 fun i => ?_⟩
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  have h1 : ‖b.repr v i‖ ≤ 1 + ∑ i, ‖b.repr v i‖ := by
    have := Finset.single_le_sum (f := fun i => ‖b.repr v i‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ i)
    linarith
  calc ‖a‖ * ‖b.repr v i‖ ≤ (1 / (1 + ∑ i, ‖b.repr v i‖)) * (1 + ∑ i, ‖b.repr v i‖) := by
        gcongr
    _ = 1 := by field_simp


variable (L) in
def adjoin [IsUltrametricDist L] (Λ : AddSubgroup V) (v : V) : AddSubgroup V where
  carrier := {z | ∃ l ∈ Λ, ∃ a : L, ‖a‖ ≤ 1 ∧ z = l + a • v}
  add_mem' := by
    rintro _ _ ⟨l, hl, a, ha, rfl⟩ ⟨l', hl', a', ha', rfl⟩
    refine ⟨l + l', Λ.add_mem hl hl', a + a',
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha ha'), ?_⟩
    rw [add_smul]
    abel
  zero_mem' := ⟨0, Λ.zero_mem, 0, by simp, by simp⟩
  neg_mem' := by
    rintro _ ⟨l, hl, a, ha, rfl⟩
    refine ⟨-l, Λ.neg_mem hl, -a, by simpa using ha, ?_⟩
    rw [neg_smul]
    abel

end Lat

section Herm

variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}

theorem herm_add_left (hh : IsHerm s h) (x y z : V) : h (x + y) z = h x z + h y z := by
  rw [hh.2.2.1 z (x + y), hh.1, map_add (f := _), ← hh.2.2.1, ← hh.2.2.1]

theorem herm_smul_left (hh : IsHerm s h) (a : L) (x y : V) : h (a • x) y = s a * h x y := by
  rw [hh.2.2.1 y (a • x), hh.2.1, map_mul, ← hh.2.2.1]

theorem herm_add_add (hh : IsHerm s h) (u v : V) :
    h (u + v) (u + v) = h u u + (h u v + s (h u v)) + h v v := by
  rw [herm_add_left hh, hh.1, hh.1, ← hh.2.2.1 u v]
  ring

end Herm

section Main

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {V : Type} [AddCommGroup V]
  [Module L V] {s : L →+* L} {δ : L} {h : V → V → L}

theorem norm_sub_le_of_le {a b : L} {c : ℝ} (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ c) : ‖a - b‖ ≤ c := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (by simpa using hb))

theorem pairing_le (hδ : IsDelta s δ) (hh : IsHerm s h) {Λ : AddSubgroup V}
    (hL : IsLat L Λ) (hint : ∀ x ∈ Λ, ‖h x x‖ ≤ 1) {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    ‖h x y‖ ≤ ‖δ‖ := by
  refine (hδ.2.1 _).1 fun t ht => ?_
  have hty : t • y ∈ Λ := smul_mem_of_isLat hL ht hy
  have e := herm_add_add hh x (t • y)
  have e' : h x y * t + s (h x y * t) =
      h (x + t • y) (x + t • y) - h x x - h (t • y) (t • y) := by
    rw [e, hh.2.1 t x y, mul_comm t]
    ring
  rw [e']
  exact norm_sub_le_of_le (norm_sub_le_of_le (hint _ (Λ.add_mem hx hty)) (hint _ hx)) (hint _ hty)

theorem adjoin_integral (hs : IsInv s) (hδ : IsDelta s δ) (hh : IsHerm s h) {Λ : AddSubgroup V}
    (hint : ∀ x ∈ Λ, ‖h x x‖ ≤ 1) {p : L} (hp0 : p ≠ 0) {x : V}
    (hq : ‖h x x‖ ≤ ‖p‖ ^ 2) (hsmall : ∀ y ∈ Λ, ‖h x y‖ ≤ ‖p‖ * ‖δ‖) :
    ∀ z ∈ adjoin (L := L) Λ (p⁻¹ • x), ‖h z z‖ ≤ 1 := by
  rintro _ ⟨l, hl, a, ha, rfl⟩
  rw [herm_add_add hh]
  have hb : ‖h l (a • p⁻¹ • x)‖ ≤ ‖δ‖ := by
    rw [hh.2.1, hh.2.1, hh.2.2.1 x l, norm_mul, norm_mul, norm_inv, hs.2.1]
    have h1 := hsmall l hl
    calc ‖a‖ * (‖p‖⁻¹ * ‖h x l‖) ≤ 1 * (‖p‖⁻¹ * (‖p‖ * ‖δ‖)) := by gcongr
      _ = ‖δ‖ := by field_simp
  have htr : ‖h l (a • p⁻¹ • x) + s (h l (a • p⁻¹ • x))‖ ≤ 1 := by
    have := (hδ.2.1 _).2 hb 1 (by simp)
    simpa using this
  have hlast : ‖h (a • p⁻¹ • x) (a • p⁻¹ • x)‖ ≤ 1 := by
    rw [herm_smul_left hh, herm_smul_left hh, hh.2.1, hh.2.1, norm_mul, norm_mul, norm_mul,
      norm_mul, hs.2.1, hs.2.1, norm_inv]
    have hpp : ‖p‖⁻¹ * (‖p‖⁻¹ * ‖p‖ ^ 2) = 1 := by field_simp
    calc ‖a‖ * (‖p‖⁻¹ * (‖a‖ * (‖p‖⁻¹ * ‖h x x‖)))
        ≤ 1 * (‖p‖⁻¹ * (1 * (‖p‖⁻¹ * ‖p‖ ^ 2))) := by gcongr
      _ = 1 := by rw [one_mul, one_mul, hpp]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
    ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hint l hl) htr)) hlast)

theorem pairing_of_sandwich : StSandwich → StPairing := by
  intro hS L _ _ _ _ s hs δ hδ V _ _ _ h hh Λ hΛ
  obtain ⟨hL, hint, hmax⟩ := hΛ
  refine ⟨fun x hx y hy => pairing_le hδ hh hL hint hx hy, ?_⟩
  intro p hp hunif x hx hxp hq
  have hp0 : p ≠ 0 := by
    rintro rfl
    obtain ⟨a, ha0, ha⟩ := NormedField.exists_norm_lt L (show (0 : ℝ) < 1 by norm_num)
    have := hunif a ha
    rw [norm_zero] at this
    linarith
  have hδ0 : δ ≠ 0 := hδ.1
  have hδn : 0 < ‖δ‖ := norm_pos_iff.mpr hδ0
  by_cases hex : ∃ y ∈ Λ, ‖h x y‖ = ‖δ‖
  · obtain ⟨y, hy, hyn⟩ := hex
    have hne : h x y ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hyn
      exact hδ0 (norm_eq_zero.mp hyn.symm)
    refine ⟨(δ / h x y) • y, smul_mem_of_isLat hL ?_ hy, ?_⟩
    · rw [norm_div, hyn, div_self hδn.ne']
    · rw [hh.2.1]
      field_simp
  · exfalso
    have hsmall : ∀ y ∈ Λ, ‖h x y‖ ≤ ‖p‖ * ‖δ‖ := by
      intro y hy
      have hlt : ‖h x y‖ < ‖δ‖ :=
        lt_of_le_of_ne (pairing_le hδ hh hL hint hx hy) fun e => hex ⟨y, hy, e⟩
      have h2 : ‖h x y / δ‖ < 1 := by
        rw [norm_div, div_lt_one hδn]
        exact hlt
      have h3 := hunif _ h2
      rw [norm_div, div_le_iff₀ hδn] at h3
      exact h3
    have hle : Λ ≤ adjoin (L := L) Λ (p⁻¹ • x) := fun l hl => ⟨l, hl, 0, by simp, by simp⟩
    have hL' : IsLat L (adjoin (L := L) Λ (p⁻¹ • x)) := by
      refine hS L V Λ _ p hL hp0 ?_ ?_ ?_
      · rintro _ ⟨l, hl, a, ha, rfl⟩
        have e : p • (l + a • p⁻¹ • x) = p • l + a • x := by
          rw [smul_add, smul_comm p a, smul_smul p, mul_inv_cancel₀ hp0, one_smul]
        rw [e]
        exact Λ.add_mem (smul_mem_of_isLat hL hp.le hl) (smul_mem_of_isLat hL ha hx)
      · intro v
        obtain ⟨a, ha, hav⟩ := exists_smul_mem_of_isLat hL v
        exact ⟨a, ha, hle hav⟩
      · rintro b hb _ ⟨l, hl, a, ha, rfl⟩
        refine ⟨b • l, smul_mem_of_isLat hL hb hl, b * a, ?_, ?_⟩
        · rw [norm_mul]
          exact mul_le_one₀ hb (norm_nonneg _) ha
        · rw [smul_add, smul_smul]
    have heq := hmax _ hL' (adjoin_integral hs hδ hh hint hp0 hq hsmall) hle
    apply hxp
    rw [← heq]
    exact ⟨0, Λ.zero_mem, 1, by simp, by simp⟩

end Main

end GlobalTheory.CompanionTheory.HermLat

end
end

section

open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.Iwahori

structure IsPieces {E ι : Type} [Ring E] [Fintype ι] (P : ι → E) : Prop where
  orth : ∀ i j, i ≠ j → P i * P j = 0
  idem : ∀ i, P i * P i = P i
  sum : ∑ i, P i = 1

def IsUpper {E ι : Type} [Ring E] (wt : ι → ℕ) (P : ι → E) (a : E) : Prop :=
  ∀ i j, wt j < wt i → P i * a * P j = 0

def IsLower {E ι : Type} [Ring E] (wt : ι → ℕ) (P : ι → E) (b : E) : Prop :=
  ∀ i j, wt i < wt j → P i * b * P j = 0

def IsLowerUni {E ι : Type} [Ring E] (wt : ι → ℕ) (P : ι → E) (b : E) : Prop :=
  IsLower wt P b ∧ ∀ i, P i * b * P i = P i

structure IsCongIdeal {E ι : Type} [Ring E] (J : AddSubgroup E) (P : ι → E) : Prop where
  mul_mem : ∀ x ∈ J, ∀ y ∈ J, x * y ∈ J
  left_mem : ∀ i, ∀ x ∈ J, P i * x ∈ J
  right_mem : ∀ i, ∀ x ∈ J, x * P i ∈ J
  inv : ∀ x ∈ J, ∃ y ∈ J, (1 + x) * (1 + y) = 1 ∧ (1 + y) * (1 + x) = 1

abbrev Idx (l : ℕ) := Option (Fin l ⊕ Fin l)

def wt {l : ℕ} : Idx l → ℕ
  | some (Sum.inl i) => i
  | none => l
  | some (Sum.inr i) => 2 * l - i

def rev {l : ℕ} : Idx l → Idx l
  | some (Sum.inl i) => some (Sum.inr i)
  | none => none
  | some (Sum.inr i) => some (Sum.inl i)

section Concrete

variable {L V : Type} [NontriviallyNormedField L] [AddCommGroup V] [Module L V]

def tau {l : ℕ} (s : L →+* L) (u : Fin l → L) : Idx l → L
  | some (Sum.inl i) => u i
  | none => 1
  | some (Sum.inr i) => (s (u i))⁻¹

def hLin {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (x : V) : V →ₗ[L] L where
  toFun := h x
  map_add' := hh.1 x
  map_smul' a y := by simpa using hh.2.1 a x y

def projE {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (δ : L) {l : ℕ} (e f : Fin l → V) (i : Fin l) :
    Module.End L V := (s δ)⁻¹ • (hLin hh (f i)).smulRight (e i)

def projF {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (δ : L) {l : ℕ} (e f : Fin l → V) (i : Fin l) :
    Module.End L V := δ⁻¹ • (hLin hh (e i)).smulRight (f i)

def piece {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (δ : L) {l : ℕ} (e f : Fin l → V) :
    Idx l → Module.End L V
  | some (Sum.inl i) => projE hh δ e f i
  | none => 1 - ∑ i, (projE hh δ e f i + projF hh δ e f i)
  | some (Sum.inr i) => projF hh δ e f i

def congJ (Λ : AddSubgroup V) (π : L) : AddSubgroup (Module.End L V) where
  carrier := {g | ∀ x ∈ Λ, ∃ y ∈ Λ, g x = π • y}
  zero_mem' x _ := ⟨0, Λ.zero_mem, by simp⟩
  add_mem' {g g'} hg hg' x hx := by
    obtain ⟨y, hy, e1⟩ := hg x hx
    obtain ⟨y', hy', e2⟩ := hg' x hx
    exact ⟨y + y', Λ.add_mem hy hy', by simp [e1, e2, smul_add]⟩
  neg_mem' {g} hg x hx := by
    obtain ⟨y, hy, e1⟩ := hg x hx
    exact ⟨-y, Λ.neg_mem hy, by simp [e1]⟩

end Concrete

end GlobalTheory.CompanionTheory.Iwahori

end
end
