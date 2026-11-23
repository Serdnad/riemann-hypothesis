module

public import ReciprocityTheory.GroupCohomology.Bundle002
public import ReciprocityTheory.GroupCohomology.Bundle003
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.GroupCohomology.Bundle007
public import ReciprocityTheory.GroupCohomology.Bundle001
public import Mathlib.Topology.Algebra.OpenSubgroup
public import ReciprocityTheory.GroupCohomology.ShiftA

@[expose] public section

section

namespace ReciprocityTheory.Coh

namespace ProcyclicCohomology

open ReciprocityTheory.Gal Topology Function

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def tr (M : TRep R G) (f : G × G → M.V) (s : G) : ℕ → M.V
  | 0 => f (1, 1)
  | j + 1 => tr M f s j - f (s ^ j, s)

theorem tr_key (M : TRep R G) (f : G × G → M.V) (hf : f ∈ Z2 M.rho) (s : G) (i j : ℕ) :
    f (s ^ i, s ^ j) = M.rho (s ^ i) (tr M f s j) - tr M f s (i + j) + tr M f s i := by
  have hc := hf.2
  induction j with
  | zero =>
    have e := hc (s ^ i) 1 1
    simp only [mul_one] at e
    rw [sub_add_cancel, sub_eq_zero] at e
    simp only [pow_zero, add_zero]
    rw [sub_add_cancel]
    exact e.symm
  | succ j ih =>
    have e := hc (s ^ i) (s ^ j) s
    rw [← pow_add, ← pow_succ, ih] at e
    have e2 : tr M f s (j + 1) = tr M f s j - f (s ^ j, s) := rfl
    have e3 : tr M f s (i + (j + 1)) = tr M f s (i + j) - f (s ^ (i + j), s) := rfl
    rw [e2, e3, map_sub, ← sub_eq_zero, ← e]
    abel

theorem tr_add (M : TRep R G) (f : G × G → M.V) (s : G) (j t : ℕ) :
    tr M f s (j + t) = tr M f s j - ∑ i ∈ Finset.range t, f (s ^ (j + i), s) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have e : tr M f s (j + (t + 1)) = tr M f s (j + t) - f (s ^ (j + t), s) := rfl
    rw [e, ih, Finset.sum_range_succ]
    abel

end ProcyclicCohomology

end ReciprocityTheory.Coh

namespace ReciprocityTheory.Coh

namespace ProcyclicCohomology

open ReciprocityTheory.Gal Topology Function

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem mem_coboundaries_of_cocycle_procyclic [CompactSpace G] [TotallyDisconnectedSpace G] (M : TRep R G)
    [DiscreteTopology M.V] {s : G}
    (hc : ∀ a b : G, a * b = b * a) (hs : Dense (Subgroup.zpowers s : Set G))
    (hidx : ∀ k : ℕ, 0 < k → ∃ W : Subgroup G, IsOpen (W : Set G) ∧ W.index = k)
    (htor : ∀ m : M.V, ∃ k : ℕ, 0 < k ∧ k • m = 0) (f : G × G → M.V) (hf : f ∈ Z2 M.rho) :
    f ∈ B2 M.rho := by
  obtain ⟨N, -, hNo, hconst, hfix⟩ := FiniteLevelCohomology.exists_open_normal M (n := 2)
    (fun v : Fin 2 → G => f (v 0, v 1))
    (hf.1.comp ((continuous_apply 0).prodMk (continuous_apply 1)))
  have hbi : ∀ g h w w', w ∈ N → w' ∈ N → f (g * w, h * w') = f (g, h) := by
    intro g h w w' hw hw'
    have := hconst ![g, h] ![w, w'] (fun i => by fin_cases i <;> simpa)
    simpa using this
  have hfixf : ∀ g h, ∀ a ∈ N, M.rho a (f (g, h)) = f (g, h) := by
    intro g h a ha
    simpa using hfix ![g, h] a ha
  set T := tr M f s
  set n := N.index
  have hsn : s ^ n ∈ N := by simpa using (zpow_mem_iff hc hs hNo (n : ℤ)).2 dvd_rfl

  set a := ∑ i ∈ Finset.range n, f (s ^ i, s)
  have hwin : ∀ j, ∑ i ∈ Finset.range n, f (s ^ (j + i), s) = a := by
    intro j
    induction j with
    | zero => simp [a]
    | succ j ih =>
      have h1 : ∑ i ∈ Finset.range (n + 1), f (s ^ (j + i), s) =
          ∑ i ∈ Finset.range n, f (s ^ (j + 1 + i), s) + f (s ^ (j + 0), s) := by
        rw [Finset.sum_range_succ']
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show j + (i + 1) = j + 1 + i by omega]
      have h2 := Finset.sum_range_succ (fun i => f (s ^ (j + i), s)) n
      have hp : f (s ^ (j + n), s) = f (s ^ (j + 0), s) := by
        rw [pow_add, add_zero]
        simpa using hbi (s ^ j) s (s ^ n) 1 hsn N.one_mem
      rw [← ih]
      rw [hp] at h2
      exact add_right_cancel (h1.symm.trans h2)
  have hTn : ∀ j t, T (j + n * t) = T j - t • a := by
    intro j t
    induction t with
    | zero => simp
    | succ t ih =>
      have htadd : ∀ j t, T (j + t) = T j - ∑ i ∈ Finset.range t, f (s ^ (j + i), s) :=
        tr_add M f s
      rw [Nat.mul_succ, ← add_assoc, htadd, ih, hwin, succ_nsmul]; abel
  obtain ⟨k, hk0, hka⟩ := htor a
  have hn0 : 0 < n := index_pos hc hNo
  obtain ⟨W0, hW0o, hW0i⟩ := hidx (n * k) (Nat.mul_pos hn0 hk0)
  set W := N ⊓ W0
  have hWo : IsOpen (W : Set G) := hNo.inter hW0o
  have hWN : W ≤ N := inf_le_left
  have hdvd : n * k ∣ W.index := hW0i ▸ Subgroup.index_dvd_of_le inf_le_right
  have hper : ∀ j, T (j + W.index) = T j := by
    obtain ⟨t, ht⟩ := hdvd
    intro j; rw [ht]
    refine per_mul _ _ (fun j => ?_) j t
    rw [hTn, hka, sub_zero]
  have hfixT : ∀ w ∈ N, ∀ j, M.rho w (T j) = T j := by
    intro w hw j
    induction j with
    | zero => exact hfixf 1 1 w hw
    | succ j ih =>
      show M.rho w (T j - f (s ^ j, s)) = T j - f (s ^ j, s)
      rw [map_sub, ih, hfixf _ _ w hw]
  have hex := exists_pow hc hs hWo
  refine ⟨desc W hex T, desc_continuous hc hs hWo hex T hper, ?_⟩
  funext ⟨g, h⟩
  have hg := Classical.choose_spec (hex g)
  have hh := Classical.choose_spec (hex h)
  set i := Classical.choose (hex g)
  set j := Classical.choose (hex h)
  have hgh : (g * h)⁻¹ * s ^ (i + j) ∈ W := by
    have e : (g * h)⁻¹ * s ^ (i + j) = (g⁻¹ * s ^ i) * (h⁻¹ * s ^ j) := by
      calc (g * h)⁻¹ * s ^ (i + j) = h⁻¹ * (g⁻¹ * s ^ i) * s ^ j := by
            rw [mul_inv_rev, pow_add]; group
        _ = (g⁻¹ * s ^ i) * (h⁻¹ * s ^ j) := by rw [hc h⁻¹ (g⁻¹ * s ^ i), mul_assoc]
    rw [e]; exact W.mul_mem hg hh
  have e1 : desc W hex T (g * h) = T (i + j) := desc_eq hc hs hWo hex _ hper hgh
  have e2 : desc W hex T g = T i := rfl
  have e3 : desc W hex T h = T j := rfl
  have hgeq : g = s ^ i * (g⁻¹ * s ^ i)⁻¹ := by group
  have hheq : h = s ^ j * (h⁻¹ * s ^ j)⁻¹ := by group
  rw [d1_apply, e1, e2, e3]
  have hr : M.rho g (T j) = M.rho (s ^ i) (T j) := by
    conv_lhs => rw [hgeq, map_mul, Module.End.mul_apply]
    rw [hfixT _ (hWN (W.inv_mem hg))]
  have hfv : f (g, h) = f (s ^ i, s ^ j) := by
    conv_lhs => rw [hgeq, hheq]
    exact hbi _ _ _ _ (hWN (W.inv_mem hg)) (hWN (W.inv_mem hh))
  rw [hr, hfv, tr_key M f hf s i j]

theorem subsingleton_H2_of_procyclic_of_torsion [CompactSpace G] [TotallyDisconnectedSpace G] (M : TRep R G)
    [DiscreteTopology M.V] {s : G}
    (hc : ∀ a b : G, a * b = b * a) (hs : Dense (Subgroup.zpowers s : Set G))
    (hidx : ∀ k : ℕ, 0 < k → ∃ W : Subgroup G, IsOpen (W : Set G) ∧ W.index = k)
    (htor : ∀ m : M.V, ∃ k : ℕ, 0 < k ∧ k • m = 0) : Subsingleton (H2 M.rho) := by
  have hz : ∀ z : H2 M.rho, z = 0 := by
    intro z
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact (Submodule.Quotient.mk_eq_zero _).mpr (mem_coboundaries_of_cocycle_procyclic M hc hs hidx htor z.1 z.2)
  exact ⟨fun x y => by rw [hz x, hz y]⟩

end ProcyclicCohomology

end ReciprocityTheory.Coh
end

section

namespace ReciprocityTheory.Coh

namespace ProcyclicCohomology

open ReciprocityTheory.Gal Topology
open scoped Pointwise

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def stab (M : TRep R G) (m : M.V) : Subgroup G where
  carrier := {a | M.rho a m = m}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem stab_isOpen (M : TRep R G) [DiscreteTopology M.V] (m : M.V) : IsOpen (stab M m : Set G) :=
  Subgroup.isOpen_of_mem_nhds _ (FiniteLevelCohomology.stab_mem_nhds M m)

theorem rho_comm (M : TRep R G) (hc : ∀ a b : G, a * b = b * a) (a b : G) (x : M.V) :
    M.rho a (M.rho b x) = M.rho b (M.rho a x) := by
  rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply]

theorem cocycle_eq_of_apply (M : TRep R G) [DiscreteTopology M.V] {s : G}
    (hs : Dense (Subgroup.zpowers s : Set G)) (c : G → M.V) (hc : c ∈ Z1 M.rho) (m : M.V)
    (hm : c s = M.rho s m - m) (g : G) : c g = M.rho g m - m := by
  have hcont : Continuous fun a : G => M.rho a m :=
    M.cont.comp (f := fun a : G => (a, m)) (continuous_id.prodMk continuous_const)
  have hcl : IsClosed {a : G | c a = M.rho a m - m} :=
    isClosed_eq hc.1 (hcont.sub continuous_const)
  have step : ∀ a : G, c (a * s) - (M.rho (a * s) m - m) = c a - (M.rho a m - m) := by
    intro a
    rw [hc.2, hm, map_mul, Module.End.mul_apply]
    simp only [map_sub]; abel
  have hz : ∀ i : ℤ, c (s ^ i) = M.rho (s ^ i) m - m := by
    have h0 : c (s ^ (0 : ℤ)) - (M.rho (s ^ (0 : ℤ)) m - m) = 0 := by
      have e := hc.2 1 1
      simp only [mul_one, map_one, Module.End.one_apply] at e
      simp only [zpow_zero, map_one, Module.End.one_apply, sub_self, sub_zero]
      exact (add_eq_left.1 e.symm)
    intro i
    have : c (s ^ i) - (M.rho (s ^ i) m - m) = 0 := by
      induction i using Int.induction_on with
      | zero => exact h0
      | succ i ih => rw [zpow_add_one, step, ih]
      | pred i ih => rw [← ih, ← step, zpow_sub_one, inv_mul_cancel_right]
    exact sub_eq_zero.1 this
  have hsub : (Subgroup.zpowers s : Set G) ⊆ {a : G | c a = M.rho a m - m} := by
    intro x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact hz i
  have h := hcl.closure_subset_iff.2 hsub
  rw [hs.closure_eq] at h
  exact h (Set.mem_univ g)

end ProcyclicCohomology

end ReciprocityTheory.Coh

namespace ReciprocityTheory.Coh

namespace ProcyclicCohomology

open ReciprocityTheory.Gal Topology
open scoped Pointwise

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def psum (M : TRep R G) (s : G) (m : M.V) (j : ℕ) : M.V :=
  ∑ i ∈ Finset.range j, M.rho (s ^ i) m

theorem psum_add (M : TRep R G) (s : G) (m : M.V) (i j : ℕ) :
    psum M s m (i + j) = psum M s m i + M.rho (s ^ i) (psum M s m j) := by

  simp only [psum, Finset.sum_range_add, map_sum, pow_add, map_mul, Module.End.mul_apply]

theorem exists_cocycle [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V] {s : G}
    (hc : ∀ a b : G, a * b = b * a) (hs : Dense (Subgroup.zpowers s : Set G))
    (hidx : ∀ k : ℕ, 0 < k → ∃ W : Subgroup G, IsOpen (W : Set G) ∧ W.index = k)
    (m : M.V) (hk : ∃ k : ℕ, 0 < k ∧ k • m = 0) : ∃ c ∈ Z1 M.rho, c s = m := by
  obtain ⟨k, hk0, hkm⟩ := hk
  set V := stab M m
  have hVo := stab_isOpen M m
  set a := V.index
  have ha : 0 < a := index_pos hc hVo
  have hsa : s ^ a ∈ V := by
    have := (zpow_mem_iff hc hs hVo (a : ℤ)).2 dvd_rfl
    simpa using this
  obtain ⟨W0, hW0o, hW0i⟩ := hidx (a * k) (Nat.mul_pos ha hk0)
  set W := V ⊓ W0
  have hWo : IsOpen (W : Set G) := hVo.inter hW0o
  have hWV : W ≤ V := inf_le_left
  have hdvd : a * k ∣ W.index := hW0i ▸ Subgroup.index_dvd_of_le inf_le_right

  have hfixV : ∀ v ∈ V, ∀ j, M.rho v (psum M s m j) = psum M s m j := by
    intro v hv j

    simp only [psum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [rho_comm M hc]
    rw [show M.rho v m = m from hv]
  have hmul : ∀ t, psum M s m (a * t) = t • psum M s m a := by
    intro t
    induction t with
    | zero => simp [psum]
    | succ t ih =>
      rw [Nat.mul_succ, psum_add, ih, hfixV _ (by rw [pow_mul]; exact V.pow_mem hsa t), succ_nsmul]
  have hN : psum M s m (a * k) = 0 := by
    rw [hmul, psum, Finset.smul_sum]
    simp only [← map_nsmul, hkm, map_zero, Finset.sum_const_zero]
  have hperN : ∀ j, psum M s m (j + a * k) = psum M s m j := by
    intro j; rw [psum_add, hN, map_zero, add_zero]
  have hper : ∀ j, psum M s m (j + W.index) = psum M s m j := by
    obtain ⟨t, ht⟩ := hdvd
    intro j; rw [ht]; exact per_mul _ _ hperN j t
  have hex := exists_pow hc hs hWo
  refine ⟨desc W hex (psum M s m), ⟨desc_continuous hc hs hWo hex _ hper, fun g h => ?_⟩, ?_⟩
  · have hg := Classical.choose_spec (hex g)
    have hh := Classical.choose_spec (hex h)
    set i := Classical.choose (hex g)
    set j := Classical.choose (hex h)
    have hgh : (g * h)⁻¹ * s ^ (i + j) ∈ W := by
      have e : (g * h)⁻¹ * s ^ (i + j) = (g⁻¹ * s ^ i) * (h⁻¹ * s ^ j) := by
        calc (g * h)⁻¹ * s ^ (i + j) = h⁻¹ * (g⁻¹ * s ^ i) * s ^ j := by
              rw [mul_inv_rev, pow_add]; group
          _ = (g⁻¹ * s ^ i) * (h⁻¹ * s ^ j) := by rw [hc h⁻¹ (g⁻¹ * s ^ i), mul_assoc]
      rw [e]; exact W.mul_mem hg hh
    have e1 : desc W hex (psum M s m) (g * h) = psum M s m (i + j) := desc_eq hc hs hWo hex _ hper hgh
    have e2 : desc W hex (psum M s m) g = psum M s m i := rfl
    have e3 : desc W hex (psum M s m) h = psum M s m j := rfl
    rw [e1, e2, e3, psum_add]
    congr 1
    have hgeq : g = s ^ i * (g⁻¹ * s ^ i)⁻¹ := by group
    conv_rhs => rw [hgeq, map_mul, Module.End.mul_apply]
    rw [hfixV _ (hWV (W.inv_mem hg))]
  · have : desc W hex (psum M s m) s = psum M s m 1 :=
      desc_eq hc hs hWo hex _ hper (by simp)
    rw [this]; simp [psum]

end ProcyclicCohomology

end ReciprocityTheory.Coh

namespace ReciprocityTheory.Coh

namespace ProcyclicCohomology

open ReciprocityTheory.Gal Function

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem model_comparison_degree_zero_bijective [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V] {s : G}
    (hc : ∀ a b : G, a * b = b * a) (hs : Dense (Subgroup.zpowers s : Set G))
    (hidx : ∀ k : ℕ, 0 < k → ∃ W : Subgroup G, IsOpen (W : Set G) ∧ W.index = k)
    (htor : ∀ m : M.V, ∃ k : ℕ, 0 < k ∧ k • m = 0) :
    ∃ e : H1 M.rho ≃ₗ[R] M.V ⧸ LinearMap.range (M.rho s - LinearMap.id),
      ∀ c : Z1 M.rho, e (Submodule.Quotient.mk c) = Submodule.Quotient.mk (c.1 s) := by
  set P := LinearMap.range (M.rho s - LinearMap.id)
  let f : Z1 M.rho →ₗ[R] M.V ⧸ P := P.mkQ ∘ₗ ((LinearMap.proj s) ∘ₗ (Z1 M.rho).subtype)
  have hf : ∀ c : Z1 M.rho, f c = Submodule.Quotient.mk (c.1 s) := fun c => rfl
  have hker : (B1 M.rho).comap (Z1 M.rho).subtype ≤ LinearMap.ker f := by
    intro c hc'
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hc'
    rw [LinearMap.mem_ker, hf, Submodule.Quotient.mk_eq_zero]
    exact ⟨m, by simpa using (hm s).symm⟩
  let φ := ((B1 M.rho).comap (Z1 M.rho).subtype).liftQ f hker
  have hφ : ∀ c : Z1 M.rho, φ (Submodule.Quotient.mk c) = Submodule.Quotient.mk (c.1 s) :=
    fun c => rfl
  have hinj : Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [hφ, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨m, hm⟩ := hx
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1]
    refine ⟨m, cocycle_eq_of_apply M hs c.1 c.2 m ?_⟩
    rw [← hm]; simp
  have hsurj : Surjective φ := by
    intro y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨c, hcZ, hcs⟩ := exists_cocycle M hc hs hidx m (htor m)
    exact ⟨Submodule.Quotient.mk ⟨c, hcZ⟩, by rw [hφ]; simp [hcs]⟩
  exact ⟨LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun c => hφ c⟩

end ProcyclicCohomology

end ReciprocityTheory.Coh
end

section

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

namespace KernelCokernelKilling

section KillLES

variable {R : Type u} [CommRing R] {A B C : Cx R} {i : Hom A B} {p : Hom B C}
  {δ : ∀ n, C.H n →ₗ[R] A.H (n + 1)}

end KillLES

section KillRep

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

end KillRep

end KernelCokernelKilling

open KernelCokernelKilling

theorem shift_holds : ShiftStatement.{u} := by
  intro R _ G _ _ _ _ N hN M _ hM n hn
  induction n, hn using Nat.le_induction generalizing M with
  | base => exact hN M hM
  | succ n hNn ih =>
    exact KernelCokernelKilling.shift_step M n (ih (KernelCokernelKilling.shQ M) (KernelCokernelKilling.shQ_tors M hM))

end

end ReciprocityTheory.Coh
end
