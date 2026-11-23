module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

theorem cone_norm_dot_root {n : ℕ} (l : Fin n → ℝ) (a b : Fin n) (c : ℝ) :
    ∑ i, l i * (c • root a b) i = c * (l a - l b) := by
  unfold root
  simp [Pi.single_apply, mul_sub, Finset.sum_sub_distrib]
  try ring

theorem cone_norm_dot_nonneg {n : ℕ} (l β : Fin n → ℝ) (hl : Antitone l) (hβ : InRootCone β) :
    0 ≤ dot l β := by
  unfold dot
  obtain ⟨m, rfl⟩ := hβ
  have hsw : ∑ i, l i * (∑ a, ∑ b, if a < b then (m a b : ℝ) • root a b else 0) i
      = ∑ a, ∑ b, ∑ i, l i * ((if a < b then (m a b : ℝ) • root a b else 0) i) := by
    simp only [Finset.sum_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
  rw [hsw]
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  split_ifs with hab
  · rw [cone_norm_dot_root]
    exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (hl hab.le))
  · simp

theorem cone_norm_eq_zero {n : ℕ} (β : Fin n → ℝ) (h : nsq β ≤ 0) : β = 0 := by
  unfold nsq dot at h
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ β i * β i := fun i _ => mul_self_nonneg _
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp (le_antisymm h (Finset.sum_nonneg hnn))
  funext i
  exact mul_self_eq_zero.mp (h0 i (Finset.mem_univ _))

theorem cone_norm (n : ℕ) : ConeNormStatement n := by
  intro lam β hl hβ h
  apply cone_norm_eq_zero
  have hd := cone_norm_dot_nonneg lam β hl hβ
  have hexp : nsq (lam + β) = nsq lam + 2 * dot lam β + nsq β := by
    unfold nsq dot
    simp only [Pi.add_apply]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  linarith

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

section GeneratorMatrix

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

private lemma le_genSub_self (E : Fin n → Fin n → Module.End ℂ M) (S : Submodule ℂ M) : S ≤ genSub E S := by
  exact le_sInf fun T hT => hT.1

private lemma genSub_stable (E : Fin n → Fin n → Module.End ℂ M) (S : Submodule ℂ M) (a b : Fin n) {v : M}
    (hv : v ∈ genSub E S) : E a b v ∈ genSub E S := by
  exact Submodule.mem_sInf.2 fun T hT => hT.2 a b v (Submodule.mem_sInf.1 hv T hT)

private lemma genSub_le_of (E : Fin n → Fin n → Module.End ℂ M) (S T : Submodule ℂ M) (hST : S ≤ T)
    (hT : ∀ a b, ∀ v ∈ T, E a b v ∈ T) : genSub E S ≤ T := by
  exact sInf_le ⟨hST, hT⟩

private lemma single_smul_fin (c : Fin n) (r : ℂ) (x : M) :
    (Pi.single c (r • x) : Fin n → M) = r • Pi.single c x := by
  funext j
  by_cases h : j = c
  · subst h
    simp
  · simp [h]

private lemma gen_generic (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (T : Fin n → Fin n → Module.End ℂ (Fin n → M))
    (hT : ∀ a b c m, Pi.single c (E a b m) - T a b (Pi.single c m) ∈
        Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)))
    (f : Fin n → M) (hf : ∀ c, f c ∈ genSub E V) :
    f ∈ genSub T (Submodule.pi Set.univ fun _ => V) := by
  classical
  let G := genSub T (Submodule.pi Set.univ fun _ => V)
  let S : Submodule ℂ M :=
    { carrier := {m | ∀ x, (Pi.single x m : Fin n → M) ∈ G}
      add_mem' := fun {m m'} hm hm' x => by rw [Pi.single_add]; exact G.add_mem (hm x) (hm' x)
      zero_mem' := fun x => by rw [Pi.single_zero]; exact G.zero_mem
      smul_mem' := fun r m hm x => by rw [single_smul_fin]; exact G.smul_mem r (hm x) }
  have hVS : V ≤ S := fun v hv x => le_genSub_self T _ (Submodule.mem_pi.2 fun j _ => by
    by_cases h : j = x
    · subst h
      simpa using hv
    · simp [h])
  have hSS : ∀ a b, ∀ m ∈ S, E a b m ∈ S := by
    intro a b m hm x
    have h2 : Submodule.span ℂ (Set.range fun y : Fin n => (Pi.single y m : Fin n → M)) ≤ G :=
      Submodule.span_le.2 (by rintro _ ⟨y, rfl⟩; exact hm y)
    have h3 := G.add_mem (h2 (hT a b x m)) (genSub_stable T _ a b (hm x))
    simpa using h3
  have hle := genSub_le_of E V S hVS hSS
  rw [← Finset.univ_sum_single f]
  exact G.sum_mem fun c _ => hle (hf c) c

private lemma tensV_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (m : M) :
    tensV E a b (Pi.single c m) = Pi.single c (E a b m) + (if b = c then Pi.single a m else 0) := by
  funext c'
  simp only [tensV, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.comp_apply, prj, LinearMap.proj_apply,
    Pi.add_apply]
  by_cases h2 : c' = a <;> by_cases h1 : c' = c <;> by_cases h3 : b = c <;>
    simp_all [Pi.single_apply, ite_apply]

private lemma tensVd_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (m : M) :
    tensVd E a b (Pi.single c m) = Pi.single c (E a b m) - (if a = c then Pi.single b m else 0) := by
  funext c'
  simp only [tensVd, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply, prj, LinearMap.proj_apply,
    Pi.sub_apply]
  by_cases h2 : c' = b <;> by_cases h1 : c' = c <;> by_cases h3 : a = c <;>
    simp_all [Pi.single_apply, ite_apply]

end GeneratorMatrix

theorem gen_statement (n : ℕ) : GenStatement n := by
  intro ε M _ _ E V _ _
  refine ⟨fun f hf => gen_generic E V (tensV E) (fun a b c m => ?_) f hf,
    fun f hf => gen_generic E V (tensVd E) (fun a b c m => ?_) f hf⟩
  · rw [tensV_single, sub_add_cancel_left]
    split_ifs
    · exact neg_mem (Submodule.subset_span ⟨a, rfl⟩)
    · simp
  · rw [tensVd_single, sub_sub_cancel]
    split_ifs
    · exact Submodule.subset_span ⟨b, rfl⟩
    · exact zero_mem _

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

section

noncomputable section

open Finset Polynomial

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

section VK

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem vk_tensV_apply (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensV E a b f c = E a b (f c) + (if c = a then f b else 0) := by
  by_cases h : c = a <;> simp [tensV, prj, h]

theorem vk_tensVd_apply (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensVd E a b f c = E a b (f c) - (if c = b then f a else 0) := by
  by_cases h : c = b <;> simp [tensVd, prj, h]

theorem vk_eeV_apply (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeV E f d = ∑ c, E c d (f c) := by
  simp [eeV, prj, LinearMap.sum_apply]

theorem vk_eeVd_apply (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeVd E f d = -∑ c, E d c (f c) := by
  simp [eeVd, prj, LinearMap.sum_apply]

theorem vk_rel (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (a b c d : Fin n) (x : M) :
    E a b (E c d x) = E c d (E a b x) + (if b = c then E a d x else 0) - (if d = a then E c b x else 0) := by
  have h := LinearMap.congr_fun (hE a b c d) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  split_ifs at h ⊢ <;> (try simp only [LinearMap.zero_apply, sub_zero, add_zero] at h ⊢) <;>
    (rw [sub_eq_iff_eq_add] at h; rw [h]; abel)

theorem vk_eeV_comm (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (a b : Fin n) :
    eeV E * tensV E a b = tensV E a b * eeV E := by
  refine LinearMap.ext fun f => funext fun d => ?_
  simp only [Module.End.mul_apply, vk_eeV_apply]
  have h1 : ∀ c, E c d (tensV E a b f c) = E a b (E c d (f c)) + (if d = a then E c b (f c) else 0) -
      (if b = c then E a d (f c) else 0) + (if c = a then E a d (f b) else 0) := by
    intro c
    rw [vk_tensV_apply, map_add (f := _), vk_rel E hE c d a b]
    by_cases h : c = a
    · subst h; simp
    · simp [h]
  rw [Finset.sum_congr rfl fun c _ => h1 c]

  simp only [vk_tensV_apply, vk_eeV_apply, map_sum]
  by_cases hda : d = a
  · subst hda; simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']
  · simp [hda, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem vk_eeVd_comm (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (a b : Fin n) :
    eeVd E * tensVd E a b = tensVd E a b * eeVd E := by
  refine LinearMap.ext fun f => funext fun d => ?_
  simp only [Module.End.mul_apply, vk_eeVd_apply]
  have h1 : ∀ c, E d c (tensVd E a b f c) = E a b (E d c (f c)) + (if c = a then E d b (f c) else 0) -
      (if b = d then E a c (f c) else 0) - (if c = b then E d b (f a) else 0) := by
    intro c
    rw [vk_tensVd_apply, map_sub, vk_rel E hE d c a b]
    by_cases h : c = b
    · subst h; simp
    · simp [h]
  rw [Finset.sum_congr rfl fun c _ => h1 c]

  simp only [vk_tensVd_apply, vk_eeVd_apply, map_sum, map_neg]
  by_cases hdb : d = b
  · subst hdb
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq']
    abel
  · have hbd : ¬ b = d := fun h => hdb h.symm
    simp [hdb, hbd, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq']

end VK

section GenKill

variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem vk_le_genSub (T : Fin n → Fin n → Module.End ℂ W) (S : Submodule ℂ W) : S ≤ genSub T S :=
  le_sInf fun _ hT => hT.1

theorem vk_genSub_stable (T : Fin n → Fin n → Module.End ℂ W) (S : Submodule ℂ W) (a b : Fin n) (v : W)
    (hv : v ∈ genSub T S) : T a b v ∈ genSub T S := by
  rw [genSub, Submodule.mem_sInf] at hv ⊢
  intro P hP
  exact hP.2 a b v (hv P hP)

theorem vk_genSub_mono (T : Fin n → Fin n → Module.End ℂ W) {S S' : Submodule ℂ W} (h : S ≤ S') :
    genSub T S ≤ genSub T S' :=
  sInf_le ⟨h.trans (vk_le_genSub T S'), fun a b v hv => vk_genSub_stable T S' a b v hv⟩

theorem vk_genSub_map (T : Fin n → Fin n → Module.End ℂ W) (B : Module.End ℂ W)
    (hB : ∀ a b, B * T a b = T a b * B) (P : Submodule ℂ W) (hP : ∀ a b, ∀ v ∈ P, T a b v ∈ P)
    (S : Set W) (hS : ∀ x ∈ S, B x ∈ P) : ∀ x ∈ genSub T (Submodule.span ℂ S), B x ∈ P := by
  intro x hx
  have hle : genSub T (Submodule.span ℂ S) ≤ P.comap B := by
    refine sInf_le ⟨Submodule.span_le.mpr fun y hy => hS y hy, fun a b v hv => ?_⟩
    rw [Submodule.mem_comap] at hv ⊢
    rw [← Module.End.mul_apply, hB a b, Module.End.mul_apply]
    exact hP a b _ hv
  exact hle hx

theorem vk_shift_comm (T : Fin n → Fin n → Module.End ℂ W) (A : Module.End ℂ W)
    (hAT : ∀ a b, A * T a b = T a b * A) (c : ℂ) (a b : Fin n) :
    (A - c • 1) * T a b = T a b * (A - c • 1) := by
  rw [sub_mul, mul_sub, hAT, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

theorem vk_aeval_lin (A : Module.End ℂ W) (c : ℂ) : aeval A (X - C c) = A - c • 1 := by
  simp [Algebra.algebraMap_eq_smul_one]

theorem vk_kill (T : Fin n → Fin n → Module.End ℂ W) (A : Module.End ℂ W)
    (hAT : ∀ a b, A * T a b = T a b * A) (θ : Fin n → ℂ) (g : Fin n → W)
    (hstep : ∀ t, (A - θ t • 1) (g t) ∈ genSub T (Submodule.span ℂ (g '' {d | t < d}))) :
    ∀ x ∈ genSub T (Submodule.span ℂ (Set.range g)), aeval A (∏ t, (X - C (θ t))) x = 0 := by
  have main : ∀ m k : ℕ, n ≤ k + m →
      ∀ x ∈ genSub T (Submodule.span ℂ (g '' {d : Fin n | k ≤ (d : ℕ)})),
        aeval A (∏ t ∈ univ.filter (fun d : Fin n => k ≤ (d : ℕ)), (X - C (θ t))) x = 0 := by
    intro m
    induction m with
    | zero =>
      intro k hk x hx
      have hempty : g '' {d : Fin n | k ≤ (d : ℕ)} = ∅ := by
        ext y
        simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists,
          not_and]
        intro d hd
        have := d.isLt
        omega
      rw [hempty, Submodule.span_empty] at hx
      have hbot : genSub T ⊥ ≤ ⊥ :=
        sInf_le ⟨le_refl _, fun a b v hv => by rw [Submodule.mem_bot] at hv ⊢; rw [hv, map_zero]⟩
      have hx0 : x = 0 := by simpa using hbot hx
      rw [hx0, map_zero]
    | succ m ih =>
      intro k hk x hx
      by_cases hkn : n ≤ k
      · exact ih k (by omega) x hx
      · replace hkn : k < n := not_le.mp hkn
        have hfil : univ.filter (fun d : Fin n => k ≤ (d : ℕ)) =
            insert ⟨k, hkn⟩ (univ.filter (fun d : Fin n => k + 1 ≤ (d : ℕ))) := by
          ext d
          simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
          omega
        have hnot : (⟨k, hkn⟩ : Fin n) ∉ univ.filter (fun d : Fin n => k + 1 ≤ (d : ℕ)) := by simp
        rw [hfil, prod_insert hnot, mul_comm, map_mul, Module.End.mul_apply]
        apply ih (k + 1) (by omega)
        rw [vk_aeval_lin]
        have hmono : ∀ t : Fin n, k ≤ (t : ℕ) →
            genSub T (Submodule.span ℂ (g '' {d | t < d})) ≤
              genSub T (Submodule.span ℂ (g '' {d : Fin n | k + 1 ≤ (d : ℕ)})) := by
          intro t ht
          apply vk_genSub_mono
          apply Submodule.span_mono
          apply Set.image_mono
          intro d hd
          simp only [Set.mem_ofPred_eq, Fin.lt_def] at hd ⊢
          omega
        refine vk_genSub_map T _ (vk_shift_comm T A hAT _) _ (vk_genSub_stable T _) _ ?_ x hx
        rintro _ ⟨d, hd, rfl⟩
        simp only [Set.mem_ofPred_eq] at hd
        rcases eq_or_lt_of_le hd with h | h
        · have hdt : d = ⟨k, hkn⟩ := Fin.ext h.symm
          rw [hdt]
          exact hmono _ le_rfl (hstep _)
        · have e : (A - θ ⟨k, hkn⟩ • 1) (g d) = (A - θ d • 1) (g d) + (θ d - θ ⟨k, hkn⟩) • g d := by
            simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_smul]
            abel
          rw [e]
          refine add_mem (hmono d hd (hstep d)) (Submodule.smul_mem _ _ ?_)
          exact vk_le_genSub _ _ (Submodule.subset_span ⟨d, h, rfl⟩)
  intro x hx
  have h0 := main n 0 (by omega) x (by
    have : g '' {d : Fin n | 0 ≤ (d : ℕ)} = Set.range g := by
      rw [← Set.image_univ]; congr 1; ext d; simp
    rw [this]; exact hx)
  have hf : univ.filter (fun d : Fin n => 0 ≤ (d : ℕ)) = univ := by ext d; simp
  rwa [hf] at h0

theorem vk_prodShift_eq (A : Module.End ℂ W) (θ : Fin n → ℝ) :
    prodShift A θ = aeval A (∏ t, (X - C ((θ t : ℝ) : ℂ))) := by
  rw [prodShift, ← List.prod_ofFn, map_list_prod, List.map_ofFn]
  refine congrArg List.prod (congrArg List.ofFn (funext fun t => ?_))
  simp [Algebra.algebraMap_eq_smul_one]

end GenKill

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS Finset

namespace TensK

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem tensV_apply' (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensV E a b f c = E a b (f c) + (if c = a then f b else 0) := by
  by_cases h : c = a <;> simp [tensV, prj, h]

theorem tensVd_apply' (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensVd E a b f c = E a b (f c) - (if c = b then f a else 0) := by
  by_cases h : c = b <;> simp [tensVd, prj, h]

theorem eeV_apply' (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeV E f d = ∑ c, E c d (f c) := by
  simp [eeV, prj, LinearMap.sum_apply]

theorem eeVd_apply' (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeVd E f d = -∑ c, E d c (f c) := by
  simp [eeVd, prj, LinearMap.sum_apply]

theorem casimir_apply' (E : Fin n → Fin n → Module.End ℂ M) (x : M) :
    casimir E x = ∑ a, ∑ b, E a b (E b a x) := by
  simp [casimir, LinearMap.sum_apply, Module.End.mul_apply]

theorem isGlRep_tensV (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) : IsGlRep (tensV E) := by
  intro a b c d
  refine LinearMap.ext fun f => funext fun e => ?_
  have key := LinearMap.congr_fun (hE a b c d) (f e)
  have key' : E a b (E c d (f e)) = E c d (E a b (f e)) +
      ((if b = c then E a d (f e) else 0) - (if d = a then E c b (f e) else 0)) := by
    by_cases h3 : b = c <;> by_cases h4 : d = a <;>
      simp only [h3, h4, if_true, if_false, LinearMap.sub_apply, Module.End.mul_apply,
        LinearMap.zero_apply] at key ⊢ <;> rw [← key] <;> abel
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply,
    tensV_apply', map_add, apply_ite (E a b), apply_ite (E c d), map_zero, key']
  by_cases h3 : b = c <;> by_cases h4 : d = a <;>
    simp only [h3, h4, if_true, if_false, LinearMap.zero_apply, Pi.zero_apply, tensV_apply'] <;>
    split_ifs <;> subst_vars <;> (try simp) <;> first | exact absurd rfl h4 | exact absurd rfl h3 | abel

theorem isGlRep_tensVd (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) : IsGlRep (tensVd E) := by
  intro a b c d
  refine LinearMap.ext fun f => funext fun e => ?_
  have key := LinearMap.congr_fun (hE a b c d) (f e)
  have key' : E a b (E c d (f e)) = E c d (E a b (f e)) +
      ((if b = c then E a d (f e) else 0) - (if d = a then E c b (f e) else 0)) := by
    by_cases h3 : b = c <;> by_cases h4 : d = a <;>
      simp only [h3, h4, if_true, if_false, LinearMap.sub_apply, Module.End.mul_apply,
        LinearMap.zero_apply] at key ⊢ <;> rw [← key] <;> abel
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply,
    tensVd_apply', map_sub, apply_ite (E a b), apply_ite (E c d), map_zero, key']
  by_cases h3 : b = c <;> by_cases h4 : d = a <;>
    simp only [h3, h4, if_true, if_false, LinearMap.zero_apply, Pi.zero_apply, tensVd_apply'] <;>
    split_ifs <;> subst_vars <;> (try simp) <;> first | exact absurd rfl h4 | exact absurd rfl h3 | abel

theorem casimir_tensV' (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) :
    casimir (tensV E) f = (fun c => casimir E (f c)) + (n : ℂ) • f + (2 : ℂ) • eeV E f := by
  funext e
  simp only [casimir_apply', Finset.sum_apply, tensV_apply', map_add (f := _), apply_ite (E _ _), map_zero,
    Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply, eeV_apply', if_true, ite_add_zero]
  simp [Finset.sum_ite_eq, Finset.sum_ite_irrel, two_smul]
  rw [Nat.cast_smul_eq_nsmul]
  abel

theorem casimir_tensVd' (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) :
    casimir (tensVd E) f = (fun c => casimir E (f c)) + (n : ℂ) • f + (2 : ℂ) • eeVd E f := by
  funext e
  simp only [casimir_apply', Finset.sum_apply, tensVd_apply', map_sub, apply_ite (E _ _), map_zero,
    Finset.sum_sub_distrib, Pi.add_apply, Pi.smul_apply, eeVd_apply', if_true]
  simp [Finset.sum_ite_eq, Finset.sum_ite_irrel, two_smul]
  rw [Nat.cast_smul_eq_nsmul]
  abel

end TensK

theorem tens_statement (n : ℕ) : TensStatement n := by
  intro M _ _ E hE
  exact ⟨TensK.isGlRep_tensV E hE, TensK.isGlRep_tensVd E hE, TensK.casimir_tensV' E, TensK.casimir_tensVd' E⟩

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
