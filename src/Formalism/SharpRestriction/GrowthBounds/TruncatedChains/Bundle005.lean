module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.RestPair
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.FiltrationAdjointStable
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.MemWeightSpaceIffDiagonalEigen
public import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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

noncomputable section

open Finset

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

section

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def resOps {m : ℕ} (E : GLOps n K V) (φ : Fin m → Fin n) : GLOps m K V := fun i j => E (φ i) (φ j)

theorem res_mem {m : ℕ} (E : GLOps n K V) (φ : Fin m → Fin n) (ν : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E ν) :
    x ∈ weightSp (resOps E φ) (ν ∘ φ) := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  intro i
  exact hx (φ i)

theorem res_rep {m : ℕ} {E : GLOps n K V} (hE : IsGLRep E) (φ : Fin m → Fin n) (hφ : Function.Injective φ) :
    IsGLRep (resOps E φ) := by
  refine ⟨fun a b c d => ?_, fun x => ?_, ?_⟩
  · have h := hE.1 (φ a) (φ b) (φ c) (φ d)
    simpa only [resOps, hφ.eq_iff] using h
  · obtain ⟨W, hW, hx, hst⟩ := hE.2.1 x
    exact ⟨W, hW, hx, fun a b y hy => hst (φ a) (φ b) y hy⟩
  · rw [eq_top_iff, ← hE.2.2]
    exact iSup_le fun mu => le_iSup_of_le (mu ∘ φ) fun x hx => res_mem E φ mu x hx

end

theorem ybat_base (D : Formalism.BasicNotions.D7) (hK : RestKill) (hP : RestPair) (hP' : RestPair') : YBat 0 0 := by
  intro K V _ _ _ _ _ n E hE a b c hab hac hbc ν s t hs ht T hT x hx
  have hs' : (s : ℤ) = ν a - ν b + 1 := by push_cast at hs; linarith
  have ht' : (t : ℤ) = ν b - ν c + 1 := by push_cast at ht; linarith
  have hu1 : ((s + t : ℕ) : ℤ) - (ν a - ν c) - 1 = (s : ℤ) - (ν a - ν b) := by push_cast; linarith
  have hu2 : ((s + t : ℕ) : ℤ) - (ν a - ν c) - 1 = (t : ℤ) - (ν b - ν c) := by push_cast; linarith
  have hsh := gl_rep_shifts_weights hE
  have hx1 : pf E b c t T x ∈ weightSp E ν := pf_wt hsh ν b c t T x hx
  have hx2 : pf E a c (s + t) T (pf E b c t T x) ∈ weightSp E ν := pf_wt hsh ν a c (s + t) T _ hx1
  have hz1 : pf E a b s T x ∈ weightSp E ν := pf_wt hsh ν a b s T x hx
  have hz2 : pf E a c (s + t) T (pf E a b s T x) ∈ weightSp E ν := pf_wt hsh ν a c (s + t) T _ hz1
  have hLw : pf E a b s T (pf E a c (s + t) T (pf E b c t T x)) ∈ weightSp E ν := pf_wt hsh ν a b s T _ hx2
  have hRw : pf E b c t T (pf E a c (s + t) T (pf E a b s T x)) ∈ weightSp E ν := pf_wt hsh ν b c t T _ hz2
  have hL_ab : E a b (pf E a b s T (pf E a c (s + t) T (pf E b c t T x))) = 0 :=
    hK K V n E hE a b hab ν s hs' T hT _ hx2
  have hL_bc : E b c (pf E a b s T (pf E a c (s + t) T (pf E b c t T x))) = 0 := by
    rw [hP K V n E hE a b c hab hac hbc ν s (s + t) hu1 T hT _ hx1, hK K V n E hE b c hbc ν t ht' T hT x hx,
      map_zero, map_zero]
  have hR_bc : E b c (pf E b c t T (pf E a c (s + t) T (pf E a b s T x))) = 0 :=
    hK K V n E hE b c hbc ν t ht' T hT _ hz2
  have hR_ab : E a b (pf E b c t T (pf E a c (s + t) T (pf E a b s T x))) = 0 := by
    rw [hP' K V n E hE a b c hab hac hbc ν t (s + t) hu2 T hT _ hz1, hK K V n E hE a b hab ν s hs' T hT x hx,
      map_zero, map_zero]
  set Lv := pf E a b s T (pf E a c (s + t) T (pf E b c t T x)) with hLv
  set Rv := pf E b c t T (pf E a c (s + t) T (pf E a b s T x)) with hRv
  have hφ : Function.Injective ![a, b, c] := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  have hE' := res_rep hE ![a, b, c] hφ
  have hv' : Lv - Rv ∈ weightSp (resOps E ![a, b, c]) (ν ∘ ![a, b, c]) :=
    res_mem E ![a, b, c] ν _ (Submodule.sub_mem _ hLw hRw)
  have hvab : E a b (Lv - Rv) = 0 := by rw [map_sub, hL_ab, hR_ab, sub_zero]
  have hvbc : E b c (Lv - Rv) = 0 := by rw [map_sub, hL_bc, hR_bc, sub_zero]
  have hvac : E a c (Lv - Rv) = 0 := by
    have h := hE.1 a b b c
    rw [if_pos rfl, if_neg hac.symm, sub_zero] at h
    rw [← h, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hvbc, hvab, map_zero, map_zero,
      sub_zero]
  have hraise : ∀ i j : Fin 3, i < j → resOps E ![a, b, c] i j (Lv - Rv) = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd hij (by decide)
      | exact hvab
      | exact hvac
      | exact hvbc
  have hlow : ∀ (i j : Fin 3), j < i → ∀ (cc : ℕ) (y : V),
      pf E (![a, b, c] j) (![a, b, c] i) cc T y - y ∈ nMinus (resOps E ![a, b, c]) := by
    intro i j hji cc y
    obtain ⟨w, hw⟩ := pf_sub E (![a, b, c] j) (![a, b, c] i) cc T y
    rw [← hw]
    exact lowering_operator_mem_nMinus (resOps E ![a, b, c]) hji w
  have hLx : Lv - x ∈ nMinus (resOps E ![a, b, c]) := by
    have e : Lv - x = (pf E a b s T (pf E a c (s + t) T (pf E b c t T x)) - pf E a c (s + t) T (pf E b c t T x)) +
        (pf E a c (s + t) T (pf E b c t T x) - pf E b c t T x) + (pf E b c t T x - x) := by
      rw [hLv]; abel
    rw [e]
    exact add_mem (add_mem (hlow 1 0 (by decide) s _) (hlow 2 0 (by decide) (s + t) _)) (hlow 2 1 (by decide) t x)
  have hRx : Rv - x ∈ nMinus (resOps E ![a, b, c]) := by
    have e : Rv - x = (pf E b c t T (pf E a c (s + t) T (pf E a b s T x)) - pf E a c (s + t) T (pf E a b s T x)) +
        (pf E a c (s + t) T (pf E a b s T x) - pf E a b s T x) + (pf E a b s T x - x) := by
      rw [hRv]; abel
    rw [e]
    exact add_mem (add_mem (hlow 2 1 (by decide) t _) (hlow 2 0 (by decide) (s + t) _)) (hlow 1 0 (by decide) s x)
  have hvn : Lv - Rv ∈ nMinus (resOps E ![a, b, c]) := by
    have h := Submodule.sub_mem _ hLx hRx
    rwa [sub_sub_sub_cancel_right] at h
  exact sub_eq_zero.mp (hwv_mem_nMinus_eq_zero D (resOps E ![a, b, c]) hE' (ν ∘ ![a, b, c]) (Lv - Rv) hv' hraise hvn)

end Formalism.MainNotions.G.ExtremalProjector
end
end

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

section

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem pp_append (E : GLOps n K V) (mu : Fin n → ℤ) (l1 l2 : List (Fin n × Fin n)) (T : ℕ) (x : V) :
    pp E mu (l1 ++ l2) T x = pp E mu l1 T (pp E mu l2 T x) := by
  simp only [pp, List.map_append, List.prod_append, Module.End.mul_apply]

theorem pp_cons (E : GLOps n K V) (mu : Fin n → ℤ) (ab : Fin n × Fin n) (l : List (Fin n × Fin n)) (T : ℕ) (x : V) :
    pp E mu (ab :: l) T x = ppFac E mu ab.1 ab.2 T (pp E mu l T x) := by
  simp only [pp, List.map_cons, List.prod_cons, Module.End.mul_apply]

end

private theorem mem_weightSp_iff_forall_diag {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (ν : Fin n → ℤ) (y : V) :
    y ∈ weightSp E ν ↔ ∀ c, E c c y = (ν c : K) • y := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, sub_eq_zero]
  first
  | simp only [Module.End.one_apply]
  | simp only [LinearMap.one_apply]

private theorem glRep_apply_mem_weightSp_shift {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (hE : IsGLRep E) (a b : Fin n) (ν : Fin n → ℤ) (y : V)
    (hy : y ∈ weightSp E ν) :
    E a b y ∈ weightSp E (fun c => ν c + ((if c = a then 1 else 0) - (if c = b then 1 else 0))) := by
  rw [mem_weightSp_iff_forall_diag] at hy ⊢
  intro c
  have h := congrArg (fun f : Module.End K V => f y) (hE.1 c c a b)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hy c, map_smul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  by_cases hca : c = a
  · subst hca
    by_cases hcb : c = b
    · subst hcb
      simp only [eq_self_iff_true, if_true]
      push_cast
      first
      | module
      | (simp [add_smul, sub_smul])
    · have hbc : ¬ b = c := fun h => hcb h.symm
      simp only [eq_self_iff_true, if_true, if_neg hbc, if_neg hcb, LinearMap.zero_apply, sub_zero]
      push_cast
      first
      | module
      | (simp [add_smul, sub_smul]; abel)
  · by_cases hcb : c = b
    · subst hcb
      simp only [eq_self_iff_true, if_true, if_neg hca, LinearMap.zero_apply, zero_sub]
      push_cast
      first
      | module
      | (simp [add_smul, sub_smul]; abel)
    · have hbc : ¬ b = c := fun h => hcb h.symm
      simp only [if_neg hca, if_neg hbc, if_neg hcb, LinearMap.zero_apply, sub_zero, zero_add]
      push_cast
      first
      | module
      | simp

private theorem glRep_pow_apply_mem_weightSp_shift {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (hE : IsGLRep E) (a b : Fin n) (k : ℕ) (ν : Fin n → ℤ) (y : V)
    (hy : y ∈ weightSp E ν) :
    (E a b ^ k) y ∈ weightSp E
      (fun c => ν c + (k : ℤ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0))) := by
  induction k generalizing ν y with
  | zero => simpa using hy
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply]
    have h1 := ih _ _ (glRep_apply_mem_weightSp_shift E hE a b ν y hy)
    convert h1 using 2
    funext c
    push_cast
    ring

private theorem ppFac_apply_mem_weightSp_of_mem {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (hE : IsGLRep E) (mu : Fin n → ℤ) (a b : Fin n) (T : ℕ) (ν : Fin n → ℤ)
    (y : V) (hy : y ∈ weightSp E ν) : ppFac E mu a b T y ∈ weightSp E ν := by
  unfold ppFac
  first
  | rw [LinearMap.sum_apply]
  | rw [LinearMap.coe_sum, Finset.sum_apply]
  | rw [LinearMap.coe_fn_sum, Finset.sum_apply]
  refine Submodule.sum_mem _ fun k _ => ?_
  simp only [divPowE, LinearMap.smul_apply, Module.End.mul_apply, map_smul]
  refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_))
  have h1 := glRep_pow_apply_mem_weightSp_shift E hE a b k ν y hy
  have h2 := glRep_pow_apply_mem_weightSp_shift E hE b a k _ _ h1
  convert h2 using 2
  funext c
  ring

private theorem pp_apply_mem_weightSp_of_mem {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (hE : IsGLRep E) (mu : Fin n → ℤ) (l : List (Fin n × Fin n)) (T : ℕ)
    (ν : Fin n → ℤ) (y : V) (hy : y ∈ weightSp E ν) : pp E mu l T y ∈ weightSp E ν := by
  induction l with
  | nil => simpa [pp] using hy
  | cons ab l ih =>
    rw [pp_cons]
    exact ppFac_apply_mem_weightSp_of_mem E hE mu ab.1 ab.2 T ν _ ih

theorem pp_step (hC : RestComm) (hY : RestYB) {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {n : ℕ} (E : GLOps n K V) (hE : IsGLRep E) (mu : Fin n → ℤ)
    (hmu : ∀ a b : Fin n, a < b → 1 ≤ mu a - mu b + ((b : ℤ) - (a : ℤ))) (T : ℕ) (hT : Module.finrank K V ≤ T)
    {l l' : List (Fin n × Fin n)} (h : Step n l l') (x : V) (hx : x ∈ weightSp E mu) :
    pp E mu l T x = pp E mu l' T x := by
  cases h with
  | swap l1 l2 a b c d hac had hbc hbd =>
    simp only [pp_append, pp_cons, ppFac_eq]
    congr 1
    exact LinearMap.congr_fun (hC K V n E hE a b c d hac had hbc hbd _ _ T).eq _
  | braid l1 l2 a b c hab hbc =>
    simp only [pp_append, pp_cons, ppFac_eq]
    congr 1
    have h1 := hmu a b hab
    have h2 := hmu b c hbc
    have h3 := hmu a c (hab.trans hbc)
    have hab2 : (a : ℕ) < b := hab
    have hbc2 : (b : ℕ) < c := hbc
    have e1 : ((mu a - mu b + ((b : ℤ) - (a : ℤ))).toNat : ℤ) = mu a - mu b + ((b : ℤ) - (a : ℤ)) :=
      Int.toNat_of_nonneg (by omega)
    have e2 : ((mu b - mu c + ((c : ℤ) - (b : ℤ))).toNat : ℤ) = mu b - mu c + ((c : ℤ) - (b : ℤ)) :=
      Int.toNat_of_nonneg (by omega)
    have e3 : ((mu a - mu c + ((c : ℤ) - (a : ℤ))).toNat : ℤ) = mu a - mu c + ((c : ℤ) - (a : ℤ)) :=
      Int.toNat_of_nonneg (by omega)
    have hu : (mu a - mu c + ((c : ℤ) - (a : ℤ))).toNat =
        (mu a - mu b + ((b : ℤ) - (a : ℤ))).toNat + (mu b - mu c + ((c : ℤ) - (b : ℤ))).toNat := by
      omega
    rw [hu]
    exact hY ((b : ℕ) - a - 1) ((c : ℕ) - b - 1) K V n E hE a b c hab.ne (hab.trans hbc).ne hbc.ne
      mu _ _ (by omega) (by omega) T hT _ (pp_apply_mem_weightSp_of_mem E hE mu l2 T mu x hx)
  | braid' l1 l2 a b c hab hbc =>
    simp only [pp_append, pp_cons, ppFac_eq]
    congr 1
    have h1 := hmu a b hab
    have h2 := hmu b c hbc
    have h3 := hmu a c (hab.trans hbc)
    have hab2 : (a : ℕ) < b := hab
    have hbc2 : (b : ℕ) < c := hbc
    have e1 : ((mu a - mu b + ((b : ℤ) - (a : ℤ))).toNat : ℤ) = mu a - mu b + ((b : ℤ) - (a : ℤ)) :=
      Int.toNat_of_nonneg (by omega)
    have e2 : ((mu b - mu c + ((c : ℤ) - (b : ℤ))).toNat : ℤ) = mu b - mu c + ((c : ℤ) - (b : ℤ)) :=
      Int.toNat_of_nonneg (by omega)
    have e3 : ((mu a - mu c + ((c : ℤ) - (a : ℤ))).toNat : ℤ) = mu a - mu c + ((c : ℤ) - (a : ℤ)) :=
      Int.toNat_of_nonneg (by omega)
    have hu : (mu a - mu c + ((c : ℤ) - (a : ℤ))).toNat =
        (mu a - mu b + ((b : ℤ) - (a : ℤ))).toNat + (mu b - mu c + ((c : ℤ) - (b : ℤ))).toNat := by
      omega
    rw [hu]
    exact (hY ((b : ℕ) - a - 1) ((c : ℕ) - b - 1) K V n E hE a b c hab.ne (hab.trans hbc).ne hbc.ne
      mu _ _ (by omega) (by omega) T hT _ (pp_apply_mem_weightSp_of_mem E hE mu l2 T mu x hx)).symm

theorem raising_kill_of_interface (hN : RestConn) (hC : RestComm) (hY : RestYB) (hK : RestKill) : SimpleRaisingKillsExtremalProjector := by
  intro K V _ _ _ _ _ n E hE mu hmu ord hord T hT x hx a b hab
  obtain ⟨l, hl⟩ := hN n ord hord a b hab
  have key : ∀ l', Relation.ReflTransGen (Step n) ord l' → pp E mu ord T x = pp E mu l' T x := by
    intro l' hl'
    induction hl' with
    | refl => rfl
    | tail _ hs ih => rw [ih, pp_step hC hY E hE mu hmu T hT hs x hx]
  have hlt : a < b := by
    rw [Fin.lt_iff_val_lt_val]
    omega
  have h1 := hmu a b hlt
  have hba : ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) = 1 := by omega
  have key2 : ((mu a - mu b + ((b : ℤ) - (a : ℤ))).toNat : ℤ) = mu a - mu b + 1 := by
    rw [Int.toNat_of_nonneg (by linarith)]
    linarith
  rw [key _ hl, pp_cons, ppFac_eq]
  exact hK K V n E hE a b hlt.ne mu _ key2 T hT _ (pp_apply_mem_weightSp_of_mem E hE mu l T mu x hx)

end Formalism.MainNotions.G.ExtremalProjector
end
end
