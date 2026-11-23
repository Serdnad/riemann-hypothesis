module

public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Formalism.SharpRestriction.LevelLetterCocycles.CoordHomMapTrace
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle028
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle032
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle033
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Order.Interval.Finset.Box
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

theorem secIn_zero {a : ZMod n} {e d : ℕ} (cond : (ℕ → ℤ) → (Fin d → O) → Prop) :
    SecIn W a e cond (fun _ => 0) :=
  ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun k => by simp⟩

theorem secIn_add {a : ZMod n} {e d : ℕ} {cond : (ℕ → ℤ) → (Fin d → O) → Prop} {F F' : Fin d → W.EE}
    (h : SecIn W a e cond F) (h' : SecIn W a e cond F') : SecIn W a e cond (F + F') := by
  obtain ⟨I, g, c₀, α, hg, hF⟩ := h
  obtain ⟨I', g', c₀', α', hg', hF'⟩ := h'
  refine ⟨I + I', Fin.append g g', Fin.append c₀ c₀', Fin.append α α', fun i => ?_, fun k => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]; exact hg i
    · simp only [Fin.append_right]; exact hg' i
  · rw [Pi.add_apply, hF k, hF' k, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

theorem inFr_mulA {a : ZMod n} {num den : LetA O n} {f : W.EE} (h : InFr W a num den f) {c : LetA O n}
    (hc : c ∈ W.AΔ) : InFr W a num den (algebraMap (LetA O n) W.EE c * f) := by
  obtain ⟨u, hu, hf⟩ := h
  refine ⟨c * u, W.AΔ.mul_mem hc hu, ?_⟩
  rw [mul_left_comm, hf, ← map_mul]
  congr 1; ring

theorem inFr_add {a : ZMod n} {num den : LetA O n} {f f' : W.EE} (h : InFr W a num den f)
    (h' : InFr W a num den f') : InFr W a num den (f + f') := by
  obtain ⟨u, hu, hf⟩ := h
  obtain ⟨u', hu', hf'⟩ := h'
  refine ⟨u + u', W.AΔ.add_mem hu hu', ?_⟩
  rw [mul_add, hf, hf', ← map_add (f := _)]
  congr 1; ring

theorem inFr_sub {a : ZMod n} {num den : LetA O n} {f f' : W.EE} (h : InFr W a num den f)
    (h' : InFr W a num den f') : InFr W a num den (f - f') := by
  obtain ⟨u, hu, hf⟩ := h
  obtain ⟨u', hu', hf'⟩ := h'
  refine ⟨u - u', W.AΔ.sub_mem hu hu', ?_⟩
  rw [mul_sub, hf, hf', ← map_sub]
  congr 1; ring

theorem inFr_zero {a : ZMod n} {num den : LetA O n} : InFr W a num den 0 :=
  ⟨0, W.AΔ.zero_mem, by simp⟩

theorem inFr_sum {a : ZMod n} {num den : LetA O n} {ι : Type} (s : Finset ι) (F : ι → W.EE)
    (h : ∀ j ∈ s, InFr W a num den (F j)) : InFr W a num den (∑ j ∈ s, F j) := by
  induction s using Finset.induction_on with
  | empty => simpa using inFr_zero W
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact inFr_add W (h j (Finset.mem_insert_self j s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem secIn_mulA {a : ZMod n} {e d : ℕ} {cond : (ℕ → ℤ) → (Fin d → O) → Prop} {F : Fin d → W.EE}
    (h : SecIn W a e cond F) {c : LetA O n} (hc : c ∈ W.AΔ) :
    SecIn W a e cond (fun k => algebraMap (LetA O n) W.EE c * F k) := by
  obtain ⟨I, g, c₀, α, hg, hF⟩ := h
  refine ⟨I, fun i => algebraMap (LetA O n) W.EE c * g i, c₀, α, fun i => ⟨inFr_mulA W (hg i).1 hc, (hg i).2⟩,
    fun k => ?_⟩
  show algebraMap (LetA O n) W.EE c * F k = _
  rw [hF k, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dvO_succ (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → O) :
    dvO W T (e + 1) b c₀ = Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V) (dvO W T e b c₀) := by
  unfold dvO dv

  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, pow_succ', Module.End.mul_apply]

theorem dvO_add (T : LocLat G Qp LL O) (e s : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → O) :
    dvO W T (e + s) b c₀ = ((Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V)) ^ s) (dvO W T e b c₀) := by
  induction s with
  | zero => simp
  | succ s ih => rw [← add_assoc, dvO_succ, ih, pow_succ', Module.End.mul_apply]

theorem filS_succ (T : LocLat G Qp LL O) (a : ZMod n) (t : ℕ) (u : ℤ) :
    FilS W T (a + 1) (t + 1) u = (FilS W T a t u).map (Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V)) := by
  unfold FilS
  rw [show a + 1 - ((t + 1 : ℕ) : ZMod n) = a - (t : ZMod n) by push_cast; ring, ← Submodule.map_comp]
  congr 1
  rw [pow_succ', Module.End.mul_eq_comp]

variable [IsDomain O]

theorem secIn_transport (T : LocLat G Qp LL O) (a : ZMod n) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)
    (H : ℕ) {v : LetA O n} (hv : v ∈ W.AΔ) (hπ : W.π₀ ∈ W.AΔ)
    (hlow : ∀ c₀ : Fin d → O, dvO W T (e + 1) b c₀ ∈ FilS W T (a + 1) 0 (-(H : ℤ))) (F : Fin d → W.EE)
    (hF : SecIn W a e (condNN W T a e b) F) :
    SecIn W (a + 1) (e + 1) (condNN W T (a + 1) (e + 1) b)
      (fun k => algebraMap (LetA O n) W.EE (ps W 0 ^ H * v) * W.φE (F k)) := by
  obtain ⟨I, g, c₀, α, hg, hFe⟩ := hF
  refine ⟨I, fun i => algebraMap (LetA O n) W.EE (ps W 0 ^ H * v) * W.φE (g i), c₀,
    fun i s => if s = 0 then (H : ℤ) else α i (s - 1), fun i => ⟨?_, ?_⟩, fun k => ?_⟩
  · obtain ⟨u, hu, hgu⟩ := (hg i).1
    refine ⟨v * W.φA u, W.AΔ.mul_mem hv (Formalism.MainNotions.UnusedSlot80.ToolsR.φ_AΔ hu), ?_⟩
    have hl : W.φA (letE a : LetA O n) = letE (a + 1) := by
      have := φA_letE W (a + 1); rwa [show a + 1 - 1 = a by ring] at this
    have h1 := congrArg W.φE hgu
    rw [map_mul, φE_alg, φE_alg, map_mul W.φA, map_mul W.φA, hl] at h1
    have hnum : W.φA (∏ s ∈ Finset.range e, ps W s ^ (α i s).toNat) =
        ∏ s ∈ Finset.range e, ps W (s + 1) ^ (α i s).toNat := by
      rw [map_prod]; exact Finset.prod_congr rfl fun s _ => by rw [map_pow, ← ps_succ]
    have hden : W.φA (∏ s ∈ Finset.range e, ps W s ^ (-(α i s)).toNat) =
        ∏ s ∈ Finset.range e, ps W (s + 1) ^ (-(α i s)).toNat := by
      rw [map_prod]; exact Finset.prod_congr rfl fun s _ => by rw [map_pow, ← ps_succ]
    rw [hnum, hden] at h1
    show algebraMap (LetA O n) W.EE (∏ s ∈ Finset.range (e + 1), ps W s ^
        (-(if s = 0 then (H : ℤ) else α i (s - 1))).toNat) *
        (algebraMap (LetA O n) W.EE (ps W 0 ^ H * v) * W.φE (g i)) =
      algebraMap (LetA O n) W.EE ((letE (a + 1) * ∏ s ∈ Finset.range (e + 1), ps W s ^
        (if s = 0 then (H : ℤ) else α i (s - 1)).toNat) * (v * W.φA u))
    rw [Finset.prod_range_succ', Finset.prod_range_succ']
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Int.toNat_natCast,
      Int.toNat_eq_zero.2 (by omega : -(H : ℤ) ≤ 0), pow_zero, mul_one]
    rw [mul_left_comm, h1]
    simp only [map_mul]
    ring
  · intro s hs
    rcases s with _ | t
    · beta_reduce
      simp only [↓reduceIte]
      exact hlow (c₀ i)
    · beta_reduce
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [filS_succ, dvO_succ]
      exact Submodule.mem_map_of_mem ((hg i).2 t (by omega))
  · show algebraMap (LetA O n) W.EE (ps W 0 ^ H * v) * W.φE (F k) = _

    rw [hFe k, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul W.φE, AlgHom.commutes]
    ring

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

section

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UGen

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.KL

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

local notation "ιE" => algebraMap (LetA O n) W.EE
local notation "aev" => Polynomial.aeval (AlgHom.toLinearMap (W.γE W.gam) : Module.End O W.EE)

theorem numI_upd (H : ℕ → ℕ) (e s : ℕ) (hs : s < e) (x : ℤ) :
    numI W e (Function.update (fun t => -((H t : ℕ) : ℤ)) s x) = ps W s ^ x.toNat := by
  unfold numI
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hs), Function.update_self]
  rw [Finset.prod_eq_one fun t ht => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase ht)]
    rw [show (-((H t : ℕ) : ℤ)).toNat = 0 by omega, pow_zero], mul_one]

theorem denI_upd (H : ℕ → ℕ) (e s : ℕ) (hs : s < e) (x : ℤ) :
    denI W e (Function.update (fun t => -((H t : ℕ) : ℤ)) s x) =
      ps W s ^ (-x).toNat * ∏ t ∈ (Finset.range e).erase s, ps W t ^ H t := by
  unfold denI
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hs), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun t ht => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase ht), neg_neg, Int.toNat_natCast]

theorem aev_fixed (P : Polynomial O) : ∀ z : W.EE, W.γE W.gam z = z → aev P z = P.eval 1 • z := by
  induction P using Polynomial.induction_on with
  | C c => intro z _; simp [Polynomial.aeval_C, Module.algebraMap_end_apply]
  | add p q hp hq => intro z hz; rw [map_add (f := _), LinearMap.add_apply, hp z hz, hq z hz,
      Polynomial.eval_add, add_smul]
  | monomial k c ih =>
    intro z hz
    rw [pow_succ, ← mul_assoc, Polynomial.aeval_mul, mul_apply_eq_comp, Polynomial.aeval_X,
      AlgHom.toLinearMap_apply, hz, ih z hz]
    simp

theorem γE_const (a : ZMod n) (x : O) :
    W.γE W.gam (ιE (letE a) * algebraMap O W.EE x) = ιE (letE a) * algebraMap O W.EE x := by
  rw [map_mul, W.γE_ext, AlgHom.commutes]
  congr 2
  exact Formalism.MainNotions.UnusedSlot80.KL.γA_letE W W.gam a

theorem lE_eq (κ : ℕ) : lE W κ = algebraMap O W.EE (((PD.p : ℕ) : O) ^ κ) := by
  simp [lE]

def InvLevAt (s : ℕ) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 5 ≤ PD.p → ∀ (a : ZMod n) (T : Finset ℕ) (e : ℕ → ℕ), s ∉ T →
    ∀ f : W.EE, InFr W a 1 (∏ t ∈ T, ps W t ^ e t) f →
    (∃ κ : ℕ, InFr W a (ps W s) (∏ t ∈ T, ps W t ^ e t) (lE W κ * (W.γE W.gam f - f))) →
    ∃ (κ : ℕ) (x : O), InFr W a (ps W s) (∏ t ∈ T, ps W t ^ e t)
      (lE W κ * f - algebraMap (LetA O n) W.EE (letE a) * algebraMap O W.EE x)

theorem invLevAt_of (h : CutU.InvLevCore W) (s : ℕ) : InvLevAt W s :=
  fun hCA h5 a T e hs f hf hγ => h hCA h5 a s T e hs f hf hγ

theorem lev_const (hKL : KillerLevCore W) (hS : PsStable W)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5 : 5 ≤ PD.p) (a : ZMod n) (ell : ℕ) (H : ℕ → ℕ) (M : ℕ)
    (hM : ∀ s < ell, H s ≤ M) (y : W.EE) (hy : InId W a ell (fun t => -((H t : ℕ) : ℤ)) y)
    (s : ℕ) (hs : s < ell) (hInv : InvLevAt W s) :
    ∃ (κ : ℕ) (x : O), InId W a ell (Function.update (fun t => -((H t : ℕ) : ℤ)) s (H s))
      (lE W κ * PPγ W ell (Finset.Ico (-(M : ℤ)) M) y - ιE (letE a) * algebraMap O W.EE x) := by
  set α0 : ℕ → ℤ := fun t => -((H t : ℕ) : ℤ) with hα0
  set JS : Finset ℤ := Finset.Ico (-(M : ℤ)) M with hJS
  set Fp : ℤ → Polynomial O := fun i => Polynomial.X ^ (PD.p ^ ell) -
    Polynomial.C (((W.χΓ W.gam) ^ (i * (PD.p : ℤ) ^ ell) : Oˣ) : O) with hFp
  set Sg : Polynomial O := ∑ k ∈ Finset.range (PD.p ^ ell), Polynomial.X ^ k with hSg
  have hPP : PPO W ell JS = (∏ i ∈ JS.erase 0, Fp i) * Sg := rfl
  obtain ⟨-, hK⟩ := hKL hCA ell JS
  by_cases hH0 : H s = 0
  · refine ⟨0, 0, ?_⟩
    have e : Function.update α0 s ((H s : ℕ) : ℤ) = α0 := by
      rw [Function.update_eq_self_iff, hα0]; simp [hH0]
    rw [e, map_zero, mul_zero, sub_zero, lE, pow_zero, one_mul]
    exact inId_aeval W hS _ y hy
  have hH1 : 1 ≤ H s := Nat.one_le_iff_ne_zero.mpr hH0
  set Sm : Finset ℤ := Finset.Ico (-((H s : ℕ) : ℤ)) 0 with hSm
  set Sp : Finset ℤ := Finset.Ico 1 ((H s : ℕ) : ℤ) with hSp
  have hMs := hM s hs
  have hsub : Sm ∪ Sp ⊆ JS.erase 0 := by
    intro i hi
    simp only [Finset.mem_union, Finset.mem_Ico, hSm, hSp] at hi
    simp only [Finset.mem_erase, Finset.mem_Ico, hJS]
    omega
  have hdisj : Disjoint Sm Sp := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    simp only [Finset.mem_Ico, hSm, hSp] at h1 h2
    omega
  set Rest : Finset ℤ := JS.erase 0 \ (Sm ∪ Sp)
  have hPP' : PPO W ell JS = (∏ i ∈ Sp, Fp i) * (Sg * ((∏ i ∈ Sm, Fp i) * ∏ i ∈ Rest, Fp i)) := by
    rw [hPP, ← Finset.prod_sdiff hsub, Finset.prod_union hdisj]
    ring

  set y₁ := aev (∏ i ∈ Rest, Fp i) y with hy₁
  have hy₁m : InId W a ell α0 y₁ := inId_aeval W hS _ y hy

  obtain ⟨κ₁, h₁⟩ := (hK a α0 s hs y₁ hy₁m).2.2 (H s)
  have e1 : α0 s + ((H s : ℕ) : ℤ) = 0 := by simp [hα0]
  have e1' : Finset.Ico (α0 s) (α0 s + ((H s : ℕ) : ℤ)) = Sm := by rw [e1]
  rw [e1', e1] at h₁
  set y₂ := lE W κ₁ * aev (∏ i ∈ Sm, Fp i) y₁ with hy₂
  set α1 := Function.update α0 s 0 with hα1

  set Gg := aev Sg y₂ with hGg
  have hGm : InId W a ell α1 Gg := inId_aeval W hS _ y₂ h₁
  obtain ⟨κ₂, h₂⟩ := (hK a α1 s hs y₂ h₁).2.2 1
  have e2 : α1 s = 0 := by rw [hα1, Function.update_self]
  have hF0 : (∏ i ∈ Finset.Ico (α1 s) (α1 s + ((1 : ℕ) : ℤ)), Fp i) = Polynomial.X ^ (PD.p ^ ell) - 1 := by
    have hI : Finset.Ico (0 : ℤ) (0 + ((1 : ℕ) : ℤ)) = {0} := by ext i; simp; omega
    rw [e2, hI, Finset.prod_singleton]
    simp [hFp]
  rw [hF0, e2] at h₂
  have hupd1 : Function.update α1 s (0 + ((1 : ℕ) : ℤ)) = Function.update α0 s 1 := by
    rw [hα1, Function.update_idem]; norm_num
  rw [hupd1] at h₂
  have hγG : W.γE W.gam Gg - Gg = aev (Polynomial.X ^ (PD.p ^ ell) - 1 : Polynomial O) y₂ := by
    rw [← mul_geom_sum, aeval_mul_apply, ← hSg, ← hGg, map_sub, LinearMap.sub_apply,
      Polynomial.aeval_X, map_one, AlgHom.toLinearMap_apply, one_apply_eq_self]
  rw [← hγG] at h₂

  have hT : s ∉ (Finset.range ell).erase s := by simp
  have hGfr : InFr W a 1 (∏ t ∈ (Finset.range ell).erase s, ps W t ^ H t) Gg := by
    have := hGm
    unfold InId at this
    have en := numI_upd W H ell s hs 0
    have ed := denI_upd W H ell s hs 0
    simp only [numI, denI] at en ed
    rw [← hα0, ← hα1] at en ed
    rw [en, ed] at this
    simpa using this
  have hγfr : InFr W a (ps W s) (∏ t ∈ (Finset.range ell).erase s, ps W t ^ H t)
      (lE W κ₂ * (W.γE W.gam Gg - Gg)) := by
    have := h₂
    unfold InId at this
    have en := numI_upd W H ell s hs 1
    have ed := denI_upd W H ell s hs 1
    simp only [numI, denI] at en ed
    rw [← hα0] at en ed
    rw [en, ed] at this
    simpa using this
  obtain ⟨κ₃, x, hx⟩ := hInv hCA h5 a _ H hT Gg hGfr ⟨κ₂, hγfr⟩

  set Z := lE W κ₃ * Gg - ιE (letE a) * algebraMap O W.EE x with hZ
  set α2 := Function.update α0 s 1 with hα2
  have hZm : InId W a ell α2 Z := by
    unfold InId
    have en := numI_upd W H ell s hs 1
    have ed := denI_upd W H ell s hs 1
    simp only [numI, denI] at en ed
    rw [← hα0, ← hα2] at en ed
    rw [en, ed]
    simpa using hx
  obtain ⟨κ₄, h₄⟩ := (hK a α2 s hs Z hZm).2.2 (H s - 1)
  have e4 : α2 s + ((H s - 1 : ℕ) : ℤ) = ((H s : ℕ) : ℤ) := by
    rw [hα2, Function.update_self]; push_cast [Nat.cast_sub hH1]; ring
  have e4' : Finset.Ico (α2 s) (α2 s + ((H s - 1 : ℕ) : ℤ)) = Sp := by
    rw [e4, hα2, Function.update_self]
  rw [e4', e4, hα2, Function.update_idem] at h₄
  refine ⟨κ₄ + κ₃ + κ₁, ((PD.p : ℕ) : O) ^ κ₄ * (Polynomial.eval 1 (∏ i ∈ Sp, Fp i)) * x, ?_⟩
  convert h₄ using 1
  have hfix := aev_fixed W (∏ i ∈ Sp, Fp i) _ (γE_const W a x)
  have hmain : aev (∏ i ∈ Sp, Fp i) Gg = lE W κ₁ * PPγ W ell JS y := by
    rw [PPγ, hPP', aeval_mul_apply, aeval_mul_apply, aeval_mul_apply, ← hy₁, ← aeval_lE, ← aeval_lE,
      ← hy₂]
  rw [hZ, map_sub, aeval_lE, hmain, hfix, Algebra.smul_def, lE_eq, lE_eq, lE_eq, lE_eq]
  simp only [map_mul, map_pow, pow_add]
  ring

end Formalism.MainNotions.UnusedSlot80.UGen
end
end
