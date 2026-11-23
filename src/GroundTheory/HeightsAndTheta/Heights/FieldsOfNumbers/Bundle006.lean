module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Order.Filter.AtTopBot.Group

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter

noncomputable section

universe u

namespace MixedDiffConst

variable {K : Type}

def shiftPoly (b : K → ℤ) (p : MvPolynomial K ℚ) : MvPolynomial K ℚ :=
  aeval (fun k => X k - C ((b k : ℤ) : ℚ)) p

def polyStep (b : K → ℤ) (p : MvPolynomial K ℚ) : MvPolynomial K ℚ :=
  p - shiftPoly b p

theorem eval_shiftPoly (b : K → ℤ) (p : MvPolynomial K ℚ) (x : K → ℚ) :
    eval x (shiftPoly b p) = eval (fun k => x k - b k) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [shiftPoly]
  | add p q hp hq => simp only [shiftPoly, map_add (f := _)] at hp hq ⊢; rw [hp, hq]
  | mul_X p k hp => simp only [shiftPoly, map_mul] at hp ⊢; rw [hp]; simp

theorem monomial_good (b : K → ℤ) (s : K →₀ ℕ) (a : ℚ) :
    (shiftPoly b (monomial s a)).totalDegree ≤ (monomial s a).totalDegree ∧
      (polyStep b (monomial s a) = 0 ∨
        (polyStep b (monomial s a)).totalDegree + 1 ≤ (monomial s a).totalDegree) := by
  refine MvPolynomial.induction_on_monomial (motive := fun q =>
    (shiftPoly b q).totalDegree ≤ q.totalDegree ∧
      (polyStep b q = 0 ∨ (polyStep b q).totalDegree + 1 ≤ q.totalDegree)) ?_ ?_ s a
  · intro a; simp [shiftPoly, polyStep]
  · intro p k hp
    obtain ⟨h1, h2⟩ := hp
    by_cases hp0 : p = 0
    · subst hp0; simp [shiftPoly, polyStep]
    have hdeg : (p * X k).totalDegree = p.totalDegree + 1 := by
      rw [totalDegree_mul_of_isDomain hp0 (X_ne_zero k), totalDegree_X]
    have hXC : (X k - C ((b k : ℤ) : ℚ) : MvPolynomial K ℚ).totalDegree ≤ 1 :=
      (totalDegree_sub _ _).trans (max_le (totalDegree_X k).le (by rw [totalDegree_C]; omega))
    have hsh : shiftPoly b (p * X k) = shiftPoly b p * (X k - C ((b k : ℤ) : ℚ)) := by
      simp [shiftPoly]
    have hst : polyStep b (p * X k) = polyStep b p * X k + C ((b k : ℤ) : ℚ) * shiftPoly b p := by
      rw [polyStep, polyStep, hsh]; ring
    refine ⟨?_, Or.inr ?_⟩
    · rw [hsh, hdeg]
      exact (totalDegree_mul _ _).trans (add_le_add h1 hXC)
    · rw [hst, hdeg, add_le_add_iff_right]
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · rcases h2 with h2 | h2
        · rw [h2, zero_mul, totalDegree_zero]; exact zero_le
        · exact (totalDegree_mul _ _).trans (by rw [totalDegree_X]; exact h2)
      · exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add]; exact h1)

theorem sum_eq (b : K → ℤ) (p : MvPolynomial K ℚ) :
    shiftPoly b p = ∑ v ∈ p.support, shiftPoly b (monomial v (AddMonoidAlgebra.coeff p v)) ∧
      polyStep b p = ∑ v ∈ p.support, polyStep b (monomial v (AddMonoidAlgebra.coeff p v)) := by
  have hs : shiftPoly b p = ∑ v ∈ p.support, shiftPoly b (monomial v (AddMonoidAlgebra.coeff p v)) := by
    conv_lhs => rw [p.as_sum]

    simp only [shiftPoly, map_sum]
  refine ⟨hs, ?_⟩
  simp only [polyStep, Finset.sum_sub_distrib]
  rw [← hs, ← p.as_sum]

theorem monomial_le (p : MvPolynomial K ℚ) {v : K →₀ ℕ} (hv : v ∈ p.support) :
    (monomial v (AddMonoidAlgebra.coeff p v)).totalDegree ≤ p.totalDegree :=
  (totalDegree_monomial_le _ _).trans (le_totalDegree hv)

theorem polyStep_deg (b : K → ℤ) (p : MvPolynomial K ℚ) :
    polyStep b p = 0 ∨ (polyStep b p).totalDegree + 1 ≤ p.totalDegree := by
  by_cases h0 : p.totalDegree = 0
  · left
    rw [totalDegree_eq_zero_iff_eq_C] at h0
    rw [h0]; simp [polyStep, shiftPoly]
  · right
    have : (polyStep b p).totalDegree ≤ p.totalDegree - 1 := by
      rw [(sum_eq b p).2]
      refine totalDegree_finsetSum_le fun v hv => ?_
      rcases (monomial_good b v (AddMonoidAlgebra.coeff p v)).2 with h | h
      · rw [h, totalDegree_zero]; exact zero_le
      · have := monomial_le p hv; omega
    omega

section Eventual

theorem eventuallyPoly_diffStep (b : K → ℤ) {g : (K → ℤ) → ℤ} {q : MvPolynomial K ℚ}
    (hq : EventuallyPoly g q) : EventuallyPoly (diffStep b g) (polyStep b q) := by
  have ht : Tendsto (fun m : K → ℤ => m - b) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-b) tendsto_id
  filter_upwards [hq, ht.eventually hq] with m h1 h2
  simp only [diffStep, polyStep, map_sub, eval_shiftPoly]
  rw [Int.cast_sub, h1, h2]
  simp [Pi.sub_apply]

theorem eventuallyPoly_foldr (L : List (K → ℤ)) {h : (K → ℤ) → ℤ} {p : MvPolynomial K ℚ}
    (hp : EventuallyPoly h p) : EventuallyPoly (L.foldr diffStep h) (L.foldr polyStep p) := by
  induction L with
  | nil => simpa using hp
  | cons b L ih => simpa using eventuallyPoly_diffStep b ih

theorem foldr_polyStep_deg (L : List (K → ℤ)) (p : MvPolynomial K ℚ) :
    L.foldr polyStep p = 0 ∨ (L.foldr polyStep p).totalDegree + L.length ≤ p.totalDegree := by
  induction L with
  | nil => simp
  | cons b L ih =>
    simp only [List.foldr_cons, List.length_cons]
    rcases ih with h0 | hd
    · left; rw [h0]; simp [polyStep, shiftPoly]
    · rcases polyStep_deg b (L.foldr polyStep p) with h | h
      · exact Or.inl h
      · right; omega

end Eventual

end MixedDiffConst


open MixedDiffConst in
theorem MixedDiffConst.proof (h1 : HilbDegreeBound.Statement.{u})
    (h2 : HilbEventuallyPoly.Statement.{u}) : MixedDiffConst.Statement.{u} := by
  intro F _ K _ _ ι _ I hI hrel n hn
  obtain ⟨p, hp⟩ := h2 F K ι I hI
  have hdeg : p.totalDegree ≤ n := by
    by_cases hp0 : p = 0
    · simp [hp0]
    · have := (h1 F K ι I hI).1 hrel p hp hp0
      rw [hn] at this
      exact_mod_cast this
  have key : ∀ (r : ℕ) (bs : Fin r → K → ℤ), n ≤ r → ∃ c : ℚ, (n < r → c = 0) ∧
      ∀ᶠ m in atTop, (mixedDiff bs (hilbFn I) m : ℚ) = c := by
    intro r bs hr
    have hE := eventuallyPoly_foldr (List.ofFn bs) hp
    rcases foldr_polyStep_deg (List.ofFn bs) p with h0 | hd
    · refine ⟨0, fun _ => rfl, ?_⟩
      filter_upwards [hE] with m hm
      rw [mixedDiff, hm, h0, map_zero]
    · rw [List.length_ofFn] at hd
      have hq0 : ((List.ofFn bs).foldr polyStep p).totalDegree = 0 := by omega
      refine ⟨AddMonoidAlgebra.coeff ((List.ofFn bs).foldr polyStep p) 0, fun hlt => by omega, ?_⟩
      rw [totalDegree_eq_zero_iff_eq_C] at hq0
      filter_upwards [hE] with m hm
      rw [mixedDiff, hm, hq0, eval_C, coeff_C, if_pos rfl]
  constructor
  · intro bs
    obtain ⟨c, -, hc⟩ := key n bs le_rfl
    obtain ⟨m0, hm0⟩ := hc.exists
    have hc' : ∀ᶠ m in atTop, mixedDiff bs (hilbFn I) m = mixedDiff bs (hilbFn I) m0 :=
      hc.mono fun m hm => by exact_mod_cast hm.trans hm0.symm
    have hex : ∃ c, ∀ᶠ m in atTop, mixedDiff bs (hilbFn I) m = c := ⟨_, hc'⟩
    have hval : intNum F I bs = mixedDiff bs (hilbFn I) m0 := by
      unfold intNum eventualValue
      rw [dite_eq_left hex]
      obtain ⟨m, hm1, hm2⟩ := (hex.choose_spec.and hc').exists
      rw [← hm1, hm2]
    filter_upwards [hc'] with m hm
    rw [hm, hval]
  · intro r hr bs
    obtain ⟨c, hc0, hc⟩ := key r bs hr.le
    filter_upwards [hc] with m hm
    rw [hc0 hr] at hm
    exact_mod_cast hm

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open GroundTheory.Heights₂.Heights.NumbersDVR Filter

universe u

section

variable {K : Type*}

theorem diffStep_zero_left (h : (K → ℤ) → ℤ) : diffStep 0 h = 0 := by
  funext m
  simp [diffStep]

theorem diffStep_zero_right (b : K → ℤ) : diffStep b (0 : (K → ℤ) → ℤ) = 0 := by
  funext m
  simp [diffStep]

theorem foldr_diffStep_eq_zero_of_mem (l : List (K → ℤ)) (hl : (0 : K → ℤ) ∈ l)
    (h : (K → ℤ) → ℤ) : l.foldr diffStep h = 0 := by
  induction l with
  | nil => simp at hl
  | cons a t ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp hl with rfl | ht
    · exact diffStep_zero_left _
    · rw [ih ht]
      exact diffStep_zero_right a

theorem mixedDiff_coord_zero {n : ℕ} (bs : Fin n → K → ℤ) (i : Fin n) (hi : bs i = 0)
    (h : (K → ℤ) → ℤ) : mixedDiff bs h = 0 :=
  foldr_diffStep_eq_zero_of_mem _ (List.mem_ofFn.mpr ⟨i, hi⟩) h

theorem diffStep_eventually_zero {b : K → ℤ} {h : (K → ℤ) → ℤ}
    (hh : ∀ᶠ m in atTop, h m = 0) : ∀ᶠ m in atTop, diffStep b h m = 0 := by
  have hs : ∀ᶠ m in atTop, h (m + -b) = 0 :=
    (tendsto_atTop_add_const_right atTop (-b) tendsto_id).eventually hh
  filter_upwards [hh, hs] with m h1 h2
  simp only [diffStep, h1, ← sub_eq_add_neg] at h2 ⊢
  rw [h2, sub_zero]

theorem mixedDiff_eventually_zero {n : ℕ} (bs : Fin n → K → ℤ) {h : (K → ℤ) → ℤ}
    (hh : ∀ᶠ m in atTop, h m = 0) : ∀ᶠ m in atTop, mixedDiff bs h m = 0 := by
  unfold mixedDiff
  induction List.ofFn bs with
  | nil => simpa using hh
  | cons a t ih => exact diffStep_eventually_zero ih

theorem eventualValue_eq_zero {f : (K → ℤ) → ℤ} (hf : ∀ᶠ m in atTop, f m = 0) :
    eventualValue f = 0 := by
  unfold eventualValue
  have hex : ∃ c, ∀ᶠ m in atTop, f m = c := ⟨0, hf⟩
  rw [dite_eq_left hex]
  obtain ⟨m, h1, h2⟩ := (hex.choose_spec.and hf).exists
  rw [← h1, h2]

end

theorem exists_nat_of_le_of_lt {x : WithBot (WithTop ℤ)} {t n : ℕ}
    (h1 : (t : WithBot (WithTop ℤ)) ≤ x) (h2 : x < n) : ∃ d : ℕ, x = d := by
  rw [← WithBot.coe_natCast, ← WithTop.coe_natCast] at h1 h2
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h1 (not_le.mpr (WithBot.bot_lt_coe _))
  | coe y =>
    induction y using WithTop.recTopCoe with
    | top => exact absurd h2 (not_lt.mpr (WithBot.coe_le_coe.mpr le_top))
    | coe z =>
      have hz : (t : ℤ) ≤ z := WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp h1)
      refine ⟨z.toNat, ?_⟩
      rw [← WithBot.coe_natCast, ← WithTop.coe_natCast, Int.toNat_of_nonneg (by omega)]

theorem IntNumZeroSlot.proof (h₁ : MixedDiffConst.Statement.{u})
    (h₂ : HilbEventuallyPoly.Statement.{u}) (h₃ : HilbDegreeBound.Statement.{u}) :
    IntNumZeroSlot.Statement.{u} := by
  intro F _ K _ _ ι _ I
  refine ⟨fun n bs i hi => ?_, fun hI n bs hn => ?_⟩
  · unfold intNum
    refine eventualValue_eq_zero (Eventually.of_forall fun m => ?_)
    rw [mixedDiff_coord_zero bs i hi]
    rfl
  · unfold intNum
    apply eventualValue_eq_zero
    by_cases hR : IsRelevant I
    · by_cases hd : ∃ d : ℕ, relDim I = d
      · obtain ⟨d, hd⟩ := hd
        have hdn : d < n := by
          rw [hd] at hn
          exact_mod_cast hn
        exact (h₁ F K ι I hI hR d hd).2 n hdn bs
      · obtain ⟨p, hp⟩ := h₂ F K ι I hI
        have hp0 : p = 0 := by
          by_contra hne
          exact hd (exists_nat_of_le_of_lt ((h₃ F K ι I hI).1 hR p hp hne) hn)
        apply mixedDiff_eventually_zero
        filter_upwards [hp] with m hm
        rw [hp0, map_zero] at hm
        exact_mod_cast hm
    · exact mixedDiff_eventually_zero bs ((h₃ F K ι I hI).2 hR)

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open GroundTheory.Heights₂.Heights.NumbersDVR

universe u

section

variable {K : Type*}

theorem diffStep_add (b b' : K → ℤ) (h : (K → ℤ) → ℤ) (m : K → ℤ) :
    diffStep (b + b') h m = diffStep b h m + diffStep b' h (m - b) := by
  simp only [diffStep, sub_add_eq_sub_sub]
  ring

theorem foldr_diffStep_set_add (h : (K → ℤ) → ℤ) (b b' : K → ℤ) :
    ∀ (L : List (K → ℤ)) (i : ℕ), i < L.length → ∀ m : K → ℤ,
      (L.set i (b + b')).foldr diffStep h m =
        (L.set i b).foldr diffStep h m + (L.set i b').foldr diffStep h (m - b)
  | [], i, hi, _ => absurd hi (Nat.not_lt_zero _)
  | a :: L, 0, _, m => by
      simp only [List.set_cons_zero, List.foldr_cons]
      exact diffStep_add b b' _ m
  | a :: L, i + 1, hi, m => by
      simp only [List.set_cons_succ, List.foldr_cons, diffStep]
      have hi' : i < L.length := by simpa using hi
      rw [foldr_diffStep_set_add h b b' L i hi' m, foldr_diffStep_set_add h b b' L i hi' (m - a),
        ← sub_right_comm m a b]
      ring

theorem ofFn_update {α : Type*} {n : ℕ} (bs : Fin n → α) (i : Fin n) (x : α) :
    List.ofFn (Function.update bs i x) = (List.ofFn bs).set i x := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.getElem_ofFn, List.getElem_set, Function.update_apply, Fin.ext_iff]
    split_ifs with h h' h'
    · rfl
    · exact absurd h.symm h'
    · exact absurd h'.symm h
    · rfl

theorem mixedDiff_update_add {n : ℕ} (bs : Fin n → K → ℤ) (i : Fin n) (b b' : K → ℤ)
    (h : (K → ℤ) → ℤ) (m : K → ℤ) :
    mixedDiff (Function.update bs i (b + b')) h m =
      mixedDiff (Function.update bs i b) h m + mixedDiff (Function.update bs i b') h (m - b) := by
  simp only [mixedDiff, ofFn_update]
  exact foldr_diffStep_set_add h b b' _ i (by simp) m

theorem tendsto_sub_const_atTop (b : K → ℤ) :
    Filter.Tendsto (fun m : K → ℤ => m - b) Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_atTop.2 fun c => ⟨c + b, fun _ hm => le_sub_iff_add_le.mpr hm⟩

theorem IntNumAdd.proof (h1 : MixedDiffConst.Statement.{u}) : IntNumAdd.Statement.{u} := by
  intro F _ K _ _ ι _ I hI hrel n hn bs i b b'
  have e := fun x : K → ℤ => (h1 F K ι I hI hrel n hn).1 (Function.update bs i x)
  have e' := (tendsto_sub_const_atTop b).eventually (e b')
  obtain ⟨m, h0, hb, hb'⟩ := ((e (b + b')).and ((e b).and e')).exists
  rw [← h0, ← hb, ← hb']
  exact mixedDiff_update_add bs i b b' _ m

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def EventuallyPolyUnique.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (h : (K → ℤ) → ℤ) (p q : MvPolynomial K ℚ),
    EventuallyPoly h p → EventuallyPoly h q → p = q

def EventuallyPolyShift.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (h : (K → ℤ) → ℤ) (p : MvPolynomial K ℚ) (c : K → ℤ),
    EventuallyPoly h p → ∃ q : MvPolynomial K ℚ,
      EventuallyPoly (fun m => h (m - c)) q ∧ q.totalDegree ≤ p.totalDegree ∧ (p = 0 → q = 0)

def HilbIrrelevantZero.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)), ¬ IsRelevant I →
    ∀ᶠ m in Filter.atTop, hilbFn I m = 0

def RelevantPrimeDimGe.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)), IsMultiProjPrime P →
    ((Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι F ⧸ P)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DivPushForward.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ (c : K → ℕ) (a : MRing (fun k => ι' (j k)) F), IsMultiHomog a c →
    a ∉ contractPrime j P' →
    ∀ (N' : Ideal (MRing ι' F) → ℤ) (N : Ideal (MRing (fun k => ι' (j k)) F) → ℤ),
      (∀ W' (hW' : IsMultiProjPrime W'), relDim W' = (n : ℕ) →
        relDim (contractPrime j W') = (n : ℕ) →
        haveI := hW'.isPrime
        N' W' = relDeg j W' * N (contractPrime j W')) →
      (∀ W', IsMultiProjPrime W' → relDim W' = (n : ℕ) → relDim (contractPrime j W') < (n : ℕ) →
        N' W' = 0) →
      haveI := hP'.isPrime
      cycEval N' (divCycle P' (rename (blockIncl j ι') a)) =
        relDeg j P' * cycEval N (divCycle (contractPrime j P') a)


end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DivCycleSupport.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)), IsMultiProjPrime P →
    ∀ n : ℕ, relDim P = (n + 1 : ℕ) → ∀ (c : K → ℕ) (f : MRing ι F), IsMultiHomog f c → f ∉ P →
    ∀ W : Ideal (MRing ι F), divCycle P f W ≠ 0 → IsMultiProjPrime W ∧ relDim W = (n : ℕ)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end
