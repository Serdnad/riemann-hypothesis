module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.AtypicalPathSmallWeight
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.NegDminusLeMu
public import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeRename
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

theorem finite_St {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) : ({I | IsSt mu I} : Set (ℤ → Finset (Fin n))).Finite := by
  classical
  refine Set.Finite.of_injOn (f := fun I (c : colRange mu) => I c.1) (t := Set.univ) (fun _ _ => Set.mem_univ _) ?_
    Set.finite_univ
  intro I hI I' hI' h
  funext c
  by_cases hc : c ∈ colRange mu
  · exact congrFun h ⟨c, hc⟩
  · rw [hI.1 c hc, hI'.1 c hc]

theorem wt_eq (D : Formalism.BasicNotions.D7) (h3 : admB3 D) {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (hd : Dominant (pEnd mu)) :
    ({I | IsSt mu I} : Set (ℤ → Finset (Fin n))).ncard = stCount n (pEnd mu) := by
  have h1 := h3 n N mu hd
  have h2 := h3 n 0 (fun _ => pEnd mu) hd
  have h4 : ((Nat.card {I : ℤ → Finset (Fin n) // IsSt mu I} : ℕ) : ℚ) = ((stCount n (pEnd mu) : ℕ) : ℚ) := by
    rw [h1]; unfold stCount; rw [h2]; rfl
  rw [← Nat.card_coe_set_eq]
  exact_mod_cast h4

theorem stCount_zero (D : Formalism.BasicNotions.D7) (h3 : admB3 D) (n : ℕ) : stCount n (0 : Fin n → ℤ) = 1 := by
  have h2 := h3 n 0 (fun _ => (0 : Fin n → ℤ)) (fun _ _ _ => le_rfl)
  have h4 : ((stCount n (0 : Fin n → ℤ) : ℕ) : ℚ) = 1 := by
    unfold stCount
    rw [h2]
    refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => ?_
    split_ifs with hij
    · have : ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ) ≠ 0 := by
        have h5 : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast hij
        linarith
      simp only [pEnd, Pi.zero_apply, Int.cast_zero, sub_zero, zero_add]
      exact div_self this
    · rfl
  exact_mod_cast h4

theorem stCount_cast {n n' : ℕ} (h : n = n') (la : Fin n' → ℤ) :
    stCount n (fun l => la (Fin.cast h l)) = stCount n' la := by
  subst h; rfl

open Classical in
theorem pieri_vec (D : Formalism.BasicNotions.D7) (h5 : GenericProjectionCriterion D) (n : ℕ) (hn : 0 < n) (ν : Fin n → ℤ) (b : ℕ) (hd : Dominant ν) :
    stCount n ν * Nat.choose (b + n - 1) (n - 1) =
      ∑ μ ∈ (Fintype.piFinset fun i : Fin n => Finset.Icc (ν i) (ν i + b)).filter (fun μ => HStrip ν μ b),
        stCount n μ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (h5 m ν b hd).1

open Classical in
theorem pieri_cov (D : Formalism.BasicNotions.D7) (h5 : GenericProjectionCriterion D) (n : ℕ) (hn : 0 < n) (ν : Fin n → ℤ) (b : ℕ) (hd : Dominant ν) :
    stCount n ν * Nat.choose (b + n - 1) (n - 1) =
      ∑ μ ∈ (Fintype.piFinset fun i : Fin n => Finset.Icc (ν i - b) (ν i)).filter (fun μ => HStrip μ ν b),
        stCount n μ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (h5 m ν b hd).2

variable {N r K : ℕ}

def StepOK (LL : Letters (Fin N)) (n0 : ℕ) (B : Fin N → ℕ) (i : Fin N) (la la' : Fin (r + K) → ℤ) : Prop :=
  (i.val < n0 → if LL.vec i then HStrip la la' (B i) else HStrip la' la (B i)) ∧
  (n0 ≤ i.val → (∃ d : ℕ, HStrip la la' d) ∧ ∀ m : Fin (r + K), m.val ≤ i.val - n0 → la' m = (beA n0 B : ℤ))

def VP (LL : Letters (Fin N)) (n0 : ℕ) (B : Fin N → ℕ) (s : ℕ) (μ : Fin (N + 1) → Fin (r + K) → ℤ) : Prop :=
  μ 0 = 0 ∧ (∀ t : Fin (N + 1), t.val ≤ s → Dominant (μ t)) ∧
    ∀ i : Fin N, i.val < s → StepOK LL n0 B i (μ i.castSucc) (μ i.succ)

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

theorem sp_iff (H : HypT N n0 r K LL B od bb a La p) (μ : Fin (N + 1) → Fin (r + K) → ℤ) :
    μ ∈ SP (r := r) (K := K) LL n0 B ↔ VP LL n0 B N μ := by
  classical
  constructor
  · rintro ⟨dd, hP⟩
    obtain ⟨P, rfl⟩ := hP.path
    refine ⟨P.zero, fun t _ => P.dom t, fun i _ => ⟨fun hi => ?_, fun hi => ⟨⟨dd i, ?_⟩, fun m hm => hP.head i m hi hm⟩⟩⟩
    · have := P.step i
      rwa [hP.degs i hi] at this
    · exact step_vec P i (H.vec_true_of_late i (by omega))
  · rintro ⟨h0, hd, hs⟩
    have hex : ∀ i : Fin N, ∃ d : ℕ, (i.val < n0 → d = B i) ∧
        if LL.vec i then HStrip (μ i.castSucc) (μ i.succ) d else HStrip (μ i.succ) (μ i.castSucc) d := by
      intro i
      by_cases hi : i.val < n0
      · exact ⟨B i, fun _ => rfl, (hs i i.2).1 hi⟩
      · obtain ⟨d, hd'⟩ := ((hs i i.2).2 (by omega)).1
        refine ⟨d, fun h => absurd h hi, ?_⟩
        rw [if_pos (H.vec_true_of_late i (by omega))]
        exact hd'
    choose dd hdd using hex
    exact ⟨dd, ⟨⟨μ, h0, fun t => hd t (by have := t.2; omega), fun i => (hdd i).2⟩, rfl⟩, fun i hi => (hdd i).1 hi,
      fun i m hi hm => ((hs i i.2).2 hi).2 m hm⟩

theorem vp_le_dplus {s : ℕ} {μ : Fin (N + 1) → Fin (r + K) → ℤ} (h : VP LL n0 B s μ) :
    ∀ (t : ℕ) (ht : t < N + 1), t ≤ s → t ≤ n0 → ∀ m, μ ⟨t, ht⟩ m ≤ (dplus LL B t : ℤ) := by
  intro t
  induction t with
  | zero =>
    intro ht _ _ m
    have h0 : (⟨0, ht⟩ : Fin (N + 1)) = 0 := rfl
    rw [h0, h.1]; simp
  | succ t ih =>
    intro ht hts htn m
    have htN : t < N := by omega
    have ih' := ih (by omega) (by omega) (by omega) m
    have hst := (h.2.2 ⟨t, htN⟩ (by simp only; omega)).1 (by simp only; omega)
    have hd : dplus LL B (t + 1) = dplus LL B t + if LL.vec ⟨t, htN⟩ = true then B ⟨t, htN⟩ else 0 :=
      dsum_succ (fun l => LL.vec l = true) B t htN
    rw [hd]
    cases hv : LL.vec ⟨t, htN⟩ with
    | true =>
      rw [if_pos hv] at hst
      have h' : μ ⟨t + 1, ht⟩ m ≤ μ ⟨t, by omega⟩ m + (B ⟨t, htN⟩ : ℤ) := strip_le_add hst m
      simp only [if_true]
      push_cast
      linarith
    | false =>
      rw [if_neg (by simp [hv])] at hst
      have h' : μ ⟨t + 1, ht⟩ m ≤ μ ⟨t, by omega⟩ m := hst.1 m
      simp
      linarith

theorem dplus_le_beA' (t : ℕ) (ht : t ≤ n0) : dplus LL B t ≤ beA n0 B := by
  unfold dplus beA
  refine Finset.sum_le_sum fun l _ => ?_
  by_cases hl : l.val < t ∧ LL.vec l = true
  · rw [if_pos hl, if_pos (by omega)]
  · rw [if_neg hl]; exact Nat.zero_le _

theorem vp_le {s : ℕ} {μ : Fin (N + 1) → Fin (r + K) → ℤ} (h : VP LL n0 B s μ) :
    ∀ (t : ℕ) (ht : t < N + 1), t ≤ s → ∀ m, μ ⟨t, ht⟩ m ≤ (beA n0 B : ℤ) := by
  intro t
  induction t with
  | zero =>
    intro ht _ m
    have h0 : (⟨0, ht⟩ : Fin (N + 1)) = 0 := rfl
    rw [h0, h.1]; simp
  | succ t ih =>
    intro ht hts m
    by_cases htn : t + 1 ≤ n0
    · refine le_trans (vp_le_dplus h (t + 1) ht hts htn m) ?_
      exact_mod_cast dplus_le_beA' (t + 1) htn
    · have htN : t < N := by omega
      obtain ⟨⟨d, hst⟩, hhead⟩ := (h.2.2 ⟨t, htN⟩ (by simp only; omega)).2 (by simp only; omega)
      by_cases hm : m.val = 0
      · exact le_of_eq (hhead m (by omega))
      · have hm1 : (m.val - 1) + 1 < r + K := by have := m.2; omega
        have h2 := hst.2.1 ⟨m.val - 1, by have := m.2; omega⟩ hm1
        have hme : (⟨(m.val - 1) + 1, hm1⟩ : Fin (r + K)) = m := Fin.ext (by simp only; omega)
        rw [hme] at h2
        exact le_trans h2 (ih (by omega) (by omega) _)


open Classical in
theorem vp_update {s : ℕ} (hs : s < N) {μ : Fin (N + 1) → Fin (r + K) → ℤ} (h : VP LL n0 B s μ)
    (la' : Fin (r + K) → ℤ) (hd : Dominant la')
    (hst : StepOK LL n0 B ⟨s, hs⟩ (μ (⟨s, hs⟩ : Fin N).castSucc) la') :
    VP LL n0 B (s + 1) (Function.update μ (⟨s, hs⟩ : Fin N).succ la') := by
  have hne : ∀ t : Fin (N + 1), t.val ≤ s → t ≠ (⟨s, hs⟩ : Fin N).succ := by
    intro t ht he
    rw [he] at ht
    simp at ht
  refine ⟨?_, ?_, ?_⟩
  · rw [Function.update_of_ne (hne 0 (by simp))]; exact h.1
  · intro t ht
    by_cases he : t = (⟨s, hs⟩ : Fin N).succ
    · rw [he, Function.update_self]; exact hd
    · rw [Function.update_of_ne he]
      refine h.2.1 t ?_
      have : t.val ≠ s + 1 := fun hv => he (Fin.ext (by simpa using hv))
      omega
  · intro i hi
    by_cases he : i.val = s
    · have hi' : i = ⟨s, hs⟩ := Fin.ext he
      subst hi'
      rw [Function.update_self, Function.update_of_ne (hne _ (by simp))]
      exact hst
    · rw [Function.update_of_ne (hne _ (by simp; omega)), Function.update_of_ne (hne _ (by simp; omega))]
      exact h.2.2 i (by omega)

end

end Formalism.MainNotions.SelectionLemmas.Pf.T
end
end

section

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

structure Dat (n' r : ℕ) where
  F : Frames n' r
  deg : Fin n' → ℕ
  L₁ : ℕ
  N₁ : ℕ
  Ns : ℕ
  E₀ : ℕ
  mStar : ℕ
  E' : Fin n' → ℕ
  a : ℝ
  Y : ℝ
  Q : ℝ
  CLa : ℝ
  Ck : ℝ

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

structure Hyp : Prop where
  prime : p.Prime
  even : Even n'
  p13 : 13 ≤ p
  r2 : 2 ≤ r
  valid : X.F.Valid X.L₁ X.N₁
  degs : ∀ t ∈ X.F.TT, X.a ≤ (X.deg t : ℝ) ∧ (X.deg t : ℝ) ≤ 2 * X.a
  card : ∀ j : ℤ, (X.F.letters j).card ≤ X.Ns
  NsN₁ : X.Ns ≤ X.N₁
  NsN : X.Ns ≤ 2 * X.F.TT.card
  NsK : X.Ns + r ≤ K
  twist : ∀ j : ℤ, ∀ x ∈ X.F.letters j, (p : ℝ) ^ X.F.dist j x ≤ X.Q
  Y1 : 1 ≤ X.Y
  P1 : X.Ck * (X.Ns : ℝ) ^ 2 * Real.log X.a ≤ ((r + K : ℕ) : ℝ)
  P2 : 128 * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * X.Y ^ 2 ≤ (p : ℝ) ^ ((X.L₁ : ℤ) - 1)
  E'le : ∀ t ∈ X.F.TT, X.E' t ≤ X.E₀
  P3 : 32 * (p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * X.Q ^ 2 * ((X.E₀ : ℝ) + X.mStar + 1) ≤ X.a

def k : ℝ := ((r + K : ℕ) : ℝ)

def La : ℝ := X.CLa * (X.Ns : ℝ) ^ 2 * Real.log X.a

def Bo (j x : ℤ) : ℝ :=
  (X.deg (posOf n' (X.F.oldest j x)) : ℝ) / (p : ℝ) ^ X.F.dist j (X.F.oldest j x)

def sg (j x : ℤ) : ℕ := ⌊X.Bo p j x / (k (r := r) K ^ 2 * X.Y)⌋₊

def mg (j x : ℤ) : ℤ := (X.mStar : ℤ) + (X.sg p K j x : ℤ)

def th (j x : ℤ) : ℝ := X.Bo p j x / 2

def o (j x : ℤ) : ℝ :=
  X.La * X.a / ((p : ℝ) * k (r := r) K * (p : ℝ) ^ X.F.dist j x) +
    (if Even x then (10 : ℝ) else 1) * X.a * (p : ℝ) ^ (-((X.L₁ : ℤ) + (X.F.dist j x : ℤ)))

def d : Fin n' → ℕ := fun t => if t ∈ X.F.TT then X.deg t - X.E' t else 0

variable [NeZero r] [NeZero K]

def XXs (O : Type) [CommRing O] (j : ℤ) : Submodule O (SegRing O r K) :=
  XX' O r K X.F j (X.mg p K j) (X.th p j) (X.o p K j)

def gen (O : Type) [CommRing O] : Set (RRing O n' (r + K)) := Gen O p K X.F (X.XXs p K O) X.d

def NN (O : Type) [CommRing O] : Submodule O (RRing O n' (r + K)) := Submodule.span O (X.gen p K O)


omit [NeZero n'] [NeZero r] [NeZero K] in
def bound (Crk : ℝ) : ℝ := (1 - Crk * (X.F.TT.card : ℝ) * (r : ℝ) ^ 2 * k (r := r) K / X.Y) *
    ∏ t ∈ X.F.TT, ((Nat.choose (X.deg t + (r + K) - 1) (r + K - 1) : ℕ) : ℝ)

def NNbar (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    Submodule (FF O) (RRing (FF O) n' (r + K)) :=
  Submodule.span (FF O) (MvPolynomial.map (IsLocalRing.residue O) '' X.gen p K O)

end Dat

def RestDeg : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O],
    X.Hyp p K → 0 ≤ X.CLa →
    ∀ P ∈ X.NN p K O, ∀ mm ∈ P.support,
      (vsDeg mm : ℝ) ≤ 10 * (X.F.TT.card : ℝ) *
        (X.La * X.a / ((p : ℝ) * Dat.k (r := r) K) + X.a * (p : ℝ) ^ (-(X.L₁ : ℤ)) + Dat.k (r := r) K * X.Q)

def RestSel : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (σ : Type) (s : Set (σ →₀ ℕ)), s.Finite →
    ∀ G : Set (MvPolynomial σ O), (∀ g ∈ G, g ∈ restrictSupport O s) →
    ∃ Sg : Submodule O (MvPolynomial σ O), Sg ≤ Submodule.span O G ∧
      (∃ T : Submodule O (MvPolynomial σ O), IsCompl Sg T) ∧
      (∃ (ιb : Type) (b : Module.Basis ιb O Sg), ∀ i, (b i : MvPolynomial σ O) ∈ G) ∧
      Module.finrank O Sg =
        Module.finrank (FF O) (Submodule.span (FF O) (MvPolynomial.map (IsLocalRing.residue O) '' G))

def RestRank (C₀ Crk : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ((p : ℝ) ^ n') ^ (-((r * K : ℕ) : ℤ)) * X.bound K Crk ≤ (Module.finrank (FF O) (X.NNbar p K O) : ℝ)

theorem degSet_finite (n' k : ℕ) (d : Fin n' → ℕ) :
    {m : Fin n' × Fin k →₀ ℕ | ∀ t, ∑ c : Fin k, m (t, c) = d t}.Finite := by
  have hpi : (Set.pi Set.univ fun v : Fin n' × Fin k => Set.Iic (d v.1)).Finite :=
    Set.Finite.pi fun v => Set.finite_Iic _
  have hpre := Set.Finite.preimage (f := (Finsupp.equivFunOnFinite : (Fin n' × Fin k →₀ ℕ) → (Fin n' × Fin k → ℕ)))
    (fun a _ b _ hab => Finsupp.equivFunOnFinite.injective hab) hpi
  refine hpre.subset ?_
  intro m hm
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Iic, Finsupp.equivFunOnFinite_apply]
  intro v
  calc m v = m (v.1, v.2) := rfl
    _ ≤ ∑ c : Fin k, m (v.1, c) :=
        Finset.single_le_sum (f := fun c => m (v.1, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v.2)
    _ = d v.1 := hm v.1

theorem nonempty_dvr_setting_of_standard {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {jW : W →+* O} {w : O} (h : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ jW w) :
    Nonempty (UniformizedDVR p O) := by
  obtain ⟨hS, hw, -, -⟩ := h
  have hw0 : w ≠ 0 := hw.ne_zero
  have hwm : w ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal]; exact hw.not_isUnit
  refine ⟨⟨w, hw, ?_, ?_, hS.complete_O⟩⟩
  · rw [← hS.w_sq]; exact Ideal.pow_mem_of_mem _ hwm 2 (by norm_num)
  · rw [← hS.w_sq]; exact pow_ne_zero 2 hw0

theorem second_estimate_of_rank_bound (D : Formalism.BasicNotions.D7) (C₀ Crk : ℝ) (hC₀ : 0 < C₀) (hCrk : 0 < Crk)
    (hDeg : RestDeg) (hSel : RestSel) (hRank : AdmB D → RestRank C₀ Crk) : SecondPartClosed D := by
  intro hAdm
  refine ⟨C₀, hC₀, fun CLa Ck hCLa hCk => ⟨Crk, 10, hCrk, by norm_num, ?_⟩⟩
  intro p n' _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jW w hSet hp13 r K _ _ hr2 F deg L₁ N₁ Ns E₀ mStar E' a Y Q
    hV hdeg hcard hNsN₁ hNsN hNsK htw hY hP1 hP2 hE' hP3
  obtain ⟨S⟩ := nonempty_dvr_setting_of_standard hSet
  let X : Dat n' r := ⟨F, deg, L₁, N₁, Ns, E₀, mStar, E', a, Y, Q, CLa, Ck⟩
  have hX : X.Hyp p K :=
    ⟨hSet.1.prime, hSet.1.even, hp13, hr2, hV, hdeg, hcard, hNsN₁, hNsN, hNsK, htw, hY, hP1, hP2, hE', hP3⟩
  have hrk := hRank hAdm p n' r K X O S hX hCLa hCk
  have hdg := hDeg p n' r K X O hX (hC₀.le.trans hCLa)
  obtain ⟨Sg, hle, hT, hb, hfr⟩ := hSel O (Fin n' × Fin (r + K)) _ (degSet_finite n' (r + K) X.d) (X.gen p K O)
    (fun g hg => by obtain ⟨x, -, l, -, -, h⟩ := hg; exact h)
  have hrk' : ((p : ℝ) ^ n') ^ (-((r * K : ℕ) : ℤ)) * X.bound K Crk ≤ (Module.finrank O Sg : ℝ) := by
    rw [hfr]; exact hrk
  refine ⟨⟨Sg, hle, hT, hb, hrk', ?_⟩, hdg⟩
  intro FFq _ _ hcardF
  have h6 : Fintype.card FFq ^ (r * (r + K - r)) ≤ nPl FFq (r + K) r :=
    hAdm.2.2.2.2.2.1 FFq (r + K) r (Nat.le_add_right r K)
  rw [hcardF, Nat.add_sub_cancel_left] at h6
  have hq : (0 : ℝ) < ((p : ℝ) ^ n') ^ (r * K) := by
    have : (0 : ℝ) < p := by exact_mod_cast hSet.1.prime.pos
    positivity
  have h6' : ((p : ℝ) ^ n') ^ (r * K) ≤ (nPl FFq (r + K) r : ℝ) := by exact_mod_cast h6
  have hn : (0 : ℝ) < (nPl FFq (r + K) r : ℝ) := lt_of_lt_of_le hq h6'
  rcases le_or_gt (X.bound K Crk) 0 with hb0 | hb0
  · exact le_trans (div_nonpos_of_nonpos_of_nonneg hb0 hn.le) (Nat.cast_nonneg _)
  · refine le_trans ?_ hrk'
    rw [zpow_neg, zpow_natCast, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hq h6') hb0.le

end Formalism.MainNotions.SelectionLemmas.Pf
end
end
