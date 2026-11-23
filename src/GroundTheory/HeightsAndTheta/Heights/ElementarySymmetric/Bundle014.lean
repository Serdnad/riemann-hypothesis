module

public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapper
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperDiffPoly
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSnapperQuotFiltX
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle051
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle038
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle035
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperQuotAdd
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle040
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperSection
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle036
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle021
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
import Std.Tactic.BVDecide.Normalize.BitVec

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace InterNumEventual

def ind {n : ℕ} (T : Finset (Fin n)) : Fin n → ℕ := fun i => if i ∈ T then 1 else 0

theorem sum_sign_prod_ind {n : ℕ} (e : Fin n → ℕ) :
    ∑ T : Finset (Fin n), (-1 : ℚ) ^ (n - T.card) * ∏ i, ((ind T i : ℕ) : ℚ) ^ e i =
      ∏ i, (1 - (0 : ℚ) ^ e i) := by
  have h1 : ∏ i, (1 - (0 : ℚ) ^ e i) = ∏ i ∈ Finset.univ, (1 + -(0 : ℚ) ^ e i) := by
    simp only [sub_eq_add_neg]
  rw [h1, Finset.prod_add, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.prod_const_one, one_mul, Finset.prod_neg, Finset.card_univ_sdiff, Fintype.card_fin,
    ← Finset.prod_mul_prod_compl T, Finset.compl_eq_univ_sdiff]
  congr 1
  rw [Finset.prod_eq_one (fun i hi => by simp [ind, hi]), one_mul]
  exact Finset.prod_congr rfl fun i hi => by
    rw [Finset.mem_sdiff] at hi
    simp [ind, hi.2]

theorem mixed_eval {n : ℕ} (Q : MvPolynomial (Fin (n + 1)) ℚ) (hQ : Q.totalDegree ≤ n) (c : ℚ) :
    ∑ T : Finset (Fin n), (-1 : ℚ) ^ (n - T.card) *
        eval (Fin.snoc (α := fun _ => ℚ) (fun j => ((ind T j : ℕ) : ℚ)) c) Q =
      ∑ d ∈ Q.support, Q.coeff d * ∏ i : Fin n, (1 - (0 : ℚ) ^ d i.castSucc) := by
  simp only [MvPolynomial.eval_eq', Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  trans ∑ T : Finset (Fin n), Q.coeff d * c ^ d (Fin.last n) *
      ((-1 : ℚ) ^ (n - T.card) * ∏ i : Fin n, ((ind T i : ℕ) : ℚ) ^ d i.castSucc)
  · refine Finset.sum_congr rfl fun T _ => ?_
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    ring
  rw [← Finset.mul_sum, sum_sign_prod_ind]
  by_cases h0 : ∃ i : Fin n, d i.castSucc = 0
  · obtain ⟨i, hi⟩ := h0
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, pow_zero, sub_self])]
    ring
  · push Not at h0
    have hdeg := (le_totalDegree hd).trans hQ
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_castSucc] at hdeg
    have hge : n ≤ ∑ i : Fin n, d i.castSucc := by
      calc n = ∑ _i : Fin n, 1 := by simp
        _ ≤ ∑ i : Fin n, d i.castSucc :=
          Finset.sum_le_sum fun i _ => Nat.one_le_iff_ne_zero.mpr (h0 i)
    rw [show d (Fin.last n) = 0 by omega, pow_zero, mul_one]

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem foldl_twist_sub {n : ℕ} (L : Fin n → SubSystem k x Ω) (I : Chart x) :
    ∀ (l : List (Fin n)) (F : SubSystem k x Ω),
      (l.foldl (fun F i => F.twist (L i)) F).sub I = F.sub I * (l.map fun i => (L i).sub I).prod
  | [], F => by simp
  | a :: l, F => by
    rw [List.foldl_cons, foldl_twist_sub L I l, SubSystem.twist_sub_eq_mul_of_line, List.map_cons,
      List.prod_cons]
    ring

theorem tensorSub_sub {n : ℕ} (L : Fin n → SubSystem k x Ω) (T : Finset (Fin n)) (I : Chart x) :
    (tensorSub L T).sub I = (twistSys k x 0).sub I * ∏ i, (L i).sub I ^ ind T i := by
  unfold tensorSub
  rw [foldl_twist_sub, Fin.prod_univ_def]
  congr 1
  induction List.finRange n with
  | nil => simp
  | cons a l ih => by_cases ha : a ∈ T <;> simp [ha, ind, ih]

theorem tensorSub_eq_twistPows {n : ℕ} (L : Fin n → SubSystem k x Ω) (T : Finset (Fin n)) :
    tensorSub L T = (twistSys k x 0).twistPows n L (ind T) :=
  SubSystem.ext_sub fun I => by rw [tensorSub_sub, SnapperSections.twistPows_sub]

end InterNumEventual


open InterNumEventual in
theorem InterNumEventual.proof (hH : SnapperHyperplane.Statement.{u, w})
    (hS : SnapperSection.Statement.{u, w}) : InterNumEventual.Statement.{u, w} := by
  have hR : RestrLenEuler.Statement.{u, w} := RestrLenEuler.proof
  intro k _ Ω _ _ N x n pp L hW
  have := hW.isPrime
  obtain ⟨Q, hQ, hev⟩ := pieceChar_isNumPolyLT hH hS SnapperDiffPoly.proof L (n + 1) pp hW.isPrime hW.homog
    hW.le hW.dim.le 0
  have hQn : Q.totalDegree ≤ n := by
    rcases hQ with h | h
    · rw [h, totalDegree_zero]; exact Nat.zero_le _
    · omega
  have hall : ∀ᶠ c : ℕ in atTop, ∀ T : Finset (Fin n),
      restrLen pp ((tensorSub (fun i => (L i).toSubSystem) T).twist (twistSys k x (c : ℤ))) =
        pieceChar k pp 0 L (ind T) c := by
    refine Filter.eventually_all.mpr fun T => ?_
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (hR k Ω N x pp hW.homog hW.le n L (ind T))] with c hc
    rw [tensorSub_eq_twistPows]
    exact hc
  have hval : ∀ c : ℕ, (∀ T : Finset (Fin n),
      restrLen pp ((tensorSub (fun i => (L i).toSubSystem) T).twist (twistSys k x (c : ℤ))) =
        pieceChar k pp 0 L (ind T) c) →
      (interSum pp (fun i => (L i).toSubSystem) c : ℚ) =
        ∑ d ∈ Q.support, Q.coeff d * ∏ i : Fin n, (1 - (0 : ℚ) ^ d i.castSucc) := by
    intro c hc
    rw [← mixed_eval Q hQn (c : ℚ)]
    unfold interSum
    push_cast
    refine Finset.sum_congr rfl fun T _ => ?_
    have hT := hev (ind T) (c : ℤ)
    simp only at hT
    rw [hc T, hT, Int.cast_natCast]
  obtain ⟨c₀, hc₀⟩ := hall.exists
  refine ⟨interSum pp (fun i => (L i).toSubSystem) c₀, hall.mono fun c hc => ?_⟩
  exact_mod_cast (hval c hc).trans (hval c₀ hc₀).symm

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace MixedTwistShiftAlt

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem foldl_twist_sub {n : ℕ} (L : Fin n → SubSystem k x Ω) (I : Chart x) :
    ∀ (l : List (Fin n)) (F : SubSystem k x Ω),
      (l.foldl (fun F i => F.twist (L i)) F).sub I = F.sub I * (l.map fun i => (L i).sub I).prod
  | [], F => by simp
  | i :: l, F => by
    rw [List.foldl_cons, foldl_twist_sub L I l, SubSystem.twist_sub_eq_mul_of_line, List.map_cons,
      List.prod_cons]
    ring

theorem prod_map_filter {R : Type*} [CommMonoid R] {n : ℕ} (g : Fin n → R) (T : Finset (Fin n)) :
    ∀ l : List (Fin n),
      ((l.filter (· ∈ T)).map g).prod = (l.map fun j => g j ^ (if j ∈ T then 1 else 0)).prod
  | [] => rfl
  | j :: l => by
    by_cases hj : j ∈ T <;> simp [hj, prod_map_filter g T l]

theorem tensorSub_sub {n : ℕ} (L : Fin n → SubSystem k x Ω) (T : Finset (Fin n)) (I : Chart x) :
    (tensorSub L T).sub I = ∏ j, (L j).sub I ^ (if j ∈ T then 1 else 0) := by
  have h0 : (twistSys k x 0).sub I = 1 := (SubSystem.pow_sub (twistSys k x 0) 0 I).trans (pow_zero _)
  rw [tensorSub, foldl_twist_sub, h0, one_mul, prod_map_filter, Fin.prod_univ_def]

theorem twistPows_snoc_sub {n : ℕ} (L : Fin n → LineBundle k x) (M : LineBundle k x) (T : Finset (Fin n))
    (m : ℕ) (I : Chart x) :
    ((twistSys k x 0).twistPows (n + 1)
        (fun j => (Fin.snoc (α := fun _ => LineBundle k x) L M j).toSubSystem)
        (Fin.snoc (α := fun _ => ℕ) (fun i => if i ∈ T then 1 else 0) m)).sub I =
      M.sub I ^ m * (tensorSub (fun i => (L i).toSubSystem) T).sub I := by
  have h0 : (twistSys k x 0).sub I = 1 := (SubSystem.pow_sub (twistSys k x 0) 0 I).trans (pow_zero _)
  rw [SnapperSections.twistPows_sub, tensorSub_sub, h0, one_mul, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  ring

end MixedTwistShiftAlt


open MixedTwistShiftAlt in
theorem MixedTwistShift.proof (hH : SnapperHyperplane.Statement.{u, w}) (hS : SnapperSection.Statement.{u, w})
    (hP : SnapperDiffPoly.Statement) (hR : RestrLenEuler.Statement.{u, w}) (hD : SubsetDiffConst.Statement) :
    MixedTwistShift.Statement.{u, w} := by
  intro k _ Ω _ _ N x n qq hp hh hle hdim L M d
  set L' : Fin (n + 1) → LineBundle k x := Fin.snoc (α := fun _ => LineBundle k x) L M with hL'
  set ν : Finset (Fin n) → ℕ → Fin (n + 1) → ℕ :=
    fun T m => Fin.snoc (α := fun _ => ℕ) (fun i => if i ∈ T then 1 else 0) m with hν
  set f : (Fin (n + 1) → ℕ) → ℤ → ℚ := fun e c => (pieceChar k qq 0 L' e c : ℚ) with hf
  set Ls : Fin n → SubSystem k x Ω := fun i => (L i).toSubSystem with hLs

  have hA : ∀ T (c : ℤ), ((tensorSub Ls T).twist M.toSubSystem).twist (twistSys k x c) =
      ((twistSys k x 0).twistPows (n + 1) (fun j => (L' j).toSubSystem) (ν T 1)).twist (twistSys k x c) := by
    intro T c
    congr 1
    refine SubSystem.ext_sub fun I => ?_
    rw [twistPows_snoc_sub, SubSystem.twist_sub_eq_mul_of_line, pow_one]
  have hB : ∀ T (c : ℤ), (tensorSub Ls T).twist (twistSys k x c) =
      ((twistSys k x 0).twistPows (n + 1) (fun j => (L' j).toSubSystem) (ν T 0)).twist (twistSys k x c) := by
    intro T c
    congr 1
    refine SubSystem.ext_sub fun I => ?_
    rw [twistPows_snoc_sub, pow_zero, one_mul]

  have hev : ∀ m : ℕ, ∀ᶠ c : ℤ in atTop, ∀ T : Finset (Fin n),
      restrLen qq (((twistSys k x 0).twistPows (n + 1) (fun j => (L' j).toSubSystem) (ν T m)).twist
        (twistSys k x c)) = pieceChar k qq 0 L' (ν T m) c :=
    fun m => eventually_all.2 fun T => hR k Ω N x qq hh hle (n + 1) L' (ν T m)
  have hsum : ∀ (m : ℕ) (c : ℤ), (∀ T : Finset (Fin n),
      restrLen qq (((twistSys k x 0).twistPows (n + 1) (fun j => (L' j).toSubSystem) (ν T m)).twist
        (twistSys k x c)) = pieceChar k qq 0 L' (ν T m) c) →
      ((∑ T : Finset (Fin n), (-1 : ℤ) ^ (n - T.card) *
        restrLen qq (((twistSys k x 0).twistPows (n + 1) (fun j => (L' j).toSubSystem) (ν T m)).twist
          (twistSys k x c)) : ℤ) : ℚ) = subsetDiff n f m c := by
    intro m c h
    rw [subsetDiff]
    push_cast
    exact Finset.sum_congr rfl fun T _ => by rw [h T]
  obtain ⟨hconst, hzero⟩ := hD n f (pieceChar_isNumPolyLT hH hS hP L' (n + 1) qq hp hh hle hdim 0)
  have hT1 : Tendsto (fun c : ℕ => (c : ℤ) + d) atTop atTop :=
    tendsto_atTop_add_const_right _ d tendsto_natCast_atTop_atTop
  have hLhs : ∀ᶠ c : ℕ in atTop, ((∑ T : Finset (Fin n), (-1 : ℤ) ^ (n - T.card) *
      restrLen qq (((tensorSub Ls T).twist M.toSubSystem).twist (twistSys k x ((c : ℤ) + d))) : ℤ) : ℚ) =
        subsetDiff n f 1 ((c : ℤ) + d) := by
    filter_upwards [hT1.eventually (hev 1)] with c hc
    simp only [hA]
    exact hsum 1 _ hc
  split_ifs with hW
  ·
    have hI : ∀ᶠ c : ℕ in atTop, (interSum qq Ls c : ℚ) = subsetDiff n f 0 (c : ℤ) := by
      filter_upwards [tendsto_natCast_atTop_atTop.eventually (hev 0)] with c hc
      rw [interSum]
      simp only [hB]
      exact hsum 0 _ hc
    obtain ⟨c₀, hc₀⟩ := hI.exists_forall_of_atTop
    have hκ : ∀ᶠ c : ℕ in atTop, interSum qq Ls c = interSum qq Ls c₀ := by
      filter_upwards [eventually_ge_atTop c₀] with c hc
      exact_mod_cast (hc₀ c hc).trans ((hconst 0 0 c c₀).trans (hc₀ c₀ le_rfl).symm)
    have hlim : interNum qq Ls = interSum qq Ls c₀ :=
      (tendsto_const_nhds.congr' (hκ.mono fun _ hc => hc.symm)).limUnder_eq
    rw [hlim]
    filter_upwards [hLhs] with c hc
    exact_mod_cast hc.trans ((hconst 1 0 _ c₀).trans (hc₀ c₀ le_rfl).symm)
  ·
    have hlow : IsNumPolyLT (n + 1) n f := by
      by_cases hrel : ∃ i, (X i : Poly k N) ∉ qq
      · have := hp
        obtain ⟨e, he⟩ := SnapperSections.exists_dim_eq qq hh hrel
        have hen : e ≠ n := fun h => hW ⟨hp, hh, hle, hrel, by subst h; exact he⟩
        have hle' : e + 1 ≤ n + 1 := by
          rw [he] at hdim
          exact_mod_cast hdim
        refine pieceChar_isNumPolyLT hH hS hP L' n qq hp hh hle ?_ 0
        rw [he]
        exact_mod_cast (by omega : e + 1 ≤ n)
      · push Not at hrel
        exact ⟨0, Or.inl rfl, fun e c => by simp [hf, pieceChar_of_irrelevant qq hrel]⟩
    filter_upwards [hLhs] with c hc
    exact_mod_cast hc.trans (hzero hlow 1 _)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

universe u w

namespace SnapperSectionClosed

theorem snapperFinite : SnapperFinite.Statement.{u, w, w} :=
  SnapperFinite.proof Extension.full Extension.full TwistTilde.proof TwistTilde.proof TildeShift.proof
    (TildeFiniteE.proof SerreFinite.full)

theorem quotAdd : SnapperQuotAdd.Statement.{u, w, w} :=
  SnapperQuotAdd.proof (SnapperSubquotFinite.proof snapperFinite)

theorem quotDevissage : SnapperQuotDevissage.Statement.{u, w, w} :=
  SnapperQuotDevissage.proof SnapperQuotFilt.proof SnapperQuotIso.proof quotAdd SubFamilyTwist.proof

end SnapperSectionClosed


open SnapperSectionClosed in
theorem SnapperSection.full : SnapperSection.Statement.{u, w} :=
  SnapperSection.proof quotAdd quotDevissage MulQuotEq.proof SectionNonvanish.proof SectionMulInj.proof

end GroundTheory.Heights₂.Heights.Kleiman
end
