module

public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPowSt

@[expose] public section

section

open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S.ThB

namespace GlobalTheory.BpStdNum

theorem gapOK_of (k r : ℕ) (hk : 1 ≤ k) (h : ℝ)
    (hh : 10 ^ 6 * (((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) ≤ h) :
    ThreeDimData.GapOK k r (h / 4) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = 2 * ((r : ℝ) + 1) := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = 2 * (r : ℝ) + k + 1 := ⟨_, rfl⟩
  have em : ((2 * r + 2 : ℕ) : ℝ) = m := by rw [hm]; push_cast; ring
  have en : ((2 * r + k + 1 : ℕ) : ℝ) = n := by rw [hn]; push_cast; ring
  have hm1 : 1 ≤ m := by linarith
  have hmn : m ≤ n := by linarith
  have hn1 : 1 ≤ n := by linarith
  have hs1 : 1 ≤ Real.sqrt m := Real.one_le_sqrt.mpr hm1
  have e9 : m ^ ((9 : ℝ) / 2) = m ^ 4 * Real.sqrt m := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add (by linarith)]
    norm_num
  rw [em, en, e9] at hh
  have hm2 : 1 ≤ m ^ 2 := one_le_pow₀ hm1
  have hm4 : 1 ≤ m ^ 4 := one_le_pow₀ hm1
  have hn3 : 1 ≤ n ^ 3 := one_le_pow₀ hn1
  have ha : 1000 * (m ^ 4 * n ^ 3) ≤ ThreeDimData.aOf r (h / 4) := by
    unfold ThreeDimData.aOf
    rw [← hm, le_div_iff₀ (by positivity)]
    have : 0 ≤ m ^ 4 * Real.sqrt m * n ^ 3 := by positivity
    nlinarith
  have hM : ThreeDimData.Mexp r ≤ m ^ 2 := by unfold ThreeDimData.Mexp; rw [hm]; nlinarith
  have hM0 : 0 ≤ ThreeDimData.Mexp r := by unfold ThreeDimData.Mexp; positivity
  have hG : ThreeDimData.AG k r ≤ 4 * n ^ 2 := by unfold ThreeDimData.AG; rw [hn]; nlinarith
  have hG0 : 0 ≤ ThreeDimData.AG k r := by unfold ThreeDimData.AG; positivity
  have hd : ThreeDimData.dN k r ≤ n ^ 2 := by unfold ThreeDimData.dN; rw [hn]; nlinarith
  have hn23 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ hn1 (by norm_num)
  have hm24 : m ^ 2 ≤ m ^ 4 := pow_le_pow_right₀ hm1 (by norm_num)
  have hS : ThreeDimData.AS k r ≤ n ^ 3 := by
    unfold ThreeDimData.AS
    have h1 : ((2 * r + k : ℕ) : ℝ) ≤ n := by rw [hn]; push_cast; linarith
    calc ((2 * r + k : ℕ) : ℝ) * ThreeDimData.dN k r ≤ ((2 * r + k : ℕ) : ℝ) * n ^ 2 :=
          mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg _)
      _ ≤ n * n ^ 2 := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = n ^ 3 := by ring
  have hX : n ^ 3 ≤ m ^ 4 * n ^ 3 := le_mul_of_one_le_left (by positivity) hm4
  refine ⟨hk, ?_, ?_, ?_⟩
  · rw [en]
    have : m ^ 4 * n ^ 3 ≤ m ^ 4 * Real.sqrt m * n ^ 3 := by
      have := mul_le_mul_of_nonneg_left hs1 (show 0 ≤ m ^ 4 * n ^ 3 by positivity)
      linarith
    linarith
  · have h1 : ThreeDimData.Mexp r * (ThreeDimData.AS k r + ThreeDimData.AG k r) ≤ m ^ 4 * (5 * n ^ 3) :=
      calc _ ≤ ThreeDimData.Mexp r * (5 * n ^ 3) := mul_le_mul_of_nonneg_left (by linarith) hM0
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  · rw [en]
    have h1 : ((r : ℝ) + 1) * n ^ 2 ≤ n * n ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : n * n ^ 2 = n ^ 3 := by ring
    linarith

section
variable {k r : ℕ} {lam : Fin (2 * r + k + 1) → ℝ} {u : ℕ → ℝ}

theorem lt_left (hk : 1 ≤ k)
    (hI : Formalism.MainNotions.S.InterlaceS (k := k) (by omega) (fun i => u (i.val + 1)) lam)
    (a : Fin (2 * r + k + 1)) (ha : a.val < k) : lam a < u (a.val + 1) := by
  by_cases h : a.val + 1 < k
  · exact (hI.1 a.val h).1
  · have h2 := hI.2 (by omega)
    have e : a = ⟨k - 1, by omega⟩ := Fin.ext (by simp only; omega)
    rw [e]; exact h2

theorem lt_right
    (hI : Formalism.MainNotions.S.InterlaceS (k := k) (by omega) (fun i => u (i.val + 1)) lam)
    (a : Fin (2 * r + k + 1)) (ha : a.val + 1 < k) : u (a.val + 2) < lam a :=
  (hI.1 a.val ha).2

theorem cloud_of
    (hI : Formalism.MainNotions.S.InterlaceS (k := k) (by omega) (fun i => u (i.val + 1)) lam)
    (a : Fin (2 * r + k + 1)) (ha : a.val + 1 < k) :
    IsCloud (fun i : Fin k => u (i.val + 1)) lam a :=
  ⟨⟨⟨a.val, by omega⟩, (hI.1 a.val ha).1⟩, ⟨⟨a.val + 1, ha⟩, (hI.1 a.val ha).2⟩⟩

theorem not_cloud_of (hk : 1 ≤ k) (hA : StrictAnti lam)
    (hI : Formalism.MainNotions.S.InterlaceS (k := k) (by omega) (fun i => u (i.val + 1)) lam)
    (a : Fin (2 * r + k + 1)) (ha : k ≤ a.val + 1) :
    ¬ IsCloud (fun i : Fin k => u (i.val + 1)) lam a := by
  rintro ⟨-, i, hi⟩
  have hik := i.isLt
  have key : ∀ j : ℕ, j < k → lam a < u (k - 1 - j + 1) := by
    intro j
    induction j with
    | zero =>
      intro _
      have h1 := lt_left hk hI ⟨k - 1, by omega⟩ (by simp only; omega)
      have h2 : lam a ≤ lam ⟨k - 1, by omega⟩ := hA.antitone (by
        rw [Fin.le_def]; simp only; omega)
      simp only [Nat.sub_zero] at h1 ⊢
      linarith
    | succ j ih =>
      intro hj
      have h0 := ih (by omega)
      have h1 := hI.1 (k - 1 - (j + 1)) (by omega)
      simp only at h1
      have e : k - 1 - (j + 1) + 1 = k - 1 - j := by omega
      have h4 : u (k - 1 - (j + 1) + 1 + 1) < u (k - 1 - (j + 1) + 1) := lt_trans h1.2 h1.1
      rw [e] at h4 ⊢
      linarith
  have h3 := key (k - 1 - i.val) (by omega)
  have e : k - 1 - (k - 1 - i.val) = i.val := by omega
  rw [e] at h3
  simp only at hi
  linarith

theorem half_of (hH : Formalism.QuantumDeterminants.IsHCParam lam)
    (hu : ∀ i ∈ Finset.Icc 1 k, ∃ a : ℤ, u i = (a : ℝ) + ((k : ℝ) - 1) / 2) :
    ∀ a, ∀ i ∈ Finset.Icc 1 k, ∃ m : ℤ, lam a - u i = (m : ℝ) + 1 / 2 := by
  intro a i hi
  obtain ⟨x, hx⟩ := hH.2 a
  obtain ⟨y, hy⟩ := hu i hi
  refine ⟨x - y + r, ?_⟩
  push_cast at hx ⊢
  linarith

theorem bound_of {b : ℝ} (hb : ∀ i : Fin k, |u (i.val + 1)| ≤ b) : ∀ i ∈ Finset.Icc 1 k, |u i| ≤ b := by
  intro i hi
  rw [Finset.mem_Icc] at hi
  have := hb ⟨i - 1, by omega⟩
  simp only at this
  rwa [Nat.sub_add_cancel hi.1] at this

end

theorem num_of_stdHyp : ∀ Cq : ℝ, 0 ≤ Cq → ∃ Cg₀ : ℝ, ∀ (Ch Cg : ℝ), Cg₀ ≤ Cg → ∀ (P : M.Par) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (T T' ka b d : ℝ) (q0 : ℕ), 2 ≤ P.k → StdHyp Ch Cg P.k P.r (PI.BesselPeriodGGP.eps48 P.k P.r) lam (fun i => P.u (i.val + 1)) (fun i => P.u' (i.val + 1)) T T' ka b → (∀ i ∈ Finset.Icc 1 P.k, (∃ a : ℤ, P.u i = (a : ℝ) + ((P.k : ℝ) - 1) / 2) ∧ ∃ a : ℤ, P.u' i = (a : ℝ) + ((P.k : ℝ) - 1) / 2) → 0 ≤ d → AllGaps lam (200 * d) → (q0 : ℝ) ≤ d + Cq * ((2 * P.r + 2 : ℕ) : ℝ) ^ 3 → ∃ bv ga h : ℝ, BranchingSupport.Num P.k P.r lam P.u b bv ga h q0 ∧ BranchingSupport.Num P.k P.r lam P.u' b bv ga h q0 ∧ Cg * (((2 * P.r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) * (((3 * (P.r + 1) : ℕ) : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ 3)) ≤ h := by
  intro Cq hCq
  refine ⟨10 ^ 6 + 200 * Cq, ?_⟩
  intro Ch Cg hCg P lam T T' ka b d q0 hk hS hint hd hgd hq
  obtain ⟨hH, hI, hI', -, -, -, -, -, -, -, hbl, hbu, hbu', hga, hgap, ⟨bv, hbv, hsh⟩, -⟩ := hS
  have hk1 : 1 ≤ P.k := by omega
  have hCg6 : (10 : ℝ) ^ 6 ≤ Cg := by linarith
  rw [mul_assoc] at hgap
  set h0 : ℝ := Cg * (((2 * P.r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) * (((3 * (P.r + 1) : ℕ) : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ 3)) with hh0
  set ga : ℝ := max (Cg * ((2 * P.r + 2 : ℕ) : ℝ) ^ 3) (200 * d) with hgadef
  have hall : AllGaps lam ga := fun s s' hs => max_le (hga s s' hs) (hgd s s' hs)
  have hm3 : (1 : ℝ) ≤ ((2 * P.r + 2 : ℕ) : ℝ) ^ 3 :=
    one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * P.r + 2))
  have hq' : 100 * ((q0 : ℝ) + 1) ≤ ga := by
    have h1 : Cg * ((2 * P.r + 2 : ℕ) : ℝ) ^ 3 ≤ ga := le_max_left _ _
    have h2 : 200 * d ≤ ga := le_max_right _ _
    have h3 := mul_le_mul_of_nonneg_right hCg (le_trans zero_le_one hm3)
    nlinarith
  have hgap' : Formalism.QuantumDeterminants.GapAtLeast (PI.BesselPeriodGGP.eps48 P.k P.r) lam (max h0 ga) := by
    intro a c hac
    exact max_le (hgap a c hac) (hall a c (fun e => hac (by rw [e])))
  have hok : ThreeDimData.GapOK P.k P.r (max h0 ga / 4) := by
    apply gapOK_of _ _ hk1
    refine le_trans ?_ (le_max_left _ _)
    rw [hh0]
    apply mul_le_mul hCg6 _ (by positivity) (by linarith)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact le_add_of_nonneg_left (by positivity)
  have hcl : ∀ a c : Fin (2 * P.r + P.k + 1), a < c → c.val + 1 < P.k → ga ≤ lam a - lam c := by
    intro a c hac _
    have := hall a c hac.ne
    rwa [abs_of_pos (sub_pos.mpr (hH.1 hac))] at this
  have hbv' : 10 ^ 6 * ((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ 7 ≤ bv :=
    le_trans (mul_le_mul_of_nonneg_right hCg6 (by positivity)) hbv
  have hs1 : ∀ a : Fin (2 * P.r + P.k + 1), a.val + 1 < P.k → 0 ≤ lam a ∧ lam a ≤ bv / 8 :=
    fun a ha => (hsh a).1 (cloud_of hI a ha)
  have hs2 : ∀ a : Fin (2 * P.r + P.k + 1), P.k ≤ a.val + 1 → -2 * bv ≤ lam a ∧ lam a ≤ -bv :=
    fun a ha => (hsh a).2 (not_cloud_of hk1 hH.1 hI a ha)
  refine ⟨bv, ga, max h0 ga, ?_, ?_, le_max_left _ _⟩
  · exact ⟨hk1, hH, half_of hH (fun i hi => (hint i hi).1), lt_left hk1 hI, lt_right hI, hs1, hs2, hbl,
      bound_of hbu, hcl, hgap', hok, hq', le_trans hq' (le_max_right _ _), hbv'⟩
  · exact ⟨hk1, hH, half_of hH (fun i hi => (hint i hi).2), lt_left hk1 hI', lt_right hI', hs1, hs2, hbl,
      bound_of hbu', hcl, hgap', hok, hq', le_trans hq' (le_max_right _ _), hbv'⟩

end GlobalTheory.BpStdNum
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullLin

theorem stalkMap_injective_of_flat {X Y : Scheme.{0}} (f : X ⟶ Y) [Flat f] (x : X) :
    Function.Injective (f.stalkMap x).hom := by
  have h := Flat.stalkMap f x
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (f x)) (B := X.presheaf.stalk x)
  exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)

theorem sec_eq_zero_of_flat {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (f : Y' ⟶ Y) [Flat f] [Surjective f]
    (h : ∀ x J, Good L x J → sval s f x J = 0) (j : K → L.ι) : s.f j = 0 := by
  refine fn_ext fun y hy => ?_
  obtain ⟨x, rfl⟩ := f.surjective y
  apply stalkMap_injective_of_flat f x
  choose J hJ using fun ψ : Y' ⟶ X => exists_chart hL (ψ x)
  refine (gs_stalkMap f x _ hy _).symm.trans (Eq.trans ?_ (gs_stalkMap f x _ hy _))
  refine (sec_trans s f x hy (Good.mem hJ φ f)).trans ?_
  refine (congrArg _ (h x J hJ)).trans ((mul_zero _).trans ?_)
  rw [gs_eq f x _ hy, map_zero, map_zero]

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (maximalIdeal V)}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem aF_fst (oa : D.toPre.OAct O) (a : O) :
    (aF D F oa a).left ≫ (fst (TF (R := V) F) D.toPre.P.A).left = (fst (TF (R := V) F) D.toPre.P.A).left :=
  congrArg (fun q => q.left) (lift_fst (fst _ _) (DegPre.prB D.toPre F ≫ oa.onB.act a))

theorem aF_snd (oa : D.toPre.OAct O) (a : O) :
    (aF D F oa a).left ≫ (DegPre.prB D.toPre F).left = (DegPre.prB D.toPre F).left ≫ (oa.onB.act a).left :=
  congrArg (fun q => q.left) (lift_snd (fst _ _) (DegPre.prB D.toPre F ≫ oa.onB.act a))

theorem isPullback_aF (oa : D.toPre.OAct O) (a : O) :
    IsPullback (aF D F oa a).left (DegPre.prB D.toPre F).left (DegPre.prB D.toPre F).left (oa.onB.act a).left := by
  have h₀ : IsPullback (fst (TF (R := V) F) D.toPre.P.A).left (DegPre.prB D.toPre F).left
      (TF (R := V) F).hom D.toPre.P.A.hom := IsPullback.of_hasPullback _ _
  refine IsPullback.of_right ?_ (aF_snd oa a) h₀
  rw [aF_fst, Over.w]
  exact h₀

theorem aF_mul (oa : D.toPre.OAct O) (a b : O) : aF D F oa (a * b) = aF D F oa b ≫ aF D F oa a := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [aF]
  · simp [aF, DegPre.prB, oa.onB.map_mul]

theorem pullAl_val (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (χ : D.toPre.X)
    {u u' : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k N))} (hu : u.IsGen) (hu' : u'.IsGen)
    {K : Type} [Fintype K] {φ : K → ((TF (R := V) F).left ⟶ D.toPre.P.A.left)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb D.toPre.P.L φ ε)}
    (c : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left) t)
    (c' : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u' (DegPre.zF D.toPre F).left) t)
    (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J) (hJ : Good D.toPre.P.L z J) :
    val u r z J = val u' r z J := by
  have z₁ : DegPre.zF D.toPre F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  refine gen_unique' D.toPre.P.isLB (fun _ _ _ => rfl) (fst (TF (R := V) F) D.toPre.P.A).left
    (DegPre.zF D.toPre F).left (congrArg (fun q => q.left) z₁) (surj_appTop D.toPre F hG) hu hu'
    (fun y I hI => ?_) Z r z J hJ
  have a₁ := val_corr hI c (𝟙 _)
  have a₂ := val_corr hI c' (𝟙 _)
  rw [val_pull hI, Category.id_comp] at a₁ a₂
  exact a₁.trans a₂.symm

theorem pullAl_unique (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) {s : Fam D.toPre F k}
    {t t' : Fam D.toPre F (k * N)} (h : PullAl D F oa a k N s t) (h' : PullAl D F oa a k N s t') : t = t' := by
  refine fam_ext fun β j => ?_
  by_cases hβ : ∃ χ, β = star a • χ
  · obtain ⟨χ, rfl⟩ := hβ
    obtain ⟨u, hu, c, e⟩ := h.1 χ
    obtain ⟨u', hu', c', e'⟩ := h'.1 χ
    refine sec_ext_val D.toPre.P.isLB (fun y J hJ => ?_) j
    rw [(secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 e _ _ y J hJ,
      (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u').1 e' _ _ y J hJ,
      pullAl_val hG oa a k N χ hu hu' c c' _ _ y J hJ]
  · exact (h.2 β (fun χ e => hβ ⟨χ, e⟩) j).trans (h'.2 β (fun χ e => hβ ⟨χ, e⟩) j).symm

theorem pullAl_add (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) {s s' : Fam D.toPre F k}
    {t t' : Fam D.toPre F (k * N)} (h : PullAl D F oa a k N s t) (h' : PullAl D F oa a k N s' t') :
    PullAl D F oa a k N (s + s') (t + t') := by
  refine ⟨fun χ => ?_, fun β hβ j => ?_⟩
  · obtain ⟨u, hu, c, e⟩ := h.1 χ
    obtain ⟨u', hu', c', e'⟩ := h'.1 χ
    refine ⟨u, hu, c, (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_⟩
    rw [sval_add _ _ _ _ y hJ, sval_add _ _ _ _ y hJ,
      (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 e _ _ y J hJ,
      (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u').1 e' _ _ y J hJ,
      pullAl_val hG oa a k N χ hu' hu c' c _ _ y J hJ, add_mul]
  · rw [add_f, h.2 β hβ j, h'.2 β hβ j, add_zero]

theorem pullAl_smul (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (ζ : F) {s : Fam D.toPre F k}
    {t : Fam D.toPre F (k * N)} (h : PullAl D F oa a k N s t) : PullAl D F oa a k N (ζ • s) (ζ • t) := by
  refine ⟨fun χ => ?_, fun β hβ j => ?_⟩
  · obtain ⟨u, hu, c, e⟩ := h.1 χ
    refine ⟨u, hu, c, (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_⟩
    rw [sval_smul _ _ _ _ y hJ, sval_smul _ _ _ _ y hJ,
      (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 e _ _ y J hJ, Category.assoc, aF_fst, _root_.mul_assoc]
  · rw [smul_f, h.2 β hβ j, mul_zero]

theorem eq_zero_of_pullAl_zero (hM : MulNSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (hN : 1 ≤ N)
    (haa : a * star a = (N : O)) {s : Fam D.toPre F k} (h : PullAl D F oa a k N s 0) : s = 0 := by
  obtain ⟨-, hflat, hsurj, -⟩ := hM _ D.toPre.P N hN
  have hm : oa.onB.act (a * star a) = mulA D.toPre.P.A N := by
    rw [haa, ← _root_.mul_one (N : O), act_nsmul, oa.onB.map_one]
  rw [← hm] at hflat hsurj
  have hp := isPullback_aF (F := F) oa (a * star a)
  have : Flat (aF D F oa (a * star a)).left := MorphismProperty.of_isPullback hp.flip hflat
  have : Surjective (aF D F oa (a * star a)).left := MorphismProperty.of_isPullback hp.flip hsurj
  refine fam_ext fun χ j => sec_eq_zero_of_flat D.toPre.P.isLB (s.s χ) (aF D F oa (a * star a)).left
    (fun x J hJ => ?_) j
  obtain ⟨u, -, -, e⟩ := h.1 χ
  have e₁ := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 e _ (aF D F oa (star a)).left x J hJ
  have e₀ : sval ((0 : Fam D.toPre F (k * N)).s (star a • χ)) (aF D F oa (star a)).left x J = 0 :=
    gs_zero _ x _ (hJ.mem _ _)
  rw [e₀, ← Over.comp_left, ← aF_mul] at e₁
  exact (Units.mul_left_eq_zero _).1 e₁.symm

theorem exists_pull_linearMap : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (O : Type) [CommRing O]
    [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O), TraceFormTwistIso D.toPre oa w0 →
    ∀ (a : O) (N k : ℕ), 1 ≤ N → 1 ≤ k → a * star a = (N : O) →
    ∃ π : Fam D.toPre F k →ₗ[F] Fam D.toPre F (k * N), Function.Injective π ∧
      ∀ s s', PullAl D F oa a k N s s' ↔ s' = π s := by
  intro hL V _ _ _ D F _ _ O _ _ _ oa w0 hw a N k hN _ haa
  have hG := hL.globalFns
  obtain ⟨uΨ, huΨ, -⟩ := id hw
  choose P hP using fun s : Fam D.toPre F k => exists_pullAl D F D.toPre.P.isLB oa w0 uΨ huΨ a N haa hN k s
    (pullSecs_fe' D F hG D.toPre.P.isLB oa w0 hw uΨ huΨ a N haa hN k s)
  let π : Fam D.toPre F k →ₗ[F] Fam D.toPre F (k * N) :=
    { toFun := P
      map_add' := fun s s' => pullAl_unique hG oa a k N (hP _) (pullAl_add hG oa a k N (hP s) (hP s'))
      map_smul' := fun ζ s => pullAl_unique hG oa a k N (hP _) (pullAl_smul oa a k N ζ (hP s)) }
  refine ⟨π, (injective_iff_map_eq_zero π).2 fun s hs => ?_, fun s s' =>
    ⟨fun h => pullAl_unique hG oa a k N h (hP s), fun h => h ▸ hP s⟩⟩
  exact eq_zero_of_pullAl_zero hL.mulN oa a k N hN haa (hs ▸ hP s)

end GlobalTheory.PullLin
end
end
