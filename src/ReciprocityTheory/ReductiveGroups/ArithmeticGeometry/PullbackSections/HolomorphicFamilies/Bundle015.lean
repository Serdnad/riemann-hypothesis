module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle006
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

set_option autoImplicit false


noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

theorem secScal_cast {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {Y : Scheme.{0}} (h : Y ⟶ G.left)
    (k : ℕ) {L1 L2 : RigLB G} (e : L1 = L2)
    (s1 : LB.Sec (LB.LinComb L1.L (K := Fin 1) (fun _ => h) (fun _ => (k : ℤ))))
    (σ1 : LB.Sec (LB.LinComb L1.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (hs : GeneratorPullback.SecScal L1.L (fun _ : Fin 1 => h) (fun _ => (k : ℤ)) s1 (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ1 h 1) :
    GeneratorPullback.SecScal L2.L (fun _ : Fin 1 => h) (fun _ => (k : ℤ)) (e ▸ s1) (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ))
      (e ▸ σ1) h 1 := by
  subst e; exact hs

theorem nuReg : NuRegSt := by
  intro E _ _ _ H V _ _ _ _ _ t P _ ϖ hϖ Q hQ vK hvK tK m w _ k hk F hF
  obtain ⟨s, Ex, htie, hexp, hnu⟩ := hF
  haveI := t.semi.smooth
  haveI := t.semi.separated
  haveI := t.semi.quasiCompact
  obtain ⟨σ', hσ'⟩ := nuExt V ϖ hϖ P.D Q hQ vK hvK P.A t.G P.U k hk s Ex hexp hnu
  have hsc := secScal_cast (pullback.fst t.G.hom (Out.jK V)) k P.bundle s σ' hσ'
  refine ⟨P.bundle ▸ σ', fun Z r zp hzp z J J' hJ hJ' => ?_⟩
  have e1 := ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.secScal_sval hsc (r ≫ iotaK m) z hJ
  rw [Category.assoc, iotaK, pullback.lift_fst] at e1
  exact e1.trans (htie Z r zp hzp z J J' hJ hJ')

theorem zCast_trans {S : Scheme.{0}} (A : Over S) {L : LB A.left} {T : Over S} {k₁ k₂ k₃ : ℤ} (h : k₁ = k₂) (h' : k₂ = k₃)
    (F : LB.Sec (LPow A L k₁ T)) : zCast A h' (zCast A h F) = zCast A (h.trans h') F := by
  subst h; subst h'; rfl

theorem zCast_self {S : Scheme.{0}} (A : Over S) {L : LB A.left} {T : Over S} {k : ℤ} (h : k = k)
    (F : LB.Sec (LPow A L k T)) : zCast A h F = F := rfl

theorem regUnif_of (hN : NuDataSt) (hT : ThetaNuSt) (hM : MulNuSt) (hF : FinNuSt) : RegUnifSt := by
  intro E _ _ _ H V _ _ _ _ _ t P hTor θ _ M hMu tK m w hrig θK hθK t₀ F hVt
  obtain ⟨ϖ, Q, vK, hϖ, hQ, hvK⟩ := hN E H V t P
  obtain ⟨t', α₀, α, s₁, U, hok1, hok2, hα₀, hnorm, hαc, htw, hsym, hact⟩ := hVt
  have hM1 : 1 ≤ M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; simp at hMu
    · exact h
  have n0 := hT E H V t P hTor ϖ hϖ Q hQ vK hvK tK m w hrig θ θK hθK
  have n0' : NuK P Q vK m w 1 (zCast tK.G Nat.cast_one.symm (zCast tK.G Nat.cast_one θK)) := by
    rw [zCast_trans, zCast_self]; exact n0
  have n1 := hM E H V t P hTor ϖ hϖ Q hQ vK hvK tK m w hrig M hM1 (zCast tK.G Nat.cast_one θK) α₀ α s₁ n0'
    hα₀ hnorm hαc htw
  have hk : 0 < M ^ 2 := pow_pos hM1 2
  have n2 := hF E H V t P hTor ϖ hϖ Q hQ vK hvK tK m w hrig ((M : ℤ) ^ 2) (M ^ 2) (natCast_sq M) hk s₁ F t' U n1
    (by first | exact hok1 | exact hok2) hsym hact
  exact nuReg E H V t P hTor ϖ hϖ Q hQ vK hvK tK m w hrig (M ^ 2) hk (zCast tK.G (natCast_sq M) F) n2

theorem nuData : NuDataSt := by
  intro E _ _ _ H V _ _ _ _ _ t P
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  choose Q hQ using fun χ => QForm.exists_QVal hϖ P.D χ
  exact ⟨ϖ, Q, TG.vK hϖ, hϖ, hQ, TG.valOver_vK hϖ⟩

theorem regUnif_of' (hT : ThetaNuSt) (hM : MulNuSt) (hF : FinNuSt) : RegUnifSt := regUnif_of nuData hT hM hF

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Jv

variable (T : CDVR) (e : ℕ)

theorem nval_alg_nonneg (r : T.V) : (0 : EReal) ≤ nval T.V e (algebraMap T.V T.Fr r) := by
  by_cases hr : algebraMap T.V T.Fr r = 0
  · rw [hr, nval_zero]
    exact le_top
  · rw [nval_of_ne hr]
    have hv0 : 0 ≤ vV T.V (algebraMap T.V T.Fr r) := by
      unfold Formalism.L2.Pj.vV Formalism.L2.Pj.valV
      have hle := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := T.Fr)
        (IsDiscreteValuationRing.maximalIdeal T.V) r
      have hne : (IsDedekindDomain.HeightOneSpectrum.valuation T.Fr (IsDiscreteValuationRing.maximalIdeal T.V))
          (algebraMap T.V T.Fr r) ≠ 0 := (Valuation.ne_zero_iff _).mpr hr
      have hlog := (WithZero.log_le_log hne one_ne_zero).mpr hle
      rw [WithZero.log_one] at hlog
      linarith
    have hv : (0 : ℝ) ≤ (vV T.V (algebraMap T.V T.Fr r) : ℝ) := by exact_mod_cast hv0
    exact EReal.coe_nonneg.mpr (div_nonneg hv (Nat.cast_nonneg e))

def Jv (c : ℝ) : Submodule T.V T.Fr where
  carrier := {x | (((-c : ℝ)) : EReal) ≤ nval T.V e x}
  add_mem' := fun {a b} ha hb => le_trans (le_min ha hb) (nval_add e a b)
  zero_mem' := by
    show _ ≤ nval T.V e 0
    rw [nval_zero]
    exact le_top
  smul_mem' := fun r x hx => by
    show _ ≤ nval T.V e (r • x)
    rw [Algebra.smul_def, nval_mul]
    exact hx.trans (le_add_of_nonneg_left (nval_alg_nonneg T e r))

theorem one_mem_Jv {c : ℝ} (hc : 0 ≤ c) : (1 : T.Fr) ∈ Jv T e c := by
  show ((-c : ℝ) : EReal) ≤ nval T.V e 1
  have h1 := Formalism.L2.Pj.vV_mul (V := T.V) (K' := T.Fr) (x := 1) (y := 1) one_ne_zero one_ne_zero
  rw [mul_one] at h1
  have h0 : vV T.V (1 : T.Fr) = 0 := by omega
  rw [nval_of_ne one_ne_zero, h0]
  simp only [Int.cast_zero, zero_div]
  exact_mod_cast neg_nonpos.mpr hc

theorem mem_Jv_pow {c : ℝ} (_hc : 0 ≤ c) : ∀ (m : ℕ) (x : T.Fr), x ∈ Jv T e c ^ m →
    (((-((m : ℝ) * c)) : ℝ) : EReal) ≤ nval T.V e x := by
  intro m
  induction m with
  | zero =>
    intro x hx
    rw [pow_zero] at hx
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hx
    simp only [Nat.cast_zero, zero_mul, neg_zero, EReal.coe_zero]
    exact nval_alg_nonneg T e r
  | succ m ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun y z hy hz => ?_)
    · rw [nval_mul]
      have h1 := ih a ha
      have h2 : ((-c : ℝ) : EReal) ≤ nval T.V e b := hb
      calc (((-(((m + 1 : ℕ) : ℝ) * c)) : ℝ) : EReal)
          = (((-((m : ℝ) * c)) : ℝ) : EReal) + ((-c : ℝ) : EReal) := by
            rw [← EReal.coe_add]
            congr 1
            push_cast
            ring
        _ ≤ _ := add_le_add h1 h2
    · exact le_trans (le_min hy hz) (nval_add e y z)

end Jv

theorem two_pairMin_le {ι π : Type} [Fintype ι] [Fintype π] [DecidableEq π] (c : ι → π) (s : ι → Bool)
    (x : ι →₀ ℕ) : 2 * pairMin c s x ≤ ∑ l, x l := by
  unfold pairMin
  rw [Finset.mul_sum]
  calc ∑ q : π, 2 * min (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = true), x l)
        (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = false), x l)
      ≤ ∑ q : π, ((∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = true), x l) +
        (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = false), x l)) := by
        refine Finset.sum_le_sum (fun q _ => ?_)
        have h1 := min_le_left (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = true), x l)
          (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = false), x l)
        have h2 := min_le_right (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = true), x l)
          (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = false), x l)
        omega
    _ = ∑ l, x l := by
        simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [Finset.sum_eq_single (c l)]
        · cases s l <;> simp
        · intro b _ hb
          have hb' : c l ≠ b := fun h => hb h.symm
          simp [hb']
        · intro h
          exact absurd (Finset.mem_univ _) h

theorem sum_pairMin_le {T : Type} [Fintype T] (rr : T → ℕ) (n : ℕ) {π : Type} [Fintype π] [DecidableEq π]
    (c : T → π) (s : T → Bool) (a : T → ℕ → ℕ) (mo : Formalism.L2.Pj.Letter T rr n →₀ ℕ)
    (hrow : ∀ (σ : T) (i : Fin (rr σ)), ∑ b : Fin n, mo ⟨σ, i, b⟩ = a σ i) :
    ∑ b, pairMin (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1) (colL rr n mo b) ≤
      (∑ σ, ∑ i : Fin (rr σ), a σ i) / 2 := by
  have h2 : 2 * ∑ b, pairMin (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1) (colL rr n mo b) ≤
      ∑ σ, ∑ i : Fin (rr σ), a σ i := by
    rw [Finset.mul_sum]
    calc _ ≤ ∑ b : Fin n, ∑ ℓ : (Σ τ : T, Fin (rr τ)), colL rr n mo b ℓ :=
          Finset.sum_le_sum (fun b _ => two_pairMin_le _ _ _)
      _ = ∑ ℓ : (Σ τ : T, Fin (rr τ)), ∑ b : Fin n, mo ⟨ℓ.1, ℓ.2, b⟩ := by
          rw [Finset.sum_comm]
          rfl
      _ = ∑ σ, ∑ i : Fin (rr σ), a σ i := by
          rw [Fintype.sum_sigma]
          exact Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun i _ => hrow σ i))
  omega

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
end
end
