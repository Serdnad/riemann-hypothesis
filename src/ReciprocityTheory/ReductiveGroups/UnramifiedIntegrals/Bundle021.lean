module

public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle002
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ExistsFinitePartOneIdeleSplitCongruenceQuotient
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle018
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.IsTransSys
public import Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsNoPrimeToPTorsion
import Formalism.EllipticTorsion.EllipticTorsionProofs.Bundle004
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.NonsingularNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle008
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle019
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
import ReciprocityTheory.NeutralLocalFields.Bundle001
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle016

@[expose] public section

section

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

theorem redOmegaK_quad (d m : ℕ) (hm : d + 1 = 4 * m) : omegaK d ^ 2 - omegaK d + (m : ℂ) = 0 := by
  have hs : (((Real.sqrt d : ℝ) : ℂ)) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    simp
  have hm' : (d : ℂ) + 1 = 4 * (m : ℂ) := by exact_mod_cast hm
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  unfold omegaK
  have : ((1 + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2) ^ 2 - (1 + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2
      + (m : ℂ) = (Complex.I ^ 2 * (((Real.sqrt d : ℝ) : ℂ)) ^ 2 - 1 + 4 * (m : ℂ)) / 4 := by ring
  rw [this, hI, hs, ← hm']
  ring

theorem omega_mem_kur (d : ℕ) (hsq : Squarefree d) (hd4 : d % 4 = 3) (l : ℕ) [Fact l.Prime] (hld : ¬ l ∣ d)
    (ι : ℂ ≃+* ℂ_[l]) : ι (omegaK d) ∈ MaximalUnramifiedExtension l := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, d + 1 = 4 * m := ⟨(d + 1) / 4, by omega⟩
  set w : ℂ_[l] := ι (omegaK d) with hw
  have hq : w ^ 2 - w + (m : ℂ_[l]) = 0 := by
    have := congrArg ι (redOmegaK_quad d m hm)
    simpa using this
  have hm1 : ‖(m : ℂ_[l])‖ ≤ 1 := by
    rw [norm_natCast_Cl]
    exact Padic.norm_int_le_one (m : ℤ)
  have hd1 : ‖(d : ℂ_[l])‖ = 1 := norm_natCast_Cl_of_not_dvd l hld
  have hw1 : ‖w‖ ≤ 1 := by
    by_contra hgt
    rw [not_le] at hgt
    have h1 : ‖w - 1‖ = ‖w‖ := by
      have hne : ‖w‖ ≠ ‖(-1 : ℂ_[l])‖ := by rw [norm_neg, norm_one]; exact hgt.ne'
      rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_neg, norm_one]
      exact max_eq_left hgt.le
    have h2 : w * (w - 1) = -(m : ℂ_[l]) := by linear_combination hq
    have h3 : ‖w‖ * ‖w‖ ≤ 1 := by
      have := congrArg norm h2
      rw [norm_mul, h1, norm_neg] at this
      rw [this]; exact hm1
    nlinarith
  have hder : ‖2 * w - 1‖ = 1 := by
    have h2 : (2 * w - 1) ^ 2 = -(d : ℂ_[l]) := by
      have hm' : (d : ℂ_[l]) + 1 = 4 * (m : ℂ_[l]) := by exact_mod_cast hm
      linear_combination 4 * hq + hm'
    have h3 : ‖2 * w - 1‖ ^ 2 = 1 := by rw [← norm_pow, h2, norm_neg, hd1]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp h3
  have hco : ∀ i, (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℂ_[l]) : Polynomial ℂ_[l]).coeff i =
      (if i = 2 then 1 else 0) - (if 1 = i then 1 else 0) + (if i = 0 then (m : ℂ_[l]) else 0) := fun i => by
    rw [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C,
      Polynomial.coeff_X]
  refine hensel_mem l (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℂ_[l])) ?_ ?_ w hw1 ?_ ?_
  · intro i
    rw [hco]
    refine (MaximalUnramifiedExtension l).add_mem ((MaximalUnramifiedExtension l).sub_mem ?_ ?_) ?_
    · split_ifs
      · exact (MaximalUnramifiedExtension l).one_mem
      · exact (MaximalUnramifiedExtension l).zero_mem
    · split_ifs
      · exact (MaximalUnramifiedExtension l).one_mem
      · exact (MaximalUnramifiedExtension l).zero_mem
    · split_ifs
      · exact natCast_mem (MaximalUnramifiedExtension l) m
      · exact (MaximalUnramifiedExtension l).zero_mem
  · intro i
    rw [hco]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ((norm_sub_le_max_Cl l _ _).trans (max_le ?_ ?_)) ?_)
    · split_ifs <;> simp
    · split_ifs <;> simp
    · split_ifs
      · exact hm1
      · simp
  · simpa using hq
  · have hd : (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℂ_[l]) : Polynomial ℂ_[l]).derivative.eval w
        = 2 * w - 1 := by
      simp
      left; norm_num
    rw [hd, hder]

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem padic_mem_Kur {l : ℕ} [Fact l.Prime] (a : ℚ_[l]) : algebraMap ℚ_[l] ℂ_[l] a ∈ MaximalUnramifiedExtension l := by
  have hcont : Continuous (algebraMap ℚ_[l] ℂ_[l]) := continuous_algebraMap ℚ_[l] ℂ_[l]
  have hclosed : IsClosed ((MaximalUnramifiedExtension l : Set ℂ_[l])) := Subfield.isClosed_topologicalClosure _
  have hpre : IsClosed ((algebraMap ℚ_[l] ℂ_[l]) ⁻¹' (MaximalUnramifiedExtension l : Set ℂ_[l])) := hclosed.preimage hcont
  have hall : Set.range ((↑) : ℚ → ℚ_[l]) ⊆ (algebraMap ℚ_[l] ℂ_[l]) ⁻¹' (MaximalUnramifiedExtension l : Set ℂ_[l]) := by
    rintro _ ⟨q, rfl⟩
    show algebraMap ℚ_[l] ℂ_[l] (q : ℚ_[l]) ∈ MaximalUnramifiedExtension l
    rw [map_ratCast]
    exact SubfieldClass.ratCast_mem (MaximalUnramifiedExtension l) q
  have hmem : a ∈ closure (Set.range ((↑) : ℚ → ℚ_[l])) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨r, hr⟩ := Padic.rat_dense (p := l) a hε
    exact ⟨r, ⟨r, rfl⟩, by rw [dist_eq_norm]; exact hr⟩
  exact hpre.closure_subset_iff.mpr hall hmem

theorem sqrt_mem_Kur {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) {d : ℕ} (hld : ¬ l ∣ d) {s : ℂ_[l]}
    (hs : s ^ 2 = -(d : ℂ_[l])) : s ∈ MaximalUnramifiedExtension l := by
  have hd : ‖(d : ℂ_[l])‖ = 1 := norm_natCast_Cl_of_not_dvd (l := l) hld
  have hc : -(d : ℂ_[l]) ∈ MaximalUnramifiedExtension l := by
    first
    | exact neg_mem (natCast_mem (MaximalUnramifiedExtension l) d)
    | exact neg_mem (by simpa using SubfieldClass.ratCast_mem (MaximalUnramifiedExtension l) (d : ℚ))
  have h2 : ‖s‖ ^ 2 = 1 := by rw [← norm_pow, hs, norm_neg, hd]
  have hy : ‖s‖ = 1 := by
    have h0 := norm_nonneg s
    nlinarith [h2, h0]
  exact sqrt_mem (l := l) hl (-(d : ℂ_[l])) s hc hy hs

def kurAlg (l : ℕ) [Fact l.Prime] : IntermediateField ℚ_[l] (PadicAlgCl l) :=
  ((MaximalUnramifiedExtension l).comap (algebraMap (PadicAlgCl l) ℂ_[l])).toIntermediateField fun a => by
    show algebraMap (PadicAlgCl l) ℂ_[l] (algebraMap ℚ_[l] (PadicAlgCl l) a) ∈ MaximalUnramifiedExtension l
    rw [← IsScalarTower.algebraMap_apply]
    exact padic_mem_Kur a

theorem mem_kurAlg {l : ℕ} [Fact l.Prime] {y : PadicAlgCl l} :
    y ∈ kurAlg l ↔ algebraMap (PadicAlgCl l) ℂ_[l] y ∈ MaximalUnramifiedExtension l := Iff.rfl

theorem kur_le {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) {d : ℕ} (hld : ¬ l ∣ d) {s : PadicAlgCl l}
    (hs : s ^ 2 = -(d : PadicAlgCl l)) {y : PadicAlgCl l}
    (hy : y ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.MaximalUnramifiedExtension l (IntermediateField.adjoin ℚ_[l] {s})) :
    algebraMap (PadicAlgCl l) ℂ_[l] y ∈ MaximalUnramifiedExtension l := by
  have hK : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] {s}) := by
    first
    | exact IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral s)
    | exact IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic s).isIntegral

  have hq2 : 2 ≤ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) := by
    by_contra hlt
    push_neg at hlt
    have h1 : ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ 1 - 1 = 0 := by rw [pow_one]; omega
    have h2 : ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ 2 - 1 = 0 := by
      have : ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ 2 ≤ 1 := by
        calc ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left (by omega) 2
          _ = 1 := one_pow 2
      omega
    have e : ReciprocityTheory.DiscreteGroups.LocalClassField.Kn l (IntermediateField.adjoin ℚ_[l] {s}) 1 = ReciprocityTheory.DiscreteGroups.LocalClassField.Kn l (IntermediateField.adjoin ℚ_[l] {s}) 2 := by simp only [ReciprocityTheory.DiscreteGroups.LocalClassField.Kn, h1, h2]
    have d1 := ReciprocityTheory.DiscreteGroups.LocalClassField.degLK_Kn (p := l) (K := (IntermediateField.adjoin ℚ_[l] {s})) hK (n := 1) one_pos
    have d2 := ReciprocityTheory.DiscreteGroups.LocalClassField.degLK_Kn (p := l) (K := (IntermediateField.adjoin ℚ_[l] {s})) hK (n := 2) two_pos
    rw [e, d2] at d1
    omega

  have hlq : l ∣ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) := by
    by_contra h
    obtain ⟨n, hn, hdvd⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_dvd_qK_pow_sub_one (p := l) (K := (IntermediateField.adjoin ℚ_[l] {s})) hK h
    have h1 : ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ∣ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ n := dvd_pow_self _ hn.ne'
    have hpos : 1 ≤ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ n := Nat.one_le_pow _ _ (by omega)
    have h3 : ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ∣ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ n - (ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ n - 1) := by
      first
      | exact Nat.dvd_sub h1 hdvd
      | exact Nat.dvd_sub (by omega) h1 hdvd
    rw [Nat.sub_sub_self hpos] at h3
    have := Nat.le_of_dvd one_pos h3
    omega
  have hnd : ∀ k, 0 < k → ¬ l ∣ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ k - 1 := by
    intro k hk h
    have h1 : l ∣ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ k := hlq.trans (dvd_pow_self _ hk.ne')
    have hpos : 1 ≤ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ k := Nat.one_le_pow _ _ (by omega)
    have h3 : l ∣ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ k - (ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ k - 1) := by
      first
      | exact Nat.dvd_sub h1 h
      | exact Nat.dvd_sub (by omega) h1 h
    rw [Nat.sub_sub_self hpos] at h3
    exact (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h3)

  have hle : ReciprocityTheory.DiscreteGroups.LocalClassField.MaximalUnramifiedExtension l (IntermediateField.adjoin ℚ_[l] {s}) ≤ kurAlg l := by
    refine iSup_le fun n => sup_le ?_ ?_
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [SetLike.mem_coe, mem_kurAlg]
      refine sqrt_mem_Kur hl hld ?_
      rw [← map_pow, hs, map_neg, map_natCast]
    · rw [IntermediateField.adjoin_le_iff]
      intro ζ hζ
      have hζ0 : ζ ^ (ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ (n + 1) - 1) = 1 := hζ
      rw [SetLike.mem_coe, mem_kurAlg]
      have hζ' : (algebraMap (PadicAlgCl l) ℂ_[l] ζ) ^ (ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ (n + 1) - 1) = 1 := by
        rw [← map_pow, hζ0, map_one]
      have hN : 0 < ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ (n + 1) - 1 := by
        have : 2 ≤ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ (n + 1) := le_trans hq2 (Nat.le_self_pow (by omega) _)
        omega
      exact Subfield.le_topologicalClosure _
        (Subfield.subset_closure ⟨_, hN, hnd (n + 1) (Nat.succ_pos n), hζ'⟩)
  exact mem_kurAlg.1 (hle hy)

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

theorem velu_pair (L : PeriodPair) (z P : ℂ) (hz : z ∉ L.lattice) (hP : P ∉ L.lattice)
    (hp : z + P ∉ L.lattice) (hm : z - P ∉ L.lattice) :
    (L.weierstrassP (z + P) - L.weierstrassP P) + (L.weierstrassP (z + -P) - L.weierstrassP (-P))
      = fW L.g₂ L.g₃ (L.weierstrassP P) / (L.weierstrassP z - L.weierstrassP P) ^ 2
        + fW' L.g₂ (L.weierstrassP P) / (2 * (L.weierstrassP z - L.weierstrassP P)) := by
  have hne := Formalism.L2.Th1.E.AddThm.P_sub_ne L z P hz hP hp hm
  have hP' : -P ∉ L.lattice := fun h => hP (by simpa using L.lattice.neg_mem h)
  have h1 := Formalism.L2.Th1.E.AddThm.P_add L z P hz hP hp hm
  have h2 := Formalism.L2.Th1.E.AddThm.P_add L z (-P) hz hP' (by simpa [sub_eq_add_neg] using hm)
    (by simpa using hp)
  rw [L.weierstrassP_neg, L.derivWeierstrassP_neg] at h2
  have hY := L.derivWeierstrassP_sq z hz
  have hy := L.derivWeierstrassP_sq P hP
  rw [L.weierstrassP_neg, h1, h2]
  unfold fW fW'
  generalize L.weierstrassP z = X at *
  generalize L.weierstrassP P = x at *
  generalize L.derivWeierstrassP z = Y at *
  generalize L.derivWeierstrassP P = y at *
  field_simp
  linear_combination 4 * hY + 4 * hy

theorem velu_fun (L : PeriodPair) (α : ℂ) (T : Finset ℂ) (hα : α ≠ 0) (hs : MulStable L α)
    (hT : IsHalfReps L α T) (z : ℂ) (hz : α * z ∉ L.lattice) :
    α ^ 2 * L.weierstrassP (α * z) = veluFun L.g₂ L.g₃ (xsOf L T) (L.weierstrassP z) := by
  obtain ⟨hK, hdisj⟩ := hT.kerReps
  have hzL : z ∉ L.lattice := fun h => hz (hs z h)
  rw [isogenyP L α _ hα hs hK z hz, Finset.sum_union hdisj,
    Finset.sum_image (by intro a _ b _ h; exact neg_injective h)]
  simp only [veluFun, xsOf]
  rw [Finset.sum_image (by intro a ha b hb h; exact hT.injOn ha hb h)]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun P hP => ?_
  obtain ⟨hαP, h2P⟩ := hT.1 P hP

  have hPL : P ∉ L.lattice := fun h => h2P (by rw [two_mul]; exact L.lattice.add_mem h h)

  have hp : z + P ∉ L.lattice := fun h => hz (by
    have := L.lattice.sub_mem (hs _ h) hαP
    rwa [mul_add, add_sub_cancel_right] at this)
  have hm : z - P ∉ L.lattice := fun h => hz (by
    have := L.lattice.add_mem (hs _ h) hαP
    rwa [mul_sub, sub_add_cancel] at this)
  exact velu_pair L z P hzL hPL hp hm

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

variable {l : ℕ} [Fact l.Prime] {g2 g3 : ℂ_[l]}

theorem good_norm_two (h : GoodPair l g2 g3) : ‖(2 : ℂ_[l])‖ = 1 := by
  have hl : ¬ (l ∣ 2) := by
    intro hd
    have h1 := Nat.le_of_dvd (by norm_num) hd
    have h2 := h.five
    omega
  have hQ : ‖(2 : ℚ_[l])‖ = 1 := by
    have e2 := Padic.eq_padicNorm (p := l) (2 : ℚ)
    push_cast at e2
    rw [e2]
    exact_mod_cast (padicNorm.nat_eq_one_iff 2).mpr hl
  have e : (2 : ℂ_[l]) = (((2 : ℚ_[l]) : PadicAlgCl l) : ℂ_[l]) := by
    rw [map_ofNat]
    first
    | exact (map_ofNat (UniformSpace.Completion.coeRingHom (α := PadicAlgCl l)) 2).symm
    | exact (UniformSpace.Completion.coe_ofNat 2).symm
    | exact (map_ofNat (algebraMap (PadicAlgCl l) ℂ_[l]) 2).symm
  rw [e, PadicComplex.norm_extends, PadicAlgCl.norm_extends, hQ]

theorem good_norm_four (h : GoodPair l g2 g3) : ‖(4 : ℂ_[l])‖ = 1 := by
  rw [show (4 : ℂ_[l]) = 2 * 2 by norm_num, norm_mul, good_norm_two h, mul_one]

theorem good_model (h : GoodPair l g2 g3) : IntegralModel (shortW g2 g3) ∧ ‖(shortW g2 g3).Δ‖ = 1 := by
  have h4 := good_norm_four h
  refine ⟨?_, ?_⟩
  · unfold IntegralModel shortW
    simp only [norm_zero, zero_le_one, norm_neg, norm_div, h4, div_one, true_and, h.norm2, h.norm3,
      and_self]
  · have hΔ : (shortW g2 g3).Δ = g2 ^ 3 - 27 * g3 ^ 2 := by
      simp only [shortW, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring
    rw [hΔ, h.disc]

theorem good_int (h : GoodPair l g2 g3) : IntCurve (shortW g2 g3) := by
  have h4 := good_norm_four h
  have hΔ := (good_model h).2
  unfold IntCurve
  simp only [shortW] at hΔ ⊢
  simp only [norm_zero, zero_le_one, norm_neg, norm_div, h4, div_one, true_and, h.norm2,
    h.norm3, and_self, hΔ]

theorem good_coeff (h : GoodPair l g2 g3) : CoeffSub (MaximalUnramifiedExtension l) (shortW g2 g3) := by
  have h4 : (4 : ℂ_[l]) ∈ MaximalUnramifiedExtension l := by
    first
    | exact ofNat_mem (MaximalUnramifiedExtension l) 4
    | (have h4' := natCast_mem (MaximalUnramifiedExtension l) 4
       exact_mod_cast h4')
  unfold CoeffSub shortW
  exact ⟨zero_mem _, zero_mem _, zero_mem _, div_mem (neg_mem h.mem2) h4,
    div_mem (neg_mem h.mem3) h4⟩

theorem integral_of_not_mem_formalGroup (h : GoodPair l g2 g3) (P : (shortW g2 g3).toAffine.Point) (hP : ¬ InFormalGroupPoints P) :
    P ≠ 0 ∧ ‖px _ P‖ ≤ 1 ∧ ‖py _ P‖ ≤ 1 := by
  unfold InFormalGroupPoints at hP
  cases P with
  | zero => exact absurd trivial hP
  | some x y hxy =>
    have hx : ‖x‖ ≤ 1 := not_lt.mp hP
    have h4 := good_norm_four h
    have heq := (WeierstrassCurve.Affine.equation_iff x y).mp hxy.1
    simp only [shortW, zero_mul, mul_zero, add_zero] at heq
    have hb1 : ‖x ^ 3‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hx
    have hb2 : ‖-g2 / 4 * x‖ ≤ 1 := by
      rw [norm_mul, norm_div, norm_neg, h4, div_one]
      exact mul_le_one₀ h.norm2 (norm_nonneg _) hx
    have hb3 : ‖-g3 / 4‖ ≤ 1 := by
      rw [norm_div, norm_neg, h4, div_one]
      exact h.norm3
    have hsum : ‖x ^ 3 + -g2 / 4 * x + -g3 / 4‖ ≤ 1 :=
      (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hb1 hb2)) hb3)
    have hy2 : ‖y‖ ^ 2 ≤ 1 := by
      rw [← norm_pow, heq]
      exact hsum
    refine ⟨by rintro (_ | _), ?_, ?_⟩
    · exact hx
    · show ‖y‖ ≤ 1
      nlinarith [norm_nonneg y]

theorem torsion_not_mem_formalGroup (h : GoodPair l g2 g3) (P : (shortW g2 g3).toAffine.Point) (N : ℕ) (hN : ¬ l ∣ N)
    (hNP : N • P = 0) (hP0 : P ≠ 0) : ¬ InFormalGroupPoints P := fun hE => by
  have hn := norm_natCast_Cl_of_not_dvd (l := l) hN
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero (by rintro rfl; simp at hn)
  have hmul := (FormalGroupPointsTorsion.mulz (good_model h).1 P hE hP0 m).2
  rw [hNP, Affine.Point.zero_def] at hmul
  simp only [FormalGroupPointsTorsion.zf, zero_sub, norm_neg, norm_mul, hn, one_mul] at hmul
  exact lt_irrefl _ hmul

theorem not_mem_formalGroup_sub (h : GoodPair l g2 g3) (P D : (shortW g2 g3).toAffine.Point) (hP : ¬ InFormalGroupPoints P)
    (hD : InFormalGroupPoints D) : ¬ InFormalGroupPoints (P - D) := fun hE => by
  have hadd : InFormalGroupPoints (P - D + D) := by
    generalize P - D = E at hE ⊢
    cases E with
    | zero =>
      change InFormalGroupPoints (0 + D)
      rwa [zero_add]
    | some x₁ y₁ h₁ =>
      cases D with
      | zero =>
        change InFormalGroupPoints (Affine.Point.some x₁ y₁ h₁ + 0)
        rwa [add_zero]
      | some x₂ y₂ h₂ =>
        by_cases hxy : x₁ = x₂ ∧ y₁ = (shortW g2 g3).toAffine.negY x₂ y₂
        · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2]
          trivial
        · rw [Affine.Point.add_some hxy]
          exact FormalGroupPointsSubgroup.addX_norm _ (good_model h).1 h₁.1 h₂.1 hxy hE hD
  exact hP (by simpa only [sub_add_cancel] using hadd)

theorem tor_y_unit (h : GoodPair l g2 g3) (P : (shortW g2 g3).toAffine.Point) (N : ℕ) (hN : ¬ l ∣ N)
    (hNP : N • P = 0) (h2 : P + P ≠ 0) : ‖py _ P‖ = 1 := by
  have hP0 : P ≠ 0 := fun h0 => h2 (by rw [h0, add_zero])
  obtain ⟨-, hx, hy⟩ := integral_of_not_mem_formalGroup h P (torsion_not_mem_formalGroup h P N hN hNP hP0)
  have hN2 : N • (P + P) = 0 := by rw [smul_add, hNP, add_zero]
  obtain ⟨-, hx2, -⟩ := integral_of_not_mem_formalGroup h (P + P) (torsion_not_mem_formalGroup h (P + P) N hN hN2 h2)
  have hu := Formalism.L2.Th1.E.UnitPsi2_of Formalism.L2.Th1.E.nonsingular_norm ℂ_[l] _ (good_int h) P hP0 h2 hx hy hx2
  have he : Formalism.L2.Th1.E.psi2 (shortW g2 g3) P = 2 * py _ P := by
    simp [Formalism.L2.Th1.E.psi2, shortW]
  rw [he, norm_mul, good_norm_two h, one_mul] at hu
  exact hu

end ReciprocityTheory.ChartRestriction.L1
end
end
