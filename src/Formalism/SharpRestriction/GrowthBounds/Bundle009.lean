module

public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.Bundle005
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.Bundle001
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.LiePolarizationDerEqZeroOfDisjoint
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.Bundle007
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.Bundle008
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissibleExternalProduct
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.Bundle006
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.SplittingThirdPartHolds
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.Bundle004
public import Formalism.SharpRestriction.GrowthBounds.Bundle005
public import Formalism.LocalToGlobal.CharacterGerms.Bundle019
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePStartSelf
import Formalism.LocalToGlobal.CharacterGerms.Bundle011
public import Formalism.LocalToGlobal.CharacterGerms.Bundle028
import Formalism.LocalToGlobal.CharacterGerms.RowTiePLSmallMain
public import Formalism.LocalToGlobal.CharacterGerms.Bundle039
public import Formalism.LocalToGlobal.CharacterGerms.Bundle008
public import Formalism.SharpRestriction.GrowthBounds.Bundle006
public import Formalism.SharpRestriction.GrowthBounds.AlongCvSmul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

namespace Formalism.MainNotions.G.ColumnFamilies.Top

open Formalism.MainNotions.CovariantDegrees

theorem b9 (D : Formalism.BasicNotions.D7) : GlobalSectionsSchur D := global_sections_schur D
theorem b10 (D : Formalism.BasicNotions.D7) : BracketPolynomialSpan D := bracket_polynomial_span D
theorem b11 (D : Formalism.BasicNotions.D7) : GradedLatticeStable D := adm_eleven D
theorem b15 (D : Formalism.BasicNotions.D7) : SaturatedLowerSetSpan D := admissible_lowerSet_span D
theorem b19 (D : Formalism.BasicNotions.D7) : WeylDualityLattice D := admissible_lattice_biduality D
theorem a2 (D : Formalism.BasicNotions.D7) : PathColumnBasis D := admissible_polynomial_basis D

end Formalism.MainNotions.G.ColumnFamilies.Top
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ RowTiePE0 RowTiePProj

namespace GmPackP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd d : ℕ}

theorem half [NeZero d] (hLie : ProjLieSelfSt) (Y : FBChart C V O dd) {I0 : Type} [Fintype I0] (p : SelfData Y d I0) (ε : O)
    (hε : ∃ y, ε * ε - ε = (V.l : O) * y) (hε1 : ∀ a, V.MM (p.em a ε - 1))
    (hεx : ∀ x : O, (∀ a, V.MM (p.em a x)) → ∃ y, ε * x = (V.l : O) * y) (M : ℕ → O) (φ : Pt C 1 dd)
    (hT : ∀ i, TendsS V (fun n => Y.B.A.act (M n * ε ^ V.l ^ n) i) (φ i)) :
    (∀ a, comp1 φ (Y.B.A.act a) = comp1 (Y.B.A.act a) φ) ∧
      ∀ v : Fin dd → C, ∃ b : I0 → C, linAct φ v = ∑ c, b c • p.e c := by
  have hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0 := const_of_lim Y hT
  have act0 : ∀ x i, MvPowerSeries.constantCoeff (Y.B.A.act x i) = 0 := Y.B.A.const
  refine ⟨?_, ?_⟩
  · intro a
    funext i
    have L := TendsS.comp1 (φ := fun n => Y.B.A.act (M n * ε ^ V.l ^ n)) (b := fun _ => Y.B.A.act a)
      (fun _ => act0 a) (act0 a) hT (fun _ => TendsS.const _) i
    have R := TendsS.comp1 (φ := fun _ => Y.B.A.act a) (b := fun n => Y.B.A.act (M n * ε ^ V.l ^ n))
      (fun n => act0 _) hφ0 (fun _ => TendsS.const _) hT i
    have eq : (fun n => comp1 (Y.B.A.act (M n * ε ^ V.l ^ n)) (Y.B.A.act a) i) =
        fun n => comp1 (Y.B.A.act a) (Y.B.A.act (M n * ε ^ V.l ^ n)) i := funext fun n => by
      rw [← Y.B.A.mul_act, ← Y.B.A.mul_act, mul_comm]
    rw [eq] at L
    exact L.unique R
  · obtain ⟨E, -, -, -, hET⟩ := StartSelf.lim_endo Y p.em p.em_int p.hd p.em_conj ε hε hεx (fun _ => 1)
      (fun N a => by rw [sub_self, map_zero]; exact VF.Ge.zero _)
    have hElim : ∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
        V.Ge N (MvPowerSeries.coeff μ (E i) - MvPowerSeries.coeff μ (Y.B.A.act (ε ^ V.l ^ n) i)) := by
      intro N i μ
      obtain ⟨n0, h⟩ := hET i μ N
      exact ⟨n0, fun n hn => by simpa only [one_mul] using h n hn⟩
    have hEspan := hLie C V O dd Y d I0 p ε hε hε1 hεx E hElim
    have hEφ : comp1 E φ = φ := by
      funext i
      have L := TendsS.comp1 (φ := fun n => Y.B.A.act (1 * ε ^ V.l ^ n)) (b := fun n => Y.B.A.act (M n * ε ^ V.l ^ n))
        (fun n => act0 _) hφ0 hET hT i
      have hdiv : ∀ n, ((V.l : O) ^ (n + 1)) ∣ (1 * ε ^ V.l ^ n) * (M n * ε ^ V.l ^ n) - M n * ε ^ V.l ^ n := by
        intro n
        have e1 : (1 * ε ^ V.l ^ n) * (M n * ε ^ V.l ^ n) - M n * ε ^ V.l ^ n =
            M n * (ε ^ V.l ^ n * ε ^ V.l ^ n - ε ^ V.l ^ n) := by ring
        rw [e1]
        exact dvd_mul_of_dvd_right (sq_cong hε n) _
      have R := tendsS_of_small RowTiePLSmall.lSmall_holds Y
        (x := fun n => (1 * ε ^ V.l ^ n) * (M n * ε ^ V.l ^ n)) (x' := fun n => M n * ε ^ V.l ^ n) hdiv hT i
      have eq : (fun n => comp1 (Y.B.A.act (1 * ε ^ V.l ^ n)) (Y.B.A.act (M n * ε ^ V.l ^ n)) i) =
          fun n => Y.B.A.act ((1 * ε ^ V.l ^ n) * (M n * ε ^ V.l ^ n)) i := funext fun n => by
        rw [Y.B.A.mul_act (1 * ε ^ V.l ^ n) (M n * ε ^ V.l ^ n)]
      rw [eq] at L
      exact L.unique R
    intro v
    obtain ⟨b, hb⟩ := hEspan (linAct φ v)
    exact ⟨b, by rw [← hb, ← VP.linAct_comp1 E φ hφ0, hEφ]⟩

theorem one_entry [NeZero d] (hLie : ProjLieSelfSt) (Y : FBChart C V O dd) {I0 : Type} [Fintype I0] (p : SelfData Y d I0)
    (M : ℕ → O) (t : ZMod d → C) (hMt : ∀ (N : ℕ) a, V.Ge ((N + 1 : ℕ) : ℝ) (t a - p.em a (M N))) :
    ∃ γ γ' : Pt C 1 dd, IsEndo Y γ ∧ IsEndo Y γ' ∧
      (∀ a, comp1 γ (Y.B.A.act a) = comp1 (Y.B.A.act a) γ) ∧
      (∀ a, comp1 γ' (Y.B.A.act a) = comp1 (Y.B.A.act a) γ') ∧
      (∀ c, linAct γ (p.e c) = t (p.ty0 c) • p.e c) ∧
      (∀ c, linAct γ' (p.e c) = t (p.ty0 c + p.hd) • p.e c) ∧
      (∀ v : Fin dd → C, ∃ b : I0 → C, linAct γ v = ∑ c, b c • p.e c) ∧
      (∀ v : Fin dd → C, ∃ b : I0 → C, linAct γ' v = ∑ c, b c • p.e c) ∧
      IntS V (FB.expS C (ev (n := 2) ![comp1 γ (pt C dd 0), pt C dd 1] Y.h -
        ev (n := 2) ![pt C dd 0, comp1 γ' (pt C dd 1)] Y.h)) := by
  obtain ⟨ε, hε, hε1, hεx⟩ := p.em_unr
  have hM : ∀ (N : ℕ) a, V.Ge ((N + 1 : ℕ) : ℝ) (p.em a (M (N + 1) - M N)) := by
    intro N a
    have e2 : p.em a (M (N + 1) - M N) = (t a - p.em a (M N)) - (t a - p.em a (M (N + 1))) := by
      rw [map_sub]; ring
    rw [e2]
    exact (hMt N a).sub ((hMt (N + 1) a).mono (by push_cast; linarith))
  have ht : ∀ a, Tends V (fun n => p.em a (M n)) (t a) := fun a =>
    tends_of_nat fun N => ⟨N, fun n hn => (hMt n a).mono (by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      push_cast; linarith)⟩
  have hεs := star_rel hε
  have hεs1 : ∀ a, V.MM (p.em a (star ε) - 1) := fun a => by rw [p.em_conj]; exact hε1 _
  have hεsx : ∀ x : O, (∀ a, V.MM (p.em a x)) → ∃ y, star ε * x = (V.l : O) * y := by
    intro x hx
    obtain ⟨y, hy⟩ := hεx (star x) fun a => by rw [p.em_conj]; exact hx (a + p.hd)
    refine ⟨star y, ?_⟩
    have h := congrArg star hy
    simp only [star_mul, star_star, star_natCast] at h
    rw [mul_comm, h, mul_comm]
  have hMs : ∀ (N : ℕ) a, V.Ge ((N + 1 : ℕ) : ℝ) (p.em a (star (M (N + 1)) - star (M N))) := fun N a => by
    rw [← star_sub, p.em_conj]; exact hM N (a + p.hd)
  have cvA := StartSelf.actCv_of Y p.em ε hε (fun a => p.em_int a ε) hεx M hM
  have cvB := StartSelf.actCv_of Y p.em (star ε) hεs (fun a => p.em_int a _) hεsx (fun N => star (M N)) hMs
  have sA : (fun n => star (M n * ε ^ V.l ^ n)) = fun n => star (M n) * star ε ^ V.l ^ n :=
    funext fun n => by rw [star_mul', star_pow]
  have sB : (fun n => star (star (M n) * star ε ^ V.l ^ n)) = fun n => M n * ε ^ V.l ^ n :=
    funext fun n => by rw [star_mul', star_pow, star_star, star_star]
  obtain ⟨γ, γb, hγI, -, hγl, hγbl, hhom, hexp⟩ := endomorphism_limit_integral Y (fun n => M n * ε ^ V.l ^ n) cvA (by rw [sA]; exact cvB)
  obtain ⟨γ2, -, hγ2I, -, hγ2l, -, hhom2, -⟩ := endomorphism_limit_integral Y (fun n => star (M n) * star ε ^ V.l ^ n) cvB
    (by rw [sB]; exact cvA)
  have hT : ∀ i, TendsS V (fun n => Y.B.A.act (M n * ε ^ V.l ^ n) i) (γ i) := tends_of_endomorphism_limit Y hγl
  have hTb : ∀ i, TendsS V (fun n => Y.B.A.act (star (M n) * star ε ^ V.l ^ n) i) (γb i) := by
    have h := tends_of_endomorphism_limit Y hγbl
    simpa only [star_mul', star_pow] using h
  have hT2 : ∀ i, TendsS V (fun n => Y.B.A.act (star (M n) * star ε ^ V.l ^ n) i) (γ2 i) := tends_of_endomorphism_limit Y hγ2l
  have heq : γ2 = γb := funext fun i => (hT2 i).unique (hTb i)
  subst heq
  obtain ⟨hc, hi⟩ := half hLie Y p ε hε hε1 hεx M γ hT
  obtain ⟨hc', hi'⟩ := half hLie Y p (star ε) hεs hεs1 hεsx (fun N => star (M N)) γ2 hT2
  refine ⟨γ, γ2, ⟨hγI, const_of_lim Y hT, hhom⟩, ⟨hγ2I, const_of_lim Y hT2, hhom2⟩, hc, hc', ?_, ?_, hi, hi', hexp⟩
  · exact fun c => StartSelf.lin_of_lim Y p M ε hε1 t ht γ hT c
  · exact fun c => StartSelf.lin_of_lim Y p (fun N => star (M N)) (star ε) hεs1 (fun a => t (a + p.hd))
      (fun a => by simp only [p.em_conj]; exact ht (a + p.hd)) γ2 hT2 c

end GmPackP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd d : ℕ}

theorem gmPack_of_lie [NeZero d] (hLie : ProjLieSelfSt) (Y : FBChart C V O dd) {I0 : Type} [Fintype I0]
    (p : SelfData Y d I0) : GmPackSt Y p := by
  choose Mm hMm using fun N : ℕ => p.gm_lim (N + 1)
  have h := fun r s : Fin 2 => GmPackP.one_entry hLie Y p (fun N => Mm N r s) (fun a => p.gm a r s)
    (fun N a => hMm N a r s)
  choose γ γ' h1 h2 h3 h4 h5 h6 h7 h8 h9 using h
  exact ⟨γ, γ', ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩⟩

theorem gmPack_of [NeZero d] (hE : RowTiePKey.KeyEigSt) (Y : FBChart C V O dd) {I0 : Type} [Fintype I0]
    (p : SelfData Y d I0) : GmPackSt Y p := gmPack_of_lie (projLieSelf_of hE) Y p

theorem gmPack_holds [NeZero d] (Y : FBChart C V O dd) {I0 : Type} [Fintype I0] (p : SelfData Y d I0) :
    GmPackSt Y p := gmPack_of RowTiePKey.keyEig_holds Y p

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds SelfConjCharts MvPowerSeries

theorem r1sExpLow_holds : ExpLowOrderTruncation := by
  intro C _ _ F m hm hK i j hj
  have h2 : ∀ k, coeff (ee i j) (F ^ (k + 1 + 1)) = 0 := by
    intro k
    have e : F ^ (k + 1 + 1) = (F * F) * F ^ k := by ring
    rw [e]
    exact kmul (a := 2 * m) (b := 0) (fun i j h => kmul hK hK i j (by omega))
      (fun _ _ h => absurd h (Nat.not_lt_zero _)) i j (by omega)
  show ∑ k ∈ Finset.range ((ee i j).degree + 1), coeff (ee i j) (F ^ k) / (k.factorial : C) = _
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  rw [add_comm]
  congr 1
  cases hd : (ee i j).degree with
  | zero =>
    rw [Finset.sum_range_zero]
    have h0 : ee i j = 0 := (Finsupp.degree_eq_zero_iff _).1 hd
    have hj0 : j = 0 := by
      have := DFunLike.congr_fun h0 1
      simpa [ee_one] using this
    exact (hK i j (by omega)).symm
  | succ n =>
    rw [Finset.sum_range_succ', Finset.sum_eq_zero (fun k _ => by rw [h2 k, zero_div])]
    simp

end Formalism.L2.FormalSeriesBounds
end
end
