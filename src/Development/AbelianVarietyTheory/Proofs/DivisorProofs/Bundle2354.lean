module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2327
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2328
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2341
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical

@[expose] public section

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTop.DgShare

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem antitone_of_gapGe (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) {la : AllWt.Weight Dw} (h : GapGe 1 la) :
    (∀ τ, Antitone (la τ)) ∧ ∀ τ, 1 ≤ gap (la τ) (Dw.p - 1) := by
  refine ⟨fun τ => ?_, fun τ => h τ _ (by omega)⟩
  have key : ∀ (n : ℕ) (a b : Fin (Dw.p + Dw.q)), (b : ℕ) = a + n → la τ b ≤ la τ a := by
    intro n
    induction n with
    | zero => intro a b e; rw [show b = a from Fin.ext e]
    | succ n ih =>
      intro a b e
      have hb := b.2
      have h1 := ih a ⟨a + n, by omega⟩ rfl
      have h2 := h τ (a + n) (by omega)
      rw [gap_eq (la τ) (i := ⟨a + n, by omega⟩) (j := b) e] at h2
      omega
  intro a b hab
  exact key (b - a) a b (by have : (a : ℕ) ≤ b := hab; omega)

theorem gapGe_of_wtBig {P : WtPar Dw} (h : WtBig P) : GapGe 1 P.u₁ ∧ GapGe 1 P.u₂ ∧ ∀ j, GapGe 1 (P.wt j) := by
  have h3 : GapGe 3 P.u₁ := h.gaps.mono (by
    have : 3 * 1 ≤ (FlagTan.dimFlag Dw + 3) * ((FlagTan.dimFlag Dw + 1).choose 2 + 4 * (Dw.p + Dw.q) + FlagTan.dimFlag Dw + 3) :=
      Nat.mul_le_mul (by omega) (by omega)
    exact_mod_cast this)
  have h2 : ∀ τ k, k + 1 < Dw.p + Dw.q → 3 ≤ gap (P.u₂ τ) k := fun τ k hk => by
    have a := h3 τ k hk
    have b := (P.gap_rem τ k).1
    simp only [gap, dif_pos hk, WtPar.u₂, Pi.add_apply] at a b ⊢
    omega
  refine ⟨h3.mono (by norm_num), fun τ k hk => le_trans (by norm_num) (h2 τ k hk), fun j τ k hk => ?_⟩
  have a := h3 τ k hk
  have b := h2 τ k hk
  have c : -2 ≤ gap (FlagTan.kap Dw τ) k := by
    simp only [gap, dif_pos hk, FlagTan.kap]
    split_ifs <;> push_cast <;> omega
  simp only [gap, dif_pos hk, WtPar.wt, WtPar.uc, Pi.add_apply, Pi.smul_apply] at a b c ⊢
  simp only [nsmul_eq_mul]
  have e1 := mul_nonneg (Int.natCast_nonneg (FlagTan.dimFlag Dw)) (le_trans (by norm_num) a)
  have e2 := mul_nonneg (Int.natCast_nonneg j) (le_trans (by norm_num) a)
  nlinarith

end Weights

end GlobalTheory.CovTop.DgShare

end
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSApp

theorem gap_add_vec {N : ℕ} (v w : Fin N → ℤ) (k : ℕ) : gap (v + w) k = gap v k + gap w k := by
  unfold gap
  split_ifs
  · simp only [Pi.add_apply]; ring
  · simp

theorem gaps_u₁_u₂_of_wtBig {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    (P : WtPar Dw) (hB : WtBig P) (τ : Psi H) (a b : Fin (Dw.p + Dw.q)) (hab : (b : ℕ) = a + 1) :
    (((CompHt.dimFlag Dw + 3) ^ 2 + 2 * (Dw.p + Dw.q) : ℕ) : ℤ) ≤ P.u₁ τ a - P.u₁ τ b ∧
    (((CompHt.dimFlag Dw + 3) ^ 2 + 2 * (Dw.p + Dw.q) : ℕ) : ℤ) ≤ P.u₂ τ a - P.u₂ τ b := by
  have hk : (a : ℕ) + 1 < Dw.p + Dw.q := by have := b.2; omega
  have g1 := hB.gaps τ a hk
  have g2 := (P.gap_rem τ a).1
  have e1 : P.u₁ τ a - P.u₁ τ b = gap (P.u₁ τ) a := (gap_eq _ hab).symm
  have e2 : P.u₂ τ a - P.u₂ τ b = gap (P.u₁ τ) a + gap (P.rem τ) a := by
    rw [← gap_eq _ hab]
    exact gap_add_vec (P.u₁ τ) (P.rem τ) a
  have hn : (CompHt.dimFlag Dw + 3) ^ 2 + 2 * (Dw.p + Dw.q) ≤
      (FlagTan.dimFlag Dw + 3) * ((FlagTan.dimFlag Dw + 1).choose 2 + 4 * (Dw.p + Dw.q) + FlagTan.dimFlag Dw + 3) := by
    rw [dimFlag_eq]
    generalize FlagTan.dimFlag Dw = D
    generalize Dw.p + Dw.q = N
    generalize (D + 1).choose 2 = C
    nlinarith [Nat.zero_le (D * C), Nat.zero_le (D * N), Nat.zero_le C]
  have hn' : (((CompHt.dimFlag Dw + 3) ^ 2 + 2 * (Dw.p + Dw.q) : ℕ) : ℤ) ≤
      (((FlagTan.dimFlag Dw + 3) * ((FlagTan.dimFlag Dw + 1).choose 2 + 4 * (Dw.p + Dw.q) + FlagTan.dimFlag Dw + 3) : ℕ) : ℤ) :=
    by exact_mod_cast hn
  rw [e1, e2]
  exact ⟨hn'.trans g1, by linarith⟩

end GlobalTheory.HSApp
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.CovTop.ShareRowsNef

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem antitone_of_gapGe (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) {la : AllWt.Weight Dw} (h : GapGe 1 la) :
    (∀ τ, Antitone (la τ)) ∧ ∀ τ, 1 ≤ gap (la τ) (Dw.p - 1) := by
  refine ⟨fun τ => ?_, fun τ => h τ _ (by omega)⟩
  have key : ∀ (n : ℕ) (a b : Fin (Dw.p + Dw.q)), (b : ℕ) = a + n → la τ b ≤ la τ a := by
    intro n
    induction n with
    | zero => intro a b e; rw [show b = a from Fin.ext e]
    | succ n ih =>
      intro a b e
      have hb := b.2
      have h1 := ih a ⟨a + n, by omega⟩ rfl
      have h2 := h τ (a + n) (by omega)
      rw [gap_eq (la τ) (i := ⟨a + n, by omega⟩) (j := b) e] at h2
      omega
  intro a b hab
  exact key (b - a) a b (by have : (a : ℕ) ≤ b := hab; omega)

theorem gapGe_of_wtBig {P : WtPar Dw} (h : WtBig P) : GapGe 1 P.u₁ ∧ GapGe 1 P.u₂ ∧ ∀ j, GapGe 1 (P.wt j) := by
  have h3 : GapGe 3 P.u₁ := h.gaps.mono (by
    have : 3 * 1 ≤ (FlagTan.dimFlag Dw + 3) * ((FlagTan.dimFlag Dw + 1).choose 2 + 4 * (Dw.p + Dw.q) + FlagTan.dimFlag Dw + 3) :=
      Nat.mul_le_mul (by omega) (by omega)
    exact_mod_cast this)
  have h2 : ∀ τ k, k + 1 < Dw.p + Dw.q → 3 ≤ gap (P.u₂ τ) k := fun τ k hk => by
    have a := h3 τ k hk
    have b := (P.gap_rem τ k).1
    simp only [gap, dif_pos hk, WtPar.u₂, Pi.add_apply] at a b ⊢
    omega
  refine ⟨h3.mono (by norm_num), fun τ k hk => le_trans (by norm_num) (h2 τ k hk), fun j τ k hk => ?_⟩
  have a := h3 τ k hk
  have b := h2 τ k hk
  have c : -2 ≤ gap (FlagTan.kap Dw τ) k := by
    simp only [gap, dif_pos hk, FlagTan.kap]
    split_ifs <;> push_cast <;> omega
  simp only [gap, dif_pos hk, WtPar.wt, WtPar.uc, Pi.add_apply, Pi.smul_apply] at a b c ⊢
  simp only [nsmul_eq_mul]
  have e1 := mul_nonneg (Int.natCast_nonneg (FlagTan.dimFlag Dw)) (le_trans (by norm_num) a)
  have e2 := mul_nonneg (Int.natCast_nonneg j) (le_trans (by norm_num) a)
  nlinarith

theorem two_le_dimFlag (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) (hf : 2 < Module.finrank ℚ E / 2) : 2 ≤ FlagTan.dimFlag Dw := by
  unfold FlagTan.dimFlag
  have : 1 ≤ (Dw.p + Dw.q).choose 2 := Nat.choose_pos (by omega)
  nlinarith

end Weights

end GlobalTheory.CovTop.ShareRowsNef

end
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false


noncomputable section

namespace GlobalTheory.CovTop.LowNonzero

theorem gapGe_wt_add_parWt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (P : WtPar Dw) (hB : WtBig P) (j : ℕ) (w : Psi H → ℤ) :
    GapGe (((FlagTan.dimFlag Dw + 1).choose 2 + 1 : ℕ) : ℤ) (P.wt j + GlobalTheory.FlatLine.parWt Dw w - FlagTan.kap Dw) := by
  intro τ k hk
  have a := (gaps_of_wtBig _ _ _ P hB P.u₁ (by simp)).1 τ k hk
  have hg := hB.gaps τ k hk
  have b := (P.gap_rem τ k).1
  have c : gap (GlobalTheory.FlatLine.parWt Dw w τ) k = 0 := by
    simp [gap, GlobalTheory.FlatLine.parWt]
  have hC0 : (0 : ℤ) ≤ (((FlagTan.dimFlag Dw + 1).choose 2 : ℕ) : ℤ) := Int.natCast_nonneg _
  have hD0 : (0 : ℤ) ≤ (FlagTan.dimFlag Dw : ℤ) := Int.natCast_nonneg _
  have hp0 : (0 : ℤ) ≤ (Dw.p : ℤ) := Int.natCast_nonneg _
  have hq0 : (0 : ℤ) ≤ (Dw.q : ℤ) := Int.natCast_nonneg _
  have e1 := mul_nonneg hD0 (le_trans zero_le_one a)
  have e2 := mul_nonneg (Int.natCast_nonneg j) (le_trans zero_le_one a)
  simp only [WtPar.wt, WtPar.uc, WtPar.u₂, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, gap_add, gap_sub, gap_nsmul, c]
  push_cast at hg ⊢
  nlinarith [mul_nonneg hD0 hC0, mul_nonneg hD0 hp0, mul_nonneg hD0 hq0, mul_nonneg hD0 hD0]


open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.Vanishing.H0 ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory in
theorem ne_zero_of_noBase {k : Type} [Field k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {hB : B.IsLB}
    {W : Submodule k (H0 p B ⊤)} {U : Y.Opens} (h : NoBase hB W U) (hU : (U : Set Y).Nonempty) : ∃ f ∈ W, f ≠ 0 := by
  obtain ⟨y, hy⟩ := hU
  by_contra hne
  push Not at hne
  refine h y hy ((mem_support_baseIdeal hB W y).2 fun s hs hy' => ?_)
  obtain ⟨i, hi⟩ := exists_chart hB y
  have hu := (isUnit_ger_iff _ hi).2 hy'
  rw [ger_toSec, hne s hs, map_zero] at hu
  exact not_isUnit_zero hu

end GlobalTheory.CovTop.LowNonzero

end
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct



namespace GlobalTheory.HSShortRoad

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem antitone_of_gapGe {g : ℤ} (hg : 0 ≤ g) {la : AllWt.Weight Dw} (h : GapGe g la) (τ : Psi H) :
    Antitone (la τ) := by
  intro a i hai
  have h0 : ∀ k, 0 ≤ gap (la τ) k := fun k => by
    by_cases hk : k + 1 < Dw.p + Dw.q
    · exact hg.trans (h τ k hk)
    · rw [gap, dite_eq_right hk]
  have e := ofGaps_gap (la τ) a i
  have := Finset.sum_le_sum_of_subset_of_nonneg (f := gap (la τ)) (Finset.range_mono (show (a : ℕ) ≤ i from hai))
    fun k _ _ => h0 k
  rw [ofGaps] at e
  linarith

theorem gapGe_wt {P : WtPar Dw} (h : WtBig P) (j : ℕ) : GapGe (FlagTan.dimFlag Dw + 1) (P.wt j) := by
  have h₁ : GapGe (FlagTan.dimFlag Dw + 3) P.u₁ := h.gaps.mono (by
    push_cast
    exact le_mul_of_one_le_right (by positivity) (by omega))
  intro τ k hk
  have a := h₁ τ k hk
  have b := (P.gap_rem τ k).1
  have c : -2 ≤ gap (FlagTan.kap Dw τ) k := by rw [gap_kap τ hk]; split_ifs <;> omega
  have d : 0 ≤ gap (P.u₁ τ) k := le_trans (by positivity) a
  simp only [WtPar.wt, WtPar.uc, WtPar.u₂, Pi.add_apply, Pi.smul_apply, gap_add, gap_nsmul]
  nlinarith [mul_nonneg (Int.natCast_nonneg j) d, mul_nonneg (Int.natCast_nonneg (FlagTan.dimFlag Dw)) d]

noncomputable abbrev sz (la : AllWt.Weight Dw) : ℝ := ∑ τ, ∑ k, |(la τ k : ℝ)|

theorem one_le_sz {la : AllWt.Weight Dw} (h : 0 < sz la) : 1 ≤ sz la := by
  have e : sz la = ((∑ τ, ∑ k, |la τ k| : ℤ) : ℝ) := by push_cast; rfl
  rw [e] at h ⊢
  exact_mod_cast (show (0 : ℤ) < _ by exact_mod_cast h)

end Weights

theorem log_le_of_le_exp {s y : ℝ} (h0 : 0 ≤ s) (hy : 0 ≤ y) (h : s ≤ Real.exp y) : Real.log s ≤ y := by
  rcases h0.eq_or_lt with rfl | h0
  · simpa using hy
  · exact (Real.log_le_iff_le_exp h0).2 h

theorem log_size_le {a L κ s : ℝ} (ha : 0 < a) (hL : 1 ≤ L) (h₁ : Real.log a ≤ L) (hκ : 1 ≤ κ)
    (h₂ : Real.log κ ≤ 2 * L) (h0 : 0 ≤ s) (h : s ≤ 2 * ((a * L) ^ 2 * κ)) : Real.log s ≤ 10 * L := by
  have hp : 0 < 2 * ((a * L) ^ 2 * κ) := by positivity
  refine log_le_of_le_exp h0 (by linarith) (h.trans ((Real.log_le_iff_le_exp hp).1 ?_))
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_mul ha.ne' (by positivity)]
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < L by linarith)
  push_cast
  linarith

theorem span_of_shortGen {F V κ : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    {Nm : κ → V → ℝ} {M : Submodule (𝓞 F) V} {n : ℕ} {w : Fin n → V} {Λ : ℝ} (h : CompHt.IsShortGen Nm M w Λ)
    (hM : Submodule.span F (M : Set V) = ⊤) : (∀ i, w i ∈ M) ∧ Submodule.span F (Set.range w) = ⊤ :=
  ⟨fun i => (h.gen _).2 (Submodule.subset_span ⟨i, rfl⟩), top_le_iff.1 (hM.ge.trans (Submodule.span_le.2 fun x hx =>
    Submodule.span_subset_span ℤ F _ ((h.gen x).1 hx)))⟩

theorem sum_univ_inst {α : Type} {i1 i2 : Fintype α} (f : α → ℝ) :
    @Finset.sum α ℝ _ (@Finset.univ α i1) f = @Finset.sum α ℝ _ (@Finset.univ α i2) f := by
  obtain rfl : i1 = i2 := Subsingleton.elim _ _
  rfl

theorem bound_le {C Z PP κ : ℝ} (hC : 0 ≤ C) (hZ : 1 ≤ Z) (hCZ : 6 * C ≤ Z) (hP : Z ^ 12 ≤ PP) (hκ : 1 ≤ κ) :
    C * (Z ^ 3 * (Z ^ 2 * κ) + Z ^ 5) ≤ PP * κ := by
  have h5 : 0 ≤ Z ^ 5 := by positivity
  have e : C * (Z ^ 3 * (Z ^ 2 * κ) + Z ^ 5) = C * Z ^ 5 * (κ + 1) := by ring
  have a1 : C * Z ^ 5 * (κ + 1) ≤ C * Z ^ 5 * (2 * κ) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have a2 : 2 * C * Z ^ 5 ≤ Z * Z ^ 5 := mul_le_mul_of_nonneg_right (by linarith) h5
  have a3 : Z * Z ^ 5 ≤ Z ^ 12 := by
    rw [← pow_succ']
    exact pow_le_pow_right₀ hZ (by norm_num)
  have a4 : 2 * C * Z ^ 5 ≤ PP := a2.trans (a3.trans hP)
  rw [e]
  calc C * Z ^ 5 * (κ + 1) ≤ C * Z ^ 5 * (2 * κ) := a1
    _ = (2 * C * Z ^ 5) * κ := by ring
    _ ≤ PP * κ := mul_le_mul_of_nonneg_right a4 (by linarith)

end GlobalTheory.HSShortRoad
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

theorem _root_.GlobalTheory.T.ampleModuloEffectiveAwayFromPoint_pull_affine : ∀ (Y X : Scheme.{0}) (π : X ⟶ Y) [IsAffineHom π] (N : LB Y), N.IsLB → ∀ x : X, AmpleAt N (π x) → AmpleAt (N.pull π) x := by
  first | exact @GlobalTheory.AmplePull.ampleAt_pull | exact GlobalTheory.AmplePull.ampleAt_pull | (intros; apply GlobalTheory.AmplePull.ampleAt_pull <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp

theorem gapGe_stdWt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) :
    GapGe 1 (GlobalTheory.CompHt.stdWt (Psi H) (Dw.p + Dw.q) : AllWt.Weight Dw) := by
  intro τ k hk
  simp only [gap, dif_pos hk, GlobalTheory.CompHt.stdWt]
  push_cast
  omega

theorem gapGe_sub_smul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    (m : ℕ) (b : AllWt.Weight Dw) (h : GapGe (m : ℤ) b) :
    GapGe 0 (b - m • (GlobalTheory.CompHt.stdWt (Psi H) (Dw.p + Dw.q) : AllWt.Weight Dw)) := by
  intro τ k hk
  have h1 := h τ k hk
  simp only [gap, dif_pos hk, Pi.sub_apply, Pi.smul_apply, GlobalTheory.CompHt.stdWt] at h1 ⊢
  rw [nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  linarith

theorem cls_common_nsmul {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (n : ℕ) (a : Λ) :
    cls (B (n • a)) (C.isLB (n • a)) = n • cls (B a) (C.isLB a) := by
  induction n with
  | zero =>
    have h := cls_common_add C 0 0
    simp only [add_zero] at h
    simp only [zero_nsmul]
    exact left_eq_add.1 h
  | succ n ih =>
    rw [succ_nsmul, cls_common_add C, ih, succ_nsmul]

end GlobalTheory.HSApp
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

theorem _root_.GlobalTheory.T.isBigLineBundle_of_smul_class_eq_ampleAt_add_nef : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N₁ N₂ : LB X) (hN : N.IsLB) (h₁ : N₁.IsLB) (h₂ : N₂.IsLB) (a : ℕ) (x : X), IsNef k N → 0 < a → a • cls N hN = cls N₁ h₁ + cls N₂ h₂ → AmpleAt N₁ x → IsNef k N₂ → IsBig k N := by
  first | exact @GlobalTheory.isBig_of_smul_cls_eq_add_ampleAt | exact GlobalTheory.isBig_of_smul_cls_eq_add_ampleAt | (intros; apply GlobalTheory.isBig_of_smul_cls_eq_add_ampleAt <;> assumption)
end
