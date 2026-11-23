module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle941
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2428
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2430
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2354
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2381
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2363
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2425
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2434
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
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
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false


noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RefSum.QuoShape

theorem antitone_of_adj {N : ℕ} (f : Fin N → ℤ) (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → f b ≤ f a) : Antitone f := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  have hab' : a ≤ b := hab
  clear hab
  induction b, hab' using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact (h ⟨n, by omega⟩ ⟨n + 1, hb⟩ rfl).trans (ih (by omega))

theorem shape {ι : Type} [Fintype ι] {N : ℕ} (W : GlobalTheory.MeanTop.Wts ι N) (hH : W.Hyp) (hD : W.IsDiv) (n : ℕ)
    (hn : 4 * (W.T : ℤ) * n ≤ W.h0) :
    (∀ τ, Antitone (W.u1 τ)) ∧
    (∀ τ (a b : Fin N), (a : ℕ) + 1 = W.p → (b : ℕ) = W.p → (n : ℤ) + 1 ≤ W.u1 τ a - W.u1 τ b) ∧
    ∀ τ a, |(W.u1 τ a : ℝ)| ≤ W.b / 2 := by
  have hT : (4 : ℤ) ≤ W.T := by have := hH.h1; omega
  have bar : ∀ τ (a b : Fin N), (a : ℕ) + 1 = W.p → (b : ℕ) = W.p → (n : ℤ) + 1 ≤ W.u1 τ a - W.u1 τ b := by
    intro τ a b ha hb
    have h := ((GlobalTheory.MeanTop.divided_gaps ι N W hH hD τ a b (by omega)).2.1 hb).2
    have h2 : (n : ℤ) ≤ W.u1 τ a - W.u1 τ b - 3 * N := le_of_mul_le_mul_left (hn.trans h) (by omega)
    have h3 := b.isLt
    omega
  refine ⟨fun τ => antitone_of_adj _ fun a b hab => ?_, bar, fun τ a => ?_⟩
  · by_cases hb : (b : ℕ) = W.p
    · have := bar τ a b (by omega) hb
      omega
    · have := (GlobalTheory.MeanTop.divided_gaps ι N W hH hD τ a b hab).1 hb
      omega
  · have h1 := (GlobalTheory.MeanTop.divided_entries ι N W hH hD τ a).1
    have h2 : 4 * |W.u1 τ a| ≤ |W.u τ a| + W.c0 + 4 * N :=
      (mul_le_mul_of_nonneg_right (by omega) (abs_nonneg _)).trans h1
    have h3 : 4 * |(W.u1 τ a : ℝ)| ≤ |(W.u τ a : ℝ)| + W.c0 + 4 * N := by exact_mod_cast h2
    have h4 := hH.h5 τ a
    linarith

theorem ranks_le (D : D7) : 80 * D.R.f * D.R.r ^ 2 ≤ D.R.r * D.R.f ^ 2 * D.R.m ^ 2 * D.R.k * (D.R.f * D.R.r.choose 2) := by
  have hf := SizeTZ.two_le_f D
  have hr := SizeTZ.six_le_r D
  have hm := D.R.two_le_m
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  generalize D.R.f = f at *
  generalize D.R.r = r at *
  generalize D.R.m = m at *
  generalize D.R.k = k at *
  have hc : r ≤ r.choose 2 := by
    rw [Nat.choose_two_right, Nat.le_div_iff_mul_le (by norm_num)]
    exact Nat.mul_le_mul_left _ (by omega)
  calc 80 * f * r ^ 2 = r * 2 ^ 2 * 2 ^ 2 * 5 * (f * r) := by ring
    _ ≤ r * f ^ 2 * m ^ 2 * k * (f * r.choose 2) := by gcongr

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem shape_at {PP : ℝ} (hPP : 1 ≤ PP) (hW : WtNum p i PP) (hi : (i : ℕ) + 1 < D.R.m) (u1 : Psi p.T.Q.H → Fin ((dat p i).p + (dat p i).q) → ℤ)
    (hq : Quo p i PP u1) :
    1 ≤ (dat p i).p ∧ 1 ≤ (dat p i).q ∧ (dat p i).p + (dat p i).q = D.R.r ∧ (∀ τ, Antitone (u1 τ)) ∧
    (∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (a : ℕ) + 1 = (dat p i).p → (b : ℕ) = (dat p i).p →
      (nCol (dat p i) : ℤ) + 1 ≤ u1 τ a - u1 τ b) ∧ ∀ τ a, |(u1 τ a : ℝ)| ≤ 2 * L.sc.b := by
  obtain ⟨h0, S, eta, -, -, -, -, hh, hH⟩ := hW.hyp hi
  have hH1 := hH u1
  have hcol : (nCol (dat p i) : ℝ) ≤ 20 * D.R.f * (D.R.r : ℝ) ^ 2 :=
    SizeTZ.nCol_le_of_pins p.fw.laws.pins ⟨Nat.le_add_left _ _, i.2⟩
  have hr : (80 : ℝ) * D.R.f * (D.R.r : ℝ) ^ 2 ≤
      D.R.r * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * (GlobalTheory.CompHt.dimFlag (dat p i) : ℝ) := by
    rw [hW.dim]; exact_mod_cast ranks_le D
  have hn : 4 * ((lenT p i PP : ℕ) : ℤ) * (nCol (dat p i) : ℕ) ≤ h0 := by
    have hT0 : (0 : ℝ) ≤ lenT p i PP := Nat.cast_nonneg _
    have h1 : 4 * (lenT p i PP : ℝ) * (nCol (dat p i) : ℝ) ≤ h0 := by
      refine le_trans ?_ hh
      generalize (lenT p i PP : ℝ) = T at *
      calc 4 * T * (nCol (dat p i) : ℝ) ≤ 4 * T * (20 * D.R.f * (D.R.r : ℝ) ^ 2) := by gcongr
        _ = 1 * (T * (80 * D.R.f * (D.R.r : ℝ) ^ 2)) := by ring
        _ ≤ PP * (T * (D.R.r * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * (GlobalTheory.CompHt.dimFlag (dat p i) : ℝ))) := by gcongr
        _ = _ := by ring
    exact_mod_cast h1
  obtain ⟨a1, a2, a3⟩ := shape (wtsAt p i PP h0 S eta u1) hH1 ((quo_iff p i PP h0 S eta u1).1 hq) (nCol (dat p i)) hn
  have b1 : D.R.k - 1 < (dat p i).p := hH1.kc_lt
  have b2 : (dat p i).p < (dat p i).p + (dat p i).q := hH1.p_lt
  refine ⟨by omega, by omega, hW.sig.2.2, a1, a2, fun τ a => (a3 τ a).trans (le_of_eq ?_)⟩
  show 4 * L.sc.b / 2 = 2 * L.sc.b
  ring

end GlobalTheory.RefSum.QuoShape

end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem IsSncChart.neg_one_lt_formOrd_sub_sum_sub_ord_of_indep : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u → (∀ j ∈ J, y ∉ Y.basicOpen (z j)) → ∀ F : Γ(Y, U), (∀ h : ∀ j : Option J, Y.presheaf.germ U y hy (j.elim F fun j => z j) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y), LinearIndependent (IsLocalRing.ResidueField (Y.presheaf.stalk y)) (fun j : Option J => ((IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).toCotangent ⟨Y.presheaf.germ U y hy (j.elim F fun j => z j), h j⟩ : IsLocalRing.CotangentSpace (Y.presheaf.stalk y)))) → ∀ (φ f : Y.functionFieldˣ) (a : Fin n → ℚ) (c : ℚ), (φ : Y.functionField) = fnOf U (gen_mem hy) F → UnitAt y ((f : Y.functionField) / φ) → (∀ j ∈ J, a j < 1) → c < 1 → ∀ E : DivOver q, E.Through y → -1 < ((fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (formOf U (gen_mem hy) (dOn q z)) : ℚ) - ∑ j ∈ J, a j * E.ord (u j) - c * E.ord f := by
  intro Y _ _ q n _ B y U hy z J w u hc hJ F hind φ f a c hφ hf ha hc1 E hE
  classical
  haveI := SmoothOfRelativeDimension.smooth n q
  have hn : topologicalKrullDim Y = n := by
    have hd (V : Y.Opens) (hV : IsAffineOpen V) (hne : (V : Set Y).Nonempty) :
        topologicalKrullDim (V : Set Y) = n := by
      rw [topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding
        hV.range_fromSpec]
      exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(Y, V))).trans
        (SmoothDim.ringKrullDim_affineOpen ℂ _ q _ inferInstance V hV hne)
    refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
    · obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top x)
      exact ⟨V, V.isOpen, hx, (hd V hV ⟨x, hx⟩).le⟩
    · obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top y)
      exact (hd V hV ⟨_, hx⟩).ge.trans (topologicalKrullDim_subspace_le _ _)

  have hunit : ∀ g : Y.functionFieldˣ, UnitAt y (g : Y.functionField) → E.ord g = 0 := by
    rintro g ⟨b, hb, hbg⟩
    have h1 : (g : Y.functionField) ∈ E.ring := hE _ ⟨b, hbg⟩
    have h2 : ((g⁻¹ : Y.functionFieldˣ) : Y.functionField) ∈ E.ring := hE _ ⟨↑(hb.unit⁻¹), by
      rw [map_units_inv, IsUnit.unit_spec, hbg]; simp⟩
    have e1 := (E.ord_nonneg_iff g).2 h1
    have e2 := (E.ord_nonneg_iff _).2 h2
    rw [E.ord_inv] at e2
    omega
  have hfφ : E.ord f = E.ord φ := by
    have hg : UnitAt y ((f * φ⁻¹ : Y.functionFieldˣ) : Y.functionField) := by
      simpa [div_eq_mul_inv] using hf
    have h0 := hunit _ hg
    have : f = (f * φ⁻¹) * φ := by group
    rw [this, E.ord_mul, h0, zero_add]
  by_cases hyF : y ∈ Y.basicOpen F
  · have hφu : UnitAt y (φ : Y.functionField) := hφ ▸ (unitAt_fnOf_iff hy _ F).2 hyF
    have hfu : UnitAt y (f : Y.functionField) := by
      have := UnitAt.mul hf hφu
      rwa [div_mul_cancel₀ _ φ.ne_zero] at this
    have h0 := hunit f hfu
    have key := (IsSncChart.neg_one_lt_formOrd_sub_sum ℂ Y q n B y U hy z J w u hc E hE a).1 ha
    rw [h0]
    simpa using key
  · have hmax : ∀ j : Option J, Y.presheaf.germ U y hy (j.elim F fun j => z j) ∈
        IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
      rintro (_ | ⟨j, hj⟩)
      · exact (IsLocalRing.mem_maximalIdeal _).2
          (mem_nonunits_iff.2 fun h => hyF ((Scheme.mem_basicOpen Y F y hy).2 h))
      · exact (IsLocalRing.mem_maximalIdeal _).2
          (mem_nonunits_iff.2 fun h => hJ j hj ((Scheme.mem_basicOpen Y (z j) y hy).2 h))
    have hv : ∀ j : Option J, ((j.elim φ fun j => u j : Y.functionFieldˣ) : Y.functionField) =
        algebraMap (Y.presheaf.stalk y) Y.functionField
          (Y.presheaf.germ U y hy (j.elim F fun j => z j)) := by
      rintro (_ | ⟨j, hj⟩)
      · simp only [Option.elim]
        rw [hφ, algebraMap_germ]
      · simp only [Option.elim]
        rw [hc.val j hj, algebraMap_germ]
    have hc' : ∀ j : Option J, (j.elim c fun j => a j) < 1 := by
      rintro (_ | ⟨j, hj⟩)
      · exact hc1
      · exact ha j hj
    have key := GlobalTheory.IndepDiscrep.neg_one_lt_formOrd_sub_sum Y q n hn y U hy (dOn q z) hc.frame
      (Option J) (fun j => Y.presheaf.germ U y hy (j.elim F fun j => z j)) hmax
      (fun j => j.elim φ fun j => u j) (fun j => j.elim c fun j => a j) (hind hmax) hv hc' E hE
    rw [Fintype.sum_option] at key
    simp only [Option.elim] at key
    rw [Finset.sum_coe_sort J (fun j => a j * (E.ord (u j) : ℚ))] at key
    rw [hfφ]
    linarith

end GlobalTheory.Discrepancy
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Discrepancy

theorem DivOver.exists_over_of_bijective_complex : ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp ℂ) (s : Y ⟶ X) [IsDominant s],
    Function.Bijective (functionFieldMap s) → ∀ E' : DivOver (s ≫ p), ∃ E : DivOver p, DivOver.Over s E' E :=
  fun p s _ hb E' => DivOver.exists_over_of_bijective ℂ _ _ p s hb E'

end GlobalTheory.Discrepancy
end
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.cartierDivisorPullback_support_and_effective : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] (D : CartierDiv X), (∀ y : Y, y ∈ (pullCart s D).supp → s y ∈ D.supp) ∧ (D.Eff → (pullCart s D).Eff) := by
  first | exact @GlobalTheory.Discrepancy.pullCart_supp_and_eff | exact GlobalTheory.Discrepancy.pullCart_supp_and_eff | (intros; apply GlobalTheory.Discrepancy.pullCart_supp_and_eff <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.exists_primeDivisor_over_source_birational : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ E : DivOver p, ∃ E' : DivOver (s ≫ p), DivOver.Over s E' E := by
  first | exact @GlobalTheory.Discrepancy.DivOver.exists_over | exact GlobalTheory.Discrepancy.DivOver.exists_over | (intros; apply GlobalTheory.Discrepancy.DivOver.exists_over <;> assumption)
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

namespace GlobalTheory.Discrepancy

theorem DivOver.exists_over_complex : ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp ℂ) (s : Y ⟶ X) [IsDominant s],
    Function.Bijective (functionFieldMap s) → ∀ E : DivOver p, ∃ E' : DivOver (s ≫ p), DivOver.Over s E' E := by
  intro X Y _ _ p s _ hs E
  exact DivOver.exists_over ℂ X Y p s hs E

end GlobalTheory.Discrepancy
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.exists_lifted_function_on_logResolution : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G N : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), IsLogRes p n η m G s K B → (∀ U : X.Opens, IsAffineOpen U → Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB (pullCart s N - F))) (s ⁻¹ᵁ U) 1)) → ∀ (y : X) (σ : Y), (∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → F.mult v ≤ 0) → s σ ⤳ y → Order.coheight σ = 1 → ∃ h : Y.functionField, (-F).RegularAt σ (h - 1) ∧ ∀ v : Y, v ≠ σ → Order.coheight v = 1 → s v ⤳ y → (-F).RegularAt v h := by
  first | exact @GlobalTheory.PairStep.exists_lifted_fn | exact GlobalTheory.PairStep.exists_lifted_fn | (intros; apply GlobalTheory.PairStep.exists_lifted_fn <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.isSncAdaptedCoordinates_of_mem_nhds : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], ∀ (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), genericPoint Y ∉ B → IsSncChart q n B y U hy z J w u → ∃ V : Y.Opens, y ∈ V ∧ ∀ y' ∈ V, ∃ (hy' : y' ∈ U) (J' : Finset (Fin n)), J' ⊆ J ∧ IsSncChart q n B y' U hy' z J' w u ∧ ∀ j ∈ J', y' ∉ Y.basicOpen (z j) := by
  first | exact @GlobalTheory.PairStep.isSncChart_spread | exact GlobalTheory.PairStep.isSncChart_spread | (intros; apply GlobalTheory.PairStep.isSncChart_spread <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.coheight_and_multiplicity_pullback_isIso_open : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (U : X.Opens), IsIso (s ∣_ U) → ∀ w : Y, s w ∈ U → Order.coheight w = Order.coheight (s w) ∧ ∀ D : CartierDiv X, (pullCart s D).mult w = D.mult (s w) := by
  first | exact @GlobalTheory.Discrepancy.MultIso.coheight_eq_and_mult_pullCart | exact GlobalTheory.Discrepancy.MultIso.coheight_eq_and_mult_pullCart | (intros; apply GlobalTheory.Discrepancy.MultIso.coheight_eq_and_mult_pullCart <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

set_option autoImplicit false

namespace GlobalTheory.BirOrd

theorem ord_and_formOrd_of_over : ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (n : ℕ),
    topologicalKrullDim X = n → ∀ (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) →
    ∀ (E : DivOver p) (E' : DivOver (s ≫ p)), DivOver.Over s E' E →
      (∀ g : X.functionFieldˣ, E'.ord (fnPull s g) = E.ord g) ∧
      ∀ η : RatForms p n, η ≠ 0 → (fun ω => @dite ℤ (∃ a, E'.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (ratPull p s n η) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η := by
  intro X Y _ _ p _ n _ s _ hbij E E' hO
  exact ⟨DivOver.Over.ord_fnPull_of_bijective ℂ X Y p s hbij E' E hO,
    fun η hη => formOrd_ratPull_of_over ℂ X Y p s hbij E' E hO n η hη⟩

end GlobalTheory.BirOrd
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

set_option autoImplicit false
noncomputable section
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory.EffGen

theorem core_gen (hK : GlobalTheory.Published.NadelVanishingAndNonKltDivisor) (hNN : GlobalTheory.Published.NefNumerics)
    (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (q : X ⟶ Sp ℂ) (D : ℕ)
    [SmoothOfRelativeDimension D q] (hq : IsProjOver q) (hD : 1 ≤ D) :
    letI := algebraΓOfHom q
    ∀ (K : CanonLB q D) (N N' B : LB X) (hN : N.IsLB) (hN' : N'.IsLB) (hB : B.IsLB) (m : ℕ) (x : X),
      IsClosed ({x} : Set X) → IsNef ℂ N → IsBig ℂ N → IsNef ℂ N' → (D + 1).choose 2 < m →
      (∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e →
        topologicalKrullDim (Z : Set X) = e → 1 ≤ interNumRed ℂ Z (fun _ : Fin e => N)) →
      cls B hB = m • cls N hN + cls N' hN' → ∃ s : (tens K.bundle B).Sec, x ∈ nonzeroLocus s := by
  letI := algebraΓOfHom q
  intro K N N' B hN hN' hB m x hx hNn hNb hN'n hm hpos hBc
  have hm1 : 1 ≤ m := by omega
  obtain ⟨N₀, h₀, hc₀, hn₀, hb₀⟩ := GlobalTheory.T.exists_nef_big_of_class_eq_smul_add_smul hNN ℂ X q hq N N' hN hN' (2 * m - 1) 2 hNn hNb hN'n (by omega)
  obtain ⟨m', D₀, U, hm', hD₀, hcur, hxU, hklt, hnk⟩ := GlobalTheory.T.exists_isolated_nonKlt_divisor_smooth_projective hK.2 X q D hq hD N₀ 2 x two_pos hn₀ hb₀ hx
    (fun Z e hZ hxZ he hdim => by
      have h1 := hpos Z e hZ hxZ he hdim
      have h2 := GlobalTheory.T.pow_mul_intersection_le_of_nef_class_on_closed hNN ℂ X q hq N N' N₀ hN hN' h₀ (2 * m - 1) 2 Z e hNn hN'n hc₀ hdim
      have h3 : ((2 * m - 1 : ℕ) : ℤ) ^ e ≤ interNumRed ℂ Z (fun _ : Fin e => N₀) := by
        have : (0 : ℤ) ≤ ((2 * m - 1 : ℕ) : ℤ) ^ e := by positivity
        nlinarith
      have h3' : (((2 * m - 1 : ℕ) : ℝ)) ^ e ≤ (interNumRed ℂ Z (fun _ : Fin e => N₀) : ℝ) := by
        exact_mod_cast h3
      have h4 : ((((D + 1).choose 2 : ℕ) : ℝ) * 2) ^ e < ((2 * m - 1 : ℕ) : ℝ) ^ e := by
        refine pow_lt_pow_left₀ ?_ (by positivity) (by omega)
        have : (D + 1).choose 2 * 2 < 2 * m - 1 := by omega
        exact_mod_cast this
      rw [lt_div_iff₀ (by positivity), ← mul_pow]
      push_cast at h4 h3' ⊢
      linarith)
  obtain ⟨J, hJ, hvan⟩ := GlobalTheory.T.nadel_vanishing_canonical_add_boundary hK.1 X q D hq K B N hB D₀ m' 2 hm' two_pos hD₀ hNn hNb
    (fun C hC => by
      have e1 := GlobalTheory.T.intersectionNumber_curve_of_class_eq_smul_add ℂ X q hq B N N' hB hN hN' m 1 C hC (by rw [hBc, one_smul])
      have e2 := GlobalTheory.T.intersectionNumber_curve_of_class_eq_smul_add ℂ X q hq N₀ N N' h₀ hN hN' (2 * m - 1) 2 C hC hc₀
      have e3 := hcur C hC
      rw [e3, e1, e2]
      have : ((2 * m - 1 : ℕ) : ℚ) = 2 * m - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      push_cast [this]
      ring)
  exact GlobalTheory.T.exists_section_nonvanishing_point ℂ X q hq (tens K.bundle B) (isLB_tens K.isLB hB) J x U hx hxU
    (fun y hy => by
      rw [hJ]
      constructor
      · intro h
        by_contra hne
        exact h (hklt y hy hne)
      · rintro rfl
        exact hnk) (hvan 1 one_pos)

theorem effective_generation : GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.NefNumerics → ∀ (F : Type) [Field F] [NumberField F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (D : ℕ) [SmoothOfRelativeDimension D p], IsProjOver p → GeometricallyConnected p → 1 ≤ D → letI := algebraΓOfHom p; ∀ (K : CanonLB p D) (N N' B : LB Y) (hN : N.IsLB) (hN' : N'.IsLB) (hB : B.IsLB) (a m : ℕ) (y : Y), IsNef F N → IsNef F N' → (D + 1).choose 2 < m → (∃ (N₁ N₂ : LB Y) (h₁ : N₁.IsLB) (h₂ : N₂.IsLB), 0 < a ∧ a • cls N hN = cls N₁ h₁ + cls N₂ h₂ ∧ AmpleAt N₁ y ∧ IsNef F N₂) → cls B hB = m • cls N hN + cls N' hN' → ∃ s : (tens K.bundle B).Sec, y ∈ nonzeroLocus s := by
  intro hK hNN F _ _ Y p D _ hproj hgc hD1
  letI := algebraΓOfHom p
  intro K N N' B hN hN' hB a m y hNn hN'n hm hdec hBc
  obtain ⟨N₁, N₂, h₁, h₂, ha, hcls, hamp, hN₂⟩ := hdec
  haveI : Algebra.IsAlgebraic ℚ F := Algebra.IsAlgebraic.of_finite ℚ F
  let σ : F →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := F)).toRingHom
  letI : Algebra F ℂ := σ.toAlgebra
  let π := pullback.fst p (spMap (algebraMap F ℂ))
  let q := pullback.snd p (spMap (algebraMap F ℂ))
  have H : IsPullback π q p (spMap (algebraMap F ℂ)) := IsPullback.of_hasPullback _ _
  obtain ⟨hXi, hXn, hsm, hqp, hsurj⟩ := GlobalTheory.T.baseChange_smooth_projective_variety_properties F ℂ Y _ p q π D H hproj hgc
  haveI := hXi; haveI := hXn; haveI := hsm
  letI := algebraΓOfHom q
  haveI : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  obtain ⟨y', rfl⟩ := hsurj y
  haveI : Smooth q := SmoothOfRelativeDimension.smooth D q
  obtain ⟨m₁, A, s₁, hm₁, hA, hAa, hy⟩ := hamp
  obtain ⟨x, hxc, hyx, hxU⟩ := GlobalTheory.T.exists_closedPoint_specializes_in_open_of_finiteType ℂ _ q (π ⁻¹ᵁ nonzeroLocus s₁) y' hy
  have hAx : AmpleAt (N₁.pull π) x := GlobalTheory.T.ampleModuloEffectiveAwayFromPoint_pull_affine Y _ π N₁ h₁ x ⟨m₁, A, s₁, hm₁, hA, hAa, hxU⟩
  have hNnC := GlobalTheory.T.isNefLineBundle_baseChange_field_extension hNN F ℂ Y _ p q π H hproj N hNn
  have hN'nC := GlobalTheory.T.isNefLineBundle_baseChange_field_extension hNN F ℂ Y _ p q π H hproj N' hN'n
  have hN₂C := GlobalTheory.T.isNefLineBundle_baseChange_field_extension hNN F ℂ Y _ p q π H hproj N₂ hN₂
  have hc : a • cls (N.pull π) (pull_isLB hN π) = cls (N₁.pull π) (pull_isLB h₁ π) + cls (N₂.pull π) (pull_isLB h₂ π) := by
    rw [cls_pull hN, cls_pull h₁, cls_pull h₂, ← map_nsmul, hcls, map_add (f := _)]
  have hbig := GlobalTheory.T.isBigLineBundle_of_smul_class_eq_ampleAt_add_nef hNN ℂ _ q hqp (N.pull π) (N₁.pull π) (N₂.pull π) _ _ _ a x hNnC ha hc hAx hN₂C
  have hpos := GlobalTheory.T.one_le_intersectionNumber_subvariety_through_positive hNN ℂ _ q hqp (N.pull π) (N₁.pull π) (N₂.pull π) _ _ _ a x hNnC ha hc hAx hN₂C
  have hcB : cls (B.pull π) (pull_isLB hB π) = m • cls (N.pull π) (pull_isLB hN π) + cls (N'.pull π) (pull_isLB hN' π) := by
    rw [cls_pull hB, cls_pull hN, cls_pull hN', hBc, map_add (f := _), map_nsmul]
  obtain ⟨s, hs⟩ := core_gen hK hNN _ q D hqp hD1 (CanonLB.baseChange H K) (N.pull π) (N'.pull π) (B.pull π)
    _ _ _ m x hxc hNnC hbig hN'nC hm hpos hcB
  exact GlobalTheory.T.exists_tensor_section_nonvanishing_of_baseChange F ℂ Y _ p q π H hproj K.bundle B K.isLB hB y' ⟨s, hyx.mem_open (nonzeroLocus s).isOpen hs⟩

end GlobalTheory.EffGen
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fockJets_origin_oppositeSignVacuum_conjPeriod : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (δ t0 : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) t0 → ∀ i : ℕ, i + 1 ≤ D.R.m → ∀ e0 : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS (.chi i D.R.m : Pair T)).rank (G.pT (.chi i D.R.m : Pair T)).rank → ℂ, Formalism.MainNotions.StandardLatticesGL3.oddE0 D D.host.ccK δ t0 _ _ e0 → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.chi i D.R.m)) (G.onT W.cart (.chi i D.R.m)) (N.latS (.chi i D.R.m) : Set _) (N.latT (.chi i D.R.m) : Set _) f → ∃ c : ℂˣ, ∀ k : FVar D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank →₀ ℕ, GlobalTheory.FunObj.fockIn W N.frC (.chi i D.R.m) f (MvPolynomial.monomial k 1) 0 = c * starRingEnd ℂ ((k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) e0) := by
  first | exact @GlobalTheory.FunObj.FockChi.fockIn_chi_zero | exact GlobalTheory.FunObj.FockChi.fockIn_chi_zero | (intros; apply GlobalTheory.FunObj.FockChi.fockIn_chi_zero <;> assumption)
end
