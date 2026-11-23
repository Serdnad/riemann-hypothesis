module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle061
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RefSum

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H}

theorem conjEmb_rt_of_not {τ : E →+* ℂ} (h : ¬ τ (H.rt : E) = H.rt0) :
    conjEmb τ (H.rt : E) = H.rt0 := by
  have hE : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
    simpa using this
  have hsq : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    rw [H.sqrt_neg_disc_sq, ← map_pow, hE]; simp
  have hneg : τ (H.rt : E) = -H.rt0 := (sq_eq_sq_iff_eq_or_eq_neg.1 hsq).resolve_left h
  have hre : H.rt0.re = 0 := by
    have h2 := H.sqrt_neg_disc_sq
    have hr := congrArg Complex.re h2
    have hi := congrArg Complex.im h2
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
      Complex.natCast_im] at hr hi
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    by_contra hne
    have him : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [him] at hr
    nlinarith [mul_self_nonneg H.rt0.re]
  show (starRingEnd ℂ) (τ (H.rt : E)) = H.rt0
  rw [hneg]
  apply Complex.ext <;> simp [hre]

theorem psi_or_conj (σ : E →+* ℂ) : (∃ τ : Psi H, σ = τ.1) ∨ ∃ τ : Psi H, σ = conjEmb τ.1 := by
  by_cases h : σ (H.rt : E) = H.rt0
  · exact Or.inl ⟨⟨σ, h⟩, rfl⟩
  · exact Or.inr ⟨⟨conjEmb σ, conjEmb_rt_of_not h⟩, (GlobalTheory.AllWt.conjEmb_conjEmb σ).symm⟩

theorem psi_nonempty : Nonempty (Psi H) := by
  have : 0 < Fintype.card (E →+* ℂ) := by
    rw [NumberField.Embeddings.card]; exact Module.finrank_pos
  obtain ⟨σ⟩ := Fintype.card_pos_iff.1 this
  rcases psi_or_conj (H := H) σ with ⟨τ, -⟩ | ⟨τ, -⟩ <;> exact ⟨τ⟩

theorem sum_mult : ∑ τ : E →+* ℂ, Dw.mult τ = (Module.finrank ℚ E / 2) * (Dw.p + Dw.q) := by
  classical
  set P := (Finset.univ : Finset (E →+* ℂ)).filter (fun τ => τ (H.rt : E) = H.rt0) with hP
  set Q := (Finset.univ : Finset (E →+* ℂ)).filter (fun τ => ¬ τ (H.rt : E) = H.rt0) with hQ
  have hcard : Q.card = P.card := by
    refine Finset.card_nbij' conjEmb conjEmb ?_ ?_ ?_ ?_
    · intro a ha
      simp only [hQ, hP, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢
      exact conjEmb_rt_of_not ha
    · intro a ha
      simp only [hQ, hP, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢
      exact GlobalTheory.AllWt.conj_not_mem ⟨a, ha⟩
    · intro a _; exact GlobalTheory.AllWt.conjEmb_conjEmb a
    · intro a _; exact GlobalTheory.AllWt.conjEmb_conjEmb a
  have htot : P.card + Q.card = Module.finrank ℚ E := by
    rw [← NumberField.Embeddings.card E ℂ, ← Finset.card_univ]
    exact Finset.card_filter_add_card_filter_not _
  have hsum : ∑ τ : E →+* ℂ, Dw.mult τ = P.card * Dw.p + Q.card * Dw.q := by
    simp only [Datum.mult]
    rw [Finset.sum_ite]
    simp [Finset.sum_const, hP, hQ]
  rw [hsum, hcard, ← htot, hcard, ← two_mul, Nat.mul_div_cancel_left _ (by norm_num)]
  ring


variable (Dw) in
abbrev thExpZ (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) : (E →+* ℂ) × ℕ → ℤ :=
  (GlobalTheory.AllWt.wtOf Dw (u + GlobalTheory.FlatLine.parWt Dw (shift Dw u n)) ((n / 2 : ℕ) : ℤ)).1

theorem thExpZ_big (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) (τ : Psi H) (i : ℕ) (hi : i < Dw.p) :
    thExpZ Dw u n (τ.1, i) = u τ ⟨i, by omega⟩ + 1 - u τ ⟨Dw.p - 1, by omega⟩ := by
  rw [thExpZ, GlobalTheory.AllWt.wtOf_big _ _ τ i hi]
  simp only [Pi.add_apply, GlobalTheory.FlatLine.parWt, shift, dif_pos (show 0 < Dw.p by omega)]
  ring

theorem thExpZ_big_ge (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) (τ : Psi H) (i : ℕ) (hi : Dw.p ≤ i) :
    thExpZ Dw u n (τ.1, i) = 0 := by
  simp only [thExpZ, GlobalTheory.AllWt.wtOf, dif_pos τ.2, dif_neg (not_lt.2 hi)]

theorem thExpZ_small (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) (hp : 0 < Dw.p) (τ : Psi H) (i : ℕ) (hi : i < Dw.q) :
    thExpZ Dw u n (conjEmb τ.1, i) =
      u τ ⟨Dw.p - 1, by omega⟩ - u τ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ - 2 * ((n / 2 : ℕ) : ℤ) - 1 := by
  rw [thExpZ, GlobalTheory.AllWt.wtOf_small _ _ τ i hi]
  simp only [Pi.add_apply, GlobalTheory.FlatLine.parWt, shift, dif_pos hp]
  ring

theorem thExpZ_small_ge (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) (τ : Psi H) (i : ℕ) (hi : Dw.q ≤ i) :
    thExpZ Dw u n (conjEmb τ.1, i) = 0 := by
  have h' : conjEmb (conjEmb τ.1) (H.rt : E) = H.rt0 := by
    rw [GlobalTheory.AllWt.conjEmb_conjEmb]; exact τ.2
  simp only [thExpZ, GlobalTheory.AllWt.wtOf, dif_neg (GlobalTheory.AllWt.conj_not_mem τ), dif_pos h', dif_neg (not_lt.2 hi)]

theorem thA_dominant_lastPos_degree (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) (b : ℝ) (hp : 1 ≤ Dw.p)
    (hn : Even n) (hu : ∀ τ, Antitone (u τ))
    (hgap : ∀ τ (i j : Fin (Dw.p + Dw.q)), (i : ℕ) + 1 = Dw.p → (j : ℕ) = Dw.p → (n : ℤ) + 1 ≤ u τ i - u τ j)
    (hb : ∀ τ i, |(u τ i : ℝ)| ≤ b) :
    Formalism.L2.Pj.Dom (thA Dw u n) n ∧
      Formalism.L2.Pj.wtZ (thA Dw u n) n =
        GlobalTheory.AllWt.wtOf Dw (u + GlobalTheory.FlatLine.parWt Dw (shift Dw u n)) ((n / 2 : ℕ) : ℤ) ∧
      Formalism.L2.Pj.LastPos Dw (thA Dw u n) ∧ (∀ x, (thA Dw u n x : ℝ) ≤ 2 * b + 1) ∧
      (Formalism.L2.Pj.DF Dw (thA Dw u n) : ℝ) ≤ (Module.finrank ℚ E / 2 : ℕ) * (Dw.p + Dw.q : ℕ) * (2 * b + 1) := by
  have hp0 : 0 < Dw.p := hp
  obtain ⟨τ0⟩ := psi_nonempty (H := H)
  have hb0 : 0 ≤ b := (abs_nonneg _).trans (hb τ0 ⟨0, by omega⟩)
  have hup : ∀ τ i, (u τ i : ℝ) ≤ b := fun τ i => (le_abs_self _).trans (hb τ i)
  have hlo : ∀ τ i, -b ≤ (u τ i : ℝ) := fun τ i => by
    have := neg_abs_le (u τ i : ℝ); linarith [hb τ i]
  have hm : 2 * ((n / 2 : ℕ) : ℤ) = n := by obtain ⟨k, rfl⟩ := hn; omega

  have F1 : ∀ x, 0 ≤ thExpZ Dw u n x := by
    rintro ⟨σ, i⟩
    rcases psi_or_conj (H := H) σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
    · by_cases hi : i < Dw.p
      · rw [thExpZ_big u n τ i hi]
        have := hu τ (show (⟨i, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨Dw.p - 1, by omega⟩ from Fin.mk_le_mk.2 (by omega))
        omega
      · rw [thExpZ_big_ge u n τ i (by omega)]
    · by_cases hi : i < Dw.q
      · rw [thExpZ_small u n hp0 τ i hi]
        have h1 := hu τ (show (⟨Dw.p, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ from
          Fin.mk_le_mk.2 (by omega))
        have h2 := hgap τ ⟨Dw.p - 1, by omega⟩ ⟨Dw.p, by omega⟩ (by simp; omega) rfl
        omega
      · rw [thExpZ_small_ge u n τ i (by omega)]

  have F2 : ∀ x, (thExpZ Dw u n x : ℝ) ≤ 2 * b + 1 := by
    rintro ⟨σ, i⟩
    rcases psi_or_conj (H := H) σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
    · by_cases hi : i < Dw.p
      · rw [thExpZ_big u n τ i hi]; push_cast
        linarith [hup τ ⟨i, by omega⟩, hlo τ ⟨Dw.p - 1, by omega⟩]
      · rw [thExpZ_big_ge u n τ i (by omega)]; push_cast; linarith
    · by_cases hi : i < Dw.q
      · rw [thExpZ_small u n hp0 τ i hi, hm]; push_cast
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
        linarith [hup τ ⟨Dw.p - 1, by omega⟩, hlo τ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩]
      · rw [thExpZ_small_ge u n τ i (by omega)]; push_cast; linarith

  have F3 : ∀ σ i, thExpZ Dw u n (σ, i + 1) ≤ thExpZ Dw u n (σ, i) := by
    intro σ i
    rcases psi_or_conj (H := H) σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
    · by_cases hi : i + 1 < Dw.p
      · rw [thExpZ_big u n τ _ hi, thExpZ_big u n τ i (by omega)]
        have := hu τ (show (⟨i, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨i + 1, by omega⟩ from Fin.mk_le_mk.2 (by omega))
        omega
      · rw [thExpZ_big_ge u n τ (i + 1) (by omega)]; exact F1 _
    · by_cases hi : i + 1 < Dw.q
      · rw [thExpZ_small u n hp0 τ _ hi, thExpZ_small u n hp0 τ i (by omega)]
        have := hu τ (show (⟨Dw.p + (Dw.q - 1 - (i + 1)), by omega⟩ : Fin (Dw.p + Dw.q)) ≤
          ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ from Fin.mk_le_mk.2 (by omega))
        omega
      · rw [thExpZ_small_ge u n τ (i + 1) (by omega)]; exact F1 _
  have hcast : ∀ x, (thA Dw u n x : ℝ) = (thExpZ Dw u n x : ℝ) := fun x => by
    have h := Int.toNat_of_nonneg (F1 x)
    show (((thExpZ Dw u n x).toNat : ℕ) : ℝ) = _
    rw [← h]; norm_cast
  have hbound : ∀ x, (thA Dw u n x : ℝ) ≤ 2 * b + 1 := fun x => (hcast x).trans_le (F2 x)
  refine ⟨⟨fun σ => antitone_nat_of_succ_le fun i => Int.toNat_le_toNat (F3 σ i), hn⟩, ?_, ?_, hbound, ?_⟩
  · refine Prod.ext (funext fun x => ?_) ?_
    · exact Int.toNat_of_nonneg (F1 x)
    · show (n : ℤ) = 2 * ((n / 2 : ℕ) : ℤ)
      omega
  · intro σ hσ _
    have hmul : Dw.mult σ = Dw.p := if_pos hσ
    rw [hmul]
    have h1 : thExpZ Dw u n (σ, Dw.p - 1) = 1 :=
      (thExpZ_big u n ⟨σ, hσ⟩ (Dw.p - 1) (by omega)).trans (by ring)
    show 0 < (thExpZ Dw u n (σ, Dw.p - 1)).toNat
    rw [h1]; decide
  · have hDF : (Formalism.L2.Pj.DF Dw (thA Dw u n) : ℝ) ≤ ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (2 * b + 1) := by
      unfold Formalism.L2.Pj.DF; push_cast
      refine Finset.sum_le_sum fun τ _ => ?_
      calc ∑ i : Fin (Dw.mult τ), (thA Dw u n (τ, i) : ℝ) ≤ ∑ _i : Fin (Dw.mult τ), (2 * b + 1) :=
            Finset.sum_le_sum fun i _ => hbound (τ, i)
        _ = _ := by simp [mul_add]
    rw [← Finset.sum_mul] at hDF
    have hs : (∑ τ : E →+* ℂ, (Dw.mult τ : ℝ)) =
        ((Module.finrank ℚ E / 2 : ℕ) : ℝ) * ((Dw.p + Dw.q : ℕ) : ℝ) := by
      rw [← Nat.cast_sum, sum_mult, Nat.cast_mul]
    rw [hs] at hDF
    exact hDF

end GlobalTheory.RefSum
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


noncomputable section

namespace GlobalTheory.CovTop.FlatSz

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem lrd_bounds {PP A M : ℝ} (hH : HostNum D L PP A M) :
    0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E ∧ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E ≤ 2 * L.sc.L := by
  have hne : (discr D.host.E : ℝ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero D.host.E
  have h1 : (1 : ℝ) ≤ |(discr D.host.E : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero D.host.E)
  have hlog0 : 0 ≤ Real.log |(discr D.host.E : ℝ)| := Real.log_nonneg h1
  have hf : (0 : ℝ) < D.R.f := by have := hH.f8; positivity
  have heq : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E = Real.log |(discr D.host.E : ℝ)| / (2 * D.R.f) := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd, NumberField.rootDiscr_def, Int.cast_abs, Real.log_rpow (abs_pos.2 hne), hH.deg]
    push_cast
    ring
  rw [heq]
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hH.disc]

theorem abs_flatDegVal_le (p : PtAt ex Csz) (i : Fin D.R.m) {PP A M : ℝ} (hH : HostNum D L PP A M) (hW : WtNum p i PP) :
    |GlobalTheory.FlatLine.flatDegVal (dat p i) (Formalism.L2.DIV.ofRecord D L p.Del p.h0).logOm| ≤ 9 * D.R.r * L.sc.L := by
  have hd : p.T.Q.H.d = D.host.d := p.fw.laws.pins.1.1
  have hpq : ((dat p i).p : ℝ) + (dat p i).q = D.R.r := by exact_mod_cast hW.sig.2.2
  have hom := hW.om
  have hL : 10 ≤ L.sc.L := hH.big.2.1
  have hld : Real.log (p.T.Q.H.d : ℝ) ≤ L.sc.L := by rw [hd]; exact hH.logd
  have hld0 : 0 ≤ Real.log (p.T.Q.H.d : ℝ) := Real.log_natCast_nonneg _
  obtain ⟨hr0, hr1⟩ := lrd_bounds hH
  unfold GlobalTheory.FlatLine.flatDegVal
  set a := (Formalism.L2.DIV.ofRecord D L p.Del p.h0).logOm
  set P : ℝ := ((dat p i).p : ℝ)
  set Q : ℝ := ((dat p i).q : ℝ)
  set u := Real.log (p.T.Q.H.d : ℝ)
  set v := GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E
  have hP : 0 ≤ P := Nat.cast_nonneg _
  have hQ : 0 ≤ Q := Nat.cast_nonneg _
  have h1 : |(P - Q) / 2 * a| ≤ (P + Q) / 2 * (3 * L.sc.L) := by
    rw [abs_mul, abs_div, abs_two]
    refine mul_le_mul ?_ hom (abs_nonneg _) (by positivity)
    gcongr
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have h2 : |Q * (u - v)| ≤ Q * (2 * L.sc.L) := by
    rw [abs_mul, abs_of_nonneg hQ]
    exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith, by linarith⟩) hQ
  have h3 := abs_add_le ((P - Q) / 2 * a) (Q * (u - v))
  rw [hpq] at h1
  have hQr : Q ≤ D.R.r := by rw [← hpq]; linarith
  have hr : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hQr (by linarith : (0 : ℝ) ≤ 2 * L.sc.L), mul_nonneg hr (by linarith : (0 : ℝ) ≤ L.sc.L)]

end GlobalTheory.CovTop.FlatSz

namespace GlobalTheory.CovTop.FlatSz

end GlobalTheory.CovTop.FlatSz

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

noncomputable section

namespace GlobalTheory.CovTop.CovSz

theorem ceil_mul_le_pow {y PP Dd k m : ℝ} (hy : 2 ≤ y) (hP0 : 0 ≤ PP) (hP : PP ≤ y) (hD0 : 0 ≤ Dd) (hD : Dd ≤ y ^ 2)
    (hk0 : 0 ≤ k) (hk : k ≤ y) (hm : 1 ≤ m) : (⌈PP ^ 2 * Dd ^ 2 * k / m⌉₊ : ℝ) * PP ≤ y ^ 9 := by
  have h0 : 0 ≤ PP ^ 2 * Dd ^ 2 * k := by positivity
  have h1 : PP ^ 2 * Dd ^ 2 * k ≤ y ^ 7 := by
    calc PP ^ 2 * Dd ^ 2 * k ≤ y ^ 2 * (y ^ 2) ^ 2 * y := by gcongr
      _ = y ^ 7 := by ring
  have h2 : PP ^ 2 * Dd ^ 2 * k / m ≤ y ^ 7 := (div_le_self h0 hm).trans h1
  have h3 : (⌈PP ^ 2 * Dd ^ 2 * k / m⌉₊ : ℝ) < PP ^ 2 * Dd ^ 2 * k / m + 1 :=
    Nat.ceil_lt_add_one (div_nonneg h0 (by linarith))
  have h4 : 1 ≤ y ^ 7 := one_le_pow₀ (by linarith)
  have h5 : (⌈PP ^ 2 * Dd ^ 2 * k / m⌉₊ : ℝ) ≤ y ^ 8 := by
    have : y ^ 8 = y ^ 7 * y := by ring
    nlinarith
  calc (⌈PP ^ 2 * Dd ^ 2 * k / m⌉₊ : ℝ) * PP ≤ y ^ 8 * y := by gcongr
    _ = y ^ 9 := by ring

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem kap_le {PP : ℝ} (hW : WtNum p i PP) : CovTop.kap p i ≤ (D.R.f : ℝ) * D.R.r * (4 * L.sc.b) := by
  have hc : (Fintype.card (Psi p.T.Q.H) : ℝ) = D.R.f := by
    rw [← hW.card, Nat.card_eq_fintype_card]
  have hr : (((dat p i).p + (dat p i).q : ℕ) : ℝ) = D.R.r := by rw [hW.sig.2.2]
  unfold CovTop.kap sizeK
  calc _ ≤ ∑ _τ : Psi p.T.Q.H, ∑ _k : Fin ((dat p i).p + (dat p i).q), 4 * L.sc.b :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun k _ => hW.up τ k
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [hc, hr]; ring

theorem kapT_at {PP A : ℝ} (hH : HostNum D L PP A 18) (hW : WtNum p i PP) :
    Real.log (CovTop.kap p i) ≤ 2 * L.sc.L ∧ (lenT p i PP : ℝ) * PP ≤ Real.sqrt L.sc.b := by
  obtain ⟨-, hL, -, -⟩ := hH.big
  obtain ⟨-, hPy, hfy⟩ := hH.poly
  have hroom := hH.room
  have hlow := hH.ppLow
  set y := L.sc.x ^ A with hy
  have hroom' : y ^ 18 ≤ L.sc.b := by
    have : y ^ (18 : ℝ) = y ^ (18 : ℕ) := by exact_mod_cast Real.rpow_natCast y 18
    rwa [this] at hroom
  have hm2 := D.R.two_le_m
  have hkm := D.R.m_add_three_le_k
  have hkr : D.R.k ≤ D.R.r := by unfold Ranks.r; omega
  have hr1 : 1 ≤ D.R.r := by omega
  have hn1 : 1 ≤ D.R.nV := by unfold Ranks.nV; omega
  have hf8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hH.f8
  have hr1' : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr1
  have hn1' : (1 : ℝ) ≤ D.R.nV := by exact_mod_cast hn1
  have hkr' : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast hkr
  have hm' : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hfr : (8 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
  have h10 : (D.R.f : ℝ) * D.R.r * 10 ≤ y := by
    refine le_trans ?_ hfy
    calc (D.R.f : ℝ) * D.R.r * 10 = (D.R.f : ℝ) * D.R.r * 1 * 10 := by ring
      _ ≤ _ := by gcongr
  have hy2 : 2 ≤ y := by linarith
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  have hyb : y ≤ L.sc.b := (le_self_pow₀ (by linarith) (by norm_num)).trans hroom'
  have hP0 : 0 ≤ PP := le_trans (Even.pow_nonneg (by decide) _) hlow
  refine ⟨?_, ?_⟩
  · have hk := kap_le p i hW
    have hk0 : 0 ≤ CovTop.kap p i :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hk2 : CovTop.kap p i ≤ Real.exp (2 * L.sc.L) := by
      have e : Real.exp (2 * L.sc.L) = L.sc.b * L.sc.b := by
        unfold Scale.b; rw [← Real.exp_add]; ring_nf
      rw [e]
      nlinarith
    rcases hk0.eq_or_lt with h | h
    · rw [← h, Real.log_zero]; linarith
    · exact (Real.log_le_iff_le_exp h).2 hk2
  · have hch : (D.R.r.choose 2 : ℝ) ≤ (D.R.r : ℝ) ^ 2 := by exact_mod_cast Nat.choose_le_pow D.R.r 2
    have hD : (CompHt.dimFlag (dat p i) : ℝ) ≤ y ^ 2 := by
      rw [hW.dim]; push_cast
      calc (D.R.f : ℝ) * (D.R.r.choose 2 : ℝ) ≤ (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 2 := by
            gcongr; nlinarith
        _ = ((D.R.f : ℝ) * D.R.r) ^ 2 := by ring
        _ ≤ y ^ 2 := by gcongr; linarith
    have hky : (D.R.k : ℝ) ≤ y := by nlinarith
    have h9 := ceil_mul_le_pow hy2 hP0 hPy (Nat.cast_nonneg _) hD (Nat.cast_nonneg _) hky hm'
    refine h9.trans (Real.le_sqrt_of_sq_le ?_)
    calc (y ^ 9) ^ 2 = y ^ 18 := by ring
      _ ≤ _ := hroom'

end Point

end GlobalTheory.CovTop.CovSz

end
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Discrepancy.DivOver

theorem exists_through_of_isProper : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → IsProper s → ∀ (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E → ∀ x : X, E.Through x → ∃ y : Y, s y = x ∧ E'.Through y := by
  intro k _ X Y _ _ p s _ _ hprop E' E hOver x hx
  haveI := hprop
  have hmem : ∀ a : X.presheaf.stalk x,
      functionFieldMap s (algebraMap _ X.functionField a) ∈ E'.ring :=
    fun a => (hOver _).1 (hx _ ⟨a, rfl⟩)
  let ψ : X.presheaf.stalk x →+* E'.ring :=
    ((functionFieldMap s).comp (algebraMap _ X.functionField)).codRestrict E'.ring.toSubring hmem
  have hc : genericFieldPoint Y ≫ s = specAlgebraMap E'.ring Y.functionField ≫
      (Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk x) := by
    rw [← specMap_functionFieldMap, ← specAlgebraMap_fromSpecStalk x]
    simp only [specAlgebraMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  obtain ⟨b, hb1, hb2⟩ := exists_valuativeExtension s _ (genericFieldPoint Y) hc
  have hdom : DominatesStalk E'.ring (b (IsLocalRing.closedPoint E'.ring)) :=
    dominatesStalk_iff_exists_hom.mpr ⟨b, hb1, rfl⟩
  have hw : E'.Through (b (IsLocalRing.closedPoint E'.ring)) := by
    rintro f ⟨c, rfl⟩
    exact hdom.1 c
  have hz : s (b (IsLocalRing.closedPoint E'.ring)) ⤳ x := by
    have e : s (b (IsLocalRing.closedPoint E'.ring)) = X.fromSpecStalk x
        (Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint E'.ring)) := by
      have := congrArg (fun l : Spec (CommRingCat.of E'.ring) ⟶ X =>
        l (IsLocalRing.closedPoint E'.ring)) hb2
      exact this
    rw [e]
    have := (IsLocalRing.specializes_closedPoint
      (Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint E'.ring))).map
        (X.fromSpecStalk x).continuous
    rwa [Scheme.fromSpecStalk_closedPoint] at this
  obtain ⟨y, hwy, hy⟩ := s.isClosedMap.specializingMap hz
  exact ⟨y, hy, hw.of_specializes hwy⟩

end GlobalTheory.Discrepancy.DivOver
end
end
