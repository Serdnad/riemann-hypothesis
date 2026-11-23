module

public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle030
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PowExponentPartMemGaugedCurveLogarithms
public import Formalism.LocalToGlobal.CharacterGerms.RowTieFB
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle061
public import Formalism.LocalToGlobal.CharacterGerms.CharacteristicFromRanks
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle049
public import Formalism.LocalToGlobal.CharacterGerms.Bundle023
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle004
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle033
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle062
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.InvariantDerivationsConstantInLogCoordinates
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001

@[expose] public section

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowKernel

variable {C : Type} [Field C] {V : VF C}

theorem mm_zero : V.MM (0 : C) := by simp [VF.MM]

theorem mm_sum {ι : Type} {s : Finset ι} {f : ι → C} (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) :=
  V.v.map_lt_sum (by simp) h

theorem mm_int_mul {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  unfold VF.MM; rw [V.v.map_mul]
  have ha' : (0 : WithTop ℝ) ≤ V.v a := ha
  exact lt_of_lt_of_le hb (le_add_of_nonneg_left ha')

theorem mm_mul_int {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  rw [mul_comm]; exact mm_int_mul hb ha

theorem mm_ge {a : C} (h : V.MM a) : V.Ge 0 a := le_of_lt h

theorem not_mm_one : ¬ V.MM (1 : C) := by simp [VF.MM]

theorem ge_of_pow {a : C} {n : ℕ} (hn : n ≠ 0) (h : V.Ge 0 (a ^ n)) : V.Ge 0 a := by
  have h' : (0 : WithTop ℝ) ≤ V.v (a ^ n) := h
  show (0 : WithTop ℝ) ≤ V.v a
  rw [V.v.map_pow] at h'
  by_contra hc
  exact absurd (nsmul_neg (not_le.mp hc) hn) (not_lt.mpr h')

theorem ge_div {a b : C} (hb : b ≠ 0) (h : V.v b ≤ V.v a) : V.Ge 0 (a / b) := by
  show (0 : WithTop ℝ) ≤ V.v (a / b)
  have e : V.v a = V.v (a / b) + V.v b := by rw [← V.v.map_mul, div_mul_cancel₀ a hb]
  have hb' : V.v b ≠ ⊤ := by simpa using hb
  rw [e] at h
  exact (WithTop.add_le_add_iff_right hb').mp (by simpa using h)

theorem card_add_le {σ : Type} [Fintype σ] (p : σ → Prop) [DecidablePred p] {N M : ℕ}
    (A : Fin N → σ → C) (B : Fin M → σ → C) (hA : IndepMod V A) (hAp : ∀ ν s, ¬ p s → A ν s = 0)
    (hB : IsSat V B) (hBp : ∀ μ s, ¬ p s → B μ s = 0) (hAB : ∀ ν μ, V.MM (∑ s, A ν s * B μ s)) :
    N + M ≤ (Finset.univ.filter p).card := by
  classical
  obtain ⟨-, W, hW, hBW⟩ := hB
  let F : Fin N ⊕ Fin M → {s // p s} → C := Sum.elim (fun ν s => A ν s.1) (fun μ s => W s.1 μ)
  have hF : LinearIndependent C F := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 : ∀ s, p s → ∑ ν, g (Sum.inl ν) * A ν s + ∑ μ, g (Sum.inr μ) * W s μ = 0 := by
      intro s hs
      have := congrFun hg ⟨s, hs⟩
      simpa [F, Fintype.sum_sum_type, Finset.sum_apply] using this
    have h2 : ∀ μ', g (Sum.inr μ') = -∑ ν, g (Sum.inl ν) * ∑ s, A ν s * B μ' s := by
      intro μ'
      have h3 : ∑ s, (∑ ν, g (Sum.inl ν) * A ν s + ∑ μ, g (Sum.inr μ) * W s μ) * B μ' s = 0 :=
        Finset.sum_eq_zero fun s _ => by
          by_cases hs : p s
          · rw [h1 s hs, zero_mul]
          · rw [hBp μ' s hs, mul_zero]
      have h4 : ∑ s, (∑ μ, g (Sum.inr μ) * W s μ) * B μ' s = g (Sum.inr μ') := by
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        have : ∀ μ, ∑ s, g (Sum.inr μ) * W s μ * B μ' s = g (Sum.inr μ) * if μ' = μ then 1 else 0 := by
          intro μ
          rw [← hBW μ' μ, Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => by ring
        simp [this]
      have h5 : ∑ s, (∑ ν, g (Sum.inl ν) * A ν s) * B μ' s = ∑ ν, g (Sum.inl ν) * ∑ s, A ν s * B μ' s := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun s _ => by ring
      simp only [add_mul, Finset.sum_add_distrib] at h3
      rw [h4, h5] at h3
      linear_combination h3
    have h6 : ∀ ν, g (Sum.inl ν) = 0 := by
      by_contra hc
      push_neg at hc
      obtain ⟨ν1, hν1⟩ := hc
      obtain ⟨ν0, -, hmin⟩ := Finset.exists_min_image Finset.univ (fun ν => V.v (g (Sum.inl ν)))
        ⟨ν1, Finset.mem_univ _⟩
      have h0 : g (Sum.inl ν0) ≠ 0 := by
        intro h0
        have := hmin ν1 (Finset.mem_univ _)
        rw [h0, V.v.map_zero, top_le_iff] at this
        exact hν1 (by simpa using this)
      have hint : ∀ ν, V.Ge 0 (g (Sum.inl ν) / g (Sum.inl ν0)) := fun ν =>
        ge_div h0 (hmin ν (Finset.mem_univ _))
      have key := hA (fun ν => g (Sum.inl ν) / g (Sum.inl ν0)) hint (fun s => by
        by_cases hs : p s
        · have e : ∑ ν, g (Sum.inl ν) / g (Sum.inl ν0) * A ν s =
              ∑ μ, (∑ ν, g (Sum.inl ν) / g (Sum.inl ν0) * ∑ s, A ν s * B μ s) * W s μ := by
            have e1 : ∑ ν, g (Sum.inl ν) / g (Sum.inl ν0) * A ν s =
                (g (Sum.inl ν0))⁻¹ * ∑ ν, g (Sum.inl ν) * A ν s := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun ν _ => by ring
            have e2 : ∀ μ, (∑ ν, g (Sum.inl ν) / g (Sum.inl ν0) * ∑ s, A ν s * B μ s) =
                -((g (Sum.inl ν0))⁻¹ * g (Sum.inr μ)) := by
              intro μ
              rw [h2 μ, mul_neg, neg_neg, Finset.mul_sum]
              exact Finset.sum_congr rfl fun ν _ => by ring
            have e3 : ∑ μ, -((g (Sum.inl ν0))⁻¹ * g (Sum.inr μ)) * W s μ =
                -((g (Sum.inl ν0))⁻¹ * ∑ μ, g (Sum.inr μ) * W s μ) := by
              rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
              exact Finset.sum_congr rfl fun ν _ => by ring
            simp only [e2]
            rw [e1, e3]
            linear_combination (g (Sum.inl ν0))⁻¹ * h1 s hs
          rw [e]
          exact mm_sum fun μ _ => mm_mul_int (mm_sum fun ν _ => mm_int_mul (hint ν) (hAB ν μ)) (hW s μ)
        · simp only [hAp _ s hs, mul_zero, Finset.sum_const_zero]
          exact mm_zero) ν0
      simp only [div_self h0] at key
      exact not_mm_one key
    intro i
    cases i with
    | inl ν => exact h6 ν
    | inr μ => rw [h2 μ]; simp [h6]
  have := hF.fintype_card_le_finrank
  simpa [Fintype.card_subtype] using this

theorem mm_pow {a : C} {n : ℕ} (hn : n ≠ 0) (h : V.MM a) : V.MM (a ^ n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [pow_succ]
  exact mm_int_mul ((mm_ge h).pow m) h

theorem independenceBoundCondition_of_rankMaximalCondition : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → X.RankHyp → ∀ H : ∀ g, X.CartHyp V g, RawChart.RankMaximalCondition H → RawChart.IndependenceBoundCondition H := by
  intro C _ V d _ I _ κ _ X hL hR H h2 hA g a ha N w x hgood hV hind
  classical
  haveI := hL.closed
  have hstep := CharacteristicFromRanks.alt_step X.big hR.big_compl hA
  have hb1 : X.big (1 - g) (a + 1) := (hR.big_compl g (a + 1)).2 fun h => (hstep g a).1 h ha
  have hb2 : ¬ X.big (1 - g) (a + 1 + 1) := fun h => (hstep (1 - g) (a + 1)).1 h hb1
  obtain ⟨M, w', x', hgood', hsupp, hsat, hcard⟩ :=
    GlobalTheory.T.exists_saturated_good_vectors_small_corank C V d (I (1 - g)) (JJ I (1 - g)) (RawChart.cart (H (1 - g))) (a + 1)
  have c1 := hR.rk_big (1 - g) (a + 1) hb1
  have c2 := hR.rk_small (1 - g) (a + 1 + 1) hb2
  have hl : V.l ≠ 0 := V.l_prime.ne_zero
  have hind' : IndepMod V (fun ν => (RawChart.cart (H g)).c0' (x ν)) := by
    intro c hc hmm
    choose co hco using fun ν => IsAlgClosed.exists_pow_nat_eq (c ν) (Nat.pos_of_ne_zero hl)
    have hcoi : ∀ ν, V.Ge 0 (co ν) := fun ν => ge_of_pow hl (by rw [hco]; exact hc ν)
    have hG := Cart.Good.comb Finset.univ (fun ν _ => hcoi ν) (fun ν _ => hgood ν)
    have h3 := h2 hA g a ha _ _ hG (fun q => by
      rw [Cart.c0'_comb]
      simp only [hco]
      exact hmm q)
    have h4 := hind co hcoi (fun k => by simpa [Finset.sum_apply] using h3 k)
    intro ν
    rw [← hco ν]
    exact mm_pow hl (h4 ν)
  have key := card_add_le (V := V) (fun c : I (1 - g) => X.ty (1 - g) c = a + 1)
    (fun ν => (RawChart.cart (H g)).c0' (x ν)) w' hind'
    (fun ν s hs => by
      have := (hgood ν).1.2.2 1 (Sum.inr s) (by simpa [RawChart.cart, RawChart.tyC] using hs)
      simp [Cart.c0', this])
    hsat (fun μ s hs => hsupp μ s hs)
    (fun ν μ => GlobalTheory.T.goodCurves_pairing_mem_maxIdeal C V d I κ X hL H g a (a + 1) (w ν) (x ν) (w' μ) (x' μ) (hgood ν) (hgood' μ) (hV ν))
  have hcard' : X.n + X.j ≤ M + X.j' := by
    rw [← c1, ← c2]
    convert hcard <;> rfl
  have key' : N + M ≤ X.n + X.j := by
    rw [← c1]
    convert key
  omega

end GlobalTheory.RowKernel
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.powExponentPart_mem_gaugedCurveLogarithms : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g, ∀ a ∈ Cv X V g, ((fun i => typ V.l (a.1 i), fun q => typ V.l (a.2 q)) : ((κ → PowerSeries C) × (JJ I g → PowerSeries C))) ∈ Cv X V g := by
  first | exact @GlobalTheory.RowLaw.typ_mem_Cv | exact GlobalTheory.RowLaw.typ_mem_Cv | (intros; apply GlobalTheory.RowLaw.typ_mem_Cv <;> assumption)
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.isIntegralGaugedFormalGroupLaw_pairData : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I), RLaw (Y.raw p) V := by
  first | exact @GlobalTheory.RowLawPair.rLaw_pairData | exact GlobalTheory.RowLawPair.rLaw_pairData | (intros; apply GlobalTheory.RowLawPair.rLaw_pairData <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.colength_bound_split_place_linear_data : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (d r m : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (s : Fin m → Fin d → O), LinDat H A B ρG N s → ∀ (w : Place p OE) (t : Fin w.n ≃ Emb (O := O) w.e) (vd : ℝ), HasVd p v w t vd → ∀ (rp rm : ℕ) (W : Fin w.n → Fin rp → Fin d → O), (∀ j, EigB ρG ((t j : Emb (O := O) w.e) : OE →+* O) (W j)) → (∀ τ ∈ Emb (O := O) w.bar, ∃ W' : Fin rm → Fin d → O, EigB ρG τ W') → ∃ xs : Fin w.n → NNReal, (∀ j, HasLen v O ((Fin rp → O) ⧸ Submodule.span O (Set.range fun k => Pdiv.ChartF.res (W j) (s k))) (xs j)) ∧ v (algebraMap O C (p : O)) ^ ((w.n : ℝ) * rm * (1 / ((p : ℝ) - 1) + vd / 2)) ≤ ∏ j, xs j := by
  first | exact @GlobalTheory.ChF.colength_bound_linDat | exact GlobalTheory.ChF.colength_bound_linDat | (intros; apply GlobalTheory.ChF.colength_bound_linDat <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torus_point_relation_succ_thickening : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegData R I) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D A G) (k : ℕ) (S : Type) [CommRing S] [Algebra R S] χ z, IRel (U.gt k) S χ z → IRel (U.gt (k + 1)) S χ z := by
  first | exact @GlobalTheory.ChF.iRel_succ | exact GlobalTheory.ChF.iRel_succ | (intros; apply GlobalTheory.ChF.iRel_succ <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

theorem exists_linDat_of_extSer : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [StarRing OE] (d g r : ℕ) (F : FGLaw O d) (FB : FGLaw O g) (J : Fin d → PS O 1 r) (Q : Fin g → PS O 1 d), ExtSer F.F FB.F J Q → FH p F.F → ∀ (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (αB : OE → Fin g → PS O 1 g), (∀ a, lin Q * ρG a = lin (αB a) * lin Q) → (∀ a, ρG a * lin J = lin J * (N a).map (Int.castRingHom O)) → (∃ (cp : O) (_ : HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (S : Matrix (Fin g) (Fin g) O), H.P = 0 ∧ H.PL = 0 ∧ IsUnit S ∧ (∀ a : OE, lin (αB a) * S = S * H.ρL (1 ⊗ₜ[ℤ] a)) ∧ ∀ i, ∃ u : PS O 1 g, IsCh FB.F u ∧ Sᵀ *ᵥ dl u = fun l => H.Ht l i) → ∃ (cp : O) (_ : HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (B : Matrix (Fin g) (Fin d) O) (m : ℕ) (u : Fin m → PS O 1 d), (∀ k, IsCh F.F (u k)) ∧ LinDat H (lin J) B ρG N (fun k => dl (u k)) := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ d g r F FB J Q hE hFH ρG N αB hB hA ⟨cp, hU, H, S, hP, hPL, hS, hα, hu⟩
  classical
  obtain ⟨h0, A', B', hA', hB', hAB⟩ := hE.exact
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hS
  have hS1 : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hdet
  have hS2 : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hdet
  choose u1 hu1 hu1' using hu
  choose u2 hu2 hu2' using GlobalTheory.T.exists_formalTorus_character_lift_to_law p C v O hv d r F hFH J A' hE.homI hA'
  obtain ⟨hc1, -, hc3⟩ := GlobalTheory.T.formalSeriesJacobian_chain_rule_linearPart O d g Q hE.homQ.1
  let w : (Fin g ⊕ Fin g) ⊕ Fin r → PS O 1 d := Sum.elim (fun i => sub ![Q] (u1 i)) u2
  let e := Fintype.equivFin ((Fin g ⊕ Fin g) ⊕ Fin r)
  refine ⟨cp, hU, H, S⁻¹ * lin Q, _, fun k => w (e.symm k), ?_, ⟨hP, hPL⟩, ⟨?_, A', B' * S, hA', ?_, ?_⟩,
    ?_, hA, ?_, ?_⟩
  · intro k
    show IsCh F.F (w (e.symm k))
    rcases e.symm k with i | i
    · exact hc3 F FB hE.homQ _ (hu1 i)
    · exact hu2 i
  · rw [Matrix.mul_assoc, h0, Matrix.mul_zero]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (lin Q), hB', Matrix.one_mul, hS1]
  · rw [Matrix.mul_assoc B', ← Matrix.mul_assoc S, hS2, Matrix.one_mul, hAB]
  · intro a
    have h : S⁻¹ * lin (αB a) = H.ρL (1 ⊗ₜ[ℤ] a) * S⁻¹ := by
      calc S⁻¹ * lin (αB a) = S⁻¹ * (lin (αB a) * S) * S⁻¹ := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, hS2, Matrix.mul_one]
        _ = _ := by rw [hα a, ← Matrix.mul_assoc, hS1, Matrix.one_mul]
    rw [Matrix.mul_assoc, hB a, ← Matrix.mul_assoc, h, Matrix.mul_assoc]
  · intro i
    refine ⟨e (Sum.inl i), ?_⟩
    simp only [Equiv.symm_apply_apply, w, Sum.elim_inl]
    rw [(hc1 _).1, ← hu1' i, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Matrix.mul_assoc, hS2,
      Matrix.one_mul]
  · intro i
    refine ⟨e (Sum.inr i), ?_⟩
    simp only [Equiv.symm_apply_apply, w, Sum.elim_inr]
    exact hu2' i

end GlobalTheory.ChF
end

section

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.L2.FormalSeriesBounds NumberField

namespace GlobalTheory.LabelledDirections

theorem ge_zero_of_isIntegral {C : Type} [Field C] (V : VF C) {x : C} (hx : IsIntegral ℤ x) : V.Ge 0 x := by
  let A : ValuationSubring C :=
    { VF.RR V with
      mem_or_inv_mem' := by
        intro z
        by_cases hz : z = 0
        · left; rw [hz]; exact VF.Ge.zero 0
        · by_contra hc
          push Not at hc
          obtain ⟨h1, h2⟩ := hc
          have h1' : V.v z < 0 := lt_of_not_ge h1
          have h2' : V.v z⁻¹ < 0 := lt_of_not_ge h2
          have h3 : V.v (z * z⁻¹) = 0 := by rw [mul_inv_cancel₀ hz]; simp
          rw [V.v.map_mul] at h3
          have h4 : V.v z + V.v z⁻¹ ≤ V.v z + 0 := add_le_add le_rfl h2'.le
          rw [h3, add_zero] at h4
          exact absurd h1' (not_lt.2 h4) }
  have h : IsIntegral A x := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (K := C) h
  rw [← hy]
  exact y.2

theorem exists_dual {R : Type} [CommRing R] {d m : ℕ} (w : Fin d → Fin d → R) (emb : Fin m ↪ Fin d)
    (hw : ∀ v : Fin d → R, ∃! a : Fin d → R, ∀ j, ∑ k, a k * w k j = v j) :
    ∃ W : Fin d → Fin m → R, ∀ i i', ∑ s, w (emb i) s * W s i' = if i = i' then 1 else 0 := by
  classical
  let U : Matrix (Fin d) (Fin d) R := Matrix.of w
  let W : Matrix (Fin d) (Fin d) R := Matrix.of fun t => (hw (Pi.single t 1)).exists.choose
  have hWU : W * U = 1 := by
    ext t s
    have := (hw (Pi.single t 1)).exists.choose_spec s
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [W, U, Matrix.of_apply]
    rw [this, Pi.single_apply]
    simp [eq_comm]
  have hUW : U * W = 1 := mul_eq_one_comm.1 hWU
  refine ⟨fun s i' => W s (emb i'), fun i i' => ?_⟩
  have := congrFun (congrFun hUW (emb i)) (emb i')
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  simpa [U] using this

theorem labGeoSt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], Formalism.L2.FormalSeriesBounds.LabGeoSt Xo c := by
  intro E _ _ _ H Dw l Xo c _ hs T io y C3 C _ _ V ι hι k Y hY Orb d _ lab ha
  classical
  letI := io.toAlgebra
  have hval : ∀ x : T.V, V.Ge 0 (ι (algebraMap T.V T.Fr x)) :=
    (GlobalTheory.nval_eq_of_extension T C V.v V.l V.l_prime.ne_zero V.v_l ι hι).1
  have huv : ∀ ℓ i, chartUnitVectors C3 ℓ i = algebraMap T.V T.Fr (C3.uvecT ℓ i) := fun ℓ i =>
    C3.gen.1.2.2.2.2.2.2 ℓ i
  have hint : ∀ (τ : E →+* ℂ) (x : 𝓞 E), V.Ge 0 (emA3 io ι τ x) := fun τ x =>
    ge_zero_of_isIntegral V (map_isIntegral_int (emA3 io ι τ) (Algebra.IsIntegral.isIntegral x))
  let M : 𝓞 E → Matrix (Fin (chD C3.ch)) (Fin (chD C3.ch)) C := fun a i j =>
    MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (Y.B.A.act a i)
  have hM : ∀ a z, linAct (Y.B.A.act a) z = (M a).mulVec z := fun a z => rfl
  have heig : ∀ (a : 𝓞 E) (ℓ : Lt1 Dw), (M a).mulVec (fun s => ι (chartUnitVectors C3 ℓ s)) =
      emA3 io ι ℓ.1 a • fun s => ι (chartUnitVectors C3 ℓ s) := by
    intro a ℓ
    funext i
    have h := congrArg ι (GlobalTheory.EigDir.linEig_holds E H Dw l Xo c T.Fr y.1 C3.ch a ℓ i)

    rw [map_sum, map_mul] at h
    refine Eq.trans ?_ h
    show ∑ j, M a i j * ι (chartUnitVectors C3 ℓ j) = _
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    simp only [M, hY.act, MvPowerSeries.coeff_map]
    rfl
  refine ⟨fun o g a x => hint _ x, ?_, ?_, ?_, ?_, ?_⟩
  · intro o a x
    have h : embK c (ComplexEmbedding.conjugate (lab.tau o 0 a)) x = embK c (lab.tau o 0 a) (H.bar x) := by
      apply Subtype.ext
      rw [embK_coe, embK_coe, ComplexEmbedding.conjugate_coe_eq, H.bar_eq,
        IsCMField.complexEmbedding_complexConj]
    rw [ha.conj, hs]
    exact congrArg (ι.comp io) h
  · intro o g x i
    unfold lieBasisVector
    rw [huv]
    exact hval _
  · intro o g x a
    exact heig a ⟨lab.tau o g x.1, x.2⟩
  · intro o g
    have key := GlobalTheory.SatBlocks.saturated_blocks_summand C V.v (𝓞 E) (ZMod d)
      (fun a => Dw.mult (lab.tau o g a)) (chD C3.ch) M (fun a x => emA3 io ι (lab.tau o g a) x)
      (lieBasisVector C3 ι lab o g) (fun x i j => Y.intAct x i _) (fun a x => hint _ x)
      (fun x q => heig x ⟨lab.tau o g q.1, q.2⟩)
      (fun a a' h => ha.sep (o, g, a) (o, g, a') (fun e => h (congrArg (fun p => p.2.2) e)))
      (fun a => by
        obtain ⟨⟨w, emb, hw1, hw2⟩, -⟩ := Formalism.L2.Pj.SaturatedCharts.saturation_charts_holds Xo c T io y C3 (lab.tau o g a)
        obtain ⟨W, hW⟩ := exists_dual w emb hw2
        refine ⟨fun s i => ι (algebraMap T.V T.Fr (W s i)), fun s i => hval _, fun i i' => ?_⟩
        have := congrArg (ι.comp (algebraMap T.V T.Fr)) (hW i i')

        rw [map_sum, apply_ite (ι.comp (algebraMap T.V T.Fr)), map_one, map_zero] at this
        refine Eq.trans ?_ this
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [map_mul, hw1]
        unfold lieBasisVector
        rw [huv]
        rfl)
    obtain ⟨w, h1, h2⟩ := key
    exact ⟨w, h1, fun q q' => by convert h2 q q'⟩
  · intro o g a v hv
    have hinj : Function.Injective fun (τ : E →+* ℂ) (x : 𝓞 E) => emA3 io ι τ x := by
      intro τ τ' h
      by_contra hne
      obtain ⟨b, hb⟩ := GlobalTheory.EigDir.embK_sep c τ τ' hne
      exact hb ((ι.comp io).injective (congrFun h b))
    obtain ⟨b, hb⟩ := GlobalTheory.eigenvector_mem_span_block_of_basis T.Fr C ι (𝓞 E) (E →+* ℂ) Dw.mult (chD C3.ch) M
      (fun τ x => emA3 io ι τ x) (chartUnitVectors C3) hinj heig C3.ch.chart.basis (lab.tau o g a) v hv
    refine ⟨fun q => if h : q.1 = a then b (Fin.cast (by rw [h]) q.2) else 0, fun q hq => dif_neg hq, ?_⟩
    rw [hb, Fintype.sum_sigma, Finset.sum_eq_single a]
    · refine Finset.sum_congr rfl fun i _ => ?_
      dsimp only
      rw [dite_eq_left rfl]
      rfl
    · intro a' _ ha'
      refine Finset.sum_eq_zero fun i _ => ?_
      dsimp only
      rw [dif_neg ha', zero_smul]
    · intro h
      exact absurd (Finset.mem_univ a) h

end GlobalTheory.LabelledDirections
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.exists_endomorphism_pair_w0 : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0), ∃ W W' : Matrix (Fin 2 × Fin dd) (Fin 2 × Fin dd) C, IsEnd (Y.rawSelf p) V W W' ∧ W + W' = 1 ∧ (∀ (v : Fin 2 × Fin dd → C) (x : Fin 2 × Fin dd), W.mulVec v x = linAct (Y.B.A.act Y.w0) (fun i => v (x.1, i)) x.2) ∧ ∑ col : Fin 2, inCol col (un1 (Y.B.hL C Y.h Y.w0)) = hEnd (Y.rawSelf p) 1 W := by
  first | exact @GlobalTheory.ActionEndSelf.exists_endomorphism_w0 | exact GlobalTheory.ActionEndSelf.exists_endomorphism_w0 | (intros; apply GlobalTheory.ActionEndSelf.exists_endomorphism_w0 <;> assumption)
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.invariantDerivations_constant_in_logCoordinates : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (n : ℕ) (W : Type) [Fintype W] (Z : Fin n × Fin dd → MvPowerSeries W C), (∀ s, MvPowerSeries.constantCoeff (Z s) = 0) → ∀ (b : Fin n) (u : Fin dd → C) (co : W → C), (∀ (b' : Fin n) (j : Fin dd), ∑ w, co w • MvPowerSeries.pderiv (R := C) w (Z (b', j)) = if b' = b then MvPowerSeries.C (u j) else 0) → ∀ G : PS C n dd, MvPowerSeries.subst (fun s : Fin n × Fin dd => MvPowerSeries.subst (fun j : Fin dd => Z (s.1, j)) (un1 (Y.ex s.2))) (DofN (Y.B.FK C) b u G) = ∑ w, co w • MvPowerSeries.pderiv (R := C) w (MvPowerSeries.subst (fun s : Fin n × Fin dd => MvPowerSeries.subst (fun j : Fin dd => Z (s.1, j)) (un1 (Y.ex s.2))) G) := by
  first | exact @GlobalTheory.InvDerivLog.subst_ex_DofN | exact GlobalTheory.InvDerivLog.subst_ex_DofN | (intros; apply GlobalTheory.InvDerivLog.subst_ex_DofN <;> assumption)
end
