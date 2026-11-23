module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
public import Formalism.HermitianCurvature.FrameExists2
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupCocycleLthPowerCoboundaryModMaximal
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralSmulCurveCoeffSeriesOfChartHOfLinearLog
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle117
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle140
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle147
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle118
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle116
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MatrixUnitZeroZeroEqInsert
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle005
public import Formalism.HermitianCurvature.Bundle004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle161
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle115
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle038
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle030
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle122
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle068
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle096
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle104
public import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OnePointBasisFundamentalDomainVolume
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle148
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle107
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle052
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle053
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle157
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted

@[expose] public section

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

theorem _root_.GlobalTheory.T.exists_wignerContraction_chain_raising : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (u : ℕ → ℝ) (β : ℂ) (L : Fin (n + 1) → ℤ) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (l : Fin (n + 1)) (n₀ : ℕ), inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π u → StrictAnti L → (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) → IsFrameOf (n + 1) r [z] B → (∀ j, j < l → L l + (n₀ : ℤ) < L j) → ∃ (V₂ : Type) (_ : NormedAddCommGroup V₂) (_ : InnerProductSpace ℂ V₂) (_ : FiniteDimensional ℂ V₂) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (A : (Fin (2 * r + (n + 1) + 1) → ℂ) → (V₂ →L[ℂ] V)), IsType (n + 1) r z π₂ (Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) + (n₀ : ℝ))) ∧ GlobalTheory.WigSh.WigMap (n + 1) r z π₂ π n₀ A ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA (EB π B)) (shf β M) → A (B (Fin.last n)) (ContinuousLinearMap.adjoint (A (B (Fin.last n))) v) = ((∏ j ∈ Finset.range n₀, GlobalTheory.WigSh.wP (Function.update L l (L l + (j : ℤ))) M l : ℝ) : ℂ) • v := by
  first | exact @GlobalTheory.WigSh.chain_raise | exact GlobalTheory.WigSh.chain_raise | (intros; apply GlobalTheory.WigSh.chain_raise <;> assumption)
end

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.formalGroupCocycle_lthPower_coboundary_mod_maximal : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ γ : κ → PowerSeries C, IsCv V γ → (∀ i n, 2 ≤ n → n < V.l ^ 2 → PowerSeries.coeff n (alongCv γ (X.lg i)) = 0) → IntS V (c2 X fun i => PowerSeries.coeff 1 (γ i)) ∧ ∀ μ, V.MM (MvPowerSeries.coeff μ ((c2 X fun i => PowerSeries.coeff 1 (γ i)) ^ V.l + cob X ((V.l : C) • hCoef X γ V.l))) := by
  first | exact @GlobalTheory.CocyclePow.cocycle_pow_coboundary | exact GlobalTheory.CocyclePow.cocycle_pow_coboundary | (intros; apply GlobalTheory.CocyclePow.cocycle_pow_coboundary <;> assumption)
end

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.integral_smul_curveCoeffSeriesOfChartH_of_linear_log : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ γ : κ → PowerSeries C, IsCv V γ → (∀ i n, 2 ≤ n → n < V.l ^ 2 → PowerSeries.coeff n (alongCv γ (X.lg i)) = 0) → IntS V ((V.l : C) • hCoef X γ V.l) ∧ ((∀ v : κ → C, (∀ i, V.Ge 0 (v i)) → V.MM ((V.l : C) * PowerSeries.coeff V.l (alongCv γ (X.sg v)))) → ∀ i μ, V.MM (MvPowerSeries.coeff μ (MvPowerSeries.pderiv (R := C) i ((V.l : C) • hCoef X γ V.l)))) := by
  first | exact @GlobalTheory.GaugeCoef.main | exact GlobalTheory.GaugeCoef.main | (intros; apply GlobalTheory.GaugeCoef.main <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF

theorem hatExp_exists_bound (P : M.Par) :
    ∃ C : ℝ, ∀ t : ℝ, C ≤ t → ∀ ρ : M.Ty P, M.xC P ρ (t : ℂ) ≠ 0 := by
  obtain ⟨C, hC⟩ := (Set.toFinite
    ((fun x : M.Ty P × ℕ => -M.rho P x.1 x.2) ''
      ((Finset.univ ×ˢ Finset.Icc 1 (P.k - 1) : Finset (M.Ty P × ℕ)) : Set (M.Ty P × ℕ)))).bddAbove
  refine ⟨C + 1, fun t ht ρ => ?_⟩
  unfold M.xC
  refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
  have h1 : -M.rho P ρ i ≤ C :=
    hC ⟨(ρ, i), Finset.mem_coe.2 (Finset.mem_product.2 ⟨Finset.mem_univ _, hi⟩), rfl⟩
  have h2 : t + M.rho P ρ i ≠ 0 := (show 0 < t + M.rho P ρ i by linarith).ne'
  exact_mod_cast h2

theorem hatExp_exists_nodes (P : M.Par) (n : ℕ) :
    ∃ y : Fin n → ℝ, Function.Injective y ∧ ∀ i, ∀ ρ : M.Ty P,
      M.xC P ρ (y i : ℂ) ≠ 0 ∧ M.xC P ρ ((y i : ℂ) - 1) ≠ 0 ∧ M.xC P ρ ((y i : ℂ) + 1) ≠ 0 := by
  obtain ⟨C, hC⟩ := hatExp_exists_bound P
  refine ⟨fun i => C + 1 + (i : ℕ), fun i j h => ?_, fun i ρ => ?_⟩
  · have h' : ((i : ℕ) : ℝ) = (j : ℕ) := by simpa using h
    exact Fin.ext (by exact_mod_cast h')
  · have h0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
    refine ⟨hC _ (by linarith) ρ, ?_, ?_⟩
    · have := hC (C + 1 + (i : ℕ) - 1) (by linarith) ρ
      rwa [Complex.ofReal_sub, Complex.ofReal_one] at this
    · have := hC (C + 1 + (i : ℕ) + 1) (by linarith) ρ
      rwa [Complex.ofReal_add _ 1, Complex.ofReal_one] at this

theorem hats_mem_nfSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (T : Set A) (a : ℕ), (∀ x ∈ basics d, x ∈ nfSpan d T 0 a 1) → ∀ X ∈ hats d.L, X ∈ nfSpan d T 0 a 1 := by
  intro P A _ _ _ _ d hd T a hT
  have hle : nfSpan d (basics d) 0 0 1 ≤ nfSpan d T 0 a 1 := by
    unfold nfSpan
    refine Submodule.span_le.2 ?_
    rintro x ⟨b, hb, H, hH, hHT, rfl⟩
    obtain ⟨h, rfl⟩ := List.length_eq_one_iff.1 hH
    have h1 := ((GlobalTheory.T.normalFormProductSpan_left_mul_closed P A d hd T).1 0 a 1 h (hT h (hHT h (List.mem_singleton_self h)))).1 b hb
    simpa [nfSpan] using h1
  obtain ⟨y, hy, hreg⟩ := hatExp_exists_nodes P (P.r + 2)
  have hyc : Function.Injective fun i => (y i : ℂ) := fun i j h => hy (Complex.ofReal_injective h)
  have hyn : Function.Injective fun i => -(y i : ℂ) := fun i j h => hyc (neg_injective h)
  have key : ∀ (Z : ℂ → A) (X : ℕ → A) (ν : Fin (P.r + 2) → ℂ), Function.Injective ν →
      (∀ s : ℂ, Z s = ∑ j ∈ Finset.range (P.r + 2), s ^ j • X j) →
      (∀ i, Z (ν i) ∈ nfSpan d T 0 a 1) → ∀ s, Z s ∈ nfSpan d T 0 a 1 := by
    intro Z X ν hν hZ hi s
    refine (Submodule.span_le.2 ?_) ((GlobalTheory.T.mem_span_values_of_vector_polynomial A (P.r + 2) Z X ν hν hZ).2 s)
    rintro _ ⟨i, rfl⟩
    exact hi i
  obtain ⟨Xa, Xr, hXa, hXr, -⟩ := GlobalTheory.T.plusHats_taylorCoeff_leibniz_rule A P.r d.L 0
  obtain ⟨Va, Vr, hVa, hVr, -⟩ := GlobalTheory.T.minusHats_taylorCoeff_leibniz_rule A P.r d.L 0
  rintro X (((⟨s, rfl⟩ | ⟨s, rfl⟩) | ⟨s, rfl⟩) | ⟨s, rfl⟩)
  · have := key (fun s => d.L.Ahat (0 + s)) Xa _ hyc hXa
      (fun i => by simpa using hT _ ⟨y i, hreg i, Or.inl rfl⟩) s
    simpa using this
  · have := key (fun s => d.L.R0 (0 + s)) Xr _ hyc hXr
      (fun i => by simpa using hle (GlobalTheory.T.R0_and_R0v_mem_nfSpan_basics_of_xC_ne_zero P A d hd (y i) (hreg i)).1) s
    simpa using this
  · have := key (fun s => d.L.Ahatv (0 - s)) Va _ hyn hVa
      (fun i => by simpa using hT _ ⟨y i, hreg i, Or.inr (Or.inl rfl)⟩) (-s)
    simpa using this
  · have := key (fun s => d.L.R0v (0 - s)) Vr _ hyn hVr
      (fun i => by simpa using hle (GlobalTheory.T.R0_and_R0v_mem_nfSpan_basics_of_xC_ne_zero P A d hd (y i) (hreg i)).2) (-s)
    simpa using this

end GlobalTheory.HatNF
end

section

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

section

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]


omit [StarModule ℂ A] in
theorem word_one_mem_nfSpan (d : Q.NFData P A) (T : Set A) : (1 : A) ∈ nfSpan d T 0 0 0 :=
  Submodule.subset_span ⟨1, one_mem _, [], rfl, by simp, by simp⟩


omit [StarModule ℂ A] in
theorem word_letter_mem_nfSpan (d : Q.NFData P A) (T : Set A) {X : A} (hX : X ∈ T) : X ∈ nfSpan d T 0 0 1 :=
  Submodule.subset_span ⟨1, one_mem _, [X], rfl, by simpa using hX, by simp⟩

theorem word_mul_mem_nfSpan (d : Q.NFData P A) (hd : HatHyp d) {n : ℕ} {x y : A}
    (hx : x ∈ nfSpan d (hats d.L) 1 0 1) (hy : y ∈ nfSpan d (hats d.L) n 0 n) :
    x * y ∈ nfSpan d (hats d.L) (n + 1) 0 (n + 1) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.normalFormProductSpan_left_mul_closed P A d hd (hats d.L)
  unfold nfSpan at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, H, hH, hT, rfl⟩ := hx
    obtain ⟨t, rfl⟩ := List.length_eq_one_iff.mp hH
    have ht : t ∈ hats d.L := hT t (by simp)
    have a1 := h2 0 (fun X hX => word_letter_mem_nfSpan d _ hX) n 0 n t ht y hy
    have a2 := (h1 _ _ _ _ a1).2.1
    have a3 := (h1 _ _ _ _ a2).1 b hb
    simpa [mul_assoc] using a3
  | zero => rw [zero_mul]; exact zero_mem _
  | add x x' _ _ ih ih' => rw [add_mul]; exact add_mem ih ih'
  | smul c x _ ih => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ih

end

theorem word_mem_nfSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (L : LevelData A P.r) (st : Start A) (s : ℂ), Comparison₂ d L st s → ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ w : List (Letter ℂ S), admitted st w → ∀ e : Ix S, ((ofWord L st w).F * TL.bTA L w) e e1 ∈ nfSpan d (hats d.L) w.length 0 w.length := by
  intro P A _ _ _ _ d hd L st s ht S _ _ w
  induction w with
  | nil =>
    intro _ e
    have : ((ofWord L st ([] : List (Letter ℂ S))).F * TL.bTA L []) = 1 := by
      simp [ofWord, Start.frame, TL.bTA, bT]
    rw [this, Matrix.one_apply]
    split_ifs
    · exact word_one_mem_nfSpan d _
    · exact zero_mem _
  | cons l w ih =>
    intro hA e
    have hAw : admitted st w := ⟨(List.nodup_cons.mp (by simpa only [List.map_cons] using hA.1)).2,
      fun l' h => hA.2.1 l' (by simp [h]), fun l' h => hA.2.2.1 l' (by simp [h]), (List.pairwise_cons.mp hA.2.2.2).2⟩
    rw [Formalism.FourierDecayAlt.P.word_recursion A S P.r L st l w ht.1 hA e, Matrix.mul_apply]
    refine Submodule.sum_mem _ fun e' _ => ?_
    have h1 : ((∑ i : Fin 2, eU l.intersection_update_fsHerm_neg_one i 0 * TL.letterCol L st l w i : SlopeTestRemainingChoices S A) e e') ∈
        nfSpan d (hats d.L) 1 0 1 := by
      rw [Matrix.sum_apply]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [Matrix.mul_apply]
      refine Submodule.sum_mem _ fun e'' _ => ?_
      simp only [eU, Matrix.of_apply]
      split_ifs
      · rw [one_mul]; exact GlobalTheory.T.letterCol_mem_normalFormProductSpan P A d hd L st s ht S l w hA i e'' e'
      · rw [zero_mul]; exact zero_mem _
    exact word_mul_mem_nfSpan d hd h1 (ih hAw e')

end GlobalTheory.HatNF
end

section

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem hats_prod_mem_nfSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (T : Set A) (a : ℕ), (∀ X ∈ hats d.L, X ∈ nfSpan d T 0 a 1) → ∀ H : List A, (∀ h ∈ H, h ∈ hats d.L) → H.prod ∈ nfSpan d T 0 (a * H.length) H.length := by
  intro P A _ _ _ _ d hd T a ha H
  induction H with
  | nil =>
    intro _
    refine Submodule.subset_span ⟨1, (bmon d).one_mem, [], rfl, by simp, ?_⟩
    simp
  | cons X H ih =>
    intro hH
    have h1 := ih (fun h hh => hH h (List.mem_cons_of_mem _ hh))
    have h2 := (GlobalTheory.T.normalFormProductSpan_left_mul_closed P A d hd T).2 a ha 0 (a * H.length) H.length X
      (hH X List.mem_cons_self) _ h1
    rw [List.prod_cons, List.length_cons, Nat.mul_succ]
    exact h2

end GlobalTheory.HatNF
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.normalForm_actualOperators_algebraicHypotheses : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → HatHyp d ∧ Comparison₂ d L st (M.sgn P l0) := by
  first | exact @GlobalTheory.HatNF.hatHyp_and_tie_of_isNF | exact GlobalTheory.HatNF.hatHyp_and_tie_of_isNF | (intros; apply GlobalTheory.HatNF.hatHyp_and_tie_of_isNF <;> assumption)
end

section

namespace GlobalTheory.HatNF.SmoothLift

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF MeasureTheory

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem opApply_JF (D : B.RealPlaceData k r Wp Wq) (A : ℝ) (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (Θ : B.DiffOp k r Wp Wq) (ho : B.opOrder Θ ≤ m) (hT : TransportedAlt k r A m) (hF : B.InCC A m F)
    (g : B.Mat k r) (hg : g ∈ Om k r D.z D.z')
    (hC : ∀ p, D.inSS p → opApply Θ (rho D p F) g = rho D p (opApply Θ F) g) :
    B.opApply Θ (B.JF D F) g = B.JF D (B.opApply Θ F) g := by
  have hW := jacquet_derivative_formula
  have hR := rewrite_rho_action
  have hCk : CkOn (m : ℕ∞) (GV k r) F := hF.choose_spec.1
  have hgG : g ∈ GV k r := hg.1
  have key : ∀ T ∈ Θ, Integrable (fun p => xiP D p • Rw T.word (rho D p F) g) D.μSS ∧
      Rw T.word (JF D F) g = ∫ p, xiP D p • Rw T.word (rho D p F) g ∂D.μSS := by
    intro T hT'
    have hvl : T.word.length ≤ m := (B5.len_le_order Θ hT').trans ho
    set v' := T.word.map fun X => ((‖X‖⁻¹ : ℝ) : ℂ) • X with hv'
    have hv'u : ∀ X ∈ v', unitLie k r X := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
      exact B4.nrm_unit (x := (false, Y)) (T.word_lie Y hY)
    have hv'l : v'.length ≤ m := by rw [hv', List.length_map]; exact hvl
    obtain ⟨hI, hE⟩ := (hW k r Wp Wq D A m F hT hF).2 [] v' (by simp) hv'u (by simpa using hv'l) g hg
    simp only [List.map_nil] at hI hE
    have hae : (fun p => xiP D p • rho D p (dLR [] (v'.map (AdR p)) F) g) =ᵐ[D.μSS]
        fun p => xiP D p • Rw v' (rho D p F) g := by
      filter_upwards [B5.ae_inSS D] with p hp
      have := hR k r Wp Wq D m F p hp hCk [] v' (by simp) (fun X hX => (hv'u X hX).1) (by simpa using hv'l) g hgG
      simp only [List.map_nil] at this
      rw [← this]
      rfl
    have hI' : Integrable (fun p => xiP D p • Rw v' (rho D p F) g) D.μSS := hI.congr hae
    have hfun : (fun p => xiP D p • Rw T.word (rho D p F) g) =
        fun p => (B4.pn (B4.lr [] T.word) : ℝ) • (xiP D p • Rw v' (rho D p F) g) := by
      funext p
      rw [WordIntegralScaling.rw_scale T.word (rho D p F), Pi.smul_apply, smul_comm]
    refine ⟨?_, ?_⟩
    · rw [hfun]; exact hI'.smul (B4.pn (B4.lr [] T.word))
    · rw [WordIntegralScaling.rw_scale T.word (JF D F), Pi.smul_apply, hfun, integral_smul]
      congr 1
      rw [← integral_congr_ae hae]
      exact hE
  have hRHS : JF D (opApply Θ F) g = ∫ p, xiP D p • opApply Θ (rho D p F) g ∂D.μSS := by
    show (∫ p, xiP D p • rho D p (opApply Θ F) g ∂D.μSS) = _
    refine integral_congr_ae ?_
    filter_upwards [B5.ae_inSS D] with p hp
    rw [hC p hp]
  rw [hRHS]
  unfold opApply
  simp only [WordIntegralScaling.smul_list]
  obtain ⟨_, hsum⟩ := WordIntegralScaling.int_list D.μSS Θ (fun T => T.coef g)
    (fun T p => xiP D p • Rw T.word (rho D p F) g) fun T hT' => (key T hT').1
  rw [hsum]
  congr 1
  refine List.map_congr_left fun T hT' => ?_
  rw [(key T hT').2]

theorem polyLift_of_smooth_comm (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (o κ : ℕ)
    (Θ : B.DiffOp P.k P.r Wp Wq) (a : RA P Bs) (hP : CutMP.PolyOp o κ Θ)
    (hC : ∀ p, Bs.inSS p → ∀ f : B.Mat P.k P.r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV P.k P.r) f →
      ∀ g ∈ B.GPos Bs, B.opApply Θ (B.rho Bs p f) g = B.rho Bs p (B.opApply Θ f) g)
    (hres : ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Q.OmPlus P.k P.r Bs.z Bs.z'),
      ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      (∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
        (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = Q.resG P.k P.r (Fin.last P.r) J x.1 x.2) →
      ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z', (a.1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
        Q.resG P.k P.r (Fin.last P.r) (B.opApply Θ J) x.1 x.2) :
    PolyLift P Bs o κ a := by
  refine ⟨Θ, hP, fun F hF Φ hΦ x hx => ?_⟩
  obtain ⟨ε, hε, hN⟩ := (compact_support_facts P.k P.r Wp Wq Bs F hF).1
  have hJ := bessel_function_finite_class P.k P.r Wp Wq Bs F ε hε hN
  rw [hres _ hJ Φ hΦ x hx]
  have hom : Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2 ∈ Om P.k P.r Bs.z Bs.z' :=
    ⟨TLB.wCell_gv Bs hx, P5.Rad.wCell_mem_omPlus Bs.z_mem Bs.z'_mem hx.1 hx.2.1 hx.2.2⟩
  simp only [Q.resG]
  rw [opApply_JF Bs _ (B.opOrder Θ) F Θ le_rfl (JFxG.thr_big P.k P.r (B.opOrder Θ)) (hN.2.1 _ _) _ hom
    (fun p hp => hC p hp F hF.1 _ ⟨hom.1, hom.2.2⟩)]

end GlobalTheory.HatNF.SmoothLift
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselNormSq

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsInner_sum_sum {m : ℕ} (A C : Fin m → (Wq →L[ℂ] Wp)) :
    B.hsInner (∑ i, A i) (∑ j, C j) = ∑ i, ∑ j, B.hsInner (A i) (C j) := by
  have h : ∀ A : Fin m → (Wq →L[ℂ] Wp), B.hsVec (∑ i, A i) = ∑ i, B.hsVec (A i) := by
    intro A
    ext t
    simp [B.hsVec, ContinuousLinearMap.sum_apply]
  unfold B.hsInner
  rw [h, h, inner_sum]
  exact Finset.sum_congr rfl fun i _ => sum_inner _ _ _

theorem Ph_sum [FiniteDimensional ℂ Wp] (D : B.RealPlaceData k r Wp Wq) {m : ℕ} (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (f : Fin m → B.Mat k r → (Wq →L[ℂ] Wp)) (hF : ∀ g ∈ B.GV k r, F g = ∑ i, f i g) (p : B.SS k r)
    (hp : D.inSS p)
    (hint : ∀ i j, Integrable (fun g : Formalism.QuantumDeterminants.Mt k r =>
      B.hsInner (B.rho D p (f i) (Matrix.of g)) (f j (Matrix.of g))) D.μG) :
    B.Ph D F F p = ∑ i, ∑ j, B.Ph D (f i) (f j) p := by
  have hae : ∀ᵐ g ∂D.μG, Matrix.of g ∈ B.GV k r := D.haarG.conc
  unfold B.Ph
  have e1 : ∀ i, ∑ j, ∫ g, B.hsInner (B.rho D p (f i) (Matrix.of g)) (f j (Matrix.of g)) ∂D.μG =
      ∫ g, ∑ j, B.hsInner (B.rho D p (f i) (Matrix.of g)) (f j (Matrix.of g)) ∂D.μG :=
    fun i => (integral_finsetSum _ fun j _ => hint i j).symm
  simp only [e1]
  rw [← integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  refine integral_congr_ae (hae.mono fun g hg => ?_)
  have h1 : B.rho D p F (Matrix.of g) = ∑ i, B.rho D p (f i) (Matrix.of g) := by
    unfold B.rho
    rw [hF _ (Formalism.FourierDecayAlt.P.B6.conj_product_mem_unitary_group D hp hg)]
    ext v
    simp [ContinuousLinearMap.sum_apply]
  simp only
  rw [h1, hF _ hg, hsInner_sum_sum]

theorem normSq_coef : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq), ∃ c : ℝ, 0 < c ∧ ∀ (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (l : R.H → Wp) (l' : R.H → Wq) (dd : ℝ), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ F s, IsCoef R l l' F s → B.normSq D F = ENNReal.ofReal (c * ‖s‖ ^ 2 / dd) := by
  intro H k r Wp _ _ _ _ Wq _ _ _ _ D
  obtain ⟨c, hc, hnb⟩ := GlobalTheory.T.besselNormSq_eq_const_mul_archPairing k r Wp Wq D
  refine ⟨c, hc, ?_⟩
  intro ε mu h R l l' dd hDS hgap hok hl hl' hdd F s hF
  have hA := (GlobalTheory.T.decayThresholds_of_spectralGapCondition k r h hok).2.1
  have hcc := (GlobalTheory.T.smooth_and_inCC_of_isCoef_of_gap H k r ε mu h R Wp Wq l l' F s hDS hgap hok hF).2
  obtain ⟨m, x, y, X, hxy, hFg, hs⟩ := hF
  set f : Fin m → B.Mat k r → (Wq →L[ℂ] Wp) := fun i g => ⟪x i, R.σ g (y i)⟫_ℂ • X i with hf
  have hI := fun i j => GlobalTheory.T.bessel_formal_degree_pairing H k r ε mu h R Wp Wq D l l' dd hDS hgap hok hl hl' hdd
    (x i) (hxy i).1 (y i) (hxy i).2 (x j) (hxy j).1 (y j) (hxy j).2 (X i) (X j)
  have hPh : B.Ph D F F =ᵐ[D.μSS] fun p => ∑ i, ∑ j, B.Ph D (f i) (f j) p :=
    (Formalism.FourierDecayAlt.P.B6.ae_inSS D).mono fun p hp => Ph_sum D F f hFg p hp fun i j =>
      (GlobalTheory.T.bessel_formal_degree_identity H k r ε mu R Wp Wq D dd hDS hdd (x i) (y i) (x j) (y j) (X i) (X j) p hp).1
  have hint : Integrable (B.Ph D F F) D.μSS :=
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hI i j).1).congr hPh.symm
  have hxi : ∀ i j, Integrable (fun p => B.xiTau D (1, 1) p * B.Ph D (f i) (f j) p) D.μSS := by
    intro i j
    refine Integrable.bdd_mul (c := 1) (hI i j).1 ?_ (Filter.Eventually.of_forall fun p => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      have c1 : Continuous fun p : B.SS k r => B.lam k r D.z (Matrix.of p.1.2) :=
        (Formalism.FourierDecayAlt.P.B6.lam_continuous k r D.z).comp (continuous_snd.comp continuous_fst)
      have c2 : Continuous fun p : B.SS k r => B.lam k r D.z' (Matrix.of p.2.2) :=
        (Formalism.FourierDecayAlt.P.B6.lam_continuous k r D.z').comp (continuous_snd.comp continuous_snd)
      unfold B.xiTau
      exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        ((continuous_const.mul c1).sub (continuous_const.mul c2))))
    · unfold B.xiTau
      rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hb : B.betaInf D F F = ((‖s‖ ^ 2 / dd : ℝ) : ℂ) := by
    rw [GlobalTheory.T.betaInf_eq_integral_of_integrable_coefficient k r Wp Wq D _ F hA (hcc 4) hint]
    have e0 : ∫ p, B.xiTau D (1, 1) p * B.Ph D F F p ∂D.μSS =
        ∫ p, ∑ i, ∑ j, B.xiTau D (1, 1) p * B.Ph D (f i) (f j) p ∂D.μSS := by
      refine integral_congr_ae (hPh.mono fun p hp => ?_)
      simp only [hp, Finset.mul_sum]
    rw [e0, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hxi i j]
    have e1 : ∀ i, ∫ p, ∑ j, B.xiTau D (1, 1) p * B.Ph D (f i) (f j) p ∂D.μSS =
        ∑ j, ⟪l (x i), X i (l' (y i))⟫_ℂ * star ⟪l (x j), X j (l' (y j))⟫_ℂ / (dd : ℂ) := by
      intro i
      rw [integral_finsetSum _ fun j _ => hxi i j]
      exact Finset.sum_congr rfl fun j _ => (hI i j).2
    simp only [e1]
    have e2 : ((‖s‖ ^ 2 / dd : ℝ) : ℂ) = s * star s / (dd : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [e2, hs, star_sum, Finset.sum_mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_div]
  rw [hnb _ F hA (hcc 5), hb, ← Complex.ofReal_mul, Complex.ofReal_re, mul_div_assoc]

end GlobalTheory.BesselNormSq
end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.bessel_gap_exists_nonzero : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → (∃ w ∈ R.sm, ∃ v ∈ R.TK, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ≠ 0) → ∃ (l₀ La : R.H → Wp), IsBes R z π l₀ ∧ NzOn R l₀ ∧ ∀ w ∈ R.sm, ∀ v ∈ R.TK, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v = (innerSL ℂ (La v)).smulRight (l₀ w) := by
  first | exact @GlobalTheory.BesselShape.bessel_shape | exact GlobalTheory.BesselShape.bessel_shape | (intros; apply GlobalTheory.BesselShape.bessel_shape <;> assumption)
end

section

open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants

theorem _root_.GlobalTheory.T.grids_at_place_longCut_normaliserPositive : ∀ (C b c : ℝ) (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ), 0 ≤ C → GridNum C b c P p.l0 lam → ((30 * (P.r + 1) ^ 2 + 6 : ℕ) : ℝ) ≤ |P.u p.l0 - P.u' p.l0| → (∀ y, 0 < Pst lam c y) ∧ 1 ≤ b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ)) ∧ ∃ Y : Finset ℝ, TBBx5.WaveGrid p (Pst lam c) Y (b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ))) 3 (3 * (P.r + 1)) ∧ TBBx5.LiftGrid p (Pst lam c) Y (b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ))) 3 (3 * (P.r + 1)) := by
  first | exact @GlobalTheory.GridAtPlace.main | exact GlobalTheory.GridAtPlace.main | (intros; apply GlobalTheory.GridAtPlace.main <;> assumption)
end
