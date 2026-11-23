module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.LeftInv
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PCompat
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
import Std.Tactic.BVDecide.Normalize.BitVec

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH lc_G sc_G lc_GLf sc_GLf t2_GL_finite_adeles borelSpaceH

namespace PositivityTheory.Rg.BcB.F.Rd.B

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem sc_H : SecondCountableTopology (H E a b) :=
  (splitH (E := E) a b).toHomeomorph.symm.secondCountableTopology

theorem lc_H : LocallyCompactSpace (H E a b) :=
  (splitH (E := E) a b).toHomeomorph.symm.isClosedEmbedding.locallyCompactSpace

theorem t2_block_group : T2Space (H E a b) :=
  (splitH (E := E) a b).toHomeomorph.t2Space

attribute [local instance] sc_H lc_H t2_block_group

theorem integrable_conv2 (μ : Measure (H E a b)) [IsFiniteMeasureOnCompacts μ] [SFinite μ]
    (φ₁ φ₂ g : H E a b → ℂ) (h₁ : IsTestH φ₁) (h₂ : IsTestH φ₂) (hg : Continuous g) :
    Integrable (fun p : H E a b × H E a b => φ₁ p.1 * φ₂ (p.1⁻¹ * p.2) * g p.2) (μ.prod μ) := by
  have hc : Continuous (fun p : H E a b × H E a b => φ₁ p.1 * φ₂ (p.1⁻¹ * p.2) * g p.2) :=
    ((h₁.1.comp continuous_fst).mul (h₂.1.comp (continuous_fst.inv.mul continuous_snd))).mul (hg.comp continuous_snd)
  refine hc.integrable_of_hasCompactSupport ?_
  have hK : IsCompact ((fun q : H E a b × H E a b => (q.1, q.1 * q.2)) '' (tsupport φ₁ ×ˢ tsupport φ₂)) :=
    (h₁.2.isCompact.prod h₂.2.isCompact).image (continuous_fst.prodMk (continuous_fst.mul continuous_snd))
  haveI ht : T2Space (H E a b) := t2_block_group
  haveI : T2Space (H E a b × H E a b) := Prod.t2Space
  refine HasCompactSupport.intro' hK hK.isClosed fun p hp => ?_
  by_contra hne
  apply hp
  refine ⟨(p.1, p.1⁻¹ * p.2), ⟨?_, ?_⟩, by simp⟩
  · exact subset_tsupport _ fun h => hne (by simp [h])
  · exact subset_tsupport _ fun h => hne (by simp [h])

theorem convolution_pairing_test_entry (μ : Measure (H E a b)) [IsFiniteMeasureOnCompacts μ] [SFinite μ] [μ.IsMulLeftInvariant]
    (φ₁ φ₂ g : H E a b → ℂ) (h₁ : IsTestH φ₁) (h₂ : IsTestH φ₂) (hg : Continuous g) :
    ∫ y, (∫ z, φ₁ z * φ₂ (z⁻¹ * y) ∂μ) * g y ∂μ = ∫ z, φ₁ z * ∫ w, φ₂ w * g (z * w) ∂μ ∂μ := by
  have hI := integrable_conv2 μ φ₁ φ₂ g h₁ h₂ hg
  have e1 : ∀ y, (∫ z, φ₁ z * φ₂ (z⁻¹ * y) ∂μ) * g y = ∫ z, φ₁ z * φ₂ (z⁻¹ * y) * g y ∂μ := fun y =>
    (integral_mul_const (g y) _).symm
  simp_rw [e1]
  rw [← integral_integral_swap (f := fun z y => φ₁ z * φ₂ (z⁻¹ * y) * g y) hI]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only
  rw [← integral_mul_left_eq_self (μ := μ) (fun y => φ₁ z * φ₂ (z⁻¹ * y) * g y) z, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [inv_mul_cancel_left]
  ring

theorem conv_mulM (D : Dom E a b) {ι : Type} [Fintype ι] (Φ₁ Φ₂ : Matrix ι ι (H E a b → ℂ)) (h₁ : IsTestM Φ₁)
    (h₂ : IsTestM Φ₂) (f : ι → H E a b → ℂ) (hf : ∀ i, Continuous (f i)) :
    PositivityTheory.Rg.BcB.E.conv D.μ (mulM D.μ Φ₁ Φ₂) f = PositivityTheory.Rg.BcB.E.conv D.μ Φ₁ (PositivityTheory.Rg.BcB.E.conv D.μ Φ₂ f) := by
  have := haar_of_dom D
  haveI : SigmaCompactSpace (H E a b) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite D.μ := SigmaFinite.of_isFiniteMeasureOnCompacts D.μ
  funext i x
  have hg : ∀ j, Continuous fun y => f j (x * y) := fun j => (hf j).comp (continuous_const.mul continuous_id)
  have hI : ∀ j k, Integrable (fun p : H E a b × H E a b => Φ₁ i k p.1 * Φ₂ k j (p.1⁻¹ * p.2) * f j (x * p.2))
      (D.μ.prod D.μ) := fun j k => integrable_conv2 D.μ _ _ _ (h₁ i k) (h₂ k j) (hg j)

  have hL : ∀ j, ∫ y, (∑ k, ∫ z, Φ₁ i k z * Φ₂ k j (z⁻¹ * y) ∂D.μ) * f j (x * y) ∂D.μ =
      ∑ k, ∫ y, (∫ z, Φ₁ i k z * Φ₂ k j (z⁻¹ * y) ∂D.μ) * f j (x * y) ∂D.μ := by
    intro j
    simp_rw [Finset.sum_mul]
    refine integral_finsetSum _ fun k _ => ?_
    have := (hI j k).integral_prod_right
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only
    exact integral_mul_const (f j (x * y)) _

  have hR : ∀ k, ∫ z, Φ₁ i k z * (∑ j, ∫ w, Φ₂ k j w * f j (x * z * w) ∂D.μ) ∂D.μ =
      ∑ j, ∫ z, Φ₁ i k z * ∫ w, Φ₂ k j w * f j (x * z * w) ∂D.μ ∂D.μ := by
    intro k
    simp_rw [Finset.mul_sum]
    refine integral_finsetSum _ fun j _ => ?_
    have := (hI j k).integral_prod_left
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only
    rw [← integral_mul_left_eq_self (μ := D.μ) (fun y => Φ₁ i k z * Φ₂ k j (z⁻¹ * y) * f j (x * y)) z,
      ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [inv_mul_cancel_left, mul_assoc]
  show ∑ j, ∫ y, (∑ k, ∫ z, Φ₁ i k z * Φ₂ k j (z⁻¹ * y) ∂D.μ) * f j (x * y) ∂D.μ =
    ∑ k, ∫ z, Φ₁ i k z * (∑ j, ∫ w, Φ₂ k j w * f j (x * z * w) ∂D.μ) ∂D.μ
  simp_rw [hL, hR]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  have := convolution_pairing_test_entry D.μ (Φ₁ i k) (Φ₂ k j) (fun y => f j (x * y)) (h₁ i k) (h₂ k j) (hg j)
  simpa only [mul_assoc] using this

end PositivityTheory.Rg.BcB.F.Rd.B

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.RgTw (Mat G)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF borelH

namespace PositivityTheory.Rg.BcB.F.Rd

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev chComm {B : Block E} {Γ : Type} (g : Γ → BGen B) (X : B.Hb →L[ℂ] B.Hb)
    (hg : ∀ x y, Commute (g x).op (g y).op ∧ Commute (g x).op (star (g y).op))
    (hX : ∀ x, Commute X (g x).op ∧ Commute X (star (g x).op)) (hXs : IsSelfAdjoint X) : CommRing (ChAlg g X) := by
  haveI : IsMulCommutative (ChAlg g X) := StarAlgebra.isMulCommutative_adjoin ℂ
    (s := gOps g ∪ {X})
    (by
      rintro u (⟨x, rfl⟩ | rfl)
      · exact ⟨((hg x x).2).symm⟩
      · exact ⟨by
          rw [hXs.star_eq]
          rfl⟩)
    (by
      rintro u (⟨x, rfl⟩ | rfl) v (⟨y, rfl⟩ | rfl) _
      · exact (hg x y).1
      · exact ((hX x).1).symm
      · exact (hX y).1
      · rfl)
    (by
      rintro u (⟨x, rfl⟩ | rfl) v (⟨y, rfl⟩ | rfl) _
      · exact (hg x y).2
      · rw [hXs.star_eq]
        exact ((hX x).1).symm
      · exact (hX y).2
      · contradiction)
  exact { (inferInstance : Ring (ChAlg g X)) with mul_comm := mul_comm' }

def genO {B : Block E} {Γ : Type} (g : Γ → BGen B) (X : B.Hb →L[ℂ] B.Hb) : Option Γ → (B.Hb →L[ℂ] B.Hb) :=
  fun o => o.elim X fun x => (g x).op

theorem range_genO {B : Block E} {Γ : Type} (g : Γ → BGen B) (X : B.Hb →L[ℂ] B.Hb) :
    Set.range (genO g X) = gOps g ∪ {X} := by
  ext z
  constructor
  · rintro ⟨o, rfl⟩
    cases o with
    | none => exact Or.inr rfl
    | some x => exact Or.inl ⟨x, rfl⟩
  · rintro (⟨x, rfl⟩ | rfl)
    · exact ⟨some x, rfl⟩
    · exact ⟨none, rfl⟩

def letter {B : Block E} {Γ : Type} (g : Γ → BGen B) (tX : PT B) : Option Γ × Bool → BGen B
  | (none, false) => Sum.inr tX
  | (none, true) => Sum.inr tX.adj
  | (some x, false) => g x
  | (some x, true) => (g x).adj

theorem letter_ok (hO : BlockOperatorsProductAdjoint) (hW : BlockWordOperators) {B : Block E} {Γ : Type} (g : Γ → BGen B)
    (X : B.Hb →L[ℂ] B.Hb) (tX t₀ : PT B) (hg : ∀ x, (g x).Ok) (htX : tX.Ok) (hX : X = tX.op) (h₀ : t₀.Ok)
    (p : Option Γ × Bool) :
    (letter g tX p).Ok ∧ (letter g tX p).op = if p.2 then star (genO g X p.1) else genO g X p.1 := by
  have hadj := (hW E B [] t₀ 0 (by simp) h₀ le_rfl (by simp)).2.2.2.2.1
  obtain ⟨o, s⟩ := p
  cases o with
  | none =>
    cases s with
    | false => exact ⟨htX, hX.symm⟩
    | true =>
      have := hO E B tX tX htX htX
      refine ⟨this.2.2.2.2.1, ?_⟩
      show tX.adj.op = star X
      rw [this.2.2.2.2.2.1, hX, ContinuousLinearMap.star_eq_adjoint]
  | some x =>
    cases s with
    | false => exact ⟨hg x, rfl⟩
    | true =>
      refine ⟨(hadj (g x) (hg x)).1, ?_⟩
      show (g x).adj.op = star (g x).op
      rw [(hadj (g x) (hg x)).2, ContinuousLinearMap.star_eq_adjoint]

theorem phiEx (hO : BlockOperatorsProductAdjoint) (hW : BlockWordOperators) (hS : BlockLinearCombinations) (hA : AdjWords) {B : Block E} {Γ : Type} (g : Γ → BGen B)
    (X : B.Hb →L[ℂ] B.Hb) (tX t₀ : PT B) (hg : ∀ x, (g x).Ok) (htX : tX.Ok) (hX : X = tX.op) (h₀ : t₀.Ok)
    (y : ChAlg g X) : ∃ Φ : Matrix B.I B.I (H E B.a B.b → ℂ), IsTestM Φ ∧ IsROp B.D Φ ((y : B.Hb →L[ℂ] B.Hb) * t₀.op) := by
  have hy : (y : B.Hb →L[ℂ] B.Hb) ∈ StarAlgebra.adjoin ℂ (Set.range (genO g X)) := by
    rw [range_genO]; exact y.2
  obtain ⟨J, hJ, c, w, L, -, hyw, -⟩ := hA (B.Hb →L[ℂ] B.Hb) (Option Γ) (genO g X) _ hy
  have hl := letter_ok hO hW g X tX t₀ hg htX hX h₀

  let bw : J → List (BGen B) := fun j => (w j).map (letter g tX)
  have bok : ∀ j, ∀ b ∈ bw j, b.Ok := fun j b hb => by
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hb
    exact (hl p).1
  have bop : ∀ j, ((bw j).map BGen.op).prod = wdVal (genO g X) (w j) := fun j => by
    simp only [bw, wdVal, List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    exact (hl p).2
  let R : J → ℝ := fun j => ((bw j).map fun b => Sum.elim (fun _ => (0 : ℝ)) (fun s => |s.T| + |s.r + B.c|) b).sum
  have hR0 : ∀ j, 0 ≤ R j := fun j => by
    apply List.sum_nonneg
    intro z hz
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hz
    rcases b with _ | s
    · exact le_rfl
    · exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hRs : ∀ j, ∀ s, Sum.inr s ∈ bw j → s.T ≤ R j ∧ s.r + B.c ≤ R j := fun j s hs => by
    have hle : |s.T| + |s.r + B.c| ≤ R j := by
      have := List.single_le_sum (l := (bw j).map fun b => Sum.elim (fun _ => (0 : ℝ)) (fun s => |s.T| + |s.r + B.c|) b)
        (fun z hz => by
          obtain ⟨b, -, rfl⟩ := List.mem_map.1 hz
          rcases b with _ | s
          · exact le_rfl
          · exact add_nonneg (abs_nonneg _) (abs_nonneg _))
        _ (List.mem_map.2 ⟨Sum.inr s, hs, rfl⟩)
      exact this
    exact ⟨(le_abs_self _).trans ((le_add_of_nonneg_right (abs_nonneg _)).trans hle),
      (le_abs_self _).trans ((le_add_of_nonneg_left (abs_nonneg _)).trans hle)⟩
  have hwd := fun j => hW E B (bw j) t₀ (R j) (bok j) h₀ (hR0 j) (hRs j)
  have hsum := hS E B.a B.b B.D B.I J Finset.univ (fun j => c j * BGen.sc (bw j)) (fun j => (BGen.wd (bw j) t₀).Φ)
    (fun j => (BGen.wd (bw j) t₀).op) (fun j _ => by
      have := hO E B _ _ (hwd j).1 (hwd j).1
      exact ⟨this.1, this.2.1⟩)
  refine ⟨_, hsum.1, ?_⟩
  convert hsum.2 using 1
  rw [hyw, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_assoc, ← bop, (hwd j).2.1, smul_smul]

end PositivityTheory.Rg.BcB.F.Rd

end
end

section

noncomputable section

open NumberField
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.gamma_zeta_nabla_cancel

open PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation

namespace RegH

theorem conj_ne {E : Type} [Field E] [NumberField E] [IsCMField E] (τ : E →+* ℂ) :
    (starRingEnd ℂ).comp τ ≠ τ := by
  intro h
  have hc : (InfinitePlace.mk τ).IsComplex := IsTotallyComplex.isComplex _
  rw [InfinitePlace.isComplex_iff] at hc
  apply hc
  have hr : ComplexEmbedding.IsReal τ := by
    rw [ComplexEmbedding.isReal_iff]
    exact RingHom.ext fun x => by simpa using congrArg (fun f : E →+* ℂ => f x) h
  rcases InfinitePlace.embedding_mk_eq τ with e | e
  · rw [e]; exact hr
  · rw [e, ComplexEmbedding.isReal_iff.1 hr]; exact hr

theorem conj_eq_conjugate {E : Type} [Field E] (τ : E →+* ℂ) :
    (starRingEnd ℂ).comp τ = ComplexEmbedding.conjugate τ := RingHom.ext fun _ => rfl

theorem mk_conj {E : Type} [Field E] [NumberField E] (τ : E →+* ℂ) :
    InfinitePlace.mk ((starRingEnd ℂ).comp τ) = InfinitePlace.mk τ := by
  rw [conj_eq_conjugate, InfinitePlace.mk_conjugate_eq]

theorem dec_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (τ : E →+* ℂ) :
    decide ((starRingEnd ℂ).comp τ = (InfinitePlace.mk ((starRingEnd ℂ).comp τ)).embedding) =
      !decide (τ = (InfinitePlace.mk τ).embedding) := by
  rw [mk_conj]
  have hne := conj_ne τ
  rcases InfinitePlace.embedding_mk_eq τ with e | e
  · rw [e]
    simp [hne]
  · rw [e, ← conj_eq_conjugate]
    have : τ ≠ (starRingEnd ℂ).comp τ := fun h => hne h.symm
    simp [this]

theorem infOf_not {n : ℕ} (lam : Fin n → ℤ) (s : Bool) (a : Fin n) :
    PositivityTheory.RgBcC.infOf lam (!s) a = -PositivityTheory.RgBcC.infOf lam s a := by
  cases s <;> simp [PositivityTheory.RgBcC.infOf]

theorem infOf_im {n : ℕ} (lam : Fin n → ℤ) (s : Bool) (a : Fin n) : (PositivityTheory.RgBcC.infOf lam s a).im = 0 := by
  cases s <;> simp [PositivityTheory.RgBcC.infOf]

theorem infOf_sep {n : ℕ} (lam : Fin n → ℤ) (hl : Antitone lam) (s : Bool) (a b : Fin n) (hab : a ≠ b) :
    (1 : ℝ) ≤ ‖PositivityTheory.RgBcC.infOf lam s a - PositivityTheory.RgBcC.infOf lam s b‖ := by
  have key : ∀ a b : Fin n, a < b → (1 : ℝ) ≤ ((lam a : ℝ) - (a : ℕ)) - ((lam b : ℝ) - (b : ℕ)) := by
    intro a b h
    have h1 : lam b ≤ lam a := hl h.le
    have h2 : (a : ℕ) + 1 ≤ (b : ℕ) := h
    have h1' : (lam b : ℝ) ≤ lam a := by exact_mod_cast h1
    have h2' : ((a : ℕ) : ℝ) + 1 ≤ (b : ℕ) := by exact_mod_cast h2
    linarith
  have e : ∀ a b : Fin n, PositivityTheory.RgBcC.infOf lam s a - PositivityTheory.RgBcC.infOf lam s b =
      ((if s then 1 else -1 : ℂ)) * ((((lam a : ℝ) - (a : ℕ)) - ((lam b : ℝ) - (b : ℕ)) : ℝ) : ℂ) := by
    intro a b
    simp only [PositivityTheory.RgBcC.infOf]
    push_cast
    ring
  have hs : ‖(if s then 1 else -1 : ℂ)‖ = 1 := by cases s <;> simp
  rcases lt_or_gt_of_ne hab with h | h
  · rw [e, norm_mul, hs, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (key a b h).trans (le_abs_self _)
  · rw [e, norm_mul, hs, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have := key b a h
    exact le_abs.mpr (Or.inr (by linarith))

theorem infOf_inj {n : ℕ} (lam : Fin n → ℤ) (hl : Antitone lam) (s : Bool) :
    Function.Injective (PositivityTheory.RgBcC.infOf lam s) := by
  intro a b h
  by_contra hab
  have := infOf_sep lam hl s a b hab
  rw [h, sub_self, norm_zero] at this
  norm_num at this

end RegH

open RegH

theorem regDom : RegDom := by
  intro E _ _ _ n l
  refine ⟨fun τ => ⟨?_, ?_⟩, fun τ => ⟨?_, ?_⟩⟩
  · intro x hx
    simp only [mOf, Multiset.mem_map] at hx
    obtain ⟨a, -, rfl⟩ := hx
    exact infOf_im _ _ _
  · simp only [mOf]
    rw [mk_conj, show decide ((starRingEnd ℂ).comp τ = (InfinitePlace.mk τ).embedding) =
        !decide (τ = (InfinitePlace.mk τ).embedding) from by rw [← dec_conj τ, mk_conj], Multiset.map_map]
    congr 1
    funext a
    exact infOf_not _ _ _
  · simp only [mOf]
    exact Multiset.Nodup.map (infOf_inj _ (l _).anti _) Finset.univ.nodup
  · intro x hx y hy hxy
    simp only [mOf, Multiset.mem_map] at hx hy
    obtain ⟨a, -, rfl⟩ := hx
    obtain ⟨b, -, rfl⟩ := hy
    have hab : a ≠ b := fun h => hxy (by rw [h])
    exact le_trans (by norm_num) (infOf_sep _ (l _).anti _ a b hab)

theorem reg_of (h : GelfInj) : Reg := by
  intro E _ _ _ n l χ hχ
  have e : mOf χ = mOf (fun v => PositivityTheory.RgBcC.infOf (l v).w) := by
    funext τ
    simp only [mOf]
    exact h n _ _ (hχ _ _)
  rw [e]
  exact regDom E n l

end PositivityTheory.Rg.BcB.F.gamma_zeta_nabla_cancel

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.RgTw (Mat G)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF borelH

namespace PositivityTheory.Rg.BcB.F.Rd.B

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Rd

def genE {E : Type} [Field E] [NumberField E] [IsCMField E] {B : Block E} {Γ : Type} (g : Γ → BGen B)
    (X : B.Hb →L[ℂ] B.Hb) (y : Γ) : ChAlg g X :=
  ⟨(g y).op, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨y, rfl⟩)⟩

def XE {E : Type} [Field E] [NumberField E] [IsCMField E] {B : Block E} {Γ : Type} (g : Γ → BGen B)
    (X : B.Hb →L[ℂ] B.Hb) : ChAlg g X :=
  ⟨X, StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)⟩

def ConvMulSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b) (ι : Type)
  [Fintype ι] (Φ₁ Φ₂ : Matrix ι ι (H E a b → ℂ)), IsTestM Φ₁ → IsTestM Φ₂ → ∀ f : ι → H E a b → ℂ,
  (∀ i, Continuous (f i)) →
  PositivityTheory.Rg.BcB.E.conv D.μ (mulM D.μ Φ₁ Φ₂) f = PositivityTheory.Rg.BcB.E.conv D.μ Φ₁ (PositivityTheory.Rg.BcB.E.conv D.μ Φ₂ f)

def FinSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E)
  (K₁ : Subgroup (GL (Fin B.a) (Af E))) (K₂ : Subgroup (GL (Fin B.b) (Af E))),
  IsOpen (K₁ : Set (GL (Fin B.a) (Af E))) → IsCompact (K₁ : Set (GL (Fin B.a) (Af E))) →
  IsOpen (K₂ : Set (GL (Fin B.b) (Af E))) → IsCompact (K₂ : Set (GL (Fin B.b) (Af E))) →
  ∀ (cK : ℂ) (ψ₀ : Matrix B.κ B.κ (Hf E B.a B.b → ℂ)),
  cK * (B.ν.real ((K₁.prod K₂ : Subgroup (Hf E B.a B.b)) : Set (Hf E B.a B.b)) : ℂ) = 1 →
  (∀ x y h, ψ₀ x y h = if x = y ∧ h ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)) then cK else 0) →
  (∀ (A : Type) (f : A × B.κ → H E B.a B.b → ℂ), (∀ i, ∀ u ∈ K₁.prod K₂, ∀ x, f i (x * finH u) = f i x) →
    convF B.ν ψ₀ f = f ∧ ∀ ψ : Matrix B.κ B.κ (Hf E B.a B.b → ℂ), IsFinM ψ → convF B.ν (mulF B.ν ψ ψ₀) f = convF B.ν ψ f) ∧
  ∀ ψ : Matrix B.κ B.κ (Hf E B.a B.b → ℂ), IsFinM ψ →
    ∀ x y, ∀ u ∈ K₁.prod K₂, ∀ h, mulF B.ν ψ ψ₀ x y (h * u) = mulF B.ν ψ ψ₀ x y h

def RealiseSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E) (Γ : Type) [Countable Γ]
  (g : Γ → BGen B) (a₀ : Γ) (t₀ : PT B) (X : B.Hb →L[ℂ] B.Hb) (tX : PT B) (χ : ChAlg g X →⋆ₐ[ℂ] ℂ),
  (∀ x, (g x).Ok) → tX.Ok → X = tX.op → g a₀ = Sum.inr t₀ →
  (∀ x y, Commute (g x).op (g y).op ∧ Commute (g x).op (star (g y).op)) →
  (∀ x, Commute X (g x).op ∧ Commute X (star (g x).op)) → IsSelfAdjoint X →
  (∀ y, ‖χ y‖ ≤ ‖(y : B.Hb →L[ℂ] B.Hb)‖) → χ (genE g X a₀) ≠ 0 →
  ∃ (M : ℕ) (s : ℕ → ChAlg g X → ℂ) (f : ℕ → B.I → H E B.a B.b → ℂ),
    (∀ y, Tendsto (fun k => s k (genE g X y)) atTop (𝓝 (χ (genE g X y)))) ∧
    Tendsto (fun k => s k (XE g X)) atTop (𝓝 (χ (XE g X))) ∧
    ∀ k, s k (genE g X a₀) ≠ 0 ∧ (∀ i, Continuous (f k i)) ∧ f k ≠ 0 ∧ LeftInv (f k) ∧ WL2 B.D M (f k) ∧
      PositivityTheory.Rg.BcB.E.conv B.D.μ t₀.Φ (f k) = s k (genE g X a₀) • f k ∧
      (∀ y (t : PT B), g y = Sum.inr t → PositivityTheory.Rg.BcB.E.conv B.D.μ (mulM B.D.μ t.Φ t₀.Φ) (f k) =
        (s k (genE g X y) * s k (genE g X a₀)) • f k) ∧
      PositivityTheory.Rg.BcB.E.conv B.D.μ (mulM B.D.μ tX.Φ t₀.Φ) (f k) = (s k (XE g X) * s k (genE g X a₀)) • f k

end PositivityTheory.Rg.BcB.F.Rd.B

end
end
