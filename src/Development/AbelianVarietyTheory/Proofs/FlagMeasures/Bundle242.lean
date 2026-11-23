module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle103
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle187
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle206
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle046
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle081
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle143
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle231
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle163
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselRootDilationNormalizesContractsUnipotent
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompactStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle164
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometryOpNormBoundedByTwoFrames
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle232
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle167
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle233
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeGaussianSumOfLengthEqTsumStabilizerCosets
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.MassGlue

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ}


omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem sumCls_le (S : Frames L r k) (φ : Set S.FrP → ℝ≥0∞) (c : ℝ≥0∞) (h : ∀ C, φ C ≤ c) :
    S.sumCls φ ≤ (S.sumCls fun _ => 1) * c := by
  unfold Frames.sumCls
  rw [← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun o => ?_
  split_ifs
  · rw [mul_one]
    gcongr
    exact h _
  · simp

theorem mass_le (S : Frames L r k) (d : S.Datum) (j : ℕ) :
    (S.mass d fun Λ => S.cardI d Λ = j) ≤
      ENNReal.ofReal (S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (j : ℝ) ^ (k - 1)) := by
  by_cases hex : ∃ Λ, S.IsTerm d Λ
  · obtain ⟨Λ₀, h₀⟩ := hex
    have hH : 1 ≤ S.Hp := (GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ₀ h₀).2.2.2.2.1
    rw [GlobalTheory.T.hermitianMass_eq_sum_frameClasses L r k S d _ (fun h hh Λ hT hP => by
      rw [(GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d Λ hT h hh).2.2.2.2.2.2.1]; exact hP)]
    refine (sumCls_le S _ _ fun C => GlobalTheory.T.hermitianTermCount_frameClass_le L r k S d C j).trans ?_
    refine (mul_le_mul_left (GlobalTheory.T.hermitianFrameClasses_total_weight_le L r k S ⟨d, Λ₀, h₀⟩) _).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← mul_assoc, ← pow_add]
    refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hH ?_) (by positivity)
    omega
  · have : (S.mass d fun Λ => S.cardI d Λ = j) = 0 := by
      unfold Frames.mass
      refine ENNReal.tsum_eq_zero.2 fun o => if_neg fun h => hex ⟨_, h.1⟩
    rw [this]
    exact zero_le

theorem finite_fibre (S : Frames L r k) (d : S.Datum) (C : Set S.FrP) :
    {Λ | S.IsTerm d Λ ∧ S.Fr d Λ = C}.Finite := by
  have h1 : ∀ j : ℕ, {Λ | S.IsTerm d Λ ∧ S.cardI d Λ = j ∧ S.Fr d Λ = C}.Finite := fun j => by
    have h := (GlobalTheory.T.hermitianTermCount_frameClass_le L r k S d C j).trans_lt ENNReal.ofReal_lt_top
    unfold Frames.nT at h
    rw [← Set.encard_lt_top_iff]
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    rw [hc] at h
    simp at h
  refine ((Set.finite_Iic S.a.toNat).biUnion fun i _ =>
    (Set.finite_Iic (S.q ^ i)).biUnion fun j _ => h1 j).subset ?_
  rintro Λ ⟨hT, hC⟩
  obtain ⟨i, hi, hb⟩ := (GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT).2.2.2.2.2.1
  have h2 := (GlobalTheory.T.gluingImage_card_pow_le_defectGroup_card L r k S d Λ hT).2.1
  simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_setOf_eq]
  exact ⟨i, by omega, S.cardI d Λ, hb ▸ h2, hT, rfl, hC⟩

theorem finite_cls (S : Frames L r k) (h : ∃ d Λ, S.IsTerm d Λ) :
    {o : MulAction.orbitRel.Quotient S.St (Set S.FrP) | S.IsIntCls o.out}.Finite := by
  have h1 := ((GlobalTheory.T.hermitianFrameClasses_total_weight_le L r k S h).trans_lt ENNReal.ofReal_lt_top).ne
  unfold Frames.sumCls at h1
  refine (ENNReal.finite_const_le_of_tsum_ne_top h1 (ε := 1) one_ne_zero).subset fun o ho => ?_
  have ho' : S.IsIntCls o.out := ho
  simp only [Set.mem_setOf_eq, if_pos ho', mul_one]
  exact ENNReal.one_le_ofReal.2 ((GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).2 _ ho'.1).2.2.1

theorem finite_orbits (S : Frames L r k) (d : S.Datum) :
    {o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V) | S.IsTerm d o.out}.Finite := by
  by_cases hex : ∃ Λ, S.IsTerm d Λ
  · obtain ⟨Λ₀, h₀⟩ := hex
    refine (((finite_cls S ⟨d, Λ₀, h₀⟩).biUnion fun o _ => finite_fibre S d o.out).image
      (fun Λ => (Quotient.mk _ Λ : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V)))).subset ?_
    intro o ho
    have hT : S.IsTerm d o.out := ho
    let o' : MulAction.orbitRel.Quotient S.St (Set S.FrP) := Quotient.mk _ (S.Fr d o.out)
    obtain ⟨h, hh⟩ : o'.out ∈ MulAction.orbit S.St (S.Fr d o.out) :=
      MulAction.orbitRel_apply.1 (Quotient.mk_out (s := MulAction.orbitRel S.St (Set S.FrP)) _)
    have hA := GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d _ hT h.1 h.2
    have hF : S.Fr d (h.1 • o.out) = o'.out := hA.2.2.2.2.1.trans hh
    refine ⟨h.1 • o.out, ?_, ?_⟩
    · simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨o', hF ▸ (GlobalTheory.HL.TermBasic.term_basic L r k S d _ hA.1).2.2.2.2.2.2.1, hA.1, hF⟩
    · refine Eq.trans ?_ (Quotient.out_eq o)
      exact Quotient.sound (MulAction.orbitRel_apply.2 ⟨h, rfl⟩)
  · refine Set.finite_empty.subset fun o ho => hex ⟨_, ho⟩

end GlobalTheory.HL.MassGlue

theorem GlobalTheory.HL.MassGlue.mass_le_and_finite : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 1 ≤ k → ∀ d : S.Datum, (∀ j : ℕ, (S.mass d fun Λ => S.cardI d Λ = j) ≤ ENNReal.ofReal (S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (j : ℝ) ^ (k - 1))) ∧ {o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V) | S.IsTerm d o.out}.Finite := by
  intro F _ _ _ _ _ E _ _ _ L r k S _ d
  exact ⟨GlobalTheory.HL.MassGlue.mass_le S d, GlobalTheory.HL.MassGlue.finite_orbits S d⟩
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.TraceRep

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E}

theorem hf_add {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_sub {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L Hm (a - b) y = hf L Hm a y - hf L Hm b y := by
  simp [hf, sub_mul, Finset.sum_sub_distrib]

theorem hf_smul {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    hf L Hm (c • a) y = c * hf L Hm a y := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_zero {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (y : Fin n → E) :
    hf L Hm 0 y = 0 := by
  simp [hf]

theorem hf_neg_right {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a y : Fin n → E) :
    hf L Hm a (-y) = - hf L Hm a y := by
  simp [hf, Finset.sum_neg_distrib]

theorem hf_swap {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm) (v w : Fin n → E) :
    hf L Hm w v = L.cj (hf L Hm v w) := by
  have h' : ∀ i j, L.cj (Hm j i) = Hm i j := fun i j => congrFun (congrFun h i) j

  simp only [hf, map_sum, map_mul, L.cj_cj, h']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_swap_zero {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm) {v w : Fin n → E}
    (h0 : hf L Hm v w = 0) : hf L Hm w v = 0 := by
  rw [hf_swap h, h0, map_zero]

variable {r k : ℕ} (S : Frames L r k)

theorem frame_perp (g : Fin (r + 1) → S.V) (T : E)
    (hg : ∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then T else 0)
    (n : S.GLV) (hn : n ∈ S.Nof g) (b : Fin (r + 1)) :
    n (g b) ∈ perp L S.Hm (S.spanTo g r) := by
  refine (hn.2.1 (g b)).2 ?_
  intro y hy
  apply hf_swap_zero S.herm.1
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := hy
    rw [hg, if_neg]
    rintro ⟨rfl, -⟩
    simp at hi
  | zero => exact hf_zero _ _
  | add a c _ _ ha hc => rw [hf_add, ha, hc, add_zero]
  | smul c a _ ha => rw [hf_smul, ha, mul_zero]

theorem spanTo_mono (g : Fin (r + 1) → S.V) {i j : ℕ} (h : i ≤ j) : S.spanTo g i ≤ S.spanTo g j :=
  Submodule.span_mono (Set.image_mono fun _ ha => lt_of_lt_of_le ha h)

theorem mof_transport (Λ : Submodule L.O S.V) (Y : Submodule E S.V) (g g' g₁ g₁' : Fin (r + 1) → S.V)
    (x x' u : S.V) (h1 : ∀ b, g₁ b = g b - S.h (g b) u • x) (h1' : ∀ b, g₁' b = g' b + S.h (g' b) u • x')
    (hO : ∀ b, S.h (g' b) u ∈ L.O) (hΛ : algebraMap F E S.th⁻¹ • (x + x') ∈ Λ) (hY : x + x' ∈ Y)
    (m : S.V) (hm : m ∈ S.Mof g g') :
    ∃ y₁ ∈ Λ, y₁ ∈ Y ∧ m - S.h m u • x + y₁ ∈ S.Mof g₁ g₁' := by
  induction hm using Submodule.span_induction with
  | mem m hm =>
    rcases hm with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · refine ⟨0, Λ.zero_mem, Y.zero_mem, ?_⟩
      rw [add_zero, ← h1]
      exact Submodule.subset_span (Or.inl ⟨b, rfl⟩)
    · refine ⟨S.h (g' b) u • (algebraMap F E S.th⁻¹ • (x + x')), Λ.smul_mem ⟨_, hO b⟩ hΛ,
        Y.smul_mem _ (Y.smul_mem _ hY), ?_⟩
      have : algebraMap F E S.th⁻¹ • (g' b - g b) - S.h (algebraMap F E S.th⁻¹ • (g' b - g b)) u • x +
          S.h (g' b) u • (algebraMap F E S.th⁻¹ • (x + x')) = algebraMap F E S.th⁻¹ • (g₁' b - g₁ b) := by
        rw [h1, h1']
        simp only [Frames.h, hf_smul, hf_sub]
        module
      simp only []
      rw [this]
      exact Submodule.subset_span (Or.inr ⟨b, rfl⟩)
  | zero =>
    refine ⟨0, Λ.zero_mem, Y.zero_mem, ?_⟩
    simp [Frames.h, hf_zero]
  | add a c _ _ ha hc =>
    obtain ⟨y, hy, hy', ha⟩ := ha
    obtain ⟨z, hz, hz', hc⟩ := hc
    refine ⟨y + z, Λ.add_mem hy hz, Y.add_mem hy' hz', ?_⟩
    have : a + c - S.h (a + c) u • x + (y + z) = (a - S.h a u • x + y) + (c - S.h c u • x + z) := by
      simp only [Frames.h, hf_add]
      module
    rw [this]
    exact Submodule.add_mem _ ha hc
  | smul c a _ ha =>
    obtain ⟨y, hy, hy', ha⟩ := ha
    refine ⟨(c : E) • y, Λ.smul_mem c hy, Y.smul_mem _ hy', ?_⟩
    have : c • a - S.h (c • a) u • x + (c : E) • y = (c : E) • (a - S.h a u • x + y) := by
      change (c : E) • a - S.h ((c : E) • a) u • x + (c : E) • y = _
      simp only [Frames.h, hf_smul]
      module
    rw [this]
    exact Submodule.smul_mem _ c ha

theorem th_ne : S.th ≠ 0 := by
  unfold Frames.th
  split_ifs
  · intro h
    exact S.ϖ_irr.ne_zero (Subtype.ext h)
  · exact one_ne_zero

end GlobalTheory.HL.TraceRep


open GlobalTheory.HL.TraceRep in
theorem GlobalTheory.HL.TraceRep.class_from_trace : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → (∃ y ∈ Λ, y ∈ S.W0 ∧ S.h u y = 1) → ∀ Λ₁ : Submodule L.O S.V, (Λ₁ : Set S.V) = S.moved Λ x u s → ∀ y ∈ S.sat Λ₁, ∃ y₀ ∈ Λ, y₀ ∈ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)) ∧ y - y₀ ∈ S.M d Λ₁ := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hF x x' u s hmv hw Λ₁ hΛ₁ y hy
  obtain ⟨w, hwΛ, hwW, huw⟩ := hw
  obtain ⟨hsx, -, -, -, -, -, -, hux, hux', hxX, hxX'⟩ :=
    GlobalTheory.T.hermitianDoubleCosetFrames_datum_move_properties L r k S j β βJ d Λ hT hF x x' u s hmv
  obtain ⟨n₀, hn₀, n₀', hn₀', n'', hn'', -, e1, e2, e3, e4, hW₁⟩ :=
    GlobalTheory.T.move_lattice_isTerm_same_datum_with_witnesses L r k S j β βJ d Λ hT hF x x' u s hmv
  obtain ⟨hSD, hW, hMs, -, hf', -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  have hlev := (GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT).2.2.2.2.2.2.2.2.2.2
  have hΛe : n₀⁻¹ • Λ = Λ₁ := SetLike.coe_injective (e4.trans hΛ₁.symm)
  rw [hΛe] at hW₁
  have hM₁ := (GlobalTheory.HL.WitIndep.witness_independence L r k S d Λ₁ _ _ hW₁).2.1
  obtain ⟨hx, hx', ⟨t, ht, hte⟩, -, huΛ, huY, -⟩ := hmv
  have hH := S.herm.1
  have hint : ∀ a ∈ Λ, ∀ b ∈ Λ, S.h a b ∈ L.O := fun a ha b hb => (hSD.2 b).2 hb a ha
  have hp := frame_perp S S.f _ S.gram _ hW.2.2.1
  have hp' := frame_perp S S.f' _ S.gram' _ hW.2.2.2.1
  have hxME : x ∈ S.ME :=
    Submodule.mem_sup_left (spanTo_mono S S.f (Nat.le_succ r) hxX)
  have hyME : y ∈ S.ME := hy.2
  have hyΛ : eich L S.Hm x u s y ∈ Λ := by
    have : y ∈ (Λ₁ : Set S.V) := hy.1
    rw [hΛ₁] at this
    exact this
  have hκ : hf L S.Hm y x ∈ L.O := by
    have h1 := hint _ hyΛ _ hwΛ
    have h2 : hf L S.Hm y w = 0 := hf_swap_zero hH (hwW y hyME)
    have h3 : hf L S.Hm x w = 0 := hf_swap_zero hH (hwW x hxME)
    have h4 : hf L S.Hm u w = 1 := huw
    simp only [Frames.h, eich, hf_sub, hf_add, hf_smul, h2, h3, h4] at h1
    have := L.O.neg_mem h1
    simpa using this
  have hbΛ : y + hf L S.Hm y u • x ∈ Λ := by
    have : y + hf L S.Hm y u • x = eich L S.Hm x u s y + hf L S.Hm y x • (u + s • x) := by
      simp [eich]
    rw [this]
    exact Λ.add_mem hyΛ (Λ.smul_mem ⟨_, hκ⟩ (Λ.add_mem huΛ hsx))
  have hbs : y + hf L S.Hm y u • x ∈ S.sat Λ :=
    ⟨hbΛ, S.ME.add_mem hyME (S.ME.smul_mem _ hxME)⟩
  obtain ⟨y₀, hy₀Y, hm⟩ := (hlev _ hbs (j + 1)).1 (hF.2.2.1 _ hbs)
  have hy₀Λ : y₀ ∈ Λ := by
    have := Λ.sub_mem hbΛ (hMs hm).1
    simpa using this
  have hfrΛ : ∀ b, S.fr' d Λ b ∈ Λ := fun b =>
    (hf' (r + 1) le_rfl _).2 (Submodule.subset_span ⟨b, b.2, rfl⟩) |>.1
  have hth : algebraMap F E S.th⁻¹ • (x + x') ∈ Λ := by
    rw [hte, smul_smul, ← map_mul, inv_mul_cancel₀ (th_ne S), map_one, one_smul]
    exact ht
  obtain ⟨y₁, hy₁Λ, hy₁Y, hm₁⟩ := mof_transport S Λ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1))
    (S.fr d Λ) (S.fr' d Λ) (fun b => (n₀⁻¹ * (S.wit d Λ).1) (S.f b))
    (fun b => (n'' * n₀' * (S.wit d Λ).2) (S.f' b)) x x' u
    (fun b => by
      change n₀⁻¹ (S.fr d Λ b) = _
      have h0 : hf L S.Hm (S.fr d Λ b) x = 0 := hp b x hxX
      rw [e1, eich, h0, hf_neg_right]
      simp [Frames.h, sub_eq_add_neg])
    (fun b => by
      change n'' (n₀' (S.fr' d Λ b)) = _
      have h0 : hf L S.Hm (S.fr' d Λ b) x' = 0 := hp' b x' hxX'
      rw [e3 (n₀' (S.fr' d Λ b)) ((hn₀'.2.1 _).2 (hp' b)), e2, eich, h0]
      simp [Frames.h])
    (fun b => hint _ (hfrΛ b) _ huΛ) hth (Submodule.add_mem_sup hx hx') _ hm
  refine ⟨y₀ - y₁, Λ.sub_mem hy₀Λ hy₁Λ, Submodule.sub_mem _ hy₀Y hy₁Y, ?_⟩
  rw [hM₁]
  have h5 : hf L S.Hm x u = 0 := hf_swap_zero hH hux
  have h6 : hf L S.Hm y₀ u = 0 := hf_swap_zero hH (huY y₀ hy₀Y)
  have : y - (y₀ - y₁) = y + hf L S.Hm y u • x - y₀ - S.h (y + hf L S.Hm y u • x - y₀) u • x + y₁ := by
    simp only [Frames.h, hf_sub, hf_add, hf_smul, h5, h6]
    module
  rw [this]
  exact hm₁
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.besselRootDilation_normalizes_contracts_unipotent : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → (∀ τ : ℝ, 0 < τ → dil k r τ ∈ GG k r ∧ (∀ h ∈ UWset k r z, dil k r τ * h = h * dil k r τ) ∧ (∀ m ∈ Nset k r, dil k r τ * m * (dil k r τ)⁻¹ ∈ Nset k r ∧ (dil k r τ)⁻¹ * m * dil k r τ ∈ Nset k r)) ∧ (∀ τ : ℝ, 1 ≤ τ → ∀ m ∈ Nset k r, ∀ i j, ‖((dil k r τ)⁻¹ * m * dil k r τ - 1) i j‖ ≤ τ⁻¹ * ‖(m - 1) i j‖) := by
  first | exact @GlobalTheory.SgInf.Dilation.main | exact GlobalTheory.SgInf.Dilation.main | (intros; apply GlobalTheory.SgInf.Dilation.main <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf

variable {k r : ℕ}

def oneM (k r : ℕ) : Mt k r := fun i j => (1 : Mat k r) i j

def nbd (k r : ℕ) (j : ℕ) : Set (Mt k r) := Metric.closedBall (oneM k r) (1 / ((j : ℝ) + 1))

def avgR {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℝ Wp] (μ : Measure (Mt k r)) (j : ℕ)
    (g : Mt k r → Wp) (x : Mt k r) : Wp :=
  ((μ (nbd k r j)).toReal)⁻¹ • ∫ y in nbd k r j, g (rmulM (Matrix.of x) y) ∂μ

theorem isCompact_nbd (j : ℕ) : IsCompact (nbd k r j) := by
  unfold nbd
  exact isCompact_closedBall _ _

theorem oneM_mem_nbd (j : ℕ) : oneM k r ∈ nbd k r j := by
  unfold nbd
  exact Metric.mem_closedBall_self (by positivity)

private lemma single_mem_inWb_and_Tz_pos (k r : ℕ) :
    Formalism.QuantumDeterminants.inWb k r (Pi.single (⟨r + k, by omega⟩ : Fin (2 * r + k + 1)) 1) ∧
      0 < Formalism.QuantumDeterminants.Tz k r (Pi.single (⟨r + k, by omega⟩ : Fin (2 * r + k + 1)) 1) := by
  constructor
  · intro i hi
    have hne : i ≠ ⟨r + k, by omega⟩ := by
      rintro rfl
      simp at hi
    simp [hne]
  · simp only [Formalism.QuantumDeterminants.Tz, Formalism.QuantumDeterminants.herm, Formalism.QuantumDeterminants.Hpk, dotProduct, mulVec, Pi.single_apply,
      Pi.star_apply, Complex.re_sum, neg_pos]
    rw [Finset.sum_eq_single (⟨r + k, by omega⟩ : Fin (2 * r + k + 1))]
    · have h1 : ¬ (r + k < r) := by omega
      simp [h1, Finset.sum_ite_eq']
    · intro b _ hb
      simp [hb]
    · simp

theorem gg_closedSub (k r : ℕ) : IsClosedSub k r (GG k r) :=
  (GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r _ (single_mem_inWb_and_Tz_pos k r).1 (single_mem_inWb_and_Tz_pos k r).2).1

theorem haar_compact_lt_top {μ : Measure (Mt k r)} (hμ : IsHaarOn (GG k r) μ) {C : Set (Mt k r)}
    (hC : IsCompact C) : μ C < ⊤ :=
  (GlobalTheory.T.closedSubgroupBessel_haar_finite_compact_pos_open k r (GG k r) μ (gg_closedSub k r) hμ).1 C hC

theorem nbd_pos {μ : Measure (Mt k r)} (hμ : IsHaarOn (GG k r) μ) (j : ℕ) : 0 < μ (nbd k r j) := by
  have h1 : Matrix.of (oneM k r) = (1 : Mat k r) := by
    ext a b
    simp [oneM]
  have hone : Matrix.of (oneM k r) ∈ GG k r := by
    rw [h1]
    exact (gg_closedSub k r).2.2.1
  have hU := (GlobalTheory.T.closedSubgroupBessel_haar_finite_compact_pos_open k r (GG k r) μ (gg_closedSub k r) hμ).2
    (Metric.ball (oneM k r) (1 / ((j : ℝ) + 1))) Metric.isOpen_ball
    ⟨oneM k r, Metric.mem_ball_self (by positivity), hone⟩
  unfold nbd
  exact lt_of_lt_of_le hU (measure_mono Metric.ball_subset_closedBall)

end GlobalTheory.SgInf
end
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.weil_formula_besselUnitary_integrable : ∀ (k r : ℕ) (S : Set (Mat k r)) (μG μS ν : Measure (Mt k r)), IsClosedSub k r S → IsHaarOn (GG k r) μG → IsHaarOn S μS → IsUnimod S μS → IsQuotMeas μG μS ν → SigmaFinite ν ∧ ν {x | Matrix.of x ∉ GG k r} = 0 ∧ μG = (ν.prod μS).map (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2) p.1) ∧ (∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B] (f : Mt k r → B), Integrable f μG → Integrable (fun x => ∫ s, f (lmulM (Matrix.of s) x) ∂μS) ν ∧ ∫ x, f x ∂μG = ∫ x, (∫ s, f (lmulM (Matrix.of s) x) ∂μS) ∂ν) ∧ (∀ F : Mt k r → ENNReal, Measurable F → (∀ s ∈ S, ∀ x, F (lmulM s x) = F x) → ∀ y ∈ GG k r, ∫⁻ x, F (rmulM y x) ∂ν = ∫⁻ x, F x ∂ν) := by
  first | exact @GlobalTheory.SgInf.weil_integrable | exact GlobalTheory.SgInf.weil_integrable | (intros; apply GlobalTheory.SgInf.weil_integrable <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.isometry_opNorm_bounded_by_two_frames : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (C : Set (Mat k r)), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsCompact C → (∀ γ ∈ C, γ ∈ GG k r ∧ Gf k r z z' γ ≠ 0) → ∃ C0 : ℝ, ∀ γ ∈ C, ∀ s ∈ GG k r, ∀ B : ℝ, 1 ≤ B → (∀ i, eucl (s *ᵥ gramVec k r z z' γ i) ≤ B) → opn s ≤ C0 * B ^ 2 := by
  first | exact @GlobalTheory.SgInf.isom_frame_bound | exact GlobalTheory.SgInf.isom_frame_bound | (intros; apply GlobalTheory.SgInf.isom_frame_bound <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.twoFlagsGramNumber_and_fibre_sets_measurable : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (γ : Mat k r), γ ∈ GG k r → Measurable (Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r} fun x => Yv k r z z' γ (Matrix.of x)) ∧ ∀ R₀ y : ℝ, MeasurableSet (Eset k r z z' γ R₀ y) := by
  first | exact @GlobalTheory.Amp.YMeas.yv_measurable | exact GlobalTheory.Amp.YMeas.yv_measurable | (intros; apply GlobalTheory.Amp.YMeas.yv_measurable <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_orthComplement_unitVector_same_fields : ∀ (I I' : AutInst) (e : I'.E ≃+* I.E) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E) (xf : I.Gf), IsPerpInst I I' e s x A xf → ∃ (D : Sib I) (B : Matrix (Fin I.n) (Fin D.n) I.E), IsPerp D s x B xf ∧ ∀ (c : InfinitePlace I.F → ℝ) (μ : Measure D.inst.Gf) [SigmaFinite μ] [μ.IsHaarMeasure] (c' : InfinitePlace I'.F → ℝ) (μ' : Measure I'.Gf) [SigmaFinite μ'] [μ'.IsHaarMeasure], IsGaugeAll D.inst c → IsGaugeAll I' c' → gaugeVol D.inst c μ = gaugeVol I' c' μ' := by
  first | exact @GlobalTheory.PerpReduce.exists_sib | exact GlobalTheory.PerpReduce.exists_sib | (intros; apply GlobalTheory.PerpReduce.exists_sib <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

theorem _root_.GlobalTheory.T.latticeGaussianSumOfLength_eq_tsum_stabilizer_cosets : ∀ (I : AutInst) (s : Bool) (x : Fin I.n → I.E), star x ⬝ᵥ (I.J *ᵥ x) = sgn I.E s → ∃ (ι : Type) (_ : Countable ι) (r : ι → I.GA), (∀ i, r i ∈ I.GFset) ∧ (∀ γ ∈ I.GFset, ∃! i, γ * (r i)⁻¹ ∈ stabF I x) ∧ ∀ g, gaussSum I (sgn I.E s) g = ∑' i, gaussAt I x (r i * g) := by
  first | exact @GlobalTheory.StabCosets.gaussSum_cosets | exact GlobalTheory.StabCosets.gaussSum_cosets | (intros; apply GlobalTheory.StabCosets.gaussSum_cosets <;> assumption)
end
