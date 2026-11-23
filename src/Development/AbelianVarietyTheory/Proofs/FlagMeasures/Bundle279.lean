module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle097
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle163
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle046
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle270
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeCountBoundFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RmulMul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle222
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle122
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle198
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsFolnerUWset
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupRepTwistedIsUnitaryRepStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularBesselSubgroupsUWNStatement
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle272
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle274
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle143
public import Formalism.PeriodIntegrals.UpqRep
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle273
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
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
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.GenMass

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ}


omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem pair_mem_cls (S : Frames L r k) (g g' : Fin (r + 1) → S.V) : (g, g') ∈ S.frameCls g g' := by
  have h1 : IsIntM L (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) := fun i j => by
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  refine ⟨1, 1, h1, h1, fun i j h => ?_, fun i => by simp, fun i j => ⟨0, zero_mem _, by simp⟩,
    fun j => ?_, fun j => ?_⟩
  · simp [Matrix.one_apply_ne h.ne']
  · simp [Matrix.one_apply]
  · simp [Matrix.one_apply]


omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem sumCls_le (S : Frames L r k) (φ : Set S.FrP → ℝ≥0∞) (c : ℝ≥0∞) (h : ∀ C, S.IsCls C → φ C ≤ c) :
    S.sumCls φ ≤ (S.sumCls fun _ => 1) * c := by
  unfold Frames.sumCls
  rw [← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun o => ?_
  split_ifs with ho
  · rw [mul_one]
    gcongr
    exact h _ ho.1
  · simp

theorem q_pow_le (S : Frames L r k) (e : ℤ) (he0 : 0 ≤ e) (he : e ≤ S.vth + S.a + S.vD) (m : ℕ) :
    (S.q : ℝ≥0∞) ^ (m * e.toNat) ≤ ENNReal.ofReal (S.Hp ^ m) := by
  have hq : 2 ≤ S.q := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
  have hq1 : (1 : ℝ) ≤ S.q := by exact_mod_cast (by omega : 1 ≤ S.q)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_comm, pow_mul]
  refine pow_le_pow_left₀ (by positivity) ?_ _
  rw [← zpow_natCast, Int.toNat_of_nonneg he0]
  exact zpow_le_zpow_right₀ hq1 he

omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem vth_nonneg (S : Frames L r k) : 0 ≤ S.vth := by
  unfold Frames.vth
  split_ifs <;> norm_num

theorem total_weight_le (S : Frames L r k) (ha : 0 ≤ S.a) (hD : 0 ≤ S.vD) :
    (S.sumCls fun _ => 1) ≤ ENNReal.ofReal (S.Hp ^ (r * (r + 1))) := by
  have hv := vth_nonneg S
  exact ((GlobalTheory.HL.ClassCount.sumCls_le_encard L r k S).trans (GlobalTheory.IntClsCount.main L r k S hD)).trans
    (q_pow_le S _ (by omega) (by omega) _)

theorem sumCls_eq_single (S : Frames L r k) (h1 : (S.sumCls fun _ => 1) ≤ 1) (φ : Set S.FrP → ℝ≥0∞)
    (hφ : ∀ h ∈ S.St, ∀ C, φ (h • C) = φ C) (C : Set S.FrP) (hC : S.IsIntCls C) :
    S.sumCls φ = ENNReal.ofReal (S.wC C) * φ C := by
  let o' : MulAction.orbitRel.Quotient S.St (Set S.FrP) := Quotient.mk _ C
  obtain ⟨h, hh⟩ : o'.out ∈ MulAction.orbit S.St C :=
    MulAction.orbitRel_apply.1 (Quotient.mk_out (s := MulAction.orbitRel S.St (Set S.FrP)) _)
  have hh' : h.1 • C = o'.out := hh
  have ho' : S.IsIntCls o'.out := hh' ▸ GlobalTheory.HL.ClassCount.isIntCls_smul S h.2 hC
  unfold Frames.sumCls at h1 ⊢
  rw [tsum_eq_single o', if_pos ho', ← hh', hφ _ h.2, ((GlobalTheory.HL.volSt L r k S).2 C hC.1).2.2.2 _ h.2]
  intro o hne
  refine if_neg fun ho => ?_
  have h2 := (ENNReal.sum_le_tsum {o, o'}).trans h1
  rw [Finset.sum_pair hne, if_pos ho, if_pos ho', mul_one, mul_one] at h2
  have h3 := ENNReal.one_le_ofReal.2 ((GlobalTheory.HL.volSt L r k S).2 _ ho.1).2.2.1
  have h4 := ENNReal.one_le_ofReal.2 ((GlobalTheory.HL.volSt L r k S).2 _ ho'.1).2.2.1
  have h5 := (add_le_add h3 h4).trans h2
  norm_num at h5

end GlobalTheory.HL.GenMass


open GlobalTheory.HL.GenMass in
theorem GlobalTheory.HL.GenMass.total_le_generic : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ d₁ Λ₁, S.IsTerm d₁ Λ₁ → ∀ g : ℝ≥0∞, g = ENNReal.ofReal (S.wC (S.Fr d₁ Λ₁)) * (S.sumData fun d => S.nT d (S.Fr d₁ Λ₁) fun Λ => S.BBzero d Λ) → 0 < g ∧ g < ⊤ ∧ S.nn ≤ ENNReal.ofReal (8 * S.Hp ^ (9 * (r + 1) ^ 2 + 2 * (2 * r + 2))) * g ∧ (S.Hp = 1 → S.nn = g) := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk d₁ Λ₁ hT g hg
  obtain ⟨hSD, -, hMs, -, -, -, hI, -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d₁ Λ₁ hT
  obtain ⟨ha, hD, -, -, hH, -⟩ := GlobalTheory.HL.Defect.exponents_and_defect L r k S d₁ Λ₁ hT
  obtain ⟨κ, hκ, hU⟩ := GlobalTheory.T.selfDualHermitianLattice_mass_of_trace L r k S (by omega) ⟨Λ₁, hSD⟩
  have hv := vth_nonneg S
  have hp : (S.fr d₁ Λ₁, S.fr' d₁ Λ₁) ∈ S.Fr d₁ Λ₁ := pair_mem_cls S _ _
  have hsw := GlobalTheory.T.hermitianDataMass_eq_sum_frameClasses L r k S (fun _ _ => True) (fun _ _ _ _ _ _ => trivial)
  have hnn : S.nn = S.sumCls fun C => S.sumData fun d => S.nT d C fun _ => True := hsw.1
  have hM := hU _ hI.1 _ hp (S.M d₁ Λ₁) le_rfl (fun x hx => (hMs hx).2)
    (fun x hx y hy => (hSD.2 y).2 (hMs hy).1 x (hMs hx).1)
  have hM' : ENNReal.ofReal (κ / 2) ≤ S.massSig (S.M d₁ Λ₁) ∧
      S.massSig (S.M d₁ Λ₁) ≤ ENNReal.ofReal (2 * κ) := by
    simpa [Frames.M] using hM
  have hg' : g = ENNReal.ofReal (S.wC (S.Fr d₁ Λ₁)) * S.massSig (S.M d₁ Λ₁) := by
    rw [hg, (GlobalTheory.T.hermitianFrameClass_terms_le_overlattice_masses L r k S _ hI.1 _ hp).2]
    rfl
  have hw := ENNReal.one_le_ofReal.2 ((GlobalTheory.HL.volSt L r k S).2 _ hI.1).2.2.1
  have hlow : ENNReal.ofReal (κ / 2) ≤ g := by
    rw [hg', ← one_mul (ENNReal.ofReal (κ / 2))]
    exact mul_le_mul' hw hM'.1
  refine ⟨(ENNReal.ofReal_pos.2 (by positivity)).trans_le hlow, ?_, ?_, fun h1 => ?_⟩
  · rw [hg']
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hM'.2.trans_lt ENNReal.ofReal_lt_top)
  · have hφ : ∀ C, S.IsCls C → (S.sumData fun d => S.nT d C fun _ => True) ≤
        ENNReal.ofReal (S.Hp ^ (2 * (2 * r + 2))) * ENNReal.ofReal (2 * κ) := by
      intro C hC
      obtain ⟨p, hpC⟩ : ∃ p, p ∈ C := by
        obtain ⟨n, -, n', -, rfl⟩ := hC
        exact ⟨_, pair_mem_cls S _ _⟩
      refine ((GlobalTheory.T.hermitianFrameClass_terms_le_overlattice_masses L r k S C hC p hpC).1 fun _ => True).trans ?_
      refine (ENNReal.tsum_le_tsum (g := fun _ => ENNReal.ofReal (2 * κ)) fun Mh => ?_).trans ?_
      · refine (hU C hC p hpC Mh.1 Mh.2.1 Mh.2.2.1 Mh.2.2.2.1).2.trans (ENNReal.ofReal_le_ofReal ?_)
        refine mul_le_of_le_one_right (by positivity) ?_
        rw [← Nat.cast_pow]
        exact Nat.cast_inv_le_one _
      · have hc := GlobalTheory.FrameOver.encard_overlattices_le L r k S C hC p hpC ha
        have he : 2 * S.a.toNat * (2 * r + 2) = 2 * (2 * r + 2) * S.a.toNat := by ring
        rw [he] at hc
        have hc' := hc.trans (q_pow_le S _ ha (by omega) _)
        rw [ENNReal.tsum_const]
        refine mul_le_mul_left (le_trans (le_of_eq ?_) hc') _
        simp only [and_true]
        rfl
    rw [hnn]
    refine (sumCls_le S _ _ hφ).trans ?_
    refine (mul_le_mul_left (total_weight_le S ha hD) _).trans ?_
    refine le_trans ?_ (mul_le_mul_right hlow _)
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : S.Hp ^ (r * (r + 1)) * S.Hp ^ (2 * (2 * r + 2)) ≤
        S.Hp ^ (9 * (r + 1) ^ 2 + 2 * (2 * r + 2)) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ hH (by nlinarith)
    have h3 : 0 ≤ S.Hp ^ (9 * (r + 1) ^ 2 + 2 * (2 * r + 2)) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h2 hκ.le, mul_nonneg h3 hκ.le]
  · have hq : 2 ≤ S.q := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
    have hB : ∀ d Λ, S.IsTerm d Λ → S.BBzero d Λ := fun d Λ h => by
      by_contra hc
      have h2 := (GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ h).2.2.2.2.2.2.2.1 hc
      rw [h1] at h2
      have : S.q ≤ 1 := by exact_mod_cast h2
      omega
    have htw := total_weight_le S ha hD
    rw [h1, one_pow, ENNReal.ofReal_one] at htw
    rw [hnn, sumCls_eq_single S htw _ (fun h hh C => by simp only [hsw.2 h hh]) _ hI, hg]
    congr 2
    funext d
    unfold Frames.nT
    congr 2
    ext Λ
    exact ⟨fun h => ⟨h.1, hB _ _ h.1, h.2.2⟩, fun h => ⟨h.1, trivial, h.2.2⟩⟩
end

section

open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.RowLev NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TauNorm

theorem exists_bound {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] E) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ B, ‖L B‖ ≤ c * ∑ i, ∑ j, ‖B i j‖ := by
  classical
  set c : ℝ := ∑ i, ∑ j, ‖L (Matrix.single i j (1 : ℂ))‖ with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨c, hc0, fun B => ?_⟩
  have hB : L B = ∑ i, ∑ j, B i j • L (Matrix.single i j (1 : ℂ)) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single B]

    simp [map_sum, ← map_smul, Matrix.smul_single]
  have hle : ∀ i j, ‖L (Matrix.single i j (1 : ℂ))‖ ≤ c := fun i j =>
    (Finset.single_le_sum (f := fun j => ‖L (Matrix.single i j (1 : ℂ))‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, ‖L (Matrix.single i j (1 : ℂ))‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  rw [hB]
  calc ‖∑ i, ∑ j, B i j • L (Matrix.single i j (1 : ℂ))‖
      ≤ ∑ i, ∑ j, ‖B i j‖ * ‖L (Matrix.single i j (1 : ℂ))‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_smul _ _).le))
    _ ≤ ∑ i, ∑ j, ‖B i j‖ * c :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hle i j) (norm_nonneg _)
    _ = c * ∑ i, ∑ j, ‖B i j‖ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem exp_dOp_le {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ B, P * B * Q ≠ 0 → Real.exp (GlobalTheory.Count.dOp (P * B * Q)) ≤ c * ∑ i, ∑ j, ‖B i j‖ := by
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    { toFun := fun B => LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (P * B * Q))
      map_add' := fun B B' => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun a B => by simp }
  obtain ⟨c, hc, h⟩ := exists_bound L
  refine ⟨c, hc, fun B hB => ?_⟩
  have hpos : 0 < ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (P * B * Q))‖ := by
    rw [norm_pos_iff]
    intro h0
    apply hB
    have h1 : Matrix.toEuclideanLin (P * B * Q) = 0 :=
      LinearMap.toContinuousLinearMap.injective (h0.trans (map_zero _).symm)
    exact Matrix.toEuclideanLin.injective (h1.trans (map_zero _).symm)
  unfold GlobalTheory.Count.dOp
  rw [Real.exp_log hpos]
  exact h B

theorem exp_mean_le {ι : Type} [Fintype ι] [Nonempty ι] (d : ι → ℝ) (K : ℝ) (h : ∀ v, Real.exp (d v) ≤ K) :
    Real.exp ((∑ v, d v) / Fintype.card ι) ≤ K := by
  obtain ⟨v₀, hv₀⟩ := Finite.exists_max d
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hmean : (∑ v, d v) / Fintype.card ι ≤ d v₀ := by
    rw [div_le_iff₀ hcard]
    calc ∑ v, d v ≤ ∑ _v : ι, d v₀ := Finset.sum_le_sum fun v _ => hv₀ v
      _ = d v₀ * Fintype.card ι := by simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  exact (Real.exp_le_exp.2 hmean).trans (h v₀)

theorem card_places (I : AutInst) : Fintype.card (InfinitePlace I.F) = I.f := by
  have := I.cm.totReal
  have h1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank I.F
  have h2 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := I.F)
  rw [NumberField.IsTotallyReal.nrComplexPlaces_eq_zero] at h1 h2
  simp only [AutInst.f]
  omega

theorem inv_tau_mul_le (I : AutInst) (hn : 1 ≤ I.n) (x g : I.GA) (hg : g.2 = 1) (K : ℝ)
    (h : ∀ v, Real.exp (GlobalTheory.Count.dOp (uMat (g.1 v))) ≤ K) :
    (GlobalTheory.Count.tau1 I (x * g))⁻¹ ≤ (GlobalTheory.Count.tau1 I x)⁻¹ * K := by
  have hK1 : g.2 ∈ I.Kset := by
    rw [hg]
    show ((1 : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
    simp only [OneMemClass.coe_one]
    exact one_mem _
  have hlog := GlobalTheory.TauLipschitz.log_trunc_le I hn x g hK1
  have hx := GlobalTheory.TauLipschitz.trunc_pos I hn x
  have hxg := GlobalTheory.TauLipschitz.trunc_pos I hn (x * g)
  have hmean : Real.exp (GlobalTheory.Dec.dSum I g.1 / I.f) ≤ K := by
    have := exp_mean_le (fun v => GlobalTheory.Count.dOp (uMat (g.1 v))) K h
    rw [card_places] at this
    simpa only [GlobalTheory.Dec.dSum] using this
  have hdiv : GlobalTheory.Count.tau1 I x / GlobalTheory.Count.tau1 I (x * g) ≤ K := by
    rw [← Real.exp_log (div_pos hx hxg), Real.log_div hx.ne' hxg.ne']
    exact (Real.exp_le_exp.2 (by linarith)).trans hmean
  rw [inv_mul_eq_div, le_div_iff₀ hx, inv_mul_eq_div]
  exact hdiv

theorem sum_le_normInf {D : D7} {V : HSp D}
    (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (g : GA D V) (τ : D.what₂.Tau) :
    ∑ i, ∑ j, ‖Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g i j‖ ≤ normInf θ V g := by
  unfold Formalism.L2.Theta.normInf
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun τ => ∑ i, ∑ j, (‖Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g i j‖ +
      ‖Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖))
    (fun _ _ => by positivity) (Finset.mem_univ τ))
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    le_add_of_nonneg_right (norm_nonneg _)

theorem uMat_ne_zero (I : AutInst) (hn : 1 ≤ I.n) (g : I.GA) (v : InfinitePlace I.F) : uMat (g.1 v) ≠ 0 := by
  have : Nonempty (Fin I.n) := ⟨⟨0, hn⟩⟩
  exact Units.ne_zero _

end GlobalTheory.TauNorm
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.Equivar

theorem rmulM_emb {k r : ℕ} {t : Mat k r} (ht : IsUnit t.det) :
    MeasurableEmbedding (rmulM t : Mt k r → Mt k r) := by
  let e : Mt k r ≃ₜ Mt k r :=
    { toFun := rmulM t
      invFun := rmulM t⁻¹
      left_inv := fun x => Matrix.mul_nonsing_inv_cancel_right t (Matrix.of x) ht
      right_inv := fun x => Matrix.nonsing_inv_mul_cancel_right t (Matrix.of x) ht
      continuous_toFun := continuous_rmulM t
      continuous_invFun := continuous_rmulM t⁻¹ }
  exact e.measurableEmbedding

theorem integral_comp_both {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A A' : E →L[ℂ] E) (B B' : F →L[ℂ] F) (h1 : A.comp A' = 1) (h2 : A'.comp A = 1)
    (h3 : B.comp B' = 1) (h4 : B'.comp B = 1) (φ : X → (F →L[ℂ] E)) :
    ∫ x, A.comp ((φ x).comp B) ∂μ = A.comp ((∫ x, φ x ∂μ).comp B) := by
  have a1 : ∀ v, A (A' v) = v := fun v => congrArg (fun f : E →L[ℂ] E => f v) h1
  have a2 : ∀ v, A' (A v) = v := fun v => congrArg (fun f : E →L[ℂ] E => f v) h2
  have a3 : ∀ v, B (B' v) = v := fun v => congrArg (fun f : F →L[ℂ] F => f v) h3
  have a4 : ∀ v, B' (B v) = v := fun v => congrArg (fun f : F →L[ℂ] F => f v) h4
  let L : (F →L[ℂ] E) ≃L[ℂ] (F →L[ℂ] E) := ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.compL ℂ F E E A).comp ((ContinuousLinearMap.compL ℂ F F E).flip B))
    ((ContinuousLinearMap.compL ℂ F E E A').comp ((ContinuousLinearMap.compL ℂ F F E).flip B'))
    (fun f => by ext v; simp [a2, a3]) (fun f => by ext v; simp [a1, a4])
  exact L.integral_comp_comm φ

theorem Iint_equivariant : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ (x y : H) (ξ : Wp) (ξ' : Wq) (Om Om' : Set (Mt k r)), MeasurableSet Om → MeasurableSet Om' → ∀ γ ∈ GG k r, ∀ t ∈ Sset k r z, ∀ t' ∈ Sset k r z', Iint (psiGen k r z c) (psiGen k r z' c') π π' (μS.restrict Om) (μS'.restrict Om') σ x y ξ ξ' (t * γ * t'⁻¹) = (PiS (psiGen k r z c) π t).comp ((Iint (psiGen k r z c) (psiGen k r z' c') π π' (μS.restrict (rmulM t '' Om)) (μS'.restrict (rmulM t' '' Om')) σ x y ξ ξ' γ).comp (PiS (psiGen k r z' c') π' t'⁻¹)) := by
  intro k r H _ _ _ Wp _ _ _ _ Wq _ _ _ _ σ w a μG d z c π μS z' c' π' μS' _ hs hs' x y ξ ξ' Om Om' _ _
    γ _ t ht t' ht'
  obtain ⟨hz, hT, hπ, hμ, -⟩ := hs
  obtain ⟨hz', hT', hπ', hμ', -⟩ := hs'
  have hS := isClosedSub_Sset hz hT
  have hS' := isClosedSub_Sset hz' hT'
  obtain ⟨-, ⟨⟨p1, pm⟩, -⟩, -⟩ := GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hz hT hπ
  obtain ⟨-, ⟨⟨q1, qm⟩, -⟩, qa, -⟩ := GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z' c' π' hz' hT' hπ'
  have u := ((GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT μS).1 hμ).1 t ht
  have u' := ((GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z' hz' hT' μS').1 hμ').1 t' ht'
  have dt := isUnit_det_of_mem_GG (hS.1 ht)
  have dt' := isUnit_det_of_mem_GG (hS'.1 ht')
  have hti := hS.2.2.2.2 t ht
  have hti' := hS'.2.2.2.2 t' ht'
  have := hμ.1
  have := hμ'.1
  have e := rmulM_emb dt
  have e' := rmulM_emb dt'
  have m : MeasurePreserving (rmulM t) μS μS := ⟨e.measurable, u⟩
  have m' : MeasurePreserving (rmulM t') μS' μS' := ⟨e'.measurable, u'⟩
  have mp := (m.restrict_image_emb e Om).prod (m'.restrict_image_emb e' Om')
  unfold Iint
  rw [← integral_comp_both _ _ (PiS (psiGen k r z c) π t⁻¹) _ (PiS (psiGen k r z' c') π' t')
    (by rw [← pm t ht _ hti, Matrix.mul_nonsing_inv _ dt, p1])
    (by rw [← pm _ hti t ht, Matrix.nonsing_inv_mul _ dt, p1])
    (by rw [← qm _ hti' _ ht', Matrix.nonsing_inv_mul _ dt', q1])
    (by rw [← qm _ ht' _ hti', Matrix.mul_nonsing_inv _ dt', q1]),
    ← mp.integral_comp (e.prodMap e')]
  have c1 : ∀ᵐ s ∂(μS.restrict Om), Matrix.of s ∈ Sset k r z := ae_restrict_of_ae hμ.2.2.1
  have c2 : ∀ᵐ s ∂(μS'.restrict Om'), Matrix.of s ∈ Sset k r z' := ae_restrict_of_ae hμ'.2.2.1
  refine integral_congr_ae ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae c1, Measure.quasiMeasurePreserving_snd.ae c2]
    with p h1 h2
  have k1 : PiS (psiGen k r z c) π (Matrix.of p.1)⁻¹ =
      (PiS (psiGen k r z c) π t).comp (PiS (psiGen k r z c) π (Matrix.of p.1 * t)⁻¹) := by
    rw [← pm t ht _ (hS.2.2.2.2 _ (hS.2.2.2.1 _ h1 _ ht)), Matrix.mul_inv_rev,
      Matrix.mul_nonsing_inv_cancel_left _ _ dt]
  have k2 : PiS (psiGen k r z' c') π' (Matrix.of p.2)⁻¹ =
      (PiS (psiGen k r z' c') π' t').comp (PiS (psiGen k r z' c') π' (Matrix.of p.2 * t')⁻¹) := by
    rw [← qm t' ht' _ (hS'.2.2.2.2 _ (hS'.2.2.2.1 _ h2 _ ht')), Matrix.mul_inv_rev,
      Matrix.mul_nonsing_inv_cancel_left _ _ dt']
  have k3 : act2 (t * γ * t'⁻¹) p = act2 γ (Prod.map (rmulM t) (rmulM t') p) := by
    show Matrix.of p.1 * (t * γ * t'⁻¹) * (Matrix.of p.2)⁻¹ =
      (Matrix.of p.1 * t) * γ * (Matrix.of p.2 * t')⁻¹
    rw [Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
  rw [k1, k2, k3]
  ext η
  rw [← (qa t' ht').2]
  simp only [Prod.map_fst, Prod.map_snd, of_rmulM, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, rankOneInnerOperator_apply, map_smul, ContinuousLinearMap.adjoint_inner_right]

end GlobalTheory.SgInf.Equivar
end
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.besselMaps_proportional_discreteSeries_largeGap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l l₁ : R.H → Wp), R.IsDG ε mu → SideG k r z π u μW μN μG νq → IsBes R z π l → NzOn R l → IsBes R z π l₁ → ∃ c : ℂ, ∀ v ∈ R.sm, l₁ v = c • l v := by
  first | exact @GlobalTheory.GapLine.bessel_line_gap | exact GlobalTheory.GapLine.bessel_line_gap | (intros; apply GlobalTheory.GapLine.bessel_line_gap <;> assumption)
end

section

open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.isBesselMap_conj_iff_and_besselFn_eq_rankOne : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (c : ℂ) (μW μN μG νq : Measure (Mt k r)) (t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), t ∈ GG k r → (∀ n, n ∈ Nset k r ↔ t * n * t⁻¹ ∈ Nset k r) → (∀ h ∈ UWset k r z, t * h = h * t) → (∀ n ∈ Nset k r, psi k r z cStd n = psi k r z c (t * n * t⁻¹)) → SideG k r z π u μW μN μG νq → SideG k r z π u μW (μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) μG (νq.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) ∧ ∀ (R : Rep k r), Formalism.MainNotions.S.IsURepOn (GG k r) R.σ → (∀ B : R.H → Wp, PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π B ↔ IsBes R z π (fun v => B (R.σ t v))) ∧ ∀ l₁ : R.H → Wp, IsBeL R z π μW (μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) l₁ → ∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be z c π R.σ μW μN x v = (innerSL ℂ (l₁ (R.σ t⁻¹ v))).smulRight (l₁ (R.σ t⁻¹ x)) := by
  first | exact @GlobalTheory.BesselMoveGap.bessel_move_gap | exact GlobalTheory.BesselMoveGap.bessel_move_gap | (intros; apply GlobalTheory.BesselMoveGap.bessel_move_gap <;> assumption)
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.exists_goodLocalDatum_of_nonzero_periods_gap : GlobalTheory.GapIn.Hyp → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (R : Rep D.R.k D.R.rS) (h : ℝ) (l : R.H → W.Wp) (l' : R.H → W.Wq) (dd : ℝ), cdScaleTie D → GoodW D τ w w' θ W → R.IsDG (epsSH D.R) lam → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z (psiS D W.z) R.σ W.π l → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z' (psiS D W.z') R.σ W.π' l' → 0 < dd → (∀ v ∈ R.sm, l2SG W.νS (fun g => l (R.σ g v)) = ENNReal.ofReal (‖v‖ ^ 2 / dd)) → (∀ v ∈ R.sm, l2SG W.νS' (fun g => l' (R.σ g v)) = ENNReal.ofReal (‖v‖ ^ 2 / dd)) → ∃ A : LocS W, GoodS D lam A := by
  first | exact @GlobalTheory.DatumOfPeriodsGap.exists_goodS | exact GlobalTheory.DatumOfPeriodsGap.exists_goodS | (intros; apply GlobalTheory.DatumOfPeriodsGap.exists_goodS <;> assumption)
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.formalDegree_ratio_eq_harishChandra_ratio_largeGap : GlobalTheory.GapIn.Hyp → ∀ (D : D7) (W : LocW D.R.k D.R.rS) (l l' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A A' : LocS W) (h : ℝ), GoodS D l A → GoodS D l' A' → GapAtLeast (epsSH D.R) l h → GapAtLeast (epsSH D.R) l' h → Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h → A'.deg / A.deg = Formalism.QuantumDeterminants.fdegHC l' / Formalism.QuantumDeterminants.fdegHC l := by
  first | exact @GlobalTheory.GapDegreeRatio.deg_ratio | exact GlobalTheory.GapDegreeRatio.deg_ratio | (intros; apply GlobalTheory.GapDegreeRatio.deg_ratio <;> assumption)
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.datumDegree_eq_mul_formalDegree_gap : GlobalTheory.GapIn.Hyp → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS), cdScaleTie D → GoodW D τ w w' θ W → ∃ κ : ℝ, 0 < κ ∧ ∀ (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), GoodS D lam A → (∃ h : ℝ, GapAtLeast (epsSH D.R) lam h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h) → ∀ v : A.H, v ≠ 0 → A.deg = κ * PI.BesselPeriodGGP.fdegH W.μG A.σ v ∧ 0 < A.deg := by
  first | exact @GlobalTheory.GapDegreeTie.deg_eq_mul_fdegH | exact GlobalTheory.GapDegreeTie.deg_eq_mul_fdegH | (intros; apply GlobalTheory.GapDegreeTie.deg_eq_mul_fdegH <;> assumption)
end

section

open MeasureTheory Matrix Filter Topology

theorem _root_.GlobalTheory.T.hasDerivAt_derived_action_max_compact_average : ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (φ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ) (v : H) (D : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ → GlobalTheory.KFinAvg.IsHaarKH k r μ → Continuous φ → Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ v → (∀ Y ∈ D, Formalism.MainNotions.S.InLieHpk k r Y) → Formalism.MainNotions.S.InLieHpk k r X → HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D (σ g v) ∂μ)) (∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ (X :: D) (σ g v) ∂μ) 0 := by
  first | exact @GlobalTheory.KFinAvg.hasDerivAt_exp_integral_dsigW | exact GlobalTheory.KFinAvg.hasDerivAt_exp_integral_dsigW | (intros; apply GlobalTheory.KFinAvg.hasDerivAt_exp_integral_dsigW <;> assumption)
end
