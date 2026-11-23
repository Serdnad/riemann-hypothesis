module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle049
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle070
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle166
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.AlgValsFinMain
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle126
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFormulaRootExchangeParabolicIntersection
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle120
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle128
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory.QuotIntFJ

theorem integral_rotate_three {B X U : Type} [MeasurableSpace X] [MeasurableSpace B] [MeasurableSpace U]
    (β : Measure B) (μ : Measure X) (ρ : Measure U) [SFinite μ] [SFinite β] [SFinite ρ]
    (Φ : B → X → U → ℂ) (hΦ : Integrable (fun z : B × (X × U) => Φ z.1 z.2.1 z.2.2) (β.prod (μ.prod ρ))) :
    Integrable (fun b => ∫ x, ∫ u, Φ b x u ∂ρ ∂μ) β ∧
      ∫ b, ∫ x, ∫ u, Φ b x u ∂ρ ∂μ ∂β = ∫ x, ∫ u, ∫ b, Φ b x u ∂β ∂ρ ∂μ := by
  have hsec : ∀ᵐ b ∂β, Integrable (fun y : X × U => Φ b y.1 y.2) (μ.prod ρ) := hΦ.prod_right_ae
  have hin : ∀ᵐ b ∂β, ∫ x, ∫ u, Φ b x u ∂ρ ∂μ = ∫ y : X × U, Φ b y.1 y.2 ∂(μ.prod ρ) := by
    filter_upwards [hsec] with b hb
    exact (integral_prod (fun y : X × U => Φ b y.1 y.2) hb).symm
  have hsw : Integrable (fun w : (X × U) × B => Φ w.2 w.1.1 w.1.2) ((μ.prod ρ).prod β) := hΦ.swap
  refine ⟨hΦ.integral_prod_left.congr (hin.mono fun b hb => hb.symm), ?_⟩
  calc ∫ b, ∫ x, ∫ u, Φ b x u ∂ρ ∂μ ∂β
      = ∫ b, ∫ y : X × U, Φ b y.1 y.2 ∂(μ.prod ρ) ∂β := integral_congr_ae hin
    _ = ∫ w : B × (X × U), Φ w.1 w.2.1 w.2.2 ∂(β.prod (μ.prod ρ)) := (integral_prod _ hΦ).symm
    _ = ∫ w : (X × U) × B, Φ w.2 w.1.1 w.1.2 ∂((μ.prod ρ).prod β) :=
        (integral_prod_swap (fun w : B × (X × U) => Φ w.1 w.2.1 w.2.2)).symm
    _ = ∫ y : X × U, ∫ b, Φ b y.1 y.2 ∂β ∂(μ.prod ρ) := integral_prod _ hsw
    _ = ∫ x, ∫ u, ∫ b, Φ b x u ∂β ∂ρ ∂μ :=
        integral_prod (fun y : X × U => ∫ b, Φ b y.1 y.2 ∂β) hsw.integral_prod_left

theorem weil_formula_FJ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c) (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) (f : GL (n ⊕ Fin c) k → ℂ) (z : ℂ), IsQuotInt ν μX μG (ρ + 1) f z → (∀ h, Integrable (fun β : n → k => f (colE c (ρ + 1) β * h)) (Measure.pi fun _ => ν)) ∧ IsQuotIntFJ ν μX μG ρ (fun h => ∫ β : n → k, f (colE c (ρ + 1) β * h) ∂(Measure.pi fun _ => ν)) z := by
  intro k _ _ _ _ _ _ n _ _ c ρ hρ hρc ν hν μX hμX μG f z hq
  obtain ⟨F, hF, hfF, hz⟩ := hq
  have hF' : IsLocallyConstant F ∧ HasCompactSupport F := hF
  obtain ⟨hsck, ht2k⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have := hsck
  have := ht2k
  obtain ⟨hB1, hL1, hS1, -⟩ := volGL_haar k n ν
  obtain ⟨hB2, hL2, hS2, -⟩ := volGL_haar k (n ⊕ Fin c) ν
  haveI : BorelSpace (GL n k) := hB1
  have := hL1
  have := hS1
  haveI : BorelSpace (GL (n ⊕ Fin c) k) := hB2
  have := hL2
  have := hS2
  haveI : BorelSpace (N k n c (ρ + 1)) := Subtype.borelSpace _

  have hV : volN ν n c (ρ + 1) =
      (Measure.pi fun _ => ν).map (GlobalTheory.RootEx.VolN.coEquiv (k := k) (n := n) (c := c) (ρ + 1)) :=
    GlobalTheory.RootEx.VolN.volN_eq (n := n) (c := c) ν (ρ + 1)
  have : SigmaFinite (volN ν n c (ρ + 1)) := by
    rw [hV]
    exact (GlobalTheory.RootEx.VolN.coEquiv (k := k) (n := n) (c := c) (ρ + 1)).sigmaFinite_map
  have : IsFiniteMeasureOnCompacts (volN ν n c (ρ + 1)) :=
    (GlobalTheory.RootEx.VolN.isHaarMeasure_volN (n := n) (c := c) ν (ρ + 1)).toIsFiniteMeasureOnCompacts

  have hint : ∀ h : GL (n ⊕ Fin c) k, Integrable
      (fun w : (n → k) × (GL n k × N k n c (ρ + 1)) =>
        F (embX c w.2.1 * (w.2.2 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) w.1 * h))
      ((Measure.pi fun _ => ν).prod (μX.prod (volN ν n c (ρ + 1)))) := by
    intro h
    have hcont : Continuous (fun w : (n → k) × (GL n k × N k n c (ρ + 1)) =>
        F (embX c w.2.1 * (w.2.2 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) w.1 * h)) := by
      refine hF'.1.continuous.comp (Continuous.mul (Continuous.mul (Continuous.mul ?_ ?_) ?_) continuous_const)
      · exact GlobalTheory.RootEx.QuotStep.continuous_embX.comp (continuous_fst.comp continuous_snd)
      · exact continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
      · exact (GlobalTheory.RootEx.QuotStep.continuous_colE (ρ + 1)).comp continuous_fst
    obtain ⟨D, hD, hDC⟩ := GlobalTheory.T.exists_compact_preimage_embX_mul_colE k n c ρ hρ hρc ((fun g => g * h⁻¹) '' tsupport F)
      (hF'.2.image (continuous_mul_const h⁻¹))
    have hsupp : HasCompactSupport (fun w : (n → k) × (GL n k × N k n c (ρ + 1)) =>
        F (embX c w.2.1 * (w.2.2 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) w.1 * h)) := by
      refine HasCompactSupport.intro
        (hD.image (f := fun t : GL n k × N k n c (ρ + 1) × (n → k) => (t.2.2, (t.1, t.2.1)))
          (by fun_prop)) ?_
      intro w hw
      by_contra hne
      apply hw
      refine ⟨(w.2.1, w.2.2, w.1), hDC _ ⟨_, subset_tsupport _ hne, ?_⟩, rfl⟩
      simp [mul_assoc]
    haveI : ∀ _ : n, IsFiniteMeasureOnCompacts ν := fun _ => hν.toIsFiniteMeasureOnCompacts
    haveI : IsFiniteMeasureOnCompacts (Measure.pi fun _ : n => ν) := Measure.pi.isFiniteMeasureOnCompacts _
    haveI : IsFiniteMeasureOnCompacts μX := hμX.toIsFiniteMeasureOnCompacts
    haveI : IsFiniteMeasureOnCompacts (μX.prod (volN ν n c (ρ + 1))) :=
      Measure.prod.instIsFiniteMeasureOnCompacts _ _
    haveI : IsFiniteMeasureOnCompacts ((Measure.pi fun _ : n => ν).prod (μX.prod (volN ν n c (ρ + 1)))) :=
      Measure.prod.instIsFiniteMeasureOnCompacts _ _
    exact hcont.integrable_of_hasCompactSupport
      (μ := (Measure.pi fun _ : n => ν).prod (μX.prod (volN ν n c (ρ + 1)))) hsupp
  have hfeq : ∀ (h : GL (n ⊕ Fin c) k) (b : n → k), f (colE c (ρ + 1) b * h) =
      ∫ x, ∫ u : N k n c (ρ + 1), F (embX c x * (u : GL (n ⊕ Fin c) k) * colE c (ρ + 1) b * h)
        ∂(volN ν n c (ρ + 1)) ∂μX := by
    intro h b
    rw [hfF]
    simp only [mul_assoc] <;> exact Eq.refl _
  have key := fun h : GL (n ⊕ Fin c) k => integral_rotate_three (Measure.pi fun _ : n => ν) μX
    (volN ν n c (ρ + 1))
    (fun b x (u : N k n c (ρ + 1)) => F (embX c x * (u : GL (n ⊕ Fin c) k) * colE c (ρ + 1) b * h))
    (hint h)
  refine ⟨fun h => (key h).1.congr (Filter.Eventually.of_forall fun b => (hfeq h b).symm), ?_⟩
  unfold IsQuotIntFJ
  refine ⟨F, hF, fun h => ?_, hz⟩
  calc ∫ b : n → k, f (colE c (ρ + 1) b * h) ∂(Measure.pi fun _ => ν)
      = ∫ b : n → k, ∫ x, ∫ u : N k n c (ρ + 1),
          F (embX c x * (u : GL (n ⊕ Fin c) k) * colE c (ρ + 1) b * h)
            ∂(volN ν n c (ρ + 1)) ∂μX ∂(Measure.pi fun _ => ν) :=
        integral_congr_ae (Filter.Eventually.of_forall (hfeq h))
    _ = _ := (key h).2

end GlobalTheory.QuotIntFJ
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory.RootEx.FourierJacobiGroup

theorem uni_conj {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι] {b : ι → ℕ}
    {A B M : Matrix ι ι k} (hA : ∀ r s, b r ≠ b s → A r s = 0) (hB : ∀ r s, b r ≠ b s → B r s = 0)
    (hAB : A * B = 1) (hM : Radical.Uni b M) : Radical.Uni b (A * M * B) := by
  intro r s hrs
  have : (A * M * B) r s = (A * (1 : Matrix ι ι k) * B) r s := by
    simp only [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun t _ => ?_
    by_cases h1 : b r = b t
    · by_cases h2 : b u = b s
      · rw [hM t u (by omega)]
      · rw [hB u s h2, mul_zero, mul_zero]
    · simp only [hA r t h1, zero_mul]
  rw [this, Matrix.mul_one, hAB]

variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem colE_add (q : ℕ) (β γ : n → k) : colE c q β * colE c q γ = colE c q (β + γ) := by
  apply Units.ext
  simp only [colE, upU, Units.val_mul, fromBlocks_multiply]
  congr 1 <;> simp
  ext r i
  by_cases h : i.val + 1 = q <;> simp [h, add_comm]

theorem colE_inv (q : ℕ) (β : n → k) : (colE c q β)⁻¹ = colE c q (-β) :=
  inv_eq_of_mul_eq_one_right (QuotStep.colE_neg q β)

theorem colE_zero (q : ℕ) : colE c q (0 : n → k) = 1 := by
  have := QuotStep.colE_neg (c := c) q (0 : n → k)
  rwa [colE_add, add_neg_cancel] at this

theorem colE_offdiag (q : ℕ) (β : n → k) (r s : n ⊕ Fin c) (h : lev q r ≠ lev q s) :
    (colE c q β).val r s = 0 := by
  rcases r with r | r <;> rcases s with s | s
  · simp [lev] at h
  · simp only [lev, Sum.elim_inl, Sum.elim_inr] at h
    simp [colE, upU, h.symm]
  · simp [colE, upU]
  · have : r ≠ s := by
      rintro rfl
      exact h rfl
    simp [colE, upU, this]

theorem colE_conj_mem (q : ℕ) (β : n → k) {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c q) :
    colE c q β * u * (colE c q β)⁻¹ ∈ N k n c q := by
  rw [Radical.mem_N_iff] at hu ⊢
  rw [colE_inv]
  exact uni_conj (b := lev q) (colE_offdiag q β) (colE_offdiag q (-β))
    (congrArg Units.val (QuotStep.colE_neg q β)) hu

theorem exists_of_mem_N {p : ℕ} (hp : p < c) {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) :
    ∃ u ∈ N k n c (p + 1), ∃ β : n → k, g = u * colE c (p + 1) β := by
  let β : n → k := fun x => g.val (Sum.inl x) (Sum.inr ⟨p, hp⟩)
  refine ⟨g * colE c (p + 1) (-β), ?_, β, by rw [mul_assoc, colE_add, neg_add_cancel, colE_zero, mul_one]⟩
  have h1 := (Radical.mem_N_iff _).1 (mul_mem hg (Radical.colE_mem (-β) (Nat.lt_succ_self p)))
  have h0 := (Radical.mem_N_iff _).1 hg
  rw [Radical.mem_N_iff]
  intro r s hrs
  by_cases h : lev p s ≤ lev p r
  · exact h1 r s h
  rcases r with r | r <;> rcases s with s | s <;> simp only [lev, Sum.elim_inl, Sum.elim_inr] at h hrs
  · omega
  · obtain rfl : s = ⟨p, hp⟩ := Fin.ext (by simp only; omega)
    have h2 : ∀ y, g.val (Sum.inl r) (Sum.inl y) = (1 : Matrix n n k) r y := fun y => by
      rw [h0 _ _ (by simp [lev])]; simp [Matrix.one_apply]
    simp [colE, upU, Matrix.mul_apply, Fintype.sum_sum_type, h2, Matrix.one_apply, β]
  · omega
  · omega

theorem colE_conj_mem_R (q : ℕ) (β : n → k) {r : GL (n ⊕ Fin c) k} (hr : r ∈ R k n c q) :
    ∃ r' ∈ R k n c q, ∃ γ : n → k, colE c q β * r = r' * colE c q γ := by
  obtain ⟨x, u, hu, rfl⟩ := Radical.exists_of_mem_R hr
  refine ⟨embX c x * (colE c q ((x⁻¹).val.mulVec β) * u * (colE c q ((x⁻¹).val.mulVec β))⁻¹),
    mul_mem (Subgroup.mem_sup_left ⟨x, rfl⟩) (Subgroup.mem_sup_right (colE_conj_mem q _ hu)),
    (x⁻¹).val.mulVec β, ?_⟩
  rw [← QuotStep.conj_colE, map_inv]
  group

theorem mem_RFJ_iff : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c), (∀ g, g ∈ RFJ k n c ρ ↔ ∃ r ∈ R k n c (ρ + 1), ∃ β : n → k, g = r * colE c (ρ + 1) β) ∧ ∀ β : n → k, ∀ u ∈ N k n c (ρ + 1), colE c (ρ + 1) β * u * (colE c (ρ + 1) β)⁻¹ ∈ N k n c (ρ + 1) := by
  intro k _ n _ _ c ρ _ hρ
  refine ⟨fun g => ⟨fun hg => ?_, ?_⟩, fun β u hu => colE_conj_mem _ β hu⟩
  · let S : Subgroup (GL (n ⊕ Fin c) k) :=
      { carrier := {g | ∃ r ∈ R k n c (ρ + 1), ∃ β : n → k, g = r * colE c (ρ + 1) β}
        one_mem' := ⟨1, one_mem _, 0, by rw [colE_zero, mul_one]⟩
        mul_mem' := by
          rintro _ _ ⟨r, hr, β, rfl⟩ ⟨r₂, hr₂, β₂, rfl⟩
          obtain ⟨r', hr', γ, e⟩ := colE_conj_mem_R (ρ + 1) β hr₂
          refine ⟨r * r', mul_mem hr hr', γ + β₂, ?_⟩
          rw [← colE_add, mul_assoc r, ← mul_assoc _ r₂, e]
          simp only [mul_assoc]
        inv_mem' := by
          rintro _ ⟨r, hr, β, rfl⟩
          obtain ⟨r', hr', γ, e⟩ := colE_conj_mem_R (ρ + 1) (-β) (inv_mem hr)
          exact ⟨r', hr', γ, by rw [_root_.mul_inv_rev, colE_inv, e]⟩ }
    have hR : R k n c (ρ + 1) ≤ S := fun r hr => ⟨r, hr, 0, by rw [colE_zero, mul_one]⟩
    have : RFJ k n c ρ ≤ S := by
      refine sup_le (sup_le (le_trans le_sup_left hR) fun g hg => ?_) hR
      obtain ⟨u, hu, β, rfl⟩ := exists_of_mem_N hρ hg
      exact ⟨u, Subgroup.mem_sup_right hu, β, rfl⟩
    exact this hg
  · rintro ⟨r, hr, β, rfl⟩
    exact mul_mem (Subgroup.mem_sup_right hr)
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Radical.colE_mem β (Nat.lt_succ_self ρ))))

end GlobalTheory.RootEx.FourierJacobiGroup
end

section

open NumberField IsDedekindDomain Formalism.L2.Host

noncomputable section

namespace GlobalTheory.EtaValsNumberField

open Formalism.BasicNotions Formalism.FrobeniusOrbits

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

def embSum : R.Psi ⊕ R.Psi → (H.E →+* ℂ) :=
  Sum.elim (embPsi H) fun g => (starRingEnd ℂ).comp (embPsi H g)

theorem embSum_injective : Function.Injective (embSum H) := by
  rintro (i | i) (j | j) hij
  · exact congrArg _ (GlobalTheory.HalfIntChars.embPsi_inj H hij)
  · exact absurd hij (GlobalTheory.HalfIntChars.embPsi_ne_conj H i j)
  · exact absurd hij.symm (GlobalTheory.HalfIntChars.embPsi_ne_conj H j i)
  · refine congrArg _ (GlobalTheory.HalfIntChars.embPsi_inj H (RingHom.ext fun x => ?_))
    have := congrArg (fun f : H.E →+* ℂ => starRingEnd ℂ (f x)) hij
    simpa [embSum] using this

theorem card_sum : Fintype.card (R.Psi ⊕ R.Psi) = Fintype.card (H.E →+* ℂ) := by
  rw [Fintype.card_sum, NumberField.Embeddings.card, H.finrank_cmField,
    ← Nat.card_eq_fintype_card, Formalism.HC.Frame.natCard_Psi]
  ring

def embEquiv : R.Psi ⊕ R.Psi ≃ (H.E →+* ℂ) :=
  Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).mpr ⟨embSum_injective H, card_sum H⟩)

theorem algType_eta : ∃ m : (H.E →+* ℂ) → ℤ, ∀ k : H.Eˣ,
    (∏ g, (embPsi H g (k : H.E) / ((‖embPsi H g (k : H.E)‖ : ℝ) : ℂ)) ^ (1 : ℤ)) *
      ∏ φ : H.E →+* ℂ, ((‖φ (k : H.E)‖ : ℝ) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) = ∏ φ : H.E →+* ℂ, φ (k : H.E) ^ m φ := by
  set bij := embEquiv H
  let g : R.Psi ⊕ R.Psi → ℤ := fun x => Sum.elim (fun _ => 1) (fun _ => 0) x
  refine ⟨fun ψ => g (bij.symm ψ), fun k => ?_⟩
  have hR : ∏ ψ : H.E →+* ℂ, ψ (k : H.E) ^ g (bij.symm ψ) = ∏ x : R.Psi ⊕ R.Psi, (bij x) (k : H.E) ^ g x :=
    (Fintype.prod_equiv bij _ _ fun x => by rw [Equiv.symm_apply_apply]).symm
  have hL : ∏ ψ : H.E →+* ℂ, ((‖ψ (k : H.E)‖ : ℝ) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) =
      ∏ x : R.Psi ⊕ R.Psi, ((‖bij x (k : H.E)‖ : ℝ) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) :=
    (Fintype.prod_equiv bij _ _ fun x => rfl).symm
  rw [hR, hL, Fintype.prod_sum_type, Fintype.prod_sum_type, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  set z := embPsi H τ (k : H.E) with hzdef
  have hz : z ≠ 0 := (map_ne_zero _).2 k.ne_zero
  have hn : (((‖z‖ : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
  show (z / ((‖z‖ : ℝ) : ℂ)) ^ (1 : ℤ) * ((((‖z‖ : ℝ) : ℂ)) ^ (((1 / 2 : ℝ)) : ℂ) *
    (((‖starRingEnd ℂ z‖ : ℝ) : ℂ)) ^ (((1 / 2 : ℝ)) : ℂ)) = z ^ (1 : ℤ) * (starRingEnd ℂ z) ^ (0 : ℤ)
  rw [Complex.norm_conj, ← Complex.cpow_add _ _ hn]
  norm_num
  rw [div_mul_cancel₀ _ hn]

theorem etaVals : ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E), IsEtaT H χ →
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ χ.ValuesIn (1 / 2) (algebraMap M ℂ) := by
  intro R H χ hχ
  obtain ⟨m, hm⟩ := algType_eta H
  obtain ⟨C, hC, hv⟩ := PI.AlgValsFin.W.algValsFin_main H.E χ (1 / 2) m (fun k => by rw [hχ.inf k]; exact hm k)
  let M : IntermediateField ℚ ℂ := C.toIntermediateField fun x => by simp
  let e : C ≃+ M :=
    { toFun := fun x => ⟨x, x.2⟩
      invFun := fun x => ⟨x, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hM : FiniteDimensional ℚ M := LinearEquiv.finiteDimensional
    { e.toAddMonoidHom.toRatLinearMap with
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv }
  refine ⟨M, hM, fun v hv' => ?_⟩
  obtain ⟨y, hy⟩ := hv v hv'
  exact ⟨e y, hy⟩

end GlobalTheory.EtaValsNumberField
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix NumberField IsDedekindDomain
open scoped NNReal TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finitePlace_relativeNorm_le_localSize_pow : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (y : D.host.E), ‖algebraMap D.host.F (Fv D.host.F v) (Algebra.norm D.host.F y)‖₊ ≤ GlobalTheory.AdelicU.absFin D.host.F v ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] y) ^ Module.finrank D.host.F D.host.E := by
  first | exact @GlobalTheory.NormFin.normFin_le | exact GlobalTheory.NormFin.normFin_le | (intros; apply GlobalTheory.NormFin.normFin_le <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.AdelicU
open scoped TensorProduct NNReal
open Classical

theorem _root_.GlobalTheory.T.infinitePlace_minpoly_coeff_le_pow_max_embeddings : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (x : E) (w : InfinitePlace F) (j : ℕ), w ((minpoly F x).coeff j) ≤ 2 ^ Module.finrank F E * ((max 1 (Finset.univ.sup fun τ : EmbOver E w => ‖τ.1 x‖₊) : ℝ≥0) : ℝ) ^ Module.finrank F E := by
  first | exact @GlobalTheory.minpoly_coeff_le_inf | exact GlobalTheory.minpoly_coeff_le_inf | (intros; apply GlobalTheory.minpoly_coeff_le_inf <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix NumberField IsDedekindDomain
open scoped NNReal TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.infinitePlace_relativeNorm_le_maxEmbedding_pow : ∀ (D : D7) (w : InfinitePlace D.host.F) (y : D.host.E) (c : ℝ≥0), (∀ τ : GlobalTheory.AdelicU.EmbOver D.host.E w, ‖τ.1 y‖₊ ≤ c) → w (Algebra.norm D.host.F y) ≤ (c : ℝ) ^ Module.finrank D.host.F D.host.E := by
  first | exact @GlobalTheory.NormInf.main | exact GlobalTheory.NormInf.main | (intros; apply GlobalTheory.NormInf.main <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.AdelicU
open scoped TensorProduct NNReal
open Classical

theorem _root_.GlobalTheory.T.nnnorm_minpoly_coeff_finitePlace_le_pow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (x : E) (v : HeightOneSpectrum (𝓞 F)) (j : ℕ), ‖algebraMap F (v.adicCompletion F) ((minpoly F x).coeff j)‖₊ ≤ max 1 (absFin F v ((1 : v.adicCompletion F) ⊗ₜ[F] x)) ^ Module.finrank F E := by
  first | exact @GlobalTheory.CoefHeight.nnnorm_coeff_minpoly_le | exact GlobalTheory.CoefHeight.nnnorm_coeff_minpoly_le | (intros; apply GlobalTheory.CoefHeight.nnnorm_coeff_minpoly_le <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

theorem _root_.GlobalTheory.T.weil_formula_rootExchange_parabolic_intersection : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (f : GL (n ⊕ Fin c) k → ℂ) (_ : IsLocallyConstant f) (_ : ∃ Ω, IsCompact Ω ∧ ∀ h, f h ≠ 0 → ∃ r ∈ R k n c p ⊓ R k n c (p + 1), ∃ w ∈ Ω, h = r * w) (_ : ∀ (x : GL n k), ∀ u ∈ N k n c p ⊓ N k n c (p + 1), ∀ h, f (embX c x * u * h) = ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) - 2 * p) : ℝ) : ℂ) * f h), ∃ z, IsQuotInt ν μX μG p (fun h => ∫ β : n → k, f (colE c (p + 1) β * h) ∂(Measure.pi fun _ => ν)) z ∧ IsQuotInt ν μX μG (p + 1) (fun h => ∫ u : n → k, f (rowE c p u * h) ∂(Measure.pi fun _ => ν)) z := by
  first | exact @GlobalTheory.RootEx.QuotStep.quotInt_step | exact GlobalTheory.RootEx.QuotStep.quotInt_step | (intros; apply GlobalTheory.RootEx.QuotStep.quotInt_step <;> assumption)
end

section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel

theorem _root_.GlobalTheory.T.parabolicProductTwoReps_equiv_two_block_induction : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W), Nonempty ((prod₂ π₁ π₂).Equiv (multiProd (two (stdSum (rfl : r + t = r + t))) (twoRep π₁ π₂))) := by
  first | exact @GlobalTheory.SmGL.Exponents.prod₂_equiv_multiProd | exact GlobalTheory.SmGL.Exponents.prod₂_equiv_multiProd | (intros; apply GlobalTheory.SmGL.Exponents.prod₂_equiv_multiProd <;> assumption)
end

section

open NumberField

noncomputable section
namespace GlobalTheory.RatCount
open GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain Formalism.UG
open scoped TensorProduct NNReal

theorem nnnorm_entry_le_opNorm {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (i j : n) :
    ‖A i j‖₊ ≤ opNorm A := by
  unfold opNorm
  have h1 : (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A (EuclideanSpace.single j 1)) i = A i j := by
    change ∑ d, A i d * (EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ n) d = A i j
    simp [PiLp.single_apply]
  have h2 := ContinuousLinearMap.le_opNNNorm (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) (EuclideanSpace.single j 1)
  rw [PiLp.nnNorm_single, nnNorm_one, mul_one] at h2
  rw [← h1]
  exact (PiLp.nnNorm_apply_le _ i).trans h2

theorem htE_entry_le_heightGL (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (N : ℕ) (γ : GL (Fin N) E) (i j : Fin N) :
    GlobalTheory.RatCount.htE F ((γ : Matrix (Fin N) (Fin N) E) i j) ≤
      GlobalTheory.AdelicU.heightGL F (Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) γ) := by
  classical
  set x : E := (γ : Matrix (Fin N) (Fin N) E) i j with hx
  set g := Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) γ with hg
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F),
      max 1 (absFin F v ((1 : Fv F v) ⊗ₜ[F] x)) ≤ htFin F v (bc (compFin F E v) g) := by
    intro v
    refine max_le (one_le_htOf _ _) (le_trans ?_ (le_htOf _ _))
    have he : ((bc (compFin F E v) g : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) i j = (1 : Fv F v) ⊗ₜ[F] x := by
      change compFin F E v ((1 : AF F) ⊗ₜ[F] x) = _
      simp [compFin, Algebra.TensorProduct.map_tmul]
    rw [← he]
    exact absFin_le_normFin F v _ i j
  have hinf : ∀ w : InfinitePlace F,
      max 1 (Finset.univ.sup fun τ : EmbOver E w => ‖τ.1 x‖₊) ≤ htInf F w (bc (compInf F E w) g) := by
    intro w
    refine max_le (one_le_htOf _ _) (le_trans ?_ (le_htOf _ _))
    refine Finset.sup_le fun τ _ => ?_
    have he : (((bc (compInf F E w) g : GL (Fin N) _) : Matrix (Fin N) (Fin N) _).map (infEmb τ)) i j = τ.1 x := by
      change infEmb τ (compInf F E w ((1 : AF F) ⊗ₜ[F] x)) = _
      simp [compInf, Algebra.TensorProduct.map_tmul, infEmb_tmul]
    rw [← he]
    exact (nnnorm_entry_le_opNorm _ i j).trans ((normInf_le_iff F w).1 le_rfl τ)
  unfold htE heightGL
  refine mul_le_mul' (Finset.prod_le_prod fun w _ => hinf w) ?_
  have hg' := finite_mulSupport_htFin F g
  refine finprod_le_finprod' (hg'.subset fun v hv hv' => hv ?_) hg' hfin
  exact le_antisymm ((hfin v).trans (le_of_eq hv')) (le_max_left _ _)

end GlobalTheory.RatCount
end
end
