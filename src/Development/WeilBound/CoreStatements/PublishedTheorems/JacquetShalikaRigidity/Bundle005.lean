module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
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

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace ColumnBlockEquiv

section Ring

variable {R : Type} [CommRing R] {a : ℕ}

theorem pm_col (m : ℕ) (y : UnipotentBlockColumnIndex a m m → R) (i k : Fin a) :
    posM (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) y i k =
      if hik : (i : ℕ) < m ∧ (k : ℕ) = m then y ⟨(i, k), hik.1, hik.2.ge, hik.2.le⟩ else 0 := by
  rw [posM, Matrix.sum_apply]
  split_ifs with hik
  · rw [Finset.sum_eq_single ⟨(i, k), hik.1, hik.2.ge, hik.2.le⟩]
    · simp
    · intro b _ hb
      rw [Matrix.single_apply, if_neg]
      rintro ⟨h1, h2⟩
      exact hb (Subtype.ext (Prod.ext h1 h2))
    · intro h
      exact absurd (Finset.mem_univ _) h
  · refine Finset.sum_eq_zero fun t _ => ?_
    rw [Matrix.single_apply, if_neg]
    rintro ⟨h1, h2⟩
    apply hik
    have := t.2
    rw [← h1, ← h2]
    omega

theorem pm_mul_apply {ι : Type} [Fintype ι] (p : ι → Fin a × Fin a) (y : ι → R)
    (M : Matrix (Fin a) (Fin a) R) (i k : Fin a) :
    (posM p y * M) i k = ∑ s, if (p s).1 = i then y s * M (p s).2 k else 0 := by
  simp only [posM, Matrix.sum_mul, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : (p s).1 = i
  · subst h
    simp [Matrix.single_mul_apply_same]
  · rw [if_neg h, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Matrix.single_apply, if_neg (fun e => h e.1), zero_mul]

theorem mul_pm_apply {ι : Type} [Fintype ι] (p : ι → Fin a × Fin a) (y : ι → R)
    (M : Matrix (Fin a) (Fin a) R) (i k : Fin a) :
    (M * posM p y) i k = ∑ s, if (p s).2 = k then M i (p s).1 * y s else 0 := by
  simp only [posM, Matrix.mul_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : (p s).2 = k
  · subst h
    simp [Matrix.mul_single_apply_same]
  · rw [if_neg h, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Matrix.single_apply, if_neg (fun e => h e.2), mul_zero]

theorem pm_mul_row (m : ℕ) (y : UnipotentBlockColumnIndex a m m → R) (M : Matrix (Fin a) (Fin a) R)
    (hM : ∀ j k : Fin a, (j : ℕ) = m → M j k = (1 : Matrix (Fin a) (Fin a) R) j k) :
    posM (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) y * M = posM Subtype.val y := by
  ext i k
  have e := pm_mul_apply (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) y 1 i k
  rw [Matrix.mul_one] at e
  rw [e, pm_mul_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hM s.1.2 k (by have := s.2; omega)]

theorem mul_posM_blockColumn (m : ℕ) (y : UnipotentBlockColumnIndex a m m → R) (h : GL (Fin a) R) (hB : GlobalTheory m h) :
    h.val * posM (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) y =
      posM Subtype.val (fun t : UnipotentBlockColumnIndex a m m => ∑ s, h.val t.1.1 s.1.1 * y s) := by
  ext i k
  rw [mul_pm_apply, pm_col]
  split_ifs with hc
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [if_pos (Fin.ext (by have := s.2; omega))]
  · refine Finset.sum_eq_zero fun s _ => ?_
    split_ifs with hs
    · have h2 := s.2
      have hk : (k : ℕ) = m := by rw [← hs]; omega
      have hi : m ≤ (i : ℕ) := by
        by_contra hh
        exact hc ⟨by omega, hk⟩
      rw [hB i s.1.1 (Or.inl hi), Matrix.one_apply_ne, zero_mul]
      intro e
      rw [← e] at h2
      omega
    · rfl

theorem conj_blkU (m : ℕ) (h : GL (Fin a) R) (hB : GlobalTheory m h) (y : UnipotentBlockColumnIndex a m m → R) :
    h * blkU y * h⁻¹ = blkU (fun t : UnipotentBlockColumnIndex a m m => ∑ s, h.val t.1.1 s.1.1 * y s) := by
  have e : h * blkU y = blkU (fun t : UnipotentBlockColumnIndex a m m => ∑ s, h.val t.1.1 s.1.1 * y s) * h := by
    apply Units.ext
    show h.val * (1 + posM Subtype.val y) = (1 + posM Subtype.val _) * h.val
    rw [mul_add, add_mul, mul_one, one_mul,
      pm_mul_row m _ h.val (fun j k hj => hB j k (Or.inl hj.ge)), mul_posM_blockColumn m y h hB]
  rw [e, mul_inv_cancel_right]

end Ring

def colEquiv (k j : ℕ) (hj : j < k) : UnipotentBlockColumnIndex k j j ≃ Fin j where
  toFun t := ⟨t.1.1.val, t.2.1⟩
  invFun i := ⟨(⟨i.val, i.2.trans hj⟩, ⟨j, hj⟩), i.2, le_rfl, le_rfl⟩
  left_inv t := Subtype.ext (Prod.ext rfl (Fin.ext (by
    have := t.2.2
    change j = (t.1.2 : ℕ)
    omega)))
  right_inv i := Fin.ext rfl

end ColumnBlockEquiv

theorem algebraic_modulus_one_of_finiteOrder_char : AdelicLinearChange → CornerEmbedding → ColumnConjugationMeasure := by
  intro hM hK E _ _ _ k j hj g hg F hF
  have hK' := hK E k j hj.le
  obtain ⟨ι, hι⟩ := hK'.1 (Ad E)
  have hK2 := hK'.2 ι hι
  obtain ⟨g', rfl⟩ := hK2.2.2.1 g hg
  have hDt : Dt (ι g') = Dt g' := hK2.2.2.2.1 g'
  let e : UnipotentBlockColumnIndex k j j ≃ Fin j := ColumnBlockEquiv.colEquiv k j hj
  let Φ := MeasurableEquiv.piCongrLeft (fun _ : Fin j => Ad E) e
  have hΦ : MeasurePreserving Φ (vecMeasure E (UnipotentBlockColumnIndex k j j)) (vecMeasure E (Fin j)) :=
    measurePreserving_piCongrLeft (fun _ : Fin j => GroundTheory.Global.adeleMeasure E) e
  have key : ∀ H : (UnipotentBlockColumnIndex k j j → Ad E) → ℝ≥0∞,
      ∫⁻ y, H y ∂vecMeasure E (UnipotentBlockColumnIndex k j j) = ∫⁻ v, H (Φ.symm v) ∂vecMeasure E (Fin j) := by
    intro H
    have h1 := hΦ.lintegral_comp_emb Φ.measurableEmbedding (fun v => H (Φ.symm v))
    simp only [MeasurableEquiv.symm_apply_apply] at h1
    exact h1
  have hsymm : ∀ (v : Fin j → Ad E) (t : UnipotentBlockColumnIndex k j j), Φ.symm v t = v (e t) := by
    intro v t
    rfl
  have hent : ∀ t s : UnipotentBlockColumnIndex k j j, (ι g').val t.1.1 s.1.1 = g'.val (e t) (e s) := by
    intro t s
    rw [hι g']
    exact dif_pos ⟨t.2.1, s.2.1⟩
  have hpt : ∀ v : Fin j → Ad E, ι g' * blkU (Φ.symm v) * (ι g')⁻¹ =
      blkU (fun t : UnipotentBlockColumnIndex k j j => (g'.val *ᵥ v) (e t)) := by
    intro v
    rw [PositivityTheory.AdelicQuotientData.ColumnBlockEquiv.conj_blkU j (ι g') hg]
    refine congrArg blkU (funext fun t => ?_)
    rw [show (g'.val *ᵥ v) (e t) = ∑ b, g'.val (e t) b * v b from rfl, ← e.sum_comp]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hsymm, hent t s]
  have hc : Continuous (fun v : Fin j → Ad E => (blkU (fun t : UnipotentBlockColumnIndex k j j => v (e t)) : GA E k)) :=
    (continuous_posU (isNil_blk k j j)).comp (continuous_pi fun t => continuous_apply (e t))
  have hG : Measurable (fun v : Fin j → Ad E => F (blkU (fun t : UnipotentBlockColumnIndex k j j => v (e t)))) :=
    hF.comp hc.measurable
  calc ∫⁻ x, F (ι g' * blkU x * (ι g')⁻¹) ∂vecMeasure E (UnipotentBlockColumnIndex k j j)
      = ∫⁻ v, F (ι g' * blkU (Φ.symm v) * (ι g')⁻¹) ∂vecMeasure E (Fin j) :=
        key (fun x => F (ι g' * blkU x * (ι g')⁻¹))
    _ = ∫⁻ v, F (blkU (fun t : UnipotentBlockColumnIndex k j j => (g'.val *ᵥ v) (e t))) ∂vecMeasure E (Fin j) :=
        lintegral_congr fun v => by rw [hpt v]
    _ = ENNReal.ofReal (Dt g')⁻¹ *
          ∫⁻ v, F (blkU (fun t : UnipotentBlockColumnIndex k j j => v (e t))) ∂vecMeasure E (Fin j) :=
        (hM E j g' _ hG).1
    _ = ENNReal.ofReal (Dt (ι g'))⁻¹ * ∫⁻ x, F (blkU x) ∂vecMeasure E (UnipotentBlockColumnIndex k j j) := by
        rw [hDt, key (fun x => F (blkU x))]
        congr 1

end PositivityTheory.AdelicQuotientData

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace QuadraticTransferFirst

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] in
theorem swap3 {μ ν ρ : Measure G} [SFinite μ] [SFinite ν] [SFinite ρ] (K : G → G → G → ℝ≥0∞)
    (hK : Measurable fun p : G × G × G => K p.1 p.2.1 p.2.2) :
    ∫⁻ g, ∫⁻ r, ∫⁻ h, K r h g ∂ν ∂ρ ∂μ = ∫⁻ r, ∫⁻ h, ∫⁻ g, K r h g ∂μ ∂ν ∂ρ := by
  have hF : Measurable (Function.uncurry fun g r => ∫⁻ h, K r h g ∂ν) := by
    have : Measurable fun q : (G × G) × G => K q.1.2 q.2 q.1.1 :=
      hK.comp ((measurable_snd.comp measurable_fst).prodMk
        (measurable_snd.prodMk (measurable_fst.comp measurable_fst)))
    exact this.lintegral_prod_right'
  rw [lintegral_lintegral_swap hF.aemeasurable]
  refine lintegral_congr fun r => ?_
  have hK' : Measurable (Function.uncurry fun g h => K r h g) :=
    hK.comp (measurable_const.prodMk (measurable_snd.prodMk measurable_fst))
  exact lintegral_lintegral_swap hK'.aemeasurable

theorem main (μ : Measure G) [μ.IsHaarMeasure] (ν ρ : Measure G) [SFinite ν] [SFinite ρ] (H : Set G)
    (β β₁ : G → ℝ≥0∞) (hinv : Measure.map (fun h => h⁻¹) ν = ν) (hH : ∀ᵐ h ∂ν, h ∈ H) (hβ : IsWt ν β)
    (hβ₁ : Measurable β₁) (h1 : ∀ g, ∫⁻ r, ∫⁻ h, β₁ (r⁻¹ * h * g) ∂ν ∂ρ = 1) (Φ : G → ℝ≥0∞)
    (hΦ : Measurable Φ) (hΦH : ∀ h ∈ H, ∀ g, Φ (h * g) = Φ g) :
    ∫⁻ g, Φ g ∂μ.withDensity β = ∫⁻ g, ∫⁻ r, Φ (r * g) ∂ρ ∂μ.withDensity β₁ := by
  have hβm : Measurable β := hβ.1
  have hH' : ∀ᵐ h ∂ν, h⁻¹ ∈ H := by
    have hH2 := hH
    rw [← hinv] at hH2
    exact ae_of_ae_map measurable_inv.aemeasurable hH2
  have hinvβ : ∀ g, ∫⁻ h, β (h⁻¹ * g) ∂ν = 1 := by
    intro g
    have hm : Measurable fun h : G => β (h * g) := by fun_prop
    rw [show (∫⁻ h, β (h⁻¹ * g) ∂ν) = ∫⁻ h, β (h * g) ∂(Measure.map (fun h => h⁻¹) ν) from
      (lintegral_map hm measurable_inv).symm, hinv]
    exact hβ.2 g
  calc ∫⁻ g, Φ g ∂μ.withDensity β
      = ∫⁻ g, β g * Φ g ∂μ := lintegral_withDensity_eq_lintegral_mul _ hβm hΦ
    _ = ∫⁻ g, ∫⁻ r, ∫⁻ h, β g * Φ g * β₁ (r⁻¹ * h * g) ∂ν ∂ρ ∂μ := by
        refine lintegral_congr fun g => ?_
        have hm1 : ∀ r, Measurable fun h => β₁ (r⁻¹ * h * g) := fun r => by fun_prop
        have hm2 : Measurable fun r => ∫⁻ h, β₁ (r⁻¹ * h * g) ∂ν := by
          have : Measurable fun p : G × G => β₁ (p.1⁻¹ * p.2 * g) := by fun_prop
          exact this.lintegral_prod_right'
        calc β g * Φ g = β g * Φ g * ∫⁻ r, ∫⁻ h, β₁ (r⁻¹ * h * g) ∂ν ∂ρ := by rw [h1 g, mul_one]
          _ = _ := by
            rw [← lintegral_const_mul _ hm2]
            refine lintegral_congr fun r => ?_
            rw [lintegral_const_mul _ (hm1 r)]
    _ = ∫⁻ r, ∫⁻ h, ∫⁻ g, β g * Φ g * β₁ (r⁻¹ * h * g) ∂μ ∂ν ∂ρ :=
        swap3 (fun r h g => β g * Φ g * β₁ (r⁻¹ * h * g))
          (show Measurable fun p : G × G × G => β p.2.2 * Φ p.2.2 * β₁ (p.1⁻¹ * p.2.1 * p.2.2) by fun_prop)
    _ = ∫⁻ r, ∫⁻ h, ∫⁻ g, β (h⁻¹ * g) * Φ g * β₁ (r⁻¹ * g) ∂μ ∂ν ∂ρ := by
        refine lintegral_congr fun r => lintegral_congr_ae (hH'.mono fun h hh => ?_)
        refine (lintegral_mul_left_eq_self (μ := μ) (fun x => β x * Φ x * β₁ (r⁻¹ * h * x)) h⁻¹).symm.trans
          (lintegral_congr fun g => ?_)
        show β (h⁻¹ * g) * Φ (h⁻¹ * g) * β₁ (r⁻¹ * h * (h⁻¹ * g)) = _
        rw [hΦH _ hh, mul_assoc r⁻¹ h, mul_inv_cancel_left]
    _ = ∫⁻ r, ∫⁻ g, ∫⁻ h, β (h⁻¹ * g) * Φ g * β₁ (r⁻¹ * g) ∂ν ∂μ ∂ρ := by
        refine lintegral_congr fun r => ?_
        exact lintegral_lintegral_swap
          (show Measurable fun p : G × G => β (p.1⁻¹ * p.2) * Φ p.2 * β₁ (r⁻¹ * p.2) by fun_prop).aemeasurable
    _ = ∫⁻ r, ∫⁻ g, Φ g * β₁ (r⁻¹ * g) ∂μ ∂ρ := by
        refine lintegral_congr fun r => lintegral_congr fun g => ?_
        simp_rw [mul_assoc]
        rw [lintegral_mul_const _ (show Measurable fun h : G => β (h⁻¹ * g) by fun_prop), hinvβ g, one_mul]
    _ = ∫⁻ r, ∫⁻ g, Φ (r * g) * β₁ g ∂μ ∂ρ := by
        refine lintegral_congr fun r => ?_
        refine (lintegral_mul_left_eq_self (μ := μ) (fun x => Φ x * β₁ (r⁻¹ * x)) r).symm.trans
          (lintegral_congr fun g => ?_)
        show Φ (r * g) * β₁ (r⁻¹ * (r * g)) = _
        rw [inv_mul_cancel_left]
    _ = ∫⁻ g, ∫⁻ r, Φ (r * g) * β₁ g ∂ρ ∂μ :=
        lintegral_lintegral_swap
          (show Measurable fun p : G × G => Φ (p.1 * p.2) * β₁ p.2 by fun_prop).aemeasurable
    _ = ∫⁻ g, ∫⁻ r, Φ (r * g) ∂ρ ∂μ.withDensity β₁ := by
        have hm : Measurable fun g => ∫⁻ r, Φ (r * g) ∂ρ := by
          have : Measurable fun p : G × G => Φ (p.2 * p.1) := by fun_prop
          exact this.lintegral_prod_right'
        rw [lintegral_withDensity_eq_lintegral_mul _ hβ₁ hm]
        refine lintegral_congr fun g => ?_
        rw [lintegral_mul_const _ (show Measurable fun r : G => Φ (r * g) by fun_prop)]
        exact mul_comm _ _

end QuadraticTransferFirst

theorem isUnit_last_join : Q1 := by
  intro G _ _ _ _ _ _ _ μ _ ν ρ _ _ H β β₁ hinv hH hβ hβ₁ h1 Φ hΦ hΦH
  exact QuadraticTransferFirst.main μ ν ρ H β β₁ hinv hH hβ hβ₁ h1 Φ hΦ hΦH

end PositivityTheory.AdelicQuotientData

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace LastRowIntegral

open ValuativeRel

theorem mul_apply_last {R : Type*} [CommRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) (i : Fin n)
    (hi : (i : ℕ) + 1 = n) (h0 : ∀ j, j < i → A i j = 0) (h1 : A i i = 1) (c : Fin n) : (A * B) i c = B i c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [h1, one_mul]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [h0 j h, zero_mul]
    · exfalso
      have h2 := j.isLt
      have h3 : (i : ℕ) < j := h
      omega
  · intro h; exact absurd (Finset.mem_univ i) h

variable {E : Type} [Field E] [NumberField E]

theorem lastRow_eq {k : ℕ} (hk : 1 ≤ k) (g : GA E k) (c : Fin k) :
    lastRow g c = g.val ⟨k - 1, by omega⟩ c := by
  unfold lastRow
  rw [Finset.sum_eq_single ⟨k - 1, by omega⟩]
  · rw [if_pos (by simp only; omega)]
  · intro j _ hj
    rw [if_neg]
    intro h; apply hj; ext; simp only; omega
  · intro h; exact absurd (Finset.mem_univ _) h

theorem lastRow_UU {k : ℕ} (hk : 1 ≤ k) {n : GA E k} (hn : UU 0 n) (g : GA E k) :
    lastRow (n * g) = lastRow g := by
  funext c
  rw [lastRow_eq hk, lastRow_eq hk, Units.val_mul]
  refine mul_apply_last _ _ _ (by simp only; omega) (fun j hj => hn.1 _ _ hj) (hn.2.1 _) c

theorem continuous_lastRow {k : ℕ} : Continuous (lastRow : GA E k → Fin k → Ad E) := by
  refine continuous_pi fun c => continuous_finsetSum _ fun i _ => ?_
  split_ifs
  · exact Units.continuous_val.matrix_elem i c
  · exact continuous_const

theorem continuous_sFin : Continuous (sFin E) :=
  (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))

theorem mem_int (w : Pl E) (x : w.adicCompletion E) (hx : x ∈ 𝒪[w.adicCompletion E]) :
    x ∈ w.adicCompletionIntegers E := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  have hO : 𝒪[w.adicCompletion E] = (w.adicCompletionIntegers E).toSubring := by
    ext y
    rw [Valuation.mem_integer_iff, he.le_one_iff_le_one]
    exact Iff.rfl
  rw [hO] at hx
  exact hx

end LastRowIntegral

namespace LastRowIntegral

open ValuativeRel GroundTheory.Automorphic.Iwasawa

theorem last_int {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {k m : ℕ} (hk : 1 ≤ k) (hkm : k < m) (ιw : GL (Fin k) F →* GL (Fin m) F)
    (hu : ∀ n ∈ unipotent F k, ιw n ∈ unipotent F m)
    (hκ : ∀ κ ∈ GLnLocal.integralGL F k, ιw κ ∈ GLnLocal.integralGL F m)
    (ht : ∀ l, ιw (torusPow F k l) = torusPow F m (pad m l)) (h : GL (Fin k) F)
    (ha : Antitone (iwasawaExponent F m (ιw h))) (c : Fin k) : h ⟨k - 1, by omega⟩ c ∈ 𝒪[F] := by
  obtain ⟨u, hu0, κ, hκ0, he⟩ := exists_eq_mul_torusPow_iwasawaExponent F k h
  set l := iwasawaExponent F k h
  have hl : iwasawaExponent F m (ιw h) = pad m l := by
    rw [he, map_mul, map_mul, ht]
    exact iwasawaExponent_eq F m (hu u hu0) (hκ κ hκ0)
  rw [hl] at ha
  have h0 : 0 ≤ l ⟨k - 1, by omega⟩ := by
    have := ha (show (⟨k - 1, by omega⟩ : Fin m) ≤ ⟨k, hkm⟩ from Fin.mk_le_mk.2 (by omega))
    simpa [pad, show k - 1 < k by omega] using this
  obtain ⟨e, he'⟩ := Int.eq_ofNat_of_zero_le h0
  rw [he, Units.val_mul, Units.val_mul, Matrix.mul_assoc,
    mul_apply_last _ _ _ (by simp only; omega) (fun j hj => hu0.1 hj) (hu0.2 _) c, coe_torusPow,
    Matrix.diagonal_mul, he', zpow_natCast]
  exact Subring.mul_mem _ (Subring.pow_mem _ (GLnLocal.uniformizer F).2 _)
    (((GLnLocal.mem_integralGL_iff F k).1 hκ0).1 _ _)

end LastRowIntegral

theorem last_row_integral_of : jumpWindows.G0 → CornerEmbedding → K8 → K6 := by
  intro hG0 h5 h8 E _ _ _ m k hk hkm ψ hψ S hS ι hι α M U φ hP
  obtain ⟨hex, hι5⟩ := h5 E m k hkm.le
  obtain ⟨-, hblk, hsurj, -, -, hcpt, -, hloc, hcInf, hUU, -⟩ := hι5 ι hι
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hg0, -, -, -, -⟩ := hG0 E k
  obtain ⟨-, -, hW⟩ := h8 E m ψ hψ S hS α φ hP.good hP.sat
  obtain ⟨C, -, hCblk, hCcpt, -, -, hB⟩ := hP.bump
  choose ιw hιw using fun w : Pl E => hex (w.adicCompletion E)
  have hlw := fun w => hloc w (ιw w) (hιw w)
  refine ⟨(fun p => p.1 + p.2) '' ((lastRow '' (ι ⁻¹' C)) ×ˢ
    Set.pi Set.univ (fun _ => sFin E '' (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)))), ?_, ?_⟩
  · exact (((hcpt C hCcpt).image LastRowIntegral.continuous_lastRow).prod (isCompact_univ_pi fun _ =>
      (GroundTheory.Global.isCompact_integralFiniteAdeles E).image LastRowIntegral.continuous_sFin)).image
      (continuous_fst.add continuous_snd)
  intro g hg
  obtain ⟨hW1, hW2⟩ := hW (ι g) hg
  obtain ⟨g₀, h0i, h0S, h0in⟩ := hg0 S g
  have hinf : cInf (ι g₀) = cInf (ι g) := by
    have e : g = g₀ * (g₀⁻¹ * g) := by group
    have h1 : cInf (g₀⁻¹ * g) = 1 := by rw [map_mul, map_inv, h0i, inv_mul_cancel]
    conv_rhs => rw [e, map_mul, map_mul, hcInf _ h1, mul_one]
  have hSl : ∀ w ∈ S, cLoc w (ι g₀) = cLoc w (ι g) := fun w hw => by
    rw [(hlw w).2.1, (hlw w).2.1, h0S w hw]
  have hin : InS S (ι g₀) := fun w hw => by rw [(hlw w).2.1, h0in w hw, map_one]
  have hne := hW1 (ι g₀) hinf hSl hin
  have hmir : Mir k (ι g₀) := fun i c h => hblk g₀ i c (h.imp id Nat.le_of_lt)
  obtain ⟨n, c, hc, t, hn, -, heq, -, -⟩ := hB (ι g₀) ⟨hin, hmir⟩ hne
  obtain ⟨c', rfl⟩ := hsurj c (hCblk c hc)
  have hn' : n = ι (g₀ * c'⁻¹) := by rw [map_mul, map_inv, heq, mul_inv_cancel_right]
  have hU0 : UU 0 (g₀ * c'⁻¹) := (hUU _).1 (hn' ▸ hn)
  have hA : lastRow g₀ = lastRow c' := by
    conv_lhs => rw [show g₀ = (g₀ * c'⁻¹) * c' by group]
    exact LastRowIntegral.lastRow_UU hk hU0 c'
  refine ⟨(lastRow g₀, lastRow g - lastRow g₀), ⟨⟨c', hc, hA.symm⟩, fun i _ => ?_⟩, by simp⟩
  refine ⟨pFin E ((lastRow g - lastRow g₀) i), ?_, ?_⟩
  · intro v
    change pLoc E v (pFin E ((lastRow g - lastRow g₀) i)) ∈ v.adicCompletionIntegers E
    rw [Pi.sub_apply, LastRowIntegral.lastRow_eq hk, LastRowIntegral.lastRow_eq hk, map_sub, map_sub]
    change (cLoc v g).val _ i - (cLoc v g₀).val _ i ∈ v.adicCompletionIntegers E
    by_cases hv : v ∈ S
    · rw [h0S v hv, sub_self]; exact zero_mem _
    · rw [h0in v hv]
      refine sub_mem (LastRowIntegral.mem_int v _ ?_) (LastRowIntegral.mem_int v _ ?_)
      · have ha := hW2 v hv
        rw [(hlw v).2.1] at ha
        exact LastRowIntegral.last_int hk hkm (ιw v) (hlw v).2.2.1 (hlw v).2.2.2.1 (hlw v).2.2.2.2 _ ha i
      · change (1 : Matrix (Fin k) (Fin k) (v.adicCompletion E)) _ i ∈ _
        rw [Matrix.one_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
  · refine ad_ext ?_ rfl
    change (infEq E).symm 0 = _
    rw [map_zero]
    change (0 : Cinf E) = pInf E ((lastRow g - lastRow g₀) i)
    rw [Pi.sub_apply, LastRowIntegral.lastRow_eq hk, LastRowIntegral.lastRow_eq hk, map_sub]
    change (0 : Cinf E) = (cInf g).val _ i - (cInf g₀).val _ i
    rw [h0i, sub_self]

end PositivityTheory.AdelicQuotientData

end
end
