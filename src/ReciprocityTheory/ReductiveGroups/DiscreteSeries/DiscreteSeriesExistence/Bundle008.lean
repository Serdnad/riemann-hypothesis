module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle006
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle007
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IntegrableOfDecayVG
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FormulaF
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsEquiv
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle003
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle005

@[expose] public section

section

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem sigLam_equiv_data (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    {V : Submodule ℂ D} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hV0 : V ≠ ⊥) :
    ∃ U : Hlam ε Ψ v₀ ≃ₗᵢ[ℂ] closGen E V, ∀ g ∈ UJset ε, ∀ x : Hlam ε Ψ v₀,
      ((U (sigLam ε Ψ v₀ g x) : closGen E V) : H) = σ g ((U x : closGen E V) : H) := by
  have hσ₁ := rreg_isURepOn ε
  obtain ⟨U, hU⟩ := data_unitary_equiv hgap hσ₁ (isDerivedOn_smE hσ₁) (datumV_isKIrrHW hP hv₀)
    (datumV_casimir hP v₀) (datumV_kStable hP v₀) (datumV_ne_bot hP hv₀) hσ hD hV hc hVK hV0
  exact ⟨U, fun g hg x => hU g hg (sigLam ε Ψ v₀ g x) x (sigLam_coe hgap hP hv₀ hg x)⟩

theorem puniq_exists_h {lam' : Fin n → ℝ} (hgap : StdGap ε lam) (hgap' : StdGap ε lam') :
    ∃ h : ℝ, GapAtLeast ε lam h ∧ GapAtLeast ε lam' h ∧
      (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h ∧ (n : ℝ) - 1 < h := by
  obtain ⟨-, h1, hg1, hb1⟩ := hgap
  obtain ⟨-, h2, hg2, hb2⟩ := hgap'
  have hpq0 : (0 : ℝ) ≤ (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) := by positivity
  by_cases hex : ∃ a b : Fin n, ε a ≠ ε b
  · obtain ⟨a, b, hab⟩ := hex

    have hp : 0 < pOf ε := by
      unfold pOf
      apply Finset.card_pos.mpr
      rcases Bool.eq_false_or_eq_true (ε a) with ha | ha
      · exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
      · have hb : ε b = true := by
          rw [ha] at hab
          revert hab
          cases ε b <;> simp
        exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩⟩
    have hq : 0 < qOf ε := by
      unfold qOf
      apply Finset.card_pos.mpr
      rcases Bool.eq_false_or_eq_true (ε a) with ha | ha
      · have hb : ε b = false := by
          rw [ha] at hab
          revert hab
          cases ε b <;> simp
        exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩⟩
      · exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
    have hp' : (1 : ℝ) ≤ (pOf ε : ℝ) := by exact_mod_cast hp
    have hq' : (1 : ℝ) ≤ (qOf ε : ℝ) := by exact_mod_cast hq
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hpq : (1 : ℝ) ≤ (pOf ε : ℝ) * (qOf ε : ℝ) := by nlinarith
    have hle : (n : ℝ) * 1 ≤ (n : ℝ) * ((pOf ε : ℝ) * (qOf ε : ℝ)) := mul_le_mul_of_nonneg_left hpq hn
    have hm := lt_min hb1 hb2
    refine ⟨min h1 h2, fun a b hab => le_trans (min_le_left _ _) (hg1 a b hab),
      fun a b hab => le_trans (min_le_right _ _) (hg2 a b hab), hm, ?_⟩
    nlinarith
  · push_neg at hex
    refine ⟨(n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + (n : ℝ) + 2, fun a b h => absurd (hex a b) h,
      fun a b h => absurd (hex a b) h, by linarith, ?_⟩
    linarith

theorem sigLam_inj (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) {lam' : Fin n → ℝ} {T' : S7.KType ε (lowK ε lam')}
    {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)} {v₀' : T'.V} (hgap' : StdGap ε lam')
    (hP' : IsPsiFor ε lam' T' Ψ') (hv₀' : v₀' ≠ 0) (U : Hlam ε Ψ v₀ ≃ₗᵢ[ℂ] Hlam ε Ψ' v₀')
    (hU : ∀ g ∈ UJset ε, ∀ x : Hlam ε Ψ v₀, U (sigLam ε Ψ v₀ g x) = sigLam ε Ψ' v₀' g (U x)) :
    lam = lam' := by
  obtain ⟨h, hg, hg', hb, hn⟩ := puniq_exists_h hgap hgap'
  have hU' : ∀ g ∈ UJset ε, ∀ y : Hlam ε Ψ' v₀', U.symm (sigLam ε Ψ' v₀' g y) = sigLam ε Ψ v₀ g (U.symm y) := by
    intro g hgU y
    have := hU g hgU (U.symm y)
    rw [LinearIsometryEquiv.apply_symm_apply] at this
    rw [← this, LinearIsometryEquiv.symm_apply_apply]
  have hK1 := puniq_isKTypeOf_map U (fun g hgK x => hU g (puniq_kset hgK) x) (sigLam_lowK hgap hP hv₀).1
  have hK2 := puniq_isKTypeOf_map U.symm (fun g hgK y => hU' g (puniq_kset hgK) y)
    (sigLam_lowK hgap' hP' hv₀').1
  have b1 := (sigLam_kType_bounds hgap' hP' hv₀' _ hK1).2 h hg' hb
  have b2 := (sigLam_kType_bounds hgap hP hv₀ _ hK2).2 h hg hb
  rw [mir_lowK_eq] at b1 b2
  by_contra hne
  have hne' : lowK ε lam ≠ lowK ε lam' := by
    intro heq
    apply hne
    funext a
    have := congrFun heq a
    simp only [lowK, Pi.add_apply, Pi.sub_apply] at this
    linarith
  have c1 := b1 hne'
  have c2 := b2 (Ne.symm hne')
  linarith

theorem puniq_psi_eq (hgap : StdGap ε lam) {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
    (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam T Ψ') (hv₀ : v₀ ≠ 0) :
    ∀ g ∈ UJset ε, Ψ' g = Ψ g := by
  have hσ₁ := rreg_isURepOn ε
  obtain ⟨U, hU⟩ := sigLam_equiv_data (Ψ := Ψ) hgap hP hv₀ hσ₁ (isDerivedOn_smE hσ₁)
    (datumV_isKIrrHW hP' hv₀) (datumV_casimir hP' v₀) (datumV_kStable hP' v₀) (datumV_ne_bot hP' hv₀)
  let U' : Hlam ε Ψ v₀ ≃ₗᵢ[ℂ] Hlam ε Ψ' v₀ := U
  have hUi : ∀ g ∈ UJset ε, ∀ x, U' (sigLam ε Ψ v₀ g x) = sigLam ε Ψ' v₀ g (U' x) := fun g hg x =>
    Subtype.ext ((hU g hg x).trans (sigLam_coe hgap hP' hv₀ hg (U' x)).symm)
  have hK := puniq_isKTypeOf_map U' (fun g hgK x => hUi g (puniq_kset hgK) x) (sigLam_lowK hgap hP hv₀).1
  have hKeq := (sigLam_lowK hgap hP' hv₀).2 _ hK
  let xv : T.V → Hlam ε Ψ v₀ := fun v => ⟨uniformisationL2 ε Ψ v₀ v, datumEmbedding_mem_Hlam hP v⟩
  have hxv_mem : ∀ v, xv v ∈ lowKSubLam ε Ψ v₀ := by
    intro v
    show (xv v : L2 ε) ∈ (datumV ε Ψ v₀).map (smD ε (rreg ε)).subtype
    exact ⟨⟨uniformisationL2 ε Ψ v₀ v, datumEmbedding_mem_smooth hP v₀ v⟩, (mem_datumV_iff hP v₀ _).2 ⟨v, rfl⟩, rfl⟩
  have hA : ∀ v, ∃ v', ((U' (xv v) : Hlam ε Ψ' v₀) : L2 ε) = uniformisationL2 ε Ψ' v₀ v' := by
    intro v
    have h1 : U' (xv v) ∈ lowKSubLam ε Ψ' v₀ := by
      rw [← hKeq]
      exact ⟨xv v, hxv_mem v, rfl⟩
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 (Submodule.mem_comap.1 h1)
    obtain ⟨v', hv'⟩ := (mem_datumV_iff hP' v₀ y).1 hy
    exact ⟨v', hyx.symm.trans hv'⟩
  choose A hAv using hA
  have hj' := uniformisationL2_injective hP' hv₀
  have xv_add : ∀ v w, xv (v + w) = xv v + xv w := fun v w =>
    Subtype.ext (by rw [Submodule.coe_add]; exact datumEmbedding_add hP v₀ v w)
  have xv_smul : ∀ (c : ℂ) v, xv (c • v) = c • xv v := fun c v =>
    Subtype.ext (by rw [Submodule.coe_smul]; exact datumEmbedding_smul hP v₀ c v)
  have hAadd : ∀ v w, A (v + w) = A v + A w := by
    intro v w
    apply hj'
    rw [← hAv, xv_add, map_add (f := _), Submodule.coe_add, hAv, hAv, datumEmbedding_add hP']
  have hAsmul : ∀ (c : ℂ) v, A (c • v) = c • A v := by
    intro c v
    apply hj'
    rw [← hAv, xv_smul, map_smul, Submodule.coe_smul, hAv, datumEmbedding_smul hP']
  have hAk : ∀ (k : S7.KG ε) (v : T.V), A (T.op k v) = T.op k (A v) := by
    intro k v
    have hk : S7.toMK k ∈ UJset ε := (k : S7.UJ ε).2
    have e1 : xv (T.op k v) = sigLam ε Ψ v₀ (S7.toMK k) (xv v) :=
      Subtype.ext ((sigLam_coe hgap hP hv₀ hk (xv v)).trans (rightRegular_datumEmbedding hP v₀ v k)).symm
    apply hj'
    rw [← hAv, e1, hUi _ hk, sigLam_coe hgap hP' hv₀ hk, hAv, rightRegular_datumEmbedding hP' v₀ (A v) k]
  let Alin : T.V →ₗ[ℂ] T.V := { toFun := A, map_add' := hAadd, map_smul' := hAsmul }
  obtain ⟨c, hc⟩ := puniq_schur T Alin hAk
  have hc' : ∀ v, A v = c • v := hc
  have key : ∀ g ∈ UJset ε, ∀ v v' : T.V,
      ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) * inner ℂ v' (Ψ g v) =
        ((‖uniformisationL2 ε Ψ' v₀ T.w‖ ^ 2 : ℝ) : ℂ) * inner ℂ (A v') (Ψ' g (A v)) := by
    intro g hg v v'
    rw [← formulaF_sigLam hgap hP hv₀ hg v v', ← formulaF hgap hP' hv₀ hg (A v) (A v'), ← hAv, ← hAv,
      ← U'.inner_map_map (xv v') (sigLam ε Ψ v₀ g (xv v)), hUi g hg, Submodule.coe_inner,
      sigLam_coe hgap hP' hv₀ hg]
  have hr : ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have := datumEmbedding_highest_ne_zero hgap hP hv₀
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr this)
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
    show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * 1 = Jm ε
    simp
  have hw0 : T.w ≠ 0 := by
    intro h
    have := T.w_norm
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hW : inner ℂ T.w T.w ≠ 0 := inner_self_ne_zero.mpr hw0
  have e1 := key 1 h1 T.w T.w
  rw [hP.2.1, hP'.2.1] at e1
  simp only [hc', map_smul, ContinuousLinearMap.one_apply, inner_smul_left, inner_smul_right] at e1
  have hrr : ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) =
      ((‖uniformisationL2 ε Ψ' v₀ T.w‖ ^ 2 : ℝ) : ℂ) * ((starRingEnd ℂ) c * c) := by
    apply mul_right_cancel₀ hW
    rw [e1]
    ring
  intro g hg
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun v' => ?_
  have e := key g hg v v'
  simp only [hc', map_smul, inner_smul_left, inner_smul_right] at e
  have e' : ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) * inner ℂ v' (Ψ g v) =
      ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) * inner ℂ v' (Ψ' g v) := by
    rw [e, hrr]
    ring
  exact (mul_left_cancel₀ hr e').symm

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem sigZeroDecay_one_le_hs {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (i : Fin n) : 1 ≤ S7.hs g := by
  unfold S7.hs
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have h1 : (gᴴ * Jm ε * g) i i = Jm ε i i := by rw [hg']
  rw [Matrix.mul_apply] at h1
  simp only [Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at h1
  have key : ‖(if ε i = true then (1 : ℂ) else -1)‖ ≤ ∑ x, ‖g x i‖ ^ 2 := by
    rw [← h1]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [norm_mul, norm_mul, norm_star]
    split_ifs <;> simp [sq]
  have hrow : ∑ x, ‖g x i‖ ^ 2 ≤ ∑ a, ∑ b, ‖g a b‖ ^ 2 :=
    Finset.sum_le_sum fun a _ =>
      Finset.single_le_sum (f := fun b => ‖g a b‖ ^ 2) (fun b _ => by positivity) (Finset.mem_univ i)
  have hn : ‖(if ε i = true then (1 : ℂ) else -1)‖ = 1 := by
    split_ifs <;> simp
  linarith

theorem sigZeroDecay_real {h c s N G : ℝ} (hh : 0 < h) (hc : 1 ≤ c) (hN : 0 < N)
    (hG : 0 < G) (hGle : G ≤ N * Real.exp s) :
    Real.exp (-(h / 8) * min (s ^ 2) (s / c)) ≤
      (Real.exp (h / (8 * c)) * N ^ (h / (8 * c))) * G ^ (-(h / (8 * c))) := by
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  have ha : 0 < h / (8 * c) := by positivity
  have hlog : Real.log G ≤ Real.log N + s := by
    have h1 := Real.log_le_log hG hGle
    rwa [Real.log_mul hN.ne' (Real.exp_pos s).ne', Real.log_exp] at h1
  have hcs : c * (s / c) = s := by
    first
      | (field_simp; done)
      | (field_simp; ring)
  have hmin : s - 1 ≤ c * min (s ^ 2) (s / c) := by
    rcases min_cases (s ^ 2) (s / c) with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]
      nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg s), sq_nonneg (s - 1)]
    · rw [h1, hcs]
      linarith
  have hh8 : h / 8 = c * (h / (8 * c)) := by
    first
      | (field_simp; done)
      | (field_simp; ring)
  rw [Real.rpow_def_of_pos hN, Real.rpow_def_of_pos hG, ← Real.exp_add, ← Real.exp_add,
    Real.exp_le_exp, hh8]
  nlinarith [mul_le_mul_of_nonneg_left hmin ha.le, mul_le_mul_of_nonneg_left hlog ha.le]

theorem dec_gN_sigLam (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) {h : ℝ} (hq : 1 ≤ S7.q0 ε)
    (hdec : ∀ (k : S7.KG ε) (X : Matrix (Fin n) (Fin n) ℂ), inP ε X →
      ‖Ψ (S7.toMK k * NormedSpace.exp X)‖ ≤
        Real.exp (-(h / 8) * min (S7.hs X) (Real.sqrt (S7.hs X) / Real.sqrt (2 * S7.q0 ε))))
    (v v' : T.V) :
    ∃ C : ℝ, ∀ g ∈ UJset ε,
      ‖inner ℂ (uniformisationL2 ε Ψ v₀ v') (rreg ε g (uniformisationL2 ε Ψ v₀ v))‖ ≤
        C * Real.sqrt (S7.hs g) ^ (-(h / (8 * Real.sqrt (2 * (S7.q0 ε : ℝ))))) := by

  have hqn : S7.q0 ε ≤ n := by
    unfold S7.q0 pOf
    exact (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans_eq (Finset.card_fin n))
  have hn : 0 < n := lt_of_lt_of_le one_pos (hq.trans hqn)
  have hG1 : ∀ g ∈ UJset ε, 1 ≤ Real.sqrt (S7.hs g) := fun g hg =>
    Real.one_le_sqrt.mpr (sigZeroDecay_one_le_hs hg ⟨0, hn⟩)
  set c := Real.sqrt (2 * (S7.q0 ε : ℝ)) with hcdef
  have hc : 1 ≤ c := by
    rw [hcdef, Real.one_le_sqrt]
    have : (1 : ℝ) ≤ S7.q0 ε := by exact_mod_cast hq
    linarith
  rcases le_or_gt h 0 with hh | hh
  ·
    refine ⟨‖uniformisationL2 ε Ψ v₀ v'‖ * ‖uniformisationL2 ε Ψ v₀ v‖, fun g hg => ?_⟩
    have hiso : ‖rreg ε g (uniformisationL2 ε Ψ v₀ v)‖ = ‖uniformisationL2 ε Ψ v₀ v‖ := (rreg_isURepOn ε).2.1 g hg _
    have hpow : 1 ≤ Real.sqrt (S7.hs g) ^ (-(h / (8 * c))) := by
      refine Real.one_le_rpow (hG1 g hg) ?_
      have : h / (8 * c) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hh (by linarith)
      linarith
    calc ‖inner ℂ (uniformisationL2 ε Ψ v₀ v') (rreg ε g (uniformisationL2 ε Ψ v₀ v))‖
        ≤ ‖uniformisationL2 ε Ψ v₀ v'‖ * ‖rreg ε g (uniformisationL2 ε Ψ v₀ v)‖ := norm_inner_le_norm _ _
      _ = ‖uniformisationL2 ε Ψ v₀ v'‖ * ‖uniformisationL2 ε Ψ v₀ v‖ := by rw [hiso]
      _ ≤ ‖uniformisationL2 ε Ψ v₀ v'‖ * ‖uniformisationL2 ε Ψ v₀ v‖ * Real.sqrt (S7.hs g) ^ (-(h / (8 * c))) :=
          le_mul_of_one_le_right (by positivity) hpow
  ·
    refine ⟨‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 * ‖v'‖ * ‖v‖ *
      (Real.exp (h / (8 * c)) * Real.sqrt n ^ (h / (8 * c))), fun g hg => ?_⟩
    obtain ⟨k, X, hX, rfl⟩ := S7.polar_exists hg
    have hd := dec_sigLam hgap hP hv₀ hdec k hX v v'
    set s := Real.sqrt (S7.hs X) with hsdef
    have hsX : S7.hs X = s ^ 2 := (Real.sq_sqrt (S7.hs_nonnegVG X)).symm
    have hN : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have hGpos : 0 < Real.sqrt (S7.hs (S7.toMK k * NormedSpace.exp X)) :=
      lt_of_lt_of_le one_pos (hG1 _ hg)
    have hGle : Real.sqrt (S7.hs (S7.toMK k * NormedSpace.exp X)) ≤ Real.sqrt n * Real.exp s := by
      rw [S7.hs_kmulVG]
      have h2 : S7.hs (NormedSpace.exp X) ≤ (Real.sqrt n * Real.exp s) ^ 2 := by
        have e2 : Real.exp s ^ 2 = Real.exp (2 * s) := by
          rw [← Real.exp_nat_mul]; norm_num
        have := S7.hs_exp_leVG X
        rw [← hsdef] at this
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), e2]
        exact this
      calc Real.sqrt (S7.hs (NormedSpace.exp X)) ≤ Real.sqrt ((Real.sqrt n * Real.exp s) ^ 2) :=
            Real.sqrt_le_sqrt h2
        _ = Real.sqrt n * Real.exp s := Real.sqrt_sq (by positivity)
    have hr := sigZeroDecay_real hh hc hN hGpos hGle
    rw [← hsX] at hr
    have hM : 0 ≤ ‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 * ‖v'‖ * ‖v‖ := by positivity
    calc _ ≤ ‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 * ‖v'‖ * ‖v‖ *
          Real.exp (-(h / 8) * min (S7.hs X) (Real.sqrt (S7.hs X) / Real.sqrt (2 * S7.q0 ε))) := hd
      _ ≤ ‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 * ‖v'‖ * ‖v‖ *
          ((Real.exp (h / (8 * c)) * Real.sqrt n ^ (h / (8 * c))) *
            Real.sqrt (S7.hs (S7.toMK k * NormedSpace.exp X)) ^ (-(h / (8 * c)))) :=
          mul_le_mul_of_nonneg_left hr hM
      _ = _ := by ring

end ReciprocityTheory.ChartRestriction.DS
end
end
