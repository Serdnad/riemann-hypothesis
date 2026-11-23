module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenericBlockMatrixIsBlockDiag
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle087
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle078
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle084
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle079
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
public import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle088
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle102
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Factor

section Holo

variable {e : ℕ} {S : Type} [TopologicalSpace S]

theorem holoOn_mono (A : FinHolAtlas e S) {U V : Set S} {f : S → ℂ} (h : A.HoloOn V f) (hU : U ⊆ V) :
    A.HoloOn U f :=
  fun j => (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hU))

theorem holoOn_const (A : FinHolAtlas e S) (U : Set S) (c : ℂ) : A.HoloOn U fun _ => c := fun _ _ _ =>
  analyticAt_const

theorem holoOn_mul (A : FinHolAtlas e S) {U : Set S} {f g : S → ℂ} (hf : A.HoloOn U f) (hg : A.HoloOn U g) :
    A.HoloOn U fun w => f w * g w := fun j u hu => (hf j u hu).mul (hg j u hu)

theorem holoOn_zpow (A : FinHolAtlas e S) {U : Set S} {f : S → ℂ} (hf : A.HoloOn U f)
    (h0 : ∀ w ∈ U, f w ≠ 0) (n : ℤ) : A.HoloOn U fun w => f w ^ n := fun j u hu =>
  (hf j u hu).zpow (h0 _ hu.2)

theorem holoOn_prod (A : FinHolAtlas e S) {U : Set S} {κ : Type} (s : Finset κ) {f : κ → S → ℂ}
    (hf : ∀ i ∈ s, A.HoloOn U (f i)) : A.HoloOn U fun w => ∏ i ∈ s, f i w := by
  induction s using Finset.induction_on with
  | empty => simpa using holoOn_const A U 1
  | insert i s hi ih =>
    have h := holoOn_mul A (hf i (Finset.mem_insert_self i s))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))
    simpa only [Finset.prod_insert hi] using h

theorem holoOn_minor (A : FinHolAtlas e S) {U : Set S} {N : ℕ} {H : S → Matrix (Fin N) (Fin N) ℂ}
    (hH : ∀ r s, A.HoloOn U fun w => H w r s) (I J : Finset (Fin N)) :
    A.HoloOn U fun w => minorIJ (H w) I J := by
  have h := StepW.ValHolo.holoOn_eval A (b := fun w (q : Fin N × Fin N) => H w q.1 q.2) (fun q => hH q.1 q.2)
    (minorIJ (Matrix.of fun r s => (MvPolynomial.X (r, s) : MvPolynomial (Fin N × Fin N) ℤ)) I J)
  have e : (fun w => minorIJ (H w) I J) = fun w => eval (fun q : Fin N × Fin N => H w q.1 q.2)
      (map (Int.castRingHom ℂ)
        (minorIJ (Matrix.of fun r s => (MvPolynomial.X (r, s) : MvPolynomial (Fin N × Fin N) ℤ)) I J)) := by
    funext w
    let f : MvPolynomial (Fin N × Fin N) ℤ →+* ℂ :=
      (eval fun q : Fin N × Fin N => H w q.1 q.2).comp (map (Int.castRingHom ℂ))
    have hm : (Matrix.of fun r s => (MvPolynomial.X (r, s) : MvPolynomial (Fin N × Fin N) ℤ)).map f = H w := by
      ext r s
      simp [f]
    have := minorIJ_map f (Matrix.of fun r s => (MvPolynomial.X (r, s) : MvPolynomial (Fin N × Fin N) ℤ)) I J
    rw [hm] at this
    exact this
  rw [e]
  exact h

theorem prod_local (A : FinHolAtlas e S) {V : Set S} {y₀ : S} {N : ℕ} (hV : IsOpen V) (hy : y₀ ∈ V)
    (g : Fin N → S → ℂ) (n : Fin N → ℤ)
    (key : ∀ i, ∃ W : Set S, IsOpen W ∧ y₀ ∈ W ∧ W ⊆ V ∧ A.HoloOn W (g i) ∧ ∀ w ∈ W, g i w ≠ 0) :
    ∃ V' : Set S, IsOpen V' ∧ y₀ ∈ V' ∧ V' ⊆ V ∧ A.HoloOn V' (fun w => ∏ i, g i w ^ n i) ∧
      ∀ w ∈ V', ∏ i, g i w ^ n i ≠ 0 := by
  choose W hW hyW hWV hh h0 using key
  have hsub : ∀ i, V ∩ ⋂ i, W i ⊆ W i := fun i => Set.inter_subset_right.trans (Set.iInter_subset _ i)
  refine ⟨V ∩ ⋂ i, W i, hV.inter (isOpen_iInter_of_finite hW), ⟨hy, Set.mem_iInter.2 hyW⟩,
    Set.inter_subset_left, ?_, ?_⟩
  · exact holoOn_prod A _ fun i _ =>
      holoOn_zpow A (holoOn_mono A (hh i) (hsub i)) (fun w hw => h0 i w (hsub i hw)) (n i)
  · exact fun w hw => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (h0 i w (hsub i hw))

end Holo

theorem minor_w_ne {N j : ℕ} (hj : j ≤ N) (i : Fin N) (hi : (i : ℕ) + 1 = j) {T : Matrix (Fin N) (Fin N) ℂ}
    (hT : IsBlockDiag j T) (hd : T.det ≠ 0) : minorIJ T (wIdx N j) (wIdx N j) ≠ 0 := by
  have h := FrameChange.detFac_ne_zero hj i hT hd
  rw [detFac, if_pos hi.ge] at h
  exact left_ne_zero_of_mul h

theorem minor_om_ne {N j : ℕ} (hj : j ≤ N) (i : Fin N) (hi : (i : ℕ) + 1 = N) {T : Matrix (Fin N) (Fin N) ℂ}
    (hT : IsBlockDiag j T) (hd : T.det ≠ 0) : minorIJ T (omIdx N j) (omIdx N j) ≠ 0 := by
  have h := FrameChange.detFac_ne_zero hj i hT hd
  rw [detFac, if_pos hi] at h
  exact right_ne_zero_of_mul h

theorem val_ne {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x)) {s : Ω} (h0 : s ≠ 0)
    (hs : RegAt x (mCoordIdeal z) s) (hi : RegAt x (mCoordIdeal z) s⁻¹) : valAt x s z ≠ 0 := by
  intro e
  have h := (reg_mul hz hs hi).2
  rw [mul_inv_cancel₀ h0, e, zero_mul] at h
  exact one_ne_zero (((ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.2.1).symm.trans h)

theorem improper_factor : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (V : Set X) (y₀ : X) (zb : X → (Σ k, baseIdx ι M.blk k) → ℂ) (Hm : X → Matrix (Fin N) (Fin N) ℂ) (F : FrameData ι Ψ N M.Ω M.blk) (τ : Ψ) (a : Fin N), IsOpen V → y₀ ∈ V → (∀ q, A.HoloOn V fun w => zb w q) → (∀ w ∈ V, zb w ∈ mcPts (mCoordIdeal M.x)) → (∀ w ∈ V, M.GoodAt F (mCoordIdeal (zb w))) → (∀ r s, A.HoloOn V fun w => Hm w r s) → (∀ w ∈ V, IsBlockDiag j (Hm w) ∧ (Hm w).det ≠ 0) → ∃ V' : Set X, IsOpen V' ∧ y₀ ∈ V' ∧ V' ⊆ V ∧ A.HoloOn V' (fun w => ∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (zb w) * (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (Hm w) (wIdx N j) (wIdx N j) else 1) else minorIJ (Hm w) (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)) ∧ ∀ w ∈ V', (∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (zb w) * (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (Hm w) (wIdx N j) (wIdx N j) else 1) else minorIJ (Hm w) (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)) ≠ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M e X _ A V y₀ zb Hm F τ a hV hy hzb hpt hgood hHm hdiag
  refine prod_local A hV hy (fun i w => if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (zb w) *
    (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (Hm w) (wIdx N j) (wIdx N j) else 1)
      else minorIJ (Hm w) (omIdx N j) (omIdx N j))) (fun i => xiCoef τ a (τ, i)) fun i => ?_
  by_cases hp : IsProperStep N j i
  · refine ⟨V, hV, hy, subset_rfl, ?_, fun w _ => ?_⟩
    · simp only [if_pos hp]
      exact holoOn_const A V 1
    · simp only [if_pos hp]
      exact one_ne_zero
  · have hnone : M.blk (τ, i) = none := (M.blk_none (τ, i)).2 hp
    obtain ⟨W, hW, hyW, hWV, hval⟩ := StepW.ValHolo.holoOn_valAt _ _ M.Ω M.x (F.υ (τ, i)) e X A V zb y₀ hV hy hzb hpt
      ((hgood y₀ hy).2.2 _ hnone).2.1
    have hm : A.HoloOn W fun w => (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (Hm w) (wIdx N j) (wIdx N j) else 1)
        else minorIJ (Hm w) (omIdx N j) (omIdx N j)) := by
      have hH : ∀ r s, A.HoloOn W fun w => Hm w r s := fun r s => holoOn_mono A (hHm r s) hWV
      by_cases h1 : (i : ℕ) + 1 = j
      · by_cases h2 : (a : ℕ) < j
        · simp only [if_pos h1, if_pos h2]
          exact holoOn_minor A hH _ _
        · simp only [if_pos h1, if_neg h2]
          exact holoOn_const A W 1
      · simp only [if_neg h1]
        exact holoOn_minor A hH _ _
    refine ⟨W, hW, hyW, hWV, ?_, fun w hw => ?_⟩
    · simp only [if_neg hp]
      exact holoOn_mul A hval hm
    · simp only [if_neg hp]
      have hwV := hWV hw
      have hv : valAt M.x (F.υ (τ, i)) (zb w) ≠ 0 :=
        val_ne (hpt w hwV) ((hgood w hwV).2.2 _ hnone).1 ((hgood w hwV).2.2 _ hnone).2.1
          ((hgood w hwV).2.2 _ hnone).2.2
      refine mul_ne_zero hv ?_
      by_cases h1 : (i : ℕ) + 1 = j
      · by_cases h2 : (a : ℕ) < j
        · simp only [if_pos h1, if_pos h2]
          exact minor_w_ne M.j_le i h1 (hdiag w hwV).1 (hdiag w hwV).2
        · simp only [if_pos h1, if_neg h2]
          exact one_ne_zero
      · simp only [if_neg h1]
        have h3 : (i : ℕ) + 1 = N := by
          by_contra h3
          exact hp ⟨h1, h3⟩
        exact minor_om_ne M.j_le i h3 (hdiag w hwV).1 (hdiag w hwV).2

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Factor
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TriStep

open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc

variable {N : ℕ}

theorem minorIJ_one_of_ne {I S : Finset (Fin N)} (hI : I ≠ S) :
    minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I S = 0 := by
  by_cases e : I.card = S.card
  · have hs : ¬ I ⊆ S := fun hs => hI (Finset.eq_of_subset_of_card_le hs e.ge)
    obtain ⟨a, ha, has⟩ := Finset.not_subset.mp hs
    exact minorIJ_eq_zero_of_row _ ha fun c hc => Matrix.one_apply_ne fun h => has (h ▸ hc)
  · exact minorIJ_of_card_ne _ e

theorem minorIJ_one_self' (S : Finset (Fin N)) : minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) S S = 1 := by
  rw [minorIJ_eq_det _ S S _ rfl rfl, Matrix.submatrix_one _ (S.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem det_submatrix_eq_zero (A : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N))
    (hA : ∀ I, I ≠ S → minorIJ A I S = 0) (f : Fin S.card → Fin N) (x : Fin S.card) (hx : f x ∉ S) :
    (A.submatrix f (S.orderEmbOfFin rfl)).det = 0 := by
  by_cases hf : Function.Injective f
  · let σ := Tuple.sort f
    have hm : StrictMono (f ∘ σ) :=
      (Tuple.monotone_sort f).strictMono_of_injective (hf.comp σ.injective)
    have hc : (Finset.univ.image f).card = S.card := by
      rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
    have hu : f ∘ σ = (Finset.univ.image f).orderEmbOfFin hc :=
      Finset.orderEmbOfFin_unique hc (fun y => Finset.mem_image_of_mem _ (Finset.mem_univ _)) hm
    have hI : Finset.univ.image f ≠ S := fun e => hx (e ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _))
    have h0 := hA _ hI
    rw [minorIJ_eq_det A _ S _ hc rfl, ← hu] at h0
    have h1 : A.submatrix (f ∘ σ) (S.orderEmbOfFin rfl) =
        (A.submatrix f (S.orderEmbOfFin rfl)).submatrix σ id := by
      ext a b; rfl
    rw [h1, Matrix.det_permute] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exfalso
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simp [e] at h
    · exact h
  · obtain ⟨a, b, hab, hne⟩ : ∃ a b, f a = f b ∧ a ≠ b := by
      simpa [Function.Injective] using hf
    exact Matrix.det_zero_of_row_eq hne (by ext y; simp [hab])

theorem eq_zero_of_minors (B : Matrix (Fin N) (Fin N) ℂ) (hB : B.det ≠ 0) (S : Finset (Fin N))
    (hA : ∀ I, I ≠ S → minorIJ B I S = 0) (r c : Fin N) (hr : r ∉ S) (hc : c ∈ S) : B r c = 0 := by
  set e := S.orderEmbOfFin rfl with he
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  have hS : minorIJ B S S ≠ 0 := by
    intro h0
    have h1 := minorIJ_mul B⁻¹ B S S
    rw [Matrix.nonsing_inv_mul _ hu, minorIJ_one_self',
      Finset.sum_eq_single S (fun I _ hI => by rw [hA I hI, mul_zero]) (by simp), h0, mul_zero] at h1
    exact one_ne_zero h1
  rw [minorIJ_eq_det B S S _ rfl rfl] at hS
  let M := B.submatrix e e
  let v : Fin S.card → ℂ := fun y => B r (e y)
  have hcr : Matrix.cramer Mᵀ v = 0 := by
    funext x
    have h1 : Mᵀ.updateCol x v = (B.submatrix (Function.update e x r) e)ᵀ := by
      ext a b
      by_cases hb : b = x
      · subst hb; simp [Matrix.updateCol_apply, v]
      · simp [Matrix.updateCol_apply, hb, M, Function.update_of_ne hb]
    rw [Matrix.cramer_apply, h1, Matrix.det_transpose]
    exact det_submatrix_eq_zero B S hA _ x (by simpa using hr)
  have hv : Mᵀ.det • v = 0 := by rw [← Matrix.mulVec_cramer, hcr, Matrix.mulVec_zero]
  have hv0 : v = 0 := by
    rcases smul_eq_zero.mp hv with h | h
    · rw [Matrix.det_transpose] at h; exact absurd h hS
    · exact h
  have hr' : c ∈ Set.range e := by rw [he, Finset.range_orderEmbOfFin]; exact hc
  obtain ⟨y, rfl⟩ := hr'
  exact congrFun hv0 y

theorem triangular_of_minors_proportional : ∀ (N j : ℕ) (h g : Matrix (Fin N) (Fin N) ℂ), j ≤ N → IsBlockDiag j h →
    IsBlockDiag j g → h.det ≠ 0 → g.det ≠ 0 →
    (∀ i : Fin N, IsProperStep N j i → ∃ μ : ℂ, ∀ I, minorIJ g I (stepCols N j i) = μ * minorIJ h I (stepCols N j i)) →
    (h⁻¹ * g).BlockTriangular id := by
  intro N j h g hj hh hg hdh hdg hμ
  have huh : IsUnit h.det := isUnit_iff_ne_zero.mpr hdh
  have hbd : IsBlockDiag j (h⁻¹ * g) := (hh.inv huh).mul hg
  have hdet : (h⁻¹ * g).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv]
    exact mul_ne_zero (by simpa using hdh) hdg
  have hstep : ∀ i : Fin N, IsProperStep N j i → ∀ r c : Fin N, r ∉ stepCols N j i → c ∈ stepCols N j i →
      (h⁻¹ * g) r c = 0 := by
    intro i hi r c hr hc
    obtain ⟨μ, hm⟩ := hμ i hi
    refine eq_zero_of_minors _ hdet _ (fun I hI => ?_) r c hr hc
    have h1 : minorIJ (h⁻¹ * g) I (stepCols N j i) =
        μ * minorIJ (h⁻¹ * h) I (stepCols N j i) := by
      rw [minorIJ_mul, minorIJ_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun I' _ => by rw [hm I']; ring
    rw [h1, Matrix.nonsing_inv_mul _ huh, minorIJ_one_of_ne hI, mul_zero]
  intro r s hrs
  have hsr : (s : ℕ) < r := hrs
  have hrN := r.2
  by_cases hb : ((r : ℕ) < N - j ↔ (s : ℕ) < N - j)
  · by_cases hω : (r : ℕ) < N - j
    · have hi : (s : ℕ) + j < N := by omega
      refine hstep ⟨(s : ℕ) + j, hi⟩ ⟨?_, ?_⟩ r s ?_ ?_
      · simp only; omega
      · simp only; omega
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_neg (by omega)]; omega
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_neg (by omega)]; omega
    · have hs' : N - j ≤ (s : ℕ) := by
        by_contra hc; exact hω (hb.mpr (by omega))
      have hi : (s : ℕ) - (N - j) < N := by omega
      refine hstep ⟨(s : ℕ) - (N - j), hi⟩ ⟨?_, ?_⟩ r s ?_ ?_
      · simp only; omega
      · simp only; omega
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_pos (by omega)]; omega
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_pos (by omega)]; omega
  · exact hbd r s hb

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TriStep
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Plane

variable {N : ℕ}

theorem minorIJ_image_of_tri {R : Type} [CommRing R] (M : Matrix (Fin N) (Fin N) R) (S : Finset (Fin N))
    (σ : Fin N → Fin N) (hσ : StrictMonoOn σ S)
    (hT : ∀ x ∈ S, ∀ y ∈ S, y < x → M (σ x) y = 0) :
    minorIJ M (S.image σ) S = ∏ c ∈ S, M (σ c) c := by
  have e : (S.image σ).card = S.card := Finset.card_image_of_injOn hσ.injOn
  unfold minorIJ
  rw [dite_eq_left e]
  have hf : (fun i => σ (S.orderEmbOfFin rfl i)) = ⇑((S.image σ).orderEmbOfFin e) := by
    apply Finset.orderEmbOfFin_unique e
    · intro i
      exact Finset.mem_image_of_mem σ (Finset.orderEmbOfFin_mem S rfl i)
    · intro i i' hii
      exact hσ (Finset.orderEmbOfFin_mem S rfl i) (Finset.orderEmbOfFin_mem S rfl i')
        ((S.orderEmbOfFin rfl).strictMono hii)
  rw [← hf, Matrix.det_of_upperTriangular]
  · simp only [Matrix.submatrix_apply]
    conv_rhs => rw [← Finset.map_orderEmbOfFin_univ S rfl]
    rw [Finset.prod_map]
    rfl
  · intro i i' hii
    exact hT _ (Finset.orderEmbOfFin_mem S rfl i) _ (Finset.orderEmbOfFin_mem S rfl i')
      ((S.orderEmbOfFin rfl).strictMono hii)

theorem mul_entry (B : Matrix (Fin N) (Fin N) ℂ) (ca cb x y : Fin N) (s : ℂ) :
    (B * (1 + Matrix.single cb ca s)) x y = B x y + if y = ca then s * B x cb else 0 := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  congr 1
  by_cases hy : y = ca
  · subst hy
    simp [Matrix.mul_single_apply_same, mul_comm]
  · simp [Matrix.mul_single_apply_of_ne, hy]

theorem one_entry (ca cb x y : Fin N) (s : ℂ) :
    (1 + Matrix.single cb ca s : Matrix (Fin N) (Fin N) ℂ) x y =
      (if x = y then 1 else 0) + if cb = x ∧ ca = y then s else 0 := by
  simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]

theorem param_core (S : Finset (Fin N)) (ca cb : Fin N) (hca : ca ∈ S) (hmax : ∀ c ∈ S, c ≤ ca) (hlt : ca < cb)
    (B : Matrix (Fin N) (Fin N) ℂ) (hB : B.BlockTriangular id) (t t' μ : ℂ)
    (H : ∀ J, minorIJ (B * (1 + Matrix.single cb ca t')) J S = μ * minorIJ (1 + Matrix.single cb ca t) J S) :
    μ = (∏ c ∈ S.erase ca, B c c) * (B ca ca + t' * B ca cb) ∧
      μ * t = (∏ c ∈ S.erase ca, B c c) * (t' * B cb cb) := by
  have hne : ∀ c ∈ S, c ≠ cb := fun c hc => ne_of_lt ((hmax c hc).trans_lt hlt)
  have hcaNe : ca ≠ cb := ne_of_lt hlt
  let σ : Fin N → Fin N := fun c => if c = ca then cb else c
  have hσca : σ ca = cb := if_pos rfl
  have hσne : ∀ c, c ≠ ca → σ c = c := fun c hc => if_neg hc
  have hσ : StrictMonoOn σ S := by
    intro x _ y hy hxy
    have hx' : x ≠ ca := ne_of_lt (hxy.trans_le (hmax y hy))
    rw [hσne x hx']
    by_cases hy' : y = ca
    · rw [hy', hσca]
      exact (hxy.trans_le (hmax y hy)).trans hlt
    · rw [hσne y hy']
      exact hxy
  have hge : ∀ x ∈ S, x ≤ σ x := by
    intro x hx
    by_cases hx' : x = ca
    · rw [hx', hσca]
      exact hlt.le
    · rw [hσne x hx']
  have hyne : ∀ x ∈ S, ∀ y, y < x → y ≠ ca := fun x hx y hy => ne_of_lt (hy.trans_le (hmax x hx))

  have L1 : minorIJ (B * (1 + Matrix.single cb ca t')) S S =
      (∏ c ∈ S.erase ca, B c c) * (B ca ca + t' * B ca cb) := by
    have h0 := minorIJ_image_of_tri (B * (1 + Matrix.single cb ca t')) S id strictMonoOn_id (by
      intro x hx y _ hy
      rw [mul_entry, if_neg (hyne x hx y hy), add_zero]
      exact hB hy)
    rw [Finset.image_id] at h0
    rw [h0, ← Finset.prod_erase_mul S _ hca]
    congr 1
    · refine Finset.prod_congr rfl fun c hc => ?_
      rw [id, mul_entry, if_neg (Finset.ne_of_mem_erase hc), add_zero]
    · rw [id, mul_entry, if_pos rfl]
  have R1 : minorIJ (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) S S = 1 := by
    have h0 := minorIJ_image_of_tri (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) S id strictMonoOn_id (by
      intro x hx y _ hy
      rw [id, one_entry, if_neg (ne_of_gt hy), if_neg (fun h => hne x hx h.1.symm), add_zero])
    rw [Finset.image_id] at h0
    rw [h0]
    refine Finset.prod_eq_one fun c hc => ?_
    rw [id, one_entry, if_pos rfl, if_neg (fun h => hne c hc h.1.symm), add_zero]

  have L2 : minorIJ (B * (1 + Matrix.single cb ca t')) (S.image σ) S =
      (∏ c ∈ S.erase ca, B c c) * (t' * B cb cb) := by
    rw [minorIJ_image_of_tri _ S σ hσ (by
      intro x hx y _ hy
      rw [mul_entry, if_neg (hyne x hx y hy), add_zero]
      exact hB (hy.trans_le (hge x hx))), ← Finset.prod_erase_mul S _ hca]
    congr 1
    · refine Finset.prod_congr rfl fun c hc => ?_
      have hc' := Finset.ne_of_mem_erase hc
      rw [hσne c hc', mul_entry, if_neg hc', add_zero]
    · have h0 : B cb ca = 0 := hB hlt
      rw [hσca, mul_entry, if_pos rfl, h0, zero_add]
  have R2 : minorIJ (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) (S.image σ) S = t := by
    rw [minorIJ_image_of_tri _ S σ hσ (by
      intro x hx y _ hy
      rw [one_entry, if_neg (ne_of_gt (hy.trans_le (hge x hx))),
        if_neg (fun h => hyne x hx y hy h.2.symm), add_zero]), ← Finset.prod_erase_mul S _ hca]
    have h1 : ∏ c ∈ S.erase ca, (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) (σ c) c = 1 := by
      refine Finset.prod_eq_one fun c hc => ?_
      have hc' := Finset.ne_of_mem_erase hc
      rw [hσne c hc', one_entry, if_pos rfl,
        if_neg (fun h => hne c (Finset.mem_of_mem_erase hc) h.1.symm), add_zero]
    rw [h1, one_mul, hσca, one_entry, if_neg (Ne.symm hcaNe), if_pos ⟨rfl, rfl⟩, zero_add]
  have e1 := H S
  have e2 := H (S.image σ)
  rw [L1, R1, mul_one] at e1
  rw [L2, R2] at e2
  exact ⟨e1.symm, e2.symm⟩

theorem param_relation : ∀ (N j : ℕ) (a b ca cb : Fin N), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (h B : Matrix (Fin N) (Fin N) ℂ) (t t' μ : ℂ), h.det ≠ 0 → IsBlockDiag j B → B.BlockTriangular id → (∀ I, minorIJ (h * B * (1 + Matrix.single cb ca t')) I (stepCols N j a) = μ * minorIJ (h * (1 + Matrix.single cb ca t)) I (stepCols N j a)) → μ = (∏ c ∈ (stepCols N j a).erase ca, B c c) * (B ca ca + t' * B ca cb) ∧ μ * t = (∏ c ∈ (stepCols N j a).erase ca, B c c) * (t' * B cb cb) := by
  intro N j a b ca cb hj hb hab hca hcb h B t t' μ hdet _ hBt hyp
  have hinv : h⁻¹ * h = 1 := Matrix.nonsing_inv_mul h (isUnit_iff_ne_zero.2 hdet)
  have hcaS : ca ∈ stepCols N j a := by
    unfold lastCol at hca
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs at hca ⊢ <;> omega
  have hmax : ∀ c ∈ stepCols N j a, c ≤ ca := by
    intro c hc
    unfold lastCol at hca
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rw [Fin.le_def]
    split_ifs at hca hc <;> omega
  have hlt : ca < cb := by
    rw [Fin.lt_def]
    omega
  refine param_core _ ca cb hcaS hmax hlt B hBt t t' μ fun J => ?_
  calc minorIJ (B * (1 + Matrix.single cb ca t')) J (stepCols N j a)
      = minorIJ (h⁻¹ * (h * B * (1 + Matrix.single cb ca t'))) J (stepCols N j a) := by
        rw [Matrix.mul_assoc h, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
    _ = ∑ I, minorIJ h⁻¹ J I * minorIJ (h * B * (1 + Matrix.single cb ca t')) I (stepCols N j a) :=
        minorIJ_mul_sum _ _ _ _
    _ = μ * ∑ I, minorIJ h⁻¹ J I * minorIJ (h * (1 + Matrix.single cb ca t)) I (stepCols N j a) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [hyp I]
        ring
    _ = μ * minorIJ (h⁻¹ * (h * (1 + Matrix.single cb ca t))) J (stepCols N j a) := by
        rw [minorIJ_mul_sum]
    _ = μ * minorIJ (1 + Matrix.single cb ca t) J (stepCols N j a) := by
        rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Plane
end
end
