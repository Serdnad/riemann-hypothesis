module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle103
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle113
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle075
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle109
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle012
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartIntegralPotentialLocallyFinite
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle021

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Orb

section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem blockMap_fst (k₀ : K) : IsBlockMap (ι := ι) (ι' := fun o : Option K => ι (o.getD k₀)) some (v₀ k₀) := by
  refine ⟨Option.some_injective _, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, i⟩ ⟨k', i'⟩ h
    simp only [v₀, Sigma.mk.injEq, Option.some.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [Option.getD_some, heq_eq_eq] at h
    subst h
    rfl
  · rintro ⟨o, i⟩ ⟨k, hk⟩
    obtain rfl : o = some k := hk.symm
    exact ⟨⟨k, i⟩, rfl⟩

theorem baseOf_mem (M : FlagModel y Ψ N j) {τ : Ψ} {a : Fin N} {k₀ : K} {ca cb : Fin N}
    {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (hz : z ∈ mcPts (wP M τ a k₀ ca cb)) :
    baseOf M k₀ z ∈ mcPts (mCoordIdeal M.x) :=
  CPts.base_mem M (CPts.comp_mem_mcPts (blockMap_fst k₀) (algebraMap Φ (RatFunc Φ)) (funext fun _ => rfl) hz)

theorem twMinor_scale (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {zb zb' : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hv : ∀ s, valAt M.x s zb' = valAt M.x s zb) (i : Fin N) (k : K) (g : Matrix (Fin N) (Fin N) ℂ)
    {u u' : (Σ k, ι k) → ℂ} {t : ℂ} (hu : ∀ m : ι k, u' ⟨k, m⟩ = t * u ⟨k, m⟩) (J : Finset (Fin N)) :
    twMinor M F zb' i k g u' J = t * twMinor M F zb i k g u J := by
  have hp : ∀ I, pluck M F zb' k u' I = t * pluck M F zb k u I := fun I => by
    unfold pluck
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hv, hu]
    ring
  unfold twMinor
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [hp]
  ring

theorem lr_key (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {zb zb' : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hv : ∀ s, valAt M.x s zb' = valAt M.x s zb) (g : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) (k : K)
    {u u' : (Σ k, ι k) → ℂ} {t : ℂ} (ht : t ≠ 0) (hu : ∀ m : ι k, u' ⟨k, m⟩ = t * u ⟨k, m⟩) (J J' : Finset (Fin N)) :
    twMinor M F zb' i k g u' J / twMinor M F zb' i k g u' J' = twMinor M F zb i k g u J / twMinor M F zb i k g u J' := by
  rw [twMinor_scale M F hv i k g hu J, twMinor_scale M F hv i k g hu J']
  exact mul_div_mul_left _ _ ht

theorem lowRead_scale (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {zb zb' : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hv : ∀ s, valAt M.x s zb' = valAt M.x s zb) (h : Ψ → Matrix (Fin N) (Fin N) ℂ)
    {u u' : (Σ k, ι k) → ℂ} {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (hu : ∀ k (m : ι k), u' ⟨k, m⟩ = c k * u ⟨k, m⟩)
    (τ' : Ψ) (a' b' : Fin N) : lowRead M F zb' h u' τ' a' b' = lowRead M F zb h u τ' a' b' := by
  unfold lowRead
  exact congrArg (Option.elim (M.blk (τ', stepOf N j b')) 0) (funext fun k => lr_key M F hv _ _ k (hc k) (hu k) _ _)

end

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ z ∈ wO M Rb τ a k₀ ca cb F kb V r h, ∀ z' ∈ mcPts (wP M τ a k₀ ca cb), SameOrbit z' z → z' ∈ wO M Rb τ a k₀ ca cb F kb V r h ∧ wRho M Rb τ k₀ ca cb F kb r h ε z' = wRho M Rb τ k₀ ca cb F kb r h ε z := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε ctx z hz z' hz' ho
  obtain ⟨-, -, -, -, -, -, -, -, hr, -, -⟩ := ctx
  obtain ⟨hzP, hs, hV, hm₁, hm₂⟩ := hz
  obtain ⟨c, hc, rfl⟩ := ho
  set z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ := fun p => c p.1 * z p with hz'def
  have hb := baseOf_mem M hzP
  have hb' := baseOf_mem M hz'
  have eb : baseOf M k₀ z' = fun q => c (some q.1.1) * baseOf M k₀ z q := rfl
  have hob : SameOrbit (baseOf M k₀ z') (baseOf M k₀ z) := ⟨fun k => c (some k.1), fun k => hc _, eb⟩
  have hnot : ∀ x : Rb.X, Rb.lift x x ∉ mcPts (⊤ : Ideal (MRing (baseIdx ι M.blk))) := fun x hx => by
    have := hx.2 1 Submodule.mem_top
    simp at this
  have hrr : r (baseOf M k₀ z') = r (baseOf M k₀ z) :=
    Rb.inj _ _ (hnot _) (orbit_trans (hr _ hb') (orbit_trans hob (orbit_symm (hr _ hb))))
  have hv : ∀ s, valAt M.x s (baseOf M k₀ z') = valAt M.x s (baseOf M k₀ z) := fun s => by
    have := StepW.TorusAct.valAt_torus (x := M.x) (fun k => c (some k.1)) (fun k => hc _) hb (eb ▸ hb') s
    rw [eb]
    exact this
  have h₁ : ∀ k (m : ι k), fstPt k₀ z' ⟨k, m⟩ = c (some k) * fstPt k₀ z ⟨k, m⟩ := fun _ _ => rfl
  let c₂ : K → ℂ := fun k => if k = k₀ then c none else c (some k)
  have hc₂ : ∀ k, c₂ k ≠ 0 := fun k => by
    simp only [c₂]
    split_ifs
    exacts [hc _, hc _]
  have h₂ : ∀ k (m : ι k), sndPt k₀ z' ⟨k, m⟩ = c₂ k * sndPt k₀ z ⟨k, m⟩ := fun k m => by
    by_cases hk : k = k₀
    · subst hk
      simp only [sndPt, Function.comp, v₁_self, c₂, if_true, hz'def]
    · simp only [sndPt, Function.comp, v₁_ne (p := ⟨k, m⟩) hk, c₂, if_neg hk, hz'def]
  refine ⟨?_, ?_⟩
  · show z' ∈ mcPts _ ∧ _
    refine ⟨hz', ?_, ?_, fun p k hp => ?_, ?_⟩
    · rw [hrr]; exact hs
    · rw [hrr]; exact hV
    · rw [twMinor_scale M F hv _ k _ (h₁ k)]
      exact mul_ne_zero (hc _) (hm₁ p k hp)
    · rw [twMinor_scale M F hv _ k₀ _ (h₂ k₀)]
      exact mul_ne_zero (hc₂ _) hm₂
  · funext i
    unfold wRho
    rcases ε.symm i with l | q | u
    · show Rb.A.chart kb (r (baseOf M k₀ z')) l = Rb.A.chart kb (r (baseOf M k₀ z)) l
      rw [hrr]
    · exact lowRead_scale M F hv h (fun k => hc (some k)) h₁ _ _ _
    · show lowRead M F _ h (sndPt k₀ z') τ cb ca - lowRead M F _ h (fstPt k₀ z') τ cb ca = _ - _
      rw [lowRead_scale M F hv h hc₂ h₂, lowRead_scale M F hv h (fun k => hc (some k)) h₁]

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Orb
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.MatRead

theorem det_of_key {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (f : Fin m → ℕ) (hf : Function.Injective f)
    (h : ∀ i j, f i < f j → A i j = 0) : A.det = ∏ i, A i i := by
  rw [Matrix.det_apply, Finset.sum_eq_single 1]
  · simp
  · intro σ _ hσ
    obtain ⟨i, hi⟩ : ∃ i, f (σ i) < f i := by
      by_contra hne
      simp only [not_exists, not_lt] at hne
      apply hσ
      have hsum : ∑ i, f (σ i) = ∑ i, f i := Equiv.sum_comp σ f
      have heq := (Finset.sum_eq_sum_iff_of_le (fun i _ => hne i)).mp hsum.symm
      refine Equiv.ext (fun i => ?_)
      exact (hf (heq i (Finset.mem_univ i)).symm : σ i = i)
    have hz : ∏ j, A (σ j) j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (h _ _ hi)
    rw [hz, smul_zero]
  · intro h1
    exact absurd (Finset.mem_univ 1) h1

private theorem minor_col_lemma {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (hX : IsLowerUni X)
    (S I : Finset (Fin N)) (a b : Fin N) (hb : b ∈ S) (hIS : I.erase a = S.erase b)
    (hcol : ∀ d ∈ I, d ≠ a → X d b = 0) (k : ℕ) (hI : I.card = k) (hS : S.card = k)
    (p q : Fin k) (hp : I.orderEmbOfFin hI p = a) (hq : S.orderEmbOfFin hS q = b) :
    (X.submatrix (I.orderEmbOfFin hI) (S.orderEmbOfFin hS)).det = (-1) ^ ((p : ℕ) + (q : ℕ)) * X a b := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := Finset.card_pos.mpr ⟨b, hb⟩; omega⟩
  have hcol' : ∀ i, i ≠ p → X (I.orderEmbOfFin hI i) b = 0 := by
    intro i hi
    refine hcol _ (Finset.orderEmbOfFin_mem I hI i) (fun h1 => hi ?_)
    apply (I.orderEmbOfFin hI).injective
    rw [h1, hp]
  have hT : (S.erase b).card = n := by
    rw [Finset.card_erase_of_mem hb, hS, Nat.add_sub_cancel]
  have hg' : ⇑(S.orderEmbOfFin hS) ∘ q.succAbove = (S.erase b).orderEmbOfFin hT := by
    apply Finset.orderEmbOfFin_unique hT
    · intro x
      rw [Function.comp_apply, Finset.mem_erase]
      exact ⟨fun h1 => Fin.succAbove_ne q x ((S.orderEmbOfFin hS).injective (h1.trans hq.symm)),
        Finset.orderEmbOfFin_mem S hS _⟩
    · exact (S.orderEmbOfFin hS).strictMono.comp (Fin.strictMono_succAbove q)
  have hg : ⇑(I.orderEmbOfFin hI) ∘ p.succAbove = (S.erase b).orderEmbOfFin hT := by
    apply Finset.orderEmbOfFin_unique hT
    · intro x
      rw [Function.comp_apply, ← hIS, Finset.mem_erase]
      exact ⟨fun h1 => Fin.succAbove_ne p x ((I.orderEmbOfFin hI).injective (h1.trans hp.symm)),
        Finset.orderEmbOfFin_mem I hI _⟩
    · exact (I.orderEmbOfFin hI).strictMono.comp (Fin.strictMono_succAbove p)
  have hdetT : (X.submatrix ((S.erase b).orderEmbOfFin hT) ((S.erase b).orderEmbOfFin hT)).det = 1 := by
    rw [det_of_key _ (fun i => (((S.erase b).orderEmbOfFin hT i : Fin N) : ℕ)) ?_ ?_]
    · exact Finset.prod_eq_one (fun i _ => hX.1 _)
    · intro i j hij
      exact ((S.erase b).orderEmbOfFin hT).injective (Fin.ext hij)
    · intro i j hij
      exact hX.2 _ _ hij
  rw [Matrix.det_succ_column _ q, Finset.sum_eq_single p]
  · have e1 : (X.submatrix (I.orderEmbOfFin hI) (S.orderEmbOfFin hS)) p q = X a b := by
      rw [Matrix.submatrix_apply, hp, hq]
    rw [e1, Matrix.submatrix_submatrix, hg, hg', hdetT, mul_one]
  · intro i _ hi
    rw [Matrix.submatrix_apply, hq, hcol' i hi, mul_zero, zero_mul]
  · intro h1
    exact absurd (Finset.mem_univ p) h1

theorem exists_sign {N : ℕ} (S : Finset (Fin N)) (a b : Fin N) (ha : a ∉ S) (hb : b ∈ S) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ X : Matrix (Fin N) (Fin N) ℂ, IsLowerUni X → (∀ d ∈ S, d ≠ b → X d b = 0) →
      minorIJ X (insert a (S.erase b)) S = c * X a b := by
  have haS : a ∉ S.erase b := fun h1 => ha (Finset.mem_of_mem_erase h1)
  have hcard : (insert a (S.erase b)).card = S.card := by
    rw [Finset.card_insert_of_notMem haS, Finset.card_erase_of_mem hb]
    have := Finset.card_pos.mpr ⟨b, hb⟩
    omega
  obtain ⟨p, hp⟩ : ∃ p, (insert a (S.erase b)).orderEmbOfFin hcard p = a := by
    have h1 : a ∈ Set.range ((insert a (S.erase b)).orderEmbOfFin hcard) := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_insert_self _ _
    exact h1
  obtain ⟨q, hq⟩ : ∃ q, S.orderEmbOfFin rfl q = b := by
    have h1 : b ∈ Set.range (S.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hb
    exact h1
  refine ⟨(-1) ^ ((p : ℕ) + (q : ℕ)), pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero), fun X hX hcol => ?_⟩
  rw [minorIJ, dite_eq_left hcard]
  refine minor_col_lemma X hX S _ a b hb (Finset.erase_insert haS) ?_ _ hcard rfl p q hp hq
  intro d hd hda
  rcases Finset.mem_insert.mp hd with h1 | h1
  · exact absurd h1 hda
  · exact hcol d (Finset.mem_of_mem_erase h1) (Finset.ne_of_mem_erase h1)

theorem minor_replace : ∀ (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N)) (a b : Fin N), IsLowerUni X → a ∉ S → b ∈ S → b < a → (∀ c ∈ S, c ≠ b → X c b = 0) → minorIJ X (insert a (S.erase b)) S = pSgn S a b * X a b ∧ pSgn S a b ≠ 0 := by
  intro N X S a b hX ha hb hba hcol
  obtain ⟨c, hc0, hc⟩ := exists_sign S a b ha hb
  have hab : a ≠ b := (ne_of_lt hba).symm
  have hY : IsLowerUni (1 + Matrix.single a b (1 : ℂ)) := by
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply,
        if_neg (fun h1 => hab (h1.1.trans h1.2.symm)), add_zero]
    · rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_lt hij), Matrix.single_apply,
        if_neg (fun h1 => lt_asymm hba (by rw [h1.1, h1.2]; exact hij)), add_zero]
  have hYcol : ∀ d ∈ S, d ≠ b → (1 + Matrix.single a b (1 : ℂ)) d b = 0 := by
    intro d hd hdb
    have hda : d ≠ a := fun h1 => ha (h1 ▸ hd)
    rw [Matrix.add_apply, Matrix.one_apply_ne hdb, Matrix.single_apply,
      if_neg (fun h1 => hda h1.1.symm), add_zero]
  have hp : pSgn S a b = c := by
    rw [pSgn, hc _ hY hYcol, Matrix.add_apply, Matrix.one_apply_ne hab, Matrix.single_apply,
      if_pos ⟨rfl, rfl⟩, zero_add, mul_one]
  rw [hp]
  exact ⟨hc X hX hcol, hc0⟩

end GlobalTheory.CompanionTheory.Ar.PB.PFl.MatRead
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.AllKept

variable {Ψ : Type} {N j : ℕ}

theorem stepOf_val' (N j : ℕ) (c : Fin N) :
    (stepOf N j c : ℕ) = if N - j ≤ (c : ℕ) then (c : ℕ) - (N - j) else (c : ℕ) + j := rfl

theorem stepOf_mem' (hj : j ≤ N) (c : Fin N) : c ∈ stepCols N j (stepOf N j c) := by
  have := c.2
  have hv := stepOf_val' N j c
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs at hv ⊢ <;> omega

theorem stepOf_top' (hj : j ≤ N) (c d : Fin N) (hd : d ∈ stepCols N j (stepOf N j c)) : d ≤ c := by
  have := c.2
  have := d.2
  have hv := stepOf_val' N j c
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hd
  rw [Fin.le_def]
  split_ifs at hv hd <;> omega

theorem stepOf_proper' (hj : j ≤ N) {a b : Fin N} (hlt : b < a) (hblk : ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)) :
    IsProperStep N j (stepOf N j b) := by
  have := a.2
  have := b.2
  have h : (b : ℕ) < a := hlt
  have hv := stepOf_val' N j b
  simp only [IsProperStep]
  split_ifs at hv <;> omega

theorem sep_of_all (hj : j ≤ N) {keep : Ψ × Fin N → Prop} (hk : ∀ p, keep p) (q : LowIdx Ψ N j) : Sep keep q :=
  ⟨stepOf N j q.1.2.2, hk _, stepOf_proper' hj q.2.1 q.2.2, stepOf_mem' hj _,
    fun h => absurd (stepOf_top' hj _ _ h) (not_le.2 q.2.1)⟩

theorem card_pIdx_of_all : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (keep : Ψ × Fin N → Prop), j ≤ N →
    (∀ p, keep p) → Nat.card (PIdx j keep) = Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) := by
  intro Ψ _ _ N j keep hj hk
  have e : PIdx j keep ≃ LowIdx Ψ N j := Equiv.subtypeUnivEquiv (sep_of_all hj hk)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, GlobalTheory.CompanionTheory.Ar.PB.WMan.ChartCount.card_lowIdx Ψ N j hj]

end GlobalTheory.CompanionTheory.Ar.PB.PFl.AllKept
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.PtsBase

section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]

theorem exists_section (M : FlagModel y Ψ N j) {κ : Kk → K} {v : (Σ k, ιk k) → (Σ k, ι k)} (hb : IsBlockMap κ v)
    (hr : ∀ k : NonPluckerBlocks M.blk, k.1 ∈ Set.range κ) :
    ∃ (κ' : NonPluckerBlocks M.blk → Kk) (v' : (Σ k, baseIdx ι M.blk k) → (Σ k, ιk k)), IsBlockMap κ' v' ∧
      (∀ q, v (v' q) = ⟨q.1.1, q.2⟩) ∧ ∀ z, pBase M v z = z ∘ v' := by
  choose κ' hκ' using hr
  have hex : ∀ q : Σ k, baseIdx ι M.blk k, ∃ q', v q' = ⟨q.1.1, q.2⟩ := fun q =>
    hb.2.2.2 ⟨q.1.1, q.2⟩ ⟨κ' q.1, hκ' q.1⟩
  choose v' hv' using hex
  have hfst : ∀ p, (v' p).1 = κ' p.1 := fun p => hb.1 (by
    rw [← hb.2.2.1, hv', hκ'])
  refine ⟨κ', v', ⟨fun a b e => Subtype.ext (by rw [← hκ' a, ← hκ' b, e]), fun a b e => ?_, hfst, ?_⟩, hv', fun z => ?_⟩
  · have e' := congrArg v e
    rw [hv', hv'] at e'
    exact (GlobalTheory.CompanionTheory.Ar.PB.CPts.blockMap_base M).2.1 e'
  · rintro q ⟨kb, hq⟩
    have h1 : (v q).1 ∈ Set.range (Subtype.val : NonPluckerBlocks M.blk → K) :=
      ⟨kb, by rw [hb.2.2.1, ← hq, hκ']⟩
    obtain ⟨p, hp⟩ := (GlobalTheory.CompanionTheory.Ar.PB.CPts.blockMap_base M).2.2.2 (v q) h1
    exact ⟨p, hb.2.1 ((hv' p).trans hp)⟩
  · funext q
    show upV v z ⟨q.1.1, q.2⟩ = z (v' q)
    rw [← hv', upV_apply hb.2.1]

end

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v → (∀ k, k ∈ Set.range κ ↔ ((∀ p, M.blk p ≠ some k) ∨ ∃ p, keep p ∧ M.blk p = some k)) → (∀ z ∈ mcPts (mCoordIdeal (y ∘ v)), pBase M v z ∈ mcPts (mCoordIdeal M.x)) ∧ ∀ z z' : (Σ k, ιk k) → ℂ, SameOrbit z z' → SameOrbit (pBase M v z) (pBase M v z') := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M keep Kk _ ιk _ κ v hb hk
  obtain ⟨κ', v', hb', hv', hz⟩ := exists_section M hb fun k => (hk k.1).2 (Or.inl k.2)
  refine ⟨fun z hzm => ?_, fun z z' ho => ?_⟩
  · rw [hz]
    refine GlobalTheory.CompanionTheory.Ar.PB.CPts.comp_mem_mcPts hb' (algebraMap M.Ω Φ) (funext fun q => ?_) hzm
    show y (v (v' q)) = algebraMap M.Ω Φ (M.x q)
    rw [hv']
    exact M.y_base q
  · obtain ⟨c, hc, e⟩ := ho
    refine ⟨fun k => c (κ' k), fun k => hc _, ?_⟩
    rw [hz, hz, e]
    funext q
    show c (v' q).1 * z' (v' q) = c (κ' q.1) * z' (v' q)
    rw [hb'.2.2.1]

end GlobalTheory.CompanionTheory.Ar.PB.PFl.PtsBase
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.DetG

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem det_genU (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S) : (genU Ω r s).det = 1 := by
  rw [det_of_lowerTriangular (genU Ω r s) fun a b h => ?_]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp [genU]
  · have h' : a < b := h
    simp [genU, not_lt.2 h'.le, h'.ne]

variable (Ψ : Type) (p q : ℕ) (Ω : Type) [Field Ω] (τ : Ψ)

theorem wBlock_gMat : wBlock (gMat p q Ω τ) = genU Ω (rk Ψ p q) (.inl τ) := by
  ext a b
  have ea : (blockEquiv p q).symm (wEmb p q a) = .inr a := by
    rw [← blockEquiv_inr, Equiv.symm_apply_apply]
  have eb : (blockEquiv p q).symm (wEmb p q b) = .inr b := by
    rw [← blockEquiv_inr, Equiv.symm_apply_apply]
  change Matrix.fromBlocks (genU Ω (rk Ψ p q) (.inr τ)) 0 0 (genU Ω (rk Ψ p q) (.inl τ))
    ((blockEquiv p q).symm (wEmb p q a)) ((blockEquiv p q).symm (wEmb p q b)) = _
  rw [ea, eb]
  rfl

theorem omBlock_gMat : omBlock (gMat p q Ω τ) = genU Ω (rk Ψ p q) (.inr τ) := by
  ext a b
  have ea : (blockEquiv p q).symm (omEmb p q a) = .inl a := by
    rw [← blockEquiv_inl, Equiv.symm_apply_apply]
  have eb : (blockEquiv p q).symm (omEmb p q b) = .inl b := by
    rw [← blockEquiv_inl, Equiv.symm_apply_apply]
  change Matrix.fromBlocks (genU Ω (rk Ψ p q) (.inr τ)) 0 0 (genU Ω (rk Ψ p q) (.inl τ))
    ((blockEquiv p q).symm (omEmb p q a)) ((blockEquiv p q).symm (omEmb p q b)) = _
  rw [ea, eb]
  rfl

theorem detFac_gMat (Ψ : Type) (p q : ℕ) (Ω : Type) [Field Ω] (τ : Ψ) (i : Fin (p + q)) :
    detFac p i (gMat p q Ω τ) = 1 := by
  have hw : minorIJ (gMat p q Ω τ) (wIdx (p + q) p) (wIdx (p + q) p) = 1 := by
    rw [minorIJ_wIdx, wBlock_gMat]
    exact det_genU Ω (rk Ψ p q) (.inl τ)
  have ho : minorIJ (gMat p q Ω τ) (omIdx (p + q) p) (omIdx (p + q) p) = 1 := by
    rw [minorIJ_omIdx, omBlock_gMat]
    exact det_genU Ω (rk Ψ p q) (.inr τ)
  simp only [detFac, hw, ho, ite_self, mul_one]

end GlobalTheory.CompanionTheory.Ar.PB.FMX.DetG
end
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX

theorem flag_total_normal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∀ (Z : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω (rk (CMType H) D.p D.q))) ⟶ Z) (f : Z ⟶ 𝔐.X), @CoordTie Z _ _ ℤ _ (Ring.toIntAlgebra _) ξ' _ (seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → (∀ q : Z, genPt ξ' ⤳ q) → GlobalTheory.CompanionTheory.Ar.Dominates ξ' 𝔐.ξ f (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) → Smooth f → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ _ Z ξ' f _ _ _ hf
  exact GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth f 𝔐.normal

end GlobalTheory.CompanionTheory.Ar.PB.FMX
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem GlobalTheory.CompanionTheory.Ar.FlagPull.field_of_hodgeOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω'] (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) (x : (Σ k, J k) → Ω) (x' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S x) (A' : HodgeCpt Y S x') (h : A'.X ⟶ A.X) (i : Ω →+* Ω') (j : A.Li →+ A'.Li) (d : ℕ), HodgeOver A' A h i j → A.IsCover d → ∃ ι : A'.Ω₀ →+* Ω, i.comp ι = A'.fn ∧ GlobalTheory.CompanionTheory.Ar.Dominates A.ξ A'.ξ₀ A.f ι ∧ letI := ι.toAlgebra; Module.finrank A'.Ω₀ Ω = d :=
  @PositivityTheory.Xgp.t_c_fm_exists_flags_field
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.chart_integral_potential_locally_finite : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (Y Z : Set M.Xc) (N : Set ((Σ k, ι k) → ℂ)) (c : Fin n → ℝ) (B : Fin n → HermLine ι) (Φ : Fin n → LocPot M.Xc) (g : ((Σ k, ι k) → ℂ) → ℝ) (G₀ : M.Xc → ℝ), IsArithVar P (n + 1) → IsGoodProj P Q → IsOpen Y → (∀ j, volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (Yᶜ ∪ Z)) = 0) → IsPtsNull P n N → (∀ i x, M.atlas.SmoothOn ((Φ i).U x ∩ Y) ((Φ i).φ x)) → (∀ i, ∀ x, ∀ y₀ ∈ (Φ i).U x ∩ Y, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Φ i).U x ∩ Y ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (P) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Φ i).φ x y' - (fun z => c i * Real.log ((B i).h z)) (s y') = (G y').re) → (∀ z ∈ mcPts P, z ∉ N → M.proj z ∈ Y → M.proj z ∉ Z → g z = G₀ (M.proj z)) → ∀ᵐ y, ∃ W : M.Xc → (((k : K) → ι k) → ℂ), Set.InjOn W (modelQ M Q ⁻¹' {y} \ modelBad M Q (Yᶜ ∪ Z)) ∧ fibre P Q y = W '' (modelQ M Q ⁻¹' {y} \ modelBad M Q (Yᶜ ∪ Z)) ∧ ∀ x ∈ modelQ M Q ⁻¹' {y} \ modelBad M Q (Yᶜ ∪ Z), sheetDensity P Q (fun i z => c i * Real.log ((B i).h z)) g y (W x) = G₀ x * pushDens M.atlas Φ (modelQ M Q) x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Push.fibre_term_ae | exact GlobalTheory.CompanionTheory.Ar.Giv.Push.fibre_term_ae | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Push.fibre_term_ae <;> assumption)
end
