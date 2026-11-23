module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle085
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle025
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AffineChartIdealPrimeAndSaturated
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle043
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle062
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle088
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle082
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle084
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle089
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

theorem _root_.GlobalTheory.T.snc_chart_regular_at_cone_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ) (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) (r : Fin e → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) (Jf : Finset (Fin e)), IsMultiHomogIdeal P → IsMultiHomogIdeal D → z ∈ conePts P → (∀ k, z ⟨k, p k⟩ ≠ 0) → (∀ h ∈ (SncRes.ideal P p), eval (renPt (affCoord p z)) h = 0) → IsRegularLocalRing (locRing (SncRes.ideal P p) (renPt (affCoord p z))) → ringKrullDim (locRing (SncRes.ideal P p) (renPt (affCoord p z))) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z))) (r l)) = Ideal.map (algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z)))) (ptIdeal (renPt (affCoord p z))) → (∀ 𝔮 : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ), 𝔮.IsPrime → (SncRes.ideal P p) ≤ 𝔮 → 𝔮 ≤ ptIdeal (renPt (affCoord p z)) → ((SncRes.ideal (P ⊔ D) p) ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → ∃ σ : Fin e → Option (Fin (SncRes.rc P D)), Set.InjOn σ Jf ∧ (∀ l, σ l = none ↔ l ∉ Jf) ∧ (∀ l k, σ l = some k → SncRes.ideal (SncRes.compIdeal P D k) p = SncRes.Par.chPrime (SncRes.ideal P p) (renPt (affCoord p z)) (r l) ∧ ∀ k', (X ⟨k', p k'⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ SncRes.compIdeal P D k) ∧ ∀ k, (∀ g ∈ SncRes.compIdeal P D k, eval z g = 0) → ∃ l ∈ Jf, σ l = some k := by
  intro K _ ι _ P D e p z r Jf hP hD hz hzp hI reg dim span hprim
  have ideal_mono {S S' : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (h : S ≤ S') (p : (k : K) → ι k) :
      SncRes.ideal S p ≤ SncRes.ideal S' p :=
    Ideal.map_mono (sup_le_sup_right h _)

  have renR_mem {S : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (p : (k : K) → ι k)
      {g : MvPolynomial (Σ k, ι k) ℂ} (hg : g ∈ S) : renR (Σ k, ι k) g ∈ SncRes.ideal S p :=
    Ideal.mem_map_of_mem _ (Ideal.mem_sup_left hg)

  have renR_X_sub_one_mem (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) (k : K) :
      renR (Σ k, ι k) (X ⟨k, p k⟩ - 1) ∈ SncRes.ideal S p :=
    Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))

  have renR_sub_deh_mem (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k)
      (f : MvPolynomial (Σ k, ι k) ℂ) :
      renR (Σ k, ι k) f - bind₁ (SncRes.lift p) f ∈ SncRes.ideal S p := by
    classical
    have key : (Ideal.Quotient.mk (SncRes.ideal S p)).comp
          (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _) =
        (Ideal.Quotient.mk (SncRes.ideal S p)).comp
          (bind₁ (SncRes.lift p) : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] _).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp [renameEquiv_apply]
      · rintro ⟨k, i⟩
        by_cases h : i = p k
        · subst h
          have h1 : SncRes.lift p ⟨k, p k⟩ = 1 := by simp [SncRes.lift]
          have h2 := renR_X_sub_one_mem S p k
          rw [map_sub, map_one] at h2
          simpa [bind₁_X_right, h1] using Ideal.Quotient.eq.2 h2
        · have h1 : SncRes.lift p ⟨k, i⟩ = X (Fintype.equivFin (Σ k, ι k) ⟨k, i⟩) := by
            simp [SncRes.lift, h, bind₁_X_right]
          simp [bind₁_X_right, h1, renameEquiv_apply]
    exact Ideal.Quotient.eq.1 (RingHom.congr_fun key f)

  have deh_mem {S : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (p : (k : K) → ι k)
      {g : MvPolynomial (Σ k, ι k) ℂ} (hg : g ∈ S) : bind₁ (SncRes.lift p) g ∈ SncRes.ideal S p := by
    have h := (SncRes.ideal S p).sub_mem (renR_mem p hg) (renR_sub_deh_mem S p g)
    simpa using h

  have exists_compIdeal_eq {P D Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
      (hQ : Q ∈ (P ⊔ D).minimalPrimes) : ∃ k, SncRes.compIdeal P D k = Q := by
    refine ⟨(SncRes.finite_minimalPrimes (P ⊔ D)).toFinset.equivFin
      ⟨Q, (Set.Finite.mem_toFinset _).2 hQ⟩, ?_⟩
    simp [SncRes.compIdeal]

  have compIdeal_injective (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) :
      Function.Injective (SncRes.compIdeal P D) := by
    intro a b h
    exact ((SncRes.finite_minimalPrimes (P ⊔ D)).toFinset.equivFin).symm.injective (Subtype.ext h)

  have exists_minimal_below {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (p : (k : K) → ι k)
      {𝔮 : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)} (h𝔮 : 𝔮.IsPrime)
      (hD : SncRes.ideal (P ⊔ D) p ≤ 𝔮) :
      ∃ Q ∈ (P ⊔ D).minimalPrimes,
        (∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) ∧ SncRes.ideal Q p ≤ 𝔮 := by
    classical
    have hle : P ⊔ D ≤ 𝔮.comap (bind₁ (SncRes.lift p) : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] _) :=
      fun g hg => hD (deh_mem p hg)
    have : (𝔮.comap (bind₁ (SncRes.lift p) : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] _)).IsPrime :=
      Ideal.comap_isPrime _ _
    obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le hle
    refine ⟨Q, hQ, fun k hX => ?_, ?_⟩
    · have h1 : bind₁ (SncRes.lift p) (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∈ 𝔮 := hQle hX
      have h2 : SncRes.lift p ⟨k, p k⟩ = 1 := by simp [SncRes.lift]
      rw [bind₁_X_right, h2] at h1
      exact h𝔮.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    · refine Ideal.map_le_iff_le_comap.2 (sup_le ?_ ?_)
      · intro f hf
        have h1 : bind₁ (SncRes.lift p) f ∈ 𝔮 := hQle hf
        have h2 := 𝔮.add_mem (hD (renR_sub_deh_mem (P ⊔ D) p f)) h1
        simpa using h2
      · rw [Ideal.span_le]
        rintro _ ⟨k, rfl⟩
        exact hD (renR_X_sub_one_mem (P ⊔ D) p k)
  have hIDc : SncRes.ideal P p ≤ SncRes.ideal (P ⊔ D) p := ideal_mono le_sup_left p
  have pr := GlobalTheory.T.regular_system_of_parameters_local_ring_alt _ e (SncRes.ideal P p) (SncRes.ideal (P ⊔ D) p) (renPt (affCoord p z)) r Jf
    hIDc hI reg dim span hprim
  have hmin := GlobalTheory.T.minimal_primes_of_multihomog_sup K ι P D hP hD
  have chart_prime_and_mem_iff (Q : Ideal (MvPolynomial (Σ k, ι k) ℂ))
      (hQ : IsMultiHomogIdeal Q) (hprime : Q.IsPrime)
      (hX : ∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) :
      (SncRes.ideal Q p).IsPrime ∧
        ∀ (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ), IsMultiHomog f a →
          (bind₁ (SncRes.lift p) f ∈ SncRes.ideal Q p ↔ f ∈ Q) := by
    have hker := SncRes.Dict.ker_theta Q hQ p hX
    refine ⟨?_, fun f a hf => ?_⟩
    · have : (chartIdeal Q p).IsPrime := hker ▸ RingHom.ker_isPrime (SncRes.Dict.theta Q p)
      exact Ideal.map_isPrime_of_equiv (renR (Σ k, ι k))
    · have hquot := Ideal.Quotient.eq.2 (renR_sub_deh_mem Q p f)
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hquot, Ideal.Quotient.eq_zero_iff_mem,
        SncRes.ideal, mem_map_renR_iff, RingEquiv.symm_apply_apply, ← hker, RingHom.mem_ker]
      exact SncRes.Dict.theta_eq_zero_iff Q p hX hf
  have step : ∀ l (_ : l ∈ Jf), ∃ k, SncRes.ideal (SncRes.compIdeal P D k) p =
        SncRes.Par.chPrime (SncRes.ideal P p) (renPt (affCoord p z)) (r l) ∧
      ∀ k', (X ⟨k', p k'⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ SncRes.compIdeal P D k := by
    intro l hl
    obtain ⟨hpr, hIq, hqt, hDq, hrl, hsep, hmn⟩ := pr l hl
    obtain ⟨Q, hQ, hX, hQle⟩ := exists_minimal_below p hpr hDq
    have hQh := hmin Q hQ
    have hQp : Q.IsPrime := hQ.1.1
    obtain ⟨hQpr, -⟩ := chart_prime_and_mem_iff Q hQh hQp hX
    have hDQ : SncRes.ideal (P ⊔ D) p ≤ SncRes.ideal Q p := ideal_mono hQ.1.2 p
    have hIQ := hIDc.trans hDQ
    obtain ⟨j, hj, hrj⟩ := (hprim _ hQpr hIQ (hQle.trans hqt)).1 hDQ
    have hjl : j = l := by
      by_contra hne
      exact hsep j hj hne (hQle hrj)
    subst hjl
    obtain ⟨k, rfl⟩ := exists_compIdeal_eq hQ
    exact ⟨k, le_antisymm hQle (hmn _ hQpr hIQ (hQle.trans hqt) hrj), hX⟩
  classical
  choose κ hκ using step
  have hσ : ∀ l k, (if h : l ∈ Jf then some (κ l h) else none) = some k →
      ∃ h : l ∈ Jf, κ l h = k := by
    intro l k h
    by_cases hl : l ∈ Jf
    · rw [dite_eq_left hl] at h
      exact ⟨hl, Option.some.inj h⟩
    · rw [dite_eq_right hl] at h
      cases h
  refine ⟨fun l => if h : l ∈ Jf then some (κ l h) else none, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    have ha' : a ∈ Jf := ha
    have hb' : b ∈ Jf := hb
    simp only [dite_eq_left ha', dite_eq_left hb'] at hab
    have hk := Option.some.inj hab
    have heq : SncRes.Par.chPrime (SncRes.ideal P p) (renPt (affCoord p z)) (r a) =
        SncRes.Par.chPrime (SncRes.ideal P p) (renPt (affCoord p z)) (r b) := by
      rw [← (hκ a ha').1, ← (hκ b hb').1, hk]
    by_contra hne
    obtain ⟨-, -, -, -, -, hsep, -⟩ := pr a ha'
    obtain ⟨-, -, -, -, hrb, -, -⟩ := pr b hb'
    exact hsep b hb' (Ne.symm hne) (heq ▸ hrb)
  · intro l
    by_cases hl : l ∈ Jf <;> simp [hl]
  · intro l k h
    obtain ⟨hl, rfl⟩ := hσ l k h
    exact hκ l hl
  · intro k hk
    have hQk := SncRes.compIdeal_mem (P := P) D k
    have hkh := hmin _ hQk
    have hkp : (SncRes.compIdeal P D k).IsPrime := hQk.1.1
    have hX : ∀ k', (X ⟨k', p k'⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ SncRes.compIdeal P D k := by
      intro k' hx
      exact hzp k' (by simpa using hk _ hx)
    obtain ⟨hkpr, hdict⟩ := chart_prime_and_mem_iff _ hkh hkp hX
    have hzc : z ∈ conePts (SncRes.compIdeal P D k) := ⟨hz.1, hk⟩
    have hpt : SncRes.ideal (SncRes.compIdeal P D k) p ≤ ptIdeal (renPt (affCoord p z)) := by
      intro h hh
      exact renPt_zero _ _ ((mem_conePts_iff_chartIdeal hkh p z hzp).1 hzc) h hh
    have hDk : SncRes.ideal (P ⊔ D) p ≤ SncRes.ideal (SncRes.compIdeal P D k) p :=
      ideal_mono hQk.1.2 p
    have hIk := hIDc.trans hDk
    obtain ⟨l, hl, hrl⟩ := (hprim _ hkpr hIk hpt).1 hDk
    obtain ⟨-, -, -, -, -, -, hmn⟩ := pr l hl
    have hle := hmn _ hkpr hIk hpt hrl
    rw [← (hκ l hl).1] at hle
    have hQ0 := SncRes.compIdeal_mem (P := P) D (κ l hl)
    obtain ⟨S, hS, hSeq⟩ := hmin _ hQ0
    have hsub : SncRes.compIdeal P D (κ l hl) ≤ SncRes.compIdeal P D k := by
      rw [hSeq, Ideal.span_le]
      intro f hf
      obtain ⟨a, ha⟩ := hS f hf
      have hfQ : f ∈ SncRes.compIdeal P D (κ l hl) := hSeq ▸ Ideal.subset_span hf
      exact (hdict f a ha).1 (hle (deh_mem p hfQ))
    have heq : SncRes.compIdeal P D (κ l hl) = SncRes.compIdeal P D k :=
      le_antisymm hsub (hQk.2 ⟨hQ0.1.1, hQ0.1.2⟩ hsub)
    refine ⟨l, hl, ?_⟩
    beta_reduce
    rw [dite_eq_left hl, compIdeal_injective P D heq]
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

theorem stepCols_ne_empty {N j : ℕ} (hj : j ≤ N) {i : Fin N} : stepCols N j i ≠ ∅ := by
  intro e
  by_cases hi : (i : ℕ) + 1 ≤ j
  · have h0 : N - j < N := by omega
    have : (⟨N - j, h0⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos hi]
      omega
    rw [e] at this
    simp at this
  · have h0 : 0 < N := by have := i.2; omega
    have : (⟨0, h0⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg hi]
      omega
    rw [e] at this
    simp at this

theorem img_form : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (z : (Σ k, ι' k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), basePart M'.blk z ∈ mcPts (mCoordIdeal M'.x) → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal (basePart M'.blk z)) → M.GoodAt F (mCoordIdeal (basePart M'.blk z ∘ Cv.v)) → (∀ τ, IsBlockDiag j (h τ)) → (∀ (p : Ψ × Fin N) (k' : K'), M'.blk p = some k' → ∃ a : ℂ, a ≠ 0 ∧ ∀ m' : ι' k', z ⟨k', m'⟩ = a * CovMap.LocImg.plk M' F' (basePart M'.blk z) p.2 ⟨k', m'⟩ (h p.1)) → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ a : ℂ, a ≠ 0 ∧ ∀ m : ι k, CovMap.LocImg.img Cv F' F z ⟨k, m⟩ = a * CovMap.LocImg.plk M F (basePart M'.blk z ∘ Cv.v) p.2 ⟨k, m⟩ (Cv.trans F' F (basePart M'.blk z) p.1 * h p.1) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv z F' F h hb hF' hF hG' hG hh hyp p k hp
  obtain ⟨k', hk'⟩ := exists_blk_cover M' hp
  obtain ⟨a, ha, hz⟩ := hyp p k' hk'
  have hCB := GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le
  have hoff : ∀ J, ¬ IsStepRows N j p.2 J → minorIJ (h p.1) J (stepCols N j p.2) = 0 := fun J hJ =>
    (hCB.2.1 (h p.1) J (hh p.1) hJ).resolve_right (stepCols_ne_empty M.j_le)
  have hdelta : ∀ I' J, IsStepRows N j p.2 I' → IsStepRows N j p.2 J →
      ∑ m' : ι' k', valAt M'.x (F'.u' I' ⟨k', m'⟩) (basePart M'.blk z) *
        valAt M'.x (F'.u ⟨k', m'⟩ J) (basePart M'.blk z) = if I' = J then 1 else 0 := by
    intro I' J hI hJ
    have hu' := fun m' : ι' k' => (hG'.2.1 ⟨k', m'⟩ I').2
    have hu := fun m' : ι' k' => (hG'.2.1 ⟨k', m'⟩ J).1
    have e1 := (reg_sum hb Finset.univ (fun m' : ι' k' => F'.u' I' ⟨k', m'⟩ * F'.u ⟨k', m'⟩ J)
      fun m' _ => (reg_mul hb (hu' m') (hu m')).1).2
    rw [hF'.2.2.1 p k' hk' I' J hI hJ] at e1
    rw [Finset.sum_congr rfl fun m' _ => ((reg_mul hb (hu' m') (hu m')).2).symm, ← e1]
    split_ifs
    · exact map_one (regVal M'.x hb)
    · exact map_zero (regVal M'.x hb)
  have hread : ∀ I', IsStepRows N j p.2 I' →
      ∑ m' : ι' k', valAt M'.x (F'.u' I' ⟨k', m'⟩) (basePart M'.blk z) * z ⟨k', m'⟩ =
        a * minorIJ (h p.1) I' (stepCols N j p.2) := by
    intro I' hI
    have e1 : ∑ m' : ι' k', valAt M'.x (F'.u' I' ⟨k', m'⟩) (basePart M'.blk z) * z ⟨k', m'⟩ =
        a * ∑ J, (∑ m' : ι' k', valAt M'.x (F'.u' I' ⟨k', m'⟩) (basePart M'.blk z) *
          valAt M'.x (F'.u ⟨k', m'⟩ J) (basePart M'.blk z)) * minorIJ (h p.1) J (stepCols N j p.2) := by
      simp_rw [hz, plk, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun m' _ => ?_
      ring
    rw [e1]
    congr 1
    rw [Finset.sum_eq_single I']
    · rw [hdelta I' I' hI hI, if_pos rfl, one_mul]
    · intro J _ hne
      by_cases hJ : IsStepRows N j p.2 J
      · rw [hdelta I' J hI hJ, if_neg hne.symm, zero_mul]
      · rw [hoff J hJ, mul_zero]
    · simp
  refine ⟨a, ha, fun m => ?_⟩
  rw [img_step Cv F' F z hp hk' m]
  unfold stepCoord plk
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [hCB.1, mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I' _ => ?_
  by_cases hI : IsStepRows N j p.2 I'
  · rw [if_pos hI, hread I' hI]; ring
  · rw [if_neg hI, hoff I' hI, mul_zero, mul_zero]

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FA

private theorem grading_map_coeff_eq_monomial {K σ : Type} (s : σ → K)
    (φ : MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial K (MvPolynomial σ ℤ))
    (hφ : ∀ q, φ (MvPolynomial.X q) = MvPolynomial.C (MvPolynomial.X q) * MvPolynomial.X (s q))
    (g : MvPolynomial σ ℤ) : ∀ a : K →₀ ℕ,
    φ ((φ g).coeff a) = MvPolynomial.monomial a ((φ g).coeff a) := by
  classical
  induction g using MvPolynomial.induction_on
  · rename_i r
    intro a
    have h1 : φ (MvPolynomial.C r) = MvPolynomial.C (MvPolynomial.C r) := by
      simpa [MvPolynomial.algebraMap_apply] using φ.commutes r
    rw [h1, MvPolynomial.coeff_C]
    split_ifs with h
    · subst h
      rw [h1, MvPolynomial.C_apply]
    · simp
  · rename_i f1 f2 hf hg
    intro a
    simp only [map_add (f := _), MvPolynomial.coeff_add, hf, hg]
  · rename_i f n hf
    intro a
    rw [map_mul φ f (MvPolynomial.X n), hφ, mul_left_comm, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_mul_X']
    split_ifs with h
    · have he : Finsupp.single (s n) 1 ≤ a := by
        rw [Finsupp.single_le_iff]
        exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp h)
      have hX : (MvPolynomial.X (s n) : MvPolynomial K (MvPolynomial σ ℤ)) =
          MvPolynomial.monomial (Finsupp.single (s n) 1) 1 := rfl
      rw [map_mul, hφ, hf, mul_assoc, hX, MvPolynomial.monomial_mul, MvPolynomial.C_mul_monomial,
        one_mul, add_tsub_cancel_of_le he]
    · simp

private theorem smul_mem_lemma_2 {K : Type} {ι : K → Type} {Φ : Type} [Field Φ]
    (y : (Σ k, ι k) → Φ) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ f ∈ mCoordIdeal y, MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f) = 0)
    (c : K → ℂ) (f : MRing ι) (hf : f ∈ mCoordIdeal y) :
    MvPolynomial.eval (fun r : (Σ k, ι k) => c r.1 * z r) (MvPolynomial.map (Int.castRingHom ℂ) f) = 0 := by
  classical
  let φ : MvPolynomial ((k : K) × ι k) ℤ →ₐ[ℤ] MvPolynomial K (MvPolynomial ((k : K) × ι k) ℤ) :=
    MvPolynomial.aeval (fun q => MvPolynomial.C (MvPolynomial.X q) * MvPolynomial.X q.1)
  have hφ : ∀ q, φ (MvPolynomial.X q) = MvPolynomial.C (MvPolynomial.X q) * MvPolynomial.X q.1 :=
    fun q => MvPolynomial.aeval_X _ _
  have hA : ∀ g, mConeMap y g =
      MvPolynomial.map (MvPolynomial.aeval (R := ℤ) y).toRingHom (φ g) := by
    intro g
    have key : (mConeMap y : MvPolynomial _ ℤ →ₐ[ℤ] MvPolynomial K Φ) =
        ((MvPolynomial.map (MvPolynomial.aeval (R := ℤ) y).toRingHom).toIntAlgHom).comp φ := by
      apply MvPolynomial.algHom_ext
      intro q
      show mConeMap y (MvPolynomial.X q) =
        MvPolynomial.map (MvPolynomial.aeval (R := ℤ) y).toRingHom (φ (MvPolynomial.X q))
      rw [hφ]
      simp [mConeMap]
    rw [key]
    rfl
  have hf' : mConeMap y f = 0 := RingHom.mem_ker.mp hf
  have hcomp : ∀ a, (φ f).coeff a ∈ mCoordIdeal y := by
    intro a
    have h1 : (MvPolynomial.aeval (R := ℤ) y).toRingHom ((φ f).coeff a) = 0 := by
      have := congrArg (AddMonoidAlgebra.coeff · a) (hA f)
      rw [hf', MvPolynomial.coeff_zero, MvPolynomial.coeff_map] at this
      exact this.symm
    show (φ f).coeff a ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker, hA, grading_map_coeff_eq_monomial Sigma.fst φ hφ f a, MvPolynomial.map_monomial, h1,
      map_zero]
  have hB : MvPolynomial.eval (fun r : (Σ k, ι k) => c r.1 * z r) (MvPolynomial.map (Int.castRingHom ℂ) f) =
      MvPolynomial.eval c (MvPolynomial.map (MvPolynomial.aeval (R := ℤ) z).toRingHom (φ f)) := by
    rw [MvPolynomial.eval_map, ← algebraMap_int_eq, ← MvPolynomial.aeval_def]
    have key : (MvPolynomial.aeval (R := ℤ) (fun r : (Σ k, ι k) => c r.1 * z r)) =
        ((MvPolynomial.eval c).toIntAlgHom).comp
          (((MvPolynomial.map (MvPolynomial.aeval (R := ℤ) z).toRingHom).toIntAlgHom).comp φ) := by
      apply MvPolynomial.algHom_ext
      intro q
      show MvPolynomial.aeval (R := ℤ) (fun r : (Σ k, ι k) => c r.1 * z r) (MvPolynomial.X q) =
        MvPolynomial.eval c (MvPolynomial.map (MvPolynomial.aeval (R := ℤ) z).toRingHom (φ (MvPolynomial.X q)))
      rw [hφ]
      simp [mul_comm]
    rw [key]
    rfl
  rw [hB]
  have hzero : MvPolynomial.map (MvPolynomial.aeval (R := ℤ) z).toRingHom (φ f) = 0 := by
    ext a
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero]
    have := hz _ (hcomp a)
    rwa [MvPolynomial.eval_map, ← algebraMap_int_eq, ← MvPolynomial.aeval_def] at this
  rw [hzero, map_zero]

theorem weight_descends_of_sameOrbit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) (N j : ℕ) (M : FlagModel y Ψ N j) (p : Ψ × Fin N) (e e' : ℕ)
    (R : AnLogRes (mCoordIdeal y) ⊤ e) (Rp : AnLogRes (mCoordIdeal (y ∘ stepV M p)) ⊤ e') (h : R.X → Rp.X)
    (A B : HermLine ι) (ph : Rp.X → ℝ) (W : Set Rp.X), A.a = B.a →
    (∀ x, SameOrbit (Rp.lift (h x) (h x)) (R.lift x x ∘ stepV M p)) →
    (∀ x ∈ W, ∀ z ∈ mcPts (mCoordIdeal y), z ∘ stepV M p = Rp.lift x x →
      Real.log (A.h z) = Real.log (B.h z) + ph x) →
    ∀ x, h x ∈ W → Real.log (A.h (R.lift x x)) = Real.log (B.h (R.lift x x)) + ph (h x) := by
  intro K _ ι _ Φ _ y Ψ N j M p e e' R Rp h A B ph W hab horb hW x hx
  classical
  obtain ⟨c, hc0, hceq⟩ := horb x
  have hwmem : R.lift x x ∈ mcPts (mCoordIdeal y) := R.mem x x (R.mem_U x)
  let c' : K → ℂ := fun k =>
    if hk : ((∀ p' : Ψ × Fin N, M.blk p' ≠ Option.some k) ∨ M.blk p = Option.some k) then c ⟨k, hk⟩ else 1
  have hc'0 : ∀ k, c' k ≠ 0 := by
    intro k
    by_cases hk : ((∀ p' : Ψ × Fin N, M.blk p' ≠ Option.some k) ∨ M.blk p = Option.some k)
    · simp only [c', dif_pos hk]
      exact hc0 _
    · simp only [c', dif_neg hk]
      exact one_ne_zero
  let z : (Σ k, ι k) → ℂ := fun r => c' r.1 * R.lift x x r
  have hzstep : z ∘ stepV M p = Rp.lift (h x) (h x) := by
    rw [hceq]
    funext q
    have hq : (∀ p' : Ψ × Fin N, M.blk p' ≠ Option.some q.1.1) ∨ M.blk p = Option.some q.1.1 := q.1.2
    show c' q.1.1 * R.lift x x ⟨q.1.1, q.2⟩ = c q.1 * R.lift x x ⟨q.1.1, q.2⟩
    congr 1
    simp only [c', dif_pos hq]
  have hzmem : z ∈ mcPts (mCoordIdeal y) := by
    refine ⟨fun k => ?_, fun f hf => ?_⟩
    · obtain ⟨i, hi⟩ := hwmem.1 k
      exact ⟨i, mul_ne_zero (hc'0 k) hi⟩
    · exact smul_mem_lemma_2 y (R.lift x x) hwmem.2 c' f hf
  have key := hW (h x) hx z hzmem hzstep
  have hAz : A.h z = (∏ k, ‖c' k‖ ^ A.a k) * A.h (R.lift x x) := A.smul c' _ hc'0
  have hBz : B.h z = (∏ k, ‖c' k‖ ^ A.a k) * B.h (R.lift x x) := by
    rw [hab]
    exact B.smul c' _ hc'0
  have hP : (∏ k, ‖c' k‖ ^ A.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc'0 k)))
  have hApos := A.pos _ hwmem.1
  have hBpos := B.pos _ hwmem.1
  rw [hAz, hBz, Real.log_mul hP hApos.ne', Real.log_mul hP hBpos.ne'] at key
  linarith

end GlobalTheory.CompanionTheory.Ar.PB.FA
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem stepGap_torus : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ)
    (BM : BaseMetric M n) (p : Ψ × Fin N) (z : (Σ k, ι k) → ℂ) (c : K → ℂ), (∀ k, c k ≠ 0) →
    (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → stepGap M BM p (fun q => c q.1 * z q) = stepGap M BM p z := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p z c hc hz
  have hpos : 0 < ∏ k, ‖c k‖ ^ M.dy p k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hc k)) _
  have h1 := (BM.hom p).smul c z hc
  rw [BM.hom_deg p] at h1
  have h2 : (fsHerm ι (M.dy p)).h (fun q => c q.1 * z q) =
      (∏ k, ‖c k‖ ^ M.dy p k) * (fsHerm ι (M.dy p)).h z := (fsHerm ι (M.dy p)).smul c z hc
  unfold stepGap
  rw [h1, h2, Real.log_mul hpos.ne' ((BM.hom p).pos z hz).ne',
    Real.log_mul hpos.ne' ((fsHerm ι (M.dy p)).pos z hz).ne']
  ring

end GlobalTheory.CompanionTheory.Ar.PB.StepW
end
end
