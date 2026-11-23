module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle020
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountPositivity.CardLeOfNegFamily
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.CntLocal
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial

@[expose] public section

section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.Cnt
open Classical ValuativeRel

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def pbLat {K V ι : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    (x : ι → V) (𝔞 : ι → FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) V :=
  Submodule.span (𝓞 K) {v | ∃ i, ∃ c ∈ (𝔞 i : Submodule (𝓞 K) K), v = c • x i}

def gram {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (x : ι → V) : Matrix ι ι K :=
  Matrix.of fun i j => h (x i) (x j)

def NMPseudo : Prop :=
  ∀ (K F V ι : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι] (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) (x : ι → V)
    (𝔞 : ι → FractionalIdeal (nonZeroDivisors (𝓞 K)) K),
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → Module.finrank F K = 2 → h.IsSymm →
    (∀ i, ∀ a ∈ (𝔞 i : Submodule (𝓞 K) K), star a ∈ (𝔞 i : Submodule (𝓞 K) K)) → (∀ i, 𝔞 i ≠ 0) →
    LinearIndependent K x → Submodule.span K (Set.range x) = X → (gram h x).det ≠ 0 →
    Formalism.HermitianLatticesTheory.IsIntegralLat h (pbLat x 𝔞) →
    nM F h X (pbLat x 𝔞) ^ 2 =
      (FractionalIdeal.absNorm ((∏ i, 𝔞 i ^ 2) *
        FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (gram h x).det) : ℝ)

def flagDifferenceVectors (D : Formalism.BasicNotions.D7) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (VS D).V :=
  Sum.elim F0.fvec fun b => ((gS D : D.host.E))⁻¹ • (F'.fl.fvec b - F0.fvec b)

def differentIdealPowers (D : Formalism.BasicNotions.D7) : Fin (D.R.rS + 1) → FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  Fin.snoc (α := fun _ => FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)
    (fun a : Fin D.R.rS => ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ)))) 1

def MMPseudo : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (Z : MatZ D) (F' : LFlag (D.sp.Y 0) D.R.rS (Tn u')), F'.zt = F'.fl.z →
        ZhatL (lf D F0) F' = Z → Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') →
        MMof D F0 F' = pbLat (flagDifferenceVectors D F0 F') (Sum.elim (differentIdealPowers D) (differentIdealPowers D))

def DetGa : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (T T' : D.host.E), star T = T → star T' = T' → ∀ Z : MatZ D,
    (Ga T T' Z).det = (-1) ^ (D.R.rS + 1) * GZ T T' Z

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S
open Classical ValuativeRel

theorem isIntegral_iff_mem_integer (F : Type) [Field F] [ValuativeRel F] (a : F) :
    IsIntegral 𝒪[F] a ↔ a ∈ 𝒪[F] := by
  constructor
  · intro h
    exact (Valuation.integer.integers _).mem_of_integral h
  · intro h
    have e : a = algebraMap 𝒪[F] F ⟨a, h⟩ := rfl
    rw [e]
    exact isIntegral_algebraMap

theorem integral_split_count : OSplit := by
  intro F E _ _ _ _ _ _ L _ e x
  rw [L.O_def]
  have key : IsIntegral 𝒪[F] x ↔ IsIntegral 𝒪[F] (e x) := by
    constructor
    · intro h
      exact h.map ((e : E →ₐ[F] F × F).restrictScalars 𝒪[F])
    · intro h
      have h' := h.map ((e.symm : F × F →ₐ[F] E).restrictScalars 𝒪[F])
      simpa using h'
  rw [key]
  constructor
  · intro h
    exact ⟨(isIntegral_iff_mem_integer F _).1 (h.map (AlgHom.fst 𝒪[F] F F)),
      (isIntegral_iff_mem_integer F _).1 (h.map (AlgHom.snd 𝒪[F] F F))⟩
  · rintro ⟨h1, h2⟩
    exact IsIntegral.pair ((isIntegral_iff_mem_integer F _).2 h1) ((isIntegral_iff_mem_integer F _).2 h2)

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField IsDedekindDomain

set_option linter.style.haveILetI false

section
variable {K : Type} [Field K] [NumberField K]

theorem quot_finite (p : HeightOneSpectrum (𝓞 K)) : Finite (𝓞 K ⧸ p.asIdeal) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ p.ne_bot

def resChar (p : HeightOneSpectrum (𝓞 K)) : ℕ := ringChar (𝓞 K ⧸ p.asIdeal)

theorem resChar_prime (p : HeightOneSpectrum (𝓞 K)) : (resChar p).Prime := by
  haveI := quot_finite p
  haveI := p.isPrime
  exact CharP.char_is_prime (𝓞 K ⧸ p.asIdeal) (ringChar (𝓞 K ⧸ p.asIdeal))

theorem resChar_mem (p : HeightOneSpectrum (𝓞 K)) : ((resChar p : ℕ) : 𝓞 K) ∈ p.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem resChar_le_absNorm (p : HeightOneSpectrum (𝓞 K)) : resChar p ≤ Ideal.absNorm p.asIdeal := by
  haveI := quot_finite p
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hinj := ZMod.castHom_injective (𝓞 K ⧸ p.asIdeal)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_zmod] at this

theorem fiber_card_le (q : ℕ) (hq : q.Prime) (s : Finset (HeightOneSpectrum (𝓞 K))) :
    (s.filter (fun p => resChar p = q)).card ≤ Module.finrank ℚ K := by
  set T := s.filter (fun p => resChar p = q) with hT

  have hdiv : (∏ p ∈ T, p.asIdeal) ∣ Ideal.span {((q : ℕ) : 𝓞 K)} := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro p _ p' _ hne
      rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
      exact Ideal.IsMaximal.coprime_of_ne p.isMaximal p'.isMaximal
        (fun h => hne (HeightOneSpectrum.ext h))
    · intro p hp
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      have : resChar p = q := (Finset.mem_filter.mp hp).2
      rw [← this]
      exact resChar_mem p
  have hnorm : Ideal.absNorm (Ideal.span {((q : ℕ) : 𝓞 K)}) = q ^ Module.finrank ℚ K := by
    rw [Ideal.absNorm_span_singleton]
    have e : ((q : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (q : ℤ) := by simp
    rw [e, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Int.natAbs_pow, Int.natAbs_natCast]
  have h1 : Ideal.absNorm (∏ p ∈ T, p.asIdeal) ∣ q ^ Module.finrank ℚ K := by
    rw [← hnorm]
    exact Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdiv)
  have h2 : q ^ T.card ≤ ∏ p ∈ T, Ideal.absNorm p.asIdeal := by
    apply Finset.pow_card_le_prod
    intro p hp
    have : resChar p = q := (Finset.mem_filter.mp hp).2
    rw [← this]
    exact resChar_le_absNorm p
  rw [← map_prod] at h2
  have h3 := le_trans h2 (Nat.le_of_dvd (pow_pos hq.pos _) h1)
  exact (Nat.pow_le_pow_iff_right hq.one_lt).mp h3
end

theorem prime_zeta_two : PrimeZeta2 := by
  intro K _ _
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  refine summable_of_sum_le
    (c := (Module.finrank ℚ K : ℝ) * ∑' n : ℕ, 1 / ((n : ℝ) ^ 2)) (fun p => by positivity) ?_
  intro u

  have step1 : ∑ p ∈ u, 1 / ((p.asIdeal.absNorm : ℝ) ^ 2) ≤ ∑ p ∈ u, 1 / ((resChar p : ℝ) ^ 2) := by
    apply Finset.sum_le_sum
    intro p _
    have hp : (0 : ℝ) < resChar p := by exact_mod_cast (resChar_prime p).pos
    have hle : (resChar p : ℝ) ≤ (p.asIdeal.absNorm : ℝ) := by exact_mod_cast resChar_le_absNorm p
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
  calc ∑ p ∈ u, 1 / ((p.asIdeal.absNorm : ℝ) ^ 2)
      ≤ ∑ p ∈ u, 1 / ((resChar p : ℝ) ^ 2) := step1
    _ = ∑ q ∈ u.image resChar, ∑ p ∈ u with resChar p = q, 1 / ((resChar p : ℝ) ^ 2) :=
        by
          rw [Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_image_of_mem _ hp)]
    _ ≤ ∑ q ∈ u.image resChar, (Module.finrank ℚ K : ℝ) * (1 / ((q : ℝ) ^ 2)) := by
        apply Finset.sum_le_sum
        intro q _
        rw [Finset.sum_congr rfl (g := fun _ => 1 / ((q : ℝ) ^ 2))
          (fun p hp => by rw [(Finset.mem_filter.mp hp).2]), Finset.sum_const, nsmul_eq_mul]
        have hc : ((u.filter (fun p => resChar p = q)).card : ℝ) ≤ Module.finrank ℚ K := by
          by_cases hq : q.Prime
          · exact_mod_cast fiber_card_le q hq u
          · have : u.filter (fun p => resChar p = q) = ∅ := by
              rw [Finset.filter_eq_empty_iff]
              intro p _ h
              exact hq (h ▸ resChar_prime p)
            rw [this, Finset.card_empty, Nat.cast_zero]
            positivity
        gcongr
    _ = (Module.finrank ℚ K : ℝ) * ∑ q ∈ u.image resChar, 1 / ((q : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ (Module.finrank ℚ K : ℝ) * ∑' n : ℕ, 1 / ((n : ℝ) ^ 2) := by
        gcongr
        exact hs.sum_le_tsum _ (fun _ _ => by positivity)

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hswap (D : Formalism.BasicNotions.D7) (x y : (VS D).V) : (VS D).hT y x = star ((VS D).hT x y) := ((VS D).herm.eq x y).symm

theorem hzero_swap (D : Formalism.BasicNotions.D7) {x y : (VS D).V} (h : (VS D).hT x y = 0) : (VS D).hT y x = 0 := by
  rw [hswap, h, star_zero]

theorem hFE (D : Formalism.BasicNotions.D7) (i i' : Fin D.R.rS) :
    (VS D).hT (D.sp.hypF i) (D.sp.hypE i') = if i' = i then 1 else 0 := by
  rw [hswap, D.sp.hyp_ef i' i]
  split_ifs <;> simp

theorem hEz (D : Formalism.BasicNotions.D7) (i : Fin D.R.rS) : (VS D).hT (D.sp.hypE i) D.sp.zm = 0 := by
  rw [hswap, (D.sp.hyp_orthz i).1, star_zero]

theorem hFz (D : Formalism.BasicNotions.D7) (i : Fin D.R.rS) : (VS D).hT (D.sp.hypF i) D.sp.zm = 0 := by
  rw [hswap, (D.sp.hyp_orthz i).2, star_zero]

theorem real_of_emb (D : Formalism.BasicNotions.D7) (τ : D.host.E →+* ℂ) (w : (VS D).V) :
    τ ((VS D).hT w w) = ((τ ((VS D).hT w w)).re : ℂ) := by
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := D.sp.cm.cmUnram.2.1 τ
  have h1 : starRingEnd ℂ (τ ((VS D).hT w w)) = τ ((VS D).hT w w) := by
    rw [← hτ, ← hswap]
  have him : (τ ((VS D).hT w w)).im = 0 := Complex.conj_eq_iff_im.1 h1
  exact Complex.ext (by simp) (by simp [him])

theorem semidef (D : Formalism.BasicNotions.D7) (w : (VS D).V) (hE : ∀ a, (VS D).hT (D.sp.hypE a) w = 0)
    (hF : ∀ a, (VS D).hT (D.sp.hypF a) w = 0) (hz : (VS D).hT D.sp.zm w = 0) (τ : D.host.E →+* ℂ) :
    0 ≤ (τ ((VS D).hT w w)).re := by
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := D.sp.cm.cmUnram.2.1 τ
  by_contra hlt
  rw [not_le] at hlt
  have hT0 : (0 : ℝ) < D.sp.T := by exact_mod_cast D.sp.T_prime.pos
  let wv : Fin D.R.rS ⊕ Bool → (VS D).V :=
    Sum.elim (fun a => D.sp.hypE a - D.sp.hypF a) (fun b => if b then w else D.sp.zm)
  let d : Fin D.R.rS ⊕ Bool → ℝ :=
    Sum.elim (fun _ => -2) (fun b => if b then (τ ((VS D).hT w w)).re else -(D.sp.T : ℝ))
  have hoff : ∀ i j, i ≠ j → (VS D).hT (wv i) (wv j) = 0 := by
    intro i j hij
    rcases i with a | b <;> rcases j with a' | b'
    · have ha : a ≠ a' := fun h => hij (by rw [h])
      have ha' : a' ≠ a := fun h => ha h.symm
      simp only [wv, Sum.elim_inl, map_sub, LinearMap.sub_apply, D.sp.hyp_ee, D.sp.hyp_ff, D.sp.hyp_ef,
        hFE, if_neg ha, if_neg ha']
      simp
    · cases b'
      · simp only [wv, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, if_false, map_sub,
          LinearMap.sub_apply, hEz, hFz, sub_zero]
      · simp only [wv, Sum.elim_inl, Sum.elim_inr, if_true, map_sub, LinearMap.sub_apply, hE, hF,
          sub_zero]
    · cases b
      · simp only [wv, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, if_false, map_sub,
          (D.sp.hyp_orthz a').1, (D.sp.hyp_orthz a').2, sub_zero]
      · simp only [wv, Sum.elim_inl, Sum.elim_inr, if_true, map_sub, hzero_swap D (hE a'),
          hzero_swap D (hF a'), sub_zero]
    · cases b <;> cases b'
      · exact absurd rfl hij
      · simpa [wv] using hz
      · simpa [wv] using hzero_swap D hz
      · exact absurd rfl hij
  have hdiag : ∀ i, τ ((VS D).hT (wv i) (wv i)) = (d i : ℂ) := by
    intro i
    rcases i with a | b
    · simp only [wv, d, Sum.elim_inl, map_sub, LinearMap.sub_apply, D.sp.hyp_ee, D.sp.hyp_ff,
        D.sp.hyp_ef, hFE, if_true]
      rw [map_zero, map_one]
      push_cast; ring
    · cases b
      · simp only [wv, d, Sum.elim_inr, Bool.false_eq_true, if_false, D.sp.zm_norm, map_neg,
          map_natCast]
        push_cast; ring
      · simp only [wv, d, Sum.elim_inr, if_true]
        exact real_of_emb D τ w
  have hneg : ∀ i, d i < 0 := by
    intro i
    rcases i with a | b
    · simp [d]
    · cases b
      · simp only [d, Sum.elim_inr, Bool.false_eq_true, if_false]; linarith
      · simpa [d] using hlt
  have hc := PI.CntNotPosW.card_le_of_negFamily (VS D) τ hτ (D.sp.Y_sig 0 τ) wv d hoff hdiag hneg
  have hq : ((D.sp.Y 0).sig τ).2 = D.R.rS + 1 := by rw [D.sp.baseSpace_signature_eq τ]; rfl
  rw [hq] at hc
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool] at hc
  omega

theorem isotropic_zero (D : Formalism.BasicNotions.D7) (w : (VS D).V) (hE : ∀ a, (VS D).hT (D.sp.hypE a) w = 0)
    (hF : ∀ a, (VS D).hT (D.sp.hypF a) w = 0) (hz : (VS D).hT D.sp.zm w = 0)
    (h0 : (VS D).hT w w = 0) : w = 0 := by
  let τ : D.host.E →+* ℂ := (IsAlgClosed.lift : D.host.E →ₐ[ℚ] ℂ).toRingHom
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := D.sp.cm.cmUnram.2.1 τ

  have orthW : ∀ y : (VS D).V, (∀ a, (VS D).hT (D.sp.hypE a) y = 0) →
      (∀ a, (VS D).hT (D.sp.hypF a) y = 0) → (VS D).hT D.sp.zm y = 0 → (VS D).hT w y = 0 := by
    intro y hyE hyF hyz
    by_contra hx
    set x := (VS D).hT w y with hxdef
    have hτx : τ x ≠ 0 := (map_ne_zero τ).2 hx
    have hN : 0 < Complex.normSq (τ x) := Complex.normSq_pos.2 hτx
    set y' : (VS D).V := star x • y with hy'
    have hxx : τ (x * star x) = ((Complex.normSq (τ x) : ℝ) : ℂ) := by
      rw [map_mul, hτ, Complex.mul_conj]
    have key : ∀ n : ℕ, 2 * n * Complex.normSq (τ x) ≤ (τ ((VS D).hT y' y')).re := by
      intro n
      set v : (VS D).V := (n : D.host.E) • w - y' with hv
      have hvE : ∀ a, (VS D).hT (D.sp.hypE a) v = 0 := by
        intro a; simp [hv, hy', map_sub, map_smul, hE a, hyE a]
      have hvF : ∀ a, (VS D).hT (D.sp.hypF a) v = 0 := by
        intro a; simp [hv, hy', map_sub, map_smul, hF a, hyF a]
      have hvz : (VS D).hT D.sp.zm v = 0 := by
        simp [hv, hy', map_sub, map_smul, hz, hyz]
      have hs := semidef D v hvE hvF hvz τ
      have hyw : (VS D).hT y w = star x := by rw [hswap]
      have e1 : (VS D).hT v v = -(2 * (n : D.host.E)) * (x * star x) + (VS D).hT y' y' := by
        simp only [hv, map_sub, LinearMap.sub_apply, map_smulₛₗ, map_smul, LinearMap.smul_apply,
          smul_eq_mul, starRingEnd_apply, star_natCast, h0, hy', star_star, hyw, ← hxdef, RingHom.id_apply]
        ring
      have e2 : (τ ((VS D).hT v v)).re =
          -(2 * n * Complex.normSq (τ x)) + (τ ((VS D).hT y' y')).re := by
        rw [e1, map_add (f := _), map_mul, hxx, map_neg, map_mul, map_ofNat, map_natCast, Complex.add_re]
        congr 1
        have : -(2 * (n : ℂ)) * ((Complex.normSq (τ x) : ℝ) : ℂ) =
            ((-(2 * n * Complex.normSq (τ x)) : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.ofReal_re]
      linarith
    obtain ⟨n, hn⟩ := exists_nat_gt ((τ ((VS D).hT y' y')).re / (2 * Complex.normSq (τ x)))
    have h2 := key n
    rw [div_lt_iff₀ (by positivity)] at hn
    nlinarith

  have hzz : (VS D).hT D.sp.zm D.sp.zm ≠ 0 := by
    rw [D.sp.zm_norm, neg_ne_zero]
    exact_mod_cast D.sp.T_prime.ne_zero
  apply (VS D).nondeg.1 w
  intro x
  set xW : (VS D).V := x - ∑ a, ((VS D).hT (D.sp.hypF a) x • D.sp.hypE a + (VS D).hT (D.sp.hypE a) x • D.sp.hypF a) -
    ((VS D).hT D.sp.zm x / (VS D).hT D.sp.zm D.sp.zm) • D.sp.zm with hxW
  have hWE : ∀ b, (VS D).hT (D.sp.hypE b) xW = 0 := by
    intro b

    simp [hxW, map_sub, map_sum, map_add (f := _), map_smul, D.sp.hyp_ee, D.sp.hyp_ef, hEz]
  have hWF : ∀ b, (VS D).hT (D.sp.hypF b) xW = 0 := by
    intro b

    simp [hxW, map_sub, map_sum, map_add (f := _), map_smul, D.sp.hyp_ff, hFE, hFz]
  have hWz : (VS D).hT D.sp.zm xW = 0 := by

    simp [hxW, map_sub, map_sum, map_add (f := _), map_smul, (D.sp.hyp_orthz _).1, (D.sp.hyp_orthz _).2, hzz]
  have h1 := orthW xW hWE hWF hWz
  have hwE : ∀ a, (VS D).hT w (D.sp.hypE a) = 0 := fun a => hzero_swap D (hE a)
  have hwF : ∀ a, (VS D).hT w (D.sp.hypF a) = 0 := fun a => hzero_swap D (hF a)
  have hwz : (VS D).hT w D.sp.zm = 0 := hzero_swap D hz

  simpa [hxW, map_sub, map_sum, map_add (f := _), map_smul, hwE, hwF, hwz] using h1

theorem weights_are_positive : WPos := by
  intro D w hE hF hz hw
  have pos : ∀ τ : D.host.E →+* ℂ, 0 < (τ ((VS D).hT w w)).re := by
    intro τ
    refine lt_of_le_of_ne (semidef D w hE hF hz τ) fun h => hw ?_
    apply isotropic_zero D w hE hF hz
    apply τ.injective
    rw [real_of_emb D τ w, ← h, Complex.ofReal_zero, map_zero]
  haveI : Nonempty (D.host.E →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  have ht := trace_eq_sum_embeddings (K := ℚ) (L := D.host.E) (E := ℂ) (x := (VS D).hT w w)
  have hre := congrArg Complex.re ht
  rw [Complex.re_sum] at hre
  have hsum : 0 < ∑ σ : D.host.E →ₐ[ℚ] ℂ, (σ ((VS D).hT w w)).re :=
    Finset.sum_pos (fun σ _ => pos σ.toRingHom) Finset.univ_nonempty
  rw [← hre] at hsum
  have : ((Algebra.trace ℚ D.host.E ((VS D).hT w w) : ℚ) : ℝ) =
      (algebraMap ℚ ℂ (Algebra.trace ℚ D.host.E ((VS D).hT w w))).re := by simp
  rw [← this] at hsum
  exact_mod_cast hsum

theorem definite_finite : DefFinW := defFinW_of weights_are_positive

end PI.UnitaryGroupMassFormula.CntFormula
end
end
