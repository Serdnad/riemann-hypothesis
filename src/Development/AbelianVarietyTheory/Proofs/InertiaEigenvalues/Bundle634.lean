module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle281
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle058
public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle564
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle607
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle590
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle589
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle605
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle606
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineSubrepresentation
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.KerGood

theorem map_aeval {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (F : M →ₗ[R] N) (A : Module.End R M) (A' : Module.End R N) (hA : ∀ y, F (A y) = A' (F y))
    (p : Polynomial R) (y : M) : F (Polynomial.aeval A p y) = Polynomial.aeval A' p (F y) := by
  induction p using Polynomial.induction_on generalizing y with
  | C c => simp [Module.algebraMap_end_apply]
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n c h =>
    simp only [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply] at h ⊢
    rw [h (A y), hA]

theorem isGood_of_injective (hF : GlobalTheory.Published.FontaineBcris) {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a]
    {ϖ : PiSys l e} {LL : FinExt l} {Pl : LocPrime l} {AI : LocAinf l Pl} (hs : IsStd Pl AI)
    {Sig : Finset (ZMod e)} {U : Finset ℤ} {T₀ T₁ : QLat LL} (f : T₀.V →ₗ[↥LL.1] T₁.V)
    (hf : Function.Injective f) (he : ∀ g x, f (T₀.ρ g x) = T₁.ρ g (f x))
    (hT : IsGood a ϖ Pl T₁ Sig U) : IsGood a ϖ Pl T₀ Sig U := by
  refine ⟨?_, ?_, ?_⟩
  · have hS := (GlobalTheory.RegularRing.fontaineFormalism hF l Pl AI hs).2.2.2.1 (ϖ.field a) LL
    exact hS _ (resF T₁ (ϖ.field a)).ρ _ (resF T₀ (ϖ.field a)).ρ f (fun g x => he _ x) hf hT.crys
  · intro γ hγ w hw x hx
    obtain ⟨r, hr⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hf)
    have hrf : ∀ v, r (f v) = v := fun v => LinearMap.congr_fun hr v
    have hRF : ∀ y, GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB (Qp := ℚ_[l]) (B := Pl.R.B) r
        (GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB (Qp := ℚ_[l]) (B := Pl.R.B) f y) = y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB, hrf]
      | add y z hy hz => simp only [map_add (f := _), hy, hz]
    have hFi : Function.Injective (GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB (Qp := ℚ_[l]) (B := Pl.R.B) f) :=
      Function.LeftInverse.injective hRF
    have hFx := GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB_mem (Pl.PD (ϖ.field a)) (ρ := (resF T₀ (ϖ.field a)).ρ)
      (ρ' := (resF T₁ (ϖ.field a)).ρ) (f := f) (fun g x => he _ x) x hx
    have h1 := hT.type γ hγ w hw _ hFx
    have hc : ∀ y, GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB (Qp := ℚ_[l]) (B := Pl.R.B) f
        (actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T₀.ρ γ y) =
        actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T₁.ρ γ (GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB (Qp := ℚ_[l]) (B := Pl.R.B) f y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB, actVB, he]
      | add y z hy hz => simp only [map_add (f := _), hy, hz]
    apply hFi
    exact (map_aeval _ _ _ hc _ x).trans (h1.trans (map_zero _).symm)
  · intro τ b hb
    exact hT.jumps τ b (GlobalTheory.HTW.isJumpV_of_injective _ _ T₁.ρ f hf he τ b hb)

theorem main : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (Sig : Finset (ZMod e)) (U : Finset ℤ) (T₁ T₂ : QLat LL) (g : LatHom T₁.L T₂.L), g.Onto → IsGood a ϖ Pl T₁ Sig U → ∃ (T₀ : QLat LL) (f : LatHom T₀.L T₁.L), IsSESLat (Qp := ℚ_[l]) f g ∧ IsGood a ϖ Pl T₀ Sig U := by
  intro hF l _ a e _ _ ϖ LL _ _ Pl AI hs Sig U T₁ T₂ g hg hT
  obtain ⟨⟨_, hD, hFr⟩, -⟩ := GlobalTheory.LocalIntegers.goodO_integers l LL
  have hden : Formalism.MainNotions.LiftingTheory.lker_Den ↥LL.1 ↥(OL LL) := by
    intro c
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj (nonZeroDivisors ↥(OL LL)) c
    refine ⟨s, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2, x, ?_⟩
    rw [mul_comm]
    exact hxs
  have hinj : Function.Injective (Formalism.MainNotions.LiftingTheory.lker_ι g hg hden).f := fun x y h => Subtype.ext h
  refine ⟨Formalism.MainNotions.LiftingTheory.lker_T₀ g hg hden, Formalism.MainNotions.LiftingTheory.lker_ι g hg hden, ?_,
    isGood_of_injective hF hs _ hinj (Formalism.MainNotions.LiftingTheory.lker_ι g hg hden).equiv hT⟩
  exact ⟨hinj, Formalism.MainNotions.LiftingTheory.lker_surj g hg, hg,
    fun x => ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩, fun y hy => hy⟩

end GlobalTheory.KerGood
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem le_one_of_mul_pow_le_one (c : ℝ) (n : ℕ) (h : ∀ t : ℝ≥0, t < 1 → c * (t : ℝ) ^ n ≤ 1) : c ≤ 1 := by
  have ht : Filter.Tendsto (fun t : ℝ≥0 => c * (t : ℝ) ^ n) (nhdsWithin (1 : ℝ≥0) (Set.Iio 1)) (nhds (c * ((1 : ℝ≥0) : ℝ) ^ n)) :=
    ((continuous_const.mul ((NNReal.continuous_coe).pow n)).tendsto 1).mono_left nhdsWithin_le_nhds
  have : (nhdsWithin (1 : ℝ≥0) (Set.Iio 1)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, zero_lt_one⟩
  have h2 := le_of_tendsto ht (eventually_nhdsWithin_of_forall fun t (hti : t ∈ Set.Iio 1) => h t hti)
  simpa using h2

theorem disc_bdd_isSeries : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ y : bk.DS ρ, (∀ ρ₁ : ℝ≥0, ρ₁ < 1 → ∃ (ρ' : ℝ≥0) (R : bk.DS ρ' →+* bk.DS ρ) (y' : bk.DS ρ'), ρ₁ ≤ ρ' ∧ ρ ≤ ρ' ∧ ρ' < 1 ∧ IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id bk.S) R ∧ R y' = y ∧ ‖y'‖ ≤ 1) → ∃ a, toDisc l (X : bk.S) ρ a = y := by
  intro l _ K bk ρ hρ hρ1 y hy
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 (Fact.out : l.Prime).pos
  obtain ⟨a, ha1, ha2, ha3, -⟩ := GlobalTheory.T.exists_gaussNorm_coeff_wittDisc l K bk ρ hρ hρ1
  obtain ⟨-, hk2, -, -⟩ := GlobalTheory.T.closedDiscGaugeCompletion_zero_one_properties l K bk

  have hcont : ∀ (r : ℝ≥0), 0 < r → ∀ (b : ℕ → (bk.DS r →+ Disc l (0 : Wq l bk.a) 1)),
      (∀ n z, ‖b n z‖ * (r : ℝ) ^ n ≤ ‖z‖) → ∀ n, Continuous (b n) := by
    intro r hr b hb n
    refine AddMonoidHomClass.continuous_of_bound (b n) (((r : ℝ) ^ n)⁻¹) fun z => ?_
    have hp : (0 : ℝ) < (r : ℝ) ^ n := pow_pos (by exact_mod_cast hr) n
    rw [inv_mul_eq_div, le_div_iff₀ hp]
    exact hb n z

  have htor : ∀ z : Disc l (0 : Wq l bk.a) 1, l • z = 0 → z = 0 := by
    intro z hz
    have h := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l (Wq l bk.a) (0 : Wq l bk.a) 1).2.1 z
    rw [← nsmul_eq_mul, hz, norm_zero] at h
    exact norm_eq_zero.1 (by
      have := (div_eq_zero_iff.1 h.symm).resolve_right hl0.ne'
      exact this)

  have hle : ∀ n, ‖a n y‖ ≤ 1 := by
    intro n
    refine le_one_of_mul_pow_le_one _ n fun t ht => ?_
    obtain ⟨ρ', R, y', h1, h2, h3, hR, hRy, hy'⟩ := hy t ht
    have hρ' : 0 < ρ' := hρ.trans_le h2
    obtain ⟨a', ha1', ha2', -, -⟩ := GlobalTheory.T.exists_gaussNorm_coeff_wittDisc l K bk ρ' hρ' h3
    have hRc : Continuous R := AddMonoidHomClass.continuous_of_bound R 1 fun z => (hR.norm_le z).trans (one_mul _).ge
    have e : ((a n).comp (R : bk.DS ρ' →+ bk.DS ρ)) = a' n :=
      (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l bk.S (X : bk.S) ρ').2.2.1 _ htor _ _ ((hcont ρ hρ a ha2 n).comp hRc)
        (hcont ρ' hρ' a' ha2' n) fun x => by
          simp only [AddMonoidHom.coe_comp, AddMonoidHom.coe_ofClass, Function.comp_apply]
          rw [hR.ext x, RingHom.id_apply, ha1, ha1']
    have e2 : a n y = a' n y' := by rw [← hRy, ← e]; rfl
    rw [e2]
    calc ‖a' n y'‖ * (t : ℝ) ^ n ≤ ‖a' n y'‖ * (ρ' : ℝ) ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ t.2 (by exact_mod_cast h1) n) (norm_nonneg _)
      _ ≤ ‖y'‖ := ha2' n y'
      _ ≤ 1 := hy'
  choose w hw using fun n => hk2 (a n y) (hle n)
  refine ⟨PowerSeries.mk w, ?_⟩
  have h0 : ‖y - toDisc l (X : bk.S) ρ (PowerSeries.mk w)‖ ≤ 0 :=
    ha3 _ 0 le_rfl fun n => by
      rw [map_sub, ha1, coeff_mk, ← hw, sub_self, norm_zero, zero_mul]
  exact (sub_eq_zero.1 (norm_le_zero_iff.1 h0)).symm

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.GaussMul

open Filter

theorem norm_sum_lt_of_ultra {E ι : Type} [SeminormedAddCommGroup E] [IsUltrametricDist E] (s : Finset ι)
    (f : ι → E) {C : ℝ} (hC : 0 < C) (h : ∀ i ∈ s, ‖f i‖ < C) : ‖∑ i ∈ s, f i‖ < C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hC
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
      (max_lt (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem exists_eq_sup {f : ℕ → ℝ} {M : ℝ} (hM : 0 < M) (hle : ∀ n, f n ≤ M)
    (hsup : ∀ r : ℝ, 0 ≤ r → (∀ n, f n ≤ r) → M ≤ r) (ht : Tendsto f atTop (nhds 0)) : ∃ n, f n = M := by
  by_contra hne
  push_neg at hne
  have hlt : ∀ n, f n < M := fun n => lt_of_le_of_ne (hle n) (hne n)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds (half_pos hM)))
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image (Finset.range (N + 1)) f ⟨0, by simp⟩
  have h1 : M ≤ max (M / 2) (f k) := hsup _ ((half_pos hM).le.trans (le_max_left _ _)) fun n => by
    by_cases hn : n < N + 1
    · exact (hk n (Finset.mem_range.2 hn)).trans (le_max_right _ _)
    · exact (hN n (by omega)).le.trans (le_max_left _ _)
  exact absurd h1 (not_le.2 (max_lt (half_lt_self hM) (hlt k)))

theorem gauss {D : Type} [NormedRing D] [IsUltrametricDist D] (hm : ∀ x y : D, ‖x * y‖ = ‖x‖ * ‖y‖) {ρ : ℝ}
    (hρ : 0 < ρ) (p q : ℕ → D) {P Q : ℝ} (hP : 0 < P) (hQ : 0 < Q) (hp : ∀ n, ‖p n‖ * ρ ^ n ≤ P)
    (hq : ∀ n, ‖q n‖ * ρ ^ n ≤ Q) (hp0 : ∃ n, ‖p n‖ * ρ ^ n = P) (hq0 : ∃ n, ‖q n‖ * ρ ^ n = Q) :
    ∃ N, ‖∑ x ∈ Finset.HasAntidiagonal.antidiagonal N, p x.1 * q x.2‖ * ρ ^ N = P * Q := by
  classical
  set n₀ := Nat.find hp0
  set m₀ := Nat.find hq0
  have hn₀ : ‖p n₀‖ * ρ ^ n₀ = P := Nat.find_spec hp0
  have hm₀ : ‖q m₀‖ * ρ ^ m₀ = Q := Nat.find_spec hq0
  refine ⟨n₀ + m₀, ?_⟩
  have hρN : 0 < ρ ^ (n₀ + m₀) := pow_pos hρ _
  have hmem : (n₀, m₀) ∈ Finset.HasAntidiagonal.antidiagonal (n₀ + m₀) := by simp
  rw [← Finset.add_sum_erase _ _ hmem]
  have hdom : ‖p n₀ * q m₀‖ * ρ ^ (n₀ + m₀) = P * Q := by
    rw [hm, pow_add, ← hn₀, ← hm₀]; ring
  have hrest : ‖∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (n₀ + m₀)).erase (n₀, m₀), p x.1 * q x.2‖ < P * Q / ρ ^ (n₀ + m₀) := by
    refine norm_sum_lt_of_ultra _ _ (div_pos (mul_pos hP hQ) hρN) fun x hx => ?_
    rw [lt_div_iff₀ hρN]
    obtain ⟨hne, hx⟩ := Finset.mem_erase.1 hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have e : ‖p x.1 * q x.2‖ * ρ ^ (n₀ + m₀) = (‖p x.1‖ * ρ ^ x.1) * (‖q x.2‖ * ρ ^ x.2) := by
      rw [hm, ← hx, pow_add]; ring
    rw [e]
    have h1 : 0 ≤ ‖p x.1‖ * ρ ^ x.1 := by positivity
    have h2 : 0 ≤ ‖q x.2‖ * ρ ^ x.2 := by positivity
    by_cases h : x.1 < n₀
    · have hlt : ‖p x.1‖ * ρ ^ x.1 < P := lt_of_le_of_ne (hp _) (Nat.find_min hp0 h)
      calc (‖p x.1‖ * ρ ^ x.1) * (‖q x.2‖ * ρ ^ x.2) ≤ (‖p x.1‖ * ρ ^ x.1) * Q :=
            mul_le_mul_of_nonneg_left (hq _) h1
        _ < P * Q := mul_lt_mul_of_pos_right hlt hQ
    · have h' : x.2 < m₀ := by
        by_contra h''
        apply hne
        ext <;> simp <;> omega
      have hlt : ‖q x.2‖ * ρ ^ x.2 < Q := lt_of_le_of_ne (hq _) (Nat.find_min hq0 h')
      calc (‖p x.1‖ * ρ ^ x.1) * (‖q x.2‖ * ρ ^ x.2) ≤ P * (‖q x.2‖ * ρ ^ x.2) :=
            mul_le_mul_of_nonneg_right (hp _) h2
        _ < P * Q := mul_lt_mul_of_pos_left hlt hP
  have hdom' : ‖p n₀ * q m₀‖ = P * Q / ρ ^ (n₀ + m₀) := by
    rw [eq_div_iff hρN.ne', hdom]
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hdom']; exact hrest.ne'), hdom',
    max_eq_left hrest.le, div_mul_cancel₀ _ hρN.ne']

end GlobalTheory.BSP.GaussMul

namespace GlobalTheory.BSP.GaussMul

theorem norm_mul_disc (l : ℕ) [hl : Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (x y : bk.DS ρ) : ‖x * y‖ = ‖x‖ * ‖y‖ := by
  obtain ⟨a, ha1, ha2, ha3, ha4⟩ := GlobalTheory.T.exists_gaussNorm_coeff_wittDisc l K bk ρ hρ0 hρ1
  haveI : IsUltrametricDist (Disc l (0 : Wq l bk.a) 1) := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l (Wq l bk.a) 0 1).1
  have hm0 := (GlobalTheory.T.closedDiscGaugeCompletion_zero_one_properties l K bk).1
  have hρ : (0 : ℝ) < ρ := NNReal.coe_pos.2 hρ0

  have step1 : ∀ s t : bk.S, ‖toDisc l (X : bk.S) ρ s * toDisc l (X : bk.S) ρ t‖ =
      ‖toDisc l (X : bk.S) ρ s‖ * ‖toDisc l (X : bk.S) ρ t‖ := by
    intro s t
    rcases eq_or_ne (toDisc l (X : bk.S) ρ s) 0 with hu | hu
    · simp [hu]
    rcases eq_or_ne (toDisc l (X : bk.S) ρ t) 0 with hv | hv
    · simp [hv]
    have hP : 0 < ‖toDisc l (X : bk.S) ρ s‖ := norm_pos_iff.2 hu
    have hQ : 0 < ‖toDisc l (X : bk.S) ρ t‖ := norm_pos_iff.2 hv
    obtain ⟨N, hN⟩ := gauss hm0 hρ (fun n => a n (toDisc l (X : bk.S) ρ s)) (fun n => a n (toDisc l (X : bk.S) ρ t))
      hP hQ (fun n => ha2 n _) (fun n => ha2 n _)
      (exists_eq_sup hP (fun n => ha2 n _) (ha3 _) (ha4 _)) (exists_eq_sup hQ (fun n => ha2 n _) (ha3 _) (ha4 _))
    have hconv : a N (toDisc l (X : bk.S) ρ s * toDisc l (X : bk.S) ρ t) =
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal N, a x.1 (toDisc l (X : bk.S) ρ s) * a x.2 (toDisc l (X : bk.S) ρ t) := by

      rw [← map_mul, ha1, coeff_mul, map_sum]
      exact Finset.sum_congr rfl fun x _ => by rw [map_mul, ha1, ha1]
    refine le_antisymm (norm_mul_le _ _) ?_
    rw [← hN, ← hconv]
    exact ha2 N _

  have hlm := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l bk.S (X : bk.S) ρ).2.1
  have hl0 : (0 : ℝ) < (l : ℝ) := Nat.cast_pos.2 hl.out.pos
  have hlpow : ∀ (n : ℕ) (z : bk.DS ρ), ‖z * ((l : ℕ) : bk.DS ρ) ^ n‖ = ‖z‖ / (l : ℝ) ^ n := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [pow_succ, ← mul_assoc, mul_comm _ ((l : ℕ) : bk.DS ρ), hlm, ih, pow_succ, div_div]
  have hpre : ∀ p : PreDisc l (X : bk.S) ρ, ∃ (n : ℕ) (s : bk.S),
      ofPre l (X : bk.S) ρ p * ((l : ℕ) : bk.DS ρ) ^ n = toDisc l (X : bk.S) ρ s := by
    intro p
    obtain ⟨n, s, h⟩ := IsLocalization.Away.surj ((l : ℕ) : bk.S) p
    refine ⟨n, s, ?_⟩
    have h' := congrArg (ofPre l (X : bk.S) ρ) h
    rw [map_mul, map_pow, map_natCast, map_natCast] at h'
    exact h'
  have step2 : ∀ p q : PreDisc l (X : bk.S) ρ, ‖ofPre l (X : bk.S) ρ p * ofPre l (X : bk.S) ρ q‖ =
      ‖ofPre l (X : bk.S) ρ p‖ * ‖ofPre l (X : bk.S) ρ q‖ := by
    intro p q
    obtain ⟨n, s, hs⟩ := hpre p
    obtain ⟨m, t, ht⟩ := hpre q
    have e : ofPre l (X : bk.S) ρ p * ofPre l (X : bk.S) ρ q * ((l : ℕ) : bk.DS ρ) ^ (n + m) =
        toDisc l (X : bk.S) ρ s * toDisc l (X : bk.S) ρ t := by
      rw [← hs, ← ht, pow_add]; ring
    have h1 := hlpow (n + m) (ofPre l (X : bk.S) ρ p * ofPre l (X : bk.S) ρ q)
    rw [e, step1, ← hs, ← ht, hlpow, hlpow, pow_add, div_mul_div_comm] at h1
    exact ((div_left_inj' (by positivity)).1 h1).symm
  exact (denseRange_ofPre l (X : bk.S) ρ).induction_on₂ (p := fun x y : bk.DS ρ => ‖x * y‖ = ‖x‖ * ‖y‖)
    (isClosed_eq (continuous_norm.comp (continuous_fst.mul continuous_snd))
      ((continuous_norm.comp continuous_fst).mul (continuous_norm.comp continuous_snd))) step2 x y

theorem norm_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 →
    ∀ x y : bk.DS ρ, ‖x * y‖ = ‖x‖ * ‖y‖ :=
  fun l _ K bk ρ h0 h1 x y => norm_mul_disc l K bk ρ h0 h1 x y

end GlobalTheory.BSP.GaussMul
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.NullOverS

theorem topBasis_c_mem_map {S A ι : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    (TB : TopBasis s I ι) (i : ι) (n : ℕ) {x : A} (hx : x ∈ (I ^ n).map s) : TB.c i x ∈ I ^ n := by
  have key : ∀ r : A, TB.c i (r * x) ∈ I ^ n := by
    refine Submodule.span_induction (p := fun x _ => ∀ r : A, TB.c i (r * x) ∈ I ^ n) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨j, hj, rfl⟩ r
      rw [mul_comm, TB.c_mul]
      exact Ideal.mul_mem_right _ _ hj
    · intro r; simp
    · intro y z _ _ hy hz r
      rw [mul_add, map_add (f := _)]; exact Ideal.add_mem _ (hy r) (hz r)
    · intro a y _ hy r
      rw [smul_eq_mul, ← mul_assoc]; exact hy _
  simpa using key 1

theorem topBasis_c_i₀ {S A ι : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    (TB : TopBasis s I ι) (a : S) : TB.c TB.i₀ (s a) = a := by
  have h := TB.c_mul TB.i₀ a 1
  rw [mul_one, ← TB.b_i₀, TB.c_self, mul_one] at h
  exact h

end GlobalTheory.NullOverS

theorem GlobalTheory.NullOverS.null_of_mul_null : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ι : Type)
    (TB : TopBasis bk.ev bk.J ι) (d : ℕ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit (Y.map (inclW l)) →
    ∀ (σ : ι → Matrix (Fin d) (Fin d) bk.S),
    (∀ (n : ℕ) (a b : Fin d), {i | (Y * (σ i).map bk.ev) a b ∉ (bk.J ^ n).map bk.ev}.Finite) →
    ∀ (n : ℕ) (a b : Fin d), {i | σ i a b ∉ bk.J ^ n}.Finite := by
  intro l _ K bk ι TB d Y hY σ hσ N a b
  obtain ⟨n, hn⟩ := GlobalTheory.T.breuilKisin_mem_ideal_pow_of_X_pow_mul_mem l K bk N
  have hdet : IsUnit (inclW l Y.det) := by
    rw [RingHom.map_det]; exact (Matrix.isUnit_iff_isUnit_det _).1 hY
  obtain ⟨m, t, q, hq⟩ := GlobalTheory.T.ainf_unit_bounded_teichmullerFlat_denominators l K bk Y.det hdet n
  obtain ⟨n', hn'⟩ := hn m
  refine (Set.finite_iUnion fun c : Fin d => hσ n' c b).subset ?_
  intro i hi
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hi ⊢
  by_contra hc
  push_neg at hc
  apply hi
  apply hn'
  have h1 : (t • adjugate Y * (Y * (σ i).map bk.ev)) a b = t * Y.det * bk.ev (σ i a b) := by
    rw [← Matrix.mul_assoc, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.smul_apply, smul_eq_mul, Matrix.map_apply]
  have h2 : bk.ev (X ^ m * σ i a b) = (t • adjugate Y * (Y * (σ i).map bk.ev)) a b -
      bk.ev ((l : bk.S) ^ n) * (q * bk.ev (σ i a b)) := by
    rw [h1, map_mul, map_pow, map_pow, map_natCast]
    linear_combination (-(bk.ev (σ i a b))) * hq
  rw [← GlobalTheory.NullOverS.topBasis_c_i₀ TB (X ^ m * σ i a b), h2, map_sub]
  refine Ideal.sub_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right ?_)
  · refine GlobalTheory.NullOverS.topBasis_c_mem_map TB _ _ ?_
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_left _ _ (hc c)
  · rw [TB.c_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_injective_map_integers_Cl_to_wittQuotient : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O), ψ bk.flat ≠ 0 → ¬ IsUnit (ψ bk.flat) → IsAdicComplete (Ideal.span {ψ bk.flat}) O → ∃ θ' : OC l →+* (WittVector l O ⧸ Ideal.span {WittVector.map ψ (bk.ev bk.E)}), (∀ a : Ainf l, θ' (Per.θ l a) = Ideal.Quotient.mk _ (WittVector.map ψ a)) ∧ Function.Injective θ' ∧ IsDomain (WittVector l O ⧸ Ideal.span {WittVector.map ψ (bk.ev bk.E)}) ∧ ∀ a : WittVector l O, ((l : ℕ) : WittVector l O ⧸ Ideal.span {WittVector.map ψ (bk.ev bk.E)}) ∣ Ideal.Quotient.mk _ a → ψ bk.flat ^ bk.Ep.natDegree ∣ a.coeff 0 := by
  first | exact @GlobalTheory.BSP.exists_untilt_map | exact GlobalTheory.BSP.exists_untilt_map | (intros; apply GlobalTheory.BSP.exists_untilt_map <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isFrame_hf : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K))
    (f : Hom bk.prism B), IsFrame bk B (BK.hf f bk.E) (BK.hf f X) := by
  intro l _ K bk B f
  refine ⟨?_, ?_⟩
  · refine (GlobalTheory.T.prism_hom_map_ideal_eq l _ bk.prism B f).symm.trans ?_
    change (Ideal.span {bk.E}).map (BK.hf f) = _
    rw [Ideal.map_span, Set.image_singleton]
  · apply f.f_str
    change Ideal.Quotient.mk (Ideal.span {bk.E}) X = bk.str.toRingHom (bk.str.symm _)
    simp

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (f : Hom bk.prism B),
    IsFrame bk B (BK.hf (bk := bk) f bk.E) (BK.hf (bk := bk) f X) := by
  intro l _ K bk B f
  have hI : bk.prism.I.map f.f = B.I :=
    GlobalTheory.T.prism_hom_map_ideal_eq l _ bk.prism B f
  refine ⟨hI.symm.trans ?_, ?_⟩
  · change (Ideal.span {bk.E}).map (BK.hf (bk := bk) f) = _
    rw [Ideal.map_span, Set.image_singleton]
  · apply f.f_str
    change Ideal.Quotient.mk (Ideal.span {bk.E}) X = bk.str.toRingHom (bk.str.symm _)
    simp
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_galois_moves_flat_by_unit_root : ∀ (l : ℕ) [Fact l.Prime], (∀ (x : ℂ_[l]) (m : ℕ), 0 < m → x ^ m = 1 → ∃ z : Om l, (z : ℂ_[l]) = x) → ∀ (K : FinExt l) (bk : BK K) (e : OCb l), e.untilt = 1 → ∃ g : ↥(GK K), Per.σF (g : GQ l) bk.flat = e * bk.flat := by
  first | exact @GlobalTheory.BSP.galois_moves_flat_by_unit_root | exact GlobalTheory.BSP.galois_moves_flat_by_unit_root | (intros; apply GlobalTheory.BSP.galois_moves_flat_by_unit_root; all_goals assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ ι : Type, Nonempty (TopBasis bk.ev bk.J ι) := by
  first | exact @GlobalTheory.BSP.AinfTopBasis.main | exact GlobalTheory.BSP.AinfTopBasis.main | (intros; apply GlobalTheory.BSP.AinfTopBasis.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.ainf_envelope_mod_prime_properties : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)), (∀ x : En.Q.A, ((l : ℕ) : En.Q.A) * x = 0 → x = 0) ∧ (∀ x : En.Q.A, ((l : ℕ) : En.Q.A) ∣ En.inl.f (bk.ev X) * x → ((l : ℕ) : En.Q.A) ∣ x) ∧ ∀ x : En.Q.A, (∀ m : ℕ, ∃ z, ((l : ℕ) : En.Q.A) ∣ x - En.inl.f (bk.ev X) ^ m * z) → ((l : ℕ) : En.Q.A) ∣ x := by
  first | exact @GlobalTheory.BSP.env_ainf_mod | exact GlobalTheory.BSP.env_ainf_mod | (intros; apply GlobalTheory.BSP.env_ainf_mod <;> assumption)
end
