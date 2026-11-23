module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle260
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle258
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle618
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle548
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle292
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle452
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle621
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleCoboundaryCommaLocalBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle619
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle155
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle622
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle451
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle603
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle605
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle606
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle607
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle137

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CechDR

open FormExt FormExtJ

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

theorem pairRes_bijective_two {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X)
    (s' : X' ⟶ Sp R') : Function.Bijective (pullHyp2 (pairRes φ s')) := by
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s'
  have hcov := _root_.GlobalTheory.CechDR.pair_cover_affine φ s'
  have hdir := _root_.GlobalTheory.CechDR.exists_pair_below_two φ s'

  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s') (pairFst φ) H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s') (pairFst φ) H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s') (pairFst φ) H hcov hdir
  have hv2 := GlobalTheory.T.twoCocycle_coboundary_of_basisFunctor (OAff s') (pairFst φ) H hcov hdir

  have hs1 := _root_.GlobalTheory.CechDR.form_eq_zero_of_basis_cover s' (pairFst φ) hcov
  have hg1 := _root_.GlobalTheory.CechDR.FormExt.glue_one_forms s' (pairFst φ) hcov hdir
  have unitE : ∀ {S S' : AffOp X'} (u : S ⟶ S') (b : (OAff s').obj S),
      IsUnit (mp (omExt (OAff s')) u (TrivSqZeroExt.inl b)) → IsUnit (mp (OAff s') u b) :=
    fun u b h ↦ ((isUnit_mp_omExt_iff (OAff s') u _).1 h)
  have HE := hasLoc_omExt (OAff s') H
  have hcovE : ∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (omExt (OAff s')).obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S),
        IsUnit (mp (omExt (OAff s')) u (b i)) →
          ∃ (t : (Pair φ)ᵒᵖ) (v : T ⟶ (pairFst φ).obj t) (w : (pairFst φ).obj t ⟶ S), v ≫ w = u :=
    fun T ↦ by
      obtain ⟨n, b, hb, h⟩ := hcov T
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), span_inl_eq_top (OAff s') hb,
        fun i S u hu ↦ h i S u (unitE u _ hu)⟩
  have hdirE : ∀ (t₁ t₂ : (Pair φ)ᵒᵖ) (S : AffOp X'), ((pairFst φ).obj t₁ ⟶ S) →
      ((pairFst φ).obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (omExt (OAff s')).obj S),
        Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : AffOp X') (u : S ⟶ S'),
          IsUnit (mp (omExt (OAff s')) u (b i)) →
            ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty ((pairFst φ).obj t₃ ⟶ S') :=
    fun t₁ t₂ S a₁ a₂ ↦ by
      obtain ⟨n, b, hb, h⟩ := hdir t₁ t₂ S a₁ a₂
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), span_inl_eq_top (OAff s') hb,
        fun i S' u hu ↦ h i S' u (unitE u _ hu)⟩
  have hsE := _root_.GlobalTheory.sep_of_factoring_cover (omExt (OAff s')) (pairFst φ) HE hcovE
  have hgE := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (omExt (OAff s')) (pairFst φ) HE hcovE hdirE
  have hvE := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (omExt (OAff s')) (pairFst φ) HE hcovE hdirE

  have hcovJ : ∀ j : ℕ, ∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (omjExt (OAff s') j).obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S),
        IsUnit (mp (omjExt (OAff s') j) u (b i)) →
          ∃ (t : (Pair φ)ᵒᵖ) (v : T ⟶ (pairFst φ).obj t) (w : (pairFst φ).obj t ⟶ S), v ≫ w = u :=
    fun j T ↦ by
      obtain ⟨n, b, hb, h⟩ := hcov T
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), span_inlJ_eq_top (OAff s') j hb,
        fun i S u hu ↦ h i S u ((isUnit_mp_omjExt_iff (OAff s') j u _).1 hu)⟩
  have hdirJ : ∀ j : ℕ, ∀ (t₁ t₂ : (Pair φ)ᵒᵖ) (S : AffOp X'), ((pairFst φ).obj t₁ ⟶ S) →
      ((pairFst φ).obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (omjExt (OAff s') j).obj S),
        Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : AffOp X') (u : S ⟶ S'),
          IsUnit (mp (omjExt (OAff s') j) u (b i)) →
            ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty ((pairFst φ).obj t₃ ⟶ S') :=
    fun j t₁ t₂ S a₁ a₂ ↦ by
      obtain ⟨n, b, hb, h⟩ := hdir t₁ t₂ S a₁ a₂
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), span_inlJ_eq_top (OAff s') j hb,
        fun i S' u hu ↦ h i S' u ((isUnit_mp_omjExt_iff (OAff s') j u _).1 hu)⟩
  have hsJ := fun j ↦ _root_.GlobalTheory.sep_of_factoring_cover (omjExt (OAff s') j) (pairFst φ)
    (GlobalTheory.T.hasLocalisationAtElements_trivSqZeroExtForms (OAff s') j H) (hcovJ j)
  have hgJ := fun j ↦ _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (omjExt (OAff s') j) (pairFst φ)
    (GlobalTheory.T.hasLocalisationAtElements_trivSqZeroExtForms (OAff s') j H) (hcovJ j) (hdirJ j)
  have hs3 : ∀ (T : AffOp X') (x : Om R' ((OAff s').obj T) 3),
      (∀ t (u : T ⟶ (pairFst φ).obj t), pOm (OAff s') 3 u x = 0) → x = 0 := by
    intro T x hx
    have h0 : (TrivSqZeroExt.inr x : (omjExt (OAff s') 3).obj T) = 0 :=
      hsJ 3 T _ fun t u ↦ (mp_omjExt_inr (OAff s') 3 u x).trans (by rw [hx t u]; exact TrivSqZeroExt.inr_zero _)
    simpa using congrArg TrivSqZeroExt.snd h0

  have b1 : Function.Bijective (pairRes φ s').pull1 :=
    ⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg,
      _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩
  have bg := _root_.GlobalTheory.restrict_glob1_bijective _ _ hs1 hg1
  have hs2 := _root_.GlobalTheory.CechDR.twoForm_sep_of_basis s' (pairFst φ) hcov
  refine ⟨GlobalTheory.T.comma_first_order_cocycle_lift _ _ (GlobalTheory.T.comma_descent_injective _ _ hs hg hv) b1.2
      (_root_.GlobalTheory.cocycle_one_forms_coboundary_of_restrict _ _ hs1 hg1) bg.2 hs2,
    GlobalTheory.T.comma_second_order_cocycle_lift _ _ (GlobalTheory.T.comma_descent_restriction_equiv _ _ hs hg hv hv2)
      (GlobalTheory.T.oneForms_twoCocycle_coboundary_of_restrict _ _ (GlobalTheory.T.comma_descent_injective _ _ hsE hgE hvE))
      (GlobalTheory.T.exists_oneForms_cocycle_restrict_sub_coboundary _ _ (_root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hsE hgE hvE))
      (GlobalTheory.T.higherForms_oneCocycle_coboundary_of_restrict _ _ 2 (_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ (hsJ 2) (hgJ 2)))
      (GlobalTheory.T.compatible_higherForms_extend_along_functor _ _ 2 (hsJ 2) (hgJ 2)) hs3⟩

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ)

theorem existsUnique_isPull2 (c : HH2 s) : ∃! c', IsPull2 h c c' := by
  obtain ⟨c', hc, hu⟩ := (pairRes_bijective_two φ s').existsUnique (pullHyp2 (pairPull h) c)
  exact ⟨c', hc.symm, fun y hy ↦ hu y hy.symm⟩

def pairResEquiv2 (φ : X' ⟶ X) (s' : X' ⟶ Sp R') : HH2 s' ≃ₗ[R'] Hyp2 (OPair φ s') :=
  LinearEquiv.ofBijective (pullHyp2 (pairRes φ s')) (pairRes_bijective_two φ s')

def pullHH2 : HH2 s →ₛₗ[σ] HH2 s' :=
  (pairResEquiv2 φ s').symm.toLinearMap.comp (pullHyp2 (pairPull h))

theorem isPull2_pullHH2 (c : HH2 s) : IsPull2 h c (pullHH2 h c) :=
  ((pairResEquiv2 φ s').apply_symm_apply _).symm

theorem IsPull2.eq_pullHH2 {c : HH2 s} {c' : HH2 s'} (e : IsPull2 h c c') : c' = pullHH2 h c :=
  (existsUnique_isPull2 h c).unique e (isPull2_pullHH2 h c)

end GlobalTheory.CechDR
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.KatzCongr

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

def coeffIdeal (τ : Type) (J : Ideal B) : Ideal (MvPowerSeries τ B) where
  carrier := {w | ∀ α, coeff α w ∈ J}
  add_mem' ha hb α := by rw [map_add (f := _)]; exact J.add_mem (ha α) (hb α)
  zero_mem' α := by rw [map_zero]; exact J.zero_mem
  smul_mem' c x hx α := by
    classical
    rw [smul_eq_mul, coeff_mul]
    exact J.sum_mem fun _ _ => J.mul_mem_left _ (hx _)

def scaledIdeal (τ : Type) (K : Ideal B) (c : Q) : Ideal (MvPowerSeries τ B) where
  carrier := {x | ∀ γ, ∃ b ∈ K, c * algebraMap B Q (coeff γ x) = algebraMap B Q b}
  add_mem' {x y} hx hy γ := by
    obtain ⟨a, ha, ea⟩ := hx γ
    obtain ⟨b, hb, eb⟩ := hy γ
    exact ⟨a + b, K.add_mem ha hb, by rw [map_add (f := _), map_add (f := _), mul_add, ea, eb, map_add (f := _)]⟩
  zero_mem' γ := ⟨0, K.zero_mem, by simp⟩
  smul_mem' r x hx γ := by
    classical

    rw [smul_eq_mul, coeff_mul, map_sum, Finset.mul_sum]
    have key : ∀ q ∈ Finset.HasAntidiagonal.antidiagonal γ, ∃ b ∈ K,
        c * algebraMap B Q (coeff q.1 r * coeff q.2 x) = algebraMap B Q b := by
      intro q _
      obtain ⟨b, hb, eb⟩ := hx q.2
      exact ⟨coeff q.1 r * b, K.mul_mem_left _ hb, by rw [map_mul, map_mul, ← eb]; ring⟩
    choose! g hg eg using key
    exact ⟨∑ q ∈ Finset.HasAntidiagonal.antidiagonal γ, g q, K.sum_mem hg, by

      rw [map_sum]; exact Finset.sum_congr rfl eg⟩

end GlobalTheory.KatzCongr

namespace GlobalTheory.KatzCongr

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {τ : Type} {J : Ideal B}

theorem pow_add_sub_pow
    (hdp : ∀ w ∈ coeffIdeal τ J, ∀ n : ℕ, 0 < n → ∃ y ∈ coeffIdeal τ J, w ^ n = (n.factorial : MvPowerSeries τ B) * y)
    (v w : MvPowerSeries τ B) (hw : w ∈ coeffIdeal τ J) (n : ℕ) :
    ∃ z ∈ coeffIdeal τ J, (v + w) ^ n - v ^ n = (n : MvPowerSeries τ B) * z := by
  cases n with
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | succ m =>
    choose! y hy ey using fun k (hk : 0 < k) => hdp w hw k hk
    refine ⟨∑ k ∈ Finset.range (m + 1), (m.descFactorial k : MvPowerSeries τ B) * y (k + 1) * v ^ (m - k),
      Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (hy _ (Nat.succ_pos k))), ?_⟩
    rw [add_comm v w, add_pow, Finset.sum_range_succ', Finset.mul_sum]
    simp only [pow_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul, add_sub_cancel_right]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h : (((k + 1).factorial * (m + 1).choose (k + 1) : ℕ) : MvPowerSeries τ B) =
        ((m + 1 : ℕ) : MvPowerSeries τ B) * (m.descFactorial k : ℕ) := by
      rw [← Nat.descFactorial_eq_factorial_mul_choose, Nat.succ_descFactorial_succ, Nat.cast_mul]
    rw [ey (k + 1) (Nat.succ_pos k), Nat.add_sub_add_right]
    push_cast at h ⊢
    linear_combination (y (k + 1) * v ^ (m - k)) * h

theorem prod_sub_mem {σ : Type} (K : Ideal B) (c : Q) (α : σ →₀ ℕ) (u v : σ → MvPowerSeries τ B)
    (hdp : ∀ w ∈ coeffIdeal τ J, ∀ n : ℕ, 0 < n → ∃ y ∈ coeffIdeal τ J, w ^ n = (n.factorial : MvPowerSeries τ B) * y)
    (huv : ∀ i, u i - v i ∈ coeffIdeal τ J)
    (hsc : ∀ i, ∀ z ∈ coeffIdeal τ J, (α i : MvPowerSeries τ B) * z ∈ scaledIdeal τ K c)
    (s : Finset σ) : ∏ i ∈ s, u i ^ α i - ∏ i ∈ s, v i ^ α i ∈ scaledIdeal τ K c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    obtain ⟨z, hz, ez⟩ := pow_add_sub_pow hdp (v a) (u a - v a) (huv a) (α a)
    rw [add_sub_cancel] at ez
    have e : u a ^ α a * ∏ i ∈ s, u i ^ α i - v a ^ α a * ∏ i ∈ s, v i ^ α i =
        u a ^ α a * (∏ i ∈ s, u i ^ α i - ∏ i ∈ s, v i ^ α i) +
          (u a ^ α a - v a ^ α a) * ∏ i ∈ s, v i ^ α i := by ring
    rw [e, ez]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ih) (Ideal.mul_mem_right _ _ (hsc a z hz))

end GlobalTheory.KatzCongr

namespace GlobalTheory.KatzCongr

theorem subst_sub_in : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ J : Ideal B, (∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) → ∀ (σ τ : Type) [Fintype σ] (N : Ideal B) (f : MvPowerSeries σ Q) (u v : σ → MvPowerSeries τ B), DIn N f → (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ i α, coeff α (u i - v i) ∈ J) →
    In (J * N) (MvPowerSeries.subst (σ := σ) (τ := τ) (R := Q) (S := Q) (up Q u) f -
      MvPowerSeries.subst (σ := σ) (τ := τ) (R := Q) (S := Q) (up Q v) f) := by
  intro p _ B O Q _ _ _ _ θ hF J hJ σ τ _ N f u v hf hu hv huv
  classical
  have hdp : ∀ w ∈ coeffIdeal τ J, ∀ n : ℕ, 0 < n →
      ∃ y ∈ coeffIdeal τ J, w ^ n = (n.factorial : MvPowerSeries τ B) * y := fun w hw n hn => by
    obtain ⟨y, hy, e⟩ := GlobalTheory.T.mvPowerSeries_coeffsInIdeal_pow_eq_factorial_mul p B O Q θ hF J hJ τ w hw n hn
    exact ⟨y, hy, e⟩
  have hsU : HasSubst (up Q u) := hasSubst_of_constantCoeff_zero fun i => by simp [up, hu i]
  have hsV : HasSubst (up Q v) := hasSubst_of_constantCoeff_zero fun i => by simp [up, hv i]
  intro γ
  rw [map_sub, coeff_subst hsU, coeff_subst hsV,
    ← finsum_sub_distrib (coeff_subst_finite hsU f γ) (coeff_subst_finite hsV f γ)]
  refine finsum_induction (fun q => ∃ b ∈ J * N, q = algebraMap B Q b) ⟨0, Submodule.zero_mem _, by simp⟩
    (fun x y ⟨a, ha, ea⟩ ⟨b, hb, eb⟩ => ⟨a + b, Submodule.add_mem _ ha hb, by rw [ea, eb, map_add (f := _)]⟩)
    (fun d => ?_)
  have hprod : ∀ w : σ → MvPowerSeries τ B,
      (d.prod fun s e => up Q w s ^ e) = map (algebraMap B Q) (∏ i, w i ^ d i) := by
    intro w
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), map_prod]
    simp [up, map_pow]
  have hsc : ∀ i, ∀ z ∈ coeffIdeal τ J,
      (d i : MvPowerSeries τ B) * z ∈ scaledIdeal τ (J * N) (coeff d f) := by
    intro i z hz γ'
    obtain ⟨b, hb, eb⟩ := hf d i
    refine ⟨coeff γ' z * b, Ideal.mul_mem_mul (hz γ') hb, ?_⟩
    rw [show ((d i : ℕ) : MvPowerSeries τ B) = C (d i : B) from (map_natCast C _).symm, coeff_C_mul,
      map_mul, map_mul, ← eb, map_natCast]
    ring
  have hmem := prod_sub_mem (J := J) (J * N) (coeff d f) d u v hdp (fun i α => huv i α) hsc Finset.univ
  obtain ⟨b, hb, eb⟩ := hmem γ
  refine ⟨b, hb, ?_⟩
  rw [hprod, hprod, smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub (coeff γ), ← map_sub, coeff_map, ← eb]

end GlobalTheory.KatzCongr
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

namespace GlobalTheory.NMulHom

theorem isHom_nmul : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
    IsLaw μ → ∀ n, IsHom μ μ (nmul μ n) :=
  GlobalTheory.NMulEndo.isHom_nmul

end GlobalTheory.NMulHom
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

theorem _root_.GlobalTheory.T.isHom_nmul_of_isLaw : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ k : ℕ, IsHom μ μ (nmul μ k) := by
  first | exact @GlobalTheory.NMulEndo.isHom_nmul | exact GlobalTheory.NMulEndo.isHom_nmul | (intros; apply GlobalTheory.NMulEndo.isHom_nmul <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory

theorem constantCoeff_eq_zero_of_eval_eq_comul : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [IsAdicComplete (Ideal.span {(p : O)}) O] {d : ℕ} (x : Fin d → A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, Coalgebra.counit (R := O) (x i) = 0) → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂ → (∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) → ∀ i, constantCoeff (μ i) = 0 := by
  intro p O A _ _ _ _ d x E₂ μ hx hE hμ i
  let φ : A ⊗[O] A →ₐ[O] O := Algebra.TensorProduct.lift (Bialgebra.counitAlgHom O A)
    (Bialgebra.counitAlgHom O A) (fun _ _ => Commute.all _ _)
  have hφ : ∀ a b : A, φ (a ⊗ₜ[O] b) = Coalgebra.counit (R := O) a * Coalgebra.counit (R := O) b := by
    intro a b
    simp [φ, Algebra.TensorProduct.lift_tmul, Bialgebra.counitAlgHom_apply]

  have hφc : ∀ a : A, φ (Coalgebra.comul (R := O) a) = Coalgebra.counit (R := O) a := by
    intro a
    have hL : (φ.toLinearMap : A ⊗[O] A →ₗ[O] O) =
        (LinearMap.mul' O O) ∘ₗ (LinearMap.lTensor O (Coalgebra.counit (R := O) (A := A))) ∘ₗ
          (LinearMap.rTensor A (Coalgebra.counit (R := O) (A := A))) := by
      apply TensorProduct.ext'
      intro a b
      simp [hφ]
    have := LinearMap.congr_fun hL (Coalgebra.comul (R := O) a)
    simp only [AlgHom.toLinearMap_apply, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul,
      LinearMap.lTensor_tmul, LinearMap.mul'_apply, one_mul] at this
    exact this
  let c : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] O :=
    { (constantCoeff : MvPowerSeries (Fin d ⊕ Fin d) O →+* O) with
      commutes' := fun r => by
        first
        | exact constantCoeff_C r
        | (rw [MvPowerSeries.algebraMap_apply]; simp)
        | (show constantCoeff (C r) = r; simp)
        | simp [MvPowerSeries.algebraMap_apply'] }
  have hc : ∀ f, c f = constantCoeff f := fun _ => rfl
  have hnil : ∀ j : Fin d ⊕ Fin d, ∃ N : ℕ, (p : O) ∣ (fun _ => (0 : O)) j ^ N :=
    fun _ => ⟨1, by simp⟩
  obtain ⟨⟨E, _, huniq⟩, _⟩ := GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p O O (Fin d ⊕ Fin d) (fun _ => (0 : O)) hnil
  have h1 : IsEval p (fun _ => (0 : O)) (φ.comp E₂) := by
    refine ⟨?_, ?_⟩
    · intro j
      rw [AlgHom.comp_apply, hE.1 j]
      cases j with
      | inl k => simp [hφ, hx]
      | inr k => simp [hφ, hx]
    · intro m
      obtain ⟨N, hN⟩ := hE.2 m
      refine ⟨N, fun f hf => ?_⟩
      obtain ⟨a, ha⟩ := hN f hf
      refine ⟨φ a, ?_⟩
      rw [AlgHom.comp_apply, ha, map_mul, map_pow, map_natCast]
  have h2 : IsEval p (fun _ => (0 : O)) c := by
    refine ⟨fun j => by simp [hc], fun m => ⟨1, fun f hf => ?_⟩⟩
    have : constantCoeff f = 0 := by
      have := hf 0 (by simp)
      simpa [coeff_zero_eq_constantCoeff_apply] using this
    rw [hc, this]; exact dvd_zero _
  have e1 := huniq _ h1
  have e2 := huniq _ h2
  have := congrArg (fun F : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] O => F (μ i)) (e1.trans e2.symm)
  simp only [AlgHom.comp_apply, hμ, hφc, hx, hc] at this
  exact this.symm

end GlobalTheory
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.formalGroupLawNatMultiple_add_mul_laws : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ m n : ℕ, (∀ i, constantCoeff (nmul μ n i) = 0) ∧ nmul μ (m + n) = op μ (nmul μ m) (nmul μ n) ∧ (∀ i, nmul μ (m * n) i = subst (nmul μ n) (nmul μ m i)) ∧ nmul μ 1 = fun i => X i := by
  first | exact @GlobalTheory.NMul.nmul_laws | exact GlobalTheory.NMul.nmul_laws | (intros; apply GlobalTheory.NMul.nmul_laws <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.coboundary_degree_part_cocycle_mod_ideal : ∀ (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (m : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) Q), (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < m → ∃ b ∈ N, coeff α c = algebraMap B Q b) → In N (cob2 (up Q μ) c) → ∀ n : Fin d →₀ ℕ, n.degree = m → ∀ a b : Fin d →₀ ℕ, a ≠ 0 → b ≠ 0 → a + b ≤ n → a + b ≠ n → ∃ r ∈ N, (∏ i, Nat.choose ((a + b) i) (a i) : Q) * coeff (Finsupp.sumElim (a + b) (n - (a + b))) c - (∏ i, Nat.choose ((n - a) i) (b i) : Q) * coeff (Finsupp.sumElim a (n - a)) c = algebraMap B Q r := by
  first | exact @GlobalTheory.CobRel.cocycle_rel_mod | exact GlobalTheory.CobRel.cocycle_rel_mod | (intros; apply GlobalTheory.CobRel.cocycle_rel_mod <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

theorem _root_.GlobalTheory.T.eval_swap_eq' : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [Coalgebra.IsCocomm O A] [IsAdicComplete (Ideal.span {(p : A ⊗[O] A)}) (A ⊗[O] A)] {d : ℕ} (x : Fin d → A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂ → (∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) → ∀ i, E₂ (swap (μ i)) = E₂ (μ i) := by
  first | exact @GlobalTheory.CommSwap.eval_swap_eq | exact GlobalTheory.CommSwap.eval_swap_eq | (intros; apply GlobalTheory.CommSwap.eval_swap_eq <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

theorem _root_.GlobalTheory.T.formalChart_groupLaw_eval_right_unit : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [IsAdicComplete (Ideal.span {(p : A)}) A] {d : ℕ} (x : Fin d → A) (ev : MvPowerSeries (Fin d) O →ₐ[O] A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) → (∀ i, Coalgebra.counit (R := O) (x i) = 0) → IsEval p x ev → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂ → (∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) → ∀ i, ev (op μ (fun i => (X i : MvPowerSeries (Fin d) O)) (fun _ => 0) i) = x i := by
  first | exact @GlobalTheory.chart_unit | exact GlobalTheory.chart_unit | (intros; apply GlobalTheory.chart_unit <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.IntAdd

theorem formalGroupLawCoboundaryOne_map_coefficients {R S : Type} [CommRing R] [CommRing S] {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (h : ∀ i, constantCoeff (μ i) = 0) (r : R →+* S)
    (f : MvPowerSeries (Fin d) R) :
    map r (cob1 μ f) = cob1 (fun i => map r (μ i)) (map r f) := by
  unfold cob1 inL inR
  rw [map_sub, map_sub, map_subst (hasSubst_of_constantCoeff_zero h),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  simp only [map_X]

theorem eq_zero_of_cob1_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ s : MvPowerSeries (Fin d) O, cob1 (up E c.μ) (map (algebraMap O E) s) = 0 → s = 0 := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ G d c E _ _ hF s hs
  have h0 : cob1 c.μ s = 0 := by
    have hm := formalGroupLawCoboundaryOne_map_coefficients c.μ c.isLaw.const (algebraMap O E) s
    have hup : (fun i => map (algebraMap O E) (c.μ i)) = up E c.μ := rfl
    rw [hup, hs] at hm
    ext α
    apply hF.inj
    have := congrArg (coeff α) hm
    rw [coeff_map] at this
    rw [this]; simp
  have hp : (p : O) ≠ 0 := by
    intro h
    exact one_ne_zero (hF.sat 1 (by rw [h, zero_mul]))
  have hev : ∀ n, c.ev n s = 0 := fun n =>
    G.eq_zero_of_cobOne_eq_zero hp n (by
      rw [← (Chart.ev₂_eval p O G d c n s).2.2.2, h0, map_zero])
  ext α
  rw [coeff_zero]
  refine hF.eq_zero_of_forall_pow_dvd fun m => ?_
  obtain ⟨n, hn⟩ := c.ker m (α.degree + 1)
  exact hn s (hev n) α (Nat.lt_succ_self _)

end GlobalTheory.QLog.IntAdd
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
open TensorProduct


theorem _root_.GlobalTheory.T.comul_chart_sub_subst_mem_p_smul : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ) (F : MvPowerSeries (Fin d) O), ∃ t : G.A n ⊗[O] G.A n, Coalgebra.comul (R := O) (c.ev n F) - c.ev₂ n (subst c.μ F) = (p : O) • t := by
  first | exact @GlobalTheory.comul_ev_sub_ev₂_subst_mem | exact GlobalTheory.comul_ev_sub_ev₂_subst_mem | (intros; apply GlobalTheory.comul_ev_sub_ev₂_subst_mem <;> assumption)
end
