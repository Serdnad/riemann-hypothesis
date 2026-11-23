module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.InfGLScalar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.AdelicLiftHasModerateGrowth
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.GaussSumBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.UniformSpace.Uniformizable
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem lift_isHol : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ), Even k →
    ∀ (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ), Sys k Ψ → ∃ φ : TR.Sm F 2, IsLift k Ψ φ.1 ∧ IsHol k (fun _ => 0) 1 φ := by
  intro F _ _ _ k hk Ψ hΨ
  obtain ⟨φ₀, hL, hR, hZ⟩ := GlobalTheory.T.exists_adelic_lift_of_hilbert_system F k hk Ψ hΨ
  obtain ⟨hsm, hlie⟩ := GlobalTheory.T.adelic_lift_mem_smooth_killed_by_lowering F k Ψ φ₀ hΨ.hol hL
  let φ : TR.Sm F 2 := ⟨φ₀, hsm⟩
  have hfix : ∀ u ∈ KLev F 2 1, TR.finRep F 2 u φ = φ := fun u hu =>
    Subtype.ext (funext fun g => hR u hu g)
  have hlev : IsOpen {u | TR.finRep F 2 u φ = φ} := by
    let H : Subgroup (GL (Fin 2) (Af F)) :=
      { carrier := {u | TR.finRep F 2 u φ = φ}
        one_mem' := by simp
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_mul, Module.End.mul_apply, hb, ha]
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_setOf_eq] at ha ⊢
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    exact Subgroup.isOpen_mono (H₁ := KLev F 2 1) (H₂ := H) hfix (isOpen_KLev (F := F) (n := 2) (M := 1) le_rfl)
  have hcen : ∀ (z : Ideles F) (g : GA F 2),
      φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = (((1 : HChar F).1 z : ℂˣ) : ℂ) * φ.1 g := by
    intro z g
    simp only [OneMemClass.coe_one, MonoidHom.one_apply, Units.val_one, one_mul]
    exact hZ z g
  have haut : TR.IsAutForm φ :=
    ⟨hL.1, hlev, GlobalTheory.T.adelic_lift_kFinite_of_isLift F k Ψ φ hL,
      UpperTheory.V.Af.Nf.zFin F k 1 IsOfFinOrder.one φ hcen (fun v => (hlie v).1) (fun v => (hlie v).2),
      GlobalTheory.T.adelic_lift_has_moderate_growth F k Ψ φ₀ hΨ.gr hL⟩
  refine ⟨φ, hL, haut, fun w u hu => hfix _ ((GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization F).2.2.1 w u hu), hcen, fun v => (hlie v).1,
    fun v => (hlie v).2⟩

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_isHol_adelic_lift_of_even_weight_system : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ), Even k → ∀ (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ), Sys k Ψ → ∃ φ : TR.Sm F 2, IsLift k Ψ φ.1 ∧ IsHol k (fun _ => 0) 1 φ := by
  first | exact @GlobalTheory.HilbertThetaSeries.lift_isHol | exact GlobalTheory.HilbertThetaSeries.lift_isHol | (intros; apply GlobalTheory.HilbertThetaSeries.lift_isHol <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem small_filtration : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (r s : ℝ) (f g : Hn F → ℂ) (c : ℂ), Small ι r f → Small ι s g → Small ι (max r s) (f + g) ∧ Small ι (r * s) (f * g) ∧ Small ι (‖ι.symm c‖ * r) (c • f) ∧ (r ≤ s → Small ι s f) ∧ 0 ≤ r ∧ Small ι ‖ι.symm c‖ (fun _ : Hn F => c) := by
  intro F _ _ _ p _ ι r s f g c hf hg
  obtain ⟨a, ha, har⟩ := hf
  obtain ⟨b, hb, hbs⟩ := hg
  have hr : 0 ≤ r := (norm_nonneg _).trans (har 0)
  have hs : 0 ≤ s := (norm_nonneg _).trans (hbs 0)
  obtain ⟨h1, h2, -, h4⟩ := GlobalTheory.T.qExpansion_linear_combination F f g a b c ha hb
  refine ⟨⟨a + b, h1, fun ξ => ?_⟩, ?_, ⟨c • a, h2, fun ξ => ?_⟩, fun hrs => ⟨a, ha, fun ξ => (har ξ).trans hrs⟩, hr,
    ⟨_, h4, fun ξ => ?_⟩⟩
  · rw [Pi.add_apply, map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (har ξ) (hbs ξ))
  · obtain ⟨d, hd, hds⟩ := GlobalTheory.T.qExpansion_mul_finite_convolution F f g a b ha hb
    refine ⟨d, hd, fun ξ => ?_⟩
    obtain ⟨t, ht⟩ := hds ξ

    rw [ht, map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hr hs) fun η _ => ?_
    rw [map_mul, norm_mul]
    exact mul_le_mul (har η) (hbs _) (norm_nonneg _) hr
  · rw [Pi.smul_apply, smul_eq_mul, map_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (har ξ) (norm_nonneg _)
  · split_ifs
    · exact le_rfl
    · rw [map_zero, norm_zero]; exact norm_nonneg _

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.hilbertQExp_padicBound_algebra_properties : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (r s : ℝ) (f g : Hn F → ℂ) (c : ℂ), Small ι r f → Small ι s g → Small ι (max r s) (f + g) ∧ Small ι (r * s) (f * g) ∧ Small ι (‖ι.symm c‖ * r) (c • f) ∧ (r ≤ s → Small ι s f) ∧ 0 ≤ r ∧ Small ι ‖ι.symm c‖ (fun _ : Hn F => c) := by
  first | exact @GlobalTheory.HilbertThetaSeries.small_filtration | exact GlobalTheory.HilbertThetaSeries.small_filtration | (intros; apply GlobalTheory.HilbertThetaSeries.small_filtration <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem GlobalTheory.HilbertThetaSeries.th_expansion : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ (a : F) (Φ : (κ → F) → ℂ) (B : ℝ), (∀ x, Φ x ≠ 0 → x ∈ aL κ a) → (∀ x, ‖Φ x‖ ≤ B) → (∀ z, Summable fun x => Φ x * ez (QF G x) z) ∧ Hol (th G Φ) ∧ Gr (th G Φ) ∧ HasQ (th G Φ) (fun ξ => ∑ᶠ x ∈ {x : κ → F | x ∈ aL κ a ∧ QF G x = ξ}, Φ x) := by
  intro F _ _ _ κ _ _ G hG a Φ B hsupp hB
  obtain ⟨C, A, hCA⟩ := GlobalTheory.HilbertThetaSeries.GaussSum.gauss_sum_bound F κ G hG a
  obtain ⟨hTP, -, hfin⟩ := GlobalTheory.HilbertThetaSeries.qf_totPos_proper F κ G hG
  obtain ⟨-, hsc, -, hint, -, haL, -⟩ := GlobalTheory.HilbertThetaSeries.formLatticeProps F κ G hG
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hle : ∀ z (x : κ → F), ‖Φ x * ez (QF G x) z‖ ≤ B * ‖ez (QF G x) z‖ := fun z x => by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
  have hsub : ∀ z, Summable fun x : aL κ a => ‖Φ x * ez (QF G (x : κ → F)) z‖ := fun z =>
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => hle z x) (((hCA z).1).mul_left B)
  have hzero : ∀ x, x ∉ aL κ a → Φ x = 0 := fun x hx => by
    by_contra h; exact hx (hsupp x h)
  have hsumN : ∀ z, Summable fun x : κ → F => ‖Φ x * ez (QF G x) z‖ := by
    intro z
    refine (Function.Injective.summable_iff (f := fun x : κ → F => ‖Φ x * ez (QF G x) z‖)
      (g := ((↑) : aL κ a → κ → F)) Subtype.val_injective ?_).1 (hsub z)
    intro x hx
    have : x ∉ aL κ a := fun h => hx ⟨⟨x, h⟩, rfl⟩
    simp [hzero x this]
  have hsum : ∀ z, Summable fun x => Φ x * ez (QF G x) z := fun z => (hsumN z).of_norm
  have hgr : Gr (th G Φ) := by
    refine ⟨B * C, A, fun z => ?_⟩
    have e1 : ‖th G Φ z‖ ≤ ∑' x, ‖Φ x * ez (QF G x) z‖ := norm_tsum_le_tsum_norm (hsumN z)
    have e2 : ∑' x, ‖Φ x * ez (QF G x) z‖ = ∑' x : aL κ a, ‖Φ x * ez (QF G (x : κ → F)) z‖ := by
      refine (tsum_subtype_eq_of_support_subset (s := (aL κ a : Set (κ → F))) ?_).symm
      intro x hx
      by_contra h
      exact hx (by simp [hzero x h])
    have e3 : ∑' x : aL κ a, ‖Φ x * ez (QF G (x : κ → F)) z‖ ≤ ∑' x : aL κ a, B * ‖ez (QF G (x : κ → F)) z‖ :=
      Summable.tsum_le_tsum (fun x => hle z x) (hsub z) (((hCA z).1).mul_left B)
    rw [tsum_mul_left] at e3
    calc ‖th G Φ z‖ ≤ _ := e1
      _ = _ := e2
      _ ≤ _ := e3
      _ ≤ B * (C * (∏ v, (1 + ‖(z v : ℂ)‖ ^ 2) / (z v).im) ^ A) := mul_le_mul_of_nonneg_left (hCA z).2 hB0
      _ = _ := by ring
  have hQ : HasQ (th G Φ) (fun ξ => ∑ᶠ x ∈ {x : κ → F | x ∈ aL κ a ∧ QF G x = ξ}, Φ x) := by
    refine ⟨?_, fun z => ?_⟩
    · obtain ⟨y, hy0, hy⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (.of_finite ℚ (a ^ 2))).exists_integral_multiple
      have hya : IsIntegral ℤ ((y.natAbs : F) * a ^ 2) := by
        have hy' : IsIntegral ℤ ((y : F) * a ^ 2) := by rwa [zsmul_eq_mul] at hy
        have hc : ((y.natAbs : ℕ) : F) = (((y.natAbs : ℕ) : ℤ) : F) := (Int.cast_natCast _).symm
        rw [hc]
        rcases Int.natAbs_eq y with h | h
        · rw [← h]; exact hy'
        · have h' : ((y.natAbs : ℕ) : ℤ) = -y := by omega
          rw [h', Int.cast_neg, neg_mul]; exact hy'.neg
      refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, fun ξ hξ => ?_⟩
      obtain ⟨x, ⟨hxa, hxξ⟩, -⟩ : ∃ x ∈ {x : κ → F | x ∈ aL κ a ∧ QF G x = ξ}, Φ x ≠ 0 := by
        by_contra h
        push_neg at h
        apply hξ
        beta_reduce
        rw [finsum_mem_eq_finite_toFinset_sum _ (hfin a ξ)]
        exact Finset.sum_eq_zero fun x hx => h x ((hfin a ξ).mem_toFinset.1 hx)
      obtain ⟨l, hl, rfl⟩ := (haL a x).1 hxa
      subst hxξ
      constructor
      · by_cases hx : a • l = 0
        · left; rw [hx]; simp [QF, BF]
        · right; exact hTP _ hx
      · rw [(hsc a l l).2.1, ← mul_assoc]
        exact hya.mul (hint l hl).1
    · have hfib : ∀ ξ, HasSum (fun c : {x // QF G x = ξ} => Φ c * ez (QF G c) z)
          ((∑ᶠ x ∈ {x : κ → F | x ∈ aL κ a ∧ QF G x = ξ}, Φ x) * ez ξ z) := by
        intro ξ
        have e : (fun c : {x // QF G x = ξ} => Φ c * ez (QF G c) z) = fun c : {x // QF G x = ξ} => Φ c * ez ξ z := by
          funext c; rw [c.2]
        rw [e]
        refine HasSum.mul_right _ ?_
        rw [finsum_mem_eq_finite_toFinset_sum _ (hfin a ξ)]
        have h2 : HasSum (({x | QF G x = ξ} : Set (κ → F)).indicator Φ) (∑ x ∈ (hfin a ξ).toFinset, Φ x) := by
          have h3 : ∑ x ∈ (hfin a ξ).toFinset, Φ x = ∑ x ∈ (hfin a ξ).toFinset, ({x | QF G x = ξ} : Set (κ → F)).indicator Φ x :=
            Finset.sum_congr rfl fun x hx => (Set.indicator_of_mem (show x ∈ ({x | QF G x = ξ} : Set (κ → F)) from ((hfin a ξ).mem_toFinset.1 hx).2) _).symm
          rw [h3]
          refine hasSum_sum_of_ne_finset_zero fun x hx => ?_
          by_cases hq : QF G x = ξ
          · rw [Set.indicator_of_mem (show x ∈ ({x | QF G x = ξ} : Set (κ → F)) from hq)]
            refine hzero x fun hxa => hx ?_
            exact (hfin a ξ).mem_toFinset.2 ⟨hxa, hq⟩
          · exact Set.indicator_of_notMem (show x ∉ ({x | QF G x = ξ} : Set (κ → F)) from hq) _
        exact (hasSum_subtype_iff_indicator (f := Φ) (s := {x | QF G x = ξ})).2 h2
      have hall : HasSum (fun x => Φ x * ez (QF G x) z) (th G Φ z) := (hsum z).hasSum
      rw [← (Equiv.sigmaFiberEquiv (QF G)).hasSum_iff] at hall
      exact hall.sigma hfib
  exact ⟨hsum, GlobalTheory.HilbertThetaSeries.QHol.hol F (th G Φ) _ hQ, hgr, hQ⟩

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.thetaSeries_holomorphic_qExpansion_of_bounded_coeff : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ (a : F) (Φ : (κ → F) → ℂ) (B : ℝ), (∀ x, Φ x ≠ 0 → x ∈ aL κ a) → (∀ x, ‖Φ x‖ ≤ B) → (∀ z, Summable fun x => Φ x * ez (QF G x) z) ∧ Hol (th G Φ) ∧ Gr (th G Φ) ∧ HasQ (th G Φ) (fun ξ => ∑ᶠ x ∈ {x : κ → F | x ∈ aL κ a ∧ QF G x = ξ}, Φ x) := by
  first | exact @GlobalTheory.HilbertThetaSeries.th_expansion | exact GlobalTheory.HilbertThetaSeries.th_expansion | (intros; apply GlobalTheory.HilbertThetaSeries.th_expansion <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.QPow

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {p : ℕ} [Fact p.Prime] {ι : Qbar p ≃+* ℂ}

theorem norm_p (ι : Qbar p ≃+* ℂ) : ‖ι.symm (p : ℂ)‖ = (p : ℝ)⁻¹ := by
  rw [map_natCast]
  have h : ‖(algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]))‖ = ‖(p : ℚ_[p])‖ :=
    PadicAlgCl.norm_extends p _
  rw [map_natCast, Padic.norm_p] at h
  exact h

private theorem hasQ_const (c : ℂ) :
    HasQ (F := F) (fun _ : Hn F => c) (({0} : Set F).indicator fun _ => c) := by
  classical
  refine ⟨⟨1, one_pos, fun ξ hξ => ?_⟩, fun z => ?_⟩
  · have h0 : ξ = 0 := by
      by_contra hne
      exact hξ (by simp [Set.indicator_apply, hne])
    subst h0
    refine ⟨Or.inl rfl, ?_⟩
    rw [mul_zero]
    exact isIntegral_zero
  · have h := hasSum_single
      (f := fun ξ : F => (({0} : Set F).indicator (fun _ => c) ξ) * ez ξ z) 0
      (fun b hb => by simp [Set.indicator_apply, hb])
    convert h using 1
    simp [Set.indicator_apply, ez, reAt]

theorem small_const {r : ℝ} {g : Hn F → ℂ} (h : Small ι r g) (c : ℂ) :
    Small (F := F) ι ‖ι.symm c‖ (fun _ : Hn F => c) := by
  classical
  refine ⟨_, hasQ_const c, fun ξ => ?_⟩
  by_cases hξ : ξ = 0
  · simp [Set.indicator_apply, hξ]
  · simp [Set.indicator_apply, hξ]

theorem small_mono {r s : ℝ} {g : Hn F → ℂ} (h : Small ι r g) (hrs : r ≤ s) : Small ι s g := by
  obtain ⟨a, ha, hb⟩ := h
  exact ⟨a, ha, fun ξ => (hb ξ).trans hrs⟩

private theorem hasQ_add {f g : Hn F → ℂ} {a b : F → ℂ} (hf : HasQ f a) (hg : HasQ g b) :
    HasQ (f + g) (a + b) := by
  obtain ⟨⟨D, hD, hDa⟩, ha⟩ := hf
  obtain ⟨⟨E, hE, hEb⟩, hb⟩ := hg
  refine ⟨⟨D * E, Nat.mul_pos hD hE, fun ξ hξ => ?_⟩, fun z => ?_⟩
  · by_cases h0 : a ξ = 0
    · have hb0 : b ξ ≠ 0 := by
        intro hb0
        apply hξ
        simp [h0, hb0]
      obtain ⟨h1, h2⟩ := hEb ξ hb0
      refine ⟨h1, ?_⟩
      have h3 := (isIntegral_natCast (R := ℤ) (B := F) D).mul h2
      have e : ((D * E : ℕ) : F) * ξ = (D : F) * ((E : F) * ξ) := by
        push_cast
        ring
      rw [e]
      exact h3
    · obtain ⟨h1, h2⟩ := hDa ξ h0
      refine ⟨h1, ?_⟩
      have h3 := (isIntegral_natCast (R := ℤ) (B := F) E).mul h2
      have e : ((D * E : ℕ) : F) * ξ = (E : F) * ((D : F) * ξ) := by
        push_cast
        ring
      rw [e]
      exact h3
  · have h := (ha z).add (hb z)
    simp only [Pi.add_apply, add_mul]
    exact h

theorem small_add {r s : ℝ} {f g : Hn F → ℂ} (hf : Small ι r f) (hg : Small ι s g) : Small ι (max r s) (f + g) := by
  obtain ⟨a, ha, ha'⟩ := hf
  obtain ⟨b, hb, hb'⟩ := hg
  refine ⟨a + b, hasQ_add ha hb, fun ξ => ?_⟩
  rw [Pi.add_apply, map_add (f := _)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (ha' ξ) (hb' ξ))

theorem small_mul {r s : ℝ} {f g : Hn F → ℂ} (hf : Small ι r f) (hg : Small ι s g) : Small ι (r * s) (f * g) := by
  obtain ⟨a, ha, ha'⟩ := hf
  obtain ⟨b, hb, hb'⟩ := hg
  have hr : 0 ≤ r := (norm_nonneg _).trans (ha' 0)
  have hs : 0 ≤ s := (norm_nonneg _).trans (hb' 0)
  obtain ⟨c, hc, hc'⟩ := hasQ_mul F f g a b ha hb
  refine ⟨c, hc, fun ξ => ?_⟩
  obtain ⟨t, ht⟩ := hc' ξ

  rw [ht, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hr hs) fun η _ => ?_
  rw [map_mul, norm_mul]
  exact mul_le_mul (ha' η) (hb' (ξ - η)) (norm_nonneg _) hr

theorem small_nonneg {r : ℝ} {f : Hn F → ℂ} (hf : Small ι r f) : 0 ≤ r := by
  obtain ⟨a, -, hb⟩ := hf
  exact (norm_nonneg _).trans (hb 0)

theorem small_zero {r : ℝ} {f : Hn F → ℂ} (hf : Small ι r f) : Small ι r (0 : Hn F → ℂ) := by
  refine ⟨0, ⟨⟨1, one_pos, fun ξ hξ => (hξ rfl).elim⟩, fun z => ?_⟩, fun ξ => ?_⟩
  · simpa using (hasSum_zero : HasSum (fun _ : F => (0 : ℂ)) 0)
  · simpa using small_nonneg hf

theorem pow_sub_one {r : ℝ} {f : Hn F → ℂ} (h : Small ι r (f - 1)) (hr : r ≤ 1) :
    ∀ m : ℕ, Small ι r (f ^ m - 1) := by
  have hr0 := small_nonneg h
  intro m
  induction m with
  | zero => simpa using small_zero h
  | succ m ih =>
    have e : f ^ (m + 1) - 1 = (f ^ m - 1) * (f - 1) + ((f ^ m - 1) + (f - 1)) := by ring
    rw [e]
    have h1 := small_add (small_mul ih h) (small_add ih h)
    refine small_mono h1 ?_
    rw [max_self]
    exact max_le (mul_le_of_le_one_left hr0 hr) le_rfl

theorem sum_small {r : ℝ} {f : Hn F → ℂ} (h : Small ι r (f - 1)) (hr : r ≤ (p : ℝ)⁻¹) :
    ∀ n : ℕ, Small ι (p : ℝ)⁻¹ (∑ i ∈ Finset.range n, (f ^ i - 1)) := by
  have hp1 : (p : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  have hs : Small ι (p : ℝ)⁻¹ (f - 1) := small_mono h hr
  intro n
  induction n with
  | zero => simpa using small_zero hs
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 := small_add ih (pow_sub_one hs hp1 n)
    rwa [max_self] at h1

theorem pow_p {r : ℝ} {f : Hn F → ℂ} (h : Small ι r (f - 1)) (hr : r ≤ (p : ℝ)⁻¹) :
    Small ι (r * (p : ℝ)⁻¹) (f ^ p - 1) := by
  have key : ∀ x : ℂ, x ^ p - 1 =
      (x - 1) * ∑ i ∈ Finset.range p, (x ^ i - 1) + (p : ℂ) * (x - 1) := by
    intro x
    have hg := geom_sum_mul x p
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    linear_combination (-1 : ℂ) * hg
  have e : f ^ p - 1 = (f - 1) * ∑ i ∈ Finset.range p, (f ^ i - 1) +
      (fun _ : Hn F => (p : ℂ)) * (f - 1) := by
    funext z
    simp only [Pi.sub_apply, Pi.pow_apply, Pi.one_apply, Pi.mul_apply, Pi.add_apply,
      Finset.sum_apply]
    exact key (f z)
  rw [e]
  have h1 := small_mul h (sum_small h hr p)
  have h2 := small_mul (small_const h (p : ℂ)) h
  rw [norm_p ι] at h2
  refine small_mono (small_add h1 h2) ?_
  rw [mul_comm (p : ℝ)⁻¹ r, max_self]

theorem main : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ)
    (f : Hn F → ℂ), Small ι (p : ℝ)⁻¹ (f - 1) → ∀ N m : ℕ,
      Small ι ((p : ℝ)⁻¹ ^ (N + 1)) (f ^ (p ^ N * m) - 1) := by
  intro F _ _ _ p _ ι f h N m
  have hp0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hp1 : (p : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  have step : ∀ n : ℕ, Small ι ((p : ℝ)⁻¹ ^ (n + 1)) (f ^ (p ^ n) - 1) := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih =>
      have h1 := pow_p ih (pow_le_of_le_one hp0 hp1 (Nat.succ_ne_zero n))
      rw [← pow_mul, ← pow_succ, ← pow_succ] at h1
      exact h1
  have h2 := pow_sub_one (step N) (pow_le_one₀ hp0 hp1) m
  rwa [← pow_mul] at h2

end GlobalTheory.QPow

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.hilbertQExp_padicCongruence_pow_prime_pow : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (f : Hn F → ℂ), Small ι (p : ℝ)⁻¹ (f - 1) → ∀ N m : ℕ, Small ι ((p : ℝ)⁻¹ ^ (N + 1)) (f ^ (p ^ N * m) - 1) := by
  first | exact @GlobalTheory.QPow.main | exact GlobalTheory.QPow.main | (intros; apply GlobalTheory.QPow.main <;> assumption)
end
