module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle035
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomOfLinearScalingHermForm
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle013
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle025
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle164
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle007
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle056
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInvariantAfterDvrExtension
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSymmetricSqrtPrincipalSiegelFiniteEtale
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle005
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam.SamePeriod

theorem int_eq_of_exp {m m' : ℤ} (h : ∀ n : ℕ, 0 < n →
    Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / n) = Complex.exp (-(2 * Real.pi * Complex.I) * (m' : ℂ) / n)) :
    m = m' := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h ((m' - m).natAbs + 1) (Nat.succ_pos _))
  have hn : (((m' - m).natAbs + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have e : ((m' - m : ℤ) : ℂ) = ((((m' - m).natAbs + 1 : ℕ) : ℤ) * k : ℤ) := by
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_sub]
    generalize (((m' - m).natAbs + 1 : ℕ) : ℂ) = N at hk hn
    apply mul_left_cancel₀ h2
    field_simp at hk
    linear_combination (2 * Real.pi * Complex.I) * hk
  have e' : ((((m' - m).natAbs + 1 : ℕ) : ℤ)) ∣ m' - m := ⟨k, by exact_mod_cast e⟩
  have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs e' (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)
  omega

noncomputable def imForm {g m : ℕ} (Hm : Matrix (Fin m) (Fin m) ℂ) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin m → ℂ)) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => (hermForm Hm (F z) (F w)).im)
    (fun z z' w => by simp [hermForm])
    (fun r z w => by simp [hermForm])
    (fun z w w' => by simp [hermForm, Matrix.mulVec_add])
    (fun r z w => by simp [hermForm, Matrix.mulVec_smul])

theorem hermForm_eq_of_im {g m m' : ℕ} (Hm : Matrix (Fin m) (Fin m) ℂ) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (Hm' : Matrix (Fin m') (Fin m') ℂ) (F' : (Fin g → ℂ) →ₗ[ℂ] (Fin m' → ℂ)) {s : Set (Fin g → ℂ)}
    (hs : Submodule.span ℝ s = ⊤)
    (h : ∀ z ∈ s, ∀ w ∈ s, (hermForm Hm (F z) (F w)).im = (hermForm Hm' (F' z) (F' w)).im) (z w : Fin g → ℂ) :
    hermForm Hm (F z) (F w) = hermForm Hm' (F' z) (F' w) := by
  have e : imForm Hm F = imForm Hm' F' :=
    LinearMap.ext_on hs fun z hz => LinearMap.ext_on hs fun w hw => h z hz w hw
  have k : ∀ z w, (hermForm Hm (F z) (F w)).im = (hermForm Hm' (F' z) (F' w)).im := fun z w =>
    LinearMap.congr_fun₂ e z w
  refine Complex.ext ?_ (k z w)
  simpa [hermForm] using k (Complex.I • z) w

theorem ex_nsmul {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (z : Fin g → ℂ) (n : ℕ) :
    u.ex ((n : ℂ) • z) = u.ex z ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_smul, pow_zero, (u.ker 0).2 u.Λ.zero_mem]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, u.ex_add, ih, pow_succ]

theorem ex_inv_pow {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) {z : Fin g → ℂ}
    (hz : z ∈ u.Λ) {n : ℕ} (hn : 0 < n) : u.ex ((n : ℂ)⁻¹ • z) ^ n = 1 := by
  rw [← ex_nsmul, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), one_smul]
  exact (u.ker _).2 hz

theorem exists_equiv (hL : Out.Laws) (hU : ThetaUnifAV) (P : Out.PolAV (Sp ℂ)) {g : ℕ}
    (τ : Matrix (Fin g) (Fin g) ℂ) (u : HolUnif P.A P.L g) (hΛ : ∀ z, z ∈ u.Λ ↔ ∃ a, z = per τ a)
    (hW : ∀ (n : ℕ) (a b : Fin g ⊕ Fin g → ℤ) (c : ℂˣ), 0 < n →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / n) →
      Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • per τ a)) (u.ex ((n : ℂ)⁻¹ • per τ b)) (unitOn c)) :
    ∃ (u₀ : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u₀.Λ → ℂ)
      (F : (Fin g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ)), u₀.IsAH Hm χ ∧
      (∀ n : ℕ, (∀ s, ∃! θ, u₀.IsThetaFn Hm χ n θ ∧ u₀.IsFnPow n s θ) ∧
        ∀ θ, u₀.IsThetaFn Hm χ n θ → ∃! s, u₀.IsFnPow n s θ) ∧
      (∀ z, u₀.ex (F z) = u.ex z) ∧
      ∀ a b, (hermForm Hm (F (per τ a)) (F (per τ b))).im = omegaStd a b := by
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨u₀, Hm, χ, Ef, hAH, -, hv, hw, -, hθ, hE, -, hW₀⟩ := hU P rig hrig
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo P.A P.isAb P.L P.g g u₀ hv hw u.ex u.ex_add
    (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  haveI := u.discrete
  haveI := u₀.discrete
  have hinj := AnyUnif.injective_of_ker_le_discrete u.Λ F fun z hz => by
    rw [← u.ker, ← hF, hz]
    exact (u₀.ker 0).2 u₀.Λ.zero_mem
  have hsurj : LinearMap.range F = ⊤ := AHWeil.eq_top_of_add_discrete u₀.Λ _ fun w => by
    obtain ⟨z, hz⟩ := u.ex_onto (u₀.ex w)
    refine ⟨⟨w - F z, (u₀.ker _).1 ?_⟩, z, by simp⟩
    have h := u₀.ex_add (w - F z) (F z)
    rw [sub_add_cancel, hF, hz] at h
    exact (mul_eq_right.1 h.symm)
  refine ⟨u₀, Hm, χ, LinearEquiv.ofBijective F ⟨hinj, LinearMap.range_eq_top.1 hsurj⟩, hAH, hθ, hF, fun a b => ?_⟩
  have hm : ∀ a, per τ a ∈ u.Λ := fun a => (hΛ _).2 ⟨a, rfl⟩
  have hm₀ : ∀ a, F (per τ a) ∈ u₀.Λ := fun a => by
    rw [← u₀.ker, hF, u.ker]
    exact hm a
  have e : Ef ⟨_, hm₀ a⟩ ⟨_, hm₀ b⟩ = omegaStd a b := int_eq_of_exp fun n hn => by
    have h₁ := hW₀ n ⟨_, hm₀ a⟩ ⟨_, hm₀ b⟩ (Units.mk0 _ (Complex.exp_ne_zero _)) hn rfl
    have h₂ := hW n a b (Units.mk0 _ (Complex.exp_ne_zero _)) hn rfl
    rw [← map_smul, ← map_smul, hF, hF] at h₁
    have := ((hL.weil _ P n _).1 _ _ (ex_inv_pow u (hm a) hn) (ex_inv_pow u (hm b) hn)).unique h₁ h₂
    exact congrArg Units.val (H1.unitOn_injective this)
  rw [← e]
  exact (hE ⟨_, hm₀ a⟩ ⟨_, hm₀ b⟩).symm

theorem exists_hom (hL : Out.Laws) (hU : ThetaUnifAV) (P P' : Out.PolAV (Sp ℂ)) {g : ℕ}
    (τ : Matrix (Fin g) (Fin g) ℂ) (u : HolUnif P.A P.L g) (hΛ : ∀ z, z ∈ u.Λ ↔ ∃ a, z = per τ a)
    (hW : ∀ (n : ℕ) (a b : Fin g ⊕ Fin g → ℤ) (c : ℂˣ), 0 < n →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / n) →
      Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • per τ a)) (u.ex ((n : ℂ)⁻¹ • per τ b)) (unitOn c))
    (u' : HolUnif P'.A P'.L g) (hΛ' : ∀ z, z ∈ u'.Λ ↔ ∃ a, z = per τ a)
    (hW' : ∀ (n : ℕ) (a b : Fin g ⊕ Fin g → ℤ) (c : ℂˣ), 0 < n →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / n) →
      Out.WeilIs P'.A P'.L n (u'.ex ((n : ℂ)⁻¹ • per τ a)) (u'.ex ((n : ℂ)⁻¹ • per τ b)) (unitOn c)) :
    ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u.ex z ≫ f = u'.ex z := by
  obtain ⟨v, Hm, χ, F, hA, hθ, hF, hE⟩ := exists_equiv hL hU P τ u hΛ hW
  obtain ⟨v', Hm', χ', F', hA', hθ', hF', hE'⟩ := exists_equiv hL hU P' τ u' hΛ' hW'
  have hH := hermForm_eq_of_im Hm' F'.toLinearMap Hm F.toLinearMap u.full fun z hz w hw => by
    obtain ⟨a, rfl⟩ := (hΛ z).1 hz
    obtain ⟨b, rfl⟩ := (hΛ w).1 hw
    exact (hE' a b).trans (hE a b).symm
  obtain ⟨f, hf, hfe⟩ := exists_hom_of_linear_scaling_hermForm P P' v v' Hm χ Hm' χ' hA hA'
    (fun k => (hθ k).2) (fun k => (hθ' k).1) (F.symm.trans F').toLinearMap 1
    (fun l hl => by
      obtain ⟨z, rfl⟩ := F.surjective l
      rw [← v.ker, hF, u.ker, hΛ, ← hΛ', ← u'.ker, ← hF', v'.ker] at hl
      simpa using hl)
    (fun z w => by
      obtain ⟨z, rfl⟩ := F.surjective z
      obtain ⟨w, rfl⟩ := F.surjective w
      simpa using hH z w)
  refine ⟨f, hf, fun z => ?_⟩
  rw [← hF, ← hfe, ← hF']
  simp

end GlobalTheory.KeyFam.SamePeriod

namespace GlobalTheory.KeyFam
open SamePeriod

theorem exists_iso_of_perLev : Out.Laws → ThetaUnifAV → ∀ (g k : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (P P' : Out.PolAV (Sp ℂ)) (lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) (lev' : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P'.A)), PerLev P τ k lev → PerLev P' τ k lev' → ∃ e : P'.A ≅ P.A, IsMonHom e.hom ∧ LamIs P'.A P'.L P.A (abelian₂ P.A P.L) e.hom.left ∧ ∀ a, lev' a ≫ e.hom = lev a := by
  rintro hL hU g k τ P P' lev lev' ⟨-, -, -, u, hΛ, hW, hlev⟩ ⟨-, -, -, u', hΛ', hW', hlev'⟩
  obtain ⟨f, hf, hfe⟩ := exists_hom hL hU P' P τ u' hΛ' hW' u hΛ hW
  obtain ⟨f', -, hfe'⟩ := exists_hom hL hU P P' τ u hΛ hW u' hΛ' hW'
  haveI := P.isAb.smooth
  haveI := P'.isAb.smooth
  haveI := P.isAb.proper
  haveI := P'.isAb.proper
  haveI := P.isAb.comm
  haveI := P'.isAb.comm
  haveI := isReduced_of_smooth_complex _ P.A.hom inferInstance
  haveI := isReduced_of_smooth_complex _ P'.A.hom inferInstance
  let e : P'.A ≅ P.A :=
    { hom := f
      inv := f'
      hom_inv_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := u'.ex_onto x
        rw [← Category.assoc, hfe, hfe', Category.comp_id]
      inv_hom_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := u.ex_onto x
        rw [← Category.assoc, hfe', hfe, Category.comp_id] }
  have tors : ∀ (n : ℕ) (x : 𝟙_ (Over (Sp ℂ)) ⟶ P'.A), 0 < n → x ^ n = 1 →
      ∃ a, x = u'.ex ((n : ℂ)⁻¹ • per τ a) := fun n x hn hx => by
    obtain ⟨z, rfl⟩ := u'.ex_onto x
    rw [← ex_nsmul, u'.ker, hΛ'] at hx
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, by rw [← ha, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), one_smul]⟩
  have h₁ := lam_iso_of_weil_pairings hL ℂ P' P f 2 1 hf Nat.prime_two inferInstance
    fun n x y c hn _ hx hy h => by
      obtain ⟨a, ha⟩ := tors n x hn hx
      obtain ⟨b, hb⟩ := tors n y hn hy
      have h₂ := hW' n a b (Units.mk0 _ (Complex.exp_ne_zero _)) hn rfl
      rw [← ha, ← hb] at h₂
      rw [pow_one, ((hL.weil _ P' n _).1 _ _ hx hy).unique h h₂, ha, hb, hfe, hfe]
      exact hW n a b _ hn rfl
  have hp : IsGrpPullback P'.A P.A (𝟙 _) f.left := @isGrpPullback_of_iso _ _ _ _ _ e hf
  have hq := LamPull.exists_isSquare hp.1.w
  have hfL : (P.L.pull f.left).IsLB := pull_isLB P.isLB _
  have h₂ := LamPull.lbIso_lam_pull hp P.isLB hfL ⟨idIso _, idIso_isGen hfL⟩ hq
  have h₀ : LBIso (abelian₂ P'.A (lbPow P'.L 1)) (abelian₂ P'.A P'.L) := by
    obtain ⟨w, hw⟩ := lbIso_lbPow_one P'.isLB
    exact ⟨LB.linCombIso w _ _, DVR.linCombIso_isGen w hw _ _⟩
  have l₀ : (abelian₂ P'.A P'.L).IsLB := DVR.linComb_isLB _ P'.isLB _ _
  have l₁ : (abelian₂ P'.A (lbPow P'.L 1)).IsLB := DVR.linComb_isLB _ (DVR.linComb_isLB _ P'.isLB _ _) _ _
  have l₂ : (abelian₂ P'.A (P.L.pull f.left)).IsLB := DVR.linComb_isLB _ hfL _ _
  have l₃ : (abelian₂ P.A P.L).IsLB := DVR.linComb_isLB _ P.isLB _ _
  refine ⟨e, hf, ⟨_, hq, LBIso.trans l₀ l₂ (pull_isLB l₃ _) (LBIso.trans l₀ l₁ l₂ h₀.symm h₁) h₂⟩, fun a => ?_⟩
  rw [hlev, hlev']
  exact hfe _

end GlobalTheory.KeyFam
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.discriminant_eq_jacobian_complete_intersection_dvr : Out.Laws → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (x : KeyIn O) (n l d : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), 1 ≤ n → x.P.g * n < l → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → {y : x.P.A.left | x.P.A.hom y = IsLocalRing.closedPoint O ∧ ∀ i, y ∉ Out.nonzeroLocus (s i)}.Finite → (∀ a, ⊤ ≤ (z a).left ⁻¹ᵁ x.P.L.U (ch a)) → (∀ a i, valT (T := O) (z a).left (x.P.L.U (ch a)) ((s i).f (ch a)) = 0) → (∀ a, jac x s (z a) (ch a) ≠ 0) → Function.Injective z → (∀ y : x.P.A.left, x.P.A.hom y ≠ IsLocalRing.closedPoint O → (∀ i, y ∉ Out.nonzeroLocus (s i)) → ∃ a, ∃ p : Sp O, (z a).left p = y) → ∃ (ev₀ : ∀ j, Matrix (Fin d) (Fin ((l - j * n) ^ x.P.g)) O) (Pm : Matrix (Fin d) (Fin d) O) (t₀ : O), (Matrix.of fun a k => valT (T := O) (z a).left (x.P.L.U (ch a)) ((b 0 k).f (ch a))) = Pm * ev₀ 0 ∧ IsCx kdeg (kosD (N := fun j => (l - j * n) ^ x.P.g) m ev₀) ∧ TorsSq kdeg (kosD (N := fun j => (l - j * n) ^ x.P.g) m ev₀) t₀ ∧ Associated (Pm.det ^ 2) (∏ a, jac x s (z a) (ch a)) := by
  first | exact @GlobalTheory.DiscrJacGlobal.main | exact GlobalTheory.DiscrJacGlobal.main | (intros; apply GlobalTheory.DiscrJacGlobal.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.exists_keyInvariant_algClosed_transversal : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (d : ℕ) (s : Fin x.P.g → RR x n) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), admitted x.P.g n l l' al → ((degProd x.P.g n l l' : ℕ) : K) ≠ 0 → EtZ x s z ch → ∃ κ, KaVal x n l l' al s κ := by
  first | exact @GlobalTheory.KeyKa.exists_kaVal_of_isAlgClosed | exact GlobalTheory.KeyKa.exists_kaVal_of_isAlgClosed | (intros; apply GlobalTheory.KeyKa.exists_kaVal_of_isAlgClosed <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.exists_keyInvariant_after_dvr_extension : Out.Laws → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (r : O →+* Ω) (x : KeyIn O) (xk : KeyIn Ω) φ w (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (d : ℕ) (hg : xk.P.g = x.P.g) (s : Fin x.P.g → RR x n) (sk : Fin xk.P.g → RR xk n) (zk : Fin d → Pt xk) (chk : Fin d → xk.P.L.ι), RingHom.ker r = IsLocalRing.maximalIdeal O → admitted x.P.g n l l' al → IsUnit ((degProd x.P.g n l l' : ℕ) : O) → KeyVia xk x r φ w → (∀ i, SecVia xk x φ w (sk i) (s (i.cast hg))) → EtZ xk sk zk chk → ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (j : O →+* O') (r' : O' →+* Ω) (x' : KeyIn O') (φ' : _) (w' : _) (hg' : x'.P.g = x.P.g) (s' : Fin x'.P.g → RR x' n) (u : O'ˣ), Function.Injective j ∧ IsLocalHom j ∧ r'.comp j = r ∧ KeyVia x' x j φ' w' ∧ (∀ i, SecVia x' x φ' w' (s' i) (s (i.cast hg'))) ∧ KaVal x' n l l' al s' u := by
  first | exact @GlobalTheory.KaLift.exists_kaVal_extension | exact GlobalTheory.KaLift.exists_kaVal_extension | (intros; apply GlobalTheory.KaLift.exists_kaVal_extension <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.exists_symmetric_sqrt_principal_siegel_finite_etale : Out.Laws → ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (R : Type) [CommRing R] [Algebra ℚ R] [IsNoetherianRing R] (S : Scheme.{0}) (s : S ⟶ Sp o) (c : SiegPre h k ζ s) (f : Sp R ⟶ S), 2 ≤ k → IsUnit ζ → c.Principal → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (P : Out.PolAV (Sp R₁)) (φ : P.A.left ⟶ c.A.left), (Module.Finite R R₁ ∧ Algebra.Etale R R₁ ∧ Module.FaithfullyFlat R R₁) ∧ SqOf P c (spMap (algebraMap R R₁) ≫ f) φ ∧ TorsConst P.A 2 := by
  first | exact @GlobalTheory.SiegelSqrt.exists_sqrt | exact GlobalTheory.SiegelSqrt.exists_sqrt | (intros; apply GlobalTheory.SiegelSqrt.exists_sqrt <;> assumption)
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.exists_iso_of_same_periodMatrix_level : Out.Laws → ThetaUnifAV → ∀ (g k : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (P P' : Out.PolAV (Sp ℂ)) (lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) (lev' : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P'.A)), PerLev P τ k lev → PerLev P' τ k lev' → ∃ e : P'.A ≅ P.A, IsMonHom e.hom ∧ LamIs P'.A P'.L P.A (abelian₂ P.A P.L) e.hom.left ∧ ∀ a, lev' a ≫ e.hom = lev a := by
  first | exact @GlobalTheory.KeyFam.exists_iso_of_perLev | exact GlobalTheory.KeyFam.exists_iso_of_perLev | (intros; apply GlobalTheory.KeyFam.exists_iso_of_perLev <;> assumption)

end
end
