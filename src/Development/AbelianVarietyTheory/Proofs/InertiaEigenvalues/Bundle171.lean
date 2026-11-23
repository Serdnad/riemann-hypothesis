module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle065
public import Mathlib.RingTheory.Norm.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle098
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle142
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearDescentPartialFourierEqFourierDescent
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle100
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle147
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle087
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle103
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle148
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle144
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle099
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle119
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle149
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.Analysis.Normed.Group.Ultra
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.Unr.NormValU

section Gen

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {E : Type} [Field E]
    [Algebra O E] [IsFractionRing O E]

theorem val_mul_ne {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) : val O (x * y) = val O x + val O y := by
  unfold val
  have hx' : (IsDiscreteValuationRing.maximalIdeal O).valuation E x ≠ 0 := by simpa using hx
  have hy' : (IsDiscreteValuationRing.maximalIdeal O).valuation E y ≠ 0 := by simpa using hy
  rw [map_mul, WithZero.log_mul hx' hy']
  ring

theorem val_one_eq : val O (1 : E) = 0 := by simp [val]

theorem val_pow_eq {x : E} (hx : x ≠ 0) (k : ℕ) : val O (x ^ k) = k * val O x := by
  induction k with
  | zero => simp [val_one_eq]
  | succ k ih =>
    rw [pow_succ, val_mul_ne O (pow_ne_zero _ hx) hx, ih]
    push_cast; ring

theorem val_inv_eq {x : E} (hx : x ≠ 0) : val O x⁻¹ = -val O x := by
  have := val_mul_ne O hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, val_one_eq] at this
  omega

theorem lift_of_val_eq_zero {x : E} (hx : x ≠ 0) (h : val O x = 0) : ∃ a : O, algebraMap O E a = x := by
  have hx' : (IsDiscreteValuationRing.maximalIdeal O).valuation E x ≠ 0 := by simpa using hx
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).valuation E x = 1 := by
    unfold val at h
    rw [← WithZero.exp_log hx']
    have : WithZero.log ((IsDiscreteValuationRing.maximalIdeal O).valuation E x) = 0 := by omega
    rw [this, WithZero.exp_zero]
  exact IsDiscreteValuationRing.exists_lift_of_le_one h1.le

theorem val_unit_eq (a : O) (ha : IsUnit a) : val O (algebraMap O E a) = 0 := by
  unfold val
  have : (IsDiscreteValuationRing.maximalIdeal O).valuation E (algebraMap O E a) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
    exact fun h => (IsLocalRing.mem_maximalIdeal a).1 h ha
  rw [this]; simp

theorem exists_val_one : ∃ π : E, val O π = 1 := by
  obtain ⟨π, hπ⟩ := (IsDiscreteValuationRing.maximalIdeal O).valuation_exists_uniformizer E
  exact ⟨π, by simp [val, hπ]⟩

end Gen

theorem norm_int (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hU : IsUnrExt K K' d φ) (hd : d ≠ 0) (z : K'.O) :
    ∃ a : K.O, algebraMap K.O K.E a = @Algebra.norm K.E K'.E _ _ φ.toAlgebra (algebraMap K'.O K'.E z) := by
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra
  haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional K.E K'.E :=
    Module.finite_of_finrank_pos (by rw [hU.2.2.2.2]; exact Nat.pos_of_ne_zero hd)
  haveI : Algebra.IsSeparable K.E K'.E := Algebra.IsSeparable.of_integral _ _
  have h := Algebra.isIntegral_norm (R := K.O) K.E (intO K K' d φ hU hd z)
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact ⟨a, ha⟩

theorem val_norm : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ y : K'.E,
    val K.O (@Algebra.norm K.E K'.E _ _ φ.toAlgebra y) = (d : ℤ) * val K'.O y := by
  intro K K' d φ hφ y
  letI : Algebra K.E K'.E := φ.toAlgebra
  have hd : d ≠ 0 := by
    intro hd0
    have h1 : Nat.card (IsLocalRing.ResidueField K'.O) = 1 := by
      rw [K'.card_res, hφ.1, hd0, pow_zero, one_pow]
    have h2 := Finite.one_lt_card (α := IsLocalRing.ResidueField K'.O)
    omega
  have hfr : Module.finrank K.E K'.E = d := hφ.2.2.2.2
  haveI : Module.Finite K.E K'.E := Module.finite_of_finrank_pos (by omega)
  by_cases hy : y = 0
  · subst hy
    rw [Algebra.norm_zero]
    simp [val]
  obtain ⟨π, hπ⟩ := exists_val_one K.O (E := K.E)
  have hπ0 : π ≠ 0 := by rintro rfl; simp [val] at hπ
  have hφπ : val K'.O (φ π) = 1 := by rw [hφ.2.2.1, hπ]
  have hφπ0 : φ π ≠ 0 := (map_ne_zero φ).2 hπ0
  set n := val K'.O y with hn
  set a := (-n).toNat
  set b := n.toNat
  have hab : (b : ℤ) - a = n := Int.toNat_sub_toNat_neg n
  set u := y * φ π ^ a * (φ π ^ b)⁻¹ with hu
  have hu0 : u ≠ 0 := mul_ne_zero (mul_ne_zero hy (pow_ne_zero _ hφπ0)) (inv_ne_zero (pow_ne_zero _ hφπ0))
  have hvu : val K'.O u = 0 := by
    rw [hu, val_mul_ne _ (mul_ne_zero hy (pow_ne_zero _ hφπ0)) (inv_ne_zero (pow_ne_zero _ hφπ0)),
      val_mul_ne _ hy (pow_ne_zero _ hφπ0), val_inv_eq _ (pow_ne_zero _ hφπ0), val_pow_eq _ hφπ0,
      val_pow_eq _ hφπ0, hφπ, ← hn]
    omega
  have hvu' : val K'.O u⁻¹ = 0 := by rw [val_inv_eq _ hu0, hvu]; rfl
  obtain ⟨u₁, hu₁⟩ := lift_of_val_eq_zero K'.O hu0 hvu
  obtain ⟨u₂, hu₂⟩ := lift_of_val_eq_zero K'.O (inv_ne_zero hu0) hvu'
  obtain ⟨m₁, hm₁⟩ := norm_int K K' d φ hφ hd u₁
  obtain ⟨m₂, hm₂⟩ := norm_int K K' d φ hφ hd u₂
  have hunit : IsUnit m₁ := by
    have h12 : m₁ * m₂ = 1 := by
      apply IsFractionRing.injective K.O K.E
      rw [map_mul, hm₁, hm₂, hu₁, hu₂, ← map_mul, mul_inv_cancel₀ hu0, map_one, map_one]
    exact IsUnit.of_mul_eq_one m₂ h12
  have hNu : val K.O (Algebra.norm K.E u) = 0 := by
    rw [← hu₁, ← hm₁]; exact val_unit_eq K.O m₁ hunit
  have hNu0 : Algebra.norm K.E u ≠ 0 := Algebra.norm_ne_zero_iff.2 hu0
  have hNy0 : Algebra.norm K.E y ≠ 0 := Algebra.norm_ne_zero_iff.2 hy
  have hNφ : Algebra.norm K.E (φ π) = π ^ d := by
    rw [← hfr]; exact Algebra.norm_algebraMap π
  have key : y * φ π ^ a = u * φ π ^ b := by
    rw [hu, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hφπ0), mul_one]
  have key2 := congrArg (fun x => val K.O (Algebra.norm K.E x)) key
  simp only [map_mul, map_pow, hNφ] at key2
  rw [val_mul_ne _ hNy0 (pow_ne_zero _ (pow_ne_zero _ hπ0)), val_mul_ne _ hNu0 (pow_ne_zero _ (pow_ne_zero _ hπ0)),
    val_pow_eq _ (pow_ne_zero _ hπ0), val_pow_eq _ (pow_ne_zero _ hπ0), val_pow_eq _ hπ0, hNu, hπ] at key2
  rw [← hab]
  push_cast at key2 ⊢
  linarith

end GlobalTheory.UnitLemma.Unr.NormValU
end
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem _root_.GlobalTheory.T.addVal_norm_unramifiedInvolutionFieldExt_eq_mul : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → 0 < d → ∀ y : K'.E, val K.O (@Algebra.norm K.E K'.E _ _ φ.toAlgebra y) = d * val K'.O y := by
  first | exact @GlobalTheory.UnitLemma.Unr.NormVal.normval | exact GlobalTheory.UnitLemma.Unr.NormVal.normval | (intros; apply GlobalTheory.UnitLemma.Unr.NormVal.normval <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.LinDesc

theorem norm_eq_of_sub_lt {F : Type} [NormedField F] [IsUltrametricDist F] {x y : F}
    (h : ‖x - y‖ < ‖y‖) : ‖x‖ = ‖y‖ := by
  have h1 : ‖x‖ ≤ max ‖x - y‖ ‖y‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (x - y) y
  have h2 : ‖y‖ ≤ max ‖y - x‖ ‖x‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (y - x) x
  rw [norm_sub_rev] at h2
  rcases le_total ‖x - y‖ ‖y‖ with h3 | h3
  · rw [max_eq_right h3] at h1
    rcases le_total ‖x - y‖ ‖x‖ with h4 | h4
    · rw [max_eq_right h4] at h2; exact le_antisymm h1 h2
    · rw [max_eq_left h4] at h2; exact absurd h (not_lt.mpr h2)
  · exact absurd h (not_lt.mpr h3)

theorem eta_det_isLocallyConstant {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F] (r : ℕ) :
    IsLocallyConstant (fun g : GL (Fin r) F => eta ((g : Matrix (Fin r) (Fin r) F).det)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hd : ((g : Matrix (Fin r) (Fin r) F).det) ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  have hc : Continuous (fun h : GL (Fin r) F => (h : Matrix (Fin r) (Fin r) F).det) :=
    Units.continuous_val.matrix_det
  have hpos : 0 < ‖(g : Matrix (Fin r) (Fin r) F).det‖ := norm_pos_iff.mpr hd
  have hev : ∀ᶠ h : GL (Fin r) F in 𝓝 g, ‖((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det - (g : Matrix (Fin r) (Fin r) F).det‖ <
      ‖(g : Matrix (Fin r) (Fin r) F).det‖ := by
    have : Continuous (fun h : GL (Fin r) F =>
        ‖(h : Matrix (Fin r) (Fin r) F).det - (g : Matrix (Fin r) (Fin r) F).det‖) :=
      (hc.sub continuous_const).norm
    exact (this.tendsto g).eventually_lt_const (by rw [sub_self, norm_zero]; exact hpos)
  filter_upwards [hev] with h hh
  unfold eta
  rw [norm_eq_of_sub_lt hh]



theorem desc_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (M : Meas r F E) (α : GL (Fin r) F → ℝ) (f' : Gl r F → ℂ), IsTest f' → IsLocallyConstant α → HasCompactSupport α → IsTest (LinDesc.desc A M hG lam α f') := by
  intro F E _ _ _ _ hU A r τ p hG lam M α f' hf hα hαc
  haveI : IsUltrametricDist F := hU.ultraF

  let ρL : A.K →ₗ[F] (Fin r → F) :=
    LinearMap.pi fun i => (Algebra.trace F A.K).comp (LinearMap.mulLeft F (τ ^ (i : ℕ)))
  have hρL : ∀ c, ρL c = fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * c) := fun c => rfl
  have hbij : Function.Bijective ρL := by
    have := (GlobalTheory.T.jacquetRallis_invK_regular_iff_isUnit F E A r τ p lam hG).1
    rw [show (⇑ρL) = fun (a : A.K) (i : Fin r) => Algebra.trace F A.K (τ ^ (i : ℕ) * a) from funext hρL]
    exact this
  let ρE : A.K ≃ₗ[F] (Fin r → F) := LinearEquiv.ofBijective ρL hbij
  have hι : Continuous (bas A hG).equivFun :=
    IsModuleTopology.continuous_of_linearMap (R := F) (bas A hG).equivFun.toLinearMap
  have hρ : Continuous ρL := IsModuleTopology.continuous_of_linearMap (R := F) ρL
  have hιs : Continuous (bas A hG).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap (R := F) (bas A hG).equivFun.symm.toLinearMap
  have hρs : Continuous ρE.symm :=
    IsModuleTopology.continuous_of_linearMap (R := F) ρE.symm.toLinearMap
  have hpt : Continuous (fun x : A.K × A.K => pt A hG lam x.1 x.2) := by
    unfold pt
    exact continuous_const.prodMk ((hι.comp continuous_fst).prodMk
      ((hρ.comp continuous_snd).prodMk continuous_const))
  have hact : Continuous (fun q : GL (Fin r) F × Gl r F => act q.1 q.2) := by
    unfold act
    have h1 : Continuous (fun q : GL (Fin r) F × Gl r F => ((q.1 : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) :=
      Units.continuous_val.comp continuous_fst
    have h2 : Continuous (fun q : GL (Fin r) F × Gl r F => ((q.1⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) :=
      Units.continuous_val.comp (continuous_inv.comp continuous_fst)
    exact ((h1.matrix_mul (continuous_fst.comp continuous_snd)).matrix_mul h2).prodMk
      ((h1.matrix_mulVec (continuous_fst.comp (continuous_snd.comp continuous_snd))).prodMk
        (((continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).matrix_vecMul h2).prodMk
          (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))))
  have heta := eta_det_isLocallyConstant (F := F) r

  have hΦ : IsLocallyConstant (fun q : (A.K × A.K) × GL (Fin r) F =>
      f' (act q.2 (pt A hG lam q.1.1 q.1.2)) * eta ((q.2 : Matrix (Fin r) (Fin r) F).det) * (α q.2 : ℂ)) := by
    have a1 : IsLocallyConstant (fun q : (A.K × A.K) × GL (Fin r) F => f' (act q.2 (pt A hG lam q.1.1 q.1.2))) :=
      hf.1.comp_continuous (hact.comp (continuous_snd.prodMk (hpt.comp continuous_fst)))
    have a2 : IsLocallyConstant (fun q : (A.K × A.K) × GL (Fin r) F => eta ((q.2 : Matrix (Fin r) (Fin r) F).det)) :=
      heta.comp_continuous continuous_snd
    have a3 : IsLocallyConstant (fun q : (A.K × A.K) × GL (Fin r) F => (α q.2 : ℂ)) :=
      (hα.comp_continuous continuous_snd).comp (fun t : ℝ => (t : ℂ))
    exact (a1.mul a2).mul a3
  have hloc : IsLocallyConstant (LinDesc.desc A M hG lam α f') := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x₀
    have h1 : ∀ᶠ x in 𝓝 x₀, ∀ g ∈ tsupport α,
        f' (act g (pt A hG lam x.1 x.2)) * eta ((g : Matrix (Fin r) (Fin r) F).det) * (α g : ℂ) =
          f' (act g (pt A hG lam x₀.1 x₀.2)) * eta ((g : Matrix (Fin r) (Fin r) F).det) * (α g : ℂ) := by
      refine hαc.eventually_forall_of_forall_eventually fun g _ => ?_
      have h2 := (hΦ.prodMk (hΦ.comp_continuous (f := fun q : (A.K × A.K) × GL (Fin r) F => (x₀, q.2))
        (continuous_const.prodMk continuous_snd))).eventually_eq (x₀, g)
      filter_upwards [h2] with q hq
      simp only [Prod.mk.injEq, Function.comp] at hq
      rw [hq.1, hq.2]
    filter_upwards [h1] with x hx
    unfold desc
    congr 1
    funext g
    by_cases hg : g ∈ tsupport α
    · exact hx g hg
    · rw [image_eq_zero_of_notMem_tsupport hg]; simp
  refine ⟨hloc, ?_⟩

  let L : (Fin r → F) × (Fin r → F) → A.K × A.K := fun u => ((bas A hG).equivFun.symm u.1, ρE.symm u.2)
  have hL : Continuous L := (hιs.comp continuous_fst).prodMk (hρs.comp continuous_snd)
  let T : GL (Fin r) F × Gl r F → A.K × A.K := fun q => L ((act q.1⁻¹ q.2).2.1, (act q.1⁻¹ q.2).2.2.1)
  have hT : Continuous T := by
    have : Continuous (fun q : GL (Fin r) F × Gl r F => act q.1⁻¹ q.2) :=
      hact.comp ((continuous_inv.comp continuous_fst).prodMk continuous_snd)
    exact hL.comp ((continuous_fst.comp (continuous_snd.comp this)).prodMk
      (continuous_fst.comp (continuous_snd.comp (continuous_snd.comp this))))
  have hS : IsCompact (T '' (tsupport α ×ˢ tsupport f')) := (hαc.prod hf.2).image hT
  have hsub : Function.support (LinDesc.desc A M hG lam α f') ⊆ T '' (tsupport α ×ˢ tsupport f') := by
    intro x hx
    by_contra hxS
    apply hx
    have h0 : ∀ g : GL (Fin r) F,
        f' (act g (pt A hG lam x.1 x.2)) * eta ((g : Matrix (Fin r) (Fin r) F).det) * (α g : ℂ) = 0 := by
      intro g
      by_contra hne
      apply hxS
      have hαg : α g ≠ 0 := by
        intro h0; apply hne; rw [h0]; simp
      have hfg : f' (act g (pt A hG lam x.1 x.2)) ≠ 0 := by
        intro h0; apply hne; rw [h0]; simp
      refine ⟨(g, act g (pt A hG lam x.1 x.2)), ⟨subset_tsupport _ hαg, subset_tsupport _ hfg⟩, ?_⟩
      have hback : act g⁻¹ (act g (pt A hG lam x.1 x.2)) = pt A hG lam x.1 x.2 := by
        rw [← act_mul, inv_mul_cancel, act_one]
      show L ((act g⁻¹ (act g (pt A hG lam x.1 x.2))).2.1, (act g⁻¹ (act g (pt A hG lam x.1 x.2))).2.2.1) = x
      rw [hback]
      show ((bas A hG).equivFun.symm ((bas A hG).equivFun x.1), ρE.symm (ρL x.2)) = x
      rw [LinearEquiv.symm_apply_apply]
      have : ρE.symm (ρL x.2) = x.2 := ρE.symm_apply_apply x.2
      rw [this]
    unfold desc
    simp only [h0, integral_zero]
  have hcl : IsClosed (Function.support (LinDesc.desc A M hG lam α f')) := by
    have := hloc.isOpen_fiber 0
    rw [← isOpen_compl_iff]
    convert this using 1
    ext x; simp
  unfold HasCompactSupport tsupport
  rw [hcl.closure_eq]
  exact hS.of_isClosed_subset hcl hsub

end GlobalTheory.JR.LinDesc
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.linearDescent_partialFourier_eq_fourier_descent : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ μK : Measure A.K, SelfDual μK (A.kerK ψ) → ∀ (α : GL (Fin r) F → ℝ) (f' : Gl r F → ℂ), IsTest f' → IsLocallyConstant α → HasCompactSupport α → (∀ (g : GL (Fin r) F) (b c : A.K), fourG M ψ f' (act g (LinDesc.pt A hG lam b c)) = A.fourK μK ψ (fun x => f' (act g (LinDesc.pt A hG lam x.1 x.2))) (b, c)) → ∀ x : A.K × A.K, LinDesc.desc A M hG lam α (fourG M ψ f') x = A.fourK μK ψ (LinDesc.desc A M hG lam α f') x := by
  first | exact @GlobalTheory.JR.LinDesc.Swap.desc_fourG_eq_fourK_desc | exact GlobalTheory.JR.LinDesc.Swap.desc_fourG_eq_fourK_desc | (intros; apply GlobalTheory.JR.LinDesc.Swap.desc_fourG_eq_fourK_desc <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.orbitalIntegral_descended_eq_unitary : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (M : Meas r F E) (τ : A.K) (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)) (hx : A.IsIsom x j) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)), (∀ z, j (algebraMap A.K A.L τ * z) = Ax.1 *ᵥ j z) → ∀ (lam : F) (ν : Measure (unitary A.L)), ν.IsHaarMeasure → ∀ (α : Matrix.unitaryGroup (Fin r) E → ℝ), IsLocallyConstant α → (∀ g, 0 ≤ α g) → ∀ Z : Set (Matrix (Fin r) (Fin r) E), (∀ g : Matrix.unitaryGroup (Fin r) E, g.1 * Ax.1 * star g.1 ∈ Z → ∫ t, α (g * (A.uHom hx t)⁻¹) ∂ν = 1) → ∀ f₀ : Hn r F E → ℂ, Continuous f₀ → (∀ X, f₀ X ≠ 0 → X.1.1 ∈ Z) → ∀ y : A.L, (letI := M.mU; Integrable (fun g => f₀ (actU g (Ax, j y, lam))) M.μU) → A.orbL ν (A.descFn M Ax j lam α f₀) y = orbU M f₀ (Ax, j y, lam) := by
  first | exact @GlobalTheory.JR.DescOrb.orbL_descFn | exact GlobalTheory.JR.DescOrb.orbL_descFn | (intros; apply GlobalTheory.JR.DescOrb.orbL_descFn <;> assumption)
end

section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped NNReal

noncomputable section

namespace GlobalTheory.JR.WeilQuad

theorem fOp_comp_smul : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ),
    Hyp A ψ x μ ω → ∀ (s : A.Kˣ) (φ : A.L → ℂ), IsTest φ → ∀ y,
      fOp A ψ x μ (fun y' => φ ((s : A.K) • y')) y =
        ((A.absK s : ℂ) ^ 2)⁻¹ * fOp A ψ x μ φ (((s⁻¹ : A.Kˣ) : A.K) • y) := by
  intro F E _ _ _ _ U A ψ x μ ω hH s φ _ y
  have := U.charZero; have := U.ultraF; have := U.lcF
  have := EtMeas.finite_L A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have hN : distribHaarChar A.L (MeasScale.unitL A s) = distribHaarChar A.K s ^ 2 := by
    obtain ⟨⟨b⟩, -, -, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
    obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
    have : ContinuousStar A.L := ⟨IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)⟩
    rw [← map_pow]
    refine GlobalTheory.JR.ModuleNorm.distribHaarChar_eq_norm A.K A.L b.equivFun.symm
        (IsModuleTopology.continuous_of_linearMap (b.equivFun.symm.toLinearMap.restrictScalars F))
        (IsModuleTopology.continuous_of_linearMap (b.equivFun.toLinearMap.restrictScalars F)) _ _ ?_
    simp [MeasScale.unitL, A.star_K, pow_two]
  have hμ : μ.IsAddHaarMeasure := hH.2.2.2.1.1
  have hinv : algebraMap A.K A.L (s : A.K) * algebraMap A.K A.L ((s⁻¹ : A.Kˣ) : A.K) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have key : ∀ y', φ ((s : A.K) • y') * A.kerL ψ x y' y =
      (fun u => φ u * A.kerL ψ x u (((s⁻¹ : A.Kˣ) : A.K) • y)) (MeasScale.unitL A s • y') := by
    intro y'
    simp only [MeasScale.unitL_smul, Et.kerL]
    rw [Algebra.smul_def, Algebra.smul_def, star_mul', A.star_K]
    congr 4
    linear_combination (star y' * y) * hinv.symm
  simp only [fOp, fourB]
  rw [integral_congr_ae (Eventually.of_forall key),
    MeasScale.integral_units_smul μ (MeasScale.unitL A s)
      (fun u => φ u * A.kerL ψ x u (((s⁻¹ : A.Kˣ) : A.K) • y)), hN, EtMeas.absK_unit]
  push_cast
  rfl

end GlobalTheory.JR.WeilQuad
end
end

section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.stableQuadraticGaussIntegral_mul_norm : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ (t s : A.Kˣ), (∃ ℓ : A.L, A.NL ℓ = s) → ∀ G : ℂ, IsStableGauss A ψ x μ t G → IsStableGauss A ψ x μ ((t * s : A.Kˣ) : A.K) (G * ((A.absK s : ℂ))⁻¹) := by
  first | exact @GlobalTheory.JR.WeilQuad.GaussTrans.main | exact GlobalTheory.JR.WeilQuad.GaussTrans.main | (intros; apply GlobalTheory.JR.WeilQuad.GaussTrans.main <;> assumption)
end

section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.quadraticWeil_unipotent_torus_preserve_test : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ φ : A.L → ℂ, IsTest φ → (∀ z, IsTest (nOp A ψ x z φ)) ∧ ∀ s, IsTest (mOp A ω s φ) := by
  first | exact @GlobalTheory.JR.WeilQuad.isTest_nOp_mOp | exact GlobalTheory.JR.WeilQuad.isTest_nOp_mOp | (intros; apply GlobalTheory.JR.WeilQuad.isTest_nOp_mOp <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma Polynomial

theorem span_adjoin_gen_eq_top {K : UQ} (B : InvAlg K) (hP : B.P.Separable) :
    Submodule.span K.E ((Subalgebra.toSubmodule (Algebra.adjoin K.O {B.g}) : Submodule K.O B.A) : Set B.A) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨f, rfl⟩ := Sandwich.exists_aeval B hP x
  rw [aeval_eq_sum_range]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  show B.g ^ i ∈ Algebra.adjoin K.O {B.g}
  exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) i

theorem pow_smul_mem_adjoin_gen : ∀ (K : UQ) (B : InvAlg K) (a : K.O), B.P.Separable → K.Small a →
    ∃ N : ℕ, ∀ r : B.A, IsIntegral K.O r → (al K a ^ N) • r ∈ Algebra.adjoin K.O {B.g} := by
  intro K B a hP ha
  obtain ⟨m, hm⟩ := Sandwich.integral_sub B hP a ha.2.1 _ (span_adjoin_gen_eq_top B hP)
  refine ⟨m, fun r hr => ?_⟩
  have h := hm m le_rfl r hr
  have e : (al K a ^ m) • r = algebraMap K.O B.A a ^ m * r := by
    rw [Algebra.smul_def, al, ← map_pow, ← map_pow, ← IsScalarTower.algebraMap_apply]
  rw [e]
  exact h

end GlobalTheory.UnitLemma.Desc
end
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

theorem _root_.GlobalTheory.T.card_lattices_idempotent_position_bounded : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι) (a : K.O), B.P.Separable → K.Small a → IsFrame B e π S → ∀ N : ℕ, ∃ C : ℕ, ∀ p : ι → ℤ, {M : Submodule K.O B.A | Pos B a e N M p}.Finite ∧ {M : Submodule K.O B.A | Pos B a e N M p}.ncard ≤ C := by
  first | exact @GlobalTheory.UnitLemma.Desc.PosCount.card_pos_le | exact GlobalTheory.UnitLemma.Desc.PosCount.card_pos_le | (intros; apply GlobalTheory.UnitLemma.Desc.PosCount.card_pos_le <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

theorem _root_.GlobalTheory.T.adelicGLProjections_mul_infiniteAdelicGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (g : GA E a) (y : GL (Fin a) (Cinf E)), prS S a (g * infGL E a y) = prS S a g * infGL E a y ∧ prO S a (g * infGL E a y) = prO S a g := by
  first | (exact @GlobalTheory.SchurExt.prS_prO_mul_infGL) | (exact GlobalTheory.SchurExt.prS_prO_mul_infGL) | (intros; apply GlobalTheory.SchurExt.prS_prO_mul_infGL <;> assumption)
end
