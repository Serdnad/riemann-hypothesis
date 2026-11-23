module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousFixingSubgroupEquiv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle050
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle276
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle164
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle352
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle426
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle300
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle307
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle453
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle327
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle053
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle454
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open GlobalTheory.Cyc GlobalTheory.Cyc.TwistLift ReciprocityTheory.Gal

namespace GlobalTheory.Cyc.CocycleCount

theorem card_Z1_mul_card_H0 {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M] (rho : Representation R G M) (h : ContAction rho) :
    Nat.card (Z1 rho) * Nat.card (H0 rho) = Nat.card M * Nat.card (H1 rho) := by
  have hker : LinearMap.ker (d0 rho) = H0 rho := by
    ext m
    rw [LinearMap.mem_ker, mem_riemannRochSpace_iff_regularAt_everywhere]
    constructor
    · intro h g
      have hg := congrFun h g
      rw [amitsur_d0_apply, Pi.zero_apply, sub_eq_zero] at hg
      exact hg
    · intro h
      funext g
      rw [amitsur_d0_apply, Pi.zero_apply, h g, sub_self]
  have hM : Nat.card M = Nat.card (H0 rho) * Nat.card (B1 rho) := by
    rw [(LinearMap.ker (d0 rho)).card_eq_card_quotient_mul_card,
      Nat.card_congr (LinearMap.quotKerEquivRange (d0 rho)).toEquiv, hker]
    rfl
  have hZ : Nat.card (Z1 rho) = Nat.card (B1 rho) * Nat.card (H1 rho) := by
    rw [((B1 rho).comap (Z1 rho).subtype).card_eq_card_quotient_mul_card,
      Nat.card_congr (Submodule.comapSubtypeEquivOfLe (coboundaries_le_cocycles rho h)).toEquiv]
  rw [hZ, hM]
  ring

private theorem pow_sub_dvd_val_of_pow_mul_eq_zero {l : ℕ} (hl : 0 < l) (N r : ℕ) [NeZero (l ^ r)] (a : ZMod (l ^ r))
    (ha : (l : ZMod (l ^ r)) ^ N * a = 0) : l ^ (r - N) ∣ a.val := by
  rcases le_or_gt r N with h | h
  · rw [Nat.sub_eq_zero_of_le h, pow_zero]
    exact one_dvd _
  · have h1 : ((l ^ N * a.val : ℕ) : ZMod (l ^ r)) = 0 := by
      push_cast
      rw [ZMod.natCast_zmod_val]
      exact ha
    rw [CharP.cast_eq_zero_iff (ZMod (l ^ r)) (l ^ r)] at h1
    have h2 : l ^ r = l ^ N * l ^ (r - N) := by
      rw [← pow_add, Nat.add_sub_cancel' h.le]
    have h3 : l ^ N * l ^ (r - N) ∣ l ^ N * a.val := by
      rw [← h2]
      exact h1
    exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hl N) h3

private theorem card_le_pow_of_injective_of_pow_mul_eq_zero {l : ℕ} [Fact l.Prime] (N r : ℕ) {X : Type*} (f : X → ZMod (l ^ r))
    (hf : Function.Injective f) (hann : ∀ x, (l : ZMod (l ^ r)) ^ N * f x = 0) :
    Nat.card X ≤ l ^ N := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have : NeZero (l ^ r) := ⟨(pow_pos hl r).ne'⟩
  let g : X → Fin (l ^ N) := fun x => ⟨(f x).val / l ^ (r - N), by
    rw [Nat.div_lt_iff_lt_mul (pow_pos hl _), ← pow_add]
    calc (f x).val < l ^ r := ZMod.val_lt _
      _ ≤ l ^ (N + (r - N)) := Nat.pow_le_pow_right hl (by omega)⟩
  have hg : Function.Injective g := by
    intro x y hxy
    apply hf
    apply ZMod.val_injective
    have hx := pow_sub_dvd_val_of_pow_mul_eq_zero hl N r (f x) (hann x)
    have hy := pow_sub_dvd_val_of_pow_mul_eq_zero hl N r (f y) (hann y)
    have e : (f x).val / l ^ (r - N) = (f y).val / l ^ (r - N) := congrArg Fin.val hxy
    rw [← Nat.div_mul_cancel hx, ← Nat.div_mul_cancel hy, e]
  have hc := Nat.card_le_card_of_injective g hg
  simpa using hc

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G]

theorem card_invariants_twistedDual_charRep_le_pow (χ ψ : G →* ℤ_[l]ˣ) (N r : ℕ)
    (g₀ : G) (hg : ‖(χ g₀ : ℤ_[l]) * (ψ g₀⁻¹ : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(N : ℤ))) :
    Finite (H0 ((twDual (redChar χ r) (charRep (redChar ψ r))).comp (MonoidHom.id G))) ∧
    Nat.card (H0 ((twDual (redChar χ r) (charRep (redChar ψ r))).comp (MonoidHom.id G))) ≤
      l ^ N := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have : NeZero (l ^ r) := ⟨(pow_pos hl r).ne'⟩
  have key : ∀ (φ : TDual (ZMod (l ^ r)) (ZMod (l ^ r))) (m : ZMod (l ^ r)), φ m = m * φ 1 := by
    intro φ m
    have h := LinearMap.map_smul (show Module.Dual (ZMod (l ^ r)) (ZMod (l ^ r)) from φ) m 1
    rw [smul_eq_mul, smul_eq_mul, mul_one] at h
    exact h
  let f : H0 ((twDual (redChar χ r) (charRep (redChar ψ r))).comp (MonoidHom.id G)) →
      ZMod (l ^ r) := fun x => x.1 1
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply LinearMap.ext
    intro m
    change x.1 m = y.1 m
    rw [key x.1 m, key y.1 m]
    exact congrArg (m * ·) hxy
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1
    ((PadicInt.norm_le_pow_iff_mem_span_pow _ N).1 hg.le)
  have hpos : (0 : ℝ) < (l : ℝ) ^ (-(N : ℤ)) := zpow_pos (by exact_mod_cast hl) _
  have hvn : ‖v‖ = 1 := by
    have hn := congrArg norm hv
    rw [norm_mul, PadicInt.norm_p_pow, hg] at hn
    exact mul_right_cancel₀ hpos.ne' (hn.trans (one_mul _).symm)
  have hvu : IsUnit (PadicInt.toZModPow r v) := (PadicInt.isUnit_iff.2 hvn).map _
  have hred : (redChar χ r g₀ : ZMod (l ^ r)) * (redChar ψ r g₀⁻¹ : ZMod (l ^ r)) - 1 =
      PadicInt.toZModPow r v * (l : ZMod (l ^ r)) ^ N := by
    have e := congrArg (PadicInt.toZModPow r) hv
    simp only [map_mul, map_pow, map_natCast, map_sub, map_one] at e
    rw [redChar_apply, redChar_apply, e]
  have hann : ∀ x, (l : ZMod (l ^ r)) ^ N * f x = 0 := by
    intro x
    have h0 : ∀ g, twDual (redChar χ r) (charRep (redChar ψ r)) g x.1 = x.1 := by
      have hx := x.2
      exact hx
    have h1 := congrArg (fun φ : TDual (ZMod (l ^ r)) (ZMod (l ^ r)) => φ 1) (h0 g₀)
    simp only [twDual_apply, charRep_apply, mul_one] at h1
    rw [key x.1] at h1
    have h2 : ((redChar χ r g₀ : ZMod (l ^ r)) * (redChar ψ r g₀⁻¹ : ZMod (l ^ r)) - 1) * f x = 0 := by
      show _ * x.1 1 = 0
      linear_combination h1
    rw [hred, mul_assoc] at h2
    exact hvu.mul_right_eq_zero.1 h2
  exact ⟨Finite.of_injective f hf, card_le_pow_of_injective_of_pow_mul_eq_zero N r f hf hann⟩

theorem card_cocycles_charRep_modPow_le_of_duality : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (χ ψ : G →* ℤ_[l]ˣ), (Continuous fun g => (ψ g : ℤ_[l])) → ∀ (N r d : ℕ) (g₀ : G), ‖(χ g₀ : ℤ_[l]) * (ψ g₀⁻¹ : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(N : ℤ)) → Nonempty (ReciprocityTheory.Gal.H2 (ReciprocityTheory.Gal.charRep (redChar χ r)) ≃ₗ[ZMod (l ^ r)] ZMod (l ^ r)) → Function.Injective (ReciprocityTheory.Gal.cup20 (redChar χ r) (ReciprocityTheory.Gal.charRep (redChar ψ r)) (MonoidHom.id G)) → Nat.card (ReciprocityTheory.Gal.H1 (ReciprocityTheory.Gal.charRep (redChar ψ r))) = Nat.card (ReciprocityTheory.Gal.H0 (ReciprocityTheory.Gal.charRep (redChar ψ r))) * Nat.card (ReciprocityTheory.Gal.H2 (ReciprocityTheory.Gal.charRep (redChar ψ r))) * Nat.card (ZMod (l ^ r)) ^ d → Finite (ReciprocityTheory.Gal.Z1 (ReciprocityTheory.Gal.charRep (redChar ψ r))) ∧ Nat.card (ReciprocityTheory.Gal.Z1 (ReciprocityTheory.Gal.charRep (redChar ψ r))) ≤ l ^ N * l ^ (r * (d + 1)) := by
  intro l _ G _ _ _ χ ψ hψ N r d g₀ hg hH2 hinj hH1
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have : NeZero (l ^ r) := ⟨(pow_pos hl r).ne'⟩
  have hcont : ContAction (charRep (redChar ψ r)) := by
    apply contAction_charRep
    have e : (fun g => ((redChar ψ r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r))) =
        fun g => PadicInt.toZModPow r (ψ g : ℤ_[l]) := funext fun g => redChar_apply ψ r g
    rw [e]
    exact (continuous_toZModPow r).comp hψ
  have h1 := card_Z1_mul_card_H0 (charRep (redChar ψ r)) hcont
  obtain ⟨hfin0, hle0⟩ := card_invariants_twistedDual_charRep_le_pow χ ψ N r g₀ hg
  obtain ⟨e⟩ := hH2
  let F : H2 (charRep (redChar ψ r)) →
      (H0 ((twDual (redChar χ r) (charRep (redChar ψ r))).comp (MonoidHom.id G)) →+ ZMod (l ^ r)) :=
    fun c => (e.toLinearMap ∘ₗ
      (cup20 (redChar χ r) (charRep (redChar ψ r)) (MonoidHom.id G) c)).toAddMonoidHom
  have hF : Function.Injective F := by
    intro c c' hcc
    apply hinj
    apply LinearMap.ext
    intro y
    apply e.injective
    exact DFunLike.congr_fun hcc y
  have : Finite (H0 ((twDual (redChar χ r) (charRep (redChar ψ r))).comp (MonoidHom.id G)) →+
      ZMod (l ^ r)) := Finite.of_injective _ DFunLike.coe_injective
  have : Finite (H2 (charRep (redChar ψ r))) := Finite.of_injective F hF
  have hc2 : Nat.card (H2 (charRep (redChar ψ r))) ≤ l ^ N :=
    ((Nat.card_le_card_of_injective F hF).trans
      (GlobalTheory.natCard_addMonoidHom_zmod_le (l ^ r) _)).trans hle0
  have hc2pos : 0 < Nat.card (H2 (charRep (redChar ψ r))) := Nat.card_pos
  have h0pos : 0 < Nat.card (H0 (charRep (redChar ψ r))) := Nat.card_pos
  have hZ : Nat.card (Z1 (charRep (redChar ψ r))) =
      l ^ r * (Nat.card (H2 (charRep (redChar ψ r))) * (l ^ r) ^ d) := by
    apply Nat.eq_of_mul_eq_mul_right h0pos
    rw [h1, hH1, Nat.card_zmod]
    ring
  refine ⟨Nat.finite_of_card_ne_zero (by rw [hZ]; positivity), ?_⟩
  rw [hZ]
  calc l ^ r * (Nat.card (H2 (charRep (redChar ψ r))) * (l ^ r) ^ d)
      ≤ l ^ r * (l ^ N * (l ^ r) ^ d) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hc2)
    _ = l ^ N * l ^ (r * (d + 1)) := by ring

end GlobalTheory.Cyc.CocycleCount
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

noncomputable section

namespace GlobalTheory.ExpImage.Sum

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem frob_π₁ : WittVector.frobenius AI.π₁ = AI.μ := by
  rw [LocAinf.π₁, LocAinf.μ, map_sub, map_one, WittVector.frobenius_eq_map_frobenius,
    WittVector.map_teichmuller]
  congr 2
  exact (frobeniusEquiv (OCb l) l).apply_symm_apply AI.ε

theorem act_μ {K : FinExt l} {h : GQ l} (hh : h ∈ Hinf K) : AI.actW h AI.μ = AI.μ := by
  have h1 : P.χQ h = 1 :=
    ((GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.2 K h (Hinf_le_fix hh)).2.mp hh
  have h2 := GlobalTheory.T.cyclotomic_action_on_root_tower l P AI h 1 (by rw [h1]; simp) 0
  have h3 : AI.actT h AI.ε = AI.ε := by simpa [LocAinf.εroot] using h2
  rw [LocAinf.μ, map_sub, map_one, LocAinf.actW, WittVector.map_teichmuller]
  congr 2

theorem step_dR (T : LocTied l P AI) {g : GQ l} {U : ℤ_[l]} {k : ℕ} {β r : Ainf l} {u : P.R.BdR}
    (hu : io AI AI.π₁ * u = 1) (h : Step AI g U AI.π₁ k β r) :
    qB P (U : ℚ_[l]) * P.actQdR g (io AI β * u ^ k) - io AI β * u ^ k = io AI r * u ^ k := by
  have e := congrArg (io AI) h
  simp only [map_sub, map_mul, map_pow, io_act, io_zl AI T] at e
  have h1 : io AI AI.π₁ ^ k * u ^ k = 1 := by rw [← mul_pow, hu, one_pow]
  have h2 : P.actQdR g (io AI AI.π₁) ^ k * P.actQdR g u ^ k = 1 := by
    rw [← mul_pow, ← map_mul, hu, map_one, one_pow]
  rw [map_mul, map_pow]
  linear_combination (u ^ k * P.actQdR g u ^ k) * e
    - (qB P (U : ℚ_[l]) * P.actQdR g (io AI β) * P.actQdR g u ^ k) * h1
    + (io AI β * u ^ k + io AI r * u ^ k) * h2

theorem limit (T : LocTied l P AI) {M : ℕ} (hM : 1 ≤ M) (g : GQ l) (U : ℤ_[l]) (b v : P.R.BdR)
    (S E : ℕ → P.R.BdR)
    (hb : ∀ n : ℕ, ∃ R₀ : ℕ, ∀ R ≥ R₀, b - S R ∈ Lat AI M n)
    (hE : ∀ n : ℕ, ∃ R₀ : ℕ, ∀ R ≥ R₀, E R ∈ Lat AI M n)
    (hS : ∀ R, ∃ z : ℤ_[l], v + (qB P (U : ℚ_[l]) * P.actQdR g (S R) - S R) = qB P (z : ℚ_[l]) - E R) :
    NearZ P M (v + (qB P (U : ℚ_[l]) * P.actQdR g b - b)) := by
  refine GlobalTheory.T.padicInt_add_fil_closed_in_deRhamPeriodRing l P AI T M hM _ fun n => ?_
  obtain ⟨R₀, h₀⟩ := hb n
  obtain ⟨R₁, h₁⟩ := hE n
  obtain ⟨z, hz⟩ := hS (max R₀ R₁)
  have a := h₀ _ (le_max_left R₀ R₁)
  have a' := h₁ _ (le_max_right R₀ R₁)
  refine ⟨z, ?_⟩
  have := add_mem (sub_mem a (qB_mul_mem_Lat AI T U (act_mem_Lat AI g a))) a'
  convert this using 1
  rw [map_sub]
  linear_combination -hz

theorem telescope (g : GQ l) (U : ℤ_[l]) (s : ℕ) (B H : ℕ → P.R.BdR)
    (h : ∀ k, ∃ z : ℤ_[l], qB P (U : ℚ_[l]) * P.actQdR g (B k) - B k =
      H k - (l : P.R.BdR) ^ s * H (k + 1) + qB P (z : ℚ_[l])) (R : ℕ) :
    ∃ z : ℤ_[l], -H 0 + (qB P (U : ℚ_[l]) *
        P.actQdR g (∑ k ∈ Finset.range R, (l : P.R.BdR) ^ (s * k) * B k) -
        ∑ k ∈ Finset.range R, (l : P.R.BdR) ^ (s * k) * B k) =
      qB P (z : ℚ_[l]) - (l : P.R.BdR) ^ (s * R) * H R := by
  induction R with
  | zero => exact ⟨0, by simp⟩
  | succ R ih =>
    obtain ⟨z, hz⟩ := ih
    obtain ⟨w, hw⟩ := h R
    refine ⟨z + (l : ℤ_[l]) ^ (s * R) * w, ?_⟩
    rw [Finset.sum_range_succ, map_add (f := _), map_mul, map_pow, map_natCast]
    rw [PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast,
      map_add, map_mul, map_pow, map_natCast, mul_add s R 1, pow_add, mul_one]
    linear_combination hz + (l : P.R.BdR) ^ (s * R) * hw

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (g : GQ l) (U : ℤ_[l]) (M : ℕ), 1 ≤ M → ∀ y : Ainf l, Solv AI K s g U (y - WittVector.frobenius y) → ∃ b ∈ FilB P 0, (∀ h ∈ Hinf K, NearZ P M (P.actQdR h b - b)) ∧ NearZ P M (io AI y + (qB P (U : ℚ_[l]) * P.actQdR g b - b)) := by
  intro l _ P AI T K s hs g U M hM y ⟨p, q, hq0, hp, hstep⟩
  have asw := (GlobalTheory.ArtinSchreierWitt.main l).2.2
  choose β hβ using fun k : ℕ => asw (AI.ξ ^ (k + 1)) (p k)
  have hη' : ∀ k : ℕ, ∃ η : Ainf l, WittVector.frobenius η - AI.ξ ^ k * η = q k ∧ (k = 0 → η = -y) := by
    intro k
    rcases k with _ | k
    · exact ⟨-y, by rw [hq0, map_neg]; ring, fun _ => rfl⟩
    · obtain ⟨η, h⟩ := asw (AI.ξ ^ (k + 1)) (q (k + 1))
      exact ⟨η, h, fun h => absurd h (Nat.succ_ne_zero k)⟩
  choose η hη hη0 using hη'
  obtain ⟨u, hu0, hu⟩ := GlobalTheory.T.exists_inv_io_pi_alt l P AI T
  have small := GlobalTheory.T.prime_pow_mul_inv_pow_mem_ainfFilLattice l P AI s hs u hu0 hu M
  obtain ⟨b, hb0, hb⟩ := GlobalTheory.T.exists_series_limit_Lat_alt l P AI M
    (fun k => (l : P.R.BdR) ^ (s * k) * (io AI (β k) * u ^ (k + 1)))
    (fun k => by
      have h1 : (l : P.R.BdR) ^ (s * k) * io AI (β k) ∈ FilB P 0 := by
        simpa using io_mem AI (((l : ℕ) : Ainf l) ^ (s * k) * β k)
      have h2 : u ^ (k + 1) ∈ FilB P 0 := by simpa using FilB_pow hu0 (k + 1)
      rw [← mul_assoc]
      exact FilB_zero_mul h1 h2)
    (fun n => by
      obtain ⟨k₀, h⟩ := small n
      exact ⟨k₀, fun k hk => by rw [← mul_assoc]; exact h k hk _⟩)
  have h1 : ∀ k, io AI AI.π₁ ^ k * u ^ k = 1 := fun k => by rw [← mul_pow, hu, one_pow]
  refine ⟨b, hb0, fun h hh => ?_, ?_⟩
  · have key : ∀ k, ∃ z : ℤ_[l], qB P ((1 : ℤ_[l]) : ℚ_[l]) * P.actQdR h (io AI (β k) * u ^ (k + 1)) -
        io AI (β k) * u ^ (k + 1) = (0 : P.R.BdR) - (l : P.R.BdR) ^ s * 0 + qB P (z : ℚ_[l]) := by
      intro k
      obtain ⟨z, hz⟩ := GlobalTheory.T.exists_ainfCocycleRecursion_of_frobenius_twist l P AI h 1 (k + 1) (β k) 0 (by
        rw [hβ]
        unfold Step
        rw [hp k h hh, act_μ AI hh]
        simp [mul_comm])
      refine ⟨z, ?_⟩
      rw [step_dR AI T hu hz, zero_add, map_mul, map_pow, io_zl AI T, mul_assoc, h1]
      ring
    have := limit AI T hM h 1 b 0 _ (fun _ => 0) hb (fun n => ⟨0, fun _ _ => zero_mem _⟩)
      (fun R => by
        simpa using telescope h 1 s (fun k => io AI (β k) * u ^ (k + 1)) (fun _ => 0) key R)
    simpa using this
  · have key : ∀ k, ∃ z : ℤ_[l], qB P (U : ℚ_[l]) * P.actQdR g (io AI (β k) * u ^ (k + 1)) -
        io AI (β k) * u ^ (k + 1) = io AI (η k) * u ^ k -
          (l : P.R.BdR) ^ s * (io AI (η (k + 1)) * u ^ (k + 1)) + qB P (z : ℚ_[l]) := by
      intro k
      obtain ⟨z, hz⟩ := GlobalTheory.T.exists_ainfCocycleRecursion_of_frobenius_twist l P AI g U (k + 1) (β k)
        (AI.π₁ * η k - ((l : ℕ) : Ainf l) ^ s * η (k + 1)) (by
        rw [hβ]
        convert hstep k using 1
        rw [← hη k, ← hη (k + 1), map_sub, map_mul, map_mul, map_pow, map_natCast, frob_π₁, AI.μ_eq]
        ring)
      refine ⟨z, ?_⟩
      rw [step_dR AI T hu hz]
      simp only [map_add (f := _), map_sub, map_mul, map_pow, map_natCast, io_zl AI T]
      linear_combination (io AI (η k) * u ^ k) * hu + qB P (z : ℚ_[l]) * h1 (k + 1)
    refine limit AI T hM g U b _ _ (fun R => (l : P.R.BdR) ^ (s * R) * (io AI (η R) * u ^ R)) hb
      (fun n => ?_) (fun R => ?_)
    · obtain ⟨k₀, h⟩ := small n
      refine ⟨k₀, fun R hR => ?_⟩
      convert h R hR (η R * AI.π₁) using 1
      rw [map_mul]
      linear_combination (-(l : P.R.BdR) ^ (s * R) * (io AI (η R) * u ^ R)) * hu
    · have := telescope g U s (fun k => io AI (β k) * u ^ (k + 1)) (fun k => io AI (η k) * u ^ k) key R
      simpa only [hη0 0 rfl, map_neg, pow_zero, mul_one, neg_neg] using this

end GlobalTheory.ExpImage.Sum
end
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LlcTame

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

end GlobalTheory.LlcTame

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial in
attribute [local instance] _root_.GlobalTheory.LocalData.complRel _root_.GlobalTheory.LocalData.isLocalField in
private theorem eq_one_of_isSemisimple_of_charpoly_eq {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : Module.End ℂ V) (hs : f.IsSemisimple)
    (hc : f.charpoly = (X - 1) ^ Module.finrank ℂ V) : f = 1 := by
  have hn : IsNilpotent (f - 1) := by
    refine ⟨Module.finrank ℂ V, ?_⟩
    have := LinearMap.aeval_self_charpoly f
    rw [hc] at this
    simpa using this
  have hs' : (f - 1).IsSemisimple :=
    hs.sub_of_commute (Commute.one_right f) Module.End.isSemisimple_id
  exact sub_eq_zero.mp (Module.End.eq_zero_of_isNilpotent_isSemisimple hn hs')

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial in
attribute [local instance] _root_.GlobalTheory.LocalData.complRel _root_.GlobalTheory.LocalData.isLocalField in
theorem _root_.GlobalTheory.LlcTame.isTameWD_iff_charPol : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (y : _root_.GlobalTheory.WeilDeligne.WD h), _root_.GlobalTheory.LocLanglands.IsTameWD y ↔
    ∀ σ : _root_.GlobalTheory.WeilDeligne.Weil h, _root_.Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : _root_.Formalism.ConjugateSelfDual.G E Ω) →
      y.charPol σ = (X - 1) ^ y.lpDim := by
  intro E Ω _ _ _ _ _ A w h y
  unfold _root_.GlobalTheory.LocLanglands.IsTameWD
  constructor
  · rintro ⟨n, a, rfl, ha⟩ σ hσ
    have hd : (_root_.GlobalTheory.WeilDeligne.WD.mk a).lpDim =
        Module.finrank ℂ (Fin n → ℂ) := _root_.GlobalTheory.WeilDeligne.WD.lpDim_mk a
    refine (_root_.GlobalTheory.WeilDeligne.WD.charPol_mk a σ).trans ?_
    rw [hd, ha σ hσ, LinearMap.charpoly_one]
  · intro H
    obtain ⟨n, a, rfl⟩ := y.exists_rep
    refine ⟨n, a, rfl, fun σ hσ => ?_⟩
    have hc := H σ hσ
    have hd : (_root_.GlobalTheory.WeilDeligne.WD.mk a).lpDim =
        Module.finrank ℂ (Fin n → ℂ) := _root_.GlobalTheory.WeilDeligne.WD.lpDim_mk a
    rw [hd] at hc
    have hc' := (_root_.GlobalTheory.WeilDeligne.WD.charPol_mk a σ).symm.trans hc
    exact eq_one_of_isSemisimple_of_charpoly_eq _ (a.semisimple σ) hc'
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

noncomputable section

namespace GlobalTheory.NuShift

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem lpChar_lpTw (x y : WD h) (s : ℝ) : (x.lpTw s).lpChar y = (x.lpChar y).lpTw s := by
  induction x using WD.ind with
  | hP n a =>
  induction y using WD.ind with
  | hP m b =>
  rw [WD.lpTw_mk, WD.lpChar_mk, WD.lpChar_mk, WD.lpTw_mk]
  refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => ?_⟩
  · simp only [WDRep.tensor_ρ, WDRep.tw_ρ, LinearEquiv.refl_apply, TensorProduct.map_smul_left]
  · rfl

theorem lpTw_lpZero (s : ℝ) : (WD.lpZero (h := h)).lpTw s = WD.lpZero (h := h) := by
  rw [WD.lpZero, WD.lpTw_mk]
  exact WD.sound ⟨.refl _ _, fun σ v => Subsingleton.elim _ _, fun v => Subsingleton.elim _ _⟩

theorem sumList_lpTw (l : List (WD h)) (s : ℝ) :
    sumList (l.map fun x => x.lpTw s) = (sumList l).lpTw s := by
  induction l with
  | nil => exact (lpTw_lpZero s).symm
  | cons x l ih =>
    show WD.lpSum _ (sumList _) = (WD.lpSum x (sumList l)).lpTw s
    rw [ih, WD.lpTw_sum]

end GlobalTheory.NuShift

namespace GlobalTheory

open GlobalTheory.NuShift

theorem lpSum_segments_nu : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)),
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    ∀ (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRec h rc →
    ∀ (l : List (Segment (w.adicCompletion E))) (c : ℝ),
      sumList ((l.map fun Γ => Γ.nu (c : ℂ)).map fun Δ =>
          ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len)) =
        (sumList (l.map fun Δ =>
          ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len))).lpTw c := by
  intro E Ω _ _ _ _ _ A w
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  intro h rc hrc l c
  obtain ⟨a, ha, ε, -, L⟩ := hrc
  rw [← sumList_lpTw, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun Γ _ => ?_
  show ((rc (Γ.first.nu (c : ℂ))).lpTw _).lpChar _ = _
  rw [L.nu_eq, WD.lpTw_add, add_comm, ← WD.lpTw_add, lpChar_lpTw]
  rfl

end GlobalTheory
end
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.irreducible_GL1_is_character : BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL (k := k)), x.1 = 1 → ∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), x = IrrGL.ofChar χ hχ := by
  first | exact @GlobalTheory.LocLanglands.DegreeOne.classOfDegreeOne_eq_ofChar | exact GlobalTheory.LocLanglands.DegreeOne.classOfDegreeOne_eq_ofChar | (intros; apply GlobalTheory.LocLanglands.DegreeOne.classOfDegreeOne_eq_ofChar <;> assumption)
end
