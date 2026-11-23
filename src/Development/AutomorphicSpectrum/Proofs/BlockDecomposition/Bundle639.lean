module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle622
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle293
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle626
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle011
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StagedDisintegrationComposition
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle107
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal

namespace GlobalTheory.CompanionTheory.KFin.EvenAniso

section Form

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {c : R →+* R} {h : V → V → R}

theorem add_left (hH : IsHerm c h) (x y z : V) : h (x + y) z = h x z + h y z := by
  rw [hH.symm z (x + y), hH.add_right, map_add (f := _), ← hH.symm z x, ← hH.symm z y]

theorem smul_left (hH : IsHerm c h) (a : R) (x y : V) : h (a • x) y = c a * h x y := by
  rw [hH.symm y (a • x), hH.smul_right, map_mul, ← hH.symm y x]

theorem zero_left (hH : IsHerm c h) (y : V) : h 0 y = 0 := by
  rw [← zero_smul R (0 : V), smul_left hH, map_zero, zero_mul]

theorem zero_right (hH : IsHerm c h) (x : V) : h x 0 = 0 := by
  rw [← zero_smul R (0 : V), hH.smul_right, zero_mul]

end Form

theorem le_one_of_mul_self {γ : ℝ≥0} (h : γ * γ ≤ 1) : γ ≤ 1 := by
  by_contra hc
  have hg : 1 < γ := not_le.mp hc
  have hgg : 1 < γ * γ := by
    calc (1 : ℝ≥0) = 1 * 1 := (one_mul 1).symm
      _ < γ * γ := mul_lt_mul'' hg hg zero_le zero_le
  exact absurd h (not_le.mpr hgg)

theorem pair_mem_of_even : ∀ {k R V : Type} [Field k] [CommRing R] [Algebra k R] [AddCommGroup V] [Module R V] (c : R →+* R) (𝔬 : Subring R) (W : Valuation R ℝ≥0), (∀ a : R, a ≠ 0 → ∃ b : R, a * b = 1) → (∀ a, c (c a) = a) → (∀ a, c a = a → ∃ x : k, algebraMap k R x = a) → (∀ x : k, c (algebraMap k R x) = algebraMap k R x) → (∀ a, a ∈ 𝔬 ↔ W a ≤ 1) → (∀ a, W (c a) = W a) → (∀ a, W a = 0 → a = 0) → (∀ e : k, W (algebraMap k R e) < 1 → ∃ u : k, u * u + u + e = 0) → ∀ h : V → V → R, IsHerm c h → (∀ z, h z z = 0 → z = 0) → ∀ (z w : V) (a b : R), a ∈ 𝔬 → b ∈ 𝔬 → h z z = a + c a → h w w = b + c b → h z w ∈ 𝔬 := by
  intro k R V _ _ _ _ _ c 𝔬 W hinv hcc hfix hck h𝔬 hWc hW0 hhen h hH hanis z w a b ha hb hzz hww
  rw [h𝔬]
  by_contra hlt
  have hs1 : 1 < W (h z w) := not_le.mp hlt
  have hsym : ∀ x y : V, h y x = c (h x y) := hH.symm
  have hself : ∀ x : V, c (h x x) = h x x := fun x => (hH.symm x x).symm
  have hWnorm : ∀ x : R, W (x * c x) = W x * W x := fun x => by rw [W.map_mul, hWc]
  have hWtr : ∀ x : R, W x ≤ 1 → W (x + c x) ≤ 1 := fun x hx =>
    le_trans (W.map_add x (c x)) (max_le hx (by rw [hWc]; exact hx))
  have hne : ∀ x : R, x ≠ 0 → W x ≠ 0 := fun x hx h0 => hx (hW0 x h0)
  have hnz : ∀ z w : V, 1 < W (h z w) → h z z ≠ 0 ∧ h w w ≠ 0 := by
    intro z w hs
    constructor
    · intro h0
      rw [hanis z h0, GlobalTheory.CompanionTheory.KFin.EvenAniso.zero_left hH, W.map_zero] at hs
      exact absurd hs (not_lt.mpr zero_le)
    · intro h0
      rw [hanis w h0, GlobalTheory.CompanionTheory.KFin.EvenAniso.zero_right hH, W.map_zero] at hs
      exact absurd hs (not_lt.mpr zero_le)
  have core : ∀ (z w : V) (a b : R), W a ≤ 1 → W b ≤ 1 → h z z = a + c a → h w w = b + c b →
      1 < W (h z w) →
      W (a * c a * h w w) < W (h z w * c (h z w) * h z z) → False := by
    intro z w a b ha hb hzz hww hs hlt'
    obtain ⟨hA, hB⟩ := hnz z w hs
    have hs0 : W (h z w) ≠ 0 := (lt_trans zero_lt_one hs).ne'
    have hA0 : W (h z z) ≠ 0 := hne _ hA
    have hB0 : W (h w w) ≠ 0 := hne _ hB
    have ha0 : W a ≠ 0 := by
      intro h0
      apply hA
      rw [hzz, hW0 a h0, map_zero, add_zero]
    have hD : h z w * c (h z w) * h z z ≠ 0 := by
      intro h0
      have h0' := congrArg W h0
      rw [W.map_zero, W.map_mul, hWnorm] at h0'
      exact mul_ne_zero (mul_ne_zero hs0 hs0) hA0 h0'
    obtain ⟨Dinv, hDinv⟩ := hinv _ hD
    have hcD : c (h z w * c (h z w) * h z z) = h z w * c (h z w) * h z z := by
      rw [map_mul, map_mul, hcc, hself z]; ring
    have hcDinv : c Dinv = Dinv := by
      have h1 : (h z w * c (h z w) * h z z) * c Dinv = 1 := by
        rw [← hcD, ← map_mul, hDinv, map_one]
      calc c Dinv = c Dinv * ((h z w * c (h z w) * h z z) * Dinv) := by rw [hDinv, mul_one]
        _ = ((h z w * c (h z w) * h z z) * c Dinv) * Dinv := by ring
        _ = Dinv := by rw [h1, one_mul]
    have hce : c (a * c a * h w w * Dinv) = a * c a * h w w * Dinv := by
      rw [map_mul, map_mul, map_mul, hcc, hself w, hcDinv]; ring
    obtain ⟨e', he'⟩ := hfix _ hce
    have hWDD : W (h z w * c (h z w) * h z z) * W Dinv = 1 := by
      rw [← W.map_mul, hDinv, W.map_one]
    have hWDinv : 0 < W Dinv := by
      rcases (zero_le : (0 : ℝ≥0) ≤ W Dinv).lt_or_eq with h0 | h0
      · exact h0
      · rw [← h0, mul_zero] at hWDD
        exact absurd hWDD zero_ne_one
    have hWe : W (algebraMap k R e') < 1 := by
      rw [he', W.map_mul, ← hWDD]
      exact mul_lt_mul_of_pos_right hlt' hWDinv
    obtain ⟨m, hm⟩ := hhen e' hWe
    have hM' : algebraMap k R m * algebraMap k R m + algebraMap k R m + a * c a * h w w * Dinv = 0 := by
      have hm' := congrArg (algebraMap k R) hm
      rw [map_add (f := _), map_add (f := _), map_mul, map_zero, he'] at hm'
      exact hm'
    have hcM' : c (algebraMap k R m) = algebraMap k R m := hck m
    obtain ⟨M, hMdef⟩ : ∃ M, algebraMap k R m = M := ⟨_, rfl⟩
    rw [hMdef] at hM' hcM'
    have hkey : (M * M + M) * (h z w * c (h z w) * h z z) + a * c a * h w w = 0 := by
      linear_combination (h z w * c (h z w) * h z z) * hM' - (a * c a * h w w) * hDinv
    have hv : h ((c a * h w w) • z + (h z z * M * c (h z w)) • w)
        ((c a * h w w) • z + (h z z * M * c (h z w)) • w) = 0 := by
      simp only [GlobalTheory.CompanionTheory.KFin.EvenAniso.add_left hH, hH.add_right,
        GlobalTheory.CompanionTheory.KFin.EvenAniso.smul_left hH, hH.smul_right, map_mul, hcc, hself, hcM']
      rw [hsym z w]
      linear_combination (h z z * h w w) * hkey - (h z z * h w w * M * h z w * c (h z w)) * hzz
    have hv0 := hanis _ hv
    have e1 : h ((c a * h w w) • z + (h z z * M * c (h z w)) • w) w = 0 := by
      rw [hv0, GlobalTheory.CompanionTheory.KFin.EvenAniso.zero_left hH]
    have e2 : h ((c a * h w w) • z + (h z z * M * c (h z w)) • w) z = 0 := by
      rw [hv0, GlobalTheory.CompanionTheory.KFin.EvenAniso.zero_left hH]
    simp only [GlobalTheory.CompanionTheory.KFin.EvenAniso.add_left hH, GlobalTheory.CompanionTheory.KFin.EvenAniso.smul_left hH, map_mul,
      hcc, hself, hcM'] at e1 e2
    rw [hsym z w] at e2
    have hfac1 : h w w * h z w * (a + h z z * M) = 0 := by linear_combination e1
    have hfac2 : h z z * (a * h w w + M * (h z w * c (h z w))) = 0 := by linear_combination e2
    have f1 : a + h z z * M = 0 := by
      apply hW0
      have h0' := congrArg W hfac1
      rw [W.map_zero, W.map_mul, W.map_mul] at h0'
      exact (mul_eq_zero.mp h0').resolve_left (mul_ne_zero hB0 hs0)
    have f2 : a * h w w + M * (h z w * c (h z w)) = 0 := by
      apply hW0
      have h0' := congrArg W hfac2
      rw [W.map_zero, W.map_mul] at h0'
      exact (mul_eq_zero.mp h0').resolve_left hA0
    have g1 : W a = W (h z z) * W M := by
      rw [eq_neg_of_add_eq_zero_left f1, W.map_neg, W.map_mul]
    have g2 : W a * W (h w w) = W M * (W (h z w) * W (h z w)) := by
      rw [← W.map_mul a (h w w), eq_neg_of_add_eq_zero_left f2, W.map_neg, W.map_mul, hWnorm]
    have hM0 : W M ≠ 0 := fun h0 => ha0 (by rw [g1, h0, mul_zero])
    have g3 : W (h z w) * W (h z w) = W (h z z) * W (h w w) := by
      apply mul_left_cancel₀ hM0
      rw [← g2, g1]; ring
    have hAle : W (h z z) ≤ 1 := by rw [hzz]; exact hWtr a ha
    have hBle : W (h w w) ≤ 1 := by rw [hww]; exact hWtr b hb
    have hss : W (h z w) * W (h z w) ≤ 1 := by
      rw [g3]
      calc W (h z z) * W (h w w) ≤ 1 * 1 := mul_le_mul hAle hBle zero_le zero_le
        _ = 1 := one_mul 1
    exact absurd hs (not_lt.mpr (GlobalTheory.CompanionTheory.KFin.EvenAniso.le_one_of_mul_self hss))
  have ha1 : W a ≤ 1 := (h𝔬 a).mp ha
  have hb1 : W b ≤ 1 := (h𝔬 b).mp hb
  rcases lt_or_ge (W (a * c a * h w w)) (W (h z w * c (h z w) * h z z)) with hc1 | hc1
  · exact core z w a b ha1 hb1 hzz hww hs1 hc1
  have hs2 : 1 < W (h w z) := by rw [hsym z w, hWc]; exact hs1
  rcases lt_or_ge (W (b * c b * h z z)) (W (h w z * c (h w z) * h w w)) with hc2 | hc2
  · exact core w z b a hb1 ha1 hww hzz hs2 hc2
  obtain ⟨hA, hB⟩ := hnz z w hs1
  have hA0 : W (h z z) ≠ 0 := hne _ hA
  have hB0 : W (h w w) ≠ 0 := hne _ hB
  rw [hsym z w] at hc2
  simp only [W.map_mul, hWc] at hc1 hc2
  have hm1 : ∀ x y : ℝ≥0, x ≤ 1 → y ≤ 1 → x * y ≤ 1 := fun x y hx hy => by
    calc x * y ≤ 1 * 1 := mul_le_mul hx hy zero_le zero_le
      _ = 1 := one_mul 1
  have hprod := mul_le_mul hc1 hc2 zero_le zero_le
  have hAB : 0 < W (h z z) * W (h w w) := pos_iff_ne_zero.mpr (mul_ne_zero hA0 hB0)
  have h4 : W (h z w) * W (h z w) * (W (h z w) * W (h z w)) ≤ W a * W a * (W b * W b) := by
    refine le_of_mul_le_mul_right ?_ hAB
    calc W (h z w) * W (h z w) * (W (h z w) * W (h z w)) * (W (h z z) * W (h w w))
        = W (h z w) * W (h z w) * W (h z z) * (W (h z w) * W (h z w) * W (h w w)) := by ring
      _ ≤ W a * W a * W (h w w) * (W b * W b * W (h z z)) := hprod
      _ = W a * W a * (W b * W b) * (W (h z z) * W (h w w)) := by ring
  have h5 := le_trans h4 (hm1 _ _ (hm1 _ _ ha1 ha1) (hm1 _ _ hb1 hb1))
  have h6 := GlobalTheory.CompanionTheory.KFin.EvenAniso.le_one_of_mul_self (GlobalTheory.CompanionTheory.KFin.EvenAniso.le_one_of_mul_self h5)
  exact absurd hs1 (not_lt.mpr h6)

end GlobalTheory.CompanionTheory.KFin.EvenAniso
end

section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.KFin.RingHyp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)}

theorem sigR_sigR (h : IsCMExt F E σ) (y : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (sigR (Fv F v) σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a e =>
    change a ⊗ₜ[F] σ (σ e) = _
    rw [cm_conj_conj h]

theorem finrank_loc (h : IsCMExt F E σ) : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2 := by
  rw [Module.finrank_baseChange, h.2.2.1]

theorem noeth_intLoc : IsNoetherianRing (intLoc F E v) := by
  let _ := (GlobalTheory.Orb.intLocMap E v).toAlgebra
  have : Module.Finite (v.adicCompletionIntegers F) (intLoc F E v) := GlobalTheory.Orb.finite_intLocMap v
  exact IsNoetherianRing.of_finite (v.adicCompletionIntegers F) _

theorem isUnit_intCast {m : ℤ} (hm : m ≠ 0) : IsUnit ((m : ℤ) : Fv F v ⊗[F] E) := by
  have h1 : IsUnit ((m : ℤ) : E) := isUnit_iff_ne_zero.2 (by exact_mod_cast hm)
  simpa using h1.map (inclR (F := F) (Fv F v))

theorem denom_intLoc (a : Fv F v ⊗[F] E) :
    ∃ s ∈ intLoc F E v, IsUnit s ∧ s * a ∈ intLoc F E v := by
  obtain ⟨x, hx⟩ := exists_sub_mem_intLoc v a
  obtain ⟨m, hm, he⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset E)
  have he' : IsIntegral ℤ (m • x) := he x (Finset.mem_singleton_self x)
  have hmem : ((m : ℤ) : Fv F v ⊗[F] E) ∈ intLoc F E v := intCast_mem _ m
  refine ⟨_, hmem, isUnit_intCast hm, ?_⟩
  have h2 := tmul_mem_intLoc (E := E) (one_mem (v.adicCompletionIntegers F)) ⟨m • x, he'⟩
  have e : ((m : ℤ) : Fv F v ⊗[F] E) * a =
      ((m : ℤ) : Fv F v ⊗[F] E) * (a - (1 : Fv F v) ⊗ₜ[F] x) + (1 : Fv F v) ⊗ₜ[F] (m • x) := by
    have e1 : ((m : ℤ) : Fv F v ⊗[F] E) * (1 : Fv F v) ⊗ₜ[F] x = (1 : Fv F v) ⊗ₜ[F] (m • x) := by
      rw [← zsmul_eq_mul, TensorProduct.tmul_smul]
    rw [mul_sub, e1, sub_add_cancel]
  rw [e]
  exact add_mem (mul_mem hmem hx) h2

theorem span_eq_of {R : Type} [CommRing R] {𝔬 : Subring R} {S : Set R} {u : R}
    (hu : u ∈ Submodule.span 𝔬 S) (h : ∀ s ∈ S, ∃ c ∈ 𝔬, s = c * u) :
    Submodule.span 𝔬 S = Submodule.span 𝔬 {u} := by
  refine le_antisymm (Submodule.span_le.2 fun s hs => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 hu)
  obtain ⟨c, hc, rfl⟩ := h s hs
  exact Submodule.mem_span_singleton.2 ⟨⟨c, hc⟩, rfl⟩

theorem finEmb_injective (hf : IsField (Fv F v ⊗[F] E)) (τ : E →ₐ[F] FvBar F v) :
    Function.Injective (finEmb F v τ) :=
  (injective_iff_map_eq_zero _).2 fun y hy => by
    by_contra h0
    obtain ⟨b, hb⟩ := hf.mul_inv_cancel h0
    have := congrArg (finEmb F v τ) hb
    simp [hy] at this

theorem absBar_finEmb_eq (hf : IsField (Fv F v ⊗[F] E)) (τ τ' : E →ₐ[F] FvBar F v) (y : Fv F v ⊗[F] E) :
    absBar F v (finEmb F v τ y) = absBar F v (finEmb F v τ' y) := by
  apply NNReal.eq
  change spectralNorm (Fv F v) (FvBar F v) _ = spectralNorm (Fv F v) (FvBar F v) _
  rw [spectralNorm, spectralNorm, minpoly.algHom_eq _ (finEmb_injective hf τ),
    minpoly.algHom_eq _ (finEmb_injective hf τ')]

theorem principal_field (hf : IsField (Fv F v ⊗[F] E)) (I : Submodule (intLoc F E v) (Fv F v ⊗[F] E))
    (hI : I.FG) (hu : ∃ u ∈ I, IsUnit u) : ∃ u : Fv F v ⊗[F] E, IsUnit u ∧ I = Submodule.span (intLoc F E v) {u} := by
  classical
  obtain ⟨S, rfl⟩ := hI
  obtain ⟨w, hw, hwu⟩ := hu
  have : Nontrivial (Fv F v ⊗[F] E) := ⟨hf.exists_pair_ne⟩
  let τ₀ : E →ₐ[F] FvBar F v := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let N : Fv F v ⊗[F] E → NNReal := fun y => absBar F v (finEmb F v τ₀ y)
  have hN0 : ∀ y, N y = 0 → y = 0 := fun y hy =>
    finEmb_injective hf τ₀ (by rw [map_zero]; exact (absBar_eq_zero F v).1 hy)
  have hS : S.Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    subst hc
    simp only [Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] at hw
    exact hwu.ne_zero hw
  obtain ⟨u, huS, hmax⟩ := S.exists_max_image N hS
  have hu0 : u ≠ 0 := by
    rintro rfl
    have h0 : (Submodule.span (intLoc F E v) (S : Set (Fv F v ⊗[F] E))) ≤ ⊥ :=
      Submodule.span_le.2 fun s hs => by
        refine hN0 s (le_antisymm ?_ zero_le)
        have := hmax s hs
        rwa [show N 0 = 0 from by simp [N, (absBar_eq_zero F v).2 rfl]] at this
    exact hwu.ne_zero (by simpa using h0 hw)
  obtain ⟨b, hb⟩ := hf.mul_inv_cancel hu0
  have huU : IsUnit u := IsUnit.of_mul_eq_one b hb
  refine ⟨u, huU, span_eq_of (Submodule.subset_span huS) fun s hs => ⟨b * s, ?_, ?_⟩⟩
  · refine mem_intLoc_iff_absFin_le_one.2 ((absFin_le_iff F v).2 fun τ => ?_)
    rw [absBar_finEmb_eq hf τ τ₀, map_mul, absBar_mul]
    have h1 : absBar F v (finEmb F v τ₀ u) * absBar F v (finEmb F v τ₀ b) = 1 := by
      rw [← absBar_mul, ← map_mul, hb, map_one]
      simpa using absBar_algebraMap F v 1
    calc _ ≤ absBar F v (finEmb F v τ₀ b) * absBar F v (finEmb F v τ₀ u) := mul_le_mul' le_rfl (hmax s hs)
      _ = 1 := by rw [mul_comm, h1]
  · rw [mul_right_comm, mul_comm b, hb, one_mul]

theorem exists_dom (ρ : Fv F v ⊗[F] E →ₐ[Fv F v] Fv F v) (S : Finset (Fv F v ⊗[F] E)) {w : Fv F v ⊗[F] E}
    (hw : w ∈ Submodule.span (intLoc F E v) (S : Set (Fv F v ⊗[F] E))) (hwu : IsUnit w) :
    ∃ j ∈ S, ρ j ≠ 0 ∧ ∀ s ∈ S, ‖ρ s‖₊ ≤ ‖ρ j‖₊ := by
  have hex : ∃ j ∈ S, ρ j ≠ 0 := by
    by_contra hc
    push Not at hc
    have h0 : ∀ y ∈ Submodule.span (intLoc F E v) (S : Set (Fv F v ⊗[F] E)), ρ y = 0 := fun y hy => by
      induction hy using Submodule.span_induction with
      | mem x hx => exact hc x hx
      | zero => simp
      | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
      | smul a x _ hx => rw [Subring.smul_def, smul_eq_mul, map_mul, hx, mul_zero]
    exact (hwu.map ρ).ne_zero (h0 w hw)
  obtain ⟨j0, hj0, hj0'⟩ := hex
  obtain ⟨j, hj, hmax⟩ := S.exists_max_image (fun s => ‖ρ s‖₊) ⟨j0, hj0⟩
  refine ⟨j, hj, fun e => hj0' ?_, hmax⟩
  have := hmax j0 hj0
  rw [e, nnnorm_zero] at this
  exact nnnorm_eq_zero.1 (le_antisymm this zero_le)

theorem principal_split (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (I : Submodule (intLoc F E v) (Fv F v ⊗[F] E))
    (hI : I.FG) (hu : ∃ u ∈ I, IsUnit u) : ∃ u : Fv F v ⊗[F] E, IsUnit u ∧ I = Submodule.span (intLoc F E v) {u} := by
  classical
  obtain ⟨S, rfl⟩ := hI
  obtain ⟨w, hw, hwu⟩ := hu
  obtain ⟨j1, hj1, h1, hm1⟩ := exists_dom (splitProj τ) S hw hwu
  obtain ⟨j2, hj2, h2, hm2⟩ := exists_dom (splitProj (τ.comp σ)) S hw hwu
  set e := splitIdem h τ with he
  have heI : e ∈ intLoc F E v := splitIdem_mem h τ
  set u : Fv F v ⊗[F] E := e * j1 + (1 - e) * j2 with hu
  have hup : splitProj τ u = splitProj τ j1 := by simp [hu, he]
  have huq : splitProj (τ.comp σ) u = splitProj (τ.comp σ) j2 := by simp [hu, he]
  have hmem : u ∈ Submodule.span (intLoc F E v) (S : Set (Fv F v ⊗[F] E)) :=
    add_mem (Submodule.smul_mem _ (⟨e, heI⟩ : intLoc F E v) (Submodule.subset_span hj1))
      (Submodule.smul_mem _ (⟨1 - e, sub_mem (one_mem _) heI⟩ : intLoc F E v) (Submodule.subset_span hj2))
  have hunit : IsUnit u := by
    refine IsUnit.of_mul_eq_one ((splitAlgEquiv h τ).symm ((splitProj τ j1)⁻¹, (splitProj (τ.comp σ) j2)⁻¹)) ?_
    refine split_ext h τ ?_ ?_
    · simp [hup, h1]
    · simp [huq, h2]
  refine ⟨u, hunit, span_eq_of hmem fun s hs => ?_⟩
  refine ⟨(splitAlgEquiv h τ).symm (splitProj τ s / splitProj τ j1, splitProj (τ.comp σ) s / splitProj (τ.comp σ) j2),
    (mem_intLoc_iff_split h τ).2 ⟨?_, ?_⟩, split_ext h τ ?_ ?_⟩
  · rw [splitProj_symm, ← nnnorm_le_one_iff_mem, nnnorm_div]
    exact div_le_one_of_le₀ (hm1 s hs) zero_le
  · rw [splitProj_comp_symm, ← nnnorm_le_one_iff_mem, nnnorm_div]
    exact div_le_one_of_le₀ (hm2 s hs) zero_le
  · simp [hup, h1]
  · simp [huq, h2]

theorem isHermRing_intLoc : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)),
      IsHermRing (sigR (Fv F v) σ) (intLoc F E v) := by
  intro F E _ _ _ _ _ σ h v
  have h2 : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2 := finrank_loc h
  have hfin : Module.Finite (Fv F v) (Fv F v ⊗[F] E) := Module.finite_of_finrank_pos (by omega)
  refine
    { invol := sigR_sigR h
      conj_mem := fun a ha => sigR_mem_intLoc σ ha
      nontrivial := Module.nontrivial_of_finrank_pos (R := Fv F v) (by omega)
      artinian := IsArtinianRing.of_finite (Fv F v) _
      noeth := noeth_intLoc
      two := ?_
      denom := denom_intLoc
      principal := fun I hI hu => ?_ }
  · have h1 : IsUnit (2 : E) := isUnit_iff_ne_zero.2 two_ne_zero
    have h3 := h1.map (inclR (F := F) (Fv F v))
    rwa [map_ofNat] at h3
  · by_cases hf : IsField (Fv F v ⊗[F] E)
    · exact principal_field hf I hI hu
    · obtain ⟨φ⟩ := nonempty_algHom_of_not_isField (K := Fv F v) h2 hf
      exact principal_split h ((φ.restrictScalars F).comp Algebra.TensorProduct.includeRight) I hI hu

end GlobalTheory.CompanionTheory.KFin.RingHyp

end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Matrix
open scoped Pointwise
open GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RegInt

noncomputable section
namespace GlobalTheory.CompanionTheory.RegInt

theorem mem_parRat_frameFlag_firstCols : ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hW : IsWittFrame D.sp.cm.sig V.gram X Y) (j : Fin r) (δ : GF V),
    (∀ l : Fin r, l ≤ j → ∃ b : Fin r → D.host.E, δ.1.1 *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0) →
    δ ∈ (frameFlag (isIsoFrame_firstCols hW j)).parRat D.sp.cm := by
  intro D V r X Y hW j δ h
  have hcoord : ∀ c : Fin V.rank → D.host.E, ratAct D.sp.cm V δ (GlobalTheory.AutFunCompare.vecOf V c) =
      GlobalTheory.AutFunCompare.vecOf V (δ.1.1 *ᵥ c) := by
    intro c
    refine V.frame.ext_elem fun i => ?_
    rw [GlobalTheory.AutFunCompare.repr_vecOf, ratAct, Matrix.repr_toLin]
    congr 1
    funext a
    exact GlobalTheory.AutFunCompare.repr_vecOf V c a
  have hspan : ∀ x ∈ GlobalTheory.AutFunCompare.colSpan V (firstCols X j),
      ratAct D.sp.cm V δ x ∈ GlobalTheory.AutFunCompare.colSpan V (firstCols X j) := by
    have hle : GlobalTheory.AutFunCompare.colSpan V (firstCols X j) ≤
        (GlobalTheory.AutFunCompare.colSpan V (firstCols X j)).comap (ratAct D.sp.cm V δ) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      obtain ⟨b, hb, hb0⟩ := h (Fin.castLE j.2 k) (Nat.lt_succ_iff.1 k.2)
      have hcol : (firstCols X j)ᵀ k = fun a => X a (Fin.castLE j.2 k) := rfl
      change ratAct D.sp.cm V δ (GlobalTheory.AutFunCompare.vecOf V ((firstCols X j)ᵀ k)) ∈ GlobalTheory.AutFunCompare.colSpan V (firstCols X j)
      rw [hcoord, hcol, hb]
      have hsum : X *ᵥ b = ∑ l, b l • (fun a => X a l) := by
        funext a
        simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

      rw [hsum, GlobalTheory.AutFunCompare.vecOf, map_sum]
      refine Submodule.sum_mem _ fun l _ => ?_
      rw [map_smul]
      by_cases hl : l ≤ j
      · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨l.val, Nat.lt_succ_iff.2 hl⟩, rfl⟩)
      · rw [hb0 l (not_le.1 hl), zero_smul]
        exact Submodule.zero_mem _
    exact fun x hx => hle hx
  change GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.diagH D.sp.cm.sig V.gram D.host.F δ ∈ IsoFlag.par _ D.sp.cm D.host.F
  rw [frameFlag, IsoFlag.par_single, diagH_mem_parab]
  exact hspan

end GlobalTheory.CompanionTheory.RegInt
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

theorem _root_.GlobalTheory.T.staged_disintegration_composition : ∀ (V₁ D H₁ H₃ A P Y₁ Y₃ : Type) [TopologicalSpace V₁] [T2Space V₁] [LocallyCompactSpace V₁] [SecondCountableTopology V₁] [MeasurableSpace V₁] [BorelSpace V₁] [TopologicalSpace D] [T2Space D] [LocallyCompactSpace D] [SecondCountableTopology D] [MeasurableSpace D] [BorelSpace D] [TopologicalSpace H₁] [T2Space H₁] [LocallyCompactSpace H₁] [SecondCountableTopology H₁] [MeasurableSpace H₁] [BorelSpace H₁] [TopologicalSpace H₃] [T2Space H₃] [LocallyCompactSpace H₃] [SecondCountableTopology H₃] [MeasurableSpace H₃] [BorelSpace H₃] [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A] [TopologicalSpace P] [T2Space P] [LocallyCompactSpace P] [SecondCountableTopology P] [MeasurableSpace P] [BorelSpace P] [AddCommGroup H₃] [IsTopologicalAddGroup H₃] (μ₁ : Measure V₁) (δ : Measure D) (ν₁ : Measure H₁) (ν₃ : Measure H₃) (α : Measure A) (ρ : Measure P) [IsLocallyFiniteMeasure μ₁] [IsLocallyFiniteMeasure δ] [IsLocallyFiniteMeasure ν₁] [ν₃.IsAddHaarMeasure] [IsLocallyFiniteMeasure α] [IsLocallyFiniteMeasure ρ] (f₁ : V₁ → Y₁) (ι₁ : H₁ → Y₁) (q₁ : V₁ → H₁) (U₁ : Set V₁) (m₁ : H₁ → Measure V₁) (f₃ : D → Y₃) (ι₃ : H₃ → Y₃) (q₃ : D → H₃) (U₃ : Set D) (m₃ : H₃ → Measure D) (Q : H₁ × P × A → H₃), IsOpen U₁ → IsOpen U₃ → Continuous q₁ → Continuous q₃ → Function.Injective ι₁ → Function.Injective ι₃ → (∀ v, f₁ v = ι₁ (q₁ v)) → (∀ v, f₃ v = ι₃ (q₃ v)) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ₁ f₁ ι₁ U₁ ν₁ Set.univ m₁ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily δ f₃ ι₃ U₃ ν₃ Set.univ m₃ → Continuous Q → ∀ ψ : V₁ × A × P × D → ℝ, Continuous ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, p.1 ∈ U₁ ∧ p.2.2.2 ∈ U₃) → (∀ p, 0 ≤ ψ p) → Continuous (fun z : H₁ × P × H₃ => ∫⁻ x, ∫⁻ a, ∫⁻ Y, ENNReal.ofReal (ψ (x, a, z.2.1, Y)) ∂(m₃ (z.2.2 - Q (z.1, z.2.1, a))) ∂α ∂(m₁ z.1)) ∧ ∀ f : H₁ × P × H₃ → ℝ≥0∞, Measurable f → ∫⁻ x, ∫⁻ a, ∫⁻ s, ∫⁻ Y, ENNReal.ofReal (ψ (x, a, s, Y)) * f (q₁ x, s, q₃ Y + Q (q₁ x, s, a)) ∂δ ∂ρ ∂α ∂μ₁ = ∫⁻ z, f z * (∫⁻ x, ∫⁻ a, ∫⁻ Y, ENNReal.ofReal (ψ (x, a, z.2.1, Y)) ∂(m₃ (z.2.2 - Q (z.1, z.2.1, a))) ∂α ∂(m₁ z.1)) ∂(ν₁.prod (ρ.prod ν₃)) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.StageAbs.stages_abstract | exact GlobalTheory.CompanionTheory.WeilSiegel.StageAbs.stages_abstract | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.StageAbs.stages_abstract <;> assumption)
end
