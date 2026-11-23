module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.InversionStatement
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FromBlocksMapIntCastMemSymplecticGroup
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LintegralLintegralNormSqRiemannTheta
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHostNormModCoprimeLevelHalf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

section

open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField

theorem _root_.GlobalTheory.T.lcsc_adelic_unitary_group : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), LocallyCompactSpace (HA (AF F) σ J) ∧ SecondCountableTopology (HA (AF F) σ J) ∧ T2Space (HA (AF F) σ J) := by
  first | exact @GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary | exact GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary | (intros; apply GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary <;> assumption)
end

section

open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem theta_sq_transform_level_eight :
    ∀ (g : ℕ) (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ),
      γ ∈ Matrix.symplecticGroup (Fin g) ℤ →
      (∀ i j, (8 : ℤ) ∣ γ (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ γ (Sum.inr i) (Sum.inl j)) →
      (∀ τ ∈ SiegelH (Fin g), ∀ z : Fin g → ℂ,
        theta (halfVec 0) (halfVec 0) (zAct γ τ z) (spAct γ τ) ^ 2 =
          ((ZMod.χ₄ ((γ.toBlocks₂₂.det : ℤ) : ZMod 4) : ℤ) : ℂ) * (jAut γ τ).det *
            eC (expArg γ τ z) * theta (halfVec 0) (halfVec 0) z τ ^ 2) := by
  intro g γ hγ h τ hτ z
  have h48 : (4 : ℤ) ∣ 8 := by norm_num
  exact theta_halfVec_sq_transform hγ (fun i j => h48.trans (h i j).1)
    (fun i j => h48.trans (h i j).2) (k := 0) (k' := 0) (m := 0) (m' := 0)
    (fun i => by rw [mulVec_zero]) (fun i => by rw [mulVec_zero]) hτ z

end GlobalTheory
end

section

open MeasureTheory Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.ThetaMean

theorem mean_image {ι κ : Type} [Fintype ι] [Fintype κ] (L : (ι → ℝ) ≃L[ℝ] (κ → ℂ))
    {s : Set (ι → ℝ)} (hs : volume s = 1) (f : (κ → ℂ) → ℝ) :
    (∫ z in L '' s, f z) / (volume (L '' s)).toReal = ∫ p in s, f (L p) := by
  have hL : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
  have : (Measure.map L (volume : Measure (ι → ℝ))).IsAddHaarMeasure := L.isAddHaarMeasure_map _
  set c := Measure.addHaarScalarFactor (volume : Measure (κ → ℂ)) (Measure.map L volume) with hc_def
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hvol : (volume : Measure (κ → ℂ)) = c • Measure.map L volume :=
    Measure.isAddLeftInvariant_eq_smul _ _
  have hpre : L ⁻¹' (L '' s) = s := Set.preimage_image_eq s L.injective
  have h1 : (volume (L '' s)).toReal = c := by
    rw [hvol, Measure.smul_apply, hL.map_apply, hpre, hs]
    simp
  have h2 : ∫ z in L '' s, f z = c * ∫ p in s, f (L p) := by
    rw [hvol, Measure.restrict_smul, integral_smul_nnreal_measure, hL.restrict_map, hpre,
      hL.integral_map, NNReal.smul_def, smul_eq_mul]
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [h2, h1, mul_div_cancel_left₀ _ hc']

def periodMap {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) : (Fin g ⊕ Fin g → ℝ) →ₗ[ℝ] (Fin g → ℂ) where
  toFun p := (fun i => (p (.inl i) : ℂ)) + τ *ᵥ (fun i => (p (.inr i) : ℂ))
  map_add' p q := by
    funext i
    simp [mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' r p := by
    funext i
    simp [mulVec, dotProduct, mul_add, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

theorem periodMap_apply {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (p : Fin g ⊕ Fin g → ℝ) :
    periodMap τ p = (fun i => (p (.inl i) : ℂ)) + τ *ᵥ (fun i => (p (.inr i) : ℂ)) := rfl

theorem im_periodMap {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (p : Fin g ⊕ Fin g → ℝ) :
    (fun i => (periodMap τ p i).im) = τ.map Complex.im *ᵥ fun i => p (.inr i) := by
  funext i
  simp [periodMap_apply, mulVec, dotProduct, Complex.im_sum]

theorem periodMap_bijective {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}
    (hp : (τ.map Complex.im).PosDef) : Function.Bijective (periodMap τ) := by
  have hinj : Function.Injective (periodMap τ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp0
    have him := im_periodMap τ p
    rw [hp0] at him
    have h2 : (fun i => p (.inr i)) = 0 := by
      refine Matrix.eq_zero_of_mulVec_eq_zero hp.det_pos.ne' ?_
      rw [← him]
      rfl
    have h1 : (fun i => (p (.inl i) : ℂ)) = 0 := by
      have := hp0
      rw [periodMap_apply] at this
      have h2' : (fun i => (p (.inr i) : ℂ)) = 0 := by
        funext i
        simp [show p (.inr i) = 0 from congrFun h2 i]
      rw [h2', mulVec_zero, add_zero] at this
      exact this
    funext x
    rcases x with i | i
    · simpa using congrFun h1 i
    · exact congrFun h2 i
  have hrank : Module.finrank ℝ (Fin g ⊕ Fin g → ℝ) = Module.finrank ℝ (Fin g → ℂ) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
    ring
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj⟩

theorem exists_fundamentalDomain_mean_norm_sq_thetaChar :
    ∀ (g : ℕ) (τ h : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ)
      (Λ : AddSubgroup (Fin g → ℂ)), τ.IsSymm → (τ.map Complex.im).PosDef → IsUnit h.det →
      (∀ i, c₁ i = 0 ∨ c₁ i = 1 / 2) → (∀ i, c₂ i = 0 ∨ c₂ i = 1 / 2) →
      (∀ lam, lam ∈ Λ ↔ ∃ m n : Fin g → ℤ,
        h *ᵥ lam = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ))) →
      ∃ Fd : Set (Fin g → ℂ), MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume ∧
        (∫ z in Fd, ‖thetaChar τ c₁ c₂ (h *ᵥ z)‖ ^ 2 * Real.exp (-2 * Real.pi *
          ((fun i => ((h *ᵥ z) i).im) ⬝ᵥ (((τ.map Complex.im)⁻¹) *ᵥ fun i => ((h *ᵥ z) i).im)))) /
          (MeasureTheory.volume Fd).toReal =
          (Real.sqrt (2 ^ g * (τ.map Complex.im).det))⁻¹ := by
  intro g τ h c₁ c₂ Λ hsym hY hh hc₁ hc₂ hΛ
  obtain ⟨a, rfl⟩ : ∃ a : Fin g → ℝ, (fun i => (a i : ℂ)) = c₁ := by
    refine ⟨fun i => (c₁ i).re, funext fun i => ?_⟩
    show ((c₁ i).re : ℂ) = c₁ i
    rcases hc₁ i with e | e <;> rw [e] <;> norm_num
  obtain ⟨b, rfl⟩ : ∃ b : Fin g → ℝ, (fun i => (b i : ℂ)) = c₂ := by
    refine ⟨fun i => (c₂ i).re, funext fun i => ?_⟩
    show ((c₂ i).re : ℂ) = c₂ i
    rcases hc₂ i with e | e <;> rw [e] <;> norm_num
  have hcancel : ∀ x : Fin g → ℂ, h⁻¹ *ᵥ (h *ᵥ x) = x := by
    intro x
    rw [mulVec_mulVec, nonsing_inv_mul _ hh, one_mulVec]
  let Pe : (Fin g ⊕ Fin g → ℝ) ≃ₗ[ℝ] (Fin g → ℂ) :=
    LinearEquiv.ofBijective (periodMap τ) (periodMap_bijective hY)
  let Hinv : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) :=
    LinearEquiv.ofLinearMap (Matrix.toLin' h⁻¹) (Matrix.toLin' h)
      (by rw [← Matrix.toLin'_mul, nonsing_inv_mul _ hh, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, mul_nonsing_inv _ hh, Matrix.toLin'_one])
  let Φ : (Fin g ⊕ Fin g → ℝ) ≃L[ℝ] (Fin g → ℂ) :=
    (Pe.trans (Hinv.restrictScalars ℝ)).toContinuousLinearEquiv
  have F1 : ∀ p, h *ᵥ Φ p = periodMap τ p := by
    intro p
    show h *ᵥ (h⁻¹ *ᵥ periodMap τ p) = _
    rw [mulVec_mulVec, mul_nonsing_inv _ hh, one_mulVec]
  let B : Module.Basis (Fin g ⊕ Fin g) ℝ (Fin g → ℂ) :=
    (Pi.basisFun ℝ (Fin g ⊕ Fin g)).map Φ.toLinearEquiv
  have hrepr : ∀ z i, B.repr z i = Φ.symm z i := by
    intro z i
    simp [B]
  have hΛeq : Λ = (Submodule.span ℤ (Set.range B)).toAddSubgroup := by
    ext lam
    rw [hΛ lam, Submodule.mem_toAddSubgroup, Module.Basis.mem_span_iff_repr_mem]
    simp only [hrepr, Set.mem_range, algebraMap_int_eq, eq_intCast]
    constructor
    · rintro ⟨m, n, hmn⟩ i
      have hPq : periodMap τ (Sum.elim (fun i => (m i : ℝ)) (fun i => (n i : ℝ))) =
          (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)) := by
        rw [periodMap_apply]
        simp
      have hΦq : Φ (Sum.elim (fun i => (m i : ℝ)) (fun i => (n i : ℝ))) = lam := by
        have e : h *ᵥ Φ (Sum.elim (fun i => (m i : ℝ)) (fun i => (n i : ℝ))) = h *ᵥ lam := by
          rw [F1, hPq, hmn]
        rw [← hcancel (Φ _), e, hcancel]
      rw [← hΦq, Φ.symm_apply_apply]
      rcases i with i | i
      · exact ⟨m i, by simp⟩
      · exact ⟨n i, by simp⟩
    · intro hk
      choose k hk using hk
      refine ⟨fun i => k (.inl i), fun i => k (.inr i), ?_⟩
      rw [← Φ.apply_symm_apply lam, F1, periodMap_apply]
      simp_rw [← hk, Complex.ofReal_intCast]
  have hFd : ZSpan.fundamentalDomain B = Φ '' Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1) := by
    rw [ContinuousLinearEquiv.image_eq_preimage_symm]
    ext z
    simp [ZSpan.mem_fundamentalDomain, hrepr]
  have hcube : volume (Set.univ.pi fun _ : Fin g ⊕ Fin g => Set.Ico (0 : ℝ) 1) = 1 := by
    simpa using Real.volume_pi_Ico (a := fun _ : Fin g ⊕ Fin g => (0 : ℝ)) (b := fun _ => 1)
  have hYu : IsUnit (τ.map Complex.im).det := hY.det_pos.ne'.isUnit
  refine ⟨ZSpan.fundamentalDomain B, by rw [hΛeq]; exact ZSpan.isAddFundamentalDomain' B _, ?_⟩
  rw [hFd, mean_image Φ hcube, ← GlobalTheory.ThetaNorm.integral_norm_sq_thetaChar g τ a b hsym hY]
  congr 1
  funext p
  rw [F1, im_periodMap, mulVec_mulVec, nonsing_inv_mul _ hYu, one_mulVec, dotProduct_comm,
    periodMap_apply]

end GlobalTheory.ThetaMean
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LevelAllPrimes

open GlobalTheory.HostModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.LevelAllPrimes.add_rt_mul_sub_rt (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (c : ℕ) :
    ((c : 𝓞 E) + H.rt) * (c - H.rt) = ((c ^ 2 + H.d : ℕ) : 𝓞 E) := by
  push_cast
  linear_combination (-1 : 𝓞 E) * H.rt_sq


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.LevelAllPrimes.isCoprime_add_rt_sub_rt (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {c : ℕ} (hc : Nat.Coprime c H.d)
    (ho : Odd (c ^ 2 + H.d)) :
    IsCoprime ((c : 𝓞 E) + H.rt) (c - H.rt) := by
  have h2 : Nat.Coprime 2 (c ^ 2 + H.d) := (Nat.coprime_two_left).2 ho
  have hc' : Nat.Coprime c (c ^ 2 + H.d) := by
    rw [sq, add_comm]
    exact (Nat.coprime_add_mul_right_right c H.d c).2 hc
  have hcop : IsCoprime ((2 * c : ℕ) : ℤ) ((c ^ 2 + H.d : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.mul_left h2 hc')
  obtain ⟨u, v, huv⟩ := hcop
  have key := congrArg (Int.cast : ℤ → 𝓞 E) huv
  push_cast at key
  refine ⟨(u : 𝓞 E) + v * (c - H.rt), u, ?_⟩
  linear_combination key - (v : 𝓞 E) * H.rt_sq

end GlobalTheory.LevelAllPrimes

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem host_bar_rt' (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : H.bar H.rt = -H.rt := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hconj : starRingEnd ℂ (φ (H.rt : E)) = -φ (H.rt : E) := by
    set z := φ (H.rt : E)
    have hz : z ^ 2 = -(H.d : ℂ) := by
      have := congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
      simpa [z] using this
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have hre := congrArg Complex.re hz
    have him := congrArg Complex.im hz
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him
    have hx : z.re = 0 := by
      rcases mul_eq_zero.1 (by linarith : z.re * z.im = 0) with h | h
      · exact h
      · rw [h] at hre; nlinarith
    apply Complex.ext <;> simp [hx]
  have key : ((H.bar H.rt : 𝓞 E) : E) = ((-H.rt : 𝓞 E) : E) := by
    rw [H.bar_eq]
    apply φ.injective
    simpa [IsCMField.complexEmbedding_complexConj] using hconj
  exact RingOfIntegers.coe_injective key

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem natCast_add_rt_mem_adjoin_w0 (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (c : ℕ) :
    (c : 𝓞 E) + H.rt ∈ Algebra.adjoin ℤ {H.w0} := by
  rw [show (c : 𝓞 E) + H.rt = ((c : 𝓞 E) - 1) + 2 * H.w0 by linear_combination -H.two_weight_eq_one_add_root]
  have hw : H.w0 ∈ Algebra.adjoin ℤ {H.w0} := Algebra.self_mem_adjoin_singleton ℤ H.w0
  have h2 : (2 : 𝓞 E) ∈ Algebra.adjoin ℤ {H.w0} := by
    simpa using natCast_mem (Algebra.adjoin ℤ {H.w0}) 2
  exact add_mem (sub_mem (natCast_mem _ c) (one_mem _)) (mul_mem h2 hw)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private theorem three_le_mul_div_prime_pow_factorization {a b : ℕ} (p : ℕ) (hab : Nat.Coprime a b)
    (ha : 3 ≤ a) (hb : 3 ≤ b) : 3 ≤ a * b / p ^ (a * b).factorization p := by
  have key : ∀ {x y : ℕ}, 3 ≤ x → 0 < y → x.factorization p = 0 →
      3 ≤ x * y / p ^ (x * y).factorization p := by
    intro x y hx hy hxp
    rw [Nat.factorization_mul (by omega) hy.ne', Finsupp.add_apply, hxp, zero_add,
      Nat.mul_div_assoc x (Nat.ordProj_dvd y p)]
    have : 1 ≤ y / p ^ y.factorization p :=
      Nat.div_pos (Nat.le_of_dvd hy (Nat.ordProj_dvd y p)) (Nat.ordProj_pos y p)
    nlinarith
  by_cases hap : a.factorization p = 0
  · exact key ha (by omega) hap
  · have hbp : b.factorization p = 0 := by
      by_contra hbp
      have hp : p.Prime := Nat.prime_of_mem_primeFactors (Finsupp.mem_support_iff.2 hap)
      have hpa : p ∣ a := Nat.dvd_of_factorization_pos hap
      have hpb : p ∣ b := Nat.dvd_of_factorization_pos hbp
      have hg := Nat.dvd_gcd hpa hpb
      rw [hab.gcd_eq_one] at hg
      exact hp.one_lt.ne' (Nat.dvd_one.1 hg)
    rw [mul_comm]
    exact key hb (by omega) hbp


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
theorem _root_.GlobalTheory.exists_level_goodAt_all_primes_and_idx :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (A : ℕ), 0 < A →
      ∃ l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, l.A = A ∧ (∀ p : ℕ, p.Prime → l.GoodAt p) ∧
        ∀ p : ℕ, p.Prime → ∃ i : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Idx H p, i.l = l := by
  intro E _ _ _ H A hA
  obtain ⟨k, hk⟩ : Odd H.d := Nat.odd_iff.2 (by have := H.d_mod; omega)
  have h2d : Nat.Coprime 2 H.d := (Nat.coprime_two_left).2 ⟨k, hk⟩
  have h4d : Nat.Coprime (2 ^ 2 + H.d) H.d := by
    rw [Nat.coprime_add_self_left]
    exact Nat.Coprime.pow_left 2 h2d
  have hc1 : Nat.Coprime 2 H.d := h2d
  have hc2 : Nat.Coprime (2 * (2 ^ 2 + H.d)) H.d := Nat.Coprime.mul_left h2d h4d
  have ho1 : Odd (2 ^ 2 + H.d) := ⟨2 + k, by rw [hk]; ring⟩
  have ho2 : Odd ((2 * (2 ^ 2 + H.d)) ^ 2 + H.d) := by
    refine Even.add_odd ?_ ⟨k, hk⟩
    rw [sq]
    exact (even_two_mul _).mul_right _
  have hM : Nat.Coprime (2 ^ 2 + H.d) ((2 * (2 ^ 2 + H.d)) ^ 2 + H.d) := by
    rw [show (2 * (2 ^ 2 + H.d)) ^ 2 + H.d = H.d + (4 * (2 ^ 2 + H.d)) * (2 ^ 2 + H.d) by ring,
      Nat.coprime_add_mul_right_right]
    exact h4d
  have e1 := _root_.GlobalTheory.LevelAllPrimes.add_rt_mul_sub_rt H 2
  have e2 := _root_.GlobalTheory.LevelAllPrimes.add_rt_mul_sub_rt H (2 * (2 ^ 2 + H.d))
  set M₁ := 2 ^ 2 + H.d with hM₁
  set c := 2 * M₁ with hc
  set M₂ := c ^ 2 + H.d with hM₂
  have hMcop : IsCoprime (M₁ : 𝓞 E) (M₂ : 𝓞 E) := by
    have := (Nat.isCoprime_iff_coprime.2 hM).map (Int.castRingHom (𝓞 E))
    simpa using this
  set al := ((2 : ℕ) + H.rt) * ((c : 𝓞 E) + H.rt) with hal
  have hbar : H.bar al = ((2 : ℕ) - H.rt) * ((c : 𝓞 E) - H.rt) := by
    simp only [hal, map_mul, map_add (f := _), map_natCast, host_bar_rt', sub_eq_add_neg]
  have hmem : al ∈ Algebra.adjoin ℤ {H.w0} :=
    mul_mem (natCast_add_rt_mem_adjoin_w0 H 2) (natCast_add_rt_mem_adjoin_w0 H c)
  have hprod : al * H.bar al = ((M₁ * M₂ : ℕ) : 𝓞 E) := by
    rw [hbar, hal, show ((2 : ℕ) + H.rt) * ((c : 𝓞 E) + H.rt) * (((2 : ℕ) - H.rt) * ((c : 𝓞 E) - H.rt))
      = (((2 : ℕ) + H.rt) * ((2 : ℕ) - H.rt)) * (((c : 𝓞 E) + H.rt) * ((c : 𝓞 E) - H.rt)) by ring,
      e1, e2]
    exact (Nat.cast_mul _ _).symm
  have hcop : IsCoprime al (H.bar al) := by
    rw [hbar, hal]
    refine IsCoprime.mul_left (IsCoprime.mul_right ?_ ?_) (IsCoprime.mul_right ?_ ?_)
    · exact _root_.GlobalTheory.LevelAllPrimes.isCoprime_add_rt_sub_rt H hc1 ho1
    · exact (hMcop.of_isCoprime_of_dvd_left (Dvd.intro _ e1)).of_isCoprime_of_dvd_right
        (Dvd.intro_left _ e2)
    · exact (hMcop.symm.of_isCoprime_of_dvd_left (Dvd.intro _ e2)).of_isCoprime_of_dvd_right
        (Dvd.intro_left _ e1)
    · exact _root_.GlobalTheory.LevelAllPrimes.isCoprime_add_rt_sub_rt H hc2 ho2
  have h3₁ : 3 ≤ M₁ := by omega
  have h3₂ : 3 ≤ M₂ := by have := Nat.zero_le (c ^ 2); have := H.d_prime.two_le; omega
  obtain ⟨l, hlM, hlA, -⟩ := (_root_.GlobalTheory.level_of_split_and_level_coeff_exist).1 E H al (M₁ * M₂) A
    hmem hprod hcop (le_trans h3₁ (Nat.le_mul_of_pos_right _ (by omega)))
    (Nat.odd_mul.2 ⟨ho1, ho2⟩) hA
  have hgood : ∀ p : ℕ, p.Prime → l.GoodAt p := by
    intro p _
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.GoodAt
    rw [hlM]
    exact three_le_mul_div_prime_pow_factorization p hM h3₁ h3₂
  refine ⟨l, hlA, hgood, fun p hp => ?_⟩
  obtain ⟨cf⟩ := (_root_.GlobalTheory.level_of_split_and_level_coeff_exist).2.2 E H l
  exact ⟨{ l := l, c := cf, good := hgood p hp }, rfl⟩

end GlobalTheory
end

section

open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.exists_hostNorm_mod_coprime_level_half : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (n : ℕ) (ν : ℤ), 0 < n → IsCoprime ν (n : ℤ) → ∃ t : 𝓞 E, (n : 𝓞 E) ∣ t * H.bar t - (ν : 𝓞 E) ∧ (l.M ∣ n → t - 1 ∈ l.Mb) := by
  first | exact @GlobalTheory.NormMod.exists_norm_mod | exact GlobalTheory.NormMod.exists_norm_mod | (intros; apply GlobalTheory.NormMod.exists_norm_mod <;> assumption)
end
