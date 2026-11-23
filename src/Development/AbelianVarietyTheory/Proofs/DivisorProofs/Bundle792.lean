module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle038
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle020
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle035
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle039
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle041
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle753
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle757
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle717
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle787
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle629
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle758
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
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.FieldTheory.Finite.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle004
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle005
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.ContDiffAtSectionFrameQuotient
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem pow_card_pow_sub_one_of_root (F : Type) [Field F] [Finite F] (f : F[X]) (hf : f.Monic)
    (hi : Irreducible f) (m : ℕ) (hd : f.natDegree ∣ m) (α : AlgebraicClosure F)
    (hα : α ∈ (f.map (algebraMap F (AlgebraicClosure F))).roots) (h0 : α ≠ 0) :
    α ^ (Nat.card F ^ m - 1) = 1 := by
  have hf0 : f.map (algebraMap F (AlgebraicClosure F)) ≠ 0 := Polynomial.map_ne_zero hi.ne_zero
  have hr : aeval α f = 0 := by
    have := (mem_roots hf0).1 hα
    rwa [IsRoot, eval_map_algebraMap] at this
  have hmin : f = minpoly F α := minpoly.eq_of_irreducible_of_monic hi hr hf
  have hx : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have hfix : α ^ Nat.card F ^ m = α := by
    have h1 := ((minpoly.irreducible hx).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X (n := m)).1
      (by rw [← hmin]; exact hd)
    rw [minpoly.dvd_iff] at h1
    simpa [sub_eq_zero] using h1
  have hpos : 1 ≤ Nat.card F ^ m := Nat.one_le_pow _ _ Nat.card_pos
  have : α ^ (Nat.card F ^ m - 1) * α = 1 * α := by
    rw [← pow_succ, Nat.sub_add_cancel hpos, hfix, one_mul]
  exact mul_right_cancel₀ h0 this

theorem pow_eq_pow_of_modEq' {M : Type} [Monoid M] (α : M) (N a b : ℕ) (h : α ^ N = 1)
    (hab : a ≡ b [MOD N]) : α ^ a = α ^ b := by
  rw [← Nat.div_add_mod a N, ← Nat.div_add_mod b N, pow_add, pow_add, pow_mul, pow_mul, h, one_pow,
    one_pow, hab]

end GlobalTheory.Shin

namespace GlobalTheory.Shin

theorem rootSum_eq_of_modEq (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (f : F[X])
    (hf : f.Monic) (hi : Irreducible f) (hc : f.coeff 0 ≠ 0) (m k k' a : ℕ) (hd : f.natDegree ∣ m)
    (hk : k' ≡ k * Nat.card F ^ a [MOD Nat.card F ^ m - 1]) :
    rootSum θ k' f = rootSum θ k f := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F (ringChar F)
  have hq : ringChar F ^ ((n : ℕ) * a) = Nat.card F ^ a := by
    rw [Nat.card_eq_fintype_card, hn, pow_mul]
  have hgal := GlobalTheory.T.rootSum_map_frobenius_pow_eq_rootSum_mul F θ (RingHom.id F) ((n : ℕ) * a) (fun x => by
    rw [hq, Nat.card_eq_fintype_card, FiniteField.pow_card_pow]; rfl) k f
  rw [Polynomial.map_id, hq] at hgal
  rw [hgal]
  unfold rootSum
  congr 1
  refine Multiset.map_congr rfl fun α hα => ?_
  have hf0 : f.map (algebraMap F (AlgebraicClosure F)) ≠ 0 := Polynomial.map_ne_zero hi.ne_zero
  have h0 : α ≠ 0 := by
    rintro rfl
    have h := (mem_roots hf0).1 hα
    rw [IsRoot, ← coeff_zero_eq_eval_zero, coeff_map] at h
    exact hc ((algebraMap F (AlgebraicClosure F)).injective (by rw [h, map_zero]))
  rw [← map_pow, ← map_pow,
    pow_eq_pow_of_modEq' α _ _ _ (pow_card_pow_sub_one_of_root F f hf hi m hd α hα h0) hk]

end GlobalTheory.Shin

namespace GlobalTheory.Shin

theorem cusp_eq_of_modEq : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ),
    (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) →
    ∀ m k k' a : ℕ, 0 < m → k' ≡ k * Nat.card F ^ a [MOD Nat.card F ^ m - 1] →
      cusp θ m k' = cusp θ m k := by
  intro F _ _ θ _ m k k' a _ hk
  funext x
  unfold cusp psiG
  congr 1
  set V := Fin m → F
  set g : Module.End F V := Matrix.toLin' (x : Matrix (Fin m) (Fin m) F)
  have hV : Finite V := Module.finite_of_finite F
  have hE : Finite (Module.End F V) := Finite.of_injective _ DFunLike.coe_injective
  have hs := (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ k).1
  have hs' := (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ k').1
  let φ : Module.End F V → ℂ := fun h => psi (rootSum θ k') V h - psi (rootSum θ k) V h
  have hc : IsClassFn φ := by
    intro e h
    simp only [φ, GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj]
  have hp : GlobalTheory.CuspGL.IsPrimitive φ := by
    intro A hA hA' g' hg'
    have e1 := GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse F V _ hs' A hA hA' g' hg'
    have e2 := GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse F V _ hs A hA hA' g' hg'
    have := finsum_mem_lin_comb_of_finite (nilRad A) 1 1 (fun h => psi (rootSum θ k') V (g' + h))
      (fun h => psi (rootSum θ k) V (g' + h))
    simp only [one_mul] at this
    simp only [φ]
    rw [this, e1, e2, sub_zero]
  have hP : (LinearMap.charpoly g).Monic := LinearMap.charpoly_monic g
  have hdeg : (LinearMap.charpoly g).natDegree = Module.finrank F V := LinearMap.charpoly_natDegree g
  have hdegm : (LinearMap.charpoly g).natDegree = m := by rw [hdeg, Module.finrank_fin_fun]
  have hc0 : (LinearMap.charpoly g).coeff 0 ≠ 0 := by
    intro h0
    have hdet := LinearMap.det_eq_sign_charpoly_coeff g
    rw [h0, mul_zero, LinearMap.det_toLin'] at hdet
    exact ((Matrix.isUnit_iff_isUnit_det _).1 x.isUnit).ne_zero hdet
  have hmang : mangoldt (rootSum θ k') (LinearMap.charpoly g) =
      mangoldt (rootSum θ k) (LinearMap.charpoly g) := by
    unfold mangoldt
    refine finsum_mem_congr rfl fun f hf => ?_
    obtain ⟨hfm, hfi, r, hr, hfr⟩ := hf
    refine rootSum_eq_of_modEq F θ f hfm hfi ?_ m k k' a ?_ hk
    · intro h
      apply hc0
      rw [hfr, coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero, h, zero_pow hr.ne']
    · refine ⟨r, ?_⟩
      rw [← hdegm, hfr, natDegree_pow, mul_comm]
  have hmass : mass φ (LinearMap.charpoly g) = 0 := by
    have := finsum_mem_lin_comb_of_finite {h : Module.End F V | LinearMap.charpoly h = LinearMap.charpoly g}
      1 1 (psi (rootSum θ k') V) (psi (rootSum θ k) V)
    simp only [one_mul] at this
    unfold mass
    simp only [φ]
    rw [this]
    have m1 := GlobalTheory.T.endomorphismMass_mobiusInverse_monic_eq F V _ hs' _ hP hdeg
    have m2 := GlobalTheory.T.endomorphismMass_mobiusInverse_monic_eq F V _ hs _ hP hdeg
    unfold mass at m1 m2
    rw [m1, m2, hmang, sub_self]
  exact sub_eq_zero.1 (GlobalTheory.T.primitiveEndClassFunction_zero_of_charpoly_mass_zero F V φ hc hp g hmass)

end GlobalTheory.Shin
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.conjugate_into_adjoined_algebra : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (δ : GL (Fin n) F') (γ : GL (Fin n) F), IsNorm s δ γ → ∃ y : GL (Fin n) F', ((y⁻¹ * δ * galAct F F' n s y : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} ∧ nrm s (y⁻¹ * δ * galAct F F' n s y) = incl F F' n γ := by
  first | (exact @GlobalTheory.Shin.isNorm_exists_twistedConj_adjoin) | (exact GlobalTheory.Shin.isNorm_exists_twistedConj_adjoin) | (intros; apply GlobalTheory.Shin.isNorm_exists_twistedConj_adjoin  <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.card_isGaloisTwistedNormGL_mul_card_GL : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (γ : GL (Fin n) F), Nat.card {δ : GL (Fin n) F' // IsNorm s δ γ} * Nat.card (GL (Fin n) F) = Nat.card {γ' : GL (Fin n) F // IsConj γ γ'} * Nat.card (GL (Fin n) F') := by
  first | (exact @GlobalTheory.Shin.NormFibre.card_isNorm_mul_card) | (exact GlobalTheory.Shin.NormFibre.card_isNorm_mul_card) | (intros; apply GlobalTheory.Shin.NormFibre.card_isNorm_mul_card  <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.primitiveFunctionCharpoly_pair_prod_rootSum : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ (m k l : ℕ) (e : Fin l → ℕ), 0 < m → ∑ᶠ x, psiG (rootSum θ k) m x * star (chG (fun P => ∏ j, rootSum θ (e j) P) m x) = (Nat.card (GL (Fin m) F) : ℂ) * ((Finset.univ.filter fun a : Fin l → Fin m => k ≡ ∑ j, e j * Nat.card F ^ (a j : ℕ) [MOD Nat.card F ^ m - 1]).card : ℂ) := by
  first | (exact @GlobalTheory.Shin.psiG_rootSum_pair_prod_rootSum) | (exact GlobalTheory.Shin.psiG_rootSum_pair_prod_rootSum) | (intros; apply GlobalTheory.Shin.psiG_rootSum_pair_prod_rootSum <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.WpFam.TauVal

theorem complex_div_pow_div_div_pow (a x k : ℂ) (n : ℕ) (hk : k ≠ 0) :
    a / k ^ n / (x / k) ^ n = a / x ^ n := by
  by_cases hx : x = 0
  · subst hx
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · simp [zero_pow h.ne']
  · rw [div_pow]; field_simp

theorem two_pi_I_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp [this, Complex.I_ne_zero]

theorem main : ∀ (Λ : PeriodPair) (c Ω : ℂ) (τ : ℍ), IsTauOf Λ c τ → (G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2 = s2 Λ / Ω ^ 2) ∧ ∀ (N : ℕ) (x : Fin 2 → ZMod N), wp N x τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2 = Λ.weierstrassP (c * tors N τ x) / Ω ^ 2 ∧ wpd N x τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 3 = Λ.derivWeierstrassP (c * tors N τ x) / Ω ^ 3 := by
  intro Λ c Ω τ h
  obtain ⟨_, hP, hD, hs, _⟩ := GlobalTheory.T.weierstrassP_homogeneity_of_isTauOf Λ c τ h
  have hG := (GlobalTheory.WpFam.LatConst.main τ).1
  have hk := two_pi_I_ne_zero
  refine ⟨?_, fun N x => ⟨?_, ?_⟩⟩
  · rw [complex_div_pow_div_div_pow _ _ _ _ hk, hs, hG, mul_pow, inv_mul_eq_div, div_div, mul_comm]
  · rw [wp, complex_div_pow_div_div_pow _ _ _ _ hk, hP, mul_pow, inv_mul_eq_div, div_div, mul_comm]
  · rw [wpd, complex_div_pow_div_div_pow _ _ _ _ hk, hD, mul_pow, inv_mul_eq_div, div_div, mul_comm]

end GlobalTheory.WpFam.TauVal
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem glue_isSSec_of_holo : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type)
    [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La)
    (u : Fin C.m → V n → ℂ), (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) →
    A.IsSSec (A.kap + la) (glue C la u) := by
  intro n Y _ _ _ _ _ ι La _ A C la u hu
  refine ⟨fun i => ?_, fun i j y hi hj => ?_⟩
  · have key : ∀ a, ContDiffOn ℝ ∞ (fun v => (C.chi a ((A.chart i).symm v) : ℂ) *
        A.g (A.kap + la) i (C.idx a) ((A.chart i).symm v) *
        u a (A.chart (C.idx a) ((A.chart i).symm v))) (A.chart i).target := by
      intro a v hv
      apply ContDiffAt.contDiffWithinAt
      by_cases hy : (A.chart i).symm v ∈ tsupport (C.chi a)
      · have hs := C.supp a hy
        have hovo : IsOpen (ovl A.chart i (C.idx a)) :=
          (A.chart i).isOpen_inter_preimage_symm (A.chart (C.idx a)).open_source
        have hvov : v ∈ ovl A.chart i (C.idx a) := ⟨hv, hs.1⟩
        have hUo : IsOpen (ovl A.chart i (C.idx a) ∩
            (A.chart (C.idx a) ∘ (A.chart i).symm) ⁻¹' ball (C.c a) (C.r a)) :=
          (A.holo_trans i (C.idx a)).continuousOn.isOpen_inter_preimage hovo isOpen_ball
        have hvU : v ∈ ovl A.chart i (C.idx a) ∩
            (A.chart (C.idx a) ∘ (A.chart i).symm) ⁻¹' ball (C.c a) (C.r a) := ⟨hvov, hs.2⟩
        have h1 : ContDiffAt ℝ ∞ (C.chi a ∘ (A.chart i).symm) v :=
          (C.smooth a i).contDiffAt ((A.chart i).open_target.mem_nhds hv)
        have h1' : ContDiffAt ℝ ∞ (fun v => (C.chi a ((A.chart i).symm v) : ℂ)) v :=
          Complex.ofRealCLM.contDiff.contDiffAt.comp v h1
        have h2 : ContDiffAt ℝ ∞ (A.g (A.kap + la) i (C.idx a) ∘ (A.chart i).symm) v :=
          hyq_contDiffAt_of_holo hovo (A.holo_g _ _ _) hvov
        have h3 : ContDiffAt ℝ ∞ (u a ∘ (A.chart (C.idx a) ∘ (A.chart i).symm)) v :=
          hyq_contDiffAt_of_holo hUo ((hu a).comp
            ((A.holo_trans i (C.idx a)).mono Set.inter_subset_left) (fun w hw => hw.2)) hvU
        exact (h1'.mul h2).mul h3
      · have hn : (tsupport (C.chi a))ᶜ ∈ 𝓝 ((A.chart i).symm v) :=
          (isClosed_tsupport _).isOpen_compl.mem_nhds hy
        have h2 : ∀ᶠ w in 𝓝 v, (A.chart i).symm w ∉ tsupport (C.chi a) :=
          ((A.chart i).continuousAt_symm hv).preimage_mem_nhds hn
        refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
        filter_upwards [h2] with w hw
        simp [image_eq_zero_of_notMem_tsupport hw]
    have he : (glue C la u i ∘ (A.chart i).symm) = fun v => ∑ a, (C.chi a ((A.chart i).symm v) : ℂ) *
        A.g (A.kap + la) i (C.idx a) ((A.chart i).symm v) *
        u a (A.chart (C.idx a) ((A.chart i).symm v)) := by
      funext v; simp [glue]
    rw [he]
    exact ContDiffOn.sum fun a _ => key a
  · simp only [glue]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : C.chi a y = 0
    · simp [h]
    · have hk := (C.supp a (subset_tsupport _ h)).1
      rw [A.g_cocycle (A.kap + la) i j (C.idx a) y hi hj hk]
      ring

end GlobalTheory.OTY
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.JetSmall

theorem ph_nsmul {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
    (A : WeightedAtlas n Y ι La) (H : La) (i : ι) (y : Y) (hy : y ∈ (A.chart i).source) (k : ℕ) :
    A.ph (k • H) i y = k * A.ph H i y := by
  induction k with
  | zero =>
    rw [zero_nsmul, Nat.cast_zero, zero_mul]
    have := A.ph_add 0 0 i y hy
    rw [add_zero] at this
    linarith
  | succ k ih =>
    rw [succ_nsmul, A.ph_add _ _ i y hy, ih]
    push_cast; ring

theorem main : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (H G : La) (i : ι) (p : V n) (r0 c Cq K : ℝ) (q : V n → ℂ), 0 < r0 → 0 < c → closedBall p r0 ⊆ (A.chart i).target → Differentiable ℂ q → (∀ v ∈ closedBall p r0, A.ph H i ((A.chart i).symm v) - 2 * (q v).re ≤ Cq * ‖v - p‖ ^ 2) → ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k ≥ k0, ∀ D : ι → Y → ℂ, A.IsSSec (A.kap + (G + k • H)) D → DifferentiableOn ℂ (D i ∘ (A.chart i).symm) (ball p r0) → n0 A (G + k • H) D ≤ ENNReal.ofReal (K * Real.exp (-c * k)) → ‖D i ((A.chart i).symm p) * Complex.exp (-(k * q p))‖ ≤ ε ∧ ‖fderiv ℂ (fun v => D i ((A.chart i).symm v) * Complex.exp (-(k * q v))) p‖ ≤ ε := by
  intro n Y _ _ _ _ _ ι La _ A H G i p r0 c Cq K q hr0 hc hsub hq hH ε hε

  set r : ℝ := min r0 (Real.sqrt (c / (2 * (|Cq| + 1)))) with hr
  have hCq1 : 0 < |Cq| + 1 := by positivity
  have hrpos : 0 < r := lt_min hr0 (Real.sqrt_pos.2 (by positivity))
  have hrr0 : r ≤ r0 := min_le_left _ _
  have hr2 : r ^ 2 ≤ c / (2 * (|Cq| + 1)) := by
    have h1 : r ≤ Real.sqrt (c / (2 * (|Cq| + 1))) := min_le_right _ _
    have h2 := pow_le_pow_left₀ hrpos.le h1 2
    rwa [Real.sq_sqrt (by positivity)] at h2
  have hsubr : closedBall p r ⊆ (A.chart i).target :=
    (closedBall_subset_closedBall hrr0).trans hsub
  have hball : ball p r ⊆ (A.chart i).target := ball_subset_closedBall.trans hsubr
  have hquad : ∀ v ∈ closedBall p r, A.ph H i ((A.chart i).symm v) - 2 * (q v).re ≤ c / 2 := by
    intro v hv
    have h := hH v (closedBall_subset_closedBall hrr0 hv)
    have hd : ‖v - p‖ ≤ r := by rw [← dist_eq_norm]; exact hv
    have hd2 : ‖v - p‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
    have h3 : Cq * ‖v - p‖ ^ 2 ≤ |Cq| * ‖v - p‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    have h4 : |Cq| * ‖v - p‖ ^ 2 ≤ |Cq| * (c / (2 * (|Cq| + 1))) :=
      mul_le_mul_of_nonneg_left (hd2.trans hr2) (abs_nonneg _)
    have h5 : |Cq| * (c / (2 * (|Cq| + 1))) ≤ c / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [abs_nonneg Cq]
    linarith

  obtain ⟨M, hM⟩ := hyq_bdd (f := fun v => Real.exp (A.ph G i ((A.chart i).symm v))) (c := p) (r := r)
    ((A.smooth_ph G i).continuousOn.rexp.mono hsubr)
  have hM0 : 0 ≤ M := (Real.exp_pos _).le.trans (hM p (mem_closedBall_self hrpos.le))

  obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.holomorphic_value_derivative_l2_ball n r hrpos

  have htend : Tendsto (fun k : ℕ => C * M * |K| * Real.exp (-(c / 2) * k)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => -(c / 2) * (k : ℝ)) atTop atBot :=
      (tendsto_natCast_atTop_atTop).const_mul_atTop_of_neg (by linarith)
    have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul (C * M * |K|)
    simpa using h2
  obtain ⟨k0, hk0⟩ := eventually_atTop.1 ((tendsto_order.1 htend).2 (ε ^ 2) (by positivity))
  refine ⟨k0, fun k hk D hD hDd hn0 => ?_⟩
  set u : V n → ℂ := fun v => D i ((A.chart i).symm v) * Complex.exp (-(k * q v)) with hu
  have hud : DifferentiableOn ℂ u (ball p r) :=
    (hDd.mono (ball_subset_ball hrr0)).mul
      ((Complex.differentiable_exp.comp ((hq.const_mul (k : ℂ)).neg)).differentiableOn)
  have hest := hC p u hud

  set la : La := G + k • H
  set f : Y → ℝ≥0∞ := fun y => ENNReal.ofReal (A.nsq (A.kap + la) D y) with hf
  have hfm : Measurable f :=
    ENNReal.measurable_ofReal.comp (A.aap_continuous_nsq _ D hD.2
      (fun j => (hD.1 j).continuousOn)).measurable

  have hpt : ∀ v ∈ ball p r, ENNReal.ofReal (‖u v‖ ^ 2) ≤
      ENNReal.ofReal (M * Real.exp (k * (c / 2))) *
        (f ((A.chart i).symm v) * ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v)))) := by
    intro v hv
    set y := (A.chart i).symm v
    have hy : y ∈ (A.chart i).source := (A.chart i).map_target (hball hv)
    have hns := hyq_nsq_chart A (A.kap + la) D i y hy (hD.2 i (A.pick y) y hy (A.mem_pick y))
    have hph : A.ph (A.kap + la) i y = A.ph A.kap i y + (A.ph G i y + k * A.ph H i y) := by
      rw [A.ph_add _ _ i y hy, A.ph_add _ _ i y hy, ph_nsmul A H i y hy]
    simp only [hf]
    rw [hns, hph, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hnu : ‖u v‖ ^ 2 = ‖D i y‖ ^ 2 * Real.exp (-(2 * k * (q v).re)) := by
      simp only [hu, norm_mul, Complex.norm_exp, mul_pow]
      congr 1
      rw [← Real.exp_nat_mul]
      congr 1
      simp [Complex.neg_re, Complex.mul_re]
      ring
    rw [hnu]
    have hq2 := hquad v (ball_subset_closedBall hv)
    have hMv := hM v (ball_subset_closedBall hv)
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have key : Real.exp (-(2 * k * (q v).re)) ≤
        M * Real.exp (k * (c / 2)) * (Real.exp (-(A.ph A.kap i y + (A.ph G i y + k * A.ph H i y))) *
          Real.exp (A.ph A.kap i y)) := by
      calc Real.exp (-(2 * k * (q v).re))
          ≤ Real.exp (A.ph G i y) * Real.exp (k * (c / 2)) *
              (Real.exp (-(A.ph A.kap i y + (A.ph G i y + k * A.ph H i y))) *
                Real.exp (A.ph A.kap i y)) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
            apply Real.exp_le_exp.2
            nlinarith [mul_le_mul_of_nonneg_left hq2 hk0]
        _ ≤ _ := by gcongr
    calc ‖D i y‖ ^ 2 * Real.exp (-(2 * k * (q v).re))
        ≤ ‖D i y‖ ^ 2 * (M * Real.exp (k * (c / 2)) *
          (Real.exp (-(A.ph A.kap i y + (A.ph G i y + k * A.ph H i y))) * Real.exp (A.ph A.kap i y))) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = _ := by ring
  have hint : ∫⁻ v in ball p r, ENNReal.ofReal (‖u v‖ ^ 2) ≤
      ENNReal.ofReal (M * Real.exp (k * (c / 2))) * n0 A la D := by
    calc ∫⁻ v in ball p r, ENNReal.ofReal (‖u v‖ ^ 2)
        ≤ ∫⁻ v in ball p r, ENNReal.ofReal (M * Real.exp (k * (c / 2))) *
            (f ((A.chart i).symm v) * ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v)))) :=
          setLIntegral_mono' measurableSet_ball hpt
      _ = ENNReal.ofReal (M * Real.exp (k * (c / 2))) * ∫⁻ v in ball p r,
            f ((A.chart i).symm v) * ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (M * Real.exp (k * (c / 2))) * n0 A la D := by
          gcongr
          exact A.aap_lintegral_chart_le i f hfm _ hball

  have hall : ENNReal.ofReal (‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2) ≤
      ENNReal.ofReal (C * M * |K| * Real.exp (-(c / 2) * k)) := by
    calc ENNReal.ofReal (‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2)
        ≤ ENNReal.ofReal C * (ENNReal.ofReal (M * Real.exp (k * (c / 2))) *
            ENNReal.ofReal (|K| * Real.exp (-c * k))) := by
          refine hest.trans ?_
          gcongr
          refine hint.trans ?_
          gcongr
          exact hn0.trans (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le))
      _ = ENNReal.ofReal (C * M * |K| * Real.exp (-(c / 2) * k)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC0]
          congr 1
          have : Real.exp (k * (c / 2)) * Real.exp (-c * k) = Real.exp (-(c / 2) * k) := by
            rw [← Real.exp_add]; congr 1; ring
          calc C * (M * Real.exp (k * (c / 2)) * (|K| * Real.exp (-c * k)))
              = C * M * |K| * (Real.exp (k * (c / 2)) * Real.exp (-c * k)) := by ring
            _ = _ := by rw [this]
  have hsq : ‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2 ≤ ε ^ 2 := by
    have hb := (hk0 k hk).le
    rcases (ENNReal.ofReal_le_ofReal_iff'.1 hall) with h | h
    · linarith
    · nlinarith [sq_nonneg ε]
  have h1 : ‖u p‖ ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg ‖fderiv ℂ u p‖]
  have h2 : ‖fderiv ℂ u p‖ ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg ‖u p‖]
  exact ⟨by nlinarith [norm_nonneg (u p)], by nlinarith [norm_nonneg (fderiv ℂ u p)]⟩

end GlobalTheory.JetSmall
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.cohomologyContinuous_base_change_of_levels : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), (∀ k : SimplexCategoryᵒᵖ, ∃ (X : Scheme.{0}) (r : X ⟶ S) (e : yoneda.obj X ≅ E.obj k), e.hom ≫ p.app k = yoneda.map r ∧ ContCone R F ((bc (sch.map r)).mapCone c)) → ContCone R F ((bc p).mapCone c) := by
  first | (exact @GlobalTheory.EtC.CcStep.cc_step) | (exact GlobalTheory.EtC.CcStep.cc_step) | (intros; apply GlobalTheory.EtC.CcStep.cc_step <;> assumption)
end
