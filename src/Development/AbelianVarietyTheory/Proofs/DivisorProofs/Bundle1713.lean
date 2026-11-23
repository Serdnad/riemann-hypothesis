module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle662
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle628
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle036
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaComplexConjugationCompatible
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle301
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle277
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntertwinerSelfDualVacuumIsVacuum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorCoeffConjugateSeries
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTaylorCoeffsAlgebraicAtComplexMultiplicatio
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateGaloisRationalityCmPoints
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle303
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaVacuaConjugatesCmPoints
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumNormConjCmPointsAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1512
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1677
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitUniq

theorem splitUniq : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (N g : GL (Fin n) (w.adicCompletion E)), N ∈ GlobalTheory.LFun.KGL w (n := n) →
    (∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧ u * N.val.charpoly + v * derivative N.val.charpoly = 1) →
    g⁻¹ * N * g ∈ GlobalTheory.LFun.KGL w (n := n) → ∃ t : GL (Fin n) (w.adicCompletion E), t * N = N * t ∧ ∃ k ∈ GlobalTheory.LFun.KGL w (n := n), g = t * k := by
  intro E _ _ n w N g hN hs hg
  letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
  have key : ∀ x : w.adicCompletion E, ‖x‖ ≤ 1 ↔ x ∈ w.adicCompletionIntegers E := fun x => by
    rw [Valued.toNormedField.norm_le_one_iff, HeightOneSpectrum.mem_adicCompletionIntegers]
  have memK : ∀ h : GL (Fin n) (w.adicCompletion E), h ∈ GlobalTheory.LFun.KGL w (n := n) ↔
      (∀ i j, h.1 i j ∈ w.adicCompletionIntegers E) ∧ ∀ i j, (h⁻¹).1 i j ∈ w.adicCompletionIntegers E := fun h => by
    rw [GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff]; rfl
  obtain ⟨hN1, -⟩ := (memK N).1 hN
  obtain ⟨hg1, -⟩ := (memK _).1 hg
  obtain ⟨u, v, hu, hv, huv⟩ := hs
  have hconj : ((g⁻¹ * N * g : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      (g : Matrix (Fin n) (Fin n) (w.adicCompletion E))⁻¹ * N * g := by
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
  obtain ⟨t, k, ht, htN, hk, hdet, hgtk⟩ := GlobalTheory.SplitLattice.split_place (w.adicCompletion E) n N.val g.val
    (fun i j => (key _).2 (hN1 i j)) ⟨u, v, fun i => (key _).2 (hu i), fun i => (key _).2 (hv i), huv⟩ g.isUnit
    (fun i j => (key _).2 (by rw [← hconj]; exact hg1 i j))
  set tU := ht.unit with htU
  refine ⟨tU, Units.ext htN, tU⁻¹ * g, ?_, by rw [mul_inv_cancel_left]⟩
  have hkv : ((tU⁻¹ * g : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = k := by
    have htt : (tU : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = t := ht.unit_spec
    rw [Units.val_mul, hgtk, ← htt, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  have hkI : ∀ i j, k i j ∈ w.adicCompletionIntegers E := fun i j => (key _).1 (hk i j)
  let M : Matrix (Fin n) (Fin n) (w.adicCompletionIntegers E) := Matrix.of fun i j => ⟨k i j, hkI i j⟩
  have hMk : M.map (w.adicCompletionIntegers E).subtype = k := by ext i j; rfl
  have hdetM : ((M.det : w.adicCompletionIntegers E) : w.adicCompletion E) = k.det := by
    rw [← hMk]
    exact (RingHom.map_det (w.adicCompletionIntegers E).subtype M)
  have hk0 : k.det ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hdet; exact zero_ne_one hdet
  have hMu : IsUnit M.det := by
    have h1 : M.det * ⟨(k.det)⁻¹, (key _).1 (by rw [norm_inv, hdet, inv_one])⟩ = 1 := by
      apply Subtype.ext
      show ((M.det : w.adicCompletionIntegers E) : w.adicCompletion E) * (k.det)⁻¹ = 1
      rw [hdetM, mul_inv_cancel₀ hk0]
    exact ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  have hMM : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hMu
  have hinv : k⁻¹ = M⁻¹.map (w.adicCompletionIntegers E).subtype := by
    apply Matrix.inv_eq_right_inv
    rw [← hMk, ← Matrix.map_mul, hMM, Matrix.map_one _ (map_zero _) (map_one _)]
  refine (memK _).2 ⟨fun i j => by rw [hkv]; exact hkI i j, fun i j => ?_⟩
  rw [Matrix.coe_units_inv, hkv, hinv]
  exact (M⁻¹ i j).2

end GlobalTheory.SplitUniq
end

section

open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict
open GlobalTheory.SW hiding Level
open scoped ComplexConjugate Classical

namespace GlobalTheory.Dict.ThetaHalf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem EF_inv_smul (X : Data E r) (M : ℕ) (u v : Fin r → E) :
    EF X ((M : E)⁻¹ • u) v = (M : ℚ)⁻¹ * EF X u v := by
  have h : (M : E)⁻¹ • u = (M : ℚ)⁻¹ • u := by
    funext j
    simp [Rat.smul_def]
  rw [h, TensLat.EF_eq_bilin, TensLat.EF_eq_bilin, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem mem_smul_iff (X : Data E r) {L : Lt E r} (hL : SelfD X L) {𝔪 : Ideal (𝓞 E)} {M : ℕ}
    (hM : M ≠ 0) (h𝔪 : 𝔪 * conjI 𝔪 = Ideal.span {(M : 𝓞 E)}) (x : Fin r → E) :
    x ∈ 𝔪 • L ↔ ∀ y ∈ 𝔪 • L, ∃ k : ℤ, (M : ℚ)⁻¹ * EF X x y = k := by
  have hME : (M : E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hcc : ∀ a : E, cc (cc a) = a := fun a => IsCMField.complexConj_apply_apply E a
  constructor
  · intro hx y hy
    refine Submodule.smul_induction_on hx (fun a ha u hu => ?_) fun x₁ x₂ h₁ h₂ => ?_
    · refine Submodule.smul_induction_on hy (fun b hb v hv => ?_) fun y₁ y₂ h₁ h₂ => ?_
      · let b' : 𝓞 E := ⟨cc (b : E), Base.isIntegral_cc b.isIntegral_coe⟩
        have hb' : b' ∈ conjI 𝔪 := Ideal.subset_span ⟨b, hb, rfl⟩
        obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (h𝔪 ▸ Ideal.mul_mem_mul ha hb')
        have ht' : (t : E) * M = a * cc (b : E) := by
          have h5 := congrArg (algebraMap (𝓞 E) E) ht
          rw [map_mul, map_mul, map_natCast] at h5
          exact h5
        obtain ⟨k, hk⟩ := (hL.2 _).1 (L.smul_mem t hu) v hv
        refine ⟨k, ?_⟩
        rw [← hk, ← EF_inv_smul]
        change EF X ((M : E)⁻¹ • (a : E) • u) ((b : E) • v) = EF X ((t : E) • u) v
        rw [← hcc (b : E), ← TensLat.EF_smul, smul_smul, smul_smul]
        congr 2
        field_simp
        linear_combination -ht'
      · obtain ⟨k₁, h₁⟩ := h₁
        obtain ⟨k₂, h₂⟩ := h₂
        refine ⟨k₁ + k₂, ?_⟩
        rw [Int.cast_add, ← h₁, ← h₂]
        simp only [TensLat.EF_eq_bilin, map_add (f := _), mul_add]
    · obtain ⟨k₁, h₁⟩ := h₁
      obtain ⟨k₂, h₂⟩ := h₂
      refine ⟨k₁ + k₂, ?_⟩
      rw [Int.cast_add, ← h₁, ← h₂]
      simp only [TensLat.EF_eq_bilin, map_add (f := _), mul_add, LinearMap.add_apply]
  · intro h
    have h1 : ∀ b ∈ conjI 𝔪, b • (M : E)⁻¹ • x ∈ L := by
      intro b hb
      induction hb using Submodule.span_induction with
      | mem b hb =>
        obtain ⟨a, ha, hb⟩ := hb
        refine (hL.2 _).2 fun u hu => ?_
        obtain ⟨k, hk⟩ := h _ (Submodule.smul_mem_smul ha hu)
        refine ⟨k, ?_⟩
        change EF X ((b : E) • (M : E)⁻¹ • x) u = k
        rw [hb, TensLat.EF_smul, hcc, EF_inv_smul]
        exact hk
      | zero => simp
      | add a b _ _ ha hb => rw [add_smul]; exact L.add_mem ha hb
      | smul t a _ ha => rw [smul_eq_mul, mul_smul]; exact L.smul_mem t ha
    have h2 : ∀ c ∈ 𝔪 * conjI 𝔪, c • (M : E)⁻¹ • x ∈ 𝔪 • L := by
      intro c hc
      refine Submodule.mul_induction_on hc (fun a ha b hb => ?_) fun c₁ c₂ h₁ h₂ => ?_
      · rw [mul_smul]; exact Submodule.smul_mem_smul ha (h1 b hb)
      · rw [add_smul]; exact add_mem h₁ h₂
    have h3 := h2 M (h𝔪 ▸ Ideal.mem_span_singleton_self _)
    have h4 : (M : 𝓞 E) • (M : E)⁻¹ • x = x := by
      rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hME,
        one_smul]
    rwa [h4] at h3

theorem span_smul (X : Data E r) {L : Lt E r} (hL : SelfD X L) {𝔪 : Ideal (𝓞 E)} {M : ℕ}
    (hM : M ≠ 0) (h𝔪 : 𝔪 * conjI 𝔪 = Ideal.span {(M : 𝓞 E)}) :
    Submodule.span E ((𝔪 • L : Lt E r) : Set (Fin r → E)) = ⊤ := by
  have hME : (M : E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hMm : (M : 𝓞 E) ∈ 𝔪 := by
    refine Ideal.mul_le_left (J := conjI 𝔪) ?_
    rw [h𝔪]
    exact Ideal.mem_span_singleton_self _
  rw [eq_top_iff, ← TensLat.span_of_selfD X hL, Submodule.span_le]
  intro u hu
  have h1 : (M : E)⁻¹ • (M : 𝓞 E) • u = u := by
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, smul_smul, inv_mul_cancel₀ hME,
      one_smul]
  have h2 : (M : 𝓞 E) • u ∈ 𝔪 • L := Submodule.smul_mem_smul hMm hu
  have h3 := Submodule.smul_mem _ (M : E)⁻¹ (Submodule.subset_span (R := E) h2)
  rw [h1] at h3
  exact h3

theorem exists_ne_zero_of_scaled {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    {g : ℕ} (B : LinearMap.BilinForm ℚ V) (p : V →ₗ[ℤ] (Fin g → ℂ)) (hp : Function.Injective p)
    (L : Submodule ℤ V) (hfg : L.FG) {M : ℕ} (hM : 2 ≤ M)
    (hL : ∀ x, x ∈ L ↔ ∀ y ∈ L, ∃ k : ℤ, (M : ℚ)⁻¹ * B x y = k)
    (hsp : Submodule.span ℝ (p '' (L : Set V)) = ⊤) {Hm : Matrix (Fin g) (Fin g) ℂ}
    (hH : Hm.IsHermitian) (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re)
    (hB : ∀ u v, (p u ⬝ᵥ Hm.mulVec (star (p v))).im = (B u v : ℝ)) (c : V → ℂ)
    (hc : ∀ v, ‖c v‖ = 1) {f : (Fin g → ℂ) → ℂ} (hd : Differentiable ℂ f) (h0 : f ≠ 0)
    (hf : ∀ v ∈ L, ∀ z, f (z + p v) = (c v * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (p v))) +
      Real.pi / 2 * (p v ⬝ᵥ Hm.mulVec (star (p v))))) * f z) :
    ∃ v ∈ L, f ((M : ℂ)⁻¹ • p v) ≠ 0 := by
  have hM0 : M ≠ 0 := by omega
  have hMC : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hM0
  have hMR : (0 : ℝ) < (M : ℝ)⁻¹ := by positivity
  have hsc : ∀ z u : Fin g → ℂ, z ⬝ᵥ ((M : ℝ)⁻¹ • Hm).mulVec u = (M : ℝ)⁻¹ • (z ⬝ᵥ Hm.mulVec u) :=
    fun z u => by rw [smul_mulVec, dotProduct_smul]
  refine GlobalTheory.T.thetaFunction_ne_zero_at_divisionPoint_selfDual V g ((M : ℚ)⁻¹ • B) p hp L hfg hL hsp ((M : ℝ)⁻¹ • Hm) ?_ (fun z hz => ?_)
    (fun u v => ?_) c hc M hM f hd h0 fun v hv z => ?_
  · ext i j
    rw [conjTranspose_apply, Matrix.smul_apply, Matrix.smul_apply, star_smul, hH.apply, star_trivial]
  · rw [hsc, smul_re, smul_eq_mul]
    exact mul_pos hMR (hpos z hz)
  · rw [hsc, smul_im, LinearMap.smul_apply, LinearMap.smul_apply, hB]
    simp
  · rw [hf v hv z, hsc, hsc]
    congr 3
    simp only [real_smul]
    push_cast
    field_simp

theorem exists_ne_zero_on_half : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → ∀ (w : E) (L : Lt E r), SelfD X L → ∀ x ∈ X.dom, ∀ (𝔪 : Ideal (𝓞 E)) (M : ℕ), 2 ≤ M → 𝔪 * conjI 𝔪 = Ideal.span {(M : 𝓞 E)} → ∀ ϑ : (Fin g → ℂ) → ℂ, IsTheta1 X bas idx w x L ϑ → ϑ ≠ 0 → ∃ u ∈ 𝔪 • L, ϑ (pv X idx x ((M : E)⁻¹ • u)) ≠ 0 := by
  intro E _ _ _ r X g bas idx hs w L hL x hx' 𝔪 M hM h𝔪 θ hθ h0
  have hM0 : M ≠ 0 := by omega
  obtain ⟨hconj, hpos, him, -, hsm, hinj, hspan, -⟩ :=
    GlobalTheory.Dict.hx_laws E r X g bas idx 0 hs Even.zero x hx'
  set Hm := (hMat X bas idx x)ᵀ * imInv X bas idx x * (hMat X bas idx x).map star with hHm
  have hform : ∀ z u, hx X bas idx x z u = z ⬝ᵥ Hm.mulVec (star u) := fun z u =>
    SiegelNormalForm.form_pull _ _ z u
  have hH : Hm.IsHermitian := by
    ext i j
    have := hconj (Pi.single j 1) (Pi.single i 1)
    rw [hform, hform, SiegelNormalForm.form_single, SiegelNormalForm.form_single] at this
    exact this.symm
  clear_value Hm
  let p : (Fin r → E) →ₗ[ℤ] (Fin g → ℂ) := (AddMonoidHom.mk' (pv X idx x) fun u v => by
    unfold pv; rw [per_add]; rfl).toIntLinearMap
  have hp : ∀ v, p v = pv X idx x v := fun _ => rfl
  have hne : ∀ v, eps1 X w v ≠ 0 := fun v => Complex.exp_ne_zero _
  have key : ∀ v ∈ L, ∀ z, θ (z + p v) =
      ((eps1 X w v)⁻¹ * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (p v))) +
      Real.pi / 2 * (p v ⬝ᵥ Hm.mulVec (star (p v))))) * θ z := by
    intro v hv z
    have h1 := congrFun (hθ.2 v hv) z
    simp only [Pi.smul_apply, smul_eq_mul, fock, hform, add_dotProduct, smul_dotProduct] at h1
    rw [← h1, ← hp, _root_.mul_mul_mul_comm, inv_mul_cancel₀ (hne v), _root_.one_mul,
      ← _root_.mul_assoc, ← Complex.exp_add]
    refine (_root_.one_mul _).symm.trans ?_
    congr 1
    refine Complex.exp_zero.symm.trans (congrArg _ ?_)
    push_cast
    ring
  obtain ⟨u, hu, hu0⟩ := exists_ne_zero_of_scaled (traceFormBilin (X.κ0 / 2) X.Gm) p hinj
    ((𝔪 • L).restrictScalars ℤ)
    (Submodule.FG.of_le hL.1 (Submodule.smul_le_right (I := 𝔪))).restrictScalars hM
    (fun u => by simp only [← TensLat.EF_eq_bilin]; exact mem_smul_iff X hL hM0 h𝔪 u)
    (hspan _ (span_smul X hL hM0 h𝔪)).1 hH (fun z hz => hform z z ▸ hpos z hz)
    (fun u v => by rw [← TensLat.EF_eq_bilin, ← him, hform, hp, hp])
    (fun v => (eps1 X w v)⁻¹)
    (fun v => by
      have : eps1 X w v = cexp ((Real.pi * (EF X v (w • v) : ℚ) : ℝ) * I) := by
        unfold eps1; congr 1; push_cast; ring
      rw [norm_inv, this, Complex.norm_exp_ofReal_mul_I, inv_one])
    hθ.1 h0 (fun v hv => key v (Submodule.smul_le_right (I := 𝔪) hv))
  refine ⟨u, hu, ?_⟩
  have e : pv X idx x ((M : E)⁻¹ • u) = (M : ℂ)⁻¹ • p u := by
    rw [hsm]
    funext j
    rw [map_inv₀, map_natCast, hp, Pi.smul_apply, smul_eq_mul]
  rwa [e]

end GlobalTheory.Dict.ThetaHalf
end

section

open NumberField
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame)
open GlobalTheory.ThFr (IsSympl per_add)
open GlobalTheory.Dict (pv pv_smul span_range_pv)

namespace GlobalTheory.FrameEquiv

theorem dense_of_rat_of_span {V : Type} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [ContinuousAdd V]
    [ContinuousSMul ℝ V] (S : Set V) (h0 : (0 : V) ∈ S) (ha : ∀ u ∈ S, ∀ v ∈ S, u + v ∈ S)
    (hq : ∀ q : ℚ, ∀ u ∈ S, (q : ℝ) • u ∈ S) (hS : Submodule.span ℝ S = ⊤) : Dense S := by
  let P : Submodule ℝ V :=
    { carrier := closure S
      zero_mem' := subset_closure h0
      add_mem' := fun {a b} h1 h2 => map_mem_closure₂ continuous_add h1 h2 ha
      smul_mem' := fun t a h1 => by
        have ht : t ∈ closure (Set.range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast t
        refine map_mem_closure₂ (f := fun (s : ℝ) (v : V) => s • v) continuous_smul ht h1 ?_
        rintro _ ⟨q, rfl⟩ u hu
        exact hq q u hu }
  have hP : Submodule.span ℝ S ≤ P := Submodule.span_le.2 subset_closure
  intro z
  exact hP (hS ▸ Submodule.mem_top)

theorem denseRange_pv {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {g : ℕ}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) : DenseRange (pv X idx x) := by
  have hq (q : ℚ) (v : Fin r → E) : pv X idx x ((q : E) • v) = (q : ℝ) • pv X idx x v := by
    rw [pv_smul]
    funext j
    simp
  refine dense_of_rat_of_span _ ⟨0, ?_⟩ ?_ ?_ (span_range_pv idx hs hx)
  · simpa using hq 0 0
  · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    refine ⟨u + v, ?_⟩
    rw [pv, pv, pv, per_add]
    rfl
  · rintro q _ ⟨u, rfl⟩
    exact ⟨_, hq q u⟩

theorem exists_apply_pv_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → ∀ x ∈ X.dom, ∀ θ : (Fin g → ℂ) → ℂ, Continuous θ → θ ≠ 0 → ∃ v : Fin r → E, θ (pv X idx x v) ≠ 0 := by
  intro E _ _ _ r X g bas idx hs x hx θ hθ h0
  by_contra h
  push Not at h
  exact h0 ((denseRange_pv idx hs hx).equalizer hθ continuous_const (funext h))

end GlobalTheory.FrameEquiv
end

section

namespace GlobalTheory.ConjTranslate

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ConjJet
open scoped BigOperators

theorem mem_Th (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a d : ℕ) (L L')
    (h1 : SD D L) (h2 : SD D L') (G : VC D a d → ℂ)
    (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G) : G ∈ Th D (tor0 D cc δ) L L' := by
  have hg := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨b, κ, hb, -, rfl⟩ := hG
  obtain ⟨-, ⟨hd, hinv⟩, -⟩ := GlobalTheory.theta_translation_intertwiner_unitary D cc δ hc a d _ _
    (Or.inl ⟨_, b, hb, rfl⟩)
    (Or.inr ⟨L, L', h1, h2, rfl⟩) _ (GlobalTheory.VacuumMove.pullbackOrthonormal_normalizedTheta_mem_thetaSpace D hg cc δ t0 hc ht b hb.1)
  refine ⟨hd.const_mul κ, fun x hx z => ?_⟩
  have := hinv x hx z
  simp only [U] at this ⊢
  rw [show (tor0 D cc δ).abelian₂ = lamOf D cc δ from rfl, ← this]
  ring

theorem conj_fix (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a d : ℕ) (L L')
    (h1 : SD D L) (h2 : SD D L') (hev : Even (a * d)) (G : VC D a d → ℂ)
    (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G)
    (y : VC D a d) (hy : LaQ D (tor0 D cc δ) L L' y)
    (ρ : Qbar →ₐ[ℚ] ℂ) (hρ : FixK D Qbar ρ) :
    Differentiable ℂ (fnConj D Qbar ρ (U D (tor0 D cc δ) y G)) ∧
    fnConj D Qbar ρ (U D (tor0 D cc δ) y G) ≠ 0 ∧
    ∀ z, ‖fnConj D Qbar ρ (U D (tor0 D cc δ) y G) z‖ ^ 2 ≤ GlobalTheory.ColNorms.supConst D a d *
      normSq D (torConj D (tor0 D cc δ) Qbar ρ) (La D (torConj D (tor0 D cc δ) Qbar ρ) L L')
        (fnConj D Qbar ρ G) *
      Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / area (lamConj Qbar ρ (lamOf D cc δ))) := by
  obtain ⟨hg, hperm⟩ := GlobalTheory.InducedType.induced_type D
  have hGT := mem_Th D cc δ t0 hc ht a d L L' h1 h2 G hG
  obtain ⟨hdata, htors⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hg).2 cc δ hc
  obtain ⟨hA, hAU, -⟩ := GlobalTheory.ThetaAlgebraic.taylor_algebraic D cc δ hc t0 ht a d L L' h1 h2 hev G hG
  obtain ⟨hTh, -⟩ := GlobalTheory.ThetaConj.useConj_all D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA
  obtain ⟨t', ht'⟩ := (GlobalTheory.TwoTorsionPt.exists_point D cc δ hc).2 Qbar ρ hdata.2.1 hdata.2.2
  obtain ⟨hN, -⟩ := GlobalTheory.ConjNorm.useNorm_all D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA
    t' ht'
  obtain ⟨cc', δ', hc', -, hΛ⟩ := GlobalTheory.ConjCurve.galCurve_holds D cc δ hc Qbar ρ hρ hdata.2.1
    hdata.2.2 1 one_pos
  obtain ⟨π, hπ⟩ := hperm Qbar ρ hρ hdata.1
  have hne : fnConj D Qbar ρ G ≠ 0 := by
    intro h
    rw [h, hΛ] at hN
    rw [hΛ] at ht'
    refine pow_ne_zero _ (thetaZeroNormSq_ne_zero_cmLattice D hg cc' δ' t' hc' ht') (hN.symm.trans ?_)
    simp [normSq]
  obtain ⟨m, hm, hmy⟩ := id hy
  obtain ⟨y', hy', -⟩ := GlobalTheory.GalExist.galEx_all D cc δ hc Qbar ρ hρ hdata htors a d L L' h1 h2 y
    (2 * m) hy (by omega)
  have hgal := (GlobalTheory.GalTheta.gal_all D cc δ hc Qbar ρ hρ hdata a d L L' h1 h2 1 (fun _ => 1)
    (fun _ => 0) G y y' m
    hGT hm hmy (fun _ => by simp) hy' (by rw [comb_one]; exact hA)
    (by rw [comb_one]; exact hAU y hy)).1
  rw [comb_one] at hgal
  rw [hgal]
  refine ⟨U_diff D (torConj D (tor0 D cc δ) Qbar ρ) y' _ hTh.1, U_ne_zero D _ _ _ hne, fun z => ?_⟩
  have := sup_perm D hg cc' δ' hc' (torConj D (tor0 D cc δ) Qbar ρ) π hΛ hπ a d L L' h1 h2 _
    hTh y' z
  rw [Hf_re, ← mul_div_assoc] at this
  exact this

theorem conj_any (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a d : ℕ) (L L')
    (h1 : SD D L) (h2 : SD D L') (hev : Even (a * d)) (G : VC D a d → ℂ)
    (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G)
    (y : VC D a d) (hy : LaQ D (tor0 D cc δ) L L' y)
    (ρ : Qbar →ₐ[ℚ] ℂ) :
    Differentiable ℂ (fnConj D Qbar ρ (U D (tor0 D cc δ) y G)) ∧
    fnConj D Qbar ρ (U D (tor0 D cc δ) y G) ≠ 0 ∧
    ∀ z, ‖fnConj D Qbar ρ (U D (tor0 D cc δ) y G) z‖ ^ 2 ≤ GlobalTheory.ColNorms.supConst D a d *
      normSq D (torConj D (tor0 D cc δ) Qbar ρ) (La D (torConj D (tor0 D cc δ) Qbar ρ) L L')
        (fnConj D Qbar ρ G) *
      Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / area (lamConj Qbar ρ (lamOf D cc δ))) := by
  have hg := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hdata, -⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hg).2 cc δ hc
  obtain ⟨hA, -⟩ := GlobalTheory.ThetaAlgebraic.taylor_algebraic D cc δ hc t0 ht a d L L' h1 h2 hev G hG
  obtain ⟨hfix | hfix, htor, hbar⟩ := GlobalTheory.ThetaConj.useBar_holds D cc δ hc Qbar ρ hdata
  · exact conj_fix D cc δ t0 hc ht a d L L' h1 h2 hev G hG y hy ρ hfix
  · obtain ⟨hd, hne, hle⟩ := conj_fix D cc δ t0 hc ht a d L L' h1 h2 hev G hG y hy
      (rhoBar Qbar ρ) hfix
    obtain ⟨hTh, -⟩ := GlobalTheory.ThetaConj.useConj_all D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ
      hdata hA
    have hn2 := ((hbar a d L L' (fnConj D Qbar ρ G)).2.2 hTh).2 h1 h2 0
    rw [U_zero] at hn2
    have hL : lamConj Qbar (rhoBar Qbar ρ) (lamOf D cc δ) =
        (lamConj Qbar ρ (lamOf D cc δ)).map (starRingEnd ℂ).toAddMonoidHom :=
      congrArg Tor.abelian₂ htor
    rw [(hbar a d L L' G).1, htor, hn2, hL, area_conj] at hle
    rw [(hbar a d L L' _).1] at hd hne hle
    refine ⟨?_, fun h => hne ?_, fun z => ?_⟩
    · have := GlobalTheory.ThetaConj.differentiable_cBar hd
      rwa [GlobalTheory.ThetaConj.cBar_cBar] at this
    · rw [h]
      funext z
      simp [cBar]
    · have := hle (vBar D z)
      rw [cBar, GlobalTheory.ThetaConj.vBar_invol] at this
      simpa only [vBar, Complex.norm_conj] using this

end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem conj_translate : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (t0 : ℂ), StandardLatticesGL3.Crv D cc dl → GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc dl) t0 → ∀ (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → Even (a * b) → ∀ F : TaylorLogMetric.VC D a b → ℂ, StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L L' F → ∀ y, StandardLatticesGL3.LaQ D (TaylorLogMetric.tor0 D cc dl) L L' y → ∀ ρ : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, Differentiable ℂ (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc dl) y F) ∧ TaylorLogMetric.CoefIn D (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc dl) y F) TaylorLogMetric.Qbar ∧ ∃ F' : TaylorLogMetric.VC D a b → ℂ, Differentiable ℂ F' ∧ (∀ α, TaylorLogMetric.taylor D F' α = StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ (TaylorLogMetric.taylor D (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc dl) y F) α)) ∧ ∀ z, ‖F' z‖ ^ 2 ≤ supConst D a b * TaylorLogMetric.normSq D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ) (TaylorLogMetric.La D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ) L L') (TaylorLogMetric.fnConj D TaylorLogMetric.Qbar ρ F) * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / TaylorLogMetric.area (TaylorLogMetric.lamConj TaylorLogMetric.Qbar ρ (TaylorLogMetric.lamOf D cc dl))) := by
  intro D cc dl t0 hc ht a b L L' h1 h2 hev F hF y hy ρ
  obtain ⟨-, hAU, -⟩ := GlobalTheory.ThetaAlgebraic.taylor_algebraic D cc dl hc t0 ht a b L L' h1 h2 hev F hF
  obtain ⟨hd, hne, hle⟩ := conj_any D cc dl t0 hc ht a b L L' h1 h2 hev F hF y hy ρ
  exact ⟨GlobalTheory.ConjJet.U_diff D _ y F (mem_Th D cc dl t0 hc ht a b L L' h1 h2 F hF).1, hAU y hy,
    _, hd, (GlobalTheory.ConjSeries.taylor_fnConj D a b _ ρ _ hd hne).1, hle⟩

end GlobalTheory.ConjTranslate
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.centralizer_element_padic_bounded : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (r : ℕ) (z : Gr G r) (K : Subgroup (Gr G r)) (g : Gr G r), 0 < r → Subgroup.Commensurable K (KHT p G.m G.n r G.Fw) → ∀ w : P.cent, P.toQr r z w ∈ K.map (MulAut.conj g).toMonoidHom → ∀ (a : FM P), jM P a = ((w : G.Cˣ × ℚˣ).1 : G.C) → ∀ τ : FM P →+* PadicAlgCl p, LiesOver G.Kq G.u (τ.comp (algebraMap G.F (FM P))) → ‖τ a‖ ≤ 1 := by
  first | (exact @GlobalTheory.StabFin.norm_le_one_at_u) | (exact GlobalTheory.StabFin.norm_le_one_at_u) | (intros; apply GlobalTheory.StabFin.norm_le_one_at_u  <;> assumption)
end
