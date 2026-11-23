module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle249
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle212
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle288
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalConvolutionOrthogonalProjectorProof
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle280
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralInvOfSupport
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle131
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle010
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsZeroCoordNeZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle009
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle012
public import Formalism.PeriodIntegrals.Bundle004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle291
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle290
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle080
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.RowCusp

theorem level_comp_Re (B : RowsAut) (k : B.I.Gf) (hk : k ∈ B.I.Kg B.g) (hg : 1 ≤ B.g) :
    (B.R (1, k)).comp B.Re = B.Re := by
  obtain ⟨hR1, hRmul, hRnorm, -, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B

  have hπ1 : (fun a : B.I.Gf => B.R (1, a)) 1 = 1 := hR1
  have hπmul : ∀ a b : B.I.Gf, (fun a : B.I.Gf => B.R (1, a)) (a * b) =
      (fun a : B.I.Gf => B.R (1, a)) a * (fun a : B.I.Gf => B.R (1, a)) b := by
    intro a b
    have hab : ((1 : B.I.Ginf), a * b) = ((1 : B.I.Ginf), a) * (1, b) := by
      simp [Prod.mk_mul_mk]
    simp only
    rw [hab, hRmul]
  have hadj : ∀ (a : B.I.Gf) (u v : B.I.L2 B.μf B.fund),
      ⟪u, B.R (1, a) v⟫_ℂ = ⟪B.R (1, a⁻¹) u, v⟫_ℂ :=
    GlobalTheory.IdemProj.inner_rep (fun a : B.I.Gf => B.R (1, a)) hπ1 hπmul (fun a v => hRnorm _ v)

  have hone : (1 : B.I.Gf) ∈ B.I.Kg B.g := by
    refine ⟨?_, fun y _ => ⟨0, Submodule.zero_mem _, ?_⟩⟩
    · show ((1 : B.I.Gf) : GL (Fin B.I.n) (TensorProduct B.I.F B.I.E (Af B.I.F))) ∈ Formalism.UG.stabGL B.I.Lf
      simpa using (Formalism.UG.stabGL B.I.Lf).one_mem
    · simp [AutInst.fmat]
  have he : ∀ x, B.e (k * x) = B.e x := by
    intro x
    have h' := B.e_adm.2.2.2.2.2.1 x k hk 1 hone
    rwa [mul_one] at h'
  refine ContinuousLinearMap.ext (fun y => ext_inner_left ℂ (fun x => ?_))
  rw [ContinuousLinearMap.comp_apply, hadj, B.Re_spec.2, B.Re_spec.2]
  have hshift : ∀ g, B.e g * ⟪B.R (1, k⁻¹) x, B.R (1, g) y⟫_ℂ =
      (fun g => B.e g * ⟪x, B.R (1, g) y⟫_ℂ) (k * g) := by
    intro g
    simp only
    rw [he, ← inv_inv k, ← hadj, inv_inv, ← ContinuousLinearMap.mul_apply, ← hπmul]
  calc ∫ g, B.e g * ⟪B.R (1, k⁻¹) x, B.R (1, g) y⟫_ℂ ∂B.μf
      = ∫ g, (fun g => B.e g * ⟪x, B.R (1, g) y⟫_ℂ) (k * g) ∂B.μf := by
        congr 1
        funext g
        exact hshift g
    _ = ∫ g, B.e g * ⟪x, B.R (1, g) y⟫_ℂ ∂B.μf :=
        integral_mul_left_eq_self (μ := B.μf) (fun g => B.e g * ⟪x, B.R (1, g) y⟫_ℂ) k

theorem integrable_ph (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ) (hd : IsDSData B d) (hn : 1 ≤ B.I.n)
    (hh : ∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) (hl : LocDec B h) :
    Integrable (ph B d) (muInf B.I) := by
  obtain ⟨hcont, hbound, hmaj⟩ := GlobalTheory.Dec.PhMajProof.phMaj B d h hd hl

  have hgap : ∀ v, rkR (B.I.ε v) = 0 ∨
      8 * Real.sqrt (rkR (B.I.ε v)) * (0 + 4 * B.I.n * rkR (B.I.ε v)) < h := by
    intro v
    rcases Nat.eq_zero_or_pos (rkR (B.I.ε v)) with hq | hq
    · exact Or.inl hq
    · right
      have hqR : (0 : ℝ) < (rkR (B.I.ε v) : ℝ) := by exact_mod_cast hq
      have hnR : (1 : ℝ) ≤ (B.I.n : ℝ) := by exact_mod_cast hn
      have hsq : (0 : ℝ) < Real.sqrt (rkR (B.I.ε v) : ℝ) := Real.sqrt_pos.mpr hqR
      have hpow : ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) =
          (rkR (B.I.ε v) : ℝ) * Real.sqrt (rkR (B.I.ε v) : ℝ) := by
        rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hqR, Real.rpow_one,
          Real.sqrt_eq_rpow]
      have hv := hh v
      rw [hpow] at hv
      have hpos : 0 < (B.I.n : ℝ) * (rkR (B.I.ε v) : ℝ) * Real.sqrt (rkR (B.I.ε v) : ℝ) := by
        positivity
      nlinarith
  have hint : Integrable (majPh B d h) (muInf B.I) := by
    simpa using hmaj 0 le_rfl hgap
  exact hint.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

theorem row_isCuspFn : StrictLow → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.g → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h → HBig B 40 h → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ A ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (A (B.tens B.w))) := by
  intro hSL B d h hd hg hh hl hH T hT A hA
  rcases Nat.eq_zero_or_pos B.I.n with hn0 | hnpos
  ·
    intro W hW
    exfalso
    apply hW.1
    rw [Submodule.eq_bot_iff]
    intro x _
    funext i
    exact absurd i.2 (by omega)
  have hn : 1 ≤ B.I.n := hnpos

  obtain ⟨A₀, hA₀, hAeq⟩ := Submodule.mem_map.mp hA
  have hAc : A = B.Re.comp A₀ := hAeq.symm
  have hA₀' : ∀ g : B.I.Ginf, A₀.comp (B.σs g) = (B.R (g, 1)).comp A₀ := hA₀
  have hcomm : ∀ g : B.I.Ginf, B.Re.comp (B.R (g, 1)) = (B.R (g, 1)).comp B.Re :=
    (GlobalTheory.IdemProj.re_orth_proj B).2.1
  have hAS : A ∈ B.I.HomS B.σs B.μf B.fund B.R := by
    show ∀ g : B.I.Ginf, A.comp (B.σs g) = (B.R (g, 1)).comp A
    intro g
    rw [hAc, ContinuousLinearMap.comp_assoc, hA₀' g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]

  have hfix : ∀ k ∈ B.I.Kg B.g, B.R (1, k) (A (B.tens B.w)) = A (B.tens B.w) := by
    intro k hk
    rw [hAc]
    exact congrArg (fun L : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund => L (A₀ (B.tens B.w)))
      (level_comp_Re B k hk hg)
  obtain ⟨C, hC⟩ := GlobalTheory.T.exists_continuousRep_bounded_evaluation_rows hSL B d hd hn hg
  obtain ⟨f, hf, hfb⟩ := hC A hAS hfix

  have hTy : T (A (B.tens B.w)) = A (B.tens B.w) :=
    ((GlobalTheory.GlobProj.globalProj_holds B d hd (integrable_ph B d h hd hn hh hl)).2.2.2 T hT).2.1 A hA
  exact (GlobalTheory.T.cuspidal_of_convolution_fixed_moderate_growth B d h hd (GlobalTheory.T.integral_discreteSeries_unipotent_vanishes hSL B d h hd hl hh) hl hH T hT (A (B.tens B.w)) f
    (C * ‖A (B.tens B.w)‖) hTy hf (fun x => (hfb x).trans_eq (by ring))).2

end GlobalTheory.RowCusp
end
end

section

open NumberField Matrix

namespace GlobalTheory.FlagMeas

open ReciprocityTheory.ChartRestriction.G.FD

theorem exists_congr_of_hasSignature {n p q : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.UG.HasSignature M p q) (f : Fin n ≃ Fin p ⊕ Fin q) :
    ∃ A : Matrix (Fin n) (Fin n) ℂ, A.det ≠ 0 ∧
      Aᵀ * Mᵀ * A.map (starRingEnd ℂ) = ((Formalism.UG.Jpq p q).submatrix f f)ᵀ := by
  obtain ⟨e, P, hP⟩ := h
  have hPu : IsUnit (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 P.isUnit
  refine ⟨(P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e f, ?_, ?_⟩
  · have hσ : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e f =
        ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix f f).submatrix (e.trans f.symm) id := by
      ext i j; simp
    rw [hσ, Matrix.det_permute, Matrix.det_submatrix_equiv_self]
    exact mul_ne_zero (by simp) hPu.ne_zero
  · have hM : M = (M.reindex e e).submatrix e e := by ext i j; simp
    have hA : ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e f)ᴴ * M *
        (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e f = (Formalism.UG.Jpq p q).submatrix f f := by
      rw [hM, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, ← hP]
      congr 1
    rw [← hA]
    simp [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.conjTranspose]
    rfl

theorem sameKindIsometric : SameKindIsometric := by
  intro E _ _ _ hE n J J' hJ hJ' hd hd' hΛ hΛ' hsig
  obtain ⟨hTC, hφ, hun⟩ := hE
  have hne : ∃ z : E, star z ≠ z := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have hc := hTC.isComplex w
    rw [InfinitePlace.isComplex_iff] at hc
    apply hc
    rw [ComplexEmbedding.isReal_iff]
    ext z
    rw [ComplexEmbedding.conjugate_coe_eq, ← hφ, hcon]
  obtain ⟨hcm, hst⟩ := (GlobalTheory.LeastExponentCompare.conj_iff E star).1
    ⟨fun φ z => by rw [hφ]; rfl, hne⟩
  have := hcm
  have hcc : ∀ z : E, star z = cc z := fun z => congrFun hst z
  have : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := by
    refine Formalism.L2.Pj.unramBridge_holds E fun P hP => ?_
    obtain ⟨θ, t, ht, hθ⟩ := hun P hP
    refine ⟨θ, ?_⟩
    convert hθ using 2
    ext
    simp [ht, hcc, cc]
  have hform : ∀ (M : Matrix (Fin n) (Fin n) E) (x y : Fin n → E),
      ReciprocityTheory.ChartRestriction.G.FD.herm Mᵀ x y = star y ⬝ᵥ (M *ᵥ x) := by
    intro M x y
    simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.transpose_apply, Pi.star_apply, hcc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hone : ∀ z : E, z ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ↔ z ∈ (algebraMap (𝓞 E) E).range := by
    intro z
    rw [FractionalIdeal.mem_one_iff, RingHom.mem_range]
  have hmod : ∀ (M : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)),
      (∀ x, x ∈ L ↔ ∀ y ∈ L, star y ⬝ᵥ (M *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) →
      ∀ x, x ∈ L ↔ ∀ y ∈ L, ReciprocityTheory.ChartRestriction.G.FD.herm Mᵀ x y ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
    intro M L h x
    simp only [hone, hform]
    exact h x
  have hherm : ∀ M : Matrix (Fin n) (Fin n) E, Mᴴ = M → ∀ a b, cc (Mᵀ a b) = Mᵀ b a := by
    intro M hM a b
    rw [← hcc]
    have := congrFun (congrFun hM a) b
    simpa [Matrix.conjTranspose_apply] using this
  have hc : ∀ z ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), cc z ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
    intro z hz
    rw [FractionalIdeal.mem_one_iff] at hz ⊢
    obtain ⟨x, rfl⟩ := hz
    exact ⟨IsCMField.ringOfIntegersComplexConj E x, by simp [cc]⟩
  have hs : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧
      J'ᵀ.map τ = Qᵀ * Jᵀ.map τ * Q.map (starRingEnd ℂ) := by
    intro τ
    obtain ⟨p, q, h1, h2⟩ := hsig τ
    obtain ⟨e, -, -⟩ := id h1
    obtain ⟨A, hA, hA'⟩ := exists_congr_of_hasSignature h1 e
    obtain ⟨B, hB, hB'⟩ := exists_congr_of_hasSignature h2 e
    have hBi : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.2 hB)
    refine ⟨A * B⁻¹, by simp [Matrix.det_nonsing_inv, hA, hB], ?_⟩
    rw [Matrix.transpose_map, Matrix.transpose_map]
    have h1' : (B⁻¹)ᵀ * Bᵀ = 1 := by rw [← Matrix.transpose_mul, hBi, Matrix.transpose_one]
    have h2' : B.map (starRingEnd ℂ) * (B⁻¹).map (starRingEnd ℂ) = 1 := by
      rw [← Matrix.map_mul, hBi]
      simp
    have hY : (J'.map τ)ᵀ = (B⁻¹)ᵀ * (Bᵀ * (J'.map τ)ᵀ * B.map (starRingEnd ℂ)) *
        (B⁻¹).map (starRingEnd ℂ) := by
      simp only [← Matrix.mul_assoc]
      rw [h1', Matrix.one_mul, Matrix.mul_assoc, h2', Matrix.mul_one]
    rw [hY, hB', ← hA', Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  obtain ⟨Λ, hΛl, hΛm⟩ := hΛ
  obtain ⟨Λ', hΛl', hΛm'⟩ := hΛ'
  have hspan : ∀ (M : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)),
      Submodule.IsLattice E L →
      (∀ x, x ∈ L ↔ ∀ y ∈ L, star y ⬝ᵥ (M *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) →
      Submodule.span E (L : Set (Fin n → E)) = ⊤ := by
    intro M L hl hm
    classical
    obtain ⟨s, hs⟩ := hl.fg
    apply eq_top_iff.mpr
    intro z _
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E))
      (s.image fun y => star y ⬝ᵥ (M *ᵥ z))
    have hd0 : (algebraMap (𝓞 E) E d) ≠ 0 :=
      (IsFractionRing.injective (𝓞 E) E).ne (nonZeroDivisors.ne_zero d.2)
    have hdz : (algebraMap (𝓞 E) E d) • z ∈ L := by
      apply (hm _).2
      intro y hy
      rw [← hs] at hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, ha⟩ := hd _ (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
        refine ⟨a, ?_⟩
        rw [Matrix.mulVec_smul, dotProduct_smul]
        simpa only [smul_eq_mul, Algebra.smul_def] using ha
      | zero => simp
      | add x y hx hy ihx ihy =>
        simpa [star_add, add_dotProduct] using add_mem ihx ihy
      | smul a x hx ih =>
        have ha : star (algebraMap (𝓞 E) E a) ∈ (algebraMap (𝓞 E) E).range := by
          rw [hcc]
          exact ⟨IsCMField.ringOfIntegersComplexConj E a, by simp [cc]⟩
        have he : star (a • x) = star (algebraMap (𝓞 E) E a) • star x := by
          ext i
          simp [Algebra.smul_def]
        rw [he, smul_dotProduct]
        simpa only [smul_eq_mul] using mul_mem ha ih
    have hz : z = (algebraMap (𝓞 E) E d)⁻¹ • ((algebraMap (𝓞 E) E d) • z) := by
      rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hdz)
  obtain ⟨P, hPd, hP⟩ := GlobalTheory.SelfDualGenus.congr_of_modular
    (GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt) GlobalTheory.QNorm.hasseNormSt
    (by
      intro h
      have h1 : (1 : E) ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
        rw [FractionalIdeal.mem_one_iff]
        exact ⟨1, map_one _⟩
      rw [h, FractionalIdeal.mem_zero_iff] at h1
      exact one_ne_zero h1) hc (hherm J hJ) (hherm J' hJ') (by rwa [Matrix.det_transpose])
    (by rwa [Matrix.det_transpose]) ⟨hΛl.fg, hspan J Λ hΛl hΛm⟩
    ⟨hΛl'.fg, hspan J' Λ' hΛl' hΛm'⟩
    (hmod J Λ hΛm) (hmod J' Λ' hΛm') hs
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero P hPd, ?_⟩
  have hT := congrArg Matrix.transpose hP
  rw [Matrix.transpose_transpose, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_transpose] at hT
  change Pᴴ * J * P = J'
  rw [hT, Matrix.mul_assoc]
  congr 1
  ext i j
  simp [Matrix.conjTranspose_apply, hcc]

end GlobalTheory.FlagMeas
end

section

open NumberField Formalism.HermitianLattices.Ext.L3

namespace GlobalTheory.Mass


open NumberField in
theorem _root_.GlobalTheory.Mass.binary_hermitian_represents : _root_.Formalism.HermitianLattices.Ext.L3.HermRepUnram := by
  unfold _root_.Formalism.HermitianLattices.Ext.L3.HermRepUnram
  intro K _ _ _ hK a b n ha hb hn hpa hpb hpn
  obtain ⟨w, hw0, hw⟩ := _root_.Formalism.HermitianLattices.Ext.L3.exists_skew hK
  have memF : ∀ x : K, star x = x → x ∈ _root_.Formalism.HermitianLattices.Ext.L3.cmF K := fun x hx => (_root_.Formalism.HermitianLattices.Ext.L3.mem_cmF_iff K x).2 hx
  obtain ⟨ψ₀⟩ : Nonempty (K →+* ℂ) := inferInstance
  have ne_of_pos : ∀ x : K, _root_.Formalism.HermitianLattices.Ext.L3.TotPos x → x ≠ 0 := by
    intro x hx h
    have := hx ψ₀
    simp [h] at this
  let a' : _root_.Formalism.HermitianLattices.Ext.L3.cmF K := ⟨a, memF a ha⟩
  let b' : _root_.Formalism.HermitianLattices.Ext.L3.cmF K := ⟨b, memF b hb⟩
  let n' : _root_.Formalism.HermitianLattices.Ext.L3.cmF K := ⟨n, memF n hn⟩
  let δ : _root_.Formalism.HermitianLattices.Ext.L3.cmF K := ⟨w * w, memF _ (by rw [star_mul, hw]; ring)⟩
  have hnegδ : _root_.Formalism.HermitianLattices.Ext.L3.TotPos ((-δ : _root_.Formalism.HermitianLattices.Ext.L3.cmF K) : K) := by
    unfold _root_.Formalism.HermitianLattices.Ext.L3.TotPos
    intro ψ
    have h1 : ψ (star w) = (starRingEnd ℂ) (ψ w) := hK.2.1 ψ w
    rw [hw, map_neg] at h1
    have hre : (ψ w).re = 0 := by
      have := congrArg Complex.re h1
      simp at this
      linarith
    have hne : ψ w ≠ 0 := (map_ne_zero ψ).2 hw0
    have him : (ψ w).im ≠ 0 := by
      intro him
      exact hne (Complex.ext hre him)
    simp [δ, Complex.mul_re, hre]
    positivity
  have hδneg : ∀ φ : _root_.Formalism.HermitianLattices.Ext.L3.cmF K →+* ℝ, φ δ < 0 := by
    intro φ
    have := (_root_.Formalism.HermitianLattices.Ext.L3.totPos_iff hK (-δ)).1 hnegδ φ
    simpa using this
  have ha' : a' ≠ 0 := fun h => ne_of_pos a hpa (congrArg Subtype.val h)
  have hb' : b' ≠ 0 := fun h => ne_of_pos b hpb (congrArg Subtype.val h)
  have hn' : n' ≠ 0 := fun h => ne_of_pos n hpn (congrArg Subtype.val h)
  have hδ0 : δ ≠ 0 := fun h => hw0 (mul_self_eq_zero.1 (congrArg Subtype.val h))
  let c : Fin 5 → _root_.Formalism.HermitianLattices.Ext.L3.cmF K := ![a', -(a' * δ), b', -(b' * δ), -n']
  have hc : ∀ i, c i ≠ 0 := by
    intro i
    fin_cases i <;> simp [c, ha', hb', hn', hδ0]
  obtain ⟨x, hx0, hx⟩ := _root_.GlobalTheory.LocalQuad.isotropic_of_indefinite _root_.GlobalTheory.QNorm.hasseNormSt
    (_root_.Formalism.HermitianLattices.Ext.L3.cmF K) c (by simp) hc (by
      intro σ
      refine ⟨4, 0, ?_, ?_⟩
      · simpa [c] using (_root_.Formalism.HermitianLattices.Ext.L3.totPos_iff hK n').1 hpn σ
      · simpa [c] using (_root_.Formalism.HermitianLattices.Ext.L3.totPos_iff hK a').1 hpa σ)
  obtain ⟨y, hy4, hy⟩ := _root_.GlobalTheory.LocalQuad.HermClass.exists_zero_coord_ne_zero hc hx0 hx 4
  have h4 : (y 4 : K) ≠ 0 := fun h => hy4 (Subtype.ext h)
  have hy' := congrArg (fun z : _root_.Formalism.HermitianLattices.Ext.L3.cmF K => (z : K)) hy
  simp [Fin.sum_univ_five, c, a', b', n', δ] at hy'
  refine ⟨((y 0 : K) + (y 1 : K) * w) / (y 4 : K), ((y 2 : K) + (y 3 : K) * w) / (y 4 : K), ?_⟩
  simp only [star_div₀, star_add, star_mul, _root_.Formalism.HermitianLattices.Ext.L3.star_coe_cmF, hw]
  field_simp
  linear_combination hy'

end GlobalTheory.Mass
end

section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.closed_matrix_subgroup_theorem : ∀ (m : ℕ) (S : Set (Matrix (Fin m) (Fin m) ℂ)), PI.IsMatGroup S → (∀ X : lieE S, unrealify (X : EuclideanSpace ℝ _) ∈ lieOf S) ∧ ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧ ∀ g ∈ S, (∀ i j, ‖(g - 1) i j‖ < δ) → Matrix.of.symm g ∈ expSet S (Metric.ball 0 ρ) := by
  first | exact @GlobalTheory.ClosedMatGroup.closed_subgroup | exact GlobalTheory.ClosedMatGroup.closed_subgroup | (intros; apply GlobalTheory.ClosedMatGroup.closed_subgroup <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory

theorem tsum_subtype_and_eq_ite {α : Type*} (S : Set α) (p q : α → Prop) (f : α → ℝ≥0∞)
    (h : ∀ t ∈ S, p t ↔ q t) :
    (∑' t : {t // t ∈ S ∧ p t}, f t.1) = ∑' t : S, (if q t.1 then f t.1 else 0) := by

  have hL : (∑' t : {t // t ∈ S ∧ p t}, f t.1) = ∑' t, ({t | t ∈ S ∧ p t} : Set α).indicator f t :=
    tsum_subtype {t | t ∈ S ∧ p t} f
  have hR : (∑' t : S, (if q t.1 then f t.1 else 0)) =
      ∑' t, S.indicator (fun t => if q t then f t else 0) t :=
    tsum_subtype S (fun t => if q t then f t else 0)
  rw [hL, hR]
  refine tsum_congr fun t => ?_
  by_cases hS : t ∈ S
  · have hpq := h t hS
    rw [Set.indicator_of_mem hS]
    by_cases hq : q t
    · rw [if_pos hq, Set.indicator_of_mem (show t ∈ {t | t ∈ S ∧ p t} from ⟨hS, hpq.2 hq⟩)]
    · rw [if_neg hq]
      exact Set.indicator_apply_eq_zero.mpr (fun (hm : t ∈ {t | t ∈ S ∧ p t}) =>
        absurd (hpq.1 hm.2) hq)
  · rw [Set.indicator_apply_eq_zero.mpr (fun (hm : t ∈ {t | t ∈ S ∧ p t}) =>
      absurd hm.1 hS), Set.indicator_apply_eq_zero.mpr (fun (hm : t ∈ S) => absurd hm hS)]

theorem mass_pairingClass_bounds : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), 4 * r + 7 ≤ k → Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (R : LocNG.Reps P) (d0 : LocNG.Datum P), (∃ t0 : Term V M r, LocNG.IsTermOver P d0 t0) → ∀ (d : LocNG.Datum P) (t : Term V M r), LocNG.IsTermOver P d t → ∀ (Y0 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (c1 : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) E)), c1 = {Y | ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ a b, b < a → A a b = 0) ∧ (∀ a, A a a = 1) ∧ ∀ a b, A a b ∈ M.L.O) ∧ ((∀ a b, b < a → A' a b = 0) ∧ (∀ a, A' a a = 1) ∧ ∀ a b, A' a b ∈ M.L.O) ∧ (∀ a b, A a b - A' a b ∈ Submodule.span M.L.O {algebraMap F E (LocNG.theta M)}) ∧ Y = (A.transpose.map M.L.cj) * Y0 * A'} → H.Zhat t.f t.f' ∈ c1 → ∀ g : ℝ≥0∞, g = (∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * ∑' t : R.RT d.1, (if ¬ LocNG.BBne (H := H) t.1 ∧ H.Zhat t.1.f t.1.f' ∈ c1 then ENNReal.ofReal (LocNG.mu P t.1) else 0)) → 0 < g ∧ g ≠ ⊤ ∧ (P.PrimeTo → LocNG.nn R d0 = g) ∧ LocNG.nn R d0 ≤ ENNReal.ofReal (8 * P.Hp ^ (9 * (r + 1) ^ 2 + 2 * (2 * r + 2))) * g := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hk hdim hrel R d0 hd0 d t hdt Y0 c1 hc1 ht g hg
  obtain ⟨t0, ht0⟩ := hd0

  let Cl : Term V M r → Prop := fun t' => ∃ s ∈ P.St, ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ i j, A i j ∈ M.L.O ∧ A' i j ∈ M.L.O ∧ ∃ c ∈ M.L.O, A' i j - A i j = algebraMap F E (LocNG.theta M) * c) ∧ (∀ i j, j < i → A i j = 0 ∧ A' i j = 0) ∧ (∀ i, A i i = 1 ∧ A' i i = 1) ∧ (∀ j, t'.f j = ∑ i, A i j • s (t.f i)) ∧ ∀ j, t'.f' j = ∑ i, A' i j • s (t.f' i)

  have hCl : ∀ (d' : LocNG.Datum P) (t' : Term V M r), LocNG.IsTermOver P d' t' →
      (H.Zhat t'.f t'.f' ∈ c1 ↔ Cl t') := fun d' t' h' =>
    GlobalTheory.T.term_over_relation_uniqueness M hM H r k P hdim hrel d d' t t' hdt h' Y0 c1 hc1 ht

  have hg' : g = ∑' d' : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d'.1) *
      ∑' t' : {t' // t' ∈ R.RT d'.1 ∧ ¬ LocNG.BBne (H := H) t' ∧ Cl t'},
        ENNReal.ofReal (LocNG.mu P t'.1) := by
    rw [hg]
    refine tsum_congr fun d' => ?_
    congr 1
    have e := tsum_subtype_and_eq_ite (R.RT d'.1) (fun t' => ¬ LocNG.BBne (H := H) t' ∧ Cl t')
      (fun t' => ¬ LocNG.BBne (H := H) t' ∧ H.Zhat t'.f t'.f' ∈ c1)
      (fun t' => ENNReal.ofReal (LocNG.mu P t'))
      (fun t' ht' => and_congr_right fun _ => (hCl d'.1 t' ((R.hRT d'.1).1 ht')).symm)
    convert e.symm
  obtain ⟨hne, hle, hprime, hpos⟩ :=
    GlobalTheory.T.hermitian_total_mass_le_generic_mass M hM H r k P hk hdim hrel R d0 d t hdt Cl (fun _ => Iff.rfl) g hg'
  exact ⟨pos_iff_ne_zero.mpr (hpos ⟨t0, ht0⟩), hne, hprime, hle⟩

end GlobalTheory
end
