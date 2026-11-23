module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.Bundle001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle004
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.CountableRationalPointsDoubled
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle001
public import Development.WeilBound.ThetaLifts.LatticeBasics.ContinuousFlat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IncMTranspose

@[expose] public section

section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def nilpotentFrameMatrix {d : SD σ} (L : LD d) (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  ∑ j, Matrix.single L.i₀ (L.em j) (u j)

theorem em_ne {d : SD σ} (L : LD d) (j : Fin L.n) : L.em j ≠ L.i₀ := ((L.rng (L.em j)).2 ⟨j, rfl⟩)

theorem nilpotent_frame_mul_zero {d : SD σ} (L : LD d) (u v : Fin L.n → AE F E) : nilpotentFrameMatrix L u * nilpotentFrameMatrix L v = 0 := by
  simp only [nilpotentFrameMatrix, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
  rw [Matrix.single_mul_single_of_ne]
  exact em_ne L _

theorem continuous_nilpotentFramePart {d : SD σ} (L : LD d) : Continuous (nilpotentFrameMatrix L) := by
  refine continuous_finsetSum _ fun j _ => ?_
  have : (fun u : Fin L.n → AE F E => Matrix.single L.i₀ (L.em j) (u j)) =
      fun u => u j • Matrix.single L.i₀ (L.em j) (1 : AE F E) := by
    funext u; rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this]
  exact (continuous_apply j).smul continuous_const

def muF {d : SD σ} (L : LD d) (u : Fin L.n → AE F E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks (1 + nilpotentFrameMatrix L u) 0 0 (((1 - nilpotentFrameMatrix L u)ᵀ).map (cA σ))

def muF' {d : SD σ} (L : LD d) (u : Fin L.n → AE F E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks (1 - nilpotentFrameMatrix L u) 0 0 (((1 + nilpotentFrameMatrix L u)ᵀ).map (cA σ))

theorem one_add_mul_one_sub {d : SD σ} (L : LD d) (u : Fin L.n → AE F E) :
    (1 + nilpotentFrameMatrix L u) * (1 - nilpotentFrameMatrix L u) = 1 := by
  rw [mul_sub, mul_one, add_mul, one_mul, nilpotent_frame_mul_zero, add_zero, add_sub_cancel_right]

theorem muF_mul {d : SD σ} (L : LD d) (u : Fin L.n → AE F E) : muF L u * muF' L u = 1 := by
  have e1 := one_add_mul_one_sub L u
  simp only [muF, muF', Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [e1, ← kunf.map_cA_mul, ← Matrix.transpose_mul, e1, Matrix.transpose_one,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.fromBlocks_one]

theorem inFrame_uM {d : SD σ} (L : LD d) {uM : (Fin L.n → AE F E) → d.G} {ν 𝓤} (h : L.UData uM ν 𝓤)
    (u : Fin L.n → AE F E) : inFrame d.b (uM u) = muF L u := by
  have hσ := kfour.sigma_sigma_of_good d.ok.good
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨a', ha⟩ := h.1 u
  change inFrame d.b (uM u) = Matrix.fromBlocks (1 + nilpotentFrameMatrix L u) 0 0 a' at ha
  have hf := kunf.frame_eq hε (uM u)
  rw [ha] at hf
  have h12 := congrArg Matrix.toBlocks₁₂ hf
  simp only [kunf.jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.transpose_zero, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, Matrix.toBlocks_fromBlocks₁₂] at h12
  have e2 : a'.map (cA σ) = (1 - nilpotentFrameMatrix L u)ᵀ := by
    calc a'.map (cA σ) = ((1 - nilpotentFrameMatrix L u)ᵀ * (1 + nilpotentFrameMatrix L u)ᵀ) * a'.map (cA σ) := by
          rw [← Matrix.transpose_mul, one_add_mul_one_sub, Matrix.transpose_one, Matrix.one_mul]
      _ = (1 - nilpotentFrameMatrix L u)ᵀ := by rw [Matrix.mul_assoc, h12, Matrix.mul_one]
  have e3 : a' = ((1 - nilpotentFrameMatrix L u)ᵀ).map (cA σ) := by
    rw [← e2]
    ext i j
    simp [Matrix.map_apply, kfour.cA_cA' σ hσ]
  rw [ha, e3]
  rfl

theorem continuous_uM {d : SD σ} (L : LD d) {uM : (Fin L.n → AE F E) → d.G} {ν 𝓤} (h : L.UData uM ν 𝓤) :
    Continuous uM := by
  have hN := continuous_nilpotentFramePart L
  have hcA : Continuous fun M : Matrix (Fin d.n) (Fin d.n) (AE F E) => M.map (cA σ) :=
    continuous_id.matrix_map (GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ)
  have hc : Continuous (muF (σ := σ) L) :=
    Continuous.matrix_fromBlocks (continuous_const.add hN) continuous_const continuous_const
      (hcA.comp (continuous_const.sub hN).matrix_transpose)
  have hc' : Continuous (muF' (σ := σ) L) :=
    Continuous.matrix_fromBlocks (continuous_const.sub hN) continuous_const continuous_const
      (hcA.comp (continuous_const.add hN).matrix_transpose)
  have h1 : Continuous fun u => incM F d.b.1 * muF L u * incM F (d.b⁻¹).1 :=
    (continuous_const.matrix_mul hc).matrix_mul continuous_const
  have h2 : Continuous fun u => incM F d.b.1 * muF' L u * incM F (d.b⁻¹).1 :=
    (continuous_const.matrix_mul hc').matrix_mul continuous_const
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · refine h1.congr fun u => ?_
    show _ = mat2 (uM u)
    rw [kunf.matrix_eq_inFrame_conj d.b, inFrame_uM L h]
  · refine h2.congr fun u => ?_
    show _ = mat2 (uM u)⁻¹
    rw [kunf.matrix_eq_inFrame_conj d.b, GlobalTheory.EisBL.DoubledParabolic.inFrame_inv, inFrame_uM L h,
      Matrix.inv_eq_right_inv (muF_mul L u)]

end PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act

def IndepDom : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (L : LD d), ∀ s₁ f, IsSec d.K d.χ s₁ f → ∀ z : ℂ,
  (∀ nb lam 𝓖 𝓖₀, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖₀ →
    ∀ uM ν 𝓤 𝓤₀, L.UData uM ν 𝓤 → L.UData uM ν 𝓤₀ → ∀ T T', L.IsSub T T' → ∀ x,
      ∫ u in 𝓤, fc d.B.ψ d.b nb lam 𝓖 (d.eis f s₁ z) T (uM u * x) ∂ν =
        ∫ u in 𝓤₀, fc d.B.ψ d.b nb lam 𝓖₀ (d.eis f s₁ z) T (uM u * x) ∂ν) ∧
  ∀ nb' lam' 𝓖' 𝓖'₀, CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖' → CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖'₀ →
    ∀ T' x, first L f s₁ z nb' lam' 𝓖' T' x = first L f s₁ z nb' lam' 𝓖'₀ T' x

def CptDom : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ),
  (∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 →
    ∃ 𝓖₀, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖₀ ∧ IsCompact (closure 𝓖₀)) ∧
  ∀ L : LD d, ∀ uM ν 𝓤, L.UData uM ν 𝓤 → ∃ 𝓤₀, L.UData uM ν 𝓤₀ ∧ IsCompact (closure 𝓤₀)

def AbsConv : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (L : LD d), ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁ → ∃ t : ℝ, ∀ z : ℂ, t < z.re →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → IsCompact (closure 𝓖) →
  ∀ uM ν 𝓤, L.UData uM ν 𝓤 → IsCompact (closure 𝓤) → ∀ (T : nF σ d.Y d.b) (x : d.G),
    (∀ q : Cs d, Integrable (kq L f s₁ z nb T uM (rep q) x) ((ν.restrict 𝓤).prod (lam.restrict 𝓖))) ∧
    Summable fun q : Cs d => ∫ p, ‖kq L f s₁ z nb T uM (rep q) x p‖ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖))

def FirstEq : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (L : LD d), ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁ → ∃ t : ℝ, ∀ z : ℂ, t < z.re →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → IsCompact (closure 𝓖) →
  ∀ nb' lam' 𝓖', CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖' → IsCompact (closure 𝓖') →
  ∀ uM ν 𝓤, L.UData uM ν 𝓤 → IsCompact (closure 𝓤) → ∀ T T', L.IsSub T T' → ∀ x,
    ∑' q : {q : Cs d // LagrangianCondition L (rep q)}, tm L f s₁ z nb lam 𝓖 T uM ν 𝓤 (rep q.1) x = first L f s₁ z nb' lam' 𝓖' T' x


variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} in
structure CLaw {d : SD σ} (R : RD d) (L : LD d) (w₁ : d.G) (cM : (Fin L.n → AE F E) × AF F → d.G)
    (κ : Measure ((Fin L.n → AE F E) × AF F)) : Prop where
  comm : ∀ w (τ : ℝ) (y : GR d.n) (g : G2 σ L.Y), IsDil (Pi.single L.i₀ 1) τ y → L.j g * R.ι w y = R.ι w y * L.j g
  wdil : ∀ w (τ : ℝ) (y : GR d.n), IsDil (Pi.single L.i₀ 1) τ y → ∃ p t, IsPar p t ∧
    (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) = Real.exp (-(2 * τ)) ∧
    (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) = 1 ∧ w₁ * R.ι w y = p * w₁
  cdil : ∀ w (τ : ℝ) (y : GR d.n), IsDil (Pi.single L.i₀ 1) τ y →
    ∃ sc : ((Fin L.n → AE F E) × AF F) ≃ᵐ ((Fin L.n → AE F E) × AF F), (∀ c, cM c * R.ι w y = R.ι w y * cM (sc c)) ∧
      κ.map sc = ENNReal.ofReal (Real.exp (2 * d.n * τ)) • κ

def SecUnf : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d) (L : LD d), ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁ →
  ∃ t : ℝ, ∀ z : ℂ, t < z.re →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → IsCompact (closure 𝓖) →
  ∀ uM ν 𝓤, L.UData uM ν 𝓤 → IsCompact (closure 𝓤) → ∀ T T', L.IsSub T T' →
  ∀ nb' lam' 𝓖', CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖' → IsCompact (closure 𝓖') →
  ∃ w₁ cM κ, CLaw R L w₁ cM κ ∧ ∃ K : ℂ, ∀ x,
    sec2 L f s₁ z nb lam 𝓖 T uM ν 𝓤 x = K * ∑' q' : Cs L.sd, ∫ β in 𝓖',
      (∫ c, phz d f s₁ z (w₁ * (cM c * (L.j (rep q' * nb' β) * x))) ∂κ) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T'.1.1 * β.1)))) ∂lam'

def SecLaw : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d) (L : LD d), ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁ →
  ∃ t : ℝ, ∀ z : ℂ, t < z.re →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → IsCompact (closure 𝓖) →
  ∀ uM ν 𝓤, L.UData uM ν 𝓤 → IsCompact (closure 𝓤) → ∀ T T', L.IsSub T T' →
  ∀ nb' lam' 𝓖', CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖' → IsCompact (closure 𝓖') →
  ∀ w (τ : ℝ) (y : GR d.n) x, IsDil (Pi.single L.i₀ 1) τ y →
    sec2 L f s₁ z nb lam 𝓖 T uM ν 𝓤 (R.ι w y * x) = Complex.exp (τ * (d.n - 2 * z)) * sec2 L f s₁ z nb lam 𝓖 T uM ν 𝓤 x


variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} in
theorem phz_par {d : SD σ} {f : d.G → ℂ} {s₁ : ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {τ : ℝ} {p : d.G} {t : GL (Fin d.n) (AE F E)}
    (hp : IsPar p t) (ha : (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) = Real.exp (-(2 * τ)))
    (hχ : (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) = 1) (g : d.G) :
    phz d f s₁ z (p * g) = Complex.exp (-(τ * (2 * z + d.n))) * phz d f s₁ z g := by
  have hH : ((d.Ht (p * g) : ℝ) : ℂ) = (Real.exp (-(2 * τ)) : ℂ) * ((d.Ht g : ℝ) : ℂ) := by
    simp only [SD.Ht]
    rw [d.ok.hgt.mul hp, ha, Real.toNNReal_mul (Real.exp_pos _).le, NNReal.coe_mul, Real.coe_toNNReal _ (Real.exp_pos _).le,
      Complex.ofReal_mul]
  have he : ∀ w : ℂ, ((Real.exp (-(2 * τ)) : ℝ) : ℂ) ^ w = Complex.exp (-(2 * τ) * w) := by
    intro w
    rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _), Complex.log_exp] <;> push_cast <;> simp [Real.pi_pos, Real.pi_pos.le]
  unfold phz
  rw [hH, Complex.mul_cpow_ofReal_nonneg (Real.exp_pos _).le NNReal.zero_le_coe, hf.law p t g hp, hχ, ha, he, he,
    ← mul_assoc]
  have : Complex.exp (-(τ * (2 * z + d.n))) = Complex.exp (-(2 * τ) * (z - s₁)) * Complex.exp (-(2 * τ) * (s₁ + d.n / 2)) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [this]; ring

theorem secLaw_of : SecUnf → SecLaw := by
  intro hU F E _ _ _ _ _ σ d R L s₁ f hf he
  obtain ⟨t, ht⟩ := hU F E σ d R L s₁ f hf he
  refine ⟨t, fun z hz nb lam 𝓖 hc hcG uM ν 𝓤 hUd hcU T T' hTT' nb' lam' 𝓖' hc' hcG' w τ y x hy => ?_⟩
  obtain ⟨w₁, cM, κ, hL, K, hK⟩ := ht z hz nb lam 𝓖 hc hcG uM ν 𝓤 hUd hcU T T' hTT' nb' lam' 𝓖' hc' hcG'
  obtain ⟨p, tp, hp, ha, hχ, hw⟩ := hL.wdil w τ y hy
  obtain ⟨sc, hsc, hκ⟩ := hL.cdil w τ y hy
  have key : ∀ h : G2 σ L.Y, ∫ c, phz d f s₁ z (w₁ * (cM c * (L.j h * (R.ι w y * x)))) ∂κ =
      Complex.exp (τ * (d.n - 2 * z)) * ∫ c, phz d f s₁ z (w₁ * (cM c * (L.j h * x))) ∂κ := by
    intro h
    have h1 : ∀ c, w₁ * (cM c * (L.j h * (R.ι w y * x))) = p * (w₁ * (cM (sc c) * (L.j h * x))) := by
      intro c
      rw [← mul_assoc (L.j h), hL.comm w τ y h hy, mul_assoc, ← mul_assoc (cM c), hsc c, mul_assoc, ← mul_assoc w₁, hw,
        mul_assoc]
    simp_rw [h1, phz_par hf z hp ha hχ]
    rw [integral_const_mul, ← integral_map_equiv sc (fun c => phz d f s₁ z (w₁ * (cM c * (L.j h * x)))), hκ,
      integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul, ← mul_assoc]
    congr 1
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  rw [hK, hK]
  simp_rw [key, mul_assoc (Complex.exp _), integral_const_mul]
  rw [tsum_mul_left]; ring


variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} in
theorem lhs_eq_tsum {d : SD σ} (L : LD d) (f : d.G → ℂ) (s₁ z : ℂ) (nb : nA σ d.Y d.b → d.G) (lam : Measure (nA σ d.Y d.b))
    (𝓖 : Set (nA σ d.Y d.b)) (T : nF σ d.Y d.b) (uM : (Fin L.n → AE F E) → d.G) (ν : Measure (Fin L.n → AE F E))
    (𝓤 : Set (Fin L.n → AE F E)) (hν : ν 𝓤 = 1) (hlam : lam 𝓖 = 1) (x : d.G)
    (hi : ∀ q : Cs d, Integrable (kq L f s₁ z nb T uM (rep q) x) ((ν.restrict 𝓤).prod (lam.restrict 𝓖)))
    (hs : Summable fun q : Cs d => ∫ p, ‖kq L f s₁ z nb T uM (rep q) x p‖ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖))) :
    Summable (fun q : Cs d => tm L f s₁ z nb lam 𝓖 T uM ν 𝓤 (rep q) x) ∧
      ∫ u in 𝓤, fc d.B.ψ d.b nb lam 𝓖 (d.eis f s₁ z) T (uM u * x) ∂ν = ∑' q : Cs d, tm L f s₁ z nb lam 𝓖 T uM ν 𝓤 (rep q) x := by
  have : Countable (rat2 σ d.Y) := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ d.Y
  have : Countable (Cs d) := Quotient.countable
  have : IsFiniteMeasure (ν.restrict 𝓤) := isFiniteMeasure_restrict.2 (by simp [hν])
  have : IsFiniteMeasure (lam.restrict 𝓖) := isFiniteMeasure_restrict.2 (by simp [hlam])
  obtain ⟨h1, h2⟩ := exch (fun q : Cs d => kq L f s₁ z nb T uM (rep q) x) hi hs
  have htm : ∀ q : Cs d, tm L f s₁ z nb lam 𝓖 T uM ν 𝓤 (rep q) x =
      ∫ u, ∫ v, kq L f s₁ z nb T uM (rep q) x (u, v) ∂(lam.restrict 𝓖) ∂(ν.restrict 𝓤) := fun q => rfl
  simp_rw [htm]
  refine ⟨h1, ?_⟩
  rw [← h2]
  refine integral_congr_ae (ae_of_all _ fun u => integral_congr_ae (ae_of_all _ fun β => ?_))
  simp only [SD.eis, GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term, kq, phz, rep]
  rw [tsum_mul_right]
  rfl

theorem ctSplit_of_parts : IndepDom → CptDom → AbsConv → FirstEq → SecLaw → CTSplit := by
  intro hI hC hA hF hS F E _ _ _ _ _ σ d R L s₁ f hf he
  obtain ⟨tA, hA'⟩ := hA F E σ d L s₁ f hf he
  obtain ⟨tF, hF'⟩ := hF F E σ d L s₁ f hf he
  obtain ⟨tS, hS'⟩ := hS F E σ d R L s₁ f hf he
  refine ⟨max tA (max tF tS), fun z hz nb lam 𝓖 hc nb' lam' 𝓖' hc' uM ν 𝓤 hU T T' hTT' => ?_⟩
  have hzA : tA < z.re := lt_of_le_of_lt (le_max_left _ _) hz
  have hzF : tF < z.re := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hz
  have hzS : tS < z.re := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hz
  obtain ⟨𝓖₀, hc₀, hk₀⟩ := (hC F E σ d).1 nb lam 𝓖 hc
  obtain ⟨𝓤₀, hU₀, hkU⟩ := (hC F E σ d).2 L uM ν 𝓤 hU
  obtain ⟨𝓖'₀, hc'₀, hk'₀⟩ := (hC F E σ L.sd).1 nb' lam' 𝓖' hc'
  refine ⟨sec2 L f s₁ z nb lam 𝓖₀ T uM ν 𝓤₀, fun x => ?_, fun w τ y x hy =>
    hS' z hzS nb lam 𝓖₀ hc₀ hk₀ uM ν 𝓤₀ hU₀ hkU T T' hTT' nb' lam' 𝓖'₀ hc'₀ hk'₀ w τ y x hy⟩
  have e1 := (hI F E σ d L s₁ f hf z).1 nb lam 𝓖 𝓖₀ hc hc₀ uM ν 𝓤 𝓤₀ hU hU₀ T T' hTT' x
  have e2 := (hI F E σ d L s₁ f hf z).2 nb' lam' 𝓖' 𝓖'₀ hc' hc'₀ T' x
  have e3 := hF' z hzF nb lam 𝓖₀ hc₀ hk₀ nb' lam' 𝓖'₀ hc'₀ hk'₀ uM ν 𝓤₀ hU₀ hkU T T' hTT' x
  obtain ⟨hi, hs⟩ := hA' z hzA nb lam 𝓖₀ hc₀ hk₀ uM ν 𝓤₀ hU₀ hkU T x
  obtain ⟨hsum, e4⟩ := lhs_eq_tsum L f s₁ z nb lam 𝓖₀ T uM ν 𝓤₀ hU₀.2.2.2 hc₀.2.2.2 x hi hs
  change _ = first L f s₁ z nb' lam' 𝓖' T' x + _
  rw [e1, e2, ← e3, e4, ← hsum.tsum_subtype_add_tsum_subtype_compl {q : Cs d | LagrangianCondition L (rep q)}]
  rfl

end PositivityTheory.SiegelWeilFormula.Act

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act.C5

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} (R : RD d) (L : LD d)

structure Hyp (nb : nA σ d.Y d.b → d.G) (uM : (Fin L.n → AE F E) → d.G) (nb' : nA σ L.Y L.b → G2 σ L.Y) (w₁ : d.G)
    (cM : (Fin L.n → AE F E) × AF F → d.G) (δ : E) : Prop where
  nb : IsNMap d.b nb
  uM : ∀ u, ∃ a', inFrame d.b (uM u) = Matrix.fromBlocks (uA L u) 0 0 a'
  nb' : IsNMap L.b nb'
  wr : w₁ ∈ rat2 σ d.Y
  wf : ∃ a b : E, a ≠ 0 ∧ b ≠ 0 ∧ inFrame d.b w₁ = 1 - Matrix.single (Sum.inl L.i₀) (Sum.inl L.i₀) 1 -
      Matrix.single (Sum.inr L.i₀) (Sum.inr L.i₀) 1 + Matrix.single (Sum.inl L.i₀) (Sum.inr L.i₀) (inclR (F := F) (AF F) a) +
      Matrix.single (Sum.inr L.i₀) (Sum.inl L.i₀) (inclR (F := F) (AF F) b)
  cf : ∀ c, ∃ A', inFrame d.b (cM c) = Matrix.fromBlocks (uA L c.1) (aB L δ c.2) 0 A'
  δ0 : δ ≠ 0

def sM (b : Fin L.n → AE F E) : d.G := elt (bMat (sB R L b))

def pb (β : nA σ d.Y d.b) : Fin L.n → AE F E := fun j => β.1 L.i₀ (L.em j)

def ellA (δ : E) : AE F E →ₗ[AF F] AF F :=
  (Algebra.TensorProduct.rid F (AF F) (AF F)).toLinearMap ∘ₗ
    LinearMap.baseChange (AF F) (Classical.epsilon fun ℓ : E →ₗ[F] F => δ ≠ 0 → ℓ δ = 1)

def pa (δ : E) (β : nA σ d.Y d.b) : AF F := ellA δ (β.1 L.i₀ L.i₀)

def E2 (Φ : d.G → ℂ) (g : d.G) : ℂ := ∑' q : {q : Cs d // ¬ LagrangianCondition L (rep q)}, Φ (rep q.1 * g)

end PositivityTheory.SiegelWeilFormula.Act.C5

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem phz_leftInv (d : SD σ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) :
    GlobalTheory.AutomorphicL2Unitary.LeftInv (par2 σ d.Y ⊓ rat2 σ d.Y) (phz d f s₁ z) := by
  intro p hp g
  obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 hp.1
  obtain ⟨T, hT⟩ := par_rat ht hp.2
  obtain ⟨u, hu⟩ := det_rat hT
  have ha : d.a (p * g) = d.a g := by
    rw [IsHgt.mul d.ok.hgt ht, hu, GlobalTheory.Doubling.absE_inclR]; simp
  have hfp : f (p * g) = f g := Law.rat (z := s₁ + (d.n : ℂ) / 2) hf.law d.ok.hecke hp.1 hp.2 g
  simp only [phz, SD.Ht, ha, hfp]

theorem eis_leftInv (d : SD σ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) :
    ∀ γ ∈ rat2 σ d.Y, ∀ g, d.eis f s₁ z (γ * g) = d.eis f s₁ z g :=
  GlobalTheory.Eis.leftInv_cosetSum (phz_leftInv d hf z)

theorem fc_dom (d : SD σ) {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 𝓖₀ : Set (nA σ d.Y d.b)}
    (h : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (h₀ : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖₀)
    (φ : d.G → ℂ) (hφ : ∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g) (T : nF σ d.Y d.b) (g : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 φ T g = fc d.B.ψ d.b nb lam 𝓖₀ φ T g := by
  unfold fc
  have := h.2.1
  have : VAddInvariantMeasure (nF σ d.Y d.b) (nA σ d.Y d.b) lam := ⟨fun c s _ => measure_preimage_add lam c.1 s⟩
  refine h.2.2.1.setIntegral_eq h₀.2.2.1 fun β₀ β => ?_
  have e1 : (β₀ +ᵥ β : nA σ d.Y d.b) = β₀.1 + β := rfl
  have e2 : ((β₀.1 + β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = β₀.1.1 + β.1 := rfl
  rw [e1, kunf.nb_add h.1, mul_assoc, hφ _ (kunf.nb_rat h.1 β₀.2), e2, Matrix.mul_add, Matrix.trace_add, map_add (f := _), neg_add,
    AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, kunf.psi_rat d.ok.good.std T β₀, inv_one, one_mul]

end PositivityTheory.SiegelWeilFormula.Act.C1

end
end
