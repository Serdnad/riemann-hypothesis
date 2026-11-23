module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle214
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle225
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle231
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle234
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexifiedDerivedActionIsLieAction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle235
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle236
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008

@[expose] public section

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

theorem GlobalTheory.FlagBundle.eq_of_coBear : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ (K : Type) [Field K] (p p' : Sp K ⟶ Y₁.X) (q : Sp K ⟶ Y₂.X), p ≫ f₁ = q ≫ f₂ → p' ≫ f₁ = q ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p q → CoBear Eb S₁ φ₁ S₂ φ₂ (p' ≫ f₁) p' q → p = p' := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ K _ p p' q hp hp' hc hc'
  obtain ⟨A, hA, h, hh, hAp, hAq⟩ := hc
  obtain ⟨B, hB, h', -, hBp', hBq⟩ := hc'
  have hA' : A ∈ Eb.S ((q ≫ f₂) (IsLocalRing.closedPoint K)) := hp ▸ hA
  have hB' : B ∈ Eb.S ((q ≫ f₂) (IsLocalRing.closedPoint K)) := hp' ▸ hB
  have hAp' : Bears S₁ φ₁ A h p' :=
    GlobalTheory.T.pointCarriesFrameFlags_transfer_between_flag_bundles F ι m X Y₂ Y₁ Eb S₂ φ₂ f₂ S₁ φ₁ f₁ hR₂ hR₁ K q p' hp'.symm A hA' B hB' h h' hAq hBq hBp'
  exact (hR₁.2.2 K (p ≫ f₁) A hA h hh).unique ⟨rfl, hAp⟩ ⟨hp'.trans hp.symm, hAp'⟩
end

section

open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology


theorem _root_.GlobalTheory.T.isNegHermitianSquare_curvature_of_holomorphic_frameChange : ∀ {n m r : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n) (W : V n → Matrix (Fin m) (Fin m) ℂ)
    (Z : V n → (Fin m → Fin r → ℂ)) (κ : ℝ), 0 < κ →
    (∀ᶠ u in 𝓝 v, G u = (κ : ℂ) • ((W u)ᵀ * domGram m r (Z u) * (W u)ᴴᵀ)) →
    (∀ᶠ u in 𝓝 v, DifferentiableAt ℂ Z u) → (∀ i j, ∀ᶠ u in 𝓝 v, DifferentiableAt ℂ (fun u => W u i j) u) →
    IsUnit (W v).det → (1 - Matrix.of (Z v) * (Matrix.of (Z v))ᴴ).PosDef →
    IsNegSq (curv (domGram m r) (Z v)) r → IsNegSq (curv G v) r := by
  first | exact @GlobalTheory.PointFormSign.isNegSq_curv_of_changeFrame_comp | exact GlobalTheory.PointFormSign.isNegSq_curv_of_changeFrame_comp | (intros; apply GlobalTheory.PointFormSign.isNegSq_curv_of_changeFrame_comp <;> assumption)
end

section

open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology


theorem _root_.GlobalTheory.T.chernFormPolyCoeff_top_of_neg_hermitianSquare : ∀ {n m r : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n) (S : Matrix (Fin m) (Fin m) ℂ)
    (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ), IsUnit S.det →
    (∀ ξ η, curv G v ξ η = S⁻¹ * (-(T ξ * (T η)ᴴ)) * S) → chernPoly G v m = (-1) ^ m * (sqPoly T).det := by
  first | exact @GlobalTheory.PointFormSign.chernPoly_top_of_negSq | exact GlobalTheory.PointFormSign.chernPoly_top_of_negSq | (intros; apply GlobalTheory.PointFormSign.chernPoly_top_of_negSq <;> assumption)
end

section

open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology


theorem _root_.GlobalTheory.T.isNegHermitianSquare_curvature_boundedDomainHodgeGram : ∀ (m r : ℕ) (x : Fin m → Fin r → ℂ), (1 - Matrix.of x * (Matrix.of x)ᴴ).PosDef →
    IsNegSq (curv (domGram m r) x) r := by
  first | exact @GlobalTheory.PointFormSign.curv_domGram_isNegSq | exact GlobalTheory.PointFormSign.curv_domGram_isNegSq | (intros; apply GlobalTheory.PointFormSign.curv_domGram_isNegSq <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.ModelFn

open SmallSec

theorem ratVal_eq {Z : Scheme.{0}} [IsIntegral Z] {k : Type} [CommRing k] {q : Z ⟶ Sp k} {σ : k →+* ℂ}
    (y : CxPts q σ) (f : Z.functionField) : ratVal f y = valAt y.1 f := by
  by_cases hf : RegAt (under y) f
  · exact ratVal_eq_valAt y hf
  · rw [ratVal, valAt, dite_eq_right hf, dite_eq_right hf]

theorem valAt_comp {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (j : Y ⟶ X) [IsPreimmersion j]
    (hη : j (genericPoint Y) ⤳ genericPoint X) {K : Type} [Field K] (y : Sp K ⟶ Y) (f : X.functionField) :
    valAt (y ≫ j) f = valAt y (fnMap j hη f) := by
  by_cases hf : RegAt (j (below y)) f
  · exact (valAt_fnMap j hη y hf).symm
  · have h₁ : ¬ RegAt (below (y ≫ j)) f := hf
    rw [valAt, valAt, dite_eq_right h₁, dite_eq_right (mt (regAt_fnMap_iff j hη).1 hf)]

end GlobalTheory.TrueGeo.ModelFn
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.derived_action_smooth_vector_real_linear : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ w ∈ smSub G (trRep σ P), (∀ X ∈ lieG G, ∀ Y ∈ lieG G, dRep (trRep σ P) (X + Y) w = dRep (trRep σ P) X w + dRep (trRep σ P) Y w) ∧ ∀ (a : ℝ), ∀ X ∈ lieG G, dRep (trRep σ P) (a • X) w = (a : ℂ) • dRep (trRep σ P) X w := by
  first | exact @GlobalTheory.SmVecLinear.dRep_linear | exact GlobalTheory.SmVecLinear.dRep_linear | (intros; apply GlobalTheory.SmVecLinear.dRep_linear <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.equivariant_map_carries_gelfandInvariant_to_function : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), IsInfFam θ → ∀ T : MMap M, IsMultMap θ M J χ T → ∀ [DecidableEq D.what₂.Tau] (τ : D.what₂.Tau) (k : ℕ) (v : M.Vec) (w : M.sm τ), (w : M.H τ) = gelfH (gramAt D V τ) (M.rep τ) k (v τ) → gelf θ V τ k (T v) = T (Function.update v τ w) := by
  first | exact @GlobalTheory.MultGelf.gelf_apply | exact GlobalTheory.MultGelf.gelf_apply | (intros; apply GlobalTheory.MultGelf.gelf_apply <;> assumption)
end

section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

theorem isHermitian_Jm_bracket {n : ℕ} (ε : Fin n → Bool) : (Jm ε).IsHermitian := by
  unfold Jm
  refine Matrix.isHermitian_diagonal_of_self_adjoint _ ?_
  funext i
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem dRep_bracket : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ w, Sm ε σ w → ∀ X ∈ lieSet ε, ∀ Y ∈ lieSet ε, dRep σ X (dRep σ Y w) - dRep σ Y (dRep σ X w) = dRep σ (X * Y - Y * X) w := by
  intro n ε H _ _ _ σ h w hw X hX Y hY
  have hd : (Jm ε).det ≠ 0 := ((isUnit_iff_isUnit_det _).1 (isUnit_Jm ε)).ne_zero
  have key := fun v (hv : Sm ε σ v) =>
    GlobalTheory.HolDict.LieAct.main n (Jm ε) H σ (isHermitian_Jm_bracket ε) hd h.1 v v hv hv
  have hB : X * Y - Y * X ∈ lieSet ε := by
    have h1 : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left hX
    have h2 : Yᴴ * Jm ε = -(Jm ε * Y) := eq_neg_of_add_eq_zero_left hY
    show (X * Y - Y * X)ᴴ * Jm ε + Jm ε * (X * Y - Y * X) = 0
    rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, sub_mul, mul_assoc, mul_assoc, h1, h2,
      mul_neg, mul_neg, ← mul_assoc, ← mul_assoc, h1, h2]
    noncomm_ring
  have hXw : Sm ε σ (dRep σ X w) := dRep_mem (isUnit_Jm ε) h.1 hw hX
  have hYw : Sm ε σ (dRep σ Y w) := dRep_mem (isUnit_Jm ε) h.1 hw hY
  have e := ((key w hw).1 0 X Y).2.2
  rw [(key w hw).2.1 _ hB, (key w hw).2.1 X hX, (key w hw).2.1 Y hY, (key _ hXw).2.1 Y hY,
    (key _ hYw).2.1 X hX] at e
  exact e.symm

end GlobalTheory.TypeSum
end

section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.SobHS

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem exists_orthonormal_expansion {ι : Type} [Fintype ι] (f : ι → H) :
    ∃ (m : ℕ) (h : Fin m → H) (φ : ι → Fin m → ℂ), Orthonormal ℂ h ∧ (∀ j, f j = ∑ p, φ j p • h p) ∧
      ∀ j, ∑ p, ‖φ j p‖ ^ 2 = ‖f j‖ ^ 2 := by
  let U : Submodule ℂ H := Submodule.span ℂ (Set.range f)
  haveI : FiniteDimensional ℂ U := FiniteDimensional.span_of_finite ℂ (Set.finite_range f)
  let b := stdOrthonormalBasis ℂ U
  let u : ι → U := fun j => ⟨f j, Submodule.subset_span ⟨j, rfl⟩⟩
  refine ⟨_, fun p => (b p : H), fun j p => ⟪b p, u j⟫_ℂ, b.orthonormal.comp_linearIsometry U.subtypeₗᵢ,
    fun j => ?_, fun j => b.sum_sq_norm_inner_right (u j)⟩
  have := congrArg Subtype.val (b.sum_repr' (u j))
  simpa using this.symm

theorem integral_sq_sum {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)} {μ : Measure (UJ ε)} {d : ℝ}
    (hd : IsFdeg μ σ d) {m : ℕ} {h : Fin m → H} (hh : Orthonormal ℂ h) (y : Fin m → H) :
    Integrable (fun g : UJ ε => ‖∑ p, ⟪h p, σ (umat g) (y p)⟫_ℂ‖ ^ 2) μ ∧
      ∫ g : UJ ε, ‖∑ p, ⟪h p, σ (umat g) (y p)⟫_ℂ‖ ^ 2 ∂μ = (∑ p, ‖y p‖ ^ 2) / d := by
  have e : ∀ g : UJ ε, ((‖∑ p, ⟪h p, σ (umat g) (y p)⟫_ℂ‖ ^ 2 : ℝ) : ℂ) =
      ∑ p, ∑ q, coefOn σ (y p) (h p) g * star (coefOn σ (y q) (h q) g) := by
    intro g
    rw [← Finset.sum_mul_sum, ← star_sum, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rfl
  have i1 : ∀ p, Integrable (fun g : UJ ε => ∑ q, coefOn σ (y p) (h p) g * star (coefOn σ (y q) (h q) g)) μ :=
    fun p => integrable_finsetSum _ fun q _ => (hd.2 _ _ _ _).1
  have i2 : Integrable (fun g : UJ ε => ((‖∑ p, ⟪h p, σ (umat g) (y p)⟫_ℂ‖ ^ 2 : ℝ) : ℂ)) μ := by
    simp only [e]
    exact integrable_finsetSum _ fun p _ => i1 p
  refine ⟨by simpa only [RCLike.re_to_complex, Complex.ofReal_re] using i2.re, ?_⟩
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp only [e]
  rw [integral_finsetSum _ fun p _ => i1 p]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_finsetSum _ fun q _ => (hd.2 _ _ _ _).1]
  simp only [(hd.2 _ _ _ _).2, orthonormal_iff_ite.1 hh]
  rw [Finset.sum_eq_single p (fun q _ hq => by simp [Ne.symm hq]) (by simp)]
  simp [inner_self_eq_norm_sq_to_K]

theorem sobolev_hilbertSchmidt : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧ ∀ (ι : Type) [Fintype ι] (f x : ι → H) (A : ℝ), 0 ≤ A → (∀ j, Sm ε σ (x j)) → (∀ l ∈ S, ∀ z : ι → ℂ, ‖∑ j, z j • Dw σ l (x j)‖ ^ 2 ≤ A * ∑ j, ‖z j‖ ^ 2) → ‖∑ j, ⟪f j, x j⟫_ℂ‖ ^ 2 ≤ C * A * ∑ j, ‖f j‖ ^ 2 := by
  intro n ε H _ _ _ σ hσ
  obtain ⟨S, C, hS, hC, H1⟩ := GlobalTheory.T.sobolev_inequality_at_one_indefiniteUnitary n ε
  obtain ⟨d, hd⟩ := hσ.2.2.2.1
  have hd0 := hd.1
  refine ⟨S, C * S.length / d, hS, by positivity, fun ι _ f x A hA hx hb => ?_⟩
  obtain ⟨m, h, φ, hh, hf, hφ⟩ := exists_orthonormal_expansion f
  let F : List (Mx n) → Mx n → ℂ := fun l g => ∑ j, ⟪f j, σ g (Dw σ l (x j))⟫_ℂ
  have eF : ∀ l g, F l g = ∑ p, ⟪h p, σ g (∑ j, (starRingEnd ℂ) (φ j p) • Dw σ l (x j))⟫_ℂ := by
    intro l g

    simp only [F, map_sum, map_smul, inner_sum, inner_smul_right]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hf j, sum_inner]
    simp only [inner_smul_left]
  have hI := fun l => integral_sq_sum hd hh fun p => ∑ j, (starRingEnd ℂ) (φ j p) • Dw σ l (x j)
  simp only [← eF] at hI
  have key := H1 F (fun l _ => continuousOn_finsetSum _ fun j _ =>
      (innerSL ℂ (f j)).continuous.comp_continuousOn (hσ.1.2.2 _)) ?_ fun l _ => (hI l).1
  · have e1 : F [] 1 = ∑ j, ⟪f j, x j⟫_ℂ := by simp only [F, sigma_one hσ.1]; rfl
    rw [e1] at key
    refine key.trans ?_
    have h2 : (S.map fun l => ∫ g : UJ ε, ‖F l (umat g)‖ ^ 2 ∂(muG ε)).sum ≤
        (S.map fun l => ∫ g : UJ ε, ‖F l (umat g)‖ ^ 2 ∂(muG ε)).length • ((A * ∑ j, ‖f j‖ ^ 2) / d) := by
      refine List.sum_le_card_nsmul _ _ fun r hr => ?_
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hr
      rw [(hI l).2]
      refine div_le_div_of_nonneg_right ?_ hd0.le
      refine (Finset.sum_le_sum fun p _ => hb l hl _).trans (le_of_eq ?_)
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [RCLike.norm_conj, hφ]
    rw [List.length_map, nsmul_eq_mul] at h2
    refine (mul_le_mul_of_nonneg_left h2 hC).trans (le_of_eq ?_)
    ring
  · intro l hl X hX g hg
    have e : ∀ t : ℝ, F l (g * NormedSpace.exp (t • X)) =
        ∑ j, ⟪f j, σ g (σ (NormedSpace.exp (t • X)) (Dw σ l (x j)))⟫_ℂ := fun t => by
      simp only [F, sigma_mul hσ.1 hg (exp_mem_UJ hX t)]
    simp only [e]
    refine HasDerivAt.fun_sum fun j _ => ?_
    have h1 := hasDerivAt_orbit hσ.1 ((hx j).word hσ.1 hl) hX 0
    rw [zero_smul, NormedSpace.exp_zero, sigma_one hσ.1] at h1
    exact (((innerSL ℂ (f j)).comp (σ g)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h1

end GlobalTheory.TypeSum.SobHS
end

section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

theorem _root_.GlobalTheory.T.charpolyRev_neg_finSumBlockDiagonalMatrix : ∀ {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R) (b : Matrix (Fin N) (Fin N) R), Matrix.charpolyRev (-(blockSum a b)) = Matrix.charpolyRev (-a) * Matrix.charpolyRev (-b) := by
  first | exact @GlobalTheory.GoodMetric.ChernSpan.charpolyRev_neg_blockSum | exact GlobalTheory.GoodMetric.ChernSpan.charpolyRev_neg_blockSum | (intros; apply GlobalTheory.GoodMetric.ChernSpan.charpolyRev_neg_blockSum <;> assumption)
end

section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

theorem _root_.GlobalTheory.T.polynomialMatrixFamilyRep_lie_directSum : ∀ {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ σ : PolyRep m) {R : Type} [CommRing R] (A : Mat m R), (ρ.sum σ).lie A = blockSum (ρ.lie A) (σ.lie A) := by
  first | exact @GlobalTheory.GoodMetric.PolyRep.lie_sum | exact GlobalTheory.GoodMetric.PolyRep.lie_sum | (intros; apply GlobalTheory.GoodMetric.PolyRep.lie_sum <;> assumption)
end

section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

theorem _root_.GlobalTheory.T.trace_pow_finProdKronecker_add_binomial : ∀ {R : Type} [CommRing R] {M N : ℕ} (L : Matrix (Fin M) (Fin M) R) (L' : Matrix (Fin N) (Fin N) R) (i : ℕ), ((kron L 1 + kron 1 L') ^ i).trace = ∑ a ∈ Finset.range (i + 1), (i.choose a : R) * (L ^ a).trace * (L' ^ (i - a)).trace := by
  first | exact @GlobalTheory.GoodMetric.ChernSpan.trace_pow_kron_add | exact GlobalTheory.GoodMetric.ChernSpan.trace_pow_kron_add | (intros; apply GlobalTheory.GoodMetric.ChernSpan.trace_pow_kron_add <;> assumption)
end
