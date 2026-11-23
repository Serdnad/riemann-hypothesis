module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle185
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle029
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle040
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle098
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle024
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle033
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableCsmul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle026
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle177
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NegMulCCancel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Meas

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def glueMapI (i : Fin (r + 1)) (c : Fin r → ℂ) (q : Cf r i × Mt k r) : (Fin r → ℂ) × Mx k r :=
  (glue i c q.1, Matrix.of q.2)

theorem glueMapI_continuous (i : Fin (r + 1)) (c : Fin r → ℂ) : Continuous (glueMapI (k := k) i c) := by
  refine Continuous.prodMk ?_ continuous_snd
  refine continuous_pi fun l => ?_
  by_cases h : i.val ≤ l.val
  · have e : (fun q : Cf r i × Mt k r => glue i c q.1 l) = fun q => q.1 ⟨l, h⟩ := by
      funext q; simp [glue, h]
    rw [e]; exact (continuous_apply _).comp continuous_fst
  · have e : (fun q : Cf r i × Mt k r => glue i c q.1 l) = fun _ => c l := by
      funext q; simp [glue, h]
    rw [e]; exact continuous_const

theorem measurableSet_glueMapI_DomR (i : Fin (r + 1)) (c : Fin r → ℂ) :
    MeasurableSet (glueMapI (k := k) i c ⁻¹' DomR k r z z') := by
  rw [DomR_eq, Set.preimage_inter]
  exact ((Formalism.FourierDecayAlt.P.Qx5.isOpen_OpR k r z z').preimage (glueMapI_continuous i c)).measurableSet.inter
    (((Formalism.FourierDecayAlt.P.Qx5.Glev_closed (Fin.last r)).preimage continuous_snd).preimage
      (glueMapI_continuous i c)).measurableSet

theorem pair_measurableI (i : Fin (r + 1)) (c : Fin r → ℂ) (Φ Ψ : RadSp k r z z' π π') :
    Measurable (fun q : Cf r i × Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue i c q.1) (Matrix.of q.2))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (glue i c q.1) (Matrix.of q.2))) := by
  have hmaps : Set.MapsTo (glueMapI (k := k) i c) (glueMapI (k := k) i c ⁻¹' DomR k r z z') (DomR k r z z') :=
    fun q hq => hq
  have hΦc := (radSp_continuousOn Φ).comp (glueMapI_continuous i c).continuousOn hmaps
  have hΨc := (radSp_continuousOn Ψ).comp (glueMapI_continuous i c).continuousOn hmaps
  refine measurable_of_continuousOn_zero (measurableSet_glueMapI_DomR i c)
    ((Formalism.FourierDecayAlt.P.B6.hsInner_continuous (Wp := Wp) (Wq := Wq)).comp_continuousOn (hΦc.prodMk hΨc)) ?_
  intro q hq
  have h0 : (Φ : Fn k r (Wq →L[ℂ] Wp)) (glue i c q.1) (Matrix.of q.2) = 0 := radSp_zero_off Φ hq
  show B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue i c q.1) (Matrix.of q.2)) _ = 0
  rw [h0, Formalism.FourierDecayAlt.P.B6.hilbert_schmidt_inner_basis_sum]
  simp

theorem pairAt_measI (μ : Measure (Mt k r)) [SFinite μ] (i : Fin (r + 1)) (u v : RadSp k r z z' π π')
    (c : Fin r → ℂ) : StronglyMeasurable (fun c' : Cf r i => pairAt μ u v (glue i c c')) :=
  (pair_measurableI i c u v).stronglyMeasurable.integral_prod_right'

def wtI (i : Fin (r + 1)) (c' : Cf r i) : ℂ := ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ)

theorem wtI_measurable (i : Fin (r + 1)) : Measurable (wtI i) := by
  unfold wtI
  have e : ∀ x : ℝ, x ^ (-2 : ℤ) = (x ^ 2)⁻¹ := fun x => by rw [zpow_neg]; norm_cast
  simp_rw [e]
  exact Complex.measurable_ofReal.comp
    (Finset.measurable_prod _ fun l _ => ((measurable_norm.comp (measurable_pi_apply l)).pow_const 2).inv)

def LevelSquareIntegrable (μ : Measure (Mt k r)) (i : Fin (r + 1)) (u : RadSp k r z z' π π') (c : Fin r → ℂ) : Prop :=
  Integrable (fun c' : Cf r i => wtI i c' * pairAt μ u u (glue i c c'))

theorem hsInner_self_ofRealI (A : Wq →L[ℂ] Wp) : B.hsInner A A = ((‖B.hsVec A‖ ^ 2 : ℝ) : ℂ) := by
  unfold B.hsInner
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (B.hsVec A)]
  push_cast
  rfl

theorem norm_pairAt_selfI (μ : Measure (Mt k r)) (u : RadSp k r z z' π π') (c : Fin r → ℂ) :
    ‖pairAt μ u u c‖ = ∫ g : Mt k r, ‖B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))‖ ∂μ := by
  unfold pairAt
  simp_rw [hsInner_self_ofRealI]
  rw [integral_complex_ofReal, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun g => by positivity)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]

theorem norm_pairAt_leI (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    {u v : RadSp k r z z' π π'} (hu : u ∈ lcSub k r z z' π π') (hv : v ∈ lcSub k r z z' π π') (c : Fin r → ℂ) :
    ‖pairAt μ u v c‖ ≤ ‖pairAt μ u u c‖ + ‖pairAt μ v v c‖ := by
  rw [norm_pairAt_selfI, norm_pairAt_selfI]
  unfold pairAt
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_add (int_lc μ hμ hu hu c).norm (int_lc μ hμ hv hv c).norm]
  exact integral_mono (int_lc μ hμ hu hv c).norm ((int_lc μ hμ hu hu c).norm.add (int_lc μ hμ hv hv c).norm)
    fun g => norm_hs_le _ _

theorem int_crossI (μ : Measure (Mt k r)) [SFinite μ] (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (i : Fin (r + 1))
    {u v : RadSp k r z z' π π'} (hu : u ∈ lcSub k r z z' π π') (hv : v ∈ lcSub k r z z' π π') (c : Fin r → ℂ)
    (Iu : LevelSquareIntegrable μ i u c) (Iv : LevelSquareIntegrable μ i v c) :
    Integrable (fun c' : Cf r i => wtI i c' * pairAt μ u v (glue i c c')) := by
  refine (Iu.norm.add Iv.norm).mono'
    ((wtI_measurable i).aestronglyMeasurable.mul (pairAt_measI μ i u v c).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun c' => ?_)
  show ‖wtI i c' * pairAt μ u v (glue i c c')‖ ≤
    ‖wtI i c' * pairAt μ u u (glue i c c')‖ + ‖wtI i c' * pairAt μ v v (glue i c c')‖
  rw [norm_mul, norm_mul, norm_mul, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_pairAt_leI μ hμ hu hv _) (norm_nonneg _)

end Meas

section Red

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem formIntOuter_of_l2I {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : Measure (Mt k r)) [SFinite μ]
    (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (i : Fin (r + 1)) (u v : Ix S → RadSp k r z z' π π')
    (hu : ∀ a, u a ∈ lcSub k r z z' π π') (hv : ∀ a, v a ∈ lcSub k r z z' π π') (c : Fin r → ℂ)
    (Iu : ∀ a, LevelSquareIntegrable μ i (u a) c) (Iv : ∀ a, LevelSquareIntegrable μ i (v a) c) :
    Integrable (fun c' : Cf r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ a, pairAt μ (u a) (v a) (glue i c c')) := by
  simp_rw [Finset.mul_sum]
  exact integrable_finsetSum _ fun a _ => int_crossI μ hμ i (hu a) (hv a) c (Iu a) (Iv a)

def HermitianSquareIntegrableAt (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (i : Fin (P.r + 1)) : Prop :=
  ∀ c ∈ OmX P.r, (∀ u ∈ herKc S P z z' π π' L st l0 D i, LevelSquareIntegrable μ i u c) ∧
    ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ x : Ix S → RadSp P.k P.r z z' π π',
      InK (herKc S P z z' π π' L st l0 D i) x → ∀ a, LevelSquareIntegrable μ i (act (RRi L st i w) x a) c

def HermitianSquareIntegrableAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ i : Fin (P.r + 1), i.val < P.r → HermitianSquareIntegrableAt (S := S) P z z' π π' μ L st l0 D i

theorem outer_form_compact_of_square (h : HermitianSquareIntegrableAll) : FormIntOuterCpt := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' w hw i c hc x y hx hy
  by_cases hi : i.val < P.r
  · have : SFinite μ := sfinite_of_isHaarOn _ μ hD.2.1
    have hle := herKc_le_lc (S := S) (st := st) (l0 := l0) X hD.2.2.1
      (fun F Φ hF hΦ => jfCptLocAll Wp Wq P z z' π π' D F Φ hD.1 hz hz' hπ hπ' hF hΦ) i
    have hRR := RRi_lc X μ L st l0 hD i w hw.1.2.1
    have hu : ∀ a, act (RRi L st i w) x a ∈ lcSub P.k P.r z z' π π' := fun a =>
      (lcSub P.k P.r z z' π π').sum_mem fun b _ => (hRR a b).1 _ (hle (hx b))
    obtain ⟨hK, hR⟩ := h Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' i hi c hc
    exact formIntOuter_of_l2I μ hD.2.1 i _ y hu (fun a => hle (hy a)) c (hR w hw x hx) (fun a => hK _ (hy a))
  · have e : i = Fin.last P.r := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
    subst e
    exact integrable_cf_last _

end Red

end Formalism.FourierDecayAlt.P5.HerD
end
end

section

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section tools

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem stabilizer_mem_unipotent {z' : Fin (2 * r + k + 1) → ℂ} {n0 : B.Mat k r} (hn0 : n0 ∈ C3.N0set k r z') :
    n0 ∈ Formalism.QuantumDeterminants.Nset k r := by
  refine ⟨hn0.1, fun a i _ => ?_, fun i j h1 h2 h3 => hn0.2.2.2.1 i j h1 h2 h3⟩
  have h := congrFun (hn0.2.1 a) i
  rw [show (n0 *ᵥ bvec (eI k r a)) i = n0 i (eI k r a) by simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]] at h
  rw [h]
  simp [bvec, Pi.single_apply]

theorem character_stabilizer_eq_one {z' : Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z') (c : ℂ) {n0 : B.Mat k r}
    (hn0 : n0 ∈ C3.N0set k r z') : psi k r z' c n0 = 1 := by
  have hcol : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), n0 i (eI k r a) = if i = eI k r a then 1 else 0 := by
    intro a i
    have h := congrFun (hn0.2.1 a) i
    rw [show (n0 *ᵥ bvec (eI k r a)) i = n0 i (eI k r a) by simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]] at h
    rw [h]
    simp [bvec, Pi.single_apply]
  have hell : ell k r z' n0 = 0 := by
    unfold ell
    refine Finset.sum_eq_zero fun a _ => ?_
    split_ifs with h
    · rw [hcol]
      rw [if_neg]
      intro he
      have := congrArg Fin.val he
      simp [eI] at this
    · rw [hn0.2.2.1]
      exact hz' _ (Or.inl (by simp [eI]))
  unfold psi
  rw [hell, mul_zero]
  simp

theorem smoothOnH_of_ckOn {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : B.Mat k r → E}
    (hf : B.CkOn ⊤ (B.GV k r) f) : SmoothOnH (Hpk k r) f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hf g₀ hg₀
  exact ⟨U, f', hU, hgU, hf', fun g hg hgG => hfe g hg hgG⟩

theorem smoothLev_of_loc {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : B.Mat k r → E}
    (hf : ∀ x ∈ B.GV k r, Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc ⊤ f x) : Q.SmoothLev k r 0 Set.univ f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hf g₀ ((Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 g₀).1 hg₀.1)
  exact ⟨U, f', hU, hgU, hf', fun g hg hgl => hfe g hg ((Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 g).1 hgl)⟩

theorem kr_left (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (σ x : B.Mat k r) :
    PBG.Kr Bs (fun g => F (σ * g)) x = PBG.Kr Bs F (σ * x) := by
  unfold PBG.Kr
  congr 1
  funext p
  have e : σ * (x * Matrix.of p.2 * Matrix.of p.1) = σ * x * Matrix.of p.2 * Matrix.of p.1 := by
    simp only [Matrix.mul_assoc]
  show star (psi k r Bs.z' cStd (Matrix.of p.2)) • (F (σ * (x * Matrix.of p.2 * Matrix.of p.1))).comp
    (Bs.π' (Matrix.of p.1)⁻¹) = _
  rw [e]

theorem kr_congr (Bs : B.RealPlaceData k r Wp Wq) {F₁ F₂ : B.Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ B.GV k r, F₁ g = F₂ g) {x : B.Mat k r} (hx : x ∈ B.GV k r) : PBG.Kr Bs F₁ x = PBG.Kr Bs F₂ x := by
  unfold PBG.Kr
  refine integral_congr_ae ?_
  filter_upwards [PBG.ae_inR Bs] with ξ hξ
  rw [h _ (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hx hξ.2.1) hξ.1.1)]

theorem kr_dmin [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (H : B.Mat k r → (Wq →L[ℂ] Wp)) (l : Fin (r + 2)) (x : B.Mat k r) :
    PBG.Kr Bs (fun g => (Dmin k r Bs.z Bs.z' g l)⁻¹ • H g) x = (Dmin k r Bs.z Bs.z' x l)⁻¹ • PBG.Kr Bs H x := by
  unfold PBG.Kr
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [PBG.ae_inR Bs] with ξ hξ
  show star (psi k r Bs.z' cStd (Matrix.of ξ.2)) • ((Dmin k r Bs.z Bs.z' (x * Matrix.of ξ.2 * Matrix.of ξ.1) l)⁻¹ •
      H (x * Matrix.of ξ.2 * Matrix.of ξ.1)).comp (Bs.π' (Matrix.of ξ.1)⁻¹) =
    (Dmin k r Bs.z Bs.z' x l)⁻¹ • (star (psi k r Bs.z' cStd (Matrix.of ξ.2)) •
      (H (x * Matrix.of ξ.2 * Matrix.of ξ.1)).comp (Bs.π' (Matrix.of ξ.1)⁻¹))
  rw [PBG.dmin_pR Bs hξ x l, ContinuousLinearMap.smul_comp, smul_comm]

def pL (x : Mt k r × Mt k r) : B.SS k r := (x, (Matrix.of.symm 1, Matrix.of.symm 1))

theorem inSS_pL (Bs : B.RealPlaceData k r Wp Wq) {x : Mt k r × Mt k r}
    (hx : (Matrix.of x.1 : B.Mat k r) ∈ UWset k r Bs.z ∧ (Matrix.of x.2 : B.Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r) :
    Bs.inSS (pL x) := by
  refine ⟨hx.1, hx.2, ?_, ?_⟩
  · change Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ UWset k r Bs.z'
    rw [Equiv.apply_symm_apply]
    exact Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw (k := k) (r := r) Bs.z'
  · change Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ Formalism.QuantumDeterminants.Nset k r
    rw [Equiv.apply_symm_apply]
    exact Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_one

theorem sgs_pL (x : Mt k r × Mt k r) (g : B.Mat k r) :
    B.sgs (pL x) g = (Matrix.of x.1 : B.Mat k r)⁻¹ * (Matrix.of x.2 : B.Mat k r)⁻¹ * g := by
  simp only [B.sgs, pL, Prod.fst, Prod.snd, Equiv.apply_symm_apply, Matrix.mul_one]

theorem contDiff_lmul (σ : B.Mat k r) : ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat k r => σ * g) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun l _ => contDiff_const.mul ((contDiff_apply ℝ (fun _ => ℂ) j).comp (contDiff_apply ℝ _ l))

theorem cpt_left (Bs : B.RealPlaceData k r Wp Wq) {G : B.Mat k r → (Wq →L[ℂ] Wp)} (hG : KB.CptCoef Bs G)
    {x : Mt k r × Mt k r}
    (hx : (Matrix.of x.1 : B.Mat k r) ∈ UWset k r Bs.z ∧ (Matrix.of x.2 : B.Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r) :
    KB.CptCoef Bs (fun g => G ((Matrix.of x.1 : B.Mat k r)⁻¹ * (Matrix.of x.2 : B.Mat k r)⁻¹ * g)) := by
  set σ : B.Mat k r := (Matrix.of x.1 : B.Mat k r)⁻¹ * (Matrix.of x.2 : B.Mat k r)⁻¹ with hσ
  have hp := inSS_pL Bs hx
  have hmem : ∀ g ∈ B.GV k r, σ * g ∈ B.GV k r := fun g hg => by
    have := Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hg
    rwa [sgs_pL] at this
  have hgf : ∀ g, Gf k r Bs.z Bs.z' (σ * g) = Gf k r Bs.z Bs.z' g := fun g => by
    have := Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp g
    rwa [sgs_pL] at this
  obtain ⟨hs, ⟨R, hR⟩, ⟨ε, hε, hGf⟩⟩ := hG
  refine ⟨fun g₀ hg₀ => ?_, ⟨B.gN (Matrix.of x.2 : B.Mat k r) * B.gN (Matrix.of x.1 : B.Mat k r) * max R 0,
    fun g hg hne => ?_⟩, ⟨ε, hε, fun g hg hne => ?_⟩⟩
  · obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hs (σ * g₀) (hmem g₀ hg₀)
    have hc : Continuous (fun g : B.Mat k r => σ * g) := (contDiff_lmul σ).continuous
    refine ⟨(fun g => σ * g) ⁻¹' U, fun g => f' (σ * g), hU.preimage hc, hgU, ?_, fun g hg hgG => hfe _ hg (hmem g hgG)⟩
    exact hf'.comp (contDiff_lmul σ).contDiffOn (fun g hg => hg)
  · have h1 := hR _ (hmem g hg) hne
    have hu1 : IsUnit (Matrix.of x.1 : B.Mat k r).det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hx.1.1
    have hu2 : IsUnit (Matrix.of x.2 : B.Mat k r).det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hx.2.1
    have e : g = (Matrix.of x.2 : B.Mat k r) * (Matrix.of x.1 : B.Mat k r) * (σ * g) := by
      rw [hσ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc (Matrix.of x.2 : B.Mat k r),
        Matrix.mul_nonsing_inv _ hu1, Matrix.mul_one, Matrix.mul_nonsing_inv _ hu2, Matrix.one_mul]
    calc B.gN g = B.gN ((Matrix.of x.2 : B.Mat k r) * (Matrix.of x.1 : B.Mat k r) * (σ * g)) := by rw [← e]
      _ ≤ B.gN ((Matrix.of x.2 : B.Mat k r) * (Matrix.of x.1 : B.Mat k r)) * B.gN (σ * g) :=
          Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _
      _ ≤ (B.gN (Matrix.of x.2 : B.Mat k r) * B.gN (Matrix.of x.1 : B.Mat k r)) * max R 0 :=
          mul_le_mul (Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _) (h1.trans (le_max_left _ _)) (Formalism.FourierDecayAlt.P.B6.gN_nonneg _)
            (mul_nonneg (Formalism.FourierDecayAlt.P.B6.gN_nonneg _) (Formalism.FourierDecayAlt.P.B6.gN_nonneg _))
  · have := hGf _ (hmem g hg) hne
    rwa [hgf] at this

theorem loc_kr [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F) :
    ∀ x0 ∈ B.GV k r, Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc ⊤ (PBG.Kr Bs F) x0 := by
  obtain ⟨hs, ⟨R, hR⟩, -⟩ := hF
  refine PBG.kr_loc_cpt Bs hs (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k r R) fun g hg hgC => ?_
  by_contra hne
  exact hgC (hR g hg hne)

end tools

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
end
end

section

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PartialBesselProperness

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section defs

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def Proper (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n) (Cs : Set (B.Mat k n))
    (U : Set (B.Mat k n)) : Prop :=
  ∀ y ∈ U, ∃ V ∈ 𝓝 y, ∃ K : Set (PBQ.XP k p ρ), IsCompact K ∧ ∀ g ∈ V, g ∈ B.GV k n → ∀ x, PBQ.GoodP Bj x → x ∉ K →
    ∀ ξ, PBG.InR B0 ξ → D.castM e (PBQ.sP Bj x) * g * Matrix.of ξ.2 * Matrix.of ξ.1 ∉ Cs

end defs

def PbWords : Prop :=
  ∀ (k p ρ n : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n),
    B0.z = D.castV e (liftVec k p ρ Bj.z) →
    ∀ (i : ℕ) (hi : i ≤ n) (H : B.Mat k n → (Wq →L[ℂ] Wp)) (Cs : Set (B.Mat k n)),
    (∀ g ∈ B.GV k n, Dmin k n B0.z B0.z' g ⟨i, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc ⊤ H g) →
    IsCompact Cs → (∀ g ∈ B.GV k n, g ∉ Cs → H g = 0) →
    ∀ U : Set (B.Mat k n), IsOpen U → (∀ g ∈ U, Dmin k n B0.z B0.z' g ⟨i, by omega⟩ ≠ 0) →
    Proper Bj B0 e Cs U →
    ∀ (w : List C.Letter) (ew : Wd.Ix (Fin w.length)), ∀ y ∈ U, y ∈ B.GV k n →
      D.uwG k n B0.z B0.z' (PBQ.pbF Bj B0 e H) i hi w ew y =
        PBQ.pbF Bj B0 e (D.uwG k n B0.z B0.z' H i hi w ew) y

def PbLoc : Prop :=
  ∀ (k p ρ n : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n),
    B0.z = D.castV e (liftVec k p ρ Bj.z) →
    ∀ (H : B.Mat k n → (Wq →L[ℂ] Wp)) (Cs : Set (B.Mat k n)),
    B.CkOn ⊤ (B.GV k n) H → IsCompact Cs → (∀ g ∈ B.GV k n, g ∉ Cs → H g = 0) →
    ∀ U : Set (B.Mat k n), IsOpen U → Proper Bj B0 e Cs U →
    ∀ y ∈ U, y ∈ B.GV k n → CapelliWordSumExpansion.Loc ⊤ (PBQ.pbF Bj B0 e H) y

end Formalism.FourierDecayAlt.P.PartialBesselProperness
end
end
