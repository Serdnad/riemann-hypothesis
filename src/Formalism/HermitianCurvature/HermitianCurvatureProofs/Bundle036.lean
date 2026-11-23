module

public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle024
public import Formalism.HermitianCurvature.Bundle004
public import Formalism.HermitianCurvature.StatementD
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle032
public import Formalism.HermitianCurvature.StatementB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle029
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P

open PI.UpqRep

namespace TranslationBesselVanishing

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem uh_mul {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : hᴴ * Hpk k r * h = Hpk k r) (hg : gᴴ * Hpk k r * g = Hpk k r) :
    (h * g)ᴴ * Hpk k r * (h * g) = Hpk k r := by
  calc (h * g)ᴴ * Hpk k r * (h * g) = gᴴ * (hᴴ * Hpk k r * h) * g := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hh, hg]

theorem sigma_mul {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hds : IsDSHpk k r ε lam σ) {h g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : hᴴ * Hpk k r * h = Hpk k r) (hg : gᴴ * Hpk k r * g = Hpk k r) :
    σ (h * g) = (σ h).comp (σ g) := by
  obtain ⟨P, hP, hDS⟩ := hds
  have hmul := hDS.2.2.1.1.2
  have hPu : P ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := hP.2
  have hsP : star P * P = 1 := Matrix.mem_unitaryGroup_iff'.mp hPu
  have hPs : P * star P = 1 := Matrix.mem_unitaryGroup_iff.mp hPu
  have hinv : P⁻¹ = star P := Matrix.inv_eq_left_inv hsP
  have hJ : Jm ε = P * Hpk k r * star P := by
    rw [← hP.1.2, ← Matrix.star_eq_conjTranspose]
    calc Jm ε = (P * star P) * Jm ε * (P * star P) := by rw [hPs, Matrix.one_mul, Matrix.mul_one]
      _ = P * (star P * Jm ε * P) * star P := by simp only [Matrix.mul_assoc]
  have memJ : ∀ x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      xᴴ * Hpk k r * x = Hpk k r → P * x * P⁻¹ ∈ UJset ε := by
    intro x hx
    have hx' : star x * Hpk k r * x = Hpk k r := by rw [Matrix.star_eq_conjTranspose]; exact hx
    show (P * x * P⁻¹)ᴴ * Jm ε * (P * x * P⁻¹) = Jm ε
    rw [hinv, hJ, ← Matrix.star_eq_conjTranspose]
    calc star (P * x * star P) * (P * Hpk k r * star P) * (P * x * star P)
        = P * (star x * (star P * P) * Hpk k r * (star P * P) * x) * star P := by
          simp only [star_mul, star_star, Matrix.mul_assoc]
      _ = P * (star x * Hpk k r * x) * star P := by simp only [hsP, Matrix.mul_one]
      _ = P * Hpk k r * star P := by rw [hx']
  have key : ∀ x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, P⁻¹ * (P * x * P⁻¹) * P = x := by
    intro x
    rw [hinv]
    calc star P * (P * x * star P) * P = (star P * P) * x * (star P * P) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [hsP, Matrix.one_mul, Matrix.mul_one]
  have hprod : (P * h * P⁻¹) * (P * g * P⁻¹) = P * (h * g) * P⁻¹ := by
    rw [hinv]
    calc P * h * star P * (P * g * star P) = P * h * (star P * P) * g * star P := by
          simp only [Matrix.mul_assoc]
      _ = P * (h * g) * star P := by rw [hsP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have h1 := hmul (P * h * P⁻¹) (memJ h hh) (P * g * P⁻¹) (memJ g hg)
  dsimp only at h1
  rw [hprod, key, key, key] at h1
  exact h1

theorem smooth_add {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} {x y : H}
    (hx : x ∈ smoothVecs (k := k) (r := r) σ) (hy : y ∈ smoothVecs (k := k) (r := r) σ) :
    x + y ∈ smoothVecs (k := k) (r := r) σ := by
  show SmoothOnH (Hpk k r) (fun g => σ g (x + y))
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hFe⟩ := (show SmoothOnH (Hpk k r) (fun g => σ g x) from hx) g₀ hg₀
  obtain ⟨V, G, hV, hgV, hG, hGe⟩ := (show SmoothOnH (Hpk k r) (fun g => σ g y) from hy) g₀ hg₀
  refine ⟨U ∩ V, fun g => F g + G g, hU.inter hV, ⟨hgU, hgV⟩,
    (hF.mono Set.inter_subset_left).add (hG.mono Set.inter_subset_right), fun g hg hgl => ?_⟩
  simp only [map_add (f := _), hFe g hg.1 hgl, hGe g hg.2 hgl]

theorem smooth_smul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} (c : ℂ) {x : H}
    (hx : x ∈ smoothVecs (k := k) (r := r) σ) : c • x ∈ smoothVecs (k := k) (r := r) σ := by
  show SmoothOnH (Hpk k r) (fun g => σ g (c • x))
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hFe⟩ := (show SmoothOnH (Hpk k r) (fun g => σ g x) from hx) g₀ hg₀
  refine ⟨U, fun g => c • F g, hU, hgU, hF.const_smul c, fun g hg hgl => ?_⟩
  simp only [map_smul, hFe g hg hgl]

theorem smooth_zero {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} :
    (0 : H) ∈ smoothVecs (k := k) (r := r) σ := by
  show SmoothOnH (Hpk k r) (fun g => σ g 0)
  intro g₀ _
  exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun g _ _ => by simp⟩

def mulRightCLM (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ →L[ℝ]
      Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun h => h * g
      map_add' := fun a b => Matrix.add_mul a b g
      map_smul' := fun c a => by simp [Matrix.smul_mul] }

theorem smooth_translate {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hds : IsDSHpk k r ε lam σ) {v : H} (hv : v ∈ smoothVecs (k := k) (r := r) σ)
    {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    σ g v ∈ smoothVecs (k := k) (r := r) σ := by
  intro h0 hh0
  obtain ⟨U, F, hU, hmem, hF, hEq⟩ := hv (h0 * g) (uh_mul hh0 hg)
  refine ⟨(mulRightCLM g) ⁻¹' U, fun h => F (h * g), hU.preimage (mulRightCLM g).continuous, hmem,
    hF.comp (mulRightCLM g).contDiff.contDiffOn (fun h hh => hh), ?_⟩
  intro h hhU hh
  have e := (hEq (h * g) hhU (uh_mul hh hg)).symm
  show σ h (σ g v) = F (h * g)
  rw [e]
  show σ h (σ g v) = σ (h * g) v
  rw [sigma_mul hds hh hg]
  rfl

end TranslationBesselVanishing


open TranslationBesselVanishing in
theorem bessel_ne_zero_of_cyclic_orbit : Formalism.FourierDecayAlt.ThreeDimData.DDNzOfCyc := by
  intro hCyc hKF k r ε lam H _ _ _ σ w0 Wp _ _ z c π hlam hds hlow Bm hB hzero x hx
  obtain ⟨hadd, -, -, C, Ws, hWs, hbd⟩ := hB
  have hw0 : w0 ∈ smoothVecs (k := k) (r := r) σ :=
    PI.UnitaryGroupMassFormula.LowSmooth.lowSmooth_of_kFinSmooth hKF k r ε lam H σ w0 hlam hds hlow
  by_contra hne
  have hpos : 0 < ‖Bm x‖ := norm_pos_iff.mpr hne
  have h2 : 0 < 2 * (|C| + 1) := by positivity
  set δ : ℝ := ‖Bm x‖ / (2 * (|C| + 1)) with hδdef
  have hδ : 0 < δ := div_pos hpos h2
  obtain ⟨N, cc, g, hg, hsum⟩ := hCyc k r ε lam H σ w0 hlam hds hlow x hx Ws hWs δ hδ
  set y : H := ∑ i, cc i • σ (g i) w0 with hy
  have hysm : y ∈ smoothVecs (k := k) (r := r) σ :=
    Finset.sum_induction _ (· ∈ smoothVecs (k := k) (r := r) σ) (fun a b ha hb => smooth_add ha hb)
      smooth_zero (fun i _ => smooth_smul _ (smooth_translate hds hw0 (hg i)))
  have hyDD : y ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp σ w0 :=
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨g i, hg i, rfl⟩))
  have hxy : x - y ∈ smoothVecs (k := k) (r := r) σ := by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ y]
    exact smooth_add hx (smooth_smul _ hysm)
  have hsplit : Bm x = Bm (x - y) + Bm y := by
    rw [← hadd _ hxy _ hysm, sub_add_cancel]
  have hBy : Bm y = 0 := hzero y hyDD
  have hb := hbd (x - y) hxy
  have hS0 : 0 ≤ (Ws.map fun w => ‖dsigW σ w (x - y)‖).sum := by
    apply List.sum_nonneg
    intro a ha
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp ha
    exact norm_nonneg _
  have hlt : ‖Bm x‖ < ‖Bm x‖ :=
    calc ‖Bm x‖ = ‖Bm (x - y)‖ := by rw [hsplit, hBy, add_zero]
      _ ≤ C * (Ws.map fun w => ‖dsigW σ w (x - y)‖).sum := hb
      _ ≤ |C| * (Ws.map fun w => ‖dsigW σ w (x - y)‖).sum :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hS0
      _ ≤ |C| * δ := mul_le_mul_of_nonneg_left hsum.le (abs_nonneg C)
      _ < ‖Bm x‖ := by
          rw [hδdef, ← mul_div_assoc, div_lt_iff₀ h2]
          nlinarith [abs_nonneg C, hpos]
  exact lt_irrefl _ hlt

end Formalism.FourierDecayAlt.P
end
end

section

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def levelZeroPointOver {k r : ℕ} (a : C.LPt) (hle : D.ptSize a ≤ r) (g : B.Mat k (r - D.ptSize a)) : B.Mat k r :=
  D.castM (by omega) (U.mMap k (D.ptSize a) (r - D.ptSize a) (U.hMat (D.ptPerm a) (D.ptDiag a)) g)

def LeftFubini : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (T : D.LevTower k r Wp Wq),
    D.TowerNormalised T → ∀ (j : ℕ) (hj : j ≤ r), 1 ≤ j → ∀ (a : C.LPt) (ha : D.IsLocPt a j),
    ∃ (X : Type) (_ : MeasurableSpace X) (μ : Measure X)
      (ℓ : X → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))) (sx : X → B.Mat k r),
      (∀ x, sx x ∈ Sset k r T.base.z) ∧
      ∀ g ∈ JF.Om k (r - j) (T.bs j).z (T.bs j).z', ∀ H : B.Mat k r → (Wq →L[ℂ] Wp),
        ContinuousOn H {x | x ∈ B.GV k r ∧ Dmin k r T.base.z T.base.z' x ⟨j, by omega⟩ ≠ 0} →
        (∃ R : ℝ, ∀ x ∈ B.GV k r, H x ≠ 0 → B.gN x ≤ R) →
        Integrable (fun x => ℓ x (PBG.Kr T.base H (sx x * levelZeroPointOver a (by rw [ha.2]; exact hj)
          (D.castM (by rw [ha.2]) g)))) μ ∧
        B.JF (T.bs j) (D.castF (by rw [ha.2]) (D.sliceAt k r T.base.z T.base.z' H a)) g =
          ∫ x, ℓ x (PBG.Kr T.base H (sx x * levelZeroPointOver a (by rw [ha.2]; exact hj) (D.castM (by rw [ha.2]) g))) ∂μ

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
end
end

section

noncomputable section

open Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEXMT

open Formalism.FourierDecayAlt

section cd

variable {m : ℕ}

theorem cd_det : ContDiff ℝ ∞ (fun M : Fin m → Fin m → ℂ => (Matrix.of M).det) := by
  simp only [Matrix.det_apply, Matrix.of_apply]
  refine ContDiff.sum fun σ _ => ?_
  refine ContDiff.const_smul _ ?_
  exact contDiff_prod fun i _ => by fun_prop

theorem cd_adj (i j : Fin m) : ContDiff ℝ ∞ (fun M : Fin m → Fin m → ℂ => (Matrix.of M).adjugate i j) := by
  have h : (fun M : Fin m → Fin m → ℂ => (Matrix.of M).adjugate i j) =
      (fun N : Fin m → Fin m → ℂ => (Matrix.of N).det) ∘
        (fun M : Fin m → Fin m → ℂ => fun a b => (Matrix.of M).updateRow j (Pi.single i 1) a b) := by
    funext M
    rw [Matrix.adjugate_apply]
    rfl
  rw [h]
  refine cd_det.comp ?_
  refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
  simp only [Matrix.updateRow_apply, Matrix.of_apply]
  split_ifs <;> fun_prop

theorem cd_inv (i j : Fin m) :
    ContDiffOn ℝ ∞ (fun M : Fin m → Fin m → ℂ => (Matrix.of M)⁻¹ i j) {M | (Matrix.of M).det ≠ 0} := by
  have h1 : ContDiffOn ℝ ∞
      (fun M : Fin m → Fin m → ℂ => ((Matrix.of M).det)⁻¹ * (Matrix.of M).adjugate i j)
      {M | (Matrix.of M).det ≠ 0} :=
    (cd_det.contDiffOn.inv fun M hM => hM).mul (cd_adj i j).contDiffOn
  refine h1.congr fun M _ => ?_
  simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]

end cd

section wm

variable {n : ℕ}

theorem cd_gram (a b : Fin n) : ContDiff ℝ ∞ (fun Z : Fin n → Fin n → ℂ => gram (Matrix.of Z) a b) := by
  simp only [gram, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  refine ContDiff.sum fun k _ => ContDiff.mul ?_ (by fun_prop)
  exact Complex.conjCLE.contDiff.comp
    (by fun_prop : ContDiff ℝ ∞ fun Z : Fin n → Fin n → ℂ => Z k a)

private lemma det_gram_castLE_ne_zero_of_det_ne_zero (Z : Fin n → Fin n → ℂ) (hZ : (Matrix.of Z).det ≠ 0) (k : ℕ)
    (hk : k ≤ n) :
    (Matrix.of fun a b : Fin k => gram (Matrix.of Z) (Fin.castLE hk a) (Fin.castLE hk b)).det ≠ 0 := by
  set E : Matrix (Fin n) (Fin k) ℂ := (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id (Fin.castLE hk) with hE
  set A : Matrix (Fin n) (Fin k) ℂ := Matrix.of Z * E with hA
  have hA' : ∀ r a, A r a = Z r (Fin.castLE hk a) := by
    intro r a
    simp [hA, hE, Matrix.mul_apply, Matrix.one_apply]
  have hB : (Matrix.of fun a b : Fin k => gram (Matrix.of Z) (Fin.castLE hk a) (Fin.castLE hk b)) =
      Aᴴ * A := by
    ext a b
    simp only [Matrix.of_apply, gram, Matrix.mul_apply, Matrix.conjTranspose_apply, hA']
  rw [hB]
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have h1 : A *ᵥ v = 0 := by
    open scoped ComplexOrder in
    exact (Matrix.conjTranspose_mul_self_mulVec_eq_zero A v).1 hv
  have h2 : E *ᵥ v = 0 := by
    by_contra hne
    apply hZ
    refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨E *ᵥ v, hne, ?_⟩
    rw [Matrix.mulVec_mulVec, ← hA, h1]
  apply hv0
  funext a
  have := congrFun h2 (Fin.castLE hk a)
  simpa [hE, Matrix.mulVec, dotProduct, Matrix.one_apply, Fin.castLE_inj] using this

theorem cd_Wm (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun Z : Fin n → Fin n → ℂ => Wm (Matrix.of Z) i j) {Z | (Matrix.of Z).det ≠ 0} := by
  simp only [Wm, blkJ, colJ, Matrix.of_apply]
  by_cases hij : (i : ℕ) < j
  · simp only [dif_pos hij, Matrix.mulVec, dotProduct, Pi.neg_apply]
    have hg : ContDiff ℝ ∞ (fun Z : Fin n → Fin n → ℂ => fun a b : Fin j =>
        gram (Matrix.of Z) (Fin.castLE j.isLt.le a) (Fin.castLE j.isLt.le b)) :=
      contDiff_pi.2 fun a => contDiff_pi.2 fun b => cd_gram _ _
    refine ContDiffOn.neg (ContDiffOn.sum fun c _ => ContDiffOn.mul ?_ (cd_gram _ _).contDiffOn)
    exact (cd_inv (m := j) ⟨i, hij⟩ c).comp hg.contDiffOn fun Z hZ => det_gram_castLE_ne_zero_of_det_ne_zero Z hZ j j.isLt.le
  · simp only [dif_neg hij]
    split_ifs <;> exact contDiffOn_const

theorem cd_Sm (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun Z : Fin n → Fin n → ℂ => Sm (Matrix.of Z) i j) {Z | (Matrix.of Z).det ≠ 0} := by
  have hW : ContDiffOn ℝ ∞ (fun Z : Fin n → Fin n → ℂ => fun a b => Wm (Matrix.of Z) a b)
      {Z | (Matrix.of Z).det ≠ 0} :=
    contDiffOn_pi.2 fun a => contDiffOn_pi.2 fun b => cd_Wm a b
  exact (cd_adj i j).comp_contDiffOn hW

end wm

end Formalism.FourierDecayAlt.P.CutEXMT
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Filter Topology

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.DifferentialOperatorClasses

section ops

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem gf_cont (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Continuous fun g : B.Mat k r => Gf k r z z' g := by
  obtain ⟨q, _, hq⟩ := P.gram_function_polynomial k r z z'
  have h1 : Continuous fun g : B.Mat k r => ((Gf k r z z' g : ℝ) : ℂ) := by
    have e : (fun g : B.Mat k r => ((Gf k r z z' g : ℝ) : ℂ)) =
        fun g => MvPolynomial.eval (Sum.elim (fun x => g x.1 x.2) (fun x => star (g x.1 x.2))) q := funext hq
    rw [e]
    refine (MvPolynomial.continuous_eval q).comp ?_
    refine continuous_pi fun i => ?_
    rcases i with ⟨a, b⟩ | ⟨a, b⟩
    · simp only [Sum.elim_inl]; exact continuous_id.matrix_elem a b
    · simp only [Sum.elim_inr]; exact continuous_star.comp (continuous_id.matrix_elem a b)
  have := Complex.continuous_re.comp h1
  refine this.congr fun g => ?_
  simp

end ops

end Formalism.FourierDecayAlt.P.DifferentialOperatorClasses

namespace Formalism.FourierDecayAlt.P

open DifferentialOperatorClasses

end Formalism.FourierDecayAlt.P
end
end

section

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k : ℕ}

theorem lift_lift_V (j ρ n r : ℕ) (hn : 1 + ρ = n) (h1 : j + n = r) (h2 : j + 1 + ρ = r)
    (v : Fin (2 * ρ + k + 1) → ℂ) :
    D.castV h1 (liftVec k j n (D.castV hn (liftVec k 1 ρ v))) = D.castV h2 (liftVec k (j + 1) ρ v) := by
  funext i
  simp only [D.castV, liftVec, Fin.coe_cast]
  split_ifs <;> (try simp only [Fin.ext_iff, Fin.val_mk, Fin.coe_cast] at *) <;> first | rfl | omega | (congr 1 <;> ext <;> simp only [Fin.val_mk, Fin.coe_cast] <;> omega)

theorem lift_lift_M (j ρ n r : ℕ) (hn : 1 + ρ = n) (h1 : j + n = r) (h2 : j + 1 + ρ = r) (y : B.Mat k ρ) :
    D.castM h1 (ιLev k j n (D.castM hn (ιLev k 1 ρ y))) = D.castM h2 (ιLev k (j + 1) ρ y) := by
  ext p q
  simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_symm, finCongr_apply, Fin.coe_cast, ιLev]
  split_ifs <;> (try simp only [Fin.ext_iff, Fin.val_mk, Fin.coe_cast] at *) <;> first | rfl | omega | (congr 1 <;> ext <;> simp only [Fin.val_mk, Fin.coe_cast] <;> omega)

theorem castV_inj {a b : ℕ} (h : a = b) {v w : Fin (2 * a + k + 1) → ℂ} (e : D.castV h v = D.castV h w) : v = w := by
  subst h
  funext i
  simpa [D.castV] using congrFun e i

section tower

variable {r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem levTower_bs_z_eq_castV_liftVec (T : D.LevTower k r Wp Wq) (j : ℕ) (hj : j + 1 ≤ r) :
    (T.bs j).z = D.castV (by omega : 1 + (r - (j + 1)) = r - j) (liftVec k 1 (r - (j + 1)) (T.bs (j + 1)).z) := by
  have e1 := T.z_lev j (by omega)
  have e2 := T.z_lev (j + 1) hj
  rw [← lift_lift_V j (r - (j + 1)) (r - j) r (by omega) (by omega) (by omega)] at e2
  have e3 := castV_inj _ (e1.trans e2.symm)
  funext i
  have hi := i.isLt
  have hi' : i.val ≤ 2 * (r - j) + k := by omega
  have := congrFun e3 ⟨i.val + j, by omega⟩
  simpa [liftVec, hi'] using this

theorem levTower_bs_z'_eq_castV_liftVec (T : D.LevTower k r Wp Wq) (j : ℕ) (hj : j + 1 ≤ r) :
    (T.bs j).z' = D.castV (by omega : 1 + (r - (j + 1)) = r - j) (liftVec k 1 (r - (j + 1)) (T.bs (j + 1)).z') := by
  have e1 := T.z'_lev j (by omega)
  have e2 := T.z'_lev (j + 1) hj
  rw [← lift_lift_V j (r - (j + 1)) (r - j) r (by omega) (by omega) (by omega)] at e2
  have e3 := castV_inj _ (e1.trans e2.symm)
  funext i
  have hi := i.isLt
  have hi' : i.val ≤ 2 * (r - j) + k := by omega
  have := congrFun e3 ⟨i.val + j, by omega⟩
  simpa [liftVec, hi'] using this

theorem tower_π (T : D.LevTower k r Wp Wq) (j : ℕ) (hj : j + 1 ≤ r) (y : B.Mat k (r - (j + 1))) :
    (T.bs (j + 1)).π y = (T.bs j).π (D.castM (by omega : 1 + (r - (j + 1)) = r - j) (ιLev k 1 (r - (j + 1)) y)) := by
  rw [T.π_lev (j + 1) hj y, T.π_lev j (by omega),
    lift_lift_M j (r - (j + 1)) (r - j) r (by omega) (by omega) (by omega)]

theorem tower_π' (T : D.LevTower k r Wp Wq) (j : ℕ) (hj : j + 1 ≤ r) (y : B.Mat k (r - (j + 1))) :
    (T.bs (j + 1)).π' y = (T.bs j).π' (D.castM (by omega : 1 + (r - (j + 1)) = r - j) (ιLev k 1 (r - (j + 1)) y)) := by
  rw [T.π'_lev (j + 1) hj y, T.π'_lev j (by omega),
    lift_lift_M j (r - (j + 1)) (r - j) r (by omega) (by omega) (by omega)]

end tower

end Formalism.FourierDecayAlt.P.PBH
end
end
