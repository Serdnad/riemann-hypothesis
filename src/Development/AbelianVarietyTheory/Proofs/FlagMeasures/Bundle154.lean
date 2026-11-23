module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle111
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle129
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle106
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle131
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

@[expose] public section

section

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

namespace GlobalTheory.Proof.rational_unipotentRadical_mem_adelic

theorem sub_one_map {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {n : ℕ}
    (g : Matrix (Fin n) (Fin n) E) : g.map ι - 1 = (g - 1).map ι := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem map_mulVec_incl {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) E) (w : Fin n → E) :
    M.map ι *ᵥ (fun i => ι (w i)) = fun i => ι ((M *ᵥ w) i) := by
  funext i

  simp [Matrix.mulVec, dotProduct, map_sum]

theorem map_mulVec_span {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) E) (S : Set (Fin n → E)) (T : Submodule A (Fin n → A))
    (h : ∀ w ∈ S, (fun i => ι ((M *ᵥ w) i)) ∈ T) :
    ∀ y ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' S), M.map ι *ᵥ y ∈ T := by
  intro y hy
  have : Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' S) ≤
      T.comap (M.map ι).mulVecLin := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
    rw [map_mulVec_incl]
    exact h w hw
  exact this hy

theorem span_univ {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {n : ℕ} :
    Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' Set.univ) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun A (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  apply Submodule.subset_span
  refine ⟨Pi.single j 1, trivial, ?_⟩
  funext i
  by_cases h : i = j <;> simp [Pi.single_apply, h]

theorem inUnipRad_map (I : AutInst) {A : Type} [CommRing A] (σ : I.E →+* I.E) (s : A →+* A)
    (ι : I.E →+* A) (hι : ∀ e, s (ι e) = ι (σ e)) (W : Submodule I.E (Fin I.n → I.E))
    (g : Matrix (Fin I.n) (Fin I.n) I.E) (hg : I.InUnipRad σ I.J W g) :
    I.InUnipRad s (I.J.map ι)
      (Submodule.span A ((fun w : Fin I.n → I.E => fun i => ι (w i)) '' (W : Set _))) (g.map ι) := by
  obtain ⟨h1, h2, h3⟩ := hg
  have hp := GlobalTheory.PerpBaseChange.perpSet_baseChange I.E A σ s ι I.n I.J W hι
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [sub_one_map]
    have h0 : ∀ w ∈ (W : Set (Fin I.n → I.E)), (fun i => ι (((g - 1) *ᵥ w) i)) ∈ (⊥ : Submodule A (Fin I.n → A)) := by
      intro w hw
      rw [h1 w hw, Submodule.mem_bot]
      funext i
      exact map_zero ι
    have := map_mulVec_span ι (g - 1) (W : Set (Fin I.n → I.E)) ⊥ h0 x hx
    exact (Submodule.mem_bot A).1 this
  · intro y hy
    replace hy := (Set.ext_iff.1 hp y).1 hy
    rw [sub_one_map]
    refine map_mulVec_span ι (g - 1) _ _ (fun w hw => ?_) y hy
    exact Submodule.subset_span ⟨_, h2 w hw, rfl⟩
  · intro y
    refine (Set.ext_iff.1 hp _).2 ?_
    rw [sub_one_map]
    refine map_mulVec_span ι (g - 1) Set.univ _ (fun w _ => ?_) y (by rw [span_univ]; trivial)
    exact Submodule.subset_span ⟨_, h3 w, rfl⟩

theorem unitary_map {E A : Type} [CommRing E] [CommRing A] (σ : E →+* E) (s : A →+* A)
    (ι : E →+* A) (hι : ∀ e, s (ι e) = ι (σ e)) {n : ℕ} (J g : Matrix (Fin n) (Fin n) E)
    (hg : Formalism.UG.cT σ g * J * g = J) :
    Formalism.UG.cT s (g.map ι) * J.map ι * g.map ι = J.map ι := by
  have : Formalism.UG.cT s (g.map ι) = (Formalism.UG.cT σ g).map ι := by
    ext i j
    simp [Formalism.UG.cT, hι]
  rw [this, ← Matrix.map_mul, ← Matrix.map_mul, hg]

theorem rational_mem_adelic (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (γ : GL (Fin I.n) I.E)
    (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J)
    (hN : I.InUnipRad (starRingEnd I.E) I.J W (γ : Matrix (Fin I.n) (Fin I.n) I.E)) :
    ∃ a ∈ I.GFset ∩ I.NA W,
      (∀ v, uMat (a.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) ∧
      I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
  have hφ : ∀ v e, starRingEnd ℂ (I.φ v e) = I.φ v (starRingEnd I.E e) :=
    fun v e => (I.cm.cmUnram.2.1 (I.φ v) e).symm
  have hf : ∀ e, Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) e) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (starRingEnd I.E e) := by
    intro e
    simp [Formalism.UG.sigR, Formalism.UG.inclE]
    rfl
  have hdet : ∀ v, IsUnit (I.P v).det := fun v => (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hPP : ∀ v, I.P v * (I.P v)⁻¹ = 1 := fun v => Matrix.mul_nonsing_inv _ (hdet v)
  let u : ∀ v : InfinitePlace I.F, (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ := fun v =>
    (I.P_unit v).unit⁻¹ * Formalism.UG.bc (I.φ v) γ * (I.P_unit v).unit
  have hu : ∀ v, (u v : Matrix (Fin I.n) (Fin I.n) ℂ) =
      (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
    intro v
    simp only [u, Units.val_mul, Matrix.coe_units_inv, IsUnit.unit_spec]
    rfl
  have hPu : ∀ v, I.P v * (u v : Matrix (Fin I.n) (Fin I.n) ℂ) =
      (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
    intro v
    rw [hu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
  have hU : ∀ v, u v ∈ Formalism.REAL.UJ (I.ε v) := by
    intro v
    change (u v : Matrix (Fin I.n) (Fin I.n) ℂ)ᴴ * Jm (I.ε v) * (u v : Matrix (Fin I.n) (Fin I.n) ℂ) = Jm (I.ε v)
    have h := unitary_map _ _ (I.φ v) (hφ v) I.J _ hγ
    have hc : Formalism.UG.cT (starRingEnd ℂ) ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)) =
        ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ := by
      ext i j
      simp [Formalism.UG.cT]
    rw [hc] at h
    rw [← I.P_spec v]
    calc (u v : Matrix (Fin I.n) (Fin I.n) ℂ)ᴴ * ((I.P v)ᴴ * I.J.map (I.φ v) * I.P v) *
          (u v : Matrix (Fin I.n) (Fin I.n) ℂ)
        = (I.P v * (u v : Matrix (Fin I.n) (Fin I.n) ℂ))ᴴ * I.J.map (I.φ v) *
          (I.P v * (u v : Matrix (Fin I.n) (Fin I.n) ℂ)) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (I.P v)ᴴ * (((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ * I.J.map (I.φ v) *
          (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)) * I.P v := by
          rw [hPu]
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h]
  have hF : Formalism.UG.bc (Formalism.UG.inclE (F := I.F) (Af I.F)) γ ∈ Formalism.UG.UPts I.cm.sig I.J (Af I.F) :=
    unitary_map _ _ _ hf I.J _ hγ
  refine ⟨(fun v => ⟨u v, hU v⟩, ⟨_, hF⟩), ⟨⟨γ, hγ, hu, rfl⟩, fun v => ?_, ?_⟩, hu, rfl⟩
  · change I.InUnipRad _ _ _ (I.P v * (u v : Matrix (Fin I.n) (Fin I.n) ℂ) * (I.P v)⁻¹)
    rw [hPu, Matrix.mul_assoc, hPP, Matrix.mul_one]
    exact inUnipRad_map I _ _ _ (hφ v) W _ hN
  · exact inUnipRad_map I _ _ _ hf W _ hN

end GlobalTheory.Proof.rational_unipotentRadical_mem_adelic
end

section

open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory

theorem exists_weakIntegral_of_stronglyContinuous {X H : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [SecondCountableTopology X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (μ : Measure X) (R : X → (H →L[ℂ] H)) (hn : ∀ x F, ‖R x F‖ = ‖F‖)
    (hc : ∀ F, Continuous fun x => R x F) (φ : X → ℂ) (hφ : Integrable φ μ) :
    ∃ T : H →L[ℂ] H, ∀ x y : H, ⟪x, T y⟫_ℂ = ∫ g, φ g * ⟪x, R g y⟫_ℂ ∂μ := by
  have hint : ∀ y : H, Integrable (fun g => φ g • R g y) μ := fun y =>
    (hφ.norm.mul_const ‖y‖).mono' (hφ.aestronglyMeasurable.smul (hc y).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun g => by rw [norm_smul, hn])
  let Tl : H →ₗ[ℂ] H :=
    { toFun := fun y => ∫ g, φ g • R g y ∂μ
      map_add' := fun y z => by
        simp only [map_add (f := _), smul_add]
        exact integral_add (hint y) (hint z)
      map_smul' := fun c y => by
        simp only [map_smul, RingHom.id_apply]
        rw [← integral_smul]
        congr 1
        ext g
        rw [smul_comm] }
  refine ⟨Tl.mkContinuous (∫ g, ‖φ g‖ ∂μ) fun y => ?_, fun x y => ?_⟩
  · calc ‖Tl y‖ = ‖∫ g, φ g • R g y ∂μ‖ := rfl
      _ ≤ ∫ g, ‖φ g • R g y‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ g, ‖φ g‖ * ‖y‖ ∂μ := by
        congr 1
        ext g
        rw [norm_smul, hn]
      _ = (∫ g, ‖φ g‖ ∂μ) * ‖y‖ := integral_mul_const _ _
  · show ⟪x, ∫ g, φ g • R g y ∂μ⟫_ℂ = _
    rw [← integral_inner (hint y)]
    congr 1
    ext g
    rw [inner_smul_right]

theorem AutInst_exists_isRConvF_and_isRConv : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA), I.IsFundDom (I.muA μf) fund → ∀ R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund), I.IsRightReg μf fund R → (∀ e : I.Gf → ℂ, Integrable e μf → ∃ T, I.IsRConvF μf fund R e T) ∧ ∀ φ : I.GA → ℂ, Integrable φ (I.muA μf) → ∃ T, I.IsRConv μf fund R φ T := by
  intro I μf _ _ fund hfund R hR
  obtain ⟨-, -, hn, hc⟩ := GlobalTheory.T.rightRegularRepresentation_unitary_mul_continuous I μf fund hfund R hR
  haveI := GlobalTheory.T.secondCountable_finiteAdelicUnitaryPoints I
  refine ⟨fun e he => ?_, fun φ hφ => ?_⟩
  · obtain ⟨T, hT⟩ := exists_weakIntegral_of_stronglyContinuous μf (fun g => R (1, g))
      (fun g F => hn _ F) (fun F => (hc F).comp (by fun_prop)) e he
    exact ⟨T, he, hT⟩
  · obtain ⟨T, hT⟩ := exists_weakIntegral_of_stronglyContinuous (I.muA μf) R hn hc φ hφ
    exact ⟨T, hφ, hT⟩

end GlobalTheory
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas Formalism.REAL

noncomputable section

namespace GlobalTheory.NilCov

variable {n : ℕ} {ε : Fin n → Bool}

private theorem hs_eq_ipL (X : Matrix (Fin n) (Fin n) ℂ) : hs X = ipL X X := by
  rw [ipL_apply]
  simp only [Formalism.REAL.hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

private theorem hs_nonneg' (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem hs_mul_le (A B : Matrix (Fin n) (Fin n) ℂ) : hs (A * B) ≤ hs A * hs B := by

  have key : ∀ i j, ‖∑ k, A i k * B k j‖ ^ 2 ≤ (∑ k, ‖A i k‖ ^ 2) * ∑ k, ‖B k j‖ ^ 2 := by
    intro i j
    calc ‖∑ k, A i k * B k j‖ ^ 2 ≤ (∑ k, ‖A i k‖ * ‖B k j‖) ^ 2 := by
          gcongr
          exact (norm_sum_le _ _).trans (le_of_eq (by simp only [norm_mul]))
      _ ≤ (∑ k, ‖A i k‖ ^ 2) * ∑ k, ‖B k j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  simp only [Formalism.REAL.hs, Matrix.mul_apply]
  calc ∑ i, ∑ j, ‖∑ k, A i k * B k j‖ ^ 2
        ≤ ∑ i, ∑ j, (∑ k, ‖A i k‖ ^ 2) * ∑ k, ‖B k j‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
    _ = (∑ i, ∑ k, ‖A i k‖ ^ 2) * ∑ j, ∑ k, ‖B k j‖ ^ 2 := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ = (∑ i, ∑ k, ‖A i k‖ ^ 2) * ∑ k, ∑ j, ‖B k j‖ ^ 2 := by congr 1; exact Finset.sum_comm

private theorem hs_neg' (X : Matrix (Fin n) (Fin n) ℂ) : hs (-X) = hs X := by
  simp only [Formalism.REAL.hs, Matrix.neg_apply, norm_neg]

private theorem hs_inv_eq (X : Matrix (Fin n) (Fin n) ℂ) : hs (Jm ε * Xᴴ * Jm ε) = hs X := by

  have hsign : ∀ a, ‖(if ε a then (1 : ℂ) else -1)‖ = 1 := by
    intro a; split_ifs <;> simp
  simp only [Formalism.REAL.hs, Formalism.REAL.Jm, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.conjTranspose_apply, norm_mul, norm_star, hsign, one_mul, mul_one]
  exact Finset.sum_comm

private theorem hs_sub_add_hs_add_eq_parallelogram (X Y : Matrix (Fin n) (Fin n) ℂ) :
    hs (X - Y) + hs (X + Y) = 2 * hs X + 2 * hs Y := by
  simp only [Formalism.REAL.hs, Matrix.sub_apply, Matrix.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := parallelogram_law_with_norm ℝ (X i j) (Y i j)
  rw [sq, sq, sq, sq]
  linarith

theorem sum_coord_sq_le_hs_and_hs_le (n d : ℕ) (ε : Fin n → Bool) (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) (hG : ∀ i, inG ε (E i)) (g : UJ ε)
    (hsp : (uMat g - 1) - Jm ε * (uMat g - 1)ᴴ * Jm ε ∈ Submodule.span ℝ (Set.range E)) :
    ∑ i, (((uMat g - 1) * (E i)ᴴ).trace).re ^ 2 ≤ hs (uMat g - 1) ∧
      hs (uMat g - 1) ≤ ∑ i, (((uMat g - 1) * (E i)ᴴ).trace).re ^ 2 + hs (uMat g - 1) ^ 2 / 4 := by
  set X := uMat g - 1 with hXdef
  set Y := Jm ε * Xᴴ * Jm ε with hYdef

  have hc : ∀ i, ipL (E i) (X - Y) = 2 * ((X * (E i)ᴴ).trace).re := by
    intro i
    rw [ipL_sub_inv (hG i) X, ipL_apply]
  have hexp : X - Y = ∑ i, ipL (E i) (X - Y) • E i := eq_sum_of_mem_span hE hsp

  have hD : hs (X - Y) = 4 * ∑ i, ((X * (E i)ᴴ).trace).re ^ 2 := by
    have h1 : ipL (X - Y) (X - Y) = ∑ i, ipL (E i) (X - Y) * ipL (E i) (X - Y) := by
      calc ipL (X - Y) (X - Y) = ipL (X - Y) (∑ i, ipL (E i) (X - Y) • E i) :=
            congrArg (fun Z => ipL (X - Y) Z) hexp
        _ = ∑ i, ipL (E i) (X - Y) * ipL (X - Y) (E i) := by

            rw [map_sum]
            simp only [map_smul, smul_eq_mul]
        _ = ∑ i, ipL (E i) (X - Y) * ipL (E i) (X - Y) :=
            Finset.sum_congr rfl fun i _ => by rw [ipL_comm (E i) (X - Y)]
    rw [hs_eq_ipL, h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hc i]; ring

  have hS : hs (X + Y) ≤ hs X ^ 2 := by
    have hYX : X + Y = -(Y * X) := add_inv_eq g
    have hYn : hs Y = hs X := hs_inv_eq X
    rw [hYX, hs_neg', sq]
    calc hs (Y * X) ≤ hs Y * hs X := hs_mul_le Y X
      _ = hs X * hs X := by rw [hYn]
  have hpara := hs_sub_add_hs_add_eq_parallelogram X Y
  have hYn : hs Y = hs X := hs_inv_eq X
  have hnn : 0 ≤ hs (X + Y) := hs_nonneg' _
  constructor <;> linarith

end GlobalTheory.NilCov
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas Formalism.REAL

noncomputable section

namespace GlobalTheory.NilCovSec

open GlobalTheory.NilCov

variable {n : ℕ}

def jInv (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := Jm ε * Xᴴ * Jm ε

variable (ε : Fin n → Bool)

theorem jInv_sub (X Y : Matrix (Fin n) (Fin n) ℂ) : jInv ε (X - Y) = jInv ε X - jInv ε Y := by
  simp only [jInv, conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]

theorem jInv_smul (a : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : jInv ε (a • X) = a • jInv ε X := by
  simp [jInv, conjTranspose_smul]

theorem jInv_jInv_mul (X : Matrix (Fin n) (Fin n) ℂ) : jInv ε (jInv ε X * X) = jInv ε X * X := by
  simp only [jInv, conjTranspose_mul, Jm_conjTranspose, conjTranspose_conjTranspose, Matrix.mul_assoc,
    Jm_mul_self, Matrix.mul_one]

theorem continuous_jInv : Continuous (jInv ε) := by
  exact (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const

def iter (Y : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Nat.rec Y (fun _ X => Y - (1 / 2 : ℝ) • (jInv ε X * X)) k

theorem continuous_iter (k : ℕ) : Continuous fun Y => iter ε Y k := by
  induction k with
  | zero => exact continuous_id
  | succ k ih =>
    exact continuous_id.sub ((((continuous_jInv ε).comp ih).matrix_mul ih).const_smul (1 / 2 : ℝ))

variable {ε} {A : ℕ → Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}

theorem iter_mem (hmul : ∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1))
    (hle : ∀ c, A (c + 1) ≤ A c) (hinv : ∀ c, ∀ X ∈ A c, Jm ε * Xᴴ * Jm ε ∈ A c)
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y ∈ A 0) (k : ℕ) : iter ε Y k ∈ A 0 := by
  induction k with
  | zero => exact hY
  | succ k ih =>
    exact (A 0).sub_mem hY ((A 0).smul_mem _ (hle 0 (hmul 0 _ (hinv 0 _ ih) _ ih).1))

theorem iter_sub_mem (hmul : ∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1))
    (hle : ∀ c, A (c + 1) ≤ A c) (hinv : ∀ c, ∀ X ∈ A c, Jm ε * Xᴴ * Jm ε ∈ A c)
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y ∈ A 0) (k : ℕ) : iter ε Y (k + 1) - iter ε Y k ∈ A k := by
  have hm := iter_mem hmul hle hinv hY
  induction k with
  | zero => exact (A 0).sub_mem (hm 1) (hm 0)
  | succ k ih =>
    have e : iter ε Y (k + 1 + 1) - iter ε Y (k + 1) =
        (-(1 / 2) : ℝ) • (jInv ε (iter ε Y (k + 1) - iter ε Y k) * iter ε Y (k + 1) +
          jInv ε (iter ε Y k) * (iter ε Y (k + 1) - iter ε Y k)) := by
      have e1 : iter ε Y (k + 1 + 1) =
        Y - (1 / 2 : ℝ) • (jInv ε (iter ε Y (k + 1)) * iter ε Y (k + 1)) := rfl
      have e2 : iter ε Y (k + 1) = Y - (1 / 2 : ℝ) • (jInv ε (iter ε Y k) * iter ε Y k) := rfl
      rw [e1]
      generalize iter ε Y (k + 1) = P at e2 ⊢
      generalize iter ε Y k = Q at e2 ⊢
      rw [jInv_sub, Matrix.sub_mul, Matrix.mul_sub]
      nth_rewrite 3 [e2]
      module
    rw [e]
    exact (A _).smul_mem _ ((A _).add_mem (hmul k _ (hinv k _ ih) _ (hm _)).1
      (hmul k _ ih _ (hinv 0 _ (hm _))).2)

theorem one_add_mul_of_fixed {X Y : Matrix (Fin n) (Fin n) ℂ} (hY : jInv ε Y = -Y)
    (h : X = Y - (1 / 2 : ℝ) • (jInv ε X * X)) : (1 + jInv ε X) * (1 + X) = 1 := by
  have h2 : jInv ε X = -Y - (1 / 2 : ℝ) • (jInv ε X * X) := by
    conv_lhs => rw [h]
    rw [jInv_sub, jInv_smul, jInv_jInv_mul, hY]
  have h3 : X + jInv ε X + jInv ε X * X = 0 := by
    generalize jInv ε X * X = P at h h2 ⊢
    rw [h2, h]
    module
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one]
  calc 1 + X + (jInv ε X + jInv ε X * X) = 1 + (X + jInv ε X + jInv ε X * X) := by abel
    _ = 1 := by rw [h3, add_zero]

theorem inUJ_of_one_add_mul {X : Matrix (Fin n) (Fin n) ℂ} (h : (1 + jInv ε X) * (1 + X) = 1) :
    (1 + X)ᴴ * Jm ε * (1 + X) = Jm ε := by
  have e : (1 + X)ᴴ * Jm ε = Jm ε * (1 + jInv ε X) := by
    rw [conjTranspose_add, conjTranspose_one, Matrix.add_mul, Matrix.mul_add, jInv, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one]
  rw [e, Matrix.mul_assoc, h, Matrix.mul_one]

theorem exists_continuous_section (n d m : ℕ) (ε : Fin n → Bool)
    (A : ℕ → Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hA : A m = ⊥) (hmul : ∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1))
    (hle : ∀ c, A (c + 1) ≤ A c)
    (hinv : ∀ c, ∀ X ∈ A c, Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε ∈ A c)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0)
    (hG : ∀ i, E i ∈ A 0 ∧ Formalism.REAL.inG ε (E i)) :
    ∃ σ : (Fin d → ℝ) → Formalism.REAL.UJ ε, Continuous σ ∧ ∀ x, uMat (σ x) - 1 ∈ A 0 ∧
      ∀ i, (((uMat (σ x) - 1) * (E i)ᴴ).trace).re = x i := by
  let Y : (Fin d → ℝ) → Matrix (Fin n) (Fin n) ℂ := fun x => ∑ i, x i • E i
  have hYc : Continuous Y := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact (continuous_apply i).smul continuous_const
  have hY0 : ∀ x, Y x ∈ A 0 := fun x =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hG i).1
  have hYθ : ∀ x, jInv ε (Y x) = -Y x := fun x => by
    simp only [jInv, Y, conjTranspose_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := jInv_smul ε (x i) (E i)
    unfold jInv at this
    rw [this, inv_eq_neg_of_inG (hG i).2, smul_neg]
  let X : (Fin d → ℝ) → Matrix (Fin n) (Fin n) ℂ := fun x => iter ε (Y x) m
  have hXc : Continuous X := (continuous_iter ε m).comp hYc
  have hfix : ∀ x, X x = Y x - (1 / 2 : ℝ) • (jInv ε (X x) * X x) := fun x => by
    have h := iter_sub_mem hmul hle hinv (hY0 x) m
    rw [hA, Submodule.mem_bot, sub_eq_zero] at h
    exact h.symm
  have h1 : ∀ x, (1 + jInv ε (X x)) * (1 + X x) = 1 := fun x => one_add_mul_of_fixed (hYθ x) (hfix x)
  let u : (Fin d → ℝ) → (Matrix (Fin n) (Fin n) ℂ)ˣ := fun x =>
    ⟨1 + X x, 1 + jInv ε (X x), mul_eq_one_comm.1 (h1 x), h1 x⟩
  have huc : Continuous u := Units.continuous_iff.2
    ⟨continuous_const.add hXc, continuous_const.add ((continuous_jInv ε).comp hXc)⟩
  have hu : ∀ x, u x ∈ UJ ε := fun x => inUJ_of_one_add_mul (h1 x)
  refine ⟨fun x => ⟨u x, hu x⟩, huc.subtype_mk hu, fun x => ?_⟩
  have e : uMat (⟨u x, hu x⟩ : UJ ε) - 1 = X x := by
    change 1 + X x - 1 = X x
    abel
  rw [e]
  refine ⟨iter_mem hmul hle hinv (hY0 x) m, fun i => ?_⟩
  have h0 : ipL (E i) (jInv ε (X x) * X x) = 0 := by
    have h := ipL_inv (hG i).2 (jInv ε (X x) * X x)
    have h' : ipL (E i) (jInv ε (jInv ε (X x) * X x)) = -ipL (E i) (jInv ε (X x) * X x) := h
    rw [jInv_jInv_mul] at h'
    linarith
  rw [← ipL_apply, hfix x, map_sub, map_smul, h0, smul_zero, sub_zero]

  simp only [Y, map_sum, map_smul, ipL_apply, hE, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp

end GlobalTheory.NilCovSec
end
end

section

open MeasureTheory Formalism.MainNotions.S NumberField
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.rightRegularRep_unitary_stronglyContinuous : ∀ B : RowsAut, B.R 1 = 1 ∧ (∀ g h, B.R (g * h) = B.R g * B.R h) ∧ (∀ g F, ‖B.R g F‖ = ‖F‖) ∧ (∀ F, Continuous fun g => B.R g F) ∧ ∀ F : B.I.L2 B.μf B.fund, (∀ᵐ y ∂(B.I.muA B.μf), ∀ γ ∈ B.I.GFset, B.I.ext F (γ * y) = B.I.ext F y) ∧ AEStronglyMeasurable (B.I.ext F) (B.I.muA B.μf) := by
  first | exact @GlobalTheory.RightRegFund.rightReg_unitary_continuous | exact GlobalTheory.RightRegFund.rightReg_unitary_continuous | (intros; apply GlobalTheory.RightRegFund.rightReg_unitary_continuous <;> assumption)
end
