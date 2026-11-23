module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1588
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle022
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1595
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1244
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1594
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1600
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle193
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FsubMinorMinus
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1596
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1597
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle025

@[expose] public section

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.CCRFock
open MvPolynomial

theorem polEval_X {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} (m : ι → Module.End ℂ V)
    (hm : ∀ i j, m i * m j = m j * m i) (f₀ : V) (i : ι) (p : MvPolynomial ι ℂ) :
    polEval m hm f₀ (X i * p) = m i (polEval m hm f₀ p) := by
  simp [polEval, Module.End.mul_apply]

theorem polEval_one {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} (m : ι → Module.End ℂ V)
    (hm : ∀ i j, m i * m j = m j * m i) (f₀ : V) : polEval m hm f₀ 1 = f₀ := by
  simp [polEval]

theorem atPl_linear {W Λ : Type} [Fintype W] [DecidableEq W] (w : W) :
    ∃ L : Module.End ℂ (MvPolynomial Λ ℂ) →ₗ[ℂ] Module.End ℂ (⨂[ℂ] _ : W, MvPolynomial Λ ℂ),
      ∀ A, L A = GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w A := ⟨(PiTensorProduct.mapMultilinear ℂ (fun _ : W => MvPolynomial Λ ℂ) (fun _ : W => MvPolynomial Λ ℂ)).toLinearMap
      (fun _ => LinearMap.id) w, fun A => by
    simp [GlobalTheory.RealLift.atPl]⟩

theorem fock_map_of_ccr : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ}
    (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V),
    (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) →
    (∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1) →
    ∀ f₀ : V, f₀ ≠ 0 →
    (∀ w a b, H (Pi.single w (Matrix.single a b 1)) f₀ +
      (lineSign a b * Complex.I) • H (Pi.single w (Matrix.single a b Complex.I)) f₀ = 0) →
    ∃ Φ : (⨂[ℂ] _ : W, Pol P Q R S) →ₗ[ℂ] V, Function.Injective Φ ∧
      ∀ c T, Φ (sumPl (fun w => heisOp (c w)) T) = H c (Φ T) := by
  intro V _ _ W _ _ P Q R S H hadd hsmul hccr f₀ hf₀ hvac

  have hm : ∀ i j, fockM H i * fockM H j = fockM H j * fockM H i := GlobalTheory.T.heisenberg_creation_operators_commute_of_ccr H hadd hsmul hccr
  have hcr := GlobalTheory.T.heisenberg_annihilation_creation_commutator_eq_delta H hadd hsmul hccr

  have hd0 : ∀ j, fockD H j f₀ = 0 := by
    rintro ⟨w, a, b⟩
    have h := hvac w a b
    simp only [fockD, unitAt, LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.add_apply]
    rw [h, smul_zero, neg_zero]
  have hpd := GlobalTheory.T.commutingOperatorsPolynomialEval_pderiv (fockM H) (fockD H) hm f₀ hcr hd0
  have hinj0 : Function.Injective (polEval (fockM H) hm f₀) :=
    GlobalTheory.T.injective_of_map_pderiv_eq_and_map_one_ne_zero _ (fockD H) hpd (by rw [polEval_one]; exact hf₀)
  refine ⟨polEval (fockM H) hm f₀ ∘ₗ polMap W (Ix P Q × Ix R S), hinj0.comp (GlobalTheory.T.tensorPolynomialsToProductVariables_injective W _), ?_⟩

  have hX : ∀ (w : W) (l : Ix P Q × Ix R S) T, polEval (fockM H) hm f₀ (polMap W (Ix P Q × Ix R S)
      (GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial (Ix P Q × Ix R S) ℂ) w
        (LinearMap.mulLeft ℂ (MvPolynomial.X l)) T)) =
      fockM H (w, l) (polEval (fockM H) hm f₀ (polMap W (Ix P Q × Ix R S) T)) := by
    intro w l T
    have h := LinearMap.congr_fun (GlobalTheory.T.tensorPolynomialsToProductVariables_comp_mulLeft_X W (Ix P Q × Ix R S) w l) T
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply] at h
    rw [h, polEval_X]
  have hD : ∀ (w : W) (l : Ix P Q × Ix R S) T, polEval (fockM H) hm f₀ (polMap W (Ix P Q × Ix R S)
      (GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial (Ix P Q × Ix R S) ℂ) w
        (MvPolynomial.pderiv l).toLinearMap T)) =
      fockD H (w, l) (polEval (fockM H) hm f₀ (polMap W (Ix P Q × Ix R S) T)) := by
    intro w l T
    have h := LinearMap.congr_fun (GlobalTheory.T.tensorPolynomialsToProductVariables_comp_pderiv W (Ix P Q × Ix R S) w l) T
    simp only [LinearMap.comp_apply, Derivation.coeFn_coe] at h
    rw [h, hpd]

  choose L hL using fun w : W => atPl_linear (Λ := Ix P Q × Ix R S) w
  intro c T
  have hsum : ∀ w, GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial (Ix P Q × Ix R S) ℂ) w (heisOp (c w)) =
      ∑ l : Ix P Q × Ix R S, ((((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * coefM (c w l.1 l.2) (lineSign l.1 l.2)) •
          GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial (Ix P Q × Ix R S) ℂ) w
            (LinearMap.mulLeft ℂ (MvPolynomial.X l)) +
        (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * coefD (c w l.1 l.2) (lineSign l.1 l.2)) •
          GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial (Ix P Q × Ix R S) ℂ) w
            (MvPolynomial.pderiv l).toLinearMap) := by
    intro w
    clear hX hD hpd hinj0 hcr hm hd0 hvac hccr hsmul hadd hf₀

    rw [← hL w (heisOp (c w)), GlobalTheory.T.fockHeisenbergOperatorOfCoords_eq_sum_mulLeft_pderiv (c w), map_sum]
    simp only [map_add (f := _), map_smul]
    simp only [hL]
  rw [GlobalTheory.T.heisenberg_family_expand_creation_annihilation H hadd hsmul c]

  simp only [GlobalTheory.RealLift.sumPl, hsum, LinearMap.comp_apply, LinearMap.sum_apply,
  LinearMap.add_apply, LinearMap.smul_apply, map_sum, map_add, map_smul, hX, hD]
  conv_rhs => rw [Fintype.sum_prod_type]

end GlobalTheory.CCRFock
end
end

section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

noncomputable section

namespace GlobalTheory.RealCharF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem infPartF_cAF (σ : E →ₐ[F] E) (z : AEF F E) :
    infPartF F E (cAF σ z) = sigR (Ainf F) σ (infPartF F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem conj_theta_tmul_one [IsTotallyReal F] {τ : E →+* ℂ} {w : InfinitePlace F}
    (hw : w.embedding = τ.comp (algebraMap F E)) {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ) (a : Ainf F) :
    starRingEnd ℂ (θ (a ⊗ₜ[F] (1 : E))) = θ (a ⊗ₜ[F] (1 : E)) := by
  have hv : w.IsReal := IsTotallyReal.isReal w
  rw [GlobalTheory.DualPairCompare.gen_inf_val τ w hw θ h a, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv]
  exact Complex.conj_ofReal _

theorem theta_sigR {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {τ : E →+* ℂ} {w : InfinitePlace F}
    (hw : w.embedding = τ.comp (algebraMap F E)) {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ)
    (y : Ainf F ⊗[F] E) : θ (sigR (Ainf F) σ y) = starRingEnd ℂ (θ y) := by
  haveI : IsTotallyReal F := hσ.1
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a e =>
    have e1 : ∀ e' : E, a ⊗ₜ[F] e' = (a ⊗ₜ[F] (1 : E)) * ((1 : Ainf F) ⊗ₜ[F] e') := by
      intro e'; rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    show θ (a ⊗ₜ[F] σ e) = _
    rw [e1 (σ e), e1 e, map_mul, map_mul, map_mul, h.1, h.1, hσ.2.2.2, conj_theta_tmul_one hw h a]
    rfl

theorem theta_infPartF_incAF {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ) (e : E) :
    θ (infPartF F E (incAF F E e)) = τ e := by
  have : infPartF F E (incAF F E e) = (1 : Ainf F) ⊗ₜ[F] e := by
    show (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) ((1 : AF F) ⊗ₜ[F] e) = _
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  rw [this, h.1]

theorem theta_fstA_symplOHF {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {τ : E →+* ℂ} {w : InfinitePlace F}
    (hw : w.embedding = τ.comp (algebraMap F E)) {θ : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmbF τ θ)
    {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (x y : WOF F E nS nT) :
    θ (fstA F (symplOHF σ JS JT ξ₀ x y) ⊗ₜ[F] (1 : E)) =
      ((τ ξ₀ * θ (infPartF F E (hOF σ JS JT x y))).re : ℂ) := by
  set z := incAF F E ξ₀ * hOF σ JS JT x y with hz
  have h1 : fstA F (symplOHF σ JS JT ξ₀ x y) =
      algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (infPartF F E z) := by
    unfold symplOHF symplOF
    rw [map_mul, AlgHom.commutes, GlobalTheory.HeisLineDiffF.map_trace_tens]
    rfl
  have h2 : ∀ c : Ainf F, c ⊗ₜ[F] (1 : E) = algebraMap (Ainf F) (Ainf F ⊗[F] E) c := by
    intro c
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have h3 : θ (algebraMap (Ainf F) (Ainf F ⊗[F] E) (algebraMap F (Ainf F) (1 / 2))) = 1 / 2 := by
    rw [← IsScalarTower.algebraMap_apply]
    have : (θ.comp (algebraMap F (Ainf F ⊗[F] E))) (1 / 2) = 1 / 2 := by
      rw [map_div₀, map_one, map_ofNat]
    exact this
  have h4 : θ (infPartF F E z) = τ ξ₀ * θ (infPartF F E (hOF σ JS JT x y)) := by
    rw [hz, map_mul, map_mul, theta_infPartF_incAF h]
  rw [h1, h2, map_mul, map_mul, GlobalTheory.SelfDualLatticeCompare.trace_tensor (Ainf F) hσ, map_add (f := _),
    theta_sigR hσ hw h, h3, h4, Complex.add_conj]
  push_cast
  ring

theorem theta_hOF {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {tau : InfinitePlace F → (E →+* ℂ)}
    (hw : ∀ w, w.embedding = (tau w).comp (algebraMap F E)) {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)}
    (hθ : IsInfFamF tau θ) {ι : (InfinitePlace F → ℂ) →+ AEF F E} (hι : IsChartF θ ι)
    {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} (JT : Matrix (Fin nT) (Fin nT) E) (hJS : JS.det ≠ 0)
    (u v : IxF F nS nT → ℂ) (w : InfinitePlace F) :
    θ w (infPartF F E (hOF σ JS JT (iotaVF ι u) (iotaVF ι v))) =
      ((JS.map (tau w))⁻¹ * (cpt v w)ᴴ * JT.map (tau w) * cpt u w).trace := by
  rw [GlobalTheory.OrientedChar.map_inv_field _ _ hJS, GlobalTheory.OrientedChar.trace_four]
  unfold hOF

  simp only [map_sum, map_mul, infPartF_cAF, theta_sigR hσ (hw w) (hθ w), theta_infPartF_incAF (hθ w),
  iotaVF, Matrix.of_apply, hι.comp, cpt, Matrix.map_apply]

theorem trace_HMF {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
    (tau : InfinitePlace F → (E →+* ℂ)) (u v : IxF F nS nT → ℂ) :
    star v ⬝ᵥ HMF JS JT ξ₀ tau *ᵥ u = ∑ w, ((2 * (tau w ξ₀).im : ℝ) : ℂ) *
      ((JS.map (tau w))⁻¹ * (cpt v w)ᴴ * JT.map (tau w) * cpt u w).trace := by
  rw [star_dotProduct_eq]
  refine Finset.sum_congr rfl fun w _ => ?_
  unfold HMF
  rw [cpt_blk, ← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul]
  simp only [Matrix.mul_assoc]

theorem psi_symplOHF_iotaVF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ u v : IxF F nS nT → ℂ, B.ψ (symplOHF σ JS JT ξ₀ (iotaVF ι u) (iotaVF ι v)) =
        Complex.exp (Real.pi * Complex.I * ((star v ⬝ᵥ HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) *ᵥ u).im : ℂ)) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ θ hθ ι hι u v
  have hσ := hB.cm
  haveI : IsTotallyReal F := hσ.1
  have hψ := GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB
  have hw : ∀ w : InfinitePlace F, w.embedding = (B.emb w).1.comp (algebraMap F E) := fun w => (B.emb w).2.symm
  set s := symplOHF σ JS JT ξ₀ (iotaVF ι u) (iotaVF ι v) with hs
  have hsnd : sndA F s = 0 :=
    GlobalTheory.HeisDerivCM.map_symplOHF_eq_zero (sndA F) σ JS JT ξ₀ _ _ (Or.inr (real_iotaVF hι v))
  have e1 : B.ψ s = psiInf F B.ψ (fstA F s) := by
    have hsplit : s = pairA F (fstA F s) 0 := Prod.ext rfl hsnd
    conv_lhs => rw [hsplit]
    rfl
  have hre : ∀ w : InfinitePlace F, ((B.emb w).1 ξ₀).re = 0 := by
    intro w
    have h1 := hσ.2.2.2 (B.emb w).1 ξ₀
    rw [hσξ, map_neg] at h1
    have h2 := congrArg Complex.re h1
    rw [Complex.neg_re, Complex.star_def, Complex.conj_re] at h2
    linarith
  rw [e1, hψ.2.2 θ hθ, trace_HMF]
  have e2 : ∑ w, θ w (fstA F s ⊗ₜ[F] (1 : E)) = ∑ w, ((((B.emb w).1 ξ₀) *
      ((JS.map (B.emb w).1)⁻¹ * (cpt v w)ᴴ * JT.map (B.emb w).1 * cpt u w).trace).re : ℂ) :=
    Finset.sum_congr rfl fun w _ => by
      rw [hs, theta_fstA_symplOHF hσ (hw w) (hθ w) JS JT ξ₀ (iotaVF ι u) (iotaVF ι v),
        theta_hOF hσ hw hθ hι JT hJS.2 u v]
  rw [e2]
  congr 1
  rw [Complex.im_sum]
  simp only [Complex.mul_re, hre, Complex.im_ofReal_mul, zero_mul, zero_sub]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

end GlobalTheory.RealCharF
end
end

section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

theorem _root_.GlobalTheory.T.exists_realChart_adeleTensor_admissibleCMBase : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∃ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι := by
  first | exact @GlobalTheory.RealWeilF.CMChart.exists_chartF | exact GlobalTheory.RealWeilF.CMChart.exists_chartF | (intros; apply GlobalTheory.RealWeilF.CMChart.exists_chartF <;> assumption)
end

section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

theorem _root_.GlobalTheory.T.hermitianFormRealCoordinateMatrix_hermitian_det_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1))ᴴ = HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) ∧ (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1)).det ≠ 0 := by
  first | exact @GlobalTheory.RealWeilF.HMF_herm_det | exact GlobalTheory.RealWeilF.HMF_herm_det | (intros; apply GlobalTheory.RealWeilF.HMF_herm_det <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.diagonalThetaIntegral_eq_nonzero_mul_diagonal : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)),
            Formalism.IndefR.Datum.IsCovolOne (ratL T S) ν 𝓕 →
          ∀ μ : @MeasureTheory.Measure (κ → AF D.host.F) (borel _),
            @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
            ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ),
              GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ) =
                c * GlobalTheory.DiagSiegel.diagInt μ Φ := by
  first | exact @GlobalTheory.DiagSiegelUnfold.diag_theta_integral | exact GlobalTheory.DiagSiegelUnfold.diag_theta_integral | (intros; apply GlobalTheory.DiagSiegelUnfold.diag_theta_integral <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.isConjugateDualTwistBy_twist_of_conjSelfDual : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {m : ℕ} {π : GlobalTheory.CuspRep.CuspSub E m}, π.IsCsd → ∀ χ : Formalism.L2.Host.HChar E, GlobalTheory.GalOfCusp.IsConjDualBy (π.twist χ) (χ * (GlobalTheory.ThetaPull.thetaChar χ)⁻¹) := by
  first | exact @GlobalTheory.ConjDualTwist.isConjDualBy_twist_thetaChar | exact GlobalTheory.ConjDualTwist.isConjDualBy_twist_thetaChar | (intros; apply GlobalTheory.ConjDualTwist.isConjDualBy_twist_thetaChar <;> assumption)
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.MinorWeight

open GlobalTheory.JointHarm

theorem detPlus_diagonal {m : ℕ} (ε : Fin m → Bool) (d : Fin m → ℂ) :
    detP ε (diagonal d) = ∏ a, if ε a then d a else 1 := by
  have e : (1 / 2 : ℂ) • (1 + Formalism.REAL.Jm ε) * diagonal d + (1 / 2 : ℂ) • (1 - Formalism.REAL.Jm ε) =
      diagonal fun a => if ε a then d a else 1 := by
    ext a b
    by_cases h : a = b
    · subst h
      cases e : ε a <;> simp [Formalism.REAL.Jm, e] <;> ring
    · simp [Formalism.REAL.Jm, h]
  rw [detP, e, det_diagonal]

theorem detM_diagonal {m : ℕ} (ε : Fin m → Bool) (d : Fin m → ℂ) :
    detM ε (diagonal d) = ∏ a, if ε a then 1 else d a := by
  have e : (1 / 2 : ℂ) • (1 - Formalism.REAL.Jm ε) * diagonal d + (1 / 2 : ℂ) • (1 + Formalism.REAL.Jm ε) =
      diagonal fun a => if ε a then 1 else d a := by
    ext a b
    by_cases h : a = b
    · subst h
      cases e : ε a <;> simp [Formalism.REAL.Jm, e] <;> ring
    · simp [Formalism.REAL.Jm, h]
  rw [detM, e, det_diagonal]

theorem fact_diagonal {D : D7} {m n : ℕ} (ε : D.what₂.Tau → Fin m → Bool) (p q : D.what₂.Tau → ℕ)
    (ap am : D.what₂.Tau → ℕ → ℕ) (x₁ x₂ x₃ : D.what₂.Tau → ℤ) (hmn : m ≤ n) (hpq : ∀ τ, p τ + q τ = m)
    (hε : ∀ τ a, ε τ a = decide ((a : ℕ) < p τ)) (hap : ∀ τ a b, a ≤ b → b < p τ → ap τ b ≤ ap τ a)
    (ham : ∀ τ a b, a ≤ b → b < q τ → am τ b ≤ am τ a) (d : D.what₂.Tau → Fin m → ℂ) (hd : ∀ τ a, d τ a ≠ 0) :
    fact ε x₁ x₂ x₃ (fun τ => diagonal (d τ)) (fun _ => 1) (delta p q ap am : PolF D m n) =
      (∏ τ, ∏ a, d τ a ^ (if (a : ℕ) < p τ then (ap τ a : ℤ) + x₁ τ else -(am τ (a - p τ) : ℤ) + x₂ τ)) •
        (delta p q ap am : PolF D m n) := by
  have h := DeltaEig.fsub_delta D m n ε p q ap am hmn hpq hε hap ham (fun τ => diagonal (d τ)) (fun _ => 1)
    (fun τ => ⟨by
      rw [Matrix.isUnit_iff_isUnit_det, det_diagonal]
      exact (Finset.prod_ne_zero_iff.2 fun a _ => hd τ a).isUnit, by
      simp [Formalism.REAL.Jm, diagonal_mul_diagonal, mul_comm]⟩)
    (fun τ a b h => by
      obtain rfl : a = b := by
        by_contra e
        exact h (diagonal_apply_ne _ e)
      exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩)
    (fun τ => ⟨isUnit_one, fun a b h => Matrix.one_apply_ne h.ne⟩)
  rw [fact, LinearMap.smul_apply, AlgHom.toLinearMap_apply, h, smul_smul, fchar, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp only [detPlus_diagonal, detM_diagonal, det_one, _root_.one_zpow, mul_one, Matrix.one_apply_eq, Finset.prod_const_one,
    diagonal_apply_eq, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [hε]
  by_cases ha : (a : ℕ) < p τ <;> simp [ha, zpow_add₀ (hd τ a), mul_comm]

theorem pure_one {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (f : X → ℂ) : pureTensorL A f 1 = f := by
  have e : (1 : MvPolynomial ι ℂ) = MvPolynomial.basisMonomials ι ℂ 0 := by
    rw [MvPolynomial.coe_basisMonomials]; rfl
  rw [e]
  unfold pureTensorL
  rw [Module.Basis.constr_basis]
  simp [opPow]

theorem conj_mem {D : D7} {T : HSp D} {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel T S) (τ : D.what₂.Tau)
    {k : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hk : k ∈ Formalism.REAL.Kset (M.ε τ)) :
    (M.fr τ)⁻¹ * k * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D T τ) := by
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ))
  have hk' : kᴴ * Formalism.REAL.Jm (M.ε τ) * k = Formalism.REAL.Jm (M.ε τ) := kset_uj hk
  have h3 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  show _ᴴ * _ * _ = _
  rw [← M.fr_gram τ]
  calc _ = (M.fr τ)ᴴ * (kᴴ * (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * k) *
        M.fr τ := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1, h3, Matrix.mul_one, Matrix.mul_one, hk']

end GlobalTheory.AdTh.MinorWeight
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic

theorem _root_.GlobalTheory.T.lbH0_nef_pow_tens_ample_le_mul_pow_dim : GlobalTheory.Published.NefNumerics → ∀ (F : Type) [Field F] (Z : Scheme.{0}) [Algebra F Γ(Z, ⊤)] (d : ℕ), IsProjOver (strHom F (X := Z)) → topologicalKrullDim Z ≤ d → ∀ L A : LB Z, IsNef F L → IsAmpleLB A → ∃ C : ℝ, ∀ᶠ m : ℕ in atTop, (lbH0 F (tens (lbPow L m) A) : ℝ) ≤ C * (m : ℝ) ^ d := by
  first | exact @GlobalTheory.NefGrowth.lineBundleGlobalSectionsDim_nefPow_tensor_ample_isBigO | exact GlobalTheory.NefGrowth.lineBundleGlobalSectionsDim_nefPow_tensor_ample_isBigO | (intros; apply GlobalTheory.NefGrowth.lineBundleGlobalSectionsDim_nefPow_tensor_ample_isBigO <;> assumption)
end

section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

theorem _root_.GlobalTheory.T.contDiffOn_coefficients_delOperator_dbarOperator : ∀ (n : ℕ) (s : Set (V n)) (F : V n → Alt n), IsOpen s →
    (∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (F v) S) s) →
    ∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (delAt F v) S) s ∧ ContDiffOn ℝ ∞ (fun v => (bas n).repr (dbarAt F v) S) s := by
  first | exact @GlobalTheory.CxForm.SmoothCoef.contDiffOn_coef | exact GlobalTheory.CxForm.SmoothCoef.contDiffOn_coef | (intros; apply GlobalTheory.CxForm.SmoothCoef.contDiffOn_coef <;> assumption)
end
