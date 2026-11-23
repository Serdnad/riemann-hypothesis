module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle704
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchwartzIntertwinesMetaplecticQuadratic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingExistsDoublingConfiguration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle037
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle002
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1114
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008

@[expose] public section

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.CCRFock

theorem coefM_one (z : ℂ) : coefM z 1 = z := by
  simp [coefM, Complex.ext_iff]

theorem coefM_neg_one (z : ℂ) : coefM z (-1) = star z := by
  simp [coefM, Complex.ext_iff]

theorem coefD_one (z : ℂ) : coefD z 1 = -star z := by
  simp [coefD, Complex.ext_iff]

theorem coefD_neg_one (z : ℂ) : coefD z (-1) = -z := by
  simp [coefD, Complex.ext_iff]

theorem heisOp_eq_sum_mul_pderiv : ∀ {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ),
    heisOp c = ∑ l : Ix P Q × Ix R S,
      ((((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefM (c l.1 l.2) (lineSign l.1 l.2)) •
          LinearMap.mulLeft ℂ (MvPolynomial.X l) +
        (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefD (c l.1 l.2) (lineSign l.1 l.2)) •
          (MvPolynomial.pderiv l).toLinearMap) := by
  intro P Q R S c
  unfold heisOp
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  rintro ⟨a, b⟩ -
  rcases a with a | a <;> rcases b with b | b <;>
    simp only [raiB, lowB, linePos, lineSign, coefM_one, coefM_neg_one, coefD_one, coefD_neg_one, if_true,
      Bool.false_eq_true, if_false] <;>
    module

end GlobalTheory.CCRFock
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl


theorem _root_.GlobalTheory.T.doubled_hermitian_space_frame_of_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (α β : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (P Q R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ),
    Framed τ JA JB a b A C → Framed τ JA (dbl JB) a b A (fun w => dblM (C w)) := by
  first | exact @GlobalTheory.RealLift.Dbl.framed_dbl | exact GlobalTheory.RealLift.Dbl.framed_dbl | (intros; apply GlobalTheory.RealLift.Dbl.framed_dbl <;> assumption)
end

section

open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil

theorem _root_.GlobalTheory.T.fockToSchwartz_intertwines_metaplecticQuadratic : (∀ (l κ : Type) [Fintype l] [DecidableEq l] [Fintype κ] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (u v : κ → (l ⊕ l → ℝ)),
    (∀ w, ∑ i, sympl (v i) w • u i = w) →
    quad X = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ i, (1 / 2 : ℂ) •
      (dRho (X *ᵥ u i) * dRho (v i) + dRho (v i) * dRho (X *ᵥ u i))) → (∀ (P Q R S : ℕ) (Y : Mat R S), Y ∈ upq R S →
    fockAct2 P Q R S Y = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ a : Ix P Q, ∑ b : Ix R S, (lineSign a b / 4) •
      ((heisOp (Matrix.single a b (1 : ℂ) * Yᵀ) * heisOp (Matrix.single a b Complex.I) +
          heisOp (Matrix.single a b Complex.I) * heisOp (Matrix.single a b (1 : ℂ) * Yᵀ)) -
        (heisOp (Matrix.single a b Complex.I * Yᵀ) * heisOp (Matrix.single a b (1 : ℂ)) +
          heisOp (Matrix.single a b (1 : ℂ)) * heisOp (Matrix.single a b Complex.I * Yᵀ)))) → ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ℕ)
    (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ (Ψ : (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S) →ₗ[ℂ] Sch l),
    (∀ c T, Ψ (sumPl (fun w => heisOp (c w)) T) = dRho (φ c) (Ψ T)) →
    ∀ Y : ι → Mat R S, (∀ w, Y w ∈ upq R S) → ∀ Z : Matrix (l ⊕ l) (l ⊕ l) ℝ,
    (∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ) →
    ∀ T, quad Z (Ψ T) = Ψ (sumPl (fun w => fockAct2 P Q R S (Y w)) T) := by
  first | exact @GlobalTheory.RealLift.QuadFock.quad_fock | exact GlobalTheory.RealLift.QuadFock.quad_fock | (intros; apply GlobalTheory.RealLift.QuadFock.quad_fock <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviHom

open Matrix GlobalTheory.LeviElem

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem levi_mul_cols {σ : E →ₐ[F] E} {b : ℕ} {W : Spc F E (b + 2)} {W₁ : Spc F E b}
    (H : Plane E (b + 2) b) (l : (AE F E)ˣ) (g₀ : UA σ W₁.J) (h : UA σ W.J) (hL : IsLevi H l g₀ h) :
    mat h * fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) =
      fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) * blk (mat g₀) l.1 (cA σ (l⁻¹).1) := by
  obtain ⟨hx, hy, hι⟩ := hL
  rw [mul_fromCols, blk, fromCols_mul_fromBlocks]
  simp only [Matrix.mul_zero, add_zero, zero_add]
  refine congrArg₂ fromCols hι ?_
  ext i k
  rw [mul_diagonal]
  fin_cases k
  · have := congrFun hx i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp [cols2, Matrix.mul_apply]
    first | (rw [this]; ring) | (rw [mul_comm (incV F H.x i), ← this]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _)
  · have := congrFun hy i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp [cols2, Matrix.mul_apply]
    first | (rw [this]; ring) | (rw [mul_comm (incV F H.y i), ← this]; done) | (rw [mul_comm (incV F H.y i), ← this]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _)

theorem isLevi_mul {σ : E →ₐ[F] E} {b : ℕ} {W : Spc F E (b + 2)} {W₁ : Spc F E b} (H : Plane E (b + 2) b)
    {l l' : (AE F E)ˣ} {g₀ g₀' : UA σ W₁.J} {h h' : UA σ W.J} (hL : IsLevi H l g₀ h) (hL' : IsLevi H l' g₀' h') :
    IsLevi H (l * l') (g₀ * g₀') (h * h') := by
  obtain ⟨hx, hy, hι⟩ := hL
  obtain ⟨hx', hy', hι'⟩ := hL'
  have hm : ∀ (A B : UA σ W.J), mat (A * B) = mat A * mat B := fun _ _ => rfl
  have hm₁ : ∀ (A B : UA σ W₁.J), mat (A * B) = mat A * mat B := fun _ _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hm, ← mulVec_mulVec, hx', mulVec_smul, hx, smul_smul, Units.val_mul, mul_comm]
  · rw [hm, ← mulVec_mulVec, hy', mulVec_smul, hy, smul_smul, _root_.mul_inv_rev, Units.val_mul, map_mul]
  · rw [hm, hm₁, Matrix.mul_assoc, hι', ← Matrix.mul_assoc, hι, Matrix.mul_assoc]

theorem levi_hom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ m : (AE F E)ˣ → UA σ G₁.V.J → UA σ G.V.J, (∀ l g₀, IsLevi H l g₀ (m l g₀)) →
    (∀ l l' g₀ g₀', m (l * l') (g₀ * g₀') = m l g₀ * m l' g₀') ∧ Continuous (fun x : (AE F E)ˣ × UA σ G₁.V.J => m x.1 x.2) := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC hB hG hG₁ m hm
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ z, σ (σ z) = z := fun z => (B.emb w).1.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have hdet : G₁.V.J.det ≠ 0 := by
    have h := det_ne_of_sig _ (hG₁.hV.sig w)
    intro h0
    apply h
    have : (G₁.V.J.map (B.emb w).1).det = (B.emb w).1 G₁.V.J.det := (RingHom.map_det (B.emb w).1 _).symm
    rw [this, h0, map_zero]
  set P := fromCols H.ι (cols2 H.x H.y) with hP
  have hK : Pᵀ * G.V.J * P.map σ = fromBlocks G₁.V.J 0 0 swap2 := gram_block σ hσ B hG.hV.herm hC.hH
  set K : Matrix (Fin b ⊕ Fin 2) (Fin b ⊕ Fin 2) E := fromBlocks G₁.V.J 0 0 swap2 with hKdef
  have hKdet : IsUnit Kᵀ.det := by
    rw [det_transpose, hKdef, det_fromBlocks_zero₂₁]
    simp [swap2, det_fin_two, hdet]
  set Q := (Kᵀ)⁻¹ * ((P.map σ)ᵀ * G.V.Jᵀ) with hQ
  have hQP : Q * P = 1 := by
    have : (P.map σ)ᵀ * G.V.Jᵀ * P = Kᵀ := by
      rw [← hK]; simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [hQ, Matrix.mul_assoc, this, nonsing_inv_mul _ hKdet]
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  set PA := fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) with hPA
  have hPf : P.map f = PA := by
    ext i (j | j)
    · rfl
    · fin_cases j <;> rfl
  have hQP' : Q.map f * PA = 1 := by
    rw [← hPf, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero f) (map_one f)]
  have hPQ' : PA * Q.map f = 1 := (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 hQP'
  set QA := Q.map f

  have hform : ∀ (l : (AE F E)ˣ) (g₀ : UA σ G₁.V.J) (h : UA σ G.V.J), IsLevi H l g₀ h → mat h = PA * blk (mat g₀) l.1 (cA σ (l⁻¹).1) * QA := by
    intro l g₀ h hL
    rw [← levi_mul_cols H l g₀ h hL, Matrix.mul_assoc, hPQ', Matrix.mul_one]
  have huniq : ∀ (l : (AE F E)ˣ) (g₀ : UA σ G₁.V.J) (h h' : UA σ G.V.J), IsLevi H l g₀ h → IsLevi H l g₀ h' → h = h' := by
    intro l g₀ h h' hL hL'
    have e : mat h = mat h' := by rw [hform l g₀ h hL, hform l g₀ h' hL']
    exact Subtype.ext (Units.ext e)
  have hmul : ∀ l l' g₀ g₀', m (l * l') (g₀ * g₀') = m l g₀ * m l' g₀' := fun l l' g₀ g₀' =>
    huniq _ _ _ _ (hm _ _) (isLevi_mul H (hm l g₀) (hm l' g₀'))
  refine ⟨hmul, ?_⟩
  have m11 : m 1 1 = 1 := by
    have := hmul 1 1 1 1
    simp only [mul_one] at this
    exact (mul_eq_left.1 this.symm)
  have hinv : ∀ l g₀, (m l g₀)⁻¹ = m l⁻¹ g₀⁻¹ := fun l g₀ =>
    inv_eq_of_mul_eq_one_right (by rw [← hmul, mul_inv_cancel, mul_inv_cancel, m11])
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hcA : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hmat : ∀ {n : ℕ} {J : Matrix (Fin n) (Fin n) E}, Continuous fun g : UA σ J => mat g :=
    Units.continuous_val.comp continuous_subtype_val
  have hvec : Continuous fun x : (AE F E)ˣ × UA σ G₁.V.J => ![x.1.1, cA σ (x.1⁻¹).1] := by
    refine continuous_pi fun k => ?_
    fin_cases k
    · exact Units.continuous_val.comp continuous_fst
    · exact hcA.comp (Units.continuous_coe_inv.comp continuous_fst)
  have hval : Continuous fun x : (AE F E)ˣ × UA σ G₁.V.J => mat (m x.1 x.2) := by
    have : (fun x : (AE F E)ˣ × UA σ G₁.V.J => mat (m x.1 x.2)) =
        fun x => PA * blk (mat x.2) x.1.1 (cA σ (x.1⁻¹).1) * QA := funext fun x => hform _ _ _ (hm _ _)
    rw [this]
    refine (continuous_const.matrix_mul ?_).matrix_mul continuous_const
    exact Continuous.matrix_fromBlocks (hmat.comp continuous_snd) continuous_const continuous_const
      (Continuous.matrix_diagonal hvec)
  have hGL : Continuous fun x : (AE F E)ˣ × UA σ G₁.V.J => ((m x.1 x.2 : UA σ G.V.J) : GL (Fin (b + 2)) (AE F E)) := by
    refine Units.continuous_iff.2 ⟨hval, ?_⟩
    have : (fun x : (AE F E)ˣ × UA σ G₁.V.J => ((((m x.1 x.2 : UA σ G.V.J) : GL (Fin (b + 2)) (AE F E))⁻¹ :
        GL (Fin (b + 2)) (AE F E)) : Matrix (Fin (b + 2)) (Fin (b + 2)) (AE F E))) =
        (fun x : (AE F E)ˣ × UA σ G₁.V.J => mat (m x.1 x.2)) ∘ fun x => (x.1⁻¹, x.2⁻¹) := by
      funext x
      simp only [Function.comp_apply, ← hinv]
      rfl
    rw [this]
    exact hval.comp ((continuous_inv.comp continuous_fst).prodMk (continuous_inv.comp continuous_snd))
  exact continuous_induced_rng.2 hGL

end GlobalTheory.LeviHom
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.HermLB

namespace GlobalTheory.ArInt

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ} {ι : Type} [Fintype ι]

theorem mixed_eq_of_icls (hX : IsArithVar p D) {T M N : HermLB p} {L : ι → HermLB p}
    {Ψ : MvPolynomial (Option (Option ι)) ℝ →ₗ[ℝ] ℝ}
    (hΨ : IsArFun (fun o : Option (Option ι) => o.elim T fun o => o.elim M L) D Ψ) (a b : ℤ)
    (hN : N.icls = b • T.icls + a • M.icls) {Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ}
    (hΦ : IsArFun (fun o : Option ι => o.elim N L) D Φ) (n : ι → ℤ) :
    Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) =
      b * Ψ (MvPolynomial.X none * rename (some ∘ some) (lin fun i => (n i : ℝ)) ^ D) +
      a * Ψ (MvPolynomial.X (some none) * rename (some ∘ some) (lin fun i => (n i : ℝ)) ^ D) := by
  classical
  let A : Option ι → Option (Option ι) → ℤ := fun j => j.elim (fun o => o.elim b fun o => o.elim a 0)
    fun i => Pi.single (some (some i)) 1
  have h := ((Published.arIso_holds k X p D hX).2 _ _ Ψ hΨ).2.2 (Option ι) (fun o : Option ι => o.elim N L) A (by
    rintro (_ | i)
    · exact icls_eq_iff.1 (by simp [A, icls_comb, Fintype.sum_option, hN])
    · exact isometric_comb_single _ (some (some i)))
  have e₀ : (lin fun i => (A none i : ℝ)) = (b : ℝ) • MvPolynomial.X none + (a : ℝ) • MvPolynomial.X (some none) := by
    simp [A, lin, Fintype.sum_option, smul_eq_C_mul]
  have e₁ (i : ι) : (lin fun j => (A (some i) j : ℝ)) = MvPolynomial.X (some (some i)) := lin_single _
  have e₂ : aeval (fun j => lin fun i => (A j i : ℝ)) (rename some (lin fun i => (n i : ℝ))) =
      rename (some ∘ some) (lin fun i => (n i : ℝ)) := by
    conv_lhs => rw [aeval_rename]
    simp only [Function.comp_def, e₁]
    rw [rename_eq_aeval]
    rfl
  rw [Model.isArFun_unique hX hΦ h, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, map_pow, e₂, aeval_X, e₀,
    add_mul, smul_mul_assoc, smul_mul_assoc, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

end GlobalTheory.ArInt

namespace GlobalTheory.Published

theorem arMetric_of_arMix : ArExists → ArMix → ArMetric := by
  intro HE H k _ X _ p D hX ι _ M L u hu hc Φ Φ' hΦ hΦ' n
  obtain ⟨Ψ, hΨ⟩ := ((HE k X p D hX).2 _
    fun o : Option (Option ι) => o.elim (ArInt.fnB u hu hc) fun o => o.elim M L).1
  obtain ⟨Θ, hΘ⟩ := ((HE k X p D hX).2 _ fun o : Option ι => o.elim (ArInt.fnB u hu hc) L).1
  obtain ⟨h₁, h₂⟩ := H.fnB HE hX hΘ n
  refine ⟨h₁, ?_⟩
  rw [← h₂, mixed_eq_of_icls hX hΨ 1 0 (by simp) hΦ, mixed_eq_of_icls hX hΨ 0 1 (by simp) hΘ,
    mixed_eq_of_icls hX hΨ 1 1 (by
      rw [← icls_eq_iff.2 (isometric_tens_fnB M u hu hc), icls_tens, one_smul, one_smul, add_comm]) hΦ']
  push_cast
  ring

end GlobalTheory.Published
end
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.gaussIntegral_normForm_nonNorm_cancel : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (t : Fˣ), t ∉ (Units.map (Algebra.norm F : E →* F)).range → ∃ s₀ : Fˣ, ∀ s : Fˣ, (s₀ : F) ∈ GlobalTheory.SplitWeil.cball s → (∫ z in {z : E | Algebra.norm F z ∈ GlobalTheory.SplitWeil.cball s}, ψ (Algebra.norm F z) ∂μ) + (nabs F t : ℂ) * ∫ z in {z : E | (t : F) * Algebra.norm F z ∈ GlobalTheory.SplitWeil.cball s}, ψ ((t : F) * Algebra.norm F z) ∂μ = 0 := by
  first | exact @GlobalTheory.KSp.Cancel.gauss_cancel | exact GlobalTheory.KSp.Cancel.gauss_cancel | (intros; apply GlobalTheory.KSp.Cancel.gauss_cancel <;> assumption)
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory

theorem finset_prod_eq_one_of_le_one_eq_one {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (f : ι → Γ) (hle : ∀ i ∈ s, f i ≤ 1)
    (hprod : ∏ i ∈ s, f i = 1) : ∀ i ∈ s, f i = 1 := by
  intro i hi
  refine le_antisymm (hle i hi) ?_
  rw [← Finset.mul_prod_erase s f hi] at hprod
  have h2 : ∏ j ∈ s.erase i, f j ≤ 1 :=
    Finset.prod_le_one' (fun j hj => hle j (Finset.mem_of_mem_erase hj))
  calc (1 : Γ) = f i * ∏ j ∈ s.erase i, f j := hprod.symm
    _ ≤ f i := mul_le_of_le_one_right' h2

theorem valuation_derivWeierstrassP_torsion_odd :
    ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 →
      V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → Odd N →
      ∀ z, z ∉ L.lattice → (N : ℂ) * z ∈ L.lattice →
        V.valuation (L.derivWeierstrassP z) = V.valuation u ^ 3 := by
  intro L β u V N hβ hβim hu hN hodd z hz hNz
  classical
  have hN0 : (N : ℂ) ≠ 0 := by
    have : N ≠ 0 := by rintro rfl; exact absurd hodd (by decide)
    exact_mod_cast this
  have hstab : MulStable L (N : ℂ) := by
    intro ω hω
    have := L.lattice.smul_mem (N : ℤ) hω
    simpa [zsmul_eq_mul] using this
  have hΔ := latticeCurve_Δ_ne_zero L
  have hvΔ : V.valuation (latticeCurve L).Δ ≠ 0 := by
    simpa using hΔ
  have hu0 : u ≠ 0 := by
    rintro rfl
    apply hvΔ
    rw [← hu]; simp
  have hvu : V.valuation u ≠ 0 := by simpa using hu0
  obtain ⟨S, hS⟩ := kerRepsExist L (N : ℂ) hN0 hstab
  have hcard := kerRepsCard L (N : ℂ) S hN0 hstab hS
  have hcardN : S.card + 1 = N * N := by
    have : ((S.card + 1 : ℕ) : ℝ) = ((N * N : ℕ) : ℝ) := by
      push_cast; rw [hcard]; simp [Complex.normSq_apply]
    exact_mod_cast this
  have heven : Even S.card := by
    have hodd2 : Odd (N * N) := hodd.mul hodd
    rw [← hcardN] at hodd2
    obtain ⟨k, hk⟩ := hodd2
    exact ⟨k, by omega⟩
  have hpf := GlobalTheory.T.prod_derivWeierstrassP_kerReps_pow_four_mul' L (N : ℂ) S hN0 hstab hS heven
  have hmem : ∀ t ∈ S, V.valuation (L.derivWeierstrassP t / u ^ 3) ≤ 1 := by
    intro t ht
    rw [ValuationSubring.valuation_le_one_iff]
    exact (GlobalTheory.T.torsion_weierstrassP_mem_valuationSubring L β u V N hβ hβim hu hN t t (hS.1 t ht).2 (hS.1 t ht).2 (hS.1 t ht).1
      (hS.1 t ht).1).1
  have hprod : ∏ t ∈ S, V.valuation (L.derivWeierstrassP t / u ^ 3) ^ 4 = 1 := by
    have hv := congrArg V.valuation hpf
    simp only [map_mul, map_pow, map_prod, hN, one_pow, mul_one] at hv
    simp only [map_div₀, map_pow, div_pow, Finset.prod_div_distrib, Finset.prod_pow,
      Finset.prod_const, ← pow_mul]
    rw [hv, ← hu, ← pow_mul, div_eq_one_iff_eq (pow_ne_zero _ hvu)]
    ring_nf
  have hall := finset_prod_eq_one_of_le_one_eq_one S _ (fun t ht => pow_le_one' (hmem t ht) 4) hprod
  obtain ⟨t, ht, hzt⟩ := hS.2.2 z (by simpa [mul_comm] using hNz) hz
  have hper : L.derivWeierstrassP z = L.derivWeierstrassP t := by
    have := L.derivWeierstrassP_add_coe t ⟨z - t, hzt⟩
    simpa using this
  have h1 : V.valuation (L.derivWeierstrassP t / u ^ 3) = 1 := by
    have h4 := hall t ht
    by_contra hne
    have hlt : V.valuation (L.derivWeierstrassP t / u ^ 3) < 1 := lt_of_le_of_ne (hmem t ht) hne
    exact absurd h4 (ne_of_lt (pow_lt_one' hlt (by norm_num)))
  rw [hper]
  rw [map_div₀, map_pow, div_eq_one_iff_eq (pow_ne_zero _ hvu)] at h1
  exact h1
end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory

theorem isArithVar_charZero_functionField_and_injective :
    ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
      IsArithVar p D → CharZero X.functionField ∧ Function.Injective (GlobalTheory.toFunctionField p) := by
  intro k _ X _ p D h
  have hΓ : CharZero Γ(X, ⊤) := h.charZero
  have hg : Function.Injective (X.presheaf.germ ⊤ (genericPoint X) trivial).hom :=
    germ_injective_of_isIntegral X _ _
  have hK : CharZero X.functionField := (RingHom.charZero_iff hg).1 hΓ
  refine ⟨hK, ?_⟩
  have := h.isDomain
  have := h.finite
  have hint : Algebra.IsIntegral ℤ k := inferInstance
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  have hker : RingHom.ker (GlobalTheory.toFunctionField p) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap, RingHom.mem_ker, algebraMap_int_eq, eq_intCast, map_intCast, Int.cast_eq_zero] at hn
    simp [hn]
  have : a ∈ RingHom.ker (GlobalTheory.toFunctionField p) := ha
  rw [hker] at this
  exact this

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem _root_.GlobalTheory.T.exists_eval_regular_functions_at_fieldPoint : ∀ (F : Type) [Field F] (Y : Var F) (Z : Scheme.{0}) [IsIntegral Z] (k : Type) [Field k] (w : Sp k ⟶ Z), ∃ ev : (algebraMap (Z.presheaf.stalk (w (IsLocalRing.closedPoint k))) Z.functionField).range →+* k, (∀ u, ev u ≠ 0 ↔ UnitAt (w (IsLocalRing.closedPoint k)) (u : Z.functionField)) ∧ ∀ (q : Z ⟶ Y.X) [IsDominant q] (u : Y.Fn), RegAt (q (w (IsLocalRing.closedPoint k))) u → ∃ h, ev ⟨functionFieldMap q u, h⟩ = (ratOf Y).val (w ≫ q) u := by
  first | exact @GlobalTheory.FlagPush.exists_eval_regular_at_fieldPoint | exact GlobalTheory.FlagPush.exists_eval_regular_at_fieldPoint | (intros; apply GlobalTheory.FlagPush.exists_eval_regular_at_fieldPoint <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem _root_.GlobalTheory.T.flag_of_dominant_point_as_triangular_matrix : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ B ∈ E'.S (genericPoint Y.X), ∀ A ∈ E.S (f (genericPoint Y.X)), ∀ (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K) (U : Mat m K), spMap ψ₁ ≫ (ratOf Y).pt ≫ f = spMap ψ₂ ≫ (ratOf Y).pt ≫ f → Bears E' φ A (U * (B * (A.map φ)⁻¹).map ψ₁) (spMap ψ₂ ≫ (ratOf Y).pt) → (∀ u : X.Fn, ψ₁ (φ u) = ψ₂ (φ u)) ∧ Par m ⊤ (U * (B.map ψ₁ * (B.map ψ₂)⁻¹)) := by
  first | exact @GlobalTheory.FlagPush.flag_conv | exact GlobalTheory.FlagPush.flag_conv | (intros; apply GlobalTheory.FlagPush.flag_conv <;> assumption)
end
