module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceBasisHyperbolicPlaneComplement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqNormCompletionTensorOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialOfLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftStandardCharacterIndefinite
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.exists_diagonalLagrangian_invariant_form : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (κ : Type) [Fintype κ], ∃ l : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] ℂ, l ∈ (adeleClass F).adm (κ ⊕ κ) ∧ (∀ (x y : κ → AF F), ∀ φ ∈ schA F (κ ⊕ κ), l (schr ψ (Sum.elim x x, Sum.elim y (-y)) φ) = l φ) ∧ ∃ φ ∈ schA F (κ ⊕ κ), l φ ≠ 0 := by
  first | exact @GlobalTheory.diagLagrangian_form | exact GlobalTheory.diagLagrangian_form | (intros; apply GlobalTheory.diagLagrangian_form <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU


theorem _root_.GlobalTheory.T.exists_splitPlace_basis_hyperbolicPlane_complement : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (τ : E →ₐ[F] v.adicCompletion F) (n n₁ : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E)
    (β₁ : GL (Fin n₁) (v.adicCompletion F)) (i₀ i₁ : ℕ), n = n₁ + 2 → i₀ < i₁ → i₁ < n → L.IsFullLattice E →
    (∀ z ∈ L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ L ∧ t • y ∈ L ∧ ι *ᵥ u ∈ L ∧ z = s • x + ι *ᵥ u + t • y) →
    ((∀ c : E, c • x ∈ L → Valued.v (τ c) ≤ 1) ∧ ∃ c : E, c • x ∈ L ∧ Valued.v (τ c) = 1) →
    ((∀ c : E, c • y ∈ L → Valued.v (τ c) ≤ 1) ∧ ∃ c : E, c • y ∈ L ∧ Valued.v (τ c) = 1) →
    IsSplitBasis τ (L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))) β₁ →
    ∃ β : GL (Fin n) (v.adicCompletion F), (∀ i : Fin n, (i.1 = i₀ → ∀ r, β.1 r i = τ (x r)) ∧
      (i.1 = i₁ → ∀ r, β.1 r i = τ (y r)) ∧ ∀ j : Fin n₁, i.1 = skip i₀ i₁ j → ∀ r, β.1 r i = (ι.map τ * β₁.1) r j) ∧
      IsSplitBasis τ L β := by
  first | exact @GlobalTheory.PlaneBasis.exists_isSplitBasis_plane | exact GlobalTheory.PlaneBasis.exists_isSplitBasis_plane | (intros; apply GlobalTheory.PlaneBasis.exists_isSplitBasis_plane <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.unit_eq_norm_completionTensor_of_isInertAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → IsField (Fv F v ⊗[F] E) →
    ∀ u : Fv F v, Valued.v u = 1 →
      ∃ z : Fv F v ⊗[F] E, algebraMap (Fv F v) (Fv F v ⊗[F] E) u = z * Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ z := by
  first | exact @GlobalTheory.InertUnitNorm.unit_eq_mul_conj | exact GlobalTheory.InertUnitNorm.unit_eq_mul_conj | (intros; apply GlobalTheory.InertUnitNorm.unit_eq_mul_conj <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
open Filter Topology

theorem _root_.GlobalTheory.T.exists_idempotentCutoff_tendsto_adelicUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {ι : Type} [Fintype ι] [DecidableEq ι] (J₀ : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (g : UG (cA σ) J₀), ∃ q : Finset (HeightOneSpectrum (𝓞 F)) → UG (cA σ) J₀, (∀ S, ((q S).1.1 : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LocalGlobalChar.eps S) • (g.1.1 : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + (1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LocalGlobalChar.eps S)) • (1 : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) ∧ Tendsto q atTop (𝓝 g) := by
  first | exact @GlobalTheory.UnitaryCutoff.exists_approx | exact GlobalTheory.UnitaryCutoff.exists_approx | (intros; apply GlobalTheory.UnitaryCutoff.exists_approx <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
open Filter Topology

theorem _root_.GlobalTheory.T.exists_rationalPoint_polynomial_idempotentUnit_value : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (S : Finset (HeightOneSpectrum (𝓞 F))) (ψ : Polynomial (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), (∀ (Ω : Type) [Field Ω] (φ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Ω), φ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LocalGlobalChar.eps S)) = 1 → ψ.map φ ≠ 0) → ∃ t : F, IsUnit (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LocalGlobalChar.eps S) * ψ.eval (algebraMap F (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) t) + (1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LocalGlobalChar.eps S))) := by
  first | exact @GlobalTheory.DenseAvoid.exists_unit_eval | exact GlobalTheory.DenseAvoid.exists_unit_eval | (intros; apply GlobalTheory.DenseAvoid.exists_unit_eval <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.ChrWUnif

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local instance locField (v : Pl F) : IsNonarchimedeanLocalField (Fv F v) := GlobalTheory.LocalData.isLocalField v

theorem valued_unifAt (v : Pl F) : Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) = WithZero.exp (-1 : ℤ) := by
  haveI : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have e := ValuativeRel.isEquiv (valuation (Fv F v)) (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ)))
  have hu : valuation (Fv F v) ((unifAt v : (Fv F v)ˣ) : Fv F v) = uniformizer (Fv F v) :=
    (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hπv : Valued.v ((π : F) : Fv F v) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hlt : Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) < 1 :=
    e.lt_one_iff_lt_one.1 (hu ▸ uniformizer_lt_one)
  have h0 : Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) ≠ 0 := by simp
  have hle1 : valuation (Fv F v) ((π : F) : Fv F v) ≤ valuation (Fv F v) ((unifAt v : (Fv F v)ˣ) : Fv F v) := by
    rw [hu, le_uniformizer_iff]
    exact e.lt_one_iff_lt_one.2 (by rw [hπv, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  have hge : WithZero.exp (-1 : ℤ) ≤ Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) := hπv ▸ (e _ _).1 hle1
  rw [← WithZero.exp_log h0] at hlt hge ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  rw [WithZero.exp_le_exp] at hge
  congr 1
  omega

theorem chrW_unifAt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : Chr F E)
    (v : Pl F) (t : E →ₐ[F] Fv F v) (h : UnrAt χ (splitPrime t)) : chrW χ t (unifAt v) = val χ (splitPrime t) := by
  refine h.locChar_eq_val ?_
  show Valued.v (complMap (splitPrime_under t) ((unifAt v : (Fv F v)ˣ) : Fv F v)) = WithZero.exp (-1 : ℤ)
  rw [GlobalTheory.LFun.SplitTie.valued_complMap t (splitPrime_under t), valued_unifAt]

end GlobalTheory.ChrWUnif
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.WeilPairPartnerF

theorem pair_partnerF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (a : UG (cA σ) (incM F JA)) (b : UG (cA σ) (incM F JB)),
          ∃ (g : GAF σ JS) (h : GAF σ JT), mtF σ JT h = a.1.1 ∧ mtF σ JS g = (b⁻¹).1.1ᵀ := by
  intro F E _ _ _ _ _ σ B _ _ nS nT JS JT hS _ ξ₀ hξ₀ _ JA JB ξ hA hB a b
  have hmap : ∀ {m n : Type} (X : Matrix m n (AF F ⊗[F] E)),
      X.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) = X.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) :=
    fun X => Matrix.ext fun i j => rfl

  have ha : (a.1.val)ᵀ * incM F JA * (a.1.val).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) = incM F JA := a.2
  set A : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E) := a.1.val with hAdef
  have hJA : incM F JA = (incM F JT)ᵀ := by
    rw [hA]; rfl
  rw [hJA] at ha
  have ha' := congrArg Matrix.transpose ha
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] at ha'
  have hmemA : a.1 ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF F) σ JT := by
    show Formalism.UG.cT _ a.1.val * _ * a.1.val = _
    simp only [Formalism.UG.cT, hmap]
    rw [Matrix.mul_assoc]
    exact ha'

  obtain ⟨cR, hcR⟩ : ∃ f, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ = f := ⟨_, rfl⟩
  have hb : (b.1.val)ᵀ * incM F JB * (b.1.val).map cR = incM F JB := by
    rw [← hcR, hmap]; exact b.2
  have hBB : b.1.val * (b⁻¹).1.val = 1 := by
    rw [Subgroup.coe_inv]; exact (b.1).mul_inv
  have hBB' : (b⁻¹).1.val * b.1.val = 1 := by
    rw [Subgroup.coe_inv]; exact (b.1).inv_mul
  obtain ⟨Bm, hBdef⟩ : ∃ M : Matrix (Fin nS) (Fin nS) (AF F ⊗[F] E), b.1.val = M := ⟨_, rfl⟩
  obtain ⟨Bi, hBidef⟩ : ∃ M : Matrix (Fin nS) (Fin nS) (AF F ⊗[F] E), (b⁻¹).1.val = M := ⟨_, rfl⟩
  rw [hBdef] at hb hBB hBB'
  rw [hBidef] at hBB hBB'
  have hdet : JS.det ≠ 0 := hS.2
  have hGN := GlobalTheory.WeilPairPartner.map_mul_map_inv (inclR (F := F) (E := E) (AF F)) JS hdet
  have hNG := GlobalTheory.WeilPairPartner.map_inv_mul_map (inclR (F := F) (E := E) (AF F)) JS hdet
  have hsm : incM F (ξ₀ • JS⁻¹) = inclR (F := F) (AF F) ξ₀ • incM F JS⁻¹ :=
    GlobalTheory.WeilPairPartner.map_smul_eq _ _ _
  have hu : IsUnit (inclR (F := F) (E := E) (AF F) ξ₀) :=
    (isUnit_iff_ne_zero.mpr hξ₀).map _
  have hcore := GlobalTheory.WeilPairPartner.conj_inv_transpose cR ξ _ hu Bm Bi (incM F JB) (incM F JS)
    (incM F JS⁻¹) hb hBB hBB' (hB.trans hsm) hGN hNG
  have hTT : Biᵀ * Bmᵀ = 1 := by
    rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one]
  let gU : GL (Fin nS) (AF F ⊗[F] E) :=
    ⟨Biᵀ, Bmᵀ, hTT, by rw [← Matrix.transpose_mul, hBB', Matrix.transpose_one]⟩
  have hmemB : gU ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF F) σ JS := by
    show Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) Biᵀ * incM F JS * Biᵀ = incM F JS
    rw [hcR]
    simp only [Formalism.UG.cT, Matrix.transpose_map, Matrix.transpose_transpose]
    exact hcore
  refine ⟨⟨gU, hmemB⟩, ⟨a.1, hmemA⟩, rfl, ?_⟩
  show Biᵀ = ((b⁻¹).1.val)ᵀ
  rw [hBidef]

end GlobalTheory.WeilPairPartnerF
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

theorem _root_.GlobalTheory.T.deriv_heisenbergCM_theta_quasiInvariant_rational : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ (γ : Matrix (Fin nT) (Fin nS) E) (w : Formalism.IndefR.DatumF.WOF F E nS nT),
      deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (Formalism.IndefR.DatumF.ratWF γ + w)) 0 = B.ψ (-(Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) w)) * deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w)) 0 := by
  first | exact @GlobalTheory.ThetaDerivQuasi.deriv_heis_quasi | exact GlobalTheory.ThetaDerivQuasi.deriv_heis_quasi | (intros; apply GlobalTheory.ThetaDerivQuasi.deriv_heis_quasi <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

theorem _root_.GlobalTheory.T.deriv_heisenbergCM_real_line_finite_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ u : Formalism.IndefR.DatumF.WOF F E nS nT, u.map (Formalism.IndefR.DatumF.infPartF F E) = 0 → Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (u) f = f →
      Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (u) (fun w => deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w)) 0) = fun w => deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w)) 0 := by
  first | exact @GlobalTheory.HeisDerivCM.heisOF_deriv_fix | exact GlobalTheory.HeisDerivCM.heisOF_deriv_fix | (intros; apply GlobalTheory.HeisDerivCM.heisOF_deriv_fix <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

theorem _root_.GlobalTheory.T.heisenbergOp_realLine_add_eq_phase_mul_shifted : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ (f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ) (w : Formalism.IndefR.DatumF.WOF F E nS nT) (s t : ℝ),
      Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L (s + t)) f w = B.ψ (Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ w (L s)) * Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L s) := by
  first | exact @GlobalTheory.heisOF_line_add | exact GlobalTheory.heisOF_line_add | (intros; apply GlobalTheory.heisOF_line_add <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

theorem _root_.GlobalTheory.T.differentiableAt_zero_heisenbergCM_real_line_theta : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ w : Formalism.IndefR.DatumF.WOF F E nS nT, DifferentiableAt ℝ (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f w) 0 := by
  first | exact @GlobalTheory.HeisLineDiffF.differentiableAt_heisOF_line | exact GlobalTheory.HeisLineDiffF.differentiableAt_heisOF_line | (intros; apply GlobalTheory.HeisLineDiffF.differentiableAt_heisOF_line <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

theorem _root_.GlobalTheory.T.theta_lift_standard_character_indefinite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ g : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ,
      (∃ U : AddSubgroup (Formalism.IndefR.DatumF.WOF F E nS nT), IsOpen (U : Set (Formalism.IndefR.DatumF.WOF F E nS nT)) ∧
        ∀ u ∈ U, u.map (Formalism.IndefR.DatumF.infPartF F E) = 0 → Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (u) g = g) →
      (∀ (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.DatumF.WOF F E nS nT), Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
        ∀ w : Formalism.IndefR.DatumF.WOF F E nS nT, ContDiff ℝ ∞ fun x => g (w + L x)) →
      Continuous g := by
  first | exact @GlobalTheory.WeilContF.continuous_of_level_real | exact GlobalTheory.WeilContF.continuous_of_level_real | (intros; apply GlobalTheory.WeilContF.continuous_of_level_real <;> assumption)
end
