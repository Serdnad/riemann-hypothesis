module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle381
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle099
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEmbeddingStabilizer
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1096
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle462
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle386
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMixedLagrangianChartIntegralRowChange
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorIsotropicTranslationCharSplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PackFrame

open GlobalTheory.PackLoc

section Lin

variable {m N : ℕ} (e : Option (Fin m) ≃ Fin N)

theorem embOpt_mul (h k : Matrix (Fin m) (Fin m) ℂ) : embOpt e (h * k) = embOpt e h * embOpt e k := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  rw [Matrix.mul_apply, ← e.sum_comp, Fintype.sum_option]
  cases a <;> cases b <;> simp [embOpt, Matrix.mul_apply]

theorem embOpt_ct (h : Matrix (Fin m) (Fin m) ℂ) : embOpt e hᴴ = (embOpt e h)ᴴ := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  cases a <;> cases b <;> simp [embOpt]

theorem embOpt_Jm {εA : Fin m → Bool} {ε : Fin N → Bool} (h0 : ε (e none) = true) (h1 : ∀ i, ε (e (some i)) = εA i) :
    Formalism.REAL.Jm ε = embOpt e (Formalism.REAL.Jm εA) := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  cases a <;> cases b <;> simp [embOpt, Formalism.REAL.Jm, Matrix.diagonal_apply, h0, h1]

theorem embOpt_unit {h : Matrix (Fin m) (Fin m) ℂ} (hh : IsUnit h) : IsUnit (embOpt e h) := by
  obtain ⟨k, hk⟩ := hh.exists_right_inv
  exact IsUnit.of_mul_eq_one (embOpt e k) (by rw [← embOpt_mul, hk, embOpt_one])

theorem embOpt_inv {h : Matrix (Fin m) (Fin m) ℂ} (hh : IsUnit h) : (embOpt e h)⁻¹ = embOpt e h⁻¹ :=
  Matrix.inv_eq_right_inv (by
    rw [← embOpt_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hh), embOpt_one])

theorem Jm_unit (ε : Fin m → Bool) : IsUnit (Formalism.REAL.Jm ε) := by
  refine IsUnit.of_mul_eq_one (Formalism.REAL.Jm ε) ?_
  rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext a; split_ifs <;> simp

def vecOpt (y : Fin m → ℂ) (a : ℂ) : Fin N → ℂ := fun b => (e.symm b).elim a y

theorem embOpt_vec (h : Matrix (Fin m) (Fin m) ℂ) (y : Fin m → ℂ) (a : ℂ) :
    embOpt e h *ᵥ vecOpt e y a = vecOpt e (h *ᵥ y) a := by
  funext b
  obtain ⟨b, rfl⟩ := e.surjective b
  rw [Matrix.mulVec, dotProduct, ← e.sum_comp, Fintype.sum_option]
  cases b <;> simp [embOpt, vecOpt, Matrix.mulVec, dotProduct]

theorem eu_vecOpt (y : Fin m → ℂ) (a : ℂ) : eu (vecOpt e y a) ^ 2 = eu y ^ 2 + ‖a‖ ^ 2 := by
  unfold eu
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), ← e.sum_comp, Fintype.sum_option, add_comm]
  simp [vecOpt]

theorem vecOpt_zero_one : vecOpt e 0 1 = Pi.single (e none) 1 := by
  funext b
  obtain ⟨b, rfl⟩ := e.surjective b
  cases b <;> simp [vecOpt, Pi.single_apply]

def colM (F : Matrix (Fin N) (Fin m) ℂ) (z : Matrix (Fin N) (Fin 1) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i b => (e.symm b).elim (z i 0) (F i)

variable (F : Matrix (Fin N) (Fin m) ℂ) (z : Matrix (Fin N) (Fin 1) ℂ)

theorem colM_vec (y : Fin m → ℂ) (a : ℂ) : colM e F z *ᵥ vecOpt e y a = F *ᵥ y + a • fun i => z i 0 := by
  funext i
  rw [Matrix.mulVec, dotProduct, ← e.sum_comp, Fintype.sum_option]
  simp [colM, vecOpt, Matrix.mulVec, dotProduct, add_comm, mul_comm]

theorem mul_colM (g : Matrix (Fin N) (Fin N) ℂ) : g * colM e F z = colM e (g * F) (g * z) := by
  ext i b
  obtain ⟨b, rfl⟩ := e.surjective b
  cases b <;> simp [colM, Matrix.mul_apply]

theorem colM_mul (h : Matrix (Fin m) (Fin m) ℂ) : colM e F z * embOpt e h = colM e (F * h) z := by
  ext i b
  obtain ⟨b, rfl⟩ := e.surjective b
  rw [Matrix.mul_apply, ← e.sum_comp, Fintype.sum_option]
  cases b <;> simp [colM, embOpt, Matrix.mul_apply]

theorem colM_gram (J : Matrix (Fin N) (Fin N) ℂ) (h1 : Fᴴ * J * z = 0) (h2 : zᴴ * J * F = 0) (h3 : zᴴ * J * z = 1) :
    (colM e F z)ᴴ * J * colM e F z = embOpt e (Fᴴ * J * F) := by
  rw [Matrix.mul_assoc] at h1 h2 h3 ⊢
  rw [Matrix.mul_assoc, mul_colM]
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  cases a with
  | none => cases b with
    | none => simpa [colM, embOpt, Matrix.mul_apply (M := _ᴴ)] using congrFun (congrFun h3 0) 0
    | some b => simpa [colM, embOpt, Matrix.mul_apply (M := _ᴴ)] using congrFun (congrFun h2 0) b
  | some a => cases b with
    | none => simpa [colM, embOpt, Matrix.mul_apply (M := _ᴴ)] using congrFun (congrFun h1 a) 0
    | some b => simp [colM, embOpt, Matrix.mul_apply (M := _ᴴ)]

theorem exists_frame (J : Matrix (Fin N) (Fin N) ℂ) (h1 : Fᴴ * J * z = 0) (h2 : zᴴ * J * F = 0) (h3 : zᴴ * J * z = 1)
    (εA : Fin m → Bool) (A : Matrix (Fin m) (Fin m) ℂ) (ε : Fin N → Bool) (hA : IsUnit A)
    (hG : Aᴴ * Formalism.REAL.Jm εA * A = Fᴴ * J * F) (h0 : ε (e none) = true) (hε : ∀ i, ε (e (some i)) = εA i) :
    ∃ B : Matrix (Fin N) (Fin N) ℂ, IsUnit B ∧ Bᴴ * Formalism.REAL.Jm ε * B = J ∧
      (∀ (y : Fin m → ℂ) (a : ℂ), eu (B *ᵥ (F *ᵥ y + a • fun i => z i 0)) ^ 2 = eu (A *ᵥ y) ^ 2 + ‖a‖ ^ 2) ∧
      B *ᵥ (fun i => z i 0) = Pi.single (e none) 1 ∧
      ∀ (g : Matrix (Fin N) (Fin N) ℂ) (h : Matrix (Fin m) (Fin m) ℂ), g * F = F * h → g * z = z →
        B * g * B⁻¹ = embOpt e (A * h * A⁻¹) := by
  set M := colM e F z with hM
  set C := embOpt e A with hC
  have hCu : IsUnit C := embOpt_unit e hA
  have hg : Mᴴ * J * M = Cᴴ * Formalism.REAL.Jm ε * C := by
    rw [hM, colM_gram e F z J h1 h2 h3, ← hG, embOpt_mul, embOpt_mul, embOpt_ct, embOpt_Jm e h0 hε]
  have hMu : IsUnit M := by
    have : IsUnit (Mᴴ * J * M) := by
      rw [hg]; exact (((Matrix.isUnit_conjTranspose _).2 hCu).mul (Jm_unit ε)).mul hCu
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at this
    exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right this)
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hMu
  have hMi : IsUnit M⁻¹ := Matrix.isUnit_nonsing_inv_iff.2 hMu
  have key : ∀ y a, (C * M⁻¹) *ᵥ (F *ᵥ y + a • fun i => z i 0) = vecOpt e (A *ᵥ y) a := by
    intro y a
    rw [← colM_vec e, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul_cancel_right _ _ hd, embOpt_vec]
  refine ⟨C * M⁻¹, hCu.mul hMi, ?_, fun y a => ?_, ?_, fun g h e1 e2 => ?_⟩
  · calc (C * M⁻¹)ᴴ * Formalism.REAL.Jm ε * (C * M⁻¹) = (M⁻¹)ᴴ * (Cᴴ * Formalism.REAL.Jm ε * C) * M⁻¹ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = (M * M⁻¹)ᴴ * J * (M * M⁻¹) := by
          rw [← hg, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Matrix.mul_nonsing_inv _ hd]; simp
  · rw [key, eu_vecOpt]
  · have := key 0 1
    simpa [vecOpt_zero_one] using this
  · have e3 : g * M = M * embOpt e h := by rw [hM, mul_colM, colM_mul, e1, e2]
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hd, embOpt_mul, embOpt_mul, ← embOpt_inv e hA, ← hC]
    calc C * M⁻¹ * g * (M * C⁻¹) = C * (M⁻¹ * (g * M)) * C⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [e3, Matrix.nonsing_inv_mul_cancel_left _ _ hd]

end Lin

variable {D : D7}

theorem map_cT_tau (τ : D.what₂.Tau) {m n : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E) :
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X).map (tauE D τ) = (X.map (tauE D τ))ᴴ := by
  ext a b
  exact GlobalTheory.FockCompare.tauE_star τ _

theorem map_incA_tau {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m n : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E) :
    (X.map (incA D)).map ((θ τ).comp (infPart D)) = X.map (tauE D τ) := by
  ext a b
  exact GlobalTheory.FockCompare.comp_incA hθ τ _

theorem exists_adapted_frame : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (τ : D.what₂.Tau)
  (εA : Fin Y.rank → Bool) (A : Matrix (Fin Y.rank) (Fin Y.rank) ℂ) (ε : Fin V.rank → Bool)
  (e : Option (Fin Y.rank) ≃ Fin V.rank),
  IsUnit A → Aᴴ * Formalism.REAL.Jm εA * A = gramAt D Y τ → ε (e none) = true → (∀ i, ε (e (some i)) = εA i) →
  ∃ B : Matrix (Fin V.rank) (Fin V.rank) ℂ, IsUnit B ∧ Bᴴ * Formalism.REAL.Jm ε * B = gramAt D V τ ∧
    (∀ (y : Fin Y.rank → ℂ) (a : ℂ),
      eu (B *ᵥ ((frameMat V Y d.ι).map (tauE D τ) *ᵥ y + a • fun i => tauE D τ (zv d i))) ^ 2 = eu (A *ᵥ y) ^ 2 + ‖a‖ ^ 2) ∧
    B *ᵥ (fun i => tauE D τ (zv d i)) = Pi.single (e none) 1 ∧
    (∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ), GlobalTheory.PackLoc.embAt θ d τ h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) ∧
    ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ), B * GlobalTheory.PackLoc.embAt θ d τ h * B⁻¹ = GlobalTheory.PackLoc.embOpt e (A * h * A⁻¹) := by
  intro D θ hθ Y V d τ εA A ε e hA hG h0 hε
  have h1 := congrArg (fun X => X.map (tauE D τ)) d.perp
  have h2 := congrArg (fun X => X.map (tauE D τ)) (GlobalTheory.UnitaryEmbeddingGroup.perp' d)
  have h3 := congrArg (fun X => X.map (tauE D τ)) d.gram
  have h4 := congrArg (fun X => X.map (tauE D τ)) (GlobalTheory.AutFunCounterexample.gram_pull V Y d.ι d.isom)
  simp only [Matrix.map_mul, map_cT_tau, Matrix.map_zero _ (map_zero _)] at h1 h2 h3 h4
  have h5 : (antiDiagonalSignGramMatrix 1 (1 : D.host.E)).map (tauE D τ) = 1 := by
    ext a b
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]; simp [antiDiagonalSignGramMatrix]
  rw [h5] at h3
  obtain ⟨B, b1, b2, b3, b4, b5⟩ := exists_frame e _ _ _ h1 h2 h3 εA A ε hA (hG.trans h4.symm) h0 hε
  refine ⟨B, b1, b2, b3, b4, fun h _ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V _ τ, fun h hh => b5 _ h ?_ ?_⟩
  · have k1 := congrArg (fun X => X.map ((θ τ).comp (infPart D))) ((embRel_iff d (atTau θ Y τ h) _).2 rfl).1
    have k2 := (GlobalTheory.PointAtPlaceHom.atTau_spec hθ Y τ hh).2.1
    simp only [Matrix.map_mul, map_incA_tau hθ] at k1
    rw [GlobalTheory.FockCompare.RealAction.infMat_eq] at k2
    exact k1.trans (congrArg _ k2)
  · have k1 := congrArg (fun X => X.map ((θ τ).comp (infPart D))) (GlobalTheory.UnitaryEmbeddingGroup.unitaryEmbedding_fixes_vectors d (atTau θ Y τ h))
    simp only [Matrix.map_mul, map_incA_tau hθ] at k1
    exact k1

end GlobalTheory.PackFrame

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.WeilConj

variable {D : D7}

theorem dag_dag {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (h : AdjLaw ψ T S) (f : WO T S → ℂ) :
    dag S T (dag T S f) = f := by
  funext y
  simp only [dag, Complex.conj_conj, h.invol y]

theorem dag_add (S T : HSp D) (f f' : WO S T → ℂ) : dag S T (f + f') = dag S T f + dag S T f' := by
  funext y; simp [dag]

theorem dag_smul (S T : HSp D) (c : ℂ) (f : WO S T → ℂ) : dag S T (c • f) = starRingEnd ℂ c • dag S T f := by
  funext y; simp [dag]

def conjE (S T : HSp D) (A : Module.End ℂ (WO S T → ℂ)) : Module.End ℂ (WO T S → ℂ) where
  toFun f := dag S T (A (dag T S f))
  map_add' f f' := by simp only [dag_add, map_add (f := _)]
  map_smul' c f := by simp only [dag_smul, map_smul, Complex.conj_conj, RingHom.id_apply]

def conjRep {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hST : AdjLaw ψ S T) (hTS : AdjLaw ψ T S) (ω : WRep S T) :
    WRep T S where
  toFun p := conjE S T (ω (p.2, p.1))
  map_one' := by
    apply LinearMap.ext; intro f
    show dag S T (ω 1 (dag T S f)) = f
    rw [map_one, Module.End.one_apply, dag_dag hTS]
  map_mul' p q := by
    apply LinearMap.ext; intro f
    show dag S T (ω ((p * q).2, (p * q).1) (dag T S f)) = dag S T (ω (p.2, p.1) (dag T S (dag S T (ω (q.2, q.1) (dag T S f)))))
    rw [dag_dag hST]
    have : ((p * q).2, (p * q).1) = (p.2, p.1) * (q.2, q.1) := rfl
    rw [this, map_mul, Module.End.mul_apply]

theorem conjRep_apply {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hST : AdjLaw ψ S T) (hTS : AdjLaw ψ T S)
    (ω : WRep S T) (h : GA D T) (g : GA D S) (f : WO T S → ℂ) :
    conjRep hST hTS ω (h, g) f = dag S T (ω (g, h) (dag T S f)) := rfl

theorem adjO_zero {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (h : AdjLaw ψ S T) : adjO S T 0 = 0 := by
  have := h.add 0 0
  rw [add_zero] at this
  simpa using this

theorem unit_transport {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hST : AdjLaw ψ S T) (hTS : AdjLaw ψ T S)
    (μ : Measure (WO T S)) (𝓕 : Set (WO T S)) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL S T) 𝓕 μ) :
    ∃ (μ' : Measure (WO S T)) (𝓕' : Set (WO S T)), μ'.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratL T S) 𝓕' μ' ∧
      ∀ G : WO S T → ENNReal, ∫⁻ w in 𝓕, G (adjO S T w) ∂μ = ∫⁻ v in 𝓕', G v ∂μ' := by
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.MixModel.lattice_Mx D S.rank T.rank
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : BorelSpace (WO T S) := ⟨rfl⟩
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  let eA : WO T S ≃+ WO S T :=
    { toFun := adjO S T
      invFun := adjO T S
      left_inv := fun x => hTS.invol x
      right_inv := fun y => hST.invol y
      map_add' := hST.add }
  let eH : WO T S ≃ₜ WO S T := ⟨eA.toEquiv, hST.cont, hTS.cont⟩
  let eM : WO T S ≃ᵐ WO S T := eH.toMeasurableEquiv
  have hHaar : (μ.map eM).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ eA hST.cont hTS.cont
  have hmp : MeasurePreserving eM μ (μ.map eM) := ⟨eM.measurable, rfl⟩
  have hmp' : MeasurePreserving eM.symm (μ.map eM) μ := MeasurePreserving.symm eM hmp
  let eG : ratL S T → ratL T S := fun g => ⟨adjO S T g, (hST.rat g).2 g.2⟩
  have hbij : Function.Bijective eG := by
    refine ⟨fun g g' hg => ?_, fun g => ⟨⟨adjO T S g, (hTS.rat g).2 g.2⟩, Subtype.ext (hST.invol g)⟩⟩
    have e := congrArg (fun x : ratL T S => adjO T S (x : WO S T)) hg
    simp only [eG, hTS.invol] at e
    exact Subtype.ext e
  have hF : IsAddFundamentalDomain (ratL T S) (eM.symm ⁻¹' 𝓕) (μ.map eM) := by
    refine h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hbij fun g x => ?_
    show adjO T S (adjO S T g + x) = (g : WO T S) + adjO T S x
    rw [hTS.add, hTS.invol]
  have hpre : eM ⁻¹' (eM.symm ⁻¹' 𝓕) = 𝓕 := by
    ext a; simp
  refine ⟨μ.map eM, eM.symm ⁻¹' 𝓕, hHaar, hF, fun G => ?_⟩
  symm
  rw [MeasurableEquiv.restrict_map, lintegral_map_equiv, hpre]
  rfl

theorem enorm_dag (S T : HSp D) (f : WO S T → ℂ) (y : WO T S) : ‖dag S T f y‖ₑ = ‖f (adjO S T y)‖ₑ := by
  simp only [dag]
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, Complex.norm_conj]

theorem isSplitIdem_cA {e : AE D} (he : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hε, h3⟩ := he
  refine ⟨by rw [← map_mul, h1], by rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, h2], v, ε, hε, ?_⟩
  rw [GlobalTheory.DualPairCheck.cA_cA, add_comm, h3]

theorem suppAt_cA {e : AE D} {V : HSp D} {g : GA D V} (h : SuppAt e V g) : SuppAt (cA D e) V g := by
  intro i j
  rw [GlobalTheory.DualPairCheck.cA_cA, add_comm]
  exact h i j

theorem exists_detAt_cA {e : AE D} (he : IsSplitIdem D e) {V : HSp D} {g : GA D V} {x : (AE D)ˣ}
    (hx : IsDetAt e V g x) : ∃ x' : (AE D)ˣ, IsDetAt (cA D e) V g x' ∧
      ∀ (χ : (AE D)ˣ →* Circle) (n : ℕ), ResEta D χ n → χ x' = χ x := by
  have hi : cA D e * cA D e = cA D e := by rw [← map_mul, he.1]
  refine ⟨GlobalTheory.SplitDetCharacter.cutDet (cA D e) hi V g, ?_, fun χ n hχ => ?_⟩
  · show _ = _
    rw [GlobalTheory.SplitDetCharacter.cutDet_val]; ring
  · refine GlobalTheory.SplitDetCharacter.char_eq_of_mul_conj hχ _ _ ?_
    rw [GlobalTheory.SplitDetCharacter.cutDet_val, hx, map_add (f := _), map_mul, map_sub, map_one]
    have hd := GlobalTheory.SplitDetCharacter.det_mul_conj V g
    linear_combination (1 - cA D (Formalism.L2.Theta.mt V g).det + (Formalism.L2.Theta.mt V g).det * cA D (Formalism.L2.Theta.mt V g).det
      - (Formalism.L2.Theta.mt V g).det) * hi + cA D e * hd

theorem exists_conj_weilDatum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : WRep S T), IsWeilDatumO ψ S T χS χT ω → ∃ ω' : WRep T S, IsWeilDatumO ψ T S χT χS ω' ∧ ∀ (g : GA D S) (h : GA D T) (f : WO S T → ℂ), ω' (h, g) (dag S T f) = dag S T (ω (g, h) f) := by
  intro D ψ S T χS χT ω H
  have hST : AdjLaw ψ S T := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D ψ H.std S T
  have hTS : AdjLaw ψ T S := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D ψ H.std T S
  refine ⟨conjRep hST hTS ω, ?_, fun g h f => by rw [conjRep_apply, dag_dag hST]⟩
  refine
    { std := H.std
      hecS := H.hecT
      hecT := H.hecS
      resS := H.resT
      resT := H.resS
      om_pres := fun p f hf => hST.theta _ (H.om_pres _ _ (hTS.theta f hf))
      om_heis := ?_
      om_aut := ?_
      om_cont := ?_
      om_unit := ?_
      om_split := ?_ }
  · intro h g w₀ f hf
    rw [conjRep_apply, conjRep_apply]
    have e1 := hTS.Heisenberg₂ (adjO S T w₀) f
    rw [hTS.invol] at e1
    rw [← e1, H.om_heis g h (adjO S T w₀) _ (hTS.theta f hf), ← hST.act, hST.Heisenberg₂]
  · intro γ hγ γ' hγ' f hf
    rw [conjRep_apply]
    simp only [dag]
    rw [adjO_zero hST, H.om_aut γ' hγ' γ hγ _ (hTS.theta f hf)]
    simp only [dag]
    rw [adjO_zero hTS, Complex.conj_conj]
  · intro f hf w
    exact Complex.continuous_conj.comp ((H.om_cont _ (hTS.theta f hf) (adjO S T w)).comp continuous_swap)
  · intro μ 𝓕 hμ h𝓕 p f hf
    obtain ⟨μ', 𝓕', hμ', h𝓕', hG⟩ := unit_transport hST hTS μ 𝓕 hμ h𝓕
    have e1 : ∀ w, ‖conjRep hST hTS ω p f w‖ₑ ^ 2 = (fun v => ‖ω (p.2, p.1) (dag T S f) v‖ₑ ^ 2) (adjO S T w) := by
      intro w
      show ‖dag S T (ω (p.2, p.1) (dag T S f)) w‖ₑ ^ 2 = _
      rw [enorm_dag]
    have e2 : ∀ w, ‖f w‖ₑ ^ 2 = (fun v => ‖dag T S f v‖ₑ ^ 2) (adjO S T w) := by
      intro w
      show _ = ‖dag T S f (adjO S T w)‖ₑ ^ 2
      rw [enorm_dag, hTS.invol]
    simp only [e1, e2]
    exact (hG (fun v => ‖ω (p.2, p.1) (dag T S f) v‖ₑ ^ 2)).trans
      ((H.om_unit μ' 𝓕' hμ' h𝓕' _ _ (hTS.theta f hf)).trans (hG (fun v => ‖dag T S f v‖ₑ ^ 2)).symm)
  · intro e he h g hTh hSg y x hy hx
    obtain ⟨x', hx', hxx⟩ := exists_detAt_cA he hx
    obtain ⟨y', hy', hyy⟩ := exists_detAt_cA he hy
    obtain ⟨r, hr, hℓ⟩ := H.om_split (cA D e) (isSplitIdem_cA he) g h (suppAt_cA hSg) (suppAt_cA hTh) x' y' hx' hy'
    refine ⟨r, hr, fun ℓ hinv f hf => ?_⟩
    let ℓω : (WO S T → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun F => starRingEnd ℂ (ℓ (dag S T F))
        map_add' := fun F F' => by simp only [dag_add, map_add (f := _)]
        map_smul' := fun c F => by simp only [dag_smul, map_smul, smul_eq_mul, map_mul, Complex.conj_conj, RingHom.id_apply] }
    have hinvω : ∀ u : WO S T, (∀ i j, cA D (cA D e) * u i j = u i j) → ∀ F, IsThetaFunO ψ S T F →
        ℓω (heisO ψ S T u F) = ℓω F := by
      intro u hu F hF
      show starRingEnd ℂ (ℓ (dag S T (heisO ψ S T u F))) = starRingEnd ℂ (ℓ (dag S T F))
      have e1 := hST.Heisenberg₂ (adjO T S u) F
      rw [hST.invol] at e1
      have hh : IsHalf (cA D (cA D (cA D e))) (adjO T S u) := hTS.half _ u hu
      rw [GlobalTheory.DualPairCheck.cA_cA] at hh
      rw [← e1, hinv _ hh _ (hST.theta F hF)]
    have key := hℓ ℓω hinvω (dag T S f) (hTS.theta f hf)
    have k1 : ℓω (ω (g, h) (dag T S f)) = starRingEnd ℂ (ℓ (conjRep hST hTS ω (h, g) f)) := rfl
    have k2 : ℓω (dag T S f) = starRingEnd ℂ (ℓ f) := by
      show starRingEnd ℂ (ℓ (dag S T (dag T S f))) = _
      rw [dag_dag hTS]
    rw [k1, k2] at key
    have hsf : (starRingEnd ℂ) ((splitFacO χS χT x' y' : Circle) : ℂ) = ((splitFacO χT χS y x : Circle) : ℂ) := by
      rw [← Circle.coe_inv_eq_conj]
      congr 1
      unfold splitFacO
      rw [hxx χT _ H.resT, hyy χS _ H.resS, _root_.mul_inv_rev, inv_inv]
    have key' := congrArg (starRingEnd ℂ) key
    rw [Complex.conj_conj, map_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal, hsf] at key'
    exact key'

end GlobalTheory.WeilConj
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch


theorem _root_.GlobalTheory.T.exists_mixedLagrangian_chart_integral_rowChange : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X →
    ∀ (v : Bs.P) (w : Pl D.host.E), splitPrime (Bs.τ v) = w → ∀ jj : Fv D.host.F v ≃+* Kw w, IsPlaceIso (Bs.τ v) w jj → IsLocIso jj →
    ∀ cc : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w), (Γ.W.bas v).val.map jj * cc.val = basCols B e w →
    ∃ g ∈ KO (Kw w) (Fin (spW G i j).rank),
      IsMixChart v.1 (mixHalf e (atPl w 1)) (mixHalf e (cA D (atPl w 1))) (mixCo B t e w)
        (fun u => chart jj (finCongr (rankW G t i j w)) (colsEq t e w) g (invT cc) (coX (Bs.τ v) (Γ.V.bas v) (Γ.W.bas v) u))
        (fun u => (xiAt w)⁻¹ • chart jj (finCongr (rankW G t i j w)) (colsEq t e w) (invT g) cc
          (coY D.sp.cm.sig Γ.V Γ.W (Bs.τ v) (Γ.V.bas v) (Γ.W.bas v) u))
        (Assignment.one.block _ _)ᶜ := by
  first | exact @GlobalTheory.FlipMatch.RowChart.exists_mixChart | exact GlobalTheory.FlipMatch.RowChart.exists_mixChart | (intros; apply GlobalTheory.FlipMatch.RowChart.exists_mixChart <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch


theorem _root_.GlobalTheory.T.heisenbergOperator_isotropic_translation_char_split : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ →
    ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d), (∀ r s, σ (X.J s r) = X.J r s) → (∀ r s, σ (Y.J s r) = -Y.J r s) → X.J.det ≠ 0 → Y.J.det ≠ 0 → ∀ (M : Model σ X Y) (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
      (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evFin F v) u → pairM (coX t b c u) (coY σ X Y t b c u) = 0 →
    ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (M.co.rho ψ u) φ φ₁ →
      (∀ ι, M.IsLinW ψ t b c ι → ∀ Z, ι φ₁ Z = psiLoc ψ v (pairM Z (coY σ X Y t b c u)) * ι φ (Z + coX t b c u)) ∧
      ∀ ι, M.IsLinBar ψ t b c ι → ∀ Z, ι φ₁ Z = psiLoc ψ v (-pairM Z (coX t b c u)) * ι φ (Z + coY σ X Y t b c u) := by
  first | exact @GlobalTheory.HeisFlip.heis_trans_char | exact GlobalTheory.HeisFlip.heis_trans_char | (intros; apply GlobalTheory.HeisFlip.heis_trans_char <;> assumption)
end
