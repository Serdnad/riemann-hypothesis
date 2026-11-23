module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2186
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1349
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneSeesaw
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNsmulAndNeg
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle023
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle124
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureVanishingLatticeEqRowLatticeMatrices
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
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle012
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertBridge

open GlobalTheory.InertCoord

theorem exists_chart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∃ (ϖ : w.adicCompletion E) (σL : w.adicCompletion E →+* w.adicCompletion E) (q : ℕ) (δ : w.adicCompletion E)
      (JS : GL (Fin a') (w.adicCompletion E)) (JT : GL (Fin (a + a')) (w.adicCompletion E)) (ψL : AddChar (w.adicCompletion E) ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') (w.adicCompletion E) →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') (w.adicCompletion E)) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) (w.adicCompletion E)) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hw _
  have h : w.under (𝓞 F) = v := (InertChart.under_eq_iff hw w).2 rfl
  obtain ⟨ϖ, σL, q, ψL, hc, hU, hodd, hpi, hpn, hψ⟩ := GlobalTheory.T.exists_inertPlace_localField_data F E σ B hTr.base v w hw h
  obtain ⟨A, hAf, hA⟩ := GlobalTheory.T.exists_inertPlace_orthonormal_selfDual_frame F E σ B a a' G hTr.base hTr.geo v w hw h σL hc
  obtain ⟨δ, Bm, hδ1, hδ2, hBf, hB⟩ := GlobalTheory.T.exists_frame_conjTranspose_mul_eq_smul_one F E σ B a a' G hTr.base hTr.geo v w hw h σL hc
  have hσσ : ∀ x, σL (σL x) = x := hU.1
  have hmapσσ : ∀ {k : ℕ} (M : Matrix (Fin k) (Fin k) (w.adicCompletion E)), (M.map σL).map σL = M := fun M =>
    Matrix.ext fun i j => hσσ _
  have hS : ∀ {k : ℕ} (g : Formalism.UG.UJ σL ((1 : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E))),
      (((g : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E)).map σL)ᵀ *
        ((g : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E)) = 1 := fun {k} g => by
    have := g.2
    change Formalism.UG.cT σL ((g : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E)) *
      (1 : Matrix (Fin k) (Fin k) (w.adicCompletion E)) * ((g : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E)) = 1 at this
    rwa [Matrix.mul_one] at this
  have hS' : ∀ {k : ℕ} (g : Formalism.UG.UJ σL ((1 : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E))),
      ((g : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E))ᵀ *
        ((g : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E)).map σL = 1 := fun g => by
    have h2 := congrArg (fun M => M.map σL) (hS g)
    simp only [Matrix.map_mul (f := σL), Matrix.transpose_map, hmapσσ] at h2
    rw [Matrix.map_one _ (map_zero σL) (map_one σL)] at h2
    exact h2
  let φS : Formalism.UG.UJ σL ((1 : GL (Fin a') (w.adicCompletion E)) : Matrix (Fin a') (Fin a') (w.adicCompletion E)) →*
      GL (Fin a') (w.adicCompletion E) := (Formalism.UG.bc σL).comp (Subgroup.subtype _)
  have hφS : ∀ g, ((φS g : GL (Fin a') (w.adicCompletion E)) : Matrix (Fin a') (Fin a') (w.adicCompletion E)) =
      ((g : GL (Fin a') (w.adicCompletion E)) : Matrix (Fin a') (Fin a') (w.adicCompletion E)).map σL := fun g => rfl
  have hφSu : ∀ g, ((φS g : GL (Fin a') (w.adicCompletion E)) : Matrix (Fin a') (Fin a') (w.adicCompletion E))ᵀ *
      ((φS g : GL (Fin a') (w.adicCompletion E)) : Matrix (Fin a') (Fin a') (w.adicCompletion E)).map σL = 1 := fun g => by
    rw [hφS, hmapσσ]; exact hS g
  obtain ⟨ιS, hSat, hSmat, hSK⟩ := GlobalTheory.T.exists_inertPlace_unitary_adelicHom F E σ v w hw h σL hc G.V' A 1 (by rw [hA, one_smul]) φS hφSu
  obtain ⟨ιT, hTat, hTmat, hTK⟩ := GlobalTheory.T.exists_inertPlace_unitary_adelicHom F E σ v w hw h σL hc G.W Bm δ hB (Subgroup.subtype _) (fun g => hS' g)
  have hgrp : ∀ {k : ℕ} (P M : GL (Fin k) (w.adicCompletion E)),
      ((P⁻¹ : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E)) *
        ((P * M * P⁻¹ : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E)) *
        (P : Matrix (Fin k) (Fin k) (w.adicCompletion E)) = (M : Matrix (Fin k) (Fin k) (w.adicCompletion E)) := fun P M => by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  refine ⟨ϖ, σL, q, δ, 1, 1, ψL, kap hw h (A : Matrix (Fin a') (Fin a') (w.adicCompletion E))
    (Bm : Matrix (Fin (a + a')) (Fin (a + a')) (w.adicCompletion E)), ιS, ιT, hU, hodd, one_mem _, one_mem _, ?_, ?_,
    ⟨hδ1, hδ2⟩, hpi, hpn, (GlobalTheory.T.inertPlacePoint_supported_and_surjective F E v w hw h A Bm).1, (GlobalTheory.T.inertPlacePoint_supported_and_surjective F E v w hw h A Bm).2,
    GlobalTheory.T.inertPoint_mem_tensorLattice_iff_integral_coords F E v w hw h G.V' G.W A Bm hAf hBf, ?_, ?_, fun g => hSat g, fun g => hTat g, ?_, ?_⟩
  · intro i j
    simp only [Units.val_one, Matrix.one_apply, eq_comm (a := i)]
    split_ifs <;> simp
  · intro i j
    simp only [Units.val_one, Matrix.one_apply, eq_comm (a := i)]
    split_ifs <;> simp
  · intro x y
    show _ = B.ψ (⅟(2 : AF F) * Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (-1 * hTens (cA σ) (incM F G.V'.J) (incM F G.W.J) _ _))
    rw [GlobalTheory.T.tensorHermitianForm_inertPoint_eq_localForm F E σ v w hw h σL hc G.V'.J G.W.J _ _ δ hA hB x y]
    exact hψ _
  · intro g k x
    change actAB (cA σ) (ιS g, ιT k) (kap hw h (A : Matrix (Fin a') (Fin a') (w.adicCompletion E)) (Bm : Matrix (Fin (a + a')) (Fin (a + a')) (w.adicCompletion E)) x) = _
    rw [GlobalTheory.T.inertPlace_action_on_tensorCoords F E σ v w hw h G.V' G.W A Bm (ιS g) (ιT k) (hSat g) (hTat k) x, hSmat, hTmat, hgrp, hgrp, hφS]
    congr 1
    have key : ∀ M : GL (Fin a') (w.adicCompletion E),
        ((M : Matrix (Fin a') (Fin a') (w.adicCompletion E)).map σL)ᵀ * (M : Matrix (Fin a') (Fin a') (w.adicCompletion E)) = 1 →
        ((M : Matrix (Fin a') (Fin a') (w.adicCompletion E)).map σL)ᵀ = ((M⁻¹ : GL (Fin a') (w.adicCompletion E)) : Matrix (Fin a') (Fin a') (w.adicCompletion E)) := by
      intro M e
      calc _ = ((M : Matrix (Fin a') (Fin a') (w.adicCompletion E)).map σL)ᵀ *
            ((M : Matrix (Fin a') (Fin a') (w.adicCompletion E)) * ((M⁻¹ : GL (Fin a') (w.adicCompletion E)) : Matrix (Fin a') (Fin a') (w.adicCompletion E))) := by
              rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, e, Matrix.one_mul]
    rw [key _ (hS g)]
    rfl
  · intro g hg
    refine hSK hAf g ?_
    obtain ⟨k, hk⟩ := hg
    let σO : Formalism.UG.intL (w.adicCompletion E) →+* Formalism.UG.intL (w.adicCompletion E) :=
      σL.restrict _ _ fun x hx => by
        change Valued.v (σL x) ≤ 1
        rw [hU.2.1 x]; exact hx
    refine ⟨Formalism.UG.bc σO k, Units.ext (Matrix.ext fun i j => ?_)⟩
    rw [hφS, ← hk]
    rfl
  · intro g hg
    exact hTK hBf g hg

end GlobalTheory.InertBridge

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.InertLagChar

theorem at_mul_left' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl (F := F)}
    {a b c : Type} [Fintype b] (P : Matrix a b (AE F E)) {z : Matrix b c (AE F E)} (hz : At (evFin F v) z) :
    At (evFin F v) (P * z) := fun u hu => by rw [← Matrix.mul_smul, hz u hu, Matrix.mul_zero]

theorem at_mul_right' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl (F := F)}
    {a b c : Type} [Fintype b] {z : Matrix a b (AE F E)} (hz : At (evFin F v) z) (P : Matrix b c (AE F E)) :
    At (evFin F v) (z * P) := fun u hu => by rw [← Matrix.smul_mul, hz u hu, Matrix.zero_mul]

theorem at_fromCols_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl (F := F)}
    {a b c : Type} {u : Matrix a b (AE F E)} (hu : At (evFin F v) u) :
    At (evFin F v) (Matrix.fromCols uᵀ (0 : Matrix b c (AE F E))) := fun t ht => by
  ext i j
  rcases j with j | j
  · have := congrArg (fun M => M j i) (hu t ht)
    simpa using this
  · simp

theorem fromCols_add_fromCols {R : Type} [Add R] {a b c : Type} (x z : Matrix a b R) (y w : Matrix a c R) :
    Matrix.fromCols x y + Matrix.fromCols z w = Matrix.fromCols (x + z) (y + w) := by
  ext i j; rcases j with j | j <;> rfl

theorem fromCols_mul_transpose_split {R : Type} [CommRing R] {a b : Type} [Fintype a] (u : Matrix a b R)
    (P : Matrix (a ⊕ a) (a ⊕ a) R) :
    Matrix.fromCols uᵀ (0 : Matrix b a R) * Pᵀ =
      Matrix.fromCols (P.toBlocks₂₁ * u)ᵀ (P.toBlocks₂₁ * u)ᵀ + Matrix.fromCols ((P.toBlocks₁₁ - P.toBlocks₂₁) * u)ᵀ 0 := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks P, Matrix.fromBlocks_transpose, Matrix.fromCols_mul_fromBlocks]
  rw [fromCols_add_fromCols]
  simp only [Matrix.zero_mul, add_zero, Matrix.transpose_mul, Matrix.transpose_sub, Matrix.mul_sub]
  congr 1
  abel

theorem diagW_omd_point : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W)
    (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ (v : Pl (F := F)) (m : ℕ) (C : Matrix (Fin d) (Fin m) (AE F E)), IsLagrAt σ W v C →
    ∀ d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J)) (Fin n × Fin d),
    (∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x) →
    ∀ dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) d' dd →
    ∀ omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J)) →* Module.End ℂ (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ),
    IsSplitting (adeleClass F) ψ dd (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ)) omd →
    ∀ l : (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] ℂ,
    (∀ z : Matrix (Fin d) (Fin n) (AE F E), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
      l (dd.rho ψ (z * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ) Φ) = l Φ) →
    ∀ r₀ : ((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ,
    (∀ φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v), Rest (evFin F v) φ r₀) →
    ∀ c₀ : ℂ, c₀ ≠ 0 → ∀ μ : @Measure (Fin n × Fin d → Fv F v) (borel _),
    (∀ φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v), l (tens (evFin F v) φ r₀) = c₀ * ∫ x, φ (Sum.elim x x) ∂μ) →
    ∀ (p : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J))) (ρ₀ : ℂ),
    (∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), l (omd p Φ) = ρ₀ * l Φ) →
    ∀ Φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v), ∀ Φ₁ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v),
    Acts (evFin F v) (omd p) Φ Φ₁ → ∀ z : Matrix (Fin n) (Fin m) (AE F E), At (evFin F v) z →
      diagW (psiAt ψ v) μ Φ₁ (locCo M.co v (z * Cᵀ)) = ρ₀ * diagW (psiAt ψ v) μ Φ (locCo M.co v
        (((((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).toBlocks₁₁ - ((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).toBlocks₂₁) * z) * Cᵀ)) := by
  intro F E _ _ _ _ _ σ n d X W M ψ hψ v m C hL d' hd' dd hdd omd hsp l hlinv r₀ hr₀ c₀ hc₀ μ hlint p ρ₀ hρ Φ hΦ Φ₁ hΦ₁ hacts z hz

  have hstep : ∀ γ, At (evFin F v) γ → ∀ φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v),
      dd.rho ψ γ (tens (evFin F v) φ r₀) = tens (evFin F v) (schr (psiAt ψ v) (locCo dd v γ) φ) r₀ :=
    fun γ hγ φ hφ => GlobalTheory.VacBridge.rho_acts_locCo dd ψ v γ hγ φ r₀ (hr₀ φ hφ)
  have hmem : ∀ γ, At (evFin F v) γ → ∀ φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v),
      dd.rho ψ γ (tens (evFin F v) φ r₀) ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)) := fun γ hγ φ hφ => by
    rw [hstep γ hγ φ hφ]
    exact (hr₀ _ (GlobalTheory.SchrSB.schr_mem_SB ψ hψ v _ φ hφ)).2
  have hW : ∀ u : Matrix (Fin n) (Fin d) (AE F E), locCo dd v (Matrix.fromCols uᵀ 0) =
      (Sum.elim (locCo M.co v u).1 0, Sum.elim (locCo M.co v u).2 0) := fun u => by
    ext k <;> rcases k with k | k <;> simp [locCo, hdd uᵀ 0, hd' u]
  have hkey : ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) u →
      ∀ φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v),
      c₀ * diagW (psiAt ψ v) μ φ (locCo M.co v u) = l (dd.rho ψ (Matrix.fromCols uᵀ 0) (tens (evFin F v) φ r₀)) :=
    fun u hu φ hφ => by
      rw [hstep _ (at_fromCols_zero hu) φ hφ, hlint _ (GlobalTheory.SchrSB.schr_mem_SB ψ hψ v _ φ hφ), hW, diagW]

  set P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) := ((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) with hP
  set u : Matrix (Fin n) (Fin d) (AE F E) := z * Cᵀ with hu
  set u' : Matrix (Fin n) (Fin d) (AE F E) := ((P.toBlocks₁₁ - P.toBlocks₂₁) * z) * Cᵀ with hu'
  have hzat : At (evFin F v) u := at_mul_right' hz _
  have hu'at : At (evFin F v) u' := at_mul_right' (at_mul_left' _ hz) _
  set xm : Matrix (Fin d) (Fin n) (AE F E) := (P.toBlocks₂₁ * u)ᵀ with hxm
  set δ : Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) :=
    xm * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ with hδ
  have hδc : δ = Matrix.fromCols xm xm := by
    rw [hδ, diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols, Matrix.transpose_one, Matrix.mul_one]
  set Ψ := tens (evFin F v) Φ r₀ with hΨ
  have hΨm : Ψ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)) := (hr₀ Φ hΦ).2
  have h1 : tens (evFin F v) Φ₁ r₀ = omd p Ψ := (hacts r₀ (hr₀ Φ hΦ)).symm
  set γ := actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p⁻¹ (Matrix.fromCols uᵀ (0 : Matrix (Fin d) (Fin n) (AE F E))) with hγ
  have hγat : At (evFin F v) γ := at_mul_right' (at_fromCols_zero hzat) _
  have hinv : dd.rho ψ (Matrix.fromCols uᵀ 0) (omd p Ψ) = omd p (dd.rho ψ γ Ψ) := by
    have h := hsp.impl p⁻¹ (Matrix.fromCols uᵀ 0) (omd p Ψ) (hsp.pres p Ψ hΨm)
    have e1 : ∀ Y, omd p⁻¹ (omd p Y) = Y := fun Y => by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have e2 : ∀ Y, omd p (omd p⁻¹ Y) = Y := fun Y => by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [e1] at h
    rw [← h, e2]
  have hdec : γ = δ + Matrix.fromCols u'ᵀ 0 := by
    have e : u' = (P.toBlocks₁₁ - P.toBlocks₂₁) * u := by rw [hu', hu, Matrix.mul_assoc]
    rw [e, hδc, hxm]
    exact fromCols_mul_transpose_split u P
  have hsum : ∀ Y, dd.rho ψ γ Y = dd.rho ψ δ (dd.rho ψ (Matrix.fromCols u'ᵀ 0) Y) := fun Y => by
    rw [hdec]
    unfold Darboux.rho
    rw [map_add (f := _)]
    apply GlobalTheory.MixXEvUniq.schr_add
    rw [hδc, hdd xm xm, hdd u'ᵀ 0, hd' u', map_zero, hxm, hd' (P.toBlocks₂₁ * u)]
    simp only [Prod.fst_zero, Prod.snd_zero, neg_zero, sumElim_dotProduct_sumElim, dotProduct_zero,
      zero_dotProduct, add_zero]
    have hform := M.co.form (P.toBlocks₂₁ * u) u'
    have h0 := GlobalTheory.InertVacIso.symp_eq_zero_of_lagAt σ X.J W v C hL (-1) (P.toBlocks₂₁ * u) u'
      ⟨at_mul_left' _ hzat, P.toBlocks₂₁ * z, by rw [hu, Matrix.mul_assoc]⟩ ⟨hu'at, (P.toBlocks₁₁ - P.toBlocks₂₁) * z, rfl⟩
    rw [h0] at hform
    exact (sub_eq_zero.mp hform.symm)
  have hW'm : dd.rho ψ (Matrix.fromCols u'ᵀ 0) Ψ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)) :=
    hmem _ (at_fromCols_zero hu'at) Φ hΦ
  have hγm : dd.rho ψ γ Ψ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)) := hmem γ hγat Φ hΦ
  apply mul_left_cancel₀ hc₀
  rw [hkey u hzat Φ₁ hΦ₁, h1, hinv, hρ _ hγm, hsum, hδ, hlinv xm _ hW'm, ← hkey u' hu'at Φ hΦ]
  ring

end GlobalTheory.InertLagChar
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.Tors.FrameTors

theorem oneGen_isGen' {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := fun _ _ =>
  (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

theorem formEq_of_eq {X Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε ε' : K → ℤ}
    (h : ∀ i, ε i = ε' i) : FormEq φ ε φ ε' := fun _ _ _ =>
  Finset.prod_congr rfl fun i _ => by rw [h i]

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_lam {N : ℕ} {g o : GtPtF D F} (hg : GtPtF.IsNsmul N g o) (ho : o.IsZero)
    (w : Frm D F 1 g.b) (hw : w.IsGen) (κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1)) (hκ : Normd κ) :
    ∃ c : F, ∀ z J, Good D.P.L z J → (val w (𝟙 _) z J ^ (N ^ 2) * val κ g.b.left z J).val = cst F z c := by
  have hb : o.b = 1 := ((isZero_iff o).1 ho).1
  have hgN : g.b ^ N = 1 := (GlobalTheory.UU.RelTests.isNsmul_b hg).symm.trans hb
  have e1 : g.b.left ≫ (𝟙 D.P.A ^ N).left = (1 : TF (R := R) F ⟶ D.P.A).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, hgN]
  have e2 : g.b.left ≫ (1 : D.P.A ⟶ D.P.A).left = (1 : TF (R := R) F ⟶ D.P.A).left := by
    rw [← Over.comp_left, MonObj.comp_one]
  have e0 : (DegPre.zeroF D F).left = (1 : TF (R := R) F ⟶ D.P.A).left := rfl
  obtain ⟨c, -, hc⟩ := TWM.exists_ratio D.P.isLB
    (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ w (N ^ 2)) (LB.pullGen D.P.L _ _ κ g.b.left))
    (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ hw _) (pullGen_isGen _ _ _ _ hκ.1 _))
    (LB.oneGen D.P.L) (oneGen_isGen' _) (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Fin.prod_univ_two, Fin.prod_univ_three, DegPre.lineφ, DegPre.lineε, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Category.comp_id, e1, e2, e0,
        Finset.univ_eq_empty, Finset.prod_empty, Matrix.tail_cons, Sum.elim_inl, Sum.elim_inr]
      generalize h (Over.Hom.left (1 : TF (R := R) F ⟶ D.P.A)) = a
      generalize h (Over.Hom.left g.b) = b
      group)
  refine ⟨c, fun z J hJ => ?_⟩
  have := hc _ (𝟙 (TF (R := R) F).left) z J hJ
  rw [val_mul hJ, TWM.val_powGen, val_pull hJ, val_one, Units.val_one, _root_.mul_one] at this
  rw [Category.id_comp (Over.Hom.left g.b)] at this
  exact this

end GlobalTheory.Poinc.Tors.FrameTors

namespace GlobalTheory.Poinc.Tors.FrameTors

theorem frame_tors : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (w₀ : W0 U.toUnifPre) (ρ : LB.Gen (A.L.pull (eSec A.A))), NormW U.toUnifPre w₀ ρ → ∀ N : ℕ, 1 ≤ N → ∀ (g o : GtPtF D.toPre F), GtPtF.IsNsmul N g o → o.IsZero → ∀ (w : Frm D.toPre F 1 g.b) (x : TFK (R := R) F ⟶ A.A) (fr : FrAt x), w.IsGen → LiesOver U.toUnifPre w₀ g w x fr → IsTorsFrame A ρ N x fr → ∀ κ : LB.Gen (kapLB D.toPre (𝟙 D.toPre.P.A ^ N) (N ^ 2) 1), Normd κ → ∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J ^ (N ^ 2) * val κ g.b.left z J = 1 := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ w₀ ρ hN N hN1 g o hgo ho w x fr hw hlies htors κ hκ
  obtain ⟨lam, hlam⟩ := exists_lam hgo ho w hw κ hκ
  have hb : o.b = 1 := ((isZero_iff o).1 ho).1
  have hgN : g.b ^ N = 1 := (GlobalTheory.UU.RelTests.isNsmul_b hgo).symm.trans hb
  have e1 : g.b.left ≫ (𝟙 D.toPre.P.A ^ N).left = (1 : TF (R := R) F ⟶ D.toPre.P.A).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, hgN]
  have e2 : g.b.left ≫ (1 : D.toPre.P.A ⟶ D.toPre.P.A).left = (1 : TF (R := R) F ⟶ D.toPre.P.A).left := by
    rw [← Over.comp_left, MonObj.comp_one]
  have e0 : (DegPre.zeroF D.toPre F).left = (1 : TF (R := R) F ⟶ D.toPre.P.A).left := rfl
  have key : ∀ k : ℕ, 4 ≤ k → lam ^ k = 1 := by
    intro k hk
    have hk1 : 1 ≤ k := by omega
    have hk'1 : 1 ≤ k * N ^ 2 := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (pow_ne_zero 2 (by omega)))
    obtain ⟨t, c, hc0, htc⟩ := GlobalTheory.T.exists_lineBundlePower_section_nonzero_at_origin hL R A F ρ hN.2.1 k hk
    obtain ⟨E, hEG, hEA, hEB, hEh, hEact⟩ := (IntEnd.exists_nsmul_and_neg hL R I hI D A G hG U).1 N
    have hsm : Function.Injective fun χ : D.toPre.X => N • χ := fun a b h => by
      have h' : (N : ℤ) • a = (N : ℤ) • b := by simpa only [natCast_zsmul] using h
      exact smul_right_injective D.toPre.X (Int.natCast_ne_zero.2 (by omega)) h'
    have hinj : Function.Injective E.h := fun a b h => hsm (by simpa only [hEh] using h)
    obtain ⟨β₀, hβ₀⟩ := ThetaSum.exists_gen_pow U.LG U.cubG U.symG U.symG_gen N E.aG hEG
    obtain ⟨β, hβ, -⟩ := exists_gen U.LG.isLB (φ' := ![𝟙 _, E.aG.left]) (ε' := ![((k * N ^ 2 : ℕ) : ℤ), -(k : ℤ)])
      (formEq_of_eq fun i => by fin_cases i <;> simp <;> push_cast <;> ring) (GeneratorPullback.powGen _ _ _ β₀ k)
      (powGen_isGen _ _ _ _ hβ₀ k)
    obtain ⟨-, CT2⟩ := coef_twistPull hL R I hI D A G hG U F E hinj (k * N ^ 2) k hk1 hk'1 ⟨β, hβ⟩
    rw [hEB] at CT2
    obtain ⟨α', hα', hα'n, hpm⟩ := PullMul.pull_mul_value R A F ρ hN.2.1 N k (k * N ^ 2) rfl x fr htors
      (mulT A.A _ N) (snd _ A.A ^ N) (lift_snd _ _) (lift_fst _ _) (by rw [MonObj.comp_pow, Category.comp_id])
    obtain ⟨t', htw, htv⟩ := hpm t c htc
    obtain ⟨e₁, he₁⟩ := GlobalTheory.exists_linearEquiv_expandsF hL.1.globalFns U F hk1 w₀ hN.1
    obtain ⟨e₂, he₂⟩ := GlobalTheory.exists_linearEquiv_expandsF hL.1.globalFns U F hk'1 w₀ hN.1
    have hs : U.ExpandsF F k w₀ t (e₁ t) := (he₁ t _).2 rfl
    have hs' : U.ExpandsF F (k * N ^ 2) w₀ t' (e₂ t') := (he₂ t' _).2 rfl
    obtain ⟨wk, hwk, hwkv⟩ := exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre F g.b)
      (ε' := DegPre.lineε (k * N ^ 2))
      (formEq_of_eq fun i => by fin_cases i <;> simp [DegPre.lineε]) (GeneratorPullback.powGen _ _ _ w (k * N ^ 2))
      (powGen_isGen _ _ _ _ hw _)
    have hκ'e : ∃ κ' : LB.Gen (kapLB D.toPre (𝟙 D.toPre.P.A ^ N) (k * N ^ 2) k), κ'.IsGen ∧
        ∀ (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J →
          val κ' r z J = val (GeneratorPullback.powGen _ _ _ κ k) r z J :=
      exists_gen D.toPre.P.isLB (formEq_of_eq fun i => by fin_cases i <;> simp <;> push_cast <;> ring)
        (GeneratorPullback.powGen _ _ _ κ k) (powGen_isGen _ _ _ _ hκ.1 _)
    obtain ⟨κ', hκ'g, hκ'v⟩ := hκ'e
    have hκ' : Normd κ' := ⟨hκ'g, corr_of_val D.toPre.P.isLB fun y J hJ => by
      rw [val_pull hJ, val_one, hκ'v _ _ y J hJ, TWM.val_powGen]
      have a := val_corr hJ hκ.2 (𝟙 _)
      rw [val_pull hJ, val_one] at a
      rw [a, one_pow]⟩

    obtain ⟨ω, hω, hωv⟩ := exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre F o.b) (ε' := DegPre.lineε k)
      (fun U _ h => by
        rw [Fintype.prod_sum_type]
        simp only [Fin.prod_univ_two, Fin.prod_univ_three, DegPre.lineφ, DegPre.lineε, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Category.comp_id, e1, e2, e0, hb,
          Matrix.tail_cons, Sum.elim_inl, Sum.elim_inr]
        generalize h (Over.Hom.left (1 : TF (R := R) F ⟶ D.toPre.P.A)) = a
        generalize h (Over.Hom.left g.b) = b
        group)
      (LB.mulGen _ _ _ _ _ wk (LB.pullGen _ _ _ κ' g.b.left))
      (mulGen_isGen _ _ _ _ _ _ _ hwk (pullGen_isGen _ _ _ _ hκ'g _))
    have hωm : ∀ z J, Good D.toPre.P.L z J →
        val wk (𝟙 _) z J * val κ' g.b.left z J = val ω (𝟙 _) z J := fun z J hJ => by
      have a := hωv _ (𝟙 (TF (R := R) F).left) z J hJ
      rw [val_mul hJ, val_pull hJ, Category.id_comp (Over.Hom.left g.b)] at a
      exact a.symm
    obtain ⟨q₁, q₂⟩ := CT2 w₀ ρ hN (mulT A.A _ N) (snd _ A.A ^ N) (lift_snd _ _) (lift_fst _ _)
      (by rw [hEA, MonObj.comp_pow, Category.comp_id]) α' hα' hα'n t t' (e₁ t) (e₂ t') hs hs' htw κ' hκ' g o
      ((hEact F g o).2 hgo) wk ω hwk hω hωm
    obtain ⟨w1, hw1⟩ := (CoefBasic.coef_basic R D.toPre F k o).2.1 hb
    have hωl : ∀ z J, Good D.toPre.P.L z J → (val ω (𝟙 _) z J).val = cst F z (lam ^ k) := fun z J hJ => by
      rw [← hωm z J hJ, hwkv _ _ z J hJ, TWM.val_powGen, hκ'v _ _ z J hJ, TWM.val_powGen, pow_mul', ← mul_pow,
        Units.val_pow_eq_pow_val, hlam z J hJ, CoefBasic.cst_eq, CoefBasic.cst_eq, map_pow]
    have hcoef : ∀ χ, coef (e₁ t) o ω χ = lam ^ k * coef (e₁ t) o w1 χ := fun χ =>
      CoefBasic.coef_eq fun z J hJ => by
        have a := CoefBasic.isCoef_coef o hw1.1 χ (e₁ t) z J hJ
        rw [hw1.2 z J hJ, Units.val_one, _root_.mul_one] at a
        rw [hωl z J hJ]
        simp only [CoefBasic.cst_eq, map_mul] at a ⊢
        rw [_root_.mul_assoc, a]
        ring
    have hsum1 : SumF I F (coef (e₂ t') g wk) c := hlies (k * N ^ 2) hk'1 wk
      (fun z J hJ => by rw [hwkv _ _ z J hJ, TWM.val_powGen]) hwk t' (e₂ t') c hs' htv
    have hsum0 : SumF I F (coef (e₁ t) o w1) c :=
      (sumF_origin hL R I hI D A G hG U F).2.2 w₀ ρ hN k t (e₁ t) hs o w1 ho hw1 c htc
    have hre := ((GlobalTheory.AdicSum.sumF_calculus R I hI F D.toPre.X (coef (e₂ t') g wk) (coef (e₂ t') g wk) c c).2.2
      D.toPre.X E.h hinj (fun β hβ => q₂ β hβ)).2 hsum1
    have e3 : (coef (e₂ t') g wk ∘ E.h) =
        fun χ => (lam ^ k - 1) * coef (e₁ t) o w1 χ + coef (e₁ t) o w1 χ := funext fun χ => by
      simp only [Function.comp_apply, q₁, hcoef]; ring
    rw [e3] at hre
    have hsc := (GlobalTheory.AdicSum.sumF_calculus R I hI F D.toPre.X (coef (e₁ t) o w1) (coef (e₁ t) o w1) c c).2.1
      hsum0 hsum0 (lam ^ k - 1)
    have huniq := (GlobalTheory.AdicSum.sumF_calculus R I hI F D.toPre.X
      (fun χ => (lam ^ k - 1) * coef (e₁ t) o w1 χ + coef (e₁ t) o w1 χ) (coef (e₁ t) o w1) c
      ((lam ^ k - 1) * c + c)).1 hre hsc
    have h0 : (lam ^ k - 1) * c = 0 := by linear_combination -huniq
    rcases mul_eq_zero.1 h0 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hc0
  have h4 := key 4 le_rfl
  have h5 := key 5 (by norm_num)
  have hl : lam = 1 := by
    have h0 : lam ≠ 0 := by rintro rfl; norm_num at h4
    calc lam = lam ^ 5 / lam ^ 4 := by field_simp
    _ = 1 := by rw [h4, h5]; norm_num
  intro z J hJ
  apply Units.ext
  rw [hlam z J hJ, hl, Units.val_one, CoefBasic.cst_eq, map_one]

end GlobalTheory.Poinc.Tors.FrameTors
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.closure_vanishing_lattice_eq_row_lattice_matrices : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om') (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E)),
    IsOpen (closure (GlobalTheory.VacShape.Sa Bs Γ L₁ L₂ : Set (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)))) → IsCompact (closure (GlobalTheory.VacShape.Sa Bs Γ L₁ L₂ : Set (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)))) →
    ∃ (P : GL (Fin a') (Fv D.host.F Bs.v₁)) (Λ : Submodule 𝒪[Fv D.host.F Bs.v₁] (Fin (a + a') → Fv D.host.F Bs.v₁)),
      ∀ Y : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁), Y ∈ closure (GlobalTheory.VacShape.Sa Bs Γ L₁ L₂ : Set (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁))) ↔ P.val * Y ∈ matLat (Fin a') Λ := by
  first | exact @GlobalTheory.VacShapeCl.closure_Sa_eq_matLat | exact GlobalTheory.VacShapeCl.closure_Sa_eq_matLat | (intros; apply GlobalTheory.VacShapeCl.closure_Sa_eq_matLat <;> assumption)
end
