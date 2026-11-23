module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1890
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2033
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2054
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle006
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.LeadingConstantNeZero
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanLogPeriodConjugatesEqChowlaSelberg
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.DifferentIdeal.AbsNormInvMulDifferent
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.LatITopBasis
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDefiniteUnitaryQuotientEqClassSum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1349
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1905
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1940

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.DblVacEigen

section Alg

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]


omit [DecidableEq α] in
theorem hTens_dbl (JA : Matrix α α E) (JB : Matrix β β E) (x₁ x₂ y₁ y₂ : Matrix α β E) :
    hTens c JA (dbl JB) (Matrix.fromCols x₁ x₂) (Matrix.fromCols y₁ y₂) = hTens c JA JB x₁ y₁ - hTens c JA JB x₂ y₂ := by
  simp only [hTens, dbl, Fintype.sum_sum_type, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul, add_zero, zero_add, mul_neg, neg_mul,
    Finset.sum_neg_distrib, Finset.sum_add_distrib, sub_eq_add_neg, Finset.sum_const_zero]


omit [DecidableEq α] [DecidableEq β] in
theorem hTens_transpose (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix β α E) :
    hTens c JA JB xᵀ yᵀ = hTens c JB JA x y := by
  unfold hTens
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.transpose_apply]
  ring

end Alg

end GlobalTheory.DblVacEigen

namespace GlobalTheory.DblVacEigen

variable {F : Type} [Field F] [NumberField F]

theorem dot_congr_at {κ : Type} [Fintype κ] (v : Pl (F := F)) {y : κ → AF F} (hy : At (evFin F v) y) {z z' : κ → AF F}
    (h : ∀ i, evFin F v (z i) = evFin F v (z' i)) : z ⬝ᵥ y = z' ⬝ᵥ y := by
  unfold dotProduct
  refine Finset.sum_congr rfl fun i _ => ?_
  have e := congrFun (hy (z i - z' i) (by rw [map_sub, h i, sub_self])) i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e
  rw [sub_mul] at e
  exact sub_eq_zero.mp e

theorem eigen_pointwise {κ : Type} [Fintype κ] (v : Pl (F := F)) (ψ : AddChar (AF F) ℂ) {φ : (κ → Fv F v) → ℂ}
    (hφ : φ ∈ SB (κ → Fv F v)) (p : (κ → AF F) × (κ → AF F)) (hp1 : At (evFin F v) p.1) (hp2 : At (evFin F v) p.2)
    (c : ℂ) (h : Acts (evFin F v) (schr ψ p) φ (c • φ)) (z : κ → AF F) :
    ψ (z ⬝ᵥ p.2 + ⅟(2 : AF F) * (p.1 ⬝ᵥ p.2)) * φ (fun i => evFin F v ((z + p.1) i)) =
      c * φ (fun i => evFin F v (z i)) := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  have hr := hR φ hφ
  let Δ : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (z i))
  have hΔ : At (evFin F v) Δ := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
  have hevΔ : ∀ i, evFin F v (Δ i) = evFin F v (z i) := fun i => GlobalTheory.LatVac.evFin_liftV v _
  have e := congrFun (h R hr) Δ
  have hR2 : R Δ = R 0 := by simpa using hr.1 0 Δ hΔ
  have hR1 : R (Δ + p.1) = R 0 := by rw [hr.1 Δ p.1 hp1, hR2]
  simp only [schr, tens, Pi.smul_apply, smul_eq_mul] at e
  rw [hR1, hR2, dot_congr_at v hp2 hevΔ] at e
  have hev : (fun i => evFin F v ((Δ + p.1) i)) = fun i => evFin F v ((z + p.1) i) := by
    funext i; simp only [Pi.add_apply, map_add (f := _), hevΔ]
  have hev' : (fun i => evFin F v (Δ i)) = fun i => evFin F v (z i) := funext hevΔ
  rw [hev, hev'] at e
  exact mul_right_cancel₀ hR0 (by linear_combination e)

theorem acts_box {κ κ' : Type} [Fintype κ] [Fintype κ'] (v : Pl (F := F)) (ψ : AddChar (AF F) ℂ)
    {φ₁ : (κ → Fv F v) → ℂ} {φ₂ : (κ' → Fv F v) → ℂ} (X₁ Y₁ : κ → AF F)
    (X₂ Y₂ : κ' → AF F) (h11 : At (evFin F v) X₁) (h21 : At (evFin F v) X₂) (c₁ c₂ : ℂ)
    (h₁ : ∀ z, ψ (z ⬝ᵥ Y₁ + ⅟(2 : AF F) * (X₁ ⬝ᵥ Y₁)) * φ₁ (fun i => evFin F v ((z + X₁) i)) =
      c₁ * φ₁ (fun i => evFin F v (z i)))
    (h₂ : ∀ z, ψ (z ⬝ᵥ Y₂ + ⅟(2 : AF F) * (X₂ ⬝ᵥ Y₂)) * φ₂ (fun i => evFin F v ((z + X₂) i)) =
      c₂ * φ₂ (fun i => evFin F v (z i))) :
    Acts (evFin F v) (schr ψ (Sum.elim X₁ X₂, Sum.elim Y₁ Y₂)) (boxFun φ₁ φ₂)
      ((c₁ * c₂) • boxFun φ₁ φ₂) := by
  intro r hr
  have hX : At (evFin F v) (Sum.elim X₁ X₂ : κ ⊕ κ' → AF F) := by
    intro u hu; funext i
    cases i with
    | inl i => exact congrFun (h11 u hu) i
    | inr i => exact congrFun (h21 u hu) i
  funext x
  have hd1 : x ⬝ᵥ Sum.elim Y₁ Y₂ = (x ∘ Sum.inl) ⬝ᵥ Y₁ + (x ∘ Sum.inr) ⬝ᵥ Y₂ := by
    simp [dotProduct, Fintype.sum_sum_type]
  have hd2 : Sum.elim X₁ X₂ ⬝ᵥ Sum.elim Y₁ Y₂ = X₁ ⬝ᵥ Y₁ + X₂ ⬝ᵥ Y₂ :=
    by simp [dotProduct, Fintype.sum_sum_type]
  simp only [schr, tens, Pi.smul_apply, smul_eq_mul]
  rw [hr.1 x _ hX, hd1, hd2,
    show (x ∘ Sum.inl) ⬝ᵥ Y₁ + (x ∘ Sum.inr) ⬝ᵥ Y₂ + ⅟(2 : AF F) * (X₁ ⬝ᵥ Y₁ + X₂ ⬝ᵥ Y₂) =
      ((x ∘ Sum.inl) ⬝ᵥ Y₁ + ⅟(2 : AF F) * (X₁ ⬝ᵥ Y₁)) + ((x ∘ Sum.inr) ⬝ᵥ Y₂ + ⅟(2 : AF F) * (X₂ ⬝ᵥ Y₂))
      by ring, AddChar.map_add_eq_mul]
  have e1 := h₁ (x ∘ Sum.inl)
  have e2 := h₂ (x ∘ Sum.inr)
  simp only [boxFun, Function.comp_def, Pi.add_apply, Sum.elim_inl, Sum.elim_inr] at e1 e2 ⊢
  rw [show ∀ a e b f s : ℂ, a * e * ((b * f) * s) = (a * b) * (e * f) * s from fun _ _ _ _ _ => by ring, e1, e2]
  ring

end GlobalTheory.DblVacEigen

namespace GlobalTheory.DblVacEigen

theorem doubled_vac_eigen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (AE F E), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')))),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) d' dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) (G.M.vac v)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • G.M.vac v)) →
    (∀ w₁ ∈ latAtV G.V G.W v, ∀ w₂ ∈ latAtV G.V G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) (boxFun (G.M.vac v) (fun x => star (G.M.vac v x)))
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • (boxFun (G.M.vac v) (fun x => star (G.M.vac v x))))) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w _ _ d' hd' dd hdd θ _ hvac w₁ hw₁ w₂ hw₂
  have hSB := (hT.geo.hM.vac v).1
  have hψ : ∀ t, ‖B.ψ t‖ = 1 := GlobalTheory.StdCharWeilDatum.norm_psi hT.base.std
  have hstar : ∀ t, star (B.ψ t) = B.ψ (-t) := by
    intro t
    rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ t]
    simp
  have hAt : ∀ γ ∈ latAtV G.V G.W v, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V G.W v).1
  have hco : ∀ γ ∈ latAtV G.V G.W v, At (evFin F v) (G.M.co.e γ).1 ∧ At (evFin F v) (G.M.co.e γ).2 := by
    intro γ hγ
    have e : ∀ u, evFin F v u = 0 → u • G.M.co.e γ = 0 := fun u hu => by
      rw [← map_smul, hAt γ hγ u hu, map_zero]
    exact ⟨fun u hu => congrArg Prod.fst (e u hu), fun u hu => congrArg Prod.snd (e u hu)⟩
  have h1 := eigen_pointwise v B.ψ hSB (G.M.co.e w₁) (hco w₁ hw₁).1 (hco w₁ hw₁).2 _ (hvac w₁ hw₁)
  have h2 := eigen_pointwise v B.ψ hSB (G.M.co.e w₂) (hco w₂ hw₂).1 (hco w₂ hw₂).2 _ (hvac w₂ hw₂)
  have h2' : ∀ z, B.ψ (z ⬝ᵥ (-(G.M.co.e w₂).2) + ⅟(2 : AF F) * ((G.M.co.e w₂).1 ⬝ᵥ (-(G.M.co.e w₂).2))) *
      (fun x => star (G.M.vac v x)) (fun i => evFin F v ((z + (G.M.co.e w₂).1) i)) =
      star (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) w₂ w₂)) * (fun x => star (G.M.vac v x)) (fun i => evFin F v (z i)) := by
    intro z
    have e := congrArg star (h2 z)
    simp only [star_mul, hstar] at e
    rw [hstar, show z ⬝ᵥ (-(G.M.co.e w₂).2) + ⅟(2 : AF F) * ((G.M.co.e w₂).1 ⬝ᵥ (-(G.M.co.e w₂).2)) =
      -(z ⬝ᵥ (G.M.co.e w₂).2 + ⅟(2 : AF F) * ((G.M.co.e w₂).1 ⬝ᵥ (G.M.co.e w₂).2)) by
        rw [dotProduct_neg, dotProduct_neg]; ring]
    linear_combination e
  have hbox := acts_box v B.ψ (φ₁ := G.M.vac v) (φ₂ := fun x => star (G.M.vac v x)) (G.M.co.e w₁).1 (G.M.co.e w₁).2 (G.M.co.e w₂).1 (-(G.M.co.e w₂).2)
    (hco w₁ hw₁).1 (hco w₂ hw₂).1 _ _ h1 h2'
  have hrho : dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ) = schr B.ψ (Sum.elim (G.M.co.e w₁).1 (G.M.co.e w₂).1,
      Sum.elim (G.M.co.e w₁).2 (-(G.M.co.e w₂).2)) := by
    rw [Darboux.rho, hdd, hd', hd']
  have hS : symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))
      (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ) = symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) w₁ w₁ - symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) w₂ w₂ := by
    unfold symp
    rw [hTens_dbl, hTens_transpose, hTens_transpose, mul_sub, map_sub]
  have hc : B.ψ (⅟(2 : AF F) * (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) w₁ w₁ - symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) w₂ w₂)) = B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) w₁ w₁) * star (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) w₂ w₂)) := by
    rw [hstar, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [hrho, hS, hc]
  exact hbox

end GlobalTheory.DblVacEigen

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocModel

theorem weil_normalises_schr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (Y : Type) [AddCommGroup Y] (Xm : Y →+ Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
      (∀ y, At (evFin F v) (Xm y)) →
      ∀ ρ : Y → Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v)),
      (∀ x (φ : SB (Fin a × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M.co.rho B.ψ (Xm x))
        (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) ((ρ x φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ)) →
      ∀ (Γ : Type) [Group Γ] (j : Γ →* UA σ G.V.J × UA σ G.W.J) (ω : Γ →* Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v))),
      (∀ g (φ : SB (Fin a × Fin (a + a') → Fv F v)) (φ₁ : (Fin a × Fin (a + a') → Fv F v) → ℂ),
        Acts (evFin F v) (om (j g)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          φ₁ = ((ω g φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ)) →
      ∀ actY : Γ → Y → Y, (∀ g x, actAB (cA σ) (j g) (Xm x) = Xm (actY g x)) →
      ∀ g x, ω g * ρ x = ρ (actY g x) * ω g := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v Y _ Xm hXm ρ hρ Γ _ j ω hω actY hact g x
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (F := F) (Fin a × Fin (a + a')) v
  have hS := IsUWeilPair.isUSplitting hT.weil
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  apply GlobalTheory.InertAvgDual.eq_of_tens_eq v hR0 (hR _ φ.2).1
  simp only [Module.End.mul_apply]
  have h1 := (hω g (ρ x φ) _).2 rfl R (hR _ (ρ x φ).2)
  have h2 := hρ x φ R (hR _ φ.2)
  have h3 := (hω g φ _).2 rfl R (hR _ φ.2)
  have h4 := hρ (actY g x) (ω g φ) R (hR _ (ω g φ).2)
  have h5 := hS.impl (j g) (Xm x) (tens (evFin F v) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) R) (hR _ φ.2).2
  rw [← h1, ← h4, ← h2, h5, hact, h3]

end GlobalTheory.InertLocModel
end
end

section

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

theorem _root_.GlobalTheory.T.vacuum_eigenvalue_theta_independent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (θ θ' : 𝓞 E), (θ : E) + σ θ = 1 → (θ' : E) + σ θ' = 1 → ∀ γ ∈ latAtV X W v,
      B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) γ γ) =
        B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ' : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) γ γ) := by
  first | exact @GlobalTheory.VacThetaIndep.vacuum_character_theta_indep | exact GlobalTheory.VacThetaIndep.vacuum_character_theta_indep | (intros; apply GlobalTheory.VacThetaIndep.vacuum_character_theta_indep <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ), l ∈ (adeleClass F).adm κ → (∀ (y : κ → AF F), ∀ φ ∈ schA F κ, l (fun x => ψ (x ⬝ᵥ y) * φ x) = l φ) → ∃ c : ℂ, ∀ φ ∈ schA F κ, l φ = c * φ 0 := by
  first | exact @GlobalTheory.CharInvForm.main | exact GlobalTheory.CharInvForm.main | (intros; apply GlobalTheory.CharInvForm.main <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.inertPlace_tensorLattice_selfDual_symplectic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ), X.IsHerm σ B r s → Y.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z →
      (z ∈ latAtV X Y v ↔ ∀ γ ∈ latAtV X Y v,
        B.ψ (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) Y.J) z γ) = 1) := by
  first | exact @GlobalTheory.InertLatSelfDual.latAtV_selfDual_inert | exact GlobalTheory.InertLatSelfDual.latAtV_selfDual_inert | (intros; apply GlobalTheory.InertLatSelfDual.latAtV_selfDual_inert <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.linearForm_eq_zero_of_kills_productSchwartzBruhat : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (ψ : AddChar (Fv F v) ℂ), Continuous ψ → ψ ≠ 1 →
    ∀ Λ : ((κ ⊕ κ' → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
      (∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ' → Fv F v), Λ (boxFun φ₁ φ₂) = 0) → ∀ Φ ∈ SB (κ ⊕ κ' → Fv F v), Λ Φ = 0 := by
  first | exact @GlobalTheory.BoxSpan.boxSpan_ker | exact GlobalTheory.BoxSpan.boxSpan_ker | (intros; apply GlobalTheory.BoxSpan.boxSpan_ker <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

namespace GlobalTheory.WeylFour.SchrKeep

theorem schr_mem_schA : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (w : (κ → AF F) × (κ → AF F)), ∀ Φ ∈ schA F κ, schr ψ w Φ ∈ schA F κ := by
  intro F _ _ ψ hψ κ _ w Φ hΦ
  exact GlobalTheory.ConeMeasV.schr_mem_schA hψ w hΦ

end GlobalTheory.WeylFour.SchrKeep
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_local_schroedinger_family_at_place : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (AF F) ℂ), IsStd ψ → PsiUnr ψ v →
    ∀ {Wm : Type} [AddCommGroup Wm] [Module (AF F) Wm] {Bf : Wm → Wm → AF F} {κ : Type} [Fintype κ] (co : Darboux Bf κ)
      (Y : Type) [AddCommGroup Y] (Xm : Y →+ Wm) (χ : Y → Y → ℂ),
      (∀ z : Wm, At (evFin F v) z ↔ ∃ y, Xm y = z) → (∀ x y, ψ (⅟(2 : AF F) * Bf (Xm x) (Xm y)) = χ x y) →
      ∃ ρ : Y → Module.End ℂ (SB (κ → Fv F v)), ρ 0 = 1 ∧ (∀ x y, ρ x * ρ y = χ x y • ρ (x + y)) ∧
        (∀ x (φ : SB (κ → Fv F v)), Acts (evFin F v) (co.rho ψ (Xm x)) (φ : (κ → Fv F v) → ℂ)
          ((ρ x φ : SB (κ → Fv F v)) : (κ → Fv F v) → ℂ)) ∧
        ∀ s : SB (κ → Fv F v), s ≠ 0 → Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ := by
  first | exact @GlobalTheory.SchrLocModel.exists_locRho | exact GlobalTheory.SchrLocModel.exists_locRho | (intros; apply GlobalTheory.SchrLocModel.exists_locRho <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.HeckeSplitBase

theorem heckeChar_eq_one_of_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ ν : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF ν →
      (∀ e, IsSplitIdemF σ e → ∀ x : (AF F ⊗[F] E)ˣ, (e + cAF σ e) * ((x : AF F ⊗[F] E) - 1) = (x : AF F ⊗[F] E) - 1 →
        ν x = 1) → ∀ x, ν x = 1 := by
  intro F E _ _ _ _ _ σ B hB ν hν hs
  exact GlobalTheory.T.heckeChar_eq_one_of_trivial_splitPlaces_CM F E σ hB.cm ν hν hs

end GlobalTheory.HeckeSplitBase

end
end

section

noncomputable section

namespace GlobalTheory.MeanPeriodClosed

open NumberField Formalism.BasicNotions
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5 (brN br_meanLogOm_eq br_b_spec absNorm_inv_mul_different natAbs_discr_eq
  discr_K discriminant_mod_four br_sqrt_sq br_finrank_K br_finrank_E)

theorem two_log_brN (D : D7) :
    (2 / (Module.finrank ℚ D.host.E : ℝ)) * Real.log (brN D) =
      Real.log D.host.rdE - Real.log (Real.sqrt (D.host.d : ℝ)) := by
  haveI : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩
  have hd0 : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  have hdK : NumberField.discr D.host.K = -(D.host.d : ℤ) :=
    discr_K D.host.K D.host.d (discriminant_mod_four D) _ (br_sqrt_sq D) (br_finrank_K D)
  have h1 := absNorm_inv_mul_different D.host.K D.host.E D.host.conj D.host.𝔟 (br_b_spec D)
  have h2 := natAbs_discr_eq D.host.K D.host.E D.host.d hdK
  set A : ℝ := (Ideal.absNorm (differentIdeal (𝓞 D.host.K) (𝓞 D.host.E)) : ℝ) with hA
  have hsq : brN D ^ 2 = A := by
    have := congrArg (fun q : ℚ => (q : ℝ)) h1
    simp only [Rat.cast_pow, Rat.cast_natCast] at this
    rw [hA, ← this]
    rfl
  set m : ℕ := Module.finrank D.host.K D.host.E with hm
  have hE : Module.finrank ℚ D.host.E = 2 * m := br_finrank_E D
  have hm0 : (m : ℝ) ≠ 0 := by
    have : 0 < m := Module.finrank_pos
    exact_mod_cast this.ne'
  have hdisc : |(NumberField.discr D.host.E : ℝ)| = A * (D.host.d : ℝ) ^ m := by
    have := congrArg (fun n : ℕ => (n : ℝ)) h2
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs] at this
    rw [hA, ← this]
  have hdisc0 : |(NumberField.discr D.host.E : ℝ)| ≠ 0 := by
    simpa using NumberField.discr_ne_zero D.host.E
  have hA0 : A ≠ 0 := fun h => hdisc0 (by rw [hdisc, h, zero_mul])
  have hlogA : 2 * Real.log (brN D) = Real.log A := by
    rw [← hsq, Real.log_pow]; push_cast; ring
  have hrd : Real.log D.host.rdE =
      (Real.log A + (m : ℝ) * Real.log D.host.d) / (2 * (m : ℝ)) := by
    unfold Formalism.BasicNotions.Host.rdE
    rw [Real.log_rpow (abs_pos.2 (by simpa using NumberField.discr_ne_zero D.host.E)), hdisc,
      Real.log_mul hA0 (pow_ne_zero _ hd0.ne'), Real.log_pow, hE]
    push_cast
    field_simp
  rw [hrd, Real.log_sqrt hd0.le, hE]
  push_cast
  field_simp
  linear_combination hlogA

theorem meanPeriodAt (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriodAt D cc δ := by
  intro M _ hM τ
  have hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have hpos : ∀ ρ : M →ₐ[ℚ] ℂ,
      0 < Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.area (Formalism.MainNotions.TaylorLogMetric.lamConj M ρ (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)) :=
    fun ρ => GlobalTheory.Glob.area_lamConj_pos hc hM ρ
  have hmean := GlobalTheory.PeriodMean.mean_log_period D (GlobalTheory.InducedType.induced_type D).1 cc δ hc M
    hM.2.1 hM.2.2
  have e := br_meanLogOm_eq D (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) M hM.1 τ hpos
  have hN := two_log_brN D
  show Formalism.MainNotions.TaylorLogMetric.meanLogOm D (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) M τ = Formalism.MainNotions.TaylorLogMetric.logOmVal D
  rw [e, GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.logOmVal_eq]
  have hmean' : (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.area
      (Formalism.MainNotions.TaylorLogMetric.lamConj M ρ (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)) / Real.pi)) / (Module.finrank ℚ M : ℝ) =
      Real.eulerMascheroniConstant + Real.log (2 * Real.pi / Real.sqrt D.host.d) -
        Formalism.MainNotions.TaylorLogMetric.logDerivativeAtOne D := hmean
  rw [hmean']
  have hd0 : (0 : ℝ) < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  have hr0 : 0 < D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE
    exact Real.rpow_pos_of_pos (abs_pos.2 (by simpa using NumberField.discr_ne_zero D.host.E)) _
  rw [Real.log_div (by positivity) hd0.ne', Real.log_div (by positivity) hr0.ne']
  rw [neg_mul, hN]
  ring

theorem meanPeriod : GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod :=
  fun D cc δ hcc hδ => meanPeriodAt D cc δ hcc hδ

end GlobalTheory.MeanPeriodClosed
end
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.integral_definiteUnitaryQuotient_eq_classSum : ∀ {D : D7} (V : HSp D) (n : ℕ) (ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V) (J : Subgroup (Formalism.MainNotions.StandardLatticesGL3.GA D n))
  (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)),
  GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace V → Function.Injective ι → ι.range = GfC V →
  (∀ x, (∃ γ ∈ GQ V, finHom V γ = finHom V (ι x)) ↔ x ∈ ratG D n) →
  GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel V K → (∀ x, Lev.finE V (ι x) ∈ K ↔ x ∈ J) → Links.IsMeasDef V K μ 𝓕 →
  ∀ Φ : GA D V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsClassFun V K Φ →
    Finite (Cls D n J) ∧ Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) Φ) (GlobalTheory.AutomorphicL2Unitary.autMeasure V μ) ∧
    ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) Φ q ∂GlobalTheory.AutomorphicL2Unitary.autMeasure V μ =
      ∑ᶠ x : Cls D n J, ((gam D J x.out : ℂ))⁻¹ * Φ (ι x.out) := by
  first | exact @GlobalTheory.NormDictClassSum.integral_eq_classSum | exact GlobalTheory.NormDictClassSum.integral_eq_classSum | (intros; apply GlobalTheory.NormDictClassSum.integral_eq_classSum <;> assumption)
end
