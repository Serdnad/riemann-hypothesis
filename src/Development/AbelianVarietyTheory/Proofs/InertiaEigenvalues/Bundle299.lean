module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle033
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle098
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle184
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle169
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle147
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle264
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle200
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle246
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle100
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle272
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle140
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisBorderedMatrixNormalFormInvariants
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle142
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle221
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle141
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle213
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle171
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle227
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle258
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle273
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle274
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Mathlib.LinearAlgebra.TensorProduct.Pi
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMonCob

theorem coboundary_cols (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ρ₀ : ↥(GK K) →* GL ι ℚ_[l]) (c₀ : ↥(GK K) → ι → ℚ_[l]) (b : (ι → ℚ_[l]) ⊗[ℚ_[l]] Bst P) :
    (∀ g, c₀ g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P (repOf ρ₀) g b - b) →
    ∃ β : ι → Bst P, ∀ g : ↥(GK K), (fun x => algebraMap ℚ_[l] (Bst P) (c₀ g x)) =
      ((ρ₀ g : Matrix ι ι ℚ_[l]).map (algebraMap ℚ_[l] (Bst P))).mulVec (fun x => actSt P (g : GQ l) (β x)) - β := by
  intro h
  let Φ : (ι → ℚ_[l]) ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] (ι → Bst P) :=
    TensorProduct.lift (LinearMap.mk₂ ℚ_[l] (fun (v : ι → ℚ_[l]) (a : Bst P) (x : ι) => v x • a)
      (fun v w a => by funext x; simp [add_smul])
      (fun c v a => by funext x; simp [mul_smul])
      (fun v a a' => by funext x; simp [smul_add])
      (fun c v a => by funext x; simp [smul_comm c]))
  have hΦ : ∀ (v : ι → ℚ_[l]) (a : Bst P), Φ (v ⊗ₜ a) = fun x => v x • a := fun v a => by
    simp [Φ]
  have hst : ∀ (g : ↥(GK K)) (y : (ι → ℚ_[l]) ⊗[ℚ_[l]] Bst P),
      Φ (stRep P (repOf ρ₀) g y) = ((ρ₀ g : Matrix ι ι ℚ_[l]).map (algebraMap ℚ_[l] (Bst P))).mulVec
        (fun x => actSt P (g : GQ l) (Φ y x)) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => funext x; simp [Matrix.mulVec, dotProduct]
    | tmul v a =>
      rw [stRep_tmul, repOf_apply, hΦ, hΦ]
      funext x
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul, map_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_smul]
    | add y z hy hz =>
      rw [map_add (f := _), map_add (f := _), hy, hz, ← Matrix.mulVec_add]
      congr 1
      funext x
      simp
  refine ⟨Φ b, fun g => ?_⟩
  have := congrArg Φ (h g)
  rw [map_sub, hst, hΦ] at this
  rw [← this]
  funext x
  simp [Algebra.algebraMap_eq_smul_one]

end GlobalTheory.PMonCob
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CobColumn

theorem coboundary_tmul_of_column : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ρ₀ : ↥(GK K) →* GL ι ℚ_[l]) (c₀ : ↥(GK K) → ι → ℚ_[l]) (β : ι → P.R.BdR),
    (∀ g : ↥(GK K), (fun x => algebraMap ℚ_[l] P.R.BdR (c₀ g x)) =
      ((ρ₀ g : Matrix ι ι ℚ_[l]).map (algebraMap ℚ_[l] P.R.BdR)).mulVec (fun x => P.actQdR (g : GQ l) (β x)) - β) →
    ∃ b : (ι → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR, ∀ g,
      c₀ g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = actVdR (P.PD K) (repOf ρ₀) g b - b := by
  intro l _ P K ι _ _ ρ₀ c₀ β h
  let Φ : (ι → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (ι → P.R.BdR) :=
    (piScalarRight ℚ_[l] ℚ_[l] P.R.BdR ι).toLinearMap ∘ₗ (TensorProduct.comm ℚ_[l] _ _).toLinearMap
  have hΦinj : Function.Injective Φ :=
    (piScalarRight ℚ_[l] ℚ_[l] P.R.BdR ι).injective.comp (TensorProduct.comm ℚ_[l] _ _).injective
  have hΦ : ∀ v b i, Φ (v ⊗ₜ b) i = algebraMap ℚ_[l] P.R.BdR (v i) * b := by
    intro v b i
    simp [Φ, piScalarRight_apply, piScalarRightHom_tmul, Algebra.smul_def]
  have hact : ∀ g v b, actVdR (P.PD K) (repOf ρ₀) g (v ⊗ₜ b) = repOf ρ₀ g v ⊗ₜ P.actQdR (g : GQ l) b := by
    intro g v b
    rw [← P.PD_actdR K g b]
    rfl
  refine ⟨∑ x, Pi.single x 1 ⊗ₜ β x, fun g => hΦinj ?_⟩
  funext i
  have hi := congrFun (h g) i

  simp only [map_sub, map_sum, Pi.sub_apply, Finset.sum_apply, hact, hΦ, repOf_apply, mul_one]
  rw [hi]
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    congr 2
    rw [Finset.sum_eq_single x (fun y _ hy => by simp [Pi.single_eq_of_ne hy]) (by simp)]
    simp
  · rw [Finset.sum_eq_single i]
    · simp
    · intro x _ hx; simp [Pi.single_eq_of_ne' hx]
    · simp

end GlobalTheory.CobColumn

end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.WeilEtProof

theorem weilAt_of_isField : WeilField → ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → IsField A.L → WeilAt A := by
  intro hF F E _ _ _ _ _ A hK hL ψ hψ x μ hμ
  have hfacts := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  refine hF F E A hK hL ψ hψ x μ hμ A.etaK (fun s => ⟨?_, fun h => GlobalTheory.T.etaK_eq_neg_one_of_not_norm F E A hK hL s h⟩)
  rintro ⟨y, hy⟩
  have hy0 : y ≠ 0 := by
    rintro rfl
    have h1 := hfacts.1 0
    rw [hy, zero_mul] at h1
    have hu : IsUnit (algebraMap A.K A.L s) := s.isUnit.map _
    rw [h1, isUnit_zero_iff] at hu
    obtain ⟨a, b, hab⟩ := hL.exists_pair_ne
    exact hab (by rw [← one_mul a, ← one_mul b, ← hu, zero_mul, zero_mul])
  obtain ⟨b, hb⟩ := hL.mul_inv_cancel hy0
  have := hfacts.2.2.2.1 y (IsUnit.of_mul_eq_one _ hb)
  rwa [hy] at this

end GlobalTheory.JR.WeilEtProof


open GlobalTheory.JR.WeilEtProof in
theorem GlobalTheory.JR.weilEt_of_weilField : WeilField → WeilEt := by
  intro hF F E _ _ _ _ _ A ψ hψ x μ hμ
  suffices h : ∀ (n : ℕ) (A : Et F E), Module.finrank F A.K = n → WeilAt A from h _ A rfl ψ hψ x μ hμ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hn
    rcases subsingleton_or_nontrivial A.K with hs | hnt
    · exact GlobalTheory.T.weilRepresentationExistsEtale_of_subsingleton F E A hs
    by_cases hK : IsField A.K
    · by_cases hL : IsField A.L
      · exact weilAt_of_isField hF F E A hK hL
      · intro ψ hψ x μ hμ
        obtain ⟨W, hW⟩ := GlobalTheory.T.exists_weilRepresentation_hyperbolic_split F E A ψ hψ hK hL x μ hμ
        exact ⟨1, W, hW⟩
    · obtain ⟨A₁, A₂, eK, eL, hs, h₁, h₂⟩ := GlobalTheory.T.exists_etaleInvolutiveAlgebraSplitting_smaller F E A hnt hK
      exact GlobalTheory.T.weil_condition_product_splitting F E A A₁ A₂ eK eL hs (ih _ (hn ▸ h₁) A₁ rfl) (ih _ (hn ▸ h₂) A₂ rfl)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.LinDesc

theorem valuationParitySign_mul_self {F : Type} [NormedField F] (x : F) : eta x * eta x = 1 := by
  unfold eta; split_ifs <;> norm_num

theorem valuationParitySign_one {F : Type} [NormedField F] : eta (1 : F) = 1 := by
  unfold eta; rw [if_pos ⟨1, by simp⟩]

theorem desc_unit_eq {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F} (hG : A.IsGen τ p) (lam : F)
    (M : Meas r F E) (α : GL (Fin r) F → ℝ) (f' : Gl r F → ℂ) (a s : A.Kˣ) :
    desc A M hG lam α f' ((a : A.K) * Ring.inverse (s : A.K), (s : A.K)) * A.etaK s =
      A.etaK a * (letI := M.mG; ∫ g, f' (act g (pt A hG lam 1 a)) * eta ((g : Matrix (Fin r) (Fin r) F).det) *
        (α (g * tm A hG a⁻¹ * tm A hG s) : ℂ) ∂M.μG) := by
  letI := M.mG
  haveI := M.bG
  haveI : M.μG.IsMulRightInvariant := GlobalTheory.T.generalLinear_haar_isMulRightInvariant_unramified F E r M
  have hmul := (GlobalTheory.T.unramifiedValuationParitySign_character_kernel_norms F E).1
  set Y := pt A hG lam 1 (a : A.K) with hY
  set u : A.Kˣ := a * s⁻¹ with hu
  have hpt : pt A hG lam ((a : A.K) * Ring.inverse (s : A.K)) (s : A.K) = act (tm A hG u) Y := by
    rw [hY, act_tm, Ring.inverse_unit]
    congr 1
    · rw [hu, Units.val_mul, mul_one]
    · rw [hu, _root_.mul_inv_rev, inv_inv, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  have h1 : desc A M hG lam α f' ((a : A.K) * Ring.inverse (s : A.K), (s : A.K)) =
      ∫ g, f' (act (g * tm A hG u) Y) * eta ((g : Matrix (Fin r) (Fin r) F).det) * (α g : ℂ) ∂M.μG := by
    unfold desc
    simp only [hpt, act_mul]
  have h2 : (∫ g, f' (act (g * tm A hG u) Y) * eta ((g : Matrix (Fin r) (Fin r) F).det) * (α g : ℂ) ∂M.μG) =
      ∫ g, f' (act g Y) * eta (((g * (tm A hG u)⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det) *
        (α (g * (tm A hG u)⁻¹) : ℂ) ∂M.μG := by
    have := integral_mul_right_eq_self (μ := M.μG) (fun h : GL (Fin r) F => f' (act h Y) *
      eta (((h * (tm A hG u)⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det) * (α (h * (tm A hG u)⁻¹) : ℂ)) (tm A hG u)
    simp only [mul_inv_cancel_right] at this
    exact this
  rw [h1, h2, ← integral_mul_const, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  have hui : (tm A hG u)⁻¹ = tm A hG a⁻¹ * tm A hG s := by
    rw [← map_inv, ← map_mul, hu, _root_.mul_inv_rev, inv_inv, mul_comm]
  have hdg : (g : Matrix (Fin r) (Fin r) F).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
  have hN : ∀ t : A.Kˣ, Algebra.norm F (t : A.K) ≠ 0 := fun t =>
    (IsUnit.map (Algebra.norm F) (Units.isUnit t)).ne_zero
  have hdet : (((g * (tm A hG u)⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det) =
      (g : Matrix (Fin r) (Fin r) F).det * (Algebra.norm F ((a⁻¹ : A.Kˣ) : A.K) * Algebra.norm F (s : A.K)) := by
    rw [hui, Units.val_mul, Matrix.det_mul, ← map_mul, det_tm, Units.val_mul, map_mul]
  have h12 : eta (Algebra.norm F (a : A.K)) * eta (Algebra.norm F ((a⁻¹ : A.Kˣ) : A.K)) = 1 := by
    rw [← hmul _ _ (hN a) (hN a⁻¹), ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, valuationParitySign_one]
  have h11 := valuationParitySign_mul_self (Algebra.norm F (a : A.K))
  have h33 := valuationParitySign_mul_self (Algebra.norm F (s : A.K))
  simp only []
  rw [hdet, hmul _ _ hdg (mul_ne_zero (hN _) (hN _)), hmul _ _ (hN _) (hN _), hui, ← _root_.mul_assoc g (tm A hG a⁻¹) (tm A hG s)]
  unfold Et.etaK
  set e1 := eta (Algebra.norm F (a : A.K))
  set e2 := eta (Algebra.norm F ((a⁻¹ : A.Kˣ) : A.K))
  set e3 := eta (Algebra.norm F (s : A.K))
  set d := eta ((g : Matrix (Fin r) (Fin r) F).det)
  set fv := f' (act g Y)
  set al : ℂ := (α (g * tm A hG a⁻¹ * tm A hG s) : ℂ)
  linear_combination (fv * d * al * e2) * h33 - (fv * d * al * e2) * h11 + (fv * d * al * e1) * h12

end GlobalTheory.JR.LinDesc

namespace GlobalTheory.JR.LinDesc

theorem orb_descent_unit : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (M : Meas r F E) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (α : GL (Fin r) F → ℝ) (f' : Gl r F → ℂ), IsTest f' → IsLocallyConstant α → HasCompactSupport α → (∀ g, 0 ≤ α g) → (∀ g : GL (Fin r) F, (∃ v w : Fin r → F, f' ((g : Matrix (Fin r) (Fin r) F) * companion p * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F), v, w, lam) ≠ 0) → ∀ s₀ : A.Kˣ, ∫ s, α (g * LinDesc.tm A hG s₀ * LinDesc.tm A hG s) ∂(LinDesc.unitsMeas A μK) = 1) → ∀ κ₀ : ℂ, (∀ a : A.K, IsUnit a → ∀ g : GL (Fin r) F, omega (act g (LinDesc.pt A hG lam 1 a)) = κ₀ * eta ((g : Matrix (Fin r) (Fin r) F).det) * A.etaK a) → ∀ a : A.K, IsUnit a → orbG M f' (LinDesc.pt A hG lam 1 a) = κ₀ * A.orbK μK (LinDesc.desc A M hG lam α f') a := by
  intro F E _ _ _ _ _ A r τ p hG lam M μK hμK α f' hf' hαlc hαcs hα0 hcut κ₀ hκ a ha
  obtain ⟨a, rfl⟩ := ha
  letI := M.mG
  set Y := pt A hG lam 1 (a : A.K) with hY
  have hconv := (GlobalTheory.T.etaleUnitsHaarMeasureDivAbs_isHaarMeasure F E A μK hμK).2.2
    (fun t => desc A M hG lam α f' ((a : A.K) * Ring.inverse t, t) * A.etaK t)
  have hO : A.orbK μK (desc A M hG lam α f') (a : A.K) =
      ∫ s, desc A M hG lam α f' ((a : A.K) * Ring.inverse (s : A.K), (s : A.K)) * A.etaK s ∂(unitsMeas A μK) := by
    rw [hconv]; rfl
  set Φ : GL (Fin r) F → ℂ := fun g => f' (act g Y) * omega (act g Y) with hΦ
  have hΔ : Delta (inv Y) ≠ 0 := by
    rw [hY, pt_one, GlobalTheory.JR.NormalFormL.inv_sec']
    exact ((GlobalTheory.T.jacquetRallis_invK_regular_iff_isUnit F E A r τ p lam hG).2 (a : A.K)).2.2 (Units.isUnit a)
  have hΦt : IsTest Φ := (GlobalTheory.T.jacquetRallis_orbitalIntegrand_isLocallyConstantCompactSupport F E r M).1 f' hf' Y hΔ
  have hinner : ∀ s : A.Kˣ, κ₀ * (desc A M hG lam α f' ((a : A.K) * Ring.inverse (s : A.K), (s : A.K)) * A.etaK s) =
      ∫ g, Φ g * (α (g * tm A hG a⁻¹ * tm A hG s) : ℂ) ∂M.μG := by
    intro s
    rw [desc_unit_eq, ← mul_assoc, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only [hΦ]
    rw [hκ (a : A.K) (Units.isUnit a) g]
    ring
  have hc : ∀ g, Φ g ≠ 0 → ∫ s, α (g * tm A hG a⁻¹ * tm A hG s) ∂(unitsMeas A μK) = 1 := by
    intro g hg
    refine hcut g ⟨(act g Y).2.1, (act g Y).2.2.1, ?_⟩ a⁻¹
    intro h0
    apply hg
    have h1 : f' (act g Y) = 0 := h0
    simp only [hΦ, h1, zero_mul]
  rw [hO, ← integral_const_mul]
  simp_rw [hinner]
  exact ((GlobalTheory.T.fubini_cutoff_integral_generalLinear_torus) F E A r τ p hG M μK hμK α Φ hΦt hαlc hαcs hα0 (tm A hG a⁻¹) hc).symm

end GlobalTheory.JR.LinDesc
end
end

section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.WeilQuad
open scoped Pointwise

theorem isStableGauss_unique {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L) (u : A.K)
    {G G' : ℂ} (h : IsStableGauss A ψ x μ u G) (h' : IsStableGauss A ψ x μ u G') : G = G' := by
  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  obtain ⟨Λ₀, ho, hc, hG⟩ := h
  obtain ⟨Λ₁, ho', hc', hG'⟩ := h'
  have hs : ((Λ₀ ⊔ Λ₁ : AddSubgroup A.L) : Set A.L) = (Λ₀ : Set A.L) + (Λ₁ : Set A.L) := AddSubgroup.add_normal Λ₀ Λ₁
  have hO : IsOpen ((Λ₀ ⊔ Λ₁ : AddSubgroup A.L) : Set A.L) := AddSubgroup.isOpen_mono le_sup_left ho
  have hC : IsCompact ((Λ₀ ⊔ Λ₁ : AddSubgroup A.L) : Set A.L) := by rw [hs]; exact hc.add hc'
  rw [← hG _ hO hC le_sup_left, ← hG' _ hO hC le_sup_right]

theorem absK_units_mul {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] (A : Et F E) (a b : A.Kˣ) :
    A.absK ((a * b : A.Kˣ) : A.K) = A.absK a * A.absK b := by
  simp [Et.absK]

theorem absK_units_ne {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] (A : Et F E) (a : A.Kˣ) : A.absK (a : A.K) ≠ 0 := by
  simp only [Et.absK, Units.isUnit, dite_true, IsUnit.unit_of_val_units, ne_eq, NNReal.coe_eq_zero]
  exact ((Group.isUnit a).map (distribHaarChar A.K)).ne_zero

theorem gauss_transform : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ (u : A.Kˣ) (G G₁ : ℂ), IsStableGauss A ψ x μ u G → IsStableGauss A ψ x μ 1 G₁ → G = G₁ * ω u * ((A.absK u : ℂ))⁻¹ := by
  intro F E _ _ _ _ _ A ψ x μ ω hH u G G₁ hG hG₁
  have hω := hH.2.2.2.2
  by_cases hu : ∃ y, A.NL y = u
  · have h1 := GlobalTheory.T.stableQuadraticGaussIntegral_mul_norm F E A ψ x μ ω hH 1 u hu G₁ (by simpa using hG₁)
    rw [one_mul] at h1
    rw [isStableGauss_unique A ψ x μ _ hG h1, (hω u).1 hu]; ring
  · obtain ⟨ϖ, hϖ, hGϖ⟩ := GlobalTheory.T.exists_nonNorm_uniformizer_isStableGauss F E A ψ x μ ω hH G₁ hG₁
    have hps : ϖ * (ϖ⁻¹ * u) = u := mul_inv_cancel_left ϖ u
    have hs : ∃ y, A.NL y = ((ϖ⁻¹ * u : A.Kˣ) : A.K) := by
      by_contra hs
      have hm := (GlobalTheory.T.normGroupSign_mul_and_neg_one F E A ψ x μ ω hH).1 ϖ (ϖ⁻¹ * u)
      rw [hps, (hω u).2 hu, (hω ϖ).2 hϖ, (hω _).2 hs] at hm
      norm_num at hm
    have h2 := GlobalTheory.T.stableQuadraticGaussIntegral_mul_norm F E A ψ x μ ω hH ϖ (ϖ⁻¹ * u) hs _ hGϖ
    rw [hps] at h2
    rw [isStableGauss_unique A ψ x μ _ hG h2, (hω u).2 hu]
    have e1 := absK_units_ne A ϖ
    have e2 := absK_units_ne A (ϖ⁻¹ * u)
    conv_rhs => rw [← hps, absK_units_mul]
    push_cast
    field_simp

end GlobalTheory.JR.WeilQuad
end
end

section

namespace GlobalTheory.TopWindow

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

theorem sg_cast_eq (l n : ℕ) (h : ZMod n → ℕ) (i : ZMod n) :
    (GlobalTheory.PhiGam.sg l h i : ℤ) = tableLineDegreeTwo.sg n l h i := by
  have h0 : (0 : ℝ) ≤ ∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1) :=
    tsum_nonneg fun j => by positivity
  simp only [GlobalTheory.PhiGam.sg, tableLineDegreeTwo.sg, Formalism.WachCohomologyFacts.V2.sgN]
  exact Int.natCast_floor_eq_floor h0

theorem inWin_iff (typ : Bool) (h η : ℕ) (u : ℤ) (h1 : 1 ≤ u) (h2 : u ≤ (h : ℤ) - 1) :
    InWin typ h η u ↔ Formalism.WachCohomologyFacts.V2.InWinN typ h η u := by
  unfold InWin Formalism.WachCohomologyFacts.V2.InWinN
  cases typ <;> simp [h1, h2]

theorem exists_topData_of_positionHyps : ∀ (l n t r : ℕ) [NeZero n] (h w η : ZMod n → ℕ)
    (typ : ZMod n → Bool) (U : ZMod n → Multiset ℤ), 2 ≤ l → 1 ≤ t →
    (∀ i, Multiset.card (U i) = r) → tableLineDegreeTwo.PositionHyps l n t h w η typ U →
    ∃ Dt : TopData n r, Dt.t = t ∧
      (∀ i, Dt.w i = w i ∧ Dt.U i = U i ∧ ∀ a, ((Dt.Ut i).count a : ℤ) = tableLineDegreeTwo.jTil U w t i a) ∧
      Dt.T1 l ∧ Dt.T2 l ∧ Dt.T3 l := by
  intro l n t r _ h w η typ U _ ht hc hS
  unfold tableLineDegreeTwo.PositionHyps at hS
  have hsg : ∀ i, (GlobalTheory.PhiGam.sg l h i : ℤ) = tableLineDegreeTwo.sg n l h i := fun i => sg_cast_eq l n h i
  obtain ⟨Dt, hDt, hw, h1, h2, h3⟩ := exists_topData l n t r h η typ (fun i => (w i : ℤ)) U
    (fun i => by obtain ⟨-, hw1, hw2, -⟩ := hS i; omega)
    (fun i => by
      obtain ⟨-, hw1, hw2, hG, hB, -⟩ := hS i
      by_cases hc : typ i = true
      · have := hG hc; omega
      · have := hB (by simpa using hc); omega)
    ht hc (fun i => (hS i).1)
    (fun i β hβ1 hβ2 => by
      obtain ⟨-, hw1, hw2, hG, hB, -⟩ := hS i
      refine ⟨by omega, by omega, ?_⟩
      unfold InWin
      split_ifs with hc
      · have := hG hc; omega
      · have := hB (by simpa using hc); omega)
    (fun i => by have := (hS i).2.2.2.2.2.1; have := hsg i; omega)
    (fun i u hu hin β hβ1 hβ2 => by
      have hr := (hS i).1 u hu
      have hlow := (hS i).2.2.2.2.2.2.1 u
        (by
          classical
          unfold tableLineDegreeTwo.lows
          exact Multiset.mem_filter.2 ⟨hu, (inWin_iff _ _ _ _ hr.1 hr.2).1 hin⟩) β
        (by rw [Formalism.WachCohomologyFacts.Top.GlobalTheory, Finset.mem_Icc]; omega)
      rw [hsg i]
      exact hlow)
    (fun i u hu hin y hy1 hy2 => by
      have hr := (hS i).1 u hu
      have hT := (hS i).2.2.2.2.2.2.2 u
        (by
          classical
          unfold Formalism.WachCohomologyFacts.V2.ClN
          exact Multiset.mem_filter.2 ⟨hu, fun h' => hin ((inWin_iff _ _ _ _ hr.1 hr.2).2 h')⟩) y
        (by have := hsg i; omega) (by have := hsg i; omega)
      intro hmod
      exact hT ((ZMod.intCast_eq_intCast_iff _ _ _).2 hmod))
  refine ⟨Dt, hDt, fun i => ⟨(hw i).1, (hw i).2.1, fun a => ?_⟩, h1, h2, h3⟩
  rw [(hw i).2.2 a]
  unfold tableLineDegreeTwo.jTil
  split_ifs <;> omega

end GlobalTheory.TopWindow
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.blochKato_reductions_orthogonal_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), Formalism.MainNotions.N.bkACore (P.PD K) → ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDR (P.PD K) A.ρ → IsDualLat1 (P.PD K) LA LA' m → ∀ (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)), ∀ c ∈ HfQ (P.PD K) LA _ hI, ∀ c' ∈ HfQ (P.PD K) LA' _ hI', CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r c c') := by
  first | exact @GlobalTheory.BKOrthRed.cupQ_cobO_of_bkA | exact GlobalTheory.BKOrthRed.cupQ_cobO_of_bkA | (intros; apply GlobalTheory.BKOrthRed.cupQ_cobO_of_bkA <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.cup_divisible_image_coboundary_iff_finite_level : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (ϖ : O) (r : ℕ) (d : ↥(latticeCocycles LA)) (c' : ↥(GK K) → ↥LA'.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)), CobO (P.PD K) L1 (cupLD LA' m (d : ↥(GK K) → A.V) (fun g => GlobalTheory.BKFinLevel.ioL LA' ϖ r (c' g))) ↔ CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r (redT LA _ d) c') := by
  first | exact @GlobalTheory.BKFinLevel.cobO_cupLD_ioL_iff | exact GlobalTheory.BKFinLevel.cobO_cupLD_ioL_iff | (intros; apply GlobalTheory.BKFinLevel.cobO_cupLD_ioL_iff <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.latticeQuotientToDivisibleQuotient_mem_cocycles : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (c : ↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), c ∈ quotientCocycles LA _ hI → (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (c g)) ∈ divisibleCocycles LA := by
  first | exact @GlobalTheory.BKFinLevelCocycle.ioL_mem_Z1D | exact GlobalTheory.BKFinLevelCocycle.ioL_mem_Z1D | (intros; apply GlobalTheory.BKFinLevelCocycle.ioL_mem_Z1D <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.finite_level_cup_swap_coboundary_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), ∀ s ∈ quotientCocycles LA _ hI, ∀ d : ↥(latticeCocycles LA'), CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r s (redT LA' _ d)) ↔ CobO (P.PD K) L1 (cupLD LA m.flip (d : ↥(GK K) → A'.V) (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (s g))) := by
  first | exact @GlobalTheory.BKSwapCup.cobO_cupQ_iff | exact GlobalTheory.BKSwapCup.cobO_cupQ_iff | (intros; apply GlobalTheory.BKSwapCup.cobO_cupQ_iff <;> assumption)
end
