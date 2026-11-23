module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle015
public import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.Bundle001
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1391
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1393
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1476
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1349
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift

theorem overK_of_sqrt {D : D7} (σ : D.what₂.LL →+* ℂ)
    (h : σ (D.embE D.host.sqrtMinusD) = D.what₂.embLL (D.embE D.host.sqrtMinusD)) : OverK σ := by
  intro x hx
  have hx' : x ∈ IntermediateField.adjoin ℚ {D.host.sqrtMinusD} := hx
  clear hx
  induction hx' using IntermediateField.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact h
  | algebraMap q => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  | inv x _ hx => rw [map_inv₀, map_inv₀, map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, map_mul, hx, hy]

theorem embLL_embE (D : D7) (x : D.host.E) : D.what₂.embLL (D.embE x) = D.host.φ₀ x :=
  RingHom.congr_fun D.embE_φ₀ x

theorem sqrtMinusD_sq (D : D7) : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) :=
  D.host.sqd_sq

theorem overK_conj {D : D7} (σ : D.what₂.LL →+* ℂ) (h : ¬ OverK σ) : OverK ((starRingEnd ℂ).comp σ) := by
  apply overK_of_sqrt
  have h0 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have h1 : σ (D.embE D.host.sqrtMinusD) ^ 2 = D.what₂.embLL (D.embE D.host.sqrtMinusD) ^ 2 := by
    rw [← map_pow, ← map_pow, ← map_pow, ← map_pow, sqrtMinusD_sq]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2
  · exact absurd (overK_of_sqrt σ h2) h
  · rw [RingHom.comp_apply, h2, embLL_embE, h0]; simp

theorem exists_psi_of_overK {D : D7} (σ : D.what₂.LL →+* ℂ) (h : OverK σ) :
    ∃ g ∈ D.R.Psi, ∀ τ, labE σ τ = D.host.emb (g * (D.eTau τ).1) := by
  obtain ⟨g0, h0⟩ := (factEmb D.R D.host).1.2 (σ.comp D.embE)
  refine ⟨g0, ((factEmb D.R D.host).2 _).1 ?_, fun τ => ?_⟩
  · have h1 := h D.host.sqrtMinusD (IntermediateField.mem_adjoin_simple_self ℚ _)
    have h2 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
    rw [h0]
    exact h1.trans ((embLL_embE D _).trans h2)
  · rw [ConjReading.emb_mul, h0]; rfl

theorem labels_overK : ∀ {D : D7} (σ : D.what₂.LL →+* ℂ),
    (OverK σ → Function.Bijective (lab (D := D) σ) ∧ ∀ ρ, labE σ (lab σ ρ) = tauE D ρ) ∧
      (¬ OverK σ → OverK ((starRingEnd ℂ).comp σ)) := by
  intro D σ
  refine ⟨fun h => ?_, overK_conj σ⟩
  obtain ⟨g, hg, key⟩ := exists_psi_of_overK σ h
  have inj := (factEmb D.R D.host).1.1
  have main : ∀ ρ, labE σ (lab σ ρ) = tauE D ρ := by
    intro ρ
    have hs : labE σ (lab σ ρ) = tauE D ρ ∨ labE σ (lab σ ρ) = (starRingEnd ℂ).comp (tauE D ρ) := by
      unfold lab; rw [dite_eq_left (ConjReading.lab_exists σ ρ)]; exact (ConjReading.lab_exists σ ρ).choose_spec
    refine hs.resolve_right fun h' => ?_
    rw [key] at h'
    exact ConjReading.conj_not_mem D ρ _ h' (Subgroup.mul_mem _ hg (D.eTau _).2)
  refine ⟨⟨fun ρ ρ' e => ?_, fun τ => ?_⟩, main⟩
  · have e' : tauE D ρ = tauE D ρ' := by rw [← main, ← main, e]
    exact D.eTau.injective (Subtype.ext (inj e'))
  · refine ⟨D.eTau.symm ⟨g * (D.eTau τ).1, Subgroup.mul_mem _ hg (D.eTau τ).2⟩, ?_⟩
    have e := main (D.eTau.symm ⟨g * (D.eTau τ).1, Subgroup.mul_mem _ hg (D.eTau τ).2⟩)
    rw [key, tauE, Equiv.apply_symm_apply] at e
    exact D.eTau.injective (Subtype.ext (mul_left_cancel (inj e)))

end GlobalTheory.GalLift
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit GlobalTheory.TowU
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

noncomputable section

namespace GlobalTheory.WeilEx.Jac

section Alg

variable {R : Type} [CommRing R] {A : Type} [CommRing A] [Algebra R A] {α β ν X : Type} [Fintype β] [DecidableEq β]
  [AddCommGroup X] [Module R X] {e : ν ⊕ ν ≃ α}


variable [Invertible (2 : R)] {D : Matrix α β A ≃ₗ[R] X × X}
  (hΔ : ∀ w, GlobalTheory.SWLit.LinAct.Del e w → (D w).1 = 0)
  (hN : ∀ w, GlobalTheory.SWLit.LinAct.Nab e w → (D w).2 = 0)
include hΔ hN

end Alg

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem absE_det_unitary {k : ℕ} {J : Matrix (Fin k) (Fin k) E} (hJ : J.det ≠ 0) (g : UA σ J) :
    absE F E (Matrix.GeneralLinearGroup.det (g : GL (Fin k) (AE F E))) = 1 := by
  set d := Matrix.GeneralLinearGroup.det (g : GL (Fin k) (AE F E)) with hd
  have hJu : IsUnit (incM F J).det := by
    have e0 : (incM F J).det = inclR (F := F) (AF F) J.det := (RingHom.map_det _ _).symm
    rw [e0]
    exact (isUnit_iff_ne_zero.2 hJ).map _
  have h := congrArg Matrix.det (show ((g : GL (Fin k) (AE F E)) : Matrix (Fin k) (Fin k) (AE F E))ᵀ * incM F J *
    ((g : GL (Fin k) (AE F E)) : Matrix (Fin k) (Fin k) (AE F E)).map (cA σ) = incM F J from g.2)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    show (((g : GL (Fin k) (AE F E)) : Matrix (Fin k) (Fin k) (AE F E)).map (cA σ)).det =
      cA σ ((g : GL (Fin k) (AE F E)) : Matrix (Fin k) (Fin k) (AE F E)).det from
      ((cA σ).toRingHom.map_det _).symm] at h
  have h2 : (d : AE F E) * cA σ d = 1 := by
    rw [hd, Matrix.GeneralLinearGroup.val_det_apply]
    exact hJu.mul_left_cancel (by linear_combination h)
  have hc : Units.map (cA σ : AE F E →* AE F E) d = conjUnit σ d := by
    ext
    simp only [Units.coe_map, MonoidHom.coe_ofClass]
    rfl
  have h3 : d * Units.map (cA σ : AE F E →* AE F E) d = 1 := Units.ext (by simpa using h2)
  have h4 : absE F E d * absE F E d = 1 := by
    nth_rewrite 2 [← absE_conjUnit σ d]
    rw [← hc, ← map_mul, h3, map_one]
  apply NNReal.coe_injective
  have h6 : (absE F E d : ℝ) * absE F E d = 1 := by exact_mod_cast h4
  have h7 : (0 : ℝ) ≤ absE F E d := (absE F E d).2
  push_cast
  exact le_antisymm (by nlinarith) (by nlinarith)

end Main

end GlobalTheory.WeilEx.Jac
end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

open Matrix
namespace GlobalTheory.AdelMatLatRight


open NumberField IsDedekindDomain in
open Matrix in
theorem _root_.GlobalTheory.AdelMatLatRight.transpose_mem_latAtV {F E : Type} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (w : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) :
    ∀ γ ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y w, γᵀ ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Y X w := by
  intro γ hγ
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV at hγ ⊢
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hai, x, hx, y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, hai, y, hy, x, hx, ?_⟩
    rw [transpose_smul]
    congr 1
    ext i j
    simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, vecMulVec_apply, mul_comm]
  | zero => simpa using zero_mem _
  | add u v _ _ hu hv => simpa [transpose_add] using add_mem hu hv
  | neg u _ hu => simpa [transpose_neg] using neg_mem hu

theorem almost_all_stable_right : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ)
    (X : Spc F E n) (Y : Spc F E d), Y.L.IsFullLattice E → ∀ N : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    Set.Finite {w : Pl (F := F) | ¬ ∀ γ ∈ latAtV X Y w, γ * Matrix.transpose N ∈ latAtV X Y w} := by
  intro F E _ _ _ _ _ n d X Y hY N
  refine (GlobalTheory.AdelMatLat.almost_all_stable F E d n Y X hY N).subset fun w hw h => hw fun γ hγ => ?_
  have h1 := transpose_mem_latAtV Y X w _ (h _ (transpose_mem_latAtV X Y w γ hγ))
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose] at h1

end GlobalTheory.AdelMatLatRight

end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem _root_.GlobalTheory.T.supportedAtInfinity_adele_eq_zero_of_complexComponents : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (emb : ∀ w : InfinitePlace F, EmbOver E w) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) z →
    (∀ w, piInf (emb w) z = 0) → z = 0 := by
  first | exact @GlobalTheory.AdeleInfInj.eq_zero_of_piInf_eq_zero | exact GlobalTheory.AdeleInfInj.eq_zero_of_piInf_eq_zero | (intros; apply GlobalTheory.AdeleInfInj.eq_zero_of_piInf_eq_zero <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.isUnit_det_gram_of_hermitianSelfDualLatticeSpace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n : ℕ) (X : Spc F E n) (r s : ℕ), X.IsHerm σ B r s → IsUnit X.J.det := by
  first | exact @GlobalTheory.isUnit_det_of_isHerm | exact GlobalTheory.isUnit_det_of_isHerm | (intros; apply GlobalTheory.isUnit_det_of_isHerm <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.integral_injectiveSubspace_compactOpen_const_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ],
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), Function.Injective j →
    ∀ c : ℂ, c ≠ 0 → ∀ U : Set ((κ → Fv F v) × (κ → Fv F v)), IsOpen U → IsCompact U → 0 ∈ U →
    ∫ y, U.indicator (fun _ => c) (j y) ∂ν ≠ 0 := by
  first | exact @GlobalTheory.integral_indicator_preimage_injective_ne_zero | exact GlobalTheory.integral_indicator_preimage_injective_ne_zero | (intros; apply GlobalTheory.integral_indicator_preimage_injective_ne_zero <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.siegelParabolic_leviInverse_quotient_det_norm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), J.det ≠ 0 →
    ∀ (v : Pl (F := F)) (p : UG (cA σ) (dbl (incM F J))) (t : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evFin F v) ((p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) →
    (p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * diagCols (Fin n) = diagCols (Fin n) * t.val →
    At (evFin F v) (t.val.det - 1) ∧ At (evFin F v) (Algebra.norm (AF F) t.val.det - 1) ∧
      ∃ s : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), s.val = ((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).toBlocks₁₁ - ((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).toBlocks₂₁ ∧
        Algebra.norm (AF F) s.val.det = Algebra.norm (AF F) t.val.det := by
  first | exact @GlobalTheory.InertLagLevi.levi_det | exact GlobalTheory.InertLagLevi.levi_det | (intros; apply GlobalTheory.InertLagLevi.levi_det <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass

theorem _root_.GlobalTheory.T.discrete_rational_points_subgroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (N : Subgroup (UA σ J)), DiscreteTopology ((ratU σ J).subgroupOf N) := by
  first | exact @GlobalTheory.RatUDiscreteSub.discreteTopology_subgroupOf | exact GlobalTheory.RatUDiscreteSub.discreteTopology_subgroupOf | (intros; apply GlobalTheory.RatUDiscreteSub.discreteTopology_subgroupOf <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU


theorem _root_.GlobalTheory.T.exists_hyperbolicPair_selfDualLattice_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n : ℕ) (Y : Spc F E n) (r s : ℕ), Y.IsHerm σ B r s →
    ∀ x : Fin n → E, x ≠ 0 → form σ Y.J x x = 0 →
    ∃ x' y : Fin n → E, form σ Y.J x' x' = 0 ∧ form σ Y.J y y = 0 ∧ form σ Y.J x' y = 1 ∧
      (∀ z ∈ Y.L, form σ Y.J z y • x' ∈ Y.L ∧ form σ Y.J z x' • y ∈ Y.L) ∧
      ∀ v : B.P, ((∀ c : E, c • x' ∈ Y.L → Valued.v (B.τ v c) ≤ 1) ∧ ∃ c : E, c • x' ∈ Y.L ∧ Valued.v (B.τ v c) = 1) ∧
        ((∀ c : E, c • y ∈ Y.L → Valued.v (B.τ v c) ≤ 1) ∧ ∃ c : E, c • y ∈ Y.L ∧ Valued.v (B.τ v c) = 1) := by
  first | exact @GlobalTheory.HypPairLat.exists_pair | exact GlobalTheory.HypPairLat.exists_pair | (intros; apply GlobalTheory.HypPairLat.exists_pair <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.exists_basis_with_dual_basis_in_hermitian_lattice_away_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) {n r s : ℕ} (X : Spc F E n), X.IsHerm σ B r s → ∀ v : Pl (F := F),
    ∃ f p : Fin n → Fin n → E, (∀ k, ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ algebraMap F E (t : F) • f k ∈ X.L) ∧
      (∀ k, ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ algebraMap F E (t : F) • p k ∈ X.L) ∧
      ∀ k l, form σ X.J (p k) (f l) = if k = l then 1 else 0 := by
  first | exact @GlobalTheory.HermLocDualBasis.exists_locDualBasis | exact GlobalTheory.HermLocDualBasis.exists_locDualBasis | (intros; apply GlobalTheory.HermLocDualBasis.exists_locDualBasis <;> assumption)
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem _root_.GlobalTheory.T.archimedeanWeilOperator_transports_heisenbergLineDerivative : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M.IsWeil B.ψ χX χW om →
    ∀ g ∈ UAt σ X (evI F), ∀ h ∈ UAt σ W (evI F), ∀ T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d),
    (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, h)) f (T f)) → (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f)) →
    ∀ u, At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) f f₁ →
      ActsD (evI F) (M.heisLine B.ψ (mat g * u * (mat h).transpose)) (T f) (T f₁) := by
  first | exact @GlobalTheory.HeisTransport.actsD_heisLine_transport | exact GlobalTheory.HeisTransport.actsD_heisLine_transport | (intros; apply GlobalTheory.HeisTransport.actsD_heisLine_transport <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.normalizedAbsDet_mul_integral_comp_mulVec_finitePlace : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)),
    @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ (T : GL (Fin N) (Fv F v)) (f : (Fin N → Fv F v) → ℂ),
      ((GlobalTheory.SplitWeil.nabs (Fv F v) (Matrix.GeneralLinearGroup.det T) : ℝ) : ℂ) * ∫ y, f (T.val *ᵥ y) ∂ν = ∫ y, f y ∂ν := by
  first | exact @GlobalTheory.InertLagChar.nabs_det_mul_integral_comp_mulVec | exact GlobalTheory.InertLagChar.nabs_det_mul_integral_comp_mulVec | (intros; apply GlobalTheory.InertLagChar.nabs_det_mul_integral_comp_mulVec <;> assumption)
end
