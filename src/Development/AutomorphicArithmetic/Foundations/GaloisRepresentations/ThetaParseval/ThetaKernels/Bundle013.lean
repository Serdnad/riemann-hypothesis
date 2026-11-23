module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle004
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle007
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
theorem _root_.GlobalTheory.T.unitary_character_trivial_of_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ ν : Formalism.IndefR.DatumF.GAF σ J →* Circle, Continuous ν → (∀ γ ∈ Formalism.IndefR.DatumF.GQF σ J, ν γ = 1) →
        (∀ e, Formalism.IndefR.DatumF.IsSplitIdemF σ e → ∀ g, Formalism.IndefR.DatumF.SuppAtF σ e J g → ν g = 1) → ∀ g, ν g = 1 := by
  first | exact @_root_.PositivityTheory.ThKW.unitary_character_trivial_global | exact _root_.PositivityTheory.ThKW.unitary_character_trivial_global | (intros; apply _root_.PositivityTheory.ThKW.unitary_character_trivial_global <;> assumption)
end
end

section



section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

theorem _root_.GlobalTheory.T.archimedean_chart_gaussian_vector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ p : GAF σ JS × GAF σ JT, (mMF σ JS JT θ p)ᴴ * HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) * mMF σ JS JT θ p = HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) := by
  first | exact @_root_.GlobalTheory.RealWeilF.mMF_unitary_k | exact _root_.GlobalTheory.RealWeilF.mMF_unitary_k | (intros; apply _root_.GlobalTheory.RealWeilF.mMF_unitary_k <;> assumption)
end
end

section



section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

theorem _root_.GlobalTheory.T.continuous_moment_map : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
      (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → Continuous (mMF σ JS JT θ) := by
  first | exact @_root_.GlobalTheory.RealWeilF.MCont.continuous_mMF_k | exact _root_.GlobalTheory.RealWeilF.MCont.continuous_mMF_k | (intros; apply _root_.GlobalTheory.RealWeilF.MCont.continuous_mMF_k <;> assumption)
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

theorem _root_.GlobalTheory.T.eta_character_archimedean_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ η : (AF F)ˣ →* Circle, IsEtaF E η → ∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) →
      (η a : ℂ) = ∏ w, piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) /
        ((‖piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)‖ : ℝ) : ℂ) := by
  first | exact @_root_.GlobalTheory.EtaSignReal.eta_eq_prod_sign_k | exact _root_.GlobalTheory.EtaSignReal.eta_eq_prod_sign_k | (intros; apply _root_.GlobalTheory.EtaSignReal.eta_eq_prod_sign_k <;> assumption)
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

theorem _root_.GlobalTheory.T.extend_character_to_norm_group : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ lam : (AF F)ˣ →* Circle, Continuous lam →
      (∀ a : Fˣ, lam (Units.map (algebraMap F (AF F)).toMonoidHom a) = 1) →
      (∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1) →
      ∃ lam' : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF lam' ∧
        (∀ z : (AF F ⊗[F] E)ˣ, At (evI F) ((z : AF F ⊗[F] E) - 1) → lam' z = 1) ∧
        ∀ a, lam' (idFF F E a) = lam a := by
  first | exact @_root_.GlobalTheory.HeckeExtend.exists_extend_hecke_k | exact _root_.GlobalTheory.HeckeExtend.exists_extend_hecke_k | (intros; apply _root_.GlobalTheory.HeckeExtend.exists_extend_hecke_k <;> assumption)
end
end

section



section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

theorem _root_.GlobalTheory.T.hermitian_form_matrix_selfadjoint : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1))ᴴ = HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) ∧ (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1)).det ≠ 0 := by
  first | exact @_root_.GlobalTheory.RealWeilF.HMF_herm_det_k | exact _root_.GlobalTheory.RealWeilF.HMF_herm_det_k | (intros; apply _root_.GlobalTheory.RealWeilF.HMF_herm_det_k <;> assumption)
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

theorem _root_.GlobalTheory.T.theta_function_integrable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ (k : ℕ) (L' : (Fin k → ℝ) →+ Formalism.IndefR.DatumF.WOF F E nS nT), Continuous L' → (∀ t, (L' t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ w : Formalism.IndefR.DatumF.WOF F E nS nT, ContDiff ℝ ∞ fun x => deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L' x)) 0 := by
  first | exact @_root_.GlobalTheory.ThetaLineSmoothF.contDiff_deriv_heisOF_line_k | exact _root_.GlobalTheory.ThetaLineSmoothF.contDiff_deriv_heisOF_line_k | (intros; apply _root_.GlobalTheory.ThetaLineSmoothF.contDiff_deriv_heisOF_line_k <;> assumption)
end
end

section



section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AdelicU GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Filter Topology
namespace Tw.VacIndic
open _root_.GlobalTheory
variable {F : Type} [Field F] [NumberField F]
end Tw.VacIndic
namespace Tw.VacIndic
open _root_.GlobalTheory
variable {F : Type} [Field F] [NumberField F]
end Tw.VacIndic
namespace Tw.VacIndic
open _root_.GlobalTheory
variable {F : Type} [Field F] [NumberField F]
end Tw.VacIndic
namespace Tw.VacIndic
open _root_.GlobalTheory
variable {F : Type} [Field F] [NumberField F]
section AtLemmas
variable {v : HeightOneSpectrum (𝓞 F)}
end AtLemmas
end Tw.VacIndic
namespace Tw.VacIndic
open _root_.GlobalTheory
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {n d : ℕ}
end Tw.VacIndic
namespace Tw.VacIndic
open _root_.GlobalTheory
section SympAdd
variable {R E' : Type} [CommRing R] [CommRing E'] [Algebra R E'] (c : E' →ₐ[R] E') (ξ : E')
  {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α E') (JB : Matrix β β E')
end SympAdd
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end Tw.VacIndic
namespace Tw.VacIndic
open _root_.GlobalTheory
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {n d : ℕ}
end Tw.VacIndic
namespace Tw.VacIndic
open _root_.GlobalTheory
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem isVac_indicator_of_theta_k {σ : E →ₐ[F] E} (B : Base F E) (hB : _root_.UpperTheory.TP.W.GoodK σ B) {n d : ℕ} (X : Spc F E n)
    (Y : Spc F E d) (r s r' s' : ℕ) (hX : X.IsHerm σ B r s) (hY : Y.IsSkew σ B r' s')
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d))
    (hrat : ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k)))
    (hθ : ∃ θ : 𝓞 E, (θ : E) + σ θ = 1) :
    ∀ᶠ v in Filter.cofinite, Model.IsVac (Model.mk (σ := σ) (X := X) (W := Y) co (fun _ => 0) 0 ∅) B.ψ v
      (Set.indicator {x | ∀ k, x k ∈ v.adicCompletionIntegers F} 1) := by
  classical
  obtain ⟨θ, hθ⟩ := hθ
  obtain ⟨G, hG⟩ := exists_gen X.L Y.L hX.lat.toIsLattice hY.lat.toIsLattice
  choose yc zc hc using hrat
  have e1 := eventually_psiLoc_eq_one B.ψ hB.std.1
  have e2 := eventually_int (F := F) (1 / 2)
  have e3 : ∀ᶠ v in cofinite, ∀ g ∈ G, ∀ k, algebraMap F (Fv F v) (yc g k) ∈ v.adicCompletionIntegers F ∧
      algebraMap F (Fv F v) (zc g k) ∈ v.adicCompletionIntegers F := by
    refine (Filter.eventually_all_finset G).2 fun g _ => Filter.eventually_all.2 fun k => ?_
    exact (eventually_int (yc g k)).and (eventually_int (zc g k))
  have e4 : ∀ᶠ v in cofinite, ∀ g ∈ G, ∀ g' ∈ G,
      algebraMap F (Fv F v) (symp σ (θ : E) X.J Y.J g g') ∈ v.adicCompletionIntegers F := by
    refine (Filter.eventually_all_finset G).2 fun g _ => (Filter.eventually_all_finset G).2 fun g' _ => ?_
    exact eventually_int _
  filter_upwards [e1, e2, e3, e4] with v h1 h2 h3 h4
  set O := v.adicCompletionIntegers F
  set T : Set (Matrix (Fin n) (Fin d) (AE F E)) :=
    {z | ∃ a : AF F, At (evFin F v) a ∧ evFin F v a ∈ O ∧ ∃ g ∈ G, z = a • incM F g} with hT
  have hA : ∀ z ∈ AddSubgroup.closure T, ∀ k, At (evFin F v) ((co.e z).1 k) ∧ At (evFin F v) ((co.e z).2 k) ∧
      evFin F v ((co.e z).1 k) ∈ O ∧ evFin F v ((co.e z).2 k) ∈ O := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hai, g, hg, rfl⟩ := hz
      intro k
      rw [map_smul, hc g]
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul, evFin_algebraMap]
      exact ⟨at_mul_right ha, at_mul_right ha, mul_mem hai (h3 g hg k).1, mul_mem hai (h3 g hg k).2⟩
    | zero =>
      intro k
      simp only [map_zero, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply]
      exact ⟨at_zero, at_zero, zero_mem _, zero_mem _⟩
    | add z z' _ _ h h' =>
      intro k
      simp only [map_add (f := _), Prod.fst_add, Prod.snd_add, Pi.add_apply]
      exact ⟨at_add (h k).1 (h' k).1, at_add (h k).2.1 (h' k).2.1, add_mem (h k).2.2.1 (h' k).2.2.1,
        add_mem (h k).2.2.2 (h' k).2.2.2⟩
    | neg z _ h =>
      intro k
      simp only [map_neg, Prod.fst_neg, Prod.snd_neg, Pi.neg_apply]
      exact ⟨at_neg (h k).1, at_neg (h k).2.1, neg_mem (h k).2.2.1, neg_mem (h k).2.2.2⟩
  set S := symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F Y.J) with hS
  have hB1 : ∀ z ∈ T, ∀ z' ∈ AddSubgroup.closure T, At (evFin F v) (S z z') ∧ evFin F v (S z z') ∈ O := by
    intro z hz z' hz'
    obtain ⟨a, ha, hai, g, hg, rfl⟩ := hz
    induction hz' using AddSubgroup.closure_induction with
    | mem z' hz' =>
      obtain ⟨a', ha', hai', g', hg', rfl⟩ := hz'
      rw [hS, symp_smul_incM, map_mul, map_mul, evFin_algebraMap]
      exact ⟨at_mul_right (at_mul_right ha), mul_mem (mul_mem hai hai') (h4 g hg g' hg')⟩
    | zero => rw [hS, symp_zero_right, map_zero]; exact ⟨at_zero, zero_mem _⟩
    | add z₁ z₂ _ _ h h' => rw [hS, symp_add_right, map_add (f := _)]; exact ⟨at_add h.1 h'.1, add_mem h.2 h'.2⟩
    | neg z₁ _ h => rw [hS, symp_neg_right, map_neg]; exact ⟨at_neg h.1, neg_mem h.2⟩
  have hB2 : ∀ z ∈ AddSubgroup.closure T, ∀ z' ∈ AddSubgroup.closure T,
      At (evFin F v) (S z z') ∧ evFin F v (S z z') ∈ O := by
    intro z hz z' hz'
    induction hz using AddSubgroup.closure_induction with
    | mem z hz => exact hB1 z hz z' hz'
    | zero => rw [hS, symp_zero_left, map_zero]; exact ⟨at_zero, zero_mem _⟩
    | add z₁ z₂ _ _ h h' => rw [hS, symp_add_left, map_add (f := _)]; exact ⟨at_add h.1 h'.1, add_mem h.2 h'.2⟩
    | neg z₁ _ h => rw [hS, symp_neg_left, map_neg]; exact ⟨at_neg h.1, neg_mem h.2⟩
  refine ⟨indicator_int_mem_SB v, indicator_int_ne_zero v, θ, hθ, fun γ hγ => ?_⟩
  have hγ' := latAtV_le X Y G hG v hγ
  have hval : B.ψ (⅟(2 : AF F) * S γ γ) = 1 := by
    have hat := hB2 γ hγ' γ hγ'
    rw [psi_of_at B.ψ (at_mul_left hat.1)]
    refine h1 _ ?_
    rw [map_mul, invOf_two_eq, evFin_algebraMap]
    exact mul_mem h2 hat.2
  rw [← hS, hval, one_smul]
  exact acts_indicator co B.ψ v γ h1 h2 (fun k => (hA γ hγ' k).1) (fun k => (hA γ hγ' k).2.1)
    (fun k => (hA γ hγ' k).2.2.1) (fun k => (hA γ hγ' k).2.2.2)
end Tw.VacIndic
namespace Tw.VacIndic
open _root_.GlobalTheory
theorem eventually_isVac_indicator_k : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d)), (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k))) →
    ∀ᶠ v in Filter.cofinite, Model.IsVac (Model.mk (σ := σ) (X := X) (W := Y) co (fun _ => 0) 0 ∅) B.ψ v
      (Set.indicator {x | ∀ k, x k ∈ v.adicCompletionIntegers F} 1) := by
  intro F E _ _ _ _ _ σ B hB n d X Y r s r' s' hX hY co hrat
  exact _root_.Tw.VacIndic.isVac_indicator_of_theta_k B hB X Y r s r' s' hX hY co hrat (_root_.Tw.exists_int_add_conj_eq_one_of_base_good_k B hB)
end Tw.VacIndic
end
end

section



section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.inert_completion_isField : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → IsField (Fv F v ⊗[F] E) := by
  first | exact @_root_.GlobalTheory.InertTensorField.isField_tensor_of_isInertAt_k | exact _root_.GlobalTheory.InertTensorField.isField_tensor_of_isInertAt_k | (intros; apply _root_.GlobalTheory.InertTensorField.isField_tensor_of_isInertAt_k <;> assumption)
end
end

section



section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
theorem _root_.GlobalTheory.T.nonempty_algHom_or_exists_inert_of_goodK : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ v : Pl F, Nonempty (E →ₐ[F] Fv F v) ∨ ∃ w : HeightOneSpectrum (𝓞 E), Formalism.UG.IsInertAt F E v w := by
  first | exact @_root_.GlobalTheory.KFinLoc.split_or_inert_k | exact _root_.GlobalTheory.KFinLoc.split_or_inert_k | (intros; apply _root_.GlobalTheory.KFinLoc.split_or_inert_k <;> assumption)
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

theorem _root_.GlobalTheory.T.theta_integral_unfolding : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ g : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ,
      (∃ U : AddSubgroup (Formalism.IndefR.DatumF.WOF F E nS nT), IsOpen (U : Set (Formalism.IndefR.DatumF.WOF F E nS nT)) ∧
        ∀ u ∈ U, u.map (Formalism.IndefR.DatumF.infPartF F E) = 0 → Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (u) g = g) →
      (∀ (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.DatumF.WOF F E nS nT), Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
        ∀ w : Formalism.IndefR.DatumF.WOF F E nS nT, ContDiff ℝ ∞ fun x => g (w + L x)) →
      Continuous g := by
  first | exact @_root_.GlobalTheory.WeilContF.continuous_of_level_real_k | exact _root_.GlobalTheory.WeilContF.continuous_of_level_real_k | (intros; apply _root_.GlobalTheory.WeilContF.continuous_of_level_real_k <;> assumption)
end
end

section



section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem Tw.RatDarboux.exists_rational_darboux_of_isGood_k : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∃ co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d), ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k)) :=
  fun B hB _ _ X Y r s r' s' hX hY => _root_.Tw.RatDarboux.exists_rational_darboux_k _ B X Y r s r' s' hB hX hY
end
end
