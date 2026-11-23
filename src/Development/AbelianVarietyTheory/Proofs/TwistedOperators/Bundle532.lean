module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle459
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle423
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryPreservesPolynomialFock
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle390
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle200
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle192
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle228
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle422
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle358
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle400
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle424
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1782
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle512
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle191
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle476
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix
open scoped Classical

noncomputable section

namespace GlobalTheory.RealLieFockX

theorem lineGroupX : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        (∀ (s t : ℝ) (f : SInf F (Fin n × Fin d)), T (s + t) f = T s (T t f)) ∧ ∀ f : SInf F (Fin n × Fin d), T 0 f = f := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om _ _ _ _ _ _ _ _ _ _ γ _ T hA
  obtain ⟨r₀, hR, hinj⟩ := GlobalTheory.ArchUniq.exists_admissible_finite_factor (F := F) (Fin n × Fin d)
  refine ⟨fun s t f => hinj _ _ ?_, fun f => hinj _ _ ?_⟩
  · rw [← hA (s + t) f r₀ (hR f), ← hA s (T t f) r₀ (hR _), ← hA t f r₀ (hR f), ofAdd_add, map_mul,
      show (γ (Multiplicative.ofAdd s) * γ (Multiplicative.ofAdd t), (1 : UA σ W.J)) =
        (γ (Multiplicative.ofAdd s), (1 : UA σ W.J)) * (γ (Multiplicative.ofAdd t), 1) by
          simp [Prod.mk_mul_mk], map_mul, Module.End.mul_apply]
  · rw [← hA 0 f r₀ (hR f), ofAdd_zero, map_one, Prod.mk_one_one, map_one, Module.End.one_apply]

theorem vacX : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        ∀ f₀, M.IsGauss ψ τ f₀ →
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f₀ p.2) ∧ ∃ f' ∈ M.Pol ψ τ, ∀ x, HasDerivAt (fun t => T t f₀ x) (f' x) 0 := by
  intro F E _ _ _ _ _ σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe τ hcX hcW γ hγ T hTa f₀ hf₀
  obtain ⟨h1, h0⟩ := lineGroupX F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe γ hγ T hTa
  have hU := GlobalTheory.T.weil_model_residue_character_pow F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe γ hγ T hTa MeasureTheory.Measure.addHaar inferInstance
  obtain ⟨A, hAc, hAadd, hA0, hAint⟩ := GlobalTheory.T.archimedean_weil_line_intertwines_heisenberg_left F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe γ hγ T hTa
  have hC := GlobalTheory.T.continuous_archimedeanWeilOperator_line_pairX F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe γ hγ T hTa
  obtain ⟨J₀, hJ, hvac⟩ := GlobalTheory.T.exists_complexStructure_gaussVacuum_isFockVacuum F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe τ hcX hcW f₀ hf₀
  haveI : BorelSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  obtain ⟨hsm, k, qs, qs', cs, c, hd⟩ := GlobalTheory.T.weilOneParam_moves_fockVacuum_smoothly (V := Fin n × Fin d → mixedEmbedding.mixedSpace F)
    MeasureTheory.Measure.addHaar (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d))
    (GlobalTheory.GaussLine.pairInf_nondeg F _) T h1 h0 hU A hAc hAadd hA0 hAint hC J₀ hJ f₀ hvac
  refine ⟨hsm, ?_⟩
  have hf₀P : f₀ ∈ M.Pol ψ τ := Submodule.mem_sInf.2 fun N hN => hN.1 f₀ hf₀
  have hmul := GlobalTheory.T.polynomial_fock_space_stable_mul_trace_pairing F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe τ hcX hcW
  choose m hmP hmE using hmul
  refine ⟨(∑ i, cs i • m (qs i) (m (qs' i) f₀ hf₀P) (hmP _ _ _)) + c • f₀,
    add_mem (sum_mem fun i _ => Submodule.smul_mem _ _ (hmP _ _ _)) (Submodule.smul_mem _ _ hf₀P), fun x => ?_⟩
  convert hd x using 1
  simp only [SchwartzMap.add_apply, SchwartzMap.sum_apply, SchwartzMap.smul_apply, smul_eq_mul, hmE]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem heisX : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        ∀ u, At (evI F) u → ∀ f ∈ M.Pol ψ τ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f p.2) →
          (∃ f' ∈ M.Pol ψ τ, ∀ x, HasDerivAt (fun t => T t f x) (f' x) 0) →
          ∀ f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ →
            ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f₁ p.2) ∧ ∃ f₁' ∈ M.Pol ψ τ, ∀ x, HasDerivAt (fun t => T t f₁ x) (f₁' x) 0 := by
  intro F E _ _ _ _ _ σ _hCM n d X W M ψ χX χW om hψ _ _ _ _ _ _ _ _ hW τ _ _ γ hγ T hTa u hu f hf hsm hder f₁ hf₁
  obtain ⟨f', hf'P, hf'd⟩ := hder
  have hstab : ∀ v : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) v → ∀ g ∈ M.Pol ψ τ,
      ∃ g₁ ∈ M.Pol ψ τ, ∀ y, g₁ y = GlobalTheory.HeisOrbit.dOp (GlobalTheory.HeisOrbit.archCo M.co v).1 (GlobalTheory.HeisOrbit.archCo M.co v).2 g y := by
    intro v hv g hg
    obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ (Fin n) (Fin d) (Fin n × Fin d) ψ (incM F X.J) (incM F W.J)
      M.co hψ
    have h0 : ∀ t, M.heisLine ψ v t 0 = 0 := fun t => by
      funext x
      simp [Model.heisLine, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]
    have hA : ActsD (evI F) (M.heisLine ψ v) g (D v g) :=
      (GlobalTheory.RealLift.actsLaws F _ g (D v g) (D v g)).1 _ h0 (hD v hv g).1
    refine ⟨D v g, Submodule.mem_sInf.2 fun N hN => hN.2 v hv g (Submodule.mem_sInf.1 hg N hN) _ hA, fun y => ?_⟩
    rw [(hD v hv g).2 y]
    rfl
  have hrel : ∀ t y, T t f₁ y = GlobalTheory.HeisOrbit.dOp (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)).1
      (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)).2 (T t f) y := fun t =>
    GlobalTheory.T.weil_operator_left_intertwines_heisenberg_derivative M ψ χX χW om hψ hW (γ (Multiplicative.ofAdd t)) (T t) (hTa t) u hu f f₁ hf₁
  obtain ⟨hφ, u', hu', hφd⟩ := GlobalTheory.T.archimedean_darboux_coords_one_param_orbit_smooth (W := W) M γ hγ u hu
  have hfun : (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f₁ p.2) =
      fun p => GlobalTheory.HeisOrbit.dOp (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd p.1)) * u)).1
        (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd p.1)) * u)).2 (T p.1 f) p.2 :=
    funext fun p => hrel p.1 p.2
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact GlobalTheory.HeisOrbit.dOp_contDiff_family (fun t => T t f) (fun t => (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)).1)
      (fun t => (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)).2) hsm hφ.fst hφ.snd
  have hT0 : T 0 f = f := by
    have h1 : om (γ (Multiplicative.ofAdd 0), 1) = 1 := by
      rw [ofAdd_zero, map_one]
      exact map_one om
    have hA : Acts (evI F) (om (γ (Multiplicative.ofAdd 0), 1)) f f := by
      rw [h1]
      intro r _
      rfl
    exact (GlobalTheory.RealLift.actsLaws F _ f (T 0 f) f).2.2.2.1 _ (hTa 0 f) hA
  have hφ0 : GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd (0 : ℝ))) * u) = GlobalTheory.HeisOrbit.archCo M.co u := by
    rw [ofAdd_zero, map_one]
    simp [mat]
  obtain ⟨g₁, hg₁P, hg₁⟩ := hstab u hu f' hf'P
  obtain ⟨g₂, hg₂P, hg₂⟩ := hstab u' hu' f hf
  refine ⟨g₁ + g₂, add_mem hg₁P hg₂P, fun x => ?_⟩
  have hP := (hasFDerivAt_fst (𝕜 := ℝ)).comp_hasDerivAt (0 : ℝ) hφd
  have hQ := (hasFDerivAt_snd (𝕜 := ℝ)).comp_hasDerivAt (0 : ℝ) hφd
  have h4 := GlobalTheory.HeisOrbit.DOpDeriv.dOp_hasDerivAt (fun t => T t f) (fun t => (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)).1)
    (fun t => (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)).2) f' _ _ hsm hf'd hP hQ x
  simp only [hφ0, hT0] at h4
  rw [SchwartzMap.add_apply, hg₁, hg₂]
  exact h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hrel t x)

theorem lie_deriv_polX : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → GlobalTheory.LFun.IsHecke F E χX → GlobalTheory.LFun.IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w, (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, ∀ f ∈ M.Pol ψ τ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ → f₁ ∈ M.Pol ψ τ := by
  intro F E _ _ _ _ _ σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hwe τ hcX hcW γ hγ
  have h1W : (1 : UA σ W.J) ∈ UAt σ W (evI F) := by
    intro u _
    have e : mat (1 : UA σ W.J) = 1 := rfl
    show u • (mat (1 : UA σ W.J) - 1) = 0
    rw [e, sub_self, smul_zero]
  choose T hT' using fun t : ℝ => GlobalTheory.FockCompactW.exists_op_of_UAt hψ hwe (γ (Multiplicative.ofAdd t), 1) (hγ.2 _) h1W
  have hvac : ∀ f₀, M.IsGauss ψ τ f₀ → f₀ ∈ M.Pol ψ τ := fun f₀ h =>
    Submodule.mem_sInf.2 fun N hN => hN.1 f₀ h
  have hstab : ∀ u, At (evI F) u → ∀ f ∈ M.Pol ψ τ, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine ψ u) f f₁ → f₁ ∈ M.Pol ψ τ := fun u hu f hf f₁ h =>
    Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ h
  let N : Submodule ℂ (SInf F (Fin n × Fin d)) :=
    { carrier := {f | f ∈ M.Pol ψ τ ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f p.2) ∧
        ∃ f' ∈ M.Pol ψ τ, ∀ x, HasDerivAt (fun t => T t f x) (f' x) 0}
      zero_mem' := ⟨zero_mem _, by simpa using contDiff_const, 0, zero_mem _, fun x => by simpa using hasDerivAt_const _ _⟩
      add_mem' := by
        rintro f g ⟨hf, hf1, f', hf', hf2⟩ ⟨hg, hg1, g', hg', hg2⟩
        refine ⟨add_mem hf hg, by simpa using hf1.add hg1, f' + g', add_mem hf' hg', fun x => ?_⟩
        show HasDerivAt (fun t => T t (f + g) x) ((f' + g') x) 0
        simp only [map_add (f := _), SchwartzMap.add_apply]
        exact (hf2 x).add (hg2 x)
      smul_mem' := by
        rintro c f ⟨hf, hf1, f', hf', hf2⟩
        refine ⟨Submodule.smul_mem _ c hf, by simpa using hf1.const_smul c, c • f', Submodule.smul_mem _ c hf', fun x => ?_⟩
        simpa using (hf2 x).const_mul c }
  have hPN : M.Pol ψ τ ≤ N := by
    refine sInf_le ⟨fun f₀ h => ?_, fun u hu f hf f₁ h => ?_⟩
    · exact ⟨hvac f₀ h, vacX F E σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hwe τ hcX hcW γ hγ T hT' f₀ h⟩
    · obtain ⟨hf0, hf1, hf2⟩ := hf
      exact ⟨hstab u hu f hf0 f₁ h,
        heisX F E σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hwe τ hcX hcW γ hγ T hT' u hu f hf0 hf1 hf2 f₁ h⟩
  intro f hf f₁ h₁
  obtain ⟨-, -, f', hf', hd⟩ := hPN hf
  have hA : ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f' := by
    intro r hr x
    have h1 : ∀ t : ℝ, om (γ (Multiplicative.ofAdd t), 1) (tens (evI F) f r) = tens (evI F) (T t f) r :=
      fun t => hT' t f r hr
    simp only [h1]
    exact (hd _).mul_const (r x)
  have e : f₁ = f' := (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f f₁ f').2.2.1 _ h₁ hA
  rw [e]; exact hf'

end GlobalTheory.RealLieFockX

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchPure

theorem acts_arch_of_weil {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (hW : M.IsWeil ψ χX χW om)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J) (hh : h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F))
    (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) :
    ∃ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (1, h)) f f₁ := by
  have hS := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hW
  set T := om (1, h) with hTdef
  have hpres : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), T Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) :=
    fun Φ hΦ => hS.pres (1, h) Φ hΦ
  have hcomm := GlobalTheory.ArchLocality.comm_fin M ψ χX χW om hW h hh
  obtain ⟨r₀, hr₀1, hr₀⟩ := GlobalTheory.ArchLocality.ref_fun (F := F) (Fin n × Fin d)
  set Φ₀ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F)
    (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) r₀ with hΦ₀
  have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hr₀ f).2
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.ArchLocality.res_arch (T Φ₀) (hpres Φ₀ hm₀)
  refine ⟨f₁, fun r hr => ?_⟩
  funext y
  set u : AF F := (0, 1) with hu
  have hu0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F u = 0 := GlobalTheory.ArchLocality.evI_fin
  have htr : ∀ Ψ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d),
      T (fun w => Ψ (w + u • (-y))) = fun w => T Ψ (w + u • (-y)) := by
    intro Ψ hΨ
    have e := hcomm u hu0 (-y) 0 Ψ hΨ
    have hs0 : ∀ G : (Fin n × Fin d → AF F) → ℂ,
        GlobalTheory.WeilM.schr ψ (u • (-y), u • (0 : Fin n × Fin d → AF F)) G = fun w => G (w + u • (-y)) := by
      intro G; funext w; simp [GlobalTheory.WeilM.schr]
    rw [hs0, hs0] at e
    exact e
  set Φ₁ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F)
    (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) r with hΦ₁
  set Φ₂ : (Fin n × Fin d → AF F) → ℂ := r y • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
  have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ :=
    Submodule.smul_mem _ _ (GlobalTheory.SchwartzTranslation.schA_add_const _ _ hm₀)
  have hz2 : ∀ z : Fin n × Fin d → AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z → ∀ i, (z i).2 = 0 := by
    intro z hz i
    have := congrArg Prod.snd (congrFun (hz u hu0) i)
    change (u * z i).2 = (0 : AF F).2 at this
    have e : (u * z i).2 = (z i).2 := one_mul _
    rw [e] at this
    exact this
  have hvan : ∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z → (Φ₁ - Φ₂) (y + z) = 0 := by
    intro z hz
    have e1 : r (y + z) = r y := hr.1 y z hz
    have e2 : (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((y + z + u • (-y)) i)) =
        fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((y + z) i) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.ArchLocality.evI_add, GlobalTheory.ArchLocality.evI_mul,
        hu0, zero_mul, add_zero]
    have e3 : r₀ (y + z + u • (-y)) = 1 := by
      refine hr₀1 _ fun i => ?_
      change ((y i + z i) + u * -(y i)).2 = 0
      change (y i).2 + (z i).2 + 1 * -(y i).2 = 0
      rw [hz2 z hz i]
      ring
    simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
    rw [e2, e3, e1]
    ring
  have h0 := GlobalTheory.ArchLocality.fibre ψ hψ T hcomm (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hvan
  rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
  have hy0 : y + u • (-y) = fun i =>
      (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (y i)), 0) : AF F) := by
    funext i
    refine Prod.ext ?_ ?_
    · change (y i).1 + 0 * -(y i).1 = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        (InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1)
      rw [RingEquiv.symm_apply_apply]
      ring
    · change (y i).2 + 1 * -(y i).2 = 0
      ring
  have h2 : T Φ₂ y = r y * f₁ (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (y i)) := by
    rw [hΦ₂, map_smul, htr Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hy0, hf₁]
  rw [h0, h2]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
  ring

theorem pure_arch : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Wd (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F), ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
    ∃ c : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      om (1, g) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure c φ := by
  intro F E _ _ _ _ _ σ n d Y Wd M ψ χX χW om hψ hM hW g hg f φ hSB hvac
  obtain ⟨c, hc⟩ := acts_arch_of_weil M ψ χX χW om hψ hW g hg f
  refine ⟨c, ?_⟩
  have hstd : ∀ᶠ v in Filter.cofinite,
      φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    (hvac.and hM.std).mono fun v h => h.1.trans h.2
  set r : (Fin n × Fin d → AF F) → ℂ :=
    fun x => ∏ᶠ v, φ v fun i => evFin F v (x i) with hr
  have hRest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F)
      (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) r := by
    refine ⟨fun x z hz => ?_, GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
    have hz0 : ∀ v i, evFin F v (z i) = 0 := by
      intro v i
      set u : AF F := (0, 1) with hu
      have h1 := congrFun (hz u GlobalTheory.ArchLocality.evI_fin) i
      have h2 : evFin F v u = 1 := map_one (evFin F v)
      have h3 := congrArg (evFin F v) h1
      simp only [Pi.zero_apply, map_zero] at h3
      change evFin F v (u * z i) = 0 at h3
      rw [map_mul, h2, one_mul] at h3
      exact h3
    simp only [hr, Pi.add_apply, map_add (f := _), hz0, add_zero]
  exact hc r hRest

end GlobalTheory.ArchPure
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical


open GlobalTheory.ArchFactor in
theorem GlobalTheory.ArchFactorPair.exists_archOperator_pair :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ h ∈ UAt σ W (evI F), ∃ T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, h)) f (T f) := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om hstd _ _ _ _ _ _ _ _ hweil h hh
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hweil
  have hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), om (1, h) Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun Φ hΦ => hW.pres (1, h) Φ hΦ
  have h1 : (1 : UA σ X.J) ∈ UAt σ X (evI F) := by
    intro u _
    simp [mat]
  have hcomm := comm_offI hweil (1, h) h1 hh
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_finiteWeight_complementary_archimedeanSchwartz (F := F) (Fin n × Fin d)
  have hB : ∀ f : SInf F (Fin n × Fin d), ∃ g : SInf F (Fin n × Fin d),
      ∀ t, g t = (R 0)⁻¹ * om (1, h) (tens (evI F) (⇑f) R) (liftI t) := by
    intro f
    obtain ⟨g, hg⟩ := GlobalTheory.T.exists_schwartz_archimedeanSlice_adelicSchwartz _ (Submodule.smul_mem _ (R 0)⁻¹ (hkeep _ (hR f).2))
    exact ⟨g, fun t => by rw [hg]; rfl⟩
  choose Tf hTf using hB
  have htens_add : ∀ f g : SInf F (Fin n × Fin d),
      tens (evI F) (⇑(f + g)) R = tens (evI F) (⇑f) R + tens (evI F) (⇑g) R := by
    intro f g; funext x; simp only [tens, SchwartzMap.add_apply, Pi.add_apply]; ring
  have htens_smul : ∀ (c : ℂ) (f : SInf F (Fin n × Fin d)),
      tens (evI F) (⇑(c • f)) R = c • tens (evI F) (⇑f) R := by
    intro c f; funext x; simp only [tens, SchwartzMap.smul_apply, Pi.smul_apply, smul_eq_mul]; ring
  let T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d) :=
    { toFun := Tf
      map_add' := fun f g => by
        ext t
        rw [SchwartzMap.add_apply, hTf, hTf, hTf, htens_add, map_add (f := _), Pi.add_apply]; ring
      map_smul' := fun c f => by
        ext t
        rw [SchwartzMap.smul_apply, hTf, hTf, htens_smul, map_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
          RingHom.id_apply]; ring }
  refine ⟨T, fun f r hr => ?_⟩
  funext y
  set T0 := om (1, h) with hT0
  set u : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) with hudef
  have hu : evI F u = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
    exact map_zero _
  set p : Fin n × Fin d → AF F := liftI (fun i => evI F (y i)) with hpdef
  have hyp : y + u • (-y) = p := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef, liftI, evI,
      RingEquiv.symm_apply_apply]
    refine Prod.ext ?_ ?_
    · show (y i).1 + 0 * (-(y i)).1 = (y i).1
      simp
    · show (y i).2 + 1 * (-(y i)).2 = 0
      rw [one_mul]
      exact add_neg_cancel ((y i).2)
  have hpat : At (evI F) p := by
    intro u' hu'
    have h0 : u'.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu')
    funext i
    refine Prod.ext ?_ ?_
    · show u'.1 * (p i).1 = 0
      rw [h0, zero_mul]
    · show u'.2 * (p i).2 = 0
      simp [hpdef, liftI]
  set Φ₀ := tens (evI F) (⇑f) R with hΦ₀
  set Φ₁ := tens (evI F) (⇑f) r with hΦ₁
  set Φ₂ : (Fin n × Fin d → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
  have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hR f).2
  have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ := Submodule.smul_mem _ _ (GlobalTheory.SchwartzTranslation.schA_add_const _ _ hm₀)
  have hfz : ∀ z, At (evI F) z → (Φ₁ - Φ₂) (y + z) = 0 := by
    intro z hz
    have e1 : r (y + z) = r y := hr.1 y z hz
    have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
    have hpz : At (evI F) (p + z) := fun u' hu' => by
      rw [smul_add, hpat u' hu', hz u' hu', add_zero]
    have e3 : R (p + z) = R 0 := by simpa using (hR f).1 0 (p + z) hpz
    have e4 : (fun i => evI F ((y + z + u • (-y)) i)) = fun i => evI F ((y + z) i) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, evI_add', evI_mul', hu, zero_mul, add_zero]
    simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, tens]
    rw [e4, e2, e3, e1]
    field_simp
    ring
  have h0 := GlobalTheory.T.heisenbergCommuting_operator_independent_of_archimedeanFibres ψ T0 hstd hkeep (fun u hu p q Φ hΦ => hcomm u hu p q Φ hΦ) (Φ₁ - Φ₂)
    (sub_mem hr.2 hm₂) y hfz
  rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
  have htr : T0 (fun w => Φ₀ (w + u • (-y))) = fun w => T0 Φ₀ (w + u • (-y)) := by
    have h := hcomm u hu (-y) 0 Φ₀ hm₀
    rw [smul_zero, schr_trans', schr_trans'] at h
    exact h
  have h2 : T0 Φ₂ y = (r y / R 0) * T0 Φ₀ p := by
    rw [hΦ₂, map_smul, htr, Pi.smul_apply, smul_eq_mul, hyp]
  show T0 Φ₁ y = tens (evI F) (⇑(Tf f)) r y
  rw [h0, h2]
  show r y / R 0 * T0 Φ₀ p = (Tf f) (fun i => evI F (y i)) * r y
  rw [hTf]
  show r y / R 0 * T0 Φ₀ p = (R 0)⁻¹ * T0 Φ₀ p * r y
  rw [div_eq_mul_inv]
  ring
end
