module

import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLines
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.PlaneRemovalConfiguration
public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

@[expose] public section

section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace LatticeQuotientMeasure

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}


variable (F) in
def e0 : AF F := ((0 : Ainf F), (1 : Af F))

theorem at_iff {M : Type} [AddCommGroup M] [Module (AF F) M] (z : M) : At (evI F) z ↔ e0 F • z = 0 := by
  constructor
  · intro h
    apply h
    show (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : Ainf F) = 0
    exact map_zero _
  · intro h u hu
    have hu1 : u.1 = 0 := by
      have hu' : (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F) u.1 = 0 := hu
      exact (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu'.trans (map_zero _).symm)
    have hue : u = u * e0 F := by
      refine Prod.ext ?_ ?_
      · show u.1 = u.1 * (0 : Ainf F)
        rw [hu1, zero_mul]
      · show u.2 = u.2 * (1 : Af F)
        rw [mul_one]
    rw [hue, mul_smul, h, smul_zero]

variable (F) in
theorem t2Space_adeleRing_of_numberField : T2Space (AF F) := by
  haveI : T2Space (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) :=
    T2Space.of_injective_continuous DFunLike.coe_injective RestrictedProduct.continuous_coe
  haveI : T2Space (NumberField.InfiniteAdeleRing F) :=
    show T2Space ((v : InfinitePlace F) → v.Completion) from inferInstance
  show T2Space (NumberField.InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
  infer_instance

variable (F E) in
theorem t2Space_cm_host_adeles : T2Space (AE F E) := by
  haveI := t2Space_adeleRing_of_numberField F
  let b := Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)
  exact T2Space.of_injective_continuous (X := AE F E) b.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap (A := AE F E) b.equivFun.toLinearMap)

variable (F E) in
theorem ring_AE : IsTopologicalRing (AE F E) := by
  exact IsModuleTopology.isTopologicalRing (AF F) (AE F E)

omit [NumberField E] in
theorem continuous_piInf {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (piInf τ) := by
  apply PositivityTheory.RL.continuous_piInf <;> assumption

variable {n d : ℕ}

theorem continuous_sz (τ : ∀ w : InfinitePlace F, EmbOver E w) : Continuous (sz τ : Ten F E n d → ℝ) := by
  exact continuous_finsetSum _ fun w _ => continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    ((continuous_piInf (τ w)).comp (continuous_id.matrix_elem i j)).norm

theorem isClosed_supp {C : Set (Ten F E n d)} (hC : IsCompact C) :
    IsClosed {z : Ten F E n d | ∃ c ∈ C, At (evI F) (z - c)} := by
  haveI := t2Space_cm_host_adeles F E
  have hset : {z : Ten F E n d | ∃ c ∈ C, At (evI F) (z - c)} =
      (fun z : Ten F E n d => e0 F • z) ⁻¹' ((fun c : Ten F E n d => e0 F • c) '' C) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image, at_iff, smul_sub, sub_eq_zero]
    constructor
    · rintro ⟨c, hc, hzc⟩
      exact ⟨c, hc, hzc.symm⟩
    · rintro ⟨c, hc, hzc⟩
      exact ⟨c, hc, hzc.symm⟩
  rw [hset]
  exact (hC.image (continuous_const_smul (e0 F))).isClosed.preimage (continuous_const_smul (e0 F))

theorem measurable_maj {G : Type} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    (τ : ∀ w : InfinitePlace F, EmbOver E w) {C : Set (Ten F E n d)} (hC : IsCompact C) (N : ℕ)
    {f : G → Ten F E n d} (hf : Continuous f) : Measurable fun g => maj τ C N (f g) := by
  have hcl := isClosed_supp (F := F) (E := E) (n := n) (d := d) hC
  delta maj
  refine Measurable.ite (hcl.preimage hf).measurableSet ?_ measurable_const
  exact ((continuous_const.add ((continuous_sz τ).comp hf)).measurable.pow_const N).inv

omit [NumberField E] in
theorem continuous_mat_inv {J : Matrix (Fin n) (Fin n) E} : Continuous fun g : UA σ J => mat g⁻¹ := by
  exact Units.continuous_coe_inv.comp continuous_subtype_val

end LatticeQuotientMeasure


open LatticeQuotientMeasure in
theorem latMeas : LatMeas := by
  intro F E _ _ _ _ _ σ _ τ n d J J' _ _ C N S hC h
  haveI := ring_AE F E
  haveI := t2Space_cm_host_adeles F E
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (Matrix (Fin n) (Fin d) E) := show Countable (Fin n → Fin d → E) from inferInstance
  haveI : BorelSpace (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ J) := ⟨rfl⟩
  delta latSum
  refine Measurable.tsum fun x => ENNReal.measurable_ofReal.comp ?_
  exact measurable_maj τ hC N ((continuous_mat_inv.matrix_mul continuous_const).matrix_mul continuous_const)

end PositivityTheory.ThKEst

end
end

section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section

variable {d : ℕ} {W : Spc F E d}

def IsLie (τ : ∀ w : InfinitePlace F, EmbOver E w) (W : Spc F E d) (Y : InfinitePlace F → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ w, (Y w)ᵀ * W.J.map (τ w).1 + W.J.map (τ w).1 * (Y w).map star = 0

def Gen (τ : ∀ w : InfinitePlace F, EmbOver E w) (W : Spc F E d) (γ : Multiplicative ℝ →* UA σ W.J)
    (Y : InfinitePlace F → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ w (t : ℝ), (mat (γ (Multiplicative.ofAdd t))).map (piInf (τ w)) = NormedSpace.exp ((t : ℂ) • Y w)


variable (W) in
def UMG (f : UA σ W.J → ℂ) : Prop :=
  ∃ (k : ℕ) (S : Set (UA σ W.J → ℂ)), f ∈ S ∧ ∀ f₁ ∈ S, Continuous f₁ ∧ (∃ C : ℝ, ∀ h, ‖f₁ h‖ ≤ C * (ht h : ℝ) ^ k) ∧
    ∀ γ ∈ Lines σ W, ∃ f₂ ∈ S, ∀ h, HasDerivAt (fun t : ℝ => f₁ (h * γ (Multiplicative.ofAdd t))) (f₂ h) 0


variable (W) in
def SmoothFin (τ : ∀ w : InfinitePlace F, EmbOver E w) (f : UA σ W.J → ℂ) : Prop :=
  ∃ U ∈ 𝓝 (1 : UA σ W.J), ∀ u ∈ U, (∀ w, (mat u).map (piInf (τ w)) = 1) → ∀ h, f (h * u) = f h

def LeftInv {J : Matrix (Fin d) (Fin d) E} (f : UA σ J → ℂ) : Prop := ∀ γ ∈ ratU σ J, ∀ h, f (γ * h) = f h

def Rapid {J : Matrix (Fin d) (Fin d) E} (f : UA σ J → ℂ) : Prop := ∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C

end

def LineGen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (d : ℕ) (W : Spc F E d), EpsHerm σ W.J → ∀ γ ∈ Lines σ W, ∃ Y : InfinitePlace F → Matrix (Fin d) (Fin d) ℂ, IsLie τ W Y ∧ Gen τ W γ Y

def LineEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (d : ℕ) (W : Spc F E d), EpsHerm σ W.J → ∀ Y : InfinitePlace F → Matrix (Fin d) (Fin d) ℂ, IsLie τ W Y → ∃ γ ∈ Lines σ W, Gen τ W γ Y ∧ ∀ γ' ∈ Lines σ W, Gen τ W γ' Y → γ' = γ

def LinDer : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (d : ℕ) (W : Spc F E d), EpsHerm σ W.J → ∃ (m : ℕ) (β : Fin m → (Multiplicative ℝ →* UA σ W.J)) (c : Fin m → (InfinitePlace F → Matrix (Fin d) (Fin d) ℂ) →ₗ[ℝ] ℝ), (∀ i, β i ∈ Lines σ W) ∧ ∀ (f : UA σ W.J → ℂ) (f' : Fin m → UA σ W.J → ℂ), (∀ i, Continuous (f' i) ∧ ∀ h, HasDerivAt (fun t : ℝ => f (h * β i (Multiplicative.ofAdd t))) (f' i h) 0) → ∀ γ ∈ Lines σ W, ∀ Y, Gen τ W γ Y → ∀ h, HasDerivAt (fun t : ℝ => f (h * γ (Multiplicative.ofAdd t))) (∑ i, (c i Y : ℂ) * f' i h) 0

def UMGSmooth : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (d : ℕ) (W : Spc F E d), EpsHerm σ W.J → ∀ f : UA σ W.J → ℂ, UMG W f → ∀ (k : ℕ) (γ : Fin k → (Multiplicative ℝ →* UA σ W.J)), (∀ i, γ i ∈ Lines σ W) → ∀ g, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (Multiplicative.ofAdd (t i))).prod)

def UMGLin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (d : ℕ) (W : Spc F E d), EpsHerm σ W.J → ∀ f f' : UA σ W.J → ℂ, UMG W f → UMG W f' → ∀ a b : ℂ, UMG W (a • f + b • f')

def CuspRapid : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (d : ℕ) (W : Spc F E d), EpsHerm σ W.J → ∀ f : UA σ W.J → ℂ, LeftInv f → UMG W f → SmoothFin W τ f → PositivityTheory.ThKEnd.IsCusp W f → Rapid f

def Level : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∀ φ ∈ SB (Fin n × Fin d → Af F), ∃ U ∈ 𝓝 (1 : UA σ W.J), ∀ u ∈ U, (∀ w, (mat u).map (piInf (B.emb w)) = 1) → ∀ f : SInf F (Fin n × Fin d), om (1, u) (pureA F f φ) = pureA F f φ

def IDer : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∀ 𝓕, Dom M om 𝓕 → ∀ φ ∈ 𝓕, φ ∈ SB _ → ∀ f ∈ M.Pol B.ψ B.emb, (∀ γ ∈ Lines σ W, ∃ f₁ ∈ M.Pol B.ψ B.emb, ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ ∧ ∀ h, HasDerivAt (fun t : ℝ => M.I om (pureA F f φ) (h * γ (Multiplicative.ofAdd t))) (M.I om (pureA F f₁ φ) h) 0) ∧ ∀ γ ∈ Lines σ X, ∃ f₁ ∈ M.Pol B.ψ B.emb, ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ ∧ M.I om (pureA F f₁ φ) = 0

def IInv : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), LeftInv (M.I om Φ) ∧ (∀ g, M.I om (om (g, 1) Φ) = M.I om Φ) ∧ ∀ h h', M.I om (om (1, h') Φ) h = M.I om Φ (h * h')

def IUMG : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∀ 𝓕, Dom M om 𝓕 → ∀ φ ∈ 𝓕, φ ∈ SB _ → ∀ f ∈ M.Pol B.ψ B.emb, UMG W (M.I om (pureA F f φ)) ∧ SmoothFin W B.emb (M.I om (pureA F f φ))

end PositivityTheory.ThKEst

end
end

section

noncomputable section

namespace PositivityTheory.ThKEst.FiniteAdelicSupportCompactness

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def stdF (κ : Type) (u : HeightOneSpectrum (𝓞 F)) : (κ → Fv F u) → ℂ :=
  Set.indicator {x | ∀ i, x i ∈ u.adicCompletionIntegers F} 1

def Good (φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ) : Prop :=
  (∀ u, φ u ∈ SB (κ → Fv F u)) ∧ ∀ᶠ u in cofinite, φ u = stdF κ u

def pf (φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ) (y : κ → Af F) : ℂ :=
  ∏ᶠ u, φ u fun i => evalV F u (y i)

theorem pure_eq (f : SInf F κ) (φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ) :
    pure f φ = pureA F f (pf φ) := rfl

theorem ev_int (y : κ → Af F) : ∀ᶠ u in cofinite, ∀ i, evalV F u (y i) ∈ u.adicCompletionIntegers F :=
  eventually_all.2 fun i => (y i).2

theorem cont_evalV (u : HeightOneSpectrum (𝓞 F)) : Continuous (evalV F u) :=
  (continuous_apply u).comp RestrictedProduct.continuous_coe

theorem isOpen_intAf : IsOpen {a : Af F | ∀ v, evalV F v a ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem
    (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _)

theorem isCompact_intV (u : HeightOneSpectrum (𝓞 F)) :
    IsCompact {x : κ → Fv F u | ∀ i, x i ∈ u.adicCompletionIntegers F} := by
  have h : IsCompact (u.adicCompletionIntegers F : Set (Fv F u)) := isCompact_iff_compactSpace.2
    (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F u)
  simpa [Set.pi] using isCompact_univ_pi fun _ : κ => h

theorem isCompact_box (C : ∀ u : HeightOneSpectrum (𝓞 F), Set (Fv F u)) (hC : ∀ u, IsCompact (C u))
    (h : ∀ᶠ u in cofinite, C u ⊆ u.adicCompletionIntegers F) : IsCompact {a : Af F | ∀ u, evalV F u a ∈ C u} := by
  let S : Set (HeightOneSpectrum (𝓞 F)) := {u | C u ⊆ u.adicCompletionIntegers F}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.2 h
  let P := RestrictedProduct (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F)
      (fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F))) (𝓟 S)
  have h1 : IsCompact {x : P | ∀ u, x u ∈ C u} := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.isCompact_iff]
    convert isCompact_univ_pi hC
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ u -
      exact hy u
    · intro hx
      exact ⟨⟨x, fun u hu => hu (hx u trivial)⟩, fun u => hx u trivial, rfl⟩
  have h2 := h1.image (RestrictedProduct.continuous_inclusion hS)
  have e : {a : Af F | ∀ u, evalV F u a ∈ C u} = RestrictedProduct.inclusion _ _ hS '' {x : P | ∀ u, x u ∈ C u} := by
    ext a
    constructor
    · intro ha
      exact ⟨⟨a.1, fun u hu => hu (ha u)⟩, ha, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  rw [e]
  exact h2

theorem pf_eq_prod {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ} (S : Finset (HeightOneSpectrum (𝓞 F)))
    (y : κ → Af F) (h : ∀ u ∉ S, φ u = stdF κ u ∧ ∀ i, evalV F u (y i) ∈ u.adicCompletionIntegers F) :
    pf φ y = ∏ u ∈ S, φ u fun i => evalV F u (y i) := by
  refine finprod_eq_prod_of_mulSupport_subset _ fun u hu => ?_
  by_contra hn
  apply hu
  simp only
  rw [(h u hn).1, stdF, Set.indicator_of_mem (by exact (h u hn).2)]
  rfl

theorem exists_fin {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ} (hφ : ∀ᶠ u in cofinite, φ u = stdF κ u)
    (y : κ → Af F) : ∃ S : Finset (HeightOneSpectrum (𝓞 F)),
      ∀ u ∉ S, φ u = stdF κ u ∧ ∀ i, evalV F u (y i) ∈ u.adicCompletionIntegers F :=
  ⟨(hφ.and (ev_int y)).toFinset, fun u hu => by
    by_contra hn
    exact hu (Set.Finite.mem_toFinset _ |>.2 hn)⟩

theorem pf_mem {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ} (hφ : Good φ) : pf φ ∈ SB (κ → Af F) := by
  have hc : ∀ u, Continuous fun (y : κ → Af F) i => evalV F u (y i) := fun u =>
    continuous_pi fun i => (cont_evalV u).comp (continuous_apply i)
  constructor
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨S, hS⟩ := exists_fin hφ.2 x
    have h1 : ∀ᶠ y in 𝓝 x, ∀ i v, evalV F v (y i - x i) ∈ v.adicCompletionIntegers F :=
      eventually_all.2 fun i => (isOpen_intAf.preimage (f := fun y : κ → Af F => y i - x i) (by fun_prop)).mem_nhds
        (by intro v; simp)
    have h2 : ∀ᶠ y in 𝓝 x, ∀ u ∈ S, φ u (fun i => evalV F u (y i)) = φ u fun i => evalV F u (x i) :=
      (eventually_all_finset S).2 fun u _ => ((hφ.1 u).1.comp_continuous (hc u)).eventually_eq x
    filter_upwards [h1, h2] with y h1 h2
    rw [pf_eq_prod S x hS, pf_eq_prod S y fun u hu => ⟨(hS u hu).1, fun i => ?_⟩]
    · exact Finset.prod_congr rfl h2
    · have := add_mem (h1 i u) ((hS u hu).2 i)
      rwa [map_sub, sub_add_cancel] at this
  · have hK : ∀ i : κ, IsCompact {a : Af F | ∀ u, evalV F u a ∈ (fun x => x i) '' tsupport (φ u)} := fun i =>
      isCompact_box _ (fun u => (hφ.1 u).2.isCompact.image (continuous_apply i)) (by
        filter_upwards [hφ.2] with u hu
        rintro _ ⟨x, hx, rfl⟩
        rw [hu] at hx
        exact closure_minimal Set.support_indicator_subset (isCompact_intV u).isClosed hx i)
    refine HasCompactSupport.intro (isCompact_univ_pi hK) fun y hy => ?_
    by_contra h0
    refine hy fun i _ u => ⟨fun i => evalV F u (y i), subset_tsupport _ (fun h => h0 ?_), rfl⟩
    obtain ⟨S, hS⟩ := exists_fin hφ.2 y
    classical
    rw [pf_eq_prod (insert u S) y fun v hv => hS v fun h => hv (Finset.mem_insert_of_mem h)]
    exact Finset.prod_eq_zero (Finset.mem_insert_self _ _) h

theorem smul_pureA (c : ℂ) (f : SInf F κ) (g : (κ → Af F) → ℂ) : c • pureA F f g = pureA F (c • f : SInf F κ) g := by
  funext x
  simp [pureA, mul_assoc]

theorem sum_of_span {S : Set ((κ → AF F) → ℂ)} {T : Set ((κ → Af F) → ℂ)}
    (h : ∀ Φ ∈ S, ∃ (f : SInf F κ) (g : (κ → Af F) → ℂ), g ∈ T ∧ Φ = pureA F f g) {Φ : (κ → AF F) → ℂ}
    (hΦ : Φ ∈ Submodule.span ℂ S) :
    ∃ (m : ℕ) (f : Fin m → SInf F κ) (φ : Fin m → (κ → Af F) → ℂ), (∀ i, φ i ∈ T) ∧ Φ = ∑ i, pureA F (f i) (φ i) := by
  obtain ⟨m, c, g, rfl⟩ := Submodule.mem_span_set'.1 hΦ
  choose f φ h1 h2 using fun i => h (g i) (g i).2
  refine ⟨m, fun i => c i • f i, φ, h1, Finset.sum_congr rfl fun i _ => ?_⟩
  rw [h2, smul_pureA]

theorem exists_one : ∃ f : SInf F κ, f 0 = 1 := by
  classical
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have hs : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((b x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp b.contDiff
  have h2 : b 0 = 1 := b.one_of_mem_closedBall (by simp [b])
  exact ⟨hs.toSchwartzMap hc, by simp [h2]⟩

def finPt (y : κ → Af F) : κ → AF F := fun i => ((0, y i) : AF F)

theorem pureA_zero (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ) (y : κ → Af F) :
    pureA F f g (finPt y) = f 0 * g y := by
  have e : (fun _ : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F 0) = 0 := funext fun _ => map_zero _
  exact congrArg (fun z => f z * g y) e

end PositivityTheory.ThKEst.FiniteAdelicSupportCompactness

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK FiniteAdelicSupportCompactness

theorem soFin_of : SoFin := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have good : ∀ φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) →
      pf φ ∈ SB (Fin n × Fin d → Af F) := fun φ h1 h2 =>
    pf_mem ⟨h1, by
      filter_upwards [h2, hP.good.std] with v a b
      exact a.trans b⟩
  refine ⟨fun Φ hΦ => ?_, fun Φ hΦ => ?_, fun Φ hΦ => ?_, fun φ hφ => ?_⟩
  · refine sum_of_span (T := soFin B M) ?_ hΦ
    rintro _ ⟨f, φ, h1, h2, h3, rfl⟩
    exact ⟨f, pf φ, ⟨good φ h1 h2, fun f' => Submodule.subset_span ⟨f', φ, h1, h2, h3, rfl⟩⟩, rfl⟩
  · refine sum_of_span (T := (SB (Fin n × Fin d → Af F) : Set _)) ?_ hΦ
    rintro _ ⟨f, g, h1, rfl⟩
    exact ⟨f, g, h1, rfl⟩
  · refine (Submodule.span_le.2 ?_ : M.So B.ψ B.τ₁ ≤ schA F _) hΦ
    rintro _ ⟨f, φ, h1, h2, -, rfl⟩
    exact Submodule.subset_span ⟨f, pf φ, good φ h1 h2, rfl⟩
  · obtain ⟨f₀, h0⟩ := exists_one (F := F) (κ := Fin n × Fin d)
    obtain ⟨m, c, g, hg⟩ := Submodule.mem_span_set'.1 (hφ.2 f₀)
    choose f χ h1 h2 h3 h4 using fun i => (g i).2
    have e : ∀ y, φ y = ∑ i, c i * f i 0 * pf (χ i) y := fun y => by
      have := congrFun hg (finPt y)
      rw [pureA_zero, h0, one_mul, Finset.sum_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [h4, pure_eq, Pi.smul_apply, pureA_zero, smul_eq_mul, mul_assoc]
    refine ⟨m, fun i => c i * f i 0, χ, fun i => ⟨h1 i, h2 i, h3 i⟩, fun f' => ?_⟩
    funext x
    rw [Finset.sum_apply]
    simp only [pure_eq, pureA, Pi.smul_apply, smul_eq_mul, e, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

end PositivityTheory.ThKEst

end
end

section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def DomU {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W)
    (𝓕 : Set ((Fin n × Fin d → Af F) → ℂ)) : Prop :=
  ∃ k : ℕ, ∀ φ ∈ 𝓕, ∃ (p : Seminorm ℂ (SInf F (Fin n × Fin d))) (G : UA σ X.J → ℝ≥0∞), Continuous p ∧ Measurable G ∧
    ∫⁻ g in M.dom, G g ∂M.μ < ⊤ ∧ ∀ (f : SInf F (Fin n × Fin d)) g h,
      ‖theta om (pureA F f φ) g h‖ₑ ≤ ENNReal.ofReal (p f * (ht h : ℝ) ^ k) * G g

def DomWeilU : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → (d + 2 * min r s < 2 * n ∨ min r s = 0) → DomU M om {φ | φ ∈ SB _}

def SoSemiU : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∀ N : ℕ, ∃ k : ℕ, ∀ φ ∈ soFin B M, ∃ p : Seminorm ℂ (SInf F (Fin n × Fin d)), Continuous p ∧
    ∀ (f : SInf F (Fin n × Fin d)) g h, ‖theta om (pureA F f φ) g h‖ * (qht g : ℝ) ^ N ≤ p f * (ht h : ℝ) ^ k

def DomSoU : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → DomU M om (soFin B M)

theorem domWeil_of_U (h : DomWeilU) : DomWeil := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP hd φ hφ
  obtain ⟨k, hk⟩ := h F E σ B n d X W M χX χW om r s r' s' hP hd
  obtain ⟨p, G, hp, hG, hint, hb⟩ := hk φ hφ
  exact ⟨p, k, G, hp, hG, hint, hb⟩

theorem soSemi_of_U (h : SoSemiU) : SoSemi := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP φ hφ N
  obtain ⟨k, hk⟩ := h F E σ B n d X W M χX χW om r s r' s' hP N
  obtain ⟨p, hp, hb⟩ := hk φ hφ
  exact ⟨p, k, hp, hb⟩

end PositivityTheory.ThKEst

end
end

section

namespace PositivityTheory.ThKEst

theorem coefReal_of : CoefReal := fun _ _ _ _ _ _ N => RealFourierCoefficientBounds.main N

end PositivityTheory.ThKEst
end
