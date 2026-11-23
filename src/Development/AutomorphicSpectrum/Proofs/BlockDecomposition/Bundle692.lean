module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle641
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
public import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.LieInvariants.InvariantOfLieOneLEqZero
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle492
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle540
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle541
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle685
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle560
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle569
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle543
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle503
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle542
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle576
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle473
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle555
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle527
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.AdmDiscFin

section Dual

variable {K : Type} [Group K]

def shiftL (Y : Submodule ℂ (K → ℂ)) (hY : ∀ f ∈ Y, ∀ k, (fun x => f (k * x)) ∈ Y) (k : K) : Y →ₗ[ℂ] Y where
  toFun f := ⟨fun x => f.1 (k * x), hY f.1 f.2 k⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def dualRep (Y : Submodule ℂ (K → ℂ)) (hY : ∀ f ∈ Y, ∀ k, (fun x => f (k * x)) ∈ Y) :
    Representation ℂ K (Module.Dual ℂ Y) where
  toFun k := (shiftL Y hY k).dualMap
  map_one' := by
    refine LinearMap.ext fun ξ => LinearMap.ext fun f => ?_
    change ξ (shiftL Y hY 1 f) = ξ f
    congr 1
    exact Subtype.ext (funext fun x => by simp [shiftL])
  map_mul' k l := by
    refine LinearMap.ext fun ξ => LinearMap.ext fun f => ?_
    change ξ (shiftL Y hY (k * l) f) = ξ (shiftL Y hY l (shiftL Y hY k f))
    congr 1
    exact Subtype.ext (funext fun x => by simp [shiftL, mul_assoc])

theorem le_coeffSpan_dualRep (Y : Submodule ℂ (K → ℂ)) (hY : ∀ f ∈ Y, ∀ k, (fun x => f (k * x)) ∈ Y) :
    Y ≤ GlobalTheory.Published.AutFin.coeffSpan (dualRep Y hY) := by
  intro f hf
  let ev : Module.Dual ℂ Y := (LinearMap.proj (1 : K)).comp Y.subtype
  refine Submodule.subset_span ⟨Module.Dual.eval ℂ Y ⟨f, hf⟩, ev, funext fun k => ?_⟩
  change f k = f (k * 1)
  rw [mul_one]

theorem isContRep_dualRep [TopologicalSpace K] [ContinuousMul K] (Y : Submodule ℂ (K → ℂ))
    (hY : ∀ f ∈ Y, ∀ k, (fun x => f (k * x)) ∈ Y) [FiniteDimensional ℂ Y] (hc : ∀ f ∈ Y, Continuous f) :
    GlobalTheory.Published.AutFin.IsContRep (dualRep Y hY) := by
  intro ℓ ξ
  let ev : K → Module.Dual ℂ Y := fun x => (LinearMap.proj x).comp Y.subtype
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    have h0 : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_dualCoannihilator] at hv
      have h2 : ∀ x, v.1 x = 0 := fun x => hv _ (Submodule.subset_span ⟨x, rfl⟩)
      rw [Submodule.mem_bot]
      exact Subtype.ext (funext h2)
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)), h0,
      Submodule.dualAnnihilator_bot]
  obtain ⟨f, rfl⟩ := (Module.evalEquiv ℂ Y).surjective ℓ
  have key : ∀ ξ ∈ Submodule.span ℂ (Set.range ev), Continuous fun k => ξ (shiftL Y hY k f) := by
    intro ξ hl
    induction hl using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, rfl⟩ := hx
      exact (hc f.1 f.2).comp (continuous_id.mul continuous_const)
    | zero => exact continuous_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul r x _ hx => exact hx.const_smul r
  exact key ξ (hspan ▸ Submodule.mem_top)

end Dual

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {M : ℕ}

theorem continuous_slice (φ : Sm E M) (g : GA E M) :
    Continuous fun k : Kinf E M => φ.1 (g * infGL E M (Unitary.toUnits k)) := by
  have h1 : Continuous fun k : Kinf E M => (Unitary.toUnits k : GL (Fin M) (Cinf E)) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_subtype_val.star⟩
  have e : (fun k : Kinf E M => φ.1 (g * infGL E M (Unitary.toUnits k))) =
      fun k => chart φ.1 g (toL (Unitary.toUnits k : GL (Fin M) (Cinf E)).val) := by
    funext k
    rw [chart_val]
  rw [e]
  have hc : ContinuousOn (chart φ.1 g) (invSet E M) := (φ.2 g).continuousOn
  have h3' : Continuous fun k : Kinf E M =>
      ((Unitary.toUnits k : GL (Fin M) (Cinf E)) : Matrix (Fin M) (Fin M) (Cinf E)) :=
    (Units.continuous_val (M := Matrix (Fin M) (Fin M) (Cinf E))).comp h1
  have h3 : Continuous fun k : Kinf E M =>
      toL ((Unitary.toUnits k : GL (Fin M) (Cinf E)) : Matrix (Fin M) (Fin M) (Cinf E)) := h3'
  exact hc.comp_continuous h3 fun k => val_mem_invSet _

theorem admissible_discrete_spaces : PositivityTheory.Rg.BcB.SpectralAccumulation.AdmDisc := by
  intro E _ _ _ M K' W' hK' hW' V hV
  haveI := hW'
  have hsc : ∀ (τ : E →+* ℂ) (u : ℂ), ∃ c : ℂ, ∀ ψ ∈ V, cap τ u ψ = c • ψ := fun τ u =>
    GlobalTheory.DiscLocEx.exists_scalarD hV (Algebra.subset_adjoin ⟨τ, u, rfl⟩) (GlobalTheory.SpehInfChar.cap_commute_act τ u)
  choose c hc using hsc
  let Y : Submodule ℂ (Kinf E M → ℂ) := Submodule.span ℂ
    {f | ∃ φ : Sm E M, φ ∈ V ∧ TypeB K' W' φ ∧ ∃ g : GA E M, f = fun k => φ.1 (g * infGL E M (Unitary.toUnits k))}
  have hYW : Y ≤ W' := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨φ, -, hφ, g, rfl⟩
    exact hφ.2 g
  haveI : FiniteDimensional ℂ Y := Submodule.finiteDimensional_of_le hYW
  have hYl : ∀ f ∈ Y, ∀ k, (fun x => f (k * x)) ∈ Y := by
    intro f hf k
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨φ, hφV, hφ, g, rfl⟩ := hf
      refine Submodule.subset_span ⟨φ, hφV, hφ, g * infGL E M (Unitary.toUnits k), funext fun x => ?_⟩
      simp only [map_mul, mul_assoc]
    | zero => exact Y.zero_mem
    | add x y _ _ hx hy => exact Y.add_mem hx hy
    | smul r x _ hx => exact Y.smul_mem r hx
  have hYc : ∀ f ∈ Y, Continuous f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨φ, -, -, g, rfl⟩ := hf
      exact continuous_slice φ g
    | zero => exact continuous_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul r x _ hx => exact hx.const_smul r
  haveI hF := PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL E M K' hK' (Module.Dual ℂ Y) (dualRep Y hYl)
    (isContRep_dualRep Y hYl hYc) c
  have hle : {φ | φ ∈ V ∧ TypeB K' W' φ} ⊆ GlobalTheory.Published.AutFinGL.forms K' (dualRep Y hYl) c := by
    rintro φ ⟨hφV, hφ⟩
    refine ⟨hV.aut φ hφV, fun k hk => Subtype.ext (funext fun g => hφ.1 k hk g), fun g => ?_,
      fun τ u => hc τ u φ hφV⟩
    exact le_coeffSpan_dualRep Y hYl (Submodule.subset_span ⟨φ, hφV, hφ, g, rfl⟩)
  exact Submodule.finiteDimensional_of_le (Submodule.span_mono hle)

end GlobalTheory.CompanionTheory.AdmDiscFin

end
end

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG

theorem hw_harm {n : ℕ} (lam : Fin n → ℤ) (hl : Antitone lam)
    (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V)
    (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (A : V →ₗ[ℂ] V) (hc : IsCoreMod (infOf lam) E1 E2 σ A)
    (ν : Fin n → ℤ) (v : V) (hv : v ≠ 0) (hh : v ∈ hwSp E1 E2 (wtR ν)) (hdom : DomLE (wtR ν) (m0 lam)) :
    ν ∈ harmZ lam := by
  obtain ⟨S, hfd, hvS, -, hKS, -⟩ := hc.der.2 v
  have hGl : Formalism.REAL.GlRel (kF E1 E2) := GlobalTheory.CompanionTheory.RealCount.KHw.glRel_kF hc.pair
  have hK : Formalism.REAL.KHighest (fun _ => true) (kF E1 E2) (wtR ν) v := hh
  have hanti : Antitone (wtR ν) := GlobalTheory.CompanionTheory.RealCount.highestWeight_antitone_of_finiteDimensional_stable V (kF E1 E2) S (wtR ν) v hGl hfd hKS hvS hv hK
  have hanti' : Antitone ν := fun a b hab => by
    have := hanti hab
    simpa [wtR] using this
  obtain ⟨ι, i1, i2, c, hcl, hconds⟩ := GlobalTheory.T.parthasarathy_rao_varadarajan n
  obtain ⟨w, hw, x, hx, hxh⟩ := hconds V (kF E1 E2) S ν v hGl hc.pair.unitK hfd hKS hvS hv hK
  have hn := GlobalTheory.T.clifford_highest_weight_vector lam V E1 E2 σ A hc ι c hcl _ x hx hxh
  exact GlobalTheory.T.harmonic_of_norm_bound lam hl ν hanti' hdom w hw hn

theorem hw_stable' {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {E1 E2 : Fin n → Fin n → Module.End ℂ V} {A : V →ₗ[ℂ] V} (hA2 : A * A = 1) (hAE : ∀ a b, A * E1 a b = E2 a b * A)
    (μ : Fin n → ℝ) : ∀ x ∈ hwSp E1 E2 μ, A x ∈ hwSp E1 E2 μ := by
  have hk : ∀ a b (y : V), A (kF E1 E2 a b y) = kF E1 E2 a b (A y) := by
    intro a b y
    have h1 : A (E1 a b y) = E2 a b (A y) := LinearMap.congr_fun (hAE a b) y
    have h2 : A (E2 a b y) = E1 a b (A y) := by
      have h3 : A (E1 a b (A y)) = E2 a b (A (A y)) := LinearMap.congr_fun (hAE a b) (A y)
      have h4 : ∀ u : V, A (A u) = u := fun u => LinearMap.congr_fun hA2 u
      rw [h4] at h3
      rw [← h3, h4]
    simp only [kF, LinearMap.add_apply, map_add (f := _), h1, h2]
    abel
  intro x hx
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · rw [← hk, hx.1 a, map_smul]
  · rw [← hk, hx.2 a b hab he, map_zero]

theorem flip_stable' {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)} {A : V →ₗ[ℂ] V} (hAσ : ∀ k, A * σ k = σ k * A)
    (E : KMod n) (T : E.V →L[ℂ] E.V) (hT : ∀ k, T * E.ρ k = E.ρ k * T) :
    ∀ t ∈ invA σ E, flipA E A T t ∈ invA σ E := by
  intro t ht k ξ
  have h1 : dualT E T (ξ ∘L E.ρ k⁻¹) = (dualT E T ξ) ∘L E.ρ k⁻¹ := by
    ext y
    have h2 := congrArg (fun S : E.V →L[ℂ] E.V => ξ (S y)) (hT k⁻¹)
    simp only [dualT, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply]
    exact (h2.symm)
  have h3 : flipA E A T t (ξ ∘L E.ρ k⁻¹) = A (t (dualT E T (ξ ∘L E.ρ k⁻¹))) := rfl
  have h4 : flipA E A T t ξ = A (t (dualT E T ξ)) := rfl
  rw [h3, h4, h1, ht k (dualT E T ξ)]
  exact LinearMap.congr_fun (hAσ k) _

theorem dual_stable' {n : ℕ} (E : KMod n) (T : E.V →L[ℂ] E.V) (hT : ∀ k, T * E.ρ k = E.ρ k * T)
    (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)) (hG : IsDualFam E G) (μ : Fin n → ℝ) :
    ∀ ξ ∈ hwOf G μ, (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) ξ ∈ hwOf G μ := by
  intro ξ hξ
  have hc := GlobalTheory.T.dual_operator_commutes_lie E T hT G hG
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · show G a a (dualT E T ξ) = _
    rw [← hc, hξ.1 a, map_smul]
    rfl
  · show G a b (dualT E T ξ) = 0
    rw [← hc, hξ.2 a b hab he, map_zero]

theorem diagonal_mem_unitary {n : ℕ} (z : Fin n → ℂ) (hz : ∀ a, ‖z a‖ = 1) :
    (diagonal z : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  refine congrArg Matrix.diagonal (funext fun a => ?_)
  change z a * (starRingEnd ℂ) (z a) = 1
  rw [Complex.mul_conj', hz a]
  simp

theorem dualtr {n : ℕ} (lam : Fin n → ℤ) (hl : Antitone lam) (E : KMod n) (T : E.V →L[ℂ] E.V) (hT : IsLefK lam E T)
    (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)) (hG : IsDualFam E G) :
    ∀ μ ∈ harmZ lam, trOn (hwOf G (wtR μ)) (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) = 2 ^ n := by
  obtain ⟨F, hF, -, hch⟩ := GlobalTheory.T.dual_weight_trace_formula E T hT.1 G hG
  intro μ hμ
  refine (GlobalTheory.T.harmonic_weights_coefficient lam hl F hF (fun ν => trOn (hwOf G (wtR ν)) (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)))
    (fun z hz hinj => ?_) μ hμ).2
  have hzi : Function.Injective z := fun a b h => hinj (by simp only [h])
  have h1 := hch ⟨diagonal z, diagonal_mem_unitary z hz⟩ z rfl hzi
  have h2 := GlobalTheory.T.twisted_trace_weyl_character lam E T hT ⟨diagonal z, diagonal_mem_unitary z hz⟩ z rfl hinj
  rw [← h1, h2]

theorem countG : CountG := by
  intro n lam hlam E T hT V _ _ E1 E2 σ A hc hfin
  obtain ⟨hsp, htop⟩ := GlobalTheory.T.dual_weights_dominated lam hlam E T hT
  obtain ⟨G, hG⟩ := GlobalTheory.T.exists_dual_lie_family E
  have hint := GlobalTheory.T.invariant_intertwines_dual V σ (kF E1 E2) hc.der E G hG
  have hmaps : ∀ t ∈ invA σ E, ∀ (μ : Fin n → ℝ), ∀ ξ ∈ hwOf G μ, t ξ ∈ hwSp E1 E2 μ := by
    intro t ht μ ξ hξ
    refine ⟨fun a => ?_, fun a b hab he => ?_⟩
    · rw [← hint t ht, hξ.1 a, map_smul]
    · rw [← hint t ht, hξ.2 a b hab he, map_zero]
  have hinj := GlobalTheory.T.finite_weights_invariant_hom V E1 E2 σ hc.pair hc.der E G hG hsp (harmZ lam)
    (fun ν v hv hh hw => hw_harm lam hlam V E1 E2 σ A hc ν v hv hh (htop ν hw))
  have hext := GlobalTheory.T.exists_invariant_extending V E1 E2 σ hc.pair hc.der E G hG (harmZ lam)
  have hA : ∀ μ, ∀ x ∈ hwSp E1 E2 μ, A x ∈ hwSp E1 E2 μ := hw_stable' hc.Asq hc.AE
  have hF : ∀ t ∈ invA σ E, flipA E A T t ∈ invA σ E := flip_stable' hc.Aσ E T hT.1
  have hB := dual_stable' E T hT.1 G hG
  have htr := dualtr lam hlam E T hT G hG
  let ι := {μ // μ ∈ harmZ lam}
  let W : ι → Type := fun i => hwOf G (wtR i.1)
  let H : ι → Type := fun i => hwSp E1 E2 (wtR i.1)
  let b : ∀ i, W i →ₗ[ℂ] W i := fun i =>
    (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)).restrict (p := hwOf G (wtR i.1)) (q := hwOf G (wtR i.1)) (hB _)
  let a : ∀ i, H i →ₗ[ℂ] H i := fun i => A.restrict (p := hwSp E1 E2 (wtR i.1)) (q := hwSp E1 E2 (wtR i.1)) (hA _)
  have e3 : ∀ i : ι, LinearMap.trace ℂ (W i) (b i) = 2 ^ n := by
    intro i
    have := htr i.1 i.2
    unfold trOn at this
    rwa [dite_eq_left (hB _)] at this
  haveI hWnt : ∀ i, Nontrivial (W i) := by
    intro i
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have h0 : b i = 0 := LinearMap.ext fun x => Subsingleton.elim _ _
    have := e3 i
    rw [h0, map_zero] at this
    exact (pow_ne_zero n (two_ne_zero : (2 : ℂ) ≠ 0)) this.symm
  let R0 : invA σ E →ₗ[ℂ] (∀ i, W i →ₗ[ℂ] H i) :=
    { toFun := fun t i => LinearMap.codRestrict (hwSp E1 E2 (wtR i.1)) (t.1 ∘ₗ (hwOf G (wtR i.1)).subtype)
        (fun ξ => hmaps t.1 t.2 _ ξ.1 ξ.2)
      map_add' := fun x y => by funext i; ext ξ; rfl
      map_smul' := fun c x => by funext i; ext ξ; rfl }
  have hR0 : ∀ (t : invA σ E) (i : ι) (ξ : W i), ((R0 t i ξ : hwSp E1 E2 (wtR i.1)) : V) = t.1 ξ.1 := fun _ _ _ => rfl
  have hbij : Function.Bijective R0 := by
    constructor
    · refine (injective_iff_map_eq_zero R0).2 fun t ht => ?_
      refine Subtype.ext (hinj t.1 t.2 fun μ hμ ξ hξ => ?_)
      have := hR0 t ⟨μ, hμ⟩ ⟨ξ, hξ⟩
      rw [ht] at this
      simpa using this.symm
    · intro f
      obtain ⟨t, ht, hf⟩ := hext (fun μ => if h : μ ∈ harmZ lam then f ⟨μ, h⟩ else 0)
      refine ⟨⟨t, ht⟩, ?_⟩
      funext i
      ext ξ
      rw [hR0]
      have := hf i.1 i.2 ξ
      rw [dite_eq_left i.2] at this
      exact this
  let R := LinearEquiv.ofBijective R0 hbij
  let Fl := (flipA E A T).restrict (p := invA σ E) (q := invA σ E) hF
  have hcomp : ∀ x i, R (Fl x) i = a i ∘ₗ R x i ∘ₗ b i := by
    intro x i
    ext ξ
    rfl
  haveI : FiniteDimensional ℂ (invA σ E) := hfin
  obtain ⟨hfd, htrace⟩ := GlobalTheory.T.trace_factor_tensor_decomp ι (invA σ E) W H R Fl a b hcomp
  have hse : harmSet lam = (harmZ lam).image wtR := harmSet_eq lam
  refine ⟨fun μ hμ => ?_, fun hne => ?_, ?_⟩
  · rw [hse, Finset.mem_image] at hμ
    obtain ⟨ν, hν, rfl⟩ := hμ
    exact ⟨hA _, hfd ⟨ν, hν⟩⟩
  · by_contra hno
    push_neg at hno
    apply hne
    refine (Submodule.eq_bot_iff _).2 fun t ht => hinj t ht fun μ hμ ξ hξ => ?_
    have h1 := hmaps t ht _ ξ hξ
    have hμ' : wtR μ ∈ harmSet lam := by
      rw [hse]
      exact Finset.mem_image_of_mem _ hμ
    rw [hno _ hμ'] at h1
    simpa using h1
  · have e1 : trOn (invA σ E) (flipA E A T) = LinearMap.trace ℂ (invA σ E) Fl := by
      unfold trOn; rw [dite_eq_left hF]
    have e2 : ∀ i : ι, trOn (hwSp E1 E2 (wtR i.1)) A = LinearMap.trace ℂ (H i) (a i) := by
      intro i
      unfold trOn; rw [dite_eq_left (hA _)]
    rw [e1, htrace, hse, Finset.sum_image (fun x _ y _ h => wtR_injective h), Finset.mul_sum,
      ← Finset.sum_coe_sort (harmZ lam)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [e3 i, e2 i]

end GlobalTheory.CompanionTheory.RealCountG
end
end
