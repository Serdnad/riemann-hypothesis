module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle005
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle285
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetLIntegralLeOfBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle286
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.AutomorphicLipschitz.NiceAut
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.BoxVolumes.ExistsMeasureLeProd
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ConjugationDifferences.ExpDivExpEq
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ConstantTermSteps.CtstepglueHolds
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFgC
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SquareIntegrableCovers.SetLIntegralLeOfCover
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.UniformInitialGrowth.InitBnd
import GroundTheory.AutomorphicForms.QuotientMeasure
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

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs GlobalTheory.SmGL

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ} {U : Submodule ℂ (Sm E (r + s))}
  {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)}

theorem orbSpan_le {a : ℕ} {V : Submodule ℂ (Sm E a)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) {φ : Sm E a} (hφ : φ ∈ V) :
    GlobalTheory.CuspRep.LocEx.orbSpan φ ≤ V :=
  Submodule.span_le.2 (by rintro _ ⟨κ, rfl⟩; exact hV (.cpt κ) φ hφ)

theorem stepA_left (hexp : HExp U T) {β : Sm E (r + s)} (hβ : β ∈ U) :
    ∃ F : Finset (Sm E r), (↑F : Set (Sm E r)) ⊆ BlockDerivatives.LS U T ∧
      ∀ m₂, sl0 m₂ (T β) ∈ Submodule.span ℂ (↑F : Set (Sm E r)) := by
  classical
  have hx := exp_one hexp hβ
  obtain ⟨n, b, q, hb, -, he⟩ := hx
  have h : ∀ i, ∃ Fi : Finset (Sm E r), (↑Fi : Set (Sm E r)) ⊆ BlockDerivatives.lsF r s (T β) 1 1 ∧
      b i ∈ Submodule.span ℂ (↑Fi : Set (Sm E r)) := fun i => Submodule.mem_span_finite_of_mem_span (hb i)
  choose Fi hFi hbFi using h
  refine ⟨Finset.univ.biUnion Fi, ?_, fun m₂ => ?_⟩
  · intro ℓ hℓ
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hℓ)
    exact BlockDerivatives.lsF_sub_LS hβ 1 1 (hFi i hi)
  · rw [left_slice_eq_sum (T β) b q he m₂]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    exact Submodule.span_mono (fun x hx => Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hx⟩))
      (hbFi i)

theorem stepA_right (hexp : HExp U T) {β : Sm E (r + s)} (hβ : β ∈ U) :
    ∃ F : Finset (Sm E s), (↑F : Set (Sm E s)) ⊆ BlockDerivatives.RS U T ∧
      ∀ m₁, sl1 m₁ (T β) ∈ Submodule.span ℂ (↑F : Set (Sm E s)) := by
  classical
  have hx := exp_one hexp hβ
  obtain ⟨n, b, q, -, hq, he⟩ := hx
  refine ⟨Finset.univ.image q, ?_, fun m₁ => ?_⟩
  · intro ℓ hℓ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hℓ)
    exact BlockDerivatives.rsF_sub_RS hβ 1 1 (hq i)
  · rw [right_slice_eq_sum (T β) b q he m₁]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem q (Finset.mem_univ i))))

theorem stepB_left (hU : IsAutSt U) (hexp : HExp U T) {φ : Sm E (r + s)} (hφ : φ ∈ U) :
    ∃ F : Finset (Sm E r), (↑F : Set (Sm E r)) ⊆ BlockDerivatives.LS U T ∧
      ∀ (κ : Kinf E (r + s)) (m₂ : GA E s), sl0 m₂ (T (act (.cpt κ) φ)) ∈ Submodule.span ℂ (↑F : Set (Sm E r)) := by
  classical
  have hfd : FiniteDimensional ℂ (GlobalTheory.CuspRep.LocEx.orbSpan φ) := (hU.2 φ hφ).kfin
  have hfg' := (Submodule.fg_iff_finiteDimensional _).2 hfd
  obtain ⟨B, hB⟩ := hfg'
  have hBU : ∀ β ∈ B, β ∈ U := fun β hβ =>
    orbSpan_le hU.1 hφ (hB ▸ Submodule.subset_span (Finset.mem_coe.2 hβ))
  have hc := collect (α := Sm E (r + s)) (β := Sm E r) B (BlockDerivatives.LS U T)
    (fun (β : Sm E (r + s)) (F : Finset (Sm E r)) => ∀ m₂, sl0 m₂ (T β) ∈ Submodule.span ℂ (↑F : Set (Sm E r)))
    (fun β F F' hFF' h m₂ => Submodule.span_mono (Finset.coe_subset.2 hFF') (h m₂))
    (fun β hβ => stepA_left hexp (hBU β hβ))
  obtain ⟨F, hF, hQ⟩ := hc
  refine ⟨F, hF, fun κ m₂ => ?_⟩
  have hmem : act (.cpt κ) φ ∈ Submodule.span ℂ (↑B : Set (Sm E (r + s))) :=
    hB ▸ Submodule.subset_span ⟨κ, rfl⟩
  have hle : Submodule.span ℂ (↑B : Set (Sm E (r + s))) ≤
      (Submodule.span ℂ (↑F : Set (Sm E r))).comap (sl0 m₂ ∘ₗ T) :=
    Submodule.span_le.2 fun β hβ => hQ β (Finset.mem_coe.1 hβ) m₂
  exact hle hmem

theorem stepB_right (hU : IsAutSt U) (hexp : HExp U T) {φ : Sm E (r + s)} (hφ : φ ∈ U) :
    ∃ F : Finset (Sm E s), (↑F : Set (Sm E s)) ⊆ BlockDerivatives.RS U T ∧
      ∀ (κ : Kinf E (r + s)) (m₁ : GA E r), sl1 m₁ (T (act (.cpt κ) φ)) ∈ Submodule.span ℂ (↑F : Set (Sm E s)) := by
  classical
  have hfd : FiniteDimensional ℂ (GlobalTheory.CuspRep.LocEx.orbSpan φ) := (hU.2 φ hφ).kfin
  have hfg' := (Submodule.fg_iff_finiteDimensional _).2 hfd
  obtain ⟨B, hB⟩ := hfg'
  have hBU : ∀ β ∈ B, β ∈ U := fun β hβ =>
    orbSpan_le hU.1 hφ (hB ▸ Submodule.subset_span (Finset.mem_coe.2 hβ))
  have hc := collect (α := Sm E (r + s)) (β := Sm E s) B (BlockDerivatives.RS U T)
    (fun (β : Sm E (r + s)) (F : Finset (Sm E s)) => ∀ m₁, sl1 m₁ (T β) ∈ Submodule.span ℂ (↑F : Set (Sm E s)))
    (fun β F F' hFF' h m₁ => Submodule.span_mono (Finset.coe_subset.2 hFF') (h m₁))
    (fun β hβ => stepA_right hexp (hBU β hβ))
  obtain ⟨F, hF, hQ⟩ := hc
  refine ⟨F, hF, fun κ m₁ => ?_⟩
  have hmem : act (.cpt κ) φ ∈ Submodule.span ℂ (↑B : Set (Sm E (r + s))) :=
    hB ▸ Submodule.subset_span ⟨κ, rfl⟩
  have hle : Submodule.span ℂ (↑B : Set (Sm E (r + s))) ≤
      (Submodule.span ℂ (↑F : Set (Sm E s))).comap (sl1 m₁ ∘ₗ T) :=
    Submodule.span_le.2 fun β hβ => hQ β (Finset.mem_coe.1 hβ) m₁
  exact hle hmem

theorem right_inv_of_stab (_hU : IsAutSt U) {c : ℂ} (hT : IsSliceMap U c T) {ψ₀ : Sm E (r + s)} (hψ₀ : ψ₀ ∈ U)
    {l : GL (Fin (r + s)) (Af E)} (hl : l ∈ JFinTr.stabFin ψ₀) (y : GA E (r + s)) :
    (T ψ₀).1 (y * finGL E (r + s) l) = (T ψ₀).1 y := by
  have h1 : act (.fin l) ψ₀ = ψ₀ := hl
  have h2 := hT.equiv (.fin l) ψ₀ hψ₀
  rw [h1] at h2
  have h3 := congrArg (fun F : Sm E (r + s) => F.1 y) h2
  rw [act_fin_eq, rt_apply, yp_one_fin] at h3
  exact h3.symm

theorem stepC_left (hU : IsAutSt U) {c : ℂ} (hT : IsSliceMap U c T) (hexp : HExp U T) {ψ₀ : Sm E (r + s)}
    (hψ₀ : ψ₀ ∈ U) :
    ∃ F : Finset (Sm E r), (↑F : Set (Sm E r)) ⊆ BlockDerivatives.LS U T ∧ ∀ W : Submodule ℂ (Sm E r), _root_.GlobalTheory.CuspRep.IsStable W →
      (↑F : Set (Sm E r)) ⊆ W → ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₂ : GA E s),
        sl0 m₂ (T (GlobalTheory.CuspRep.rt E (r + s) (BlockDerivatives.yp k g) ψ₀)) ∈ W := by
  classical
  have hL : IsOpen ((JFinTr.stabFin ψ₀ : Subgroup (GL (Fin (r + s)) (Af E))) : Set (GL (Fin (r + s)) (Af E))) :=
    (hU.2 ψ₀ hψ₀).level
  have hcov := cover (r := r) (s := s) (JFinTr.stabFin ψ₀) hL
  obtain ⟨Tf, hTf⟩ := hcov
  have hc := collect (α := GL (Fin (r + s)) (Af E)) (β := Sm E r) Tf (BlockDerivatives.LS U T)
    (fun (t : GL (Fin (r + s)) (Af E)) (F : Finset (Sm E r)) => ∀ (κ : Kinf E (r + s)) (m₂ : GA E s),
      sl0 m₂ (T (act (.cpt κ) (act (.fin t) ψ₀))) ∈ Submodule.span ℂ (↑F : Set (Sm E r)))
    (fun t F F' hFF' h κ m₂ => Submodule.span_mono (Finset.coe_subset.2 hFF') (h κ m₂))
    (fun t _ => stepB_left hU hexp (hU.1 (.fin t) ψ₀ hψ₀))
  obtain ⟨F, hF, hQ⟩ := hc
  refine ⟨F, hF, fun W hW hFW k g m₂ => ?_⟩
  obtain ⟨x, a, b, t, l, ht, hl, rfl⟩ := hTf g
  rw [T_rt_yp hU.1 hT.equiv k _ hψ₀,
    slice_decomp_left (T ψ₀) (hT.unipInv ψ₀ hψ₀) l (right_inv_of_stab hU hT hψ₀ hl) k x a b t m₂]
  refine hW (.fin a) _ ?_
  rw [← T_rt_yp hU.1 hT.equiv k t hψ₀, rt_yp_eq]
  exact Submodule.span_le.2 hFW (hQ t ht k _)

theorem stepC_right (hU : IsAutSt U) {c : ℂ} (hT : IsSliceMap U c T) (hexp : HExp U T) {ψ₀ : Sm E (r + s)}
    (hψ₀ : ψ₀ ∈ U) :
    ∃ F : Finset (Sm E s), (↑F : Set (Sm E s)) ⊆ BlockDerivatives.RS U T ∧ ∀ W : Submodule ℂ (Sm E s), _root_.GlobalTheory.CuspRep.IsStable W →
      (↑F : Set (Sm E s)) ⊆ W → ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₁ : GA E r),
        sl1 m₁ (T (GlobalTheory.CuspRep.rt E (r + s) (BlockDerivatives.yp k g) ψ₀)) ∈ W := by
  classical
  have hL : IsOpen ((JFinTr.stabFin ψ₀ : Subgroup (GL (Fin (r + s)) (Af E))) : Set (GL (Fin (r + s)) (Af E))) :=
    (hU.2 ψ₀ hψ₀).level
  have hcov := cover (r := r) (s := s) (JFinTr.stabFin ψ₀) hL
  obtain ⟨Tf, hTf⟩ := hcov
  have hc := collect (α := GL (Fin (r + s)) (Af E)) (β := Sm E s) Tf (BlockDerivatives.RS U T)
    (fun (t : GL (Fin (r + s)) (Af E)) (F : Finset (Sm E s)) => ∀ (κ : Kinf E (r + s)) (m₁ : GA E r),
      sl1 m₁ (T (act (.cpt κ) (act (.fin t) ψ₀))) ∈ Submodule.span ℂ (↑F : Set (Sm E s)))
    (fun t F F' hFF' h κ m₁ => Submodule.span_mono (Finset.coe_subset.2 hFF') (h κ m₁))
    (fun t _ => stepB_right hU hexp (hU.1 (.fin t) ψ₀ hψ₀))
  obtain ⟨F, hF, hQ⟩ := hc
  refine ⟨F, hF, fun W hW hFW k g m₁ => ?_⟩
  obtain ⟨x, a, b, t, l, ht, hl, rfl⟩ := hTf g
  rw [T_rt_yp hU.1 hT.equiv k _ hψ₀,
    slice_decomp_right (T ψ₀) (hT.unipInv ψ₀ hψ₀) l (right_inv_of_stab hU hT hψ₀ hl) k x a b t m₁]
  refine hW (.fin b) _ ?_
  rw [← T_rt_yp hU.1 hT.equiv k t hψ₀, rt_yp_eq]
  exact Submodule.span_le.2 hFW (hQ t ht k _)

theorem LS_fg (hU : IsAutSt U) {c : ℂ} (hT : IsSliceMap U c T) (hfg : FinGen U) (hexp : HExp U T) :
    ∃ S₁ : Finset (Sm E r), (↑S₁ : Set (Sm E r)) ⊆ BlockDerivatives.LS U T ∧
      ∀ W : Submodule ℂ (Sm E r), _root_.GlobalTheory.CuspRep.IsStable W → (↑S₁ : Set (Sm E r)) ⊆ W → BlockDerivatives.LS U T ≤ W := by
  classical
  obtain ⟨S₀, hS₀U, hS₀⟩ := id hfg
  have hc := collect (α := Sm E (r + s)) (β := Sm E r) S₀ (BlockDerivatives.LS U T)
    (fun (ψ₀ : Sm E (r + s)) (F : Finset (Sm E r)) => ∀ W : Submodule ℂ (Sm E r), _root_.GlobalTheory.CuspRep.IsStable W → (↑F : Set (Sm E r)) ⊆ W →
      ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₂ : GA E s),
        sl0 m₂ (T (GlobalTheory.CuspRep.rt E (r + s) (BlockDerivatives.yp k g) ψ₀)) ∈ W)
    (fun ψ₀ F F' hFF' h W hW hW' => h W hW ((Finset.coe_subset.2 hFF').trans hW'))
    (fun ψ₀ hψ₀ => stepC_left hU hT hexp (hS₀U hψ₀))
  obtain ⟨F, hF, hQ⟩ := hc
  refine ⟨F, hF, fun W hW hFW => ?_⟩
  have hUM : U ≤ Mleft U T W :=
    hS₀ _ (Mleft_stable hU hT hexp W hW) fun ψ₀ hψ₀ => ⟨hS₀U hψ₀, hQ ψ₀ hψ₀ W hW hFW⟩
  refine Submodule.span_le.2 ?_
  rintro ℓ ⟨ψ, hψ, k, g, hℓ⟩
  obtain ⟨m₂, rfl⟩ := lsF_yp (T ψ) k g ℓ hℓ
  rw [← T_rt_yp hU.1 hT.equiv k g hψ]
  exact (hUM hψ).2 k g m₂

theorem RS_fg (hU : IsAutSt U) {c : ℂ} (hT : IsSliceMap U c T) (hfg : FinGen U) (hexp : HExp U T) :
    ∃ S₁ : Finset (Sm E s), (↑S₁ : Set (Sm E s)) ⊆ BlockDerivatives.RS U T ∧
      ∀ W : Submodule ℂ (Sm E s), _root_.GlobalTheory.CuspRep.IsStable W → (↑S₁ : Set (Sm E s)) ⊆ W → BlockDerivatives.RS U T ≤ W := by
  classical
  obtain ⟨S₀, hS₀U, hS₀⟩ := id hfg
  have hc := collect (α := Sm E (r + s)) (β := Sm E s) S₀ (BlockDerivatives.RS U T)
    (fun (ψ₀ : Sm E (r + s)) (F : Finset (Sm E s)) => ∀ W : Submodule ℂ (Sm E s), _root_.GlobalTheory.CuspRep.IsStable W → (↑F : Set (Sm E s)) ⊆ W →
      ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₁ : GA E r),
        sl1 m₁ (T (GlobalTheory.CuspRep.rt E (r + s) (BlockDerivatives.yp k g) ψ₀)) ∈ W)
    (fun ψ₀ F F' hFF' h W hW hW' => h W hW ((Finset.coe_subset.2 hFF').trans hW'))
    (fun ψ₀ hψ₀ => stepC_right hU hT hexp (hS₀U hψ₀))
  obtain ⟨F, hF, hQ⟩ := hc
  refine ⟨F, hF, fun W hW hFW => ?_⟩
  have hUM : U ≤ Mright U T W :=
    hS₀ _ (Mright_stable hU hT hexp W hW) fun ψ₀ hψ₀ => ⟨hS₀U hψ₀, hQ ψ₀ hψ₀ W hW hFW⟩
  refine Submodule.span_le.2 ?_
  rintro ℓ ⟨ψ, hψ, k, g, hℓ⟩
  obtain ⟨m₁, rfl⟩ := rsF_yp (T ψ) k g ℓ hℓ
  rw [← T_rt_yp hU.1 hT.equiv k g hψ]
  exact (hUM hψ).2 k g m₁

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration
end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary PositivityTheory.Rg.Rs
open scoped Pointwise ENNReal

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

namespace Grow

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem leftInv {φ : Sm E N} (hφ : IsAutForm φ) (hcen : ∀ (t : ℝ) g, φ.1 (splitCentre E N t * g) = φ.1 g) :
    ∀ γ ∈ latticeGL E N, ∀ g, φ.1 (γ * g) = φ.1 g := by
  let S : Subgroup (GA E N) :=
    { carrier := {γ | ∀ g, φ.1 (γ * g) = φ.1 g}
      one_mem' := fun g => by rw [one_mul]
      mul_mem' := fun {x y} hx hy g => by rw [mul_assoc, hx, hy]
      inv_mem' := fun {x} hx g => by rw [← hx, mul_inv_cancel_left] }
  have : latticeGL E N ≤ S := sup_le (by rintro _ ⟨γ, rfl⟩; exact hφ.left γ) (Subgroup.zpowers_le.2 (hcen 1))
  exact this

theorem exists_kill {φ : Sm E N} (hφ : IsAutForm φ) (hcen : ∀ (t : ℝ) g, φ.1 (splitCentre E N t * g) = φ.1 g)
    {r : ℕ} (hr0 : 0 < r) (hrN : r < N) :
    ∃ p : ℂ[X], p.Monic ∧ An.Kill r φ.1 p ∧ ∀ z, p.IsRoot z → ∃ c ∈ Exp r φ.1, z = Complex.exp c := by
  obtain ⟨hA, hS, _, hCT⟩ := dict_holds E N
  have hcen' : ∀ (t : ℝ) g, φ.1 (An.tor E (fun _ => t) * g) = φ.1 g := fun t g => by
    rw [← hS]; exact hcen t g
  have hnice := niceAut_holds E N φ hφ hcen'
  have hct := (hCT φ hφ r hr0 hrN).1
  have hfin := finTr_holds E N φ hφ r hr0 hrN _ hct
  have hadd : ∀ s t, aT E N r (s + t) = aT E N r s * aT E N r t := fun s t => by
    rw [hA, hA, hA]; exact JSqIntGlue.aR_add r s t
  have hcont : ∀ g, Continuous fun t => An.ctn r φ.1 (aT E N r t * g) := by
    intro g
    have e : (fun t => An.ctn r φ.1 (aT E N r t * g)) = fun t => An.ctn r φ.1 (An.aR E N r t * g) :=
      funext fun t => by rw [hA]
    rw [e]
    exact JSqIntGlue.continuous_ctn_comp hnice.cont r ((JSqIntGlue.continuous_aR r).mul continuous_const)
  obtain ⟨p, hp, hpk, hroots⟩ := killPoly_holds (GA E N) (aT E N r) (An.ctn r φ.1) hadd hcont hfin
  refine ⟨p, hp, fun g => ?_, fun z hz => ?_⟩
  · have := hpk g
    simpa only [hA] using this
  · obtain ⟨c, rfl, F, hF, hF0, hFe⟩ := hroots z hz
    exact ⟨c, ⟨_, hct, F, hF, hF0, hFe⟩, rfl⟩

theorem bnd_of' {φ : Sm E N} (hφ : IsAutForm φ) (hcen : ∀ (t : ℝ) g, φ.1 (splitCentre E N t * g) = φ.1 g)
    (κ : ℕ → ℝ) (hκ : ∀ r, 0 < r → r < N → ∃ p : ℂ[X], p.Monic ∧ An.Kill r φ.1 p ∧
      ∀ z, p.IsRoot z → ‖z‖ < Real.exp (κ r)) : An.Bnd φ.1 κ := by
  obtain ⟨_, hS, _, _⟩ := dict_holds E N
  have hcen' : ∀ (t : ℝ) g, φ.1 (An.tor E (fun _ => t) * g) = φ.1 g := fun t g => by
    rw [← hS]; exact hcen t g
  have hnice := niceAut_holds E N φ hφ hcen'
  obtain ⟨M, hM⟩ := initBnd_holds E N φ hφ hcen'
  exact GlobalTheory.CompanionTheory.AnBoot.bootGlue diffstep_holds (ctstepglue_holds GlobalTheory.CompanionTheory.LinRec.recBound) E N φ.1 M κ hnice hM hκ

theorem bnd_of {φ : Sm E N} (hφ : IsAutForm φ) (hcen : ∀ (t : ℝ) g, φ.1 (splitCentre E N t * g) = φ.1 g)
    (κ : ℕ → ℝ) (hκ : ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, c.re < κ r) : An.Bnd φ.1 κ := by
  refine bnd_of' hφ hcen κ fun r hr0 hrN => ?_
  obtain ⟨p, hp, hk, hroots⟩ := exists_kill hφ hcen hr0 hrN
  refine ⟨p, hp, hk, fun z hz => ?_⟩
  obtain ⟨c, hc, rfl⟩ := hroots z hz
  rw [Complex.norm_exp]
  exact Real.exp_lt_exp.2 (hκ r hr0 hrN c hc)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem re_le_rho {r : ℕ} {c : ℂ} (h : pE E N r c ≤ 0) : c.re ≤ An.rho E N r := by
  have hd : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  unfold pE at h
  have h2 : c.re / (Module.finrank ℚ E : ℝ) ≤ (r : ℝ) * ((N : ℝ) - r) / 2 := by linarith
  have h3 := (div_le_iff₀ hd).1 h2
  unfold An.rho
  calc c.re ≤ (r : ℝ) * ((N : ℝ) - r) / 2 * (Module.finrank ℚ E : ℝ) := h3
    _ = _ := by ring

omit [_root_.NumberField.IsTotallyComplex E] in
theorem re_lt_rho {r : ℕ} {c : ℂ} (h : pE E N r c < 0) : c.re < An.rho E N r := by
  have hd : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  unfold pE at h
  have h2 : c.re / (Module.finrank ℚ E : ℝ) < (r : ℝ) * ((N : ℝ) - r) / 2 := by linarith
  have h3 := (div_lt_iff₀ hd).1 h2
  unfold An.rho
  calc c.re < (r : ℝ) * ((N : ℝ) - r) / 2 * (Module.finrank ℚ E : ℝ) := h3
    _ = _ := by ring

end Grow

open Grow in
theorem growPHolds : GrowPHolds := by
  intro E _ _ _ N χ hχ hcen hnp
  refine ⟨ContAut.continuous_of_isOpen_stab E N χ hχ.level, leftInv hχ hcen, fun ε hε => ?_⟩
  exact bnd_of hχ hcen _ fun r hr0 hrN c hc => by
    have := re_le_rho (hnp r hr0 hrN c hc)
    linarith

open Grow in
theorem growQHolds : GrowQHolds := by
  intro E _ _ _ N u hu hsq
  have hcen := hsq.1
  have hk : ∀ r, ∃ κ : ℝ, 0 < r → r < N → κ < An.rho E N r ∧ ∃ p : ℂ[X], p.Monic ∧ An.Kill r u.1 p ∧
      ∀ z, p.IsRoot z → ‖z‖ < Real.exp κ := by
    intro r
    by_cases hr : 0 < r ∧ r < N
    swap
    · exact ⟨0, fun h1 h2 => (hr ⟨h1, h2⟩).elim⟩
    obtain ⟨hr0, hrN⟩ := hr
    obtain ⟨p, hp, hpk, hroots⟩ := exists_kill hu hcen hr0 hrN
    have hroot' : ∀ z ∈ p.roots.toFinset, ‖z‖ < Real.exp (An.rho E N r) := by
      intro z hz
      rw [Multiset.mem_toFinset, mem_roots hp.ne_zero] at hz
      obtain ⟨c, hc, rfl⟩ := hroots z hz
      rw [Complex.norm_exp]
      exact Real.exp_lt_exp.2 (re_lt_rho (expNeg_holds E N u hu hsq r hr0 hrN c hc))
    obtain ⟨κ, hκ, hκz⟩ := JSqIntGlue.exists_lt_of_finset _ _ hroot'
    refine ⟨κ, fun _ _ => ⟨hκ, p, hp, hpk, fun z hz => hκz z ?_⟩⟩
    rw [Multiset.mem_toFinset, mem_roots hp.ne_zero]
    exact hz
  choose κ hκ using hk
  exact ⟨ContAut.continuous_of_isOpen_stab E N u hu.level, leftInv hu hcen, κ, fun r h1 h2 => (hκ r h1 h2).1,
    bnd_of' hu hcen κ fun r h1 h2 => (hκ r h1 h2).2⟩

theorem intBnd : IntBnd := by
  intro E _ _ _ N H hc h0 hl m hm hB
  obtain ⟨_, hS, hL, _⟩ := dict_holds E N
  set φ : GA E N → ℂ := fun g => ((Real.sqrt (H g) : ℝ) : ℂ) with hφ
  have hφc : Continuous φ := Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp hc)
  have hφB : An.Bnd φ (fun r => m r / 2) := by
    intro ω hω hωB t₀ Q hQ
    obtain ⟨C, hC⟩ := hB ω hω hωB t₀ Q hQ
    refine ⟨Real.sqrt (max C 0), fun b hb x hx q hq => ?_⟩
    have h1 := hC b hb x hx q hq
    rw [Complex.norm_real, Real.norm_of_nonneg (h0 _)] at h1
    set S := ∑ r ∈ Finset.range N, m r * An.sr x r with hSdef
    have e2 : ∑ r ∈ Finset.range N, m r / 2 * An.sr x r = S / 2 := by
      rw [hSdef, Finset.sum_div]
      exact Finset.sum_congr rfl fun r _ => by ring
    have e : Real.exp (∑ r ∈ Finset.range N, m r / 2 * An.sr x r) = Real.sqrt (Real.exp S) := by
      rw [e2]
      conv_rhs => rw [show S = S / 2 + S / 2 by ring]
      rw [Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le]
    have h2 : H (b * An.tor E x * q) ≤ max C 0 * Real.exp S :=
      h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    calc ‖φ (b * An.tor E x * q)‖ = Real.sqrt (H (b * An.tor E x * q)) := by
          rw [hφ, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ Real.sqrt (max C 0 * Real.exp S) := Real.sqrt_le_sqrt h2
      _ = Real.sqrt (max C 0) * Real.sqrt (Real.exp S) := Real.sqrt_mul (le_max_right _ _) _
      _ = _ := by rw [e]
  have hκ : ∀ r, 0 < r → r < N → m r / 2 < An.rho E N r := fun r h1 h2 => by
    have := hm r h1 h2
    linarith
  have hslab := GlobalTheory.CompanionTheory.SlabGlue.slabGlue boxvol_holds E N Measure.haar φ (fun r => m r / 2) hφc hφB hκ
  have hfd := isFundamentalDomain_stdDom (latticeGL E N) (Measure.haar : Measure (GA E N))
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := GroundTheory.Automorphic.Reduction.exists_siegelSet (K := E) N
  have : MeasurableConstSMul (latticeGL E N) (GA E N) := ⟨fun γ => measurable_const_mul (γ : GA E N)⟩
  have : SMulInvariantMeasure (latticeGL E N) (GA E N) (Measure.haar : Measure (GA E N)) :=
    ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  have hle := JSqIntGlue.setLIntegral_le_of_cover hfd (S := An.slab ω (max 0 (-Real.log t)))
    (fun g => by
      obtain ⟨γ, hγ, h⟩ := JSqIntGlue.exists_mem_slab hS hL ht hsieg g
      exact ⟨⟨γ, hγ⟩, h⟩) (fun g => ENNReal.ofReal (H g)) (fun γ g => by
      show ENNReal.ofReal (H (γ.1 * g)) = ENNReal.ofReal (H g)
      rw [hl γ.1 γ.2 g])
  have e : ∀ g, ‖φ g‖ₑ ^ 2 = ENNReal.ofReal (H g) := fun g => by
    show ‖((Real.sqrt (H g) : ℝ) : ℂ)‖ₑ ^ 2 = _
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
      Real.sq_sqrt (h0 g)]
  simp only [e] at hslab
  exact hle.trans_lt (hslab ω hω hωB _)

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

end
end
