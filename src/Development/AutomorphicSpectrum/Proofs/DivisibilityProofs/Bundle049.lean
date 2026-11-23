module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle179
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle171
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle163
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

open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RT.Inj

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

section Model
variable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (ψ : AddChar (AF F) ℂ)

theorem std_of_cof (hM : M.IsGood ψ) {φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ}
    (h2 : ∀ᶠ v in cofinite, φ v = M.vac v) :
    ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
  (h2.and hM.std).mono fun _ h => h.1.trans h.2

theorem pure_eq_pureA (hM : M.IsGood ψ) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (h1 : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _)
    (h2 : ∀ᶠ v in cofinite, φ v = M.vac v) :
    ∃ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F), ∀ f : SInf F (Fin n × Fin d), pure f φ = pureA F f g :=
  ⟨_, ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ h1 (std_of_cof M ψ hM h2),
    GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ h1 (std_of_cof M ψ hM h2)⟩, fun _ => rfl⟩

theorem pure_at (hM : M.IsGood ψ) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ)
    (h2 : ∀ᶠ v in cofinite, φ v = M.vac v) (f : SInf F (Fin n × Fin d)) (v : Pl F) :
    ∃ r : (Fin n × Fin d → AF F) → ℂ, (∀ x z, At (evFin F v) z → r (x + z) = r x) ∧
      ∀ φ₂ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ, (∀ w, w ≠ v → φ₂ w = φ w) →
        pure f φ₂ = tens (evFin F v) (φ₂ v) r := by
  classical
  obtain ⟨r, hr, e⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ (std_of_cof M ψ hM h2)
  refine ⟨r, hr, fun φ₂ h => ?_⟩
  have : φ₂ = Function.update φ v (φ₂ v) := by
    funext w
    by_cases hw : w = v
    · subst hw
      simp
    · rw [Function.update_of_ne hw, h w hw]
  rw [e (φ₂ v), ← this]
end Model

variable {B : Base F E} {Γ : Geo σ a a'} {X : Chars F E} {om : Rep σ Γ.V Γ.W} {om' : Rep σ Γ.V' Γ.W}

variable {R : RealMaps F a a'} {Rf : FinMaps F a a'}

end GlobalTheory.CompanionTheory.Ar.RT.Inj

end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem curveDeg_toZ {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} (t : X ⟶ Sp ℤ) {D : ℕ}
    (hX : IsArithVar p D) (L : HermLB p) (hL : ∀ τ, (wZ L t τ).IsCInf) (i : Z ⟶ X) [IsClosedImmersion i]
    [IsIntegral Z] [IsLocallyNoetherian Z] (hc : CharZero Γ(Z, ⊤)) (hd : topologicalKrullDim Z = 1)
    (r : (L.restr i).B.ι → Z.functionFieldˣ) (hr : IsRatSec (L.restr i).B r) :
    HermLB.curveDeg ((toZ L t hL).restr i) (r := r) hr = HermLB.curveDeg (L.restr i) hr := by
  have hv : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hc (by simpa using hd)
  have e := GlobalTheory.T.sum_logNorm_eq_sum_embeddings k Z (i ≫ p) (i ≫ t) (Int.castRingHom ℂ) hv (L.restr i)
    (((toZ L t hL).restr i).φ (Int.castRingHom ℂ))
    (wOver_restr_pow k X Z p t i L hL _).1 r hr
  unfold HermLB.curveDeg
  refine congrArg (_ - ·) ?_
  rw [finsum_eq_single _ (Int.castRingHom ℂ) fun τ h => absurd (RingHom.ext_int _ _) h]
  exact e

theorem arch_toZ {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} (t : X ⟶ Sp ℤ) {D : ℕ}
    (hX : IsArithVar p D) (L : HermLB p) (hL : ∀ τ, (wZ L t τ).IsCInf) (i : Z ⟶ X) [IsClosedImmersion i]
    [IsIntegral Z] (hc : CharZero Γ(Z, ⊤)) (e : ℕ) (hd : topologicalKrullDim Z = (e + 1 : ℕ)) (m : ℕ)
    (r : ((L.restr i).pow m).B.ι → Z.functionFieldˣ) (hr : IsRatSec ((L.restr i).pow m).B r) :
    (HermLB.ArchIntegrable ((toZ L t hL).restr i) ((toZ L t hL).restr i |>.pow m) (r := r) e hr ↔
      HermLB.ArchIntegrable (L.restr i) ((L.restr i).pow m) e hr) ∧
    (HermLB.ArchIntegrable (L.restr i) ((L.restr i).pow m) e hr →
      HermLB.archInt ((toZ L t hL).restr i) ((toZ L t hL).restr i |>.pow m) (r := r) e hr =
        HermLB.archInt (L.restr i) ((L.restr i).pow m) e hr) := by
  have hv : IsArithVar (i ≫ p) e := hX.of_isClosedImmersion i hc hd
  have hw := wOver_restr_pow k X Z p t i L hL (Int.castRingHom ℂ)
  obtain ⟨e₁, e₂⟩ := GlobalTheory.T.archIntegrable_iff_over_integers k Z (i ≫ p) (i ≫ t) (Int.castRingHom ℂ) e hv (L.restr i)
    ((L.restr i).pow m) (((toZ L t hL).restr i).φ (Int.castRingHom ℂ))
    ((((toZ L t hL).restr i).pow m).φ (Int.castRingHom ℂ)) hw.1 (hw.2 m)
    (((toZ L t hL).restr i).cInf _) e r hr
  have hτ (τ : ℤ →+* ℂ) : τ = Int.castRingHom ℂ := RingHom.ext_int _ _
  refine ⟨⟨fun H => e₁.1 (H _), fun H τ => ?_⟩, fun H => ?_⟩
  · rw [hτ τ]
    exact e₁.2 H
  · unfold HermLB.archInt
    rw [finsum_eq_single _ (Int.castRingHom ℂ) fun τ h => absurd (hτ τ) h]
    exact e₂ H

theorem isArithHeight_toZ_iff : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (hL : ∀ τ, (wZ L t τ).IsCInf) (h : X → ℝ), (toZ L t hL).IsArithHeight h ↔ L.IsArithHeight h := by
  intro k _ X p t D hX L hL h
  refine ⟨fun H => ⟨H.vertical, ?_, ?_⟩, fun H => ⟨H.vertical, ?_, ?_⟩⟩
  · intro Z i _ _ _ hc hd r hr
    exact (H.point Z i hc hd r hr).trans (curveDeg_toZ t hX L hL i hc hd r hr)
  · intro Z i _ _ _ hc e he hd m r hr
    obtain ⟨e₁, e₂⟩ := arch_toZ t hX L hL i hc e hd m r hr
    obtain ⟨h₁, h₂⟩ := H.recursion Z i hc e he hd m r hr
    have h₃ := e₁.1 h₁
    exact ⟨h₃, h₂.trans (congrArg (_ - ·) (e₂ h₃))⟩
  · intro Z i _ _ _ hc hd r hr
    exact (H.point Z i hc hd r hr).trans (curveDeg_toZ t hX L hL i hc hd r hr).symm
  · intro Z i _ _ _ hc e he hd m r hr
    obtain ⟨e₁, e₂⟩ := arch_toZ t hX L hL i hc e hd m r hr
    obtain ⟨h₁, h₂⟩ := H.recursion Z i hc e he hd m r hr
    exact ⟨e₁.2 h₁, h₂.trans (congrArg (_ - ·) (e₂ h₁).symm)⟩

end GlobalTheory.CompanionTheory.Ar.BaseZ
end
end
