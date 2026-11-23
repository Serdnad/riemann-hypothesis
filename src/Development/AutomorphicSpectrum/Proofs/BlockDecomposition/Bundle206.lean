module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import GroundTheory.AutomorphicForms.GL2.AdelicFourier2TensorCosetIndicatorAlgebraMap
import GroundTheory.GlobalFields.TateThesis.AdelePoisson
public import GroundTheory.GlobalFields.TateThesis.Bundle009
public import GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite
public import GroundTheory.GlobalFields.TateThesis.Bundle008
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.RightHolRightHolEq
import GroundTheory.AutomorphicForms.GL2.GodementSection
import GroundTheory.AutomorphicForms.GL2.SummableNormIffAndTsumEqCoset2
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.GlobalFields.TateThesis.Bundle001
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue

variable {K : Type} [Field K]

def topResEquiv (hT : TopRes) {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} K) (U : ObjectProperty C)
    (hU : ∀ T, U T) (n : ℕ) : CH.H F n ≃ₗ[K] CH.H (U.ι ⋙ F) n :=
  LinearEquiv.ofBijective ((CH.Mor.restrict F U.ι).pull n)
    (CrystallineSemistableComparison.P.mapH_bij (CH.Mor.restrict F U.ι).hom (fun m => (hT K C F U ⊥ hU m).1) n)

theorem cls_congr' {R : Type} [CommRing R] {L : Cx.{1} R} {n : ℕ} {x y : L.X n} (e : x = y) (hx : L.d n x = 0)
    (hy : L.d n y = 0) : L.cls x hx = L.cls y hy := by
  subst e
  rfl

theorem XD.pr_restrict (E : XD K) (U₁ : ObjectProperty E.C₁) (U₂ : ObjectProperty E.C₂) (U₃ : ObjectProperty E.D)
    (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) {a a' c p q n : ℕ} (ha : a + a' = c)
    (h : p + q = n) (x : CH.Cn (E.F₁ a) p) (y : CH.Cn (E.F₂ a') q) :
    (E.pr U₁ U₂ U₃ h₁ h₂ ha).μ h ((CH.Mor.restrict (E.F₁ a) U₁.ι).pullC p x)
        ((CH.Mor.restrict (E.F₂ a') U₂.ι).pullC q y) =
      (CH.Mor.restrict (E.F₃ c) U₃.ι).pullC n
        ((E.μ ha).cupC h ((E.m₁ a).pullC p x) ((E.m₂ a').pullC q y)) := by
  funext s
  rfl

theorem XD.kun_cup (hT : TopRes) (E : XD K) (U₁ : ObjectProperty E.C₁) (U₂ : ObjectProperty E.C₂)
    (U₃ : ObjectProperty E.D) (hU₁ : ∀ T, U₁ T) (hU₂ : ∀ T, U₂ T) (hU₃ : ∀ T, U₃ T)
    (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) {c n : ℕ}
    (e : (⨁ t : Idx c n, (CH.cx (U₁.ι ⋙ E.F₁ t.a)).H t.i ⊗[K] (CH.cx (U₂.ι ⋙ E.F₂ t.a')).H t.j) ≃ₗ[K]
      (CH.cx (U₃.ι ⋙ E.F₃ c)).H n)
    (he : ∀ (t : Idx c n) (x : (CH.cx (U₁.ι ⋙ E.F₁ t.a)).X t.i) (y : (CH.cx (U₂.ι ⋙ E.F₂ t.a')).X t.j)
      (hx : (CH.cx (U₁.ι ⋙ E.F₁ t.a)).d t.i x = 0) (hy : (CH.cx (U₂.ι ⋙ E.F₂ t.a')).d t.j y = 0)
      (hz : (CH.cx (U₃.ι ⋙ E.F₃ c)).d n ((E.pr U₁ U₂ U₃ h₁ h₂ t.ha).μ t.h x y) = 0),
      e (DirectSum.lof K _ (fun t : Idx c n => (CH.cx (U₁.ι ⋙ E.F₁ t.a)).H t.i ⊗[K] (CH.cx (U₂.ι ⋙ E.F₂ t.a')).H t.j) t
        ((CH.cx (U₁.ι ⋙ E.F₁ t.a)).cls x hx ⊗ₜ (CH.cx (U₂.ι ⋙ E.F₂ t.a')).cls y hy)) =
        (CH.cx (U₃.ι ⋙ E.F₃ c)).cls ((E.pr U₁ U₂ U₃ h₁ h₂ t.ha).μ t.h x y) hz)
    (t : Idx c n) (u : CH.H (E.F₁ t.a) t.i) (v : CH.H (E.F₂ t.a') t.j) :
    topResEquiv hT (E.F₃ c) U₃ hU₃ n
        ((E.μ t.ha).cup t.h ((E.m₁ t.a).pull t.i u) ((E.m₂ t.a').pull t.j v)) =
      e (DirectSum.lof K _ (fun t : Idx c n => (CH.cx (U₁.ι ⋙ E.F₁ t.a)).H t.i ⊗[K] (CH.cx (U₂.ι ⋙ E.F₂ t.a')).H t.j) t
        (topResEquiv hT (E.F₁ t.a) U₁ hU₁ t.i u ⊗ₜ topResEquiv hT (E.F₂ t.a') U₂ hU₂ t.j v)) := by
  obtain ⟨x, hx, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj u
  obtain ⟨y, hy, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj v
  have hx₁ := CrystallineSemistableComparison.CechClassBoundaries.cyc (E.m₁ t.a).hom x hx
  have hy₁ := CrystallineSemistableComparison.CechClassBoundaries.cyc (E.m₂ t.a').hom y hy
  obtain ⟨hc, ec⟩ := CrystallineSemistableComparison.P.cup_cls (E.μ t.ha) t.h _ _ hx₁ hy₁
  have hx₂ := CrystallineSemistableComparison.CechClassBoundaries.cyc (CH.Mor.restrict (E.F₁ t.a) U₁.ι).hom x hx
  have hy₂ := CrystallineSemistableComparison.CechClassBoundaries.cyc (CH.Mor.restrict (E.F₂ t.a') U₂.ι).hom y hy
  have hc₂ := CrystallineSemistableComparison.CechClassBoundaries.cyc (CH.Mor.restrict (E.F₃ c) U₃.ι).hom _ hc
  have hz : (CH.cx (U₃.ι ⋙ E.F₃ c)).d n ((E.pr U₁ U₂ U₃ h₁ h₂ t.ha).μ t.h
      ((CH.Mor.restrict (E.F₁ t.a) U₁.ι).pullC t.i x) ((CH.Mor.restrict (E.F₂ t.a') U₂.ι).pullC t.j y)) = 0 := by
    rw [XD.pr_restrict]
    exact hc₂
  have key := he t _ _ hx₂ hy₂ hz
  refine Eq.trans ?_ key.symm |>.trans rfl
  change (CH.Mor.restrict (E.F₃ c) U₃.ι).pull n ((E.μ t.ha).cup t.h ((CH.cx _).cls _ hx₁) ((CH.cx _).cls _ hy₁)) = _
  rw [ec]
  exact cls_congr' (XD.pr_restrict E U₁ U₂ U₃ h₁ h₂ t.ha t.h x y).symm hc₂ hz

def sliceMap {A₀ B₀ A B : Type*} [AddCommGroup A₀] [Module K A₀] [AddCommGroup B₀] [Module K B₀] [AddCommGroup A]
    [Module K A] [AddCommGroup B] [Module K B] (r₁ : A₀ ≃ₗ[K] A) (r₂ : B₀ ≃ₗ[K] B) (φ : Module.Dual K A₀) :
    A ⊗[K] B →ₗ[K] B₀ :=
  (TensorProduct.lid K B₀).toLinearMap ∘ₗ TensorProduct.map (φ ∘ₗ r₁.symm.toLinearMap) r₂.symm.toLinearMap

theorem sliceMap_tmul {A₀ B₀ A B : Type*} [AddCommGroup A₀] [Module K A₀] [AddCommGroup B₀] [Module K B₀] [AddCommGroup A]
    [Module K A] [AddCommGroup B] [Module K B] (r₁ : A₀ ≃ₗ[K] A) (r₂ : B₀ ≃ₗ[K] B) (φ : Module.Dual K A₀) (u : A₀) (v : B₀) :
    sliceMap r₁ r₂ φ (r₁ u ⊗ₜ r₂ v) = φ u • v := by
  simp [sliceMap]

def compMap {ι : Type*} [DecidableEq ι] (N : ι → Type*) [∀ t, AddCommGroup (N t)] [∀ t, Module K (N t)]
    {A T W : Type*} [AddCommGroup A] [Module K A] [AddCommGroup T] [Module K T] [AddCommGroup W] [Module K W]
    (ρ : A ≃ₗ[K] T) (e : (⨁ t, N t) ≃ₗ[K] T) (t₀ : ι) (g : N t₀ →ₗ[K] W) : A →ₗ[K] W :=
  g ∘ₗ DirectSum.component K ι N t₀ ∘ₗ e.symm.toLinearMap ∘ₗ ρ.toLinearMap

theorem compMap_self {ι : Type*} [DecidableEq ι] (N : ι → Type*) [∀ t, AddCommGroup (N t)] [∀ t, Module K (N t)]
    {A T W : Type*} [AddCommGroup A] [Module K A] [AddCommGroup T] [Module K T] [AddCommGroup W] [Module K W]
    (ρ : A ≃ₗ[K] T) (e : (⨁ t, N t) ≃ₗ[K] T) (t₀ : ι) (g : N t₀ →ₗ[K] W) (x : A) (w : N t₀)
    (hx : ρ x = e (DirectSum.lof K ι N t₀ w)) : compMap N ρ e t₀ g x = g w := by
  simp only [compMap, LinearMap.comp_apply, LinearEquiv.coe_coe, hx, LinearEquiv.symm_apply_apply]
  rw [DirectSum.component.lof_self]

theorem compMap_ne {ι : Type*} [DecidableEq ι] (N : ι → Type*) [∀ t, AddCommGroup (N t)] [∀ t, Module K (N t)]
    {A T W : Type*} [AddCommGroup A] [Module K A] [AddCommGroup T] [Module K T] [AddCommGroup W] [Module K W]
    (ρ : A ≃ₗ[K] T) (e : (⨁ t, N t) ≃ₗ[K] T) (t₀ : ι) (g : N t₀ →ₗ[K] W) (x : A) (t : ι) (w : N t) (ht : t ≠ t₀)
    (hx : ρ x = e (DirectSum.lof K ι N t w)) : compMap N ρ e t₀ g x = 0 := by
  simp only [compMap, LinearMap.comp_apply, LinearEquiv.coe_coe, hx, LinearEquiv.symm_apply_apply]
  rw [DirectSum.component.of, dite_eq_right ht, map_zero]

theorem XD.slant (hT : TopRes) (E : XD K) (U₁ : ObjectProperty E.C₁) (U₂ : ObjectProperty E.C₂)
    (U₃ : ObjectProperty E.D) (hU₁ : ∀ T, U₁ T) (hU₂ : ∀ T, U₂ T) (hU₃ : ∀ T, U₃ T)
    (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) (hK : E.Kun U₁ U₂ U₃ h₁ h₂)
    (a i a' j c n : ℕ) (ha : a + a' = c) (h : i + j = n) (φ : Module.Dual K (CH.H (E.F₁ a) i)) :
    ∃ sl : CH.H (E.F₃ c) n →ₗ[K] CH.H (E.F₂ a') j,
      (∀ u v, sl ((E.μ ha).cup h ((E.m₁ a).pull i u) ((E.m₂ a').pull j v)) = φ u • v) ∧
      ∀ (b i' b' j' : ℕ) (hb : b + b' = c) (h' : i' + j' = n), (b, i') ≠ (a, i) →
        ∀ (u : CH.H (E.F₁ b) i') (v : CH.H (E.F₂ b') j'),
          sl ((E.μ hb).cup h' ((E.m₁ b).pull i' u) ((E.m₂ b').pull j' v)) = 0 := by
  obtain ⟨e, he⟩ := hK c n
  have kc := XD.kun_cup hT E U₁ U₂ U₃ hU₁ hU₂ hU₃ h₁ h₂ e he
  refine ⟨compMap (fun t : Idx c n => (CH.cx (U₁.ι ⋙ E.F₁ t.a)).H t.i ⊗[K] (CH.cx (U₂.ι ⋙ E.F₂ t.a')).H t.j)
    (topResEquiv hT (E.F₃ c) U₃ hU₃ n) e ⟨a, i, a', j, ha, h⟩
    (sliceMap (topResEquiv hT (E.F₁ a) U₁ hU₁ i) (topResEquiv hT (E.F₂ a') U₂ hU₂ j) φ), ?_, ?_⟩
  · intro u v
    exact (compMap_self _ _ e _ _ _ _ (kc ⟨a, i, a', j, ha, h⟩ u v)).trans (sliceMap_tmul _ _ φ u v)
  · intro b i' b' j' hb h' hne u v
    refine compMap_ne _ _ e _ _ _ ⟨b, i', b', j', hb, h'⟩ _ ?_ (kc ⟨b, i', b', j', hb, h'⟩ u v)
    intro hh
    exact hne (by rw [show b = a from congrArg Idx.a hh, show i' = i from congrArg Idx.i hh])

theorem slant_of_kun : TopRes → SiteLaws → (∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q] [IsProper q'] [Smooth q'] (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q'), ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q ⊤) (inU q' ⊤) (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤)) h₁ h₂) → Slant := by
  intro hT hS hK K _ _ X X' P q q' _ _ _ _ p₁ p₂ hP a i a' j c n ha h φ
  have top₁ : ∀ T, inU q ⊤ T := fun T => (hS K X X X q (𝟙 X) (𝟙 X)).2.2.1 T
  have top₂ : ∀ T, inU q' ⊤ T := fun T => (hS K X' X' X' q' (𝟙 X') (𝟙 X')).2.2.1 T
  have topP : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T := by
    have e : p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤ = ⊤ := by simp
    rw [e]
    exact fun T => (hS K P P P (p₁ ≫ q) (𝟙 P) (𝟙 P)).2.2.1 T
  have h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T) :=
    fun T _ => top₁ _
  have h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T) :=
    fun T _ => top₂ _
  exact XD.slant hT (hodgeXD q q' p₁ p₂ hP.w.symm) (inU q ⊤) (inU q' ⊤) (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤))
    top₁ top₂ topP h₁ h₂ (hK K X X' P q q' p₁ p₂ hP h₁ h₂) a i a' j c n ha h φ

end GlobalTheory.CompanionTheory.KunGlue
end
end

section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveK

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Norms

variable [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V]

end Norms

def WaveUniq : Prop :=
  ∀ (n : ℕ) (E : KMod n) (u v : ℝ → Mat n → E.V), IsWave E u → IsWave E v → (∀ g ∈ GLs n, u 0 g = v 0 g) →
    ∀ t, ∀ x ∈ GLs n, u t x = v t x

end GlobalTheory.CompanionTheory.WaveK
end
end

section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal
open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveCp.Rep.Frame

variable {n : ℕ}

theorem contDiffOn_inv_real : ContDiffOn ℝ ∞ (fun x : Mat n => x⁻¹) (GLs n) :=
  ReciprocityTheory.ChartRestriction.DS.Lap.LemK.contDiffOn_inv_det_ne_zero.restrict_scalars ℝ

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

end GlobalTheory.CompanionTheory.WaveCp.Rep.Frame

namespace GlobalTheory.CompanionTheory.WaveCp.Rep

end GlobalTheory.CompanionTheory.WaveCp.Rep
end
end

section

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.EisRk1Bound

open NumberField NumberField.mixedEmbedding IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical nonZeroDivisors Pointwise
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Adele2

set_option synthInstance.maxSize 1000

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem vecMul_vecMul_inv (x : Fin 2 → 𝔸[K]) (h : GL (Fin 2) 𝔸[K]) :
    (x ᵥ* (h : Matrix (Fin 2) (Fin 2) 𝔸[K])) ᵥ*
      ((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K]) = x := by
  rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]

theorem continuous_infRingHom : Continuous (infRingHom (K := K)) := by
  exact (GroundTheory.Global.homeomorphMixedSpace K).continuous.comp continuous_fst

theorem continuous_finRingHom : Continuous (finRingHom (K := K)) := by
  exact continuous_snd

theorem continuous_inv_entry (i j : Fin 2) :
    Continuous fun h : GL (Fin 2) 𝔸[K] ↦
      ((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K]) i j := by
  exact Units.continuous_coe_inv.matrix_elem i j

private theorem mul_mem_idealFiniteAdeles_of_mem_integral {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {x a : 𝔸ᶠ[K]}
    (hx : x ∈ idealFiniteAdeles I) (ha : a ∈ integralFiniteAdeles (𝓞 K) K) :
    a * x ∈ idealFiniteAdeles I := by
  change ∀ v, Valued.v ((a * x) v) ≤ _
  intro v
  have h1 : Valued.v (x v) ≤ WithZero.exp (-FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)) :=
    hx v
  have h2 : Valued.v (a v) ≤ 1 := (mem_adicCompletionIntegers _ _ _).mp (ha v)
  have h3 : (a * x) v = a v * x v := rfl
  rw [h3, Valuation.map_mul]
  calc Valued.v (a v) * Valued.v (x v) ≤ 1 * Valued.v (x v) := mul_le_mul' h2 le_rfl
    _ ≤ _ := by rw [one_mul]; exact h1

private theorem mem_idealFiniteAdeles_one_of_mem_integral {a : 𝔸ᶠ[K]} (ha : a ∈ integralFiniteAdeles (𝓞 K) K) :
    a ∈ idealFiniteAdeles (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) := by
  change ∀ v, Valued.v (a v) ≤ _
  intro v
  rw [Units.val_one, FractionalIdeal.count_one, neg_zero, WithZero.exp_zero]
  exact (mem_adicCompletionIntegers _ _ _).mp (ha v)

theorem exists_fractionalIdeal_of_isCompact (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : Fin 2 → 𝔸ᶠ[K])
    {C : Set (GL (Fin 2) 𝔸[K])} (hC : IsCompact C) :
    ∃ J : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ∀ h ∈ C, ∀ ξ : Fin 2 → K,
      (∀ i, finPart ((fun i ↦ algebraMap K 𝔸[K] (ξ i)) ᵥ* (h : Matrix (Fin 2) (Fin 2) 𝔸[K])) i - b i ∈
        idealFiniteAdeles I) → ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 K)⁰ K) := by
  set S : Set 𝔸ᶠ[K] := ((⋃ i : Fin 2, ⋃ j : Fin 2,
      (fun h : GL (Fin 2) 𝔸[K] =>
        finRingHom (((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K]) i j)) '' C) ∪
      Set.range b) ∪ {1} with hS
  have hSc : IsCompact S :=
    ((isCompact_iUnion fun i => isCompact_iUnion fun j =>
      hC.image (continuous_finRingHom.comp (continuous_inv_entry i j))).union
      (isCompact_range continuous_of_discreteTopology)).union isCompact_singleton
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hSc
  have hL0 : ((I : FractionalIdeal (𝓞 K)⁰ K) ⊔ 1) ≠ 0 := by
    intro h0
    have h1 : (1 : FractionalIdeal (𝓞 K)⁰ K) ≤ 0 := h0 ▸ le_sup_right
    exact one_ne_zero (le_antisymm h1 (FractionalIdeal.zero_le _))
  set L : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 _ hL0 with hLdef
  have hIL : (idealFiniteAdeles I : Set 𝔸ᶠ[K]) ⊆ idealFiniteAdeles L :=
    idealFiniteAdeles_subset (by rw [hLdef, Units.val_mk0]; exact le_sup_left)
  have h1L : (idealFiniteAdeles (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Set 𝔸ᶠ[K]) ⊆ idealFiniteAdeles L :=
    idealFiniteAdeles_subset (by rw [hLdef, Units.val_mk0, Units.val_one]; exact le_sup_right)
  set e : K := algebraMap (𝓞 K) K d with he_def
  have he : e ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0
  have hE0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ (e⁻¹ * e⁻¹) * (L : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    mul_ne_zero ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr
      (mul_ne_zero (inv_ne_zero he) (inv_ne_zero he))) (Units.ne_zero L)
  refine ⟨Units.mk0 _ hE0, fun h hh ξ hξ i => ?_⟩
  set y := finPart ((fun i ↦ algebraMap K 𝔸[K] (ξ i)) ᵥ* (h : Matrix (Fin 2) (Fin 2) 𝔸[K])) with hy
  have hrec : (fun i => algebraMap K 𝔸ᶠ[K] (ξ i)) =
      y ᵥ* ((((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K])).map finRingHom) := by
    rw [hy, ← finPart_vecMul, vecMul_vecMul_inv, finPart_algebraMap]
  have hξi : algebraMap K 𝔸ᶠ[K] (ξ i) = ∑ j, y j *
      finRingHom (((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K]) j i) := by
    rw [congrFun hrec i]
    rfl
  set E : 𝔸ᶠ[K] := algebraMap K 𝔸ᶠ[K] e with hEdef
  have hE1 : E ∈ integralFiniteAdeles (𝓞 K) K := by
    have := hd 1 (Or.inr rfl)
    rwa [mul_one] at this
  have hEs : ∀ j, E * finRingHom (((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K]) j i) ∈
      integralFiniteAdeles (𝓞 K) K := fun j =>
    hd _ (Or.inl (Or.inl (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨i, ⟨h, hh, rfl⟩⟩⟩)))
  have hEb : ∀ j, E * b j ∈ integralFiniteAdeles (𝓞 K) K := fun j =>
    hd _ (Or.inl (Or.inr ⟨j, rfl⟩))
  have hmemL : algebraMap K 𝔸ᶠ[K] (e * e * ξ i) ∈ idealFiniteAdeles L := by
    rw [map_mul, map_mul, hξi, Finset.mul_sum]
    refine sum_mem fun j _ => ?_
    have hsplit : E * E * (y j * finRingHom (((h⁻¹ : GL (Fin 2) 𝔸[K]) :
        Matrix (Fin 2) (Fin 2) 𝔸[K]) j i)) =
        (E * (E * finRingHom (((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K]) j i))) *
          (y j - b j) +
        (E * b j) * (E * finRingHom (((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K]) j i)) := by
      ring
    rw [hsplit]
    refine add_mem (hIL (mul_mem_idealFiniteAdeles_of_mem_integral (hξ j) (mul_mem hE1 (hEs j)))) ?_
    exact h1L (mem_idealFiniteAdeles_one_of_mem_integral (mul_mem (hEb j) (hEs j)))
  have hmem : e * e * ξ i ∈ (L : FractionalIdeal (𝓞 K)⁰ K) :=
    (algebraMap_mem_idealFiniteAdeles_iff L _).mp hmemL
  rw [Units.val_mk0]
  have hξeq : ξ i = (e⁻¹ * e⁻¹) * (e * e * ξ i) := by field_simp
  rw [hξeq]
  exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hmem

def latticeWeight (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (k : ℕ) (x : K) : ℝ :=
  if x ∈ (J : FractionalIdeal (𝓞 K)⁰ K) then ((1 + ‖mixedEmbedding K x‖) ^ k)⁻¹ else 0

theorem latticeWeight_nonneg (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (k : ℕ) (x : K) :
    0 ≤ latticeWeight J k x := by
  unfold latticeWeight
  split_ifs <;> positivity

end

end GlobalTheory.CompanionTheory.EisRk1Bound
end

section

open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem infiniteEmbedding_mem_standardOpenSubgroup {F : Type*} [Field F] [NumberField F]
    (w : InfinitePlace F) (a : (w.Completion)ˣ) :
    infiniteEmbedding w a ∈ standardOpenSubgroup F := by
  refine (mem_standardOpenSubgroup F).2 fun v ↦ ?_
  have h1 : ((infiniteEmbedding w a : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := by
    rw [coe_infiniteEmbedding]
    rfl
  have h2 : (((infiniteEmbedding w a)⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := by
    rw [← map_inv, coe_infiniteEmbedding]
    rfl
  rw [h1, h2]
  exact ⟨one_mem _, one_mem _⟩

theorem infiniteParams_eq_zero {F : Type*} [Field F] [NumberField F] (χ : HeckeCharacter F)
    (hχ : standardOpenSubgroup F ≤ χ.toIdele.ker) (w : InfinitePlace F) :
    χ.infiniteParams w = (0, 0) := by
  refine (χ.infiniteParams_unique w (p := (0, 0)) (fun _ ↦ ⟨le_rfl, by norm_num⟩) fun a ↦ ?_).symm
  have h : χ.toIdele (infiniteEmbedding w a) = 1 :=
    hχ (infiniteEmbedding_mem_standardOpenSubgroup w a)
  simp [HeckeCharacter.infiniteComponent_apply, h]

theorem gammaFactor_eq_of_unramified : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (χ : HeckeCharacter F), standardOpenSubgroup F ≤ χ.toIdele.ker →
    ∀ s : ℂ, χ.gammaFactor s = Complex.Gammaℝ s ^ Module.finrank ℚ F := by
  intro F _ _ _ χ hχ s
  have hw : ∀ w : InfinitePlace F, χ.infiniteGamma w s = Complex.Gammaℝ s := fun w ↦ by
    have hr : w.IsReal := IsTotallyReal.isReal w
    have hp := infiniteParams_eq_zero χ hχ w
    simp [HeckeCharacter.infiniteGamma, hr, HeckeCharacter.infiniteTau,
      HeckeCharacter.infiniteWeight, hp]
  have hcard : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank F
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F
    have h3 := IsTotallyReal.nrComplexPlaces_eq_zero F
    omega
  rw [HeckeCharacter.gammaFactor, Finset.prod_congr rfl fun w _ ↦ hw w, Finset.prod_const,
    Finset.card_univ, hcard]

end GlobalTheory.CompanionTheory.PartialZeta
end

section

open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Adele2 GroundTheory.Automorphic.GodementSection IdeleGroup

namespace GlobalTheory.CompanionTheory.EisRk1Theta

variable {K : Type*} [Field K] [NumberField K]

theorem continuous_setIntegral_of_continuous_uncurry {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (ν : Measure Y)
    [IsFiniteMeasureOnCompacts ν] {E : Set Y} (hE : IsCompact (closure E)) (hν : ν E < ⊤)
    {f : X → Y → ℂ} (hf : Continuous (Function.uncurry f)) :
    Continuous fun x ↦ ∫ u in E, f x u ∂ν := by
  have hint : ∀ x, IntegrableOn (f x) E ν := fun x ↦ by
    have hc : Continuous (f x) := hf.comp (Continuous.prodMk_right x)
    exact (hc.continuousOn.integrableOn_compact hE).mono_set subset_closure
  refine continuous_iff_continuousAt.2 fun q ↦ Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  set m := ν.real E with hm
  have hm0 : 0 ≤ m := measureReal_nonneg
  have hδ : 0 < ε / (2 * (m + 1)) := by positivity
  obtain ⟨v, hv, hvu⟩ := hE.mem_uniformity_of_prod (f := f) (s := Set.univ) (q := q)
    hf.continuousOn (Set.mem_univ q) (Metric.dist_mem_uniformity hδ)
  rw [nhdsWithin_univ] at hv
  filter_upwards [hv] with p hp
  rw [dist_eq_norm, ← integral_sub (hint p) (hint q)]
  have hb : ‖∫ u in E, (f p u - f q u) ∂ν‖ ≤ ε / (2 * (m + 1)) * m := by
    refine norm_setIntegral_le_of_norm_le_const hν fun u hu ↦ ?_
    have := hvu p hp u (subset_closure hu)
    rw [Set.mem_setOf_eq, dist_eq_norm] at this
    exact this.le
  refine hb.trans_lt ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

end GlobalTheory.CompanionTheory.EisRk1Theta
end
