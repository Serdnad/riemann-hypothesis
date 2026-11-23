module

public import GroundTheory.AutomorphicForms.SmoothRep
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import GroundTheory.AutomorphicForms.RealGroupsPolar
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Aesop.Main
public import GroundTheory.AutomorphicForms.Bundle005
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

section

noncomputable section

namespace GroundTheory.Automorphic

open Set Filter Topology

section General

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V)

theorem dual_apply_apply (g : G) (f : Module.Dual ℂ V) (v : V) :
    Representation.dual ρ g f v = f (ρ g⁻¹ v) := rfl


variable {ρ} in
theorem mem_fixedVectors_dual {H : Subgroup G} {f : Module.Dual ℂ V} :
    f ∈ fixedVectors (Representation.dual ρ) H ↔ ∀ h ∈ H, ∀ v, f (ρ h v) = f v := by
  constructor
  · intro hf h hh v
    have := LinearMap.congr_fun (hf h⁻¹ (inv_mem hh)) v
    rwa [dual_apply_apply, inv_inv] at this
  · intro hf h hh
    ext v
    rw [dual_apply_apply]
    exact hf _ (inv_mem hh) v

variable [TopologicalSpace G] [IsTopologicalGroup G]


variable {ρ} in
theorem mem_smoothVectors_of_mem_fixedVectors {H : Subgroup G} (hH : IsOpen (H : Set G))
    {v : V} (hv : v ∈ fixedVectors ρ H) : v ∈ smoothVectors ρ :=
  Subgroup.isOpen_mono (mem_fixedVectors_iff_le.1 hv) hH

variable {ρ} in
theorem mem_fixedVectors_smoothPart {H : Subgroup G} {x : smoothVectors ρ} :
    x ∈ fixedVectors (smoothPart ρ) H ↔ (x : V) ∈ fixedVectors ρ H := by
  simp only [mem_fixedVectors, Subtype.ext_iff, coe_smoothPart_apply]

def contragredient : Representation ℂ G (smoothVectors (Representation.dual ρ)) :=
  smoothPart (Representation.dual ρ)

theorem contragredient_apply_apply (g : G) (x : smoothVectors (Representation.dual ρ)) (v : V) :
    ((contragredient ρ g x : smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) v =
      (x : Module.Dual ℂ V) (ρ g⁻¹ v) := rfl

theorem isSmooth_contragredient : IsSmooth (contragredient ρ) :=
  isSmooth_smoothPart _

variable {ρ} in
theorem mem_fixedVectors_contragredient {H : Subgroup G}
    {x : smoothVectors (Representation.dual ρ)} :
    x ∈ fixedVectors (contragredient ρ) H ↔
      ∀ h ∈ H, ∀ v, (x : Module.Dual ℂ V) (ρ h v) = (x : Module.Dual ℂ V) v :=
  mem_fixedVectors_smoothPart.trans mem_fixedVectors_dual

def restrictFixed (H : Subgroup G) :
    fixedVectors (contragredient ρ) H →ₗ[ℂ] Module.Dual ℂ (fixedVectors ρ H) :=
  (fixedVectors ρ H).subtype.dualMap ∘ₗ (smoothVectors (Representation.dual ρ)).subtype ∘ₗ
    (fixedVectors (contragredient ρ) H).subtype

theorem restrictFixed_apply (H : Subgroup G) (x : fixedVectors (contragredient ρ) H)
    (v : fixedVectors ρ H) :
    restrictFixed ρ H x v =
      ((x : smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) v := rfl

def evalSmooth : V →ₗ[ℂ] Module.Dual ℂ (smoothVectors (Representation.dual ρ)) :=
  (smoothVectors (Representation.dual ρ)).subtype.dualMap ∘ₗ Module.Dual.eval ℂ V

theorem evalSmooth_apply (v : V) (x : smoothVectors (Representation.dual ρ)) :
    evalSmooth ρ v x = (x : Module.Dual ℂ V) v := rfl


variable {ρ} in
theorem evalSmooth_mem {v : V} (hv : v ∈ smoothVectors ρ) :
    evalSmooth ρ v ∈ smoothVectors (Representation.dual (contragredient ρ)) := by
  refine Subgroup.isOpen_mono (H₁ := stabilizerOf ρ v) (fun g hg => ?_) hv
  rw [mem_stabilizerOf] at hg ⊢
  ext x
  rw [dual_apply_apply, evalSmooth_apply, evalSmooth_apply, contragredient_apply_apply, inv_inv,
    hg]


variable {ρ} in
def toDoubleContragredient (hρ : IsSmooth ρ) :
    Representation.IntertwiningMap ρ (contragredient (contragredient ρ)) where
  toLinearMap := (evalSmooth ρ).codRestrict _ fun v => evalSmooth_mem (hρ v)
  isIntertwining' g := by
    refine LinearMap.ext fun v => Subtype.ext (LinearMap.ext fun x => ?_)
    change (x : Module.Dual ℂ V) (ρ g v) = (x : Module.Dual ℂ V) (ρ g⁻¹⁻¹ v)
    rw [inv_inv]

end General

section LocallyProfinite

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}

def extendFixed (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    (μ : Module.Dual ℂ (fixedVectors ρ K)) : fixedVectors (contragredient ρ) K :=
  have hinv : ∀ k ∈ K, ∀ v, (μ ∘ₗ fixedProj ρ hρ hKc hKo) (ρ k v) =
      (μ ∘ₗ fixedProj ρ hρ hKc hKo) v := fun k hk v => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, fixedProj_apply_act hρ hKc hKo hk]
  ⟨⟨μ ∘ₗ fixedProj ρ hρ hKc hKo,
    mem_smoothVectors_of_mem_fixedVectors hKo (mem_fixedVectors_dual.2 hinv)⟩,
    mem_fixedVectors_contragredient.2 hinv⟩

variable (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
include hρ hKc hKo

theorem restrictFixed_bijective : Function.Bijective (restrictFixed ρ K) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hx' : ((x : smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) = 0 :=
      eq_of_invariant_of_eqOn hρ hKc hKo (mem_fixedVectors_contragredient.1 x.2)
        (fun _ _ _ => rfl) fun v hv => LinearMap.congr_fun hx ⟨v, hv⟩
    exact Subtype.ext (Subtype.ext hx')
  · intro μ
    refine ⟨extendFixed hρ hKc hKo μ, LinearMap.ext fun v => ?_⟩
    change μ (fixedProj ρ hρ hKc hKo v) = μ v
    rw [Subtype.ext (fixedProj_apply_of_mem hρ hKc hKo v.2)]

def fixedContragredientEquiv :
    fixedVectors (contragredient ρ) K ≃ₗ[ℂ] Module.Dual ℂ (fixedVectors ρ K) :=
  LinearEquiv.ofBijective (restrictFixed ρ K) (restrictFixed_bijective hρ hKc hKo)

theorem fixedContragredientEquiv_apply (x : fixedVectors (contragredient ρ) K) :
    fixedContragredientEquiv hρ hKc hKo x = restrictFixed ρ K x := rfl

end LocallyProfinite

section Admissible

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

theorem isAdmissible_contragredient (h : IsAdmissible ρ) : IsAdmissible (contragredient ρ) := by
  refine ⟨isSmooth_contragredient ρ, fun K hKc hKo => ?_⟩
  have := h.2 K hKc hKo
  exact LinearEquiv.finiteDimensional (fixedContragredientEquiv h.1 hKc hKo).symm

theorem toDoubleContragredient_bijective (h : IsAdmissible ρ) :
    Function.Bijective (toDoubleContragredient h.1) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro v hv
    obtain ⟨K, hKc, hKo, hvK⟩ := (isSmooth_iff_forall_exists ρ).1 h.1 v
    set e := fixedContragredientEquiv h.1 hKc hKo
    have hzero : (⟨v, hvK⟩ : fixedVectors ρ K) = 0 := by
      refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun μ => ?_
      have h1 : (((e.symm μ : fixedVectors (contragredient ρ) K) :
          smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) v = 0 := by
        have := congrArg (fun Φ : smoothVectors (Representation.dual (contragredient ρ)) =>
          (Φ : Module.Dual ℂ (smoothVectors (Representation.dual ρ)))
            (e.symm μ : fixedVectors (contragredient ρ) K)) hv
        exact this
      have h2 : e (e.symm μ) = μ := e.apply_symm_apply μ
      rw [← h2, fixedContragredientEquiv_apply, restrictFixed_apply]
      exact h1
    simpa using congrArg Subtype.val hzero
  · intro Φ
    obtain ⟨K, hKc, hKo, hΦK⟩ := (mem_smoothVectors_iff _).1 Φ.2
    set e := fixedContragredientEquiv h.1 hKc hKo
    have := h.2 K hKc hKo
    let ψ : Module.Dual ℂ (Module.Dual ℂ (fixedVectors ρ K)) :=
      (Φ : Module.Dual ℂ (smoothVectors (Representation.dual ρ))) ∘ₗ
        (fixedVectors (contragredient ρ) K).subtype ∘ₗ e.symm.toLinearMap
    set w := (Module.evalEquiv ℂ (fixedVectors ρ K)).symm ψ
    have hw : ∀ μ : Module.Dual ℂ (fixedVectors ρ K), μ w = ψ μ := fun μ =>
      LinearMap.congr_fun ((Module.evalEquiv ℂ (fixedVectors ρ K)).apply_symm_apply ψ) μ
    refine ⟨(w : V), Subtype.ext ?_⟩
    refine eq_of_invariant_of_eqOn (isSmooth_contragredient ρ) hKc hKo (fun k hk x => ?_)
      (mem_fixedVectors_dual.1 hΦK) fun x hx => ?_
    · change (x : Module.Dual ℂ V) (ρ k⁻¹ w) = (x : Module.Dual ℂ V) w
      rw [w.2 _ (inv_mem hk)]
    · have h1 : (Φ : Module.Dual ℂ (smoothVectors (Representation.dual ρ))) x =
          ψ (e ⟨x, hx⟩) := by
        simp [ψ]
      rw [h1, ← hw]
      rfl

end Admissible

end GroundTheory.Automorphic
end
end

section

noncomputable section

namespace GroundTheory.Automorphic

open Set Filter Topology Pointwise

section RightTranslation

variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]

def rightTranslation : Representation ℂ G (G → W) where
  toFun g := LinearMap.funLeft ℂ W (· * g)
  map_one' := by
    ext f x
    simp [LinearMap.funLeft_apply]
  map_mul' g h := by
    ext f x
    simp [LinearMap.funLeft_apply, Module.End.mul_apply, mul_assoc]

@[simp]
theorem rightTranslation_apply (g : G) (f : G → W) (x : G) :
    rightTranslation g f x = f (x * g) := rfl

end RightTranslation

section Induced

variable {G : Type*} [Group G] [TopologicalSpace G] (H : Subgroup G)
  {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ H W)

def indSpace : Submodule ℂ (G → W) where
  carrier := {f | (∀ h : H, ∀ g : G, f ((h : G) * g) = σ h (f g)) ∧
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ k ∈ K, ∀ g : G, f (g * k) = f g}
  add_mem' := by
    rintro f₁ f₂ ⟨h₁, K₁, hK₁, hf₁⟩ ⟨h₂, K₂, hK₂, hf₂⟩
    refine ⟨fun h g => by simp [h₁ h g, h₂ h g], K₁ ⊓ K₂, ?_, fun k hk g => ?_⟩
    · rw [Subgroup.coe_inf]
      exact hK₁.inter hK₂
    · simp [hf₁ k (Subgroup.mem_inf.1 hk).1 g, hf₂ k (Subgroup.mem_inf.1 hk).2 g]
  zero_mem' := ⟨fun h g => by simp, ⊤, by simp, fun k _ g => rfl⟩
  smul_mem' := by
    rintro c f ⟨h₁, K, hK, hf⟩
    exact ⟨fun h g => by simp [h₁ h g], K, hK, fun k hk g => by simp [hf k hk g]⟩

variable {H σ} in
theorem mem_indSpace {f : G → W} :
    f ∈ indSpace H σ ↔ (∀ h : H, ∀ g : G, f ((h : G) * g) = σ h (f g)) ∧
      ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ k ∈ K, ∀ g : G, f (g * k) = f g :=
  Iff.rfl


variable [IsTopologicalGroup G]


variable {H σ} in
theorem rightTranslation_mem_indSpace {f : G → W} (hf : f ∈ indSpace H σ) (g : G) :
    rightTranslation g f ∈ indSpace H σ := by
  obtain ⟨h₁, K, hK, hfK⟩ := hf
  refine ⟨fun h x => ?_, K.comap (MulAut.conj g⁻¹).toMonoidHom, ?_, fun k hk x => ?_⟩
  · show f ((h : G) * x * g) = σ h (f (x * g))
    rw [mul_assoc, h₁]
  · rw [Subgroup.coe_comap]
    have : ⇑(MulAut.conj g⁻¹).toMonoidHom = fun x : G => g⁻¹ * x * g⁻¹⁻¹ := by
      ext x
      simp
    rw [this]
    exact hK.preimage (by fun_prop)
  · have := hfK _ hk (x * g)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at this
    simp only [rightTranslation_apply]
    rw [← this]
    congr 1
    group


def indRep : Representation ℂ G (indSpace H σ) :=
  (rightTranslation (W := W)).subrepresentation (indSpace H σ) fun g f hf =>
    rightTranslation_mem_indSpace (H := H) (σ := σ) (f := f) hf g

@[simp]
theorem coe_indRep_apply (g : G) (f : indSpace H σ) (x : G) :
    (indRep H σ g f : G → W) x = (f : G → W) (x * g) := rfl

theorem isSmooth_indRep : IsSmooth (indRep H σ) := by
  intro f
  obtain ⟨-, K, hK, hfK⟩ := f.2
  refine Subgroup.isOpen_mono (fun k hk => ?_) hK
  rw [mem_stabilizerOf]
  exact Subtype.ext (funext fun x => hfK k hk x)

section Frobenius

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)

def evalOne : indSpace H σ →ₗ[ℂ] W :=
  LinearMap.proj (R := ℂ) (φ := fun _ : G => W) 1 ∘ₗ (indSpace H σ).subtype

omit [IsTopologicalGroup G] in
@[simp]
theorem evalOne_apply (f : indSpace H σ) : evalOne H σ f = (f : G → W) 1 := rfl

theorem evalOne_indRep (h : H) (f : indSpace H σ) :
    evalOne H σ (indRep H σ h f) = σ h (evalOne H σ f) := by
  simpa using f.2.1 h 1

def frobeniusFun (Φ : Representation.IntertwiningMap π (indRep H σ)) :
    Representation.IntertwiningMap (π.comp H.subtype) σ where
  toLinearMap := evalOne H σ ∘ₗ Φ.toLinearMap
  isIntertwining' h := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, MonoidHom.coe_comp,
      Subgroup.coe_subtype, Representation.IntertwiningMap.toLinearMap_apply]
    rw [Representation.IntertwiningMap.isIntertwining _ _ Φ, evalOne_indRep]

variable {π}

def frobeniusInv (hπ : IsSmooth π) (φ : Representation.IntertwiningMap (π.comp H.subtype) σ) :
    Representation.IntertwiningMap π (indRep H σ) where
  toFun v := ⟨fun g => φ (π g v), fun h g => by
      simp only [map_mul, Module.End.mul_apply]
      exact Representation.IntertwiningMap.isIntertwining _ _ φ h (π g v),
    stabilizerOf π v, hπ v, fun k hk g => by
      simp [map_mul, Module.End.mul_apply, mem_stabilizerOf.1 hk]⟩
  map_add' v w := Subtype.ext (funext fun g => by simp)
  map_smul' c v := Subtype.ext (funext fun g => by simp)
  isIntertwining' g := LinearMap.ext fun v => Subtype.ext (funext fun x => by
    simp [map_mul, Module.End.mul_apply])

@[simp]
theorem frobeniusInv_apply (hπ : IsSmooth π)
    (φ : Representation.IntertwiningMap (π.comp H.subtype) σ) (v : V) (g : G) :
    (frobeniusInv H σ hπ φ v : G → W) g = φ (π g v) := rfl

def frobenius (hπ : IsSmooth π) :
    Representation.IntertwiningMap π (indRep H σ) ≃ₗ[ℂ]
      Representation.IntertwiningMap (π.comp H.subtype) σ where
  toFun := frobeniusFun H σ π
  map_add' Φ Ψ := Representation.IntertwiningMap.ext (LinearMap.ext fun v => by
    simp [frobeniusFun])
  map_smul' c Φ := Representation.IntertwiningMap.ext (LinearMap.ext fun v => by
    simp [frobeniusFun])
  invFun := frobeniusInv H σ hπ
  left_inv Φ := Representation.IntertwiningMap.ext (LinearMap.ext fun v =>
    Subtype.ext (funext fun x => by
      simp only [Representation.IntertwiningMap.toLinearMap_apply, frobeniusInv_apply]
      show (evalOne H σ) (Φ (π x v)) = _
      rw [Representation.IntertwiningMap.isIntertwining _ _ Φ, evalOne_apply, coe_indRep_apply, one_mul]))
  right_inv φ := Representation.IntertwiningMap.ext (LinearMap.ext fun v => by
    show (evalOne H σ) (frobeniusInv H σ hπ φ v) = φ v
    simp)

end Frobenius

end Induced

end GroundTheory.Automorphic
end
end

section

namespace GroundTheory.Automorphic

open Matrix Polynomial
open scoped MatrixOrder ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

theorem exists_KAK (g : GL n 𝕜) :
    ∃ k₁ k₂ : unitaryGroup n 𝕜, ∃ a : n → ℝ, (∀ i, 0 < a i) ∧
      (g : Matrix n n 𝕜) = (k₁ : Matrix n n 𝕜) * diagonal (fun i => (a i : 𝕜)) * k₂ := by
  have hp : (polarPos g).PosDef := polarPos_posDef g
  have hH : (polarPos g).IsHermitian := hp.isHermitian
  refine ⟨⟨polarUnitary g, polarUnitary_mem g⟩ * hH.eigenvectorUnitary, star hH.eigenvectorUnitary,
    hH.eigenvalues, hp.eigenvalues_pos, ?_⟩
  have hs := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  calc (g : Matrix n n 𝕜) = polarUnitary g * polarPos g := (polarUnitary_mul_polarPos g).symm
    _ = polarUnitary g * ((hH.eigenvectorUnitary : Matrix n n 𝕜) *
          diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star (hH.eigenvectorUnitary : Matrix n n 𝕜)) := by
        rw [← hs]
    _ = _ := by simp [Matrix.mul_assoc, Function.comp_def]

end GroundTheory.Automorphic
end

section

noncomputable section

namespace GroundTheory.Automorphic

open Set Filter Topology MeasureTheory
open scoped Pointwise ENNReal

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [IsFiniteMeasureOnCompacts μ]

theorem integral_eq_smul_finsum_coset (K : OpenSubgroup G) (hKc : IsCompact (K : Set G))
    {f : G → E} (hf : HasCompactSupport f) (hK : ∀ g, ∀ k ∈ K, f (g * k) = f g) :
    ∫ g, f g ∂μ = μ.real (K : Set G) • ∑ᶠ x : G ⧸ (K : Subgroup G), f x.out := by
  set S := (finite_image_mk_tsupport K hf).toFinset with hS
  have hmeas : ∀ g : G, MeasurableSet (g • (K : Set G)) := fun g =>
    (K.isOpen.smul g).measurableSet
  have hfin : ∀ g : G, μ (g • (K : Set G)) ≠ ∞ := fun g =>
    (hKc.smul g).measure_lt_top.ne
  have hvol : ∀ g : G, μ.real (g • (K : Set G)) = μ.real (K : Set G) := fun g => by
    simp [Measure.real, measure_smul]
  have hdec := eq_sum_indicator_coset K hf hK
  rw [finsum_eq_sum_of_support_subset (s := S)]
  · calc ∫ g, f g ∂μ
        = ∫ g, ∑ x ∈ S, (x.out • (K : Set G)).indicator (fun _ => f x.out) g ∂μ :=
          integral_congr_ae (Eventually.of_forall fun g => by
            rw [congrFun hdec g, Finset.sum_apply])
      _ = ∑ x ∈ S, ∫ g, (x.out • (K : Set G)).indicator (fun _ => f x.out) g ∂μ :=
          integral_finsetSum _ fun x _ =>
            (integrable_indicator_iff (hmeas _)).2 (integrableOn_const (hfin _))
      _ = μ.real (K : Set G) • ∑ x ∈ S, f x.out := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [integral_indicator_const _ (hmeas _), hvol]
  · intro x hx
    rw [hS, Set.Finite.coe_toFinset]
    exact ⟨x.out, subset_tsupport f hx, QuotientGroup.out_eq' x⟩

end Integral

end GroundTheory.Automorphic
end
end
