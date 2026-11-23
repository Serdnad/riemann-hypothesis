module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import GroundTheory.AutomorphicForms.Iwasawa
public import GroundTheory.AutomorphicForms.InductionParabolicGroups
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle205
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormConsMul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle200
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle201
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle202
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle203
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Std.Tactic.BVDecide.Normalize.Prop
public import GroundTheory.AutomorphicForms.FiniteBruhat
public import GroundTheory.AutomorphicForms.GeometricLemmaJacquetCell
public import GroundTheory.AutomorphicForms.GeometricLemmaModular
public import GroundTheory.AutomorphicForms.GeometricLemmaNormal
import GroundTheory.AutomorphicForms.Bundle002
import Mathlib.Tactic.TypeStar

@[expose] public section

section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.ParabBridge

theorem parab_eq_blockUpper : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → parab k e = blockUpper k N β := by
  intro k _ _ _ _ α _ _ N m _ _ e β h
  ext g
  rw [mem_parab, GroundTheory.Automorphic.Iwasawa.mem_blockUpper]
  exact forall₂_congr fun i j => by rw [h j i]

end GlobalTheory.CompanionTheory.ParabBridge
end

section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical leviPar normLeviParSqrtModular)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.RelUnipBridge

theorem one_apply_sigma {k n α : Type} [Zero k] [One k] [DecidableEq n] {m : α → Type}
    [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ n) (a : α) (r s : m a) :
    (1 : Matrix n n k) (e ⟨a, r⟩) (e ⟨a, s⟩) = (1 : Matrix (m a) (m a) k) r s := by
  by_cases h : r = s
  · subst h; simp
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne]
    intro h'
    have := e.injective h'
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at this
    exact h this

theorem mem_relUnip_iff_leviEmb_mem : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {c : α → β' → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (e : (Σ i, m i) ≃ Fin N) (f : ∀ i, (Σ j, c i j) ≃ m i) (δ : Fin N → ℕ) (hδ : ∀ i j j' (t : c i j) (t' : c i j'), δ (e ⟨i, f i ⟨j, t⟩⟩) < δ (e ⟨i, f i ⟨j', t'⟩⟩) ↔ j < j') (x : Levi k m), x ∈ relUnip k f ↔ leviEmb k e x ∈ unipotentRadical k N δ := by
  intro k _ _ _ _ α β' _ _ _ _ N m _ _ c _ _ e f δ hδ x
  rw [GroundTheory.Automorphic.Parabolic.mem_unipotentRadical]
  constructor
  · intro hx
    have hx' : ∀ a, x a ∈ unipRad k (f a) := fun a => hx a trivial
    refine ⟨fun r s hrs => ?_, fun r s hrs => ?_⟩
    · obtain ⟨⟨a, r⟩, rfl⟩ := e.surjective r
      obtain ⟨⟨b, s⟩, rfl⟩ := e.surjective s
      by_cases hab : a = b
      · subst hab
        rw [leviEmb_apply_same]
        obtain ⟨⟨j, t⟩, rfl⟩ := (f a).surjective r
        obtain ⟨⟨j', t'⟩, rfl⟩ := (f a).surjective s
        exact mem_parab_iff.1 (mem_unipRad.1 (hx' a)).1 j j' t t' ((hδ a j' j t' t).1 hrs)
      · exact leviEmb_apply_ne k e x hab r s
    · obtain ⟨⟨a, r⟩, rfl⟩ := e.surjective r
      obtain ⟨⟨b, s⟩, rfl⟩ := e.surjective s
      by_cases hab : a = b
      · subst hab
        rw [leviEmb_apply_same, one_apply_sigma]
        obtain ⟨⟨j, t⟩, rfl⟩ := (f a).surjective r
        obtain ⟨⟨j', t'⟩, rfl⟩ := (f a).surjective s
        have hjj : j = j' := by
          rcases lt_trichotomy j j' with h | h | h
          · exact absurd ((hδ a j j' t t').2 h) hrs.not_lt
          · exact h
          · exact absurd ((hδ a j' j t' t).2 h) hrs.symm.not_lt
        subst hjj
        rw [one_apply_sigma]
        exact (mem_unipRad.1 (hx' a)).2 j t t'
      · rw [leviEmb_apply_ne k e x hab r s, Matrix.one_apply_ne]
        intro h
        exact hab (congrArg Sigma.fst (e.injective h))
  · rintro ⟨hP, h1⟩ a -
    refine mem_unipRad.2 ⟨mem_parab_iff.2 fun j j' t t' hjj => ?_, fun j t t' => ?_⟩
    · have := hP ((hδ a j' j t' t).2 hjj)
      rwa [leviEmb_apply_same] at this
    · have hd : δ (e ⟨a, f a ⟨j, t⟩⟩) = δ (e ⟨a, f a ⟨j, t'⟩⟩) := by
        rcases lt_trichotomy (δ (e ⟨a, f a ⟨j, t⟩⟩)) (δ (e ⟨a, f a ⟨j, t'⟩⟩)) with h | h | h
        · exact absurd ((hδ a j j t t').1 h) (lt_irrefl j)
        · exact h
        · exact absurd ((hδ a j j t' t).1 h) (lt_irrefl j)
      have := h1 _ _ hd
      rwa [leviEmb_apply_same, one_apply_sigma, one_apply_sigma] at this

end GlobalTheory.CompanionTheory.RelUnipBridge
end

section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical leviPar normLeviParSqrtModular)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.CellCompare

theorem mem_relParab_iff_leviEmb_mem_blockUpper :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {N : ℕ}
      {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {c : α → β' → Type}
      [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (e : (Σ i, m i) ≃ Fin N)
      (f : ∀ i, (Σ j, c i j) ≃ m i) (δ : Fin N → ℕ)
      (hδ : ∀ i j j' (t : c i j) (t' : c i j'),
        δ (e ⟨i, f i ⟨j, t⟩⟩) < δ (e ⟨i, f i ⟨j', t'⟩⟩) ↔ j < j') (x : Levi k m),
      x ∈ relParab k f ↔ leviEmb k e x ∈ blockUpper k N δ := by
  intro k _ _ _ _ α β' _ _ _ _ N m _ _ c _ _ e f δ hδ x
  unfold relParab
  rw [Subgroup.mem_pi]
  change _ ↔ (leviEmb k e x : Matrix (Fin N) (Fin N) k).BlockTriangular δ
  constructor
  · intro hx p q hpq
    obtain ⟨⟨a, u⟩, rfl⟩ := e.surjective p
    obtain ⟨⟨b, v⟩, rfl⟩ := e.surjective q
    by_cases hab : a = b
    · subst hab
      obtain ⟨⟨j, t⟩, rfl⟩ := (f a).surjective u
      obtain ⟨⟨j', t'⟩, rfl⟩ := (f a).surjective v
      rw [leviEmb_apply_same]
      exact mem_parab_iff.1 (hx a trivial) j j' t t' ((hδ a j' j t' t).1 hpq)
    · exact leviEmb_apply_ne k e x hab u v
  · intro hx i _
    rw [mem_parab_iff]
    intro j j' t t' hjj
    have h := hx ((hδ i j' j t' t).2 hjj)
    rwa [leviEmb_apply_same] at h

end GlobalTheory.CompanionTheory.CellCompare
end

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

variable {n : ℕ}

def lmulCLM (a : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => a * y
      map_add' := mul_add a
      map_smul' := fun r y => by simp }

theorem lmulCLM_apply (a y : Mat n) : lmulCLM a y = a * y := rfl

theorem inv_mul_mem_GLs {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x⁻¹ * y ∈ GLs n := by
  have hxu : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  have h1 : IsUnit (x⁻¹).det := Matrix.isUnit_nonsing_inv_det x hxu
  show (x⁻¹ * y).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero h1.ne_zero hy

theorem lg_left_facts : LgFacts → ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ GLs n,
    ContDiffOn ℝ ∞ (fun y : Mat n => lg (x⁻¹ * y)) (GLs n) ∧
    (∀ R : ℝ, IsCompact {y : G n | lg (x⁻¹ * y.val) ≤ R}) ∧
    ∀ y ∈ GLs n, ∀ p : Ix n, |fderiv ℝ (fun y : Mat n => lg (x⁻¹ * y)) y (y * hm p)| ≤ C := by
  intro hL n
  obtain ⟨-, -, -, hsm, hcpt, -, C₀, hC₀⟩ := hL n
  refine ⟨2 * |C₀|, by positivity, fun x hx => ?_⟩
  have hxu : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  have hsm' : ContDiffOn ℝ ∞ (fun y : Mat n => lg (x⁻¹ * y)) (GLs n) :=
    hsm.comp (lmulCLM x⁻¹).contDiff.contDiffOn (fun y hy => inv_mul_mem_GLs hx hy)
  refine ⟨hsm', fun R => ?_, fun y hy p => ?_⟩
  · have hxU : IsUnit x := (Matrix.isUnit_iff_isUnit_det x).2 hxu
    let X : G n := hxU.unit
    have hXv : (X : Mat n) = x := rfl
    have hXi : ((X⁻¹ : G n) : Mat n) = x⁻¹ := by
      rw [Matrix.coe_units_inv, hXv]
    have hset : {y : G n | lg (x⁻¹ * y.val) ≤ R} = (fun z : G n => X * z) '' {z : G n | lg z.val ≤ R} := by
      ext y
      constructor
      · intro hy
        refine ⟨X⁻¹ * y, ?_, by simp⟩
        show lg ((X⁻¹ * y : G n) : Mat n) ≤ R
        rw [Units.val_mul, hXi]
        exact hy
      · rintro ⟨z, hz, rfl⟩
        show lg (x⁻¹ * ((X * z : G n) : Mat n)) ≤ R
        rw [Units.val_mul, ← hXi, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
        exact hz
    rw [hset]
    exact (hcpt R).image (continuous_const.mul continuous_id)
  · have hw : x⁻¹ * y ∈ GLs n := inv_mul_mem_GLs hx hy
    have hdiff : DifferentiableAt ℝ lg (x⁻¹ * y) :=
      (hsm.contDiffAt (isOpen_GLs.mem_nhds hw)).differentiableAt (by simp)
    have hder : fderiv ℝ (fun y : Mat n => lg (x⁻¹ * y)) y
        = (fderiv ℝ lg (x⁻¹ * y)).comp (lmulCLM x⁻¹) :=
      ((hdiff.hasFDerivAt).comp y (lmulCLM x⁻¹).hasFDerivAt).fderiv
    have hCle : C₀ ≤ |C₀| := le_abs_self C₀
    rw [hder, ContinuousLinearMap.comp_apply, lmulCLM_apply, ← mul_assoc]
    obtain ⟨b, i, j⟩ := p
    have h1 := abs_le.1 (hC₀ _ hw (b, i, j))
    have h2 := abs_le.1 (hC₀ _ hw (b, j, i))
    cases b
    · have e : hm ((false, i, j) : Ix n) = bs (false, i, j) - bs (false, j, i) := by
        simp [hm, bs]
      rw [e, mul_sub, map_sub, abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · have e : hm ((true, i, j) : Ix n) = bs (true, i, j) + bs (true, j, i) := by
        simp [hm, bs]
      rw [e, mul_add, map_add (f := _), abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end GlobalTheory.CompanionTheory.WaveSpd
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT CrystallineSemistableComparison.Onto

noncomputable section

namespace GlobalTheory.CompanionTheory.RelKill

section Fam
variable {K : Type} [CommRing K] {ι : Type} {a : ℕ}

theorem lam_family (hDW : DWedge) (hDL : DLog) (hFL : FormLaws) (A : Finset ι → Type) [∀ S, CommRing (A S)] [∀ S, Algebra K (A S)]
    {H₂ X₂ H₃ X₃ : Finset ι → Type*} [∀ S, AddCommGroup (H₂ S)] [∀ S, Module K (H₂ S)]
    [∀ S, AddCommGroup (X₂ S)] [∀ S, Module K (X₂ S)] [∀ S, AddCommGroup (H₃ S)] [∀ S, Module K (H₃ S)]
    [∀ S, AddCommGroup (X₃ S)] [∀ S, Module K (X₃ S)]
    (i₂ : ∀ S, H₂ S →ₗ[K] X₂ S) (i₃ : ∀ S, H₃ S →ₗ[K] X₃ S)
    (e₂ : ∀ S, S.Nonempty → (Om K (A S) a →ₗ[K] X₂ S)) (e₃ : ∀ S, S.Nonempty → (Om K (A S) (a + 1) →ₗ[K] X₃ S))
    (he₂ : ∀ S hS, Function.Bijective (e₂ S hS)) (hi₃ : ∀ S, S.Nonempty → Function.Injective (i₃ S))
    (I : ∀ S, Ideal (A S))
    (hr₂ : ∀ S hS ω, e₂ S hS ω ∈ LinearMap.range (i₂ S) ↔ ω ∈ relOm K (I S) a)
    (hr₃ : ∀ S hS ω, e₃ S hS ω ∈ LinearMap.range (i₃ S) ↔ ω ∈ relOm K (I S) (a + 1))
    (f : ∀ (α : ι) (S : Finset ι), α ∈ S → A S) (hI : ∀ α S hα, I S = Ideal.span {f α S hα})
    (hnz : ∀ α S hα (ω : Om K (A S) (a + 1)), f α S hα • ω = 0 → ω = 0) (c : ℤ)
    (φ : ∀ {S T : Finset ι}, S ⊆ T → (A S →ₐ[K] A T))
    (hφ : ∀ α {S T : Finset ι} (h : S ⊆ T) hα, φ h (f α S hα) = f α T (h hα))
    (ρ₂ : ∀ {S T : Finset ι}, S ⊆ T → (H₂ S →ₗ[K] H₂ T)) (ρ₃ : ∀ {S T : Finset ι}, S ⊆ T → (H₃ S →ₗ[K] H₃ T))
    (x₂ : ∀ {S T : Finset ι}, S ⊆ T → (X₂ S →ₗ[K] X₂ T)) (x₃ : ∀ {S T : Finset ι}, S ⊆ T → (X₃ S →ₗ[K] X₃ T))
    (hρ₂ : ∀ {S T : Finset ι} (h : S ⊆ T) y, i₂ T (ρ₂ h y) = x₂ h (i₂ S y))
    (hρ₃ : ∀ {S T : Finset ι} (h : S ⊆ T) y, i₃ T (ρ₃ h y) = x₃ h (i₃ S y))
    (hx₂ : ∀ {S T : Finset ι} (h : S ⊆ T) hS hT ω, x₂ h (e₂ S hS ω) = e₂ T hT (omMap (φ h) a ω))
    (hx₃ : ∀ {S T : Finset ι} (h : S ⊆ T) hS hT ω, x₃ h (e₃ S hS ω) = e₃ T hT (omMap (φ h) (a + 1) ω)) :
    ∃ lam : ∀ (α : ι) (S : Finset ι), α ∈ S → (H₂ S →ₗ[K] H₃ S),
      (∀ α {S T : Finset ι} (h : S ⊆ T) hS y, lam α T (h hS) (ρ₂ h y) = ρ₃ h (lam α S hS y)) ∧
      ∀ α S hα y ω η (w : Om K (A S) a →ₗ[A S] Om K (A S) (a + 1)),
        (∀ g₀ (g : Fin a → A S), w (form K g₀ g) = form K g₀ (Fin.cons (f α S hα) g)) →
        i₂ S y = e₂ S ⟨α, hα⟩ ω → f α S hα • η = w ω → i₃ S (lam α S hα y) = e₃ S ⟨α, hα⟩ (c • η) := by
  have key := fun (α : ι) (S : Finset ι) (hα : α ∈ S) =>
    lam_one hDW hDL hFL (i₂ S) (i₃ S) (e₂ S ⟨α, hα⟩) (e₃ S ⟨α, hα⟩) (he₂ S _) (hi₃ S ⟨α, hα⟩) (I S) (hr₂ S _)
      (hr₃ S _) (f α S hα) (hI α S hα) (hnz α S hα) c
  choose lam hlam using key
  refine ⟨lam, fun α S T h hα y => ?_, hlam⟩
  have hS : S.Nonempty := ⟨α, hα⟩
  have hT : T.Nonempty := ⟨α, h hα⟩
  refine hi₃ T hT ?_
  obtain ⟨ω, hω⟩ := (he₂ S hS).2 (i₂ S y)
  have hm : ω ∈ relOm K (Ideal.span {f α S hα}) a := by
    rw [← hI α S hα]
    exact (hr₂ S hS ω).1 ⟨y, hω.symm⟩
  obtain ⟨w, hw⟩ := hDW K (A S) a (f α S hα)
  obtain ⟨η, ⟨-, hη⟩, -⟩ := hDL K (A S) a (f α S hα) (hnz α S hα) w hw ω hm
  obtain ⟨w', hw'⟩ := hDW K (A T) a (f α T (h hα))
  have wm := wedge_map hFL (φ h) (f α S hα) w w' hw (by rw [hφ]; exact hw') ω
  have s1 := hlam α S hα y ω η w hw hω.symm hη
  have s2 := hlam α T (h hα) (ρ₂ h y) (omMap (φ h) a ω) (omMap (φ h) (a + 1) η) w' hw'
    (by rw [hρ₂, ← hω, hx₂ h hS hT]) (by
      rw [← wm, ← hη, ((hFL K (A S) (A T) (a + 1)).2 (φ h)).2.1, hφ])
  rw [s2, hρ₃, s1, hx₃ h hS hT, map_zsmul (omMap (φ h) (a + 1))]

end Fam

section Kill
variable {K : Type} [CommRing K] {C : Type 1} [Category.{0} C]
  {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} K} {ι : Type} [DecidableEq ι]

theorem cov_kill (hCK : ConeKill) (hCD : CovDesc) (hDW : DWedge) (hDL : DLog) (hFL : FormLaws)
    (P : CH.Pairing F₁ F₂ F₃) (U : ι → ObjectProperty C)
    (hU : ∀ α, Cosieve (U α)) {Q : ObjectProperty C} (hQ : Cosieve Q) (a : ℕ)
    (h1 : (covSy F₂ U hQ).One a) (h2 : (covSy F₃ U hQ).One (a + 1))
    (r : CH.Cn F₁ 2) (hr : CH.d F₁ 2 r = 0) (β : ∀ α, CH.Cn ((U α).ι ⋙ F₁) 1)
    (hβ : ∀ α, CH.d _ 1 (β α) = (CH.Mor.restrict F₁ (U α).ι).pullC 2 r)
    (A : Finset ι → Type) [∀ S, CommRing (A S)] [∀ S, Algebra K (A S)]
    (e₂ : ∀ S, S.Nonempty → (Om K (A S) a →ₗ[K] HU F₂ (capU U S) a))
    (e₃ : ∀ S, S.Nonempty → (Om K (A S) (a + 1) →ₗ[K] HU F₃ (capU U S) (a + 1)))
    (he₂ : ∀ S hS, Function.Bijective (e₂ S hS))
    (hi₃ : ∀ S, S.Nonempty → Function.Injective ((incl F₃ (capU U S) hQ).mapH (a + 1)))
    (I : ∀ S, Ideal (A S))
    (hr₂ : ∀ S hS ω, e₂ S hS ω ∈ LinearMap.range ((incl F₂ (capU U S) hQ).mapH a) ↔ ω ∈ relOm K (I S) a)
    (hr₃ : ∀ S hS ω, e₃ S hS ω ∈ LinearMap.range ((incl F₃ (capU U S) hQ).mapH (a + 1)) ↔ ω ∈ relOm K (I S) (a + 1))
    (f : ∀ (α : ι) (S : Finset ι), α ∈ S → A S) (hI : ∀ α S hα, I S = Ideal.span {f α S hα})
    (hnz : ∀ α S hα (ω : Om K (A S) (a + 1)), f α S hα • ω = 0 → ω = 0) (c : ℤ)
    (φ : ∀ {S T : Finset ι}, S ⊆ T → (A S →ₐ[K] A T))
    (hφ : ∀ α {S T : Finset ι} (h : S ⊆ T) hα, φ h (f α S hα) = f α T (h hα))
    (k : ∀ {S T : Finset ι}, S ⊆ T → capU U T ≤ capU U S)
    (hx₂ : ∀ {S T : Finset ι} (h : S ⊆ T) hS hT ω,
      (resU F₂ (k h)).pull a (e₂ S hS ω) = e₂ T hT (omMap (φ h) a ω))
    (hx₃ : ∀ {S T : Finset ι} (h : S ⊆ T) hS hT ω,
      (resU F₃ (k h)).pull (a + 1) (e₃ S hS ω) = e₃ T hT (omMap (φ h) (a + 1) ω))
    (u : ∀ (α α' : ι) (S : Finset ι), α ∈ S → α' ∈ S → (A S)ˣ)
    (huf : ∀ α α' S hα hα', f α S hα = u α α' S hα hα' * f α' S hα')
    (hcup : ∀ α α' S hα hα' (y : CH.Cn ((capU U S).ι ⋙ F₂) a) (hy : CH.d _ a y = 0) (ω : Om K (A S) a)
      (w : Om K (A S) a →ₗ[A S] Om K (A S) (a + 1)),
      (∀ g₀ (g : Fin a → A S), w (form K g₀ g) = form K g₀ (Fin.cons (u α α' S hα hα' : A S) g)) →
      (CH.cx _).cls y hy = e₂ S ⟨α, hα⟩ ω → ∀ hz,
      (CH.cx ((capU U S).ι ⋙ F₃)).cls ((pairU P (capU U S)).cupC (Nat.add_comm 1 a)
        ((resU F₁ (capU_le U S hα)).pullC 1 (β α) - (resU F₁ (capU_le U S hα')).pullC 1 (β α')) y) hz =
        e₃ S ⟨α, hα⟩ (c • ((↑(u α α' S hα hα')⁻¹ : A S) • w ω)))
    (n : ℕ) (x : ((covSy F₂ U hQ).K ∅).X n) (hx : ((covSy F₂ U hQ).K ∅).d n x = 0) :
    rhoS P U hQ r ∅ n x ∈ ((covSy F₃ U hQ).K ∅).B (n + 2) := by
  obtain ⟨lam, lam_nat, lam_spec⟩ := lam_family (K := K) (a := a) hDW hDL hFL A
    (H₂ := fun S => ((covSy F₂ U hQ).K S).H a) (X₂ := fun S => HU F₂ (capU U S) a)
    (H₃ := fun S => ((covSy F₃ U hQ).K S).H (a + 1)) (X₃ := fun S => HU F₃ (capU U S) (a + 1))
    (fun S => (incl F₂ (capU U S) hQ).mapH a) (fun S => (incl F₃ (capU U S) hQ).mapH (a + 1))
    e₂ e₃ he₂ hi₃ I hr₂ hr₃ f hI hnz c φ hφ
    (fun h => ((covSy F₂ U hQ).res h).mapH a) (fun h => ((covSy F₃ U hQ).res h).mapH (a + 1))
    (fun h => (resU F₂ (k h)).pull a) (fun h => (resU F₃ (k h)).pull (a + 1))
    (fun h y => by
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rfl)
    (fun h y => by
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rfl)
    hx₂ hx₃
  refine cone_apply hCK hCD P U hU hQ a h1 h2 r hr β hβ lam (fun α S T h hS x => lam_nat α h hS x) ?_ n x hx
  intro α α' S hα hα' x hx hz
  have hS : S.Nonempty := ⟨α, hα⟩
  refine hi₃ S hS ?_
  have hy : CH.d _ a x.1 = 0 := congrArg Subtype.val hx
  obtain ⟨ω, hω⟩ := (he₂ S hS).2 ((CH.cx _).cls x.1 hy)
  have hi : (incl F₂ (capU U S) hQ).mapH a (((covSy F₂ U hQ).K S).cls x hx) = e₂ S hS ω := hω.symm
  have hm : ω ∈ relOm K (I S) a := (hr₂ S hS ω).1 ⟨_, hi⟩
  have hm₁ : ω ∈ relOm K (Ideal.span {f α S hα}) a := hI α S hα ▸ hm
  have hm₂ : ω ∈ relOm K (Ideal.span {f α' S hα'}) a := hI α' S hα' ▸ hm
  obtain ⟨w, hw⟩ := hDW K (A S) a (f α S hα)
  obtain ⟨w', hw'⟩ := hDW K (A S) a (f α' S hα')
  obtain ⟨wu, hwu⟩ := hDW K (A S) a (u α α' S hα hα' : A S)
  obtain ⟨η, ⟨-, hη⟩, -⟩ := hDL K (A S) a (f α S hα) (hnz α S hα) w hw ω hm₁
  obtain ⟨η', ⟨-, hη'⟩, -⟩ := hDL K (A S) a (f α' S hα') (hnz α' S hα') w' hw' ω hm₂
  have d := eta_diff hFL (u α α' S hα hα') (f α S hα) (f α' S hα') (huf α α' S hα hα') (hnz α S hα) w w' wu hw hw' hwu
    ω η η' hη hη'
  have s1 := lam_spec α S hα _ ω η w hw hi hη
  have s2 := lam_spec α' S hα' _ ω η' w' hw' hi hη'
  have hz' : CH.d ((capU U S).ι ⋙ F₃) (a + 1) ((pairU P (capU U S)).cupC (Nat.add_comm 1 a)
      ((resU F₁ (capU_le U S hα)).pullC 1 (β α) - (resU F₁ (capU_le U S hα')).pullC 1 (β α')) x.1) = 0 := by
    rw [map_sub, LinearMap.sub_apply]
    exact congrArg Subtype.val hz
  have s3 := hcup α α' S hα hα' x.1 hy ω wu hwu hω.symm hz'
  have e1 : (incl F₃ (capU U S) hQ).mapH (a + 1) (((covSy F₃ U hQ).K S).cls
      (etaS P U hQ β α S hα a x - etaS P U hQ β α' S hα' a x) hz) = (CH.cx ((capU U S).ι ⋙ F₃)).cls
      ((pairU P (capU U S)).cupC (Nat.add_comm 1 a)
        ((resU F₁ (capU_le U S hα)).pullC 1 (β α) - (resU F₁ (capU_le U S hα')).pullC 1 (β α')) x.1) hz' := by
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    exact (LinearMap.congr_fun (map_sub ((pairU P (capU U S)).cupC (Nat.add_comm 1 a)) _ _) x.1).symm
  have e2 := (map_sub ((incl F₃ (capU U S) hQ).mapH (a + 1)) (lam α S hα (((covSy F₂ U hQ).K S).cls x hx))
    (lam α' S hα' (((covSy F₂ U hQ).K S).cls x hx))).trans (congrArg₂ (· - ·) s1 s2)
  refine (e1.trans s3).trans (Eq.trans ?_ e2.symm)
  have e3 : (e₃ S ⟨α', hα'⟩ : _) = e₃ S ⟨α, hα⟩ := rfl
  rw [e3, ← map_sub, ← smul_sub, d]

end Kill

end GlobalTheory.CompanionTheory.RelKill
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

theorem _root_.GlobalTheory.T.pairing_restrict_compat : ∀ {K : Type} [Field K] (E : XD K) {U₁ U₁' : ObjectProperty E.C₁} {U₂ U₂' : ObjectProperty E.C₂} {U₃ U₃' : ObjectProperty E.D} (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) (h₁' : ∀ T, U₃' T → U₁' (E.L₁.obj T)) (h₂' : ∀ T, U₃' T → U₂' (E.L₂.obj T)) (k₁ : U₁' ≤ U₁) (k₂ : U₂' ≤ U₂) (k₃ : U₃' ≤ U₃) {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (hn : i + j = n) (x : CH.Cn (U₁.ι ⋙ E.F₁ a) i) (y : CH.Cn (U₂.ι ⋙ E.F₂ a') j), (resU (E.F₃ c) k₃).pullC n ((E.pr U₁ U₂ U₃ h₁ h₂ ha).μ hn x y) = (E.pr U₁' U₂' U₃' h₁' h₂' ha).μ hn ((resU (E.F₁ a) k₁).pullC i x) ((resU (E.F₂ a') k₂).pullC j y) := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.pr_res | exact GlobalTheory.CompanionTheory.KunGlue.pr_res | (intros; apply GlobalTheory.CompanionTheory.KunGlue.pr_res <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

theorem _root_.GlobalTheory.T.direct_sum_system_descends : ∀ {K : Type} [Field K] {ι : Type} [DecidableEq ι] [Fintype ι] {I : Type 1} [DecidableEq I] (A : I → Sy.{1} K ι), (∀ i, (A i).Desc) → (sumSy A).Desc := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.SumDesc.sum_desc | exact GlobalTheory.CompanionTheory.KunGlue.SumDesc.sum_desc | (intros; apply GlobalTheory.CompanionTheory.KunGlue.SumDesc.sum_desc <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

theorem _root_.GlobalTheory.T.kuenneth_swap : ∀ {K : Type} [Field K] {P Q T : ℕ → Cx.{1} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)), KunE pr → KunE (P := Q) (Q := P) (T := T) (fun {a a' c} ha => swapPr pr ha) := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.kunE_swap | exact GlobalTheory.CompanionTheory.KunGlue.kunE_swap | (intros; apply GlobalTheory.CompanionTheory.KunGlue.kunE_swap <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

theorem _root_.GlobalTheory.T.shifted_system_descends : ∀ {K : Type} [Field K] {ι : Type} [DecidableEq ι] (ς : ℤˣ) (k : ℕ) (A : Sy.{1} K ι), A.Desc → (shSy ς k A).Desc := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.ShDesc.sh_desc | exact GlobalTheory.CompanionTheory.KunGlue.ShDesc.sh_desc | (intros; apply GlobalTheory.CompanionTheory.KunGlue.ShDesc.sh_desc <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

theorem _root_.GlobalTheory.T.direct_sum_complex_cohomology : ∀ {K : Type} [Field K] {I : Type 1} [DecidableEq I] (E : I → Cx.{1} K) (n : ℕ), ∃ e : (⨁ i, (E i).H n) ≃ₗ[K] (Dsum E).H n, ∀ (i : I) (x : (E i).X n) (hx : (E i).d n x = 0) (hx' : (Dsum E).d n (DirectSum.lof K I (fun i => (E i).X n) i x) = 0), e (DirectSum.lof K I (fun i => (E i).H n) i ((E i).cls x hx)) = (Dsum E).cls (DirectSum.lof K I (fun i => (E i).X n) i x) hx' := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.dsum_coh | exact GlobalTheory.CompanionTheory.KunGlue.dsum_coh | (intros; apply GlobalTheory.CompanionTheory.KunGlue.dsum_coh <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

theorem _root_.GlobalTheory.T.shifted_complex_cohomology : ∀ {K : Type} [Field K] (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) (n : ℕ), (n < k → Subsingleton ((Sh ς k C).H n)) ∧ ∀ (m : ℕ) (h : m + k = n), ∃ e : C.H m ≃ₗ[K] (Sh ς k C).H n, ∀ (y : (Sh ς k C).X n) (hy : (Sh ς k C).d n y = 0) (hy' : C.d m (y ⟨m, h⟩) = 0), e (C.cls (y ⟨m, h⟩) hy') = (Sh ς k C).cls y hy := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.ShiftCoh.main | exact GlobalTheory.CompanionTheory.KunGlue.ShiftCoh.main | (intros; apply GlobalTheory.CompanionTheory.KunGlue.ShiftCoh.main <;> assumption)
end

end

section

@[expose] public section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

theorem _root_.GlobalTheory.T.parabolic_eq_block_upper : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → parab k e = blockUpper k N β := by
  first | exact @GlobalTheory.CompanionTheory.ParabBridge.parab_eq_blockUpper | exact GlobalTheory.CompanionTheory.ParabBridge.parab_eq_blockUpper | (intros; apply GlobalTheory.CompanionTheory.ParabBridge.parab_eq_blockUpper <;> assumption)

end
end

section

@[expose] public section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical leviPar normLeviParSqrtModular)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

theorem _root_.GlobalTheory.T.levi_refinement_parabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {c : α → β' → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (e : (Σ i, m i) ≃ Fin N) (f : ∀ i, (Σ j, c i j) ≃ m i) (δ : Fin N → ℕ) (hδ : ∀ i j j' (t : c i j) (t' : c i j'), δ (e ⟨i, f i ⟨j, t⟩⟩) < δ (e ⟨i, f i ⟨j', t'⟩⟩) ↔ j < j') (x : Levi k m), x ∈ relUnip k f ↔ leviEmb k e x ∈ unipotentRadical k N δ := by
  first | exact @GlobalTheory.CompanionTheory.RelUnipBridge.mem_relUnip_iff_leviEmb_mem | exact GlobalTheory.CompanionTheory.RelUnipBridge.mem_relUnip_iff_leviEmb_mem | (intros; apply GlobalTheory.CompanionTheory.RelUnipBridge.mem_relUnip_iff_leviEmb_mem <;> assumption)

end
end

section

@[expose] public section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical leviPar normLeviParSqrtModular)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

theorem _root_.GlobalTheory.T.levi_refinement_block_order : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {c : α → β' → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (e : (Σ i, m i) ≃ Fin N) (f : ∀ i, (Σ j, c i j) ≃ m i) (δ : Fin N → ℕ) (hδ : ∀ i j j' (t : c i j) (t' : c i j'), δ (e ⟨i, f i ⟨j, t⟩⟩) < δ (e ⟨i, f i ⟨j', t'⟩⟩) ↔ j < j') (x : Levi k m), x ∈ relParab k f ↔ leviEmb k e x ∈ blockUpper k N δ := by
  first | exact @GlobalTheory.CompanionTheory.CellCompare.mem_relParab_iff_leviEmb_mem_blockUpper | exact GlobalTheory.CompanionTheory.CellCompare.mem_relParab_iff_leviEmb_mem_blockUpper | (intros; apply GlobalTheory.CompanionTheory.CellCompare.mem_relParab_iff_leviEmb_mem_blockUpper <;> assumption)

end
end
