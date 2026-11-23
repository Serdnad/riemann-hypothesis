module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapSpanBaseChangeEquivSubmoduleOf
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2658
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.OpenSubgrp

attribute [local instance] Over.cartesianMonoidalCategory

variable {S P : Scheme.{0}} {H₁ H₂ : Over S} [GrpObj H₁] [GrpObj H₂] {h₁ : H₁.left ⟶ P} {h₂ : H₂.left ⟶ P}
  {pS : P ⟶ S}

theorem mul_mem_range (e₁ : h₁ ≫ pS = H₁.hom) (e₂ : h₂ ≫ pS = H₂.hom) [IsOpenImmersion h₂]
    (hm : MulAgree H₁ H₂ h₁ h₂) {T : Scheme.{0}} {t : T ⟶ S} (a b : Over.mk t ⟶ H₁)
    (ha : ∀ y, h₁ (a.left y) ∈ Set.range h₂) (hb : ∀ y, h₁ (b.left y) ∈ Set.range h₂) :
    ∀ y, h₁ ((a * b).left y) ∈ Set.range h₂ := by
  have lift : ∀ c : Over.mk t ⟶ H₁, (∀ y, h₁ (c.left y) ∈ Set.range h₂) →
      ∃ c' : Over.mk t ⟶ H₂, c.left ≫ h₁ = c'.left ≫ h₂ := by
    intro c hc
    let c'' := IsOpenImmersion.lift h₂ (c.left ≫ h₁) (by rintro _ ⟨y, rfl⟩; exact hc y)
    have ec : c'' ≫ h₂ = c.left ≫ h₁ := IsOpenImmersion.lift_fac _ _ _
    refine ⟨Over.homMk c'' ?_, ec.symm⟩
    show c'' ≫ H₂.hom = t
    rw [← e₂, ← Category.assoc, ec, Category.assoc, e₁, Over.w c]
    rfl
  obtain ⟨a', ea⟩ := lift a ha
  obtain ⟨b', eb⟩ := lift b hb
  have := hm T t t a b a' b' ea eb
  intro y
  rw [← Scheme.Hom.comp_apply, this, Scheme.Hom.comp_apply]
  exact ⟨_, rfl⟩

end GlobalTheory.OpenSubgrp

namespace GlobalTheory.OpenSubgrp

attribute [local instance] Over.cartesianMonoidalCategory

theorem comp_inv' {S : Scheme.{0}} {G : Over S} [GrpObj G] {T T' : Over S} (ρ : T' ⟶ T) (x : T ⟶ G) :
    ρ ≫ x⁻¹ = (ρ ≫ x)⁻¹ :=
  (Category.assoc _ _ _).symm

theorem range_subset : ∀ (S P : Scheme.{0}) (H₁ H₂ : Over S) [GrpObj H₁] [GrpObj H₂] (h₁ : H₁.left ⟶ P)
    (h₂ : H₂.left ⟶ P), ∀ pS : P ⟶ S, h₁ ≫ pS = H₁.hom → h₂ ≫ pS = H₂.hom → IsOpenImmersion h₁ →
    IsOpenImmersion h₂ → Smooth H₁.hom → GeometricallyConnected H₁.hom → MulAgree H₁ H₂ h₁ h₂ →
    OneAgree (𝟙 S) (𝟙 S) H₁ H₂ h₁ h₂ → Set.range h₁ ⊆ Set.range h₂ := by
  intro S P H₁ H₂ _ _ h₁ h₂ pS e₁ e₂ _ _ _ _ hm ho
  have : GeometricallyIntegral H₁.hom := GlobalTheory.grpObj_geometricallyIntegral_of_smooth S H₁
  let WO : H₁.left.Opens := h₁ ⁻¹ᵁ h₂.opensRange
  have hW : ∀ x, x ∈ WO ↔ h₁ x ∈ Set.range h₂ := fun x => Iff.rfl

  have hone : ∀ s : S, ∃ y ∈ WO, H₁.hom y = s := by
    intro s
    refine ⟨(1 : Over.mk (𝟙 S) ⟶ H₁).left s, ?_, ?_⟩
    · rw [hW, ← Scheme.Hom.comp_apply, ho S (𝟙 S) (𝟙 S) rfl, Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    · rw [← Scheme.Hom.comp_apply, Over.w]; rfl
  let f := fst H₁ H₁
  let g := snd H₁ H₁
  let a : H₁ ⊗ H₁ ⟶ H₁ := g⁻¹ * f
  let O : (H₁ ⊗ H₁).left.Opens := a.left ⁻¹ᵁ WO ⊓ g.left ⁻¹ᵁ WO
  let Y : Over S := Over.mk (O.ι ≫ (H₁ ⊗ H₁).hom)
  let j : Y ⟶ H₁ ⊗ H₁ := Over.homMk O.ι rfl
  have e1 : (j ≫ g) * (j ≫ a) = j ≫ f := by
    rw [MonObj.comp_mul, comp_inv', mul_inv_cancel_left]
  have inW : ∀ y, h₁ ((j ≫ f).left y) ∈ Set.range h₂ := by
    rw [← e1]
    exact OpenSubgrp.mul_mem_range e₁ e₂ hm (j ≫ g) (j ≫ a) (fun y => y.2.2) (fun y => y.2.1)
  have hg : GeometricallyIrreducible f.left :=
    inferInstanceAs (GeometricallyIrreducible (pullback.fst H₁.hom H₁.hom))
  have m2 : ∀ z : H₁.left, ∃ w : (H₁ ⊗ H₁).left, g.left w ∈ WO ∧ f.left w = z := by
    intro z
    obtain ⟨y, hy, e⟩ := hone (H₁.hom z)
    obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback z y e.symm
    exact ⟨w, by rw [← hw2] at hy; exact hy, hw1⟩
  have m1 : ∀ z : H₁.left, ∃ w : (H₁ ⊗ H₁).left, a.left w ∈ WO ∧ f.left w = z := by
    intro z
    obtain ⟨w, hw1, hw2⟩ := m2 z
    let b : H₁ ⊗ H₁ ⟶ H₁ ⊗ H₁ := lift f (f * g⁻¹)
    have b1 : b ≫ a = g := by
      rw [MonObj.comp_mul, comp_inv', lift_fst, lift_snd, mul_inv_rev, inv_inv, inv_mul_cancel_right]
    have b2 : b ≫ f = f := lift_fst _ _
    refine ⟨b.left w, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, b1]; exact hw1
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, b2]; exact hw2
  rintro _ ⟨z, rfl⟩
  have hi : IsIrreducible (f.left ⁻¹' {z}) := by
    rw [← f.left.range_fiberι, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (f.left.fiberι z).continuous.continuousOn
  obtain ⟨w, hw, e⟩ := m1 z
  obtain ⟨w', hw', e'⟩ := m2 z
  obtain ⟨y, hy, k₁, k₂⟩ := hi.2 _ _ (a.left ⁻¹ᵁ WO).2 (g.left ⁻¹ᵁ WO).2 ⟨w, e, hw⟩ ⟨w', e', hw'⟩
  have := inW ⟨y, k₁, k₂⟩
  convert this using 2
  exact hy.symm

end GlobalTheory.OpenSubgrp
end

section

open GlobalTheory.Desc

open TensorProduct

namespace GlobalTheory.FlatSpanInter

theorem spanBy_algebraMap_eq {R₁ F₁ : Type} [CommRing R₁] [CommRing F₁] [Algebra R₁ F₁] (T : Set F₁) :
    spanBy (algebraMap R₁ F₁) T = (Submodule.span R₁ T : Set F₁) := by
  ext v
  simp only [SetLike.mem_coe, Submodule.mem_span_set']
  constructor
  · rintro ⟨n, r, t, ht, rfl⟩
    exact ⟨n, r, fun i => ⟨t i, ht i⟩, by simp [Algebra.smul_def]⟩
  · rintro ⟨n, r, t, rfl⟩
    exact ⟨n, r, fun i => t i, fun i => (t i).2, by simp [Algebra.smul_def]⟩

variable {R R₁ F F₁ : Type} [CommRing R] [IsDomain R] [CommRing R₁] [Field F] [CommRing F₁]
  [Algebra R R₁] [Algebra R F] [Algebra R₁ F₁] [Algebra R F₁] [IsScalarTower R R₁ F₁]

theorem smul_injective_tensor (hc₀ : Function.Injective (algebraMap R F)) {d : R} (hd : d ≠ 0)
    (x : R₁ ⊗[R] F) (hx : d • x = 0) : x = 0 := by
  set u : F := (algebraMap R F d)⁻¹
  have hu : u * algebraMap R F d = 1 :=
    inv_mul_cancel₀ (fun h => hd (hc₀ (by rw [h, map_zero])))
  have key : ∀ z : R₁ ⊗[R] F, LinearMap.lTensor R₁ (LinearMap.mulLeft R u) (d • z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r f =>
      rw [← TensorProduct.tmul_smul, LinearMap.lTensor_tmul, LinearMap.mulLeft_apply, Algebra.smul_def,
        ← mul_assoc, hu, one_mul]
    | add a b ha hb => rw [smul_add, map_add (f := _), ha, hb]
  rw [← key x, hx, map_zero]

theorem free_injective (θ : F →ₐ[R] F₁)
    (hLD : LinDisj (algebraMap R F) (algebraMap R₁ F₁) (θ : F →+* F₁))
    {ι : Type} [Fintype ι] (v : ι → F) (hli : LinearIndependent R v) :
    Function.Injective ((LinearMap.liftBaseChange R₁ θ.toLinearMap) ∘ₗ
      ((Submodule.span R (Set.range v)).subtype.baseChange R₁)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  set bB := Module.Basis.span hli
  set bb := Algebra.TensorProduct.basis R₁ bB
  have hval : ∀ j, ((LinearMap.liftBaseChange R₁ θ.toLinearMap) ∘ₗ
      ((Submodule.span R (Set.range v)).subtype.baseChange R₁)) (bb j) = θ (v j) := by
    intro j
    simp [bb, bB, Algebra.TensorProduct.basis_apply, Module.Basis.span_apply, LinearMap.liftBaseChange_tmul, LinearMap.baseChange_tmul]
  have e1 : ((LinearMap.liftBaseChange R₁ θ.toLinearMap) ∘ₗ
      ((Submodule.span R (Set.range v)).subtype.baseChange R₁)) y =
        ∑ j, algebraMap R₁ F₁ (bb.repr y j) * θ (v j) := by
    conv_lhs => rw [← bb.sum_repr y]

    simp only [map_sum, map_smul, hval, Algebra.smul_def]
  rw [hy] at e1
  set e := (Fintype.equivFin ι).symm
  have h0 := hLD _ (v ∘ e) (by
      intro r hr
      funext i
      exact Fintype.linearIndependent_iff.1 (hli.comp e e.injective) r
        (by simpa [Algebra.smul_def] using hr) i)
    (fun i => bb.repr y (e i)) (by
      rw [e1, ← Equiv.sum_comp e]
      rfl)
  have hr : bb.repr y = 0 := by
    ext j
    simpa using congrFun h0 (e.symm j)
  exact bb.repr.map_eq_zero_iff.1 hr

theorem liftBaseChange_injective (hc₀ : Function.Injective (algebraMap R F)) (θ : F →ₐ[R] F₁)
    (hLD : LinDisj (algebraMap R F) (algebraMap R₁ F₁) (θ : F →+* F₁)) :
    Function.Injective (LinearMap.liftBaseChange R₁ θ.toLinearMap) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
  set g : S → F := fun i => (i : R₁ × F).2
  obtain ⟨s, hli, hmax⟩ := exists_maximal_linearIndepOn R g
  have ha : ∀ i, ∃ a : R, a ≠ 0 ∧ a • g i ∈ Submodule.span R (g '' s) := by
    intro i
    by_cases hi : i ∈ s
    · exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span ⟨i, hi, rfl⟩⟩
    · exact hmax i hi
  choose a ha0 ha using ha
  set d := ∏ i, a i
  have hd : d ≠ 0 := Finset.prod_ne_zero_iff.2 (fun i _ => ha0 i)
  have hdg : ∀ i, d • g i ∈ Submodule.span R (Set.range fun j : s => g j) := by
    intro i
    rw [← Set.image_eq_range]
    obtain ⟨e, he⟩ : a i ∣ d := Finset.dvd_prod_of_mem a (Finset.mem_univ i)
    rw [he, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (ha i)
  haveI : Fintype s := Fintype.ofFinite s
  set B := Submodule.span R (Set.range fun j : s => g j)
  set y : R₁ ⊗[R] B := ∑ i : S, (i : R₁ × F).1 ⊗ₜ ⟨d • g i, hdg i⟩
  have hy : B.subtype.baseChange R₁ y = d • ∑ i ∈ S, i.1 ⊗ₜ i.2 := by
    rw [Finset.smul_sum, ← Finset.sum_coe_sort S]

    simp only [y, map_sum, LinearMap.baseChange_tmul, Submodule.subtype_apply, TensorProduct.tmul_smul, g]
  have hz : ((LinearMap.liftBaseChange R₁ θ.toLinearMap) ∘ₗ (B.subtype.baseChange R₁)) y = 0 := by
    rw [LinearMap.comp_apply, hy, LinearMap.map_smul_of_tower, hx, smul_zero]
  have hy0 : y = 0 := free_injective θ hLD (fun j : s => g j) hli (by rw [hz, map_zero])
  exact smul_injective_tensor hc₀ hd _ (by rw [← hy, hy0, map_zero])

theorem spanBy_image_eq_map (θ : F →ₐ[R] F₁) (P : Submodule R F) :
    spanBy (algebraMap R₁ F₁) (θ '' P) =
      ((P.baseChange R₁).map (LinearMap.liftBaseChange R₁ θ.toLinearMap) : Set F₁) := by
  rw [spanBy_algebraMap_eq, Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe,
    Set.image_image]
  congr 2
  ext p
  simp [LinearMap.liftBaseChange_tmul]

end GlobalTheory.FlatSpanInter

theorem GlobalTheory.Desc.spanBy_image_inter : ∀ (R R₁ F F₁ : Type) [CommRing R] [IsDomain R] [CommRing R₁] [Field F] [Field F₁]
    (ρ : R →+* R₁) (c₀ : R →+* F) (c₁ : R₁ →+* F₁) (θ : F →+* F₁), ρ.Flat → Function.Injective c₀ →
    θ.comp c₀ = c₁.comp ρ → LinDisj c₀ c₁ θ → ∀ (M N : Set F), (0 : F) ∈ M → (∀ a ∈ M, ∀ b ∈ M, a + b ∈ M) →
    (∀ r, ∀ a ∈ M, c₀ r * a ∈ M) → (0 : F) ∈ N → (∀ a ∈ N, ∀ b ∈ N, a + b ∈ N) → (∀ r, ∀ a ∈ N, c₀ r * a ∈ N) →
    spanBy c₁ (θ '' (M ∩ N)) = spanBy c₁ (θ '' M) ∩ spanBy c₁ (θ '' N) := by
  intro R R₁ F F₁ _ _ _ _ _ ρ c₀ c₁ θ hρ hc₀ hcomp hLD M N hM0 hMa hMs hN0 hNa hNs
  letI : Algebra R R₁ := ρ.toAlgebra
  letI : Algebra R F := c₀.toAlgebra
  letI : Algebra R₁ F₁ := c₁.toAlgebra
  letI : Algebra R F₁ := (c₁.comp ρ).toAlgebra
  haveI : IsScalarTower R R₁ F₁ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Flat R R₁ := hρ
  let θa : F →ₐ[R] F₁ := { θ with commutes' := fun r => RingHom.congr_fun hcomp r }
  let MS : Submodule R F :=
    { carrier := M, add_mem' := fun ha hb => hMa _ ha _ hb, zero_mem' := hM0,
      smul_mem' := fun r a ha => hMs r a ha }
  let NS : Submodule R F :=
    { carrier := N, add_mem' := fun ha hb => hNa _ ha _ hb, zero_mem' := hN0,
      smul_mem' := fun r a ha => hNs r a ha }
  have hinj := GlobalTheory.FlatSpanInter.liftBaseChange_injective (R₁ := R₁) hc₀ θa hLD
  have kI : spanBy c₁ (θ '' (M ∩ N)) = _ := GlobalTheory.FlatSpanInter.spanBy_image_eq_map θa (MS ⊓ NS)
  have kM : spanBy c₁ (θ '' M) = _ := GlobalTheory.FlatSpanInter.spanBy_image_eq_map θa MS
  have kN : spanBy c₁ (θ '' N) = _ := GlobalTheory.FlatSpanInter.spanBy_image_eq_map θa NS
  rw [kI, kM, kN, GlobalTheory.baseChange_inf, Submodule.map_inf _ hinj, Submodule.coe_inf]
end

section

open GlobalTheory.Desc

namespace GlobalTheory.Desc.LocalDescent

theorem exists_basis_of_finite : ∀ (R F : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Field F] (c₀ : R →+* F), Function.Injective c₀ → ∀ (p : Ideal R), p.IsPrime → p.height = 1 → ∀ (T : Set F), T.Finite → ∃ (k : ℕ) (b : Fin k → F), (∀ j, ∃ (n : ℕ) (g : Fin n → R) (v : Fin n → F) (t : R), t ∉ p ∧ (∀ i, v i ∈ T) ∧ c₀ t * b j = ∑ i, c₀ (g i) * v i) ∧ (∀ r : Fin k → R, ∑ j, c₀ (r j) * b j = 0 → r = 0) ∧ ∃ t : R, t ∉ p ∧ ∀ v ∈ T, ∃ g : Fin k → R, c₀ t * v = ∑ j, c₀ (g j) * b j := by
  intro R F _ _ _ _ _ c₀ hc p hp hp1 T hT
  classical
  let B := Localization.AtPrime p
  haveI := GlobalTheory.isDiscreteValuationRing_of_height_eq_one p hp1 B
  have hu : ∀ y : p.primeCompl, IsUnit (c₀ y) := fun y => IsUnit.mk0 _ fun h =>
    y.2 (((injective_iff_map_eq_zero c₀).mp hc _ h) ▸ p.zero_mem)
  let l : B →+* F := IsLocalization.lift hu
  have hl : ∀ r, l (algebraMap R B r) = c₀ r := fun r => IsLocalization.lift_eq hu r
  have hinj := IsLocalization.injective B p.primeCompl_le_nonZeroDivisors
  have hli : Function.Injective l := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨r, s⟩, e⟩ := IsLocalization.surj p.primeCompl z
    have h0 : c₀ r = 0 := by rw [← hl, ← e, map_mul, hz, zero_mul]
    rw [(injective_iff_map_eq_zero c₀).mp hc _ h0, map_zero] at e
    exact (IsLocalization.map_units B s).mul_left_eq_zero.mp e
  letI : Algebra B F := l.toAlgebra
  have hsm : ∀ (z : B) (v : F), z • v = l z * v := fun _ _ => rfl
  haveI : FaithfulSMul B F := (faithfulSMul_iff_algebraMap_injective B F).mpr hli
  let E := Submodule.span B T
  haveI : Module.Finite B E := Module.Finite.span_of_finite B hT
  haveI : Module.Free B E := inferInstance
  let e := Module.finBasis B E
  have clear : ∀ {ι : Type} [Finite ι] (z : ι → B), ∃ t, t ∉ p ∧ ∃ g : ι → R,
      ∀ i, c₀ (g i) = c₀ t * l (z i) := fun z => by
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite p.primeCompl z
    choose h hh using hd
    exact ⟨d, d.2, h, fun i => by rw [← hl, hh, Algebra.smul_def, map_mul, hl]⟩
  refine ⟨_, fun j => (e j : F), fun j => ?_, fun r hr => ?_, ?_⟩
  · obtain ⟨n, z, v, hv⟩ := Submodule.mem_span_set'.mp (e j).2
    obtain ⟨t, ht, g, hg⟩ := clear z
    refine ⟨n, g, fun i => v i, t, ht, fun i => (v i).2, ?_⟩
    simp only [← hv, hg, hsm, Finset.mul_sum, mul_assoc]
  · have := Fintype.linearIndependent_iff.mp e.linearIndependent (fun j => algebraMap R B (r j))
      (Subtype.ext (by simpa [hsm, hl] using hr))
    funext j
    exact (injective_iff_map_eq_zero _).mp hinj _ (this j)
  · haveI : Finite T := hT
    obtain ⟨t, ht, g, hg⟩ := clear
      fun z : T × Fin (Module.finrank B E) => e.repr ⟨z.1, Submodule.subset_span z.1.2⟩ z.2
    refine ⟨t, ht, fun v hv => ⟨fun j => g (⟨v, hv⟩, j), ?_⟩⟩
    have := congrArg Subtype.val (e.sum_repr ⟨v, Submodule.subset_span hv⟩)
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, hsm] at this
    simp only [hg, mul_assoc, ← Finset.mul_sum, this]

theorem span_test : ∀ (R₁ F₁ : Type) [CommRing R₁] [IsDomain R₁] [IsNoetherianRing R₁] [IsIntegrallyClosed R₁] [Field F₁] (c₁ : R₁ →+* F₁), Function.Injective c₁ → ∀ (S : Submonoid R₁), (0 : R₁) ∉ S → ∀ (k : ℕ) (b : Fin k → F₁), (∀ r : Fin k → R₁, ∑ j, c₁ (r j) * b j = 0 → r = 0) → ∀ (x : F₁) (a : R₁), a ≠ 0 → (∃ (t : R₁) (g : Fin k → R₁), t ∈ S ∧ c₁ (t * a) * x = ∑ j, c₁ (g j) * b j) → (∀ q : Ideal R₁, q.IsPrime → q.height = 1 → a ∈ q → Disjoint (S : Set R₁) (q : Set R₁) → ∃ s, s ∉ q ∧ ∃ (t : R₁) (g : Fin k → R₁), t ∈ S ∧ c₁ (t * s) * x = ∑ j, c₁ (g j) * b j) → ∃ (t : R₁) (g : Fin k → R₁), t ∈ S ∧ c₁ t * x = ∑ j, c₁ (g j) * b j := by
  intro R₁ F₁ _ _ _ _ _ c₁ hc S hS k b hind x a ha ⟨t, g, ht, e⟩ hloc
  classical
  have hle : S ≤ nonZeroDivisors R₁ := fun y hy =>
    mem_nonZeroDivisors_of_ne_zero fun h => hS (h ▸ hy)
  let A := Localization S
  haveI : IsDomain A := IsLocalization.isDomain_of_le_nonZeroDivisors A hle
  haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing S A inferInstance
  haveI : IsIntegrallyClosed A := isIntegrallyClosed_of_isLocalization A S hle
  have hinj := IsLocalization.injective A hle
  have hdvd : ∀ j, algebraMap R₁ A a ∣ algebraMap R₁ A (g j) := fun j => by
    refine GlobalTheory.dvd_of_forall_height_eq_one ((map_ne_zero_iff _ hinj).mpr ha) fun Q hQ h1 haQ => ?_
    obtain ⟨hq, hd⟩ := (IsLocalization.isPrime_iff_isPrime_disjoint S A Q).mp hQ
    obtain ⟨s, hs, t', g', ht', e'⟩ := hloc (Q.comap (algebraMap R₁ A)) hq
      (by rw [IsLocalization.height_under S Q, h1]) haQ hd
    have h0 := hind (fun j => t' * s * g j - t * a * g' j) (by
      simp only [map_sub, map_mul, sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum, ← e, ← e']
      ring)
    have h1 : t' * s * g j = t * a * g' j := sub_eq_zero.mp (congrFun h0 j)
    refine ⟨algebraMap R₁ A s, hs, (IsLocalization.map_units A ⟨t', ht'⟩).dvd_mul_left.mp ?_⟩
    refine ⟨algebraMap R₁ A (t * g' j), ?_⟩
    simp only [← map_mul]
    congr 1
    linear_combination h1
  choose y hy using hdvd
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite S y
  choose h hh using hd
  refine ⟨d * t, h, S.mul_mem d.2 ht, ?_⟩
  have h1 : ∀ j, (d : R₁) * g j = a * h j := fun j => hinj (by
    rw [map_mul, map_mul, hh, hy, Algebra.smul_def]; ring)
  apply mul_left_cancel₀ ((map_ne_zero_iff c₁ hc).mpr ha)
  have : c₁ a * (c₁ (d * t) * x) = c₁ d * (c₁ (t * a) * x) := by simp only [map_mul]; ring
  rw [this, e, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, h1]

theorem mem_spanBy_of_forall_height_one : ∀ (R R₁ F F₁ : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CommRing R₁] [IsDomain R₁] [IsNoetherianRing R₁] [IsIntegrallyClosed R₁] [Field F] [Field F₁] (ρ : R →+* R₁) (c₀ : R →+* F) (c₁ : R₁ →+* F₁) (θ : F →+* F₁) (f : R), f ≠ 0 → ρ.Flat → Function.Injective ρ → Function.Injective c₀ → θ.comp c₀ = c₁.comp ρ → LinDisj c₀ c₁ θ → ∀ (p : Ideal R), p.IsPrime → p.height = 1 → f ∈ p → ∀ (W : Set F), (∀ u, ∃ m : ℕ, c₀ f ^ m * u ∈ W) → (∀ a ∈ W, ∀ b ∈ W, a + b ∈ W) → (∀ r, ∀ a ∈ W, c₀ r * a ∈ W) → (∀ s, s ∉ p → ∀ a ∈ W, (c₀ s)⁻¹ * a ∈ W) → ∀ x ∈ spanBy c₁ (Set.range θ), (∀ q : Ideal R₁, q.IsPrime → q.height = 1 → ρ f ∈ q → q.comap ρ = p → ∃ s, s ∉ q ∧ c₁ s * x ∈ spanBy c₁ (θ '' W)) → x ∈ spanBy c₁ (θ '' W) := by
  intro R R₁ F F₁ _ _ _ _ _ _ _ _ _ _ ρ c₀ c₁ θ f hf _ hρ hc₀ hcomp hlin p hp hp1 _ W hWt hWadd hWsmul hWdiv x hx hloc
  classical
  have hθ : ∀ r, θ (c₀ r) = c₁ (ρ r) := fun r => RingHom.congr_fun hcomp r
  have hc₁ : Function.Injective c₁ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro r hr
    have := hlin 1 (fun _ => 1) (fun g hg => by
      funext i
      have h0 : c₀ (g 0) = 0 := by simpa using hg
      rw [Subsingleton.elim i 0]
      exact (injective_iff_map_eq_zero c₀).mp hc₀ _ h0) (fun _ => r) (by simpa using hr)
    exact congrFun this 0
  have hW0 : (0 : F) ∈ W := by simpa using hWt 0
  have hWsum : ∀ (n : ℕ) (g : Fin n → R) (v : Fin n → F), (∀ i, v i ∈ W) → ∑ i, c₀ (g i) * v i ∈ W :=
    fun n g v hv => Finset.sum_induction _ (· ∈ W) (fun a b ha hb => hWadd a ha b hb) hW0
      fun i _ => hWsmul _ _ (hv i)
  have hne : ∀ t, t ∉ p → c₀ t ≠ 0 := fun t ht h =>
    ht (((injective_iff_map_eq_zero c₀).mp hc₀ _ h) ▸ p.zero_mem)
  have hρf : ρ f ≠ 0 := fun h => hf ((injective_iff_map_eq_zero ρ).mp hρ _ h)
  obtain ⟨n, r, u', hu', rfl⟩ := hx
  choose u hu using hu'
  obtain rfl : u' = fun i => θ (u i) := funext fun i => (hu i).symm
  set x := ∑ i, c₁ (r i) * θ (u i) with hxdef
  choose m hm using hWt
  let M := Finset.univ.sup fun i => m (u i)
  have hM : ∀ i, c₀ f ^ M * u i ∈ W := fun i => by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le
      (Finset.le_sup (f := fun i => m (u i)) (Finset.mem_univ i) : m (u i) ≤ M)
    have := hWsmul (f ^ d) _ (hm (u i))
    rwa [map_pow, ← mul_assoc, ← pow_add, add_comm, ← hd] at this
  let S : Submonoid R₁ := p.primeCompl.map ρ
  let G : Set (PrimeSpectrum R₁) :=
    {q | q.asIdeal.height = 1 ∧ ρ f ∈ q.asIdeal ∧ Disjoint (S : Set R₁) (q.asIdeal : Set R₁)}
  have hG : G.Finite := (GlobalTheory.finite_height_eq_one_mem hρf).subset fun q hq => ⟨hq.1, hq.2.1⟩
  have H : ∀ q : G, ∃ (s : R₁) (N : ℕ) (g : Fin N → R₁) (w : Fin N → F),
      s ∉ q.1.asIdeal ∧ (∀ l, w l ∈ W) ∧ c₁ s * x = ∑ l, c₁ (g l) * θ (w l) := by
    rintro ⟨q, h1, h2, h3⟩
    have hle : q.asIdeal.comap ρ ≤ p := fun t ht => by_contra fun htp =>
      Set.disjoint_left.mp h3 ⟨t, htp, rfl⟩ ht
    have heq : q.asIdeal.comap ρ = p :=
      le_antisymm hle ((GlobalTheory.mem_minimalPrimes_span_singleton_of_height_eq_one hp1 hf (hle h2)).2
        ⟨Ideal.comap_isPrime ρ _, (Ideal.span_singleton_le_iff_mem _).mpr h2⟩ hle)
    obtain ⟨s, hs, N, g, w', hw', e⟩ := hloc q.asIdeal q.isPrime h1 h2 heq
    choose w hw hw' using hw'
    exact ⟨s, N, g, w, hs, hw, by simp only [hw', e]⟩
  choose s N g w hs hw he using H
  haveI : Finite G := hG
  let T : Set F := Set.range (fun i => c₀ f ^ M * u i) ∪ ⋃ q : G, Set.range (w q)
  have hT : T.Finite := (Set.finite_range _).union (Set.finite_iUnion fun q => Set.finite_range _)
  have hTW : T ⊆ W := by
    rintro _ (⟨i, rfl⟩ | ⟨_, ⟨q, rfl⟩, l, rfl⟩)
    · exact hM i
    · exact hw q l
  obtain ⟨k, b, hb, hind, t, ht, hexp⟩ := exists_basis_of_finite R F c₀ hc₀ p hp hp1 T hT
  have hbW : ∀ j, b j ∈ W := fun j => by
    obtain ⟨n', g', v, t', ht', hv, e⟩ := hb j
    have := hWdiv t' ht' _ (hWsum n' g' v fun i => hTW (hv i))
    rwa [← e, inv_mul_cancel_left₀ (hne t' ht')] at this
  have key : ∀ (n' : ℕ) (g' : Fin n' → R₁) (v : Fin n' → F), (∀ i, v i ∈ T) →
      ∃ h : Fin k → R₁, c₁ (ρ t) * ∑ i, c₁ (g' i) * θ (v i) = ∑ j, c₁ (h j) * θ (b j) := by
    intro n' g' v hv
    choose h hh using fun i => hexp (v i) (hv i)
    refine ⟨fun j => ∑ i, g' i * ρ (h i j), ?_⟩

    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_

    rw [mul_left_comm, ← hθ, ← map_mul, hh, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hθ, mul_assoc]
  have htS : ρ t ∈ S := ⟨t, ht, rfl⟩
  obtain ⟨_, h, ⟨t₀, ht₀, rfl⟩, e⟩ := span_test R₁ F₁ c₁ hc₁ S
    (by
      rintro ⟨t₀, ht₀, e⟩
      exact ht₀ (((injective_iff_map_eq_zero ρ).mp hρ _ e) ▸ p.zero_mem))
    k (fun j => θ (b j)) (hlin k b hind) x (ρ f ^ M) (pow_ne_zero _ hρf)
    (by
      obtain ⟨h, e⟩ := key n r (fun i => c₀ f ^ M * u i) fun i => Or.inl ⟨i, rfl⟩
      refine ⟨_, h, htS, ?_⟩
      rw [← e, map_mul, mul_assoc, hxdef, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_pow, map_pow, hθ, mul_left_comm])
    (by
      intro q hq h1 h2 h3
      let q' : G := ⟨⟨q, hq⟩, h1, hq.mem_of_pow_mem _ h2, h3⟩
      obtain ⟨h, e⟩ := key _ (g q') (w q') fun l => Or.inr (Set.mem_iUnion.mpr ⟨q', l, rfl⟩)
      exact ⟨s q', hs q', _, h, htS, by rw [← e, ← he, map_mul, mul_assoc]⟩)
  refine ⟨k, h, fun j => θ ((c₀ t₀)⁻¹ * b j), fun j => ⟨_, hWdiv t₀ ht₀ _ (hbW j), rfl⟩, ?_⟩
  have h0 : c₁ (ρ t₀) ≠ 0 := by rw [← hθ]; exact (map_ne_zero θ).mpr (hne t₀ ht₀)
  apply mul_left_cancel₀ h0
  rw [e, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  beta_reduce
  rw [map_mul, map_inv₀, hθ, mul_left_comm, mul_inv_cancel_left₀ h0]

end GlobalTheory.Desc.LocalDescent
end

section

open AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.hasFibrewiseNonvanishingThetaSection_of_smooth_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), SmoothOfRelativeDimension Dw.dim Y.s → GlobalTheory.Models.HasTheta Y.t.G Y.t.PP.L := by
  first | exact @GlobalTheory.ThetaNormal.hasTheta_of_smooth | exact GlobalTheory.ThetaNormal.hasTheta_of_smooth | (intros; apply GlobalTheory.ThetaNormal.hasTheta_of_smooth <;> assumption)
end
