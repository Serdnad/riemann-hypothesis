module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle759
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle720
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle721
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle762
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle763
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

private theorem exAff (Z : Scheme.{0}) {O : Z.Opens} {z : Z} (hz : z ∈ O) :
    ∃ V : Z.affineOpens, z ∈ V.1 ∧ V.1 ≤ O := by
  obtain ⟨V, hV, hzV, hVO⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens hz
  exact ⟨⟨V, hV⟩, hzV, hVO⟩

theorem pair_pre_bijective : ∀ (R' : Type) [CommRing R'] (X Y Y' : Scheme.{0}) (ψ : Y ⟶ X) (χ : Y' ⟶ Y) [IsClosedImmersion χ] (q' : Y' ⟶ Sp R'), Function.Bijective (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull1 ∧ Function.Bijective (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull2 ∧ (CohomZeroIsConstants (OAff q') → CohomZeroIsConstants (pairFst ψ ⋙ OPre χ q')) := by
  intro R' _ X Y Y' ψ χ _ q'
  have hG : Monotone (fun p : Pair ψ ↦ preU χ p.1.1) := fun _ _ h ↦ preU_mono χ (Pair.le_fst h)
  have hF : pairFst ψ ⋙ preAff χ = hG.functor.op := rfl
  have key := GlobalTheory.T.structureSheafCohomology_basis_bijective R' Y' q' (Pair ψ) (fun p ↦ preU χ p.1.1) hG ?cov ?dir
  · rw [hF]
    exact key
  case cov =>
    intro U x hx
    obtain ⟨t, ht, hte⟩ := χ.isClosedEmbedding.isInducing.isOpen_iff.1 U.1.2
    have hxt : χ x ∈ (⟨t, ht⟩ : Y.Opens) := by
      show χ x ∈ t
      rw [← Set.mem_preimage, hte]; exact hx
    obtain ⟨W, hW, -⟩ := exAff X (show ψ (χ x) ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨V, hV, hVle⟩ := exAff Y (show χ x ∈ (⟨t, ht⟩ : Y.Opens) ⊓ ψ ⁻¹ᵁ W.1 from ⟨hxt, hW⟩)
    refine ⟨⟨(V, W), fun y hy ↦ (hVle hy).2⟩, hV, ?_⟩
    intro y hy
    have : χ y ∈ t := (hVle hy).1
    rw [← Set.mem_preimage, hte] at this
    exact this
  case dir =>
    intro a b x ha hb
    have hya : ψ (χ x) ∈ a.1.2.1 := a.2 ha
    have hyb : ψ (χ x) ∈ b.1.2.1 := b.2 hb
    obtain ⟨W, hW, hWle⟩ := exAff X (show ψ (χ x) ∈ a.1.2.1 ⊓ b.1.2.1 from ⟨hya, hyb⟩)
    obtain ⟨V, hV, hVle⟩ := exAff Y
      (show χ x ∈ (a.1.1.1 ⊓ b.1.1.1) ⊓ ψ ⁻¹ᵁ W.1 from ⟨⟨ha, hb⟩, hW⟩)
    refine ⟨⟨(V, W), fun y hy ↦ (hVle hy).2⟩, ?_, ?_, hV⟩
    · exact ⟨fun y hy ↦ (hVle hy).1.1, fun y hy ↦ (hWle hy).1⟩
    · exact ⟨fun y hy ↦ (hVle hy).1.2, fun y hy ↦ (hWle hy).2⟩

end GlobalTheory.AbCoh
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.AxesPull

variable {R : Type} [CommRing R]

theorem isAffine_unit : IsAffine (𝟙_ (Over (Sp R))).left := inferInstanceAs (IsAffine (Sp R))

theorem pO1_comp {X Y Z : Over (Sp R)} (g : X ⟶ Y) (f : Y ⟶ Z) (a) : pO1 g (pO1 f a) = pO1 (g ≫ f) a :=
  ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.1 R R Z.left Y.left Z.hom Y.hom (RingHom.id R) f.left (ovw f) R X.left X.hom (RingHom.id R) g.left
    (ovw g) (RingHom.id R) (g ≫ f).left (ovw (g ≫ f)) (Over.comp_left _ _ _ g f) fun _ ↦ rfl).1 a)

theorem pF_comp {X Y Z : Over (Sp R)} (g : X ⟶ Y) (f : Y ⟶ Z) (a) : pF g (pF f a) = pF (g ≫ f) a :=
  ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.1 R R Z.left Y.left Z.hom Y.hom (RingHom.id R) f.left (ovw f) R X.left X.hom (RingHom.id R) g.left
    (ovw g) (RingHom.id R) (g ≫ f).left (ovw (g ≫ f)) (Over.comp_left _ _ _ g f) fun _ ↦ rfl).2.2.1 a)

theorem pH1_comp {X Y Z : Over (Sp R)} (g : X ⟶ Y) (f : Y ⟶ Z) (a) : deRhamH1Pullback g (deRhamH1Pullback f a) = deRhamH1Pullback (g ≫ f) a :=
  ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.1 R R Z.left Y.left Z.hom Y.hom (RingHom.id R) f.left (ovw f) R X.left X.hom (RingHom.id R) g.left
    (ovw g) (RingHom.id R) (g ≫ f).left (ovw (g ≫ f)) (Over.comp_left _ _ _ g f) fun _ ↦ rfl).2.2.2.1 a)

theorem pO1_unit {X Y : Over (Sp R)} (u : X ⟶ 𝟙_ (Over (Sp R))) (f : 𝟙_ (Over (Sp R)) ⟶ Y) (a) :
    pO1 (u ≫ f) a = 0 := by
  rw [← pO1_comp]
  haveI := ((GlobalTheory.AbCoh.Vanish.main.1 R (𝟙_ (Over (Sp R))).left (𝟙_ (Over (Sp R))).hom isAffine_unit).1)
  rw [Subsingleton.elim (pO1 f a) 0, map_zero]

theorem pF_unit {X Y : Over (Sp R)} (u : X ⟶ 𝟙_ (Over (Sp R))) (f : 𝟙_ (Over (Sp R)) ⟶ Y) (a) :
    pF (u ≫ f) a = 0 := by
  rw [← pF_comp]
  haveI := (GlobalTheory.AbCoh.Vanish.main.2 R).1
  rw [Subsingleton.elim (pF f a) 0, map_zero]

theorem pH1_unit {X Y : Over (Sp R)} (u : X ⟶ 𝟙_ (Over (Sp R))) (f : 𝟙_ (Over (Sp R)) ⟶ Y) (a) :
    deRhamH1Pullback (u ≫ f) a = 0 := by
  rw [← pH1_comp]
  haveI := (GlobalTheory.AbCoh.Vanish.main.2 R).2
  rw [Subsingleton.elim (deRhamH1Pullback f a) 0, map_zero]

theorem main : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], (∀ a, pO1 (lift (𝟙 A) (toUnit A ≫ η[A])) (pO1 (fst A A) a) = a ∧ pO1 (lift (𝟙 A) (toUnit A ≫ η[A])) (pO1 (snd A A) a) = 0 ∧ pO1 (lift (𝟙 A) (toUnit A ≫ η[A])) (pO1 μ[A] a) = a ∧ pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)) (pO1 (fst A A) a) = 0 ∧ pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)) (pO1 (snd A A) a) = a ∧ pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)) (pO1 μ[A] a) = a) ∧ (∀ a, pF (lift (𝟙 A) (toUnit A ≫ η[A])) (pF (fst A A) a) = a ∧ pF (lift (𝟙 A) (toUnit A ≫ η[A])) (pF (snd A A) a) = 0 ∧ pF (lift (𝟙 A) (toUnit A ≫ η[A])) (pF μ[A] a) = a ∧ pF (lift (toUnit A ≫ η[A]) (𝟙 A)) (pF (fst A A) a) = 0 ∧ pF (lift (toUnit A ≫ η[A]) (𝟙 A)) (pF (snd A A) a) = a ∧ pF (lift (toUnit A ≫ η[A]) (𝟙 A)) (pF μ[A] a) = a) ∧ (∀ a, deRhamH1Pullback (lift (𝟙 A) (toUnit A ≫ η[A])) (deRhamH1Pullback (fst A A) a) = a ∧ deRhamH1Pullback (lift (𝟙 A) (toUnit A ≫ η[A])) (deRhamH1Pullback (snd A A) a) = 0 ∧ deRhamH1Pullback (lift (𝟙 A) (toUnit A ≫ η[A])) (deRhamH1Pullback μ[A] a) = a ∧ deRhamH1Pullback (lift (toUnit A ≫ η[A]) (𝟙 A)) (deRhamH1Pullback (fst A A) a) = 0 ∧ deRhamH1Pullback (lift (toUnit A ≫ η[A]) (𝟙 A)) (deRhamH1Pullback (snd A A) a) = a ∧ deRhamH1Pullback (lift (toUnit A ≫ η[A]) (𝟙 A)) (deRhamH1Pullback μ[A] a) = a) := by
  intro R _ A _
  have hid := (GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.2.2 R A)
  refine ⟨fun a ↦ ?_, fun a ↦ ?_, fun a ↦ ?_⟩
  · simp only [pO1_comp, lift_fst, lift_snd, lift_comp_one_right, lift_comp_one_left, pO1_unit, hid.1, and_self]
  · simp only [pF_comp, lift_fst, lift_snd, lift_comp_one_right, lift_comp_one_left, pF_unit, hid.2.2.1, and_self]
  · simp only [pH1_comp, lift_fst, lift_snd, lift_comp_one_right, lift_comp_one_left, pH1_unit, hid.2.2.2.1, and_self]

end GlobalTheory.AbCoh.AxesPull
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.AbCoh.PrimLift

theorem pO1_comp {R : Type} [CommRing R] {Y A B : Over (Sp R)} (f : Y ⟶ A) (g : A ⟶ B) (a : HO1 B.hom) :
    pO1 (f ≫ g) a = pO1 f (pO1 g a) := by
  unfold pO1
  exact ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.1 R R B.left A.left B.hom A.hom (RingHom.id R) g.left (ovw g) R Y.left Y.hom
    (RingHom.id R) f.left (ovw f) (RingHom.id R) (f ≫ g).left (ovw (f ≫ g)) (by simp)
    (fun _ => rfl)).1 a).symm

theorem pO1_id {R : Type} [CommRing R] {A : Over (Sp R)} (a : HO1 A.hom) : pO1 (𝟙 A) a = a :=
  (GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.2.2 R A).1 a

theorem pO1_unit_eq_zero {R : Type} [CommRing R] (a : HO1 (𝟙_ (Over (Sp R))).hom) : a = 0 := by
  haveI : IsAffine (𝟙_ (Over (Sp R))).left := by
    show IsAffine (Sp R)
    infer_instance
  exact (GlobalTheory.AbCoh.Vanish.main.1 R _ _ this).1.elim a 0

theorem primO1_of_axesO1 : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], AxesVanishingStructureSheafDegOne A → StructureSheafH1Primitive A := by
  intro R _ A _ hax x
  have key : ∀ j : A ⟶ A ⊗ A, pO1 (j ≫ μ[A]) x - pO1 (j ≫ fst A A) x - pO1 (j ≫ snd A A) x =
      pO1 j (pO1 μ[A] x - pO1 (fst A A) x - pO1 (snd A A) x) := by
    intro j
    rw [map_sub, map_sub, pO1_comp, pO1_comp, pO1_comp]
  have hη : pO1 (toUnit A ≫ η[A]) x = 0 := by
    rw [pO1_comp, pO1_unit_eq_zero (pO1 η[A] x), map_zero]
  have h := hax (pO1 μ[A] x - pO1 (fst A A) x - pO1 (snd A A) x)
    (by
      rw [← key, lift_comp_one_right, lift_fst, lift_snd, pO1_id, hη]
      simp)
    (by
      rw [← key, lift_comp_one_left, lift_fst, lift_snd, pO1_id, hη]
      simp)
  rw [sub_sub, sub_eq_zero] at h
  exact h

end GlobalTheory.AbCoh.PrimLift
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

def untwist {Γ W : Type} [Group Γ] [AddCommGroup W] [Module ℂ W] (ρ' : Representation ℂ Γ W) (χ : Γ →* ℂˣ) :
    Representation ℂ Γ W where
  toFun g := (((χ g)⁻¹ : ℂˣ) : ℂ) • ρ' g
  map_one' := by simp
  map_mul' g h := by
    ext v
    simp only [map_mul, mul_inv_rev, Units.val_mul, LinearMap.smul_apply, Module.End.mul_apply,
      LinearMap.map_smul, smul_smul]
    ring_nf

theorem untwist_apply {Γ W : Type} [Group Γ] [AddCommGroup W] [Module ℂ W] (ρ' : Representation ℂ Γ W)
    (χ : Γ →* ℂˣ) (g : Γ) (w : W) : untwist ρ' χ g w = (((χ g)⁻¹ : ℂˣ) : ℂ) • ρ' g w := rfl

theorem embReg_count_of_ranks : ∀ (K Γ R W : Type) [Field K] [Algebra K ℂ] [Group Γ] [Finite Γ] [CommRing R] [Algebra K R] (act : Γ →* (R →ₐ[K] R)) (Hb H : Subgroup Γ) [Fintype Hb] [DecidableEq Hb] [Fintype H] [DecidableEq H] (u0 u : R), (Matrix.of fun h g : Hb => act ((h : Γ) * g) u0).det ∈ nonZeroDivisors R → (Matrix.of fun h g : H => act ((h : Γ) * g) u).det ∈ nonZeroDivisors R → ∀ (Vm V V1 V2 : Submodule K R) [FiniteDimensional K V] [FiniteDimensional K V2] (ρ : Representation K Γ V), (∀ g x, (ρ g x : R) = act g x) → (∀ h : Hb, ∀ x ∈ Vm, x * act h u0 ∈ V) → (∀ h : H, ∀ x ∈ V, x * act h u ∈ V1) → (∀ h : H, ∀ x ∈ V1, act h x ∈ V1) → (∀ h : H, ∀ x ∈ V1, x * act h u ∈ V2) → ∀ c : ℝ, 0 ≤ c → (finrank K V2 : ℝ) ≤ c * finrank K Vm → ∀ [AddCommGroup W] [Module K W] [Module ℂ W] [IsScalarTower K ℂ W] (f : V →ₗ[K] W), IsBaseChange ℂ f → ∀ (ρ' : Representation ℂ Γ W) (χ : Γ →* ℂˣ), (∀ g v, ρ' g (f v) = ((χ g : ℂˣ) : ℂ) • f (ρ g v)) → ∀ lam : Hb →* ℂˣ, ∃ n : ℕ, EmbReg ρ' H n ∧ (n : ℝ) * Nat.card H ≤ c * Nat.card Hb * finrank ℂ (eig ρ' Hb lam) := by
  intro K Γ R W _ _ _ _ _ _ act Hb H _ _ _ _ u0 u hu0 hu Vm V V1 V2 _ _ ρ hρ hVm hV hV1 hV2 c hc hcr _ _ _ _ f hf ρ' χ hρ' lam
  obtain ⟨n, hn, hnle⟩ := GlobalTheory.T.embedsInRegularRepresentationCopies_of_groupDeterminant K Γ R act H u hu V V1 V2 ρ hρ hV hV1 hV2
  have hf'' : ∀ g v, untwist ρ' χ g (f v) = f (ρ g v) := by
    intro g v
    rw [untwist_apply, hρ', smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  have hn'' : EmbReg (untwist ρ' χ) H n :=
    embReg_of_isBaseChange K ℂ Γ V W f hf ρ (untwist ρ' χ) hf'' H n hn
  have hn' : EmbReg ρ' H n := by
    refine GlobalTheory.T.embedsInRegularRepresentationCopies_of_characterTwist ℂ Γ W (untwist ρ' χ) ρ' χ ?_ H n hn''
    intro g v
    rw [untwist_apply, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  let lam' : Hb →* ℂˣ := lam * (χ.comp Hb.subtype)⁻¹
  have heig : eig ρ' Hb lam = eig (untwist ρ' χ) Hb lam' := by
    ext v
    rw [mem_eig, mem_eig]
    refine forall_congr' fun h => ?_
    rw [untwist_apply]
    simp only [lam', MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
      Units.val_mul]
    constructor
    · intro e; rw [e, smul_smul, mul_comm]
    · intro e
      have := congrArg (fun w => ((χ (h : Γ) : ℂˣ) : ℂ) • w) e
      simp only [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul] at this
      rw [this]; congr 1
      rw [mul_left_comm, mul_inv_cancel, mul_one]
  have hlow := GlobalTheory.T.finrank_le_card_mul_finrank_characterSpace_baseChange K ℂ Γ R W act Hb u0 hu0 Vm V ρ hρ hVm f hf (untwist ρ' χ) hf'' lam'
  rw [← heig] at hlow
  refine ⟨n, hn', ?_⟩
  have h1 : ((n * Nat.card H : ℕ) : ℝ) ≤ finrank K V2 := by exact_mod_cast hnle
  have h2 : (finrank K Vm : ℝ) ≤ Nat.card Hb * finrank ℂ (eig ρ' Hb lam) := by exact_mod_cast hlow
  push_cast at h1
  calc (n : ℝ) * Nat.card H ≤ finrank K V2 := h1
    _ ≤ c * finrank K Vm := hcr
    _ ≤ c * (Nat.card Hb * finrank ℂ (eig ρ' Hb lam)) := mul_le_mul_of_nonneg_left h2 hc
    _ = c * Nat.card Hb * finrank ℂ (eig ρ' Hb lam) := by ring

end GlobalTheory.BadCount
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset


theorem _root_.GlobalTheory.T.cech_h2_pullback_refinement_compat : ∀ {R' R'' : Type} [CommRing R'] [CommRing R''] {X' X'' : Scheme.{0}} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R' →+* R''} {ψ : X'' ⟶ X'} (w : ψ ≫ s' = s'' ≫ spMap σ) {κ : Type} [LinearOrder κ] (D' : κ → X'.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D' i)) (D'' : κ → X''.Opens) (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D'' i)) (hle : ∀ i, D'' i ≤ ψ ⁻¹ᵁ D' i) (y : HO2 s'), (CoefMap.restrict (OAff s'') (cov_mono D'' hD'').functor.op).pull2 (pullHO2 w y) = (pullCoef w D' hD' D'' hD'' hle).pull2 ((CoefMap.restrict (OAff s') (cov_mono D' hD').functor.op).pull2 y) := by
  first | exact @GlobalTheory.CechPoset.restrict_pull2_pullHO2 | exact GlobalTheory.CechPoset.restrict_pull2_pullHO2 | (intros; apply GlobalTheory.CechPoset.restrict_pull2_pullHO2 <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

theorem _root_.GlobalTheory.T.surjective_pullHO2_of_pullHO1 : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ), Function.Surjective (pullHO1 h) → WedgeO (OAff s') → Function.Surjective (pullHO2 h) := by
  first | exact @GlobalTheory.AbCoh.pullHO2_surjective_of_wedge | exact GlobalTheory.AbCoh.pullHO2_surjective_of_wedge | (intros; apply GlobalTheory.AbCoh.pullHO2_surjective_of_wedge <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem compatibleGlobalOneForms_finite_projective : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    HasFrame F → CohomZeroIsConstants F → Module.Finite R (Glob1 F) ∧ Module.Projective R (Glob1 F) := by
  intro R _ C _ F hF h0
  obtain ⟨n, ⟨Φ⟩⟩ := hF
  obtain ⟨l, -, hl⟩ := GlobalTheory.T.globalOneFormFrame_coordinates_constant R C F h0 n Φ
  let L : Glob1 F →ₗ[R] (Fin n → R) := LinearMap.pi l
  let S : (Fin n → R) →ₗ[R] Glob1 F := Fintype.linearCombination R Φ.w
  have hSL : S.comp L = LinearMap.id := by
    refine LinearMap.ext fun w ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.id_apply, S, L, Fintype.linearCombination_apply, LinearMap.pi_apply]
    exact (hl w).symm
  have hsurj : Function.Surjective S := fun w ↦ ⟨L w, by
    simpa using LinearMap.congr_fun hSL w⟩
  exact ⟨Module.Finite.of_surjective S hsurj, Module.Projective.of_split L S hSL⟩

end GlobalTheory.AbCoh
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AbCoh

theorem hyp2_eq_sum_cup_of_fn_exact : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ hc : Closed1 F = ⊤, Function.Surjective (toO F) → ∀ c : cechDeRhamTotalCocyclesTwo F, (∃ f, d1 F f = c.1.1) → ∃ (n : ℕ) (a : Fin n → Hyp1 F) (w : Fin n → Glob1 F), Hyp2.mk F c = ∑ k, cupHyp F (a k) (clAll F hc (w k)) := by
  intro R _ C _ F hfr h0 hc hs c ⟨f, hf⟩
  obtain ⟨m, ⟨fr⟩⟩ := hfr
  have hcl : ∀ (w : Glob1 F) (T : C), dOne R _ (w.1 T) = 0 := fun w T ↦
    (show w ∈ Closed1 F by rw [hc]; trivial) T
  have hclAll : ∀ w : Glob1 F, clAll F hc w = Hyp1.mk F ⟨(0, w.1), mem_cechDeRhamTotalCocyclesOne_iff.2 ⟨zero_mem _,
      fun T T' φ ↦ by simpa using w.2 φ, fun T ↦ hcl w T⟩⟩ := fun w ↦ rfl
  set c' : cechDeRhamTotalCocyclesTwo F := c - ⟨dTot1 F (f, 0), dTot1_mem F _⟩ with hc'
  have hmk : Hyp2.mk F c = Hyp2.mk F c' := by
    rw [hc', map_sub, (Hyp2.mk_eq_zero (c := ⟨dTot1 F (f, 0), dTot1_mem F _⟩)).2 ⟨(f, 0), rfl⟩, sub_zero]
  have hz : ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''), c'.1.1 T T' T'' φ ψ = 0 := by
    intro T T' T'' φ ψ
    change c.1.1 T T' T'' φ ψ - d1 F f T T' T'' φ ψ = 0
    rw [hf, sub_self]
  set a : A1 F := c'.1.2.1 with ha
  have hacoc : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), a T T'' (φ ≫ ψ) = p1 F ψ (a T T' φ) + a T' T'' ψ := by
    intro T T' T'' φ ψ
    rw [ha, cechDeRhamTotalCocyclesTwo.one c' φ ψ, hz, map_zero, add_zero]
  let g : Fin m → Z1 F := fun i ↦ ⟨fun T T' φ ↦ fr.δ i T' (a T T' φ), fun T T' T'' φ ψ ↦ by
    simp only [hacoc φ ψ, map_add (f := _), fr.nat]⟩
  have hE : ∀ i, ∃ e : cechDeRhamTotalCocyclesOne F, e.1.1 = (g i).1 := by
    intro i
    obtain ⟨x, hx⟩ := hs (H1.mk F (g i))
    obtain ⟨e0, rfl⟩ := Hyp1.mk_surjective F x
    rw [toO_mk, H1.mk_eq_mk] at hx
    obtain ⟨h, hh⟩ := hx
    refine ⟨e0 - ⟨dTot0 F h, dTot0_mem F h⟩, ?_⟩
    change e0.1.1 - d0 F h = (g i).1
    rw [hh]; change e0.1.1 - (e0.1.1 - (g i).1) = (g i).1; abel
  choose e he using hE
  let η' : W0 F 2 := fun T ↦ c'.1.2.2 T - ∑ i, wedge R _ ((e i).1.2 T) ((fr.w i).1 T)
  have hη' : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), η' T' = pOm F 2 φ (η' T) := by
    intro T T' φ
    have hd : dOne R _ (a T T' φ) = ∑ i, wedge R _ (D R _ (fr.δ i T' (a T T' φ))) ((fr.w i).1 T') := by
      conv_lhs => rw [fr.sum T' (a T T' φ)]

      simp [map_sum, dOne_smul, hcl]
    have hw : ∀ i, (fr.w i).1 T' = p1 F φ ((fr.w i).1 T) := fun i ↦ (fr.w i).2 φ
    have he' : ∀ i, (e i).1.2 T' = p1 F φ ((e i).1.2 T) + D R _ (fr.δ i T' (a T T' φ)) := by
      intro i; rw [cechDeRhamTotalCocyclesOne.conn (e i) φ, he]

    simp only [η', map_sub, map_sum, pOm_wedge]
    rw [cechDeRhamTotalCocyclesTwo.two c' φ, ← ha, hd]
    simp only [he', map_add (f := _), LinearMap.add_apply, Finset.sum_add_distrib, ← hw]
    abel
  obtain ⟨n, u, v, huv⟩ := GlobalTheory.T.globalTwoForm_eq_sumWedgeGlobalOneForms R C F ⟨m, ⟨fr⟩⟩ h0 η' hη'
  refine ⟨m + n, Fin.append (fun i ↦ Hyp1.mk F (e i)) (fun k ↦ clAll F hc (u k)), Fin.append fr.w v, ?_⟩
  rw [Fin.sum_univ_add]

  simp only [Fin.append_left, Fin.append_right, hclAll, cupHyp_mk, ← map_sum, ← map_add (f := _), hmk]
  congr 1
  apply Subtype.ext
  refine Tot2.ext (fun T T' T'' φ ψ ↦ ?_) (fun T T' φ ↦ ?_) (fun T ↦ ?_)
  · simp only [Submodule.coe_add, Submodule.coe_sum, Prod.fst_add, Prod.fst_sum, Pi.add_apply,
      Finset.sum_apply, coe_cupZZ, cupTot_apply, hz, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  · simp only [Submodule.coe_add, Submodule.coe_sum, Prod.snd_add, Prod.snd_sum, Prod.fst_add, Prod.fst_sum,
      Pi.add_apply, Finset.sum_apply, coe_cupZZ, cupTot_a, Pi.zero_apply, zero_smul, sub_zero,
      Finset.sum_const_zero, add_zero, he]
    exact fr.sum T' (a T T' φ)
  · have := congrFun huv T
    simp only [η', wsum] at this
    simp only [Submodule.coe_add, Submodule.coe_sum, Prod.snd_add, Prod.snd_sum, Pi.add_apply,
      Finset.sum_apply, coe_cupZZ, cupTot_η]
    rw [← this]; abel
end GlobalTheory.AbCoh
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem isBaseChange_glob1 (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (hF : HasFrame F) (h0 : CohomZeroIsConstants F) (T : C) (e : Glob1 F →ₗ[R] Ω[F.obj T⁄R]) (he : ∀ w, e w = w.1 T) :
    IsBaseChange (F.obj T) e := by
  obtain ⟨n, ⟨Φ⟩⟩ := hF
  obtain ⟨l, hl, hsum⟩ := GlobalTheory.T.globalOneFormFrame_coordinates_constant R C F h0 n Φ
  let S := F.obj T
  let fwd : S ⊗[R] Glob1 F →ₗ[S] Ω[F.obj T⁄R] := e.liftBaseChange S
  let inv : Ω[F.obj T⁄R] →ₗ[S] S ⊗[R] Glob1 F :=
    ∑ i, (Φ.δ i T).smulRight ((1 : S) ⊗ₜ[R] Φ.w i)
  have hinv : ∀ ω, inv ω = ∑ i, Φ.δ i T ω ⊗ₜ[R] Φ.w i := by
    intro ω
    simp only [inv, LinearMap.sum_apply, LinearMap.smulRight_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  have h1 : ∀ ω, fwd (inv ω) = ω := by
    intro ω

    rw [hinv, map_sum]
    simp only [fwd, LinearMap.liftBaseChange_tmul, he]
    exact (Φ.sum T ω).symm
  have h2 : ∀ x, inv (fwd x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
    | tmul b w =>
      have : ∑ i, Φ.δ i T (w.1 T) ⊗ₜ[R] Φ.w i = (1 : S) ⊗ₜ[R] w := by
        conv_rhs => rw [hsum w]
        rw [TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hl, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
      show inv (e.liftBaseChange S (b ⊗ₜ[R] w)) = _
      rw [LinearMap.liftBaseChange_tmul, map_smul, he, hinv, this, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  exact IsBaseChange.of_equiv (LinearEquiv.ofLinear fwd inv (LinearMap.ext h1) (LinearMap.ext h2))
    (fun w ↦ by simp [fwd])

end GlobalTheory.AbCoh
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem exists_obRel_of_dRel : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ (x : GlobalTheory.CatCoh.H1 F) (n : ℕ) (y : Fin n → GlobalTheory.CatCoh.H1 F) (w : Fin n → Glob1 F), DRel F x y w → (∀ l : Glob1 F →ₗ[R] R, ∑ k, l (w k) • y k = 0) → ∃ (m : ℕ) (u v : Fin m → Glob1 F), ObRel F x u v := by
  intro R _ C _ F hF h0 x n y w hD hy
  obtain ⟨N, ⟨Φ⟩⟩ := hF
  obtain ⟨l, -, hl2⟩ := GlobalTheory.T.globalOneFormFrame_coordinates_constant R C F h0 N Φ
  obtain ⟨f, g, ω, hf, hg, hfD⟩ := hD
  have hcl : ∀ i, ∃ b : C0 F, d0 F b = (∑ k, l i (w k) • g k).1 := fun i ↦ by
    refine H1.mk_eq_zero.1 ?_

    simp only [map_sum, map_smul, hg]
    exact hy (l i)
  choose b hb using hcl
  have hb' : ∀ i ⦃T T' : C⦄ (φ : T ⟶ T'),
      b i T' - mp F φ (b i T) = ∑ k, l i (w k) • (g k).1 T T' φ := fun i T T' φ ↦ by
    have := congrFun (congrFun (congrFun (hb i) T) T') φ
    rw [amitsur_d0_apply] at this
    rw [this, Submodule.coe_sum]
    simp only [Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply]
  have hw : ∀ k (T : C), (w k).1 T = ∑ i, l i (w k) • (Φ.w i).1 T := fun k T ↦ by
    have := congrArg (fun v : Glob1 F ↦ v.1 T) (hl2 (w k))
    simpa [Submodule.coe_sum, Finset.sum_apply] using this
  have hsum : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), ∑ k, (g k).1 T T' φ • (w k).1 T' =
      ∑ i, (b i T' - mp F φ (b i T)) • (Φ.w i).1 T' := fun T T' φ ↦ by
    simp only [hb', hw, Finset.smul_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
    rw [smul_comm, smul_assoc]
  let ω' : A0 F := fun T ↦ ω T + ∑ i, b i T • (Φ.w i).1 T
  have hconn : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), ω' T' = p1 F φ (ω' T) + D R (F.obj T') (f.1 T T' φ) := by
    intro T T' φ
    rw [hfD φ, hsum φ]

    simp only [ω', map_add (f := _), map_sum, oneFormsMapOfFunctorMorphism_smul, ← (Φ.w _).2 φ, sub_smul, Finset.sum_sub_distrib]
    abel
  have hglob : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'),
      dOne R (F.obj T') (ω' T') = pOm F 2 φ (dOne R (F.obj T) (ω' T)) := by
    intro T T' φ
    rw [hconn φ, map_add (f := _), dOne_D, add_zero, pOm_dOne]
  obtain ⟨m, u, v, hζ⟩ := GlobalTheory.T.globalTwoForm_eq_sumWedgeGlobalOneForms R C F ⟨N, ⟨Φ⟩⟩ h0 (fun T ↦ dOne R (F.obj T) (ω' T)) hglob
  exact ⟨m, u, v, f, ω', hf, hconn, fun T ↦ congrFun hζ T⟩

end GlobalTheory.AbCoh
end
