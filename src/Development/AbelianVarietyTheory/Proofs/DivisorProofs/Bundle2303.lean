module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1106
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2282
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2138
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle069
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle081
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1110
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle094
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle146
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle052
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVR
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle109
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1572
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1630
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1056
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle002
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.HTIso

theorem one_comp_monHom {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [GrpObj A'] (f : A ⟶ A') [IsMonHom f] :
    (1 : A ⟶ A) ≫ f = 1 := by
  rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]

theorem comp_one' {S : Scheme.{0}} {A A' : Over S} [GrpObj A'] (f : A ⟶ A') : f ≫ (1 : A' ⟶ A') = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, comp_toUnit]

theorem pull_birig : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (f : A ⟶ A'), IsMonHom f → ∀ P : LB (G2 A').left, P.IsLB →
    (∃ t : (P.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) →
    LBIso P (P.pull (lift (snd A' A') (fst A' A')).left) →
    (P.pull (lift (fst A A ≫ f) (snd A A ≫ f)).left).IsLB ∧
    (∃ t : ((P.pull (lift (fst A A ≫ f) (snd A A ≫ f)).left).pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧
    (∃ t : ((P.pull (lift (fst A A ≫ f) (snd A A ≫ f)).left).pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧
    LBIso (P.pull (lift (fst A A ≫ f) (snd A A ≫ f)).left)
      ((P.pull (lift (fst A A ≫ f) (snd A A ≫ f)).left).pull (lift (snd A A) (fst A A)).left) := by
  intro S A A' _ _ _ _ f hf P hP ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ hs
  haveI := hf
  set φ₂ := (lift (fst A A ≫ f) (snd A A ≫ f)).left with hφ₂
  have hP₂ : (P.pull φ₂).IsLB := pull_isLB hP _

  have triv : ∀ (l : A ⟶ G2 A) (l' : A' ⟶ G2 A'), l ≫ lift (fst A A ≫ f) (snd A A ≫ f) = f ≫ l' →
      ∀ t : (P.pull l'.left).Gen, t.IsGen → ∃ s : ((P.pull φ₂).pull l.left).Gen, s.IsGen := by
    intro l l' hl t ht
    have e₁ : LBIso (P.pull (f.left ≫ l'.left)) ((P.pull l'.left).pull f.left) :=
      GlobalTheory.GenSpread.lbIso_pull_pull hP f.left rfl
    have e₂ : LBIso (P.pull (f.left ≫ l'.left)) ((P.pull φ₂).pull l.left) :=
      GlobalTheory.GenSpread.lbIso_pull_pull hP l.left (by rw [hφ₂, ← Over.comp_left, ← Over.comp_left, hl])
    obtain ⟨s, hs⟩ := GlobalTheory.RigidTranslate.gen_of_lbIso (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) e₁.symm
      (pullGenLB t f.left) (pullGenLB_isGen ht f.left)
    exact GlobalTheory.RigidTranslate.gen_of_lbIso (pull_isLB hP _) (pull_isLB hP₂ _) e₂ s hs
  refine ⟨hP₂, triv _ _ ?_ t₁ ht₁, triv _ _ ?_ t₂ ht₂, ?_⟩
  · apply CartesianMonoidalCategory.hom_ext <;> simp [one_comp_monHom, comp_one']
  · apply CartesianMonoidalCategory.hom_ext <;> simp [one_comp_monHom, comp_one']
  · have eq : (lift (snd A A) (fst A A)).left ≫ φ₂ = φ₂ ≫ (lift (snd A' A') (fst A' A')).left := by
      rw [hφ₂, ← Over.comp_left, ← Over.comp_left]
      congr 1
      apply CartesianMonoidalCategory.hom_ext <;> simp
    have e₁ : LBIso (P.pull φ₂) ((P.pull (lift (snd A' A') (fst A' A')).left).pull φ₂) :=
      GlobalTheory.GenSpread.lbIso_pullback hs φ₂
    have e₂ : LBIso (P.pull (φ₂ ≫ (lift (snd A' A') (fst A' A')).left))
        ((P.pull (lift (snd A' A') (fst A' A')).left).pull φ₂) :=
      GlobalTheory.GenSpread.lbIso_pull_pull hP φ₂ rfl
    have e₃ : LBIso (P.pull (φ₂ ≫ (lift (snd A' A') (fst A' A')).left)) ((P.pull φ₂).pull (lift (snd A A) (fst A A)).left) :=
      GlobalTheory.GenSpread.lbIso_pull_pull hP _ eq.symm
    exact LBIso.trans hP₂ (pull_isLB (pull_isLB hP _) _) (pull_isLB hP₂ _) e₁
      (LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB hP₂ _) e₂.symm e₃)

theorem weil_pull_iso : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (F : A ≅ A'), IsMonHom F.hom → ∀ P : LB (G2 A').left, P.IsLB → ∀ (T : Over S) (k : ℤ) (x y : T ⟶ A)
    (c : Γ(T.left, ⊤)ˣ), Out.WeilIs A' (P.pull (lift (𝟙 A') (𝟙 A')).left) k (x ≫ F.hom) (y ≫ F.hom) c →
    Out.WeilIs A ((P.pull (lift (fst A A ≫ F.hom) (snd A A ≫ F.hom)).left).pull (lift (𝟙 A) (𝟙 A)).left) k x y c := by
  intro S A A' _ _ _ _ F hF P hP T k x y c H
  haveI := hF
  set φ₂ := (lift (fst A A ≫ F.hom) (snd A A ≫ F.hom)).left with hφ₂
  have eq : (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ = F.hom.left ≫ (lift (𝟙 A') (𝟙 A')).left := by
    rw [hφ₂, ← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have e₁ : LBIso (P.pull ((lift (𝟙 A) (𝟙 A)).left ≫ φ₂)) ((P.pull φ₂).pull (lift (𝟙 A) (𝟙 A)).left) :=
    GlobalTheory.GenSpread.lbIso_pull_pull hP _ rfl
  have e₂ : LBIso (P.pull ((lift (𝟙 A) (𝟙 A)).left ≫ φ₂)) ((P.pull (lift (𝟙 A') (𝟙 A')).left).pull F.hom.left) :=
    GlobalTheory.GenSpread.lbIso_pull_pull hP _ eq
  have iso := LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) e₁.symm e₂
  let x₀ : Over.mk (T.hom ≫ 𝟙 S) ⟶ A' := Over.homMk (x.left ≫ F.hom.left) (by simp)
  let y₀ : Over.mk (T.hom ≫ 𝟙 S) ⟶ A' := Over.homMk (y.left ≫ F.hom.left) (by simp)
  refine (GlobalTheory.weilIs_iff_of_isGrpPullback_comm S S A' A (𝟙 S) F.hom.left _ _ (pull_isLB hP _)
    (pull_isLB (pull_isLB hP _) _) (isGrpPullback_of_iso F) iso T k x y x₀ y₀ c rfl rfl).2 ?_
  exact GlobalTheory.UnifPoint.weilIs_congr (Category.comp_id _).symm rfl rfl H

theorem nonempty_objMap_of_markedIsom : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o o' : Obj b N (spMap σ)) h hL h' hL' (D' D'' : PLat D.O D.inv) t t' Q Q' e e' (w : D'.La ≃ₗ[D.O] D''.La) (u : (Fin D.g → ℂ) ≃ₗ[ℂ] (Fin D.g → ℂ)), 0 < N → UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e → UnifAt (o'.fam h' hL') σ ρ N D'' t' Q' (𝟙 _) e' → IsMarkedIsom N D' D'' t t' w → (∀ x, Q' (w x) = u (Q x)) → Nonempty (ObjMap o o' (𝟙 _)) := by
  rintro p _ D R _ b N σ ρ o o' h hL h' hL' D' D'' t t' Q Q' e e' w u hN0
    ⟨-, hP, he, hk, hl, hw, hη⟩ ⟨-, hP', he', hk', hl', hw', hη'⟩ ⟨hiso, hmark⟩ hu

  have k1 : ∀ z, e z = 1 → e' (u z) = 1 := by
    intro z hz
    obtain ⟨x, rfl⟩ := (hk z).1 hz
    exact (hk' _).2 ⟨w x, hu x⟩
  have k2 : ∀ z, e' z = 1 → e (u.symm z) = 1 := by
    intro z hz
    obtain ⟨x, rfl⟩ := (hk' z).1 hz
    refine (hk _).2 ⟨w.symm x, ?_⟩
    apply u.injective
    rw [u.apply_symm_apply, ← hu, w.apply_symm_apply]
  obtain ⟨f, ⟨hf, hfe⟩, -⟩ := GlobalTheory.T.existsUnique_isMonHom_of_linear_map_kernels o.A o'.A D.g D.g o.ab o'.ab h h' e e' u.toLinearMap he he' k1
  obtain ⟨f', ⟨hf', hfe'⟩, -⟩ := GlobalTheory.T.existsUnique_isMonHom_of_linear_map_kernels o'.A o.A D.g D.g o'.ab o.ab h' h e' e u.symm.toLinearMap he' he k2
  obtain ⟨f₀, -, uid⟩ := GlobalTheory.T.existsUnique_isMonHom_of_linear_map_kernels o.A o.A D.g D.g o.ab o.ab h h e e LinearMap.id he he (fun z hz => hz)
  obtain ⟨f₀', -, uid'⟩ := GlobalTheory.T.existsUnique_isMonHom_of_linear_map_kernels o'.A o'.A D.g D.g o'.ab o'.ab h' h' e' e' LinearMap.id he' he' (fun z hz => hz)
  have hfe2 : ∀ z, e' (u z) = e z ≫ f := hfe
  have hfe2' : ∀ z, e (u.symm z) = e' z ≫ f' := hfe'
  haveI := hf
  haveI := hf'
  have c1 : f ≫ f' = 𝟙 _ := by
    rw [uid (f ≫ f') ⟨inferInstance, fun z => ?_⟩, uid (𝟙 _) ⟨inferInstance, fun z => (Category.comp_id _).symm⟩]
    refine Eq.trans ?_ (Category.assoc (e z) f f')
    rw [← hfe2]
    exact (by rw [u.symm_apply_apply]; rfl : e (LinearMap.id z) = e (u.symm (u z))).trans (hfe2' (u z))
  have c2 : f' ≫ f = 𝟙 _ := by
    rw [uid' (f' ≫ f) ⟨inferInstance, fun z => ?_⟩, uid' (𝟙 _) ⟨inferInstance, fun z => (Category.comp_id _).symm⟩]
    refine Eq.trans ?_ (Category.assoc (e' z) f' f)
    rw [← hfe2']
    exact (by rw [u.apply_symm_apply]; rfl : e' (LinearMap.id z) = e' (u (u.symm z))).trans (hfe2 (u.symm z))
  let F : o.A ≅ o'.A := ⟨f, f', c1, c2⟩
  haveI : IsMonHom F.hom := hf

  have hcomm : ∀ (c : D.O) z, u (ρ c *ᵥ z) = ρ c *ᵥ u z := by
    intro c
    have := LinearMap.ext_on_range (R := ℝ) (v := fun x => Q x) hP.2.2.2.1
      (f := (u.toLinearMap ∘ₗ Matrix.toLin' (ρ c)).restrictScalars ℝ)
      (g := (Matrix.toLin' (ρ c) ∘ₗ u.toLinearMap).restrictScalars ℝ) (fun x => by
        simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply, Matrix.toLin'_apply, LinearEquiv.coe_coe]
        rw [← hP.1, ← hu, ← hu, w.map_smul, hP'.1])
    intro z
    simpa using LinearMap.congr_fun this z
  have hact : ∀ c, o.act.act c ≫ f = f ≫ o'.act.act c := by
    intro c
    haveI := o.act.hom c
    haveI := o'.act.hom c
    obtain ⟨fa, -, ua⟩ := GlobalTheory.T.existsUnique_isMonHom_of_linear_map_kernels o.A o'.A D.g D.g o.ab o'.ab h h' e e'
      (u.toLinearMap ∘ₗ Matrix.toLin' (ρ c)) he he' (fun z hz => by
        obtain ⟨x, rfl⟩ := (hk z).1 hz
        simp only [LinearMap.comp_apply, Matrix.toLin'_apply, LinearEquiv.coe_coe]
        rw [← hP.1]
        exact k1 _ ((hk _).2 ⟨_, rfl⟩))
    rw [ua (o.act.act c ≫ f) ⟨inferInstance, fun z => ?_⟩, ua (f ≫ o'.act.act c) ⟨inferInstance, fun z => ?_⟩]
    · simp only [LinearMap.comp_apply, Matrix.toLin'_apply, LinearEquiv.coe_coe]
      refine Eq.trans ?_ (Category.assoc (e z) f (o'.act.act c))
      rw [← hfe2, hcomm]
      exact hl' c (u z)
    · simp only [LinearMap.comp_apply, Matrix.toLin'_apply, LinearEquiv.coe_coe]
      refine Eq.trans ?_ (Category.assoc (e z) (o.act.act c) f)
      rw [hfe2]
      exact congrArg (· ≫ f) (hl c z)
  have hT : (toUnit (Over.mk (𝟙 (Sp ℂ)))).left = 𝟙 _ := by
    simpa using Over.w (toUnit (Over.mk (𝟙 (Sp ℂ))))
  have heta : ∀ y, (o.eta y).left ≫ f.left = 𝟙 _ ≫ (o'.eta y).left := by
    intro y
    obtain ⟨e₀, he₀⟩ := hmark y
    have hN : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
    have hη2 : toUnit (Over.mk (𝟙 (Sp ℂ))) ≫ o.eta y = e ((N : ℂ)⁻¹ • Q (t y)) := hη y
    have hη2' : toUnit (Over.mk (𝟙 (Sp ℂ))) ≫ o'.eta y = e' ((N : ℂ)⁻¹ • Q' (t' y)) := hη' y
    have a1 : (toUnit (Over.mk (𝟙 (Sp ℂ))) ≫ o.eta y) ≫ f = toUnit (Over.mk (𝟙 (Sp ℂ))) ≫ o'.eta y := by
      refine (congrArg (· ≫ f) hη2).trans ((hfe2 _).symm.trans (Eq.trans ?_ hη2'.symm))
      have hz : (N : ℂ)⁻¹ • N • Q' e₀ = Q' e₀ := by
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN, one_smul]
      rw [map_smul, ← hu, he₀, map_add (f := _), map_nsmul, smul_add, hz, he'.1, (hk' (Q' e₀)).2 ⟨e₀, rfl⟩, _root_.mul_one]
    have a2 := congrArg (fun q => q.left) a1
    simp only [Over.comp_left, hT, Category.id_comp] at a2
    rw [Category.id_comp]
    exact a2
  obtain ⟨B1, B2, B3, B4⟩ := pull_birig (Sp ℂ) o.A o'.A f hf o'.P o'.isLB o'.rig₁ o'.rig₂ o'.symm
  have ew : ∀ (k : ℕ) a, e' ((k : ℂ)⁻¹ • Q' (w a)) = e ((k : ℂ)⁻¹ • Q a) ≫ f := by
    intro k a
    rw [hu, ← u.map_smul]
    exact hfe2 _
  have pol := GlobalTheory.T.birigidified_bundle_iso_of_weil_pairing_eq o.A D.g o.ab h o.P (o'.P.pull (lift (fst o.A o.A ≫ f) (snd o.A o.A ≫ f)).left)
    o.isLB o.rig₁ o.rig₂ o.symm B1 B2 B3 B4 e D'.La Q D'.EF he hP.2.1 hk hw (fun k a a₂ c hk0 hc => by
      have W' := hw' k (w a) (w a₂) c hk0 (by rw [hiso]; exact hc)
      rw [ew, ew] at W'
      exact weil_pull_iso (Sp ℂ) o.A o'.A F inferInstance o'.P o'.isLB _ k _ _ _ W')
  exact ⟨{ φ := f.left
           φ₂ := (lift (fst o.A o.A ≫ f) (snd o.A o.A ≫ f)).left
           cart := isGrpPullback_of_iso F
           sq := ⟨by rw [← Over.comp_left, lift_fst, Over.comp_left], by rw [← Over.comp_left, lift_snd, Over.comp_left]⟩
           act := fun c => by rw [← Over.comp_left, hact c, Over.comp_left]
           pol := pol
           eta := heta }⟩

end GlobalTheory.HTIso
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistFlat
open GlobalTheory.StabFlatLocal GlobalTheory.StabFlat GlobalTheory.UU

theorem flat_of_isFinite_twist : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V]
    (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ L : LB B.left, L.IsLB →
    (∃ t : LB.Gen (Theta B L), t.IsGen) → ∀ O : LB B.left, O.IsLB → (∃ u : LB.Gen (abelian₂ B O), u.IsGen) →
    ∀ (H : Over (Sp V)) (j : H ⟶ B), IsClosedImmersion j.left →
    (∀ (T : Over (Sp V)) (x : T ⟶ B), (∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι)) ↔
        ∃ y : T ⟶ H, y ≫ j = x) → IsFinite H.hom → Flat H.hom := by
  intro hG V _ _ _ B _ _ hB hp L hL hΘ O hO hu H j hj hH hf
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim V B hB
  rw [← Over.w j]
  refine GlobalTheory.T.flat_closedSubscheme_finite_over_localRing V B.left H.left B.hom j.left hj (by rw [Over.w j]; exact hf) fun h σ hσ hn => ?_
  have cl : ∀ (z : H.left) (p : Spec (B.left.presheaf.stalk (j.left h))),
      (IsLocalRing.maximalIdeal V).map σ ≤ p.asIdeal →
      j.left z = B.left.fromSpecStalk (j.left h) p → IsClosed ({j.left z} : Set B.left) := by
    intro z p hp e
    have hz : H.hom z = IsLocalRing.closedPoint V := by
      rw [← Over.w j, Scheme.Hom.comp_apply, e, ← Scheme.Hom.comp_apply, hσ]
      refine PrimeSpectrum.ext (Eq.symm ((IsLocalRing.maximalIdeal.isMaximal V).eq_of_le
        (PrimeSpectrum.isPrime _).ne_top ?_))
      exact Ideal.map_le_iff_le_comap.1 hp
    have := j.left.isClosedEmbedding.isClosedMap _ (isClosed_of_isFinite H.hom z hz)
    rwa [Set.image_singleton] at this
  have hm : (IsLocalRing.maximalIdeal V).map σ ≤ IsLocalRing.maximalIdeal _ :=
    Ideal.map_le_iff_le_comap.2 fun v hv => map_nonunit σ v hv
  obtain ⟨h₀, h₁, h₂, h₃⟩ := GlobalTheory.T.stalk_regular_flat_of_smooth V B.left B.hom g hg (j.left h)
    (cl h (IsLocalRing.closedPoint _) hm Scheme.fromSpecStalk_closedPoint.symm) σ hσ hn
  refine @exists_ideal hG V _ _ _ B _ _ hB hp g hg L O hL hO hΘ hu H j hH
    (B.left.presheaf.stalk (j.left h)) _ h₀ _
    (B.left.fromSpecStalk (j.left h)) σ hn h₁ h₂ h₃ (H.left.residueField h) _
    (j.left.stalkMap h ≫ H.left.residue h).hom
    (RingHom.isLocalHom_comp (IsLocalRing.residue (H.left.presheaf.stalk h)) (j.left.stalkMap h).hom) ⟨H.left.fromSpecResidueField h, ?_⟩ ?_
  · rw [Scheme.fromSpecResidueField, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Spec.map_comp_assoc]
    rfl
  · rintro K _ φ hφ ⟨y, hy⟩
    let p := Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint K)
    have hk : p.asIdeal = RingHom.ker φ := by
      show Ideal.comap φ (IsLocalRing.maximalIdeal K) = _
      rw [IsLocalRing.maximalIdeal_eq_bot, RingHom.ker_eq_comap_bot]
    have e : j.left (y (IsLocalRing.closedPoint K)) = B.left.fromSpecStalk (j.left h) p :=
      congrArg (fun q => q (IsLocalRing.closedPoint K)) hy
    have hc := cl _ p (hφ.trans hk.ge) e
    have hs : B.left.fromSpecStalk (j.left h) p ⤳ j.left h := by
      have : B.left.fromSpecStalk (j.left h) p ∈ Set.range (B.left.fromSpecStalk (j.left h)) := ⟨p, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have e' : j.left h = B.left.fromSpecStalk (j.left h) p := (hs.mem_closed hc e.symm).trans e
    have hp' : p = IsLocalRing.closedPoint _ := (B.left.fromSpecStalk (j.left h)).isEmbedding.injective
      (e'.symm.trans Scheme.fromSpecStalk_closedPoint.symm)
    rw [← hk, hp']
    rfl

end GlobalTheory.TwistFlat

namespace GlobalTheory.TwistFlat

theorem flat_local : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left,
    L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) (N : LB (A ⊗ T).left), Fam A N →
    ∀ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left →
    (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t) →
    ∀ (V : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] (φ : Sp V ⟶ T.left),
    IsFinite (pullback.snd (h ≫ snd A T).left φ) → Flat (pullback.snd (h ≫ snd A T).left φ) := by
  intro R _ A _ hA L hL ha T N hN H h hh hH V _ _ _ φ hfin
  have hB : IsAbelianScheme (bc A φ) := GlobalTheory.isAbelianScheme_pullback_obj _ A hA
  have : IsCommMonObj (bc A φ) := hB.comm
  have hP : IsProjBy (bc A φ).hom :=
    (GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ A L hA hL ha V (φ ≫ T.hom)
      _ (pullback.fst A.hom (φ ≫ T.hom)) (pullback.snd A.hom (φ ≫ T.hom)) (IsPullback.of_hasPullback _ _)).1
  have hL' : (L.pull (pullback.fst A.hom (φ ≫ T.hom))).IsLB := LB.isLB_pull hL _
  have hO : (twist A φ N).IsLB := pull_isLB hN.isLB _
  refine flat_of_isFinite_twist GlobalTheory.T.abelianScheme_laws_unconditional.1.globalFns V (bc A φ) hB hP _ hL'
    (GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy GlobalTheory.T.abelianScheme_laws_unconditional.1 _ _ hB hP _ hL') (twist A φ N) hO
    (GlobalTheory.T.lineBundleFamilyAtPoint_lambda_trivial A φ N hN) (ker A φ h) (kerι A φ h) (GlobalTheory.T.isClosedImmersion_fibreOverPointToBaseChange A φ h hh) (fun Y x => ?_) hfin
  rw [GlobalTheory.T.factors_fibreOverPoint_iff_factors_product A φ h Y x, ← hH, GlobalTheory.T.mumfordBundle_iso_family_iff_locally_trivial_translationDiff A T hA L hL N hN]
  exact forall_congr' fun p => exists_congr fun U => and_congr_right' (GlobalTheory.T.translationDifference_trivial_baseChange_iff_over_A A φ L hL N hN.isLB Y x U)

end GlobalTheory.TwistFlat

namespace GlobalTheory.TwistFlat

theorem isNoetherianRing_top (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) [IsAffine X]
    (f : X ⟶ Sp R) (hf : LocallyOfFiniteType f) : IsNoetherianRing Γ(X, ⊤) := by
  have h1 : (f.appTop).hom.FiniteType := (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).1 hf
  have : IsNoetherianRing Γ(Sp R, ⊤) :=
    isNoetherianRing_of_ringEquiv R (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  letI := (f.appTop).hom.toAlgebra
  have : Algebra.FiniteType Γ(Sp R, ⊤) Γ(X, ⊤) := h1
  exact Algebra.FiniteType.isNoetherianRing Γ(Sp R, ⊤) Γ(X, ⊤)

theorem flat_twisted_kernel : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ N : LB (A ⊗ T).left, Fam A N → ∀ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t) → IsFinite (h ≫ snd A T).left → Flat (h ≫ snd A T).left := by
  intro R _ _ A _ hA L hL ha T _ hT N hN H h hh hH hfin
  have : IsNoetherianRing Γ(T.left, ⊤) := isNoetherianRing_top R T.left T.hom hT
  let e := T.left.isoSpec
  let f := (h ≫ snd A T).left
  haveI : IsFinite f := hfin
  let H' : Over (Sp Γ(T.left, ⊤)) := Over.mk (f ≫ e.hom)
  have hfin' : IsFinite H'.hom := by
    show IsFinite (f ≫ e.hom)
    infer_instance
  have hflat : Flat (f ≫ e.hom) := by
    refine GlobalTheory.flat_of_isFinite_of_flat_localization_maximal Γ(T.left, ⊤) H' hfin' fun m _ => ?_
    let φ : Sp (Localization.AtPrime m) ⟶ T.left := spMap (algebraMap Γ(T.left, ⊤) (Localization.AtPrime m)) ≫ e.inv
    have hf : IsFinite (pullback.snd f φ) := MorphismProperty.of_isPullback (P := @IsFinite) (IsPullback.of_hasPullback f φ) hfin
    haveI := flat_local R A hA L hL ha T N hN H h hh hH (Localization.AtPrime m) φ hf
    have sq : IsPullback (pullback.fst f φ) (pullback.snd f φ) (f ≫ e.hom)
        (spMap (algebraMap Γ(T.left, ⊤) (Localization.AtPrime m))) :=
      (IsPullback.of_hasPullback f φ).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e (by simp) (by simp)
        (by simp) (by simp [φ])
    show Flat (pullback.snd (f ≫ e.hom) _)
    rw [← sq.isoPullback_inv_snd]
    infer_instance
  have hfe : f = (f ≫ e.hom) ≫ e.inv := by simp
  show Flat f
  rw [hfe]
  infer_instance

end GlobalTheory.TwistFlat
end
end

section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O

open scoped ContDiff

namespace GlobalTheory.Mean4O.ReadsProj

theorem hess_comb : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {ι : Type} [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ) (σ : k →+* ℂ) {D : ℕ} (c : AlgChart p σ D) {y : CxPts p σ}, y ∈ c.e.source → ∀ (i : (ArInt.comb L n).B.ι), y ∈ ptsIn p σ ((ArInt.comb L n).B.U i) → ∀ (m : ∀ l, (L l).B.ι), (∀ l, y ∈ ptsIn p σ ((L l).B.U (m l))) → c.hess ((ArInt.comb L n).φ σ) i y = ∑ l, ((n l : ℝ) : ℂ) • c.hess ((L l).φ σ) (m l) y := by
  classical
  intro k _ X p ι _ L n σ D c y hy i hi m hm
  obtain ⟨i₀, hi₀, e₀⟩ := halfWeight_comb (fun l => halfWeight_locPot (σ := σ) (L l)) n y
  choose j hj ej using fun l => halfWeight_locPot (σ := σ) (L l) y
  set F : ι → ReciprocityTheory.L2DbarEstimates.V D → ℝ := fun l v => ((L l).φ σ).φ (j l) (c.e.symm v) with hF
  have e : ∀ z, ((ArInt.comb L n).φ σ).φ i₀ z = ∑ l, (n l : ℝ) * ((L l).φ σ).φ (j l) z := by
    intro z
    have h := e₀ z
    simp only [← ej] at h
    have h2 : ∑ l, (n l : ℝ) * (((L l).φ σ).φ (j l) z / 2) =
        (∑ l, (n l : ℝ) * ((L l).φ σ).φ (j l) z) / 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun _ _ => by ring
    linarith
  set Ω := c.e.target ∩ c.e.symm ⁻¹' ⋂ l, ptsIn p σ ((L l).B.U (j l)) with hΩdef
  have hΩ : IsOpen Ω := ChartGlue.isOpen_over c.e (isOpen_iInter_of_finite fun l => isOpen_ptsIn _)
  have hmem : c.e y ∈ Ω := ChartGlue.mem_over c.e hy (Set.mem_iInter.2 hj)
  have hs : ∀ l, ContDiffOn ℝ ∞ (F l) Ω := fun l =>
    (contDiffOn_chart ((L l).cInf σ (j l)) c).mono fun v hv => ⟨hv.1, Set.mem_iInter.1 hv.2 l⟩
  have key : ∀ s : Finset ι,
      ReciprocityTheory.L2DbarEstimates.cHess D (fun v => ((∑ l ∈ s, (n l : ℝ) * F l v : ℝ) : ℂ)) (c.e y) =
        ∑ l ∈ s, ((n l : ℝ) : ℂ) • ReciprocityTheory.L2DbarEstimates.cHess D (fun v => (F l v : ℂ)) (c.e y) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have h0 := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul hΩ (p := fun _ => (0 : ℝ))
        (q := fun _ => (0 : ℝ)) contDiffOn_const contDiffOn_const 1 hmem
      simp only [mul_zero, add_zero, Complex.ofReal_one, one_smul] at h0
      simp only [Finset.sum_empty]
      exact left_eq_add.1 h0
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have h1 := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul hΩ
        (p := fun w => ∑ l ∈ s, (n l : ℝ) * F l w) (q := F a)
        (ContDiffOn.sum fun l _ => contDiffOn_const.mul (hs l)) (hs a) (n a) hmem
      have h3 : (fun v => ((∑ l ∈ insert a s, (n l : ℝ) * F l v : ℝ) : ℂ)) =
          fun v => ((∑ l ∈ s, (n l : ℝ) * F l v + (n a : ℝ) * F a v : ℝ) : ℂ) := by
        funext v
        rw [Finset.sum_insert ha, add_comm]
      rw [h3, h1, ih, add_comm]
  calc c.hess ((ArInt.comb L n).φ σ) i y = c.hess ((ArInt.comb L n).φ σ) i₀ y :=
        c.hess_eq ((ArInt.comb L n).cInf σ) hy hi₀ hi
    _ = ReciprocityTheory.L2DbarEstimates.cHess D (fun v => ((∑ l, (n l : ℝ) * F l v : ℝ) : ℂ)) (c.e y) := by
        simp only [AlgChart.hess, e, hF]
    _ = ∑ l, ((n l : ℝ) : ℂ) • ReciprocityTheory.L2DbarEstimates.cHess D (fun v => (F l v : ℂ)) (c.e y) := key _
    _ = ∑ l, ((n l : ℝ) : ℂ) • c.hess ((L l).φ σ) (m l) y :=
        Finset.sum_congr rfl fun l _ => by
          rw [← c.hess_eq ((L l).cInf σ) hy (hm l) (hj l)]
          rfl

end GlobalTheory.Mean4O.ReadsProj
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

theorem GlobalTheory.LKCx.minpoly_of_regAf_of_fixL : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ (β : G.Cˣ), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (y : grp G β) (h : G.GAf) (z : PosV G v β), FixL G v β y z.1 → RegAf G (h⁻¹ * toAfF G β x t hx y * h) → (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable := by
  intro p _ G v hv β hβ hR x t hx y h z hfix hreg
  have hcomm : ∀ a b : G.C, Commute a (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) →
      Commute b (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) → Commute a b := by
    obtain ⟨w, hw⟩ := hreg
    obtain ⟨U, hU⟩ := ubc_val_eq G β x t hx y h w
    rw [hU] at hw
    intro a b ha hb
    let ι : G.C →ₐ[ℚ] w.1.adicCompletion ℚ ⊗[ℚ] G.C := Algebra.TensorProduct.includeRight
    have hinj : Function.Injective ι :=
      Algebra.TensorProduct.includeRight_injective (algebraMap ℚ (w.1.adicCompletion ℚ)).injective
    have e : ι (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
        (1 : w.1.adicCompletion ℚ) ⊗ₜ (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) := rfl
    have ha' := ha.map ι
    have hb' := hb.map ι
    rw [e] at ha' hb'
    have hab := comm_of_conj U _ hw (ι a) (ι b) ha' hb'
    exact hinj (by rw [map_mul, map_mul]; exact hab.eq)
  obtain ⟨-, -, Z, hZ⟩ := GlobalTheory.LKCx.herm_laws p G v β hβ hR
  have hsim := GlobalTheory.LKCx.grp_similitude_herm p G v β y
  have hs : (0 : ℝ) < ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by exact_mod_cast y.2.2
  obtain ⟨c0, hc0⟩ := hfix
  obtain ⟨H, hH, hHM⟩ := GlobalTheory.T.similitude_signature_one_preserves_posDef_form G.n (G.gram v) (herm G v β) (toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ)
    (G.gram_herm v) Z _ (G.gram_det v) hv hZ hs (by rw [Complex.ofReal_ratCast]; exact hsim) z.1 c0 z.2 hc0
  have hsq := GlobalTheory.T.aeval_eq_zero_of_sq_eq_zero_of_posDef_similitude G.n H _ _ hH hs hHM
  have hsep := GlobalTheory.T.minpoly_separable_of_no_sq_zero_polynomial_image G.F G.C G.n v.embedding (G.psi v) G.n_pos (G.psi_F v) _ hsq
  exact ⟨GlobalTheory.T.natDegree_minpoly_eq_deg_centralSimple_commCentraliser G.F G.C G.n G.rankC _ hsep hcomm, hsep⟩
end
