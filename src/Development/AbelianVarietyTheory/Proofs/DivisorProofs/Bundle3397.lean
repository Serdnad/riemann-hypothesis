module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Flat.TorsionFree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDeRhamHomologyAbelianVarietyCharZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3339
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2184
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2255
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3390
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniqueIsConnOfLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2576
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentCompatibility
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2590
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2885
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle092
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle096
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3389
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.dividingLabel_persists_thetaSetupTower : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (𝔗 : Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), 𝔗.X₂.M.Div 𝔗.X₂.S.th (𝔗.lam x₀) z₂ := by
  first | exact @GlobalTheory.Poinc.Sep.Tower.div_lam | exact GlobalTheory.Poinc.Sep.Tower.div_lam | (intros; apply GlobalTheory.Poinc.Sep.Tower.div_lam <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DeRham

theorem charpoly_push_eq_map_charpoly (k : Type) [Field k] [IsAlgClosed k]
    (B : GlobalTheory.AV.AbVar k) (f : B ⟶ B) [Module.Finite k (HdR B.X)] :
    LinearMap.charpoly (push (dp0 k) (𝟙 _) f.hom) =
      (GlobalTheory.AV.AbVar.charpoly (End.of f)).map (Int.castRingHom k) := by
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with h | h
  · haveI : Fact p.Prime := ⟨h⟩
    exact GlobalTheory.T.charpoly_deRhamHomology_abelianVariety_charP p k B f
  · subst h
    have : CharZero k := CharP.charP_to_charZero k
    have hcharpoly := GlobalTheory.DeRhamCharpolyZero.charpoly_push k B f
    exact hcharpoly

theorem charpoly_push_eq : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (f : A ⟶ A) [IsMonHom f] (L : Type) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
      (φ : L →ₗ[ℤ] L) (l : ℕ), l.Prime → (l : k) ≠ 0 →
      ∀ ev : ℕ → L → (Over.mk (𝟙 (Sp k)) ⟶ A),
      (∀ j x y, ev j (x + y) = ev j x * ev j y) →
      (∀ j x, ev j (φ x) = ev j x ≫ f) →
      (∀ j x, ev j x = 1 ↔ ∃ y, x = l ^ j • y) →
      (∀ j (q : Over.mk (𝟙 (Sp k)) ⟶ A), q ^ (l ^ j) = 1 ↔ ∃ x, ev j x = q) →
      ∀ [Module.Finite k (HdR A)],
        LinearMap.charpoly (push (dp0 k) (𝟙 _) f) = (LinearMap.charpoly φ).map (Int.castRingHom k) := by
  intro k _ _ A _ _ hA f _ L _ _ _ φ l hl hlk ev hadd hφ hker him _
  obtain ⟨g, hg⟩ := GlobalTheory.AV.exists_smoothOfRelativeDimension_of_isAbelianScheme k A hA
  let B : GlobalTheory.AV.AbVar k := ⟨A, hA, g, hg⟩
  let f' : B ⟶ B := GlobalTheory.AV.AbVar.Hom.mk (A := B) (B := B) f
  rw [GlobalTheory.T.l_power_torsion_endomorphism_evaluation k B f' L φ l hl hlk ev hadd hφ hker him]
  exact charpoly_push_eq_map_charpoly k B f'

end GlobalTheory.DeRham
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroCrys

theorem isBC_trivSqZeroExt : ∀ (k : Type) [Field k] (V : Type) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V]
    [IsCentralScalar k V] (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ →
    ∀ (h2 : RingHom.ker (TrivSqZeroExt.fstHom k k V).toRingHom ^ 2 = 0)
      (m : GrpMor (dp0 k) (𝟙 _) A₀ (divided₂ h2) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀
        (algebraMap k (TrivSqZeroExt k V)) (𝟙 _) (Over.Hom.left (𝟙 A₀))), m.IsBC := by
  intro k _ V _ _ _ _ A₀ _ hA h2 m
  have := hA.smooth
  obtain ⟨g, hg⟩ := GlobalTheory.SerreDim.exists_dim_of_grpObj A₀
  have e : (𝟙 _ : Sp k ⟶ Sp k) = spMap (RingHom.id k) := (Cris.spMap_id k).symm
  have h := (GlobalTheory.CrysConn.isGrpPullback_refl A₀).congr e rfl
  have key : ∀ (t : Sp k ⟶ Sp k), t = spMap (RingHom.id k) →
      ∀ m : GrpMor (dp0 k) t A₀ (divided₂ h2) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀
        (algebraMap k (TrivSqZeroExt k V)) (𝟙 _) (Over.Hom.left (𝟙 A₀)), m.IsBC := by
    rintro _ rfl m
    exact GlobalTheory.CrysConn.isBC_of_lift GlobalTheory.T.abelianScheme_firstDeRham_structure hA hg (isDPNilpotent_bot k) Function.surjective_id
      ((RingHom.injective_iff_ker_eq_bot _).1 Function.injective_id) h (isDPNilpotent_squareZero _)
      (fun r ↦ ⟨TrivSqZeroExt.inl r, rfl⟩) rfl m (GlobalTheory.CrysConn.isGrpPullback_refl A₀)
  exact key _ e m

end GlobalTheory.SqZeroCrys
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CrysFree

theorem isLocalRing_of_sq {Λ k : Type} [CommRing Λ] [Field k] (π : Λ →+* k) (hπ : Function.Surjective π)
    (hI : RingHom.ker π ^ 2 = 0) : IsLocalRing Λ := by
  have hmax : (RingHom.ker π).IsMaximal := RingHom.ker_isMaximal_of_surjective π hπ
  haveI := hmax.isPrime
  have hle : RingHom.ker π ≤ nilradical Λ := fun x hx ↦ ⟨2, by
    have : x * x ∈ RingHom.ker π ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hx hx
    rw [hI] at this; simpa [pow_two] using this⟩
  have heq : nilradical Λ = RingHom.ker π := le_antisymm (nilradical_le_prime _) hle
  haveI : (nilradical Λ).IsMaximal := heq ▸ hmax
  exact IsLocalRing.of_isMaximal_nilradical Λ

theorem isDPMorphism_red {Λ k : Type} [CommRing Λ] [Field k] (π : Λ →+* k)
    (hI : RingHom.ker π ^ 2 = 0) : DividedPowers.IsDPMorphism (divided₂ hI) (dp0 k) π := by
  refine (DividedPowers.isDPMorphism_iff _ _ _).2 ⟨?_, fun n hn a ha ↦ ?_⟩
  · rw [Ideal.map_le_iff_le_comap]; intro x hx
    simpa using (RingHom.mem_ker.1 hx)
  · rw [RingHom.mem_ker.1 ha]
    rcases n with _ | _ | n
    · exact absurd rfl hn
    · rw [zero_add, (divided₂ hI).dpow_one ha, RingHom.mem_ker.1 ha, (dp0 k).dpow_one (Ideal.zero_mem _)]
    · rw [squareZeroDividedPowers_dpow hI (by omega), map_zero, DividedPowers.dpow_eval_zero _ hn]

theorem mem_smul_top_of_forall {Λ : Type} [CommRing Λ] {P : Type*} [AddCommGroup P] [Module Λ P]
    [Module.Finite Λ P] [Module.Free Λ P] (J : Ideal Λ) (h : Module.Dual Λ P) (hh : ∀ c, h c ∈ J) :
    h ∈ J • (⊤ : Submodule Λ (Module.Dual Λ P)) := by
  classical
  let b := Module.Free.chooseBasis Λ P
  rw [← b.sum_dual_apply_smul_coord h]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (hh _) Submodule.mem_top

end GlobalTheory.CrysFree

namespace GlobalTheory.CrysFree

theorem crys_free_and_red : ∀ (F : Type) [Field F] [NumberField F] (Λ : Type) [CommRing Λ] (k : Type) [Field k] (π : Λ →+* k) (hπ : Function.Surjective π) (hI : RingHom.ker π ^ 2 = 0) (A₀ : Over (Sp k)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ a : OAct (𝓞 F) A₀, letI := tensorModule (divided₂ hI) (spMap π) a; letI := tensorModule (dp0 k) (𝟙 _) a; Module.Finite Λ (Crys (divided₂ hI) (spMap π) A₀) ∧ Module.Free Λ (Crys (divided₂ hI) (spMap π) A₀) ∧ ∃ f : Crys (divided₂ hI) (spMap π) A₀ →ₛₗ[(Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ (𝓞 F))).toRingHom] HdR A₀, Function.Surjective f ∧ ∀ m, f m = 0 → m ∈ (RingHom.ker π) • (⊤ : Submodule Λ (Crys (divided₂ hI) (spMap π) A₀)) := by
  intro F _ _ Λ _ k _ π hπ hI A₀ _ _ hA₀ a
  haveI := isLocalRing_of_sq π hπ hI
  letI : Algebra Λ k := π.toAlgebra
  obtain ⟨A, _, i, h, hA⟩ := GlobalTheory.T.abelianScheme_unobstructed_squareZero_affine Λ (RingHom.ker π) hI k π hπ rfl A₀ hA₀
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim Λ A hA
  obtain ⟨HFree, -, HBC, HRigid, -⟩ := GlobalTheory.T.abelianScheme_firstDeRham_structure
  have hrig := HRigid Λ A g hA hg (RingHom.ker π) (divided₂ hI) (isDPNilpotent_squareZero hI) k π hπ rfl A₀ i h
  let e : primDR A ≃ₗ[Λ] prim (divided₂ hI) (spMap π) A₀ :=
    LinearEquiv.ofBijective (liftMor (divided₂ hI) h).pull hrig
  obtain ⟨hfin, hproj, -⟩ := HFree.prim hA hg
  haveI : Module.Finite Λ (prim (divided₂ hI) (spMap π) A₀) := Module.Finite.equiv e
  haveI : Module.Projective Λ (prim (divided₂ hI) (spMap π) A₀) := Module.Projective.of_equiv e
  haveI := Module.finitePresentation_of_projective Λ (prim (divided₂ hI) (spMap π) A₀)
  haveI : Module.Free Λ (prim (divided₂ hI) (spMap π) A₀) := Module.free_of_flat_of_isLocalRing
  have m : GrpMor (divided₂ hI) (spMap π) A₀ (dp0 k) (𝟙 _) A₀ (algebraMap Λ k) (𝟙 _) (Over.Hom.left (𝟙 A₀)) :=
    ⟨isDPMorphism_red π hI, by simp, by simp, by
      intro T x y x₀ y₀ hx hy
      have ex : x₀.left = x.left := by simpa using hx
      have ey : y₀.left = y.left := by simpa using hy
      have eqx : x₀ = x := Over.OverMorphism.ext ex
      have eqy : y₀ = y := Over.OverMorphism.ext ey
      subst x₀
      subst y₀
      simp only [Over.id_left, Category.comp_id]
      rfl⟩
  have hm : m.IsBC := by
    have hb := (HBC Λ A g hA hg k A₀ i h).1
    let E := LinearEquiv.baseChange Λ k _ _ e
    have key : liftSemi m.pull ∘ₗ E.toLinearMap =
        liftSemi (GlobalTheory.Published.AbelianDeRham.bcMor (R' := k) h).pull := by
      refine LinearMap.ext fun z ↦ ?_
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x c =>
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, E, LinearEquiv.baseChange_tmul,
          liftSemi_tmul]
        congr 1
        exact GrpMor.pull_pull (liftMor (divided₂ hI) h) m (GlobalTheory.Published.AbelianDeRham.bcMor (R' := k) h)
          (fun _ ↦ rfl) (by simp) c
      | add x y hx hy => rw [map_add (f := _), hx, hy, map_add (f := _)]
    have : liftSemi m.pull = liftSemi (GlobalTheory.Published.AbelianDeRham.bcMor (R' := k) h).pull ∘ₗ
        E.symm.toLinearMap := by
      rw [← key, LinearMap.comp_assoc, ← LinearEquiv.coe_trans, LinearEquiv.symm_trans_self]; rfl
    unfold GrpMor.IsBC
    rw [this]
    exact hb.comp E.symm.bijective
  refine ⟨inferInstance, inferInstance, ?_⟩
  have hact : ∀ (o : 𝓞 F) (x : Crys (divided₂ hI) (spMap π) A₀),
      hm.bcMap (act (divided₂ hI) (spMap π) a o x) = act (dp0 k) (𝟙 _) a o (hm.bcMap x) := by
    intro o x
    haveI := a.hom o
    rw [act_apply, act_apply]
    exact hm.corr_iff.1 (GrpMor.Corr.push (m := m) m (a.act o) (a.act o) (by simp) (hm.corr_iff.2 rfl))
  letI := tensorModule (divided₂ hI) (spMap π) a
  letI := tensorModule (dp0 k) (𝟙 _) a
  refine ⟨{ toFun := hm.bcMap, map_add' := hm.bcMap.map_add, map_smul' := ?_ }, ?_, ?_⟩
  · intro r x
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul l o =>
      have e1 : (l ⊗ₜ[ℤ] o) • x = l • act (divided₂ hI) (spMap π) a o x := rfl
      have e2 : ∀ y : HdR A₀, ((Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ (𝓞 F))).toRingHom
          (l ⊗ₜ[ℤ] o)) • y = π l • act (dp0 k) (𝟙 _) a o y := fun y ↦ rfl
      rw [e1, e2, hm.bcMap.map_smulₛₗ, hact]
      rfl
    | add r s hr hs =>
      rw [add_smul, map_add (f := hm.bcMap), hr, hs, map_add (f := _), add_smul]
  · intro h'
    let l : prim (divided₂ hI) (spMap π) A₀ →ₗ[Λ] k :=
      { toFun c := h' (m.pull c)
        map_add' c d := by rw [map_add (f := _), map_add (f := _)]
        map_smul' r c := by
          rw [map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, Algebra.smul_def] }
    obtain ⟨hh, hhl⟩ := Module.projective_lifting_property (Algebra.linearMap Λ k) l hπ
    exact ⟨hh, hm.corr_iff.1 fun c ↦ (LinearMap.congr_fun hhl c).symm⟩
  · intro x hx
    have hc : m.Corr x 0 := hm.corr_iff.2 hx
    exact mem_smul_top_of_forall _ x fun c ↦ RingHom.mem_ker.2 ((hc c).symm.trans (LinearMap.zero_apply _))

end GlobalTheory.CrysFree
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftFilEq

open GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing



theorem liftFil_le (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (A₁ A₂ : Over (Sp (DualNumber k)))
    [GrpObj A₁] [GrpObj A₂] (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₀.left ⟶ A₂.left)
    (h₁ : IsGrpPullback A₀ A₁ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i₁)
    (h₂ : IsGrpPullback A₀ A₂ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i₂)
    (hA₁ : IsAbelianScheme A₁) (g : HdR A₀ → HdR A₀)
    (H₁ : ∀ x ∈ Fil A₀, IsFilLift h₁ x (g x)) (H₂ : ∀ x ∈ Fil A₀, IsFilLift h₂ x (g x)) :
    liftFil (epsDP k) h₁ ≤ liftFil (epsDP k) h₂ := by
  have P : AbelianDeRham := GlobalTheory.T.abelianScheme_firstDeRham_structure
  obtain ⟨g₁, hg₁⟩ := GlobalTheory.AbelianDim.exists_relDim (DualNumber k) A₁ hA₁
  have hA₀ : IsAbelianScheme A₀ := by
    have := hA₁.comm
    have hc : IsCommMonObj A₀ := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (h₁.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← h₁.2 T x y (pushPt h₁.1.w x) (pushPt h₁.1.w y) rfl rfl,
        ← h₁.2 T y x (pushPt h₁.1.w y) (pushPt h₁.1.w x) rfl rfl, _root_.mul_comm]
    exact { comm := hc
            smooth := MorphismProperty.of_isPullback (P := @Smooth) h₁.1 hA₁.smooth
            proper := MorphismProperty.of_isPullback (P := @IsProper) h₁.1 hA₁.proper
            geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h₁.1 hA₁.geomConnected }
  have gA₀ := (smoothOfRelativeDimension_isStableUnderBaseChange g₁).of_isPullback h₁.1 hg₁
  obtain ⟨C, _, φ, j, hφ, hic, e1⟩ := exists_const A₀
  have hBC := constMor_isBC P hA₀ gA₀ hφ hic e1
  have HC : Canonical (epsDP k) (TrivSqZeroExt.fstHom k k k).toRingHom :=
    canonical_of_abelianDeRham P (isDPNilpotent_squareZero _) (fun r ↦ ⟨TrivSqZeroExt.inl r, rfl⟩) rfl
  have step : ∀ x ∈ liftFil (epsDP k) h₁, ∃ y ∈ liftFil (epsDP k) h₁ ⊓ liftFil (epsDP k) h₂,
      ∃ z : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀, x = y + (DualNumber.eps : DualNumber k) • z := by
    intro x hx
    have ha := crysLo_mem_Fil P hA₁ hg₁ h₁ hx
    obtain ⟨d₁, hd₁, e₁⟩ := H₁ _ ha
    obtain ⟨d₂, hd₂, e₂⟩ := H₂ _ ha
    have e : d₁ = d₂ := crys_ext P hA₀ gA₀ fun c ↦ (e₁ c).trans (e₂ c).symm
    obtain ⟨z, hz⟩ := hBC.exists (crysHi x - g (crysLo x))
    have hd₁₂ : d₁ ∈ liftFil (epsDP k) h₂ := by rw [e]; exact hd₂
    refine ⟨d₁, ⟨hd₁, hd₁₂⟩, z, crys_ext P hA₀ gA₀ fun c ↦ ?_⟩
    rw [LinearMap.add_apply, LinearMap.smul_apply, e₁, hz c, crys_constMor x c]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hEq : liftFil (epsDP k) h₁ = liftFil (epsDP k) h₁ ⊓ liftFil (epsDP k) h₂ := by
    refine eq_of_le_of_le_add_eps ?_ inf_le_left step
    obtain ⟨N, hN⟩ := (HC g₁ A₀ A₁ i₁ h₁ hA₁ hg₁).2.1
    have c := HC.crysToDR_bijective h₁ hA₁ hg₁
    exact ⟨_, (Submodule.orderIsoMapComap (LinearEquiv.ofBijective _ c)).symm.isCompl hN⟩
  exact fun x hx ↦ (hEq.le hx).2

theorem liftFil_eq : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (A₁ A₂ : Over (Sp (DualNumber k))) [GrpObj A₁] [GrpObj A₂] (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₀.left ⟶ A₂.left) (h₁ : IsGrpPullback A₀ A₁ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i₁) (h₂ : IsGrpPullback A₀ A₂ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i₂), IsAbelianScheme A₁ → IsAbelianScheme A₂ → ∀ g : HdR A₀ → HdR A₀, (∀ x ∈ Fil A₀, IsFilLift h₁ x (g x)) → (∀ x ∈ Fil A₀, IsFilLift h₂ x (g x)) → liftFil (epsDP k) h₁ = liftFil (epsDP k) h₂ := by
  intro k _ A₀ _ A₁ A₂ _ _ i₁ i₂ h₁ h₂ hA₁ hA₂ g H₁ H₂
  exact le_antisymm (liftFil_le k A₀ A₁ A₂ i₁ i₂ h₁ h₂ hA₁ g H₁ H₂)
    (liftFil_le k A₀ A₂ A₁ i₂ i₁ h₂ h₁ hA₂ g H₂ H₁)

end GlobalTheory.LiftFilEq
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

namespace GlobalTheory.PolRootComplete

theorem root_given {S T : Scheme.{0}} {A : Over S} [GrpObj A] {P : LB (G2 A).left} (hP : P.IsLB) {t : T ⟶ S}
    (h : Root A P t) {B : Over T} [GrpObj B] [IsCommMonObj B] {β : B.left ⟶ A.left}
    {β₂ : (G2 B).left ⟶ (G2 A).left} (hβ : IsGrpPullback B A t β) (hsq : IsSquare β β₂) :
    ∃ L : LB B.left, L.IsLB ∧ LBIso (abelian₂ B L) (P.pull β₂) := by
  obtain ⟨C, _, _, c, c₂, hc, hsqc, L, hL, H⟩ := h
  let φ : B.left ⟶ C.left := hc.1.lift β B.hom hβ.1.w
  have hφc : φ ≫ c = β := hc.1.lift_fst _ _ _
  have hφw : φ ≫ C.hom = B.hom ≫ 𝟙 T := (hc.1.lift_snd _ _ _).trans (Category.comp_id _).symm
  have hφ : IsGrpPullback B C (𝟙 T) φ := hc.cancel (hβ.congr (Category.id_comp t).symm hφc.symm) hφw
  obtain ⟨φ₂, hφ₂⟩ := GlobalTheory.ZM.SiegPull.exists_isSquare hφw
  have e : φ₂ ≫ c₂ = β₂ :=
    GlobalTheory.ZM.SiegPull.isSquare_unique (GlobalTheory.ZM.SiegPull.isSquare_comp hφ₂ hsqc) hsq hφc
  have hLφ : (L.pull φ).IsLB := pull_isLB hL φ
  refine ⟨L.pull φ, hLφ, ?_⟩
  have h1 : LBIso (abelian₂ B (L.pull φ)) ((abelian₂ C L).pull φ₂) :=
    GlobalTheory.ZM.SiegPull.lbIso_lam_pull hφ (GlobalTheory.GtBaseChange.lbIso_refl hLφ) hφ₂
  have h2 : LBIso ((abelian₂ C L).pull φ₂) (P.pull (φ₂ ≫ c₂)) := GlobalTheory.ZM.SiegPull.lbIso_pull_comp H φ₂
  rw [e] at h2
  exact LBIso.trans (LB.isLB_linComb hLφ _ _) (pull_isLB (LB.isLB_linComb hL _ _) _) (pull_isLB hP _) h1 h2

theorem root_of_closedFibre (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsAdicComplete (maximalIdeal R) R) (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) (P : LB (G2 B).left) (hP : P.IsLB)
    (g1 : ∃ u : (P.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, u.IsGen)
    (g2 : ∃ u : (P.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, u.IsGen)
    (gamp : RelAmple B (P.pull (lift (𝟙 B) (𝟙 B)).left))
    (h0 : ∃ L₀ : LB (thickObj R (maximalIdeal R) 0 B).left, L₀.IsLB ∧
      ∀ b₂ : (G2 (thickObj R (maximalIdeal R) 0 B)).left ⟶ (G2 B).left,
        IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) 0)) b₂ →
          LBIso (abelian₂ (thickObj R (maximalIdeal R) 0 B) L₀) (P.pull b₂)) :
    ∃ L : LB B.left, L.IsLB ∧ LBIso (abelian₂ B L) P := by
  let Q : ∀ e, LB (thickObj R (maximalIdeal R) e B).left → Prop := fun e L => L.IsLB ∧
    ∀ b₂ : (G2 (thickObj R (maximalIdeal R) e B)).left ⟶ (G2 B).left,
      IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) e)) b₂ →
        LBIso (abelian₂ (thickObj R (maximalIdeal R) e B) L) (P.pull b₂)
  have step : ∀ e (L : {L // Q e L}), ∃ L' : {L' // Q (e + 1) L'},
      LBIso (L'.1.pull (thickMap R (maximalIdeal R) e B)) L.1 := fun e L => by
    obtain ⟨L', h1', h2', h3'⟩ := GlobalTheory.T.line_bundle_thickening_square_theorem R B hB P hP g1 g2 e L.1 L.2.1 L.2.2
    exact ⟨⟨L', h1', h2'⟩, h3'⟩
  choose F hF using step
  obtain ⟨L₀, hL₀⟩ := h0
  let N : ∀ e, {L // Q e L} := fun e => Nat.rec ⟨L₀, hL₀⟩ (fun e L => F e L) e
  have hN : ∀ e, LBIso ((N (e + 1)).1.pull (thickMap R (maximalIdeal R) e B)) (N e).1 := fun e => hF e (N e)
  have hproj : GlobalTheory.AbLaw.IsProjBy B.hom := GlobalTheory.WtTower.isProjBy_of_relAmple B (pull_isLB hP _) gamp
  obtain ⟨M, hM, HM⟩ := GlobalTheory.LBAlgComplete.exists_lineBundle_of_reductions GlobalTheory.formalAlgebraisation R
    (maximalIdeal R) hR B hproj (fun e => thickObj R (maximalIdeal R) e B)
    (fun e => thickMap R (maximalIdeal R) e B) (fun e => pullback.fst B.hom (thick R (maximalIdeal R) e))
    (fun e => (isGrpPullback_pullback B (thick R (maximalIdeal R) e)).1)
    (fun e => (pullback.lift_fst _ _ _).trans (Category.comp_id _)) (fun e => (N e).1) (fun e => (N e).2.1)
    (fun e => (hN e).symm)
  haveI := GlobalTheory.WtTower.isLocalRing_quotient_pow R 0
  obtain ⟨b₂, hb₂⟩ := GlobalTheory.ZM.SiegPull.exists_isSquare (isGrpPullback_pullback B (thick R (maximalIdeal R) 0)).1.w
  exact ⟨M, hM, GlobalTheory.T.lineBundleIso_mumfordLambda_of_local_quotient R (R ⧸ maximalIdeal R ^ (0 + 1)) (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective B (thickObj R (maximalIdeal R) 0 B) (pullback.fst _ _) b₂ hB
    (isGrpPullback_pullback B _) hb₂ P hP g1 g2 M (N 0).1 hM (N 0).2.1 (HM 0).symm ((N 0).2.2 b₂ hb₂)⟩

theorem root_of_residue : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ t : Sp R ⟶ S, Root A P (spMap (residue R) ≫ t) → Root A P t := by
  intro S A _ _ hA P hP h1 h2 hamp R _ _ _ hR t hroot
  obtain ⟨B, _, β, hβ⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A t
  have hB : IsAbelianScheme B := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hβ
  haveI : IsCommMonObj B := hB.comm
  obtain ⟨β₂, hsq⟩ := GlobalTheory.ZM.SiegPull.exists_isSquare hβ.1.w
  obtain ⟨g1, g2⟩ := GlobalTheory.T.axisTrivial_lineBundle_groupPullback S (Sp R) A P hP h1 h2 t B β β₂ hβ hsq
  have gamp := GlobalTheory.T.relAmple_diagonal_pullback_baseChange S (Sp R) A hA P hP hamp t B β β₂ hβ.1 hsq
  have le : maximalIdeal R ≤ maximalIdeal R ^ (0 + 1) := by rw [zero_add, pow_one]
  have ethick : thick R (maximalIdeal R) 0 =
      spMap (Ideal.Quotient.factor le) ≫ spMap (residue R) := by
    simp only [thick, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hres : Root A P (thick R (maximalIdeal R) 0 ≫ t) := by
    rw [ethick, Category.assoc]
    exact hroot.comp hA _
  have hY := isGrpPullback_pullback B (thick R (maximalIdeal R) 0)
  obtain ⟨b₂, hb₂⟩ := GlobalTheory.ZM.SiegPull.exists_isSquare hY.1.w
  obtain ⟨L₀, hL₀, H₀⟩ := root_given hP hres (hY.comp hβ) (GlobalTheory.ZM.SiegPull.isSquare_comp hb₂ hsq)
  obtain ⟨L, hL, HL⟩ := root_of_closedFibre R hR B hB (P.pull β₂) (pull_isLB hP _) g1 g2 gamp
    ⟨L₀, hL₀, fun b₂' hb₂' => by
      have e : b₂' = b₂ := GlobalTheory.ZM.SiegPull.isSquare_unique hb₂' hb₂ rfl
      subst e
      exact LBIso.trans (LB.isLB_linComb hL₀ _ _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) H₀
        (GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.GtBaseChange.lbIso_refl (pull_isLB hP β₂)) b₂').symm⟩
  exact ⟨B, inferInstance, inferInstance, β, β₂, hβ, hsq, L, hL, HL⟩

end GlobalTheory.PolRootComplete
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.unitary_labelling_transport_galois_conjugate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X₁ : USetup C) (D : UDeep X₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (s : D.X.M.Z ⟶ D.X.M.Z), D.X.M.pt ≫ s = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.M.pt → ∀ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a → (∀ x, a (D.lab x) = D.lab x) → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y) (h' : (y ≫ s) ≫ D.q = ct.y) (yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X), UIsLab D.X (D.lift ct y h) yy → UIsLab D.X (D.lift ct (y ≫ s) h') (yy.comp a.toAddMonoidHom) := by
  first | exact @GlobalTheory.UPoinc.UGalTrans.isLab_conj | exact GlobalTheory.UPoinc.UGalTrans.isLab_conj | (intros; apply GlobalTheory.UPoinc.UGalTrans.isLab_conj <;> assumption)
end
