module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle013
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle018
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2630
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.MapPowLeOfIsPullUnif
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle094
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle044
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle678
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle190
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false


noncomputable section

namespace GlobalTheory.KSChartRes

theorem isUnit_of_comap_mem {A S : Type} [CommRing A] [CommRing S] (φ : A →+* S) (s : A)
    (h : ∀ x : PrimeSpectrum S, PrimeSpectrum.comap φ x ∈ PrimeSpectrum.basicOpen s) : IsUnit (φ s) := by
  by_contra hn
  obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ (Ideal.span_singleton_ne_top hn)
  exact h ⟨m, hm.isPrime⟩ (hsm (Ideal.mem_span_singleton_self _))

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (α : A →+* B) (β : B →+* C) :
    spMap β ≫ spMap α = spMap (β.comp α) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (α : A →+* B) (β : B →+* C) :
    (dualMap β).comp (dualMap α) = dualMap (β.comp α) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap]

theorem isKS_top_of_basicOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (m : ℕ) (tt : Fin m → R) (n : ℕ) (v' : Fin n → TanM (𝟙 (Sp R)) t.G) (D : Derivation ℤ R R) (DV : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)) (Θ : Matrix (Fin n) (Fin n) R), (∀ r, DV (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D r))) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (fun a => spMap (dualMap (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) ≫ (tv (v' a)).left) ⇑DV ((((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).mapMatrix Θ) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) (fun a => spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) ≫ (tv (v' a)).left) (fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r))) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.mapMatrix Θ) := by
  intro E _ _ _ H R _ _ _ _ _ _ t m tt n v' D DV Θ hD ⟨J, Wc, j, d, hsup, hj, hfld, hcomp, htest⟩

  set s := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i) with hs
  set Wa := (Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) s with hWa
  have hWV : ∀ i, Wc i ≤ t.G.hom ⁻¹ᵁ Wa.1 := fun i =>
    (le_iSup Wc i).trans (hsup.le.trans (t.G.hom.preimage_mono inf_le_left))
  have hle : Wa.1 ≤ ⊤ := le_top
  refine ⟨J, Wc, j, d, ?_, hj, hfld, fun i h r => ?_, fun i i' O hO f S _ φ g₀ w hg₀ hO' hw => ?_⟩
  · rw [hsup, top_inf_eq]
    exact congrArg _ (inf_idem _)
  · have e : ∀ x, (t.G.hom.appLE ⊤ (Wc i) h).hom x =
        (t.G.hom.appLE Wa.1 (Wc i) (hWV i)).hom (((Sp R).presheaf.map (homOfLE hle).op).hom x) := fun x =>
      (congrArg (fun k => k.hom x) (t.G.hom.map_appLE (hWV i) (homOfLE hle).op)).symm
    have hr : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) = r :=
      Iso.hom_inv_id_apply _ _
    rw [e, e, hcomp i (hWV i)]
    have := hD ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r)
    rw [hr] at this
    exact congrArg _ this
  · have hOW : O ≤ t.G.hom ⁻¹ᵁ (Wa.1 ⊓ (Sp R).basicOpen s) :=
      hO.trans (inf_le_left.trans ((le_iSup Wc i).trans hsup.le))
    have hu : IsUnit (φ s) := by
      refine isUnit_of_comap_mem φ s fun x => ?_
      have hx : g₀ x ∈ O := hO' (show x ∈ (⊤ : (Sp S).Opens) from trivial)
      have hV : t.G.hom (g₀ x) ∈ (Sp R).basicOpen s := (hOW hx).2
      have e1 : t.G.hom (g₀ x) = (g₀ ≫ t.G.hom) x := rfl
      rw [e1, hg₀] at hV
      have h2 : (spMap φ) x ∈ (GlobalTheory.LogKS.chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ⁻¹ᵁ (Sp R).basicOpen s := hV
      change (spMap φ) x ∈ (isAffineOpen_top (Sp R)).fromSpec ⁻¹ᵁ (Sp R).basicOpen s at h2
      rw [(isAffineOpen_top (Sp R)).fromSpec_preimage_basicOpen s] at h2
      exact h2
    letI : Algebra Γ(Sp R, ⊤) Γ(Sp R, Wa.1) := ((Sp R).presheaf.map (homOfLE hle).op).hom.toAlgebra
    have hl : IsLocalization.Away s Γ(Sp R, Wa.1) :=
      (isAffineOpen_top (Sp R)).isLocalization_of_eq_basicOpen s (homOfLE hle) rfl
    obtain ⟨ψ, hψ⟩ : ∃ ψ : Γ(Sp R, Wa.1) →+* S, ψ.comp ((Sp R).presheaf.map (homOfLE hle).op).hom = φ :=
      ⟨IsLocalization.Away.lift s hu, IsLocalization.lift_comp _⟩
    subst hψ
    have hres : spMap ((Sp R).presheaf.map (homOfLE hle).op).hom ≫
        GlobalTheory.LogKS.chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) = GlobalTheory.LogKS.chart Wa :=
      (isAffineOpen_top (Sp R)).map_fromSpec Wa.2 (homOfLE hle).op
    have := htest i i' O hO f S ψ g₀ w ?_ hO' ?_
    · exact this
    · rw [hg₀, ← hres, ← Category.assoc, spMap_comp']
    · intro a
      obtain ⟨g', v'', h₁, h₂, h₃⟩ := hw a
      refine ⟨g', v'', h₁, ?_, h₃⟩
      rw [h₂]
      dsimp only
      rw [← Category.assoc, ← Category.assoc, spMap_comp']
      erw [spMap_comp']
      erw [dualMap_comp']

end GlobalTheory.KSChartRes
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BalProj

theorem actMat_ringHom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {X : Scheme.{0}} (t : SAB H X) (S : Type) [CommRing S] (x0 : Spec (CommRingCat.of S) ⟶ X) (n : ℕ) (v : Fin n → (Spec (CommRingCat.of (DualNumber S)) ⟶ t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) S), (∀ i, IsTanAtG t x0 (v i)) → (∀ w, IsTanAtG t x0 w → ∃! cf : Fin n → S, IsCombAtG t x0 v cf w) → (∀ a i, IsCombAtG t x0 v (A a i) (v i ≫ (t.act.act a).left)) → A 1 = 1 ∧ (∀ a b, A (a + b) = A a + A b) ∧ (∀ a b, A (a * b) = A a * A b) := by
  intro E _ _ _ H X t S _ x0 n v A hv hb hA
  classical
  let T : Fin n → TanM x0 t.G := fun i => GlobalTheory.LieMet.tanOf (hv i)
  have uniq : ∀ c c' : Fin n → S, ∑ j, c j • T j = ∑ j, c' j • T j → c = c' := by
    intro c c' h
    obtain ⟨cf, _, hcf⟩ := hb _ (GlobalTheory.LieMet.isTan_tv (∑ j, c j • T j))
    have h1 : IsCombAtG t x0 v c (tv (∑ j, c j • T j)).left := (GlobalTheory.LieMet.isComb_iff T c _).2 rfl
    have h2 : IsCombAtG t x0 v c' (tv (∑ j, c j • T j)).left := (GlobalTheory.LieMet.isComb_iff T c' _).2 h
    exact (hcf _ h1).trans (hcf _ h2).symm
  have hact : ∀ a i, ReciprocityTheory.ChartRestriction.G.PullbackSections.actR t.act a (T i) = ∑ j, A a i j • T j := fun a i =>
    (GlobalTheory.LieMet.isComb_iff T (A a i) (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR t.act a (T i))).1 (hA a i)
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    have e : ∑ k, A 1 i k • T k = ∑ k, (1 : Matrix (Fin n) (Fin n) S) i k • T k := by
      rw [← hact, map_one, Module.End.one_apply]
      simp [Matrix.one_apply]
    exact congrFun (uniq _ _ e) j
  · intro a b
    ext i j
    have e : ∑ k, A (a + b) i k • T k = ∑ k, (A a + A b) i k • T k := by
      rw [← hact, map_add (f := _), LinearMap.add_apply, hact, hact]
      simp [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
    exact congrFun (uniq _ _ e) j
  · intro a b
    ext i j
    have e : ∑ k, A (a * b) i k • T k = ∑ k, (A a * A b) i k • T k := by

      rw [← hact, mul_comm a b, map_mul, Module.End.mul_apply, hact, map_sum]
      simp only [map_smul, hact, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
      exact Finset.sum_comm
    exact congrFun (uniq _ _ e) j

end GlobalTheory.BalProj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerKilledNear

def FibreKilled (d : ℕ) {S' : Scheme.{0}} (G : Over S') [GrpObj G] (P : LB (G2 G).left) (s : S') : Prop :=
  ∀ (T' : Over S') (x : T' ⟶ G),
    (∃ f : T'.left ⟶ Spec (S'.residueField s), T'.hom = f ≫ S'.fromSpecResidueField s) →
    (∃ c : (P.pull (lift (snd G T' ≫ x) (fst G T')).left).Gen, c.IsGen) → x ^ d = 1

end GlobalTheory.KerKilledNear
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem isAbelianScheme_of_retract_of_isSemiAbelian : ∀ (S : Scheme.{0}) (A G : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj G] [IsCommMonObj G] (inc : G ⟶ A) (pr : A ⟶ G), IsAbelianScheme A → IsSemiAbelian G → IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → IsAbelianScheme G := by
  intro S A G _ _ _ _ inc pr hA hG _ _ h
  have hApr : IsProper A.hom := hA.proper
  have hsep : IsSeparated G.hom := hG.separated
  have hpr : IsSeparated pr.left := by
    have e : pr.left ≫ G.hom = A.hom := Over.w pr
    have : IsSeparated (pr.left ≫ G.hom) := by rw [e]; infer_instance
    exact IsSeparated.of_comp pr.left G.hom
  have hid : inc.left ≫ pr.left = 𝟙 G.left := by rw [← Over.comp_left, h, Over.id_left]
  have hci : IsClosedImmersion inc.left := by
    have : IsClosedImmersion (inc.left ≫ pr.left) := by rw [hid]; infer_instance
    exact IsClosedImmersion.of_comp inc.left pr.left
  refine ⟨hG.comm, hG.smooth, ?_, hG.geomConnected⟩
  have e : inc.left ≫ A.hom = G.hom := Over.w inc
  rw [← e]
  infer_instance

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.exists_free_submodule_finite_index_numberField : ∀ {E : Type} [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X], ∃ (f : (Fin (Module.finrank (𝓞 E) X) → 𝓞 E) →ₗ[𝓞 E] X) (m : ℕ), 0 < m ∧ Function.Injective f ∧ ∀ x : X, m • x ∈ LinearMap.range f := by
  first | exact @GlobalTheory.latt_free_sub_full_rank | exact GlobalTheory.latt_free_sub_full_rank | (intros; apply GlobalTheory.latt_free_sub_full_rank <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
open ReciprocityTheory.ChartRestriction.G.Out

noncomputable section

namespace GlobalTheory.UnifMoveGiven


open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear GlobalTheory.UnifMove in
theorem exists_pull_given {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R}
    {I' : Ideal R'} (hR : AdmBase R I) (hR' : AdmBase R' I') (g : R →+* R') (hg : Function.Injective g)
    (hI : I.map g ≤ I') (gK : FractionRing R →+* FractionRing R') (sq : spMap gK ≫ jK R = jK R' ≫ spMap g)
    {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G)
    (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (gA : A'.A.left ⟶ A.A.left)
    (gpA : IsGrpPullback A'.A A.A (spMap gK) gA) (hL : LBIso A'.L (A.L.pull gA)) (dA : A'.g = A.g) :
    ∃ (D' : DegData R' I') (hD : IsPullDeg g D.toPre D'.toPre)
      (U' : Unif I' D' A' ((Over.pullback (specOf g)).obj G)),
      IsPullUnif g hD (Iso.refl _) U U' ∧
      U'.gen.hom.left ≫ gA ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
        pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g) := by
  have hU : UnifBaseChangeSt := GlobalTheory.UnifPullGuards.unifBaseChange_holds
  have hψ : PsiOnExistsSt := psiOnExists
  have gpG := ThetaBaseChange.grp_generic U.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (specOf g)).obj G)) G (spMap gK ≫ jK R)
      (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g)) :=
    ((isGrpPullback_pullback ((Over.pullback (specOf g)).obj G) (jK R')).comp (isGrpPullback_pullback G (spMap g))).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) = pullback.fst G.hom (spMap g) :=
    Category.id_comp _
  have wA : LBIso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫
      (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U.LG.isLB _)
      (hL.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc, ← heA]; simp only [Category.assoc]
  have he : eSec ((Over.pullback (specOf g)).obj G) ≫ (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) = specOf g ≫ eSec G := by
    rw [hbc]; exact (cubeMapOf (isGrpPullback_pullback G (spMap g))).e_comm
  have hr : (rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig).IsGen :=
    LBxP.isGen_pullAlong U.LG.L _ (specOf g) (fun _ : PUnit => eSec G) (fun _ => 1) (fun _ => eSec ((Over.pullback (specOf g)).obj G))
      (fun _ => he) U.LG.rig U.LG.rigGen
  let L' : RigLB ((Over.pullback (specOf g)).obj G) := ⟨U.LG.L.pull ((Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g)),
    rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig, pull_isLB U.LG.isLB _, hr⟩
  obtain ⟨Wo, hWo, hψ⟩ := hψ R I hR D
  have hgen : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) ∈ Wo := by
    have : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective g hg)
    rw [this]; exact hWo
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf g)).obj G)).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨D', hD, U', -, hgenU, hPU⟩ := hU R R' I I' hR hR' g hI D A G hG U Wo hψ hgen ((Over.pullback (specOf g)).obj G)
    (Iso.refl _) mR A' dA eA mE wA L' (idIso _) he (idIso_isGen L'.isLB) (fun p => hr p.1 p.2)
  exact ⟨D', hD, U', hPU, by rw [hgenU]; exact heA⟩


open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear GlobalTheory.UnifMove in
theorem move_given : ∀ (V V' : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'], IsAdicComplete (maximalIdeal V) V → IsAdicComplete (maximalIdeal V') V' → ∀ (φ : V →+* V') (φK : FractionRing V →+* FractionRing V'), φK.comp (algebraMap V _) = (algebraMap V' _).comp φ → (maximalIdeal V).map φ ≤ maximalIdeal V' → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (A' : PolAV (Sp (FractionRing V'))) (ψ : A'.A.left ⟶ A.A.left), IsGrpPullback A'.A A.A (spMap φK) ψ → LBIso A'.L (A.L.pull ψ) → A'.g = A.g → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra (FractionRing V') F], (algebraMap (FractionRing V') F).comp φK = algebraMap (FractionRing V) F → ∃ (D' : DegData V' (maximalIdeal V')) (hD : IsPullDeg φ D.toPre D'.toPre) (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (U' : Unif (maximalIdeal V') D' A' G'), IsSemiAbelian G' ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (q : QkPt D.toPre F k) (x : TFK (R := V) F ⟶ A.A), QkToAkU U.toUnifPre F k q x → ∃ (q' : QkPt D'.toPre F k) (x' : TFK (R := V') F ⟶ A'.A), hD.xe q'.y = q.y ∧ x'.left ≫ ψ = x.left ∧ QkToAkU U'.toUnifPre F k q' x' := by
  intro V V' _ _ _ _ _ _ hV hV' φ φK hK hI D A G _ _ U A' ψ gp hL hg F _ _ _ hF
  have aV : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  have aV' : AdmBase V' (IsLocalRing.maximalIdeal V') := ⟨inferInstance, inferInstance, inferInstance, hV'⟩
  have hK' : ∀ r, φK (algebraMap V _ r) = algebraMap V' _ (φ r) := fun r => RingHom.congr_fun hK r
  have hφ : Function.Injective φ := fun a b h =>
    IsFractionRing.injective V (FractionRing V) (φK.injective (by rw [hK', hK', h]))
  have sq : spMap φK ≫ jK V = jK V' ≫ spMap φ := by
    refine (Spec.map_comp _ _).symm.trans (Eq.trans ?_ (Spec.map_comp _ _))
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hK
  have hFc : ∀ r : V, algebraMap (FractionRing V) F (algebraMap V (FractionRing V) r) =
      algebraMap (FractionRing V') F (algebraMap V' (FractionRing V') (φ r)) := fun r => by
    rw [← hK', ← hF]; rfl
  have sF : jFK (R := V') F ≫ spMap φK = jFK (R := V) F := by
    refine (Spec.map_comp _ _).symm.trans ?_
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hF
  obtain ⟨D', hD, U', hU, hgen⟩ := exists_pull_given aV aV' φ hφ hI φK sq
    (isSemiAbelian_of_unifPre_dvr V D A G U.toUnifPre) U A' ψ gp hL hg
  refine ⟨D', hD, _, inferInstance, inferInstance, U',
    isSemiAbelian_of_unifPre_dvr V' D' A' _ U'.toUnifPre, fun k hk q x H => ?_⟩
  obtain ⟨τ, hτ, -⟩ := exists_qk_pull_equiv abelianSchemeLaws_all.1 abelianSchemeLaws_all.2 V V' φ D.toPre D'.toPre hD
    D.tau_bimult D'.tau_bimult F hFc k
  obtain ⟨hy, hg'⟩ := (hτ q _).1 rfl
  have w : x.left ≫ A.A.hom = jFK (R := V') F ≫ spMap φK := (Over.w x).trans sF.symm
  let x' : TFK (R := V') F ⟶ A'.A := Over.homMk (gp.1.lift x.left (jFK (R := V') F) w) (gp.1.lift_snd _ _ _)
  have hx : x'.left ≫ ψ = x.left := gp.1.lift_fst _ _ _
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf φ)).obj G)).hom := by show IsMonHom (𝟙 _); infer_instance
  refine ⟨τ q, x', by rw [hy]; exact hD.xe.apply_symm_apply _, hx,
    qkToAk_baseChange abelianSchemeLaws_all.1.globalFns abelianSchemeLaws_all.1.secBaseChange V V' _ _ aV aV' φ D A G U
      _ (Iso.refl _) mR A' D' hD U' hU F hFc k hk q x (τ q) x' hy hg' ?_ H⟩
  have n : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U'.gen.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl ((Over.pullback (specOf φ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf φ) =
      pullback.fst G.hom (spMap φ) := Category.id_comp _
  rw [hbc, ← hgen, ← Category.assoc U'.gen.inv.left, n, Category.id_comp, ← Category.assoc, hx]

end GlobalTheory.UnifMoveGiven

end
end

section

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.StalkField

theorem exists_stalk_field_hom : ∀ (Ω : Type) [Field Ω] (X : Scheme.{0}) (p : Sp Ω ⟶ X), (p.stalkMap (genericPoint (Sp Ω))).hom.Finite → ∃ φ : X.presheaf.stalk (p.base (genericPoint (Sp Ω))) →+* Ω, φ.Finite ∧ ∀ (K : Type) [Field K] (τ₁ τ₂ : Ω →+* K), spMap τ₁ ≫ p = spMap τ₂ ≫ p → τ₁.comp φ = τ₂.comp φ := by
  intro Ω _ X p hfin
  have hpt : genericPoint (Sp Ω) = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
  rw [hpt] at hfin ⊢
  refine ⟨(Scheme.stalkClosedPointTo p).hom, ?_, ?_⟩
  · have e : Scheme.stalkClosedPointTo p = p.stalkMap _ ≫ (stalkClosedPointIso (CommRingCat.of Ω)).hom := rfl
    rw [e, CommRingCat.hom_comp]
    exact RingHom.Finite.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (CommRingCat.of Ω)).hom).2) hfin
  · intro K _ τ₁ τ₂ h
    have hs : ∀ τ : Ω →+* K, (spMap τ ≫ p) (IsLocalRing.closedPoint K) ⤳ p (IsLocalRing.closedPoint Ω) := by
      intro τ
      apply specializes_of_eq
      exact congrArg p (Subsingleton.elim ((spMap τ).base (IsLocalRing.closedPoint K)) (IsLocalRing.closedPoint Ω))
    have H : ∀ (q₁ q₂ : Sp K ⟶ X), q₁ = q₂ → ∀ (h₁ : q₁ (IsLocalRing.closedPoint K) ⤳ p (IsLocalRing.closedPoint Ω))
        (h₂ : q₂ (IsLocalRing.closedPoint K) ⤳ p (IsLocalRing.closedPoint Ω)) a,
        (Scheme.stalkClosedPointTo q₁).hom ((X.presheaf.stalkSpecializes h₁).hom a) =
          (Scheme.stalkClosedPointTo q₂).hom ((X.presheaf.stalkSpecializes h₂).hom a) := by
      rintro _ _ rfl _ _ _; rfl
    ext a
    simp only [RingHom.comp_apply]
    rw [← GlobalTheory.TorRef.stalkClosedPointTo_comp_spMap_specializes X p τ₁ (hs τ₁) a,
      ← GlobalTheory.TorRef.stalkClosedPointTo_comp_spMap_specializes X p τ₂ (hs τ₂) a]
    exact H _ _ h _ _ a

end GlobalTheory.StalkField
end
