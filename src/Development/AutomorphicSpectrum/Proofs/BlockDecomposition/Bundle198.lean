module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.FormCos
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle190
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle191
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SurjectiveOfLocallySurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle194
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle601
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.IwasawaUnitaryAdelic.IUAIwa
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle047
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle025
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle192
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

theorem _root_.GlobalTheory.T.cover_intersection_graded_iso : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q) (a n : ℕ)
    (i : Fin (n + 1) → U.ι) (r : ℕ), Nonempty (HU (Fk q U a) (capT (Vk q U a) i) r ≃+ HQ (KS q (a + 1) {capO U.U i}) (a : ℤ) ((a : ℤ) + 1) r) := by
  first | exact @GlobalTheory.CompanionTheory.CapKC.cap_kc | exact GlobalTheory.CompanionTheory.CapKC.cap_kc | (intros; apply GlobalTheory.CompanionTheory.CapKC.cap_kc <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

theorem _root_.GlobalTheory.T.pullback_cover_star_compat : ∀ {K : Type} [CommRing K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K))
    (u : X ⟶ Y) (hu : u ≫ p = q) (U : Cov q) (W : Cov p) (τ : U.ι → W.ι)
    (hτ : ∀ n (i : Fin (n + 1) → U.ι), capO U.U i ≤ u ⁻¹ᵁ capO W.U (τ ∘ i)) (a : ℕ),
    ∃ hG : ∀ T, KC q U a T → KC p W a ((pullM u hu a).G.obj T),
      ∀ α T, Vk q U a α T → Vk p W a (τ α) ((morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG).G.obj T) := by
  first | exact @GlobalTheory.CompanionTheory.OmGlobPush.push_kc | exact GlobalTheory.CompanionTheory.OmGlobPush.push_kc | (intros; apply GlobalTheory.CompanionTheory.OmGlobPush.push_kc <;> assumption)
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite GlobalTheory.CechDR GlobalTheory.HodgeCoh

namespace GlobalTheory.CompanionTheory.FormsGlue

section Alg

variable {K : Type} [CommRing K] {A B : Type} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

theorem omMap_eq_mOm (φ : A →ₐ[K] B) (h : SemiHom (RingHom.id K) (φ : A →+* B)) (a : ℕ) (ω : CrystallineSemistableComparison.Onto.Om K A a) :
    CrystallineSemistableComparison.Onto.omMap φ a ω = h.mOm a ω := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K A B := IsScalarTower.of_algHom φ
  have hs : ∀ (c : A) (x : CrystallineSemistableComparison.Onto.Om K A a), CrystallineSemistableComparison.Onto.omMap φ a (c • x) = φ c • CrystallineSemistableComparison.Onto.omMap φ a x := by
    intro c x
    have h' := map_smul (exteriorPower.alternatingMapLinearEquiv
      { ((exteriorPower.ιMulti B a (M := Ω[B⁄K])).toMultilinearMap.restrictScalars A).compLinearMap
          fun _ => KaehlerDifferential.map K K A B with
        map_eq_zero_of_eq' := fun v i j h hij =>
          (exteriorPower.ιMulti B a (M := Ω[B⁄K])).map_eq_zero_of_eq (fun k => KaehlerDifferential.map K K A B (v k))
            (congrArg _ h) hij } : CrystallineSemistableComparison.Onto.Om K A a →ₗ[A] CrystallineSemistableComparison.Onto.Om K B a) c x
    exact h'.trans (algebraMap_smul B c _)
  have hι : ∀ g : Fin a → Ω[A⁄K], CrystallineSemistableComparison.Onto.omMap φ a (exteriorPower.ιMulti A a g) =
      h.mOm a (exteriorPower.ιMulti A a g) := by
    intro g
    have e1 : CrystallineSemistableComparison.Onto.omMap φ a (exteriorPower.ιMulti A a g) =
        exteriorPower.ιMulti B a fun k => KaehlerDifferential.map K K A B (g k) :=
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _
    rw [e1]
    refine Subtype.ext ?_
    rw [SemiHom.coe_mOm, exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe,
      ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
    congr 2
    funext k
    exact (congrArg ι1 (SemiHom.oneFormMap_eq_kaehlerDifferential_map h (fun _ => rfl) (g k))).symm.trans (SemiHom.mDR_ι h (g k)).symm
  have hmem : ω ∈ (⊤ : Submodule A (CrystallineSemistableComparison.Onto.Om K A a)) := Submodule.mem_top
  rw [← exteriorPower.ιMulti_span] at hmem
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact hι g
  | zero => rw [map_zero, map_zero]
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | smul c x _ hx => rw [hs, SemiHom.mOm_smul, hx]; rfl

end Alg

section Sch

variable {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

abbrev omSheaf (a : ℕ) : TopCat.Sheaf Ab X := ⟨(Omega q a).presheaf, (Omega q a).isSheaf⟩

theorem glue_core [IsAffine X] {ι : Type} (U : ι → X.Opens) (hcov : (⨆ α, U α) = ⊤) (a : ℕ) :
    (∀ ω ω' : OmU q ⊤ a, (∀ α, toOm q a (U α) (formRes q (le_top : U α ≤ ⊤) a ω) =
      toOm q a (U α) (formRes q (le_top : U α ≤ ⊤) a ω')) → ω = ω') ∧
    ∀ y : ∀ α, OmU q (U α) a,
      (∀ α β, formRes q (inf_le_left : U α ⊓ U β ≤ U α) a (y α) = formRes q (inf_le_right : U α ⊓ U β ≤ U β) a (y β)) →
      ∃ ω : OmU q ⊤ a, ∀ α, toOm q a (U α) (formRes q (le_top : U α ≤ ⊤) a ω) = toOm q a (U α) (y α) := by
  have hT : IsAffineOpen (⊤ : X.Opens) := isAffineOpen_top X
  refine ⟨fun ω ω' h => toOm_injective hT ?_, fun y hy => ?_⟩
  · refine TopCat.Sheaf.eq_of_locally_eq' (omSheaf q a) U ⊤ (fun α => homOfLE le_top) hcov.ge _ _ fun α => ?_
    exact (res_toOm q a le_top ω).trans ((h α).trans (res_toOm q a le_top ω').symm)
  · have hc : TopCat.Presheaf.IsCompatible (omSheaf q a).1 U (fun α => toOm q a (U α) (y α)) := fun α β =>
      (res_toOm q a inf_le_left (y α)).trans ((congrArg _ (hy α β)).trans (res_toOm q a inf_le_right (y β)).symm)
    obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' (omSheaf q a) U ⊤ (fun α => homOfLE le_top) hcov.ge
      (fun α => toOm q a (U α) (y α)) hc
    obtain ⟨ω, rfl⟩ := toOm_surjective hT t
    exact ⟨ω, fun α => (res_toOm q a le_top ω).symm.trans (ht α)⟩

theorem omMap_res {V W : X.Opens} (h : W ≤ V) (φ : CrystallineSemistableComparison.Onto.Sec q V →ₐ[K] CrystallineSemistableComparison.Onto.Sec q W)
    (hφ : ∀ g, φ g = (X.presheaf.map (homOfLE h).op).hom g) (a : ℕ)
    (ω : CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q V) a) : CrystallineSemistableComparison.Onto.omMap φ a ω = formRes q h a ω := by
  have e : φ = (Sec.res q h : GlobalTheory.CechDR.Sec q V →ₐ[K] GlobalTheory.CechDR.Sec q W) := AlgHom.ext hφ
  subst e
  exact omMap_eq_mOm _ (SemiHom.of_algHom (Sec.res q h)) a ω

end Sch

end GlobalTheory.CompanionTheory.FormsGlue

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

namespace GlobalTheory.CompanionTheory.FormsGlue

theorem forms_glue : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] {ι : Type}
    (U : ι → X.Opens), (∀ α, IsAffineOpen (U α)) → (⨆ α, U α) = ⊤ →
    ∀ (φ : ∀ α, CrystallineSemistableComparison.Onto.Sec q ⊤ →ₐ[K] CrystallineSemistableComparison.Onto.Sec q (U α))
      (ψ₁ : ∀ α β, CrystallineSemistableComparison.Onto.Sec q (U α) →ₐ[K] CrystallineSemistableComparison.Onto.Sec q (U α ⊓ U β))
      (ψ₂ : ∀ α β, CrystallineSemistableComparison.Onto.Sec q (U β) →ₐ[K] CrystallineSemistableComparison.Onto.Sec q (U α ⊓ U β)),
    (∀ α g, φ α g = (X.presheaf.map (homOfLE (le_top : U α ≤ ⊤)).op).hom g) →
    (∀ α β g, ψ₁ α β g = (X.presheaf.map (homOfLE (inf_le_left : U α ⊓ U β ≤ U α)).op).hom g) →
    (∀ α β g, ψ₂ α β g = (X.presheaf.map (homOfLE (inf_le_right : U α ⊓ U β ≤ U β)).op).hom g) → ∀ a : ℕ,
    Function.Injective (fun (ω : CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q ⊤) a) α => CrystallineSemistableComparison.Onto.omMap (φ α) a ω) ∧
    ∀ y : ∀ α, CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q (U α)) a,
      (∀ α β, CrystallineSemistableComparison.Onto.omMap (ψ₁ α β) a (y α) = CrystallineSemistableComparison.Onto.omMap (ψ₂ α β) a (y β)) →
      ∃ ω, ∀ α, CrystallineSemistableComparison.Onto.omMap (φ α) a ω = y α := by
  intro K _ X q _ ι U hU hcov φ ψ₁ ψ₂ hφ hψ₁ hψ₂ a
  have hc := glue_core q U hcov a
  refine ⟨fun ω ω' h => hc.1 ω ω' fun α => ?_, fun y hy => ?_⟩
  · have e := congrFun h α
    simp only [] at e
    rw [omMap_res q le_top (φ α) (hφ α), omMap_res q le_top (φ α) (hφ α)] at e
    exact congrArg _ e
  · obtain ⟨ω, hω⟩ := hc.2 y fun α β => by
      have e := hy α β
      rw [omMap_res q inf_le_left (ψ₁ α β) (hψ₁ α β), omMap_res q inf_le_right (ψ₂ α β) (hψ₂ α β)] at e
      exact e
    refine ⟨ω, fun α => ?_⟩
    rw [omMap_res q le_top (φ α) (hφ α)]
    exact toOm_injective (hU α) (hω α)

end GlobalTheory.CompanionTheory.FormsGlue
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory

namespace GlobalTheory.CompanionTheory.RelInjAbs

open CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Onto

section Cxs

variable {R : Type} [CommRing R]

end Cxs

section Abs

variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R} (m : CH.Mor F F' (RingHom.id R))
  {ι : Type} [DecidableEq ι]

theorem bij_res_of_eq {Ut V₁ V₂ : ObjectProperty C} (e : V₁ = V₂) {Q : ObjectProperty C} (hQ : Cosieve Q) (h₁ : V₁ ≤ Ut)
    (h₂ : V₂ ≤ Ut) (n : ℕ) (hb : Function.Bijective ((RC.res F hQ h₁).mapH n)) :
    Function.Bijective ((RC.res F hQ h₂).mapH n) := by
  subst e
  exact hb

theorem capU_empty (U : ι → ObjectProperty C) : (fun T => ∃ α, U α T) = capU U ∅ := by
  funext T
  exact propext ⟨fun h => ⟨h, fun α hα => absurd hα (Finset.notMem_empty α)⟩, fun h => h.1⟩

theorem capU_nonempty (U : ι → ObjectProperty C) (P : ObjectProperty C) (S : Finset ι) (hS : S.Nonempty)
    (h : ∀ T, P T ↔ ∀ α ∈ S, U α T) : capU U S = P := by
  funext T
  refine propext ⟨fun hT => (h T).2 hT.2, fun hT => ?_⟩
  obtain ⟨α, hα⟩ := hS
  exact ⟨⟨α, (h T).1 hT α hα⟩, (h T).1 hT⟩

end Abs

end GlobalTheory.CompanionTheory.RelInjAbs

namespace GlobalTheory.CompanionTheory.RelInjZ

open Limits AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.RelInjAbs

variable {K : Type} [Field K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z}
  {D : E.LineData Y} {d : ℕ}

theorem affine_inf (q : Z ⟶ Spec (CommRingCat.of K)) [IsSeparated q] {V V' : Z.Opens} (h : IsAffineOpen V) (h' : IsAffineOpen V') :
    IsAffineOpen (V ⊓ V') :=
  GlobalTheory.FinNear.isAffineOpen_preimage_inf_of_isSeparated_over (𝟙 Z) q (isAffineOpen_top (Spec (CommRingCat.of K))) h
    (fun _ _ => trivial) h' (fun _ _ => trivial)

theorem affine_finset_inf (q : Z ⟶ Spec (CommRingCat.of K)) [IsSeparated q] {κ : Type} (V : κ → Z.Opens) (S : Finset κ)
    (hS : S.Nonempty) (h : ∀ o ∈ S, IsAffineOpen (V o)) : IsAffineOpen (S.inf V) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact absurd hS Finset.not_nonempty_empty
  | insert a s ha ih =>
    rw [Finset.inf_insert]
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simpa using h a (by simp)
    · exact affine_inf q (h a (by simp)) (ih hs fun o ho => h o (Finset.mem_insert_of_mem ho))

theorem inU_finset_inf (hs : SiteLaws) (i : W ⟶ Z) {κ : Type} (V : κ → Z.Opens) (S : Finset κ) (T) :
    inU q (S.inf V) T ↔ ∀ o ∈ S, inU q (V o) T := by
  classical
  obtain ⟨-, -, htop, hinf, -, -⟩ := hs K W Z Z q i (𝟙 Z)
  induction S using Finset.induction_on with
  | empty => simpa using htop T
  | insert a s ha ih =>
    rw [Finset.inf_insert, hinf, ih]
    simp

end GlobalTheory.CompanionTheory.RelInjZ
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.SysBC

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} {P : Type} [SemilatticeInf P]

theorem exists_sec_equiv (h : IsPullback φ s' s (spMap (algebraMap R R'))) {U : X.Opens}
    (hU : IsAffineOpen U) :
    ∃ e : R' ⊗[R] Sec s U ≃ₗ[R'] Sec s' (φ ⁻¹ᵁ U),
      ∀ b, e (1 ⊗ₜ b) = (φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom b := by
  letI : Algebra (Sec s U) (Sec s' (φ ⁻¹ᵁ U)) := (φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  letI : Algebra R (Sec s' (φ ⁻¹ᵁ U)) :=
    ((algebraMap R' (Sec s' (φ ⁻¹ᵁ U))).comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' (Sec s' (φ ⁻¹ᵁ U)) := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower R (Sec s U) (Sec s' (φ ⁻¹ᵁ U)) :=
    .of_algebraMap_eq fun r ↦ (GlobalTheory.AbLaw.appLE_cst h.w le_rfl r).symm
  haveI hp : Algebra.IsPushout R R' (Sec s U) (Sec s' (φ ⁻¹ᵁ U)) :=
    CommRingCat.isPushout_iff_isPushout.mp (GlobalTheory.AbLaw.isPushout_cst h hU rfl)
  refine ⟨hp.out.equiv, fun b ↦ ?_⟩
  exact (hp.out.equiv_tmul 1 b).trans (one_smul _ _)

def pullSys (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P) : Sys X' P where
  u a := ⟨φ ⁻¹ᵁ (S.u a).1, GlobalTheory.AbLaw.isAffineOpen_preimage_of_isPullback h (S.u a).2⟩
  map_inf a b := by
    change φ ⁻¹ᵁ (S.u (a ⊓ b)).1 = φ ⁻¹ᵁ (S.u a).1 ⊓ φ ⁻¹ᵁ (S.u b).1
    rw [S.map_inf]; rfl
  cover := by
    change ⨆ a, φ ⁻¹ᵁ (S.u a).1 = ⊤
    rw [← Scheme.Hom.preimage_iSup, S.cover]; rfl

def pt (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P) (a : P) : Pair φ :=
  ⟨((pullSys h S).u a, S.u a), le_rfl⟩

theorem pt_mono (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P) :
    Monotone (pt h S) := fun _ _ hab ↦
  Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨(pullSys h S).mono hab, S.mono hab⟩)

def ptFn (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P) : Pᵒᵖ ⥤ (Pair φ)ᵒᵖ :=
  (pt_mono h S).functor.op

def ptRes (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P) :
    CoefMap (RingHom.id R') (OPair φ s') (OSys s' (pullSys h S)) where
  G := ptFn h S
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

def pullBC (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P) :
    BC (OSys s S) (OSys s' (pullSys h S)) where
  α T := secPull s s' (pt h S T.unop)
  naturality ψ b := (pairPull h.w).naturality ((ptFn h S).map ψ) b
  smul T r b := (pairPull h.w).smul (op (pt h S T.unop)) r b
  bij T := exists_sec_equiv h (S.u T.unop).2

theorem pull1_restrict_pair_pullback (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P)
    (c : HO1 s) : (ptRes h S).pull1 ((pairPull h.w).pull1 c) =
      (pullBC h S).coef.pull1 ((resSys s S).pull1 c) := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  rfl

theorem pull1_restrict_pair_restriction (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P)
    (c : HO1 s') : (ptRes h S).pull1 ((pairRes φ s').pull1 c) =
      (resSys s' (pullSys h S)).pull1 c := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  rfl

end GlobalTheory.CompanionTheory.SysBC


open GlobalTheory.CompanionTheory.SysBC in
theorem GlobalTheory.CompanionTheory.SysBC.sysBCSt : DescentSt → LowSt → SysBCSt := by
  intro hD hL R R' _ _ _ X X' s s' φ h hs P _ S
  have hs' : IsSeparated s' := MorphismProperty.of_isPullback (P := @IsSeparated) h hs
  refine ⟨pullSys h S, pullBC h S, fun c c' e ↦ ?_⟩
  have inj := (hL R' _ _ _ _ (resSys s' (pullSys h S)) (hD R' X' s' hs' P (pullSys h S))).1.1
  obtain ⟨x, hx⟩ := (pairRes_bijective φ s').1.2 ((pairPull h.w).pull1 c)
  have e' : x = c' := inj (by
    rw [← pull1_restrict_pair_restriction h S x, hx, pull1_restrict_pair_pullback, e])
  exact hx.symm.trans (congrArg _ e')
end
end

section

open Matrix
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.admitted

theorem isAdmissible_of_unitary_irreducible : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G →
    PositivityTheory.Tls2.Iua.AdmG G → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsURepOn G σ → Formalism.MainNotions.S.IsIrredOn G σ →
    GlobalTheory.LinRed.IsAdmOn G σ := by
  intro n G hG hA H _ _ _ σ hσ hirr
  refine ⟨hσ.1, hσ.2.2, fun k hk v => hσ.2.1 k hk.1 v, ?_⟩
  intro S hfd hS _
  haveI := hfd
  let b := Module.finBasis ℂ S
  choose Y hYfd _ hvY hY using fun i => hA H σ hσ hirr S hS (b i) (b i).2
  haveI : ∀ i, FiniteDimensional ℂ (Y i) := hYfd
  have hsup : FiniteDimensional ℂ (⨆ i, Y i : Submodule ℂ H) := Submodule.finiteDimensional_iSup Y
  refine Submodule.finiteDimensional_of_le (S₂ := ⨆ i, Y i) (sSup_le ?_)
  rintro _ ⟨Θ, rfl, hΘ⟩
  let T : H →L[ℂ] H := (LinearMap.toContinuousLinearMap (Θ.domRestrict S)).comp S.orthogonalProjectionOnto
  have hT : ∀ k ∈ GlobalTheory.LinRed.maxCpt G, ∀ u, T (σ k u) = σ k (T u) := by
    intro k hk u
    have hk1 : k * k.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.1 hk.2
    have hks : k.conjTranspose ∈ GlobalTheory.LinRed.maxCpt G := ⟨hG.star_mem k hk.1, Unitary.star_mem hk.2⟩
    have hiso : ∀ x y, ⟪σ k x, σ k y⟫_ℂ = ⟪x, y⟫_ℂ := fun x y =>
      (LinearIsometry.mk (σ k : H →ₗ[ℂ] H) (hσ.2.1 k hk.1)).inner_map_map x y
    have hP : ((S.orthogonalProjectionOnto (σ k u) : S) : H) = σ k (S.orthogonalProjectionOnto u : S) := by
      refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hS k hk _ (S.orthogonalProjectionOnto u).2) ?_
      intro w hw
      have hw' : σ k (σ k.conjTranspose w) = w := by
        rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 _ hk.1 _ hks.1, hk1, hσ.1.1]
        rfl
      rw [← hw', ← map_sub, hiso]
      exact S.starProjection_inner_eq_zero u _ (hS _ hks w hw)
    have h := hΘ k hk _ (S.orthogonalProjectionOnto u).2
    simpa [T, hP] using h
  rintro _ ⟨v, hv, rfl⟩
  have hv' : v = ((⟨v, hv⟩ : S) : H) := rfl
  rw [hv', ← b.sum_repr ⟨v, hv⟩]

  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem i ?_)
  have := hY i T hT _ (hvY i)
  simpa [T] using this

end GlobalTheory.CompanionTheory.admitted

end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open PositivityTheory.Rg.Mass

namespace GlobalTheory.CompanionTheory.Mass

theorem anisotropic_binary_one_vector_formula : Prop1 → Simil → Hasse → Cnt → E1 := by
  intro hP hS hH hC F E _ _ _ _ _ σ hcm J hJ hA T hT hd d b li lam hli hlam μ 𝓕 hμ h𝓕 mi m hmi hm
  obtain ⟨β, rfl, hβ, he⟩ := GlobalTheory.T.hermitian_one_by_one_is_scalar F E σ hcm T hT
  have hβ0 : β ≠ 0 := hβ hd
  simp only [he]
  have hsph : {X : Fin 1 → Fin 2 → E | gramE σ J X = fun _ _ => algebraMap F E β} = sph σ J β := rfl
  rw [hsph]
  obtain ⟨c, hc⟩ := hP F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm β hβ0
  by_cases h0 : mi (hermScal (Ainf F) σ (algebraMap F _ β)) = 0 ∨
      ∃ v, m v (hermScal (Fv F v) σ (algebraMap F _ β)) = 0
  · rw [(GlobalTheory.T.euler_product_measure_zero F E σ hcm d b 1 2 _ c _ _).2.1 hc h0]
    exact (GlobalTheory.T.euler_product_measure_zero F E σ hcm d b 1 2 0 1 _ _).2.2 hc.1 hc.2.1 h0
  push Not at h0
  have hne : (sph σ J β).Nonempty :=
    hH F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm β hβ0 h0.1
  have hall : ∀ β' : F, β' ≠ 0 → EP b μ 𝓕 mi m β' c := by
    intro β' hβ'
    by_cases hn : (sph σ J β').Nonempty
    · exact hS F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm β β' hβ0 hβ' hne hn c hc
    · obtain ⟨c', hc'⟩ := hP F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm β' hβ'
      have hz : mi (hermScal (Ainf F) σ (algebraMap F _ β')) = 0 := by
        by_contra hz
        exact hn (hH F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm β' hβ' hz)
      have ht : thetaMeas σ J μ 𝓕 (sph σ J β') = 0 := by
        have he' : IsEmpty (sph σ J β') := Set.not_nonempty_iff_eq_empty.1 hn ▸ inferInstance
        simp [thetaMeas]
      unfold EP
      rw [ht]
      exact (GlobalTheory.T.euler_product_measure_zero F E σ hcm d b 1 2 0 c _ _).2.2 hc'.1 hc'.2.1 (Or.inl hz)
  have h1 : c = 1 := hC F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm c hall
  exact h1 ▸ hc

end GlobalTheory.CompanionTheory.Mass
end

section

open CategoryTheory AlgebraicGeometry

theorem _root_.GlobalTheory.T.krull_dim_quotient_eq_trdeg_succ : ∀ (Y : Scheme.{0}) (B : Type) [CommRing B] [Algebra ℤ B] [Algebra.FiniteType ℤ B] (j : Spec (.of B) ⟶ Y) [IsOpenImmersion j] (q : PrimeSpectrum B), CharZero (Y.residueField (j q)) → ringKrullDim (B ⧸ q.asIdeal) = (((Algebra.trdeg ℤ (Y.residueField (j q))).toENat + 1 : ℕ∞) : WithBot ℕ∞) := by
  first | exact @GlobalTheory.CompanionTheory.DimChart.ringKrullDim_quotient_eq | exact GlobalTheory.CompanionTheory.DimChart.ringKrullDim_quotient_eq | (intros; apply GlobalTheory.CompanionTheory.DimChart.ringKrullDim_quotient_eq <;> assumption)
end
