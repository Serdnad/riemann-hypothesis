module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle451
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrystallineFormLiftDifferenceEqSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrobeniusOnTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2257
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1909
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1244
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2272
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2275
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
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
import Mathlib.RingTheory.LocalProperties.FinitePresentation
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

set_option autoImplicit false

namespace GlobalTheory.CechKS

theorem valR_comp_app {Y Z : Scheme.{0}} {S : Type} [CommRing S] (z : Sp S ⟶ Y) (m : Y ⟶ Z) (O : Z.Opens)
    (f : Γ(Z, O)) : valR (z ≫ m) O f = valR z (m ⁻¹ᵁ O) ((m.app O).hom f) := by
  by_cases h : ⊤ ≤ z ⁻¹ᵁ (m ⁻¹ᵁ O)
  · rw [valR_eq_ev _ _ h, valR_eq_ev (z ≫ m) O h, ← GlobalTheory.FlagMod.ev_appLE z m le_rfl h h, Scheme.Hom.appLE_eq_app]
  · rw [valR, valR, dif_neg h]
    exact dif_neg h

theorem le_preimage_of_red {Y : Scheme.{0}} {B : Type} [CommRing B] {x : Sp B ⟶ Y} {w : Sp (DualNumber B) ⟶ Y}
    (hw : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ w = x) {O : Y.Opens} (h : ⊤ ≤ x ⁻¹ᵁ O) : ⊤ ≤ w ⁻¹ᵁ O := by
  intro p _
  have hs : Function.Surjective (spMap (TrivSqZeroExt.fstHom B B B).toRingHom) := by
    intro q
    refine ⟨spMap (algebraMap B (DualNumber B)) q, ?_⟩
    refine PrimeSpectrum.ext (Ideal.ext fun c ↦ ?_)
    change algebraMap B (DualNumber B) c.fst ∈ q.asIdeal ↔ c ∈ q.asIdeal
    have hn : c - algebraMap B (DualNumber B) c.fst ∈ q.asIdeal := by
      refine q.isPrime.mem_of_pow_mem 2 ?_
      have : (c - algebraMap B (DualNumber B) c.fst) ^ 2 = 0 := by
        ext <;> simp [pow_two, TrivSqZeroExt.algebraMap_eq_inl]
      rw [this]; exact zero_mem _
    exact ⟨fun hc ↦ by simpa using add_mem hn hc, fun hc ↦ by simpa using sub_mem hc hn⟩
  obtain ⟨q, rfl⟩ := hs p
  have := h (Set.mem_univ q)
  rw [← hw] at this
  exact this

theorem valR_resG {Z : Scheme.{0}} {S : Type} [CommRing S] (z : Sp S ⟶ Z) {U V : Z.Opens} (e : V ≤ U)
    (h : ⊤ ≤ z ⁻¹ᵁ V) (a : Γ(Z, U)) : valR z V (resG Z e a) = valR z U a := by
  calc
    valR z V (resG Z e a) = GlobalTheory.FlagMod.ev z V h (resG Z e a) := valR_eq_ev z V h _
    _ = GlobalTheory.FlagMod.ev z U (GlobalTheory.FlagMod.le_preimage_mono e h) a :=
      GlobalTheory.FlagMod.ev_res z e h _ a
    _ = valR z U a := (valR_eq_ev z U _ a).symm

theorem isAffineHom_of_field {K : Type} [Field K] {X : Scheme.{0}} (x0 : Sp K ⟶ X) : IsAffineHom x0 := by
  refine ⟨fun U _ => ?_⟩
  by_cases h : (default : PrimeSpectrum K) ∈ x0 ⁻¹ᵁ U
  · have e : x0 ⁻¹ᵁ U = ⊤ := eq_top_iff.2 fun p _ => by
      rwa [Subsingleton.elim (α := PrimeSpectrum K) p default]
    rw [e]
    exact isAffineOpen_top _
  · have e : x0 ⁻¹ᵁ U = ⊥ := eq_bot_iff.2 fun p hp => by
      rw [Subsingleton.elim (α := PrimeSpectrum K) p default] at hp
      exact (h hp).elim
    rw [e]
    exact isAffineOpen_bot _

theorem IsChartPt.of_le {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))}
    {Z : Scheme.{0}} {m : A.left ⟶ Z} {m' : A'.left ⟶ Z} {W₀ : Z.Opens} {d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)}
    (hd : LogKS.IsField W₀ d) {Ω₀ Ω : Z.Opens} (h0 : Ω₀ ≤ Ω) (h1 : Ω ≤ W₀) {n : ℕ} {u : Fin n → (epsR K ⟶ A)}
    {θ : Matrix (Fin n) (Fin n) K} {Wo : A.left.Opens} {g : Γ(A.left, Wo)ˣ} {B : Type} [CommRing B]
    [Algebra (DualNumber K) B] {x : Sp B ⟶ A.left} {l : Sp B ⟶ A'.left} (hx : x ≫ A.hom = spMap (baseMap K B))
    (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω₀)) (hut : ∀ a, IsTangent (u a)) (hl : IsChartPt A' m m' Ω₀ (d Ω₀) u θ Wo g x l) :
    IsChartPt A' m m' Ω (d Ω) u θ Wo g x l := by
  obtain ⟨h₁, h₂, h₃⟩ := hl
  refine ⟨h₁, GlobalTheory.FlagMod.le_preimage_mono h0 h₂, fun f => ?_⟩
  have hxm : ⊤ ≤ (x ≫ m) ⁻¹ᵁ Ω₀ := hxΩ
  have hw : ∀ a, ⊤ ≤ (transl (baseMap K B) x (u a) ≫ m) ⁻¹ᵁ Ω₀ := fun a =>
    le_preimage_of_red ((isTransl_transl _ x hx (u a)).red (hut a)) hxΩ
  rw [← valR_resG _ h0 h₂, h₃, chartVal, chartVal, hd.2.2 Ω Ω₀ h0 h1, valR_resG _ h0 hxm, valR_resG _ h0 hxm]
  simp only [valR_resG _ h0 (hw _)]

end GlobalTheory.CechKS
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.InvForm

section Alg
variable {R C E : Type} [CommRing R] [CommRing C] [Algebra R C] [CommRing E] [Algebra R E]

theorem dVal_smul_left (φ : C →ₐ[R] DualNumber E) (c : C) (x : Ω[C⁄R]) :
    dVal φ (c • x) = (φ c).fst * dVal φ x := by
  letI : Algebra C E := (redHom φ).toAlgebra
  haveI : IsScalarTower R C E := IsScalarTower.of_algebraMap_eq fun r ↦ (redHom_algebraMap φ r).symm
  unfold dVal
  simp only [LinearMap.coe_restrictScalars]
  rw [LinearMap.map_smul]
  rfl

def semiDerHom (σ : C →ₐ[R] E) (θ : Ω[C⁄R] →ₗ[R] E) (hθ : ∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = σ c * θ x) :
    C →ₐ[R] DualNumber E where
  toFun c := TrivSqZeroExt.inl (σ c) + TrivSqZeroExt.inr (θ (KaehlerDifferential.D R C c))
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [hθ, MulOpposite.smul_eq_mul_unop]; ring
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  commutes' r := by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl']

theorem fst_semiDerHom (σ : C →ₐ[R] E) (θ : Ω[C⁄R] →ₗ[R] E) (hθ : ∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = σ c * θ x)
    (c : C) : (semiDerHom σ θ hθ c).fst = σ c := by simp [semiDerHom]

theorem dVal_semiDerHom (σ : C →ₐ[R] E) (θ : Ω[C⁄R] →ₗ[R] E) (hθ : ∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = σ c * θ x) :
    dVal (semiDerHom σ θ hθ) = θ := by
  refine LinearMap.ext fun x ↦ ?_
  induction x using GlobalTheory.CechDR.ind1 with
  | h b c =>
    rw [dVal_smul_left, dVal_D, hθ, fst_semiDerHom]
    simp [semiDerHom]
  | h0 => simp
  | ha x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

end Alg
end GlobalTheory.InvForm

namespace GlobalTheory.InvForm

theorem exists_transl_val : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (U V : AffOp A.left)
    (θ : Ω[Sec A.hom V.unop.1⁄R] →ₗ[R] Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1),
    (∀ (c : Sec A.hom V.unop.1) (x : Ω[Sec A.hom V.unop.1⁄R]), θ (c • x) = (1 ⊗ₜ c) * θ x) →
    ∃ ψ : Sec A.hom U.unop.1 →ₐ[R] DualNumber (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1),
      (∀ b, (ψ b).fst = b ⊗ₜ 1) ∧
      ∀ w : GlobalTheory.InvForm.InvForm A, θ (evForm A.hom V w.1) = GlobalTheory.InvForm.dVal ψ (evForm A.hom U w.1) := by
  intro R _ A _ U V θ hθ
  let T := Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1
  let σ : Sec A.hom V.unop.1 →ₐ[R] T := Algebra.TensorProduct.includeRight
  let τ : Sec A.hom U.unop.1 →ₐ[R] T := Algebra.TensorProduct.includeLeft
  have hθ' : ∀ (c : Sec A.hom V.unop.1) (x : Ω[Sec A.hom V.unop.1⁄R]), θ (c • x) = σ c * θ x := hθ
  let φ := semiDerHom σ θ hθ'
  let aV : Over.mk (spMap (algebraMap R (Sec A.hom V.unop.1))) ⟶ A :=
    Over.homMk (affPt A.hom V.unop) (affPt_w A.hom V.unop)
  let aU : Over.mk (spMap (algebraMap R (Sec A.hom U.unop.1))) ⟶ A :=
    Over.homMk (affPt A.hom U.unop) (affPt_w A.hom U.unop)
  let p := GlobalTheory.DeRham.spOver φ ≫ aV
  let x₀ := GlobalTheory.DeRham.spOver τ ≫ aU
  let y₀ := GlobalTheory.DeRham.spOver σ ≫ aV
  let q' := y₀⁻¹ * x₀
  let dualInclusion := TrivSqZeroExt.inlAlgHom R T T
  let dualProjection := TrivSqZeroExt.fstHom R T T
  let q := GlobalTheory.DeRham.spOver dualInclusion ≫ q'
  let red := GlobalTheory.DeRham.spOver dualProjection
  have h1 : red ≫ p = y₀ := by
    have hφ : dualProjection.comp φ = σ := AlgHom.ext fun c ↦ fst_semiDerHom σ θ hθ' c
    simp only [red, p, y₀, ← Category.assoc, GlobalTheory.DeRham.spOver_comp, hφ]
  have h2 : red ≫ q = q' := by
    have hsection : dualProjection.comp dualInclusion = AlgHom.id R T := AlgHom.ext fun _ ↦ rfl
    have hid : GlobalTheory.DeRham.spOver (AlgHom.id R T) = 𝟙 (Over.mk (spMap (algebraMap R T))) := by
      apply Over.OverMorphism.ext
      simp only [GlobalTheory.DeRham.spOver, Over.homMk_left, Over.id_left]
      exact Cris.spMap_id T
    simp only [red, q, ← Category.assoc, GlobalTheory.DeRham.spOver_comp, hsection, hid, Category.id_comp]
  have h3 : red ≫ (p * q) = x₀ := by
    rw [MonObj.comp_mul, h1, h2, mul_inv_cancel_left]
  have h3Left : spMap dualProjection.toRingHom ≫ (p * q).left = spMap τ.toRingHom ≫ affPt A.hom U.unop := by
    simpa only [Over.comp_left, red, x₀, aU, GlobalTheory.DeRham.spOver, Over.homMk_left,
      AlgHom.toRingHom_eq_coe]
      using congrArg (fun f ↦ f.left) h3
  have htop : ⊤ ≤ (p * q).left ⁻¹ᵁ U.unop.1 := by
    have hsurj : Function.Surjective (spMap dualProjection.toRingHom) :=
      GlobalTheory.PtExt.surjective_spMap_of_sq _ TrivSqZeroExt.fst_surjective fun a ha ↦ by
        have ha' : a.fst = 0 := ha
        ext <;> simp [ha']
    intro x _
    obtain ⟨t, rfl⟩ := hsurj x
    change ((spMap dualProjection.toRingHom ≫ (p * q).left).base t) ∈ U.unop.1
    rw [h3Left]
    change U.unop.2.fromSpec.base ((spMap τ.toRingHom).base t) ∈ U.unop.1
    exact (Set.ext_iff.mp U.unop.2.range_fromSpec _).1 ⟨_, rfl⟩
  have hs : (p * q).left ≫ A.hom = spMap (algebraMap R (DualNumber T)) := Over.w (p * q)
  let ψ := GlobalTheory.CechKS.FormLocal.valHom (s := A.hom) (U := U.unop.1) (p * q).left htop hs
  have hψ : spMap ψ.toRingHom ≫ affPt A.hom U.unop = (p * q).left :=
    GlobalTheory.CechKS.FormLocal.valHom_pt U.unop.2 _ htop hs
  have hfst : dualProjection.toRingHom.comp ψ.toRingHom = τ.toRingHom := by
    apply GlobalTheory.CechKS.FormLocal.ringHom_ext_affPt (s := A.hom) U.unop.2
    change spMap _ ≫ affPt A.hom U.unop = spMap _ ≫ affPt A.hom U.unop
    rw [Cris.spMap_comp, Category.assoc, hψ]
    exact h3Left
  refine ⟨ψ, fun b ↦ RingHom.congr_fun hfst b, fun w ↦ ?_⟩
  have hp : p.left = spMap φ.toRingHom ≫ affPt A.hom V.unop := by
    simp only [p, aV, Over.comp_left, GlobalTheory.DeRham.spOver, Over.homMk_left, AlgHom.toRingHom_eq_coe]
  have hq : q.left = spMap (algebraMap T (DualNumber T)) ≫ q'.left := by
    have hι : (dualInclusion : T →+* DualNumber T) = algebraMap T (DualNumber T) := RingHom.ext fun _ ↦ rfl
    simp only [q, Over.comp_left, GlobalTheory.DeRham.spOver, Over.homMk_left, hι]
  have key := w.2 T V.unop U.unop φ ψ p q q'.left hp hq hψ.symm
  rw [dVal_semiDerHom] at key
  exact key

end GlobalTheory.InvForm
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.InvFormProj

theorem finite_projective_of_locally_projective (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (h : ∀ q : PrimeSpectrum R, ∃ r : R, r ∉ q.asIdeal ∧ ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F)
      (_ : Module (Localization.Away r) F) (_ : IsScalarTower R (Localization.Away r) F)
      (_ : Module.Finite (Localization.Away r) F) (_ : Module.Projective (Localization.Away r) F)
      (ϕ : M →ₗ[R] F), IsBaseChange (Localization.Away r) ϕ) :
    Module.Finite R M ∧ Module.Projective R M := by
  let s : Set R := {r | ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F)
    (_ : Module (Localization.Away r) F) (_ : IsScalarTower R (Localization.Away r) F)
    (_ : Module.Finite (Localization.Away r) F) (_ : Module.Projective (Localization.Away r) F)
    (ϕ : M →ₗ[R] F), IsBaseChange (Localization.Away r) ϕ}
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr, hP⟩ := h ⟨m, hm.isPrime⟩
    exact hr (hsm (Ideal.subset_span hP))
  have hg : ∀ g : s, g.1 ∈ s := fun g => g.2
  choose F iA iM iL iT iFin iProj ϕ hϕ using hg
  letI := iA
  letI := iM
  letI := iL
  haveI := iT
  haveI := iFin
  haveI := iProj
  haveI (g : s) : IsLocalizedModule (Submonoid.powers g.1) (ϕ g) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers g.1) (Localization.Away g.1) (ϕ g)).2 (hϕ g)
  haveI (g : s) : Module.Flat R (F g) := by
    haveI : Module.Flat R (Localization.Away g.1) :=
      IsLocalization.flat _ (Submonoid.powers g.1)
    exact Module.Flat.trans R (Localization.Away g.1) (F g)
  haveI hfp : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_localizationSpan' s hs (Mₚ := F)
      (Rₚ := fun g : s => Localization.Away g.1) ϕ
      fun _ => Module.finitePresentation_of_projective _ _
  haveI : Module.Flat R M :=
    Module.flat_of_isLocalized_span R M s hs F ϕ fun _ => inferInstance
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

theorem finite_projective : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (∀ U : AffOp A.left, IsBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (GlobalTheory.InvForm.InvForm A).subtype)) → Module.Finite R (GlobalTheory.InvForm.InvForm A) ∧ Module.Projective R (GlobalTheory.InvForm.InvForm A) := by
  intro R _ A _ g _ hsm hbc
  haveI : SmoothOfRelativeDimension g A.hom := hsm
  haveI : Smooth A.hom := SmoothOfRelativeDimension.smooth g A.hom
  apply finite_projective_of_locally_projective
  intro q
  let e : Spec (CommRingCat.of R) ⟶ A.left := η[A].left
  have he : e ≫ A.hom = 𝟙 _ := by simp [e]
  obtain ⟨V, hV, hqV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp A.left.isBasis_affineOpens)
    (show e q ∈ (⊤ : A.left.Opens) from trivial)
  obtain ⟨_, ⟨r, rfl⟩, hr, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := q) (u := (e ⁻¹ᵁ V).1) hqV (e ⁻¹ᵁ V).2
  refine ⟨r, hr, ?_⟩
  let y : Sp (Localization.Away r) ⟶ A.left := spMap (algebraMap R (Localization.Away r)) ≫ e
  have hy : ⊤ ≤ y ⁻¹ᵁ V := by
    intro t _
    have : PrimeSpectrum.comap (algebraMap R (Localization.Away r)) t ∈
        (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact ⟨t, rfl⟩
    exact hsub this
  have hs : y ≫ A.hom = spMap (algebraMap R (Localization.Away r)) := by
    simp only [y, Category.assoc, he, Category.comp_id]
  let φ := GlobalTheory.CechKS.FormLocal.valHom (s := A.hom) (U := V) y hy hs
  letI : Algebra (Sec A.hom V) (Localization.Away r) := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R (Sec A.hom V) (Localization.Away r) :=
    IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  haveI : Algebra.Smooth R (Sec A.hom V) := smooth_sec_affine A.hom ⟨V, hV⟩
  have hb := hbc (Opposite.op ⟨V, hV⟩)
  exact ⟨Localization.Away r ⊗[Sec A.hom V] Ω[Sec A.hom V⁄R], inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, _,
    hb.comp (TensorProduct.isBaseChange (Sec A.hom V) Ω[Sec A.hom V⁄R] (Localization.Away r))⟩

end GlobalTheory.InvFormProj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Hecke


open GlobalTheory.AbDual GlobalTheory.CechPic in
theorem evc_pow_left {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) {P : LB (A ⊗ A).left}
    (hP : P.IsLB) (h₁ : GlobalTheory.AbLaw.Triv (ev P (1 : A ⟶ A) (𝟙 A))) (h₂ : GlobalTheory.AbLaw.Triv (ev P (𝟙 A) (1 : A ⟶ A)))
    {Y : Over S} (a t : Y ⟶ A) (n : ℕ) : evc hP (a ^ n) t = n • evc hP a t := by
  have hadd := (isAdditive_iff hP).1 (additive_of_cube GlobalTheory.CubeTop.cubeTheorem hA hA hP h₁ h₂).1
  induction n with
  | zero =>
    rw [pow_zero, zero_smul]
    exact (additive_of_cube GlobalTheory.CubeTop.cubeTheorem hA hA hP h₁ h₂).1.evc_one hP t
  | succ n ih => rw [pow_succ, hadd, ih, succ_nsmul]

theorem kernel_descent : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A') (G : Subgroup (𝟙_ (Over S) ⟶ o.A)), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ (m : ℕ), m.Coprime p → ∀ (P' : LB (G2 A').left), P'.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  intro p _ D R _ b M S s o A' _ _ ψ G _ hψ hG m hm P' hP' hiso
  obtain ⟨e₀, he₀, hker⟩ := o.kerP
  refine ⟨m * e₀, Nat.Coprime.mul_left hm he₀, ?_⟩
  intro T x hx
  have := hG.etale
  have := hG.fin
  have := hG.onto

  let T' : Over S := Over.mk (pullback.fst x.left ψ.left ≫ T.hom)
  let π' : T' ⟶ T := Over.homMk (pullback.fst x.left ψ.left) rfl
  let y : T' ⟶ o.A := Over.homMk (pullback.snd x.left ψ.left) (by
    show pullback.snd x.left ψ.left ≫ o.A.hom = pullback.fst x.left ψ.left ≫ T.hom
    rw [← Over.w ψ, ← Category.assoc, ← pullback.condition, Category.assoc, Over.w x])
  have hy : y ≫ ψ = π' ≫ x := Over.OverMorphism.ext (by
    show pullback.snd x.left ψ.left ≫ ψ.left = pullback.fst x.left ψ.left ≫ x.left
    exact pullback.condition.symm)

  have hP := o.isLB
  have hPm : (lbPow o.P m).IsLB := LB.isLB_linComb hP _ _
  have hc : GlobalTheory.CechPic.cls _ hPm = m • GlobalTheory.CechPic.cls o.P hP := by
    refine (GlobalTheory.CechPic.cls_linComb hP (K := Fin m) (fun _ => 𝟙 _) (fun _ => 1) hPm).trans ?_
    simp only [GlobalTheory.CechPic.pull_id, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hc' : GlobalTheory.CechPic.cls _ hPm = GlobalTheory.CechPic.pull (sq2 ψ) (GlobalTheory.CechPic.cls P' hP') :=
    (GlobalTheory.CechPic.cls_eq_iff hPm (pull_isLB hP' _)).2 hiso
  have h0 : GlobalTheory.AbDual.evc hP' (snd A' T ≫ x) (fst A' T) = 0 := (GlobalTheory.AbDual.triv_ev_iff hP' _ _).1 hx
  have h1 := congrArg (GlobalTheory.CechPic.pull (lift (fst o.A T' ≫ ψ) (snd o.A T' ≫ π')).left) h0
  rw [GlobalTheory.AbDual.pull_evc, map_zero, lift_snd_assoc, lift_fst, Category.assoc, ← hy] at h1
  have e2 : GlobalTheory.AbDual.evc hP' (snd o.A T' ≫ y ≫ ψ) (fst o.A T' ≫ ψ) =
      GlobalTheory.CechPic.pull (lift (snd o.A T' ≫ y) (fst o.A T')).left (GlobalTheory.CechPic.pull (sq2 ψ) (GlobalTheory.CechPic.cls P' hP')) := by
    rw [← GlobalTheory.CechPic.pull_comp, GlobalTheory.AbDual.evc, sq2, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc,
      Category.assoc]
  rw [e2, ← hc', hc, map_nsmul] at h1
  have h3 : GlobalTheory.AbDual.evc hP (snd o.A T' ≫ y ^ m) (fst o.A T') = 0 := by
    rw [comp_pow, evc_pow_left o.ab hP o.rig₁ o.rig₂]
    exact h1
  have h4 := hker T' (y ^ m) ((GlobalTheory.AbDual.triv_ev_iff hP _ _).2 h3)
  rw [← pow_mul] at h4
  have h5 : π' ≫ x ^ (m * e₀) = π' ≫ 1 := by
    rw [comp_pow, ← hy, ← GlobalTheory.SS.FrobTorsion.pow_comp' ψ y, h4, MonObj.one_comp, MonObj.comp_one]
  apply Over.OverMorphism.ext
  have h6 := congrArg (fun f => f.left) h5
  simp only [Over.comp_left] at h6
  exact (cancel_epi (pullback.fst x.left ψ.left)).1 h6

end GlobalTheory.UPel.HT.Hecke
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_doubledPairWeilDatum_schrodingerTransport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∃ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd ∧
          ∃ omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (GlobalTheory.DblSchr.JBd S JB)) →*
              Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.DblSchr.ddr co) ωd omd₀ := by
  first | exact @GlobalTheory.DblSchr.exists_dbl_weilDatum_transport | exact GlobalTheory.DblSchr.exists_dbl_weilDatum_transport | (intros; apply GlobalTheory.DblSchr.exists_dbl_weilDatum_transport <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.transportedWeilDatum_isUnitary_adelicSchwartz : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om → GlobalTheory.WeilM.IsUnitaryOn (GlobalTheory.WeilM.adeleClass D.host.F) om := by
  first | exact @GlobalTheory.WeilUnitaryTransport.isUnitaryOn_transport | exact GlobalTheory.WeilUnitaryTransport.isUnitaryOn_transport | (intros; apply GlobalTheory.WeilUnitaryTransport.isUnitaryOn_transport <;> assumption)
end
