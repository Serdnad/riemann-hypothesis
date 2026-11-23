module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle046
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle155
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle669
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.GalAut

section General

variable {o Ω₁ Ω₂ : Type} [CommRing o] [Field Ω₁] [Algebra o Ω₁] [Field Ω₂] [Algebra o Ω₂]
  {M₁ : RatModel o Ω₁} {N : RatModel o Ω₂} {φ : Ω₁ →ₐ[o] Ω₂} {q : N.Z ⟶ M₁.Z} [IsFinite q]

theorem map_ringOn (hf : M₁.IsHom N φ q) (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.Z) (τ : Ω₂ →ₐ[o] Ω₂) (hτ : ∀ a, τ (φ a) = φ a)
    {U₀ : M₁.Z.Opens} (hU₀ : IsAffineOpen U₀) (hne : ((q ⁻¹ᵁ U₀ : N.Z.Opens) : Set N.Z).Nonempty) :
    ∀ x ∈ N.ringOn ((q ⁻¹ᵁ U₀ : N.Z.Opens) : Set N.Z), τ x ∈ N.ringOn ((q ⁻¹ᵁ U₀ : N.Z.Opens) : Set N.Z) := by
  intro x hx
  obtain ⟨f, rfl⟩ := (RatModel.mem_ringOn_iff_exists hne).1 hx
  refine RatModel.mem_ringOn.2 fun z hz => ?_
  have hzU : q z ∈ U₀ := hz
  haveI := RatModel.isIntegrallyClosed_O hn z
  letI : Algebra Γ(M₁.Z, U₀) Γ(N.Z, q ⁻¹ᵁ U₀) := (q.app U₀).hom.toAlgebra
  have hi : IsIntegral Γ(M₁.Z, U₀) f := (IsFinite.finite_app q U₀ hU₀).to_isIntegral f
  have hmem : ∀ a : Γ(M₁.Z, U₀), φ.toRingHom (M₁.res U₀ ⟨_, hzU⟩ a) ∈ N.O z := fun a => by
    have e : φ.toRingHom (M₁.res U₀ ⟨_, hzU⟩ a) = φ (valF M₁.pt U₀ a) := congrArg φ (M₁.res_apply _ _ a)
    rw [e]
    exact hf.map_mem_O (z := z) (RatModel.valF_mem_O hzU a)
  let χ : Γ(M₁.Z, U₀) →+* N.O z :=
    RingHom.codRestrict (φ.toRingHom.comp (M₁.res U₀ ⟨_, hzU⟩)) (N.O z) hmem
  let ψ : Γ(N.Z, q ⁻¹ᵁ U₀) →+* Ω₂ := τ.toRingHom.comp (N.res (q ⁻¹ᵁ U₀) hne)
  have hc : (algebraMap (N.O z) Ω₂).comp χ = ψ.comp (algebraMap Γ(M₁.Z, U₀) Γ(N.Z, q ⁻¹ᵁ U₀)) := by
    ext a
    have e := hf.valF_app ⟨_, hzU⟩ a
    change φ (M₁.res U₀ ⟨_, hzU⟩ a) = τ (N.res (q ⁻¹ᵁ U₀) hne ((q.app U₀).hom a))
    calc φ (M₁.res U₀ ⟨_, hzU⟩ a) = φ (valF M₁.pt U₀ a) := congrArg φ (M₁.res_apply _ _ a)
      _ = τ (φ (valF M₁.pt U₀ a)) := (hτ _).symm
      _ = τ (valF N.pt (q ⁻¹ᵁ U₀) (q.app U₀ a)) := congrArg τ e.symm
      _ = τ (N.res (q ⁻¹ᵁ U₀) hne ((q.app U₀).hom a)) := congrArg τ (N.res_apply _ _ _).symm
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hi.map_of_comp_eq χ ψ hc)
  have e2 : ψ f = τ (valF N.pt (q ⁻¹ᵁ U₀) f) := congrArg τ (N.res_apply _ _ f)
  have e3 : τ (valF N.pt (q ⁻¹ᵁ U₀) f) = (w : Ω₂) := e2.symm.trans hw.symm
  rw [e3]
  exact w.2

theorem exists_isHom (hf : M₁.IsHom N φ q) (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.Z) (τ : Ω₂ →ₐ[o] Ω₂)
    (hτ : ∀ a, τ (φ a) = φ a) : ∃ s : N.Z ⟶ N.Z, N.IsHom N τ s := by
  refine RatModel.exists_isHom_of_local fun z => ?_
  obtain ⟨U₀, hU₀, hz, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : M₁.Z.Opens)) (x := q z) trivial
  exact ⟨q ⁻¹ᵁ U₀, q ⁻¹ᵁ U₀, hz, hU₀.preimage q, ⟨z, hz⟩, map_ringOn hf hn τ hτ hU₀ ⟨z, hz⟩⟩

end General

section Over

variable {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂]
  [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] [Algebra o₁ Ω₂]

def overBase (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z) [IsFinite q]
    (hq : M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt)
    (hA : algebraMap o₁ Ω₂ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)) : RatModel o₁ Ω₂ where
  Z := M₂.Z
  s := q ≫ M₁.s
  sep := by haveI := M₁.sep; infer_instance
  lft := by haveI := M₁.lft; infer_instance
  qc := by haveI := M₁.qc; infer_instance
  pt := M₂.pt
  pt_s := by
    rw [← Category.assoc, hq, Category.assoc, M₁.pt_s, hA]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  gen := M₂.gen
  onto := M₂.onto

def incl (hA : algebraMap o₁ Ω₂ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)) : Ω₁ →ₐ[o₁] Ω₂ :=
  { algebraMap Ω₁ Ω₂ with commutes' := fun r => by rw [hA]; rfl }

theorem autO_comm (hA : algebraMap o₁ Ω₂ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)) (σ : Ω₂ ≃ₐ[Ω₁] Ω₂)
    (r : o₁) : σ (algebraMap o₁ Ω₂ r) = algebraMap o₁ Ω₂ r := by
  rw [hA]
  exact σ.commutes (algebraMap o₁ Ω₁ r)

def autO (hA : algebraMap o₁ Ω₂ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)) (σ : Ω₂ ≃ₐ[Ω₁] Ω₂) :
    Ω₂ →ₐ[o₁] Ω₂ :=
  { (σ : Ω₂ →+* Ω₂) with commutes' := fun r => autO_comm hA σ r }

theorem autO_apply (hA : algebraMap o₁ Ω₂ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)) (σ : Ω₂ ≃ₐ[Ω₁] Ω₂)
    (x : Ω₂) : autO hA σ x = σ x := rfl

end Over

theorem autAct : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₂.Z → IsFinite q → M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ σ : Ω₂ ≃ₐ[Ω₁] Ω₂, ∃ s : M₂.Z ⟶ M₂.Z, M₂.pt ≫ s = spMap (σ : Ω₂ →+* Ω₂) ≫ M₂.pt ∧ s ≫ q = q ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ M₂.Z) (b : Ω₂), M₂.val (y ≫ s) b = M₂.val y (σ b) := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ _ M₁ M₂ q hn hfin hq σ
  haveI := hfin
  letI : Algebra o₁ Ω₂ := ((algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)).toAlgebra
  have hA : algebraMap o₁ Ω₂ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁) := rfl
  let N := overBase M₁ M₂ q hq hA
  haveI hfN : IsFinite (show N.Z ⟶ M₁.Z from q) := hfin
  have hqN : M₁.IsHom N (incl hA) q := hq
  have hnN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.Z := hn
  obtain ⟨s, hs⟩ := exists_isHom hqN hnN (autO hA σ) fun a => σ.commutes a
  obtain ⟨t, ht⟩ := exists_isHom hqN hnN (autO hA σ.symm) fun a => σ.symm.commutes a
  have hst : s ≫ t = 𝟙 N.Z := by
    have h1 := ht.comp hs
    have e : (autO hA σ).comp (autO hA σ.symm) = AlgHom.id o₁ Ω₂ := by
      ext x
      exact σ.apply_symm_apply x
    rw [e] at h1
    exact h1.unique (RatModel.isHom_id N)
  have hsq : s ≫ q = q := by
    have h1 := hqN.comp hs
    have e : (autO hA σ).comp (incl hA) = incl hA := by
      ext a
      exact σ.commutes a
    rw [e] at h1
    exact h1.unique hqN
  refine ⟨s, hs, hsq, fun K _ y b => ?_⟩
  let w : Sp K := IsLocalRing.closedPoint K
  have hts : ∀ z, t (s z) = z := fun z => by
    rw [← Scheme.Hom.comp_apply, hst]
    rfl
  by_cases hb : b ∈ N.O (s (y w))
  · exact hs.val_comp y w hb
  · have hb' : σ b ∉ N.O (y w) := by
      intro h
      apply hb
      have h2 := ht.map_mem_O (z := s (y w)) (x := σ b) (by
        have e : N.O (t (s (y w))) = N.O (y w) := congrArg N.O (hts (y w))
        rw [e]; exact h)
      simpa [autO_apply] using h2
    have e1 : M₂.val (y ≫ s) b = 0 := RatModel.val_of_notMem (M := N) (y := y ≫ s) w hb
    have e2 : M₂.val y (σ b) = 0 := RatModel.val_of_notMem (M := N) (y := y) w hb'
    rw [e1, e2]

end GlobalTheory.Poinc.GalAut
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc.EqNormAt

theorem spectrumMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem norm_val_eqAt : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (D : GlobalTheory.EffCartierData M.Z) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ϖ : V) (a : ℕ) (ξ : Sp V ⟶ M.Z) (p : ℕ) [Fact p.Prime] (ι : FractionRing V →+* PadicAlgCl p) (j : V →+* OO p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → (∀ v, (j v : PadicAlgCl p) = ι (algebraMap V (FractionRing V) v)) → idlAlong D.idealSheaf ξ = Ideal.span {ϖ ^ a} → ∀ f, EqAt M D (ξ (closedPoint V)) f → ‖M.val (gPt p ≫ spMap j ≫ ξ) f‖ = ‖ι (algebraMap V (FractionRing V) ϖ)‖ ^ a := by
  intro o Ω _ _ _ M D V _ _ _ ϖ a ξ p _ ι j hι hj hid f hf
  obtain ⟨i, hxi, rfl⟩ := hf
  set z := ξ (closedPoint V) with hz
  set e : V := (Scheme.stalkClosedPointTo ξ).hom ((M.Z.presheaf.germ _ z hxi).hom (D.f i)) with he
  have key : Ideal.span {e} = Ideal.span {ϖ ^ a} := by
    rw [← hid, idlAlong, D.stalkId_idealSheaf i z hxi, Ideal.map_span, Set.image_singleton]
  obtain ⟨u, hu⟩ := (Ideal.span_singleton_eq_span_singleton).1 key

  have hval : M.val (gPt p ≫ spMap j ≫ ξ) (valF M.pt (D.U i) (D.f i)) = ((j e : OO p) : PadicAlgCl p) := by
    rw [← Category.assoc, gPt, spectrumMap_comp, RatModel.val_spMap_comp _ ξ (specializes_rfl : z ⤳ z)
      ⟨valF M.pt (D.U i) (D.f i), RatModel.valF_mem_O hxi _⟩]
    have hv : M.valLoc ξ z specializes_rfl ⟨valF M.pt (D.U i) (D.f i), RatModel.valF_mem_O hxi _⟩ = e := by
      simp only [RatModel.valLoc, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        ← RatModel.stalkEquiv_germ hxi, RingEquiv.symm_apply_apply, TopCat.Presheaf.stalkSpecializes_refl,
        Category.id_comp, he]
      rw [Category.id_comp]
    rw [RingHom.comp_apply, hv]
    rfl
  rw [hval, hj]
  have hunit : ∀ w : Vˣ, ‖ι (algebraMap V (FractionRing V) (w : V))‖ = 1 := by
    intro w
    have h1 := (hι _).2 ⟨(w : V), rfl⟩
    have h2 := (hι _).2 ⟨((w⁻¹ : Vˣ) : V), rfl⟩
    have h3 : ‖ι (algebraMap V (FractionRing V) (w : V))‖ * ‖ι (algebraMap V (FractionRing V) ((w⁻¹ : Vˣ) : V))‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
    nlinarith [norm_nonneg (ι (algebraMap V (FractionRing V) (w : V))),
      norm_nonneg (ι (algebraMap V (FractionRing V) ((w⁻¹ : Vˣ) : V)))]
  have he' : e = ϖ ^ a * ((u⁻¹ : Vˣ) : V) := by
    rw [← hu, mul_assoc, Units.mul_inv, mul_one]
  rw [he', map_mul, map_mul, norm_mul, hunit, mul_one, map_pow, map_pow, norm_pow]

end GlobalTheory.Poinc.EqNormAt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.LabelLevel

theorem perV_add {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (M N M' N' : Fin g → ℤ) :
    perV τ (M + M') (N + N') = perV τ M N + perV τ M' N' := by
  have h : ∀ a b : Fin g → ℤ, cv (a + b) = cv a + cv b := fun a b => funext fun i => by simp [cv]
  simp only [perV, h, Matrix.mulVec_add]
  abel

theorem perV_smul {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (k : ℕ) (M N : Fin g → ℤ) :
    perV τ ((k : ℤ) • M) ((k : ℤ) • N) = (k : ℂ) • perV τ M N := by
  have h : ∀ a : Fin g → ℤ, cv ((k : ℤ) • a) = (k : ℂ) • cv a := fun a => funext fun i => by simp [cv]
  simp only [perV, h, Matrix.mulVec_smul, smul_add]

theorem prod_single {n k : ℕ} [NeZero k] (a : Fin n → ZMod k) :
    (List.ofFn fun i => (Multiplicative.ofAdd (Pi.single i 1 : Fin n → ZMod k)) ^ (a i).val).prod =
      Multiplicative.ofAdd a := by
  rw [List.prod_ofFn]
  simp only [← ofAdd_nsmul, ← ofAdd_sum]
  congr 1
  funext j
  simp [Finset.sum_apply, Pi.single_apply, -ZMod.natCast_val, ZMod.natCast_zmod_val]

theorem exists_level_of_labels : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (W : Fin g → Fin g → ℂ), NF x hg u τ a b c W → ∀ (k : ℕ), 0 < k → ∀ (ζ : ℂˣ), IsPrimitiveRoot ζ k → ∀ M Nn : (Fin (2 * g) → ZMod k) → Fin g → ℤ, ((∀ a a', ∃ M' N', M (a + a') = M a + M a' + (k : ℤ) • M' ∧ Nn (a + a') = Nn a + Nn a' + (k : ℤ) • N') ∧ (∀ a a' M' N', M a' = M a + (k : ℤ) • M' → Nn a' = Nn a + (k : ℤ) • N' → a = a') ∧ (∀ M₁ N₁, ∃ a M' N', M₁ = M a + (k : ℤ) • M' ∧ N₁ = Nn a + (k : ℤ) • N') ∧ ∀ i j, Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (cv (M (Pi.single i 1)) ⬝ᵥ cv (Nn (Pi.single j 1)) - cv (Nn (Pi.single i 1)) ⬝ᵥ cv (M (Pi.single j 1))) / k) = ((ζ ^ stdSymp g i j : ℂˣ) : ℂ)) → ∃ lev : Out.Level x.P k (unitOn ζ), ∀ a, (levelPoint lev hg a).left = (u.ex ((k : ℂ)⁻¹ • perV τ (M a) (Nn a))).left := by
  intro g x hg u τ a b c W hNF k hk ζ hζ M Nn ⟨hadd, _, _, hpair⟩
  subst hg
  obtain ⟨hs, hp, ha, hb, hc, hΛ, -, hfn, -⟩ := hNF
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have : NeZero k := ⟨hk.ne'⟩
  have hper : ∀ M' N', u.ex (perV τ M' N') = 1 := fun M' N' => (u.ker _).2 ((hΛ _).2 ⟨M', N', rfl⟩)
  let e : Multiplicative (Fin (2 * x.P.g) → ZMod k) →* (𝟙_ (Over (Sp ℂ)) ⟶ x.P.A) :=
    MonoidHom.mk' (fun s => u.ex ((k : ℂ)⁻¹ • perV τ (M s.toAdd) (Nn s.toAdd))) (fun s t => by
      obtain ⟨M', N', h1, h2⟩ := hadd s.toAdd t.toAdd
      rw [toAdd_mul, h1, h2, perV_add, perV_add, perV_smul, smul_add, smul_add, inv_smul_smul₀ hk', u.ex_add,
        u.ex_add, hper, _root_.mul_one])
  let f : Multiplicative (Fin (2 * x.P.g) → ZMod k) →* (baseOver (Sp ℂ) ⟶ x.P.A) := e
  have hcv : ∀ M' N' : Fin x.P.g → ℤ, perV τ M' N' = GlobalTheory.KeyFam.per τ (Sum.elim N' M') := fun M' N' => by
    rw [perV, add_comm]; rfl
  obtain ⟨lev, hlev⟩ := GlobalTheory.Ex.FibIso.exists_level GlobalTheory.abelianSchemeLaws_all.1 x.P rfl hk' hζ
    (fun i => f (Multiplicative.ofAdd (Pi.single i 1)))
    (fun i => by
      rw [← map_pow, ← ofAdd_nsmul, ← f.map_one]
      congr 2
      funext j
      simp)
    (fun i j => by
      have h := GlobalTheory.WeilStd.weilIs_per x _ u τ a b c rfl hs hp ⟨ha, hb⟩ hc hΛ hfn k
        (Sum.elim (Nn (Pi.single i 1)) (M (Pi.single i 1))) (Sum.elim (Nn (Pi.single j 1)) (M (Pi.single j 1)))
        (ζ ^ stdSymp x.P.g i j) hk (by
          rw [← hpair i j]
          congr 2
          simp only [omegaStd, cv, dotProduct, Sum.elim_inl, Sum.elim_inr, Finset.sum_sub_distrib]
          push_cast
          ring)
      rw [← hcv, ← hcv, show unitOn (ζ ^ stdSymp x.P.g i j) = unitOn ζ ^ stdSymp x.P.g i j from map_zpow _ _ _] at h
      exact h)
  refine ⟨lev, fun s => ?_⟩
  have h : levelPoint lev rfl s = f (Multiplicative.ofAdd s) := by
    rw [levelBasis_rfl] at hlev
    rw [levelPoint_rfl, Level.toPt, hlev, GlobalTheory.Ex.FibIso.linComb_map, prod_single]
  rw [h]
  rfl

end GlobalTheory.MBLow.LabelLevel

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem symTup_mul {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) (a : R) (j : Fin N) :
    symTup (fun b => a * c b) j = a ^ N.factorial * symTup c j := by
  have h : (Finset.univ.val.map fun b => a * c b) = (Finset.univ.val.map c).map (fun x => a • x) := by
    rw [Multiset.map_map]; rfl
  have hd : ((j : ℕ) + 1) ∣ N.factorial := Nat.dvd_factorial (Nat.succ_pos _) j.isLt
  unfold symTup
  rw [h, ← Multiset.pow_smul_esymm, smul_eq_mul, mul_pow, ← pow_mul, Nat.mul_div_cancel' hd]

theorem symTup_perm {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) (σ : Equiv.Perm (Fin N)) :
    symTup (fun b => c (σ b)) = symTup c := by
  have h : (Finset.univ.val.map fun b => c (σ b)) = Finset.univ.val.map c := by
    conv_rhs => rw [← Multiset.map_univ_val_equiv σ, Multiset.map_map]
    rfl
  funext j
  unfold symTup
  rw [h]

theorem map_symTup {R R' : Type} [CommRing R] [CommRing R'] (i : R →+* R') {N : ℕ} (c : Fin N → R) (j : Fin N) :
    i (symTup c j) = symTup (fun b => i (c b)) j := by
  have h : (Finset.univ.val.map fun b => i (c b)) = (Finset.univ.val.map c).map i := by
    rw [Multiset.map_map]; rfl
  unfold symTup
  rw [h, map_pow]
  congr 1
  simp only [Multiset.esymm, map_multiset_sum, Multiset.powersetCard_map, Multiset.map_map, Function.comp_def,
    map_multiset_prod]

theorem exists_symTup_ne_zero {K : Type} [Field K] {N : ℕ} (c : Fin N → K) (h : ∃ a, c a ≠ 0) :
    ∃ j, symTup c j ≠ 0 := by
  obtain ⟨a, ha⟩ := h
  by_contra hne
  push Not at hne
  have hc : Multiset.card (Finset.univ.val.map c) = N := by simp
  have he : ∀ k, 0 < k → k ≤ N → (Finset.univ.val.map c).esymm k = 0 := by
    intro k hk hkN
    have := hne ⟨k - 1, by omega⟩
    unfold symTup at this
    have h2 := eq_zero_of_pow_eq_zero this
    simpa [Nat.sub_add_cancel hk] using h2
  have hp : ((Finset.univ.val.map c).map fun t => Polynomial.X - Polynomial.C t).prod = Polynomial.X ^ N := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, hc, Finset.sum_range_succ']
    rw [Finset.sum_eq_zero]
    · simp [Multiset.esymm]
    · intro k hk
      rw [he (k + 1) (Nat.succ_pos _) (Finset.mem_range.1 hk)]
      simp
  have hev := congrArg (Polynomial.eval (c a)) hp
  rw [Polynomial.eval_multiset_prod, Multiset.prod_eq_zero] at hev
  · simp only [Polynomial.eval_pow, Polynomial.eval_X] at hev
    exact pow_ne_zero N ha hev.symm
  · simp only [Multiset.mem_map]
    exact ⟨_, ⟨c a, ⟨a, Finset.mem_univ_val a, rfl⟩, rfl⟩, by simp⟩

theorem symTup_basic :
    (∀ (R : Type) [CommRing R] (N : ℕ) (c : Fin N → R) (a : R) (j : Fin N),
      symTup (fun b => a * c b) j = a ^ N.factorial * symTup c j) ∧
    (∀ (R : Type) [CommRing R] (N : ℕ) (c : Fin N → R) (σ : Equiv.Perm (Fin N)),
      symTup (fun b => c (σ b)) = symTup c) ∧
    (∀ (R R' : Type) [CommRing R] [CommRing R'] (i : R →+* R') (N : ℕ) (c : Fin N → R) (j : Fin N),
      i (symTup c j) = symTup (fun b => i (c b)) j) ∧
    ∀ (K : Type) [Field K] (N : ℕ) (c : Fin N → K), (∃ a, c a ≠ 0) → ∃ j, symTup c j ≠ 0 :=
  ⟨fun _ _ _ c a j => symTup_mul c a j, fun _ _ _ c σ => symTup_perm c σ,
    fun _ _ _ _ i _ c j => map_symTup i c j, fun _ _ _ c h => exists_symTup_ne_zero c h⟩

end GlobalTheory.UMin
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

open Polynomial

private theorem symTup_mul_left {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) (a : R) (j : Fin N) :
    symTup (fun b => a * c b) j = a ^ N.factorial * symTup c j := by
  have h : (Finset.univ.val.map fun b => a * c b) = (Finset.univ.val.map c).map (fun x => a • x) := by
    rw [Multiset.map_map]; rfl
  have hd : ((j : ℕ) + 1) ∣ N.factorial := Nat.dvd_factorial (Nat.succ_pos _) j.isLt
  unfold symTup
  rw [h, ← Multiset.pow_smul_esymm, smul_eq_mul, mul_pow, ← pow_mul, Nat.mul_div_cancel' hd]

theorem symTup_eq_finite (K : Type) [Field K] (N : ℕ) (e : Fin N → K) :
    {c : Fin N → K | symTup c = e}.Finite := by
  classical

  let A : Fin (N + 1) → Set K := fun k =>
    {x | ((k : ℕ) = 0 → x = 1) ∧ ∀ j : Fin N, (j : ℕ) + 1 = k → x ^ (N.factorial / ((j : ℕ) + 1)) = e j}
  have hA : ∀ k, (A k).Finite := by
    intro k
    by_cases hk : (k : ℕ) = 0
    · exact (Set.finite_singleton (1 : K)).subset fun x hx => hx.1 hk
    · have hk1 : (k : ℕ) - 1 < N := by omega
      let j : Fin N := ⟨(k : ℕ) - 1, hk1⟩
      have hj : (j : ℕ) + 1 = k := by simp [j]; omega
      have hpos : 0 < N.factorial / ((j : ℕ) + 1) :=
        Nat.div_pos ((Nat.succ_le_of_lt j.isLt).trans (Nat.self_le_factorial N)) (Nat.succ_pos _)
      refine (Polynomial.finite_setOf_isRoot (X_pow_sub_C_ne_zero hpos (e j))).subset ?_
      intro x hx
      simp [IsRoot, hx.2 j hj]
  let V : Set (Fin (N + 1) → K) := Set.pi Set.univ A
  have hV : V.Finite := Set.Finite.pi hA
  let poly : (Fin (N + 1) → K) → K[X] := fun s =>
    ∑ k : Fin (N + 1), (-1) ^ (k : ℕ) * (C (s k) * X ^ (N - (k : ℕ)))
  let R : Set K := ⋃ p ∈ poly '' V, {x | x ∈ p.roots}
  have hR : R.Finite := (hV.image poly).biUnion fun p _ => Multiset.finite_toSet p.roots
  refine (Set.Finite.pi (t := fun _ : Fin N => R) fun _ => hR).subset ?_
  intro c hc
  simp only [Set.mem_setOf_eq] at hc
  let m : Multiset K := Finset.univ.val.map c
  have hm : Multiset.card m = N := by simp [m]
  let s : Fin (N + 1) → K := fun k => m.esymm k
  have hs : s ∈ V := by
    intro k _
    refine ⟨fun hk => ?_, fun j hj => ?_⟩
    · simp [s, hk, Multiset.esymm]
    · have := congrFun hc j
      simp only [symTup] at this
      simp only [s, ← hj]
      exact this
  have hpoly : poly s = (m.map fun t => X - C t).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, hm, Finset.sum_range (fun j => (-1) ^ j * (C (m.esymm j) * X ^ (N - j)))]
  intro a _
  simp only [R, Set.mem_iUnion, Set.mem_image]
  refine ⟨poly s, ⟨s, hs, rfl⟩, ?_⟩
  simp only [Set.mem_setOf_eq, hpoly, Polynomial.roots_multiset_prod_X_sub_C]
  exact Multiset.mem_map_of_mem c (Finset.mem_univ a)

theorem symTup_scale_finite : ∀ (K : Type) [Field K] [IsAlgClosed K] (N : ℕ) (e : Fin N → K), ∃ T : Finset (Fin N → K),
    ∀ (c : Fin N → K) (a : K), a ≠ 0 → (∀ j, symTup c j = a * e j) → ∃ mu : K, mu ≠ 0 ∧ (fun b => mu * c b) ∈ T := by
  intro K _ _ N e
  refine ⟨(symTup_eq_finite K N e).toFinset, ?_⟩
  intro c a ha hc
  obtain ⟨mu, hmu⟩ := IsAlgClosed.exists_pow_nat_eq a⁻¹ (Nat.factorial_pos N)
  have hmu0 : mu ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.factorial_pos N).ne'] at hmu
    exact inv_ne_zero ha hmu.symm
  refine ⟨mu, hmu0, ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  funext j
  rw [symTup_mul_left, hmu, hc, ← _root_.mul_assoc, inv_mul_cancel₀ ha, _root_.one_mul]

end GlobalTheory.UMin
end
end
