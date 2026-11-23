module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle157
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.GmSec

def gammaIso : yoneda.obj (Spec (CommRingCat.of (MvPolynomial Unit (ULift ℤ)))) ≅ Scheme.Γ ⋙ forget CommRingCat :=
  NatIso.ofComponents (fun U => Equiv.toIso
    ((AffineSpace.toSpecMvPolyIntEquiv Unit (X := U.unop)).trans (Equiv.funUnique Unit _))) (by
      intro U V f
      ext g
      rfl)


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct in
theorem _root_.GlobalTheory.EtC.GmSec.isSheaf_gamma :
    Presieve.IsSheaf Scheme.etaleTopology.{0} (Scheme.Γ ⋙ forget CommRingCat) :=
  Presieve.isSheaf_iso _ _root_.GlobalTheory.EtC.GmSec.gammaIso
    (Presieve.isSheaf_of_le _ Scheme.etaleTopology_le_proetaleTopology
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _))

abbrev uval {V : Scheme.{0}} (t : ((Scheme.Γ ⋙ unitsF) ⋙ forget (ModuleCat.{1} (ULift.{1} ℤ))).obj (op V)) : Γ(V, ⊤)ˣ :=
  Additive.toMul (ULift.down (α := Additive Γ(V, ⊤)ˣ) t)

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct in
private lemma gmSec_uval_map_eq_units_map {U V : Scheme.{0}} (g : V ⟶ U)
    (t : ((Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF) ⋙
      forget (ModuleCat.{1} (ULift.{1} ℤ))).obj (op U)) :
    _root_.GlobalTheory.EtC.GmSec.uval (((Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF) ⋙
        forget (ModuleCat.{1} (ULift.{1} ℤ))).map g.op t) =
      Units.map (Scheme.Γ.map g.op).hom.toMonoidHom (_root_.GlobalTheory.EtC.GmSec.uval t) :=
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct in
private lemma gmSec_eq_of_uval_eq {U : Scheme.{0}}
    (s s' : ((Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF) ⋙
      forget (ModuleCat.{1} (ULift.{1} ℤ))).obj (op U))
    (h : _root_.GlobalTheory.EtC.GmSec.uval s = _root_.GlobalTheory.EtC.GmSec.uval s') : s = s' := by
  cases s; cases s'; congr 1

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct in
private theorem isSheaf_etaleTopology_units :
    Presieve.IsSheaf Scheme.etaleTopology.{0}
      ((Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF) ⋙ forget (ModuleCat.{1} (ULift.{1} ℤ))) := by
  intro U S hS x hx
  have hG := _root_.GlobalTheory.EtC.GmSec.isSheaf_gamma S hS
  let a : Presieve.FamilyOfElements (Scheme.Γ ⋙ forget CommRingCat) S.arrows :=
    fun V f hf => ((_root_.GlobalTheory.EtC.GmSec.uval (x f hf) : Γ(V, ⊤)ˣ) : Γ(V, ⊤))
  let b : Presieve.FamilyOfElements (Scheme.Γ ⋙ forget CommRingCat) S.arrows :=
    fun V f hf => (((_root_.GlobalTheory.EtC.GmSec.uval (x f hf))⁻¹ : Γ(V, ⊤)ˣ) : Γ(V, ⊤))
  have ha : a.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
    exact congrArg (fun t => ((_root_.GlobalTheory.EtC.GmSec.uval t : Γ(Z, ⊤)ˣ) : Γ(Z, ⊤)))
      (hx g₁ g₂ h₁ h₂ w)
  have hb : b.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
    have := congrArg (fun t => (((_root_.GlobalTheory.EtC.GmSec.uval t)⁻¹ : Γ(Z, ⊤)ˣ) : Γ(Z, ⊤)))
      (hx g₁ g₂ h₁ h₂ w)
    simp only [gmSec_uval_map_eq_units_map, ← map_inv] at this
    exact this
  have hA := hG.isAmalgamation ha
  have hB := hG.isAmalgamation hb
  set A := hG.amalgamate a ha
  set B := hG.amalgamate b hb
  have hAB : A * B = 1 := by
    refine hG.isSeparatedFor.ext fun V f hf => ?_
    change (Scheme.Γ.map f.op).hom (A * B) = (Scheme.Γ.map f.op).hom 1
    rw [map_mul, map_one]
    change (Scheme.Γ ⋙ forget CommRingCat).map f.op A *
      (Scheme.Γ ⋙ forget CommRingCat).map f.op B = 1
    rw [hA f hf, hB f hf]
    exact (_root_.GlobalTheory.EtC.GmSec.uval (x f hf)).mul_inv
  have hBA : B * A = 1 := by rw [mul_comm, hAB]
  let u : Γ(U, ⊤)ˣ := ⟨A, B, hAB, hBA⟩
  refine ⟨⟨Additive.ofMul u⟩, fun V f hf => gmSec_eq_of_uval_eq _ _ (Units.ext (hA f hf)),
    fun t ht => gmSec_eq_of_uval_eq _ _ (Units.ext ?_)⟩
  refine hG.isSeparatedFor.ext fun V f hf => ?_
  change ((_root_.GlobalTheory.EtC.GmSec.uval (((Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF) ⋙
      forget (ModuleCat.{1} (ULift.{1} ℤ))).map f.op t) : Γ(V, ⊤)ˣ) : Γ(V, ⊤)) =
    (Scheme.Γ ⋙ forget CommRingCat).map f.op A
  rw [ht f hf, hA f hf]


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct in
theorem _root_.GlobalTheory.EtC.GmSec.gm_sec_bijective :
    ∀ U : Scheme.{0},
      Function.Bijective
        (_root_.GlobalTheory.EtC.ofRings.sec _root_.GlobalTheory.EtC.unitsF U) := by
  intro U
  have hP : Presheaf.IsSheaf Scheme.etaleTopology (Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF) :=
    (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).mpr
      ((isSheaf_iff_isSheaf_of_type _ _).mpr isSheaf_etaleTopology_units)
  haveI := isIso_toSheafify Scheme.etaleTopology hP
  delta _root_.GlobalTheory.EtC.ofRings.sec
  exact ConcreteCategory.bijective_of_isIso
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF)).app (op U))

end GlobalTheory.EtC.GmSec
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.cochain_shortExact_of_injective :
    ∀ (R : Type) [CommRing R] (I : _root_.GlobalTheory.EtC.Cx R), (∀ n, Injective (I.X n)) → ∀ (S : ShortComplex (_root_.GlobalTheory.EtC.Cx R)), S.ShortExact → ∀ n : ℤ, (∀ a : Cochain S.X₁ I n, ∃ b : Cochain S.X₂ I n, (Cochain.ofHom S.f).comp b (zero_add n) = a) ∧ (∀ b : Cochain S.X₂ I n, (Cochain.ofHom S.f).comp b (zero_add n) = 0 → ∃ c : Cochain S.X₃ I n, (Cochain.ofHom S.g).comp c (zero_add n) = b) ∧ ∀ c : Cochain S.X₃ I n, (Cochain.ofHom S.g).comp c (zero_add n) = 0 → c = 0 := by
  intro R _ I hI S hS n
  have hp : ∀ p : ℤ, (S.map (HomologicalComplex.eval _ _ p)).ShortExact :=
    fun p => hS.map_of_exact _
  have hmono : ∀ p : ℤ, Mono (S.f.f p) := fun p => (hp p).mono_f
  have hepi : ∀ p : ℤ, Epi (S.g.f p) := fun p => (hp p).epi_g
  refine ⟨fun a => ?_, fun b hb => ?_, fun c hc => ?_⟩
  · refine ⟨Cochain.mk (fun p q h => Injective.factorThru (a.v p q h) (S.f.f p)), ?_⟩
    ext p q h
    simp
  · have hb' : ∀ p q (h : p + n = q), S.f.f p ≫ b.v p q h = 0 := by
      intro p q h
      have := Cochain.congr_v hb p q h
      simpa using this
    refine ⟨Cochain.mk (fun p q h =>
      (CokernelCofork.IsColimit.desc' (hp p).gIsCokernel (b.v p q h) (hb' p q h)).1), ?_⟩
    refine Cochain.ext _ _ (fun p q h => ?_)
    simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.mk_v]
    exact (CokernelCofork.IsColimit.desc' (hp p).gIsCokernel (b.v p q h) (hb' p q h)).2
  · refine Cochain.ext _ _ (fun p q h => ?_)
    have := Cochain.congr_v hc p q h
    simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.zero_v] at this
    simpa using (cancel_epi (S.g.f p)).mp (this.trans (comp_zero).symm)

end GlobalTheory.EtC
end

section

noncomputable section

namespace GlobalTheory.SwapSlice

open GlobalTheory.WeilM

variable {k κ Y : Type}

def barL (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ) where
  toFun Φ := fun y => starRingEnd ℂ (ι (fun x => starRingEnd ℂ (Φ x)) y)
  map_add' Φ Ψ := by
    funext y
    have e : (fun x => starRingEnd ℂ ((Φ + Ψ) x)) = (fun x => starRingEnd ℂ (Φ x)) + fun x => starRingEnd ℂ (Ψ x) := by
      funext x; simp
    show starRingEnd ℂ (ι (fun x => starRingEnd ℂ ((Φ + Ψ) x)) y) = _
    rw [e, map_add (f := _), Pi.add_apply, map_add (f := _)]
    rfl
  map_smul' c Φ := by
    funext y
    have e : (fun x => starRingEnd ℂ ((c • Φ) x)) = starRingEnd ℂ c • fun x => starRingEnd ℂ (Φ x) := by
      funext x; simp
    show starRingEnd ℂ (ι (fun x => starRingEnd ℂ ((c • Φ) x)) y) = _
    rw [e, map_smul, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_conj]
    rfl

theorem barL_apply (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) (Φ : (κ → k) → ℂ) (y : Y) :
    barL ι Φ y = starRingEnd ℂ (ι (fun x => starRingEnd ℂ (Φ x)) y) := rfl

def sliceT (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) : ((κ ⊕ κ → k) → ℂ) →ₗ[ℂ] (Y × Y → ℂ) where
  toFun Φ := fun Z => barL ι (fun x₂ => ι (fun x₁ => Φ (Sum.elim x₁ x₂)) Z.1) Z.2
  map_add' Φ Ψ := by
    funext Z
    have e : (fun x₂ => ι (fun x₁ => (Φ + Ψ) (Sum.elim x₁ x₂)) Z.1) =
        (fun x₂ => ι (fun x₁ => Φ (Sum.elim x₁ x₂)) Z.1) + fun x₂ => ι (fun x₁ => Ψ (Sum.elim x₁ x₂)) Z.1 := by
      funext x₂
      have e' : (fun x₁ => (Φ + Ψ) (Sum.elim x₁ x₂)) = (fun x₁ => Φ (Sum.elim x₁ x₂)) + fun x₁ => Ψ (Sum.elim x₁ x₂) := rfl
      rw [e', map_add (f := _)]
      rfl
    show barL ι (fun x₂ => ι (fun x₁ => (Φ + Ψ) (Sum.elim x₁ x₂)) Z.1) Z.2 = _
    rw [e, map_add (f := _)]
    rfl
  map_smul' c Φ := by
    funext Z
    have e : (fun x₂ => ι (fun x₁ => (c • Φ) (Sum.elim x₁ x₂)) Z.1) =
        c • fun x₂ => ι (fun x₁ => Φ (Sum.elim x₁ x₂)) Z.1 := by
      funext x₂
      have e' : (fun x₁ => (c • Φ) (Sum.elim x₁ x₂)) = c • fun x₁ => Φ (Sum.elim x₁ x₂) := rfl
      rw [e', map_smul]
      rfl
    show barL ι (fun x₂ => ι (fun x₁ => (c • Φ) (Sum.elim x₁ x₂)) Z.1) Z.2 = _
    rw [e, map_smul]
    rfl

theorem sliceT_apply (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) (Φ : (κ ⊕ κ → k) → ℂ) (Z : Y × Y) :
    sliceT ι Φ Z = barL ι (fun x₂ => ι (fun x₁ => Φ (Sum.elim x₁ x₂)) Z.1) Z.2 := rfl

def swapNeg [Neg Y] (Z : Y × Y) : Y × Y := (-Z.2, -Z.1)

theorem swapNeg_apply [Neg Y] (Z : Y × Y) : swapNeg Z = (-Z.2, -Z.1) := rfl

theorem sliceT_boxFun [CommRing k] (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) (φ₁ φ₂ : (κ → k) → ℂ) (Z : Y × Y) :
    sliceT ι (boxFun φ₁ φ₂) Z = ι φ₁ Z.1 * barL ι φ₂ Z.2 := by
  have e : (fun x₂ => ι (fun x₁ => boxFun φ₁ φ₂ (Sum.elim x₁ x₂)) Z.1) = ι φ₁ Z.1 • φ₂ := by
    funext x₂
    have e' : (fun x₁ => boxFun φ₁ φ₂ (Sum.elim x₁ x₂)) = φ₂ x₂ • φ₁ := by
      funext x₁; simp [boxFun, Function.comp_def, mul_comm]
    rw [e', map_smul]
    simp [mul_comm]
  rw [sliceT_apply, e, map_smul]
  simp

end GlobalTheory.SwapSlice
end
end

section

namespace AdelicReflection
section

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.AdelicReflect

def conjNeg {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  let g : SchwartzMap E ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (ContinuousLinearEquiv.neg ℝ) f
  { toFun := fun y => starRingEnd ℂ (g y)
    smooth' := Complex.conjCLE.contDiff.comp g.smooth'
    decay' := by
      intro k n
      obtain ⟨C, hC⟩ := g.decay' k n
      refine ⟨C, fun x => ?_⟩
      have e : (fun y => starRingEnd ℂ (g y)) = Complex.conjLIE ∘ g := rfl
      rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
      exact hC x }

theorem conjNeg_mem_SB {X : Type} [TopologicalSpace X] [AddGroup X] [IsTopologicalAddGroup X] {g : X → ℂ}
    (hg : g ∈ GlobalTheory.WeilM.SB X) : (fun y => starRingEnd ℂ (g (-y))) ∈ GlobalTheory.WeilM.SB X := by
  obtain ⟨hlc, hcs⟩ := hg
  refine ⟨(hlc.comp_continuous continuous_neg).comp (starRingEnd ℂ), ?_⟩
  exact (hcs.comp_homeomorph (Homeomorph.neg X)).comp_left (g := starRingEnd ℂ) (map_zero _)

theorem conj_pureA_neg (F : Type) [Field F] [NumberField F] {κ : Type}
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → AdeleRing (𝓞 F) F) :
    starRingEnd ℂ (GlobalTheory.WeilM.pureA F f g (-x)) =
      GlobalTheory.WeilM.pureA F (fun y => starRingEnd ℂ (f (-y))) (fun y => starRingEnd ℂ (g (-y))) x := by
  simp only [GlobalTheory.WeilM.pureA, map_mul]
  congr 3
  funext i
  rw [Pi.neg_apply, Pi.neg_apply, ← map_neg]
  rfl

theorem schA_conj_neg : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∀ φ ∈ GlobalTheory.WeilM.schA F κ, (fun x => starRingEnd ℂ (φ (-x))) ∈ GlobalTheory.WeilM.schA F κ := by
  intro F _ _ κ _ φ hφ
  unfold GlobalTheory.WeilM.schA at hφ ⊢
  induction hφ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    refine Submodule.subset_span ⟨conjNeg f, fun y => starRingEnd ℂ (g (-y)), conjNeg_mem_SB hg, ?_⟩
    funext x
    rw [conj_pureA_neg]
    congr 1
  | zero =>
    convert Submodule.zero_mem _ using 1
    funext x
    simp
  | add a b _ _ ha hb =>
    convert Submodule.add_mem _ ha hb using 1
    funext x
    simp only [Pi.add_apply, map_add]
  | smul c a _ ha =>
    convert Submodule.smul_mem _ (starRingEnd ℂ c) ha using 1
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]

end GlobalTheory.CompanionTheory.AdelicReflect

end

end

end AdelicReflection
section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.Adopt.adelicSchwartzSpace_closed_under_conj_reflection : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∀ φ ∈ GlobalTheory.WeilM.schA F κ, (fun x => starRingEnd ℂ (φ (-x))) ∈ GlobalTheory.WeilM.schA F κ := by
  intro F _ _ κ _ φ hφ
  exact AdelicReflection.GlobalTheory.CompanionTheory.AdelicReflect.schA_conj_neg F κ φ hφ

end
end

section

noncomputable section

open NumberField IsDedekindDomain
open scoped Classical

namespace GlobalTheory.WeilCont

variable (F : Type) [Field F] [NumberField F] {κ : Type}

def adeleJoin (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) : κ → AdeleRing (𝓞 F) F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i)

theorem pureA_adeleJoin (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    GlobalTheory.WeilM.pureA F f g (adeleJoin F x y) = f x * g y := by
  simp only [GlobalTheory.WeilM.pureA, adeleJoin, RingEquiv.apply_symm_apply]

theorem exists_slice [Fintype κ] {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ)
    (y : κ → FiniteAdeleRing (𝓞 F) F) :
    ∃ s : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∀ x, s x = Φ (adeleJoin F x y) := by
  unfold GlobalTheory.WeilM.schA at hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, -, rfl⟩ := h
    exact ⟨g y • f, fun x => by rw [smul_apply, pureA_adeleJoin, smul_eq_mul, mul_comm]⟩
  | zero => exact ⟨0, fun x => by simp⟩
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨s1, hs1⟩ := h1
    obtain ⟨s2, hs2⟩ := h2
    exact ⟨s1 + s2, fun x => by rw [add_apply, hs1, hs2]; rfl⟩
  | smul c Φ _ h =>
    obtain ⟨s, hs⟩ := h
    exact ⟨c • s, fun x => by rw [smul_apply, hs]; rfl⟩

theorem isContOn_of_local [Fintype κ] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] {G : Type} [Group G] [TopologicalSpace G]
    {om : G →* Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ)}
    (hfin : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ p0 : G, ∃ N ∈ nhds p0, ∃ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
      (y : Fin m → κ → FiniteAdeleRing (𝓞 F) F),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ (∀ i j, g i (y j) = if i = j then 1 else 0) ∧
      ∀ p ∈ N, ∃ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, om p Φ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (g i))
    (hsl : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ y : κ → FiniteAdeleRing (𝓞 F) F,
      ∃ s : G → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, Continuous s ∧ ∀ p x, s p x = om p Φ (adeleJoin F x y)) :
    GlobalTheory.WeilM.IsContOn (GlobalTheory.WeilM.adeleClass F) om := by
  intro l hl φ hφ
  change φ ∈ GlobalTheory.WeilM.schA F κ at hφ
  change ∀ g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F),
    ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, l (GlobalTheory.WeilM.pureA F f g) = T f at hl
  rw [continuous_iff_continuousAt]
  intro p0
  obtain ⟨N, hN, m, g, y, hgSB, hgy, hrep⟩ := hfin φ hφ p0
  choose T hT using fun i => hl (g i) (hgSB i)
  choose s hs hsx using fun j => hsl φ hφ (y j)
  have hcont : Continuous fun p => ∑ i, T i (s i p) :=
    continuous_finsetSum _ (fun i _ => (T i).continuous.comp (hs i))
  refine hcont.continuousAt.congr ?_
  filter_upwards [hN] with p hp
  obtain ⟨f, hf⟩ := hrep p hp
  have hfs : ∀ j, f j = s j p := by
    intro j
    ext x
    rw [hsx, hf, Finset.sum_apply, Finset.sum_eq_single j]
    · rw [pureA_adeleJoin, hgy j j, if_pos rfl, mul_one]
    · intro i _ hij
      rw [pureA_adeleJoin, hgy i j, if_neg hij, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h

  rw [hf, map_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [hT, hfs])

end GlobalTheory.WeilCont

end
end

section

noncomputable section

open Matrix
open scoped NNReal Kronecker

namespace GlobalTheory.WeilM

variable {R : Type} [CommRing R]

theorem schr_schr [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ] (w w' : (κ → R) × (κ → R))
    (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x w.1 w'.1]
  congr 2
  simp only [add_dotProduct, dotProduct_add]
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * (mul_invOf_self (2 : R))


variable {α β κ : Type}

def flat (σ : κ ≃ α × β) : Matrix α β R ≃ₗ[R] (κ → R) where
  toFun X k := X (σ k).1 (σ k).2
  invFun u := of fun i j => u (σ.symm (i, j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv X := by ext i j; simp
  right_inv u := by ext k; simp

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]




def dblNum (σ : κ ≃ α × β) : κ ⊕ κ ≃ α × (β ⊕ β) := (σ.sumCongr σ).trans (Equiv.prodSumDistrib α β β).symm

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] in
theorem flat_fromCols (σ : κ ≃ α × β) (X Y : Matrix α β R) :
    flat (dblNum σ) (fromCols X Y) = Sum.elim (flat σ X) (flat σ Y) := by
  funext k
  cases k <;> rfl

end GlobalTheory.WeilM

end
end

section

open GlobalTheory.LKTrip

theorem _root_.GlobalTheory.T.padicEmbedding_liesOver_or_complexConj_liesOver : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (τ : G.F →+* PadicAlgCl p), LiesOver G.Kq G.u τ ∨ LiesOver G.Kq G.u (τ.comp (conjQ G.F).toRingHom) := by
  first | exact @GlobalTheory.HTGroupOver.liesOver_or_conj | exact GlobalTheory.HTGroupOver.liesOver_or_conj | (intros; apply GlobalTheory.HTGroupOver.liesOver_or_conj <;> assumption)
end

section

open IsDedekindDomain

theorem _root_.GlobalTheory.T.ratFiniteAdeles_split_awayFromPrime_padic : ∀ (p : ℕ) [Fact p.Prime], ∃ π : FiniteAdeleRing ℤ ℚ →ₐ[ℚ] ℚ_[p], Continuous π ∧ Function.Bijective (fun a => (GlobalTheory.LKTrip.AfP.restr p a, π a)) := by
  first | (exact @GlobalTheory.AdeleSplitP.finiteAdele_split) | (exact GlobalTheory.AdeleSplitP.finiteAdele_split) | (intros; apply GlobalTheory.AdeleSplitP.finiteAdele_split  <;> assumption)
end
