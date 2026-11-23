module

public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

theorem LocalMultOrd.proof : LocalMultOrd.Statement := by
  intro A _ _ I W x _ hW
  set J := I ⊔ Ideal.span {x} with hJ
  have hWp : W.IsPrime := hW.1.1
  have hIW : I ≤ W := le_sup_left.trans hW.1.2
  have hxJ : x ∈ J := Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)
  set P := W.map (Ideal.Quotient.mk I) with hPdef
  have hcomap : W = P.comap (Ideal.Quotient.mk I) := by
    rw [hPdef, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left.mpr hIW]
  have hcompl : ∀ a : A, a ∉ W → Ideal.Quotient.mk I a ∈ P.primeCompl := fun a ha h =>
    ha (hcomap ▸ h)
  let AW := Localization.AtPrime W
  let BP := Localization.AtPrime P
  let φ : AW →+* BP := Localization.localRingHom W P (Ideal.Quotient.mk I) hcomap
  set x' : BP := algebraMap (A ⧸ I) BP (Ideal.Quotient.mk I x) with hx'
  let C := BP ⧸ Ideal.span {x'}
  let π : AW →+* C := (Ideal.Quotient.mk _).comp φ
  have hφ : ∀ a : A, φ (algebraMap A AW a) = algebraMap (A ⧸ I) BP (Ideal.Quotient.mk I a) :=
    fun a => Localization.localRingHom_to_map _ _ _ _ _
  have hφs : Function.Surjective φ := by
    intro z
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (s : A ⧸ I)
    have htW : t ∈ W.primeCompl := fun h => s.2 (ht ▸ Ideal.mem_map_of_mem _ h)
    refine ⟨IsLocalization.mk' AW a ⟨t, htW⟩, ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext ht
  have hπs : Function.Surjective π := Ideal.Quotient.mk_surjective.comp hφs

  have hmax : ∀ Q ∈ (Ideal.span {x'}).minimalPrimes, Q.IsMaximal := by
    intro Q hQ
    have := hQ.1.1
    have hle : W ≤ (Q.comap (algebraMap (A ⧸ I) BP)).comap (Ideal.Quotient.mk I) := by
      refine hW.2 ⟨Ideal.comap_isPrime _ _, sup_le ?_ ?_⟩ ?_
      · intro a ha
        simp [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      · rw [Ideal.span_le, Set.singleton_subset_iff]
        exact hQ.1.2 (Ideal.mem_span_singleton_self _)
      · intro a ha
        by_contra haW
        exact hQ.1.1.ne_top (Ideal.eq_top_of_isUnit_mem _ ha
          (IsLocalization.map_units BP (⟨_, hcompl a haW⟩ : P.primeCompl)))
    have hm : IsLocalRing.maximalIdeal BP ≤ Q := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
      intro b hb
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
      exact hle (by rw [hcomap]; exact hb)
    rw [le_antisymm (IsLocalRing.le_maximalIdeal hQ.1.1.ne_top) hm]
    infer_instance
  have : Ring.KrullDimLE 0 C :=
    Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr hmax
  have : IsArtinianRing C := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero (R := C)
  have hfin : Module.length C C ≠ ⊤ :=
    Module.length_ne_top_iff.mpr
      (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)

  let : Algebra AW C := RingHom.toAlgebra (R := AW) (S := C) π
  have hJπ : ∀ y ∈ J.map (algebraMap A AW), (Algebra.ofId AW C) y = 0 := by
    have : J.map (algebraMap A AW) ≤ RingHom.ker π := by
      rw [Ideal.map_le_iff_le_comap]
      refine sup_le (fun a ha => ?_) ?_
      · simp [RingHom.mem_ker, π, hφ, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      · rw [Ideal.span_le, Set.singleton_subset_iff]
        simp [RingHom.mem_ker, π, hφ, ← hx']
    exact fun y hy => this hy
  let f : (AW ⧸ J.map (algebraMap A AW)) →ₐ[AW] C := Ideal.Quotient.liftₐ _ (Algebra.ofId AW C) hJπ
  have hf : ∀ y, f (Ideal.Quotient.mk _ y) = π y := fun y => rfl
  let ψ0 : A ⧸ I →+* AW ⧸ J.map (algebraMap A AW) :=
    Ideal.Quotient.lift I ((Ideal.Quotient.mk _).comp (algebraMap A AW)) (fun a ha =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ (Ideal.mem_sup_left ha)))
  have hunit : ∀ s : P.primeCompl, IsUnit (ψ0 s) := by
    intro s
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (s : A ⧸ I)
    have htW : t ∈ W.primeCompl := fun h => s.2 (ht ▸ Ideal.mem_map_of_mem _ h)
    rw [← ht]
    exact (IsLocalization.map_units AW (⟨t, htW⟩ : W.primeCompl)).map (Ideal.Quotient.mk _)
  let ψ1 : BP →+* AW ⧸ J.map (algebraMap A AW) := IsLocalization.lift hunit
  have hψ1 : ∀ a : A, ψ1 (algebraMap (A ⧸ I) BP (Ideal.Quotient.mk I a)) =
      Ideal.Quotient.mk _ (algebraMap A AW a) := fun a => by
    simp [ψ1, ψ0, IsLocalization.lift_eq]
  let ψ : C →+* AW ⧸ J.map (algebraMap A AW) := Ideal.Quotient.lift _ ψ1 (by
    intro z hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    rw [map_mul, hx', hψ1, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hxJ), mul_zero])
  have hψπ : ψ.comp π = Ideal.Quotient.mk _ := by
    apply IsLocalization.ringHom_ext W.primeCompl
    ext a
    change ψ (Ideal.Quotient.mk _ (φ (algebraMap A AW a))) =
      Ideal.Quotient.mk _ (algebraMap A AW a)
    rw [hφ]
    exact hψ1 a
  have hinj : Function.Injective f := by
    intro q₁ q₂ h
    obtain ⟨y₁, rfl⟩ := Ideal.Quotient.mk_surjective q₁
    obtain ⟨y₂, rfl⟩ := Ideal.Quotient.mk_surjective q₂
    rw [hf, hf] at h
    have e₁ : ψ (π y₁) = _ := RingHom.congr_fun hψπ y₁
    have e₂ : ψ (π y₂) = _ := RingHom.congr_fun hψπ y₂
    exact e₁.symm.trans ((congrArg ψ h).trans e₂)
  have hsurj : Function.Surjective f := fun c => by
    obtain ⟨y, rfl⟩ := hπs c
    exact ⟨_, hf y⟩
  let e := LinearEquiv.ofBijective f.toLinearMap ⟨hinj, hsurj⟩
  have hord : Ring.ord BP x' = Module.length C C :=
    Module.length_eq_of_surjective (S := BP) (R := C) (M := C) Ideal.Quotient.mk_surjective
  have hlen : Module.length AW (AW ⧸ J.map (algebraMap A AW)) = Module.length C C := by
    rw [e.length_eq]
    exact Module.length_eq_of_surjective (S := AW) (R := C) (M := C) hπs
  have hloc : localMult J W = (Module.length AW (AW ⧸ J.map (algebraMap A AW))).toNat := by
    unfold localMult
    rw [dite_eq_left hWp]
  rw [hloc, hlen, hord]
  exact ENat.natCast_toNat hfin

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem FGNullstellensatz.proof : FGNullstellensatz.Statement := by
  intro F _ D _ _ _ _ r hr
  have hJ : IsJacobsonRing D := isJacobsonRing_of_finiteType (A := F)
  have hmem : r ∈ (⊥ : Ideal D).jacobson := by
    rw [Ideal.jacobson, Submodule.mem_sInf]
    rintro m ⟨-, hm⟩
    let _ : Field (D ⧸ m) := Ideal.Quotient.field m
    have : Algebra.FiniteType F (D ⧸ m) := inferInstance
    have : Module.Finite F (D ⧸ m) := finite_of_finite_type_of_isJacobsonRing F (D ⧸ m)
    have : Algebra.IsAlgebraic F (D ⧸ m) := inferInstance
    let ψ : (D ⧸ m) →ₐ[F] AlgebraicClosure F := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    have h0 : ψ (Ideal.Quotient.mkₐ F m r) = 0 := hr (ψ.comp (Ideal.Quotient.mkₐ F m))
    have h1 : Ideal.Quotient.mkₐ F m r = 0 := (map_eq_zero_iff ψ ψ.toRingHom.injective).mp h0
    exact Ideal.Quotient.eq_zero_iff_mem.mp h1
  rw [← Ideal.radical_eq_jacobson] at hmem
  obtain ⟨k, hk⟩ := hmem
  exact IsReduced.eq_zero r ⟨k, by simpa using hk⟩

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

section Chart

variable {F : Type} [Field F] {n : ℕ}

def chartIncIdeal (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ) :
    Ideal (MvPolynomial (Fin n ⊕ Fin e × Fin n) F) :=
  (I ⊔ Ideal.span {linForm t - 1}).map (rename Sum.inl) ⊔
    Ideal.span (Set.range fun i : Fin e => ∑ m, X (Sum.inr (i, m)) * X (Sum.inl m))

def ChartInc (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ) : Type :=
  MvPolynomial (Fin n ⊕ Fin e × Fin n) F ⧸ chartIncIdeal I t e

instance (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ) : CommRing (ChartInc I t e) :=
  inferInstanceAs (CommRing (MvPolynomial (Fin n ⊕ Fin e × Fin n) F ⧸ chartIncIdeal I t e))

def chartIncHom (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ) :
    MvPolynomial (Fin e × Fin n) F →+* ChartInc I t e :=
  (Ideal.Quotient.mk (chartIncIdeal I t e)).comp (rename Sum.inr).toRingHom

instance (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ) :
    Algebra (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) :=
  (chartIncHom I t e).toAlgebra

def chartX (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ) :
    MvPolynomial (Fin n) F →+* ChartInc I t e :=
  (Ideal.Quotient.mk (chartIncIdeal I t e)).comp (rename Sum.inl).toRingHom

def chartLin (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ) (u : Fin n → F) :
    ChartInc I t e :=
  chartX I t e (linForm u)

abbrev ChartLoc (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ)
    (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime] : Type :=
  Localization (Algebra.algebraMapSubmonoid (ChartInc I t e) p.primeCompl)

def chartIdeal (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ)
    (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime] (W : Ideal (MvPolynomial (Fin n) F)) :
    Ideal (ChartLoc I t e p) :=
  (W.map (chartX I t e)).map (algebraMap (ChartInc I t e) (ChartLoc I t e p))

end Chart

def IncIdealBelow.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F), IsProjPrime I → IsChowForm I (e + 1) f →
      incIdeal I e = ⊥

def SpecFirstMemIncIdeal.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I W : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t : Fin n → F), IsChowForm I (e + 1) f → I ≤ W →
      linForm t ∈ W → specFirst f t ∈ incIdeal W e

def ChartChoice.Statement : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (q : MvPolynomial (Fin e × Fin n) F),
    IsProjPrime I → IsChowForm I (e + 1) f → Prime q → ∃ t : Fin n → F, ¬ q ∣ specFirst f t

def SpecFirstNe.Statement : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (u : Fin n → F),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I → specFirst f u ≠ 0

def LocalizationPrimeDVR.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R]
    (q : R) (p : Ideal R) [p.IsPrime], Prime q → p = Ideal.span {q} →
      IsDiscreteValuationRing (Localization.AtPrime p)

def EmultiplicityOrd.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R]
    (q x : R) (p : Ideal R) [p.IsPrime], Prime q → p = Ideal.span {q} → x ≠ 0 →
      emultiplicity q x = Ring.ord (Localization.AtPrime p) (algebraMap R _ x)

def ChartFinite.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t : Fin n → F)
    (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f → specFirst f t ∉ p →
      Module.Finite (Localization.AtPrime p) (ChartLoc I t e p)

def ChartLocDomain.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t : Fin n → F)
    (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f → linForm t ∉ I →
      IsDomain (ChartLoc I t e p) ∧
        Function.Injective (algebraMap (Localization.AtPrime p) (ChartLoc I t e p)) ∧
        ∀ u : Fin n → F, linForm u ∉ I →
          algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u) ≠ 0

def ChartNorm.Statement : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t : Fin n → F)
    (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f → (p = ⊥ ∨ ∃ q, Prime q ∧ p = Ideal.span {q}) →
      specFirst f t ∉ p → ∀ u : Fin n → F,
        algebraMap _ (Localization.AtPrime p) (specFirst f u) =
          algebraMap _ (Localization.AtPrime p) (specFirst f t) *
            LinearMap.det (LinearMap.mulLeft (Localization.AtPrime p)
              (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u)))


open Classical in
def ChartLength.Statement : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t u : Fin n → F)
    (q : MvPolynomial (Fin e × Fin n) F) (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I → Prime q → p = Ideal.span {q} →
      ¬ q ∣ specFirst f t →
        Module.length (Localization.AtPrime p) (ChartLoc I t e p ⧸ LinearMap.range
            (LinearMap.mulLeft (Localization.AtPrime p)
              (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u)))) =
          ∑ W ∈ (divCycle I u).support with Ideal.span {q} = incIdeal W e,
            ((divCycle I u W : ℕ) : ℕ∞)

def LengthFiniteAlgebra.Statement : Prop :=
  ∀ (O B : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing B] [Algebra O B]
    [Module.Finite O B] (θ : B),
    Module.length O (B ⧸ LinearMap.range (LinearMap.mulLeft O θ)) =
      ∑ᶠ 𝔓 : MaximalSpectrum B,
        Ring.ord (Localization.AtPrime 𝔓.asIdeal) (algebraMap B _ θ) * Module.length O (B ⧸ 𝔓.asIdeal)

def ChartMaxIdeals.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t u : Fin n → F)
    (q : MvPolynomial (Fin e × Fin n) F) (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I → Prime q → p = Ideal.span {q} →
      ¬ q ∣ specFirst f t →
        Set.BijOn (chartIdeal I t e p)
          {W | W ∈ (divCycle I u).support ∧ Ideal.span {q} = incIdeal W e}
          {𝔓 | 𝔓.IsMaximal ∧
            algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u) ∈ 𝔓}

def ChartLocalOrder.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I W : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t u : Fin n → F)
    (q : MvPolynomial (Fin e × Fin n) F) (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I → Prime q → p = Ideal.span {q} →
      ¬ q ∣ specFirst f t → W ∈ relComps (I ⊔ Ideal.span {linForm u}) → q ∈ incIdeal W e →
        linForm t ∉ W →
          ∃ _ : (chartIdeal I t e p W).IsPrime,
            Ring.ord (Localization.AtPrime (chartIdeal I t e p W))
                (algebraMap (ChartLoc I t e p) _
                  (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u))) =
              (localMult (I ⊔ Ideal.span {linForm u}) W : ℕ∞)

def ChartResidueDegree.Statement : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n e : ℕ) (I W : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t u : Fin n → F)
    (q : MvPolynomial (Fin e × Fin n) F) (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I → Prime q → p = Ideal.span {q} →
      ¬ q ∣ specFirst f t → W ∈ relComps (I ⊔ Ideal.span {linForm u}) → q ∈ incIdeal W e →
        linForm t ∉ W →
          Module.length (Localization.AtPrime p) (ChartLoc I t e p ⧸ chartIdeal I t e p W) = 1

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem ProjNullstellensatz.proof (h₁ : FGNullstellensatz.Statement) :
    ProjNullstellensatz.Statement := by
  intro F _ n P hP
  have : P.IsPrime := hP.isPrime
  obtain ⟨j, hj⟩ := hP.isRelevant
  set D := MvPolynomial (Fin n) F ⧸ P
  have hr : Ideal.Quotient.mk P (X j) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hj
  have hφ : ∃ φ : D →ₐ[F] AlgebraicClosure F, φ (Ideal.Quotient.mk P (X j)) ≠ 0 := by
    by_contra hne
    apply hr
    refine h₁ F D _ (fun φ => ?_)
    by_contra h
    exact hne ⟨φ, h⟩
  obtain ⟨φ, hφj⟩ := hφ
  have hcomp : φ.comp (Ideal.Quotient.mkₐ F P) = aeval (fun i => φ (Ideal.Quotient.mk P (X i))) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, aeval_X]
    rfl
  refine ⟨fun i => φ (Ideal.Quotient.mk P (X i)), ?_, ?_⟩
  · intro h0
    exact hφj (congrFun h0 j)
  · intro g hg
    rw [← hcomp, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr hg, map_zero]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Module

theorem LengthQuotientDet.ord_prod {O : Type} [CommRing O] [IsDomain O] {ι : Type*} (s : Finset ι)
    (a : ι → O) (ha : ∀ i, a i ≠ 0) : Ring.ord O (∏ i ∈ s, a i) = ∑ i ∈ s, Ring.ord O (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj,
      Ring.ord_mul' O (mem_nonZeroDivisors_of_ne_zero (ha j)), ih]

theorem LengthQuotientDet.proof : LengthQuotientDet.Statement := by
  intro O _ _ _ M _ _ _ _ φ hdet
  classical
  have hinj : Function.Injective φ :=
    LinearMap.ker_eq_bot.mp (not_not.mp (mt LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hdet))
  set ι := Module.Free.ChooseBasisIndex O M
  let b := Module.Free.chooseBasis O M
  have hrank : finrank O (LinearMap.range φ) = finrank O M := LinearMap.finrank_range_of_inj hinj
  set a := Submodule.smithNormalFormCoeffs b hrank
  let b' := Submodule.smithNormalFormTopBasis b hrank
  let ab := Submodule.smithNormalFormBotBasis b hrank
  have ha : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b hrank

  have hlen : Module.length O (M ⧸ LinearMap.range φ) = ∑ i, Ring.ord O (a i) := by
    rw [(Submodule.quotientEquivPiSpan (LinearMap.range φ) b hrank).length_eq,
      Module.length_pi_of_fintype]
    rfl

  let v : Basis ι O M := ab.map (LinearEquiv.ofInjective φ hinj).symm
  have hv : ∀ i, φ (v i) = a i • b' i := by
    intro i
    have h1 : φ (v i) = ((LinearEquiv.ofInjective φ hinj) (v i) : M) :=
      (LinearEquiv.ofInjective_apply _ _).symm
    rw [h1]
    simp only [v, Basis.map_apply, LinearEquiv.apply_symm_apply]
    exact Submodule.smithNormalFormBotBasis_def b hrank i
  have hdetprod : LinearMap.det φ * b'.det v = ∏ i, a i := by
    rw [← Basis.det_comp]
    have : (⇑φ ∘ ⇑v) = fun i => a i • b' i := funext hv
    rw [this, AlternatingMap.map_smul_univ, Basis.det_self, smul_eq_mul, mul_one]
  have hassoc : Associated (LinearMap.det φ) (∏ i, a i) := by
    obtain ⟨u, hu⟩ := b'.isUnit_det v
    exact ⟨u, by rw [hu]; exact hdetprod⟩
  rw [hlen, Ring.ord_eq_of_associated hassoc, LengthQuotientDet.ord_prod _ _ ha]

end GroundTheory.Heights₂.Heights
end
