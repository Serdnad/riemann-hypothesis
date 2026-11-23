module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobFactsAlt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CharZeroAdicCompletion
import GroundTheory.LocalFields.Uniqueness
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DZA UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

private lemma galOf_mul' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {A B : Type*} [CommRing A] [Algebra F A] [CommRing B] [Algebra E B] (e : TensorProduct F E A ≃ₐ[E] B)
    (a b : E ≃ₐ[F] E) (y : B) :
    PositivityTheory.Rg.Tf.Geo.galOf e (a * b) y = PositivityTheory.Rg.Tf.Geo.galOf e a (PositivityTheory.Rg.Tf.Geo.galOf e b y) := by
  have h : ∀ z : TensorProduct F E A,
      Algebra.TensorProduct.map ((a * b : E ≃ₐ[F] E) : E →ₐ[F] E) (AlgHom.id F A) z =
        Algebra.TensorProduct.map (a : E →ₐ[F] E) (AlgHom.id F A)
          (Algebra.TensorProduct.map (b : E →ₐ[F] E) (AlgHom.id F A) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x c => simp
    | add x c hx hc => simp only [map_add (f := _), hx, hc]
  simp [PositivityTheory.Rg.Tf.Geo.galOf, h]

private lemma galOf_one' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {A B : Type*} [CommRing A] [Algebra F A] [CommRing B] [Algebra E B] (e : TensorProduct F E A ≃ₐ[E] B)
    (y : B) : PositivityTheory.Rg.Tf.Geo.galOf e (1 : E ≃ₐ[F] E) y = y := by
  have h : ∀ z : TensorProduct F E A,
      Algebra.TensorProduct.map ((1 : E ≃ₐ[F] E) : E →ₐ[F] E) (AlgHom.id F A) z = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x c => simp
    | add x c hx hc => simp only [map_add (f := _), hx, hc]
  simp [PositivityTheory.Rg.Tf.Geo.galOf, h]

private lemma galFin_mul' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (a b : E ≃ₐ[F] E) (v : Pl F) (y : CompletionsOver E v) :
    galFin (a * b) v y = galFin a v (galFin b v y) := galOf_mul' _ a b y

private lemma galFin_one' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : Pl F) (y : CompletionsOver E v) : galFin (1 : E ≃ₐ[F] E) v y = y := galOf_one' _ y

theorem globOf : GlobOf := by
  intro F E _ _ _ _ _ _ hp v w hw
  have hs := sum_finrank_eq E v
  rw [Fintype.sum_eq_single w (fun w' h => (h (hw w')).elim)] at hs
  intro alg hcomp
  have hdeg : Module.finrank (HeightOneSpectrum.adicCompletion F v) (HeightOneSpectrum.adicCompletion E w.1)
      = Module.finrank F E := by
    convert hs using 2
    congr 1
    first
    | exact Algebra.algebra_ext _ _ (fun x => (hcomp x).symm)
    | exact Algebra.algebra_ext _ _ (fun x => hcomp x)
  have hp2 := hp.two_le
  haveI : FiniteDimensional (HeightOneSpectrum.adicCompletion F v) (HeightOneSpectrum.adicCompletion E w.1) :=
    Module.finite_of_finrank_pos (by omega)
  let ψ : CompletionsOver E v ≃+* HeightOneSpectrum.adicCompletion E w.1 :=
    RingEquiv.ofBijective (Pi.evalRingHom (fun w' : PlacesOver E v => HeightOneSpectrum.adicCompletion E w'.1) w)
      ⟨fun y₁ y₂ h => funext fun w' => by
          obtain rfl := hw w'
          exact h,
        fun z => ⟨fun w' => by
          rw [hw w']
          exact z, rfl⟩⟩
  have hx : ∀ (σ : Gal(E/F)) (x : E),
      galFin σ v (algebraMap E (CompletionsOver E v) x) = algebraMap E (CompletionsOver E v) (σ x) := by
    intro σ x
    have e1 : ∀ z : E, algebraMap E (CompletionsOver E v) z =
        tensorEquiv' E v (z ⊗ₜ[F] (1 : HeightOneSpectrum.adicCompletion F v)) := by
      intro z
      rw [tensorEquiv'_tmul, map_one, mul_one]
    rw [e1, e1]
    show tensorEquiv' E v (Algebra.TensorProduct.map ((σ : E ≃ₐ[F] E) : E →ₐ[F] E) (AlgHom.id F _)
      ((tensorEquiv' E v).symm (tensorEquiv' E v (x ⊗ₜ[F] (1 : HeightOneSpectrum.adicCompletion F v))))) = _
    rw [AlgEquiv.symm_apply_apply, Algebra.TensorProduct.map_tmul]
    rfl
  have halg : ∀ (σ : Gal(E/F)) (r : HeightOneSpectrum.adicCompletion F v),
      galFin σ v (algebraMap _ (CompletionsOver E v) r) = algebraMap _ (CompletionsOver E v) r := by
    intro σ r
    have e1 : algebraMap _ (CompletionsOver E v) r = tensorEquiv' E v ((1 : E) ⊗ₜ[F] r) := by
      rw [tensorEquiv'_tmul, map_one, one_mul]
    rw [e1]
    show tensorEquiv' E v (Algebra.TensorProduct.map ((σ : E ≃ₐ[F] E) : E →ₐ[F] E) (AlgHom.id F _)
      ((tensorEquiv' E v).symm (tensorEquiv' E v ((1 : E) ⊗ₜ[F] r)))) = _
    rw [AlgEquiv.symm_apply_apply, Algebra.TensorProduct.map_tmul, map_one]
    rfl
  have hψalg : ∀ r : HeightOneSpectrum.adicCompletion F v,
      ψ.symm (algebraMap _ (HeightOneSpectrum.adicCompletion E w.1) r) = algebraMap _ (CompletionsOver E v) r := by
    intro r
    apply ψ.injective
    rw [RingEquiv.apply_symm_apply]
    exact (hcomp r).symm
  let φ : Gal(E/F) →* Gal(HeightOneSpectrum.adicCompletion E w.1/HeightOneSpectrum.adicCompletion F v) :=
    { toFun := fun σ =>
        { toFun := fun z => ψ (galFin σ v (ψ.symm z))
          invFun := fun z => ψ (galFin σ⁻¹ v (ψ.symm z))
          left_inv := fun z => by
            show ψ (galFin σ⁻¹ v (ψ.symm (ψ (galFin σ v (ψ.symm z))))) = z
            rw [RingEquiv.symm_apply_apply, ← galFin_mul', inv_mul_cancel, galFin_one',
              RingEquiv.apply_symm_apply]
          right_inv := fun z => by
            show ψ (galFin σ v (ψ.symm (ψ (galFin σ⁻¹ v (ψ.symm z))))) = z
            rw [RingEquiv.symm_apply_apply, ← galFin_mul', mul_inv_cancel, galFin_one',
              RingEquiv.apply_symm_apply]
          map_mul' := fun a b => by simp only [map_mul]
          map_add' := fun a b => by simp only [map_add (f := _)]
          commutes' := fun r => by
            show ψ (galFin σ v (ψ.symm (algebraMap _ _ r))) = _
            rw [hψalg, halg]
            exact hcomp r }
      map_one' := by
        apply AlgEquiv.ext
        intro z
        show ψ (galFin 1 v (ψ.symm z)) = z
        rw [galFin_one', RingEquiv.apply_symm_apply]
      map_mul' := by
        intro a b
        apply AlgEquiv.ext
        intro z
        show ψ (galFin (a * b) v (ψ.symm z)) = ψ (galFin a v (ψ.symm (ψ (galFin b v (ψ.symm z)))))
        rw [RingEquiv.symm_apply_apply, galFin_mul'] }
  haveI : Nontrivial (CompletionsOver E v) := ψ.toEquiv.nontrivial
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    apply AlgEquiv.ext
    intro x
    have h1 : φ σ (ψ (algebraMap E (CompletionsOver E v) x)) = ψ (algebraMap E (CompletionsOver E v) x) := by
      rw [hσ]
      rfl
    have h2 : φ σ (ψ (algebraMap E (CompletionsOver E v) x)) = ψ (algebraMap E (CompletionsOver E v) (σ x)) := by
      show ψ (galFin σ v (ψ.symm (ψ _))) = _
      rw [RingEquiv.symm_apply_apply, hx]
    exact (algebraMap E (CompletionsOver E v)).injective (ψ.injective (h2.symm.trans h1))
  have hbij : Function.Bijective φ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, le_antisymm (Fintype.card_le_of_injective _ hinj) ?_⟩
    have c1 := AlgEquiv.card_le (F := HeightOneSpectrum.adicCompletion F v)
      (K := HeightOneSpectrum.adicCompletion E w.1)
    have c2 := IsGalois.card_aut_eq_finrank F E
    simp only [Fintype.card_eq_nat_card] at c1 c2 ⊢
    omega
  refine ⟨?_, hdeg, ?_⟩
  · intro hsplit
    have h1 : Module.finrank (HeightOneSpectrum.adicCompletion F v) (HeightOneSpectrum.adicCompletion E w.1) = 1 := by
      rw [finrank_eq_one_iff_of_nonzero' (1 : HeightOneSpectrum.adicCompletion E w.1) one_ne_zero]
      intro z
      obtain ⟨c, hc⟩ := hsplit w z
      exact ⟨c, by rw [Algebra.smul_def, mul_one, ← hcomp, hc]⟩
    omega
  · intro s hs
    obtain ⟨σ, hσ⟩ := hbij.2 s
    refine ⟨σ, ?_, ?_⟩
    · intro τ
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hs (φ τ))
      refine Subgroup.mem_zpowers_iff.2 ⟨n, hinj ?_⟩
      rw [map_zpow, hσ, hn]
    · intro y
      rw [← hσ]
      show _ = ψ (galFin σ v (ψ.symm (ψ y)))
      rw [RingEquiv.symm_apply_apply]
      rfl

end UpperTheory.Gal.InertialTypesAlt.L
end
end

section

noncomputable section

open ValuativeRel Matrix GlobalTheory.DZA

namespace UpperTheory.Gal.InertialTypesAlt.L

section

variable {k K : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K]

private theorem mem_int (s : K ≃ₐ[k] K) (x : 𝒪[K]) : s (x : K) ∈ 𝒪[K] := by
  change valuation K (s (x : K)) ≤ 1
  rw [GroundTheory.LocalField.valuation_algEquiv_apply]
  exact x.2

private def resO (s : K ≃ₐ[k] K) : 𝒪[K] →+* 𝒪[K] :=
  (s.toAlgHom.toRingHom.comp (algebraMap 𝒪[K] K)).codRestrict 𝒪[K] fun x => mem_int s x

private theorem resO_coe (s : K ≃ₐ[k] K) (x : 𝒪[K]) : ((resO s x : 𝒪[K]) : K) = s (x : K) := rfl

private theorem resO_inv (s : K ≃ₐ[k] K) (x : 𝒪[K]) : resO s (resO s⁻¹ x) = x := by
  apply Subtype.ext
  rw [resO_coe, resO_coe]
  change s (s.symm (x : K)) = x
  exact s.apply_symm_apply _

private theorem map_res (s : K ≃ₐ[k] K) (n : ℕ) (y : GL (Fin n) 𝒪[K]) :
    GeneralLinearGroup.map (algebraMap 𝒪[K] K) (GeneralLinearGroup.map (resO s) y) =
      GlobalTheory.LBC.galAct s n (GeneralLinearGroup.map (algebraMap 𝒪[K] K) y) := by
  ext i j
  simp [GlobalTheory.LBC.galAct]
  exact resO_coe s _

private theorem map_res_inv (s : K ≃ₐ[k] K) (n : ℕ) (y : GL (Fin n) 𝒪[K]) :
    GeneralLinearGroup.map (resO s) (GeneralLinearGroup.map (resO s⁻¹) y) = y := by
  ext i j
  simp [resO_inv]

variable {F₀ F₁ : Type} [Field F₀] [Fintype F₀] [Field F₁] [Algebra F₀ F₁]
    {rk : 𝒪[k] →+* F₀} {rK : 𝒪[K] →+* F₁} {s : K ≃ₐ[k] K} {sb : F₁ ≃ₐ[F₀] F₁}

private theorem map_res_red (h : IsRes rk rK s sb) (n : ℕ) (y : GL (Fin n) 𝒪[K]) :
    GeneralLinearGroup.map rK (GeneralLinearGroup.map (resO s) y) =
      GlobalTheory.LBC.galAct sb n (GeneralLinearGroup.map rK y) := by
  ext i j
  simp [GlobalTheory.LBC.galAct]
  exact h.gal _ _ (resO_coe s _)

private theorem pow_red (h : IsRes rk rK s sb) (j : ℕ) (x : 𝒪[K]) :
    (sb ^ j) (rK x) = rK (resO (s ^ j) x) := by
  induction j generalizing x with
  | zero =>
    have hx : resO (s ^ 0) x = x := Subtype.ext (resO_coe _ x)
    rw [hx]
    rfl
  | succ j ih =>
    rw [pow_succ, AlgEquiv.mul_apply, ← h.gal x (resO s x) (resO_coe s x), ih]
    congr 1

private theorem finrank_dvd [Fintype F₁] (h : IsRes rk rK s sb) :
    Module.finrank k K ∣ orderOf s := by
  have hsb : sb = FiniteField.frobeniusAlgEquivOfAlgebraic F₀ F₁ := by
    ext z
    rw [h.frob z, FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
  have hpow : sb ^ orderOf s = 1 := by
    ext z
    obtain ⟨x, rfl⟩ := h.onto₁ z
    rw [pow_red h, pow_orderOf_eq_one]
    have hx : resO (1 : K ≃ₐ[k] K) x = x := Subtype.ext (resO_coe _ x)
    rw [hx]
    rfl
  have hord : orderOf sb = Module.finrank F₀ F₁ := by
    rw [hsb]
    exact FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic F₀ F₁
  rw [← h.deg, ← hord]
  exact orderOf_dvd_of_pow_eq_one hpow

private theorem mem_zpowers_of_isRes [IsGalois k K] [Fintype F₁] (h : IsRes rk rK s sb)
    (τ : K ≃ₐ[k] K) : τ ∈ Subgroup.zpowers s := by
  have hdvd := finrank_dvd h
  have hcard : Nat.card (K ≃ₐ[k] K) = Module.finrank k K := IsGalois.card_aut_eq_finrank k K
  have hle : orderOf s ∣ Nat.card (K ≃ₐ[k] K) := orderOf_dvd_natCard s
  have heq : Nat.card (Subgroup.zpowers s) = Nat.card (K ≃ₐ[k] K) := by
    rw [Nat.card_zpowers]
    exact Nat.dvd_antisymm hle (hcard ▸ hdvd)
  rw [Subgroup.eq_top_of_card_eq _ heq]
  exact Subgroup.mem_top τ

end

end UpperTheory.Gal.InertialTypesAlt.L

open UpperTheory.Gal.InertialTypesAlt.L in
theorem UpperTheory.Gal.InertialTypesAlt.L.frobFacts :
    UpperTheory.Gal.InertialTypesAlt.L.FrobFacts := by
  intro k K _ _ _ _ _ _ _ _ _ _ _ _ F₀ F₁ _ _ _ _ _ rk rK s sb h
  have key : ∀ (n : ℕ) (z : GL (Fin n) F₁), GlobalTheory.LBC.galAct sb⁻¹ n (GlobalTheory.LBC.galAct sb n z) = z := by
    intro n z
    rw [← MonoidHom.comp_apply, ← GlobalTheory.LBC.galAct_mul, inv_mul_cancel, GlobalTheory.LBC.galAct_one]
    rfl
  refine ⟨mem_zpowers_of_isRes h, fun n => ⟨?_, ?_, fun y =>
    ⟨GeneralLinearGroup.map (resO s) y, map_res s n y, map_res_red h n y⟩⟩⟩
  · have hinj : Function.Injective (GlobalTheory.LBC.galAct sb n) := by
      intro a b hab
      calc a = GlobalTheory.LBC.galAct sb⁻¹ n (GlobalTheory.LBC.galAct sb n a) := (key n a).symm
        _ = GlobalTheory.LBC.galAct sb⁻¹ n (GlobalTheory.LBC.galAct sb n b) := by rw [hab]
        _ = b := key n b
    unfold GlobalTheory.LBC.IsStable K1
    apply le_antisymm
    · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨GeneralLinearGroup.map (resO s) y, ?_, map_res s n y⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker] at hy ⊢
      rw [map_res_red h, hy, map_one]
    · rintro _ ⟨y, hy, rfl⟩
      refine ⟨GeneralLinearGroup.map (algebraMap 𝒪[K] K) (GeneralLinearGroup.map (resO s⁻¹) y),
        ⟨GeneralLinearGroup.map (resO s⁻¹) y, ?_, rfl⟩, ?_⟩
      · rw [SetLike.mem_coe, MonoidHom.mem_ker] at hy ⊢
        apply hinj
        rw [← map_res_red h, map_res_inv, hy, map_one]
      · rw [← map_res, map_res_inv]
  · unfold GlobalTheory.LBC.IsStable KO
    apply le_antisymm
    · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨GeneralLinearGroup.map (resO s) y, map_res s n y⟩
    · rintro _ ⟨y, rfl⟩
      exact ⟨GeneralLinearGroup.map (algebraMap 𝒪[K] K) (GeneralLinearGroup.map (resO s⁻¹) y),
        ⟨_, rfl⟩, by rw [← map_res, map_res_inv]⟩
end
end

section

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.DZA GlobalTheory.LBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

def itN {A : Type} [CommRing A] (τ : A ≃+* A) (d : ℕ) (x : A) : A := ∏ i ∈ Finset.range d, τ^[i] x

def IntEl {k : Type} [Field k] [ValuativeRel k] {n : ℕ} (γ : GL (Fin n) k) : Prop :=
  (∀ i, valuation k ((γ : Matrix (Fin n) (Fin n) k).charpoly.coeff i) ≤ 1) ∧ valuation k (γ : Matrix (Fin n) (Fin n) k).det = 1

def FrobeniusTwistedHilbertNinety : Prop :=
  ∀ (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁] (sb : F₁ ≃ₐ[F₀] F₁),
    (∀ z : F₁, sb z = z ^ Fintype.card F₀) → ∀ (A : Type) [CommRing A] [Algebra F₁ A] [Finite A] (τ : A ≃+* A), (∀ z, τ (algebraMap F₁ A z) = algebraMap F₁ A (sb z)) →
      (∀ x, τ^[Module.finrank F₀ F₁] x = x) → ∀ c : A, itN τ (Module.finrank F₀ F₁) c = 1 → ∃ y : Aˣ, c * τ y = y

def NormFin : Prop :=
  ∀ (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁] (sb : F₁ ≃ₐ[F₀] F₁),
    (∀ z : F₁, sb z = z ^ Fintype.card F₀) → ∀ (A : Type) [CommRing A] [Algebra F₁ A] [Finite A] (τ : A ≃+* A), (∀ z, τ (algebraMap F₁ A z) = algebraMap F₁ A (sb z)) →
      (∀ x, τ^[Module.finrank F₀ F₁] x = x) → ∀ x : A, IsUnit x → τ x = x → ∃ y : A, itN τ (Module.finrank F₀ F₁) y = x

def NormAdic : Prop :=
  ∀ (A : Type) [CommRing A] (I : Ideal A) [IsAdicComplete I A] (τ : A ≃+* A) (d : ℕ), (∀ x, τ^[d] x = x) → (∀ x ∈ I, τ x ∈ I) →
    ∀ a : A, ∑ i ∈ Finset.range d, τ^[i] a = 1 → ∀ x y : A, IsUnit x → τ x = x → itN τ d y - x ∈ I → ∃ y', itN τ d y' = x

def NormPoly : Prop :=
  ∀ (k K : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K] [IsGalois k K]
    (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁]
    (rk : 𝒪[k] →+* F₀) (rK : 𝒪[K] →+* F₁) (s : K ≃ₐ[k] K) (sb : F₁ ≃ₐ[F₀] F₁), IsRes rk rK s sb →
    ∀ χ : k[X], χ.Monic → (∀ i, valuation k (χ.coeff i) ≤ 1) → valuation k (χ.coeff 0) = 1 →
      ∃ p : K[X], (∀ i, valuation K (p.coeff i) ≤ 1) ∧
        χ.map (algebraMap k K) ∣ ∏ i ∈ Finset.range (Module.finrank k K), p.map ((s ^ i : K ≃ₐ[k] K) : K →+* K) - X

def GoodDelta : Prop :=
  ∀ (k K : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K] [IsGalois k K]
    (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁]
    (rk : 𝒪[k] →+* F₀) (rK : 𝒪[K] →+* F₁) (s : K ≃ₐ[k] K) (sb : F₁ ≃ₐ[F₀] F₁), IsRes rk rK s sb →
    ∀ (n : ℕ) (γ : GL (Fin n) k), IntEl γ → ∃ δ : GL (Fin n) K, GlobalTheory.LBC.norm k s δ = incl K n γ ∧
      (∀ x : GL (Fin n) K, Commute x (incl K n γ) → Commute x δ) ∧
      ∀ g : GL (Fin n) K, g⁻¹ * incl K n γ * g ∈ KO K n → g⁻¹ * δ * g ∈ KO K n

def LatDesc : Prop :=
  ∀ (k K : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K] [IsGalois k K]
    (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁]
    (rk : 𝒪[k] →+* F₀) (rK : 𝒪[K] →+* F₁) (s : K ≃ₐ[k] K) (sb : F₁ ≃ₐ[F₀] F₁), IsRes rk rK s sb →
    ∀ (n : ℕ) (g : GL (Fin n) K), g⁻¹ * galAct s n g ∈ KO K n → ∃ h : GL (Fin n) k, ∃ κ ∈ KO K n, g = incl K n h * κ

def LiftVal : Prop :=
  ∀ (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁] (sb : F₁ ≃ₐ[F₀] F₁),
    (∀ z : F₁, sb z = z ^ Fintype.card F₀) → ∀ (n : ℕ) (fb : GL (Fin n) F₀ → ℂ), (∀ a b, fb (b⁻¹ * a * b) = fb a) →
      (∀ δ γ, IsFinNorm sb δ γ → normLift sb fb δ = fb γ) ∧
      ∀ δ x : GL (Fin n) F₁, normLift sb fb (x⁻¹ * δ * galAct sb n x) = normLift sb fb δ

def RedNorm : Prop :=
  ∀ (k K : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K] [IsGalois k K]
    (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁]
    (rk : 𝒪[k] →+* F₀) (rK : 𝒪[K] →+* F₁) (s : K ≃ₐ[k] K) (sb : F₁ ≃ₐ[F₀] F₁), IsRes rk rK s sb →
    ∀ n : ℕ, (∀ h : GL (Fin n) k, incl K n h ∈ KO K n ↔ h ∈ KO k n) ∧ (∀ β ∈ KO K n, GlobalTheory.LBC.norm k s β ∈ KO K n) ∧
      (∀ β g : GL (Fin n) K, GlobalTheory.LBC.norm k s (g⁻¹ * β * galAct s n g) = g⁻¹ * GlobalTheory.LBC.norm k s β * g) ∧
      (∀ (γ : GL (Fin n) k) (g : GL (Fin n) K), g⁻¹ * incl K n γ * g ∈ KO K n → IntEl γ) ∧
      ∀ fb : GL (Fin n) F₀ → ℂ, (∀ a b, fb (b⁻¹ * a * b) = fb a) →
        (∀ β ∈ KO K n, ∀ γ : GL (Fin n) k, GlobalTheory.LBC.norm k s β = incl K n γ → infl rK (normLift sb fb) β = infl rk fb γ) ∧
        ∀ κ ∈ KO K n, ∀ y, infl rK (normLift sb fb) (κ⁻¹ * y * galAct s n κ) = infl rK (normLift sb fb) y

def OrbTransfer : Prop :=
  ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [T2Space H] (j : H →* G), Topology.IsClosedEmbedding j → ∀ (θ : G →* G) (K : Subgroup G) (K₀ : Subgroup H),
    (∀ h, j h ∈ K ↔ h ∈ K₀) → ∀ (δ : G) (γ : H), GlobalTheory.BCT.twCent θ δ = (GlobalTheory.BCT.twCent (MonoidHom.id H) γ).map j →
    ∀ (φ : G → ℂ) (f : H → ℂ), (∀ κ ∈ K, ∀ y, φ (κ⁻¹ * y * θ κ) = φ y) →
      (∀ x, φ (x⁻¹ * δ * θ x) ≠ 0 → ∃ h, ∃ κ ∈ K, x = j h * κ) → (∀ h, φ ((j h)⁻¹ * δ * θ (j h)) = f (h⁻¹ * γ * h)) →
      (∀ h, θ (j h) = j h) → GlobalTheory.BCT.twOrb θ K δ φ = GlobalTheory.BCT.twOrb (MonoidHom.id H) K₀ γ f

def Derive : Prop :=
  ∀ (k K : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Algebra k K], Continuous (algebraMap k K) →
    ∀ (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁]
      (rk : 𝒪[k] →+* F₀) (rK : 𝒪[K] →+* F₁) (s : K ≃ₐ[k] K) (sb : F₁ ≃ₐ[F₀] F₁), IsRes rk rK s sb →
      ValuativeExtension k K ∧ FiniteDimensional k K ∧ IsGalois k K

end UpperTheory.Gal.InertialTypesAlt.L
end
end
