module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle109
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle034
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle115
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle062
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle408
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle372
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistTrivialOnRational
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelGroupLatticeCongruence
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
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
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
theorem _root_.GlobalTheory.T.ordinarySelmer_vanishes_of_dual_vanishes : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → GrZero (dual1 W) A → GrZero W A := by
  first | exact @GlobalTheory.Ord2.grZero_of_grZero_dual1 | exact GlobalTheory.Ord2.grZero_of_grZero_dual1 | (intros; apply GlobalTheory.Ord2.grZero_of_grZero_dual1 <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

namespace GlobalTheory.RecOne

section Gen

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

def evMul (l : ℕ) (A : ValuationSubring Ω) : Submodule A (KaehlerDifferential (fixA A) A) where
  carrier := {ω | ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ z : A, IsPrimitiveRoot (z : Ω) (l ^ N) →
    ω ∈ Submodule.span A {dA A z}}
  add_mem' := by
    rintro a b ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
    exact ⟨max N₁ N₂, fun N hN z hz =>
      add_mem (h₁ N (le_trans (le_max_left _ _) hN) z hz) (h₂ N (le_trans (le_max_right _ _) hN) z hz)⟩
  zero_mem' := ⟨0, fun _ _ _ _ => zero_mem _⟩
  smul_mem' := by
    rintro c a ⟨N₁, h₁⟩
    exact ⟨N₁, fun N hN z hz => Submodule.smul_mem _ c (h₁ N hN z hz)⟩

theorem dA_mem_evMul (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) {x : A} {n : ℕ}
    (hx : x ^ (l ^ n) = 1) : dA A x ∈ evMul l A := by
  refine ⟨n, fun N hN z hz => ?_⟩
  have : NeZero (l ^ N) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have h1 : (x : Ω) ^ (l ^ N) = 1 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hN
    have h0 : (x : Ω) ^ (l ^ n) = 1 := by
      have := congrArg (fun t : A => (t : Ω)) hx
      simpa using this
    rw [pow_add, pow_mul, h0, one_pow]
  obtain ⟨i, -, hi⟩ := hz.eq_pow_of_pow_eq_one h1
  have h2 : x = z ^ i := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, hi]
  rw [h2, Derivation.leibniz_pow]
  exact Submodule.smul_of_tower_mem _ _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

end Gen

theorem l_sq_smul_dA_eq_smul : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ v : A, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ z : A, IsPrimitiveRoot (z : Ω) (l ^ N) → ∃ y : A, ((l : A) ^ 2) • dA A v = y • dA A z := by
  intro l _ hl2 Ω _ _ _ A hA v
  have hder : ∀ B : Subalgebra (fixA A) A, IsDerOn B (fun x => dA A x) := fun B =>
    ⟨fun x _ y _ => map_add (dA A) x y, fun x _ y _ => Derivation.leibniz (dA A) x y,
      fun a => (dA A).map_algebraMap a⟩
  obtain ⟨C, tr, k, a, b, hF, htr⟩ := GlobalTheory.T.exists_almostDualTraceData_cyclotomicAlgebra l hl2 Ω A hA {v}
  have h1 := GlobalTheory.AlmostEt.derOn_mem_span_of_trData (fixA A) A _ (cycAlg l A) C tr k a b _ htr
    (fun x => dA A x) (hder C) v (hF (by simp))
  have h2 : Submodule.span A ((fun x => dA A x) '' (cycAlg l A : Set A)) ≤ evMul l A := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have h3 := GlobalTheory.AlmostEt.derOn_adjoin_mem_span (fixA A) A _ {z : A | ∃ n : ℕ, z ^ (l ^ n) = 1}
      (fun x => dA A x) (hder _) x hx
    refine Submodule.span_le.2 ?_ h3
    rintro _ ⟨y, ⟨n, hn⟩, rfl⟩
    exact dA_mem_evMul l A hn
  obtain ⟨N₀, h⟩ := h2 h1
  refine ⟨N₀, fun N hN z hz => ?_⟩
  obtain ⟨y, hy⟩ := Submodule.mem_span_singleton.1 (h N hN z hz)
  exact ⟨y, by rw [pow_two]; exact hy.symm⟩

end GlobalTheory.RecOne
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

namespace GlobalTheory.RecOne

theorem pow_four_mul_mem_of_smul_dA_eq_zero : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (N : ℕ) (z : A), IsPrimitiveRoot (z : Ω) (l ^ N) → ∀ a : A, a • dA A z = 0 → ∃ w ∈ A, (l : Ω) ^ 4 * (a : Ω) = (l : Ω) ^ N * w := by
  intro l _ hl2 Ω _ _ _ A hA N z hz a hrel
  have hlΩ : (l : Ω) ≠ 0 := by
    haveI : CharZero Ω := algebraRat.charZero Ω
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hpos : 0 < l ^ N := pow_pos (Fact.out : l.Prime).pos N
  have hz1 : (z : Ω) ^ (l ^ N) = 1 := hz.pow_eq_one
  have hzA : z ^ (l ^ N) = 1 := Subtype.ext (by simpa using hz1)
  have hzT : z ∈ cycAlg l A := mem_cycAlg_of_pow hzA
  have hrel' : ∑ i : Fin 1, (fun _ => a) i •
      KaehlerDifferential.D (fixA A) A ((fun _ => z) i) = 0 := by
    simpa using hrel
  obtain ⟨F, hF⟩ := kaehler_rel_local (fixA A) A 1 _ _ hrel'
  obtain ⟨C, tr, m, α, β, hFC, htr⟩ := GlobalTheory.T.exists_almostDualTraceData_cyclotomicAlgebra l hl2 Ω A hA F
  obtain ⟨D, hD, hDv⟩ := GlobalTheory.T.exists_zeta_derivation_inertia_cyclotomic_algebra l Ω A hA N z hz
  obtain ⟨D', hD', hD'v⟩ := exists_derOn_ext (fixA A) A (FracA A) (cycAlg l A) C tr m α β _ htr D hD
  have h := hF C hFC (fun _ => htr.le hzT) (FracA A) D' hD'
  rw [Fin.sum_univ_one, hD'v _ hzT, hDv, smul_smul, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨t, ht⟩ := h
  have ht' : (t : Ω) = (a : Ω) * (l : Ω) ^ 3 * ((z : Ω) * (l : Ω) / (l : Ω) ^ N) := by
    simpa [Algebra.smul_def] using ht
  refine ⟨((t * z ^ (l ^ N - 1) : A) : Ω), (t * z ^ (l ^ N - 1)).2, ?_⟩
  have hzz : (z : Ω) * (z : Ω) ^ (l ^ N - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hpos, hz1]
  push_cast
  rw [ht']
  field_simp
  linear_combination (-((a : Ω))) * hzz

end GlobalTheory.RecOne
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TraceLattice

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open scoped TensorProduct Matrix nonZeroDivisors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem det_baseChange_lift {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
    (γ : (M ⧸ I • (⊤ : Submodule R M)) ≃ₗ[R] (M ⧸ I • (⊤ : Submodule R M))) (f : M →ₗ[R] M)
    (hf : ∀ v, (I • (⊤ : Submodule R M)).mkQ (f v) = γ ((I • (⊤ : Submodule R M)).mkQ v)) :
    LinearMap.det (LinearMap.baseChange (R ⧸ I) f) =
      ((LinearEquiv.det (γ.extendScalarsOfSurjective (S := R ⧸ I) Ideal.Quotient.mk_surjective) : (R ⧸ I)ˣ) : R ⧸ I) := by
  let e := (TensorProduct.quotTensorEquivQuotSMul M I).extendScalarsOfSurjective (S := R ⧸ I) Ideal.Quotient.mk_surjective
  rw [LinearEquiv.coe_det, ← LinearMap.det_conj _ e]
  congr 1
  refine LinearMap.ext fun q => ?_
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  change TensorProduct.quotTensorEquivQuotSMul M I (LinearMap.baseChange (R ⧸ I) f
    ((TensorProduct.quotTensorEquivQuotSMul M I).symm (Submodule.Quotient.mk a))) = γ _
  rw [TensorProduct.quotTensorEquivQuotSMul_symm_mk, LinearMap.baseChange_tmul,
    ← TensorProduct.quotTensorEquivQuotSMul_symm_mk, LinearEquiv.apply_symm_apply]
  exact hf a

section General

open GlobalTheory.AdLat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


variable (F E) in
def swapF : RA F E →+* E ⊗[F] Formalism.L2.Herm.Af F :=
  (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).toAlgHom.toRingHom

theorem exists_res_eq_zero {I : Ideal (𝓞 E)} {PP : Pl E} (hI : I ≤ PP.asIdeal) {x : RA F E}
    (hx : x ∈ hat1 F ((I : FractionalIdeal (𝓞 E)⁰ E) : Set E)) :
    ∃ t : Formalism.L2.Herm.intAf F E, t.1 = swapF F E x ∧ resS F PP t = 0 := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, y, hy, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    refine ⟨oToS F E b * ⟨(1 : E) ⊗ₜ a, Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)⟩, ?_, ?_⟩
    · change ((b : E) ⊗ₜ 1) * ((1 : E) ⊗ₜ a) = (b : E) ⊗ₜ a
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    · rw [map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 (hI hb), zero_mul]
  | zero => exact ⟨0, (RingHom.map_zero _).symm, RingHom.map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hs'⟩ := hx
    obtain ⟨t, ht, ht'⟩ := hy
    exact ⟨s + t, by rw [RingHom.map_add (f := _), ← hs, ← ht]; rfl, by rw [RingHom.map_add (f := _), hs', ht', add_zero]⟩
  | neg x _ hx =>
    obtain ⟨s, hs, hs'⟩ := hx
    exact ⟨-s, by rw [RingHom.map_neg, ← hs]; rfl, by rw [RingHom.map_neg, hs', neg_zero]⟩

theorem det_eq_one_of_lift {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) (Pg : Finset (Pl E)) (I J : Ideal (𝓞 E)) (hI : I ≠ ⊥) (hIJ : I ⊔ J = ⊤)
    (hPg : I = ∏ PP ∈ Pg, PP.asIdeal) {M : Type} [AddCommGroup M] [Module (𝓞 E) M] (ι : M →ₗ[𝓞 E] (Fin n → E))
    (hinj : Function.Injective ι) (hr : LinearMap.range ι = L)
    (γ : (M ⧸ I • (⊤ : Submodule (𝓞 E) M)) ≃ₗ[𝓞 E] (M ⧸ I • (⊤ : Submodule (𝓞 E) M))) (f : M →ₗ[𝓞 E] M)
    (hf : ∀ v, (I • (⊤ : Submodule (𝓞 E) M)).mkQ (f v) = γ ((I • (⊤ : Submodule (𝓞 E) M)).mkQ v))
    (k : Matrix (Fin n) (Fin n) (RA F E)) (s : Formalism.L2.Herm.intAf F E) (hs : swapF F E k.det = s.1)
    (hdet : ∀ PP ∈ Pg, resS F PP s = 1) {N : ℕ} (hN : (N : 𝓞 E) ∈ I)
    (h : ∀ a ∈ J • (⊤ : Submodule (𝓞 E) M), ∃ w ∈ hat F (L : Set (Fin n → E)),
      fv F (ι (f a)) - k.mulVec (fv F (ι a)) = N • w) :
    LinearMap.det (LinearMap.baseChange (𝓞 E ⧸ I) f) = 1 := by
  have h1 : (1 : 𝓞 E) ∈ I ⊔ J := by rw [hIJ]; trivial
  obtain ⟨m, hm, c, hc, hmc⟩ := Submodule.mem_sup.1 h1
  obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective ((LinearEquiv.det (γ.extendScalarsOfSurjective (S := 𝓞 E ⧸ I)
    Ideal.Quotient.mk_surjective) : (𝓞 E ⧸ I)ˣ) : 𝓞 E ⧸ I)
  let ρ : 𝓞 E →+* RA F E :=
    (Algebra.TensorProduct.includeRight (R := F) (A := FiniteAdeleRing (𝓞 F) F) (B := E)).toRingHom.comp (algebraMap (𝓞 E) E)
  have hfv : ∀ (b : 𝓞 E) a, fv F (ι (b • a)) = ρ b • fv F (ι a) := fun b a => by
    funext i
    rw [map_smul]
    change (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((b : E) * ι a i) =
      ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ι a i)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have key := GlobalTheory.LevDet.det_sub_mem_completedIdeal_of_level F L hfg hsp I hI ι hinj hr γ f hf (ρ c • k) (fun a => by
      obtain ⟨w, hw, e⟩ := h (c • a) (Submodule.smul_mem_smul hc trivial)
      have hfa : fv F (ι (f a)) ∈ hat F (L : Set (Fin n → E)) :=
        AddSubgroup.subset_closure ⟨1, fun v => one_mem _, _, hr ▸ LinearMap.mem_range_self ι _, rfl⟩
      rw [map_smul, hfv, hfv, Matrix.mulVec_smul, ← Nat.cast_smul_eq_nsmul (RA F E), ← map_natCast ρ] at e
      have e' : (ρ c • k) *ᵥ fv F (ι a) - fv F (ι (f a)) = -(ρ m • fv F (ι (f a))) - ρ (N : 𝓞 E) • w := by
        have : ρ m = 1 - ρ c := by rw [← map_one ρ, ← hmc, map_add (f := _), add_sub_cancel_right]
        rw [← e, this, Matrix.smul_mulVec, sub_smul, one_smul]
        abel
      rw [e']
      exact sub_mem (neg_mem (AddSubgroup.subset_closure ⟨m, hm, _, hfa, rfl⟩))
        (AddSubgroup.subset_closure ⟨_, hN, w, hw, rfl⟩)) u hu
  rw [det_baseChange_lift I γ _ hf, ← hu, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq, hPg,
    Ideal.prod_eq_iInf_of_pairwise_isCoprime fun a _ b _ hab => HeightOneSpectrum.isCoprime_of_ne _ _ hab]
  refine Ideal.mem_iInf.2 fun PP => Ideal.mem_iInf.2 fun hP => ?_
  have hle : I ≤ PP.asIdeal := hPg ▸ Ideal.prod_le_inf.trans (Finset.inf_le hP)
  obtain ⟨t, ht, ht0⟩ := exists_res_eq_zero hle key
  have hρ : ∀ b, swapF F E (ρ b) = (oToS F E b).1 := fun _ => rfl
  have e : t = oToS F E c ^ n * s - oToS F E u := by
    apply Subtype.ext
    rw [ht, Matrix.det_smul, RingHom.map_sub, RingHom.map_mul, RingHom.map_pow, hρ, hs, Fintype.card_fin]
    rfl
  have h4 : Ideal.Quotient.mk PP.asIdeal c = 1 := by
    rw [← map_one (Ideal.Quotient.mk PP.asIdeal), ← hmc, map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.2 (hle hm), zero_add]
  rw [e, RingHom.map_sub, RingHom.map_mul, RingHom.map_pow, resS_oToS, resS_oToS, hdet PP hP, h4, one_pow, one_mul,
    sub_eq_zero] at ht0
  rw [← Ideal.Quotient.eq, ← ht0, map_one]

theorem exists_det_of_mem_St {n : ℕ} (k : Matrix (Fin n) (Fin n) (RA F E)) {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (hk : x.1 = (swapF F E).mapMatrix k) (hx : x ∈ St β) : ∃ s : Formalism.L2.Herm.intAf F E, swapF F E k.det = s.1 ∧
      ∀ PP, resS F PP s = ((redFn β PP x : GL _ _) : Matrix (Fin n) (Fin n) (kP PP)).det := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨y.1.det, ?_, fun PP => ?_⟩
  · have e2 : (y.1.det).1 = (intGL F E _ y).1.det := RingHom.map_det (Formalism.L2.Herm.intAf F E).subtype _
    rw [RingHom.map_det, ← hk, e2]
    exact Matrix.det_units_conj β _
  · rw [redFn_frGL]
    exact RingHom.map_det _ _

end General

variable {D : D7}

theorem detOne_of_lift (V : HSp D) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hι : LatEmb V ι) (γ : LaMod Dw l ≃ₗ[𝓞 D.host.E] LaMod Dw l)
    (κ : GA D V) (β : GL (Fin V.rank) (EAf D)) (hκ : finE V κ ∈ St β) (Pg : Finset (Pl D.host.E))
    (hPg : l.Mb = ∏ PP ∈ Pg, PP.asIdeal)
    (hdet : ∀ PP ∈ Pg, ((redFn β PP (finE V κ) : GL _ _) : Matrix (Fin V.rank) (Fin V.rank) (kP PP)).det = 1)
    (h : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat V 1,
      finVec V (ι (liftLa γ a)) - (finHom V κ).1.mulVec (finVec V (ι a)) = l.M • w) : DetOne γ := by
  obtain ⟨hfg, hsp, -, -, hhat, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V 1
  have hI : l.Mb ≠ ⊥ := fun h0 => by
    have h1 := (natCast_mem_half l).1
    rw [h0, Ideal.mem_bot, Nat.cast_eq_zero] at h1
    have := l.three_le
    omega
  rw [hhat] at h
  obtain ⟨s, hs, hs'⟩ := exists_det_of_mem_St (F := D.host.F) (finHom V κ).1 rfl hκ
  exact det_eq_one_of_lift (latG V 1) hfg hsp Pg l.Mb (Mfr l) hI l.coprime hPg ι hι.1 hι.2 γ _ (liftLa_spec γ)
    (finHom V κ).1 s hs (fun PP hP => (hs' PP).trans (hdet PP hP)) (natCast_mem_half l).1 h

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem latEmb_iotaW {T : Full D} (hT : LawsFull T) (ι : Fin D.R.m) : LatEmb (Wc D ι) (iotaW T.J ι) := by
  obtain ⟨hr, _, _, _, _, _, _, hL, -⟩ := hT.j.adPin _ (inR_succ ι) T.σ₀ T.toCore.good_σ₀
  have key : ∀ (V : HSp D) (_ : V = Wc D ι) (hr : V.rank = D.R.r),
      LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota ((ι : ℕ) + 1)) →
      LatEmb (Wc D ι) (iotaW T.J ι) := by
    rintro _ rfl _ h
    exact h
  exact key _ (hT.p.spaceW _ (inR_succ ι) _ T.toCore.good_σ₀) hr hL

theorem detOne_of_levelPin {T : Full D} [Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F} (hT : LawsFull T)
    {ι : Fin D.R.m} {ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)}
    (hℓ : LevelPin R ι ℓ) (hPg : T.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal) {g : G}
    (hg : ∀ PP : R.Pg, ((R.eG g PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1) : DetOne (ℓ g) := by
  obtain ⟨κ, ⟨-, hκ, hr⟩, h⟩ := hℓ g
  refine detOne_of_lift (Wc D ι) _ (latEmb_iotaW hT ι) _ κ (R.βW ι) (parLev_St hκ) R.Pg hPg (fun PP hP => ?_) h
  have e : upperLeftBlock (r_le_rank_Wc ι) (redFn (R.βW ι) PP (finE (Wc D ι) κ)) = R.eG g ⟨PP, hP⟩ := congrFun hr ⟨PP, hP⟩
  have hb : redFn (R.βW ι) PP (finE (Wc D ι) κ) ∈ blockTri (blk2 D.R.r) := fun i j hij => by
    have hi : i.val < D.R.r := (rank_Wc ι) ▸ i.2
    have hj : j.val < D.R.r := (rank_Wc ι) ▸ j.2
    simp [blk2, hi, hj] at hij
  rw [← hg ⟨PP, hP⟩, ← e, upper_block_val_submatrix _ hb]
  exact (Matrix.det_submatrix_equiv_self (finCongr (rank_Wc ι).symm) _).symm

end GlobalTheory.TraceLattice
end
end
