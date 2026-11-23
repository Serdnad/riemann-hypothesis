module

public import Formalism.LocalRingCardinality.Bundle002
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapStab
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapLoc
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Formalism.SatakeDualWeyl.Bundle001
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle002
public import Formalism.HermitianLattices.StatementLat
public import Formalism.SatakeDualWeyl.DefsCS
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.Gaps.CC.Idx

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.UG.P Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.Gaps.LG
open scoped TensorProduct

section Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

end Defs

section SA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

theorem inverse_in_adic_integers (c : 𝓞 F) (w : HeightOneSpectrum (𝓞 F)) [Decidable (Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) c) < 1)] :
    (if Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) c) < 1 then (0 : w.adicCompletion F)
      else (algebraMap (𝓞 F) (w.adicCompletion F) c)⁻¹) ∈ w.adicCompletionIntegers F := by
  split_ifs with h
  · exact zero_mem _
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀]
    have h1 : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) c) = 1 :=
      le_antisymm ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (levelaf_int_mem_v w c)) (not_lt.1 h)
    rw [h1, inv_one]


open Classical in
def a_u (c : 𝓞 F) : FiniteAdeleRing (𝓞 F) F :=
  ⟨fun w => if Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) c) < 1 then (0 : w.adicCompletion F)
      else (algebraMap (𝓞 F) (w.adicCompletion F) c)⁻¹, Filter.Eventually.of_forall fun w => inverse_in_adic_integers c w⟩

theorem a_u_mem (c : 𝓞 F) : a_u c ∈ intAd F := fun w => inverse_in_adic_integers c w

theorem mem_S_of_loc (x : E ⊗[F] FiniteAdeleRing (𝓞 F) F) (h : ∀ w, prV (E := E) w x ∈ intV E w) :
    x ∈ tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) := by
  classical
  obtain ⟨c, hc0, hc⟩ := loc_int_bound F E
  have hfin := levelaf_finite_places c hc0
  have key : x = ∑ v ∈ hfin.toFinset, afsplitIE v (prV (E := E) v x) +
      ((1 : E) ⊗ₜ[F] a_u c) * (levelafC E c * x) := by
    rw [← sub_eq_zero]
    apply afsplit_inj
    intro w

    rw [map_sub, map_add (f := _), map_sum, map_mul, map_mul, sub_eq_zero, afsplit_prV_tmul]
    unfold levelafC
    rw [afsplit_prV_tmul]
    by_cases hw : w ∈ hfin.toFinset
    · rw [Finset.sum_eq_single w (fun v _ hv => afsplit_prV_IE_ne v w (Ne.symm hv) _)
        (fun h => absurd hw h), afsplit_prV_IE]
      have h0 : (a_u c) w = 0 := if_pos (by simpa using hw)
      rw [h0, TensorProduct.tmul_zero, zero_mul, add_zero]
    · rw [Finset.sum_eq_zero (fun v hv => afsplit_prV_IE_ne v w (by rintro rfl; exact hw hv) _), zero_add]
      have h0 : (a_u c) w = (algebraMap (𝓞 F) (w.adicCompletion F) c)⁻¹ := if_neg (by simpa using hw)
      rw [h0, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        show (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) c) w = algebraMap (𝓞 F) (w.adicCompletion F) c from rfl,
        inv_mul_cancel₀ (levelaf_algebraMap_ne_zero w c hc0), ← Algebra.TensorProduct.one_def, one_mul]
  rw [key]
  refine add_mem (Subring.sum_mem _ fun v _ => afsplit_IE_int v _ (h v)) (mul_mem ?_ (hc x h))
  exact Subring.subset_closure (Or.inr ⟨⟨a_u c, a_u_mem c⟩, rfl⟩)

end SA

section SP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]


end SP

section SL

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

end SL

section K

end K

section TAbs

variable {A : Type} [CommRing A] (O : Subring A) {n : Type} [Fintype n] [DecidableEq n] (i0 : n) (p q qi : A)
  (Lb Ld : Submodule O (n → A))

variable (hp : p ∈ O) (hq : q ∈ O) (hqi : q * qi = 1)
  (mLb : ∀ y, y ∈ Lb ↔ (∃ c ∈ O, y i0 = p * c) ∧ ∀ i, i ≠ i0 → y i ∈ O)
  (mLd : ∀ y, y ∈ Ld ↔ q * y i0 ∈ O ∧ ∀ i, i ≠ i0 → y i ∈ O)






end TAbs

section TConc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem t_unit_inv {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (τ : A →+* A) (g : GL n A)
    (hg : g ∈ UJ τ (1 : Matrix n n A)) (i j : n) : ((g⁻¹ : GL n A) : Matrix n n A) i j = τ ((g : Matrix n n A) j i) := by
  have h : cT τ (g : Matrix n n A) * 1 * (g : Matrix n n A) = 1 := hg
  rw [Matrix.mul_one] at h
  have h2 : ((g⁻¹ : GL n A) : Matrix n n A) = cT τ (g : Matrix n n A) := by
    calc ((g⁻¹ : GL n A) : Matrix n n A) = (cT τ (g : Matrix n n A) * (g : Matrix n n A)) * ((g⁻¹ : GL n A) : Matrix n n A) := by
          rw [h, Matrix.one_mul]
      _ = cT τ (g : Matrix n n A) := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [h2]
  rfl

variable {k : ℕ} (P : Par F E k)

end TConc

section TMain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end TMain

section Asm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable {k : ℕ} (P : Par F E k)

variable {P} {f : ℕ}

end Asm

section Host

variable {R : Ranks} (H : Host R)

end Host

end Formalism.MainNotions.Gaps.CC.Idx

end
end

section

noncomputable section

namespace Formalism.MainNotions.Gaps.Loc

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hom_int (w : HeightOneSpectrum (𝓞 F)) (ρ : E →+* w.adicCompletion F) (x : 𝓞 E) :
    ρ (x : E) ∈ w.adicCompletionIntegers F := by
  obtain ⟨P, hP, hP0⟩ := RingOfIntegers.isIntegral_coe x
  have h2 : IsIntegral (w.adicCompletionIntegers F) (ρ (x : E)) := by
    refine ⟨P.map (Int.castRingHom _), hP.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap (w.adicCompletionIntegers F) (w.adicCompletion F)).comp (Int.castRingHom _) =
        ρ.comp (algebraMap ℤ E) := RingHom.ext_int _ _
    rw [e, ← Polynomial.hom_eval₂, hP0, map_zero]
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := w.adicCompletionIntegers F)
    (K := w.adicCompletion F)).1 h2
  rw [← hy]; exact y.2

theorem fst_int (w : HeightOneSpectrum (𝓞 F))
    (φ : E ⊗[F] w.adicCompletion F ≃+* w.adicCompletion F × w.adicCompletion F)
    (halg : ∀ a : w.adicCompletion F, φ ((1 : E) ⊗ₜ[F] a) = (a, a))
    (s : E ⊗[F] w.adicCompletion F) (hs : s ∈ intV E w) : (φ s).1 ∈ w.adicCompletionIntegers F := by
  have hle : intV E w ≤ (w.adicCompletionIntegers F).toSubring.comap
      ((RingHom.fst _ _).comp φ.toRingHom) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨_, ⟨y, rfl⟩⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)
    · exact hom_int w (((RingHom.fst _ _).comp φ.toRingHom).comp (inclE (F := F) (w.adicCompletion F))) y
    · show (φ ((1 : E) ⊗ₜ[F] c)).1 ∈ w.adicCompletionIntegers F
      rw [halg]; exact hc
  exact hle hs

theorem exists_spl {K : Type} [Field K] [Algebra F K] (sig : E →ₐ[F] E) (hsig : ∀ x, sig (sig x) = x)
    (h2 : Module.finrank F E = 2) (b : E) (hb0 : b ≠ 0) (hb : sig b = -b) (ψ : E →ₐ[F] K) :
    ∃ φ : E ⊗[F] K ≃+* K × K, (∀ x, φ (sigR sig K x) = swapR _ (φ x)) ∧
      (∀ a : K, φ ((1 : E) ⊗ₜ[F] a) = (a, a)) ∧ ∀ x : E, (φ (inclE (F := F) K x)).1 = ψ x := by
  obtain ⟨φ, hφ⟩ := Formalism.MainNotions.Gaps.LG.sc_exists_iso sig h2 ψ b hb0 hb
  refine ⟨φ, fun x => ?_, fun a => ?_, fun x => ?_⟩
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
    | tmul x c =>
      have : sigR sig K (x ⊗ₜ[F] c) = sig x ⊗ₜ[F] c := rfl
      rw [this, hφ, hφ, hsig]; rfl
  · rw [hφ]; simp
  · have : inclE (F := F) K x = x ⊗ₜ[F] (1 : K) := rfl
    rw [this, hφ, one_mul]

theorem fr_lat_of {k : ℕ} (w : HeightOneSpectrum (𝓞 F))
    (φ : E ⊗[F] w.adicCompletion F ≃+* w.adicCompletion F × w.adicCompletion F)
    (halg : ∀ a : w.adicCompletion F, φ ((1 : E) ⊗ₜ[F] a) = (a, a))
    (Λ : Submodule (𝓞 E) (Fin k → E)) (B : GL (Fin k) E)
    (h1 : ∀ x ∈ Λ, ∀ a, (((B⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ x) a ∈ (algebraMap (𝓞 E) E).range)
    (N : ℕ) (hN : (N : 𝓞 F) ∉ w.asIdeal)
    (h2 : ∀ i, (N : E) • ((B : Matrix (Fin k) (Fin k) E) *ᵥ Pi.single i 1) ∈ Λ)
    (t : Fin k → w.adicCompletion F) :
    (∃ x ∈ Formalism.L2.Herm.locL w Λ, ∀ a, (φ (x a)).1 = t a) ↔
      ∀ a, (((bc (((RingHom.fst _ _).comp φ.toRingHom).comp (inclE (F := F) (w.adicCompletion F))) B)⁻¹ :
        GL (Fin k) (w.adicCompletion F)) : Matrix (Fin k) (Fin k) (w.adicCompletion F)).mulVec t a ∈
          w.adicCompletionIntegers F := by
  set π : E ⊗[F] w.adicCompletion F →+* w.adicCompletion F := (RingHom.fst _ _).comp φ.toRingHom with hπ
  set ρ : E →+* w.adicCompletion F := π.comp (inclE (F := F) (w.adicCompletion F)) with hρ
  have hπa : ∀ s, π s = (φ s).1 := fun _ => rfl
  have hinv : (((bc ρ B)⁻¹ : GL (Fin k) (w.adicCompletion F)) : Matrix (Fin k) (Fin k) (w.adicCompletion F)) =
      ((B⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E).map ρ := by
    rw [← map_inv]; rfl
  have hval : ((bc ρ B : GL (Fin k) (w.adicCompletion F)) : Matrix (Fin k) (Fin k) (w.adicCompletion F)) =
      (B : Matrix (Fin k) (Fin k) E).map ρ := rfl
  constructor
  · rintro ⟨x, hx, hxt⟩
    have ht : t = fun a => π (x a) := funext fun a => (hxt a).symm
    rw [ht]
    clear ht hxt
    unfold Formalism.L2.Herm.locL latS at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      intro a
      have e1 : ((((B⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E).map ρ) *ᵥ
          (fun b => π (inclE (F := F) (w.adicCompletion F) (l b)))) a =
          ρ ((((B⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ l) a) :=
        (RingHom.map_mulVec ρ _ l a).symm
      rw [hinv, e1]
      obtain ⟨y, hy⟩ := h1 l hl a
      rw [← hy]
      exact hom_int w ρ y
    | zero =>
      intro a
      have : (fun b => π ((0 : Fin k → E ⊗[F] w.adicCompletion F) b)) = 0 := by
        funext b; simp
      rw [this, mulVec_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      intro a
      have : (fun b => π ((x + y) b)) = (fun b => π (x b)) + fun b => π (y b) := by
        funext b; simp
      rw [this, mulVec_add]
      exact add_mem (hx a) (hy a)
    | smul s x _ hx =>
      intro a
      have : (fun b => π ((s • x) b)) = π (s : E ⊗[F] w.adicCompletion F) • fun b => π (x b) := by
        funext b
        show π ((s : E ⊗[F] w.adicCompletion F) * x b) = π (s : E ⊗[F] w.adicCompletion F) * π (x b)
        rw [map_mul]
      rw [this, mulVec_smul]
      exact mul_mem (fst_int w φ halg _ s.2) (hx a)
  · intro hu
    set u : Fin k → w.adicCompletion F :=
      (((bc ρ B)⁻¹ : GL (Fin k) (w.adicCompletion F)) : Matrix (Fin k) (Fin k) (w.adicCompletion F)) *ᵥ t with hudef
    have ht : t = (B : Matrix (Fin k) (Fin k) E).map ρ *ᵥ u := by
      rw [← hval, hudef, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    have hNv : Valued.v ((N : ℕ) : w.adicCompletion F) = 1 := by
      have := Formalism.MainNotions.Gaps.LG.sc_val_one w (N : 𝓞 F) hN
      simpa using this
    have hN0 : ((N : ℕ) : w.adicCompletion F) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hNv
      exact zero_ne_one hNv
    have hNi : ((N : ℕ) : w.adicCompletion F)⁻¹ ∈ w.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hNv, inv_one]
    let s : Fin k → intV E w := fun i =>
      ⟨(1 : E) ⊗ₜ[F] (u i * ((N : ℕ) : w.adicCompletion F)⁻¹),
        Formalism.MainNotions.Gaps.LG.sc_right_mem w _ (mul_mem (hu i) hNi)⟩
    let g : Fin k → Fin k → E ⊗[F] w.adicCompletion F := fun i a =>
      inclE (F := F) (w.adicCompletion F) (((N : E) • ((B : Matrix (Fin k) (Fin k) E) *ᵥ Pi.single i 1)) a)
    refine ⟨∑ i, s i • g i, ?_, fun a => ?_⟩
    · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h2 i, rfl⟩)
    · have hB : ∀ i, ((B : Matrix (Fin k) (Fin k) E) *ᵥ Pi.single i 1) a = (B : Matrix (Fin k) (Fin k) E) a i := by
        intro i
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      have hterm : ∀ i, π ((s i • g i) a) = ρ ((B : Matrix (Fin k) (Fin k) E) a i) * u i := by
        intro i
        show π (((1 : E) ⊗ₜ[F] (u i * ((N : ℕ) : w.adicCompletion F)⁻¹)) * g i a) = _
        rw [map_mul, hπa ((1 : E) ⊗ₜ[F] _), halg]
        show u i * ((N : ℕ) : w.adicCompletion F)⁻¹ *
          ρ (((N : E) • ((B : Matrix (Fin k) (Fin k) E) *ᵥ Pi.single i 1)) a) = _
        rw [Pi.smul_apply, smul_eq_mul, hB, map_mul, map_natCast]
        field_simp

      rw [← hπa, Finset.sum_apply, map_sum, ht]
      simp only [hterm]
      simp [Matrix.mulVec, dotProduct]

end Formalism.MainNotions.Gaps.Loc

end
end

section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.MainNotions.Gaps.CC.Stab

open Formalism.UG Formalism.UG.CS

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

theorem exists_place_two : ∃ v : HeightOneSpectrum (𝓞 F), ((2 : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have hp : Nat.Prime 2 := Nat.prime_two
  have hpZ : Prime ((2 : ℕ) : ℤ) := Nat.prime_iff_prime_int.1 hp
  obtain ⟨Q, hQ, hov⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 F)
    (Ideal.span {((2 : ℕ) : ℤ)})
  have hmem : ((2 : ℕ) : 𝓞 F) ∈ Q := by
    have : ((2 : ℕ) : ℤ) ∈ Q.under ℤ := by rw [← hov.over]; exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ.isPrime, ?_⟩, hmem⟩
  rintro rfl
  have : ((2 : ℕ) : 𝓞 F) = 0 := by simpa using hmem
  exact hp.ne_zero (by exact_mod_cast this)

instance finiteAdeleRing_nontrivial : Nontrivial (FiniteAdeleRing (𝓞 F) F) := by
  obtain ⟨v, -⟩ := exists_place_two (F := F)
  exact (evalV F v).toRingHom.domain_nontrivial

section Herm

variable [StarRing E] (σ : E →ₐ[F] E) (hσ : ∀ e, σ e = star e)
  (h : (n → E) →ₗ⋆[E] (n → E) →ₗ[E] E)







section Mass

variable (hsymm : h.IsSymm) (hpos : ∀ x : n → E, x ≠ 0 → 0 < Algebra.trace ℚ E (h x x))
  (Λ : Submodule (𝓞 E) (n → E)) (hΛ : Submodule.IsLattice E Λ)
  (hIn : ∀ g ∈ UPts σ (Formalism.UG.gram h) (FiniteAdeleRing (𝓞 F) F), globLat g Λ ∈ Formalism.HermitianLatticesTheory.genus h Λ)
  (hSurj : ∀ M ∈ Formalism.HermitianLatticesTheory.genus h Λ, ∃ g ∈ UPts σ (Formalism.UG.gram h) (FiniteAdeleRing (𝓞 F) F), globLat g Λ = M)






end Mass

end Herm

section Std

open Formalism.MainNotions.StandardLattice

variable {k : ℕ} [StarRing E] (σ : E →ₐ[F] E) (hσ : ∀ e, σ e = star e)


variable (hc : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a))





end Std

end Formalism.MainNotions.Gaps.CC.Stab
end
end
