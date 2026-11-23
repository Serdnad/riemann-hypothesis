module

public import Formalism.LocalRingCardinality.Bundle006
public import Formalism.LocalToGlobal.HermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle050
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle745
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle051
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

namespace GlobalTheory.EX.Glue

open Formalism.BasicNotions NumberField IsDedekindDomain

theorem exists_clear {R : Type} [CommRing R] [IsDedekindDomain R] (c : R) (hc : c ≠ 0)
    (w₀ : HeightOneSpectrum R) :
    ∃ t : R, t ∉ w₀.asIdeal ∧ ∀ w : HeightOneSpectrum R, w ≠ w₀ → ∃ s : R, s ∉ w.asIdeal ∧ c ∣ s * t := by
  classical
  haveI := w₀.isMaximal
  have hI : Ideal.span {c} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using hc
  obtain ⟨Q, hQ, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hI w₀.asIdeal
  have hQn : ¬ Q ≤ w₀.asIdeal := by
    intro h
    rw [sup_eq_left.2 h] at hQ
    exact w₀.isPrime.ne_top hQ
  obtain ⟨t, htQ, ht⟩ := SetLike.not_le_iff_exists.1 hQn
  refine ⟨t, ht, fun w hw => ?_⟩
  generalize Multiset.count w₀.asIdeal _ = k at hfac
  have hP : ¬ w₀.asIdeal ^ k ≤ w.asIdeal := by
    intro h
    haveI := w.isPrime
    have h' : w₀.asIdeal ≤ w.asIdeal := Ideal.IsPrime.le_of_pow_le h
    exact hw (HeightOneSpectrum.ext (w₀.isMaximal.eq_of_le w.isPrime.ne_top h').symm)
  obtain ⟨s, hsP, hs⟩ := SetLike.not_le_iff_exists.1 hP
  refine ⟨s, hs, ?_⟩
  rw [← Ideal.mem_span_singleton, hfac]
  exact Ideal.mul_mem_mul hsP htQ

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]

def locSub (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) V) : Submodule (𝓞 K) V where
  carrier := {x | InLoc w M x}
  zero_mem' := ⟨1, (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top, by simp⟩
  add_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
    refine ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ hx
    · rw [mul_smul]; exact M.smul_mem _ hy
  smul_mem' := by
    rintro a x ⟨s, hs, hx⟩
    exact ⟨s, hs, by rw [smul_comm]; exact M.smul_mem _ hx⟩

theorem mem_locSub {w : HeightOneSpectrum (𝓞 K)} {M : Submodule (𝓞 K) V} {x : V} :
    x ∈ locSub w M ↔ InLoc w M x := Iff.rfl

theorem inLoc_iInf (B : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) V)
    (hsat : ∀ w (t : 𝓞 K) (x : V), t ∉ w.asIdeal → t • x ∈ B w → x ∈ B w)
    (hden : ∀ x : V, ∃ c : 𝓞 K, c ≠ 0 ∧ ∀ w, c • x ∈ B w) (w₀ : HeightOneSpectrum (𝓞 K)) (x : V) :
    InLoc w₀ (⨅ w, B w) x ↔ x ∈ B w₀ := by
  constructor
  · rintro ⟨s, hs, hx⟩
    exact hsat w₀ s x hs ((Submodule.mem_iInf _).1 hx w₀)
  · intro hx
    obtain ⟨c, hc, hcx⟩ := hden x
    obtain ⟨t, ht, h⟩ := exists_clear c hc w₀
    refine ⟨t, ht, (Submodule.mem_iInf _).2 fun w => ?_⟩
    by_cases hw : w = w₀
    · subst hw; exact (B w).smul_mem _ hx
    · obtain ⟨s, hs, d, hd⟩ := h w hw
      refine hsat w s _ hs ?_
      rw [← mul_smul, hd, mul_comm, mul_smul]
      exact (B w).smul_mem _ (hcx w)

theorem exists_glue : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V) (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (A : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) V), S.Finite →
    (∀ x : V, ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ M) →
    (∀ w ∈ S, (∀ (t : 𝓞 K) (x : V), t ∉ w.asIdeal → t • x ∈ A w → x ∈ A w) ∧
      ∃ n : ℕ, n ≠ 0 ∧ (∀ x ∈ M, n • x ∈ A w) ∧ ∀ x ∈ A w, InLoc w M (n • x)) →
    ∃ N : Submodule (𝓞 K) V, (∀ w ∈ S, ∀ x, InLoc w N x ↔ x ∈ A w) ∧
      ∀ w ∉ S, ∀ x, InLoc w N x ↔ InLoc w M x := by
  intro K V _ _ _ _ _ _ M S A hS hM hA
  classical
  let B : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) V := fun w => if w ∈ S then A w else locSub w M
  have hB1 : ∀ w ∈ S, B w = A w := fun w hw => if_pos hw
  have hB2 : ∀ w ∉ S, B w = locSub w M := fun w hw => if_neg hw
  have hsat : ∀ w (t : 𝓞 K) (x : V), t ∉ w.asIdeal → t • x ∈ B w → x ∈ B w := by
    intro w t x ht hx
    by_cases hw : w ∈ S
    · rw [hB1 w hw] at hx ⊢
      exact (hA w hw).1 t x ht hx
    · rw [hB2 w hw] at hx ⊢
      obtain ⟨s, hs, hx⟩ := hx
      exact ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, by rwa [mul_smul]⟩
  have hn : ∀ w, ∃ n : ℕ, n ≠ 0 ∧ (w ∈ S → ∀ x ∈ M, n • x ∈ A w) := by
    intro w
    by_cases hw : w ∈ S
    · obtain ⟨n, hn, h, -⟩ := (hA w hw).2
      exact ⟨n, hn, fun _ => h⟩
    · exact ⟨1, one_ne_zero, fun h => absurd h hw⟩
  choose n hn0 hn using hn
  have hden : ∀ x : V, ∃ c : 𝓞 K, c ≠ 0 ∧ ∀ w, c • x ∈ B w := by
    intro x
    obtain ⟨m, hm, hx⟩ := hM x
    refine ⟨(((∏ w ∈ hS.toFinset, n w) * m : ℕ) : 𝓞 K), ?_, fun w => ?_⟩
    · exact Nat.cast_ne_zero.2 (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun w _ => hn0 w) hm)
    · rw [Nat.cast_smul_eq_nsmul, mul_smul]
      by_cases hw : w ∈ S
      · rw [hB1 w hw]
        obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem n (hS.mem_toFinset.2 hw)
        rw [hd, mul_comm, mul_smul]
        exact nsmul_mem (hn w hw _ hx) d
      · rw [hB2 w hw]
        exact ⟨1, (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top, by
          rw [one_smul]; exact nsmul_mem hx _⟩
  refine ⟨⨅ w, B w, fun w hw x => ?_, fun w hw x => ?_⟩
  · rw [inLoc_iInf B hsat hden, hB1 w hw]
  · rw [inLoc_iInf B hsat hden, hB2 w hw, mem_locSub]

end GlobalTheory.EX.Glue
end

section

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unipotentTypeLevel_character_finiteOrder_rootsOfUnity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (gp : Fin 2 → ℕ) (G : GLoc F E σ gp) (a t skip fc : ℕ) (zl : Bool) (_ : GLev S G a t 0 skip fc zl) (K : Type) [Field K] (s : K →+* ℂ), (∀ i, (gp i).Prime) → (∀ i, ∃ ζ : K, IsPrimitiveRoot ζ (gp i)) → ∃ N : ℕ, 0 < N ∧ ∀ x : S.U, ((S.chi x : ℂˣ) : ℂ) ^ N = 1 ∧ ∃ r : K, s r = ((S.chi x : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.unipotent_type_character_finite_order | exact GlobalTheory.unipotent_type_character_finite_order | (intros; apply GlobalTheory.unipotent_type_character_finite_order <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.HeckeSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


omit [NumberField E] in
theorem under_eq_iff_map_le (v : HeightOneSpectrum (𝓞 F)) (Q : HeightOneSpectrum (𝓞 E)) :
    Q.under (𝓞 F) = v ↔ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ Q.asIdeal := by
  rw [Ideal.map_le_iff_le_comap]
  constructor
  · rintro rfl
    exact le_rfl
  · intro h
    apply HeightOneSpectrum.ext
    exact (v.isMaximal.eq_of_le (Q.under (𝓞 F)).isPrime.ne_top h).symm

theorem under_eq_iff (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E))
    (h : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) (Q : HeightOneSpectrum (𝓞 E)) :
    Q.under (𝓞 F) = v ↔ (Q = P ∨ Q = P') := by
  rw [under_eq_iff_map_le, h, Q.isPrime.mul_le]
  refine or_congr ⟨fun h => ?_, fun h => h ▸ le_rfl⟩ ⟨fun h => ?_, fun h => h ▸ le_rfl⟩
  · exact HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h).symm
  · exact HeightOneSpectrum.ext (P'.isMaximal.eq_of_le Q.isPrime.ne_top h).symm

theorem not_mul_le_sq (P P' : HeightOneSpectrum (𝓞 E)) (hne : P ≠ P') :
    ¬ P.asIdeal * P'.asIdeal ≤ P.asIdeal ^ 2 := by
  intro h
  rw [← Ideal.dvd_iff_le, sq, mul_dvd_mul_iff_left P.ne_bot, Ideal.dvd_iff_le] at h
  exact hne (HeightOneSpectrum.ext (P'.isMaximal.eq_of_le P.isPrime.ne_top h).symm)

theorem val_eq_inv_of_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (χ : Formalism.L2.Host.HChar E) (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E)),
    χ.TrivOn F → χ.UnrAt P → χ.UnrAt P' → P ≠ P' →
    Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal → χ.val P' = (χ.val P)⁻¹ := by
  intro F E _ _ _ _ _ χ v P P' hχ h1 h2 hne hv
  classical
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have h0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hab : aboveF (L := E) F v = {P, P'} := by
    ext Q
    rw [aboveF, Set.Finite.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
    exact under_eq_iff v P P' hv Q
  have key : ∀ Q : HeightOneSpectrum (𝓞 E), Q.under (𝓞 F) = v → χ.UnrAt Q →
      ¬ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ Q.asIdeal ^ 2 →
      χ.locK Q (upF F (Units.mk0 π h0)) = χ.val Q := by
    intro Q hQ hunr hu
    refine χ.val_eq hunr _ ?_
    subst hQ
    show Valued.v ((algebraMap F E π : E) : Q.adicCompletion E) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', GlobalTheory.MuConj.valuation_up Q hu, hπ]
  have h := hχ.1 v (Units.mk0 π h0)
  rw [HChar.resFin_apply, hab, Finset.prod_pair hne,
    key P ((under_eq_iff v P P' hv _).2 (Or.inl rfl)) h1 (hv ▸ not_mul_le_sq P P' hne),
    key P' ((under_eq_iff v P P' hv _).2 (Or.inr rfl)) h2
      (by rw [hv, mul_comm]; exact not_mul_le_sq P' P hne.symm)] at h
  exact eq_inv_of_mul_eq_one_right h

end GlobalTheory.HeckeSplit
end

section

open Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.conj_on_inter_quadraticKernels_of_trace_eq : ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (ρ ρ' : Γ →* GL (Fin n) k) (χ₁ χ₂ : Γ →* ℤˣ), IsSSRep ρ → IsSSRep ρ' → (∀ g, χ₁ g = 1 → χ₂ g = 1 → ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace = ((ρ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) → ∃ P : GL (Fin n) k, ∀ g, χ₁ g = 1 → χ₂ g = 1 → ρ' g = P⁻¹ * ρ g * P := by
  first | exact @GlobalTheory.QuadKernelConj.conj_on_ker_inf_ker | exact GlobalTheory.QuadKernelConj.conj_on_ker_inf_ker | (intros; apply GlobalTheory.QuadKernelConj.conj_on_ker_inf_ker <;> assumption)
end
