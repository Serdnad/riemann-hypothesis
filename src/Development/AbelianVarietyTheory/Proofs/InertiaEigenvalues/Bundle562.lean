module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle046
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle177
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle336
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle541
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle082
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Kernel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem envExt_sub_mem {S A C : Type} [CommRing S] [CommRing A] [CommRing C] (G G' : A →+* C) (s : S →+* A)
    (J : Ideal S) (x a : A) (hs : G.comp s = G'.comp s) (ha : G a = G' a) (hx : x - a ∈ J.map s) :
    G x - G' x ∈ J.map (G.comp s) := by
  have e : G x - G' x = G (x - a) - G' (x - a) := by rw [map_sub, map_sub, ha]; ring
  rw [e]
  refine Ideal.sub_mem _ ?_ ?_
  · rw [← Ideal.map_map]; exact Ideal.mem_map_of_mem G hx
  · rw [hs, ← Ideal.map_map]; exact Ideal.mem_map_of_mem G' hx

theorem envExt_haus {C : Type} [CommRing C] (I : Ideal C) (h : IsHausdorff I C) (z : C) (hz : ∀ n : ℕ, z ∈ I ^ n) :
    z = 0 :=
  h.haus z fun n => by
    rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
    exact hz n



theorem envExt_agree : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (d p : B.A) (En : Env bk B d p) (C : Type) [CommRing C] (φ : C →+* C) (F F' : En.Q.A →+* C), (∀ c : C, ((l : ℕ) : C) * c = 0 → c = 0) → (∀ a, F (En.Q.D.φ a) = φ (F a)) → (∀ a, F' (En.Q.D.φ a) = φ (F' a)) → (∀ b, F (En.inl.f b) = F' (En.inl.f b)) → F (BK.hf En.inr X) = F' (BK.hf En.inr X) → F (En.inl.f d) ∈ nonZeroDivisors C → IsHausdorff ((Ideal.span {((l : ℕ) : B.A)} ⊔ B.I).map (F.comp En.inl.f)) C → F = F' := by
  intro l _ K bk B d p En C _ φ F F' hl hF hF' hb hX hd hH

  have hw : F En.w = F' En.w := by
    have h1 := congrArg F En.w_eq
    have h2 := congrArg F' En.w_eq
    rw [map_add (f := _), map_mul] at h1 h2
    have h3 : F (En.inl.f d) * F En.w = F (En.inl.f d) * F' En.w := by
      rw [hb d] at h1 ⊢
      rw [hb p] at h1
      rw [hX] at h1
      rw [h2] at h1
      linear_combination -h1
    exact (mul_cancel_left_mem_nonZeroDivisors hd).1 h3

  have hδ : ∀ a, F a = F' a → F (En.Q.D.δ a) = F' (En.Q.D.δ a) := by
    intro a ha
    have e1 := hF a
    have e2 := hF' a
    rw [En.Q.D.φ_eq, map_add (f := _), map_mul, map_pow, map_natCast] at e1 e2
    rw [← ha] at e2
    have : ((l : ℕ) : C) * (F (En.Q.D.δ a) - F' (En.Q.D.δ a)) = 0 := by
      linear_combination e1 - e2
    exact sub_eq_zero.1 (hl _ this)
  have hit : ∀ i : ℕ, F (En.Q.D.δ^[i] En.w) = F' (En.Q.D.δ^[i] En.w) := by
    intro i
    induction i with
    | zero => exact hw
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact hδ _ ih
  have hbasis : ∀ α, F (En.tb.b α) = F' (En.tb.b α) := by
    intro α
    rw [En.tb_b, map_finsuppProd, map_finsuppProd]
    refine Finsupp.prod_congr fun i _ => ?_
    rw [map_pow, map_pow, hit i]
  have hcomp : F.comp En.inl.f = F'.comp En.inl.f := RingHom.ext hb
  have key : ∀ x (n : ℕ), F x - F' x ∈ ((Ideal.span {((l : ℕ) : B.A)} ⊔ B.I) ^ n).map (F.comp En.inl.f) := by
    intro x n
    have hfin := En.tb.fin x n
    have happ := En.tb.approx x n hfin.toFinset (fun i hi => by
      by_contra h
      exact hi (hfin.mem_toFinset.2 h))
    have hsum : F (∑ i ∈ hfin.toFinset, En.inl.f (En.tb.c i x) * En.tb.b i) =
        F' (∑ i ∈ hfin.toFinset, En.inl.f (En.tb.c i x) * En.tb.b i) := by

      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_mul, hb, hbasis]
    exact envExt_sub_mem F F' En.inl.f _ _ _ hcomp hsum happ
  ext x
  exact sub_eq_zero.1 (envExt_haus _ hH _ fun n => by rw [← Ideal.map_pow]; exact key x n)

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.BSP

theorem strat_of_envCocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (d a b : ℕ) (A A' : Matrix (Fin d) (Fin d) bk.S), A * A' = bk.E ^ b • (1 : Matrix (Fin d) (Fin d) bk.S) → ∀ ε : Matrix (Fin d) (Fin d) En.Q.A, BK.hf En.inr bk.E ^ a • (A.map (BK.hf En.inl) * ε.map En.Q.D.φ) = BK.hf En.inl bk.E ^ a • (ε * A.map (BK.hf En.inr)) → (∀ (B : Obj l ↥(OL K)), (∀ k : Hom En.Q B, k.comp En.inl = k.comp En.inr → ε.map k.f = 1) ∧ ∀ k₁ k₂ k₃ : Hom En.Q B, k₁.comp En.inr = k₂.comp En.inl → k₁.comp En.inl = k₃.comp En.inl → k₂.comp En.inr = k₃.comp En.inr → ε.map k₁.f * ε.map k₂.f = ε.map k₃.f) → ∃ S : Strat bk d, S.a = a ∧ S.A = A ∧ ∀ (B : Obj l ↥(OL K)) (k : Hom En.Q B), S.ε (k.comp En.inl) (k.comp En.inr) = ε.map k.f := by
  intro l _ K bk En d a b A A' hA ε hφ hε
  have comp_assoc : ∀ {P P' P'' P''' : Obj l ↥(OL K)} (h : Hom P'' P''') (g : Hom P' P'') (f : Hom P P'),
      (h.comp g).comp f = h.comp (g.comp f) := fun _ _ _ => Hom.ext' rfl
  let c : ∀ {B : Obj l ↥(OL K)}, Hom bk.prism B → Hom bk.prism B → Hom En.Q B :=
    fun {B} f g => (En.univ B f g).choose
  have hc : ∀ {B : Obj l ↥(OL K)} (f g : Hom bk.prism B), (c f g).comp En.inl = f ∧ (c f g).comp En.inr = g :=
    fun {B} f g => (En.univ B f g).choose_spec.1
  have hu : ∀ {B : Obj l ↥(OL K)} (k : Hom En.Q B), c (k.comp En.inl) (k.comp En.inr) = k :=
    fun {B} k => ((En.univ B _ _).choose_spec.2 k ⟨rfl, rfl⟩).symm
  clear_value c
  refine ⟨Strat.mk a b A A' hA (fun f g => ε.map (c f g).f) ?_ ?_ ?_ ?_, rfl, rfl, ?_⟩
  · intro B f
    exact (hε B).1 (c f f) ((hc f f).1.trans (hc f f).2.symm)
  · intro B f g h
    exact (hε B).2 (c f g) (c g h) (c f h) ((hc f g).2.trans (hc g h).1.symm)
      ((hc f g).1.trans (hc f h).1.symm) ((hc g h).2.trans (hc f h).2.symm)
  · intro B B' k f g
    have e : c (k.comp f) (k.comp g) = k.comp (c f g) :=
      (En.univ B' (k.comp f) (k.comp g)).unique (hc _ _)
        ⟨by rw [comp_assoc, (hc f g).1], by rw [comp_assoc, (hc f g).2]⟩
    refine Eq.trans ?_ (congrArg (fun k' : Hom En.Q B' => ε.map k'.f) e).symm
    ext i j
    rfl
  · intro B f g
    have e1 : ∀ x, (c f g).f (BK.hf En.inl x) = BK.hf f x := fun x =>
      congrArg (fun k : Hom bk.prism B => k.f x) (hc f g).1
    have e2 : ∀ x, (c f g).f (BK.hf En.inr x) = BK.hf g x := fun x =>
      congrArg (fun k : Hom bk.prism B => k.f x) (hc f g).2
    have e3 : ∀ x, (c f g).f (En.Q.D.φ x) = B.D.φ ((c f g).f x) := (c f g).f_φ
    ext i j
    have h := congrArg (fun M => (c f g).f (M i j)) hφ

    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, map_mul, map_pow, map_sum, Matrix.map_apply,
    e1, e2, e3] at h
    simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply] using h
  · intro B k
    exact congrArg (fun k' : Hom En.Q B => ε.map k'.f) (hu k)

end GlobalTheory.BSP
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem bezout_Ep_derivative : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ (c : ℕ) (a b : Polynomial (Wq l bk.a)),
    a * bk.Ep + b * Polynomial.derivative bk.Ep = Polynomial.C ((l : Wq l bk.a) ^ c) := by
  intro l _ K bk
  haveI : CharZero (Wq l bk.a) := GlobalTheory.charZero_wittVector_of_field l (Fq l bk.a)
  have hirr : Irreducible (l : Wq l bk.a) := WittVector.irreducible l (k := Fq l bk.a)
  have hprime : Prime (l : Wq l bk.a) := hirr.prime
  have hP : (Ideal.span {(l : Wq l bk.a)}).IsPrime := (Ideal.span_singleton_prime hprime.ne_zero).2 hprime
  have hE : bk.Ep.IsEisensteinAt (Ideal.span {(l : Wq l bk.a)}) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [bk.monic.leadingCoeff, Ideal.mem_span_singleton]
      exact fun h => hirr.not_isUnit (isUnit_of_dvd_one h)
    · intro n hn
      exact Ideal.mem_span_singleton.2 (bk.dvd_coeff n hn)
    · obtain ⟨w, hw⟩ := bk.coeff_zero
      rw [hw, Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_two]
      intro h
      have h2 : (l : Wq l bk.a) ∣ (w : Wq l bk.a) := (mul_dvd_mul_iff_left hprime.ne_zero).1 h
      exact hirr.not_isUnit (isUnit_of_dvd_unit h2 w.isUnit)
  have hirrE : Irreducible bk.Ep := hE.irreducible hP bk.monic.isPrimitive bk.deg_pos
  let F := FractionRing (Wq l bk.a)
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective (Wq l bk.a) F)
  have hirrF : Irreducible (bk.Ep.map (algebraMap (Wq l bk.a) F)) :=
    (bk.monic.irreducible_iff_irreducible_map_fraction_map).1 hirrE
  obtain ⟨a, b, hab⟩ := hirrF.separable
  rw [Polynomial.derivative_map] at hab
  obtain ⟨d₁, hd₁, hA⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors (Wq l bk.a)) a
  obtain ⟨d₂, hd₂, hB⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors (Wq l bk.a)) b
  set A := IsLocalization.integerNormalization (nonZeroDivisors (Wq l bk.a)) a
  set B := IsLocalization.integerNormalization (nonZeroDivisors (Wq l bk.a)) b
  have hd : d₁ * d₂ ≠ 0 := mul_ne_zero (nonZeroDivisors.ne_zero hd₁) (nonZeroDivisors.ne_zero hd₂)
  have key : Polynomial.C d₂ * A * bk.Ep + Polynomial.C d₁ * B * Polynomial.derivative bk.Ep =
      Polynomial.C (d₁ * d₂) := by
    apply Polynomial.map_injective (algebraMap (Wq l bk.a) F) (IsFractionRing.injective (Wq l bk.a) F)
    simp only [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_C, hA, hB, Polynomial.derivative_map]
    simp only [Algebra.smul_def, Polynomial.algebraMap_apply, map_mul, Polynomial.C_mul]
    linear_combination (Polynomial.C (algebraMap (Wq l bk.a) F d₁) * Polynomial.C (algebraMap (Wq l bk.a) F d₂)) * hab
  obtain ⟨m, u, hu⟩ := WittVector.exists_eq_pow_p_mul' (p := l) (k := Fq l bk.a) (d₁ * d₂) hd
  refine ⟨m, Polynomial.C ((↑u⁻¹ : Wq l bk.a) * d₂) * A, Polynomial.C ((↑u⁻¹ : Wq l bk.a) * d₁) * B, ?_⟩
  have : Polynomial.C ((l : Wq l bk.a) ^ m) = Polynomial.C (↑u⁻¹ : Wq l bk.a) * Polynomial.C (d₁ * d₂) := by
    rw [hu, ← Polynomial.C_mul]
    congr 1
    rw [mul_comm, mul_assoc, Units.mul_inv, mul_one]
  rw [this, ← key]
  simp only [Polynomial.C_mul]
  ring

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_residue_basis_of_isMaximal {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) (m : Ideal R)
    [hm : m.IsMaximal] (h : m.map f ≠ ⊤) :
    ∃ (ι : Type) (b : ι → A) (i₀ : ι), b i₀ = 1 ∧
      (∀ x : A, ∃ a : ι →₀ R, x - a.sum (fun i y => f y * b i) ∈ m.map f) ∧
      ∀ a : ι →₀ R, a.sum (fun i y => f y * b i) ∈ m.map f → ∀ i, a i ∈ m := by
  first
  | exact @_root_.GlobalTheory.ClosedStatement.main
  | exact _root_.GlobalTheory.ClosedStatement.main
  | (apply _root_.GlobalTheory.ClosedStatement.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClosedStatement.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClosedStatement.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClosedStatement.main ..)

theorem isMaximal_span_l_sup_span_X (l a : ℕ) [Fact l.Prime] [NeZero a] :
    (Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {(X : (Wq l a)⟦X⟧)}).IsMaximal := by
  have hmax : (Ideal.span {(l : Wq l a)}).IsMaximal := by
    rw [← (WittVector.irreducible l (k := Fq l a)).maximalIdeal_eq]
    infer_instance
  have hsurj : Function.Surjective (constantCoeff (R := Wq l a)) := fun w => ⟨C w, by simp⟩
  have heq : Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {(X : (Wq l a)⟦X⟧)} =
      (Ideal.span {(l : Wq l a)}).comap (constantCoeff (R := Wq l a)) := by
    apply le_antisymm
    · refine sup_le ?_ ?_ <;> rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
      · rw [map_natCast]
        exact Ideal.mem_span_singleton_self _
      · simp
    · intro x hx
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hx)
      have hX : (X : (Wq l a)⟦X⟧) ∣ x - C w * l := by
        rw [X_dvd_iff, map_sub, map_mul, map_natCast, constantCoeff_C, hw, sub_self]
      have : x = C w * l + (x - C w * l) := by ring
      rw [this]
      exact Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
        (Ideal.mem_span_singleton.2 hX)
  rw [heq]
  exact Ideal.comap_isMaximal_of_surjective _ hsurj

theorem BK.map_span_l_sup_span_X_ne_top {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) :
    (Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)}).map bk.ev ≠ ⊤ := by
  let M : Ideal (Ainf l) := (IsLocalRing.maximalIdeal (OC l)).comap (Per.θ l)
  haveI hM : M.IsPrime := Ideal.comap_isPrime _ _
  let N : Ideal bk.S := M.comap bk.ev
  haveI hN : N.IsPrime := Ideal.comap_isPrime _ _
  have hl : (l : bk.S) ∈ N := by
    change Per.θ l (bk.ev l) ∈ IsLocalRing.maximalIdeal (OC l)
    rw [map_natCast, map_natCast]
    exact (Fact.out : ¬ IsUnit (l : OC l))
  have hE : bk.E ∈ N := by
    change Per.θ l (bk.ev bk.E) ∈ IsLocalRing.maximalIdeal (OC l)
    have : bk.ev bk.E ∈ RingHom.ker (Per.θ l) := bk.span_ev ▸ Ideal.mem_span_singleton_self _
    rw [RingHom.mem_ker.1 this]
    exact Ideal.zero_mem _
  have hX : (X : bk.S) ∈ N := by
    apply hN.mem_of_pow_mem bk.Ep.natDegree
    have h1 := congrArg (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) bk.monic.as_sum

    rw [map_add (f := _), map_pow, map_sum] at h1
    have hs : ∑ i ∈ Finset.range bk.Ep.natDegree, Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)
        (Polynomial.C (bk.Ep.coeff i) * Polynomial.X ^ i) ∈ N := by
      refine Ideal.sum_mem _ fun i hi => ?_
      obtain ⟨w, hw⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
      rw [hw, map_mul, map_mul, map_mul, map_natCast, map_natCast]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hl)
    have h2 := N.sub_mem hE hs
    simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X] at h1 h2
    have h3 := sub_eq_of_eq_add h1
    rwa [h3] at h2
  intro htop
  apply hM.ne_top
  rw [eq_top_iff, ← htop, Ideal.map_le_iff_le_comap]
  exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 hl) ((Ideal.span_singleton_le_iff_mem _).2 hX)

theorem BK.exists_residue_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    ∃ (ι : Type) (b : ι → Ainf l) (i₀ : ι), b i₀ = 1 ∧
      (∀ x : Ainf l, ∃ a : ι →₀ bk.S, x - a.sum (fun i y => bk.ev y * b i) ∈
        (Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)}).map bk.ev) ∧
      ∀ a : ι →₀ bk.S, a.sum (fun i y => bk.ev y * b i) ∈
        (Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)}).map bk.ev →
        ∀ i, a i ∈ Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)} := by
  intro l _ K bk
  haveI := isMaximal_span_l_sup_span_X l bk.a
  exact exists_residue_basis_of_isMaximal bk.ev _ bk.map_span_l_sup_span_X_ne_top

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP.BddDen

variable {l : ℕ} [hl : Fact l.Prime]

abbrev redMap {K : FinExt l} (bk : BK K) : bk.S →+* (OC l ⧸ Ideal.span {((l : ℕ) : OC l)}) :=
  (Ideal.Quotient.mk _).comp ((Per.θ l).comp bk.ev)

theorem redMap_coe {K : FinExt l} (bk : BK K) (p : Polynomial (Wq l bk.a)) :
    redMap bk (p : bk.S) = p.eval₂ ((redMap bk).comp PowerSeries.C) (redMap bk X) := by
  have h : (redMap bk).comp (Polynomial.coeToPowerSeries.ringHom) =
      Polynomial.eval₂RingHom ((redMap bk).comp PowerSeries.C) (redMap bk X) :=
    Polynomial.ringHom_ext (fun a => by simp) (by simp)
  exact congrArg (fun f => f p) h

theorem redMap_E {K : FinExt l} (bk : BK K) : redMap bk bk.E = redMap bk X ^ bk.Ep.natDegree := by
  rw [BK.E, redMap_coe, Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, bk.monic.coeff_natDegree,
    map_one, one_mul, add_eq_right]
  refine Finset.sum_eq_zero fun i hi => ?_
  obtain ⟨c, hc⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
  have hl0 : ((l : ℕ) : OC l ⧸ Ideal.span {((l : ℕ) : OC l)}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)})), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  rw [RingHom.comp_apply, hc, map_mul, map_mul, map_natCast, map_natCast, hl0, zero_mul, zero_mul]

theorem flat_not_isUnit {K : FinExt l} (bk : BK K) : ¬ IsUnit bk.flat := by
  intro hu
  have h0 : redMap bk bk.E = 0 := by
    have hk : bk.ev bk.E ∈ RingHom.ker (Per.θ l) := bk.span_ev ▸ Ideal.mem_span_singleton_self _
    rw [RingHom.mem_ker] at hk
    simp only [redMap, RingHom.comp_apply, hk, map_zero]
  rw [redMap_E, redMap, RingHom.comp_apply, RingHom.comp_apply, ← map_pow, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at h0
  have hX : IsUnit (bk.ev X) := bk.ev_X ▸ hu.map (WittVector.teichmuller l)
  exact PI.ArtSch.OC_l_not_unit l (isUnit_of_dvd_unit h0 ((hX.map (Per.θ l)).pow _))

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (a : Ainf l), IsUnit (inclW l a) →
    ∀ n : ℕ, ∃ (m : ℕ) (t : Ainf l), (l : Ainf l) ^ n ∣ t * a - bk.ev X ^ m := by
  intro l _ K bk a ha n
  have ha0 : a.coeff 0 ≠ 0 := by
    intro h
    have h1 := ha.map (WittVector.constantCoeff (p := l) (R := Cb l))
    rw [WittVector.constantCoeff_apply, inclW, WittVector.map_coeff, h, map_zero] at h1
    exact not_isUnit_zero h1
  have hv1 : PI.ArtSch.valb l bk.flat < 1 := by
    by_contra h
    push_neg at h
    exact flat_not_isUnit bk (isUnit_of_dvd_one
      (GlobalTheory.ArtinSchreierTilt.tiltDiv l 1 bk.flat (by rw [map_one]; exact h)))
  have hv0 : 0 < PI.ArtSch.valb l (a.coeff 0) := by
    rw [pos_iff_ne_zero]
    exact fun h => ha0 ((PreTilt.map_eq_zero (PadicComplexInt.integers l)).1 h)
  obtain ⟨m₀, hm₀⟩ := exists_pow_lt_of_lt_one hv0 hv1
  obtain ⟨c, hc⟩ := GlobalTheory.ArtinSchreierTilt.tiltDiv l (bk.flat ^ m₀) (a.coeff 0) (by rw [map_pow]; exact hm₀.le)
  obtain ⟨b, hb⟩ : (l : Ainf l) ∣ a - WittVector.teichmuller l (a.coeff 0) := by
    rw [← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub]
    simp [WittVector.constantCoeff_apply]
  have hxy : WittVector.teichmuller l c * a =
      bk.ev X ^ m₀ + (l : Ainf l) * (WittVector.teichmuller l c * b) := by
    have ha' : a = WittVector.teichmuller l (a.coeff 0) + (l : Ainf l) * b := by linear_combination hb
    have ht : WittVector.teichmuller l c * WittVector.teichmuller l (a.coeff 0) = bk.ev X ^ m₀ := by
      rw [bk.ev_X, ← map_pow, hc, map_mul, mul_comm]
    rw [ha', mul_add, ht]
    ring
  have h2 := geom_sum₂_mul (bk.ev X ^ m₀) (-((l : Ainf l) * (WittVector.teichmuller l c * b))) n
  refine ⟨m₀ * n, WittVector.teichmuller l c * ∑ i ∈ Finset.range n,
    (bk.ev X ^ m₀) ^ i * (-((l : Ainf l) * (WittVector.teichmuller l c * b))) ^ (n - 1 - i),
    -((-(WittVector.teichmuller l c * b)) ^ n), ?_⟩
  rw [pow_mul]
  linear_combination (∑ i ∈ Finset.range n,
    (bk.ev X ^ m₀) ^ i * (-((l : Ainf l) * (WittVector.teichmuller l c * b))) ^ (n - 1 - i)) * hxy + h2

end GlobalTheory.BSP.BddDen
end
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem wmap_ev_eq : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type) [CommRing O] [IsDomain O]
    [CharP O l] [PerfectRing O l] (ψ ψ' : OCb l →+* O), ψ bk.flat ≠ 0 →
    IsAdicComplete (Ideal.span {ψ bk.flat}) O →
    (∀ s : bk.S, ψ ((bk.ev s).coeff 0) = ψ' ((bk.ev s).coeff 0)) →
    ∀ s : bk.S, WittVector.map ψ (bk.ev s) = WittVector.map ψ' (bk.ev s) := by
  intro l _ K bk O _ _ _ _ ψ ψ' h0 hc h s
  have hval : ∀ y : Fq l bk.a, ψ (Fq.val l bk.a y) = ψ' (Fq.val l bk.a y) := fun y => by
    have := h (C (WittVector.teichmuller l y))
    rwa [bk.ev_C, wA_teich, WittVector.teichmuller_coeff_zero] at this
  have hflat : ψ bk.flat = ψ' bk.flat := by
    have := h X
    rwa [bk.ev_X, WittVector.teichmuller_coeff_zero] at this
  have hX : ((WittVector.map ψ).comp bk.ev) X = WittVector.teichmuller l (ψ bk.flat) := by
    rw [RingHom.comp_apply, bk.ev_X, WittVector.map_teichmuller]
  have hcomp := (GlobalTheory.T.wittVector_teichmuller_isAdicComplete_of_perfect l O (ψ bk.flat) h0 hc).1
  refine RingHom.congr_fun (ringHom_ext_of_sep ((WittVector.map ψ).comp bk.ev) ((WittVector.map ψ').comp bk.ev)
    (fun w => ?_) ?_ fun x hx => ?_) s
  · simp only [RingHom.comp_apply, bk.ev_C]
    refine WittVector.ext fun n => ?_
    simp only [wA, AlgHom.coe_mk, WittVector.map_coeff]
    exact hval _
  · rw [hX, RingHom.comp_apply, bk.ev_X, WittVector.map_teichmuller, hflat]
  · rw [hX] at hx
    refine IsHausdorff.haus' (I := Ideal.span {WittVector.teichmuller l (ψ bk.flat)}) x fun n => ?_
    simp only [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton.2 (hx n)

end GlobalTheory.BSP
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_isPer : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ τ : Ainf l, bk.IsPer τ := by
  intro l hl K bk
  obtain ⟨ζ, e, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : e.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps e := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  set x : Ainf l := Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e) with hx
  have hxl : x ^ l = Per.tm e := by
    rw [hx, ← map_pow, frobeniusEquiv_symm_pow_p]
  have hφx : WittVector.frobenius x = Per.tm e := by
    rw [hx, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def,
      frobeniusEquiv_symm_pow_p]
  have hξ : GlobalTheory.MemLoc.xi e * (x - 1) = Per.tm e - 1 := by
    rw [GlobalTheory.MemLoc.xi, ← hx, geom_sum_mul, hxl]
  have hsp : Ideal.span {bk.ev bk.E} = Ideal.span {GlobalTheory.MemLoc.xi e} :=
    bk.span_ev.trans (GlobalTheory.MemLoc.ker_theta_eq_span_xi hE)
  obtain ⟨ω, hω⟩ := Ideal.span_singleton_eq_span_singleton.1 hsp.symm
  obtain ⟨η, hη⟩ := GlobalTheory.T.exists_ainf_unit_frobenius_eq_mul l ω
  refine ⟨(x - 1) * η, ?_, e, ω * η, hE, ?_⟩
  · rw [map_mul, map_sub, map_one, hφx, hη, ← hω, ← hξ]
    ring
  · rw [map_mul, map_sub, map_one, hφx, hη, Units.val_mul]
    rw [mul_comm]
end GlobalTheory.BSP
end
