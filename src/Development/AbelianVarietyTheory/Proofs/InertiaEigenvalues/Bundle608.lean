module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle572
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle103
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle592
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle591
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle514
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle567
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle566
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle593
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle579
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle594
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEvaluationConvergentSeriesBcris
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.EnvLevel

theorem mem_smul_top_of_mem_map_C {R : Type} [CommRing R] (I : Ideal R) (p : MvPolynomial ℕ R)
    (hp : p ∈ Ideal.map (MvPolynomial.C : R →+* MvPolynomial ℕ R) I) :
    p ∈ I • (⊤ : Submodule R (MvPolynomial ℕ R)) := by
  rw [MvPolynomial.mem_map_C_iff] at hp
  rw [MvPolynomial.as_sum p]
  refine Submodule.sum_mem _ fun s _ => ?_
  have : MvPolynomial.monomial s (p.coeff s) = p.coeff s • MvPolynomial.monomial s (1 : R) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [this]
  exact Submodule.smul_mem_smul (hp s) Submodule.mem_top

theorem tri_map {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) (l i : ℕ) (v : Aˣ)
    (a b : MvPolynomial ℕ A)
    (ha : a ∈ MvPolynomial.supported A (Set.Iio i)) (hb : b ∈ MvPolynomial.supported A (Set.Iio i)) :
    ∃ (v' : Rˣ) (a' b' : MvPolynomial ℕ R), a' ∈ MvPolynomial.supported R (Set.Iio i) ∧
      b' ∈ MvPolynomial.supported R (Set.Iio i) ∧
      MvPolynomial.map f (MvPolynomial.C (v : A) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b) =
        MvPolynomial.C (v' : R) * MvPolynomial.X i ^ l + a' * MvPolynomial.X i + b' := by
  refine ⟨Units.map f.toMonoidHom v, MvPolynomial.map f a, MvPolynomial.map f b, ?_, ?_, ?_⟩
  · rw [MvPolynomial.mem_supported] at ha ⊢
    exact (Finset.coe_subset.mpr (MvPolynomial.vars_map a f)).trans ha
  · rw [MvPolynomial.mem_supported] at hb ⊢
    exact (Finset.coe_subset.mpr (MvPolynomial.vars_map b f)).trans hb
  · simp [map_add (f := _), map_mul, map_pow, MvPolynomial.map_C, MvPolynomial.map_X]

end GlobalTheory.EnvLevel

theorem GlobalTheory.digitMonomials_basis_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (J : Ideal A) (r : ℕ → MvPolynomial ℕ A), (∀ i, ∃ (v : Aˣ) (a b : MvPolynomial ℕ A), a ∈ MvPolynomial.supported A (Set.Iio i) ∧ b ∈ MvPolynomial.supported A (Set.Iio i) ∧ r i - (MvPolynomial.C (v : A) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b) ∈ J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A)) → ∀ n : ℕ, (∀ x : MvPolynomial ℕ A, ∃ c : Digits l →₀ A, x - c.sum (fun α a => MvPolynomial.monomial α.1 a) ∈ Ideal.span (Set.range r) ⊔ (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A)) ∧ ∀ c : Digits l →₀ A, c.sum (fun α a => MvPolynomial.monomial α.1 a) ∈ Ideal.span (Set.range r) ⊔ (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A) → ∀ α, c α ∈ J ^ n := by
  intro l _ A _ J r hr n
  classical
  let π : MvPolynomial ℕ A →+* MvPolynomial ℕ (A ⧸ J ^ n) := MvPolynomial.map (Ideal.Quotient.mk (J ^ n))
  have hπs : Function.Surjective π := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker π = (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A) := by
    simp only [π]; rw [MvPolynomial.ker_map, Ideal.mk_ker]
  let I : Ideal (A ⧸ J ^ n) := J.map (Ideal.Quotient.mk (J ^ n))
  have hIn : I ^ n = ⊥ := by
    simp only [I]; rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  choose v a b ha hb hrab using hr
  let t : ℕ → MvPolynomial ℕ (A ⧸ J ^ n) := fun i =>
    π (MvPolynomial.C (v i : A) * MvPolynomial.X i ^ l + a i * MvPolynomial.X i + b i)
  have ht := fun i => GlobalTheory.EnvLevel.tri_map (Ideal.Quotient.mk (J ^ n)) l i (v i) (a i) (b i) (ha i) (hb i)
  obtain ⟨htli, htsp⟩ := GlobalTheory.T.triangular_system_monomial_products_basis l (A ⧸ J ^ n) t ht
  let B : Digits l × (ℕ →₀ ℕ) → MvPolynomial ℕ (A ⧸ J ^ n) := fun x =>
    MvPolynomial.monomial x.1.1 (1 : A ⧸ J ^ n) * x.2.prod fun i m => π (r i) ^ m
  have hK : ∀ i, π (r i) - t i ∈ Ideal.map (MvPolynomial.C : (A ⧸ J ^ n) →+* MvPolynomial ℕ (A ⧸ J ^ n)) I := by
    intro i
    have h1 : π (r i) - t i = π (r i - (MvPolynomial.C (v i : A) * MvPolynomial.X i ^ l + a i * MvPolynomial.X i + b i)) := by
      simp only [t, map_sub]
    have h2 : Ideal.map (MvPolynomial.C : (A ⧸ J ^ n) →+* MvPolynomial ℕ (A ⧸ J ^ n)) I =
        Ideal.map π (J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A)) := by
      simp only [I, π]
      rw [Ideal.map_map, Ideal.map_map, MvPolynomial.map_comp_C]
    rw [h1, h2]
    exact Ideal.mem_map_of_mem _ (hrab i)
  have hBK : ∀ x, B x - (MvPolynomial.monomial x.1.1 (1 : A ⧸ J ^ n) * x.2.prod fun i m => t i ^ m) ∈
      I • (⊤ : Submodule (A ⧸ J ^ n) (MvPolynomial ℕ (A ⧸ J ^ n))) := by
    intro x
    apply GlobalTheory.EnvLevel.mem_smul_top_of_mem_map_C
    rw [← Ideal.Quotient.eq]
    simp only [B, map_mul, Finsupp.prod, map_prod, map_pow]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Ideal.Quotient.eq.mpr (hK i)]
  obtain ⟨hBli, hBsp⟩ := GlobalTheory.T.basis_of_congr_basis_mod_nilpotent_ideal (A ⧸ J ^ n) (MvPolynomial ℕ (A ⧸ J ^ n)) (Digits l × (ℕ →₀ ℕ))
    _ B I n hIn htli htsp hBK
  have hBmem : ∀ k : Digits l × (ℕ →₀ ℕ), k.2 ≠ 0 → B k ∈ Ideal.span (Set.range (⇑π ∘ r)) := by
    intro k hk
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hk
    apply Ideal.mul_mem_left
    have hd : π (r i) ^ k.2 i ∣ k.2.prod fun i m => π (r i) ^ m :=
      Finset.dvd_prod_of_mem (fun i => π (r i) ^ k.2 i) hi
    obtain ⟨d, hd⟩ := hd
    rw [hd]
    apply Ideal.mul_mem_right
    exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_range_self (f := ⇑π ∘ r) i)) _
      (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))
  let S : Submodule (A ⧸ J ^ n) (MvPolynomial ℕ (A ⧸ J ^ n)) :=
    Submodule.span (A ⧸ J ^ n) (B '' {x | x.2 ≠ 0})
  have hmulS : ∀ i (p : MvPolynomial ℕ (A ⧸ J ^ n)), p * π (r i) ∈ S := by
    intro i p
    have hp : p ∈ Submodule.span (A ⧸ J ^ n) (Set.range B) := by rw [hBsp]; exact Submodule.mem_top
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      have : B k * π (r i) = B (k.1, k.2 + Finsupp.single i 1) := by
        simp only [B]
        rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
          Finsupp.prod_single_index (by simp)]
        simp only [pow_one, mul_assoc]
      rw [this]
      refine Submodule.subset_span ⟨(k.1, k.2 + Finsupp.single i 1), ?_, rfl⟩
      intro h
      have := DFunLike.congr_fun h i
      simp at this
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact S.add_mem hx hy
    | smul c x _ hx => rw [smul_mul_assoc]; exact S.smul_mem c hx
  have hspanS : ∀ x ∈ Ideal.span (Set.range (⇑π ∘ r)), ∀ p, p * x ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact fun p => hmulS i p
    | zero => intro p; simp
    | add y z _ _ hy hz => intro p; rw [mul_add]; exact S.add_mem (hy p) (hz p)
    | smul c y _ hy => intro p; rw [smul_eq_mul, ← mul_assoc]; exact hy (p * c)
  refine ⟨?_, ?_⟩
  · intro x
    have hx : π x ∈ Submodule.span (A ⧸ J ^ n) (Set.range B) := by rw [hBsp]; exact Submodule.mem_top
    obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
    let f0 := f.filter fun k => k.2 = 0
    let f1 := f.filter fun k => ¬ k.2 = 0
    let g : Digits l →₀ (A ⧸ J ^ n) := f0.mapDomain Prod.fst
    have hsplit : π x = (f0.sum fun k a => a • B k) + (f1.sum fun k a => a • B k) := by
      rw [← hf, ← Finsupp.sum_add_index' (h := fun k a => a • B k) (fun _ => zero_smul _ _)
        (fun _ _ _ => add_smul _ _ _)]
      simp only [f0, f1]
      rw [Finsupp.filter_add_filter_not]
    have h0sum : (f0.sum fun k a => a • B k) = g.sum fun α a => MvPolynomial.monomial α.1 a := by
      simp only [g]
      rw [Finsupp.sum_mapDomain_index (h := fun (α : Digits l) (a : A ⧸ J ^ n) => MvPolynomial.monomial α.1 a)
        (fun (α : Digits l) => (MvPolynomial.monomial (R := A ⧸ J ^ n) α.1).map_zero)
        (fun (α : Digits l) _ _ => (MvPolynomial.monomial (R := A ⧸ J ^ n) α.1).map_add _ _)]
      refine Finsupp.sum_congr fun k hk => ?_
      have hk2 : k.2 = 0 := by
        simp only [f0] at hk
        rw [Finsupp.support_filter, Finset.mem_filter] at hk; exact hk.2
      simp only [B, hk2, Finsupp.prod_zero_index, mul_one, MvPolynomial.smul_monomial, smul_eq_mul]
    have h1mem : (f1.sum fun k a => a • B k) ∈ Ideal.span (Set.range (⇑π ∘ r)) := by
      unfold Finsupp.sum
      refine Ideal.sum_mem _ fun k hk => ?_
      have hk2 : k.2 ≠ 0 := by
        simp only [f1] at hk
        rw [Finsupp.support_filter, Finset.mem_filter] at hk; exact hk.2
      show f1 k • B k ∈ _
      rw [MvPolynomial.smul_eq_C_mul]
      exact Ideal.mul_mem_left _ _ (hBmem k hk2)
    let sec : (A ⧸ J ^ n) → A := fun y =>
      if y = 0 then 0 else Function.surjInv (Ideal.Quotient.mk_surjective (I := J ^ n)) y
    have hsec0 : sec 0 = 0 := by simp [sec]
    have hsec : ∀ y, Ideal.Quotient.mk (J ^ n) (sec y) = y := by
      intro y
      by_cases h : y = 0
      · simp [sec, h]
      · simp only [sec, h, if_false]; exact Function.surjInv_eq _ y
    refine ⟨g.mapRange sec hsec0, ?_⟩
    have hmap : π ((g.mapRange sec hsec0).sum fun α a => MvPolynomial.monomial α.1 a) =
        g.sum fun α a => MvPolynomial.monomial α.1 a := by
      rw [map_finsuppSum, Finsupp.sum_mapRange_index (h := fun (α : Digits l) (a : A) => π (MvPolynomial.monomial α.1 a))
        (fun _ => by simp)]
      simp only [π, MvPolynomial.map_monomial, hsec]
    have hmem : x - ((g.mapRange sec hsec0).sum fun α a => MvPolynomial.monomial α.1 a) ∈
        Ideal.comap π (Ideal.map π (Ideal.span (Set.range r))) := by
      rw [Ideal.mem_comap, Ideal.map_span, ← Set.range_comp, map_sub, hmap, hsplit, ← h0sum,
        add_sub_cancel_left]
      exact h1mem
    rwa [Ideal.comap_map_of_surjective _ hπs, ← RingHom.ker_eq_comap_bot, hker] at hmem
  · intro c hc α
    have h1 : π (c.sum fun α a => MvPolynomial.monomial α.1 a) ∈ Ideal.span (Set.range (⇑π ∘ r)) := by
      have := Ideal.mem_map_of_mem π hc
      rwa [Ideal.map_sup, ← hker, (Ideal.map_eq_bot_iff_le_ker π).mpr le_rfl, sup_bot_eq, Ideal.map_span,
        ← Set.range_comp] at this
    have h2 : π (c.sum fun α a => MvPolynomial.monomial α.1 a) ∈ S := by
      simpa using hspanS _ h1 1
    have hinj : Function.Injective (fun α : Digits l => (α, (0 : ℕ →₀ ℕ))) :=
      fun _ _ h => congrArg Prod.fst h
    let g' : Digits l × (ℕ →₀ ℕ) →₀ (A ⧸ J ^ n) :=
      Finsupp.mapDomain (fun α => (α, (0 : ℕ →₀ ℕ))) (c.mapRange (Ideal.Quotient.mk (J ^ n)) (map_zero _))
    have hg' : Finsupp.linearCombination (A ⧸ J ^ n) B g' = π (c.sum fun α a => MvPolynomial.monomial α.1 a) := by
      rw [Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply,
        Finsupp.sum_mapRange_index (h := fun i a => a • (B ∘ fun α => (α, (0 : ℕ →₀ ℕ))) i)
          (fun _ => zero_smul _ _), map_finsuppSum]
      refine Finsupp.sum_congr fun β _ => ?_
      simp [B, π, MvPolynomial.smul_monomial]
    obtain ⟨l', hl', hl'eq⟩ := (Finsupp.mem_span_image_iff_linearCombination (A ⧸ J ^ n)).mp h2
    have hl : l' = g' := hBli (hl'eq.trans hg'.symm)
    have h3 : g' (α, 0) = 0 := by
      rw [← hl]; exact (Finsupp.mem_supported' (A ⧸ J ^ n) l').mp hl' _ (by simp)
    have h4 : g' (α, 0) = Ideal.Quotient.mk (J ^ n) (c α) :=
      Finsupp.mapDomain_apply_of_injective hinj (c.mapRange (Ideal.Quotient.mk (J ^ n)) (map_zero _)) α
    rw [h4] at h3
    exact Ideal.Quotient.eq_zero_iff_mem.mp h3
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory

namespace GlobalTheory.PolChar

open Formalism.L2.Host

section Comp

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def ideleInf : (AdeleRing (𝓞 E) E)ˣ →* InfiniteAdeleRing E :=
  (MonoidHom.fst _ _).comp (Units.coeHom (InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E))

def ideleAt (u : HeightOneSpectrum (𝓞 E)) : (AdeleRing (𝓞 E) E)ˣ →* u.adicCompletion E :=
  (RestrictedProduct.evalMonoidHom _ u).comp
    ((MonoidHom.snd _ _).comp (Units.coeHom (InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E)))

theorem ideleMap_localIdele_atFin (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap F E (Neutral.B1.localIdele F v (atFin v a)) =
      ∏ w ∈ aboveF (L := E) F v, Neutral.B1.localIdele E w (atFin w (upF F a)) := by
  classical
  refine Units.ext (Prod.ext ?_ (FiniteAdeleRing.ext _ fun u => ?_))
  · refine Eq.trans ?_ (map_prod (ideleInf E) _ _).symm
    refine Eq.trans ?_ (Finset.prod_eq_one fun w _ => rfl).symm
    exact map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E)
  · refine Eq.trans ?_ (map_prod (ideleAt E u) _ _).symm
    change GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap F E u
        (Neutral.B1.finiteSingle F v (algebraMap F _ (a : F)) (u.under (𝓞 F))) =
      ∏ w ∈ aboveF (L := E) F v, Neutral.B1.finiteSingle E w (algebraMap E _ (algebraMap F E a)) u
    by_cases h : u.under (𝓞 F) = v
    · have hu : u ∈ aboveF (L := E) F v := by simp [aboveF, h]
      rw [Finset.prod_eq_single_of_mem u hu fun w _ hw => GlobalTheory.LFun.finSingle_ne (Ne.symm hw) _,
        GlobalTheory.LFun.finSingle_self]
      subst h
      rw [GlobalTheory.LFun.finSingle_self, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_coe]
    · rw [GlobalTheory.LFun.finSingle_ne h, map_one]
      refine (Finset.prod_eq_one fun w hw => GlobalTheory.LFun.finSingle_ne ?_ _).symm
      rintro rfl
      exact h (by simpa [aboveF] using hw)

end Comp

end GlobalTheory.PolChar

namespace GlobalTheory.PolChar

open Formalism.L2.Host

theorem resReal_val_eq_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ν : Formalism.L2.Host.HChar E)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))),
    (∀ w ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v,
      ν.UnrAt w ∧ w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1) →
    (GlobalTheory.PolChar.resReal ν).val v = ∏ w ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v, ν.val w := by
  intro E _ _ _ ν v hv
  have key : ∀ w ∈ aboveF (L := E) (maximalRealSubfield E) v,
      ν.loc w (atFin w (upF (maximalRealSubfield E) (unif v))) = ν.val w := by
    intro w hw
    obtain ⟨hunr, he⟩ := hv w hw
    refine HChar.val_eq ν hunr _ ?_
    have hu : w.under (𝓞 (maximalRealSubfield E)) = v := by simpa [aboveF] using hw
    have h1 := unif_spec v
    unfold IsUnifAt at h1 ⊢
    change Valued.v (((algebraMap (maximalRealSubfield E) E ((unif v : (maximalRealSubfield E)ˣ) :
      maximalRealSubfield E)) : E) : w.adicCompletion E) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', GlobalTheory.LFun.valuation_up hu, he, pow_one]
    change Valued.v (((unif v : (maximalRealSubfield E)ˣ) : maximalRealSubfield E) :
      v.adicCompletion (maximalRealSubfield E)) = _ at h1
    rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
  show (resReal ν).1 (Neutral.B1.localIdele _ v (atFin v (unif v))) = _
  rw [resReal_apply, ideleMap_localIdele_atFin, map_prod]
  exact Finset.prod_congr rfl key

end GlobalTheory.PolChar
end
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

theorem _root_.GlobalTheory.T.tendsto_signedLatticeSum_product_sub_factors : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] (e₁ π₁ : ι₁ → B₁.A) (e₂ π₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (S₂ : Finset ι₂) (a : K.O), B₁.LieReg → B₂.LieReg → (B₁.P * B₂.P).Separable → K.Small a → IsFrame B₁ e₁ π₁ S₁ → IsFrame B₂ e₂ π₂ S₂ → Tendsto (fun k : ℕ => (((HH (B₁.prod B₂) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) 1 - (-(K.q : ℚ)) ^ val K.O (resultant B₁.P B₂.P) * (HH B₁ π₁ S₁ ∅ (algebraMap K.O B₁.A a ^ (2 * k)) 1 * HH B₂ π₂ ∅ S₂ (algebraMap K.O B₂.A a ^ (2 * k)) 1) : ℚ) : ℝ) / ((B₁.rho (algebraMap K.O B₁.A a ^ k) : ℝ) * (B₂.rho (algebraMap K.O B₂.A a ^ k) : ℝ)))) atTop (𝓝 0) := by
  first | exact @GlobalTheory.UnitLemma.Desc.hh_prod_tendsto | exact GlobalTheory.UnitLemma.Desc.hh_prod_tendsto | (intros; apply GlobalTheory.UnitLemma.Desc.hh_prod_tendsto <;> assumption)
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

theorem _root_.GlobalTheory.T.signedInvolutionStableLatticeSum_eq_alternating_sum : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] [DecidableEq ι] (e π : ι → B.A) (S : Finset ι), B.LieReg → IsFrame B e π S → ∀ I ⊆ S, ∀ u : B.A, IsUnit u → HH B π I (S \ I) u 1 = ∑ J ∈ S.powerset, (-1 : ℚ) ^ (J ∩ I).card * B.GG ((∏ j ∈ J, π j) * u) := by
  first | exact @GlobalTheory.UnitLemma.Desc.HH_eq_alternating_GG | exact GlobalTheory.UnitLemma.Desc.HH_eq_alternating_GG | (intros; apply GlobalTheory.UnitLemma.Desc.HH_eq_alternating_GG <;> assumption)
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

theorem _root_.GlobalTheory.T.tendsto_signedLatticeSum_sub_normCharacter_mul : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] [DecidableEq ι] (e π : ι → B.A) (S : Finset ι) (a : K.O), B.LieReg → K.Small a → IsFrame B e π S → ∀ I ⊆ S, ∀ x : B.A, B.Plus x → Tendsto (fun k : ℕ => (((HH B π I (S \ I) (x * algebraMap K.O B.A a ^ (2 * k)) 1 - chi B e I x * HH B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 : ℚ) : ℝ) / (B.rho (algebraMap K.O B.A a ^ k) : ℝ))) atTop (𝓝 0) := by
  first | exact @GlobalTheory.UnitLemma.Desc.HH_sub_chi_mul_HH_negligible | exact GlobalTheory.UnitLemma.Desc.HH_sub_chi_mul_HH_negligible | (intros; apply GlobalTheory.UnitLemma.Desc.HH_sub_chi_mul_HH_negligible <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

theorem _root_.GlobalTheory.T.adelicDiagonalUniformizer_commute_of_one_off : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (l : GlobalTheory.CellDec.abelian₂ E n S) (p : GA E n),
    (∀ w ∉ S, Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p = 1) →
    p * GlobalTheory.CellDec.tl n ϖ l.1 = GlobalTheory.CellDec.tl n ϖ l.1 * p := by
  first | exact @GlobalTheory.CellDec.TlComm.tl_commute_of_one_off | exact GlobalTheory.CellDec.TlComm.tl_commute_of_one_off | (intros; apply GlobalTheory.CellDec.TlComm.tl_commute_of_one_off <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.jointHarmonic_highestWeight_multiplicity_one : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (lam : D.what₂.Tau → Fin n → ℂ) (P P' : PolF D m n), P ≠ 0 → GlobalTheory.LowestKType.IsHarm w P → GlobalTheory.LowestKType.IsHarm w P' → GlobalTheory.LowestKType.IsNHw w lam P → GlobalTheory.LowestKType.IsNHw w lam P' → GlobalTheory.LowestKType.IsKHw w P → GlobalTheory.LowestKType.IsKHw w P' → ∃ c : ℂ, P' = c • P := by
  first | exact @GlobalTheory.HarmLine.joint_line | exact GlobalTheory.HarmLine.joint_line | (intros; apply GlobalTheory.HarmLine.joint_line <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

theorem _root_.GlobalTheory.T.localHeisenbergSpan_preserves_type_relations : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.thP_ωP → ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∈ Sb → ∀ (ε : AF D.host.F) (a : AE D), IsPlaceIdem D v ε → a + cA D a = algebraMap (AF D.host.F) (AE D) ε → ∀ f : WO (Vc D i) (Wc D i) → ℂ, TypeIn R i t Sb f → CleanIn R i t Sb f → LikeOff R i t Sb f → ∀ f' ∈ locSpan R.ψ (Vc D i) (Wc D i) a f, TypeIn R i t (dropPl Sb v) f' ∧ CleanIn R i t (dropPl Sb v) f' ∧ LikeOff R i t Sb f' := by
  first | exact @GlobalTheory.DownLift.PlaceTranslate.locSpan_pres | exact GlobalTheory.DownLift.PlaceTranslate.locSpan_pres | (intros; apply GlobalTheory.DownLift.PlaceTranslate.locSpan_pres <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.TraceConjugationCover

theorem tup_mul_tup {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {a m : ℕ}
    (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (g h : Γ) : tup ρs g * tup ρs h = tup ρs (g * h) := by
  funext k
  simp [tup, map_mul, Units.val_mul]

theorem tup_mul_smul {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {a m : ℕ}
    (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (g : Γ) (c : ℤ_[l]) (x : Fin m → Matrix (Fin a) (Fin a) (Om l)) :
    tup ρs g * (c • x) = c • (tup ρs g * x) := by
  rw [← zOm_smul, ← zOm_smul]
  funext k
  simp [Pi.mul_apply, Pi.smul_apply, Matrix.mul_smul]

theorem stabE : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (M : ℕ), (∀ k g, ∀ x ∈ t k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x = ∑ y ∈ t k, zOm l (c' y) • y) → (∀ g, ∀ x ∈ GlobalTheory.TraceConjugationCover.latL t M, GlobalTheory.TraceConjugationCover.tup ρs g * x ∈ GlobalTheory.TraceConjugationCover.latL t M) ∧ ∀ g, ∀ x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M, GlobalTheory.TraceConjugationCover.tup ρs g * x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M := by
  intro l _ Γ _ a m ρs t M hc
  have hL : ∀ g, ∀ x ∈ latL t M, tup ρs g * x ∈ latL t M := by
    intro g x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      obtain ⟨y, hy, rfl⟩ := hk
      obtain ⟨c', hc'⟩ := hc k g y hy
      have e : tup ρs g * Pi.single k ((l : Om l) ^ M • y)
          = ∑ z ∈ t k, c' z • (Pi.single k ((l : Om l) ^ M • z) : Fin m → Matrix (Fin a) (Fin a) (Om l)) := by
        have e1 : tup ρs g * Pi.single k ((l : Om l) ^ M • y)
            = Pi.single k ((l : Om l) ^ M • (((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * y)) := by
          funext j
          by_cases hj : j = k
          · subst hj; simp [tup, Matrix.mul_smul]
          · simp [Pi.single_apply, hj]
        rw [e1, hc', Finset.smul_sum]
        funext j
        rw [Finset.sum_apply]
        by_cases hj : j = k
        · subst hj
          simp only [Pi.single_eq_same, Pi.smul_apply]
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [smul_comm ((l : Om l) ^ M) (zOm l (c' z)) z, zOm_smul]
        · simp [Pi.single_apply, hj]
      rw [e]
      refine Submodule.sum_mem _ fun z hz => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      exact Set.mem_iUnion.mpr ⟨k, z, hz, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [tup_mul_smul]; exact Submodule.smul_mem _ _ hx
  refine ⟨hL, fun g x hx => ?_⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  clear hx
  rw [mul_add]
  refine Submodule.add_mem _ ?_ (Submodule.mem_sup_right (hL g z hz))
  refine Submodule.mem_sup_left ?_
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    rw [tup_mul_tup]; exact Submodule.subset_span ⟨_, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [tup_mul_smul]; exact Submodule.smul_mem _ _ hx

end GlobalTheory.TraceConjugationCover
end
end

section

open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.greenCuspidalCharsByRegularChars_proof : GlobalTheory.Published.GreenRegularCharacters := by
  first | exact @GlobalTheory.greenRegularCharacters_holds | exact GlobalTheory.greenRegularCharacters_holds | (intros; apply GlobalTheory.greenRegularCharacters_holds <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem _root_.GlobalTheory.T.exists_evaluation_convergent_series_Bcris : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β → ∃ J, IsEval I β J := by
  first | exact @GlobalTheory.HWL.BanachEval.exists_eval | exact GlobalTheory.HWL.BanachEval.exists_eval | (intros; apply GlobalTheory.HWL.BanachEval.exists_eval <;> assumption)
end
