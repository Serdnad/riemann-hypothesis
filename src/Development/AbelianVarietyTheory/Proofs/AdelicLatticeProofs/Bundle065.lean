module

import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasFiniteAdelicDoubleCosetsOfBlockDiagPartImage
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle009
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle167
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatVacFull

variable {D : D7}

theorem exists_nat_integral {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ n : ℕ, 0 < n ∧ ∃ d : 𝓞 E, (d : E) = n * c := by
  apply GlobalTheory.NatMulMemRingOfIntegers.exists_nat_mul_mem_ringOfIntegers <;> assumption

theorem AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  refine mul_ne_zero ?_ (inv_ne_zero ?_)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    exact D.host.ccK_ne_bot
      ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective _ _)).1 h)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    have h1 := D.host.𝔟_spec.1
    rw [h, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1

section
variable (S T : HSp D) (s x y : Fin S.rank → D.host.E) (t u v : Fin T.rank → D.host.E) (a c : D.host.E)

theorem genMap_one (ha0 : a ≠ 0) : genMap S T 1 s t = a⁻¹ • genMap S T a s t := by
  ext i j
  simp only [genMap, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ ha0]

theorem genMap_zero_right : genMap S T 1 s 0 = 0 := by
  ext i j
  simp only [genMap, Matrix.of_apply, Pi.zero_apply, Matrix.zero_apply, mul_zero, zero_mul]

theorem genMap_add_right : genMap S T 1 s (u + v) = genMap S T 1 s u + genMap S T 1 s v := by
  ext i j
  simp only [genMap, Matrix.of_apply, Pi.add_apply, Matrix.add_apply, mul_add, add_mul]

theorem genMap_smul_right : genMap S T 1 s (c • u) = c • genMap S T 1 s u := by
  ext i j
  simp only [genMap, Matrix.of_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, one_mul, mul_assoc]

theorem genMap_zero_left : genMap S T 1 0 t = 0 := by
  ext i j
  simp only [genMap, Matrix.of_apply, Pi.zero_apply, Matrix.zero_apply, star_zero, mul_zero, zero_mul,
    Finset.sum_const_zero]

theorem genMap_add_left : genMap S T 1 (x + y) t = genMap S T 1 x t + genMap S T 1 y t := by
  ext i j
  simp only [genMap, Matrix.of_apply, Pi.add_apply, Matrix.add_apply, star_add, mul_add, add_mul,
    Finset.sum_add_distrib]

theorem genMap_smul_left : genMap S T 1 (c • x) t = star c • genMap S T 1 x t := by
  refine Matrix.ext fun i j => ?_
  simp only [genMap, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, star_mul',
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

end

def sat (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) :
    Submodule D.host.E (Matrix (Fin T.rank) (Fin S.rank) D.host.E) where
  carrier := {M | ∃ N : ℕ, 0 < N ∧ N • M ∈ latRat S T LS LT}
  zero_mem' := ⟨1, one_pos, by simp⟩
  add_mem' := by
    rintro x y ⟨n, hn, hx⟩ ⟨m, hm, hy⟩
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hx m
    · rw [mul_smul]; exact nsmul_mem hy n
  smul_mem' := by
    rintro c x ⟨n, hn, hx⟩
    obtain ⟨m, hm, d, hd⟩ := exists_nat_integral c
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    have h := smul_mem_latRat d hx
    have e : (m * n) • c • x = (d : D.host.E) • n • x := by
      rw [hd]; ext i j; simp; ring
    rw [e]; exact h

theorem genMap_mem_sat (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hS : Submodule.IsFullLattice D.host.E ΛS)
    (hT : Submodule.IsFullLattice D.host.E ΛT) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    genMap S T 1 s t ∈ sat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) := by
  obtain ⟨a, ha0, ha⟩ : ∃ a : D.host.E, a ≠ 0 ∧ a ∈ D.host.AA := by
    by_contra h
    push_neg at h
    apply AA_ne_zero D
    rw [FractionalIdeal.eq_zero_iff]
    intro x hx
    by_contra hx0
    exact h x hx0 hx
  have hs : s ∈ Submodule.span D.host.E (ΛS : Set (Fin S.rank → D.host.E)) := by
    rw [Submodule.IsFullLattice.span_eq_top (self := hS)]; trivial
  have ht : t ∈ Submodule.span D.host.E (ΛT : Set (Fin T.rank → D.host.E)) := by
    rw [Submodule.IsFullLattice.span_eq_top (self := hT)]; trivial
  induction hs using Submodule.span_induction with
  | mem s hs =>
    induction ht using Submodule.span_induction with
    | mem t ht =>
      rw [genMap_one S T s t a ha0]
      refine Submodule.smul_mem _ _ ⟨1, one_pos, ?_⟩
      rw [one_smul]
      exact AddSubgroup.subset_closure ⟨a, ha, s, hs, t, ht, rfl⟩
    | zero => rw [genMap_zero_right]; exact zero_mem _
    | add x y _ _ hx hy => rw [genMap_add_right]; exact add_mem hx hy
    | smul c x _ hx => rw [genMap_smul_right]; exact Submodule.smul_mem _ _ hx
  | zero => rw [genMap_zero_left]; exact zero_mem _
  | add x y _ _ hx hy => rw [genMap_add_left]; exact add_mem hx hy
  | smul c x _ hx => rw [genMap_smul_left]; exact Submodule.smul_mem _ _ hx

theorem latRat_full (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hS : Submodule.IsFullLattice D.host.E ΛS)
    (hT : Submodule.IsFullLattice D.host.E ΛT) (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ∃ N : ℕ, 0 < N ∧
      N • M ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) := by
  change M ∈ sat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
  have e : M = ∑ i, genMap S T 1 (fun k => star ((M * S.gram⁻¹) i k)) (Pi.single i 1) := by
    ext i j
    have h : ∀ l, ∑ k, (M * S.gram⁻¹) l k * S.gram k j = M l j := by
      intro l
      rw [← Matrix.mul_apply, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (gram_det_isUnit S),
        Matrix.mul_one]
    simp only [Matrix.sum_apply, genMap, Matrix.of_apply, star_star, h, one_mul]
    simp [Pi.single_apply]
  rw [e]
  exact Submodule.sum_mem _ fun i _ => genMap_mem_sat S T ΛS ΛT hS hT _ _

end GlobalTheory.LatVacFull

end
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.classFiniteness_completelyReducible : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), IsQGroup Γ → SS Γ → AdelicPair R R₀ → CF Γ R R₀ := by
  first | exact @GlobalTheory.ClassFin.cf_of_ss | exact GlobalTheory.ClassFin.cf_of_ss | (intros; apply GlobalTheory.ClassFin.cf_of_ss <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.hasFiniteAdelicDoubleCosets_of_blockDiagPart_image : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), IsQGroup Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → AdelicPair R R₀ → CF (blk e '' Γ) R R₀ → CF Γ R R₀ := by
  first | exact @GlobalTheory.ClassFin.cf_of_cf_blk_image | exact GlobalTheory.ClassFin.cf_of_cf_blk_image | (intros; apply GlobalTheory.ClassFin.cf_of_cf_blk_image <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.exists_places_with_pth_roots_and_separating_units : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (ζ : F) (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → δ ∈ sUnits F S → (∀ r : F, r ^ p ≠ (δ : F)) → ∃ T : Finset (HeightOneSpectrum (𝓞 F)), Disjoint S T ∧ T.card + 1 = S.card + Fintype.card (InfinitePlace F) ∧ (∀ v ∈ T, ∃ r : v.adicCompletion F, r ^ p = algebraMap F (v.adicCompletion F) (δ : F)) ∧ ∀ v ∈ T, ∃ u ∈ sUnits F S, u ∉ powSub p (algebraMap F (v.adicCompletion F)) ∧ ∀ v' ∈ T, v' ≠ v → u ∈ powSub p (algebraMap F (v'.adicCompletion F)) := by
  first | exact @GlobalTheory.CNorm.exists_auxiliary_places_prime | exact GlobalTheory.CNorm.exists_auxiliary_places_prime | (intros; apply GlobalTheory.CNorm.exists_auxiliary_places_prime <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatFinMod

open GlobalTheory.LatVac

theorem exists_finite_mod {W : Type} [AddCommGroup W] {G : Set W} (hG : G.Finite) {k : ℕ} (hk : 0 < k) :
    ∃ R : Set W, R.Finite ∧ ∀ x ∈ Submodule.span ℤ G, ∃ r ∈ R, ∃ u ∈ Submodule.span ℤ G, x = r + k • u := by
  induction G, hG using Set.Finite.induction_on with
  | empty => exact ⟨{0}, Set.finite_singleton _, fun x hx => ⟨0, rfl, 0, zero_mem _, by simpa using hx⟩⟩
  | @insert g G _ _ ih =>
    obtain ⟨R, hR, h⟩ := ih
    refine ⟨Set.image2 (fun (j : ℤ) r => j • g + r) (Set.Ico 0 k) R, (Set.finite_Ico _ _).image2 _ hR,
      fun x hx => ?_⟩
    obtain ⟨c, y, hy, rfl⟩ := Submodule.mem_span_insert.1 hx
    obtain ⟨r, hr, u, hu, rfl⟩ := h y hy
    have hk' : (0 : ℤ) < k := by exact_mod_cast hk
    refine ⟨_, ⟨c % k, ⟨Int.emod_nonneg _ hk'.ne', Int.emod_lt_of_pos _ hk'⟩, r, hr, rfl⟩,
      (c / k) • g + u, Submodule.mem_span_insert.2 ⟨_, u, hu, rfl⟩, ?_⟩
    conv_lhs => rw [← Int.emod_add_mul_ediv c k]
    simp only [add_smul, mul_smul, smul_add, natCast_zsmul]
    abel

theorem exists_int_gen {E M : Type} [Field E] [NumberField E] [AddCommGroup M] [Module (𝓞 E) M]
    (N : Submodule (𝓞 E) M) (hN : N.FG) :
    ∃ A : Set M, A.Finite ∧ A ⊆ N ∧ ∀ x ∈ N, x ∈ Submodule.span ℤ A := by
  have h1 : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 hN
  have h2 : Module.Finite ℤ N := Module.Finite.trans (𝓞 E) N
  obtain ⟨s, hs⟩ := h2.fg_top
  refine ⟨Subtype.val '' (s : Set N), s.finite_toSet.image _, ?_, fun x hx => ?_⟩
  · rintro _ ⟨y, -, rfl⟩; exact y.2
  · have : (⟨x, hx⟩ : N) ∈ Submodule.span ℤ (s : Set N) := by rw [hs]; trivial
    exact Submodule.apply_mem_span_image_of_mem_span (N.subtype.toAddMonoidHom.toIntLinearMap) this

theorem triadd_mem_span {X Y Z W : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [AddCommGroup W]
    (f : X → Y → Z → W) (h1 : ∀ a a' s t, f (a + a') s t = f a s t + f a' s t)
    (h2 : ∀ a s s' t, f a (s + s') t = f a s t + f a s' t) (h3 : ∀ a s t t', f a s (t + t') = f a s t + f a s t')
    {A : Set X} {B : Set Y} {C : Set Z} {a s t} (ha : a ∈ Submodule.span ℤ A) (hs : s ∈ Submodule.span ℤ B)
    (ht : t ∈ Submodule.span ℤ C) :
    f a s t ∈ Submodule.span ℤ ((fun p : X × Y × Z => f p.1 p.2.1 p.2.2) '' (A ×ˢ B ×ˢ C)) := by
  have gen : ∀ {U : Type} [AddCommGroup U] (g : U → W), (∀ u u', g (u + u') = g u + g u') →
      ∀ (N : Submodule ℤ W) (V : Set U), (∀ u ∈ V, g u ∈ N) → ∀ u ∈ Submodule.span ℤ V, g u ∈ N := by
    intro U _ g hg N V hV u hu
    have : Submodule.span ℤ V ≤ N.comap (AddMonoidHom.mk' g hg).toIntLinearMap := Submodule.span_le.2 hV
    exact this hu
  refine gen (fun a => f a s t) (fun a a' => h1 a a' s t) _ A (fun a ha => ?_) a ha
  refine gen (fun s => f a s t) (fun s s' => h2 a s s' t) _ B (fun s hs => ?_) s hs
  refine gen (fun t => f a s t) (h3 a s) _ C (fun t ht => ?_) t ht
  exact Submodule.subset_span ⟨(a, s, t), ⟨ha, hs, ht⟩, rfl⟩

theorem star_sum_add {E : Type} [CommRing E] [StarRing E] {n : ℕ} (c : E) (s s' g : Fin n → E) :
    c * ∑ k, star ((s + s') k) * g k = c * ∑ k, star (s k) * g k + c * ∑ k, star (s' k) * g k := by
  simp [mul_add, add_mul, Finset.sum_add_distrib]

theorem pair_tmul_split {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (ε β : Af F) (x : F) (k : ℕ) (a t g : E) :
    pairA F 0 (ε * (algebraMap F _ x + k • β)) ⊗ₜ[F] (a * t * g) =
      pairA F 0 ε ⊗ₜ[F] (algebraMap F E x * a * t * g) + k • (pairA F 0 (ε * β) ⊗ₜ[F] (a * t * g)) := by
  have hp : pairA F 0 (ε * (algebraMap F _ x + k • β)) = x • pairA F 0 ε + k • pairA F 0 (ε * β) := by
    refine Prod.ext ?_ ?_
    · change (0 : Ainf F) = x • 0 + k • 0
      simp
    · change ε * (algebraMap F _ x + k • β) = x • ε + k • (ε * β)
      rw [mul_add, mul_smul_comm, Algebra.smul_def x, mul_comm ε]
  rw [hp, TensorProduct.add_tmul, TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def x,
    ← mul_assoc, ← mul_assoc]

theorem add_nsmul_residue_add {W : Type} [AddCommGroup W] (k : ℕ) (y u y' u' : W) :
    y + k • u + (y' + k • u') = y + y' + k • (u + u') := by rw [smul_add]; abel

theorem neg_nsmul_residue {W : Type} [AddCommGroup W] (k : ℕ) (y u : W) : -(y + k • u) = -y + k • -u := by
  rw [smul_neg]; abel

theorem add_nsmul_residue_assoc {W : Type} [AddCommGroup W] (k : ℕ) (r u' u : W) :
    r + k • u' + k • u = r + k • (u' + u) := by rw [smul_add, add_assoc]

variable {D : D7}

theorem genMap_mem_span (S T : HSp D) {A : Set D.host.E} {B : Set (Fin S.rank → D.host.E)}
    {C : Set (Fin T.rank → D.host.E)} {a s t} (ha : a ∈ Submodule.span ℤ A) (hs : s ∈ Submodule.span ℤ B)
    (ht : t ∈ Submodule.span ℤ C) :
    genMap S T a s t ∈ Submodule.span ℤ ((fun p : _ × _ × _ => genMap S T p.1 p.2.1 p.2.2) '' (A ×ˢ B ×ˢ C)) := by
  refine triadd_mem_span (genMap S T) (fun a a' s t => ?_) (fun a s s' t => ?_) (fun a s t t' => ?_) ha hs ht
  · exact Matrix.ext fun i j => (congrArg (· * _) (add_mul a a' (t i))).trans (add_mul _ _ _)
  · exact Matrix.ext fun i j => star_sum_add (a * t i) s s' fun k => S.gram k j
  · exact Matrix.ext fun i j => (congrArg (· * _) (mul_add a (t i) (t' i))).trans (add_mul _ _ _)


open Classical in
def idemAt (F : Type) [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F) → Prop) : Af F :=
  ⟨fun v => if P v then 1 else 0, Filter.Eventually.of_forall fun v => by
    by_cases h : P v
    · simp only [h, if_true]; exact one_mem _
    · simp only [h, if_false]; exact zero_mem _⟩

open Classical in
theorem evalV_idemAt (F : Type) [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F) → Prop)
    (v : HeightOneSpectrum (𝓞 F)) : evalV F v (idemAt F P) = if P v then 1 else 0 := rfl

theorem latO_finite_mod : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), ΛS.FG → ΛT.FG → ∀ (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (k : ℕ), 0 < k → ∃ R : Set (WO S T), R.Finite ∧ ∀ t ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) P, ∃ r ∈ R, ∃ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) P, t = r + k • u := by
  intro D S T ΛS ΛT hS hT P k hk
  obtain ⟨A, hA, hA1, hA2⟩ := exists_int_gen (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)
    (FractionalIdeal.fg_of_isNoetherianRing le_rfl _)
  obtain ⟨B, hB, hB1, hB2⟩ := exists_int_gen ΛS hS
  obtain ⟨C, hC, hC1, hC2⟩ := exists_int_gen ΛT hT
  let ε := idemAt D.host.F P
  have hε : ε ∈ intAf D.host.F := by
    intro v
    rw [evalV_idemAt]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hε0 : ∀ v, ¬ P v → evalV D.host.F v ε = 0 := fun v hv => by rw [evalV_idemAt, if_neg hv]
  let φ : Matrix (Fin T.rank) (Fin S.rank) D.host.E →ₗ[ℤ] WO S T :=
    (AddMonoidHom.mk' (finTens ε) (finTens_add ε)).toIntLinearMap
  let G := φ '' ((fun p : _ × _ × _ => genMap S T p.1 p.2.1 p.2.2) '' (A ×ˢ B ×ˢ C))
  have hG : G.Finite := ((hA.prod (hB.prod hC)).image _).image _
  set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) P
  have hGΛ : ∀ x ∈ Submodule.span ℤ G, x ∈ Λ := by
    have : Submodule.span ℤ G ≤ Λ.toIntSubmodule := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨_, ⟨⟨a, s, t⟩, ⟨ha, hs, ht⟩, rfl⟩, rfl⟩
      exact AddSubgroup.subset_closure ⟨ε, hε, hε0, a, hA1 ha, s, hB1 hs, t, hC1 ht, rfl⟩
    exact fun x hx => this hx
  have key : ∀ w ∈ Λ, ∃ y ∈ Submodule.span ℤ G, ∃ u ∈ Λ, w = y + k • u := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, h0, a, ha, s, hs, t, ht, rfl⟩ := hw
      obtain ⟨x, β, hβ, hx⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat D.host.F k hk).2 α hα
      have e : α = ε * α := by
        refine RestrictedProduct.ext _ _ fun v => ?_
        change evalV D.host.F v α = evalV D.host.F v (ε * α)
        rw [map_mul, evalV_idemAt]
        split_ifs with hv
        · rw [one_mul]
        · rw [h0 v hv, mul_zero]
      have hxa : algebraMap D.host.F D.host.E x * a ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) :=
        Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)
          (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) ha
      refine ⟨φ (genMap S T (algebraMap D.host.F D.host.E x * a) s t),
        Submodule.apply_mem_span_image_of_mem_span φ
          (genMap_mem_span S T (hA2 _ hxa) (hB2 _ hs) (hC2 _ ht)),
        finTens (ε * β) (genMap S T a s t),
        AddSubgroup.subset_closure ⟨ε * β, fun v => ?_, fun v hv => ?_, a, ha, s, hs, t, ht, rfl⟩, ?_⟩
      · rw [map_mul]; exact mul_mem (hε v) (hβ v)
      · rw [map_mul, hε0 v hv, zero_mul]
      · rw [e, hx]
        exact Matrix.ext fun i j => pair_tmul_split ε β _ k a (t i) _
    | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
    | add x x' _ _ h h' =>
      obtain ⟨y, hy, u, hu, rfl⟩ := h
      obtain ⟨y', hy', u', hu', rfl⟩ := h'
      exact ⟨y + y', add_mem hy hy', u + u', add_mem hu hu', add_nsmul_residue_add k y u y' u'⟩
    | neg x _ h =>
      obtain ⟨y, hy, u, hu, rfl⟩ := h
      exact ⟨-y, neg_mem hy, -u, neg_mem hu, neg_nsmul_residue k y u⟩
  obtain ⟨R, hR, h⟩ := exists_finite_mod hG hk
  refine ⟨R, hR, fun w hw => ?_⟩
  obtain ⟨y, hy, u, hu, rfl⟩ := key w hw
  obtain ⟨r, hr, u', hu', rfl⟩ := h y hy
  exact ⟨r, hr, u' + u, add_mem (hGΛ _ hu') hu, add_nsmul_residue_assoc k r u' u⟩

end GlobalTheory.LatFinMod

end
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

theorem tsum_ideal_mul_absNorm_cpow_eq_exp_tsum :
    ∀ (K : Type) [Field K] [NumberField K] (X : Ideal (𝓞 K) → ℂ), X ⊥ = 0 → X ⊤ = 1 → (∀ I J, X (I * J) = X I * X J) → (∀ I, ‖X I‖ ≤ 1) → ∀ s : ℂ, 1 < s.re → ∑' I, X I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s) = Complex.exp (∑' P : HeightOneSpectrum (𝓞 K), -Complex.log (1 - X P.asIdeal * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))) := by
  intro K _ _ X hbot htop hmul hle s hs
  have hnorm : ∀ P : HeightOneSpectrum (𝓞 K), 1 < Ideal.absNorm P.asIdeal := by
    intro P
    have h0 : Ideal.absNorm P.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.ne_bot
    have h1 : Ideal.absNorm P.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact P.isPrime.ne_top
    omega
  refine GlobalTheory.Mem.tsum_eq_exp_tsum_neg_log_of_primes (fun P : HeightOneSpectrum (𝓞 K) => P.asIdeal)
    (fun P => P.prime) ?_ (fun I => X I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)) ?_ ?_ ?_ ?_ ?_
  ·
    intro P Q h
    rw [Ideal.dvd_iff_le] at h
    exact HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h).symm
  · intro I J
    rw [hmul, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    ring
  · simp [Ideal.one_eq_top, htop]
  · intro I hI hfI
    have hbot' : I ≠ ⊥ := by
      rintro rfl; exact hfI (by simp [hbot])
    have htop' : I ≠ ⊤ := by rwa [← Ideal.one_eq_top]
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I htop'
    have hMbot : M ≠ ⊥ := fun h => hbot' (le_bot_iff.mp (h ▸ hIM))
    exact ⟨⟨M, hM.isPrime, hMbot⟩, (Ideal.dvd_iff_le).mpr hIM⟩
  · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun I => ?_)
      (GlobalTheory.Mem.summable_norm_absNorm_cpow K hs)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hle I)
  · intro P hP
    have hlt : ‖X P.asIdeal * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)‖ < 1 := by
      have hn := hnorm P
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
      have hr : ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s).re < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hn) (by simp; linarith)
      calc ‖X P.asIdeal‖ * ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s).re
          ≤ 1 * ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s).re :=
            mul_le_mul_of_nonneg_right (hle _) (by positivity)
        _ < 1 := by rw [one_mul]; exact hr
    rw [sub_eq_zero] at hP
    rw [← hP, norm_one] at hlt
    exact lt_irrefl _ hlt

end GlobalTheory
end
