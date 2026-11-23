module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Localization.Integer

@[expose] public section

section

namespace GlobalTheory.SimpStatement

open Finset

theorem main {K B W G ι : Type} [Field K] [CommRing B] [IsDomain B] [Algebra K B]
    [AddCommGroup W] [Module B W] [Module K W] [IsScalarTower K B W] [Module.IsTorsionFree B W]
    (a : G → B → B) (σ : G → W →+ W)
    (hσ : ∀ (g : G) (b : B) (w : W), (σ g : W → W) (b • w) = a g b • (σ g : W → W) w)
    (ha : ∀ (b b' : B), b ≠ (0 : B) → (∀ (g : G), b * a g b' = a g b * b') →
      ∃ (c : K), b' = (Algebra.algebraMap K B : K → B) c * b)
    (v : ι → W) (hv : ∀ (g : G) (i : ι), (σ g : W → W) (v i) = v i)
    (s : Finset ι) (hK : LinearIndepOn K v (↑s : Set ι)) :
    LinearIndepOn B v (↑s : Set ι) := by
  classical

  have key : ∀ T : Finset ι, T ⊆ s → ∀ f : ι → B, ∑ i ∈ T, f i • v i = 0 → ∀ i ∈ T, f i = 0 := by
    intro T
    induction T using Finset.strongInduction with
    | H T ih =>
      intro hTs f hf
      by_contra hne
      push_neg at hne
      obtain ⟨i₀, hi₀, hfi₀⟩ := hne

      have hrel : ∀ j ∈ T, ∀ g : G, f i₀ * a g (f j) = a g (f i₀) * f j := by
        intro j hj g
        set f' : ι → B := fun i => f i₀ * a g (f i) - a g (f i₀) * f i with hf'
        have hsum : ∑ i ∈ T, f' i • v i = 0 := by
          have h1 : ∑ i ∈ T, a g (f i) • v i = 0 := by
            have := congrArg (σ g : W → W) hf

            rw [map_sum, map_zero] at this
            rw [← this]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hσ, hv]
          simp only [hf', sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, h1, hf,
            smul_zero, sub_zero]
        have hf'i₀ : f' i₀ = 0 := by simp only [hf']; ring
        have hsum' : ∑ i ∈ T.erase i₀, f' i • v i = 0 := by
          rw [← Finset.add_sum_erase T _ hi₀, hf'i₀, zero_smul, zero_add] at hsum
          exact hsum
        by_cases hj0 : j = i₀
        · subst hj0; ring
        · have := ih (T.erase i₀) (Finset.erase_ssubset hi₀)
            ((Finset.erase_subset _ _).trans hTs) f' hsum' j (Finset.mem_erase.2 ⟨hj0, hj⟩)
          simp only [hf'] at this
          exact sub_eq_zero.1 this
      have hc : ∀ j ∈ T, ∃ c : K, f j = (Algebra.algebraMap K B : K → B) c * f i₀ :=
        fun j hj => ha (f i₀) (f j) hfi₀ (hrel j hj)
      choose! c hc using hc
      have hsumK : ∑ i ∈ T, c i • v i = 0 := by
        have : f i₀ • ∑ i ∈ T, c i • v i = 0 := by
          rw [← hf, Finset.smul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [hc i hi, mul_comm, mul_smul, smul_comm]
          rw [algebraMap_smul]
          exact smul_comm (c i) (f i₀) (v i)
        exact (smul_eq_zero_iff_right hfi₀).1 this
      have hKT : LinearIndepOn K v (↑T : Set ι) := hK.mono (by exact_mod_cast hTs)
      have hci₀ := (linearIndepOn_finset_iff.1 hKT) c hsumK i₀ hi₀
      apply hfi₀
      rw [hc i₀ hi₀, hci₀, map_zero, zero_mul]
  exact linearIndepOn_finset_iff.2 (key s subset_rfl)

end GlobalTheory.SimpStatement
end

section

namespace GlobalTheory.PowerBound

theorem pow_le {A : Type} [CommRing A] (a d : A) (n : ℕ) :
    (Ideal.span {a} ⊔ Ideal.span {d}) ^ (n + 1) ≤
      Ideal.span {a ^ (n + 1)} ⊔ Ideal.span {d} * (Ideal.span {a} ⊔ Ideal.span {d}) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    set I := Ideal.span {a} ⊔ Ideal.span {d} with hI
    have haI : a ^ (n + 1) ∈ I ^ (n + 1) :=
      Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a)) _
    calc I ^ (n + 1 + 1) = I * I ^ (n + 1) := pow_succ' I (n + 1)
      _ ≤ I * (Ideal.span {a ^ (n + 1)} ⊔ Ideal.span {d} * I ^ n) := Ideal.mul_mono_right ih
      _ = I * Ideal.span {a ^ (n + 1)} ⊔ Ideal.span {d} * (I * I ^ n) := by
          rw [Ideal.mul_sup, mul_left_comm]
      _ ≤ Ideal.span {a ^ (n + 1 + 1)} ⊔ Ideal.span {d} * I ^ (n + 1) := by
          apply sup_le
          · rw [hI, Ideal.sup_mul, Ideal.span_singleton_mul_span_singleton, ← pow_succ']
            apply sup_le_sup_left
            exact Ideal.mul_mono_right ((Ideal.span_singleton_le_iff_mem _).2 haI)
          · rw [← pow_succ']
            exact le_sup_right

theorem main : ∀ {A : Type} [inst : CommRing A] (a d : A) (n : ℕ) {x : A},
    x ∈ (Ideal.span {a} ⊔ Ideal.span {d}) ^ (n + (1 : ℕ)) →
      ∃ (u : A), ∃ w ∈ (Ideal.span {a} ⊔ Ideal.span {d}) ^ n, x = a ^ (n + (1 : ℕ)) * u + d * w := by
  intro A _ a d n x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (pow_le a d n hx)
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨w, hw, rfl⟩ := Ideal.mem_span_singleton_mul.1 hz
  exact ⟨u, w, hw, by ring⟩

end GlobalTheory.PowerBound
end

section

namespace GlobalTheory

theorem mem_ideal_smul_top_pi_fin_iff {Λ : Type} [CommRing Λ] (J : Ideal Λ) {a : ℕ}
    (y : Fin a → Λ) : y ∈ J • (⊤ : Submodule Λ (Fin a → Λ)) ↔ ∀ i, y i ∈ J := by
  constructor
  · intro h
    refine Submodule.smul_induction_on h ?_ ?_
    · intro r hr m _ i
      exact J.mul_mem_right _ hr
    · intro x z hx hz i
      exact J.add_mem (hx i) (hz i)
  · intro h
    rw [pi_eq_sum_univ y]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

theorem chain_le_iInf_sup_pow_smul_top :
    ∀ (Λ : Type) [CommRing Λ] (I : Ideal Λ) [IsPrecomplete I Λ] (a : ℕ)
      (N : ℕ → Submodule Λ (Fin a → Λ)),
  (∀ n, N (n + 1) ≤ N n) → (∀ n, I ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ)) ≤ N n) →
  (∀ n, N n ≤ N (n + 1) ⊔ I ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ))) →
  ∀ n, N n ≤ (⨅ k, N k) ⊔ I ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ)) := by
  intro Λ _ I hI a N hanti hpow hstep n x hx
  have hA : Antitone N := antitone_nat_of_succ_le hanti
  have step : ∀ m (y : N m), ∃ z : N (m + 1),
      (y : Fin a → Λ) - z ∈ I ^ (m + 1) • (⊤ : Submodule Λ (Fin a → Λ)) := by
    intro m y
    obtain ⟨z, hz, w, hw, h⟩ := Submodule.mem_sup.1 (hstep m y.2)
    refine ⟨⟨z, hz⟩, ?_⟩
    have : (y : Fin a → Λ) - z = w := by rw [← h]; abel
    simpa [this] using hw
  choose f hf using step
  let u : ∀ j : ℕ, N (n + j) := fun j =>
    Nat.rec (motive := fun j => N (n + j)) ⟨x, hx⟩ (fun j y => f (n + j) y) j
  have hu0 : (u 0 : Fin a → Λ) = x := rfl
  have hus : ∀ j, (u j : Fin a → Λ) - u (j + 1) ∈
      I ^ (n + j + 1) • (⊤ : Submodule Λ (Fin a → Λ)) := fun j => hf (n + j) (u j)
  have htel : ∀ j j', j ≤ j' → ∀ i, (u j : Fin a → Λ) i - (u j' : Fin a → Λ) i ∈
      I ^ (n + j + 1) := by
    intro j j' hjj i
    induction j', hjj using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      have h1 := (mem_ideal_smul_top_pi_fin_iff _ _).1 (hus k) i
      have h2 : I ^ (n + k + 1) ≤ I ^ (n + j + 1) := Ideal.pow_le_pow_right (by omega)
      have h3 := Ideal.add_mem _ ih (h2 h1)
      simpa using h3
  have hlim : ∀ i, ∃ L : Λ, ∀ j, (u j : Fin a → Λ) i - L ∈ I ^ j := by
    intro i
    obtain ⟨L, hL⟩ := IsPrecomplete.prec hI (f := fun j => (u j : Fin a → Λ) i) (by
      intro m k hmk
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      exact Ideal.pow_le_pow_right (by omega) (htel m k hmk i))
    refine ⟨L, fun j => ?_⟩
    have := hL j
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  choose L hL using hlim
  have hdiff : ∀ j, (u j : Fin a → Λ) - L ∈
      I ^ (n + j + 1) • (⊤ : Submodule Λ (Fin a → Λ)) := by
    intro j
    rw [mem_ideal_smul_top_pi_fin_iff]
    intro i
    have h3 := Ideal.add_mem _ (htel j (n + j + 1) (by omega) i) (hL i (n + j + 1))
    simpa using h3
  have hLmem : L ∈ ⨅ k, N k := by
    rw [Submodule.mem_iInf]
    intro k
    have h1 : (u k : Fin a → Λ) - (u k - L) ∈ N (n + k) :=
      Submodule.sub_mem _ (u k).2 (hpow _ (hdiff k))
    rw [sub_sub_cancel] at h1
    exact hA (by omega) h1
  refine Submodule.mem_sup.2 ⟨L, hLmem, x - L, hdiff 0, by abel⟩

end GlobalTheory
end

section

namespace GlobalTheory.IntegralPi

open Polynomial

theorem isIntegral_pi {O : Type} [CommRing O] {ι : Type} [Finite ι] {R : ι → Type}
    [∀ i, CommRing (R i)] [∀ i, Algebra O (R i)] (x : ∀ i, R i)
    (hx : ∀ i, IsIntegral O (x i)) : IsIntegral O x := by
  classical
  haveI := Fintype.ofFinite ι
  choose p hpm hp using hx
  refine ⟨∏ i, p i, monic_prod_of_monic _ _ (fun i _ => hpm i), ?_⟩
  rw [← aeval_def]
  funext j
  have key : (aeval x (∏ i, p i)) j = aeval (x j) (∏ i, p i) := by
    have := (aeval_algHom_apply (Pi.evalAlgHom O R j) x (∏ i, p i)).symm
    simpa using this
  rw [key, map_prod, Pi.zero_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [aeval_def]; exact hp j)

theorem main : ∀ {O : Type} [inst : CommRing O] {ι : Type} [Finite ι] {R : ι → Type}
    [inst_2 : (i : ι) → CommRing (R i)] [inst_3 : (i : ι) → Algebra O (R i)] (x : (i : ι) → R i),
    (∀ (i : ι), IsIntegral O (x i)) → IsIntegral O x :=
  fun x hx => isIntegral_pi x hx

end GlobalTheory.IntegralPi
end

section

namespace GlobalTheory.GroupAlg.ClassSum

open MonoidAlgebra

variable {G : Type} [Group G] [Fintype G]

noncomputable def classSum [DecidableEq (ConjClasses G)] (C : ConjClasses G) : MonoidAlgebra ℤ G :=
  ∑ h, single h (if ConjClasses.mk h = C then (1 : ℤ) else 0)

theorem coeff_classSum [DecidableEq (ConjClasses G)] (C : ConjClasses G) (y : G) :
    (classSum C).coeff y = if ConjClasses.mk y = C then 1 else 0 := by
  classical
  simp [classSum, coeff_sum, coeff_single, Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem classSum_comm [DecidableEq (ConjClasses G)] (C : ConjClasses G) (a : MonoidAlgebra ℤ G) :
    classSum C * a = a * classSum C := by
  induction a using MonoidAlgebra.induction_on with
  | of k =>
    apply MonoidAlgebra.ext
    ext x
    simp only [MonoidAlgebra.of_apply, coeff_mul_single_apply, coeff_single_mul_apply, coeff_classSum,
      mul_one, one_mul]
    have : ConjClasses.mk (x * k⁻¹) = ConjClasses.mk (k⁻¹ * x) := by
      rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
      exact ⟨k⁻¹, by group⟩
    rw [this]
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

theorem coeff_conj_eq {R : Type} [CommRing R] (z : MonoidAlgebra R G)
    (hz : z ∈ Subalgebra.center R (MonoidAlgebra R G)) {a b : G} (hab : IsConj a b) :
    z.coeff a = z.coeff b := by
  rw [Subalgebra.mem_center_iff] at hz
  obtain ⟨g, rfl⟩ := isConj_iff.mp hab
  have h := congrArg (fun w => w.coeff (g * a)) (hz (single g (1 : R)))
  simp only [coeff_mul_single_apply, coeff_single_mul_apply, one_mul, mul_one, inv_mul_cancel_left] at h
  exact h

theorem mem_span (R G : Type) [CommRing R] [Group G] [Finite G] (z : MonoidAlgebra R G)
    (hz : z ∈ Subalgebra.center R (MonoidAlgebra R G)) :
    z ∈ Submodule.span R ((MonoidAlgebra.mapRingHom G (Int.castRingHom R)) ''
      {c : MonoidAlgebra ℤ G | ∀ a, c * a = a * c}) := by
  classical
  haveI := Fintype.ofFinite G
  haveI : Fintype (ConjClasses G) := Fintype.ofFinite _
  let rep : ConjClasses G → G := fun C => C.exists_rep.choose
  have hrep : ∀ C, ConjClasses.mk (rep C) = C := fun C => C.exists_rep.choose_spec
  have hmap : ∀ (C : ConjClasses G) (x : G),
      (MonoidAlgebra.mapRingHom G (Int.castRingHom R) (classSum C)).coeff x =
        if ConjClasses.mk x = C then 1 else 0 := by
    intro C x

    simp [classSum, map_sum, coeff_sum, coeff_single,
    Finsupp.finsetSum_apply, Finsupp.single_apply, apply_ite (Int.cast : ℤ → R)]
  have hz' : z = ∑ C, z.coeff (rep C) • MonoidAlgebra.mapRingHom G (Int.castRingHom R) (classSum C) := by
    apply MonoidAlgebra.ext
    ext x
    rw [coeff_sum, Finsupp.finsetSum_apply]
    simp only [coeff_smul, Finsupp.smul_apply, hmap, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    refine coeff_conj_eq z hz ?_
    rw [← ConjClasses.mk_eq_mk_iff_isConj, hrep]
  rw [hz']
  refine Submodule.sum_mem _ fun C _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨classSum C, ?_, rfl⟩)
  exact classSum_comm C

end GlobalTheory.GroupAlg.ClassSum

theorem GlobalTheory.GroupAlg.center_mem_span_classSums : ∀ (R G : Type) [CommRing R] [Group G] [Finite G] (z : MonoidAlgebra R G), z ∈ Subalgebra.center R (MonoidAlgebra R G) → z ∈ Submodule.span R ((MonoidAlgebra.mapRingHom G (Int.castRingHom R)) '' {c : MonoidAlgebra ℤ G | ∀ a, c * a = a * c}) :=
  fun R G _ _ _ z hz => GlobalTheory.GroupAlg.ClassSum.mem_span R G z hz
end

section

namespace GlobalTheory.SubalgebraMulVecZero

theorem mulVec_frac_eq_zero {B : Type} [CommRing B] [IsDomain B] {ι κ : Type} [Fintype ι]
    (A : Matrix κ ι B) (hA : ∀ u : ι → B, A.mulVec u = 0 → u = 0)
    (v : ι → FractionRing B)
    (hv : (A.map (algebraMap B (FractionRing B))).mulVec v = 0) : v = 0 := by
  classical
  obtain ⟨⟨b, hbM⟩, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors B) Finset.univ v
  choose u hu using fun i => hb i (Finset.mem_univ i)
  have hAu : A.mulVec u = 0 := by
    funext k
    apply IsFractionRing.injective B (FractionRing B)
    rw [Pi.zero_apply, map_zero]
    have e : algebraMap B (FractionRing B) (A.mulVec u k) =
        (A.map (algebraMap B (FractionRing B))).mulVec (fun i => algebraMap B (FractionRing B) (u i)) k := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [e]
    have e2 : (fun i => algebraMap B (FractionRing B) (u i)) = b • v := funext hu
    rw [e2, Matrix.mulVec_smul, hv, smul_zero]
    rfl
  have hu0 := hA u hAu
  funext i
  have h1 := hu i
  rw [hu0, Pi.zero_apply, map_zero] at h1
  have hb0 : algebraMap B (FractionRing B) b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hbM
  rw [Algebra.smul_def] at h1
  exact (mul_eq_zero.1 h1.symm).resolve_left hb0

theorem exists_left_inv {K : Type} [Field K] {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : Matrix κ ι K) (hA : ∀ v : ι → K, A.mulVec v = 0 → v = 0) :
    ∃ N : Matrix ι κ K, N * A = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' A) (by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    exact hA v hv)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have e : LinearMap.toMatrix' (g ∘ₗ Matrix.toLin' A) = LinearMap.toMatrix' g * A := by
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin']
  rw [← e, hg, LinearMap.toMatrix'_id]

theorem mulVec_eq_zero_of_subalgebra {O S : Type} [CommRing O] [CommRing S] [IsDomain S]
    [Algebra O S] (B : Subalgebra O S) {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (M : Matrix κ ι S) (hM : ∀ (i : κ) (j : ι), M i j ∈ B)
    (hinj : ∀ v : ι → S, (∀ j, v j ∈ B) → Matrix.mulVec M v = 0 → v = 0)
    (w : ι → S) (hw : Matrix.mulVec M w = 0) : w = 0 := by
  let A : Matrix κ ι B := Matrix.of fun i j => ⟨M i j, hM i j⟩
  let c : B →+* S := B.val.toRingHom
  have hc : Function.Injective c := Subtype.val_injective
  have hAM : A.map c = M := by
    ext i j
    rfl
  have hA : ∀ u : ι → B, A.mulVec u = 0 → u = 0 := by
    intro u hu
    have h1 : M.mulVec (c ∘ u) = 0 := by
      funext i
      rw [← hAM, ← RingHom.map_mulVec, hu]
      simp
    have h2 := hinj (c ∘ u) (fun j => (u j).2) h1
    funext j
    apply hc
    have := congrFun h2 j
    simpa using this
  obtain ⟨N, hN⟩ := exists_left_inv (A.map (algebraMap B (FractionRing B)))
    (mulVec_frac_eq_zero A hA)
  have hL := IsFractionRing.injective S (FractionRing S)
  let g : B →+* FractionRing S := (algebraMap S (FractionRing S)).comp c
  have hg : Function.Injective g := hL.comp hc
  let φ : FractionRing B →+* FractionRing S := IsFractionRing.lift hg
  have hmap : (A.map (algebraMap B (FractionRing B))).map φ
      = M.map (algebraMap S (FractionRing S)) := by
    ext i j
    simp only [Matrix.map_apply]
    exact IsFractionRing.lift_algebraMap hg (A i j)
  have hN' : N.map φ * M.map (algebraMap S (FractionRing S)) = 1 := by
    rw [← hmap, ← Matrix.map_mul, hN]
    exact Matrix.map_one _ (map_zero φ) (map_one φ)
  have hw' : (M.map (algebraMap S (FractionRing S))).mulVec
      ((algebraMap S (FractionRing S)) ∘ w) = 0 := by
    funext i
    rw [← RingHom.map_mulVec, hw]
    simp
  have h0 : (algebraMap S (FractionRing S)) ∘ w = 0 := by
    rw [← Matrix.one_mulVec ((algebraMap S (FractionRing S)) ∘ w), ← hN',
      ← Matrix.mulVec_mulVec, hw', Matrix.mulVec_zero]
  funext j
  apply hL
  have := congrFun h0 j
  simpa using this

end GlobalTheory.SubalgebraMulVecZero
end

section

namespace GlobalTheory.LeftTransversalSum

theorem sum_mul_left_transversal {G M : Type} [Group G] [AddCommMonoid M] (H N : Subgroup G)
    (S : Finset G) (hS : ∀ s ∈ S, s ∈ H) (huniq : ∀ h ∈ H, ∃! s : G, s ∈ S ∧ s⁻¹ * h ∈ N)
    (f : G → M) (hf : ∀ (g n : G), n ∈ N → f (g * n) = f g) :
    ∀ h ∈ H, ∑ s ∈ S, f (h * s) = ∑ s ∈ S, f s := by
  intro h hh
  have hex : ∀ s : G, ∃ t : G, s ∈ S → t ∈ S ∧ t⁻¹ * (h * s) ∈ N := by
    intro s
    by_cases hs : s ∈ S
    · obtain ⟨t, ht, -⟩ := huniq _ (H.mul_mem hh (hS s hs))
      exact ⟨t, fun _ => ht⟩
    · exact ⟨s, fun h' => absurd h' hs⟩
  choose σ hσ using hex
  have uniq : ∀ x ∈ H, ∀ t ∈ S, ∀ t' ∈ S, t⁻¹ * x ∈ N → t'⁻¹ * x ∈ N → t = t' :=
    fun x hx t ht t' ht' h1 h2 => (huniq x hx).unique ⟨ht, h1⟩ ⟨ht', h2⟩
  refine Finset.sum_nbij σ (fun s hs => (hσ s hs).1) ?_ ?_ ?_
  · intro s hs s' hs' he
    have n1 := (hσ s hs).2
    have n2 := (hσ s' hs').2
    rw [← he] at n2
    have hss : s⁻¹ * s' ∈ N := by
      convert N.mul_mem (N.inv_mem n1) n2 using 1
      group
    exact uniq s' (hS s' hs') s hs s' hs' hss (by simp)
  · intro t ht
    obtain ⟨s, ⟨hs, hsN⟩, -⟩ := huniq (h⁻¹ * t) (H.mul_mem (H.inv_mem hh) (hS t ht))
    refine ⟨s, hs, ?_⟩
    refine uniq (h * s) (H.mul_mem hh (hS s hs)) _ (hσ s hs).1 t ht (hσ s hs).2 ?_
    convert N.inv_mem hsN using 1
    group
  · intro s hs
    have e := hf (σ s) ((σ s)⁻¹ * (h * s)) (hσ s hs).2
    rw [mul_inv_cancel_left] at e
    exact e

end GlobalTheory.LeftTransversalSum
end
