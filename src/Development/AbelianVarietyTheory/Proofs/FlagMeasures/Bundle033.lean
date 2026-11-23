module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle028
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.Henselian
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
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.DedekindDomain.Factorization
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001

@[expose] public section

section

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Inhab
open GlobalTheory.HL.Model

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem cj_int (L : LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.O_def] at hx ⊢
  exact hx.map L.cj

theorem hf_sum_right (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) {ι : Type} (s : Finset ι)
    (a : ι → Fin n → E) (y : Fin n → E) : hf L H y (∑ i ∈ s, a i) = ∑ i ∈ s, hf L H y (a i) := by
  induction s using Finset.cons_induction with
  | empty => simp [hf]
  | cons i s hi ih => rw [Finset.sum_cons, Finset.sum_cons, hf_add_right, ih]

section General
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

end General

theorem mem_stdLat (L : LocE F E) {n : ℕ} (x : Fin n → E) : x ∈ stdLat L n ↔ ∀ i, x i ∈ L.O := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      intro i
      show (Pi.single j 1 : Fin n → E) i ∈ L.O
      rw [Pi.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    | zero => intro i; exact zero_mem _
    | add u v _ _ hu hv => intro i; exact add_mem (hu i) (hv i)
    | smul c u _ hu =>
      intro i
      rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
      exact mul_mem c.2 (hu i)
  · intro hx
    have hsum : x = ∑ i, (⟨x i, hx i⟩ : L.O) • (Pi.single i 1 : Fin n → E) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Subring.smul_def]
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem isSD_stdLat (L : LocE F E) {n : ℕ} (H K : Matrix (Fin n) (Fin n) E) (hH : IsIntM L H)
    (hK : IsIntM L K) (hKH : K * H = 1) : IsSD L H (stdLat L n) := by
  refine ⟨⟨Submodule.fg_span (Set.finite_range _), ?_⟩, ?_⟩
  · rw [eq_top_iff]
    intro v _
    have hsum : v = ∑ i, v i • (Pi.single i 1 : Fin n → E) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span ⟨i, rfl⟩))
  · intro y
    rw [mem_stdLat]
    constructor
    · intro h j
      have hrow : ∀ i, (Matrix.mulVec H fun k => L.cj (y k)) i ∈ L.O := by
        intro i
        have hs : (Pi.single i 1 : Fin n → E) ∈ stdLat L n := (mem_stdLat L _).2 fun k => by
          rw [Pi.single_apply]
          split_ifs
          · exact one_mem _
          · exact zero_mem _
        have := h _ hs
        simpa [hf, Pi.single_apply, Matrix.mulVec, dotProduct] using this
      have hcK : (fun k => L.cj (y k)) = Matrix.mulVec K (Matrix.mulVec H fun k => L.cj (y k)) := by
        rw [Matrix.mulVec_mulVec, hKH, Matrix.one_mulVec]
      have hcj : (Matrix.mulVec K (Matrix.mulVec H fun k => L.cj (y k))) j ∈ L.O := by
        simp only [Matrix.mulVec, dotProduct]
        exact Subring.sum_mem _ fun i _ => mul_mem (hK j i) (hrow i)
      rw [← hcK] at hcj
      have := cj_int L hcj
      simpa [L.cj_cj] using this
    · intro h x hx
      rw [mem_stdLat] at hx
      exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ =>
        mul_mem (mul_mem (hx i) (hH i j)) (cj_int L (h j))

section Blocks
variable {s m N : ℕ} (e : Fin s ⊕ Fin m ≃ Fin N)

end Blocks

end GlobalTheory.HL.Inhab
end
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

noncomputable section

namespace GlobalTheory.Mass.SemiBasis

variable {K : Type} [Field K] [NumberField K]

open NumberField IsDedekindDomain in
private theorem natCast_not_isUnit_lemma_3 {F : Type} [Field F] [NumberField F] {N : ℕ} (hN : 2 ≤ N) :
    ¬ IsUnit (N : 𝓞 F) := by
  intro h
  have h1 : IsUnit (Algebra.norm ℤ (algebraMap ℤ (𝓞 F) (N : ℤ))) := by
    have : algebraMap ℤ (𝓞 F) (N : ℤ) = (N : 𝓞 F) := by simp
    rw [this]; exact h.map _
  rw [Algebra.norm_algebraMap, Int.isUnit_iff] at h1
  have hk : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
  have h2 : (2 : ℤ) ≤ (N : ℤ) ^ Module.finrank ℤ (𝓞 F) := by
    calc (2 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
      _ = (N : ℤ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by omega) hk
  omega

open NumberField IsDedekindDomain in
private theorem mem_primeTo_ne_zero_lemma_2 {F : Type} [Field F] [NumberField F] {N : ℕ} (hN : 2 ≤ N)
    {x : 𝓞 F} (hx : x ∈ _root_.GlobalTheory.Mass.primeTo (N : 𝓞 F)) : x ≠ 0 := by
  rintro rfl
  obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal (Ideal.span {(N : 𝓞 F)})
    (by rw [Ne, Ideal.span_singleton_eq_top]; exact natCast_not_isUnit_lemma_3 hN)
  exact hx Q hQ (hle (Ideal.mem_span_singleton_self _)) Q.zero_mem

open NumberField IsDedekindDomain in
private theorem primeTo_le_nonZeroDivisors__lemma {F : Type} [Field F] [NumberField F] {N : ℕ}
    (hN : 2 ≤ N) : _root_.GlobalTheory.Mass.primeTo (N : 𝓞 F) ≤ nonZeroDivisors (𝓞 F) :=
  fun _ hx => mem_nonZeroDivisors_of_ne_zero (mem_primeTo_ne_zero_lemma_2 hN hx)

open NumberField Matrix in
open scoped ENNReal Classical in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.Mass.SemiBasis.primeTo_le {d : ℕ} (hd : 2 ≤ d) :
    _root_.GlobalTheory.Mass.primeTo (d : 𝓞 K) ≤ nonZeroDivisors (𝓞 K) :=
  primeTo_le_nonZeroDivisors__lemma hd

abbrev A (K : Type) [Field K] [NumberField K] {d : ℕ} (hd : 2 ≤ d) : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K (primeTo (d : 𝓞 K)) (primeTo_le hd)

theorem primes_finite {d : ℕ} (hd : 2 ≤ d) : {P : Ideal (A K hd) | P.IsPrime}.Finite := by
  have hd0 : (d : 𝓞 K) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hfin : {P : Ideal (𝓞 K) | P.IsMaximal ∧ (d : 𝓞 K) ∈ P}.Finite := by
    have h0 : Ideal.span {(d : 𝓞 K)} ≠ 0 := by
      simpa [Ideal.span_singleton_eq_bot] using hd0
    refine ((Ideal.finite_factors h0).image (fun v => v.asIdeal)).subset ?_
    rintro P ⟨hP, hdP⟩
    have hb : P ≠ ⊥ := by
      rintro rfl
      exact hd0 (by simpa using hdP)
    exact ⟨⟨P, hP.isPrime, hb⟩, Ideal.dvd_span_singleton.2 hdP, rfl⟩
  apply ((hfin.insert ⊥).image (Ideal.map (algebraMap (𝓞 K) (A K hd)))).subset
  intro P hP
  have hP' : P.IsPrime := hP
  obtain ⟨hQ, hdisj⟩ :=
    (IsLocalization.isPrime_iff_isPrime_disjoint (primeTo (d : 𝓞 K)) (A K hd) P).mp hP'
  refine ⟨P.comap (algebraMap (𝓞 K) (A K hd)), ?_,
    IsLocalization.map_under (primeTo (d : 𝓞 K)) (A K hd) P⟩
  set Q := P.comap (algebraMap (𝓞 K) (A K hd))
  have hsub : (Q : Set (𝓞 K)) ⊆ ⋃ i ∈ (hfin.toFinset : Set (Ideal (𝓞 K))), ((id i : Ideal (𝓞 K)) : Set (𝓞 K)) := by
    intro x hx
    by_contra hn
    refine Set.disjoint_left.mp hdisj (?_ : x ∈ primeTo (d : 𝓞 K)) hx
    intro I hI hdI hxI
    apply hn
    simp only [Set.mem_iUnion]
    exact ⟨I, by simpa using ⟨hI, hdI⟩, hxI⟩
  by_cases hb : Q = ⊥
  · exact Or.inl hb
  have hmax : Q.IsMaximal := hQ.isMaximal hb
  obtain ⟨I, hI, hle⟩ := (Ideal.subset_union_prime ⊥ ⊥ (fun i hi _ _ => by
    have : i.IsMaximal ∧ (d : 𝓞 K) ∈ i := by simpa using hi
    exact this.1.isPrime)).1 hsub
  have hI' : I.IsMaximal ∧ (d : 𝓞 K) ∈ I := by simpa using hI
  have : Q = I := hmax.eq_of_le hI'.1.ne_top hle
  right
  rw [this]
  exact hI'

theorem isPID {d : ℕ} (hd : 2 ≤ d) : IsPrincipalIdealRing (A K hd) := by
  have : IsDedekindDomain (A K hd) :=
    IsLocalization.isDedekindDomain (𝓞 K) (primeTo_le hd) (A K hd)
  exact IsPrincipalIdealRing.of_finite_primes (primes_finite hd)

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

end GlobalTheory.Mass.SemiBasis
end
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.LatticeGens

section Dedekind
variable {R V : Type*} [CommRing R] [IsDedekindDomain R] [AddCommGroup V] [Module R V]

theorem exists_gens_of_between (A : Submodule R V) (m : R) (hm : m ≠ 0) (t : Finset V) :
    (∀ x ∈ t, m • x ∈ A) → ∀ L : Submodule R V, A ≤ L → L ≤ A ⊔ Submodule.span R (t : Set V) →
      ∃ t' : Finset V, t'.card ≤ t.card ∧ L = A ⊔ Submodule.span R (t' : Set V) := by
  induction t using Finset.induction_on with
  | empty =>
    intro _ L h1 h2
    exact ⟨∅, le_rfl, le_antisymm h2 (by simpa using h1)⟩
  | insert x t hx ih =>
    intro ht L h1 h2
    obtain ⟨t', hc, ht'⟩ := ih (fun y hy => ht y (Finset.mem_insert_of_mem hy))
      (L ⊓ (A ⊔ Submodule.span R (t : Set V))) (le_inf h1 le_sup_left) inf_le_right
    set I : Ideal R := (A ⊔ Submodule.span R (t : Set V)).comap (LinearMap.toSpanSingleton R V x)
      with hI
    set J : Ideal R := (L ⊔ Submodule.span R (t : Set V)).comap (LinearMap.toSpanSingleton R V x)
      with hJ
    have hIJ : I ≤ J := Submodule.comap_mono (sup_le_sup_right h1 _)
    have hI0 : I ≠ 0 := by
      intro h
      have : m ∈ I := Submodule.mem_sup_left (ht x (Finset.mem_insert_self _ _))
      rw [h] at this
      exact hm (by simpa using this)
    obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq hIJ hI0
    have haJ : a ∈ J := by
      rw [← ha]; exact Submodule.mem_sup_right (Ideal.mem_span_singleton_self a)
    obtain ⟨l, hl, s, hs, hls⟩ := Submodule.mem_sup.1 haJ
    have hls' : l + s = a • x := hls
    refine ⟨insert l t', ?_, le_antisymm ?_ ?_⟩
    · rw [Finset.card_insert_of_notMem hx]
      exact (Finset.card_insert_le _ _).trans (by omega)
    · intro y hy
      have hy2 := h2 hy
      rw [Finset.coe_insert, Submodule.span_insert] at hy2
      obtain ⟨a0, ha0, z, hz, rfl⟩ := Submodule.mem_sup.1 hy2
      obtain ⟨w, hw, s0, hs0, rfl⟩ := Submodule.mem_sup.1 hz
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hw
      have hr : r ∈ J := by
        have : r • x = ((a0 + (r • x + s0)) - a0) - s0 := by abel
        change r • x ∈ L ⊔ Submodule.span R (t : Set V)
        rw [this]
        exact sub_mem (Submodule.mem_sup_left (sub_mem hy (h1 ha0))) (Submodule.mem_sup_right hs0)
      rw [← ha] at hr
      obtain ⟨i, hi, j, hj, rfl⟩ := Submodule.mem_sup.1 hr
      obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.1 hj
      have hi' : i • x ∈ A ⊔ Submodule.span R (t : Set V) := hi
      have key : a0 + ((i + k * a) • x + s0) - k • l ∈
          L ⊓ (A ⊔ Submodule.span R (t : Set V)) := by
        refine ⟨sub_mem hy (L.smul_mem _ hl), ?_⟩
        have : a0 + ((i + k * a) • x + s0) - k • l = a0 + i • x + s0 + k • s := by
          rw [add_smul, mul_smul, ← hls', smul_add]; abel
        rw [this]
        exact add_mem (add_mem (add_mem (Submodule.mem_sup_left ha0) hi')
          (Submodule.mem_sup_right hs0)) (Submodule.mem_sup_right (Submodule.smul_mem _ _ hs))
      rw [ht'] at key
      have hle : A ⊔ Submodule.span R (t' : Set V) ≤
          A ⊔ Submodule.span R ((insert l t' : Finset V) : Set V) :=
        sup_le_sup_left (Submodule.span_mono (by simp)) _
      have hl' : k • l ∈ A ⊔ Submodule.span R ((insert l t' : Finset V) : Set V) :=
        Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      simpa using add_mem (hle key) hl'
    · rw [Finset.coe_insert, Submodule.span_insert]
      refine sup_le h1 (sup_le ?_ ?_)
      · exact (Submodule.span_singleton_le_iff_mem _ _).2 hl
      · exact (le_sup_right.trans ht'.ge).trans inf_le_left

end Dedekind

section Count
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem idxN_smul_mem (A B : Submodule R V) {x : V} (hx : x ∈ B) :
    ((idxN B A : ℕ) : R) • x ∈ A := by
  rw [Nat.cast_smul_eq_nsmul]
  exact AddSubgroup.nsmul_relIndex_mem A.toAddSubgroup (K := B.toAddSubgroup) hx

theorem card_map_mkQ (A B : Submodule R V) : Nat.card (B.map A.mkQ) = idxN B A := by
  have h := AddSubgroup.relIndex_ker (K := B.toAddSubgroup) A.mkQ.toAddMonoidHom
  have hk : A.mkQ.toAddMonoidHom.ker = A.toAddSubgroup := by
    ext x; simp
  rw [hk] at h
  unfold idxN
  rw [h]
  rfl

theorem encard_between_le (A B : Submodule R V) (hn : idxN B A ≠ 0) (e : ℕ)
    (h : ∀ L, A ≤ L → L ≤ B →
      ∃ t' : Finset V, t'.card ≤ e ∧ L = A ⊔ Submodule.span R (t' : Set V)) :
    {L | A ≤ L ∧ L ≤ B}.encard ≤ ((idxN B A ^ e : ℕ) : ℕ∞) := by
  have hfin : Finite (B.map A.mkQ) := Nat.finite_of_card_ne_zero (by rwa [card_map_mkQ])
  let Φ : (Fin e → B.map A.mkQ) → Submodule R V := fun f =>
    (Submodule.span R (Set.range fun i => (f i : V ⧸ A))).comap A.mkQ
  have hsub : {L | A ≤ L ∧ L ≤ B} ⊆ Φ '' Set.univ := by
    rintro L ⟨h1, h2⟩
    obtain ⟨t, hc, ht⟩ := h L h1 h2
    obtain ⟨emb⟩ : Nonempty (t ↪ Fin e) :=
      Function.Embedding.nonempty_of_card_le (by simpa using hc)
    let g : Fin e → V := Function.extend emb (fun x => (x : V)) 0
    have hg : ∀ i, g i ∈ Submodule.span R (t : Set V) := by
      intro i
      by_cases hi : ∃ x, emb x = i
      · obtain ⟨x, rfl⟩ := hi
        simp only [g, emb.injective.extend_apply]
        exact Submodule.subset_span x.2
      · simp only [g, Function.extend_apply' _ _ _ hi]
        simp
    have hspan : Submodule.span R (Set.range g) = Submodule.span R (t : Set V) := by
      refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
      · rintro _ ⟨i, rfl⟩; exact hg i
      · intro x hx
        exact ⟨emb ⟨x, hx⟩, by simp only [g, emb.injective.extend_apply]⟩
    have hgB : ∀ i, g i ∈ B := fun i => h2 (by rw [ht]; exact Submodule.mem_sup_right (hg i))
    refine ⟨fun i => ⟨A.mkQ (g i), Submodule.mem_map_of_mem (hgB i)⟩, trivial, ?_⟩
    have : (Set.range fun i => A.mkQ (g i)) = A.mkQ '' Set.range g := by
      rw [← Set.range_comp]; rfl
    change (Submodule.span R (Set.range fun i => A.mkQ (g i))).comap A.mkQ = L
    rw [this, ← Submodule.map_span, Submodule.comap_map_mkQ, hspan, ← ht]
  calc {L | A ≤ L ∧ L ≤ B}.encard ≤ (Φ '' Set.univ).encard := Set.encard_le_encard hsub
    _ ≤ (Set.univ : Set (Fin e → B.map A.mkQ)).encard := Set.encard_image_le _ _
    _ = _ := by
      rw [Set.encard_univ, ENat.card_eq_coe_natCard, Nat.card_fun, card_map_mkQ]
      simp

end Count

theorem exists_scaled_span (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (B : Submodule (𝓞 K) V) (hB : B.FG) :
    ∃ (c : 𝓞 K) (t : Finset V), c ≠ 0 ∧ t.card ≤ Module.finrank K V ∧ (∀ x ∈ t, c • x ∈ B) ∧
      B ≤ Submodule.span (𝓞 K) (t : Set V) := by
  obtain ⟨b, hbB, hspan, hli⟩ := exists_linearIndependent K (B : Set V)
  have hbf : b.Finite := hli.setFinite
  obtain ⟨s, rfl⟩ := hbf.exists_finset_coe
  have hcard : s.card ≤ Module.finrank K V := LinearIndependent.finset_card_le_finrank hli
  obtain ⟨G, rfl⟩ := hB
  have h1 : ∀ x ∈ G, ∃ c : 𝓞 K, c ≠ 0 ∧ c • x ∈ Submodule.span (𝓞 K) (s : Set V) := by
    intro x hx
    have hx' : x ∈ Submodule.span K (s : Set V) := by
      rw [hspan]; exact Submodule.subset_span (Submodule.subset_span hx)
    obtain ⟨c, hc⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ _ hx'
    exact ⟨c, nonZeroDivisors.coe_ne_zero c, hc⟩
  choose! f hf0 hf using h1
  set c : 𝓞 K := ∏ x ∈ G, f x with hc
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 hf0
  have hcK : algebraMap (𝓞 K) K c ≠ 0 := by simpa using hc0
  have hcG : ∀ x ∈ G, c • x ∈ Submodule.span (𝓞 K) (s : Set V) := by
    intro x hx
    rw [hc, ← Finset.prod_erase_mul _ _ hx, mul_smul]
    exact Submodule.smul_mem _ _ (hf x hx)
  let φ : V →ₗ[𝓞 K] V := (LinearMap.lsmul K V (algebraMap (𝓞 K) K c)⁻¹).restrictScalars (𝓞 K)
  have hφ : ∀ x, φ (c • x) = x := by
    intro x
    simp only [φ, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]
    rw [← algebraMap_smul K c x, smul_smul, inv_mul_cancel₀ hcK, one_smul]
  refine ⟨c, s.image φ, hc0, Finset.card_image_le.trans hcard, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    rw [← map_smul, hφ]
    exact hbB hy
  · rw [Submodule.span_le]
    intro x hx
    rw [Finset.coe_image, ← Submodule.map_span, ← hφ x]
    exact Submodule.mem_map_of_mem (hcG x hx)

theorem gens_and_count : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (A B : Submodule (𝓞 K) V), A ≤ B → idxN B A ≠ 0 → (B.FG → ∃ t : Finset V, t.card ≤ Module.finrank K V ∧ B = A ⊔ Submodule.span (𝓞 K) (t : Set V)) ∧ ∀ (e : ℕ) (t : Finset V), t.card ≤ e → B = A ⊔ Submodule.span (𝓞 K) (t : Set V) → ({L | A ≤ L ∧ L ≤ B}.encard ≤ ((idxN B A ^ e : ℕ) : ℕ∞)) ∧ ∀ L, A ≤ L → L ≤ B → ∃ t' : Finset V, t'.card ≤ e ∧ L = A ⊔ Submodule.span (𝓞 K) (t' : Set V) := by
  intro K V _ _ _ _ _ _ _ A B hAB hn
  have hn' : ((idxN B A : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hn
  refine ⟨fun hB => ?_, fun e t hc ht => ?_⟩
  · obtain ⟨c, t, hc0, hcard, hcB, hBt⟩ := exists_scaled_span K V B hB
    obtain ⟨t', h1, h2⟩ := exists_gens_of_between A (((idxN B A : ℕ) : 𝓞 K) * c)
      (mul_ne_zero hn' hc0) t
      (fun x hx => by rw [mul_smul]; exact idxN_smul_mem A B (hcB x hx)) B hAB
      (hBt.trans le_sup_right)
    exact ⟨t', h1.trans hcard, h2⟩
  · have key : ∀ L, A ≤ L → L ≤ B →
        ∃ t' : Finset V, t'.card ≤ e ∧ L = A ⊔ Submodule.span (𝓞 K) (t' : Set V) := by
      intro L h1 h2
      obtain ⟨t', h3, h4⟩ := exists_gens_of_between A _ hn' t
        (fun x hx => idxN_smul_mem A B
          (by rw [ht]; exact Submodule.mem_sup_right (Submodule.subset_span hx))) L h1
        (h2.trans ht.le)
      exact ⟨t', h3.trans hc, h4⟩
    exact ⟨encard_between_le A B hn e key, key⟩

end GlobalTheory.Mass.LatticeGens
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.unitriangular_close_to_one_inverse_close : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (n : ℕ) (M : Matrix (Fin n) (Fin n) E) (t : E), t ∈ L.O → (∀ i j, j < i → M i j = 0) → (∀ i, M i i = 1) → (∀ i j, ∃ o ∈ L.O, (M - 1) i j = t * o) → ∃ Mi : Matrix (Fin n) (Fin n) E, Mi * M = 1 ∧ M * Mi = 1 ∧ ∀ i j, ∃ o ∈ L.O, (Mi - 1) i j = t * o := by
  first | exact @GlobalTheory.unitriangular_inv_close | exact GlobalTheory.unitriangular_inv_close | (intros; apply GlobalTheory.unitriangular_inv_close <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SgAlg GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct ENNReal NNReal

namespace GlobalTheory.GramFibreRescale

theorem isFibreFamily_smul {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
    [TopologicalSpace X] [MeasurableSpace X] {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V}
    {ν : Measure X} {B : Set X} {fib : X → Measure V} (h : IsFibreFamily μ f ι U ν B fib)
    (c d : ℝ≥0) (hd : d ≠ 0) :
    IsFibreFamily (c • μ) f ι U (d • ν) B (fun b => (c / d) • fib b) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφ hc hU => ⟨fun b hb => ?_, ?_⟩⟩
  · rw [Measure.smul_apply, h1 b, smul_zero]
  · simp only [Measure.restrict_smul, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← mul_assoc, ← ENNReal.coe_mul,
      mul_div_cancel₀ _ hd, h2 φ hφ]
  · exact ((h3 φ hφ hc hU).1 b hb).smul_measure_nnreal
  · simp only [integral_smul_nnreal_measure]
    exact (h3 φ hφ hc hU).2.const_smul (c / d)

end GlobalTheory.GramFibreRescale
end
