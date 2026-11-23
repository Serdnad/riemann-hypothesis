module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle003
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle030
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle028
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle026
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle031
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle029
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
public import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.exists_least_prime_detIdeal :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) → Nonempty ι →
      ∃ K : Ideal P, K.IsPrime ∧ detIdeal z m ≤ K ∧ ∀ Q : Ideal P, Q.IsPrime → detIdeal z m ≤ Q → K ≤ Q := by
  intro P _ _ ι _ _ z m h hι
  obtain ⟨c0⟩ := id hι
  refine ⟨genKer z m c0, (genKer_isPrime P ι z m h c0).1, (genKer_isPrime P ι z m h c0).2, ?_⟩
  intro Q hQ hle
  let f : P →+* FractionRing (P ⧸ Q) :=
    (algebraMap (P ⧸ Q) (FractionRing (P ⧸ Q))).comp (Ideal.Quotient.mk Q)
  have hf : ∀ x, f x = 0 ↔ x ∈ Q := by
    intro x
    simp only [f, RingHom.comp_apply]
    rw [map_eq_zero_iff _ (IsFractionRing.injective (P ⧸ Q) (FractionRing (P ⧸ Q))),
      Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  have h1 : (z.map f).mulVec (fun j => f (m j)) = 0 := by
    funext i
    have hi : z.mulVec m i ∈ Q :=
      hle (Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩))
    have h2 := (hf _).2 hi

    simpa [Matrix.mulVec, dotProduct, map_sum, map_mul] using h2
  have h2 : (z.map f).det = 0 := by
    have hi : z.det ∈ Q := hle (Ideal.mem_sup_right (Ideal.subset_span rfl))
    have h3 := (hf _).2 hi
    rw [RingHom.map_det] at h3
    exact h3
  obtain ⟨c, l, hc, hl, hz, hm⟩ := exists_kernel_vector _ V ι (z.map f) (fun j => f (m j)) h1 h2
  haveI : IsLocalRing V.toSubring := inferInstanceAs (IsLocalRing V)
  have hk := genKer_le_ker P ι z m h c V.toSubring (f.codRestrict V.toSubring hV)
    (fun j => ⟨l j, hl j⟩) (Subtype.ext hc) (by
      funext i
      apply Subtype.ext
      have h4 := congrFun hz i
      simpa [Matrix.mulVec, dotProduct] using h4) (fun j => Subtype.ext (hm j))
  rw [genKer_eq P ι z m h c0 c]
  intro x hx
  have h5 := hk hx
  rw [RingHom.mem_ker] at h5
  exact (hf x).1 (congrArg Subtype.val h5)
end

section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem pm_conj_apply (R : Type) [CommRing R] {n : ℕ} (w : Equiv.Perm (Fin n)) (g : GL (Fin n) R)
    (a b : Fin n) :
    (((pm R n w)⁻¹ * g * pm R n w : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b =
      (g : Matrix (Fin n) (Fin n) R) (w a) (w b) := by
  have hinv : (pm R n w)⁻¹ = pm R n w⁻¹ := (map_inv _ _).symm
  rw [hinv, Units.val_mul, Units.val_mul, Matrix.mul_apply]
  simp [-map_inv, Matrix.mul_apply, pm_apply, Equiv.Perm.eq_inv_iff_eq, Equiv.eq_symm_apply]

private theorem pm_mem_KO (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (w : Equiv.Perm (Fin n)) : pm k n w ∈ KO k (Fin n) := by
  refine ⟨pm 𝒪[k] n w, ?_⟩
  ext a b
  simp [pm_apply]

private theorem invLen_one (n : ℕ) : invLen (1 : Equiv.Perm (Fin n)) = 0 := by
  unfold invLen
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro p - ⟨h1, h2⟩
  exact lt_asymm h1 h2

theorem UpperTheory.V.AlgebraTools.permMul :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M) (w : Equiv.Perm (Fin n)) (i j : Fin n), (j : ℕ) = i + 1 → w⁻¹ i < w⁻¹ j → hk ρ (iwC k n C) (pm k n (Equiv.swap i j)) * hk ρ (iwC k n C) (pm k n w) = hk ρ (iwC k n C) (pm k n (Equiv.swap i j * w)) := by
  intro k _ _ _ _ n C A M _ _ _ ρ w i j hij hlt
  rw [map_mul]
  have hP := (heckePairIwC k n C).1
  have hne : i ≠ j := by
    intro h
    rw [h] at hij
    omega
  have hU : unipO k n ≤ iwC k n C := by
    unfold iwC
    exact le_sup_right.trans le_sup_left
  apply hkMul A _ M ρ _ _ _ hP
  · intro b hb
    obtain ⟨r, hr⟩ : ∃ r : 𝓀[k] → 𝒪[k], ∀ c, IsLocalRing.residue 𝒪[k] (r c) = c :=
      ⟨fun c => (IsLocalRing.residue_surjective c).choose,
        fun c => (IsLocalRing.residue_surjective c).choose_spec⟩
    obtain ⟨x, hx1, hx2, -, hx4⟩ := simpleOrbit k n C i j hij r hr
    obtain ⟨c, b', hb', he⟩ := hx4 b hb
    have hxc : x c ∈ unipB k (Fin n) ⊓ KO k (Fin n) := hx2 c
    have hmem : (pm k n w)⁻¹ * x c * pm k n w ∈ unipO k n := by
      unfold unipO
      refine Subgroup.mem_inf.2 ⟨(mem_unipB k).2 ⟨?_, ?_⟩, ?_⟩
      · intro a b hba
        rw [pm_conj_apply, hx1 c]
        have hab : w a ≠ w b := fun h => (ne_of_lt hba) (w.injective h).symm
        rw [Matrix.add_apply, Matrix.one_apply_ne hab, zero_add, Matrix.single_apply, if_neg]
        rintro ⟨h1, h2⟩
        apply absurd hlt
        rw [h1, h2]
        simpa using hba.le
      · intro a
        rw [pm_conj_apply, hx1 c]
        rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply, if_neg, add_zero]
        rintro ⟨h1, h2⟩
        exact hne (h1.trans h2.symm)
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (pm_mem_KO k w))
          (Subgroup.mem_inf.1 hxc).2) (pm_mem_KO k w)
    refine ⟨b', hb', (pm k n w)⁻¹ * x c * pm k n w, hU hmem, ?_⟩
    rw [he]
    group
  · rw [← map_mul, permCard, permCard, permCard, ((lenStep n w).1 i j hij).1 hlt]
    have hij' : (1 : Equiv.Perm (Fin n))⁻¹ i < (1 : Equiv.Perm (Fin n))⁻¹ j := by
      rw [inv_one]
      show i < j
      rw [Fin.lt_def]
      omega
    have h1 := ((lenStep n 1).1 i j hij).1 hij'
    rw [mul_one, invLen_one] at h1
    rw [h1]
    ring
end

section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem domSum_reps {G : Type} [Group G] {N I : Subgroup G} (hN : N ≤ I) (d : G) (h : FinOrb I I d) :
    ∃ s : Finset G, (∀ u ∈ s, u ∈ N) ∧ ∀ y ∈ N, ∃! u, u ∈ s ∧ d⁻¹ * (u⁻¹ * y) * d ∈ I := by
  obtain ⟨S, hS, hb⟩ := Set.exists_subset_bijOn (N : Set G) (fun y => ((y * d : G) : G ⧸ I))
  have hq : ((fun y => ((y * d : G) : G ⧸ I)) '' (N : Set G)).Finite := by
    refine h.subset ?_
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨⟨y, hN hy⟩, rfl⟩
  have hf : S.Finite := Set.Finite.of_finite_image (hb.image_eq ▸ hq) hb.injOn
  have key : ∀ u y : G, ((u * d : G) : G ⧸ I) = ((y * d : G) : G ⧸ I) ↔ d⁻¹ * (u⁻¹ * y) * d ∈ I := by
    intro u y
    rw [QuotientGroup.eq]
    have : (u * d)⁻¹ * (y * d) = d⁻¹ * (u⁻¹ * y) * d := by group
    rw [this]
  refine ⟨hf.toFinset, fun u hu => hS (hf.mem_toFinset.1 hu), fun y hy => ?_⟩
  obtain ⟨u, hu, e⟩ := hb.surjOn ⟨y, hy, rfl⟩
  refine ⟨u, ⟨hf.mem_toFinset.2 hu, (key u y).1 e⟩, ?_⟩
  rintro u' ⟨hu', e'⟩
  exact hb.injOn (hf.mem_toFinset.1 hu') hu (((key u' y).2 e').trans e.symm)

private theorem domSum_gen {G : Type} [Group G] {I : Subgroup G} (F : LeviFact I) (d : G) (hI : HeckePair I)
    (hp : F.Pos d) (hn : F.NormJ d) (s : Finset G) (hs : ∀ u ∈ s, u ∈ F.Uf ⊓ I)
    (hs' : ∀ x ∈ F.Uf ⊓ I, ∃! u, u ∈ s ∧ d⁻¹ * (u⁻¹ * x) * d ∈ I)
    (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (v : fixd ρ I) :
    (hk ρ I d v : M) = ∑ u ∈ s, ρ (u * d) v := by
  classical
  have H := leviSum G I F d hI hp {d}
    (fun a ha => ⟨1, one_mem _, 1, one_mem _, by simpa using ha⟩)
    (fun j hj => ⟨d, ⟨Finset.mem_singleton_self d, by simpa [mul_assoc] using (hn j hj).2⟩,
      fun a ha => Finset.mem_singleton.1 ha.1⟩)
    (fun _ => s) (fun a ha => by
      rw [Finset.mem_singleton.1 ha]
      exact ⟨hs, hs'⟩)
  have h2 := (hkApply A G M ρ I I d (hI d)).2.1 (s.image (· * d)) ?_ ?_ v
  · rw [hk, h2, Finset.sum_image (fun a _ b _ h => mul_right_cancel h)]
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨⟨u, (hs u hu).2⟩, rfl⟩
  · intro q hq
    obtain ⟨⟨a, u⟩, ⟨ha, hu, e⟩, huniq⟩ := (H q).1 hq
    have had : a = d := Finset.mem_singleton.1 ha
    subst had
    refine ⟨u * a, ⟨Finset.mem_image.2 ⟨u, hu, rfl⟩, e⟩, ?_⟩
    rintro y ⟨hy, e'⟩
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.1 hy
    have := huniq (a, u') ha hu' e'
    rw [show u' = u from (Prod.ext_iff.1 this).2]

theorem UpperTheory.V.AlgebraTools.domSum :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (t : Fin n → kˣ), Dom t → ∃ s : Finset (GL (Fin n) k), (∀ u ∈ s, u ∈ unipO k n) ∧ (∀ y ∈ unipO k n, ∃! u, u ∈ s ∧ (diagT k (Fin n) t)⁻¹ * (u⁻¹ * y) * diagT k (Fin n) t ∈ unipO k n) ∧ ∀ (C : Subgroup 𝓀[k]ˣ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M) (v : fixd ρ (iwC k n C)), (hk ρ (iwC k n C) (diagT k (Fin n) t) v : M) = ∑ u ∈ s, ρ (u * diagT k (Fin n) t) v := by
  intro k _ _ _ _ n t ht
  have key : ∀ (C : Subgroup 𝓀[k]ˣ), ∀ u ∈ unipO k n, ∀ y ∈ unipO k n,
      (diagT k (Fin n) t)⁻¹ * (u⁻¹ * y) * diagT k (Fin n) t ∈ iwC k n C ↔
      (diagT k (Fin n) t)⁻¹ * (u⁻¹ * y) * diagT k (Fin n) t ∈ unipO k n := by
    intro C u hu y hy
    obtain ⟨F, -, -, -, hU, -, hF⟩ := factTorus k n C
    rw [← hU] at hu hy ⊢
    have := F.M_U _ (inv_mem ((hF t).2 ht).1) _ (mul_mem (inv_mem hu.1) hy.1)
    rw [inv_inv] at this
    exact ⟨fun h => ⟨this, h⟩, fun h => h.2⟩
  have hle : unipO k n ≤ iwC k n ⊤ := le_sup_right.trans le_sup_left
  obtain ⟨s, hs, hs'⟩ := domSum_reps hle (diagT k (Fin n) t) ((heckePairIwC k n ⊤).1 _)
  have hs2 : ∀ (C : Subgroup 𝓀[k]ˣ), ∀ y ∈ unipO k n, ∃! u, u ∈ s ∧
      (diagT k (Fin n) t)⁻¹ * (u⁻¹ * y) * diagT k (Fin n) t ∈ iwC k n C := by
    intro C y hy
    refine (existsUnique_congr fun u => and_congr_right fun hu => ?_).1 (hs' y hy)
    rw [key ⊤ u (hs u hu) y hy, key C u (hs u hu) y hy]
  refine ⟨s, hs, fun y hy => ?_, fun C A M _ _ _ ρ v => ?_⟩
  · exact (existsUnique_congr fun u => and_congr_right fun hu => key ⊤ u (hs u hu) y hy).1 (hs' y hy)
  · obtain ⟨F, -, -, -, hU, -, hF⟩ := factTorus k n C
    exact domSum_gen F _ (heckePairIwC k n C).1 ((hF t).2 ht) (hF t).1 s (hU ▸ hs) (hU ▸ hs2 C) A M ρ v
end
