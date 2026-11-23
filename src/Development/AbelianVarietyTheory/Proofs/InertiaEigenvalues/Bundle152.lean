module

public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.ExpDefs
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import ReciprocityTheory.GaloisValuations.GlobalA
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory

theorem orbit_stab_cut_finite (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (H : Subgroup (G E Ω)) (y : Ω) :
    ∃ s : Finset Ω, ∀ σ : G E Ω, (∀ x ∈ s, σ x = x) ↔ ∀ τ ∈ H, ∃ τ' ∈ H, σ (τ y) = τ' y := by
  classical
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  have hint : IsIntegral E y := Algebra.IsIntegral.isIntegral y
  set S : Set Ω := {t | ∃ τ ∈ H, τ y = t} with hSdef
  have hS : S.Finite := by
    refine ((minpoly E y).rootSet_finite Ω).subset ?_
    rintro t ⟨τ, -, rfl⟩
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [Polynomial.aeval_algEquiv]
    simp [minpoly.aeval]
  set O := hS.toFinset with hOdef
  have hmemO : ∀ t, t ∈ O ↔ ∃ τ ∈ H, τ y = t := fun t => by simp [O, S]
  set P : Polynomial Ω := ∏ t ∈ O, (X - C t) with hP
  refine ⟨(Finset.range (P.natDegree + 1)).image P.coeff, fun σ => ?_⟩
  have key : (∀ x ∈ (Finset.range (P.natDegree + 1)).image P.coeff, σ x = x) ↔
      P.map (σ : Ω →+* Ω) = P := by
    constructor
    · intro h
      ext n
      rw [coeff_map]
      by_cases hn : n ≤ P.natDegree
      · exact h _ (Finset.mem_image.2 ⟨n, Finset.mem_range.2 (Nat.lt_succ_of_le hn), rfl⟩)
      · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hn)]; simp
    · intro h x hx
      obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hx
      have := congrArg (fun p => p.coeff n) h
      simpa [coeff_map] using this
  have hmap : P.map (σ : Ω →+* Ω) = ∏ t ∈ O, (X - C (σ t)) := by
    simp [hP, Polynomial.map_prod]
  rw [key, hmap]
  constructor
  · intro h τ hτ
    have h0 : (∏ t ∈ O, (X - C (σ t))).eval (σ (τ y)) = 0 := by
      rw [eval_prod]
      exact Finset.prod_eq_zero ((hmemO _).2 ⟨τ, hτ, rfl⟩) (by simp)
    rw [h, hP, eval_prod, Finset.prod_eq_zero_iff] at h0
    obtain ⟨t, ht, ht0⟩ := h0
    obtain ⟨τ', hτ', rfl⟩ := (hmemO t).1 ht
    refine ⟨τ', hτ', ?_⟩
    simpa [sub_eq_zero] using ht0
  · intro h
    have hinj : Function.Injective (σ : Ω → Ω) := σ.injective
    have hsub : O.image σ ⊆ O := by
      intro u hu
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨τ, hτ, rfl⟩ := (hmemO t).1 ht
      obtain ⟨τ', hτ', he⟩ := h τ hτ
      exact (hmemO _).2 ⟨τ', hτ', he.symm⟩
    have heq : O.image σ = O :=
      Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injective _ hinj])
    calc ∏ t ∈ O, (X - C (σ t)) = ∏ u ∈ O.image σ, (X - C u) :=
          by
          rw [Finset.prod_image (fun a _ b _ hab => hinj hab)]
      _ = P := by rw [heq]

end GlobalTheory
end

section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.PowFix

theorem exists_pos_pow_apply_eq {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (σ : Ω ≃ₐ[E] Ω) (x : Ω) (hx : IsIntegral E x) : ∃ k : ℕ, 0 < k ∧ (σ ^ k) x = x := by
  classical
  have hfin : ((minpoly E x).rootSet Ω).Finite := Polynomial.rootSet_finite _ _
  haveI := hfin.to_subtype
  let f : ℕ → (minpoly E x).rootSet Ω := fun n => ⟨(σ ^ n) x, by
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hx, ?_⟩
    rw [show ((σ ^ n) x) = ((σ ^ n : Ω ≃ₐ[E] Ω) : Ω →ₐ[E] Ω) x from rfl,
      Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]⟩
  obtain ⟨a, b, hab, h⟩ := Finite.exists_ne_map_eq_of_infinite f
  have h' : (σ ^ a) x = (σ ^ b) x := congrArg Subtype.val h
  have key : ∀ a b : ℕ, a < b → (σ ^ a) x = (σ ^ b) x → ∃ k : ℕ, 0 < k ∧ (σ ^ k) x = x := by
    intro a b hlt he
    refine ⟨b - a, Nat.sub_pos_of_lt hlt, ?_⟩
    have e : σ ^ b = σ ^ a * σ ^ (b - a) := by rw [← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [e, AlgEquiv.mul_apply] at he
    exact ((σ ^ a).injective he).symm
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · exact key a b hlt h'
  · exact key b a hlt h'.symm

theorem pow_apply_eq_of_apply_eq {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (τ : Ω ≃ₐ[E] Ω) (x : Ω) (h : τ x = x) (j : ℕ) : (τ ^ j) x = x := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, h, ih]

theorem exists_pos_pow_fix : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (σ : G E Ω) (s : Finset Ω), ∃ m : ℕ, 0 < m ∧ ∀ x ∈ s, (σ ^ m) x = x := by
  intro E Ω _ _ _ _ _ σ s
  classical
  have hint : ∀ x : Ω, IsIntegral E x := fun x =>
    (Algebra.IsAlgebraic.isAlgebraic (R := E) x).isIntegral
  choose k hk0 hk using fun x : Ω => exists_pos_pow_apply_eq σ x (hint x)
  refine ⟨∏ x ∈ s, k x, Finset.prod_pos fun x _ => hk0 x, fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem k hx
  rw [hc, pow_mul]
  exact pow_apply_eq_of_apply_eq _ x (hk x) c

end GlobalTheory.PowFix
end

section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

theorem GlobalTheory.stab_finset_eq_stab_primitive : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (s : Finset Ω), ∃ β : Ω, ∀ σ : G E Ω, σ β = β ↔ ∀ x ∈ s, σ x = x := by
  intro E Ω _ _ _ _ _ s
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  set K := IntermediateField.adjoin E (s : Set Ω) with hK
  haveI : FiniteDimensional E K :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  obtain ⟨α, hα⟩ := Field.exists_primitive_element E K
  refine ⟨(α : Ω), fun σ => ?_⟩
  have key : IntermediateField.adjoin E {(α : Ω)} = K := by
    have h1 := congrArg (IntermediateField.map K.val) hα
    rw [IntermediateField.adjoin_map] at h1
    have hm : IntermediateField.map K.val ⊤ = K := by
      ext y; constructor
      · rintro ⟨z, -, rfl⟩; exact z.2
      · intro hy; exact ⟨⟨y, hy⟩, trivial, rfl⟩
    rw [hm] at h1
    simpa [Set.image_singleton] using h1

  have gen : ∀ (T : Set Ω), (∀ x ∈ T, σ x = x) → ∀ y ∈ IntermediateField.adjoin E T, σ y = y := by
    intro T hT y hy
    have := IntermediateField.algHom_ext_of_eq_adjoin E (S := IntermediateField.adjoin E T) (s := T) rfl
      (φ₁ := ((σ : Ω →ₐ[E] Ω)).comp (IntermediateField.adjoin E T).val)
      (φ₂ := (IntermediateField.adjoin E T).val) (fun x hx => by simp [hT x hx])
    exact congrArg (fun φ => φ ⟨y, hy⟩) this
  constructor
  · intro h x hx
    have hxK : x ∈ IntermediateField.adjoin E {(α : Ω)} := by
      rw [key]; exact IntermediateField.subset_adjoin E _ hx
    exact gen {(α : Ω)} (by simpa using h) x hxK
  · intro h
    exact gen (s : Set Ω) (fun x hx => h x hx) (α : Ω) α.2
end

section

noncomputable section

namespace GlobalTheory.MeetsGen

def pU {K G : Type} [Field K] [Group G] (U : Subgroup G) [Fintype U] (f : U → K) : MonoidAlgebra K G :=
  ∑ u : U, MonoidAlgebra.single (u : G) ((Fintype.card U : K)⁻¹ * f u)

def cU {K G : Type} [Field K] [Group G] [Fintype G] (U : Subgroup G) [Fintype U] (f : U → K) : MonoidAlgebra K G :=
  ∑ g : G, MonoidAlgebra.single g (1 : K) * pU U f * MonoidAlgebra.single g⁻¹ (1 : K)

def uElt {K G : Type} [Field K] [Group G] [Fintype G] (U : Subgroup G) [Fintype U] (f : U → K) (e : MonoidAlgebra K G) :
    MonoidAlgebra K G :=
  cU U f * e + (1 - e)

theorem uup_eq_one_of_le_one {ι : Type} [Fintype ι] (p : ι → ℕ) (r : ℕ) (hr : r ≤ 1) (u : Formalism.L2.NX.GProd p r)
    (hu : u ∈ Formalism.L2.NX.Uup p r) : u = 1 := by
  funext x
  apply Units.ext
  ext a c
  have ha : a = c := Fin.ext (by have := a.2; have := c.2; omega)
  subst ha
  simp only [Pi.one_apply, Units.val_one, Matrix.one_apply_eq]
  exact ((Formalism.L2.NX.mem_Uup).1 hu x).2 a

theorem map_uElt {E L G : Type} [Field E] [Field L] [Group G] [Fintype G] (j : E →+* L) (U : Subgroup G) [Fintype U]
    (f : U → E) (e : MonoidAlgebra E G) :
    MonoidAlgebra.mapRingHom G j (uElt U f e) = uElt U (fun u => j (f u)) (MonoidAlgebra.mapRingHom G j e) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [uElt, cU, pU, map_add (f := _), map_mul, map_sub, map_one, map_sum, MonoidAlgebra.mapRingHom_single, map_inv₀,
    map_natCast]

theorem eq_sum_of_uElt_mul {K G : Type} [Field K] [Group G] [Fintype G] (U : Subgroup G) [Fintype U] (f : U → K)
    (e v : MonoidAlgebra K G) (hI : e * e = e) (hC : ∀ a, e * a = a * e) (hv : uElt U f e * v = 1) :
    e = ∑ g : G, MonoidAlgebra.single g (1 : K) * pU U f * (MonoidAlgebra.single g⁻¹ (1 : K) * e * v) := by
  have h1 : e * uElt U f e = cU U f * e := by
    simp only [uElt]
    rw [mul_add, mul_sub, mul_one, hI, sub_self, add_zero, ← mul_assoc, hC (cU U f), mul_assoc, hI]
  calc e = e * (uElt U f e * v) := by rw [hv, mul_one]
    _ = cU U f * e * v := by rw [← mul_assoc, h1]
    _ = _ := by
      simp only [cU, Finset.sum_mul]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [mul_assoc]

end GlobalTheory.MeetsGen

end
end

section

namespace GlobalTheory.RootsOfUnityClose

theorem geom_sum_close {K : Type*} [NormedField K] [IsUltrametricDist K] {z : K}
    (hz : ‖z - 1‖ < 1) (n : ℕ) :
    ‖z ^ n - 1‖ < 1 ∧ ‖(∑ i ∈ Finset.range n, z ^ i) - (n : K)‖ < 1 := by
  have hz1 : ‖z‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (z - 1) 1
    rw [sub_add_cancel, norm_one] at h
    exact h.trans (max_le hz.le le_rfl)
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    constructor
    · have e : z ^ (n + 1) - 1 = z * (z ^ n - 1) + (z - 1) := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ hz)
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hz1).trans_lt h1
    · have e : (∑ i ∈ Finset.range (n + 1), z ^ i) - ((n + 1 : ℕ) : K)
          = ((∑ i ∈ Finset.range n, z ^ i) - (n : K)) + (z ^ n - 1) := by
        rw [Finset.sum_range_succ]; push_cast; ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h2 h1)

theorem norm_natCast_eq_one {l : ℕ} [Fact l.Prime] {m : ℕ} (h : ¬ l ∣ m) :
    ‖(m : PadicAlgCl l)‖ = 1 := by
  have e : (m : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (m : ℚ_[l]) := by simp
  rw [e, norm_algebraMap']
  exact Padic.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h)

theorem eq_of_pow_eq_one_of_norm_sub_lt_one {l : ℕ} [Fact l.Prime] {m : ℕ} (hm : 0 < m)
    (hl : ¬ l ∣ m) {a b : Formalism.BasicNotions.Loc.Om l} (ha : a ^ m = 1) (hb : b ^ m = 1)
    (hab : ‖a - b‖ < 1) : a = b := by
  have hb1 : ‖b‖ = 1 := by
    have h : ‖b‖ ^ m = 1 := by rw [← norm_pow, hb, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').mp h
  have hb0 : b ≠ 0 := by
    intro h; rw [h, norm_zero] at hb1; exact zero_ne_one hb1
  have hz : ‖a / b - 1‖ < 1 := by
    rw [div_sub_one hb0, norm_div, hb1, div_one]; exact hab
  have hzm : (a / b) ^ m = 1 := by rw [div_pow, ha, hb, div_one]
  by_contra hne
  have hne1 : a / b - 1 ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    exact hne ((div_eq_one_iff_eq hb0).mp h)
  have hs : (∑ i ∈ Finset.range m, (a / b) ^ i) = 0 := by
    have h := geom_sum_mul (a / b) m
    rw [hzm, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right hne1
  have h := (geom_sum_close hz m).2
  rw [hs, zero_sub, norm_neg, norm_natCast_eq_one hl] at h
  exact lt_irrefl _ h

end GlobalTheory.RootsOfUnityClose
end

section

namespace GlobalTheory.NL.Coker

open Formalism.BasicNotions

variable {O : Type} [CommRing O] {n : ℕ} {M : Type} [AddCommGroup M] [Module (LetA O n) M]

def satM (p : ℕ) (P N : Submodule (LetA O n) M) : Submodule (LetA O n) M where
  carrier := {x | x ∈ N ∧ ∃ k : ℕ, ((p : LetA O n)) ^ k • x ∈ P ∧ (letπ : LetA O n) ^ k • x ∈ P}
  add_mem' := by
    rintro x y ⟨hx, k, hk1, hk2⟩ ⟨hy, j, hj1, hj2⟩
    refine ⟨N.add_mem hx hy, k + j, ?_, ?_⟩
    · rw [smul_add, pow_add]
      refine P.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact P.smul_mem _ hk1
      · rw [mul_smul]; exact P.smul_mem _ hj1
    · rw [smul_add, pow_add]
      refine P.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact P.smul_mem _ hk2
      · rw [mul_smul]; exact P.smul_mem _ hj2
  zero_mem' := ⟨N.zero_mem, 0, by simp, by simp⟩
  smul_mem' := by
    rintro a x ⟨hx, k, hk1, hk2⟩
    refine ⟨N.smul_mem a hx, k, ?_, ?_⟩
    · rw [smul_comm]; exact P.smul_mem a hk1
    · rw [smul_comm]; exact P.smul_mem a hk2

theorem satM_le (p : ℕ) (P N : Submodule (LetA O n) M) : satM p P N ≤ N := fun _ hx => hx.1

theorem le_satM (p : ℕ) {P N : Submodule (LetA O n) M} (h : P ≤ N) : P ≤ satM p P N :=
  fun x hx => ⟨h hx, 0, by simpa using hx, by simpa using hx⟩

theorem mem_satM_of_smul {p : ℕ} {P N : Submodule (LetA O n) M} {x : M} (hx : x ∈ N)
    (h1 : ((p : LetA O n)) • x ∈ satM p P N) (h2 : (letπ : LetA O n) • x ∈ satM p P N) :
    x ∈ satM p P N := by
  obtain ⟨-, k, hk1, -⟩ := h1
  obtain ⟨-, j, -, hj2⟩ := h2
  refine ⟨hx, k + j + 1, ?_, ?_⟩
  · have : ((p : LetA O n)) ^ (k + j + 1) • x = ((p : LetA O n)) ^ j • (((p : LetA O n)) ^ k • ((p : LetA O n)) • x) := by
      rw [smul_smul, smul_smul]; congr 1; ring
    rw [this]; exact P.smul_mem _ hk1
  · have : (letπ : LetA O n) ^ (k + j + 1) • x = (letπ : LetA O n) ^ k • ((letπ : LetA O n) ^ j • (letπ : LetA O n) • x) := by
      rw [smul_smul, smul_smul]; congr 1; ring
    rw [this]; exact P.smul_mem _ hj2

theorem uniform {p : ℕ} {P N : Submodule (LetA O n) M} (hN : N.FG) (h : N ≤ satM p P N) :
    ∃ c : ℕ, ∀ z ∈ N, ((p : LetA O n)) ^ c • z ∈ P ∧ (letπ : LetA O n) ^ c • z ∈ P := by
  classical
  obtain ⟨G, rfl⟩ := hN
  have hk : ∀ x ∈ G, ∃ k : ℕ, ((p : LetA O n)) ^ k • x ∈ P ∧ (letπ : LetA O n) ^ k • x ∈ P :=
    fun x hx => (h (Submodule.subset_span hx)).2
  choose! k hk using hk
  refine ⟨G.sup k, fun z hz => ?_⟩
  induction hz using Submodule.span_induction with
  | mem x hx =>
    have hle : k x ≤ G.sup k := Finset.le_sup hx
    obtain ⟨h1, h2⟩ := hk x hx
    constructor
    · rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]; exact P.smul_mem _ h1
    · rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]; exact P.smul_mem _ h2
  | zero => simp
  | add x y _ _ hx hy =>
    exact ⟨by rw [smul_add]; exact P.add_mem hx.1 hy.1, by rw [smul_add]; exact P.add_mem hx.2 hy.2⟩
  | smul a x _ hx =>
    exact ⟨by rw [smul_comm]; exact P.smul_mem a hx.1, by rw [smul_comm]; exact P.smul_mem a hx.2⟩

end GlobalTheory.NL.Coker
end

section

namespace GlobalTheory.IntegerRingPowers

open Formalism.BasicNotions

theorem exists_pow_smul_mem_OL {l : ℕ} [Fact (Nat.Prime l)] (LL : Loc.FinExt l) (a : ↥LL.1) :
    ∃ n : ℕ, (l : ↥LL.1) ^ n * a ∈ Loc.OL LL := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have hint : IsIntegral ℚ_[l] a := IsIntegral.of_finite ℚ_[l] a
  obtain ⟨⟨m, hm⟩, hmi⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors ℤ_[l]) a hint
  have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
  refine ⟨m.valuation, ?_⟩
  rw [Loc.OL, mem_integralClosure_iff]
  have hmi' : IsIntegral ℤ_[l] (m • a) := hmi
  have e := PadicInt.unitCoeff_spec hm0
  set u := PadicInt.unitCoeff hm0
  have key : (l : ↥LL.1) ^ m.valuation * a = ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • (m • a) := by
    conv_rhs => rw [e]
    rw [smul_smul, ← mul_assoc, Units.inv_mul, one_mul, Algebra.smul_def, map_pow, map_natCast]
  rw [key]
  exact IsIntegral.smul _ hmi'

theorem smul_mem_of_mem_OL {l : ℕ} [Fact (Nat.Prime l)] {K LL : Loc.FinExt l}
    (T : LocLat ↥(Loc.GK K) ℚ_[l] ↥LL.1 ↥(Loc.OL LL)) {c : ↥LL.1} (hc : c ∈ Loc.OL LL)
    {w : T.V} (hw : w ∈ T.L.T) : c • w ∈ T.L.T := by
  have h := T.L.T.smul_mem (⟨c, hc⟩ : ↥(Loc.OL LL)) hw
  have e := T.towO.smul_assoc (⟨c, hc⟩ : ↥(Loc.OL LL)) (1 : ↥LL.1) w
  have e2 : ((⟨c, hc⟩ : ↥(Loc.OL LL)) • (1 : ↥LL.1)) = c := by
    rw [Algebra.smul_def, mul_one]; rfl
  rw [e2, one_smul] at e
  rw [e]; exact h

theorem natCast_pow_mem_OL {l : ℕ} [Fact (Nat.Prime l)] (LL : Loc.FinExt l) (k : ℕ) :
    (l : ↥LL.1) ^ k ∈ Loc.OL LL :=
  (Loc.OL LL).pow_mem ((Loc.OL LL).natCast_mem l) k

theorem pow_smul_smul_eq {l : ℕ} [Fact (Nat.Prime l)] {K LL : Loc.FinExt l}
    (T : LocLat ↥(Loc.GK K) ℚ_[l] ↥LL.1 ↥(Loc.OL LL)) (a : ↥LL.1) (x : T.V) (k n : ℕ) :
    (l : ↥LL.1) ^ (k + n) • a • x = ((l : ↥LL.1) ^ k * a) • ((l : ↥LL.1) ^ n • x) := by
  rw [pow_add, mul_smul, mul_smul]
  congr 1
  rw [← mul_smul, ← mul_smul, mul_comm]

theorem main : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (K LL : Formalism.BasicNotions.Loc.FinExt l)
    (T : Formalism.BasicNotions.LocLat ↥(Formalism.BasicNotions.Loc.GK K) ℚ_[l]
      ↥(↑LL : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↥(Formalism.BasicNotions.Loc.OL LL))
    (v : Formalism.BasicNotions.LocLat.V T),
    ∃ (n : ℕ), (↑l : ↥(↑LL : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l))) ^ n • v ∈
      Formalism.WeaklyAdmissibleFiltrations.Lattice.T (Formalism.BasicNotions.LocLat.L T) := by
  intro l _ K LL T v
  have hv : v ∈ Submodule.span ↥LL.1 (T.L.T : Set T.V) := by
    rw [T.L.span]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by rw [pow_zero, one_smul]; exact hx⟩
  | zero => exact ⟨0, by rw [smul_zero]; exact T.L.T.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨k, hk⟩ := hy
    refine ⟨n + k, ?_⟩
    rw [smul_add]
    refine T.L.T.add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]
      exact smul_mem_of_mem_OL T (natCast_pow_mem_OL LL k) hn
    · rw [pow_add, mul_smul]
      exact smul_mem_of_mem_OL T (natCast_pow_mem_OL LL n) hk
  | smul a x _ hx =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨k, hk⟩ := exists_pow_smul_mem_OL LL a
    refine ⟨k + n, ?_⟩
    rw [pow_smul_smul_eq T a x k n]
    exact smul_mem_of_mem_OL T hk hn

end GlobalTheory.IntegerRingPowers
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.LocIota

theorem ιB_algebraMap_Kur {l : ℕ} [Fact l.Prime] (P : LocPrime l) (c : ↥(MaximalUnramifiedExtension l)) :
    P.ιB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap (Om l) P.R.BdR (c : Om l) := by
  have hint : IsIntegral ℚ_[l] (c : Om l) := Algebra.IsIntegral.isIntegral _
  obtain ⟨K, hc⟩ : ∃ K : FinExt l, (c : Om l) ∈ K0 K :=
    ⟨⟨IntermediateField.adjoin ℚ_[l] {(c : Om l)},
      IntermediateField.adjoin.finiteDimensional hint⟩,
      IntermediateField.mem_adjoin_simple_self ℚ_[l] (c : Om l), c.2⟩
  have h := (P.PD K).ι.commutes (⟨c, hc⟩ : ↥(K0 K))
  rw [P.PD_ι] at h
  exact h

end GlobalTheory.LocIota
end
