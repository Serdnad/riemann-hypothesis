module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle017
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwMemIwC
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
import Mathlib.RingTheory.PiTensorProduct
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

@[expose] public section

section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem unif_lt {x : kˣ} (hx : IsUnif x) (y : k) :
    valuation k y < 1 ↔ valuation k y ≤ valuation k (x : k) := by
  obtain ⟨p, hp, e⟩ := hx
  have hI := Valuation.integer.integers (valuation k)
  have h1 : valuation k (x : k) < 1 := by
    rw [← e]
    refine lt_of_le_of_ne p.2 fun h => hp.not_isUnit (hI.isUnit_iff_valuation_eq_one.2 h)
  refine ⟨fun h => ?_, fun h => h.trans_lt h1⟩
  let z : 𝒪[k] := ⟨y, h.le⟩
  have hz : z ∈ IsLocalRing.maximalIdeal 𝒪[k] := fun hu => h.ne (hI.isUnit_iff_valuation_eq_one.1 hu)
  rw [hp.maximalIdeal_eq, Ideal.mem_span_singleton] at hz
  rw [← e]
  exact hI.le_of_dvd hz

private def Bd (x : kˣ) (g : GL (Fin n) k) : Prop :=
  ∀ i j, valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ valuation k (x : k) ^ (if j < i then 1 else 0 : ℤ)

private theorem mem_iw_iff {x : kˣ} (hx : IsUnif x) (g : GL (Fin n) k) :
    g ∈ iwahori k (Fin n) ↔ Bd x g ∧ Bd x g⁻¹ := by
  have h1 : valuation k (x : k) ≤ 1 := ((unif_lt hx x).2 le_rfl).le
  have A : ∀ g ∈ iwahori k (Fin n), Bd x g := by
    intro g hg i j
    have hg' := mem_iwahori.1 hg
    split_ifs with h
    · simpa using (unif_lt hx _).1 (hg'.2 i j h)
    · rw [zpow_zero]
      exact ((GlobalTheory.SplitFlip.mem_KO_iff g).1 hg'.1).1 i j
  have B : ∀ g : GL (Fin n) k, Bd x g → ∀ i j, valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
    intro g hg i j
    have := hg i j
    split_ifs at this with h
    · exact le_trans (by simpa using this) h1
    · simpa using this
  refine ⟨fun hg => ⟨A g hg, A _ (inv_mem hg)⟩, fun ⟨ha, hb⟩ => mem_iwahori.2
    ⟨(GlobalTheory.SplitFlip.mem_KO_iff g).2 ⟨B _ ha, B _ hb⟩, fun i j h => (unif_lt hx _).2 ?_⟩⟩
  simpa [h] using ha i j

private theorem conj_entry (x : kˣ) (a : Fin n → ℤ) (w : Equiv.Perm (Fin n)) (g : GL (Fin n) k) (i j : Fin n) :
    ((pm k n w * pw x a * g * (pm k n w * pw x a)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (w i) (w j) =
      (x : k) ^ (a i - a j) * (g : Matrix (Fin n) (Fin n) k) i j := by
  have e : pm k n w * pw x a * g * (pm k n w * pw x a)⁻¹ =
      pm k n w * (pw x a * g * diagT k (Fin n) (fun i => x ^ a i)⁻¹) * pm k n w⁻¹ := by
    rw [map_inv, map_inv, pw]; group
  rw [e]
  simp only [Units.val_mul, pw, val_diagT]
  generalize hM : (diagonal (fun i => ((x ^ a i : kˣ) : k)) * (g : Matrix (Fin n) (Fin n) k) *
    diagonal fun i => (((fun i => x ^ a i)⁻¹ i : kˣ) : k)) = M
  have hM' : M i j = (x : k) ^ (a i - a j) * (g : Matrix (Fin n) (Fin n) k) i j := by
    rw [← hM, mul_diagonal, diagonal_mul, zpow_sub₀ x.ne_zero]
    simp only [Pi.inv_apply, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val]
    ring
  rw [← hM']
  simp only [Matrix.mul_apply, pm_apply]
  simp

private theorem bd_conj (x : kˣ) (a : Fin n → ℤ) (w : Equiv.Perm (Fin n))
    (hw : ∀ i j, (if w j < w i then 1 else 0 : ℤ) = (a i - a j) + (if j < i then 1 else 0)) (g : GL (Fin n) k) :
    Bd x (pm k n w * pw x a * g * (pm k n w * pw x a)⁻¹) ↔ Bd x g := by
  have h0 : 0 < valuation k (x : k) := zero_lt_iff.2 (by simp)
  unfold Bd
  rw [w.surjective.forall₂]
  refine forall₂_congr fun i j => ?_
  rw [conj_entry, hw, map_mul, map_zpow₀, zpow_add₀ h0.ne', mul_le_mul_iff_right₀ (zpow_pos h0 _)]

private theorem exists_rot (n m : ℕ) (hm : m ≤ n) : ∃ w : Equiv.Perm (Fin n),
    ∀ i j, (if w j < w i then 1 else 0 : ℤ) = (fund n m i - fund n m j) + (if j < i then 1 else 0) := by
  let f : Fin n → Fin n := fun i => ⟨if (i : ℕ) < m then n - m + i else i - m, by
    have := i.2; split_ifs <;> omega⟩
  have hf : Function.Injective f := by
    intro i j h
    have h' := congrArg Fin.val h
    have := i.2; have := j.2
    simp only [f] at h'
    ext
    split_ifs at h' <;> omega
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf), fun i j => ?_⟩
  have := i.2; have := j.2
  simp only [Equiv.ofBijective_apply, f, fund, Fin.lt_def]
  split_ifs <;> omega

end SlopeTestRemainingChoices

theorem UpperTheory.V.AlgebraTools.fundNorm :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (x : kˣ), IsUnif x → ∀ m ≤ n, ∃ w : Equiv.Perm (Fin n), pm k n w * pw x (fund n m) ∈ Subgroup.normalizer (iwC k n C : Set (GL (Fin n) k)) := by
  intro k _ _ _ _ n C x hx m hm
  obtain ⟨w, hw⟩ := exists_rot n m hm
  refine ⟨w, Subgroup.mem_normalizer_iff.2 fun g => ?_⟩
  have e : (pm k n w * pw x (fund n m) * g * (pm k n w * pw x (fund n m))⁻¹)⁻¹ =
      pm k n w * pw x (fund n m) * g⁻¹ * (pm k n w * pw x (fund n m))⁻¹ := by group
  rw [(memIwC k n C).1, (memIwC k n C).1, mem_iw_iff hx, mem_iw_iff hx, e, bd_conj x _ w hw, bd_conj x _ w hw]
  refine and_congr Iff.rfl ?_
  conv_rhs => rw [w.surjective.forall]
  simp only [conj_entry, sub_self, zpow_zero, one_mul]
end

section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

section SlopeTestRemainingChoices

private noncomputable def elem {R : Type} [CommRing R] {n : ℕ} {i j : Fin n} (h : i ≠ j) (a : R) : GL (Fin n) R :=
  ⟨1 + single i j a, 1 - single i j a,
    by simp [add_mul, mul_sub, single_mul_single_of_ne _ _ _ _ h.symm],
    by simp [sub_mul, mul_add, single_mul_single_of_ne _ _ _ _ h.symm]⟩

private theorem conj_apply {R : Type} [CommRing R] {n : ℕ} (w : Equiv.Perm (Fin n)) (g : GL (Fin n) R) (a b : Fin n) :
    (((pm R n w)⁻¹ * g * pm R n w : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b
      = (g : Matrix (Fin n) (Fin n) R) (w a) (w b) := by
  rw [← map_inv]
  simp only [Units.val_mul, Matrix.mul_apply, pm_apply, Equiv.Perm.eq_inv_iff_eq]
  simp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem res_zero (x : 𝒪[k]) : IsLocalRing.residue 𝒪[k] x = 0 ↔ valuation k (algebraMap 𝒪[k] k x) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => h.ne⟩

private theorem pm_KO (w : Equiv.Perm (Fin n)) : pm k n w ∈ KO k (Fin n) := by
  refine ⟨pm 𝒪[k] n w, ?_⟩
  ext a b
  show algebraMap 𝒪[k] k ((pm 𝒪[k] n w : Matrix (Fin n) (Fin n) 𝒪[k]) a b) = _
  rw [pm_apply, pm_apply]
  split_ifs <;> simp

private theorem conj_mem {C : Subgroup 𝓀[k]ˣ} {i j : Fin n} (hij : (j : ℕ) = i + 1) {g : GL (Fin n) k}
    (hg : g ∈ iwC k n C) :
    (pm k n (Equiv.swap i j))⁻¹ * g * pm k n (Equiv.swap i j) ∈ iwC k n C ↔
      valuation k ((g : Matrix (Fin n) (Fin n) k) i j) < 1 := by
  have hm := (memIwC k n C).1
  obtain ⟨h1, h2⟩ := (hm g).1 hg
  obtain ⟨h3, h4⟩ := mem_iwahori.1 h1
  have hlt : i < j := by rw [Fin.lt_def]; omega
  constructor
  · intro h
    have := (mem_iwahori.1 ((hm _).1 h).1).2 j i hlt
    rwa [conj_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] at this
  · intro h
    refine (hm _).2 ⟨mem_iwahori.2 ⟨mul_mem (mul_mem (inv_mem (pm_KO _)) h3) (pm_KO _), fun a b hab => ?_⟩,
      fun a => ?_⟩
    · rw [conj_apply]
      by_cases hc : a = j ∧ b = i
      · rwa [hc.1, hc.2, Equiv.swap_apply_left, Equiv.swap_apply_right]
      · apply h4
        simp only [Equiv.swap_apply_def]
        simp only [Fin.ext_iff, Fin.lt_def] at *
        split_ifs <;> omega
    · rw [conj_apply]
      exact h2 _

private theorem pick {C : Subgroup 𝓀[k]ˣ} {g : GL (Fin n) k} (hg : g ∈ iwC k n C)
    {r : 𝓀[k] → 𝒪[k]} (hr : ∀ c, IsLocalRing.residue 𝒪[k] (r c) = c) (a i j : Fin n) :
    ∃ c, valuation k ((g : Matrix (Fin n) (Fin n) k) i j
      - algebraMap 𝒪[k] k (r c) * (g : Matrix (Fin n) (Fin n) k) a a) < 1 := by
  obtain ⟨h1, h2⟩ := ((memIwC k n C).1 g).1 hg
  obtain ⟨_, ⟨u, -, rfl⟩, hu⟩ := h2 a
  obtain ⟨h, rfl⟩ := (mem_iwahori.1 h1).1
  refine ⟨IsLocalRing.residue 𝒪[k] ((h : Matrix (Fin n) (Fin n) 𝒪[k]) i j * (u⁻¹ : 𝒪[k]ˣ)), ?_⟩
  rw [← hu]
  have := (res_zero ((h : Matrix (Fin n) (Fin n) 𝒪[k]) i j -
    r (IsLocalRing.residue 𝒪[k] ((h : Matrix (Fin n) (Fin n) 𝒪[k]) i j * (u⁻¹ : 𝒪[k]ˣ))) * (u : 𝒪[k]))).1 (by
      rw [map_sub, map_mul, hr, ← map_mul, Units.inv_mul_cancel_right, sub_self])
  rw [map_sub, map_mul] at this
  exact this

private theorem elem_mem {i j : Fin n} (h : i < j) (a : 𝒪[k]) :
    elem h.ne (algebraMap 𝒪[k] k a) ∈ unipO k n := by
  refine ⟨mem_unipRad.2 ⟨mem_parab_iff.2 fun a b _ _ hab => ?_, fun a _ _ => ?_⟩, elem h.ne a, ?_⟩
  · show (1 + single i j _ : Matrix (Fin n) (Fin n) k) a b = 0
    have : ¬ (i = a ∧ j = b) := by
      rintro ⟨rfl, rfl⟩
      exact absurd hab h.asymm
    simp [one_apply_ne hab.ne', single_apply, this]
  · show (1 + single i j _ : Matrix (Fin n) (Fin n) k) a a = _
    have : ¬ (i = a ∧ j = a) := by
      rintro ⟨rfl, rfl⟩
      exact h.ne rfl
    simp [single_apply, this]
  · ext p q
    show algebraMap 𝒪[k] k ((1 + single i j a : Matrix (Fin n) (Fin n) 𝒪[k]) p q) =
      (1 + single i j _ : Matrix (Fin n) (Fin n) k) p q
    simp only [Matrix.add_apply, Matrix.one_apply, single_apply, map_add (f := _)]
    split_ifs <;> simp

end SlopeTestRemainingChoices

theorem UpperTheory.V.AlgebraTools.simpleOrbit :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (i j : Fin n), (j : ℕ) = i + 1 → ∀ (r : 𝓀[k] → 𝒪[k]), (∀ c, IsLocalRing.residue 𝒪[k] (r c) = c) → ∃ x : 𝓀[k] → GL (Fin n) k, (∀ c, (x c : Matrix (Fin n) (Fin n) k) = 1 + Matrix.single i j (algebraMap 𝒪[k] k (r c))) ∧ (∀ c, x c ∈ unipO k n) ∧ (∀ q : GL (Fin n) k ⧸ iwC k n C, q ∈ MulAction.orbit (iwC k n C) ((pm k n (Equiv.swap i j) : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C) ↔ ∃! c, ((x c * pm k n (Equiv.swap i j) : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C) = q) ∧ ∀ g ∈ iwC k n C, ∃ c, ∃ b ∈ iwC k n C, pm k n (Equiv.swap i j) * g = b * (pm k n (Equiv.swap i j) * x c) := by
  intro k _ _ _ _ n C i j hij r hr
  have hlt : i < j := by rw [Fin.lt_def]; omega
  have hle : unipO k n ≤ iwC k n C := le_sup_of_le_left le_sup_right
  have hx : ∀ c, elem hlt.ne (algebraMap 𝒪[k] k (r c)) ∈ iwC k n C := fun c => hle (elem_mem hlt _)
  have hL : ∀ (a : k) (g : GL (Fin n) k), (((elem hlt.ne a)⁻¹ * g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j
      = (g : Matrix (Fin n) (Fin n) k) i j - a * (g : Matrix (Fin n) (Fin n) k) j j := by
    intro a g
    show ((1 - single i j a) * (g : Matrix (Fin n) (Fin n) k)) i j = _
    simp [sub_mul]
  have hR : ∀ (a : k) (g : GL (Fin n) k), ((g * (elem hlt.ne a)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j
      = (g : Matrix (Fin n) (Fin n) k) i j - a * (g : Matrix (Fin n) (Fin n) k) i i := by
    intro a g
    show ((g : Matrix (Fin n) (Fin n) k) * (1 - single i j a)) i j = _
    simp [mul_sub, mul_comm]
  have hs : (pm k n (Equiv.swap i j))⁻¹ = pm k n (Equiv.swap i j) := by rw [← map_inv, Equiv.swap_inv]
  refine ⟨fun c => elem hlt.ne (algebraMap 𝒪[k] k (r c)), fun c => rfl, fun c => elem_mem hlt _, fun q => ?_,
    fun g hg => ?_⟩
  · constructor
    · rintro ⟨⟨g, hg⟩, rfl⟩
      obtain ⟨c, hc⟩ := pick hg hr j i j
      have h1 : ((elem hlt.ne (algebraMap 𝒪[k] k (r c)) * pm k n (Equiv.swap i j) : GL (Fin n) k) :
          GL (Fin n) k ⧸ iwC k n C) = ((g * pm k n (Equiv.swap i j) : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C) := by
        rw [QuotientGroup.eq, _root_.mul_inv_rev, mul_assoc, ← mul_assoc _ g, ← mul_assoc]
        exact (conj_mem hij (mul_mem (inv_mem (hx c)) hg)).2 (by rwa [hL])
      refine ⟨c, h1, fun d hd => ?_⟩
      have h2 := h1.trans (Eq.symm hd)
      rw [QuotientGroup.eq, _root_.mul_inv_rev, mul_assoc, ← mul_assoc _ (elem _ _), ← mul_assoc,
        conj_mem hij (mul_mem (inv_mem (hx c)) (hx d)), hL] at h2
      have h3 : valuation k (algebraMap 𝒪[k] k (r d - r c)) < 1 := by
        convert h2 using 2
        simp [elem, one_apply_ne hlt.ne, single_apply, hlt.ne]
      have h4 := (res_zero _).2 h3
      rwa [map_sub, hr, hr, sub_eq_zero] at h4
    · rintro ⟨c, rfl, -⟩
      exact ⟨⟨_, hx c⟩, rfl⟩
  · obtain ⟨c, hc⟩ := pick hg hr i i j
    refine ⟨c, _, (conj_mem hij (mul_mem hg (inv_mem (hx c)))).2 (by rwa [hR]), ?_⟩
    rw [mul_assoc, ← mul_assoc (pm k n _) (pm k n _), ← map_mul, Equiv.swap_mul_self, map_one, one_mul, hs,
      mul_assoc, inv_mul_cancel_right]
end
