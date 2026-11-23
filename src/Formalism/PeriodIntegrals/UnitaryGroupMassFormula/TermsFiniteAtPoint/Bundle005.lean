module

public import Formalism.LocalRingCardinality.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.HeisOpHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.Bundle004
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

section

noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW.LeviW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.TermsAtPtFiniteW.HeisW

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def psiF (e f : Fin r → S.V) (U U' : Matrix (Fin r) (Fin r) E) : S.V →ₗ[E] S.V :=
  LinearMap.id + ∑ a, (S.hT (f a)).smulRight (∑ c, U c a • e c - e a) +
    ∑ a, (S.hT (e a)).smulRight (∑ c, U' c a • f c - f a)

theorem psiF_apply (e f : Fin r → S.V) (U U' : Matrix (Fin r) (Fin r) E) (v : S.V) :
    psiF e f U U' v = v + ∑ a, S.hT (f a) v • (∑ c, U c a • e c - e a) +
      ∑ a, S.hT (e a) v • (∑ c, U' c a • f c - f a) := by
  simp [psiF, LinearMap.sum_apply]

def wv (e f : Fin r → S.V) (v : S.V) : S.V :=
  v - ∑ a, S.hT (f a) v • e a - ∑ a, S.hT (e a) v • f a

theorem psiF_eq (e f : Fin r → S.V) (U U' : Matrix (Fin r) (Fin r) E) (v : S.V) :
    psiF e f U U' v = wv e f v + ∑ a, S.hT (f a) v • ∑ c, U c a • e c +
      ∑ a, S.hT (e a) v • ∑ c, U' c a • f c := by
  rw [psiF_apply, wv]
  simp only [smul_sub, Finset.sum_sub_distrib]
  abel

section Pair

variable (e f : Fin r → S.V) (hee : ∀ a b, S.hT (e a) (e b) = 0) (hff : ∀ a b, S.hT (f a) (f b) = 0)
  (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0)

include hef in
theorem hfe (a b : Fin r) : S.hT (f a) (e b) = if a = b then 1 else 0 := by
  rw [← hsym, hef]
  by_cases h : a = b
  · subst h; simp
  · simp [h, Ne.symm h]

include hee hef in
theorem e_w (c : Fin r) (v : S.V) : S.hT (e c) (wv e f v) = 0 := by
  simp [wv, hee, hef]

include hff hef in
theorem f_w (c : Fin r) (v : S.V) : S.hT (f c) (wv e f v) = 0 := by
  simp [wv, hff, hfe e f hef]

theorem algδ (p q : Fin r → E) (u w : Matrix (Fin r) (Fin r) E)
    (h : ∀ a b, ∑ c, u c a * w c b = if a = b then 1 else 0) :
    ∑ a, p a * ∑ c, u c a * ∑ b, q b * w c b = ∑ a, p a * q a := by
  have key : ∀ a, ∑ c, u c a * ∑ b, q b * w c b = q a := by
    intro a
    calc ∑ c, u c a * ∑ b, q b * w c b = ∑ b, q b * ∑ c, u c a * w c b := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      _ = q a := by simp [h]
  simp only [key]

include hee hff hef in
theorem gram (U U' : Matrix (Fin r) (Fin r) E) (hUU : ∀ a b, ∑ c, star (U c a) * U' c b = if a = b then 1 else 0)
    (x y : S.V) :
    S.hT (psiF e f U U' x) (psiF e f U U' y) = S.hT (wv e f x) (wv e f y) +
      ∑ a, star (S.hT (f a) x) * S.hT (e a) y + ∑ a, star (S.hT (e a) x) * S.hT (f a) y := by
  have hUU' : ∀ a b, ∑ c, star (U' c a) * U c b = if a = b then 1 else 0 := by
    intro a b
    have h1 : ∑ c, star (U' c a) * U c b = star (∑ c, star (U c b) * U' c a) := by
      simp only [star_sum, star_mul', star_star]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [h1, hUU b a]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  have pairR : ∀ (u : S.V) (s : Fin r → E) (t : Matrix (Fin r) (Fin r) E) (g : Fin r → S.V),
      S.hT u (∑ a, s a • ∑ c, t c a • g c) = ∑ a, s a * ∑ c, t c a * S.hT u (g c) := by
    intro u s t g

    simp [map_sum, smul_eq_mul]
  have pairL : ∀ (u : S.V) (s : Fin r → E) (t : Matrix (Fin r) (Fin r) E) (g : Fin r → S.V),
      S.hT (∑ a, s a • ∑ c, t c a • g c) u = ∑ a, star (s a) * ∑ c, star (t c a) * S.hT (g c) u := by
    intro u s t g

    simp [map_sum, LinearMap.sum_apply, smul_eq_mul, starRingEnd_apply]
  have hwe : ∀ (v : S.V) (c : Fin r), S.hT (wv e f v) (e c) = 0 := fun v c => by
    rw [← hsym, e_w e f hee hef c v, star_zero]
  have hwf : ∀ (v : S.V) (c : Fin r), S.hT (wv e f v) (f c) = 0 := fun v c => by
    rw [← hsym, f_w e f hff hef c v, star_zero]
  have hfe' := hfe e f hef
  have k1 : ∑ a, star (S.hT (f a) x) * ∑ c, star (U c a) * ∑ b, S.hT (e b) y * U' c b =
      ∑ a, star (S.hT (f a) x) * S.hT (e a) y :=
    algδ _ _ (fun c a => star (U c a)) U' hUU
  have k2 : ∑ a, star (S.hT (e a) x) * ∑ c, star (U' c a) * ∑ b, S.hT (f b) y * U c b =
      ∑ a, star (S.hT (e a) x) * S.hT (f a) y :=
    algδ _ _ (fun c a => star (U' c a)) U hUU'
  rw [psiF_eq, psiF_eq]
  simp only [map_add (f := _), LinearMap.add_apply]
  simp only [pairL]
  simp only [pairR]
  simp only [hwe, hwf, e_w e f hee hef, f_w e f hff hef, hee, hff, hef, hfe', mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, mul_ite, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  linear_combination k1 + k2

include hee hff hef in
theorem isom_psiF (U U' : Matrix (Fin r) (Fin r) E)
    (hUU : ∀ a b, ∑ c, star (U c a) * U' c b = if a = b then 1 else 0) (x y : S.V) :
    S.hT (psiF e f U U' x) (psiF e f U U' y) = S.hT x y := by
  rw [gram e f hee hff hef U U' hUU x y]
  have h1 : ∀ c, S.hT (wv e f x) (e c) = 0 := fun c => by
    rw [← hsym, e_w e f hee hef c x, star_zero]
  have h2 : ∀ c, S.hT (wv e f x) (f c) = 0 := fun c => by
    rw [← hsym, f_w e f hff hef c x, star_zero]
  have h3 : S.hT (wv e f x) (wv e f y) = S.hT (wv e f x) y := by
    rw [show wv e f y = y - ∑ a, S.hT (f a) y • e a - ∑ a, S.hT (e a) y • f a from rfl]
    simp [h1, h2]
  have h4 : S.hT (wv e f x) y = S.hT x y - ∑ a, star (S.hT (f a) x) * S.hT (e a) y -
      ∑ a, star (S.hT (e a) x) * S.hT (f a) y := by
    simp [wv, LinearMap.sum_apply, smul_eq_mul, starRingEnd_apply]
  rw [h3, h4]
  ring

include hef in
theorem psiF_e (U U' : Matrix (Fin r) (Fin r) E) (hee : ∀ a b, S.hT (e a) (e b) = 0) (j : Fin r) :
    psiF e f U U' (e j) = ∑ c, U c j • e c := by
  rw [psiF_apply]
  simp [hfe e f hef, hee] <;> abel

theorem psiF_fix (U U' : Matrix (Fin r) (Fin r) E) (v : S.V) (h1 : ∀ a, S.hT (f a) v = 0)
    (h2 : ∀ a, S.hT (e a) v = 0) : psiF e f U U' v = v := by
  rw [psiF_apply]
  simp [h1, h2]

end Pair

theorem gmap_of_isom (Λ : Submodule (𝓞 E) S.V) (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (n : S.V ≃ₗ[E] S.V)
    (hn : ∀ x y, S.hT (n x) (n y) = S.hT x y) (hΛ : ∀ v ∈ Λ, n v ∈ Λ) : Formalism.HermitianLatticesTheory.gmap n Λ = Λ := by
  unfold Formalism.HermitianLatticesTheory.gmap
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    intro w hw
    exact hΛ w hw
  · intro v hv
    rw [Submodule.mem_map]
    refine ⟨n.symm v, ?_, by simp⟩
    have hU' : Formalism.HermitianLatticesTheory.dual S.hT Λ = Λ := hU
    have h1 : v ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by rw [hU']; exact hv
    rw [← hU']
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.coe_restrictScalars] at h1 ⊢
    intro y hy
    have := h1 (n y) (hΛ y hy)
    rwa [← hn y (n.symm v), LinearEquiv.apply_symm_apply]

theorem inj_of_isom (g : S.V →ₗ[E] S.V) (hg : ∀ x y, S.hT (g x) (g y) = S.hT x y) : Function.Injective g := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  apply S.nondeg.1 x
  intro y
  rw [← hg x y, hx]
  simp

end PI.TermsAtPtFiniteW.LeviW
end
end

section

noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.Saturated

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ndS_mul_int (D : D7) (a : Fin D.R.rS) (t : D.host.E) (ht : t ∈ aaS D a) :
    ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * t := by
  have ha := a.isLt
  obtain ⟨m, hm⟩ : ∃ m : ℕ, D.R.rS = (a : ℕ) + m := ⟨D.R.rS - (a : ℕ), by omega⟩
  have haa : aaS D a = (((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ^ m : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹ := by
    unfold aaS ddS
    rw [FractionalIdeal.coeIdeal_pow, ← zpow_natCast, ← zpow_neg]
    congr 1
    omega
  rw [haa] at ht
  by_cases hJ : (((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ^ m : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = 0
  · rw [hJ] at ht
    have ht0 : t = 0 := by
      first
        | (rw [FractionalIdeal.inv_zero', FractionalIdeal.mem_zero_iff] at ht; exact ht)
        | (rw [inv_zero, FractionalIdeal.mem_zero_iff] at ht; exact ht)
    exact ⟨0, by rw [ht0, map_zero, mul_zero]⟩
  · rw [FractionalIdeal.inv_eq] at ht
    first
      | rw [FractionalIdeal.mem_div_iff_of_ne_zero hJ] at ht
    have hN : ((Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) : (𝓞 D.host.E)) ^ m) ∈ ((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ^ m : Ideal (𝓞 D.host.E)) :=
      Ideal.pow_mem_pow (Ideal.absNorm_mem _) m
    have hy : algebraMap (𝓞 D.host.E) D.host.E ((Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) : (𝓞 D.host.E)) ^ m) ∈
        (((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ^ m : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :=
      by
        first
          | exact FractionalIdeal.mem_coeIdeal_of_mem _ hN
    have h1 := ht _ hy
    rw [FractionalIdeal.mem_one_iff] at h1
    obtain ⟨o', ho'⟩ := h1
    refine ⟨(Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) : (𝓞 D.host.E)) ^ (a : ℕ) * o', ?_⟩
    have hsplit : (Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) : D.host.E) ^ D.R.rS =
        (Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) : D.host.E) ^ (a : ℕ) * (Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) : D.host.E) ^ m := by
      rw [← pow_add, ← hm]
    rw [map_mul, ho']
    simp only [ndS, map_pow, map_natCast, Nat.cast_pow, hsplit]
    ring

theorem fInt_holds : FInt := by
  intro D T F0 Λ f L hff hef hL hΛ
  refine ⟨?_, ?_⟩
  ·
    have hd : differentIdeal ℤ (𝓞 D.host.F) ≠ ⊥ := by
      first
        | exact differentIdeal_ne_bot
    have hinj : Function.Injective (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
      first
        | exact FaithfulSMul.algebraMap_injective _ _
        | (have h1 : Function.Injective (algebraMap (𝓞 D.host.F) D.host.E) := by
             rw [IsScalarTower.algebraMap_eq (𝓞 D.host.F) D.host.F D.host.E, RingHom.coe_comp]
             exact (algebraMap D.host.F D.host.E).injective.comp (IsFractionRing.injective _ _)
           rw [IsScalarTower.algebraMap_eq (𝓞 D.host.F) (𝓞 D.host.E) D.host.E, RingHom.coe_comp] at h1
           exact h1.of_comp)
    have hmap : (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ≠ ⊥ := by
      rwa [Ne, Ideal.map_eq_bot_iff_of_injective hinj]
    have hN : Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ≠ 0 := by
      rwa [Ne, Ideal.absNorm_eq_zero_iff]
    unfold ndS
    exact pow_pos (Nat.pos_of_ne_zero hN) _
  · intro x hx c

    have hec : ∀ a, (VS D).hT (f c) (F0.e a) = if a = c then 1 else 0 := by
      intro a
      have hs : starRingEnd D.host.E ((VS D).hT (F0.e a) (f c)) = (VS D).hT (f c) (F0.e a) := by
        first
          | exact (VS D).herm.eq _ _
      rw [← hs, hef]
      split_ifs <;> simp
    let P : Submodule (𝓞 D.host.E) (VS D).V :=
      { carrier := {y | ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (y)}
        add_mem' := by
          rintro y z ⟨o1, h1⟩ ⟨o2, h2⟩
          exact (show ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (y + z) from ⟨o1 + o2, by rw [map_add (f := _), map_add (f := _), mul_add, h1, h2]⟩)
        zero_mem' := by
          exact (show ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (0) from ⟨0, by rw [map_zero, map_zero, mul_zero]⟩)
        smul_mem' := by
          rintro r y ⟨o, h⟩
          refine (show ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (r • y) from ⟨r * o, ?_⟩)
          rw [← algebraMap_smul D.host.E r y, map_smul, smul_eq_mul, map_mul, h]
          ring }
    have hP : Λ ≤ P := by
      rw [hΛ]
      refine sup_le (sup_le ?_ ?_) ?_
      · unfold latSpan
        rw [Submodule.span_le]
        rintro y ⟨a, t, ht, rfl⟩
        show ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (t • F0.e a)
        rw [map_smul, smul_eq_mul, hec a]
        by_cases hac : a = c
        · subst hac
          obtain ⟨o, ho⟩ := ndS_mul_int D a t ht
          exact ⟨o, by rw [ho, if_pos rfl, mul_one]⟩
        · exact ⟨0, by rw [if_neg hac, mul_zero, mul_zero, map_zero]⟩
      · intro y hy
        show ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (y)
        exact ⟨0, by rw [(hL y hy c).2, mul_zero, map_zero]⟩
      · unfold latSpan
        rw [Submodule.span_le]
        rintro y ⟨a, t, ht, rfl⟩
        show ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (t • f a)
        exact ⟨0, by rw [map_smul, smul_eq_mul, hff c a, mul_zero, mul_zero, map_zero]⟩
    obtain ⟨o, ho⟩ := hP hx
    exact ⟨o, ho⟩

end PI.TermsAtPtFiniteW
end
end

section

noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW

open NumberField

theorem resFin_holds : ResFin := by
  intro E _ _ V _ _ _ _ Λ hΛ c hc
  have hZ : (Λ.restrictScalars ℤ).FG := by
    first
      | exact Submodule.FG.restrictScalars hΛ
      | (obtain ⟨t, ht⟩ := hΛ
         obtain ⟨s0, hs0⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (𝓞 E)).FG)
         rw [← ht, ← Submodule.span_smul_of_span_eq_top hs0]
         exact Submodule.fg_def.2 ⟨_, s0.finite_toSet.smul t.finite_toSet, rfl⟩)
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hZ
  have hmem : ∀ x ∈ Λ, ∃ a : Fin n → ℤ, ∑ i, a i • g i = x := by
    intro x hx
    have hx' : x ∈ Submodule.span ℤ (Set.range g) := by rw [hg]; exact hx
    rw [Submodule.mem_span_range_iff_exists_fun] at hx'
    exact hx'
  haveI : NeZero c := ⟨by omega⟩
  refine ⟨Fin n → ZMod c, inferInstance,
    fun x => if hx : x ∈ Λ then fun i => (((hmem x hx).choose i : ℤ) : ZMod c) else 0, ?_⟩
  intro x hx y hy hxy
  beta_reduce at hxy
  rw [dite_eq_left hx, dite_eq_left hy] at hxy
  have hax := (hmem x hx).choose_spec
  have hby := (hmem y hy).choose_spec
  have hdiv : ∀ i, (c : ℤ) ∣ (hmem y hy).choose i - (hmem x hx).choose i := fun i => by
    have hi := congrFun hxy i
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hi
    exact hi
  choose k hk using hdiv
  refine ⟨∑ i, k i • g i, ?_, ?_⟩
  · have hs : ∑ i, k i • g i ∈ Submodule.span ℤ (Set.range g) :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    rw [hg] at hs
    exact hs
  · rw [← hax, ← hby, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sub_smul, hk i, mul_smul, Nat.cast_smul_eq_nsmul E, natCast_zsmul]

end PI.TermsAtPtFiniteW
end
end
