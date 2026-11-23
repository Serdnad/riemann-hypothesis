module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle016
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section JProper

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem twist_sub_eq_mul (F Q : SubSystem S x Ω) (I : Chart x) :
    (F.twist Q).sub I = Q.sub I * F.sub I := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    exact Submodule.mul_mem_mul hq hy
  · refine Submodule.mul_le.mpr fun q hq y hy => Submodule.subset_span ⟨q, hq, y, hy, rfl⟩

def ChartInvertible {I : Chart x} (P : Submodule (chartRing S x I) Ω) : Prop :=
  ∃ Q' : Submodule (chartRing S x I) Ω, P * Q' = 1

theorem ChartInvertible.mul {I : Chart x} {P P' : Submodule (chartRing S x I) Ω}
    (h : ChartInvertible P) (h' : ChartInvertible P') : ChartInvertible (P * P') := by
  obtain ⟨Q, hQ⟩ := h
  obtain ⟨Q', hQ'⟩ := h'
  exact ⟨Q * Q', by rw [mul_mul_mul_comm, hQ, hQ', one_mul]⟩

theorem chartInvertible_twistSys (c : ℤ) (I : Chart x) :
    ChartInvertible ((twistSys S x c).sub I) :=
  (twistBundle S x c).invertible I

theorem chartInvertible_twistMul (M : LineBundle S x) (p : ℕ) (m : ℤ) (I : Chart x) :
    ChartInvertible ((twistMul M.toSubSystem p m).sub I) := by
  have hpow : ∀ n : ℕ, ChartInvertible ((M.toSubSystem.pow n).sub I) := by
    intro n
    induction n with
    | zero => exact chartInvertible_twistSys 0 I
    | succ n ih =>
      change ChartInvertible (((M.toSubSystem.pow n).twist M.toSubSystem).sub I)
      rw [twist_sub_eq_mul]
      exact ChartInvertible.mul (M.invertible I) ih
  rw [twistMul, twist_sub_eq_mul]
  exact ChartInvertible.mul (chartInvertible_twistSys m I) (hpow p)

theorem aeval_mul_mem_twistMod {I : Chart x} {G : Poly S N} {b : ℕ} (hG : G.IsHomogeneous b) {a : ℤ}
    {o : Ω} (ho : o ∈ twistMod S x a I) : aeval x G * o ∈ twistMod S x (a + b) I := by
  refine Submodule.span_induction (p := fun o _ => aeval x G * o ∈ twistMod S x (a + b) I)
    ?_ ?_ ?_ ?_ ho
  · rintro _ ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩
    refine Submodule.subset_span ⟨G * f, s, e, b + e', hs, hG.mul hf, hse, by push_cast; omega, ?_⟩
    rw [map_mul, mul_div_assoc]
  · rw [mul_zero]; exact Submodule.zero_mem _
  · intro y z _ _ hy hz; rw [mul_add]; exact Submodule.add_mem _ hy hz
  · intro r z _ hz
    rw [chartRing_smul_def, mul_left_comm, ← chartRing_smul_def]
    exact Submodule.smul_mem _ r hz

theorem exists_form_chart {I : Chart x} {P : Submodule (chartRing S x I) Ω} (hP : ChartInvertible P)
    {σ : Ω} (hσ : σ ∈ P) (hσ0 : σ ≠ 0) : ∃ (g : Poly S N) (e : ℕ), g.IsHomogeneous e ∧
      aeval x g ≠ 0 ∧ ∀ δ ∈ P, ∃ o ∈ twistMod S x (e : ℤ) I, aeval x g * δ = σ * o := by
  obtain ⟨Q', hQ'⟩ := hP
  have hq : ∃ q ∈ Q', q ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hbot : Q' = ⊥ := (Submodule.eq_bot_iff _).mpr hcon
    have h1 : (1 : Ω) ∈ (1 : Submodule (chartRing S x I) Ω) := Submodule.mem_one.mpr ⟨1, map_one _⟩
    rw [← hQ', hbot, Submodule.mul_bot, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  obtain ⟨q, hqQ, hq0⟩ := hq
  obtain ⟨b, hb⟩ := Submodule.mem_one.mp (hQ' ▸ Submodule.mul_mem_mul hσ hqQ :
    σ * q ∈ (1 : Submodule (chartRing S x I) Ω))
  obtain ⟨g, s, e, hs, hg, hse, hbg⟩ := b.2
  have hs0 := eval_ne_zero_of_mem_monos I hs
  have hb' : (b : Ω) = σ * q := hb
  have hgx : aeval x g = σ * q * aeval x s := by
    rw [← hb', hbg, div_mul_cancel₀ _ hs0]
  refine ⟨g, e, hg, by rw [hgx]; exact mul_ne_zero (mul_ne_zero hσ0 hq0) hs0, fun δ hδ => ?_⟩
  obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hQ' ▸ Submodule.mul_mem_mul hδ hqQ :
    δ * q ∈ (1 : Submodule (chartRing S x I) Ω))
  obtain ⟨h, t, e', ht, hh, hte, hah⟩ := a.2
  have ha' : aeval x h / aeval x t = δ * q := by rw [← hah]; exact ha
  refine ⟨aeval x (s * h) / aeval x t,
    Submodule.subset_span ⟨s * h, t, e', e + e', ht, hse.mul hh, hte, by push_cast; ring, rfl⟩, ?_⟩
  rw [map_mul, mul_div_assoc, ha', hgx]
  ring

end JProper

theorem StepData.JProper.proof : StepData.JProper.Statement.{u, w} := by
  classical
  intro k _ Ω _ _ N x T
  have hloc : ∀ I : Chart x, ∃ (g : Poly k N) (e : ℕ), g.IsHomogeneous e ∧ aeval x g ≠ 0 ∧
      ∀ δ ∈ T.D.sub I, ∃ o ∈ twistMod k x (e : ℤ) I, aeval x g * δ = T.si * o := fun I =>
    exists_form_chart (chartInvertible_twistMul T.M T.p (T.m - T.c₁) I)
      ((Submodule.mem_iInf _).mp T.si_mem I) T.si_ne
  choose g e hg hg0 hgD using hloc
  refine ⟨∏ I, g I, ∑ I, e I, Ideal.subset_span ⟨∑ I, e I, IsHomogeneous.prod _ _ _
    fun I _ => hg I, fun I δ hδ => ?_⟩, IsHomogeneous.prod _ _ _ fun I _ => hg I, ?_⟩
  · obtain ⟨o, ho, hδo⟩ := hgD I δ hδ
    have hrest : (∏ J ∈ Finset.univ.erase I, g J).IsHomogeneous (∑ J ∈ Finset.univ.erase I, e J) :=
      IsHomogeneous.prod _ _ _ fun J _ => hg J
    refine ⟨aeval x (∏ J ∈ Finset.univ.erase I, g J) * o, ?_, ?_⟩
    · have hm := aeval_mul_mem_twistMod hrest ho
      have hdeg : ((e I : ℕ) : ℤ) + ((∑ J ∈ Finset.univ.erase I, e J : ℕ) : ℤ) =
          ((∑ J, e J : ℕ) : ℤ) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ I)]; push_cast; ring
      rwa [hdeg] at hm
    · rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ I), map_mul, mul_comm (aeval x (g I)),
        mul_assoc, hδo]
      ring
  · rw [mem_primeOf_of_isHomogeneous x (IsHomogeneous.prod _ _ _ fun I _ => hg I), map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun I _ => hg0 I

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace TwistTildeProof

theorem smul_mem_of_mem_span {R A M : Type*} [CommRing R] [Ring A] [AddCommGroup M] [Module R A]
    [Module A M] [Module R M] [IsScalarTower R A M] [SMulCommClass A R M] {s : Set A} {t : Set M}
    {T : Submodule R M} (h : ∀ a ∈ s, ∀ b ∈ t, a • b ∈ T) {q : A} (hq : q ∈ Submodule.span R s)
    {m : M} (hm : m ∈ Submodule.span R t) : q • m ∈ T := by
  refine Submodule.span_induction (p := fun q _ => q • m ∈ T) ?_ ?_ ?_ ?_ hq
  · intro a ha
    refine Submodule.span_induction (p := fun m _ => a • m ∈ T) ?_ ?_ ?_ ?_ hm
    · exact fun b hb => h a ha b hb
    · rw [smul_zero]; exact T.zero_mem
    · intro b c _ _ hb hc; rw [smul_add]; exact T.add_mem hb hc
    · intro r b _ hb; rw [smul_comm]; exact T.smul_mem r hb
  · rw [zero_smul]; exact T.zero_mem
  · intro a b _ _ ha hb; rw [add_smul]; exact T.add_mem ha hb
  · intro r a _ ha; rw [smul_assoc]; exact T.smul_mem r ha

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]

def prodSet (M : FinGradedSub (S := S) (x := x) E) (Q : FinGradedSub (S := S) (x := x) Ω) (c : ℤ) :
    Set E :=
  {z | ∃ (a b : ℤ) (q : Ω) (m : E), q ∈ Q.piece a ∧ m ∈ M.piece b ∧ a + b = c ∧ z = q • m}

def prod (M : FinGradedSub (S := S) (x := x) E) (Q : FinGradedSub (S := S) (x := x) Ω) :
    FinGradedSub (S := S) (x := x) E where
  piece c := Submodule.span S (prodSet M Q c)
  smul_mem d c f m hf hm := by
    refine Submodule.span_induction (p := fun m _ => aeval x f • m ∈ Submodule.span S
      (prodSet M Q (c + d))) ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨a, b, q, m, hq, hm, hab, rfl⟩
      refine Submodule.subset_span ⟨a, b + d, q, aeval x f • m, hq, M.smul_mem d b f m hf hm,
        by omega, ?_⟩
      rw [smul_smul, smul_smul, mul_comm]
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro r a _ ha; rw [smul_comm]; exact Submodule.smul_mem _ r ha
  fg := by
    obtain ⟨n, deg, gen, hgen, hspan⟩ := M.fg
    obtain ⟨n', deg', gen', hgen', hspan'⟩ := Q.fg
    let e := (finProdFinEquiv : Fin n' × Fin n ≃ Fin (n' * n))
    refine ⟨n' * n, fun k => deg' (e.symm k).1 + deg (e.symm k).2,
      fun k => gen' (e.symm k).1 • gen (e.symm k).2, fun k => Submodule.subset_span
        ⟨_, _, _, _, hgen' _, hgen _, rfl, rfl⟩, fun c => Submodule.span_le.mpr ?_⟩
    rintro _ ⟨a, b, q, m, hq, hm, hab, rfl⟩
    refine smul_mem_of_mem_span ?_ (hspan' a hq) (hspan b hm)
    rintro _ ⟨l, f', e', hf', he', rfl⟩ _ ⟨j, f, e'', hf, he'', rfl⟩
    refine Submodule.subset_span ⟨e (l, j), f' * f, e' + e'', hf'.mul hf, ?_, ?_⟩
    · simp only [Equiv.symm_apply_apply]; push_cast; omega
    · simp only [Equiv.symm_apply_apply, smul_eq_mul, map_mul, smul_smul]
      congr 1; ring

theorem twist_eq (M : FinGradedSub (S := S) (x := x) E) (Q : FinGradedSub (S := S) (x := x) Ω)
    (I : Chart x) : ((M.tildeSys 0).twist (Q.tildeSys 0)).sub I = (prod M Q).tilde 0 I := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    change q ∈ Q.tilde 0 I at hq
    change y ∈ M.tilde 0 I at hy
    refine smul_mem_of_mem_span ?_ hq hy
    rintro _ ⟨q, s₁, a₁, e₁, hs₁, hse₁, hq, ha₁, rfl⟩ _ ⟨m, s₂, a₂, e₂, hs₂, hse₂, hm, ha₂, rfl⟩
    refine Submodule.subset_span ⟨q • m, s₁ * s₂, a₁ + a₂, e₁ + e₂, mul_mem hs₁ hs₂, hse₁.mul hse₂,
      Submodule.subset_span ⟨a₁, a₂, q, m, hq, hm, rfl, rfl⟩, by push_cast; omega, ?_⟩
    simp only [smul_eq_mul, smul_smul, map_mul, mul_inv]
    congr 1; ring
  · obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨p, s, a, e, hs, hse, hp, hae, rfl⟩
    have hs0 := eval_ne_zero_of_mem_monos I hs
    refine Submodule.span_induction (p := fun p _ => (aeval x s)⁻¹ • p ∈
      ((M.tildeSys 0).twist (Q.tildeSys 0)).sub I) ?_ ?_ ?_ ?_ hp
    · rintro _ ⟨a', b', q, m, hq, hm, hab, rfl⟩
      set k := a'.toNat
      set j := (-a').toNat
      have hkj : (k : ℤ) - j = a' := Int.toNat_sub_toNat_neg a'
      have hq' : (aeval x (X i ^ k : Poly S N))⁻¹ • (aeval x (X i ^ j : Poly S N) • q) ∈
          Q.tilde 0 I := by
        have h := Q.smul_mem j a' _ q (isHomogeneous_X_pow i j) hq
        rw [show a' + (j : ℤ) = k by omega] at h
        exact Submodule.subset_span ⟨_, X i ^ k, k, k, pow_mem (X_mem_monos hi) k,
          isHomogeneous_X_pow i k, h, by simp, rfl⟩
      have hm' : (aeval x (s * X i ^ j))⁻¹ • (aeval x (X i ^ k : Poly S N) • m) ∈ M.tilde 0 I := by
        have h := M.smul_mem k b' _ m (isHomogeneous_X_pow i k) hm
        exact Submodule.subset_span ⟨_, s * X i ^ j, b' + k, e + j,
          mul_mem hs (pow_mem (X_mem_monos hi) j), hse.mul (isHomogeneous_X_pow i j), h,
          by push_cast; omega, rfl⟩
      have heq : (aeval x s)⁻¹ • (q • m) = ((aeval x (X i ^ k : Poly S N))⁻¹ •
          (aeval x (X i ^ j : Poly S N) • q)) • ((aeval x (s * X i ^ j))⁻¹ •
          (aeval x (X i ^ k : Poly S N) • m)) := by
        simp only [smul_eq_mul, smul_smul, map_mul, map_pow, aeval_X]
        congr 1
        field_simp
      rw [heq]
      exact Submodule.subset_span ⟨_, hq', _, hm', rfl⟩
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro r a _ ha; rw [smul_comm]; exact Submodule.smul_of_tower_mem _ r ha

end TwistTildeProof


open TwistTildeProof in
theorem TwistTilde.proof : TwistTilde.Statement := by
  intro S _ Ω _ _ N x E _ _ _ _ M Q
  exact ⟨prod M Q, fun c => rfl, twist_eq M Q⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section ZeroIdealChartAux

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

def chartUnion (I K : Chart x) : Chart x :=
  ⟨I.1 ∪ K.1, I.2.1.mono Finset.subset_union_left, Finset.union_subset I.2.2 K.2.2⟩

theorem monos_union_split {I K : Finset (Fin (N + 1))} {s : Poly S N} (hs : s ∈ monos (I ∪ K)) :
    ∃ u ∈ monos (S := S) I, ∃ v ∈ monos (S := S) K, u * v = s := by
  unfold monos at hs
  rw [Finset.coe_union, Set.image_union, Submonoid.closure_union, Submonoid.mem_sup] at hs
  exact hs

theorem aeval_mem_twistMod {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) (K : Chart x) :
    aeval x f ∈ twistMod S x (e : ℤ) K :=
  Submodule.subset_span ⟨f, 1, 0, e, one_mem _, hf, isHomogeneous_one _ _, by simp, by simp⟩

theorem exists_monos_mul_mem_twistMod (I K : Chart x) (b : Ω)
    (hb : b ∈ chartRing S x (chartUnion I K)) :
    ∃ u ∈ monos (S := S) I.1, ∃ d : ℕ, u.IsHomogeneous d ∧ aeval x u * b ∈ twistMod S x (d : ℤ) K := by
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := hb
  obtain ⟨u, hu, v, hv, rfl⟩ := monos_union_split hs
  obtain ⟨du, hdu⟩ := monos_isHomogeneous hu
  obtain ⟨dv, hdv⟩ := monos_isHomogeneous hv
  have huv0 := eval_ne_zero_of_mem_monos (chartUnion I K) hs
  have hu0 := eval_ne_zero_of_mem_monos I hu
  have hv0 := eval_ne_zero_of_mem_monos K hv
  have he : du + dv = e := (hdu.mul hdv).inj_right hse (fun h => huv0 (by rw [h, map_zero]))
  refine ⟨u, hu, du, hdu, Submodule.subset_span ⟨f, v, dv, e, hv, hf, hdv, by omega, ?_⟩⟩
  rw [map_mul]
  field_simp

theorem twistMod_mul_mem {K : Chart x} {a b : Ω} {c c' : ℤ} (ha : a ∈ twistMod S x c K)
    (hb : b ∈ twistMod S x c' K) : a * b ∈ twistMod S x (c + c') K := by
  have h := Submodule.mul_mem_mul (M := (twistSys S x c).sub K) (N := (twistSys S x c').sub K) ha hb
  rw [twistSys_sub_mul] at h
  exact h

theorem mul_mem_chartRing_union (D : SubFamily S x Ω) (I K : Chart x) (y : Ω)
    (hy : ∀ δ ∈ D.sub I, y * δ ∈ chartRing S x I) :
    ∀ δ ∈ D.sub (chartUnion I K), y * δ ∈ chartRing S x (chartUnion I K) := by
  intro δ hδ
  obtain ⟨a, ⟨w, hw⟩, haδ⟩ := (D.mem_iff I (chartUnion I K) Finset.subset_union_left δ).mp hδ
  have hinv : ((↑w⁻¹ : chartRing S x (chartUnion I K)) : Ω) * (a : Ω) = 1 := by
    have := congrArg Subtype.val (Units.inv_mul w)
    rw [hw] at this
    exact this
  have h1 : y * ((a : Ω) • δ) ∈ chartRing S x (chartUnion I K) :=
    chartRing_mono Finset.subset_union_left (hy _ haδ)
  have h2 : y * δ = ((↑w⁻¹ : chartRing S x (chartUnion I K)) : Ω) * (y * ((a : Ω) • δ)) := by
    rw [smul_eq_mul, mul_left_comm y, ← mul_assoc, hinv, one_mul]
  rw [h2]
  exact mul_mem (w⁻¹ : (chartRing S x (chartUnion I K))ˣ).1.2 h1

end ZeroIdealChartAux

theorem ZeroIdealChart.proof : ZeroIdealChart.Statement.{u, w} := by
  classical
  intro k _ Ω _ _ N x T I y hy
  obtain ⟨L, hL⟩ := exists_lineBundle_twistMul T.M T.p (T.m - T.c₁)
  have hLD : L.toSubSystem = T.D := hL
  have hsub : ∀ K, T.D.sub K = L.sub K := fun K => by rw [← hLD]

  have hsi : T.si ∈ T.D.sub I := (Submodule.mem_iInf _).mp T.si_mem I
  obtain ⟨f, s, n, hs, hf, hsn, hz⟩ := hy _ hsi
  have hs0 := eval_ne_zero_of_mem_monos I hs
  have hfz : y * T.si * aeval x s = aeval x f := (eq_div_iff hs0).mp hz

  have hyL : ∀ δ ∈ L.sub I, y * δ ∈ chartRing k x I := fun δ hδ => hy δ (by rw [hsub]; exact hδ)
  have hyU := mul_mem_chartRing_union L.toSubFamily I

  choose G hG using fun K => L.fg K
  have hgen : ∀ p : Σ K : Chart x, (G K : Set Ω),
      y * (p.2 : Ω) ∈ chartRing k x (chartUnion I p.1) := fun p =>
    hyU p.1 y hyL _ (L.mono p.1 (chartUnion I p.1)
      (show p.1.1 ⊆ (chartUnion I p.1).1 from Finset.subset_union_right) _
      (by rw [← hG p.1]; exact Submodule.subset_span p.2.2))
  choose u hu d hd hud using fun p : (Σ K : Chart x, (G K : Set Ω)) =>
    exists_monos_mul_mem_twistMod (S := k) I p.1 (y * (p.2 : Ω)) (hgen p)

  obtain ⟨U, hUdef⟩ : ∃ U : Poly k N, U = ∏ p, u p := ⟨_, rfl⟩
  obtain ⟨dU, hdUdef⟩ : ∃ dU : ℕ, dU = ∑ p, d p := ⟨_, rfl⟩
  have hUm : U ∈ monos (S := k) I.1 := hUdef ▸ prod_mem fun p _ => hu p
  have hUh : U.IsHomogeneous dU := hUdef ▸ hdUdef ▸ IsHomogeneous.prod _ _ _ fun p _ => hd p
  have key : ∀ p : Σ K : Chart x, (G K : Set Ω),
      aeval x U * (y * (p.2 : Ω)) ∈ twistMod k x (dU : ℤ) p.1 := by
    intro p
    have hsplit : U = u p * ∏ q ∈ Finset.univ.erase p, u q := by
      rw [hUdef, Finset.mul_prod_erase _ _ (Finset.mem_univ p)]
    have hdsplit : dU = d p + ∑ q ∈ Finset.univ.erase p, d q := by
      rw [hdUdef, Finset.add_sum_erase _ _ (Finset.mem_univ p)]
    have h2 := aeval_mem_twistMod (x := x)
      (IsHomogeneous.prod _ _ _ fun q _ => hd q : (∏ q ∈ Finset.univ.erase p, u q).IsHomogeneous _) p.1
    have h3 := twistMod_mul_mem (hud p) h2
    rw [hsplit, hdsplit, map_mul, Nat.cast_add]
    convert h3 using 1
    ring
  have hUK : ∀ (K : Chart x), ∀ δ ∈ L.sub K, aeval x U * (y * δ) ∈ twistMod k x (dU : ℤ) K := by
    intro K δ hδ
    rw [← hG K] at hδ
    induction hδ using Submodule.span_induction with
    | mem δ hδ => exact key ⟨K, ⟨δ, hδ⟩⟩
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add, mul_add]; exact add_mem ha hb
    | smul a b _ hb =>
      rw [chartRing_smul_def, show aeval x U * (y * ((a : Ω) * b)) = (a : Ω) * (aeval x U * (y * b)) by ring,
        ← chartRing_smul_def]
      exact Submodule.smul_mem _ a hb
  have hU0 := eval_ne_zero_of_mem_monos I hUm

  have hfU : f * U ∈ T.J := by
    refine Ideal.subset_span ⟨n + dU, hf.mul hUh, fun K δ hδ => ?_⟩
    refine ⟨aeval x s * (aeval x U * (y * δ)), ?_, ?_⟩
    · rw [Nat.cast_add]
      exact twistMod_mul_mem (aeval_mem_twistMod hsn K) (hUK K δ (by rw [← hsub]; exact hδ))
    · rw [map_mul, ← hfz]
      ring

  refine Submodule.subset_span ⟨f * U, s * U, n + dU, hfU, mul_mem hs hUm, hf.mul hUh, hsn.mul hUh, ?_⟩
  rw [map_mul, map_mul, ← hfz]
  field_simp

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u w

theorem VeryAmpleDegree.proof (hDim : VeryAmpleDim.Statement.{u, w})
    (hSecs : VeryAmpleSecs.Statement.{u, w}) (hHilb : VeryAmpleHilbert.Statement.{u, w}) :
    VeryAmpleDegree.Statement.{u, w} := by
  intro k _ Ω _ _ N x e Nb r h hZ hV
  obtain ⟨-, P, -, hP, hPn⟩ := hHilb k Ω N x e Nb hZ ⟨r, h, hV⟩
  obtain ⟨-, Q, -, hQ, hQn⟩ := hHilb k Ω r h e (twistBundle k h 1) (hDim k Ω N x e Nb r h hZ hV)
    isVeryAmple_twistSys_one
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hPn.and hQn)
  have hPQ : P = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ => ((m + n₀ : ℕ) : ℚ)) ?_ ?_
    · intro a b hab
      have : a + n₀ = b + n₀ := by simpa using hab
      omega
    · intro m
      obtain ⟨h1, h2⟩ := hn₀ (m + n₀) (Nat.le_add_left n₀ m)
      change P.eval _ = Q.eval _
      rw [← h1, ← h2, hSecs k Ω N x Nb r h hV (m + n₀)]
      rfl
  have hnum : (interNum (primeOf (S := k) x) (fun _ : Fin e => Nb.toSubSystem) : ℚ) =
      (interNum (primeOf (S := k) h) (fun _ : Fin e => twistSys k h 1) : ℚ) := by
    rw [← hP, hPQ, hQ]
    rfl
  exact_mod_cast hnum

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def CellDSq.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (n : ℕ)
    (s : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω), cellD S y (n + 1) (cellD S y n s) = 0

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
