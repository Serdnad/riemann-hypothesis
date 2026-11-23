module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle509
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle585
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle649
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
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.Domain
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
public import Mathlib.RingTheory.WittVector.Identities
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001

@[expose] public section

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem semiHom_ev₂_pull2 : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (φ : Fin d → MvPowerSeries (Fin e) k'), (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → ∀ n t, c'.ev₂ n (pull2 φ (MvPowerSeries.map σ t)) = (s.app n).two (c.ev₂ n t) := by
  intro p k k' _ _ σ d e G G' c c' s φ hφ n t
  have hev := GlobalTheory.T.connectedChart_evalSquare_variables_swap_constant p k' e G' c' n
  let a : Fin d ⊕ Fin d → MvPowerSeries (Fin e ⊕ Fin e) k' :=
    Sum.elim (fun j => inL (φ j)) (fun j => inR (φ j))
  have ha : ∀ i, constantCoeff (a i) = 0 := by
    intro i
    have hc := hev.2.2.2
    cases i with
    | inl j =>
      change constantCoeff (inL (φ j)) = 0
      rw [← hc, hev.1, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      change Coalgebra.counit (R := k') (c'.ev n (φ j)) = 0
      rw [hφ n j, (s.app n).counit_map, c.aug, map_zero]
    | inr j =>
      change constantCoeff (inR (φ j)) = 0
      rw [← hc, hev.2.1, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      change Coalgebra.counit (R := k') (c'.ev n (φ j)) = 0
      rw [hφ n j, (s.app n).counit_map, c.aug, map_zero]
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  let B := G'.A n ⊗[k'] G'.A n
  letI : Algebra k B := ((algebraMap k' B).comp σ).toAlgebra
  let u : G.A n →ₐ[k] B :=
    { ((Algebra.TensorProduct.includeLeft : G'.A n →ₐ[k'] B) : G'.A n →+* B).comp
        (s.app n).toRingHom with
      commutes' := fun r => by
        change Algebra.TensorProduct.includeLeft (R := k') (S := k') ((s.app n) (algebraMap k (G.A n) r)) = _
        rw [(s.app n).map_algebraMap, AlgHom.commutes]; rfl }
  let v : G.A n →ₐ[k] B :=
    { ((Algebra.TensorProduct.includeRight : G'.A n →ₐ[k'] B) : G'.A n →+* B).comp
        (s.app n).toRingHom with
      commutes' := fun r => by
        change Algebra.TensorProduct.includeRight (R := k') ((s.app n) (algebraMap k (G.A n) r)) = _
        rw [(s.app n).map_algebraMap, AlgHom.commutes]; rfl }
  let T : G.A n ⊗[k] G.A n →ₐ[k] B := Algebra.TensorProduct.lift u v (fun _ _ => Commute.all _ _)
  have hT : ∀ z, T z = (s.app n).two z := fun z => by
    induction z with
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    | tmul x y =>
      rw [Algebra.TensorProduct.lift_tmul, TensorProduct.map_tmul]
      change ((s.app n) x ⊗ₜ[k'] 1) * (1 ⊗ₜ[k'] (s.app n) y) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]; rfl
  let L : MvPowerSeries (Fin d ⊕ Fin d) k →ₐ[k] B :=
    { (c'.ev₂ n).toRingHom.comp
        ((substAlgHom (R := k') hs).toRingHom.comp
          (MvPowerSeries.map σ)) with
      commutes' := fun r => by
        change c'.ev₂ n (substAlgHom (R := k') hs (MvPowerSeries.map σ (C r))) = algebraMap k' B (σ r)
        rw [MvPowerSeries.map_C, show (C (σ r) : MvPowerSeries (Fin d ⊕ Fin d) k') =
          algebraMap k' _ (σ r) by rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply],
          AlgHom.commutes, AlgHom.commutes] }
  have hL : ∀ f, L f = c'.ev₂ n (pull2 φ (MvPowerSeries.map σ f)) := fun f => by
    change c'.ev₂ n (substAlgHom hs (MvPowerSeries.map σ f)) = _
    rw [coe_substAlgHom]; rfl
  have key : T.comp (c.ev₂ n) = L := by
    refine GlobalTheory.T.mvPowerSeries_algHom_ext_of_isNilpotent_X k (Fin d ⊕ Fin d) B _ _ (fun i => ?_) (fun i => ?_)
    · rw [AlgHom.comp_apply]
      change IsNilpotent (T (evA k (c.x₂ n) (c.nil₂ n) (X i)))
      rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate]; exact (c.nil₂ n i).map T
    · rw [AlgHom.comp_apply, hL, hT, MvPowerSeries.map_X]
      change (s.app n).two (evA k (c.x₂ n) (c.nil₂ n) (X i)) = c'.ev₂ n (subst a (X i))
      rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate, subst_X hs]
      cases i with
      | inl j =>
        change (s.app n).two (c.x n j ⊗ₜ 1) = c'.ev₂ n (inL (φ j))
        rw [hev.1, hφ n j, TensorProduct.map_tmul, SemiBialgHom.lin_apply, SemiBialgHom.lin_apply]
        congr 1; exact map_one (s.app n).toRingHom
      | inr j =>
        change (s.app n).two (1 ⊗ₜ c.x n j) = c'.ev₂ n (inR (φ j))
        rw [hev.2.1, hφ n j, TensorProduct.map_tmul, SemiBialgHom.lin_apply, SemiBialgHom.lin_apply]
        congr 1; exact map_one (s.app n).toRingHom
  rw [← hL, ← key, AlgHom.comp_apply, hT]

end GlobalTheory.Katz
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

namespace GlobalTheory.LazardOne

theorem choose_pow_mul_add_modEq_one (p : ℕ) [hp : Fact p.Prime] :
    ∀ (s A B : ℕ), B < p ^ s → (p ^ s * A + B).choose B ≡ 1 [MOD p] := by
  intro s
  induction s with
  | zero =>
    intro A B hB
    have : B = 0 := by simpa using hB
    subst this
    simp [Nat.ModEq]
  | succ s ih =>
    intro A B hB
    have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat (p ^ (s + 1) * A + B) B p _
    have e0 : p ^ (s + 1) * A + B = B + p * (p ^ s * A) := by ring
    rw [e0, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hp.out.pos, Nat.choose_self,
      one_mul] at h
    have hB' : B / p < p ^ s := by
      rw [Nat.div_lt_iff_lt_mul hp.out.pos, ← pow_succ]; exact hB
    have := ih A (B / p) hB'
    rw [add_comm (p ^ s * A)] at this
    rw [e0]; exact h.trans this

theorem not_dvd_choose_pow_mul_add (p : ℕ) [hp : Fact p.Prime] (s A B : ℕ) (hB : B < p ^ s) :
    ¬ p ∣ (p ^ s * A + B).choose B := by
  intro hd
  have h0 := (Nat.modEq_zero_iff_dvd.2 hd).symm.trans (choose_pow_mul_add_modEq_one p s A B hB)
  exact hp.out.not_dvd_one (Nat.modEq_zero_iff_dvd.1 h0.symm)

variable (p : ℕ) [hp : Fact p.Prime] {k : Type} [Field k] [CharP k p]

theorem eq_zero_of_eq_zero (N : ℕ) (c : ℕ → k)
    (hsym : ∀ i, i ≤ N → c i = c (N - i))
    (hrel : ∀ i j l, 0 < i → 0 < j → 0 < l → i + j + l = N →
      c (i + j) * ((i + j).choose i : k) = c i * ((j + l).choose j : k))
    (s K : ℕ) (hN : N = p ^ s * K) (hK2 : 2 ≤ K)
    (hK : ∀ u, 0 < u → u < K → ¬ p ∣ u ∨ ¬ p ∣ (K - u))
    (h0 : c (p ^ s) = 0) : ∀ n, 0 < n → n < N → c n = 0 := by
  have hA : ∀ i n, c i = 0 → 0 < i → i < n → n < N → ¬ p ∣ n.choose i → c n = 0 := by
    intro i n hi hi0 hin hnN hd
    have h := hrel i (n - i) (N - n) hi0 (by omega) (by omega) (by omega)
    rw [show i + (n - i) = n by omega, hi, zero_mul] at h
    have hne : ((n.choose i : ℕ) : k) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff k p]; exact hd
    exact (mul_eq_zero.1 h).resolve_right hne
  have hq : 0 < p ^ s := pow_pos hp.out.pos s
  have hb1 : ∀ u, 0 < u → u < K → ¬ p ∣ u → c (p ^ s * u) = 0 := by
    intro u hu huK hpu
    rcases Nat.lt_or_ge 1 u with h1 | h1
    · refine hA (p ^ s) (p ^ s * u) h0 hq (lt_mul_of_one_lt_right hq h1) ?_
        (GlobalTheory.Honda.Lazard.not_dvd_choose_pow_mul hp.out u hpu s)
      rw [hN]; exact Nat.mul_lt_mul_of_pos_left huK hq
    · have : u = 1 := by omega
      subst this; simpa using h0
  have hb : ∀ u, 0 < u → u < K → c (p ^ s * u) = 0 := by
    intro u hu huK
    rcases hK u hu huK with h | h
    · exact hb1 u hu huK h
    · have h' := hb1 (K - u) (by omega) (by omega) h
      have hle : p ^ s * (K - u) ≤ N := by rw [hN]; exact Nat.mul_le_mul_left _ (by omega)
      rw [hsym _ hle] at h'
      rwa [show N - p ^ s * (K - u) = p ^ s * u by
        rw [hN, ← Nat.mul_sub]; congr 1; omega] at h'
  intro n hn hnN
  obtain ⟨u, v, hvlt, rfl⟩ : ∃ u v, v < p ^ s ∧ n = p ^ s * u + v :=
    ⟨n / p ^ s, n % p ^ s, Nat.mod_lt _ hq, (Nat.div_add_mod n (p ^ s)).symm⟩
  have huK : u < K := by
    apply Nat.lt_of_mul_lt_mul_left (a := p ^ s)
    rw [← hN]; omega
  rcases Nat.eq_zero_or_pos v with hv | hv
  · subst hv
    rw [add_zero] at hn ⊢
    rcases Nat.eq_zero_or_pos u with hu | hu
    · subst hu; simp at hn
    · exact hb u hu huK
  · have hK1 : c (p ^ s * (K - 1)) = 0 := hb (K - 1) (by omega) (by omega)
    have e1 : p ^ s * K = p ^ s * (K - 1) + p ^ s := by
      rw [← Nat.mul_succ]; congr 1; omega
    have hNv : N - v = p ^ s * (K - 1) + (p ^ s - v) := by omega
    have hpos : 0 < p ^ s * (K - 1) := Nat.mul_pos hq (by omega)
    have hcNv : c (N - v) = 0 := by
      rw [hNv]
      refine hA (p ^ s * (K - 1)) _ hK1 hpos (by omega) (by omega) ?_
      rw [Nat.choose_symm_add]
      exact not_dvd_choose_pow_mul_add p s (K - 1) (p ^ s - v) (by omega)
    have hcv : c v = 0 := by rw [hsym v (by omega), hcNv]
    rcases Nat.eq_zero_or_pos u with hu | hu
    · subst hu; simpa using hcv
    · have hsu : 0 < p ^ s * u := Nat.mul_pos hq hu
      exact hA v _ hcv hv (by omega) hnN (not_dvd_choose_pow_mul_add p s u v hvlt)

theorem exists_scalar (N : ℕ) (a : ℕ → k)
    (hsym : ∀ i, i ≤ N → a i = a (N - i))
    (hrel : ∀ i j l, 0 < i → 0 < j → 0 < l → i + j + l = N →
      a (i + j) * ((i + j).choose i : k) = a i * ((j + l).choose j : k))
    (g : ℕ) (hg : 0 < g) (hdiv : ∀ i, 0 < i → i < N → g ∣ N.choose i)
    (s K : ℕ) (hN : N = p ^ s * K) (hK2 : 2 ≤ K)
    (hK : ∀ u, 0 < u → u < K → ¬ p ∣ u ∨ ¬ p ∣ (K - u))
    (hb : ((N.choose (p ^ s) / g : ℕ) : k) ≠ 0) :
    ∃ z : k, ∀ i, 0 < i → i < N → a i = z * ((N.choose i / g : ℕ) : k) := by
  set b : ℕ → k := fun i => ((N.choose i / g : ℕ) : k) with hbdef
  have hbsym : ∀ i, i ≤ N → b (N - i) = b i := by
    intro i hi; simp only [hbdef, Nat.choose_symm hi]
  have hbrel : ∀ i j l, 0 < i → 0 < j → 0 < l → i + j + l = N →
      b (i + j) * ((i + j).choose i : k) = b i * ((j + l).choose j : k) := by
    intro i j l hi hj hl hs
    obtain ⟨x, hx⟩ := hdiv (i + j) (by omega) (by omega)
    obtain ⟨y, hy⟩ := hdiv i hi (by omega)
    have hm := Nat.choose_mul (n := N) (k := i + j) (s := i) (by omega)
    rw [show N - i = j + l by omega, show i + j - i = j by omega, hx, hy, mul_assoc, mul_assoc] at hm
    have hm' := Nat.eq_of_mul_eq_mul_left hg hm
    simp only [hbdef, hx, hy, Nat.mul_div_cancel_left _ hg]
    rw [← Nat.cast_mul, ← Nat.cast_mul, hm']
  refine ⟨a (p ^ s) / b (p ^ s), ?_⟩
  have key := eq_zero_of_eq_zero p N (fun i => a i - a (p ^ s) / b (p ^ s) * b i) ?_ ?_ s K hN hK2 hK ?_
  · intro i hi hiN
    exact sub_eq_zero.1 (key i hi hiN)
  · intro i hi
    rw [hsym i hi, hbsym i hi]
  · intro i j l hi hj hl hs
    rw [sub_mul, sub_mul, hrel i j l hi hj hl hs, mul_assoc, mul_assoc, hbrel i j l hi hj hl hs]
  · rw [div_mul_cancel₀ _ hb, sub_self]

theorem exists_lift : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (N : ℕ)
    (a : ℕ → k), 2 ≤ N → (∀ i, i ≤ N → a i = a (N - i)) →
    (∀ i j l, 0 < i → 0 < j → 0 < l → i + j + l = N →
      a (i + j) * ((i + j).choose i : k) = a i * ((j + l).choose j : k)) →
    ∃ t : Fr p k, ∀ i, 0 < i → i < N → ∃ w : WittVector p k,
      t * (N.choose i : Fr p k) = algebraMap (WittVector p k) (Fr p k) w ∧
      WittVector.constantCoeff w = a i := by
  intro p _ k _ _ _ N a hN2 hsym hrel
  have hp : p.Prime := Fact.out
  obtain ⟨g, hg, hg1, hdiv, z, hz⟩ : ∃ g, 0 < g ∧ (g = 1 ∨ g = p) ∧
      (∀ i, 0 < i → i < N → g ∣ N.choose i) ∧
      ∃ z : k, ∀ i, 0 < i → i < N → a i = z * ((N.choose i / g : ℕ) : k) := by
    obtain ⟨r, m, hm, hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : N ≠ 0) p hp.one_lt.ne'
    by_cases hm1 : m = 1
    · subst hm1
      rw [mul_one] at hNe
      have hr : 0 < r := by
        rcases Nat.eq_zero_or_pos r with h | h
        · subst h; simp at hNe; omega
        · exact h
      have hdv : ∀ i, 0 < i → i < N → p ∣ N.choose i := by
        intro i hi hiN; rw [hNe] at hiN ⊢; exact hp.dvd_choose_pow (by omega) (by omega)
      refine ⟨p, hp.pos, Or.inr rfl, hdv, ?_⟩
      obtain ⟨c, hc, hch⟩ := GlobalTheory.Honda.Lazard.choose_prime_pow_pred hp r hr
      refine exists_scalar p N a hsym hrel p hp.pos hdv (r - 1) p ?_ hp.two_le ?_ ?_
      · rw [hNe, ← pow_succ]; congr 1; omega
      · intro u hu hup; left; exact fun h => absurd (Nat.le_of_dvd hu h) (by omega)
      · rw [hNe, hch, Nat.mul_div_cancel_left _ hp.pos, Ne, CharP.cast_eq_zero_iff k p]; exact hc
    · have hm0 : m ≠ 0 := by rintro rfl; simp at hNe; omega
      have hm2 : 2 ≤ m := by omega
      refine ⟨1, one_pos, Or.inl rfl, fun _ _ _ => one_dvd _, ?_⟩
      refine exists_scalar p N a hsym hrel 1 one_pos (fun _ _ _ => one_dvd _) r m hNe hm2 ?_ ?_
      · intro u hu huK
        by_contra h
        push_neg at h
        have := Nat.dvd_add h.2 h.1
        rw [Nat.sub_add_cancel huK.le] at this
        exact hm this
      · rw [Nat.div_one, hNe, Ne, CharP.cast_eq_zero_iff k p]
        exact GlobalTheory.Honda.Lazard.not_dvd_choose_pow_mul hp m hm r
  have hgW : ((g : ℕ) : WittVector p k) ≠ 0 := by
    rcases hg1 with h | h
    · subst h; simp
    · rw [h]
      intro h0
      have := congrArg (fun x : WittVector p k => x.coeff 1) h0
      simp only [WittVector.coeff_p_one, WittVector.zero_coeff] at this
      exact one_ne_zero this
  have hgF : ((g : ℕ) : Fr p k) ≠ 0 := by
    rw [← map_natCast (algebraMap (WittVector p k) (Fr p k)), Ne,
      map_eq_zero_iff _ (IsFractionRing.injective (WittVector p k) (Fr p k))]
    exact hgW
  refine ⟨algebraMap (WittVector p k) (Fr p k) (WittVector.teichmuller p z) / (g : Fr p k), ?_⟩
  intro i hi hiN
  obtain ⟨q, hq⟩ := hdiv i hi hiN
  refine ⟨WittVector.teichmuller p z * (q : WittVector p k), ?_, ?_⟩
  · rw [hq, Nat.cast_mul, map_mul, map_natCast]
    field_simp
  · rw [hz i hi hiN, hq, Nat.mul_div_cancel_left _ hg, map_mul, map_natCast,
      WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

end GlobalTheory.LazardOne
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz.Chart

theorem eq_zero_of_ev_cube : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), (∀ n i, IsNilpotent ((Sum.elim (fun i => c.x n i ⊗ₜ[k] (1 : G.A n ⊗[k] G.A n)) (fun j => (1 : G.A n) ⊗ₜ[k] c.x₂ n j)) i)) ∧ ∀ f : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k, (∀ n (h : ∀ i, IsNilpotent ((Sum.elim (fun i => c.x n i ⊗ₜ[k] (1 : G.A n ⊗[k] G.A n)) (fun j => (1 : G.A n) ⊗ₜ[k] c.x₂ n j)) i)), evA k _ h f = 0) → f = 0 := by
  intro p k _ d G c
  have hnil : ∀ n i, IsNilpotent ((Sum.elim (fun i => c.x n i ⊗ₜ[k] (1 : G.A n ⊗[k] G.A n)) (fun j => (1 : G.A n) ⊗ₜ[k] c.x₂ n j)) i) := by
    intro n i
    cases i with
    | inl i => exact (c.nil n i).map (Algebra.TensorProduct.includeLeft (R := k) (S := k))
    | inr j => exact (c.nil₂ n j).map (Algebra.TensorProduct.includeRight (R := k))
  refine ⟨hnil, fun f hf => ?_⟩
  ext α
  obtain ⟨n, hn⟩ := c.presents.2 (α.degree + 1)
  have hs := c.presents.1 n
  have h2 := GlobalTheory.T.powerSeriesPresentation_up_to_order_tensorProduct k (Fin d) (Fin d) (G.A n) (G.A n) (c.x n) (c.nil n) (c.x n) (c.nil n)
    (c.nil₂ n) hs hs
  have h3 := GlobalTheory.T.powerSeriesPresentation_up_to_order_tensorProduct k (Fin d) (Fin d ⊕ Fin d) (G.A n) (G.A n ⊗[k] G.A n) (c.x n) (c.nil n)
    (c.x₂ n) (c.nil₂ n) (hnil n) hs h2.1
  have := (h3.2 (α.degree + 1) hn (h2.2 (α.degree + 1) hn hn) f (hf n (hnil n)) α (Nat.lt_succ_self _))
  simpa using this

end GlobalTheory.Katz.Chart
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.quasiLogarithm_eq_p_smul_add_integral : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ), ∀ f ∈ quasiLog p h, ∀ b, Red p (cob1 (fun i => Katz.lift p (μ i)) f) (cob1 μ b) → RedV p (lin f) (lin b) → ∃ g ∈ quasiLog p h, f - (p : WittVector p k) • g ∈ intBy p k (Fin d) 1 := by
  first | exact @GlobalTheory.Katz.quasiLog_eq_p_smul_add_int | exact GlobalTheory.Katz.quasiLog_eq_p_smul_add_int | (intros; apply GlobalTheory.Katz.quasiLog_eq_p_smul_add_int <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz.Chart

theorem functions_are_series : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k)
    (c : Chart G d), (∀ n f, G.res n (c.ev (n + 1) f) = c.ev n f) ∧
    (∀ n s, pullbackTwo (G.res n) (c.ev₂ (n + 1) s) = c.ev₂ n s) ∧
    ∀ b : ∀ n, G.A n, (∀ n, G.res n (b (n + 1)) = b n) → ∃! f, ∀ n, c.ev n f = b n := by
  intro p k _ d G c
  refine ⟨fun n f => ?_, fun n s => ?_, fun b hb => ?_⟩
  · exact (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A (n + 1))).2 (G.A n) (G.res n : G.A (n + 1) →ₐ[k] G.A n)
      (c.x (n + 1)) (c.nil (n + 1)) (c.x n) (c.nil n) (fun i => c.res n i) f
  · let g : G.A (n + 1) →ₐ[k] G.A n := G.res n
    have h := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) (G.A (n + 1) ⊗[k] G.A (n + 1))).2
      (G.A n ⊗[k] G.A n) (Algebra.TensorProduct.map g g)
      (c.x₂ (n + 1)) (c.nil₂ (n + 1)) (c.x₂ n) (c.nil₂ n) (fun i => by
        cases i with
        | inl i => simp [x₂, g, c.res n i]
        | inr i => simp [x₂, g, c.res n i]) s
    refine Eq.trans ?_ h
    rfl
  · exact GlobalTheory.T.existsUnique_powerSeries_of_compatible_system k (Fin d) G.A c.x c.nil (fun n => (G.res n : G.A (n + 1) →ₐ[k] G.A n))
      (fun n i => c.res n i) c.presents b hb

end GlobalTheory.Katz.Chart
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.cechNerve_levelwise_equivalence_integral_pullback : ∀ (R : Type) [CommRing R] (F : Shv R) (Y X Y' X' : Scheme.{0}) (a : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (b : X' ⟶ X),
    IsPullback a f' f b → IsIntegralHom f →
    (∀ (Z Z' : Scheme.{0}) (h : Z ⟶ X) (h' : Z' ⟶ X') (φ : Z' ⟶ Z), IsIntegralHom h → IsPullback φ h' h b → Eqv R (sch.map φ) F) →
    ∀ (m : cech f' ⟶ cech f), IsPullback m (cechAug f') (cechAug f) (sch.map b) → ∀ n, Eqv R (disc.map (m.app n)) F := by
  first | (exact @GlobalTheory.cech_level_eqv_of_integral_pullback) | (exact GlobalTheory.cech_level_eqv_of_integral_pullback) | (intros; apply GlobalTheory.cech_level_eqv_of_integral_pullback  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleCohomologyEquivalence_pullback_integral_affine : ∀ (R : Type) [CommRing R] (F : Shv R) (A C : Type) [CommRing A] [CommRing C] [Algebra A C],
    (∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B],
      Eqv R (spMap (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B).toRingHom) F) →
    ∀ (Z Z' : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of A)) (h' : Z' ⟶ Spec (CommRingCat.of C)) (φ : Z' ⟶ Z),
    IsIntegralHom h → IsPullback φ h' h (Spec.map (CommRingCat.ofHom (algebraMap A C))) → Eqv R (sch.map φ) F := by
  first | (exact @GlobalTheory.EtC.eqv_pullback_integral_affine) | (exact GlobalTheory.EtC.eqv_pullback_integral_affine) | (intros; apply GlobalTheory.EtC.eqv_pullback_integral_affine  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem quasiIso_chains_cech_of_isLocallySurjective : ∀ (R : Type) [CommRing R] (P Q : PSh) (f : P ⟶ Q),
    Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f →
    QuasiIso ((chains R).map (show ((Arrow.mk f).cechNerve : Spc) ⟶ disc.obj Q from
      (Arrow.mk f).augmentedCechNerve.hom)) := by
  intro R _ P Q f hf
  exact GlobalTheory.T.quasiIso_cechNerveChains_of_etaleLocallySurjective R f (fun U y => ⟨Presheaf.imageSieve f y, hf.imageSieve_mem y, fun V g hg => hg⟩)

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace GlobalTheory.EtC

theorem chains_cechAug_quasiIso_of_smooth (R : Type) [CommRing R] {Y X : Scheme.{0}} (f : Y ⟶ X)
    [Smooth f] [Surjective f] : QuasiIso ((chains R).map (cechAug f)) :=
  GlobalTheory.T.quasiIso_cechNerveChains_of_etaleLocallySurjective R (yoneda.map f) (fun U y => GlobalTheory.T.smooth_surjective_etale_locally_has_sections f U y)

end GlobalTheory.EtC
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.hilbertLatticeTwistByMatrixModN_mul_SL2Z : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F) (α : Matrix (Fin 2) (Fin 2) (ZMod N)) (γ : SL(2, ℤ)), L ≤ stdLat F → twist N L (α * (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N)) = mulMat (twist N L α) (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
  first | exact @GlobalTheory.HilbFam.TwistSL.twist_mul_sl | exact GlobalTheory.HilbFam.TwistSL.twist_mul_sl | (intros; apply GlobalTheory.HilbFam.TwistSL.twist_mul_sl <;> assumption)
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.hilbertLatticeTwistByMatrixModN_mul : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F) (α β : Matrix (Fin 2) (Fin 2) (ZMod N)), L ≤ stdLat F → twist N (twist N L α) β = twist N L (α * β) := by
  first | exact @GlobalTheory.HilbFam.TwistMul.twist_twist | exact GlobalTheory.HilbFam.TwistMul.twist_twist | (intros; apply GlobalTheory.HilbFam.TwistMul.twist_twist <;> assumption)
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.hilbertSplitLattice_twist_diagonal_coprime : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (𝔞 𝔟 : Frac F) (x : F) (a : ℤ), IsCoprime a (N : ℤ) → HasLevel N (split 𝔞 𝔟 x) → twist N (split 𝔞 𝔟 x) (Matrix.diagonal ![1, (a : ZMod N)]) = split 𝔞 𝔟 (a * x) := by
  first | exact @GlobalTheory.HilbFam.twist_split_diagonal | exact GlobalTheory.HilbFam.twist_split_diagonal | (intros; apply GlobalTheory.HilbFam.twist_split_diagonal <;> assumption)
end
