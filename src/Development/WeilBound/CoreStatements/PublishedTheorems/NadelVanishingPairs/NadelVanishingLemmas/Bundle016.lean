module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle253
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle394
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle012
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle001
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle013
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SplittingLocalIntegrality
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier

namespace GlobalTheory.LogDR

theorem extD_mem_logSec_roundedTwist : ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι) (G : CartierDiv X) (r : C → ℕ), (∀ c, r c < p) → ∀ (q : ℕ) (W : X.Opens) (η : abelian₂ X.functionField), η ∈ logSec (suppAll E) (p • G + ∑ c, r c • E c) q W → extD _ η ∈ logSec (suppAll E) (p • G + ∑ c, r c • E c) (q + 1) W := by
  intro p _ X _ _ C _ E n ι _ 𝒜 G r hr q W η hη
  simp only [logSec, latSec, AddSubgroup.mem_iInf] at hη ⊢
  intro y hy
  have hcov : y ∈ (⨆ i, 𝒜.U i) := by rw [𝒜.cover]; trivial
  obtain ⟨i, hi⟩ := (Opens.mem_iSup).1 hcov
  obtain ⟨t, ht⟩ := G.exists_isEqn y
  obtain ⟨-, hloc⟩ := GlobalTheory.T.roundedTwist_localEquation_chart p 𝒜 G r hr
  obtain ⟨ρ, -, hρ⟩ := hloc i
  have heq := hρ y hi t ht
  have hstalk := GlobalTheory.T.log_forms_eq_chart_forms (suppAll E) (𝒜.U i) (𝒜.x i) (𝒜.J i) (p • G + ∑ c, r c • E c) y
    (t ^ p * ∏ j ∈ 𝒜.J i, 𝒜.x i j ^ ρ j)
  have h1 := hη y hy
  rw [hstalk q (𝒜.chart i) hi heq] at h1
  rw [hstalk (q + 1) (𝒜.chart i) hi heq]
  exact GlobalTheory.T.chart_forms_differential_closed X.functionField p (locRing y) n (𝒜.x i) (𝒜.J i) t ρ
    ((𝒜.chart i).chart y hi) q η h1

end GlobalTheory.LogDR
end

section

open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory.ProjFn

theorem list_prod_apply_fixed {M : Type} [AddCommMonoid M] (l : List (AddMonoid.End M)) (y : M)
    (h : ∀ f ∈ l, f y = y) : l.prod y = y := by
  induction l with
  | nil => rfl
  | cons f l ih =>
    rw [List.prod_cons]
    show f (l.prod y) = y
    rw [ih (fun g hg => h g (List.mem_cons_of_mem _ hg)), h f List.mem_cons_self]

theorem mul_list_prod_eq_zero {R : Type} [Ring R] (a b : R) (l : List R) (hb : b ∈ l)
    (hc : ∀ f ∈ l, Commute a f) (hab : a * b = 0) : a * l.prod = 0 := by
  induction l with
  | nil => simp at hb
  | cons f l ih =>
    rw [List.prod_cons, ← mul_assoc]
    rcases List.mem_cons.1 hb with rfl | hb'
    · rw [hab, zero_mul]
    · rw [(hc f List.mem_cons_self).eq, mul_assoc,
        ih hb' (fun g hg => hc g (List.mem_cons_of_mem _ hg)), mul_zero]

private theorem derivation_iterate_mul_antidiagonal {K : Type} [Field K] (D : Derivation ℤ K K) (n : ℕ) (a b : K) :
    (⇑D)^[n] (a * b) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        n.choose ij.1 • ((⇑D)^[ij.1] a * (⇑D)^[ij.2] b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_antidiagonal_choose_succ_nsmul
      (fun i j => (⇑D)^[i] a * (⇑D)^[j] b) n]

    rw [Function.iterate_succ_apply', ih, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [map_nsmul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, Function.iterate_succ_apply',
      Function.iterate_succ_apply',
      n.choose_symm_of_eq_add (Finset.HasAntidiagonal.mem_antidiagonal.1 hij).symm,
      nsmul_add, mul_comm ((⇑D)^[ij.2] b)]

private theorem derivation_iterate_char_mul {K : Type} [Field K] (p : ℕ) [hp : Fact p.Prime] [CharP K p]
    (D : Derivation ℤ K K) (a b : K) :
    (⇑D)^[p] (a * b) = a * (⇑D)^[p] b + b * (⇑D)^[p] a := by
  rw [derivation_iterate_mul_antidiagonal, Finset.sum_eq_add_of_mem (0, p) (p, 0)]
  · simp only [Nat.choose_zero_right, Nat.choose_self, one_smul, Function.iterate_zero, id]
    rw [mul_comm ((⇑D)^[p] a)]
  · simp
  · simp
  · intro h
    have := congrArg Prod.fst h
    exact hp.out.ne_zero this.symm
  · intro c hc hne
    obtain ⟨h1, h2⟩ := hne
    have hsum := Finset.HasAntidiagonal.mem_antidiagonal.1 hc
    have hc1 : c.1 ≠ 0 := by
      intro h0
      apply h1
      ext
      · exact h0
      · simp at hsum ⊢; omega
    have hc2 : c.1 < p := by
      rcases Nat.lt_or_ge c.1 p with h | h
      · exact h
      · exfalso
        apply h2
        ext
        · simp; omega
        · simp; omega
    have hdvd := hp.out.dvd_choose_self hc1 hc2
    rw [nsmul_eq_mul, (CharP.cast_eq_zero_iff K p _).2 hdvd, zero_mul]

private theorem derivation_eq_zero_of_kills_coords {K : Type} [Field K] {n : ℕ} (x : Fin n → Kˣ)
    (D : Fin n → Derivation ℤ K K) (hd : ∀ c : K, dK c = ∑ j, D j c • dlog (x j))
    (E : Derivation ℤ K K) (hE : ∀ k, E (x k : K) = 0) (c : K) : E c = 0 := by
  rw [← E.liftKaehlerDifferential_comp_D c]
  have hc : KaehlerDifferential.D ℤ K c = ∑ j, D j c • dlog (x j) := hd c

  rw [hc, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_smul]
  show D j c • E.liftKaehlerDifferential
    (((↑(x j)⁻¹ : Kˣ) : K) • KaehlerDifferential.D ℤ K (x j : K)) = 0
  rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, hE, smul_zero, smul_zero]

private theorem derivation_iterate_char_eq_self_of_coords {K : Type} [Field K] (p : ℕ) [hp : Fact p.Prime] [CharP K p] {n : ℕ}
    (x : Fin n → Kˣ) (D : Fin n → Derivation ℤ K K)
    (hd : ∀ c : K, dK c = ∑ j, D j c • dlog (x j))
    (hD : ∀ i j, D i (x j : K) = if i = j then (x j : K) else 0) (i : Fin n) (c : K) :
    (⇑(D i))^[p] c = D i c := by
  let L : K →ₗ[ℤ] K := ((D i : K →ₗ[ℤ] K) ^ p) - (D i : K →ₗ[ℤ] K)
  have hL : ∀ a, L a = (⇑(D i))^[p] a - D i a := by
    intro a
    show ((D i : K →ₗ[ℤ] K) ^ p) a - (D i : K →ₗ[ℤ] K) a = _
    rw [Module.End.pow_apply]
    rfl
  let E : Derivation ℤ K K := Derivation.mk' L (by
    intro a b
    rw [hL, hL, hL, derivation_iterate_char_mul p, Derivation.leibniz, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      smul_eq_mul]
    ring)
  have hE : ∀ k, E (x k : K) = 0 := by
    intro k
    show L (x k : K) = 0
    rw [hL]
    obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.out.pos).symm⟩
    rw [hm, Function.iterate_succ_apply]
    by_cases hik : i = k
    · have hfix : D i (x k : K) = x k := by rw [hD, if_pos hik]
      rw [hfix, Function.iterate_fixed hfix, sub_self]
    · have hz : D i (x k : K) = 0 := by rw [hD, if_neg hik]
      rw [hz, Function.iterate_fixed (map_zero (D i)), sub_self]
  have := derivation_eq_zero_of_kills_coords x D hd E hE c
  have h2 : L c = 0 := this
  rw [hL, sub_eq_zero] at h2
  exact h2

private theorem derivation_comm_of_dK_eq_sum_dlog {K : Type} [Field K] {n : ℕ} (x : Fin n → Kˣ)
    (D : Fin n → Derivation ℤ K K) (hd : ∀ c : K, dK c = ∑ j, D j c • dlog (x j))
    (hD : ∀ i j, D i (x j : K) = if i = j then (x j : K) else 0) (i j : Fin n) (c : K) :
    D i (D j c) = D j (D i c) := by
  have h := derivation_eq_zero_of_kills_coords x D hd ⁅D i, D j⁆ (by
    intro k
    rw [Derivation.commutator_apply]
    by_cases hik : i = k <;> by_cases hjk : j = k <;> simp [hD, hik, hjk]) c
  rw [Derivation.commutator_apply, sub_eq_zero] at h
  exact h

theorem projector_pthPow : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (n : ℕ) (x : Fin n → Kˣ) (D : Fin n → Derivation ℤ K K), IsCoord x → (∀ c : K, dK c = ∑ j, D j c • dlog (x j)) → (∀ i j, D i (x j : K) = if i = j then (x j : K) else 0) → ∀ π : AddMonoid.End K, π = (List.ofFn fun i => 1 - (show AddMonoid.End K from (D i).toLinearMap.toAddMonoidHom) ^ (p - 1)).prod → (∀ c, ∃ g : K, π c = g ^ p) ∧ ∀ g : K, π (g ^ p) = g ^ p := by
  intro K _ p _ _ n x D _hx hd hD π hπ
  have hpr : p.Prime := Fact.out
  let Dend : Fin n → AddMonoid.End K := fun i => (D i).toLinearMap.toAddMonoidHom
  have hpow : ∀ i (m : ℕ) c, (Dend i ^ m) c = (⇑(D i))^[m] c := by
    intro i m c
    rw [AddMonoid.End.coe_pow]
    rfl
  obtain ⟨m, hm⟩ : ∃ m, p - 1 = m + 1 := ⟨p - 2, by have := hpr.two_le; omega⟩
  have hπ' : π = (List.ofFn fun i => 1 - Dend i ^ (p - 1)).prod := hπ
  have hcomm : ∀ i j, Commute (Dend i) (Dend j) := by
    intro i j
    refine AddMonoidHom.ext fun c => ?_
    exact derivation_comm_of_dK_eq_sum_dlog x D hd hD i j c
  refine ⟨?_, ?_⟩
  · intro c
    apply dK_eq_zero_imp_pow K p
    rw [hd]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hz : Dend j * π = 0 := by
      rw [hπ']
      apply mul_list_prod_eq_zero (Dend j) (1 - Dend j ^ (p - 1))
      · rw [List.mem_ofFn]
        exact ⟨j, rfl⟩
      · intro f hf
        rw [List.mem_ofFn] at hf
        obtain ⟨i, rfl⟩ := hf
        exact (Commute.one_right _).sub_right ((hcomm j i).pow_right _)
      · have hp' : Dend j ^ p = Dend j := AddMonoidHom.ext fun c =>
          (hpow j p c).trans (derivation_iterate_char_eq_self_of_coords p x D hd hD j c)
        rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hpr.one_lt.le, hp', sub_self]
    have h0 : D j (π c) = 0 := by
      show (Dend j * π) c = 0
      rw [hz]
      rfl
    rw [h0, zero_smul]
  · intro g
    rw [hπ']
    apply list_prod_apply_fixed
    intro f hf
    rw [List.mem_ofFn] at hf
    obtain ⟨i, rfl⟩ := hf
    have hDg : D i (g ^ p) = 0 := by
      rw [Derivation.leibniz_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    show g ^ p - (Dend i ^ (p - 1)) (g ^ p) = g ^ p
    rw [hpow, hm, Function.iterate_succ_apply, hDg, Function.iterate_fixed (map_zero (D i)),
      sub_zero]

end GlobalTheory.ProjFn
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.local_ring_image_stalk_map : ∀ {X Y : Scheme.{0}} [IsIntegral X] (π : X ⟶ Y) (y : X) (h : π (genericPoint X) ⤳ π y), Function.Surjective (π.stalkMap y).hom → ∀ c : X.functionField, c ∈ locRing y ↔ ∃ z ∈ stalkIm h, (π.stalkMap (genericPoint X)).hom z = c := by
  first | exact @_root_.GlobalTheory.DI.mem_locRing_iff_exists_stalkIm | exact _root_.GlobalTheory.DI.mem_locRing_iff_exists_stalkIm | (intros; apply _root_.GlobalTheory.DI.mem_locRing_iff_exists_stalkIm <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DI

theorem mem_latSec_iff {X : Scheme.{0}} {V : Type} [AddCommGroup V] (M : X → AddSubgroup V) (U : X.Opens)
    (v : V) : v ∈ latSec M U ↔ ∀ y ∈ U, v ∈ M y := by
  simp only [latSec, AddSubgroup.mem_iInf]

theorem latSec_anti {X : Scheme.{0}} {V : Type} [AddCommGroup V] (M : X → AddSubgroup V) {U U' : X.Opens}
    (h : U' ≤ U) : latSec M U ≤ latSec M U' := fun v hv =>
  (mem_latSec_iff M U' v).2 fun y hy => (mem_latSec_iff M U v).1 hv y (h hy)

theorem forms_le_of_subset_of_subset {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {B B' : Set K}
    {L L' : Set V} (q : ℕ) (hB : B ⊆ B') (hL : L ⊆ L') : forms B L q ≤ forms B' L' q :=
  AddSubgroup.closure_mono fun _ ⟨b, hb, v, hv, e⟩ => ⟨b, hB hb, v, fun k => hL (hv k), e⟩

theorem f_dlog_of_frob {K Kt : Type} [Field K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : Kt →+* K) (F : Kt →+* Kt) (f : Ω[K⁄ℤ] →+ Ω[K⁄ℤ]) (hf : IsF p π F f) (g : Kˣ) (z : Kt)
    (hz : π z = g) (hF : F z = z ^ p) : f (dlog g) = dlog g := by
  have key := hf.2 z 0 (by rw [hF]; ring)
  rw [map_zero, map_zero, add_zero, hz] at key
  have hp := (Fact.out : p.Prime)
  have e1 : ((g : K)⁻¹) ^ p * (g : K) ^ (p - 1) = (g : K)⁻¹ := by
    have hg : (g : K) ≠ 0 := g.ne_zero
    obtain ⟨n, hn⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
    rw [hn, Nat.add_sub_cancel, pow_succ, mul_comm ((g : K)⁻¹ ^ n), mul_assoc, ← mul_pow,
      inv_mul_cancel₀ hg, one_pow, mul_one]
  simp only [dlog, dK, Units.val_inv_eq_inv_val]
  rw [hf.1, key, smul_smul, e1]

end GlobalTheory.DI

namespace GlobalTheory.DI

theorem decomp_of_isLifted : ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] (Z : Set X) {ι : Type} [LinearOrder ι] (U : ι → X.Opens) {n : ℕ} (x : ι → Fin n → X.functionFieldˣ) (W : Finset ι → X.Opens) (G H : CartierDiv X), n < p → (∀ i, genericPoint X ∈ U i) → (∀ i, IsCoord (x i)) → (∀ s : Finset ι, s.Nonempty → ∀ y, y ∈ W s ↔ ∀ i ∈ s, y ∈ U i) → IsLifted p Z U x → (H - p • G).Eff → (∀ q (s : Finset ι) η, η ∈ logSec Z H q (W s) → extD _ η ∈ logSec Z H (q + 1) (W s)) → (∀ (s : Finset ι), ∀ j ∈ s, ∀ γ, IsCartierMap p (x j) γ → CartierAt (extD _) γ (fun a => logSec Z G a (W s)) (fun a => logSec Z H a (W s))) → ∀ a b, HypZero (extD _) (fun q s => logSec Z H q (W s)) (a + b) → CechZero (fun s => logSec Z G a (W s)) b := by
  intro p _ X _ _ Z ι _ U n x W G H hnp hgen hcoord hW hlift hEff hdT hCart a b hHyp
  obtain ⟨Kt, _, π, F, hπ, hF, hz, hlog⟩ := hlift
  choose f hf using fun i => exists_isF_of_flatLift p π (F i) hπ (hF i)
  choose h hh using fun i j => exists_isH_of_isFrob p π (F i) (F j) hπ (hF i) (hF j)
  have hd := GlobalTheory.T.exterior_derivative_is_differential X.functionField
  have hdat := isDatum_of_frobenius_lifts p π F (extD X.functionField) f h hπ hF hd hf hh
  choose γ hγ using fun i => exists_isGamma p (f i) (hf i).1

  have hWmono : ∀ s t : Finset ι, s.Nonempty → s ⊆ t → W t ≤ W s := by
    intro s t hs hst y hy
    exact (hW s hs y).2 fun i hi => (hW t (hs.mono hst) y).1 hy i (hst hi)
  have hgenW : ∀ s : Finset ι, s.Nonempty → genericPoint X ∈ W s := fun s hs =>
    (hW s hs _).2 fun i _ => hgen i
  have hNuniv : ∀ a' (s : Finset ι), s.Nonempty →
      logSec Z G a' (W s) ≤ forms (Set.univ : Set X.functionField) (Set.univ : Set Ω[X.functionField⁄ℤ]) a' := by
    intro a' s hs v hv
    have := (mem_latSec_iff _ _ v).1 hv _ (hgenW s hs)
    exact forms_le_of_subset_of_subset a' (Set.subset_univ _) (Set.subset_univ _) this
  refine GlobalTheory.T.splitting_local_integrality (K := X.functionField) (V := Ω[X.functionField⁄ℤ]) p (extD X.functionField) f h γ
    (P := X) (fun s => {y | ∀ i ∈ s, y ∈ U i}) (fun y => locRing y) (fun y => {c | G.RegularAt y c})
    (fun y => dlog '' {g | LogUnit Z y g}) (fun q s => logSec Z G q (W s)) (fun q s => logSec Z H q (W s))
    hd.toIsOddDer hdat hγ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a b hHyp
  · intro q s t hs hst
    exact latSec_anti _ (hWmono s t hs hst)
  · intro q s t hs hst
    exact latSec_anti _ (hWmono s t hs hst)
  · intro q s v hv
    exact hdT q s v hv
  · intro a' s hs
    exact hNuniv a' s hs
  · intro a' s hs hpa
    obtain ⟨i, -⟩ := id hs
    rw [eq_bot_iff]
    refine (hNuniv a' s hs).trans (le_of_eq ?_)
    exact spanForms_eq_bot_of_lt_card X.functionField n (x i) _ _ a' (hcoord i) (by omega)
  · intro a' s hs y hy v hv
    exact (mem_latSec_iff _ _ v).1 hv y ((hW s hs y).2 hy)
  · intro q s v hs _ hv
    refine (mem_latSec_iff _ _ v).2 fun y hy => ?_
    exact forms_le_of_subset_of_subset q (GlobalTheory.T.regular_functions_pth_power_twist p G H y hEff) subset_rfl (hv y ((hW s hs y).1 hy))
  · rintro s y hy i hi _ ⟨g, hg, rfl⟩
    obtain ⟨hfi, -⟩ := divided_frob_logForm p π F f h s (locRing y) (g : X.functionField) hf hh
      (hlog y s hy g hg)
    obtain ⟨w, hwA, hw⟩ := hfi i hi
    have e : dlog g = ((g : X.functionField))⁻¹ • KaehlerDifferential.D ℤ X.functionField g := by
      simp only [dlog, dK, Units.val_inv_eq_inv_val]
    rw [e, hw g.ne_zero, map_add (f := _), ← e]
    exact AddSubgroup.add_mem _ ((GlobalTheory.T.log_forms_generated_dlog Z y).2 g hg) ((GlobalTheory.T.log_forms_generated_dlog Z y).1 w hwA)
  · rintro s y hy i hi j hj _ ⟨g, hg, rfl⟩
    obtain ⟨-, hhij⟩ := divided_frob_logForm p π F f h s (locRing y) (g : X.functionField) hf hh
      (hlog y s hy g hg)
    have e : dlog g = ((g : X.functionField))⁻¹ • KaehlerDifferential.D ℤ X.functionField g := by
      simp only [dlog, dK, Units.val_inv_eq_inv_val]
    rw [e]
    exact hhij i hi j hj
  · intro s j hj
    refine hCart s j hj (γ j) ⟨(hγ j).1, fun l => ?_⟩
    obtain ⟨z, hzx, hzF⟩ := hz j l
    rw [(hγ j).2, f_dlog_of_frob p π (F j) (f j) (hf j) (x j l) z hzx hzF]

end GlobalTheory.DI
end
end
