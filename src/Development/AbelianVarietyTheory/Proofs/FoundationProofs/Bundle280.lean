module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle095
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle171
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle169
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle273
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
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
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle004
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases

@[expose] public section

section

open GlobalTheory.K5 GlobalTheory.KumDlog

noncomputable section

namespace GlobalTheory.KumDlog.AlmostGal

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

def Rep (C : Subalgebra (O0 p) Ω) (H : Subgroup (Gal p Ω)) (F : Gal p Ω → Ω) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (u v : ι → Ω), (∀ k, u k ∈ C) ∧ (∀ k, v k ∈ C) ∧
    ∀ h ∈ H, F h = ∑ k, u k * h (v k)

variable {C : Subalgebra (O0 p) Ω} {H : Subgroup (Gal p Ω)}

theorem rep_congr {F G : Gal p Ω → Ω} (hF : Rep C H F) (e : ∀ h ∈ H, G h = F h) : Rep C H G := by
  obtain ⟨ι, hι, u, v, hu, hv, hF⟩ := hF
  exact ⟨ι, hι, u, v, hu, hv, fun h hh => (e h hh).trans (hF h hh)⟩

theorem rep_const {c : Ω} (hc : c ∈ C) : Rep C H (fun _ => c) :=
  ⟨Unit, inferInstance, fun _ => c, fun _ => 1, fun _ => hc, fun _ => C.one_mem,
    fun h _ => by simp⟩

theorem rep_eval {x : Ω} (hx : x ∈ C) : Rep C H (fun h => h x) :=
  ⟨Unit, inferInstance, fun _ => 1, fun _ => x, fun _ => C.one_mem, fun _ => hx,
    fun h _ => by simp⟩

theorem rep_add {F G : Gal p Ω → Ω} (hF : Rep C H F) (hG : Rep C H G) :
    Rep C H (fun h => F h + G h) := by
  obtain ⟨ι, _, u, v, hu, hv, hF⟩ := hF
  obtain ⟨ι', _, u', v', hu', hv', hG⟩ := hG
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim u u', Sum.elim v v', ?_, ?_, fun h hh => ?_⟩
  · rintro (k | k)
    · exact hu k
    · exact hu' k
  · rintro (k | k)
    · exact hv k
    · exact hv' k
  · show F h + G h = _
    rw [Fintype.sum_sum_type, hF h hh, hG h hh]
    simp

theorem rep_mul {F G : Gal p Ω → Ω} (hF : Rep C H F) (hG : Rep C H G) :
    Rep C H (fun h => F h * G h) := by
  obtain ⟨ι, _, u, v, hu, hv, hF⟩ := hF
  obtain ⟨ι', _, u', v', hu', hv', hG⟩ := hG
  refine ⟨ι × ι', inferInstance, fun k => u k.1 * u' k.2, fun k => v k.1 * v' k.2,
    fun k => C.mul_mem (hu _) (hu' _), fun k => C.mul_mem (hv _) (hv' _), fun h hh => ?_⟩
  show F h * G h = ∑ k : ι × ι', u k.1 * u' k.2 * h (v k.1 * v' k.2)
  rw [hF h hh, hG h hh, Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul]; ring

theorem rep_prod {α : Type*} (s : Finset α) (F : α → Gal p Ω → Ω)
    (hF : ∀ a ∈ s, Rep C H (F a)) : Rep C H (fun h => ∏ a ∈ s, F a h) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (rep_const (H := H) C.one_mem)
  | insert a s ha ih =>
    refine rep_congr (rep_mul (hF a (by simp)) (ih fun b hb => hF b (by simp [hb])))
      fun h _ => ?_
    rw [Finset.prod_insert ha]

theorem gal_mem_C {T : Tower p Ω} {n : ℕ} {r : Ω}
    (hH : ∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) {g : Gal p Ω} (hg : g ∈ Hinf T)
    {x : Ω} (hx : x ∈ FixI (Hfix T r)) : g x ∈ FixI (Hfix T r) := by
  refine ⟨int_gal g hx.1, fun h hh => ?_⟩
  obtain ⟨hhinf, hhr⟩ := mem_Hfix.1 hh
  have hgr : h (g r) = g r := by
    obtain ⟨i, hi⟩ := hH g hg
    rw [hi, map_mul, map_pow, (mem_Hinf.1 hhinf n).1, hhr]
  have hk : g⁻¹ * h * g ∈ Hfix T r := by
    refine mem_Hfix.2 ⟨(Hinf T).mul_mem ((Hinf T).mul_mem ((Hinf T).inv_mem hg) hhinf) hg, ?_⟩
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hgr, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  have e := hx.2 _ hk
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] at e
  exact e

theorem eq_on_C {T : Tower p Ω} {r : Ω} {g h : Gal p Ω} (hg : g ∈ Hinf T) (hh : h ∈ Hinf T)
    (hr : h r = g r) {x : Ω} (hx : x ∈ FixI (Hfix T r)) : h x = g x := by
  have hk : g⁻¹ * h ∈ Hfix T r := by
    refine mem_Hfix.2 ⟨(Hinf T).mul_mem ((Hinf T).inv_mem hg) hh, ?_⟩
    rw [AlgEquiv.mul_apply, hr, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  have e := hx.2 _ hk
  rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] at e
  exact e

theorem rep_of_span {T : Tower p Ω} {n : ℕ} {r : Ω}
    (hH : ∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) {g : Gal p Ω} (hg : g ∈ Hinf T) {y : Ω}
    (hy : y ∈ Submodule.span (FixI (Hfix T r)) {y : Ω | ∃ x ∈ FixI (Hfix T r), y = g x - x}) :
    ∃ F : Gal p Ω → Ω, Rep (FixI (Hfix T r)) (Hinf T) F ∧ F 1 = y ∧
      ∀ h ∈ Hinf T, h r = g r → F h = 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨fun h => g x + (-1) * h x, rep_add (rep_const (gal_mem_C hH hg hx))
      (rep_mul (rep_const (neg_mem (Subalgebra.one_mem _))) (rep_eval hx)), ?_, ?_⟩
    · simp only [AlgEquiv.one_apply]; ring
    · intro h hh hr
      simp only [eq_on_C hg hh hr hx]; ring
  | zero => exact ⟨fun _ => 0, rep_const (Subalgebra.zero_mem _), rfl, fun _ _ _ => rfl⟩
  | add y z _ _ ihy ihz =>
    obtain ⟨F, hF, hF1, hF0⟩ := ihy
    obtain ⟨G, hG, hG1, hG0⟩ := ihz
    exact ⟨fun h => F h + G h, rep_add hF hG, by simp [hF1, hG1],
      fun h hh hr => by simp [hF0 h hh hr, hG0 h hh hr]⟩
  | smul a y _ ih =>
    obtain ⟨F, hF, hF1, hF0⟩ := ih
    exact ⟨fun h => (a : Ω) * F h, rep_mul (rep_const a.2) hF,
      by simp [hF1, Subalgebra.smul_def], fun h hh hr => by simp [hF0 h hh hr]⟩

end GlobalTheory.KumDlog.AlmostGal


open GlobalTheory.KumDlog.AlmostGal in
theorem GlobalTheory.KumDlog.almostGal_coord : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω]
    [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ) (r : Ω), IsInt (p := p) r →
    (∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) →
  ∃ (ι : Type) (_ : Fintype ι) (u v : ι → Ω), (∀ k, u k ∈ FixI (Hfix T r)) ∧
    (∀ k, v k ∈ FixI (Hfix T r)) ∧
  ∑ k, u k * v k = (p : Ω) ∧ ∀ h ∈ Hinf T, h r ≠ r → ∑ k, u k * h (v k) = 0 := by
  intro p _ hp2 Ω _ _ hclo T n r hr hH
  classical
  have hp : p.Prime := Fact.out
  set τ : Ω := T.ζ (n + 1) - 1 with hτ
  have hτ0 : τ ≠ 0 :=
    sub_ne_zero.2 ((T.prim (n + 1)).ne_one (Nat.one_lt_pow (by omega) hp.one_lt))

  set W : Finset Ω := ((Finset.range (p ^ n)).image (fun i => T.ζ n ^ i * r)).filter
    (fun w => w ≠ r ∧ ∃ g ∈ Hinf T, g r = w) with hW
  have hF : ∀ w ∈ W, ∃ F : Gal p Ω → Ω, Rep (FixI (Hfix T r)) (Hinf T) F ∧ F 1 = τ ∧
      ∀ h ∈ Hinf T, h r = w → F h = 0 := by
    intro w hw
    obtain ⟨hwr, g, hg, hgw⟩ := (Finset.mem_filter.1 hw).2
    obtain ⟨F, hF, hF1, hF0⟩ := rep_of_span hH hg
      (GlobalTheory.T.zeta_sub_one_mem_span_galois_differences p hp2 Ω hclo T n r hr hH (n + 1) (by omega) g hg (hgw ▸ hwr))
    exact ⟨F, hF, hF1, fun h hh e => hF0 h hh (e.trans hgw.symm)⟩
  choose! F hFr hF1 hF0 using hF
  set s := W.card with hs
  have hsle : s ≤ Nat.totient (p ^ (n + 1)) := by
    rw [Nat.totient_prime_pow hp (by omega), Nat.add_sub_cancel]
    calc s ≤ ((Finset.range (p ^ n)).image (fun i => T.ζ n ^ i * r)).card :=
          Finset.card_filter_le _ _
      _ ≤ (Finset.range (p ^ n)).card := Finset.card_image_le
      _ = p ^ n := Finset.card_range _
      _ ≤ p ^ n * (p - 1) := Nat.le_mul_of_pos_right _ (by have := hp.two_le; omega)
  set c : Ω := (p : Ω) / τ ^ s with hc
  have hcC : c ∈ FixI (Hfix T r) := by
    refine ⟨GlobalTheory.T.isInt_prime_div_rootOfUnity_sub_one_pow p Ω T (n + 1) s (by omega) hsle, fun g hg => ?_⟩
    have hz : g (T.ζ (n + 1)) = T.ζ (n + 1) := (mem_Hinf.1 (mem_Hfix.1 hg).1 (n + 1)).1
    rw [hc, map_div₀, map_pow, hτ, map_sub, map_one, hz, map_natCast]
  have hrep : Rep (FixI (Hfix T r)) (Hinf T) (fun h => c * ∏ w ∈ W, F w h) :=
    rep_mul (rep_const hcC) (rep_prod W F hFr)
  obtain ⟨ι, hι, u, v, hu, hv, he⟩ := hrep
  refine ⟨ι, hι, u, v, hu, hv, ?_, fun h hh hhr => ?_⟩
  · have e := he 1 (Hinf T).one_mem
    simp only [AlgEquiv.one_apply] at e
    rw [← e, Finset.prod_congr rfl hF1, Finset.prod_const, ← hs, hc,
      div_mul_cancel₀ _ (pow_ne_zero _ hτ0)]
  · rw [← he h hh]
    obtain ⟨i, hi⟩ := hH h hh
    have hmod : h r = T.ζ n ^ (i % p ^ n) * r := by
      rw [hi]
      conv_lhs => rw [← Nat.div_add_mod i (p ^ n), pow_add, pow_mul, (T.prim n).pow_eq_one,
        one_pow, one_mul]
    have hmem : h r ∈ W := by
      refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨i % p ^ n, Finset.mem_range.2
        (Nat.mod_lt _ (ppow_pos n)), hmod.symm⟩, hhr, h, hh, rfl⟩
    show c * ∏ w ∈ W, F w h = 0
    rw [Finset.prod_eq_zero hmem (hF0 _ hmem h hh rfl), mul_zero]
end
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem zmf_congr_cop {k l : ℕ} (u v : ℤ → ℂ) (F G : ℕ → ℕ → ℂ)
    (h : ∀ x y : ℕ, ¬ l ∣ x → ¬ l ∣ y → F x y = G x y) : Zm k l u v F = Zm k l u v G := by
  funext n
  unfold Zm
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  split_ifs with hp
  · rfl
  · push_neg at hp
    rw [Nat.mem_divisorsAntidiagonal] at hx hy
    have hx' : ¬ l ∣ x.1 := fun hd => hp.1 (hx.1 ▸ dvd_mul_of_dvd_left hd _)
    have hy' : ¬ l ∣ y.2 := fun hd => hp.2 (hy.1 ▸ dvd_mul_of_dvd_right hd _)
    rw [h _ _ hx' hy']

theorem zmf_sum_smul {ι : Type*} (s : Finset ι) (k l : ℕ) (u v : ℤ → ℂ) (c : ι → ℂ) (G : ι → ℕ → ℕ → ℂ) :
    Zm k l u v (fun x y => ∑ i ∈ s, c i * G i x y) = ∑ i ∈ s, c i • Zm k l u v (G i) := by
  funext n
  simp only [Zm, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs
  · simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    ring

theorem zmf_mf_sum {ι : Type*} (s : Finset ι) (k L : ℕ) (χ : ℤ → ℂ) (g : ι → ℕ → ℂ)
    (h : ∀ i ∈ s, MF k L χ (g i)) : MF k L χ (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (GlobalTheory.T.modularFormCoeffSeq_linear_structure k L χ).1
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact ((GlobalTheory.T.modularFormCoeffSeq_linear_structure k L χ).2.1 _ _ (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))).1

theorem zm_fun_mf : ∀ (k N l m : ℕ) (ε θ ν : DirichletCharacter ℂ N) (f : ZMod (l ^ m) → ℂ), 3 ≤ k → Odd k → 0 < N → l.Prime → 1 ≤ m → ¬ l ∣ N → ε = θ⁻¹ * ν → ν (-1) = -θ (-1) → (∀ x, f (-x) = θ (-1) * f x) → MF k (N * l ^ (m + 1)) (ch ε) (Zm k l (hat θ) (ch ν) (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹))) := by
  intro k N l m ε θ ν f hk hodd hN hl hm hlN hε hν hf
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
  set φ : ℂ := ((l ^ m).totient : ℂ) with hφ
  have hφ0 : φ ≠ 0 := by
    rw [hφ]; exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (pow_ne_zero _ hl.ne_zero))).ne'
  set c : DirichletCharacter ℂ (l ^ m) → ℂ := fun ψ => φ⁻¹ * ∑ u : (ZMod (l ^ m))ˣ, f u * ψ⁻¹ u with hc
  have hinv : ∀ (ψ : DirichletCharacter ℂ (l ^ m)) (u : (ZMod (l ^ m))ˣ),
      ψ⁻¹ (u : ZMod (l ^ m)) = ψ ((u : ZMod (l ^ m))⁻¹) := by
    intro ψ u; rw [MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]
  have hexp : ∀ w : (ZMod (l ^ m))ˣ, f w = ∑ ψ, c ψ * ψ w := by
    intro w
    calc f w = φ⁻¹ * (f w * φ) := by field_simp
      _ = φ⁻¹ * ∑ u : (ZMod (l ^ m))ˣ, f u * (if (u : ZMod (l ^ m)) = w then φ else 0) := by
          congr 1
          simp only [Units.val_inj, mul_ite, mul_zero]
          rw [Finset.sum_ite_eq']; simp
      _ = φ⁻¹ * ∑ u : (ZMod (l ^ m))ˣ, f u * ∑ ψ : DirichletCharacter ℂ (l ^ m), ψ ((u : ZMod (l ^ m))⁻¹) * ψ w := by
          congr 1
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ u.isUnit]
      _ = ∑ ψ, c ψ * ψ w := by
          simp only [hc, hinv, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun ψ _ => Finset.sum_congr rfl fun u _ => ?_
          ring
  have hquo : Zm k l (hat θ) (ch ν) (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹)) = Zm k l (hat θ) (ch ν)
      (fun x y => ∑ ψ : DirichletCharacter ℂ (l ^ m), c ψ * (ch ψ x * ch ψ⁻¹ y * ((y : ℂ) / x) ^ 0)) := by
    apply zmf_congr_cop
    intro x y hx hy
    have cx : Nat.Coprime x (l ^ m) := (Nat.Coprime.pow_left m ((hl.coprime_iff_not_dvd).2 hx)).symm
    have cy : Nat.Coprime y (l ^ m) := (Nat.Coprime.pow_left m ((hl.coprime_iff_not_dvd).2 hy)).symm
    set ux := ZMod.unitOfCoprime x cx
    set uy := ZMod.unitOfCoprime y cy
    have ex : ((x : ℤ) : ZMod (l ^ m)) = ux := by simp [ux, ZMod.coe_unitOfCoprime]
    have ey : ((y : ℤ) : ZMod (l ^ m)) = uy := by simp [uy, ZMod.coe_unitOfCoprime]
    have ex' : (x : ZMod (l ^ m)) = ux := by simp [ux, ZMod.coe_unitOfCoprime]
    have ey' : (y : ZMod (l ^ m)) = uy := by simp [uy, ZMod.coe_unitOfCoprime]
    simp only [ch, ex, ey, ex', ey', pow_zero, mul_one, hinv]
    rw [ZMod.inv_coe_unit, ← Units.val_mul, hexp]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [← map_mul, ← Units.val_mul]
  rw [hquo, zmf_sum_smul]
  apply zmf_mf_sum
  intro ψ _
  have hsq : ∀ {M : ℕ} (χ : DirichletCharacter ℂ M), χ (-1) * χ (-1) = 1 := by
    intro M χ; rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have hh := (GlobalTheory.T.dirichletCharFiniteFourierTransform_properties).1 N θ hN
  by_cases hψ : ψ (-1) = θ (-1)
  · have h1 : ψ (-1) * θ (-1) = (-1) ^ (k - 1 - 0) := by
      obtain ⟨r, rfl⟩ := hodd
      rw [hψ, hsq, show 2 * r + 1 - 1 - 0 = 2 * r by omega, pow_mul]; norm_num
    have h2 : ψ (-1) * ν (-1) = (-1) ^ (0 + 1) := by
      rw [hψ, hν, mul_neg, hsq]; norm_num
    exact ((GlobalTheory.T.modularFormCoeffSeq_linear_structure k _ (ch ε)).2.2.1 (c ψ) _
      (GlobalTheory.T.muModelProduct_isModularFormCoeffSeq_locallyAlgebraic k 0 N l m ε (hat θ) θ ν ψ (by omega) hN hl hm hlN hh.1 hh.2.1 hε h1 h2)).1
  · have hc0 : c ψ = 0 := by
      have hpm : ∀ {M : ℕ} (χ : DirichletCharacter ℂ M), χ (-1) = 1 ∨ χ (-1) = -1 := by
        intro M χ
        have := hsq χ
        have h' : (χ (-1) - 1) * (χ (-1) + 1) = 0 := by linear_combination this
        rcases mul_eq_zero.1 h' with h | h
        · left; linear_combination h
        · right; linear_combination h
      have hprod : θ (-1) * ψ⁻¹ (-1) = -1 := by
        have hi : ψ⁻¹ (-1) = ψ (-1) := by
          rw [MulChar.inv_apply, show (-1 : ZMod (l ^ m)) = ((-1 : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) by simp, Ring.inverse_unit, inv_neg_one]
        rw [hi]
        rcases hpm θ with h | h <;> rcases hpm ψ with h' | h' <;> rw [h, h'] at hψ ⊢
        all_goals first | exact absurd rfl hψ | norm_num
      set S := ∑ u : (ZMod (l ^ m))ˣ, f u * ψ⁻¹ u with hS
      have hS' : S = - S := by
        calc S = ∑ u : (ZMod (l ^ m))ˣ, f ((-u : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) * ψ⁻¹ ((-u : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) :=
              (Fintype.sum_equiv (Equiv.neg _) _ _ (fun _ => rfl)).symm
          _ = ∑ u : (ZMod (l ^ m))ˣ, (θ (-1) * ψ⁻¹ (-1)) * (f u * ψ⁻¹ u) := by
              refine Finset.sum_congr rfl fun u _ => ?_
              rw [Units.val_neg, hf, neg_eq_neg_one_mul (u : ZMod (l ^ m)), map_mul]
              ring
          _ = - S := by rw [← Finset.mul_sum, hprod, neg_one_mul]
      have : S = 0 := by linear_combination hS' / 2
      simp [hc, ← hS, this]
    rw [hc0, zero_smul]
    exact (GlobalTheory.T.modularFormCoeffSeq_linear_structure k _ (ch ε)).1

end GlobalTheory.EisM
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles

namespace GlobalTheory.AntiRam

section General

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem valuation_comap_lt_one (c : Ω ≃+* Ω) (A : ValuationSubring Ω) (y : Ω) :
    (A.comap c.symm.toRingHom).valuation y < 1 ↔ A.valuation (c.symm y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ValuationSubring.mem_comap,
    ValuationSubring.mem_comap, ← map_inv₀, map_eq_zero_iff _ c.symm.injective]
  rfl

theorem exists_conj_mem_Ine (c : Ω ≃+* Ω) (κ : E → E)
    (hc : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (κ x)) (hκ : ∀ x, κ (κ x) = x)
    (A : ValuationSubring Ω) (σ : G E Ω) (hσ : σ ∈ Ine (F := E) A) :
    ∃ σ' : G E Ω, (∀ x, σ' x = c (σ (c.symm x))) ∧ σ' ∈ Ine (F := E) (A.comap c.symm.toRingHom) := by
  have hs : ∀ x, c.symm (algebraMap E Ω x) = algebraMap E Ω (κ x) := fun x => by
    rw [RingEquiv.symm_apply_eq, hc, hκ]
  let σ' : Ω ≃ₐ[E] Ω := AlgEquiv.ofRingEquiv (f := (c.symm.trans (σ : Ω ≃ₐ[E] Ω).toRingEquiv).trans c)
    (fun x => by
      show c (σ (c.symm (algebraMap E Ω x))) = _
      rw [hs, AlgEquiv.commutes, hc, hκ])
  have h' : ∀ x, σ' x = c (σ (c.symm x)) := fun _ => rfl
  have hm : ∀ y, y ∈ A.comap c.symm.toRingHom ↔ c.symm y ∈ A := fun _ => Iff.rfl
  refine ⟨σ', h', ?_, fun x hx => ?_⟩
  · change σ' ∈ Dec (F := E) _
    rw [mem_Dec]
    ext y
    obtain ⟨z, rfl⟩ := σ'.surjective y
    rw [← AlgEquiv.smul_def σ' z, ValuationSubring.smul_mem_pointwise_smul_iff, AlgEquiv.smul_def,
      hm, hm, h', RingEquiv.symm_apply_apply, apply_mem_iff_of_mem_Dec hσ.1]
  · rw [valuation_comap_lt_one, map_sub, h', RingEquiv.symm_apply_apply]
    refine hσ.2 _ ?_
    rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
    exact (hm x).1 hx

end General

theorem ramExactly_conj : ∀ (D : D7) (M : Type) [CommGroup M] (ψ : G D.host.E D.nd.Om →* M) (Q : Set (PlE D.host)), AntiHom D.ntw.cc ψ → RamExactly ψ Q → ∀ P ∈ Q, ∀ P' : PlE D.host, IsConjPl D.host P P' → P' ∈ Q := by
  intro D M _ ψ Q hA hR P hP P' hPP
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hst : ∀ x : D.host.E, IsCMField.complexConj D.host.E x = D.host.conj x :=
    bridge_star_holds D.R D.host
  obtain ⟨⟨j, hj⟩, -⟩ := D.ntw.cc_cm
  have hκ : ∀ x, D.host.conj (D.host.conj x) = x := fun x => by
    rw [← hst, ← hst, IsCMField.complexConj_apply_apply]
  have hc : ∀ x, D.ntw.cc (algebraMap D.host.E D.nd.Om x) =
      algebraMap D.host.E D.nd.Om (D.host.conj x) := fun x => by
    apply j.injective
    rw [hj, ← hst]
    exact (IsCMField.complexEmbedding_complexConj D.host.E
      (j.comp (algebraMap D.host.E D.nd.Om)) x).symm
  have hs : ∀ x, D.ntw.cc.symm (algebraMap D.host.E D.nd.Om x) =
      algebraMap D.host.E D.nd.Om (D.host.conj x) := fun x => by
    rw [RingEquiv.symm_apply_eq, hc, hκ]
  have hpl : IsPlaceOver (D.nd.plOm.1 P) P := D.nd.plOm.2 P
  obtain ⟨σ, hσ, hne⟩ := (hR P _ hpl).2 hP
  obtain ⟨σ', h1, h2⟩ := exists_conj_mem_Ine D.ntw.cc (fun x => D.host.conj x) hc hκ _ σ hσ
  refine (hR P' _ (fun y => ?_)).1 ⟨σ', h2, ?_⟩
  · have hint : IsIntegral ℤ (D.host.conj (y : D.host.E)) := by
      rw [← hst]
      exact (RingOfIntegers.isIntegral_coe y).map
        ((IsCMField.complexConj D.host.E).toRingEquiv.toRingHom.toIntAlgHom)
    rw [valuation_comap_lt_one, hs, ← hPP ⟨_, hint⟩ y (hκ _).symm]
    exact hpl ⟨_, hint⟩
  · rw [hA σ σ' h1]
    exact inv_ne_one.2 hne

end GlobalTheory.AntiRam
end
