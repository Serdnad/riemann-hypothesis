module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle039
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Subrepresentation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle053
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle026
public import Mathlib.NumberTheory.ModularForms.Basic
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005

@[expose] public section

section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

theorem _root_.GlobalTheory.T.unramified_integers_adic_complete : ∀ (p : ℕ) [Fact p.Prime], IsAdicComplete (Ideal.span {(p : O0 p)}) (O0 p) := by
  first | exact @GlobalTheory.K5.o0_isAdicComplete_span_p | exact GlobalTheory.K5.o0_isAdicComplete_span_p | (intros; apply GlobalTheory.K5.o0_isAdicComplete_span_p <;> assumption)
end

section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

noncomputable section

namespace GlobalTheory.K5.LauZ

variable (p : ℕ) [hp : Fact p.Prime]

def red : Lau p →+* LaurentSeries (ZMod p) where
  toFun f := f.map (PadicInt.toZMod (p := p)).toNonUnitalRingHom
  map_one' := by
    ext n
    show PadicInt.toZMod ((1 : Lau p).coeff n) = (1 : LaurentSeries (ZMod p)).coeff n
    rw [HahnSeries.coeff_one, HahnSeries.coeff_one]
    split_ifs <;> simp
  map_mul' x y := HahnSeries.map_mul _
  map_zero' := by ext n; simp
  map_add' x y := by ext n; simp

theorem red_coeff (f : Lau p) (n : ℤ) : (red p f).coeff n = PadicInt.toZMod (f.coeff n) := rfl

def lift (F : LaurentSeries (ZMod p)) : Lau p :=
  ⟨fun n => ((F.coeff n).val : ℤ_[p]), F.isPWO_support'.mono fun n hn => by
    simp only [Function.mem_support] at hn ⊢
    intro h; apply hn; rw [h]; simp⟩

theorem red_lift (F : LaurentSeries (ZMod p)) : red p (lift p F) = F := by
  ext n
  rw [red_coeff]
  show PadicInt.toZMod (((F.coeff n).val : ℕ) : ℤ_[p]) = F.coeff n
  rw [map_natCast, ZMod.natCast_zmod_val]

theorem red_single (a : ℤ) : red p (HahnSeries.single a (1 : ℤ_[p])) = HahnSeries.single a (1 : ZMod p) := by
  ext n
  rw [red_coeff]
  by_cases h : n = a
  · subst h; simp
  · simp [HahnSeries.coeff_single_of_ne h]

theorem exists_pow_comb (f : Lau p) : ∃ (g : Fin p → Lau p) (h : Lau p),
    f = ∑ j : Fin p, HahnSeries.single ((j : ℕ) : ℤ) (1 : ℤ_[p]) * g j ^ p + (p : Lau p) * h := by
  obtain ⟨G, hG⟩ := GlobalTheory.T.laurentSeries_eq_sum_single_mul_pow_prime p (red p f)
  set S : Lau p := ∑ j : Fin p, HahnSeries.single ((j : ℕ) : ℤ) (1 : ℤ_[p]) * lift p (G j) ^ p
  have hS : red p S = red p f := by
    rw [hG]

    simp only [S, map_sum, map_mul, map_pow, red_single, red_lift]
  have h0 : (f - S).map (PadicInt.toZMod (p := p)).toNonUnitalRingHom = 0 := by
    show red p (f - S) = 0
    rw [map_sub, hS, sub_self]
  obtain ⟨h, hh⟩ := (GlobalTheory.K5.Basic.dvd_iff_map p (f - S)).2 h0
  exact ⟨fun j => lift p (G j), h, by rw [← hh, add_sub_cancel]⟩

end GlobalTheory.K5.LauZ

end
end

section

open GlobalTheory.K5 GlobalTheory.KumDlog

namespace GlobalTheory.KumExpo

theorem exponents : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (T : Tower p Ω) (n m : ℕ), 2 * n ≤ m → ∀ lz lq : Gal p Ω → ZMod (p ^ n),
  IsKum T n (Gn T n) (T.ζ (2 * n)) lz → IsKum T n (Gn T n) (T.qq (2 * n)) lq → ∀ g ∈ Gn T n,
  ∃ (i j : ℕ) (s t : ℤ), g (T.ζ m) = T.ζ m ^ i ∧ g (T.qq m) = T.ζ m ^ j * T.qq m ∧
    (i : ℤ) = 1 + p ^ n * ((lz g).val : ℤ) + p ^ (2 * n) * s ∧ (j : ℤ) = p ^ n * ((lq g).val : ℤ) + p ^ (2 * n) * t := by
  intro p _ Ω _ _ T n m hm lz lq hz hq g hg
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm

  have h1 : (g (T.ζ (2 * n + k))) ^ (p ^ (2 * n + k)) = 1 := by
    rw [← map_pow, (T.prim _).pow_eq_one, map_one]
  obtain ⟨i, -, hi⟩ := (T.prim _).eq_pow_of_pow_eq_one h1
  have hqne := qq_ne T (2 * n + k)
  have h2 : (g (T.qq (2 * n + k)) / T.qq (2 * n + k)) ^ (p ^ (2 * n + k)) = 1 := by
    rw [div_pow, ← map_pow, kummerTower_qq_pow_level_eq_q, AlgEquiv.commutes, ← kummerTower_qq_pow_level_eq_q T (2 * n + k),
      div_self (pow_ne_zero _ hqne)]
  obtain ⟨j, -, hj⟩ := (T.prim _).eq_pow_of_pow_eq_one h2
  have hj' : g (T.qq (2 * n + k)) = T.ζ (2 * n + k) ^ j * T.qq (2 * n + k) := by
    rw [hj, div_mul_cancel₀ _ hqne]

  have ez : T.ζ (2 * n + k) ^ (p ^ k) = T.ζ (2 * n) := zeta_pow T (2 * n) k
  have eq' : T.qq (2 * n + k) ^ (p ^ k) = T.qq (2 * n) := qq_pow T (2 * n) k
  have ezn : T.ζ (2 * n) ^ (p ^ n) = T.ζ n := by
    have := zeta_pow T n n
    rwa [← two_mul] at this
  have gz : g (T.ζ (2 * n)) = T.ζ (2 * n) ^ i := by
    rw [← ez, map_pow, ← hi, ← pow_mul, ← pow_mul, Nat.mul_comm i]
  have gq : g (T.qq (2 * n)) = T.ζ (2 * n) ^ j * T.qq (2 * n) := by
    rw [← eq', map_pow, hj', mul_pow, ← pow_mul, mul_comm j, pow_mul, ez]
  have kz := hz g hg
  have kq := hq g hg
  rw [gz, ← ezn, ← pow_mul, ← pow_succ] at kz
  rw [gq, ← ezn, ← pow_mul] at kq
  have kq' := mul_right_cancel₀ (qq_ne T (2 * n)) kq
  rw [GlobalTheory.K5.Basic.zeta_pow_eq_iff] at kz kq'
  rw [Nat.modEq_iff_dvd] at kz kq'
  obtain ⟨s, hs⟩ := kz
  obtain ⟨t, ht⟩ := kq'
  refine ⟨i, j, -s, -t, hi.symm, hj', ?_, ?_⟩
  · push_cast at hs ⊢
    linear_combination -hs
  · push_cast at ht ⊢
    linear_combination -ht

end GlobalTheory.KumExpo
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem twKer_unipB_le_of_stages : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (r + t)) k) V) (P : Submodule ℂ V), twKer π (unipRad k (two (stdSum (rfl : r + t = r + t)))) 1 ≤ P → (∀ u ∈ unipB k (Fin r), ∀ w, π (emb₂ k (stdSum (rfl : r + t = r + t)) (u, 1)) w - w ∈ P) → (∀ u ∈ unipB k (Fin t), ∀ w, π (emb₂ k (stdSum (rfl : r + t = r + t)) (1, u)) w - w ∈ P) → twKer π (unipB k (Fin (r + t))) 1 ≤ P := by
  intro k _ _ _ _ r t V _ _ π P h0 h1 h2
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨u, hu⟩, w, rfl⟩
  set e := stdSum (rfl : r + t = r + t) with he
  obtain ⟨hl, hd⟩ := (mem_unipB k).1 hu
  have hp : u ∈ parab k (two e) := (mem_parab_two k).2 fun j i => hl _ _ (by
    rw [Fin.lt_def, he, stdSum_inl, stdSum_inr]; omega)
  obtain ⟨y, hy, hdec⟩ := exists_levi_mul_unip k (two e) ⟨u, hp⟩
  set a : GL (Fin r) k := leviProj k (two e) ⟨u, hp⟩ false with ha
  set b : GL (Fin t) k := leviProj k (two e) ⟨u, hp⟩ true with hb
  have hau : a ∈ unipB k (Fin r) := (mem_unipB k).2 ⟨fun i j hij => hl (e (.inl i)) (e (.inl j)) (by
    rw [Fin.lt_def, he, stdSum_inl, stdSum_inl]; exact hij), fun i => hd (e (.inl i))⟩
  have hbu : b ∈ unipB k (Fin t) := (mem_unipB k).2 ⟨fun i j hij => hl (e (.inr i)) (e (.inr j)) (by
    rw [Fin.lt_def, he, stdSum_inr, stdSum_inr]; exact Nat.add_lt_add_left hij r), fun i => hd (e (.inr i))⟩
  have hlev : leviEmb k (two e) (leviProj k (two e) ⟨u, hp⟩) = emb₂ k e (a, 1) * emb₂ k e (1, b) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    show _ = leviEmb k (two e) (leviTwo k _ _ (a, b))
    congr 1
    funext x
    cases x <;> rfl
  have hdec' : u = emb₂ k e (a, 1) * emb₂ k e (1, b) * y := by rw [← hlev]; exact hdec
  have h3 : π y w - w ∈ P := h0 (Submodule.subset_span ⟨⟨y, hy⟩, w, by simp⟩)
  have h4 := P.add_mem (P.add_mem (h1 a hau (π (emb₂ k e (1, b)) (π y w))) (h2 b hbu (π y w))) h3
  have h5 : π u w - w ∈ P := by
    rw [hdec', map_mul, map_mul]
    simpa using h4
  simpa using h5

end GlobalTheory.PsType
end

section

namespace GlobalTheory.AdmissibleProjection

open GlobalTheory.UnitarySemisimple

variable {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W]

def stab (ρ : Representation ℂ H W) (v : W) : Subgroup H where
  carrier := {g | ρ g v = v}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha]
      _ = v := rho_inv_rho ρ a v

theorem orbit_finite [TopologicalSpace H] [IsTopologicalGroup H] (ρ : Representation ℂ H W)
    (hsm : ∀ w, IsOpen {k : H | ρ k w = w}) (K : Subgroup H) (hK : IsCompact (K : Set H))
    (w : W) : (Set.range fun k : K => ρ k w).Finite := by
  have hopen : ∀ i : K, IsOpen {h : H | ρ h w = ρ (i : H) w} := by
    intro i
    have e : {h : H | ρ h w = ρ (i : H) w} = (fun h => (i : H)⁻¹ * h) ⁻¹' {h | ρ h w = w} := by
      ext h
      simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul, Module.End.mul_apply]
      constructor
      · intro e; rw [e, rho_inv_rho]
      · intro e
        calc ρ h w = ρ (i : H) (ρ (i : H)⁻¹ (ρ h w)) := (rho_rho_inv ρ _ _).symm
          _ = ρ (i : H) w := by rw [e]
    rw [e]
    exact (hsm w).preimage (continuous_const_mul _)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun i : K => {h : H | ρ h w = ρ (i : H) w}) hopen
    (fun h hh => Set.mem_iUnion.2 ⟨⟨h, hh⟩, rfl⟩)
  refine (t.finite_toSet.image (fun i : K => ρ (i : H) w)).subset ?_
  rintro _ ⟨k, rfl⟩
  obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.1 (ht k.2)
  exact ⟨i, hi, hki.symm⟩

theorem hadm_of [TopologicalSpace H] [IsTopologicalGroup H] (ρ : Representation ℂ H W)
    (hK0 : ∃ K : Subgroup H, IsOpen (K : Set H) ∧ IsCompact (K : Set H))
    (hsm : ∀ w, IsOpen {k : H | ρ k w = w})
    (hfd : ∀ K : Subgroup H, IsOpen (K : Set H) → FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K)) :
    ∀ v, ∃ K : Subgroup H, (∀ k ∈ K, ρ k v = v) ∧ FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K) ∧
      ∀ w, (Set.range fun k : K => ρ k w).Finite := by
  obtain ⟨K₀, hop, hco⟩ := hK0
  intro v
  refine ⟨K₀ ⊓ stab ρ v, fun k hk => hk.2, hfd _ ?_, fun w => ?_⟩
  · rw [Subgroup.coe_inf]; exact hop.inter (hsm v)
  · refine (orbit_finite ρ hsm K₀ hco w).subset ?_
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨k, k.2.1⟩, rfl⟩

theorem exists_proj (ρ : Representation ℂ H W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (hdef : ∀ v, B v v = 0 → v = 0) (hinv : ∀ g u v, B (ρ g u) (ρ g v) = B u v)
    (hadm : ∀ v, ∃ K : Subgroup H, (∀ k ∈ K, ρ k v = v) ∧ FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K) ∧
      ∀ w, (Set.range fun k : K => ρ k w).Finite)
    (Z : Subrepresentation ρ) :
    ∃ P : W →ₗ[ℂ] W, (∀ w, P w ∈ Z.toSubmodule) ∧ (∀ w, ∀ z ∈ Z.toSubmodule, B z (w - P w) = 0) ∧
      ∀ g w, P (ρ g w) = ρ g (P w) := by
  classical
  have hex := fun w => exists_compl_proj ρ B hdef hinv hadm Z w
  let f : W → W := fun w => Classical.choose (hex w)
  have hf1 : ∀ w, f w ∈ Z.toSubmodule := fun w => (Classical.choose_spec (hex w)).1
  have hf2 : ∀ w, ∀ z ∈ Z.toSubmodule, B z (w - f w) = 0 :=
    fun w => (Classical.choose_spec (hex w)).2
  have huniq : ∀ w t, t ∈ Z.toSubmodule → (∀ z ∈ Z.toSubmodule, B z (w - t) = 0) → f w = t := by
    intro w t ht htw
    have hd : f w - t ∈ Z.toSubmodule := sub_mem (hf1 w) ht
    have h0 : B (f w - t) (f w - t) = 0 := by
      calc B (f w - t) (f w - t) = B (f w - t) ((w - t) - (w - f w)) := by congr 1; abel
        _ = 0 := by rw [map_sub, htw _ hd, hf2 w _ hd, sub_zero]
    exact sub_eq_zero.1 (hdef _ h0)
  let P : W →ₗ[ℂ] W :=
    { toFun := f
      map_add' := fun a b => huniq _ _ (add_mem (hf1 a) (hf1 b)) (fun z hz => by
        rw [show a + b - (f a + f b) = (a - f a) + (b - f b) by abel, map_add (f := _), hf2 a z hz,
          hf2 b z hz, add_zero])
      map_smul' := fun c a => by
        simp only [RingHom.id_apply]
        exact huniq _ _ (Z.toSubmodule.smul_mem c (hf1 a)) (fun z hz => by
          rw [← smul_sub, map_smul, hf2 a z hz, smul_zero]) }
  refine ⟨P, hf1, hf2, fun g w => ?_⟩
  exact huniq _ _ (Z.apply_mem_toSubmodule g (hf1 w)) (fun z hz => by
    rw [← map_sub]; exact orth_stable ρ B hinv Z (w - f w) (hf2 w) g z hz)

theorem exists_irreducible_equivariant_projection : ∀ (H W : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), (∀ u v, star (B u v) = B v u) → (∀ v, 0 ≤ (B v v).re) → (∀ v, B v v = 0 → v = 0) → (∀ g u v, B (ρ g u) (ρ g v) = B u v) → (∃ K : Subgroup H, IsOpen (K : Set H) ∧ IsCompact (K : Set H)) → (∀ w, IsOpen {k : H | ρ k w = w}) → (∀ K : Subgroup H, IsOpen (K : Set H) → FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K)) → ∀ x : W, x ≠ 0 → ∃ (U : Submodule ℂ W) (P : W →ₗ[ℂ] W), U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧ (∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U) ∧ (∀ w, P w ∈ U) ∧ (∀ g w, P (ρ g w) = ρ g (P w)) ∧ P x ≠ 0 := by
  intro H W _ _ _ _ _ ρ B hherm hpos hdef hinv hK0 hsm hfd x hx
  classical
  have hadm := hadm_of ρ hK0 hsm hfd
  obtain ⟨K0, hxK, hfdK, -⟩ := hadm x
  set F := GlobalTheory.PRep.fixed ρ K0 with hF
  haveI := hfdK
  have ofF : ∀ u ∈ F, ∀ k ∈ K0, ρ k u = u := by
    intro u hu k hk
    have := hu ⟨k, hk⟩
    simpa using this
  have memF : ∀ u, (∀ k ∈ K0, ρ k u = u) → u ∈ F := by
    intro u hu k
    show ρ (k : H) u = ((1 : ℂˣ) : ℂ) • u
    simp [hu k k.2]
  set O := (orbSpan ρ x).toSubmodule with hO
  let Q : W → Prop := fun y => y ≠ 0 ∧ y ∈ F ∧ y ∈ O
  have hex : ∃ n : ℕ, ∃ y, Q y ∧
      Module.finrank ℂ ((orbSpan ρ y).toSubmodule ⊓ F : Submodule ℂ W) = n :=
    ⟨_, x, ⟨hx, memF x hxK, mem_orbSpan ρ x⟩, rfl⟩
  obtain ⟨y, ⟨hy0, hyF, hyO⟩, hn⟩ := Nat.find_spec hex
  have hmin : ∀ t, Q t → Module.finrank ℂ ((orbSpan ρ y).toSubmodule ⊓ F : Submodule ℂ W) ≤
      Module.finrank ℂ ((orbSpan ρ t).toSubmodule ⊓ F : Submodule ℂ W) := by
    intro t ht
    rw [hn]
    exact Nat.find_min' hex ⟨t, ht, rfl⟩
  set U := orbSpan ρ y with hU
  have hyU : y ∈ U.toSubmodule := mem_orbSpan ρ y
  have hUO : U.toSubmodule ≤ O := orbSpan_le ρ y (orbSpan ρ x) hyO
  obtain ⟨P, hP1, hP2, hP3⟩ := exists_proj ρ B hdef hinv hadm U
  refine ⟨U.toSubmodule, P, ?_, fun g u hu => U.apply_mem_toSubmodule g hu, ?_, hP1, hP3, ?_⟩
  · intro h
    apply hy0
    rw [h] at hyU
    exact (Submodule.mem_bot ℂ).1 hyU
  · intro N hNU hN
    let N' : Subrepresentation ρ := ⟨N, by intro g v hv; exact hN g v hv⟩
    obtain ⟨t, htN, ht⟩ := exists_compl_proj ρ B hdef hinv hadm N' y
    have hfix : ∀ g, ρ g y = y → ρ g t = t := by
      intro g hg
      have h1 : ρ g t - t ∈ N'.toSubmodule := sub_mem (N'.apply_mem_toSubmodule g htN) htN
      have h2 : ∀ z ∈ N'.toSubmodule, B z (ρ g t - t) = 0 := by
        intro z hz
        have e : ρ g t - t = (y - t) - ρ g (y - t) := by
          rw [map_sub, hg]
          abel
        rw [e, map_sub, ht z hz, orth_stable ρ B hinv N' _ ht g z hz, sub_zero]
      exact sub_eq_zero.1 (hdef _ (h2 _ h1))
    by_cases ht0 : t = 0
    · left
      have hyo : ∀ z ∈ N'.toSubmodule, B z y = 0 := by
        intro z hz
        simpa [ht0] using ht z hz
      have hUo : ∀ z ∈ N'.toSubmodule, ∀ u ∈ U.toSubmodule, B z u = 0 := by
        intro z hz u hu
        have hle : U.toSubmodule ≤ LinearMap.ker (B z) := by
          refine Submodule.span_le.2 ?_
          rintro _ ⟨g, rfl⟩
          exact orth_stable ρ B hinv N' y hyo g z hz
        exact hle hu
      rw [Submodule.eq_bot_iff]
      intro v hv
      exact hdef _ (hUo _ hv _ (hNU hv))
    · right
      have hQt : Q t := ⟨ht0, memF t (fun k hk => hfix k (ofF y hyF k hk)), hUO (hNU htN)⟩
      have h1 := hmin t hQt
      haveI : FiniteDimensional ℂ (U.toSubmodule ⊓ F : Submodule ℂ W) :=
        Submodule.finiteDimensional_of_le inf_le_right
      haveI : FiniteDimensional ℂ (N ⊓ F : Submodule ℂ W) :=
        Submodule.finiteDimensional_of_le inf_le_right
      have hle1 : ((orbSpan ρ t).toSubmodule ⊓ F : Submodule ℂ W) ≤ N ⊓ F :=
        inf_le_inf_right _ (orbSpan_le ρ t N' htN)
      have hle2 : (N ⊓ F : Submodule ℂ W) ≤ U.toSubmodule ⊓ F := inf_le_inf_right _ hNU
      have h2 := LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion hle1)
        (Submodule.inclusion_injective hle1)
      have heq := Submodule.eq_of_le_of_finrank_le hle2 (h1.trans h2)
      have hyN : y ∈ N := by
        have : y ∈ (N ⊓ F : Submodule ℂ W) := heq ▸ ⟨hyU, hyF⟩
        exact this.1
      exact le_antisymm hNU (orbSpan_le ρ y N' hyN)
  · intro hPx
    have hxo : ∀ z ∈ U.toSubmodule, B z x = 0 := by
      intro z hz
      simpa [hPx] using hP2 x z hz
    have hle : O ≤ LinearMap.ker (B y) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, rfl⟩
      exact orth_stable ρ B hinv U x hxo g y hyU
    exact hy0 (hdef _ (hle (hUO hyU)))

end GlobalTheory.AdmissibleProjection
end

section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil


open Classical in
open scoped BigOperators in
theorem _root_.GlobalTheory.FinWeil.sumOp_sumOp_eq_idx_smul : ∀ {R X M : Type} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R}
    {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, _root_.GlobalTheory.FinWeil.IsHeis σ w γ W →
    ∀ (A B : Submodule R X), _root_.GlobalTheory.FinWeil.SelfDual γ A → _root_.GlobalTheory.FinWeil.SelfDual γ B →
    _root_.GlobalTheory.FinWeil.idx A B ≠ 0 →
    _root_.GlobalTheory.FinWeil.idx B A = _root_.GlobalTheory.FinWeil.idx A B ∧
      ∀ v, _root_.GlobalTheory.FinWeil.Fixes W A v →
        _root_.GlobalTheory.FinWeil.sumOp W B A (_root_.GlobalTheory.FinWeil.sumOp W A B v) =
          (_root_.GlobalTheory.FinWeil.idx A B : ℂ) • v := by
  intro R X M _ _ _ _ _ σ w γ W hW A B hA hB hAB
  obtain ⟨hidx, -, hsum⟩ := _root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW B.toAddSubgroup A.toAddSubgroup
    A.toAddSubgroup B.toAddSubgroup (fun a _ => hB a)
    (fun t _ => (hA t).trans (forall₂_congr fun a _ =>
      ⟨hW.swap_eq_one, hW.swap_eq_one⟩)) hAB
  refine ⟨hidx, fun v hv => ?_⟩
  have hfinB : (A.toAddSubgroup.addSubgroupOf B.toAddSubgroup).FiniteIndex := ⟨hAB⟩
  have hfinA : (B.toAddSubgroup.addSubgroupOf A.toAddSubgroup).FiniteIndex := by
    refine ⟨?_⟩
    change B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0
    rw [hidx]; exact hAB
  letI := Fintype.ofFinite (B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup)
  letI := Fintype.ofFinite (A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup)
  unfold _root_.GlobalTheory.FinWeil.sumOp

  simp_rw [finsum_eq_sum_of_fintype, map_sum] at hsum ⊢
  have hcomm : ∀ a ∈ A, ∀ b : X, W a (W b v) = γ a b • W b v := by
    intro a ha b
    rw [hW.comm, hv a ha]
  calc ∑ q : A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup,
        ∑ p : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup,
          W (Quotient.out q).1 (W (Quotient.out p).1 v)
      = ∑ p : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup,
          (∑ q : A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup,
            γ (Quotient.out q).1 (Quotient.out p).1) • W (Quotient.out p).1 v := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_smul]
        exact Finset.sum_congr rfl fun q _ => hcomm _ (Quotient.out q).2 _
    _ = ∑ p : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup,
          if p = 0 then (_root_.GlobalTheory.FinWeil.idx A B : ℂ) • v else 0 := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hsum _ (Quotient.out p).2]
        have hmem : (Quotient.out p).1 ∈ A.toAddSubgroup ↔ p = 0 := by
          conv_rhs => rw [← QuotientAddGroup.out_eq' p]
          rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
        by_cases hp : p = 0
        · rw [if_pos (hmem.2 hp), if_pos hp, hv _ (hmem.2 hp)]
          exact congrArg (fun n : ℕ => (n : ℂ) • v) hidx
        · rw [if_neg (mt hmem.1 hp), if_neg hp, zero_smul]
    _ = (_root_.GlobalTheory.FinWeil.idx A B : ℂ) • v := by
        rw [Finset.sum_ite_eq']
        simp

end GlobalTheory.FinWeil
end

section

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem cuspForm_of_chiInv : ∀ (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ), 0 < N →
    CuspAll k G → ChiInv k N N χ G → ∃ f : CuspForm (Gamma1 N) k, ⇑f = G := by
  intro N k χ G _ hC hχ
  refine ⟨{ toFun := G
            slash_action_eq' := fun A hA => ?_
            holo' := hC.1
            zero_at_cusps' := fun {c} hc => hC.2 c (hc.mono ?_) }, rfl⟩
  · obtain ⟨A, hA, rfl⟩ := hA
    have hA0 : A ∈ Gamma0 N := Gamma1_in_Gamma0 N hA
    have h11 : ((mat A 1 1 : ℤ) : ZMod N) = 1 := ((Gamma1_mem N A).1 hA).2.1
    have := hχ A hA0
    rw [h11, map_one, one_smul, ModularForm.SL_slash] at this
    exact this
  · rintro _ ⟨γ, -, rfl⟩; exact ⟨γ, rfl⟩
end GlobalTheory.HeckeFamilyMatrices
end
