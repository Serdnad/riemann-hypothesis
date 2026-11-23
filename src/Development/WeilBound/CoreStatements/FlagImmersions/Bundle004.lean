module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isOpen_nonvanishing_blocks : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z : (Σ k, ι k) → ℂ | z ⟨k, i⟩ ≠ 0} := by
    ext z; simp
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem smooth_metric_zpow {A : HermLine ι} (hA : IsSmoothHerm A) (n : ℤ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => A.h z ^ n) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  cases n with
  | ofNat m =>
    simp only [Int.ofNat_eq_coe, zpow_natCast]
    exact hA.pow m
  | negSucc m =>
    simp only [zpow_negSucc]
    exact (hA.pow (m + 1)).inv fun z hz => pow_ne_zero _ (A.pos z hz).ne'

theorem combLine_smooth {J : Type} [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ)
    (h : ∀ j, IsSmoothHerm (ℓ j)) : IsSmoothHerm (combLine ℓ n) := by
  show ContDiffOn ℝ _ (fun z => ∏ j, (ℓ j).h z ^ n j) _
  exact contDiffOn_prod fun j _ => smooth_metric_zpow (h j) (n j)

theorem combLine_conj_invariant {J : Type} [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ)
    (h : ∀ j, IsConjInvariantH (ℓ j)) : IsConjInvariantH (combLine ℓ n) := by
  intro z
  show ∏ j, (ℓ j).h _ ^ n j = ∏ j, (ℓ j).h z ^ n j
  exact Finset.prod_congr rfl fun j _ => by rw [h j z]

end

theorem leviForm_congr_eventually {ι : Type} [Fintype ι] {φ ψ : (ι → ℂ) → ℝ} {z : ι → ℂ} (h : φ =ᶠ[𝓝 z] ψ)
    (w : ι → ℂ) : leviForm φ z w = leviForm ψ z w := by
  simp only [leviForm, h.fderiv.fderiv_eq]

theorem leviForm_smul {ι : Type} [Fintype ι] (c : ℝ) (φ : (ι → ℂ) → ℝ) (z w : ι → ℂ) :
    leviForm (c • φ) z w = c * leviForm φ z w := by
  by_cases hc : c = 0
  · subst hc
    simp [leviForm]
  · letI : Invertible c := invertibleOfNonzero hc
    have h1 : fderiv ℝ (c • φ) = c • fderiv ℝ φ :=
      funext fun x => fderiv_const_smul_of_invertible c
    have h2 : fderiv ℝ (c • fderiv ℝ φ) z = c • fderiv ℝ (fderiv ℝ φ) z :=
      fderiv_const_smul_of_invertible c
    simp only [leviForm, h1, h2, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring

theorem root_model_line_semipositive : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), (∀ j, (n j : ℝ) = q * M.coef lam s j) → M.Semipos t lam s → IsSemipositiveH M.P (combLine (M.line t) n) ∧ IsConjInvariantH (combLine (M.line t) n) := by
  intro Ψ _ N M t lam s q n hn hS
  have hsm : IsSmoothHerm (combLine (M.line t) n) := by
    refine combLine_smooth _ _ fun j => ?_
    cases j with
    | none => exact M.A_smooth
    | some r => exact M.x_smooth t r
  have hcj : IsConjInvariantH (combLine (M.line t) n) := by
    refine combLine_conj_invariant _ _ fun j => ?_
    cases j with
    | none => exact M.A_conj
    | some r => exact M.x_conj t r
  refine ⟨⟨hsm, fun z hz w hw => ?_⟩, hcj⟩
  have hev : (fun y => Real.log ((combLine (M.line t) n).h y)) =ᶠ[𝓝 z]
      ((q : ℝ) • M.weight t lam s) := by
    filter_upwards [isOpen_nonvanishing_blocks.mem_nhds hz.1] with y hy
    rw [Pi.smul_apply, smul_eq_mul]
    show Real.log (∏ j, (M.line t j).h y ^ n j) =
      (q : ℝ) * ∑ j, M.coef lam s j * Real.log ((M.line t j).h y)
    rw [Real.log_prod (fun j _ => zpow_ne_zero _ ((M.line t j).pos y hy).ne'), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Real.log_zpow, hn j]
    ring
  rw [leviForm_congr_eventually hev w, leviForm_smul]
  exact mul_nonneg (Nat.cast_nonneg _) (hS z hz w hw)

end RootFieldNumerics
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

namespace Ii

theorem contDiffOn_zpow_h {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι)
    (hA : IsSmoothHerm A) (n : ℤ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => A.h z ^ n) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  unfold IsSmoothHerm at hA
  have hne : ∀ z ∈ {z : (k : K) × ι k → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}, A.h z ≠ 0 :=
    fun z hz => (A.pos z hz).ne'
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · simpa using hA.pow m
  · simp only [zpow_neg, zpow_natCast]
    exact (hA.pow m).inv (fun z hz => pow_ne_zero _ (hne z hz))

end Ii

open Ii in
theorem combLine_smooth_conj_invariant : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J : Type) [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ), ((∀ j, IsSmoothHerm (ℓ j)) → IsSmoothHerm (combLine ℓ n)) ∧ ((∀ j, IsConjInvariantH (ℓ j)) → IsConjInvariantH (combLine ℓ n)) ∧ IsSmoothHerm (trivLine ι) := by
  intro K _ ι _ J _ ℓ n
  refine ⟨fun h => ?_, fun h z => ?_, ?_⟩
  · exact contDiffOn_prod fun j _ => contDiffOn_zpow_h (ℓ j) (h j) (n j)
  · exact Finset.prod_congr rfl fun j _ => by rw [h j z]
  · exact contDiffOn_const

end RootFieldNumerics
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

namespace Ii

theorem exists_perm_of_map_eq {α J : Type} [Fintype α] (f g : α → J)
    (h : Finset.univ.val.map f = Finset.univ.val.map g) : ∃ σ : Equiv.Perm α, ∀ a, g (σ a) = f a := by
  classical
  have hc : ∀ j, Fintype.card {a // f a = j} = Fintype.card {a // g a = j} := by
    intro j
    have := congrArg (Multiset.count j) h
    simp only [Multiset.count_map] at this
    rw [Fintype.card_subtype, Fintype.card_subtype]
    convert this using 1 <;> simp [Finset.card_def, Finset.filter_val, eq_comm]
  let e : ∀ j, {a // f a = j} ≃ {a // g a = j} := fun j => Fintype.equivOfCardEq (hc j)
  let σ : Equiv.Perm α :=
    ((Equiv.sigmaFiberEquiv f).symm.trans (Equiv.sigmaCongrRight e)).trans (Equiv.sigmaFiberEquiv g)
  refine ⟨σ, fun a => ?_⟩
  exact (e (f a) ⟨a, rfl⟩).2

theorem toMultiset_sum_single {d : ℕ} {J : Type} (w : Fin d → J) :
    Finsupp.toMultiset (∑ k, Finsupp.single (w k) 1 : J →₀ ℕ) = Finset.univ.val.map w := by
  rw [Finsupp.toMultiset_sum]
  simp only [Finsupp.toMultiset_single, one_smul]
  rw [← Multiset.sum_map_singleton (Finset.univ.val.map w), Multiset.map_map]
  rfl

end Ii

open Ii in
theorem intersection_monomial_lines : ∀ II : IntersectionSystem, IsIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (J : Type) (ℓ : J → HermLine ι) (w : Fin d → J), IsArithVar P d → (∀ j, IsSmoothHerm (ℓ j)) → (∑ k, Finsupp.single (w k) 1 : J →₀ ℕ).degree = d ∧ ∃ σ : Equiv.Perm (Fin d), monoLines ℓ (∑ k, Finsupp.single (w k) 1) d = (fun k => ℓ (w k)) ∘ σ ∧ II K ι P d (monoLines ℓ (∑ k, Finsupp.single (w k) 1) d) = II K ι P d (fun k => ℓ (w k)) := by
  intro II hII K _ ι _ P d J ℓ w hP hℓ
  set m : J →₀ ℕ := ∑ k, Finsupp.single (w k) 1 with hm
  have hdeg : m.degree = d := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hm, map_sum, Finsupp.degree_single]
  set L : List J := (Finsupp.toMultiset m).toList with hL
  have hML : (L : Multiset J) = Finset.univ.val.map w := by
    rw [hL, Multiset.coe_toList, hm, toMultiset_sum_single]
  have hlen : L.length = d := by
    have := congrArg Multiset.card hML
    simpa using this
  let f : Fin d → J := fun k => L.get (Fin.cast hlen.symm k)
  have hf : List.ofFn f = L :=
    List.ext_get (by simp [hlen]) (fun i h1 h2 => by simp [f])
  have hmap : Finset.univ.val.map f = Finset.univ.val.map w := by
    rw [Fin.univ_val_map, hf, hML]
  obtain ⟨σ, hσ⟩ := exists_perm_of_map_eq f w hmap
  have hmono : monoLines ℓ m d = (fun k => ℓ (w k)) ∘ σ := by
    funext k
    have hk : (k : ℕ) < L.length := by
      rw [hlen]
      exact k.2
    simp only [monoLines, Function.comp_apply, hσ k]
    rw [dite_eq_left hk]
    rfl
  refine ⟨hdeg, σ, hmono, ?_⟩
  rw [hmono]
  exact (hII K ι).1 P d (fun k => ℓ (w k)) σ hP (fun j => hℓ _)

end RootFieldNumerics
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

theorem geoNum_one_linear_in_degree {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι)) :
    ∃ c : K → ℤ, ∀ a : K → ℤ, geoNum 1 W (fun _ => a) = ∑ k, a k * c k := by
  classical
  refine ⟨fun k => geoNum 1 W (fun _ => Pi.single k 1), fun a => ?_⟩
  have hs : ∀ b : K → ℤ, (Fin.init (fun _ : Fin 1 => b) : Fin 0 → K → ℤ) = fun i => i.elim0 :=
    fun b => Subsingleton.elim _ _
  rw [geoNum.eq_2 (n := 0)]
  simp only [geoNum.eq_2 (n := 0), hs]
  split_ifs with h
  · simp [Pi.single_apply]
  · simp

theorem geoNum_linear_combination {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    {J : Type} [Fintype J] (n : J → ℤ) (b : J → K → ℤ) :
    geoNum 1 W (fun _ => ∑ j, n j • b j) = ∑ j, n j * geoNum 1 W (fun _ => b j) := by
  obtain ⟨c, hc⟩ := geoNum_one_linear_in_degree (K := K) W
  rw [hc]
  simp only [hc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem char_prime_of_prime_ideal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    (hW : W.IsPrime) (h : charOf W ≠ 0) : (charOf W).Prime := by
  classical
  set I : Ideal ℤ := Ideal.comap (C : ℤ →+* MRing ι) W with hI
  have hp : I.IsPrime := Ideal.IsPrime.comap _
  have hne : I ≠ ⊥ := by
    intro hb
    apply h
    have : Submodule.IsPrincipal.generator I = 0 :=
      (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero I).mp hb
    simp [charOf, ← hI, this]
  have hg := Submodule.IsPrincipal.prime_generator_of_isPrime I hne
  have : charOf W = (Submodule.IsPrincipal.generator I).natAbs := by
    simp [charOf, ← hI]
  rw [this]
  exact Int.prime_iff_natAbs_prime.mp hg

theorem root_line_a_independent {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (t : ℝ) (j : Option (Ψ × Fin N)) :
    (M.line t j).a = (M.line 1 j).a := by
  cases j with
  | none => rfl
  | some r => simp only [RootModel.line, M.x_deg]

end RootFieldNumerics

theorem RootFieldNumerics.curveDeg_eq_and_nefOnFibres_of_coef : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), (∀ j, (n j : ℝ) = q * M.coef lam s j) → (∀ W : Ideal (MRing M.ι), (geoNum 1 W (fun _ => (combLine (M.line t) n).a) : ℝ) = q * M.curveDeg lam s W) ∧ (M.NefFib lam s → NefOnFibres M.P (combLine (M.line t) n).a) := by
  intro Ψ _ N M t lam s q n hn
  have key : ∀ W : Ideal (MRing M.ι),
      (geoNum 1 W (fun _ => (combLine (M.line t) n).a) : ℝ) = q * M.curveDeg lam s W := by
    intro W
    rw [show (combLine (M.line t) n).a = ∑ j, n j • (M.line t j).a from rfl,
      geoNum_linear_combination W n (fun j => (M.line t j).a)]
    push_cast
    rw [RootModel.curveDeg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [root_line_a_independent M t j, hn j]
    ring
  refine ⟨key, fun hN W hWp hPW hc hd => ?_⟩
  have hpr := char_prime_of_prime_ideal W hWp.1 hc
  have h0 := hN _ hpr W ⟨hWp, hPW, rfl, hd⟩
  have h1 : (0:ℝ) ≤ geoNum 1 W (fun _ => (combLine (M.line t) n).a) := by
    rw [key]
    exact mul_nonneg (Nat.cast_nonneg _) h0
  exact_mod_cast h1
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

theorem exists_clear_denominators_bis {J : Type} [Fintype J] (c : J → ℚ) :
    ∃ (q : ℕ) (n : J → ℤ), 0 < q ∧ ∀ j, (n j : ℚ) = q * c j := by
  classical
  refine ⟨∏ i, (c i).den, fun j => (c j).num * (((∏ i, (c i).den) / (c j).den : ℕ) : ℤ), ?_, ?_⟩
  · exact Finset.prod_pos (fun i _ => (c i).den_pos)
  · intro j
    obtain ⟨k, hk⟩ : (c j).den ∣ ∏ i, (c i).den := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    show (((c j).num * (((∏ i, (c i).den) / (c j).den : ℕ) : ℤ) : ℤ) : ℚ) = ((∏ i, (c i).den : ℕ) : ℚ) * c j
    rw [hk, Nat.mul_div_cancel_left _ (c j).den_pos]
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring

end RootFieldNumerics

theorem RootFieldNumerics.exists_integer_coefficients_rational : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (lam : Wt Ψ N) (s : ℚ), IsRatWt lam → ∃ (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), 0 < q ∧ ∀ j, (n j : ℝ) = q * M.coef lam s j := by
  intro Ψ _ N M lam s hlam
  classical
  choose f hf using hlam
  let c : Option (Ψ × Fin N) → ℚ := fun j => match j with
    | some r => -f r.1 r.2
    | none => s / M.kA
  obtain ⟨q, n, hq, hn⟩ := RootFieldNumerics.exists_clear_denominators_bis c
  refine ⟨q, n, hq, fun j => ?_⟩
  have h : ((n j : ℚ) : ℝ) = ((q * c j : ℚ) : ℝ) := by rw [hn j]
  push_cast at h
  rw [h]
  congr 1
  cases j with
  | none => simp [c, RootModel.coef]
  | some r => simp [c, RootModel.coef, hf]
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

theorem root_coef_add {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (lam mu : Wt Ψ N) (s s' : ℝ)
    (j : Option (Ψ × Fin N)) : M.coef (lam + mu) (s + s') j = M.coef lam s j + M.coef mu s' j := by
  cases j with
  | none => simp only [RootModel.coef]; ring
  | some r => simp only [RootModel.coef, Pi.add_apply]; ring

theorem root_coef_smul {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (lam : Wt Ψ N) (a s : ℝ)
    (j : Option (Ψ × Fin N)) : M.coef (a • lam) (a * s) j = a * M.coef lam s j := by
  cases j with
  | none => simp only [RootModel.coef, mul_div_assoc]
  | some r => simp only [RootModel.coef, Pi.smul_apply, smul_eq_mul]; ring

theorem root_coef_split {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (lam : Wt Ψ N) (s : ℝ)
    (j : Option (Ψ × Fin N)) : M.coef lam s j = M.coef lam 0 j + s * M.coef 0 1 j := by
  cases j with
  | none => simp only [RootModel.coef]; ring
  | some r => simp only [RootModel.coef, Pi.zero_apply]; ring

theorem root_coef_weighted_sum_split {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (lam : Wt Ψ N) (s : ℝ)
    (g : Option (Ψ × Fin N) → ℝ) :
    ∑ j, M.coef lam s j * g j = ∑ j, M.coef lam 0 j * g j + s * ∑ j, M.coef 0 1 j * g j := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [root_coef_split M lam s j]
  ring

end RootFieldNumerics

theorem RootFieldNumerics.curveDeg_linear_and_nef : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (lam mu : Wt Ψ N) (s s' a : ℝ), (∀ W, M.curveDeg (lam + mu) (s + s') W = M.curveDeg lam s W + M.curveDeg mu s' W) ∧ (∀ W, M.curveDeg (a • lam) (a * s) W = a * M.curveDeg lam s W) ∧ (∀ p, 0 ≤ s → M.NefAt p lam 0 → M.NefAt p 0 1 → M.NefAt p lam s) ∧ (0 ≤ s → M.NefGen lam 0 → M.NefGen 0 1 → M.NefGen lam s) := by
  intro Ψ _ N M lam mu s s' a
  refine ⟨fun W => ?_, fun W => ?_, fun p hs h1 h2 W hW => ?_, fun hs h1 h2 W hW hP => ?_⟩
  · simp only [RootModel.curveDeg]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [RootFieldNumerics.root_coef_add]; ring
  · simp only [RootModel.curveDeg]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [RootFieldNumerics.root_coef_smul]; ring
  · have e : M.curveDeg lam s W = M.curveDeg lam 0 W + s * M.curveDeg 0 1 W :=
      RootFieldNumerics.root_coef_weighted_sum_split M lam s _
    rw [e]
    exact add_nonneg (h1 W hW) (mul_nonneg hs (h2 W hW))
  · have e : ∑ j, M.coef lam s j * geomDeg W (M.line 1 j) 1
        = ∑ j, M.coef lam 0 j * geomDeg W (M.line 1 j) 1
          + s * ∑ j, M.coef 0 1 j * geomDeg W (M.line 1 j) 1 :=
      RootFieldNumerics.root_coef_weighted_sum_split M lam s _
    rw [e]
    exact add_nonneg (h1 W hW hP) (mul_nonneg hs (h2 W hW hP))
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

private theorem prod_le_mul_two_pow_card {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ℝ)
    (h0 : ∀ x, 0 ≤ f x) (h2 : ∀ x, f x ≤ 2) (x₀ : ι) (c : ℝ) (hc : f x₀ = c) :
    ∏ x, f x ≤ c * 2 ^ Fintype.card ι := by
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ x₀), hc]
  refine mul_le_mul_of_nonneg_left ?_ (hc ▸ h0 x₀)
  calc ∏ x ∈ Finset.univ.erase x₀, f x ≤ ∏ x ∈ Finset.univ.erase x₀, (2 : ℝ) :=
        Finset.prod_le_prod₀ (fun x _ => h0 x) (fun x _ => h2 x)
    _ = 2 ^ (Finset.univ.erase x₀).card := Finset.prod_const 2
    _ ≤ 2 ^ Fintype.card ι := pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ _)

theorem flagDeg_le_gap : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ), 1 ≤ j → j < N → ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam : Wt Ψ N) (τ₀ : Ψ), ‖lam‖ ≤ 1 → Dominant lam → flagDeg lam ≤ C * gap j lam τ₀ := by
  intro Ψ _ _ N j hj hjN
  refine ⟨((GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N).factorial : ℝ) * 2 ^ Fintype.card (Ψ × Fin N × Fin N),
    by positivity, ?_⟩
  intro lam τ₀ hlam hdom
  have hj1 : j - 1 < N := by omega
  have hbound : ∀ τ i, |lam τ i| ≤ 1 := by
    intro τ i
    have h1 := norm_le_pi_norm (show Ψ → Fin N → ℝ from lam) τ
    have h2 := norm_le_pi_norm (lam τ) i
    rw [Real.norm_eq_abs] at h2
    have h3 : ‖(show Ψ → Fin N → ℝ from lam)‖ ≤ 1 := hlam
    linarith
  have hfac : ∀ τ (i k : Fin N),
      0 ≤ (if i < k then (lam τ i - lam τ k) / (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ)) else 1) ∧
        (if i < k then (lam τ i - lam τ k) / (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ)) else 1) ≤ 2 := by
    intro τ i k
    split_ifs with hik
    · have hik' : (i : ℕ) < (k : ℕ) := hik
      have hd : ((i : ℕ) : ℝ) + 1 ≤ ((k : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hik'
      have hmono := hdom τ i k hik.le
      have hi := abs_le.mp (hbound τ i)
      have hk := abs_le.mp (hbound τ k)
      constructor
      · apply div_nonneg <;> linarith
      · rw [div_le_iff₀ (by linarith)]
        linarith
    · norm_num
  have hgap : GlobalTheory.CompanionTheory.Ar.Top.gap j lam τ₀ = lam τ₀ ⟨j - 1, hj1⟩ - lam τ₀ ⟨j, hjN⟩ := by
    unfold GlobalTheory.CompanionTheory.Ar.Top.gap GlobalTheory.CompanionTheory.Ar.Top.ent
    rw [dite_eq_left hj1, dite_eq_left hjN]
  have hx0 : (if (⟨j - 1, hj1⟩ : Fin N) < ⟨j, hjN⟩ then
      (lam τ₀ ⟨j - 1, hj1⟩ - lam τ₀ ⟨j, hjN⟩) /
        ((((⟨j, hjN⟩ : Fin N) : ℕ) : ℝ) - (((⟨j - 1, hj1⟩ : Fin N) : ℕ) : ℝ)) else 1) =
      lam τ₀ ⟨j - 1, hj1⟩ - lam τ₀ ⟨j, hjN⟩ := by
    have hlt : (⟨j - 1, hj1⟩ : Fin N) < ⟨j, hjN⟩ := by
      rw [Fin.lt_def]
      show j - 1 < j
      omega
    rw [if_pos hlt]
    have hden : (((⟨j, hjN⟩ : Fin N) : ℕ) : ℝ) - (((⟨j - 1, hj1⟩ : Fin N) : ℕ) : ℝ) = 1 := by
      show ((j : ℕ) : ℝ) - ((j - 1 : ℕ) : ℝ) = 1
      rw [Nat.cast_sub hj, Nat.cast_one]
      ring
    rw [hden, div_one]
  have key := prod_le_mul_two_pow_card
    (fun x : Ψ × Fin N × Fin N => if x.2.1 < x.2.2 then
      (lam x.1 x.2.1 - lam x.1 x.2.2) / (((x.2.2 : ℕ) : ℝ) - ((x.2.1 : ℕ) : ℝ)) else 1)
    (fun x => (hfac x.1 x.2.1 x.2.2).1) (fun x => (hfac x.1 x.2.1 x.2.2).2)
    (τ₀, ⟨j - 1, hj1⟩, ⟨j, hjN⟩) _ hx0
  simp only [Fintype.prod_prod_type] at key
  obtain ⟨hdeg, -, -⟩ := GlobalTheory.T.flag_degree_weight_formula Ψ N lam
  rw [hdeg, hgap]
  calc _ ≤ ((GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N).factorial : ℝ) *
        ((lam τ₀ ⟨j - 1, hj1⟩ - lam τ₀ ⟨j, hjN⟩) * 2 ^ Fintype.card (Ψ × Fin N × Fin N)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = _ := by ring

end RootFieldNumerics
end
