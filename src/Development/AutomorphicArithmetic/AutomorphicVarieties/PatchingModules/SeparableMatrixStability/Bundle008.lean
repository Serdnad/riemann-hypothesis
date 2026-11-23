module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.CoboundaryFirstSubsetSelmerFirst
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SelmerSecondExistsUltrafilterLimit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle002

@[expose] public section

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem card_submodule_mul_quotient_le {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (S B : Submodule A M)
    (hBS : (B : Set M) ⊆ S) (hS : (S : Set M).Finite) (I : Ideal A) (e : ℕ) (φ : (Fin e → A) → M)
    (hφ : ∀ c, φ c ∈ S) (hsub : ∀ c c', φ (c - c') = φ c - φ c') (hI : ∀ c, φ c ∈ B → ∀ i, c i ∈ I) :
    (B : Set M).ncard * Nat.card (A ⧸ I) ^ e ≤ (S : Set M).ncard := by
  haveI : Finite (S : Set M) := hS
  choose s hs using (Ideal.Quotient.mk_surjective (I := I))
  let f : ↥(B : Set M) × (Fin e → A ⧸ I) → ↥(S : Set M) := fun p =>
    ⟨φ (fun i => s (p.2 i)) + p.1, S.add_mem (hφ _) (hBS p.1.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨b, c⟩ ⟨b', c'⟩ hh
    have h1 : φ (fun i => s (c i)) + b = φ (fun i => s (c' i)) + b' := congrArg Subtype.val hh
    have h2 : φ ((fun i => s (c i)) - fun i => s (c' i)) ∈ B := by
      rw [hsub]
      have : φ (fun i => s (c i)) - φ (fun i => s (c' i)) = (b' : M) - b := by
        rw [sub_eq_sub_iff_add_eq_add, h1, add_comm]
      rw [this]
      exact B.sub_mem b'.2 b.2
    have h3 : c = c' := by
      funext i
      rw [← hs (c i), ← hs (c' i)]
      exact Ideal.Quotient.eq.2 (hI _ h2 i)
    subst h3
    exact Prod.ext (Subtype.ext (add_left_cancel h1)) rfl
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin e), Fintype.card_fin,
    Nat.card_coe_set_eq, Nat.card_coe_set_eq] at this

theorem UpperTheory.V.Pa.firstCohomologyBound_of_boundaryBound :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (D0 : ℕ), TopFG G.Γ → FirstSelmerCardBoundAtAllLevels h k D0 → K1 h k D0 := by
  intro l _ L G G0 h n x k D0 hfg hB e z hz hind
  obtain ⟨C, hC⟩ := coefficients_bounded_of_selmer_boundary l L G G0 h n x k e z hfg hz hind
  obtain ⟨C', hC'⟩ := hB
  obtain ⟨⟨S0, hS0⟩, -⟩ := sel_lin l G.frame n x.A (DD x.A k.g) x.t (fun g => k.ρ1 x.A (h.p₀ g)) (k.w1 x.A)
    (k.wi1 x.A) (W1 n x.A x.A k.g x.a)
  have hS0' : (S0 : Set _) = Sel1 h x.A k := hS0
  have key : ∀ m, (m - C) * e ≤ m * D0 + C' := by
    intro m
    obtain ⟨⟨S, hS⟩, ⟨B, hB⟩⟩ := sel_lin l G.frame n x.A (DD (x.Am m) k.g) x.t (fun g => k.ρ1 (x.Am m) (h.p₀ g))
      (k.w1 (x.Am m)) (k.wi1 (x.Am m)) (W1 n x.A (x.Am m) k.g x.a)
    have hS' : (S : Set _) = Sel1 h (x.Am m) k := hS
    have hB' : (B : Set _) = Bd1 h (x.Am m) k := hB
    obtain ⟨hfin, hle⟩ := hC' m
    have hBS := coboundary_first_subset_selmer_first l L G G0 h n x k (x.Am m)
    rw [← hS'] at hfin hle hBS
    rw [← hB'] at hle hBS
    have hc := card_submodule_mul_quotient_le S B hBS hfin (Ideal.span {x.t ^ (m - C)}) e
      (fun c g => ((∑ i, c i • z i) g).map (x.redD k.g m))
      (fun c => by
        have h1 : (∑ i, c i • z i) ∈ Sel1 h x.A k := by
          rw [← hS0']
          exact S0.sum_mem fun i _ => S0.smul_mem _ (by rw [← SetLike.mem_coe, hS0']; exact hz i)
        have h2 := (sel_red l L G G0 h n x k x.A (x.Am m) (Ideal.Quotient.mkₐ x.A _)).2.1 _ h1
        rw [← hS'] at h2
        exact h2)
      (fun c c' => by
        funext g
        ext1 a b
        simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, Matrix.map_apply, Matrix.sub_apply, map_sub])
      (fun c hc => hC m c (by rw [← hB']; exact hc))
    have hcard : Nat.card (x.A ⧸ Ideal.span {x.t ^ (m - C)}) = Nat.card x.K ^ (m - C) :=
      (am_fin l G0.frame n x (m - C) 0).2.1
    have hpos : 0 < Set.ncard (SetLike.coe B) := (Set.ncard_pos (hfin.subset hBS)).2 ⟨0, B.zero_mem⟩
    rw [hcard, ← pow_mul] at hc
    have h3 := Nat.le_of_mul_le_mul_left (hc.trans hle) hpos
    exact (Nat.pow_le_pow_iff_right (am_fin l G0.frame n x 0 0).2.2.2.2.2).1 h3
  by_contra hlt
  have h1 : D0 + 1 ≤ e := by omega
  have h2 := key (C + (C * D0 + C' + 1))
  rw [Nat.add_sub_cancel_left] at h2
  have h3 := (Nat.mul_le_mul_left (C * D0 + C' + 1) h1).trans h2
  nlinarith
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem power_series_exists_ultrafilter_limit {K : Type} [Field K] [Finite K] (U : Ultrafilter ℕ) (c : ℕ → PowerSeries K) :
    ∃ c0 : PowerSeries K, ∀ j, ∀ᶠ m in (U : Filter ℕ), (PowerSeries.X : PowerSeries K) ^ j ∣ c m - c0 := by
  have hv : ∀ i : ℕ, ∃ v : K, {m | PowerSeries.coeff i (c m) = v} ∈ (U : Filter ℕ) := by
    intro i
    by_contra hno
    push_neg at hno
    have hall : ∀ v : K, {m | PowerSeries.coeff i (c m) = v}ᶜ ∈ U := fun v =>
      Ultrafilter.compl_mem_iff_notMem.2 (hno v)
    have hinter : (⋂ v : K, {m | PowerSeries.coeff i (c m) = v}ᶜ) ∈ (U : Filter ℕ) :=
      Filter.iInter_mem.2 hall
    obtain ⟨m, hm⟩ := Filter.nonempty_of_mem hinter
    simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_setOf_eq] at hm
    exact hm _ rfl
  choose v hv using hv
  refine ⟨PowerSeries.mk v, fun j => ?_⟩
  have hj : ∀ᶠ m in (U : Filter ℕ), ∀ i : Fin j, PowerSeries.coeff (i : ℕ) (c m) = v i :=
    Filter.eventually_all.2 fun i => hv i
  filter_upwards [hj] with m hm
  rw [PowerSeries.X_pow_dvd_iff]
  intro i hi
  simp [map_sub, hm ⟨i, hi⟩, PowerSeries.coeff_mk]

private theorem power_series_eq_of_dvd_all_powers {K : Type} [Field K] (a b : PowerSeries K)
    (H : ∀ j, (PowerSeries.X : PowerSeries K) ^ j ∣ a - b) : a = b := by
  rw [← sub_eq_zero]
  ext n
  have h := H (n + 1)
  rw [PowerSeries.X_pow_dvd_iff] at h
  simpa using h n (Nat.lt_succ_self n)

private theorem dual_numbers_map_surjective {A X X' : Type} [CommRing A] [CommRing X] [CommRing X'] [Algebra A X] [Algebra A X'] (g : ℕ)
    (f : X →ₐ[A] X') (hf : Function.Surjective f) : Function.Surjective (DD.map g f) := by
  intro y
  choose pre hpre using hf
  exact ⟨⟨pre y.a, fun j => pre (y.ep j), fun j => pre (y.ep' j), pre y.eta⟩,
    DD.ext (hpre _) (funext fun j => hpre _) (funext fun j => hpre _) (hpre _)⟩

theorem UpperTheory.V.Pa.secondCohomologyBound_of_boundaryBound :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x), TopFG G.Γ → SecondSelmerSpanBoundAtAllLevels h k → K2 h k := by
  intro l _ L G G0 h n x k hTop hB2 z hz
  obtain ⟨C, hC⟩ := hB2
  set q : ∀ m : ℕ, x.A →ₐ[x.A] x.Am m := fun m => Ideal.Quotient.mkₐ x.A (Ideal.span {x.t ^ m}) with hqdef
  have hsurj : ∀ m, Function.Surjective (q m) := fun m => Ideal.Quotient.mkₐ_surjective _ _
  have hqeq : ∀ m (u v : x.A), q m u = q m v ↔ (PowerSeries.X : PowerSeries x.K) ^ m ∣ u - v := by
    intro m u v
    simp only [hqdef, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq, Ideal.mem_span_singleton] <;> rfl
  have hzm : ∀ m i j, (fun g => (z i j g).map (q m)) ∈ SelP h x (x.Am m) :=
    fun m i j => (sel_red l L G G0 h n x k x.A (x.Am m) (q m)).1 _ (hz i j)
  choose cm hcu Ψm hΨm hΨe using fun m => hC m (fun i j g => (z i j g).map (q m)) (hzm m)
  choose Ψt hΨt using fun m (g : G.G₀) (a b : Fin n) =>
    dual_numbers_map_surjective k.g (q m) (hsurj m) (Ψm m g a b)
  set Z : ℕ → G.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g) :=
    fun m g => Matrix.of (fun a b => Ψt m g a b) with hZdef
  have hZ : ∀ m, (fun g => (Z m g).map (x.redD k.g m)) = Ψm m := by
    intro m
    funext g
    exact Matrix.ext fun a b => hΨt m g a b
  set U := Ultrafilter.of (atTop : Filter ℕ) with hUdef
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨Ψ, hΨ, hlim⟩ := selmer_second_exists_ultrafilter_limit l L G G0 h n x k U Z hTop hU (fun m => by rw [hZ m]; exact hΨm m)
  choose c0 hc0 using fun i : Fin (k.g + 1) => power_series_exists_ultrafilter_limit U (fun m => cm m i)
  choose idx hidx using hcu
  have hi0 : ∃ i0, ∀ᶠ m in (U : Filter ℕ), idx m = i0 := by
    by_contra hno
    push_neg at hno
    have hinter : ∀ᶠ m in (U : Filter ℕ), ∀ i, ¬ idx m = i :=
      Filter.eventually_all.2 fun i => by simpa using hno i
    obtain ⟨m, hm⟩ := hinter.exists
    exact hm _ rfl
  obtain ⟨i0, hi0⟩ := hi0
  refine ⟨fun i => x.t ^ C * c0 i, ?_, Ψ, hΨ, ?_⟩
  · intro h0
    have h1 : x.t ^ C * c0 i0 = 0 := congrFun h0 i0
    have hc00 : c0 i0 = 0 := by
      rcases mul_eq_zero.1 h1 with h2 | h2
      · exact absurd h2 (pow_ne_zero _ PowerSeries.X_ne_zero)
      · exact h2
    obtain ⟨m, hm1, hm2⟩ := (hi0.and (hc0 i0 1)).exists
    have hu := hidx m
    rw [hm1] at hu
    have h3 : (PowerSeries.X : PowerSeries x.K) ∣ cm m i0 := by
      simpa [hc00] using hm2
    have h7 := isUnit_of_dvd_unit h3 hu
    simp [PowerSeries.isUnit_iff_constantCoeff] at h7
  · intro j γ a b
    apply power_series_eq_of_dvd_all_powers
    intro J
    obtain ⟨m, hm1, hm2, hm3⟩ := ((hlim J).and ((Filter.eventually_all.2 fun i => hc0 i J).and
      ((Filter.eventually_ge_atTop J).filter_mono hU))).exists
    have d1 : (PowerSeries.X : PowerSeries x.K) ^ J ∣ (Ψ γ a b).ep' j - (Ψt m γ a b).ep' j := by
      have e := congrArg (fun M => (M a b).ep' j) (hm1 γ)
      exact (hqeq J ((Ψ γ a b).ep' j) ((Ψt m γ a b).ep' j)).1 e
    have d2 : (PowerSeries.X : PowerSeries x.K) ^ J ∣
        (Ψt m γ a b).ep' j - x.t ^ C * ∑ i, cm m i * z i j γ a b := by
      have e := hΨe m j γ a b
      rw [← hΨt m γ a b] at e
      have e2 : q m ((Ψt m γ a b).ep' j) = q m (x.t ^ C * ∑ i, cm m i * z i j γ a b) := by
        rw [show q m ((Ψt m γ a b).ep' j) = (DD.map k.g (q m) (Ψt m γ a b)).ep' j from rfl, e]
        simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.map_apply]

        rw [map_mul, map_sum]
        simp only [map_mul]
        rw [Algebra.smul_def, ← (q m).commutes, Algebra.algebraMap_self, RingHom.id_apply]
        congr 1
      exact (pow_dvd_pow _ hm3).trans ((hqeq m _ _).1 e2)
    have d3 : (PowerSeries.X : PowerSeries x.K) ^ J ∣
        x.t ^ C * ∑ i, cm m i * z i j γ a b - (∑ i, (x.t ^ C * c0 i) • z i j γ) a b := by
      have e : x.t ^ C * ∑ i, cm m i * z i j γ a b - (∑ i, (x.t ^ C * c0 i) • z i j γ) a b =
          x.t ^ C * ∑ i, (cm m i - c0 i) * z i j γ a b := by
        simp [Matrix.sum_apply, Finset.mul_sum, ← Finset.sum_sub_distrib, sub_mul, mul_sub, mul_assoc]
      rw [e]
      exact Dvd.dvd.mul_left (Finset.dvd_sum fun i _ => Dvd.dvd.mul_right (hm2 i) _) _
    have := dvd_add (dvd_add d1 d2) d3
    simpa using this
end
