module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarizedGaloisRep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

noncomputable section

namespace GlobalTheory.JetTieCompare

open GlobalTheory.IndefiniteRowSideFullHecke.IntegralJetEntries (IsRBasis)

variable {p : ℕ} [Fact p.Prime]

theorem mem_int_iff (x : ℂ_[p]) : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm, Valuation.norm_def,
    (show Valuation.RankLeOne.hom' Valued.v = MonoidWithZeroHom.ValueGroup₀.embedding from rfl), Valuation.embedding_restrict]
  exact_mod_cast Iff.rfl

theorem norm_int_le {E : Type} [Field E] (ρ : E →+* ℂ_[p]) (x : 𝓞 E) : ‖ρ (x : E)‖ ≤ 1 := by
  have h : IsIntegral 𝓞_ℂ_[p] (ρ (x : E)) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom _) ρ (RingHom.ext_int _ _) x.isIntegral_coe
  exact (mem_int_iff _).1 ((PadicComplexInt.integers p).mem_of_integral h)

theorem exists_denom {E : Type} [Field E] [NumberField E] (ρ : E →+* ℂ_[p]) (x : E) (hx : ‖ρ x‖ ≤ 1) :
    ∃ s n : 𝓞 E, ‖ρ (s : E)‖ = 1 ∧ (s : E) * x = n := by
  let I : Ideal (𝓞 E) :=
    { carrier := {y | ‖ρ (y : E)‖ < 1}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add (f := _)] at ha hb ⊢
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      smul_mem' := fun c {a} ha => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at ha ⊢
        exact mul_lt_one_of_nonneg_of_lt_one_right (norm_int_le ρ c) (norm_nonneg _) ha }
  have hI : ∀ y : 𝓞 E, y ∉ I ↔ ‖ρ (y : E)‖ = 1 := fun y =>
    ⟨fun h => le_antisymm (norm_int_le ρ y) (not_lt.1 h), fun h h' => absurd h (ne_of_lt h')⟩
  have hp : I.IsPrime := by
    refine ⟨(Ideal.ne_top_iff_one _).2 ((hI 1).2 (by simp)), fun {a b} hab => ?_⟩
    by_contra hc
    rw [not_or, hI, hI] at hc
    exact (hI (a * b)).2 (by simp [hc.1, hc.2]) hab
  have hpI : ((p : ℕ) : 𝓞 E) ∈ I := by
    change ‖ρ (((p : ℕ) : 𝓞 E) : E)‖ < 1
    have : ρ (((p : ℕ) : 𝓞 E) : E) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by simp
    rw [this, norm_algebraMap']
    exact Padic.norm_p_lt_one
  have hne : I ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hpI
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hpI)
  obtain ⟨n, d, h | h⟩ := (⟨I, hp, hne⟩ : HeightOneSpectrum (𝓞 E)).exists_primeCompl_mul_eq_or_mul_eq (K := E) x
  · exact ⟨d, n, (hI _).1 d.2, by rw [mul_comm]; exact h⟩
  · refine ⟨n, d, le_antisymm (norm_int_le ρ n) ?_, by rw [mul_comm]; exact h⟩
    have h1 : ‖ρ x‖ * ‖ρ (n : E)‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← (hI _).1 d.2]
      exact congrArg (fun y => ‖ρ y‖) h
    nlinarith [norm_nonneg (ρ (n : E)), norm_nonneg (ρ x)]

theorem exists_common_denom {E : Type} [Field E] [NumberField E] (ρ : E →+* ℂ_[p]) {N : ℕ} (x : Fin N → E)
    (hx : ∀ a, ‖ρ (x a)‖ ≤ 1) : ∃ (s : 𝓞 E) (n : Fin N → 𝓞 E), ‖ρ (s : E)‖ = 1 ∧ ∀ a, (s : E) * x a = n a := by
  classical
  choose s n hs hn using fun a => exists_denom ρ (x a) (hx a)
  refine ⟨∏ a, s a, fun a => (∏ b ∈ Finset.univ.erase a, s b) * n a, ?_, fun a => ?_⟩
  · have : ((∏ a, s a : 𝓞 E) : E) = ∏ a, (s a : E) := map_prod (algebraMap (𝓞 E) E) _ _
    rw [this, map_prod, norm_prod]
    exact Finset.prod_eq_one fun a _ => hs a
  · rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ a)]
    change algebraMap (𝓞 E) E (_ * _) * _ = algebraMap (𝓞 E) E (_ * _)
    rw [map_mul, map_mul, mul_assoc]
    exact congrArg _ (hn a)

theorem exists_locBasis (D : D7) (ρ : D.host.E →+* ℂ_[p]) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (hfg : L.FG) (hsp : Submodule.span D.host.E (L : Set (Fin N → D.host.E)) = ⊤) :
    ∃ P, TaylorLogMetric.LocBasisW D ρ L P := by
  classical
  obtain ⟨s, rfl⟩ := hfg
  rw [Submodule.span_span_of_tower] at hsp
  let M : (Fin N → s) → Matrix (Fin N) (Fin N) D.host.E := fun f => Matrix.of fun k a => (f a).1 k
  obtain ⟨f₀, hf₀⟩ : ∃ f, (M f).det ≠ 0 := by
    obtain ⟨b, hbs, hb, hli⟩ := exists_linearIndependent D.host.E (s : Set (Fin N → D.host.E))
    let B : Module.Basis b D.host.E (Fin N → D.host.E) := Module.Basis.mk hli (by simp [hb, hsp])
    let e := B.indexEquiv (Pi.basisFun D.host.E (Fin N))
    refine ⟨fun a => ⟨(e.symm a).1, hbs (e.symm a).2⟩, ?_⟩
    have h := (Matrix.linearIndependent_cols_iff_isUnit (A := M fun a => ⟨(e.symm a).1, hbs (e.symm a).2⟩)).1
      (hli.comp _ e.symm.injective)
    exact ((Matrix.isUnit_iff_isUnit_det _).1 h).ne_zero
  haveI : Nonempty (Fin N → s) := ⟨f₀⟩
  obtain ⟨f, hf⟩ := Finite.exists_max fun f => ‖ρ (M f).det‖
  have hpos : 0 < ‖ρ (M f).det‖ := lt_of_lt_of_le (norm_pos_iff.2 ((map_ne_zero ρ).2 hf₀)) (hf f₀)
  have hdet : (M f).det ≠ 0 := (map_ne_zero ρ).1 (norm_pos_iff.1 hpos)
  refine ⟨M f, hdet, fun a => ⟨1, by simp, ?_⟩, fun x hx => ?_⟩
  · rw [one_smul]
    exact Submodule.subset_span (f a).2
  · have key : ∃ c : Fin N → D.host.E, (∀ a, ‖ρ (c a)‖ ≤ 1) ∧ x = (M f).mulVec c := by
      induction hx using Submodule.span_induction with
      | mem y hy =>
        refine ⟨((M f).det)⁻¹ • (M f).cramer y, fun a => ?_, ?_⟩
        · have h1 : (M f).updateCol a y = M (Function.update f a ⟨y, hy⟩) := by
            ext k b
            by_cases hb : b = a
            · subst hb; simp [M]
            · simp [M, Matrix.updateCol_ne hb, Function.update_of_ne hb]
          rw [Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply, h1, map_mul, map_inv₀, norm_mul, norm_inv,
            inv_mul_le_iff₀ hpos, mul_one]
          exact hf _
        · rw [Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul, inv_mul_cancel₀ hdet, one_smul]
      | zero => exact ⟨0, by simp, by simp⟩
      | add y z _ _ hy hz =>
        obtain ⟨c, hc, rfl⟩ := hy
        obtain ⟨c', hc', rfl⟩ := hz
        refine ⟨c + c', fun a => ?_, by rw [Matrix.mulVec_add]⟩
        rw [Pi.add_apply, map_add (f := _)]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hc a) (hc' a))
      | smul r y _ hy =>
        obtain ⟨c, hc, rfl⟩ := hy
        refine ⟨(r : D.host.E) • c, fun a => ?_, by rw [Matrix.mulVec_smul]; rfl⟩
        rw [Pi.smul_apply, smul_eq_mul, map_mul, norm_mul]
        exact mul_le_one₀ (norm_int_le ρ r) (norm_nonneg _) (hc a)
    obtain ⟨c, hc, rfl⟩ := key
    obtain ⟨t, n, ht, hn⟩ := exists_common_denom ρ c hc
    refine ⟨t, ht, n, ?_⟩
    funext k
    rw [Finset.sum_apply]
    change (t : D.host.E) * (∑ a, M f k a * c a) = ∑ a, (n a : D.host.E) * M f k a
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [← hn a]; ring

theorem exists_tauHom (D : D7) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) :
    ∃ ρ : D.host.E →+* ℂ_[p], TaylorLogMetric.tauEmb D lam τ = ρ := by
  have h : ∀ x, TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := fun x =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (TaylorLogMetric.embT D τ).toRatAlgHom)
  refine ⟨lam.comp ((TaylorLogMetric.embT D τ).codRestrict TaylorLogMetric.Qbar h), funext fun x => ?_⟩
  rw [TaylorLogMetric.tauEmb, TaylorLogMetric.lamC, dite_eq_left (h x)]
  rfl

end GlobalTheory.JetTieCompare
end
end

section

open NumberField

namespace GlobalTheory.CoprimeUnitMultipliers

theorem exists_common_smul {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (U : R → Prop) (h1 : U 1) (hm : ∀ a b, U a → U b → U (a * b))
    (M N : Submodule R V) (hM : M.FG) (h : ∀ x ∈ M, ∃ s, U s ∧ s • x ∈ N) :
    ∃ s, U s ∧ ∀ x ∈ M, s • x ∈ N := by
  classical
  obtain ⟨S, rfl⟩ := hM
  have key : ∀ T : Finset V, (∀ x ∈ T, ∃ s, U s ∧ s • x ∈ N) → ∃ s, U s ∧ ∀ x ∈ T, s • x ∈ N := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; exact ⟨1, h1, by simp⟩
    | insert a T _ ih =>
      intro hT
      obtain ⟨s, hs, hsT⟩ := ih fun x hx => hT x (Finset.mem_insert_of_mem hx)
      obtain ⟨t, ht, hta⟩ := hT a (Finset.mem_insert_self a T)
      refine ⟨s * t, hm _ _ hs ht, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · rw [mul_smul]; exact N.smul_mem _ hta
      · rw [mul_comm, mul_smul]; exact N.smul_mem _ (hsT x hx)
  obtain ⟨s, hs, hS⟩ := key S fun x hx => h x (Submodule.subset_span hx)
  refine ⟨s, hs, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact N.add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact N.smul_mem _ hx

theorem norm_natCast_of_coprime {p : ℕ} [Fact p.Prime] {s : ℕ} (h : Nat.Coprime s p) :
    ‖(s : ℂ_[p])‖ = 1 := by
  have h1 : (s : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (s : ℚ_[p]) := by simp
  rw [h1, norm_algebraMap']
  exact Padic.norm_natCast_eq_one_iff.2 h.symm

theorem general {E : Type*} [Field E] {p : ℕ} [Fact p.Prime] (ρ : E →+* ℂ_[p]) {N N' : ℕ}
    (L L₁ : Submodule (𝓞 E) (Fin N → E)) (L' L₁' : Submodule (𝓞 E) (Fin N' → E))
    (P : Matrix (Fin N) (Fin N) E) (P' : Matrix (Fin N') (Fin N') E) (hfg : L₁.FG)
    (s : ℕ) (hs : Nat.Coprime s p) (hL : ∀ x ∈ L₁, (s : E) • x ∈ L)
    (s' : ℕ) (hs' : Nat.Coprime s' p) (hL' : ∀ x ∈ L', (s' : E) • x ∈ L₁')
    (hdet : P.det ≠ 0)
    (hP : ∀ x ∈ L, ∃ t : 𝓞 E, ‖ρ (t : E)‖ = 1 ∧ ∃ c : Fin N → 𝓞 E, t • x = ∑ a, c a • P.transpose a)
    (hP' : ∀ a, ∃ t : 𝓞 E, ‖ρ (t : E)‖ = 1 ∧ t • P'.transpose a ∈ L') :
    ∃ σ σ' : 𝓞 E, ‖ρ (σ : E)‖ = 1 ∧ ‖ρ (σ' : E)‖ = 1 ∧
      (∀ a : Fin N, ∀ x ∈ L₁, ∃ o : 𝓞 E, (o : E) = (σ : E) * ∑ j : Fin N, P⁻¹ a j * x j) ∧
      ∀ b : Fin N', (fun i : Fin N' => (σ' : E) * P' i b) ∈ L₁' := by
  have h1 : ‖ρ ((1 : 𝓞 E) : E)‖ = 1 := by simp
  have hm : ∀ a b : 𝓞 E, ‖ρ (a : E)‖ = 1 → ‖ρ (b : E)‖ = 1 → ‖ρ ((a * b : 𝓞 E) : E)‖ = 1 := by
    intro a b ha hb
    rw [RingOfIntegers.coe_eq_algebraMap] at ha hb ⊢
    rw [map_mul, map_mul, norm_mul, ha, hb, one_mul]
  have hn : ∀ n : ℕ, Nat.Coprime n p → ‖ρ (((n : 𝓞 E)) : E)‖ = 1 := by
    intro n hn
    rw [RingOfIntegers.coe_eq_algebraMap, map_natCast, map_natCast]
    exact norm_natCast_of_coprime hn
  have hsm : ∀ {k : ℕ} (n : ℕ) (x : Fin k → E), (n : 𝓞 E) • x = (n : E) • x := by
    intro k n x
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  obtain ⟨σ, hσ, hσL⟩ := exists_common_smul (fun t : 𝓞 E => ‖ρ (t : E)‖ = 1) h1 hm L₁
    (Submodule.span (𝓞 E) (Set.range P.transpose)) hfg (by
      intro x hx
      obtain ⟨t, ht, c, hc⟩ := hP _ (hL x hx)
      refine ⟨t * s, hm _ _ ht (hn s hs), ?_⟩
      rw [mul_smul, hsm, hc]
      exact Submodule.sum_mem _ fun a _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
  obtain ⟨σ', hσ', hσL'⟩ := exists_common_smul (fun t : 𝓞 E => ‖ρ (t : E)‖ = 1) h1 hm
    (Submodule.span (𝓞 E) (Set.range P'.transpose)) L₁'
    (Submodule.fg_span (Set.finite_range _)) (by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨t, ht, hta⟩ := hP' a
        refine ⟨s' * t, hm _ _ (hn s' hs') ht, ?_⟩
        rw [mul_smul, hsm]
        exact hL' _ hta
      | zero => exact ⟨1, h1, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨t, ht, htx⟩ := hx
        obtain ⟨u, hu, huy⟩ := hy
        refine ⟨t * u, hm _ _ ht hu, ?_⟩
        rw [smul_add]
        refine L₁'.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact L₁'.smul_mem _ htx
        · rw [mul_smul]; exact L₁'.smul_mem _ huy
      | smul a x _ hx =>
        obtain ⟨t, ht, htx⟩ := hx
        exact ⟨t, ht, by rw [smul_comm]; exact L₁'.smul_mem _ htx⟩)
  refine ⟨σ, σ', hσ, hσ', fun a x hx => ?_, fun b => ?_⟩
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 (hσL x hx)
    refine ⟨c a, ?_⟩
    have e1 : P.mulVec (fun i => (c i : E)) = (σ : E) • x := by
      funext i
      have := congrFun hc i
      simp only [Finset.sum_apply, Pi.smul_apply, Matrix.transpose_apply, Algebra.smul_def] at this
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      rw [RingOfIntegers.coe_eq_algebraMap σ, ← this]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have e2 : (fun i => (c i : E)) = (σ : E) • P⁻¹.mulVec x := by
      rw [← Matrix.mulVec_smul, ← e1, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]
    have := congrFun e2 a
    simpa [Matrix.mulVec, dotProduct] using this
  · have := hσL' _ (Submodule.subset_span ⟨b, rfl⟩)
    convert this using 1
    funext i
    simp [Pi.smul_apply, Algebra.smul_def]

theorem exists_unit_multipliers : ∀ (D : Formalism.BasicNotions.D7) (p : ℕ) [inst : Fact (Nat.Prime p)] (ρ : (Formalism.BasicNotions.D7.host D).E →+* ℂ_[p]) (N N' : ℕ) (L L₁ : Submodule (NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)) (Fin N → (Formalism.BasicNotions.D7.host D).E)) (L' L₁' : Submodule (NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)) (Fin N' → (Formalism.BasicNotions.D7.host D).E)) (P : Matrix (Fin N) (Fin N) ((Formalism.BasicNotions.D7.host D).E)) (P' : Matrix (Fin N') (Fin N') ((Formalism.BasicNotions.D7.host D).E)), Submodule.FG L₁ → Formalism.MainNotions.TaylorLogMetric.EqAt D p L L₁ → Formalism.MainNotions.TaylorLogMetric.EqAt D p L' L₁' → Formalism.MainNotions.TaylorLogMetric.LocBasisW D (⇑ρ : (Formalism.BasicNotions.D7.host D).E → ℂ_[p]) L P → Formalism.MainNotions.TaylorLogMetric.LocBasisW D (⇑ρ : (Formalism.BasicNotions.D7.host D).E → ℂ_[p]) L' P' → ∃ (σ : NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)) (σ' : NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)), ‖(ρ : (Formalism.BasicNotions.D7.host D).E → ℂ_[p]) (↑σ : (Formalism.BasicNotions.D7.host D).E)‖ = (1 : ℝ) ∧ ‖(ρ : (Formalism.BasicNotions.D7.host D).E → ℂ_[p]) (↑σ' : (Formalism.BasicNotions.D7.host D).E)‖ = (1 : ℝ) ∧ (∀ (a : Fin N), ∀ x ∈ L₁, ∃ (o : NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)), (↑o : (Formalism.BasicNotions.D7.host D).E) = (↑σ : (Formalism.BasicNotions.D7.host D).E) * ∑ j : Fin N, P⁻¹ a j * x j) ∧ ∀ (b : Fin N'), (fun (i : Fin N') ↦ (↑σ' : (Formalism.BasicNotions.D7.host D).E) * P' i b) ∈ L₁' := by
  intro D p inst ρ N N' L L₁ L' L₁' P P' hfg h h' hP hP'
  obtain ⟨s, hs, -, hL⟩ := h
  obtain ⟨s', hs', hL', -⟩ := h'
  exact general ρ L L₁ L' L₁' P P' hfg s hs hL s' hs' hL' hP.1 hP.2.2 hP'.2.1

end GlobalTheory.CoprimeUnitMultipliers
end

section

noncomputable section

namespace GlobalTheory.InertialTypesCmp

open Formalism.BasicNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open Formalism.MainNotions.SumRepresentations.At

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

open NumberField IsDedekindDomain Polynomial in
variable {R : _root_.Formalism.BasicNotions.Ranks} {H : _root_.Formalism.BasicNotions.Host R} {what₂ : _root_.Formalism.BasicNotions.Rows.Data R} (N : _root_.Formalism.BasicNotions.NData R H what₂) (A : _root_.Formalism.BasicNotions.NAut N) in
private theorem lpDim_foldr_lpSum_eq_sum_map {α : Type*} {w : _root_.Formalism.BasicNotions.PlE H}
    (f : α → A.LP w) (l : List α) :
    A.lpDim (l.foldr (fun k acc => A.lpSum (f k) acc) (A.lpZero w)) =
      (l.map fun k => A.lpDim (f k)).sum := by
  induction l with
  | nil => simp [_root_.Formalism.BasicNotions.NAut.lpDim_zero]
  | cons k l ih => simp [_root_.Formalism.BasicNotions.NAut.lpDim_sum, ih]

open NumberField IsDedekindDomain Polynomial in
variable {R : _root_.Formalism.BasicNotions.Ranks} {H : _root_.Formalism.BasicNotions.Host R} {what₂ : _root_.Formalism.BasicNotions.Rows.Data R} (N : _root_.Formalism.BasicNotions.NData R H what₂) (A : _root_.Formalism.BasicNotions.NAut N) in
private theorem lpDim_foldr_lpSum_eq_length_mul_of_const {α : Type*} {w : _root_.Formalism.BasicNotions.PlE H}
    (f : α → A.LP w) (m : ℕ) (hf : ∀ k, A.lpDim (f k) = m) (l : List α) :
    A.lpDim (l.foldr (fun k acc => A.lpSum (f k) acc) (A.lpZero w)) = l.length * m := by
  induction l with
  | nil => simp [_root_.Formalism.BasicNotions.NAut.lpDim_zero]
  | cons k l ih => simp [_root_.Formalism.BasicNotions.NAut.lpDim_sum, hf, ih, add_mul, add_comm]

open NumberField IsDedekindDomain Polynomial in
variable {R : _root_.Formalism.BasicNotions.Ranks} {H : _root_.Formalism.BasicNotions.Host R} {what₂ : _root_.Formalism.BasicNotions.Rows.Data R} (N : _root_.Formalism.BasicNotions.NData R H what₂) (A : _root_.Formalism.BasicNotions.NAut N) in
private theorem lpDim_spehLoc_eq_mul (p : _root_.Formalism.BasicNotions.Part A.CG) (w : _root_.Formalism.BasicNotions.PlE H) :
    A.lpDim (_root_.Formalism.MainNotions.N.spehLoc N A p w) = p.a * p.d := by
  unfold _root_.Formalism.MainNotions.N.spehLoc
  rw [lpDim_foldr_lpSum_eq_length_mul_of_const N A _ p.a (fun k => by rw [_root_.Formalism.BasicNotions.NAut.lpDim_tw, _root_.Formalism.BasicNotions.NAut.locG_dim])]
  simp [mul_comm]

open NumberField IsDedekindDomain Polynomial in
variable {R : _root_.Formalism.BasicNotions.Ranks} {H : _root_.Formalism.BasicNotions.Host R} {what₂ : _root_.Formalism.BasicNotions.Rows.Data R} (N : _root_.Formalism.BasicNotions.NData R H what₂) (A : _root_.Formalism.BasicNotions.NAut N) in
theorem _root_.GlobalTheory.InertialTypesCmp.lpDim_isoLoc (P : List (_root_.Formalism.BasicNotions.Part A.CG)) (w : _root_.Formalism.BasicNotions.PlE H) :
    A.lpDim (_root_.Formalism.MainNotions.N.isoLoc N A P w) = _root_.Formalism.MainNotions.N.rankIso N A P := by
  unfold _root_.Formalism.MainNotions.N.isoLoc _root_.Formalism.MainNotions.N.rankIso
  rw [lpDim_foldr_lpSum_eq_sum_map]
  simp [lpDim_spehLoc_eq_mul]

end GlobalTheory.InertialTypesCmp

end
end

section

noncomputable section

namespace GlobalTheory.GaloisInputCompare

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations.At

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem norm_le_one_of_isIntegral {K : Type} [NormedField K] [IsUltrametricDist K] {x : K} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := K)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := K))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff] at h
  exact_mod_cast h

theorem exists_inducesW (i : N.Loc) (τ : H.E →+* Qbar (N.l i)) :
    ∃ w ∈ placesOver H.E (N.l i), InducesW N i τ w := by
  have hle : ∀ x : 𝓞 H.E, ‖τ (x : H.E)‖ ≤ 1 := fun x =>
    norm_le_one_of_isIntegral (map_isIntegral_int τ (RingOfIntegers.isIntegral_coe x))
  let I : Ideal (𝓞 H.E) :=
    { carrier := {x | ‖τ (x : H.E)‖ < 1}
      zero_mem' := by simp
      add_mem' := fun {x y} hx hy => by
        change ‖τ ((x + y : 𝓞 H.E) : H.E)‖ < 1
        rw [show ((x + y : 𝓞 H.E) : H.E) = x + y from rfl, map_add (f := _)]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx hy)
      smul_mem' := fun c x hx => by
        change ‖τ ((c * x : 𝓞 H.E) : H.E)‖ < 1
        rw [show ((c * x : 𝓞 H.E) : H.E) = c * x from rfl, map_mul, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hle c)).trans_lt hx }
  have hI : ∀ x : 𝓞 H.E, x ∈ I ↔ ‖τ (x : H.E)‖ < 1 := fun x => Iff.rfl
  have hl : ((N.l i : ℕ) : 𝓞 H.E) ∈ I := by
    rw [hI, show (((N.l i : ℕ) : 𝓞 H.E) : H.E) = (N.l i : ℕ) by simp, map_natCast,
      ← map_natCast (algebraMap ℚ_[N.l i] (PadicAlgCl (N.l i))), PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have hP : I.IsPrime := by
    refine ⟨fun h => ?_, fun {x y} h => ?_⟩
    · have := (hI 1).1 (h ▸ Submodule.mem_top)
      simp at this
    · rw [hI, show ((x * y : 𝓞 H.E) : H.E) = x * y from rfl, map_mul, norm_mul] at h
      by_contra hn
      rw [not_or, hI, hI, not_lt, not_lt] at hn
      exact absurd h (not_lt.2 (one_le_mul_of_one_le_of_one_le hn.1 hn.2))
  refine ⟨⟨I, hP, fun h => ?_⟩, hl, fun x => (hI x).symm⟩
  rw [h, Ideal.mem_bot] at hl
  exact (N.lPrime i).out.ne_zero (by exact_mod_cast hl)


end GlobalTheory.GaloisInputCompare
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.SSComplement

section Rep

variable {Γ k : Type} [Group Γ] [Field k]

def blockM {a b n : ℕ} (e0 : Fin a ⊕ Fin b ≃ Fin n) (ρ₁ : Γ →* GL (Fin a) k) (ρ₂ : Γ →* GL (Fin b) k) :
    Γ →* Matrix (Fin n) (Fin n) k where
  toFun g := Matrix.reindex e0 e0
    (Matrix.fromBlocks (ρ₁ g : Matrix (Fin a) (Fin a) k) 0 0 (ρ₂ g : Matrix (Fin b) (Fin b) k))
  map_one' := by simp
  map_mul' g g' := by simp [Matrix.fromBlocks_multiply]

def diagM {t : ℕ} (χ : Fin t → Γ →* kˣ) : Γ →* Matrix (Fin t) (Fin t) k where
  toFun g := Matrix.diagonal fun c => ((χ c g : kˣ) : k)
  map_one' := by simp
  map_mul' g h := by simp [Matrix.diagonal_mul_diagonal]

theorem blockM_ss {a b n : ℕ} (e0 : Fin a ⊕ Fin b ≃ Fin n) (ρ₁ : Γ →* GL (Fin a) k)
    (ρ₂ : Γ →* GL (Fin b) k) (h₁ : IsSSRep ρ₁) (h₂ : IsSSRep ρ₂) : IsSSRep (blockM e0 ρ₁ ρ₂).toHomUnits := by
  refine GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.isSSRep_of_prod ((LinearEquiv.funCongrLeft k k e0).trans
    (LinearEquiv.sumArrowLequivProdArrow _ _ k k)) (fun g v => ?_) h₁ h₂
  show _ = _
  ext i <;> simp [blockM, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, LinearMap.funLeft] <;> rfl

theorem ss_of_scalar {a : ℕ} (ρ : Γ →* GL (Fin a) k) (c : Γ → k)
    (h : ∀ g v, (ρ g : Matrix (Fin a) (Fin a) k).mulVec v = c g • v) : IsSSRep ρ := by
  intro W _
  obtain ⟨W', hW'⟩ := W.exists_isCompl
  exact ⟨W', fun g v hv => by rw [h]; exact W'.smul_mem _ hv, hW'⟩

theorem diagM_ss : ∀ {t : ℕ} (χ : Fin t → Γ →* kˣ), IsSSRep (diagM χ).toHomUnits := by
  intro t
  induction t with
  | zero =>
    intro χ
    exact ss_of_scalar _ (fun _ => 0) fun g v => funext fun c => c.elim0
  | succ t ih =>
    intro χ
    refine GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.isSSRep_of_prod (ρ₁ := (diagM fun c : Fin t => χ (Fin.castAdd 1 c)).toHomUnits)
      (ρ₂ := (diagM fun c : Fin 1 => χ (Fin.natAdd t c)).toHomUnits)
      ((LinearEquiv.funCongrLeft k k finSumFinEquiv).trans
        (LinearEquiv.sumArrowLequivProdArrow _ _ k k)) (fun g v => ?_) (ih _)
      (ss_of_scalar _ (fun g => ((χ (Fin.last t) g : kˣ) : k)) fun g v => ?_)
    · show _ = _
      ext i <;> simp [diagM, Matrix.mulVec_diagonal, LinearMap.funLeft]
    · funext c
      obtain rfl : c = 0 := Subsingleton.elim _ _
      change (Matrix.diagonal fun c : Fin 1 => ((χ (Fin.natAdd t c) g : kˣ) : k)).mulVec v 0 = _
      exact Matrix.mulVec_diagonal _ _ _

end Rep

end GlobalTheory.SSComplement
end
end
