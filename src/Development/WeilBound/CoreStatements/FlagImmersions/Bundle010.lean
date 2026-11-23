module

import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle028
import Development.WeilBound.CoreStatements.FlagImmersions.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
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

@[expose] public section

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace RootFieldNumerics.EffN

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem smooth_comb {J : Type} [Fintype J] {ℓ : J → HermLine ι} (hℓ : ∀ j, IsSmoothHerm (ℓ j))
    (n : J → ℤ) : IsSmoothHerm (combLine ℓ n) := by
  show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => ∏ j, (ℓ j).h z ^ n j)
    {z : (k : K) × ι k → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  exact contDiffOn_prod (fun j _ => RootFieldNumerics.Ii.contDiffOn_zpow_h (ℓ j) (hℓ j) (n j))

theorem comb_a {J : Type} [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ) :
    (combLine ℓ n).a = ∑ j, n j • (ℓ j).a := rfl

theorem exists_smooth (b : K → ℤ) : ∃ B : HermLine ι, IsSmoothHerm B ∧ B.a = b := by
  apply PositivityTheory.UnitarySelfGeneration.RC.exists_line <;> assumption

theorem smooth_snoc {e : ℕ} {L : Fin e → HermLine ι} {X : HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    (hX : IsSmoothHerm X) (j : Fin (e + 1)) :
    IsSmoothHerm ((Fin.snoc L X : Fin (e + 1) → HermLine ι) j) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa using hX
  · simpa using hL i

theorem last_lin (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (P : Ideal (MRing ι)) (e : ℕ)
    (hP : IsArithVar P (e + 2)) (L : Fin e → HermLine ι) (A B C : HermLine ι) (m : ℤ)
    (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) (hC : IsSmoothHerm C)
    (hdeg : C.a = B.a + m • A.a) :
    ptsIntegral P (fun j z => Real.log (((Fin.snoc L C : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1) =
      ptsIntegral P (fun j z => Real.log (((Fin.snoc L B : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1) +
        m * ptsIntegral P (fun j z => Real.log (((Fin.snoc L A : Fin (e + 1) → HermLine ι) j).h z))
          (fun _ => 1) := by
  classical
  let ℓ : Fin e ⊕ Bool → HermLine ι := Sum.elim L (fun t => if t then A else B)
  have hℓ : ∀ j, IsSmoothHerm (ℓ j) := by
    rintro (i | _ | _) <;> simp [ℓ, hL, hA, hB]
  let n : Fin (e + 1) → Fin e ⊕ Bool → ℤ :=
    Fin.snoc (fun i => Pi.single (Sum.inl i) 1)
      (Pi.single (Sum.inr false) 1 + m • Pi.single (Sum.inr true) 1)
  obtain ⟨hexp, hperm⟩ := GlobalTheory.T.log_integral_multilinear II hII K ι P (e + 1) (Fin e ⊕ Bool) ℓ n hP hℓ
  have h1 := hperm (fun k => combLine ℓ (n k)) (Fin.snoc L C) 1 (fun k => smooth_comb hℓ _)
    (smooth_snoc hL hC) (by
      intro k
      simp only [Equiv.Perm.coe_one, id]
      rw [comb_a]
      refine Fin.lastCases ?_ (fun i => ?_) k
      · simp [n, ℓ, Fintype.sum_sum_type, Pi.single_apply, hdeg]
        abel
      · simp [n, ℓ, Fintype.sum_sum_type, Pi.single_apply])
  let w0 : Fin (e + 1) → Fin e ⊕ Bool := Fin.snoc (fun i => Sum.inl i) (Sum.inr false)
  let w1 : Fin (e + 1) → Fin e ⊕ Bool := Fin.snoc (fun i => Sum.inl i) (Sum.inr true)
  have hne : w0 ≠ w1 := by
    intro h
    have := congrFun h (Fin.last e)
    simp [w0, w1] at this
  have hzero : ∀ w : Fin (e + 1) → Fin e ⊕ Bool, w ≠ w0 ∧ w ≠ w1 →
      (∏ k, (n k (w k) : ℝ)) * ptsIntegral P (fun k z => Real.log ((ℓ (w k)).h z)) (fun _ => 1) = 0 := by
    rintro w ⟨hw0, hw1⟩
    apply mul_eq_zero_of_left
    by_contra hprod
    have hf : ∀ k, (n k (w k) : ℝ) ≠ 0 := fun k =>
      Finset.prod_ne_zero_iff.mp hprod k (Finset.mem_univ _)
    have hcs : ∀ i : Fin e, w (Fin.castSucc i) = Sum.inl i := by
      intro i
      have := hf (Fin.castSucc i)
      simp [n, Pi.single_apply] at this
      exact this
    have hl := hf (Fin.last e)
    rcases hw : w (Fin.last e) with i | (_ | _)
    · rw [hw] at hl
      simp [n, Pi.single_apply] at hl
    · exact hw0 (funext fun k => by
        refine Fin.lastCases ?_ (fun i => ?_) k
        · simp [w0, hw]
        · simp [w0, hcs i])
    · exact hw1 (funext fun k => by
        refine Fin.lastCases ?_ (fun i => ?_) k
        · simp [w1, hw]
        · simp [w1, hcs i])
  have e0 : ∀ k, ℓ (w0 k) = (Fin.snoc L B : Fin (e + 1) → HermLine ι) k := by
    intro k
    refine Fin.lastCases ?_ (fun i => ?_) k <;> simp [ℓ, w0]
  have e1 : ∀ k, ℓ (w1 k) = (Fin.snoc L A : Fin (e + 1) → HermLine ι) k := by
    intro k
    refine Fin.lastCases ?_ (fun i => ?_) k <;> simp [ℓ, w1]
  have p0 : ∏ k, (n k (w0 k) : ℝ) = 1 := by
    rw [Fin.prod_univ_castSucc]
    simp [n, w0]
  have p1 : ∏ k, (n k (w1 k) : ℝ) = m := by
    rw [Fin.prod_univ_castSucc]
    simp [n, w1]
  rw [h1, hexp, Fintype.sum_eq_add w0 w1 hne hzero, p0, p1]
  simp only [e0, e1, one_mul]

end RootFieldNumerics.EffN
end
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace RootFieldNumerics.GeoComb

theorem exists_perm_of_map_eq {J : Type} {d : ℕ} (f g : Fin d → J)
    (h : Finset.univ.val.map f = Finset.univ.val.map g) : ∃ σ : Equiv.Perm (Fin d), ∀ k, f k = g (σ k) := by
  classical
  have hc : ∀ j, Fintype.card {a // f a = j} = Fintype.card {a // g a = j} := by
    intro j
    have := congrArg (Multiset.count j) h
    simp only [Multiset.count_map] at this
    rw [Fintype.card_subtype, Fintype.card_subtype]
    convert this using 1 <;> simp [Finset.card_def, Finset.filter_val, eq_comm]
  let e : ∀ j, {a // f a = j} ≃ {a // g a = j} := fun j => Fintype.equivOfCardEq (hc j)
  let σ : Equiv.Perm (Fin d) :=
    ((Equiv.sigmaFiberEquiv f).symm.trans (Equiv.sigmaCongrRight e)).trans (Equiv.sigmaFiberEquiv g)
  refine ⟨σ, fun a => ?_⟩
  exact ((e (f a) ⟨a, rfl⟩).2).symm

theorem toMultiset_word {J : Type} {d : ℕ} (w : Fin d → J) :
    Finsupp.toMultiset (∑ k, Finsupp.single (w k) 1 : J →₀ ℕ) = Finset.univ.val.map w := by
  rw [Finsupp.toMultiset_sum]
  simp only [Finsupp.toMultiset_single, one_smul]
  rw [← Multiset.sum_map_singleton (Finset.univ.val.map w), Multiset.map_map]
  rfl

theorem degree_word {J : Type} {d : ℕ} (w : Fin d → J) :
    (∑ k, Finsupp.single (w k) 1 : J →₀ ℕ).degree = d := by

  rw [map_sum]
  simp

theorem monoLines_word {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Type} (ℓ : J → HermLine ι)
    {d : ℕ} (w : Fin d → J) :
    ∃ σ : Equiv.Perm (Fin d), ∀ k, monoLines ℓ (∑ k, Finsupp.single (w k) 1) d k = ℓ (w (σ k)) := by
  set m : J →₀ ℕ := ∑ k, Finsupp.single (w k) 1 with hm
  set L : List J := (Finsupp.toMultiset m).toList with hL
  have hML : (L : Multiset J) = Finset.univ.val.map w := by
    rw [hL, Multiset.coe_toList, hm, toMultiset_word]
  have hlen : L.length = d := by
    have := congrArg Multiset.card hML
    simpa using this
  let f : Fin d → J := fun k => L.get (Fin.cast hlen.symm k)
  have hf : List.ofFn f = L :=
    List.ext_get (by simp [hlen]) (fun i h1 h2 => by simp [f])
  have hmap : Finset.univ.val.map f = Finset.univ.val.map w := by
    rw [Fin.univ_val_map, hf, hML]
  obtain ⟨σ, hσ⟩ := exists_perm_of_map_eq f w hmap
  refine ⟨σ, fun k => ?_⟩
  have hk : (k : ℕ) < L.length := by
    rw [hlen]
    exact k.2
  rw [← hσ k]
  simp only [monoLines]
  rw [dite_eq_left hk]
  rfl

theorem map_prod_lin {J : Type} [Fintype J] [DecidableEq J] {d : ℕ} (Φ : MvPolynomial J ℝ →ₗ[ℝ] ℝ)
    (c : Fin d → J → ℝ) :
    Φ (∏ k, ∑ j, C (c k j) * X j) =
      ∑ w : Fin d → J, (∏ k, c k (w k)) * Φ (monomial (∑ k, Finsupp.single (w k) 1) 1) := by

  rw [Finset.prod_univ_sum, map_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Finset.prod_mul_distrib, ← map_prod, MvPolynomial.C_mul', map_smul, smul_eq_mul,
    MvPolynomial.monomial_sum_one]
  rfl

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

def cf (lam : Wt Ψ N) (s : ℝ) : Option (Ψ × Fin N) → ℝ
  | some r => -lam r.1 r.2
  | none => s

theorem linA_eq (lam : Wt Ψ N) (s : ℝ) : linA lam s = ∑ j, C (cf lam s j) * X j := by
  rw [Fintype.sum_option]

  simp only [linA, toA, linRoot, cf, map_neg, map_sum, map_mul, rename_C, rename_X, neg_mul,
  Finset.sum_neg_distrib]
  ring

theorem coef_mul (M : RootModel Ψ N) (lam : Wt Ψ N) (s : ℝ) (j : Option (Ψ × Fin N)) :
    M.coef lam s j * (M.kA : ℝ) ^ ((Finsupp.single j 1 : Option (Ψ × Fin N) →₀ ℕ) none) = cf lam s j := by
  cases j with
  | none =>
    have hk : (M.kA : ℝ) ≠ 0 := by exact_mod_cast M.kA_pos.ne'
    simp [RootModel.coef, cf]
    field_simp
  | some r =>
    simp [RootModel.coef, cf]

theorem line_smooth (M : RootModel Ψ N) (t : ℝ) (j : Option (Ψ × Fin N)) : IsSmoothHerm (M.line t j) := by
  cases j with
  | none => exact M.A_smooth
  | some r => exact M.x_smooth t r

theorem line_deg (M : RootModel Ψ N) (t t' : ℝ) (j : Option (Ψ × Fin N)) : (M.line t j).a = (M.line t' j).a := by
  cases j with
  | none => rfl
  | some r => simp [RootModel.line, M.x_deg]

theorem geoFun_monomial (M : RootModel Ψ N) (m : Option (Ψ × Fin N) →₀ ℕ) :
    M.geoFun (monomial m 1) = M.geoMono m := by
  have hb : (monomial m 1 : RPA Ψ N) = basisMonomials (Option (Ψ × Fin N)) ℝ m := by
    simp [MvPolynomial.coe_basisMonomials]
  rw [hb]
  exact Module.Basis.constr_basis _ _ _ _

end RootFieldNumerics.GeoComb

namespace RootFieldNumerics

open GeoComb

theorem root_model_points_integral : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Fin (dimFl Ψ N) → Wt Ψ N) (s : Fin (dimFl Ψ N) → ℝ) (q : ℕ) (n : Fin (dimFl Ψ N) → Option (Ψ × Fin N) → ℤ), (∀ k j, (n k j : ℝ) = q * M.coef (lam k) (s k) j) → ptsIntegral M.P (fun k z => Real.log ((combLine (M.line t) (n k)).h z)) (fun _ => 1) = M.δ * (q : ℝ) ^ dimFl Ψ N * M.geoFun (∏ k, linA (lam k) (s k)) := by
  intro II hII Ψ _ N M t lam s q n hn
  classical
  have hP : IsArithVar M.P (dimFl Ψ N + 1) := M.arith
  have hsm : ∀ j, IsSmoothHerm (M.line t j) := line_smooth M t
  obtain ⟨hexp, hperm⟩ :=
    GlobalTheory.T.log_integral_multilinear II hII M.K M.ι M.P (dimFl Ψ N) (Option (Ψ × Fin N)) (M.line t) n hP hsm
  have hterm : ∀ w : Fin (dimFl Ψ N) → Option (Ψ × Fin N),
      ptsIntegral M.P (fun k z => Real.log ((M.line t (w k)).h z)) (fun _ => 1) =
        M.δ * (M.kA : ℝ) ^ ((∑ k, Finsupp.single (w k) 1 : Option (Ψ × Fin N) →₀ ℕ) none) *
          M.geoMono (∑ k, Finsupp.single (w k) 1) := by
    intro w
    obtain ⟨σ, hσ⟩ := monoLines_word (M.line 1) w
    have hmono_sm : ∀ k, IsSmoothHerm (monoLines (M.line 1) (∑ k, Finsupp.single (w k) 1) (dimFl Ψ N) k) := by
      intro k
      rw [hσ k]
      exact line_smooth M 1 _
    rw [hperm (monoLines (M.line 1) (∑ k, Finsupp.single (w k) 1) (dimFl Ψ N)) (fun k => M.line t (w k))
      σ⁻¹ hmono_sm (fun k => hsm _)
      (fun k => by
        rw [hσ, show σ (σ⁻¹ k) = k by simp]
        exact line_deg M t 1 _)]
    have hδ : (M.δ : ℝ) ≠ 0 := by exact_mod_cast M.δ_pos.ne'
    have hk : (M.kA : ℝ) ≠ 0 := by exact_mod_cast M.kA_pos.ne'
    rw [RootModel.geoMono, if_pos (degree_word w)]
    field_simp
  rw [hexp]
  simp_rw [linA_eq]
  rw [map_prod_lin, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [hterm w, geoFun_monomial]
  have hc : (∏ k, (n k (w k) : ℝ)) *
      (M.kA : ℝ) ^ ((∑ k, Finsupp.single (w k) 1 : Option (Ψ × Fin N) →₀ ℕ) none) =
        (q : ℝ) ^ dimFl Ψ N * ∏ k, cf (lam k) (s k) (w k) := by
    rw [Finsupp.finsetSum_apply, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    simp_rw [hn, mul_assoc, coef_mul]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  linear_combination ((M.δ : ℝ) * M.geoMono (∑ k, Finsupp.single (w k) 1)) * hc

end RootFieldNumerics
end
end

end

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem geoFun_comb_mixed : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Fin (dimFl Ψ N) → Wt Ψ N) (s : Fin (dimFl Ψ N) → ℝ) (q : ℕ) (n : Fin (dimFl Ψ N) → Option (Ψ × Fin N) → ℤ), (∀ k j, (n k j : ℝ) = q * M.coef (lam k) (s k) j) → ptsIntegral M.P (fun k z => Real.log ((combLine (M.line t) (n k)).h z)) (fun _ => 1) = M.δ * (q : ℝ) ^ dimFl Ψ N * M.geoFun (∏ k, linA (lam k) (s k)) := by
  exact RootFieldNumerics.root_model_points_integral

end GlobalTheory.CompanionTheory.Ar.Top

end
end
