module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle022
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FrobeniusLiftEmbeddingsUnit
public import Formalism.LocalToGlobal.CharacterGerms.Bundle005
public import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.Bundle001
public import Formalism.LocalToGlobal.CharacterGerms.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle034
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle007
public import Mathlib.RingTheory.DedekindDomain.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicUnitQuotientPrincipalBasis
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
import Mathlib.NumberTheory.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle033
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import ReciprocityTheory.DualLattices.FormalChartAtZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001

@[expose] public section

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.SeparatingSeq

open TeichSeq

variable {C : Type} [Field C] {V : VF C}

theorem ge_of_mul_unit {w : ℝ} {a u : C} (hu : V.Ge 0 u) (hu' : ¬ V.MM u)
    (h : V.Ge w (a * u)) : V.Ge w a := by
  have h0 : V.v u = 0 := le_antisymm (not_lt.1 hu') (by simpa [VF.Ge] using hu)
  unfold VF.Ge at h ⊢
  rwa [V.v.map_mul, h0, add_zero] at h

theorem ge_pow_pow_sub {t c : C} (ht : V.Ge 0 t) (hc : V.Ge 0 c) (h : V.Ge 1 (t - c)) (n : ℕ) :
    V.Ge n (t ^ V.l ^ n - c ^ V.l ^ n) := by
  have hq : V.Ge 0 ((V.l : C)⁻¹ * (t - c)) := by simpa using h.l_inv_mul
  have hd : (V.l : intRing V) ∣ (⟨t, ht⟩ : intRing V) - ⟨c, hc⟩ :=
    ⟨⟨_, hq⟩, Subtype.ext (by
      show t - c = ((V.l : intRing V) : C) * ((V.l : C)⁻¹ * (t - c))
      rw [SubringClass.coe_natCast, mul_inv_cancel_left₀ VF.l_ne_zero])⟩
  obtain ⟨z, hz⟩ := (pow_dvd_pow _ (Nat.le_succ n)).trans (dvd_sub_pow_of_dvd_sub hd n)
  have hz' : t ^ V.l ^ n - c ^ V.l ^ n = (z : C) * (V.l : C) ^ n := by
    have := congrArg Subtype.val hz
    simpa [mul_comm] using this
  rw [hz']
  exact VF.Ge.mul_int z.2 (ge_l_pow V n)

theorem main : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] (d : ℕ) [NeZero d] (em : ZMod d → (O →+* C)), (∀ a x, V.Ge 0 (em a x)) → (∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)) → (∃ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) ∧ (∀ a, V.MM (em a ε - 1)) ∧ ∀ x : O, (∀ a, V.MM (em a x)) → ∃ y, ε * x = (V.l : O) * y) → ∃ s : ℕ → O, (∀ n, ∃ y, s (n + 1) - s n = (V.l : O) ^ n * y) ∧ (∀ (a : ZMod d) (K : ℕ), ∃ n0, ∀ n ≥ n0, V.Ge K (1 - em a (s n))) ∧ ∀ φ : O →+* C, (∀ x, V.Ge 0 (φ x)) → (∀ a, ∃ x, V.v (em a x - φ x) = 0) → ∀ K : ℕ, ∃ n0, ∀ n ≥ n0, V.Ge K (0 - φ (s n)) := by
  intro C _ _ V O _ d _ em hint hfrob ⟨ε, ⟨y0, hε2⟩, hε1, hεP⟩
  have hεpow : ∀ n, (V.l : O) ∣ ε ^ (n + 1) - ε := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      have : ε ^ (n + 1 + 1) - ε = (ε ^ (n + 1) - ε) * ε + (ε * ε - ε) := by ring
      rw [this]
      exact dvd_add (ih.mul_right _) ⟨y0, hε2⟩
  have hprod : ∀ ψ : O →+* C, (∀ x, V.Ge 0 (ψ x)) → V.Ge 1 ((ψ ε - 1) * ψ ε) := fun ψ hψ => by
    have h1 : (ψ ε - 1) * ψ ε = ψ y0 * (V.l : C) := by
      have := congrArg ψ hε2
      rw [map_sub, map_mul, map_mul, map_natCast] at this
      linear_combination this
    rw [h1]
    exact (hψ y0).mul_int VF.ge_l
  have hnot : ∀ t : C, V.MM t → ¬ V.MM (t - 1) := fun t h1 h2 => by
    have h3 : V.MM (-(t - 1)) := by unfold VF.MM; rw [V.v.map_neg]; exact h2
    have h4 : 0 < V.v (t + -(t - 1)) := V.v.map_lt_add h1 h3
    simp at h4
  refine ⟨fun n => ε ^ V.l ^ n, fun n => ?_, fun a K => ⟨K, fun n hn => ?_⟩,
    fun φ hφ hsep K => ⟨K, fun n hn => ?_⟩⟩
  · have h1 := hεpow (V.l - 1)
    rw [Nat.sub_add_cancel V.l_prime.one_lt.le] at h1
    have h2 := (pow_dvd_pow _ (Nat.le_succ n)).trans (dvd_sub_pow_of_dvd_sub h1 n)
    rw [← pow_mul, ← pow_succ'] at h2
    exact h2
  · have h1 : V.Ge 1 (em a ε - 1) :=
      ge_of_mul_unit (hint a ε) (fun h => hnot _ h (hε1 a)) (hprod _ (hint a))
    have h2 := (ge_pow_pow_sub (hint a ε) VF.Ge.one h1 n).neg
    rw [one_pow, neg_sub, ← map_pow] at h2
    exact h2.mono (by exact_mod_cast hn)
  · have hm : V.MM (φ ε) := by
      by_contra hu
      obtain ⟨a, ha⟩ := ResidueChar.main C V O d em hint hfrob φ hφ (fun x hx => by
        obtain ⟨y, hy⟩ := hεP x hx
        have h1 : φ x * φ ε = φ y * (V.l : C) := by
          have := congrArg φ hy
          rw [map_mul, map_mul, map_natCast] at this
          linear_combination this
        refine mm_of_ge_one V (ge_of_mul_unit (hφ ε) hu ?_)
        rw [h1]
        exact (hφ y).mul_int VF.ge_l)
      obtain ⟨x, hx⟩ := hsep a
      have h2 : 0 < V.v (φ x - em a x) := ha x
      rw [← neg_sub, V.v.map_neg, hx] at h2
      exact lt_irrefl _ h2
    have h1 : V.Ge 1 (φ ε - 0) := by
      rw [sub_zero]
      refine ge_of_mul_unit ((hφ ε).sub VF.Ge.one) (hnot _ hm) ?_
      rw [mul_comm]
      exact hprod φ hφ
    have h2 := (ge_pow_pow_sub (hφ ε) (VF.Ge.zero 0) h1 n).neg
    rw [zero_pow (pow_ne_zero _ V.l_prime.ne_zero), neg_sub, ← map_pow] at h2
    exact h2.mono (by exact_mod_cast hn)

end GlobalTheory.SeparatingSeq
end

section

noncomputable section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowVal

open GlobalTheory.RowValueCheck

theorem valOf_eq_hRow : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ) (H : X.Hyps V) (N : ℕ) (P : MvPolynomial (Fin N × WV I) C) (kind : Fin N → Option (Fin 2 × ZMod d × ZMod d)), RowsOK (X.rowData H).G (X.rowData H).Alt P kind → ∀ gr : Fin N → MvPowerSeries (WV I) C, ValOf (X.rowData H).hL P kind gr = jetAt0 P (∏ ρ, (rowCopy ρ (gr ρ) * mvExp (rowCopy ρ X.hRow))) := by
  intro C _ V d _ I _ κ _ X H N P kind hk gr
  classical
  rw [valOf_eq]
  set S : Set (Fin N × WV I) := {x | ∃ μ ∈ P.support, μ x ≠ 0} with hS
  have key : ∀ ρ, Agree {w | (ρ, w) ∈ S} (hOf (X.rowData H).hL (kind ρ)) X.hRow := by
    intro ρ μ hμ
    rcases hr : kind ρ with _ | ⟨g, a, a'⟩
    · obtain ⟨g, hg⟩ := hk.2 ρ hr
      have h1 : ∀ w, μ w ≠ 0 → w.1 = g := fun w hw => by
        obtain ⟨ν, hν, hν'⟩ := hμ w hw
        exact hg ν hν w hν'
      show (0 : C) = _
      refine (H.axes μ ?_).symm
      have hg2 : g = 0 ∨ g = 1 := (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) g
      rcases hg2 with rfl | rfl
      · exact Or.inl fun w hw => h1 w (Finsupp.mem_support_iff.1 hw)
      · exact Or.inr fun w hw => h1 w (Finsupp.mem_support_iff.1 hw)
    · obtain ⟨-, -, hl⟩ := hk.1 ρ g a a' hr
      have h1 : ∀ w, μ w ≠ 0 → X.OnLf g a a' w := fun w hw => by
        obtain ⟨ν, hν, hν'⟩ := hμ w hw
        exact hl ν hν w hν'
      exact if_pos fun w hw => h1 w (Finsupp.mem_support_iff.1 hw)
  have hA := Agree.prod (S := S) Finset.univ (fun ρ =>
    Agree.mul (F := rowCopy ρ (gr ρ)) (F' := rowCopy ρ (gr ρ)) (fun _ _ => rfl)
      (agree_rowCopy S ρ _ _ (key ρ)).exp)
  unfold jetAt0
  exact Finset.sum_congr rfl fun μ hμ => by rw [hA μ fun x hx => ⟨μ, hμ, hx⟩]

end GlobalTheory.RowVal
end
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.MainTerm

theorem linPull_coord_weight_nonneg : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) [NeZero d] (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (t : I → MvPowerSeries I C), S.IsT t → ∀ (N : ℕ) (e : Fin N → I → C), (∀ j x, V.Ge 0 (e j x)) → ∀ (c : I) (μ : Fin N →₀ ℕ), V.Ge (-((μ.degree : ℝ) / ((V.l : ℝ) - 1))) (MvPowerSeries.coeff μ (linPull e (t c))) := by
  intro C _ _ V d _ I J _ _ G S t hT N e he c μ

  have hU : ∀ i j, V.Ge 0 (S.U⁻¹ i j) := inv_int S.U (fun i j => S.U_int i j) S.unimod

  have hco : ∀ (h : I ⊕ J → C) (w : ℝ), (∀ k, V.Ge w (h (Sum.inl k))) → ∀ b, V.Ge w (S.co h b) := by
    intro h w hh b
    have hs := VF.Ge.sum (s := Finset.univ) (fun k _ => VF.Ge.mul (hh k) (hU k b))
    rw [add_zero] at hs
    exact hs

  obtain ⟨z, hze, hzi⟩ : ∃ z : I → Fin N → C,
      (∀ j x, e j x = ∑ b, z b j * S.tan b x) ∧ ∀ b j, V.Ge 0 (z b j) := by
    refine ⟨fun b j => S.co (Sum.elim (e j) 0) b, fun j x => ?_, fun b j => hco _ 0 (fun k => he j k) b⟩
    have hs := S.co_spec (Sum.elim (e j) 0) x
    simp only [Sys.U, Matrix.of_apply, Sum.elim_inl] at hs
    exact hs.symm

  obtain ⟨al, hal0, halk, hali⟩ : ∃ al : I → ℕ → I → C, (∀ c b, al c 0 b = if c = b then 1 else 0) ∧
      (∀ c (k : ℕ) x, 1 ≤ k → S.al c k x = ∑ b, al c k b * S.al b 0 x) ∧
      ∀ c (n : ℕ) b, V.Ge (-(n : ℝ)) (al c n b) := by
    refine ⟨fun c k b => if k = 0 then (if c = b then 1 else 0) else S.co (Sum.elim (S.al c k) 0) b,
      fun c b => if_pos rfl, ?_, ?_⟩
    · intro c k x hk
      have hk0 : k ≠ 0 := by omega
      have hs := S.co_spec (Sum.elim (S.al c k) 0) x
      simp only [Sys.U, Matrix.of_apply, Sum.elim_inl] at hs
      rw [← hs]
      refine Finset.sum_congr rfl fun b _ => ?_
      beta_reduce
      rw [if_neg hk0, Sys.al, S.cur_zero_inl]
    · intro c n b
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · beta_reduce
        rw [if_pos rfl, Nat.cast_zero, neg_zero]
        split_ifs
        · exact VF.Ge.one
        · exact VF.Ge.zero _
      · beta_reduce
        rw [if_neg (show n ≠ 0 by omega)]
        exact hco _ _ (fun k => lattice_inclusion_forms_injective G S c n (Sum.inl k)) b
  obtain ⟨h0, hlog, -⟩ := GlobalTheory.T.formalGroupCoordinates_pullback_linear_tangentBasis C V d I J G S t hT (Fin N) e z al hze hal0 halk

  let σ := Fintype.equivFin I
  have key := GlobalTheory.ExpWeight.ordGe_of_lgSum_eq_linear C V.v V.l V.l_prime V.v_l (Fintype.card I) N
    (fun a n b => al (σ.symm a) n (σ.symm b)) (fun a j => z (σ.symm a) j)
    (fun a => linPull e (t (σ.symm a)))
    (fun a b => by simp only [hal0, Equiv.apply_eq_iff_eq])
    (fun a n b => hali _ _ _)
    (fun a j => by
      have hz := hzi (σ.symm a) j
      unfold VF.Ge at hz
      rwa [WithTop.coe_zero] at hz)
    (fun a => h0 _) ?_ (σ c)
  · have hα := key μ
    simp only [Equiv.symm_apply_apply] at hα
    unfold VF.Ge
    refine le_trans ?_ hα
    refine WithTop.coe_le_coe.mpr ?_
    have hl : (1 : ℝ) < V.l := by exact_mod_cast V.l_prime.one_lt
    have hpos : (0 : ℝ) < 1 / ((V.l : ℝ) - 1) := by
      have : (0 : ℝ) < (V.l : ℝ) - 1 := by linarith
      positivity
    rw [← Finset.mul_sum, ← Nat.cast_sum, ← Finsupp.degree_eq_sum]
    have hd : ((μ.degree : ℕ) : ℝ) / ((V.l : ℝ) - 1) = 1 / ((V.l : ℝ) - 1) * (μ.degree : ℝ) := by ring
    rw [hd]
    linarith
  · intro b
    ext α
    show (∑ n ∈ Finset.range (α.degree + 1), ∑ a, al (σ.symm a) n (σ.symm b) *
      MvPowerSeries.coeff α (linPull e (t (σ.symm a)) ^ (V.l ^ n))) = _
    rw [← hlog (σ.symm b) α]
    refine Finset.sum_congr rfl fun n _ => ?_
    exact Equiv.sum_comp σ.symm (fun a => al a n (σ.symm b) * MvPowerSeries.coeff α (linPull e (t a) ^ (V.l ^ n)))

end GlobalTheory.MainTerm
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.padic_unit_quotient_principal_basis : ∀ (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (w : PlaceU p OE), IsDomain ((ℤ_[p] ⊗[ℤ] OE) ⧸ Ideal.span {1 - w.e}) ∧ IsPrincipalIdealRing ((ℤ_[p] ⊗[ℤ] OE) ⧸ Ideal.span {1 - w.e}) ∧ ∃ (α : ℤ_[p] ⊗[ℤ] OE) (b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e))), ∀ k, (b k : ℤ_[p] ⊗[ℤ] OE) = w.e * α ^ (k : ℕ) := by
  first | exact @GlobalTheory.PlaceMono.place_monogenic | exact GlobalTheory.PlaceMono.place_monogenic | (intros; apply GlobalTheory.PlaceMono.place_monogenic <;> assumption)
end
