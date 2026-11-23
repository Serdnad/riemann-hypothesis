module

public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle033
public import Formalism.LocalToGlobal.CharacterGerms.Bundle022
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeBiadditiveSymmAdjointIntegralEnd
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReciprocityTheory.DualLattices.Bundle007
public import ReciprocityTheory.DualLattices.DiscriminantColengthStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LatticeInequalityValuationIntegers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import ReciprocityTheory.DualLattices.FormalChartAtZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

noncomputable section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowVal.PlaneRead

open MvPowerSeries EndCalc

variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
  {X : RawChart C d I κ}

def expAt (X : RawChart C d I κ) {ω : Type} [Fintype ω] (v : ω → κ → C) : κ → MvPowerSeries ω C :=
  fun x => subst (fun i : κ => ∑ w, v w i • (MvPowerSeries.X w : MvPowerSeries ω C)) (X.ex x)

theorem comb_cc {ι ω : Type} [Fintype ι] (c : ι → C) (φ : ι → ω) :
    constantCoeff (∑ w, c w • (MvPowerSeries.X (φ w) : MvPowerSeries ω C)) = 0 := by

  rw [map_sum]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [constantCoeff_smul, constantCoeff_X, smul_zero]

theorem expAt_cc (H : RLaw X V) {ω : Type} [Fintype ω] (v : ω → κ → C) (x : κ) :
    constantCoeff (expAt X v x) = 0 := by
  unfold expAt
  rw [cc_subst (fun i => comb_cc (fun w => v w i) (fun w => w)), H.exc]

theorem subst_endomorphismSeries_expAt (H : RLaw X V) {ω : Type} [Fintype ω] (v : ω → κ → C) (A : Matrix κ κ C) (i : κ) :
    subst (expAt X v) (endP X A (MvPowerSeries.X : κ → MvPowerSeries κ C) i) =
      expAt X (fun w => A.mulVec (v w)) i := by
  rw [subst_endP H (fun s => constantCoeff_X s) (expAt_cc H v)]
  simp only [subst_X (hasSubst_of_constantCoeff_zero (expAt_cc H v))]
  have hl : ∀ y, subst (expAt X v) (X.lg y) = ∑ w, v w y • (MvPowerSeries.X w : MvPowerSeries ω C) :=
    fun y => lg_ex H (fun i => comb_cc (fun w => v w i) (fun w => w)) y
  unfold endP
  simp only [hl]
  unfold expAt
  congr 1
  funext x
  simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

theorem subst_hEnd_expAt (H : RLaw X V) {ω : Type} [Fintype ω] (v : ω → κ → C) (A B : Matrix κ κ C) :
    subst (expAt X v) (hEnd X A B) =
      hAt X (expAt X (fun w => A.mulVec (v w))) (expAt X (fun w => B.mulVec (v w))) := by
  unfold hEnd
  rw [subst_hAt (constantCoeff_expMulLog H (fun s => constantCoeff_X s) A) (constantCoeff_expMulLog H (fun s => constantCoeff_X s) B) (expAt_cc H v)]
  simp only [subst_endomorphismSeries_expAt H]

theorem hEnd_cc (H : RLaw X V) (A B : Matrix κ κ C) : constantCoeff (hEnd X A B) = 0 :=
  hAt_cc H (constantCoeff_expMulLog H (fun s => constantCoeff_X s) A) (constantCoeff_expMulLog H (fun s => constantCoeff_X s) B)

end GlobalTheory.RowVal.PlaneRead

namespace GlobalTheory.RowVal

open PlaneRead EndCalc

theorem exists_intS_frame_eq_prod : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) (Orb : Type) [Fintype Orb] (I : Orb → Fin 2 → Type) [∀ o g, Fintype (I o g)] (κ : Type) [Fintype κ] [DecidableEq κ] (X : ∀ o, RawChart C d (I o) κ) (d₀ : ℕ) (I₀ : Fin 2 → Type) [∀ g, Fintype (I₀ g)] (X₀ : RawChart C d₀ I₀ κ), RLaw X₀ V → (∀ o, (X o).ex = X₀.ex ∧ (X o).h = X₀.h ∧ (X o).k = X₀.k) → ∀ (π : Orb → Fin 2 → Matrix κ κ C) (W : Matrix κ κ C), (∀ o g, IntEnd X₀ V (π o g)) → (∀ o g c, (π o g).mulVec ((X o).u g c) = (X o).u g c) → (∀ o g o' g' c, (o, g) ≠ (o', g') → (π o g).mulVec ((X o').u g' c) = 0) → (∑ o, hEnd X₀ (π o 0) (π o 1)) - hEnd X₀ (∑ o, ∑ g, π o g) (W * ∑ o, ∑ g, π o g) ∈ logInt V κ → ∀ gr : ∀ o, MvPowerSeries (WV (I o)) C, (∀ o, gr o ∈ ExpInt (X o) V) → ∃ F : MvPowerSeries κ C, IntS V F ∧ MvPowerSeries.subst (fun x : κ => MvPowerSeries.subst (fun i : κ => ∑ w : WVO I, (X w.1).u w.2.1 w.2.2 i • (MvPowerSeries.X w : MvPowerSeries (WVO I) C)) (X₀.ex x)) (F * mvExp ((X₀.k : C) • hEnd X₀ 1 W)) = ∏ o, MvPowerSeries.subst (fun w : WV (I o) => (MvPowerSeries.X (⟨o, w⟩ : WVO I) : MvPowerSeries (WVO I) C)) (gr o * mvExp (X o).hRow) := by
  intro C _ _ V d Orb _ I _ κ _ _ X d₀ I₀ _ X₀ H hX π W hπ hfix hkill hD gr hgr
  classical
  choose f hf hgf using hgr
  let u : WVO I → κ → C := fun w => (X w.1).u w.2.1 w.2.2
  set P : Matrix κ κ C := ∑ o, ∑ g, π o g with hP
  set D := (∑ o, hEnd X₀ (π o 0) (π o 1)) - hEnd X₀ P (W * P) with hDdef
  have cX : ∀ s : κ, MvPowerSeries.constantCoeff (MvPowerSeries.X s : MvPowerSeries κ C) = 0 :=
    fun s => MvPowerSeries.constantCoeff_X s
  have cπ : ∀ o (p : Fin 2 × κ), MvPowerSeries.constantCoeff
      (endP X₀ (π o p.1) (MvPowerSeries.X : κ → MvPowerSeries κ C) p.2) = 0 := fun o p => constantCoeff_expMulLog H cX _ _
  have hkD : (X₀.k : C) • D ∈ logInt V κ := by
    rw [Nat.cast_smul_eq_nsmul]
    exact AddSubgroup.nsmul_mem _ hD _
  let r : ∀ o, WV (I o) → MvPowerSeries (WVO I) C := fun o w => MvPowerSeries.X (⟨o, w⟩ : WVO I)
  have cr : ∀ o w, MvPowerSeries.constantCoeff (r o w) = 0 := fun o w => MvPowerSeries.constantCoeff_X _
  have hr := fun o => MvPowerSeries.hasSubst_of_constantCoeff_zero (cr o)
  have ce := expAt_cc H u
  have he := MvPowerSeries.hasSubst_of_constantCoeff_zero ce
  have cE : ∀ o (p : Fin 2 × κ), MvPowerSeries.constantCoeff ((X o).expPt p.1 p.2) = 0 := by
    intro o p
    unfold RawChart.expPt
    rw [cc_subst (fun i => comb_cc (fun c => (X o).u p.1 c i) (fun c => (⟨p.1, c⟩ : WV (I o)))), (hX o).1, H.exc]
  have hpt : ∀ o g x, expAt X₀ (fun w => (π o g).mulVec (u w)) x =
      MvPowerSeries.subst (r o) ((X o).expPt g x) := by
    intro o g x
    unfold RawChart.expPt expAt
    rw [comp_cc (fun i => comb_cc (fun c => (X o).u g c i) (fun c => (⟨g, c⟩ : WV (I o)))) (cr o), (hX o).1]
    congr 1
    funext i
    rw [subst_lin (cr o), Fintype.sum_sigma, Finset.sum_eq_single o, Fintype.sum_sigma, Finset.sum_eq_single g]
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [MvPowerSeries.subst_X (hr o)]
      show (π o g).mulVec ((X o).u g c) i • _ = _
      rw [hfix]
    · intro g' _ hg
      refine Finset.sum_eq_zero fun c _ => ?_
      show (π o g).mulVec ((X o).u g' c) i • _ = _
      rw [hkill o g o g' c (by simp [Ne.symm hg]), Pi.zero_apply, zero_smul]
    · simp
    · intro o' _ ho
      refine Finset.sum_eq_zero fun c _ => ?_
      show (π o g).mulVec ((X o').u c.1 c.2) i • _ = _
      rw [hkill o g o' c.1 c.2 (by simp [Ne.symm ho]), Pi.zero_apply, zero_smul]
    · simp
  have hPu : ∀ w, P.mulVec (u w) = u w := by
    rintro ⟨o, g, c⟩
    show P.mulVec ((X o).u g c) = (X o).u g c
    rw [hP, Matrix.sum_mulVec, Finset.sum_eq_single o, Matrix.sum_mulVec, Finset.sum_eq_single g, hfix]
    · intro g' _ hg
      exact hkill o g' o g c (by simp [hg])
    · simp
    · intro o' _ ho
      rw [Matrix.sum_mulVec]
      exact Finset.sum_eq_zero fun g' _ => hkill o' g' o g c (by simp [ho])
    · simp
  have h1 : MvPowerSeries.subst (expAt X₀ u) (hEnd X₀ P (W * P)) =
      MvPowerSeries.subst (expAt X₀ u) (hEnd X₀ 1 W) := by
    simp only [subst_hEnd_expAt H, ← Matrix.mulVec_mulVec, hPu, Matrix.one_mulVec]
  have h2 : ∀ o, (X₀.k : C) • MvPowerSeries.subst (expAt X₀ u) (hEnd X₀ (π o 0) (π o 1)) =
      MvPowerSeries.subst (r o) (X o).hRow := by
    intro o
    unfold RawChart.hRow
    rw [MvPowerSeries.subst_smul (hr o), comp_cc (cE o) (cr o), subst_hEnd_expAt H, (hX o).2.1, (hX o).2.2]
    unfold hAt
    congr 2
    funext p
    obtain ⟨g, x⟩ := p
    fin_cases g
    · simpa using hpt o 0 x
    · simpa using hpt o 1 x
  have cH : ∀ o, MvPowerSeries.constantCoeff (X o).hRow = 0 := by
    intro o
    unfold RawChart.hRow
    rw [MvPowerSeries.constantCoeff_smul, cc_subst (cE o), (hX o).2.1, h_cc H, smul_zero]
  have c1 : MvPowerSeries.constantCoeff ((X₀.k : C) • hEnd X₀ 1 W) = 0 := by
    rw [MvPowerSeries.constantCoeff_smul, hEnd_cc H, smul_zero]
  have h3 : MvPowerSeries.subst (expAt X₀ u) ((X₀.k : C) • D + (X₀.k : C) • hEnd X₀ 1 W) =
      ∑ o, MvPowerSeries.subst (r o) (X o).hRow := by

    rw [← smul_add, MvPowerSeries.subst_smul he, MvPowerSeries.subst_add he, ← h1, ← MvPowerSeries.subst_add he,
    hDdef, sub_add_cancel, ← MvPowerSeries.substAlgHom_apply he, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [MvPowerSeries.substAlgHom_apply, h2]
  refine ⟨(∏ o, MvPowerSeries.subst (fun p : Fin 2 × κ =>
    endP X₀ (π o p.1) (MvPowerSeries.X : κ → MvPowerSeries κ C) p.2) (f o)) * mvExp ((X₀.k : C) • D),
    intS_mul (intS_prod _ fun o => intS_subst (cπ o) (fun p => hπ o p.1 p.2) (hf o)) hkD.2, ?_⟩
  show MvPowerSeries.subst (expAt X₀ u) _ = ∏ o, MvPowerSeries.subst (r o) _
  rw [mul_assoc, ← mvExp_add hkD.1 c1, MvPowerSeries.subst_mul he,
    subst_mvExp ce (by rw [map_add (f := _), hkD.1, c1, add_zero]), h3,
    mvExp_sum _ (fun o => by rw [cc_subst (cr o), cH]), ← MvPowerSeries.substAlgHom_apply he, map_prod,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun o _ => ?_
  rw [MvPowerSeries.substAlgHom_apply, MvPowerSeries.subst_mul (hr o), subst_mvExp (cr o) (cH o), hgf o,
    comp_cc (cπ o) ce, comp_cc (cE o) (cr o)]
  simp only [subst_endomorphismSeries_expAt H, hpt]

end GlobalTheory.RowVal
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lattice_inequality_valuation_integers : ∀ (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → (∃ c : C, 0 < v c ∧ v c < 1) → ∀ (n s h : ℕ) (a : Fin n → O), Function.Injective a → ∀ (M : Submodule O (Fin n × Fin s → O)), M.FG → (∀ f ∈ M, (fun y : Fin n × Fin s => a y.1 * f y) ∈ M) → (∀ (τ : Fin n) (z : Fin s → O), ∃ f ∈ M, ∀ i, f (τ, i) = z i) → ∀ (φ : Fin h → Fin n × Fin s → O), (∀ l, φ l ∈ M) → ∀ c : NNReal, c ≠ 0 → HasLen v O (M ⧸ (Submodule.span O (Set.range fun q : Fin n × Fin h => fun y : Fin n × Fin s => a y.1 ^ (q.1 : ℕ) * φ q.2 y)).comap M.subtype) c → ∃ x : Fin n → NNReal, (∀ τ, HasLen v O ((Fin s → O) ⧸ Submodule.span O (Set.range fun l => fun i => φ l (τ, i))) (x τ)) ∧ c ^ 2 * v (discr fun τ => algebraMap O C (a τ)) ^ h ≤ (∏ τ, x τ) ^ 2 * v (discr fun τ => algebraMap O C (a τ)) ^ s := by
  first | exact @GlobalTheory.ChF.lattice_ineq_integers | exact GlobalTheory.ChF.lattice_ineq_integers | (intros; apply GlobalTheory.ChF.lattice_ineq_integers <;> assumption)
end
