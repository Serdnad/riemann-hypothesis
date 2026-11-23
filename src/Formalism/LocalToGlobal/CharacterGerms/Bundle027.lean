module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle023
public import Formalism.LocalToGlobal.CharacterGerms.Bundle016
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Formalism.LocalToGlobal.CharacterGerms.RowTieJet
public import Formalism.LocalToGlobal.CharacterGerms.Bundle011
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Formal

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

def FBChart.chartLinearTerm (Y : FBChart C V O dd) (u : Fin dd → C) : PS C 2 dd :=
  fun μ => ∑ i, u i * MvPowerSeries.coeff
    (μ.mapDomain (fun p : Fin 2 × Fin dd => (p.1.succ, p.2)) + Finsupp.single ((0 : Fin 3), i) 1) Y.B.ph2

def cvAt (s : MvPowerSeries (Fin 2) C) (γ : PowerSeries C) : MvPowerSeries (Fin 2) C :=
  MvPowerSeries.subst (fun _ : Unit => s) γ

def NDG (Y : FBChart C V O dd) : Prop :=
  ∀ γ : Fin dd → PowerSeries C, IsCv V γ → (∃ i, ¬ V.MM (PowerSeries.coeff 1 (γ i))) →
    (∀ i (μ : Fin 2 →₀ ℕ), μ 0 < V.l → μ 1 < V.l → V.MM (MvPowerSeries.coeff μ
      (MvPowerSeries.subst (fun p : Fin 2 × Fin dd => cvAt (MvPowerSeries.X p.1) (γ p.2)) (Y.B.G.F i) -
        cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (γ i)))) →
    ¬ ∃ b : PS C 1 dd, IntS V b ∧ ∀ μ, V.MM (MvPowerSeries.coeff μ
      (Y.chartLinearTerm (fun i => PowerSeries.coeff 1 (γ i)) -
        (ev (n := 2) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1)] b - ev (n := 2) ![pt C dd 0] b -
          ev (n := 2) ![pt C dd 1] b)))

end Formal

def RankMaximalOfNondegenerate : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I),
    NDG Y → (Y.raw p).RankHyp → ∀ Hc : ∀ g, (Y.raw p).CartHyp V g, RawChart.RankMaximalCondition Hc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

def NondegenerateCharts : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → NDG Y

end Formalism.L2.FormalSeriesBounds
end
end

section

set_option autoImplicit false

noncomputable section

open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open ValuationFitting

structure RingPk {C : Type} [Field C] (V : VF C) where
  vm : Valuation C NNReal
  tie : ValTie V vm
  int : vm.Integers V.RR
  pos : 0 < (vm (V.l : C) : ℝ)
  lt : (vm (V.l : C) : ℝ) < 1
  nonunit : ¬ IsUnit ((V.l : ℕ) : V.RR)
  cpl : IsAdicComplete (Ideal.span {((V.l : ℕ) : V.RR)}) V.RR
  loc : IsLocalRing V.RR
  alg : Algebra ℤ_[V.l] V.RR
  mm : ∀ x : V.RR, V.MM (x : C) → x ∈ IsLocalRing.maximalIdeal V.RR

def RingPkSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C),
    (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) → Nonempty (RingPk V)

end UpFBr

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

section Pull

variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))

theorem cc_X {σ : Type} (s : σ) : MvPowerSeries.constantCoeff (MvPowerSeries.X s : MvPowerSeries σ C) = 0 := MvPowerSeries.constantCoeff_X s

end Pull

section Emb

variable {n : ℕ}

def eRow (b : Fin n) : WVO I ↪ Fin n × WVO I := ⟨fun w => (b, w), Prod.mk_right_injective b⟩

def eAll (n : ℕ) (o : Orb) : Fin n × WV (I o) ↪ Fin n × WVO I :=
  ⟨fun x => (x.1, (⟨o, x.2⟩ : WVO I)), fun x y h => by
    have h1 : x.1 = y.1 := (Prod.ext_iff.1 h).1
    have h2 : (⟨o, x.2⟩ : WVO I) = ⟨o, y.2⟩ := (Prod.ext_iff.1 h).2
    exact Prod.ext h1 (eq_of_heq (Sigma.mk.inj h2).2)⟩

theorem rowOf_eq (b : Fin n) (F : MvPowerSeries (WVO I) C) : rowOf b F = MvPowerSeries.rename (eRow b) F := by
  unfold rowOf
  rw [MvPowerSeries.rename_eq_subst]
  rfl

theorem rowOf_toAllS (b : Fin n) (o : Orb) (F : MvPowerSeries (WV (I o)) C) :
    rowOf b (toAllS o F) = MvPowerSeries.rename (eAll n o) (rowCopy b F) := by
  have e1 : toAllS o F =
      MvPowerSeries.rename (Function.Embedding.sigmaMk (β := fun o => WV (I o)) o) F := by
    unfold toAllS
    rw [MvPowerSeries.rename_eq_subst]
    rfl
  rw [rowOf_eq, e1, rtj_rowCopy_eq, MvPowerSeries.rename_rename, MvPowerSeries.rename_rename]
  exact rtj_rename_congr (by funext w; rfl) F

theorem rowOf_mul (b : Fin n) (F G : MvPowerSeries (WVO I) C) : rowOf b (F * G) = rowOf b F * rowOf b G := by
  unfold rowOf
  exact VP.subst_mul (fun _ => MvPowerSeries.constantCoeff_X _) F G

theorem rowOf_prod (b : Fin n) {ι : Type} (s : Finset ι) (F : ι → MvPowerSeries (WVO I) C) :
    rowOf b (∏ i ∈ s, F i) = ∏ i ∈ s, rowOf b (F i) := by
  unfold rowOf
  exact VP.subst_prod (fun _ => MvPowerSeries.constantCoeff_X _) s F

theorem toAllS_mul (o : Orb) (F G : MvPowerSeries (WV (I o)) C) : toAllS o (F * G) = toAllS o F * toAllS o G := by
  unfold toAllS
  exact VP.subst_mul (fun _ => MvPowerSeries.constantCoeff_X _) F G

theorem jet_orb (Po : ∀ o, MvPolynomial (Fin n × WV (I o)) C) (Φ : ∀ o, MvPowerSeries (Fin n × WV (I o)) C) :
    jetAt0 (∏ o, toAll o (Po o)) (∏ o, MvPowerSeries.rename (eAll n o) (Φ o)) = ∏ o, jetAt0 (Po o) (Φ o) := by
  have hA : ∀ o ∈ (Finset.univ : Finset Orb), ∀ o' ∈ (Finset.univ : Finset Orb), o ≠ o' →
      Disjoint (Set.range (eAll (I := I) n o)) (Set.range (eAll (I := I) n o')) := by
    intro o _ o' _ h
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    exact h (congrArg (fun z : Fin n × WVO I => z.2.1) hy).symm
  have hT : ∀ o, toAll o (Po o) = MvPolynomial.rename (eAll n o) (Po o) := fun o => rfl
  exact (rtj_jet_prod (fun o => Set.range (eAll (I := I) n o)) Finset.univ hA
    (fun o => toAll o (Po o)) (fun o => MvPowerSeries.rename (eAll n o) (Φ o))
    (fun o _ => by rw [hT]; exact rtj_rename_supported _ _)
    (fun o _ => rtj_serIn_rename _ _)).trans
    (Finset.prod_congr rfl fun o _ => by rw [hT]; exact rtj_jet_rename _ _ _)

end Emb

end VP

end Formalism.L2.FormalSeriesBounds
end
end
