module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle097
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle031
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle046
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle122
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfMulVec
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitEntries
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentLeviRadicalCoordsHomeomorph
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle151
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle148
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralEquivariantLeftInvariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.StabUnfold

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

structure Sib (I : AutInst) where
  n : ℕ
  J : Matrix (Fin n) (Fin n) I.E
  J_herm : Formalism.UG.IsHerm (starRingEnd I.E) J
  J_det : J.det ≠ 0
  L : Submodule (𝓞 I.E) (Fin n → I.E)
  L_span : Submodule.span I.E (L : Set (Fin n → I.E)) = ⊤
  L_fg : L.FG
  L_dual : ∀ x : Fin n → I.E, x ∈ L ↔
    ∀ y ∈ L, Formalism.UG.hform (starRingEnd I.E) J y x ∈ (algebraMap (𝓞 I.E) I.E).range
  ε : InfinitePlace I.F → Fin n → Bool
  P : InfinitePlace I.F → Matrix (Fin n) (Fin n) ℂ
  P_unit : ∀ v, IsUnit (P v)
  P_spec : ∀ v, (P v)ᴴ * J.map (I.φ v) * P v = Formalism.REAL.Jm (ε v)

variable {I : AutInst}

def Sib.frames (D : Sib I) : AutInst :=
  GlobalTheory.AutInhab.ofFrames I.cm D.n D.J D.J_herm D.J_det D.L D.L_span D.L_fg D.L_dual D.ε I.φ I.φ_over D.P
    D.P_unit D.P_spec

@[reducible] def Sib.inst (D : Sib I) : AutInst where
  F := I.F
  E := I.E
  cm := I.cm
  n := D.n
  J := D.J
  J_herm := D.J_herm
  J_det := D.J_det
  L := D.L
  L_span := D.L_span
  L_fg := D.L_fg
  L_dual := D.L_dual
  ε := D.ε
  φ := I.φ
  φ_over := I.φ_over
  P := D.P
  P_unit := D.P_unit
  P_spec := D.P_spec
  topf := D.frames.topf
  topf_group := D.frames.topf_group
  topf_open := D.frames.topf_open
  topf_basis := D.frames.topf_basis

instance (D : Sib I) : TopologicalSpace D.inst.Gf := D.inst.topf
instance (D : Sib I) : IsTopologicalGroup D.inst.Gf := D.inst.topf_group
instance (D : Sib I) : MeasurableSpace D.inst.Gf := AutInst.instMeasurableSpaceGf D.inst
instance (D : Sib I) : BorelSpace D.inst.Gf := AutInst.instBorelSpaceGf D.inst

def IsPerp (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf) : Prop :=
  D.n + 1 = I.n ∧ star x ⬝ᵥ (I.J *ᵥ x) = sgn I.E s ∧ star x ᵥ* (I.J * A) = 0 ∧ Aᴴ * I.J * A = D.J ∧
    x ∈ lamX I (1, xf) ∧ ∀ y : Fin D.n → I.E, y ∈ D.L ↔ A *ᵥ y ∈ lamX I (1, xf)

def afVec (I : AutInst) {m : ℕ} (x : Fin m → I.E) : Fin m → I.E ⊗[I.F] Af I.F :=
  fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)

def afMat (I : AutInst) {m k : ℕ} (A : Matrix (Fin m) (Fin k) I.E) : Matrix (Fin m) (Fin k) (I.E ⊗[I.F] Af I.F) :=
  A.map (Formalism.UG.inclE (F := I.F) (Af I.F))

def infVec (I : AutInst) (v : InfinitePlace I.F) (x : Fin I.n → I.E) : Fin I.n → ℂ :=
  (I.P v)⁻¹ *ᵥ fun i => I.φ v (x i)

def infMat (D : Sib I) (v : InfinitePlace I.F) (A : Matrix (Fin I.n) (Fin D.n) I.E) :
    Matrix (Fin I.n) (Fin D.n) ℂ :=
  (I.P v)⁻¹ * A.map (I.φ v) * D.P v

def IsFinEmb (D : Sib I) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (jf : D.inst.Gf →* I.Gf) :
    Prop :=
  ∀ g, I.fmat (jf g) *ᵥ afVec I x = afVec I x ∧ I.fmat (jf g) * afMat I A = afMat I A * D.inst.fmat g

def IsInfEmb (D : Sib I) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E)
    (jv : ∀ v, Formalism.REAL.UJ (D.ε v) →* Formalism.REAL.UJ (I.ε v)) : Prop :=
  ∀ v g, uMat (jv v g) *ᵥ infVec I v x = infVec I v x ∧ uMat (jv v g) * infMat D v A = infMat D v A * uMat g

def embA (D : Sib I) (jv : ∀ v, Formalism.REAL.UJ (D.ε v) →* Formalism.REAL.UJ (I.ε v)) (jf : D.inst.Gf →* I.Gf) :
    D.inst.GA →* I.GA where
  toFun g := (fun v => jv v (g.1 v), jf g.2)
  map_one' := by
    refine Prod.ext (funext fun v => ?_) ?_
    · exact map_one (jv v)
    · exact map_one jf
  map_mul' g h := by
    refine Prod.ext (funext fun v => ?_) ?_
    · exact map_mul (jv v) _ _
    · exact map_mul jf _ _

def gaussAt (I : AutInst) (x : Fin I.n → I.E) (g : I.GA) : ENNReal :=
  (∏ v, ENNReal.ofReal (gauss ((uMat (g.1 v))⁻¹ *ᵥ infVec I v x))) *
    {h : I.Gf | x ∈ lamX I (1, h)}.indicator 1 g.2

def stabF (I : AutInst) (x : Fin I.n → I.E) : Set I.GA :=
  {γ | γ ∈ I.GFset ∧ I.fmat γ.2 *ᵥ afVec I x = afVec I x}

def Ksub (I : AutInst) : Subgroup I.Gf :=
  (Formalism.UG.stabGL I.Lf).comap (Formalism.UG.UPts I.cm.sig I.J (Af I.F)).subtype

end GlobalTheory.StabUnfold
end
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.PSplit

theorem mp_merge {ι α : Type} [Fintype ι] [MeasureSpace α] [SigmaFinite (volume : Measure α)]
    (p q : ι → Prop) [DecidablePred p] [Fintype {i // p i}] [Fintype {i // q i}]
    (hq : ∀ i, q i ↔ ¬ p i) :
    MeasurePreserving (fun x : ({i // p i} → α) × ({i // q i} → α) =>
      fun i => if h : p i then x.1 ⟨i, h⟩ else x.2 ⟨i, (hq i).2 h⟩) volume volume := by
  obtain rfl : q = fun i => ¬ p i := funext fun i => propext (hq i)
  have := (volume_preserving_piEquivPiSubtypeProd (fun _ : ι => α) p).symm
  convert this using 1
  all_goals first | rfl | (congr <;> exact Subsingleton.elim _ _)

theorem mp_comm {A B C D : Type} [MeasureSpace A] [MeasureSpace B] [MeasureSpace C]
    [MeasureSpace D] [SFinite (volume : Measure A)] [SFinite (volume : Measure B)]
    [SFinite (volume : Measure C)] [SFinite (volume : Measure D)] :
    MeasurePreserving (fun x : (A × B) × (C × D) => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
      volume volume := by
  have h1 := measurePreserving_prodAssoc (volume : Measure A) (volume : Measure B)
    (volume : Measure (C × D))
  have h2 := (MeasurePreserving.id (volume : Measure A)).prod
    (measurePreserving_prodAssoc (volume : Measure B) (volume : Measure C)
      (volume : Measure D)).symm
  have h3 := (MeasurePreserving.id (volume : Measure A)).prod
    ((Measure.measurePreserving_swap (μ := (volume : Measure B)) (ν := (volume : Measure C))).prod
      (MeasurePreserving.id (volume : Measure D)))
  have h4 := (MeasurePreserving.id (volume : Measure A)).prod
    (measurePreserving_prodAssoc (volume : Measure C) (volume : Measure B)
      (volume : Measure D))
  have h5 := (measurePreserving_prodAssoc (volume : Measure A) (volume : Measure C)
    (volume : Measure (B × D))).symm
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

theorem lintegral_shift {A C T : Type} [MeasureSpace A] [MeasureSpace C] [MeasureSpace T]
    [SFinite (volume : Measure A)] [SFinite (volume : Measure C)] [SFinite (volume : Measure T)]
    [AddGroup C] [MeasurableAdd₂ C] [Measure.IsAddRightInvariant (volume : Measure C)]
    (F : (A × C) × T → ℝ≥0∞) (hF : Measurable F) (c : A × T → C) (hc : Measurable c) :
    ∫⁻ x, F x = ∫⁻ y : A × C, ∫⁻ t : T, F ((y.1, y.2 + c (y.1, t)), t) := by
  have hG : Measurable (fun x : (A × C) × T => F ((x.1.1, x.1.2 + c (x.1.1, x.2)), x.2)) := by
    apply hF.comp
    fun_prop
  rw [lintegral_lintegral_swap (f := fun (y : A × C) (t : T) => F ((y.1, y.2 + c (y.1, t)), t))
    hG.aemeasurable, Measure.volume_eq_prod, lintegral_prod_symm _ hF.aemeasurable]
  refine lintegral_congr fun t => ?_
  rw [Measure.volume_eq_prod, lintegral_prod _ (Measurable.aemeasurable (by fun_prop)),
    lintegral_prod (fun y : A × C => F ((y.1, y.2 + c (y.1, t)), t))
      (Measurable.aemeasurable (hG.comp (f := fun y : A × C => (y, t)) (by fun_prop)))]
  refine lintegral_congr fun a => ?_
  exact (lintegral_add_right_eq_self (fun s => F ((a, s), t)) (c (a, t))).symm

theorem sf_pair (ι κ : Type) [Fintype ι] [Fintype κ] :
    SFinite (volume : Measure ((ι → ℂ) × (κ → ℝ))) := inferInstance

theorem sf_rows (ι κ : Type) [Fintype ι] [Fintype κ] :
    SFinite (volume : Measure (ι → κ → ℂ)) := inferInstance

theorem sf_triple (ι ι' κ κ' : Type) [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ'] :
    SFinite (volume : Measure ((ι → ι' → ℂ) × (κ → ℂ) × (κ' → ℝ))) := by
  have := sf_pair κ κ'
  have := sf_rows ι ι'
  exact Measure.prod.instSFinite

theorem inv_pair (ι κ : Type) [Fintype ι] [Fintype κ] :
    Measure.IsAddRightInvariant (volume : Measure ((ι → ℂ) × (κ → ℝ))) :=
  Measure.prod.instIsAddRightInvariant

def merge (k r j : ℕ) (x : PSec k r j × PTop k r j) : PPar k r :=
  (fun a => if h : (a : ℕ) < j then x.1.1 ⟨a, h⟩ else x.2.1 ⟨a, not_lt.1 h⟩,
   fun p => if h : (p.1.1 : ℕ) < j then x.1.2.1 ⟨p, h⟩ else x.2.2.1 ⟨p, not_lt.1 h⟩,
   fun a => if h : (a : ℕ) < j then x.1.2.2 ⟨a, h⟩ else x.2.2.2 ⟨a, not_lt.1 h⟩)

theorem mp_mergeP (k r j : ℕ) : MeasurePreserving (merge k r j) volume volume := by
  have h1 := mp_merge (α := Fin (k + 1) → ℂ) (fun a : Fin r => (a : ℕ) < j)
    (fun a : Fin r => j ≤ (a : ℕ)) (fun _ => not_lt.symm)
  have h2 := mp_merge (α := ℂ) (fun p : UT r => (p.1.1 : ℕ) < j)
    (fun p : UT r => j ≤ (p.1.1 : ℕ)) (fun _ => not_lt.symm)
  have h3 := mp_merge (α := ℝ) (fun a : Fin r => (a : ℕ) < j)
    (fun a : Fin r => j ≤ (a : ℕ)) (fun _ => not_lt.symm)
  have := sf_pair {p : UT r // (p.1.1 : ℕ) < j} {a : Fin r // (a : ℕ) < j}
  have := sf_pair {p : UT r // j ≤ (p.1.1 : ℕ)} {a : Fin r // j ≤ (a : ℕ)}
  have := sf_pair (UT r) (Fin r)
  have h4 := (h2.prod h3).comp mp_comm
  have h5 := @MeasurePreserving.prod _ _ _ _ _ _ _ _ _ _ _ _ Measure.prod.instSFinite
    Measure.prod.instSFinite _ _ h1 h4
  exact h5.comp mp_comm

theorem cont_pOf (k r : ℕ) : Continuous (fun q : PPar k r => (fun a b => pOf k r q a b : Mt k r)) := by
  refine continuous_pi fun i => continuous_pi fun i' => ?_
  simp only [pOf, pEl, skewM, Rad.herm_Hb]
  split_ifs <;> fun_prop

noncomputable def shift (k r j : ℕ)
    (x : ({a : Fin r // (a : ℕ) < j} → Fin (k + 1) → ℂ) × PTop k r j) :
    ({p : UT r // (p.1.1 : ℕ) < j} → ℂ) × ({a : Fin r // (a : ℕ) < j} → ℝ) :=
  (fun p => if h : j ≤ (p.1.1.2 : ℕ) then
      herm (Hb k) (x.2.1 ⟨p.1.1.2, h⟩) (x.1 ⟨p.1.1.1, p.2⟩) / 2 else 0, 0)

theorem meas_shift (k r j : ℕ) : Measurable (shift k r j) := by
  refine Measurable.prodMk (Measurable.of_eval fun p => ?_) measurable_const
  simp only [Rad.herm_Hb]
  split_ifs <;> fun_prop

theorem herm_zero_left {k : ℕ} (w : Fin (k + 1) → ℂ) : herm (Hb k) 0 w = 0 := by
  simp [Rad.herm_Hb]

theorem herm_zero_right {k : ℕ} (w : Fin (k + 1) → ℂ) : herm (Hb k) w 0 = 0 := by
  simp [Rad.herm_Hb]

theorem mul_eq (k r j : ℕ) (q' : PSec k r j) (q : PTop k r j) :
    pTop k r j q * pSec k r j q' =
      pOf k r (merge k r j ((q'.1, q'.2 + shift k r j (q'.1, q)), q)) := by
  simp only [pTop, pSec, pOf, Rad.pEl_mul, merge]
  congr 1
  · funext a
    by_cases h : (a : ℕ) < j
    · simp [h, not_le.2 h]
    · simp [h, not_lt.1 h]
  · ext a b
    simp only [Matrix.add_apply, Matrix.of_apply, skewM, shift]
    by_cases ha : (a : ℕ) < j <;> by_cases hb : (b : ℕ) < j
    · have ha' := not_le.2 ha
      have hb' := not_le.2 hb
      simp [ha, hb, ha', hb', herm_zero_left, herm_zero_right]
    · have ha' := not_le.2 ha
      have hb' := not_lt.1 hb
      have hab : a < b := by rw [Fin.lt_def]; omega
      simp [ha, hb, ha', hb', hab, herm_zero_left]
    · have ha' := not_lt.1 ha
      have hb' := not_le.2 hb
      have hab : b < a := by rw [Fin.lt_def]; omega
      simp [ha, hb, ha', hb', hab, hab.not_gt, herm_zero_left]
      rw [← Rad.herm_star]
      simp only [Complex.star_def]
      ring
    · have ha' := not_lt.1 ha
      have hb' := not_lt.1 hb
      simp [ha, hb, ha', hb', herm_zero_left, herm_zero_right]

theorem lintegral_split (k r j : ℕ) (f : Mat k r → ℝ≥0∞)
    (hf : Measurable (fun x : Mt k r => f (Matrix.of x))) :
    ∫⁻ q : PPar k r, f (pOf k r q) =
      ∫⁻ q' : PSec k r j, ∫⁻ q : PTop k r j, f (pTop k r j q * pSec k r j q') := by
  have hg : Measurable (fun q : PPar k r => f (pOf k r q)) :=
    hf.comp (f := fun q : PPar k r => (fun a b => pOf k r q a b : Mt k r))
      (cont_pOf k r).measurable
  have := sf_pair {p : UT r // (p.1.1 : ℕ) < j} {a : Fin r // (a : ℕ) < j}
  have := sf_triple {a : Fin r // j ≤ (a : ℕ)} (Fin (k + 1)) {p : UT r // j ≤ (p.1.1 : ℕ)}
    {a : Fin r // j ≤ (a : ℕ)}
  have := inv_pair {p : UT r // (p.1.1 : ℕ) < j} {a : Fin r // (a : ℕ) < j}
  rw [← (mp_mergeP k r j).lintegral_comp hg,
    lintegral_shift (fun x => f (pOf k r (merge k r j x))) (hg.comp (mp_mergeP k r j).measurable) _ (meas_shift k r j)]
  simp only [mul_eq]

end GlobalTheory.Amp.PSplit
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.GoodPlace

theorem equality : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → S.gg = false → vE L S.ϖ S.G = 0 → (∀ l, S.D l ≠ 0 → vE L S.ϖ (S.D l * L.cj (S.D l)) = 0) → (∀ d Λ, S.IsTerm d Λ → S.BBzero d Λ) ∧ S.Hp = 1 ∧ (S.ampSq fun _ _ => True) = S.nn ∧ ∀ d, (S.mass d fun _ => True) = 0 ∨ (S.mass d fun _ => True) = 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S _ hgg hG hD
  have hvth : S.vth = 0 := by simp [Frames.vth, hgg]
  have ha : S.a = 0 := by simp [Frames.a, hvth, hG]
  have hvD : S.vD = 0 := Finset.sum_eq_zero fun l _ => by
    split_ifs with h
    · exact hD l h.2
    · rfl
  have huniq := fun d Λ h => GlobalTheory.HL.UnimodTerm.term_unique L r k S d Λ h ha
  have key : ∀ d, ((S.mass d fun _ => True) = 0 ∨ (S.mass d fun _ => True) = 1) ∧
      ENNReal.ofReal (‖S.amp d fun _ => True‖ ^ 2) = S.mass d fun _ => True := by
    intro d
    by_cases hex : ∃ Λ, S.IsTerm d Λ
    swap
    · have h0 : ∀ Λ, ¬ S.IsTerm d Λ := fun Λ h => hex ⟨Λ, h⟩
      simp [Frames.mass, Frames.amp, h0]
    obtain ⟨Λ₀, h₀⟩ := hex
    obtain ⟨-, -, hDO, -⟩ := GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ₀ h₀
    obtain ⟨-, -, -, -, hDu, -⟩ := GlobalTheory.FrameBasic.main L r k S
    obtain ⟨-, -, -, hvu⟩ := GlobalTheory.UnramVal.vE_valuation L S.ϖ S.ϖ_irr
    have hunit : ∀ l, S.D l ≠ 0 → S.D l ∈ L.O ∧ ∃ y ∈ L.O, S.D l * y = 1 := by
      intro l hl
      refine ⟨hDO l, ?_⟩
      obtain ⟨e, he⟩ := GlobalTheory.UnramOrder.exists_norm L (hDO l)
      have he0 : (e : F) ≠ 0 := fun h0 => by
        rw [h0, map_zero] at he
        apply hl
        rw [← L.cj_cj (S.D l), (hDu l hl).mul_right_eq_zero.1 he, map_zero]
      obtain ⟨u, hu⟩ := hvu _ he0
      rw [← he, hD l hl, zpow_zero, one_mul] at hu
      refine ⟨L.cj (S.D l) * algebraMap F E (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F),
        L.O.mul_mem (GlobalTheory.UnramOrder.cj_mem L (hDO l))
          ((GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (Subtype.property _)), ?_⟩
      rw [← mul_assoc, he, ← map_mul, hu, ← Subring.coe_mul, Units.mul_inv]
      simp
    obtain ⟨hC0, hw0, hall⟩ := GlobalTheory.HL.GoodClass.one_class L r k S hgg hunit
    set C0 := S.frameCls S.f S.f' with hC0def
    have hact := GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d
    have hint : ∀ Λ, S.IsTerm d Λ → S.IsIntCls (S.Fr d Λ) := fun Λ h =>
      (TermBasic.term_basic L r k S d Λ h).2.2.2.2.2.2.1

    have hm : (S.mass d fun _ => True) = 0 ∨ (S.mass d fun _ => True) = 1 := by
      rw [mass_eq_sumCls L r k S d _ (fun _ _ _ _ _ => trivial)]
      unfold Frames.sumCls
      let o₀ : MulAction.orbitRel.Quotient S.St (Set S.FrP) := Quotient.mk _ C0
      rw [tsum_eq_single o₀ (fun o ho => if_neg fun hI => ho (by
        obtain ⟨h, hh, e⟩ := hall _ hI
        rw [← Quotient.out_eq o]
        exact Quotient.sound ⟨⟨h, hh⟩, e.symm⟩))]
      split_ifs with hI
      swap
      · exact Or.inl rfl
      obtain ⟨h, hh, e⟩ := hall _ hI
      have hw : S.wC o₀.out = 1 := by
        rw [e, ((volSt L r k S).2 C0 hC0.1).2.2.2 h hh, hw0]
      rw [hw, ENNReal.ofReal_one, one_mul]
      have hs : ({Λ | S.IsTerm d Λ ∧ True ∧ S.Fr d Λ = o₀.out} : Set (Submodule L.O S.V)).Subsingleton :=
        fun Λ hΛ Λ' hΛ' => (huniq d Λ' hΛ'.1).2 Λ hΛ.1 (hΛ.2.2.trans hΛ'.2.2.symm)
      unfold Frames.nT
      beta_reduce
      rcases hs.eq_empty_or_singleton with h1 | ⟨x, h1⟩
      · left; rw [h1]; simp
      · right; rw [h1]; simp
    refine ⟨hm, ?_⟩

    let o₁ : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V) := Quotient.mk _ Λ₀
    have hone : ∀ o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V), o ≠ o₁ →
        ¬ (S.IsTerm d o.out ∧ True) := by
      intro o ho hT
      apply ho
      obtain ⟨h, hh, e⟩ := hall _ (hint _ hT.1)
      obtain ⟨h', hh', e'⟩ := hall _ (hint _ h₀)
      have hmem : h * h'⁻¹ ∈ S.St := S.St.mul_mem hh (S.St.inv_mem hh')
      have hA := hact Λ₀ h₀ _ hmem
      have e2 : (h * h'⁻¹) • Λ₀ = o.out := (huniq d _ hT.1).2 _ hA.1 (by
        rw [hA.2.2.2.2.1, e', e, smul_smul, inv_mul_cancel_right])
      rw [← Quotient.out_eq o]
      exact Quotient.sound ⟨⟨_, hmem⟩, e2⟩
    have e1 : (S.mass d fun _ => True) =
        if S.IsTerm d o₁.out ∧ True then ENNReal.ofReal (S.mu o₁.out) else 0 := by
      unfold Frames.mass
      rw [tsum_eq_single o₁]
      · congr
      · exact fun o ho => if_neg (hone o ho)
    have e2 : (S.amp d fun _ => True) =
        if S.IsTerm d o₁.out ∧ True then (S.mu o₁.out : ℂ) * S.om d o₁.out else 0 := by
      unfold Frames.amp
      rw [tsum_eq_single o₁]
      · congr
      · exact fun o ho => if_neg (hone o ho)
    rw [e1] at hm ⊢
    rw [e2]
    by_cases hT : S.IsTerm d o₁.out ∧ True
    swap
    · simp only [if_neg hT]; simp
    simp only [if_pos hT] at hm ⊢
    have hom : ‖S.om d o₁.out‖ = 1 := by
      obtain ⟨p, hp⟩ := hT.1
      exact (WitIndep.witness_independence L r k S d _ _ _ hp).2.2.2.2
    have hmu : 0 ≤ S.mu o₁.out := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    rw [norm_mul, hom, mul_one, Complex.norm_real, Real.norm_of_nonneg hmu]
    rcases hm with h | h
    · rw [le_antisymm (ENNReal.ofReal_eq_zero.1 h) hmu]; simp
    · rw [ENNReal.ofReal_eq_one.1 h]; simp
  refine ⟨fun d Λ h => (huniq d Λ h).1, by simp [Frames.Hp, hvth, ha, hvD], ?_, fun d => (key d).1⟩
  unfold Frames.ampSq Frames.nn
  congr 1
  funext d
  exact (key d).2

end GlobalTheory.HL.GoodPlace
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.unipotent_levi_radical_coords_homeomorph : ∀ k r : ℕ, Set.BijOn (fun q : (UT r → ℂ) × PPar k r => uEmb k r (upper q.1) * pOf k r q.2) Set.univ (Nset k r) ∧ Continuous (fun q : (UT r → ℂ) × PPar k r => uEmb k r (upper q.1) * pOf k r q.2) ∧ ∃ c : Mat k r → (UT r → ℂ) × PPar k r, Continuous c ∧ ∀ q : (UT r → ℂ) × PPar k r, c (uEmb k r (upper q.1) * pOf k r q.2) = q := by
  first | exact @GlobalTheory.Amp.NCoord.coord_homeo | exact GlobalTheory.Amp.NCoord.coord_homeo | (intros; apply GlobalTheory.Amp.NCoord.coord_homeo <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.completedTensorDiscreteSeries_irreducible_formalDegree : TensorRep := by
  first | exact @GlobalTheory.Dec.tensorRep | exact GlobalTheory.Dec.tensorRep | (intros; apply GlobalTheory.Dec.tensorRep <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.weil_integral_vanishing_of_fibre_integrals : WeilVanish := by
  first | exact @GlobalTheory.Dec.weilVanish | exact GlobalTheory.Dec.weilVanish | (intros; apply GlobalTheory.Dec.weilVanish <;> assumption)
end

section

namespace GlobalTheory.IwaInt

theorem iwasawaInt : GlobalTheory.Dec.IwasawaInt := iwasawaInt_of GlobalTheory.T.iwasawa_decomp_complexifiedMaxCompact

end GlobalTheory.IwaInt
end
