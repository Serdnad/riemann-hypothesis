module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle141
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle148
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepVec

theorem phiQ_eq_viaRed_qLoc : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E)
    (r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP), IsRedMap φ PP r →
    ∀ (a b k : ℕ) (mu : (Fv D.host.F v)ˣ →* ℂˣ) (ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), LiftsChar φ PP mu ξ⁻¹ →
    ∀ Y : Matrix (Fin b) (Fin a) (Fv D.host.F v), phiQ v k mu Y = viaRed r (qLoc k PP ξ) Y := by
  intro D v φ PP r hr a b k mu ξ hmu Y
  classical
  unfold phiQ viaRed
  by_cases hint : ∀ i j, Y i j ∈ v.adicCompletionIntegers D.host.F
  swap
  · rw [dite_eq_right hint, dite_eq_right (fun h => hint h.2.2.1)]
  rw [dite_eq_left hint]

  set Yo : Matrix (Fin b) (Fin a) (v.adicCompletionIntegers D.host.F) := fun i j => ⟨Y i j, hint i j⟩ with hYo
  have hy : (Matrix.of fun i j => r ⟨Y i j, hint i j⟩) = Yo.map r := rfl
  have htopY : topL k Y = (topL k Yo).map (v.adicCompletionIntegers D.host.F).subtype := by
    ext i j
    simp only [topL, Matrix.map_apply]
    split_ifs <;> simp [Yo]
  have htopy : topL k (Yo.map r) = (topL k Yo).map r := by
    ext i j
    simp only [topL, Matrix.map_apply]
    split_ifs <;> simp
  set d := (topL k Yo).det with hd
  have hdetY : (topL k Y).det = (d : Fv D.host.F v) := by
    rw [htopY]; exact (RingHom.map_det (v.adicCompletionIntegers D.host.F).subtype _).symm
  have hdety : (topL k (Yo.map r)).det = r d := by
    rw [htopy]; exact (RingHom.map_det r _).symm
  have hle : Valued.v (d : Fv D.host.F v) ≤ 1 := d.2
  have hunit : IsUnit (r d) ↔ Valued.v (d : Fv D.host.F v) = 1 := by
    constructor
    · intro hu
      refine le_antisymm hle (not_lt.mp fun hlt => ?_)
      exact hu.ne_zero ((hr.2.1 d).mpr hlt)
    · intro h1
      have hne : (d : Fv D.host.F v) ≠ 0 := by
        intro h0; rw [h0, map_zero] at h1; exact zero_ne_one h1
      have hinv : ((d : Fv D.host.F v))⁻¹ ∈ v.adicCompletionIntegers D.host.F := by
        show Valued.v ((d : Fv D.host.F v))⁻¹ ≤ 1
        rw [map_inv₀, h1, inv_one]
      have hdu : IsUnit d := by
        refine ⟨⟨d, ⟨_, hinv⟩, ?_, ?_⟩, rfl⟩ <;> ext <;> simp [hne]
      exact hdu.map r
  have hlow : LowZero k (Yo.map r) ↔ ∀ i j, k ≤ i.val → j.val < k → Valued.v (Y i j) < 1 := by
    unfold LowZero
    refine forall_congr' fun i => forall_congr' fun j => forall_congr' fun _ => forall_congr' fun _ => ?_
    exact hr.2.1 (Yo i j)
  rw [hy]
  unfold qLoc
  by_cases hc : Valued.v (d : Fv D.host.F v) = 1 ∧ ∀ i j, k ≤ i.val → j.val < k → Valued.v (Y i j) < 1
  · have hA : IsUnit (topL k Y).det ∧ Valued.v (topL k Y).det = 1 ∧ (∀ i j, Y i j ∈ v.adicCompletionIntegers D.host.F) ∧
        ∀ i j, k ≤ i.val → j.val < k → Valued.v (Y i j) < 1 := by
      refine ⟨?_, by rw [hdetY]; exact hc.1, hint, hc.2⟩
      rw [hdetY, isUnit_iff_ne_zero]
      intro h0; have := hc.1; rw [h0, map_zero] at this; exact zero_ne_one this
    have hB : LowZero k (Yo.map r) ∧ IsUnit (topL k (Yo.map r)).det :=
      ⟨hlow.mpr hc.2, by rw [hdety]; exact hunit.mpr hc.1⟩
    rw [dite_eq_left hA, dite_eq_left hB]
    have hrel : RedRel φ PP ((hA.1.unit : Fv D.host.F v)) ((hB.2.unit : Formalism.L2.DIV.kP PP)) := by
      refine (hr.2.2.1 _ _).mpr ⟨by convert d.2 using 2; rw [IsUnit.unit_spec, hdetY], ?_⟩
      rw [IsUnit.unit_spec hB.2, hdety]
      congr 1
      apply Subtype.ext
      simp [IsUnit.unit_spec, hdetY]
    have hm := hmu _ _ hrel
    rw [hm, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_inv]
  · rw [dite_eq_right (fun h => hc ⟨by rw [← hdetY]; exact h.2.1, h.2.2.2⟩),
      dite_eq_right (fun h => hc ⟨hunit.mp (by rw [← hdety]; exact h.2), hlow.mp h.1⟩)]

end GlobalTheory.StepVec
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepVec

variable {D : D7}

theorem isUnit_of_isRedMap {v : FinPl D} {φ : SplitProj D v} {PP : Formalism.L2.DIV.Pl D.host.E}
    {r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP} (hr : IsRedMap φ PP r)
    {x : v.adicCompletionIntegers D.host.F} (h : IsUnit (r x)) : IsUnit x := by
  by_contra hx
  have h1 := Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hx
  have h2 : r x = 0 := (hr.2.1 x).2 h1
  rw [h2] at h
  exact not_isUnit_zero h

theorem redRel_of_isRedMap {v : FinPl D} {φ : SplitProj D v} {PP : Formalism.L2.DIV.Pl D.host.E}
    {r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP} (hr : IsRedMap φ PP r)
    (x : v.adicCompletionIntegers D.host.F) : RedRel φ PP (x : Fv D.host.F v) (r x) :=
  (hr.2.2.1 _ _).2 ⟨x.2, rfl⟩



theorem locDatum_eq_viaRed : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E)
    (r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP), IsRedMap φ PP r →
    ∀ (a b t : ℕ) (ht : a + t = b) (L : Formalism.L2.DIV.LevDat D.host.E ℂ a)
    (H : Subgroup (GL (Fin L.r) (Formalism.L2.DIV.kP PP))) (c : H →* ℂˣ)
    (J : Subgroup (GL (Fin a) (v.adicCompletionIntegers D.host.F))) (lam : J →* ℂˣ), IsLocLevel φ PP L H c J lam →
    ∀ (mu : (Fv D.host.F v)ˣ →* ℂˣ) (χ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), LiftsChar φ PP mu χ →
    ∀ Y : Matrix (Fin b) (Fin a) (Fv D.host.F v),
      localNewformFunction v J lam mu (rowsTB ht Y) = viaRed r (gLoc (b := b) L PP H c χ) Y := by
  intro D v φ PP r hr a b t ht L H c J lam hJ mu χ hmu Y
  have hinl : ∀ (i : Fin a) (j : Fin a), rowsTB ht Y (Sum.inl i) j = Y ⟨i.val, by omega⟩ j := fun _ _ => rfl
  have hinr : ∀ (i : Fin t) (j : Fin a), rowsTB ht Y (Sum.inr i) j = Y ⟨a + i.val, by omega⟩ j := fun _ _ => rfl

  unfold viaRed
  by_cases hint : ∀ i j, Y i j ∈ v.adicCompletionIntegers D.host.F
  swap
  · rw [dite_eq_right hint]
    unfold localNewformFunction
    rw [dite_eq_right]
    rintro ⟨⟨k, hk⟩, hbot⟩
    apply hint
    intro i j
    by_cases hi : i.val < a
    · have h1 := congrFun (congrFun hk ⟨i.val, hi⟩) j
      rw [Matrix.submatrix_apply, hinl] at h1
      simp only [Matrix.map_apply, id] at h1
      rw [show i = ⟨i.val, by omega⟩ from rfl, ← h1]
      exact ((k : GL (Fin a) (v.adicCompletionIntegers D.host.F)) : Matrix (Fin a) (Fin a) (v.adicCompletionIntegers D.host.F)) ⟨i.val, hi⟩ j |>.2
    · have h1 := (hbot ⟨i.val - a, by omega⟩ j).1
      rw [hinr] at h1
      have : (⟨a + (i.val - a), by omega⟩ : Fin b) = i := Fin.ext (by simp; omega)
      rwa [this] at h1
  rw [dite_eq_left hint]

  set y : Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP) := Matrix.of fun i j => r ⟨Y i j, hint i j⟩ with hy
  let K : Matrix (Fin a) (Fin a) (v.adicCompletionIntegers D.host.F) := fun i j => ⟨Y ⟨i.val, by omega⟩ j, hint _ _⟩
  have hKr : K.map r = topL a y := by
    ext i j
    simp only [topL, Matrix.map_apply]
    rw [dite_eq_left ⟨by omega, j.2⟩]
    rfl

  have hKk : ∀ k : GL (Fin a) (v.adicCompletionIntegers D.host.F),
      ((k : Matrix (Fin a) (Fin a) _).map (algebraMap (v.adicCompletionIntegers D.host.F) (Fv D.host.F v)) =
        (rowsTB ht Y).submatrix Sum.inl id) → (k : Matrix (Fin a) (Fin a) _) = K := by
    intro k hk
    funext i j
    apply Subtype.ext
    have h1 := congrFun (congrFun hk i) j
    rw [Matrix.submatrix_apply, hinl] at h1
    exact h1

  have hred : ∀ k : GL (Fin a) (v.adicCompletionIntegers D.host.F), (k : Matrix (Fin a) (Fin a) _) = K →
      ((Matrix.GeneralLinearGroup.map r k : GL (Fin a) (Formalism.L2.DIV.kP PP)) : Matrix (Fin a) (Fin a) _) = topL a y ∧
      ∀ i j, RedRel φ PP (((k : Matrix (Fin a) (Fin a) _) i j : v.adicCompletionIntegers D.host.F) : Fv D.host.F v)
        (((Matrix.GeneralLinearGroup.map r k : GL (Fin a) (Formalism.L2.DIV.kP PP)) : Matrix (Fin a) (Fin a) _) i j) := by
    intro k hk
    refine ⟨?_, fun i j => redRel_of_isRedMap hr _⟩
    rw [← hKr, ← hk]
    rfl

  unfold gLoc localNewformFunction
  split_ifs with hP hG hG
  ·
    have hk0 := hP.1.choose_spec
    have hg0 := hG.2.choose_spec
    generalize hP.1.choose = k₀ at hk0 ⊢
    obtain ⟨k, hkJ⟩ := k₀
    have hK := hKk k hk0
    obtain ⟨hm, hrr⟩ := hred k hK
    have hkg : Matrix.GeneralLinearGroup.map r k = hG.2.choose := Units.ext (hm.trans hg0.1.symm)
    have hlam := (hJ _ _ hrr).2 hkJ
    rw [hkg, Formalism.L2.DIV.extendOne_of_mem _ hg0.2.2] at hlam
    have hdet : RedRel φ PP ((Units.map (algebraMap (v.adicCompletionIntegers D.host.F) (Fv D.host.F v)).toMonoidHom
        (Matrix.GeneralLinearGroup.det k) : (Fv D.host.F v)ˣ) : Fv D.host.F v)
          ((Matrix.GeneralLinearGroup.det hG.2.choose : (Formalism.L2.DIV.kP PP)ˣ) : Formalism.L2.DIV.kP PP) := by
      have e2 : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map r k) : (Formalism.L2.DIV.kP PP)ˣ) :
          Formalism.L2.DIV.kP PP) = r ((Matrix.GeneralLinearGroup.det k : (v.adicCompletionIntegers D.host.F)ˣ) :
            v.adicCompletionIntegers D.host.F) := by
        exact (RingHom.map_det r (k : Matrix (Fin a) (Fin a) _)).symm
      rw [← hkg, e2]
      exact redRel_of_isRedMap hr _
    rw [hlam, hmu _ _ hdet]
    push_cast
    rfl
  ·
    exfalso
    apply hG
    obtain ⟨⟨⟨k, hkJ⟩, hk⟩, hbot⟩ := hP
    have hK := hKk k hk
    obtain ⟨hm, hrr⟩ := hred k hK
    have hJk := ((hJ k _ hrr).1.1 hkJ)
    refine ⟨?_, Matrix.GeneralLinearGroup.map r k, hm, hJk⟩
    intro i j hi hj
    have h1 := hbot ⟨i.val - a, by omega⟩ ⟨j.val, hj⟩
    rw [hinr] at h1
    have : (⟨a + (i.val - a), by omega⟩ : Fin b) = i := Fin.ext (by simp; omega)
    rw [this] at h1
    exact (hr.2.1 ⟨Y i ⟨j.val, hj⟩, hint _ _⟩).2 h1.2
  ·
    exfalso
    apply hP
    obtain ⟨hlow, g, hg, hgT, hgH⟩ := hG
    have hdet : IsUnit K.det := by
      apply isUnit_of_isRedMap hr
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hKr, ← hg]
      exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    let k : GL (Fin a) (v.adicCompletionIntegers D.host.F) := ((Matrix.isUnit_iff_isUnit_det K).2 hdet).unit
    have hkK : (k : Matrix (Fin a) (Fin a) _) = K := rfl
    obtain ⟨hm, hrr⟩ := hred k hkK
    have hkg : Matrix.GeneralLinearGroup.map r k = g := Units.ext (hm.trans hg.symm)
    have hkJ : k ∈ J := (hJ k _ hrr).1.2 (hkg ▸ ⟨hgT, hgH⟩)
    refine ⟨⟨⟨k, hkJ⟩, ?_⟩, ?_⟩
    · funext i j
      rfl
    · intro i j
      rw [hinr]
      refine ⟨hint _ _, (hr.2.1 ⟨Y _ j, hint _ _⟩).1 ?_⟩
      exact hlow ⟨a + i.val, by omega⟩ j (by simp) j.2
  · rfl

end GlobalTheory.StepVec
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StepVec

theorem level_character_congr {E : Type} [Field E] [NumberField E] {Pg : Finset (Formalism.L2.DIV.Pl E)} {r : ℕ}
    {P Q : Formalism.L2.DIV.LevelP Pg r ℂ} (h : P = Q) (x : Formalism.L2.DIV.G0 Pg r) (hx : x ∈ P.H) (hx' : x ∈ Q.H) :
    P.chi ⟨x, hx⟩ = Q.chi ⟨x, hx'⟩ := by
  subst h; rfl

theorem omegaG_eq_prod_gLoc : ∀ (D : D7) (a b : ℕ) (L : Formalism.L2.DIV.LevDat D.host.E ℂ a)
    (χ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (Hl : ∀ PP : ↥L.Pg, Subgroup (GL (Fin L.r) (Formalism.L2.DIV.kP PP.1))) (cl : ∀ PP : ↥L.Pg, Hl PP →* ℂˣ),
    L.P = Formalism.L2.DIV.LevelP.ofLocal Hl cl →
    ∀ y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP),
      omegaG L χ y = ∏ PP : ↥L.Pg, gLoc L PP.1 (Hl PP) (cl PP) (χ PP.1) (y PP.1) := by
  intro D a b L χ Hl cl hP y
  classical
  have hmem : ∀ x, x ∈ L.P.H ↔ ∀ PP, x PP ∈ Hl PP := by
    intro x; rw [hP]; simp [Formalism.L2.DIV.LevelP.ofLocal, Subgroup.mem_pi]
  by_cases hall : ∀ PP : ↥L.Pg, LowZero a (y PP.1) ∧ ∃ g : GL (Fin a) (Formalism.L2.DIV.kP PP.1),
      ((g : GL (Fin a) _) : Matrix (Fin a) (Fin a) _) = topL a (y PP.1) ∧
      g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t) ∧ Formalism.L2.DIV.upperLeftBlock L.hr g ∈ Hl PP
  · have hG : (∀ PP ∈ L.Pg, LowZero a (y PP)) ∧
        ∃ g : ∀ PP : ↥L.Pg, GL (Fin a) (Formalism.L2.DIV.kP PP.1),
          (∀ PP : ↥L.Pg, ((g PP : GL (Fin a) _) : Matrix (Fin a) (Fin a) _) = topL a (y PP.1)) ∧
          (∀ PP : ↥L.Pg, g PP ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t)) ∧
          (fun PP => Formalism.L2.DIV.upperLeftBlock L.hr (g PP)) ∈ L.P.H :=
      ⟨fun PP hPP => (hall ⟨PP, hPP⟩).1, fun PP => (hall PP).2.choose, fun PP => (hall PP).2.choose_spec.1,
        fun PP => (hall PP).2.choose_spec.2.1, (hmem _).2 fun PP => (hall PP).2.choose_spec.2.2⟩
    have key : ∀ PP, hG.2.choose PP = (hall PP).2.choose := fun PP =>
      Units.ext ((hG.2.choose_spec.1 PP).trans ((hall PP).2.choose_spec.1).symm)
    rw [omegaG, dite_eq_left hG]
    have hloc : ∀ PP : ↥L.Pg, gLoc L PP.1 (Hl PP) (cl PP) (χ PP.1) (y PP.1) =
        ((cl PP ⟨Formalism.L2.DIV.upperLeftBlock L.hr (hall PP).2.choose, (hall PP).2.choose_spec.2.2⟩ : ℂˣ) : ℂ) *
          (∏ i ∈ Finset.range L.s,
            ((L.cg (i + 1) PP.1 (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf L.r L.t) (i + 1) (hall PP).2.choose) : ℂˣ) : ℂ)) *
          (((χ PP.1 (Matrix.GeneralLinearGroup.det (hall PP).2.choose)) : ℂˣ) : ℂ)⁻¹ := fun PP => by
      rw [gLoc, dite_eq_left (hall PP)]
    rw [Finset.prod_congr rfl fun PP _ => hloc PP]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    have hx' : (fun PP => Formalism.L2.DIV.upperLeftBlock L.hr (hG.2.choose PP)) ∈ (Formalism.L2.DIV.LevelP.ofLocal Hl cl).H := by
      rw [← hP]; exact hG.2.choose_spec.2.2
    congr 1
    congr 1
    · rw [level_character_congr hP _ _ hx', ← Units.coe_prod]
      refine congrArg Units.val ((MonoidHom.finsetProd_apply _ _ _).trans (Finset.prod_congr rfl fun PP _ => ?_))
      refine congrArg (cl PP) (Subtype.ext ?_)
      exact congrArg (Formalism.L2.DIV.upperLeftBlock L.hr) (key PP)
    · refine Finset.prod_congr rfl fun PP _ => ?_
      rw [key PP]
    · refine Finset.prod_congr rfl fun PP _ => ?_
      rw [key PP]
  · have hG : ¬ ((∀ PP ∈ L.Pg, LowZero a (y PP)) ∧
        ∃ g : ∀ PP : ↥L.Pg, GL (Fin a) (Formalism.L2.DIV.kP PP.1),
          (∀ PP : ↥L.Pg, ((g PP : GL (Fin a) _) : Matrix (Fin a) (Fin a) _) = topL a (y PP.1)) ∧
          (∀ PP : ↥L.Pg, g PP ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t)) ∧
          (fun PP => Formalism.L2.DIV.upperLeftBlock L.hr (g PP)) ∈ L.P.H) := by
      rintro ⟨h1, g, hg1, hg2, hg3⟩
      exact hall fun PP => ⟨h1 PP.1 PP.2, g PP, hg1 PP, hg2 PP, (hmem _).1 hg3 PP⟩
    push_neg at hall
    obtain ⟨PP, hPP⟩ := hall
    rw [omegaG, dite_eq_right hG]
    refine (Finset.prod_eq_zero (Finset.mem_univ PP) ?_).symm
    rw [gLoc, dite_eq_right]
    rintro ⟨h1, g, hg1, hg2, hg3⟩
    exact hPP h1 g hg1 hg2 hg3

end GlobalTheory.StepVec

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StepVec

variable {D : D7}

def redLevGrp {κ : Type} [CommRing κ] {a : ℕ} (r t : ℕ) (hr : r ≤ a) (H : Subgroup (GL (Fin r) κ)) :
    Subgroup (GL (Fin a) κ) where
  carrier := {kb | kb ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ∧ Formalism.L2.DIV.upperLeftBlock hr kb ∈ H}
  one_mem' := by
    refine ⟨Subgroup.one_mem _, ?_⟩
    show Formalism.L2.DIV.ext1 _ _ 1 ∈ H
    rw [Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one]; exact H.one_mem
  mul_mem' := by
    rintro x y ⟨hx, hxH⟩ ⟨hy, hyH⟩
    refine ⟨Subgroup.mul_mem _ hx hy, ?_⟩
    have e : Formalism.L2.DIV.upperLeftBlock hr (x * y) = Formalism.L2.DIV.upperLeftBlock hr x * Formalism.L2.DIV.upperLeftBlock hr y :=
      Formalism.L2.DIV.extendMatrixByIdentityAlongIndices_mul _ (Formalism.L2.DIV.blockTri_blkOf_le r t hx) (Formalism.L2.DIV.blockTri_blkOf_le r t hy)
    rw [e]; exact H.mul_mem hxH hyH
  inv_mem' := by
    rintro x ⟨hx, hxH⟩
    refine ⟨Subgroup.inv_mem _ hx, ?_⟩
    have e : Formalism.L2.DIV.upperLeftBlock hr x⁻¹ = (Formalism.L2.DIV.upperLeftBlock hr x)⁻¹ :=
      Formalism.L2.DIV.extendOne_inv _ (Formalism.L2.DIV.blockTri_blkOf_le r t hx)
    rw [e]; exact H.inv_mem hxH

def redLevChar {κ : Type} [CommRing κ] {a : ℕ} (r t s : ℕ) (hr : r ≤ a) (H : Subgroup (GL (Fin r) κ)) (c : H →* ℂˣ)
    (cg : ℕ → κˣ →* ℂˣ) : redLevGrp r t hr H →* ℂˣ where
  toFun kb := Formalism.L2.DIV.ext1 H c (Formalism.L2.DIV.upperLeftBlock hr kb.1) *
    ∏ i ∈ Finset.range s, cg (i + 1) (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) (i + 1) kb.1)
  map_one' := by
    simp only [OneMemClass.coe_one]
    have h1 : Formalism.L2.DIV.upperLeftBlock hr (1 : GL (Fin a) κ) = 1 := Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
    have h2 : ∀ c', Formalism.L2.DIV.dBlk (κ := κ) (n := a) (Formalism.L2.DIV.blkOf r t) c' 1 = 1 := fun _ =>
      Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
    rw [h1, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one]
    simp [h2]
  map_mul' := by
    rintro ⟨x, hx, hxH⟩ ⟨y, hy, hyH⟩
    show Formalism.L2.DIV.ext1 H c (Formalism.L2.DIV.upperLeftBlock hr (x * y)) *
        ∏ i ∈ Finset.range s, cg (i + 1) (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) (i + 1) (x * y)) = _
    have e : Formalism.L2.DIV.upperLeftBlock hr (x * y) = Formalism.L2.DIV.upperLeftBlock hr x * Formalism.L2.DIV.upperLeftBlock hr y :=
      Formalism.L2.DIV.extendMatrixByIdentityAlongIndices_mul _ (Formalism.L2.DIV.blockTri_blkOf_le r t hx) (Formalism.L2.DIV.blockTri_blkOf_le r t hy)
    rw [e, Formalism.L2.DIV.extendMatrixByIdentityAlongIndices_mul c hxH hyH]
    have e2 : ∀ i ∈ Finset.range s, cg (i + 1) (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) (i + 1) (x * y)) =
        cg (i + 1) (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) (i + 1) x) *
          cg (i + 1) (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) (i + 1) y) := fun i _ => by
      rw [Formalism.L2.DIV.diag_block_det_mul hx hy, map_mul]
    rw [Finset.prod_congr rfl e2, Finset.prod_mul_distrib, mul_mul_mul_comm]

theorem exists_isLocLevel : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E)
    (r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP), IsRedMap φ PP r →
    ∀ (a : ℕ) (L : Formalism.L2.DIV.LevDat D.host.E ℂ a) (H : Subgroup (GL (Fin L.r) (Formalism.L2.DIV.kP PP))) (c : H →* ℂˣ),
    ∃ (J : Subgroup (GL (Fin a) (v.adicCompletionIntegers D.host.F))) (lam : J →* ℂˣ), IsLocLevel φ PP L H c J lam := by
  intro D v φ PP r hred a L H c
  let f := Matrix.GeneralLinearGroup.map (n := Fin a) r
  refine ⟨(redLevGrp L.r L.t L.hr H).comap f,
    (redLevChar L.r L.t L.s L.hr H c (fun i => L.cg i PP)).comp
      ((f.subgroupComap (redLevGrp L.r L.t L.hr H))), ?_⟩
  intro k kb hk
  have hkb : kb = f k := by
    ext i j
    obtain ⟨h, e⟩ := (hred.2.2.1 _ _).1 (hk i j)
    rw [← e]
    rfl
  subst hkb
  exact ⟨Iff.rfl, fun _ => rfl⟩

end GlobalTheory.StepVec
end
end

section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional

private lemma detShift_eq_add_of_weight_shift (n : ℕ) (c : ℤ) (lam lam' : DomWeight n) (h : ∀ i, lam'.w i = lam.w i + c)
    (hn : 0 < n) : lam'.detShift = lam.detShift + c := by
  simp only [DomWeight.detShift, dif_pos hn, h]

private lemma natW_eq_of_weight_shift (n : ℕ) (c : ℤ) (lam lam' : DomWeight n) (h : ∀ i, lam'.w i = lam.w i + c) :
    lam'.natW = lam.natW := by
  funext i
  simp only [DomWeight.natW, detShift_eq_add_of_weight_shift n c lam lam' h (Fin.pos i), h]
  congr 1
  ring

private lemma nablaSq_eq_of_weight_shift (n : ℕ) (c : ℤ) (lam lam' : DomWeight n) (h : ∀ i, lam'.w i = lam.w i + c) :
    nablaSq ℂ n lam' = nablaSq ℂ n lam := by
  simp only [nablaSq, natW_eq_of_weight_shift n c lam lam' h]

private lemma detPow_detShift_of_weight_shift (n : ℕ) (c : ℤ) (lam lam' : DomWeight n) (h : ∀ i, lam'.w i = lam.w i + c) (g : U n) :
    detPow ℂ n (unitaryIncl n g) lam'.detShift =
      ((detU n g ^ c : ℂˣ) : ℂ) * detPow ℂ n (unitaryIncl n g) lam.detShift := by
  have hdet : Matrix.GeneralLinearGroup.det (unitaryIncl n g) = detU n g := by
    ext
    simp [detU, unitaryIncl_coe]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h1 : detU 0 g = 1 := by
      ext
      simp [detU]
    simp [h1, DomWeight.detShift, detPow]
  · simp only [detPow, detShift_eq_add_of_weight_shift n c lam lam' h hn, hdet, zpow_add, Units.val_mul]
    ring

theorem iso_twist_det_irr_shift (n : ℕ) (c : ℤ) (lam lam' : DomWeight n) (h : ∀ i, lam'.w i = lam.w i + c) :
    Iso (GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.twist (detU n ^ c) (irr n lam)) (irr n lam') := by
  refine ⟨LinearEquiv.ofEq _ _ (nablaSq_eq_of_weight_shift n c lam lam' h).symm, fun g x => ?_⟩
  apply Subtype.ext
  change ((detU n ^ c) g : ℂ) • (sqRep ℂ n lam (unitaryIncl n g) x : MvPolynomial (Fin n × Fin n) ℂ) =
    (sqRep ℂ n lam' (unitaryIncl n g) (LinearEquiv.ofEq _ _ (nablaSq_eq_of_weight_shift n c lam lam' h).symm x) :
      MvPolynomial (Fin n × Fin n) ℂ)
  have hz : (detU n ^ c) g = detU n g ^ c := rfl
  rw [sqRep_coe, sqRep_coe, hz]
  simp only [sqAct, LinearEquiv.coe_ofEq_apply, detPow_detShift_of_weight_shift n c lam lam' h g, mul_smul]

end GlobalTheory.OneFunctional
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.idempotentComponent_mem_frameStabilizer : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (g g' : GA D V) (f : AE D), f * f = f → finE V g ∈ St β → Formalism.L2.Theta.mt V g' = f • Formalism.L2.Theta.mt V g + (1 - f) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → finE V g' ∈ St β := by
  first | exact @GlobalTheory.CompStab.component_mem_St | exact GlobalTheory.CompStab.component_mem_St | (intros; apply GlobalTheory.CompStab.component_mem_St <;> assumption)
end
