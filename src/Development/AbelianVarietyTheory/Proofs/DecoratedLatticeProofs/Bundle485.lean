module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle410
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle423
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle192
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle469
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle400
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle403
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle467
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle402
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle177
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle285
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle468
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle143
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle470
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LastLine

variable {D : D7}

theorem cancel (v : GlobalTheory.FinPl.Pl D) (x : D.host.E) (hx : x ≠ 0) (A : AE D → Prop)
    (hA : ∀ a ∈ idAt D (· = v), A a ↔ incA D x⁻¹ * a ∈ intAt D (· = v)) (P Q : AE D → Prop)
    (hP : ∀ o ∈ intAt D (· = v), ∀ t, P t → P (o * t)) (hQ : ∀ o ∈ intAt D (· = v), ∀ t, Q t → Q (o * t))
    (h : ∀ s ∈ idAt D (· = v), (∀ a ∈ idAt D (· = v), A a → P (s * a)) ↔ (∀ a ∈ idAt D (· = v), A a → Q (s * a))) :
    ∀ t ∈ idAt D (· = v), (P t ↔ Q t) := by
  intro t ht
  obtain ⟨ε, -, hεI, hε⟩ := GlobalTheory.IwaPlace.LocSD.exists_idem (D := D) v
  have hs : incA D x⁻¹ * t ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ ht
  have ha0 : incA D x * ε ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ hεI.1
  have hA0 : A (incA D x * ε) := by
    rw [hA _ ha0, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hx, map_one, one_mul]
    exact hεI
  have hst : incA D x⁻¹ * t * (incA D x * ε) = t := by
    rw [show incA D x⁻¹ * t * (incA D x * ε) = (incA D x⁻¹ * incA D x) * (ε * t) by ring, ← map_mul,
      inv_mul_cancel₀ hx, map_one, one_mul, hε t ht]
  have hsa : ∀ a, incA D x⁻¹ * t * a = (incA D x⁻¹ * a) * t := fun a => by ring
  constructor
  · intro hPt
    have := (h _ hs).1 (fun a ha hAa => by
      rw [hsa]; exact hP _ ((hA a ha).1 hAa) t hPt) _ ha0 hA0
    rwa [hst] at this
  · intro hQt
    have := (h _ hs).2 (fun a ha hAa => by
      rw [hsa]; exact hQ _ ((hA a ha).1 hAa) t hQt) _ ha0 hA0
    rwa [hst] at this

theorem colMul_mul {m n : ℕ} (X : Mx D m n) (i : Fin n) (o t : AE D) :
    colMul X i (o * t) = o • colMul X i t := by
  funext k
  simp only [GlobalTheory.FinPl.colMul, Pi.smul_apply, smul_eq_mul, mul_assoc]

end GlobalTheory.Core.Mi.LastLine

end

noncomputable section

namespace GlobalTheory.Core.Mi.LastLine

variable {D : D7}

theorem lastLine_match : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (z : Fin S₀.rank → D.host.E) (L L' : Lat S) (M M' : Lat S₀) (v : GlobalTheory.FinPl.Pl D) (c : AE D) (γ : GA D S₀), IsSelfDualC S₀ M → z ≠ 0 → LastAt ψ d z L M v → LastAt ψ d z L' M' v → NormOneAt v c → Formalism.L2.Theta.mt S₀ γ *ᵥ ratV z = ratV z → SMoves S₀ c γ M M' v → ∀ i : Fin ρ, i.1 + 1 = ρ → ∀ a ∈ idAt D (· = v), (colMul d.jX i a ∈ latV S L (· = v) ↔ colMul d.jX i (c * a) ∈ latV S L' (· = v)) := by
  intro D ψ S S₀ ρ d z L L' M M' v c γ hM hz hL hL' hc hγ hmv i hi a ha
  obtain ⟨𝔞, h𝔞, -, hline⟩ := GlobalTheory.T.selfDualLattice_rationalLineTrace_fractionalIdeal D S₀ M z hM hz
  obtain ⟨x, hx, hgen⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔞 h𝔞
  have hA : ∀ b ∈ idAt D (· = v), b • ratV z ∈ latV S₀ M (· = v) ↔ incA D x⁻¹ * b ∈ intAt D (· = v) :=
    fun b hb => (hline v b hb).trans ((hgen b).trans ⟨fun h => h.1, fun h => ⟨h, hb⟩⟩)
  have hent : ∀ b ∈ idAt D (· = v), ∀ k, (b • ratV z) k ∈ idAt D (· = v) := fun b hb k => by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hb
  have hmove : ∀ b ∈ idAt D (· = v),
      b • ratV z ∈ latV S₀ M (· = v) ↔ (c * b) • ratV z ∈ latV S₀ M' (· = v) := by
    intro b hb
    rw [hmv _ (hent b hb), Matrix.mulVec_smul, hγ, smul_smul]
  have hcc : c * cA D c = 1 := hc.1
  have key : ∀ s ∈ idAt D (· = v),
      (∀ b ∈ idAt D (· = v), b • ratV z ∈ latV S₀ M (· = v) → colMul d.jX i (s * b) ∈ latV S L (· = v)) ↔
        (∀ b ∈ idAt D (· = v), b • ratV z ∈ latV S₀ M (· = v) →
          colMul d.jX i (c * (s * b)) ∈ latV S L' (· = v)) := by
    intro s hs
    rw [hL i hi s hs, ← hL' i hi s hs]
    constructor
    · intro h b hb hbM
      rw [show c * (s * b) = s * (c * b) by ring]
      exact h _ (Ideal.mul_mem_left _ _ hb) ((hmove b hb).1 hbM)
    · intro h b' hb' hb'M
      have hb : cA D c * b' ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ hb'
      have hcb : c * (cA D c * b') = b' := by rw [← mul_assoc, hcc, one_mul]
      have := h _ hb ((hmove _ hb).2 (by rw [hcb]; exact hb'M))
      rwa [show c * (s * (cA D c * b')) = s * (c * (cA D c * b')) by ring, hcb] at this
  exact cancel v x hx (fun b => b • ratV z ∈ latV S₀ M (· = v)) hA
    (fun t => colMul d.jX i t ∈ latV S L (· = v)) (fun t => colMul d.jX i (c * t) ∈ latV S L' (· = v))
    (fun o ho t ht => by
      show colMul d.jX i (o * t) ∈ latV S L (· = v)
      rw [colMul_mul]
      exact GlobalTheory.FinPlLoc.smul_latV v ho ht)
    (fun o ho t ht => by
      show colMul d.jX i (c * (o * t)) ∈ latV S L' (· = v)
      rw [mul_left_comm, colMul_mul]
      exact GlobalTheory.FinPlLoc.smul_latV v ho ht)
    key a ha

end GlobalTheory.Core.Mi.LastLine

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch.FlagDown

variable {D : D7}

theorem col_ne_zero {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (j : Fin ρ) : (fun k => d.e k j) ≠ 0 := by
  intro h
  have h1 := congrFun (congrFun d.e'e j) j
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
  have : ∀ k, d.e k j = 0 := fun k => congrFun h k
  simp [this] at h1

theorem colMul_eq {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (j : Fin ρ) (a : AE D) :
    colMul d.jX j a = a • ratV (fun k => d.e k j) := rfl

theorem mem_idAt_of_colMul {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (j : Fin ρ) {L : Lat S}
    {P : GlobalTheory.FinPl.Pl D → Prop} {a : AE D} (h : colMul d.jX j a ∈ latV S L P) : a ∈ idAt D P := by
  obtain ⟨k, hk⟩ : ∃ k, d.e k j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact col_ne_zero d j (funext hc)
  have h1 : a * incA D (d.e k j) ∈ idAt D P := GlobalTheory.FinPlLoc.latV_idAt h k
  have h2 := (idAt D P).mul_mem_right (incA D (d.e k j)⁻¹) h1
  rwa [mul_assoc, ← map_mul, mul_inv_cancel₀ hk, map_one, mul_one] at h2

theorem line_gen {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (j : Fin ρ) (L : Lat S) (hL : IsSelfDualC S L)
    (v : GlobalTheory.FinPl.Pl D) : ∃ x : D.host.E, x ≠ 0 ∧ ∀ a ∈ idAt D (· = v),
      (colMul d.jX j a ∈ latV S L (· = v) ↔ incA D x⁻¹ * a ∈ intAt D (· = v)) := by
  obtain ⟨𝔞, h𝔞, -, hv⟩ := GlobalTheory.T.selfDualLattice_rationalLineTrace_fractionalIdeal D S L _ hL (col_ne_zero d j)
  obtain ⟨x, hx, hx'⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔞 h𝔞
  refine ⟨x, hx, fun a ha => ?_⟩
  rw [colMul_eq, hv v a ha, hx']
  exact ⟨fun h => h.1, fun h => ⟨h, ha⟩⟩

theorem cancel {v : GlobalTheory.FinPl.Pl D} (x : D.host.E) (hx : x ≠ 0) (P Q : AE D → Prop)
    (hP : ∀ o ∈ intAt D (· = v), ∀ t, P t → P (o * t)) (hQ : ∀ o ∈ intAt D (· = v), ∀ t, Q t → Q (o * t))
    (h : ∀ s ∈ idAt D (· = v),
      (∀ a ∈ idAt D (· = v), incA D x⁻¹ * a ∈ intAt D (· = v) → P (s * a)) ↔
        (∀ a ∈ idAt D (· = v), incA D x⁻¹ * a ∈ intAt D (· = v) → Q (s * a))) :
    ∀ t ∈ idAt D (· = v), P t ↔ Q t := by
  obtain ⟨ε, -, -, hε, hεid, -⟩ := GlobalTheory.FinPlLoc.part_idem (D := D) (· = v)
  intro t ht
  have hs : incA D x⁻¹ * t ∈ idAt D (· = v) := (idAt D _).mul_mem_left _ ht
  have ha0 : incA D x * ε ∈ idAt D (· = v) := (idAt D _).mul_mem_left _ hε.1
  have ha0' : incA D x⁻¹ * (incA D x * ε) ∈ intAt D (· = v) := by
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hx, map_one, one_mul]
  have key : incA D x⁻¹ * t * (incA D x * ε) = t := by
    calc _ = (incA D x⁻¹ * incA D x) * (ε * t) := by ring
    _ = t := by rw [← map_mul, inv_mul_cancel₀ hx, map_one, one_mul]; exact (hεid t).1 ht
  have red : ∀ R : AE D → Prop, (∀ o ∈ intAt D (· = v), ∀ t, R t → R (o * t)) → R t →
      ∀ a ∈ idAt D (· = v), incA D x⁻¹ * a ∈ intAt D (· = v) → R (incA D x⁻¹ * t * a) := by
    intro R hR hRt a _ ha
    have := hR _ ha t hRt
    rwa [show incA D x⁻¹ * a * t = incA D x⁻¹ * t * a by ring] at this
  constructor
  · intro hPt
    have := (h _ hs).1 (red P hP hPt) _ ha0 ha0'
    rwa [key] at this
  · intro hQt
    have := (h _ hs).2 (red Q hQ hQt) _ ha0 ha0'
    rwa [key] at this

end GlobalTheory.Core.Mi.LatMatch.FlagDown


open GlobalTheory.Core.Mi.LatMatch.FlagDown in
theorem GlobalTheory.Core.Mi.LatMatch.match_down_flag : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L L' : Lat S) (v : GlobalTheory.FinPl.Pl D) (c : AE D), IsSelfDualC S L → PrimAt ψ d L v → PrimAt ψ d L' v → NormOneAt v c → ∀ i j : Fin ρ, j.1 = i.1 + 1 → (∀ a ∈ idAt D (· = v), (colMul d.jX j a ∈ latV S L (· = v) ↔ colMul d.jX j (c * a) ∈ latV S L' (· = v))) → ∀ a ∈ idAt D (· = v), (colMul d.jX i a ∈ latV S L (· = v) ↔ colMul d.jX i (c * a) ∈ latV S L' (· = v)) := by
  intro D ψ S S₀ ρ d L L' v c hsd hP hP' hc i j hij hj
  obtain ⟨x, hx, hA⟩ := line_gen d j L hsd v
  refine cancel x hx (fun t => colMul d.jX i t ∈ latV S L (· = v))
    (fun t => colMul d.jX i (c * t) ∈ latV S L' (· = v)) ?_ ?_ ?_
  · intro o ho t ht
    have e : colMul d.jX i (o * t) = o • colMul d.jX i t := by
      funext k; simp only [colMul, Pi.smul_apply, smul_eq_mul]; ring
    show colMul d.jX i (o * t) ∈ latV S L (· = v)
    rw [e]; exact GlobalTheory.FinPlLoc.smul_latV v ho ht
  · intro o ho t ht
    have e : colMul d.jX i (c * (o * t)) = o • colMul d.jX i (c * t) := by
      funext k; simp only [colMul, Pi.smul_apply, smul_eq_mul]; ring
    show colMul d.jX i (c * (o * t)) ∈ latV S L' (· = v)
    rw [e]; exact GlobalTheory.FinPlLoc.smul_latV v ho ht
  · intro s hs
    have e1 := hP i j hij s hs
    have e2 := hP' i j hij s hs
    have l1 : (∀ a ∈ idAt D (· = v), incA D x⁻¹ * a ∈ intAt D (· = v) → colMul d.jX i (s * a) ∈ latV S L (· = v)) ↔
        (∀ a : AE D, colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (s * a) ∈ latV S L (· = v)) := by
      constructor
      · intro H a ha
        have hid := mem_idAt_of_colMul d j ha
        exact H a hid ((hA a hid).1 ha)
      · intro H a ha hx'
        exact H a ((hA a ha).2 hx')
    have l2 : (∀ a ∈ idAt D (· = v), incA D x⁻¹ * a ∈ intAt D (· = v) →
        colMul d.jX i (c * (s * a)) ∈ latV S L' (· = v)) ↔
        (∀ a' : AE D, colMul d.jX j a' ∈ latV S L' (· = v) → colMul d.jX i (s * a') ∈ latV S L' (· = v)) := by
      constructor
      · intro H a' ha'
        have ha'id := mem_idAt_of_colMul d j ha'
        have hb : cA D c * a' ∈ idAt D (· = v) := (idAt D _).mul_mem_left _ ha'id
        have hcb : c * (cA D c * a') = a' := by rw [← mul_assoc, hc.1, one_mul]
        have hj' := (hj _ hb).2 (by rw [hcb]; exact ha')
        have := H _ hb ((hA _ hb).1 hj')
        rwa [show c * (s * (cA D c * a')) = s * (c * (cA D c * a')) by ring, hcb] at this
      · intro H a ha hx'
        have hj' := (hj a ha).1 ((hA a ha).2 hx')
        have := H _ hj'
        rwa [show s * (c * a) = c * (s * a) by ring] at this
    exact l1.trans (e1.trans e2.symm) |>.trans l2.symm
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

open GlobalTheory.SeeSaw.AdaptFBIdeals

theorem primAt_lastAt_of_lines : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (z : Fin S₀.rank → D.host.E) (L : Lat S) (M : Lat S₀) (μ : D.host.E) (v : GlobalTheory.FinPl.Pl D), μ ≠ 0 → LineAt z μ M v → (∀ i : Fin ρ, ∀ a ∈ idAt D (· = v), colMul d.jX i a ∈ latV S L (· = v) ↔ incA D μ * a ∈ idV (dI D ^ (ρ - i.1)) v) → PrimAt ψ d L v ∧ LastAt ψ d z L M v := by
  intro D ψ hψ S S₀ ρ d z L M μ v hμ hline hcol
  have hdI : dI D ≠ 0 := (GlobalTheory.SeeSaw.ChainIdeals.host_ne_zero D).2.2.2
  have hu : incA D μ⁻¹ * incA D μ = 1 := by rw [← map_mul, inv_mul_cancel₀ hμ, map_one]
  have key : ∀ 𝔞 𝔟 : FI D, 𝔞 ≠ 0 → 𝔟 ≠ 0 → 𝔟 * 𝔞⁻¹ = dI D → ∀ s ∈ idAt D (· = v),
      ((∀ a ∈ idAt D (· = v), incA D μ * a ∈ idV 𝔞 v → incA D μ * (s * a) ∈ idV 𝔟 v) ↔
        ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1) := by
    intro 𝔞 𝔟 h𝔞 h𝔟 hq s hs
    rw [← GlobalTheory.SeeSaw.DiffDual.idV_dI_iff D ψ hψ v s hs, ← hq, ← GlobalTheory.T.mul_fractionalIdealCompletion_subset_iff_mem_quotient D v 𝔞 𝔟 h𝔞 h𝔟 s hs]
    constructor
    · intro h b hb
      have hbAt := idV_supp 𝔞 v hb
      have ha : incA D μ⁻¹ * b ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ hbAt
      have hb' : incA D μ * (incA D μ⁻¹ * b) = b := by rw [← mul_assoc, mul_comm (incA D μ), hu, one_mul]
      have h2 := h _ ha (by rw [hb']; exact hb)
      rwa [mul_left_comm, hb'] at h2
    · intro h a _ hma
      rw [mul_left_comm]
      exact h _ hma
  constructor
  · intro i j hij s hs
    have hq : dI D ^ (ρ - i.1) * (dI D ^ (ρ - j.1))⁻¹ = dI D := by
      have he : ρ - i.1 = (ρ - j.1) + 1 := by have := j.2; omega
      rw [he, pow_succ, mul_comm, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hdI), one_mul]
    rw [← key (dI D ^ (ρ - j.1)) (dI D ^ (ρ - i.1)) (pow_ne_zero _ hdI) (pow_ne_zero _ hdI) hq s hs]
    constructor
    · intro h a ha hma
      exact (hcol i (s * a) (Ideal.mul_mem_left _ _ ha)).1 (h a ((hcol j a ha).2 hma))
    · intro h a ha
      have haAt := supp_of_colMul d L v j a ha
      exact (hcol i (s * a) (Ideal.mul_mem_left _ _ haAt)).2 (h a haAt ((hcol j a haAt).1 ha))
  · intro i hi s hs
    rw [← key 1 (dI D) one_ne_zero hdI (by rw [inv_one, mul_one]) s hs]
    have hρi : ρ - i.1 = 1 := by omega
    constructor
    · intro h a ha hma
      rw [GlobalTheory.SeeSaw.idV_one_eq_intAt] at hma
      have h2 := (hcol i (s * a) (Ideal.mul_mem_left _ _ ha)).1 (h a ha ((hline a ha).2 hma))
      rwa [hρi, pow_one] at h2
    · intro h a ha hz
      have h2 := h a ha ((GlobalTheory.SeeSaw.idV_one_eq_intAt D v _).2 ((hline a ha).1 hz))
      exact (hcol i (s * a) (Ideal.mul_mem_left _ _ ha)).2 (by rwa [hρi, pow_one])

end GlobalTheory.Core.Mi.LatMatch

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.KsetAt

theorem mem_Kset_iff_moves : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (v : GlobalTheory.FinPl.Pl D) (κ : GA D (D.sp.Y 0)), κ ∈ grpAt (D.sp.Y 0) (· = v) → ((iotaX X h κ).2 ∈ X.B.I.Kset ↔ Moves (D.sp.Y 0) κ (latS D) (latS D) (· = v)) := by
  intro D X h v κ hκ
  have hlat : Submodule.IsLattice D.host.E (latS D) :=
    GlobalTheory.StdFrames.isLattice_crdLat (D.sp.Y 0) (D.sp.Y 0).standardTuple_isLattice
  obtain ⟨β, hβ⟩ := GlobalTheory.StdFrames.exists_base (D.sp.Y 0)
  have hβ' : Formalism.L2.DIV.IsFrame β (latS D) := by
    change Formalism.L2.DIV.IsFrame β (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0)
    rw [hβ]
    exact GlobalTheory.StdFrames.isFrame_lat β
  have h1 := ((GlobalTheory.SeeConjReadIota.read_iota X h β hβ' κ).2.1)
  have h2 := GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_of_fg (D.sp.Y 0) β (latS D) hβ' hlat.fg κ
  have h3 : κ ∈ GlobalTheory.AdelicU.levelOpen D.sp.cm.sig (D.sp.Y 0).gram (latS D) ↔
      Moves (D.sp.Y 0) κ (latS D) (latS D) (· = v) :=
    ⟨fun hk => GlobalTheory.FinPl.KOpen.moves_of_levelOpen (D.sp.Y 0) (latS D) hlat.fg (· = v) hk,
     fun hm => GlobalTheory.FinPl.KOpen.levelOpen_of_inK (D.sp.Y 0) (latS D) hlat.fg (· = v) ⟨hκ, hm⟩⟩
  exact h1.trans (h2.trans (GlobalTheory.AdelicU.mem_levelOpen.symm.trans h3))

end GlobalTheory.Core.Mi.KsetAt
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

namespace GlobalTheory.QPl.EpsSupp

theorem exists_prod_of_mem_support_conv {G : Type} [Monoid G] : ∀ (n : ℕ) (f : Fin n → (G →₀ ℂ)) (g : G),
    g ∈ (conv (List.ofFn f)).support → ∃ x : Fin n → G, (∀ i, x i ∈ (f i).support) ∧ g = (List.ofFn x).prod := by
  classical
  intro n
  induction n with
  | zero =>
    intro f g hg
    simp only [List.ofFn_zero, conv, List.foldr_nil] at hg
    have := Finsupp.support_single_subset hg
    rw [Finset.mem_singleton] at this
    exact ⟨Fin.elim0, fun i => i.elim0, by simp [this]⟩
  | succ n ih =>
    intro f g hg
    rw [List.ofFn_succ] at hg
    simp only [conv, List.foldr_cons] at hg
    have h1 := Finsupp.support_sum hg
    rw [Finset.mem_biUnion] at h1
    obtain ⟨g₀, hg₀, h2⟩ := h1
    have h3 := Finsupp.support_sum h2
    rw [Finset.mem_biUnion] at h3
    obtain ⟨g', hg', h4⟩ := h3
    have h5 := Finsupp.support_single_subset h4
    rw [Finset.mem_singleton] at h5
    obtain ⟨x, hx, hxe⟩ := ih (fun k => f k.succ) g' hg'
    refine ⟨Fin.cons g₀ x, fun i => Fin.cases hg₀ (fun k => hx k) i, ?_⟩
    rw [List.ofFn_succ, List.prod_cons, h5, hxe]
    simp

theorem eps_mem_grpAt {D : D7} {c : Comm D} {v : VCom c} {t : Tup c} (F : QFam v t) (sc cT : ℕ → ℂ)
    (h0 : ∀ i β, (F.Q i).εL 0 β = Finsupp.single 1 1) (j : ℕ) (α : t.Ch j) :
    ∀ g ∈ ((F.pinTup sc cT).ε j α).support, g ∈ GlobalTheory.FinPl.grpAt (c.V j) (· ∈ (F.pinTup sc cT).Q) := by
  classical
  intro g hg
  dsimp only [QFam.pinTup] at hg ⊢
  split_ifs at hg with hc
  · have hg' := Finsupp.support_smul hg
    obtain ⟨x, hx, rfl⟩ := exists_prod_of_mem_support_conv _ _ g hg'
    apply Subgroup.list_prod_mem
    intro y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
    have hP : (F.Q i).q.v ∈ Finset.univ.image fun i => (F.Q i).q.v := Finset.mem_image_of_mem _ (Finset.mem_univ i)
    rcases hc with ⟨ρ, hρ⟩ | hj
    · obtain ⟨e, -, he⟩ := (F.Q i).εL_at j ρ hρ (2 * ρ) (by have := (F.Q i).hs; omega) (F.eqv j α i)
      have hxi := hx i
      rw [he] at hxi
      obtain ⟨a, -, hax⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hxi)
      rw [← hax]
      exact GlobalTheory.SuppGrp.mem_grpAt_of_suppAt D _ (F.Q i).q _ _ ((F.Q i).gl_loc _ _ _ a).1 _ hP
    · subst hj
      have hxi := hx i
      rw [h0] at hxi
      have h1 := Finsupp.support_single_subset hxi
      rw [Finset.mem_singleton] at h1
      rw [h1]
      exact one_mem _
  · simp at hg

end GlobalTheory.QPl.EpsSupp

end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.PenLev

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}
  {a : GeoAll W u} {t : W.P.T}

def relax (J : QJ a t) (j : ℕ) (hj : j + 1 = B.R.m) (α : J.Ch j) : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :=
  (J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (GlobalTheory.PenBridge.plF J)) ⊓ GfC _ ⊓
    (Subgroup.pi Set.univ fun i =>
      KO (J.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1) ⊕ Fin 0)).comap (GlobalTheory.PenBridge.rd J j hj)

def U0 (a : GeoAll W u) (j : ℕ) (hj : j + 1 = B.R.m) : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :=
  if h : ∃ t, ∃ J : QJ a t, J.Reads ∧ Nonempty (J.Ch j) then
    relax h.choose_spec.choose j hj h.choose_spec.choose_spec.2.some
  else ⊥

end GlobalTheory.PenLev
end
end
