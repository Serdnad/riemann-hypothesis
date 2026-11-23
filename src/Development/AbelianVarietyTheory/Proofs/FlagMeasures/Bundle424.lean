module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle339
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle370
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle296
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivFramesSameSecondLatticeFiberProof
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle184
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle141
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle241
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle022
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle369
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle411
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle371
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle418
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle393
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle419
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle380
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TripOfTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle340
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle407
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle321
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBesselScaleBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle149
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BpFormsOfThmBpDS
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle162
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle004
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle421
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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

noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc
namespace GlobalTheory.TypeAsm.PerRow
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sum_le_encard_fibres {α Θ : Type} (S : Finset α) (xf yf : α → ℕ) (Φ : α → Θ) (Tr : ℕ → ℕ → Set Θ) (f : α → ℝ)
    (B₁ B₂ : ℕ → ℝ) (R₁ R₂ : Finset ℕ) (hf : ∀ a ∈ S, 0 ≤ f a)
    (hR : ∀ a ∈ S, xf a ∈ R₁ ∧ yf a ∈ R₂ ∧ Φ a ∈ Tr (xf a) (yf a))
    (hB : ∀ a ∈ S, ∑ b ∈ S.filter (fun b => Φ b = Φ a ∧ xf b = xf a ∧ yf b = yf a), f b ≤ B₁ (xf a) * B₂ (yf a)) :
    ENNReal.ofReal (∑ a ∈ S, f a) ≤
      ∑ x ∈ R₁, ∑ y ∈ R₂, (((Tr x y).encard : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (B₁ x * B₂ y) :=
  GlobalTheory.T.sum_fibre_two_index_encard_bound α Θ S xf yf Φ Tr f B₁ B₂ R₁ R₂ hf hR hB

theorem sum_pairs_le_classes (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (hS : Std D large₂)
    (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W)
    (he : GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (h : GTu Y u → (W ≃ₗ[D.host.E] W))
    (hh : ∀ t ∈ relSet Y u, GlobalTheory.DegAsm.IsH (F0 X u) (Ft t) W.subtype t.lin (h t)) (Sf : Finset (GTu Y u × GTu Y u))
    (hSf : ∀ p ∈ Sf, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ p.1.lam = Λ)
    (hη : ∀ p ∈ Sf, ∀ q ∈ Sf, h p.1 * (h p.2)⁻¹ = h q.1 * (h q.2)⁻¹) :
    ∑ p ∈ Sf, wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2) ≤
      (∑ b ∈ Sf.image (fun p => frCls Λ p.1), clsOm Y u Λ b) * ∑ b ∈ Sf.image (fun p => frCls Λ p.2), clsOm Y u Λ b :=
  GlobalTheory.T.sum_pairs_definiteIsometry_le_frameClasses D large₂ X Y u hS W HW he Λ h hh Sf hSf hη

theorem sum_classes_le (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (hS : Std D large₂)
    (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W)
    (he : GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (j x : ℕ) (δ : ℕ → D.host.E)
    (d : Submodule (𝓞 D.host.E) W × Submodule (𝓞 D.host.E) (W × W)) (N : GTu Y u → GlobalTheory.DegCnt.NF (HV D) D.R.rS)
    (A : Finset (GTu Y u)) (hne : A.Nonempty)
    (hA : ∀ t ∈ A, t ∈ relSet Y u ∧ t.lam = Λ ∧ jT t = j ∧ labT t = δ ∧ AdT t (N t) ∧ (N t).IsTerm (gS D) Λ ∧
      (N t).gI (gS D) Λ = x ∧ GlobalTheory.DegAsm.datOf (F0 X u) (Ft t) W.subtype (gS D) Λ = d) :
    ∑ b ∈ A.image (frCls Λ), clsOm Y u Λ b ≤
      GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j δ) (DbL D j δ) (NT D u) x :=
  GlobalTheory.T.sum_frameClassWeights_le_datumBound D large₂ X Y u hS W HW he Λ j x δ d N A hne hA

theorem termData (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (hS : Std D large₂)
    (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W)
    (he : GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype) (t : GTu Y u) (ht : t ∈ relSet Y u) :
    ∃ (N : GlobalTheory.DegCnt.NF (HV D) D.R.rS) (h : W ≃ₗ[D.host.E] W), AdT t N ∧ N.IsTerm (gS D) t.lam ∧ N.j = jT t ∧
      N.T = Tu D u ∧ N.Del = k2Del D (jT t) (labT t) ∧ N.Db = DbL D (jT t) (labT t) ∧ 1 ≤ N.Del ∧ 1 ≤ N.Db ∧
      1 ≤ N.gI (gS D) t.lam ∧ (N.gI (gS D) t.lam : ℝ) ≤ N.Del ∧
      GlobalTheory.DegAsm.lab (F0 X u) (Ft t) (jT t) = (fun l => star (labT t l)) ∧
      h ∈ GlobalTheory.HermLat.isomGrp HW ∧ GlobalTheory.DegAsm.IsH (F0 X u) (Ft t) W.subtype t.lin h ∧
      Module.finrank D.host.E W = D.R.k := by
  obtain ⟨N, hA, hj, hT⟩ := GlobalTheory.T.exists_adaptedNormalForm_relevantTerm D large₂ X Y u hS t ht
  have hterm := GlobalTheory.T.rowLattice_term_adaptedNormalForm D large₂ X Y u hS t N hA
  obtain ⟨-, -, hDel, hDb, hlab⟩ := GlobalTheory.T.adaptedNormalForm_normsMinors_eq_label D large₂ X Y u hS t N hA
  obtain ⟨hK, -, -, -, -, -, -, -, -, -, hfin, hg2, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hS
  have hg : 1 ≤ gS D := by omega
  obtain ⟨-, hx1, hxD, -, hdim⟩ := GlobalTheory.T.embeddedDatum_of_term_definiteSpace D.host.E (VS D).V W (HV D) HW W.subtype hK D.R.rS (F0 X u) (Ft t)
    (dI D) N (gS D) t.lam hg he hA hterm
  obtain ⟨𝔠, -, hDb1, hDel1, -⟩ := GlobalTheory.T.exists_star_stable_ideal_absorbing_minors D.host.E (VS D).V (HV D) hK D.R.rS N (gS D) t.lam hg hterm
  have hiso : t.lin ∈ GlobalTheory.HermLat.isomGrp (HV D) := fun x y => t.rep.2.2.1 x y
  obtain ⟨h, hh, hH, -, -⟩ := GlobalTheory.T.exists_definiteSpace_isometry_of_adapted_pair D.host.E (VS D).V W (HV D) HW W.subtype hK D.R.rS (F0 X u) (Ft t) (dI D) N
    t.lin he hA hiso (fun a => GlobalTheory.TypeAsm.FibProof.Ft_e t a)
  exact ⟨N, h, hA, hterm, hj, hT, hDel, hDb, hDel1, hDb1, hx1, hxD, hlab, hh, hH, by omega⟩

theorem pairTrip (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (hS : Std D large₂)
    (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W)
    (he : GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype) (p : GTu Y u × GTu Y u) (hp : p ∈ (Y.tO u u).allPairs (relSet Y u))
    (N₁ N₂ : GlobalTheory.DegCnt.NF (HV D) D.R.rS) (h₁ h₂ : W ≃ₗ[D.host.E] W) (hA₁ : AdT p.1 N₁) (hA₂ : AdT p.2 N₂)
    (ht₁ : N₁.IsTerm (gS D) p.1.lam) (ht₂ : N₂.IsTerm (gS D) p.2.lam)
    (hH₁ : GlobalTheory.DegAsm.IsH (F0 X u) (Ft p.1) W.subtype p.1.lin h₁)
    (hH₂ : GlobalTheory.DegAsm.IsH (F0 X u) (Ft p.2) W.subtype p.2.lin h₂) :
    p.1.lam = p.2.lam ∧
      (GlobalTheory.DegAsm.datOf (F0 X u) (Ft p.1) W.subtype (gS D) p.1.lam,
        GlobalTheory.DegAsm.datOf (F0 X u) (Ft p.2) W.subtype (gS D) p.1.lam, h₁ * h₂⁻¹) ∈
        GlobalTheory.DegCnt.Trip HW (gS D) (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype p.1.lam) D.R.rS (N₁.gI (gS D) p.1.lam)
          (N₂.gI (gS D) p.1.lam) := by
  obtain ⟨hK, -, -, -, -, -, -, -, -, -, -, hg2, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hS
  have hg : 1 ≤ gS D := by omega
  obtain ⟨hl, hl', hc⟩ := GlobalTheory.T.termsOverRow_compatible D X Y u p ⟨trivial, trivial, hp.2.2⟩
  refine ⟨hl, ?_⟩
  have hi₁ : p.1.lin ∈ GlobalTheory.HermLat.isomGrp (HV D) := fun x y => p.1.rep.2.2.1 x y
  have hi₂ : p.2.lin ∈ GlobalTheory.HermLat.isomGrp (HV D) := fun x y => p.2.rep.2.2.1 x y
  have hΛ₁ : p.1.lin • p.1.lam' = p.1.lam := by
    rw [← GlobalTheory.TypeAsm.FibProof.gmap_eq_smul]; exact p.1.rep.2.2.2.1
  have hΛ₂ : p.2.lin • p.1.lam' = p.1.lam := by
    rw [hl, hl', ← GlobalTheory.TypeAsm.FibProof.gmap_eq_smul]; exact p.2.rep.2.2.2.1
  rw [← hl] at ht₂
  exact GlobalTheory.DegAsm.trip_of_terms D.host.E (VS D).V W (HV D) HW W.subtype hK D.R.rS (F0 X u) (Ft p.1) (Ft p.2) (dI D)
    N₁ N₂ (gS D) p.1.lam p.1.lam' p.1.lin p.2.lin h₁ h₂ hg he hA₁ hA₂ ht₁ ht₂ hi₁ hi₂
    (fun a => ⟨GlobalTheory.TypeAsm.FibProof.Ft_e p.1 a, GlobalTheory.TypeAsm.FibProof.Ft_e p.2 a⟩) hΛ₁ hΛ₂ hH₁ hH₂ hc

end GlobalTheory.TypeAsm.PerRow

namespace GlobalTheory.TypeAsm
open PerRow

theorem perRowC : PerRowC := by
  intro D large₂ X Y u hS W HW he Λ j' j'' δ' δ'' S hS'
  rcases S.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · simp
  obtain ⟨hK, -, -, -, -, -, -, -, -, -, -, hg2, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hS
  obtain ⟨N₀, h₀, -⟩ := termData D large₂ X Y u hS W HW he p₀.1 (hS' p₀ hp₀).1.1
  have hdata : ∀ t : GTu Y u, ∃ (N : GlobalTheory.DegCnt.NF (HV D) D.R.rS) (h : W ≃ₗ[D.host.E] W), t ∈ relSet Y u →
      AdT t N ∧ N.IsTerm (gS D) t.lam ∧ N.j = jT t ∧
      N.T = Tu D u ∧ N.Del = k2Del D (jT t) (labT t) ∧ N.Db = DbL D (jT t) (labT t) ∧ 1 ≤ N.Del ∧ 1 ≤ N.Db ∧
      1 ≤ N.gI (gS D) t.lam ∧ (N.gI (gS D) t.lam : ℝ) ≤ N.Del ∧
      GlobalTheory.DegAsm.lab (F0 X u) (Ft t) (jT t) = (fun l => star (labT t l)) ∧
      h ∈ GlobalTheory.HermLat.isomGrp HW ∧ GlobalTheory.DegAsm.IsH (F0 X u) (Ft t) W.subtype t.lin h ∧
      Module.finrank D.host.E W = D.R.k := by
    intro t
    by_cases ht : t ∈ relSet Y u
    · obtain ⟨N, h, hp⟩ := termData D large₂ X Y u hS W HW he t ht
      exact ⟨N, h, fun _ => hp⟩
    · exact ⟨N₀, h₀, fun h => absurd h ht⟩
  choose N h hNh using hdata

  have hpair : ∀ p ∈ S, p.2.lam = Λ ∧
      (GlobalTheory.DegAsm.datOf (F0 X u) (Ft p.1) W.subtype (gS D) Λ,
        GlobalTheory.DegAsm.datOf (F0 X u) (Ft p.2) W.subtype (gS D) Λ, h p.1 * (h p.2)⁻¹) ∈
        GlobalTheory.DegCnt.Trip HW (gS D) (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) D.R.rS ((N p.1).gI (gS D) Λ)
          ((N p.2).gI (gS D) Λ) ∧
      (N p.1).gI (gS D) Λ ∈ Finset.Icc 1 ⌊k2Del D j' δ'⌋₊ ∧ (N p.2).gI (gS D) Λ ∈ Finset.Icc 1 ⌊k2Del D j'' δ''⌋₊ := by
    intro p hp
    obtain ⟨hpa, hl, hj1, hj2, hd1, hd2⟩ := hS' p hp
    obtain ⟨a1, a2, -, -, a5, -, -, -, a9, a10, -, -, a13, -⟩ := hNh p.1 hpa.1
    obtain ⟨b1, b2, -, -, b5, -, -, -, b9, b10, -, -, b13, -⟩ := hNh p.2 hpa.2.1
    obtain ⟨hl2, htr⟩ := pairTrip D large₂ X Y u hS W HW he p hpa (N p.1) (N p.2) (h p.1) (h p.2) a1 b1 a2 b2 a13 b13
    rw [hl] at htr hl2 a9 a10
    rw [← hl2] at b9 b10
    refine ⟨hl2.symm, htr, Finset.mem_Icc.2 ⟨a9, Nat.le_floor ?_⟩, Finset.mem_Icc.2 ⟨b9, Nat.le_floor ?_⟩⟩
    · rw [← hj1, ← hd1, ← a5]; exact a10
    · rw [← hj2, ← hd2, ← b5]; exact b10
  refine sum_le_encard_fibres S (fun p => (N p.1).gI (gS D) Λ) (fun p => (N p.2).gI (gS D) Λ)
    (fun p => (GlobalTheory.DegAsm.datOf (F0 X u) (Ft p.1) W.subtype (gS D) Λ,
        GlobalTheory.DegAsm.datOf (F0 X u) (Ft p.2) W.subtype (gS D) Λ, h p.1 * (h p.2)⁻¹))
    (fun x y => GlobalTheory.DegCnt.Trip HW (gS D) (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) D.R.rS x y)
    (fun p => wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2))
    (fun x => GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j' δ') (DbL D j' δ') (NT D u) x)
    (fun x => GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j'' δ'') (DbL D j'' δ'') (NT D u) x) _ _ ?_
    (fun p hp => ⟨(hpair p hp).2.2.1, (hpair p hp).2.2.2, (hpair p hp).2.1⟩) ?_
  · intro p _
    have hw : 0 ≤ wRow D (X.Fu u) p.1.lam' := by unfold wRow; positivity
    have ho : ∀ t : GTu Y u, 0 ≤ omT t := fun t =>
      ((GlobalTheory.DegAsm.WeightInf.main D.host.E (VS D).V (HV D) hK D.R.rS).2 _ _ _ _).1
    exact mul_nonneg hw (mul_nonneg (ho _) (ho _))
  · intro a ha
    have key : ∀ Sf : Finset (GTu Y u × GTu Y u), (∀ q ∈ Sf, q ∈ S ∧ GlobalTheory.DegAsm.datOf (F0 X u) (Ft q.1) W.subtype (gS D) Λ =
        GlobalTheory.DegAsm.datOf (F0 X u) (Ft a.1) W.subtype (gS D) Λ ∧
        GlobalTheory.DegAsm.datOf (F0 X u) (Ft q.2) W.subtype (gS D) Λ =
        GlobalTheory.DegAsm.datOf (F0 X u) (Ft a.2) W.subtype (gS D) Λ ∧ h q.1 * (h q.2)⁻¹ = h a.1 * (h a.2)⁻¹ ∧
        (N q.1).gI (gS D) Λ = (N a.1).gI (gS D) Λ ∧ (N q.2).gI (gS D) Λ = (N a.2).gI (gS D) Λ) → a ∈ Sf →
        ∑ p ∈ Sf, wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2) ≤
          GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j' δ') (DbL D j' δ') (NT D u) ((N a.1).gI (gS D) Λ) *
          GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j'' δ'') (DbL D j'' δ'') (NT D u) ((N a.2).gI (gS D) Λ) := by
      intro Sf hmem haf
      have h1 := sum_pairs_le_classes D large₂ X Y u hS W HW he Λ h (fun t ht => (hNh t ht).2.2.2.2.2.2.2.2.2.2.2.2.1) Sf
        (fun p hp => ⟨(hS' p (hmem p hp).1).1, (hS' p (hmem p hp).1).2.1⟩)
        (fun p hp q hq => ((hmem p hp).2.2.2.1).trans ((hmem q hq).2.2.2.1).symm)
      have hA1 : ∀ t ∈ Sf.image Prod.fst, t ∈ relSet Y u ∧ t.lam = Λ ∧ jT t = j' ∧ labT t = δ' ∧ AdT t (N t) ∧
          (N t).IsTerm (gS D) Λ ∧ (N t).gI (gS D) Λ = (N a.1).gI (gS D) Λ ∧
          GlobalTheory.DegAsm.datOf (F0 X u) (Ft t) W.subtype (gS D) Λ = GlobalTheory.DegAsm.datOf (F0 X u) (Ft a.1) W.subtype (gS D) Λ := by
        intro t ht
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 ht
        obtain ⟨hqS, c1, -, -, c4, -⟩ := hmem q hq
        obtain ⟨hpa, hl, hj1, -, hd1, -⟩ := hS' q hqS
        obtain ⟨a1, a2, -⟩ := hNh q.1 hpa.1
        rw [hl] at a2
        exact ⟨hpa.1, hl, hj1, hd1, a1, a2, c4, c1⟩
      have hA2 : ∀ t ∈ Sf.image Prod.snd, t ∈ relSet Y u ∧ t.lam = Λ ∧ jT t = j'' ∧ labT t = δ'' ∧ AdT t (N t) ∧
          (N t).IsTerm (gS D) Λ ∧ (N t).gI (gS D) Λ = (N a.2).gI (gS D) Λ ∧
          GlobalTheory.DegAsm.datOf (F0 X u) (Ft t) W.subtype (gS D) Λ = GlobalTheory.DegAsm.datOf (F0 X u) (Ft a.2) W.subtype (gS D) Λ := by
        intro t ht
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 ht
        obtain ⟨hqS, -, c2, -, -, c5⟩ := hmem q hq
        obtain ⟨hpa, -, -, hj2, -, hd2⟩ := hS' q hqS
        have hl2 := (hpair q hqS).1
        obtain ⟨b1, b2, -⟩ := hNh q.2 hpa.2.1
        rw [hl2] at b2
        exact ⟨hpa.2.1, hl2, hj2, hd2, b1, b2, c5, c2⟩
      have h2 := sum_classes_le D large₂ X Y u hS W HW he Λ j' _ δ' _ N (Sf.image Prod.fst) ⟨a.1, Finset.mem_image_of_mem _ haf⟩ hA1
      have h3 := sum_classes_le D large₂ X Y u hS W HW he Λ j'' _ δ'' _ N (Sf.image Prod.snd) ⟨a.2, Finset.mem_image_of_mem _ haf⟩ hA2
      rw [Finset.image_image] at h2 h3
      have n2 : 0 ≤ ∑ b ∈ Sf.image (fun p => frCls Λ p.2), clsOm Y u Λ b :=
        Finset.sum_nonneg fun b _ => clsOm_nonneg Y u Λ hK b
      have n1 : 0 ≤ ∑ b ∈ Sf.image (fun p => frCls Λ p.1), clsOm Y u Λ b :=
        Finset.sum_nonneg fun b _ => clsOm_nonneg Y u Λ hK b
      exact h1.trans (mul_le_mul h2 h3 n2 (n1.trans h2))

    rw [Finset.filter_congr_decidable]
    refine key _ (fun q hq => ?_) (Finset.mem_filter.2 ⟨ha, rfl, rfl, rfl⟩)
    obtain ⟨hqS, he1, he2, he3⟩ := Finset.mem_filter.1 hq
    obtain ⟨c1, c2⟩ := Prod.mk.inj he1
    obtain ⟨c2, c3⟩ := Prod.mk.inj c2
    exact ⟨hqS, c1, c2, c3, he2, he3⟩

end GlobalTheory.TypeAsm
end
end

section

noncomputable section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OrbitCount

theorem relIndex_prod_prod {G G' : Type} [Group G] [Group G'] (H K : Subgroup G) (H' K' : Subgroup G') :
    (H.prod H').relIndex (K.prod K') = H.relIndex K * H'.relIndex K' := by
  unfold Subgroup.relIndex
  rw [← Subgroup.index_prod,
    ← Subgroup.index_comap_of_surjective ((H.subgroupOf K).prod (H'.subgroupOf K'))
      (f := (Subgroup.prodEquiv K K').toMonoidHom) (Subgroup.prodEquiv K K').surjective]
  congr 1

theorem card_image_eq_relIndex {Γ α : Type} [Group Γ] (P B : Subgroup Γ) (f : Γ → α)
    (hf : ∀ p ∈ P, ∀ q ∈ P, f p = f q ↔ p⁻¹ * q ∈ B) :
    Nat.card (f '' (P : Set Γ)) = B.relIndex P := by
  unfold Subgroup.relIndex Subgroup.index
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (Quotient.lift (s := QuotientGroup.leftRel (B.subgroupOf P))
      (fun p : P => (⟨f p, p, p.2, rfl⟩ : f '' (P : Set Γ))) ?_) ⟨?_, ?_⟩)
  · intro a b h
    have h' := QuotientGroup.leftRel_apply.mp h
    apply Subtype.ext
    exact (hf a a.2 b b.2).2 (by simpa [Subgroup.mem_subgroupOf] using h')
  · intro x y hxy
    induction x using Quotient.inductionOn with | h a => ?_
    induction y using Quotient.inductionOn with | h b => ?_
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    have := congrArg Subtype.val hxy
    simp only [Quotient.lift_mk] at this
    simpa [Subgroup.mem_subgroupOf] using (hf a a.2 b b.2).1 this
  · rintro ⟨_, p, hp, rfl⟩
    exact ⟨Quotient.mk _ ⟨p, hp⟩, rfl⟩

theorem lrel_refl {D : D7} {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (Λ : LV D) :
    LRel F F' Λ Λ := by
  refine ⟨1, ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).one_mem, fun a => rfl, fun a => rfl⟩, ?_⟩
  congr 1
  simp [Formalism.HermitianLatticesTheory.gmap]

end GlobalTheory.OrbitCount

namespace GlobalTheory.OrbitCount

theorem orbit_count : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (t₀ : TauC Y u u') (Λ₀ : LV D), TG F F' t₀ Λ₀ → ∀ K, K = {κ | ∃ (t : TauC Y u u') (Λ₁ : LV D), TG F F' t Λ₁ ∧ LRel F F' Λ₀ Λ₁ ∧ key t = κ} → K.Finite ∧ (∀ κ ∈ K, ∃ t : TauC Y u u', TG F F' t Λ₀ ∧ key t = κ) ∧ (∀ (t : TauC Y u u') (Λ₁ : LV D), TG F F' t Λ₁ → LRel F F' Λ₀ Λ₁ → wt t = wt t₀) ∧ (K.encard : ℝ≥0∞) * ENNReal.ofReal (wt t₀ ^ 2) = (((stabL F F' Λ₀).encard : ℝ≥0∞))⁻¹ := by
  intro D X Y u u' F F' w hw hG t₀ Λ₀ h₀ K hK
  obtain ⟨A, N, hA, hN, hNA, hNn, hiA, hcA⟩ := GlobalTheory.T.rowLattice_automorphisms_eq_adapted_mod_unipotent D X Y u u' t₀.lam t₀.mem
  obtain ⟨A', N', hA', hN', hNA', hNn', hiA', hcA'⟩ := GlobalTheory.T.rowLattice_automorphisms_eq_adapted_mod_unipotent D X Y u' u t₀.lam' t₀.mem'
  obtain ⟨B, hB, hNB, hBiff⟩ := GlobalTheory.T.exists_subgroup_unitriangular_pairs_keeping_doubleCoset D X Y u u' t₀
  have hS := GlobalTheory.T.card_stabilizer_innerDatum_rowDoubleCoset D X Y u u' F F' w hw hG t₀ Λ₀ h₀ B N N' hB hN hN'
  have mA : ∀ a, a ∈ A ↔ a ∈ Aut0 (lf D (X.Fu u)) t₀.lam := fun a => SetLike.mem_coe.symm.trans (Set.ext_iff.mp hA a)
  have mA' : ∀ a, a ∈ A' ↔ a ∈ Aut0 (lf D (X.Fu u')) t₀.lam' := fun a => SetLike.mem_coe.symm.trans (Set.ext_iff.mp hA' a)
  have mN : ∀ a, a ∈ N ↔ a ∈ NLam t₀.lam (lf D (X.Fu u)) := fun a => SetLike.mem_coe.symm.trans (Set.ext_iff.mp hN a)
  have mN' : ∀ a, a ∈ N' ↔ a ∈ NLam t₀.lam' (lf D (X.Fu u')) := fun a => SetLike.mem_coe.symm.trans (Set.ext_iff.mp hN' a)
  set P : Subgroup (GV D × GV D) := A.prod A' with hP
  have htr : ∀ p : GV D × GV D, ∃ s : TauC Y u u', p ∈ P → (s.lam = t₀.lam ∧ s.lam' = t₀.lam' ∧
      ∃ n ∈ NLam t₀.lam (lf D (X.Fu u)), ∃ n' ∈ NLam t₀.lam' (lf D (X.Fu u')), s.lin = n * (p.1 * t₀.lin * p.2⁻¹) * n') := by
    intro p
    by_cases hp : p ∈ P
    · obtain ⟨s, h1, h2, n, hn, n', hn', h3⟩ := GlobalTheory.T.exists_term_translate_by_adapted_lattice_automorphisms D X Y u u' t₀ p.1 ((mA _).1 hp.1) p.2 ((mA' _).1 hp.2)
      exact ⟨s, fun _ => ⟨h1, h2, n, hn, n', hn', h3⟩⟩
    · exact ⟨t₀, fun h => absurd h hp⟩
  choose s hs using htr
  have hTG : ∀ p ∈ P, TG F F' (s p) Λ₀ := by
    intro p hp
    obtain ⟨h1, -, n, hn, n', hn', h3⟩ := hs p hp
    exact GlobalTheory.T.baseFrameLattice_invariant_under_adapted_translate D X Y u u' F F' t₀ (s p) Λ₀ p.1 p.2 n n' h₀ ((mA _).1 hp.1) ((mA' _).1 hp.2) hn hn' h1 h3

  have hfib : ∀ p ∈ P, ∀ q ∈ P, key (s p) = key (s q) ↔ p⁻¹ * q ∈ B := by
    intro p hp q hq
    obtain ⟨hp1, hp2, n, hn, n', hn', hpl⟩ := hs p hp
    obtain ⟨hq1, hq2, m, hm, m', hm', hql⟩ := hs q hq
    rw [GlobalTheory.T.term_row_double_coset_eq_iff_isometries D X Y u u' (s p) (s q), hp1, hq1, hp2, hq2]
    simp only [true_and]
    have ep : (s p).lin = (n * p.1) * t₀.lin * (n'⁻¹ * p.2)⁻¹ := by rw [hpl]; group
    have eq : (s q).lin = (m * q.1) * t₀.lin * (m'⁻¹ * q.2)⁻¹ := by rw [hql]; group
    have hnA : n ∈ A := hNA ((mN n).2 hn)
    have hmA : m ∈ A := hNA ((mN m).2 hm)
    have hnA' : n'⁻¹ ∈ A' := A'.inv_mem (hNA' ((mN' n').2 hn'))
    have hmA' : m'⁻¹ ∈ A' := A'.inv_mem (hNA' ((mN' m').2 hm'))
    rw [ep, eq, hBiff (n * p.1) ((mA _).1 (A.mul_mem hnA hp.1)) (m * q.1) ((mA _).1 (A.mul_mem hmA hq.1))
      (n'⁻¹ * p.2) ((mA' _).1 (A'.mul_mem hnA' hp.2)) (m'⁻¹ * q.2) ((mA' _).1 (A'.mul_mem hmA' hq.2))]
    have hx : p.1⁻¹ * (n⁻¹ * m) * p.1⁻¹⁻¹ ∈ N :=
      hNn _ (A.inv_mem hp.1) _ (N.mul_mem (N.inv_mem ((mN n).2 hn)) ((mN m).2 hm))
    have hx' : p.2⁻¹ * (n' * m'⁻¹) * p.2⁻¹⁻¹ ∈ N' :=
      hNn' _ (A'.inv_mem hp.2) _ (N'.mul_mem ((mN' n').2 hn') (N'.inv_mem ((mN' m').2 hm')))
    have hmB : (p.1⁻¹ * (n⁻¹ * m) * p.1⁻¹⁻¹, p.2⁻¹ * (n' * m'⁻¹) * p.2⁻¹⁻¹) ∈ B :=
      hNB _ ((mN _).1 hx) _ ((mN' _).1 hx')
    have heq : ((n * p.1)⁻¹ * (m * q.1), (n'⁻¹ * p.2)⁻¹ * (m'⁻¹ * q.2)) =
        (p.1⁻¹ * (n⁻¹ * m) * p.1⁻¹⁻¹, p.2⁻¹ * (n' * m'⁻¹) * p.2⁻¹⁻¹) * (p⁻¹ * q) := by
      ext <;> simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv] <;> group
    rw [heq, B.mul_mem_cancel_left hmB]

  have hKim : K = (fun p => key (s p)) '' (P : Set (GV D × GV D)) := by
    rw [hK]
    ext κ
    constructor
    · rintro ⟨t, Λ₁, ht, hrel, rfl⟩
      obtain ⟨a, ha, a', ha', hkey⟩ := GlobalTheory.T.matching_translate_same_row_double_coset D X Y u u' F F' w hw hG t₀ t Λ₀ Λ₁ h₀ ht hrel
      have hp : (a, a') ∈ P := ⟨(mA a).2 ha, (mA' a').2 ha'⟩
      obtain ⟨h1, h2, n, hn, n', hn', h3⟩ := hs (a, a') hp
      exact ⟨(a, a'), hp, hkey (s (a, a')) h1 h2 ⟨n, hn, n', hn', h3⟩⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨s p, Λ₀, hTG p hp, lrel_refl F F' Λ₀, rfl⟩
  have hcardK : Nat.card K = B.relIndex P := by
    rw [hKim]; exact card_image_eq_relIndex P B _ hfib
  have hBP : B ≤ P := fun b hb => ⟨(mA _).2 ((hB b).1 hb).1, (mA' _).2 ((hB b).1 hb).2.1⟩
  have hNNB : N.prod N' ≤ B := fun b hb => by
    have := hNB b.1 ((mN _).1 hb.1) b.2 ((mN' _).1 hb.2)
    simpa using this
  have hprod : (N.prod N').relIndex B * B.relIndex P = Nat.card (autLz D (X.Fu u) t₀.lam) * Nat.card (autLz D (X.Fu u') t₀.lam') := by
    rw [Subgroup.relIndex_mul_relIndex _ _ _ hNNB hBP, hP, relIndex_prod_prod, hiA, hiA']
  set k := B.relIndex P with hk
  set m := (N.prod N').relIndex B with hm
  set c := Nat.card (autLz D (X.Fu u) t₀.lam) with hc
  set c' := Nat.card (autLz D (X.Fu u') t₀.lam') with hc'
  have hmk : 0 < m * k := by rw [hprod]; exact Nat.mul_pos hcA hcA'
  have hk0 : 0 < k := Nat.pos_of_mul_pos_left hmk
  have hm0 : 0 < m := Nat.pos_of_mul_pos_right hmk
  have hKfin : K.Finite := by
    have : 0 < Nat.card K := hcardK ▸ hk0
    exact Set.finite_coe_iff.mp (Nat.card_pos_iff.mp this).2
  have hSfin : (stabL F F' Λ₀).Finite := by
    have : 0 < Nat.card (stabL F F' Λ₀) := hS ▸ hm0
    exact Set.finite_coe_iff.mp (Nat.card_pos_iff.mp this).2
  have hKenc : K.encard = (k : ℕ∞) := by
    rw [← hKfin.cast_ncard_eq, ← Nat.card_coe_set_eq, hcardK]
  have hSenc : (stabL F F' Λ₀).encard = (m : ℕ∞) := by
    rw [← hSfin.cast_ncard_eq, ← Nat.card_coe_set_eq, hS]
  have hwt : ∀ (t : TauC Y u u'), t.lam = t₀.lam → t.lam' = t₀.lam' → wt t = wt t₀ := by
    intro t h1 h2
    simp only [wt, h1, h2]
  refine ⟨hKfin, ?_, ?_, ?_⟩
  · intro κ hκ
    rw [hKim] at hκ
    obtain ⟨p, hp, rfl⟩ := hκ
    exact ⟨s p, hTG p hp, rfl⟩
  · intro t Λ₁ ht hrel
    obtain ⟨h1, h2, -⟩ := GlobalTheory.T.terms_same_rational_inner_class_are_translates D X Y u u' F F' w hw hG t₀ t Λ₀ Λ₁ h₀ ht hrel
    exact hwt t h1 h2
  · have hw2 : wt t₀ ^ 2 = (c : ℝ)⁻¹ * (c' : ℝ)⁻¹ := by
      simp only [wt]
      rw [Real.sq_sqrt (by unfold wRow; positivity)]
      rfl
    rw [hKenc, hSenc, hw2, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_inv_of_pos (by exact_mod_cast hcA), ENNReal.ofReal_inv_of_pos (by exact_mod_cast hcA'),
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    have hcc : ((c : ℝ≥0∞))⁻¹ * ((c' : ℝ≥0∞))⁻¹ = ((m : ℝ≥0∞))⁻¹ * ((k : ℝ≥0∞))⁻¹ := by
      rw [← ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),
        ← ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
      congr 1
      exact_mod_cast hprod.symm
    simp only [ENat.toENNReal_coe]
    rw [hcc, mul_comm, mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hk0.ne') (ENNReal.natCast_ne_top _), mul_one]

end GlobalTheory.OrbitCount
end
end

section

open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.QuantumDeterminants GlobalTheory.ThA

namespace GlobalTheory

theorem bp_forms_of_gapIn_thmBpDS : GlobalTheory.GapIn.Hyp → ThmBpDS → ∀ Ch : ℝ, ∃ Cb Cg₀ : ℝ, ∀ Cg : ℝ, Cg₀ ≤ Cg → (∀ (D : D7) (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (f : B.Mat D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b : ℝ), LocOk D Ch Cg L lam0 ka b 1 → AllGaps lam0 (200 * l1 L.lam lam0) → IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec → ∀ γ : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → BpIneq D Cb L f μsec b γ) ∧ (∀ D : D7, Formalism.MainNotions.OnePlaceEstimates.TheoremBPrimePointwise D Ch Cg Cb) ∧ ∀ (D : D7) (Cu Cg' : ℝ), 200 * Cu ≤ Cg' → Formalism.MainNotions.OnePlaceEstimates.UniformityTheoremBPrime D Ch Cu Cg Cg' Cb := by
  intro hH hT Ch
  obtain ⟨C₄, G₀, hC₄, hloc⟩ := GlobalTheory.pointwiseBound_at_place_of_locBessel hT Ch
  obtain ⟨c₃, hdict⟩ := GlobalTheory.ThA.BpDict.bpIneq_of_thmBpAt
  refine ⟨max (C₄ + 1) 10, max G₀ (240 + 2 * |c₃|), fun Cg hCg => ?_⟩
  have hG₀ : G₀ ≤ Cg := (le_max_left _ _).trans hCg
  have hG₁ : 240 + 2 * |c₃| ≤ Cg := (le_max_right _ _).trans hCg
  have main : ∀ (D : D7) (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (f : B.Mat D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b : ℝ), LocOk D Ch Cg L lam0 ka b 1 → AllGaps lam0 (200 * l1 L.lam lam0) → IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec → ∀ γ : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → BpIneq D (max (C₄ + 1) 10) L f μsec b γ := by
    intro D L lam0 f μsec ka b hL hg hf hsec
    obtain ⟨U, U', p, n₀, hstd, hn₀, hB⟩ := hloc Cg hG₀ D L lam0 f μsec ka b hL hg hf hsec
    obtain ⟨hk, -, hc, hκ0, hκ, hS, -⟩ := hL
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hb, -, -, hall, hgap, -⟩ := hS
    obtain ⟨hOK, hA⟩ := bpNear_gapOK D.R.k D.R.rS hk c₃ Cg hG₁
    obtain ⟨v1, v2, -⟩ := GlobalTheory.upqRep_vocabulary_agree D.R.k D.R.rS L.Hs L.σ L.ε L.lam
    have hone : (1 : B.Mat D.R.k D.R.rS) ∈ UH (Hpk D.R.k D.R.rS) := by simp [UH]
    have hE := GlobalTheory.T.discreteSeriesCoefficient_smooth_decay_capelliEigen_largeGap hH D.R.k D.R.rS L.ε L.lam _ ⟨L.Hs, L.σ⟩ L.Wp L.Wq f ⟨L.hlam, v1.1 L.hσ⟩
      (bpNear_gapAtLeast _ _ _ _ hgap hg) hOK (by
        obtain ⟨P, Q, hQ, hP, he⟩ := hf
        exact ⟨1, hone, 1, hone, P, Q, fun w => (v2 _).1 (hQ w), fun x => (v2 _).1 (hP x), fun g => by
          simpa using he g⟩)
    have hr : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
    have hm : ((2 * D.R.rS + 2 : ℕ) : ℝ) = 2 * ((D.R.rS : ℝ) + 1) := by push_cast; ring
    have hb3 : 3 ≤ b := by
      have h1 := hall ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp)
      have h2 := abs_sub (lam0 ⟨0, by omega⟩) (lam0 ⟨1, by omega⟩)
      have h3 : (1 : ℝ) ≤ ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 := one_le_pow₀ (by rw [hm]; linarith)
      have h4 : 240 * 1 ≤ Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 :=
        mul_le_mul (by linarith [abs_nonneg c₃]) h3 (by norm_num) (by linarith [abs_nonneg c₃])
      linarith [hb ⟨0, by omega⟩, hb ⟨1, by omega⟩]
    refine hdict D L μsec U U' p f _ b C₄ _ n₀ _ hstd (hc.trans Formalism.MainNotions.OnePlaceEstimates.cOfDpsi_one) hκ0.ne' hκ hA (hE.2.1 1)
      hb3 (le_max_left _ _) ?_ hB
    have h1 : (n₀ : ℝ) ≤ 30 * ((D.R.rS : ℝ) + 1) ^ 2 + 6 := by exact_mod_cast hn₀
    have h2 : 10 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 ≤ max (C₄ + 1) 10 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    refine le_trans ?_ h2
    rw [hm]; push_cast; nlinarith
  refine ⟨main, ?_, ?_⟩
  · intro D L f μsec ka b hL hf hsec
    exact main D L L.lam f μsec ka b hL (fun s s' _ => by simp [l1]) hf hsec
  · intro D Cu Cg' hCu L lam0 f μsec ka b hL hR hf hsec _
    refine main D L lam0 f μsec ka b hL (fun s s' hs => le_trans ?_ (hR.1 s s' hs)) hf hsec
    have h1 := hR.2
    have h2 : 200 * Cu * ((D.R.k : ℝ) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) ≤
        Cg' * ((D.R.k : ℝ) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) := mul_le_mul_of_nonneg_right hCu (by positivity)
    nlinarith

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

theorem _root_.GlobalTheory.T.levelPrimes_size_bounds_columnDimension : Formalism.HermitianLatticesTheory.SiegelMassRatio → Formalism.L2.SG.Pf.SzHypFD.DsigHC → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), Ties D → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → 40 ≤ Cl → Cu * large₂.sc.L ≤ (D.R.m : ℝ) - 1 → C0 * Real.exp 8 ≤ D.R.k → LocalBesselAndTopKernel.FamilyMidVolume D → ∀ u, large₂.sc.b ^ ((1 / 2 : ℝ) * (D.R.m : ℝ)) ≤ Tr D u ∧ Tr D u ≤ large₂.sc.b ^ ((4 * Cg + 13) * (D.R.m : ℝ)) := by
  first | exact @GlobalTheory.levelPrime_size | exact GlobalTheory.levelPrime_size | (intros; apply GlobalTheory.levelPrime_size <;> assumption)
end
