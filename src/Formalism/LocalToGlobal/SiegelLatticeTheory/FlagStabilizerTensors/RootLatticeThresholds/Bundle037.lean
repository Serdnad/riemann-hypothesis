module

public import Formalism.HermitianCurvature.Bundle008
public import Formalism.SharpRestriction.CuspSpanNormBounds.BigCellDensity
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle036
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActRRep
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SubMemOfIndQ
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.BesselSplit
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuBesselLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.InstLocallyCompactSpace
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle038
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.XLeSpanEXLam
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpFibreConstOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle030
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.Isometry
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf

@[expose] public section

section

noncomputable section

namespace Formalism.L2.SG.Pf.BesselExpansion

open MeasureTheory Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.BesselShellMomentBounds Formalism.MainNotions.BigCellDensity
open scoped InnerProductSpace

def parOfL {k r : ℕ} (L : LocBessel k r) (u u' : ℕ → ℝ) : Formalism.FourierDecayAlt.M.Par :=
  ⟨k, r, Tz k r L.z, Tz k r L.z', u, u'⟩

def PlTie {k r : ℕ} (L : LocBessel k r) {u u' : ℕ → ℝ} (p : Formalism.FourierDecayAlt.KB.Pl (parOfL L u u') L.Wp L.Wq) : Prop :=
  p.T.base.z = L.z ∧ p.T.base.z' = L.z' ∧ p.T.base.π = L.π ∧ p.T.base.π' = L.π' ∧ p.T.base.μW = L.μW ∧
    p.T.base.μN = L.μN ∧ p.T.base.μW' = L.μW'

def WeightTie : Prop :=
  ∀ (k r : ℕ) (T T' : ℝ) (p : Point ℂ (r + 1)), 1 ≤ k →
    ptWeight k r T T' p = Formalism.FourierDecayAlt.TBB.nPt k r (T * T') (p.1.map Prod.swap)

def EnergyTie : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (f : Mx k r → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (u u' : ℕ → ℝ)
    (p : Formalism.FourierDecayAlt.KB.Pl (parOfL L u u') L.Wp L.Wq), 1 ≤ k → L.c = cStd → 0 < L.κN → L.κN ≠ ⊤ → PlTie L p →
    IsKFinCoefH L.σ f → Formalism.FourierDecayAlt.B.InCC (A0 k r) 1 f → IsSection k r L.z L.z' μsec →
    Formalism.FourierDecayAlt.TBB.jN2 p f ≤ ENNReal.ofReal (Real.pi ^ (2 * (2 * r + 2) ^ 2)) * jNorm2 L f μsec

def CoefCC1 (Cgc : ℝ) : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (f : Mx k r → (L.Wq →L[ℂ] L.Wp)), 1 ≤ k → IsKFinCoefH L.σ f →
    GapAtLeast L.ε L.lam (Cgc * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) →
    Formalism.FourierDecayAlt.B.InCC (A0 k r) 1 f

theorem tieTopXk (k r : ℕ) (hk : 1 ≤ k) (L : LocBessel k r) (Ds : Formalism.FourierDecayAlt.B.RealPlaceData k r L.Wp L.Wq)
    (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : Formalism.FourierDecayAlt.B.Mat k r) :
    L.c = cStd → 0 < L.κN → L.κN ≠ ⊤ → Ds.z = L.z → Ds.z' = L.z' → Ds.π = L.π → Ds.π' = L.π' →
    Ds.μW = L.μW → Ds.μN = L.μN → Ds.μW' = L.μW' → Formalism.FourierDecayAlt.D.IsBaseFrame Ds ν' m₀ →
      ∀ (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1)), IsKFinCoefH L.σ F →
        Formalism.FourierDecayAlt.B.InCC (A0 k r) 1 F →
        0 < Gpt (Tz k r L.z) (Tz k r L.z') γ → (∃ g, IsPtRep L γ g ∧ IsRelStab L g) →
        orbSq L F γ = ENNReal.ofReal (Real.pi ^ (2 * Formalism.MainNotions.BigCellDensity.pc r (γ.1.map Prod.snd)) *
          (Formalism.FourierDecayAlt.B.hsInner (Formalism.FourierDecayAlt.D.vecV Ds ν' m₀ F (γ.1.map Prod.swap))
            (Formalism.FourierDecayAlt.D.vecV Ds ν' m₀ F (γ.1.map Prod.swap))).re) := by
  obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
  exact topLevelBesselHypothesis k0 r L Ds ν' m₀

theorem pc_le (r : ℕ) (s : List ℕ) : Formalism.MainNotions.BigCellDensity.pc r s ≤ (r + 1) ^ 2 := by
  unfold Formalism.MainNotions.BigCellDensity.pc
  refine (Finset.card_filter_le _ _).trans ?_
  simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, sq]

theorem exists_relrep {k r : ℕ} (L : LocBessel k r) (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1))
    (h : orbSq L F γ ≠ 0) : ∃ g, IsPtRep L γ g ∧ IsRelStab L g := by
  by_contra hne
  apply h
  unfold orbSq
  refine le_antisymm ?_ bot_le
  refine iSup_le fun g => iSup_le fun μR => iSup_le fun ν => iSup_le fun hg => ?_
  exact (hne ⟨g, hg.1, hg.2.1⟩).elim

theorem ew_top {P : Formalism.FourierDecayAlt.M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : Formalism.FourierDecayAlt.KB.Pl P Wp Wq) (F : Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (γ : Formalism.FourierDecayAlt.C.LPt)
    (hγ : Formalism.FourierDecayAlt.D.IsLocPt γ (P.r + 1)) (hn : 0 ≤ Formalism.FourierDecayAlt.TBB.nPt P.k P.r (Formalism.FourierDecayAlt.TBB.TTp p) γ) :
    Formalism.FourierDecayAlt.TBB.Ew p (fun _ => 1) F (P.r + 1) [] γ =
      Formalism.FourierDecayAlt.TBB.nPt P.k P.r (Formalism.FourierDecayAlt.TBB.TTp p) γ *
        (Formalism.FourierDecayAlt.B.hsInner (Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ F γ) (Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ F γ)).re := by
  unfold Formalism.FourierDecayAlt.TBB.Ew Formalism.FourierDecayAlt.TBB.NP Formalism.FourierDecayAlt.KB.Pl.RR Formalism.FourierDecayAlt.D.RRplace
  rw [dite_eq_left ⟨hγ, hγ⟩, dite_eq_right (by omega), ite_eq_left rfl, ite_eq_left rfl]
  simp only [Formalism.FourierDecayAlt.TBB.normC, List.map_nil, List.prod_nil, div_one, Real.mul_self_sqrt hn,
    Complex.re_ofReal_mul]

theorem pointWeight_eq_blockWeight (k r : ℕ) (T T' GG : ℝ) (hk : 1 ≤ k) : ∀ (bs : List (ℂ × ℕ)) (a : ℕ),
    (∀ b ∈ bs, 1 ≤ b.2) → a + (bs.map Prod.snd).sum = r + 1 →
    (∀ x, bs.getLast? = some x → GG = Complex.normSq x.1 - T * T') →
    ptWeightFrom k r T T' a bs = Formalism.FourierDecayAlt.C.nAux k r GG (fun _ _ => 1) (a + 1) (bs.map Prod.swap)
  | [], a, _, _, _ => by simp [ptWeightFrom, Formalism.FourierDecayAlt.C.nAux]
  | (t, s) :: bs, a, hs, hsum, hlast => by
    have hs1 : 1 ≤ s := hs (t, s) (by simp)
    have hsum' : a + (s + (bs.map Prod.snd).sum) = r + 1 := by simpa using hsum
    have ih := pointWeight_eq_blockWeight k r T T' GG hk bs (a + s) (fun b hb => hs b (by simp [hb])) (by omega)
      (fun x hx => hlast x (by rw [List.getLast?_cons, hx]; rfl))
    simp only [ptWeightFrom, List.map_cons, Prod.swap_prod_mk, Formalism.FourierDecayAlt.C.nAux]
    rw [show a + 1 + s = a + s + 1 by omega, ← ih]
    congr 1
    have hindex : a + s + 1 - 1 = a + s := by omega
    have hcond : (a + s = r + 1 ∧ s = 1) ↔ (s = 1 ∧ a + 1 = r + 1) := by omega
    simp only [hindex, hcond]
    by_cases hc : s = 1 ∧ a + 1 = r + 1
    · simp only [ite_eq_left hc]
      have hbs : bs = [] := by
        cases bs with
        | nil => rfl
        | cons b bs' =>
          have := hs b (by simp)
          simp only [List.map_cons, List.sum_cons] at hsum'
          omega
      subst hbs
      rw [hlast (t, s) (by simp)]
    · simp only [ite_eq_right hc, one_mul]
      have hle : a + s ≤ r + 1 := by omega
      have hexp : (2 * (s : ℤ) * (Formalism.FourierDecayAlt.C.Mlev k r (a + s) + s - 3)) =
          ((2 * s * (Ml k r (a + s) + s - 3) : ℕ) : ℤ) := by
        unfold Formalism.FourierDecayAlt.C.Mlev Ml
        have h3 : 3 ≤ 2 * (r + 1 - (a + s)) + k + 1 + s := by omega
        push_cast [h3, Nat.sub_add_cancel hle]
        have e2 : ((r + 1 - (a + s) : ℕ) : ℤ) = (r : ℤ) + 1 - ((a + s : ℕ) : ℤ) := by omega
        rw [e2]
        push_cast
        ring
      rw [hexp, zpow_natCast]

theorem weightTie : WeightTie := by
  intro k r T T' p hk
  unfold ptWeight Formalism.FourierDecayAlt.TBB.nPt
  refine pointWeight_eq_blockWeight k r T T' _ hk p.1 0 (fun b hb => (p.2.1 b hb).2)
    (by rw [p.2.2, Nat.zero_add]) ?_
  intro x hx
  simp [Formalism.FourierDecayAlt.D.ptGG, Formalism.FourierDecayAlt.D.ptLast, List.getLast?_map, hx]

end Formalism.L2.SG.Pf.BesselExpansion
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.Pf.FibreEq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X} {u u' : D.what₂.Word}

theorem partner (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u' Y.hK) (hIR : Formalism.L2.SG.Pf.SatGramRep.IotaRepC)
    {l₁ l₂ s₁ : _root_.Formalism.L2.SG.PackageTie2.TT Y u u'} (hrow : rowOf Y.TR (Y.cs u) (Y.cs u') l₁ = rowOf Y.TR (Y.cs u) (Y.cs u') l₂)
    (h : l₁.toTerm = s₁.toTerm) :
    ∃ s₂ : _root_.Formalism.L2.SG.PackageTie2.TT Y u u', s₂.toTerm = l₂.toTerm ∧
      rowOf Y.TR (Y.cs u) (Y.cs u') s₁ = rowOf Y.TR (Y.cs u) (Y.cs u') s₂ := by
  obtain ⟨γ, rfl⟩ := Formalism.L2.SG.Pf.KernelOfEmbedding.fib_gam hN h
  refine ⟨Formalism.L2.SG.Pf.KernelOfEmbedding.act Y ⟨l₁.lam', l₁.mem'⟩ γ l₂, Formalism.L2.SG.Pf.KernelOfEmbedding.toTerm_act _ _ _, ?_⟩
  have hl := Formalism.L2.SG.Pf.KernelOfEmbedding.lam_eq_of_row hrow
  have i1 := Formalism.L2.SG.Pf.KernelOfEmbedding.iota_act hIR ⟨l₁.lam', l₁.mem'⟩ γ l₁ rfl
  have i2 := Formalism.L2.SG.Pf.KernelOfEmbedding.iota_act hIR ⟨l₁.lam', l₁.mem'⟩ γ l₂ hl.2.symm
  have hι : iotaOf Y.TR (Y.cs u) (Y.cs u') l₁ = iotaOf Y.TR (Y.cs u) (Y.cs u') l₂ :=
    congrArg (fun r => r.2.2) hrow
  unfold rowOf
  simp only [Prod.mk.injEq, Subtype.mk.injEq]
  exact ⟨hl.1, hl.2, by rw [i1, i2, hι]⟩

theorem fibreCountEq_of (hF : FinX Y) (hN : ∀ u' : D.what₂.Word, Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u' Y.hK)
    (hIR : Formalism.L2.SG.Pf.SatGramRep.IotaRepC) (hRF : Formalism.L2.SG.Pf.FibreCounting.RowFree Y) :
    Formalism.L2.SG.Pf.KernelOfEmbedding.FibreCountEq hF := by
  intro u u' q
  let _ := hF.fibFT q.1.1
  let _ := hF.fibFT q.1.2
  obtain ⟨l₁, l₂, hrow⟩ := q.2
  have hinner : ∀ r₁ : fib Y q.1.1,
      ∑ r₂ : fib Y q.1.2, (if Formalism.L2.SG.Pf.KernelOfEmbedding.row Y r₁.1 = Formalism.L2.SG.Pf.KernelOfEmbedding.row Y r₂.1 then
        Formalism.MainNotions.S.wRow D (X.Fu u') r₁.1.lam' else 0) = Formalism.MainNotions.S.wRow D (X.Fu u') r₁.1.lam' := by
    intro r₁
    obtain ⟨s₂, hs₂t, hs₂r⟩ := partner (hN u') hIR hrow (l₁.2.trans r₁.2.symm)
    have hs₂ : s₂.toTerm = q.1.2 := hs₂t.trans l₂.2
    refine (Finset.sum_eq_single (s := (Finset.univ : Finset (fib Y q.1.2))) (show fib Y q.1.2 from ⟨s₂, hs₂⟩)
      (fun b _ hb => ?_) (fun hb => absurd (Finset.mem_univ _) hb)).trans (if_pos hs₂r)
    refine if_neg (fun hrb => hb (Subtype.ext ?_))
    exact hRF u u' b.1 s₂ (b.2.trans hs₂.symm) (hrb.symm.trans hs₂r)
  have hlam : ∀ r₁ : fib Y q.1.1, r₁.1.lam' = l₁.1.lam' := fun r₁ =>
    Formalism.L2.SG.Pf.FibreCounting.lam'_eq (r₁.2.trans l₁.2.symm)
  have hsum : ∑ r₁ : fib Y q.1.1, ∑ r₂ : fib Y q.1.2, (if Formalism.L2.SG.Pf.KernelOfEmbedding.row Y r₁.1 = Formalism.L2.SG.Pf.KernelOfEmbedding.row Y r₂.1
      then Formalism.MainNotions.S.wRow D (X.Fu u') r₁.1.lam' else 0) =
      (Fintype.card (fib Y q.1.1) : ℝ) * Formalism.MainNotions.S.wRow D (X.Fu u') l₁.1.lam' := by
    rw [Finset.sum_congr rfl (fun r₁ _ => (hinner r₁).trans (by rw [hlam r₁])), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  rw [Fintype.sum_prod_type]
  refine hsum.trans ?_
  obtain ⟨f, hf⟩ := Formalism.L2.SG.Pf.FibreCounting.fib_bij (hN u') l₁.1
  have hcard : Fintype.card (fib Y q.1.1) = Nat.card ↥(autLz D (X.Fu u') l₁.1.lam') := by
    rw [← Nat.card_eq_fintype_card]
    have e1 : fib Y q.1.1 ≃ {s : _root_.Formalism.L2.SG.PackageTie2.TT Y u u' // s.toTerm = l₁.1.toTerm} :=
      Equiv.subtypeEquivRight (fun s => by rw [l₁.2])
    exact (Nat.card_congr e1).trans (Nat.card_congr (Equiv.ofBijective f hf))
  have hpos : 0 < Fintype.card (fib Y q.1.1) := Fintype.card_pos_iff.2 ⟨l₁⟩
  unfold Formalism.MainNotions.S.wRow
  rw [← hcard]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 hpos.ne')

theorem fibreCountEq_of' (hF : FinX Y) (hIR : Formalism.L2.SG.Pf.SatGramRep.IotaRepC) (hRF : Formalism.L2.SG.Pf.FibreCounting.RowFree Y) :
    Formalism.L2.SG.Pf.KernelOfEmbedding.FibreCountEq hF :=
  fibreCountEq_of hF (fun u' => Formalism.L2.SG.Closed.NeatKu_holds X u' Y.hK) hIR hRF

theorem FibreCountEq_holds (hF : FinX Y) : Formalism.L2.SG.Pf.KernelOfEmbedding.FibreCountEq hF :=
  fibreCountEq_of' hF Formalism.L2.SG.Pf.iotaRepC_holds
    (Formalism.L2.SG.Pf.Act.rowFree_of (fun u' => Formalism.L2.SG.Closed.NeatKu_holds X u' Y.hK) Formalism.L2.SG.Pf.iotaRepC_holds)

end Formalism.L2.SG.Pf.FibreEq
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.FibreCounting

theorem LiftMassC_holds {D : D7} (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) :
    Formalism.L2.SG.Pf.RowForm.LiftMassC X Y u u' :=
  liftMassC_of (Formalism.L2.SG.Closed.NeatKu_holds X u' Y.hK)

end Formalism.L2.SG.Pf.FibreCounting
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open scoped InnerProductSpace ENNReal
open Matrix

namespace Formalism.L2.SG.Pf.LocF

section Easy

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem w_smooth (C : Choice X θ) (τ : D.what₂.Tau) :
    X.B.w (vOf X τ) ∈ smoothVecs (k := D.R.k) (r := D.R.rS) (sigB X (C.Q τ) (C.Qi τ) τ) := by
  have hds := Formalism.L2.SG.Pf.dsTr C τ
  obtain ⟨hrep, hiso⟩ := Formalism.L2.SG.Pf.WuBL.sigB_rep C τ
  obtain ⟨P, hP, hmem⟩ := C.y_low τ
  have hy := C.y_mem τ
  have hw1 : ‖X.B.w (vOf X τ)‖ = 1 := (X.low (vOf X τ)).1
  have hlow : IsLowUnitH D.R.k D.R.rS (epsSH D.R) (lamD D τ) (sigB X (C.Q τ) (C.Qi τ) τ)
      (sigB X (C.Q τ) (C.Qi τ) τ (C.y τ) (X.B.w (vOf X τ))) := ⟨P, hP, by rw [hiso _ hy, hw1], hmem⟩
  have hv0 := Formalism.L2.SG.Pf.WuDec.lowSmoothSK hds hlow
  have hyi : (C.y τ)⁻¹ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := WlocSk.HM.uh_inv hy
  have hsm := Formalism.L2.SG.BesselSplit.smooth_translate_ds hds hv0 hyi
  have hinvy : (C.y τ)⁻¹ * C.y τ = 1 := Matrix.nonsing_inv_mul _ (WlocSk.HM.isUnit_of_uh hy)
  have e : sigB X (C.Q τ) (C.Qi τ) τ (C.y τ)⁻¹ (sigB X (C.Q τ) (C.Qi τ) τ (C.y τ) (X.B.w (vOf X τ))) =
      X.B.w (vOf X τ) := by
    rw [← ContinuousLinearMap.comp_apply, ← hrep.2 _ hyi _ hy, hinvy, hrep.1]
    rfl
  rw [e] at hsm
  exact hsm

theorem muS_haar (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ)) (muS (C.muW u τ) (muNB D θ)) := by
  have hθ := Formalism.L2.SG.Pf.WuBL.theta_pos C u τ
  obtain ⟨hz, hTz⟩ := zTr C u τ
  have hT : 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by rw [hTz]; exact Tr_pos D u
  exact isHaarOn_muS hz hT (C.muW_haar u τ) (C.muW_one u τ) (kapN_ne_zero D hθ) (kapN_ne_top D θ)

end Easy

section Clauses

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

def ContClause (C : Choice X θ) : Prop :=
  ∀ u τ, ContinuousOn (wT C u τ) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS))

def EquivClause (C : Choice X θ) : Prop :=
  ∀ u τ, IsSPsiEquiv (zB X (C.Qi τ) u τ) (psiS D (zB X (C.Qi τ) u τ)) (piB X (C.Q τ) (C.Qi τ) u τ) (wT C u τ)

def ReprodClause (C : Choice X θ) : Prop :=
  ∀ u τ, ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS),
    MeasureTheory.Integrable (fun g : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      eFun (muGB X (C.Q τ) (C.Qi τ) τ) (sigB X (C.Q τ) (C.Qi τ) τ) (X.B.w (vOf X τ)) (Matrix.of g) •
        wT C u τ (x * Matrix.of g)) (muGB X (C.Q τ) (C.Qi τ) τ) ∧
    rconv (muGB X (C.Q τ) (C.Qi τ) τ) (eFun (muGB X (C.Q τ) (C.Qi τ) τ) (sigB X (C.Q τ) (C.Qi τ) τ)
      (X.B.w (vOf X τ))) (wT C u τ) x = wT C u τ x

def L2ChoiceCondition (C : Choice X θ) : Prop :=
  ∀ u τ, l2SG (C.nuS u τ) (wT C u τ) ≠ 0 ∧ l2SG (C.nuS u τ) (wT C u τ) < ⊤

def EquivAll : Prop := ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ), EquivClause C

def L2ConditionAllChoices : Prop :=
  ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (θ : ℝ) (C : Choice X θ), L2ChoiceCondition C

def ContAll : Prop := ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ), ContClause C

def ReprodAll : Prop :=
  ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (θ : ℝ) (C : Choice X θ), ReprodClause C

theorem locFactor_of_clauses (C : Choice X θ) (hC : ContClause C) (hE : EquivClause C) (hR : ReprodClause C)
    (hL : L2ChoiceCondition C) : LocFactor C :=
  fun u τ => ⟨w_smooth C τ, (X.low (vOf X τ)).1, muS_haar C u τ, hC u τ, hE u τ, hR u τ, (hL u τ).1, (hL u τ).2⟩

theorem locFactor_of (hCA : ContAll) (hEA : EquivAll) (hRA : ReprodAll) (hLA : L2ConditionAllChoices)
    (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (C : Choice X θ) : LocFactor C :=
  locFactor_of_clauses C (hCA D X θ C) (hEA D X θ C) (hRA D hG X θ C) (hLA D hG X θ C)

end Clauses

end Formalism.L2.SG.Pf.LocF
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.FibreCounting

theorem FibreCount_holds {D : D7} {X : HidaSetting D} (Y : Full X) : Formalism.L2.SG.LoopTieOf.FibreCount Y :=
  fibreCount_of (Formalism.L2.SG.Pf.Act.rowFree_of (fun u' => Formalism.L2.SG.Closed.NeatKu_holds X u' Y.hK)
    Formalism.L2.SG.Pf.iotaRepC_holds)

end Formalism.L2.SG.Pf.FibreCounting
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.FibreCounting

theorem AmpFibreConst_holds {D : D7} {X : HidaSetting D} (Y : Full X) : Formalism.L2.SG.LoopTieOf.AmpFibreConst Y :=
  ampFibreConst_of Formalism.L2.SG.Pf.ratPt_holds Formalism.L2.SG.Closed.ChiTrivialC_holds Y

end Formalism.L2.SG.Pf.FibreCounting
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf

namespace Formalism.L2.SG.Pf.KernelOfEmbedding

theorem AmpCov_holds {D : D7} {X : HidaSetting D} (Y : Formalism.L2.SG.Full.Full X) : AmpCov Y :=
  ampCov_of Formalism.L2.SG.Pf.ratPt_holds Formalism.L2.SG.Closed.ChiTrivialC_holds Y

variable {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X} {hF : FinX Y} (W : WittDat X)
  (hI : SIso D.s (_root_.Formalism.L2.SG.PackageTie2.sOf hF))

end Formalism.L2.SG.Pf.KernelOfEmbedding
end
end

section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants
open scoped ENNReal

namespace Formalism.L2.SG.unitMultiplierModel

open Formalism.MainNotions.BigCellDensity Formalism.FourierDecayAlt.P.Dx2.Rad Formalism.L2.SG.monomialWeightModel

variable {r : ℕ} (pN : Formalism.MainNotions.S.Point ℂ (r + 1))

local notation "W" => wPt pN

theorem mul_unit_mp (c : ℂ) (h : ‖c‖ = 1) : MeasurePreserving (fun z : ℂ => c * z) volume volume := by
  have hc : c ∈ Submonoid.unitSphere ℂ := by simp [Submonoid.unitSphere, h]
  have key := (rotation (⟨c, hc⟩ : Circle)).measurePreserving
  have e : (fun z : ℂ => c * z) = rotation (⟨c, hc⟩ : Circle) := by
    funext z; rfl
  rw [e]
  exact key

variable (d : Fin (r + 1) → ℂ)

theorem Rm_mp (hd : ∀ a, d a ≠ 0) (hdm : ∀ q : Formalism.FourierDecayAlt.C2.Lstidx W, ‖d (W q.1.1)‖ = ‖d (W q.1.2)‖) :
    MeasurePreserving (Rm pN d) volume volume := by
  have hsw : Function.Involutive (sw pN) := by
    intro q
    exact Subtype.ext (Prod.ext (wPt_invol pN q.1.1) (wPt_invol pN q.1.2))
  let e : Formalism.FourierDecayAlt.C2.Lstidx W ≃ Formalism.FourierDecayAlt.C2.Lstidx W :=
    ⟨sw pN, sw pN, hsw, hsw⟩
  have hG := volume_measurePreserving_piCongrLeft (fun _ : Formalism.FourierDecayAlt.C2.Lstidx W => ℂ) e.symm
  have h : ∀ q : Formalism.FourierDecayAlt.C2.Lstidx W,
      MeasurePreserving (fun z : ℂ => d (W q.1.1) / d (W q.1.2) * star z) volume volume := by
    intro q
    have hu : ‖d (W q.1.1) / d (W q.1.2)‖ = 1 := by
      rw [norm_div, hdm q, div_self]
      exact norm_ne_zero_iff.mpr (hd _)
    exact (mul_unit_mp _ hu).comp Complex.conjLIE.measurePreserving
  have hF := volume_preserving_pi h
  have heq : Rm pN d = (fun (a : Formalism.FourierDecayAlt.C2.Lstidx W → ℂ) (i : Formalism.FourierDecayAlt.C2.Lstidx W) =>
      d (W i.1.1) / d (W i.1.2) * star (a i)) ∘
      (MeasurableEquiv.piCongrLeft (fun _ : Formalism.FourierDecayAlt.C2.Lstidx W => ℂ) e.symm) := by
    funext x q
    have hq := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℂ) e.symm x (e q)
    rw [Equiv.symm_apply_apply] at hq
    change _ = x (sw pN q) at hq
    simp only [Rm, Function.comp_apply, hq]
  rw [heq]
  exact hF.comp hG

end Formalism.L2.SG.unitMultiplierModel

end
end

section

namespace Formalism.L2.SG.Pf.KernelOfEmbedding

theorem IotaKer_holds : Formalism.L2.SG.Pf.FinXP.IotaKer := by
  intro D X Y u u' s₁ s₂ t₁ t₂ n₁ n₂ m₁ m₂ c₁ c₂
  exact iotaKer_core (Formalism.L2.SG.Closed.NeatKu_holds X u' Y.hK) Formalism.L2.SG.Pf.iotaRepC_holds s₁ s₂ t₁ t₂ n₁ n₂ m₁ m₂ c₁ c₂

end Formalism.L2.SG.Pf.KernelOfEmbedding
end
