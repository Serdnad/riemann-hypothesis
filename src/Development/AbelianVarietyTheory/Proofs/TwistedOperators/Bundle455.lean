module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1999
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1376
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle318
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.SharpRestriction.Divisibility.JetPolynomialLogs.AnnihilatorMulRelativeDifferent
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle421
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.RowEx

section Mono

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil}
  {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} {S : GridChoice W Set.univ}

theorem charsIn_mono (h : CharsIn G σ) (hσ : Set.range σ ⊆ Set.range σ') : CharsIn G σ' :=
  ⟨fun j w x => hσ (h.mu0 j w x), fun t w x => hσ (h.xi t w x),
    fun i a b w x => hσ (h.chi i a b w x), fun v hv => hσ (h.eta v hv), fun v hv => hσ (h.chiPsi v hv),
    fun v hv => hσ (h.del v hv), fun v hv => hσ (h.del' v hv)⟩

theorem rootCl_mono (h : RootCl σ S) (hσ : Set.range σ ⊆ Set.range σ') : RootCl σ' S :=
  ⟨fun z hz => hσ (h.1 z hz), fun t w hw z hz => hσ (h.2.1 t w hw z hz), fun w hw => hσ (h.2.2 w hw)⟩

theorem phaseCl_mono (h : PhaseCl σ S) (hσ : Set.range σ ⊆ Set.range σ') : PhaseCl σ' S :=
  fun t Φ β hβ w x y e a b => hσ (h t Φ β hβ w x y e a b)

theorem jetCl_mono (h : JetCl σ S) (hσ : Set.range σ ⊆ Set.range σ') : JetCl σ' S :=
  fun t Φ β hβ τ hτ d hd c => ⟨fun j a b => hσ ((h t Φ β hβ τ hτ d hd c).1 j a b),
    fun i a b => hσ ((h t Φ β hβ τ hτ d hd c).2 i a b)⟩

theorem lRatios_mono {μ₀ : T} (h : ∀ i j, LRatiosIn G σ μ₀ i j) (hσ : Set.range σ ⊆ Set.range σ') :
    ∀ i j, LRatiosIn G σ' μ₀ i j :=
  fun i j t Λ Λ₀ a b s c d e => hσ (h i j t Λ Λ₀ a b s c d e)

theorem botCl_mono (h : BotCl W σ) (hσ : Set.range σ ⊆ Set.range σ') : BotCl W σ' := by
  intro i j
  obtain ⟨A, A', WW, X, h1, Ω, Ω', h2, h3, H⟩ := h i j
  exact ⟨A, A', WW, X, h1, Ω, Ω', h2, h3, fun t g hg =>
    ⟨fun k hk => hσ ((H t g hg).1 k hk), fun k hk => hσ ((H t g hg).2 k hk)⟩⟩

end Mono

theorem range_algebraMap_mono {M M' : IntermediateField ℚ ℂ} (h : M ≤ M') :
    Set.range (algebraMap M ℂ) ⊆ Set.range (algebraMap M' ℂ) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨x.1, h x.2⟩, rfl⟩

theorem InNF.and {Q Q' : ∀ M : IntermediateField ℚ ℂ, (M →+* ℂ) → Prop}
    (hQ : ∀ M M' : IntermediateField ℚ ℂ, M ≤ M' → Q M (algebraMap M ℂ) → Q M' (algebraMap M' ℂ))
    (hQ' : ∀ M M' : IntermediateField ℚ ℂ, M ≤ M' → Q' M (algebraMap M ℂ) → Q' M' (algebraMap M' ℂ))
    (h : InNF Q) (h' : InNF Q') : InNF fun M σ => Q M σ ∧ Q' M σ := by
  obtain ⟨M, hM, hq⟩ := h
  obtain ⟨M', hM', hq'⟩ := h'
  exact ⟨M ⊔ M', IntermediateField.finiteDimensional_sup M M', hQ _ _ le_sup_left hq, hQ' _ _ le_sup_right hq'⟩

theorem nfAll_of : NFChars → NFRoot → NFPhase → NFJet → NFRatio → NFBot → NFAll := by
  intro h1 h2 h3 h4 h5 h6
  obtain ⟨CF0, H⟩ := Big.and h1 (Big.and h2 (Big.and h3 (Big.and h4 (Big.and h5 h6))))
  refine ⟨CF0, fun ε CF hC => ?_⟩
  obtain ⟨x₀, H⟩ := H ε CF hC
  refine ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi ha => ?_⟩
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := H D large₂ e hx Γ Pl0 T A Ks R F s ch hi ha
  have k := InNF.and (fun M M' h q => charsIn_mono q (range_algebraMap_mono h))
    (fun M M' h q => rootCl_mono q (range_algebraMap_mono h)) c1 c2
  have k := InNF.and (fun M M' h q => ⟨charsIn_mono q.1 (range_algebraMap_mono h), rootCl_mono q.2 (range_algebraMap_mono h)⟩)
    (fun M M' h q => phaseCl_mono q (range_algebraMap_mono h)) k c3
  have k := InNF.and (fun M M' h q => ⟨⟨charsIn_mono q.1.1 (range_algebraMap_mono h), rootCl_mono q.1.2 (range_algebraMap_mono h)⟩,
      phaseCl_mono q.2 (range_algebraMap_mono h)⟩)
    (fun M M' h q => jetCl_mono q (range_algebraMap_mono h)) k c4
  have k := InNF.and (fun M M' h q => ⟨⟨⟨charsIn_mono q.1.1.1 (range_algebraMap_mono h),
      rootCl_mono q.1.1.2 (range_algebraMap_mono h)⟩, phaseCl_mono q.1.2 (range_algebraMap_mono h)⟩,
      jetCl_mono q.2 (range_algebraMap_mono h)⟩)
    (fun M M' h q => lRatios_mono q (range_algebraMap_mono h)) k c5
  have k := InNF.and (fun M M' h q => ⟨⟨⟨⟨charsIn_mono q.1.1.1.1 (range_algebraMap_mono h),
      rootCl_mono q.1.1.1.2 (range_algebraMap_mono h)⟩, phaseCl_mono q.1.1.2 (range_algebraMap_mono h)⟩,
      jetCl_mono q.1.2 (range_algebraMap_mono h)⟩, lRatios_mono q.2 (range_algebraMap_mono h)⟩)
    (fun M M' h q => botCl_mono q (range_algebraMap_mono h)) k c6
  obtain ⟨M, hM, ⟨⟨⟨⟨⟨q1, q2⟩, q3⟩, q4⟩, q5⟩, q6⟩⟩ := k
  exact ⟨M, hM, ⟨q1, q2, q3, q4, q5, q6⟩⟩

end GlobalTheory.RowEx

end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.RowEx



theorem trEasy : TrEasy := by
  intro X X' T T' L L' sc G G' W W' S S' μ₀ μ₀' ι h M σ
  obtain ⟨⟨hpre, -, -, hC, hbase, hxi, hQ, -⟩, hg, -, hs⟩ := h
  obtain ⟨B, C, Wr, V, Sg, N, Gj⟩ := X
  obtain ⟨B', C', Wr', V', Sg', N', Gj'⟩ := X'
  cases B
  cases B'
  dsimp only at hpre
  subst hpre
  obtain ⟨f, f', hff, hLC, hLC'⟩ := hC
  have hf : f' = f := eq_of_heq hff
  subst hf
  have hv0 : G'.pl.v0 = G.pl.v0 := eq_of_heq hg.v0
  have hw : G'.pl.w = G.pl.w := eq_of_heq hg.w
  have hchi : G'.ch.chiH = G.ch.chiH := eq_of_heq hg.chiH
  have hxi' : ∀ t, L'.xiH t = L.xiH (ι t) := fun t => eq_of_heq (hxi t)
  have hQ' : ∀ t, L'.Q t = L.Q (ι t) := fun t => eq_of_heq (hQ t)
  have hPA : S'.PA = S.PA := eq_of_heq hs.PA
  have hW0 : G'.pl.W0 = G.pl.W0 := by
    unfold Places.W0 Places.S0
    rw [hv0, hw]
    rfl
  have hloc : ∀ t, locPl G' t = locPl G (ι t) := fun t => by
    unfold locPl
    rw [hW0, hQ' t]
    rfl
  have hdep : ∀ w, depthAt G' w = depthAt G w := fun w => by
    unfold depthAt cosExp Places.depth
    rw [hW0, hv0]
    rfl
  refine ⟨fun hch => ?_, fun hr => ?_, fun hr => ?_⟩
  · refine ⟨fun j => ?_, fun t => ?_, fun i h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
    · have := hch.mu0 j
      rw [hLC] at this
      rw [hLC']
      exact this
    · rw [hxi' t]
      exact hch.xi (ι t)
    · rw [hchi]
      exact hch.chi i h1 h2
    · have := hch.eta
      rw [hLC] at this
      rw [hLC']
      exact this
    · have := hch.chiPsi
      rw [hLC] at this
      rw [hLC']
      exact this
    · have := hch.del
      rw [hLC] at this
      rw [hLC']
      exact this
    · have := hch.del'
      rw [hLC] at this
      rw [hLC']
      exact this
  · refine ⟨hr.1, fun t w hwt => ?_, fun w hw' => ?_⟩
    · rw [hdep]
      rw [hloc] at hwt
      exact hr.2.1 (ι t) w hwt
    · rcases hw' with hw' | ⟨t, hw'⟩
      · rw [hPA] at hw'
        exact hr.2.2 w (Or.inl hw')
      · rw [hloc] at hw'
        exact hr.2.2 w (Or.inr ⟨ι t, hw'⟩)
  · intro i j t Λ Λ₀ h1 h2 s hs1 hs2 hΛ
    have hν : ∀ t, SqNum.nuH G' t i j = SqNum.nuH G (ι t) i j := fun t => by
      unfold SqNum.nuH
      rw [hLC', hLC, hxi' t, hchi]
      rfl
    rw [hν] at h1
    rw [hν, hbase] at h2
    exact hr i j (ι t) Λ Λ₀ h1 h2 s hs1 hs2 hΛ

end GlobalTheory.RowEx
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.RowEx.RatioField

open GlobalTheory.FunObj.SqNum GlobalTheory.CMVal

theorem kap_add_big (D : D7) (C : ℝ) (i j : Fin D.R.m) (τ : D.what₂.Tau) {s : ℕ} (hs : s ≤ bigN D + 1) :
    (kap D C i j s τ : ℤ) + s = (num D C τ).e (j + 1) + cen D C τ (D.R.m - i) ∧ 0 < kap D C i j s τ := by
  have h := SqNum.Model.gap_le D C i j τ
  have h2 := (GlobalTheory.ChiGrid.isLeast_gap D C).1.2.1
  have h4 : bigN D ≤ bigN D ^ 3 := Nat.le_self_pow (by norm_num) _
  unfold kap
  omega

theorem isValChar_shift {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} {s s' : ℕ}
    {κ κ' : I → ℕ} {𝔣 : Ideal (OF E)} {Q : Finset (HeightOneSpectrum (OF E))} {χ : HChar E}
    (h : IsValChar φ s κ 𝔣 Q χ) (e : ∀ i, (κ i : ℤ) + s = κ' i + s') : IsValChar φ s' κ' 𝔣 Q χ := by
  obtain ⟨a, b, c, d⟩ := h
  have : (fun i => (κ' i : ℤ) + s') = fun i => (κ i : ℤ) + s := funext fun i => (e i).symm
  exact ⟨a, b, this ▸ c, d⟩

theorem cmPhi_comp_eq {D : D7} (hfd : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (cmPhi D)) (τ τ' : D.what₂.Tau) :
    (cmPhi D τ).comp (algebraMap D.host.K D.host.E) = (cmPhi D τ').comp (algebraMap D.host.K D.host.E) := by
  obtain ⟨w, hw, hφw⟩ := hfd.2.2.2.2.2.2.2
  refine GlobalTheory.ToricRatioBridge.comp_eq_of_sqrt D.host _ _ ?_
  have hs := Formalism.BasicNotions.Host.sqrtMinusD_sq D.host
  have h0 : (D.host.sqrtMinusD - w) * (D.host.sqrtMinusD + w) = 0 := by linear_combination hs - hw
  rcases mul_eq_zero.1 h0 with h | h
  · rw [sub_eq_zero.1 h, hφw, hφw]
  · rw [eq_neg_of_add_eq_zero_left h, map_neg, map_neg, hφw, hφw]


open Classical in
theorem ratio_algebraic (hTR : GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates) {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts}
    {μ₀ : T} (hL : Lc.Is μ₀) (G : GridData Lc sc) (hcm : IsCMField D.host.E)
    (hfd : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (cmPhi D)) (hbc : IsBaseCond (condF G.pl))
    (i j : Fin D.R.m) (t : T) (s : ℕ) (hs1 : 1 ≤ s) (hs2 : s ≤ bigN D + 1) (Λ Λ₀ : ℂ → ℂ)
    (hΛ : IsHeckeL (nuH G t i j) Λ) (hΛ₀ : IsHeckeL (nuH G μ₀ i j) Λ₀) :
    IsAlgebraic ℚ (Λ s / Λ₀ s) := by
  haveI := hcm
  have hU : UnramFin D.host.E := hfd.2.2.1
  have hφ : IsCMType (cmPhi D) := hfd.2.2.2.2.2.2.1
  have e : ∀ τ, (kap D sc.cGap i j 0 τ : ℤ) + ((0 : ℕ) : ℤ) = kap D sc.cGap i j s τ + s := fun τ =>
    (SqNum.Model.kap_add D sc.cGap i j τ (Nat.zero_le _)).1.trans (kap_add_big D sc.cGap i j τ hs2).1.symm
  have hv0 : IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) ∅ (nuH G μ₀ i j) :=
    isValChar_shift (SqNum.Model.isValChar_nu hL G i j (Nat.zero_le _)).1 e
  obtain ⟨Q, hQdef⟩ : ∃ Q : Finset (HeightOneSpectrum (OF D.host.E)),
      Q = (GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F) := ⟨_, rfl⟩
  have hvt : IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) Q (nuH G t i j) :=
    hQdef ▸ isValChar_shift (GlobalTheory.SqTop.TwVal.isValChar_nu_twist G hL t i j (Nat.zero_le _)) e
  have hQaux : IsFinSetSplitPlacesCoprimeConductor (condF G.pl) Q := hQdef ▸ GlobalTheory.KummerTwistLemmas.twist_places_under_split_coprime_conductor G hL t
  have hQram := GlobalTheory.SqTop.nuH_not_unrAt_twPl G hL t i j
  have hex : ∀ q ∈ Q, ∃ P ∈ GlobalTheory.SqTop.twPl G t, P.under (𝓞 D.host.F) = q := fun q hq => by
    rw [hQdef] at hq
    exact Finset.mem_image.1 hq
  let Pq : HeightOneSpectrum (OF D.host.E) → HeightOneSpectrum (𝓞 D.host.E) := fun q =>
    if h : ∃ P ∈ GlobalTheory.SqTop.twPl G t, P.under (𝓞 D.host.F) = q then h.choose else G.pl.w G.pl.v0
  have hPq : ∀ q ∈ Q, Pq q ∈ GlobalTheory.SqTop.twPl G t ∧ (Pq q).under (𝓞 D.host.F) = q := fun q hq => by
    have h := hex q hq
    simp only [Pq, dif_pos h]
    exact h.choose_spec
  have hov : ∀ q ∈ Q, Over (Pq q) q := fun q hq =>
    (show Over (Pq q) ((Pq q).under (OF D.host.E)) from rfl).trans (congrArg HeightOneSpectrum.asIdeal (hPq q hq).2)

  have htor := GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.Published.HeckeEntire_holds D.host.E D.what₂.Tau (cmPhi D) hφ s
    (kap D sc.cGap i j s) (condF G.pl) Q (nuH G t i j) Pq Λ hU hs1 hbc hQaux hvt hov hΛ
  rw [Finset.filter_false_of_mem (fun q hq => hQram _ (hPq q hq).1), Finset.prod_empty, mul_one] at htor

  have htor0 := GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.Published.HeckeEntire_holds D.host.E D.what₂.Tau (cmPhi D) hφ s
    (kap D sc.cGap i j s) (condF G.pl) ∅ (nuH G μ₀ i j) (fun _ => G.pl.w G.pl.v0) Λ₀ hU hs1 hbc
    (fun q hq => absurd hq (Finset.notMem_empty q)) hv0 (fun q hq => absurd hq (Finset.notMem_empty q)) hΛ₀
  simp only [condQ, Finset.prod_empty, mul_one, Finset.filter_empty] at htor0

  have hnu : nuH G t i j = nuH G μ₀ i j * Lc.xiH t := by
    rw [nuH, nuH, hL.xi_base, mul_one, div_mul_eq_mul_div]

  obtain ⟨k, hk, hko⟩ := hL.xi_fin t
  have hinf : ∀ y : D.host.Eˣ, (Lc.xiH t).inf y = 1 := fun y => GlobalTheory.TypeValues.inf_eq_one _ hk hko y
  have hu : ∀ u ∈ hatOUnits (condQ (condF G.pl) Q), finPart (Lc.xiH t) u = 1 := fun u hu => by
    have a := GlobalTheory.CMVal.OrderUnits.finPart_eq_one D.host.E D.what₂.Tau (cmPhi D) hφ s (kap D sc.cGap i j s)
      (condF G.pl) Q (nuH G t i j) hU hbc hQaux hvt u hu
    have hle : condQ (condF G.pl) Q ≤ condQ (condF G.pl) ∅ := by
      simp only [condQ, Finset.prod_empty, mul_one]
      exact Ideal.mul_le_left
    have b := GlobalTheory.CMVal.OrderUnits.finPart_eq_one D.host.E D.what₂.Tau (cmPhi D) hφ s (kap D sc.cGap i j s)
      (condF G.pl) ∅ (nuH G μ₀ i j) hU hbc (fun q hq => absurd hq (Finset.notMem_empty q)) hv0 u
      (hatOUnits_mono hle hu)
    rw [hnu, finPart_mul, b, one_mul] at a
    exact a
  have hker : princ ⊔ hatOUnits (condQ (condF G.pl) Q) ≤ (finPart (Lc.xiH t)).ker := by
    refine sup_le ?_ fun u hu' => hu u hu'
    rintro _ ⟨a, rfl⟩
    have := finPart_mul_inf (Lc.xiH t) a
    rw [hinf a, mul_one] at this
    exact this
  let ψ : PicO (condQ (condF G.pl) Q) →* ℂˣ := QuotientGroup.lift _ (finPart (Lc.xiH t)) hker

  haveI : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by have := hfd.2.2.2.2.2.1; omega)
  let τ₀ : D.what₂.Tau := Classical.arbitrary _
  have hK2 : Module.finrank ℚ D.host.K = 2 := Formalism.MainNotions.DIV.Bridge.LogAbsNormDifferent.finrank_K D
  let δ : D.host.K := ⟨D.host.sqrtMinusD, GlobalTheory.Mem.Col2.HostK.sqrt_mem D.host⟩
  have hδ : δ ^ 2 = -(D.host.d : D.host.K) := Subtype.ext (by simpa using Formalism.BasicNotions.Host.sqrtMinusD_sq D.host)
  obtain ⟨T₀, Tf, hT₀, -, hTw, hAlg, -⟩ := hTR D.host.E D.host.K D.host.d δ
    ((cmPhi D τ₀).comp (algebraMap D.host.K D.host.E)) D.what₂.Tau (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) Q
    (nuH G μ₀ i j) hU hK2 hfd.1.pos hδ hφ (fun τ => cmPhi_comp_eq hfd τ τ₀) hs1
    (fun τ => (kap_add_big D sc.cGap i j τ hs2).2) hbc hQaux hv0
  have e1 : T₀ = Λ₀ s := hT₀.unique htor0
  have e2 : Tf ψ = Λ s :=
    ((GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.isTwistedSum_iff_isToricSum (ξ := Lc.xiH t) (fun y => rfl) _).1 (hTw ψ)).unique (hnu ▸ htor)
  rw [← e1, ← e2]
  exact hAlg ψ

end GlobalTheory.RowEx.RatioField

namespace GlobalTheory.RowEx.RatioField

open GlobalTheory.FunObj.SqNum GlobalTheory.CMVal

theorem inNF_ratios (hTR : GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates) {D : D7} {T : Type} [Finite T] {Lc : LevCh D T} {sc : Consts}
    {μ₀ : T} (hL : Lc.Is μ₀) (G : GridData Lc sc) (hcm : IsCMField D.host.E)
    (hfd : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (cmPhi D)) (hbc : IsBaseCond (condF G.pl)) :
    InNF fun _ σ => ∀ i j, LRatiosIn G σ μ₀ i j := by
  let S : Set ℂ := ⋃ (i : Fin D.R.m) (j : Fin D.R.m) (t : T) (s ∈ Set.Icc 1 (bigN D + 1)),
    {z | ∃ Λ Λ₀ : ℂ → ℂ, IsHeckeL (nuH G t i j) Λ ∧ IsHeckeL (nuH G μ₀ i j) Λ₀ ∧ z = Λ s / Λ₀ s}
  have hS : S.Finite := by
    refine Set.finite_iUnion fun i => Set.finite_iUnion fun j => Set.finite_iUnion fun t =>
      (Set.finite_Icc _ _).biUnion fun s _ => Set.Subsingleton.finite ?_
    rintro _ ⟨Λ, Λ₀, h1, h2, rfl⟩ _ ⟨Λ', Λ₀', h1', h2', rfl⟩
    rw [h1.unique h1', h2.unique h2']
  have hSa : ∀ z ∈ S, IsAlgebraic ℚ z := by
    intro z hz
    simp only [S, Set.mem_iUnion, Set.mem_setOf_eq] at hz
    obtain ⟨i, j, t, s, ⟨h1, h2⟩, Λ, Λ₀, hΛ, hΛ₀, rfl⟩ := hz
    exact ratio_algebraic hTR hL G hcm hfd hbc i j t s h1 h2 Λ Λ₀ hΛ hΛ₀
  haveI : Finite S := hS.to_subtype
  refine ⟨IntermediateField.adjoin ℚ S, IntermediateField.finiteDimensional_adjoin fun z hz => (hSa z hz).isIntegral,
    fun i j t Λ Λ₀ hΛ hΛ₀ s h1 h2 _ => ⟨⟨Λ s / Λ₀ s, IntermediateField.subset_adjoin ℚ S ?_⟩, rfl⟩⟩
  simp only [S, Set.mem_iUnion, Set.mem_setOf_eq]
  exact ⟨i, j, t, s, ⟨h1, h2⟩, Λ, Λ₀, hΛ, hΛ₀, rfl⟩

end GlobalTheory.RowEx.RatioField
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3

namespace GlobalTheory.RowEx.DatTw

open Formalism.L2.Host

theorem not_two_primes {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (h1 : (p : R) ∈ P) (h2 : (q : R) ∈ P) : False := by
  obtain ⟨u, v, huv⟩ : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  apply hP.ne_top
  rw [Ideal.eq_top_iff_one]
  have e := congrArg (Int.cast : ℤ → R) huv
  push_cast at e
  rw [← e]
  exact P.add_mem (P.mul_mem_left _ h1) (P.mul_mem_left _ h2)

theorem unrAt_mul {L : Type} [Field L] [NumberField L] {χ χ' : HChar L} {v : HeightOneSpectrum (𝓞 L)} (h : χ.UnrAt v)
    (h' : χ'.UnrAt v) : (χ * χ').UnrAt v := fun x hx => by
  change χ.loc v x * χ'.loc v x = 1
  rw [h x hx, h' x hx, one_mul]

theorem unrAt_one {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) : (1 : HChar L).UnrAt v := fun _ _ => rfl

variable {R : Ranks} (H : Host R)

theorem unrAt_of_isTwist {S : Set ℕ} (hS : GlobalTheory.EX.DC.q0H H ∈ S) {ψ : HChar H.E} (hψ : Chr.IsTwist H S ψ)
    {v : HeightOneSpectrum (𝓞 H.E)} (hv : ((GlobalTheory.EX.DC.q0H H : ℕ) : 𝓞 H.E) ∈ v.asIdeal) : ψ.UnrAt v := by
  by_contra h
  obtain ⟨-, hpr, -, hnot⟩ := hψ.2.2.2 v h
  by_cases e : Ideal.absNorm v.asIdeal = GlobalTheory.EX.DC.q0H H
  · exact hnot (e ▸ hS)
  · exact not_two_primes v.asIdeal hpr (GlobalTheory.EX.DC.globalTwisting_spec_fact H).1 e (Ideal.absNorm_mem _) hv

theorem not_overP_pde {v : HeightOneSpectrum (𝓞 H.E)} (hv : ((GlobalTheory.EX.DC.q0H H : ℕ) : 𝓞 H.E) ∈ v.asIdeal) :
    ¬ OverP H H.pde v ∧ ¬ OverP H H.pde' v :=
  ⟨fun h => not_two_primes v.asIdeal H.pde_prime (GlobalTheory.EX.DC.globalTwisting_spec_fact H).1 (GlobalTheory.EX.DC.q0H_ne_pde_and_ne_pde' H).1.symm h hv,
    fun h => not_two_primes v.asIdeal H.pde'_prime (GlobalTheory.EX.DC.globalTwisting_spec_fact H).1 (GlobalTheory.EX.DC.q0H_ne_pde_and_ne_pde' H).2.symm h hv⟩

theorem unrAt_of_mem_set {B : Base} {f : Fr B.toPre} {T : TwDat B} {ξ : HChar B.host.E} (h : ξ ∈ T.set f)
    {v : HeightOneSpectrum (𝓞 B.host.E)} (hv : ((GlobalTheory.EX.DC.q0H B.host : ℕ) : 𝓞 B.host.E) ∈ v.asIdeal) : ξ.UnrAt v := by
  have hd := not_overP_pde B.host hv
  have hdel : f.del.UnrAt v := f.isDel.unr v hd.1
  have hdel' : f.del'.UnrAt v := f.isDel'.unr v hd.2
  simp only [TwDat.set, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range] at h
  rcases h with (rfl | rfl | rfl) | ⟨w, rfl⟩
  · exact unrAt_one v
  · exact hdel
  · exact hdel'
  · unfold TwDat.xiTw
    refine unrAt_mul ?_ (unrAt_of_isTwist B.host ?_ (T.psi_tw w) hv)
    · split_ifs
      · exact hdel'
      · exact hdel
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))

end GlobalTheory.RowEx.DatTw

theorem GlobalTheory.RowEx.twisted_data_off_base_level : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok)
    (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt), GlobalTheory.RowEx.TwistPlacesOffPrimeQZero z.R.toLevCh ∧ z.R.C = Fr.at (w.st Z) f ∧
      (T.set f).Finite ∧ ∀ t, z.R.xiH t ∈ T.set f := by
  intro B f T w Z hX Wt z
  have hmem : ∀ t, z.R.xiH t ∈ T.set f := fun t => by
    rw [z.lev.xiH t, ← w.xi_range]
    exact ⟨_, rfl⟩
  refine ⟨fun t PP hPP hq => ?_, ?_, ?_, hmem⟩
  · exact (z.lev.is.Q_ram t PP).2 (Or.inl hPP) (GlobalTheory.RowEx.DatTw.unrAt_of_mem_set (hmem t) hq)
  · rw [z.lev.C, w.C_eq]
  · rw [← w.xi_range]
    exact Set.finite_range _
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin


theorem _root_.GlobalTheory.T.positiveRealPart_traceCharacter_mem_nhds : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (n ρ : ℕ) (L : Mx D ρ n) (x : Mx D n ρ), {z : Mx D n ρ | 0 < (star (psiE ψ (upSum (L ⬝ (z - x))))).re} ∈ nhds x := by
  first | exact @GlobalTheory.PosNhdsChar.posNhds | exact GlobalTheory.PosNhdsChar.posNhds | (intros; apply GlobalTheory.PosNhdsChar.posNhds <;> assumption)
end
