module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle547
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle561
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitBlockTypes
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterConductorCondition
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle009
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealModelExists
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
public import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

section LimLists

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem limL_allLeaves_strip (P : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop) :
    ∀ {N : ℕ} (t : Tr E N), t.strip.AllLeaves P ↔ t.AllLeaves P := by
  intro N t
  induction t with
  | leaf V z => exact Iff.rfl
  | node t₁ t₂ i₁ i₂ => exact and_congr i₁ i₂

theorem limL_allLeaves_shift (P : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop) (z : ℂ) :
    ∀ {N : ℕ} (t : Tr E N), (t.shift z).AllLeaves P ↔ t.AllLeaves P := by
  intro N t
  induction t with
  | leaf V z' => exact Iff.rfl
  | node t₁ t₂ i₁ i₂ => exact and_congr i₁ i₂

theorem limL_allLeaves_mono {P Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} (h : ∀ M V, P M V → Q M V) :
    ∀ {N : ℕ} {t : Tr E N}, t.AllLeaves P → t.AllLeaves Q := by
  intro N t
  induction t with
  | leaf V z => exact h _ _
  | node t₁ t₂ i₁ i₂ => exact fun a => ⟨i₁ a.1, i₂ a.2⟩

theorem limL_disc_shift (z : ℂ) : ∀ {N : ℕ} {t : Tr E N}, t.AllLeaves (fun M _ => 0 < M) → t.Disc → (t.shift z).Disc := by
  intro N t
  induction t with
  | leaf V z' =>
    intro hp h
    rcases h with h | h
    · exact absurd h.1 (Nat.ne_of_gt (show 0 < _ from hp))
    · exact Or.inr h
  | node t₁ t₂ i₁ i₂ => exact fun hp h => ⟨i₁ hp.1 h.1, i₂ hp.2 h.2⟩

theorem limL_good_shift {z : ℂ} (hz : z.re = 0) :
    ∀ {N : ℕ} {t : Tr E N}, t.AllLeaves (fun M _ => 0 < M) → t.Good → (t.shift z).Good := by
  intro N t
  induction t with
  | leaf V z' =>
    intro hp h
    rcases h with h | h
    · exact absurd h.1 (Nat.ne_of_gt (show 0 < _ from hp))
    · exact Or.inr ⟨h.1, h.2.1, by simp [h.2.2, hz]⟩
  | node t₁ t₂ i₁ i₂ => exact fun hp h => ⟨i₁ hp.1 h.1, i₂ hp.2 h.2⟩

def LimDiscBody (E : Type) [Field E] [NumberField E] [IsCMField E] (M : ℕ) (W : Submodule ℂ (Kinf E M → ℂ))
    (K : Subgroup (GL (Fin M) (Af E))) (Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)))
    (Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) : Prop :=
  ∀ [MeasurableSpace (GA E M)] [BorelSpace (GA E M)] (μ : Measure (GA E M)) [μ.IsHaarMeasure] (R : ℝ), 0 < M →
  ReproAll E →
  ∀ V : ℕ → Submodule ℂ (Sm E M), (∀ k, IsDiscrete (V k)) → (∀ k, HasType K W (V k)) → (∀ k, InfBdd R (V k)) →
  ∃ (φ : ℕ → ℕ) (t : ℕ → Tr E M) (t₀ : Tr E M), StrictMono φ ∧ t₀.Good ∧ (∀ k, (t k).Disc) ∧
    (∀ k, (t k).strip = t₀.strip) ∧
    t₀.AllLeaves (fun M V => 0 < M ∧ ∃ K' ∈ Θ M, ∃ W' ∈ Ω M, HasType K' W' V) ∧
    (∀ i, Tendsto (fun k => ((t k).twists.getD i 0)) atTop (𝓝 (t₀.twists.getD i 0))) ∧
    ∀ k, Emb (V (φ k)) (· ∈ (t k).space)

theorem limL_exists_haar (M : ℕ) : ∃ (_ : MeasurableSpace (GA E M)) (_ : BorelSpace (GA E M)) (μ : Measure (GA E M)),
    μ.IsHaarMeasure := by
  letI : MeasurableSpace (GA E M) := borel _
  haveI : BorelSpace (GA E M) := ⟨rfl⟩
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E M
  exact ⟨_, inferInstance, Measure.haar, inferInstance⟩

theorem limL_lim_one (hS : ConvStrip) (hSh : ConvShift) (hC : ConvComp) (hT : TwShift) {M : ℕ} (hM : 0 < M)
    {W : Submodule ℂ (Kinf E M → ℂ)} {K : Subgroup (GL (Fin M) (Af E))}
    {Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))} {Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))}
    (hB : LimDiscBody E M W K Ω Θ) (V : ℕ → Submodule ℂ (Sm E M)) (z : ℕ → ℂ) (R : ℝ) (hR : ReproAll E)
    (hD : ∀ k, IsDiscrete (V k)) (hz : ∀ k, (z k).re = 0) (hTy : ∀ k, HasType K W (V k))
    (hI : ∀ k, InfBdd R (V k)) (hzR : ∀ k, ‖z k‖ ≤ R) :
    ∃ (φ : ℕ → ℕ) (t : ℕ → Tr E M) (s : Tr E M), StrictMono φ ∧ Conv t s ∧ Red s ∧ s.Good ∧
      s.AllLeaves (fun M V => 0 < M ∧ ∃ K' ∈ Θ M, ∃ W' ∈ Ω M, HasType K' W' V) ∧ (∀ k, (t k).Disc) ∧
      ∀ k, Emb (tw (V (φ k)) (z (φ k))) (· ∈ (t k).space) := by
  obtain ⟨_, _, μ, _⟩ := limL_exists_haar (E := E) M
  obtain ⟨φ, tt, t₀, hφ, hG, hDt, hst, hL, htw, hE⟩ := hB μ R hM hR V hD hTy hI
  obtain ⟨z₀, hz₀, ψ, hψ, hlim⟩ := tendsto_subseq_of_bounded (x := fun k => z (φ k))
    (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)) (fun k => by simpa using hzR (φ k))
  have hre : z₀.re = 0 := by
    have h1 : Tendsto (fun k => (z (φ (ψ k))).re) atTop (𝓝 z₀.re) :=
      (Complex.continuous_re.tendsto z₀).comp hlim
    simp only [hz, ] at h1
    exact (tendsto_nhds_unique h1 tendsto_const_nhds)
  have hpos : t₀.AllLeaves (fun M _ => 0 < M) := limL_allLeaves_mono (fun _ _ h => h.1) hL
  have hposk : ∀ k, (tt k).AllLeaves (fun M _ => 0 < M) := fun k => by
    rw [← limL_allLeaves_strip, hst k, limL_allLeaves_strip]
    exact hpos
  have hconv : Conv tt t₀ := (hS E M tt t₀).2 ⟨hst, htw⟩
  have hconv' : Conv (fun k => (tt (ψ k)).shift (z (φ (ψ k)))) (t₀.shift z₀) :=
    hSh E M _ t₀ _ z₀ (hC E M tt t₀ ψ hconv hψ) hlim
  have hL' : (t₀.shift z₀).AllLeaves (fun M V => 0 < M ∧ ∃ K' ∈ Θ M, ∃ W' ∈ Ω M, HasType K' W' V) :=
    (limL_allLeaves_shift _ _ _).2 hL
  exact ⟨fun k => φ (ψ k), fun k => (tt (ψ k)).shift (z (φ (ψ k))), t₀.shift z₀, hφ.comp hψ, hconv',
    red_of_leaves hL', limL_good_shift hre hpos hG, hL', fun k => limL_disc_shift _ (hposk _) (hDt _),
    fun k => hT E M _ _ _ (hD _).stable (hE _)⟩

end LimLists

theorem limLists : ConvStrip → ConvShift → ConvComp → LimLists := by
  intro hS hSh hC h5 hT E _ _ _ N Ωs hΩs
  have h1 : ∀ (M : ℕ) (W : Submodule ℂ (Kinf E M → ℂ)),
      ∃ Ω : ∀ M' : ℕ, Set (Submodule ℂ (Kinf E M' → ℂ)), KTypes E Ω ∧
        (FiniteDimensional ℂ W → ∀ K : Subgroup (GL (Fin M) (Af E)), IsOpen (K : Set (GL (Fin M) (Af E))) →
          ∃ Θ : ∀ M' : ℕ, Set (Subgroup (GL (Fin M') (Af E))), Levels E Θ ∧ LimDiscBody E M W K Ω Θ) := by
    intro M W
    by_cases hW : FiniteDimensional ℂ W
    · obtain ⟨Ω, hΩ, h⟩ := h5 E M W hW
      exact ⟨Ω, hΩ, fun _ K hK => h K hK⟩
    · exact ⟨fun _ => ∅, fun _ => ⟨Set.finite_empty, by simp⟩, fun h => absurd h hW⟩
  choose Om hOm hOm' using h1
  refine ⟨fun M' => ⋃ M ∈ Set.Icc 1 N, ⋃ W ∈ Ωs M, Om M W M', ?_, ?_⟩
  · intro M'
    refine ⟨(Set.finite_Icc 1 N).biUnion fun M _ => (hΩs M).1.biUnion fun W _ => (hOm M W M').1, ?_⟩
    intro W' hW'
    simp only [Set.mem_iUnion] at hW'
    obtain ⟨M, _, W, _, h⟩ := hW'
    exact (hOm M W M').2 W' h
  intro Θs hΘs
  have h2 : ∀ (M : ℕ) (W : Submodule ℂ (Kinf E M → ℂ)) (K : Subgroup (GL (Fin M) (Af E))),
      ∃ Θ : ∀ M' : ℕ, Set (Subgroup (GL (Fin M') (Af E))), Levels E Θ ∧
        (FiniteDimensional ℂ W → IsOpen (K : Set (GL (Fin M) (Af E))) → LimDiscBody E M W K (Om M W) Θ) := by
    intro M W K
    by_cases h : FiniteDimensional ℂ W ∧ IsOpen (K : Set (GL (Fin M) (Af E)))
    · obtain ⟨Θ, hΘ, hb⟩ := hOm' M W h.1 K h.2
      exact ⟨Θ, hΘ, fun _ _ => hb⟩
    · exact ⟨fun _ => ∅, fun _ => ⟨Set.finite_empty, fun _ hk => False.elim hk⟩,
        fun a b => absurd ⟨a, b⟩ h⟩
  choose Th hTh hTh' using h2
  refine ⟨fun M' => ⋃ M ∈ Set.Icc 1 N, ⋃ W ∈ Ωs M, ⋃ K ∈ Θs M, Th M W K M', ?_, ?_⟩
  · intro M'
    refine ⟨(Set.finite_Icc 1 N).biUnion fun M _ => (hΩs M).1.biUnion fun W _ =>
      (hΘs M).1.biUnion fun K _ => (hTh M W K M').1, ?_⟩
    intro K' hK'
    simp only [Set.mem_iUnion] at hK'
    obtain ⟨M, _, W, _, K, _, h⟩ := hK'
    exact (hTh M W K M').2 K' h
  intro M hM hMN V z R hR hD hz hTy hI hzR
  choose Kk hKk Wk hWk hty using hTy
  have hfin : (Θs M ×ˢ Ωs M).Finite := (hΘs M).1.prod (hΩs M).1
  haveI := hfin.to_subtype
  obtain ⟨⟨⟨K, W⟩, hKW⟩, hinf⟩ := Finite.exists_infinite_fiber
    (fun k : ℕ => (⟨(Kk k, Wk k), hKk k, hWk k⟩ : ↥(Θs M ×ˢ Ωs M)))
  have hfr : ∃ᶠ k in atTop, Kk k = K ∧ Wk k = W := by
    refine Nat.frequently_atTop_iff_infinite.2 ((Set.infinite_coe_iff.1 hinf).mono ?_)
    intro k hk
    have h := congrArg Subtype.val (Set.mem_singleton_iff.1 (Set.mem_preimage.1 hk))
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  obtain ⟨a, ha, hak⟩ := extraction_of_frequently_atTop hfr
  have hK : K ∈ Θs M := hKW.1
  have hW : W ∈ Ωs M := hKW.2
  have hbody : LimDiscBody E M W K (Om M W) (Th M W K) := hTh' M W K ((hΩs M).2 W hW) ((hΘs M).2 K hK)
  have htyp : ∀ k, HasType K W (V (a k)) := fun k => by
    have h := hty (a k)
    rwa [(hak k).1, (hak k).2] at h
  obtain ⟨φ, t, s, hφ, hc, hr, hg, hl, hd, he⟩ := limL_lim_one hS hSh hC hT hM hbody (fun k => V (a k))
    (fun k => z (a k)) R hR (fun k => hD _) (fun k => hz _) htyp (fun k => hI _) (fun k => hzR _)
  refine ⟨fun k => a (φ k), t, s, ha.comp hφ, hc, hr, hg, limL_allLeaves_mono ?_ hl, hd, he⟩
  rintro M' V' ⟨-, K'', hK'', W'', hW'', h⟩
  refine Or.inr ⟨K'', ?_, W'', ?_, h⟩
  · simp only [Set.mem_iUnion]
    exact ⟨M, ⟨hM, hMN⟩, W, hW, K, hK, hK''⟩
  · simp only [Set.mem_iUnion]
    exact ⟨M, ⟨hM, hMN⟩, W, hW, hW''⟩

end GlobalTheory.CompanionTheory.EGlue

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV

namespace GlobalTheory.CompanionTheory.EGlue.Restrict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem pairSpace_le_prodSpan (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) :
    pairSpace U₁ U₂ ≤ prodSpan (U₁.map (Sm E a).subtype) (U₂.map (Sm E b).subtype) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨φ₁, h₁, φ₂, h₂, rfl⟩
  exact Submodule.subset_span ⟨φ₁.1, ⟨φ₁, h₁, rfl⟩, φ₂.1, ⟨φ₂, h₂, rfl⟩, rfl⟩

theorem prodSpan_le_pairSpace (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) :
    prodSpan (U₁.map (Sm E a).subtype) (U₂.map (Sm E b).subtype) ≤ pairSpace U₁ U₂ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨_, ⟨φ₁, h₁, rfl⟩, _, ⟨φ₂, h₂, rfl⟩, rfl⟩
  exact Submodule.subset_span ⟨φ₁, h₁, φ₂, h₂, rfl⟩

theorem slice_mem (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (F : H E a b → ℂ)
    (hF : F ∈ pairSpace U₁ U₂) (m₁ : GA E a) :
    (fun y => F (m₁, y)) ∈ U₂.map (Sm E b).subtype := by
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨φ₁, -, φ₂, h₂, rfl⟩ := h
    exact ⟨φ₁.1 m₁ • φ₂, U₂.smul_mem _ h₂, by funext y; simp⟩
  | zero => exact Submodule.zero_mem _
  | add F F' _ _ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
  | smul r F _ h => exact Submodule.smul_mem _ r h

end GlobalTheory.CompanionTheory.EGlue.Restrict

namespace GlobalTheory.CompanionTheory.EGlue

theorem pairRestrict_holds : PairRestrict := by
  intro E _ _ _ a b U₁ U₂ U₂' F hF hs
  have hS₂ : ∀ m₁, (fun y => F (m₁, y)) ∈ U₂'.map (Sm E b).subtype := by
    intro m₁
    obtain ⟨φ, -, hφ⟩ := Restrict.slice_mem U₁ U₂ F hF m₁
    exact ⟨φ, hs m₁ φ hφ, hφ⟩
  have h := GlobalTheory.CompanionTheory.LimV.Slices.mem_prodSpan_inf_of_slices (U₁.map (Sm E a).subtype) ⊤
    (U₂.map (Sm E b).subtype) (U₂'.map (Sm E b).subtype) F
    (Restrict.pairSpace_le_prodSpan U₁ U₂ hF) (fun _ => Submodule.mem_top) hS₂
  refine Restrict.prodSpan_le_pairSpace U₁ U₂' ?_
  refine Submodule.span_mono ?_ h
  rintro _ ⟨p, hp, q, hq, rfl⟩
  exact ⟨p, hp.1, q, hq.2, rfl⟩

end GlobalTheory.CompanionTheory.EGlue

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue.PairT₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem sl₂_eq {F : H E a b → ℂ} {m : GA E a} {φ : Sm E b} (h : φ.1 = fun x => F (m, x)) : sl₂ F m = φ := by
  have hx : ∃ φ : Sm E b, φ.1 = fun x => F (m, x) := ⟨φ, h⟩
  unfold sl₂
  rw [dite_eq_left hx]
  exact Subtype.ext (hx.choose_spec.trans h.symm)

variable {U₁ : Submodule ℂ (Sm E a)} {U₂ : Submodule ℂ (Sm E b)} {F G : H E a b → ℂ}

theorem sl₂_val (hS : PairSlices) (hF : F ∈ pairSpace U₁ U₂) (m : GA E a) (x : GA E b) :
    (sl₂ F m).1 x = F (m, x) :=
  congrFun ((hS E a b U₁ U₂ F hF).2 m).2 x

theorem sl₂_mem (hS : PairSlices) (hF : F ∈ pairSpace U₁ U₂) (m : GA E a) : sl₂ F m ∈ U₂ :=
  ((hS E a b U₁ U₂ F hF).2 m).1

theorem ap₂_add (hS : PairSlices) (T : Sm E b →ₗ[ℂ] Sm E b) (hF : F ∈ pairSpace U₁ U₂)
    (hG : G ∈ pairSpace U₁ U₂) : ap₂ T (F + G) = ap₂ T F + ap₂ T G := by
  funext x
  have e : sl₂ (F + G) x.1 = sl₂ F x.1 + sl₂ G x.1 := sl₂_eq (by
    funext y
    exact congrArg₂ (· + ·) (sl₂_val hS hF x.1 y) (sl₂_val hS hG x.1 y))
  change (T (sl₂ (F + G) x.1)).1 x.2 = _
  rw [e, map_add (f := _)]
  rfl

theorem ap₂_smul (hS : PairSlices) (T : Sm E b →ₗ[ℂ] Sm E b) (c : ℂ) (hF : F ∈ pairSpace U₁ U₂) :
    ap₂ T (c • F) = c • ap₂ T F := by
  funext x
  have e : sl₂ (c • F) x.1 = c • sl₂ F x.1 := sl₂_eq (by
    funext y
    exact congrArg (c * ·) (sl₂_val hS hF x.1 y))
  change (T (sl₂ (c • F) x.1)).1 x.2 = _
  rw [e, map_smul]
  rfl

theorem ap₂_zero (hS : PairSlices) (T : Sm E b →ₗ[ℂ] Sm E b) (U₁ : Submodule ℂ (Sm E a))
    (U₂ : Submodule ℂ (Sm E b)) : ap₂ T (0 : H E a b → ℂ) = 0 := by
  have h := ap₂_smul hS T (0 : ℂ) (Submodule.zero_mem (pairSpace U₁ U₂))
  simpa using h

theorem ap₂_sum (hS : PairSlices) (T : Sm E b →ₗ[ℂ] Sm E b) {α : Type} (s : Finset α)
    (f : α → H E a b → ℂ) (hf : ∀ j ∈ s, f j ∈ pairSpace U₁ U₂) :
    ap₂ T (∑ j ∈ s, f j) = ∑ j ∈ s, ap₂ T (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ap₂_zero hS T U₁ U₂
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      ap₂_add hS T (hf j (Finset.mem_insert_self j s))
        (Submodule.sum_mem _ fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem ap₂_rt (hS : PairSlices) (T : Sm E b →ₗ[ℂ] Sm E b)
    (hT : ∀ o, ∀ ψ ∈ U₂, T (act o ψ) = act o (T ψ)) (hF : F ∈ pairSpace U₁ U₂) (g : Hf E a b)
    (x : H E a b) : ap₂ T (fun y => F (y * finH g)) x = ap₂ T F (x * finH g) := by
  have e : sl₂ (fun y => F (y * finH g)) x.1 = act (.fin g.2) (sl₂ F (x.1 * finGL E a g.1)) :=
    sl₂_eq (by
      funext y
      exact (sl₂_val hS hF _ _).trans rfl)
  change (T (sl₂ _ x.1)).1 x.2 = (T (sl₂ F (x.1 * finGL E a g.1))).1 (x.2 * finGL E b g.2)
  rw [e, hT _ _ (sl₂_mem hS hF _)]
  rfl

theorem rt_mem (hU : _root_.GlobalTheory.CuspRep.IsStable U₂) (hF : F ∈ pairSpace U₁ U₂) (g : Hf E a b) :
    (fun y => F (y * finH g)) ∈ pairSpace (⊤ : Submodule ℂ (Sm E a)) U₂ := by
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨φ₁, -, φ₂, h₂, rfl⟩ := h
    exact Submodule.subset_span ⟨act (.fin g.1) φ₁, trivial, act (.fin g.2) φ₂, hU _ _ h₂, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add F G _ _ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
  | smul r F _ h => exact Submodule.smul_mem _ r h

theorem ap₂_mem (hS : PairSlices) {U₂' : Submodule ℂ (Sm E b)} (T : Sm E b →ₗ[ℂ] Sm E b)
    (hTU : ∀ ψ ∈ U₂, T ψ ∈ U₂') (hF : F ∈ pairSpace U₁ U₂) : ap₂ T F ∈ pairSpace U₁ U₂' := by
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := h
    refine Submodule.subset_span ⟨φ₁, h₁, T φ₂, hTU _ h₂, ?_⟩
    funext x
    have e : sl₂ (fun x : H E a b => φ₁.1 x.1 * φ₂.1 x.2) x.1 = φ₁.1 x.1 • φ₂ := sl₂_eq rfl
    change (T (sl₂ _ x.1)).1 x.2 = _
    rw [e, map_smul]
    rfl
  | zero =>
    rw [ap₂_zero hS T U₁ U₂]
    exact Submodule.zero_mem _
  | add F G hF hG h₁ h₂ =>
    rw [ap₂_add hS T hF hG]
    exact Submodule.add_mem _ h₁ h₂
  | smul r F hF h =>
    rw [ap₂_smul hS T r hF]
    exact Submodule.smul_mem _ r h

theorem ap₂_type (hS : PairSlices) {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} (fd₁ : FiniteDimensional ℂ W₁)
    (fd₂ : FiniteDimensional ℂ W₂) (T : Sm E b →ₗ[ℂ] Sm E b)
    (hT : ∀ o, ∀ ψ ∈ U₂, T (act o ψ) = act o (T ψ)) (hF : F ∈ pairSpace U₁ U₂)
    (hty : TypeH K₁ K₂ W₁ W₂ F) : TypeH K₁ K₂ W₁ W₂ (ap₂ T F) := by
  refine ⟨fun u₁ h₁ u₂ h₂ x => ?_, fun x => ?_⟩
  · have e : (fun y => F (y * finH ((u₁, u₂) : Hf E a b))) = F := funext (hty.1 u₁ h₁ u₂ h₂)
    have h := ap₂_rt hS T hT hF (u₁, u₂) x
    rw [e] at h
    exact h.symm
  · haveI : FiniteDimensional ℂ (Submodule.span ℂ {f : Kinf E a × Kinf E b → ℂ |
        ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}) :=
      GlobalTheory.CompanionTheory.LimV.finiteDimensional_prodSpan_of_fd W₁ W₂ fd₁ fd₂
    let ev : GA E b → Sm E b →ₗ[ℂ] ℂ := fun y =>
      (LinearMap.proj y : (GA E b → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (Sm E b).subtype
    have h := GlobalTheory.CompanionTheory.LimV.BlockTy.mem_of_separating
      (Submodule.span ℂ {f : Kinf E a × Kinf E b → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2})
      (fun k : Kinf E a × Kinf E b =>
        act (.cpt k.2) (sl₂ F (x.1 * infGL E a (Unitary.toUnits k.1)))) ev
      (fun m hm => Subtype.ext (funext hm)) (ev x.2 ∘ₗ T) (fun y => by
        have e : (fun k : Kinf E a × Kinf E b =>
            ev y (act (.cpt k.2) (sl₂ F (x.1 * infGL E a (Unitary.toUnits k.1))))) =
            fun k => F ((x.1, y) * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2))) :=
          funext fun k => (sl₂_val hS hF _ _).trans rfl
        rw [e]
        exact hty.2 (x.1, y))
    convert h using 2 with k
    have e := hT (.cpt k.2) _ (sl₂_mem hS hF (x.1 * infGL E a (Unitary.toUnits k.1)))
    change _ = (T (act (.cpt k.2) (sl₂ F (x.1 * infGL E a (Unitary.toUnits k.1))))).1 x.2
    rw [e]
    rfl

theorem ap₂_hecke (hS : PairSlices) {ι : Type} [Fintype ι] (hU : _root_.GlobalTheory.CuspRep.IsStable U₂) (T : Sm E b →ₗ[ℂ] Sm E b)
    (hT : ∀ o, ∀ ψ ∈ U₂, T (act o ψ) = act o (T ψ)) {f : ι → H E a b → ℂ}
    (hf : ∀ i, f i ∈ pairSpace U₁ U₂) (h : HeckeM E a b ι) (c : ℂ) (hh : heckeAct h f = c • f) :
    heckeAct h (fun i => ap₂ T (f i)) = c • fun i => ap₂ T (f i) := by
  funext i x
  have e : heckeAct h f i = ∑ j, ∑ g ∈ (h i j).support, (h i j g) • fun y => f j (y * finH g) := by
    funext y
    simp [heckeAct, Finsupp.sum, Finset.sum_apply]
  have e₁ : ap₂ T (heckeAct h f i) = c • ap₂ T (f i) := by
    rw [hh]
    exact ap₂_smul hS T c (hf i)
  have e₂ : ap₂ T (heckeAct h f i) x = ∑ j, ∑ g ∈ (h i j).support, h i j g * ap₂ T (f j) (x * finH g) := by
    rw [e, ap₂_sum (U₁ := ⊤) (U₂ := U₂) hS T _ _ fun j _ =>
      Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (rt_mem hU (hf j) g), Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ap₂_sum (U₁ := ⊤) (U₂ := U₂) hS T _ _ fun g _ => Submodule.smul_mem _ _ (rt_mem hU (hf j) g),
      Finset.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [ap₂_smul (U₁ := ⊤) (U₂ := U₂) hS T _ (rt_mem hU (hf j) g), Pi.smul_apply, smul_eq_mul,
      ap₂_rt hS T hT (hf j) g x]
  have e₃ : heckeAct h (fun i => ap₂ T (f i)) i x =
      ∑ j, ∑ g ∈ (h i j).support, h i j g * ap₂ T (f j) (x * finH g) := rfl
  rw [e₃, ← e₂, e₁]
  rfl

end GlobalTheory.CompanionTheory.EGlue.PairT₂

namespace GlobalTheory.CompanionTheory.EGlue

theorem pairStep₂ : PairSlices → PairStep₂ := by
  intro hS E _ _ _ a b ι _ K₁ K₂ W₁ W₂ U₁ U₂ U₂' T f fd₁ fd₂ hU hT hTU hf hty hne
  refine ⟨?_, fun i => PairT₂.ap₂_mem hS T hTU (hf i), fun i => PairT₂.ap₂_type hS fd₁ fd₂ T hT (hf i) (hty i),
    fun h c hh => PairT₂.ap₂_hecke hS hU T hT hf h c hh⟩
  obtain ⟨i, m, φ, hφ, hTφ⟩ := hne
  intro h0
  apply hTφ
  refine Subtype.ext (funext fun y => ?_)
  have e : sl₂ (f i) m = φ := PairT₂.sl₂_eq hφ
  have h1 : ap₂ T (f i) (m, y) = 0 := congrFun (congrFun h0 i) (m, y)
  change (T (sl₂ (f i) m)).1 y = 0 at h1
  rw [e] at h1
  exact h1

end GlobalTheory.CompanionTheory.EGlue

end
end

section


theorem _root_.GlobalTheory.T.character_conductor_condition : PositivityTheory.SiegelWeilFormula.Gunr.PsiCond := by
  first | exact @GlobalTheory.CompanionTheory.PsiCondLoc.psiCond | exact GlobalTheory.CompanionTheory.PsiCondLoc.psiCond | (intros; apply GlobalTheory.CompanionTheory.PsiCondLoc.psiCond <;> assumption)
end

section


theorem _root_.GlobalTheory.T.coset_integral_unramified : PositivityTheory.SiegelWeilFormula.Gunr.CosetInt := by
  first | exact @GlobalTheory.CompanionTheory.CosetSum.integrable_iff_and_integral_eq | exact GlobalTheory.CompanionTheory.CosetSum.integrable_iff_and_integral_eq | (intros; apply GlobalTheory.CompanionTheory.CosetSum.integrable_iff_and_integral_eq <;> assumption)
end

section

theorem _root_.GlobalTheory.T.real_model_exists : PositivityTheory.RgBcC.RealD.ModelEx :=
  GlobalTheory.CompanionTheory.ModelS.modelEx_main
end
