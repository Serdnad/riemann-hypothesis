module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonUnipotentStabiliserPreservesTermsAndDatum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairInnerLatticesUnimodularPrimitive
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle143
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexNeZero
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle046
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle032
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle082
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle125
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle124
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle231
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle107
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselConstantBoundsOfGeTwoNPowFiveStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelUnitaryGroupOpNormPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOpNormPowerIntegralLtTopClosedSubgroupStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle223
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle151
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients

@[expose] public section

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegAsm.WeightInf

theorem invVol_nn {G : Type} [Group G] (A B : Subgroup G) : 0 ≤ GlobalTheory.HL.invVol A B := by
  unfold GlobalTheory.HL.invVol
  positivity

theorem invVol_pos' {G : Type} [Group G] (A B : Subgroup G) (h1 : A.relIndex B ≠ 0) (h2 : B.relIndex A ≠ 0) :
    0 < GlobalTheory.HL.invVol A B := by
  unfold GlobalTheory.HL.invVol
  have h1' := Nat.pos_of_ne_zero h1
  have h2' := Nat.pos_of_ne_zero h2
  positivity

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), (∀ (N : NF H r) (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → 0 < N.om Λ ∧ ∀ s ∈ N.R, N.om (s • Λ) = N.om Λ) ∧ ∀ (F F' : FlagD H r) (𝔡 : Ideal (𝓞 K)) (Λ : Submodule (𝓞 K) V), 0 ≤ omI F F' 𝔡 Λ ∧ (∀ N : NF H r, Adapt F F' 𝔡 N → omI F F' 𝔡 Λ ≤ N.om Λ) ∧ ∀ a c : ℝ, 0 ≤ c → (∃ N : NF H r, Adapt F F' 𝔡 N) → (∀ N : NF H r, Adapt F F' 𝔡 N → a ≤ c * N.om Λ) → a ≤ c * omI F F' 𝔡 Λ := by
  intro K V _ _ _ _ _ _ _ _ H hK r
  refine ⟨?_, ?_⟩
  · intro N g Λ hg hT
    have hnil := (GlobalTheory.UnipStab.common_unipotent_stabiliser K V H hK r N).2.2.2.2
    have href := (GlobalTheory.DegCnt.InnerLat.main K V H hK r N g Λ hg hT).2.2.2.2.1
    have hΛdata := ((isUnimod_iff H Λ).1 hT.1.1).1
    have hΛ : Submodule.IsFullLattice K Λ :=
      { toIsLattice := Submodule.IsLattice.of_fg K hΛdata.1, span_eq_top := hΛdata.2 }
    have hrefFull : Submodule.IsFullLattice K (N.Ref (latL N.F N.F' Λ)) := by
      refine { toIsLattice := href, span_eq_top := ?_ }
      obtain ⟨-, -, hC, -, hWn, hUp, -, -, -, -, -, hPi⟩ :=
        GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
      have hP : N.Pi ≤ Submodule.span K (N.Ref (latL N.F N.F' Λ) : Set V) := by
        rw [hPi, ← GlobalTheory.DegCnt.InnerLat.span_hermFramePair_lattice_eq_sup N]
        exact Submodule.span_mono (show (N.P0 : Set V) ⊆ N.Ref (latL N.F N.F' Λ) from
          fun _ hx => Submodule.mem_sup_left hx)
      have hW : N.Wt ≤ Submodule.span K (N.Ref (latL N.F N.F' Λ) : Set V) := by
        intro x hx
        have hxW : x ∈ N.Wn := by rw [hWn]; exact Submodule.mem_sup_left hx
        obtain ⟨c, hc, hcx⟩ := GlobalTheory.DegCnt.InnerLat.exists_mult hΛdata.2 x
        rw [← Submodule.smul_mem_iff _ hc]
        apply Submodule.subset_span
        apply Submodule.mem_sup_right
        refine ⟨⟨?_, Submodule.mem_sup_left hcx⟩, N.Wn.smul_mem c hxW⟩
        rw [hUp]
        exact Submodule.mem_sup_left (N.Wn.smul_mem c hxW)
      apply eq_top_iff.mpr
      rw [← hC.sup_eq_top]
      exact sup_le hW hP
    have h1 := GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R (2 * r + 1) hnil Λ _ hΛ hrefFull
    have h2 := GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R (2 * r + 1) hnil _ Λ hrefFull hΛ
    refine ⟨invVol_pos' _ _ h2.1 h1.1, fun s hs => ?_⟩
    have h3 := (GlobalTheory.DegCnt.StabInv.main K V H hK r N g Λ hg hT s hs).2.1.1
    unfold NF.om
    rw [h3]
    exact h1.2 s hs
  · intro F F' 𝔡 Λ
    have hnn : ∀ x ∈ ((fun N : NF H r => N.om Λ) '' {N | Adapt F F' 𝔡 N}), (0 : ℝ) ≤ x := by
      rintro _ ⟨N, -, rfl⟩
      exact invVol_nn _ _
    refine ⟨Real.sInf_nonneg hnn, fun N hN => csInf_le ⟨0, hnn⟩ ⟨N, hN, rfl⟩, ?_⟩
    rintro a c hc ⟨N₀, hN₀⟩ h
    rcases hc.eq_or_lt with rfl | hc
    · simpa using h N₀ hN₀
    · rw [← div_le_iff₀' hc]
      refine le_csInf ⟨_, N₀, hN₀, rfl⟩ ?_
      rintro _ ⟨N, hN, rfl⟩
      rw [div_le_iff₀' hc]
      exact h N hN

end GlobalTheory.DegAsm.WeightInf
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem sumData_nT_eq_mass : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (C : Set S.FrP) (P : S.Datum → Submodule L.O S.V → Prop), (∀ h ∈ S.H0, ∀ d Λ, S.IsTerm d Λ → P d Λ → P (h • d) (h • Λ)) → (S.sumData fun d => S.nT d C (P d)) = ∑' o : MulAction.orbitRel.Quotient S.H0 (Submodule L.O S.V), if ∃ d, S.IsTerm d o.out ∧ P d o.out ∧ S.Fr d o.out = C then ENNReal.ofReal (invVol S.complementReferenceCompactSubgroup (S.H0 ⊓ MulAction.stabilizer S.GLV o.out)) else 0 := by
  intro F _ _ _ _ _ E _ _ _ L r k S C P hP
  let π : Submodule L.O S.V → S.Datum := fun Λ =>
    if H : ∃ d, S.IsTerm d Λ then H.choose else (⊥, ⊥, ∅)
  have hπ : ∀ d Λ, S.IsTerm d Λ → π Λ = d := by
    intro d Λ hd
    have H : ∃ d, S.IsTerm d Λ := ⟨d, hd⟩
    simp only [π, dif_pos H]
    exact (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hd).2.2.2.2.2.2.2 _ H.choose_spec
  obtain ⟨v1, v2⟩ := GlobalTheory.HL.Frames.stab_commensurable_invVol_smul L r k S
  have hlat : ∀ d Λ, S.IsTerm d Λ → IsLat L Λ := fun d Λ hd =>
    (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hd).1.1
  have key := mass_orbits_eq_tsum_fiber S.H0 S.complementReferenceCompactSubgroup
    (fun Λ : Submodule L.O S.V => ∃ d, S.IsTerm d Λ ∧ P d Λ ∧ S.Fr d Λ = C) π inf_le_left
    (by
      rintro h hh Λ ⟨d, hd, hp, hc⟩
      obtain ⟨a1, -, -, -, -, a6⟩ := GlobalTheory.HL.ComplAct.main L r k S d Λ hd h hh
      refine ⟨⟨h • d, a1, hP h hh d Λ hd hp, a6.trans hc⟩, ?_, (v1 Λ (hlat d Λ hd)).2.2 h hh⟩
      rw [hπ _ _ a1, hπ _ _ hd])
    (by
      rintro Λ ⟨d, hd, -, -⟩
      rw [hπ _ _ hd]
      exact ⟨(v1 Λ (hlat d Λ hd)).1, (v1 Λ (hlat d Λ hd)).2.1, (v2 d Λ hd).1, (v2 d Λ hd).2⟩)
  refine Eq.trans ?_ (key.symm.trans ?_)
  · unfold Frames.sumData Frames.nu Frames.nT
    refine tsum_congr fun c => ?_
    refine congrArg (fun s : Set (Submodule L.O S.V) => _ * ((s.encard : ℕ∞) : ℝ≥0∞)) ?_
    ext Λ
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hd, hp, hc⟩
      exact ⟨⟨_, hd, hp, hc⟩, hπ _ _ hd⟩
    · rintro ⟨⟨d, hd, hp, hc⟩, e⟩
      rw [hπ _ _ hd] at e
      rw [← e]
      exact ⟨hd, hp, hc⟩
  · refine tsum_congr fun o => ?_
    congr

end GlobalTheory.HL
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.CuspFixed

theorem isHaarSub_map_emb {H G : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (ι : H →* G) (hι : Topology.IsClosedEmbedding ι) (N : Subgroup H)
    (hN : IsClosed (N : Set H)) (ν : Measure H) (hν : IsHaarSub (N : Set H) ν) :
    IsClosed ((N.map ι : Subgroup G) : Set G) ∧ IsHaarSub ((N.map ι : Subgroup G) : Set G) (ν.map ι) := by
  have hme : MeasurableEmbedding ι := hι.measurableEmbedding
  have hS : ((N.map ι : Subgroup G) : Set G) = ι '' (N : Set H) := Subgroup.coe_map ι N
  obtain ⟨hne, hfc, hnull, hinv⟩ := hν
  refine ⟨by rw [hS]; exact hι.isClosedMap _ hN, ?_, ?_, ?_, ?_⟩
  · intro h0
    apply hne
    rwa [Measure.map_eq_zero_iff hme.measurable.aemeasurable] at h0
  · refine ⟨fun K hK => ?_⟩
    rw [hme.map_apply]
    exact hfc.lt_top_of_isCompact (hι.isCompact_preimage hK)
  · rw [hme.map_apply, Set.preimage_compl, hS, Set.preimage_image_eq _ hι.injective]
    exact hnull
  · intro m hm
    rw [hS] at hm
    obtain ⟨k, hk, rfl⟩ := hm
    have hcomm : (fun z : G => ι k * z) ∘ ι = ι ∘ (fun z : H => k * z) := by
      funext z
      simp only [Function.comp_apply, map_mul]
    rw [Measure.map_map (continuous_const_mul (ι k)).measurable hme.measurable, hcomm,
      ← Measure.map_map hme.measurable (continuous_const_mul k).measurable, hinv k hk]

theorem constTerm_repro {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ ν : Measure G) [SFinite μ]
    [μ.IsMulLeftInvariant] [IsFiniteMeasure ν] (f φ : G → ℂ) (hf : Continuous f) (hφ : Measurable φ) (x : G)
    (Φ : G → ℝ) (hΦ : Integrable Φ μ) (hb : ∀ᵐ m ∂ν, ∀ g, ‖φ g * f (m * x * g)‖ ≤ Φ g)
    (hr : ∀ z, f z = ∫ g, φ g * f (z * g) ∂μ) :
    Integrable (fun y => (∫ m, f (m * y) ∂ν) * φ (x⁻¹ * y)) μ ∧
      ∫ m, f (m * x) ∂ν = ∫ y, (∫ m, f (m * y) ∂ν) * φ (x⁻¹ * y) ∂μ := by
  have hmeas : Measurable (Function.uncurry fun (m g : G) => φ g * f (m * x * g)) := by
    apply Measurable.mul
    · exact hφ.comp measurable_snd
    · exact (hf.comp (by fun_prop : Continuous fun p : G × G => p.1 * x * p.2)).measurable
  have hint : Integrable (Function.uncurry fun (m g : G) => φ g * f (m * x * g)) (ν.prod μ) := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).mul_prod hΦ) hmeas.aestronglyMeasurable ?_
    have hae := (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := μ)).ae hb
    filter_upwards [hae] with p hp
    simpa [Function.uncurry] using hp p.2
  have hH : (fun g => ∫ m, φ g * f (m * x * g) ∂ν) =
      fun g => (fun y => (∫ m, f (m * y) ∂ν) * φ (x⁻¹ * y)) (x * g) := by
    funext g
    beta_reduce
    rw [integral_const_mul, inv_mul_cancel_left, mul_comm]
    simp_rw [mul_assoc]
  have hI : Integrable (fun g => ∫ m, φ g * f (m * x * g) ∂ν) μ := hint.integral_prod_right
  rw [hH] at hI
  have hI2 := hI.comp_mul_left x⁻¹
  simp only [mul_inv_cancel_left] at hI2
  refine ⟨hI2, ?_⟩
  calc ∫ m, f (m * x) ∂ν = ∫ m, ∫ g, φ g * f (m * x * g) ∂μ ∂ν := by
        congr 1; funext m; exact hr (m * x)
    _ = ∫ g, ∫ m, φ g * f (m * x * g) ∂ν ∂μ := integral_integral_swap hint
    _ = ∫ g, (fun y => (∫ m, f (m * y) ∂ν) * φ (x⁻¹ * y)) (x * g) ∂μ := by rw [hH]
    _ = ∫ y, (∫ m, f (m * y) ∂ν) * φ (x⁻¹ * y) ∂μ :=
        integral_mul_left_eq_self (fun y => (∫ m, f (m * y) ∂ν) * φ (x⁻¹ * y)) x

theorem continuous_phe (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (hd : IsDSData B d) : Continuous (phe B d) := by
  have he : Continuous B.e := (rowsAut_idem_elementary B).2.2.2
  have hv : ∀ v, Continuous (fun g : B.I.Ginf => B.σ v (uMat (g v)) (B.w v)) := by
    intro v
    have hc := ((hd v).2.1.2.2.1).2.2 (B.w v)
    exact hc.comp_continuous ((Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply v))
      (fun g => (g v).2)
  have hph : Continuous (ph B d) := by
    unfold ph
    exact continuous_const.mul
      (continuous_star.comp (continuous_finsetProd _ fun v _ => continuous_const.inner (hv v)))
  unfold phe
  exact (hph.comp continuous_fst).mul (he.comp continuous_snd)

theorem one_le_of_isIsot (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (hW : I.IsIsot W) : 1 ≤ I.n := by
  rcases Nat.eq_zero_or_pos I.n with h0 | hpos
  · exfalso
    apply hW.1
    rw [Submodule.eq_bot_iff]
    intro x _
    funext i
    exact absurd i.isLt (by omega)
  · exact hpos


open Classical in
noncomputable def incl (I : AutInst) (v : InfinitePlace I.F) : UJ (I.ε v) →* I.GA :=
  (MonoidHom.inl I.Ginf I.Gf).comp (MonoidHom.mulSingle (fun v => UJ (I.ε v)) v)

theorem isClosedEmbedding_incl (I : AutInst) (v : InfinitePlace I.F) : Topology.IsClosedEmbedding (incl I v) := by
  obtain ⟨hT2, -⟩ := CongTop.adelic_topology I
  haveI := hT2
  classical
  refine Function.LeftInverse.isClosedEmbedding (f := fun p : I.GA => p.1 v) ?_ ?_ ?_
  · intro m
    simp [incl]
  · exact (continuous_apply v).comp continuous_fst
  · exact (continuous_mulSingle (A := fun w : InfinitePlace I.F => UJ (I.ε w)) v).prodMk continuous_const

theorem cusp_of_fixed : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ (v : InfinitePlace B.I.F) (Wv : Submodule ℂ (Fin B.I.n → ℂ)), IsIsoC (B.I.ε v) Wv → ∀ ν : Measure (UJ (B.I.ε v)), IsHaarSub (NW (B.I.ε v) Wv) ν → ∀ x y : B.I.GA, ∫ m, phe B d (x * (open Classical in ((Pi.mulSingle v m, 1) : B.I.GA)) * y) ∂ν = 0) → LocDec B h → HBig B 40 h → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ (y : B.I.L2 B.μf B.fund) (f : B.I.GA → ℂ) (C : ℝ), T y = y → IsContRep B y f → (∀ x, ‖f x‖ ≤ C * (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f)) → (∀ W, B.I.IsIsot W → ∀ ν : Measure B.I.GA, B.I.IsNQuotMeas W ν → ∀ x, ∫ m, f (m * x) ∂ν = 0) ∧ B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext y) := by
  intro B d h hd hfib hloc hbig T hT y f C hfix hrep hgr
  obtain ⟨hT2, hLC, hSC, -⟩ := CongTop.adelic_topology B.I
  haveI := hT2
  haveI := hLC
  haveI := hSC
  haveI hHaar : (B.I.muA B.μf).IsHaarMeasure := by
    haveI h1 : ∀ w, (muG (B.I.ε w)).IsHaarMeasure := fun w => inferInstance
    haveI h2 : ∀ w, SigmaFinite (muG (B.I.ε w)) := fun w => inferInstance
    haveI h3 : (Measure.pi fun w => muG (B.I.ε w)).IsHaarMeasure := Measure.pi.isHaarMeasure _
    haveI h4 : SFinite (Measure.pi fun w => muG (B.I.ε w)) := inferInstance
    haveI h5 : SFinite B.μf := inferInstance
    unfold AutInst.muA
    exact Measure.prod.instIsHaarMeasure _ _
  have main : ∀ W, B.I.IsIsot W → ∀ ν : Measure B.I.GA, B.I.IsNQuotMeas W ν →
      ∀ x, ∫ m, f (m * x) ∂ν = 0 := by
    intro W hW ν hνW x
    have hn : 1 ≤ B.I.n := one_le_of_isIsot B.I W hW
    obtain ⟨⟨Φ, hΦi, hΦb⟩, hrepf⟩ := GlobalTheory.T.reproducing_formula_fixedVector_moderateGrowth B d h hd hn hloc hbig T hT y f C hfix hrep hgr
    obtain ⟨hfin, -, hconc, hinvN⟩ := hνW
    haveI := hfin
    obtain ⟨c, hc0, hc⟩ := exists_pos_le_tau1_mul_of_mem_NA_of_isIsot B.I W x hW
    have hbd : ∀ᵐ m ∂ν, ∀ g, ‖phe B d g * f (m * x * g)‖ ≤
        c⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * Φ g := by
      filter_upwards [mem_ae_iff.mpr hconc] with m hm g
      have ht : c ≤ tau1 B.I (m * x) := hc m hm
      have htpos : 0 < tau1 B.I (m * x) := hc0.trans_le ht
      have hb1 := hΦb (m * x) g
      have hpow : 0 < (tau1 B.I (m * x))⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) :=
        pow_pos (inv_pos.mpr htpos) _
      have hΦ0 : 0 ≤ Φ g := (mul_nonneg_iff_of_pos_left hpow).mp ((norm_nonneg _).trans hb1)
      exact hb1.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (inv_nonneg.mpr htpos.le) (inv_anti₀ hc0 ht) _) hΦ0)
    obtain ⟨hint, heq⟩ := constTerm_repro (B.I.muA B.μf) ν f (phe B d) hrep.1
      (continuous_phe B d hd).measurable x (fun g => c⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * Φ g)
      (hΦi.const_mul _) hbd hrepf
    rw [heq]
    obtain ⟨v⟩ : Nonempty (InfinitePlace B.I.F) := inferInstance
    obtain ⟨Wv, hWv, hemb⟩ := RadEmb.radical_embeds B.I W v hW
    obtain ⟨νv, hνv⟩ := exists_isHaarSub_NW (B.I.ε v) Wv
    have hNcl : IsClosed ((nwSub (B.I.ε v) Wv : Subgroup (UJ (B.I.ε v))) : Set (UJ (B.I.ε v))) := by
      rw [coe_nwSub]
      exact isClosed_NW _ _
    have hνv' : IsHaarSub ((nwSub (B.I.ε v) Wv : Subgroup (UJ (B.I.ε v))) : Set (UJ (B.I.ε v))) νv := by
      rw [coe_nwSub]
      exact hνv
    have hemb' := isClosedEmbedding_incl B.I v
    obtain ⟨hNcl', hHs⟩ := isHaarSub_map_emb (incl B.I v) hemb' _ hNcl νv hνv'
    refine weilVanish B.I.GA (B.I.muA B.μf) _ _ hNcl' hHs (fun z => ∫ m, f (m * z) ∂ν)
      (fun z => phe B d (x⁻¹ * z)) ?_ ?_ ?_ hint ?_
    · exact (StronglyMeasurable.integral_prod_right' (ν := ν)
        (f := fun p : B.I.GA × B.I.GA => f (p.2 * p.1))
        (hrep.1.comp (continuous_snd.mul continuous_fst)).stronglyMeasurable).measurable
    · exact ((continuous_phe B d hd).comp (continuous_const.mul continuous_id)).measurable
    · intro n hn z
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hn
      have hk' : k ∈ NW (B.I.ε v) Wv := by
        rw [← coe_nwSub]
        exact hk
      have hkNA : incl B.I v k ∈ B.I.NA W := hemb k hk'
      have hsh := hinvN (fun m => f (m * z)) (fun γ hγ w => by
        show f (γ * w * z) = f (w * z)
        rw [mul_assoc]
        exact hrep.2.1 γ hγ.1 (w * z)) (incl B.I v k) hkNA
      show ∫ m, f (m * (incl B.I v k * z)) ∂ν = ∫ m, f (m * z) ∂ν
      simpa only [mul_assoc] using hsh
    · intro z
      rw [hemb'.measurableEmbedding.integral_map]
      have hz := hfib v Wv hWv νv hνv x⁻¹ z
      simp only [← mul_assoc]
      exact hz
  refine ⟨main, ?_⟩
  intro W hW ν hνW
  have hae := (ExtContRep.ext_ae_eq_contRep B y f hrep).2.2.2 ν hνW.1
  filter_upwards [hae] with x hx
  rw [integral_congr_ae hx]
  exact main W hW ν hνW x

end GlobalTheory.CuspFixed
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf

theorem integrable_opn_rpow_neg {k r : ℕ} (μ : Measure (Mt k r)) (A : ℝ)
    (hc : Continuous fun x : Mat k r => opn x) (h : normInt μ A < ⊤) :
    Integrable (fun x : Mt k r => opn (Matrix.of x) ^ (-A)) μ := by
  have hm : Measurable fun x : Mt k r => opn (Matrix.of x) ^ (-A) :=
    (show Continuous fun x : Mt k r => opn (Matrix.of x) from hc).measurable.pow_const _
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (opn_nonneg _) _)).2 h

theorem rpow_fubini_ineq {x y t a : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (ht : 0 < t) (hyt : t / x ≤ y)
    (ha : 0 ≤ a) : x ^ (-a) * y ^ (-a) ≤ x ^ (-(a / 2)) * t ^ (-(a / 2)) := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have h1 : y ^ (-a) ≤ y ^ (-(a / 2)) := Real.rpow_le_rpow_of_exponent_le hy (by linarith)
  have h2 : y ^ (-(a / 2)) ≤ (t / x) ^ (-(a / 2)) :=
    Real.rpow_le_rpow_of_nonpos (div_pos ht hx0) hyt (by linarith)
  have h3 : (t / x) ^ (-(a / 2)) = t ^ (-(a / 2)) / x ^ (-(a / 2)) := Real.div_rpow ht.le hx0.le _
  have h4 : x ^ (-a) = x ^ (-(a / 2)) * x ^ (-(a / 2)) := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hxp : 0 < x ^ (-(a / 2)) := Real.rpow_pos_of_pos hx0 _
  calc x ^ (-a) * y ^ (-a) ≤ x ^ (-a) * ((t / x) ^ (-(a / 2))) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (Real.rpow_nonneg hx0.le _)
    _ = x ^ (-(a / 2)) * t ^ (-(a / 2)) := by
        rw [h3, h4]; field_simp

theorem fubini_bound : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ v₁ ∈ DD σ w, Integrable (fun p : Mt k r × Mt k r => coef σ u v (Matrix.of p.1) * star (coef σ u₁ v₁ (Matrix.of p.2 * Matrix.of p.1))) (μG.prod μS) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv v₁ hv₁
  obtain ⟨hk, hrep, -, -, hHG, -, ha, hdec, -⟩ := hStd
  obtain ⟨hz, hT, -, hHS, -⟩ := hSide
  obtain ⟨hGc, -, -, hSc, -⟩ := GlobalTheory.SgInf.closedSub_groups k r z hz hT
  obtain ⟨hN1, -, hNc, -, -, -, hN7, -⟩ := GlobalTheory.T.besselModelUnitaryGroup_opNorm_properties k r
  have hA := (GlobalTheory.T.bessel_constant_bounds_of_ge_two_n_pow_five k r a hk ha).1
  have hIG := GlobalTheory.T.besselOpNormPowerIntegral_lt_top_closedSubgroup k r (GG k r) μG (a / 2) hGc hHG hA
  have hIS := GlobalTheory.T.besselOpNormPowerIntegral_lt_top_closedSubgroup k r (Sset k r z) μS (a / 2) hSc hHS hA
  obtain ⟨C, hC⟩ := hdec u hu v hv
  obtain ⟨C₁, hC₁⟩ := hdec u₁ hu₁ v₁ hv₁
  haveI := hHG.1
  haveI := hHS.1
  have ha0 : 0 ≤ a := le_trans (by positivity) ha
  set T : Set (Mt k r × Mt k r) := {p | Matrix.of p.1 ∈ GG k r ∧ Matrix.of p.2 ∈ Sset k r z} with hTdef
  have hTm : MeasurableSet T := by
    have h1 : IsClosed {p : Mt k r × Mt k r | Matrix.of p.1 ∈ GG k r} :=
      hGc.2.1.preimage continuous_fst
    have h2 : IsClosed {p : Mt k r × Mt k r | Matrix.of p.2 ∈ Sset k r z} :=
      hSc.2.1.preimage continuous_snd
    exact (h1.inter h2).measurableSet
  have hTae : ∀ᵐ p ∂(μG.prod μS), p ∈ T := by
    rw [ae_iff]
    refine measure_mono_null (t := ({x : Mt k r | Matrix.of x ∉ GG k r} ×ˢ Set.univ) ∪
      (Set.univ ×ˢ {x : Mt k r | Matrix.of x ∉ Sset k r z})) ?_ ?_
    · intro p hp
      simp only [Set.mem_setOf_eq, hTdef, not_and_or] at hp
      rcases hp with hp | hp
      · exact Or.inl ⟨hp, trivial⟩
      · exact Or.inr ⟨trivial, hp⟩
    · refine measure_union_null ?_ ?_
      · rw [Measure.prod_prod, hHG.2.2.1, zero_mul]
      · rw [Measure.prod_prod, hHS.2.2.1, mul_zero]
  have hg : Integrable (fun p : Mt k r × Mt k r => (|C| * |C₁|) *
      (opn (Matrix.of p.1) ^ (-(a / 2)) * opn (Matrix.of p.2) ^ (-(a / 2)))) (μG.prod μS) :=
    ((integrable_opn_rpow_neg μG _ hNc hIG).mul_prod (integrable_opn_rpow_neg μS _ hNc hIS)).const_mul _
  have hcont : ContinuousOn (fun p : Mt k r × Mt k r =>
      coef σ u v (Matrix.of p.1) * star (coef σ u₁ v₁ (Matrix.of p.2 * Matrix.of p.1))) T := by
    have c1 : ContinuousOn (fun p : Mt k r × Mt k r => σ (Matrix.of p.1) u) T :=
      (hrep.2.2 u).comp (continuous_fst.continuousOn) (fun p hp => hp.1)
    have hmul : Continuous fun p : Mt k r × Mt k r => (Matrix.of p.2 * Matrix.of p.1 : Mat k r) :=
      (continuous_snd (X := Mat k r) (Y := Mat k r)).matrix_mul continuous_fst
    have c2 : ContinuousOn (fun p : Mt k r × Mt k r => σ (Matrix.of p.2 * Matrix.of p.1) u₁) T :=
      (hrep.2.2 u₁).comp hmul.continuousOn
        (fun p hp => hGc.2.2.2.1 _ (hSc.1 hp.2) _ hp.1)
    exact (continuousOn_const.inner c1).mul (continuous_star.comp_continuousOn (continuousOn_const.inner c2))
  refine hg.mono' ?_ ?_
  · have := hcont.aestronglyMeasurable (μ := μG.prod μS) hTm
    rwa [Measure.restrict_eq_self_of_ae_mem hTae] at this
  · filter_upwards [hTae] with p hp
    obtain ⟨hpG, hpS⟩ := hp
    have hSG : Matrix.of p.2 ∈ GG k r := hSc.1 hpS
    have hyG : (Matrix.of p.2 * Matrix.of p.1 : Mat k r) ∈ GG k r := hGc.2.2.2.1 _ hSG _ hpG
    have hx1 := (hN1 _ hpG).2
    have ht1 := (hN1 _ hSG).2
    have hy1 := (hN1 _ hyG).2
    have hyt : opn (Matrix.of p.2 : Mat k r) / opn (Matrix.of p.1 : Mat k r) ≤
        opn (Matrix.of p.2 * Matrix.of p.1 : Mat k r) := (hN7 _ hSG _ hpG).1
    have e1 : ‖coef σ u v (Matrix.of p.1)‖ ≤ |C| * opn (Matrix.of p.1 : Mat k r) ^ (-a) :=
      (hC _ hpG).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (opn_nonneg _) _))
    have e2 : ‖coef σ u₁ v₁ (Matrix.of p.2 * Matrix.of p.1)‖ ≤
        |C₁| * opn (Matrix.of p.2 * Matrix.of p.1 : Mat k r) ^ (-a) :=
      (hC₁ _ hyG).trans (mul_le_mul_of_nonneg_right (le_abs_self C₁) (Real.rpow_nonneg (opn_nonneg _) _))
    have key := rpow_fubini_ineq hx1 hy1 (lt_of_lt_of_le one_pos ht1) hyt ha0
    rw [norm_mul, norm_star]
    calc ‖coef σ u v (Matrix.of p.1)‖ * ‖coef σ u₁ v₁ (Matrix.of p.2 * Matrix.of p.1)‖
        ≤ (|C| * opn (Matrix.of p.1 : Mat k r) ^ (-a)) *
            (|C₁| * opn (Matrix.of p.2 * Matrix.of p.1 : Mat k r) ^ (-a)) :=
          mul_le_mul e1 e2 (norm_nonneg _) (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (opn_nonneg _) _))
      _ = (|C| * |C₁|) * (opn (Matrix.of p.1 : Mat k r) ^ (-a) *
            opn (Matrix.of p.2 * Matrix.of p.1 : Mat k r) ^ (-a)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left key (mul_nonneg (abs_nonneg _) (abs_nonneg _))

end GlobalTheory.SgInf
end
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.isUnimodular_besselModelUnitaryGroup : ∀ (k r : ℕ) (μ : Measure (Mt k r)), IsHaarOn (GG k r) μ → IsUnimod (GG k r) μ := by
  first | exact @GlobalTheory.SgInf.isUnimod_GG | exact GlobalTheory.SgInf.isUnimod_GG | (intros; apply GlobalTheory.SgInf.isUnimod_GG <;> assumption)
end
