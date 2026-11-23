module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle430
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle276
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle123
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle417
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle374
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle433
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle417
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle110
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle402
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle436
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.GroupRetwisting

theorem pass_step_congr {α : Type*} (g : ∀ P : Pre, Fr P → α) {P P' : Pre} {f : Fr P} {f' : Fr P'} (h : P = P') (hf : HEq f f') :
    g P f = g P' f' := by
  subst h
  rw [eq_of_heq hf]

theorem pass_step : ∀ (KP : BaseP) (Q : V4.Slot) (r r' : AtP), BaseCond KP → Pass KP Q r → Step KP r r' → Pass KP Q r' := by
  classical
  intro KP Q r r' hK hR hS
  refine (EvG.inter hS hR).imp fun K _ _ _ _ H => ?_
  obtain ⟨hs, hr⟩ := H
  have hs' : large₂ K fun B f T => KP B f → r K B f T → r' K B f T :=
    (hs.inter (lg_forced K)).imp fun _ _ _ _ G a b => G.1 a G.2 b
  obtain ⟨S₁, P₁, A₀, S₂₀, a₁, a₂, hlg⟩ := hs'
  have hb : large₂ K fun B f T => (∀ z ∈ S₁ B.toPre f B.KsC, z ∈ B.fixedCoefficientFieldInComplex) ∧ P₁ B.toPre f B.KsC B.fixedCoefficientFieldInComplex ⊆ T.pl :=
    ⟨S₁, P₁, fun _ _ _ _ _ => ∅, S₂₀, a₁, a₂, fun _ _ _ _ h p _ => ⟨h.1, p⟩⟩
  refine (hr.inter hb).imp ?_
  rintro B f T hO ⟨hr, h₁, hp⟩ hKP hT C W V S N G c q hx A S₂ hS₂
  obtain ⟨B', f', T', e, hf, hpl, hAv, hS', hr'⟩ := hr hKP hT C W V S N G c q hx
    (fun l => A l ∪ A₀ B.toPre f B.KsC B.fixedCoefficientFieldInComplex l) (fun P g Ξ => S₂ P g Ξ ∪ S₂₀ P g B.KsC B.fixedCoefficientFieldInComplex Ξ)
    (fun P g Ξ z hz => (Finset.mem_union.1 hz).elim (hS₂ P g Ξ z) (a₂ P g _ _ Ξ z))
  have hP : B'.toPre = B.toPre := e.1
  have hk : B'.KsC = B.KsC := e.KsC_eq
  have hl : B'.fixedCoefficientFieldInComplex = B.fixedCoefficientFieldInComplex := e.fixedCoefficientField_eq
  have hO' : K.Over B'.toPre := hP ▸ hO
  have hLL : ∀ z ∈ S₂₀ B'.toPre f' B'.KsC B'.fixedCoefficientFieldInComplex (T'.set f'), z ∈ B'.LLC := by
    intro z hz
    rw [hk, hl] at hz
    obtain ⟨x, rfl⟩ := hS' z (Finset.mem_union_right _ hz)
    exact ⟨x, rfl⟩
  have r'' := hlg B' f' T' hO'
    ⟨by rw [hk, hl, pass_step_congr S₁ hP hf]; exact h₁, hLL⟩
    (by rw [hk, hl, pass_step_congr P₁ hP hf, hpl]; exact hp)
    (fun w v hv hA => hAv w v hv (Finset.mem_union_right _ (by
      rw [hk, hl, pass_step_congr A₀ hP hf] at hA; exact hA)))
    (hK.enl B B' f f' e hf hKP) hr'
  exact ⟨B', f', T', e, hf, hpl, fun w v hv hA => hAv w v hv (Finset.mem_union_left _ hA),
    fun z hz => hS' z (Finset.mem_union_left _ hz), r''⟩

end GlobalTheory.Mem.Top.GroupRetwisting
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.layeredAutomorphicData_exists_of_twoPasses : (∀ D : D7, Formalism.L2.Theta.VolTieG D → StandardLattice.VolumeEqMass₂ D) → ∀ (KP : GroupRetwisting.BaseP) (Q Q' : V4.Slot), GroupRetwisting.BaseCond KP → GroupRetwisting.FirstG KP Q → GroupRetwisting.ExportF KP Q → GroupRetwisting.SecondG KP Q Q' → RecAtG (fun K D Y => GroupRetwisting.FromCoreAt Q' K D Y ∧ DQ.TupUsedAt D ∧ DQ.TwAllAt D Y.nch Y.xd ∧ DQ.MtStableAt D) := by
  first | exact @GlobalTheory.Mem.Top.GroupRetwisting.recAtG_of_two_passes | exact GlobalTheory.Mem.Top.GroupRetwisting.recAtG_of_two_passes | (intros; apply GlobalTheory.Mem.Top.GroupRetwisting.recAtG_of_two_passes <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FixedAtSplit

open Filter Topology IsDedekindDomain

theorem exists_ne_zero_norm_lt_one {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ ϖ : v.adicCompletion F, ϖ ≠ 0 ∧ ‖ϖ‖ < 1 := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  refine ⟨(π : v.adicCompletion F), ?_, ?_⟩
  · intro h0
    have := v.valuedAdicCompletion_eq_valuation' π
    rw [h0, map_zero, hπ] at this
    exact WithZero.coe_ne_zero this.symm
  · rw [Valued.toNormedField.norm_lt_one_iff, v.valuedAdicCompletion_eq_valuation', hπ]
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num

theorem valued_lt_one_of_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (c : v.adicCompletion F ≃+* w.adicCompletion E) (hc : Continuous c) (z : v.adicCompletion F)
    (hz : Valued.v (c z) < 1) : Valued.v z < 1 := by
  rw [← Valued.toNormedField.norm_lt_one_iff] at hz ⊢
  have h1 : ∀ y : v.adicCompletion F, ‖y‖ < 1 → ‖c y‖ < 1 := fun y hy => by
    have h2 := (hc.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.2 hy)
    rw [map_zero] at h2
    refine tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 ?_
    simpa [Function.comp_def, map_pow] using h2
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := exists_ne_zero_norm_lt_one v
  by_contra h
  push_neg at h
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [norm_zero] at h
    norm_num at h
  have hcz0 : 0 < ‖c z‖ := norm_pos_iff.2 ((map_ne_zero c).2 hz0)
  have hcϖ : 0 < ‖c ϖ‖ := norm_pos_iff.2 ((map_ne_zero c).2 hϖ0)
  have key : ∀ N : ℕ, ‖c ϖ‖ < ‖c z‖ ^ N := by
    intro N
    have hzN : 1 ≤ ‖z‖ ^ N := one_le_pow₀ h
    have hq : ‖ϖ / z ^ N‖ < 1 := by
      rw [norm_div, norm_pow, div_lt_one (by positivity)]
      exact lt_of_lt_of_le hϖ1 hzN
    have := h1 _ hq
    rw [map_div₀, map_pow, norm_div, norm_pow, div_lt_one (by positivity)] at this
    exact this
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (c z)) hz
  obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds hcϖ)).exists
  exact lt_asymm hN (key N)

end GlobalTheory.FixedAtSplit

namespace GlobalTheory.FixedAtSplit

open IsDedekindDomain ValuativeRel

theorem mem_KOne_iff' {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    (κ : GL (Fin n) (w.adicCompletion E)) :
    κ ∈ GlobalTheory.SplitWeil.KOne (w.adicCompletion E) (Fin n) ↔
      ∀ a b, Valued.v (((κ : Matrix (Fin n) (Fin n) (w.adicCompletion E)) - 1) a b) < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [GlobalTheory.StepData.mem_KOne]
  exact forall_congr' fun a => forall_congr' fun b => he.lt_one_iff_lt_one

theorem mem_KOne_of_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (c : v.adicCompletion F ≃+* w.adicCompletion E) (hc : Continuous c) {n : ℕ}
    (A : GL (Fin n) (v.adicCompletion F))
    (h : Matrix.GeneralLinearGroup.map c.toRingHom A ∈ GlobalTheory.SplitWeil.KOne (w.adicCompletion E) (Fin n)) :
    A ∈ GlobalTheory.SplitWeil.KOne (v.adicCompletion F) (Fin n) := by
  refine (mem_KOne_iff' A).2 fun a b => valued_lt_one_of_map c hc _ ?_
  have := (mem_KOne_iff' _).1 h a b
  convert this using 2
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.GeneralLinearGroup.map_apply]
  split_ifs <;> simp

end GlobalTheory.FixedAtSplit

namespace GlobalTheory.FixedAtSplit

theorem fixed_ne_bot_of_fixed_vector : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.FinTyp L n) (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), GlobalTheory.HeightCounting.IsLocS π.S s τ → ∀ f ∈ π.S, f ≠ 0 → (∀ κ : Formalism.AUTREP.GAf L n, TrivOutside {s.v} κ → s.loc n κ ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n) → NG.rt L n κ f = f) → GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KOne (s.w.adicCompletion L) (Fin n)) ≠ ⊥ := by
  intro L _ _ _ n π s τ hloc f hf hf0 hfix
  classical
  obtain ⟨c, _, hc, hci, _⟩ := id hloc
  have hspan := GlobalTheory.T.finiteType_spanned_by_splitPlace_localComponent L n π s τ hloc c hc hci hf
  let H : Subgroup (GAf L n) :=
    { carrier := {x | TrivOutside {s.v} x}
      mul_mem' := fun {x y} hx hy v hv => by
        simp only [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul, hx v hv, hy v hv, mul_one]
      one_mem' := fun v _ => by simp
      inv_mem' := fun {x} hx v hv => by
        have h1 : (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
            ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := by simp
        have h2 := congrArg (fun M => Matrix.map M (compAt L v)) h1
        simp only [Matrix.map_mul, hx v hv, mul_one, Matrix.map_one _ (map_zero _) (map_one _)] at h2
        exact h2 }
  let φ : H →* GL (Fin n) (s.w.adicCompletion L) :=
    (Matrix.GeneralLinearGroup.map c.toRingHom).comp ((s.loc n).comp H.subtype)
  have hφ : Function.Surjective φ := by
    intro h
    obtain ⟨x, hx, e⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s
      (Matrix.GeneralLinearGroup.map c.symm.toRingHom h)
    refine ⟨⟨x, hx⟩, ?_⟩
    change Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) = h
    rw [e]
    ext i j
    simp
  let σ' : Representation ℂ H τ.V := τ.ρ.comp φ
  have hσ' : σ'.IsIrreducible := GlobalTheory.CuspRep.ParLaws.isIrreducible_comp τ.irr φ hφ
  let ρ' : Representation ℂ H (GAf L n → ℂ) :=
    { toFun := fun x => NG.rt L n (x : GAf L n)
      map_one' := by
        apply LinearMap.ext
        intro g
        funext a
        simp [NG.rt]
      map_mul' := fun x y => by
        apply LinearMap.ext
        intro g
        funext a
        simp [NG.rt, mul_assoc] }
  rw [iSup_subtype'] at hspan
  obtain ⟨t, ht⟩ := Submodule.mem_iSup_iff_exists_finset.1 hspan
  let T : t → σ'.IntertwiningMap ρ' := fun j =>
    LinearMap.intertwiningMap_of_isIntertwiningMap σ' ρ' j.1.1 fun g v => j.1.2.2 g.1 g.2 v
  have hf' : f ∈ ⨆ j, LinearMap.range (T j).toLinearMap := by
    rw [iSup_subtype'] at ht
    exact ht
  let K : Subgroup H := (GlobalTheory.SplitWeil.KOne (s.w.adicCompletion L) (Fin n)).comap φ
  have hfixK : ∀ k ∈ K, ρ' k f = f := fun k hk =>
    hfix k.1 k.2 (mem_KOne_of_map c hc _ hk)
  have hne := GlobalTheory.UnrLoc.fixed_ne_bot_of_mem_iSup_range hσ' T K hf' hf0 hfixK
  rw [Submodule.ne_bot_iff] at hne ⊢
  obtain ⟨y, hy, hy0⟩ := hne
  refine ⟨y, GlobalTheory.Parabolic.mem_fixed.2 fun h hh => ?_, hy0⟩
  obtain ⟨x, rfl⟩ := hφ h
  exact GlobalTheory.Parabolic.mem_fixed.1 hy x hh

end GlobalTheory.FixedAtSplit
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutPts

theorem l0 : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C) (Pl : PlSide D) (M : MtFam D) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec Pl M C big X T) (i : X.nd.Loc) (w : PlE D.host) (s : SplitPlace D.host.E), SplitOut X.nd i w → IsConjPl D.host w s.w → s.v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩) := GlobalTheory.T.splitPlace_outside_nonHyperspecial_of_localisation
theorem l1 : ∀ (D : D7) (μ : D.what₂.Tup) (j : ℕ) (Mr : MtReal D μ j) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))), NG.IsProdLevel Mr.J → NG.HypOutside Mr.J Mr.χ B → ∀ (S : Submodule ℂ (GAf D.host.E D.R.nV → Mr.wt.W)), NG.IsIrrRep Mr.wt.ρ S → ∀ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ), s.v ∉ B → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∃ c : ℂ, ∀ y ∈ (NG.isoTyp Mr.wt.ρ S).comap Mr.real, NG.tN Mr.J s ϖ k (Mr.real y) = c • Mr.real y := GlobalTheory.T.isotypic_heckeOperator_hyperspecial_acts_by_scalar
theorem l2a : ∀ (D : D7) (Pl : PlSide D) (M : MtFam D) (C : NChoice D) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec Pl M C big X T) (j : ℕ) (w : D.what₂.places.Pl) (i : X.nd.Loc) (h : i ∈ X.nd.locs j w) (x : X.nd.X i), X.nd.mult i x = Module.finrank (FractionRing (Sp.B.Oc j w)) ↥(⨅ (v : PlE D.host) (k : ℕ) (_ : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k), Module.End.eigenspace (Sp.B.hK j w v k) (algebraMap (Sp.B.Oc j w) (FractionRing (Sp.B.Oc j w)) (Sp.phO j w i h ((X.nd.hT i v k : X.nd.X i → X.nd.O i) x)))) := GlobalTheory.T.heckeMultiplicity_eq_finrank_jointEigenspace
theorem l2b : ∀ (D : D7) (M : MtFam D) (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) (μ : D.what₂.Tup) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), μ = D.what₂.muTw w → ∀ (φ : FractionRing (B.Oc j w) →+* ℂ), (∀ x, φ (B.ec j w x) = D.what₂.embLL x) → ∀ (κ : PlE D.host → ℕ → FractionRing (B.Oc j w)) (E : Submodule ℂ (D.what₂.Mt μ j)), (∀ v k, GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → (∀ v k (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ → ∀ (c : ℂ) (f f' : GAf D.host.E D.R.nV → (M μ j h1 h2).wt.W), NG.tN (M μ j h1 h2).J s ϖ k (c • f + f') = c • NG.tN (M μ j h1 h2).J s ϖ k f + NG.tN (M μ j h1 h2).J s ϖ k f') → (∀ y, y ∈ E ↔ ∀ v k (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ → NG.tN (M μ j h1 h2).J s ϖ k ((M μ j h1 h2).real y) = φ (κ v k) • (M μ j h1 h2).real y) → Module.finrank (FractionRing (B.Oc j w)) ↥(⨅ (v : PlE D.host) (k : ℕ) (_ : GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k), Module.End.eigenspace (B.hK j w v k) (κ v k)) = Module.finrank ℂ E := GlobalTheory.T.finrank_jointEigenspace_coefficientField_complex

theorem mt_tr {D : D7} (M : MtFam D) (Pr : ∀ (μ : D.what₂.Tup) (j : ℕ), MtReal D μ j → Prop) {μ μ' : D.what₂.Tup}
    {j j' : ℕ} (hμ : μ = μ') (hj : j = j') (a1 : 1 ≤ j) (a2 : j ≤ D.R.m) (b1 : 1 ≤ j') (b2 : j' ≤ D.R.m) :
    Pr μ j (M μ j a1 a2) → Pr μ' j' (M μ' j' b1 b2) := by
  subst hμ hj; exact id

theorem genAt_iff' {D : D7} {Pl : PlSide D} {M : MtFam D} {C : NChoice D} {big : D.what₂.places.Pl → Finset ℂ}
    {X : LocNd (lay0 D)} {T : LocTw X} (Sp : NdSpec Pl M C big X T) (i : X.nd.Loc) (v : PlE D.host) (k : ℕ) :
    GenAt D (D.what₂.places.resChar (X.nd.w i)) (Sp.B.Qc (X.nd.j i) (X.nd.w i)) v k ↔
      (SplitOut X.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV) := by
  have h : i ∈ X.nd.locs (X.nd.j i) (X.nd.w i) := (X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  have hl : X.nd.l i = D.what₂.places.resChar (X.nd.w i) := (X.nd.w_l i).symm
  have hS : v ∈ X.nd.S i ↔ v ∈ placesS D (D.what₂.places.resChar (X.nd.w i)) := by
    rw [X.nd.S_def, hl]; rfl
  unfold SplitOut GenAt
  rw [hS, Sp.Q_eq _ _ i h, hl]
  tauto

theorem mem_iSup_iff {V Wf : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup Wf] [Module ℂ Wf] {ι : Type}
    [Finite ι] (real : V →ₗ[ℂ] Wf) (hreal : Function.Injective real) (typ : ι → Submodule ℂ V)
    (hind : iSupIndep typ) (htop : ⨆ P, typ P = ⊤) {Par : Type} (Good : Par → Prop) (op : Par → Wf → Wf)
    (hlin : ∀ p, Good p → ∀ (c : ℂ) (f f' : Wf), op p (c • f + f') = c • op p f + op p f')
    (hsc : ∀ P p, Good p → ∃ c : ℂ, ∀ y ∈ typ P, op p (real y) = c • real y) (lam : Par → ℂ) (Q : ι → Prop)
    (hQ : ∀ P, Q P ↔ ∀ p, Good p → ∀ y ∈ typ P, op p (real y) = lam p • real y) (y : V) :
    y ∈ (⨆ P ∈ {P | Q P}, typ P) ↔ ∀ p, Good p → op p (real y) = lam p • real y := by
  classical
  have hop0 : ∀ p, Good p → op p 0 = 0 := fun p hp => by
    have h := hlin p hp 1 0 0
    rw [one_smul, add_zero, one_smul] at h
    exact (add_eq_left.1 h.symm)
  have hopadd : ∀ p, Good p → ∀ f f' : Wf, op p (f + f') = op p f + op p f' := fun p hp f f' => by
    simpa using hlin p hp 1 f f'
  have hopsmul : ∀ p, Good p → ∀ (c : ℂ) (f : Wf), op p (c • f) = c • op p f := fun p hp c f => by
    simpa [hop0 p hp] using hlin p hp c f 0
  let Es : Submodule ℂ V :=
    { carrier := {y | ∀ p, Good p → op p (real y) = lam p • real y}
      zero_mem' := fun p hp => by simp [hop0 p hp]
      add_mem' := fun {a b} ha hb p hp => by
        simp only [map_add (f := _), hopadd p hp, ha p hp, hb p hp, smul_add]
      smul_mem' := fun c a ha p hp => by
        simp only [map_smul, hopsmul p hp, ha p hp, smul_comm c (lam p)] }
  show y ∈ _ ↔ y ∈ Es
  constructor
  · intro hy
    refine (iSup₂_le fun P hP => ?_ : (⨆ P ∈ {P | Q P}, typ P) ≤ Es) hy
    intro z hz p hp
    exact (hQ P).1 hP p hp z hz
  · intro hy
    have hy' : y ∈ ⨆ P, typ P := by rw [htop]; trivial
    obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp typ y).1 hy'
    rw [← hsum]
    refine Submodule.finsuppSum_mem _ _ _ _ fun P hPs => ?_
    by_cases h0 : f P = 0
    · rw [h0]; exact Submodule.zero_mem _
    refine (le_iSup₂ (f := fun P (_ : P ∈ {P | Q P}) => typ P) P ?_) (hf P)
    show Q P
    refine (hQ P).2 fun p hp => ?_
    obtain ⟨c, hc⟩ := hsc P p hp
    choose cc hcc using fun P' => hsc P' p hp

    have hz : ∑ P' ∈ f.support, (cc P' - lam p) • f P' = 0 := by
      apply hreal

      rw [map_zero, map_sum]
      have e1 : ∀ P' ∈ f.support, real ((cc P' - lam p) • f P') = op p (real (f P')) - lam p • real (f P') := by
        intro P' _
        rw [map_smul, hcc P' _ (hf P'), sub_smul]
      rw [Finset.sum_congr rfl e1, Finset.sum_sub_distrib, ← Finset.smul_sum]
      have e2 : ∀ s : Finset ι, op p (real (∑ P' ∈ s, f P')) = ∑ P' ∈ s, op p (real (f P')) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp [hop0 p hp]
        | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, map_add (f := _), hopadd p hp, ih]
      have e3 : (∑ P' ∈ f.support, f P') = y := hsum
      have e4 : ∑ P' ∈ f.support, op p (real (f P')) = op p (real y) := by rw [← e2, e3]
      have e5 : ∑ P' ∈ f.support, real (f P') = real y := by rw [← e3, map_sum]
      rw [e4, e5, hy p hp, sub_self]
    have hz' := ((iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero typ).1 hind) f.support
      (fun P' => (cc P' - lam p) • f P') (fun P' _ => Submodule.smul_mem _ _ (hf P')) hz P
      (Finsupp.mem_support_iff.2 h0)
    have hcl : cc P = lam p := by
      rcases smul_eq_zero.1 hz' with h | h
      · exact sub_eq_zero.1 h
      · exact absurd h h0
    intro z hz
    rw [hcc P z hz, hcl]

end GlobalTheory.AutPts

namespace GlobalTheory.AutPts


end GlobalTheory.AutPts
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.VacReal

open GlobalTheory.ChainFr GlobalTheory.Size

theorem ptF_zero {D : D7} {V W : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : Fr V) (B : Fr W)
    (P : PolF D W.rank V.rank) : ptF ψ θ A B 0 P = 0 := by
  have hd : ∀ τ z, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z 0 = 0 := by
    intro τ z
    funext w
    simp [Formalism.IndefR.Datum.dRho, heisO]
  have : pureTensorO ψ θ V W A.cart B.cart A.onb B.onb 0 = 0 := by
    unfold pureTensorO pureTensorL
    refine (MvPolynomial.basisMonomials _ ℂ).ext fun k => ?_
    rw [Module.Basis.constr_basis]
    show opPow _ k 0 = 0
    unfold opPow
    induction Multiset.toList (Finsupp.toMultiset k) with
    | nil => rfl
    | cons a l ih => rw [List.foldr_cons, ih]; simp [aPlusAll, aPlus, crea, hd]
  unfold ptF
  rw [this]
  rfl

theorem exists_isVacF_ne_zero : ∀ (D : D7) (V W : HSp D) (A : GlobalTheory.ChainFr.Fr V) (B : GlobalTheory.ChainFr.Fr W) (θ : InfFam D)
    (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f, IsThetaFunO ψ V W f → f ≠ 0 →
      ∃ f₀, GlobalTheory.ChainFr.IsVacF ψ θ A B f₀ ∧ f₀ ≠ 0 := by
  intro D V W A B θ ψ hψ hθ f hf hf0
  by_contra hno
  push_neg at hno
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  have i6 : BorelSpace (WO V W) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO V W) (ratL W V) K hK hKc).1
  obtain ⟨U, -, -, hd⟩ := GlobalTheory.T.fockVectors_overVacua_dense_thetaFunctions D V W A B θ ψ hψ hθ μ 𝓕 ⟨hμ, h𝓕, h1⟩ f hf
  have hspan : fockSpan ψ θ A B U = ⊥ := by
    unfold fockSpan
    rw [Submodule.span_eq_bot]
    rintro g ⟨f₀, P, hv, -, rfl⟩
    rw [hno f₀ hv]
    exact ptF_zero ψ θ A B P
  have hl : l2O μ 𝓕 f = 0 := by
    by_contra hne
    obtain ⟨g, hg, -, hlt⟩ := hd 0 (l2O μ 𝓕 f) (pos_iff_ne_zero.2 hne)
    rw [hspan, Submodule.mem_bot] at hg
    rw [hg, sub_zero] at hlt
    have e : sobO ψ θ μ 𝓕 0 f = l2O μ 𝓕 f := wordSum_zero _ _ _
    rw [e] at hlt
    exact lt_irrefl _ hlt
  have h0 : ∀ᵐ x ∂μ.restrict 𝓕, f x = 0 :=
    (eLpNorm_eq_zero_iff two_ne_zero).1 hl
  exact hf0 (GlobalTheory.WeilVacMove.eq_zero_of_ae_fundamentalDomain (ratL W V) μ 𝓕 h𝓕 f hf.cont
    (GlobalTheory.WeilVacMove.norm_periodic hψ hf) h0)

end GlobalTheory.Mem.VacReal

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.split_place_hecke_operator_eigenvalue_conj_spherical : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)), IsUnif L s.v ϖ → ∀ J : Subgroup (GAf L n),
    (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) →
    ∀ (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L))) (α : Fin n → ℂˣ),
    GlobalTheory.SmGL.HasSatake σ.ρ α →
    ∀ (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* (GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L), Continuous i →
    (∀ x : L, i ((GlobalTheory.HeckeFrob.conjSplit s).i x) = algebraMap L ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L) x) →
    ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (T : σ.V →ₗ[ℂ] (GAf L n → W)),
    GlobalTheory.HeckeFrob.IsLocMap (GlobalTheory.HeckeFrob.conjSplit s) σ i T →
    ∀ e ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SplitWeil.KO ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L) (Fin n)),
    ∀ k, 1 ≤ k → k ≤ n →
      ((normV (GlobalTheory.HeckeFrob.conjSplit s).w : ℕ) : ℂ) ^ (k * (k - 1) / 2) • NG.tN J s ϖ k (T e) =
        (GlobalTheory.HeckeFrob.twEig (GlobalTheory.HeckeFrob.conjSplit s).w α).esymm k • T e := by
  first | exact @GlobalTheory.HeckeEigConj.tN_eig | exact GlobalTheory.HeckeEigConj.tN_eig | (intros; apply GlobalTheory.HeckeEigConj.tN_eig <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.definiteUnitary_realPoints_act_fock_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (θ : InfFam D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (f : WO V W → ℂ), IsWeilDatumO ψ V W χS χT ω → IsInfFam θ → V.SigOK → W.SigOK → AllPlus M → AllPlus M' → IsThetaFunO ψ V W f → (∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) f) → ∀ τ, (∀ g : Matrix.unitaryGroup (Fin V.rank) ℂ, ∃ c : ℂ, c ≠ 0 ∧ ∀ P, ω (atTau θ V τ (unfr M τ g), 1) (ptOf ψ θ M M' f P) = c • ptOf ψ θ M M' f (colSub W.rank τ g P)) ∧ ∀ u : Matrix.unitaryGroup (Fin W.rank) ℂ, ∃ c : ℂ, c ≠ 0 ∧ ∀ P, ω (1, atTau θ W τ (unfr M' τ u)) (ptOf ψ θ M M' f P) = c • ptOf ψ θ M M' f (rowSub V.rank τ u P) := by
  first | exact @GlobalTheory.DefLift.FockAct.fock_act | exact GlobalTheory.DefLift.FockAct.fock_act | (intros; apply GlobalTheory.DefLift.FockAct.fock_act <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.exists_localComponent_conj_splitPlace : ∀ (D : D7) (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E) (w : PlE D.host),
    IsConjPl D.host w s.w → ∃ x, GlobalTheory.AutQuot.LocAt π w x := by
  first | exact @GlobalTheory.AutQuot.conjLoc | exact GlobalTheory.AutQuot.conjLoc | (intros; apply GlobalTheory.AutQuot.conjLoc <;> assumption)
end
