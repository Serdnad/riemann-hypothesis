module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle011
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle232
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle144
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle115
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle164
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle322
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle137
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle351
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle302
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatePlaceBoundedMatrixFromConjugateHalfHomL
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle178
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle309
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.ParameterTransferTypes GlobalTheory.Hk3 GlobalTheory.SplitHeckeAdj

namespace GlobalTheory.LiftOntoCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Abstract

variable {H Γ W : Type} [Group H] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ι : Γ →* H}
  {ρ : Γ →* Module.End ℂ W} {J : Subgroup H} {χ : J →* ℂˣ} {Φ : H → W}

theorem mem_adForms_iff : Φ ∈ Bridge.AdForms ι ρ J χ ↔
    (∀ γ u, Φ (ι γ * u) = ρ γ (Φ u)) ∧ ∀ u k (hk : k ∈ J), Φ (u * k) = (χ ⟨k, hk⟩ : ℂ) • Φ u :=
  ⟨fun h => ⟨fun γ u => by simpa using h γ u 1, fun u k hk => by simpa using h 1 u ⟨k, hk⟩⟩,
    fun h γ u k => by rw [h.2 _ _ k.2, h.1]⟩

theorem eq_of_dual {x y : W} (h : ∀ ℓ : W →ₗ[ℂ] ℂ, ℓ x = ℓ y) : x = y :=
  sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => by rw [map_sub, h ℓ, sub_self])

end Abstract

section General

variable {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} (c : CoefA V)

variable {c}

theorem hasType_form {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ρ : GQ V →* Module.End ℂ W} {Φ : Bridge.Gf V → W}
    (hΦ : Φ ∈ Bridge.AdForms (Bridge.ratF V) ρ (levEnv V β L).J (levEnv V β L).χ)
    (ℓ : W →ₗ[ℂ] ℂ) : HasType V β (flag1L L) fun g => ℓ (Φ (fin V g)) := fun κ hκ g =>
  (congrArg (fun u => ℓ (Φ u)) ((fin V).map_mul g κ)).trans
    ((congrArg ℓ ((mem_adForms_iff.1 hΦ).2 (fin V g) _ ((mem_J V β L hκ.1).2 hκ))).trans (ℓ.map_smul _ _))

theorem forall_fin {p : Bridge.Gf V → Prop} (h : ∀ g ∈ GfC V, p (fin V g)) (u : Bridge.Gf V) : p u :=
  (fin_lift V u).elim fun g hg => hg.2 ▸ h g hg.1

theorem hkF_mem {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ρ : GQ V →* Module.End ℂ W} {w : Pl D.host.E}
    (a : List ℤ →₀ ℂ) (h3 : ∀ Φ, HasType V β (flag1L L) Φ → HasType V β (flag1L L) (hk V w a Φ))
    {Φ : Bridge.Gf V → W} (hΦ : Φ ∈ Bridge.AdForms (Bridge.ratF V) ρ (levEnv V β L).J (levEnv V β L).χ) :
    hkF V w a Φ ∈ Bridge.AdForms (Bridge.ratF V) ρ (levEnv V β L).J (levEnv V β L).χ := by
  have hc : ∀ (ℓ : W →ₗ[ℂ] ℂ) g, hk V w a (fun g => ℓ (Φ (fin V g))) g = ℓ (hkF V w a Φ (fin V g)) := fun ℓ g => by
    rw [GlobalTheory.LevOp.hk_apply]

    simp only [hkF, Finsupp.sum, map_sum, LinearMap.map_smul, smul_eq_mul, heckeLin_apply, MonoidHom.map_mul]
  refine mem_adForms_iff.2 ⟨fun γ u => ?_, fun u k => ?_⟩

  · simp only [hkF, Finsupp.sum, mul_assoc, (mem_adForms_iff.1 hΦ).1, map_sum, LinearMap.map_smul]
  · refine forall_fin (p := fun k => ∀ hk : k ∈ (levEnv V β L).J,
      hkF V w a Φ (u * k) = ((levEnv V β L).χ ⟨k, hk⟩ : ℂ) • hkF V w a Φ u) (fun κ hκ hk => ?_) k
    refine forall_fin (p := fun u => hkF V w a Φ (u * fin V κ) = ((levEnv V β L).χ ⟨fin V κ, hk⟩ : ℂ) • hkF V w a Φ u)
      (fun g _ => eq_of_dual fun ℓ => ?_) u
    have := h3 _ (hasType_form hΦ ℓ) κ ((mem_J V β L hκ).1 hk) g
    rw [hc, hc, MonoidHom.map_mul] at this
    exact this.trans (ℓ.map_smul _ _).symm

theorem one_notMem (w : Pl D.host.E) (n : ℕ) : ((1 ^ n : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  rw [one_pow, Nat.cast_one]
  exact (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top

end General

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem offS_iff_good (t : T) (w : Pl D.host.E) : OffS D (badS R t) w ↔ Good R t w := by
  classical
  rw [GlobalTheory.GoodPrimes.offS_iff]
  unfold badS
  simp only [Finset.mem_image, Finset.mem_union, not_exists, not_and]
  refine forall₂_congr fun PP _ => ⟨fun h => ⟨fun e => h (by rw [e]), fun e => h (GlobalTheory.LevelPlaces.under_eq_of_isConjPl e)⟩, fun h e => ?_⟩
  rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with h1 | h1
  · exact h.1 h1.symm
  · exact h.2 (GlobalTheory.GoodPrimes.isConjPl_iff.2 h1)

theorem exists_opsV (hL : R.toLevCh.Is A.μ0) (hM : R.IsModels) (i : Fin D.R.m) (t : T) : ∃ h, IsOpsV R i t h := by
  have key : ∀ w a, ∃ s : Module.End ℂ (R.HV i t).H, Good R t w → ∀ x, (R.HV i t).e (s x) = hkF (Vc D i) w a ((R.HV i t).e x) := by
    intro w a
    by_cases hw : Good R t w
    swap
    · exact ⟨0, fun h => absurd h hw⟩
    refine (hL.βV i).elim fun n hn => ?_
    have h3 := (GlobalTheory.LevOp.level_operators (Vc D i) (R.βV i) (R.ΛV i) _ (flag1L (R.datVt i t)) hn w (one_notMem w n) hw).2.2.1 a
    exact (GlobalTheory.DefiniteOps.exists_lift (R.HV i t) _ _ (hM.HV i t)
      (opOf (GlobalTheory.DefiniteOps.rtr (fin (Vc D i)) (R.cV i).W) w a)
      fun Φ hΦ => GlobalTheory.DefiniteOps.hkF_eq (Vc D i) w a Φ ▸ hkF_mem a h3 hΦ).imp
      fun s hs _ x => (hs x).trans (GlobalTheory.DefiniteOps.hkF_eq _ _ _ _).symm
  choose h hh using key
  exact ⟨h, fun w hw c x => hh w c hw x⟩

section Levels

variable (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ)

end Levels

section Compare

variable (R) (F : Face D A)

variable {R}

variable (R)

end Compare

end GlobalTheory.LiftOntoCompare

end
end

section

noncomputable section

namespace GlobalTheory.SatBoundInert

open Formalism.UG GlobalTheory.PRep GlobalTheory.LGrp GlobalTheory.LFun

theorem norm_form_le {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ)
    (hsym : ∀ v w, B w v = starRingEnd ℂ (B v w)) (hpos : ∀ v, v ≠ 0 → 0 < (B v v).re) (u v : V)
    (h : B u u = B v v) : ‖B u v‖ ≤ (B v v).re := by
  have hnn : ∀ z, 0 ≤ (B z z).re := fun z => by
    by_cases hz : z = 0
    · simp [hz]
    · exact (hpos z hz).le
  by_cases h0 : B u v = 0
  · rw [h0, norm_zero]; exact hnn v
  have hn : (‖B u v‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 h0)
  have hz := hnn (u - (B u v / (‖B u v‖ : ℂ)) • v)
  have e : B (u - (B u v / (‖B u v‖ : ℂ)) • v) (u - (B u v / (‖B u v‖ : ℂ)) • v) =
      B u u - starRingEnd ℂ (B u v / (‖B u v‖ : ℂ)) * B u v - (B u v / (‖B u v‖ : ℂ)) * starRingEnd ℂ (B u v) +
        (B u v / (‖B u v‖ : ℂ)) * starRingEnd ℂ (B u v / (‖B u v‖ : ℂ)) * B v v := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, map_smulₛₗ, smul_eq_mul]
    rw [hsym u v]
    ring
  have h1 : starRingEnd ℂ (B u v / (‖B u v‖ : ℂ)) * B u v = ‖B u v‖ := by
    rw [map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, Complex.conj_mul', sq]
    field_simp
  have h2 : (B u v / (‖B u v‖ : ℂ)) * starRingEnd ℂ (B u v) = ‖B u v‖ := by
    rw [div_mul_eq_mul_div, Complex.mul_conj', sq]
    field_simp
  have h3 : (B u v / (‖B u v‖ : ℂ)) * starRingEnd ℂ (B u v / (‖B u v‖ : ℂ)) = 1 := by
    rw [map_div₀, Complex.conj_ofReal, div_mul_div_comm, Complex.mul_conj', sq]
    field_simp
  rw [e, h1, h2, h3, h] at hz
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, one_mul] at hz
  linarith

theorem satakeBoundInert : GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.SatakeBoundInert := by
  intro L _ _ _ ϖ σ q n hU V _ _ π α _ hun hsat
  obtain ⟨B, hsym, hpos, hinv⟩ := hun
  obtain ⟨x, hx⟩ := hsat.exists_vec
  have hxx : B x x ≠ 0 := fun h => by
    have := hpos x hx.1
    rw [h] at this
    simp at this
  let c : ℂ := (B x x)⁻¹
  let l : V →ₗ[ℂ] ℂ :=
    { toFun := fun y => B y x * c
      map_add' := fun a b => by simp [add_mul]
      map_smul' := fun a y => by simp [mul_assoc] }
  have hl : ∀ k ∈ KU σ n, ∀ y, l (π k y) = l y := fun k hk y => by
    show B (π k y) x * c = B y x * c
    conv_lhs => rw [← GlobalTheory.LGrp.mem_fixed.1 hx.2.1 k hk]
    rw [hinv]
  have h1 : l x = 1 := mul_inv_cancel₀ hxx
  have hz := GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.isZonal_of_isSatVecU hU hx l hl h1
  have hϖ : ϖ ≠ 0 := by
    intro h
    have := hU.2.2.2.1
    rw [h, map_zero] at this
    exact WithZero.zero_ne_coe this
  refine GlobalTheory.T.satakeTrivialBound_of_bounded_zonal_spherical_unitary GlobalTheory.InertZeta.unramDoublingInert L (Units.mk0 ϖ hϖ) σ q n hU α _ hz ⟨(B x x).re * ‖c‖, fun g => ?_⟩
  show ‖B (π g x) x * c‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_form_le B hsym hpos _ _ (hinv g x x)) (norm_nonneg _)

end GlobalTheory.SatBoundInert

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift.AvgLift

private theorem isFundamentalDomain_preimage_mul_right' {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (Γ : Subgroup G) (μ : Measure G) [μ.IsMulRightInvariant] {𝓕 : Set G}
    (h : IsFundamentalDomain Γ 𝓕 μ) (a : G) : IsFundamentalDomain Γ ((fun g => g * a) ⁻¹' 𝓕) μ :=
  h.preimage_of_equiv (measurePreserving_mul_right μ a).quasiMeasurePreserving Function.bijective_id
    (fun γ x => mul_assoc (γ : G) x a)

theorem integrableOn_mul_right {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G)
    [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {𝓕 : Set G}
    (h : IsFundamentalDomain Γ 𝓕 μ) {Φ : G → ℂ} (hΦ : ∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) (hi : IntegrableOn Φ 𝓕 μ)
    (a : G) : IntegrableOn (fun g => Φ (g * a)) 𝓕 μ := by
  have hinv : ∀ (γ : Γ) (x : G), (fun g => Φ (g * a)) (γ • x) = (fun g => Φ (g * a)) x := by
    intro γ x
    show Φ ((γ : G) * x * a) = Φ (x * a)
    rw [mul_assoc]
    exact hΦ γ γ.2 (x * a)
  rw [h.integrableOn_iff (isFundamentalDomain_preimage_mul_right' Γ μ h a) hinv]
  exact ((measurePreserving_mul_right μ a).integrableOn_comp_preimage
    (MeasurableEquiv.mulRight a).measurableEmbedding).mpr hi

private theorem setIntegral_fd_comp_mul_right_of_invariant {G E : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Γ : Subgroup G) [Countable Γ] (μ : Measure G)
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {𝓕 : Set G} (h : IsFundamentalDomain Γ 𝓕 μ)
    {Φ : G → E} (hΦ : ∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) (a : G) :
    ∫ g in 𝓕, Φ (g * a) ∂μ = ∫ g in 𝓕, Φ g ∂μ := by
  have hinv : ∀ (γ : Γ) (x : G), (fun g => Φ (g * a)) (γ • x) = (fun g => Φ (g * a)) x := by
    intro γ x
    show Φ ((γ : G) * x * a) = Φ (x * a)
    rw [mul_assoc]
    exact hΦ γ γ.2 (x * a)
  rw [h.setIntegral_eq (isFundamentalDomain_preimage_mul_right' Γ μ h a) hinv]
  exact (measurePreserving_mul_right μ a).setIntegral_preimage_emb
    (MeasurableEquiv.mulRight a).measurableEmbedding Φ 𝓕

theorem setIntegral_average {G K : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [SecondCountableTopology G] (Γ : Subgroup G) [Countable Γ]
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {𝓕 : Set G}
    (h : IsFundamentalDomain Γ 𝓕 μ) [TopologicalSpace K] [MeasurableSpace K] [OpensMeasurableSpace K]
    (m : Measure K) [IsProbabilityMeasure m] {κ : K → G} (hκ : Continuous κ)
    {Φ : G → ℂ} (hΦ : ∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) (hc : Continuous Φ) (hi : IntegrableOn Φ 𝓕 μ) :
    ∫ g in 𝓕, ∫ k, Φ (g * κ k) ∂m ∂μ = ∫ g in 𝓕, Φ g ∂μ := by
  have hjoint : Continuous fun p : G × K => Φ (p.1 * κ p.2) :=
    hc.comp (continuous_fst.mul (hκ.comp continuous_snd))
  have hint : Integrable (Function.uncurry fun g k => Φ (g * κ k)) ((μ.restrict 𝓕).prod m) := by
    refine (integrable_prod_iff' hjoint.aestronglyMeasurable).mpr ⟨?_, ?_⟩
    · exact Filter.Eventually.of_forall fun k => integrableOn_mul_right Γ μ h hΦ hi (κ k)
    · have hn : ∀ k, ∫ g in 𝓕, ‖Φ (g * κ k)‖ ∂μ = ∫ g in 𝓕, ‖Φ g‖ ∂μ := fun k =>
        setIntegral_fd_comp_mul_right_of_invariant Γ μ h (Φ := fun g => ‖Φ g‖)
          (fun γ hγ g => by simp only [hΦ γ hγ g]) (κ k)
      show Integrable (fun k => ∫ g in 𝓕, ‖Φ (g * κ k)‖ ∂μ) m
      simp only [hn]
      exact integrable_const _
  rw [integral_integral_swap hint]
  have hs : ∀ k, ∫ g in 𝓕, Φ (g * κ k) ∂μ = ∫ g in 𝓕, Φ g ∂μ := fun k =>
    setIntegral_fd_comp_mul_right_of_invariant Γ μ h hΦ (κ k)
  simp only [hs, integral_const, probReal_univ, one_smul]

variable {D : D7} {T : HSp D} {Sp : D.what₂.Tau → SPar}

theorem frame_mem (M : DSModel T Sp) (τ : D.what₂.Tau) {κ : Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hκ : κ ∈ Formalism.REAL.Kset (M.ε τ)) : (M.fr τ)⁻¹ * κ * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D T τ) := by
  obtain ⟨hu, hcomm⟩ := hκ
  have hdet : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have h2 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have hκu : κᴴ * κ = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hu
    rwa [Matrix.star_eq_conjTranspose] at this
  show ((M.fr τ)⁻¹ * κ * M.fr τ)ᴴ * gramAt D T τ * ((M.fr τ)⁻¹ * κ * M.fr τ) = gramAt D T τ
  rw [← M.fr_gram τ]
  simp only [Matrix.conjTranspose_mul, mul_assoc]
  rw [← mul_assoc ((M.fr τ)⁻¹)ᴴ, h2, one_mul, ← mul_assoc (M.fr τ) (M.fr τ)⁻¹, h1, one_mul,
    ← mul_assoc (Formalism.REAL.Jm (M.ε τ)) κ, ← hcomm, mul_assoc κ, ← mul_assoc κᴴ κ, hκu, one_mul]

theorem continuous_elt {θ : InfFam D} (hθ : IsInfFam θ) (M : DSModel T Sp) (τ : D.what₂.Tau) :
    Continuous fun k : Formalism.REAL.KG (M.ε τ) => GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M τ (Formalism.REAL.toMK k) := by
  have hK : ∀ k : Formalism.REAL.KG (M.ε τ), Formalism.REAL.toMK k ∈ Formalism.REAL.Kset (M.ε τ) := fun k =>
    (Formalism.REAL.mem_KG (M.ε τ) k).mp k.2
  have hc : Continuous fun k : Formalism.REAL.KG (M.ε τ) => Formalism.REAL.toMK k :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  show Continuous fun k : Formalism.REAL.KG (M.ε τ) => atTau θ T τ ((M.fr τ)⁻¹ * Formalism.REAL.toMK k * M.fr τ)
  exact (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ T τ).comp_continuous
    ((continuous_const.matrix_mul hc).matrix_mul continuous_const)
    (fun k => frame_mem M τ (hK k))

theorem liftInt_eq_sum_average : ∀ (D : D7) (V W : HSp D) (S' : D.what₂.Tau → SPar) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν → ∀ (τ : D.what₂.Tau) (n : ℕ) (c : Fin n → Formalism.REAL.KG (M'.ε τ) → ℂ) (f : WO V W → ℂ) (fs : Fin n → WO V W → ℂ) (F : GA D W → ℂ) (Fs : Fin n → GA D W → ℂ), (∀ i, Continuous (c i)) → IsThetaFunO ψ V W f → (∀ k, ω (1, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) f = ∑ i, c i k • fs i) → IsAutFun W F → (∀ i h, Fs i h = ∫ k, c i k * F (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) ∂(Formalism.REAL.muK (M'.ε τ))) → ∀ g, IntegrableOn (fun h => thetaKO ω g h f * F h) 𝓕 ν → (∀ i, IntegrableOn (fun h => thetaKO ω g h (fs i) * Fs i h) 𝓕 ν) → Lift.liftInt ν 𝓕 (thetaKO ω) f F g = ∑ i, Lift.liftInt ν 𝓕 (thetaKO ω) (fs i) (Fs i) g := by
  intro D V W S' M' θ ψ χS χT ω ν 𝓕 hθ hW hν h𝓕 τ n c f fs F Fs hc hf hω hF hFs g hi hii
  obtain ⟨hlc, hsc, ht2, hbor, htg, -, hcount⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨hright, -⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D W ν hν
  have hker := GlobalTheory.thetaKO_continuous_and_rat_invariant ψ V W χS χT ω hW f hf
  have hec : Continuous fun k : Formalism.REAL.KG (M'.ε τ) => GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k) :=
    continuous_elt hθ M' τ
  have hΦinv : ∀ γ ∈ GQ W, ∀ h, thetaKO ω g (γ * h) f * F (γ * h) = thetaKO ω g h f * F h := by
    intro γ hγ h
    have h1 := hker.2 1 (GQ V).one_mem γ hγ g h
    rw [one_mul] at h1
    rw [h1, hF.left γ hγ h]
  have hΦc : Continuous fun h => thetaKO ω g h f * F h :=
    (hker.1.comp (continuous_const.prodMk continuous_id)).mul hF.cont
  have hlin : ∀ (h k : GA D W) (u : WO V W → ℂ), thetaKO ω g (h * k) u = thetaKO ω g h (ω (1, k) u) := by
    intro h k u
    show ω (g, h * k) u 0 = ω (g, h) (ω (1, k) u) 0
    have hp : ((g, h * k) : GA D V × GA D W) = (g, h) * (1, k) := by simp
    rw [hp, map_mul]
    rfl
  have hsum : ∀ (h : GA D W) (k : Formalism.REAL.KG (M'.ε τ)),
      thetaKO ω g h (∑ i, c i k • fs i) = ∑ i, c i k * thetaKO ω g h (fs i) := by
    intro h k
    show ω (g, h) (∑ i, c i k • fs i) 0 = ∑ i, c i k * ω (g, h) (fs i) 0

    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hpt : ∀ h, ∫ k, thetaKO ω g (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) f *
      F (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) ∂(Formalism.REAL.muK (M'.ε τ)) =
      ∑ i, thetaKO ω g h (fs i) * Fs i h := by
    intro h
    have hexp : ∀ k, thetaKO ω g (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) f *
        F (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) =
        ∑ i, thetaKO ω g h (fs i) * (c i k * F (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k))) := by
      intro k
      rw [hlin, hω k, hsum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hFk : Continuous fun k : Formalism.REAL.KG (M'.ε τ) =>
        F (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) :=
      hF.cont.comp (continuous_const.mul hec)
    have hint : ∀ i, Integrable (fun k => thetaKO ω g h (fs i) *
        (c i k * F (h * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)))) (Formalism.REAL.muK (M'.ε τ)) := fun i =>
      integrableOn_univ.mp
        ((continuous_const.mul ((hc i).mul hFk)).continuousOn.integrableOn_compact isCompact_univ)
    simp_rw [hexp]
    rw [integral_finsetSum _ fun i _ => hint i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, hFs i h]
  show ∫ h in 𝓕, thetaKO ω g h f * F h ∂ν = ∑ i, ∫ h in 𝓕, thetaKO ω g h (fs i) * Fs i h ∂ν
  refine (setIntegral_average (GQ W) ν h𝓕 (m := Formalism.REAL.muK (M'.ε τ))
    (Φ := fun h => thetaKO ω g h f * F h) hec hΦinv hΦc hi).symm.trans ?_
  rw [← integral_finsetSum _ fun i _ => hii i]
  exact integral_congr_ae (Filter.Eventually.of_forall hpt)

end GlobalTheory.Chain.IoLift.AvgLift

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilNormCont

theorem continuous_meanSquareNorm_weilRep_sub : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsCovolOne (ratL T S) μ 𝓕 → ∀ f₁ f₂ : WO S T → ℂ, IsThetaFunO ψ S T f₁ → IsThetaFunO ψ S T f₂ → Continuous fun p : GA D S × GA D T => nrm2 μ 𝓕 (om p f₁ - f₂) := by
  intro D ψ S T χS χT om μ 𝓕 hom hμ f₁ f₂ h₁ h₂
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  obtain ⟨b, hb⟩ := GlobalTheory.WeilSupBound.exists_sup_bound D ψ S T χS χT om hom f₂ h₂ {1} isCompact_singleton
  have hb' : ∀ w, ‖f₂ w‖ ≤ b := fun w => by simpa using hb 1 rfl w
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds p₀
  obtain ⟨c, hc⟩ := GlobalTheory.WeilSupBound.exists_sup_bound D ψ S T χS χT om hom f₁ h₁ K hK
  unfold nrm2
  refine continuousAt_of_dominated (bound := fun _ => (c + b) ^ 2) ?_ ?_ (integrable_const _) ?_
  · refine Filter.Eventually.of_forall fun p => ?_
    exact ((((hom.om_pres p f₁ h₁).cont.sub h₂.cont).norm.pow 2).measurable).aestronglyMeasurable
  · filter_upwards [hK0] with p hp
    refine Filter.Eventually.of_forall fun w => ?_
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (add_le_add (hc p hp w) (hb' w))) 2
  · refine Filter.Eventually.of_forall fun w => ?_
    exact (((hom.om_cont f₁ h₁ w).sub continuous_const).norm.pow 2).continuousAt

end GlobalTheory.WeilNormCont
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.splitPlaceAdjointMatrix_homLattice_bounded_conjugateIdeal : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ a : D.host.E, (∀ a' : D.host.E, a' ∈ D.host.AA → Valued.v (rdQ φ (star a')) ≤ Valued.v (rdQ φ (star a))) → ∀ u ∈ latO S T ΛS ΛT (fun _ => True), ∀ i j, Valued.v (adjCo φ S T (frCo φ βS) (frCo φ βT) u i j) ≤ Valued.v (rdQ φ (star a)) := by
  first | exact @GlobalTheory.SplitAdjBound.adjCo_bound | exact GlobalTheory.SplitAdjBound.adjCo_bound | (intros; apply GlobalTheory.SplitAdjBound.adjCo_bound <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.splitPlaceHomLattice_entries_bounded_by_idealValuation : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ a : D.host.E, (∀ a' : D.host.E, a' ∈ D.host.AA → Valued.v (rdQ φ a') ≤ Valued.v (rdQ φ a)) → ∀ u ∈ latO S T ΛS ΛT (fun _ => True), ∀ i j, Valued.v (mapCo φ S T (frCo φ βS) (frCo φ βT) u i j) ≤ Valued.v (rdQ φ a) := by
  first | exact @GlobalTheory.SplitHomBound.hbound | exact GlobalTheory.SplitHomBound.hbound | (intros; apply GlobalTheory.SplitHomBound.hbound <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.cmAdeleIdempotentOfPlace_properties : ∀ D : D7, (∀ p, idem D p * idem D p = idem D p) ∧ (∀ p q, p ≠ q → idem D p * idem D q = 0) ∧ (∀ p, cA D (idem D p) = idem D p) ∧ (∀ v : FinPl D, infPart D (idem D (.inl v)) = 0 ∧ finPart D (idem D (.inl v)) ∈ intAE D ∧ IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1))) ∧ (∀ τ : D.what₂.Tau, finPart D (idem D (.inr τ)) = 0) ∧ infPart D (∑ τ : D.what₂.Tau, idem D (.inr τ)) = 1 ∧ ∀ θ : InfFam D, IsInfFam θ → ∀ τ : D.what₂.Tau, θ τ (infPart D (idem D (.inr τ))) = 1 ∧ ∀ τ' : D.what₂.Tau, τ' ≠ τ → θ τ (infPart D (idem D (.inr τ'))) = 0 := by
  first | exact @GlobalTheory.PlaceTensor.idem_spec | exact GlobalTheory.PlaceTensor.idem_spec | (intros; apply GlobalTheory.PlaceTensor.idem_spec <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.conjugatePlaceBoundedMatrix_from_conjugateHalfHomLattice : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ a : D.host.E, a ∈ D.host.AA → a ≠ 0 → ∀ y : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v), (∀ i j, Valued.v (y i j) ≤ Valued.v (rdQ φ (star a))) → ∃ u, u ∈ latO S T ΛS ΛT (fun _ => True) ∧ IsHalf (cA D e) u ∧ adjCo φ S T (frCo φ βS) (frCo φ βT) u = y := by
  first | exact @GlobalTheory.ConjHalfOnto.conj_half_onto | exact GlobalTheory.ConjHalfOnto.conj_half_onto | (intros; apply GlobalTheory.ConjHalfOnto.conj_half_onto <;> assumption)
end
