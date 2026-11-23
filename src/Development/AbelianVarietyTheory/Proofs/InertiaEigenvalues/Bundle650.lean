module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle456
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle620
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle280
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle285
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle618
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle471
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle477
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle328
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle475
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle538
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle489
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle639
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle619
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle273
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle065
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1648
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeIndexSplitPlaceEqProductLocal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011

@[expose] public section

section

noncomputable section

open NumberField ReciprocityTheory.Gal Formalism.ConjugateSelfDual IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
  GlobalTheory.CuspRep GlobalTheory.DefiniteBC

namespace GlobalTheory.LFun.SatBridge

theorem hasSatGL_of_hasSatake : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V)
    (α : Fin n → ℂˣ),
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    HasSatake π α → GlobalTheory.LFun.HasSatGL w π (Finset.univ.val.map α) := by
  intro E _ _ w n V _ _ π α
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  intro h
  exact GlobalTheory.LFun.SatCompare.hasSatGL_of_hasSatakeGL
    ((GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ π _).2 ⟨α, rfl, h⟩)

end GlobalTheory.LFun.SatBridge
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.FlatConj

theorem xiR_val {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    (t : T0) (PP : Pl D.host.E) (hP : PP ∈ R.Q t) (u : (kP PP)ˣ) :
    ∃ s : (AE D)ˣ, ((R.xiR t PP u : ℂˣ) : ℂ) = ((R.xi t s : Circle) : ℂ) := by
  obtain ⟨a, k, hk, hx⟩ := GlobalTheory.ConjRes.exists_lift PP u
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 PP
  refine ⟨Formalism.L2.JoinChr.locU he.1 k, ?_⟩
  rw [hC.lev.xiR t PP hP a k u hk hx, (hC.lev.xi t).2 PP e he k _ (Formalism.L2.JoinChr.locU_val he.1 k)]

theorem prod_val {D : D7} (ξ : (AE D)ˣ →* Circle) (S : Finset (Pl D.host.E)) (v : Pl D.host.E → ℂ)
    (hv : ∀ PP ∈ S, ∃ s : (AE D)ˣ, v PP = ((ξ s : Circle) : ℂ)) :
    ∃ s : (AE D)ˣ, ∏ PP ∈ S, v PP = ((ξ s : Circle) : ℂ) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert a S ha ih =>
    obtain ⟨s0, h0⟩ := hv a (Finset.mem_insert_self a S)
    obtain ⟨s1, h1⟩ := ih fun PP hP => hv PP (Finset.mem_insert_of_mem hP)
    refine ⟨s0 * s1, ?_⟩
    rw [Finset.prod_insert ha, h0, h1, map_mul, Circle.coe_mul]

end GlobalTheory.FlatConj
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.KerSat



theorem mem_N_of_map_mem : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → ∀ x : W.DD T₀, W.map ι x ∈ W.N T₁ → x ∈ W.N T₀ := by
  intro D HW F l _ K s LL h W E T₀ T₁ T₂ ι π h0 h1 h2 hses x hx
  have hex : Function.Injective (W.map ι) ∧ Function.Exact (W.map ι) (W.map π) ∧
      Function.Surjective (W.map π) := by
    haveI := GlobalTheory.EtaleExact.finite_OL LL
    haveI : IsNoetherianRing ↥(OL LL) := IsNoetherianRing.of_finite ℤ_[l] ↥(OL LL)
    refine GlobalTheory.EtaleExact.exact_of_tie E (GlobalTheory.EtaleExact.map_ne_top_of_tie E ?_ ?_) T₀ T₁ T₂ ι π hses
    · rw [(D.loc l).PD_p K]
      exact GlobalTheory.EtaleExact.isUnit_or_dvd_pow (D.loc l) LL
    · rw [(D.loc l).PD_p K]
      exact GlobalTheory.EtaleExact.sep_RW LL
  have key := GlobalTheory.T.wachModule_uniqueness_characterisation D HW F l K s LL h T₀ h0
  obtain ⟨hinj, hexact, hsurj⟩ : Function.Injective (W.map ι) ∧ Function.Exact (W.map ι) (W.map π) ∧
      Function.Surjective (W.map π) := hex
  haveI := GlobalTheory.EtaleExact.finite_OL LL
  haveI : IsNoetherianRing ↥(OL LL) := IsNoetherianRing.of_finite ℤ_[l] ↥(OL LL)
  haveI := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  haveI : Module.Flat (AA K LL) W.EE :=
    GlobalTheory.T.flat_over_product_power_series_ring _ _ W.EE ((D.loc l).PD K).p W.EE_π W.EE_complete W.EE_dense W.EE_sat
  have hbc : IsBaseChange W.EE ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))).subtype :=
    GlobalTheory.T.isBaseChange_comap_of_exact_flat (AA K LL) W.EE _ _ _ (W.map ι) (W.map π) (W.N T₁) (W.N T₂) hinj hexact hsurj
      (W.N_base T₁ h1) (W.N_base T₂ h2) (fun y hy => W.map_N π h1 h2 y hy)
  have hcomp : ∀ z, W.map π (W.map ι z) = 0 := fun z => (hexact _).2 ⟨z, rfl⟩
  have hA : ∀ (a : AA K LL) (z : W.DD T₀), W.map ι (a • z) = a • W.map ι z := fun a z =>
    ((W.map ι).restrictScalars (AA K LL)).map_smul a z
  have hAπ : ∀ (a : AA K LL) (z : W.DD T₁), W.map π (a • z) = a • W.map π z := fun a z =>
    ((W.map π).restrictScalars (AA K LL)).map_smul a z
  have hπc : ∀ y : W.DD T₁, W.map π ((letπ : AA K LL) • y) = 0 → W.map π y = 0 := by
    intro y hy
    rw [hAπ, ← algebraMap_smul W.EE (letπ : AA K LL)] at hy
    exact (W.EE_π.smul_left_cancel).mp (hy.trans (smul_zero _).symm)
  have hγ : ∀ y ∈ (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)), W.γ T₀ y ∈
      (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)) := by
    intro y hy
    show W.map ι (W.γD T₀ W.gam y) ∈ W.N T₁
    rw [W.map_γ]
    exact W.N_Γ T₁ W.gam _ hy
  have hγπ : ∀ y ∈ (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)), W.γ T₀ y - y ∈
      ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))).map (smulA W T₀ letπ) := by
    intro y hy
    change W.map ι y ∈ W.N T₁ at hy
    obtain ⟨z, hz, hzeq⟩ := W.N_π T₁ W.gam _ hy
    have h3 : W.map π z = 0 := by
      apply hπc
      rw [← hzeq, map_sub, W.map_γ, hcomp, map_zero, sub_zero]
    obtain ⟨z₀, rfl⟩ := (hexact z).1 h3
    refine ⟨z₀, hz, ?_⟩
    apply hinj
    change W.map ι ((letπ : AA K LL) • z₀) = W.map ι (W.γD T₀ W.gam y - y)
    rw [hA, map_sub, W.map_γ, hzeq]
  have hφ : ∀ y ∈ (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)), ∃ k : ℕ, W.Q ^ k • W.φD T₀ y ∈
      (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)) := by
    intro y hy
    obtain ⟨k, hk⟩ := W.N_φ T₁ _ hy
    refine ⟨k, ?_⟩
    show W.map ι (W.Q ^ k • W.φD T₀ y) ∈ W.N T₁
    rw [hA, W.map_φ]
    exact hk
  have hfree := GlobalTheory.T.wachKernel_intersection_free_of_baseChange D HW F l K s LL h T₀ T₁ T₂ ι π h0 h1 h2 hses hbc
  have hspan := GlobalTheory.T.wachKernel_mem_frobeniusSpan_after_Q_pow D HW F l K s LL h T₀ T₁ T₂ ι π h0 h1 h2 hses
  have heq := key _ hfree hbc hγ hγπ hφ hspan
  rw [← heq]
  exact hx

end GlobalTheory.NL.KerSat
end
end

section

noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.BridgeInertia

variable {l : ℕ} [Fact l.Prime]

theorem valuation_lt_one_iff_norm {Ω : Type} [Field Ω] {A : ValuationSubring Ω} {j : Ω →+* Loc.Om l}
    (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) (x : Ω) : A.valuation x < 1 ↔ ‖j x‖ < 1 := by
  rw [valuation_lt_one_iff', hj, hj, map_inv₀, norm_inv]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h0 : 0 < ‖j x‖ := norm_pos_iff.mpr ((_root_.map_ne_zero _).mpr hx)
    simp only [hx, false_or, not_le, one_lt_inv₀ h0]
    exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

theorem residue_trivial_of_image {Ω : Type} [Field Ω] [IsAlgClosed Ω] (j : Ω →+* Loc.Om l) (σ : GQ l)
    (h : ∀ y : Ω, ‖j y‖ ≤ 1 → ‖σ (j y) - j y‖ < 1) (x : Loc.Om l) (hx : ‖x‖ ≤ 1) : ‖σ x - x‖ < 1 := by
  obtain ⟨y, hy⟩ := (GlobalTheory.PlaceBridge.denseRange_embedding j).exists_dist_lt x one_pos
  rw [dist_eq_norm] at hy
  have hn : ∀ z, ‖σ z‖ = ‖z‖ := fun z => (spectralNorm_eq_of_equiv σ z).symm
  have hadd : ∀ a b : Loc.Om l, ‖a + b‖ ≤ max ‖a‖ ‖b‖ := IsUltrametricDist.norm_add_le_max
  have hjy : ‖j y‖ ≤ 1 := by
    have e : j y = x + -(x - j y) := by ring
    rw [e]
    exact (hadd _ _).trans (max_le hx (by rw [norm_neg]; exact hy.le))
  have e : σ x - x = σ (x - j y) + ((σ (j y) - j y) + -(x - j y)) := by
    rw [map_sub]; ring
  rw [e]
  refine (hadd _ _).trans_lt (max_lt (by rw [hn]; exact hy) ((hadd _ _).trans_lt (max_lt (h y hjy) ?_)))
  rw [norm_neg]; exact hy

theorem mem_Ine_iff {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosed Ω] {A : ValuationSubring Ω}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : ∀ x, x ∈ A ↔ ‖Bw.j x‖ ≤ 1) (σ : ↥(GK Bw.Kw)) :
    ((Bw.e.symm σ : ↥(Dec (F := E) A)) : Ω ≃ₐ[E] Ω) ∈ Ine (F := E) A ↔
      ∀ x : Loc.Om l, ‖x‖ ≤ 1 → ‖(σ : GQ l) x - x‖ < 1 := by
  have hc : ∀ y, (σ : GQ l) (Bw.j y) = Bw.j (((Bw.e.symm σ : ↥(Dec (F := E) A)) : Ω ≃ₐ[E] Ω) y) := fun y => by
    rw [← Bw.e_comm, MulEquiv.apply_symm_apply]
  constructor
  · intro h
    refine residue_trivial_of_image Bw.j _ fun y hy => ?_
    rw [hc, ← map_sub, ← valuation_lt_one_iff_norm hj]
    exact h.2 y ((A.valuation_le_one_iff y).2 ((hj y).2 hy))
  · intro h
    refine ⟨(Bw.e.symm σ).2, fun y hy => ?_⟩
    rw [valuation_lt_one_iff_norm hj, map_sub, ← hc]
    exact h _ ((hj y).1 ((A.valuation_le_one_iff y).1 hy))

theorem inertEq : ∀ D : D7, InertEq D := by
  intro D i w hw
  have : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  have key : ∀ σ : Br.G D.nbr i w hw, σ ∈ Br.inert D.nbr i w hw ↔
      ∀ x : Loc.Om (D.nd.l i), ‖x‖ ≤ 1 → ‖(σ : GQ (D.nd.l i)) x - x‖ < 1 := fun σ =>
    mem_Ine_iff (D.nbr i w hw) (D.nbr_ind i w hw) σ
  refine le_antisymm (fun σ hσ => Subgroup.subset_closure ?_) ?_
  · exact (key σ).1 hσ
  · exact (Subgroup.closure_le _).2 fun σ hσ => (key σ).2 hσ

end GlobalTheory.BridgeInertia

end
end

section

noncomputable section

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem exists_inv_pow_one_add {l : ℕ} [Fact l.Prime] {s : ℕ} (hs : 1 ≤ s) (e : ℕ) (u : ℚ_[l]ˣ)
    (hu : (u : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l])) :
    ∃ U : ℤ_[l], (U : ℚ_[l]) = ((u ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) ∧ (l : ℤ_[l]) ^ s ∣ U - 1 := by
  have hn : (-(l : ℤ_[l]) ^ s) ∈ nonunits ℤ_[l] := by
    rw [PadicInt.mem_nonunits, norm_neg, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (by rw [PadicInt.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)) (by omega)
  have hunit := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hn
  obtain ⟨V, hV⟩ := hunit.exists_left_inv
  refine ⟨V ^ e, ?_, ?_⟩
  · have h1 : (V : ℚ_[l]) * (u : ℚ_[l]) = 1 := by
      have := congrArg (fun z : ℤ_[l] => (z : ℚ_[l])) hV
      rw [hu]
      push_cast at this ⊢
      linear_combination this
    have h2 : (V : ℚ_[l]) = (u : ℚ_[l])⁻¹ := eq_inv_of_mul_eq_one_left h1
    simp [h2]
  · have h1 : (l : ℤ_[l]) ^ s ∣ V - 1 := ⟨-V, by linear_combination hV⟩
    have h2 := sub_dvd_pow_sub_pow V 1 e
    rw [one_pow] at h2
    exact h1.trans h2

theorem zetaQ_pow_level {l : ℕ} [Fact l.Prime] (P : LocPrime l) (s : ℕ) : P.ζQ s ^ (l ^ s) = 1 := by
  induction s with
  | zero => simpa using P.ζQ_zero
  | succ s ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

theorem levSum_mem_Ks {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s j : ℕ) {ι : Type}
    (T : Finset ι) (c : ι → ↥(K0 K)) (m : ι → ℕ) (d : ↥(K0 K)) :
    levSum P K s j T c m d ∈ Ks K s := by
  have h0 : ∀ x : ↥(K0 K), (x : Om l) ∈ Ks K s := fun x => (le_sup_left : K0 K ≤ Ks K s) x.2
  have hζ : P.ζQ s ∈ Ks K s := by
    refine (le_sup_right : _ ≤ Ks K s) (IntermediateField.subset_adjoin _ _ ?_)
    exact zetaQ_pow_level P s
  unfold levSum
  refine add_mem (sum_mem fun i _ => mul_mem (pow_mem (natCast_mem _ _) _) (sum_mem fun a _ =>
    mul_mem (mul_mem (h0 _) (pow_mem (natCast_mem _ _) _)) (pow_mem hζ _)))
    (mul_mem (pow_mem (natCast_mem _ _) _) (h0 _))

theorem expStar_levSum : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ) (g : GQ l), g ∈ Gj K s → ((LT l).χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) → ∀ (ι : Type) (T : Finset ι) (c : ι → ↥(K0 K)) (m : ι → ℕ) (d : ℕ → ↥(K0 K)), (∀ i ∈ T, ‖(c i : Om l)‖ ≤ 1 ∧ ¬ l ∣ m i) → (∀ j ≤ e, ‖(d j : Om l)‖ ≤ 1 ∧ d j - (l : ↥(K0 K)) ^ j * frK (LT l) K (d j) = (frK (LT l) K ^ s) (∑ i ∈ T, c i * (m i : ↥(K0 K)) ^ j)) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (algebraMap ℚ_[l] (Om l) (logZl l ((1 + l ^ s : ℕ) : ℚ_[l]) * ((e.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * e)))⁻¹ * levSum (LT l) K s e T c m (d e)) := by
  intro LT l _ AI hT K s hs e g hg hχ ι T c m d hc hd
  classical
  obtain ⟨U, hU, hU1⟩ := exists_inv_pow_one_add hs.1 e ((LT l).χQ g) hχ
  have hgen : IsGen (LT l).χQ K s g := by
    refine ⟨hg, ?_⟩
    rw [hχ]
    push_cast
    rw [add_sub_cancel_left, Padic.norm_p_pow]
  have hw : ∀ i, ∃ w : Ainf l, i ∈ T → Lifts AI K w (c i) := by
    intro i
    by_cases hi : i ∈ T
    · obtain ⟨w, hw⟩ := GlobalTheory.T.exists_lifts_of_norm_le_one_alt l (LT l) AI hT K (c i) (hc i hi).1
      exact ⟨w, fun _ => hw⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose w hw using hw
  obtain ⟨y, hy, hexp⟩ := GlobalTheory.T.frobeniusSolution_expansion_mod_filtration l (LT l) AI hT K s ι T w c m (e + 1) d (by omega) hw
    (fun j hj => hd j (by omega))
  have hsolv : Solv AI K s g U (y - WittVector.frobenius y) := by
    rw [hy]
    refine Solv.sum T _ fun i hi => ?_
    exact (GlobalTheory.T.ainfCocycleSolution_teichmullerEpsilonRoot_pow l (LT l) AI K s hs g hχ U hU1 (m i) (hc i hi).2).mul
      ((hw i hi).act (Gj_le_fix s hg)) (fun h hh => (hw i hi).act (Hinf_le_fix hh))
  obtain ⟨b, hb0, hbH, z₀, hz₀⟩ := GlobalTheory.T.exists_deRham_element_of_cocycleRecursion l (LT l) AI hT K s hs g U (e + 1) (by omega) y hsolv
  obtain ⟨z, hz, hE⟩ := GlobalTheory.T.expStar_of_low_terms_removed LT l AI hT K s hs e g hgen
    (fun j => algebraMap ℚ_[l] (Om l) ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ *
      levSum (LT l) K s j T c m (d j))
    (fun j => mul_mem (IntermediateField.algebraMap_mem _ _) (levSum_mem_Ks _ _ _ _ _ _ _ _))
    b hb0 hbH ⟨z₀, by
      have := add_mem hz₀ hexp
      rw [hU] at this
      convert this using 1
      ring⟩
  refine ⟨z, hz, ?_⟩
  rw [hχ, ← mul_assoc, ← map_mul, ← mul_inv] at hE
  exact hE

end GlobalTheory.ExpImage
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.existsNonzeroFrobVectorResidueZero_proof : ExII := by
  first | exact @GlobalTheory.PMon.exII_holds | exact GlobalTheory.PMon.exII_holds | (intros; apply GlobalTheory.PMon.exII_holds <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.lubinTateTwistTotalWeightZero_proof : TwistStep := by
  first | exact @GlobalTheory.PMon.twistStep | exact GlobalTheory.PMon.twistStep | (intros; apply GlobalTheory.PMon.twistStep <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.mooreDeterminant_crisPlus_ne_zero : Moore := by
  first | exact @GlobalTheory.PMon.moore_statement | exact GlobalTheory.PMon.moore_statement | (intros; apply GlobalTheory.PMon.moore_statement <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.CongIndex

theorem bounded_cover {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {J : Subgroup (GAf L n)}
    (hJ : IsBounded J) {M : ℕ} (hM : 0 < M) :
    ∃ F : Finset (GAf L n), ∀ κ ∈ J, ∃ f ∈ F, NG.Cong L n M (f⁻¹ * κ) := by
  classical
  obtain ⟨F0, hF0⟩ := hJ
  obtain ⟨F1, hF1⟩ := GlobalTheory.AlgFormsFin.exists_cover L n hM
  refine ⟨(F0 ×ˢ F1).image (fun p => p.1 * p.2), fun κ hκ => ?_⟩
  obtain ⟨f0, hf0, hu⟩ := hF0 κ hκ
  obtain ⟨j, hj, κ', hκ', e⟩ := hF1 _ hu
  refine ⟨f0 * j, Finset.mem_image.2 ⟨(f0, j), Finset.mem_product.2 ⟨hf0, hj⟩, rfl⟩, ?_⟩
  have h1 : (f0 * j)⁻¹ * κ = κ' := by
    rw [mul_inv_rev, mul_assoc, e, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [h1]
  exact hκ'

theorem finite_index_conj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J : Subgroup (GAf L n)),
    IsBounded J → ∀ (h : GAf L n) (N : ℕ), 0 < N →
      (∃ N' : ℕ, 0 < N' ∧ ∀ κ, NG.Cong L n N' κ → NG.Cong L n N (h⁻¹ * κ * h)) ∧
      (∃ F : Finset (GAf L n), ∀ κ ∈ J, ∃ f ∈ F, NG.Cong L n N (f⁻¹ * κ)) ∧
      IsBounded (J.map (MulAut.conj h).toMonoidHom) := by
  intro L _ _ _ n J hJ h N hN
  refine ⟨GlobalTheory.CongConjugate.congConj L n h N hN, bounded_cover hJ hN, ?_⟩
  classical
  obtain ⟨N', hN', hc⟩ := GlobalTheory.CongConjugate.congConj L n h⁻¹ 1 one_pos
  obtain ⟨F, hF⟩ := bounded_cover hJ hN'
  refine ⟨F.image (fun f => h * f * h⁻¹), fun x hx => ?_⟩
  obtain ⟨κ, hκ, rfl⟩ := Subgroup.mem_map.1 hx
  obtain ⟨f, hf, hcf⟩ := hF κ hκ
  refine ⟨h * f * h⁻¹, Finset.mem_image_of_mem _ hf, ?_⟩
  have hu := (hc _ hcf).1
  have e : (h * f * h⁻¹)⁻¹ * (MulAut.conj h).toMonoidHom κ = h⁻¹⁻¹ * (f⁻¹ * κ) * h⁻¹ := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]
  rw [e]
  exact hu

end GlobalTheory.CongIndex

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.WeilPairing



theorem thetaInner_weilRep : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsWeilDatumO ψ V W χV χW om → IsCovolOne (ratL W V) μ 𝓕 → ∀ (p : GA D V × GA D W) (a b : WO V W → ℂ), IsThetaFunO ψ V W a → IsThetaFunO ψ V W b → thetaIP μ 𝓕 (om p a) (om p b) = thetaIP μ 𝓕 a b := by
  intro D ψ V W χV χW om μ 𝓕 hom hc p a b ha hb
  have h := GlobalTheory.WeilInner.om_inner D ψ V W χV χW om hom μ 𝓕 hc p b a hb ha
  have e : ∀ (f g : WO V W → ℂ), thetaIP μ 𝓕 f g = ∫ w in 𝓕, g w * (starRingEnd ℂ) (f w) ∂μ := fun f g => by
    unfold thetaIP
    congr 1
    funext w
    exact mul_comm _ _
  rw [e, e]
  exact h

end GlobalTheory.WeilPairing
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke GlobalTheory.RawLift
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lattice_index_split_place_eq_product_local : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (W : HSp D) (β : GL (Fin W.rank) (Fv D.host.F v)), Frame W e π β → ∀ g : GA D W, SuppAt e W g → latIndex W g = ((Submodule.span (Ov D v) (Set.range (Pi.basisFun (Fv D.host.F v) (Fin W.rank)))).map ((((rho W π β g : GL (Fin W.rank) (Fv D.host.F v)) : Matrix (Fin W.rank) (Fin W.rank) (Fv D.host.F v)).mulVecLin).restrictScalars (Ov D v))).toAddSubgroup.relIndex (Submodule.span (Ov D v) (Set.range (Pi.basisFun (Fv D.host.F v) (Fin W.rank)))).toAddSubgroup * ((Submodule.span (Ov D v) (Set.range (Pi.basisFun (Fv D.host.F v) (Fin W.rank)))).map ((((rho W π β g⁻¹ : GL (Fin W.rank) (Fv D.host.F v)) : Matrix (Fin W.rank) (Fin W.rank) (Fv D.host.F v))ᵀ.mulVecLin).restrictScalars (Ov D v))).toAddSubgroup.relIndex (Submodule.span (Ov D v) (Set.range (Pi.basisFun (Fv D.host.F v) (Fin W.rank)))).toAddSubgroup := by
  first | exact @GlobalTheory.SplitIndexLocal.latIndex_split_local | exact GlobalTheory.SplitIndexLocal.latIndex_split_local | (intros; apply GlobalTheory.SplitIndexLocal.latIndex_split_local <;> assumption)
end
