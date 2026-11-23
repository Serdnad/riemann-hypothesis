module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1306
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle019
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FderivIntegralApplyOfHolomorphicOfDominated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1296
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.HSAmp

theorem loc_continuousOn_holo : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (σ : k →+* ℂ) (f : X.functionField), f ∈ P.H a b → ∀ i j, ContinuousOn (ratVal (q := p) (σ := σ) (P.loc a b f i j)) (ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j)) ∧ ∀ (D : ℕ) (c : AlgChart p σ D), DifferentiableOn ℂ (fun v => ratVal (P.loc a b f i j) (c.e.symm v)) (c.e.target ∩ c.e.symm ⁻¹' (ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j))) := by
  intro k _ X _ p P a b σ f hf i j
  have key : ∀ y ∈ ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j), ∃ (W : X.Opens) (hW : genericPoint X ∈ W)
      (g : Γ(X, W)), y ∈ ptsIn p σ W ∧ P.loc a b f i j = fnOf W hW g := by
    intro y hy
    have hr : RegAt (under y) (P.loc a b f i j) := hf _ i j (mem_ptsIn.1 hy.1) (mem_ptsIn.1 hy.2)
    obtain ⟨W, hx, g, e⟩ := hr.exists_fnOf
    exact ⟨W, gen_mem hx, g, mem_ptsIn.2 hx, e.symm⟩
  refine ⟨fun y hy => ?_, fun D c => ?_⟩
  · obtain ⟨W, hW, g, hy', e⟩ := key y hy
    have hc : ContinuousAt (ratVal (q := p) (σ := σ) (P.loc a b f i j)) y := by
      refine ((continuousOn_ev (p := p) (σ := σ) g).continuousAt ((isOpen_ptsIn W).mem_nhds hy')).congr ?_
      filter_upwards [(isOpen_ptsIn W).mem_nhds hy'] with z hz
      rw [e, ratVal_fnOf hz]
    exact hc.continuousWithinAt
  · intro v hv
    obtain ⟨W, hW, g, hy', e⟩ := key _ hv.2
    have hO : IsOpen (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ W) :=
      c.e.isOpen_inter_preimage_symm (isOpen_ptsIn W)
    have hm : v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ W := ⟨hv.1, hy'⟩
    have hd := (c.holo W g).differentiableAt (hO.mem_nhds hm)
    refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hO.mem_nhds hm] with w hw
    rw [e, ratVal_fnOf hw.2]
    rfl

end GlobalTheory.HSAmp
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.MultDer

theorem rderC_eq : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T → ∀ (v : M.Vec) (τ : D.what₂.Tau) (Z : Mt V.rank) (y : M.sm τ), (y : M.H τ) = dRepC (gramAt D V τ) (M.rep τ) Z (v τ : M.H τ) → RderC θ V τ Z (T v) = T (Function.update v τ y) := by
  intro D θ V _ S M J χ T hT v τ Z y hy
  obtain ⟨hc, hU, -⟩ := GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ
  have hu := GlobalTheory.SmoothAutCheck.gramAt_unit V τ
  obtain ⟨hsp, hsm⟩ := GlobalTheory.T.smoothVectors_subspace_stable_sobolevForm_deriv V.rank (gramAt D V τ) (M.H τ) (M.rep τ)
    (GlobalTheory.SmoothAutCheck.gramAt_herm V τ) hu.ne_zero hU
  have hv : SmoothVec (lieH (gramAt D V τ)) (M.rep τ) (v τ : M.H τ) := hsp _ (v τ).2
  obtain ⟨h1, -, -, h4⟩ := hsm _ hv
  funext g
  obtain ⟨ℓ, hℓ, hval⟩ := hT.cont τ v g
  have key : ∀ X ∈ lieAt V τ, Rder θ V τ X (T v) g = ℓ (dRep (M.rep τ) X (v τ : M.H τ)) := by
    intro X hX
    have e : (fun t : ℝ => T v (g * oneP θ V τ X t)) =
        fun t : ℝ => ℓ (M.rep τ (NormedSpace.exp (t • X)) (v τ : M.H τ)) := by
      funext t
      have hm := GlobalTheory.SmoothAutCheck.exp_mem_UH hu hX t
      let w : M.sm τ := ⟨M.rep τ (NormedSpace.exp (t • X)) (v τ : M.H τ), Submodule.subset_span (h1 _ hm)⟩
      have h := congrFun (hT.equiv τ _ hm v w rfl) g
      exact ((hval w).trans h).symm
    unfold Rder
    rw [e]
    exact (h4 ℓ hℓ X hX).deriv
  obtain ⟨p1, p2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  have h := hval y
  rw [hy] at h
  refine Eq.trans ?_ h
  unfold RderC dRepC
  rw [Pi.add_apply, Pi.smul_apply, key _ p1, key _ p2, map_add (f := _), map_smul]
  rfl

end GlobalTheory.MultDer
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TransvMeasure

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

theorem exists_fundamentalDomain_subset [SecondCountableTopology G] (Γ : Subgroup G) [DiscreteTopology Γ] {K : Set G}
    (hK : IsClosed K) (hcov : ∀ x : G, ∃ γ ∈ Γ, γ * x ∈ K) (μ : Measure G) :
    ∃ S ⊆ K, IsFundamentalDomain Γ S μ := by
  classical
  have := GlobalTheory.countable_of_discrete_subgroup Γ
  obtain ⟨D, hD, hu, -⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup Γ
  obtain ⟨c, hc⟩ := exists_injective_nat Γ
  let S : Set G := K ∩ ⋃ g : Γ, ((fun y => g • y) ⁻¹' D ∩ ⋂ h : Γ, ⋂ _ : c h < c g, ((fun y => (h⁻¹ * g) • y) ⁻¹' K)ᶜ)
  have hS : ∀ y, y ∈ S ↔ y ∈ K ∧ ∃ g : Γ, g • y ∈ D ∧ ∀ h : Γ, c h < c g → (h⁻¹ * g) • y ∉ K := fun y => by
    simp only [S, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff]
  refine ⟨S, Set.inter_subset_left, IsFundamentalDomain.mk' (MeasurableSet.nullMeasurableSet ?_) fun x => ?_⟩
  · exact hK.measurableSet.inter <| MeasurableSet.iUnion fun g => (measurable_const_smul g hD).inter <|
      MeasurableSet.iInter fun h => MeasurableSet.iInter fun _ => (measurable_const_smul _ hK.measurableSet).compl
  · obtain ⟨d, hd, hdu⟩ := hu x
    have hex : ∃ n, ∃ g : Γ, c g = n ∧ (g⁻¹ * d) • x ∈ K := by
      obtain ⟨γ, hγ, h⟩ := hcov x
      refine ⟨_, d * (⟨γ, hγ⟩ : Γ)⁻¹, rfl, ?_⟩
      rw [_root_.mul_inv_rev, inv_inv, inv_mul_cancel_right]
      exact h
    obtain ⟨g, hg, hgK⟩ := Nat.find_spec hex
    refine ⟨g⁻¹ * d, (hS _).2 ⟨hgK, g, ?_, fun h hh hK' => ?_⟩, fun k hk => ?_⟩
    · rw [smul_smul, mul_inv_cancel_left]; exact hd
    · refine Nat.find_min hex (hg ▸ hh) ⟨h, rfl, ?_⟩
      rwa [smul_smul, mul_assoc, mul_inv_cancel_left] at hK'
    · obtain ⟨hkK, g', h1, h2⟩ := (hS _).1 hk
      rw [smul_smul] at h1
      have e : g' * k = d := hdu _ h1
      have ek : k = g'⁻¹ * d := by rw [← e, inv_mul_cancel_left]
      have hle : Nat.find hex ≤ c g' := Nat.find_min' hex ⟨g', rfl, ek ▸ hkK⟩
      rcases hle.eq_or_lt with h | h
      · rw [ek, hc (hg.trans h)]
      · refine (h2 g (hg ▸ h) ?_).elim
        rw [smul_smul, mul_assoc, e]
        exact hgK


open Pointwise in
theorem measure_ne_top_of_cocompact (Γ : Subgroup G) [Countable Γ] {K : Set G} (hK : IsCompact K)
    (hcov : ∀ x : G, ∃ γ ∈ Γ, γ * x ∈ K) (μ : Measure G) [μ.IsHaarMeasure] {F : Set G}
    (hF : IsFundamentalDomain Γ F μ) : μ F ≠ ⊤ := by
  have hsub : F ⊆ ⋃ γ : Γ, ((γ • K) ∩ F) := by
    intro g hg
    obtain ⟨γ, hγ, hk⟩ := hcov g
    refine Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hg⟩
    rw [Set.mem_inv_smul_set_iff]
    exact hk
  refine ne_of_lt ?_
  calc μ F ≤ μ (⋃ γ : Γ, ((γ • K) ∩ F)) := measure_mono hsub
    _ ≤ ∑' γ : Γ, μ ((γ • K) ∩ F) := measure_iUnion_le _
    _ = μ K := (hF.measure_eq_tsum K).symm
    _ < ⊤ := hK.measure_lt_top

end General

theorem exists_sub_mem_of_isOpen (F : Type) [Field F] [NumberField F] (W : AddSubgroup (AF F))
    (hW : IsOpen (W : Set (AF F))) (a : AF F) : ∃ x : F, a - algebraMap F (AF F) x ∈ W := by
  obtain ⟨K, hK, hx⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  let H : AddSubgroup (AF F) := (algebraMap F (AF F)).toAddMonoidHom.range ⊔ W
  have hH : IsOpen (H : Set (AF F)) := AddSubgroup.isOpen_mono le_sup_right hW
  have hd : DiscreteTopology (AF F ⧸ H) := QuotientAddGroup.discreteTopology hH
  have hf : Finite (AF F ⧸ H) := by
    have h1 : (QuotientAddGroup.mk '' K : Set (AF F ⧸ H)).Finite :=
      (hK.image QuotientAddGroup.continuous_mk).finite_of_discrete
    refine Set.finite_univ_iff.1 (h1.subset fun q _ => ?_)
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨x, h⟩ := hx b
    refine ⟨_, h, QuotientAddGroup.eq.2 ?_⟩
    have : -(b - algebraMap F (AF F) x) + b = algebraMap F (AF F) x := by ring
    rw [this]
    exact AddSubgroup.mem_sup_left ⟨x, rfl⟩
  have hn : (H.index : F) ≠ 0 := Nat.cast_ne_zero.2 H.index_ne_zero_of_finite
  have hm := H.nsmul_index_mem ((H.index : F)⁻¹ • a)
  rw [← Nat.cast_smul_eq_nsmul F, smul_smul, mul_inv_cancel₀ hn, one_smul] at hm
  obtain ⟨_, ⟨x, rfl⟩, w, hw, e⟩ := AddSubgroup.mem_sup.1 hm
  refine ⟨x, ?_⟩
  rw [← e]
  simpa using hw

theorem map_proj {R A n : Type} [CommRing R] [CommRing A] [DecidableEq n] (f : R →+* A) (ε : R) (M : Matrix n n R) :
    (f ε = 0 → (1 + ε • (M - 1)).map f = 1) ∧ (f ε = 1 → (1 + ε • (M - 1)).map f = M.map f) := by
  constructor <;> intro h <;> ext i j <;> by_cases hij : i = j <;> simp [h, Matrix.one_apply, hij]

theorem continuous_proj {X R n : Type} [TopologicalSpace X] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [DecidableEq n] (ε : R) {M : X → Matrix n n R} (h : Continuous M) : Continuous fun x => 1 + ε • (M x - 1) :=
  continuous_const.add ((h.sub continuous_const).const_smul ε)

theorem proj_smul {R n : Type} [CommRing R] [DecidableEq n] (ε a : R) {M M' N : Matrix n n R}
    (h : M' = 1 + ε • (M - 1)) (ha : M - 1 = a • N) : M' - 1 = (ε * a) • N := by
  rw [h, ha, add_sub_cancel_left, smul_smul]

variable {D : D7}

theorem exists_finite_projection_mat (V : HSp D) : ∃ (p : GA D V →* GA D V) (ε : AE D), (∀ g, infHom V (p g) = 1) ∧
    (∀ g, finHom V (p g) = finHom V g) ∧ ∀ g, (matHom V (p g)).1 = 1 + ε • ((matHom V g).1 - 1) := by
  choose q h1 h2 using fun g : GA D V =>
    GlobalTheory.UnitarySplit.ga_glue V 1 _ (one_mem _) (GlobalTheory.UnitarySplit.finHom_mem V g)
  obtain ⟨ε, e1, e2⟩ := GlobalTheory.UnitarySplit.parts_surj D 0 1
  refine ⟨MonoidHom.mk' q fun a b => GlobalTheory.UnitarySplit.ga_ext V
    (by rw [map_mul, h1, h1, h1, mul_one]) (by rw [h2, map_mul, map_mul, h2, h2]), ε, h1, h2, fun g => ?_⟩
  refine GlobalTheory.UnitarySplit.mat_ext (infPart D) (finPart D) (GlobalTheory.UnitarySplit.parts_inj D) ?_ ?_
  · exact (congrArg Units.val (h1 g)).trans ((map_proj (infPart D) ε _).1 e1).symm
  · exact (congrArg Units.val (h2 g)).trans ((map_proj (finPart D) ε _).2 e2).symm

theorem exists_finite_projection (V : HSp D) : ∃ p : GA D V →* GA D V, Continuous p ∧ (∀ g, p g ∈ GfC V) ∧
    (∀ g, g * (p g)⁻¹ ∈ GinfC V) ∧ ∀ ξ, ∀ g ∈ ZI V ξ, p g ∈ ZI V ξ := by
  obtain ⟨p, ε, h1, h2, hm⟩ := exists_finite_projection_mat V
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have i0 := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hc : Continuous fun h : GA D V => (matHom V h).1 :=
    Units.continuous_val.comp (continuous_subtype_val (p := (· ∈ HR (AF D.host.F) D.sp.cm.sig V.gram)))
  have hc' : Continuous fun g : GA D V => (matHom V (p g)).1 :=
    (continuous_proj (R := AE D) ε hc).congr fun g => (hm g).symm
  refine ⟨p, ?_, h1, fun g => ?_, fun ξ g hg => ?_⟩
  · have h3 : Continuous fun g : GA D V => matHom V (p g) := by
      refine Units.continuous_iff.2 ⟨hc', (hc'.comp (continuous_inv (G := GA D V))).congr fun g => ?_⟩
      rw [Function.comp_apply, map_inv, map_inv]
    exact continuous_induced_rng.2 h3
  · change finHom V (g * (p g)⁻¹) = 1
    rw [map_mul, map_inv, h2 g, mul_inv_cancel]
  · have : ZI V ξ ≤ (ZI V ξ).comap p := by
      refine (Subgroup.closure_le _).2 ?_
      rintro g ⟨a, ha⟩
      exact Subgroup.subset_closure ⟨ε * a, proj_smul ε a (hm g) ha⟩
    exact this hg

theorem transvection_measure : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ ξ, IsoVec V ξ → (∃ (μ : Measure (ZI V ξ)) (𝓕 : Set (ZI V ξ)), μ.IsHaarMeasure ∧ IsFundamentalDomain ((GQ V).subgroupOf (ZI V ξ)) 𝓕 μ ∧ IsCompact (closure 𝓕)) ∧ (∀ (μ : Measure (ZI V ξ)) (𝓕 : Set (ZI V ξ)), μ.IsHaarMeasure → IsFundamentalDomain ((GQ V).subgroupOf (ZI V ξ)) 𝓕 μ → μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤) ∧ ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) → ∀ z ∈ ZI V ξ, ∃ γ ∈ ZI V ξ, γ ∈ GQ V ∧ ∃ u ∈ ZI V ξ, u ∈ GinfC V ∧ ∃ k ∈ ZI V ξ, k ∈ GfC V ∧ k ∈ U ∧ z = γ * u * k := by
  intro D θ V hθ ξ hξ
  obtain ⟨⟨e, he⟩, -⟩ := GlobalTheory.T.adelicTransvectionSubgroup_eq_adeles_closed D θ V hθ ξ hξ
  have i0 := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have i4 := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  obtain ⟨-, i2, i3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  have : LocallyCompactSpace (Multiplicative (AF D.host.F)) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele _
  have : LocallyCompactSpace (ZI V ξ) := e.toHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  have : BorelSpace (ZI V ξ) := Subtype.borelSpace _
  have : SecondCountableTopology (ZI V ξ) := TopologicalSpace.Subtype.secondCountableTopology _
  have hd : DiscreteTopology ((GQ V).subgroupOf (ZI V ξ)) := by
    obtain ⟨U, hU, hx⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero D.host.F
    refine discreteTopology_of_isOpen_singleton_one ?_
    rw [isOpen_singleton_iff_nhds_eq_pure]
    refine le_antisymm (Filter.le_pure_iff.2 ?_) (pure_le_nhds _)
    have hc : ContinuousAt (fun x : (GQ V).subgroupOf (ZI V ξ) => Multiplicative.toAdd (e.symm x)) 1 :=
      (continuous_toAdd.comp (e.symm.continuous.comp continuous_subtype_val)).continuousAt
    refine Filter.mem_of_superset (hc.preimage_mem_nhds (by simpa using hU)) ?_
    rintro ⟨z, hz⟩ hy
    obtain ⟨a, rfl⟩ := e.surjective z
    obtain ⟨x, hxa⟩ := (he a).1 hz
    have hy' : Multiplicative.toAdd a ∈ U := by simpa using hy
    have h0 : x = 0 := hx x (hxa ▸ hy')
    have : a = 1 := by
      rw [h0, map_zero] at hxa
      exact Multiplicative.toAdd.injective hxa.symm
    subst this
    exact Subtype.ext (map_one e)
  have := GlobalTheory.countable_of_discrete_subgroup ((GQ V).subgroupOf (ZI V ξ))
  obtain ⟨K, hK, hKx⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele D.host.F
  have hK' : IsCompact ((fun a => e (Multiplicative.ofAdd a)) '' K) :=
    hK.image (e.continuous.comp continuous_ofAdd)
  have hcov : ∀ z : ZI V ξ, ∃ γ ∈ (GQ V).subgroupOf (ZI V ξ), γ * z ∈ (fun a => e (Multiplicative.ofAdd a)) '' K := by
    intro z
    obtain ⟨a, rfl⟩ := e.surjective z
    obtain ⟨x, hx⟩ := hKx a.toAdd
    refine ⟨e (Multiplicative.ofAdd (algebraMap _ _ (-x))), (he _).2 ⟨-x, rfl⟩, _, hx, ?_⟩
    beta_reduce
    rw [← map_mul, map_neg, sub_eq_neg_add]
    rfl
  refine ⟨?_, fun μ 𝓕 hμ h𝓕 => ⟨h𝓕.measure_ne_zero (NeZero.ne μ), measure_ne_top_of_cocompact _ hK' hcov μ h𝓕⟩,
    fun U hU z hz => ?_⟩
  · obtain ⟨S, hS, h⟩ := exists_fundamentalDomain_subset _ hK'.isClosed hcov Measure.haar
    exact ⟨Measure.haar, S, inferInstance, h, hK'.closure_of_subset hS⟩
  · obtain ⟨p, hp, h1, h2, h3⟩ := exists_finite_projection V
    let f : Multiplicative (AF D.host.F) →* GA D V := p.comp ((ZI V ξ).subtype.comp e.toMulEquiv.toMonoidHom)
    have hf : Continuous f := hp.comp (continuous_subtype_val.comp e.continuous)
    obtain ⟨a, ha⟩ := e.surjective ⟨z, hz⟩
    obtain ⟨x, hx⟩ := exists_sub_mem_of_isOpen D.host.F (Subgroup.toAddSubgroup' (U.comap f))
      (hU.preimage (hf.comp continuous_ofAdd)) a.toAdd
    set k : ZI V ξ := e (Multiplicative.ofAdd (a.toAdd - algebraMap _ _ x)) with hk
    have hkU : p k ∈ U := hx
    refine ⟨e (Multiplicative.ofAdd (algebraMap _ _ x)), SetLike.coe_mem _, (he _).2 ⟨x, rfl⟩,
      k * (p k)⁻¹, mul_mem k.2 (inv_mem (h3 ξ _ k.2)), h2 _, p k, h3 ξ _ k.2, h1 _, hkU, ?_⟩
    rw [mul_assoc, inv_mul_cancel_right, hk, ← Subgroup.coe_mul, ← map_mul, ← ofAdd_add, add_sub_cancel,
      ofAdd_toAdd, ha]

end GlobalTheory.TransvMeasure
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem UpT.diag_ne_zero {n : ℕ} {b : Mt n} (hb : UpT b) (a : Fin n) : b a a ≠ 0 := by
  have hdet : b.det = ∏ i, b i i := Matrix.det_of_upperTriangular (fun i j hij => hb.2 i j hij)
  have h := hb.1
  rw [hdet, Finset.prod_ne_zero_iff] at h
  exact h a (Finset.mem_univ a)

theorem holFn_integral : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Hm : ι → Mt n) (q : ι → ℕ) (x₀ : ι → Mt n) (w : ι → Fin n → ℤ), (∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) → ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) [IsFiniteMeasure ν] (f : Ω → (ι → Mt n) → ℂ) (C : ℝ), (∀ o, HolFn Hm q x₀ w (f o)) → (∀ o, ∀ u ∈ UG Hm, ‖f o u‖ ≤ C) → (∀ u ∈ UG Hm, AEStronglyMeasurable (fun o => f o u) ν) → HolFn Hm q x₀ w fun u => ∫ o, f o u ∂ν := by
  intro n ι _ _ Hm q x₀ w hx Ω _ ν _ f C hf hC hmeas

  have hf' : ∀ o, ∃ P, HolSec Hm q w P ∧ ∀ u ∈ UG Hm, f o u = P fun τ => (u τ * x₀ τ : Mt n) := hf
  choose Pc hPc using hf'

  have hβ := fun τ => GlobalTheory.T.smooth_gram_schmidt_indefinite_hermitian_frames n (Hm τ) (q τ) (x₀ τ) (hx τ)
  choose β hβc hβ using hβ
  obtain ⟨hopen, -, hmul, hx0⟩ := GlobalTheory.T.negativeFrameDomainProduct_open_preconnected_stable n ι Hm q x₀ hx

  let uu : (ι → Fin n → Fin n → ℂ) → ι → Mt n :=
    fun y τ => Matrix.of (y τ) * (Matrix.of (β τ (y τ)))⁻¹ * (x₀ τ)⁻¹
  let cc : (ι → Fin n → Fin n → ℂ) → ℂ := fun y => ∏ τ, ∏ a, (β τ (y τ)) a a ^ w τ a
  have huu : ∀ y ∈ frDoms Hm q, uu y ∈ UG Hm := fun y hy τ => (hβ τ (y τ) (hy τ)).2

  have hkey : ∀ o, ∀ y ∈ frDoms Hm q, Pc o y = cc y * f o (uu y) := by
    intro o y hy
    have hu := huu y hy
    have hone : ∀ _τ : ι, UpT (1 : Mt n) := fun _ =>
      ⟨by simp, fun a c hca => Matrix.one_apply_ne (ne_of_gt hca)⟩
    have hfr : (fun τ => (uu y τ * x₀ τ : Mt n)) ∈ frDoms Hm q := by
      have := hmul (uu y) hu (fun _ => 1) hone (fun τ => (x₀ τ : Mt n)) hx0
      simp only [Matrix.mul_one] at this
      exact this
    have hB : ∀ τ, UpT (Matrix.of (β τ (y τ))) := fun τ => (hβ τ (y τ) (hy τ)).1
    have heq := (hPc o).1.2 (fun τ => (uu y τ * x₀ τ : Mt n)) hfr
      (fun τ => Matrix.of (β τ (y τ))) hB
    have hrec : (fun τ => (Matrix.of ((uu y τ * x₀ τ : Mt n)) * Matrix.of (β τ (y τ)) : Mt n)) = y := by
      funext τ
      have hX : (x₀ τ)⁻¹ * x₀ τ = 1 :=
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hx0 τ).1)
      have hBB : (Matrix.of (β τ (y τ)))⁻¹ * Matrix.of (β τ (y τ)) = 1 :=
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hB τ).1)
      show Matrix.of (y τ) * (Matrix.of (β τ (y τ)))⁻¹ * (x₀ τ)⁻¹ * x₀ τ * Matrix.of (β τ (y τ)) = y τ
      rw [Matrix.mul_assoc (Matrix.of (y τ) * (Matrix.of (β τ (y τ)))⁻¹), hX, Matrix.mul_one,
        Matrix.mul_assoc, hBB, Matrix.mul_one]
      rfl
    rw [hrec] at heq
    rw [heq, ← (hPc o).2 (uu y) hu]
    rfl

  have hcc : ContinuousOn cc (frDoms Hm q) := by
    apply continuousOn_finsetProd _
    intro τ _
    apply continuousOn_finsetProd _
    intro a _
    have h1 : ContinuousOn (fun y : ι → Fin n → Fin n → ℂ => β τ (y τ)) (frDoms Hm q) :=
      (hβc τ).continuousOn.comp (continuous_apply τ).continuousOn (fun y hy => hy τ)
    have h2 : ContinuousOn (fun y : ι → Fin n → Fin n → ℂ => β τ (y τ) a a) (frDoms Hm q) :=
      (show Continuous fun M : Fin n → Fin n → ℂ => M a a from
        (continuous_apply a).comp (continuous_apply a)).comp_continuousOn h1
    exact h2.zpow₀ _ (fun y hy => Or.inl (UpT.diag_ne_zero (hβ τ (y τ) (hy τ)).1 a))
  have hPmeas : ∀ y ∈ frDoms Hm q, AEStronglyMeasurable (fun o => Pc o y) ν := by
    intro y hy
    have : (fun o => Pc o y) = fun o => cc y * f o (uu y) := funext fun o => hkey o y hy
    rw [this]
    exact (hmeas (uu y) (huu y hy)).const_mul (cc y)
  have hdom : ∀ x ∈ frDoms Hm q, ∃ s ∈ 𝓝 x, ∃ bound : Ω → ℝ, Integrable bound ν ∧
      ∀ᵐ o ∂ν, ∀ y ∈ s, ‖Pc o y‖ ≤ bound o := by
    intro x hxm
    have hca : ContinuousAt cc x := hcc.continuousAt (hopen.mem_nhds hxm)
    have hev : ∀ᶠ y in 𝓝 x, ‖cc y‖ < ‖cc x‖ + 1 :=
      hca.norm.eventually (Iio_mem_nhds (lt_add_one _))
    refine ⟨{y | ‖cc y‖ < ‖cc x‖ + 1} ∩ frDoms Hm q, Filter.inter_mem hev (hopen.mem_nhds hxm),
      fun _ => (‖cc x‖ + 1) * max C 0, integrable_const _, Filter.Eventually.of_forall ?_⟩
    intro o y hy
    rw [hkey o y hy.2, norm_mul]
    exact mul_le_mul hy.1.le (le_max_of_le_left (hC o (uu y) (huu y hy.2))) (norm_nonneg _)
      (by positivity)
  unfold HolFn HolSec
  refine ⟨fun y => ∫ o, Pc o y ∂ν, ⟨?_, ?_⟩, ?_⟩
  · exact (GlobalTheory.differentiableOn_integral_of_holomorphic_of_locally_dominated hopen hPmeas
      (Filter.Eventually.of_forall fun o => (hPc o).1.1) hdom).1
  · intro x hxm b hb
    calc ∫ o, Pc o (fun τ => (Matrix.of (x τ) * b τ : Mt n)) ∂ν
        = ∫ o, (∏ τ, ∏ a, b τ a a ^ w τ a) * Pc o x ∂ν :=
          integral_congr_ae (Filter.Eventually.of_forall fun o => (hPc o).1.2 x hxm b hb)
      _ = (∏ τ, ∏ a, b τ a a ^ w τ a) * ∫ o, Pc o x ∂ν := integral_const_mul _ _
  · intro u hu
    exact integral_congr_ae (Filter.Eventually.of_forall fun o => (hPc o).2 u hu)

end GlobalTheory.HolDict
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

namespace GlobalTheory.VolBr

theorem exists_finite_controlling_points : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∃ S : Set X, S.Finite ∧ ∀ (x : X) i j, x ∈ P.L.B.U i → x ∈ P.A.B.U j → ∀ τ g : X.functionField, RegAt x τ → (∀ z ∈ S, z ⤳ x → UnitAt z τ) → RegAt x g → RegAt x (g * τ / P.loc 0 1 s i j) → RegAt x (g / P.loc 0 1 s i j) := by
  intro k _ X _ p D hX P s hs hs0
  have : IsNoetherian X := hX.isNoetherian
  have hloc0 : ∀ (i : P.L.B.ι) (j : P.A.B.ι), P.loc 0 1 s i j = s * (P.r' j : X.functionField) := by
    intro i j; simp [Pair.loc]
  have hloc : ∀ x : X, ∃ (V : X.Opens) (j : P.A.B.ι) (_ : IsAffineOpen V) (hx : x ∈ V) (a : Γ(X, V)),
      V ≤ P.A.B.U j ∧ fnOf V (gen_mem hx) a = s * (P.r' j : X.functionField) := by
    intro x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (P.L.isLB.cover ▸ Opens.mem_top x : x ∈ ⨆ i, P.L.B.U i)
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (P.A.isLB.cover ▸ Opens.mem_top x : x ∈ ⨆ j, P.A.B.U j)
    obtain ⟨c, hc⟩ := hs x i j hi hj
    obtain ⟨U, hxU, f, rfl⟩ := TopCat.Presheaf.germ_exist X.presheaf c
    obtain ⟨V, hV, hxV, hVW⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show x ∈ U ⊓ P.A.B.U j from ⟨hxU, hj⟩)
    refine ⟨V, j, hV, hxV, resG X (hVW.trans inf_le_left) f, hVW.trans inf_le_right, ?_⟩
    rw [fnOf_resG, ← algebraMap_germ hxU, hc, hloc0]
  choose V jj hV hxV a hVj ha using hloc
  have hne : ∀ y, fnOf (V y) (gen_mem (hxV y)) (a y) ≠ 0 := by
    intro y; rw [ha]; exact mul_ne_zero hs0 (P.r' (jj y)).ne_zero
  choose T hTfin hT using fun y => GlobalTheory.T.exists_finite_points_regular_div_affineOpen X (V y) (hV y) (gen_mem (hxV y)) (a y) (hne y)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (V y : Set X)) (fun y => (V y).isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨y, hxV y⟩)
  refine ⟨⋃ y ∈ t, T y, t.finite_toSet.biUnion fun y _ => hTfin y, ?_⟩
  intro x i j hi hj τ g hτ hS hg hgτ
  obtain ⟨y, hyt, hxy⟩ : ∃ y ∈ t, x ∈ V y := by
    have := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion] at this
    obtain ⟨y, hy, h⟩ := this
    exact ⟨y, hy, h⟩
  have hxj' : x ∈ P.A.B.U j ⊓ P.A.B.U (jj y) := ⟨hj, hVj y hxy⟩
  set w : X.functionField := fnOf _ (gen_mem hxj') (P.A.B.g j (jj y) : Γ(X, P.A.B.U j ⊓ P.A.B.U (jj y))) with hw
  have hwu : UnitAt x w := unitAt_fnOf hxj' _ _
  have hw0 : w ≠ 0 := hwu.ne_zero
  have hrel : P.loc 0 1 s i j = fnOf (V y) (gen_mem (hxV y)) (a y) * w := by
    rw [hloc0, ha, P.hr' j (jj y) (gen_mem hxj')]; ring
  rw [hrel] at hgτ ⊢
  set σ := fnOf (V y) (gen_mem (hxV y)) (a y)
  have h1 : RegAt x (g * τ / σ) := by
    have := hgτ.mul hwu.regAt
    convert this using 1
    field_simp
  have h2 := hT y x hxy τ g hτ (fun z hz hzx => hS z (Set.mem_biUnion hyt hz) hzx) hg h1
  have := h2.mul hwu.inv.regAt
  convert this using 1
  rw [div_mul_eq_div_div, div_eq_mul_inv (g / σ)]

end GlobalTheory.VolBr
end
