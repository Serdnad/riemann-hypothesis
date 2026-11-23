module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle727
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle306
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle309
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.SplitTransfer

section Abstract

open Formalism.UG GlobalTheory.PRep

theorem heckeVec_indicator {G V ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {K : Subgroup G} {x : V} (hx : x ∈ fixed ρ K) {S : Set G} (hm : ∀ g ∈ S, ∀ k ∈ K, g * k ∈ S) (R : Finset ι)
    (g : ι → G) (hR : ∀ i ∈ R, g i ∈ S) (hR' : ∀ y ∈ S, ∃! i, i ∈ R ∧ (g i)⁻¹ * y ∈ K) :
    GlobalTheory.LFun.heckeVec ρ K (Set.indicator S 1) x = ∑ i ∈ R, ρ (g i) x := by
  classical
  have hinj : Set.InjOn (fun i : ι => (g i : G ⧸ K)) R := fun γ hγ δ hδ e =>
    (hR' _ (hR δ hδ)).unique ⟨hγ, QuotientGroup.eq.1 e⟩ ⟨hδ, by simp⟩
  rw [GlobalTheory.LFun.heckeVec, finsum_eq_sum_of_support_subset (s := R.image fun i : ι => (g i : G ⧸ K)),
    Finset.sum_image hinj]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (g γ)
    rw [hk, Set.indicator_of_mem (hm _ (hR γ hγ) k k.2), map_mul, Module.End.mul_apply,
      GlobalTheory.LGrp.mem_fixed.1 hx _ k.2]
    simp
  · intro c hc
    have : c.out ∈ S := by
      by_contra h0
      exact hc (by simp [h0])
    obtain ⟨γ, ⟨h1, h2⟩, -⟩ := hR' _ this
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨γ, h1, (QuotientGroup.eq.2 h2).trans c.out_eq'⟩)

end Abstract


open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.InertHeckeEigen Formalism.UG GlobalTheory.PRep GlobalTheory.DefU in
theorem heckeVec_eq_of_isCompAlong {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {U : Submodule ℂ (UA L n → ℂ)} (hU : IsAutRepU U) (w : HeightOneSpectrum (𝓞 L)) {H X : Type} [Group H]
    [AddCommGroup X] [Module ℂ X] {K : Subgroup H} (hK : IsCommensurated K) (p : locU n w →* H)
    (hp : Function.Surjective p) (σ : Representation ℂ H X) (hcomp : IsCompAlong U (locU n w) p σ) {h : H → ℂ}
    (hh : h ∈ Hecke ℂ K) {lam : ℂ} (hsat : ∀ v ∈ fixed σ K, v ≠ 0 → GlobalTheory.LFun.heckeVec σ K h v = lam • v)
    {φ : UA L n → ℂ} (hφ : φ ∈ U) (hfix : ∀ x : locU n w, p x ∈ K → RU L n x.val φ = φ) :
    GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) (K.comap p) (fun x => h (p x)) φ = lam • φ := by
  have hfin : {c : locU n w ⧸ K.comap p | h (p c.out) ≠ 0}.Finite :=
    finite_support_comp p hp hh.1 (Formalism.UG.P.finite_support_cosets hK hh.2)
  have hS : ∀ c : locU n w ⧸ K.comap p, (fun x => h (p x)) c.out ≠ 0 → c ∈ hfin.toFinset :=
    fun c hc => hfin.mem_toFinset.2 hc
  let T : (UA L n → ℂ) →ₗ[ℂ] (UA L n → ℂ) :=
    ∑ c ∈ hfin.toFinset, h (p c.out) • (RU L n) (c.out : UA L n)
  have hT : ∀ x, GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) (K.comap p) (fun x => h (p x)) x
      = T x := fun x => by
    rw [heckeVec_eq_sum _ _ _ _ hS x]
    simp [T, LinearMap.sum_apply]
  let Z : Submodule ℂ (UA L n → ℂ) :=
    fixed ((RU L n).comp (locU n w).subtype) (K.comap p) ⊓ LinearMap.ker (T - lam • LinearMap.id)
  have hZ' : ∀ x, x ∈ Z ↔ (∀ k ∈ K.comap p, RU L n (k : UA L n) x = x) ∧ T x = lam • x := fun x => by
    simp only [Z, Submodule.mem_inf, GlobalTheory.LGrp.mem_fixed, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  let π : AutSub L n := ⟨U, hU⟩
  obtain ⟨hσirr, f, hf0, hfm, hf⟩ := hcomp
  have hirr : Representation.IsIrreducible (σ.comp p) := by
    obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 hσirr
    refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun Y hY => h1 Y fun g v hv => ?_⟩
    obtain ⟨x, rfl⟩ := hp g
    exact hY x v hv
  let F : Representation.IntertwiningMap (σ.comp p) (π.rep.comp (locU n w).subtype) :=
    ⟨f.codRestrict _ hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h => hf0 (LinearMap.ext fun v => by
    have := congrArg Subtype.val (DFunLike.congr_fun h v)
    exact this)
  obtain ⟨r, -, -, hr⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints L n w
  have htop := (GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor (UA L n) (locU n w) π.V X X π.rep (locU n w).subtype (σ.comp p) (σ.comp p)
    π.isIrreducible_rep hirr hirr (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1
  let fi : Representation.IntertwiningMap (σ.comp p) (π.rep.comp (locU n w).subtype) → X →ₗ[ℂ] (UA L n → ℂ) :=
    fun i => U.subtype ∘ₗ i.toLinearMap
  have hfi : ∀ i g u, fi i ((σ.comp p) g u) = (RU L n).comp (locU n w).subtype g (fi i u) := fun i g u =>
    congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining (σ.comp p) (π.rep.comp (locU n w).subtype) i g u)
  have hmem : φ ∈ ⨆ i, LinearMap.range (fi i) := by
    have : φ ∈ (⨆ i : Representation.IntertwiningMap (σ.comp p) (π.rep.comp (locU n w).subtype),
        LinearMap.range i.toLinearMap).map U.subtype := by
      rw [htop]; exact ⟨⟨φ, hφ⟩, Submodule.mem_top, rfl⟩
    simp only [fi, LinearMap.range_comp]
    rwa [Submodule.map_iSup] at this
  have hZ : ∀ i v, (∀ k ∈ (K.comap p : Set (locU n w)), (σ.comp p) k v = v) → fi i v ∈ Z := by
    intro i v hv
    by_cases hv0 : v = 0
    · rw [hv0, map_zero]; exact Z.zero_mem
    have hvK : v ∈ fixed σ K := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
      obtain ⟨x, rfl⟩ := hp k
      exact hv x hk
    refine (hZ' _).2 ⟨fun k hk => (hfi i k v).symm.trans (congrArg (fi i) (hv k hk)), ?_⟩
    have e2 := heckeVec_comp_surj p hp hh.1 σ hvK
    rw [heckeVec_eq_sum _ _ _ _ hS] at e2
    rw [hsat v hvK hv0] at e2
    rw [← hT (fi i v), heckeVec_eq_sum _ _ _ _ hS]
    calc _ = fi i (∑ c ∈ hfin.toFinset, h (p c.out) • (σ.comp p) c.out v) := by

          rw [map_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [map_smul, hfi]
      _ = lam • fi i v := by rw [e2, map_smul]
  have hZK : ∀ z ∈ Z, ∀ k ∈ (K.comap p : Set (locU n w)), (RU L n).comp (locU n w).subtype k z = z :=
    fun z hz k hk => ((hZ' z).1 hz).1 k hk
  have hφZ := mem_of_mem_iSup ((RU L n).comp (locU n w).subtype) (σ.comp p) hirr fi hfi _ Z hZ hZK φ
    (fun k hk => hfix k hk) hmem
  rw [hT]
  exact ((hZ' φ).1 hφZ).2

end GlobalTheory.SplitTransfer

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitTransfer

theorem heckeVec_divInd {D : D7} [IsCMField D.host.E] {V : HSp D}
    {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {j : UA D.host.E V.rank ≃ₜ* GA D V} {h₀ : GA D V} (hT : IsTransfer V θ j h₀)
    {P : HeightOneSpectrum (𝓞 D.host.E)} {φ : UA D.host.E V.rank → ℂ}
    (hφ : ∀ x ∈ KP V.rank P, RU D.host.E V.rank x φ = φ) {d : List ℤ} {R : Finset (GA D V)}
    (hR : GlobalTheory.Hk3.SphOp V P d R) :
    GlobalTheory.LFun.heckeVec ((RU D.host.E V.rank).comp (locU V.rank P).subtype)
      ((GlobalTheory.LFun.KGL P (n := V.rank)).comap ((cLoc P).comp (locU V.rank P).subtype))
      (fun x => divInd (Ov D.host.E P) d (((cLoc P).comp (locU V.rank P).subtype) x)) φ =
      ∑ γ ∈ R, RU D.host.E V.rank ((cj j h₀).symm γ) φ := by
  classical
  obtain ⟨h1, h2⟩ := hT.2.2.2.2.2.2.2 P d R hR
  let g : GA D V → locU V.rank P := fun γ =>
    if h : (cj j h₀).symm γ ∈ locU V.rank P then ⟨_, h⟩ else 1
  have hg : ∀ γ ∈ R, (g γ : UA D.host.E V.rank) = (cj j h₀).symm γ := fun γ hγ => by
    simp only [g, dif_pos (h1 γ hγ).1]
  have e : (fun x : locU V.rank P => divInd (Ov D.host.E P) d (((cLoc P).comp (locU V.rank P).subtype) x)) =
      Set.indicator {x : locU V.rank P | HasDiv (Ov D.host.E P) d (cLoc P x.val)} 1 := by
    funext x
    by_cases hx : HasDiv (Ov D.host.E P) d (cLoc P x.val)
    · rw [Set.indicator_of_mem (s := {x : locU V.rank P | HasDiv (Ov D.host.E P) d (cLoc P x.val)}) hx]
      exact Set.indicator_of_mem (s := {g | HasDiv (Ov D.host.E P) d g}) hx _
    · rw [Set.indicator_of_notMem (s := {x : locU V.rank P | HasDiv (Ov D.host.E P) d (cLoc P x.val)}) hx]
      exact Set.indicator_of_notMem (s := {g | HasDiv (Ov D.host.E P) d g}) hx _
  rw [e, heckeVec_indicator (GlobalTheory.LGrp.mem_fixed.2 fun k hk => hφ k.val ⟨k.2, hk⟩) ?_ R g ?_ ?_]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    rw [← hg γ hγ]
    rfl
  · intro x hx k hk
    have := GlobalTheory.SphGal.hasDiv_mul_mul hx (one_mem _) hk
    rw [one_mul] at this
    change HasDiv _ d (cLoc P (x.val * k.val))
    rw [map_mul]
    exact this
  · intro γ hγ
    change HasDiv _ d (cLoc P (g γ).val)
    rw [hg γ hγ]
    exact (h1 γ hγ).2
  · intro y hy
    obtain ⟨γ, ⟨a1, a2⟩, a3⟩ := h2 y.val y.2 hy
    refine ⟨γ, ⟨a1, ?_⟩, fun δ hδ => a3 δ ⟨hδ.1, ?_⟩⟩
    · change cLoc P ((g γ).val⁻¹ * y.val) ∈ GlobalTheory.LFun.KGL P (n := V.rank)
      rw [hg γ a1]
      exact a2.2
    · rw [← hg δ hδ.1]
      exact ⟨((g δ)⁻¹ * y).2, hδ.2⟩

end GlobalTheory.SplitTransfer

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilAdm

open Topology Filter

theorem pureA_fixed_fin :
    ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), Continuous ψ →
    ∀ (κ : Type) [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) →
      ∃ M : AddSubgroup ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (M : Set ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F))) ∧
        ∀ m ∈ M, ∀ f : (κ → mixedEmbedding.mixedSpace F) → ℂ,
          GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilAdm.finE2 F m) (GlobalTheory.WeilM.pureA F f g) = GlobalTheory.WeilM.pureA F f g := by
  intro F _ _ ψ hψ κ _ g hg
  haveI := GlobalTheory.HeisSchA.nonarch_finiteAdeleRing (F := F)
  haveI : NonarchimedeanAddGroup (κ → FiniteAdeleRing (𝓞 F) F) := GlobalTheory.HeisSchA.nonarch_pi
  let χ := GlobalTheory.HeisSchA.finChar ψ
  have hL : IsOpen {a | χ a = 1} := (GlobalTheory.HeisSchA.finChar_isLocallyConstant ψ hψ).isOpen_fiber 1
  let c : FiniteAdeleRing (𝓞 F) F := (⅟(2 : AdeleRing (𝓞 F) F)).2

  obtain ⟨V0, hV0⟩ : ∃ V0 : OpenAddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
      ∀ u ∈ V0, ∀ v ∈ V0, χ (c * (u ⬝ᵥ v)) = 1 := by
    have hcont : Continuous fun p : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) =>
        c * (p.1 ⬝ᵥ p.2) :=
      continuous_const.mul (continuous_fst.dotProduct continuous_snd)
    have h0 : ∀ᶠ p : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) in 𝓝 0 ×ˢ 𝓝 0,
        χ (c * (p.1 ⬝ᵥ p.2)) = 1 := by
      rw [← nhds_prod_eq]
      refine hcont.continuousAt.preimage_mem_nhds (hL.mem_nhds ?_)
      simp [χ]
    obtain ⟨s, hs, hss⟩ := (Filter.eventually_prod_self_iff (r := fun a b => χ (c * (a ⬝ᵥ b)) = 1)).mp h0
    obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean s hs
    exact ⟨V, fun u hu v hv => hss u (hV hu) v (hV hv)⟩

  have hloc : ∀ y : κ → FiniteAdeleRing (𝓞 F) F, ∃ V : OpenAddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
      ∀ a ∈ V, ∀ u ∈ V, g (y + a + u) = g y ∧ χ ((y + a) ⬝ᵥ u) = 1 := by
    intro y
    have c1 : Continuous fun p : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) =>
        y + p.1 + p.2 := (continuous_const.add continuous_fst).add continuous_snd
    have c2 : Continuous fun p : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) =>
        (y + p.1) ⬝ᵥ p.2 := (continuous_const.add continuous_fst).dotProduct continuous_snd
    have h0 : ∀ᶠ p : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) in 𝓝 0 ×ˢ 𝓝 0,
        g (y + p.1 + p.2) = g y ∧ χ ((y + p.1) ⬝ᵥ p.2) = 1 := by
      rw [← nhds_prod_eq]
      refine Filter.Eventually.and (c1.continuousAt.preimage_mem_nhds ((hg.1.isOpen_fiber (g y)).mem_nhds ?_))
        (c2.continuousAt.preimage_mem_nhds (hL.mem_nhds ?_))
      · simp
      · simp [χ]
    obtain ⟨s, hs, hss⟩ := (Filter.eventually_prod_self_iff
      (r := fun a u => g (y + a + u) = g y ∧ χ ((y + a) ⬝ᵥ u) = 1)).mp h0
    obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean s hs
    exact ⟨V, fun a ha u hu => hss a (hV ha) u (hV hu)⟩
  choose V hV using hloc
  obtain ⟨t, -, htK⟩ := (hg.2 : IsCompact (tsupport g)).elim_nhds_subcover
    (fun y => {z | z - y ∈ (V y : Set (κ → FiniteAdeleRing (𝓞 F) F))}) (fun y _ => by
      refine (continuous_sub_right y).continuousAt.preimage_mem_nhds ?_
      rw [sub_self]
      exact (V y).isOpen.mem_nhds (V y).zero_mem)
  let M0 : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) :=
    (V0 : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)) ⊓ ⨅ y ∈ t, (V y : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F))
  have hM0 : ∀ u ∈ M0, u ∈ V0 ∧ ∀ y ∈ t, u ∈ V y := fun u hu => by
    simp only [M0, AddSubgroup.mem_inf, AddSubgroup.mem_iInf] at hu
    exact ⟨hu.1, hu.2⟩
  have hM0open : IsOpen (M0 : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by
    refine M0.isOpen_of_mem_nhds (g := 0) ?_
    refine Filter.mem_of_superset (Filter.inter_mem (V0.isOpen.mem_nhds V0.zero_mem)
      ((Filter.biInter_finset_mem t).2 fun y _ => (V y).isOpen.mem_nhds (V y).zero_mem)) ?_
    intro u hu
    simp only [Set.mem_inter_iff, Set.mem_iInter] at hu
    simp only [M0, SetLike.mem_coe, AddSubgroup.mem_inf, AddSubgroup.mem_iInf]
    exact ⟨hu.1, hu.2⟩
  have hcov : ∀ y ∈ tsupport g, ∀ u ∈ M0, g (y + u) = g y ∧ ∀ v ∈ M0, χ (y ⬝ᵥ v) = 1 := by
    intro y hy u hu
    obtain ⟨z, hz, hyz⟩ : ∃ z ∈ t, y - z ∈ V z := by simpa using htK hy
    have e : z + (y - z) = y := by abel
    have h1 := hV z (y - z) hyz u ((hM0 u hu).2 z hz)
    have h2 := hV z (y - z) hyz 0 (V z).zero_mem
    rw [e] at h1 h2
    rw [add_zero] at h2
    refine ⟨h1.1.trans h2.1.symm, fun v hv => ?_⟩
    have h3 := hV z (y - z) hyz v ((hM0 v hv).2 z hz)
    rw [e] at h3
    exact h3.2
  have hinv : ∀ u ∈ M0, ∀ y, g (y + u) = g y := by
    intro u hu y
    by_cases hy : y ∈ tsupport g
    · exact (hcov y hy u hu).1
    by_cases hy' : y + u ∈ tsupport g
    · have := (hcov (y + u) hy' (-u) (M0.neg_mem hu)).1
      rw [add_neg_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hy']
  refine ⟨M0.prod M0, by rw [AddSubgroup.coe_prod]; exact hM0open.prod hM0open, ?_⟩
  rintro ⟨u, v⟩ hm f
  rw [AddSubgroup.mem_prod] at hm
  obtain ⟨hu, hv⟩ := hm
  funext x
  simp only [GlobalTheory.WeilM.schr, GlobalTheory.WeilM.pureA, finE2]
  have harg : x ⬝ᵥ finE F v + ⅟(2 : AdeleRing (𝓞 F) F) * (finE F u ⬝ᵥ finE F v) =
      ((0 : InfiniteAdeleRing F), (fun i => (x i).2) ⬝ᵥ v + c * (u ⬝ᵥ v)) := by
    have hp1 : ∀ (w : κ → FiniteAdeleRing (𝓞 F) F) (i : κ), GlobalTheory.HeisSchA.p1 (finE F w i) = 0 := fun _ _ => rfl
    have hp2 : ∀ (w : κ → FiniteAdeleRing (𝓞 F) F) (i : κ), GlobalTheory.HeisSchA.p2 (finE F w i) = w i := fun _ _ => rfl
    refine Prod.ext ?_ ?_
    · change GlobalTheory.HeisSchA.p1 (x ⬝ᵥ finE F v + ⅟(2 : AdeleRing (𝓞 F) F) * (finE F u ⬝ᵥ finE F v)) = 0

      simp only [map_add (f := _), map_mul, dotProduct, map_sum, hp1, mul_zero, Finset.sum_const_zero, add_zero]
    · change GlobalTheory.HeisSchA.p2 (x ⬝ᵥ finE F v + ⅟(2 : AdeleRing (𝓞 F) F) * (finE F u ⬝ᵥ finE F v)) = _

      simp only [map_add (f := _), map_mul, dotProduct, map_sum, hp2]
      rfl
  have hf : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + finE F u) i).1) =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 := by
    funext i
    rw [show ((x + finE F u) i).1 = (x i).1 from add_zero (x i).1]
  have hgx : (fun i => ((x + finE F u) i).2) = (fun i => (x i).2) + u := by
    funext i
    rfl
  rw [harg, hf, hgx, hinv u hu]
  by_cases h0 : g (fun i => (x i).2) = 0
  · rw [h0]
    ring
  · have hy : (fun i => (x i).2) ∈ tsupport g := subset_tsupport g h0
    have e1 := (hcov _ hy u hu).2 v hv
    have e2 := hV0 u (hM0 u hu).1 v (hM0 v hv).1
    have : ψ ((0 : InfiniteAdeleRing F), (fun i => (x i).2) ⬝ᵥ v + c * (u ⬝ᵥ v)) = 1 := by
      change χ ((fun i => (x i).2) ⬝ᵥ v + c * (u ⬝ᵥ v)) = 1
      rw [AddChar.map_add_eq_mul, e1, e2, one_mul]
    rw [this, one_mul]

end GlobalTheory.WeilAdm
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN
open scoped Matrix

namespace GlobalTheory.AdelicSvNQuad

open GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic
open scoped Classical

def quad {R κ : Type} [CommRing R] [Fintype κ] (h : R) (A : Matrix κ κ R) (x : κ → R) : R := h * (x ⬝ᵥ (A *ᵥ x))

theorem map_quad {R S κ : Type} [CommRing R] [CommRing S] [Fintype κ] (q : R →+* S) (h : R) (A : Matrix κ κ R)
    (x : κ → R) : q (quad h A x) = quad (q h) (A.map q) (fun i => q (x i)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [quad, dotProduct, Matrix.mulVec, map_sum]

theorem quad_neg {R κ : Type} [CommRing R] [Fintype κ] (h : R) (A : Matrix κ κ R) (x : κ → R) :
    quad h (-A) x = -quad h A x := by
  simp [quad, Matrix.neg_mulVec]

theorem continuous_quad {R κ : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [Fintype κ] (h : R)
    (A : Matrix κ κ R) : Continuous (quad h A) :=
  continuous_const.mul (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id))

theorem quad_add {R κ : Type} [CommRing R] [Invertible (2 : R)] [Fintype κ] (A : Matrix κ κ R) (hA : Aᵀ = A)
    (x u v : κ → R) : quad (⅟2) A x + (x ⬝ᵥ v + ⅟(2 : R) * (u ⬝ᵥ v)) =
      (x ⬝ᵥ (-(A *ᵥ u) + v) + ⅟(2 : R) * (u ⬝ᵥ (-(A *ᵥ u) + v))) + quad (⅟2) A (x + u) := by
  have hs : u ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (A *ᵥ u) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA, dotProduct_comm]
  have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self _
  simp only [quad, Matrix.mulVec_add, dotProduct_add, add_dotProduct, dotProduct_neg, hs]
  linear_combination (-(x ⬝ᵥ (A *ᵥ u))) * h2

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def archMul (h : mixedEmbedding.mixedSpace F) (A : Matrix κ κ (mixedEmbedding.mixedSpace F))
    (y : κ → mixedEmbedding.mixedSpace F) : ℂ :=
  eChar (-Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (quad h A y))

theorem archMul_temperate (h : mixedEmbedding.mixedSpace F) (A : Matrix κ κ (mixedEmbedding.mixedSpace F)) :
    Function.HasTemperateGrowth (archMul h A) := by
  have hp : ∀ i : κ, Function.HasTemperateGrowth fun y : κ → mixedEmbedding.mixedSpace F => y i := fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => mixedEmbedding.mixedSpace F) i).hasTemperateGrowth
  have hq : Function.HasTemperateGrowth (quad h A) := by
    have e : quad h A = fun y => h * ∑ i, y i * ∑ j, A i j * y j := rfl
    rw [e]
    refine (Function.HasTemperateGrowth.const h).mul (Function.HasTemperateGrowth.sum fun i _ => (hp i).mul ?_)
    exact Function.HasTemperateGrowth.sum fun j _ => (Function.HasTemperateGrowth.const _).mul (hp j)
  let L : mixedEmbedding.mixedSpace F →L[ℝ] ℝ :=
    -LinearMap.toContinuousLinearMap (Algebra.trace ℝ (mixedEmbedding.mixedSpace F))
  exact hasTemperateGrowth_eChar.comp (L.hasTemperateGrowth.comp hq)

def mulQ (ψ : AddChar (AF F) ℂ) (h : AF F) (A : Matrix κ κ (AF F)) :
    ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun φ x := ψ (quad h A x) * φ x
  map_add' φ φ' := funext fun x => mul_add _ _ _
  map_smul' a φ := funext fun x => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem mulQ_apply (ψ : AddChar (AF F) ℂ) (h : AF F) (A : Matrix κ κ (AF F)) (φ : (κ → AF F) → ℂ) (x : κ → AF F) :
    mulQ ψ h A φ x = ψ (quad h A x) * φ x := rfl

theorem mulQ_pureA (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (h : AF F) (A : Matrix κ κ (AF F))
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ g' ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∃ M : SInf F κ →L[ℂ] SInf F κ,
      ∀ f : SInf F κ, mulQ ψ h A (pureA F f g) = pureA F (M f) g' := by
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let q : AdeleRing (𝓞 F) F →+* mixedEmbedding.mixedSpace F := e.toRingHom.comp p1
  refine ⟨fun z => finChar ψ (quad (p2 h) (A.map p2) z) * g z,
    ⟨((finChar_isLocallyConstant ψ hψ.1).comp_continuous (continuous_quad _ _)).mul hg.1, hg.2.mul_left⟩,
    SchwartzMap.smulLeftCLM ℂ (archMul (q h) (A.map q)), fun f => funext fun x => ?_⟩
  let y : κ → mixedEmbedding.mixedSpace F := fun i => q (x i)
  let z : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (x i)
  have h3 : ψ (quad h A x) = archMul (q h) (A.map q) y * finChar ψ (quad (p2 h) (A.map p2) z) := by
    rw [map_eq_mul ψ, hψ.2.2 _ (at_mk _)]
    congr 1
    · have e1 : evI F (mk (p1 (quad h A x)) 0) = quad (q h) (A.map q) y := map_quad q h A x
      rw [e1, archMul, eChar_apply]
      congr 1
      push_cast
      ring
    · exact congrArg _ (map_quad p2 h A x)
  change ψ (quad h A x) * (f y * g z) =
    SchwartzMap.smulLeftCLM ℂ (archMul (q h) (A.map q)) f y * (finChar ψ (quad (p2 h) (A.map p2) z) * g z)
  rw [h3, SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _), smul_eq_mul]
  ring

theorem mulQ_mem (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (h : AF F) (A : Matrix κ κ (AF F)) :
    ∀ φ ∈ schA F κ, mulQ ψ h A φ ∈ schA F κ := by
  have hle : schA F κ ≤ (schA F κ).comap (mulQ ψ h A) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, g, hg, rfl⟩
    obtain ⟨g', hg', M, hM⟩ := mulQ_pureA ψ hψ h A hg
    exact Submodule.subset_span ⟨M f, g', hg', hM f⟩
  exact fun φ hφ => hle hφ

theorem act_unip {K R ι : Type} [Field K] [CommRing R] [Algebra K R] [Fintype ι] [DecidableEq ι] (C : Matrix ι ι K)
    (w : (ι → R) × (ι → R)) :
    AdelicSvN.act (Matrix.fromBlocks 1 0 (-C) 1) w = (w.1, -(C.map (algebraMap K R) *ᵥ w.1) + w.2) := by
  have h1 : (1 : Matrix ι ι K).map (algebraMap K R) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h0 : (0 : Matrix ι ι K).map (algebraMap K R) = 0 := Matrix.map_zero _ (map_zero _)
  have hn : (-C).map (algebraMap K R) = -C.map (algebraMap K R) := Matrix.map_neg _ (map_neg _) _
  simp only [AdelicSvN.act, Matrix.fromBlocks_map, h1, h0, hn, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, Matrix.neg_mulVec]

theorem realised_unip : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [DecidableEq κ] (C : Matrix κ κ F), Cᵀ = C → Realised ψ (Matrix.fromBlocks 1 0 (-C) 1) := by
  intro F _ _ ψ hψ κ _ _ C hC
  let A : Matrix κ κ (AF F) := C.map (algebraMap F (AF F))
  have hA : Aᵀ = A := by rw [← Matrix.transpose_map, hC]
  refine ⟨mulQ ψ (⅟2) A, mulQ_mem ψ hψ _ A, fun φ hφ => ⟨mulQ ψ (⅟2) (-A) φ, mulQ_mem ψ hψ _ _ φ hφ, ?_⟩,
    fun l hl => ⟨l ∘ₗ mulQ ψ (⅟2) A, fun g hg => ?_, fun _ _ => rfl⟩, fun w φ _ => funext fun x => ?_⟩
  · funext x
    rw [mulQ_apply, mulQ_apply, ← mul_assoc, ← AddChar.map_add_eq_mul, quad_neg, add_neg_cancel,
      AddChar.map_zero_eq_one, one_mul]
  · obtain ⟨g', hg', M, hM⟩ := mulQ_pureA ψ hψ (⅟2) A hg
    obtain ⟨T, hT⟩ := hl g' hg'
    exact ⟨T.comp M, fun f => (congrArg l (hM f)).trans (hT (M f))⟩
  · rw [act_unip, mulQ_apply]
    simp only [schr]
    rw [mulQ_apply, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, quad_add A hA]

end GlobalTheory.AdelicSvNQuad

end
end
