module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle525
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle259
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle526
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle383
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle137
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.KTypeProj

theorem typeSpan_proj_mem {M ι : Type} [AddCommGroup M] [Module ℂ M] (b : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (G : Submodule ℂ M)
    (ρ : ι → M →ₗ[ℂ] M) (inv : ι → ι) (hpos : ∀ x ∈ G, x ≠ 0 → 0 < (b x x).re)
    (hherm : ∀ x ∈ G, ∀ y ∈ G, star (b x y) = b y x)
    (_hρG : ∀ i, ∀ x ∈ G, ρ i x ∈ G) (hadj : ∀ i, ∀ x ∈ G, ∀ y ∈ G, b (ρ i x) y = b x (ρ (inv i) y))
    (hproj : ∀ F : Submodule ℂ M, F ≤ G → FiniteDimensional ℂ F →
      ∃ π : M →ₗ[ℂ] M, (∀ x, π x ∈ F) ∧ ∀ x, ∀ f ∈ F, b (π x) f = b x f)
    (Y₀ : Submodule ℂ M) (e : M →ₗ[ℂ] M) (he : ∀ x, e x ∈ typeSpan ρ Y₀ G)
    (he' : ∀ x, ∀ f ∈ typeSpan ρ Y₀ G, b (e x) f = b x f)
    (Y : Submodule ℂ M) (hYf : FiniteDimensional ℂ Y) (hYG : Y ≤ G) (hYρ : ∀ i, ∀ y ∈ Y, ρ i y ∈ Y) :
    ∀ x ∈ Y, e x ∈ Y := by
  intro x hx
  have hzero : ∀ d ∈ G, b d d = 0 → d = 0 := by
    intro d hd h
    by_contra hne
    have := hpos d hd hne
    rw [h] at this
    simp at this
  obtain ⟨π, hπY, hπ⟩ := hproj Y hYG hYf
  have hcomm : ∀ i, ∀ z ∈ G, π (ρ i z) = ρ i (π z) := by
    intro i z hz
    have hdY : π (ρ i z) - ρ i (π z) ∈ Y := Y.sub_mem (hπY _) (hYρ i _ (hπY z))
    have hpair : ∀ y ∈ Y, b (π (ρ i z) - ρ i (π z)) y = 0 := by
      intro y hy
      have h1 : b (π (ρ i z)) y = b (ρ i z) y := hπ _ y hy
      have h2 : b (ρ i z) y = b z (ρ (inv i) y) := hadj i z hz y (hYG hy)
      have h3 : b z (ρ (inv i) y) = b (π z) (ρ (inv i) y) := (hπ z _ (hYρ (inv i) y hy)).symm
      have h4 : b (ρ i (π z)) y = b (π z) (ρ (inv i) y) := hadj i (π z) (hYG (hπY z)) y (hYG hy)
      rw [map_sub, LinearMap.sub_apply, h1, h2, h3, h4, sub_self]
    exact sub_eq_zero.mp (hzero _ (hYG hdY) (hpair _ hdY))
  have hSG : typeSpan ρ Y₀ G ≤ G := typeSpan_le ρ Y₀ G
  have hY1f : FiniteDimensional ℂ (typeSpan ρ Y₀ G ⊓ Y : Submodule ℂ M) :=
    Submodule.finiteDimensional_of_le inf_le_right
  obtain ⟨π₁, hπ₁Y, hπ₁⟩ := hproj (typeSpan ρ Y₀ G ⊓ Y) (inf_le_left.trans hSG) hY1f
  have hpS : π₁ x ∈ typeSpan ρ Y₀ G := (hπ₁Y x).1
  have hpY : π₁ x ∈ Y := (hπ₁Y x).2
  have hxp : x - π₁ x ∈ Y := Y.sub_mem hx hpY
  have hle : typeSpan ρ Y₀ G ≤ LinearMap.ker (b (x - π₁ x)) := by
    refine iSup₂_le fun T hT => ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [LinearMap.mem_ker]
    have hTw : T w ∈ G := hT.1 ⟨w, hw, rfl⟩
    have hπT : π (T w) ∈ typeSpan ρ Y₀ G ⊓ Y := by
      refine ⟨?_, hπY _⟩
      have hm := map_le_typeSpan ρ (Y₀ := Y₀) (G := G) (π ∘ₗ T) ?_ ?_
      · exact hm ⟨w, hw, rfl⟩
      · rintro _ ⟨v, -, rfl⟩; exact hYG (hπY _)
      · intro i v hv
        simp only [LinearMap.comp_apply]
        rw [hT.2 i v hv, hcomm i _ (hT.1 ⟨v, hv, rfl⟩)]
    have e1 : b (x - π₁ x) (π (T w)) = 0 := by
      rw [map_sub, LinearMap.sub_apply, hπ₁ x _ hπT, sub_self]
    have e2 : b (T w - π (T w)) (x - π₁ x) = 0 := by
      rw [map_sub b (T w) (π (T w)), LinearMap.sub_apply, hπ (T w) _ hxp, sub_self]
    have e3 : b (x - π₁ x) (T w - π (T w)) = 0 := by
      rw [← hherm _ (G.sub_mem hTw (hYG (hπY _))) _ (hYG hxp), e2, star_zero]
    have hsplit : T w = π (T w) + (T w - π (T w)) := by abel
    rw [hsplit, map_add (f := _), e1, e3, add_zero]
  have hd : e x - π₁ x ∈ typeSpan ρ Y₀ G := Submodule.sub_mem _ (he x) hpS
  have hdd : b (e x - π₁ x) (e x - π₁ x) = 0 := by
    have h1 := he' x _ hd
    have h2 := LinearMap.mem_ker.mp (hle hd)
    rw [map_sub b x (π₁ x), LinearMap.sub_apply] at h2
    rw [map_sub b (e x) (π₁ x), LinearMap.sub_apply]
    rw [h1, sub_eq_zero.mp h2, sub_self]
  have h0 := hzero _ (hSG hd) hdd
  rw [sub_eq_zero.mp h0]
  exact hpY

end GlobalTheory.KTypeProj

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory.KTypeGelf

theorem gelf_mem_typeSpan : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ → ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ →
    ∀ (Y₀ : Submodule ℂ (GA D V → ℂ)) (τ : D.what₂.Tau) (k : ℕ),
    ∀ f ∈ GlobalTheory.KTypeProj.typeSpan (GlobalTheory.KTypeProj.rhoK θ M) Y₀ (GlobalTheory.CuspGK.gkGen θ M ψ),
      gelf θ V τ k f ∈ GlobalTheory.KTypeProj.typeSpan (GlobalTheory.KTypeProj.rhoK θ M) Y₀ (GlobalTheory.CuspGK.gkGen θ M ψ) := by
  intro D θ V S M hθ ψ hψ Y₀ τ k
  set G := GlobalTheory.CuspGK.gkGen θ M ψ with hGdef
  set ρ := GlobalTheory.KTypeProj.rhoK θ M with hρ
  have hGsm : ∀ f ∈ G, f ∈ GlobalTheory.Mem.AutSpace.SmFun θ V := fun f hf =>
    fun k τs Xs h g => (GlobalTheory.KTypeAdm.isAutFunSm_of_mem_gkGen θ M hθ hψ f hf).smooth k τs Xs h g
  have hL := GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) τ k

  let g0 : GlobalTheory.Mem.AutSpace.SmFun θ V →ₗ[ℂ] (GA D V → ℂ) :=
    { toFun := fun φ => gelf θ V τ k φ
      map_add' := fun φ ψ' => hL.add _ φ.2 _ ψ'.2
      map_smul' := fun c φ => hL.smul c φ }
  obtain ⟨L, hLe⟩ := LinearMap.exists_extend g0
  have hLa : ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, L φ = gelf θ V τ k φ := fun φ hφ => by
    have := congrArg (fun F => F ⟨φ, hφ⟩) hLe
    simpa [g0] using this
  have hgel0 : gelf θ V τ k 0 = 0 := by
    have := hL.smul 0 0
    simpa using this
  let Q : Submodule ℂ (GA D V → ℂ) :=
    { carrier := {f | f ∈ G ∧ gelf θ V τ k f ∈ GlobalTheory.KTypeProj.typeSpan ρ Y₀ G}
      add_mem' := fun {a b} ha hb => by
        refine ⟨G.add_mem ha.1 hb.1, ?_⟩
        rw [hL.add a (hGsm a ha.1) b (hGsm b hb.1)]
        exact Submodule.add_mem _ ha.2 hb.2
      zero_mem' := ⟨G.zero_mem, by rw [hgel0]; exact Submodule.zero_mem _⟩
      smul_mem' := fun c f hf => by
        refine ⟨G.smul_mem c hf.1, ?_⟩
        rw [hL.smul c f]
        exact Submodule.smul_mem _ c hf.2 }
  have hle : GlobalTheory.KTypeProj.typeSpan ρ Y₀ G ≤ Q := by
    refine iSup₂_le fun T hT => ?_
    rintro _ ⟨w, hw, rfl⟩
    have hTw : T w ∈ G := hT.1 ⟨w, hw, rfl⟩
    refine ⟨hTw, ?_⟩
    have hmap : Y₀.map (L ∘ₗ T) ≤ G := by
      rintro _ ⟨v, hv, rfl⟩
      have hTv : T v ∈ G := hT.1 ⟨v, hv, rfl⟩
      show L (T v) ∈ G
      rw [hLa _ (hGsm _ hTv)]
      exact GlobalTheory.KTypeAdm.gelf_mem_of_isGKSub θ M (GlobalTheory.CuspGK.isGKSub_gkGen θ M ψ) τ k _ hTv
    have hcomm : ∀ i, ∀ v ∈ Y₀, (L ∘ₗ T) (ρ i v) = ρ i ((L ∘ₗ T) v) := by
      intro i v hv
      have hTv : T v ∈ G := hT.1 ⟨v, hv, rfl⟩
      have hs := hGsm _ hTv
      simp only [LinearMap.comp_apply]
      rw [hT.2 i v hv, hLa _ (hs), hρ, GlobalTheory.KTypeProj.rhoK, GlobalTheory.KTypeProj.rTrL_apply, GlobalTheory.KTypeProj.rTrL_apply,
        hLa _ (GlobalTheory.RegSch.CentreRight.rTr_mem_all hθ _ hs), GlobalTheory.RegSch.CentreRight.gelf_rTr_all hθ _ τ k hs]
    have := GlobalTheory.KTypeProj.map_le_typeSpan ρ (L ∘ₗ T) hmap hcomm ⟨w, hw, rfl⟩
    simpa [hLa _ (hGsm _ hTw)] using this
  intro f hf
  exact (hle hf).2

end GlobalTheory.KTypeGelf
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.GKGenKFin

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

def kGrp : Subgroup (GA D V) :=
  Subgroup.closure {k | ∃ τ g, GlobalTheory.CuspGK.InK M τ g ∧ k = atTau θ V τ g}

theorem kGrp_le : kGrp θ M ≤ GinfC V :=
  (Subgroup.closure_le _).2 fun _ ⟨τ, g, _, e⟩ => e ▸ GlobalTheory.FinTranslate.atTau_mem θ V τ g

theorem rTr_mul (x y : GA D V) (f : GA D V → ℂ) : rTr V (x * y) f = rTr V x (rTr V y f) := by
  funext g
  simp only [rTr, mul_assoc]

theorem rTr_inv_rTr (x : GA D V) (f : GA D V → ℂ) : rTr V x⁻¹ (rTr V x f) = f := by
  funext g
  simp only [rTr, inv_mul_cancel_right]

theorem rTr_mem_of_kStable {W : Submodule ℂ (GA D V → ℂ)} (hW : FiniteDimensional ℂ W)
    (hK : GlobalTheory.KTypeProj.KStable θ M W) {k : GA D V} (hk : k ∈ kGrp θ M) : ∀ f ∈ W, rTr V k f ∈ W := by
  refine Subgroup.closure_induction (p := fun k _ => ∀ f ∈ W, rTr V k f ∈ W) (fun x hx => ?_) ?_
    (fun x y _ _ hx hy => ?_) (fun x _ hx => ?_) hk
  · obtain ⟨τ, g, hg, rfl⟩ := hx
    exact hK τ g hg
  · intro f hf
    have e : rTr V 1 f = f := funext fun g => by simp [rTr]
    rw [e]
    exact hf
  · intro f hf
    rw [rTr_mul]
    exact hx _ (hy f hf)
  · let T : W →ₗ[ℂ] W := ((GlobalTheory.KTypeProj.rTrL x).restrict (p := W) (q := W) fun f hf => hx f hf)
    have hinj : Function.Injective T := by
      intro a b hab
      apply Subtype.ext
      have h1 : rTr V x a.1 = rTr V x b.1 := congrArg Subtype.val hab
      have h2 := congrArg (rTr V x⁻¹) h1
      rwa [rTr_inv_rTr, rTr_inv_rTr] at h2
    have hsurj := LinearMap.injective_iff_surjective.1 hinj
    intro f hf
    obtain ⟨h, hh⟩ := hsurj ⟨f, hf⟩
    have e : rTr V x h.1 = f := congrArg Subtype.val hh
    rw [← e, rTr_inv_rTr]
    exact h.2

theorem isKFinite_smul {Φ : GA D V → ℂ} {K : Subgroup (GA D V)} (h : GlobalTheory.Doubling.IsKFinite K Φ) (c : ℂ) :
    GlobalTheory.Doubling.IsKFinite K (c • Φ) := by
  obtain ⟨W, hW, hm⟩ := GlobalTheory.Doubling.isKFinite_iff.1 h
  exact GlobalTheory.Doubling.isKFinite_iff.2 ⟨W, hW, fun k hk => by
    exact W.smul_mem c (hm k hk)⟩

def kfinSm (hθ : IsInfFam θ) : Submodule ℂ (GA D V → ℂ) where
  carrier := {x | IsAutFunSm θ V x ∧ GlobalTheory.Doubling.IsKFinite (kGrp θ M) x}
  zero_mem' := ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_zero θ V, .of_invariant fun _ _ _ => rfl⟩
  add_mem' := fun h h' => ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_add h.1 h'.1, h.2.add h'.2⟩
  smul_mem' := fun c _ h => ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_smul c h.1, isKFinite_smul h.2 c⟩

theorem exists_kStable {x : GA D V → ℂ} (h : GlobalTheory.Doubling.IsKFinite (kGrp θ M) x) :
    ∃ Y : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ Y ∧ x ∈ Y ∧ GlobalTheory.KTypeProj.KStable θ M Y := by
  refine ⟨GlobalTheory.Doubling.kSpan (kGrp θ M) x, h, Submodule.subset_span ⟨1, one_mem _, funext fun g => by simp⟩, ?_⟩
  intro τ g hg f hf
  have ha : atTau θ V τ g ∈ kGrp θ M := Subgroup.subset_closure ⟨τ, g, hg, rfl⟩
  have hle : GlobalTheory.Doubling.kSpan (kGrp θ M) x ≤
      (GlobalTheory.Doubling.kSpan (kGrp θ M) x).comap (GlobalTheory.KTypeProj.rTrL (atTau θ V τ g)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    refine Submodule.subset_span ⟨atTau θ V τ g * k, mul_mem ha hk, ?_⟩
    funext y
    simp only [GlobalTheory.KTypeProj.rTrL_apply, rTr, mul_assoc]
  exact hle hf

theorem isGKSub_kfinSm (hθ : IsInfFam θ) : GlobalTheory.CuspGK.IsGKSub θ M (kfinSm θ M hθ) := by
  constructor
  · intro τ g hg f hf
    exact ⟨GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau D θ hθ V f hf.1 τ g hg.1,
      hf.2.translate (Subgroup.subset_closure ⟨τ, g, hg, rfl⟩)⟩
  · intro τ X hX f hf
    exact ⟨GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX hf.1,
      GlobalTheory.CuspLie.isKFinite_Rder hθ hX (kGrp_le θ M) hf.1.smooth hf.2⟩

theorem kFinite_of_mem_gkGen : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ → ∀ ψ : GA D V → ℂ,
    IsAutFunSm θ V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ GlobalTheory.KTypeProj.KStable θ M W) →
    ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∃ Y : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ Y ∧ x ∈ Y ∧
      GlobalTheory.KTypeProj.KStable θ M Y := by
  intro D θ V S M hθ ψ hψ ⟨W, hW, hψW, hK⟩ x hx
  have hm : ψ ∈ kfinSm θ M hθ :=
    ⟨hψ, GlobalTheory.Doubling.isKFinite_iff.2 ⟨W, hW, fun k hk => rTr_mem_of_kStable θ M hW hK hk ψ hψW⟩⟩
  exact exists_kStable θ M (GlobalTheory.CuspGK.gkGen_le θ M hm (isGKSub_kfinSm θ M hθ) hx).2

end GlobalTheory.GKGenKFin

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.KTypeRep

open GlobalTheory.KTypeProj GlobalTheory.Published.AutFin

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

theorem conj_UH (τ : D.what₂.Tau) (k : Formalism.REAL.KG (M.ε τ)) :
    (M.fr τ)⁻¹ * Formalism.REAL.toMK k * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
  GlobalTheory.Published.AutFin.conj_mem_UH (M.fr_unit τ) (M.fr_gram τ) k

theorem fr_mul_inv (τ : D.what₂.Tau) : M.fr τ * (M.fr τ)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ))

theorem fr_inv_mul (τ : D.what₂.Tau) : (M.fr τ)⁻¹ * M.fr τ = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ))

theorem conj_inK (τ : D.what₂.Tau) (k : Formalism.REAL.KG (M.ε τ)) :
    GlobalTheory.CuspGK.InK M τ ((M.fr τ)⁻¹ * Formalism.REAL.toMK k * M.fr τ) := by
  refine ⟨conj_UH M τ k, ?_⟩
  have hc : M.fr τ * ((M.fr τ)⁻¹ * Formalism.REAL.toMK k * M.fr τ) * (M.fr τ)⁻¹ =
      (M.fr τ * (M.fr τ)⁻¹) * Formalism.REAL.toMK k * (M.fr τ * (M.fr τ)⁻¹) := by
    simp only [mul_assoc]
  rw [hc, fr_mul_inv M τ, one_mul, mul_one]
  exact k.2

theorem kAt_one (hθ : IsInfFam (D := D) θ) (τ : D.what₂.Tau) : kAt θ V τ (M.ε τ) (M.fr τ) 1 = 1 := by
  show atTau θ V τ ((M.fr τ)⁻¹ * Formalism.REAL.toMK (1 : Formalism.REAL.KG (M.ε τ)) * M.fr τ) = 1
  have h1 : Formalism.REAL.toMK (1 : Formalism.REAL.KG (M.ε τ)) = 1 := rfl
  rw [h1, mul_one, fr_inv_mul M τ]
  exact GlobalTheory.PointAtPlaceHom.atTau_one hθ V τ

theorem kAt_mul (hθ : IsInfFam (D := D) θ) (τ : D.what₂.Tau) (a b : Formalism.REAL.KG (M.ε τ)) :
    kAt θ V τ (M.ε τ) (M.fr τ) (a * b) = kAt θ V τ (M.ε τ) (M.fr τ) a * kAt θ V τ (M.ε τ) (M.fr τ) b := by
  show atTau θ V τ ((M.fr τ)⁻¹ * Formalism.REAL.toMK (a * b) * M.fr τ) =
    atTau θ V τ ((M.fr τ)⁻¹ * Formalism.REAL.toMK a * M.fr τ) * atTau θ V τ ((M.fr τ)⁻¹ * Formalism.REAL.toMK b * M.fr τ)
  rw [← GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ (conj_UH M τ a) (conj_UH M τ b)]
  have hab : Formalism.REAL.toMK (a * b) = Formalism.REAL.toMK a * Formalism.REAL.toMK b := rfl
  have hsplit : (M.fr τ)⁻¹ * Formalism.REAL.toMK a * M.fr τ * ((M.fr τ)⁻¹ * Formalism.REAL.toMK b * M.fr τ) =
      (M.fr τ)⁻¹ * Formalism.REAL.toMK a * (M.fr τ * (M.fr τ)⁻¹) * Formalism.REAL.toMK b * M.fr τ := by
    simp only [mul_assoc]
  rw [hsplit, fr_mul_inv M τ, mul_one, hab]
  simp only [mul_assoc]

theorem continuous_kAt (hθ : IsInfFam (D := D) θ) (τ : D.what₂.Tau) :
    Continuous fun k => kAt θ V τ (M.ε τ) (M.fr τ) k := by
  have hK : Continuous fun k : Formalism.REAL.KG (M.ε τ) => Formalism.REAL.toMK k :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hconj : Continuous fun k : Formalism.REAL.KG (M.ε τ) => (M.fr τ)⁻¹ * Formalism.REAL.toMK k * M.fr τ :=
    (continuous_const.matrix_mul hK).matrix_mul continuous_const
  exact (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ).comp_continuous hconj fun k => conj_UH M τ k

def kRep (hθ : IsInfFam (D := D) θ) (Y : Submodule ℂ (GA D V → ℂ)) (hY : KStable θ M Y) (τ : D.what₂.Tau) :
    Representation ℂ (Formalism.REAL.KG (M.ε τ)) Y where
  toFun k := (rTrL (kAt θ V τ (M.ε τ) (M.fr τ) k)).restrict fun f hf => hY τ _ (conj_inK M τ k) f hf
  map_one' := by
    refine LinearMap.ext fun w => Subtype.ext (funext fun x => ?_)
    show w.1 (x * kAt θ V τ (M.ε τ) (M.fr τ) 1) = w.1 x
    rw [kAt_one M hθ, mul_one]
  map_mul' a b := by
    refine LinearMap.ext fun w => Subtype.ext (funext fun x => ?_)
    show w.1 (x * kAt θ V τ (M.ε τ) (M.fr τ) (a * b)) =
      w.1 (x * kAt θ V τ (M.ε τ) (M.fr τ) a * kAt θ V τ (M.ε τ) (M.fr τ) b)
    rw [kAt_mul M hθ, mul_assoc]

theorem isContRep_kRep (hθ : IsInfFam (D := D) θ) (Y : Submodule ℂ (GA D V → ℂ)) [FiniteDimensional ℂ Y]
    (hY : KStable θ M Y) (hc : ∀ f ∈ Y, Continuous f) (τ : D.what₂.Tau) : IsContRep (kRep M hθ Y hY τ) := by
  intro ℓ w
  have hℓ : Continuous ℓ := LinearMap.continuous_of_finiteDimensional ℓ
  refine hℓ.comp (continuous_induced_rng.2 (continuous_pi fun x => ?_))
  show Continuous fun k => (w : GA D V → ℂ) (x * kAt θ V τ (M.ε τ) (M.fr τ) k)
  exact (hc _ w.2).comp (continuous_const.mul (continuous_kAt M hθ τ))

end GlobalTheory.KTypeRep

theorem GlobalTheory.KTypeRep.exists_contRep_types : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ Y : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ Y → GlobalTheory.KTypeProj.KStable θ M Y → (∀ f ∈ Y, Continuous f) →
    ∀ τ, ∃ ρ : Representation ℂ (Formalism.REAL.KG (M.ε τ)) Y, GlobalTheory.Published.AutFin.IsContRep ρ ∧
      ∀ T : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ),
        (∀ i, ∀ w ∈ Y, T (GlobalTheory.KTypeProj.rhoK θ M i w) = GlobalTheory.KTypeProj.rhoK θ M i (T w)) →
        ∀ w : Y, GlobalTheory.Published.AutFin.HasTypeAt θ V τ (M.ε τ) (M.fr τ) ρ (T w) := by
  intro D θ V S M hθ Y hfin hY hc τ
  haveI := hfin
  refine ⟨GlobalTheory.KTypeRep.kRep M hθ Y hY τ, GlobalTheory.KTypeRep.isContRep_kRep M hθ Y hY hc τ, ?_⟩
  intro T hT w
  refine GlobalTheory.Published.AutFin.hasTypeAt_of_map θ V τ (M.ε τ) (M.fr τ) _ (T ∘ₗ Y.subtype) (fun k u => ?_) w
  exact hT ⟨(τ, (M.fr τ)⁻¹ * Formalism.REAL.toMK k * M.fr τ), GlobalTheory.KTypeRep.conj_inK M τ k⟩ u.1 u.2

end
end
