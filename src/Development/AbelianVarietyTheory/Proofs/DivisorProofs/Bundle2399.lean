module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotOntoOfCharAlone
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle331
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1170
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle978
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle962
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2374
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle233
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1588
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2363
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumCMPreservesSchwartzHeisenber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders

namespace GlobalTheory.BadOnRec

theorem finrank_inf_range_add_inf_ker {K M : Type} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (e : M →ₗ[K] M) (he : ∀ x, e (e x) = e x) (V : Submodule K M) (hV : ∀ x ∈ V, e x ∈ V) :
    finrank K (V ⊓ LinearMap.range e : Submodule K M) + finrank K (V ⊓ LinearMap.ker e : Submodule K M) = finrank K V := by
  let f : V →ₗ[K] V := e.restrict hV
  have h1 : (LinearMap.range f).map V.subtype = V ⊓ LinearMap.range e := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨hV x x.2, x, rfl⟩
    · rintro ⟨hy, z, rfl⟩
      exact ⟨⟨e z, hy⟩, ⟨⟨e z, hy⟩, Subtype.ext (he z)⟩, rfl⟩
  have h2 : (LinearMap.ker f).map V.subtype = V ⊓ LinearMap.ker e := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, congrArg Subtype.val hx⟩
    · rintro ⟨hy, hk⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hk, rfl⟩
  rw [← h1, ← h2, Submodule.finrank_map_subtype_eq, Submodule.finrank_map_subtype_eq]
  exact LinearMap.finrank_range_add_finrank_ker f

theorem finrank_eq_of_bij {K M N : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (f : M →ₗ[K] N) (hf : Function.Bijective f) (p : Submodule K M) (q : Submodule K N) (h : ∀ x, x ∈ p ↔ f x ∈ q) :
    finrank K p = finrank K q := by
  have e : p.map f = q := by
    ext y
    obtain ⟨x, rfl⟩ := hf.2 y
    constructor
    · rintro ⟨x', hx', e'⟩
      exact hf.1 e' ▸ (h x').1 hx'
    · intro hy
      exact ⟨x, (h x).2 hy, rfl⟩
  rw [← e]
  exact (Submodule.equivMapOfInjective f hf.1 p).finrank_eq

end GlobalTheory.BadOnRec

namespace GlobalTheory.BadOnRec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance runAlgBad {D : D7} {J : CoreJ D} [inst : Algebra J.Q.c.F D.what₂.LL] (r : _root_.GlobalTheory.RealIndexBound.RunData J) :
    Algebra r.full.J.Q.c.F D.what₂.LL := inst

section General

open scoped TensorProduct

attribute [local instance 2000] Submodule.module

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {h : LawsP T.toTop} {fw : FWTie T.J R κ v₀} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ}
  {ι : Fin D.R.m} {wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)} {nT : ℕ}
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  {O : OnObj S P oc} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {i : Bs.J}
  {z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
    D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {inc : P →* G}
  {ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)} {ph : ℂ}
  {y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (srcDim A ι (R.mu v) F.P0 F.ψ0⁻¹) → D.what₂.LL)}

theorem mem_eig_iff (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ F.P0 F.ψ0⁻¹ ph y) (ha : ActionPin h fw ι ℓ)
    (hG : R.IsGrp F) (hinc : F.P0 ≤ inc.range) (x : Fin (O.nZ i) → D.what₂.LL) :
    x ∈ Formalism.EigenvalueLevelCeiling.eig (O.ρ i) O.U O.ψ ↔ GlobalTheory.OnTies.toForms h fw ι z x ∈ GlobalTheory.CovTop.spType R F ι := by
  have hb := GlobalTheory.OnTies.toForms_bijective h fw ι z
  have e1 : x ∈ Formalism.EigenvalueLevelCeiling.eig (O.ρ i) O.U O.ψ ↔ ∀ u : O.U, O.ρ i u x = ((O.ψ u : 𝓞 D.what₂.LL) : D.what₂.LL) • x := by
    unfold Formalism.EigenvalueLevelCeiling.eig
    rw [Submodule.mem_iInf]
    exact forall_congr' fun u => sub_eq_zero
  have e2 : ∀ (g : P) (hg : inc g ∈ F.P0), O.ρ i g x = ((O.ψ g : 𝓞 D.what₂.LL) : D.what₂.LL) • x ↔
      (R.FW ι).ρ (inc g) (GlobalTheory.OnTies.toForms h fw ι z x) =
        (((R.FW ι).chi (inc g) * F.ψ0⁻¹ ⟨inc g, hg⟩ : D.what₂.LLˣ) : D.what₂.LL) • GlobalTheory.OnTies.toForms h fw ι z x :=
    fun g hg => by
      rw [← t.rho_eq_of_actionPin ha, GlobalTheory.OnCoord.chi_eq_one hG ι hg, one_mul, ← t.ψ_eq g hg, ← map_smul, hb.1.eq_iff]
  refine e1.trans ⟨fun hx => ?_, fun hx u => ?_⟩
  · rintro ⟨g, hg⟩
    obtain ⟨u, rfl⟩ := hinc hg
    exact (e2 u hg).1 (hx ⟨u, t.U_eq.ge hg⟩)
  · exact (e2 u (t.U_eq.le u.2)).2 (hx ⟨inc u, t.U_eq.le u.2⟩)

end General

end GlobalTheory.BadOnRec

namespace GlobalTheory.BadOnRec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

attribute [local instance] runAlgBad

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz}

end Point

end GlobalTheory.BadOnRec

namespace GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.BigOn
end
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open scoped TensorProduct

namespace GlobalTheory.GenSmoothCover

theorem isPullback_rat (k K : Type) [CommRing k] [IsDomain k] [Module.Finite ℤ k] [CharZero k] [Field K] [CharZero K]
    [Algebra k K] [IsFractionRing k K] :
    IsPullback (spMap (algebraMap k K)) (spMap (algebraMap ℚ K)) (spMap (Int.castRingHom k))
      (spMap (algebraMap ℤ ℚ)) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid k (nonZeroDivisors ℤ)) K := inferInstance
  have := Algebra.isPushout_of_isLocalization (nonZeroDivisors ℤ) ℚ k K
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_of_isPushout ℤ k ℚ K)

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}


attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem genericFibre [IsIntegral X] (h : IsArithVar p D) {K : Type} [Field K] [Algebra k K]
    [IsFractionRing k K] {Y : Scheme.{0}} {j : Y ⟶ X} {q : Y ⟶ Sp K}
    (H : IsPullback j q p (spMap (algebraMap k K))) :
    ∃ _ : IsIntegral Y, topologicalKrullDim Y = D ∧ j (genericPoint Y) = genericPoint X := by
  have := h.isDomain
  have : IsProper p := CommonModel.isProper_of_isProjOver h.isProjOver
  obtain ⟨A, _, _, i, _, a, -, hi⟩ := exists_affine_chart_over p (genericPoint X)
  have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨a⟩
  obtain ⟨_, _, _⟩ := RegGenSmooth.chart_props h i hi
  obtain ⟨_, hd⟩ := RegGenSmooth.ringKrullDim_chart h H i hi
  have := IsLocalization.tensorRight (S := A) K (nonZeroDivisors k)
  have hle : Algebra.algebraMapSubmonoid A (nonZeroDivisors k) ≤ nonZeroDivisors A :=
    Submonoid.map_le_iff_le_comap.mpr fun x hx ↦ mem_nonZeroDivisors_of_ne_zero
      (by simpa using nonZeroDivisors.ne_zero hx)
  have hinj : Function.Injective (algebraMap A (K ⊗[k] A)) := IsLocalization.injective _ hle
  obtain ⟨i₀, _, H₀⟩ := exists_affine_chart_of_isPullback H i hi
  have : LocallyOfFiniteType q := MorphismProperty.of_isPullback H inferInstance
  have := IsPreimmersion.of_isLocalization (R := k) (S := K) (nonZeroDivisors k)
  have : IsPreimmersion j := MorphismProperty.of_isPullback H.flip this
  have := flat_specMap_localization (nonZeroDivisors k) K
  have : Flat j := MorphismProperty.of_isPullback H.flip this
  let η : Spec (.of (K ⊗[k] A)) := (⟨⊥, inferInstance⟩ : PrimeSpectrum _)
  have e₁ : topologicalKrullDim (closure {i₀ η} : Set Y) = D :=
    (topologicalKrullDim_closure_eq_ringKrullDim_quotient q i₀ η).trans
      ((ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)).trans hd)
  have e₂ : j (i₀ η) = genericPoint X := by
    rw [← Scheme.Hom.comp_apply, H₀.w, Scheme.Hom.comp_apply, ← genericPoint_eq_of_isOpenImmersion i]
    congr 1
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ hinj)
  have e₃ : closure {i₀ η} = Set.univ :=
    Set.eq_univ_of_forall fun y => specializes_iff_mem_closure.1
      (j.isEmbedding.isInducing.specializes_iff.1 (e₂ ▸ genericPoint_specializes _))
  have : IrreducibleSpace Y := (irreducibleSpace_def Y).2 (by
    rw [Set.top_eq_univ, ← e₃]; exact isIrreducible_singleton.closure)
  have hr (y : Y) : _root_.IsReduced (Y.presheaf.stalk y) := by
    have := GenSpread.isIso_stalkMap_of_flat j y
    exact isReduced_of_injective (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv.symm
      (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv.symm.injective
  have : IsReduced Y := isReduced_of_isReduced_stalk Y
  rw [e₃, (Homeomorph.Set.univ Y).isHomeomorph.topologicalKrullDim_eq] at e₁
  refine ⟨isIntegral_of_irreducibleSpace_of_isReduced Y, e₁, ?_⟩
  rw [← e₂, (genericPoint_spec Y).eq (show IsGenericPoint (i₀ η) Set.univ from e₃)]

theorem exists_closure (hp : IsProjOver p) {K : Type} [Field K] [Algebra k K] [IsFractionRing k K] {W : Scheme.{0}}
    [IsIntegral W] (w : W ⟶ X) (q : W ⟶ Sp K) (hw : w ≫ p = q ≫ spMap (algebraMap k K)) (hq : IsProjOver q) :
    ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X) (_ : IsIntegral Y) (j : W ⟶ Y), j ≫ ρ = w ∧ IsProjOver (ρ ≫ p) ∧
      IsPullback j q (ρ ≫ p) (spMap (algebraMap k K)) ∧ IsSchemeTheoreticallyDominant j ∧ QuasiCompact j := by
  obtain ⟨M, i, _, rfl⟩ := hq
  have B := ProjSpace.isPullback_baseChange M (algebraMap k K)
  have hP := ProjSpace.isProjOver_pullback hp (ProjSpace.isProjOver_pspace_str k M)
  let π := pullback.fst p (PSpace.str k M) ≫ p
  have : IsProper π := CommonModel.isProper_of_isProjOver hP
  let j : W ⟶ pullback p (PSpace.str k M) :=
    pullback.lift w (i ≫ ProjSpace.baseChange M (algebraMap k K)) (by rw [hw, Category.assoc, Category.assoc, B.w])
  have hj₁ : j ≫ pullback.fst _ _ = w := pullback.lift_fst _ _ _
  have hj₂ : j ≫ pullback.snd _ _ = i ≫ ProjSpace.baseChange M (algebraMap k K) := pullback.lift_snd _ _ _
  have G := IsPullback.of_hasPullback π (spMap (algebraMap k K))
  let c := G.lift j (i ≫ PSpace.str K M) (by rw [reassoc_of% hj₁, hw])
  have hc₁ : c ≫ pullback.fst _ _ = j := G.lift_fst _ _ _
  have hc₂ : c ≫ pullback.snd _ _ = i ≫ PSpace.str K M := G.lift_snd _ _ _
  let t := B.lift (pullback.fst π (spMap (algebraMap k K)) ≫ pullback.snd _ _) (pullback.snd _ _)
    (by rw [Category.assoc, ← pullback.condition, G.w])
  have ht₁ : t ≫ _ = _ := B.lift_fst _ _ _
  have ht₂ : t ≫ _ = _ := B.lift_snd _ _ _
  have : IsSeparated (t ≫ PSpace.str K M) := by rw [ht₂]; infer_instance
  have : IsSeparated t := IsSeparated.of_comp t (PSpace.str K M)
  have hct : c ≫ t = i := B.hom_ext (by rw [Category.assoc, ht₁, reassoc_of% hc₁, hj₂])
    (by rw [Category.assoc, ht₂, hc₂])
  have : IsClosedImmersion (c ≫ t) := by rwa [hct]
  have : IsClosedImmersion c := .of_comp c t
  have := flat_specMap_localization (nonZeroDivisors k) K
  have := mono_specMap_localization (nonZeroDivisors k) K
  have : QuasiCompact j := by rw [← hc₁]; infer_instance
  have H := (isPullback_toImage_of_isClosedImmersion j c _ hc₁).flip.paste_vert G
  rw [hc₂] at H
  refine ⟨j.image, j.imageι ≫ pullback.fst _ _, inferInstance, j.toImage, by simp [hj₁], ?_, ?_, inferInstance,
    inferInstance⟩
  · rw [Category.assoc]
    exact ProjSpace.isProjOver_comp_of_isClosedImmersion _ hP
  · rw [Category.assoc]
    exact H

theorem exists_isCov_genSmooth : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    [IsIntegral X] (D : ℕ), IsArithVar p D → ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X) (_ : IsIntegral Y),
      FlagChain.IsCov p D ρ ∧ GenSmooth (ρ ≫ p) D := by
  intro hP k _ X p _ D h
  have := h.isDomain
  have := h.finite
  have := h.charZero_base
  have := h.isNoetherianRing
  let K := FractionRing k
  have G := IsPullback.of_hasPullback p (spMap (algebraMap k K))
  set f := pullback.fst p (spMap (algebraMap k K))
  set q := pullback.snd p (spMap (algebraMap k K))
  obtain ⟨_, hd, hf⟩ := genericFibre h G
  have hq : IsProjOver q := ProjSpace.isProjOver_of_isPullback_spMap _ G h.isProjOver
  obtain ⟨W, s, U, _, hsm, hW, hU, hiso⟩ := WeakRes.weak_resolution hP K _ q D hq hd
  have : IsProper q := CommonModel.isProper_of_isProjOver hq
  have : IsProper (s ≫ q) := CommonModel.isProper_of_isProjOver hW
  have hdW : topologicalKrullDim W = D :=
    (OpenDim.topologicalKrullDim_eq_of_isIso_restrict K _ W q (s ≫ q) s inferInstance inferInstance rfl U hU hiso).trans hd
  obtain ⟨Y, ρ, _, j, hj, hY, H, _, _⟩ := exists_closure h.isProjOver (s ≫ f) (s ≫ q)
    (by rw [Category.assoc, Category.assoc, G.w]) hW
  have : IsProper (ρ ≫ p) := CommonModel.isProper_of_isProjOver hY
  have : IsFinite (spMap (Int.castRingHom k)) := (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 h.finite)
  have H' := H.paste_vert (isPullback_rat k K)
  have : Flat (j ≫ (ρ ≫ p) ≫ spMap (Int.castRingHom k)) := flat_of_over_fractionField (K := ℚ) _ _ H'.w.symm
  have hfl : Flat ((ρ ≫ p) ≫ spMap (Int.castRingHom k)) := flat_of_schemeDominant_of_isDedekindDomain j _
  have hA : IsArithVar (ρ ≫ p) D :=
    ⟨h.isDomain, h.finite, ‹_›, hY, hfl, IntModel.topologicalKrullDim_eq_succ Int.not_isField H' hdW⟩
  obtain ⟨_, -, hjη⟩ := genericFibre hA H
  obtain ⟨x, hx⟩ := hU
  have : Nonempty (s ⁻¹ᵁ U : W.Opens).toScheme := ⟨inv (s ∣_ U) ⟨x, hx⟩⟩
  have : IsIntegral (s ⁻¹ᵁ U : W.Opens).toScheme := isIntegral_of_isOpenImmersion (s ⁻¹ᵁ U).ι
  have e : ((s ⁻¹ᵁ U).ι ≫ j) ≫ ρ = (s ∣_ U ≫ U.ι) ≫ f := by
    rw [Category.assoc, hj, morphismRestrict_ι, Category.assoc]
  have eη : ((s ⁻¹ᵁ U).ι ≫ j) (genericPoint _) = genericPoint Y := by
    rw [Scheme.Hom.comp_apply, genericPoint_eq_of_isOpenImmersion, hjη]
  have := IsPreimmersion.of_isLocalization (R := k) (S := K) (nonZeroDivisors k)
  have : IsPreimmersion f := MorphismProperty.of_isPullback G.flip this
  refine ⟨Y, ρ, ‹_›, ⟨hA, ?_, ?_⟩, fun σ => ?_⟩
  · rw [← eη, ← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply, genericPoint_eq_of_isOpenImmersion, hf]
  · have h₁ := PullbackFinitePoint.residueDegree_ne_zero_of_surjectiveOnStalks ((s ∣_ U ≫ U.ι) ≫ f) (genericPoint _)
    rw [← e, CurveDegreesCompare.residueDegree_comp, eη] at h₁
    exact left_ne_zero_of_mul h₁
  · have : LocallyOfFinitePresentation (ρ ≫ p) := inferInstance
    exact ⟨⟨AlgChart (ρ ≫ p) σ D, id, ModelCharts.exists_chart H (RegGenSmooth.injective_of_charZero σ)⟩⟩

end GlobalTheory.GenSmoothCover
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.inertPlace_doubledUnitary_vacuumTensor_eigen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M'.co dd →
      IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M'.vac v) R →
    ∀ g ∈ GlobalTheory.InertDbl.KAtD σ G.W v, ∃ c : ℂ, omd g (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      c • GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  first | exact @GlobalTheory.InertDblLine.line | exact GlobalTheory.InertDblLine.line | (intros; apply GlobalTheory.InertDblLine.line <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVac

theorem gen_diag_anti : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ H : Subgroup (GlobalTheory.DblVac.UD σ G.W),
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PDiag σ G.W → p ∈ H) →
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PAnti σ G.W → p ∈ H) → ∀ g ∈ GlobalTheory.DblVac.KD σ G.W v, g ∈ H := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hv H hD hA g hg
  obtain ⟨p, hpK, hpD, hpgK, hbig⟩ := GlobalTheory.T.exists_diagonalStabiliser_mul_mem_bigCell_inert σ B G.W _ _ hT.base hT.geo.hW v w hv g hg
  obtain ⟨q, hqK, hqA, p', hp'K, hp'D, he⟩ := GlobalTheory.T.doubledVacuumStabilizer_gaussDecomposition_bigCell σ G.W v (hT.base.inert v w hv).1 (p * g) hpgK hbig
  have hg' : g = p⁻¹ * (q * p') := by rw [← he]; group
  rw [hg']
  exact H.mul_mem (H.inv_mem (hD p hpK hpD)) (H.mul_mem (hA q hqK hqA) (hD p' hp'K hp'D))

end GlobalTheory.DblVac
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.doubledVacuum_eigen_inertPlace_latticeStabiliser : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.V →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) d' dd →
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) dd (X.β / X.α) (diagCols (Fin a)) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r →
    ∀ g ∈ GlobalTheory.DblVac.KD σ G.V v, ∃ μ : ℂ,
      omd g (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) := by
  first | exact @GlobalTheory.VDblEig.vdbl_eigen | exact GlobalTheory.VDblEig.vdbl_eigen | (intros; apply GlobalTheory.VDblEig.vdbl_eigen <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.WeilAdmCMUnit

theorem isUnitaryOn_transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → IsUnitaryOn (adeleClass F) om :=
  GlobalTheory.T.isUnitaryOn_weilDatum_transport_adelicSchwartz

end GlobalTheory.WeilAdmCMUnit
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.transportedWeilDatum_CM_preserves_schwartz_heisenberg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om →
              (∀ p, ∀ φ ∈ schA F κ, om p φ ∈ schA F κ) ∧
              ∀ p w, ∀ φ ∈ schA F κ, om p (co.rho B.ψ w φ) = co.rho B.ψ (actAB (cA σ) p w) (om p φ) := by
  first | exact @GlobalTheory.TransportHeisF.pres_impl | exact GlobalTheory.TransportHeisF.pres_impl | (intros; apply GlobalTheory.TransportHeisF.pres_impl <;> assumption)
end

section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CuspEmb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem isSec_cast (X : Data E r) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E) (p0 : ℕ)
    (h1 : X.Ψ = Ψ) (h2 : X.Gm = Gm) (h3 : X.p0 = p0) (la : Wt Ψ r) (G : Frame Ψ r → ℂ)
    (hG : X.IsSec (castWt h1 la) (fun x => G (castFrame h1 x))) :
    DifferentiableOn ℂ G (GG Ψ Gm p0) ∧
      ∀ γ ∈ X.Γ, ∀ x ∈ GG Ψ Gm p0, G (lact γ x) = X.χ (castWt h1 la) γ * G x := by
  subst h1 h2 h3
  exact ⟨hG.1, hG.2.2⟩

theorem res_mem_HA (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C]
    (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ) (hF : F ∈ M.SS la) : M.res F ∈ HA M := by
  have key := fun c => isSec_cast (M.comp c).toData M.Ψ M.Gm M.p0 (M.comp_Ψ c) (M.comp_Gm c) (M.comp_basePoint c) la (F c)
    (hF c).1.1
  refine ⟨fun c => ⟨F c, (key c).1, fun x => rfl⟩, fun c γ hγ x hx => ?_⟩
  show F c (lact γ x.1) = F c x.1
  rw [(key c).2 γ hγ x.1 x.2, M.χ_one c _ γ hγ, one_mul]

end GlobalTheory.CuspEmb

end
end
