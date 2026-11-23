module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIso
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle481
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.JordanChevalley
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
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WdResGen

private theorem wdAt_of_model {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
    {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (B : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces B) {a : ℕ}
    (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (L₂ : FinExt l) (r₂ : ↥(Dec (F := E) A) →* GL (Fin a) ↥L₂.1)
    (hm₂ : IsModel B r L₂ r₂) (hV₂ : IsPst P (B.repE L₂ r₂)) :
    wdAt P ι B h hj r = wdPst P ι B h hj (B.repE L₂ r₂) := by
  obtain ⟨L₁, r₁, hm₁, hV₁, e₁⟩ := wdAt_of_isPstAt ι B h hj (r := r) ⟨L₂, r₂, hm₂, hV₂⟩
  have h₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have h₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have e : mapRep (IntermediateField.inclusion h₁).toRingHom r₁ =
      mapRep (IntermediateField.inclusion h₂).toRingHom r₂ := by
    ext g i j
    exact congrArg (fun f : ↥(Dec (F := E) A) →* GL (Fin a) (Om l) => (f g : Matrix (Fin a) (Fin a) (Om l)) i j)
      (hm₁.2.trans hm₂.2.symm)
  rw [e₁, BridgeParam.wdPst_enlarge P ι B h hj h₁ r₁ hV₁, BridgeParam.wdPst_enlarge P ι B h hj h₂ r₂ hV₂, e]

private theorem wdRel_of_frobSS {E Ω E' Ω' : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'} (φ : Ω ≃+* Ω')
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {ρ : Weil h → Module.End ℂ V} {ρ' : Weil h' → Module.End ℂ V} {N : Module.End ℂ V}
    {a : WDRep h V} {b : WDRep h' V} (ha : IsFrobSS ρ N a) (hb : IsFrobSS ρ' N b)
    (hρ : ∀ σ σ', WeilRel φ σ σ' → ρ σ = ρ' σ') : WDRel φ (WD.mk a) (WD.mk b) := by
  let e := (Module.finBasis ℂ V).equivFun
  refine ⟨_, a.transport e, b.transport e, WD.sound (a.iso_transport e).symm, WD.sound (b.iso_transport e).symm,
    ?_, fun σ σ' hσ => ?_⟩
  · show e.conjAlgEquiv ℂ a.N = e.conjAlgEquiv ℂ b.N
    rw [ha.1, hb.1]
  · show e.conjAlgEquiv ℂ (a.ρ σ) = e.conjAlgEquiv ℂ (b.ρ σ')
    have h1 := hρ σ σ' hσ
    have h2 := hb.2 σ'
    rw [← h1] at h2
    rw [(Module.End.isNilpotent_isSemisimple_unique (ha.2 σ).2 (a.semisimple σ) h2.2 (b.semisimple σ')
      ((ha.2 σ).1.symm.sub_left (Commute.refl _)) (h2.1.symm.sub_left (Commute.refl _))
      (by simp)).2]

end GlobalTheory.WdResGen


open GlobalTheory.WdResGen in

theorem GlobalTheory.RealGal.wdRelRes_gen : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (P : LocPrime l) (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (Bw' : LocBridge l K Ω (Dec (F := K) A) O), Bw'.Kw = Bw.Kw → Bw'.j = Bw.j → Bw'.LL = Bw.LL → ∀ (a : ℕ) (r : G F Ω →* GL (Fin a) (Qbar l)), IsPstAt P Bw (r.comp (Dec (F := F) A).subtype) → ∀ (ι : Qbar l ≃+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (h' : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw') (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) (algebraMap F K) i → WDRel (RingEquiv.refl Ω) (wdAt P ι Bw h hj (r.comp (Dec (F := F) A).subtype)) (wdAt P ι Bw' h' hj' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype)) := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ l _ P A O _ _ _ Bw Bw' hK hJ hL n r hr ι v w h h' hj hj' i hP
  obtain ⟨Kw, j, j_E, j_dense, e, e_cont, e_symm_cont, e_comm, LL, LL_split, eO, eO_alg, eO_cont, eO_symm_cont⟩ := Bw'
  dsimp only at hK hJ hL
  subst hK hJ hL
  set Bw' : LocBridge l K Ω (Dec (F := K) A) O :=
    ⟨Bw.Kw, Bw.j, j_E, j_dense, e, e_cont, e_symm_cont, e_comm, Bw.LL, LL_split, eO, eO_alg, eO_cont, eO_symm_cont⟩
    with hB
  obtain ⟨L, r', hm, hV⟩ := hr
  have key : ∀ (g : ↥(Dec (F := K) A)) (x : Ω), ((Bw.e.symm (e g) : ↥(Dec (F := F) A)) : G F Ω) x = (g : G K Ω) x :=
    fun g x => Bw.j.injective (by rw [← Bw.e_comm, MulEquiv.apply_symm_apply, e_comm])
  let r'' : ↥(Dec (F := K) A) →* GL (Fin n) ↥L.1 := r'.comp (e.trans Bw.e.symm).toMonoidHom
  have hm' : IsModel Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype)
      L r'' := by
    refine ⟨hm.1, MonoidHom.ext fun g => ?_⟩
    have h1 := DFunLike.congr_fun hm.2 (Bw.e.symm (e g))
    refine h1.trans (congrArg r (AlgEquiv.ext (key g)))
  have hrep : Bw'.repE L r'' = Bw.repE L r' := by
    refine MonoidHom.ext fun g => ?_
    have h1 : r'' (e.symm g) = r' (Bw.e.symm g) := by simp [r'']
    exact congrArg (fun m : GL (Fin n) ↥L.1 => Matrix.toLin' (m : Matrix (Fin n) (Fin n) ↥L.1)) h1
  have hV' : IsPst P (Bw'.repE L r'') := by rw [hrep]; exact hV
  rw [wdAt_of_model _ ι Bw h hj _ L r' hm hV, wdAt_of_model _ ι Bw' h' hj' _ L r'' hm' hV', hrep]
  generalize Bw.repE L r' = ρ at hV ⊢
  haveI := hV.finite
  rw [wdPst_of_isPst ι Bw h hj hV, wdPst_of_isPst ι Bw' h' hj' hV]
  obtain ⟨c, hc, hdeg, hq, -⟩ := GlobalTheory.T.place_over_transport_ring_iso F Ω A v h K Ω A w h' _ _ i hP
  refine wdRel_of_frobSS _ (BridgeParam.isFrobSS_wdRep P ι Bw h hj ρ)
    (BridgeParam.isFrobSS_wdRep P ι Bw' h' hj' ρ) fun σ σ' hσ => ?_
  have h1 : weilToGK Bw h σ = weilToGK Bw' h' σ' := by
    have h2 : Subgroup.inclusion (Weil_le_Dec h) σ = Bw.e.symm (e (Subgroup.inclusion (Weil_le_Dec h') σ')) :=
      Subtype.ext (AlgEquiv.ext fun x => (hσ x).trans (key (Subgroup.inclusion (Weil_le_Dec h') σ') x).symm)
    exact (congrArg Bw.e h2).trans (Bw.e.apply_symm_apply _)
  have h3 : alpha l σ = alpha l σ' := by
    rw [alpha, alpha, ← (hc σ σ').1 hσ, hdeg, resDeg, resDeg, hq]
  have h4 : weilD Bw h P ρ σ = weilD Bw' h' P ρ σ' :=
    (weilD_apply Bw h P ρ σ).trans ((congrArg₂ (fun (g : ↥(GK Bw.Kw)) (m : ℤ) => actD P ρ g *
      Units.val (phiU P ρ ^ (-m)))
      h1 h3).trans (weilD_apply Bw' h' P ρ σ').symm)
  refine wd_ext _ ι ρ fun x => ?_
  exact (wdRho_mk P ι Bw h hj ρ σ x).trans
    ((congrArg (wdMk P ι ρ) (LinearMap.congr_fun h4 x)).trans (wdRho_mk P ι Bw' h' hj' ρ σ' x).symm)
end

section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ParamSplitPlace

theorem main : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (r : G F Ω →* GL (Fin a) (Qbar l)) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (h' : IsPlaceOver A w) (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) (algebraMap F K) i → ∀ x' : WD h', IsWDOf ι (r.comp (res F Ω K)) x' → ∃ x : WD h, IsWDOf ι r x ∧ WDRel (RingEquiv.refl Ω) x x' := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ l _ ι n r A v w h h' i hP x' hx'
  obtain ⟨t', ht', φ', hφ', N, b', hN', hb', rfl⟩ := hx'
  obtain ⟨c, hc, hdeg, hq, hsm⟩ := GlobalTheory.T.place_over_transport_ring_iso F Ω A v h K Ω A w h' (RingEquiv.refl Ω) (algebraMap F K) i hP
  have hcz : ∀ (σ : Weil h) (z : Ω), ((c σ : Weil h') : G K Ω) z = (σ : G F Ω) z :=
    fun σ z => ((hc σ (c σ)).2 rfl z).symm
  have hres : ∀ σ : Weil h, res F Ω K ((c σ : Weil h') : G K Ω) = (σ : G F Ω) :=
    fun σ => AlgEquiv.ext fun z => hcz σ z
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic

  have hm : ∀ σ : Ine (F := F) A, ((c (ineIncl h σ) : Weil h') : G K Ω) ∈ Ine (F := K) A := fun σ => by
    rw [← deg_eq_zero_iff, hdeg, deg_ineIncl]
  let e : Ine (F := F) A →* Ine (F := K) A :=
    (((Weil h').subtype.comp c.toMonoidHom).comp (ineIncl h)).codRestrict _ hm
  have he : ∀ σ, ineIncl h' (e σ) = c (ineIncl h σ) := fun σ => Subtype.ext rfl
  have hez : ∀ (σ : Ine (F := F) A) (z : Ω), ((e σ : Ine (F := K) A) : G K Ω) z = (σ : G F Ω) z := fun σ z => by
    have := hcz (ineIncl h σ) z
    rwa [coe_ineIncl] at this
  have he_surj : Function.Surjective e := by
    intro τ
    have hm' : ((c.symm (ineIncl h' τ) : Weil h) : G F Ω) ∈ Ine (F := F) A := by
      rw [← deg_eq_zero_iff, ← hdeg, MulEquiv.apply_symm_apply, deg_ineIncl]
    refine ⟨⟨_, hm'⟩, Subgroup.inclusion_injective (Ine_le_Weil h') ?_⟩
    show ineIncl h' (e _) = ineIncl h' τ
    rw [he]
    have : ineIncl h ⟨_, hm'⟩ = c.symm (ineIncl h' τ) := Subtype.ext rfl
    rw [this, MulEquiv.apply_symm_apply]
  have he_cont : Continuous e := by
    refine continuous_of_continuousAt_one e ?_
    rw [ContinuousAt, map_one, tendsto_subtype_rng]
    intro O' hO'
    obtain ⟨U, hU, hU1, hUO⟩ := GlobalTheory.WeilTransport.conj_nhds F Ω K Ω (RingEquiv.refl Ω) O' hO'
    refine Filter.mem_map.2 (Filter.mem_of_superset ((hU.preimage continuous_subtype_val).mem_nhds hU1) ?_)
    intro τ hτ
    exact hUO (τ : G F Ω) hτ ((e τ : Ine (F := K) A) : G K Ω) fun z => (hez τ z).symm

  let t : Ine (F := F) A →* Multiplicative ℤ_[l] := t'.comp e
  have ht : IsTameChar t := ⟨ht'.1.comp he_cont, ht'.2.comp he_surj⟩
  have hφ : deg (c.symm φ') = 1 := by rw [← hdeg, MulEquiv.apply_symm_apply, hφ']
  have hN : IsMonodromy t r N := by
    obtain ⟨hnil, U', hU', H⟩ := hN'
    refine ⟨hnil, U'.comap e, hU'.preimage he_cont, fun σ hσ => ?_⟩
    have h1 := H (e σ) hσ
    have h2 : res F Ω K ((e σ : Ine (F := K) A) : G K Ω) = (σ : G F Ω) := AlgEquiv.ext fun z => hez σ z
    rw [MonoidHom.comp_apply, h2] at h1
    exact h1
  have hpart : ∀ g : Weil h, e (inePart hφ g) = inePart hφ' (c g) := fun g =>
    Subgroup.inclusion_injective (Ine_le_Weil h') (by
      show ineIncl h' _ = ineIncl h' _
      rw [he, ineIncl_inePart, ineIncl_inePart, map_mul, map_inv, map_zpow, MulEquiv.apply_symm_apply, hdeg])
  have key : ∀ g : Weil h, wdMat t hφ r N g = wdMat t' hφ' (r.comp (res F Ω K)) N (c g) := fun g => by
    rw [wdMat, wdMat, ← hpart]
    show (r (g : G F Ω) : Matrix (Fin n) (Fin n) (Qbar l)) * _ =
      (r (res F Ω K ((c g : Weil h') : G K Ω)) : Matrix (Fin n) (Fin n) (Qbar l)) * _
    rw [hres]
    rfl

  let b : WDRep h (Fin n → ℂ) :=
    { ρ := b'.ρ.comp c.toMonoidHom
      N := b'.N
      smooth := (hsm _ b'.ρ).1 b'.smooth
      semisimple := fun σ => b'.semisimple (c σ)
      nilpotent := b'.nilpotent
      comm := fun σ => by
        have := b'.comm (c σ)
        rwa [hdeg, hq] at this }
  refine ⟨WD.mk b, ⟨t, ht, c.symm φ', hφ, N, b, hN, ⟨hb'.1, fun g => ?_⟩, rfl⟩,
    ⟨_, b, b', rfl, rfl, rfl, fun σ σ' hσ => ?_⟩⟩
  · show Commute (b'.ρ (c g)) _ ∧ IsNilpotent (_ - b'.ρ (c g))
    simpa only [key] using hb'.2 (c g)
  · show b'.ρ (c σ) = b'.ρ σ'
    rw [(hc σ σ').1 hσ]

end GlobalTheory.ParamSplitPlace
end

section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RealGal

theorem bridge_j_mem_Kw_of_dec_le : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O), Dec (F := F) A ≤ (res F Ω K).range → ∀ x : K, Bw.j (algebraMap K Ω x) ∈ Bw.Kw.1 := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ l _ A O _ _ _ Bw hD x
  have hfix : ∀ σ ∈ (Bw.Kw.1).fixingSubgroup, σ (Bw.j (algebraMap K Ω x)) = Bw.j (algebraMap K Ω x) := by
    intro σ hσ
    obtain ⟨g, hg⟩ := Bw.e.surjective ⟨σ, hσ⟩
    have h1 := Bw.e_comm g (algebraMap K Ω x)
    rw [hg] at h1
    obtain ⟨h, hh⟩ := hD g.2
    have h2 : (g : Ω ≃ₐ[F] Ω) (algebraMap K Ω x) = algebraMap K Ω x := by
      rw [← hh]
      exact h.commutes x
    simpa [h2] using h1
  haveI : IsGalois ℚ_[l] (Om l) := inferInstance
  rw [← InfiniteGalois.fixedField_fixingSubgroup Bw.Kw.1]
  exact fun σ => hfix σ.1 σ.2

end GlobalTheory.RealGal
end

section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.RealGal.dRSstCrysPstJumps_descend : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (P : LocPrime l) (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (Bw' : LocBridge l K Ω (Dec (F := K) A) O), Bw'.Kw = Bw.Kw → Bw'.j = Bw.j → Bw'.LL = Bw.LL → ∀ (a : ℕ) (r : G F Ω →* GL (Fin a) (Qbar l)), (IsdRAt P Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype) → IsdRAt P Bw (r.comp (Dec (F := F) A).subtype)) ∧ (IsSstAt P Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype) → IsSstAt P Bw (r.comp (Dec (F := F) A).subtype)) ∧ (IsCrysAt P Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype) → IsCrysAt P Bw (r.comp (Dec (F := F) A).subtype)) ∧ (IsPstAt P Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype) → IsPstAt P Bw (r.comp (Dec (F := F) A).subtype)) ∧ ∀ (τ : K →+* Qbar l) (J : Multiset ℤ), IsJumpsAt P Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype) τ J → IsJumpsAt P Bw (r.comp (Dec (F := F) A).subtype) (τ.comp (algebraMap F K)) J := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ l _ P A O _ _ _ Bw Bw' hK hj hL a r
  obtain ⟨Kw', j', jE', jd', e', ec', esc', ecomm', LL0', hs', eO', h1', h2', h3'⟩ := Bw'
  dsimp only at hK hj hL
  subst hK hj hL
  set Bw' : LocBridge l K Ω (Dec (F := K) A) O :=
    ⟨Bw.Kw, Bw.j, jE', jd', e', ec', esc', ecomm', Bw.LL, hs', eO', h1', h2', h3'⟩ with hBw'
  have key : ∀ (LL' : FinExt l) (r'' : ↥(Dec (F := K) A) →* GL (Fin a) ↥LL'.1),
      IsModel Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype) LL' r'' →
      IsModel Bw (r.comp (Dec (F := F) A).subtype) LL' (r''.comp (Bw.e.trans e'.symm).toMonoidHom) ∧
      Bw.repE LL' (r''.comp (Bw.e.trans e'.symm).toMonoidHom) = Bw'.repE LL' r'' := by
    intro LL' r'' ⟨hle, hmap⟩
    refine ⟨⟨hle, ?_⟩, ?_⟩
    · refine MonoidHom.ext fun g => ?_
      have h1 := DFunLike.congr_fun hmap (e'.symm (Bw.e g))
      have h2 : AlgEquiv.restrictScalarsHom F ((e'.symm (Bw.e g) : ↥(Dec (F := K) A)) : Ω ≃ₐ[K] Ω) =
          ((g : ↥(Dec (F := F) A)) : Ω ≃ₐ[F] Ω) := by
        refine AlgEquiv.ext fun x => Bw.j.injective ?_
        change Bw.j (((e'.symm (Bw.e g) : ↥(Dec (F := K) A)) : Ω ≃ₐ[K] Ω) x) = _
        rw [← ecomm', MulEquiv.apply_symm_apply, Bw.e_comm]
      exact h1.trans (congrArg r h2)
    · refine MonoidHom.ext fun g => ?_
      simp only [LocBridge.repE, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨LL', r'', hm, hd⟩
    obtain ⟨hm2, he⟩ := key LL' r'' hm
    refine ⟨LL', _, hm2, ?_⟩
    unfold LocBridge.IsdRE at hd ⊢
    rw [he]; exact hd
  · rintro ⟨LL', r'', hm, hd⟩
    obtain ⟨hm2, he⟩ := key LL' r'' hm
    refine ⟨LL', _, hm2, ?_⟩
    rw [he]; exact hd
  · rintro ⟨LL', r'', hm, hd⟩
    obtain ⟨hm2, he⟩ := key LL' r'' hm
    refine ⟨LL', _, hm2, ?_⟩
    unfold LocBridge.IsCrysE at hd ⊢
    rw [he]; exact hd
  · rintro ⟨LL', r'', hm, hd⟩
    obtain ⟨hm2, he⟩ := key LL' r'' hm
    refine ⟨LL', _, hm2, ?_⟩
    rw [he]; exact hd
  · rintro τ J ⟨LL', r'', hm, hd, τ', hind, hc⟩
    obtain ⟨hm2, he⟩ := key LL' r'' hm
    refine ⟨LL', _, hm2, ?_, τ', ?_, ?_⟩
    · unfold LocBridge.IsdRE at hd ⊢
      rw [he]; exact hd
    · intro x
      have := hind (algebraMap F K x)
      simp only [RingHom.comp_apply]
      rw [this]
      congr 3
      exact congrArg Bw.j (IsScalarTower.algebraMap_apply F K Ω x).symm
    · intro n
      rw [hc n]
      unfold LocBridge.multE
      rw [he]
end
