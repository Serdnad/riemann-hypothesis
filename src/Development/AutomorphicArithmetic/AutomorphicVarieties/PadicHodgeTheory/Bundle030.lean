module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle440
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle481
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle029
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle028
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle010
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle008
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle002
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

section SlopeTestRemainingChoices
open Neutral.B1 Formalism.L2.Host Formalism.MainNotions.N Polynomial GlobalTheory.Pst UpperTheory.V
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem wdAt_of_model {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
    {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (B : LocBridge l E Ω (_root_.ReciprocityTheory.Gal.Dec (F := E) A) O) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces B) {a : ℕ}
    (r : ↥(_root_.ReciprocityTheory.Gal.Dec (F := E) A) →* GL (Fin a) (Om l)) (L₂ : FinExt l) (r₂ : ↥(_root_.ReciprocityTheory.Gal.Dec (F := E) A) →* GL (Fin a) ↥L₂.1)
    (hm₂ : IsModel B r L₂ r₂) (hV₂ : IsPst P (B.repE L₂ r₂)) :
    wdAt P ι B h hj r = wdPst P ι B h hj (B.repE L₂ r₂) := by
  obtain ⟨L₁, r₁, hm₁, hV₁, e₁⟩ := wdAt_of_isPstAt ι B h hj (r := r) ⟨L₂, r₂, hm₂, hV₂⟩
  have h₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have h₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have e : mapRep (IntermediateField.inclusion h₁).toRingHom r₁ =
      mapRep (IntermediateField.inclusion h₂).toRingHom r₂ := by
    ext g i j
    exact congrArg (fun f : ↥(_root_.ReciprocityTheory.Gal.Dec (F := E) A) →* GL (Fin a) (Om l) => (f g : Matrix (Fin a) (Fin a) (Om l)) i j)
      (hm₁.2.trans hm₂.2.symm)
  rw [e₁, BridgeParam.wdPst_enlarge P ι B h hj h₁ r₁ hV₁, BridgeParam.wdPst_enlarge P ι B h hj h₂ r₂ hV₂, e]

private theorem wdRel_of_frobSS {E Ω E' Ω' : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w}
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A' w'} (φ : Ω ≃+* Ω')
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

private theorem eig_of_wdRel {E Ω E' Ω' : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w}
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A' w'} {φ : Ω ≃+* Ω'}
    {y : WD h} {y' : WD h'} (H : WDRel φ y y') {σ : Weil h} {σ' : Weil h'} (hσ : WeilRel φ σ σ') :
    y.eig σ = y'.eig σ' := by
  obtain ⟨n, b, b', rfl, rfl, -, H⟩ := H
  rw [WD.eig_mk, WD.eig_mk, H σ σ' hσ]


private theorem exists_transfer {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω]
    [Algebra F Ω] [Algebra K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 K)} (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v) (h' : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l F Ω (_root_.ReciprocityTheory.Gal.Dec (F := F) A) O) (Bw' : LocBridge l K Ω (_root_.ReciprocityTheory.Gal.Dec (F := K) A) O)
    (hj : Induces Bw) (hj' : Induces Bw') (hK : Bw'.Kw = Bw.Kw) (hJ : Bw'.j = Bw.j) (hL : Bw'.LL = Bw.LL)
    (hdeg : ∀ (σ : Weil h) (σ' : Weil h'), WeilRel (RingEquiv.refl Ω) σ σ' → deg σ' = deg σ)
    (hq : normV w = normV v) (ι : Qbar l ≃+* ℂ) :
    ∃ t : ↥(_root_.ReciprocityTheory.Gal.Dec (F := K) A) →* ↥(_root_.ReciprocityTheory.Gal.Dec (F := F) A), Continuous t ∧
      (∀ (g : ↥(_root_.ReciprocityTheory.Gal.Dec (F := K) A)) (x : Ω), ((t g : ↥(_root_.ReciprocityTheory.Gal.Dec (F := F) A)) : _root_.Formalism.ConjugateSelfDual.G F Ω) x = (g : _root_.Formalism.ConjugateSelfDual.G K Ω) x) ∧
      ∀ (n : ℕ) (r : ↥(_root_.ReciprocityTheory.Gal.Dec (F := F) A) →* GL (Fin n) (Qbar l)), IsPstAt (Loc.PP l) Bw r →
        IsPstAt (Loc.PP l) Bw' (r.comp t) ∧
          WDRel (RingEquiv.refl Ω) (wdAt (Loc.PP l) ι Bw h hj r) (wdAt (Loc.PP l) ι Bw' h' hj' (r.comp t)) := by
  obtain ⟨Kw, j, j_E, j_dense, e, e_cont, e_symm_cont, e_comm, LL, LL_split, eO, eO_alg, eO_cont, eO_symm_cont⟩ := Bw'
  dsimp only at hK hJ hL
  subst hK hJ hL
  set Bw' : LocBridge l K Ω (_root_.ReciprocityTheory.Gal.Dec (F := K) A) O :=
    ⟨Bw.Kw, Bw.j, j_E, j_dense, e, e_cont, e_symm_cont, e_comm, Bw.LL, LL_split, eO, eO_alg, eO_cont, eO_symm_cont⟩
    with hB
  have key : ∀ (g : ↥(_root_.ReciprocityTheory.Gal.Dec (F := K) A)) (x : Ω), ((Bw.e.symm (e g) : ↥(_root_.ReciprocityTheory.Gal.Dec (F := F) A)) : _root_.Formalism.ConjugateSelfDual.G F Ω) x = (g : _root_.Formalism.ConjugateSelfDual.G K Ω) x :=
    fun g x => Bw.j.injective (by rw [← Bw.e_comm, MulEquiv.apply_symm_apply, e_comm])
  refine ⟨(e.trans Bw.e.symm).toMonoidHom, Bw.e_symm_cont.comp e_cont, key, fun n r hr => ?_⟩
  obtain ⟨L, r', hm, hV⟩ := hr
  let r'' : ↥(_root_.ReciprocityTheory.Gal.Dec (F := K) A) →* GL (Fin n) ↥L.1 := r'.comp (e.trans Bw.e.symm).toMonoidHom
  have hm' : IsModel Bw' (r.comp (e.trans Bw.e.symm).toMonoidHom) L r'' :=
    ⟨hm.1, MonoidHom.ext fun g => DFunLike.congr_fun hm.2 (Bw.e.symm (e g))⟩
  have hrep : Bw'.repE L r'' = Bw.repE L r' := by
    refine MonoidHom.ext fun g => ?_
    have h1 : r'' (e.symm g) = r' (Bw.e.symm g) := by simp [r'']
    exact congrArg (fun m : GL (Fin n) ↥L.1 => Matrix.toLin' (m : Matrix (Fin n) (Fin n) ↥L.1)) h1
  have hV' : IsPst (Loc.PP l) (Bw'.repE L r'') := by rw [hrep]; exact hV
  refine ⟨⟨L, r'', hm', hV'⟩, ?_⟩
  rw [wdAt_of_model _ ι Bw h hj _ L r' hm hV, wdAt_of_model _ ι Bw' h' hj' _ L r'' hm' hV', hrep]
  generalize Bw.repE L r' = ρ at hV ⊢
  haveI := hV.finite
  rw [wdPst_of_isPst ι Bw h hj hV, wdPst_of_isPst ι Bw' h' hj' hV]
  refine wdRel_of_frobSS _ (BridgeParam.isFrobSS_wdRep (Loc.PP l) ι Bw h hj ρ)
    (BridgeParam.isFrobSS_wdRep (Loc.PP l) ι Bw' h' hj' ρ) fun σ σ' hσ => ?_
  have h1 : weilToGK Bw h σ = weilToGK Bw' h' σ' := by
    have h2 : Subgroup.inclusion (Weil_le_Dec h) σ = Bw.e.symm (e (Subgroup.inclusion (Weil_le_Dec h') σ')) :=
      Subtype.ext (AlgEquiv.ext fun x => (hσ x).trans (key (Subgroup.inclusion (Weil_le_Dec h') σ') x).symm)
    exact (congrArg Bw.e h2).trans (Bw.e.apply_symm_apply _)
  have h3 : alpha l σ = alpha l σ' := by
    rw [alpha, alpha, hdeg σ σ' hσ, resDeg, resDeg, hq]
  have h4 : weilD Bw h (Loc.PP l) ρ σ = weilD Bw' h' (Loc.PP l) ρ σ' :=
    (weilD_apply Bw h (Loc.PP l) ρ σ).trans ((congrArg₂ (fun (g : ↥(GK Bw.Kw)) (m : ℤ) => actD (Loc.PP l) ρ g *
      (Units.val (phiU (Loc.PP l) ρ ^ (-m))))
      h1 h3).trans (weilD_apply Bw' h' (Loc.PP l) ρ σ').symm)
  refine wd_ext _ ι ρ fun x => ?_
  exact (wdRho_mk (Loc.PP l) ι Bw h hj ρ σ x).trans
    ((congrArg (wdMk (Loc.PP l) ι ρ) (LinearMap.congr_fun h4 x)).trans (wdRho_mk (Loc.PP l) ι Bw' h' hj' ρ σ' x).symm)

private theorem hasLT_transfer {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω]
    [Algebra F Ω] [Algebra K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω}
    {v : Plc F} {w : Plc K} (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v) (h' : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l F Ω (_root_.ReciprocityTheory.Gal.Dec (F := F) A) O) (Bw' : LocBridge l K Ω (_root_.ReciprocityTheory.Gal.Dec (F := K) A) O)
    (hj : Induces Bw) (hj' : Induces Bw') (hK : Bw'.Kw = Bw.Kw) (hJ : Bw'.j = Bw.j) (hL : Bw'.LL = Bw.LL)
    (hdeg : ∀ (σ : Weil h) (σ' : Weil h'), WeilRel (RingEquiv.refl Ω) σ σ' → deg σ' = deg σ)
    (hq : normV w = normV v) (ι : Qbar l ≃+* ℂ) (c : Weil h' →* Weil h)
    (hc : ∀ σ', WeilRel (RingEquiv.refl Ω) (c σ') σ')
    (hs : ∀ f : Weil h →* ℂˣ, IsSmooth f → IsSmooth (f.comp c))
    (wt : Emb l v → ℤ) (wt' : Emb l w → ℤ) (a : Weil h →* (v.adicCompletion F)ˣ) (a' : Weil h' →* (w.adicCompletion K)ˣ)
    (hp : ∀ σ σ', WeilRel (RingEquiv.refl Ω) σ σ' →
      ∏ᶠ τ : Emb l v, τ.1 (a σ : v.adicCompletion F) ^ wt τ = ∏ᶠ τ : Emb l w, τ.1 (a' σ' : w.adicCompletion K) ^ wt' τ)
    (H : Loc.HasLT h Bw hj ι wt a) : Loc.HasLT h' Bw' hj' ι wt' a' := by
  obtain ⟨μ, ξ, hμ, hξ, hP, h1, h2⟩ := H
  obtain ⟨t, ht, key, hr⟩ := exists_transfer h h' Bw Bw' hj hj' hK hJ hL hdeg hq ι
  obtain ⟨h3, h4⟩ := hr 1 _ hP
  refine ⟨μ.comp t, ξ.comp c, hμ.comp ht, hs ξ hξ, h3, fun σ' => ?_, fun σ' => ?_⟩
  · have e : t (Subgroup.inclusion (Weil_le_Dec h') σ') = Subgroup.inclusion (Weil_le_Dec h) (c σ') :=
      Subtype.ext (AlgEquiv.ext fun x => (key _ x).trans (hc σ' x).symm)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, e, h1, hp _ _ (hc σ')]
  · have e := h2 (c σ')
    rw [eig_of_wdRel h4 (hc σ')] at e
    exact e

private theorem cont_symm {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 K)} (i : v.adicCompletion F ≃+* w.adicCompletion K)
    (hi : Continuous i) : Continuous i.symm := by
  haveI : CharZero (v.adicCompletion F) := charZero_of_injective_algebraMap (algebraMap F _).injective
  haveI : CharZero (w.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K _).injective
  exact (GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation _ _ i hi).1

end SlopeTestRemainingChoices

theorem UpperTheory.hasLocalLanglands_iff_of_placeIso :
    ∀ {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F Ω] [Algebra K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {v : Plc F} {w : Plc K} (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v) (h' : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (_root_.ReciprocityTheory.Gal.Dec (F := F) A) O) (Bw' : LocBridge l K Ω (_root_.ReciprocityTheory.Gal.Dec (F := K) A) O) (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw'), Bw'.Kw = Bw.Kw → Bw'.j = Bw.j → Bw'.LL = Bw.LL → ∀ (jF : F →+* K) (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) jF i → ∀ (ι : Qbar l ≃+* ℂ) (wt : Emb l v → ℤ) (wt' : Emb l w → ℤ), (∀ (τ : Emb l v) (τ' : Emb l w), τ.1 = τ'.1.comp i.toRingHom → wt τ = wt' τ') → ∀ (a : Weil h →* (v.adicCompletion F)ˣ) (a' : Weil h' →* (w.adicCompletion K)ˣ), (∀ σ σ', WeilRel (RingEquiv.refl Ω) σ σ' → a' σ' = Units.map i.toRingHom.toMonoidHom (a σ)) → (UpperTheory.V.Loc.HasLT h Bw hj ι wt a ↔ UpperTheory.V.Loc.HasLT h' Bw' hj' ι wt' a') := by
  intro F K Ω _ _ _ _ _ _ _ _ _ l _ A v w h h' O _ _ _ Bw Bw' hj hj' hK hJ hL jF i hP ι wt wt' hwt a a' ha
  obtain ⟨c, hc, hdeg, hq, hs⟩ := GlobalTheory.T.place_over_transport_ring_iso F Ω A v h K Ω A w h' _ _ i hP
  have hi' : Continuous i.symm := cont_symm i hP.cont
  let E : Emb l w ≃ Emb l v :=
    { toFun := fun τ => ⟨τ.1.comp i.toRingHom, τ.2.comp hP.cont⟩
      invFun := fun τ => ⟨τ.1.comp i.symm.toRingHom, τ.2.comp hi'⟩
      left_inv := fun τ => Subtype.ext (RingHom.ext fun x => congrArg τ.1 (i.apply_symm_apply x))
      right_inv := fun τ => Subtype.ext (RingHom.ext fun x => congrArg τ.1 (i.symm_apply_apply x)) }
  have hp : ∀ σ σ', WeilRel (RingEquiv.refl Ω) σ σ' →
      ∏ᶠ τ : Emb l v, τ.1 (a σ : v.adicCompletion F) ^ wt τ =
        ∏ᶠ τ : Emb l w, τ.1 (a' σ' : w.adicCompletion K) ^ wt' τ := by
    intro σ σ' hσ
    rw [← finprod_comp_equiv E]
    refine finprod_congr fun τ => ?_
    rw [hwt (E τ) τ rfl, ha σ σ' hσ]
    rfl
  have sy : ∀ (σ : Weil h) (σ' : Weil h'), WeilRel (RingEquiv.refl Ω) σ' σ → WeilRel (RingEquiv.refl Ω) σ σ' :=
    fun σ σ' H z => (H z).symm
  have hd : ∀ (σ : Weil h) (σ' : Weil h'), WeilRel (RingEquiv.refl Ω) σ σ' → deg σ' = deg σ :=
    fun σ σ' H => by rw [← (hc σ σ').1 H, hdeg]
  refine ⟨hasLT_transfer h h' Bw Bw' hj hj' hK hJ hL hd hq ι c.symm.toMonoidHom
      (fun σ' => (hc _ _).2 (c.apply_symm_apply σ')) (fun f hf => (hs _ _).2 ?_) wt wt' a a' hp,
    hasLT_transfer h' h Bw' Bw hj' hj hK.symm hJ.symm hL.symm (fun σ' σ H => (hd σ σ' (sy _ _ H)).symm) hq.symm ι
      c.toMonoidHom (fun σ z => ((hc σ _).2 rfl z).symm) (fun f hf => (hs _ f).1 hf) wt' wt a' a
      fun σ' σ H => (hp σ σ' (sy _ _ H)).symm⟩
  have e : (f.comp c.symm.toMonoidHom).comp c.toMonoidHom = f :=
    MonoidHom.ext fun σ => congrArg f (c.symm_apply_apply σ)
  rw [e]
  exact hf
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.V.Loc.prF :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρ : Representation E G V), ContAction ρ → Positive φ ρ → H0dual ((cycA l l E).comp φ) ρ = ⊥ → UpperTheory.V.Loc.finiteCocycles φ ρ = Z1 ρ := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ hc hpos hd
  obtain ⟨h0, -, -, hf⟩ := UpperTheory.V.Loc.posBasic hP φ hφ ρ hc hpos
  obtain ⟨hfin, -, h1, h2⟩ := UpperTheory.V.Loc.tateRat (v := l) (l := l) hP φ hφ ρ hc
  have hB := (UpperTheory.V.Loc.z1fMap φ ρ ρ).1 hc
  rw [hd, finrank_bot] at h2
  rw [h0, finrank_bot, h2, if_pos rfl, zero_add, zero_add] at h1
  have htop : finiteCohomology φ ρ = ⊤ := Submodule.eq_top_of_finrank_eq (hf.trans h1.symm)
  refine le_antisymm (fun c hc' => hc'.1) (fun c hc' => ?_)
  have hm : (Submodule.mkQ _ (⟨c, hc'⟩ : ↥(ReciprocityTheory.Gal.Z1 ρ)) : ReciprocityTheory.Gal.H1 ρ) ∈ finiteCohomology φ ρ := by
    rw [htop]; trivial
  obtain ⟨y, hy, hyc⟩ := hm
  have hsub := (Submodule.Quotient.eq _).1 hyc
  have h3 : (y : G → V) - c ∈ UpperTheory.V.Loc.finiteCocycles φ ρ := hB hsub
  have h4 := (UpperTheory.V.Loc.finiteCocycles φ ρ).sub_mem hy h3
  simpa using h4
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial

private theorem crOn_top {l : ℕ} [Fact l.Prime] {G A V : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A]
    [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] (φ : G →* GQ l)
    (ρ : Representation A G V) : CrOn φ ρ ⊤ ↔ IsCr φ ρ := by
  have he : Function.Surjective (fun g : (⊤ : Subgroup G) => (g : G)) := fun g => ⟨⟨g, trivial⟩, rfl⟩
  have hr : (φ.comp (⊤ : Subgroup G).subtype).range = φ.range := by
    ext σ
    exact ⟨fun ⟨g, hg⟩ => ⟨g, hg⟩, fun ⟨g, hg⟩ => ⟨⟨g, trivial⟩, hg⟩⟩
  have hc : Dcr (φ.comp (⊤ : Subgroup G).subtype)
      (resCoef ℚ_[l] (ρ.comp (⊤ : Subgroup G).subtype : Representation A (⊤ : Subgroup G) V)) =
      Dcr φ (resCoef ℚ_[l] ρ) := by
    unfold Dcr
    exact he.iInf_comp (fun g => LinearMap.ker (actC φ (resCoef ℚ_[l] ρ) g - LinearMap.id))
  unfold CrOn IsCr
  rw [hr, hc]

private def glOn {G R : Type} [Group G] [CommRing R] {m : ℕ} (H : Subgroup G)
    (r : G →* GG (m := m) (R := R))
    (h : ∀ g ∈ H, (r g).right = 1) : H →* GL (Fin m) R where
  toFun g := (r g).left
  map_one' := by simp
  map_mul' g g' := by simp [h g g.2]

private theorem isLCr_iff {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    (D : Dat3 l O) {B : Type} [CommRing B] [Algebra O B] [Algebra ℚ_[l] B]
    (r : GQ l →* GG (m := 3) (R := B))
    (h : ∀ g ∈ D.HL, (r g).right = 1) : D.IsLCr r ↔ IsCr D.HL.subtype (colRep (glOn D.HL r h)) := by
  refine ⟨fun ⟨ρ, h1, h2⟩ => ?_, fun h2 => ⟨_, fun _ => rfl, h2⟩⟩
  have : ρ = glOn D.HL r h := MonoidHom.ext h1
  exact this ▸ h2

theorem UpperTheory.V.Loc.dualCr :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O]
      (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E]
      [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E]
      [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E]
      (r : GQ l →* GG (m := 3) (R := E)), HasMult D.η r → Continuous (fun g => (r g).mat) →
      ∀ γ ∈ Z1 (adRep r), ∀ r' : GQ l →* GG (m := 3) (R := DualNumber E), DualDef r γ r' →
        (D.IsLCr r' ↔ D.IsLCr r ∧ γ ∈ finiteCocycles (MonoidHom.id _) (adRep r)) := by
  intro l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _ _ _ _ r hm hr γ hγ r' hd
  haveI : IsModuleTopology ℚ_[l] (Matrix (Fin 3) (Fin 3) E) :=
    inferInstanceAs (IsModuleTopology ℚ_[l] (Fin 3 → Fin 3 → E))
  have hη : IsOpen (D.η.ker : Set (GQ l)) := by
    have e : D.η.ker = GK D.Kv := Subgroup.ext fun g => D.η_ker g
    haveI := D.Kv.2
    rw [e]
    exact IntermediateField.fixingSubgroup_isOpen D.Kv.1
  have hH : IsOpen (D.HL : Set (GQ l)) := hη.inter D.τ_open
  haveI : D.HL.Normal := inferInstanceAs (D.η.ker ⊓ D.τ.ker).Normal
  haveI : Finite (GQ l ⧸ D.HL) := Subgroup.quotient_finite_of_isOpen _ hH
  haveI : D.HL.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have h1 : ∀ g ∈ D.HL, (r g).right = 1 := fun g hg => (hm g).trans hg.1
  have h1' : ∀ g ∈ D.HL, (r' g).right = 1 := fun g hg => (hd g).1.trans (h1 g hg)
  have had : ((adRep r).comp D.HL.subtype : Representation E D.HL _) = adGL (glOn D.HL r h1) := by
    refine MonoidHom.ext fun g => LinearMap.ext fun X => ?_
    change (r g).adFun X = _
    rw [GG.adFun, if_pos (h1 g g.2)]
    rfl
  have hy : (fun h : D.HL => γ h) ∈ Z1 (adGL (glOn D.HL r h1)) := by
    rw [← had]
    exact ⟨hγ.1.comp continuous_subtype_val, fun g h => hγ.2 g h⟩
  have key := deformCr D.HL.subtype hH.isOpenEmbedding_subtypeVal (glOn D.HL r h1)
    (hr.comp continuous_subtype_val) _ hy (glOn D.HL r' h1') (fun g i j => (hd g).2 i j) ⊤ (by simp)
  rw [isLCr_iff D r' h1', isLCr_iff D r h1, ← crOn_top, ← crOn_top, key,
    z1fDesc (MonoidHom.id _) (adRep r) D.HL γ hγ, had, MonoidHom.id_comp]
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private theorem gam_cocycle {G B : Type} [Group G] [CommRing B] {η : G →* ℤˣ} (T : Tor η B) (h : B)
    (β : G → B × B) (hβ : ∀ g g', β (g * g') = β g + T.M1 g (β g')) (a b c : G) :
    (T.χ2 a : B) * (-(h * omg (β b) (T.M1 b (β c)))) - (-(h * omg (β (a * b)) (T.M1 (a * b) (β c))))
      + (-(h * omg (β a) (T.M1 a (β (b * c))))) - (-(h * omg (β a) (T.M1 a (β b)))) = 0 := by
  have e := T.alternatingForm_adjointSuperdiagRep a (β b) (T.M1 b (β c))
  rw [hβ a b, hβ b c, map_mul, Module.End.mul_apply, map_add (f := _)]
  generalize T.M1 a (T.M1 b (β c)) = u at e ⊢
  generalize T.M1 a (β b) = w at e ⊢
  simp only [omg, Prod.fst_add, Prod.snd_add] at e ⊢
  linear_combination h * e

theorem UpperTheory.exists_continuous_isGam_of_torus_cocycle :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {η : GQ l →* ℤˣ} {Ψ : GQ l →* Eˣ} {H : Subgroup (GQ l)} {e : ℕ} (hD : TriDat η Ψ H e) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (T : Tor η B), T.Good π Ψ → ∀ (h : B), ∀ β ∈ Z1 T.M1, ∃ γ : GQ l → B, Continuous γ ∧ T.IsGam h β γ := by
  intro hP l _ E _ _ _ _ _ η Ψ H e hD B _ _ _ _ _ _ _ _ _ _ π hπ T hT h β hβ
  haveI : ContinuousConstSMul E B := contConstSMul_alg E
  have hχ := Tor.continuous_χ2 hD.ηlc T hT.cont hT.cont_inv
  have hM := Tor.contAction_torus_module hD.ηlc T hT.cont hT.cont_inv
  have hρ : ContAction (resCoef E (chRep T.χ2)) := contAction_chRep hχ
  obtain ⟨-, f2, -, e2⟩ := tateRat hP (v := l) (l := l) (MonoidHom.id (GQ l)) IsOpenEmbedding.id
    (resCoef E (chRep T.χ2)) hρ
  obtain ⟨s, hs, hsi⟩ := ((cycInertia l).2 H hD.isOpen).2
  have hsH : s ∈ H := hs.1
  have hsI : s ∈ Iq l := hs.2
  have hχs : (T.χ2 s : B) = algebraMap E B ((cycA l l E s ^ (2 * e) : Eˣ) : E) := by
    have h0 := hT.ine s hsI 0
    have h2 := hT.ine s hsI 2
    have w0 : wt1 (0 : Fin 3) = 1 := by decide
    have w2 : wt1 (2 : Fin 3) = -1 := by decide
    rw [w0, zpow_one] at h0
    rw [w2, zpow_neg_one] at h2
    have k0 : T.t s 0 = Units.map (algebraMap E B : E →* B) (Ψ s) := Units.ext h0
    have k2 : T.t s 2 = Units.map (algebraMap E B : E →* B) (Ψ s)⁻¹ := Units.ext h2
    rw [Tor.χ2_apply, hD.ηH s hsH, k0, k2, ← map_div, div_inv_eq_mul, hD.ΨH s hsH hsI, ← pow_add, ← two_mul]
    simp
  have hne : ((cycA l l E s ^ (2 * e) : Eˣ) : E) ≠ (cycA l l E s : E) := by
    intro hc
    apply hsi
    have h1 : cycA l l E s ^ (2 * e - 1) = 1 := by
      have := Units.ext hc
      have he := hD.e_pos
      rw [show 2 * e = (2 * e - 1) + 1 by omega, pow_succ] at this
      exact mul_eq_right.1 this
    have inj : Function.Injective (algebraMap ℤ_[l] E) := by
      rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E]
      exact (algebraMap ℚ_[l] E).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
    refine isOfFinOrder_iff_pow_eq_one.2 ⟨2 * e - 1, by have := hD.e_pos; omega, ?_⟩
    apply Units.map_injective (f := (algebraMap ℤ_[l] E : ℤ_[l] →* E)) inj
    rw [map_pow, map_one]
    exact h1
  have hbot : H0dual ((cycA l l E).comp (MonoidHom.id (GQ l))) (resCoef E (chRep T.χ2)) = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    rw [Submodule.mem_bot]
    refine LinearMap.ext fun x => ?_
    have h1 : f ((T.χ2 s : B) * x) = (cycA l l E s : E) * f x := hf s x
    rw [hχs, ← Algebra.smul_def, map_smul, smul_eq_mul] at h1
    exact (mul_eq_zero.1 (show (_ - _) * f x = 0 by rw [sub_mul, h1, sub_self])).resolve_left (sub_ne_zero.2 hne)
  rw [hbot, finrank_bot] at e2
  haveI := f2
  have hsub : Subsingleton (H2 (resCoef E (chRep T.χ2))) := Module.finrank_zero_iff.1 e2
  have hc : Continuous fun p : GQ l × GQ l => -(h * omg (β p.1) (T.M1 p.1 (β p.2))) := by
    have a1 : Continuous fun p : GQ l × GQ l => β p.1 := hβ.1.comp continuous_fst
    have a2 : Continuous fun p : GQ l × GQ l => T.M1 p.1 (β p.2) :=
      hM.comp (continuous_fst.prodMk (hβ.1.comp continuous_snd))
    exact (continuous_const.mul ((a1.fst.mul a2.snd).sub (a1.snd.mul a2.fst))).neg
  let z : Z2 (resCoef E (chRep T.χ2)) := ⟨fun p => -(h * omg (β p.1) (T.M1 p.1 (β p.2))), hc,
    fun a b c => gam_cocycle T h β hβ.2 a b c⟩
  have hz : z ∈ (B2 (resCoef E (chRep T.χ2))).comap (Z2 (resCoef E (chRep T.χ2))).subtype :=
    (Submodule.Quotient.mk_eq_zero _).1 (Subsingleton.elim _ _)
  obtain ⟨γ, hγ, hγ2⟩ := (separated_dvr_second_cohomology_mem _ _).1 hz
  refine ⟨γ, hγ, fun g g' => ?_⟩
  have h1 : (T.χ2 g : B) * γ g' - γ (g * g') + γ g = -(h * omg (β g) (T.M1 g (β g'))) := congrFun hγ2 (g, g')
  linear_combination -h1
end
