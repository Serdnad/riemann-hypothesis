module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle273
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle336
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle045
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Bundle017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle612
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle618
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle837
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle466
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle617
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIso
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle556
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.UniformSpace.Uniformizable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem charPol_lpChar {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w} {n : ℕ} (x y : WD h) (s : Weil h)
    (α : Fin n → ℂ) (c : ℂ) (hx : x.charPol s = ∏ j, (X - C (α j))) (hy : y.charPol s = X - C c) :
    (x.lpChar y).charPol s = ∏ j, (X - C (α j * c)) := by
  have hd : y.lpDim = 1 := by rw [← WD.charPol_natDegree y s, hy, natDegree_X_sub_C]
  have hc : y.eig s = {c} := by
    change (y.charPol s).roots = _
    rw [hy, roots_X_sub_C]
  have h1 := GlobalTheory.RowTie.EigTwist.eig_lpChar x y s hd c hc
  change ((x.lpChar y).charPol s).roots = (x.charPol s).roots.map _ at h1
  have h2 : (x.charPol s).roots = Finset.univ.val.map α := by
    rw [hx, ← roots_multiset_prod_X_sub_C (Finset.univ.val.map α), Multiset.map_map]
    rfl
  rw [(IsAlgClosed.splits _).eq_prod_roots_of_monic (WD.charPol_monic (x.lpChar y) s), h1, h2, Multiset.map_map,
    Multiset.map_map]
  rfl

theorem UpperTheory.deRham_rational_twist_by_character :
    GlobalTheory.Published.DeRhamPotSemistable → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {n : ℕ} (r r' : ↥(Dec (F := F) A) →* GL (Fin n) (Qbar l)) (μ : ↥(Dec (F := F) A) →* (Qbar l)ˣ), Continuous r → Continuous r' → Continuous μ → (∀ g, (r' g : Matrix (Fin n) (Fin n) (Qbar l)) = (μ g : Qbar l) • (r g : Matrix (Fin n) (Fin n) (Qbar l))) → ∀ (HT : (F →+* Qbar l) → Multiset ℤ) (c : (F →+* Qbar l) → ℤ) (α : Fin n → ↥(Weil h) → ℂ) (β : ↥(Weil h) → ℂ), DRat ι h r HT (fun s => ∏ j, (X - C (α j s))) → DRat ι h (GlobalTheory.TripleGal.rk1 μ) (fun τ => {c τ}) (fun s => X - C (β s)) → DRat ι h r' (fun τ => (HT τ).map (· + c τ)) (fun s => ∏ j, (X - C (α j s * β s))) := by
  intro hP F Ω _ _ _ _ _ l _ ι A w h n r r' μ hr hr' hμ he HT c α β h1 h2 O _ _ _ Bw hj
  obtain ⟨d1, j1, p1⟩ := h1 O Bw hj
  obtain ⟨d2, j2, p2⟩ := h2 O Bw hj
  have tw := GlobalTheory.TwistAbove.twist_above l _ _ (UpperTheory.V.Loc.tiedP l) F Ω _ O Bw n r r' μ he
  have d3 := tw.1 d1 d2
  refine ⟨d3, fun τ L' τ' hτ => tw.2.2.2 τ _ _ (j1 τ L' τ' hτ) (j2 τ L' τ' hτ), fun s => ?_⟩
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  have hdet : Matrix.GeneralLinearGroup.det.comp (GlobalTheory.TripleGal.rk1 μ) = μ := by
    ext g
    simp [GlobalTheory.TripleGal.rk1, Matrix.det_unique]
  have hr'e : r' = Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp (GlobalTheory.TripleGal.rk1 μ)) := by
    rw [hdet, GlobalTheory.TwistBridgeDR.twGL_eq]
    exact MonoidHom.ext fun g => Units.ext (he g)
  have c1 := Units.continuous_val.comp hr
  have c3 := Units.continuous_val.comp hr'
  have c2 : Continuous fun g => ((GlobalTheory.TripleGal.rk1 μ g : GL (Fin 1) (Qbar l)) : Matrix (Fin 1) (Fin 1) (Qbar l)) := by
    refine continuous_matrix fun i j => ?_
    have : (fun g => ((GlobalTheory.TripleGal.rk1 μ g : GL (Fin 1) (Qbar l)) : Matrix (Fin 1) (Fin 1) (Qbar l)) i j) =
        fun g => (μ g : Qbar l) := by
      funext g
      fin_cases i; fin_cases j
      simp [GlobalTheory.TripleGal.rk1]
    rw [this]
    exact Units.continuous_val.comp hμ
  have q1 := hP.isPstAt T Bw r c1 d1
  have q2 := hP.isPstAt T Bw _ c2 d2
  have q3 := hP.isPstAt T Bw r' c3 d3
  rw [hr'e] at q3
  rw [hr'e, GlobalTheory.TwistParamAbove.wdAt_twist l _ _ ⟨T⟩ ι F Ω A w h O Bw hj n r _ c1 c2 q1 q2 q3]
  exact charPol_lpChar _ _ s _ _ (p1 s) (p2 s)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial

theorem UpperTheory.V.Loc.rtPoints :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (r : GQ l →* GG (m := 3) (R := B)), D.On U r → (∀ a b, QCont l fun g => (r g).mat a b) ∧ True ∧ D.IsLCr r :=
  by
  intro hP l _ O _ _ _ _ _ _ _ D U B _ _ _ _ _ _ _ r hr
  exact ⟨(GlobalTheory.OrdLoc.rtPoints hP D U B r hr).1, trivial, (GlobalTheory.OrdLoc.rtPoints hP D U B r hr).2⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

section
variable {F M Ω : Type} [Field F] [NumberField F] [Field M] [NumberField M] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  [Algebra M Ω] [IsAlgClosure M Ω] {A : ValuationSubring Ω} {v : Plc F} {w : Plc M}
  {h : IsPlaceOver A v} {h' : IsPlaceOver A w}

private theorem locAlg_step {l : ℕ} [Fact l.Prime] (c : Weil h →* Weil h')
    (hc : ∀ (σ : Weil h) z, (σ : G F Ω) z = (c σ : G M Ω) z) (hdeg : ∀ σ, deg (c σ) = deg σ)
    (i : v.adicCompletion F ≃+* w.adicCompletion M) (hi : Continuous i) (hi' : Continuous i.symm)
    (hA : ∀ a, IsLocalArtin h a → ∃ a', IsLocalArtin h' a' ∧ ∀ σ, (a' (c σ) : w.adicCompletion M) = i (a σ))
    (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (κ' : ↥(Dec (F := M) A) →* (Qbar l)ˣ)
    (hκ : ∀ (g : ↥(Dec (F := F) A)) (g' : ↥(Dec (F := M) A)), (∀ z, (g : G F Ω) z = (g' : G M Ω) z) → κ g = κ' g')
    (wt : Emb l v → ℤ) (wt' : Emb l w → ℤ)
    (hwt : ∀ τ' : Emb l w, wt' τ' = wt ⟨τ'.1.comp i.toRingHom, τ'.2.comp hi⟩) :
    IsLocAlg h' κ' wt' → IsLocAlg h κ wt := by
  rintro ⟨ph, hop, hph⟩
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  have hm : ∀ σ : Ine (F := F) A, ((c (ineIncl h σ) : Weil h') : G M Ω) ∈ Ine (F := M) A := fun σ => by
    rw [← deg_eq_zero_iff, hdeg, deg_ineIncl]
  let e : Ine (F := F) A →* Ine (F := M) A :=
    (((Weil h').subtype.comp c).comp (ineIncl h)).codRestrict _ hm
  have he : ∀ σ, ineIncl h' (e σ) = c (ineIncl h σ) := fun σ => Subtype.ext rfl
  refine ⟨ph.comp e, ?_, fun a ha σ => ?_⟩
  · obtain ⟨O', hO', hpre⟩ := isOpen_induced_iff.mp hop
    have h1 : (1 : G M Ω) ∈ O' := by
      have : (1 : Ine (F := M) A) ∈ Subtype.val ⁻¹' O' := by rw [hpre]; simp
      exact this
    obtain ⟨U, hU, hU1, hUO⟩ := GlobalTheory.WeilTransport.conj_nhds F Ω M Ω (RingEquiv.refl Ω) O' (hO'.mem_nhds h1)
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1)
      (Filter.mem_of_superset ((hU.preimage continuous_subtype_val).mem_nhds hU1) fun τ hτ => ?_)
    have hO : e τ ∈ Subtype.val ⁻¹' O' := hUO τ hτ _ (hc (ineIncl h τ))
    rw [hpre] at hO
    exact hO
  · obtain ⟨a', ha', haa⟩ := hA a ha
    have h1 := hph a' ha' (e σ)
    rw [hκ _ (Subgroup.inclusion (Weil_le_Dec h') (ineIncl h' (e σ))) (hc (ineIncl h σ)), MonoidHom.comp_apply, h1, he, haa]
    let E : Emb l w ≃ Emb l v :=
      { toFun := fun τ' => ⟨τ'.1.comp i.toRingHom, τ'.2.comp hi⟩
        invFun := fun τ => ⟨τ.1.comp i.symm.toRingHom, τ.2.comp hi'⟩
        left_inv := fun τ => Subtype.ext (RingHom.ext fun x => by simp)
        right_inv := fun τ => Subtype.ext (RingHom.ext fun x => by simp) }
    rw [← finprod_comp_equiv E]
    refine finprod_congr fun τ => ?_
    rw [hwt]
    rfl

private theorem artin_step (hG : GlobalArtinReciprocity) (c : Weil h' →* Weil h) (hcs : Function.Surjective c)
    (c' : Weil h →* Weil h') (hcc : ∀ σ, c' (c σ) = σ)
    (hsm : ∀ ξ : Weil h' →* ℂˣ, GlobalTheory.WeilDeligne.IsSmooth ξ → GlobalTheory.WeilDeligne.IsSmooth (ξ.comp c'))
    (i : v.adicCompletion F ≃+* w.adicCompletion M) (hi' : Continuous i.symm)
    (a : Weil h →* (v.adicCompletion F)ˣ) (ha : IsLocalArtin h a)
    (hglob : ∀ art', IsGlobalArtin art' → ∀ σ' : Weil h',
      art' (Neutral.B1.localIdele M w (Units.map i.toRingHom.toMonoidHom (a (c σ')))) = toAb M Ω σ') :
    IsLocalArtin h' ((Units.map i.toRingHom.toMonoidHom).comp (a.comp c)) := by
  obtain ⟨art, hart⟩ := hG M Ω
  obtain ⟨b, hs, ho, hg⟩ := GlobalTheory.InvLocalArtin.exists_invLocalArtin M Ω A w h' art hart
  have hb : (Units.map i.toRingHom.toMonoidHom).comp (a.comp c) = b := MonoidHom.ext fun σ =>
    GlobalTheory.T.globalArtin_localIdele_injective GlobalTheory.Published.chevalleyUnits' M Ω art hart w ((hglob art hart σ).trans (hg σ).symm)
  refine ⟨hb ▸ hs, hb ▸ GlobalTheory.ArtinInvCont.continuous_inv_on_ine M Ω A w h' art b hart ho hg, hb ▸ ho, fun ξ hξ => ?_, hglob⟩
  obtain ⟨χ, hχ, e⟩ := ha.factor _ (hsm ξ hξ)
  refine ⟨χ.comp (Units.map i.symm.toRingHom.toMonoidHom), IsOpen.preimage (Continuous.units_map _ hi') hχ, ?_⟩
  refine MonoidHom.ext fun σ => ?_
  have h1 : Units.map i.symm.toRingHom.toMonoidHom (Units.map i.toRingHom.toMonoidHom (a (c σ))) = a (c σ) := by
    ext; simp
  have h2 := DFunLike.congr_fun e (c σ)
  simp only [MonoidHom.comp_apply] at h2 ⊢
  rw [h1, ← h2, hcc]

end

theorem UpperTheory.isLocallyAlgebraic_transfer_of_placeIso :
    GlobalArtinReciprocity → ∀ {F M Ω : Type} [Field F] [NumberField F] [Field M] [NumberField M] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Algebra M Ω] [IsAlgClosure M Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {v : Plc F} {w : Plc M} (h : IsPlaceOver A v) (h' : IsPlaceOver A w) (j : F →+* M) (i : v.adicCompletion F ≃+* w.adicCompletion M) (hP : PlaceIso A v A w (RingEquiv.refl Ω) j i) (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (κ' : ↥(Dec (F := M) A) →* (Qbar l)ˣ), (∀ (g : ↥(Dec (F := F) A)) (g' : ↥(Dec (F := M) A)), (∀ z, (g : G F Ω) z = (g' : G M Ω) z) → κ g = κ' g') → ∀ (wt : Emb l v → ℤ) (wt' : Emb l w → ℤ), (∀ τ' : Emb l w, wt' τ' = wt ⟨τ'.1.comp i.toRingHom, τ'.2.comp hP.cont⟩) → (IsLocAlg h κ wt ↔ IsLocAlg h' κ' wt') := by
  intro hG F M Ω _ _ _ _ _ _ _ _ _ l _ A v w h h' j i hP κ κ' hκ wt wt' hwt
  obtain ⟨c, hc, hdeg, -, hsm⟩ := GlobalTheory.WeilTransport.weil_equiv F Ω A v h M Ω A w h' _ j i hP
  have hi' : Continuous i.symm := by
    have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
    have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion M w
    exact i.toEquiv.continuous_symm_iff.2
      (AddMonoidHom.isOpenMap_of_sigmaCompact i.toAddEquiv.toAddMonoidHom i.surjective hP.cont)
  have hr : ∀ σ, WeilRel (RingEquiv.refl Ω) σ (c σ) := fun σ => (hc σ _).2 rfl
  have hr' : ∀ σ', WeilRel (RingEquiv.refl Ω) (c.symm σ') σ' := fun σ => (hc _ σ).2 (c.apply_symm_apply σ)
  have inj := GlobalTheory.T.globalArtin_localIdele_injective GlobalTheory.Published.chevalleyUnits'
  constructor
  · refine locAlg_step c.symm.toMonoidHom (fun σ z => (hr' σ z).symm)
      (fun σ => by rw [← hdeg]; simp) i.symm hi' hP.cont (fun a' ha' => ⟨_, artin_step hG c.toMonoidHom c.surjective
        c.symm.toMonoidHom c.symm_apply_apply (fun ξ hξ => (hsm _ _).2 ?_) i.symm hP.cont a' ha' fun art hart σ => ?_,
          fun σ => by simp⟩) κ' κ (fun g g' hg => (hκ g' g fun z => (hg z).symm).symm) wt' wt fun τ => ?_
    · convert hξ using 1
      ext; simp
    · obtain ⟨art', hart'⟩ := hG M Ω
      refine GlobalTheory.T.globalArtin_compat_localDegreeOne F Ω A v h M Ω A w h' _ j i hP art art' hart hart' σ (c σ) _ (hr σ) ?_
      rw [← ha'.glob art' hart' (c σ)]
      congr 2
      ext; simp
    · rw [hwt]
      congr 1
      exact Subtype.ext (RingHom.ext fun x => by simp)
  · refine locAlg_step c.toMonoidHom (fun σ z => hr σ z) hdeg i hP.cont hi'
      (fun a ha => ⟨_, artin_step hG c.symm.toMonoidHom c.symm.surjective
        c.toMonoidHom c.apply_symm_apply (fun ξ hξ => (hsm _ _).1 hξ) i hi' a ha fun art' hart' σ => ?_,
          fun σ => by simp⟩) κ κ' hκ wt wt' hwt
    obtain ⟨art, hart⟩ := hG F Ω
    obtain ⟨b, -, -, hg⟩ := GlobalTheory.InvLocalArtin.exists_invLocalArtin M Ω A w h' art' hart'
    have hx : Units.map i.toRingHom.toMonoidHom (Units.map i.symm.toRingHom.toMonoidHom (b σ)) = b σ := by
      ext; simp
    have h1 := GlobalTheory.T.globalArtin_compat_localDegreeOne F Ω A v h M Ω A w h' _ j i hP art art' hart hart' (c.symm σ) σ _ (hr' σ)
      (by rw [hx]; exact hg σ)
    have h2 := inj F Ω art hart v (h1.trans (ha.glob art hart (c.symm σ)).symm)
    rw [← hg σ, ← hx, h2]
    rfl
end
