module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle350
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle577
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle576
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle324
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.DisjointSplitLevelPlaces
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolKerFin

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem polZero_om_fin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v),
    ∀ Φ, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) → GlobalTheory.PolKer.PolZero Bs G Xc R Rf (om (1, h) Φ) := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM v h hh Φ hΦ
  classical
  obtain ⟨T, hXT, m, f, φ, hf, rfl, hz⟩ := hΦ
  have hP := GlobalTheory.ThK.RealUniq.isPair_V hM.triple
  have h1 : (1 : UA σ G.V.J) ∈ UAt σ G.V (evFin F v) := by
    intro u _
    show u • ((1 : UA σ G.V.J).1.1 - 1) = 0
    simp
  have hex : ∀ φ₀ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ₀ φ₁ :=
    fun φ₀ hφ₀ => GlobalTheory.ThK.LocalOps.acts_exists hP v (1, h) h1 hh φ₀ hφ₀
  choose D hDSB hDA using hex
  have hex' : ∀ φ₀ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ₀ φ₁ := fun φ₀ hφ₀ => ⟨D φ₀ hφ₀, hDSB φ₀ hφ₀, hDA φ₀ hφ₀⟩
  let Dl : SB (Fin a × Fin (a + a') → Fv F v) →ₗ[ℂ] SB (Fin a × Fin (a + a') → Fv F v) :=
    { toFun := fun x => ⟨D x.1 x.2, hDSB x.1 x.2⟩
      map_add' := fun x y => by
        apply Subtype.ext
        have hl := GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) hex' x.2 y.2 (hDA x.1 x.2) (hDA y.1 y.2) 1 1
        simp only [one_smul] at hl
        exact GlobalTheory.ThK.LocalOps.acts_unique v _ (x + y).2 (hDA _ (x + y).2) hl
      map_smul' := fun c x => by
        apply Subtype.ext
        have hl := GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) hex' x.2 x.2 (hDA x.1 x.2) (hDA x.1 x.2) c 0
        simp only [zero_smul, add_zero] at hl
        exact GlobalTheory.ThK.LocalOps.acts_unique v _ (c • x).2 (hDA _ (c • x).2) hl }
  let π : SB (Fin a × Fin (a + a') → Fv F v) →ₗ[ℂ] Rf.Pi v := (Rf.p v).comp (SB _).subtype
  have hsurj : Function.Surjective π := by
    intro y
    have hy : y ∈ (SB _).map (Rf.p v) := (hM.fin.onto v).symm ▸ Submodule.mem_top
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hA0 : Acts (evFin F v) (om' (1, h)) (0 : (Fin a' × Fin (a + a') → Fv F v) → ℂ) 0 := by
    intro r _
    have e : tens (evFin F v) (0 : (Fin a' × Fin (a + a') → Fv F v) → ℂ) r = 0 := by
      funext y; simp [tens]
    rw [e, map_zero]
  have hD : ∀ x, π x = 0 → π (Dl x) = 0 := by
    intro x hx
    have e := hM.fin.equiv v h hh x.1 x.2 0 (zero_mem _) (D x.1 x.2) (hDSB x.1 x.2) 0 (zero_mem _) (hDA x.1 x.2) hA0
      (by rw [map_zero]; exact hx)
    rw [map_zero] at e
    exact e
  let L : Rf.Pi v →ₗ[ℂ] Rf.Pi v := GlobalTheory.ThK.RealUniq.induced π hsurj Dl hD
  let ψ : Fin m → (Fin a × Fin (a + a') → Fv F v) → ℂ := fun i => D (φ i v) ((hf i).2.1 v)
  have hL : ∀ i, L (Rf.p v (φ i v)) = Rf.p v (ψ i) := fun i =>
    GlobalTheory.ThK.RealUniq.induced_apply π hsurj Dl hD ⟨φ i v, (hf i).2.1 v⟩
  let φ₂ : Fin m → ∀ w : Pl F, (Fin a × Fin (a + a') → Fv F w) → ℂ := fun i => Function.update (φ i) v (ψ i)
  have hstd : ∀ i, ∀ᶠ w in Filter.cofinite, φ i w = Set.indicator {x | ∀ j, x j ∈ w.adicCompletionIntegers F} 1 := by
    intro i
    filter_upwards [hM.triple.geo.hM.std, T.finite_toSet.compl_mem_cofinite] with w hw hwT
    rw [(hf i).2.2 w hwT, hw]
  have hpure : ∀ i, om (1, h) (pure (f i) (φ i)) = pure (f i) (φ₂ i) := by
    intro i
    obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v (f i) (φ i) (hstd i)
    have e1 : pure (f i) (φ i) = tens (evFin F v) (φ i v) r := by
      rw [hrt, Function.update_eq_self]
    have hRest : Rest (evFin F v) (φ i v) r :=
      ⟨hr, by rw [← e1]; exact GlobalTheory.TensUniq.pure_mem_schA _ _ (hf i).2.1 (hstd i)⟩
    rw [e1, hDA _ _ r hRest, hrt]
  have hv : v ∈ insert v T := Finset.mem_insert_self _ _
  have hTS : T ⊆ insert v T := Finset.subset_insert _ _
  refine ⟨insert v T, hXT.trans hTS, m, f, φ₂, fun i => ⟨(hf i).1, fun w => ?_, fun w hw => ?_⟩, ?_, ?_⟩
  · by_cases hwv : w = v
    · subst hwv
      simp only [φ₂, Function.update_self]
      exact hDSB _ _
    · simp only [φ₂, Function.update_of_ne hwv]
      exact (hf i).2.1 w
  · rw [Finset.mem_insert, not_or] at hw
    simp only [φ₂, Function.update_of_ne hw.1]
    exact (hf i).2.2 w hw.2

  · rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hpure i
  · have hz' := GlobalTheory.PolMatchLin.transport Bs G Xc om om' R Rf hM.fin hXT hTS f φ
      (fun j : Fin 0 => j.elim0 : Fin 0 → SInf F (Fin a' × Fin (a + a')))
      (fun j : Fin 0 => j.elim0 : Fin 0 → ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ)
      (fun i => (hf i).2.2) (fun j => j.elim0) (by rw [hz]; simp)
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hz'
    let Lw : ∀ u : (insert v T : Finset (Pl F)), Rf.Pi u →ₗ[ℂ] Rf.Pi u :=
      Function.update (fun _ => LinearMap.id) ⟨v, hv⟩ L
    have key := congrArg (LinearMap.lTensor R.Pi (PiTensorProduct.map Lw)) hz'

    rw [map_zero, map_sum] at key
    rw [← key]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.lTensor_tmul, PiTensorProduct.map_tprod]
    congr 2
    funext u
    by_cases hu : u = ⟨v, hv⟩
    · subst hu
      simp only [Lw, φ₂, Function.update_self]
      exact (hL i).symm
    · have hu' : u.1 ≠ v := fun e => hu (Subtype.ext e)
      simp only [Lw, φ₂, Function.update_of_ne hu, Function.update_of_ne hu', LinearMap.id_apply]

end GlobalTheory.PolKerFin
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.SmallGauss

open GlobalTheory.SmallDat GlobalTheory.TripleCplxAt
open scoped ComplexConjugate

theorem pure_vac_inj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {Y : Spc F E d} {M : Model σ X Y} {ψ : AddChar (AF F) ℂ} (hG : M.IsGood ψ)
    {f f' : SInf F (Fin n × Fin d)} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' M.vac) : f = f' := by
  classical
  choose ξ hξ using fun v => Function.ne_iff.1 (hG.vac v).2.1
  have hS := Filter.eventually_cofinite.1 hG.std
  let y : Fin n × Fin d → Af F := fun k => ∑ v ∈ hS.toFinset, singleFin v (ξ v k)
  have hy : finPartFn M.vac y ≠ 0 := by
    refine finprod_induction (· ≠ (0 : ℂ)) one_ne_zero (fun _ _ => mul_ne_zero) fun v => ?_
    by_cases hv : v ∈ hS.toFinset
    · have : (fun k => evalV F v (y k)) = ξ v := funext fun k => by

        rw [map_sum, Finset.sum_eq_single_of_mem v hv fun v' _ h => evalV_singleFin_ne h.symm _, evalV_singleFin_self]
      rw [this]
      exact hξ v
    · have : (fun k => evalV F v (y k)) = 0 := funext fun k => by

        rw [map_sum]
        exact Finset.sum_eq_zero fun v' h => evalV_singleFin_ne (fun e : v = v' => hv (e ▸ h)) _
      rw [this, of_not_not (mt hS.mem_toFinset.2 hv), Set.indicator_of_mem (by exact fun _ => zero_mem _)]
      exact one_ne_zero
  ext z
  have := congrFun h fun k => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace _).symm (z k)) (y k)
  simp only [pure_eq, pureA, pairA, RingEquiv.apply_symm_apply] at this
  exact mul_right_cancel₀ hy this

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

theorem compAt_mapA (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (t : T) (e : Num G i j) (u : PtS G i j) :
    compAt θ τ (mapA t e u) = ((compAt θ τ u).submatrix id fun k => e (.inl k))ᵀ * gramAt D (spW₁ G i j) τ := by
  show compAt θ τ (HMul.hMul (colV e u)ᵀ ((spW₁ G i j).gram.map (incA D))) = _
  rw [compAt_mul', compAt_inc θ hθ]
  rfl

theorem compAt_mapB (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (e : Num G i j) (u : PtS G i j) :
    compAt θ τ (mapB e u) = -(((compAt θ τ u).submatrix id fun k => e (.inr k)).map conj * gramAt D (spV₁ G i j) τ) := by
  show compAt θ τ (-HMul.hMul ((u.submatrix id fun k => e (.inr k)).map (cA D)) ((spV₁ G i j).gram.map (incA D))) = _
  rw [compAt_neg', compAt_mul', compAt_inc θ hθ, compAt_conj θ hθ]
  rfl


open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (blk) in
theorem cplx_pairS {W : G.Weil} {M : Vol G} {t : T} {i j : Fin D.R.m} {e : Num G i j} {Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E}
    {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j} {X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} (h : IsTripleOf W M t i j e Bs Γ X) (u u' : PtS G i j)
    (hu : ∀ w, u'.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) =
      Complex.I • (Γ.V'.θ w * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) * (Γ.W.θ w)ᵀ)) (τ : D.what₂.Tau) :
    compAt W.θ τ (mapA t e u') = cplxO (W.cart (.grid i j) τ) (W.cart (.grid i (j + 1)) τ) (compAt W.θ τ (mapA t e u)) ∧
    compAt W.θ τ (mapB e u') = cplxO (-W.cart (.grid (i + 1) j) τ) (W.cart (.grid i j) τ) (compAt W.θ τ (mapB e u)) := by
  obtain ⟨w, hpi, hV, hWW⟩ : ∃ w, (∀ y, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w) y = conj (W.θ τ (infPart D y))) ∧
      Γ.V'.θ w = -W.cart (.grid i j) τ ∧
      Γ.W.θ w = (blk e (W.cart (.grid i (j + 1)) τ) (W.cart (.grid (i + 1) j) τ)).map conj := by
    obtain ⟨w, hw⟩ : ∃ w : InfinitePlace D.host.F, w = InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)) :=
      ⟨_, rfl⟩
    obtain ⟨τ', hemb, -, hV, hWW⟩ := h.cart w
    have h1 : (Bs.emb w).1.comp (algebraMap D.host.F D.host.E) = w.embedding := (Bs.emb w).2
    have h2 : (tauE D τ').comp (algebraMap D.host.F D.host.E) = NumberField.ComplexEmbedding.conjugate w.embedding := by
      ext x
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq, ← h1]
      simp [hemb]
    have hh : ((starRingEnd ℂ).comp (tauE D τ')).comp (algebraMap D.host.F D.host.E) = w.embedding := by
      rw [← h1]; ext x; simp [hemb]
    have hb : Bs.emb w = ⟨_, hh⟩ := Subtype.ext (RingHom.ext hemb)
    have hτ : τ' = τ := (GlobalTheory.CMTypePlaces.places_bijective D).1 (by
      show InfinitePlace.mk ((tauE D τ').comp _) = InfinitePlace.mk ((tauE D τ).comp _)
      rw [h2, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding, hw])
    subst hτ
    exact ⟨w, fun y => by rw [hb]; exact GlobalTheory.ConjInfExp.piInf_eq W.θ W.θ_is _ w hh y, hV, hWW⟩
  have hmap : ∀ v : PtS G i j, v.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) = (compAt W.θ τ v).map conj :=
    fun v => Matrix.ext fun a b => hpi _
  have hX := hu w
  rw [hmap, hmap, hV, hWW] at hX
  have cW₁ := W.cart_is (.grid (i : ℕ) (j : ℕ)) ⟨by omega, by omega⟩ τ
  have cV₁ := W.cart_is (.grid ((i : ℕ) + 1) (j : ℕ)) ⟨by omega, by omega⟩ τ
  refine ⟨?_, ?_⟩
  · have hs : (-W.cart (.grid i j) τ)ᴴ * (-gramAt D (spW₁ G i j) τ) =
        (-gramAt D (spW₁ G i j) τ) * (-W.cart (.grid i j) τ) := by
      rw [Matrix.conjTranspose_neg, neg_mul_neg, neg_mul_neg]
      exact cartan_comm cW₁
    have := algV e _ _ _ _ _ _ hX hs
    simp only [neg_neg] at this
    rw [compAt_mapA W.θ W.θ_is, compAt_mapA W.θ W.θ_is]
    exact this
  · have := algW e _ _ _ _ _ _ hX (cartan_comm cV₁)
    rw [compAt_mapB W.θ W.θ_is, compAt_mapB W.θ W.θ_is, this]
    show _ = Complex.I • (_ * _ * _)
    simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]

theorem isGauss : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (t : T) (i j : Fin D.R.m) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X → IsTriple Bs Γ X om om' →
    ∀ (f₁ : GlobalTheory.SmallDat.HomA G t i j → ℂ) (f₂ : GlobalTheory.SmallDat.HomB G i j → ℂ), W.IsVac (.mu t i j) f₁ → W.IsVac (.chi i j) f₂ →
    ∀ (c : ℂ) (f₀ : SInf D.host.F (GlobalTheory.SmallDat.IxS G i j)),
      GlobalTheory.SmallDat.thetaS Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M'.vac) = c • GlobalTheory.SmallDat.boxS t e f₁ f₂ → Γ.M'.IsGauss Bs.ψ Bs.emb f₀ := by
  intro D T L sc G W M t i j e Bs Γ X om om' h hT f₁ f₂ h₁ h₂ c f₀ hb
  obtain ⟨-, hinj, -⟩ := GlobalTheory.T.smallModel_thetaTransform_injective_products W M t i j e Bs Γ X om om' h hT
  have hG : Γ.M'.IsGood W.ψ := h.ψ ▸ hT.geo.hM'
  have hm := fun f => (isFinPart_vac hG ∅).fam.mem hG f
  rw [h.ψ]
  refine ⟨1, fun u u' _ _ hJ f f' hf hf' => pure_vac_inj hG (hinj _ (hm _) _ (hm _) (funext fun x => ?_))⟩
  have hc := cplx_pairS h u u' fun w => by simpa using hJ w
  obtain ⟨a, ha, ha'⟩ := GlobalTheory.T.fockVacuum_thetaFunction_derivative_complex_structure W.ψ W.θ _ _ _ _ f₁ W.ψ_std W.θ_is h₁.2.theta h₁.2.fock _ _ (fun τ => (hc τ).1)
    (mapA t e x)
  obtain ⟨b, hb₁, hb'⟩ := GlobalTheory.T.fockVacuum_thetaFunction_derivative_complex_structure W.ψ W.θ _ _ _ _ f₂ W.ψ_std W.θ_is h₂.2.theta h₂.2.fock _ _ (fun τ => (hc τ).2)
    (mapB e x)
  have hr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evI D.host.F) f₀ fun y : IxS G i j → AF D.host.F => finPartFn Γ.M'.vac fun k => (y k).2 := by
    refine ⟨fun y z hz => ?_, hm f₀⟩
    refine congrArg (finPartFn Γ.M'.vac) (funext fun k => ?_)
    have : (pairA D.host.F 0 1 * z k).2 = 0 :=
      congrArg (fun q => (q k).2) (hz (pairA D.host.F 0 1) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace _)))
    exact (add_eq_left (a := (y k).2)).2 ((one_mul (z k).2).symm.trans this)
  have key : ∀ u (g : SInf D.host.F (IxS G i j)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (evI D.host.F) (Γ.M'.heisLine W.ψ u) f₀ g →
      HasDerivAt (fun s : ℝ => c * (heisO W.ψ _ _ (realAd D.host.F s • mapA t e u) f₁ (mapA t e x) *
        heisO W.ψ _ _ (realAd D.host.F s • mapB e u) f₂ (mapB e x))) (thetaS Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g Γ.M'.vac) x) 0 := by
    intro u g hg
    have := GlobalTheory.T.hasDerivAt_thetaTransform_heisenberg_real_line Γ.M'.co W.ψ inferInstance W.ψ_std.1 u _ (hm f₀) _ (hm g) (hg _ hr) x
    convert this using 2 with s
    refine Eq.trans ?_ (congrFun (thetaS_rho Γ W.ψ _ (realAd D.host.F s • u)) x).symm
    rw [hb, ← mapA_smul, ← mapB_smul]
    refine Eq.trans (congrArg (c * ·) (congrFun (heisS_box t e Γ h.JW₁ h.JWW W.ψ _ f₁ f₂) x).symm) ?_
    simp only [heisS, Pi.smul_apply, smul_eq_mul]
    ring
  have e1 := (key u f hf).unique ((ha.mul hb₁).const_mul c)
  have e2 := (key u' f' hf').unique ((ha'.mul hb').const_mul c)
  have e3 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Complex.I • f) Γ.M'.vac = Complex.I • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f Γ.M'.vac :=
    funext fun _ => mul_assoc _ _ _
  have e4 : realAd D.host.F 0 = 0 := by
    unfold realAd
    rw [map_zero (algebraMap ℝ _), map_zero (RingEquiv.symm _)]
    rfl
  have e5 : thetaS Γ W.ψ (Complex.I • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f Γ.M'.vac) x =
      Complex.I * thetaS Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f Γ.M'.vac) x := thetaS_smul _ _ _ _ _
  rw [e3, e5, e1, e2]
  simp only [e4, zero_smul]
  ring

end GlobalTheory.SmallGauss
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
noncomputable section

namespace GlobalTheory.TopLevelInv

variable {D : D7}

theorem infPart_of_isIdemSum {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) : infPart D e = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have hs := map_sum (infPart D).toAddMonoidHom es P
  change (infPart D).toAddMonoidHom _ = 0
  rw [hs]
  exact Finset.sum_eq_zero fun PP hPP =>
    (GlobalTheory.IdemSupport.delta_of_isIdemAt (GlobalTheory.StdFrames.comp_toAd D) (hes PP hPP)).1


open Classical in
theorem cpt_of_isIdemSum {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) (Q : Pl D.host.E) :
    GlobalTheory.StdFrames.cpt Q (toEAf D e) = if Q ∈ P then 1 else 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have hs := map_sum ((GlobalTheory.StdFrames.cpt Q).comp (toEAf D)).toAddMonoidHom es P
  change ((GlobalTheory.StdFrames.cpt Q).comp (toEAf D)).toAddMonoidHom _ = _
  rw [hs]
  have h : ∀ PP ∈ P, GlobalTheory.StdFrames.cpt Q (toEAf D (es PP)) = if PP = Q then 1 else 0 := fun PP hPP => by
    by_cases hQ : PP = Q
    · subst hQ; rw [if_pos rfl]; exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes PP hPP)).1
    · rw [if_neg hQ]; exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes PP hPP)).2 Q (Ne.symm hQ)
  calc _ = ∑ PP ∈ P, (if PP = Q then (1 : Q.adicCompletion D.host.E) else 0) := Finset.sum_congr rfl h
    _ = _ := by rw [Finset.sum_ite_eq']

theorem cpt_one_of_isIdemSum {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {Q : Pl D.host.E} (hQ : Q ∈ P) :
    GlobalTheory.StdFrames.cpt Q (toEAf D e) = 1 := by
  classical
  rw [cpt_of_isIdemSum he, if_pos hQ]

theorem cpt_zero_of_isIdemSum {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {Q : Pl D.host.E} (hQ : Q ∉ P) :
    GlobalTheory.StdFrames.cpt Q (toEAf D e) = 0 := by
  classical
  rw [cpt_of_isIdemSum he, if_neg hQ]

theorem map_unitMix_of_zero {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (e x : R) (h : φ e = 0) :
    φ (e * x + (1 - e)) = 1 := by
  rw [map_add (f := _), map_mul, map_sub, map_one, h]; ring


theorem detAt_cutPart_parts {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) (V : HSp D) (g : GA D V) :
    infPart D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem V (cutPart (e + cA D e) V g) : AE D) = 1 ∧
    (∀ Q ∈ P, GlobalTheory.StdFrames.cpt Q (toEAf D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem V
      (cutPart (e + cA D e) V g) : AE D)) = ((Formalism.L2.Theta.mt V g).map fun z => GlobalTheory.StdFrames.cpt Q (toEAf D z)).det) ∧
    ∀ Q ∉ P, GlobalTheory.StdFrames.cpt Q (toEAf D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem V
      (cutPart (e + cA D e) V g) : AE D)) = 1 := by
  have hee : e * e = e := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem
  have hc : e * cA D e = 0 := he.2
  have hf := idem_conj_sum hee hc
  have hval : (GlobalTheory.VecInv.detAt e hee V (cutPart (e + cA D e) V g) : AE D) =
      e * (Formalism.L2.Theta.mt V (cutPart (e + cA D e) V g)).det + (1 - e) := rfl
  rw [hval]
  have hinf := infPart_of_isIdemSum he
  refine ⟨?_, fun Q hQ => ?_, fun Q hQ => ?_⟩
  · rw [RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hinf, zero_mul, zero_add, sub_zero]
  · let φ : AE D →+* Q.adicCompletion D.host.E := (GlobalTheory.StdFrames.cpt Q).comp (toEAf D)
    have h1 : φ e = 1 := cpt_one_of_isIdemSum he hQ
    have h2 : φ (cA D e) = 0 := by
      have := congrArg φ hc
      rwa [RingHom.map_mul, RingHom.map_zero, h1, one_mul] at this
    have h3 : φ (e + cA D e) = 1 := by rw [RingHom.map_add (f := _), h1, h2, add_zero]
    change φ _ = ((Formalism.L2.Theta.mt V g).map φ).det
    rw [RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_sub, RingHom.map_one, h1, one_mul, sub_self, add_zero,
      RingHom.map_det, mt_cutPart hf.1 hf.2]
    congr 1
    refine Matrix.ext fun i j => ?_
    change φ ((e + cA D e) * Formalism.L2.Theta.mt V g i j + (1 - (e + cA D e)) * (1 : Matrix _ _ (AE D)) i j) = φ (Formalism.L2.Theta.mt V g i j)
    rw [RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, h3, one_mul, sub_self,
      zero_mul, add_zero]
  · let φ : AE D →+* Q.adicCompletion D.host.E := (GlobalTheory.StdFrames.cpt Q).comp (toEAf D)
    have h1 : φ e = 0 := cpt_zero_of_isIdemSum he hQ
    change φ _ = 1
    exact map_unitMix_of_zero φ e _ h1

end GlobalTheory.TopLevelInv

end
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.IndefR.NX (ExpSet CoefLat)
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Tow

namespace GlobalTheory.Tow

theorem idemAt_orth {D : D7} {P Q : Formalism.L2.DIV.Pl D.host.E} {a b : AE D} (ha : Formalism.L2.NTheta.IsIdemAt a P)
    (hb : Formalism.L2.NTheta.IsIdemAt b Q) (h : P ≠ Q) : a * b = 0 := by

  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have ha0 := GlobalTheory.PlaceModelSum.infPart_split ha.1
  have hda := (GlobalTheory.IdemSupport.tie_iff hΦ ha.1.1 ha0 P).mp ha.2
  have hdb := (GlobalTheory.IdemSupport.tie_iff hΦ hb.1.1 (GlobalTheory.PlaceModelSum.infPart_split hb.1) Q).mp hb.2
  apply hΦ.ext'
  · rw [map_mul, ha0, zero_mul, map_zero]
  · intro R
    rw [GlobalTheory.IdemSupport.ev_mul, GlobalTheory.IdemSupport.ev_zero]
    by_cases hR : R = P
    · rw [hR, hdb.2.2 P h, mul_zero]
    · rw [hda.2.2 R hR, zero_mul]

theorem idemAt_unique {D : D7} {P : Formalism.L2.DIV.Pl D.host.E} {a b : AE D} (ha : Formalism.L2.NTheta.IsIdemAt a P)
    (hb : Formalism.L2.NTheta.IsIdemAt b P) : a = b := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  exact GlobalTheory.IdemSupport.delta_unique hΦ
    ((GlobalTheory.IdemSupport.tie_iff hΦ ha.1.1 (GlobalTheory.PlaceModelSum.infPart_split ha.1) P).mp ha.2)
    ((GlobalTheory.IdemSupport.tie_iff hΦ hb.1.1 (GlobalTheory.PlaceModelSum.infPart_split hb.1) P).mp hb.2)

theorem idemSum_mul_of_subset {D : D7} {e e₂ : AE D} {P P₂ : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (h : IsIdemSum e P) (h₂ : IsIdemSum e₂ P₂) (hP : P ⊆ P₂) : e₂ * e = e := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  obtain ⟨⟨fs, hfs, rfl⟩, -⟩ := h₂
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun R hR => ?_

  rw [Finset.sum_mul, Finset.sum_eq_single_of_mem R (hP hR)]
  · rw [idemAt_unique (hfs R (hP hR)) (hes R hR)]
    exact (hes R hR).1.1
  · intro Q hQ hQR
    exact idemAt_orth (hfs Q hQ) (hes R hR) hQR

end GlobalTheory.Tow
end
