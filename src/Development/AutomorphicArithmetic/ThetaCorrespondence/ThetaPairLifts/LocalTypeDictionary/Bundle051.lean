module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1381
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2030
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaPairCompactLineAction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle222
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle175
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle348
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle047
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle045
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle011
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedFiniteMapsRestriction

@[expose] public section

section

section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
noncomputable section
namespace GlobalTheory.ReBase
section Real
open scoped Matrix
open GlobalTheory.RealActs GlobalTheory.ThK.RealUniq
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}
theorem howe_supremum_projection (hKP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {n d r s r' s' : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {χY χW : Chr F E}
    {o : Rep σ Y W} (h : IsPair B M χY χW o r s r' s') :
    ∀ N N', GlobalTheory.Published.ThetaSubInf M B.ψ B.emb o N → GlobalTheory.Published.ThetaSubInf M B.ψ B.emb o N' → N ≠ M.Pol B.ψ B.emb →
      N' ≠ M.Pol B.ψ B.emb → N ⊔ N' ≠ M.Pol B.ψ B.emb := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hY : Y.J.det ≠ 0 := fun h0 => det_ne_zero_of_sig (h.herm.sig w) (by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero])
  have hW : W.J.det ≠ 0 := fun h0 => det_ne_zero_of_sig (h.skew.sig w) (by
    rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero])
  exact (hKP.howeDualityReal F E σ h.base.cm n d Y W M B.ψ χY χW o h.base.std h.herm.herm hY h.skew.skew hW h.resX h.resW
    h.hX h.hW h.weil B.emb h.herm.cartan h.skew.cartan).2
theorem real_maps_unique : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
    ∀ R₃ : RealMaps F a a', IsRealMaps B G om om' R₃ → ∃ (ψ : R.Pi ≃ₗ[ℂ] R₃.Pi) (l : ℂ), l ≠ 0 ∧
      (∀ f ∈ G.M.Pol B.ψ B.emb, R₃.p f = ψ (R.p f)) ∧ ∀ f ∈ G.M'.Pol B.ψ B.emb, R₃.p' f = l • ψ (R.p' f) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM R₃ hR₃
  have hR := hM.real
  have hPV := isPair_V hM.triple
  have hPV' := isPair_V' hM.triple
  have actV := _root_.GlobalTheory.T.dualPair_preserves_polarization hKP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hPV
  have actV' := _root_.GlobalTheory.T.dualPair_preserves_polarization hKP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hPV'
  have ks_p : ∀ R' : RealMaps F a a', IsRealMaps B G om om' R' → KerStab B G.M om R'.p := fun R' h =>
    ⟨fun γ hγ f hf f₁ h1 h0 => by
      have := h.lie γ hγ f hf 0 (zero_mem _) f₁ 0 h1 (actsD_zero _) (by rw [h0, map_zero])
      rwa [map_zero] at this,
     fun k hk f hf f₁ h1 h0 => by
      have := h.cpt k hk f hf 0 (zero_mem _) f₁ 0 h1 (acts_zero _) (by rw [h0, map_zero])
      rwa [map_zero] at this⟩
  have ks_p' : ∀ R' : RealMaps F a a', IsRealMaps B G om om' R' → KerStab B G.M' om' R'.p' := fun R' h =>
    ⟨fun γ hγ f hf f₁ h1 h0 => by
      have := h.lie γ hγ 0 (zero_mem _) f hf 0 f₁ (actsD_zero _) h1 (by rw [h0, map_zero])
      rw [map_zero] at this; exact this.symm,
     fun k hk f hf f₁ h1 h0 => by
      have := h.cpt k hk 0 (zero_mem _) f hf 0 f₁ (acts_zero _) h1 (by rw [h0, map_zero])
      rw [map_zero] at this; exact this.symm⟩
  have onto' : ∀ R' : RealMaps F a a', IsRealMaps B G om om' R' → ∀ y, ∃ f' ∈ G.M'.Pol B.ψ B.emb, R'.p' f' = y :=
    fun R' h y => by
      have : y ∈ (G.M'.Pol B.ψ B.emb).map R'.p' := h.quot'.onto ▸ Submodule.mem_top
      exact Submodule.mem_map.1 this
  have onto : ∀ R' : RealMaps F a a', IsRealMaps B G om om' R' → ∀ y, ∃ f ∈ G.M.Pol B.ψ B.emb, R'.p f = y :=
    fun R' h y => by
      have : y ∈ (G.M.Pol B.ψ B.emb).map R'.p := h.quot.onto ▸ Submodule.mem_top
      exact Submodule.mem_map.1 this
  have irr_p' : ∀ R' : RealMaps F a a', IsRealMaps B G om om' R' → Irred B G.M' om' R'.p' := fun R' h N h1 h2 => by
    apply h.irred N
    · intro γ hγ f hf f₁ hf₁ hN
      obtain ⟨f', hf', e⟩ := onto' R' h (R'.p f)
      obtain ⟨D, -, hDi⟩ := actV'.2.2.1 γ hγ
      have h1' := (hDi f' hf' (D f')).2 rfl
      rw [h.lie γ hγ f hf f' hf' f₁ (D f') hf₁ h1' e.symm]
      exact h1 γ hγ f' hf' (D f') h1' (e ▸ hN)
    · intro k hk f hf f₁ hf₁ hN
      obtain ⟨f', hf', e⟩ := onto' R' h (R'.p f)
      obtain ⟨D, -, hDi⟩ := actV'.2.2.2 k hk
      have h1' := (hDi f' hf' (D f')).2 rfl
      rw [h.cpt k hk f hf f' hf' f₁ (D f') hf₁ h1' e.symm]
      exact h2 k hk f' hf' (D f') h1' (e ▸ hN)
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_equiv_howeDuality_realPlaces F E σ B _ _ _ _ G.M om _ _ R.p R₃.p actV (_root_.GlobalTheory.ReBase.howe_supremum_projection hKP hPV) hR.quot hR₃.quot hR.nontriv
    hR₃.nontriv (ks_p R hR) (ks_p R₃ hR₃) hR.irred hR₃.irred
  obtain ⟨ψ₁, hψ₁⟩ := GlobalTheory.T.exists_equiv_howeDuality_realPlaces F E σ B _ _ _ _ G.M' om' _ _ R.p' R₃.p' actV' (_root_.GlobalTheory.ReBase.howe_supremum_projection hKP hPV') hR.quot' hR₃.quot'
    hR.nontriv hR₃.nontriv (ks_p' R hR) (ks_p' R₃ hR₃) (irr_p' R hR) (irr_p' R₃ hR₃)
  choose DL hDLm hDLi using actV.2.2.1
  choose DK hDKm hDKi using actV.2.2.2
  choose DL' hDLm' hDLi' using actV'.2.2.1
  choose DK' hDKm' hDKi' using actV'.2.2.2
  let ι : Type := {γ // γ ∈ Lines σ G.W} ⊕ {k // k ∈ KInf σ G.W B.emb}
  let D : ι → SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')) :=
    Sum.elim (fun γ => DL γ.1 γ.2) (fun k => DK k.1 k.2)
  let D' : ι → SInf F (Fin a' × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a' × Fin (a + a')) :=
    Sum.elim (fun γ => DL' γ.1 γ.2) (fun k => DK' k.1 k.2)
  have Dm : ∀ i, ∀ f ∈ G.M.Pol B.ψ B.emb, D i f ∈ G.M.Pol B.ψ B.emb := by
    rintro (γ | k) f hf
    exacts [hDLm _ _ f hf, hDKm _ _ f hf]
  have Dm' : ∀ i, ∀ f ∈ G.M'.Pol B.ψ B.emb, D' i f ∈ G.M'.Pol B.ψ B.emb := by
    rintro (γ | k) f hf
    exacts [hDLm' _ _ f hf, hDKm' _ _ f hf]
  have joint : ∀ R' : RealMaps F a a', IsRealMaps B G om om' R' → ∀ i, ∀ f ∈ G.M.Pol B.ψ B.emb,
      ∀ f' ∈ G.M'.Pol B.ψ B.emb, R'.p f = R'.p' f' → R'.p (D i f) = R'.p' (D' i f') := by
    rintro R' h (γ | k) f hf f' hf' e
    · exact h.lie γ.1 γ.2 f hf f' hf' _ _ ((hDLi _ _ f hf _).2 rfl) ((hDLi' _ _ f' hf' _).2 rfl) e
    · exact h.cpt k.1 k.2 f hf f' hf' _ _ ((hDKi _ _ f hf _).2 rfl) ((hDKi' _ _ f' hf' _).2 rfl) e
  have ker0 : ∀ i, ∀ f ∈ G.M.Pol B.ψ B.emb, R.p f = 0 → R.p (D i f) = 0 := by
    rintro (γ | k) f hf h0
    · exact (ks_p R hR).1 γ.1 γ.2 f hf _ ((hDLi _ _ f hf _).2 rfl) h0
    · exact (ks_p R hR).2 k.1 k.2 f hf _ ((hDKi _ _ f hf _).2 rfl) h0
  let π : G.M.Pol B.ψ B.emb →ₗ[ℂ] R.Pi := R.p ∘ₗ (G.M.Pol B.ψ B.emb).subtype
  have hπ : Function.Surjective π := fun y => by
    obtain ⟨f, hf, e⟩ := onto R hR y
    exact ⟨⟨f, hf⟩, e⟩
  let ρ : ι → Module.End ℂ R.Pi := fun i =>
    induced π hπ ((D i).restrict (Dm i)) (fun u hu => ker0 i u.1 u.2 hu)
  have hρ : ∀ i, ∀ f (hf : f ∈ G.M.Pol B.ψ B.emb), ρ i (R.p f) = R.p (D i f) := fun i f hf =>
    induced_apply π hπ _ _ ⟨f, hf⟩
  have irrρ : ∀ N : Submodule ℂ R.Pi, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤ := fun N hN => by
    apply hR.irred N
    · intro γ hγ f hf f₁ h1 hx
      rw [(hDLi γ hγ f hf f₁).1 h1]
      have := hN (Sum.inl ⟨γ, hγ⟩) _ hx
      rwa [hρ _ f hf] at this
    · intro k hk f hf f₁ h1 hx
      rw [(hDKi k hk f hf f₁).1 h1]
      have := hN (Sum.inr ⟨k, hk⟩) _ hx
      rwa [hρ _ f hf] at this
  let T : Module.End ℂ R.Pi := ψ.symm.toLinearMap ∘ₗ ψ₁.toLinearMap
  have comm : ∀ i, T * ρ i = ρ i * T := fun i => by
    refine LinearMap.ext fun x => ?_
    obtain ⟨f', hf', rfl⟩ := onto' R hR x
    obtain ⟨f, hf, e⟩ := onto R hR (R.p' f')
    obtain ⟨g, hg, eg⟩ := onto R₃ hR₃ (R₃.p' f')
    have j1 := joint R hR i f hf f' hf' e
    have j3 := joint R₃ hR₃ i g hg f' hf' eg
    have lhs : T (ρ i (R.p' f')) = R.p (D i g) := by
      calc T (ρ i (R.p' f')) = ψ.symm (ψ₁ (R.p' (D' i f'))) := by rw [← e, hρ i f hf, j1]; rfl
      _ = ψ.symm (R₃.p' (D' i f')) := by rw [← hψ₁ _ (Dm' i f' hf')]
      _ = R.p (D i g) := by rw [← j3, hψ _ (Dm i g hg), LinearEquiv.symm_apply_apply]
    have rhs : ρ i (T (R.p' f')) = R.p (D i g) := by
      calc ρ i (T (R.p' f')) = ρ i (ψ.symm (R₃.p' f')) := by
            show ρ i (ψ.symm (ψ₁ (R.p' f'))) = _
            rw [← hψ₁ f' hf']
      _ = ρ i (R.p g) := by rw [← eg, hψ g hg, LinearEquiv.symm_apply_apply]
      _ = R.p (D i g) := hρ i g hg
    rw [Module.End.mul_apply, Module.End.mul_apply, lhs, rhs]
  have hrank : Module.rank ℂ R.Pi ≤ Cardinal.aleph0 :=
    (LinearMap.rank_le_of_surjective π hπ).trans (_root_.GlobalTheory.T.polarization_rank_le_dim hKP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hPV)
  obtain ⟨c, hc⟩ := GlobalTheory.T.eq_smul_one_of_commute_irreducible_of_countable_rank R.Pi ι ρ T hR.nontriv hrank irrρ comm
  have hT : ∀ x, T x = c • x := fun x => by rw [hc]; rfl
  refine ⟨ψ, c, ?_, hψ, fun f hf => ?_⟩
  · rintro rfl
    haveI := hR.nontriv
    obtain ⟨x, hx⟩ := exists_ne (0 : R.Pi)
    have h0 : ψ.symm (ψ₁ x) = 0 := by rw [← zero_smul ℂ x, ← hT x]; rfl
    exact hx (ψ₁.injective (ψ.symm.injective (h0.trans (map_zero _).symm) |>.trans (map_zero _).symm))
  · rw [hψ₁ f hf]
    calc ψ₁ (R.p' f) = ψ (T (R.p' f)) := by
          show _ = ψ (ψ.symm (ψ₁ (R.p' f)))
          rw [LinearEquiv.apply_symm_apply]
    _ = c • ψ (R.p' f) := by rw [hT, map_smul]
end Real
section Fin
open GlobalTheory.FinUniq
end Fin
end GlobalTheory.ReBase
end
end
end

section

section
open NumberField IsDedekindDomain
noncomputable section
namespace GlobalTheory.KExpLineW
section Abstract
variable {α : Type}
end Abstract
end GlobalTheory.KExpLineW
namespace GlobalTheory.KExpLineW
section Orbit
variable {α : Type}
end Orbit
end GlobalTheory.KExpLineW
namespace GlobalTheory.KExpLineW
open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
end GlobalTheory.KExpLineW
namespace GlobalTheory.KExpLineW
open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
theorem KExpLine_stabilizes_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W, (∀ t, γ t ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W B.emb) →
    ∀ N : Submodule ℂ (GlobalTheory.ThK.Fn F n d),
      (∀ Ψ ∈ N, ∀ Ψ₁ ∈ GlobalTheory.ThK.PolData B M,
        (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Ψ x) (Ψ₁ x) 0) → Ψ₁ ∈ N) →
      ∀ Φ ∈ N, Φ ∈ GlobalTheory.ThK.PolData B M → om (1, γ (Multiplicative.ofAdd (1 : ℝ))) Φ ∈ N := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP γ hγL hγK N hN Φ hΦN hΦ
  obtain ⟨-, -, hDer, hOp⟩ := _root_.GlobalTheory.T.dualPair_preserves_polarization hPr F E σ B n d X W M χX χW om r s r' s' hP
  obtain ⟨Dg, hDgP, hDg⟩ := hDer γ hγL
  choose D hDP hD using fun t : ℝ => hOp (γ (Multiplicative.ofAdd t)) (hγK _)
  let U : Multiplicative ℝ →* Module.End ℂ (Fn F n d) := om.comp ((MonoidHom.inr (UA σ X.J) (UA σ W.J)).comp γ)
  have hdiff : ∀ Ψ ∈ PolData B M, ∀ x (t : ℝ),
      DifferentiableAt ℝ (fun s : ℝ => U (Multiplicative.ofAdd s) Ψ x) t := by
    intro Ψ hΨ x
    induction hΨ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, φ, hφ, hvac, rfl⟩ := hy
      intro t
      have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
        (hvac.and hP.good.std).mono fun _ h => h.1.trans h.2
      have hpt : ∀ u : ℝ, U (Multiplicative.ofAdd u) (pure f φ) = pure (D u f) φ := fun u =>
        map_pure M B.ψ hP.good _ f (D u f) ((hD u f hf (D u f)).2 rfl) φ hφ hvac
      have hshift : ∀ s', U (Multiplicative.ofAdd (s' + t)) (pure f φ) =
          U (Multiplicative.ofAdd s') (pure (D t f) φ) := by
        intro s'
        rw [ofAdd_add, map_mul, Module.End.mul_apply, hpt t]
      have h0 := (hDg (D t f) (hDP t f hf) (Dg (D t f))).2 rfl _
        (GlobalTheory.ThK.EvUniqInf.rest_pure (D t f) φ hφ hstd) x
      have h0' : DifferentiableAt ℝ (fun s' : ℝ => U (Multiplicative.ofAdd s') (pure (D t f) φ) x) 0 :=
        h0.differentiableAt
      have e : (fun s : ℝ => U (Multiplicative.ofAdd s) (pure f φ) x) =
          (fun s' : ℝ => U (Multiplicative.ofAdd s') (pure (D t f) φ) x) ∘ fun s => s - t := by
        funext s
        show _ = U (Multiplicative.ofAdd (s - t)) (pure (D t f) φ) x
        rw [← hshift, sub_add_cancel]
      have h4 : DifferentiableAt ℝ (fun s' : ℝ => U (Multiplicative.ofAdd s') (pure (D t f) φ) x)
          ((fun s : ℝ => s - t) t) := by
        simp only [sub_self]
        exact h0'
      rw [e]
      exact DifferentiableAt.comp (f := fun s : ℝ => s - t) t h4 (differentiableAt_id.sub_const t)
    | zero =>
      intro t
      simp only [map_zero, Pi.zero_apply]
      exact differentiableAt_const _
    | add y z _ _ hy hz =>
      intro t
      simp only [map_add (f := _), Pi.add_apply]
      exact (hy t).add (hz t)
    | smul a y _ hy =>
      intro t
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      exact (hy t).const_mul a
  obtain ⟨C, hCfin, hCP, hCk⟩ := polData_kfin F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  haveI := hCfin
  exact orbit_mem U (PolData B M) N C hCP (fun Ψ h Ψ₁ h₁ hd => hN Ψ h Ψ₁ h₁ hd) Φ hΦN
    (fun t => hCk _ (hγK _)) (hdiff Φ hΦ) 1
end GlobalTheory.KExpLineW
end
end

section
open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.stabilizer_of_K_exponential_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W, (∀ t, γ t ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W B.emb) →
    ∀ N : Submodule ℂ (GlobalTheory.ThK.Fn F n d),
      (∀ Ψ ∈ N, ∀ Ψ₁ ∈ GlobalTheory.ThK.PolData B M,
        (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Ψ x) (Ψ₁ x) 0) → Ψ₁ ∈ N) →
      ∀ Φ ∈ N, Φ ∈ GlobalTheory.ThK.PolData B M → om (1, γ (Multiplicative.ofAdd (1 : ℝ))) Φ ∈ N := by
  first | exact @_root_.GlobalTheory.KExpLineW.KExpLine_stabilizes_line | exact _root_.GlobalTheory.KExpLineW.KExpLine_stabilizes_line | (intros; apply _root_.GlobalTheory.KExpLineW.KExpLine_stabilizes_line <;> assumption)
end
end

section

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
namespace GlobalTheory.FockVacStab
theorem isGaussian_of_fock_vacuum_stabilizer_acts : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ X B.emb, ∀ f₀ : SInf F (Fin n × Fin d),
    M.IsGauss B.ψ B.emb f₀ → ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (k, 1)) f₀ f₁ → M.IsGauss B.ψ B.emb f₁ := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP k hk f₀ hG f₁ hact
  have hPA := _root_.GlobalTheory.T.dualPair_preserves_polarization hPr F E σ B n d X W M χX χW om r s r' s' hP
  obtain ⟨m, L, hD⟩ := GlobalTheory.T.heisenbergLine_derivative_finite_span F E σ n d X W M B.ψ hP.base.std
  choose! Dfun hDiff _ using hD
  obtain ⟨Dk, _, hDk⟩ := hPA.2.1 k hk
  have hGP : ∀ g, M.IsGauss B.ψ B.emb g → g ∈ M.Pol B.ψ B.emb := fun g h =>
    Submodule.mem_sInf.2 fun N hN => hN.1 g h
  have hclos : ∀ u, At (evI F) u → ∀ g ∈ M.Pol B.ψ B.emb, Dfun u g ∈ M.Pol B.ψ B.emb := fun u hu g hg =>
    Submodule.mem_sInf.2 fun N hN => hN.2 u hu g (Submodule.mem_sInf.1 hg N hN) _ ((hDiff u hu g _).2 rfl)
  have hAt : ∀ (a : Matrix (Fin n) (Fin n) (AE F E)) (u : Matrix (Fin n) (Fin d) (AE F E)), At (evI F) u →
      At (evI F) (a * u) := fun a u hu c hc => by rw [← Matrix.mul_smul, hu c hc, Matrix.mul_zero]
  obtain ⟨hkk, hkk'⟩ := mat_mul_mat_inv k
  have hcomm : ∀ w, (mat k⁻¹).map (piInf (B.emb w)) * X.θ w = X.θ w * (mat k⁻¹).map (piInf (B.emb w)) := by
    intro w
    set A := (mat k).map (piInf (B.emb w))
    set A' := (mat k⁻¹).map (piInf (B.emb w))
    have h1 : A * A' = 1 := by
      rw [← Matrix.map_mul, hkk]; exact Matrix.map_one _ (map_zero _) (map_one _)
    have h2 : A' * A = 1 := by
      rw [← Matrix.map_mul, hkk']; exact Matrix.map_one _ (map_zero _) (map_one _)
    have hc : A * X.θ w = X.θ w * A := hk.2 w
    calc A' * X.θ w = A' * X.θ w * (A * A') := by rw [h1, Matrix.mul_one]
      _ = A' * (X.θ w * A) * A' := by simp only [Matrix.mul_assoc]
      _ = A' * (A * X.θ w) * A' := by rw [hc]
      _ = (A' * A) * X.θ w * A' := by simp only [Matrix.mul_assoc]
      _ = X.θ w * A' := by rw [h2, Matrix.one_mul]
  obtain ⟨ε, hε⟩ := hG
  refine ⟨ε, fun u u' hu hu' huu' f f' hf hf' => ?_⟩
  set v := mat k⁻¹ * u
  set v' := mat k⁻¹ * u'
  have hv : At (evI F) v := hAt _ u hu
  have hv' : At (evI F) v' := hAt _ u' hu'
  have hvv' : ∀ w, v'.map (piInf (B.emb w)) =
      (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * v.map (piInf (B.emb w)) * (W.θ w)ᵀ) := by
    intro w
    simp only [v, v', Matrix.map_mul, huu' w, Matrix.mul_smul, ← Matrix.mul_assoc, hcomm w]
  have hkv : mat k * v = u := by simp only [v, ← Matrix.mul_assoc, hkk, Matrix.one_mul]
  have hkv' : mat k * v' = u' := by simp only [v', ← Matrix.mul_assoc, hkk, Matrix.one_mul]
  have hgg : Dfun v' f₀ = Complex.I • Dfun v f₀ :=
    hε v v' hv hv' hvv' _ _ ((hDiff v hv f₀ _).2 rfl) ((hDiff v' hv' f₀ _).2 rfl)
  have hf0 : f₀ ∈ M.Pol B.ψ B.emb := hGP f₀ ⟨ε, hε⟩
  have hmove : ∀ x, At (evI F) x → ActsD (evI F) (M.heisLine B.ψ (mat k * x)) f₁ (Dk (Dfun x f₀)) := by
    intro x hx
    exact GlobalTheory.T.compactUnitary_moves_heisenbergDerivative F E σ B n d X W M χX χW om r s r' s' hP k hk x hx f₀ (Dfun x f₀) f₁ (Dk (Dfun x f₀))
      ((hDiff x hx f₀ _).2 rfl) hact ((hDk _ (hclos x hx f₀ hf0) _).2 rfl)
  have e1 : f = Dk (Dfun v f₀) := by
    have a := (hDiff u hu f₁ f).1 hf
    have b := (hDiff u hu f₁ _).1 (hkv ▸ hmove v hv)
    rw [a, b]
  have e2 : f' = Dk (Dfun v' f₀) := by
    have a := (hDiff u' hu' f₁ f').1 hf'
    have b := (hDiff u' hu' f₁ _).1 (hkv' ▸ hmove v' hv')
    rw [a, b]
  rw [e2, e1, hgg, map_smul]
end GlobalTheory.FockVacStab
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.fock_vacuum_stabilized_is_gaussian : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ X B.emb, ∀ f₀ : SInf F (Fin n × Fin d),
    M.IsGauss B.ψ B.emb f₀ → ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (k, 1)) f₀ f₁ → M.IsGauss B.ψ B.emb f₁ := by
  first | exact @_root_.GlobalTheory.FockVacStab.isGaussian_of_fock_vacuum_stabilizer_acts | exact _root_.GlobalTheory.FockVacStab.isGaussian_of_fock_vacuum_stabilizer_acts | (intros; apply _root_.GlobalTheory.FockVacStab.isGaussian_of_fock_vacuum_stabilizer_acts <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.LineDerivSplit
theorem line_derivative_split_eq_sum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ {ι : Type} (l : List ι) (γs : ι → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)),
    (∀ i, γs i ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X) → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, (∀ t, γ t = (l.map fun i => γs i t).prod) →
    ∀ ΦD ∈ GlobalTheory.SquareAgree.algD M B.ψ B.emb, ∀ Φ₁D : (Fin n × Fin d → AF F) → ℂ,
    (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) ΦD x) (Φ₁D x) 0) →
    ∃ Ψ : ι → ((Fin n × Fin d → AF F) → ℂ), (∀ i, Ψ i ∈ GlobalTheory.SquareAgree.algD M B.ψ B.emb) ∧
      (∀ i, ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho B.ψ u (om (γs i (Multiplicative.ofAdd t), 1) ΦD)))
        (GlobalTheory.WeilM.thetaSum F (M.co.rho B.ψ u (Ψ i))) 0) ∧ Φ₁D = (l.map Ψ).sum := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP ι l γs hγs γ hγ hprod ΦD hΦD Φ₁D hΦ₁
  have hact := _root_.GlobalTheory.T.dualPair_preserves_polarization hPr F E σ B n d X W M χX χW om r s r' s' hP
  choose Ds hDsP hDs using fun i => hact.1 (γs i) (hγs i)
  obtain ⟨Dγ, -, hDγ⟩ := hact.1 γ hγ
  obtain ⟨m, c, g, hg⟩ := (Submodule.mem_span_set').1 hΦD
  choose f φ hf hSB hcof hgf using fun j => (g j).2
  have hstd : ∀ j, ∀ᶠ v in Filter.cofinite,
      φ j v = Set.indicator {x : Fin n × Fin d → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} 1 := by
    intro j
    filter_upwards [hcof j, hP.good.std] with v h1 h2
    rw [h1, h2]
  have hmem : ∀ j, c j • f j ∈ M.Pol B.ψ B.emb := fun j => Submodule.smul_mem _ _ (hf j)
  have hΦ : ΦD = ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c j • f j) (φ j) := by
    rw [← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hgf j, pure_smul₀]
  refine ⟨fun i => ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Ds i (c j • f j)) (φ j), fun i => ?_, fun i u => ?_, ?_⟩
  · refine Submodule.sum_mem _ fun j _ => Submodule.subset_span ?_
    exact ⟨_, φ j, hDsP i _ (hmem j), hSB j, hcof j, rfl⟩
  · rw [hΦ]
    exact _root_.GlobalTheory.ThetaLineDerFirst.hasDerivAt_thetaSum_along_line hPr M B.ψ χX χW om hP.base.std hP.good hP.weil (γs i) (hγs i) m
      (fun j => c j • f j) (fun j => Ds i (c j • f j)) φ (fun j => ⟨hSB j, hcof j⟩)
      (fun j => (hDs i _ (hmem j) _).2 rfl) u
  · have hpt : ∀ x, Φ₁D x = ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Dγ (c j • f j)) (φ j) x := by
      intro x
      have h2 : HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) ΦD x)
          (∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Dγ (c j • f j)) (φ j) x) 0 := by
        have e : (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) ΦD x) =
            fun t => ∑ j, om (γ (Multiplicative.ofAdd t), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c j • f j) (φ j)) x := by
          funext t

          rw [hΦ, map_sum, Finset.sum_apply]
        rw [e]
        have hs := HasDerivAt.sum (u := Finset.univ) fun j _ => GlobalTheory.ThetaFacInf.Fib.hasDerivAt_pure (φ j) (hSB j) (hstd j)
          ((hDγ _ (hmem j) _).2 rfl) x
        simpa [Finset.sum_fn] using hs
      exact (hΦ₁ x).unique h2
    have hadd : ∀ j, Dγ (c j • f j) = (l.map fun i => Ds i (c j • f j)).sum := fun j =>
      _root_.GlobalTheory.T.line_derivative_additive_in_lines hPr F E σ B n d X W M χX χW om r s r' s' hP l γs hγs γ hγ hprod _ (hmem j) _ _
        ((hDγ _ (hmem j) _).2 rfl) (fun i => (hDs i _ (hmem j) _).2 rfl)
    calc Φ₁D = ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Dγ (c j • f j)) (φ j) :=
          funext fun x => (hpt x).trans (Finset.sum_apply x _ _).symm
      _ = ∑ j, (l.map fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Ds i (c j • f j)) (φ j)).sum := by
          simp only [hadd, pure_listSum]
      _ = (l.map fun i => ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Ds i (c j • f j)) (φ j)).sum :=
          sum_listSum l (fun j i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Ds i (c j • f j)) (φ j))
end GlobalTheory.LineDerivSplit
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.line_derivative_splits : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ {ι : Type} (l : List ι) (γs : ι → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)),
    (∀ i, γs i ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X) → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, (∀ t, γ t = (l.map fun i => γs i t).prod) →
    ∀ ΦD ∈ GlobalTheory.SquareAgree.algD M B.ψ B.emb, ∀ Φ₁D : (Fin n × Fin d → AF F) → ℂ,
    (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) ΦD x) (Φ₁D x) 0) →
    ∃ Ψ : ι → ((Fin n × Fin d → AF F) → ℂ), (∀ i, Ψ i ∈ GlobalTheory.SquareAgree.algD M B.ψ B.emb) ∧
      (∀ i, ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho B.ψ u (om (γs i (Multiplicative.ofAdd t), 1) ΦD)))
        (GlobalTheory.WeilM.thetaSum F (M.co.rho B.ψ u (Ψ i))) 0) ∧ Φ₁D = (l.map Ψ).sum := by
  first | exact @_root_.GlobalTheory.LineDerivSplit.line_derivative_split_eq_sum | exact _root_.GlobalTheory.LineDerivSplit.line_derivative_split_eq_sum | (intros; apply _root_.GlobalTheory.LineDerivSplit.line_derivative_split_eq_sum <;> assumption)
end
end
