module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle163
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle153
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle781
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle166
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle127
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeAdelicVectorSizeProductMulUnitaryQuotientHeigh
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField

@[expose] public section

section

noncomputable section

namespace GlobalTheory.LFun.SplitVal

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {w w' : HeightOneSpectrum (𝓞 E)}

private lemma sigR_tmul_adelic_iwasawa_hecke {K L : Type} [Field K] [Field L] [Algebra K L] {τ : L →ₐ[K] L} {R : Type} [CommRing R]
    [Algebra K R] (r : R) (e : L) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R τ (r ⊗ₜ[K] e) = r ⊗ₜ[K] τ e := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]

private lemma extZero_tmul {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L] (a : Af K) (e : L) :
    extZero K L (a ⊗ₜ[K] e) = (LinearMap.inr K (Ainf K) (Af K) a : AF K) ⊗ₜ[K] e :=
  GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul _ _ a e

omit [NumberField E] in
theorem sigR_extZero (y : Af F ⊗[F] E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ (extZero F E y) = extZero F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af F) σ y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a e =>
    rw [sigR_tmul_adelic_iwasawa_hecke, extZero_tmul, extZero_tmul]
    exact sigR_tmul_adelic_iwasawa_hecke (R := AF F) (LinearMap.inr F (Ainf F) (Af F) a) e
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

omit [NumberField E] in
theorem evalV_sigR (y : Af F ⊗[F] E) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af F) σ y) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private lemma map_evalV_eq_of_finAdEquiv_eq {v' : HeightOneSpectrum (𝓞 F)} {y₁ y₂ : Af F ⊗[F] E}
    (H : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v' → finAdEquiv F E y₁ u = finAdEquiv F E y₂ u) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v') (AlgHom.id F E) y₁ =
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v') (AlgHom.id F E) y₂ := by
  have hev1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v' (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v' 1) = 1 := by
    classical
    change (RestrictedProduct.single (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletionIntegers F) v'
      (1 : Fv F v')) v' = 1
    exact RestrictedProduct.single_eq_same _ _ _
  have hev0 : ∀ v'' : HeightOneSpectrum (𝓞 F), v'' ≠ v' →
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v'' (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v' 1) = 0 :=
    fun v'' hv => by
    classical
    change (RestrictedProduct.single (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletionIntegers F) v'
      (1 : Fv F v')) v'' = 0
    exact RestrictedProduct.single_eq_of_ne _ _ hv
  have hs1 : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v') (AlgHom.id F E)
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v' 1 ⊗ₜ[F] (1 : E)) = 1 := by
    rw [Algebra.TensorProduct.map_tmul, hev1, AlgHom.id_apply]; rfl
  have key : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v' 1 ⊗ₜ[F] (1 : E)) * y₁ =
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v' 1 ⊗ₜ[F] (1 : E)) * y₂ := by
    apply (finAdEquiv F E).injective
    refine FiniteAdeleRing.ext _ fun u => ?_
    rw [map_mul, map_mul]
    change finAdEquiv F E _ u * finAdEquiv F E y₁ u = finAdEquiv F E _ u * finAdEquiv F E y₂ u
    by_cases hu : u.under (𝓞 F) = v'
    · rw [H u hu]
    · rw [finAdEquiv_apply (rfl : u.under (𝓞 F) = u.under (𝓞 F)), Algebra.TensorProduct.map_tmul, hev0 _ hu,
        TensorProduct.zero_tmul, map_zero, zero_mul, zero_mul]
  have := congrArg (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v') (AlgHom.id F E)) key
  rwa [map_mul, map_mul, hs1, one_mul, one_mul] at this

theorem single_apply_ne (x : (w.adicCompletion E)ˣ) {u : HeightOneSpectrum (𝓞 E)} (hu : u ≠ w) :
    (GlobalTheory.CMVal.single w x : FiniteAdeleRing (𝓞 E) E) u = 1 := by
  classical
  first
  | (change (RestrictedProduct.mulSingle (fun u : HeightOneSpectrum (𝓞 E) => u.adicCompletionIntegers E) w
        (x : w.adicCompletion E)) u = 1
     exact RestrictedProduct.mulSingle_eq_of_ne _ _ hu)
  | (unfold GlobalTheory.CMVal.single
     simp only [Units.coe_map, Neutral.B1.finiteSingle, MonoidHom.coe_mk, OneHom.coe_mk,
       RestrictedProduct.coe_mulSingle_apply]
     simp [Pi.mulSingle, Function.update, hu])

private lemma cmval_single_apply_self (x : (w.adicCompletion E)ˣ) :
    (GlobalTheory.CMVal.single w x : FiniteAdeleRing (𝓞 E) E) w = x := by
  classical
  first
  | (change (Pi.mulSingle w (x : w.adicCompletion E) : ∀ u : HeightOneSpectrum (𝓞 E), u.adicCompletion E) w = x
     exact Pi.mulSingle_eq_same _ _)
  | (change (RestrictedProduct.mulSingle (fun u : HeightOneSpectrum (𝓞 E) => u.adicCompletionIntegers E) w
        (x : w.adicCompletion E)) w = x
     exact RestrictedProduct.mulSingle_eq_same _ _)
  | (unfold GlobalTheory.CMVal.single
     simp only [Units.coe_map, Neutral.B1.finiteSingle, MonoidHom.coe_mk, OneHom.coe_mk,
       RestrictedProduct.coe_mulSingle_apply]
     exact Pi.mulSingle_eq_same _ _)

theorem sigR_single (hE : IsCMExt F E σ) (h : w.under (𝓞 F) = v) (h' : w'.under (𝓞 F) = v) (hne : w ≠ w')
    (a : (Fv F v)ˣ) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af F) σ ((finAdEquiv F E).symm
      (GlobalTheory.CMVal.single w (Units.map (complMap h).toMonoidHom a) : FiniteAdeleRing (𝓞 E) E)) =
    (finAdEquiv F E).symm (GlobalTheory.CMVal.single w' (Units.map (complMap h').toMonoidHom a) : FiniteAdeleRing (𝓞 E) E) := by
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq hE hne h h'
  have hτ' : GlobalTheory.AdelicU.splitPrime (τ.comp σ) = w' := by
    obtain ⟨τ', hτ'', -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq hE (Ne.symm hne) h' h
    rcases GlobalTheory.AdelicU.eq_or_eq_comp_conj hE τ τ' with e | e
    · exact absurd (hτ''.symm.trans (e ▸ hτ)) (Ne.symm hne)
    · rw [← e]; exact hτ''
  have hz1 : GlobalTheory.AdelicU.splitProj τ (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
      ((finAdEquiv F E).symm (GlobalTheory.CMVal.single w (Units.map (complMap h).toMonoidHom a) : FiniteAdeleRing (𝓞 E) E)))
      = (a : Fv F v) := by
    apply (complMap h).injective
    rw [← GlobalTheory.LFun.ConjPlace.toCompl_eq hE h hτ, ← finAdEquiv_apply h, RingEquiv.apply_symm_apply, cmval_single_apply_self]
    rfl
  have hz2 : GlobalTheory.AdelicU.splitProj (τ.comp σ) (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
      ((finAdEquiv F E).symm (GlobalTheory.CMVal.single w (Units.map (complMap h).toMonoidHom a) : FiniteAdeleRing (𝓞 E) E)))
      = 1 := by
    apply (complMap h').injective
    rw [← GlobalTheory.LFun.ConjPlace.toCompl_eq hE h' hτ', ← finAdEquiv_apply h', RingEquiv.apply_symm_apply, map_one]
    exact single_apply_ne _ (Ne.symm hne)
  apply (finAdEquiv F E).injective
  rw [RingEquiv.apply_symm_apply]
  refine FiniteAdeleRing.ext _ fun u => ?_
  by_cases hu : u.under (𝓞 F) = v
  · have hu2 : u = w ∨ u = w' := by
      by_cases huw : u = w
      · exact Or.inl huw
      · right
        obtain ⟨τu, hτu, -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq hE huw hu h
        rcases GlobalTheory.AdelicU.eq_or_eq_comp_conj hE τ τu with e | e
        · exact absurd (hτu.symm.trans (e ▸ hτ)) huw
        · rw [← hτu, e, hτ']
    rcases hu2 with huw | huw
    · rw [huw, finAdEquiv_apply h, evalV_sigR, GlobalTheory.LFun.ConjPlace.toCompl_eq hE h hτ, ← GlobalTheory.AdelicU.splitProj_comp,
        hz2, map_one]
      exact (single_apply_ne _ hne).symm
    · rw [huw, finAdEquiv_apply h', evalV_sigR, GlobalTheory.LFun.ConjPlace.toCompl_eq hE h' hτ',
        GlobalTheory.AdelicU.splitProj_comp_sigR hE τ, hz1, cmval_single_apply_self]
      rfl
  · have h1 := map_evalV_eq_of_finAdEquiv_eq (v' := u.under (𝓞 F))
      (y₁ := (finAdEquiv F E).symm (GlobalTheory.CMVal.single w (Units.map (complMap h).toMonoidHom a) : FiniteAdeleRing (𝓞 E) E))
      (y₂ := 1) (fun u' hu' => by
        rw [RingEquiv.apply_symm_apply, map_one]
        exact single_apply_ne _ (by rintro rfl; exact hu (hu'.symm.trans h)))
    rw [finAdEquiv_apply (rfl : u.under (𝓞 F) = u.under (𝓞 F)), evalV_sigR, h1]
    simp only [map_one]
    exact (single_apply_ne _ (by rintro rfl; exact hu h')).symm

private lemma coe_locIdele' (u : HeightOneSpectrum (𝓞 E)) (x : (u.adicCompletion E)ˣ) :
    ((locIdele F u x : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = 1 - extZero F E 1 +
      extZero F E ((finAdEquiv F E).symm (GlobalTheory.CMVal.single u x : FiniteAdeleRing (𝓞 E) E)) := rfl

theorem sigR_locIdele (hE : IsCMExt F E σ) (h : w.under (𝓞 F) = v) (h' : w'.under (𝓞 F) = v) (hne : w ≠ w')
    (a : (Fv F v)ˣ) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ (locIdele F w (Units.map (complMap h).toMonoidHom a) : AF F ⊗[F] E) =
      locIdele F w' (Units.map (complMap h').toMonoidHom a) := by
  rw [coe_locIdele', coe_locIdele', map_add (f := _), map_sub, map_one, sigR_extZero, sigR_extZero, map_one,
    sigR_single hE h h' hne a]

theorem val_mul_val_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (μ : (TensorProduct F (AF F) E)ˣ →* Circle) (b : ℕ), ResEta F E μ b → ∀ (w w' : HeightOneSpectrum (𝓞 E)), w.under (𝓞 F) = w'.under (𝓞 F) → w ≠ w' → UnrAt μ w → UnrAt μ w' → val μ w * val μ w' = 1 := by
  intro F E _ _ _ _ _ σ hE μ b hμ w w' hww hne hw hw'
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq hE hne rfl hww.symm
  have hτ' : GlobalTheory.AdelicU.splitPrime (τ.comp σ) = w' := by
    obtain ⟨τ', hτ'', -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq hE (Ne.symm hne) hww.symm rfl
    rcases GlobalTheory.AdelicU.eq_or_eq_comp_conj hE τ τ' with e | e
    · exact absurd (hτ''.symm.trans (e ▸ hτ)) (Ne.symm hne)
    · rw [← e]; exact hτ''
  have ha := Formalism.L2.Host.unif_spec (w.under (𝓞 F))
  set a := Formalism.L2.Host.atFin (w.under (𝓞 F)) (Formalism.L2.Host.unif (w.under (𝓞 F))) with ha_def
  have hx : Formalism.L2.Host.IsUnifAt w (Units.map (complMap (rfl : w.under (𝓞 F) = _)).toMonoidHom a) := by
    unfold Formalism.L2.Host.IsUnifAt at ha ⊢
    rw [← ha]
    exact GlobalTheory.LFun.ConjPlace.valued_complMap hE rfl hτ _
  have hx' : Formalism.L2.Host.IsUnifAt w' (Units.map (complMap hww.symm).toMonoidHom a) := by
    unfold Formalism.L2.Host.IsUnifAt at ha ⊢
    rw [← ha]
    exact GlobalTheory.LFun.ConjPlace.valued_complMap hE hww.symm hτ' _
  rw [← UnrAt.locChar_eq_val hw hx, ← UnrAt.locChar_eq_val hw' hx']
  simp only [locChar, MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul]
  have hP : locIdele F w (Units.map (complMap (rfl : w.under (𝓞 F) = _)).toMonoidHom a) *
      locIdele F w' (Units.map (complMap hww.symm).toMonoidHom a) =
      ideleMap F E (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
        (locIdele F w (Units.map (complMap (rfl : w.under (𝓞 F) = _)).toMonoidHom a))) := by
    apply Units.ext
    rw [Units.val_mul, ← sigR_locIdele hE rfl hww.symm hne a, ← GlobalTheory.Doubling.algebraMap_norm_eq hE]
    rfl
  obtain ⟨⟨η, hη⟩, hall⟩ := hμ
  rw [hP, hall η hη, hη.2.2.1, one_pow, map_one]

end GlobalTheory.LFun.SplitVal

end
end

section

noncomputable section

namespace GlobalTheory.LFun

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU
open Formalism.L2.Host (IsUnifAt atFin)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}

namespace InertValue

theorem single_ne' {K : Type} [Field K] [NumberField K] {P Q : HeightOneSpectrum (𝓞 K)} (h : Q ≠ P)
    (u : (P.adicCompletion K)ˣ) : (GlobalTheory.CMVal.single P u : FiniteAdeleRing (𝓞 K) K) Q = 1 := by
  classical
  exact Pi.mulSingle_eq_of_ne h _

theorem exists_isUnifAt (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) :
    ∃ a : (Fv F v)ˣ, IsUnifAt w (Units.map (complMap h).toMonoidHom a) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp at hπ
    exact WithZero.exp_ne_zero hπ.symm
  refine ⟨Units.mk0 (algebraMap F (Fv F v) π) ((map_ne_zero _).2 hπ0), ?_⟩
  have hw' : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = w.asIdeal := hw
  have : w.asIdeal.LiesOver v.asIdeal := ⟨by subst h; rfl⟩
  have he : v.asIdeal.ramificationIdx' w.asIdeal = 1 := by
    apply Ideal.ramificationIdx'_spec
    · rw [pow_one, hw']
    · exact InertChart.not_map_le_sq hw
  show Valued.v (complMap h (algebraMap F (Fv F v) π)) = WithZero.exp (-1)
  rw [complMap_algebraMap]
  have hvw : Valued.v (algebraMap E (w.adicCompletion E) (algebraMap F E π)) = w.valuation E (algebraMap F E π) := by
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := w) (algebraMap F E π)
  rw [hvw, ← HeightOneSpectrum.valuation_liesOver E v w,
    ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot, he, pow_one, hπ]

theorem locIdele_complMap (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) (a : (Fv F v)ˣ) :
    locIdele F w (Units.map (complMap h).toMonoidHom a) =
      ideleMap F E (GlobalTheory.CMVal.finIdele F (GlobalTheory.CMVal.single v a)) := by
  subst h
  have key : (finAdEquiv F E).symm ((GlobalTheory.CMVal.single w (Units.map (complMap rfl).toMonoidHom a) :
      (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) =
      ((GlobalTheory.CMVal.single (w.under (𝓞 F)) a : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (1 : E) := by
    rw [RingEquiv.symm_apply_eq]
    refine FiniteAdeleRing.ext (h := fun u => ?_)
    rw [finAdEquiv_apply (rfl : u.under (𝓞 F) = _)]
    simp only [Algebra.TensorProduct.map_tmul, toCompl_tmul, map_one, mul_one]
    classical
    have same : ∀ (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) (z : (P.adicCompletion K)ˣ),
        ((GlobalTheory.CMVal.single P z : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) P = z :=
      fun K _ _ P z => Pi.mulSingle_eq_same (M := fun R : HeightOneSpectrum (𝓞 K) => R.adicCompletion K) P
        (z : P.adicCompletion K)
    by_cases hu : u = w
    · subst hu
      rw [same]
      exact congrArg (complMap (rfl : u.under (𝓞 F) = _)) (same F _ a).symm
    · have hne : u.under (𝓞 F) ≠ w.under (𝓞 F) := fun h' => hu ((InertChart.under_eq_iff hw u).1 h')
      rw [single_ne' hu]
      have e2 : ((GlobalTheory.CMVal.single (w.under (𝓞 F)) a : (FiniteAdeleRing (𝓞 F) F)ˣ) :
          FiniteAdeleRing (𝓞 F) F) (u.under (𝓞 F)) = 1 := single_ne' hne a
      exact ((congrArg (complMap (rfl : u.under (𝓞 F) = _)) e2).trans (map_one _)).symm
  apply Units.ext
  show 1 - extZero F E 1 + extZero F E ((finAdEquiv F E).symm ((GlobalTheory.CMVal.single w
      (Units.map (complMap rfl).toMonoidHom a) : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E)) =
    algebraMap (AF F) (AF F ⊗[F] E) ((MonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
      ((GlobalTheory.CMVal.single (w.under (𝓞 F)) a : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))
  rw [key]
  generalize ((GlobalTheory.CMVal.single (w.under (𝓞 F)) a : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) = s
  have h2 : extZero F E 1 = (@id (AF F) (LinearMap.inr F (Ainf F) (Af F) 1)) ⊗ₜ[F] (1 : E) :=
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul _ _ 1 1
  have h3 : extZero F E (s ⊗ₜ[F] (1 : E)) = (@id (AF F) (LinearMap.inr F (Ainf F) (Af F) s)) ⊗ₜ[F] (1 : E) :=
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul _ _ s 1
  have h4 : algebraMap (AF F) (AF F ⊗[F] E) (MonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) s) =
      (@id (AF F) (MonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) s)) ⊗ₜ[F] (1 : E) := rfl
  have hX : (1 : AF F) - (@id (AF F) (LinearMap.inr F (Ainf F) (Af F) 1)) +
      (@id (AF F) (LinearMap.inr F (Ainf F) (Af F) s)) =
      (@id (AF F) (MonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) s)) := by
    refine Prod.ext ?_ ?_
    · show (1 : Ainf F) - 0 + 0 = 1
      simp
    · show (1 : Af F) - 1 + s = s
      simp
  rw [h2, h3, h4, ← hX, TensorProduct.add_tmul, TensorProduct.sub_tmul]
  rfl

theorem eta_sq (h2 : Module.finrank F E = 2) {η : (AF F)ˣ →* Circle} (hη : IsEta F E η) (a : (AF F)ˣ) :
    η a ^ 2 = 1 := by
  have hn := hη.2.2.1 (ideleMap F E a)
  have hnorm : Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (ideleMap F E a) = a ^ 2 := by
    apply Units.ext
    show Algebra.norm (AF F) (algebraMap (AF F) (AF F ⊗[F] E) (a : AF F)) = ((a ^ 2 : (AF F)ˣ) : AF F)
    rw [Units.val_pow_eq_pow_val,
      Algebra.norm_algebraMap_of_basis (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)), Fintype.card_fin, h2]
  rw [hnorm, map_pow] at hn
  exact hn

end InertValue


open InertValue in
theorem val_sq_eq_one_of_isInertAt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (μ : (TensorProduct F (AF F) E)ˣ →* Circle) (b : ℕ) (hμ : ResEta F E μ b)
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (hw : IsInertAt F E v w) (hu : UnrAt μ w) :
    val μ w ^ 2 = 1 := by
  obtain ⟨⟨η, hη⟩, hres⟩ := hμ
  have h2 : Module.finrank F E = 2 := hσ.2.2.1
  have hw' : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = w.asIdeal := hw
  have hv : w.under (𝓞 F) = v := by
    ext1
    symm
    refine v.isMaximal.eq_of_le (w.under (𝓞 F)).isPrime.ne_top ?_
    exact Ideal.map_le_iff_le_comap.1 hw'.le
  obtain ⟨a, ha⟩ := exists_isUnifAt hw hv
  rw [← UnrAt.locChar_eq_val hu ha]
  simp only [locChar, MonoidHom.comp_apply]
  rw [locIdele_complMap hw hv a, hres η hη, ← map_pow, ← pow_mul, mul_comm, pow_mul, eta_sq h2 hη, one_pow,
    map_one]

end GlobalTheory.LFun

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LeviNorm

variable {D : D7}

def sandwichHomeo {m n : ℕ} (P : GL (Fin m) (AE D)) (Q : GL (Fin n) (AE D)) : Mx D m n ≃ₜ Mx D m n where
  toFun u := HMul.hMul (HMul.hMul P.val u) Q.val
  invFun v := HMul.hMul (HMul.hMul (P⁻¹).val v) (Q⁻¹).val
  left_inv u := by
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  right_inv v := by
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem phase_sandwich (ψ : AddChar (AF D.host.F) ℂ) (W : HSp D) {r : ℕ} (h : GA D W) (a : GL (Fin r) (AE D))
    (y u : Mx D W.rank r) :
    phase ψ W (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) y) (GlobalTheory.MixModel.adj (a⁻¹).val))
      (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val) = phase ψ W y u := by
  rw [phase_apply, phase_apply]
  congr 3
  have hu := GlobalTheory.MixModel.mt_unitary W h⁻¹
  have adj_mul_local {l m n : ℕ} (x : Mx D l m) (y : Mx D m n) :
      GlobalTheory.MixModel.adj (x * y) = GlobalTheory.MixModel.adj y * GlobalTheory.MixModel.adj x := by
    unfold GlobalTheory.MixModel.adj
    rw [Matrix.map_mul, Matrix.transpose_mul]
  change (GlobalTheory.MixModel.adj ((Formalism.L2.Theta.mt W h⁻¹) * y * (GlobalTheory.MixModel.adj (a⁻¹).val)) *
    (GlobalTheory.MixModel.gA W * ((Formalism.L2.Theta.mt W h⁻¹) * u * a.val))).trace = _
  simp only [adj_mul_local, GlobalTheory.MixModel.adj_adj]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (GlobalTheory.MixModel.gA W) (Formalism.L2.Theta.mt W h⁻¹),
    ← Matrix.mul_assoc (GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt W h⁻¹)), hu, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem absE_det_matHom_inv {W : HSp D} (h : GA D W)
    (hh : GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.matHom W h)) = 1) :
    GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.matHom W h⁻¹)) = 1 := by
  rw [map_inv, map_inv, map_inv, hh, inv_one]

theorem absE_det_pow_ne {r : ℕ} (a : GL (Fin r) (AE D)) (k : ℕ) :
    ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ENNReal) ^ k) ≠ 0 ∧
      ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ENNReal) ^ k) ≠ ⊤ :=
  ⟨pow_ne_zero _ (ENNReal.coe_ne_zero.2 ((Group.isUnit (Matrix.GeneralLinearGroup.det a)).map
    (GlobalTheory.Doubling.absE D.host.F D.host.E)).ne_zero), ENNReal.pow_ne_top ENNReal.coe_ne_top⟩



theorem integral_phase_sandwich : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W : HSp D) (r : ℕ) (μ : Measure (Mx D W.rank r)), μ.IsAddHaarMeasure → ∀ (h : GA D W), GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det (matHom W h)) = 1 → ∀ (a : GL (Fin r) (AE D)) (N : Mx D W.rank r → ℂ), Continuous N → Integrable N μ → Integrable (fun u : Mx D W.rank r => N (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val)) μ ∧ ∀ y : Mx D W.rank r, ∫ u, GlobalTheory.LeviNorm.phase ψ W (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) y) (GlobalTheory.MixModel.adj (a⁻¹).val)) u * N u ∂μ = ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ^ W.rank * ∫ u, GlobalTheory.LeviNorm.phase ψ W y u * N (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val) ∂μ := by
  intro D ψ _ W r μ hμ h hh a N _ hNi
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  have hmod := GlobalTheory.T.addHaar_leftRightMul_adelicMatrices_module D W.rank r μ hμ (Formalism.L2.Theta.matHom W h⁻¹) a
  have h1 := absE_det_matHom_inv h hh
  rw [h1, ENNReal.coe_one, one_pow, one_mul] at hmod
  obtain ⟨hc0, hcT⟩ := absE_det_pow_ne a W.rank
  let e := (sandwichHomeo (Formalism.L2.Theta.matHom W h⁻¹) a).toMeasurableEquiv
  have he : ∀ u, e u = HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val := fun _ => rfl
  have hmap : (Measure.map (fun u : Mx D W.rank r =>
      (HMul.hMul (HMul.hMul (Formalism.L2.Theta.matHom W h⁻¹).val (u : Matrix (Fin W.rank) (Fin r) (AE D))) a.val :
        Mx D W.rank r)) μ) = Measure.map e μ := rfl
  rw [hmap] at hmod
  refine ⟨?_, fun y => ?_⟩
  · rw [hmod, integrable_smul_measure hc0 hcT, integrable_map_equiv] at hNi
    exact hNi
  · conv_lhs => rw [hmod]
    rw [integral_smul_measure, integral_map_equiv]
    simp only [he, phase_sandwich]
    rw [ENNReal.toReal_pow, ENNReal.coe_toReal, Complex.real_smul]
    push_cast
    rfl

end GlobalTheory.LeviNorm
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integral_fundamentalDomain_eq_iterated_decomp : ∀ (D : D7) (V W : HSp D) (a b k : ℕ) (f₁ f₃ : Mx D a b → WO V W) (f₂ : Mx D 1 k → WO V W), Continuous f₁ → Continuous f₂ → Continuous f₃ → (∀ s s', f₁ (s + s') = f₁ s + f₁ s') → (∀ z z', f₂ (z + z') = f₂ z + f₂ z') → (∀ y y', f₃ (y + y') = f₃ y + f₃ y') → (∀ x : WO V W, ∃ s z y, x = f₁ s + f₂ z + f₃ y) → (∀ s z y, f₁ s + f₂ z + f₃ y = 0 → s = 0 ∧ z = 0 ∧ y = 0) → (∀ s z y, f₁ s + f₂ z + f₃ y ∈ ratL W V ↔ s ∈ GlobalTheory.MixModel.ratMx D a b ∧ z ∈ GlobalTheory.MixModel.ratMx D 1 k ∧ y ∈ GlobalTheory.MixModel.ratMx D a b) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (GlobalTheory.MixModel.ratMx D a b) μ 𝓨 → ∀ (η : Measure (Mx D 1 k)) (𝓩 : Set (Mx D 1 k)), η.IsAddHaarMeasure → IsAddFundamentalDomain (GlobalTheory.MixModel.ratMx D 1 k) 𝓩 η → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∃ κ : ℝ, 0 < κ ∧ ∀ T : WO V W → ℂ, Continuous T → (∀ γ ∈ ratL W V, ∀ u, T (γ + u) = T u) → ∫ u in 𝓕, T u ∂ν = κ * ∫ s in 𝓨, (∫ z in 𝓩, (∫ y in 𝓨, T (f₁ s + f₂ z + f₃ y) ∂μ) ∂η) ∂μ := by
  first | exact @GlobalTheory.CoordUnfold.integral_fundamentalDomain_eq_iterated | exact GlobalTheory.CoordUnfold.integral_fundamentalDomain_eq_iterated | (intros; apply GlobalTheory.CoordUnfold.integral_fundamentalDomain_eq_iterated <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.iteratedIntegral_decomp_continuous_periodic : ∀ (D : D7) (V W : HSp D) (a b k : ℕ) (f₁ f₃ : Mx D a b → WO V W) (f₂ : Mx D 1 k → WO V W), Continuous f₁ → Continuous f₂ → Continuous f₃ → (∀ s s', f₁ (s + s') = f₁ s + f₁ s') → (∀ r ∈ GlobalTheory.MixModel.ratMx D a b, f₁ r ∈ ratL W V) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (GlobalTheory.MixModel.ratMx D a b) μ 𝓨 → ∀ (η : Measure (Mx D 1 k)) (𝓩 : Set (Mx D 1 k)), η.IsAddHaarMeasure → IsAddFundamentalDomain (GlobalTheory.MixModel.ratMx D 1 k) 𝓩 η → ∀ T : WO V W → ℂ, Continuous T → (∀ γ ∈ ratL W V, ∀ u, T (γ + u) = T u) → Continuous (fun s => ∫ z in 𝓩, (∫ y in 𝓨, T (f₁ s + f₂ z + f₃ y) ∂μ) ∂η) ∧ ∀ r ∈ GlobalTheory.MixModel.ratMx D a b, ∀ s, ∫ z in 𝓩, (∫ y in 𝓨, T (f₁ (r + s) + f₂ z + f₃ y) ∂μ) ∂η = ∫ z in 𝓩, (∫ y in 𝓨, T (f₁ s + f₂ z + f₃ y) ∂μ) ∂η := by
  first | exact @GlobalTheory.IsoMean.iterInt_continuous_periodic | exact GlobalTheory.IsoMean.iterInt_continuous_periodic | (intros; apply GlobalTheory.IsoMean.iterInt_continuous_periodic <;> assumption)
end

section

open Classical MeasureTheory

theorem _root_.GlobalTheory.T.fockS_fockColumnSubstitution_unitary : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (u : ι → Matrix.unitaryGroup (Fin a) ℂ) (P Q : GlobalTheory.MinorFrame.Pol ι d a),
  Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.colSub (fun τ => (u τ : Matrix (Fin a) (Fin a) ℂ)) P)
    (GlobalTheory.MinorFrame.colSub (fun τ => (u τ : Matrix (Fin a) (Fin a) ℂ)) Q) = Formalism.L2.DIV.fockS P Q := by
  first | exact @GlobalTheory.MinorFrame.fockS_colSub_unitary | exact GlobalTheory.MinorFrame.fockS_colSub_unitary | (intros; apply GlobalTheory.MinorFrame.fockS_colSub_unitary <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.le_adelicVectorSizeProduct_mul_unitaryQuotientHeight_pow : ∀ (D : D7) (V : HSp D), ∃ (c : ℝ) (N : ℕ), 0 < c ∧ ∀ (g : GA D V) (ξ : Fin V.rank → D.host.E), ξ ≠ 0 → c ≤ GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen V g ξ) * GlobalTheory.Grow.quotHeight V g ^ N := by
  first | exact @GlobalTheory.SeenSize.le_vsize_mul_quotHeight | exact GlobalTheory.SeenSize.le_vsize_mul_quotHeight | (intros; apply GlobalTheory.SeenSize.le_vsize_mul_quotHeight <;> assumption)
end
