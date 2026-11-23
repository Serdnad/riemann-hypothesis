module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryScalarInertPlaceInvertibleShifts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1879
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1906
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1908
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1349
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.LatVac

theorem heis_at_local_identity : ∀ {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {W : Type} [AddCommGroup W]
    [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ)
    (γ : W) (f : (κ → Fv F v) → ℂ) (χ : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) γ →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (co.rho ψ γ) f (χ • f) →
    ∀ r : (κ → AF F) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) f r → ∀ x₀, r x₀ ≠ 0 →
    ∀ ξ : κ → Fv F v, GlobalTheory.LatVac.psiAt ψ v (ξ ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 +
        (2 : Fv F v)⁻¹ * ((GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2)) *
      f (ξ + (GlobalTheory.LatVac.locCo co v γ).1) = χ * f ξ := by
  intro F _ _ v W _ _ B κ _ co ψ γ f χ hγ hA r hr x₀ hx₀ ξ
  have hx1 : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) ((co.e γ).1 k) := fun k u hu => by
    have h := congrArg (fun w => (co.e w).1 k) (hγ u hu)
    simpa [LinearEquiv.map_smul] using h
  have hy1 : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) ((co.e γ).2 k) := fun k u hu => by
    have h := congrArg (fun w => (co.e w).2 k) (hγ u hu)
    simpa [LinearEquiv.map_smul] using h
  set z : κ → AF F := fun k => GlobalTheory.LatVac.liftV v (ξ k - evFin F v (x₀ k)) with hz
  have hzat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z :=
    GlobalTheory.VacIndic.at_pi fun k => GlobalTheory.LatVac.at_liftV v _
  set x : κ → AF F := x₀ + z with hx
  have hevx : (fun i => evFin F v (x i)) = ξ := by
    funext i
    simp [hx, hz, GlobalTheory.LatVac.evFin_liftV]
  have hrx : r x = r x₀ := hr.1 x₀ z hzat
  have hrx1 : r (x + (co.e γ).1) = r x := hr.1 x _ (GlobalTheory.VacIndic.at_pi hx1)
  have key := congrFun (hA r hr) x
  simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens] at key
  have hAt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v)
      (x ⬝ᵥ (co.e γ).2 + ⅟(2 : AF F) * ((co.e γ).1 ⬝ᵥ (co.e γ).2)) := by
    refine GlobalTheory.VacIndic.at_add ?_ (GlobalTheory.VacIndic.at_mul_left ?_)
    · exact GlobalTheory.VacIndic.at_sum _ _ fun i => GlobalTheory.VacIndic.at_mul_left (hy1 i)
    · exact GlobalTheory.VacIndic.at_sum _ _ fun i => GlobalTheory.VacIndic.at_mul_left (hy1 i)
  rw [GlobalTheory.VacIndic.psi_of_at ψ hAt, hrx1] at key
  have hhalf : evFin F v (⅟(2 : AF F)) = (2 : Fv F v)⁻¹ := by
    rw [GlobalTheory.VacIndic.invOf_two_eq, GlobalTheory.VacIndic.evFin_algebraMap]
    simp [map_ofNat]
  have hdot : ∀ a b : κ → AF F, evFin F v (a ⬝ᵥ b) = (fun i => evFin F v (a i)) ⬝ᵥ (fun i => evFin F v (b i)) := by
    intro a b

    simp [dotProduct, map_sum, map_mul]
  have hsum : (fun i => evFin F v ((x + (co.e γ).1) i)) = ξ + (GlobalTheory.LatVac.locCo co v γ).1 := by
    funext i
    rw [← hevx]
    simp [GlobalTheory.LatVac.locCo]
  rw [map_add (f := _), map_mul, hhalf, hdot, hdot, hevx, hsum] at key
  have hr0 : r x ≠ 0 := hrx ▸ hx₀
  rw [GlobalTheory.LatVac.psiAt_apply]
  have := key
  simp only [Pi.smul_apply, smul_eq_mul] at this
  apply mul_right_cancel₀ hr0
  rw [← this]
  simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  ring

end GlobalTheory.LatVac
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.hermitian_tensor_skewHermitian_lattice_open_compact : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n)
    (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X Y,
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        M.co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k))) →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F),
      IsOpen (((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v).map (GlobalTheory.LatVac.locCo M.co v) :
        AddSubgroup ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))) : Set ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))) ∧
      IsCompact (((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v).map (GlobalTheory.LatVac.locCo M.co v) :
        AddSubgroup ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))) : Set ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))) := by
  first | exact @GlobalTheory.LatOpenCpt.main | exact GlobalTheory.LatOpenCpt.main | (intros; apply GlobalTheory.LatOpenCpt.main <;> assumption)
end

section

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section

namespace GlobalTheory.PsiProd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F : Type} [Field F] [NumberField F]

def intFin (y : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) : Af F :=
  RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
    (fun v => ⟨(y v).1, (y v).2⟩)

theorem continuous_intFin : Continuous (intFin (F := F)) :=
  RestrictedProduct.isEmbedding_structureMap.continuous

theorem evalV_intFin (y : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F))
    (w : HeightOneSpectrum (𝓞 F)) : evalV F w (intFin y) = (y w : Fv F w) := rfl

theorem intFin_nsmul (n : ℕ) (y : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) :
    intFin (n • y) = n • intFin y := by
  refine GlobalTheory.AdelicU.af_ext fun w => ?_
  rw [map_nsmul, evalV_intFin, evalV_intFin]
  rfl

theorem exists_finset_trivial (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) :
    ∃ I : Finset (HeightOneSpectrum (𝓞 F)), ∀ y : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F),
      (∀ v ∈ I, y v = 0) → ψ (LinearMap.inr F (Ainf F) (Af F) (intFin y)) = 1 := by
  let ι : (∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) → AF F := fun y =>
    LinearMap.inr F (Ainf F) (Af F) (intFin y)
  have hι : Continuous ι := continuous_const.prodMk continuous_intFin
  have hopen : IsOpen {y | ‖ψ (ι y) - 1‖ < 1 / 2} :=
    isOpen_lt ((hψ.comp hι).sub continuous_const).norm continuous_const
  have h0 : (0 : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) ∈ {y | ‖ψ (ι y) - 1‖ < 1 / 2} := by
    have : ι 0 = 0 := by
      have h : intFin (0 : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) = 0 := by
        simpa using intFin_nsmul (F := F) 0 0
      show LinearMap.inr F (Ainf F) (Af F) (intFin 0) = (0 : AF F)
      rw [h, map_zero]
    simp [this, AddChar.map_zero_eq_one]
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 hopen 0 h0
  refine ⟨I, fun y hy => GlobalTheory.eq_one_of_forall_norm_pow_sub_one_lt _ fun n => ?_⟩
  have hmem : n • y ∈ (I : Set _).pi u := by
    intro a ha
    have : (n • y) a = 0 := by rw [Pi.smul_apply, hy a ha, smul_zero]
    rw [this]; exact (hu a ha).2
  have e : (ι (n • y) : AF F) = n • (ι y : AF F) := by
    show LinearMap.inr F (Ainf F) (Af F) (intFin (n • y)) = _
    rw [intFin_nsmul, map_nsmul]
  have h := hsub hmem
  simp only [Set.mem_setOf_eq] at h
  rwa [e, AddChar.map_nsmul_eq_pow] at h

end GlobalTheory.PsiProd

namespace GlobalTheory.PsiProd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem addChar_sum {A ι : Type} [AddCommMonoid A] (χ : AddChar A ℂ) (s : Finset ι) (f : ι → A) :
    χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddChar.map_zero_eq_one]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

theorem psiAt_eq_one_of_integral {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (I : Finset (HeightOneSpectrum (𝓞 F)))
    (hI : ∀ y : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F),
      (∀ v ∈ I, y v = 0) → ψ (LinearMap.inr F (Ainf F) (Af F) (intFin y)) = 1)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ I) (a : Fv F v) (ha : a ∈ v.adicCompletionIntegers F) :
    GlobalTheory.LatVac.psiAt ψ v a = 1 := by
  classical
  let y : ∀ u : HeightOneSpectrum (𝓞 F), ↥(u.adicCompletionIntegers F) := Pi.single v ⟨a, ha⟩
  have hy : ∀ u ∈ I, y u = 0 := fun u hu => Pi.single_eq_of_ne (by rintro rfl; exact hv hu) _
  have hfin : intFin y = GlobalTheory.AdelicU.singleFin v a := by
    refine GlobalTheory.AdelicU.af_ext fun w => ?_
    rw [evalV_intFin]
    by_cases e : w = v
    · subst e
      rw [GlobalTheory.AdelicU.evalV_singleFin_self]
      simp [y]
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne e]
      simp [y, Pi.single_eq_of_ne e]
  have := hI y hy
  rw [hfin] at this
  exact this

theorem psi_prod : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ x : AF F,
    (Function.mulSupport fun v : Pl F => GlobalTheory.LatVac.psiAt ψ v (evFin F v x)).Finite ∧
    ψ x = ψ (pairA F (fstA F x) 0) * ∏ᶠ v : Pl (F := F), GlobalTheory.LatVac.psiAt ψ v (evFin F v x) := by
  intro F _ _ ψ hψ x
  classical
  obtain ⟨I, hI⟩ := exists_finset_trivial ψ hψ
  set xf : Af F := sndA F x with hxf
  have hT : {v : HeightOneSpectrum (𝓞 F) | evalV F v xf ∉ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 xf.2
  let S : Finset (HeightOneSpectrum (𝓞 F)) := I ∪ hT.toFinset
  have hev : ∀ v, evFin F v x = evalV F v xf := fun v => rfl
  have hsupp : (Function.mulSupport fun v : Pl F => GlobalTheory.LatVac.psiAt ψ v (evFin F v x)) ⊆ (S : Set _) := by
    intro v hv
    by_contra hvS
    apply hv
    simp only [S, Finset.coe_union, Set.mem_union, Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
      not_or, not_not] at hvS
    show GlobalTheory.LatVac.psiAt ψ v (evFin F v x) = 1
    rw [hev]
    exact psiAt_eq_one_of_integral ψ I hI v hvS.1 _ hvS.2
  refine ⟨(S.finite_toSet).subset hsupp, ?_⟩
  let j : Af F →ₗ[F] AF F := LinearMap.inr F (Ainf F) (Af F)
  let χ : AddChar (Af F) ℂ := ψ.compAddMonoidHom j.toAddMonoidHom
  have hχ : ∀ a, χ a = ψ (j a) := fun a => rfl
  have hloc : ∀ v (a : Fv F v), GlobalTheory.LatVac.psiAt ψ v a = χ (GlobalTheory.AdelicU.singleFin v a) := fun v a => rfl
  have hx : x = pairA F (fstA F x) 0 + j xf := by
    refine Prod.ext ?_ ?_
    · show x.1 = x.1 + (0 : Ainf F)
      rw [add_zero]
    · show x.2 = (0 : Af F) + x.2
      rw [zero_add]
  let r : ∀ w : HeightOneSpectrum (𝓞 F), ↥(w.adicCompletionIntegers F) := fun w =>
    if hw : w ∈ S then 0 else ⟨evalV F w xf, by
      have : w ∉ hT.toFinset := fun h => hw (Finset.mem_union_right _ h)
      simpa using this⟩
  have hr : ∀ v ∈ I, r v = 0 := fun v hv => dif_pos (Finset.mem_union_left _ hv)
  have hdec : xf = ∑ v ∈ S, GlobalTheory.AdelicU.singleFin v (evalV F v xf) + intFin r := by
    refine GlobalTheory.AdelicU.af_ext fun w => ?_

    rw [map_add (f := _), map_sum, evalV_intFin]
    by_cases hw : w ∈ S
    · rw [Finset.sum_eq_single w (fun b _ hb => GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm hb) _)
        (fun h => absurd hw h), GlobalTheory.AdelicU.evalV_singleFin_self]
      simp [r, hw]
    · rw [Finset.sum_eq_zero (fun b hb => GlobalTheory.AdelicU.evalV_singleFin_ne (by rintro rfl; exact hw hb) _)]
      simp [r, hw]
  have hrr : χ (intFin r) = 1 := hI r hr
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
  conv_lhs => rw [hx]
  rw [AddChar.map_add_eq_mul]
  congr 1
  rw [← hχ, hdec, AddChar.map_add_eq_mul, hrr, mul_one, addChar_sum]
  exact Finset.prod_congr rfl fun v _ => by rw [hloc, hev]

end GlobalTheory.PsiProd
end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.local_weyl_element_doubled : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Pl (F := F)) (f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) →
    ∃ w : UG (cA σ) (dbl (incM F J)),
      ((w : GL (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) ∧
      At (evFin F v) (((w : GL (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) ∧
      w * w = 1 ∧
      ∀ k : UA σ J, At (evFin F v) (mat k - 1) → ∀ gd gd' : UG (cA σ) (dbl (incM F J)),
        ((gd : GL (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = Matrix.fromBlocks (mat k) 0 0 1 →
        ((gd' : GL (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = Matrix.fromBlocks 1 0 0 (mat k) →
        w * gd * w = gd' := by
  first | exact @GlobalTheory.DblDiag.swap_at_place | exact GlobalTheory.DblDiag.swap_at_place | (intros; apply GlobalTheory.DblDiag.swap_at_place <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.latticeLocalDarbouxCoordinates_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v : Pl (F := F), ∃ c : Fv F v, c ≠ 0 ∧ ∀ γ ∈ latAtV G.V G.W v, ∀ k,
      c * (GlobalTheory.LatVac.locCo G.M.co v γ).1 k ∈ HeightOneSpectrum.adicCompletionIntegers F v ∧
      c * (GlobalTheory.LatVac.locCo G.M.co v γ).2 k ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
  first | exact @GlobalTheory.LatVacBdd.locCo_bounded | exact GlobalTheory.LatVacBdd.locCo_bounded | (intros; apply GlobalTheory.LatVacBdd.locCo_bounded <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.local_idempotent_character_value : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ {a' d : ℕ} (J : Matrix (Fin a') (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) → piW t f = 1 → piW (t.comp σ) f = -1 →
    ∀ w : UG (cA σ) (dbl J),
      ((w : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin a') (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) →
    At (evFin F v) (((w : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) ∧
    ∀ (u₁ u₂ : Matrix (Fin d) (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evFin F v) u₁ → At (evFin F v) u₂ →
      (u₁.map (piW t) = 0 → u₂.map (piW t) = 0 →
        actB (cA σ) w (Matrix.fromCols u₁ u₂) = Matrix.fromCols (-u₂) (-u₁)) ∧
      (u₁.map (piW (t.comp σ)) = 0 → u₂.map (piW (t.comp σ)) = 0 →
        actB (cA σ) w (Matrix.fromCols u₁ u₂) = Matrix.fromCols u₂ u₁) := by
  first | exact @GlobalTheory.SwapAtPlace.swap_at_acts | exact GlobalTheory.SwapAtPlace.swap_at_acts | (intros; apply GlobalTheory.SwapAtPlace.swap_at_acts <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.local_matrix_moment_surjective_conj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d r s r' s' : ℕ) (X : Spc F E n) (W : Spc F E d), X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (Z : Matrix (Fin n) (Fin d) (Fv F v)), ∃ u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      At (evFin F v) u ∧ u.map (piW (t.comp σ)) = 0 ∧ ∀ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) x →
        x.map (piW t) = 0 → B.ψ (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) x u) =
          GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, (-((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (x).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1)) i j * Z i j) := by
  first | exact @GlobalTheory.OppLinChar.char_eq_psi_symp | exact GlobalTheory.OppLinChar.char_eq_psi_symp | (intros; apply GlobalTheory.OppLinChar.char_eq_psi_symp <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix

namespace GlobalTheory.DblVacEigen

theorem local_identity_of_tens_eigen : ∀ {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (ψ : AddChar (AF F) ℂ) (γ : W) (f : (κ → Fv F v) → ℂ)
    (R : (κ → AF F) → ℂ) (c : ℂ), At (evFin F v) γ → (∀ x z, At (evFin F v) z → R (x + z) = R x) →
    ∀ x₀, R x₀ ≠ 0 → co.rho ψ γ (tens (evFin F v) f R) = c • tens (evFin F v) f R →
    ∀ ξ : κ → Fv F v, GlobalTheory.LatVac.psiAt ψ v (ξ ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 +
        (2 : Fv F v)⁻¹ * ((GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2)) *
      f (ξ + (GlobalTheory.LatVac.locCo co v γ).1) = c * f ξ := by
  intro F _ _ v W _ _ B κ _ co ψ γ f R c hγ hR x₀ hx₀ hA ξ
  have hx1 : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) ((co.e γ).1 k) := fun k u hu => by
    have h := congrArg (fun w => (co.e w).1 k) (hγ u hu)
    simpa [LinearEquiv.map_smul] using h
  have hy1 : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) ((co.e γ).2 k) := fun k u hu => by
    have h := congrArg (fun w => (co.e w).2 k) (hγ u hu)
    simpa [LinearEquiv.map_smul] using h
  set z : κ → AF F := fun k => GlobalTheory.LatVac.liftV v (ξ k - evFin F v (x₀ k)) with hz
  have hzat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z :=
    GlobalTheory.VacIndic.at_pi fun k => GlobalTheory.LatVac.at_liftV v _
  set x : κ → AF F := x₀ + z with hx
  have hevx : (fun i => evFin F v (x i)) = ξ := by
    funext i
    simp [hx, hz, GlobalTheory.LatVac.evFin_liftV]
  have hrx : R x = R x₀ := hR x₀ z hzat
  have hrx1 : R (x + (co.e γ).1) = R x := hR x _ (GlobalTheory.VacIndic.at_pi hx1)
  have key := congrFun hA x
  simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Pi.smul_apply, smul_eq_mul] at key
  have hAt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v)
      (x ⬝ᵥ (co.e γ).2 + ⅟(2 : AF F) * ((co.e γ).1 ⬝ᵥ (co.e γ).2)) := by
    refine GlobalTheory.VacIndic.at_add ?_ (GlobalTheory.VacIndic.at_mul_left ?_)
    · exact GlobalTheory.VacIndic.at_sum _ _ fun i => GlobalTheory.VacIndic.at_mul_left (hy1 i)
    · exact GlobalTheory.VacIndic.at_sum _ _ fun i => GlobalTheory.VacIndic.at_mul_left (hy1 i)
  rw [GlobalTheory.VacIndic.psi_of_at ψ hAt, hrx1] at key
  have hhalf : evFin F v (⅟(2 : AF F)) = (2 : Fv F v)⁻¹ := by
    rw [GlobalTheory.VacIndic.invOf_two_eq, GlobalTheory.VacIndic.evFin_algebraMap]
    simp [map_ofNat]
  have hdot : ∀ a b : κ → AF F, evFin F v (a ⬝ᵥ b) = (fun i => evFin F v (a i)) ⬝ᵥ (fun i => evFin F v (b i)) := by
    intro a b

    simp [dotProduct, map_sum, map_mul]
  have hsum : (fun i => evFin F v ((x + (co.e γ).1) i)) = ξ + (GlobalTheory.LatVac.locCo co v γ).1 := by
    funext i
    rw [← hevx]
    simp [GlobalTheory.LatVac.locCo]
  rw [map_add (f := _), map_mul, hhalf, hdot, hdot, hevx, hsum] at key
  have hr0 : R x ≠ 0 := hrx ▸ hx₀
  rw [GlobalTheory.LatVac.psiAt_apply]
  have := key
  apply mul_right_cancel₀ hr0
  simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this ⊢
  linear_combination this

end GlobalTheory.DblVacEigen
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_unitaryScalar_inertPlace_invertible_shifts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (g : UA σ J),
    ∃ k : UA σ J, At (evFin F v) (mat k - 1) ∧ ∃ a b : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) a ∧ At (evFin F v) b ∧
      a * (1 - mat k) = liftV v (1 : Fv F v) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) ∧
      (1 - mat k) * a = liftV v (1 : Fv F v) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) ∧
      b * (1 - mat (g⁻¹ * k)) = liftV v (1 : Fv F v) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) ∧
      (1 - mat (g⁻¹ * k)) * b = liftV v (1 : Fv F v) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
  first | exact @GlobalTheory.InertScalarUnit.exists_scalar_inv_at | exact GlobalTheory.InertScalarUnit.exists_scalar_inv_at | (intros; apply GlobalTheory.InertScalarUnit.exists_scalar_inv_at <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.smallRoute_sum_translated_outerIntegrals_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ' : TotT G (routeSmall t i j))
    (F : Fn G (.grid i (j + 1))) (hB : TotConv W M _ Θ' F) (g₁ : GA D (G.V (.grid (i + 1) j))) (z : GA D (G.V (.grid i j)) →₀ ℂ)
    (hI : ∀ d ∈ Θ'.support, ∀ k, IntegrableOn (fun u => GlobalTheory.SmallRoute.outer W M d F g₁ (u * k)) (M.fd (.grid i j)) (M.ν (.grid i j)))
    (hJ : Integrable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid i j)) => F p.1 * translates z (kerSmall W Θ' p.1 g₁) p.2)
      (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod ((M.ν (.grid i j)).restrict (M.fd (.grid i j))))),
    (Θ'.sum fun d c => c * ∫ u in M.fd (.grid i j), translates z (GlobalTheory.SmallRoute.outer W M d F g₁) u ∂M.ν (.grid i j)) =
      ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid i j),
        translates z (kerSmall W Θ' g g₁) u ∂M.ν (.grid i j) ∂M.ν (.grid i (j + 1)) := by
  first | exact @GlobalTheory.SmallRoute.sum_integral_translates_outer_eq | exact GlobalTheory.SmallRoute.sum_integral_translates_outer_eq | (intros; apply GlobalTheory.SmallRoute.sum_integral_translates_outer_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.smallRoute_combination_mul_lift_by_degree : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (F : Fn G (.grid i (j + 1))) (hF : IsAutFunSm W.θ _ F) (hB : TotConv W M _ Θ' F) (g₁ : GA D (G.V (.grid (i + 1) j)))
    (z : GA D (G.V (.grid i j)) →₀ ℂ),
    (∀ d ∈ Θ'.support, ∀ k, IntegrableOn (fun u => GlobalTheory.SmallRoute.outer W M d F g₁ (u * k)) (M.fd (.grid i j)) (M.ν (.grid i j))) ∧
    zdeg z * liftT W M (routeSmall t i j) Θ' F g₁ =
      Θ'.sum fun d c => c * ∫ u in M.fd (.grid i j), translates z (GlobalTheory.SmallRoute.outer W M d F g₁) u ∂M.ν (.grid i j) := by
  first | exact @GlobalTheory.SmallRoute.zdeg_mul_liftT | exact GlobalTheory.SmallRoute.zdeg_mul_liftT | (intros; apply GlobalTheory.SmallRoute.zdeg_mul_liftT <;> assumption)
end
