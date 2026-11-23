module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle014
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.Bundle003
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.Bundle002
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.ExistsSchroedingerEigenvectorCompactCocycle
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.StandardTraceAdelicAddCharLocalComponentNeOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle019
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle022
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle040
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle030
import Development.WeilBound.CoreStatements.LocalThetaKernels.ExistsSmallSubgroups
import Development.WeilBound.CoreStatements.LocalThetaKernels.LinearIndependentOfNotMem
import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep
import Development.WeilBound.CoreStatements.LocalThetaKernels.LocrepAd
public import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA
public import Development.WeilBound.ThetaLifts.LatticeBasics.PairsB
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle006
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle012
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle019
public import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.AdelInt
public import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowDef
public import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle006
import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle005
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle002
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section



section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny
noncomputable section
namespace Tw.VacAny
open _root_.GlobalTheory _root_.GlobalTheory.VacAny

private theorem supported_sum {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} {ι : Type} (s : Finset ι) {f : ι → AF F}
    (h : ∀ i ∈ s, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (f i)) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (∑ i ∈ s, f i) := by
  intro u hu
  rw [Finset.smul_sum]
  exact Finset.sum_eq_zero fun i hi => h i hi u hu

private theorem supported_neg {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} {x : AF F}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) x) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (-x) := by
  intro u hu
  rw [smul_neg, h u hu, neg_zero]
private theorem supported_atPlace {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} (t : Fv F v) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (GlobalTheory.EmbChart.atPlace v t) := by
  intro u hu
  rw [smul_eq_mul, mul_comm, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]

private theorem supported_sub {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} {x y : AF F}
    (hx : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) x)
    (hy : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) y) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (x - y) := by
  intro u hu
  rw [smul_sub, hx u hu, hy u hu, sub_self]

private theorem evFin_invOf_two_local {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} :
    GlobalTheory.AdelicU.evFin F v (⅟(2 : AF F)) = ⅟(2 : Fv F v) := by
  refine (invOf_eq_right_inv ?_).symm
  have h : GlobalTheory.AdelicU.evFin F v (2 * ⅟(2 : AF F)) = 1 := by
    rw [mul_invOf_self, map_one]
  rwa [map_mul, map_ofNat] at h

private theorem supported_mul_right {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} {x : AF F}
    (hx : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) x) (y : AF F) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (x * y) := by
  intro u hu
  rw [smul_eq_mul, ← mul_assoc, show u * x = 0 from hx u hu, zero_mul]

private theorem supported_mul_left {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} (x : AF F) {y : AF F}
    (hy : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) y) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (x * y) := by
  rw [mul_comm]
  exact supported_mul_right hy x

theorem exists_isVac_any_darboux_k : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d)) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∃ φ, Model.IsVac (Model.mk (σ := σ) (X := X) (W := Y) co (fun _ => 0) 0 ∅) B.ψ v φ := by
  intro F E _ _ _ _ _ σ B hB n d X Y r s r' s' hX hY co v
  obtain ⟨θ, hθ⟩ := _root_.Tw.exists_int_add_conj_eq_one_of_base_good_k B hB
  obtain ⟨M, _, g, hΓ⟩ := Tw.LatParam.latAtV_param X Y hX.lat.toIsLattice hY.lat.toIsLattice v
  let γf : (M → v.adicCompletionIntegers F) → Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
    fun a => ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m)
  let u : M → (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) := fun m =>
    (fun i => GlobalTheory.AdelicU.evFin F v ((co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))).1 i),
     fun i => GlobalTheory.AdelicU.evFin F v ((co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))).2 i))
  let χ : (M → v.adicCompletionIntegers F) → ℂ := fun a => B.ψ (⅟(2 : AF F) *
    GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) (γf a) (γf a))
  have he : ∀ a, co.e (γf a) =
      ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m)) := by
    intro a

    simp only [γf, map_sum, map_smul]
  have hcomp : ∀ a i, (co.e (γf a)).1 i =
      ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) * (co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))).1 i ∧
      (co.e (γf a)).2 i =
      ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) * (co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))).2 i := by
    intro a i
    rw [he]
    simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, smul_eq_mul]
  have hAt : ∀ a i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) ((co.e (γf a)).1 i) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) ((co.e (γf a)).2 i) := by
    intro a i
    rw [(hcomp a i).1, (hcomp a i).2]
    exact ⟨supported_sum _ fun m _ => supported_mul_right (supported_atPlace _) _,
      supported_sum _ fun m _ => supported_mul_right (supported_atPlace _) _⟩
  have hev : ∀ a, ((fun i => GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).1 i)),
      (fun i => GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).2 i))) = ∑ m, (a m : Fv F v) • u m := by
    intro a
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)

    · simp [(hcomp a i).1, map_sum, map_mul, GlobalTheory.EmbChart.evFin_atPlace, Prod.fst_sum, Finset.sum_apply, u]

    · simp [(hcomp a i).2, map_sum, map_mul, GlobalTheory.EmbChart.evFin_atPlace, Prod.snd_sum, Finset.sum_apply, u]
  have hψ : ∀ z : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z →
      B.ψ z = GlobalTheory.VacAny.psiV B.ψ v (GlobalTheory.AdelicU.evFin F v z) := fun z hz => by
    rw [GlobalTheory.VacAny.psiV_apply, ← Tw.VacAny.eq_atPlace_of_at v z hz]
  have hzero : ∀ a, ∑ m, (a m : Fv F v) • u m = 0 → γf a = 0 := by
    intro a h
    rw [← hev a] at h
    have h1 : co.e (γf a) = 0 := by
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
      · rw [Tw.VacAny.eq_atPlace_of_at v _ (hAt a i).1, show GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).1 i) = 0 from
          congrFun (congrArg Prod.fst h) i, map_zero]
        rfl
      · rw [Tw.VacAny.eq_atPlace_of_at v _ (hAt a i).2, show GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).2 i) = 0 from
          congrFun (congrArg Prod.snd h) i, map_zero]
        rfl
    exact co.e.map_eq_zero_iff.1 h1
  have hker : ∀ a, ∑ m, (a m : Fv F v) • u m = 0 → χ a = 1 := by
    intro a h
    simp only [χ, hzero a h]
    simp [GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens]
  have hadd : ∀ a b, γf (a + b) = γf a + γf b := by
    intro a b
    simp only [γf]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show (((a + b) m : v.adicCompletionIntegers F) : Fv F v) = (a m : Fv F v) + b m from rfl, map_add (f := _), add_smul]
  have hmem : ∀ a, γf a ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v := fun a => (hΓ _).2 ⟨a, rfl⟩
  have hdot : ∀ a b, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) ((co.e (γf a)).1 ⬝ᵥ (co.e (γf b)).2) ∧
      GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).1 ⬝ᵥ (co.e (γf b)).2) =
        (∑ m, (a m : Fv F v) • u m).1 ⬝ᵥ (∑ m, (b m : Fv F v) • u m).2 := by
    intro a b
    refine ⟨supported_sum _ fun i _ => supported_mul_right (hAt a i).1 _, ?_⟩
    rw [← hev a, ← hev b]

    simp only [dotProduct, map_sum, map_mul]
  have hcoc : ∀ a b, χ (a + b) = χ a * χ b * GlobalTheory.VacAny.psiV B.ψ v
      (-(⅟(2 : Fv F v) * ((∑ m, (a m : Fv F v) • u m).1 ⬝ᵥ (∑ m, (b m : Fv F v) • u m).2 -
        (∑ m, (b m : Fv F v) • u m).1 ⬝ᵥ (∑ m, (a m : Fv F v) • u m).2))) := by
    intro a b
    simp only [χ]
    rw [hadd, _root_.Tw.VacCocycle.psi_half_symp_add_k B hB X Y r s r' s' hX hY θ hθ v _ (hmem a) _ (hmem b), co.form]
    congr 1
    have hz := supported_neg (supported_mul_left (⅟(2 : AF F))
      (supported_sub (hdot a b).1 (hdot b a).1))
    rw [hψ _ hz, map_neg, map_mul, map_sub, (hdot a b).2, (hdot b a).2, evFin_invOf_two_local]
  obtain ⟨φ, hφSB, hφ0, hφ⟩ := Tw.VacLoc.exists_schr_eigen v (GlobalTheory.VacAny.psiV B.ψ v) (GlobalTheory.VacAny.continuous_psiV hB.std.1 v)
    (Tw.PsiNontriv.psiV_ne_one B.ψ hB.std v) u χ (Tw.ContSymp.continuous_psi_symp_atPlace σ B.ψ hB.std.1 X.J Y.J (θ : E) v g) hker hcoc
  refine ⟨φ, hφSB, hφ0, θ, hθ, ?_⟩
  intro γ hγ
  obtain ⟨a, rfl⟩ := (hΓ γ).1 hγ
  intro rr hrr
  show GlobalTheory.WeilM.schr B.ψ (co.e (γf a)) _ = _
  rw [Tw.SchrLoc.schr_tens_of_at B.ψ v (co.e (γf a)) (fun i => (hAt a i).1) (fun i => (hAt a i).2) φ rr hrr.1, hev a, hφ a]
end Tw.VacAny
end
end
end

section



section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
open UpperTheory.TP
namespace UpperTheory.PolynomialDataFiniteKType₂
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
private theorem mat_inv_mul_pk {X : Spc F E n} (g : UA σ X.J) : mat g⁻¹ * mat g = 1 := by
  have : mat (g⁻¹ * g) = mat g⁻¹ * mat g := rfl
  rw [← this, inv_mul_cancel]; rfl
private theorem gInf_le_pk {W : Spc F E d} {k : UA σ W.J} (hk : k ∈ gInf σ W) : k ∈ UAt σ W (evI F) := by
  induction hk using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one =>
    intro u _
    have : mat (1 : UA σ W.J) = 1 := rfl
    rw [this, sub_self, smul_zero]
  | mul g h _ _ hg hh =>
    intro u hu
    have e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by
      have : mat (g * h) = mat g * mat h := rfl
      rw [this, sub_mul, one_mul]; abel
    rw [e, smul_add, ← Matrix.smul_mul, hg u hu, hh u hu, Matrix.zero_mul, add_zero]
  | inv g _ hg =>
    intro u hu
    have e : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by rw [mul_sub, mat_inv_mul_pk, mul_one, neg_sub]
    rw [e, smul_neg, ← Matrix.mul_smul, hg u hu, Matrix.mul_zero, neg_zero]
private noncomputable def pureL_pk {κ : Type} [Fintype κ] (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : SInf F κ →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun f := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ
  map_add' f g := funext fun x => by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
  map_smul' c f := funext fun x => by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]
end UpperTheory.PolynomialDataFiniteKType₂
open UpperTheory.PolynomialDataFiniteKType₂ in
theorem UpperTheory.exists_finiteDimensional_weil_archimedean_orbit :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → ∀ Φ ∈ PolData B M, ∃ V : Submodule ℂ (Fn F n d), FiniteDimensional ℂ V ∧ V ≤ schA F (Fin n × Fin d) ∧ ∀ k ∈ gInf σ W, om (1, k) Φ ∈ V := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om hP Φ hΦ
  have hK : ∀ k ∈ gInf σ W, k ∈ KInf σ W B.emb := fun k hk =>
    ⟨gInf_le_pk hk, fun w => by
      rw [GlobalTheory.ThK.Dbl.Prs.cartan_one (hP.skew.sig w) (hP.skew.cartan w)]
      exact Commute.one_right _⟩
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, φ, h1, h2, rfl⟩ := hx
    have hfin : {v | ¬ φ v = M.vac v}.Finite := h2
    have hD : GlobalTheory.ThK.Dbl.Prs.Dat B M hfin.toFinset f φ :=
      ⟨hf, h1, fun v hv => by simpa using hv⟩
    obtain ⟨g, hg, e⟩ := hD.pureA hP.good
    obtain ⟨U, hU, hU'⟩ := _root_.GlobalTheory.ThK.Dbl.polFin_k hP f hf
    refine ⟨U.map (pureL_pk φ), inferInstance, ?_, fun k hk => ?_⟩
    · rintro _ ⟨f', -, rfl⟩
      exact Submodule.subset_span ⟨f', g, hg, e f'⟩
    · obtain ⟨A, hA⟩ := _root_.GlobalTheory.ThK.Dbl.Prs.inf_op_k _root_.PositivityTheory.ThKF.A.archOp_k hP (hK k hk)
      have hact := (hA f hf).2
      exact ⟨A f, hU' k (hK k hk) _ hact, (hact _ (hD.rest hP.good)).symm⟩
  | zero => exact ⟨⊥, inferInstance, bot_le, fun k _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨V, h1, h2, h3⟩ := hx
    obtain ⟨V', h1', h2', h3'⟩ := hy
    exact ⟨V ⊔ V', inferInstance, sup_le h2 h2', fun k hk => by
      rw [map_add (f := _)]; exact Submodule.add_mem_sup (h3 k hk) (h3' k hk)⟩
  | smul c x _ hx =>
    obtain ⟨V, h1, h2, h3⟩ := hx
    exact ⟨V, h1, h2, fun k hk => by rw [map_smul]; exact V.smul_mem c (h3 k hk)⟩
end
end

section



section
noncomputable section
namespace PositivityTheory.ThKF0
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK
open PositivityTheory.ThKH.Locrep
theorem actsEx_k : _root_.GlobalTheory.ThK.ActsEx_k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v
  obtain ⟨ω, ρ, L⟩ := _root_.PositivityTheory.ThKH.Locrep.locRepEx_k F E σ n d B X W M om ⟨hP.base, ⟨r, s, hP.herm⟩, ⟨r', s', hP.skew⟩, hP.good, χX, χW, hP.weil⟩ v
  refine ⟨fun g hg h hh φ hφ => ⟨ω (g, h) φ, ⟨L.pres g hg h hh φ hφ, (L.acts g hg h hh φ hφ _).2 rfl⟩,
      fun φ₁ h₁ => (L.acts g hg h hh φ hφ _).1 h₁.2⟩,
    fun u hu φ hφ => ⟨ρ u φ, ⟨L.presH u hu φ hφ, (L.actsH u hu φ hφ _).2 rfl⟩,
      fun φ₁ h₁ => (L.actsH u hu φ hφ _).1 h₁.2⟩, fun φ hφ => ?_⟩
  have hs := IsUWeilPair.isUSplitting hP.weil
  obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base (Fin n × Fin d) v
  let loc : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v) := fun p => res v x₀ ∘ₗ om p ∘ₗ tensL v r₀
  have hloc : ∀ p : UA σ X.J × UA σ W.J, p.1 ∈ UAt σ X (evFin F v) → p.2 ∈ UAt σ W (evFin F v) → ∀ φ ∈ SB _,
      loc p φ = ω p φ := fun p h1 h2 φ hφ =>
    (eq_of_acts v h₁ (h₀ φ hφ) ((L.acts p.1 h1 p.2 h2 φ hφ _).2 rfl)).symm
  obtain ⟨K, hK1, hK2, hK3, hK4⟩ := exists_small_subgroups σ X v
  obtain ⟨K', hK1', hK2', hK3', hK4'⟩ := exists_small_subgroups σ W v
  obtain ⟨m, hm⟩ := smooth_of_weak (SB _) (fun k => (K k).prod (K' k))
    (fun a b hab => Subgroup.prod_mono (hK1 hab) (hK1' hab))
    (fun U hU => by
      obtain ⟨U₁, h1, U₂, h2, h⟩ := mem_nhds_prod_iff.1 hU
      obtain ⟨a, ha⟩ := hK2 U₁ h1
      obtain ⟨b, hb⟩ := hK2' U₂ h2
      exact ⟨max a b, fun p hp => h ⟨ha (hK1 (le_max_left a b) hp.1), hb (hK1' (le_max_right a b) hp.2)⟩⟩)
    loc (fun p hp φ hφ => by
      rw [hloc p (hK3 0 hp.1) (hK3' 0 hp.2) φ hφ]
      exact L.pres p.1 (hK3 0 hp.1) p.2 (hK3' 0 hp.2) φ hφ)
    (fun φ hφ => by
      rw [hloc 1 (one_mem_UAt X v) (one_mem_UAt W v) φ hφ]
      exact L.one φ hφ)
    (fun p hp q hq φ hφ => by
      rw [hloc (p * q) (mul_mem_UAt (hK3 0 hp.1) (hK3 0 hq.1)) (mul_mem_UAt (hK3' 0 hp.2) (hK3' 0 hq.2)) φ hφ,
        hloc q (hK3 0 hq.1) (hK3' 0 hq.2) φ hφ,
        hloc p (hK3 0 hp.1) (hK3' 0 hp.2) _ (L.pres q.1 (hK3 0 hq.1) q.2 (hK3' 0 hq.2) φ hφ)]
      exact L.mul p.1 (hK3 0 hp.1) p.2 (hK3' 0 hp.2) q.1 (hK3 0 hq.1) q.2 (hK3' 0 hq.2) φ hφ)
    (fun l φ hφ => hs.cont _ (res_adm v x₀ l) _ (h₀ φ hφ).2) φ hφ
  obtain ⟨U, hU, hUK⟩ := hK4 m
  obtain ⟨U', hU', hUK'⟩ := hK4' m
  refine ⟨U ×ˢ U', prod_mem_nhds hU hU', fun x hx h1 h2 => ?_⟩
  refine (L.acts x.1 h1 x.2 h2 φ hφ φ).2 ?_
  rw [← hloc x h1 h2 φ hφ]
  exact (hm x ⟨hUK _ hx.1 h1, hUK' _ hx.2 h2⟩).symm
end PositivityTheory.ThKF0
end
end
end

section



section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
open UpperTheory.TP
theorem UpperTheory.weilRep_mem_polynomialFock_of_archimedean :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → ∀ g ∈ UAt σ X (evI F), ∀ h ∈ UAt σ W (evI F), ∀ Φ ∈ PolData B M, om (g, h) Φ ∈ PolData B M := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om hp g hg h hh Φ hΦ
  obtain ⟨T, hT, hP⟩ := _root_.PositivityTheory.ThKF.A.archOp_k F E σ B n d X W M χX χW om n 0 d 0 hp g hg h hh
  have kg : g ∈ KInf σ X B.emb := ⟨hg, fun w => by
    rw [GlobalTheory.ThK.Dbl.Prs.cartan_one (hp.herm.sig w) (hp.herm.cartan w)]; exact Commute.one_right _⟩
  have kh : h ∈ KInf σ W B.emb := ⟨hh, fun w => by
    rw [GlobalTheory.ThK.Dbl.Prs.cartan_one (hp.skew.sig w) (hp.skew.cartan w)]; exact Commute.one_right _⟩
  refine Submodule.span_induction (p := fun Φ _ => om (g, h) Φ ∈ PolData B M) ?_ (by simp)
    (fun x y _ _ a b => by rw [map_add]; exact add_mem a b)
    (fun c x _ a => by rw [map_smul]; exact Submodule.smul_mem _ c a) hΦ
  rintro _ ⟨f, f1, φ, f2, f3, rfl⟩
  obtain ⟨ξ, hξ, e⟩ := PositivityTheory.ThKG.pure_eq_pureA hp.good φ f2 f3
  rw [e f, hT.1 f ξ hξ, ← e (T f)]
  exact Submodule.subset_span ⟨T f, hP kg kh f f1, φ, f2, f3, rfl⟩
end
end

section



section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Bad
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKG.Loc (idem)
open PositivityTheory.ThKG.Loc.Cone
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
variable {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}
theorem orth_k (P : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s') {ν} (hν : @Measure.IsAddHaarMeasure _ _ _ (borel _) ν) {Φ} (h : Φ ∈ schA F _)
    (h0 : Φ ≠ 0) {g u} {c c' : ℂ} (hc : c ≠ c') (h1 : M.co.rho B.ψ u Φ = c • Φ) (h2 : M.co.rho B.ψ (mat g * u) Φ = c' • Φ) :
    coef om ν Φ g = 0 := by
  by_contra hn
  have i := P.weil.isUSplitting.impl (g, 1) u Φ h
  rw [h1, map_smul, show actAB (cA σ) (g, 1) u = mat g * u from (congrArg _ Matrix.transpose_one).trans (Matrix.mul_one _)] at i
  have a1 := schr_unit P.base.std ν hν (M.co.e (mat g * u)) (om (g, 1) Φ) Φ
  have a2 := schr_unit P.base.std ν hν (M.co.e (mat g * u)) Φ Φ
  have k : ∀ (A : Fn F n d) (t : ℂ), ∫ x, (t • A) x * star ((c' • Φ) x) ∂ν = t * star c' * ∫ x, A x * star (Φ x) ∂ν := fun A t => by
    rw [← integral_const_mul]
    exact integral_congr_ae (.of_forall fun x => by simp only [Pi.smul_apply, smul_eq_mul, star_mul']; ring)
  rw [show schr B.ψ (M.co.e (mat g * u)) Φ = _ from h2] at a1 a2
  rw [show schr B.ψ (M.co.e (mat g * u)) (om (g, 1) Φ) = _ from i.symm, k] at a1
  rw [k] at a2
  have b1 := (mul_eq_right₀ hn).1 a1
  have b2 := (mul_eq_right₀ (sq_ne ν hν h h0)).1 a2
  exact hc (mul_right_cancel₀ (right_ne_zero_of_mul_eq_one b1) (b1.trans b2.symm))
theorem law_k {dd om₂ S l} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (h : IsDbl (σ := σ) (A := W) (Y := X) (κ := (Fin n × Fin d) ⊕ (Fin n × Fin d)) B.ψ dd χW om₂ S l)
    {Ψ} (hΨ : Ψ ∈ schA F _) : Law χW (d / 2) fun x => l (om₂ x Ψ) := fun p t x hp => by
  have := hB.cm.1
  beta_reduce
  rw [map_mul, Module.End.mul_apply, h.weil.2.2 l h.adm h.kill p t hp _ (h.weil.2.1.pres x Ψ hΨ), PositivityTheory.ThKF0.Chr.absE_eq,
    Complex.ofReal_cpow (NNReal.coe_nonneg _), Fintype.card_fin]
  push_cast
  rfl
end GlobalTheory.ThK.Dbl.Bad
end
end
end

section



section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
noncomputable section
namespace PositivityTheory.ThKF0
theorem thetaSum_rational_pair_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP γ hγ γ' hγ' Φ hΦ
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have hX : X.J.det ≠ 0 := rat_det_ne_zero_of_map X.J (B.emb w).1 (rat_det_ne_zero_of_hasSig _ (hP.herm.sig w))
  have hW : W.J.det ≠ 0 := by
    refine rat_det_ne_zero_of_map W.J (B.emb w).1 fun h0 => rat_det_ne_zero_of_hasSig _ (hP.skew.sig w) ?_
    rw [Matrix.det_smul, h0, mul_zero]
  exact darboux_coordinates_rational_exist F E σ hP.base.cm B.ψ hP.base.std n d X.J W.J hP.herm.herm hX hP.skew.skew hW M.co
    hP.good.rat χX χW hP.hX hP.hW om hP.weil γ hγ γ' hγ' Φ hΦ
end PositivityTheory.ThKF0
end
end
end

section



section
noncomputable section
namespace PositivityTheory.ThKF0.Grow
open scoped Matrix NNReal ENNReal Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}
open GlobalTheory.LFun GlobalTheory.ThK in
theorem schwartz_decay_uniform (hA : HtBd) (hF : FinInv) (hS : Sob) (hT : TrBd) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ g h (x : Fin n × Fin d → AF F),
    ‖om (g, h) Φ x‖ * (1 + ‖fun i => evI F (x i)‖) ^ N ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ N
  obtain ⟨C, -, hC⟩ := hA F E σ n d X W M
  obtain ⟨C', k, -, h⟩ := weighted hF hS hT hP.base.std hΦ N
  refine ⟨C' * C ^ k, k, fun g g' x => ?_⟩
  obtain ⟨m, h1, h2, h3⟩ := hC g g'
  rw [mul_assoc, ← mul_pow]
  exact h _ _ m _ h1 h2 (impl_sOf hP.weil g g') h3 x
end PositivityTheory.ThKF0.Grow
end
end
end
