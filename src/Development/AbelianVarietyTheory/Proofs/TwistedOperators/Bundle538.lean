module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicUnitaryProdLocalPointsMulLatticeStab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1482
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle520
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle528
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalStabilizerDoubledVacuumEigenvalueEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1230
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle503
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle177
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle521
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle522
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
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp

namespace GlobalTheory.SphGlob

theorem loc_mem_KAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (K : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J),
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat K *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat K⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    GlobalTheory.FinDecomp.loc (GlobalTheory.FinDecomp.idem F v) (GlobalTheory.FinDecomp.idem_mul_self v) K ∈ GlobalTheory.InertSph.KAt σ W v := by
  intro F E _ _ _ _ _ σ d W v K hK

  have hfix : ∀ z ∈ GlobalTheory.InertSph.latAt W v, GlobalTheory.FinDecomp.idem F v • z = z := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, -, y, -, rfl⟩ := hz
      rw [smul_smul, GlobalTheory.FinDecomp.idem_mul_of_at ha]
    | zero => simp
    | add z z' _ _ h h' => rw [smul_add, h, h']
    | neg z _ h => rw [smul_neg, h]
  have hphi : ∀ (M : Matrix (Fin d) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), ∀ z ∈ GlobalTheory.InertSph.latAt W v,
      GlobalTheory.FinDecomp.phi (GlobalTheory.FinDecomp.idem F v) M *ᵥ z = M *ᵥ z := by
    intro M z hz
    have h1 : (1 - GlobalTheory.FinDecomp.idem F v) • z = 0 := by rw [sub_smul, one_smul, hfix z hz, sub_self]
    rw [GlobalTheory.FinDecomp.phi, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h1, zero_add,
      ← Matrix.mulVec_smul, hfix z hz]
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · show u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.FinDecomp.loc _ _ K) - 1) = 0
    rw [GlobalTheory.FinDecomp.mat_loc, GlobalTheory.FinDecomp.phi_sub_one, smul_smul, GlobalTheory.FinDecomp.mul_idem_of_evFin hu, zero_smul]
  · rw [GlobalTheory.FinDecomp.mat_loc, GlobalTheory.FinDecomp.mat_loc_inv, hphi _ z hz, hphi _ z hz]
    exact hK z hz

end GlobalTheory.SphGlob

namespace GlobalTheory.SphGlob


open scoped Classical in
theorem ev_mem_adm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (x : κ → AF F) :
    (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (GlobalTheory.WeilM.adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • (BoundedContinuousFunction.evalCLM ℂ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  simp only [LinearMap.proj_apply, GlobalTheory.WeilM.pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
  rw [mul_comm]

end GlobalTheory.SphGlob


open GlobalTheory.SphGlob in
theorem GlobalTheory.SphGlob.fixes_pure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))),
    0 < n → X.L.IsFullLattice E → W.L.IsLattice E → M.IsGood ψ → M.IsWeil ψ χX χW om →
    (∀ v, v ∉ S → ∀ k ∈ GlobalTheory.InertSph.KAt σ W v,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, k)) (M.vac v) (M.vac v)) →
    ∀ k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J,
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w, w ∉ S → ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W w) →
    ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ),
      (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F w)) → (∀ w, w ∉ S → φ w = M.vac w) →
      om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  classical
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om S hn hXL hWL hM hw hAct k hinf hS hlat f φ hSB hφ

  have hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    filter_upwards [hM.std, S.finite_toSet.eventually_cofinite_notMem] with w hw hwS
    rw [hφ w hwS, hw]
  set Φ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ with hΦ

  have hloc : ∀ v, v ∉ S → ∀ h ∈ GlobalTheory.InertSph.KAt σ W v, om (1, h) Φ = Φ := by
    intro v hv h hh
    obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
    have e1 : Φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) (φ v) r := by rw [hΦ, hrt, Function.update_eq_self]
    have hRest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) (φ v) r :=
      ⟨hr, by rw [← e1]; exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
    have hA := hAct v hv h hh
    rw [← hφ v hv] at hA
    rw [e1, hA r hRest]

  have hcut : ∀ v, v ∉ S → loc (idem F v) (idem_mul_self v) k ∈ GlobalTheory.InertSph.KAt σ W v := by
    intro v hv
    refine loc_mem_KAt F E σ d W v k fun z hz => ⟨?_, ?_⟩
    · refine GlobalTheory.T.mem_adelicLatticeAtPlace_of_tensor_with_lattice F E n d X W v _ hn (by letI := hXL; infer_instance) fun x hx => ?_
      have h0 := GlobalTheory.InertSphStab.vecMulVec_mem X W v hx hz
      rw [← GlobalTheory.InertSphStab.vecMulVec_mul_transpose]
      exact (hlat v hv _).2 h0
    · refine GlobalTheory.T.mem_adelicLatticeAtPlace_of_tensor_with_lattice F E n d X W v _ hn (by letI := hXL; infer_instance) fun x hx => ?_
      have h0 := GlobalTheory.InertSphStab.vecMulVec_mem X W v hx hz
      refine (hlat v hv _).1 ?_
      rw [GlobalTheory.InertSphStab.vecMulVec_mul_transpose, Matrix.mulVec_mulVec, mat_mul_inv, Matrix.one_mulVec]
      exact h0
  have hcutS : ∀ v ∈ S, loc (idem F v) (idem_mul_self v) k = 1 := by
    intro v hv
    apply ua_ext
    rw [mat_loc, mat_one, ← sub_eq_zero, phi_sub_one]
    exact hS v hv _ fun u hu => by rw [smul_eq_mul, mul_idem_of_evFin hu]
  have hone : ∀ v, om (1, loc (idem F v) (idem_mul_self v) k) Φ = Φ := by
    intro v
    by_cases hv : v ∈ S
    · rw [hcutS v hv]; show om 1 Φ = Φ; rw [map_one]; rfl
    · exact hloc v hv _ (hcut v hv)
  have hlist : ∀ l : List (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
      om (1, (l.map fun v => loc (idem F v) (idem_mul_self v) k).prod) Φ = Φ := by
    intro l
    induction l with
    | nil => show om 1 Φ = Φ; rw [map_one]; rfl
    | cons v t ih =>
      rw [List.map_cons, List.prod_cons]
      have : ((1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J), loc (idem F v) (idem_mul_self v) k *
          (t.map fun v => loc (idem F v) (idem_mul_self v) k).prod) =
          (1, loc (idem F v) (idem_mul_self v) k) * (1, (t.map fun v => loc (idem F v) (idem_mul_self v) k).prod) := by
        simp
      rw [this, map_mul, Module.End.mul_apply, ih, hone]
  have hT : ∀ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), om (1, loc (idemS F T) (idemS_mul_self T) k) Φ = Φ := by
    intro T
    have e : loc (idemS F T) (idemS_mul_self T) k = (T.toList.map fun v => loc (idem F v) (idem_mul_self v) k).prod := by
      apply ua_ext
      rw [mat_prod_loc k _ T.nodup_toList, Finset.toList_toFinset, mat_loc]
    rw [e]; exact hlist _

  have hcont := hw.2.2
  have hΦA : Φ ∈ (GlobalTheory.WeilM.adeleClass F).sp (Fin n × Fin d) := GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd
  funext x
  have hc := hcont _ (ev_mem_adm x) Φ hΦA
  have ht : Filter.Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) =>
      ((1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J), loc (idemS F T) (idemS_mul_self T) k)) Filter.atTop (nhds (1, k)) :=
    tendsto_const_nhds.prodMk_nhds (GlobalTheory.T.tendsto_unitaryGroupIdempotentLocalization_finiteSets F E σ d W.J k hinf)
  have hlim : Filter.Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) =>
      (LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) (om (1, loc (idemS F T) (idemS_mul_self T) k) Φ))
      Filter.atTop (nhds ((LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) (om (1, k) Φ))) :=
    (hc.tendsto _).comp ht
  have hconst : (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) =>
      (LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) (om (1, loc (idemS F T) (idemS_mul_self T) k) Φ)) =
      fun _ => Φ x := by
    funext T; rw [hT T]; rfl
  rw [hconst] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacSiegelAny
open GlobalTheory.DblVacSiegel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piE_locIdele_self (P : HeightOneSpectrum (𝓞 E)) (y : (P.adicCompletion E)ˣ) :
    piE F P (locIdele F P y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = y := by
  classical
  change (finAdEquiv F E (finTens F E (locIdele F P y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) P = _
  rw [finTens_locIdele, GlobalTheory.CMVal.single_apply]
  exact Function.update_self _ _ _

theorem piE_locIdele_ne {P Q : HeightOneSpectrum (𝓞 E)} (h : Q ≠ P) (y : (P.adicCompletion E)ˣ) :
    piE F Q (locIdele F P y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 1 := by
  classical
  change (finAdEquiv F E (finTens F E (locIdele F P y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) Q = _
  rw [finTens_locIdele, GlobalTheory.CMVal.single_apply]
  exact Function.update_of_ne h _ _

theorem eq_one_of_comp {x : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ} (h1 : infTens F E x = 1) (h2 : ∀ P, piE F P (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 1) : x = 1 := by
  refine Units.ext (tens_ext (h1.trans (map_one _).symm) ((finAdEquiv F E).injective ?_))
  refine FiniteAdeleRing.ext _ fun P => ?_
  rw [Units.val_one, map_one, map_one]
  exact h2 P

theorem chr_eq_one_of_supp (χ : Chr F E) (S : Finset (HeightOneSpectrum (𝓞 E))) (hχ : ∀ P ∈ S, UnrAt χ P)
    (x : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ) (h1 : infTens F E x = 1) (hoff : ∀ P ∉ S, piE F P (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 1)
    (hu : ∀ P ∈ S, Valued.v (piE F P (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = 1) : χ x = 1 := by
  classical
  induction S using Finset.induction_on generalizing x with
  | empty =>
    rw [eq_one_of_comp h1 fun P => hoff P (Finset.notMem_empty P), map_one]
  | insert P S hPS ih =>
    let y : (P.adicCompletion E)ˣ := Units.map (piE F P).toMonoidHom x
    have hy : Formalism.L2.Host.IsUnitAt P y := hu P (Finset.mem_insert_self P S)
    have hl : χ (locIdele F P y) = 1 := Circle.ext (congrArg Units.val (hχ P (Finset.mem_insert_self P S) y hy))
    set x' := x * (locIdele F P y)⁻¹ with hx'
    have ex : (x' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) * (locIdele F P y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = x := by
      rw [hx', Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
    have hcomp : ∀ {R : Type} [CommRing R] (φ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* R), φ (locIdele F P y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 1 →
        φ (x' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = φ x := fun φ h => by rw [← ex, map_mul, h, mul_one]
    have hx : x = x' * locIdele F P y := by rw [hx', inv_mul_cancel_right]
    rw [hx, map_mul, hl, mul_one]
    refine ih (fun Q hQ => hχ Q (Finset.mem_insert_of_mem hQ)) x' ?_ (fun Q hQ => ?_) (fun Q hQ => ?_)
    · rw [hcomp _ (infTens_locIdele P y), h1]
    · by_cases hQP : Q = P
      · subst hQP
        have e := congrArg (piE F Q) ex
        rw [map_mul, piE_locIdele_self] at e
        have h0 : (piE F Q (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) ≠ 0 := (Units.map (piE F Q).toMonoidHom x).ne_zero
        exact mul_right_cancel₀ h0 (e.trans (one_mul _).symm)
      · rw [hcomp _ (piE_locIdele_ne hQP y)]
        exact hoff Q (by simp [hQP, hQ])
    · have hQP : Q ≠ P := fun h => hPS (h ▸ hQ)
      rw [hcomp _ (piE_locIdele_ne hQP y)]
      exact hu Q (Finset.mem_insert_of_mem hQ)

theorem finite_under_eq (v : Pl (F := F)) : {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) = v}.Finite := by
  have h0 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact v.ne_bot
  refine (Ideal.finite_factors h0).subset fun P hP => ?_
  simp only [Set.mem_setOf_eq] at hP ⊢
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← hP]
  exact le_rfl

theorem chr_det_eq_one_any {d : ℕ} (W : Spc F E d) (hL : W.L.IsFullLattice E) {v : Pl (F := F)} {χ : Chr F E}
    (hχ : ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v → UnrAt χ P) (t : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (h1 : At (evFin F v) ((t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1))
    (ht : ∀ z ∈ GlobalTheory.InertSph.latAt W v, (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧
      ((t⁻¹ : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    χ (Matrix.GeneralLinearGroup.det t) = 1 := by
  classical
  set δ := Matrix.GeneralLinearGroup.det t with hδ
  have hN := h1 (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
  have hφ : ∀ {R : Type} [CommRing R] (φ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* R),
      φ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1)) = 0 → φ (δ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 1 := by
    intro R _ φ hφ
    have : φ.mapMatrix (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = φ.mapMatrix 1 := by
      ext i j
      have h2 := congrArg φ (congrFun (congrFun hN i) j)
      rw [Matrix.smul_apply, Algebra.smul_def, map_mul, map_sub, map_sub, map_one, map_one, hφ, sub_zero, one_mul,
        Matrix.sub_apply, map_sub, Matrix.zero_apply, map_zero, sub_eq_zero] at h2
      exact h2
    rw [hδ, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det, this, map_one, Matrix.det_one]
  refine chr_eq_one_of_supp χ (finite_under_eq (E := E) v).toFinset
    (fun P hP => hχ P ((finite_under_eq v).mem_toFinset.1 hP)) δ (hφ _ (TensorProduct.zero_tmul _ _))
    (fun P hP => ?_) (fun P hP => ?_)
  · have hPv : P.under (𝓞 F) ≠ v := fun h => hP ((finite_under_eq v).mem_toFinset.2 h)
    refine hφ _ ?_
    rw [piE_algebraMap rfl]
    exact (congrArg _ (evalV_singleFin_ne hPv 1)).trans (map_zero _)
  · have hu : P.under (𝓞 F) = v := (finite_under_eq v).mem_toFinset.1 hP
    let y : (P.adicCompletion E)ˣ := Units.map (piE F P).toMonoidHom δ
    have a1 : Valued.v (y : P.adicCompletion E) ≤ 1 := val_det_le_one W hL hu _ fun z hz => (ht z hz).1
    have a2 : Valued.v ((y⁻¹ : (P.adicCompletion E)ˣ) : P.adicCompletion E) ≤ 1 := by
      have := val_det_le_one W hL hu _ fun z hz => (ht z hz).2
      rw [← Matrix.GeneralLinearGroup.val_det_apply, map_inv] at this
      exact this
    have h0 : 0 < Valued.v (y : P.adicCompletion E) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 y.ne_zero)
    rw [Units.val_inv_eq_inv_val, map_inv₀, inv_le_one₀ h0] at a2
    exact le_antisymm a1 a2

theorem eigen_eq_one_of_diag_any : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), v ∉ X.T →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.W →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M.co dd →
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.β (diagCols (Fin (a + a'))) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r → tens (evFin F v) (G.M.vac v) r ≠ 0 →
    ∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PDiag σ G.W → ∀ μ : ℂ,
      omd p (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) → μ = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv dd omd hdd hW r hr h0 p hp hpd μ hμ
  obtain ⟨t, ht₀⟩ := hpd
  have ht : GlobalTheory.DblVac.matD p * (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
      (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * (t : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := ht₀
  have hF := hT.base.cm.1
  set Ψ := tens (evFin F v) (G.M.vac v) r with hΨ
  have hS := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Ψ hr.2 _ (GlobalTheory.SchAConj.star_mem_schA F _ Ψ hr.2)
  have hl := lDiag_box_ne_zero hF hr.2 h0
  have hS0 : (boxFun Ψ fun x => star (Ψ x)) ≠ 0 := fun h => hl (by rw [h, map_zero])
  have hn := norm_eq_one_of_eigen hF hW.2.1.unit hS hS0 hμ
  have hrule := hW.2.2 _ DiagForm.lDiag_adm (fun z φ hφ => by
    have e : z * (diagCols (Fin (a + a')) : Matrix _ _ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ = Matrix.fromCols z z := by
      rw [diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols, Matrix.transpose_one, Matrix.mul_one]
    rw [e, Darboux.rho, hdd]
    exact DiagForm.lDiag_schr B.ψ _ _ hφ) p t ht _ hS
  have hvec : ∀ (g : GlobalTheory.DblVac.UD σ G.W) (s : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
      GlobalTheory.DblVac.matD g * (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * s → ∀ z,
      (GlobalTheory.DblVac.matD g *ᵥ Sum.elim z z) ∘ Sum.inl = s *ᵥ z := fun g s hs z => by
    have e : ∀ z : Fin (a + a') → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z = Sum.elim z z := fun z => by
      rw [diagCols, Matrix.fromRows_mulVec, Matrix.one_mulVec]
    rw [← e, Matrix.mulVec_mulVec, hs, ← Matrix.mulVec_mulVec, e]
    rfl
  have ht' : GlobalTheory.DblVac.matD p⁻¹ * (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
      (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * ((t⁻¹ : GL (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
    have e1 : GlobalTheory.DblVac.matD p⁻¹ * GlobalTheory.DblVac.matD p = 1 := p.1.inv_mul
    calc _ = GlobalTheory.DblVac.matD p⁻¹ * ((diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * (t : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) *
          ((t⁻¹ : GL (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, t.mul_inv, Matrix.mul_one]
      _ = _ := by rw [← ht, ← Matrix.mul_assoc, e1, Matrix.one_mul]
  have hβ : X.β (Matrix.GeneralLinearGroup.det t) = 1 := by
    refine chr_det_eq_one_any (v := v) G.W hT.geo.hW.lat (fun P hP => hT.chars.unrβ P fun h => hv (hP ▸ (h : P.under (𝓞 F) ∈ (X.T : Set (Pl (F := F)))))) t
      (fun u hu => ?_) fun z hz => ?_
    · have e1 : (GlobalTheory.DblVac.matD p - 1) * (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
          (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * ((t : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) := by
        rw [Matrix.sub_mul, Matrix.mul_sub, ht, Matrix.one_mul, Matrix.mul_one]
      have e2 : (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * (u • ((t : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1)) = 0 := by
        rw [Matrix.mul_smul, ← e1, ← Matrix.smul_mul, hp.1 u hu, Matrix.zero_mul]
      rw [diagCols, Matrix.fromRows_mul, Matrix.one_mul] at e2
      ext i j
      exact congrFun (congrFun e2 (Sum.inl i)) j
    · have hz' := hp.2 (Sum.elim z z) ⟨hz, hz⟩
      exact ⟨hvec p _ ht z ▸ hz'.1.1, hvec p⁻¹ _ ht' z ▸ hz'.2.1⟩
  have hrule' := (congrArg (DiagForm.lDiag F (Fin a × Fin (a + a'))) hμ).symm.trans hrule
  simp only [map_smul, smul_eq_mul, hβ, Circle.coe_one, one_mul] at hrule'
  have hμ' := mul_right_cancel₀ hl hrule'
  rw [hμ', Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)] at hn
  rw [hμ', hn, Complex.ofReal_one]

theorem eigen_eq_one_of_diag_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → v ∉ X.T → PsiUnr B.ψ v →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.W →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M.co dd →
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.β (diagCols (Fin (a + a'))) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r → tens (evFin F v) (G.M.vac v) r ≠ 0 →
    ∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PDiag σ G.W → ∀ μ : ℂ,
      omd p (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) → μ = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v _ hv _ dd omd hdd hW r hr h0 p hp hpd μ hμ
  exact eigen_eq_one_of_diag_any F E σ B a a' G X om om' hT v hv dd omd hdd hW r hr h0 p hp hpd μ hμ

end GlobalTheory.DblVacSiegelAny
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size


theorem _root_.GlobalTheory.T.average_preserves_K_finiteness : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ), IsAutFunSm θ N.V ψ → ∀ (τ τ' : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ') → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ') e → GlobalTheory.CuspKFin.KFinAt θ N τ ψ → GlobalTheory.CuspKFin.KFinAt θ N τ (GlobalTheory.SeriesToClosure.avg θ N.V τ' (N.M.ε τ') (N.M.fr τ') e ψ) := by
  first | exact @GlobalTheory.CuspKFin.kFinAt_avg_of_kFinAt | exact GlobalTheory.CuspKFin.kFinAt_avg_of_kFinAt | (intros; apply GlobalTheory.CuspKFin.kFinAt_avg_of_kFinAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

noncomputable section

namespace GlobalTheory.CuspKFinAvg

open Formalism.REAL Matrix

end GlobalTheory.CuspKFinAvg

namespace GlobalTheory.CuspKFin

open Formalism.REAL Matrix MeasureTheory

theorem kFinAt_avg : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ),
    IsAutFunSm θ N.V ψ → ∀ (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e →
    GlobalTheory.CuspKFin.KFinAt θ N τ (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ) := by
  first
  | exact @_root_.GlobalTheory.LeftRegularRepresentation.kFinAt_avg
  | exact _root_.GlobalTheory.LeftRegularRepresentation.kFinAt_avg
  | (apply _root_.GlobalTheory.LeftRegularRepresentation.kFinAt_avg <;> assumption)
  | (intros; apply _root_.GlobalTheory.LeftRegularRepresentation.kFinAt_avg <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LeftRegularRepresentation.kFinAt_avg <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LeftRegularRepresentation.kFinAt_avg ..)

end GlobalTheory.CuspKFin

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
open GlobalTheory.VacTransfer

theorem _root_.GlobalTheory.T.realPlaceComponent_archLine_complexStructure : ∀ (D : D7) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d),
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
    ∀ u u' : Matrix (Fin S.rank) (Fin d) (AE D),
      (∀ w, u'.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) =
        Complex.I • (Vs.θ w * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) * (Ws.θ w)ᵀ)) →
    ∀ τ, compAt θ τ (GlobalTheory.VacTransfer.archLine cS u' 1) =
      cplxO ((frSgn ε A).cart τ) (B.cart τ) (compAt θ τ (GlobalTheory.VacTransfer.archLine cS u 1)) := by
  first | exact @GlobalTheory.CartanLinTransfer.compAt_archLine_cplxO | exact GlobalTheory.CartanLinTransfer.compAt_archLine_cplxO | (intros; apply GlobalTheory.CartanLinTransfer.compAt_archLine_cplxO <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.forms_of_bounded_adelic_function_norm_bounded : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → ∀ f', C.IsBase Lv B f' → ∀ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (z φ : GA D T → ℂ), (∀ a ∈ GinfC T, RealScal C om B a (z a)) → (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → om (1, k) (C.uVec Lv hn f') = C.uVec Lv hn f' ∧ ∀ g, φ (g * k) = φ g) → ∀ (v₀ : Lt D.host.E T.rank → TF S.rank C.g) (μ : GL (Fin T.rank) D.host.E → Lt D.host.E T.rank → ℂ), (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → (∀ γ ∈ Lv.grp, ∀ L ∈ Lv.lats, ∀ k : Lv.J, Lv.Red (fun i => (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i) k → wG C.X C.bas C.idx γ (v₀ L) = (μ γ L * (Lv.lam k : ℂˣ)) • v₀ (mapL γ L)) → ∀ (ep : GA D S → ℂ) (cf : GA D T → ℂ), (∀ (h : GA D S) (Λ : Lt D.host.E S.rank) (g : GA D T) (L : Lt D.host.E T.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ‖ep h‖ = 1 ∧ ‖cf g‖ = 1 ∧ om (h, g) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) = (ep h * cf g) • (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L Λ))) → ∀ gL : Lt D.host.E T.rank → GA D T, (∀ L ∈ Lv.lats, gL L ∈ GfC T ∧ TrivAt T (C.under Lv) (gL L) ∧ IsMov (fmt T (gL L)) C.X.Λ L) → ∀ F : Lt D.host.E T.rank → Frame C.X.Ψ T.rank → ℂ, (∀ L ∈ Lv.lats, DifferentiableOn ℂ (F L) C.X.dom) → (∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, ∀ b ∈ Bor C.X.Ψ T.rank, F L (rmul x b) = bchar (wtOf C.X C.hr c c' S.rank) b * F L x) → (∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = z a * (ep 1 * cf (gL L)) * F L (C.xB (C.mvB a B))) → (∃ K : ℝ, ∀ g, ‖φ g‖ ≤ K) → ∃ K : ℝ, ∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, C.X.pnorm (wtOf C.X C.hr c c' S.rank) (F L) x ≤ K := by
  first | exact @GlobalTheory.AdSpan.BddForms.pnorm_le_of_bdd | exact GlobalTheory.AdSpan.BddForms.pnorm_le_of_bdd | (intros; apply GlobalTheory.AdSpan.BddForms.pnorm_le_of_bdd <;> assumption)
end
