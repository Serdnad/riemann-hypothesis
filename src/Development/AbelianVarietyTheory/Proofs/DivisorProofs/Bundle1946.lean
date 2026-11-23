module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1865
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1905
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def infHom (lam : InfinitePlace E → DomWeight n) : Submodule ℂ (Wsp lam →ₗ[ℂ] (UA E n → ℂ)) where
  carrier := {T | ∀ x ∈ infU E n, ∀ w, T (wInf lam x w) = RU E n x (T w)}
  add_mem' ha hb x hx w := by
    simp only [LinearMap.add_apply, ha x hx, hb x hx, map_add (f := _)]
  zero_mem' x _ w := by simp
  smul_mem' c T hT x hx w := by
    simp only [LinearMap.smul_apply, hT x hx, map_smul]

theorem RU_mul (a b : UA E n) (φ : UA E n → ℂ) : RU E n (a * b) φ = RU E n a (RU E n b φ) := by
  rw [map_mul]; rfl

theorem comp_mem_infHom (lam : InfinitePlace E → DomWeight n) {T : Wsp lam →ₗ[ℂ] (UA E n → ℂ)} (hT : T ∈ infHom lam)
    (k : finU (E := E) (n := n)) : RU E n k.1 ∘ₗ T ∈ infHom lam := by
  intro x hx w
  simp only [LinearMap.comp_apply, hT x hx, ← RU_mul, GlobalTheory.DefU.fin_mul_inf k.2 hx]

theorem exists_op (lam : InfinitePlace E → DomWeight n) (A : Module.End ℂ (Wsp lam)) :
    ∃ P : Module.End ℂ (UA E n → ℂ), ∀ T ∈ infHom lam, ∀ w, T (A w) = P (T w) := by
  have hA : A ∈ Submodule.span ℂ (Set.range fun x : infU E n => wInf lam (x : UA E n)) := by
    rw [GlobalTheory.T.span_infinitePlacesWeightRepresentation_eq_top E n lam]; exact Submodule.mem_top
  induction hA using Submodule.span_induction with
  | mem A h =>
    obtain ⟨x, rfl⟩ := h
    exact ⟨RU E n x.1, fun T hT w => hT x.1 x.2 w⟩
  | zero => exact ⟨0, fun T _ w => by simp⟩
  | add A B _ _ hA hB =>
    obtain ⟨P, hP⟩ := hA
    obtain ⟨Q, hQ⟩ := hB
    exact ⟨P + Q, fun T hT w => by simp [hP T hT, hQ T hT]⟩
  | smul c A _ hA =>
    obtain ⟨P, hP⟩ := hA
    exact ⟨c • P, fun T hT w => by simp [hP T hT]⟩

theorem eq_zero_of_sum (lam : InfinitePlace E → DomWeight n) {ι : Type} [Fintype ι] (b : Module.Basis ι ℂ (Wsp lam))
    (T : ι → Wsp lam →ₗ[ℂ] (UA E n → ℂ)) (hT : ∀ j, T j ∈ infHom lam) (h : ∑ j, T j (b j) = 0) (k : ι) :
    T k = 0 := by
  refine b.ext fun m => ?_
  obtain ⟨P, hP⟩ := exists_op lam ((b.coord k).smulRight (b m))
  have := congrArg P h

  rw [map_sum, map_zero] at this
  rw [LinearMap.zero_apply, ← this]
  rw [Finset.sum_eq_single k]
  · rw [← hP _ (hT k)]; simp
  · intro j _ hj
    rw [← hP _ (hT j)]
    simp [Module.Basis.coord_apply, Module.Basis.repr_self, hj]
  · simp

end GlobalTheory.BCT.TrKer

namespace GlobalTheory.BCT.TrKer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_span_values (lam : InfinitePlace E → DomWeight n) (π : Submodule ℂ (UA E n → ℂ)) (hπ : IsAutRepU π)
    (hW : ∀ v : InfinitePlace E, HasWeightAt π v.embedding (lam v)) {φ : UA E n → ℂ} (hφ : φ ∈ π) :
    φ ∈ Submodule.span ℂ {ψ | ∃ T ∈ infHom lam, (∀ w, T w ∈ π) ∧ ∃ w, T w = ψ} := by
  set Sv := Submodule.span ℂ {ψ | ∃ T ∈ infHom lam, (∀ w, T w ∈ π) ∧ ∃ w, T w = ψ}
  have hle : Sv ≤ π := Submodule.span_le.2 (by rintro _ ⟨T, -, hT, w, rfl⟩; exact hT w)
  have hst : ∀ g, ∀ ψ ∈ Sv, RU E n g ψ ∈ Sv := by
    intro g ψ hψ
    induction hψ using Submodule.span_induction with
    | mem ψ h =>
      obtain ⟨T, hT, hTπ, w, rfl⟩ := h
      rw [eq_splitFin_mul_splitInf g, RU_mul, ← hT _ (splitInf E n g).2]
      exact Submodule.subset_span ⟨_, comp_mem_infHom lam hT (splitFin E n g),
        fun w' => hπ.stable _ _ (hTπ w'), _, rfl⟩
    | zero => simp
    | add a c _ _ ha hc => rw [map_add]; exact add_mem ha hc
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  obtain ⟨T, hT0, hTπ, hT⟩ := GlobalTheory.T.exists_ne_zero_weightTensor_intertwining_autRep E n lam π hπ hW
  obtain ⟨w, hw⟩ := DFunLike.ne_iff.1 hT0
  rcases hπ.irred Sv hle hst with h | h
  · have hm : T w ∈ Sv := Submodule.subset_span ⟨T, hT, hTπ, w, rfl⟩
    rw [h, Submodule.mem_bot] at hm
    exact absurd hm hw
  · rw [h]; exact hφ

theorem mem_range_of_mem (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (lam : InfinitePlace E → DomWeight n)
    (π : Submodule ℂ (UA E n → ℂ)) (hπ : IsAutRepU π) (hW : ∀ v : InfinitePlace E, HasWeightAt π v.embedding (lam v))
    {φ : UA E n → ℂ} (hφ : φ ∈ π) (hfix : φ ∈ fixed (RF E n) (globLev S K')) :
    φ ∈ LinearMap.range (Phi S lam K') := by
  classical
  let b := Module.finBasis ℂ (Wsp lam)
  have hdec : ∀ ψ ∈ Submodule.span ℂ {ψ | ∃ T ∈ infHom lam, (∀ w, T w ∈ π) ∧ ∃ w, T w = ψ},
      ∃ T : Fin (Module.finrank ℂ (Wsp lam)) → (Wsp lam →ₗ[ℂ] (UA E n → ℂ)),
        (∀ j, T j ∈ infHom lam) ∧ (∀ j w, T j w ∈ π) ∧ ψ = ∑ j, T j (b j) := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem ψ h =>
      obtain ⟨T, hT, hTπ, w, rfl⟩ := h
      refine ⟨fun j => b.repr w j • T, fun j => Submodule.smul_mem _ _ hT, fun j w' => π.smul_mem _ (hTπ w'), ?_⟩
      calc T w = T (∑ j, b.repr w j • b j) := by rw [b.sum_repr]
        _ = ∑ j, (b.repr w j • T) (b j) := by simp only [map_sum, map_smul, LinearMap.smul_apply]
    | zero => exact ⟨0, fun _ => zero_mem _, fun _ _ => π.zero_mem, by simp⟩
    | add a c _ _ ha hc =>
      obtain ⟨A, hA, hAπ, rfl⟩ := ha
      obtain ⟨C, hC, hCπ, rfl⟩ := hc
      exact ⟨A + C, fun j => add_mem (hA j) (hC j), fun j w => π.add_mem (hAπ j w) (hCπ j w),
        by simp [Finset.sum_add_distrib]⟩
    | smul c a _ ha =>
      obtain ⟨A, hA, hAπ, rfl⟩ := ha
      exact ⟨c • A, fun j => Submodule.smul_mem _ c (hA j), fun j w => π.smul_mem c (hAπ j w),
        by simp [Finset.smul_sum]⟩
  obtain ⟨T, hT, hTπ, rfl⟩ := hdec φ (mem_span_values lam π hπ hW hφ)
  have hfixT : ∀ k ∈ globLev S K', ∀ j, RU E n k.1 ∘ₗ T j = T j := by
    intro k hk j
    have h1 : RU E n k.1 (∑ j, T j (b j)) = ∑ j, T j (b j) := by
      have := hfix ⟨k, hk⟩
      simpa [RF] using this
    have h2 : ∑ i, (RU E n k.1 ∘ₗ T i - T i) (b i) = 0 := by

      simp only [LinearMap.sub_apply, LinearMap.comp_apply, Finset.sum_sub_distrib, ← map_sum, h1, sub_self]
    exact sub_eq_zero.1 (eq_zero_of_sum lam b _ (fun i => sub_mem (comp_mem_infHom lam (hT i) k) (hT i)) h2 j)
  obtain ⟨F, hFa⟩ : ∃ F : Fin (Module.finrank ℂ (Wsp lam)) → finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam),
      ∀ j x w, F j x w = T j w x.1 :=
    ⟨fun j x => LinearMap.proj (R := ℂ) (φ := fun _ : UA E n => ℂ) x.1 ∘ₗ T j, fun _ _ _ => rfl⟩
  have hphi : ∀ j, phiFun lam (F j) = T j := by
    intro j
    refine LinearMap.ext fun w => funext fun g => ?_
    rw [phiFun_apply, hFa]
    have hg := eq_splitFin_mul_splitInf g
    have hw : wInf lam g = wInf lam (splitInf E n g).1 := by
      conv_lhs => rw [hg]
      rw [map_mul, wInf_fin, one_mul]
    rw [hw, hT j _ (splitInf E n g).2]
    change T j w ((splitFin E n g).1 * (splitInf E n g).1) = T j w g
    rw [← hg]
  have hF : ∀ j, F j ∈ vecM S lam K' := by
    intro j
    refine ⟨fun γ x => ?_, fun k hk x => ?_⟩
    · refine LinearMap.ext fun w => ?_
      rw [LinearMap.dualMap_apply, hFa, hFa]
      obtain ⟨r, hr, hrf, hrc⟩ := GlobalTheory.T.exists_definiteUnitaryRationalPoint_finite_and_infinite_parts E n γ
      set i := splitInf E n r
      have hri : r = (finPt γ).1 * i.1 := by rw [← hrf]; exact eq_splitFin_mul_splitInf r
      have hc : ∀ v : InfinitePlace E, cEmb v.embedding (i.1⁻¹) = GeneralLinearGroup.map v.embedding (γ⁻¹).1 := by
        intro v
        have : i.1⁻¹ = r⁻¹ * (finPt γ).1 := by rw [hri]; group
        rw [this, map_mul, map_inv, hrc v, cEmb_fin, mul_one, Subgroup.coe_inv, map_inv]
      have hwi : wInf lam i.1⁻¹ = wAt lam γ⁻¹ := by
        change PiTensorProduct.map (fun v => GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb v.embedding i.1⁻¹)) = _
        unfold wAt
        simp only [hc]
      have hl := (hπ.aut _ (hTπ j w)).left r hr (i.1⁻¹ * x.1)
      rw [← hwi, hT j _ (inv_mem i.2)]
      change T j w ((finPt γ).1 * x.1) = T j w (x.1 * i.1⁻¹)
      rw [GlobalTheory.DefU.fin_mul_inf x.2 (inv_mem i.2), ← hl, hri]
      group
    · refine LinearMap.ext fun w => ?_
      rw [hFa, hFa]
      change T j w (x.1 * k.1) = T j w x.1
      exact congrFun (LinearMap.congr_fun (hfixT k hk j) w) x.1
  refine ⟨∑ j, ⟨F j, hF j⟩ ⊗ₜ b j, ?_⟩

  simp [map_sum, Phi_tmul, hphi]

theorem forms_le_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → forms S lam K' ≤ LinearMap.range (Phi S lam K') := by
  intro E _ _ _ _ n _ S _ lam K' _
  refine iSup_le fun π => iSup_le fun hπ => ?_
  rintro φ ⟨hφ, hfix⟩
  exact mem_range_of_mem S K' lam π hπ.1 hπ.2 hφ hfix

end GlobalTheory.BCT.TrKer

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.LatBound

theorem exists_mul_mem_integers {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    {T : Type} [Fintype T] (w : T → Fv F v) :
    ∃ c : Fv F v, c ≠ 0 ∧ ∀ t, c * w t ∈ v.adicCompletionIntegers F := by
  classical
  have key : ∀ x : Fv F v, ∃ c : Fv F v, c ≠ 0 ∧ c ∈ v.adicCompletionIntegers F ∧
      c * x ∈ v.adicCompletionIntegers F := by
    intro x
    by_cases hx : x ∈ v.adicCompletionIntegers F
    · exact ⟨1, one_ne_zero, one_mem _, by simpa using hx⟩
    · have hx0 : x ≠ 0 := by rintro rfl; exact hx (zero_mem _)
      refine ⟨x⁻¹, inv_ne_zero hx0, ?_, by rw [inv_mul_cancel₀ hx0]; exact one_mem _⟩
      exact ((v.adicCompletionIntegers F).mem_or_inv_mem x).resolve_left hx
  choose cw hcw0 hcwO hcw using key
  refine ⟨∏ t, cw (w t), Finset.prod_ne_zero_iff.2 fun t _ => hcw0 _, fun t => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ (fun t => cw (w t)) (Finset.mem_univ t), mul_comm (cw (w t)), mul_assoc]
  exact mul_mem (prod_mem fun t' _ => hcwO _) (hcw _)

theorem locCo_latAtV_bounded : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    {B : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → AF F}
    {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ), X.L.IsLattice E → Y.L.IsLattice E →
    ∃ c : Fv F v, c ≠ 0 ∧ ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v, ∀ i,
      c * (GlobalTheory.LatVac.locCo co v γ).1 i ∈ v.adicCompletionIntegers F ∧
      c * (GlobalTheory.LatVac.locCo co v γ).2 i ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ _ n d X Y v B κ _ co hX hY
  obtain ⟨M, _, g, hg⟩ := GlobalTheory.LatParam.latAtV_param X Y hX hY v
  obtain ⟨c, hc0, hc⟩ := exists_mul_mem_integers v
    (fun t : Bool × M × κ => if t.1 then (GlobalTheory.LatVac.locCo co v (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g t.2.1))).1 t.2.2
      else (GlobalTheory.LatVac.locCo co v (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g t.2.1))).2 t.2.2)
  have hsmul : ∀ (t : Fv F v) z, GlobalTheory.LatVac.locCo co v (GlobalTheory.EmbChart.atPlace v t • z) =
      t • GlobalTheory.LatVac.locCo co v z := by
    intro t z
    simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_smul]
    ext k <;> simp [smul_eq_mul, map_mul, GlobalTheory.EmbChart.evFin_atPlace]
  refine ⟨c, hc0, fun γ hγ i => ?_⟩
  obtain ⟨a, rfl⟩ := (hg γ).1 hγ

  simp only [map_sum, hsmul, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Prod.smul_fst, Prod.smul_snd,
  Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  constructor
  · refine sum_mem fun m _ => ?_
    rw [mul_left_comm]
    exact mul_mem (a m).2 (by simpa using hc (true, m, i))
  · refine sum_mem fun m _ => ?_
    rw [mul_left_comm]
    exact mul_mem (a m).2 (by simpa using hc (false, m, i))

end GlobalTheory.LatBound
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, (fun t : κ → Fv F v => Φ (fun i => GlobalTheory.LatVac.liftV v (t i))) ∈ GlobalTheory.WeilM.SB (κ → Fv F v) := by
  first | exact @GlobalTheory.LatVac.restrict_liftV_mem_SB | exact GlobalTheory.LatVac.restrict_liftV_mem_SB | (intros; apply GlobalTheory.LatVac.restrict_liftV_mem_SB <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.adelicTrace_supportedAtSplitPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (τ : E →ₐ[F] Fv F v) (z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) z = GlobalTheory.LatVac.liftV v (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ z + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) z) := by
  first | exact @GlobalTheory.SplitAdeleTrace.trace_at_split | exact GlobalTheory.SplitAdeleTrace.trace_at_split | (intros; apply GlobalTheory.SplitAdeleTrace.trace_at_split <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.PsiNontrivAt

theorem exists_psiAt_ne_one : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1 := by
  intro F _ _ ψ hψ w
  by_contra h
  push_neg at h
  refine GlobalTheory.PsiNontriv.psiAt_ne_one ψ hψ w ?_
  ext t
  rw [h t, AddChar.one_apply]

end GlobalTheory.PsiNontrivAt
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.archimedean_smooth_bump_with_trigonometric_expansion : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ (U : Set (κ → Ainf F)) (y : κ → AF F), IsOpen U → (fun i => (y i).1) ∈ U →
    ∃ β : (κ → Ainf F) → ℝ, Continuous β ∧ (∀ u, 0 ≤ β u ∧ β u ≤ 1) ∧ β (fun i => (y i).1) = 1 ∧
      (∀ u, β u ≠ 0 → u ∈ U) ∧
      ∃ (s : ℕ → Finset (κ → AF F)) (c : ℕ → (κ → AF F) → ℂ) (C : ℝ),
        (∀ n, ∀ b ∈ s n, ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), GlobalTheory.LatVac.liftV v 1 • b = 0) ∧
        (∀ n (x : κ → AF F), ‖∑ b ∈ s n, c n b * ψ (x ⬝ᵥ b)‖ ≤ C) ∧
        ∀ x : κ → AF F, Filter.Tendsto (fun n => ∑ b ∈ s n, c n b * ψ (x ⬝ᵥ b)) Filter.atTop
          (nhds ((β (fun i => (x i).1) : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.ArchTrigBump.arch_bump_trig | exact GlobalTheory.ArchTrigBump.arch_bump_trig | (intros; apply GlobalTheory.ArchTrigBump.arch_bump_trig <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.LatVac.DualLoc

variable {F : Type} [Field F] [NumberField F]

theorem form_smul_left {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux B κ) (u : AF F) (z γ : W) : B (u • z) γ = u * B z γ := by
  rw [co.form, co.form, map_smul]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul, mul_sub]

theorem at_form {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux B κ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {z : W}
    (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z) (γ : W) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (B z γ) := by
  intro u hu
  rw [smul_eq_mul, ← form_smul_left co, hz u hu, co.form]
  simp

theorem evFin_form {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux B κ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (z γ : W) :
    evFin F v (B z γ) = (GlobalTheory.LatVac.locCo co v z).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 -
      (GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v z).2 := by
  rw [co.form]

  simp only [dotProduct, map_sub, map_sum, map_mul]
  rfl

theorem psi_form {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux B κ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (ψ : AddChar (AF F) ℂ) {z : W}
    (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z) (γ : W) :
    ψ (B z γ) = GlobalTheory.LatVac.psiAt ψ v ((GlobalTheory.LatVac.locCo co v z).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 -
      (GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v z).2) := by
  rw [GlobalTheory.VacIndic.psi_of_at ψ (at_form co v hz γ), ← evFin_form co v z γ]
  rfl

theorem map_selfDual : ∀ {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {W : Type} [AddCommGroup W]
    [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ)
    (Λ : AddSubgroup W), (∀ γ ∈ Λ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) γ) →
    (∀ z : W, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → (z ∈ Λ ↔ ∀ γ ∈ Λ, ψ (B z γ) = 1)) →
    ∀ w : (κ → Fv F v) × (κ → Fv F v), w ∈ Λ.map (GlobalTheory.LatVac.locCo co v) ↔
      ∀ l ∈ Λ.map (GlobalTheory.LatVac.locCo co v), GlobalTheory.LatVac.psiAt ψ v (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1 := by
  intro F _ _ v W _ _ B κ _ co ψ Λ hat hdual w
  constructor
  · rintro ⟨z, hz, rfl⟩ l ⟨γ, hγ, rfl⟩
    rw [← psi_form co v ψ (hat z hz) γ]
    exact (hdual z (hat z hz)).1 hz γ hγ
  · intro hw
    obtain ⟨p, hp⟩ : ∃ p : (κ → AF F) × (κ → AF F),
        p = (fun k => GlobalTheory.LatVac.liftV v (w.1 k), fun k => GlobalTheory.LatVac.liftV v (w.2 k)) := ⟨_, rfl⟩
    have hzat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (co.e.symm p) := by
      intro u hu
      have hp0 : u • p = 0 := by
        subst hp
        refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
        · exact GlobalTheory.LatVac.at_liftV v (w.1 k) u hu
        · exact GlobalTheory.LatVac.at_liftV v (w.2 k) u hu
      rw [← map_smul, hp0, map_zero]
    have hloc : GlobalTheory.LatVac.locCo co v (co.e.symm p) = w := by
      subst hp
      refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
      · show evFin F v ((co.e (co.e.symm _)).1 k) = w.1 k
        rw [LinearEquiv.apply_symm_apply]
        exact GlobalTheory.LatVac.evFin_liftV v (w.1 k)
      · show evFin F v ((co.e (co.e.symm _)).2 k) = w.2 k
        rw [LinearEquiv.apply_symm_apply]
        exact GlobalTheory.LatVac.evFin_liftV v (w.2 k)
    have hz : co.e.symm p ∈ Λ := (hdual _ hzat).2 fun γ hγ => by
      rw [psi_form co v ψ hzat γ, hloc]
      exact hw _ ⟨γ, hγ, rfl⟩
    exact ⟨_, hz, hloc⟩

end GlobalTheory.LatVac.DualLoc
end
end
