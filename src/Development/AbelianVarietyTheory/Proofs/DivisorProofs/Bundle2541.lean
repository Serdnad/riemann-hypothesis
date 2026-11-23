module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1244
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1358
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2335
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle002
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle451

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SumSize GlobalTheory.FunObj.AaCoef
open GlobalTheory.RowClaim GlobalTheory.ArchTens ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.ArchTens.VolSize

theorem abs_zpow_le {q : ℕ} (hq : q ≠ 0) {z : ℤ} {A : ℝ} (h : |(z : ℝ)| ≤ A) :
    |(((q : ℚ) ^ z : ℚ) : ℝ)| ≤ Real.exp (A * Real.log q) := by
  have h0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have e : (((q : ℚ) ^ z : ℚ) : ℝ) = Real.exp ((z : ℝ) * Real.log q) := by
    rw [← Real.log_zpow, Real.exp_log (zpow_pos h0 z)]
    push_cast
    rfl
  rw [e, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ((le_abs_self _).trans h) (Real.log_natCast_nonneg _))

theorem prod_zpow_sum {q : ℚ} (hq : q ≠ 0) {ι : Type} (s : Finset ι) (z : ι → ℤ) : ∏ i ∈ s, q ^ z i = q ^ ∑ i ∈ s, z i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hq]

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem coef_le_of_chosen {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) {P : Pl D.host.E} (hP : P ∈ G.pl.W0)
    (hl : P ∈ locPl G t) {β : CosFam G t} (hβ : β ∈ S.supp t Φ) :
    |((S.term t Φ β ⟨P, hl⟩).coef : ℝ)| ≤
      Real.exp ((D.R.m : ℝ) ^ 3 * bigN D * cosExp G P * Real.log (resCard (Kw P) : ℕ)) := by
  classical
  have hs : 1 ≤ (locGrid G t P).s := one_le_sLen
  have hkeep : keepAt G P = false := by simp [keepAt, hP]
  have hdep : depthAt G P = cosExp G P := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
    obtain ⟨h1, h2⟩ := depthAt_w G hv
    rw [h1, h2]
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := ((Good.locGrid_isGood hL G W t hde hc).1 P hl).square 0 hm 0 hm
  haveI := (isUnitVol_unitVol P).1
  have hT := isTensor_Tflip hL W S.B t Φ hde hc hl
  rw [hdep] at hT
  have hO := oneCoset hs (psiAt W P) (unitVol P) (givenLevel G t P) (Tflip W S.B t Φ P) (unifAt P) (cosExp G P) D.R.m_even
    (isUnif_unifAt P) h00.cond hT (fun j hj _ => givenLevel_KO G t P hj)
  have hb := hβ ⟨P, hl⟩
  have hb' : β ⟨P, hl⟩ ∈ unfSupport (psiAt W P) (unitVol P) false
      (Reps.through hs (givenLevel G t P) (stair (locGrid G t P) (unifAt P) (cosExp G P))) (Tflip W S.B t Φ P) := by
    have : keepAt G (⟨P, hl⟩ : locPl G t).1 = false := hkeep
    rw [this] at hb
    exact hb
  have hβ' := funext (hO _ hb')
  have hz : ∀ i : Fin ((locGrid G t P).m - 2), ∃ z : ℤ,
      invVol (conjLevel hs (givenLevel G t P) ((repsAt G t P).elt (β ⟨P, hl⟩)) (j := i + 1) (by omega)) =
        (resCard (Kw P) : ℚ) ^ z ∧ |z| ≤ (bigN D : ℤ) * ((D.R.m : ℤ) * ((cosExp G P : ℤ) * (D.R.m : ℤ))) := fun i =>
    factor_stair G t P hs (cosExp G P) _ (Nat.succ_pos _) _ (by
      rw [hβ']
      exact through_elt _ (by omega))
  choose z hz hzb using hz
  have hq : resCard (Kw P) ≠ 0 := resCard_ne P
  have e : (S.term t Φ β ⟨P, hl⟩).coef = (resCard (Kw P) : ℚ) ^ (∑ i, z i) := by
    rw [← prod_zpow_sum (by exact_mod_cast hq)]
    refine Eq.trans ?_ (Finset.prod_congr rfl fun i _ => hz i)
    rfl
  rw [e]
  refine abs_zpow_le hq ?_
  have hm2 : (((locGrid G t P).m - 2 : ℕ) : ℤ) ≤ D.R.m := by
    have : (locGrid G t P).m - 2 ≤ D.R.m := by show D.R.m - 2 ≤ D.R.m; omega
    exact_mod_cast this
  have key : |∑ i, z i| ≤ (D.R.m : ℤ) ^ 3 * bigN D * cosExp G P :=
    calc |∑ i, z i| ≤ ∑ i, |z i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin ((locGrid G t P).m - 2), (bigN D : ℤ) * ((D.R.m : ℤ) * ((cosExp G P : ℤ) * (D.R.m : ℤ))) :=
        Finset.sum_le_sum fun i _ => hzb i
      _ = (((locGrid G t P).m - 2 : ℕ) : ℤ) * ((bigN D : ℤ) * ((D.R.m : ℤ) * ((cosExp G P : ℤ) * (D.R.m : ℤ)))) := by simp
      _ ≤ (D.R.m : ℤ) * ((bigN D : ℤ) * ((D.R.m : ℤ) * ((cosExp G P : ℤ) * (D.R.m : ℤ)))) :=
        mul_le_mul_of_nonneg_right hm2 (by positivity)
      _ = _ := by ring
  exact_mod_cast key

theorem exponent_le (P : Pl D.host.E) {C : ℝ} (hC : 2 ≤ C) :
    (D.R.m : ℝ) ^ 3 * bigN D * cosExp G P * Real.log (resCard (Kw P) : ℕ) ≤
      C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * placeSz G P := by
  have h1 := log_absNorm_le P
  have hS := placeSz_nonneg G P
  have hmN : (D.R.m : ℝ) ≤ bigN D := by exact_mod_cast m_le_bigN
  rw [ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.ResCardPlace.resCard_Kw]
  have h2 : (cosExp G P : ℝ) * Real.log (Ideal.absNorm P.asIdeal : ℕ) ≤ C * placeSz G P :=
    calc (cosExp G P : ℝ) * Real.log (Ideal.absNorm P.asIdeal : ℕ)
        ≤ (cosExp G P : ℝ) * (2 * Real.log (Ideal.absNorm (P.under (𝓞 D.host.F)).asIdeal)) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      _ = 2 * placeSz G P := by rw [placeSz]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC hS
  have h3 : (D.R.m : ℝ) ^ 3 * bigN D ≤ (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 :=
    calc (D.R.m : ℝ) ^ 3 * bigN D = (D.R.m : ℝ) ^ 2 * bigN D * D.R.m := by ring
      _ ≤ (D.R.m : ℝ) ^ 2 * bigN D * bigN D := mul_le_mul_of_nonneg_left hmN (by positivity)
      _ = _ := by ring
  calc _ = ((D.R.m : ℝ) ^ 3 * bigN D) * ((cosExp G P : ℝ) * Real.log (Ideal.absNorm P.asIdeal : ℕ)) := by ring
    _ ≤ ((D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2) * (C * placeSz G P) :=
      mul_le_mul h3 h2 (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)) (by positivity)
    _ = _ := by ring

end GlobalTheory.ArchTens.VolSize

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DblSchr

open Matrix

section Gen

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

theorem actAB_one_reG (e : γ ≃ β) {JA : Matrix α α E} {J : Matrix β β E} {J' : Matrix γ γ E} (h : J' = J.submatrix e e)
    (g : GlobalTheory.WeilM.UG c J) (w : Matrix α β E) :
    GlobalTheory.WeilM.actAB c ((1 : GlobalTheory.WeilM.UG c JA), reG c e h g) (w.submatrix id e) =
      (GlobalTheory.WeilM.actB c g w).submatrix id e := by
  simp only [GlobalTheory.WeilM.actAB, GlobalTheory.WeilM.actB, reG_val, OneMemClass.coe_one, Units.val_one, Matrix.one_mul,
    Matrix.transpose_submatrix]
  exact Matrix.submatrix_mul_equiv _ _ _ _ _

theorem continuous_reG [TopologicalSpace E] (e : γ ≃ β) {J : Matrix β β E} {J' : Matrix γ γ E}
    (h : J' = J.submatrix e e) : Continuous (reG c e h) := by
  unfold reG
  refine Continuous.subtype_mk ?_ _
  refine (Continuous.units_map (Matrix.reindexAlgEquiv E E e.symm).toAlgHom.toMonoidHom ?_).comp continuous_subtype_val
  exact (continuous_id (X := Matrix β β E)).matrix_reindex e.symm e.symm

end Gen

section Read

variable {D : D7} [Invertible (2 : AF D.host.F)]

theorem dblD_rho_eq {S T : HSp D} {ξ : AF D.host.F ⊗[D.host.F] D.host.E} {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E}
    {JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ)
    (ψ : AddChar (AF D.host.F) ℂ) (w : Matrix (Fin T.rank) (Fin S.rank ⊕ Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) :
    (dblD _ co).rho ψ w = (ddr co).rho ψ (w.submatrix id finSumFinEquiv.symm) := by
  unfold GlobalTheory.WeilM.Darboux.rho ddr
  rw [reD_e, Matrix.submatrix_submatrix]
  simp

end Read

end GlobalTheory.DblSchr

namespace GlobalTheory.DblSchr



theorem isUSplitting_omdOf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
          ∀ omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (GlobalTheory.DblSchr.JBd S JB)) →*
              Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.DblSchr.ddr co) ωd omd₀ →
          GlobalTheory.WeilM.IsUSplitting (GlobalTheory.WeilM.adeleClass D.host.F) ψ (GlobalTheory.DblSchr.dblD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co)
            (GlobalTheory.WeilM.actB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)) (GlobalTheory.DblSchr.omdOf omd₀) := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hξ κ _ co hco ωd hωd omd₀ htr
  have h1 : IsHeckeChar D 1 := ⟨continuous_const, fun _ => rfl⟩
  have r1 : ResEta D 1 (GlobalTheory.Doubling.dblSp S).rank := GlobalTheory.Core.Rk.IP.FockModel.resEta_one_dbl S rT
  have hξd := GlobalTheory.DblSchr.dblGram_xi D S JB ξ hξ
  have hrat := GlobalTheory.DblSchr.ddr_rat D S T JA JB ξ κ co hco
  obtain ⟨hpres, himpl⟩ := GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D ψ hψ (GlobalTheory.Doubling.dblSp S) T 1 χT h1 hT r1 rT JA (JBd S JB) ξ hJA hξd
    (κ ⊕ κ) (ddr co) hrat ωd hωd omd₀ htr
  have hadm := GlobalTheory.T.transportedWeilDatum_keeps_admissible_forms D ψ hψ (GlobalTheory.Doubling.dblSp S) T 1 χT h1 hT r1 rT JA (JBd S JB) ξ hJA hξd
    (κ ⊕ κ) (ddr co) hrat ωd hωd omd₀ htr
  have hunit := GlobalTheory.T.transportedWeilDatum_isUnitary_adelicSchwartz D ψ hψ (GlobalTheory.Doubling.dblSp S) T 1 χT h1 hT r1 rT JA (JBd S JB) ξ hJA hξd
    (κ ⊕ κ) (ddr co) hrat ωd hωd omd₀ htr
  have hcont := GlobalTheory.T.continuous_transported_weilDatum_adelicSchwartz D ψ hψ (GlobalTheory.Doubling.dblSp S) T 1 χT h1 hT r1 rT JA (JBd S JB) ξ hJA hξd
    (κ ⊕ κ) (ddr co) hrat ωd hωd omd₀ htr
  have hom : ∀ g, omdOf omd₀ g = omd₀ (1, reG _ finSumFinEquiv.symm (incM_JBd S JB) g) := fun _ => rfl
  refine { pres := ?_, impl := ?_, adm := ?_, unit := ?_, cont := ?_ }
  · intro g φ hφ
    rw [hom]
    exact hpres _ φ hφ
  · intro g w φ hφ
    have e1 := dblD_rho_eq co ψ w
    have e2 := dblD_rho_eq co ψ (GlobalTheory.WeilM.actB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) g w)
    have e3 := himpl (1, reG _ finSumFinEquiv.symm (incM_JBd S JB) g) (w.submatrix id finSumFinEquiv.symm) φ hφ
    have e4 := actAB_one_reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (JA := incM D.host.F JA) (incM_JBd S JB) g w
    rw [e4] at e3
    rw [hom]
    exact (congrArg (fun f => omd₀ _ (f φ)) e1).trans (e3.trans (congrFun e2 _).symm)
  · intro g l hl
    rw [hom]
    exact hadm _ l hl
  · exact hunit.comp _
  · have hr := continuous_reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (incM_JBd S JB)
    have hp : Continuous fun g => ((1 : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA)),
        reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (incM_JBd S JB) g) := continuous_const.prodMk hr
    intro l hl φ hφ
    exact Continuous.congr ((hcont l hl φ hφ).comp hp) (fun g => rfl)

end GlobalTheory.DblSchr
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

noncomputable section

namespace GlobalTheory.UnfoldLoss.MovedChosen

section Local

variable {k : Type} [Field k] {G : Grid k}

theorem gdet_stair (hs : 1 ≤ G.s) (ϖ : kˣ) (e j : ℕ) :
    ∃ a : ℕ, gdet (stair G ϖ e j) = ϖ ^ a ∧ a ≤ G.rank (G.m, j) * (e * G.m) := by
  refine ⟨∑ a : Fin (G.rank (G.m, j)), e * (a.val + 1 - topRank G j), ?_, ?_⟩
  · rw [stair, gdet, det_diagGL, Finset.prod_pow_eq_pow_sum]
  · calc ∑ a : Fin (G.rank (G.m, j)), e * (a.val + 1 - topRank G j) ≤ ∑ _a : Fin (G.rank (G.m, j)), e * G.m :=
          Finset.sum_le_sum fun a _ => Nat.mul_le_mul_left _ (by have := topRank_add hs j; have := a.2; omega)
      _ = _ := by simp

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem gdet_elt (hs : 1 ≤ G.s) (J : G.Level) (ϖ : kˣ) (e : ℕ) (X : ℕ × ℕ) :
    ∃ a : ℕ, gdet ((Reps.through hs J (stair G ϖ e)).elt (fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) X) = ϖ ^ a ∧
      a ≤ G.rank X * (e * G.m) := by
  obtain ⟨i, j⟩ := X
  by_cases hi : i = G.m
  · subst hi
    by_cases hj : j + 2 ≤ G.m
    · borelize k
      rw [through_elt _ hj]
      exact gdet_stair hs ϖ e j
    · cases j with
      | zero =>
        rw [Reps.elt, onColumn_apply]
        exact gdet_stair hs ϖ e 0
      | succ i =>
        refine ⟨0, ?_, Nat.zero_le _⟩
        rw [Reps.elt, onColumn_apply]
        simp [show ¬ i < G.m - 2 by omega]
  · refine ⟨0, ?_, Nat.zero_le _⟩
    simp [Reps.elt, onColumn, hi]

theorem apow_half {ϖ : kˣ} (hϖ : IsUnif ϖ) (a n : ℕ) :
    apow (ϖ ^ a)⁻¹ ((n : ℂ) / 2) = ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (a * n) := by
  rw [apow_inv, apow_pow, hϖ.apow_eq, neg_neg, mul_comm a n, pow_mul]
  congr 1
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg _), ← Complex.cpow_mul_nat]
  push_cast
  congr 1
  ring

end Local

section Val

variable {D : D7}

theorem lossLe_mul {w : PlL D} {z z' : ℂ} {a a' : ℝ} (h : LossLe w z a) (h' : LossLe w z' a') :
    LossLe w (z * z') (a + a') := by
  obtain ⟨y, rfl, hy⟩ := h
  obtain ⟨y', rfl, hy'⟩ := h'
  refine ⟨y * y', map_mul _ _ _, ?_⟩
  by_cases h0 : y = 0
  · exact Or.inl (by simp [h0])
  by_cases h0' : y' = 0
  · exact Or.inl (by simp [h0'])
  refine Or.inr ?_
  have h1 := hy.resolve_left h0
  have h2 := hy'.resolve_left h0'
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ h0 h0', Int.cast_add]
  linarith

theorem lossLe_list_prod {w : PlL D} {ι : Type} (f : ι → ℂ) (a : ℝ) (l : List ι) (h : ∀ b ∈ l, LossLe w (f b) a) :
    LossLe w (l.map f).prod (l.length * a) := by
  induction l with
  | nil => exact ⟨1, by simp, Or.inr (by simp [Formalism.DivisionValues.ValuationRepresentative.vw_one])⟩
  | cons b l ih =>
    rw [List.map_cons, List.prod_cons]
    refine (lossLe_mul (h b (by simp)) (ih fun c hc => h c (by simp [hc]))).mono (le_of_eq ?_)
    simp only [List.length_cons]
    push_cast
    ring

theorem lossLe_sqrt {w : PlL D} {q : ℕ} (hq : q ≠ 0) (hs : ((Real.sqrt q : ℝ) : ℂ) ∈ Set.range D.what₂.embLL) (n n' : ℕ) :
    LossLe w (((Real.sqrt q : ℝ) : ℂ) ^ n * (((Real.sqrt q : ℝ) : ℂ) ^ n')⁻¹) (n' * (vw w (q : D.what₂.LL) : ℝ) / 2) := by
  obtain ⟨y, hy⟩ := hs
  have h2 : y ^ 2 = (q : D.what₂.LL) := D.what₂.embLL.injective (by
    rw [map_pow, hy, map_natCast, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast])
  have hy0 : y ≠ 0 := by
    rintro rfl
    have : (q : D.what₂.LL) = 0 := by rw [← h2]; simp
    exact hq (by exact_mod_cast this)
  have hv : (vw w (q : D.what₂.LL) : ℝ) = 2 * vw w y := by
    rw [← h2, ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_npow w hy0]
    push_cast
    ring
  have hv0 : (0 : ℝ) ≤ (vw w (q : D.what₂.LL) : ℝ) := by exact_mod_cast ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_nat_nonneg w q
  refine ⟨y ^ n * (y ^ n')⁻¹, by rw [map_mul, map_inv₀, map_pow, map_pow, hy], Or.inr ?_⟩
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (pow_ne_zero _ hy0) (inv_ne_zero (pow_ne_zero _ hy0)), Formalism.DivisionValues.ValuationRepresentative.vw_inv,
    ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_npow w hy0, ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_npow w hy0, hv]
  rw [hv] at hv0
  have : (0 : ℝ) ≤ (n : ℝ) * vw w y := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  push_cast
  linarith

theorem rank_le {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (P : Pl D.host.E) {i j : ℕ}
    (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) : (locGrid G t P).rank (i, j) ≤ bigN D := by
  have h1 := Nat.mul_le_mul_right D.R.t hj
  have h2 := Nat.mul_le_mul_right (sLen D) hi
  have hr : D.R.r ≤ D.R.k + D.R.m := by
    have : D.R.r = D.R.k + D.R.m - 1 := rfl
    omega
  change D.R.r + j * D.R.t + i * sLen D ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
  nlinarith

end Val

theorem moved_loss : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ),
    HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∀ (P : locPl ch.G t),
    (P : Pl D.host.E) ∈ ch.G.pl.W0 → ∀ (w : PlL D) (c : ℝ), 0 ≤ c → (∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) c) →
    ∀ z, LossLe w (moved (locGrid ch.G t P) (keepAt ch.G P) ((repsAt ch.G t P).elt (β P)) (Tflip ch.W ch.S.B t Φ P) z)
      (c + (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (cosExp ch.G P : ℝ) * (vw w ((resCard (Kw (P : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b hS _ _ hF t Φ β hβ P hW w c _ hT z
  classical
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hde := Test.pde_ne_q hS
  have hc' : ∀ Q ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal :=
    GlobalTheory.RowTest.guard_of_qGuard hS.guard t
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hTT := isTensor_Tflip hL ch.W ch.S.B t Φ hde hc' P.2
  have hcond : HasConductor (psiAt ch.W P.1) 1 :=
    (((Good.locGrid_isGood hL ch.G ch.W t hde hc').1 P.1 P.2).square 0 hm 0 hm).cond
  haveI := (isUnitVol_unitVol P.1).1
  set e := cosExp ch.G P with he
  have hdep : depthAt ch.G P = e := by
    obtain ⟨v, hv, hvP⟩ := Finset.mem_image.1 hW
    have := depthAt_w ch.G hv
    rw [he, ← hvP, this.1, this.2]
  rw [hdep] at hTT
  have hkeep : keepAt ch.G P = false := by simp [keepAt, hW]
  have hO := oneCoset one_le_sLen (psiAt ch.W P.1) (unitVol P.1) (givenLevel ch.G t P) (Tflip ch.W ch.S.B t Φ P) (unifAt P.1) e
    D.R.m_even (isUnif_unifAt P.1) hcond hTT (fun j hj _ => ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.givenLevel_KO ch.G t P hj)
  have hb : β P ∈ unfSupport (psiAt ch.W P.1) (unitVol P.1) false
      (Reps.through one_le_sLen (givenLevel ch.G t P) (stair (locGrid ch.G t P) (unifAt P.1) e)) (Tflip ch.W ch.S.B t Φ P) := by
    have := hβ P
    rw [hkeep] at this
    exact this
  have hβ' := funext (hO _ hb)
  have hdet : ∀ X, ∃ a : ℕ, gdet ((repsAt ch.G t P).elt (β P) X) = unifAt P.1 ^ a ∧
      a ≤ (locGrid ch.G t P).rank X * (e * D.R.m) := fun X => by
    rw [hβ']
    exact gdet_elt (G := locGrid ch.G t P) one_le_sLen _ _ _ X
  generalize (repsAt ch.G t P).elt (β P) = g at hdet ⊢
  have hq := ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.resCard_ne P.1
  have hsq : ((Real.sqrt (resCard (Kw (P : Pl D.host.E)) : ℕ) : ℝ) : ℂ) ∈ Set.range D.what₂.embLL := by
    rw [ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.ResCardPlace.resCard_Kw]
    exact hF.sqrt P.1 (Or.inr ⟨t, P.2⟩)
  set v : ℝ := (vw w ((resCard (Kw (P : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ) with hv
  have hv0 : 0 ≤ v := by rw [hv]; exact_mod_cast ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_nat_nonneg w _
  rw [hkeep, moved_false]
  have hP := lossLe_list_prod (w := w) (fun b : Edge => apow (gdet (g b.src))⁻¹ (((locGrid ch.G t P).rank b.tgt : ℂ) / 2) *
      apow (gdet (g b.tgt))⁻¹ (-((locGrid ch.G t P).rank b.src : ℂ) / 2))
      ((bigN D * (e * D.R.m) * bigN D : ℕ) * v / 2) (oppositePath (locGrid ch.G t P).m) (fun b hb => by
    have hr : (locGrid ch.G t P).rank b.src ≤ bigN D ∧ (locGrid ch.G t P).rank b.tgt ≤ bigN D := by
      change b ∈ oppositePath D.R.m at hb
      simp only [oppositePath, List.mem_append, List.mem_map, List.mem_range, List.mem_reverse] at hb
      rcases hb with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
      · exact ⟨rank_le _ _ _ hi.le le_rfl, rank_le _ _ _ hi le_rfl⟩
      · exact ⟨rank_le _ _ _ le_rfl hj, rank_le _ _ _ le_rfl hj.le⟩
    obtain ⟨a, ha, -⟩ := hdet b.src
    obtain ⟨a', ha', hle⟩ := hdet b.tgt
    rw [ha, ha', neg_div, apow_neg, apow_half (isUnif_unifAt P.1), apow_half (isUnif_unifAt P.1)]
    refine (lossLe_sqrt hq hsq _ _).mono ?_
    have h1 : a' * (locGrid ch.G t P).rank b.src ≤ bigN D * (e * D.R.m) * bigN D :=
      Nat.mul_le_mul (hle.trans (Nat.mul_le_mul_right _ hr.2)) hr.1
    have h2 : ((a' * (locGrid ch.G t P).rank b.src : ℕ) : ℝ) ≤ (bigN D * (e * D.R.m) * bigN D : ℕ) := by exact_mod_cast h1
    have h3 := mul_le_mul_of_nonneg_right h2 hv0
    rw [← hv]
    linarith)
  refine (lossLe_mul hP (hT _)).mono (le_of_eq ?_)
  have hlen : (oppositePath (locGrid ch.G t P).m).length = 2 * D.R.m := by
    change (oppositePath D.R.m).length = _
    simp [oppositePath]; ring
  rw [hlen]
  push_cast
  ring

end GlobalTheory.UnfoldLoss.MovedChosen

end
end
