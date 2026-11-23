module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilTransportAdelicSchwartzCmExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle003
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ProjFacts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle077
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle048
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle065
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContinuousCA
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle089
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle084
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle085
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles

@[expose] public section

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
set_option linter.unusedSectionVars false
noncomputable section
namespace PositivityTheory.ThKW.AdelicSchwartzProperties
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation PositivityTheory.ThKW.PhaseFourierInjectivity GlobalTheory.ThetaTransform GlobalTheory.RatDarboux
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {nS nT N : ℕ}
theorem pairing_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {JS : Matrix (Fin nS) (Fin nS) E}
    {JT : Matrix (Fin nT) (Fin nT) E} (hS : IsHermND σ JS) (hT : IsHermND σ JT) {ξ₀ : E} (hξ : ξ₀ ≠ 0) :
    ∃ (N : ℕ) (α β : WOF F E nS nT ≃ₗ[AF F] (Fin N → AF F)) (a b : Matrix (Fin nT) (Fin nS) E ≃ₗ[F] (Fin N → F)),
      (∀ v u, symplOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ (dCd F JT * v) (dC (AF F ⊗[F] E) nT * u) =
        α v ⬝ᵥ β u) ∧ (∀ x, α (ratWF x) = GlobalTheory.SWQ.rat (a x)) ∧ ∀ x, β (ratWF x) = GlobalTheory.SWQ.rat (b x) := by
  classical
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hinv := GlobalTheory.SplitDetCharF.sig_invol hB.cm
  have eB : (-1 : AF F ⊗[F] E) • incM F (-(ξ₀ • JS⁻¹)) = incM F (ξ₀ • JS⁻¹) := by
    funext i j
    simp [incM]
  have hbij := bijective_sympBil σ hinv (JA := (1 : Matrix (Fin nT) (Fin nT) E)ᵀ) (JB := -(ξ₀ • JS⁻¹)) (by simp)
    (by
      rw [← neg_smul, Matrix.det_smul]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 hξ)) (Matrix.isUnit_nonsing_inv_det _ (Ne.isUnit hS.2)).ne_zero)
  let b := Module.finBasis F (Matrix (Fin nT) (Fin nS) E)
  let b' := b.dualBasis.map (LinearEquiv.ofBijective _ hbij).symm
  have hb : ∀ i j, symp σ (-1) (1 : Matrix (Fin nT) (Fin nT) E)ᵀ (-(ξ₀ • JS⁻¹)) (b' i) (b j) = if j = i then 1 else 0 :=
    fun i j => by
      have h1 := (LinearEquiv.ofBijective _ hbij).apply_symm_apply (b.dualBasis i)
      have h2 := LinearMap.congr_fun h1 (b j)
      rw [Module.Basis.dualBasis_apply_self] at h2
      exact h2
  let P : LinearMap.BilinForm (AF F) (WOF F E nS nT) :=
    sympBil (cA σ) (-1) (incM F (1 : Matrix (Fin nT) (Fin nT) E)ᵀ) (incM F (-(ξ₀ • JS⁻¹)))
  have hP : ∀ v u, P v u = (adB b').equivFun v ⬝ᵥ (adB b).equivFun u := fun v u => by
    have h0 : ∀ i j, P (adB b' i) (adB b j) = if j = i then 1 else 0 := fun i j => by
      rw [adB_apply, adB_apply]
      refine (symp_map (AF F) σ _ _ (b' i) (b j)).trans ?_
      rw [hb]
      split_ifs <;> simp
    conv_lhs => rw [← (adB b').sum_repr v, ← (adB b).sum_repr u]

    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, h0, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, dotProduct, Module.Basis.equivFun_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  refine ⟨_, (adB b').equivFun, (adB b).equivFun, b'.equivFun, b.equivFun, fun v u => ?_, adB_rat b', adB_rat b⟩
  rw [← hP]
  refine Eq.trans ?_ (GlobalTheory.TransportF.symplOF_eq_symp (JT := 1) rfl eB v u)
  unfold symplOF
  rw [hOF_dual JS JT hT.2, hOF_eq_trace, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
theorem coords_k {σ : E →ₐ[F] E} {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E}
    {JT : Matrix (Fin nT) (Fin nT) E} (hS : IsHermND σ JS) (hT : IsHermND σ JT) {ξ₀ : E} (hξ : ξ₀ ≠ 0)
    (hσ : σ ξ₀ = -ξ₀) :
    ∃ (N : ℕ) (α β : WOF F E nS nT ≃ₗ[AF F] (Fin N → AF F))
      (e : WOF F E nS (nT + nT) ≃ₗ[AF F] VA F N),
      (∀ u v, e (dC (AF F ⊗[F] E) nT * u + dCd F JT * v) = (α v, β u)) ∧
      (∀ w w', symplOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ w w' = symV (e w) (e w')) ∧
      (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : Fin N → F,
        e (ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) ∧
      (∀ y z : Fin N → F, ∃ x : Matrix (Fin (nT + nT)) (Fin nS) E, e (ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) ∧
      Continuous e ∧ Continuous e.symm ∧
      Continuous α ∧ Continuous α.symm ∧ Continuous β ∧ Continuous β.symm ∧
      (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y : Fin N → F, β (ratWF x) = GlobalTheory.SWQ.rat y) ∧
      (∀ y : Fin N → F, ∃ x : Matrix (Fin nT) (Fin nS) E, β (ratWF x) = GlobalTheory.SWQ.rat y) := by
  have hinv := GlobalTheory.SplitDetCharF.sig_invol hB.cm
  obtain ⟨N, α, β, a, b, hP, ha, hb⟩ := _root_.PositivityTheory.ThKW.AdelicSchwartzProperties.pairing_k hB hS hT hξ
  obtain ⟨d, U, V, hd, hd'⟩ := split (nS := nS) JT hT
  obtain ⟨e, he0⟩ : ∃ e : WOF F E nS (nT + nT) ≃ₗ[AF F] VA F N, ∀ w, e w = (α (d w).1, β (d w).2) :=
    ⟨d.trans (α.prodCongr β), fun _ => rfl⟩
  have he : ∀ u v, e (dC (AF F ⊗[F] E) nT * u + dCd F JT * v) = (α v, β u) := fun u v => by
    rw [he0, ← hd' (v, u), d.apply_symm_apply]
  have j1 : IsModuleTopology (AF F) (Fin N → AF F) := inferInstance
  have j2 : IsModuleTopology (AF F) (VA F N) := inferInstance
  have c1 := cont2 (modTop _ _) j2 e
  have c2 := cont2 (modTop _ _) j1 α
  have c3 := cont2 (modTop _ _) j1 β
  refine ⟨N, α, β, e, he, fun w w' => ?_, fun x => ?_, fun y z => ?_, c1.1, c1.2, c2.1, c2.2, c3.1, c3.2,
    fun x => ⟨_, hb x⟩, fun y => ⟨b.symm y, by rw [hb, LinearEquiv.apply_symm_apply]⟩⟩
  · obtain ⟨⟨v, u⟩, rfl⟩ := d.symm.surjective w
    obtain ⟨⟨v', u'⟩, rfl⟩ := d.symm.surjective w'
    have s1 : symplOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ (dC (AF F ⊗[F] E) nT * u)
        (dC (AF F ⊗[F] E) nT * u') = 0 := by rw [symplOF, h_CC, mul_zero, map_zero]
    have s2 : symplOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ (dCd F JT * v) (dCd F JT * v') = 0 := by
      rw [symplOF, dCd_eq, Matrix.mul_assoc, Matrix.mul_assoc, h_AA, mul_zero, map_zero]
    have s3 := GlobalTheory.T.adelicSymplecticTraceForm_alternating_swap F E σ hinv _ _ JS _ hS (GlobalTheory.WeilSchrodinger.DblTargetF.isHermND_dblG hT) ξ₀ hσ
      (dCd F JT * v') (dC (AF F ⊗[F] E) nT * u)
    rw [hd', hd', he, he, GlobalTheory.ThetaSchurF.symplOF_add_left, GlobalTheory.ThetaSchurF.symplOF_add_right,
      GlobalTheory.ThetaSchurF.symplOF_add_right, s1, s2, s3, hP, hP, symV]
    ring
  · refine ⟨a (V * x), b (U * x), ?_⟩
    rw [he0, hd, rat_mul, rat_mul, ha, hb]
  · refine ⟨dC E nT * b.symm z + dCdE JT * a.symm y, ?_⟩
    have : (ratWF (dC E nT * b.symm z + dCdE JT * a.symm y) : WOF F E nS (nT + nT)) =
        dC (AF F ⊗[F] E) nT * (ratWF (b.symm z) : WOF F E nS nT) + dCd F JT * (ratWF (a.symm y) : WOF F E nS nT) := by
      rw [← dC_map (incAF F E), dCd, rat_mul, rat_mul]
      exact Matrix.map_add _ (map_add _) _ _
    rw [this, he, ha, hb, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
end PositivityTheory.ThKW.AdelicSchwartzProperties
end
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.ThetaLevelF
open Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem thetaTr_levelF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, ∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
            ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT ξ₀ B.ψ u (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) = GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ := by
  intro F E _ _ _ _ _ σ B _ hψ nS nT JS JT _ _ ξ₀ _ _ JA JB ξ hA hB κ _ co _ Φ hΦ
  haveI : IsModuleTopology (AF F) (WOF F E nS nT) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin nT → Fin nS → AF F ⊗[F] E))
  obtain ⟨K, hK⟩ := GlobalTheory.ThetaLevel.schr_fin_fix F B.ψ hψ.1.1 Φ hΦ
  have hcont : Continuous co.e := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
  let f1 : WOF F E nS nT →+ (κ → Af F) :=
    AddMonoidHom.mk' (fun u i => ((co.e u).1 i).2) (fun u v => by funext i; rw [map_add (f := _)]; rfl)
  let f2 : WOF F E nS nT →+ (κ → Af F) :=
    AddMonoidHom.mk' (fun u i => ((co.e u).2 i).2) (fun u v => by funext i; rw [map_add (f := _)]; rfl)
  have hf1 : Continuous f1 :=
    continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_fst.comp hcont))
  have hf2 : Continuous f2 :=
    continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_snd.comp hcont))
  let U : OpenAddSubgroup (WOF F E nS nT) := K.comap f1 hf1 ⊓ K.comap f2 hf2
  refine ⟨(U : AddSubgroup _), U.isOpen, fun u hu hinf => funext fun w => ?_⟩
  have hfix : GlobalTheory.WeilM.schr B.ψ (co.e u) Φ = Φ := by
    rw [e_eq_fin co u hinf]
    exact hK _ hu.1 _ hu.2
  show B.ψ (symplOHF σ JS JT ξ₀ w u) * GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr B.ψ (co.e (w + u)) Φ) =
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr B.ψ (co.e w) Φ)
  rw [map_add (f := _)]
  have h1 : GlobalTheory.WeilM.schr B.ψ (co.e w + co.e u) Φ = fun x =>
      B.ψ (-(⅟(2 : AF F) * ((co.e w).1 ⬝ᵥ (co.e u).2 - (co.e u).1 ⬝ᵥ (co.e w).2))) *
        GlobalTheory.WeilM.schr B.ψ (co.e w) (GlobalTheory.WeilM.schr B.ψ (co.e u) Φ) x :=
    funext (GlobalTheory.ThetaLevel.schr_add B.ψ _ _ Φ)
  rw [h1, hfix]
  simp only [GlobalTheory.WeilM.thetaSum]
  rw [tsum_mul_left, ← mul_assoc, ← AddChar.map_add_eq_mul]
  have h2 : symplOHF σ JS JT ξ₀ w u =
      ⅟(2 : AF F) * ((co.e w).1 ⬝ᵥ (co.e u).2 - (co.e u).1 ⬝ᵥ (co.e w).2) := by
    rw [symplOHF, GlobalTheory.TransportF.symplOF_eq_symp hA hB, co.form]
    congr 1
    refine (invOf_eq_right_inv ?_).symm
    rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
    norm_num
  rw [h2, add_neg_cancel, AddChar.map_zero_eq_one, one_mul]
end GlobalTheory.ThetaLevelF
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C4
namespace PositivityTheory.SiegelWeilFormula.Act.C6
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem second_orbit_bijection_weyl (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) :
    ∃ e : (Σ _ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Cr_k L) ≃ {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ∀ x, ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧
      _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e x).1 = p * (w₁ * (cM x.2.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k x.1))) := by
  have hg : ∀ x : (Σ _ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Cr_k L), w₁ * (cM x.2.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k x.1)) ∈ rat2 σ d.Y := fun x =>
    (rat2 σ d.Y).mul_mem h.wr ((rat2 σ d.Y).mul_mem (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.cM_rat'_k h x.2.2.1 x.2.2.2) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_rat_k L (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.rep_mem_k L.sd x.1)))
  have hfix : ∀ x : (Σ _ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Cr_k L), _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L (cM x.2.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k x.1)) := fun x => _root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_mul_k (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_cM'_k h _) (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_j_k _)
  let Fm : (Σ _ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Cr_k L) → {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)} := fun x =>
    ⟨Quotient.mk _ ⟨_, hg x⟩, by
      obtain ⟨p, hp, -, e⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.out_mk_k d ⟨_, hg x⟩
      rw [e, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.first_orbit_parabolic_left hp]
      exact _root_.PositivityTheory.SiegelWeilFormula.Act.C6.not_first_orbit_weyl h (hfix x)⟩
  have hinj : Function.Injective Fm := by
    rintro ⟨q₁, c₁⟩ ⟨q₂, c₂⟩ hE
    have hE' : (Quotient.mk _ ⟨_, hg ⟨q₁, c₁⟩⟩ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d) = Quotient.mk _ ⟨_, hg ⟨q₂, c₂⟩⟩ := congrArg Subtype.val hE
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.mk_eq_mk_k] at hE'
    set g₁ := w₁ * (cM c₁.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q₁))
    set g₂ := w₁ * (cM c₂.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q₂))
    have e : (g₂ * g₁⁻¹) * (w₁ * (cM c₁.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q₁))) = w₁ * (cM c₂.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q₂)) := by
      simp only [g₁, g₂]; group
    have hpr : g₂ * g₁⁻¹ ∈ rat2 σ d.Y := (rat2 σ d.Y).mul_mem (hg ⟨q₂, c₂⟩) ((rat2 σ d.Y).inv_mem (hg ⟨q₁, c₁⟩))
    obtain ⟨hP, hc⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.inj_core_k h hE' hpr (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.rep_mem_k L.sd q₁) (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.rep_mem_k L.sd q₂) e
    have hq : q₁ = q₂ := by
      rw [← _root_.PositivityTheory.SiegelWeilFormula.Act.C6.mk_rep_k L.sd q₁, ← _root_.PositivityTheory.SiegelWeilFormula.Act.C6.mk_rep_k L.sd q₂, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.mk_eq_mk_k]
      exact hP
    subst hq
    rw [hc rfl]
  have hsurj : Function.Surjective Fm := by
    rintro ⟨q, hq⟩
    obtain ⟨p, hp, hpr, hfx⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.normalize_k h (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.rep_mem_k d q) hq
    have hr : w₁⁻¹ * (p * _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) ∈ rat2 σ d.Y :=
      (rat2 σ d.Y).mul_mem ((rat2 σ d.Y).inv_mem h.wr) ((rat2 σ d.Y).mul_mem hpr (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.rep_mem_k d q))
    obtain ⟨s, c, γ', hsr, hW, hγ', -, hx⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.stab_dec_k h hr hfx
    obtain ⟨p', hp', hp'r, he'⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.out_mk_k L.sd ⟨γ', hγ'⟩
    obtain ⟨p₂, hp₂, hp₂r, c₂, hc₂⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.conj_par_k h ((par2 σ L.Y).inv_mem hp') ((rat2 σ L.Y).inv_mem hp'r) c
    refine ⟨⟨Quotient.mk _ ⟨γ', hγ'⟩, c₂⟩, Subtype.ext ?_⟩
    show (Quotient.mk _ ⟨_, hg ⟨Quotient.mk _ ⟨γ', hγ'⟩, c₂⟩⟩ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d) = q
    conv_rhs => rw [← _root_.PositivityTheory.SiegelWeilFormula.Act.C6.mk_rep_k d q]
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.mk_eq_mk_k]
    have hγ'' : γ' = p'⁻¹ * _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (Quotient.mk _ ⟨γ', hγ'⟩ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd) := by rw [he']; group
    have key : p * _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q = (w₁ * s * w₁⁻¹) * p₂ * (w₁ * (cM c₂.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (Quotient.mk _ ⟨γ', hγ'⟩ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd)))) := by
      have h1 : p * _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q = w₁ * (s * (cM c.1 * L.j γ')) := by rw [← hx]; group
      rw [h1]
      conv_lhs => rw [hγ'', map_mul]
      have h2 : w₁ * (s * (cM c.1 * (L.j p'⁻¹ * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (Quotient.mk _ ⟨γ', hγ'⟩ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd))))) =
          (w₁ * s * w₁⁻¹) * ((w₁ * (cM c.1 * L.j p'⁻¹)) * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (Quotient.mk _ ⟨γ', hγ'⟩ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd))) := by group
      rw [h2, hc₂]
      group
    have : _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q * (w₁ * (cM c₂.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (Quotient.mk _ ⟨γ', hγ'⟩ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd))))⁻¹ = p⁻¹ * ((w₁ * s * w₁⁻¹) * p₂) := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, key]; group
    rw [this]
    exact (par2 σ d.Y).mul_mem ((par2 σ d.Y).inv_mem hp) ((par2 σ d.Y).mul_mem hW hp₂)
  refine ⟨Equiv.ofBijective Fm ⟨hinj, hsurj⟩, fun x => ?_⟩
  obtain ⟨p, hp, hpr, e⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.out_mk_k d ⟨_, hg x⟩
  exact ⟨p, hp, hpr, e⟩
end PositivityTheory.SiegelWeilFormula.Act.C6
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem coordsC_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)}
    (hU : L.UData uM ν 𝓤) {lam' : Measure (nA σ L.Y L.b)} {𝓖' : Set (nA σ L.Y L.b)}
    (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖') {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T')
    {𝓐 : Set (AF F)} (h𝓐 : IsAddFundamentalDomain (fA F) 𝓐 (lamA F))
    {P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b)} (hP : ∀ β, P β = ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β), _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β))
    {c : ℝ≥0∞} (hPc : lam.map P = c • ((ν.prod (lamA F)).prod lam'))
    (Ψ : d.G → ℂ) (hΨ : ∀ r ∈ rat2 σ d.Y, (∀ k, inFrame d.b r k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) → ∀ g, Ψ (r * g) = Ψ g) (x : d.G) :
    ∫ p, Ψ (nb p.2 * (uM p.1 * x)) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2 ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) =
      c.toReal • ∫ p, Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x))) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k T' p.1
        ∂((lam'.restrict 𝓖').prod ((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐)))) := by
  exact _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.coordsC_ck_k h hc hU hc' hT h𝓐 hP hPc Ψ hΨ x
theorem coordsE_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)}
    (hU : L.UData uM ν 𝓤) {lam' : Measure (nA σ L.Y L.b)} {𝓖' : Set (nA σ L.Y L.b)}
    (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖') {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T')
    {𝓐 : Set (AF F)} (h𝓐 : IsAddFundamentalDomain (fA F) 𝓐 (lamA F))
    {P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b)} (hP : ∀ β, P β = ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β), _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β))
    {c : ℝ≥0∞} (hPc : lam.map P = c • ((ν.prod (lamA F)).prod lam'))
    (Ψ : d.G → ℝ≥0∞) (hΨm : Measurable Ψ) (hΨ : ∀ r ∈ rat2 σ d.Y, (∀ k, inFrame d.b r k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) → ∀ g, Ψ (r * g) = Ψ g) (x : d.G) :
    ∫⁻ p, Ψ (nb p.2 * (uM p.1 * x)) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2‖ₑ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) =
      c * ∫⁻ p, Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x))) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k T' p.1‖ₑ
        ∂((lam'.restrict 𝓖').prod ((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐)))) := by
  exact _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.coordsE_ck_k h hc hU hc' hT h𝓐 hP hPc Ψ hΨm hΨ x
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end
