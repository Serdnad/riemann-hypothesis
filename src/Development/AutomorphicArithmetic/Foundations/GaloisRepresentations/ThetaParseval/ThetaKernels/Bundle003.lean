module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1284
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1445
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHeckeCharacterExtendingBaseCharacte
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Mfac
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.CAFInvol
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LeviGLInvVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1593
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1595
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
noncomputable section
namespace GlobalTheory.ThetaLineSmoothF
open Formalism.IndefR.DatumF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
section Form
variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ : E)
end Form
theorem contDiff_deriv_heisOF_line_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ (k : ℕ) (L' : (Fin k → ℝ) →+ Formalism.IndefR.DatumF.WOF F E nS nT), Continuous L' → (∀ t, (L' t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ w : Formalism.IndefR.DatumF.WOF F E nS nT, ContDiff ℝ ∞ fun x => deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L' x)) 0 := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ hψ f hf L hL hL0 k L' hL' hL0' w
  obtain ⟨lam, hl, hlam⟩ := exists_log hψ
  have hi : Continuous (fun v : Fin (k + 1) → ℝ => Fin.init v) := continuous_pi fun i => continuous_apply _
  let M : (Fin (k + 1) → ℝ) →+ WOF F E nS nT :=
    { toFun := fun v => L' (Fin.init v) + L (v (Fin.last k))
      map_zero' := by
        show L' (Fin.init (0 : Fin (k + 1) → ℝ)) + L ((0 : Fin (k + 1) → ℝ) (Fin.last k)) = 0
        rw [show Fin.init (0 : Fin (k + 1) → ℝ) = (0 : Fin k → ℝ) from rfl, Pi.zero_apply, map_zero, map_zero, add_zero]
      map_add' := fun u v => by
        show L' (Fin.init (u + v)) + L (u (Fin.last k) + v (Fin.last k)) = _
        rw [show Fin.init (u + v) = Fin.init u + Fin.init v from rfl, map_add (f := _), map_add (f := _)]
        abel }
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : ContinuousAdd (WOF F E nS nT) := inferInstanceAs (ContinuousAdd (Fin nT → Fin nS → AF F ⊗[F] E))
  have hM : Continuous M := (hL'.comp hi).add (hL.comp (continuous_apply _))
  have hM0 : ∀ v, (M v).map (finPartF F E) = 0 := fun v => by
    show (L' (Fin.init v) + L (v (Fin.last k))).map (finPartF F E) = 0
    rw [Matrix.map_add _ (map_add _), hL0', hL0, add_zero]
  have hg : ContDiff ℝ ∞ fun v => f (w + M v) := hf.smooth (k + 1) M hM hM0 w
  have hsnoc : ContDiff ℝ ∞ (fun p : (Fin k → ℝ) × ℝ => (Fin.snoc (α := fun _ => ℝ) p.1 p.2 : Fin (k + 1) → ℝ)) := by
    refine contDiff_pi.2 fun i => ?_
    induction i using Fin.lastCases with
    | last => simp only [Fin.snoc_last]; exact contDiff_snd
    | cast j => simp only [Fin.snoc_castSucc]; exact (contDiff_apply ℝ (fun _ => ℝ) j).comp contDiff_fst
  let h : (Fin k → ℝ) × ℝ → ℂ := fun p => f (w + M (Fin.snoc (α := fun _ => ℝ) p.1 p.2))
  have hh : ContDiff ℝ ∞ h := hg.comp hsnoc
  have hfe : ∀ x t, f (w + L' x + L t) = h (x, t) := by
    intro x t
    show _ = f (w + (L' (Fin.init (Fin.snoc (α := fun _ => ℝ) x t)) + L (Fin.snoc (α := fun _ => ℝ) x t (Fin.last k))))
    rw [Fin.init_snoc, Fin.snoc_last, add_assoc]
  have hpsi : ∀ y (t : ℝ), B.ψ (symplOHF σ JS JT ξ₀ y (L t)) =
      Complex.exp (t * lam (symplOHF σ JS JT ξ₀ y (L 1))) := by
    intro y t
    rw [hlam _ (snd_symplOHF σ JS JT ξ₀ y _ (hL0 t))]
    congr 1
    let φ : ℝ →+ ℂ :=
      { toFun := fun t => lam (symplOHF σ JS JT ξ₀ y (L t))
        map_zero' := by rw [map_zero L, symplOHF_zero_right, map_zero]
        map_add' := fun a b => by rw [map_add L, symplOHF_add_right, map_add (f := _)] }
    have hφ : Continuous φ := hl.comp (continuous_symplOHF σ JS JT ξ₀ continuous_const hL)
    have := (φ.toRealLinearMap hφ).map_smul t 1
    rw [smul_eq_mul, mul_one, Complex.real_smul] at this
    exact this
  have hd : ∀ x, HasDerivAt (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L' x))
      (lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1)) * h (x, 0) + fderiv ℝ h (x, 0) (0, 1)) 0 := by
    intro x
    have e : (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L' x)) = fun t : ℝ =>
        Complex.exp (t * lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1))) * h (x, t) := by
      funext t
      show B.ψ (symplOHF σ JS JT ξ₀ (w + L' x) (L t)) * f (w + L' x + L t) = _
      rw [hpsi, hfe]
    rw [e]
    have h0 : HasDerivAt (fun t : ℝ => (t : ℂ) * lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1)))
        (lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1))) 0 := by
      simpa using (HasDerivAt.ofReal_comp (hasDerivAt_id (0 : ℝ))).mul_const
        (lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1)))
    have hp : HasDerivAt (fun t : ℝ => (x, t)) ((0 : Fin k → ℝ), (1 : ℝ)) 0 :=
      (hasDerivAt_const (0 : ℝ) x).prodMk (hasDerivAt_id 0)
    have h2 : HasDerivAt (fun t : ℝ => h (x, t)) (fderiv ℝ h (x, 0) (0, 1)) 0 :=
      ((hh.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hp
    have h3 : HasDerivAt (fun t : ℝ => Complex.exp (t * lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1))) * h (x, t))
        (Complex.exp (((0 : ℝ) : ℂ) * lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1))) *
          lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1)) * h (x, 0) +
          Complex.exp (((0 : ℝ) : ℂ) * lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1))) * fderiv ℝ h (x, 0) (0, 1)) 0 :=
      h0.cexp.mul h2
    refine h3.congr_deriv ?_
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
  let φ' : (Fin k → ℝ) →+ ℂ :=
    { toFun := fun x => lam (symplOHF σ JS JT ξ₀ (L' x) (L 1))
      map_zero' := by rw [map_zero L', symplOHF_zero_left, map_zero]
      map_add' := fun a b => by rw [map_add L', symplOHF_add_left, map_add (f := _)] }
  have hφ' : ContDiff ℝ ∞ φ' :=
    (φ'.toRealLinearMap (hl.comp (continuous_symplOHF σ JS JT ξ₀ hL' continuous_const))).contDiff
  have e : (fun x => deriv (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L' x)) 0) = fun x =>
      (lam (symplOHF σ JS JT ξ₀ w (L 1)) + φ' x) * h (x, 0) + fderiv ℝ h (x, 0) (0, 1) := by
    funext x
    rw [(hd x).deriv, symplOHF_add_left, map_add (f := _)]
    rfl
  rw [e]
  have hin : ContDiff ℝ ∞ (fun x : Fin k → ℝ => (x, (0 : ℝ))) := contDiff_id.prodMk contDiff_const
  exact ((contDiff_const.add hφ').mul (hh.comp hin)).add
    (((hh.fderiv_right (m := ∞) (by simp)).comp hin).clm_apply contDiff_const)
end GlobalTheory.ThetaLineSmoothF
end
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open GlobalTheory.HeckeExtend
noncomputable section
namespace GlobalTheory.HeckeExtend
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem exists_extend_hecke_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ lam : (AF F)ˣ →* Circle, Continuous lam →
      (∀ a : Fˣ, lam (Units.map (algebraMap F (AF F)).toMonoidHom a) = 1) →
      (∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1) →
      ∃ lam' : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF lam' ∧
        (∀ z : (AF F ⊗[F] E)ˣ, At (evI F) ((z : AF F ⊗[F] E) - 1) → lam' z = 1) ∧
        ∀ a, lam' (idFF F E a) = lam a := by
  intro F E _ _ _ _ _ σ B hB lam hc h1 hinf
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨M, hM, hMk⟩ := GlobalTheory.T.exists_congruence_kernel_ideleCharacter_trivialAtInfinity F lam hc hinf
  let V : Subgroup (AF F ⊗[F] E)ˣ := (Units.map (incAF F E).toMonoidHom).range ⊔ WE F E (8 * M)
  have hkey : ∀ a : (AF F)ˣ, idFF F E a ∈ V → lam a = 1 := key σ hB.cm M hM lam h1 hMk
  have hN : 0 < 8 * M := by positivity
  have hWo : IsOpen (WE F E (8 * M) : Set (AF F ⊗[F] E)ˣ) := by
    have ho := GlobalTheory.T.isOpen_integralTensorAdeleMultiples F E (8 * M) hN
    have hcv : Continuous fun z : (AF F ⊗[F] E)ˣ => (z : AF F ⊗[F] E) - 1 :=
      Units.continuous_val.sub continuous_const
    have hci : Continuous fun z : (AF F ⊗[F] E)ˣ => ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 :=
      Units.continuous_coe_inv.sub continuous_const
    exact (ho.preimage hcv).inter (ho.preimage hci)
  have hVo : IsOpen (V : Set (AF F ⊗[F] E)ˣ) := Subgroup.isOpen_mono le_sup_right hWo
  let ψ0 : (AF F)ˣ →* (AF F ⊗[F] E)ˣ ⧸ V := (QuotientGroup.mk' V).comp (idFF F E)
  have hker : ψ0.ker ≤ lam.ker := fun a ha => hkey a ((QuotientGroup.eq_one_iff _).1 ha)
  letI : DivisibleBy (Additive Circle) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn u => by
    obtain ⟨t, ht⟩ := Circle.exp_surjective u.toMul
    refine ⟨Additive.ofMul (Circle.exp (t / n)), ?_⟩
    show Additive.ofMul (Circle.exp (t / n) ^ n) = u
    rw [← Circle.exp_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hn), ht]
    rfl
  letI : DivisibleBy (Additive Circle) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨ρ, hρ⟩ := (Module.Baer.of_divisible (Additive Circle)).extension_property_addMonoidHom
    (MonoidHom.toAdditive (QuotientGroup.kerLift ψ0)) (QuotientGroup.kerLift_injective ψ0)
    (MonoidHom.toAdditive (QuotientGroup.lift ψ0.ker lam hker))
  let κ : (AF F ⊗[F] E)ˣ ⧸ V →* Circle := MonoidHom.toAdditive.symm ρ
  have hκ : ∀ x, κ (QuotientGroup.kerLift ψ0 x) = QuotientGroup.lift ψ0.ker lam hker x :=
    fun x => DFunLike.congr_fun hρ (Additive.ofMul x)
  have hV1 : ∀ z ∈ V, κ.comp (QuotientGroup.mk' V) z = 1 := fun z hz => by
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).2 hz, map_one]
  refine ⟨κ.comp (QuotientGroup.mk' V), ⟨?_, fun x => hV1 _ (le_sup_left (a := (Units.map (incAF F E).toMonoidHom).range)
    ⟨x, rfl⟩)⟩, fun z hz => hV1 z (le_sup_right (a := (Units.map (incAF F E).toMonoidHom).range) ?_), fun a => hκ (a : (AF F)ˣ ⧸ ψ0.ker)⟩
  · refine continuous_of_continuousAt_one _ ?_
    unfold ContinuousAt
    rw [map_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hVo.mem_nhds (one_mem V)] with z hz
    exact (hV1 z hz).symm
  · have hN' := hN
    refine ⟨GlobalTheory.T.mem_tensorCongruence_of_supported_at_infinity F E _ hN' _ hz, GlobalTheory.T.mem_tensorCongruence_of_supported_at_infinity F E _ hN' _ ?_⟩
    intro u hu
    have e : ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 = -(((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * ((z : AF F ⊗[F] E) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
    rw [e, smul_neg, ← mul_smul_comm, hz u hu, mul_zero, neg_zero]
end GlobalTheory.HeckeExtend
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
namespace PositivityTheory.ThKW.LeviParabolicGL
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
variable {n : ℕ}
end PositivityTheory.ThKW.LeviParabolicGL

open PositivityTheory.ThKW.LeviParabolicGL in
theorem PositivityTheory.ThKW.PhaseFourierInjectivity.levi_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E), IsHermND σ JT →
    ∃ m : GL (Fin nT) (AF F ⊗[F] E) →* GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT), Continuous m ∧
      (∀ t, mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) (m t) * PositivityTheory.ThKW.ModulusFactorDefinition.dC (AF F ⊗[F] E) nT =
        PositivityTheory.ThKW.ModulusFactorDefinition.dC (AF F ⊗[F] E) nT * t.1) ∧
      ∀ a : GL (Fin nT) E, m (Matrix.GeneralLinearGroup.map (incAF F E) a) ∈
        GQF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) := by
  intro F E _ _ _ _ _ σ B hB n JT hT
  classical
  have hc : IsCMExt F E σ := hB.cm
  have hcc := GlobalTheory.SplitLagrF.cAF_invol hc
  have hccE : ∀ x : E, (σ : E →+* E) ((σ : E →+* E) x) = x := fun x => GlobalTheory.SplitDetCharF.sig_invol hc x
  set rE : E := (2 : E)⁻¹ with hrE
  have hrE2 : 2 * rE = 1 := mul_inv_cancel₀ two_ne_zero
  have hr : 2 * (inclR (F := F) (AF F)) rE = 1 := by
    have := congrArg (inclR (F := F) (AF F)) hrE2
    rwa [map_mul, map_ofNat, map_one] at this
  have hJ : ((JR (F := F) (AF F) JT).map (cAF σ))ᵀ = JR (F := F) (AF F) JT := by
    ext i j
    show (1 : AF F) ⊗ₜ[F] σ (JT j i) = (1 : AF F) ⊗ₜ[F] JT i j
    rw [hT.1]
  have hJE : (JT.map (σ : E →+* E))ᵀ = JT := by
    ext i j
    exact hT.1 i j
  have hu : IsUnit (JR (F := F) (AF F) JT).det := by
    have := ((Ne.isUnit hT.2).map (inclR (F := F) (AF F)))
    rwa [RingHom.map_det] at this
  have huE : IsUnit JT.det := Ne.isUnit hT.2
  have eJ : JR (F := F) (AF F) (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) =
      (Matrix.fromBlocks (JR (F := F) (AF F) JT) 0 0 (-JR (F := F) (AF F) JT)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [GlobalTheory.WeilSchrodinger.DblTargetF.dblG, JR, Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_apply_apply, Matrix.map_apply] <;> simp [dbl]
  have eJE : GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT =
      (Matrix.fromBlocks JT 0 0 (-JT)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := rfl
  let mG := leviGL (cAF σ) hr hu
  have hmem : ∀ t, mG t ∈ HR (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) := by
    intro t
    have h := leviGL_mem (cAF σ) hcc hr hJ hu t
    rw [← eJ] at h
    exact h
  let m₀ : GL (Fin n) (AF F ⊗[F] E) →* HR (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) := mG.codRestrict _ hmem
  let m : GL (Fin n) (AF F ⊗[F] E) →* GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) :=
    { toFun := fun t => m₀ t
      map_one' := m₀.map_one
      map_mul' := m₀.map_mul }
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have hcont_c : Continuous (cAF (F := F) (E := E) σ) := GlobalTheory.HeisThetaF.continuous_cAF
  have hL : ∀ (f g : GL (Fin n) (AF F ⊗[F] E) → Matrix (Fin n) (Fin n) (AF F ⊗[F] E)), Continuous f → Continuous g →
      Continuous fun t => (L (cAF σ) (inclR (F := F) (AF F) rE) (JR (F := F) (AF F) JT) (f t) (g t)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
    intro f g hf hg
    refine Continuous.matrix_submatrix ?_ _ _
    simp only [L, sM]
    refine ((continuous_const.matrix_mul ?_).matrix_mul continuous_const)
    refine Continuous.matrix_fromBlocks hf continuous_const continuous_const ?_
    exact (continuous_const.matrix_mul ((hg.matrix_map hcont_c).matrix_transpose)).matrix_mul continuous_const
  have hmG : Continuous mG := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · show Continuous fun t : GL (Fin n) (AF F ⊗[F] E) =>
        (L (cAF σ) (inclR (F := F) (AF F) rE) (JR (F := F) (AF F) JT) t.1 (t⁻¹).1).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm
      exact hL _ _ Units.continuous_val Units.continuous_coe_inv
    · show Continuous fun t : GL (Fin n) (AF F ⊗[F] E) =>
        (L (cAF σ) (inclR (F := F) (AF F) rE) (JR (F := F) (AF F) JT) (t⁻¹).1 t.1).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm
      exact hL _ _ Units.continuous_coe_inv Units.continuous_val
  have hm : Continuous m := by
    have : Continuous fun t => (⟨mG t, hmem t⟩ : HR (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) :=
      hmG.subtype_mk _
    exact this
  refine ⟨m, hm, ?_, ?_⟩
  · intro t
    exact leviGL_col (cAF σ) hr hu t
  · intro a
    let a' : GL (Fin n) (AF F ⊗[F] E) := Matrix.GeneralLinearGroup.map (incAF F E) a
    show ((m₀ a' : HR (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) : GL (Fin (n + n)) (AF F ⊗[F] E)) ∈
      HFin (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
    refine ⟨leviGL (σ : E →+* E) hrE2 huE a, ?_, ?_⟩
    · have h := leviGL_mem (σ : E →+* E) hccE hrE2 hJE huE a
      rw [← eJE] at h
      exact h
    · exact leviGL_map (inclR (F := F) (AF F)) (σ : E →+* E) (cAF σ) (fun x => rfl) hrE2 hr huE hu a
end
end
end

section



section
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
namespace GlobalTheory.EtaSignReal
open GlobalTheory.QuadSymbol GlobalTheory.IdeleNormChar GlobalTheory.AdelicU
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem eta_eq_prod_sign_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ η : (AF F)ˣ →* Circle, IsEtaF E η → ∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) →
      (η a : ℂ) = ∏ w, piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) /
        ((‖piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)‖ : ℝ) : ℂ) := by
  intro F E _ _ _ _ _ σ B hB η hη a ha
  have hcm := hB.cm
  haveI : Algebra.IsQuadraticExtension F E := ⟨hcm.2.2.1⟩
  haveI := hcm.1
  rw [eq_signToCircle η hη, MonoidHom.comp_apply, normSign_eq_prod (finComp_eq_one ha), map_prod]
  rw [show ((∏ w : InfinitePlace F, signToCircle (eta F E w.Completion (infComp a w)) : Circle) : ℂ) =
      ∏ w : InfinitePlace F, ((signToCircle (eta F E w.Completion (infComp a w)) : Circle) : ℂ) from
    map_prod Circle.coeHom _ _]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hw : w.IsReal := IsTotallyReal.isReal w
  rw [piInf_idFF hw]
  set r := InfinitePlace.Completion.ringEquivRealOfIsReal hw ((infComp a w : (w.Completion)ˣ) : w.Completion)
  have hx := mem_normGroup_iff_pos hcm hw (B.emb w) (infComp a w)
  have hr0 : r ≠ 0 := (map_ne_zero _).2 (infComp a w).ne_zero
  rw [Complex.norm_real, Real.norm_eq_abs]
  by_cases hpos : 0 < r
  · rw [eta_eq_one_iff.2 (hx.2 hpos), map_one, abs_of_pos hpos, div_self (by exact_mod_cast hr0)]
    rfl
  · have hneg : r < 0 := lt_of_le_of_ne (not_lt.1 hpos) hr0
    rw [eta_eq_neg_one_iff.2 (fun h => hpos (hx.1 h)), abs_of_neg hneg]
    change ((if (-1 : ℤˣ) = 1 then (1 : Circle) else -1 : Circle) : ℂ) = _
    rw [if_neg (by decide)]
    push_cast
    rw [div_neg, div_self (by exact_mod_cast hr0)]
end GlobalTheory.EtaSignReal
end
end
end

section



section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
noncomputable section
namespace GlobalTheory.RealWeilF.MCont
theorem continuous_mMF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
      (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → Continuous (mMF σ JS JT θ) := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT θ hθ
  have hc : ∀ (w : InfinitePlace F) (m n : ℕ), Continuous fun x : Matrix (Fin m) (Fin n) (AEF F E) => compAtF θ w x :=
    fun w m n => continuous_id.matrix_map (continuous_comp_infPartF (hθ w))
  have h1 : Continuous fun p : GAF σ JS × GAF σ JT => mtF σ JT p.2 :=
    (Units.continuous_val.comp continuous_subtype_val).comp continuous_snd
  have h2 : Continuous fun p : GAF σ JS × GAF σ JT => mtF σ JS p.1⁻¹ := by
    have : (fun g : GAF σ JS => mtF σ JS g⁻¹) =
        fun g => (((Subtype.val (show HR (AF F) σ JS from g))⁻¹ : GL (Fin nS) (AF F ⊗[F] E)) : Matrix _ _ _) := rfl
    have hi : Continuous fun g : GAF σ JS => mtF σ JS g⁻¹ := by
      rw [this]; exact Units.continuous_coe_inv.comp continuous_subtype_val
    exact hi.comp continuous_fst
  have e : (mMF σ JS JT θ : GAF σ JS × GAF σ JT → _) = fun p =>
      GlobalTheory.RealWeil.blk (fun w => compAtF θ w (mtF σ JT p.2)) fun w => compAtF θ w (mtF σ JS p.1⁻¹) := funext fun p => rfl
  rw [e]
  exact GlobalTheory.RealWeil.continuous_blk (fun w => (hc w _ _).comp h1) fun w => (hc w _ _).comp h2
end GlobalTheory.RealWeilF.MCont
end
end
end

section



section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
noncomputable section
namespace GlobalTheory.RealWeilF
section Unitary
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end Unitary
theorem mMF_unitary_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ p : GAF σ JS × GAF σ JT, (mMF σ JS JT θ p)ᴴ * HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) * mMF σ JS JT θ p = HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ θ hθ ι _ p
  obtain ⟨g, h⟩ := p
  have hσ : ∀ w x, (B.emb w).1 (σ x) = star ((B.emb w).1 x) := fun w x => hB.cm.2.2.2 _ x
  unfold HMF
  rw [mMF_apply, blk_conjTranspose, blk_mul, blk_mul]
  congr 1 <;> funext w
  · rw [Matrix.mul_smul, Matrix.smul_mul, compAtF_unitary hσ hθ]
  · have h1 := compAtF_unitary hσ hθ JS g w
    have h2 := compAtF_mul_inv θ JS g w
    conv_rhs => rw [← h1, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← conjTranspose_nonsing_inv, inv_eq_right_inv h2]
end GlobalTheory.RealWeilF
end
end
end

section



section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.RealWeilF
end GlobalTheory.RealWeilF
theorem GlobalTheory.RealWeilF.HMF_herm_det_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1))ᴴ = HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) ∧ (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1)).det ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hσ
  exact GlobalTheory.RealWeilF.hermitianFormRealCoordinateBlock_hermitian_det σ hB.cm.2.2.2 JS JT hS hT ξ₀ h0 hσ _
end
end
