module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle334
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle047
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle322
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle312
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle433
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle389
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle043
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle464
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle367
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle404
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle512
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle405
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle481
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle193
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2275
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle317
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle150
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle218
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle354
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle514
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle220
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle294
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle137
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneTupleRowsCuspFormsIsometricThetaLifts
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
import Std.Tactic.BVDecide.Normalize.BitVec
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Compactness.Paracompact
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay
open scoped TensorProduct ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift

variable {D : D7} {θ : InfF D}

theorem IsKerSys.lift (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {V W : HSp D} {M : Type} [AddCommGroup M]
    [Module ℂ M] {κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)} (hκ : IsKerSys θ V W κ) {μ : Measure (GA D V)}
    {𝓕 : Set (GA D V)} (hq : IsQuot V μ 𝓕) {F : GA D V → ℂ} (hF : IsCuspForm θ V F) (f : M) :
    (∀ h, IntegrableOn (fun g => κ f g h * F g) 𝓕 μ) ∧ IsAutFunSm θ W fun h => ∫ g in 𝓕, κ f g h * F g ∂μ := by
  have hD := GlobalTheory.T.smoothCuspForm_mem_unitaryRapidDecayForms hP D θ hθ V F hF
  obtain ⟨h1, h2, ⟨N, h3⟩, h4⟩ := GlobalTheory.T.thetaKernelLift_converges_continuous_growth_deriv D θ hθ V W M κ hκ μ 𝓕 hq F hD
  let L : M → GA D W → ℂ := fun f h => ∫ g in 𝓕, κ f g h * F g ∂μ
  have hd : ∀ f τ, ∀ X ∈ lieAt W τ, ∃ f', ∀ h,
      HasDerivAt (fun t : ℝ => L f (h * oneP θ W τ X t)) (L f' h) 0 := fun f τ X hX =>
    (hκ.derW τ X hX f).imp fun f' e => h4 τ X hX f f' e
  refine ⟨h1 f, ⟨fun γ hγ h => ?_, ?_, h2 f⟩, ?_, GlobalTheory.T.kernelLift_gelfandInvariantFinite_of_finite D θ hθ V W M κ hκ μ 𝓕 hq F hD hF.1.zfin f, ?_⟩
  · have := fun g => hκ.left f 1 (one_mem _) γ hγ g h
    simp only [one_mul] at this
    simp only [this]
  · obtain ⟨U, U', -, hU', e⟩ := hκ.level f
    refine ⟨U', hU', fun k a b h => ?_⟩
    have := fun g => e 1 (one_mem _) (one_mem _) k a b g h
    simp only [mul_one] at this
    simp only [this]
  · refine GlobalTheory.T.mem_smoothFunctions_of_closed_rightDerivatives D θ hθ W (Set.range L) ?_ ?_ _ ⟨f, rfl⟩
    · rintro _ ⟨f, rfl⟩
      exact h2 f
    · rintro _ ⟨f, rfl⟩ τ X hX
      obtain ⟨f', e⟩ := hd f τ X hX
      exact ⟨_, ⟨f', rfl⟩, e⟩
  · obtain ⟨K, hK⟩ := GlobalTheory.T.unitaryAdelicHeight_coset_le_normInf_pow D θ W
    refine ⟨K * N, fun l hl x => ?_⟩
    have hw : ∃ f', l.foldr (fun p φ => Rder θ W p.1 p.2 φ) (L f) = L f' := by
      induction l with
      | nil => exact ⟨f, rfl⟩
      | cons p l ih =>
        obtain ⟨f', e⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
        obtain ⟨f'', e'⟩ := hd f' p.1 p.2 (hl p List.mem_cons_self)
        exact ⟨f'', by rw [List.foldr_cons, e]; exact funext fun h => (e' h).deriv⟩
    obtain ⟨f', e⟩ := hw
    obtain ⟨C, hC⟩ := h3 f'
    obtain ⟨C', hC'⟩ := hK x
    refine ⟨|C| * C' ^ N, fun g hg => ?_⟩
    rw [show (fun h => ∫ g in 𝓕, κ f g h * F g ∂μ) = L f from rfl, e]
    refine (hC _).trans ?_
    rw [pow_mul, mul_assoc, ← mul_pow]
    exact mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (NNReal.coe_nonneg _) (hC' g hg) N)
      (pow_nonneg (NNReal.coe_nonneg _) N) (abs_nonneg _)

def matLin {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A where
  toFun X := ∑ i, ∑ j, X i j • E i j
  map_add' X Y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c X := by simp [Finset.smul_sum, mul_smul]

theorem matLin_single {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (i j : Fin n) :
    matLin E (Matrix.single i j 1) = E i j := by
  simp [matLin, Matrix.single, ite_and]

theorem isKerSys_thKer (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hw : GlobalTheory.Ker.IsWeak ψ S T om) (hc : OmCont ψ S T om) :
    IsKerSys θ S T (thKer ψ S T om) := by
  have cont : ∀ f, Continuous fun p : GA D S × GA D T => thKer ψ S T om f p.1 p.2 := fun f => hc f.1 f.2 0
  have left : ∀ f, ∀ γ ∈ GQ S, ∀ δ ∈ GQ T, ∀ g h, thKer ψ S T om f (γ * g) (δ * h) = thKer ψ S T om f g h := by
    intro f γ hγ δ hδ g h
    have e : om (γ * g, δ * h) = om (γ, δ) * om (g, h) := by rw [← map_mul]; rfl
    change om (γ * g, δ * h) f.1 0 = om (g, h) f.1 0
    rw [e]
    exact hw.om_aut γ hγ δ hδ _ (hw.om_pres _ _ f.2)
  have level : ∀ f, ∃ (U : Subgroup (GA D S)) (U' : Subgroup (GA D T)), IsOpen (U : Set (GA D S)) ∧
      IsOpen (U' : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC S → ∀ k' ∈ U', k' ∈ GfC T → ∀ g h,
        thKer ψ S T om f (g * k) (h * k') = thKer ψ S T om f g h := by
    intro f
    obtain ⟨U, U', a, b, e⟩ := GlobalTheory.T.exists_open_level_fixing_theta_function D ψ hψ S T om hw hc f.1 f.2
    refine ⟨U, U', a, b, fun k h1 h2 k' h3 h4 g h => ?_⟩
    have e' : om (g * k, h * k') = om (g, h) * om (k, k') := by rw [← map_mul]; rfl
    change om (g * k, h * k') f.1 0 = om (g, h) f.1 0
    rw [e', mul_apply_eq_comp, e k h1 h2 k' h3 h4]
  obtain ⟨x, d, hx⟩ := GlobalTheory.T.thetaKernel_lieAction_through_weylAlgebra D ψ hψ S T om hw hc θ hθ
  have derV : ∀ τ, ∀ X ∈ lieAt S τ, ∀ f, ∃ f', ∀ g h,
      HasDerivAt (fun t : ℝ => thKer ψ S T om f (g * oneP θ S τ X t) h) (thKer ψ S T om f' g h) 0 :=
    fun τ X hX f => ((hx τ).2.2 X hX).elim fun _ e => ⟨_, e f⟩
  have derW : ∀ τ, ∀ X ∈ lieAt T τ, ∀ f, ∃ f', ∀ g h,
      HasDerivAt (fun t : ℝ => thKer ψ S T om f g (h * oneP θ T τ X t)) (thKer ψ S T om f' g h) 0 :=
    fun τ X hX f => ((hx τ).2.1 X hX).elim fun _ e => ⟨_, e f⟩
  refine ⟨cont, left, level, ?_, derV, derW, fun τ => ?_⟩
  · obtain ⟨N, hN⟩ := GlobalTheory.T.weilRep_thetaFunction_polynomialGrowth_realPoints D ψ hψ S T om hw θ hθ
    obtain ⟨N', hN'⟩ := GlobalTheory.T.adelicHeight_growth_of_cosetGrowth_unitaryPair D θ hθ S T N
    exact ⟨N', fun f => hN' _ (left f) (level f) fun x y =>
      (hN f.1 f.2 x y).imp fun C e a ha b hb => e a ha b hb 0⟩
  · have sT : ∀ f g, thKer ψ S T om f g ∈ SmFun θ T := fun f g => by
      refine GlobalTheory.T.mem_smoothFunctions_of_closed_rightDerivatives D θ hθ T (Set.range fun f => thKer ψ S T om f g) ?_ ?_ _ ⟨f, rfl⟩
      · rintro _ ⟨f, rfl⟩
        exact (cont f).comp (Continuous.prodMk_right g)
      · rintro _ ⟨f, rfl⟩ τ X hX
        obtain ⟨f', e⟩ := derW τ X hX f
        exact ⟨_, ⟨f', rfl⟩, e g⟩
    have sS : ∀ f h, swapKer (thKer ψ S T om) f h ∈ SmFun θ S := fun f h => by
      refine GlobalTheory.T.mem_smoothFunctions_of_closed_rightDerivatives D θ hθ S (Set.range fun f => swapKer (thKer ψ S T om) f h) ?_ ?_ _ ⟨f, rfl⟩
      · rintro _ ⟨f, rfl⟩
        exact (cont f).comp (Continuous.prodMk_left h)
      · rintro _ ⟨f, rfl⟩ τ X hX
        obtain ⟨f', e⟩ := derV τ X hX f
        exact ⟨_, ⟨f', rfl⟩, fun g => e g h⟩
    obtain ⟨g1, g2⟩ := GlobalTheory.T.glRel_of_canonicalCommutationRelations _ _ _ (x τ) (d τ) (hx τ).1
    obtain ⟨c, e1⟩ := GlobalTheory.T.gelfandInvariants_act_kernelFamily_shifted D θ hθ T _ _ (thKer ψ S T om) sT τ (matLin fun i j => ∑ a, x τ (i, a) * d τ (j, a))
      (by simpa only [matLin_single] using g1) (hx τ).2.1
    obtain ⟨c', e2⟩ := GlobalTheory.T.gelfandInvariants_act_kernelFamily_shifted D θ hθ S _ _ (swapKer (thKer ψ S T om)) sS τ
      (matLin fun a b => -∑ i, x τ (i, b) * d τ (i, a)) (by simpa only [matLin_single] using g2)
      fun Y hY => ((hx τ).2.2 Y hY).imp fun _ e f h g => e f g h
    simp only [matLin_single] at e1 e2
    exact ⟨_, _, e2, e1, (GlobalTheory.T.adjoin_gelfandInvariants_dual_pair_eq _ _ _ (x τ) (d τ) (hx τ).1 c c').symm⟩

theorem toTWsmall_zero (S T : HSp D) : toTWsmall S T 0 = 0 := by
  unfold toTWsmall
  rw [Matrix.zero_mul, Matrix.transpose_zero]

theorem exists_thKer {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (Wf : WeilFun D ψ) {V W : HSp D}
    {χ χ' : IdC D} (ha : admitted V W χ χ') (hr : V.rank < W.rank) :
    ∃ om, GlobalTheory.Ker.IsWeak ψ V W om ∧ OmCont ψ V W om ∧
      ∀ Φ, ∃ f, ∀ g h, Wf.ker V W χ χ' Φ g h = thKer ψ V W om f g h := by
  obtain ⟨om, H, e⟩ := GlobalTheory.T.exists_orientedWeilDatum_of_adelicWeilRep_theta D ψ hψ V W χ χ' _ ha hr (Wf.core.weil V W χ χ' ha)
  obtain ⟨E, -, -, hE, -, -, -, h7, -⟩ := GlobalTheory.OrientedCoord.exists_coord D V W hr.le
  refine ⟨om, GlobalTheory.Ker.isWeak_of_datum H, H.om_cont, fun Φ => ⟨⟨fun x => Φ.1 (toTWsmall V W x), ?_⟩, fun g h => ?_⟩⟩
  · have := (h7 ψ Φ.1).2 (mem_ThS.1 Φ.2)
    simp only [hE] at this
    exact this
  · have := congrFun (e (g, h) Φ) 0
    rw [toTWsmall_zero] at this
    exact this.symm

theorem liftAut : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, LiftAut D := by
  intro hP D θ hθ ψ hψ Wf V W χ χ' ha μ 𝓕 hq Φ F hF
  rcases lt_or_gt_of_ne ha.1 with hr | hr
  · obtain ⟨om, hw, hc, e⟩ := exists_thKer hψ Wf ha hr
    obtain ⟨f, e⟩ := e Φ
    simp only [e]
    exact (isKerSys_thKer hθ hψ hw hc).lift hP hθ hq hF f
  · have ha' : admitted W V χ' χ := ⟨ha.1.symm, ha.2.2.1, ha.2.1, ha.2.2.2.2, ha.2.2.2.1⟩
    obtain ⟨om, hw, hc, e⟩ := exists_thKer hψ Wf ha' hr
    have hΦ := (GlobalTheory.Mem.ThetaClosed.thetaFun_closed D ψ hψ V W Φ.1).2.2 ha.1 (mem_ThS.1 Φ.2)
    obtain ⟨f, e⟩ := e ⟨_, mem_ThS.2 hΦ⟩
    have e' : ∀ g h, Wf.ker V W χ χ' Φ g h = swapKer (thKer ψ W V om) f g h := fun g h =>
      (Wf.om_swap V W χ χ' ha g h Φ ⟨_, mem_ThS.2 hΦ⟩ (fun _ => rfl) 0).symm.trans (e h g)
    simp only [e']
    have hk := isKerSys_thKer hθ hψ hw hc
    have hs : IsKerSys θ V W (swapKer (thKer ψ W V om)) := by
      refine ⟨fun f => (hk.cont f).comp continuous_swap, fun f γ hγ δ hδ g g' =>
        hk.left f δ hδ γ hγ g' g, ?_, ?_, ?_, ?_, ?_⟩
      · intro f
        obtain ⟨U, U', hU, hU', hk'⟩ := hk.level f
        exact ⟨U', U, hU', hU, fun k hk1 hk2 k' hk1' hk2' g g' =>
          hk' k' hk1' hk2' k hk1 hk2 g' g⟩
      · obtain ⟨N, hN⟩ := hk.growth
        refine ⟨N, fun f => ?_⟩
        obtain ⟨C, hC⟩ := hN f
        refine ⟨C, fun g g' => ?_⟩
        have hb := hC g' g
        rw [mul_comm (height θ W g' : ℝ)] at hb
        exact hb
      · intro τ X hX f
        obtain ⟨f', hf'⟩ := hk.derW τ X hX f
        exact ⟨f', fun g g' => hf' g' g⟩
      · intro τ X hX f
        obtain ⟨f', hf'⟩ := hk.derV τ X hX f
        exact ⟨f', fun g g' => hf' g' g⟩
      · intro τ
        obtain ⟨a, b, ha, hb, hab⟩ := hk.cap τ
        exact ⟨b, a, fun k f g' => hb k f g', fun k f g => ha k f g, hab.symm⟩
    exact hs.lift hP hθ hq hF f

end GlobalTheory.Mem.Lift

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompactAction

theorem trace_Jm {n p q : ℕ} (h : p + q = n) (ε : Fin n → Bool) (hε : ∀ a, ε a = decide ((a : ℕ) < p)) :
    (Formalism.REAL.Jm ε).trace = (p : ℂ) - q := by
  subst h
  unfold Formalism.REAL.Jm
  rw [Matrix.trace_diagonal, Fin.sum_univ_add]
  simp [hε, sub_eq_add_neg]

theorem isCartanInv_one {n : ℕ} {G B : Matrix (Fin n) (Fin n) ℂ} (h : Bᴴ * G * B = 1) : IsCartanInv G 1 := by
  have hB : B * (Bᴴ * G) = 1 := mul_eq_one_comm.1 h
  have hi : B⁻¹ = Bᴴ * G := Matrix.inv_eq_right_inv hB
  have hu : IsUnit B := IsUnit.of_mul_eq_one _ hB
  have hG : G = (B⁻¹)ᴴ * B⁻¹ := by
    have h1 : (B⁻¹)ᴴ * Bᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hi, hB, Matrix.conjTranspose_one]
    calc G = ((B⁻¹)ᴴ * Bᴴ) * G := by rw [h1, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, ← hi]
  refine ⟨by simp, by simp, ?_⟩
  rw [Matrix.mul_one, hG]
  refine Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit ?_)
  exact (Matrix.isUnit_nonsing_inv_iff).2 hu

theorem conj_unitary {n : ℕ} {G B g : Matrix (Fin n) (Fin n) ℂ} (h : Bᴴ * G * B = 1) (hg : gᴴ * G * g = G) :
    B⁻¹ * g * B ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hB : B * (Bᴴ * G) = 1 := mul_eq_one_comm.1 h
  have hi : B⁻¹ = Bᴴ * G := Matrix.inv_eq_right_inv hB
  have h0 : B * B⁻¹ = 1 := by rw [hi, hB]
  have h1 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h0, Matrix.conjTranspose_one]
  have hG : (B⁻¹)ᴴ * B⁻¹ = G := by
    calc _ = (B⁻¹)ᴴ * (Bᴴ * G) := by rw [← hi]
      _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  calc _ = Bᴴ * (gᴴ * ((B⁻¹)ᴴ * B⁻¹) * g) * B := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hG, hg, h]

theorem det_conj {n : ℕ} {F F' : Matrix (Fin n) (Fin n) ℂ} (h : F' * F = 1) (A C x : Matrix (Fin n) (Fin n) ℂ) :
    (A * (F * x * F') + C).det = (F' * A * F * x + F' * C * F).det := by
  have e : F' * A * F * x + F' * C * F = F' * (A * (F * x * F') + C) * F := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, h, Matrix.mul_one]
  have hd : F'.det * F.det = 1 := by rw [← Matrix.det_mul, h, Matrix.det_one]
  rw [e, Matrix.det_mul, Matrix.det_mul]
  linear_combination (-(A * (F * x * F') + C).det) * hd

theorem pureTensorO_smul {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (c : ℂ) (f : WO S T → ℂ) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (c • f) P = c • pureTensorO ψ θ S T sS sT BS BT f P := by
  have hd : ∀ τ z (f : WO S T → ℂ), dRho (heisO ψ S T) θ τ z (c • f) = c • dRho (heisO ψ S T) θ τ z f := by
    intro τ z f
    funext x
    simp only [Formalism.IndefR.Datum.dRho, heisO, Pi.smul_apply, smul_eq_mul]
    rw [← deriv_const_mul_field]
    congr 1
    funext t
    ring
  refine (GlobalTheory.OrientedHeis.pureTensorL_intertwine (fun _ => True) trivial (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial) _ _ (c • (1 : Module.End ℂ (WO S T → ℂ))) (fun k f _ => ⟨trivial, ?_⟩) f trivial P).2.symm
  simp only [aPlusAll, Formalism.IndefR.Datum.aPlus, crea, LinearMap.smul_apply, Module.End.one_apply, hd]
  rw [smul_comm Complex.I c, ← smul_sub, smul_comm]

theorem om_pureTensorO_eq_fact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → S.SigOK → T.SigOK → (∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) → ∀ (p q : D.what₂.Tau → ℕ), (∀ τ, p τ + q τ = T.rank) → (∀ τ a, M.ε τ a = decide ((a : ℕ) < p τ)) → ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D χS τ (a τ)) → (∀ τ, HasInfExp D χT τ (b τ)) → ∀ (x₁ x₂ x₃ : D.what₂.Tau → ℤ), (∀ τ, (x₁ τ : ℚ) = a τ + (S.rank : ℚ) / 2) → (∀ τ, (x₂ τ : ℚ) = a τ - (S.rank : ℚ) / 2) → (∀ τ, (x₃ τ : ℚ) = -(((p τ : ℚ) - q τ) / 2 + b τ)) → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) f) → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, (∀ τ, M.fr τ * compAt θ τ (Formalism.L2.Theta.mt T h) * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)) → (∀ τ, (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) ∧ ∀ P : PolF D T.rank S.rank, om (g, h) (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f P) = pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f (fact M.ε x₁ x₂ x₃ (fun τ => M.fr τ * compAt θ τ (Formalism.L2.Theta.mt T h) * (M.fr τ)⁻¹) (fun τ => (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ) P) := by
  intro D ψ θ S T χS χT om Sp M BS hom hθ hS hT hBS p q hpq hε a b ha hb x₁ x₂ x₃ h₁ h₂ h₃ f hf hv g hg h hh hk
  have hu : ∀ τ, (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ ∈ Matrix.unitaryGroup (Fin S.rank) ℂ :=
    fun τ => conj_unitary (hBS τ) (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ S g τ)
  refine ⟨hu, fun P => ?_⟩
  have f1 : ∀ τ, M.fr τ * (M.fr τ)⁻¹ = 1 := fun τ =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ))
  have f2 : ∀ τ, (M.fr τ)⁻¹ * M.fr τ = 1 := fun τ => mul_eq_one_comm.1 (f1 τ)
  have b1 : ∀ τ, BS τ * (BS τ)⁻¹ = 1 := fun τ => by
    have hB : BS τ * ((BS τ)ᴴ * gramAt D S τ) = 1 := mul_eq_one_comm.1 (hBS τ)
    rw [Matrix.inv_eq_right_inv hB, hB]
  have hc : ∀ τ, cart M τ * compAt θ τ (Formalism.L2.Theta.mt T h) = compAt θ τ (Formalism.L2.Theta.mt T h) * cart M τ := fun τ => by
    have e := congrArg (fun X => (M.fr τ)⁻¹ * X * M.fr τ) (hk τ).2
    simp only [Matrix.mul_assoc, f2, Matrix.mul_one] at e
    rw [← Matrix.mul_assoc (M.fr τ)⁻¹ (M.fr τ), f2, Matrix.one_mul] at e
    unfold cart
    simp only [Matrix.mul_assoc]
    exact e.symm
  have htr : ∀ τ, (cart M τ).trace = (p τ : ℂ) - q τ := fun τ => by
    unfold cart
    rw [Matrix.trace_mul_cycle, f1, Matrix.one_mul, trace_Jm (hpq τ) _ (hε τ)]
  have hvac := GlobalTheory.T.vacuum_character_positive_definite_source D ψ θ S T χS χT om hom hθ hS hT (cart M) (fun τ => isCartanInv_one (hBS τ))
    (GlobalTheory.Chain.VacVec.cart_isCartanInv M) a b ha hb x₁ x₂ x₃ h₁ h₂ (fun τ => by
      rw [htr]
      have := congrArg (fun x : ℚ => (x : ℂ)) (h₃ τ)
      push_cast at this
      exact this) f hf hv g hg h hh hc
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hom hθ (fun _ => 1) (fun _ => 1) BS
    (fun τ => BS τ * ((BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ)) (cart M) (cart M) (onb M)
    (fun τ => onb M τ * (M.fr τ * compAt θ τ (Formalism.L2.Theta.mt T h) * (M.fr τ)⁻¹)) g h
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) hc
    (fun τ => by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, b1, Matrix.one_mul])
    (fun τ => by unfold onb; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, f2, Matrix.one_mul]) f hf P).2,
    GlobalTheory.T.fockPolynomialVector_change_orthonormalBases_subst D ψ θ S T Sp M BS hom.std hθ hBS _ _ hk hu _ (hom.om_pres _ _ hf), hvac, pureTensorO_smul]
  unfold fact
  rw [LinearMap.smul_apply, map_smul]
  congr 1
  unfold fchar
  refine Finset.prod_congr rfl fun τ _ => ?_
  have eP : (M.fr τ)⁻¹ * ((1 / 2 : ℂ) • (1 + Formalism.REAL.Jm (M.ε τ))) * M.fr τ = (1 / 2 : ℂ) • (1 + cart M τ) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, f2]; rfl
  have eM : (M.fr τ)⁻¹ * ((1 / 2 : ℂ) • (1 - Formalism.REAL.Jm (M.ε τ))) * M.fr τ = (1 / 2 : ℂ) • (1 - cart M τ) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, f2]; rfl
  have eU : ((BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ).det = (compAt θ τ (Formalism.L2.Theta.mt S g)).det := by
    rw [Matrix.det_mul_comm, ← Matrix.mul_assoc, b1, Matrix.one_mul]
  unfold detP detM
  rw [det_conj (f2 τ), det_conj (f2 τ), eP, eM, eU]

end GlobalTheory.FockCompactAction

end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.DefLiftDer

theorem hasDerivAt_integral_of_cocompact {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup H) [Countable Γ] (μ : Measure H)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] (𝓕 C : Set H)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hC : IsCompact C)
    (hcov : ∀ h : H, ∃ γ ∈ Γ, ∃ c ∈ C, h = γ * c) (K K' : ℝ → H → ℂ)
    (hK : ∀ t, Continuous (K t)) (hK' : Continuous fun p : ℝ × H => K' p.1 p.2)
    (hinv : ∀ γ ∈ Γ, ∀ t h, K t (γ * h) = K t h) (hinv' : ∀ γ ∈ Γ, ∀ t h, K' t (γ * h) = K' t h)
    (hd : ∀ t h, HasDerivAt (fun s => K s h) (K' t h) t) (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ h in 𝓕, K t h ∂μ) (∫ h in 𝓕, K' t₀ h ∂μ) t₀ := by
  obtain ⟨N, hN, hN₀⟩ := exists_compact_mem_nhds t₀
  obtain ⟨M, hM⟩ := (hN.prod hC).exists_bound_of_continuousOn hK'.continuousOn
  have hconst : IntegrableOn (fun _ : H => (M : ℂ)) 𝓕 μ :=
    GlobalTheory.CocompactIntegrable.integrableOn_of_cocompact Γ μ 𝓕 C h𝓕 hC hcov _ continuous_const
      (fun _ _ _ => rfl)
  have hconst' : Integrable (fun _ : H => M) (μ.restrict 𝓕) := by
    have h := hconst.re
    change Integrable (fun _ : H => Complex.re (M : ℂ)) (μ.restrict 𝓕) at h
    simpa only [Complex.ofReal_re] using h
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => M) hN₀
    (Filter.Eventually.of_forall fun t => (hK t).aestronglyMeasurable)
    (GlobalTheory.CocompactIntegrable.integrableOn_of_cocompact Γ μ 𝓕 C h𝓕 hC hcov _ (hK t₀) (fun γ hγ h => hinv γ hγ t₀ h))
    (hK'.comp (Continuous.prodMk_right t₀)).aestronglyMeasurable ?_ hconst'
    (Filter.Eventually.of_forall fun h t _ => hd t h)).2
  refine Filter.Eventually.of_forall fun h t ht => ?_
  obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
  rw [hinv' γ hγ]
  exact hM (t, c) ⟨ht, hc⟩

theorem kernel_continuous_invariant {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
    {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hom : IsWeilDatumO ψ S T χS χT om) {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]
    (L : X →ₗ[ℂ] (WO S T → ℂ)) (hL : ∀ x, IsThetaFunO ψ S T (L x)) {F : GA D S → X} (hF : Continuous F)
    (hinv : ∀ γ ∈ GQ S, ∀ h, F (γ * h) = F h) :
    (Continuous fun p : GA D T × GA D S => thetaKO om p.2 p.1 (L (F p.2))) ∧
      (∀ γ ∈ GQ S, ∀ g h, thetaKO om (γ * h) g (L (F (γ * h))) = thetaKO om h g (L (F h))) ∧
      ∀ γ ∈ GQ T, ∀ g h, thetaKO om h (γ * g) (L (F h)) = thetaKO om h g (L (F h)) := by
  refine ⟨?_, fun γ hγ g h => ?_, fun γ hγ g h => ?_⟩
  · let b := Module.finBasis ℂ X
    have e : (fun p : GA D T × GA D S => thetaKO om p.2 p.1 (L (F p.2))) =
        fun p => ∑ k, b.coord k (F p.2) * om (p.2, p.1) (L (b k)) 0 := by
      funext p
      conv_lhs => rw [← b.sum_repr (F p.2)]

      simp only [thetaKO, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Module.Basis.coord_apply]
    rw [e]
    refine continuous_finsetSum _ fun k _ => Continuous.mul ?_ ?_
    · exact ((b.coord k).continuous_of_finiteDimensional.comp hF).comp continuous_snd
    · exact (hom.om_cont _ (hL (b k)) 0).comp continuous_swap
  · have := (GlobalTheory.thetaKO_continuous_and_rat_invariant ψ S T χS χT om hom _ (hL (F h))).2 γ hγ 1 (one_mem _) h g
    rw [one_mul] at this
    rw [hinv γ hγ, this]
  · have := (GlobalTheory.thetaKO_continuous_and_rat_invariant ψ S T χS χT om hom _ (hL (F h))).2 1 (one_mem _) γ hγ h g
    rwa [one_mul] at this

theorem lift_continuous_invariant_hasDerivAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → (∀ τ, (gramAt D S τ).PosDef) → ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO S T → ℂ)), (∀ x, IsThetaFunO ψ S T (L x)) → ∀ F : GA D S → X, Continuous F → (∀ γ ∈ GQ S, ∀ h, F (γ * h) = F h) → ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → (Continuous (lift om ν 𝓕 fun h => L (F h)) ∧ ∀ γ ∈ GQ T, ∀ g, lift om ν 𝓕 (fun h => L (F h)) (γ * g) = lift om ν 𝓕 (fun h => L (F h)) g) ∧ ∀ τ, ∀ Y ∈ lieAt T τ, ∃ L' : X →ₗ[ℂ] (WO S T → ℂ), (∀ x, IsThetaFunO ψ S T (L' x)) ∧ (∀ x h g, HasDerivAt (fun t : ℝ => thetaKO om h (g * oneP θ T τ Y t) (L x)) (thetaKO om h g (L' x)) 0) ∧ ∀ g, HasDerivAt (fun t : ℝ => lift om ν 𝓕 (fun h => L (F h)) (g * oneP θ T τ Y t)) (lift om ν 𝓕 (fun h => L' (F h)) g) 0 := by
  intro D ψ S T χS χT om hom θ hθ hpos X _ _ _ L hL F hF hinv ν 𝓕 hν h𝓕
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact S hpos
  obtain ⟨-, -, -, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T
  obtain ⟨hc, hiS, hiT⟩ := kernel_continuous_invariant hom L hL hF hinv
  refine ⟨⟨?_, fun γ hγ g => ?_⟩, fun τ Y hY => ?_⟩
  · exact GlobalTheory.DefLiftCont.continuous_integral_of_cocompact (GQ S) ν 𝓕 C h𝓕 hC hcov
      (fun g h => thetaKO om h g (L (F h))) hc hiS
  · simp only [GlobalTheory.DefLift.lift, hiT γ hγ]
  · obtain ⟨Gn, hGn⟩ := GlobalTheory.T.exists_weilDatum_generator_realOneParamGroup D ψ S T χS χT om hom θ hθ τ Y hY
    have hL' : ∀ x, IsThetaFunO ψ S T ((Gn ∘ₗ L) x) := fun x => (hGn _ (hL x)).1
    have hd : ∀ x h g, HasDerivAt (fun t : ℝ => thetaKO om h (g * oneP θ T τ Y t) (L x))
        (thetaKO om h g ((Gn ∘ₗ L) x)) 0 := by
      intro x h g
      have := (hGn _ (hL x)).2.2.2 (h, g) 0
      simp only [Prod.mk_mul_mk, mul_one] at this
      exact this
    refine ⟨Gn ∘ₗ L, hL', hd, fun g => ?_⟩
    obtain ⟨hc', hiS', -⟩ := kernel_continuous_invariant hom (Gn ∘ₗ L) hL' hF hinv
    have hp : Continuous fun t : ℝ => g * oneP θ T τ Y t :=
      continuous_const.mul (GlobalTheory.Mem.Lift.continuous_oneP hθ hY)
    have key := hasDerivAt_integral_of_cocompact (GQ S) ν 𝓕 C h𝓕 hC hcov
      (fun t h => thetaKO om h (g * oneP θ T τ Y t) (L (F h)))
      (fun t h => thetaKO om h (g * oneP θ T τ Y t) ((Gn ∘ₗ L) (F h)))
      (fun t => hc.comp (Continuous.prodMk_right (g * oneP θ T τ Y t)))
      (hc'.comp (hp.prodMap continuous_id))
      (fun γ hγ t h => hiS γ hγ _ h) (fun γ hγ t h => hiS' γ hγ _ h)
      (fun t h => GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hY (φ := fun g => thetaKO om h g (L (F h)))
        (φ' := fun g => thetaKO om h g ((Gn ∘ₗ L) (F h))) (hd (F h) h) g t) 0
    simp only [GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at key
    exact key

end GlobalTheory.DefLiftDer
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.oneTuple_rows_cuspForms_isometric_thetaLifts : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsChain → ∀ (t : T) (μ : D.what₂.Tup), (∃ (e : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] R.CC t j) (eX : D.what₂.Mult μ D.R.m →ₗ[ℂ] LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) (ν : ∀ j, Measure (GA D (Yc D j))) (𝓕 : ∀ j, Set (GA D (Yc D j))) (c : ℕ → ℝ) (cX : ℝ), (∀ j, j < D.R.m → IsQuot (Yc D j) (ν j) (𝓕 j) ∧ 0 < c j ∧ ∀ x y, ⟪x, y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (e j y).1 (e j x).1) ∧ (∃ J χ, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) ≤ MultT R.θ R.MX J χ) ∧ 0 < cX ∧ (∀ x y, ⟪x, y⟫_ℂ = (cX : ℂ) * ipT R.MX (R.νX t) (R.fdX t) (eX y).1 (eX x).1) ∧ (∀ j, j + 1 < D.R.m → ∀ x y, ⟪x, D.what₂.io μ j y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (R.ioY t j (e (j + 1) y)).1 (e j x).1) ∧ ∀ x (y : D.what₂.Mult μ (D.R.m - 1 + 1)) (y' : D.what₂.Mult μ D.R.m), HEq y y' → ⟪x, D.what₂.io μ (D.R.m - 1) y⟫_ℂ = (c (D.R.m - 1) : ℂ) * ipT (R.MY (D.R.m - 1)) (ν (D.R.m - 1)) (𝓕 (D.R.m - 1)) (R.ioX t (eX y')).1 (e (D.R.m - 1) x).1) → ∀ (Wf : WeilFun D R.ψ) (κ : ℕ → ℝ), (∀ j, 0 < κ j) → ∃ (row : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] CuspS R.θ (D.sp.Y j)) (Phi : ∀ j, ThS R.ψ (D.sp.Y (j + 1)) (D.sp.Y j)), (∀ j, j < D.R.m → Phi j ≠ 0) ∧ (∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (κ j) (fun h => star ((row j x).1 h) * (row j y).1 h) (inner ℂ x y)) ∧ ∀ j, j < D.R.m → ∀ y : D.what₂.Mult μ (j + 1), ∃ L : GA D (D.sp.Y j) → ℂ, (∀ g, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y (j + 1)) (κ (j + 1)) (fun h => Wf.ker _ _ (if Even (j + 1) then R.toLevCh.mu t (j + 1) * R.eta⁻¹ else R.toLevCh.mu t (j + 1)) (if Even j then R.toLevCh.mu t (j + 1) * R.eta⁻¹ else R.toLevCh.mu t (j + 1)) (Phi j) h g * (row (j + 1) y).1 h) (L g)) ∧ ∀ x : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (κ j) (fun g => star (L g) * (row j x).1 g) (inner ℂ (D.what₂.io μ j y) x) := by
  first | exact @GlobalTheory.Mem.OneTuple.rows_theta | exact GlobalTheory.Mem.OneTuple.rows_theta | (intros; apply GlobalTheory.Mem.OneTuple.rows_theta <;> assumption)
end
