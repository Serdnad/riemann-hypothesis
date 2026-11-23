module

public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1542
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeValuesSameParameters
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle614
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle249
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle785
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle301
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle352
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace PSmo

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem val_eq_prod {π : CuspSub E a} {ω : HChar E} (hω : π.HasCentChar ω) {w : HeightOneSpectrum (𝓞 E)}
    {B : Multiset ℂˣ} (hB : HasSatGL w (π.locRep w) B) : ω.val w = B.prod := by
  classical
  obtain ⟨x, hx⟩ := hB.exists_vec
  set u : (w.adicCompletion E)ˣ := atFin w (unif w) with hu_def
  have hu : IsUnifV E w (u : w.adicCompletion E) := unif_spec w
  have h0 : (u : w.adicCompletion E) ≠ 0 := u.ne_zero

  have hTn : Tj ℂ a (Ov E w) (u : w.adicCompletion E) a =
      dosetInd ℂ (KGL w (n := a)) (GlobalTheory.WeylGL.tor h0 fun _ => 1) := by
    rw [GlobalTheory.WeylGL.Tj_eq h0]; simp
  have h1 := hx.2.2.2 _ hu a le_rfl
  rw [hTn, heckeVec_dosetInd (R := {GlobalTheory.WeylGL.tor h0 fun _ => 1}) hx.2.1, Finset.sum_singleton] at h1
  rotate_left
  · intro γ hγ
    exact GlobalTheory.WeylGL.mem_doset.2 ⟨1, one_mem _, 1, one_mem _, by simpa using hγ⟩
  · intro g hg
    obtain ⟨c, hc, d, hd, rfl⟩ := GlobalTheory.WeylGL.mem_doset.1 hg
    refine ⟨_, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
    rw [← GlobalTheory.WeylGL.tor_const_comm, mul_assoc, inv_mul_cancel_left]
    exact mul_mem hc hd
  have ht : GlobalTheory.WeylGL.tor h0 (fun _ : Fin a => (1 : ℤ)) = GeneralLinearGroup.scalar (Fin a) u := by
    ext i j
    simp [GlobalTheory.WeylGL.tor_val, Matrix.diagonal_apply]
  have hz : locGL E a w (GeneralLinearGroup.scalar (Fin a) u) =
      GeneralLinearGroup.scalar (Fin a) (Units.map (corner (sLoc E w)) u) := cornerGL_scalar _ u
  have e1 := finId_det_locGL (E := E) (a := 1) w (GeneralLinearGroup.scalar (Fin 1) u)
  have e2 : GeneralLinearGroup.det (locGL E 1 w (GeneralLinearGroup.scalar (Fin 1) u)) =
      Units.map (corner (sLoc E w)) u := by
    rw [locGL, cornerGL_scalar]; ext; simp
  have e3 : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 1) u) = u := by ext; simp
  rw [e2, e3] at e1
  have hf : ω.1 (finId E (Units.map (corner (sLoc E w)) u)) = ω.val w := by rw [e1]; rfl
  have h2 : π.locRep w (GeneralLinearGroup.scalar (Fin a) u) x = ((ω.val w : ℂˣ) : ℂ) • x := by
    rw [CuspSub.locRep_eq, hz]
    have := hω (Units.map (corner (sLoc E w)) u) x
    change _ = ((ω.1 (finId E (Units.map (corner (sLoc E w)) u)) : ℂˣ) : ℂ) • x at this
    rw [hf] at this
    exact this
  rw [ht, h2] at h1
  have h3 : satEig (qV E w) a B a = ((B.prod : ℂˣ) : ℂ) := by
    have hc : (B.map fun b : ℂˣ => (b : ℂ)).card = a := by rw [Multiset.card_map]; exact hx.2.2.1
    rw [satEig, sub_self, mul_zero, zero_div, Complex.cpow_zero, one_mul]
    conv_lhs => rw [← hc]
    rw [Multiset.esymm, Multiset.powersetCard_self, Multiset.map_singleton, Multiset.sum_singleton]
    exact (map_multiset_prod (Units.coeHom ℂ) B).symm
  rw [h3] at h1
  exact Units.ext (smul_left_injective ℂ hx.1 h1)

theorem central_eq (hG : HeckeCharacterRigidity) {π π' : CuspSub E a} (h : SameSat π π') {ω ω' : HChar E} (hω : π.HasCentChar ω)
    (hω' : π'.HasCentChar ω') : ω = ω' :=
  hG E ω ω' (h.mono fun _ ⟨_, h1, h2⟩ => (val_eq_prod hω h1).trans (val_eq_prod hω' h2).symm)

theorem sameSat_twist {π π' : CuspSub E a} (h : SameSat π π') (ν : HChar E) : SameSat (π.twist ν) (π'.twist ν) := by
  filter_upwards [h, Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified ν)] with w ⟨B, h1, h2⟩ hν
  exact ⟨B.map (· * ν.val w), GlobalTheory.SphGal.hasSatGL_twist E a π ν w B hν h1,
    GlobalTheory.SphGal.hasSatGL_twist E a π' ν w B hν h2⟩

end PSmo

theorem smo_of : SmoNorm → HeckeCharacterRigidity → Smo := by
  intro hS hG E _ _ _ a π π' h
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact hS E 0 π π' (GlobalTheory.CompanionTheory.TwistNorm.isNormalised_rank_zero π) (GlobalTheory.CompanionTheory.TwistNorm.isNormalised_rank_zero π') h
  obtain ⟨ω, hω⟩ := Central.exists_hasCentral E a π
  obtain ⟨ω', hω'⟩ := Central.exists_hasCentral E a π'
  obtain rfl : ω = ω' := PSmo.central_eq hG h (CuspSub.hasCentral_iff.1 hω) (CuspSub.hasCentral_iff.1 hω')
  obtain ⟨ν, hν⟩ := GlobalTheory.SplitCentreChar.exists_hChar_splitCentre E a ha (dchi ω 1)
  have e := hS E a _ _ (GlobalTheory.CompanionTheory.TwistNorm.isNormalised_twist hω hν) (GlobalTheory.CompanionTheory.TwistNorm.isNormalised_twist hω' hν)
    (PSmo.sameSat_twist h ν)
  have e' := congrArg (fun σ : CuspSub E a => σ.twist ν⁻¹) e
  simpa only [← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one] using e'

end PositivityTheory.jumpWindows

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace GeneralLinearInduction

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {ψ : AddChar (Ad E) ℂ}

theorem step (hψ : StdPsi ψ) (m : ℕ) (f : GA E a → ℂ) (hma : m + 1 < a) (hG : Good ψ (m + 1) f)
    (Z : Set (GA E a)) (hZ : ∀ γ, IsMir (m + 1) γ → ∀ g ∈ Z, ratGL E a γ * g ∈ Z)
    (hc : ∀ g ∈ Z, colT ψ (m + 1) f g = 0) : ∀ g ∈ Z, f g = 0 := by
  intro g₀ hg
  have hPer : Per (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))) (fun x => f (blkU x * g₀)) :=
    per_blk hG.cont (fun c g => hG.left _ (isMir_blkU c) g) g₀
  have hΦ : (fun x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E => f (blkU x * g₀)) = 0 := by
    refine _root_.GlobalTheory.T.periodic_eq_zero_of_fourier_coefficients_zero E _ ψ hψ _ hPer fun ξ => ?_
    by_cases hξ0 : ξ = 0
    · subst hξ0
      have hv := hG.van (m + 1) (Nat.succ_pos m) le_rfl g₀
      have e : ∀ x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E,
          ψ (-dot (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E) x) = 1 := by
        intro x
        simp [dot]
      simp only [e, one_mul]
      exact hv
    · obtain ⟨γ, hγ, hγξ⟩ := _root_.GlobalTheory.T.exists_rationalMirabolic_moving_row_to_last E a m hma ξ hξ0
      have h1 := hc _ (hZ γ hγ g₀ hg)
      simp only [colT] at h1
      rw [_root_.GlobalTheory.T.whittakerCoefficient_rationalMirabolic_mul E a ψ hψ m f hG.cont hG.left γ hγ (eLast a (m + 1)) g₀] at h1
      have e : (fun t : UnipotentBlockColumnIndex a (m + 1) (m + 1) =>
          ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), eLast a (m + 1) s * γ.val s.1.1 t.1.1) = ξ := funext hγξ
      rw [e] at h1
      exact h1
  have h1 := congrFun hΦ 0
  simp only [Pi.zero_apply] at h1
  have e : (blkU (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) : GA E a) = 1 := posU_zero _
  rw [e, one_mul] at h1
  exact h1

theorem main (hψ : StdPsi ψ) (m : ℕ) : ∀ (f : GA E a → ℂ), (m < a ∨ m = 0) → Good ψ m f →
    ∀ Z : Set (GA E a), (∀ γ, IsMir m γ → ∀ g ∈ Z, ratGL E a γ * g ∈ Z) →
      (∀ g ∈ Z, whit ψ m f g = 0) → ∀ g ∈ Z, f g = 0 := by
  induction m with
  | zero => intro f _ _ Z _ hw; exact hw
  | succ m ih =>
    intro f hm hG Z hZ hw
    have hma : m + 1 < a := by omega
    refine step hψ m f hma hG Z hZ ?_
    refine ih _ (Or.inl (by omega)) (_root_.GlobalTheory.CuspRep.Generic.good_colT hψ hma hG) Z
      (fun γ hγ g hg => hZ γ (fun i k h => hγ i k (by omega)) g hg) ?_
    intro g hg
    exact hw g hg

end GeneralLinearInduction

theorem induction_g11_holds : FourierUniquenessMirabolic := by
  intro E _ _ _ a ψ hψ m f hm hG Z hZ _ hw
  exact GeneralLinearInduction.main hψ m f hm hG Z hZ hw

end PositivityTheory.jumpWindows

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host
open GlobalTheory.CuspRep.Generic

namespace PositivityTheory.jumpWindows.WhittakerFunctional

section Avg

variable {G : Type} [AddCommGroup G] [TopologicalSpace G]

theorem norm_avg_le (Γ : AddSubgroup G) (Φ : G → ℂ) {C : ℝ} (h0 : 0 ≤ C) (hC : ∀ x, ‖Φ x‖ ≤ C) :
    ‖avg Γ Φ‖ ≤ C := by
  let _ : MeasurableSpace G := borel G
  unfold avg
  split_ifs with h
  · have h1 := h.choose_spec.2.2
    have hs : h.choose.1 h.choose.2 < ⊤ := by rw [h1]; exact ENNReal.one_lt_top
    have := norm_setIntegral_le_of_norm_le_const hs (f := Φ) (fun x _ => hC x)
    simpa [Measure.real, h1] using this
  · simpa using h0

end Avg

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {ψ : AddChar (Ad E) ℂ}

theorem norm_colT_le (hψ : StdPsi ψ) (k : ℕ) {f : GA E a → ℂ} {C : ℝ} (h0 : 0 ≤ C) (hf : ∀ g, ‖f g‖ ≤ C)
    (g : GA E a) : ‖colT ψ k f g‖ ≤ C := by
  refine norm_avg_le _ _ h0 fun x => ?_
  rw [norm_mul, hψ.norm, one_mul]
  exact hf _

theorem norm_whit_le (hψ : StdPsi ψ) (m : ℕ) {f : GA E a → ℂ} {C : ℝ} (h0 : 0 ≤ C) (hf : ∀ g, ‖f g‖ ≤ C)
    (g : GA E a) : ‖whit ψ m f g‖ ≤ C := by
  induction m generalizing f g with
  | zero => exact hf g
  | succ m ih =>
    rw [whit_succ]
    exact ih (fun g => norm_colT_le hψ (m + 1) h0 hf g) g

theorem good_add {m : ℕ} {f f' : GA E a → ℂ} (hf : Good ψ m f) (hf' : Good ψ m f') :
    Good ψ m (fun g => f g + f' g) := by
  refine ⟨hf.cont.add hf'.cont, ?_, ?_, ?_⟩
  · intro γ hγ g
    simp only [hf.left γ hγ g, hf'.left γ hγ g]
  · intro k hk y g
    simp only [hf.law k hk y g, hf'.law k hk y g, mul_add]
  · intro r hr hrm g
    have := GlobalTheory.T.quotientAverage_add_of_periodic _ (ratV E (UnipotentBlockColumnIndex a r m)) (isCoLat_ratV E _) _ _
      (per_blk hf.cont (fun c g => hf.left _ (isMir_blkU c) g) g)
      (per_blk hf'.cont (fun c g => hf'.left _ (isMir_blkU c) g) g)
    rw [this, hf.van r hr hrm g, hf'.van r hr hrm g, add_zero]

theorem good_smul (c : ℂ) {m : ℕ} {f : GA E a → ℂ} (hf : Good ψ m f) : Good ψ m (fun g => c * f g) := by
  refine ⟨continuous_const.mul hf.cont, ?_, ?_, ?_⟩
  · intro γ hγ g
    simp only [hf.left γ hγ g]
  · intro k hk y g
    simp only [hf.law k hk y g]
    ring
  · intro r hr hrm g
    show avg _ (fun x => c * f (blkU x * g)) = 0
    rw [avg_const_mul, hf.van r hr hrm g, mul_zero]

theorem good_zero (m : ℕ) : Good ψ m (fun _ : GA E a => (0 : ℂ)) := by
  refine ⟨continuous_const, fun _ _ _ => rfl, ?_, ?_⟩
  · intro _ _ _ _
    simp
  · intro r _ _ g
    have := avg_const_mul (ratV E (UnipotentBlockColumnIndex a r m)) 0 (fun _ => 0)
    simpa using this

theorem good_rt {m : ℕ} {f : GA E a → ℂ} (hf : Good ψ m f) (h : GA E a) : Good ψ m (fun x => f (x * h)) := by
  refine ⟨hf.cont.comp (continuous_id.mul continuous_const), ?_, ?_, ?_⟩
  · intro γ hγ g
    simp only [mul_assoc, hf.left γ hγ (g * h)]
  · intro k hk y g
    simp only [mul_assoc, hf.law k hk y (g * h)]
  · intro r hr hrm g
    simp only [mul_assoc]
    exact hf.van r hr hrm (g * h)

theorem dot_eLast (k : ℕ) (y : UnipotentBlockColumnIndex a k k → Ad E) : dot (eLast a k) y = lastE k y := by
  simp only [dot, eLast, lastE]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp


variable (E a) in
def Yg (hψ : StdPsi ψ) : Submodule ℂ (XB E a) where
  carrier := {φ | Good ψ (a - 1) φ}
  add_mem' h h' := good_add h h'
  zero_mem' := good_zero (a - 1)
  smul_mem' c _ h := good_smul c h

def whL (hψ : StdPsi ψ) (g : GA E a) : Yg E a hψ →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun φ => whit ψ (a - 1) (φ.1 : GA E a → ℂ) g
      map_add' := fun φ φ' => congrFun (whit_add hψ (a - 1) (by omega) φ.2 φ'.2) g
      map_smul' := fun c φ => congrFun (whit_smul (a - 1) c (φ.1 : GA E a → ℂ)) g } 1
    fun φ => by
      rw [one_mul]
      exact norm_whit_le hψ _ (norm_nonneg _) (fun g => φ.1.norm_coe_le_norm g) g

end PositivityTheory.jumpWindows.WhittakerFunctional

namespace PositivityTheory.jumpWindows

theorem local_group_averaging_tensor : G5 := by
  intro E _ _ _ a ψ hψ
  have h0 : a - 1 < a ∨ a - 1 = 0 := by omega
  refine ⟨fun g => ?_, fun φ g h => ?_, fun φ h hφ => ?_, fun φ hφ => ⟨?_, fun hne => ?_, fun k hk y g => ?_⟩⟩
  · obtain ⟨Λ, hΛ, -⟩ := exists_extension_norm_eq (WhittakerFunctional.Yg E a hψ) (WhittakerFunctional.whL hψ g)
    refine ⟨Λ, fun φ hφ => ?_⟩
    have := hΛ ⟨φ, hφ⟩
    rw [WhittakerFunctional.whL, LinearMap.mkContinuous_apply] at this
    exact this
  · exact whit_rt (a - 1) φ h g
  · exact WhittakerFunctional.good_rt hφ h
  · exact (whit_good hψ (a - 1) h0 hφ).1.cont
  · have hf : (φ : GA E a → ℂ) ≠ 0 := fun h => hne (DFunLike.coe_injective (by simpa using h))
    obtain ⟨g, hg⟩ := Function.ne_iff.1 ((whit_good hψ (a - 1) h0 hφ).2 hf)
    exact ⟨g, hg⟩
  · rw [← WhittakerFunctional.dot_eLast]
    exact (whit_good hψ (a - 1) h0 hφ).1.law k hk y g

end PositivityTheory.jumpWindows

end
end
