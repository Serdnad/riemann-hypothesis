module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle009
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle240
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceA
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceB
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatCoreB
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open scoped ContDiff

namespace PositivityTheory.Rg.Rs.InducedTensorMap

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem F.hasDerivAt_line {a : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : Lie E a → Y}
    (hf : ContDiffAt ℝ ∞ f (oneL E a)) (X : Lie E a) :
    HasDerivAt (fun t : ℝ => f (oneL E a + t • X)) (fderiv ℝ f (oneL E a) X) 0 := by
  have hl : HasDerivAt (fun t : ℝ => oneL E a + t • X) X 0 :=
    (((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (oneL E a)).congr_deriv (one_smul _ _)
  have hd : HasFDerivAt f (fderiv ℝ f (oneL E a)) (oneL E a + (0 : ℝ) • X) := by
    rw [zero_smul, add_zero]
    exact (hf.differentiableAt (by simp)).hasFDerivAt
  exact hd.comp_hasDerivAt (0 : ℝ) hl

theorem lieD_of_expansion {H : GA E (r + s) → ℂ} (hH : H ∈ Sm E (r + s)) {n : ℕ} (K : Fin n → GA E r × GA E s → ℂ)
    (C : Fin n → Lie E (r + s) → ℂ) (b₁ : Lie E (r + s) → GL (Fin r) (Cinf E))
    (b₂ : Lie E (r + s) → GL (Fin s) (Cinf E)) (hC : ∀ j, ContDiffAt ℝ ∞ (C j) (oneL E (r + s)))
    (h₁ : b₁ (oneL E (r + s)) = 1) (h₂ : b₂ (oneL E (r + s)) = 1) (m : GA E r × GA E s)
    (he : chart H (lev (Ad E) r s m) =ᶠ[nhds (oneL E (r + s))]
      fun y => ∑ j, C j y * K j (m.1 * infGL E r (b₁ y), m.2 * infGL E s (b₂ y)))
    (X : Lie E (r + s)) (D : Fin n → ℂ)
    (hD : ∀ j, HasDerivAt (fun t : ℝ => K j (m.1 * infGL E r (b₁ (oneL E (r + s) + t • X)),
      m.2 * infGL E s (b₂ (oneL E (r + s) + t • X)))) (D j) 0) :
    lieD X H (lev (Ad E) r s m) = ∑ j, (fderiv ℝ (C j) (oneL E (r + s)) X * K j m + C j (oneL E (r + s)) * D j) := by
  have l0 : oneL E (r + s) + (0 : ℝ) • X = oneL E (r + s) := by rw [zero_smul, add_zero]
  have hl : HasDerivAt (fun t : ℝ => oneL E (r + s) + t • X) X 0 :=
    (((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (oneL E (r + s))).congr_deriv (one_smul _ _)
  have a1 := F.hasDerivAt_line (contDiffAt_chart hH (lev (Ad E) r s m) isUnit_one) X
  have a2 := HasDerivAt.fun_sum (u := Finset.univ) fun j _ => (F.hasDerivAt_line (hC j) X).mul (hD j)
  have ht : Filter.Tendsto (fun t : ℝ => oneL E (r + s) + t • X) (nhds 0) (nhds (oneL E (r + s))) := by
    have := hl.continuousAt.tendsto
    rwa [l0] at this
  have a3 := a2.congr_of_eventuallyEq (ht.eventually he)
  refine (a1.unique a3).trans (Finset.sum_congr rfl fun j _ => ?_)
  simp only [l0, h₁, h₂, map_one, mul_one]

theorem res_lie {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : Sm E (r + s)} (hF : F ∈ indSub U₁ U₂)
    (hK : F ∈ finVec (cptRep E (r + s))) (X : Lie E (r + s)) :
    res 1 (lieD X (ind f₁ f₂ F.1)) = tensOp f₁ f₂ (res 1 (lie E (r + s) X F).1) := by
  obtain ⟨n, G, C, b₁, b₂, hG, hC, hb₁, hb₂, h₁, h₂, e⟩ := exists_expansion hF hK
  have g₁ : (fun t : ℝ => b₁ (oneL E (r + s) + t • X)) 0 = 1 := by simp only [zero_smul, add_zero, h₁]
  have g₂ : (fun t : ℝ => b₂ (oneL E (r + s) + t • X)) 0 = 1 := by simp only [zero_smul, add_zero, h₂]
  choose G' hd₁ hd₂ using fun j => tensOp_deriv H.hf₁ H.hf₂ (fun t : ℝ => b₁ (oneL E (r + s) + t • X))
    (fun t : ℝ => b₂ (oneL E (r + s) + t • X)) _ _ g₁ g₂ (InducedTensorMap.F.hasDerivAt_line hb₁ X) (InducedTensorMap.F.hasDerivAt_line hb₂ X) (hG j)
  have hid : ∀ j, tensOp LinearMap.id LinearMap.id (G j) = G j := fun j => tensOp_id (hG j)
  have eF : ∀ m : GA E r × GA E s, chart F.1 (lev (Ad E) r s m) =ᶠ[nhds (oneL E (r + s))]
      fun y => ∑ j, C j y * G j (m.1 * infGL E r (b₁ y), m.2 * infGL E s (b₂ y)) := by
    intro m
    have := e (good_id H.hU₁ H.hU₂) m
    rw [ind_id H.hU₁ H.hU₂ hF] at this
    simpa only [hid] using this
  have eq1 : res 1 (lie E (r + s) X F).1 =
      ∑ j, (fderiv ℝ (C j) (oneL E (r + s)) X • G j + C j (oneL E (r + s)) • G' j) := by
    funext m
    rw [res_apply, mul_one, lie_apply,
      lieD_of_expansion F.2 G C b₁ b₂ hC h₁ h₂ m (eF m) X (fun j => G' j m) (fun j => hd₁ j m)]
    simp [Finset.sum_apply]
  funext m

  rw [res_apply, mul_one, eq1, map_sum,
  lieD_of_expansion (ind_mem_Sm H hF hK) (fun j => tensOp f₁ f₂ (G j)) C b₁ b₂ hC h₁ h₂ m (e H m) X
    (fun j => tensOp f₁ f₂ (G' j) m) (fun j => hd₂ j m)]
  simp [Finset.sum_apply]

theorem ind_lie {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : Sm E (r + s)} (hF : F ∈ indSub U₁ U₂)
    (hK : F ∈ finVec (cptRep E (r + s))) (X : Lie E (r + s)) (hX : lie E (r + s) X F ∈ indSub U₁ U₂) :
    ind f₁ f₂ (lie E (r + s) X F).1 = lieD X (ind f₁ f₂ F.1) := by
  let Gs : Sm E (r + s) := ⟨ind f₁ f₂ F.1, ind_mem_Sm H hF hK⟩
  have hleft : ∀ (u : BlockIx (r + s) r → Ad E) x,
      lieD X (ind f₁ f₂ F.1) (unip u * x) = lieD X (ind f₁ f₂ F.1) x := by
    intro u x
    have e : chart (ind f₁ f₂ F.1) (unip u * x) = chart (ind f₁ f₂ F.1) x := by
      funext y
      unfold chart
      split_ifs with hy
      · rw [mul_assoc, ind_left H hF]
      · rfl
    simp only [lieD, e]
  refine ext_res (ind_left H hX) hleft fun k g => ?_
  obtain ⟨X', hX'⟩ : ∃ X', rt E (r + s) (cf (r + s) k g) * lie E (r + s) X =
      lie E (r + s) X' * rt E (r + s) (cf (r + s) k g) := by
    refine ⟨toL ((Unitary.toUnits k).val * Matrix.of X * ((Unitary.toUnits k)⁻¹).val), ?_⟩
    rw [cf, map_mul, mul_assoc, ← lie_rt_fin, ← mul_assoc, ← mul_assoc]
    exact congrArg (· * _) (GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits k) (Matrix.of X))
  have ec : ∀ ψ : Sm E (r + s), res (cf (r + s) k g) (lie E (r + s) X ψ).1 =
      res 1 (lie E (r + s) X' (rt E (r + s) (cf (r + s) k g) ψ)).1 := fun ψ => funext fun m => by
    have := congrArg (fun f : Module.End ℂ (Sm E (r + s)) => (f ψ).1 (lev (Ad E) r s m * 1)) hX'
    simp only [Module.End.mul_apply, rt_apply, mul_one] at this
    rw [res_apply, res_apply, mul_one]
    exact this
  have hF' : rt E (r + s) (cf (r + s) k g) F ∈ indSub U₁ U₂ := isInd_rt hF k g
  have hK' := finVec_rt hK k g
  have hr : (rt E (r + s) (cf (r + s) k g) Gs).1 = ind f₁ f₂ (rt E (r + s) (cf (r + s) k g) F).1 :=
    funext fun x => (ind_rt H hF k g x).symm
  have h1 : res (cf (r + s) k g) (lieD X (ind f₁ f₂ F.1)) = res (cf (r + s) k g) (lie E (r + s) X Gs).1 := rfl
  have h2 : (lie E (r + s) X' (rt E (r + s) (cf (r + s) k g) Gs)).1 =
      lieD X' (ind f₁ f₂ (rt E (r + s) (cf (r + s) k g) F).1) := by
    rw [← hr]
    rfl
  rw [ind_levi H hX k g, h1, ec Gs, ec F, h2, res_lie H hF' hK' X']

end PositivityTheory.Rg.Rs.InducedTensorMap

end
end

section

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace PositivityTheory.Rg.Rs.SliceClasses

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def E_L (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N r : ℕ) (t : ℝ) :
    (GA E N → ℂ) →ₗ[ℂ] (GA E N → ℂ) :=
  LinearMap.funLeft ℂ ℂ fun g => aT E N r t * g

theorem E_L_apply {N r : ℕ} (t : ℝ) (f : GA E N → ℂ) (g : GA E N) : E_L E N r t f g = f (aT E N r t * g) := rfl

theorem constant_term_zero_eq {N r : ℕ} (f : GA E N → ℂ) : E_L E N r 0 f = f := by
  funext g
  rw [E_L_apply, aT_zero, one_mul]

theorem E_LL {N r : ℕ} (s t : ℝ) (f : GA E N → ℂ) : E_L E N r s (E_L E N r t f) = E_L E N r (t + s) f := by
  funext g
  rw [E_L_apply, E_L_apply, E_L_apply, aT_add, mul_assoc]

variable {r s : ℕ}

theorem E_key_left {r₁ : ℕ} (hr₁ : r₁ < r) (φ : Sm E (r + s)) (hφ : IsAutForm φ) (τs : Finset ℝ) (a : ℝ → ℂ)
    (F : GA E (r + s) → ℂ) (hF : ∀ g, F g = ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g))
    (ψ : GA E r → ℂ) (m₂ : GA E s) (h : GA E (r + s)) (hψF : ∀ m₁, ψ m₁ = F (lev (Ad E) r s (m₁, m₂) * h)) :
    An.ctn r₁ ψ = E_B (fun b : {x : PPos (r + s) {r₁, r} // ¬ IsTop r₁ x} → Ad E =>
        (parGL (joinPos (r := r₁) 0 b) : GA E (r + s)))
      (fun t (m : GA E r) => aT E (r + s) r t * (lev (Ad E) r s (m, m₂) * h))
      ((E_vol E r r₁)⁻¹ * ((E_vol E (r + s) r)⁻¹ * E_vol E (r + s) r₁)) τs a (An.ctn r₁ φ.1) := by
  have hφc : Continuous φ.1 := GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E _ φ hφ.level
  have hφl := GlobalTheory.CompanionTheory.LeftInv.isLeftInvariant_of_isAutForm E _ φ hφ
  have hcr : Continuous (An.ctn r φ.1) := E_cont_ctn r hφc hφ.left
  funext m₁
  set y := lev (Ad E) r s (m₁, m₂) * h with hy
  have hpos : ∀ x : PPos (r + s) {r₁, r}, ¬ IsTop r x → ((x.1.1 : ℕ) < r ↔ (x.1.2 : ℕ) < r) := fun x hx => by
    have := E_pos_top hr₁ x hx
    omega
  have e2 : ∀ A : UPos r r₁ → Ad E, ψ (unipGL A * m₁) = ∑ t ∈ τs, a t *
      An.ctn r φ.1 (parGL (joinPos (r := r) 0 fun q => A ((eL r s r₁ hr₁).symm q)) * (aT E (r + s) r t * y)) := by
    intro A
    rw [hψF, hF]
    refine Finset.sum_congr rfl fun t _ => ?_
    have e : lev (Ad E) r s (unipGL A * m₁, m₂) = lev (Ad E) r s (unipGL A, 1) * lev (Ad E) r s (m₁, m₂) := by
      rw [← map_mul, Prod.mk_mul_mk, one_mul]
    rw [e, lev_unipGL_left r s r₁ hr₁, mul_assoc, ← mul_assoc (aT E (r + s) r t), aT_comm_parGL _ _ _ _ hpos,
      mul_assoc]
  have e3 : ∀ z, ∫ b, An.ctn r φ.1 (parGL (joinPos (r := r) 0 b) * z)
      ∂(Measure.pi fun _ : {x : PPos (r + s) {r₁, r} // ¬ IsTop r x} => boxMeasure E) =
      (E_vol E (r + s) r)⁻¹ * (E_vol E (r + s) r₁ * ∫ b, An.ctn r₁ φ.1 (parGL (joinPos (r := r₁) 0 b) * z)
        ∂(Measure.pi fun _ : {x : PPos (r + s) {r₁, r} // ¬ IsTop r₁ x} => boxMeasure E)) := by
    intro z
    simp only [E_ctn_eq r]
    rw [integral_const_mul, ← constantTermPar_eq_top hr₁ hφc, constantTermPar_eq_bot hr₁ hφc hφl]
    congr 1
    rw [← integral_const_mul]
    congr 1
    funext b
    exact E_ct_eq r₁ _ _
  have hint : ∀ t ∈ τs, Integrable (fun A : UPos r r₁ → Ad E => a t * An.ctn r φ.1
      (parGL (joinPos (r := r) 0 fun q => A ((eL r s r₁ hr₁).symm q)) * (aT E (r + s) r t * y)))
      (Measure.pi fun _ => boxMeasure E) := by
    intro t _
    refine (integrable_box ?_).const_mul _
    exact hcr.comp ((((E_cont_join (E := E) (n := r + s) (S := {r₁, r}) r).comp
      (continuous_pi fun q => continuous_apply _))).mul continuous_const)
  rw [E_ctn_eq, constantTerm_eq_integral]
  simp only [e2]
  rw [integral_finsetSum _ hint]
  simp only [integral_const_mul, E_B]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← integral_box_reindex (eL r s r₁ hr₁)
    (fun b => An.ctn r φ.1 (parGL (joinPos (r := r) 0 b) * (aT E (r + s) r t * y))), e3]
  ring

theorem E_hB_left {r₁ : ℕ} (hr₁ : r₁ < r) (m₂ : GA E s) (h : GA E (r + s)) (κ : ℂ) (τs : Finset ℝ) (a : ℝ → ℂ)
    (t : ℝ) (f : GA E (r + s) → ℂ) :
    E_B (fun b : {x : PPos (r + s) {r₁, r} // ¬ IsTop r₁ x} → Ad E => (parGL (joinPos (r := r₁) 0 b) : GA E (r + s)))
      (fun t (m : GA E r) => aT E (r + s) r t * (lev (Ad E) r s (m, m₂) * h)) κ τs a (E_L E (r + s) r₁ t f) =
    E_L E r r₁ t (E_B (fun b : {x : PPos (r + s) {r₁, r} // ¬ IsTop r₁ x} → Ad E =>
        (parGL (joinPos (r := r₁) 0 b) : GA E (r + s)))
      (fun t (m : GA E r) => aT E (r + s) r t * (lev (Ad E) r s (m, m₂) * h)) κ τs a f) := by
  have hpos : ∀ x : PPos (r + s) {r₁, r}, ¬ IsTop r₁ x → ((x.1.1 : ℕ) < r₁ ↔ (x.1.2 : ℕ) < r₁) := fun x hx => by
    have := E_pos_bot hr₁ x hx
    omega
  funext m₁
  rw [E_L_apply]
  unfold E_B
  refine congrArg (κ * ·) (Finset.sum_congr rfl fun u _ => congrArg (a u * ·)
    (integral_congr_ae (.of_forall fun b => ?_)))
  change f (aT E (r + s) r₁ t * _) = f _
  refine congrArg f ?_
  rw [← mul_assoc, aT_comm_parGL _ _ _ _ hpos, mul_assoc, ← mul_assoc (aT E (r + s) r₁ t), aT_comm, mul_assoc,
    ← mul_assoc (aT E (r + s) r₁ t), ← lev_aT_left r s r₁ hr₁.le, ← map_mul, Prod.mk_mul_mk, one_mul]

theorem E_trans_right {r₂ : ℕ} (hr₂ : 0 < r₂) (φ : Sm E (r + s)) (hφ : IsAutForm φ) (w : GA E (r + s)) :
    ∫ b, An.ctn r φ.1 (parGL (joinPos (r := r) 0 b) * w)
      ∂(Measure.pi fun _ : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop r x} => boxMeasure E) =
    (E_vol E (r + s) r)⁻¹ * (E_vol E (r + s) (r + r₂) * ∫ b, An.ctn (r + r₂) φ.1
      (parGL (joinPos (r := r + r₂) 0 b) * w)
        ∂(Measure.pi fun _ : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} => boxMeasure E)) := by
  have hφc : Continuous φ.1 := GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E _ φ hφ.level
  have hφl := GlobalTheory.CompanionTheory.LeftInv.isLeftInvariant_of_isAutForm E _ φ hφ
  have hpq : r < r + r₂ := by omega
  simp only [E_ctn_eq r]
  rw [integral_const_mul, ← constantTermPar_eq_bot hpq hφc hφl, constantTermPar_eq_top hpq hφc]
  congr 1
  rw [← integral_const_mul]
  congr 1
  funext b
  exact E_ct_eq (r + r₂) _ _

theorem E_int_right {r₂ : ℕ} (hr₂ : 0 < r₂) (φ : Sm E (r + s)) (hφ : IsAutForm φ) (τs : Finset ℝ) (a : ℝ → ℂ)
    (F : GA E (r + s) → ℂ) (hF : ∀ g, F g = ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g)) (z : GA E (r + s)) :
    ∫ b, F (parGL (joinPos (r := r) 0 b) * z)
      ∂(Measure.pi fun _ : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop r x} => boxMeasure E) =
    ∑ t ∈ τs, a t * ((E_vol E (r + s) r)⁻¹ * (E_vol E (r + s) (r + r₂) * ∫ b, An.ctn (r + r₂) φ.1
      (parGL (joinPos (r := r + r₂) 0 b) * (aT E (r + s) r t * z))
        ∂(Measure.pi fun _ : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} => boxMeasure E))) := by
  have hφc : Continuous φ.1 := GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E _ φ hφ.level
  have hcr : Continuous (An.ctn r φ.1) := E_cont_ctn r hφc hφ.left
  have hpq : r < r + r₂ := by omega
  have hpos : ∀ x : PPos (r + s) {r, r + r₂}, ¬ IsTop r x → ((x.1.1 : ℕ) < r ↔ (x.1.2 : ℕ) < r) := fun x hx => by
    have := E_pos_bot hpq x hx
    omega
  have e1 : ∀ b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop r x} → Ad E, F (parGL (joinPos (r := r) 0 b) * z) =
      ∑ t ∈ τs, a t * An.ctn r φ.1 (parGL (joinPos (r := r) 0 b) * (aT E (r + s) r t * z)) := by
    intro b
    rw [hF]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← mul_assoc, aT_comm_parGL _ _ _ _ hpos, mul_assoc]
  have hint : ∀ t ∈ τs, Integrable (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop r x} → Ad E =>
      a t * An.ctn r φ.1 (parGL (joinPos (r := r) 0 b) * (aT E (r + s) r t * z))) (Measure.pi fun _ => boxMeasure E) :=
    fun t _ => (integrable_box (hcr.comp
      ((E_cont_join (E := E) (n := r + s) (S := {r, r + r₂}) r).mul continuous_const))).const_mul _
  simp only [e1]
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [integral_const_mul, E_trans_right hr₂ φ hφ]

theorem E_G_shift {r₂ : ℕ} (hr₂ : 0 < r₂) (τs : Finset ℝ) (a : ℝ → ℂ) (u : ℝ) (f : GA E (r + s) → ℂ)
    (z : GA E (r + s)) :
    E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
        (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
      (fun t (z : GA E (r + s)) => aT E (r + s) r t * z) 1 τs a (E_L E (r + s) (r + r₂) u f) z =
    E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
        (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
      (fun t (z : GA E (r + s)) => aT E (r + s) r t * z) 1 τs a f (aT E (r + s) (r + r₂) u * z) := by
  have hpq : r < r + r₂ := by omega
  have hpos : ∀ x : PPos (r + s) {r, r + r₂}, ¬ IsTop (r + r₂) x →
      ((x.1.1 : ℕ) < r + r₂ ↔ (x.1.2 : ℕ) < r + r₂) := fun x hx => by
    have := E_pos_top hpq x hx
    omega
  unfold E_B
  refine congrArg (1 * ·) (Finset.sum_congr rfl fun t _ => congrArg (a t * ·)
    (integral_congr_ae (.of_forall fun b => ?_)))
  change f (aT E (r + s) (r + r₂) u * _) = f _
  refine congrArg f ?_
  rw [← mul_assoc, aT_comm_parGL _ _ _ _ hpos, mul_assoc, ← mul_assoc (aT E (r + s) (r + r₂) u), aT_comm, mul_assoc]

theorem E_aT_right {r₂ : ℕ} (hr₂s : r₂ ≤ s) (t : ℝ) (m₁ : GA E r) (m₂ : GA E s) (h : GA E (r + s)) :
    aT E (r + s) (r + r₂) t * (lev (Ad E) r s (m₁, m₂) * h) =
      aT E (r + s) r t * (lev (Ad E) r s (m₁, aT E s r₂ t * m₂) * h) := by
  have e1 : aT E (r + s) (r + r₂) t = lev (Ad E) r s (1, aT E s r₂ t) * aT E (r + s) r t := by
    rw [lev_aT_right r s r₂ hr₂s, mul_assoc, ← aT_add, neg_add_cancel, aT_zero, mul_one]
  have e2 : lev (Ad E) r s (m₁, aT E s r₂ t * m₂) = lev (Ad E) r s (1, aT E s r₂ t) * lev (Ad E) r s (m₁, m₂) := by
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  rw [e1, e2, (aT_comm_lev r s t _).symm]
  simp only [mul_assoc]

end PositivityTheory.Rg.Rs.SliceClasses

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.SmGL GlobalTheory.CuspRep
open scoped TensorProduct

namespace PositivityTheory.Rg.Rs.SatakeVectors.Core

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem heckeVec_apply {N : ℕ} (w : HeightOneSpectrum (𝓞 E)) {F : Sm E N}
    {f : GL (Fin N) (w.adicCompletion E) → ℂ} (hf : f ∈ Hecke ℂ (KGL w (n := N))) (y : GA E N) :
    (heckeVec ((finRep E N).comp (locGL E N w)) (KGL w (n := N)) f F).1 y =
      heckeVec (rightReg ℂ _ ℂ) (KGL w (n := N)) f (fun g => F.1 (y * finGL E N (locGL E N w g))) 1 := by
  have hK := Final.GLintComm E w N
  rw [heckeVec, heckeVec]
  have e1 := ((LinearMap.proj (R := ℂ) (φ := fun _ : GA E N => ℂ) y).comp (Sm E N).subtype).toAddMonoidHom.map_finsum
    (finite_heckeVec hK hf ((finRep E N).comp (locGL E N w)) F)
  have e2 := (LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin N) (w.adicCompletion E) => ℂ)
    (1 : GL (Fin N) (w.adicCompletion E))).toAddMonoidHom.map_finsum
    (finite_heckeVec hK hf (rightReg ℂ _ ℂ) (fun g => F.1 (y * finGL E N (locGL E N w g))))
  refine e1.trans (Eq.trans (finsum_congr fun c => ?_) e2.symm)
  show f c.out • F.1 (y * finGL E N (locGL E N w c.out)) = f c.out • F.1 (y * finGL E N (locGL E N w (1 * c.out)))
  rw [one_mul]

def evAt {m : ℕ} (U : Submodule ℂ (Sm E m)) (x : GA E m) : U →ₗ[ℂ] ℂ :=
  LinearMap.proj x ∘ₗ (Sm E m).subtype ∘ₗ U.subtype

theorem exists_tensor {c : ℕ} {n : Fin c → ℕ} (U : ∀ i, Submodule ℂ (Sm E (n i)))
    {Φ : (∀ i, GA E (n i)) → ℂ} (hΦ : Φ ∈ GlobalTheory.BCWords.tensorSp U) :
    ∃ v : ⨂[ℂ] i, U i, ∀ m, Φ m = evT (fun i => evAt (U i) (m i)) v := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, rfl⟩ := hx
    exact ⟨PiTensorProduct.tprod ℂ φ, fun m => by rw [evT_tprod]; rfl⟩
  | zero => exact ⟨0, fun m => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨v, hv⟩ := hx
    obtain ⟨v', hv'⟩ := hy
    exact ⟨v + v', fun m => by rw [Pi.add_apply, hv, hv', map_add (f := _)]⟩
  | smul a x _ hx =>
    obtain ⟨v, hv⟩ := hx
    exact ⟨a • v, fun m => by rw [Pi.smul_apply, hv, map_smul, smul_eq_mul]⟩

end PositivityTheory.Rg.Rs.SatakeVectors.Core

end
end
