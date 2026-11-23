module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle057
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle055
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle056
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle058
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle065
public import Formalism.ConjugateSelfDual.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle074
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.GLift

theorem exists_emb_of_last {F : Type} [Field F] (r : ℕ) (m : GL (Fin (r + 1)) F)
    (hc : (m : Matrix _ _ F) *ᵥ GlobalTheory.JR.Step.eL r F = GlobalTheory.JR.Step.eL r F)
    (hr : GlobalTheory.JR.Step.eL r F ᵥ* (m : Matrix _ _ F) = GlobalTheory.JR.Step.eL r F) :
    ∃ s : GL (Fin r) F, m = GlobalTheory.JR.Step.emb r F s := by
  classical
  set t : Matrix (Fin r) (Fin r) F := (m : Matrix _ _ F).submatrix Fin.castSucc Fin.castSucc with ht
  have hcol : ∀ i, (m : Matrix _ _ F) i (Fin.last r) = (Pi.single (Fin.last r) (1 : F) : Fin (r + 1) → F) i := by
    intro i
    have := congrFun hc i
    simpa [GlobalTheory.JR.Step.eL, Matrix.mulVec_single_one] using this
  have hrow : ∀ j, (m : Matrix _ _ F) (Fin.last r) j = (Pi.single (Fin.last r) (1 : F) : Fin (r + 1) → F) j := by
    intro j
    have := congrFun hr j
    simpa [GlobalTheory.JR.Step.eL, Matrix.single_one_vecMul] using this
  have hm : (m : Matrix _ _ F) = GlobalTheory.JR.Step.embHom r F t := by
    ext i j
    induction i using Fin.lastCases with
    | last =>
      rw [hrow j]
      induction j using Fin.lastCases with
      | last => simp [GlobalTheory.JR.Step.embHom]
      | cast j => simp [GlobalTheory.JR.Step.embHom, Fin.castSucc_ne_last]
    | cast i =>
      induction j using Fin.lastCases with
      | last => rw [hcol]; simp [GlobalTheory.JR.Step.embHom, Fin.castSucc_ne_last]
      | cast j => simp [GlobalTheory.JR.Step.embHom, ht]
  have hdet : (m : Matrix (Fin (r + 1)) (Fin (r + 1)) F).det = t.det := by
    rw [hm]
    simp [GlobalTheory.JR.Step.embHom, Matrix.det_fromBlocks_zero₂₁]
  have hu : IsUnit t.det := by
    rw [← hdet]
    exact (Matrix.isUnit_iff_isUnit_det (m : Matrix (Fin (r + 1)) (Fin (r + 1)) F)).mp (Units.isUnit m)
  refine ⟨Matrix.nonsingInvUnit t hu, ?_⟩
  ext : 1
  rw [hm]
  rfl

end GlobalTheory.JR.GLift

namespace GlobalTheory.JR.GLift

theorem support_lift : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (Z : Gl r F) (μ l : F), ‖μ‖ = 1 →
    ∀ g : GL (Fin (r + 1)) F, unitG (r + 1) F (act g (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 →
      ∃ k ∈ glO (r + 1) F, ∃ s : GL (Fin r) F, g = k * GlobalTheory.JR.Step.emb r F s := by
  intro F E _ _ _ _ _ r Z μ l hμ g hg
  classical
  obtain ⟨-, hb, hc, -⟩ := Set.mem_of_indicator_ne_zero hg
  simp only [act, GlobalTheory.JR.Step.lift] at hb hc
  set e : Fin (r + 1) → F := GlobalTheory.JR.Step.eL r F with he
  have hv : ∀ i, ‖((g : Matrix (Fin (r + 1)) (Fin (r + 1)) F) *ᵥ e) i‖ ≤ 1 := by
    intro i
    have := hb i
    rwa [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, norm_mul, hμ, one_mul] at this
  have hw : ∀ i, ‖(e ᵥ* ((g⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F)) i‖ ≤ 1 := hc
  have hgg : ((g⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) * (g : Matrix (Fin (r + 1)) (Fin (r + 1)) F) = 1 :=
    Units.inv_mul g
  have hee : e ⬝ᵥ e = 1 := by simp [he, GlobalTheory.JR.Step.eL]
  have hwv : (e ᵥ* ((g⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F)) ⬝ᵥ ((g : Matrix (Fin (r + 1)) (Fin (r + 1)) F) *ᵥ e) = 1 := by
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec, hee]
  obtain ⟨k, hk, hkv, hkw⟩ := GlobalTheory.LatL.glO_transitive_pairs F E r _ _ hv hw hwv
  have hkv' : (k : Matrix (Fin (r + 1)) (Fin (r + 1)) F) *ᵥ e = (g : Matrix (Fin (r + 1)) (Fin (r + 1)) F) *ᵥ e := hkv
  have hkw' : (e ᵥ* ((g⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F)) ᵥ* (k : Matrix (Fin (r + 1)) (Fin (r + 1)) F) = e := hkw
  have hkk : ((k⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) * (k : Matrix (Fin (r + 1)) (Fin (r + 1)) F) = 1 :=
    Units.inv_mul k
  have hkk' : (k : Matrix (Fin (r + 1)) (Fin (r + 1)) F) * ((k⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) = 1 :=
    Units.mul_inv k
  have hek : e ᵥ* ((k⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) = e ᵥ* ((g⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) := by
    conv_lhs => rw [← hkw']
    rw [Matrix.vecMul_vecMul, hkk', Matrix.vecMul_one]
  obtain ⟨s, hs⟩ := exists_emb_of_last r (k⁻¹ * g) (by
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← hkv', Matrix.mulVec_mulVec, hkk, Matrix.one_mulVec])
    (by rw [Units.val_mul, ← Matrix.vecMul_vecMul, hek, Matrix.vecMul_vecMul, hgg, Matrix.vecMul_one])
  exact ⟨k, hk, s, by rw [← hs, mul_inv_cancel_left]⟩

end GlobalTheory.JR.GLift
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Step.InvMap

variable {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k') {r : ℕ}

theorem mom_glMap (Y : Gl r k) (i : ℕ) : mom (glMap φ Y) i = φ (mom Y i) := by
  have hp : (Y.1.map φ) ^ i = (Y.1 ^ i).map φ := by
    have := map_pow φ.mapMatrix Y.1 i
    simpa only [RingHom.mapMatrix_apply] using this.symm

  simp only [mom, glMap, hp, dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul]

theorem inv_glMap (Y : Gl r k) : GlobalTheory.JR.inv (glMap φ Y) = (GlobalTheory.JR.inv Y).map φ := by
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · funext i
    simp only [GlobalTheory.JR.inv, Inv.map, glMap, Matrix.charpoly_map, Polynomial.coeff_map]
  · funext i
    exact mom_glMap φ Y i

theorem sec_map (a : Inv r k) : sec (a.map φ) = glMap φ (sec a) := by
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · ext i j
    simp only [sec, companion, glMap, Inv.map, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  · funext i
    simp only [sec, glMap]
    split_ifs <;> simp

theorem Delta_map (a : Inv r k) : Delta (a.map φ) = φ (Delta a) := by
  rw [Delta, Delta, RingHom.map_det]
  congr 1
  ext i j
  simp only [hankel, sec_map, mom_glMap, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]

open Matrix MeasureTheory Filter Topology in
variable {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k') {r : ℕ} in
private theorem mom_glMap_eq_map_mom (ψ : k →+* k') (Y : _root_.GlobalTheory.JR.Gl r k) (n : ℕ) :
    _root_.GlobalTheory.JR.mom (_root_.GlobalTheory.JR.Step.glMap ψ Y) n = ψ (_root_.GlobalTheory.JR.mom Y n) := by
  unfold _root_.GlobalTheory.JR.mom _root_.GlobalTheory.JR.Step.glMap
  rw [RingHom.map_dotProduct]
  congr 1
  funext i
  rw [Function.comp_apply, RingHom.map_mulVec, Matrix.map_pow]
  rfl

open Matrix MeasureTheory Filter Topology in
variable {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k') {r : ℕ} in
private theorem sec_map_eq_glMap_sec (ψ : k →+* k') (a : _root_.GlobalTheory.JR.Inv r k) :
    _root_.GlobalTheory.JR.sec (a.map ψ) = _root_.GlobalTheory.JR.Step.glMap ψ (_root_.GlobalTheory.JR.sec a) := by
  unfold _root_.GlobalTheory.JR.sec _root_.GlobalTheory.JR.Inv.map _root_.GlobalTheory.JR.Step.glMap
  simp only [_root_.GlobalTheory.JR.ImgSec.companion_map, Prod.mk.injEq, true_and, and_true]
  funext i
  split_ifs <;> simp


open Matrix MeasureTheory Filter Topology in
variable {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k') {r : ℕ} in
theorem _root_.GlobalTheory.JR.Step.InvMap.inv_and_Delta_map : ∀ (k k' : Type) [CommRing k] [CommRing k'] (φ : k →+* k') (r : ℕ),
    (∀ Y : _root_.GlobalTheory.JR.Gl r k, _root_.GlobalTheory.JR.inv (_root_.GlobalTheory.JR.Step.glMap φ Y) = (_root_.GlobalTheory.JR.inv Y).map φ) ∧
      (∀ a : _root_.GlobalTheory.JR.Inv r k, _root_.GlobalTheory.JR.Delta (a.map φ) = φ (_root_.GlobalTheory.JR.Delta a)) := by
  intro k k' _ _ φ r
  refine ⟨fun Y => ?_, fun a => ?_⟩
  · unfold _root_.GlobalTheory.JR.inv _root_.GlobalTheory.JR.Inv.map
    simp only [mom_glMap_eq_map_mom]
    refine Prod.ext ?_ rfl
    funext i
    simp [_root_.GlobalTheory.JR.Step.glMap, Matrix.charpoly_map]
  · unfold _root_.GlobalTheory.JR.Delta
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [_root_.GlobalTheory.JR.hankel, sec_map_eq_glMap_sec, mom_glMap_eq_map_mom]

end GlobalTheory.JR.Step.InvMap
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.WeilMix

theorem psi_isLocallyConstant {F : Type} [NontriviallyNormedField F] (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    IsLocallyConstant (fun x => ψ x) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy
  have h1 : ψ (y - x) = 1 := hψ.1 _ (by rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hy).le)
  calc ψ y = ψ (x + (y - x)) := by rw [add_sub_cancel]
    _ = ψ x := by rw [AddChar.map_add_eq_mul, h1, mul_one]

theorem isOpen_setOf_eq_of_isLocallyConstant {Y : Type} [TopologicalSpace Y] {g h : Y → ℂ}
    (hg : IsLocallyConstant g) (hh : IsLocallyConstant h) : IsOpen {p | g p = h p} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  filter_upwards [(IsLocallyConstant.iff_eventually_eq g).1 hg p,
    (IsLocallyConstant.iff_eventually_eq h).1 hh p] with q h1 h2
  show g q = h q
  rw [h1, h2]; exact hp

theorem isTest_partialFourier {X F : Type} [TopologicalSpace X] [T2Space X] [NontriviallyNormedField F]
    [ProperSpace F] {r : ℕ} [MeasurableSpace (Fin r → F)] (μ : Measure (Fin r → F))
    (hμ : ∀ (g : (Fin r → F) → ℂ) (w : Fin r → F), ∫ b, g (b + w) ∂μ = ∫ b, g b ∂μ)
    (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (f : X × (Fin r → F) → ℂ) (hf : IsTest f) :
    IsTest (fun p : X × (Fin r → F) => ∫ b, f (p.1, b) * ψ (b ⬝ᵥ p.2) ∂μ) := by
  obtain ⟨hfl, hfc⟩ := hf
  have hK : IsCompact (tsupport f) := hfc
  have hψl := psi_isLocallyConstant ψ hψ

  have hn1 : IsOpen {q : (X × (Fin r → F)) × (Fin r → F) | f (q.1.1, q.1.2 + q.2) = f q.1} :=
    isOpen_setOf_eq_of_isLocallyConstant (hfl.comp_continuous (by fun_prop))
      (hfl.comp_continuous continuous_fst)
  obtain ⟨u1, v1, -, hv1, hKu, h0v, huv⟩ :=
    generalized_tube_lemma hK (isCompact_singleton (x := (0 : Fin r → F))) hn1 (by
      rintro ⟨p, w⟩ ⟨-, hw⟩
      simp only [Set.mem_singleton_iff] at hw
      subst hw
      simp)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hv1 0 (h0v rfl)
  have inv1 : ∀ x b (w : Fin r → F), ‖w‖ < δ → f (x, b + w) = f (x, b) := by
    intro x b w hw
    have hwv : w ∈ v1 := hball (by simpa using hw)
    by_cases hxb : (x, b) ∈ tsupport f
    · exact huv (⟨hKu hxb, hwv⟩ : ((x, b), w) ∈ u1 ×ˢ v1)
    · by_cases hxbw : (x, b + w) ∈ tsupport f
      · have hmw : -w ∈ v1 := hball (by simpa using hw)
        have := huv (⟨hKu hxbw, hmw⟩ : ((x, b + w), -w) ∈ u1 ×ˢ v1)
        simp only [Set.mem_setOf_eq, add_neg_cancel_right] at this
        exact this.symm
      · rw [image_eq_zero_of_notMem_tsupport hxb, image_eq_zero_of_notMem_tsupport hxbw]
  have hzero : ∀ x b, b ∉ Prod.snd '' tsupport f → f (x, b) = 0 := fun x b hb =>
    image_eq_zero_of_notMem_tsupport (fun h => hb ⟨_, h, rfl⟩)
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨x0, u0⟩
    have hdot : Continuous fun q : (X × (Fin r → F)) × (Fin r → F) => q.2 ⬝ᵥ q.1.2 := by
      unfold dotProduct; fun_prop
    have hdot0 : Continuous fun q : (X × (Fin r → F)) × (Fin r → F) => q.2 ⬝ᵥ u0 := by
      unfold dotProduct; fun_prop
    have hn2 : IsOpen {q : (X × (Fin r → F)) × (Fin r → F) |
        f (q.1.1, q.2) * ψ (q.2 ⬝ᵥ q.1.2) = f (x0, q.2) * ψ (q.2 ⬝ᵥ u0)} :=
      isOpen_setOf_eq_of_isLocallyConstant
        ((hfl.comp_continuous (by fun_prop)).comp₂ (hψl.comp_continuous hdot) (· * ·))
        ((hfl.comp_continuous (by fun_prop)).comp₂ (hψl.comp_continuous hdot0) (· * ·))
    obtain ⟨u2, v2, hu2, -, hxu, hKv, hu2n⟩ :=
      generalized_tube_lemma (isCompact_singleton (x := (x0, u0))) (hK.image continuous_snd) hn2 (by
        rintro ⟨p, b⟩ ⟨hp, -⟩
        simp only [Set.mem_singleton_iff] at hp
        subst hp
        simp)
    filter_upwards [hu2.mem_nhds (hxu rfl)] with p hp
    refine integral_congr_ae (Eventually.of_forall fun b => ?_)
    by_cases hb : b ∈ Prod.snd '' tsupport f
    · exact hu2n (⟨hp, hKv hb⟩ : (p, b) ∈ u2 ×ˢ v2)
    · simp only [hzero _ _ hb, zero_mul]
  · obtain ⟨a, ha, -⟩ := hψ.2
    refine HasCompactSupport.intro
      ((hK.image continuous_fst).prod (isCompact_closedBall (0 : Fin r → F) (‖a‖ / δ))) ?_
    rintro ⟨x, u⟩ hxu
    rw [Set.mem_prod, not_and_or] at hxu
    rcases hxu with hx | hu
    · have h0 : ∀ b, f (x, b) = 0 := fun b =>
        image_eq_zero_of_notMem_tsupport (fun h => hx ⟨_, h, rfl⟩)
      simp [h0]
    · rw [mem_closedBall_zero_iff, not_le] at hu
      obtain ⟨i, hi⟩ : ∃ i, ‖a‖ / δ < ‖u i‖ := by
        by_contra h
        push_neg at h
        exact (not_le.2 hu) ((pi_norm_le_iff_of_nonneg (by positivity)).2 h)
      have hui : u i ≠ 0 := by
        intro h
        rw [h, norm_zero] at hi
        exact (not_lt.2 (by positivity)) hi
      classical
      have hw : ‖(Pi.single i (a / u i) : Fin r → F)‖ < δ := by
        rw [Pi.norm_single, norm_div, div_lt_iff₀ (norm_pos_iff.2 hui)]
        rw [div_lt_iff₀ hδ] at hi
        linarith
      have hwu : (Pi.single i (a / u i) : Fin r → F) ⬝ᵥ u = a := by
        rw [single_dotProduct]; field_simp
      have key := hμ (fun b => f (x, b) * ψ (b ⬝ᵥ u)) (Pi.single i (a / u i))
      have hsh : ∀ b, f (x, b + Pi.single i (a / u i)) * ψ ((b + Pi.single i (a / u i)) ⬝ᵥ u) =
          (f (x, b) * ψ (b ⬝ᵥ u)) * ψ a := by
        intro b
        rw [inv1 x b _ hw, add_dotProduct, AddChar.map_add_eq_mul, hwu]
        ring
      simp only [hsh, integral_mul_const] at key
      show ∫ b, f (x, b) * ψ (b ⬝ᵥ u) ∂μ = 0
      by_contra hI
      exact ha (mul_left_cancel₀ hI (key.trans (mul_one _).symm))

end GlobalTheory.JR.WeilMix

namespace GlobalTheory.JR.WeilMix

theorem ptrB_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f : Gl r F → ℂ,
    IsTest f → IsTest (WeilMix.ptrB M ψ f) := by
  intro F E _ _ _ _ hU r M ψ hψ f hf
  letI := M.mF
  haveI := M.bF
  haveI := M.haarF
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  let eH : Gl r F ≃ₜ (Matrix (Fin r) (Fin r) F × (Fin r → F) × F) × (Fin r → F) :=
    { toFun := fun Y => ((Y.1, Y.2.2.1, Y.2.2.2), Y.2.1)
      invFun := fun p => (p.1.1, p.2, p.1.2.1, p.1.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hμ : ∀ (g : (Fin r → F) → ℂ) (w : Fin r → F),
      ∫ b, g (b + w) ∂(Measure.pi fun _ : Fin r => M.μF) = ∫ b, g b ∂(Measure.pi fun _ : Fin r => M.μF) :=
    fun g w => integral_add_right_eq_self g w
  have hg : IsTest (f ∘ eH.symm) := ⟨hf.1.comp_continuous eH.symm.continuous, hf.2.comp_homeomorph eH.symm⟩
  have h1 := isTest_partialFourier (Measure.pi fun _ : Fin r => M.μF) hμ ψ hψ (f ∘ eH.symm) hg
  exact ⟨h1.1.comp_continuous eH.continuous, h1.2.comp_homeomorph eH⟩

end GlobalTheory.JR.WeilMix
end

section

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem exists_gen_of_valuation_eq (K : UQ) (x : K.E)
    (hx : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x = WithZero.exp (-1)) :
    ∃ a : K.O, algebraMap K.O K.E a = x ∧ IsLocalRing.maximalIdeal K.O = Ideal.span {a} := by
  set v := IsDiscreteValuationRing.maximalIdeal K.O with hv
  obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one (A := K.O) (K := K.E)
    (x := x) (by rw [hx, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num)
  refine ⟨a, rfl, ?_⟩
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap] at hx
  have h1 : a ∈ v.asIdeal := by
    rw [← IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem, hx, ← WithZero.exp_zero,
      WithZero.exp_lt_exp]; norm_num
  have h2 : a ∉ v.asIdeal ^ 2 := by
    rw [← IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem, hx, WithZero.exp_le_exp]; norm_num
  change a ∈ IsLocalRing.maximalIdeal K.O at h1
  change a ∉ IsLocalRing.maximalIdeal K.O ^ 2 at h2
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  have hm := hϖ.maximalIdeal_eq
  rw [hm] at h1 h2 ⊢
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 h1
  have hb : IsUnit b := by
    by_contra hb
    apply h2
    have : b ∈ IsLocalRing.maximalIdeal K.O := (IsLocalRing.mem_maximalIdeal b).2 hb
    rw [hm] at this
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_two]
    exact mul_dvd_mul (Ideal.mem_span_singleton.1 this) dvd_rfl
  rw [Ideal.span_singleton_mul_left_unit hb]

theorem exists_unif (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (h : IsUnrExt K K' d φ) :
    ∃ π : K.O, ∃ π' : K'.O, algebraMap K'.O K'.E π' = φ (algebraMap K.O K.E π) ∧
      IsLocalRing.maximalIdeal K.O = Ideal.span {π} ∧ IsLocalRing.maximalIdeal K'.O = Ideal.span {π'} := by
  obtain ⟨x, hx⟩ := (IsDiscreteValuationRing.maximalIdeal K.O).valuation_exists_uniformizer K.E
  have hx' : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x = WithZero.exp (-1) := hx
  obtain ⟨π, hπ, hm⟩ := exists_gen_of_valuation_eq K x hx'
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx'
    exact WithZero.exp_ne_zero hx'.symm
  have hv := h.2.2.1 x
  unfold val at hv
  rw [hx', WithZero.log_exp] at hv
  have hy0 : (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E (φ x) ≠ 0 := by
    simpa using (map_ne_zero φ).2 hx0
  have hy : (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E (φ x) = WithZero.exp (-1) := by
    rw [← WithZero.exp_log hy0]; congr 1; omega
  obtain ⟨π', hπ', hm'⟩ := exists_gen_of_valuation_eq K' (φ x) hy
  exact ⟨π, π', by rw [hπ', hπ], hm, hm'⟩

end GlobalTheory.UnitLemma.Unr
end
end

section

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem valuation_le_one_of_val_nonneg (K : UQ) (e : K.E) (he : e ≠ 0) (h : 0 ≤ val K.O e) :
    (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E e ≤ 1 := by
  unfold val at h
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E e ≠ 0 := by simpa using he
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

theorem val_nonneg_of_int (K : UQ) (x : K.O) : 0 ≤ val K.O (algebraMap K.O K.E x) := by
  by_cases hx : algebraMap K.O K.E x = 0
  · rw [hx]; unfold val; simp
  unfold val
  have h1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (IsDiscreteValuationRing.maximalIdeal K.O) (K := K.E) x
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E x) ≠ 0 := by simpa using hx
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  omega

theorem map_int (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hU : IsUnrExt K K' d φ) (x : K.O) :
    ∃ y : K'.O, algebraMap K'.O K'.E y = φ (algebraMap K.O K.E x) := by
  by_cases hx : algebraMap K.O K.E x = 0
  · exact ⟨0, by rw [hx, map_zero, map_zero]⟩
  have hφ : φ (algebraMap K.O K.E x) ≠ 0 := by simpa using hx
  have hv : 0 ≤ val K'.O (φ (algebraMap K.O K.E x)) := by
    rw [hU.2.2.1]; exact val_nonneg_of_int K x
  exact IsDiscreteValuationRing.exists_lift_of_le_one (valuation_le_one_of_val_nonneg K' _ hφ hv)

end GlobalTheory.UnitLemma.Unr
end
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.isFrob_fixes_root_of_one_mod_place : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (M : ℕ) (ζ : F),
    IsPrimitiveRoot ζ M → ∀ v : HeightOneSpectrum (𝓞 F), ((M : ℕ) : 𝓞 F) ∉ v.asIdeal →
    ∀ A : ValuationSubring Ω, Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ σ : Formalism.ConjugateSelfDual.G F Ω, Formalism.ConjugateSelfDual.IsFrob A (Formalism.ConjugateSelfDual.normV v) σ →
    ∀ x : 𝓞 F, x - 1 ∈ v.asIdeal → ∀ w : Ω, w ^ M = algebraMap F Ω (x : F) → σ w = w := by
  first | exact @GlobalTheory.frob_fixes_root_of_one_mod | exact GlobalTheory.frob_fixes_root_of_one_mod | (intros; apply GlobalTheory.frob_fixes_root_of_one_mod <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Pj

theorem _root_.GlobalTheory.T.exists_complex_embedding_fractionField_cdvr : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (T : CDVR), T.FinRes → ∀ io : K →+* T.Fr, ∃ ι : T.Fr →+* ℂ, ι.comp io = σ := by
  first | exact @GlobalTheory.ComplexEmbedding.exists_embedding_fractionField | exact GlobalTheory.ComplexEmbedding.exists_embedding_fractionField | (intros; apply GlobalTheory.ComplexEmbedding.exists_embedding_fractionField <;> assumption)
end
