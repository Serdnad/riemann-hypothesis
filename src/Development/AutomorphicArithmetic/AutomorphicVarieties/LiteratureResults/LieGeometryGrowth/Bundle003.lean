module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle001
import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle003
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
import Mathlib.RingTheory.PiTensorProduct
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

@[expose] public section

section

open UpperTheory.V.Lit.Geo

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Bor

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem level_lie (X : Lie E a) (φ : Sm E a) (h : IsOpen {k | act (.fin k) φ = φ}) :
    IsOpen {k | act (.fin k) (lie E a X φ) = lie E a X φ} := by
  let S : Sm E a → Subgroup (GL (Fin a) (GlobalTheory.CuspRep.Af E)) := fun θ =>
    { carrier := {k | finRep E a k θ = θ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hle : S φ ≤ S (lie E a X φ) := fun k hk => by
    have e : lie E a X (finRep E a k φ) = finRep E a k (lie E a X φ) :=
      LinearMap.congr_fun (lie_rt_fin X k) φ
    have hk' : finRep E a k φ = φ := hk
    change finRep E a k (lie E a X φ) = lie E a X φ
    rw [← e, hk']
  exact Subgroup.isOpen_mono hle h

private theorem left_lie (X : Lie E a) (φ : Sm E a) (x : GA E a) (h : ∀ g, φ.1 (x * g) = φ.1 g) (g : GA E a) :
    (lie E a X φ).1 (x * g) = (lie E a X φ).1 g := by
  obtain ⟨c, c0, -, -, cder, -⟩ := UpperTheory.V.Lit.Bor.oneParam E a X
  have h1 := hasDerivAt_curve φ (x * g) c X c0 cder
  have h2 := hasDerivAt_curve φ g c X c0 cder
  simp only [mul_assoc, h] at h1
  exact h1.unique h2

theorem UpperTheory.V.Lit.Geo.Pf.invLie :
    UpperTheory.V.Lit.Geo.Pf.InvLie := by
  intro E _ _ _ a φ h
  exact ⟨⟨ContAut.continuous_of_isOpen_stab E a φ h.level, h.left, h.centre⟩, fun X =>
    ⟨fun γ => left_lie X φ _ (h.left γ), fun t => left_lie X φ _ (h.centre t), level_lie X φ h.level⟩⟩

end
end

section

open UpperTheory.V.Lit.Geo


open NumberField Formalism.L2.Host GroundTheory.Global in
private theorem norm_of_normOne {E : Type} [Field E] [NumberField E] (χ : HChar E) {y : IdeleGroup E}
    (hy : y ∈ IdeleGroup.normOneSubgroup E) : ‖((χ.1 y : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨D, hD, -, hxD⟩ := IdeleGroup.exists_isCompact_normOneSubgroup E
  have hc : Continuous fun z : IdeleGroup E => ((χ.1 z : ℂˣ) : ℂ) := Units.continuous_val.comp χ.2.1
  obtain ⟨M, hM⟩ := hD.exists_bound_of_continuousOn hc.continuousOn
  have hb : ∀ z ∈ IdeleGroup.normOneSubgroup E, ‖((χ.1 z : ℂˣ) : ℂ)‖ ≤ M := fun z hz => by
    obtain ⟨k, hk⟩ := hxD z hz
    have h := hM _ hk
    have h1 : χ.1 (IdeleGroup.diagonal E k) = 1 := χ.2.2 k
    have h2 : χ.1 (IdeleGroup.diagonal E k * z) = χ.1 z :=
      (map_mul χ.1 _ _).trans (by rw [h1, one_mul])
    rwa [h2] at h
  have hle : ∀ z ∈ IdeleGroup.normOneSubgroup E, ‖((χ.1 z : ℂˣ) : ℂ)‖ ≤ 1 := fun z hz => by
    by_contra h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M (not_le.1 h)
    have h3 := hb _ (pow_mem hz n)
    have h4 : χ.1 (z ^ n) = χ.1 z ^ n := map_pow χ.1 z n
    rw [h4, Units.val_pow_eq_pow_val, norm_pow] at h3
    exact (not_le.2 hn) h3
  have h5 := hle _ (inv_mem hy)
  have h6 : χ.1 y⁻¹ = (χ.1 y)⁻¹ := map_inv χ.1 y
  rw [h6, Units.val_inv_eq_inv_val, norm_inv, inv_le_one₀ (norm_pos_iff.2 (Units.ne_zero _))] at h5
  exact le_antisymm (hle _ hy) h5

theorem UpperTheory.V.Lit.Geo.Pf.chiOne :
    UpperTheory.V.Lit.Geo.Pf.ChiOne := by
  intro E _ _ _ a χ s _ g
  exact norm_of_normOne χ g.2
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo
open scoped TensorProduct

namespace UpperTheory.V.Lit.Geo.Pf

section
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (χ : Formalism.L2.Host.HChar E) {d : ℕ}
  (G : Matrix (Fin d) (Fin d) ℂ) (g : GA E a)

private theorem ev_eq (x : Sm E a ⊗[ℂ] (Fin d → ℂ)) : ev x g = fun j => (cmp j x).1 g :=
  funext fun j => (cmp_ev x j g).symm

private theorem ev_add' (x y : Sm E a ⊗[ℂ] (Fin d → ℂ)) : ev (x + y) g = ev x g + ev y g := by
  funext j
  simp [ev_eq]

private noncomputable def ptL (y : Sm E a ⊗[ℂ] (Fin d → ℂ)) : Sm E a ⊗[ℂ] (Fin d → ℂ) →+ ℂ :=
  AddMonoidHom.mk' (fun x => pt χ G x y g) fun x x' => by
    simp only [pt, ev_add', star_add, add_dotProduct, mul_add]

private noncomputable def ptR (x : Sm E a ⊗[ℂ] (Fin d → ℂ)) : Sm E a ⊗[ℂ] (Fin d → ℂ) →+ ℂ :=
  AddMonoidHom.mk' (fun y => pt χ G x y g) fun y y' => by
    simp only [pt, ev_add', mulVec_add, dotProduct_add, mul_add]

private theorem pt_sum_left {ι : Type} (s : Finset ι) (x : ι → Sm E a ⊗[ℂ] (Fin d → ℂ)) (y : Sm E a ⊗[ℂ] (Fin d → ℂ)) :
    pt χ G (∑ i ∈ s, x i) y g = ∑ i ∈ s, pt χ G (x i) y g := map_sum (ptL χ G g y) x s

private theorem pt_sum_right {ι : Type} (s : Finset ι) (x : Sm E a ⊗[ℂ] (Fin d → ℂ)) (y : ι → Sm E a ⊗[ℂ] (Fin d → ℂ)) :
    pt χ G x (∑ i ∈ s, y i) g = ∑ i ∈ s, pt χ G x (y i) g := map_sum (ptR χ G g x) y s

private theorem pt_zsmul_left (k : ℤ) (x y : Sm E a ⊗[ℂ] (Fin d → ℂ)) :
    pt χ G (k • x) y g = k • pt χ G x y g := map_zsmul (ptL χ G g y) k x

private theorem pt_zsmul_right (k : ℤ) (x y : Sm E a ⊗[ℂ] (Fin d → ℂ)) :
    pt χ G x (k • y) g = k • pt χ G x y g := map_zsmul (ptR χ G g x) k y

end

end UpperTheory.V.Lit.Geo.Pf

open UpperTheory.V.Lit.Geo.Pf in
theorem UpperTheory.V.Lit.Geo.Pf.ptD :
    UpperTheory.V.Lit.Geo.Pf.PtD := by
  intro E _ _ _ a Ξ χ G n e q L β η g
  refine ⟨?_, ?_⟩
  · have key : ∀ i : Fin (q + 1), ∑ I : Fin (q + 1) → Fin n,
        pt χ G (β fun k => e (I k)) ((-1 : ℤ) ^ (i : ℕ) • L (toL (e (I i)).1) (η (i.removeNth fun k => e (I k)))) g =
        ∑ J : Fin q → Fin n, ∑ j,
          pt χ G (β (Matrix.vecCons (e j) fun i => e (J i))) (L (toL (e j).1) (η fun i => e (J i))) g := fun i => by
      rw [← (Fin.insertNthEquiv (fun _ => Fin n) i).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun j _ => ?_
      have h1 : (fun k => e ((Fin.insertNthEquiv (fun _ => Fin n) i (j, J)) k)) =
          i.insertNth (α := fun _ => Herm E a) (e j) (fun k => e (J k)) := by
        funext k
        refine Fin.succAboveCases i ?_ (fun k => ?_) k <;> simp [Fin.insertNthEquiv]
      have h2 : (Fin.insertNthEquiv (fun _ => Fin n) i (j, J)) i = j := by simp [Fin.insertNthEquiv]
      rw [h1, h2, Fin.removeNth_insertNth, AlternatingMap.map_insertNth, pt_zsmul_left, pt_zsmul_right,
        smul_smul, ← mul_pow]
      simp
    have h0 : ptIp χ G e β (dCo L η) g = ∑ i : Fin (q + 1), ∑ I : Fin (q + 1) → Fin n,
        pt χ G (β fun k => e (I k)) ((-1 : ℤ) ^ (i : ℕ) • L (toL (e (I i)).1) (η (i.removeNth fun k => e (I k)))) g := by
      rw [Finset.sum_comm, ptIp_eq]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [dCo_apply, pt_sum_right]
    rw [h0, Finset.sum_congr rfl fun i _ => key i]
    simp
  · rw [ptIp_eq]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [del_apply, pt_sum_left]
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo
open scoped TensorProduct ComplexOrder

theorem UpperTheory.V.Lit.Geo.Pf.ptPos :
    UpperTheory.V.Lit.Geo.Pf.PtPos := by
  intro E _ _ _ a Ξ χ G hG n e he q α
  have hnn : ∀ v : Fin Ξ.d → ℂ, 0 ≤ star v ⬝ᵥ G *ᵥ v := fun v => hG.pos.posSemidef.dotProduct_mulVec_nonneg v
  refine ⟨fun g => ?_, fun h0 => ?_⟩
  · have h : 0 ≤ ptIp χ G e α α g :=
      mul_nonneg (Complex.zero_le_real.2 (by positivity)) (Finset.sum_nonneg fun I _ => hnn _)
    obtain ⟨h1, h2⟩ := Complex.nonneg_iff.1 h
    exact ⟨_, h1, Complex.ext rfl h2.symm⟩
  · have h2 : ∀ I : Fin q → Fin n, (α fun i => e (I i)) = 0 := fun I => by
      have hev : ∀ g, ev (α fun i => e (I i)) g = 0 := fun g => by
        have h := h0 g
        rw [ptIp, mul_eq_zero] at h
        rcases h with h | h
        · simp at h
        · have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun I _ => hnn _)).1 h I (Finset.mem_univ _)
          by_contra hne
          exact (hG.pos.dotProduct_mulVec_pos hne).ne' h1
      rw [← sum_cmp (α fun i => e (I i))]
      refine Finset.sum_eq_zero fun j _ => ?_
      have : cmp j (α fun i => e (I i)) = 0 := Subtype.ext (funext fun g => by
        rw [Pf.cmp_ev, hev]; rfl)
      rw [this, TensorProduct.zero_tmul]
    refine AlternatingMap.ext fun X => ?_
    have hX : X = fun i => ∑ j, trF (e j).1 (X i).1 • e j := funext fun i => he (X i)
    have h3 : α X = ∑ I : Fin q → Fin n, α fun i => trF (e (I i)).1 (X i).1 • e (I i) := by
      conv_lhs => rw [hX]
      exact α.toMultilinearMap.map_sum (fun i j => trF (e j).1 (X i).1 • e j)
    rw [h3, AlternatingMap.zero_apply]
    refine Finset.sum_eq_zero fun I _ => ?_
    rw [α.map_smul_univ (fun i => trF (e (I i)).1 (X i).1) (fun i => e (I i)), h2, smul_zero]
end

section

open UpperTheory.V.Lit.Geo
open NumberField MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC
open UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped GlobalTheory.CuspRep.CuspidalL2GL

theorem UpperTheory.V.Lit.Geo.Pf.zeroInt :
    UpperTheory.V.Lit.Geo.Pf.ZeroInt := by
  intro E _ _ _ a μ _ F hF hpos hI h0
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (latticeGL E a) F := CuspidalL2GL.leftInv_latticeGL hF.left hF.centre
  have hn : ∀ g, F g = ((‖F g‖ : ℝ) : ℂ) := fun g => by
    obtain ⟨t, ht, e⟩ := hpos g
    rw [e, Complex.norm_real, Real.norm_of_nonneg ht]
  have h1 : ∫ x : GlobalTheory.AutomorphicL2Unitary.Quot (latticeGL E a), ‖F x.out‖ ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ) = 0 := by
    have h2 : Pf.qint μ F =
        ((∫ x : GlobalTheory.AutomorphicL2Unitary.Quot (latticeGL E a), ‖F x.out‖ ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => hn _)
    rw [h0] at h2
    exact_mod_cast h2.symm
  have h3 := (integral_eq_zero_iff_of_nonneg (fun x => norm_nonneg _) (Integrable.norm hI)).1 h1
  have h4 : F =ᵐ[μ] fun _ => 0 := by
    filter_upwards [GlobalTheory.AutomorphicL2Unitary.ae_quotMeasure_iff.1 h3] with g hg
    have e : F (GlobalTheory.AutomorphicL2Unitary.mk (latticeGL E a) g).out = F g := hL.descend_mk g
    simpa [e] using hg
  exact fun g => congrFun ((Continuous.ae_eq_iff_eq μ hF.cont continuous_const).1 h4) g
end

section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Geo

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem chart_conj_mul (f h : GA E a → ℂ) (g : GA E a) :
    chart (fun x => starRingEnd ℂ (f x) * h x) g = fun y => Complex.conjCLE (chart f g y) * chart h g y := by
  funext y
  unfold chart
  split_ifs <;> simp

end

theorem UpperTheory.V.Lit.Geo.Pf.prodEx :
    UpperTheory.V.Lit.Geo.Pf.ProdEx := by
  intro E _ _ _ a φ ψ
  refine ⟨⟨fun x => starRingEnd ℂ (φ.1 x) * ψ.1 x, fun g => ?_⟩, fun _ => rfl, fun X g => ?_⟩
  · rw [chart_conj_mul]
    exact (Complex.conjCLE.contDiff.comp_contDiffOn (φ.2 g)).mul (ψ.2 g)
  · have hv : ∀ f : GA E a → ℂ, chart f g (oneL E a) = f g := fun f => by
      simpa using chart_val f g 1
    change fderiv ℝ (chart (fun x => starRingEnd ℂ (φ.1 x) * ψ.1 x) g) (oneL E a) X =
      starRingEnd ℂ (fderiv ℝ (chart φ.1 g) (oneL E a) X) * ψ.1 g +
        starRingEnd ℂ (φ.1 g) * fderiv ℝ (chart ψ.1 g) (oneL E a) X
    have h1 := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp (oneL E a)
      (differentiableAt_chart φ.2 g).hasFDerivAt).fun_mul (differentiableAt_chart ψ.2 g).hasFDerivAt
    rw [chart_conj_mul]
    refine (congrArg (fun L => L X) h1.fderiv).trans ?_
    simp [hv, mul_comm, add_comm]
end
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum
open scoped ContDiff TensorProduct

namespace UpperTheory.V.Lit.Geo

section Abs

variable {V' V F : Type} [NormedAddCommGroup V'] [NormedSpace ℝ V'] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def pb (H : V' → V) {q : ℕ} (w : V → V [⋀^Fin q]→L[ℝ] F) (p : V') : V' [⋀^Fin q]→L[ℝ] F :=
  (w (H p)).compContinuousLinearMap (fderiv ℝ H p)

theorem pb_apply (H : V' → V) {q : ℕ} (w : V → V [⋀^Fin q]→L[ℝ] F) (p : V') (v : Fin q → V') :
    pb H w p v = w (H p) fun i => fderiv ℝ H p (v i) := rfl

def flow (W : V → V) (t : ℝ) (p : V) : V := p + t • W p

def hk (W : V → V) (t : ℝ) {q : ℕ} (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F) (p : V) : V [⋀^Fin q]→L[ℝ] F :=
  ((w (flow W t p)).curryLeft (W p)).compContinuousLinearMap (fderiv ℝ (flow W t) p)

theorem hk_apply (W : V → V) (t : ℝ) {q : ℕ} (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F) (p : V) (v : Fin q → V) :
    hk W t w p v = w (flow W t p) (Matrix.vecCons (W p) fun i => fderiv ℝ (flow W t) p (v i)) := rfl

def hom (W : V → V) {q : ℕ} (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F) (p : V) : V [⋀^Fin q]→L[ℝ] F :=
  ∫ t in (0 : ℝ)..1, hk W t w p

def IsField (Y : Set V) (W : V → V) : Prop :=
  ContDiffOn ℝ ∞ W Y ∧ ∀ p ∈ Y, ∀ t ∈ Set.Icc (0 : ℝ) 1, flow W t p ∈ Y

end Abs

section Om

variable {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ} (G : Dr.Geo Γ V S d)

structure IsFlow (W : S → V → V) : Prop where
  field : ∀ s, IsField G.Y (W s)
  equiv : ∀ γ s, ∀ p ∈ G.Y, W (G.σ γ s) (G.ρ γ p) = G.ρ γ (W s p)
  homog : ∀ s (t : ℝ), 0 < t → ∀ p ∈ G.Y, W s (t • p) = t • W s p

theorem isFlow_zero : IsFlow G 0 :=
  ⟨fun _ => ⟨contDiffOn_const, fun p hp t _ => by simpa [flow] using hp⟩, fun _ _ _ _ => by simp, fun _ _ _ _ _ => by simp⟩


open Classical in
def toOm {q : ℕ} (z : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) : G.Om q :=
  if h : ∀ s, ContDiffOn ℝ ∞ (z s) G.Y then
    ⟨fun s => G.Y.indicator (z s), fun s =>
      ⟨(h s).congr fun _ hp => Set.indicator_of_mem hp _, fun _ hp => Set.indicator_of_notMem hp _⟩⟩
  else 0

theorem toOm_apply {q : ℕ} {z : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)} (h : ∀ s, ContDiffOn ℝ ∞ (z s) G.Y) (s : S) {p : V}
    (hp : p ∈ G.Y) : (toOm G z).1 s p = z s p := by
  rw [toOm, dite_eq_left h]
  exact Set.indicator_of_mem hp _

def pbOm (W : S → V → V) {q : ℕ} (w : G.Om q) : G.Om q := toOm G fun s => pb (flow (W s) 1) (w.1 s)

def homOm (W : S → V → V) {q : ℕ} (w : G.Om (q + 1)) : G.Om q := toOm G fun s => hom (W s) (w.1 s)

structure Good {q : ℕ} (w : G.Om q) : Prop where
  inv : ∀ γ, G.act q γ w = w
  basic : ∀ s, RadBasic G.Y (w.1 s)
  dbasic : ∀ s, RadBasic G.Y ((G.dOm q w).1 s)

end Om

section Ad

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

structure IsFld (U : Subgroup (GL (Fin a) (Af E))) (Y : GA E a → Herm E a) (C : ℝ) : Prop where
  sm : ∀ i j w, ∃ φ : Sm E a, (∀ g, φ.1 g = (Y g).1 i j w) ∧ BddDer φ
  left : ∀ γ t g, Y (ratGL E a γ * splitCentre E a t * g) = Y g
  cpt : ∀ (k : Kinf E a) g, adHerm k (Y (g * infGL E a (Unitary.toUnits k))) = Y g
  lev : ∀ u ∈ U, ∀ g, Y (g * finGL E a u) = Y g
  root : ∀ g (t : ℝ), |t| ≤ 1 → ∃ h : GL (Fin a) (Cinf E), h.val * star h.val = 1 + t • (Y g).1 ∧
    ‖toL h.val‖ ≤ C ∧ ‖toL (h⁻¹).val‖ ≤ C

theorem IsStep.fld {U : Subgroup (GL (Fin a) (Af E))} {f : GA E a → ℝ} {Y : GA E a → Herm E a} {C c f₀ : ℝ}
    (h : IsStep U f Y C c f₀) : IsFld U Y C := ⟨h.Y_sm, h.Y_left, h.Y_cpt, h.Y_lev, h.root⟩

theorem IsFld.neg {U : Subgroup (GL (Fin a) (Af E))} {Y : GA E a → Herm E a} {C : ℝ} (h : IsFld U Y C) :
    IsFld U (-Y) C := by
  refine { sm := ?_, left := ?_, cpt := ?_, lev := ?_, root := ?_ }
  · intro i j w
    obtain ⟨φ, h1, h2⟩ := h.sm i j w
    refine ⟨-φ, fun g => congrArg Neg.neg (h1 g), fun X l => ?_⟩
    obtain ⟨B, hB⟩ := h2 X l
    exact ⟨B, fun g => by rw [map_neg]; exact (norm_neg _).trans_le (hB g)⟩
  · exact fun γ t g => congrArg Neg.neg (h.left γ t g)
  · intro k g
    have e := congrArg Subtype.val (h.cpt k g)
    refine Subtype.ext ?_
    change k.1 * (-(Y (g * infGL E a (Unitary.toUnits k))).1) * star k.1 = -(Y g).1
    rw [mul_neg, neg_mul, ← e]
    rfl
  · exact fun u hu g => congrArg Neg.neg (h.lev u hu g)
  · intro g t ht
    obtain ⟨x, h1, h2⟩ := h.root g (-t) (by rwa [abs_neg])
    exact ⟨x, by rw [h1, neg_smul]; exact congrArg (1 + ·) (smul_neg t (Y g).1).symm, h2⟩

def FCorr (U : Subgroup (GL (Fin a) (Af E))) (Y : GA E a → Herm E a) (W : (GL (Fin a) (Af E) ⧸ U) → HV E a → HV E a) : Prop :=
  ∀ (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)),
    W (x : GL (Fin a) (Af E) ⧸ U) (sand g (hOne E a)) = sand g (hv (Y (infGL E a g * finGL E a x)))

def Bd {Ξ : AlgRep E a} {q : ℕ} (α : Co Ξ q) (g : GA E a) (M : ℝ) : Prop :=
  ∀ X : Fin q → Herm E a, ‖ev (α X) (retractOne g : KernelIndexFullLattice.G1 E a).1‖ ≤ M * ∏ i, ‖hv (X i)‖

theorem Bd.mono {Ξ : AlgRep E a} {q : ℕ} {α : Co Ξ q} {g : GA E a} {M M' : ℝ} (h : Bd α g M) (hM : M ≤ M') : Bd α g M' :=
  fun X => (h X).trans (mul_le_mul_of_nonneg_right hM (Finset.prod_nonneg fun _ _ => norm_nonneg _))

theorem Bd.sub {Ξ : AlgRep E a} {q : ℕ} {α β : Co Ξ q} {g : GA E a} {M M' : ℝ} (h : Bd α g M) (h' : Bd β g M') :
    Bd (α - β) g (M + M') := fun X => by
  rw [sub_apply, map_sub, Pi.sub_apply, add_mul]
  exact (norm_sub_le _ _).trans (add_le_add (h X) (h' X))

end Ad

end UpperTheory.V.Lit.Geo
end
end

section

open UpperTheory.V.Lit.Geo
open NumberField Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private def levSub {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) : Submodule ℂ (Sm E a) where
  carrier := {φ | IsLevelFn U Ξ φ}
  zero_mem' := ⟨fun _ _ => rfl, fun u _ => map_zero _, fun m _ => by simp⟩
  add_mem' := fun {φ ψ} h h' => ⟨fun γ g => congrArg₂ (· + ·) (h.1 γ g) (h'.1 γ g),
    fun u hu => by rw [map_add (f := _), h.2.1 u hu, h'.2.1 u hu],
    fun m hm => by rw [map_add (f := _), h.2.2 m hm, h'.2.2 m hm, smul_add]⟩
  smul_mem' := fun c φ h => ⟨fun γ g => congrArg (c • ·) (h.1 γ g),
    fun u hu => by rw [map_smul, h.2.1 u hu],
    fun m hm => by rw [map_smul, h.2.2 m hm, smul_comm]⟩

private theorem stab_open {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) {S : Set G} (hS : IsOpen S) (h1 : (1 : G) ∈ S) (h : ∀ g ∈ S, ρ g v = v) :
    IsOpen {g | ρ g v = v} := by
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' S, fun x hx => ?_, hS.preimage (by fun_prop), by simpa using h1⟩
  have e : x = g * (g⁻¹ * x) := by group
  have hg' : ρ g v = v := hg
  show ρ x v = v
  rw [e, map_mul, Module.End.mul_apply, h _ hx, hg']

theorem UpperTheory.V.Lit.Geo.Pf.levInv :
    UpperTheory.V.Lit.Geo.Pf.LevInv := by
  intro E _ _ _ a ha U hU Ξ r χ h1 hχ q α hα X j
  have hφ : IsLevelFn U Ξ (cmp j (α X)) :=
    mem_tens.1 (span_le_tens (N := levSub U Ξ) (fun φ h => h) (hα.val X)) j
  generalize cmp j (α X) = φ at hφ
  refine ⟨fun γ g => ?_, fun t g => ?_, ?_⟩
  · rw [mulChi_apply, mulChi_apply, map_mul, chiDet_ratGL, one_mul, hφ.1]
  · have hz : lie E a (oneL E a) (mulChi a χ φ) = (0 : ℂ) • mulChi a χ φ := by
      rw [hχ.2, hφ.2.2 _ h1, (ellFacts E a).1 ha, mul_one, ← add_smul, neg_add_cancel, zero_smul, map_zero, zero_smul]
    rw [aInv E a _ _ hz t g, zero_mul, Complex.exp_zero, one_mul]
  · change IsOpen {k | finRep E a k (mulChi a χ φ) = mulChi a χ φ}
    refine stab_open (finRep E a) _ (hU.inter (isOpen_ker_chiDet (a := a) χ)) ⟨U.one_mem, by simp⟩ ?_
    rintro k ⟨hk, h2⟩
    have h1' : rt E a (finGL E a k) φ = φ := hφ.2.1 k hk
    have h2' : chiDet a χ (finGL E a k) = 1 := h2
    change rt E a (finGL E a k) (mulChi a χ φ) = _
    rw [rt_mulChi, h1', h2']
    simp
end
