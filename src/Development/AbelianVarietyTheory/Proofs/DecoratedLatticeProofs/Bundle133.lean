module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.RatCoord



theorem coords_rat {D : D7} {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (c' : skewA D ρ) (b' : Mx D ρ V₀.rank)
    (u : GL (Fin ρ) (AE D)) (hQ : d.nC c' * (d.nB b' * d.levi u) ∈ GQ V) :
    c'.1 ∈ ratMx D ρ ρ ∧ b' ∈ ratMx D ρ V₀.rank ∧ u.1 ∈ ratMx D ρ ρ ∧ (u⁻¹).1 ∈ ratMx D ρ ρ := by
  generalize hg : d.nC c' * (d.nB b' * d.levi u) = g at hQ
  have hM : mt V g ∈ ratMx D V.rank V.rank := (mem_GQ_iff V g).1 hQ
  have hM' : mt V g⁻¹ ∈ ratMx D V.rank V.rank := (mem_GQ_iff V g⁻¹).1 (inv_mem hQ)
  have hX : mt V g ⬝ d.jX = d.jX ⬝ u.1 := by
    rw [← hg]; simp only [mt_mul, Matrix.mul_assoc, d.levi_jX, cancel₂ (d.nB_jX _), cancel₂ (d.nC_jX _)]
  have hX' : mt V g⁻¹ ⬝ d.jX = d.jX ⬝ (u⁻¹).1 := by
    calc mt V g⁻¹ ⬝ d.jX = mt V g⁻¹ ⬝ (d.jX ⬝ u.1 ⬝ (u⁻¹).1) := by
          rw [Matrix.mul_assoc d.jX, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = d.jX ⬝ (u⁻¹).1 := by rw [← hX, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
  have h0 : mt V g ⬝ d.j0 = d.j0 + d.jX ⬝ b' := by
    rw [← hg]; simp only [mt_mul, Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic, d.nB_j0, Matrix.mul_add, cancel₂ (d.nC_jX _), d.nC_j0]
  have hY : d.pX ⬝ (mt V g ⬝ d.jY) = (c'.1 - half D • (b' ⬝ plus V₀ b')) ⬝ adj (u⁻¹).1 := by
    rw [← hg, mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.levi_jY, cancel₂ (d.nB_jY _)]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, cancel₂ (d.nC_jY _),
      cancel₂ (d.nC_j0 _), cancel₂ (d.nC_jX _), cancel₂ d.pX_jY, cancel₂ d.pX_jX, cancel₂ d.pX_j0,
      Matrix.one_mul, Matrix.zero_mul, zero_add, sub_zero]
  have hu1 : u.1 ∈ ratMx D ρ ρ := by
    have e : d.pX ⬝ (mt V g ⬝ d.jX) = u.1 := by rw [hX, cancel₂ d.pX_jX, Matrix.one_mul]
    rw [← e]; exact ratMx_mul (rat_mem _) (ratMx_mul hM (rat_mem _))
  have hu2 : (u⁻¹).1 ∈ ratMx D ρ ρ := by
    have e : d.pX ⬝ (mt V g⁻¹ ⬝ d.jX) = (u⁻¹).1 := by rw [hX', cancel₂ d.pX_jX, Matrix.one_mul]
    rw [← e]; exact ratMx_mul (rat_mem _) (ratMx_mul hM' (rat_mem _))
  have hb : b' ∈ ratMx D ρ V₀.rank := by
    have e : d.pX ⬝ (mt V g ⬝ d.j0) = b' := by
      rw [h0, Matrix.mul_add, d.pX_j0, zero_add, cancel₂ d.pX_jX, Matrix.one_mul]
    rw [← e]; exact ratMx_mul (rat_mem _) (ratMx_mul hM (rat_mem _))
  have hc : c'.1 = d.pX ⬝ (mt V g ⬝ d.jY) ⬝ adj u.1 + half D • (b' ⬝ plus V₀ b') := by
    have e : adj (u⁻¹).1 ⬝ adj u.1 = 1 := by rw [← adj_mul, Units.mul_inv, adj_one]
    rw [hY, Matrix.mul_assoc, e, Matrix.mul_one, sub_add_cancel]
  refine ⟨?_, hb, hu1, hu2⟩
  rw [hc]
  exact add_mem (ratMx_mul (ratMx_mul (rat_mem _) (ratMx_mul hM (rat_mem _))) (ratMx_adj hu1))
    (ratMx_smul _ (ratMx_mul hb (ratMx_mul (rat_mem _) (ratMx_adj hb))))

theorem rat_coords_of_mem_flagN : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (γ : GA D V), γ ∈ GQ V → γ ∈ flagN d → ∃ (c : skewA D ρ) (b : Mx D ρ V₀.rank) (u : UX D ρ), γ = d.nC c * (d.nB b * d.levi u.1) ∧ c.1 ∈ ratMx D ρ ρ ∧ b ∈ ratMx D ρ V₀.rank ∧ u ∈ UXQ D ρ := by
  intro D V V₀ ρ d γ hQ hN
  obtain ⟨T, b, hT, hX, h0⟩ := exists_blocks d hN
  obtain ⟨u, hu, hu1⟩ := GlobalTheory.MixPer.Decomp.exists_unit hT
  let g := d.nB b * d.levi u
  let n := g⁻¹ * γ
  have fixed {k : ℕ} {X : Mx D V.rank k} (h : mt V γ ⬝ X = mt V g ⬝ X) : mt V n ⬝ X = X := by
    rw [show n = g⁻¹ * γ from rfl, mt_mul, Matrix.mul_assoc, h, ← Matrix.mul_assoc, mt_inv_mul,
      Matrix.one_mul]
  have fixX : mt V n ⬝ d.jX = d.jX := fixed (by
    rw [hX, show g = d.nB b * d.levi u from rfl, mt_mul, Matrix.mul_assoc, d.levi_jX,
      cancel₂ (d.nB_jX b), hu1, Matrix.mul_add, Matrix.mul_one])
  have fix0 : mt V n ⬝ d.j0 = d.j0 := fixed (by
    rw [h0, show g = d.nB b * d.levi u from rfl, mt_mul, Matrix.mul_assoc,
      d.wittDecomp_levi_inclAnisotropic, d.nB_j0])
  have gram {k l : ℕ} (X : Mx D V.rank k) (Y : Mx D V.rank l) :
      adj (mt V n ⬝ X) ⬝ (gA V ⬝ (mt V n ⬝ Y)) = adj X ⬝ (gA V ⬝ Y) := by
    rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA V) _ Y, ← Matrix.mul_assoc (adj (mt V n)),
      GlobalTheory.MixModel.mt_unitary]
  let c := d.pX ⬝ (mt V n ⬝ d.jY)
  have imageY : mt V n ⬝ d.jY = d.jY + d.jX ⬝ c := by
    have projY : d.pY ⬝ (mt V n ⬝ d.jY) = 1 := by
      rw [d.pY_eq, Matrix.mul_assoc, ← fixX, gram, d.gram_XY]
    have proj0 : d.p0 ⬝ (mt V n ⬝ d.jY) = 0 := by
      rw [d.p0_eq, Matrix.mul_assoc, Matrix.mul_assoc, ← fix0, gram, d.gram_0Y, Matrix.mul_zero]
    conv_lhs => rw [← Matrix.one_mul (mt V n ⬝ d.jY), ← d.sum_eq_one]
    simp only [Matrix.add_mul, Matrix.mul_assoc, proj0, projY, Matrix.mul_zero, Matrix.mul_one, add_zero]
    exact add_comm _ _
  have skew : c ∈ skewA D ρ := by
    have h := gram d.jY d.jY
    rw [imageY, d.gram_YY] at h
    simp only [adj_add, adj_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, d.gram_YY, d.gram_XY,
      cancel₃ d.gram_XX, cancel₃ d.gram_YX, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul,
      Matrix.mul_one, add_zero, zero_add] at h
    exact eq_neg_of_add_eq_zero_left h
  let c₀ : skewA D ρ := ⟨c, skew⟩
  have hn : n = d.nC c₀ := d.ga_ext (fixX.trans (d.nC_jX c₀).symm) (fix0.trans (d.nC_j0 c₀).symm)
    (imageY.trans (d.nC_jY c₀).symm)
  have hγ : γ = d.nC (skewConj u.1 c₀) * (d.nB b * d.levi u) := by
    calc
      γ = g * n := (mul_inv_cancel_left g γ).symm
      _ = _ := by rw [hn, show g = d.nB b * d.levi u from rfl, mul_assoc, d.levi_mul_nC,
        ← mul_assoc, ← d.nC_mul_nB, mul_assoc]
  rw [hγ] at hQ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := coords_rat d _ _ u hQ
  exact ⟨skewConj u.1 c₀, b, ⟨u, hu⟩, rfl, h1, h2, h3, h4⟩

end GlobalTheory.RatCoord

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf



namespace GlobalTheory.LeftUniQmp

theorem qmp_left_uni : ∀ (D : D7) (ρ n : ℕ) (μ : Measure (Mx D ρ n)), μ.IsAddHaarMeasure → ∀ u : UX D ρ, Measure.QuasiMeasurePreserving (fun b : Mx D ρ n => u.1.1 ⬝ b) μ μ := by
  intro D ρ n μ hμ u
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D ρ n
  haveI : BorelSpace (Mx D ρ n) := ⟨rfl⟩
  have hc : Continuous (fun b : Mx D ρ n => u.1.1 ⬝ b) := continuous_const.matrix_mul continuous_id
  have hc' : Continuous (fun b : Mx D ρ n => (u.1⁻¹).1 ⬝ b) := continuous_const.matrix_mul continuous_id
  let T : Mx D ρ n ≃+ Mx D ρ n :=
    { toFun := fun b => u.1.1 ⬝ b
      invFun := fun b => (u.1⁻¹).1 ⬝ b
      left_inv := fun b => by
        show (u.1⁻¹).1 ⬝ (u.1.1 ⬝ b) = b
        rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      right_inv := fun b => by
        show u.1.1 ⬝ ((u.1⁻¹).1 ⬝ b) = b
        rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      map_add' := fun a b => Matrix.mul_add _ _ _ }
  haveI : (μ.map T).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ T hc hc'
  refine ⟨hc.measurable.aemeasurable, ?_⟩
  have e := Measure.isAddLeftInvariant_eq_smul (μ.map T) μ
  show μ.map T ≪ μ
  rw [e]
  exact Measure.smul_absolutelyContinuous

end GlobalTheory.LeftUniQmp
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.SkewConjQmp

theorem skewConj_matMul {D : D7} {ρ : ℕ} (a b : Mx D ρ ρ) (c : skewA D ρ) :
    skewConj (a ⬝ b) c = skewConj a (skewConj b c) := by
  apply Subtype.ext
  simp only [skewConj, adj_mul, Matrix.mul_assoc]

theorem skewConj_matOne {D : D7} {ρ : ℕ} (c : skewA D ρ) : skewConj (1 : Mx D ρ ρ) c = c := by
  apply Subtype.ext
  simp only [skewConj, adj_one, Matrix.one_mul, Matrix.mul_one]

theorem skewConj_addArg {D : D7} {ρ : ℕ} (a : Mx D ρ ρ) (c d : skewA D ρ) :
    skewConj a (c + d) = skewConj a c + skewConj a d := by
  apply Subtype.ext
  simp only [skewConj, AddSubgroup.coe_add, Matrix.mul_add, Matrix.add_mul]

theorem continuous_skewConj_arg {D : D7} {ρ : ℕ} (a : Mx D ρ ρ) : Continuous (skewConj a : skewA D ρ → skewA D ρ) := by
  have h1 : Continuous fun c : skewA D ρ => (a ⬝ c.1 : Mx D ρ ρ) := continuous_const.matrix_mul continuous_subtype_val
  have h2 : Continuous fun c : skewA D ρ => (a ⬝ c.1 ⬝ adj a : Mx D ρ ρ) := h1.matrix_mul continuous_const
  exact Continuous.subtype_mk h2 _

noncomputable def skewConjEquiv {D : D7} {ρ : ℕ} (g : GL (Fin ρ) (AE D)) : skewA D ρ ≃+ skewA D ρ where
  toFun := skewConj g.val
  invFun := skewConj (g⁻¹).val
  left_inv c := by
    rw [← skewConj_matMul]
    have : (g⁻¹).val ⬝ g.val = 1 := Units.inv_mul g
    rw [this, skewConj_matOne]
  right_inv c := by
    rw [← skewConj_matMul]
    have : g.val ⬝ (g⁻¹).val = 1 := Units.mul_inv g
    rw [this, skewConj_matOne]
  map_add' := skewConj_addArg _



theorem quasiMeasurePreserving_skewConj : ∀ (D : D7) (ρ : ℕ) (lC : Measure (skewA D ρ)), lC.IsAddHaarMeasure →
    ∀ u : UX D ρ, Measure.QuasiMeasurePreserving (skewConj u.1.1) lC lC := by
  intro D ρ lC hC u
  obtain ⟨a1, a2, a3, a4, -⟩ := lattice_Mx D ρ ρ
  have : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  have : BorelSpace (skewA D ρ) := Subtype.borelSpace _
  have hcl : IsClosed (skewA D ρ : Set (Mx D ρ ρ)) := isClosed_eq continuous_adj continuous_neg
  have : LocallyCompactSpace (skewA D ρ) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : IsTopologicalAddGroup (skewA D ρ) := inferInstance
  have : SecondCountableTopology (skewA D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
  have hc := continuous_skewConj_arg (u.1.1 : Mx D ρ ρ)
  have hH : (lC.map (skewConj u.1.1)).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map lC (skewConjEquiv u.1) hc
      (continuous_skewConj_arg (u.1⁻¹).val)
  refine ⟨hc.measurable.aemeasurable, ?_⟩
  exact Measure.absolutelyContinuous_isAddHaarMeasure _ _

end GlobalTheory.Unf.SkewConjQmp
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem fjKer_eq_om_apply : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (W W₀ V₀ A L : HSp D) (ρ : ℕ) (dW : HypDec W W₀ ρ) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om V₀ W₀), IsWeilDatumO ψ V₀ W₀ χ χ' om → ∀ Ξ, IsThetaFunO ψ V₀ W₀ Ξ → ∀ h₀ n h, fjKer ψ dW o ζ om Ξ h₀ n h = ψ (cenT dW L (yZero L ρ ζ) n) * om (o.emb (h₀, 1), h) Ξ ((o.resS W₀).symm (0, ptT dW L (yZero L ρ ζ) n)) := by
  intro D ψ W W₀ V₀ A L ρ dW o ζ χ χ' om hW Ξ hΞ h₀ n h
  have hp : (o.resS W₀).symm (0, ptT dW L (yZero L ρ ζ) n) = ptT dW V₀ (yZero V₀ ρ (vecB o ζ)) n := by
    rw [← ptT_yZero_vecB o dW ζ n, AddEquiv.symm_apply_apply]
  have hfix : actO V₀ W₀ (o.emb (h₀, 1)) 1 (ptT dW V₀ (yZero V₀ ρ (vecB o ζ)) n) =
      ptT dW V₀ (yZero V₀ ρ (vecB o ζ)) n := by
    apply (o.resS W₀).injective
    rw [o.resS_actO, ptT_yZero_vecB]
    simp only [actO_eq, inv_one, mt_one, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul]
  have hm : om (o.emb (h₀, 1), 1) (om (1, h) Ξ) = om (o.emb (h₀, 1), h) Ξ := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  rw [hp, fjKer, opA, jacT, map_smul, hW.om_heis _ _ _ _ (hW.om_pres _ _ hΞ), hfix, hm, cenT_yZero_vecB]
  simp only [Pi.smul_apply, smul_eq_mul, heisO, zero_add, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.Unf
end
