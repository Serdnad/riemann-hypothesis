module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.SplitP
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ParabolicLowerBlockZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.Bundle001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.VacCut
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.MatrixEqFrameConjugate
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.SchwartzOfConstantPolynomialOne
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
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.Bundle001

@[expose] public section

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Avac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open GlobalTheory.Doubling (absE)

omit [NumberField E] in
theorem incM_mul'' {a b c : Type} [Fintype b] (X : Matrix a b E) (Y : Matrix b c E) :
    incM F (X * Y) = incM F X * incM F Y := Matrix.map_mul

theorem isPar_of_frame (d : SD σ) (p : d.G) (h21 : (inFrame d.b p).toBlocks₂₁ = 0) :
    ∃ t : GL (Fin d.n) (AE F E), IsPar p t ∧ (Matrix.GeneralLinearGroup.det t : AE F E) = (inFrame d.b p).toBlocks₁₁.det := by
  obtain ⟨-, tb, htb⟩ := d.ok.frame
  set M := inFrame d.b p with hM
  let E1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := Matrix.fromRows 1 0
  let DC : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := diagCols (Fin d.n)
  have htb' : d.b.1.toCols₁ = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * tb.1 := htb
  have hcol : ∀ N : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E), N * E1 = N.toCols₁ := by
    intro N
    ext i j
    simp [E1, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]
  have h1 : incM F d.b.1 * E1 = incM F (d.b.1.toCols₁) := by
    rw [hcol]
    ext i j
    rfl
  have h2 : incM F ((diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * tb.1) = DC * incM F tb.1 := by
    rw [incM_mul'']
    congr 1
    ext i j
    cases i <;> simp [DC, diagCols, incM, Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all
  have hb : incM F d.b.1 * E1 = DC * incM F tb.1 := h1.trans ((congrArg (incM F) htb').trans h2)
  have hTb : incM F tb.1 * incM F (tb⁻¹).1 = 1 := by
    rw [← incM_mul'', Units.mul_inv]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hTb' : incM F (tb⁻¹).1 * incM F tb.1 = 1 := by
    rw [← incM_mul'', Units.inv_mul]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hdc : DC = incM F d.b.1 * E1 * incM F (tb⁻¹).1 := by
    rw [hb, Matrix.mul_assoc, hTb, Matrix.mul_one]
  have hME : M * E1 = E1 * M.toBlocks₁₁ := by
    rw [hcol]
    ext i j
    cases i with
    | inl i => simp [E1, Matrix.toCols₁, Matrix.toBlocks₁₁, Matrix.mul_apply, Matrix.one_apply]
    | inr i =>
      have := congrFun (congrFun h21 i) j
      simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply] at this
      simp [E1, Matrix.toCols₁, this, Matrix.mul_apply]

  have hBm : IsUnit (incM F d.b.1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, KWhit.incM_mul_inv d, Matrix.det_one]⟩)
  have hBi : IsUnit (incM F (d.b⁻¹).1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, KWhit.incM_inv_mul d, Matrix.det_one]⟩)
  have hug : IsUnit M := (hBi.mul (Units.isUnit p.1)).mul hBm
  have hgb : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    rw [← h21, Matrix.fromBlocks_toBlocks]
  have hdet : IsUnit (M.toBlocks₁₁.det * M.toBlocks₂₂.det) := by
    rw [← Matrix.det_fromBlocks_zero₂₁ M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₂, ← hgb]
    exact (Matrix.isUnit_iff_isUnit_det M).1 hug
  have hA : IsUnit M.toBlocks₁₁.det := isUnit_of_mul_isUnit_left hdet
  have hTbu : IsUnit (incM F tb.1).det :=
    isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, hTb, Matrix.det_one]⟩
  have hTbiu : IsUnit (incM F (tb⁻¹).1).det :=
    isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, hTb', Matrix.det_one]⟩
  have hu : IsUnit (incM F tb.1 * M.toBlocks₁₁ * incM F (tb⁻¹).1) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, Matrix.det_mul]
    exact (hTbu.mul hA).mul hTbiu
  refine ⟨hu.unit, ?_, ?_⟩
  · show mat2 p * DC = DC * (hu.unit : Matrix (Fin d.n) (Fin d.n) (AE F E))
    rw [IsUnit.unit_spec, KWhit.matrix_eq_frame_conjugate d p]
    change incM F d.b.1 * M * incM F (d.b⁻¹).1 * DC = DC * (incM F tb.1 * M.toBlocks₁₁ * incM F (tb⁻¹).1)
    rw [hdc]
    calc incM F d.b.1 * M * incM F (d.b⁻¹).1 * (incM F d.b.1 * E1 * incM F (tb⁻¹).1)
        = incM F d.b.1 * M * (incM F (d.b⁻¹).1 * incM F d.b.1) * E1 * incM F (tb⁻¹).1 := by
          simp only [Matrix.mul_assoc]
      _ = incM F d.b.1 * (M * E1) * incM F (tb⁻¹).1 := by
          rw [KWhit.incM_inv_mul d, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = incM F d.b.1 * E1 * (incM F (tb⁻¹).1 * incM F tb.1) * M.toBlocks₁₁ * incM F (tb⁻¹).1 := by
          rw [hME, hTb', Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  · rw [Matrix.GeneralLinearGroup.val_det_apply, IsUnit.unit_spec, Matrix.det_mul, Matrix.det_mul, mul_comm _ M.toBlocks₁₁.det,
      mul_assoc, ← Matrix.det_mul, hTb, Matrix.det_one, mul_one]

theorem a_mul_par (d : SD σ) {q : d.G} {t : GL (Fin d.n) (AE F E)} (hq : IsPar q t) (y : d.G) :
    d.a (q * y) = (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) * d.a y := by
  obtain ⟨p, t', hp, k, hk, rfl⟩ := d.ok.hgt.iwa y
  rw [← mul_assoc, d.ok.hgt.val _ _ (KSplitP.isPar_mul hq hp) k hk, d.ok.hgt.val p t' hp k hk, map_mul, map_mul,
    NNReal.coe_mul]

end PositivityTheory.SiegelWeilFormula.Avac

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Avac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics (mkGR inFrame_mul inFrame_one cw_mul cw_one form_w)

variable {d : SD σ}

theorem iota_vg (hO : LocOpEx) (hI : LocInst) (R : RD d) (w : InfinitePlace F) (y : GR d.n) (hy : InK (mR y))
    {g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ} {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (hT : d.T Φ = vg R g) :
    ∃ c : ℂ, d.T (d.om (R.ι w y) Φ) = vg R (c • g) := by
  obtain ⟨L, hL⟩ := hO F E σ d R w
  obtain ⟨sL, ρ, p, q, e, -, hld, -, hk⟩ := hI F E σ d R w L hL
  have h1 := (hL y _ isSchwartz_indicator_one).2 (psiW R g w) (psiW_indep R g w) Φ hΦ (hT.trans (vg_tens R g w))
  refine ⟨F0 p q e y, ?_⟩
  rw [h1, hk y 1 hy, hld.kvac y hy, vg_tens R _ w]
  funext X
  simp only [RD.tens, psiW, Pi.smul_apply, smul_eq_mul, fP_smul_one]
  ring

theorem dZ_conjT {ζ : ℂ} : (dZ d.n ζ)ᴴ = dZ d.n (star ζ) := by
  simp [dZ, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_smul]

theorem star_zeta (R : RD d) : star R.ζ = R.ζ⁻¹ := by
  rcases R.hζ with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp

theorem kdec (R : RD d) (w : InfinitePlace F) (k : d.G)
    (hk : d.cw w (inFrame d.b k) * (d.cw w (inFrame d.b k))ᴴ = 1) :
    ∃ y : GR d.n, InK (mR y) ∧ d.cw w (inFrame d.b (R.ι w y)) = d.cw w (inFrame d.b k) := by
  have hζ0 := Krd.zeta_ne R.hζ
  obtain ⟨M, hM⟩ : ∃ M, M = d.cw w (inFrame d.b k) := ⟨_, rfl⟩
  have hY := Krd.inG_conj R.hζ M (hM ▸ form_w d R w k)
  have hMM : Mᴴ * M = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 (hM ▸ hk)
  refine ⟨mkGR _ hY, ⟨hY, ?_⟩, ?_⟩
  · show (dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹)ᴴ * (dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹) = 1
    have hA : (dZ d.n R.ζ)ᴴ = dZ d.n R.ζ⁻¹ := by rw [dZ_conjT, star_zeta]
    have hB : (dZ d.n R.ζ⁻¹)ᴴ = dZ d.n R.ζ := by rw [dZ_conjT, star_inv₀, star_zeta, inv_inv]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hA, hB]
    calc dZ d.n R.ζ * (Mᴴ * dZ d.n R.ζ⁻¹) * (dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹)
        = dZ d.n R.ζ * (Mᴴ * (dZ d.n R.ζ⁻¹ * dZ d.n R.ζ) * M) * dZ d.n R.ζ⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Krd.dZ_inv_mul hζ0, Matrix.mul_one, hMM, Matrix.mul_one, Krd.dZ_mul_inv hζ0]
  · rw [← hM]
    have h := R.at_w w (mkGR _ hY)
    calc d.cw w (inFrame d.b (R.ι w (mkGR _ hY)))
        = dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * d.cw w (inFrame d.b (R.ι w (mkGR _ hY)))) := by
          rw [← Matrix.mul_assoc, Krd.dZ_inv_mul hζ0, Matrix.one_mul]
      _ = dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹ * dZ d.n R.ζ) := by rw [h]; rfl
      _ = M := by
          simp only [Matrix.mul_assoc]
          rw [Krd.dZ_inv_mul hζ0, Matrix.mul_one, ← Matrix.mul_assoc, Krd.dZ_inv_mul hζ0, Matrix.one_mul]

theorem cw_inv_iota (R : RD d) (w : InfinitePlace F) (y : GR d.n) (k : d.G) (w' : InfinitePlace F) :
    d.cw w' (inFrame d.b ((R.ι w y)⁻¹ * k)) = d.cw w' (inFrame d.b (R.ι w y)⁻¹) * d.cw w' (inFrame d.b k) := by
  rw [inFrame_mul, cw_mul]

theorem peel (hO : LocOpEx) (hI : LocInst) (hA : FinAct) (R : RD d) (S : Finset (InfinitePlace F)) :
    ∀ k : d.G, (∀ w ∈ S, d.cw w (inFrame d.b k) * (d.cw w (inFrame d.b k))ᴴ = 1) →
      (∀ w ∉ S, d.cw w (inFrame d.b k) = 1) → ∀ g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F), ∀ Φ ∈ d.sch,
        d.T Φ = vg R g → ∃ g' ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F), d.T (d.om k Φ) = vg R g' := by
  induction S using Finset.induction_on with
  | empty =>
    intro k _ h1 g hg Φ hΦ hT
    obtain ⟨g', hg', H⟩ := hA F E σ d k (fun w => h1 w (Finset.notMem_empty w)) g hg
    exact ⟨g', hg', H _ (gauss_indep R) Φ hΦ hT⟩
  | insert w S hw ih =>
    intro k h0 h1 g hg Φ hΦ hT
    obtain ⟨y, hy, hyw⟩ := kdec R w k (h0 w (Finset.mem_insert_self w S))
    have hinv : ∀ w', w' ≠ w → d.cw w' (inFrame d.b (R.ι w y)⁻¹) = 1 := fun w' h => by
      rw [← map_inv]; exact R.off_w w w' y⁻¹ h
    have e1 : d.cw w (inFrame d.b (R.ι w y)⁻¹) * d.cw w (inFrame d.b (R.ι w y)) = 1 := by
      rw [← cw_mul, ← inFrame_mul, inv_mul_cancel, inFrame_one, cw_one]
    have hkw : d.cw w (inFrame d.b ((R.ι w y)⁻¹ * k)) = 1 := by rw [cw_inv_iota, ← hyw, e1]
    have hkw' : ∀ w', w' ≠ w → d.cw w' (inFrame d.b ((R.ι w y)⁻¹ * k)) = d.cw w' (inFrame d.b k) := fun w' h => by
      rw [cw_inv_iota, hinv w' h, Matrix.one_mul]
    obtain ⟨g₁, hg₁, e₁⟩ := ih ((R.ι w y)⁻¹ * k)
      (fun w' h => by
        rw [hkw' w' (fun e => hw (e ▸ h))]
        exact h0 w' (Finset.mem_insert_of_mem h))
      (fun w' h => by
        by_cases e : w' = w
        · rw [e, hkw]
        · rw [hkw' w' e]
          exact h1 w' fun h' => (Finset.mem_insert.1 h').elim e h)
      g hg Φ hΦ hT
    obtain ⟨c, e₂⟩ := iota_vg hO hI R w y hy (d.ok.dbl.weil.2.1.pres _ Φ hΦ) e₁
    refine ⟨c • g₁, Submodule.smul_mem _ c hg₁, ?_⟩
    rw [show k = R.ι w y * ((R.ι w y)⁻¹ * k) from (mul_inv_cancel_left _ _).symm, map_mul, Module.End.mul_apply]
    exact e₂

theorem vg_K' (hO : LocOpEx) (hI : LocInst) (hA : FinAct) (R : RD d)
    {g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ} (hg : g ∈ SB _) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (hT : d.T Φ = vg R g)
    {k : d.G} (hk : k ∈ d.K) : ∃ g' ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F), d.T (d.om k Φ) = vg R g' :=
  peel hO hI hA R Finset.univ k (fun w _ => ((d.ok.stdK k).1 hk).1 w) (fun w h => absurd (Finset.mem_univ w) h) g hg Φ hΦ hT

theorem vac_K' (hT : TAll) (hF : FockMem) (hO : LocOpEx) (hI : LocInst) (hA : FinAct) (R : RD d) :
    ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → ∀ k ∈ d.K, d.T (d.om k Φ) ∈ R.vac := by
  let S' : Submodule ℂ d.Fn :=
    { carrier := {Φ | Φ ∈ d.sch ∧ ∀ k ∈ d.K, d.T (d.om k Φ) ∈ R.vac}
      zero_mem' := ⟨zero_mem _, fun k _ => by
        rw [map_zero]
        have : d.T 0 = 0 := (Tl d).map_zero
        rw [this]; exact zero_mem _⟩
      add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, fun k hk => by
        rw [map_add (f := _)]
        have : d.T (d.om k a + d.om k b) = d.T (d.om k a) + d.T (d.om k b) := (Tl d).map_add _ _
        rw [this]; exact add_mem (ha.2 k hk) (hb.2 k hk)⟩
      smul_mem' := fun c a ha => ⟨Submodule.smul_mem _ c ha.1, fun k hk => by
        rw [map_smul]
        have : d.T (c • d.om k a) = c • d.T (d.om k a) := (Tl d).map_smul _ _
        rw [this]; exact Submodule.smul_mem _ c (ha.2 k hk)⟩ }
  have hle : R.vac ≤ S'.map (Tl d) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    have hm : vg R g ∈ d.schM := (hF F E σ d R).1 (vac_le_fock R (vg_mem R hg))
    obtain ⟨Φ, hΦ, e⟩ := (hT.1 F E σ d).2.1 _ hm
    refine ⟨Φ, ⟨hΦ, fun k hk => ?_⟩, e⟩
    obtain ⟨g', hg', e'⟩ := vg_K' hO hI hA R hg hΦ e hk
    rw [e']; exact vg_mem R hg'
  intro Φ hΦ hv k hk
  obtain ⟨Φ', hΦ', e⟩ := hle hv
  have : Φ' = Φ := T_inj hT.1 hΦ'.1 hΦ e
  rw [← this]
  exact hΦ'.2 k hk

end PositivityTheory.SiegelWeilFormula.Avac

end
end
