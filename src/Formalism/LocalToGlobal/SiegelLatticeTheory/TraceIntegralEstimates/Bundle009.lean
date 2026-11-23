module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Saturated
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpRootCut
public import Formalism.FormalDegreeBessel.FinalG
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle038
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PtCellUniq
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
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.Bundle003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.Bundle005
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.HeisOpHolds

@[expose] public section

section

noncomputable section

open scoped Classical

namespace Formalism.L2.S.Pv.ClassCounting

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.TermsAtPtFiniteW
  PI.TermsAtPtFiniteW.HeisW PI.TermsAtPtFiniteW.LeviW Formalism.L2.SG.Saturated

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem orth_span (v : Fin r → S.V) {y : S.V} (h : ∀ a, S.hT (v a) y = 0) :
    ∀ x ∈ Submodule.span E (Set.range v), S.hT x y = 0 := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, rfl⟩ := hz
    exact h a
  | zero => simp
  | add x x' _ _ hx hx' => simp [hx, hx']
  | smul c x _ hx => simp [hx]

theorem latSpan_le_span (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (v : Fin r → S.V) :
    latSpan aa v ≤ (Submodule.span E (Set.range v)).restrictScalars (𝓞 E) := by
  unfold latSpan
  rw [Submodule.span_le]
  rintro y ⟨a, x, -, rfl⟩
  exact Submodule.smul_mem _ x (Submodule.subset_span ⟨a, rfl⟩)

theorem coef_of_span (e f : Fin r → S.V) (hfe : ∀ a b, S.hT (f a) (e b) = if a = b then 1 else 0) {x : S.V}
    (hx : x ∈ Submodule.span E (Set.range e)) : x = ∑ a, S.hT (f a) x • e a := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hx
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1

  rw [map_sum]
  simp [hfe]

variable (Λ : Submodule (𝓞 E) S.V) (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (e f : Fin r → S.V)
  (L : Submodule (𝓞 E) S.V)

theorem mem_L_of_dual (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ)
    (hΛ : Λ = latSpan aa e ⊔ L ⊔ latSpan (fun a => (aa a)⁻¹) f)
    (hee : ∀ a b, S.hT (e a) (e b) = 0) (hff : ∀ a b, S.hT (f a) (f b) = 0)
    (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0)
    (hL : ∀ x ∈ L, ∀ a, S.hT (e a) x = 0 ∧ S.hT (f a) x = 0)
    {x : S.V} (hxe : ∀ a, S.hT (e a) x = 0) (hxf : ∀ a, S.hT (f a) x = 0)
    (hxL : ∀ y ∈ L, ∃ o : 𝓞 E, (o : E) = S.hT y x) : x ∈ L := by
  have horth2 : ∀ (u : S.V) (w : Fin r → S.V), (∀ b, S.hT u (w b) = 0) →
      ∀ y ∈ Submodule.span E (Set.range w), S.hT u y = 0 := by
    intro u w hw y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨b, rfl⟩ := hz
      exact hw b
    | zero => simp
    | add x x' _ _ hx hx' => simp [hx, hx']
    | smul c x _ hx => simp [hx]
  have hfe : ∀ a b, S.hT (f a) (e b) = if a = b then 1 else 0 := by
    intro a b
    rw [← S.herm.eq (e b) (f a), hef b a]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  have hxd : x ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by
    unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
    simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]
    intro y hy
    rw [hΛ] at hy
    obtain ⟨y12, hy12, y2, hy2, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨y1, hy1, yL, hyL, rfl⟩ := Submodule.mem_sup.mp hy12
    have h1 : S.hT y1 x = 0 := orth_span e hxe y1 (latSpan_le_span aa e hy1)
    have h2 : S.hT y2 x = 0 := orth_span f hxf y2 (latSpan_le_span _ f hy2)
    obtain ⟨o, ho⟩ := hxL yL hyL
    refine ⟨o, ?_⟩
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, h1, h2, ← ho]
    simp
  have hxΛ : x ∈ Λ := by
    unfold Formalism.HermitianLatticesTheory.IsUnimodular at hU
    rw [hU] at hxd
    exact hxd
  rw [hΛ] at hxΛ
  obtain ⟨x12, hx12, x2, hx2, hxeq⟩ := Submodule.mem_sup.mp hxΛ
  obtain ⟨x1, hx1, xL, hxL', rfl⟩ := Submodule.mem_sup.mp hx12
  have hx1' : x1 ∈ Submodule.span E (Set.range e) := latSpan_le_span aa e hx1
  have hx2' : x2 ∈ Submodule.span E (Set.range f) := latSpan_le_span _ f hx2
  have hf1 : ∀ a, S.hT (f a) x1 = 0 := by
    intro a
    have h := hxf a
    rw [← hxeq, map_add (f := _), map_add (f := _), (hL xL hxL' a).2, horth2 (f a) f (hff a) x2 hx2'] at h
    simpa using h
  have he2 : ∀ a, S.hT (e a) x2 = 0 := by
    intro a
    have h := hxe a
    rw [← hxeq, map_add (f := _), map_add (f := _), (hL xL hxL' a).1, horth2 (e a) e (hee a) x1 hx1'] at h
    simpa using h
  have h10 : x1 = 0 := by
    rw [coef_of_span e f hfe hx1']
    simp [hf1]
  have h20 : x2 = 0 := by
    rw [coef_of_span f e hef hx2']
    simp [he2]
  rw [← hxeq, h10, h20, zero_add, add_zero]
  exact hxL'

theorem exists_partner (z : S.V) (hzL : z ∈ L) (hzz : S.hT z z ≠ 0)
    (hint : ∀ x ∈ L, ∀ y ∈ L, ∃ o : 𝓞 E, (o : E) = S.hT x y)
    (hdual : ∀ c : E, (∀ y ∈ L, ∃ o : 𝓞 E, (o : E) = S.hT y (c • z)) → c • z ∈ L)
    (hprim : ∀ c : E, c • z ∈ L → ∃ o : 𝓞 E, (o : E) = c) :
    ∃ σ ∈ L, S.hT σ z = 1 := by
  classical
  have hstar : ∀ o : 𝓞 E, ∃ o' : 𝓞 E, (o' : E) = star (o : E) := by
    intro o
    exact ⟨⟨star (o : E), (o.2).map (starRingEnd E).toIntAlgHom⟩, rfl⟩
  have hsmul : ∀ (c : 𝓞 E) (y : S.V), c • y = (c : E) • y := fun c y => (algebraMap_smul E c y).symm
  let J : Ideal (𝓞 E) :=
    { carrier := {o | ∃ σ ∈ L, (o : E) = S.hT σ z}
      add_mem' := by
        rintro a b ⟨σ, hσ, ha⟩ ⟨τ, hτ, hb⟩
        exact ⟨σ + τ, L.add_mem hσ hτ, by simp [ha, hb]⟩
      zero_mem' := ⟨0, L.zero_mem, by simp⟩
      smul_mem' := by
        rintro c a ⟨σ, hσ, ha⟩
        obtain ⟨c', hc'⟩ := hstar c
        refine ⟨c' • σ, L.smul_mem c' hσ, ?_⟩
        rw [hsmul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, ← ha, hc']
        simp [starRingEnd_apply] }
  obtain ⟨o0, ho0⟩ := hint z hzL z hzL
  have hJ : J ≠ ⊥ := by
    intro h
    have hmem : o0 ∈ J := ⟨z, hzL, ho0⟩
    rw [h, Ideal.mem_bot] at hmem
    rw [hmem] at ho0
    exact hzz (by simpa using ho0.symm)
  have hI : (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hJ
  have hinv : (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹ ≤ 1 := by
    intro x hx
    rw [FractionalIdeal.mem_inv_iff hI] at hx
    have hxz : x • z ∈ L := by
      apply hdual
      intro y hy
      obtain ⟨o, ho⟩ := hint y hy z hzL
      have hoJ : (o : E) ∈ (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :=
        (FractionalIdeal.mem_coeIdeal _).mpr ⟨o, ⟨y, hy, ho⟩, rfl⟩
      obtain ⟨o', ho'⟩ := (FractionalIdeal.mem_one_iff _).mp (hx _ hoJ)
      exact ⟨o', by rw [map_smul, smul_eq_mul, ← ho, ← ho']⟩
    obtain ⟨o, ho⟩ := hprim x hxz
    exact (FractionalIdeal.mem_one_iff _).mpr ⟨o, ho⟩
  have h1 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≤ J := by
    calc (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = J * (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹ :=
          (mul_inv_cancel₀ hI).symm
      _ ≤ J * 1 := by gcongr
      _ = J := mul_one _
  have h1J : (1 : E) ∈ (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := h1 (FractionalIdeal.one_mem_one _)
  obtain ⟨j, ⟨σ, hσ, hj⟩, hj1⟩ := (FractionalIdeal.mem_coeIdeal _).mp h1J
  refine ⟨σ, hσ, ?_⟩
  rw [← hj]
  exact hj1

end Gen

end Formalism.L2.S.Pv.ClassCounting

end
end

section

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Formalism.L2.S.Pv.AmpCell

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

theorem one_mem_UW' (z : Fin (2 * r + k + 1) → ℂ) :
    (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UWset k r z := by
  refine ⟨?_, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩
  show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r
  simp

theorem mem_S_of_N (z : Fin (2 * r + k + 1) → ℂ) {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hn : n ∈ Nset k r) : n ∈ Sset k r z := ⟨1, one_mem_UW' z, n, hn, (one_mul n).symm⟩

def Ds (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.diagonal fun b => (-1 : ℂ) ^ (r - b.val)

theorem Ds_mul_Ds : Ds r * Ds r = 1 := by
  unfold Ds
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  rw [← mul_pow]
  norm_num

theorem zhatO_eq (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ZhatO k r z z' g = Zhat k r z z' g * Ds r := by
  ext a b
  simp only [Ds]
  rw [Matrix.mul_diagonal]
  simp only [ZhatO]
  ring

theorem inCell_of_rep {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z)
    (hT' : 0 < Tz k r z') {n n' g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hn : n ∈ Nset k r)
    (hn' : n' ∈ Nset k r) {p : Point ℂ (r + 1)} (hZ : ZhatO k r z z' g₀ = ptMat p) :
    IsInCell (ZhatO k r z z' (n * g₀ * n')) p := by
  have hni : n⁻¹ ∈ Nset k r := WeylGroupFacts.mem_n_inv hn
  have hE := Formalism.FourierDecayAlt.P.zhat_equivalence k r z z' ⟨hz, hT⟩ ⟨hz', hT'⟩ n⁻¹ (mem_S_of_N z hni) n'
    (mem_S_of_N z' hn') g₀
  have hnn : (n⁻¹)⁻¹ = n := Matrix.nonsing_inv_nonsing_inv _ (WeylGroupFacts.isUnit_of_uh hn.1)
  rw [hnn] at hE
  have hu := ((Formalism.FourierDecayAlt.P.unipotent_map_frame k r z ⟨hz, hT⟩).1 n⁻¹ (mem_S_of_N z hni)).2.1
  have hu' := ((Formalism.FourierDecayAlt.P.unipotent_map_frame k r z' ⟨hz', hT'⟩).1 n' (mem_S_of_N z' hn')).2.1
  refine ⟨(Formalism.FourierDecayAlt.C2.uMap k r z n⁻¹)ᴴ, Ds r * Formalism.FourierDecayAlt.C2.uMap k r z' n' * Ds r, fun i j => ⟨fun hij => ?_, fun hij => ?_⟩,
    fun i j => ⟨fun hij => ?_, fun hij => ?_⟩, ?_⟩
  · rw [Matrix.conjTranspose_apply, hu.1 j i hij, star_zero]
  · subst hij; rw [Matrix.conjTranspose_apply, hu.2 i, star_one]
  · unfold Ds; rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hu'.1 i j hij]; ring
  · subst hij; unfold Ds; rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hu'.2 i, mul_one, ← pow_add, ← two_mul, pow_mul]
    simp
  · rw [zhatO_eq, hE, ← hZ, zhatO_eq]
    calc (Formalism.FourierDecayAlt.C2.uMap k r z n⁻¹)ᴴ * Zhat k r z z' g₀ * Formalism.FourierDecayAlt.C2.uMap k r z' n' * Ds r
        = (Formalism.FourierDecayAlt.C2.uMap k r z n⁻¹)ᴴ * (Zhat k r z z' g₀ * (Ds r * Ds r)) * Formalism.FourierDecayAlt.C2.uMap k r z' n' * Ds r := by
          rw [Ds_mul_Ds, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem zhat_monomial {z z' : Fin (2 * r + k + 1) → ℂ} {g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {p : Point ℂ (r + 1)} (hZ : ZhatO k r z z' g₀ = ptMat p) :
    Formalism.FourierDecayAlt.C2.IsMonomial (Zhat k r z z' g₀) := by
  have hinv : Function.Involutive (Formalism.L2.SG.PtCell.pinv p) := Formalism.L2.SG.PtCell.pinv_pinv p
  refine ⟨hinv.toPerm _, fun a => (-1 : ℂ) ^ (r - a.val) * Formalism.L2.SG.PtCell.pval p.1 (Formalism.L2.SG.PtCell.pinv p a).val,
    fun a => mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Formalism.L2.SG.PtCell.pval_ne p.1 (fun b hb => (p.2.1 b hb).1) _ (by rw [p.2.2]; exact (Formalism.L2.SG.PtCell.pinv p a).isLt)),
    ?_⟩
  have hZ' : Zhat k r z z' g₀ = ptMat p * Ds r := by
    rw [← hZ, zhatO_eq, Matrix.mul_assoc, Ds_mul_Ds, Matrix.mul_one]
  rw [hZ', Formalism.L2.SG.PtCell.ptMat_eq_mono]
  ext i a
  rw [show Ds r = Matrix.diagonal (fun b : Fin (r + 1) => (-1 : ℂ) ^ (r - b.val)) from rfl, Matrix.mul_diagonal]
  simp only [Formalism.L2.SG.PtCell.mono, Formalism.FourierDecayAlt.C2.monoP, Matrix.of_apply, Function.Involutive.coe_toPerm]
  by_cases h : a = Formalism.L2.SG.PtCell.pinv p i
  · have h2 : i = Formalism.L2.SG.PtCell.pinv p a := by rw [h, hinv]
    rw [if_pos h]
    simp only [h2, if_true]
    ring
  · have h2 : ¬ i = Formalism.L2.SG.PtCell.pinv p a := fun e => h (by rw [e, hinv])
    rw [if_neg h]
    simp only [h2, if_false]
    ring

theorem cell_representation : Formalism.MainNotions.S.Pv.LemmaJ.CellRep := by
  intro D W γ p θ' νR hz hz' hT hT' hRel hνR
  obtain ⟨p', μR, ⟨n, hn, n', hn', g₀, hγ, hZ', μ₀, h0, h1, hμR⟩, hq⟩ := hνR
  have hcell := inCell_of_rep hz hz' hT hT' hn hn' hZ'
  rw [← hγ] at hcell
  have hpp : p = p' := Formalism.L2.SG.PtCell.isInCell_uniq hRel.2.1 hcell
  subst hpp
  have hnU : n ∈ UH (Hpk D.R.k D.R.rS) := hn.1
  have hn'U : n' ∈ UH (Hpk D.R.k D.R.rS) := hn'.1
  have hu := WeylGroupFacts.isUnit_of_uh hnU
  have hu' := WeylGroupFacts.isUnit_of_uh hn'U
  have hg₀ : g₀ = n⁻¹ * γ * n'⁻¹ := by
    rw [hγ]
    calc g₀ = (n⁻¹ * n) * g₀ * (n' * n'⁻¹) := by
          rw [Matrix.nonsing_inv_mul _ hu, Matrix.mul_nonsing_inv _ hu', Matrix.one_mul, Matrix.mul_one]
      _ = n⁻¹ * (n * g₀ * n') * n'⁻¹ := by simp only [Matrix.mul_assoc]
  have hg₀U : g₀ ∈ UH (Hpk D.R.k D.R.rS) := by
    rw [hg₀]
    exact WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hnU) hRel.1) (WeylGroupFacts.uh_inv hn'U)
  have hGeq : Gf D.R.k D.R.rS W.z W.z' γ = Gf D.R.k D.R.rS W.z W.z' g₀ := by
    rw [hγ]
    exact Formalism.QuantumDeterminants.gInv _ _ _ _ hz hz' n (mem_S_of_N _ hn) n' (mem_S_of_N _ hn') g₀
  have hG : 0 < Gf D.R.k D.R.rS W.z W.z' g₀ := by
    refine lt_of_le_of_ne (Formalism.QuantumDeterminants.gNonneg _ _ _ _ hz hz' hT hT' g₀ hg₀U) (fun e => hRel.2.2 ?_)
    rw [hGeq, ← e]
  refine ⟨n, hn, n', hn', g₀, hγ, hg₀U, hZ', hG, zhat_monomial hZ', μ₀, h0, h1, ?_⟩
  rw [← hμR]
  exact hq

end Formalism.L2.S.Pv.AmpCell
end
end
