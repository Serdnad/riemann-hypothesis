module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Mathlib.MeasureTheory.Constructions.Pi
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle177
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle121
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

noncomputable section

namespace GlobalTheory.IwConst.Adapted

variable {n a b c e : ℕ}

theorem trace_cmb_mul_cmb {E : Fin a → Matrix (Fin n) (Fin n) ℂ} {F : Fin b → Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ i k, (E i * F k).trace = 0) (x : Fin a → ℝ) (y : Fin b → ℝ) : (cmb E x * cmb F y).trace = 0 := by
  simp [cmb, Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum, h]

theorem trace_cmb_mul_cmb_star {E : Fin a → Matrix (Fin n) (Fin n) ℂ} {F : Fin b → Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ i k, (E i * (F k)ᴴ).trace = 0) (x : Fin a → ℝ) (y : Fin b → ℝ) : (cmb E x * (cmb F y)ᴴ).trace = 0 := by
  simp [cmb, Matrix.conjTranspose_sum, Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum, h]

theorem trace_star_star (X Y : Matrix (Fin n) (Fin n) ℂ) (h : (X * Y).trace = 0) : (Xᴴ * Yᴴ).trace = 0 := by
  rw [← Matrix.conjTranspose_mul, Matrix.trace_conjTranspose, Matrix.trace_mul_comm, h, star_zero]

theorem hs_neg_star (X : Matrix (Fin n) (Fin n) ℂ) : Formalism.REAL.hs (-Xᴴ) = Formalism.REAL.hs X := by
  rw [← nrm_sq, ← nrm_sq, nrm_neg, nrm_conjTranspose]

theorem hs_three {EN : Fin a → Matrix (Fin n) (Fin n) ℂ} {EM : Fin b → Matrix (Fin n) (Fin n) ℂ}
    (hN : IsON EN) (hM : IsON EM) (h1 : ∀ i k, (EN i * (EM k)ᴴ).trace = 0) (h2 : ∀ i k, (EN i * EM k).trace = 0)
    (h3 : ∀ i k, (EN i * EN k).trace = 0) (x u : Fin a → ℝ) (y : Fin b → ℝ) :
    Formalism.REAL.hs (cmb EN x + cmb EM y + -(cmb EN u)ᴴ) = ∑ i, x i ^ 2 + ∑ i, y i ^ 2 + ∑ i, u i ^ 2 := by
  have e2 : (cmb EM y * cmb EN u).trace = 0 := by
    rw [Matrix.trace_mul_comm]; exact trace_cmb_mul_cmb h2 u y
  rw [hs_add, hs_add, hs_neg_star, hs_cmb hN, hs_cmb hM, hs_cmb hN, trace_cmb_mul_cmb_star h1]
  simp [Matrix.add_mul, trace_cmb_mul_cmb h3, e2]

def cmbL (E : Fin a → Matrix (Fin n) (Fin n) ℂ) : (Fin a → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := cmb E
  map_add' := cmb_add E
  map_smul' := cmb_smul E

def crdL (E : Fin a → Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Fin a → ℝ) where
  toFun := crd E
  map_add' := crd_add E
  map_smul' := crd_smul E

def adp (EN : Fin a → Matrix (Fin n) (Fin n) ℂ) (EL : Fin e → Matrix (Fin n) (Fin n) ℂ) :
    ((Fin a → ℝ) × (Fin e → ℝ)) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun v := cmb EN ((Real.sqrt 2)⁻¹ • v.1) - (cmb EN ((Real.sqrt 2)⁻¹ • v.1))ᴴ + cmb EL v.2
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, smul_add, cmb_add, Matrix.conjTranspose_add]; abel
  map_smul' r v := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_comm (Real.sqrt 2)⁻¹ r, cmb_smul EN r, cmb_smul EL r,
      Matrix.conjTranspose_smul, star_trivial, RingHom.id_apply, smul_add, smul_sub]

theorem cmb_mem_of {E : Fin a → Matrix (Fin n) (Fin n) ℂ} {S : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}
    (h : ∀ i, E i ∈ S) (x : Fin a → ℝ) : cmb E x ∈ S :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h i)

theorem cmb_sub_star_mem {E : Fin a → Matrix (Fin n) (Fin n) ℂ} {S : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}
    (h : ∀ i, E i - (E i)ᴴ ∈ S) (x : Fin a → ℝ) : cmb E x - (cmb E x)ᴴ ∈ S := by
  have : cmb E x - (cmb E x)ᴴ = cmb (fun i => E i - (E i)ᴴ) x := by
    simp [cmb, Matrix.conjTranspose_sum, smul_sub, Finset.sum_sub_distrib]
  rw [this]; exact cmb_mem_of h x

theorem sum_sq_half (w : Fin a → ℝ) : ∑ i, ((Real.sqrt 2)⁻¹ • w) i ^ 2 = ∑ i, w i ^ 2 / 2 := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_pow, inv_pow, Real.sq_sqrt (by norm_num)]
  ring

theorem exists_adapted (n : ℕ) (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ)
    (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ)
    (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ) (hN : IsON EN) (hM : IsON EM) (hK : IsON EK) (hL : IsON EL)
    (hR : LieRel EN EM EK EL) (hd : dK = dN + dL) :
    ∃ (Q : (Fin dK → ℝ) →ₗ[ℝ] (Fin dN → ℝ) × (Fin dL → ℝ)) (ι : (Fin dL → ℝ) →ₗ[ℝ] (Fin dM → ℝ)),
      (∀ z, ∑ i, (Q z).1 i ^ 2 + ∑ i, (Q z).2 i ^ 2 = ∑ i, z i ^ 2) ∧
      ∀ x y z, Formalism.REAL.hs (cmb EN x + cmb EM y + cmb EK z) =
        ∑ i, (x i + (Q z).1 i / Real.sqrt 2) ^ 2 + ∑ i, (y i + ι (Q z).2 i) ^ 2 + ∑ i, (Q z).1 i ^ 2 / 2 ∧
        crd EL (cmb EK z) = (Q z).2 := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := hR
  have hι : ∀ t, cmb EM (crd EM (cmb EL t)) = cmb EL t := fun t => cmb_crd hM (cmb_mem_of h4 t)
  have hmem : ∀ v, adp EN EL v ∈ Submodule.span ℝ (Set.range EK) := fun v =>
    Submodule.add_mem _ (cmb_sub_star_mem h7 _) (cmb_mem_of h5 _)
  have hsum : ∀ x y v, Formalism.REAL.hs (cmb EN x + cmb EM y + adp EN EL v) =
      ∑ i, (x i + v.1 i / Real.sqrt 2) ^ 2 + ∑ i, (y i + crd EM (cmb EL v.2) i) ^ 2 + ∑ i, v.1 i ^ 2 / 2 := by
    intro x y v
    have e : cmb EN x + cmb EM y + adp EN EL v = cmb EN (x + (Real.sqrt 2)⁻¹ • v.1) +
        cmb EM (y + crd EM (cmb EL v.2)) + -(cmb EN ((Real.sqrt 2)⁻¹ • v.1))ᴴ := by
      rw [cmb_add, cmb_add, hι]
      simp only [adp, LinearMap.coe_mk, AddHom.coe_mk]
      abel
    rw [e, hs_three hN hM h1 h2 h3, sum_sq_half]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
  have hhs : ∀ v, Formalism.REAL.hs (adp EN EL v) = ∑ i, v.1 i ^ 2 + ∑ i, v.2 i ^ 2 := by
    intro v
    have e : adp EN EL v = cmb EN ((Real.sqrt 2)⁻¹ • v.1) +
        cmb EM (crd EM (cmb EL v.2)) + -(cmb EN ((Real.sqrt 2)⁻¹ • v.1))ᴴ := by
      rw [hι]
      simp only [adp, LinearMap.coe_mk, AddHom.coe_mk]
      abel
    rw [e, hs_three hN hM h1 h2 h3, sum_sq_half, ← hs_cmb hM, hι, hs_cmb hL, ← Finset.sum_div]
    ring
  let T : ((Fin dN → ℝ) × (Fin dL → ℝ)) →ₗ[ℝ] (Fin dK → ℝ) := (crdL EK).comp (adp EN EL)
  have hT : ∀ v, cmb EK (T v) = adp EN EL v := fun v => cmb_crd hK (hmem v)
  have hinj : Function.Injective T := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    have h := hhs v
    rw [← hT, hv, hs_cmb hK] at h
    simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero] at h
    have p1 : 0 ≤ ∑ i, v.1 i ^ 2 := by positivity
    have p2 : 0 ≤ ∑ i, v.2 i ^ 2 := by positivity
    have q1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (v.1 i)).1
      (show ∑ i, v.1 i ^ 2 = 0 by linarith)
    have q2 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (v.2 i)).1
      (show ∑ i, v.2 i ^ 2 = 0 by linarith)
    ext i
    · exact pow_eq_zero_iff two_ne_zero |>.1 (q1 i (Finset.mem_univ i))
    · exact pow_eq_zero_iff two_ne_zero |>.1 (q2 i (Finset.mem_univ i))
  have hdim : Module.finrank ℝ ((Fin dN → ℝ) × (Fin dL → ℝ)) = Module.finrank ℝ (Fin dK → ℝ) := by
    simp [hd]
  let U := LinearMap.linearEquivOfInjective T hinj hdim
  have hU : ∀ z, cmb EK z = adp EN EL (U.symm z) := by
    intro z
    rw [← hT]
    congr 1
    exact (U.apply_symm_apply z).symm
  refine ⟨U.symm.toLinearMap, (crdL EM).comp (cmbL EL), fun z => ?_, fun x y z => ⟨?_, ?_⟩⟩
  · rw [← hs_cmb hK z, hU, hhs]; rfl
  · rw [hU, hsum]; rfl
  · rw [hU]
    change crd EL (_ - _ + _) = (U.symm z).2
    rw [crd_add, crd_cmb hL, add_eq_right]
    funext i
    simp only [crd, Pi.zero_apply]
    rw [← cmb_crd hM (h4 i), Matrix.sub_mul, Matrix.trace_sub, trace_cmb_mul_cmb_star h1,
      trace_star_star _ _ (trace_cmb_mul_cmb h2 _ _)]
    simp

end GlobalTheory.IwConst.Adapted
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConstApprox

variable {n : ℕ}

theorem nrm_conj_Jm (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    nrm (Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε) = nrm X := by

  have hs : ∀ a, ‖(if ε a then (1 : ℂ) else -1)‖ = 1 := fun a => by split_ifs <;> simp
  unfold nrm
  congr 1
  unfold Formalism.REAL.hs Formalism.REAL.Jm
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, norm_mul, norm_mul, hs, hs, one_mul, mul_one]

theorem nrm_sub_proj_le_sq (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ)
    (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (h : IsCut ε S E) (g : Formalism.REAL.UJ ε) (hg : g ∈ S) :
    nrm (uMat g - 1 - cmb E (crd E (uMat g - 1))) ≤ nrm (uMat g - 1) ^ 2 := by

  have hON : IsON E := h.isON
  obtain ⟨H, hH, -⟩ := h.subgroup
  obtain ⟨A, hAmul, -, hspan, hS⟩ := h
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have hJt : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := Formalism.REAL.Jm_conjTranspose ε
  have hJJ' : ∀ M : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hgU : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  have h1 : uMat g⁻¹ * uMat g = 1 := by
    show (((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * _ = 1
    rw [Subgroup.coe_inv, Units.inv_mul]
  have h2 : uMat g * uMat g⁻¹ = 1 := by
    show _ * (((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
    rw [Subgroup.coe_inv, Units.mul_inv]
  have hinv : uMat g⁻¹ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by
    calc uMat g⁻¹ = Formalism.REAL.Jm ε * Formalism.REAL.Jm ε * uMat g⁻¹ := by rw [hJJ, Matrix.one_mul]
      _ = Formalism.REAL.Jm ε * ((uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g) * uMat g⁻¹ := by rw [hgU]
      _ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε * (uMat g * uMat g⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by rw [h2, Matrix.mul_one]
  have hgH : g ∈ H := by rw [← SetLike.mem_coe, hH]; exact hg
  have hgi : g⁻¹ ∈ S := by rw [← hH]; exact H.inv_mem hgH
  rw [hS] at hg hgi
  have hXA : uMat g - 1 ∈ A := hg
  have hXsA : uMat g⁻¹ - 1 ∈ A := hgi
  have hXs : Formalism.REAL.Jm ε * (uMat g - 1)ᴴ * Formalism.REAL.Jm ε = uMat g⁻¹ - 1 := by
    rw [hinv]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, hJJ]
  have key : (uMat g⁻¹ - 1) * (uMat g - 1) = -((uMat g - 1) + (uMat g⁻¹ - 1)) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, h1, Matrix.mul_one, Matrix.one_mul]
    abel
  have hG : Formalism.REAL.inG ε ((1 / 2 : ℝ) • ((uMat g - 1) - (uMat g⁻¹ - 1))) := by
    rw [← hXs]
    generalize uMat g - 1 = X
    have h0 : (X - Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε)ᴴ * Formalism.REAL.Jm ε +
        Formalism.REAL.Jm ε * (X - Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) = 0 := by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        hJt, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hJJ, hJJ', Matrix.mul_one]
      abel
    unfold Formalism.REAL.inG
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h0,
      smul_zero]
  have hY : (1 / 2 : ℝ) • ((uMat g - 1) - (uMat g⁻¹ - 1)) ∈ Submodule.span ℝ (Set.range E) :=
    (hspan _).1 ⟨A.smul_mem _ (A.sub_mem hXA hXsA), hG⟩
  have hsq : nrm (uMat g⁻¹ - 1) = nrm (uMat g - 1) := by
    rw [← hXs, nrm_conj_Jm, nrm_conjTranspose]
  calc nrm (uMat g - 1 - cmb E (crd E (uMat g - 1)))
      ≤ nrm (uMat g - 1 - (1 / 2 : ℝ) • ((uMat g - 1) - (uMat g⁻¹ - 1))) := nrm_sub_proj_le hON _ hY
    _ = nrm ((-(1 / 2 : ℝ)) • ((uMat g⁻¹ - 1) * (uMat g - 1))) := by
        rw [key]
        congr 1
        module
    _ = 1 / 2 * nrm ((uMat g⁻¹ - 1) * (uMat g - 1)) := by
        rw [nrm_smul]
        norm_num
    _ ≤ 1 / 2 * (nrm (uMat g⁻¹ - 1) * nrm (uMat g - 1)) := by
        gcongr
        exact nrm_mul_le _ _
    _ ≤ nrm (uMat g - 1) ^ 2 := by
        rw [hsq]
        nlinarith [sq_nonneg (nrm (uMat g - 1)), nrm_nonneg (uMat g - 1)]

end GlobalTheory.IwConstApprox
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

noncomputable section

namespace GlobalTheory.IwConst.Shear

theorem vol_ball_type (κ : Type) [Fintype κ] (d : ℕ) (h : Fintype.card κ = d) :
    volume {x : κ → ℝ | ∑ i, x i ^ 2 ≤ 1} = ballVol d := by
  classical
  let e : κ ≃ Fin d := Fintype.equivFinOfCardEq h
  have h1 := (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).measurePreserving
  have h2 := PiLp.volume_preserving_toLp κ
  have h3 := (h1.comp h2).measure_preimage
    (s := Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) measurableSet_closedBall.nullMeasurableSet
  unfold ballVol
  rw [← Measure.addHaar_unitClosedBall_eq_addHaar_unitBall, ← h3]
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Function.comp_apply, mem_closedBall_zero_iff,
    LinearIsometryEquiv.norm_map, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, Real.sqrt_le_one]

theorem vol_ball_three (a b : ℕ) :
    volume {p : ((Fin a → ℝ) × (Fin b → ℝ)) × (Fin a → ℝ) |
      ∑ i, p.1.1 i ^ 2 + ∑ i, p.1.2 i ^ 2 + ∑ i, p.2 i ^ 2 ≤ 1} = ballVol (2 * a + b) := by
  rw [← vol_ball_type ((Fin a ⊕ Fin b) ⊕ Fin a) (2 * a + b) (by simp; ring)]
  have h1 := volume_measurePreserving_sumPiEquivProdPi (fun _ : (Fin a ⊕ Fin b) ⊕ Fin a => ℝ)
  have h2 := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => ℝ)
  have h3 := (h2.prod (MeasurePreserving.id (volume : Measure (Fin a → ℝ)))).comp h1
  have hm : MeasurableSet {p : ((Fin a → ℝ) × (Fin b → ℝ)) × (Fin a → ℝ) |
      ∑ i, p.1.1 i ^ 2 + ∑ i, p.1.2 i ^ 2 + ∑ i, p.2 i ^ 2 ≤ 1} :=
    measurableSet_le (by fun_prop) measurable_const
  have h4 := h3.measure_preimage hm.nullMeasurableSet
  rw [Measure.volume_eq_prod, ← h4]
  congr 1
  ext x
  simp [Fintype.sum_sum_type, MeasurableEquiv.sumPiEquivProdPi]

theorem vol_scale (a : ℕ) (q : ℝ) :
    volume {w : Fin a → ℝ | q + ∑ i, w i ^ 2 / 2 ≤ 1} =
      ENNReal.ofReal ((2 : ℝ) ^ ((a : ℝ) / 2)) * volume {w : Fin a → ℝ | q + ∑ i, w i ^ 2 ≤ 1} := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have h := Measure.addHaar_preimage_smul (volume : Measure (Fin a → ℝ)) (r := (Real.sqrt 2)⁻¹)
    (inv_ne_zero h2.ne') {w : Fin a → ℝ | q + ∑ i, w i ^ 2 ≤ 1}
  have e1 : |(((Real.sqrt 2)⁻¹) ^ Module.finrank ℝ (Fin a → ℝ))⁻¹| = (2 : ℝ) ^ ((a : ℝ) / 2) := by
    rw [Module.finrank_fin_fun, inv_pow, inv_inv, abs_of_pos (pow_pos h2 _), Real.sqrt_eq_rpow,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1; ring
  rw [e1] at h
  rw [← h]
  congr 1
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Pi.smul_apply, smul_eq_mul, mul_pow, inv_pow,
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  simp only [div_eq_inv_mul]

theorem vol_ell_three (a b : ℕ) :
    volume {p : ((Fin a → ℝ) × (Fin b → ℝ)) × (Fin a → ℝ) |
      ∑ i, p.1.1 i ^ 2 + ∑ i, p.1.2 i ^ 2 + ∑ i, p.2 i ^ 2 / 2 ≤ 1} =
      ENNReal.ofReal ((2 : ℝ) ^ ((a : ℝ) / 2)) * ballVol (2 * a + b) := by
  rw [← vol_ball_three]
  have hm : MeasurableSet {p : ((Fin a → ℝ) × (Fin b → ℝ)) × (Fin a → ℝ) |
      ∑ i, p.1.1 i ^ 2 + ∑ i, p.1.2 i ^ 2 + ∑ i, p.2 i ^ 2 ≤ 1} :=
    measurableSet_le (by fun_prop) measurable_const
  have hm' : MeasurableSet {p : ((Fin a → ℝ) × (Fin b → ℝ)) × (Fin a → ℝ) |
      ∑ i, p.1.1 i ^ 2 + ∑ i, p.1.2 i ^ 2 + ∑ i, p.2 i ^ 2 / 2 ≤ 1} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [Measure.volume_eq_prod, Measure.prod_apply hm, Measure.prod_apply hm',
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun x => ?_
  exact vol_scale a (∑ i, x.1 i ^ 2 + ∑ i, x.2 i ^ 2)

theorem vol_shear {G Z : Type} [MeasurableSpace G] [AddCommGroup G] [MeasurableAdd₂ G] [MeasurableSpace Z]
    (μ : Measure G) [μ.IsAddRightInvariant] [SFinite μ] (ν : Measure Z) [SFinite ν] (f : Z → G)
    (hf : Measurable f) (s : Set (G × Z)) (hs : MeasurableSet s) :
    (μ.prod ν) {p | (p.1 + f p.2, p.2) ∈ s} = (μ.prod ν) s := by
  have hm : MeasurableSet {p : G × Z | (p.1 + f p.2, p.2) ∈ s} :=
    (show Measurable fun p : G × Z => (p.1 + f p.2, p.2) by fun_prop) hs
  rw [Measure.prod_apply_symm hm, Measure.prod_apply_symm hs]
  refine lintegral_congr fun z => ?_
  exact measure_preimage_add_right μ (f z) ((fun x => (x, z)) ⁻¹' s)

theorem volume_sheared_balls (a b c : ℕ) (ι : (Fin c → ℝ) →ₗ[ℝ] (Fin b → ℝ)) :
    volume {v : (Fin a → ℝ) × (Fin b → ℝ) × ((Fin a → ℝ) × (Fin c → ℝ)) |
      ∑ i, (v.1 i + v.2.2.1 i / Real.sqrt 2) ^ 2 + ∑ i, (v.2.1 i + ι v.2.2.2 i) ^ 2 +
        ∑ i, v.2.2.1 i ^ 2 / 2 ≤ 1 ∧ ∑ i, v.2.2.2 i ^ 2 ≤ 1} =
      ENNReal.ofReal ((2 : ℝ) ^ ((a : ℝ) / 2)) * ballVol (2 * a + b) * ballVol c := by
  have hι : Continuous ι := ι.continuous_of_finiteDimensional
  have hS : MeasurableSet {v : (Fin a → ℝ) × (Fin b → ℝ) × ((Fin a → ℝ) × (Fin c → ℝ)) |
      ∑ i, (v.1 i + v.2.2.1 i / Real.sqrt 2) ^ 2 + ∑ i, (v.2.1 i + ι v.2.2.2 i) ^ 2 +
        ∑ i, v.2.2.1 i ^ 2 / 2 ≤ 1 ∧ ∑ i, v.2.2.2 i ^ 2 ≤ 1} := by
    rw [Set.setOf_and]
    exact ((isClosed_le (by fun_prop) continuous_const).inter
      (isClosed_le (by fun_prop) continuous_const)).measurableSet
  have hs : MeasurableSet {v : ((Fin a → ℝ) × (Fin b → ℝ)) × ((Fin a → ℝ) × (Fin c → ℝ)) |
      ∑ i, v.1.1 i ^ 2 + ∑ i, v.1.2 i ^ 2 + ∑ i, v.2.1 i ^ 2 / 2 ≤ 1 ∧ ∑ i, v.2.2 i ^ 2 ≤ 1} := by
    rw [Set.setOf_and]
    exact ((isClosed_le (by fun_prop) continuous_const).inter
      (isClosed_le (by fun_prop) continuous_const)).measurableSet
  have h1 := (volume_preserving_prodAssoc (α₁ := Fin a → ℝ) (β₁ := Fin b → ℝ)
    (γ₁ := (Fin a → ℝ) × (Fin c → ℝ))).measure_preimage hS.nullMeasurableSet
  have h2 := vol_shear ((volume : Measure (Fin a → ℝ)).prod (volume : Measure (Fin b → ℝ)))
    (volume : Measure ((Fin a → ℝ) × (Fin c → ℝ)))
    (fun z => ((fun i => z.1 i / Real.sqrt 2), ι z.2)) (Continuous.measurable (by fun_prop)) _ hs
  have h3 := (volume_preserving_prodAssoc (α₁ := (Fin a → ℝ) × (Fin b → ℝ)) (β₁ := Fin a → ℝ)
    (γ₁ := Fin c → ℝ)).measure_preimage hs.nullMeasurableSet
  rw [← h1]
  refine (h2.trans h3.symm).trans ?_
  rw [← vol_ell_three, ← vol_ball_type (Fin c) c (Fintype.card_fin c), ← Measure.prod_prod]
  rfl

end GlobalTheory.IwConst.Shear
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst.FlagTrace

variable {n a : ℕ} {ε : Fin n → Bool} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}

theorem mem_lowers {X : Matrix (Fin n) (Fin n) ℂ} : X ∈ lowers ε W ↔
    ((∀ i : Fin a, ∀ y ∈ W i.succ, X *ᵥ y ∈ W i.castSucc) ∧
      ∀ y ∈ perp ε (W (Fin.last a)), X *ᵥ y ∈ W (Fin.last a)) ∧
      ∀ i : Fin a, ∀ y ∈ perp ε (W i.castSucc), X *ᵥ y ∈ perp ε (W i.succ) := by
  simp only [lowers, Submodule.mem_inf, Submodule.mem_iInf, mem_into]

theorem mem_keeps {X : Matrix (Fin n) (Fin n) ℂ} : X ∈ keeps ε W ↔
    (∀ i, ∀ y ∈ W i, X *ᵥ y ∈ W i) ∧ ∀ i, ∀ y ∈ perp ε (W i), X *ᵥ y ∈ perp ε (W i) := by
  simp only [keeps, Submodule.mem_inf, Submodule.mem_iInf, mem_into]

theorem perp_anti {V V' : Submodule ℂ (Fin n → ℂ)} (h : V ≤ V') : perp ε V' ≤ perp ε V :=
  fun _ hy x hx => hy x (h hx)

theorem mul_mem_lowers {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lowers ε W) (hY : Y ∈ keeps ε W) :
    X * Y ∈ lowers ε W := by
  rw [mem_lowers] at hX ⊢
  rw [mem_keeps] at hY
  simp only [← Matrix.mulVec_mulVec]
  exact ⟨⟨fun i y hy => hX.1.1 i _ (hY.1 _ y hy), fun y hy => hX.1.2 _ (hY.2 _ y hy)⟩,
    fun i y hy => hX.2 i _ (hY.2 _ y hy)⟩

theorem isNilpotent_of_mem_lowers (h0 : W 0 = ⊥) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lowers ε W) :
    IsNilpotent X := by
  rw [mem_lowers] at hX
  have h1 : ∀ i : Fin (a + 1), ∀ y, X ^ (i : ℕ) *ᵥ y ∈ perp ε (W i) := by
    intro i
    induction i using Fin.induction with
    | zero => intro y x hx; rw [h0, Submodule.mem_bot] at hx; simp [hx]
    | succ i ih =>
      intro y
      rw [Fin.val_succ, pow_succ', ← Matrix.mulVec_mulVec]
      exact hX.2 i _ (ih y)
  have h2 : ∀ i : Fin (a + 1), ∀ y ∈ W i, X ^ (i : ℕ) *ᵥ y = 0 := by
    intro i
    induction i using Fin.induction with
    | zero => intro y hy; rw [h0, Submodule.mem_bot] at hy; simp [hy]
    | succ i ih =>
      intro y hy
      rw [Fin.val_succ, pow_succ, ← Matrix.mulVec_mulVec]
      exact ih _ (hX.1.1 i y hy)
  refine ⟨a + 1 + a, ?_⟩
  refine Matrix.toLin'.injective (LinearMap.ext fun y => ?_)
  rw [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply, pow_add, pow_succ, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec]
  exact h2 (Fin.last a) _ (hX.1.2 _ (h1 (Fin.last a) y))

theorem lowers_le_keeps {j : Fin a → ℕ} (h : IsIsoFlag ε j W) : lowers ε W ≤ keeps ε W := by
  obtain ⟨h0, hm, -, hi⟩ := h
  intro X hX
  rw [mem_lowers] at hX
  rw [mem_keeps]
  refine ⟨fun i => ?_, fun i => ?_⟩
  · induction i using Fin.cases with
    | zero => intro y hy; rw [h0, Submodule.mem_bot] at hy; simp [hy]
    | succ i => exact fun y hy => hm (Fin.castSucc_le_succ i) (hX.1.1 i y hy)
  · induction i using Fin.lastCases with
    | last => exact fun y hy x hx => hi x hx _ (hX.1.2 y hy)
    | cast i => exact fun y hy => perp_anti (hm (Fin.castSucc_le_succ i)) (hX.2 i y hy)

theorem trace_lowers_keeps : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W →
    (∀ X ∈ lowers ε W, ∀ Y ∈ keeps ε W, (X * Y).trace = 0) ∧ lowers ε W ≤ keeps ε W ∧
      (1 : Matrix (Fin n) (Fin n) ℂ) ∈ keeps ε W ∧ ∀ X ∈ keeps ε W, ∀ Y ∈ keeps ε W, X * Y ∈ keeps ε W := by
  intro n ε a j W h
  refine ⟨fun X hX Y hY => ?_, lowers_le_keeps h, ?_, fun X hX Y hY => ?_⟩
  · exact (Matrix.isNilpotent_trace_of_isNilpotent
      (isNilpotent_of_mem_lowers h.1 (mul_mem_lowers hX hY))).eq_zero
  · rw [mem_keeps]; simp
  · rw [mem_keeps] at hX hY ⊢
    simp only [← Matrix.mulVec_mulVec]
    exact ⟨fun i y hy => hX.1 i _ (hY.1 i y hy), fun i y hy => hX.2 i _ (hY.2 i y hy)⟩

end GlobalTheory.IwConst.FlagTrace
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

theorem _root_.GlobalTheory.T.measurePreserving_rearrange_pi_prod_measures : ∀ (V V' V'' : Type) [Fintype V] [Fintype V'] [Fintype V''] (β : V ≃ V') (σ : V ≃ V'') (a : ℕ) (X : Fin a → Type) [∀ i, MeasurableSpace (X i)] (Y : V'' → Type) [∀ w, MeasurableSpace (Y w)] (m : ∀ i, Measure (X i)) [∀ i, SigmaFinite (m i)] (ν : ∀ w, Measure (Y w)) [∀ w, SigmaFinite (ν w)] (b : Fin a → ℝ) (c : V'' → ℝ), (∀ i, 0 ≤ b i) → (∀ w, 0 ≤ c w) → MeasurePreserving (fun (z : (∀ i, V' → X i) × (∀ w, Y w)) (v : V) => ((fun i => z.1 i (β v)), z.2 (σ v))) (((∏ i, ENNReal.ofReal (b i ^ Fintype.card V)) * ENNReal.ofReal (∏ w, c w)) • (Measure.pi fun i => Measure.pi fun _ : V' => m i).prod (Measure.pi ν)) (Measure.pi fun v : V => (Measure.pi fun i => ENNReal.ofReal (b i) • m i).prod (ENNReal.ofReal (c (σ v)) • ν (σ v))) := by
  first | exact @GlobalTheory.LeviIso.measurePreserving_rearrange | exact GlobalTheory.LeviIso.measurePreserving_rearrange | (intros; apply GlobalTheory.LeviIso.measurePreserving_rearrange <;> assumption)
end
