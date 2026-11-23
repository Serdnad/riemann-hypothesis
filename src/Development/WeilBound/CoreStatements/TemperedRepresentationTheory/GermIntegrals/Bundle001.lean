module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.StepSt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle032
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle040
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002

@[expose] public section

section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel PositivityTheory.Tls2.Ming3

namespace PositivityTheory.Tls2.Ming3.RkX

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_ne_zero_of_near_one {j : ℕ} (A : Matrix (Fin j) (Fin j) k)
    (hA : ∀ i l, valuation k (A i l - (1 : Matrix (Fin j) (Fin j) k) i l) < 1) : A.det ≠ 0 := by
  have hint : ∀ i l, A i l ∈ 𝒪[k] := by
    intro i l
    have h1 : valuation k ((1 : Matrix (Fin j) (Fin j) k) i l) ≤ 1 := by
      by_cases h : i = l
      · subst h; simp
      · simp [Matrix.one_apply_ne h]
    have : A i l = (A i l - (1 : Matrix (Fin j) (Fin j) k) i l) + (1 : Matrix (Fin j) (Fin j) k) i l := by ring
    show valuation k (A i l) ≤ 1
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le (hA i l).le h1)
  let y : Matrix (Fin j) (Fin j) 𝒪[k] := Matrix.of fun i l => ⟨A i l, hint i l⟩
  have hy : (algebraMap 𝒪[k] k).mapMatrix y = A := by
    ext i l; rfl
  have hres : (IsLocalRing.residue 𝒪[k]).mapMatrix y = 1 := by
    ext i l
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [show (1 : Matrix (Fin j) (Fin j) (IsLocalRing.ResidueField 𝒪[k])) i l
        = IsLocalRing.residue 𝒪[k] ((1 : Matrix (Fin j) (Fin j) 𝒪[k]) i l) by
      by_cases h : i = l
      · subst h; simp
      · simp [Matrix.one_apply_ne h]]
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
    have e : algebraMap 𝒪[k] k (y i l - (1 : Matrix (Fin j) (Fin j) 𝒪[k]) i l)
        = A i l - (1 : Matrix (Fin j) (Fin j) k) i l := by
      by_cases h : i = l
      · subst h; simp [y]; rfl
      · simp [y, Matrix.one_apply_ne h]; rfl
    rw [e]
    exact (hA i l).ne
  have hdet : IsLocalRing.residue 𝒪[k] y.det = 1 := by
    rw [RingHom.map_det, hres, Matrix.det_one]
  intro h0
  have : y.det = 0 := by
    apply Subtype.ext
    have := congrArg (fun M => M.det) hy
    rw [← RingHom.map_det] at this
    rw [← this] at h0
    exact h0
  rw [this, map_zero] at hdet
  exact zero_ne_one hdet

end PositivityTheory.Tls2.Ming3.RkX

namespace PositivityTheory.Tls2.Ming3

theorem rk : RkSt := by
  intro k _ _ _ _ n r j hjn hjr c hc x hx
  let A : Matrix (Fin j) (Fin j) k := x.submatrix (Fin.castLE hjn) (Fin.castLE hjr)
  have hA : ∀ i l, valuation k (A i l - (1 : Matrix (Fin j) (Fin j) k) i l) < 1 := by
    intro i l
    have h := hx (Fin.castLE hjn i) (Fin.castLE hjr l)
    have e : idem k r n j (Fin.castLE hjn i) (Fin.castLE hjr l) = (1 : Matrix (Fin j) (Fin j) k) i l := by
      show (if (i : ℕ) = l ∧ (l : ℕ) < j then (1 : k) else 0) = _
      by_cases h : i = l
      · subst h; simp
      · have h' : (i : ℕ) ≠ l := fun e => h (Fin.ext e)
        simp [Matrix.one_apply_ne h, h']
    rw [e] at h
    exact h.trans_lt hc
  have hdet := RkX.det_ne_zero_of_near_one A hA
  have h1 : A.rank = j := by
    rw [Matrix.rank_of_isUnit A ((Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 hdet))]
    simp
  calc j = A.rank := h1.symm
    _ ≤ x.rank := Matrix.rank_submatrix_le x _ _

end PositivityTheory.Tls2.Ming3
end

section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel PositivityTheory.Tls2.Ming3
open scoped TensorProduct

noncomputable section

namespace PositivityTheory.Tls2.Ming3.FrobX

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r t : ℕ} {μ : kˣ →* ℂˣ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (GL (Fin r) k) V} {π : Representation ℂ (GL (Fin (r + t)) k) W}

abbrev lrep (t : ℕ) (μ : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin r) k) V) :
    Representation ℂ (Levi k (Two (Fin r) (Fin t))) (V ⊗[ℂ] ℂ) :=
  (extTensor σ (detRep (Fin t) μ)).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem lrep_tmul (g : Levi k (Two (Fin r) (Fin t))) (v : V) :
    lrep t μ σ g (v ⊗ₜ[ℂ] (1 : ℂ)) =
      (μ (Matrix.GeneralLinearGroup.det (g true : GL (Fin t) k)) : ℂ) •
        (σ (g false : GL (Fin r) k) v ⊗ₜ[ℂ] (1 : ℂ)) := by
  change σ (g false) v ⊗ₜ[ℂ] ((μ (Matrix.GeneralLinearGroup.det (g true : GL (Fin t) k)) : ℂ) • (1 : ℂ)) = _
  rw [TensorProduct.tmul_smul]

def fn (π : Representation ℂ (GL (Fin (r + t)) k) W) (ev : W →ₗ[ℂ] V) (w : W) :
    GL (Fin (r + t)) k → V ⊗[ℂ] ℂ :=
  fun h => ev (π h w) ⊗ₜ[ℂ] (1 : ℂ)

theorem fn_law {ev : W →ₗ[ℂ] V} (hl : ParLaw μ σ π ev) (w : W)
    (p : parab k (two (stdSum (rfl : r + t = r + t)))) (g : GL (Fin (r + t)) k) :
    fn π ev w (p * g) =
      ((twist (lrep t μ σ) (deltaHalf k (Two (Fin r) (Fin t)))).comp
        (leviProj k (two (stdSum (rfl : r + t = r + t))))) p (fn π ev w g) := by
  rw [MonoidHom.comp_apply, GlobalTheory.SmGL.twist_apply]
  simp only [PositivityTheory.Tls2.Ming3.FrobX.fn]
  rw [PositivityTheory.Tls2.Ming3.FrobX.lrep_tmul, smul_smul, TensorProduct.smul_tmul', map_mul,
    Module.End.mul_apply, hl p (π g w)]

def elt (hπ : IsSmooth π) {ev : W →ₗ[ℂ] V} (hl : ParLaw μ σ π ev) (w : W) :
    IndSp (two (stdSum (rfl : r + t = r + t))) (lrep t μ σ) :=
  ⟨⟨fn π ev w, fun p g => fn_law hl w p g⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset ((hπ w).mem_nhds (by simp)) (by
      intro g hg
      have hg' : π g w = w := hg
      refine Subtype.ext (funext fun x => ?_)
      show fn π ev w (x * g) = fn π ev w x
      simp only [fn, map_mul, Module.End.mul_apply, hg']))⟩

def frobMap (hπ : IsSmooth π) {ev : W →ₗ[ℂ] V} (hl : ParLaw μ σ π ev) :
    π.IntertwiningMap (prod₂ σ (detRep (Fin t) μ)) where
  toFun w := elt hπ hl w
  map_add' w w' := Subtype.ext (Subtype.ext (funext fun h => by
    show ev (π h (w + w')) ⊗ₜ[ℂ] (1 : ℂ) = ev (π h w) ⊗ₜ[ℂ] (1 : ℂ) + ev (π h w') ⊗ₜ[ℂ] (1 : ℂ)
    simp [TensorProduct.add_tmul]))
  map_smul' c w := Subtype.ext (Subtype.ext (funext fun h => by
    show ev (π h (c • w)) ⊗ₜ[ℂ] (1 : ℂ) = c • (ev (π h w) ⊗ₜ[ℂ] (1 : ℂ))
    simp [TensorProduct.smul_tmul']))
  isIntertwining' g := by
    refine LinearMap.ext fun w => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show ev (π x (π g w)) ⊗ₜ[ℂ] (1 : ℂ) = ev (π (x * g) w) ⊗ₜ[ℂ] (1 : ℂ)
    rw [map_mul, Module.End.mul_apply]

end PositivityTheory.Tls2.Ming3.FrobX

namespace PositivityTheory.Tls2.Ming3

theorem frob : FrobSt := by
  intro k _ _ _ _ r t μ V _ _ W _ _ σ π ev hπ hev hl
  refine ⟨PositivityTheory.Tls2.Ming3.FrobX.frobMap hπ hl, fun h => hev ?_⟩
  refine LinearMap.ext fun w => ?_
  have h1 : ev (π 1 w) ⊗ₜ[ℂ] (1 : ℂ) = 0 :=
    congrArg (fun x => x.1.1 (1 : GL (Fin (r + t)) k)) (LinearMap.congr_fun h w)
  rw [map_one, Module.End.one_apply] at h1
  have h2 := congrArg (TensorProduct.rid ℂ V) h1
  rw [TensorProduct.rid_tmul, one_smul, map_zero] at h2
  rw [LinearMap.zero_apply]
  exact h2

end PositivityTheory.Tls2.Ming3
end
end

section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel PositivityTheory.Tls2.Ming3

namespace PositivityTheory.Tls2.Ming3.LawX

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nabs_inv (x : kˣ) : nabs k x⁻¹ = (nabs k x)⁻¹ := by
  have h := nabs_mul' k x⁻¹ x
  rw [inv_mul_cancel, show nabs k 1 = 1 by simp [nabs]] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem inv_natPow_rpow_neg_half_even_eq_pow {A H : ℝ} (hA : 0 < A) (hH : 0 < H) (N r : ℝ) :
    A ^ (N / 2) * H ^ (-r / 2) * ((H⁻¹) ^ (-r) * A ^ (-N)) = A ^ (-N / 2) * H ^ (r / 2) := by
  rw [Real.inv_rpow hH.le, Real.rpow_neg hH.le, inv_inv]
  have e1 : A ^ (-N / 2) = A ^ (N / 2) * A ^ (-N) := by
    rw [← Real.rpow_add hA]; congr 1; ring
  have e2 : H ^ (r / 2) = H ^ (-r / 2) * H ^ r := by
    rw [← Real.rpow_add hH]; congr 1; ring
  rw [e1, e2]; ring

theorem rpow_product_eq_one {A D : ℝ} (hA : 0 < A) (hD : 0 < D) (r t : ℝ) :
    A ^ (-(r + t) / 2) * (A * D) ^ (r / 2) * (A ^ (t / 2) * D ^ (-r / 2)) = 1 := by
  have : A ^ (-(r + t) / 2) * (A * D) ^ (r / 2) * (A ^ (t / 2) * D ^ (-r / 2)) =
      A ^ (-(r + t) / 2 + r / 2 + t / 2) * D ^ (r / 2 + -r / 2) := by
    rw [Real.mul_rpow hA.le hD.le, Real.rpow_add hA, Real.rpow_add hA, Real.rpow_add hD]; ring
  rw [this, show -(r + t) / 2 + r / 2 + t / 2 = (0 : ℝ) by ring, show r / 2 + -r / 2 = (0 : ℝ) by ring]
  simp

variable [MeasurableSpace k] [BorelSpace k]

theorem integral_om (hcov : CovSt) (ν : Measure k) (hν : IsUnitVol ν) {r N : ℕ} (μ : kˣ →* ℂˣ)
    (g : GL (Fin r) k) (h : GL (Fin N) k) (Φ : Matrix (Fin N) (Fin r) k → ℂ) :
    ∫ x, om μ g h Φ x ∂volM ν (Fin N) (Fin r) =
      (μ (Matrix.GeneralLinearGroup.det g) : ℂ) * ((μ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) *
        ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(N : ℝ) / 2) : ℝ) : ℂ) *
        ((nabs k (Matrix.GeneralLinearGroup.det h) ^ ((r : ℝ) / 2) : ℝ) : ℂ) *
        ∫ x, Φ x ∂volM ν (Fin N) (Fin r) := by
  simp only [om]
  rw [integral_const_mul, hcov k ν hν N r h⁻¹ g Φ, map_inv, nabs_inv, Fintype.card_fin, Fintype.card_fin]
  have hR := inv_natPow_rpow_neg_half_even_eq_pow (nabs_pos' k (Matrix.GeneralLinearGroup.det g))
    (nabs_pos' k (Matrix.GeneralLinearGroup.det h)) (N : ℝ) (r : ℝ)
  have hR' := congrArg (fun x : ℝ => (x : ℂ)) hR
  set C : ℂ := (μ (Matrix.GeneralLinearGroup.det g) : ℂ) * ((μ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ)
  set I := ∫ x, Φ x ∂volM ν (Fin N) (Fin r)
  simp only [Complex.ofReal_mul] at hR' ⊢
  linear_combination (C * I) * hR'

end PositivityTheory.Tls2.Ming3.LawX

namespace PositivityTheory.Tls2.Ming3

open PositivityTheory.Tls2.Ming3.LawX in
theorem law : BallSt → CovSt → LawSt := by
  intro hball hcov k _ _ _ _ _ _ ν hν r t μ V _ _ W _ _ σ π B hEq ev hG p w
  set a : GL (Fin r) k := leviProj k (two (stdSum (rfl : r + t = r + t))) p false with ha
  set d : GL (Fin t) k := leviProj k (two (stdSum (rfl : r + t = r + t))) p true with hd
  set e := GlobalTheory.GodementJacquet.eMat k r t with he
  refine ((hG _ _).1 ?_).symm
  obtain ⟨c₀, hc₀⟩ := (hG w (ev w)).2 rfl
  have hfe : ((p : GL (Fin (r + t)) k)⁻¹ : GL (Fin (r + t)) k).val * e * a.val = e := by
    rw [Matrix.mul_assoc, he, ha, ← GlobalTheory.GodementJacquet.parab_mul_eMat p, ← Matrix.mul_assoc,
      Units.inv_mul, Matrix.one_mul]
  have hfc : Continuous fun y : Matrix (Fin (r + t)) (Fin r) k =>
      ((p : GL (Fin (r + t)) k)⁻¹ : GL (Fin (r + t)) k).val * y * a.val :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have he0 : e ∈ ballM c₀ e := fun i l => by simp
  have hU : (fun y : Matrix (Fin (r + t)) (Fin r) k =>
      ((p : GL (Fin (r + t)) k)⁻¹ : GL (Fin (r + t)) k).val * y * a.val) ⁻¹' ballM c₀ e ∈ nhds e := by
    refine hfc.continuousAt.preimage_mem_nhds ?_
    rw [hfe]
    exact ((hball k (r + t) r).1 c₀ e).1.mem_nhds he0
  obtain ⟨c, -, hc⟩ := (hball k (r + t) r).2.1 e _ hU
  refine ⟨c, fun Φ' hΦ' => ?_⟩
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : SB (Matrix (Fin (r + t)) (Fin r) k),
      Φ.1 = om μ a⁻¹ ((p : GL (Fin (r + t)) k)⁻¹) Φ'.1 :=
    ⟨⟨_, om_mem_SB μ _ _ Φ'.2⟩, rfl⟩
  have hΦΦ' : (Φ' : Matrix (Fin (r + t)) (Fin r) k → ℂ) = om μ a (p : GL (Fin (r + t)) k) Φ.1 := by
    show Φ'.1 = _
    rw [hΦdef, ← om_mul, mul_inv_cancel, mul_inv_cancel, om_one]
  have hsupp : ∀ x, Φ.1 x ≠ 0 → x ∈ ballM c₀ e := by
    intro x hx
    rw [hΦdef] at hx
    simp only [om, inv_inv] at hx
    have hy := hΦ' _ (right_ne_zero_of_mul hx)
    have h2 := hc hy
    simp only [Set.mem_preimage] at h2
    have h3 : ((p : GL (Fin (r + t)) k)⁻¹ : GL (Fin (r + t)) k).val *
        ((p : GL (Fin (r + t)) k).val * x * (a⁻¹ : GL (Fin r) k).val) * a.val = x := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
        Units.inv_mul, Matrix.mul_one]
    rwa [h3] at h2
  have h1 := hEq a (p : GL (Fin (r + t)) k) Φ Φ' hΦΦ' w
  rw [h1, hc₀ Φ hsupp, map_smul, smul_smul]
  congr 1
  show _ = (∫ x, Φ'.1 x ∂volM ν (Fin (r + t)) (Fin r)) * _
  rw [show Φ'.1 = om μ a (p : GL (Fin (r + t)) k) Φ.1 from hΦΦ', integral_om hcov ν hν μ a _ Φ.1]
  have hl : leviProj k (two (stdSum (rfl : r + t = r + t))) p = leviTwo k (Fin r) (Fin t) (a, d) := by
    funext x
    cases x <;> rfl
  have hdet : Matrix.GeneralLinearGroup.det (p : GL (Fin (r + t)) k) =
      Matrix.GeneralLinearGroup.det a * Matrix.GeneralLinearGroup.det d := by
    rw [det_parab, Fintype.prod_bool, mul_comm]
  have e1 : (absPow k ((t : ℂ) / 2) (Matrix.GeneralLinearGroup.det a) : ℂ) =
      ((nabs k (Matrix.GeneralLinearGroup.det a) ^ ((t : ℝ) / 2) : ℝ) : ℂ) := by
    rw [show ((t : ℂ) / 2) = (((t : ℝ) / 2 : ℝ) : ℂ) by simp]
    exact val_absPow_ofReal k _ _
  have e2 : (absPow k (-(r : ℂ) / 2) (Matrix.GeneralLinearGroup.det d) : ℂ) =
      ((nabs k (Matrix.GeneralLinearGroup.det d) ^ (-(r : ℝ) / 2) : ℝ) : ℂ) := by
    rw [show (-(r : ℂ) / 2) = ((-(r : ℝ) / 2 : ℝ) : ℂ) by simp]
    exact val_absPow_ofReal k _ _
  have hR := rpow_product_eq_one (nabs_pos' k (Matrix.GeneralLinearGroup.det a))
    (nabs_pos' k (Matrix.GeneralLinearGroup.det d)) (r : ℝ) (t : ℝ)
  have hR' := congrArg (fun x : ℝ => (x : ℂ)) hR
  simp only [Complex.ofReal_mul, Complex.ofReal_one] at hR'
  have hn : (μ (Matrix.GeneralLinearGroup.det a) : ℂ) ≠ 0 := Units.ne_zero _
  have hn2 : (μ (Matrix.GeneralLinearGroup.det d) : ℂ) ≠ 0 := Units.ne_zero _
  rw [hl, deltaHalf_two]
  simp only [Units.val_mul, e1, e2, hdet, map_mul, nabs_mul', Fintype.card_fin, Nat.cast_add,
    Units.val_inv_eq_inv_val, mul_inv]
  have hinv := mul_inv_cancel₀ hn
  have hinv2 := mul_inv_cancel₀ hn2
  generalize (μ (Matrix.GeneralLinearGroup.det a) : ℂ) = a' at *
  generalize (μ (Matrix.GeneralLinearGroup.det d) : ℂ) = d' at *
  generalize ∫ x, Φ.1 x ∂volM ν (Fin (r + t)) (Fin r) = I at *
  set x1 : ℂ := ((nabs k (Matrix.GeneralLinearGroup.det a) ^ (-((r : ℝ) + (t : ℝ)) / 2) : ℝ) : ℂ)
  set x2 : ℂ := (((nabs k (Matrix.GeneralLinearGroup.det a) * nabs k (Matrix.GeneralLinearGroup.det d)) ^
    ((r : ℝ) / 2) : ℝ) : ℂ)
  set x3 : ℂ := ((nabs k (Matrix.GeneralLinearGroup.det a) ^ ((t : ℝ) / 2) : ℝ) : ℂ)
  set x4 : ℂ := ((nabs k (Matrix.GeneralLinearGroup.det d) ^ (-(r : ℝ) / 2) : ℝ) : ℂ)
  linear_combination (-I) * hR' + (-I * x1 * x2 * x3 * x4 * d' * d'⁻¹) * hinv + (-I * x1 * x2 * x3 * x4) * hinv2
end PositivityTheory.Tls2.Ming3
end

section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel PositivityTheory.Tls2.Ming3

namespace PositivityTheory.Tls2.Ming3

theorem cov : CovSt := by
  intro k _ _ _ _ _ _ ν hν n r h g Φ
  haveI : ν.IsAddHaarMeasure := hν.1
  rw [GlobalTheory.SplitWeil.integral_comp_mul_mul_volM ν g h Φ]
  simp only [Fintype.card_fin, Complex.real_smul]

end PositivityTheory.Tls2.Ming3
end
