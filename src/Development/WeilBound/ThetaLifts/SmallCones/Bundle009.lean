module

public import Development.WeilBound.ThetaLifts.SmallCones.Bundle005
import Development.WeilBound.ThetaLifts.SmallCones.Bundle002
public import Development.WeilBound.ThetaLifts.SmallCones.KerGeo
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.Bundle001
public import Development.WeilBound.ThetaLifts.SmallCones.ExpAlg
public import Development.WeilBound.ThetaLifts.SmallCones.MatCancel
import Development.WeilBound.ThetaLifts.TowerModels.LeviAd
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.WeilBound.ThetaLifts.CTKernel
import Development.WeilBound.ThetaLifts.TowerModels.Bundle003

@[expose] public section

section

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cA_cA (hσ : IsCMExt F E σ) (x : AE F E) : cA σ (cA σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => simp [cA, cm_conj_conj hσ]
  | add a b ha hb => simp [ha, hb]

theorem chi_conj (hσ : IsCMExt F E σ) {χ : Chr F E} {k : ℕ}
    (h : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ k) (t : (AE F E)ˣ) :
    χ (GlobalTheory.Doubling.conjUnit σ t) = (χ t)⁻¹ := by
  have h1 := h (Units.map (Algebra.norm (AF F) : AE F E →* AF F) t)
  rw [if_pos (Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨t, rfl⟩)), Circle.coe_eq_one,
    show Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) (Units.map (Algebra.norm (AF F) : AE F E →* AF F) t) =
      t * GlobalTheory.Doubling.conjUnit σ t from Units.ext (GlobalTheory.Doubling.algebraMap_norm_eq hσ (R := AF F) t.1), map_mul] at h1
  exact eq_inv_of_mul_eq_one_right h1

theorem conjUnit_val (t : (AE F E)ˣ) : (GlobalTheory.Doubling.conjUnit σ t : (AE F E)ˣ).1 = cA σ t.1 := rfl

section

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E} {M : Model σ X W}
  {om : Rep σ X W} {om₀ : Rep σ X₁ W₁} {H : Plane E n n₁} {H' : Plane E d d₁} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {χX χW : Chr F E}
  {r s r' s' : ℕ} {rX rW : ℝ}

theorem isLevi_inv' {t h₁ p} (h : IsLevi (σ := σ) (W := W) (W₁ := W₁) H' t h₁ p) :
    mat p⁻¹ *ᵥ incV F H'.x = (t⁻¹ : (AE F E)ˣ).1 • incV F H'.x :=
  mat_inv_mulVec p (by rw [Matrix.mulVec_smul, h.1, smul_smul, Units.inv_mul, one_smul])

theorem levi_inv_y {t h₁ p} (h : IsLevi (σ := σ) (W := W) (W₁ := W₁) H' t h₁ p) :
    mat p⁻¹ *ᵥ incV F H'.y = cA σ t.1 • incV F H'.y :=
  mat_inv_mulVec p (by rw [Matrix.mulVec_smul, h.2.1, smul_smul, ← map_mul, Units.mul_inv, map_one, one_smul])

theorem Mix2.levi (h : Mix2 H H' χX χW rX rW om om₀ e) {t g₁ p t' h₁ p'} (h1 : IsLevi H t g₁ p) (h2 : IsLevi H' t' h₁ p') {Φ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) : e (om (p, p') Φ) = ((χW t : ℂ) * (((absE F E t : ℝ) ^ rX : ℝ) : ℂ) *
      ((χX t' : ℂ) * (((absE F E t' : ℝ) ^ rW : ℝ) : ℂ))) • om₀ (g₁, h₁) (e Φ) := by
  simpa using h t g₁ p h1 1 (one_mem _) t' h₁ p' h2 1 (one_mem _) Φ hΦ

theorem Mix2.uni (h : Mix2 H H' χX χW rX rW om om₀ e) {m} (hm : m ∈ unip σ X H) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    e (om (m, 1) Φ) = e Φ := by
  simpa [← Prod.one_eq_mk] using h 1 1 1 (levi_one H) m hm 1 1 1 (levi_one H') 1 (one_mem _) Φ hΦ

theorem rpow_c {a : ℝ} (ha : 0 < a) (x y : ℝ) : ((a ^ x : ℝ) : ℂ) * ((a ^ y : ℝ) : ℂ) = ((a ^ (x + y) : ℝ) : ℂ) := by
  rw [Real.rpow_add ha, Complex.ofReal_mul]

theorem lawsTA (hp : IsPair B M χX χW om r s r' s') (hM : Mix2 H H' χX χW ((d₁ : ℝ) / 2) ((n : ℝ) / 2) om om₀ e)
    (hx : ∀ m ∈ unip σ X H, mat m *ᵥ incV F H.x = incV F H.x) :
    LawsT B M om om₀ H H' e (shiftA H H') (fun l => (χW⁻¹ l : ℂ) * (((absE F E l : ℝ) ^ ((n : ℝ) - 1 - d₁ / 2) : ℝ) : ℂ))
      fun l => l⁻¹ := by
  have hs := fun w Ψ h => rho_mem M hp.base.std w (Φ := Ψ) h
  refine ⟨inv_one, by simp, fun m hm Ψ hΨ => ?_, fun l g₁ p h₁ p' h1 h2 Ψ hΨ => ?_⟩
  · unfold shiftA
    rw [rho_om hp _ _ _ _ _ hΨ, hM.uni hm (hs _ _ hΨ), mat_inv_mulVec m (hx m hm), inv_one, mat_one', Matrix.one_mulVec]
  · unfold shiftA
    rw [rho_om hp _ _ _ _ _ hΨ, hM.levi h1 h2 (hs _ _ hΨ), isLevi_inv' h1, levi_inv_y h2, smul_smul]
    simp only [inv_inv, Units.val_one, map_one, one_smul, Matrix.smul_vecMulVec, NNReal.coe_one, Real.one_rpow, Circle.coe_one,
      Complex.ofReal_one, mul_one, map_inv, MonoidHom.inv_apply]
    congr 1
    have ha := absE_pos (F := F) l
    rw [mul_left_comm, NNReal.coe_inv, rpow_c (inv_pos.2 ha), Real.inv_rpow ha.le, ← Real.rpow_neg ha.le]
    congr 3
    ring

theorem lawsA (hp : IsPair B M χX χW om r s r' s') (hM : Mix2 H H' χX χW ((d₁ : ℝ) / 2) ((n : ℝ) / 2) om om₀ e) {z : ℕ}
    (hz : 2 * n = d + 2 * z) (hd : d = d₁ + 2) (hx : ∀ m ∈ unip σ X H, mat m *ᵥ incV F H.x = incV F H.x) :
    Laws B M om om₀ H H' e (shiftA H H') χW⁻¹ (χX / χW) z fun l => l⁻¹ := by
  have hs := fun w Ψ h => rho_mem M hp.base.std w (Φ := Ψ) h
  have hd' : (d : ℝ) = d₁ + 2 := by exact_mod_cast hd
  have hz' : (2 * n : ℝ) = d + 2 * z := by exact_mod_cast hz
  refine ⟨?_, fun t h₁ p' h2 => ⟨GlobalTheory.Doubling.conjUnit σ t, fun l Ψ hΨ => ?_⟩⟩
  · convert lawsTA hp hM hx using 3 with l
    rw [← Complex.ofReal_pow, ← Real.rpow_natCast]
    congr 2
    linarith
  · unfold shiftA
    rw [rho_om hp _ _ _ _ _ hΨ, hM.levi (levi_one H) h2 (hs _ _ hΨ), levi_inv_y h2, inv_one, mat_one', Matrix.one_mulVec,
      Matrix.vecMulVec_smul, smul_smul, Units.val_mul, conjUnit_val]
    congr 1
    have ha := absE_pos (F := F) t
    simp only [map_one, NNReal.coe_one, Real.one_rpow, Circle.coe_one, Complex.ofReal_one, mul_one, one_mul, MonoidHom.inv_apply,
      chi_conj hp.base.cm hp.resW, inv_inv, GlobalTheory.Doubling.absE_conjUnit, MonoidHom.div_apply, Circle.coe_div]
    rw [← Complex.ofReal_pow, ← Real.rpow_natCast, show (n : ℝ) / 2 = (d - n) / 2 + z by linarith, ← rpow_c ha]
    field_simp

theorem sy_iso (hx : form σ W.J H'.x H'.x = 0) (a b : Fin n → AE F E) :
    sy σ X W (Matrix.vecMulVec a (incV F H'.x)) (Matrix.vecMulVec b (incV F H'.x)) = 0 := by
  have h0 : ∑ j, ∑ l, incV F H'.x j * incM F W.J j l * cA σ (incV F H'.x l) = 0 := by
    have := congrArg (inclR (F := F) (AF F)) hx

    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, map_zero] at this
    simpa [incV, incM, cA, inclR, mul_assoc] using this
  have : hTens (cA σ) (incM F X.J) (incM F W.J) (Matrix.vecMulVec a (incV F H'.x)) (Matrix.vecMulVec b (incV F H'.x)) = 0 := by
    calc _ = ∑ i, ∑ k, a i * incM F X.J i k * cA σ (b k) * ∑ j, ∑ l, incV F H'.x j * incM F W.J j l * cA σ (incV F H'.x l) := by
          simp only [hTens, Matrix.vecMulVec_apply, map_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
      _ = 0 := by simp [h0]
  simp only [sy, symp, this, mul_zero, map_zero]

theorem lawsB {M₀ : Model σ X₁ W₁} (hp : IsPair B M χX χW om r s r' s') (he : IsEv B M M₀ H.ι H'.ι (isoB H H') e)
    (hM : Mix2 H H' χX χW ((d : ℝ) / 2) ((n₁ : ℝ) / 2) om om₀ e) {z : ℕ}
    (hz : d + 2 = 2 * n + 2 * z) (hn : n = n₁ + 2) (hxx : form σ W.J H'.x H'.x = 0)
    (hy : ∀ m ∈ unip σ X H, ∃ (y : Fin n₁ → AE F E) (c : AE F E),
      mat m *ᵥ incV F H.y = incV F H.y + incM F H.ι *ᵥ y + c • incV F H.x) :
    Laws B M om om₀ H H' e (shiftB σ H H') χW (χX / χW) z id := by
  have hs := fun w Ψ h => rho_mem M hp.base.std w (Φ := Ψ) h
  have hz' : (d : ℝ) + 2 = 2 * n + 2 * z := by exact_mod_cast hz
  have hn' : (n : ℝ) = n₁ + 2 := by exact_mod_cast hn
  refine ⟨⟨rfl, by simp, fun m hm Ψ hΨ => ?_, fun l g₁ p h₁ p' h1 h2 Ψ hΨ => ?_⟩,
    fun t h₁ p' h2 => ⟨(GlobalTheory.Doubling.conjUnit σ t)⁻¹, fun l Ψ hΨ => ?_⟩⟩
  · unfold shiftB
    obtain ⟨y, c, hy'⟩ := hy m⁻¹ (inv_mem hm)
    rw [rho_om hp _ _ _ _ _ hΨ, hM.uni hm (hs _ _ hΨ), hy', inv_one, mat_one', Matrix.one_mulVec, Units.val_one, map_one, one_smul,
      one_smul, Matrix.add_vecMulVec, Matrix.add_vecMulVec, add_comm, ← rho_rho_of M.co B.ψ _ _ (by
        rw [← Matrix.add_vecMulVec]; exact sy_iso hxx _ _), he.inv _ (Or.inl ⟨c • incV F H'.x, by
        rw [Matrix.smul_vecMulVec, Matrix.vecMulVec_smul]⟩) _ (hs _ _ hΨ), add_comm, ← rho_rho_of M.co B.ψ _ _ (sy_iso hxx _ _),
      he.inv _ (Or.inr ⟨y, rfl⟩) _ (hs _ _ hΨ)]
  · unfold shiftB
    rw [rho_om hp _ _ _ _ _ hΨ, hM.levi h1 h2 (hs _ _ hΨ), levi_inv_y h1, isLevi_inv' h2, smul_smul]
    simp only [id, inv_one, Units.val_one, map_one, one_smul, Matrix.smul_vecMulVec, NNReal.coe_one, Real.one_rpow, Circle.coe_one,
      Complex.ofReal_one, mul_one]
    congr 1
    have ha := absE_pos (F := F) l
    rw [mul_left_comm, rpow_c ha, ← Complex.ofReal_pow, ← Real.rpow_natCast]
    congr 3
    linarith
  · unfold shiftB
    have hc : cA σ (l * (GlobalTheory.Doubling.conjUnit σ t)⁻¹ : (AE F E)ˣ).1 = cA σ l.1 * (t⁻¹ : (AE F E)ˣ).1 := by
      rw [Units.val_mul, map_mul, ← map_inv, conjUnit_val, cA_cA hp.base.cm]
    rw [rho_om hp _ _ _ _ _ hΨ, hM.levi (levi_one H) h2 (hs _ _ hΨ), isLevi_inv' h2, inv_one, mat_one', Matrix.one_mulVec,
      Matrix.vecMulVec_smul, smul_smul, hc]
    congr 1
    have ha := absE_pos (F := F) t
    simp only [map_one, NNReal.coe_one, Real.one_rpow, Circle.coe_one, Complex.ofReal_one, mul_one, one_mul, map_inv,
      chi_conj hp.base.cm hp.resW, inv_inv, GlobalTheory.Doubling.absE_conjUnit, MonoidHom.div_apply, Circle.coe_div, NNReal.coe_inv]
    rw [← Complex.ofReal_pow, ← Real.rpow_natCast, Real.inv_rpow ha.le, ← Real.rpow_neg ha.le,
      show (n₁ : ℝ) / 2 = (d - n) / 2 + -z by linarith, ← rpow_c ha]
    field_simp

end

end PositivityTheory.ThKCT

end
end

section

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT.Ker

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow PositivityTheory.Mix
open GlobalTheory.Doubling (absE)
open Matrix (vecMulVec)

section Alg

variable {R : Type} [CommRing R] {n k : ℕ} {c : R →+* R} {J : Matrix (Fin n) (Fin n) R} {ε : R} {x y : Fin n → R}
  {ι : Matrix (Fin n) (Fin k) R}

def eich (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) (ε : R) (x v : Fin n → R) (a : R) : Matrix (Fin n) (Fin n) R :=
  1 + ε • vecMulVec (v + a • x) (J *ᵥ fun i => c (x i)) + (-1 : R) • vecMulVec x (J *ᵥ fun i => c (v i))

theorem eich_apply (v : Fin n → R) (a : R) (w) :
    eich c J ε x v a *ᵥ w = w + (ε * bf c J w x) • (v + a • x) + (-bf c J w v) • x := by
  simp only [eich, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, bf, dotProduct_comm w,
    op_smul_eq_smul, smul_smul, neg_one_mul]

variable (h : PlaneOK c J ε x y ι)
include h

theorem eich_alt (z a) : eich c J ε x (ι *ᵥ z) a *ᵥ x = x := by rw [eich_apply, h.xx, h.xi]; module
theorem eich_y (z a) : eich c J ε x (ι *ᵥ z) a *ᵥ y = y + ι *ᵥ z + a • x := by rw [eich_apply, h.yx, h.yi, h.ee]; module
theorem eich_i (z a w) : eich c J ε x (ι *ᵥ z) a *ᵥ (ι *ᵥ w) = ι *ᵥ w + (-bf c J (ι *ᵥ w) (ι *ᵥ z)) • x := by
  rw [eich_apply, h.ix]; module

theorem eich_mul (z a) : eich c J ε x (ι *ᵥ z) a * eich c J ε x (ι *ᵥ (-z)) (-a - bf c J (ι *ᵥ z) (ι *ᵥ z)) = 1 := by
  have e : ι *ᵥ (-z) = (-1 : R) • (ι *ᵥ z) := by rw [Matrix.mulVec_neg, neg_one_smul]
  refine h.ext ?_ ?_ fun w => ?_
  · rw [← Matrix.mulVec_mulVec, eich_alt h, eich_alt h, Matrix.one_mulVec]
  · rw [← Matrix.mulVec_mulVec, eich_y h, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, eich_alt h, eich_y h, eich_i h,
      Matrix.one_mulVec, e, bf_smul_l]
    module
  · rw [← Matrix.mulVec_mulVec, eich_i h, Matrix.mulVec_add, Matrix.mulVec_smul, eich_alt h, eich_i h, Matrix.one_mulVec, e, bf_smul_r,
      map_neg, map_one]
    module

theorem eich_unit (z a) (ha : bf c J (ι *ᵥ z) (ι *ᵥ z) + a + ε * c a = 0) :
    (eich c J ε x (ι *ᵥ z) a)ᵀ * J * (eich c J ε x (ι *ᵥ z) a).map c = J := by
  ext i j
  rw [← bf_single (c := c) (J := _ * J * _), ← bf_mulVec, ← bf_single (c := c) (J := J) i j]
  obtain ⟨s, t, u, e⟩ := h.span (Pi.single i 1)
  obtain ⟨s', t', u', e'⟩ := h.span (Pi.single j 1)
  rw [e, e']
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, eich_alt h, eich_y h, eich_i h, bf_add_l, bf_add_r, bf_smul_l, bf_smul_r, h.xx, h.xy,
    h.yx, h.yy, h.ix, h.iy, h.xi, h.yi, map_neg, h.symm (ι *ᵥ u') (ι *ᵥ z)]
  linear_combination (t * c t') * ha

theorem coef_y {M : Matrix (Fin n) (Fin n) R} (hu : Mᵀ * J * M.map c = J) (hx : M *ᵥ x = x) {s t : R} {z}
    (e : M *ᵥ y = s • x + ι *ᵥ z + t • y) : t = 1 := by
  have e1 : bf c J (M *ᵥ y) (M *ᵥ x) = ε := by rw [bf_mulVec, hu, h.yx]
  rw [hx, e] at e1
  simp only [bf_add_l, bf_smul_l, h.xx, h.ix, h.yx] at e1
  linear_combination ε * e1 - (t - 1) * h.ee

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d n₁ d₁ m : ℕ} {B : Base F E} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
variable {H : Plane E d d₁} {ε : ℤ}

theorem exists_eich (h : PG σ W W₁ H ε) (z : Fin d₁ → AE F E) (a : AE F E)
    (ha : bf (cA σ).toRingHom (incM F W.J) (incM F H.ι *ᵥ z) (incM F H.ι *ᵥ z) + a + ε * cA σ a = 0) :
    ∃ u : unip σ W H, mat u.1⁻¹ = eich (cA σ).toRingHom (incM F W.J) ε (incV F H.x) (incM F H.ι *ᵥ z) a := by
  obtain ⟨g, hg⟩ := PositivityTheory.ThKG.Tow.Levi.exists_UA (σ := σ) (eich_mul h.ad z a) (eich_unit h.ad z a ha)
  refine ⟨⟨g, Fr.mem_unip.2 ⟨hg ▸ eich_alt h.ad z a, fun w => ⟨_, hg ▸ eich_i h.ad z a w⟩⟩⟩⁻¹, ?_⟩
  simpa using hg

theorem unip_y (h : PG σ W W₁ H ε) {u : UA σ W.J} (hu : u ∈ unip σ W H) :
    ∃ (a : AE F E) (z : Fin d₁ → AE F E), mat u *ᵥ incV F H.y = a • incV F H.x + incM F H.ι *ᵥ z + incV F H.y := by
  obtain ⟨s, t, z, e⟩ := h.ad.span (mat u *ᵥ incV F H.y)
  exact ⟨s, z, by rw [e, coef_y h.ad u.2 (Fr.mem_unip.1 hu).1 e, one_smul]⟩

theorem incV_smul (a : E) (x : Fin n → E) : incV F (a • x) = inclR (F := F) (AF F) a • incV F x := funext fun _ => map_mul _ _ _

theorem incV_add (x y : Fin n → E) : incV F (x + y) = incV F x + incV F y := funext fun _ => map_add _ _ _

theorem unip_y_rat (h : PG σ W W₁ H ε) {u : UA σ W.J} (hu : u ∈ unip σ W H) (hr : u ∈ ratU σ W.J) :
    ∃ (a : E) (z : Fin d₁ → E), mat u *ᵥ incV F H.y = incV F (a • H.x) + incV F (H.ι *ᵥ z) + incV F H.y := by
  obtain ⟨D, hD⟩ := Fr.mem_ratU.1 hr
  obtain ⟨s, t, z, e⟩ := h.rat.span (D *ᵥ H.y)
  have e' : mat u *ᵥ incV F H.y = inclR (F := F) (AF F) s • incV F H.x + incM F H.ι *ᵥ incV F z +
      inclR (F := F) (AF F) t • incV F H.y := by
    rw [hD, inc_mulVec, e, incV_add, incV_add, incV_smul, incV_smul, inc_mulVec]
  exact ⟨s, z, by rw [e', coef_y h.ad u.2 (Fr.mem_unip.1 hu).1 e', one_smul, incV_smul, inc_mulVec]⟩

section Mean

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

theorem mean_zero (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {𝓕 : Set G}
    (h : IsFundamentalDomain Γ 𝓕 μ) {f : G → ℂ} (hl : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) {g : G} {c : ℂ} (hc : c ≠ 1)
    (hr : ∀ x, f (x * g) = c * f x) : ∫ x in 𝓕, f x ∂μ = 0 := by
  have hm : MeasurePreserving (fun x => x * g) μ μ := measurePreserving_mul_right μ g
  have h2 : IsFundamentalDomain Γ ((fun x => x * g) ⁻¹' 𝓕) μ :=
    h.preimage_of_equiv hm.quasiMeasurePreserving (e := id) Function.bijective_id fun γ x => mul_assoc _ _ _
  have e1 := hm.setIntegral_preimage_emb (MeasurableEquiv.mulRight g).measurableEmbedding f 𝓕
  have e2 := h2.setIntegral_eq h (f := f) fun γ x => hl γ.1 γ.2 x
  simp only [hr, integral_const_mul, e2] at e1
  have : (c - 1) * ∫ x in 𝓕, f x ∂μ = 0 := by rw [sub_mul, e1, one_mul, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hc)


omit [Group G] [IsTopologicalGroup G] in
theorem mean_hasSum {ι : Type} [Countable ι] (μ : Measure G) {𝓕 : Set G} (h1 : μ 𝓕 = 1) {f : ι → G → ℂ} (hf : ∀ i, Continuous (f i))
    {b : ι → ℝ} (hb : Summable b) (hfb : ∀ i x, ‖f i x‖ ≤ b i) {s : G → ℂ} (hs : ∀ x, HasSum (fun i => f i x) (s x)) :
    HasSum (fun i => ∫ x in 𝓕, f i x ∂μ) (∫ x in 𝓕, s x ∂μ) := by
  haveI : IsProbabilityMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]⟩
  have hi : ∀ i, Integrable (f i) (μ.restrict 𝓕) := fun i =>
    Integrable.of_bound (hf i).aestronglyMeasurable (b i) (Eventually.of_forall (hfb i))
  have := hasSum_integral_of_summable_integral_norm hi (hb.of_nonneg_of_le (fun i => integral_nonneg fun _ => norm_nonneg _) fun i => by
    simpa using integral_mono (hi i).norm (integrable_const (b i)) (hfb i))
  simpa only [(hs _).tsum_eq] using this

end Mean

theorem psi_rat {ψ : AddChar (AF F) ℂ} (h : IsStd ψ) (x y : Matrix (Fin n) (Fin d) E) :
    ψ (-(⅟(2 : AF F) * sy σ X W (incM F x) (incM F y))) = 1 := by
  rw [sy_inc, show ⅟(2 : AF F) = algebraMap F (AF F) (2⁻¹ : F) from
    invOf_eq_right_inv (by rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]; norm_num), ← map_mul, ← map_neg, h.2.1]

theorem half_sy (hB : B.IsGood σ) {x y : Ten F E n d} {a : AF F}
    (h : hTens (cA σ) (incM F X.J) (incM F W.J) x y = algebraMap (AF F) (AE F E) a) : -(⅟(2 : AF F) * sy σ X W x y) = a := by
  have e : Algebra.trace (AF F) (AE F E) 1 = 2 := by
    rw [← map_one (inclR (F := F) (E := E) (AF F)), tr_inc, ← map_one (algebraMap F E), Algebra.trace_algebraMap, hB.cm.2.2.1]
    simp [map_ofNat]
  rw [sy, symp, h, neg_one_mul, map_neg, Algebra.algebraMap_eq_smul_one, map_smul, e, smul_eq_mul, mul_neg, neg_neg, mul_comm a,
    invOf_mul_cancel_left]

variable {M : Model σ X W} {M₁ : Model σ X₁ W₁} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {ι : Matrix (Fin n) (Fin n₁) E}
  {ι' : Matrix (Fin d) (Fin d₁) E} {I : Set (Ten F E n d)}

theorem rho_split (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (a b : Ten F E n d) (Φ) :
    M.co.rho ψ (a + b) Φ = ψ (-(⅟(2 : AF F) * sy σ X W a b)) • M.co.rho ψ a (M.co.rho ψ b Φ) := by
  rw [rho_rho, smul_smul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_smul]

theorem ev_I (h : IsStd B.ψ) (he : IsEv B M M₁ ι ι' I e) {a} (ha : a ∈ I) (b) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    e (M.co.rho B.ψ (a + b) Φ) = B.ψ (-(⅟(2 : AF F) * sy σ X W a b)) • e (M.co.rho B.ψ b Φ) := by
  rw [rho_split, map_smul, he.inv a ha _ (rho_mem M h b hΦ)]

theorem ev_mid (h : IsStd B.ψ) (he : IsEv B M M₁ ι ι' I e) (w : Ten F E n₁ d₁) (b) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    e (M.co.rho B.ψ (incM F ι * w * (incM F ι')ᵀ + b) Φ) =
      B.ψ (-(⅟(2 : AF F) * sy σ X W (incM F ι * w * (incM F ι')ᵀ) b)) • M₁.co.rho B.ψ w (e (M.co.rho B.ψ b Φ)) := by
  rw [rho_split, map_smul, he.Heisenberg₂ w _ (rho_mem M h b hΦ)]

theorem theta_rho_rat (h : IsStd B.ψ) (hM : M.IsGood B.ψ) (x : Matrix (Fin n) (Fin d) E) (Φ) :
    thetaSum F (M.co.rho B.ψ (incM F x) Φ) = thetaSum F Φ := by
  obtain ⟨a, b, hab⟩ := hM.rat x
  rw [Darboux.rho, hab, theta_schr_rat h]

theorem theta_smul {κ : Type} (c : ℂ) (Φ : (κ → AF F) → ℂ) : thetaSum F (c • Φ) = c * thetaSum F Φ := by
  simp only [thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]

variable {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

theorem om_mem (hp : IsPair B M χX χW om r s r' s') (x) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) : om x Φ ∈ schA F _ :=
  (IsUWeilPair.isUSplitting hp.weil).pres x Φ hΦ

theorem om_om (om : Rep σ X W) (x y) (Φ) : om x (om y Φ) = om (x * y) Φ := by rw [map_mul]; rfl

theorem om_rho (hp : IsPair B M χX χW om r s r' s') (g h) (U : Ten F E n d) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    om (g, h) (M.co.rho B.ψ U Φ) = M.co.rho B.ψ (mat g * U * (mat h)ᵀ) (om (g, h) Φ) :=
  (IsUWeilPair.isUSplitting hp.weil).impl (g, h) U Φ hΦ

theorem rho_om (hp : IsPair B M χX χW om r s r' s') (h) (U : Ten F E n d) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    M.co.rho B.ψ U (om (1, h) Φ) = om (1, h) (M.co.rho B.ψ (U * (mat h⁻¹)ᵀ) Φ) := by
  rw [om_rho hp _ _ _ hΦ, Fr.mat_one, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Fr.mat_mul, mul_inv_cancel,
    Fr.mat_one, Matrix.transpose_one, Matrix.mul_one]

end PositivityTheory.ThKCT.Ker

end
end
