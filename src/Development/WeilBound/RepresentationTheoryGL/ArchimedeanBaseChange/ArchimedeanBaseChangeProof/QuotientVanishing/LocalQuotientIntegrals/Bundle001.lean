module

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetOneAddOfSq
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.OneVanish
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle410
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousConjNilSymm

@[expose] public section

section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open scoped ComplexOrder

namespace PositivityTheory.Rg.BcB.CV.LocalPlacePositivity

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem cV_alg (v : InfinitePlace E) (x : E) : cV v (algebraMap E (Ad E) x) = v.embedding x :=
  pInf_algebraMap x v

open Classical in
theorem cV_embInf (v w : InfinitePlace E) (y : GL (Fin n) ℂ) :
    GeneralLinearGroup.map (cV w) (embInf n v y) = if w = v then y else 1 := by
  ext i j
  change (GeneralLinearGroup.map (pInf E) (embInf n v y)) i j w = _
  unfold embInf
  rw [MonoidHom.comp_apply, pInf_infGL]
  change (MonoidHom.mulSingle (fun _ : InfinitePlace E => GL (Fin n) ℂ) v y w).val i j = _
  by_cases h : w = v
  · subst h
    simp
  · simp [h]

theorem cV_embInf_self (v : InfinitePlace E) (y : GL (Fin n) ℂ) :
    GeneralLinearGroup.map (cV v) (embInf n v y) = y := by
  classical
  rw [cV_embInf, if_pos rfl]

theorem pFin_embInf (v : InfinitePlace E) (y : GL (Fin n) ℂ) :
    GeneralLinearGroup.map (pFin E) (embInf n v y) = 1 := by
  unfold embInf
  exact pFin_infGL _

theorem cW_embInf (w : HeightOneSpectrum (𝓞 E)) (v : InfinitePlace E) (y : GL (Fin n) ℂ) :
    GeneralLinearGroup.map (cW w) (embInf n v y) = 1 := by
  have e : GeneralLinearGroup.map (cW w) (embInf n v y) =
      GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) (embInf n v y)) := rfl
  rw [e, pFin_embInf, map_one]

theorem cV_ratGL (v : InfinitePlace E) (d : GL (Fin n) E) :
    GeneralLinearGroup.map (cV v) (ratGL E n d) = locGL v d := by
  ext i j
  exact pInf_algebraMap (d i j) v

theorem map_inv_val {R : Type} [CommRing R] (f : Ad E →+* R) (x : GA E n) :
    ((x⁻¹ : GA E n).val).map f = ((GeneralLinearGroup.map f x)⁻¹ : GL (Fin n) R).val := by
  rw [← map_inv]; rfl

theorem frame_map_eq {R : Type} [CommRing R] (f : Ad E →+* R) (x y : GA E n)
    (h : GeneralLinearGroup.map f x = GeneralLinearGroup.map f y) {r : ℕ} (M : Matrix (Fin n) (Fin r) E) :
    (frame x M).map f = (frame y M).map f := by
  rw [frame, frame, Matrix.map_mul, Matrix.map_mul, map_inv_val, map_inv_val, h]

theorem frame_map (v : InfinitePlace E) (x : GA E n) {r : ℕ} (M : Matrix (Fin n) (Fin r) E) :
    (frame x M).map (cV v) = ((GeneralLinearGroup.map (cV v) x)⁻¹ : GL (Fin n) ℂ).val * M.map v.embedding := by
  have h : (M.map (algebraMap E (Ad E))).map (cV v) = M.map v.embedding := by
    ext i j
    exact cV_alg v (M i j)
  rw [frame, Matrix.map_mul, h, map_inv_val]

theorem lognInf_eq (v : InfinitePlace E) (x : GA E n) {r : ℕ} (M : Matrix (Fin n) (Fin r) E) :
    lognInf v (frame x M) = ploc (M.map v.embedding) (GeneralLinearGroup.map (cV v) x) := by
  rw [lognInf, frame_map, ploc]

theorem exists_ginv {K : Type} [Field K] {r m : ℕ} (A : Matrix (Fin r) (Fin m) K) :
    ∃ B : Matrix (Fin m) (Fin r) K, A * B * A = A := by
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective A.mulVecLin.rangeRestrict
    (LinearMap.range_rangeRestrict _)
  obtain ⟨h, hh⟩ := LinearMap.exists_extend g
  refine ⟨LinearMap.toMatrix' h, ?_⟩
  apply Matrix.mulVec_injective
  funext z
  have hz : A *ᵥ z ∈ LinearMap.range A.mulVecLin := ⟨z, rfl⟩
  have h1 : h (A *ᵥ z) = g ⟨A *ᵥ z, hz⟩ := LinearMap.congr_fun hh ⟨A *ᵥ z, hz⟩
  have h2 : A *ᵥ g ⟨A *ᵥ z, hz⟩ = A *ᵥ z :=
    congrArg Subtype.val (LinearMap.congr_fun hg ⟨A *ᵥ z, hz⟩)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec, h1, h2]

theorem exists_left (v : InfinitePlace E) (W : Submodule E (Fin n → E)) :
    ∃ L : Matrix (Fin (Module.finrank E W)) (Fin n) ℂ, L * (basisMat W).map v.embedding = 1 := by
  apply _root_.GlobalTheory.CompanionTheory.LocFlagPf.exists_left <;> assumption

theorem gram_re_pos {r : ℕ} (B : Matrix (Fin n) (Fin r) ℂ) (L : Matrix (Fin r) (Fin n) ℂ) (hL : L * B = 1) :
    0 < (Bᴴ * B).det.re := by
  have hps : (Bᴴ * B).PosSemidef := posSemidef_conjTranspose_mul_self B
  have h0 : (Bᴴ * B).det ≠ 0 := by
    intro h
    obtain ⟨w, hw, hw0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    apply hw
    have h1 : B *ᵥ w = 0 := (conjTranspose_mul_self_mulVec_eq_zero B w).1 hw0
    calc w = (L * B) *ᵥ w := by rw [hL, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]
  have hpos : 0 < (Bᴴ * B).det := lt_of_le_of_ne hps.det_nonneg (Ne.symm h0)
  exact (Complex.pos_iff.1 hpos).1

theorem ploc_re_pos (v : InfinitePlace E) (W : Submodule E (Fin n → E)) (g : GL (Fin n) ℂ) :
    0 < ((((g⁻¹ : GL (Fin n) ℂ).val * (basisMat W).map v.embedding)ᴴ *
      ((g⁻¹ : GL (Fin n) ℂ).val * (basisMat W).map v.embedding)).det).re := by
  obtain ⟨L, hL⟩ := exists_left v W
  refine gram_re_pos _ (L * g.val) ?_
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc g.val, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, hL]

theorem ploc_cont (v : InfinitePlace E) (W : Submodule E (Fin n → E)) :
    Continuous (ploc ((basisMat W).map v.embedding)) := by
  have hB : Continuous fun g : GL (Fin n) ℂ => (g⁻¹ : GL (Fin n) ℂ).val * (basisMat W).map v.embedding :=
    Units.continuous_coe_inv.matrix_mul continuous_const
  have hd : Continuous fun g : GL (Fin n) ℂ => ((((g⁻¹ : GL (Fin n) ℂ).val * (basisMat W).map v.embedding)ᴴ *
      ((g⁻¹ : GL (Fin n) ℂ).val * (basisMat W).map v.embedding)).det).re :=
    Complex.continuous_re.comp (hB.matrix_conjTranspose.matrix_mul hB).matrix_det
  exact (hd.log fun g => (ploc_re_pos v W g).ne').congr fun g => rfl

theorem ploc_mul_k {r : ℕ} (M : Matrix (Fin n) (Fin r) ℂ) (x k : GL (Fin n) ℂ) (hk : thC n k = k) :
    ploc M (x * k) = ploc M x := by
  have hk' : ((k⁻¹ : GL (Fin n) ℂ).val)ᴴ = k.val := by
    have h := congrArg Units.val hk
    rw [thetaR_val] at h
    refine Eq.trans ?_ h
    ext i j
    simp [Matrix.conjTranspose_apply]
  have e : ∀ B : Matrix (Fin n) (Fin r) ℂ,
      ((k⁻¹ : GL (Fin n) ℂ).val * B)ᴴ * ((k⁻¹ : GL (Fin n) ℂ).val * B) = Bᴴ * B := fun B => by
    rw [Matrix.conjTranspose_mul, hk', Matrix.mul_assoc, ← Matrix.mul_assoc k.val, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.one_mul]
  unfold ploc
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, e]

theorem ploc_empty {r : ℕ} (M : Matrix (Fin n) (Fin r) ℂ) (hr : r = 0) (g : GL (Fin n) ℂ) : ploc M g = 0 := by
  subst hr
  simp [ploc]

theorem degM_empty {r : ℕ} (x : GA E n) (M : Matrix (Fin n) (Fin r) E) (hr : r = 0) : degM x M = 0 := by
  subst hr
  exact degM_zero x M

theorem deg_embInf (v : InfinitePlace E) (W : Submodule E (Fin n → E)) (g : GL (Fin n) ℂ) (x : GA E n) :
    deg (embInf n v g * x) W + ploc ((basisMat W).map v.embedding) (g * GeneralLinearGroup.map (cV v) x) =
      deg x W + ploc ((basisMat W).map v.embedding) (GeneralLinearGroup.map (cV v) x) := by
  classical
  have hfin : ∀ w, lognFin w (frame (embInf n v g * x) (basisMat W)) = lognFin w (frame x (basisMat W)) :=
    fun w => by
      unfold lognFin
      rw [frame_map_eq (cW w) _ x (by rw [map_mul, cW_embInf, one_mul])]
  have hinf : ∀ w, lognInf w (frame (embInf n v g * x) (basisMat W)) = lognInf w (frame x (basisMat W)) +
      if w = v then ploc ((basisMat W).map v.embedding) (g * GeneralLinearGroup.map (cV v) x) -
        ploc ((basisMat W).map v.embedding) (GeneralLinearGroup.map (cV v) x) else 0 := fun w => by
    by_cases h : w = v
    · subst h
      rw [if_pos rfl, lognInf_eq, lognInf_eq, map_mul, cV_embInf_self]
      ring
    · rw [if_neg h, add_zero]
      unfold lognInf
      rw [frame_map_eq (cV w) _ x (by rw [map_mul, cV_embInf, if_neg h, one_mul])]
  simp only [deg, degM, hfin, hinf, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring

end PositivityTheory.Rg.BcB.CV.LocalPlacePositivity

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 in
theorem PositivityTheory.Rg.BcB.CV.pf_Ploc : PositivityTheory.Rg.BcB.CV.Ploc := by
  intro E _ _ _ n v W
  refine ⟨fun x => LocalPlacePositivity.lognInf_eq v x _, LocalPlacePositivity.ploc_cont v W, fun x k hk => LocalPlacePositivity.ploc_mul_k _ x k hk,
    fun hW => ?_, LocalPlacePositivity.cV_embInf_self v, fun v' hv' g => ?_, fun d => LocalPlacePositivity.cV_ratGL v d,
    fun g x => LocalPlacePositivity.deg_embInf v W g x⟩
  · subst hW
    exact ⟨fun x => LocalPlacePositivity.ploc_empty _ (by simp) x, fun x => LocalPlacePositivity.degM_empty x _ (by simp)⟩
  · classical
    rw [LocalPlacePositivity.cV_embInf, if_neg hv']
end

section

noncomputable section

open MeasureTheory PositivityTheory.Rg.Tf.Loc

namespace PositivityTheory.Rg.BcB.CV.FirstVanishingAlt

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.BcB.CV

theorem twConj_mul_left {n : ℕ} (d t x : GL (Fin n) ℂ) (ht : t ∈ twCent (thC n) d) :
    twConj (thC n) (t * x) d = twConj (thC n) x d := by
  rw [mem_twCent] at ht
  simp only [twConj, map_mul]
  calc (t * x)⁻¹ * d * ((thC n) t * (thC n) x) = x⁻¹ * (t⁻¹ * d * (thC n) t) * (thC n) x := by group
    _ = x⁻¹ * d * (thC n) x := by rw [ht]

theorem sle_refl {m : ℕ} (e : Fin m → SignType) : SLe e e := fun _ _ => rfl

def zr {m : ℕ} (z : (Fin m → SignType) → ℝ) (s : Finset (Fin m → SignType)) : (Fin m → SignType) → ℝ :=
  fun e => if e ∈ s then z e else 0

theorem zr_insert {m : ℕ} (z y : (Fin m → SignType) → ℝ) {s : Finset (Fin m → SignType)} {e : Fin m → SignType}
    (he : e ∉ s) : y + zr z (insert e s) = Function.update (y + zr z s) e (y e + z e) := by
  funext e'
  by_cases h : e' = e
  · subst h; simp [zr]
  · simp [zr, h]

theorem zr_self {m : ℕ} (z y : (Fin m → SignType) → ℝ) {s : Finset (Fin m → SignType)} {e : Fin m → SignType}
    (he : e ∉ s) : y + zr z s = Function.update (y + zr z s) e (y e) := by
  funext e'
  by_cases h : e' = e
  · subst h; simp [zr, he]
  · simp [h]

theorem diff_step {m : ℕ} {V : ((Fin m → SignType) → ℝ) → ℂ} (hV : VP V) (z : (Fin m → SignType) → ℝ)
    (s : Finset (Fin m → SignType)) (e : Fin m → SignType) (he : e ∉ s) (y y' : (Fin m → SignType) → ℝ)
    (hyy : ∀ e', SLe e e' ∨ SLe e' e → y e' = y' e') :
    V (y + zr z (insert e s)) - V (y + zr z s) = V (y' + zr z (insert e s)) - V (y' + zr z s) := by
  have key : ∀ w : (Fin m → SignType) → ℝ, V (w + zr z (insert e s)) - V (w + zr z s) =
      V (Function.update (w + zr z s) e (w e + z e)) - V (Function.update (w + zr z s) e (w e)) := fun w => by
    rw [← zr_insert z w he, ← zr_self z w he]
  have hee : y e = y' e := hyy e (Or.inl (sle_refl e))
  rw [key y, key y', hee]
  exact hV.diff _ _ e _ _ (fun e' h => by simp only [Pi.add_apply, hyy e' h])

theorem good_V {n m : ℕ} [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)] {d : GL (Fin n) ℂ}
    {V : ((Fin m → SignType) → ℝ) → ℂ} {p : GL (Fin n) ℂ → (Fin m → SignType) → ℝ} (hV : VP V) (hL : LocFam d V p)
    (c : (Fin m → SignType) → ℝ) :
    Measurable (fun x => V (p x + c)) ∧ (∀ t ∈ twCent (thC n) d, ∀ x, V (p (t * x) + c) = V (p x + c)) ∧
      ∀ C : Set (GL (Fin n) ℂ), IsCompact C → ∃ B : ℝ, ∀ x ∈ C, ‖V (p x + c)‖ ≤ B := by
  refine ⟨hV.meas.comp (hL.cont.add continuous_const).measurable, fun t ht x => hL.tor t ht x c, fun C hC => ?_⟩
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (f := fun x => p x + c) (hL.cont.add continuous_const).continuousOn
  obtain ⟨B, hB⟩ := hV.bdd M
  refine ⟨B, fun x hx => hB _ fun e => ?_⟩
  have := (norm_le_pi_norm (p x + c) e).trans (hM x hx)
  rwa [Real.norm_eq_abs] at this

end PositivityTheory.Rg.BcB.CV.FirstVanishingAlt

open PositivityTheory.Rg.BcB.CV.FirstVanishingAlt in
theorem PositivityTheory.Rg.BcB.CV.pf_OneVanish : PositivityTheory.Rg.BcB.LocVanish → PositivityTheory.Rg.BcB.D4.LocProper → PositivityTheory.Rg.BcB.CV.LocTor → PositivityTheory.Rg.BcB.CV.QInt → PositivityTheory.Rg.BcB.CV.QAdd → PositivityTheory.Rg.BcB.CV.OneVanish := by
  intro hLV hLP hLT hQI hQA n m _ _ μ _ d ν _ _ f V p z hsep hf hfs hfc hV hL hz0
  obtain ⟨hTc, -, hθc, hlc, hsc⟩ := hLT n d hsep
  have := hlc
  have := hsc
  have htc : Continuous (fun x : GL (Fin n) ℂ => twConj (thC n) x d) := by
    unfold twConj
    exact (continuous_inv.mul continuous_const).mul hθc
  obtain ⟨Bf, hBf⟩ := hf.bounded_above_of_compact_support hfs
  obtain ⟨C', hC', hsub⟩ := hLP n d hsep (tsupport f) hfs
  obtain ⟨A, -, hAI⟩ := hQI (GL (Fin n) ℂ) μ (twCent (thC n) d) ν C' hTc hC'
  have fin : ∀ g : GL (Fin n) ℂ → ℂ, Measurable g → (∀ t ∈ twCent (thC n) d, ∀ x, g (t * x) = g x) →
      (∀ C : Set (GL (Fin n) ℂ), IsCompact C → ∃ B : ℝ, ∀ x ∈ C, ‖g x‖ ≤ B) →
      Measurable (fun x => f (twConj (thC n) x d) * g x) ∧
      quotLIntegral μ (twCent (thC n) d) ν (fun x => ‖f (twConj (thC n) x d) * g x‖ₑ) ≠ ⊤ := by
    intro g hgm hgT hgb
    obtain ⟨Bg, hBg⟩ := hgb C' hC'
    have hm : Measurable (fun x => f (twConj (thC n) x d) * g x) := (hf.comp htc).measurable.mul hgm
    refine ⟨hm, (hAI _ (max Bf 0 * max Bg 0) (mul_nonneg (le_max_right _ _) (le_max_right _ _)) hm ?_ ?_ ?_).1⟩
    · intro t ht x
      rw [twConj_mul_left d t x ht, hgT t ht x]
    · intro x hx
      exact hsub (show twConj (thC n) x d ∈ tsupport f from
        subset_tsupport f (Function.mem_support.2 (left_ne_zero_of_mul hx)))
    · intro x hx
      rw [norm_mul]
      exact mul_le_mul ((hBf _).trans (le_max_left _ _)) ((hBg x hx).trans (le_max_left _ _)) (norm_nonneg _)
        (le_max_right _ _)
  have goodsub : ∀ c c' : (Fin m → SignType) → ℝ, Measurable (fun x => V (p x + c) - V (p x + c')) ∧
      (∀ t ∈ twCent (thC n) d, ∀ x, V (p (t * x) + c) - V (p (t * x) + c') = V (p x + c) - V (p x + c')) ∧
      ∀ C : Set (GL (Fin n) ℂ), IsCompact C → ∃ B : ℝ, ∀ x ∈ C, ‖V (p x + c) - V (p x + c')‖ ≤ B := by
    intro c c'
    obtain ⟨h1, h2, h3⟩ := good_V hV hL c
    obtain ⟨h1', h2', h3'⟩ := good_V hV hL c'
    refine ⟨h1.sub h1', fun t ht x => by rw [h2 t ht x, h2' t ht x], fun C hC => ?_⟩
    obtain ⟨B, hB⟩ := h3 C hC
    obtain ⟨B', hB'⟩ := h3' C hC
    exact ⟨B + B', fun x hx => (norm_sub_le _ _).trans (add_le_add (hB x hx) (hB' x hx))⟩
  have h0int : quotIntegral μ (twCent (thC n) d) ν (fun _ => (0 : ℂ)) = 0 := by
    simpa using (hQA (GL (Fin n) ℂ) μ (twCent (thC n) d) ν).2.2 0 (fun _ => 0)
  have main : ∀ s : Finset (Fin m → SignType), quotIntegral μ (twCent (thC n) d) ν
      (fun x => f (twConj (thC n) x d) * (V (p x + zr z s) - V (p x + 0))) = 0 := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · have h0 : zr z ∅ = 0 := by funext e; simp [zr]
      simp only [h0, sub_self, mul_zero]
      exact h0int
    · intro e s he ih
      have hFi := fin _ (goodsub (zr z (insert e s)) 0).1 (goodsub _ 0).2.1 (goodsub _ 0).2.2
      have hFs := fin _ (goodsub (zr z s) 0).1 (goodsub _ 0).2.1 (goodsub _ 0).2.2
      have hdiff : quotIntegral μ (twCent (thC n) d) ν
          (fun x => f (twConj (thC n) x d) * (V (p x + zr z (insert e s)) - V (p x + zr z s))) = 0 := by
        by_cases he0 : e = 0
        · subst he0
          have hzz : zr z (insert 0 s) = zr z s := by
            funext e'
            by_cases h : e' = 0
            · subst h; simp [zr, he, hz0]
            · simp [zr, h]
          simp only [hzz, sub_self, mul_zero]
          exact h0int
        · obtain ⟨W₁, W₂, ⟨hW1, hW12, hp1, hp2⟩, hnil⟩ := hL.nil e he0
          obtain ⟨hm, hTi, hb⟩ := goodsub (zr z (insert e s)) (zr z s)
          exact hLV n μ f (fun x => V (p x + zr z (insert e s)) - V (p x + zr z s)) d ν W₁ W₂ hf hfs hfc hsep
            hW1 hW12 hp1 hp2 hm hb (fun x k hk => by simp only [hL.cpt x k hk]) hTi
            (fun u hu x => diff_step hV z s e he _ _ (fun e' h => hnil u hu x e' h))
      have key : quotIntegral μ (twCent (thC n) d) ν
          (fun x => f (twConj (thC n) x d) * (V (p x + zr z (insert e s)) - V (p x + 0)) -
            f (twConj (thC n) x d) * (V (p x + zr z s) - V (p x + 0))) =
          quotIntegral μ (twCent (thC n) d) ν (fun x => f (twConj (thC n) x d) * (V (p x + zr z (insert e s)) - V (p x + 0))) -
          quotIntegral μ (twCent (thC n) d) ν (fun x => f (twConj (thC n) x d) * (V (p x + zr z s) - V (p x + 0))) :=
        (hQA (GL (Fin n) ℂ) μ (twCent (thC n) d) ν).2.1 _ _ hFi.1 hFs.1 hFi.2 hFs.2
      have hfun : (fun x => f (twConj (thC n) x d) * (V (p x + zr z (insert e s)) - V (p x + 0)) -
            f (twConj (thC n) x d) * (V (p x + zr z s) - V (p x + 0))) =
          fun x => f (twConj (thC n) x d) * (V (p x + zr z (insert e s)) - V (p x + zr z s)) := by
        funext x; ring
      rw [hfun, hdiff, ih, sub_zero] at key
      exact key.symm
  have hu : zr z Finset.univ = z := by funext e; simp [zr]
  have := main Finset.univ
  rw [hu] at this
  simpa using this
end
end

section

noncomputable section

open MeasureTheory PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace PositivityTheory.Rg.BcB.CV

namespace QuotientIntegral

theorem enorm_ofReal_toReal_le' (r : ℝ≥0∞) : ‖((r.toReal : ℝ) : ℂ)‖ₑ ≤ r := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_toReal_le

theorem integrable_mul {G : Type*} [MeasurableSpace G] {μ : Measure G} {F : G → ℂ}
    {ρ : G → ℝ≥0∞} (hF : Measurable F) (hρ : Measurable ρ) (h : ∫⁻ g, ‖F g‖ₑ * ρ g ∂μ ≠ ⊤) :
    Integrable (fun g => F g * ((ρ g).toReal : ℂ)) μ := by
  refine ⟨(hF.mul (Complex.measurable_ofReal.comp hρ.ennreal_toReal)).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun g => ?_) h.lt_top
  rw [enorm_mul]
  gcongr
  exact enorm_ofReal_toReal_le' _

end QuotientIntegral

theorem pf_QAdd : QAdd := by
  intro G _ _ μ T ν
  classical
  by_cases hex : ∃ ρ, IsQuotNormaliser T ν ρ
  · have hL : ∀ F : G → ℂ, quotLIntegral μ T ν (fun x => ‖F x‖ₑ) =
        ∫⁻ g, ‖F g‖ₑ * hex.choose g ∂μ := fun F => by rw [quotLIntegral, dite_eq_left hex]
    have hI : ∀ F : G → ℂ, quotIntegral μ T ν F =
        ∫ g, F g * ((hex.choose g).toReal : ℂ) ∂μ := fun F => by rw [quotIntegral, dite_eq_left hex]
    have hint : ∀ F : G → ℂ, Measurable F → quotLIntegral μ T ν (fun x => ‖F x‖ₑ) ≠ ⊤ →
        Integrable (fun g => F g * ((hex.choose g).toReal : ℂ)) μ := fun F hF h =>
      QuotientIntegral.integrable_mul hF hex.choose_spec.1 (by rwa [hL] at h)
    refine ⟨fun ι s F hF => ?_, fun F F' hF hF' h h' => ?_, fun c F => ?_⟩
    · simp only [hI, Finset.sum_mul]
      exact integral_finsetSum s fun i hi => hint _ (hF i hi).1 (hF i hi).2
    · simp only [hI, sub_mul]
      exact integral_sub (hint _ hF h) (hint _ hF' h')
    · simp only [hI, mul_assoc]
      exact integral_const_mul c _
  · refine ⟨fun _ _ _ _ => ?_, fun _ _ _ _ _ _ => ?_, fun _ _ => ?_⟩ <;>
      simp [quotIntegral, hex]

end PositivityTheory.Rg.BcB.CV
end
end

section

noncomputable section

open Matrix PositivityTheory.Rg.Tf.Loc

namespace PositivityTheory.Rg.BcB.CV.LocalTorus

theorem comm (n : ℕ) (d : GL (Fin n) ℂ) (hs : (d * thC n d).val.charpoly.Separable)
    (s : GL (Fin n) ℂ) (hs' : s ∈ twCent (thC n) d) (t : GL (Fin n) ℂ) (ht : t ∈ twCent (thC n) d) :
    s * t = t * s := by
  have hθθ : ∀ g : GL (Fin n) ℂ, thC n (thC n g) = g := by
    intro g
    apply Units.ext
    show ((((thC n g)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))ᵀ = (g : Matrix (Fin n) (Fin n) ℂ)
    have e : (((thC n g)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
        ((g : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))ᵀ := rfl
    rw [e]
    ext i j
    simp [Matrix.map_apply, Matrix.transpose_apply]
  have key : ∀ x ∈ twCent (thC n) d,
      Commute ((d * thC n d : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) (x : Matrix (Fin n) (Fin n) ℂ) := by
    intro x hx
    have h1 : x⁻¹ * d * thC n x = d := hx
    have h2 : d * thC n x = x * d := by
      calc d * thC n x = x * (x⁻¹ * d * thC n x) := by group
        _ = x * d := by rw [h1]
    have h3 : thC n d * x = thC n x * thC n d := by
      have h4 := congrArg (thC n) h2
      rw [map_mul, map_mul, hθθ] at h4
      exact h4
    apply Commute.units_val
    show (d * thC n d) * x = x * (d * thC n d)
    rw [mul_assoc, h3, ← mul_assoc, h2, mul_assoc]
  have hc := GlobalTheory.BCT.CentComm.commute_of_commute_separable hs (key s hs') (key t ht)
  exact Units.ext (by simpa using hc.eq)

end PositivityTheory.Rg.BcB.CV.LocalTorus

theorem PositivityTheory.Rg.BcB.CV.pf_LocTor : PositivityTheory.Rg.BcB.CV.LocTor := by
  intro n d hs
  exact ⟨GlobalTheory.CompanionTheory.LocVan.isClosed_twCent d, PositivityTheory.Rg.BcB.CV.LocalTorus.comm n d hs,
    GlobalTheory.CompanionTheory.LocVan.continuous_thC, GlobalTheory.CompanionTheory.LocVan.locallyCompact_GL n, GlobalTheory.CompanionTheory.LocVan.secondCountable_GL n⟩

end
end
