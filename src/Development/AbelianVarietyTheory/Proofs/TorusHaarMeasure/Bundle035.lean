module

public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle044
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle005
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle022
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle034
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle008
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle006
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle009
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle014
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Development.AbelianVarietyTheory.Definitions.UpperBounds.PhRec
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BigRec

namespace GlobalTheory.BigRec

theorem adjoin_div_le {K F κ : Type} [Field K] [Field F] [Algebra K F] (a : κ → F) (p q : κ) (hq : a q ≠ 0) :
    IntermediateField.adjoin K (Set.range fun k => a k / a p) ≤
      IntermediateField.adjoin K (Set.range fun k => a k / a q) := by
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro _ ⟨k, rfl⟩
  have hk : a k / a q ∈ IntermediateField.adjoin K (Set.range fun k => a k / a q) :=
    IntermediateField.subset_adjoin K _ ⟨k, rfl⟩
  have hp : a p / a q ∈ IntermediateField.adjoin K (Set.range fun k => a k / a q) :=
    IntermediateField.subset_adjoin K _ ⟨p, rfl⟩
  have hkp := div_mem hk hp
  rwa [div_div_div_cancel_right₀ hq] at hkp

theorem ratio_single {F Γ : Type} [Field F] [AddCommGroup Γ] (g : Γ) (a b : F) (hb : b ≠ 0) :
    ReciprocityTheory.ChartRestriction.G.T0.ratio (Ω := F) (AddMonoidAlgebra.single g a : AddMonoidAlgebra F Γ)
      (AddMonoidAlgebra.single g b) = a / b := by
  have hex : ∃ c : F, (AddMonoidAlgebra.single g a : AddMonoidAlgebra F Γ) = c • AddMonoidAlgebra.single g b :=
    ⟨a / b, by rw [AddMonoidAlgebra.smul_single', div_mul_cancel₀ a hb]⟩
  rw [ReciprocityTheory.ChartRestriction.G.T0.ratio, dite_eq_left hex]
  have hc := hex.choose_spec
  rw [AddMonoidAlgebra.smul_single'] at hc
  have hv : a = hex.choose * b := by
    first
    | exact AddMonoidAlgebra.single_injective g hc
    | simpa using hc
  exact eq_div_of_mul_eq hb hv.symm

theorem independent_differentials_ratios_of_trdeg_values {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)] (hG : GenFrEx Xo c)
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z))
    {κ : Type} (w : κ → Rul Xo c) (e : κ ≃ Fin (d.N + 1)) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (htr : FnTrdeg Xo c d.D) (hw : ∀ k, d.w (e k) = valC hG a n (w k)) (hb : ∀ Z, d.w (d.jc Z) Z ≠ 0)
    (hbig : ∀ Z : Comp Xo c, ∃ k₀, evC hG Z (w k₀) ≠ 0 ∧ Algebra.trdeg c.F
      (IntermediateField.adjoin c.F (Set.range fun k => evC hG Z (w k) / evC hG Z (w k₀))) = d.D) :
    A1Bigness d := by
  unfold A1Bigness
  intro Z
  have hfull : Algebra.trdeg c.F (Om Z) = d.D := by
    unfold FnTrdeg at htr
    exact htr Z
  refine (GlobalTheory.trdegD_iff_exists_linearIndependent_D d Z hfull (hb Z)).mp ?_
  unfold ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD
  obtain ⟨k₀, hk₀, htk⟩ := hbig Z
  have hwZ : ∀ k, d.w (e k) Z = AddMonoidAlgebra.single (wtZ a n) (evC hG Z (w k)) := by
    intro k
    rw [hw k]
    rfl
  set kc := e.symm (d.jc Z) with hkc
  have hjc : d.jc Z = e kc := (e.apply_symm_apply _).symm
  have hc0 : evC hG Z (w kc) ≠ 0 := by
    intro h0
    apply hb Z
    rw [hjc, hwZ, h0, AddMonoidAlgebra.single_zero]
  have hrange : (Set.range fun j => ReciprocityTheory.ChartRestriction.G.T0.ratio (Ω := Om Z) (d.w j Z) (d.w (d.jc Z) Z)) =
      Set.range fun k => evC hG Z (w k) / evC hG Z (w kc) := by
    rw [← e.surjective.range_comp]
    congr 1
    funext k
    change ReciprocityTheory.ChartRestriction.G.T0.ratio (d.w (e k) Z) (d.w (d.jc Z) Z) = _
    rw [hjc, hwZ, hwZ]
    exact ratio_single _ _ _ hc0
  rw [hrange]
  have hsame : IntermediateField.adjoin c.F (Set.range fun k => evC hG Z (w k) / evC hG Z (w kc)) =
      IntermediateField.adjoin c.F (Set.range fun k => evC hG Z (w k) / evC hG Z (w k₀)) :=
    le_antisymm (adjoin_div_le (fun k => evC hG Z (w k)) kc k₀ hk₀)
      (adjoin_div_le (fun k => evC hG Z (w k)) k₀ kc hc0)
  rw [hsame]
  exact htk




theorem independent_differentials_ratios_cusp_forms_trdeg : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z)) (e : Fin G.N ≃ Fin (d.N + 1)), d.D = WeightFamilies.dimY D j → (∀ k, d.w (e k) = valC hG (wtA wL) wL.n (G.w k).1) → (∀ Z, d.w (d.jc Z) Z ≠ 0) → (∀ Z : Comp (T.Q.Xo j) T.Q.c, ∃ k₀, evC hG Z (G.w k₀).1 ≠ 0 ∧ Algebra.trdeg T.Q.c.F (IntermediateField.adjoin T.Q.c.F (Set.range fun k => evC hG Z (G.w k).1 / evC hG Z (G.w k₀).1)) = WeightFamilies.dimY D j) → A1Bigness d := by
  intro D T h j hj hG ka wL wF G _ d e hD hw hb hbig
  have hpin : T.Q.PinDat := by
    have hp := h.toLawsCore.pins
    unfold Par.Pins at hp
    exact hp.2.2.2
  have htr := (GlobalTheory.FlagDim.fnFG_fnTrdeg_record D T.Q hpin j hj).2
  rw [← hD] at htr hbig
  exact independent_differentials_ratios_of_trdeg_values hG d (fun k => (G.w k).1) e (wtA wL) wL.n htr hw hb hbig

end GlobalTheory.BigRec
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.HeightEnds

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


omit [NumberField E] [IsCMField E] in
theorem gram_eq_mul {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * G.map τ * (xᴴ)ᵀ := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem norm_det_orth {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (hx : IsOrth X x) (τ : X.Ψ) :
    ‖(mat x τ).det‖ ^ 2 * ‖τ.1 X.Gm.det‖ = 1 := by
  have h := congrArg (fun M => ‖Matrix.det M‖) (hx τ)
  simp only [gram_eq_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_conjTranspose,
    Matrix.det_diagonal, norm_mul, norm_star, norm_prod] at h
  have h1 : ∀ a : Fin r, ‖((sgn X.p0 (a : ℕ) : ℝ) : ℂ)‖ = 1 := by
    intro a
    unfold sgn
    split_ifs <;> simp
  simp only [h1, Finset.prod_const_one] at h
  rw [RingHom.map_det, RingHom.mapMatrix_apply, ← h]
  ring

theorem gramDet_square {r : ℕ} (N : Matrix (Fin r) (Fin r) ℂ) :
    (Nᴴ * N).det.re = ‖N.det‖ ^ 2 := by
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def, Complex.conj_mul']
  norm_cast

theorem exists_pos_le_bot_top : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∃ m : ℝ, 0 < m ∧ ∀ x, IsOrth X x → m ≤ d x ⊥ ∧ m ≤ d x ⊤) := by
  intro r X d hd
  obtain ⟨w0, hw0, hΛ0, hsp0⟩ := GlobalTheory.LatBasis.exists_basis_mem r X ⊤
  have hr : r = Module.finrank E (⊤ : Submodule E (Fin r → E)) := by simp
  let w : Fin r → Fin r → E := w0 ∘ finCongr hr
  have hw : LinearIndependent E w := hw0.comp _ (finCongr hr).injective
  have hΛ : ∀ a, w a ∈ X.Λ := fun a => hΛ0 _
  have hsp : Submodule.span E (Set.range w) = ⊤ := by
    rw [(finCongr hr).surjective.range_comp]; exact hsp0
  have hdet : (Matrix.of w).det ≠ 0 := by
    have : IsUnit (Matrix.of w) := Matrix.linearIndependent_rows_iff_isUnit.1 hw
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  have hind := GlobalTheory.SpanIndex.relIndex_span_ne_zero r X (Fin r) w hw hΛ
  set n : ℕ := (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup) with hn
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hind)
  let c : ℝ := (∏ τ : X.Ψ, ‖τ.1 X.Gm.det‖ * ‖τ.1 (Matrix.of w).det‖ ^ 2) / n
  have hc : 0 < c := by
    refine div_pos (Finset.prod_pos fun τ _ => mul_pos ?_ (pow_pos ?_ 2)) hnpos
    · exact norm_pos_iff.2 ((map_ne_zero τ.1).2 X.Gm_det)
    · exact norm_pos_iff.2 ((map_ne_zero τ.1).2 hdet)
  refine ⟨min 1 c, lt_min one_pos hc, fun x hx => ?_⟩
  have hxd : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 := by
    intro τ h0
    have := norm_det_orth X x hx τ
    simp [h0] at this
  constructor
  · have h := hd x hxd Empty (fun a => a.elim) linearIndependent_empty_type (fun a => a.elim)
    have hre : Set.range (fun a : Empty => (a.elim : Fin r → E)) = ∅ := Set.range_eq_empty _
    rw [hre] at h
    simp only [Submodule.span_empty, Matrix.det_isEmpty, Complex.one_re, Finset.prod_const_one,
      Submodule.bot_toAddSubgroup, inf_bot_eq, AddSubgroup.relIndex_self, Nat.cast_one,
      div_one] at h
    rw [h]
    exact min_le_left _ _
  · have h := hd x hxd (Fin r) w hw hΛ
    rw [← hn, hsp] at h
    rw [h]
    refine (min_le_right _ _).trans (le_of_eq ?_)
    refine congrArg (· / (n : ℝ)) (Finset.prod_congr rfl fun τ _ => ?_)
    have h1 : (Matrix.of fun k a => τ.1 (w a k)).det = τ.1 (Matrix.of w).det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.det_transpose]
      rfl
    have h2 := norm_det_orth X x hx τ
    have h3 : ‖(mat x τ).det‖ ≠ 0 := norm_ne_zero_iff.2 (hxd τ)
    rw [gramDet_square, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', h1, norm_mul,
      norm_inv, mul_pow, inv_pow]
    congr 1
    exact eq_inv_of_mul_eq_one_right h2

end GlobalTheory.HeightEnds
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.HeightInv


open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
theorem _root_.GlobalTheory.HeightInv.relIndex_span_map {R K V ι : Type} [CommRing R] [Field K] [Algebra R K] [AddCommGroup V]
    [Module K V] [Module R V] [IsScalarTower R K V] (Λ : Submodule R V) (f : V →ₗ[K] V)
    (hinj : Function.Injective f) (hsurj : Function.Surjective f) (hΛ : ∀ x, x ∈ Λ ↔ f x ∈ Λ)
    (w : ι → V) :
    (Submodule.span R (Set.range fun a => f (w a))).toAddSubgroup.relIndex
        (Λ.toAddSubgroup ⊓ (Submodule.span K (Set.range fun a => f (w a))).toAddSubgroup) =
      (Submodule.span R (Set.range w)).toAddSubgroup.relIndex
        (Λ.toAddSubgroup ⊓ (Submodule.span K (Set.range w)).toAddSubgroup) := by
  let g : V →+ V := f.toAddMonoidHom
  have hg : Function.Injective g := hinj
  have hΛmap : Λ.toAddSubgroup.map g = Λ.toAddSubgroup := by
    ext v
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hΛ x).1 hx
    · intro hv
      obtain ⟨x, rfl⟩ := hsurj v
      exact ⟨x, (hΛ x).2 hv, rfl⟩
  have hK : Submodule.span K (Set.range fun a => f (w a)) = (Submodule.span K (Set.range w)).map f := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hR : Submodule.span R (Set.range fun a => f (w a)) =
      (Submodule.span R (Set.range w)).map (f.restrictScalars R) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hKg : ((Submodule.span K (Set.range w)).map f).toAddSubgroup =
      (Submodule.span K (Set.range w)).toAddSubgroup.map g := by
    ext v
    simp [Submodule.mem_map, AddSubgroup.mem_map, g]
  have hRg : ((Submodule.span R (Set.range w)).map (f.restrictScalars R)).toAddSubgroup =
      (Submodule.span R (Set.range w)).toAddSubgroup.map g := by
    ext v
    simp [Submodule.mem_map, AddSubgroup.mem_map, g]
  have hinf : Λ.toAddSubgroup ⊓ (Submodule.span K (Set.range w)).toAddSubgroup.map g =
      (Λ.toAddSubgroup ⊓ (Submodule.span K (Set.range w)).toAddSubgroup).map g := by
    rw [AddSubgroup.map_inf_eq _ _ _ hg, hΛmap]
  rw [hK, hR, hKg, hRg, hinf, AddSubgroup.relIndex_map_map_of_injective _ _ hg]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem height_lact : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ → ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → (∀ τ : X.Ψ, (mat (lact γ x) τ).det ≠ 0) ∧ ∀ W : Submodule E (Fin r → E), d (lact γ x) (W.map (γ : Matrix (Fin r) (Fin r) E).mulVecLin) = d x W) := by
  intro r X d hd γ hγ x hx
  have hmat : ∀ τ : X.Ψ, mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ :=
    fun τ => rfl
  have hγdet : (γ : Matrix (Fin r) (Fin r) E).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).ne_zero
  have hτdet : ∀ τ : X.Ψ, ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det ≠ 0 := by
    intro τ
    have := τ.1.map_det (γ : Matrix (Fin r) (Fin r) E)
    rw [RingHom.mapMatrix_apply] at this
    rw [← this]
    exact (map_ne_zero τ.1).2 hγdet
  have hx' : ∀ τ : X.Ψ, (mat (lact γ x) τ).det ≠ 0 := by
    intro τ
    rw [hmat, Matrix.det_mul]
    exact mul_ne_zero (hτdet τ) (hx τ)
  refine ⟨hx', fun W => ?_⟩
  obtain ⟨w, hw, hwΛ, hsp⟩ := GlobalTheory.LatBasis.exists_basis_mem r X W
  set f := (γ : Matrix (Fin r) (Fin r) E).mulVecLin with hf
  have hinj : Function.Injective f := Matrix.mulVec_injective_of_isUnit γ.isUnit
  have hsurj : Function.Surjective f := LinearMap.injective_iff_surjective.1 hinj
  have hΛ : ∀ y, y ∈ X.Λ ↔ f y ∈ X.Λ := hγ.2
  have hw' : LinearIndependent E (fun a => f (w a)) :=
    hw.map' f (LinearMap.ker_eq_bot.2 hinj)
  have hsp' : W.map f = Submodule.span E (Set.range fun a => f (w a)) := by
    conv_lhs => rw [← hsp]
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  have e1 := hd (lact γ x) hx' _ (fun a => f (w a)) hw' (fun a => (hΛ _).1 (hwΛ a))
  have e2 := hd x hx _ w hw hwΛ
  have hM : ∀ τ : X.Ψ, (mat (lact γ x) τ)⁻¹ * (Matrix.of fun k a => τ.1 (f (w a) k)) =
      (mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)) := by
    intro τ
    have : (Matrix.of fun k a => τ.1 (f (w a) k)) =
        (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (Matrix.of fun k a => τ.1 (w a k)) := by
      ext k a
      simp [hf, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [this, hmat, Matrix.mul_inv_rev, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul_cancel_left _ _ (hτdet τ).isUnit]
  rw [hsp', e1, relIndex_span_map X.Λ f hinj hsurj hΛ w]
  rw [hsp] at e2
  rw [e2, hsp]
  simp only [hM]

end GlobalTheory.HeightInv
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.HeightCont

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem height_continuousOn : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ W, ContinuousOn (fun x => d x W) {x : Frame X.Ψ r | (∀ τ : X.Ψ, (mat x τ).det ≠ 0)}) := by
  intro r X d hd W
  obtain ⟨w, hw, hΛ, hsp⟩ := GlobalTheory.LatBasis.exists_basis_mem r X W
  suffices H : ContinuousOn (fun x => d x (Submodule.span E (Set.range w)))
      {x : Frame X.Ψ r | (∀ τ : X.Ψ, (mat x τ).det ≠ 0)} by rwa [hsp] at H
  refine ContinuousOn.congr ?_ (fun x hx => hd x hx _ w hw hΛ)
  refine ContinuousOn.div_const ?_ _
  refine continuousOn_finsetProd _ fun τ _ x hx => ContinuousAt.continuousWithinAt ?_
  have hm : Continuous (fun x : Frame X.Ψ r => mat x τ) := continuous_apply τ
  have hr : ContinuousAt (Ring.inverse : ℂ → ℂ) (mat x τ).det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (hx τ)
  have hi : ContinuousAt (fun x : Frame X.Ψ r => (mat x τ)⁻¹) x :=
    ContinuousAt.comp (f := fun x : Frame X.Ψ r => mat x τ) (continuousAt_matrix_inv _ hr)
      hm.continuousAt
  have hg : Continuous (fun A : Matrix (Fin r) (Fin r) ℂ =>
      ((A * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * (A * (Matrix.of fun k a => τ.1 (w a k)))).det.re) :=
    Complex.continuous_re.comp
      (((continuous_id.matrix_mul continuous_const).matrix_conjTranspose.matrix_mul
        (continuous_id.matrix_mul continuous_const)).matrix_det)
  exact ContinuousAt.comp (f := fun x : Frame X.Ψ r => (mat x τ)⁻¹) hg.continuousAt hi

end GlobalTheory.HeightCont
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.HeightLower

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_pos_le_height : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∃ m : ℝ, 0 < m ∧ ∀ W, m ≤ d x W) := by
  intro r X d hd x hx
  obtain ⟨C, hC, hCle⟩ := GlobalTheory.relIndex_span_le_norm_minor r X
  have hω : ∀ τ : X.Ψ, ∃ ω : ℝ, 1 ≤ ω ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (M : Matrix (Fin r) ι ℂ), ((mat x τ * M)ᴴ * (mat x τ * M)).det.re ≤ ω * (Mᴴ * M).det.re :=
    fun τ => GlobalTheory.gram_det_mul_le GlobalTheory.det_re_mono_of_posSemidef r (mat x τ)
  choose ω hω1 hωle using hω
  have hΩ : 0 < ∏ τ, ω τ := Finset.prod_pos fun τ _ => lt_of_lt_of_le one_pos (hω1 τ)
  refine ⟨1 / (C * ∏ τ, ω τ), by positivity, fun W => ?_⟩
  obtain ⟨w, hwi, hwΛ, hspan⟩ := GlobalTheory.LatBasis.exists_basis_mem r X W
  obtain ⟨e, he, hδ⟩ := GlobalTheory.exists_maximal_minor_ne_zero_of_linearIndependent E r _ w hwi
  have hdW := hd x hx _ w hwi hwΛ
  rw [hspan] at hdW
  rw [hdW]
  have hI0 := GlobalTheory.SpanIndex.relIndex_span_ne_zero r X _ w hwi hwΛ
  have hIle := hCle _ w hwi hwΛ e he hδ
  rw [hspan] at hI0 hIle
  set I := ((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex
    (X.Λ.toAddSubgroup ⊓ W.toAddSubgroup)) with hIdef
  have hIpos : (0 : ℝ) < (I : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hI0

  have key : ∀ τ : X.Ψ, ‖τ.1 (Matrix.of fun k a => w a (e k)).det‖ ^ 2 ≤
      ω τ * (((mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w a k))ᴴ *
        ((mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w a k))).det.re := by
    intro τ
    have hu : IsUnit (mat x τ).det := isUnit_iff_ne_zero.mpr (hx τ)
    have h1 := hωle τ _ ((mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w a k))
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hu] at h1
    have h2 := GlobalTheory.norm_det_submatrix_sq_le_det_gram (Fin r) _
      (Matrix.of fun k a => τ.1 (w a k)) e he
    have h3 : ((Matrix.of fun k a => τ.1 (w a k)).submatrix e id).det =
        τ.1 (Matrix.of fun k a => w a (e k)).det := by
      rw [RingHom.map_det]
      congr 1
    rw [h3] at h2
    exact h2.trans h1
  have hprod : ∏ τ : X.Ψ, ‖τ.1 (Matrix.of fun k a => w a (e k)).det‖ ^ 2 ≤
      (∏ τ, ω τ) * ∏ τ : X.Ψ, (((mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w a k))ᴴ *
        ((mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w a k))).det.re := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun τ _ => by positivity) (fun τ _ => key τ)
  rw [div_le_div_iff₀ (by positivity) hIpos, one_mul]
  calc (I : ℝ) ≤ C * _ := hIle
    _ ≤ C * ((∏ τ, ω τ) * _) := mul_le_mul_of_nonneg_left hprod hC.le
    _ = _ := by ring

end GlobalTheory.HeightLower
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.SubspaceHeight

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem det_gram_reindex {r : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : κ ≃ ι) (A : Matrix (Fin r) (Fin r) ℂ) (f : ι → Fin r → ℂ) :
    ((A * (Matrix.of fun k a => f (e a) k))ᴴ * (A * (Matrix.of fun k a => f (e a) k))).det =
      ((A * (Matrix.of fun k a => f a k))ᴴ * (A * (Matrix.of fun k a => f a k))).det := by
  rw [← Matrix.det_submatrix_equiv_self e]
  congr 1

theorem exists_height : (∀ (r : ℕ) (X : Data E r), ∃ d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ, (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ)))) := by
  intro r X
  choose b hb hΛ hsp using GlobalTheory.LatBasis.exists_basis_mem r X
  refine ⟨fun x W => ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (b W a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (b W a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range (b W))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (b W))).toAddSubgroup)) : ℝ)), ?_⟩
  intro x _ ι _ _ w hw hwΛ
  have hc : Module.finrank E (Submodule.span E (Set.range w)) = Fintype.card ι :=
    finrank_span_eq_card hw
  let e : Fin (Module.finrank E (Submodule.span E (Set.range w))) ≃ ι :=
    (Fintype.equivFinOfCardEq hc.symm).symm
  have hr : Set.range (fun a => w (e a)) = Set.range w := e.surjective.range_comp w
  have key := GlobalTheory.T.gramDet_div_index_eq_of_span_eq r X x _ (b (Submodule.span E (Set.range w))) (fun a => w (e a))
    (hb _) (hΛ _) (hw.comp e e.injective) (fun a => hwΛ _) (by rw [hr, hsp])
  refine key.trans ?_
  rw [hr]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  exact congrArg Complex.re (det_gram_reindex e _ (fun a k => τ.1 (w a k)))

end GlobalTheory.SubspaceHeight
end
