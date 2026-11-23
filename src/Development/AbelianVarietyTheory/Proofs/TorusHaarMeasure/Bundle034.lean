module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle038
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.PhRec
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle003
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle009
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle008
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle033
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002

@[expose] public section

section

noncomputable section

namespace GlobalTheory.BigRec

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem pnorm_pos_of_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r)
    (P : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ) {x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom)
    (hP : P x ≠ 0) : 0 < X.pnorm la P x := by
  have hd : ∀ τ i, ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i ≠ 0 := by
    intro τ i h0
    have := (hx τ).2 i
    rw [h0] at this
    simp at this
  refine mul_pos (norm_pos_iff.2 hP) (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => ?_)
  exact Real.rpow_pos_of_pos (norm_pos_iff.2 (div_ne_zero (hd _ _) (hd _ _))) _

theorem exp_le_of_neg_log_sqrt_le {S a b : ℝ} (hS : 0 < S) (h : -Real.log (Real.sqrt S) ≤ a + b) :
    Real.exp (-(2 * b)) ≤ Real.exp (2 * a) * S := by
  rw [Real.log_sqrt hS.le] at h
  calc Real.exp (-(2 * b)) ≤ Real.exp (2 * a + Real.log S) := Real.exp_le_exp.2 (by linarith)
    _ = Real.exp (2 * a) * S := by rw [Real.exp_add, Real.exp_log hS]

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_rdU_ne_zero {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) {N : ℕ} (w : Fin N → Rul Xo c)
    (hw : NoCommonZero Xo c w) (k : U.Comp) {x : ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ r} (hx : x ∈ (U.X k).dom) :
    ∃ m, rdU U (w m) k x ≠ 0 := by
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  obtain ⟨m, hm⟩ := hw (CAt σ) (U.un k ⟨x, hx⟩)
  refine ⟨m, ?_⟩
  have e : rdU U (w m) k x = toC (evR Xo c (w m) (U.un k ⟨x, hx⟩)) := dif_pos hx
  rw [e]
  exact hm

theorem model_ineq_of_log_bound {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (xR : ℝ) (σ : c.F →+* ℂ)
    {N N' : ℕ} (i : ℕ) (w : Fin N → Rul Xo c) (e : Fin (N' + 1) ≃ Fin N) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (th tableLineDegreeFive DF tableLineDegreeTwo cc : ℝ) (hσ : GoodEmb c σ)
    (hI : I2AtFramePoints U xR (fun m => w (e m)) (a, n) th tableLineDegreeFive DF cc) (hw : NoCommonZero Xo c w)
    (k : (U σ).Comp) (eW : ReciprocityTheory.ChartRestriction.G.FD.Wt ((U σ).X k).Ψ r)
    (et : ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ r → ℂ)
    (het : ∀ x ∈ ((U σ).X k).dom, ((U σ).X k).pnorm eW et x ≤
      Real.exp (-(i : ℝ) * (ReciprocityTheory.ChartRestriction.G.I2.phiFD ((U σ).X k) th x - tableLineDegreeTwo))) :
    ReciprocityTheory.ChartRestriction.G.AR.Up.InterpolationModelInequalities ((U σ).X k) (laU (U σ) a n k) eW (fun m => rdU (U σ) (w m) k) et cc i
      (ReciprocityTheory.ChartRestriction.G.I2.phiFD ((U σ).X k) th) := by
  refine ⟨⟨Real.exp (2 * (tableLineDegreeFive * DF)) * lieFac Dw xR a ^ 2, fun x hx => ?_⟩,
    Real.exp (2 * (i * tableLineDegreeTwo)), fun x hx => ?_⟩
  · have h1 := hI σ hσ k x hx
    have hs : ∑ m, recNrm (U σ) xR a n (w (e m)) k x ^ 2 =
        lieFac Dw xR a ^ 2 * ∑ m, ((U σ).X k).pnorm (laU (U σ) a n k) (rdU (U σ) (w m) k) x ^ 2 := by
      rw [Finset.mul_sum, ← e.sum_comp]
      exact Finset.sum_congr rfl fun m _ => by rw [recNrm, mul_pow]
    have hpos : 0 < ∑ m, ((U σ).X k).pnorm (laU (U σ) a n k) (rdU (U σ) (w m) k) x ^ 2 := by
      obtain ⟨m, hm⟩ := exists_rdU_ne_zero (U σ) w hw k hx
      exact Finset.sum_pos' (fun _ _ => sq_nonneg _)
        ⟨m, Finset.mem_univ _, pow_pos (pnorm_pos_of_ne_zero _ _ _ hx hm) 2⟩
    simp only [hs] at h1
    have h2 := exp_le_of_neg_log_sqrt_le (mul_pos (pow_pos (lieFac_pos Dw xR a) 2) hpos) h1
    rw [← mul_assoc, ← mul_assoc] at h2
    exact h2
  · have h0 : 0 ≤ ((U σ).X k).pnorm eW et x :=
      mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ =>
        Real.rpow_nonneg (norm_nonneg _) _)
    refine (pow_le_pow_left₀ h0 (het x hx) 2).trans (le_of_eq ?_)
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring

end Gen

theorem firstMin_fn_nonneg {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (th : ℝ) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    0 ≤ ReciprocityTheory.ChartRestriction.G.I2.phiFD X th x := by
  unfold ReciprocityTheory.ChartRestriction.G.I2.phiFD
  split_ifs <;> positivity

theorem firstMin_fn_lower {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) {th : ℝ} (hth : 0 < th) :
    ∃ ca ε0 : ℝ, 0 < ca ∧ 0 < ε0 ∧ ∀ x ∈ X.dom, X.la1 x < ε0 →
      ca / X.la1 x ^ 2 ≤ ReciprocityTheory.ChartRestriction.G.I2.phiFD X th x := by
  have hf : 0 < ReciprocityTheory.ChartRestriction.G.I2.PT.f E := by
    unfold ReciprocityTheory.ChartRestriction.G.I2.PT.f
    have h1 := IsTotallyComplex.finrank E
    have h2 : 0 < Module.finrank ℚ E := Module.finrank_pos
    omega
  have hrd : 0 < ReciprocityTheory.ChartRestriction.G.I2.PT.rd E := by
    unfold ReciprocityTheory.ChartRestriction.G.I2.PT.rd
    exact Real.rpow_pos_of_pos (abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero E))) _
  refine ⟨2 * ReciprocityTheory.ChartRestriction.G.I2.PT.f E / ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2, th, by positivity, hth,
    fun x _ hlt => ?_⟩
  unfold ReciprocityTheory.ChartRestriction.G.I2.phiFD
  rw [if_pos hlt, div_div]




theorem phRec_of_firstMin : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ) (wL : WeightFamilies.Wt D j) (N N' i : ℕ) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (e : Fin (N' + 1) ≃ Fin N) (et : (recB h.toLawsCore).Cusp j (etWt D j i)) (th tableLineDegreeFive DF tableLineDegreeTwo c : ℝ), GoodEmb T.Q.c σ → 0 < th → I2AtFramePoints (T.U j) (xiR D) (fun m => (w (e m)).1) (wtA wL, wL.n) th tableLineDegreeFive DF c → NoCommonZero (T.Q.Xo j) T.Q.c (fun m => (w m).1) → (∀ k : (T.U j σ).Comp, ∀ x ∈ ((T.U j σ).X k).dom, ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA (etWt D j i)) ((etWt D j i)).n k) (rdU (T.U j σ) et.1 k) x ≤ Real.exp (-(i : ℝ) * (ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k) th x - tableLineDegreeTwo))) → PhRec h j σ w i et c := by
  intro D T h j hj σ wL N N' i w e et th tableLineDegreeFive DF tableLineDegreeTwo c hσ hth hI hw het k
  exact ⟨ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k) th, fun x _ => firstMin_fn_nonneg _ th x,
    firstMin_fn_lower _ hth,
    model_ineq_of_log_bound (T.U j) (xiR D) σ i (fun m => (w m).1) e (wtA wL) wL.n th tableLineDegreeFive DF tableLineDegreeTwo c hσ hI hw k _ _
      (het k)⟩

end GlobalTheory.BigRec
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.LatBasisAdapted

theorem span_range_smul_comp {K V ι κ : Type*} [Field K] [AddCommGroup V] [Module K V]
    (c : ι → K) (hc : ∀ i, c i ≠ 0) (w : ι → V) (f : κ → ι) :
    Submodule.span K (Set.range ((fun i => c i • w i) ∘ f)) =
      Submodule.span K (Set.range (w ∘ f)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    have h : (w ∘ f) k = (c (f k))⁻¹ • ((fun i => c i • w i) ∘ f) k := by
      simp [smul_smul, inv_mul_cancel₀ (hc (f k))]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_basis_adapted_mem : (∀ (r : ℕ) (X : Data E r) (W₁ W₂ : Submodule E (Fin r → E)), ∃ (a b c : ℕ) (w : Fin a ⊕ Fin b ⊕ Fin c → Fin r → E), LinearIndependent E w ∧ (∀ k, w k ∈ X.Λ) ∧ Submodule.span E (Set.range (w ∘ Sum.inl)) = W₁ ⊓ W₂ ∧ Submodule.span E (Set.range (w ∘ Sum.map id Sum.inl)) = W₁ ∧ Submodule.span E (Set.range (w ∘ Sum.map id Sum.inr)) = W₂ ∧ Submodule.span E (Set.range w) = W₁ ⊔ W₂) := by
  intro r X W₁ W₂
  obtain ⟨a, b, c, w, hw, h0, h1, h2, h3⟩ :=
    GlobalTheory.exists_basis_adapted_two_subspaces E (Fin r → E) W₁ W₂
  choose n hn hm using fun k => (GlobalTheory.LatDen.latDen r X).1 (w k)
  have hc : ∀ k, (n k : E) ≠ 0 := fun k => Nat.cast_ne_zero.2 (hn k).ne'
  refine ⟨a, b, c, fun k => (n k : E) • w k, ?_, hm, ?_, ?_, ?_, ?_⟩
  · exact hw.units_smul (fun k => Units.mk0 _ (hc k))
  · rw [span_range_smul_comp _ hc, h0]
  · rw [span_range_smul_comp _ hc, h1]
  · rw [span_range_smul_comp _ hc, h2]
  · exact (span_range_smul_comp _ hc w id).trans h3

end GlobalTheory.LatBasisAdapted
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory

theorem relIndex_span_le_norm_minor :
    (∀ (r : ℕ) (X : Data E r), ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → ∀ e : ι → Fin r, Function.Injective e → (Matrix.of fun k a => w a (e k)).det ≠ 0 → (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ) ≤ C * ∏ τ : X.Ψ, ‖τ.1 (Matrix.of fun k a => w a (e k)).det‖ ^ 2) := by
  intro r X
  obtain ⟨n, hn, hint⟩ := (GlobalTheory.LatDen.latDen r X).2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : E) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨∏ _τ : X.Ψ, ((n : ℝ) ^ r) ^ 2, Finset.prod_pos fun _ _ => by positivity, ?_⟩
  intro ι _ _ w _ hw e he hdet
  set M : Matrix ι ι E := Matrix.of fun k a => w a (e k) with hM
  set L : AddSubgroup (Fin r → E) :=
    X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup with hL
  let A : Matrix ι ι (𝓞 E) := Matrix.of fun k a => ⟨(n : E) * w a (e k), hint _ (hw a) _⟩
  have hA : (algebraMap (𝓞 E) E).mapMatrix A = (n : E) • M := by
    ext k a
    rfl
  have hdetA : ((A.det : 𝓞 E) : E) = (n : E) ^ Fintype.card ι * M.det := by
    rw [← Matrix.det_smul, ← hA, ← RingHom.map_det]
  have hA0 : A.det ≠ 0 := by
    intro h
    rw [h] at hdetA
    exact mul_ne_zero (pow_ne_zero _ hn0) hdet (hdetA.symm.trans rfl)
  let φ : L →+ (ι → 𝓞 E) :=
    { toFun := fun v k => ⟨(n : E) * v.1 (e k), hint _ v.2.1 _⟩
      map_zero' := by
        ext k
        exact mul_zero (n : E)
      map_add' := fun u v => by
        ext k
        exact mul_add (n : E) _ _ }
  set R := (LinearMap.range A.mulVecLin).toAddSubgroup with hR
  have hidx := index_range_mulVecLin_eq_abs_norm_det ι A hA0
  rw [← hR] at hidx
  have hR0 : R.index ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero, eq_comm, abs_eq_zero, Algebra.norm_eq_zero_iff] at hidx
    exact hA0 (by exact_mod_cast hidx)
  have hle : R.comap φ ≤ (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.addSubgroupOf L := by
    rintro ⟨v, hvΛ, hv⟩ ⟨c, hc⟩
    obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hv
    have hb : M *ᵥ (fun a => (c a : E)) = M *ᵥ b := by
      funext k
      have h := congrArg (algebraMap (𝓞 E) E) (congrFun hc k)

      rw [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, map_sum] at h
      apply mul_left_cancel₀ hn0
      have h2 : (algebraMap (𝓞 E) E) (φ ⟨∑ i, b i • w i, hvΛ, hv⟩ k) =
          (n : E) * (∑ i, b i • w i) (e k) := rfl
      rw [h2] at h
      have h3 : (M *ᵥ b) k = (∑ i, b i • w i) (e k) := by
        simp [Matrix.mulVec, dotProduct, hM, Finset.sum_apply, mul_comm]
      rw [h3, ← h, Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul, ← mul_assoc]
      rfl
    have hcb := Matrix.mulVec_injective_of_det_ne_zero hdet hb
    change (∑ i, b i • w i) ∈ Submodule.span (𝓞 E) (Set.range w)
    rw [← hcb]
    refine Submodule.sum_mem _ fun a _ => ?_
    exact Submodule.smul_mem _ (c a) (Submodule.subset_span ⟨a, rfl⟩)
  have h1 : (R.comap φ).index ≤ R.index := by
    rw [AddSubgroup.index_comap, ← AddSubgroup.relIndex_top_right]
    exact AddSubgroup.relIndex_le_of_le_right le_top (by rwa [AddSubgroup.relIndex_top_right])
  have h0 : (R.comap φ).index ≠ 0 := by
    rw [AddSubgroup.index_comap]
    exact fun h => hR0 (AddSubgroup.index_eq_zero_of_relIndex_eq_zero h)
  have h2 : (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex L ≤ R.index :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (AddSubgroup.index_dvd_of_le hle)).trans h1
  have h3 : (R.index : ℝ) = ∏ τ : X.Ψ, ‖τ.1 ((A.det : 𝓞 E) : E)‖ ^ 2 := by
    rw [← abs_norm_eq_prod_cmType_sq r X, ← hidx, Rat.cast_natCast]
  have hcard : Fintype.card ι ≤ r := by simpa using Fintype.card_le_of_injective e he
  refine (Nat.cast_le.2 h2).trans ?_
  rw [h3, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun τ _ => ?_
  rw [hdetA, map_mul, map_pow, map_natCast, norm_mul, norm_pow, Complex.norm_natCast, mul_pow]
  gcongr

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.LatBasis

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_basis_mem : (∀ (r : ℕ) (X : Data E r) (W : Submodule E (Fin r → E)), ∃ w : Fin (Module.finrank E W) → Fin r → E, LinearIndependent E w ∧ (∀ a, w a ∈ X.Λ) ∧ Submodule.span E (Set.range w) = W) := by
  intro r X W
  choose n hn hmem using (GlobalTheory.LatDen.latDen r X).1
  set b := Module.finBasis E W
  set v : Fin (Module.finrank E W) → Fin r → E := fun i => (b i : Fin r → E) with hv
  have hvli : LinearIndependent E v := b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hne : ∀ i, (n (v i) : E) ≠ 0 := fun i => Nat.cast_ne_zero.2 (hn (v i)).ne'
  set c : Fin (Module.finrank E W) → Eˣ := fun i => Units.mk0 _ (hne i)
  have hli : LinearIndependent E (fun i => (n (v i) : E) • v i) := hvli.units_smul c
  refine ⟨fun i => (n (v i) : E) • v i, hli, fun a => hmem (v a), ?_⟩
  have hle : Submodule.span E (Set.range fun i => (n (v i) : E) • v i) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact W.smul_mem _ (b i).2
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [finrank_span_eq_card hli, Fintype.card_fin]

end GlobalTheory.LatBasis
end
