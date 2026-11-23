module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle030
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle031
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle040
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle044
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle036
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle019
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle043
public import Formalism.LocalToGlobal.ProjectiveLattices.LocalUnitReduction.IsUnitMkOfForallPrime
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle005
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
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall

@[expose] public section

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Test

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem wtC_of (hB : BorChartF Xo c) (hA : AllTest Xo c) (σ : c.F →+* ℂ) : WtC Xo c σ := by
  intro a n _ f hf t y y' hb
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  exact wtField_of_borChart hB a n f hf (CAt σ) t y y' (hA _ y) (hA _ y') hb

end Test

section Inv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

end Inv

section Cont

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

def DictLoc (V : HSp D) {X : Comp → Data E r} (dict : GA D V → Σ k, Frame (X k).Ψ r) : Prop :=
  ∀ g₀ : GA D V, ∃ N ∈ 𝓝 g₀, ∃ (k : Comp) (x : GA D V → Frame (X k).Ψ r), ContinuousOn x N ∧
    ∀ g ∈ N, x g ∈ (X k).dom ∧ ∃ γ ∈ (X k).Γ, dict g = ⟨k, lact γ (x g)⟩

end Cont

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)


include h hj in
theorem pt_realise (la : HeightOneSpectrum (𝓞 T.Q.c.F))
    (y : PtV (T.Q.Xo j) T.Q.c (algCls _ _) Unit (fun _ _ _ _ => True) la) :
    ∃ y' : T.PtA j la, ∀ f, vAtV y' f = vAtV y f := by
  rcases y with ⟨q, S, io, e, ho, z, hz, η, hη, rfl⟩
  obtain ⟨η', hη'⟩ := T.G.liesTotal h.points_condition h.bc66 hj la S io e ho z hz
  exact ⟨PtV.mk la ho z hz η' hη', fun _ => rfl⟩

theorem ereal_lin (a c : ℝ) (v : EReal) (h0 : 0 ≤ v) (ht : v ≠ ⊤) :
    (((a + c * v.toReal : ℝ)) : EReal) = (a : EReal) + (c : EReal) * v := by
  have hb : v ≠ ⊥ := fun hb => by simp [hb] at h0
  conv_rhs => rw [← EReal.coe_toReal ht hb]
  push_cast
  rfl

theorem regularity_R2_extended_points :
    RegularityR2 (recPJ h j hj) (extAll h j hj)
      (fun {wL} {n} gens => NoCommonZero (T.Q.Xo j) T.Q.c fun i => (gens i).1) := by
  have hv : ∀ la (y : (recPJ h j hj).Pt la) w (F : (recB h.toLawsCore).Cusp j w),
      (recPJ h j hj).vAt la y ((recPJ h j hj).inc w F) = vAtV y F.1 :=
    fun la y w F => recPJ_vAt_inc h j hj la y w F
  have ev : ∀ la (y : (extAll h j hj).Pt' la) w (F : (recB h.toLawsCore).Cusp j w),
      (extAll h j hj).vAt' la y ((recPJ h j hj).inc w F) = y.1 F.1 :=
    fun la y w F => extAll_vAt_inc h j hj la y w F
  constructor
  · intro wL wE n gens et nus c hc hNZ hX la y'
    have hR := (h.reg j hj).1.2 ⟨(wtA wL, wL.n), dom_wtA wL⟩ ⟨(wtA wE, wE.n), dom_wtA wE⟩ n
      (fun k => ⟨(gens k).1, cutR_le T.C j wL (gens k).2⟩) ⟨et.1, cutR_le T.C j wE et.2⟩ nus c hc hNZ
      (by
        rintro la' ⟨_, ⟨y, rfl⟩⟩
        obtain ⟨y0, hy0⟩ := pt_realise h j hj la' y
        have hx := hX la' y0
        have eet : (recPJ h j hj).vAt la' y0 ((recPJ h j hj).inc wE et) = vAtV y et.1 :=
          (hv la' y0 wE et).trans (hy0 _)
        have egs : (⨅ k, (recPJ h j hj).vAt la' y0 ((recPJ h j hj).inc wL (gens k))) =
            ⨅ k, vAtV y (gens k).1 := iInf_congr fun k => (hv la' y0 wL (gens k)).trans (hy0 _)
        have h0 : 0 ≤ vAtV y et.1 := le_of_le_of_eq hx.1 eet
        show 0 ≤ vAtV y et.1 ∧ (vAtV y et.1 ≠ ⊤ →
          (⨅ k, vAtV y (gens k).1) ≤ (nus la' : EReal) + (c : EReal) * vAtV y et.1)
        refine ⟨h0, fun hne => ?_⟩
        have hne' : (recPJ h j hj).vAt la' y0 ((recPJ h j hj).inc wE et) ≠ ⊤ := by rw [eet]; exact hne
        calc (⨅ k, vAtV y (gens k).1)
            = ⨅ k, (recPJ h j hj).vAt la' y0 ((recPJ h j hj).inc wL (gens k)) := egs.symm
          _ ≤ (((nus la' : ℝ) + c * ((recPJ h j hj).vAt la' y0 ((recPJ h j hj).inc wE et)).toReal : ℝ) :
                EReal) := hx.2 hne'
          _ = (nus la' : EReal) + (c : EReal) * vAtV y et.1 := by
              rw [eet]; exact ereal_lin _ _ _ h0 hne)
    obtain ⟨h1, h2⟩ := hR.1 la ⟨y'.1, y'.2⟩
    have eet : (extAll h j hj).vAt' la y' ((recPJ h j hj).inc wE et) = y'.1 et.1 := ev la y' wE et
    have egs : (⨅ k, (extAll h j hj).vAt' la y' ((recPJ h j hj).inc wL (gens k))) =
        ⨅ k, y'.1 (gens k).1 := iInf_congr fun k => ev la y' wL (gens k)
    have h1' : 0 ≤ y'.1 et.1 := h1
    refine ⟨le_of_le_of_eq h1' eet.symm, fun hne => ?_⟩
    have hne' : y'.1 et.1 ≠ ⊤ := by rw [← eet]; exact hne
    calc (⨅ k, (extAll h j hj).vAt' la y' ((recPJ h j hj).inc wL (gens k)))
        = ⨅ k, y'.1 (gens k).1 := egs
      _ ≤ (nus la : EReal) + (c : EReal) * y'.1 et.1 := h2 hne'
      _ = (((nus la : ℝ) + c * ((extAll h j hj).vAt' la y' ((recPJ h j hj).inc wE et)).toReal : ℝ) :
            EReal) := by rw [eet]; exact (ereal_lin _ _ _ h1' hne').symm
  · intro wL n gens nus hNZ hX la y'
    have hR := (h.reg j hj).2 (wtA wL) wL.n (dom_wtA wL) n (fun k => (gens k).1)
      (fun k => cutR_le T.C j wL (gens k).2) hNZ nus
      (by
        rintro la' _ ⟨y, rfl⟩
        obtain ⟨y0, hy0⟩ := pt_realise h j hj la' y
        have egs : (⨅ k, (recPJ h j hj).vAt la' y0 ((recPJ h j hj).inc wL (gens k))) =
            ⨅ k, vAtV y (gens k).1 := iInf_congr fun k => (hv la' y0 wL (gens k)).trans (hy0 _)
        exact le_of_eq_of_le egs.symm (hX la' y0)) la y'.1 y'.2
    calc (⨅ k, (extAll h j hj).vAt' la y' ((recPJ h j hj).inc wL (gens k)))
        = ⨅ k, y'.1 (gens k).1 := iInf_congr fun k => ev la y' wL (gens k)
      _ ≤ _ := hR

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7}

def SpanW {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) {wL : WeightFamilies.Wt D j} {N : ℕ}
    (w : Fin N → B.Cusp j wL) (S : Scal B) : Prop :=
  Submodule.span (𝓞 B.KO) (Set.range w) = X.WWc S.sW wL

variable {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)

def wNorm (σ : T.Q.c.F →+* ℂ) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (p : FPt (T.U j σ).X) : ℝ :=
  Real.sqrt (∑ k, (((T.U j σ).X p.1).pnorm (laU (T.U j σ) (wtA wL) wL.n p.1)
    (rdU (T.U j σ) ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) p.1) p.2) ^ 2)

def BigAt (hG : GenFrEx (T.Q.Xo j) T.Q.c) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF) : Prop :=
  NoCommonZero (Xo := T.Q.Xo j) (c := T.Q.c) (fun k => ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j)) ∧
  (∀ Z : Comp (T.Q.Xo j) T.Q.c, ∃ k₀, evC hG Z ((G.w k₀ : (recB h.toLawsCore).Cusp j wL) : T.R j) ≠ 0 ∧
    Algebra.trdeg T.Q.c.F (IntermediateField.adjoin T.Q.c.F (Set.range fun k =>
      evC hG Z ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) /
        evC hG Z ((G.w k₀ : (recB h.toLawsCore).Cusp j wL) : T.R j))) = WeightFamilies.dimY D j)

def ThAt (hG : GenFrEx (T.Q.Xo j) T.Q.c) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (g0 : (recB h.toLawsCore).Cusp j wF) : Prop :=
  ∃ (e : ℕ) (w' : WeightFamilies.Wt D j) (θ : (recB h.toLawsCore).Cusp j w'),
    wadd wF w' = wsmul e wL ∧
    ∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z ((θ : (recB h.toLawsCore).Cusp j w') : T.R j) ≠ 0

def CurveInstSt : Prop :=
  ∀ (hG : GenFrEx (T.Q.Xo j) T.Q.c) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (S : Scal (recB h.toLawsCore))
    (g0 : (recB h.toLawsCore).Cusp j wF),
    SpanW (recPlus h j hj) G.w S → BigAt h j hj hG G → ThAt h j hj hG G g0 → (recPlus h j hj).NonZeroComp wF g0 →
    Nonempty (CurveModel G la g0)

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor TensorProduct

section Gen

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
  (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

theorem curveUnit_isUnit_emb (Ω : Type) [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)
    (F : X.Forms) (hF : gF F ≠ 0) :
    IsUnit (lwZ X la N Ω gF w (algebraMap (Rp X la N) (Lw X la w) (emb X la N F))) := by
  rw [lwZ_alg, rzMap_emb]
  have h1 : IsUnit ((1 : X.Kl la) ⊗ₜ[B.KO] gF F) := by
    simpa using (IsUnit.mk0 _ hF).map
      (Algebra.TensorProduct.includeRight : Ω →ₐ[B.KO] X.Kl la ⊗[B.KO] Ω)
  have h2 : IsUnit ((1 : Kp X la N) ⊗ₜ[X.Kl la] ((1 : X.Kl la) ⊗ₜ[B.KO] gF F)) := by
    simpa using h1.map (Algebra.TensorProduct.includeRight :
      X.Kl la ⊗[B.KO] Ω →ₐ[X.Kl la] Kp X la N ⊗[X.Kl la] (X.Kl la ⊗[B.KO] Ω))
  exact h2.map _

theorem curveUnit_isUnit_w0inv (Ω : Type) [CommRing Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω) :
    IsUnit (lwZ X la N Ω gF w (w0inv X la w)) := by
  refine IsUnit.of_mul_eq_one (lwZ X la N Ω gF w (algebraMap (Rp X la N) (Lw X la w) (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))) ?_
  rw [← map_mul, mul_comm, section_mul_inverse_eq_one, map_one]

variable {ι : Type} (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)]
  (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)

theorem nonzero_divisor_cusp_form
    (hInj : ∀ f : ↥(Frac0 X la w), (∀ Z, phiZ X la N (Ω Z) (gF Z) w f = 0) → f = 0)
    (F : X.Forms) (hF : ∀ Z, gF Z F ≠ 0) (b : ↥(Frac0 X la w))
    (hb : (b : Lw X la w) * algebraMap (Rp X la N) (Lw X la w) (emb X la N F) = 0) : b = 0 := by
  refine hInj b fun Z => ?_
  rw [phiZ_apply]
  have h1 := congrArg (lwZ X la N (Ω Z) (gF Z) w) hb
  rw [map_mul, map_zero] at h1
  exact (curveUnit_isUnit_emb X la N w (Ω Z) (gF Z) F (hF Z)).mul_left_eq_zero.mp h1

theorem curveUnit_unit_gen [Fintype ι]
    (hInj : ∀ f : ↥(Frac0 X la w), (∀ Z, phiZ X la N (Ω Z) (gF Z) w f = 0) → f = 0)
    (hone : ∀ Q : Ideal ↥(Frac0 X la w), Q.IsPrime → Jid X la w ≤ Q → ∀ Z Z',
      RingHom.ker (phiZ X la N (Ω Z) (gF Z) w) ≤ Q → RingHom.ker (phiZ X la N (Ω Z') (gF Z') w) ≤ Q → Z = Z')
    (hloc : ∀ Z (r : RZs X la N (Ω Z) (gF Z) w), ∃ a p : ↥(Frac0 X la w),
      (∀ Q : Ideal ↥(Frac0 X la w), Q.IsPrime → Jid X la w ≤ Q →
        RingHom.ker (phiZ X la N (Ω Z) (gF Z) w) ≤ Q → p ∉ Q) ∧
      phiZ X la N (Ω Z) (gF Z) w p * r = phiZ X la N (Ω Z) (gF Z) w a)
    (hfd : FiniteDimensional (Kp X la N) (OsK X la w))
    (u : ↥(Frac0 X la w)) (hu : ∀ Z, IsUnit (phiZ X la N (Ω Z) (gF Z) w u)) :
    IsUnit (toOsK X la w u) := by
  classical
  have hmem : ∀ b : ↥(Frac0 X la w), b * u ∈ Jid X la w → b ∈ Jid X la w := by
    intro b hb
    refine LocalUnitReduction.mem_of_forall_sup_ker (Jid X la w) (R := fun Z => RZs X la N (Ω Z) (gF Z) w)
      (fun Z => phiZ X la N (Ω Z) (gF Z) w) hInj hone fun Z => ?_
    refine LocalUnitReduction.mem_sup_ker (Jid X la w) (R := fun Z => RZs X la N (Ω Z) (gF Z) w)
      (fun Z => phiZ X la N (Ω Z) (gF Z) w) (hloc Z) ?_
    obtain ⟨v, hv⟩ := hu Z
    have h1 : phiZ X la N (Ω Z) (gF Z) w (b * u) ∈
        Ideal.map (phiZ X la N (Ω Z) (gF Z) w) (Jid X la w) := Ideal.mem_map_of_mem _ hb
    rw [map_mul, ← hv] at h1
    have h2 := Ideal.mul_mem_right (↑v⁻¹ : RZs X la N (Ω Z) (gF Z) w) _ h1
    rwa [mul_assoc, Units.mul_inv, mul_one] at h2
  have hinj : Function.Injective (LinearMap.mulRight (Kp X la N) (toOsK X la w u)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨b, rfl⟩ := toOsK_surjective X la w y
    rw [LinearMap.mulRight_apply, ← map_mul, toOsK_eq_zero_iff] at hy
    rw [toOsK_eq_zero_iff]
    exact hmem b hy
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hinj) 1
  rw [LinearMap.mulRight_apply] at hy
  exact IsUnit.of_mul_eq_one y (by rw [mul_comm]; exact hy)

end Gen

section U0

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X}
  {hM : IntAtExt X E} {ka wL wF : WeightFamilies.Wt D j}

theorem phi_unit_product_cusp_forms (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO))
    (g0 : B.Cusp j wF) {e : ℕ} {w' : WeightFamilies.Wt D j} (θ : B.Cusp j w') (hw : wadd wF w' = wsmul e wL)
    (Ω : Type) [Field Ω] [Algebra B.KO Ω] (gF : (xplus X E hM).Forms →ₐ[B.KO] Ω)
    (hg : gF (X.inc wF g0) ≠ 0) (hθ : gF (X.inc w' θ) ≠ 0) :
    IsUnit (phiZ (xplus X E hM) la G.N Ω gF G.w (u0 G la g0 θ hw)) := by
  rw [phiZ_apply]
  show IsUnit (lwZ (xplus X E hM) la G.N Ω gF G.w (frac (xplus X E hM) la G.w e
    (emb (xplus X E hM) la G.N (X.inc wF g0) * emb (xplus X E hM) la G.N (X.inc w' θ))))
  simp only [frac_apply, map_mul, map_pow]
  exact ((curveUnit_isUnit_emb _ la G.N G.w Ω gF _ hg).mul
    (curveUnit_isUnit_emb _ la G.N G.w Ω gF _ hθ)).mul ((curveUnit_isUnit_w0inv _ la G.N G.w Ω gF).pow e)

end U0

section Inst

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)
  (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)

theorem curveUnit_gF_inc (Z : Comp (T.Q.Xo j) T.Q.c) (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u) :
    formsEvR j hG hT Z ((recPJ h j hj).inc u F) = evC hG Z (F : T.R j) :=
  formsEvR_single j hG hT Z _ _

variable {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
  (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (g0 : (recB h.toLawsCore).Cusp j wF)

theorem nonzero_divisor_cusp_form_record
    (hInj : ∀ f : ↥(Frac0 (recPlus h j hj) la G.w),
      (∀ Z : Comp (T.Q.Xo j) T.Q.c, phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w f = 0) →
        f = 0)
    (hg0 : ∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z ((g0 : (recB h.toLawsCore).Cusp j wF) : T.R j) ≠ 0) :
    ∀ b : ↥(Frac0 (recPlus h j hj) la G.w),
      (b : Lw (recPlus h j hj) la G.w) *
        algebraMap (Rp (recPlus h j hj) la G.N) (Lw (recPlus h j hj) la G.w)
          (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc wF g0)) = 0 →
        b = 0 :=
  fun b hb => nonzero_divisor_cusp_form (recPlus h j hj) la G.N G.w (fun Z => Om Z) (fun Z => formsEvR j hG hT Z)
    hInj _ (fun Z h0 => hg0 Z ((curveUnit_gF_inc h j hj hG hT Z wF g0).symm.trans h0)) b hb

theorem unit_ideal_cusp_form_record [Fintype (Comp (T.Q.Xo j) T.Q.c)]
    {e : ℕ} {w' : WeightFamilies.Wt D j} (θ : (recB h.toLawsCore).Cusp j w') (hw : wadd wF w' = wsmul e wL)
    (hInj : ∀ f : ↥(Frac0 (recPlus h j hj) la G.w),
      (∀ Z : Comp (T.Q.Xo j) T.Q.c, phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w f = 0) →
        f = 0)
    (hone : ∀ Q : Ideal ↥(Frac0 (recPlus h j hj) la G.w), Q.IsPrime → Jid (recPlus h j hj) la G.w ≤ Q →
      ∀ Z Z' : Comp (T.Q.Xo j) T.Q.c,
        RingHom.ker (phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w) ≤ Q →
        RingHom.ker (phiZ (recPlus h j hj) la G.N (Om Z') (formsEvR j hG hT Z') G.w) ≤ Q → Z = Z')
    (hloc : ∀ (Z : Comp (T.Q.Xo j) T.Q.c)
      (r : RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w),
      ∃ a p : ↥(Frac0 (recPlus h j hj) la G.w),
        (∀ Q : Ideal ↥(Frac0 (recPlus h j hj) la G.w), Q.IsPrime → Jid (recPlus h j hj) la G.w ≤ Q →
          RingHom.ker (phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w) ≤ Q → p ∉ Q) ∧
        phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w p * r =
          phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w a)
    (hfd : FiniteDimensional (Kp (recPlus h j hj) la G.N) (OsK (recPlus h j hj) la G.w))
    (hg0 : ∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z ((g0 : (recB h.toLawsCore).Cusp j wF) : T.R j) ≠ 0)
    (hθ : ∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z ((θ : (recB h.toLawsCore).Cusp j w') : T.R j) ≠ 0) :
    IsUnit (toOsK (recPlus h j hj) la G.w (u0 G la g0 θ hw)) :=
  curveUnit_unit_gen (recPlus h j hj) la G.N G.w (fun Z => Om Z) (fun Z => formsEvR j hG hT Z)
    hInj hone hloc hfd _ fun Z => phi_unit_product_cusp_forms G la g0 θ hw (Om Z) (formsEvR j hG hT Z)
      (fun h0 => hg0 Z ((curveUnit_gF_inc h j hj hG hT Z wF g0).symm.trans h0))
      (fun h0 => hθ Z ((curveUnit_gF_inc h j hj hG hT Z w' θ).symm.trans h0))

end Inst

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j}

def ESecSt (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∀ (y : PtsG G la → E.Pt' la) (hw : ∀ ζ, FromW ζ (y ζ)) (g0 : B.Cusp j wF),
    Nonempty (CurveModel G la g0) →
    (∀ ζ, (hw ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0)) ≠ 0) →
    ∃ (k : ℕ) (p q : Rp (xplus X E hM) la G.N),
      p ∈ Vw (xplus X E hM) la G.N (addL (wt0 D j) wL k) ∧ q ∈ Vw (xplus X E hM) la G.N (addL (wt0 D j) wL k) ∧
      (∀ β, β ≠ 0 → hasseRp (xplus X E hM) la G.N β p = 0) ∧
      (∀ β, β ≠ 0 → hasseRp (xplus X E hM) la G.N β q = 0) ∧
      ∀ ζ, (hw ζ).ev p ≠ 0 ∧ (hw ζ).ev q ≠ 0 ∧
        vV (hw ζ).T.V ((hw ζ).ev p) + vV (hw ζ).T.V ((hw ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0))) =
          vV (hw ζ).T.V ((hw ζ).ev q)

def LocStructSt (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∀ (y : PtsG G la → E.Pt' la) (hw : ∀ ζ, FromW ζ (y ζ)) (g0 : B.Cusp j wF),
    Nonempty (CurveModel G la g0) →
    (∀ ζ, (hw ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0)) ≠ 0) →
    ∀ g : ↥(Frac0 (xplus X E hM) la G.w),
      (∀ ζ, 0 ≤ nval (hw ζ).T.V 1 ((hw ζ).toSecPt.lift (g : Lw (xplus X E hM) la G.w))) →
      ∃ (f d : ↥(Frac0 (xplus X E hM) la G.w)) (hd : ∀ ζ, (hw ζ).toSecPt.lift (d : Lw (xplus X E hM) la G.w) ≠ 0),
        toOsK (xplus X E hM) la G.w f = toOsK (xplus X E hM) la G.w d * toOsK (xplus X E hM) la G.w g ∧
        ∀ (l : List (Idx D j G.N →₀ ℕ)) (ζ : PtsG G la),
          0 ≤ nval (hw ζ).T.V 1 (evL (fun ζ => (hw ζ).toSecPt) ζ (hdList (fun ζ => (hw ζ).toSecPt) l
            (ιW (fun ζ => (hw ζ).toSecPt) (f : Lw (xplus X E hM) la G.w) *
              ↑(isUnit_of_lift_ne (fun ζ => (hw ζ).toSecPt) hd).unit⁻¹)))

theorem locRing_of {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}
    (h1 : ESecSt G la) (h2 : LocStructSt G la) : LocRingSt G la :=
  fun y hw g0 hC hg0 => ⟨h1 y hw g0 hC hg0, h2 y hw g0 hC hg0⟩

section Inst

variable {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)

def ValSepSt {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) : Prop :=
  ∀ (y : PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ ζ, FromW ζ (y ζ)),
    ∃ (Zc : PtsG G la → Comp (T.Q.Xo j) T.Q.c) (ι : ∀ ζ, Om (Zc ζ) →+* (hw ζ).T.Fr),
      (∀ ζ, ∃ a : Om (Zc ζ), vV (hw ζ).T.V (ι ζ a) = 1) ∧
      (∀ ζ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w),
        evC hG (Zc ζ) ((F : (recB h.toLawsCore).Cusp j w) : T.R j) = 0 →
          (hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)) = 0) ∧
      (∀ ζ (w : WeightFamilies.Wt D j) (F F' : (recB h.toLawsCore).Cusp j w),
        ι ζ (evC hG (Zc ζ) ((F : (recB h.toLawsCore).Cusp j w) : T.R j)) *
            (hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F')) =
          ι ζ (evC hG (Zc ζ) ((F' : (recB h.toLawsCore).Cusp j w) : T.R j)) *
            (hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F))) ∧
      ∀ ζ ζ', ζ ≠ ζ' → Zc ζ = Zc ζ' →
        ∃ (w : WeightFamilies.Wt D j) (F F' : (recB h.toLawsCore).Cusp j w),
          (hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F')) ≠ 0 ∧
          (hw ζ').ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F')) ≠ 0 ∧
          nval (hw ζ).T.V 1 ((hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F'))) <
            nval (hw ζ).T.V 1 ((hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F))) ∧
          nval (hw ζ').T.V 1 ((hw ζ').ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F'))) <
            nval (hw ζ').T.V 1 ((hw ζ').ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)) -
              (hw ζ').ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F')))

end Inst

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)

def BIRSt {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF) : Prop :=
  ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (a : Om Z), ∃ (k : ℕ) (g : (recB h.toLawsCore).Cusp j (wsmul k wL))
    (p : MvPolynomial (Fin G.N) T.Q.c.F), p.IsHomogeneous k ∧
    MvPolynomial.aeval (fun i => evC hG Z ((G.w i : (recB h.toLawsCore).Cusp j wL) : T.R j)) p ≠ 0 ∧
    a * MvPolynomial.aeval (fun i => evC hG Z ((G.w i : (recB h.toLawsCore).Cusp j wL) : T.R j)) p =
      evC hG Z ((g : (recB h.toLawsCore).Cusp j (wsmul k wL)) : T.R j)

def CompSplitSt : Prop :=
  ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (w : WeightFamilies.Wt D j) (g : (recB h.toLawsCore).Cusp j w),
    ∃ g' : (recB h.toLawsCore).Cusp j w,
      evC hG Z ((g' : (recB h.toLawsCore).Cusp j w) : T.R j) = evC hG Z ((g : (recB h.toLawsCore).Cusp j w) : T.R j) ∧
      ∀ Z', Z' ≠ Z → evC hG Z' ((g' : (recB h.toLawsCore).Cusp j w) : T.R j) = 0

def GenValInjSt : Prop :=
  ∀ (w : WeightFamilies.Wt D j) (g : (recB h.toLawsCore).Cusp j w),
    (∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z ((g : (recB h.toLawsCore).Cusp j w) : T.R j) = 0) → g = 0

end Formalism.L2.Pj
end
end
