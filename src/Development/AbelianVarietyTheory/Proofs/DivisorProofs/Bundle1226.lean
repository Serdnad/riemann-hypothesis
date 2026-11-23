module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1169
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1170
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1103
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle201
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
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
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle005
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.ExistsLinearIndependentNormLe

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem Dat.fv_add_h_res {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {p : ℕ} {G : PDivGroup p R}
    {t : G.TorsionTower A} {c : primDR A} (d : Dat t c) (n : ℕ) (D : Type) [CommRing D] [Algebra R D]
    (φ : G.A n →ₐ[R] D) :
    fv d.f (G.A (n + 1)) D (φ.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n)) (t.y (n + 1)) +
      (φ.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n)) (d.h (n + 1)) = fv d.f (G.A n) D φ (t.y n) + φ (d.h n) := by
  have hc := (fv_isCoc_and_ev_eq R A d.f).1 (G.A (n + 1)) (G.A n) D
    (G.res n : G.A (n + 1) →ₐ[R] G.A n) φ (t.y (n + 1)) (sm_whole (t.y (n + 1)))
  rw [hc, t.res n, d.res n, AlgHom.comp_apply, map_sub]
  simp only [BialgHom.coe_toAlgHom]
  abel

theorem Dat.pullTwo_res_coc (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (n : ℕ) :
    pullbackTwo (G.res n) (d.coc (n + 1)) = d.coc n := by
  let L : G.A n →ₐ[R] G.A n ⊗[R] G.A n := Algebra.TensorProduct.includeLeft
  let Rt : G.A n →ₐ[R] G.A n ⊗[R] G.A n := Algebra.TensorProduct.includeRight
  have hres : ∀ u : G.A (n + 1) ⊗[R] G.A (n + 1), pullbackTwo (G.res n) u =
      Algebra.TensorProduct.lift (L.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n))
        (Rt.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n)) (fun _ _ ↦ Commute.all _ _) u := by
    intro u
    induction u using TensorProduct.inductionOn with
    | tmul a b => simp [L, Rt]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hid : ∀ u : G.A n ⊗[R] G.A n,
      Algebra.TensorProduct.lift L Rt (fun _ _ ↦ Commute.all _ _) u = u := by
    intro u
    simp only [L, Rt, Algebra.TensorProduct.lift_includeLeft_includeRight, AlgHom.id_apply]
  have hmul : (toConv (L.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n)) *
      toConv (Rt.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n))).ofConv =
      (toConv L * toConv Rt).ofConv.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n) :=
    (AlgHom.convMul_comp_bialgHom_distrib (toConv L) (toConv Rt) (G.res n)).symm
  rw [hres, Dat.lift_coc, hmul, d.fv_add_h_res n, d.fv_add_h_res n, d.fv_add_h_res n]
  conv_rhs => rw [← hid (d.coc n), Dat.lift_coc]
  simp only [← spOver_comp, Category.assoc, t.res]

end GlobalTheory.PtExt
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R] {A : Over (Sp R)}

theorem fv_form (β : Form (A.hom ≫ 𝟙 _)) {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (x : Pt A D) : fv β.1 D D' φ x = 0 := by
  simpa only [fv, GlobalTheory.Cris.ev] using β.2 (trivMap φ x) rfl rfl

variable [GrpObj A] {p : ℕ} {G : PDivGroup p R}

def formDat (t : G.TorsionTower A) (β : Form (A.hom ≫ 𝟙 _)) (hβ : Form.cl _ β ∈ primDR A) : Dat t ⟨_, hβ⟩ where
  f := β.1
  cl := rfl
  g := fun _ _ _ _ _ ↦ 0
  add := fun _ _ _ _ _ _ φ _ _ ↦ by simp [fv_form]
  h := 0
  res := fun n ↦ by simp [fv_form]

theorem isCan_form : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (β : Form (A.hom ≫ 𝟙 _)) (hβ : Form.cl _ β ∈ primDR A),
    ∃ w : G.omega, (∀ n, w.1 n = cotVal β.1 (t.y n)) ∧ IsCan t ⟨_, hβ⟩ (G.rigOfOmega w) := by
  intro R _ A _ p G t β hβ
  refine ⟨⟨(formDat t β hβ).om, fun n ↦ GlobalTheory.T.torsionTowerPresentation_cotangentPullback_res_rigidification R A p G t _ (formDat t β hβ) n⟩, fun n ↦ ?_,
    formDat t β hβ, 0, _, fun n ↦ ?_, fun _ ↦ rfl, rfl⟩
  · change cotVal β.1 (t.y n) - dUnit (R := R) (0 : G.A n) = _
    rw [dUnit, map_zero, sub_zero]
  · change (0 : _) = 0 - (fv β.1 _ _ _ _ - fv β.1 _ _ _ _ - fv β.1 _ _ _ _) - cobOne R (G.A n) 0
    simp [fv_form]

end GlobalTheory.PtExt
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Weight

open ReciprocityTheory.L2DbarEstimates (V leviV)

theorem semiPosReg_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (π : Y ⟶ X) (hπ : π ≫ p = q) (D D' : ℕ), SmoothOfRelativeDimension D p → ∀ (B : LB X) (φ : Weight p σ B), φ.IsCInf → φ.SemiPosReg D → (φ.pull π hπ).SemiPosReg D' := by
  intro k _ X Y p q σ π hπ D D' hs B φ hC hSP
  haveI := hs
  intro i c y hy ξ
  set m := PtsOver.map π hπ (spMap σ)
  have hm : ∀ z, (m z).1 = z.1 ≫ π := fun _ => rfl
  obtain ⟨c0, h0⟩ := AlgChart.exists_mem_source (p := p) (σ := σ) (D := D) (m y)
  have him : m y ∈ ptsIn p σ (B.U (i PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => m y) (fun _ => rfl) hy.2 PUnit.unit
  set F : V D' → V D := c0.e ∘ m ∘ c.e.symm with hFdef
  set U := c.e.target ∩ c.e.symm ⁻¹' (m ⁻¹' c0.e.source)
  have hU : IsOpen U := GlobalTheory.ChartGlue.isOpen_over c.e (c0.e.open_source.preimage (continuous_of_comp hm))
  have hyU : c.e y ∈ U := GlobalTheory.ChartGlue.mem_over c.e hy.1 h0
  have hF0 : DifferentiableOn ℂ F U := AlgChart.holo_map hm c c0
  have hF : ContDiffOn ℂ 2 F U := (contDiffOn_piLp 2).2 fun a =>
    (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D' _ U hU
      (differentiableOn_euclidean.1 hF0 a)).of_le (by norm_cast)
  have hFy : F (c.e y) = c0.e (m y) := by
    simp only [hFdef, Function.comp_apply, c.e.left_inv hy.1]
  set g : V D → ℂ := fun v => (φ.φ (i PUnit.unit) (c0.e.symm v) : ℂ) with hgdef
  have hg : ContDiffAt ℝ 2 g (F (c.e y)) := hFy ▸
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hC.contDiffAt c0 h0 him)
  have e : (fun v => ((φ.pull π hπ).φ i (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)] g ∘ F := by
    filter_upwards [hU.mem_nhds hyU] with v hv
    have := Weight.pull_φ φ π hπ i (c.e.symm v)
    simp only [g, hFdef, Function.comp_apply, c0.e.left_inv hv.2]
    exact congrArg _ this
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr e,
    ReciprocityTheory.ChartRestriction.G.AR.Up.RGF.gc_leviV_comp D' D g F U hU _ hyU hF hg ξ, hFy]
  exact hSP (i PUnit.unit) c0 (m y) ⟨h0, him⟩ _

end GlobalTheory.Weight
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.ContRead

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {U : X.Opens}

theorem val_eq_of_evHom_eq (hU : IsAffineOpen U) {σ τ : k →+* ℂ} {y : CxPts p σ} {z : CxPts p τ}
    (hy : y ∈ ptsIn p σ U) (hz : z ∈ ptsIn p τ U) (e : evHom hy = evHom hz) : y.1 = z.1 := by
  have e₁ : y.1.appLE U ⊤ hy = z.1.appLE U ⊤ hz := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom]
    exact CommRingCat.hom_ext e
  have a := IsAffineOpen.SpecMap_appLE_fromSpec y.1 hU (isAffineOpen_top (Sp ℂ)) hy
  have a' := IsAffineOpen.SpecMap_appLE_fromSpec z.1 hU (isAffineOpen_top (Sp ℂ)) hz
  rw [e₁, a', IsAffineOpen.fromSpec_top] at a
  exact ((cancel_epi _).1 a).symm

theorem eq_of_val_eq (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) {σ τ : k →+* ℂ} (e : σ = τ)
    (y : CxPts p σ) (z : CxPts p τ) (h : y.1 = z.1) : u σ y = u τ z := by
  subst e
  rw [Subtype.ext h]

theorem evHom_ofHom (hU : IsAffineOpen U) {σ : k →+* ℂ} (φ : Γ(X, U) →+* ℂ)
    (h : ∀ a, φ (algX p U a) = σ a) : evHom (ofHom_mem hU φ h) = φ :=
  RingHom.ext fun f => (ev_eq _ f).symm.trans (ev_ofHom hU φ h f)

theorem evHom_comp_algX {σ : k →+* ℂ} {y : CxPts p σ} (hy : y ∈ ptsIn p σ U) :
    (evHom hy).comp (algX p U) = σ :=
  RingHom.ext fun a => (ev_eq hy _).symm.trans (ev_algX hy a)

theorem exists_continuous_read : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (U : X.Opens) (hU : IsAffineOpen U) (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ), (∀ σ, ContinuousOn (u σ) (ptsIn p σ U)) → (letI : TopologicalSpace (Γ(X, U) →+* ℂ) := TopologicalSpace.induced (fun x : Γ(X, U) →+* ℂ => (x : Γ(X, U) → ℂ)) inferInstance; ∃ ψ : (Γ(X, U) →+* ℂ) → ℝ, Continuous ψ ∧ (∀ (σ : k →+* ℂ) (y : CxPts p σ) (hy : y ∈ ptsIn p σ U), ψ (evHom hy) = u σ y) ∧ (∀ x : Γ(X, U) →+* ℂ, ∃ (σ : k →+* ℂ) (y : CxPts p σ) (hy : y ∈ ptsIn p σ U), evHom hy = x) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ) (hy : y ∈ ptsIn p σ U) (W : Set (Γ(X, U) →+* ℂ)), W ∈ 𝓝 (evHom hy) → {z : CxPts p σ | ∃ hz : z ∈ ptsIn p σ U, evHom hz ∈ W} ∈ 𝓝 y) := by
  intro k _ X _ p D hX U hU u hu
  letI : TopologicalSpace (Γ(X, U) →+* ℂ) :=
    TopologicalSpace.induced (fun x : Γ(X, U) →+* ℂ => (x : Γ(X, U) → ℂ)) inferInstance
  have hcf : ∀ f : Γ(X, U), Continuous fun x : Γ(X, U) →+* ℂ => x f := fun f =>
    (continuous_apply f).comp continuous_induced_dom
  refine ⟨fun x => u (x.comp (algX p U)) (ofHom hU x fun _ => rfl), ?_, ?_, ?_, ?_⟩
  · have := hX.finite_emb
    classical
    rw [continuous_iff_continuousAt]
    intro x₀
    obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀, x₀.comp (algX p U) = σ₀ := ⟨_, rfl⟩
    have hN : {x : Γ(X, U) →+* ℂ | x.comp (algX p U) = σ₀} ∈ 𝓝 x₀ := by
      have hex : ∀ τ : k →+* ℂ, τ ≠ σ₀ → ∃ a, τ a ≠ σ₀ a := fun τ h => by
        by_contra hc
        push_neg at hc
        exact h (RingHom.ext hc)
      choose! a ha using hex
      have hopen : ∀ τ : k →+* ℂ,
          {x : Γ(X, U) →+* ℂ | τ ≠ σ₀ → x (algX p U (a τ)) ≠ τ (a τ)} ∈ 𝓝 x₀ := by
        intro τ
        by_cases hτ : τ = σ₀
        · exact Filter.Eventually.of_forall fun x h => (h hτ).elim
        · have ho : IsOpen {x : Γ(X, U) →+* ℂ | x (algX p U (a τ)) ≠ τ (a τ)} :=
            isOpen_ne_fun (hcf _) continuous_const
          filter_upwards [ho.mem_nhds (show x₀ (algX p U (a τ)) ≠ τ (a τ) from
            fun h => ha τ hτ (h.symm.trans (RingHom.congr_fun hσ₀ (a τ))))] with x hx _ using hx
      filter_upwards [(Filter.iInter_mem (f := 𝓝 x₀)).2 hopen] with x hx
      by_contra hne
      exact (Set.mem_iInter.1 hx _) hne rfl
    let F : (Γ(X, U) →+* ℂ) → CxPts p σ₀ := fun x =>
      if h : x.comp (algX p U) = σ₀ then ofHom hU x (fun a => RingHom.congr_fun h a)
      else ofHom hU x₀ (fun a => RingHom.congr_fun hσ₀ a)
    have hF0 : F x₀ = ofHom hU x₀ (fun a => RingHom.congr_fun hσ₀ a) := dif_pos hσ₀
    have hFmem : ∀ x, F x ∈ ptsIn p σ₀ U := fun x => by
      by_cases h : x.comp (algX p U) = σ₀
      · simp only [F, dif_pos h]; exact ofHom_mem _ _ _
      · simp only [F, dif_neg h]; exact ofHom_mem _ _ _
    have hF : ContinuousAt F x₀ := by
      refine tendsto_subtype_rng.2 ?_
      rw [hF0]
      refine GlobalTheory.Points.tendsto_of_isAffineOpen hU (ofHom_mem hU x₀ _) (Filter.Eventually.of_forall hFmem)
        fun f => ?_
      have e : ∀ᶠ x in 𝓝 x₀, x f = valR (F x).1 U f := by
        filter_upwards [hN] with x hx
        simp only [F, dif_pos hx]
        exact (ev_ofHom hU x _ f).symm
      rw [show valR (ofHom hU x₀ (fun a => RingHom.congr_fun hσ₀ a)).1 U f = x₀ f from
        ev_ofHom hU x₀ _ f]
      exact ((hcf f).tendsto x₀).congr' e
    have hu0 : ContinuousAt (u σ₀) (F x₀) :=
      (hu σ₀).continuousAt ((isOpen_ptsIn U).mem_nhds (hFmem x₀))
    refine (hu0.comp hF).congr_of_eventuallyEq ?_
    filter_upwards [hN] with x hx
    simp only [Function.comp_apply, F, dif_pos hx]
    exact eq_of_val_eq u hx _ _ rfl
  · intro σ y hy
    exact eq_of_val_eq u (evHom_comp_algX hy) _ _
      (val_eq_of_evHom_eq hU (ofHom_mem hU _ _) hy (evHom_ofHom hU _ _))
  · intro x
    exact ⟨x.comp (algX p U), ofHom hU x (fun _ => rfl), ofHom_mem hU x _, evHom_ofHom hU x _⟩
  · intro σ y hy W hW
    rw [nhds_induced] at hW
    obtain ⟨t, ht, hsub⟩ := mem_comap.1 hW
    have hc : ContinuousAt (fun z : CxPts p σ => fun f : Γ(X, U) => ev p σ U f z) y :=
      continuousAt_pi.2 fun f => (continuousOn_ev f).continuousAt ((isOpen_ptsIn U).mem_nhds hy)
    have hval : (fun f : Γ(X, U) => ev p σ U f y) = ⇑(evHom hy) := funext fun f => ev_eq hy f
    rw [← hval] at ht
    filter_upwards [hc.preimage_mem_nhds ht, (isOpen_ptsIn U).mem_nhds hy] with z hz hzU
    refine ⟨hzU, hsub ?_⟩
    have hv : (fun f : Γ(X, U) => ev p σ U f z) = ⇑(evHom hzU) := funext fun f => ev_eq hzU f
    show ⇑(evHom hzU) ∈ t
    rw [← hv]
    exact hz

end GlobalTheory.ContRead
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory

theorem weight_cInf_semiPos_of_generated : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (B : LB X), B.IsLB → (∃ (n : ℕ) (u : Fin n → B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → ∃ (φ : Weight p σ B), φ.IsCInf ∧ ∀ D : ℕ, φ.SemiPosReg D := by
  intro k _ X p σ B hB ⟨n, u, hu⟩
  exact ⟨Weight.fsBasis p σ hB u hu 1 (by simp), Weight.isCInf_fsBasis hB u hu 1 (by simp),
    fun D => Weight.semiPosReg_fsBasis hB u hu 1 (by simp)⟩

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem weight_sub_cInf : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (B : LB X) (φ ψ : Weight p σ B), φ.IsCInf → ψ.IsCInf → ∃ u : CxPts p σ → ℝ, (∀ y, CInfAt u y) ∧ ∀ i, ∀ y ∈ ptsIn p σ (B.U i), ψ.φ i y = φ.φ i y + u y := by
  intro k _ X p σ B φ ψ hφ hψ
  have key : ∀ i y, y ∈ ptsIn p σ (B.U i) →
      ψ.φ i y - φ.φ i y = ψ.φ (pick φ.isLB y) y - φ.φ (pick φ.isLB y) y := by
    intro i y hi
    rw [ψ.trans _ i y (mem_pick φ.isLB y) hi, φ.trans _ i y (mem_pick φ.isLB y) hi]
    ring
  refine ⟨fun y => ψ.φ (pick φ.isLB y) y - φ.φ (pick φ.isLB y) y, fun y => ?_, fun i y hi => ?_⟩
  · have hy := mem_pick φ.isLB y
    have hs : CInfAt (fun z => ψ.φ (pick φ.isLB y) z + -φ.φ (pick φ.isLB y) z) y :=
      (hψ _ y hy).add (hφ _ y hy).neg
    refine hs.congr ?_
    filter_upwards [(isOpen_ptsIn _).mem_nhds hy] with z hz
    rw [← key _ z hz, sub_eq_add_neg]
  · have := key i y hi
    linarith

end GlobalTheory.Mix
end

section

set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.Published
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier

namespace GlobalTheory.FibreProj

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} [IsIntegral B] {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {d : ℕ}

theorem isProper_of_isArithVar {D : ℕ} (h : IsArithVar p D) : IsProper p := by
  obtain ⟨N, j, _, hj⟩ := h.isProjOver
  have := isProper_str k N
  exact hj ▸ inferInstance



end GlobalTheory.FibreProj
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WeightShift

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {B : LB Y}

theorem exists_semiPosReg_pow_addFn [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)]
    (R : AnRead p σ D) {φ : Weight p σ B} (h : φ.IsSmooth R) (hp : φ.StrictPos R)
    {v : CxPts p σ → ℝ} (hv : ∀ y, CInfAt v y) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ((φ.pow m).addFn v).SemiPosReg D := by
  have hA : IsAlgAtlas R.finAtlas := R.isAlgAtlas_finAtlas
  have hv' : R.SmoothOn univ v := (cInfAt_iff_smoothOn R isOpen_univ).1 fun y _ => hv y
  have hw : R.finAtlas.Smooth fun y => v y / 2 :=
    (hA.smooth_iff R).2 fun c => (hv' c).div_const 2
  have hΩ := h.isPotential hA
  have hpos := (h.isPosPot_iff hA).2 hp
  have hpsh : IsPsh R.finAtlas φ.locPot := fun x j z hz w => by
    by_cases h0 : w = 0
    · rw [h0, ReciprocityTheory.AnForm.levi_zero]
    · exact (hpos x j z hz w h0).le
  obtain ⟨C, hC⟩ := pshShift R.finAtlas φ.locPot hΩ hpos _ hw
  refine ⟨⌈C⌉₊, fun m hm i c y hy ξ => ?_⟩
  have hmC : 0 ≤ (m : ℝ) - C := sub_nonneg.2 (Nat.ceil_le.1 hm)
  have hχ : ((φ.pow m).addFn v).IsSmooth R := (h.zpow m).addFn hv'
  obtain ⟨j, hj⟩ := R.finAtlas.cover y
  obtain ⟨c', hc'⟩ := hA j
  rw [hc'] at hj
  have hb : y ∈ ptsIn p σ ((lbPow B m).U fun _ => pick φ.isLB y) :=
    mem_pow_iff.2 (mem_pick φ.isLB y)
  obtain ⟨w, -, e⟩ := hχ.exists_levi_eq c c' hy.1 hj hy.2 hb ξ
  rw [hχ.leviV_re_eq c hy.1 hy.2, e]
  have hz : c'.finChart y ∈ c'.finChart.target ∩ c'.finChart.symm ⁻¹' φ.locPot.U y :=
    mem_over c'.e hj (φ.locPot.mem_U y)
  have h₁ := hC y j (c'.finChart y) (by rw [hc']; exact ⟨hz.1, trivial, hz.2⟩) w
  have h₂ := hpsh y j (c'.finChart y) (by rw [hc']; exact hz) w
  rw [hc'] at h₁ h₂
  have d₁ : ContDiffAt ℝ 2 (((φ.pow m).addFn v).φ (fun _ => pick φ.isLB y) ∘ c'.finChart.symm)
      (c'.finChart y) := hχ.contDiffAt_finChart c' hj hb
  have d₂ : ContDiffAt ℝ 2 (φ.locPot.φ y ∘ c'.finChart.symm) (c'.finChart y) :=
    (h.contDiffAt_finChart c' hj (mem_pick φ.isLB y)).div_const 2
  have e₁ := ReciprocityTheory.AnForm.levi_add_smul (w := w) (C - m) (d₁.div_const 2) d₂
  rw [FinChart.levi_half] at e₁
  have e₂ : (LocPot.ofFun (fun y => v y / 2) + φ.locPot.rsmul C).φ y ∘ c'.finChart.symm =
      fun z => (((φ.pow m).addFn v).φ (fun _ => pick φ.isLB y) ∘ c'.finChart.symm) z / 2 +
        (C - m) * (φ.locPot.φ y ∘ c'.finChart.symm) z := by
    funext z
    have := φ.zpow_φ (m : ℤ) (fun _ => pick φ.isLB y) (c'.finChart.symm z)
    change v (c'.finChart.symm z) / 2 + C * (φ.φ (pick φ.isLB y) (c'.finChart.symm z) / 2) =
      ((φ.zpow (m : ℤ)).φ (fun _ => pick φ.isLB y) (c'.finChart.symm z) + v (c'.finChart.symm z)) / 2 +
        (C - m) * (φ.φ (pick φ.isLB y) (c'.finChart.symm z) / 2)
    rw [this]
    push_cast
    ring
  rw [e₂, e₁] at h₁
  nlinarith [mul_nonneg hmC h₂]

theorem strictPos_fsO1 (N : ℕ) (R : AnRead (PSpace.str k N) σ N) :
    (ProjAn.fsO1 k σ N).StrictPos R := fun i c y hy ξ h0 => by
  have := ProjPos.fubiniStudy_weight_pullback_closed_immersion_strictPos (σ := σ) (𝟙 _) (Category.id_comp (PSpace.str k N)) R
    (fun _ => i) c y ⟨hy.1, mem_ptsIn.2 (Set.mem_iInter.2 fun _ => mem_ptsIn.1 hy.2)⟩ ξ h0
  have e (z) : ((ProjAn.fsO1 k σ N).pull (𝟙 _) (Category.id_comp (PSpace.str k N))).φ (fun _ => i) z =
      (ProjAn.fsO1 k σ N).φ i z := by
    refine (Weight.pull_φ _ _ _ _ _).trans ?_
    have e : PtsOver.map (𝟙 _) (Category.id_comp (PSpace.str k N)) _ z = z :=
      Subtype.ext (Category.comp_id _)
    erw [e]
  simpa only [e] using this

theorem exists_semiPosReg_fubiniStudy : ∀ (k : Type) [CommRing k] (σ : k →+* ℂ) (N : ℕ) (v : CxPts (PSpace.str k N) σ → ℝ), (∀ y, CInfAt v y) → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ((((ProjSpace.hermitianTwistingSheaf k N).φ σ).pow m).addFn v).SemiPosReg N := fun k _ σ N v hv =>
  haveI : T2Space (CxPts (PSpace.str k N) σ) :=
    CxPts.t2Space_cxPts_of_isProjOver σ ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩
  exists_semiPosReg_pow_addFn (AnRead.all _ σ N)
    ((Weight.isCInf_iff_isSmooth _).1 ((ProjSpace.hermitianTwistingSheaf k N).cInf σ)) (strictPos_fsO1 N _) hv

end GlobalTheory.WeightShift
end
end
