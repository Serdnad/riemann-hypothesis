module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1225
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1180
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1249
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1103
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAffineNeighbourhoodExists
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.DifferentiableAtChart
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle003
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpbHessAtAddConst
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1270
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem lie_psi_cl_eq_tanVal (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ)
    (hN : (p : R) ^ N = 0) (A : Over (Sp R)) [GrpObj A] (hA : IsAbelianScheme A)
    (G : PDivGroup p R) (t : PDivGroup.TorsionTower G A)
    (ψ : PrimitiveSubmodule A →ₗ[R] G.omega)
    (hψ : ∀ c : PrimitiveSubmodule A, GlobalTheory.PtExt.IsCan t c.1 (G.rigOfOmega (ψ c)))
    (β : Form (A.hom ≫ 𝟙 _)) (hβ : Form.cl _ β ∈ primDR A)
    (hF : (⟨_, hβ⟩ : primDR A) ∈ PrimitiveSubmodule A) (x : G.Lie) (v : epsR R ⟶ A)
    (hx : t.LieCorr x v) : x (ψ ⟨_, hF⟩) = tanVal v β := by
  obtain ⟨w, hw1, hw2⟩ := isCan_form R A p G t β hβ
  have hw : ψ ⟨_, hF⟩ = w :=
    PDivGroup.rigOfOmega_injective_of_pow p R N hN G
      (isCan_unique R A p G t ⟨_, hβ⟩ hA _ _ (hψ ⟨_, hF⟩) hw2)
  rw [hw]
  exact lie_cotVal_eq_tanVal R A p G t ⟨N, hN⟩ β w hw1 x v hx

end GlobalTheory.PtExt
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.bialgebraPullbackTwoVariables_res_cocycle_eq
    (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (n : ℕ) :
    pullbackTwo (G.res n) (d.coc (n + 1)) = d.coc n :=
  Dat.pullTwo_res_coc R A p G t c d n
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem contr_chern_eq_tanCoc : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v → ∀ (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι), IsChoice P j → ∀ w : Z2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)), IsChern (dp0 R) _ P (CatCoh.H2.mk _ w) → (∀ (T T' T'' : Thick (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) (a : T ⟶ T') (b : T' ⟶ T''), T.J = ⊥ → T'.J = ⊥ → T''.J = ⊥ → w.1 T T' T'' a b = 0) → ∀ κ : Fn1 A, IsContr w.1 v κ → ∃ u : Fn1 (A ⊗ B), IsCoc P.U u ∧ Cohom (chartsA P) κ ((tanCoc P j v).add (sndPull u v)) := by
  intro R _ A B _ _ P hP v hv j hj w hch hw κ hκ
  obtain ⟨i, hi, U, ℓ, hU, hℓ, hcl⟩ := hch
  rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk] at hcl
  obtain ⟨n, hn⟩ := hcl
  refine ⟨cocOf P.U n, ?_, ?_⟩
  · apply GlobalTheory.PtExt.isCoc_cocOf
    intro T T' T'' a b h h' h''
    have e := congrFun (congrFun (congrFun (congrFun (congrFun hn T) T') T'') a) b
    rw [e]
    have h0 : ℓ.1 T T' T'' a b = 0 := by
      have hm := (hℓ T T' T'' a b).1
      rw [h''] at hm
      exact Ideal.mem_bot.mp hm
    change w.1 _ _ _ _ _ - ℓ.1 T T' T'' a b = 0
    rw [h0, sub_zero]
    exact hw _ _ _ _ _ h h' h''
  · exact GlobalTheory.T.chernCocycle_tangentContraction_cohomologous_torsor
      R A B P hP v hv j hj w hw i hi U ℓ hU hℓ n hn κ hκ

end GlobalTheory.PtExt
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory

theorem addGroupFG_sec_of_isArithVar : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ B : LB X, B.IsLB → AddGroup.FG B.Sec := by
  intro k _ X _ p D h B hB
  letI : Algebra k Γ(X, ⊤) :=
    ((Scheme.Hom.appTop p).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).toAlgebra
  have hf : ∀ r : k, algebraMap k Γ(X, ⊤) r =
      (Scheme.Hom.appTop p) ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r) := fun _ => rfl
  haveI := h.finite
  haveI : IsNoetherianRing k := isNoetherian_of_tower ℤ inferInstance
  have hfin : Module.Finite k (coh (twist (QCoh.structureModule X) B) 0) :=
    finite_coh_twist_of_isProjOver hf (QCoh.structureModule X) h.isProjOver hB 0
  haveI : Module.Finite ℤ (coh (twist (QCoh.structureModule X) B) 0) := Module.Finite.trans k _
  have hfg : AddGroup.FG (coh (twist (QCoh.structureModule X) B) 0) :=
    Module.Finite.iff_addGroup_fg.mp inferInstance
  exact AddGroup.fg_of_surjective (f := (cohZeroTwistEquiv B).toAddEquiv.toAddMonoidHom)
    (cohZeroTwistEquiv B).toAddEquiv.surjective

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HermLB

open Set GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic
open ReciprocityTheory.L2DbarEstimates (V leviV)

theorem semiPos_pull_of_genSmooth : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k)
    (q : Y ⟶ Sp k) (D E : ℕ), GenSmooth p D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p),
    L.SemiPos D → (L.pull π hπ).SemiPos E := by
  intro k _ X Y p q D E hX π hπ L hL σ
  obtain ⟨R⟩ := hX σ
  intro i c y hy ξ
  set φ := L.φ σ
  set m := PtsOver.map π hπ (spMap σ)
  have hm : ∀ z, (m z).1 = z.1 ≫ π := fun _ => rfl
  obtain ⟨a, h0⟩ := R.cover (m y)
  set c0 := R.chart a
  have him : m y ∈ ptsIn p σ (L.B.U (i PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => m y) (fun _ => rfl) hy.2 PUnit.unit
  set F : V E → V D := c0.e ∘ m ∘ c.e.symm with hFdef
  set U := c.e.target ∩ c.e.symm ⁻¹' (m ⁻¹' c0.e.source)
  have hU : IsOpen U := GlobalTheory.ChartGlue.isOpen_over c.e (c0.e.open_source.preimage (continuous_of_comp hm))
  have hyU : c.e y ∈ U := GlobalTheory.ChartGlue.mem_over c.e hy.1 h0
  have hF0 : DifferentiableOn ℂ F U := AlgChart.holo_map hm c c0
  have hF : ContDiffOn ℂ 2 F U := (contDiffOn_piLp 2).2 fun a =>
    (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn E _ U hU
      (differentiableOn_euclidean.1 hF0 a)).of_le (by norm_cast)
  have hFy : F (c.e y) = c0.e (m y) := by
    simp only [hFdef, Function.comp_apply, c.e.left_inv hy.1]
  set g : V D → ℂ := fun v => (φ.φ (i PUnit.unit) (c0.e.symm v) : ℂ) with hgdef
  have hg : ContDiffAt ℝ 2 g (F (c.e y)) := hFy ▸
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((L.cInf σ).contDiffAt c0 h0 him)
  have e : (fun v => ((L.pull π hπ).φ σ |>.φ i (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)] g ∘ F := by
    filter_upwards [hU.mem_nhds hyU] with v hv
    have := Weight.pull_φ φ π hπ i (c.e.symm v)
    simp only [g, hFdef, Function.comp_apply, c0.e.left_inv hv.2]
    exact congrArg _ this
  show 0 ≤ (leviV E (fun v => ((L.pull π hπ).φ σ |>.φ i (c.e.symm v) : ℂ)) (c.e y) ξ).re
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr e,
    ReciprocityTheory.ChartRestriction.G.AR.Up.RGF.gc_leviV_comp E D g F U hU _ hyU hF hg ξ, hFy]
  exact hL σ (i PUnit.unit) c0 (m y) ⟨h0, him⟩ _

end GlobalTheory.HermLB
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

open Filter Topology Set
open scoped ContDiff

namespace GlobalTheory.HessPull


open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives ReciprocityTheory.L2DbarEstimates.Y ReciprocityTheory.ChartRestriction.G.AR.Up.RGF in
theorem cHess_comp_apply (n d : ℕ) (g : V d → ℂ) (F : V n → V d) (U : Set (V n)) (hU : IsOpen U)
    (v : V n) (hv : v ∈ U) (hF : ContDiffOn ℂ 2 F U) (hg : ContDiffAt ℝ 2 g (F v)) (j k : Fin n) :
    cHess n (g ∘ F) v j k = ∑ a, ∑ b,
      cHess d g (F v) b a * fderiv ℂ F v (bas n j) b *
        (starRingEnd ℂ) (fderiv ℂ F v (bas n k) a) := by
  have hFd : ∀ y ∈ U, HasFDerivAt F (fderiv ℂ F y) y := fun y hy =>
    (((hF.differentiableOn (by norm_num)) y hy).differentiableAt (hU.mem_nhds hy)).hasFDerivAt
  have hgev : ∀ᶠ y in 𝓝 v, ContDiffAt ℝ 2 g (F y) :=
    (hFd v hv).continuousAt.eventually (hg.eventually (by simp))
  have hwdb : ∀ k, wdb n k (g ∘ F) =ᶠ[𝓝 v]
      fun y => ∑ a, wdb d a g (F y) * (starRingEnd ℂ) (fderiv ℂ F y (bas n k) a) := by
    intro k
    filter_upwards [hgev, hU.mem_nhds hv] with y hy hyU
    exact gc_wdb_comp n d g F _ y (hy.differentiableAt (by simp)) (hFd y hyU) k
  have hD : DifferentiableAt ℝ (fderiv ℝ g) (F v) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hWg : ∀ a, DifferentiableAt ℝ (wdb d a g) (F v) := by
    intro a
    show DifferentiableAt ℝ (fun y => (fderiv ℝ g y (bas d a) +
      Complex.I * fderiv ℝ g y (Complex.I • bas d a)) / 2) (F v)
    have h1 := hD.clm_apply (differentiableAt_const (bas d a))
    have h2 := hD.clm_apply (differentiableAt_const (Complex.I • bas d a))
    have h3 := (h1.add (h2.const_mul Complex.I)).mul_const ((2 : ℂ)⁻¹)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    simp [div_eq_mul_inv]
  have hWa : ∀ a, DifferentiableAt ℝ (fun y => wdb d a g (F y)) v := fun a =>
    (hWg a).comp v ((hFd v hv).restrictScalars ℝ).differentiableAt
  have hDF : DifferentiableAt ℂ (fun y => fderiv ℂ F y) v :=
    ((hF.fderiv_of_isOpen hU (m := 1) (by norm_num)).contDiffAt (hU.mem_nhds hv)).differentiableAt
      (by norm_num)
  have hPa : ∀ k a, DifferentiableAt ℂ (fun y => fderiv ℂ F y (bas n k) a) v := fun k a =>
    (differentiableAt_piLp 2).1 (hDF.clm_apply (differentiableAt_const _)) a
  have hCa : ∀ k a, DifferentiableAt ℝ
      (fun y => (starRingEnd ℂ) (fderiv ℂ F y (bas n k) a)) v := by
    intro k a
    have := Complex.conjCLE.differentiableAt.comp v ((hPa k a).restrictScalars ℝ)
    simpa [Function.comp_def] using this
  show wd n j (wdb n k (g ∘ F)) v = _
  rw [wd_congr n j _ _ v (hwdb k),
    fc_wd_sum n j Finset.univ (fun a y => wdb d a g (F y) *
      (starRingEnd ℂ) (fderiv ℂ F y (bas n k) a)) v (fun a _ => (hWa a).mul (hCa k a))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [wd_mul' n j _ _ v (hWa a) (hCa k a), wd_conj', fc_wdb_holo n _ v (hPa k a) j, map_zero,
    mul_zero, add_zero]
  have := gc_wd_comp n d (wdb d a g) F (fderiv ℂ F v) v (hWg a) (hFd v hv) j
  rw [show (fun y => wdb d a g (F y)) = wdb d a g ∘ F from rfl, this, Finset.sum_mul]
  rfl

end GlobalTheory.HessPull

namespace GlobalTheory.HessPull

open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open GlobalTheory.ChartGlue

theorem hess_pull_factor : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k)
    (f : Y ⟶ B) (w : f ≫ q = p) (σ : k →+* ℂ) (D d : ℕ) (c : AlgChart p σ D) (c' : AlgChart q σ d)
    (y : CxPts p σ), y ∈ c.e.source → PtsOver.map f w (spMap σ) y ∈ c'.e.source →
    ∃ (P : Matrix (Fin D) (Fin d) ℂ) (Q : Matrix (Fin d) (Fin D) ℂ), ∀ (A : HermLB q)
      (i : (A.pull f w).B.ι), y ∈ ptsIn p σ ((A.pull f w).B.U i) →
        ∃ K : Matrix (Fin d) (Fin d) ℂ, c.hess ((A.pull f w).φ σ) i y = P * K * Q := by
  intro k _ B Y q p f w σ D d c c' y hy hy'
  set m := PtsOver.map f w (spMap σ)
  have hm : ∀ z, (m z).1 = z.1 ≫ f := fun _ => rfl
  set F : V D → V d := c'.e ∘ m ∘ c.e.symm with hFdef
  set U := c.e.target ∩ c.e.symm ⁻¹' (m ⁻¹' c'.e.source)
  have hU : IsOpen U := isOpen_over c.e (c'.e.open_source.preimage (continuous_of_comp hm))
  have hyU : c.e y ∈ U := mem_over c.e hy hy'
  have hF0 : DifferentiableOn ℂ F U := AlgChart.holo_map hm c c'
  have hF : ContDiffOn ℂ 2 F U := (contDiffOn_piLp 2).2 fun a =>
    (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ U hU
      (differentiableOn_euclidean.1 hF0 a)).of_le (by norm_cast)
  have hFy : F (c.e y) = c'.e (m y) := by
    simp only [hFdef, Function.comp_apply, c.e.left_inv hy]
  refine ⟨Matrix.of fun j b => fderiv ℂ F (c.e y) (bas D j) b,
    Matrix.of fun a k => (starRingEnd ℂ) (fderiv ℂ F (c.e y) (bas D k) a), ?_⟩
  intro A i hi
  have him : m y ∈ ptsIn q σ (A.B.U (i PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => m y) (fun _ => rfl) hi PUnit.unit
  set g : V d → ℂ := fun v => ((A.φ σ).φ (i PUnit.unit) (c'.e.symm v) : ℂ)
  have hg : ContDiffAt ℝ 2 g (F (c.e y)) := hFy ▸
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((A.cInf σ).contDiffAt c' hy' him)
  have e : (fun v => (((A.pull f w).φ σ).φ i (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)] g ∘ F := by
    filter_upwards [hU.mem_nhds hyU] with v hv
    have := Weight.pull_φ (A.φ σ) f w i (c.e.symm v)
    simp only [g, hFdef, Function.comp_apply, c'.e.left_inv hv.2]
    exact congrArg _ this
  refine ⟨cHess d g (F (c.e y)), ?_⟩
  show cHess D _ (c.e y) = _
  rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e]
  ext j k
  rw [cHess_comp_apply D d g F U hU _ hyU hF hg j k, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

end GlobalTheory.HessPull
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.GenEtale

theorem exists_opens_etale : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ V : Y.Opens, (V : Set Y).Nonempty ∧ Etale (V.ι ≫ π) := by
  intro k _ X Y _ _ p q D hp hq π hπ hη hd
  have := GlobalTheory.SchemeWords.isProper_of_isProjOver hp.isProjOver
  have : IsProper (π ≫ p) := hπ ▸ GlobalTheory.SchemeWords.isProper_of_isProjOver hq.isProjOver
  have : IsProper π := IsProper.of_comp π p
  have := hp.isLocallyNoetherian
  have := hp.charZero
  obtain ⟨U, -, hU, hxU, hW, -, hE, -⟩ :=
    GlobalTheory.GenFiniteEtale.exists_finite_etale_of_isProper π hη hd ⊤ (Opens.mem_top _)
  refine ⟨π ⁻¹ᵁ U, ⟨genericPoint Y, show π _ ∈ U from hη ▸ hxU⟩, ?_⟩
  have : IsAffine U := hU
  have : IsAffine (π ⁻¹ᵁ U) := hW
  have hE' : ∀ U' : X.Opens, U' = U → (π.app U').hom.Etale := by
    rintro _ rfl
    exact hE
  have e : U.ι ''ᵁ ⊤ = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  have h1 : Etale (π ∣_ U) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), morphismRestrict_appTop]
    exact (RingHom.Etale.respectsIso).cancel_right_isIso _ _ |>.2 (hE' _ e)
  rw [← morphismRestrict_ι]
  infer_instance

end GlobalTheory.GenEtale
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.regularAt_iff_forall_specializes_ord_add_mult_nonneg : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (D : CartierDiv X) (x : X) (f : X.functionFieldˣ), D.RegularAt x (f : X.functionField) ↔ ∀ z, z ⤳ x → 0 ≤ Scheme.ord (f : X.functionField) z + D.mult z := by
  first | exact @GlobalTheory.RegCodimOne.regularAt_iff_forall_specializes | exact GlobalTheory.RegCodimOne.regularAt_iff_forall_specializes | (intros; apply GlobalTheory.RegCodimOne.regularAt_iff_forall_specializes <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

set_option autoImplicit false
noncomputable section
open GlobalTheory.Cartier.CartierDiv
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.Cartier.EffDiff

variable {X : Scheme.{0}} [IsIntegral X]

theorem exists_pow_regAt {V : X.Opens} (hV : IsAffineOpen V) (τ : Γ(X, V))
    (hη : genericPoint X ∈ X.basicOpen τ) {f : X.functionField}
    (hf : ∀ x ∈ X.basicOpen τ, RegAt x f) :
    ∃ m : ℕ, ∀ x ∈ V, RegAt x (f * fnOf V (X.basicOpen_le τ hη) τ ^ m) := by
  obtain ⟨b, hb⟩ := exists_fnOf_eq hη hf
  haveI := hV.isLocalization_basicOpen τ
  obtain ⟨m, a, e⟩ := IsLocalization.Away.surj τ b
  refine ⟨m, fun x hx => ?_⟩
  have e' := congrArg (fnOf _ hη) e
  rw [map_mul, map_pow, hb] at e'
  have h1 : ∀ c : Γ(X, V), fnOf _ hη (algebraMap Γ(X, V) Γ(X, X.basicOpen τ) c) =
      fnOf V (X.basicOpen_le τ hη) c := fun c => fnOf_resG (X.basicOpen_le τ) hη c
  rw [h1, h1] at e'
  rw [e']
  exact regAt_fnOf hx _ a

theorem eventually_eff_add_nsmul [CompactSpace X] {L : LB X} (hL : L.IsLB) (t : L.Sec)
    (ht : genericPoint X ∈ nonzeroLocus t) (D : CartierDiv X)
    (hD : ∀ x ∈ nonzeroLocus t, D.RegularAt x 1) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → (D + N • divOfSec hL t ht).Eff := by
  have key : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ∃ m : ℕ, ∀ N, m ≤ N → ∀ y ∈ V,
      (D + N • divOfSec hL t ht).RegularAt y 1 := by
    intro x
    obtain ⟨W, hxW, h, hh⟩ := D.exists_isEqn_nhds x
    obtain ⟨i, hi⟩ := exists_chart hL x
    obtain ⟨V, hVa, hxV, hVle⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show x ∈ W ⊓ L.U i from ⟨hxW, hi⟩)
    have hVW : V ≤ W := hVle.trans inf_le_left
    have hVi : V ≤ L.U i := hVle.trans inf_le_right
    set τ : Γ(X, V) := resG X hVi (t.f i)
    have hbo : ∀ y, y ∈ X.basicOpen τ ↔ y ∈ V ∧ y ∈ nonzeroLocus t := fun y => by
      have hb : X.basicOpen τ = V ⊓ X.basicOpen (t.f i) := X.basicOpen_res _ _
      rw [hb]
      exact ⟨fun hy => ⟨hy.1, (mem_nonzeroLocus_iff t i (hVi hy.1)).2 hy.2⟩,
        fun hy => ⟨hy.1, (mem_nonzeroLocus_iff t i (hVi hy.1)).1 hy.2⟩⟩
    have hη : genericPoint X ∈ X.basicOpen τ := (hbo _).2 ⟨gen_mem hxV, ht⟩
    obtain ⟨m, hm⟩ := exists_pow_regAt hVa τ hη (f := h) fun y hy => by
      obtain ⟨hyV, hyt⟩ := (hbo y).1 hy
      have := (hh y (hVW hyV)).regularAt_iff.1 (hD y hyt)
      rwa [one_mul] at this
    refine ⟨V, hxV, m, fun N hN y hyV => ?_⟩
    have hT := (presents_divOfRatSec hL (isRatSec_ratOfSec t ht)).isEqn i y (hVi hyV)
    refine ⟨_, (hh y (hVW hyV)).add (hT.nsmul N), ?_⟩
    have e : (ratOfSec t ht i : X.functionField) = fnOf V (X.basicOpen_le τ hη) τ := by
      rw [val_ratOfSec (gen_mem (hVi hyV)), fnOf_resG]
    rw [one_mul, Units.val_mul, Units.val_pow_eq_pow_val, e, ← Nat.add_sub_cancel' hN, pow_add,
      ← mul_assoc]
    have hp := regAt_fnOf hyV (X.basicOpen_le τ hη) (τ ^ (N - m))
    rw [map_pow] at hp
    exact (hm y hyV).mul hp
  choose V hxV m hm using key
  obtain ⟨S, hS⟩ := exists_finset_iSup_eq_top V hxV
  refine ⟨S.sup m, fun N hN y => ?_⟩
  obtain ⟨x, hy⟩ := Opens.mem_iSup.1 (hS.ge (Set.mem_univ y))
  exact hm x N ((Finset.le_sup x.2).trans hN) y hy

end GlobalTheory.Cartier.EffDiff

theorem GlobalTheory.Cartier.EffDiff.exists_eff_and_add_eff : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (H : LB X),
    IsAmpleLB H → ∀ D : CartierDiv X, ∃ E : CartierDiv X, E.Eff ∧ (D + E).Eff := by
  intro X _ _ H hH D
  haveI := hH.compactSpace
  obtain ⟨W, hηW, g, hg⟩ := D.exists_isEqn_nhds (genericPoint X)
  obtain ⟨n, -, t, hηt, htW, hU⟩ := hH.exists_affine_le hηW
  have hL := isLB_lbPow hH.isLB n
  haveI : Nonempty (nonzeroLocus t) := ⟨⟨_, hηt⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen X _ hU
  obtain ⟨a, c, hc, e⟩ := IsFractionRing.div_surjective (A := Γ(X, nonzeroLocus t))
    (g : X.functionField)
  have hfn : ∀ b : Γ(X, nonzeroLocus t),
      algebraMap Γ(X, nonzeroLocus t) X.functionField b = fnOf _ hηt b := fun _ => rfl
  have hc0 : fnOf _ hηt c ≠ 0 := by
    rw [← hfn]; exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hc
  obtain ⟨N₁, h₁⟩ := eventually_eff_add_nsmul hL t hηt (principal (Units.mk0 _ hc0))
    fun x hx => ⟨_, isEqn_principal _ x, by rw [one_mul, Units.val_mk0]; exact regAt_fnOf hx hηt c⟩
  obtain ⟨N₂, h₂⟩ := eventually_eff_add_nsmul hL t hηt (D + principal (Units.mk0 _ hc0))
    fun x hx => ⟨_, (hg x (htW hx)).add (isEqn_principal _ x), by
      rw [one_mul, Units.val_mul, Units.val_mk0, ← e, hfn, hfn, div_mul_cancel₀ _ hc0]
      exact regAt_fnOf hx hηt a⟩
  refine ⟨principal (Units.mk0 _ hc0) + max N₁ N₂ • divOfSec hL t hηt, h₁ _ (le_max_left _ _), ?_⟩
  rw [← add_assoc]
  exact h₂ _ (le_max_right _ _)
end
end
