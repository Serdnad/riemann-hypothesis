module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Formalism.LocalToGlobal.ProjectiveLattices.VAddIntNonneg
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle027
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
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.UnivChartLoc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeB
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem pos_ppx_le {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i := by
  intro p hp
  have hp' : ∀ k, p ∈ (snd (Over.mk x') Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) :=
    Set.mem_iInter.1 hp
  have e := congrArg (fun f : Gx x' ⟶ Xo.univ.t.G.left => f.base p) hs
  show pm.base p ∈ ⋂ k, (snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
  refine Set.mem_iInter.2 fun k => ?_
  show (pm ≫ (snd (Over.mk x) Xo.univ.t.G).left).base p ∈ (Xo.univ.t.PP.L.U (i k) : Set _)
  rw [e]
  exact hp' k

set_option synthInstance.maxHeartbeats 400000 in
theorem pos_frMap (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) {K₁ K₂ : Type}
    [Field K₁] [Field K₂] [Algebra c.F K₁] [Algebra c.F K₂] (φ : K₁ →ₐ[c.F] K₂) (y : FrPt Xo c K₁) :
    ∃ z : FrPt Xo c K₂, FrMap φ y z := by
  classical
  let _ : Algebra K₁ K₂ := φ.toRingHom.toAlgebra
  have htow : ∀ r : c.F, algebraMap c.F K₂ r = algebraMap K₁ K₂ (algebraMap c.F K₁ r) := fun r => (φ.commutes r).symm
  have : FaithfulSMul K₁ K₂ := (faithfulSMul_iff_algebraMap_injective K₁ K₂).2 (algebraMap K₁ K₂).injective
  letI : GrpObj Xo.univ.t.G := Xo.univ.t.grp
  letI : GrpObj ((Over.pullback y.x).obj Xo.univ.t.G) :=
    Functor.grpObjObj (F := Over.pullback y.x) (G := Xo.univ.t.G)
  obtain ⟨n, xc, hx⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc ((Over.pullback y.x).obj Xo.univ.t.G)
  have hco : ∀ τ i, ∃ cc, y.u τ i = gfpVec y.x xc cc := fun τ i => gfp_exists hx _ (y.tan τ i)
  choose d hdu using hco
  have hdW : ∀ τ i, d τ i ∈ gfpEig (c := c) hx τ := fun τ i =>
    (gfp_eig_iff hx τ _).1 (by rw [← hdu τ i]; exact y.eig τ i)
  have hd : ∀ τ, LinearIndependent K₁ (d τ) := by
    intro τ
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hu : y.u τ = fun i => gfpVec y.x xc (d τ i) := funext (hdu τ)
    have h0 : (0 : Fin n → K₁) ∈ gfpEig (c := c) hx τ := Submodule.zero_mem _
    obtain ⟨a, -, ha⟩ := y.basis τ (gfpVec y.x xc 0) (gfp_tan hx 0) ((gfp_eig_iff hx τ 0).2 h0)
    have e1 : IsCombAt y.x (y.u τ) g (gfpVec y.x xc 0) := by
      rw [hu]
      exact (gfp_comb_iff hx (d τ) g 0).2 hg.symm
    have e2 : IsCombAt y.x (y.u τ) 0 (gfpVec y.x xc 0) := by
      rw [hu]
      exact (gfp_comb_iff hx (d τ) 0 0).2 (by simp)
    have e3 := (ha g e1).trans (ha 0 e2).symm
    exact fun i => congrFun e3 i
  obtain ⟨xc', hx', hv, htm⟩ := gfp_bc (L' := K₂) hx
  have hx0' := gfp_over_bc htow y.x_over
  have hW' : ∀ τ j, (algebraMap K₁ K₂ ∘ d τ j) ∈ gfpEig (c := c) hx' τ := by
    intro τ j
    have h0 := hdW τ j
    unfold gfpEig at h0 ⊢
    rw [ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff] at h0 ⊢
    intro a
    rw [htm a (d τ j), h0 a]
    funext k
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, htow]
  have hli : ∀ τ, LinearIndependent K₂ (fun i => algebraMap K₁ K₂ ∘ d τ i) := fun τ =>
    linearIndependent_algebraMap_comp_iff.mpr (hd τ)
  refine ⟨⟨spMap (algebraMap K₁ K₂) ≫ y.x, hx0', fun τ i => gfpVec _ xc' (algebraMap K₁ K₂ ∘ d τ i),
    fun τ i => gfp_tan hx' _, fun τ i => (gfp_eig_iff hx' τ _).2 (hW' τ i),
    fun τ w hw he => gfp_basis hx0' hx' τ _ (hli τ) (hW' τ) w hw he,
    ReciprocityTheory.ChartRestriction.G.PullbackSections.secCP (ReciprocityTheory.ChartRestriction.G.PullbackSections.cpS (algebraMap K₁ K₂) y.x) y.s,
    fun s' => ReciprocityTheory.ChartRestriction.G.PullbackSections.genBC_frame y.x hS hT (algebraMap K₁ K₂) y.s y.gen s'⟩, rfl, fun τ i => ?_,
    ReciprocityTheory.ChartRestriction.G.PullbackSections.bcPm (algebraMap K₁ K₂) y.x, ReciprocityTheory.ChartRestriction.G.PullbackSections.bcPm_snd _ _, ReciprocityTheory.ChartRestriction.G.PullbackSections.bcPm_fst _ _,
    fun i h => rfl⟩
  show gfpVec _ xc' (algebraMap K₁ K₂ ∘ d τ i) = spMap (dualMap φ.toRingHom) ≫ y.u τ i
  rw [hdu τ i]
  exact hv (d τ i)

end Formalism.L2.Pj
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory Formalism.L2.Theta
open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.L2.Pj

variable {D : D7}

def VolPairEx (V : HSp D) : Prop := ∃ p : Measure (GA D V) × Set (GA D V), IsVolPair D V p.1 p.2

theorem volPair_eq_choose (V : HSp D) (h : VolPairEx V) : volPair V = h.choose := by
  unfold volPair
  exact dif_pos h

theorem volPair_isVolPair (V : HSp D) (h : VolPairEx V) : IsVolPair D V (volPair V).1 (volPair V).2 := by
  rw [volPair_eq_choose V h]
  exact h.choose_spec

theorem autMk_measurable (V : HSp D) : Measurable (autMk V) := by
  first
  | exact measurable_quotient_mk'
  | exact fun _ hs => hs

theorem muQ_univ (V : HSp D) : muQ V Set.univ = (volPair V).1 (volPair V).2 := by
  unfold muQ
  rw [Measure.map_apply (autMk_measurable V) MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply_univ]

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)
  (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop)

def algCls (T : CDVR) (ι : c.F →+* T.Fr) (y : IntFr Xo c T ι) : Prop := y.IsAlg

def valSet (la : HeightOneSpectrum (𝓞 c.F)) : Set (Rul Xo c → EReal) :=
  Set.range (vAtV : PtV Xo c cls Unit (fun _ _ _ _ => True) la → Rul Xo c → EReal)

variable {Xo c cls}

theorem isVal_vAt {PY : Type} {lies : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY → Prop}
    {la : HeightOneSpectrum (𝓞 c.F)} (y : PtV Xo c cls PY lies la) : IsVal la (vAtV y) :=
  ⟨vAtV_zero y, vAtV_ne_bot y, vAtV_add y, fun a f ha => vAtV_smul y a f ha, vAtV_mul y⟩

theorem isVal_valSet (la : HeightOneSpectrum (𝓞 c.F)) : ∀ v ∈ valSet Xo c cls la, IsVal la v := by
  rintro _ ⟨y, rfl⟩
  exact isVal_vAt y

variable (Xo c cls)

def LiesTotal (PY : HeightOneSpectrum (𝓞 c.F) → Type)
    (lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop) : Prop :=
  ∀ la (T : CDVR) (ι : c.F →+* T.Fr) (e : ℕ), OverLa la T.V ι e → ∀ y : IntFr Xo c T ι, cls T ι y →
    ∃ η, lies la T ι y η

variable {Xo c cls}

theorem nonneg_iff_of_liesTotal {PY : HeightOneSpectrum (𝓞 c.F) → Type}
    {lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop}
    (h : LiesTotal Xo c cls PY lies) (f : Rul Xo c) :
    (∀ la, ∀ v ∈ valSet Xo c cls la, 0 ≤ v f) ↔
      ∀ la (y : PtV Xo c cls (PY la) (lies la) la), 0 ≤ vAtV y f := by
  constructor
  · rintro h0 la ⟨q, T, ι, e, ho, y, hy, η, hη, rfl⟩
    exact h0 la _ ⟨PtV.mk la ho y hy () trivial, rfl⟩
  · rintro h0 la _ ⟨⟨q, T, ι, e, ho, y, hy, η, hη, rfl⟩, rfl⟩
    obtain ⟨η', hη'⟩ := h la T ι e ho y hy
    exact h0 la (PtV.mk la ho y hy η' hη')

end Formalism.L2.Pj
end
end

section

noncomputable section

open scoped TensorProduct
open MeasureTheory NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.L2.Pj

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

abbrev FDSec (X : Comp → Data E r) : Type := ∀ c, Frame (X c).Ψ r → ℂ

abbrev FPt (X : Comp → Data E r) : Type := Σ c, ((X c).dom : Set (Frame (X c).Ψ r))

def IsHolCusp (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) : Prop :=
  ∀ c, P c ∈ (X c).SS (la c)

def supE (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) : ENNReal :=
  ⨆ p : FPt X, ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2)

def supN (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) : ℝ := (supE X la P).toReal

theorem pnorm_fac_nonneg (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) :
    0 ≤ ∏ τ, ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) := Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _

theorem pnorm_add_le (X : Data E r) (la : Wt X.Ψ r) (P Q : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la (P + Q) x ≤ X.pnorm la P x + X.pnorm la Q x := by
  simp only [Data.pnorm, Pi.add_apply]
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (pnorm_fac_nonneg X la x)

theorem pnorm_smul (X : Data E r) (la : Wt X.Ψ r) (a : ℂ) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la (a • P) x = ‖a‖ * X.pnorm la P x := by
  simp only [Data.pnorm, Pi.smul_apply, smul_eq_mul, norm_mul]
  ring

theorem pnorm_zero (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) : X.pnorm la 0 x = 0 := by
  simp [Data.pnorm]

def holSub (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) : Submodule ℂ (FDSec X) :=
  Submodule.span ℂ {P | IsHolCusp X la P}

theorem holCusp_mem_holSub (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) {P : FDSec X}
    (h : IsHolCusp X la P) : P ∈ holSub X la := Submodule.subset_span h

def dmet (n f r : ℕ) : ℝ := Real.exp ((n : ℝ) * f * r * (-(1 / 2) * Real.log (2 * Real.pi)) / 2)

theorem supN_nonneg (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) : 0 ≤ supN X la P := ENNReal.toReal_nonneg

variable (V : HSp D)

def adel {X : Comp → Data E r} (dict : GA D V → Σ c, Frame (X c).Ψ r) (mu : GA D V → ℂ) :
    FDSec X →ₗ[ℂ] (GA D V → ℂ) where
  toFun P := fun g => mu g * P (dict g).1 (dict g).2
  map_add' P Q := by funext g; simp [mul_add]
  map_smul' a P := by funext g; simp [mul_left_comm]

def onQ : (GA D V → ℂ) →ₗ[ℂ] (AutQ V → ℂ) where
  toFun φ := fun q => φ q.out
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def SS {X : Comp → Data E r} (la : ∀ c, Wt (X c).Ψ r) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) : Submodule ℂ (Lp ℂ 2 (muQ1 V)) :=
  Submodule.span ℂ {F | ∃ P : FDSec X, IsHolCusp X la P ∧
    ∃ h : MemLp (onQ V (adel V dict mu P)) 2 (muQ1 V), F = h.toLp _}

variable {K : Type} [Field K] {C : Type} [AddCommGroup C] [Module K C] (σ : K →+* ℂ)

def jFn {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) : C →ₛₗ[σ] (AutQ V → ℂ) :=
  (onQ V ∘ₗ adel V dict mu).comp rd

def RdHolCusp {X : Comp → Data E r} (la : ∀ c, Wt (X c).Ψ r) (rd : C →ₛₗ[σ] FDSec X) : Prop :=
  ∀ f, IsHolCusp X la (rd f)

def JMemL2 {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) : Prop :=
  ∀ f, MemLp (jFn V σ rd dict mu f) 2 (muQ1 V)

def uniformisationL2 {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) (h : JMemL2 V σ rd dict mu) : C →ₛₗ[σ] Lp ℂ 2 (muQ1 V) where
  toFun f := (h f).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    congr 1
    exact map_add _ f g
  map_smul' a f := by
    rw [← MemLp.toLp_const_smul]
    congr 1
    exact map_smulₛₗ _ a f

def l2NormAlt {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) (h : JMemL2 V σ rd dict mu) (f : C) : ℝ :=
  ‖uniformisationL2 V σ rd dict mu h f‖

theorem l2Norm_nonneg_bis {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) (h : JMemL2 V σ rd dict mu) (f : C) : 0 ≤ l2NormAlt V σ rd dict mu h f := norm_nonneg _

theorem l2Norm_smul_alt {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) (h : JMemL2 V σ rd dict mu) (a : K) (f : C) :
    l2NormAlt V σ rd dict mu h (a • f) = ‖σ a‖ * l2NormAlt V σ rd dict mu h f := by
  simp only [l2NormAlt, map_smulₛₗ, norm_smul]

theorem L2Norm_add_le {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) (h : JMemL2 V σ rd dict mu) (f g : C) :
    l2NormAlt V σ rd dict mu h (f + g) ≤ l2NormAlt V σ rd dict mu h f + l2NormAlt V σ rd dict mu h g := by
  simp only [l2NormAlt, map_add (f := _)]
  exact norm_add_le _ _

def JInj {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) (h : JMemL2 V σ rd dict mu) : Prop :=
  ∀ (n : ℕ) (b : Fin n → C), LinearIndependent K b → LinearIndependent ℂ (fun i => uniformisationL2 V σ rd dict mu h (b i))

def L2Definite {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) (h : JMemL2 V σ rd dict mu) : Prop :=
  ∀ f, l2NormAlt V σ rd dict mu h f = 0 → f = 0

def FinVol : Prop := muQ V Set.univ ≠ 0 ∧ muQ V Set.univ ≠ ⊤

def archM (th' : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (h : GA D V) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  (infHom V h).1.map th'

def archMat {X : Comp → Data E r} (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hr : V.rank = r)
    (x0 : ∀ c, Frame (X c).Ψ r) (h : GA D V) (c : Comp) : Frame (X c).Ψ r :=
  fun τ => ((mat (x0 c) τ)⁻¹ * Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th c τ) h) * mat (x0 c) τ :
    Matrix (Fin r) (Fin r) ℂ)

def DictIsUnif {X : Comp → Data E r} (dict : GA D V → Σ c, Frame (X c).Ψ r) (Kf : Subgroup (GA D V))
    (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hr : V.rank = r) : Prop :=
  (∀ γ ∈ GQ V, ∀ g, ∃ γ' ∈ (X (dict g).1).Γ, dict (γ * g) = ⟨(dict g).1, lact γ' (dict g).2⟩) ∧
    (∀ k ∈ Kf, ∀ g, ∃ γ' ∈ (X (dict g).1).Γ, dict (g * k) = ⟨(dict g).1, lact γ' (dict g).2⟩) ∧
    (∃ x0 : ∀ c, Frame (X c).Ψ r, (∀ c, x0 c ∈ (X c).dom ∧ ∃ g, dict g = ⟨c, x0 c⟩) ∧
      ∀ g, ∀ h ∈ GinfC V, ∃ γ' ∈ (X (dict g).1).Γ,
        dict (g * h) = ⟨(dict g).1, lact γ' (rmul (dict g).2 (archMat V th hr x0 h (dict g).1))⟩) ∧
    (∀ g, (dict g).2 ∈ (X (dict g).1).dom) ∧
    (∀ c, ∀ x ∈ (X c).dom, ∃ g, ∃ γ ∈ (X c).Γ, ∃ b ∈ Bor (X c).Ψ r, dict g = ⟨c, rmul (lact γ x) b⟩) ∧
    ∀ g g', (∃ γ' ∈ (X (dict g).1).Γ, dict g' = ⟨(dict g).1, lact γ' (dict g).2⟩) →
      ∃ γ ∈ GQ V, ∃ k ∈ Kf, g' = γ * g * k

def repOf {X : Comp → Data E r} (dict : GA D V → Σ c, Frame (X c).Ψ r) (c : Comp) : GA D V :=
  Classical.epsilon fun g => (dict g).1 = c

def MuUnit {X : Comp → Data E r} (dict : GA D V → Σ c, Frame (X c).Ψ r) (mu : GA D V → ℂ) : Prop :=
  (∀ g g', mu (g * g') = mu g * mu g') ∧ (∀ g, ‖mu g‖ = 1) ∧ (∀ γ ∈ GQ V, mu γ = 1) ∧
    ∀ g τ i, ‖dmin (X (dict g).1).Gm (dict g).2 τ i‖ = 1

theorem pnorm_eq_of_unit (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r)
    (h : ∀ τ i, ‖dmin X.Gm x τ i‖ = 1) : X.pnorm la P x = ‖P x‖ := by
  simp [Data.pnorm, norm_div, h]

theorem L2Norm_le_sup_norm {X : Comp → Data E r} (la : ∀ c, Wt (X c).Ψ r) (rd : C →ₛₗ[σ] FDSec X)
    (dict : GA D V → Σ c, Frame (X c).Ψ r) (mu : GA D V → ℂ) (h : JMemL2 V σ rd dict mu)
    (hd : ∀ g, (dict g).2 ∈ (X (dict g).1).dom) (hm : MuUnit V dict mu) (f : C)
    (hfin : supE X la (rd f) ≠ ⊤) : l2NormAlt V σ rd dict mu h f ≤ supN X la (rd f) := by
  haveI : IsProbabilityMeasure (muQ1 V) := by
    unfold muQ1
    split_ifs with hh
    · constructor
      rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hh.1 hh.2]
    · infer_instance
  have hC : 0 ≤ supN X la (rd f) := supN_nonneg X la (rd f)
  have hb : ∀ᵐ q ∂(muQ1 V), ‖(uniformisationL2 V σ rd dict mu h f : AutQ V → ℂ) q‖ ≤ supN X la (rd f) := by
    filter_upwards [(h f).coeFn_toLp] with q hq
    have hq' : (uniformisationL2 V σ rd dict mu h f : AutQ V → ℂ) q = jFn V σ rd dict mu f q := hq
    rw [hq']
    show ‖mu q.out * rd f (dict q.out).1 (dict q.out).2‖ ≤ _
    rw [norm_mul, hm.2.1, one_mul,
      ← pnorm_eq_of_unit (X (dict q.out).1) (la (dict q.out).1) (rd f (dict q.out).1) (dict q.out).2 (hm.2.2.2 q.out)]
    have h1 : ENNReal.ofReal ((X (dict q.out).1).pnorm (la (dict q.out).1) (rd f (dict q.out).1) (dict q.out).2)
        ≤ supE X la (rd f) :=
      le_iSup (fun p : FPt X => ENNReal.ofReal ((X p.1).pnorm (la p.1) (rd f p.1) p.2))
        ⟨(dict q.out).1, ⟨(dict q.out).2, hd q.out⟩⟩
    have h0 : 0 ≤ (X (dict q.out).1).pnorm (la (dict q.out).1) (rd f (dict q.out).1) (dict q.out).2 := by
      unfold Data.pnorm
      exact mul_nonneg (norm_nonneg _) (pnorm_fac_nonneg _ _ _)
    have h2 := ENNReal.toReal_mono hfin h1
    rwa [ENNReal.toReal_ofReal h0] at h2
  have := Lp.norm_le_of_ae_bound hC hb
  simpa [l2NormAlt, measureUnivNNReal] using this

def EquivariantFiniteGroup {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) {G0 : Type} [Group G0] (ρ : G0 →* (C →ₗ[K] C)) (chi : G0 →* Kˣ) (ℓ : G0 → GA D V) :
    Prop :=
  ∀ g f x, adel V dict mu (rd (ρ g f)) x = σ ((chi g : Kˣ) : K) * adel V dict mu (rd f) (x * ℓ g)

end Formalism.L2.Pj
end
end
