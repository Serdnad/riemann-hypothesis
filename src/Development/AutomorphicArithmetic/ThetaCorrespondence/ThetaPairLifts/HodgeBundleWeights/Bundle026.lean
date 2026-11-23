module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle008
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle025
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
public import Development.WeilBound.CoreStatements.NefModelVolumes.NV
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2332
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.LocalUnitMapSurjective
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle053
public import Development.WeilBound.CoreStatements.NefModelVolumes.NormGenValLe
public import Development.WeilBound.CoreStatements.ProjectiveValuations.NonemptyToroidalFlagBundle
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026

@[expose] public section

section

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0
open GlobalTheory.Vanishing.H0
namespace GlobalTheory.CuspTransfer
theorem exists_cusp_germ_transfer : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), FnAlgClosed (Xo := Xo) (c := c) → ∀ (M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw)) (ω : CanId M) (b s : AllWt.Weight Dw), FlagTan.kap Dw + b = s → vanBd TF.X Z s ≤ space TF.X Z U s → ∃ F : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤ → Cusp Z U s, ∀ (z : M.X) (hz : z ∈ M.off) (j : (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)).ι) (hj : z ∈ (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)).U j) (i : (L₀ TF.X Z s).ι) (hi : M.σ z ∈ (L₀ TF.X Z s).U i), ∃ u : (M.X.presheaf.stalk z)ˣ, ∀ g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤, germ j z (memTop z) hj g = u.val * (M.σ.stalkMap z).hom (germ i (M.σ z) (M.off_eq.le hz) hi (cuspSec TF.X Z U s (F g))) := by
  intro hP hG E _ _ _ H Dw l Xo c TF Z r U hF M ω b s hs hvs
  set C := ((common₀ TF.X Z).pull M.σ).canChart M.K.isLB hs with hC
  have key : ∀ g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤, ∃ f : Cusp Z U s,
      C.mul ω.ω (M.pullOff (cuspSec TF.X Z U s f)) = H0.restr le_top g := by
    intro g
    obtain ⟨m, hm⟩ := (M.bijective_pullOff (isLB_L₀ TF.X Z s)).2 ((C.mulEquiv ω.unit).symm (H0.restr le_top g))
    have hm' : C.mul ω.ω (M.pullOff m) = H0.restr le_top g := by
      rw [hm, ← ProdChart.mulEquiv_apply C ω.unit, LinearEquiv.apply_symm_apply]
    obtain ⟨g', hv, hr⟩ := (_root_.GlobalTheory.T.log_canonical_criterion_boundary hP hG E H Dw l Xo c TF Z hF M ω b s hs m).2 ⟨g, hm'.symm⟩
    refine ⟨ofSpace TF.X Z U s ⟨g', hvs hv⟩, ?_⟩
    rw [cuspSec_ofSpace]
    exact (congrArg (fun x => C.mul ω.ω (M.pullOff x)) hr).trans hm'
  refine ⟨fun g => (key g).choose, ?_⟩
  intro z hz j hj i hi
  obtain ⟨t, ha, hb, hc⟩ := C.cover z
  have hω : IsUnit (H0.germ (C.a t) z hz ha ω.ω) := ω.unit z hz (C.a t) ha
  refine ⟨tr _ z j (C.c t) * hω.unit *
      Units.map (M.σ.stalkMap z).hom.toMonoidHom (tr (L₀ TF.X Z s) (M.σ z) (C.b t PUnit.unit) i), ?_⟩
  intro g
  have hg := (key g).choose_spec
  rw [H0.germ_change j (C.c t) z (memTop z) hj hc g, ← H0.germ_restr le_top (C.c t) z hz hc g, ← hg,
    C.germ_mul ω.ω _ t z hz ha hb hc]
  change _ = _ * (M.σ.stalkMap z).hom _
  have e2 := H0.germ_pull M.σ M.off_eq.le (C.b t) z hz hb (cuspSec TF.X Z U s (key g).choose)
  change _ * (_ * H0.germ (C.b t) z hz hb (H0.pull M.σ M.off_eq.le (cuspSec TF.X Z U s (key g).choose))) = _
  rw [e2]
  erw [H0.germ_change (B := L₀ TF.X Z s) (C.b t PUnit.unit) i (M.σ z) (M.off_eq.le hz) _ hi, map_mul]
  simp only [Units.val_mul, IsUnit.unit_spec, Units.coe_map]
  simp only [mul_assoc]
  rfl
end GlobalTheory.CuspTransfer
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0
open GlobalTheory.Vanishing.H0

theorem _root_.GlobalTheory.T.cusp_germ_transfer_of_boundary : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), FnAlgClosed (Xo := Xo) (c := c) → ∀ (M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw)) (ω : CanId M) (b s : AllWt.Weight Dw), FlagTan.kap Dw + b = s → vanBd TF.X Z s ≤ space TF.X Z U s → ∃ F : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤ → Cusp Z U s, ∀ (z : M.X) (hz : z ∈ M.off) (j : (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)).ι) (hj : z ∈ (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)).U j) (i : (L₀ TF.X Z s).ι) (hi : M.σ z ∈ (L₀ TF.X Z s).U i), ∃ u : (M.X.presheaf.stalk z)ˣ, ∀ g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤, germ j z (memTop z) hj g = u.val * (M.σ.stalkMap z).hom (germ i (M.σ z) (M.off_eq.le hz) hi (cuspSec TF.X Z U s (F g))) := by
  first | exact @_root_.GlobalTheory.CuspTransfer.exists_cusp_germ_transfer | exact _root_.GlobalTheory.CuspTransfer.exists_cusp_germ_transfer | (intros; apply _root_.GlobalTheory.CuspTransfer.exists_cusp_germ_transfer <;> assumption)
end
end

section

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
namespace GlobalTheory.CuspNonvanishing
theorem exists_vanBd_section_nonzero_of_canonical_twist_nonzero : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw)) (ω : CanId M) (la : AllWt.Weight Dw) (g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z (la - FlagTan.kap Dw)).pull M.σ)) ⊤) (z : M.X), z ∈ M.off → z ∈ nonzeroLocus (toSec g) → ∃ s ∈ vanBd TF.X Z la, M.σ z ∈ nonzeroLocus (toSec s) := by
  intro hP hG E _ _ _ H Dw l Xo c TF Z hF M ω la g z hz hg
  have hs : FlagTan.kap Dw + (la - FlagTan.kap Dw) = la := by abel
  set C := ((common₀ TF.X Z).pull M.σ).canChart M.K.isLB hs
  obtain ⟨m, hm⟩ := (M.bijective_pullOff (isLB_L₀ TF.X Z la)).2 ((C.mulEquiv ω.unit).symm (H0.restr le_top g))
  have hm' : C.mul ω.ω (M.pullOff m) = H0.restr le_top g := by
    rw [hm, ← ProdChart.mulEquiv_apply C ω.unit, LinearEquiv.apply_symm_apply]
  obtain ⟨s, hsv, hsr⟩ := (_root_.GlobalTheory.T.log_canonical_criterion_boundary hP hG E H Dw l Xo c TF Z hF M ω (la - FlagTan.kap Dw) la hs m).2 ⟨g, hm'.symm⟩
  refine ⟨s, hsv, ?_⟩
  obtain ⟨t, ha, hb, hc⟩ := C.cover z
  have e := C.germ_mul ω.ω (M.pullOff m) t z hz ha hb hc
  rw [hm', H0.germ_restr] at e
  have hu : IsUnit (H0.germ (C.c t) z (memTop z) hc g) := by
    rw [← ger_toSec]; exact (isUnit_ger_iff _ hc).2 hg
  rw [e] at hu
  have hu2 := isUnit_of_mul_isUnit_right hu
  have e2 := H0.germ_pull M.σ M.off_eq.le (C.b t) z hz hb m
  change IsUnit (H0.germ (C.b t) z hz hb (H0.pull M.σ M.off_eq.le m)) at hu2
  rw [e2] at hu2
  have hu3 := (isUnit_map_iff (M.σ.stalkMap z).hom _).1 hu2
  rw [← hsr] at hu3
  erw [H0.germ_restr] at hu3
  rw [← ger_toSec] at hu3
  exact (isUnit_ger_iff _ _).1 hu3
end GlobalTheory.CuspNonvanishing
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem _root_.GlobalTheory.T.exists_form_nonvanishing_at_cusp : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw)) (ω : CanId M) (la : AllWt.Weight Dw) (g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z (la - FlagTan.kap Dw)).pull M.σ)) ⊤) (z : M.X), z ∈ M.off → z ∈ nonzeroLocus (toSec g) → ∃ s ∈ vanBd TF.X Z la, M.σ z ∈ nonzeroLocus (toSec s) := by
  first | exact @_root_.GlobalTheory.CuspNonvanishing.exists_vanBd_section_nonzero_of_canonical_twist_nonzero | exact _root_.GlobalTheory.CuspNonvanishing.exists_vanBd_section_nonzero_of_canonical_twist_nonzero | (intros; apply _root_.GlobalTheory.CuspNonvanishing.exists_vanBd_section_nonzero_of_canonical_twist_nonzero <;> assumption)
end
end

section

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option autoImplicit false

noncomputable section
namespace PositivityTheory.Xj7N
open GlobalTheory GlobalTheory.CompHS GlobalTheory.Adelic
section Generic
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
variable {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {D : D7} {V : (c.F →+* ℂ) → HSp D}
  {dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r}
end Generic
section Main
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
  {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {D : D7} {V : (c.F →+* ℂ) → HSp D}
  {dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r}
end Main
theorem weil_height_archimedean_contribution : NV → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → ∀ (N m : ℕ) (b : Module.Basis (Fin N) Y.d.c₂.F (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (g : Matrix (Fin N) (Fin m) Y.d.c₂.F) (A : (Y.d.c₂.F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), IsFrame (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) b g A → ∀ (σ : Y.d.c₂.F →+* ℂ) (ρ : Om Z →+* ℂ), ρ.comp (algebraMap Y.d.c₂.F (Om Z)) = σ → ∀ τ : ℕ, 0 < τ → ∀ f ∈ smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) τ t, ‖ρ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂))‖ ≤ Real.exp (τ * t) * GlobalTheory.Adelic.archSize (A σ) (fun i => ρ (genVal Z ((b i : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂))) ^ τ := by
  intro hNV hP D T j Y e o hY hf Z u t hG hB _ _ N m b g A hF σ ρ hρ τ _ f hfs
  have hd : ∀ σ, GoodEmb Y.d.c₂ σ → ∀ g, (Y.dict σ g).2 ∈ ((Y.U σ).X (Y.dict σ g).1).dom := fun σ hσ => by
    obtain ⟨th, hr, hth, hdU⟩ := hY.dictU σ hσ
    exact hdU.2.2.2.1
  have hD : 1 ≤ GlobalTheory.FlagTan.dimFlag (T.Q.Dw j) := by
    have h2 : D.R.r = (T.Q.Dw j).p + (T.Q.Dw j).q :=
      (hY.unf _ (goodEmb_goodOf Y.d.c₂ Y.d.c₂.F.val.toRingHom)).1
    have hm := D.R.two_le_m
    have hk := D.R.m_add_three_le_k
    have h3 : 2 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
      rw [← h2]; unfold Formalism.BasicNotions.Ranks.r; omega
    exact Nat.mul_pos (by omega) (Nat.choose_pos h3)
  obtain ⟨TF⟩ := DifferentiableLines.nonempty_toroidal_flag_bundle hP.p1 _ _ _ _ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.CompHS.TorFlagEx.one_le_of_dimFlag hD)
  have hspan : ∀ σ, GoodEmb Y.d.c₂ σ → ∀ P ∈ holSub (Y.U σ).X (modelWt (Y.U σ) (wtOf (T.Q.Dw j) u 0)),
      ∃ Q ∈ Submodule.span ℂ (rdU (Y.U σ) '' (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0) : Set (Rul Y.d.Xo₂ Y.d.c₂))),
        ∀ w ∈ framesOn (Y.U σ) Z, P w.1 w.2 = Q w.1 w.2 := fun σ hσ P hPh => by
    obtain ⟨m', as, fs, hfs', hPQ⟩ := _root_.PositivityTheory.Xj7N.local_unit_map_surjective hNV hP D T j Y e o hY hf Z TF u hG hB σ hσ P hPh
    choose g' hg hgf using fun i => GlobalTheory.T.extVan_section_has_cusp_form_match D T j Y e o hY hf Z TF u (fs i) (hfs' i)
    refine ⟨∑ i, as i • rdU (Y.U σ) (g' i), Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨g' i, hg i, rfl⟩), fun w hw => ?_⟩
    rw [hPQ w hw]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [hgf i σ hσ w hw]
  exact norm_small_le hY.unf hd (AllWt.even_wtOf u 0) hspan hF σ ρ hρ τ t f hfs
end PositivityTheory.Xj7N
end
end
end
