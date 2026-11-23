module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1929
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1540
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1841
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1404
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1474
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1960
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1933
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1963
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1935
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1934
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem GlobalTheory.HSNef.height_generic_nonneg_of_ample : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → 1 ≤ D → ∀ (C : HermLB p) (h : X → ℝ), IsAmpleLB C.B → C.SemiPos D → C.IsArithHeight h → (∀ z, z ≠ genericPoint X → 0 ≤ h z) → 0 ≤ h (genericPoint X) := by
  intro hAr hHS k _ X _ p D hX hD C h hA hS hH hnn
  by_contra hc
  push_neg at hc
  have hg : 0 < gdeg C D := GlobalTheory.T.geometricDegree_pos_of_ample_semiPositive hAr hHS k X p D hX C hA hS
  set c := h (genericPoint X) with hcdef
  set g := gdeg C D with hgdef
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  set x : ℝ := -c / g with hx
  have hx0 : 0 < x := div_pos (by linarith) hg
  have hxg : x * g = -c := by rw [hx]; field_simp
  set u : ℝ := x * (D + 2) / (2 * (D + 1)) with hu
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  set α : ℝ := c + ((D : ℝ) + 1) * u * g with hα
  have hαv : α = -c * D / 2 := by
    rw [hα, hu]; field_simp; linear_combination ((D : ℝ) + 2) * hxg
  have hα0 : 0 < α := by rw [hαv]; have : 0 < -c := by linarith
                         positivity
  have hcu : c + u * g < 0 := by
    have e : c + u * g = c * D / (2 * (D + 1)) := by
      rw [hu]; field_simp; linear_combination ((D : ℝ) + 2) * hxg
    rw [e]; exact div_neg_of_neg_of_pos (by nlinarith) (by positivity)
  set C' := C.shift (fun _ => u) fun _ => rfl with hC'
  have hself : C.IsSelfInter c := ⟨h, hH, rfl⟩
  have hα' : C'.IsSelfInter α := hAr.arShift k X p D hX C c u hself
  have hA' : IsAmpleLB C'.B := hA
  have hS' : C'.SemiPos D := hS.shift _ _
  obtain ⟨P, hPL, -⟩ := exists_pair C' C'
  have hrep : P.Rep 1 0 C' := hPL ▸ (GlobalTheory.VolBr.Pair.rep_base k X p P).1
  have hfac : (0 : ℝ) < ((D + 1).factorial : ℝ) := by positivity
  have hε : 0 < α / (2 * ((D + 1).factorial : ℝ)) := by positivity
  obtain ⟨m, hm, hm0⟩ := ((GlobalTheory.T.log_count_radius_one_lower_bound_ample_semiPos hHS k X p D hX P 1 0 0 0 C' α hrep hA' hS' hα' _ hε).and
    (eventually_gt_atTop 0)).exists
  have hcoef : α / ((D + 1).factorial : ℝ) - α / (2 * ((D + 1).factorial : ℝ)) = α / (2 * ((D + 1).factorial : ℝ)) := by
    field_simp; ring
  rw [hcoef] at hm
  have hlc : 0 < P.lc ((m : ℤ) * 1) ((m : ℤ) * 0) 1 := by
    have : (0 : ℝ) < (m : ℝ) ^ (D + 1) := by positivity
    have := mul_pos hε this
    simpa using lt_of_lt_of_le this hm
  have hn : 1 < (P.Bl ((m : ℤ) * 1) ((m : ℤ) * 0) 1).ncard := by
    by_contra hle
    push_neg at hle
    have : ((P.Bl ((m : ℤ) * 1) ((m : ℤ) * 0) 1).ncard : ℝ) ≤ 1 := by exact_mod_cast hle
    exact absurd hlc (not_lt.2 (Real.log_nonpos (Nat.cast_nonneg _) this))
  have hfin : (P.Bl ((m : ℤ) * 1) ((m : ℤ) * 0) 1).Finite :=
    Set.finite_of_ncard_ne_zero (by omega)
  have henc : 1 < ((C'.pow m).smallSec).encard := by
    rw [(GlobalTheory.VolBr.SmallBall.main k X p P 1 0 C' hrep 0 m).2.1, ← hfin.cast_ncard_eq]
    exact_mod_cast hn
  obtain ⟨a, b, ha, hb, hab⟩ := Set.one_lt_encard_iff.1 henc
  have hex : ∃ s ∈ (C'.pow m).smallSec, s ≠ 0 := by
    by_cases ha0 : a = 0
    · exact ⟨b, hb, fun hb0 => hab (ha0.trans hb0.symm)⟩
    · exact ⟨a, ha, ha0⟩
  have := GlobalTheory.T.height_add_mul_geometricDegree_nonneg_of_smallSection hAr k X p D hX hD C h hS hH hnn m u hm0 hu0 hex
  linarith
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OnCmp

theorem weil_twist_base_of : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (χ : (AE D)ˣ →* Circle) (ω : GlobalTheory.OnTies.WeilRep D i), GlobalTheory.OnCmp.IsWeilTw R i χ ω → ∀ (k : GA D (Wc D i)) (x : (AE D)ˣ), IsDetRoot (Wc D i) k x → ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ω (1, k) f = ((χ x : Circle) : ℂ) • R.ωP i A.μ0 (1, k) f := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i χ ω hω k x hx f hf
  have h := GlobalTheory.TwistFactorProof.weil_ratio (GlobalTheory.T.weilDatum_unique_on_thetaFunctions D) (GlobalTheory.WeilChange.exists_weilDatum_twist D)
    (hR.thP.ωP i A.μ0) hω (GlobalTheory.TwistFactorProof.isDetRoot_one _) hx hf
  rw [h]
  congr 2
  show _ * (R.mu0 _ x * χ x * (R.mu0 _ x * R.xi A.μ0 x)⁻¹) = χ x
  rw [GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (χ := R.xi A.μ0) (hR.lev.xi_base ▸ hR.lev.xi A.μ0) x]
  simp only [map_one, mul_inv_cancel, inv_one, one_mul, mul_one]
  rw [mul_comm (R.mu0 _ x), mul_inv_cancel_right]

end GlobalTheory.OnCmp
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.transport_pureTensors_productMeasure_finiteAdelic : ∀ (D : D7) (V V' : HSp D) (j : ∀ v, GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v), (∀ v g, j v g ∈ Kv V' v ↔ g ∈ Kv V v) → ∀ Φ : GfC V ≃ₜ* GfC V', (∀ v g, Φ (locFin V v g) = locFin V' v (j v g)) → (∀ ff g, finFn V' (transfer j ff) (Φ g) = finFn V ff g) ∧ ∀ μf ν, IsFinMeas V μf ν → IsFinMeas V' (fun v => (μf v).map (j v)) (ν.map Φ) := by
  first | exact @GlobalTheory.TrMultTransport.transport | exact GlobalTheory.TrMultTransport.transport | (intros; apply GlobalTheory.TrMultTransport.transport <;> assumption)
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2

open GlobalTheory.Points GlobalTheory.ChartGlue

theorem contDiffAt_chart_of_eqOn_ev {F : Type} [Field F] {Y : Var F} {σ : F →+* ℂ} {D : ℕ} (c' : AlgChart Y.str σ D)
    {g : CxPts Y.str σ → ℂ} {S : Set (CxPts Y.str σ)} (hS : IsOpen S) {W : Y.X.Opens} (a : Γ(Y.X, W))
    (hg : ∀ z ∈ S, g z = ev Y.str σ W a z) {y : CxPts Y.str σ} (hy : y ∈ c'.e.source) (hyS : y ∈ S)
    (hyW : y ∈ ptsIn Y.str σ W) : ContDiffAt ℂ 2 (g ∘ c'.e.symm) (c'.e y) := by
  have hO := isOpen_over c'.e (hS.inter (isOpen_ptsIn (p := Y.str) (σ := σ) W))
  have hm := mem_over c'.e (S := S ∩ ptsIn Y.str σ W) hy ⟨hyS, hyW⟩
  have hd : DifferentiableOn ℂ (ev Y.str σ W a ∘ c'.e.symm) (c'.e.target ∩ c'.e.symm ⁻¹' (S ∩ ptsIn Y.str σ W)) :=
    (c'.holo W a).mono fun v hv => ⟨hv.1, hv.2.2⟩
  have h1 : ContDiffAt ℂ 2 (ev Y.str σ W a ∘ c'.e.symm) (c'.e y) := ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ _ hO hd).contDiffAt (hO.mem_nhds hm)).of_le
    (by norm_cast)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [hO.mem_nhds hm] with v hv
  exact hg _ hv.2.1

theorem cellMap_contDiffAt : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), ∀ (n : ℕ) (ε : Fin n ≃ Fin X.dim ⊕ Cell m) (x : (atlas Y σ).Pt), x.pt ∈ cellSet E E' φ f hf c A u → ContDiffAt ℂ 2 (cellMap ε f hf c u ∘ x.ch.symm) x.crd := by
  intro F _ σ X Y ι _ m E E' φ f hf hR c A u n ε x hx
  obtain ⟨hcell, hsrc⟩ := hx
  have hreg := (isOpen_inCell_and_regAt F X Y ι m E E' φ f hR A u).2 _ hcell
  set c' : AlgChart Y.str σ Y.dim := x.1.1
  have hy : x.pt ∈ c'.e.source := x.2
  change ContDiffAt ℂ 2 (cellMap ε f hf c u ∘ c'.e.symm) (c'.e x.pt)
  refine contDiffAt_euclidean.2 fun a => ?_
  change ContDiffAt ℂ 2 ((fun z => cellMap ε f hf c u z a) ∘ c'.e.symm) (c'.e x.pt)
  rcases hε : ε a with b | j
  · have hS : IsOpen (ptMap σ f hf ⁻¹' c.e.source) :=
      c.e.open_source.preimage (PtsOver.continuous_map f hf _)
    refine contDiffAt_chart_of_eqOn_ev c' hS (f.app c.U (c.x b)) (fun z hz => ?_) hy hsrc ?_
    · simp only [cellMap, pt, hε, Sum.elim_inl]
      rw [c.apply_eq _ hz b, ev_app f hf]
      rfl
    · rw [mem_ptsIn]
      exact mem_ptsIn.1 (c.source_subset hsrc)
  · obtain ⟨U, hU, w, hw⟩ := (hreg j).exists_fnOf
    refine contDiffAt_chart_of_eqOn_ev c' (isOpen_ptsIn U) w (fun z hz => ?_) hy (mem_ptsIn.2 hU) (mem_ptsIn.2 hU)
    simp only [cellMap, pt, hε, Sum.elim_inr]
    rw [← hw, ratVal_fnOf hz]

end GlobalTheory.FlagCell2
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

theorem _root_.GlobalTheory.T.contDiffAt_flagCellGradedLinePotential : ∀ (ι : Type) (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (w : V n) (x : Root m), (G (bsL ε w) x.1).PosDef → MContDiffAt 2 (fun v => G v x.1) (bsL ε w) → ContDiffAt ℝ 2 (cellPot ε G x) w ∧ 0 < grD (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2 := by
  first | exact @GlobalTheory.CellPotSmooth.cellPot_contDiffAt | exact GlobalTheory.CellPotSmooth.cellPot_contDiffAt | (intros; apply GlobalTheory.CellPotSmooth.cellPot_contDiffAt <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

theorem _root_.GlobalTheory.T.gradedSquaredLength_upperUnitriangular_gram_eq_of_agree : ∀ (s : ℕ) (G : Matrix (Fin s) (Fin s) ℂ) (y y' : Low s → ℂ) (i : Fin s), (∀ j : Low s, j.1.2 ≤ i → y' j = y j) → grD (upU y' * G * (upU y')ᴴ) i = grD (upU y * G * (upU y)ᴴ) i := by
  first | exact @GlobalTheory.FlagCell2.grD_upU_gram_eq | exact GlobalTheory.FlagCell2.grD_upU_gram_eq | (intros; apply GlobalTheory.FlagCell2.grD_upU_gram_eq <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

theorem _root_.GlobalTheory.T.isOpen_flagBundleCell_and_coords_regular : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (A : Mat m X.Fn) (u : Cell m → Y.Fn), IsOpen {y : Y.X | InCell E E' φ f A u y} ∧ ∀ y, InCell E E' φ f A u y → ∀ j, RegAt y (u j) := by
  first | exact @GlobalTheory.FlagCell2.isOpen_inCell_and_regAt | exact GlobalTheory.FlagCell2.isOpen_inCell_and_regAt | (intros; apply GlobalTheory.FlagCell2.isOpen_inCell_and_regAt <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

theorem _root_.GlobalTheory.T.prod_fubiniStudy_densities_eq_flagCell_invariant_density : ∀ (s : ℕ) (G : Matrix (Fin s) (Fin s) ℂ), G.PosDef → ∀ (y : Low s → ℂ), ∏ i : Fin s, (((s - 1 - i : ℕ).factorial : ℝ) / Real.pi ^ (s - 1 - i : ℕ) * (G.det.re / (leadMinor (upU y * G * (upU y)ᴴ) i).re / grD (upU y * G * (upU y)ᴴ) i ^ ((s - 1 - i : ℕ) + 1))) = GlobalTheory.TrueCx.flagConst s * G.det.re ^ ((s : ℤ) - 1) * GlobalTheory.FlagFibre.dens Gᵀ y := by
  first | exact @GlobalTheory.FlagCellDens.main | exact GlobalTheory.FlagCellDens.main | (intros; apply GlobalTheory.FlagCellDens.main <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_openCompact_level_sphericalOffTypes : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), ∃ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) ∧ IsCompact (K : Set (GfC V)) ∧ ∀ (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → ∀ ff, IsTestFin T U μf ff → SphRest T U ff → IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff ∧ ∀ k ∈ K, ∀ g, finFn V ff (k * g) = finFn V ff g := by
  first | exact @GlobalTheory.TrMult.oneLevel | exact GlobalTheory.TrMult.oneLevel | (intros; apply GlobalTheory.TrMult.oneLevel <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2

theorem card_row_sub (s : ℕ) (i : Fin s) : Fintype.card {j : Low s // j.1.2 = i} = s - 1 - i := by
  rw [← Fin.card_Ioi, ← Fintype.card_coe]
  refine Fintype.card_congr
    { toFun := fun j => ⟨j.1.1.1, by simpa [Finset.mem_Ioi, ← j.2] using j.1.2⟩
      invFun := fun c => ⟨⟨(c.1, i), Finset.mem_Ioi.mp c.2⟩, rfl⟩
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨⟨⟨b, a⟩, h⟩, rfl⟩; rfl
  · rintro ⟨c, hc⟩; rfl

noncomputable def rowEquiv {ι : Type} (m : ι → ℕ) (τ : ι) (i : Fin (m τ)) :
    {j : Low (m τ) // j.1.2 = i} ≃ {j : Cell m // j.root = ⟨τ, i⟩} :=
  Equiv.ofBijective (fun b => ⟨⟨τ, b.1⟩, by simp [Cell.root, b.2]⟩) (by
    constructor
    · rintro ⟨b, hb⟩ ⟨b', hb'⟩ h
      simp only [Subtype.mk.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
      exact Subtype.ext h
    · rintro ⟨⟨σ, l⟩, h⟩
      simp only [Cell.root, Sigma.mk.inj_iff] at h
      obtain ⟨rfl, h2⟩ := h
      exact ⟨⟨l, eq_of_heq h2⟩, rfl⟩)

theorem add_sum_coord_apply {n : ℕ} {B : Type} [Fintype B] (e : B → Fin n) (he : Function.Injective e)
    (z : V n) (t : B → ℂ) (k : Fin n) :
    (z + ∑ a, t a • coordVec (e a)) k = z k + ∑ a, if k = e a then t a else 0 := by
  simp [coordVec, Finset.sum_apply, PiLp.single_apply, Pi.single_apply, mul_ite]

end GlobalTheory.FlagCell2

namespace GlobalTheory.FlagCell2

theorem quad_pos {B : Type} [Fintype B] [DecidableEq B] (Q : Matrix (Option B) (Option B) ℂ) (hQ : Q.PosDef)
    (z : B → ℂ) : 0 < ∑ a, ∑ b, Option.elim a 1 z * Q a b * star (Option.elim b 1 z) := by
  have hv : (fun a => star (Option.elim a 1 z)) ≠ 0 := by
    intro h; have := congrFun h none; simp at this
  have := hQ.dotProduct_mulVec_pos hv
  convert this using 1
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_star, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end GlobalTheory.FlagCell2

namespace GlobalTheory.FlagCell2

theorem row_levi_det_of (hR : ∀ (n : ℕ) (B : Type) [Fintype B] [DecidableEq B] (e : B → Fin n), Function.Injective e → ∀ (Q : Matrix (Option B) (Option B) ℂ), Q.IsHermitian → ∀ (u : V n → ℝ) (z : V n), ContDiffAt ℝ 2 u z → (∀ t : B → ℂ, u (z + ∑ a, t a • coordVec (e a)) = Real.log ((∑ a, ∑ b, Option.elim a 1 (fun a => z (e a) + t a) * Q a b * star (Option.elim b 1 (fun b => z (e b) + t b))).re)) → ∀ q : ℂ, q = ∑ a, ∑ b, Option.elim a 1 (fun a => z (e a)) * Q a b * star (Option.elim b 1 (fun b => z (e b))) → q ≠ 0 → ∀ a b : B, leviForm u z (coordVec (e a)) (coordVec (e b)) = Q (some a) (some b) / q - (∑ c, Q (some a) c * star (Option.elim c 1 (fun c => z (e c)))) * (∑ c, Option.elim c 1 (fun c => z (e c)) * Q c (some b)) / q ^ 2) (hD : ∀ (B : Type) [Fintype B] [DecidableEq B] (Q : Matrix (Option B) (Option B) ℂ) (z z' : B → ℂ) (q : ℂ), q = ∑ a, ∑ b, Option.elim a 1 z * Q a b * Option.elim b 1 z' → q ≠ 0 → (Matrix.of fun a b : B => Q (some a) (some b) / q - (∑ c, Q (some a) c * Option.elim c 1 z') * (∑ c, Option.elim c 1 z * Q c (some b)) / q ^ 2).det = Q.det / q ^ (Fintype.card B + 1)) (hQ : ∀ (s : ℕ) (G : Matrix (Fin s) (Fin s) ℂ), G.PosDef → ∀ (y : Low s → ℂ) (i : Fin s), ∃ Q : Matrix (Option {j : Low s // j.1.2 = i}) (Option {j : Low s // j.1.2 = i}) ℂ, Q.PosDef ∧ Q.det * leadMinor (upU y * G * (upU y)ᴴ) i = G.det ∧ ∀ y' : Low s → ℂ, (∀ j : Low s, j.1.2 < i → y' j = y j) → grD (upU y' * G * (upU y')ᴴ) i = (∑ a, ∑ b, Option.elim a 1 (fun a => y' a.1) * Q a b * star (Option.elim b 1 (fun b => y' b.1))).re) (ι : Type) [Fintype ι] (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (w : V n) (x : Root m) (hG : (G (bsL ε w) x.1).PosDef) (hs : MContDiffAt 2 (fun v => G v x.1) (bsL ε w)) : Fintype.card {j : Cell m // j.root = x} = m x.1 - 1 - x.2 ∧ (Matrix.of fun a b : {j : Cell m // j.root = x} => -leviForm (cellPot ε G x) w (coordVec (ε.symm (.inr a.1))) (coordVec (ε.symm (.inr b.1)))).det = (((G (bsL ε w) x.1).det.re / (leadMinor (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2).re / grD (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2 ^ ((m x.1 - 1 - x.2 : ℕ) + 1) : ℝ) : ℂ) := by
  obtain ⟨τ, i⟩ := x
  have hsm := GlobalTheory.CellPotSmooth.cellPot_contDiffAt ι m n d ε G w ⟨τ, i⟩ hG hs
  have hcard : Fintype.card {j : Cell m // j.root = ⟨τ, i⟩} = m τ - 1 - i := by
    rw [← Fintype.card_congr (rowEquiv m τ i), card_row_sub]
  refine ⟨hcard, ?_⟩
  simp only at hG hs hsm ⊢
  let e : {j : Low (m τ) // j.1.2 = i} → Fin n := fun b => ε.symm (.inr ⟨τ, b.1⟩)
  have he : Function.Injective e := by
    intro b b' h
    have := ε.symm.injective h
    simp only [Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at this
    exact Subtype.ext this
  set y : Low (m τ) → ℂ := fun s => fb ε w ⟨τ, s⟩ with hy
  obtain ⟨Q, hQpd, hQdet, hQg⟩ := hQ (m τ) (G (bsL ε w) τ) hG y i
  set q : ℂ := ∑ a, ∑ b, Option.elim a 1 (fun a => w (e a)) * Q a b * star (Option.elim b 1 (fun b => w (e b))) with hq
  have hqpos : 0 < q := quad_pos Q hQpd _
  have hgr : grD (upM (fb ε w) τ * G (bsL ε w) τ * (upM (fb ε w) τ)ᴴ) i = q.re := hQg y (fun _ _ => rfl)
  have hqre : q = ((grD (upM (fb ε w) τ * G (bsL ε w) τ * (upM (fb ε w) τ)ᴴ) i : ℝ) : ℂ) := by
    rw [hgr]; exact Complex.ext rfl (by simp [(Complex.pos_iff.mp hqpos).2])
  have hq0 : q ≠ 0 := hqpos.ne'
  have hstar : ∀ c : Option {j : Low (m τ) // j.1.2 = i}, star (Option.elim c 1 (fun c => w (e c))) = Option.elim c 1 (fun c => star (w (e c))) := by
    intro c; cases c <;> simp
  have hres : ∀ t : {j : Low (m τ) // j.1.2 = i} → ℂ, (fun v => -cellPot ε G ⟨τ, i⟩ v) (w + ∑ a, t a • coordVec (e a)) = Real.log ((∑ a, ∑ b, Option.elim a 1 (fun a => w (e a) + t a) * Q a b * star (Option.elim b 1 (fun b => w (e b) + t b))).re) := by
    intro t
    set w' := w + ∑ a, t a • coordVec (e a) with hw'
    have hb : bsL ε w' = bsL ε w := by
      ext c
      simp only [bsL_apply, hw', add_sum_coord_apply e he]
      rw [Finset.sum_eq_zero]
      · simp
      intro a _
      rw [ite_eq_right]
      simp [e]
    have hf : ∀ s : Low (m τ), fb ε w' ⟨τ, s⟩ = y s + if h : s.1.2 = i then t ⟨s, h⟩ else 0 := by
      intro s
      simp only [fb, hy, hw', add_sum_coord_apply e he]
      congr 1
      split_ifs with h
      · rw [Finset.sum_eq_single ⟨s, h⟩]
        · simp [e]
        · intro b _ hb
          rw [ite_eq_right]
          intro h'
          exact hb (he (show e ⟨s, h⟩ = e b from h')).symm
        · simp
      · refine Finset.sum_eq_zero fun b _ => ?_
        rw [ite_eq_right]
        intro h'
        have := ε.symm.injective h'
        simp only [e, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at this
        exact h (this ▸ b.2)
    have hfa : ∀ a : Option {j : Low (m τ) // j.1.2 = i}, Option.elim a 1 (fun a => fb ε w' ⟨τ, a.1⟩) = Option.elim a 1 (fun a => w (e a) + t a) := by
      rintro (_ | b)
      · rfl
      · simp only [Option.elim, hf, dite_eq_left b.2]
        rfl
    simp only [cellPot, neg_neg]
    rw [hb, show upM (fb ε w') τ = upU (fun s => fb ε w' ⟨τ, s⟩) from rfl,
      hQg _ (fun j hj => by rw [hf, dite_eq_right (ne_of_lt hj)]; simp)]
    simp only [hfa]
  have hR' := hR n {j : Low (m τ) // j.1.2 = i} e he Q hQpd.1 (fun v => -cellPot ε G ⟨τ, i⟩ v) w hsm.1.neg hres q hq hq0
  have hD' := hD {j : Low (m τ) // j.1.2 = i} Q (fun a => w (e a)) (fun b => star (w (e b))) q (by rw [hq]; simp only [hstar]) hq0
  rw [← Matrix.det_submatrix_equiv_self (rowEquiv m τ i)]
  have hM : (Matrix.of fun a b : {j : Cell m // j.root = ⟨τ, i⟩} => -leviForm (cellPot ε G ⟨τ, i⟩) w (coordVec (ε.symm (.inr a.1))) (coordVec (ε.symm (.inr b.1)))).submatrix (rowEquiv m τ i) (rowEquiv m τ i) = Matrix.of fun a b : {j : Low (m τ) // j.1.2 = i} => Q (some a) (some b) / q - (∑ c, Q (some a) c * Option.elim c 1 (fun b => star (w (e b)))) * (∑ c, Option.elim c 1 (fun a => w (e a)) * Q c (some b)) / q ^ 2 := by
    ext a b
    have := hR' a b
    simp only [leviForm_neg, ContinuousLinearMap.neg_apply, hstar] at this
    rw [Matrix.submatrix_apply, Matrix.of_apply, Matrix.of_apply, ← this]
    rfl
  rw [hM, hD', card_row_sub]
  have hQd := hQpd.det_pos
  have hGd := hG.det_pos
  obtain ⟨hQr, hQi⟩ := Complex.pos_iff.mp hQd
  obtain ⟨hGr, hGi⟩ := Complex.pos_iff.mp hGd
  have h1 : Q.det = (Q.det.re : ℂ) := Complex.ext rfl (by simp [hQi])
  have h2 : (G (bsL ε w) τ).det = ((G (bsL ε w) τ).det.re : ℂ) := Complex.ext rfl (by simp [hGi])
  have hQdet' : Q.det * leadMinor (upM (fb ε w) τ * G (bsL ε w) τ * (upM (fb ε w) τ)ᴴ) i = (G (bsL ε w) τ).det := hQdet
  have hQ0 : (Q.det.re : ℂ) ≠ 0 := by exact_mod_cast hQr.ne'
  have hL : leadMinor (upM (fb ε w) τ * G (bsL ε w) τ * (upM (fb ε w) τ)ᴴ) i = (((G (bsL ε w) τ).det.re / Q.det.re : ℝ) : ℂ) := by
    rw [h1, h2] at hQdet'
    push_cast
    rw [eq_div_iff hQ0, mul_comm]
    exact hQdet'
  rw [hL, Complex.ofReal_re]
  conv_lhs => rw [h1, hqre]
  have hgpos : 0 < grD (upM (fb ε w) τ * G (bsL ε w) τ * (upM (fb ε w) τ)ᴴ) i := hsm.2
  push_cast
  have : ((G (bsL ε w) τ).det.re : ℂ) ≠ 0 := by exact_mod_cast hGr.ne'
  have : (grD (upM (fb ε w) τ * G (bsL ε w) τ * (upM (fb ε w) τ)ᴴ) i : ℂ) ≠ 0 := by exact_mod_cast hgpos.ne'
  field_simp

end GlobalTheory.FlagCell2

namespace GlobalTheory.FlagCell2

theorem row_levi_det (ι : Type) [Fintype ι] (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ)
    (w : V n) (x : Root m) (hG : (G (bsL ε w) x.1).PosDef) (hs : MContDiffAt 2 (fun v => G v x.1) (bsL ε w)) :
    Fintype.card {j : Cell m // j.root = x} = m x.1 - 1 - x.2 ∧ (Matrix.of fun a b : {j : Cell m // j.root = x} => -leviForm (cellPot ε G x) w (coordVec (ε.symm (.inr a.1))) (coordVec (ε.symm (.inr b.1)))).det = (((G (bsL ε w) x.1).det.re / (leadMinor (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2).re / grD (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2 ^ ((m x.1 - 1 - x.2 : ℕ) + 1) : ℝ) : ℂ) :=
  row_levi_det_of GlobalTheory.LogHermHess.leviForm_log_herm GlobalTheory.det_schur_bilinear_entry GlobalTheory.FlagCell2.exists_posDef_grD ι m n d ε G w x hG hs

end GlobalTheory.FlagCell2
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

theorem _root_.GlobalTheory.T.pullGram_flagCell_frame : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ z : CxPts Y.str σ, InCell E E' φ f A u (under z) → pullGram E H φ f hf (upM u * A.map φ) z = fun τ => upM (fun j => ratVal (u j) z) τ * H A (ptMap σ f hf z) τ * (upM (fun j => ratVal (u j) z) τ)ᴴ := by
  first | exact @GlobalTheory.FlagCell2.pullGram_cell | exact GlobalTheory.FlagCell2.pullGram_cell | (intros; apply GlobalTheory.FlagCell2.pullGram_cell <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

theorem _root_.GlobalTheory.T.topDegreeDensity_baseForm_mul_fibreVolume : ∀ (n d : ℕ) (J : Type) [Fintype J] (ε : Fin n ≃ Fin d ⊕ J) (α : Alt d), dens (pull (bsL ε) α * ((∏ j : J, (Complex.I / 2) • sym (ε.symm (.inr j), ε.symm (.inr j)) : Ev n) : Alt n)) = dens α := by
  first | exact @GlobalTheory.FlagCell2.BaseVol.dens_pull_mul_vol | exact GlobalTheory.FlagCell2.BaseVol.dens_pull_mul_vol | (intros; apply GlobalTheory.FlagCell2.BaseVol.dens_pull_mul_vol <;> assumption)
end
