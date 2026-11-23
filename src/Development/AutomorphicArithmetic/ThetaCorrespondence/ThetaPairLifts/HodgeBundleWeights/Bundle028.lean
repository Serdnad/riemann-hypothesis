module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle008
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3118
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2660
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3401
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2435
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1596
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle134
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringTopologyRefinement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle022
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle024
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings

@[expose] public section

section

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option autoImplicit false
namespace GlobalTheory.HodgeBig
theorem hodgeLineBundle_isBig : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p → 1 ≤ Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ (δ : LB (X₀ TF.Y Z)) (hδ : δ.IsLB), CechPic.pull (π₀ TF.X Z) (cls δ hδ) = cls (L₀ TF.X Z (hodgeWt Dw)) (isLB_L₀ TF.X Z _) → letI := algebraΓOfHom (s₀ TF.Y Z); IsBig c.F δ := by
  intro hP _ _ hS hK E _ _ _ H Dw l Xo c TF Z _ _ hF δ hδ hpull
  classical
  obtain ⟨ω, hω, e, hdom⟩ := HodgeDominates.exists_lb_dominates hP.p22 hS hK.toroidalChartsForFan TF
  obtain ⟨_, -, hproj, -, hsurj, -⟩ := GlobalTheory.BaseVar.isVariety_barComp E H Dw l Xo c TF Z hF
  have hprojY : IsProjOver (str₀ TF.X Z) := (GlobalTheory.VarFlag.isVariety₀_flag E H Dw l Xo c TF Z hF).2.1
  have hN := hP.q7
  let χ : AllWt.Weight Dw := fun _ i => if (i : ℕ) < Dw.p then (1 : ℤ) else -1
  have hB : (ω.pull (barComp TF.Y Z).ι).IsLB := pull_isLB hω _
  have hBp : CechPic.pull (π₀ TF.X Z) (cls _ hB) = cls (L₀ TF.X Z χ) (isLB_L₀ TF.X Z _) := by
    rw [cls_pull hω _ hB, ← CechPic.pull_comp, morphismRestrict_ι, CechPic.pull_comp, ← e]
    exact (cls_pull (TF.X.isLB_Llam _) _ _).symm
  let C := common₀ TF.X Z
  let φ := AddMonoidHom.mk' (fun a => cls (L₀ TF.X Z a) (C.isLB a)) (cls_common_add C)
  have hφ : ∀ a, cls (L₀ TF.X Z a) (isLB_L₀ TF.X Z a) = φ a := fun _ => rfl
  let w : AllWt.Weight Dw := ∑ τ : Psi H, NefWt.unitWt τ (-1)
  have ew : 2 • hodgeWt Dw - χ = w := by
    funext τ i
    simp only [w, Finset.sum_apply, NefWt.unitWt_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.sub_apply,
      Pi.smul_apply, hodgeWt, CompHt.barWt, χ, smul_eq_mul]
    split_ifs <;> norm_num
  have hwnef : (letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z w)) := by
    letI := algebraΓOfHom (str₀ TF.X Z)
    obtain ⟨A, hA⟩ := exists_isAmpleLB_of_isProjOver hprojY
    refine IsNef.of_cls_eq_sum Finset.univ
      (fun τ : Psi H => (_root_.GlobalTheory.NefUnit.isNef_hodgeBundle_unitWeight (_root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems.toClassicalTheorems hP) hN E H Dw l Xo c TF Z hF τ).2) (fun _ => 1) hA
      (isLB_L₀ TF.X Z w) ?_

    rw [hφ, map_sum]
    exact Finset.sum_congr rfl fun τ _ => (one_smul _ _).symm
  letI := algebraΓOfHom (s₀ TF.Y Z)
  have hf : ∀ r : c.F, algebraMap c.F Γ(X₀ TF.Y Z, ⊤) r =
      (s₀ TF.Y Z).appTop ((Scheme.ΓSpecIso (.of c.F)).inv r) := fun _ => rfl
  have hp' : IsProjOver (strHom c.F (X := (X₀ TF.Y Z))) := by rw [strHom_eq hf]; exact hproj
  have h2 := isLB_lbPow hδ 2
  have hNl := LB.isLB_div h2 hB
  have hNp : CechPic.pull (π₀ TF.X Z) (cls _ hNl) = cls (L₀ TF.X Z w) (isLB_L₀ TF.X Z _) := by
    rw [cls_div h2 hB hNl, map_sub, cls_lbPow hδ 2 h2, map_nsmul, hpull, hBp, hφ, hφ, hφ, ← ew, map_sub, map_nsmul]
  have hNnef : IsNef c.F (LB.div (lbPow δ 2) (ω.pull (barComp TF.Y Z).ι)) :=
    GlobalTheory.NefDescent.isNef_of_pull c.F _ _ (π₀ TF.X Z) (s₀ TF.Y Z) (str₀ TF.X Z) _ hNl _
      (isLB_L₀ TF.X Z w) (π₀_s₀ TF.X Z) hproj hprojY hsurj hNp hwnef
  have : IsProper (s₀ TF.Y Z) := ThetaDescent.isProper_of_isProjOver hproj
  have : CompactSpace (X₀ TF.Y Z) := QuasiCompact.compactSpace_of_compactSpace (s₀ TF.Y Z)
  obtain ⟨A, hA⟩ := exists_isAmpleLB_of_isProjOver TF.Y.proj
  have hA₀ : IsAmpleLB (A.pull (barComp TF.Y Z).ι) := hA.pull_of_isOpenImmersion _
  have hw : TF.Y.j (genPt Z) ∈ barComp TF.Y Z := (j_mem_barComp Z _).2 (CompSplitPfB.cspB_genPt_mem Z)
  obtain ⟨m, hm, s, hs⟩ := hdom (genPt Z) A hA.isLB
  have hD := LB.isLB_div (isLB_lbPow hω m) hA.isLB
  have ht : (⟨_, hw⟩ : X₀ TF.Y Z) ∈ nonzeroLocus (lbSecPull _ s (barComp TF.Y Z).ι) := by
    rw [HodgeDominates.nonzeroLocus_lbSecPull]
    exact hs
  have hNm := hNnef.pow hA₀ m
  have hbig := hNm.isBig_tens_ample hN hp' hA₀
  have hδm : IsBig c.F (lbPow δ (2 * m)) :=
    hbig.of_cls_eq_add hf hproj (pull_isLB hD _) ⟨_, sec_ne_zero_of_mem ht⟩ (isLB_lbPow hδ _) (by
      rw [cls_tens hNm.isLB hA₀.isLB, cls_lbPow hNl, cls_div h2 hB hNl, cls_lbPow hδ, cls_lbPow hδ, cls_pull hω,
        cls_pull hA.isLB, cls_pull hD, cls_div (isLB_lbPow hω m) hA.isLB, cls_lbPow hω, map_sub, map_nsmul,
        smul_sub, mul_comm, mul_smul]
      abel)
  exact hδm.of_pow hδ (by omega) fun n => finite_coh_zero_twist_of_isProjOver hf hproj (isLB_lbPow hδ n)
end GlobalTheory.HodgeBig
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

theorem _root_.GlobalTheory.T.hodgeLineBundle_bigness_on_shimuraVariety : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p → 1 ≤ Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ (δ : LB (X₀ TF.Y Z)) (hδ : δ.IsLB), CechPic.pull (π₀ TF.X Z) (cls δ hδ) = cls (L₀ TF.X Z (hodgeWt Dw)) (isLB_L₀ TF.X Z _) → letI := algebraΓOfHom (s₀ TF.Y Z); IsBig c.F δ := by
  first | exact @_root_.GlobalTheory.HodgeBig.hodgeLineBundle_isBig | exact _root_.GlobalTheory.HodgeBig.hodgeLineBundle_isBig | (intros; apply _root_.GlobalTheory.HodgeBig.hodgeLineBundle_isBig <;> assumption)
end
end

section

section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
namespace GlobalTheory.HodgeDominates
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
theorem exists_weight_hodgeBundle_dominates : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∃ χ : AllWt.Weight Dw, ∀ y ∈ U₀ TF.X Z, ∀ A : LB TF.Y.X, A.IsLB → ∃ (m : ℕ) (s : (LB.div (lbPow (L₀ TF.X Z χ) m) (A.pull (inc₀ TF.X Z ≫ TF.X.π))).Sec), 0 < m ∧ y ∈ nonzeroLocus s := by
  intro hP _ hS hF E _ _ _ H Dw l Xo c TF Z _
  obtain ⟨ω, hω, e, h⟩ := exists_lb_dominates (E := E) (H := H) (Dw := Dw) (l := l) (Xo := Xo) (c := c) hP.p22 hS hF TF
  refine ⟨FlagMod.mu0 Dw, fun y hy A hA => ?_⟩
  obtain ⟨w, hw⟩ : ∃ w, TF.Y.j w = (inc₀ TF.X Z ≫ TF.X.π) y := hy
  obtain ⟨m, hm, s, hs⟩ := h w A hA
  have hD := LB.isLB_div (isLB_lbPow hω m) hA
  have hL := isLB_L₀ TF.X Z (FlagMod.mu0 Dw)
  have hT := LB.isLB_div (isLB_lbPow hL m) (pull_isLB hA (inc₀ TF.X Z ≫ TF.X.π))
  have e' : cls _ hL = CechPic.pull (inc₀ TF.X Z ≫ TF.X.π) (cls ω hω) := by
    rw [CechPic.pull_comp, ← e]
    exact cls_pull (TF.X.isLB_Llam _) _ _
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hT (pull_isLB hD (inc₀ TF.X Z ≫ TF.X.π))
    ((cls_eq_iff hT (pull_isLB hD _)).1 (by
      rw [cls_div (isLB_lbPow hL m) (pull_isLB hA _), cls_lbPow hL, cls_pull hA, cls_pull hD,
        cls_div (isLB_lbPow hω m) hA, cls_lbPow hω, map_sub, map_nsmul, e'])) (lbSecPull _ s _)
  refine ⟨m, t, hm, ?_⟩
  rw [ht, nonzeroLocus_lbSecPull]
  exact (hw ▸ hs : (inc₀ TF.X Z ≫ TF.X.π) y ∈ nonzeroLocus s)
end GlobalTheory.HodgeDominates
end
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

theorem _root_.GlobalTheory.T.hodgeBundle_dominates_of_large_weight : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∃ χ : AllWt.Weight Dw, ∀ y ∈ U₀ TF.X Z, ∀ A : LB TF.Y.X, A.IsLB → ∃ (m : ℕ) (s : (LB.div (lbPow (L₀ TF.X Z χ) m) (A.pull (inc₀ TF.X Z ≫ TF.X.π))).Sec), 0 < m ∧ y ∈ nonzeroLocus s := by
  first | exact @_root_.GlobalTheory.HodgeDominates.exists_weight_hodgeBundle_dominates | exact _root_.GlobalTheory.HodgeDominates.exists_weight_hodgeBundle_dominates | (intros; apply _root_.GlobalTheory.HodgeDominates.exists_weight_hodgeBundle_dominates <;> assumption)
end
end
