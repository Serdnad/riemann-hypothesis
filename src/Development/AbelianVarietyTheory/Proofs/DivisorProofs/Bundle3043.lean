module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2898
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle801
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2757
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle614
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle172
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2883
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle069
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle079
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescentDataChartsCommon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2944
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2945
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CoverRefinementPullback

theorem resG_resG' {X : Scheme.{0}} {O₀ O₁ O₂ : X.Opens} (h : O₁ ≤ O₀) (h' : O₂ ≤ O₁) (s : Γ(X, O₀)) :
    resG X h' (resG X h s) = resG X (h'.trans h) s := by
  simp only [resG]; rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem pbT_id' {X : Scheme.{0}} {O₀ : X.Opens} (s : Γ(X, O₀)) {O : X.Opens} (h : O ≤ O₀) :
    pbT (𝟙 X) s O = resG X h s := by
  unfold pbT; rw [dite_eq_left (show O ≤ (𝟙 X) ⁻¹ᵁ O₀ from h)]; simp [Scheme.Hom.appLE, resG, Category.id_comp]; rfl

theorem dlg_res' {A : Type} [CommRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (L : LB B.left)
    (δ : Fld B.left) (hδ : IsField ⊤ δ) (i j : L.ι) {T : B.left.Opens} (hT : T ≤ L.U i ⊓ L.U j) :
    rsT (dlg B (𝟙 _) L δ i j (L.U i ⊓ L.U j)) T =
      δ T (res hT (L.g i j)).val * (res hT (L.g i j))⁻¹.val := by
  unfold dlg
  rw [GlobalTheory.KS.rsT_of_le hT, map_mul, pbT_id' _ le_rfl, pbT_id' _ le_rfl, ← hδ.2.2 _ _ hT le_top, resG_resG', resG_resG']
  rfl

theorem dlg_tri {A : Type} [CommRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (L : LB B.left) (hL : L.IsLB)
    (δ : Fld B.left) (hδ : IsField ⊤ δ) (i j k : L.ι) {T : B.left.Opens} (h₁ : T ≤ L.U i ⊓ L.U j)
    (h₂ : T ≤ L.U j ⊓ L.U k) (h₃ : T ≤ L.U i ⊓ L.U k) :
    rsT (dlg B (𝟙 _) L δ i j (L.U i ⊓ L.U j)) T + rsT (dlg B (𝟙 _) L δ j k (L.U j ⊓ L.U k)) T =
      rsT (dlg B (𝟙 _) L δ i k (L.U i ⊓ L.U k)) T := by
  rw [dlg_res' B L δ hδ i j h₁, dlg_res' B L δ hδ j k h₂, dlg_res' B L δ hδ i k h₃,
    ← FinAffineCharts.cocycle_on hL i j k h₁ h₂ h₃]
  set u := res h₁ (L.g i j)
  set w := res h₂ (L.g j k)
  rw [mul_inv, Units.val_mul, hδ.2.1 _ le_top, Units.val_mul]
  have hu : (u : Γ(B.left, _)) * (u⁻¹ : Γ(B.left, _)ˣ).val = 1 := Units.mul_inv u
  have hw : (w : Γ(B.left, _)) * (w⁻¹ : Γ(B.left, _)ˣ).val = 1 := Units.mul_inv w
  linear_combination (-(δ _ w.val * (w⁻¹).val)) * hu + (-(δ _ u.val * (u⁻¹).val)) * hw

theorem dlg_refine {A : Type} [CommRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (L : LB B.left)
    (δ : Fld B.left) (hδ : IsField ⊤ δ) {κ : Type} (W : κ → B.left.Opens) (c : κ → L.ι) (h : ∀ a, W a ≤ L.U (c a))
    (a b : κ) {T : B.left.Opens} (hT : T ≤ W a ⊓ W b) :
    rsT (dlg B (𝟙 _) (FinAffineCharts.refineLB L W c h) δ a b (W a ⊓ W b)) T =
      rsT (dlg B (𝟙 _) L δ (c a) (c b) (L.U (c a) ⊓ L.U (c b))) T := by
  refine (dlg_res' B (FinAffineCharts.refineLB L W c h) δ hδ a b hT).trans ?_
  rw [dlg_res' B L δ hδ (c a) (c b) (hT.trans (inf_le_inf (h a) (h b)))]
  have e : res hT ((FinAffineCharts.refineLB L W c h).g a b) =
      res (hT.trans (inf_le_inf (h a) (h b))) (L.g (c a) (c b)) := FinAffineCharts.res_res _ _ _
  exact congrArg (fun u : Γ(B.left, T)ˣ => δ T u.val * (u⁻¹).val) e

theorem rsT_cmul {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R) {O₀ : Y.Opens} (r : R) (s : Γ(Y, O₀))
    (O : Y.Opens) : rsT (constFn q O₀ r * s) O = constFn q O r * rsT s O := by
  by_cases h : O ≤ O₀
  · rw [GlobalTheory.KS.rsT_mul, GlobalTheory.KS.rsT_constFn q h]
  · unfold rsT; simp [h]

theorem sum_reindex {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R) (O : Y.Opens) {d g : ℕ}
    (cc : Fin d → R) (e : Fin d → Fin g) (X : Fin g → Γ(Y, O)) :
    ∑ a, constFn q O (∑ b, if e b = a then cc b else 0) * X a = ∑ b, constFn q O (cc b) * X (e b) := by
  have h0 : ∀ a, constFn q O (∑ b, if e b = a then cc b else 0) = ∑ b, if e b = a then constFn q O (cc b) else 0 := by
    intro a; simp only [constFn, map_sum]; refine Finset.sum_congr rfl fun b _ => ?_; split_ifs <;> simp
  simp only [h0, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (g : ℕ) (w : Fin g → TanM (𝟙 (Sp R)) Dd.toPre.P.A) (dd' : Fin g → Fld Dd.toPre.P.A.left), (∀ a, IsInv Dd.toPre.P.A (w a) (dd' a)) → (∀ u : TanM (𝟙 (Sp R)) Dd.toPre.P.A, ∃ cf : Fin g → R, u = ∑ a, cf a • w a) → ∀ (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι), ⨆ i, V i = ⊤ → (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) → ∀ z : C1 V, IsCoc V z → ∃ (c : Fin g → R) (y : ∀ i, Γ(Dd.toPre.P.A.left, V i)), ∀ i i', z i i' = ∑ a, constFn Dd.toPre.P.A.hom _ (c a) * rsT (dlg Dd.toPre.P.A (𝟙 _) Dd.toPre.P.L (dd' a) (j i) (j i') (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i'))) (V i ⊓ V i') + (rsT (y i') (V i ⊓ V i') - rsT (y i) (V i ⊓ V i')) := by
  intro R _ _ _ _ _ _ Dd g w dd' hinv hspan J V j hV hVj z hz
  have hab : IsAbelianScheme Dd.toPre.P.A := Dd.toPre.P.isAb
  haveI : CompactSpace Dd.toPre.P.A.left := by
    have := hab.proper; exact QuasiCompact.compactSpace_of_compactSpace Dd.toPre.P.A.hom
  obtain ⟨κ, hκ, W, c, hWa, hWc, hWcov⟩ :=
    FinAffineCharts.exists_finite_affine_cover Dd.toPre.P.L Dd.toPre.P.isLB
  have hL' := FinAffineCharts.refineLB_isLB Dd.toPre.P.isLB W c hWc hWcov
  have hiso := FinAffineCharts.iso_refineLB Dd.toPre.P.isLB W c hWc
  have hK' := MulDescent.kTriv_of_lbIso Dd.toPre.P.isLB hL' hiso Dd.toPre.P.ktriv
  have hA' : RelAmple Dd.toPre.P.A (FinAffineCharts.refineLB Dd.toPre.P.L W c hWc) := by
    obtain ⟨w0, hw0⟩ : LBIso (FinAffineCharts.refineLB Dd.toPre.P.L W c hWc)
        (Dd.toPre.P.L.pull (𝟙 Dd.toPre.P.A.left)) :=
      hiso.symm.chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull Dd.toPre.P.L (𝟙 _) (𝟙 _) rfl)
    exact relAmple_pull IsPullback.of_id_fst Dd.toPre.P.isLB hL' ((isGen_iff w0).1 hw0) ⊤
      (isAffineOpen_top _) (fun _ => trivial) Dd.toPre.P.ample
  obtain ⟨bs⟩ := GlobalTheory.T.basis_tangentModule_abelianScheme_of_relDim R Dd.toPre.P.A Dd.toPre.P.g hab Dd.toPre.P.smoothDim
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_subfamily_unique_repr_of_spanning_of_local R _ Dd.toPre.P.g g ⟨bs⟩ w hspan
  have hI := GlobalTheory.T.invariant_vector_fields_basis_tangent R Dd.toPre.P.A Dd.toPre.P.g _ hab Dd.toPre.P.smoothDim hL' hA' hK' hWa hκ
    (fun a => w (e a)) (fun a => dd' (e a)) (fun a => hinv (e a)) he
  obtain ⟨z', b, hz'c, hR1, hR2⟩ := GlobalTheory.T.exists_cechOneCocycle_on_affine_cover_mixed _ J κ V W hV hWa z hz
  obtain ⟨cc, ⟨y', hy'⟩, -⟩ := hI z' hz'c

  obtain ⟨φV, hφV⟩ : ∃ φV : Fin g → C1 V, φV = fun a i i' => rsT (dlg Dd.toPre.P.A (𝟙 _) Dd.toPre.P.L (dd' a)
      (j i) (j i') (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i'))) (V i ⊓ V i') := ⟨_, rfl⟩
  obtain ⟨φU, hφU⟩ : ∃ φU : Fin g → C1 W, φU = fun a k k' => dlg Dd.toPre.P.A (𝟙 _)
      (FinAffineCharts.refineLB Dd.toPre.P.L W c hWc) (dd' a) k k' (W k ⊓ W k') := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : Fin g → ∀ i k, Γ(Dd.toPre.P.A.left, V i ⊓ W k), β = fun a i k =>
      rsT (dlg Dd.toPre.P.A (𝟙 _) Dd.toPre.P.L (dd' a) (j i) (c k)
        (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (c k))) (V i ⊓ W k) := ⟨_, rfl⟩

  have hm1 : ∀ a i i' k, rsT (φV a i i') (V i ⊓ V i' ⊓ W k) =
      rsT (β a i k) (V i ⊓ V i' ⊓ W k) - rsT (β a i' k) (V i ⊓ V i' ⊓ W k) := by
    intro a i i' k
    subst hφV hβ
    have t1 : V i ⊓ V i' ⊓ W k ≤ V i ⊓ V i' := inf_le_left
    have t2 : V i ⊓ V i' ⊓ W k ≤ V i ⊓ W k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have t3 : V i ⊓ V i' ⊓ W k ≤ V i' ⊓ W k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    simp only
    rw [GlobalTheory.KS.rsT_rsT (inf_le_inf (hVj i) (hVj i')) t1, GlobalTheory.KS.rsT_rsT (inf_le_inf (hVj i) (hWc k)) t2,
      GlobalTheory.KS.rsT_rsT (inf_le_inf (hVj i') (hWc k)) t3,
      ← dlg_tri _ _ Dd.toPre.P.isLB (dd' a) (hinv a).1 (j i) (j i') (c k)
        (t1.trans (inf_le_inf (hVj i) (hVj i'))) (t3.trans (inf_le_inf (hVj i') (hWc k)))
        (t2.trans (inf_le_inf (hVj i) (hWc k)))]
    abel
  have hm2 : ∀ a i k k', rsT (φU a k k') (V i ⊓ W k ⊓ W k') =
      rsT (β a i k') (V i ⊓ W k ⊓ W k') - rsT (β a i k) (V i ⊓ W k ⊓ W k') := by
    intro a i k k'
    subst hφU hβ
    have t1 : V i ⊓ W k ⊓ W k' ≤ W k ⊓ W k' := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have t2 : V i ⊓ W k ⊓ W k' ≤ V i ⊓ W k := inf_le_left
    have t3 : V i ⊓ W k ⊓ W k' ≤ V i ⊓ W k' := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    simp only
    rw [dlg_refine _ _ (dd' a) (hinv a).1 W c hWc k k' t1, GlobalTheory.KS.rsT_rsT (inf_le_inf (hVj i) (hWc k)) t2,
      GlobalTheory.KS.rsT_rsT (inf_le_inf (hVj i) (hWc k')) t3,
      ← dlg_tri _ _ Dd.toPre.P.isLB (dd' a) (hinv a).1 (j i) (c k) (c k')
        (t2.trans (inf_le_inf (hVj i) (hWc k))) (t1.trans (inf_le_inf (hWc k) (hWc k')))
        (t3.trans (inf_le_inf (hVj i) (hWc k')))]
    abel

  set q := Dd.toPre.P.A.hom
  have hmix := GlobalTheory.T.isCechOneCoboundary_of_mixed_overlaps _ J κ V W hWcov
    (fun i i' => z i i' - ∑ a, constFn q _ (cc a) * φV (e a) i i')
    (fun k k' => z' k k' - ∑ a, constFn q _ (cc a) * φU (e a) k k')
    (fun i k => b i k - ∑ a, constFn q _ (cc a) * β (e a) i k)
    (fun i i' k => by
      simp only [GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_sum, rsT_cmul, hR1, hm1, mul_sub, Finset.sum_sub_distrib]; abel)
    (fun i k k' => by
      simp only [GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_sum, rsT_cmul, hR2, hm2, mul_sub, Finset.sum_sub_distrib]; abel)
    ⟨y', fun k k' => by subst hφU; exact hy' k k'⟩
  obtain ⟨y, hy⟩ := hmix
  refine ⟨fun a => ∑ b, if e b = a then cc b else 0, y, fun i i' => ?_⟩
  have h := hy i i'
  rw [sum_reindex q _ cc e (fun a => rsT (dlg Dd.toPre.P.A (𝟙 _) Dd.toPre.P.L (dd' a) (j i) (j i')
    (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i'))) (V i ⊓ V i'))]
  simp only at h
  rw [← h]
  subst hφV
  simp only
  abel

end GlobalTheory.CoverRefinementPullback
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegelLevelPull

theorem exists_siegPre_of_points : ∀ (n : ℕ) (hn : 3 ≤ n) (V V₁ : Type) [CommRing V] [CommRing V₁] [IsLocalRing V₁] [IsNoetherianRing V₁] (f₁ : V →+* V₁) (b : cycAway n →+* V) (PB : PolAV (Sp V)) (lev : (Fin PB.g ⊕ Fin PB.g → ℤ) → (Over.mk (spMap f₁) ⟶ PB.A)) (r : ℕ) (d₀ : Fin r → (Over.mk (spMap f₁) ⟶ PB.A)) (c : Fin r → (𝟙_ (Over (Sp V)) ⟶ PB.A)), (∀ x y, lev (x + y) = lev x * lev y) → (∀ x, lev x ^ n = 1) → (∀ x y, Out.WeilIs PB.A PB.L n (lev x) (lev y) (unitOn (Units.map (f₁.comp b).toMonoidHom (GlobalTheory.LowChart.isUnit_zetaAway n hn).unit ^ omegaStd x y))) → (∀ i, d₀ i ^ n = toUnit _ ≫ c i) → ∃ (s : SiegPre PB.g n (zetaAway n) (spMap (f₁.comp b))) (β₁ : s.A.left ⟶ PB.A.left) (β₁₂ : (G2 s.A).left ⟶ (G2 PB.A).left) (d : Fin r → (𝟙_ (Over (Sp V₁)) ⟶ s.A)), s.Principal ∧ IsGrpPullback s.A PB.A (spMap f₁) β₁ ∧ IsSquare β₁ β₁₂ ∧ LBIso s.P ((abelian₂ PB.A PB.L).pull β₁₂) ∧ ∀ i, (d i ^ n).left ≫ β₁ = spMap f₁ ≫ (c i).left := by
  set_option backward.isDefEq.respectTransparency false in
    intro n hn V V₁ _ _ _ _ f₁ b PB lev r d₀ c hadd htors hweil hd
    have hn0 : n ≠ 0 := by omega
    haveI := PB.isAb.comm
    let P₁ : PolAV (Sp V₁) := GlobalTheory.StrictPull.polPull PB (spMap f₁)
    haveI : IsCommMonObj P₁.A := P₁.isAb.comm
    have hpb : IsGrpPullback P₁.A PB.A (spMap f₁) (pullback.fst PB.A.hom (spMap f₁)) :=
      isGrpPullback_pullback PB.A (spMap f₁)
    obtain ⟨κ, hκ⟩ := GlobalTheory.UnifPoint.exists_pointEquiv hpb
    have hk : ∀ x, (κ.symm x).left ≫ pullback.fst PB.A.hom (spMap f₁) = x.left := fun x => by
      rw [← hκ, κ.apply_symm_apply]
    let ze : V₁ˣ := Units.map (f₁.comp b).toMonoidHom (GlobalTheory.LowChart.isUnit_zetaAway n hn).unit
    let lev₁ : (Fin PB.g ⊕ Fin PB.g → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ P₁.A) := fun x => κ.symm (lev x)
    have hL₁ : LBIso P₁.L (PB.L.pull (pullback.fst PB.A.hom (spMap f₁))) :=
      GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB PB.isLB _)
    have hw : ∀ x y, WeilIs P₁.A P₁.L n (lev₁ x) (lev₁ y) (unitOn (ze ^ omegaStd x y)) := fun x y =>
      (GlobalTheory.weilIs_grpPullback_of_comm _ _ PB.A P₁.A (spMap f₁) _ PB.L P₁.L PB.isLB P₁.isLB hpb hL₁ _ n _ _
        (pushPt hpb.1.w (lev₁ x)) (pushPt hpb.1.w (lev₁ y)) _ rfl rfl).2
        (GlobalTheory.UnifPoint.weilIs_congr (Category.id_comp _).symm (hk _).symm (hk _).symm (hweil x y))
    have hadd₁ : ∀ x y, lev₁ (x + y) = lev₁ x * lev₁ y := fun x y => by
      simp only [lev₁, hadd, map_mul]
    have htors₁ : ∀ x, lev₁ x ^ n = 1 := fun x => by
      simp only [lev₁, ← map_pow, htors, map_one]
    have hu : IsUnit (n : V₁) := by simpa using (GlobalTheory.SiegelTor.isUnit_natCast hn0).map (f₁.comp b)
    have hze : (ze : V₁) = (f₁.comp b) (zetaAway n) := by simp [ze]
    have hprim : ∀ (k : Type) [Field k] (gk : V₁ →+* k), IsPrimitiveRoot (gk ze) n := fun k _ gk => by
      rw [hze]; exact GlobalTheory.SiegelTor.isPrimitiveRoot_map hn0 (gk.comp (f₁.comp b))
    haveI : IsMonHom (Iso.refl P₁.A).hom := inferInstanceAs (IsMonHom (𝟙 _))
    have hid : IsGrpPullback P₁.A P₁.A (spMap (RingHom.id V₁)) (𝟙 _) :=
      (isGrpPullback_of_iso (Iso.refl P₁.A)).congr (by simp [spMap]) rfl
    obtain ⟨s, ψ, hψ, hs, hsP⟩ := GlobalTheory.SiegelOverLocal.exists_siegPre V₁ V₁ P₁ (RingHom.id V₁) P₁ (𝟙 _) hid
      (GlobalTheory.lbIso_pull_id P₁.isLB).symm rfl (cycAway n) (f₁.comp b) PB.g n (zetaAway n) ze lev₁ rfl hu hze hprim
      hadd₁ htors₁ hw

    haveI := hψ
    have hLamB : (abelian₂ PB.A PB.L).IsLB := DVR.linComb_isLB _ PB.isLB _ _
    have hLam₁ : (abelian₂ P₁.A P₁.L).IsLB := DVR.linComb_isLB _ P₁.isLB _ _
    obtain ⟨β₂, hsq, hlam⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ (spMap f₁) PB.A P₁.A _ hpb
    have e₁ : LBIso (abelian₂ P₁.A P₁.L) ((abelian₂ PB.A PB.L).pull (β₂ ≫ 𝟙 _)) :=
      hlam PB.L P₁.L _ (abelian₂ PB.A PB.L) (𝟙 _) PB.isLB P₁.isLB hLamB hL₁ (GlobalTheory.lbIso_pull_id hLamB).symm
    rw [Category.comp_id] at e₁
    let κ₂ := (lift (fst s.A s.A ≫ ψ.hom) (snd s.A s.A ≫ ψ.hom)).left
    have e₂ : LBIso ((abelian₂ P₁.A P₁.L).pull κ₂) ((abelian₂ PB.A PB.L).pull (κ₂ ≫ β₂)) :=
      LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ κ₂ κ₂ rfl) (chartPullSame (abelian₂ PB.A PB.L) _ (fun _ => β₂) _ κ₂ fun _ => rfl) e₁
    let d : Fin r → (𝟙_ (Over (Sp V₁)) ⟶ s.A) := fun i => κ.symm (d₀ i) ≫ ψ.inv
    have hpow : ∀ (x : 𝟙_ (Over (Sp V₁)) ⟶ P₁.A) (m : ℕ), ((x ≫ ψ.inv) ^ m) ≫ ψ.hom = x ^ m := fun x m => by
      induction m with
      | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
      | succ m ih => rw [pow_succ, MonObj.mul_comp, ih, Category.assoc, Iso.inv_hom_id, Category.comp_id, pow_succ]
    refine ⟨s, ψ.hom.left ≫ pullback.fst PB.A.hom (spMap f₁), κ₂ ≫ β₂, d, hs,
      ((isGrpPullback_of_iso ψ).comp hpb).congr (Category.id_comp _) rfl, ⟨?_, ?_⟩,
      LBIso.trans s.isLB (pull_isLB hLam₁ _) (pull_isLB hLamB _) hsP e₂, fun i => ?_⟩
    · rw [Category.assoc, hsq.1]
      have e : κ₂ ≫ (fst P₁.A P₁.A).left = (fst s.A s.A).left ≫ ψ.hom.left := by
        simp only [κ₂]; rw [← Over.comp_left, ← Over.comp_left, lift_fst]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst PB.A.hom (spMap f₁)) e).trans (Category.assoc _ _ _))
    · rw [Category.assoc, hsq.2]
      have e : κ₂ ≫ (snd P₁.A P₁.A).left = (snd s.A s.A).left ≫ ψ.hom.left := by
        simp only [κ₂]; rw [← Over.comp_left, ← Over.comp_left, lift_snd]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst PB.A.hom (spMap f₁)) e).trans (Category.assoc _ _ _))
    · have h1 : (d i ^ n).left ≫ ψ.hom.left = (κ.symm (d₀ i) ^ n).left := by
        rw [← Over.comp_left, hpow]
      have hT : (toUnit (Over.mk (spMap f₁))).left = spMap f₁ := by
        simpa using Over.w (toUnit (Over.mk (spMap f₁)))
      calc (d i ^ n).left ≫ ψ.hom.left ≫ pullback.fst PB.A.hom (spMap f₁)
          = ((d i ^ n).left ≫ ψ.hom.left) ≫ pullback.fst PB.A.hom (spMap f₁) := (Category.assoc _ _ _).symm
        _ = (κ.symm (d₀ i) ^ n).left ≫ pullback.fst PB.A.hom (spMap f₁) := by rw [h1]
        _ = (d₀ i ^ n).left := by rw [← map_pow, hk]
        _ = spMap f₁ ≫ (c i).left := by rw [hd, Over.comp_left, hT]

end GlobalTheory.SiegelLevelPull
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowChart.Compare

open TopologicalSpace

section Comp

variable {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}

theorem gm_self_of_pgen (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (hw : PGen w) {Y : Scheme.{0}} (f : Y ⟶ X')
    (y : Y) {j : L.ι} {i : L'.ι} (hj : F (f y) ∈ L.U j) (hi : f y ∈ L'.U i) :
    gm (f ≫ F) y (L.U j ⊓ L.U j) (L.g j j) = 1 := by
  have c := hw Y f y j j i i hj hj hi hi
  rw [gm_self hL' f y hi, inv_one, _root_.mul_one] at c
  exact mul_eq_right.1 c.symm

theorem indep_comp' (w : LB.Iso L' (L.pull F)) (w' : LB.Iso L'' (L'.pull F')) (hw : PGen w) (hw' : PGen w')
    (hL' : L'.IsLB) (hL'' : L''.IsLB) {Y : Scheme.{0}} (f : Y ⟶ X'') (y : Y) (j : L.ι) (i i' : L'.ι) (k : L''.ι)
    (hj : F (F' (f y)) ∈ L.U j) (hi : F' (f y) ∈ L'.U i) (hi' : F' (f y) ∈ L'.U i') (hk : f y ∈ L''.U k) :
    gw w (f ≫ F') y j i * gw w' f y i k = gw w (f ≫ F') y j i' * gw w' f y i' k := by
  have a := hw Y (f ≫ F') y j j i i' hj hj hi hi'
  have b := hw' Y f y i i' k k hi hi' hk hk
  rw [gm_self_of_pgen hL' w hw (f ≫ F') y hj hi] at a
  rw [gm_self hL'' f y hk] at b
  rw [a, b]
  generalize gm (f ≫ F') y _ (L'.g i i') = B
  generalize gw w (f ≫ F') y j i' = C
  generalize gw w' f y i' k = D
  rw [_root_.one_mul, inv_one, _root_.mul_one, _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul]

theorem exists_comp' (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (w' : LB.Iso L'' (L'.pull F')) (hw : PGen w)
    (hw' : PGen w') (hL'' : L''.IsLB) :
    ∃ w'' : LB.Iso L'' (L.pull (F' ≫ F)), Tri w w' w'' := by
  have glue : ∀ (j : L.ι) (k : L''.ι), ∃ s : Γ(X'', (L.pull (F' ≫ F)).U (fun _ => j) ⊓ L''.U k)ˣ,
      ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (i : L'.ι), F (F' (f y)) ∈ L.U j → F' (f y) ∈ L'.U i → f y ∈ L''.U k →
        gm f y _ s = gw w (f ≫ F') y j i * gw w' f y i k := by
    intro j k
    obtain ⟨W, hW⟩ : ∃ W : L'.ι → X''.Opens, ∀ i x, x ∈ W i ↔ F (F' x) ∈ L.U j ∧ F' x ∈ L'.U i ∧ x ∈ L''.U k :=
      ⟨fun i => F' ⁻¹ᵁ (F ⁻¹ᵁ L.U j) ⊓ (F' ⁻¹ᵁ L'.U i ⊓ L''.U k), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ i, W i ≤ (L.pull (F' ≫ F)).U (fun _ => j) ⊓ L''.U k := fun i x hx =>
      ⟨mem_pull₂.2 ((hW i x).1 hx).1, ((hW i x).1 hx).2.2⟩
    have l₁ : ∀ i, W i ≤ F' ⁻¹ᵁ ((L.pull F).U (fun _ => j) ⊓ L'.U i) := fun i x hx =>
      ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_pull.2 ((hW i x).1 hx).1, ((hW i x).1 hx).2.1⟩
    have l₂ : ∀ i, W i ≤ (L'.pull F').U (fun _ => i) ⊓ L''.U k := fun i x hx =>
      ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_pull.2 ((hW i x).1 hx).2.1, ((hW i x).1 hx).2.2⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(X'', W i)ˣ, ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (i : L'.ι), f y ∈ W i →
        gm f y (W i) (u i) = gw w (f ≫ F') y j i * gw w' f y i k :=
      ⟨fun i => res (l₁ i) (pullU F' _ (w.s (fun _ => j, i))) * res (l₂ i) (w'.s (fun _ => i, k)), fun Y f y i hy =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res f y (l₁ i) hy _).trans (gm_pull f F' y _ (l₁ i hy) _)) (gm_res f y (l₂ i) hy _))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        obtain ⟨i, hi⟩ := exists_chart hL' (F' x)
        exact Opens.mem_iSup.2 ⟨i, (hW i x).2 ⟨mem_pull₂.1 hx.1, hi, hx.2⟩⟩) u (fun i i' x hx => by
        have h₁ := (hW i x).1 hx.1
        have h₂ := (hW i' x).1 hx.2
        exact (hu _ (𝟙 X'') x i hx.1).trans ((indep_comp' w w' hw hw' hL' hL'' (𝟙 X'') x j i i' k h₁.1 h₁.2.1
          h₂.2.1 h₁.2.2).trans (hu _ (𝟙 X'') x i' hx.2).symm))
    refine ⟨s, fun Y f y i hj hi hk => ?_⟩
    have hy := (hW i (f y)).2 ⟨hj, hi, hk⟩
    exact (gm_res f y (l₀ i) hy s).symm.trans ((congrArg (gm f y (W i)) (hs i)).trans (hu Y f y i hy))
  choose s hs using glue
  exact ⟨⟨fun p => s (p.1 PUnit.unit) p.2⟩, fun Y f y j i k hj hi hk => hs j k Y f y i hj hi hk⟩

end Comp

end GlobalTheory.LowChart.Compare

namespace GlobalTheory.LowChart

theorem exists_siegAt_of_siegPB : ∀ {o : Type} [CommRing o] {ζ : o} {h n : ℕ} (F : SFam h n ζ) {S S₀ : Scheme.{0}} (g : S ⟶ S₀) (s' : S ⟶ Sp o) (x : S ⟶ F.X), x ≫ F.s = s' → ∀ (c : SiegPre h n ζ s'), SiegPB c F.univ x → ∀ (A₀ : Over S₀) [GrpObj A₀] [IsCommMonObj A₀] (Q : LB (G2 A₀).left) (β : c.A.left ⟶ A₀.left) (β₂ : (G2 c.A).left ⟶ (G2 A₀).left), IsGrpPullback c.A A₀ g β → IsSquare β β₂ → LBIso c.P (Q.pull β₂) → ∀ (r : ℕ) (d : Fin r → (𝟙_ (Over S) ⟶ c.A)), ∃ (v : S ⟶ (GlobalTheory.LowChart.powA F r).left) (hs : v ≫ GlobalTheory.LowChart.toO F r = s') (β₁ : (GlobalTheory.LowChart.siegAt F v s' hs).A.left ⟶ A₀.left) (β₁₂ : (G2 (GlobalTheory.LowChart.siegAt F v s' hs).A).left ⟶ (G2 A₀).left), IsGrpPullback (GlobalTheory.LowChart.siegAt F v s' hs).A A₀ g β₁ ∧ IsSquare β₁ β₁₂ ∧ LBIso (GlobalTheory.LowChart.siegAt F v s' hs).P (Q.pull β₁₂) ∧ ∀ a, (GlobalTheory.LowChart.cAt F v s' hs a).left ≫ β₁ = (∏ i, d i ^ a i).left ≫ β := by
  intro o _ ζ h n F S S₀ g s' x hx c hc A₀ _ _ Q β β₂ hβ hβ₂ hQ r d
  obtain ⟨φ, φ₂, hφ, hφ₂, hP, -⟩ := hc
  have hp : ∀ i, ((d i).left ≫ φ) ≫ F.univ.A.hom = x := fun i => by
    rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w (d i)]
    exact Category.id_comp _
  obtain ⟨v, hv, hvc⟩ : ∃ v : S ⟶ (powA F r).left, v ≫ (powA F r).hom = x ∧
      ∀ i, v ≫ (coord F i).left = (d i).left ≫ φ :=
    ⟨lift x (fun i => (d i).left ≫ φ) hp, lift_hom _ _ _, fun i => lift_coord _ _ _ i⟩
  have hs : v ≫ toO F r = s' := by
    rw [toO, ← Category.assoc, hv, hx]
  refine ⟨v, hs, ?_⟩
  have hpb : IsGrpPullback (siegAt F v s' hs).A F.univ.A x (Pdiv.PullbackComparison.pφ (v ≫ (powA F r).hom) F.univ.A) :=
    (Pdiv.PullbackComparison.isGrpPullback _ _).congr hv rfl
  obtain ⟨e, he, heφ⟩ := grpPullback_iso hpb hφ
  haveI := he
  let C := siegAt F v s' hs
  let θ₂ : (G2 C.A).left ⟶ (G2 c.A).left := (CartesianMonoidalCategory.lift (fst C.A C.A ≫ e.hom) (snd C.A C.A ≫ e.hom)).left
  have hθf : θ₂ ≫ (fst c.A c.A).left = (fst C.A C.A).left ≫ e.hom.left := by
    rw [← Over.comp_left, CartesianMonoidalCategory.lift_fst, Over.comp_left]
  have hθs : θ₂ ≫ (snd c.A c.A).left = (snd C.A C.A).left ≫ e.hom.left := by
    rw [← Over.comp_left, CartesianMonoidalCategory.lift_snd, Over.comp_left]
  refine ⟨e.hom.left ≫ β, θ₂ ≫ β₂, ((isGrpPullback_of_iso e).comp hβ).congr (Category.id_comp g) rfl,
    ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Category.assoc, hβ₂.1, ← Category.assoc, hθf, Category.assoc]
  · rw [Category.assoc, hβ₂.2, ← Category.assoc, hθs, Category.assoc]
  · have hθ₂ : Pdiv.PullbackComparison.pφ₂ (v ≫ (powA F r).hom) F.univ.A = θ₂ ≫ φ₂ :=
      have e1 : (θ₂ ≫ φ₂) ≫ (fst F.univ.A F.univ.A).left =
          (fst C.A C.A).left ≫ Pdiv.PullbackComparison.pφ (v ≫ (powA F r).hom) F.univ.A := by
        rw [Category.assoc, hφ₂.1, ← Category.assoc, hθf, Category.assoc, heφ]
      have e2 : (θ₂ ≫ φ₂) ≫ (snd F.univ.A F.univ.A).left =
          (snd C.A C.A).left ≫ Pdiv.PullbackComparison.pφ (v ≫ (powA F r).hom) F.univ.A := by
        rw [Category.assoc, hφ₂.2, ← Category.assoc, hθs, Category.assoc, heφ]
      Pdiv.PullbackComparison.adelic_GL2_ext_of_local_components (G := F.univ.A) _ _
        ((Pdiv.PullbackComparison.pφ₂_fst _ _).trans e1.symm) ((Pdiv.PullbackComparison.pφ₂_snd _ _).trans e2.symm)
    have w1 : LBIso C.P (c.P.pull θ₂) :=
      LBIso.chartPull (chartPullSame F.univ.P (fun _ : PUnit.{1} => Pdiv.PullbackComparison.pφ₂ (v ≫ (powA F r).hom) F.univ.A)
        (fun _ => φ₂) (fun _ => 1) θ₂ (fun _ => hθ₂)) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull c.P θ₂ θ₂ rfl) (LBIso.symm hP)
    obtain ⟨w, hw⟩ := hQ
    obtain ⟨w', hw'⟩ := w1
    have pw := (isGen_iff w).1 hw
    have pw' := (isGen_iff w').1 hw'
    obtain ⟨w'', T⟩ := Compare.exists_comp' c.isLB w w' pw pw' C.isLB
    exact ⟨w'', (isGen_iff w'').2 (T.pgen_comp c.isLB pw pw')⟩
  · have hpt : ∀ i, ptAt F v s' hs i ≫ e.hom = d i := fun i =>
      Over.OverMorphism.ext (hφ.1.hom_ext
        (by rw [Over.comp_left, Category.assoc, heφ, ptAt_left, hvc])
        (by rw [Over.comp_left, Category.assoc, Over.w e.hom, Over.w (ptAt F v s' hs i), Over.w (d i)]))
    let ψ : (𝟙_ (Over S) ⟶ C.A) →* (𝟙_ (Over S) ⟶ c.A) :=
      MonoidHom.mk' (· ≫ e.hom) fun a b => MonObj.mul_comp a b e.hom
    intro a
    have key : cAt F v s' hs a ≫ e.hom = ∏ i, d i ^ a i := by
      show ψ (cAt F v s' hs a) = _
      rw [cAt, map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_zpow]
      exact congrArg (· ^ a i) (hpt i)
    rw [← Category.assoc, ← Over.comp_left, key]

end GlobalTheory.LowChart
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.abelianSchemeDescentData_charts_common : ∀ σ : Setup, σ.Common := by
  first | exact @GlobalTheory.Desc.setup_common | exact GlobalTheory.Desc.setup_common | (intros; apply GlobalTheory.Desc.setup_common <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.ringHomCoeffSpanSet_sections_flat_baseChange_normal : ∀ (R R₁ F F₁ : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CommRing R₁] [IsDomain R₁] [IsNoetherianRing R₁] [IsIntegrallyClosed R₁] [Field F] [Field F₁] (ρ : R →+* R₁) (c₀ : R →+* F) (c₁ : R₁ →+* F₁) (θ : F →+* F₁) (f : R), f ≠ 0 → ρ.Flat → Function.Injective ρ → Function.Injective c₀ → θ.comp c₀ = c₁.comp ρ → LinDisj c₀ c₁ θ → ∀ (V₀ : Set F), (0 : F) ∈ V₀ → (∀ a ∈ V₀, ∀ b ∈ V₀, a + b ∈ V₀) → (∀ r, ∀ a ∈ V₀, c₀ r * a ∈ V₀) → (∀ a ∈ V₀, (c₀ f)⁻¹ * a ∈ V₀) → ∀ (W : Ideal R → Set F) (W₁ : Ideal R₁ → Set F₁), (∀ p : Ideal R, p.IsPrime → f ∈ p → ∀ u, ∃ m : ℕ, c₀ f ^ m * u ∈ W p) → (∀ p : Ideal R, p.IsPrime → p.height = 1 → f ∈ p → (∀ a ∈ W p, ∀ b ∈ W p, a + b ∈ W p) ∧ (∀ r, ∀ a ∈ W p, c₀ r * a ∈ W p) ∧ (∀ s, s ∉ p → ∀ a ∈ W p, (c₀ s)⁻¹ * a ∈ W p)) → (∀ q : Ideal R₁, q.IsPrime → q.height = 1 → ρ f ∈ q → GaussAt c₁ q θ (W (q.comap ρ)) (W₁ q)) → spanBy c₁ (θ '' {u | u ∈ V₀ ∧ ∀ p : Ideal R, p.IsPrime → p.height = 1 → f ∈ p → u ∈ W p}) = spanBy c₁ (θ '' V₀) ∩ {v | ∀ q : Ideal R₁, q.IsPrime → q.height = 1 → ρ f ∈ q → v ∈ W₁ q} := by
  first | exact @GlobalTheory.Desc.spanBy_sections_eq_of_flat | exact GlobalTheory.Desc.spanBy_sections_eq_of_flat | (intros; apply GlobalTheory.Desc.spanBy_sections_eq_of_flat <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.proj_model_baseChange_standard_open_app_injective : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F), GradedFam c₀ N → ∀ (P : Scheme.{0}) [IsIntegral P] (p : P ⟶ Sp R) (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (ρ : R →+* R₁), ρ.Flat → Function.Injective c₀ → ∀ (Y : Scheme.{0}) [IsIntegral Y] [CompactSpace Y] [QuasiSeparatedSpace Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (D₁ : CartierDiv Y), θ.comp c₀ = (GlobalTheory.Desc.cst q).comp ρ → LinDisj c₀ (GlobalTheory.Desc.cst q) θ → AmpleDiv D₁ → (∀ k, Sec D₁ k = spanBy (GlobalTheory.Desc.cst q) (θ '' N k)) → ∀ m : Y ⟶ P, PFF (𝟙 _) m (θ.comp ψ) → (∀ k, 1 ≤ k → ∀ b ∈ N k, ∀ y, m y ∈ Dp k b ↔ y ∈ locus D₁ k (θ b)) → ∀ (hm : m ≫ p = q ≫ spMap ρ) (k : ℕ), 1 ≤ k → ∀ b ∈ N k, Function.Injective ((pullback.lift m q hm).app ((pullback.fst p (spMap ρ)) ⁻¹ᵁ Dp k b)) := by
  first | exact @GlobalTheory.Desc.BaseInj.app_injective | exact GlobalTheory.Desc.BaseInj.app_injective | (intros; apply GlobalTheory.Desc.BaseInj.app_injective <;> assumption)
end
