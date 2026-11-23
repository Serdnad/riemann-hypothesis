module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1743
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1666
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle978
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1609
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1761
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSCore.RegSeqGlue

open GlobalTheory.Twist

variable {Y : Scheme.{0}} {L : LB Y}

def LocSpan (F : Y.Modules) {d : ℕ} (t : Fin d → L.Sec) {l m : ℤ} (h : l + 1 = m) {O : Y.Opens}
    (x : Γ(twistZ F L m, O)) : Prop :=
  ∀ y ∈ O, ∃ (V : Y.Opens) (hV : V ≤ O), y ∈ V ∧ ∃ c : Fin d → Γ(twistZ F L l, V),
    (twistZ F L m).presheaf.map (homOfLE hV).op x = ∑ i, (mulSecOfEq F (zofSec (t i)) h).app V (c i)

theorem res_res (G : Y.Modules) {U V W : Y.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (x : Γ(G, U)) :
    G.presheaf.map (homOfLE h₁).op (G.presheaf.map (homOfLE h₂).op x) =
      G.presheaf.map (homOfLE (h₁.trans h₂)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

theorem eq_zero_of_locSpan (F : Y.Modules) (t : Fin 0 → L.Sec) {l m : ℤ} (h : l + 1 = m) {O : Y.Opens}
    (x : Γ(twistZ F L m, O)) (hx : LocSpan F t h x) : x = 0 :=
  section_eq_zero_of_germ x fun y hy => by
    obtain ⟨V, hV, hyV, c, e⟩ := hx y hy
    rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hV) y hyV, e, Finset.univ_eq_empty, Finset.sum_empty, map_zero]

variable (hL : L.IsLB)

theorem π_mul (F : Y.Modules) (s a : L.Sec) {l m : ℤ} (h : l + 1 = m) (V : Y.Opens) (u : Γ(twistZ F L l, V)) :
    (Twist.map (lbZPow L m) (cutπ F hL s)).app V ((mulSecOfEq F (zofSec a) h).app V u) =
      (mulSecOfEq (cut F hL s) (zofSec a) h).app V ((Twist.map (lbZPow L l) (cutπ F hL s)).app V u) := by
  rw [app_app, app_app, mulSecOfEq_naturality]

theorem map_locSpan (F : Y.Modules) {d : ℕ} (t : Fin (d + 1) → L.Sec) [Mono (cutHom F hL (t 0))] {l m : ℤ}
    (h : l + 1 = m) {O : Y.Opens} {x : Γ(twistZ F L m, O)} (hx : LocSpan F t h x) :
    LocSpan (cut F hL (t 0)) (fun i => t i.succ) h ((Twist.map (lbZPow L m) (cutπ F hL (t 0))).app O x) :=
  fun y hy => by
    obtain ⟨V, hV, hyV, c, e⟩ := hx y hy
    refine ⟨V, hV, hyV, fun i => (Twist.map (lbZPow L l) (cutπ F hL (t 0))).app V (c i.succ), ?_⟩
    have := (RegSeqKer.shortExact_twistComplex hL F (t 0) h).mono_f
    have hex : Function.Exact ((mulSecOfEq F (zofSec (t 0)) h).app V)
        ((Twist.map (lbZPow L m) (cutπ F hL (t 0))).app V) :=
      exact_app_of_exact_of_mono (RegSeqKer.shortExact_twistComplex hL F (t 0) h).exact V

    rw [← app_res, e, Fin.sum_univ_succ, map_add (f := _), hex.apply_apply_eq_zero, zero_add, map_sum]
    exact Finset.sum_congr rfl fun i _ => π_mul hL F _ _ h V _

theorem exists_glue (d : ℕ) : ∀ (t : Fin d → L.Sec) (F : Y.Modules) [F.IsQuasicoherent] (j₀ l m : ℤ)
    (h : l + 1 = m), RegSeq hL F (List.ofFn t) → VanishFrom L F j₀ → j₀ + d ≤ m →
    ∀ (W : Y → Y.Opens) (b : ∀ y, Γ(twistZ F L m, W y)), (∀ y, y ∈ W y) →
    (∀ y z, LocSpan F t h ((twistZ F L m).presheaf.map (homOfLE (inf_le_left : W y ⊓ W z ≤ W y)).op (b y) -
      (twistZ F L m).presheaf.map (homOfLE (inf_le_right : W y ⊓ W z ≤ W z)).op (b z))) →
    ∃ σ : Γ(twistZ F L m, ⊤), ∀ y, LocSpan F t h ((twistZ F L m).presheaf.map (homOfLE le_top).op σ - b y) := by
  induction d with
  | zero =>
    intro t F _ j₀ l m h _ _ _ W b hW hb
    have hc : ∀ y z, (twistZ F L m).presheaf.map (homOfLE (inf_le_left : W y ⊓ W z ≤ W y)).op (b y) =
        (twistZ F L m).presheaf.map (homOfLE (inf_le_right : W y ⊓ W z ≤ W z)).op (b z) := fun y z =>
      sub_eq_zero.1 (eq_zero_of_locSpan F t h _ (hb y z))
    obtain ⟨σ, hσ, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨(twistZ F L m).presheaf, (twistZ F L m).isSheaf⟩ W ⊤
      (fun y => homOfLE le_top) (fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) b (fun y z => hc y z)
    refine ⟨σ, fun y z hz => ⟨W y, le_rfl, hz, fun i => i.elim0, ?_⟩⟩
    rw [hσ y, sub_self, map_zero, Finset.univ_eq_empty, Finset.sum_empty]
  | succ d ih =>
    intro t F _ j₀ l m h hr hv hj W b hW hb
    rw [List.ofFn_succ, regSeq_cons] at hr
    obtain ⟨hm0, hr⟩ := hr
    have hS := RegSeqKer.shortExact_twistComplex hL F (t 0) h
    have := hS.mono_f
    have hex : ∀ V : Y.Opens, Function.Exact ((mulSecOfEq F (zofSec (t 0)) h).app V)
        ((Twist.map (lbZPow L m) (cutπ F hL (t 0))).app V) := fun V =>
      exact_app_of_exact_of_mono hS.exact V
    obtain ⟨σ', hσ'⟩ := ih (fun i => t i.succ) (cut F hL (t 0)) (j₀ + 1) l m h hr
      (RegSeqKer.vanishFrom_cut hL F (t 0) hv) (by push_cast at hj; omega) W
      (fun y => (Twist.map (lbZPow L m) (cutπ F hL (t 0))).app (W y) (b y)) hW fun y z => by
        have := map_locSpan hL F t h (hb y z)
        rwa [map_sub, app_res, app_res] at this
    obtain ⟨σ, hσ⟩ := cohOn.app_surjective hS ⊤ (hv l (by push_cast at hj; omega) 1 one_pos) σ'
    change (Twist.map (lbZPow L m) (cutπ F hL (t 0))).app ⊤ σ = σ' at hσ
    have hEpi : Epi (Twist.map (lbZPow L l) (cutπ F hL (t 0))) :=
      (RegSeqKer.shortExact_twistComplex hL F (t 0) (l := l - 1) (m := l) (by omega)).epi_g
    have := isQuasicoherent_twist (F := F) (isLB_lbZPow hL l)
    have := isQuasicoherent_twist (F := cut F hL (t 0)) (isLB_lbZPow hL l)
    refine ⟨σ, fun y z hz => ?_⟩
    obtain ⟨V, hV, hzV, c', e⟩ := hσ' y z hz
    obtain ⟨A, hzA, hAV⟩ := exists_affine hzV
    have hlift : ∀ i, ∃ u : Γ(twistZ F L l, A.1), (Twist.map (lbZPow L l) (cutπ F hL (t 0))).app A.1 u =
        (twistZ (cut F hL (t 0)) L l).presheaf.map (homOfLE hAV).op (c' i) := fun i =>
      surjective_app_of_epi _ A.2 _
    choose u hu using hlift
    obtain ⟨v, hv'⟩ := (hex A.1 ((twistZ F L m).presheaf.map (homOfLE (hAV.trans hV)).op
        ((twistZ F L m).presheaf.map (homOfLE le_top).op σ - b y) -
        ∑ i, (mulSecOfEq F (zofSec (t i.succ)) h).app A.1 (u i))).1 (by

      rw [map_sub, map_sum, sub_eq_zero]
      erw [app_res, map_sub, app_res, hσ]
      rw [← res_res _ hAV hV]
      erw [e]

      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [π_mul, hu]
      exact (app_res _ _ _).symm)
    refine ⟨A.1, hAV.trans hV, hzA, Fin.cons v u, ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hv', sub_add_cancel]

end GlobalTheory.HSCore.RegSeqGlue

namespace GlobalTheory.HSCore.RegSeqGlue

open GlobalTheory.Twist GlobalTheory.HSKerRes

variable {k : Type} [CommRing k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) {M L : LB Y} (hM : M.IsLB) (hL : L.IsLB)


include hM hL in
theorem toH0_res {n : ℤ} {O O' : Y.Opens} (h : O' ≤ O) (s : Γ(twistZ (LB.toMod M) L n, O)) :
    toH0 p ((twistZ (LB.toMod M) L n).presheaf.map (homOfLE h).op s) = H0.restr h (toH0 p s) :=
  tw_ext hM hL fun i j y hy hi hj => by
    rw [H0.germ_restr, germ_of_global_section p _ i j y _ hi hj, germ_of_global_section p _ i j y _ hi hj]
    erw [Twist.zcoord_resM]
    rw [HSKerRes.coord_resM, ger_resG]


include hM in
theorem vanishesTo_mulSec {d : ℕ} (t : Fin d → L.Sec) (a : Fin d) {n l : ℤ} (h : n + 1 = l) {O : Y.Opens}
    (f : Vanishing.H0 p (tw M L n) O) : VanishesTo (cutIdeal hL t) 1 (mulSec hM hL (t a) h f) :=
  vanishesTo_of_exists fun y _ hy => by
    obtain ⟨i, hi⟩ := exists_chart hM y
    obtain ⟨j, hj⟩ := exists_chart hL y
    refine ⟨twIdx l i j, mem_tw_U.2 ⟨hi, hj⟩, ?_⟩
    rw [germ_mulSec _ _ _ _ _ _ _ _ _ hi hj, pow_one, stalkId_cutIdeal hL t j y hj]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨a, rfl⟩)


include hM in
theorem vanishesTo_of_locSpan {d : ℕ} (t : Fin d → L.Sec) {l m : ℤ} (h : l + 1 = m) {O : Y.Opens}
    (x : Γ(twistZ (LB.toMod M) L m, O)) (hx : LocSpan (LB.toMod M) t h x) :
    VanishesTo (cutIdeal hL t) 1 (toH0 p x) := fun y hs hy i hi => by
  obtain ⟨V, hV, hyV, c, e⟩ := hx y hy
  have hv : VanishesTo (cutIdeal hL t) 1 (H0.restr hV (toH0 p x)) := by

    rw [← toH0_res p hM hL, e, map_sum]
    show _ ∈ filTop p _ V (cutIdeal hL t) 1
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [mem_filTop, global_section_mul p hM hL (t a) h]
    exact vanishesTo_mulSec p hM hL t a h _
  have := hv y hs hyV i hi
  rwa [H0.germ_restr] at this


include hM in
theorem locSpan_of_vanishesTo {d : ℕ} (t : Fin d → L.Sec) {l m : ℤ} (h : l + 1 = m) {O : Y.Opens}
    (s : Γ(twistZ (LB.toMod M) L m, O)) (hs : VanishesTo (cutIdeal hL t) 1 (toH0 p s)) :
    LocSpan (LB.toMod M) t h s := fun y hy => by
  obtain ⟨i, hi⟩ := exists_chart hM y
  obtain ⟨j, hj⟩ := exists_chart hL y
  obtain ⟨V, hV, e⟩ := exists_affine (memInf (memInf hy hi) hj)
  have hVO : V.1 ≤ O := e.trans (inf_le_left.trans inf_le_left)
  have hVi : V.1 ≤ M.U i := e.trans (inf_le_left.trans inf_le_right)
  have hVj : V.1 ≤ L.U j := e.trans inf_le_right
  have h₁ : V.1 ≤ O ⊓ (tw M L m).U (twIdx m i j) := fun _ hz => ⟨hVO hz, mem_tw_U.2 ⟨hVi hz, hVj hz⟩⟩
  have h₂ := vanishesTo_iff_affine.1 hs V _ h₁
  rw [pow_one, ideal_cutIdeal hL t V j hVj, restricted_section_chart_coords p s i j h₁ (le_inf (le_inf hVO hVj) hVi)] at h₂
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 h₂
  refine ⟨V.1, hVO, hV, fun a => (Twist.zchartEquiv hL l j hVj).symm ((LB.chartEquiv hM i hVi).symm (c a)), ?_⟩
  refine (Twist.zchartEquiv hL m j hVj).injective ((LB.chartEquiv hM i hVi).injective ?_)

  simp only [map_sum, Twist.zchartEquiv_mulSecOfEq_app, map_smul, LinearEquiv.apply_symm_apply, Twist.zfun_zofSec,
  smul_eq_mul]
  rw [LB.chartEquiv_apply, Twist.zchartEquiv_apply]
  refine Eq.trans ?_ (hc.symm.trans (Finset.sum_congr rfl fun a _ => mul_comm _ _))
  rw [HSKerRes.coord_resM]
  erw [Twist.zcoord_resM]
  rw [HSKerRes.coord_resM, LB.resG_resG, LB.resG_resG]

end GlobalTheory.HSCore.RegSeqGlue

theorem GlobalTheory.HSCore.exists_glue_mod_regSeq : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (GlobalTheory.strHom k (X := Y)) → ∀ (p : Y ⟶ Sp k) (M L : LB Y), M.IsLB → ∀ (hL : L.IsLB) (d : ℕ) (t : Fin d → L.Sec) (l : ℤ), RegSeq hL (GlobalTheory.LB.toMod M) (List.ofFn t) → VanishFrom L (GlobalTheory.LB.toMod M) 0 → (d : ℤ) ≤ l → ∀ (W : Y → Y.Opens) (b : ∀ y, Vanishing.H0 p (tw M L l) (W y)), (∀ y, y ∈ W y) → (∀ y z, VanishesTo (cutIdeal hL t) 1 (Vanishing.H0.restr inf_le_left (b y) - Vanishing.H0.restr inf_le_right (b z) : Vanishing.H0 p (tw M L l) (W y ⊓ W z))) → ∃ σ : Vanishing.H0 p (tw M L l) ⊤, ∀ y, VanishesTo (cutIdeal hL t) 1 (Vanishing.H0.restr le_top σ - b y) := by
  intro k _ Y _ _ p M L hM hL d t l hreg hvan hd W b hW hb
  have hl : l - 1 + 1 = l := by omega
  have := (VB.isVB_toMod hM).isFiniteQC
  have hs : ∀ y, ∃ β : Γ(twistZ (LB.toMod M) L l, W y), HSKerRes.toH0 p β = b y := fun y =>
    HSKerRes.surjective_ofTwist hM (Twist.isLB_lbZPow hL _) (b y)
  choose β hβ using hs
  obtain ⟨σ, hσ⟩ := RegSeqGlue.exists_glue hL d t (LB.toMod M) 0 (l - 1) l hl hreg hvan (by omega) W β hW
    fun y z => RegSeqGlue.locSpan_of_vanishesTo p hM hL t hl _ (by
      rw [map_sub, RegSeqGlue.toH0_res p hM hL, RegSeqGlue.toH0_res p hM hL, hβ, hβ]
      exact hb y z)
  refine ⟨HSKerRes.toH0 p σ, fun y => ?_⟩
  have := RegSeqGlue.vanishesTo_of_locSpan p hM hL t hl _ (hσ y)
  rwa [map_sub, RegSeqGlue.toH0_res p hM hL, hβ] at this
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

theorem _root_.GlobalTheory.T.rightLieDerivative_realEntryPolynomialFunction : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), RealPoints θ V → ∀ (τ : D.what₂.Tau) (X : LieAt V τ) (P : PolyE V), lieDer V (expInf θ V) (atPlace V τ X) (polyFun θ V P) = polyFun θ V (matDer τ X.1 P) := by
  first | exact @GlobalTheory.PolyRightDeriv.lieDer_polyFun | exact GlobalTheory.PolyRightDeriv.lieDer_polyFun | (intros; apply GlobalTheory.PolyRightDeriv.lieDer_polyFun <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

theorem _root_.GlobalTheory.T.polyFun_mem_smooth_vectors : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), RealPoints θ V → ∀ P : PolyE V, polyFun θ V P ∈ SmF θ V := by
  first | exact @GlobalTheory.CentralOps.polyFun_mem_smF | exact GlobalTheory.CentralOps.polyFun_mem_smF | (intros; apply GlobalTheory.CentralOps.polyFun_mem_smF <;> assumption)
end

section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

noncomputable section

namespace GlobalTheory.FinLatHeis

open GlobalTheory.FinLatF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}

theorem unitary_mtF {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : GAF σ J) :
    ((mtF σ J g).map (cAF σ))ᵀ * J.map (incAF F E) * mtF σ J g = J.map (incAF F E) :=
  g.2

theorem hOF_actOF (hS : IsHermND σ JS) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    hOF σ JS JT (actOF σ JS JT g h x) (actOF σ JS JT g h y) = hOF σ JS JT x y := by
  have hu : IsUnit JS.det := isUnit_iff_ne_zero.mpr hS.2
  have h1 : JS⁻¹.map (incAF F E) * JS.map (incAF F E) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu]
    exact Matrix.map_one _ (incAF F E).map_zero (incAF F E).map_one
  exact GlobalTheory.SymplOInv.sum_unitary (cAF σ) (JT.map (incAF F E)) (mtF σ JT h) (JS⁻¹.map (incAF F E))
    (JS.map (incAF F E)) (mtF σ JS g⁻¹) h1 (unitary_mtF h) (unitary_mtF g⁻¹) x y

theorem symplOHF_actOF (hS : IsHermND σ JS) (ξ₀ : E) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ (actOF σ JS JT g h x) (actOF σ JS JT g h y) = symplOHF σ JS JT ξ₀ x y := by
  unfold symplOHF symplOF
  rw [hOF_actOF hS]


variable (F E) in
def realIdF : AEF F E := algebraMap (AF F) (AEF F E) (pairA F 1 0)

theorem infPartF_realIdF : infPartF F E (realIdF F E) = 1 := by
  show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (pairA F 1 0 ⊗ₜ[F] (1 : E)) = 1
  rw [Algebra.TensorProduct.map_tmul, show fstA F (pairA F 1 0) = 1 from rfl]
  rfl

theorem realIdF_mul_of_inf {z : AEF F E} (hz : infPartF F E z = 0) : realIdF F E * z = 0 := by
  rw [realIdF, ← Algebra.smul_def]
  exact GlobalTheory.HeisThetaF.smul_eq_zero_of_infPartF hz

theorem realIdF_smul_of_fin {x : WOF F E nS nT} (hx : x.map (infPartF F E) = 0) : realIdF F E • x = 0 := by
  ext i j
  exact realIdF_mul_of_inf (congrFun (congrFun hx i) j)

theorem fin_part (w₀ : WOF F E nS nT) : ((1 - realIdF F E) • w₀).map (infPartF F E) = 0 := by
  funext i j
  show infPartF F E ((1 - realIdF F E) * w₀ i j) = 0
  rw [map_mul, map_sub, infPartF_realIdF, map_one, sub_self, zero_mul]

theorem decomp (w₀ : WOF F E nS nT) : w₀ = realIdF F E • w₀ + (1 - realIdF F E) • w₀ := by
  rw [← add_smul, add_sub_cancel, one_smul]

theorem symplOF_real_fin (hσ : ∀ x, σ (σ x) = x) (ξ₀ : E) (u : WOF F E nS nT) {x : WOF F E nS nT}
    (hx : x.map (infPartF F E) = 0) : symplOF σ JS JT ξ₀ (realIdF F E • u) x = 0 := by
  rw [symplOF_smul σ JS JT hσ, realIdF, GlobalTheory.HeisThetaF.cAF_algebraMap, ← realIdF, realIdF_smul_of_fin hx,
    GlobalTheory.HeisLineF.symplOF_zero_right]

theorem symplOHF_real_fin (hσ : ∀ x, σ (σ x) = x) (ξ₀ : E) (u : WOF F E nS nT) {x : WOF F E nS nT}
    (hx : x.map (infPartF F E) = 0) : symplOHF σ JS JT ξ₀ (realIdF F E • u) x = 0 := by
  unfold symplOHF; rw [symplOF_real_fin hσ ξ₀ u hx, mul_zero]

theorem symplOHF_fin_real (hσ : ∀ x, σ (σ x) = x) (hS : IsHermND σ JS) (hT : IsHermND σ JT) {ξ₀ : E}
    (hξ : σ ξ₀ = -ξ₀) (u : WOF F E nS nT) {x : WOF F E nS nT}
    (hx : x.map (infPartF F E) = 0) : symplOHF σ JS JT ξ₀ x (realIdF F E • u) = 0 := by
  unfold symplOHF
  rw [GlobalTheory.HeisLineF.symplOF_skew σ JS JT hσ hS hT ξ₀ hξ, symplOF_real_fin hσ ξ₀ u hx, neg_zero, mul_zero]

theorem realIdF_smul_mtF {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : GAF σ J} (hg : g ∈ GlobalTheory.WeilPartsF.GfCF σ J) :
    realIdF F E • mtF σ J g = realIdF F E • (1 : Matrix (Fin n) (Fin n) (AEF F E)) := by
  have h : (mtF σ J g).map (infPartF F E) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hg)
  rw [← sub_eq_zero, ← smul_sub]
  refine Matrix.ext fun i j => ?_
  show realIdF F E * (mtF σ J g - 1) i j = 0
  refine realIdF_mul_of_inf ?_
  rw [Matrix.sub_apply, map_sub, sub_eq_zero]
  refine (congrFun (congrFun h i) j).trans ?_
  rw [← Matrix.map_one (infPartF F E) (infPartF F E).map_zero (infPartF F E).map_one]
  rfl

theorem actOF_real {g : GAF σ JS} {h : GAF σ JT} (hg : g ∈ GlobalTheory.WeilPartsF.GfCF σ JS)
    (hh : h ∈ GlobalTheory.WeilPartsF.GfCF σ JT) (u : WOF F E nS nT) :
    actOF σ JS JT g h (realIdF F E • u) = realIdF F E • u := by
  have h1 := realIdF_smul_mtF hh
  have h2 := realIdF_smul_mtF ((GlobalTheory.WeilPartsF.GfCF σ JS).inv_mem hg)
  unfold actOF
  have hI : realIdF F E * realIdF F E = realIdF F E := by
    rw [realIdF, ← map_mul]
    congr 1
    show ((1 : Ainf F) * 1, (0 : Af F) * 0) = ((1 : Ainf F), (0 : Af F))
    rw [one_mul, mul_zero]
  calc mtF σ JT h * (realIdF F E • u) * mtF σ JS g⁻¹
      = (realIdF F E • mtF σ JT h) * u * (realIdF F E • mtF σ JS g⁻¹) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hI]
    _ = realIdF F E • u := by
        rw [h1, h2, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hI]

end GlobalTheory.FinLatHeis

namespace GlobalTheory.FinLatHeis

open GlobalTheory.FinLatF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {ψ : AddChar (AF F) ℂ}

theorem phaseF_rhoFF (hS : IsHermND σ JS) (w : 𝓞 E) (p : GAF σ JS × GAF σ JT) (x : XFF F E nS nT) :
    phaseF σ JS JT ξ₀ ψ w (rhoFF σ JS JT p x) = phaseF σ JS JT ξ₀ ψ w x := by
  rw [phaseF, phaseF, coe_rhoFF, ← actOF_smul, symplOHF_actOF hS]

theorem phaseF_ne_zero (w : 𝓞 E) (x : XFF F E nS nT) : phaseF σ JS JT ξ₀ ψ w x ≠ 0 := by
  intro h0
  have h := AddChar.map_add_eq_mul ψ (-symplOHF σ JS JT ξ₀ (intAF F w • (x : WOF F E nS nT)) x)
    (symplOHF σ JS JT ξ₀ (intAF F w • (x : WOF F E nS nT)) x)
  rw [neg_add_cancel, AddChar.map_zero_eq_one] at h
  rw [phaseF] at h0
  rw [h0, zero_mul] at h
  exact one_ne_zero h

variable {hc : HeisClosedF σ JS JT ξ₀ ψ} {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {w : 𝓞 E}
  {lam : ℕ →* ℂ} {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ)}

theorem comm (hσ : ∀ x, σ (σ x) = x) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : σ ξ₀ = -ξ₀)
    (hR : IsLatRepF σ JS JT ξ₀ ψ hc Λ w lam Om)
    (L : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ →ₗ[ℂ] GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ)
    (hL : ∀ x v, L (opFF hc w x v) = opFF hc w x (L v))
    (p : GAF σ JS × GAF σ JT) (f : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ) : Om p (L f) = L (Om p f) := by
  have H := isHeis_opFF hσ hS hT hξ hc hR.hw
  have : Om p ∘ₗ L = L ∘ₗ Om p := by
    refine LinearMap.ext_on hR.span ?_
    rintro _ ⟨x, e, he, rfl⟩
    have he' : Fixes (opFF hc w) (latF F E nS nT Λ) (L e) := fun a ha => by rw [← hL, he a ha]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hL, hR.op, hR.op, hL, hR.vac p e he, hR.vac p _ he',
      GlobalTheory.FinWeilO.normOp_comm H lam (hR.sd' p) (hR.fin p) L hL he]
  exact LinearMap.congr_fun this f

theorem heis_fin (hS : IsHermND σ JS) (hR : IsLatRepF σ JS JT ξ₀ ψ hc Λ w lam Om)
    (p : GAF σ JS × GAF σ JT) (x : XFF F E nS nT) (f f' : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ)
    (hf : (f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ ψ x f) :
    (Om p f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ ψ (actOF σ JS JT p.1 p.2 x) (Om p f) := by
  have h1 : opFF hc w x f = phaseF σ JS JT ξ₀ ψ w x • f' := Subtype.ext (by rw [coe_opFF, Submodule.coe_smul, hf])
  have h2 := congrArg Subtype.val (hR.op p x f)
  rw [h1, map_smul, Submodule.coe_smul, coe_opFF, phaseF_rhoFF hS, coe_rhoFF] at h2
  exact smul_right_injective _ (phaseF_ne_zero w x) h2

end GlobalTheory.FinLatHeis


open GlobalTheory.FinLatF GlobalTheory.FinLatHeis in
theorem GlobalTheory.FinLatHeis.isLatRepF_heis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        GlobalTheory.FinLatF.IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ g ∈ GlobalTheory.WeilPartsF.GfCF σ JS, ∀ h ∈ GlobalTheory.WeilPartsF.GfCF σ JT, ∀ (w₀ : WOF F E nS nT)
          (f f' : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ),
          (f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ w₀ f →
          (Om (g, h) f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ (actOF σ JS JT g h w₀) (Om (g, h) f) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ _ hξ hc Λ w lam Om hR g hg h hh w₀ f f' hf
  have hσ : ∀ x, σ (σ x) = x := by
    intro x
    let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
    apply τ.injective
    rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]
  set r := realIdF F E
  let L : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ →ₗ[ℂ] GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ :=
    (heisLF σ JS JT ξ₀ B.ψ (r • w₀)).restrict fun f hf => hc _ f hf
  have hL : ∀ m, (L m : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ (r • w₀) m := fun _ => rfl
  have hLop : ∀ x v, L (opFF hc w x v) = opFF hc w x (L v) := fun x v => Subtype.ext (by
    rw [hL, coe_opFF, coe_opFF, hL, GlobalTheory.WeilPartsF.heisOF_smul, heisOF_heisOF', heisOF_heisOF',
      symplOHF_real_fin hσ ξ₀ w₀ x.fin, symplOHF_fin_real hσ hS hT hξ w₀ x.fin, add_comm])
  let f₁ : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ := ⟨_, hc ((1 - r) • w₀) f f.2⟩
  have hf' : f' = L f₁ := Subtype.ext (by
    rw [hf, hL]
    show heisOF σ JS JT ξ₀ B.ψ w₀ f = heisOF σ JS JT ξ₀ B.ψ (r • w₀) (heisOF σ JS JT ξ₀ B.ψ ((1 - r) • w₀) f)
    rw [heisOF_heisOF', symplOHF_real_fin hσ ξ₀ w₀ (fin_part w₀), AddChar.map_zero_eq_one, one_smul, ← decomp])
  have h1 := heis_fin hS hR (g, h) (XFF.mk _ (fin_part w₀)) f f₁ rfl
  rw [XFF.coe_mk] at h1
  rw [hf', comm hσ hS hT hξ hR L hLop, hL, h1, heisOF_heisOF',
    symplOHF_real_fin hσ ξ₀ w₀ (actOF_mem_finSubF g h (fin_part w₀)), AddChar.map_zero_eq_one, one_smul]
  congr 1
  conv_rhs => rw [decomp w₀, actOF_add, actOF_real hg hh]

end
end

section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

theorem _root_.GlobalTheory.T.exists_invariant_wachModule_basis_of_nonneg_jumps : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ) (n : ℕ), GlobalTheory.AdmLoc.CrysWith ((D.loc l).PD K) ((HW l).W K 1 LL hA.2.2).emb T.ρ U → (∀ i, ∀ u ∈ U i, 0 ≤ u) → Module.finrank ↥(OL LL) ↥T.L.T = n → ∀ γ : ((HW l).W K 1 LL hA.2.2).Gam, ∃ (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N T)) (N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)), IsFrame ((HW l).W K 1 LL hA.2.2) T γ b N := by
  first | exact @GlobalTheory.WachFrame.exists_frame | exact GlobalTheory.WachFrame.exists_frame | (intros; apply GlobalTheory.WachFrame.exists_frame <;> assumption)
end
