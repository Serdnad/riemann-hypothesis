module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1505
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem real_root_quad_le {x : ℝ} {α β : ℂ} (h : (x : ℂ) ^ 2 - α * x - β = 0) : x ≤ ‖α‖ + ‖β‖ + 1 := by
  have h1 : (x : ℂ) ^ 2 = α * x + β := by linear_combination h
  have h2 : ‖(x : ℂ)‖ ^ 2 ≤ ‖α‖ * ‖(x : ℂ)‖ + ‖β‖ := by
    calc ‖(x : ℂ)‖ ^ 2 = ‖(x : ℂ) ^ 2‖ := (norm_pow _ _).symm
    _ = ‖α * x + β‖ := by rw [h1]
    _ ≤ ‖α * x‖ + ‖β‖ := norm_add_le _ _
    _ = ‖α‖ * ‖(x : ℂ)‖ + ‖β‖ := by rw [norm_mul]
  have hx : ‖(x : ℂ)‖ = |x| := by rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hx] at h2
  have ha := norm_nonneg α
  have hb := norm_nonneg β
  by_contra hc
  push_neg at hc
  have ht : ‖α‖ + ‖β‖ + 1 < |x| := lt_of_lt_of_le hc (le_abs_self x)
  nlinarith [mul_nonneg hb (by linarith : (0:ℝ) ≤ |x| - 1),
    mul_pos (by linarith : (0:ℝ) < |x| - (‖α‖ + ‖β‖ + 1)) (by linarith : (0:ℝ) < |x|)]

theorem diag_eig_le_of_cas_min : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : ι → Bool) (α β : ℂ), ∃ R : ℝ, ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (F : ι → ι → Module.End ℂ M), IsGl F → (∀ a b, qop F α β a b = 0) → LocU s F → ∀ ω : ℝ, (∀ (ω' : ℝ) (v : M), v ≠ 0 → cas s F v = (ω' : ℂ) • v → ω < ω' + 1) → ∀ (x : ℝ) (y : ι → M), y ≠ 0 → (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = (x : ℂ) • y a) → (∀ a, cas s F (y a) = (ω : ℂ) • y a) → x ≤ R := by
  intro ι _ _ s α β
  refine ⟨max (‖α‖ + ‖β‖ + 1) ((2 * ‖α‖ + Fintype.card ι + 1) / 4), ?_⟩
  intro M _ _ F hGl hq hLoc ω hω x y hy hfalse htrue hcas
  by_cases hz : ∀ j, s j = false → ∑ b, F j b (y b) = 0
  · have hbc := GlobalTheory.T.quadraticOperator_eigenvector_diagonalBlock_identity ι M s F α β x y hq hfalse htrue hz
    obtain ⟨a, ha⟩ : ∃ a, y a ≠ 0 := by
      by_contra h
      push_neg at h
      exact hy (funext h)
    have h0 : (x : ℂ) ^ 2 - α * x - β = 0 := by
      by_contra hne
      exact ha ((smul_eq_zero.mp (hbc a)).resolve_left hne)
    exact le_max_of_le_left (real_root_quad_le h0)
  · push_neg at hz
    obtain ⟨j, hj, hzj⟩ := hz
    have hd := GlobalTheory.T.blockCasimir_eigenvalue_drops_offBlock ι M s F α β x ω y hGl hq hfalse htrue hcas j hj
    obtain ⟨U, hU, hUU⟩ := hLoc {∑ b, F j b (y b)}
    have hzU : ∑ b, F j b (y b) ∈ U := hU _ (Finset.mem_singleton_self _)
    have him := ((GlobalTheory.T.blockDiagonalFibreCasimir_eigen_nonneg_real_unitary ι M s F U hUU).1 _ _ hzU hzj hd).1
    set c : ℂ := (ω : ℂ) - 4 * x + 2 * α + ((Finset.univ.filter fun a => s a = true).card : ℂ)
      - ((Finset.univ.filter fun a => s a = false).card : ℂ) with hc
    have hcre : c = ((c.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    have hlt := hω c.re _ hzj (by rw [← hcre]; exact hd)
    have hre : c.re = ω - 4 * x + 2 * α.re + ((Finset.univ.filter fun a => s a = true).card : ℝ)
      - ((Finset.univ.filter fun a => s a = false).card : ℝ) := by simp [hc]
    have hr : ((Finset.univ.filter fun a => s a = true).card : ℝ) ≤ Fintype.card ι := by
      have := Finset.card_filter_le (Finset.univ : Finset ι) (fun a => s a = true)
      rw [Finset.card_univ] at this
      exact_mod_cast this
    have hαre : α.re ≤ ‖α‖ := Complex.re_le_norm α
    have hr'0 : (0:ℝ) ≤ ((Finset.univ.filter fun a => s a = false).card : ℝ) := Nat.cast_nonneg _
    refine le_max_of_le_right ?_
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
    linarith

end GlobalTheory.HoweR
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.exists_section_generic_fiber_pullback_local_iso : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral G] [IsLocallyNoetherian G] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ), (∀ x, IsIso (j.stalkMap x)) → ∀ (M : MLine p (τ.comp (algebraMap k K))) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s), j (genericPoint G) = genericPoint X → ∃ (s' : (M.bc hp.w τ).B.Sec) (hs' : genericPoint G ∈ nonzeroLocus s'), nonzeroLocus s' = j ⁻¹ᵁ nonzeroLocus s ∧ (∀ x, (divOfSec (M.bc hp.w τ).φ.isLB s' hs').mult x = (divOfSec M.φ.isLB s hs).mult (j x)) ∧ ∀ y, (M.bc hp.w τ).logSec s' y = M.logSec s (bcPt hp.w τ y) := by
  first | exact @GlobalTheory.Mix.exists_sec_bc | exact GlobalTheory.Mix.exists_sec_bc | (intros; apply GlobalTheory.Mix.exists_sec_bc <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOnBase

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section ClassSum

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem j_thetaMat_base (hB : BaseLinks R F) (j : Fin D.R.m) (t : T0)
    (y : Fin ((A.fam.L j t).dZ (liftLvl F) (liftSub R F j t)) → D.what₂.LL) :
    (R.FW j).j (sg0 D A) (coordMap R F j ((thetaMat R F j t).mulVec y)) =
      R.thG j t (R.jV j t ((A.fam.L j t).toF (liftLvl F) (liftSub R F j t) y)) := by
  have k0 := j_coordMap (R := R) (F := F) j ((thetaMat R F j t).mulVec y)
  have k1 := (R.toCx F).key_lift F.cr false hB.1 hB.2.1 j t y
  have k2 := tC_cpt (R.toCx F) F.cr false j t y
  have k3 : (R.toCx F).θ' j t ((R.toCx F).jL j t (F.cr.toL (R.toCx F).zs false j t y)) =
      Tw.mk (twAt D.what₂.embLL A.v0) (R.thG j t (R.jV j t ((A.fam.L j t).toF (liftLvl F) (liftSub R F j t) y))) := rfl
  exact k0.trans ((k1.trans k2).trans k3)

theorem eq_thetaOp_base {s : ℕ} (hOk : A.fam.Ok s) (hHV : R.models_HV) (hjV : R.models_jV) (hU : R.LUnif) (hB : BaseLinks R F)
    (i : Fin D.R.m) (t : T0) (x : Fin (OntoChain.srcDim F i t) → D.what₂.LL) {u : Fin (R.nW i) → D.what₂.LL}
    (hu : u ∈ R.WL F false i) (ha : (R.FW i).j (sg0 D A) u = R.thG i t (R.jV i t (srcF F i t x))) :
    u = thetaOp R F i t x := by
  rw [← range_coordMap] at hu
  obtain ⟨z, rfl⟩ := hu
  obtain ⟨y, rfl⟩ : ∃ y, (thetaMat R F i t).mulVec y = z := ((R.toCx F).liftMat_bij F.cr false (RealDat.kForm hU false)
    (RealDat.ewNorm false) (RealDat.nP_pos false) hB.1 hB.2.1 i t).2 z
  have hb : _ = R.thG i t (R.jV i t (srcF F i t (((A.fam.L i t).lE (liftLvl F) (liftSub R F i t)).mulVec y))) :=
    (j_thetaMat_base hB i t y).trans (congrArg (fun f => R.thG i t (R.jV i t f)) (toF_eq_srcF hOk i t y))
  have h0 := lPr_eq_zero_of_ker hOk hHV hjV i t (x - ((A.fam.L i t).lE (liftLvl F) (liftSub R F i t)).mulVec y)
    ((lift_sub i t _ _).trans (sub_eq_zero.2 (ha.symm.trans hb)))
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, BlockDat.lf_lPr_lE (blockHyp (F := F) hOk i t), Matrix.one_mulVec,
    sub_eq_zero] at h0
  rw [← h0, Matrix.mulVec_mulVec]
  rfl

theorem goodOp_classSum_base {s : ℕ} (hOk : A.fam.Ok s) {ph : Fin D.R.m → ℂ} (hG : PhasedLift R ph) (hHV : R.models_HV)
    (hjV : R.models_jV) (hHW : R.models_HW) (hU : R.LUnif) (hB : BaseLinks R F) (i : Fin D.R.m) (t : T0)
    {θ : (Fin (OnTies.srcDim A i t F.P0 F.ψ0⁻¹) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)}
    (hθ : OnTies.IsClassSum R i t F.P0 F.ψ0⁻¹ (ph i) θ) (x : Fin (OnTies.srcDim A i t F.P0 F.ψ0⁻¹) → D.what₂.LL)
    (hx : goodOp R i (θ x) ∈ R.WL F false i) : goodOp R i (θ x) = thetaOp R F i t x := by
  refine eq_thetaOp_base hOk hHV hjV hU hB i t x hx ((hHW i _).1 ?_)
  refine (adForm_goodOp hU i _).trans ?_
  refine (congrArg (Mult.postOn _ (R.eWf i (sg0 D A))) (hθ x)).trans ?_
  exact (LinearMap.map_smul _ _ _).trans (hG i t _).symm

end ClassSum

section Tied

variable {J : CoreJ D} [inst : Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

local instance runAlg (r : RunData J) : Algebra r.full.J.Q.c.F D.what₂.LL := inst

variable {fw : FWTie J R κ v₀} {hc : LawsCore J.toCore} {run : HeightOneSpectrum (𝓞 D.what₂.LL) → RunData J}
  {h : ∀ v, LawsP (run v).full.toTop} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D}
  {p : HeightOneSpectrum (𝓞 D.what₂.LL) → ℕ}
  {wL wF : HeightOneSpectrum (𝓞 D.what₂.LL) → ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {nT : ℕ}
  {ℓ : ∀ i : Fin D.R.m, G → (LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l ≃ₗ[𝓞 D.host.E] LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l)}
  {ph : Fin D.R.m → ℂ} {c : OnConst} {s : ℕ}

theorem exists_tieCoord_base {P : Type} [Group P] [Finite P] {inc : P →* G} {O : OnObj ((R.toCx F).data F.cr false) P c}
    (ht : OnObjLevelCompatibility F fw hc run h hinj EX p wL wF nT ℓ ph inc O) (hinc : F.P0 ≤ inc.range)
    (hOk : A.fam.Ok s) (h1 : R.grp_levels F) (h2 : R.grp_chiW) (hHV : R.models_HV) (hjV : R.models_jV) (hHW : R.models_HW)
    (hμ : R.tup_mu_conj) (hG : PhasedLift R ph) (hU : R.LUnif) (hB : BaseLinks R F)
    (hrat : TwistedRational R F ph) (hI : LeafIdentity O) (hT : LeafTW2 O) : ∃ w, TieCoord (withCoord O w) := by
  obtain ⟨z, act, y, ht⟩ := ht
  obtain ⟨v₁, -⟩ := exists_place3 D.what₂.LL
  let w : ∀ j, (Fin (O.nZ j) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (R.nW j) → D.what₂.LL) := fun j =>
    LinearEquiv.ofBijective (toForms (T := (run v₁).full) (R := R) (h v₁) fw j (z j))
      (toForms_bijective (T := (run v₁).full) (R := R) (h v₁) fw j (z j))
  have he : ∀ j x, w j (O.e j x) = goodOp R j (w j x) := fun j x => (ht v₁ j).1.e_eOp x
  have hZ : ∀ j x, x ∈ O.Zg j ↔ w j x ∈ R.WL F false j := fun j =>
    mem_Zg_iff h1 h2 hinc j ((ht v₁ j).1.rho_eq_of_actionPin (ht v₁ j).2) (ht v₁ j).1.U_eq (ht v₁ j).1.ψ_eq (he j)
      (ht v₁ j).1.V₀_eq
  have hM : ∀ j x, x ∈ O.Ms j ↔ w j x ∈ supLat (R.FW j) := fun j x => mem_Ms_iff (ht v₁ j).1 x
  have key : ∀ v j, ClassSumRational R j (R.mu v) F.P0 F.ψ0⁻¹ (ph j) →
      (O.θ' v j ∘ₗ O.eX v j = O.e j ∘ₗ O.θ' v j ∧
        ∀ x ∈ LinearMap.range (O.eX v j), x - O.pr v j x ∈ LinearMap.ker (O.θ' v j)) →
      IsLatIn (O.Zg j) (O.Im v j) → (withCoord O w).TjId j v (R.mu v) := fun v j hra hI hT => by
    refine coord_tuple j v (y v j) (fun x => by rw [(ht v j).1.Mt_eq]; rfl) (fun x hx => ?_) hI
    have hθ : OnTies.IsClassSum R j (R.mu v) F.P0 F.ψ0⁻¹ (ph j)
        ((w j).toLinearMap ∘ₗ O.θ' v j ∘ₗ (y v j).symm.toLinearMap) := (ht v j).1.θ'_eq hra
    have e : ((w j).toLinearMap ∘ₗ O.θ' v j ∘ₗ (y v j).symm.toLinearMap) (y v j x) = w j (O.θ' v j x) :=
      congrArg (fun u => w j (O.θ' v j u)) ((y v j).symm_apply_apply x)
    have hm : w j (O.e j (O.θ' v j x)) ∈ R.WL F false j :=
      (hZ j _).1 (hT.2.le (Submodule.subset_span ⟨_, ⟨x, hx, rfl⟩, rfl⟩))
    have := goodOp_classSum_base hOk hG hHV hjV hHW hU hB j (R.mu v) hθ (y v j x) (by rw [e, ← he]; exact hm)
    rw [e, ← he] at this
    exact this
  refine ⟨w, fun j => coord_lattice j (hZ j) (hM j), fun v hv j =>
    ⟨key v j (hrat v hv j) ((hI v hv).1 j) ((hT v hv).1 j).2.1, ?_⟩⟩
  have := key (_root_.Formalism.DivisionValues.conjPl v) j (by rw [hμ v]; exact hrat v hv j) ((hI v hv).2 j) ((hT v hv).2 j).2.1
  rwa [hμ v] at this

end Tied

section Free

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type}
  [Group P] [Finite P] {c : OnConst}

end Free

end GlobalTheory.BigOnBase

end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

theorem grp_factor_eq_of_conj : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (y y₀ : grp G β) (c : G.Cˣ),
    (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C) →
    (y : G.Cˣ × ℚˣ).2 = (y₀ : G.Cˣ × ℚˣ).2 := by
  intro p _ G β y y₀ c hyc
  haveI : Module.Finite ℚ G.C := Module.Finite.trans G.F G.C
  haveI : Nontrivial G.C := inferInstance
  set d : G.C → ℚ := fun a => LinearMap.det (LinearMap.mulLeft ℚ a) with hd
  have dmul : ∀ a b, d (a * b) = d a * d b := by
    intro a b; simp only [hd, LinearMap.mulLeft_mul, LinearMap.det_comp]
  have done : d 1 = 1 := by simp [hd, LinearMap.mulLeft_one]
  have dsc : ∀ s : ℚ, d (algebraMap ℚ G.C s) = s ^ Module.finrank ℚ G.C := by
    intro s
    have : LinearMap.mulLeft ℚ (algebraMap ℚ G.C s) = s • LinearMap.id := by
      ext x; simp [Algebra.smul_def]
    simp only [hd, this, LinearMap.det_smul, LinearMap.det_id, mul_one]
  have dunit : ∀ u : G.Cˣ, d (u : G.C) * d ((u⁻¹ : G.Cˣ) : G.C) = 1 := by
    intro u; rw [← dmul, Units.mul_inv, done]
  have shmul : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a := by
    intro a b; simp only [sh, map_mul, MulOpposite.unop_mul]
  have shone : sh G 1 = 1 := by simp [sh]
  have dsh_conj : d (sh G (c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C))) =
      d (sh G (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) := by
    have e : d (sh G ((c⁻¹ : G.Cˣ) : G.C)) * d (sh G (c : G.C)) = 1 := by
      rw [← dmul, ← shmul, Units.mul_inv, shone, done]
    rw [shmul, shmul, dmul, dmul]
    calc d (sh G ((c⁻¹ : G.Cˣ) : G.C)) * (d (sh G (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) * d (sh G (c : G.C)))
        = d (sh G (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) *
          (d (sh G ((c⁻¹ : G.Cˣ) : G.C)) * d (sh G (c : G.C))) := by ring
      _ = _ := by rw [e, mul_one]
  have d_conj : d (c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C)) =
      d (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) := by
    rw [dmul, dmul]
    calc d (c : G.C) * d (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * d ((c⁻¹ : G.Cˣ) : G.C)
        = d (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * (d (c : G.C) * d ((c⁻¹ : G.Cˣ) : G.C)) := by ring
      _ = _ := by rw [dunit, mul_one]
  obtain ⟨hy, hs⟩ := y.2
  obtain ⟨hy₀, hs₀⟩ := y₀.2
  have ey := congrArg d hy
  have ey₀ := congrArg d hy₀
  rw [dmul, dmul, dmul, dsc] at ey ey₀
  rw [hyc, d_conj, dsh_conj, ey₀] at ey
  have hβ : d (β : G.C) ≠ 0 := by
    intro h; have := dunit β; rw [h, zero_mul] at this; exact zero_ne_one this
  have hN : Module.finrank ℚ G.C ≠ 0 := Module.finrank_pos.ne'
  have hpow : ((y : G.Cˣ × ℚˣ).2 : ℚ) ^ Module.finrank ℚ G.C = ((y₀ : G.Cˣ × ℚˣ).2 : ℚ) ^ Module.finrank ℚ G.C :=
    (mul_right_cancel₀ hβ ey).symm
  exact Units.ext ((pow_left_inj₀ hs.le hs₀.le hN).1 hpow)

end GlobalTheory
end

section

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.TorCls

variable {p : ℕ} [Fact p.Prime]

def InT (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (β y : G.C) (z : (R ⊗[ℚ] G.C)ˣ × Rˣ) : Prop :=
  (z.1 : R ⊗[ℚ] G.C) * inC G R β * (starT G.star R (z.1 : R ⊗[ℚ] G.C)).unop =
      algebraMap R (R ⊗[ℚ] G.C) (z.2 : R) * inC G R β ∧
    Commute (z.1 : R ⊗[ℚ] G.C) (inC G R y)

def psiAway (G : HTGroup p) (x : (AfP p ⊗[ℚ] G.C)ˣ) :
    (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ →* (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ :=
  (MulAut.conj x).toMonoidHom.prodMap (MonoidHom.id _)

def psiP (G : HTGroup p) : (ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ →* Gr G 1 :=
  (inclG G 1).comp ((MonoidHom.snd _ _).prod (Pi.monoidHom fun w =>
    (Units.map ((G.locW w).toRingHom.toMonoidHom)).comp (MonoidHom.fst _ _)))

@[simp] theorem psiAway_apply (G : HTGroup p) (x : (AfP p ⊗[ℚ] G.C)ˣ) (z : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) :
    psiAway G x z = (x * z.1 * x⁻¹, z.2) := rfl

def dg (D : Type) [Ring D] [Algebra ℚ D] (p : ℕ) [Fact p.Prime] :
    Dˣ × ℚˣ →* ((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ) :=
  ((Units.map (Algebra.TensorProduct.includeRight : D →ₐ[ℚ] AfP p ⊗[ℚ] D).toMonoidHom).prodMap
      (Units.map (algebraMap ℚ (AfP p)).toMonoidHom)).prod
    ((Units.map (Algebra.TensorProduct.includeRight : D →ₐ[ℚ] ℚ_[p] ⊗[ℚ] D).toMonoidHom).prodMap
      (Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom))

theorem toAfF_eq_psiAway (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (y : grp G β) :
    ((toAfF G β x t hx y : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) =
      psiAway G x ((dg G.C p (y : G.Cˣ × ℚˣ)).1) := rfl

theorem formGroupToPadicPointsDegreeOne_eq_unitaryPoints (G : HTGroup p) (β : G.Cˣ) (y : grp G β) :
    toP1 G β y = psiP G ((dg G.C p (y : G.Cˣ × ℚˣ)).2) := by
  simp only [toP1, psiP, MonoidHom.comp_apply]
  congr 1
  refine Prod.ext rfl (funext fun w => Units.ext ?_)
  change G.rho w _ = G.locW w ((1 : ℚ_[p]) ⊗ₜ _)
  change _ = (Algebra.ofId ℚ_[p] (Matrix (Fin G.n) (Fin G.n) (G.Fw w)) (1 : ℚ_[p])) * (G.rho w).toRatAlgHom _
  rw [map_one, one_mul]
  rfl

theorem form_mul_inv {D : Type} [Ring D] [Algebra ℚ D] (σ : D →+* Dᵐᵒᵖ) (β : D) (a e : Dˣ) (α η : ℚˣ)
    (ha : (a : D) * β * (σ a).unop = algebraMap ℚ D α * β) (he : (e : D) * β * (σ e).unop = algebraMap ℚ D η * β) :
    ((a * e⁻¹ : Dˣ) : D) * β * (σ ((a * e⁻¹ : Dˣ) : D)).unop = algebraMap ℚ D ((α * η⁻¹ : ℚˣ) : ℚ) * β := by
  have hs : (σ (e : D)).unop * (σ ((e⁻¹ : Dˣ) : D)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have hs' : (σ ((e⁻¹ : Dˣ) : D)).unop * (σ (e : D)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.mul_inv, map_one, MulOpposite.unop_one]
  have hη : algebraMap ℚ D ((η⁻¹ : ℚˣ) : ℚ) * algebraMap ℚ D (η : ℚ) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have key : ((e⁻¹ : Dˣ) : D) * β * (σ ((e⁻¹ : Dˣ) : D)).unop = algebraMap ℚ D ((η⁻¹ : ℚˣ) : ℚ) * β := by
    calc ((e⁻¹ : Dˣ) : D) * β * (σ ((e⁻¹ : Dˣ) : D)).unop
        = algebraMap ℚ D ((η⁻¹ : ℚˣ) : ℚ) * (((e⁻¹ : Dˣ) : D) * (algebraMap ℚ D (η : ℚ) * β) *
            (σ ((e⁻¹ : Dˣ) : D)).unop) := by
          simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul]
          rw [show (η : ℚ) * ((η⁻¹ : ℚˣ) : ℚ) = 1 by simp, one_smul]
      _ = algebraMap ℚ D ((η⁻¹ : ℚˣ) : ℚ) * ((((e⁻¹ : Dˣ) : D) * e) * β *
            ((σ (e : D)).unop * (σ ((e⁻¹ : Dˣ) : D)).unop)) := by
          rw [← he]; simp only [mul_assoc]
      _ = _ := by rw [Units.inv_mul, hs, one_mul, mul_one]
  have hsm : (σ ((a * e⁻¹ : Dˣ) : D)).unop = (σ ((e⁻¹ : Dˣ) : D)).unop * (σ (a : D)).unop := by
    rw [Units.val_mul, map_mul, MulOpposite.unop_mul]
  rw [hsm, Units.val_mul, Units.val_mul, map_mul]
  calc (a : D) * ((e⁻¹ : Dˣ) : D) * β * ((σ ((e⁻¹ : Dˣ) : D)).unop * (σ (a : D)).unop)
      = (a : D) * (((e⁻¹ : Dˣ) : D) * β * (σ ((e⁻¹ : Dˣ) : D)).unop) * (σ (a : D)).unop := by
        simp only [mul_assoc]
    _ = algebraMap ℚ D ((η⁻¹ : ℚˣ) : ℚ) * ((a : D) * β * (σ (a : D)).unop) := by
        rw [key, ← mul_assoc (a : D), ← Algebra.commutes ((η⁻¹ : ℚˣ) : ℚ) (a : D)]; simp only [mul_assoc]
    _ = _ := by
        rw [ha, ← mul_assoc, ← map_mul, mul_comm ((η⁻¹ : ℚˣ) : ℚ), map_mul]

theorem conj_back {S A : Type*} [Ring S] [CommRing A] [Algebra A S] (σ : S →+* Sᵐᵒᵖ) (b : S) (x g : Sˣ)
    (t c : A) (hx : (x : S) * b * (σ x).unop = algebraMap A S t)
    (hg : (g : S) * (σ g).unop = algebraMap A S c) :
    ((x⁻¹ * g * x : Sˣ) : S) * b * (σ ((x⁻¹ * g * x : Sˣ) : S)).unop = algebraMap A S c * b := by
  have h1 : (σ (x : S)).unop * (σ ((x⁻¹ : Sˣ) : S)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have hb : b = algebraMap A S t * (((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop) := by
    calc b = (((x⁻¹ : Sˣ) : S) * x) * b * ((σ (x : S)).unop * (σ ((x⁻¹ : Sˣ) : S)).unop) := by
          rw [Units.inv_mul, h1, one_mul, mul_one]
      _ = ((x⁻¹ : Sˣ) : S) * ((x : S) * b * (σ (x : S)).unop) * (σ ((x⁻¹ : Sˣ) : S)).unop := by
          simp only [mul_assoc]
      _ = _ := by rw [hx, ← Algebra.commutes, mul_assoc]
  have hσ : (σ ((x⁻¹ * g * x : Sˣ) : S)).unop =
      (σ (x : S)).unop * (σ (g : S)).unop * (σ ((x⁻¹ : Sˣ) : S)).unop := by
    simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
  rw [hσ]
  calc ((x⁻¹ * g * x : Sˣ) : S) * b * ((σ (x : S)).unop * (σ (g : S)).unop * (σ ((x⁻¹ : Sˣ) : S)).unop)
      = ((x⁻¹ : Sˣ) : S) * ((g : S) * ((x : S) * b * (σ (x : S)).unop) * (σ (g : S)).unop) *
          (σ ((x⁻¹ : Sˣ) : S)).unop := by
        simp only [Units.val_mul, mul_assoc]
    _ = ((x⁻¹ : Sˣ) : S) * (algebraMap A S t * ((g : S) * (σ (g : S)).unop)) *
          (σ ((x⁻¹ : Sˣ) : S)).unop := by
        rw [hx, ← Algebra.commutes t (g : S)]; simp only [mul_assoc]
    _ = algebraMap A S (c * t) * (((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop) := by
        rw [hg, ← map_mul, ← Algebra.commutes, mul_assoc, mul_comm t c]
    _ = algebraMap A S c * b := by rw [hb, map_mul, mul_assoc]

theorem inT_psiAway_inv_of_commute : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (y₀ : grp G β) (c : G.GAf), c * toAfF G β x t hx y₀ = toAfF G β x t hx y₀ * c →
    InT G (AfP p) β (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) (psiAway G x⁻¹ (c : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ)) := by
  intro p _ G β x t hx y₀ c hc
  have hxx : ((x⁻¹)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) = x := inv_inv x
  refine ⟨?_, ?_⟩
  · have hg : (((c : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
        (starT G.star (AfP p) (((c : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) :
          AfP p ⊗[ℚ] G.C)).unop =
        algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) ((c : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : AfP p) := c.2
    have h := conj_back (starT G.star (AfP p)) (inC G (AfP p) β) x _ (t : AfP p) _ hx hg
    simp only [psiAway_apply, hxx]
    exact h
  · have hU := congrArg (fun g : G.GAf => ((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)) hc
    simp only [Subgroup.coe_mul, Prod.fst_mul] at hU
    rw [toAfF_eq_psiAway, psiAway_apply] at hU
    simp only [psiAway_apply, hxx]
    set c1 := (c : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1
    set Y := (dg G.C p (y₀ : G.Cˣ × ℚˣ)).1.1
    have hUU : (x⁻¹ * c1 * x) * Y = Y * (x⁻¹ * c1 * x) := by
      calc (x⁻¹ * c1 * x) * Y = x⁻¹ * (c1 * (x * Y * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * Y * x⁻¹) * c1) * x := by rw [hU]
        _ = Y * (x⁻¹ * c1 * x) := by group
    exact congrArg Units.val hUU

end GlobalTheory.TorCls
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx.Form

theorem rel_equivalence {p : ℕ} [Fact p.Prime] (G : HTGroup p) : Equivalence (Form.Rel (G := G)) := by
  have sh_mul : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a := by
    intro a b; simp only [sh, map_mul, MulOpposite.unop_mul]
  have sh_one : sh G (1 : G.C) = 1 := by simp only [sh, map_one, MulOpposite.unop_one]
  refine ⟨fun P => ?_, fun {P Q} h => ?_, fun {P Q R} h h' => ?_⟩
  · exact ⟨1, 1, one_pos, by simp [sh_one]⟩
  · obtain ⟨y, s, hs, hβ⟩ := h
    refine ⟨y⁻¹, s⁻¹, inv_pos.mpr hs, ?_⟩
    have e : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
      rw [← sh_mul, Units.inv_mul, sh_one]
    rw [hβ]
    simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, e, mul_one,
      inv_mul_cancel₀ hs.ne', mul_inv_cancel₀ hs.ne', one_smul, Units.inv_mul_cancel_left]
  · obtain ⟨y, s, hs, hβ⟩ := h
    obtain ⟨y', s', hs', hβ'⟩ := h'
    refine ⟨y' * y, s' * s, mul_pos hs' hs, ?_⟩
    rw [hβ', hβ, Units.val_mul, sh_mul]
    simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, mul_comm s]

theorem mk_eq_iff_rel : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Form G),
    Quot.mk Form.Rel P = Quot.mk Form.Rel Q ↔ Form.Rel P Q := by
  intro p _ G P Q
  rw [← (rel_equivalence G).eqvGen_iff]
  exact ⟨Quot.eqvGen_exact, Quot.eqvGen_sound⟩

end GlobalTheory.LKCx.Form
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleCohomology_field_eq_galoisCohomology : GlobalTheory.EtC.B7 := by
  first | (exact @GlobalTheory.EtC.FieldTw.field_tw_coh_eq_galois) | (exact GlobalTheory.EtC.FieldTw.field_tw_coh_eq_galois) | (intros; apply GlobalTheory.EtC.FieldTw.field_tw_coh_eq_galois  <;> assumption)
end
