module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle616
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.AuxStatement14
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle020
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2276
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle887
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle980
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle889
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle892
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle719
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2374
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
open scoped Matrix TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClassSumIdentity

theorem sub_orthProj_perp_mem {K : Type} [Field K] [NumberField K] [StarRing K] {v0 : InfinitePlace K} (h0 : IsConjAt v0) {n : ℕ}
    {H : Matrix (Fin n) (Fin n) K} (hH : (H.map v0.embedding).PosDef) (N : Submodule K (Fin n → K)) (x : Fin n → K) :
    x - orthProj H (perpOf H N) x ∈ N := by
  have hd : ∀ Z : Submodule K (Fin n → K), Hᴴ = H ∧ IsUnit ((subE Z)ᴴ * H * subE Z).det := fun Z =>
    have k := orthogonal_projection_exists K v0 h0 _ _ H hH (subE Z) (subspace_image_spec K n Z).1
    ⟨k.1, k.2.2.1⟩
  have h1 : ∀ u y : Fin n → K, hform H u y = star u ⬝ᵥ H.mulVec y := fun u y => by
    simp [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, starRingEnd_apply, mul_assoc,
      mul_comm, mul_left_comm]
  have hs : ∀ u y : Fin n → K, hform H u y = 0 → hform H y u = 0 := fun u y e => by
    rw [h1] at e ⊢
    have := congrArg star e
    rwa [star_zero, ← Matrix.star_dotProduct_star, star_star, Matrix.star_mulVec, (hd N).1, ← Matrix.dotProduct_mulVec] at this
  set y := x - orthProj H (perpOf H N) x
  have hy : y ∈ perpOf H (perpOf H N) := sub_orthProj_mem_perpOf H _ (hd _).2 x
  have hq : orthProj H N y ∈ N := orthProj_mem H N y
  have hw : y - orthProj H N y ∈ perpOf H N := sub_orthProj_mem_perpOf H _ (hd _).2 y
  have hw' : y - orthProj H N y ∈ perpOf H (perpOf H N) :=
    Submodule.sub_mem _ hy fun z hz => hs _ _ (hz _ hq)
  obtain ⟨a, ha⟩ := (subspace_image_spec K n (perpOf H N)).2.ge hw
  have h2 : ((subE (perpOf H N))ᴴ * H * subE (perpOf H N)).mulVec a = 0 := by
    funext i
    have := hw' _ ((subspace_image_spec K n (perpOf H N)).2.le ⟨Pi.single i 1, rfl⟩)
    rw [← ha, h1, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
    simpa [← Pi.single_star] using this
  have h3 : a = 0 := by
    rw [← Matrix.one_mulVec a, ← Matrix.nonsing_inv_mul _ (hd (perpOf H N)).2, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_zero]
  rw [h3, map_zero] at ha
  exact sub_eq_zero.1 ha.symm ▸ hq

theorem lvlE_lvlOp {K : Type} [Field K] [NumberField K] [StarRing K] {v0 : InfinitePlace K} (h0 : IsConjAt v0) (S : CSD K)
    (hH : (S.H.map v0.embedding).PosDef) {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms) (hr : S.ActGood r)
    (U : Subgroup G) (ψ : U →* Kˣ) (a : MonoidAlgebra K G) (ha : ∀ b, b * a = a * b) (x : Fin (S.lvlDim r U ψ) → K) :
    S.basis.equivFun.symm ((S.lvlE r U ψ).mulVec ((S.lvlOp r U ψ a).mulVec x)) =
      ∑ g, a.coeff g • r g (S.basis.equivFun.symm ((S.lvlE r U ψ).mulVec x)) := by

  rw [Matrix.mulVec_mulVec, (level_operator_spec K v0 h0 S hH G r hr U ψ a (ha _).symm).1, ← Matrix.mulVec_mulVec, CSD.gaMat,
  Matrix.sum_mulVec, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Matrix.smul_mulVec, map_smul]
  exact congrArg _ (Subtype.ext (action_matrix_spec K S G r g _))

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}


open GlobalTheory.TraceIncl in
theorem classSum_eOp {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m} {t : T0}
    {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : ℂ} (h : HidaSetting R i t) {θ} (hθ : OnTies.IsClassSum R i t U ψ ph θ)
    (c : G → D.what₂.LL) {x y : Fin (OnTies.srcDim A i t U ψ) → D.what₂.LL}
    (e : srcForm A i t U ψ y = ∑ g, c g • A.leftGroupActionLift i t g (srcForm A i t U ψ x)) : θ y = (R.FW i).eOp c (θ x) := by
  rcases subsingleton_or_nontrivial (Fin (R.nW i) → D.what₂.LL) with hs | hs
  · exact Subsingleton.elim _ _
  refine h.eq_of_adForm fun v => ?_
  have e0 : adForm R i ((R.FW i).eOp c (θ x)) = ∑ g, adForm R i ((c g * (((R.FW i).chi g)⁻¹ : D.what₂.LLˣ)) • (R.FW i).ρ g (θ x)) := by
    unfold adForm

    rw [Arith.FormsL.eOp_apply, map_sum, map_sum]
  have e4 : ∀ g, adForm R i ((c g * (((R.FW i).chi g)⁻¹ : D.what₂.LLˣ)) • (R.FW i).ρ g (θ x)) (fun ρ => v ρ) =
      ph • (clSum (presV R i t) (kern R i t) (c g • A.leftGroupActionLift i t g (srcForm A i t U ψ x))) v := fun g => by
    have e1 : adForm R i ((R.FW i).ρ g (θ x)) (fun ρ => v ρ) = sg0 D A ((R.FW i).chi g : D.what₂.LLˣ) •
        Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (adForm R i (θ x) fun ρ => v ρ) :=
      DFunLike.congr_fun ((h.unif i _).2.2 g (θ x)) _
    have e2 : clSum (presV R i t) (kern R i t) (A.leftGroupActionLift i t g (srcForm A i t U ψ x)) v =
        Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)
          (clSum (presV R i t) (kern R i t) (srcForm A i t U ψ x) v) :=
      congrFun (h.clSum_equiv g (srcForm A i t U ψ x)) v
    have e3 : sg0 D A ((R.FW i).chi g : D.what₂.LLˣ) = D.what₂.embLL ((R.FW i).chi g : D.what₂.LLˣ) :=
      congrArg (fun s : D.what₂.LL →+* ℂ => s _) (sign_at_base_place_eq_embedding R)
    have e5 : clSum (presV R i t) (kern R i t) (c g • A.leftGroupActionLift i t g (srcForm A i t U ψ x)) v =
        D.what₂.embLL (c g) • clSum (presV R i t) (kern R i t) (A.leftGroupActionLift i t g (srcForm A i t U ψ x)) v :=
      congrFun (LinearMap.map_smulₛₗ _ _ _) v
    have e6 : D.what₂.embLL (c g * (((R.FW i).chi g)⁻¹ : D.what₂.LLˣ)) * D.what₂.embLL ((R.FW i).chi g : D.what₂.LLˣ) =
        D.what₂.embLL (c g) := by rw [← map_mul, mul_assoc, Units.inv_mul, mul_one]
    rw [e5, e2, adForm_smul, MultilinearMap.smul_apply, e1, e3, h.adForm_theta hθ, smul_smul, e6, LinearMap.map_smul, smul_comm]
  have e7 : clSum (presV R i t) (kern R i t) (srcForm A i t U ψ y) v =
      ∑ g, clSum (presV R i t) (kern R i t) (c g • A.leftGroupActionLift i t g (srcForm A i t U ψ x)) v :=
    (congrArg (fun f => clSum (presV R i t) (kern R i t) f v) e).trans
      ((congrFun (map_sum (clSum (presV R i t) (kern R i t)) _ _) v).trans (Finset.sum_apply _ _ _))
  refine (h.adForm_theta hθ y v).trans (((congrArg (fun F => ph • F) e7).trans Finset.smul_sum).trans (Eq.symm ?_))
  exact (DFunLike.congr_fun e0 _).trans ((MultilinearMap.sum_apply _ _ _).trans (Finset.sum_congr rfl fun g _ => e4 g))

section Comparison₂

attribute [local instance 2000] Submodule.module

variable {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {h : LawsP T.toTop} {fw : FWTie T.J R κ v₀} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ}
  {ι : Fin D.R.m} {wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)} {nT : ℕ}
  {O : OnObj S P oc} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {i : Bs.J}
  {z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
    D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {inc : P →* G}
  {ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)}
  {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : ℂ}
  {y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (OnTies.srcDim A ι (R.mu v) U ψ) → D.what₂.LL)}

theorem identity_of_tie (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y)
    (hS : GlobalTheory.TraceIncl.HidaSetting R ι (R.mu v)) {s : ℕ} (hOk : A.fam.Ok s) (hr : ClassSumRational R ι (R.mu v) U ψ ph) :
    O.θ' v i ∘ₗ O.eX v i = O.e i ∘ₗ O.θ' v i ∧
      ∀ x ∈ LinearMap.range (O.eX v i), x - O.pr v i x ∈ LinearMap.ker (O.θ' v i) := by
  have hθy : ∀ x, (toForms h fw ι z ∘ₗ O.θ' v i ∘ₗ y.symm.toLinearMap) (y x) = toForms h fw ι z (O.θ' v i x) := fun x =>
    congrArg (fun a => toForms h fw ι z (O.θ' v i a)) (y.symm_apply_apply x)
  refine ⟨LinearMap.ext fun x => (toForms_bijective h fw ι z).1 ?_, fun x _ => ?_⟩
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, t.e_eOp, ← hθy, ← hθy]
    refine classSum_eOp hS (t.θ'_eq hr) _ ?_
    refine (congrArg (srcForm A ι (R.mu v) U ψ) (LinearMap.congr_fun t.eX_eq x)).trans ?_
    exact lvlE_lvlOp hOk.conj (A.MtCSD ι (R.mu v)) ((hOk.lifts ι (R.mu v)).hpos _) (A.leftGroupActionLift ι (R.mu v)) hS.act U ψ _
      (idempotent_central _ _ A.X hOk.irr).2 (y x)
  · have hpos : (((A.MtCSD ι (R.mu v)).lvlH (A.leftGroupActionLift ι (R.mu v)) U ψ).map A.v0.embedding).PosDef :=
      BlockDat.lf_lvlH_pos (B := A.fam.L ι (R.mu v)) (ℓ := ⟨A.X, U, ψ⟩) ⟨hOk.conj, hOk.irr, hOk.lifts ι (R.mu v)⟩ A.v0
    obtain ⟨a, ha, e⟩ := sub_orthProj_perp_mem hOk.conj hpos ((LinearMap.ker (O.θ' v i)).map y.toLinearMap) (y x)
    have e' : y a = y (x - O.pr v i x) :=
      e.trans ((congrArg (fun b => y x - b) (LinearMap.congr_fun t.pr_eq x).symm).trans (y.map_sub _ _).symm)
    exact y.injective e' ▸ ha

end Comparison₂


attribute [local instance] GlobalTheory.BigOn.runAlg' in
theorem leafIdentity_of_isRec : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → ∀ s : ℕ, A.fam.Ok s → R.Char F → R.LUnif → TwistedRational R F (fun _ => 1) → LeafIdentity O := by
  intro D G _ _ Pl0 T0 A J inst R F κ v₀ fw L Pm Tp hK EX r c O hO s hOk hC hU hrat
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hO.tied
  have key : ∀ v j, ClassSumRational R j (R.mu v) F.P0 F.ψ0⁻¹ 1 →
      O.θ' v j ∘ₗ O.eX v j = O.e j ∘ₗ O.θ' v j ∧
        ∀ x ∈ LinearMap.range (O.eX v j), x - O.pr v j x ∈ LinearMap.ker (O.θ' v j) := fun v j hr =>
    identity_of_tie (T := (r.used v).full) (inst := inst) (R := R) (ht v j).1
      ⟨hC.lev, hC.grp.red_L, hC.fam.tie, hC.models, hC.thP, hU, ⟨_, (fw.hv₀ j _).1⟩, (hOk.lifts _ _).act,
        GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar R hC.lev hC.models.inf hC.thP.ωP hC.thP.vP j (R.mu v)⟩ hOk hr
  exact fun w hw => ⟨fun j => key w j (hrat w hw j), fun j => key _ j (by rw [hC.tup.mu_conj w]; exact hrat w hw j)⟩

end GlobalTheory.ClassSumIdentity
end
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LieInjField


open GlobalTheory.CechDR in
theorem cmpForm_surjective (hC : GlobalTheory.Published.CrystallineSmoothLift) (hH : GlobalTheory.Published.AbelianHodgeDeRham)
    (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hab : IsAbelianScheme A)
    (hdim : SmoothOfRelativeDimension g A.hom) : Function.Surjective (cmpForm (A.hom ≫ 𝟙 (Sp R))) := by
  have hsm : Smooth (A.hom ≫ 𝟙 (Sp R)) := by haveI := hab.smooth; infer_instance
  have hsep : IsSeparated (A.hom ≫ 𝟙 (Sp R)) := by haveI := hab.proper; infer_instance
  have hqc : QuasiCompact (A.hom ≫ 𝟙 (Sp R)) := by haveI := hab.proper; infer_instance
  have hcmp := (cechDeRham_comparison_bijective_cup_smooth hC R A.left _ hsm hsep hqc).1
  have hcl : Function.Injective (clForm (A.hom ≫ 𝟙 (Sp R))) := (hH R A g hab hdim).2.2.2.2.1.2.1
  intro ω
  obtain ⟨c, hc⟩ := hcmp.2 (clForm _ ω)
  have hF : clForm _ ω ∈ CechHodgeFiltration (A.hom ≫ 𝟙 (Sp R)) := by rw [cechHodgeFiltration_eq_range]; exact ⟨ω, rfl⟩
  have h1 : c ∈ F1 (A.hom ≫ 𝟙 (Sp R)) := by
    change toH1O _ c = 0
    apply GlobalTheory.T.structure_sheaf_comparison_injective R A.left _
    rw [← structureSheaf_comparison_comm, map_zero, hc]
    exact hF
  rw [hodgeFiltration_eq_range] at h1
  obtain ⟨f, rfl⟩ := h1
  rw [comparison_formClass] at hc
  exact ⟨f, hcl hc⟩

theorem cmpForm_eq_zero_of_tangent (hC : GlobalTheory.Published.CrystallineSmoothLift) (hH : GlobalTheory.Published.AbelianHodgeDeRham)
    (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B] (g : ℕ) (hab : IsAbelianScheme B)
    (hdim : SmoothOfRelativeDimension g B.hom) (f : Form (B.hom ≫ 𝟙 (Sp K)))
    (hf : ∀ v : epsR K ⟶ B, IsTangent v → tanVal v f = 0) :
    GlobalTheory.CechDR.cmpForm (B.hom ≫ 𝟙 (Sp K)) f = 0 := by
  haveI := hab.comm
  have hsm : Smooth B.hom := hab.smooth
  obtain ⟨y, hy⟩ := GlobalTheory.T.exists_lieBasis_smooth_commGroupScheme_field K B g hdim
  refine GlobalTheory.T.cmpForm_eq_zero_of_pullback_vanishing K B hsm f fun L _ σ ↦ ?_
  letI : GrpObj ((Over.pullback (spMap σ)).obj B) := Functor.grpObjObj
  have hG := isGrpPullback_pullback B (spMap σ)
  have hab' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hab hG
  haveI := hab'.comm
  have hdim' : SmoothOfRelativeDimension g ((Over.pullback (spMap σ)).obj B).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hG.1 hdim
  have m : IsMor (dp0 K) (B.hom ≫ 𝟙 (Sp K)) (dp0 L) (((Over.pullback (spMap σ)).obj B).hom ≫ 𝟙 (Sp L)) σ
      (Limits.pullback.fst B.hom (spMap σ)) := IsMor.of_dividedPowersZeroIdeal _ (by simpa using hG.1.w)
  refine ⟨_, _, m, hG.1, fun u ↦ ?_⟩
  let c : epsR L ⟶ (Over.pullback (spMap σ)).obj B := GlobalTheory.GrpTangent.epsScale 0 ≫ u
  have hc : tanVal c (m.pullForm f) = 0 := by
    rw [tanVal_epsScale, zero_mul]
  have ht : IsTangent (c⁻¹ * u) := by
    rw [GlobalTheory.GrpTangent.isTangent_iff, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
      GlobalTheory.GrpTangent.epsZero_epsScale, inv_mul_cancel]
  have e : u = c * (c⁻¹ * u) := (mul_inv_cancel_left c u).symm
  rw [e, GlobalTheory.T.crystallineForm_tangentValue_mul_abelianScheme hC hH L _ g hab' hdim', hc, zero_add]
  exact GlobalTheory.T.pullbackForm_vanishes_tangents_of_lieBasis K B hsm g y hy f (fun i ↦ hf _ (hy.1 i)) L σ _ _ hG m _ ht

def lieVal (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] :
    Serre.Lie (Serre.intAct B) →ₗ[K] Module.Dual K (Form (B.hom ≫ 𝟙 (Sp K))) where
  toFun v := tanVal v.hom
  map_add' v w := LinearMap.ext fun f ↦ tanVal_mul v.isTangent w.isTangent f
  map_smul' r v := LinearMap.ext fun f ↦ tanVal_epsScale r v.hom f

theorem eq_of_tanVal_eq : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → ∀ (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ∀ v w : epsR K ⟶ B, IsTangent v → IsTangent w → (∀ f : Form (B.hom ≫ 𝟙 (Sp K)), tanVal v f = tanVal w f) → v = w := by
  intro hC hH K _ B _ g hab hdim v w hv hw h
  haveI := hab.comm
  obtain ⟨y, hy⟩ := GlobalTheory.T.exists_lieBasis_smooth_commGroupScheme_field K B g hdim
  let b := Serre.Lie.basis (Serre.intAct B) hy
  haveI := Module.Finite.of_basis b
  have hL : Module.finrank K (Serre.Lie (Serre.intAct B)) = g := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have htop : GlobalTheory.CechDR.ClosedForm (B.hom ≫ 𝟙 (Sp K)) = ⊤ := (hH K B g hab hdim).2.2.2.2.1.1
  obtain ⟨hfin, -, hrk⟩ : Module.Finite K (GlobalTheory.CechDR.GlobForm (B.hom ≫ 𝟙 (Sp K))) ∧
      Module.Projective K (GlobalTheory.CechDR.GlobForm (B.hom ≫ 𝟙 (Sp K))) ∧
      ∀ p : PrimeSpectrum K, Module.rankAtStalk (GlobalTheory.CechDR.GlobForm (B.hom ≫ 𝟙 (Sp K))) p = g :=
    (hH K B g hab hdim).2.2.1
  have hG : Module.finrank K (GlobalTheory.CechDR.GlobForm (B.hom ≫ 𝟙 (Sp K))) = g := by
    have h' := hrk (IsLocalRing.closedPoint K)
    rwa [Module.rankAtStalk_eq_finrank_of_free] at h'
  let eC : GlobalTheory.CechDR.ClosedForm (B.hom ≫ 𝟙 (Sp K)) ≃ₗ[K] GlobalTheory.CechDR.GlobForm (B.hom ≫ 𝟙 (Sp K)) := LinearEquiv.ofTop _ htop
  haveI : Module.Finite K (GlobalTheory.CechDR.ClosedForm (B.hom ≫ 𝟙 (Sp K))) := Module.Finite.equiv eC.symm
  have hC' : Module.finrank K (GlobalTheory.CechDR.ClosedForm (B.hom ≫ 𝟙 (Sp K))) = g := by rw [eC.finrank_eq, hG]
  let c := GlobalTheory.CechDR.cmpForm (B.hom ≫ 𝟙 (Sp K))
  have hcs : Function.Surjective c := cmpForm_surjective hC hH K B g hab hdim
  let P := lieVal K B
  have hker : LinearMap.ker c ≤ LinearMap.ker P.flip := fun f hf ↦
    LinearMap.ext fun u ↦ GlobalTheory.T.formValueOnTangentVector_eq_zero_of_globalForm_zero K B u.hom f hf
  let T : GlobalTheory.CechDR.ClosedForm (B.hom ≫ 𝟙 (Sp K)) →ₗ[K] Module.Dual K (Serre.Lie (Serre.intAct B)) :=
    (LinearMap.ker c).liftQ P.flip hker ∘ₗ (c.quotKerEquivOfSurjective hcs).symm.toLinearMap
  have hT : ∀ f, T (c f) = P.flip f := fun f ↦ by
    have : (c.quotKerEquivOfSurjective hcs).symm (c f) = Submodule.Quotient.mk f :=
      (c.quotKerEquivOfSurjective hcs).symm_apply_eq.2 rfl
    change (LinearMap.ker c).liftQ P.flip hker ((c.quotKerEquivOfSurjective hcs).symm (c f)) = _
    rw [this]; rfl
  have hTi : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro ω hω
    obtain ⟨f, rfl⟩ := hcs ω
    rw [LinearMap.mem_ker, hT] at hω
    exact cmpForm_eq_zero_of_tangent hC hH K B g hab hdim f fun v hv ↦
      LinearMap.congr_fun hω (Serre.Lie.mk (Serre.intAct B) v hv)
  have hTs : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Subspace.dual_finrank_eq, hL, hC'])).1 hTi
  let V := Serre.Lie.mk (Serre.intAct B) v hv
  let W := Serre.Lie.mk (Serre.intAct B) w hw
  have hsurj : Function.Surjective (T ∘ₗ c) := hTs.comp hcs
  have key : ∀ φ : Module.Dual K (Serre.Lie (Serre.intAct B)), φ V = φ W := fun φ ↦ by
    obtain ⟨f, rfl⟩ := hsurj φ
    rw [LinearMap.comp_apply, hT]
    exact h f
  have hVW : V - W = 0 :=
    (Module.forall_dual_apply_eq_zero_iff K (V - W)).1 fun φ ↦ by rw [map_sub, key φ, sub_self]
  exact congrArg Serre.Lie.hom (sub_eq_zero.1 hVW)

end GlobalTheory.LieInjField
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FirstOrderValue

def evalSq {S : Type} [CommRing S] (e : S) (he : e * e = 0) : DualNumber S →+* S where
  toFun z := z.fst + e * z.snd
  map_one' := by simp
  map_mul' a b := by
    simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, op_smul_eq_smul]
    linear_combination (-(a.snd * b.snd)) * he
  map_zero' := by simp
  map_add' a b := by simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add]; ring

theorem evalSq_apply {S : Type} [CommRing S] (e : S) (he : e * e = 0) (z : DualNumber S) :
    evalSq e he z = z.fst + e * z.snd := rfl

theorem dual_apply {R S : Type} [CommRing R] [CommRing S] (f : DualNumber R →+* S) (z : DualNumber R) :
    f z = f (TrivSqZeroExt.inl z.fst) + f (TrivSqZeroExt.inl z.snd) * f DualNumber.eps := by
  have hz : z = TrivSqZeroExt.inl z.fst + TrivSqZeroExt.inl z.snd * DualNumber.eps := by
    ext <;> simp
  conv_lhs => rw [hz]
  rw [map_add (f := _), map_mul]

theorem comp_prod_ofFn {C : Type*} [Category C] [CartesianMonoidalCategory C] {M A B : C} [MonObj M]
    (k : A ⟶ B) : ∀ {m : ℕ} (u : Fin m → (B ⟶ M)), k ≫ (List.ofFn u).prod = (List.ofFn fun i => k ≫ u i).prod
  | 0, u => by simp [MonObj.comp_one]
  | m + 1, u => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, MonObj.comp_mul, comp_prod_ofFn]

end GlobalTheory.FirstOrderValue

namespace GlobalTheory.FirstOrderValue

theorem valR_mul_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → ∀ (c : Fin n → Γ(X, U.1)) (x : tEpsG (chart U) ⟶ t.G), IsCombAtG t (chart U) v c x.left → (∀ (S : Type) [CommRing S] (ψ : DualNumber Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (a : Over.mk (g₀ ≫ t.G.hom) ⟶ tEpsG (chart U)) (w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), a.left = spMap ψ → (∀ b, IsTranslate t (ψ.comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1)))) g₀ (v b) (w b)) → ∀ (O : t.G.left.Opens) (f : Γ(t.G.left, O)), ⊤ ≤ g₀ ⁻¹ᵁ O → ⊤ ≤ ((a ≫ x) * (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G)).left ⁻¹ᵁ O ∧ valR ((a ≫ x) * (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G)).left O f = valR g₀ O f + ψ DualNumber.eps * ∑ b, ψ (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1)) (c b)) * (valR (w b) O f).snd) := by
  intro E _ _ _ H X t U n v hv c x hx S _ ψ g₀ a w ha hw O f hO
  obtain ⟨φ, hφ⟩ : ∃ φ : Γ(X, U.1) →+* S, φ = ψ.comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) := ⟨_, rfl⟩
  rw [← hφ] at hw
  obtain ⟨e, hedef⟩ : ∃ e : S, e = ψ DualNumber.eps := ⟨_, rfl⟩
  rw [← hedef]
  have he : e * e = 0 := by rw [hedef, ← map_mul, DualNumber.eps_mul_eps, map_zero]
  have hφs : ∀ s, φ s = ψ (TrivSqZeroExt.inl s) := fun s => by
    rw [hφ, RingHom.comp_apply, TrivSqZeroExt.algebraMap_eq_inl]

  have hg₀ : g₀ ≫ t.G.hom = spMap φ ≫ chart U := by
    have h1 : a.left ≫ spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) ≫ chart U = g₀ ≫ t.G.hom := Over.w a
    rw [← h1, ha, ← Category.assoc, GlobalTheory.KSLin.spMap_comp_spMap, hφ]
  choose g'' v'' hg'' hv'' hw'' using hw
  let g' : tEpsG (g₀ ≫ t.G.hom) ⟶ t.G :=
    Over.homMk (spMap (algebraMap S (DualNumber S)) ≫ g₀) (Category.assoc _ _ _)
  have hgg : ∀ b, g'' b = g' := fun b => Over.OverMorphism.ext (hg'' b)

  let h : tEpsG (g₀ ≫ t.G.hom) ⟶ Over.mk (chart U) :=
    Over.homMk (spMap (algebraMap S (DualNumber S)) ≫ spMap φ) (by
      show (spMap _ ≫ spMap φ) ≫ chart U = spMap _ ≫ g₀ ≫ t.G.hom
      rw [Category.assoc, hg₀])
  have hy0 : ∀ b, smT (g₀ ≫ t.G.hom) 0 (v'' b) = 1 := by
    intro b
    apply Over.OverMorphism.ext
    have h1 : (smT (g₀ ≫ t.G.hom) 0 (v'' b)).left = spMap (epsMul 0) ≫ (v'' b).left := rfl
    have e1 : (epsMul (0 : S)).comp (dualMap φ) = ((algebraMap S (DualNumber S)).comp φ).comp
        (TrivSqZeroExt.fstHom Γ(X, U.1) Γ(X, U.1) Γ(X, U.1)).toRingHom := by
      apply RingHom.ext; intro z; ext <;> simp [epsMul, dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    rw [h1, hv'' b, ← Category.assoc, GlobalTheory.KSLin.spMap_comp_spMap, e1, ← GlobalTheory.KSLin.spMap_comp_spMap,
      ← GlobalTheory.KSLin.spMap_comp_spMap, Category.assoc, Category.assoc, (hv b).2]
    have h2 : (h ≫ (1 : Over.mk (chart U) ⟶ t.G)).left = (1 : tEpsG (g₀ ≫ t.G.hom) ⟶ t.G).left :=
      congrArg (fun k : tEpsG (g₀ ≫ t.G.hom) ⟶ t.G => k.left) (MonObj.comp_one h)
    have h3 : (spMap (algebraMap S (DualNumber S)) ≫ spMap φ) ≫ (1 : Over.mk (chart U) ⟶ t.G).left =
        (1 : tEpsG (g₀ ≫ t.G.hom) ⟶ t.G).left := h2
    rw [← h3, Category.assoc]

  obtain ⟨u, hu, hux⟩ := hx
  obtain rfl : x = (List.ofFn u).prod := (Over.OverMorphism.ext hux).symm

  let ρ := evalSq e he
  have hρψ : ∀ r, ψ.comp (epsMul r) = (ρ.comp (epsMul (φ r))).comp (dualMap φ) := by
    intro r
    apply RingHom.ext; intro z
    simp only [RingHom.comp_apply]
    rw [dual_apply ψ, ← hedef, evalSq_apply]
    simp [epsMul, dualMap, hφs]
    ring
  have hsp : spMap ρ ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
    rw [GlobalTheory.KSLin.spMap_comp_spMap]
    have : ρ.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
      ext s; simp [ρ, evalSq_apply, TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]; simp [spMap]
  let ρh : Over.mk (g₀ ≫ t.G.hom) ⟶ tEpsG (g₀ ≫ t.G.hom) :=
    Over.homMk (spMap ρ) (by
      show spMap ρ ≫ spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom = g₀ ≫ t.G.hom
      rw [← Category.assoc, hsp, Category.id_comp])
  have hu' : ∀ b, a ≫ u b = ρh ≫ smT (g₀ ≫ t.G.hom) (φ (c b)) (v'' b) := by
    intro b
    apply Over.OverMorphism.ext
    have h1 : (smT (g₀ ≫ t.G.hom) (φ (c b)) (v'' b)).left = spMap (epsMul (φ (c b))) ≫ (v'' b).left := rfl
    simp only [Over.comp_left]
    rw [h1, hv'' b, hu b, ha]
    show spMap ψ ≫ spMap (epsMul (c b)) ≫ v b = spMap ρ ≫ spMap (epsMul (φ (c b))) ≫ spMap (dualMap φ) ≫ v b
    simp only [← Category.assoc, GlobalTheory.KSLin.spMap_comp_spMap, hρψ]
  have hg'eq : (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G) = ρh ≫ g' := by
    apply Over.OverMorphism.ext
    show g₀ = spMap ρ ≫ spMap (algebraMap S (DualNumber S)) ≫ g₀
    rw [← Category.assoc, hsp, Category.id_comp]
  have hmain : (a ≫ (List.ofFn u).prod) * (Over.homMk g₀ rfl : Over.mk (g₀ ≫ t.G.hom) ⟶ t.G) =
      ρh ≫ (g' * (List.ofFn fun b => smT (g₀ ≫ t.G.hom) (φ (c b)) (v'' b)).prod) := by
    rw [comp_prod_ofFn, hg'eq, MonObj.comp_mul, comp_prod_ofFn, mul_comm]
    simp only [hu']
  have hP1 := GlobalTheory.KSLin.snd_sectionValue_translate_list_prod_induction g₀ g' rfl O hO f n v'' (fun b => φ (c b)) hy0
  have hQ0 : smT (g₀ ≫ t.G.hom) 0 (g' * (List.ofFn fun b => smT (g₀ ≫ t.G.hom) (φ (c b)) (v'' b)).prod) = g' := by
    rw [smT_mul, GlobalTheory.KSLin.smT_const g₀ g' rfl, hP1.1, _root_.mul_one]
  have hQ : ⊤ ≤ (Over.Hom.left (g' * (List.ofFn fun b => smT (g₀ ≫ t.G.hom) (φ (c b)) (v'' b)).prod)) ⁻¹ᵁ O :=
    GlobalTheory.KSLin.top_le_of_smT_zero g₀ g' rfl O hO _ hQ0
  have hfst := GlobalTheory.KSLin.fst_comp_of_smT_zero g₀ g' rfl _ hQ0
  have hwb : ∀ b, (g' * v'' b).left = w b := fun b => by rw [← hgg b]; exact hw'' b
  rw [hmain, Over.comp_left]
  show ⊤ ≤ (spMap ρ ≫ _) ⁻¹ᵁ O ∧ valR (spMap ρ ≫ _) O f = _
  refine ⟨GlobalTheory.TanDeriv.comp_top_le ρ _ O hQ, ?_⟩
  have hOg : ⊤ ≤ g₀ ⁻¹ᵁ O := hO
  rw [GlobalTheory.KSLin.valR_spMap_comp ρ _ O hQ f, evalSq_apply, hP1.2]
  conv_rhs => rw [← hfst, GlobalTheory.KSLin.valR_spMap_comp _ _ O hQ f]
  simp only [hwb, hφs, TrivSqZeroExt.algebraMap_eq_inl]
  rfl

end GlobalTheory.FirstOrderValue
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

theorem _root_.GlobalTheory.T.cartierDivToWeilQDivisor_add_of_effective : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → letI := algebraΓOfHom p; ∀ (D E : CartierDiv X) (a b : ℕ), 0 < a → 0 < b → D.Eff → E.Eff → (b • D + a • E).Eff ∧ qWeil (b • D + a • E) (a * b) = qWeil D a + qWeil E b ∧ ∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB (b • D + a • E)] : ℚ) / ((a * b : ℕ) : ℚ) = (interNumRed ℂ C ![toLB D] : ℚ) / a + (interNumRed ℂ C ![toLB E] : ℚ) / b := by
  first | exact @GlobalTheory.QDivSum.sum_eq | exact GlobalTheory.QDivSum.sum_eq | (intros; apply GlobalTheory.QDivSum.sum_eq <;> assumption)
end
