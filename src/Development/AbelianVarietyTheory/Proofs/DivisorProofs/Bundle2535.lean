module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2526
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1703
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1505
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle092
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeafDataOfOnTieOfIntegral
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle192
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle093
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2527
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernel
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle017
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2532
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2530
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2528
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianScheme_structureSheafCohomology_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → FP R (HO1 A.hom) g ∧ WedgeO (OAff A.hom) ∧ StructureSheafH1BaseChange A.hom ∧ StructureSheafH2BaseChange A.hom := by
  first | exact @GlobalTheory.AbCohRing.oStr_noetherian | exact GlobalTheory.AbCohRing.oStr_noetherian | (intros; apply GlobalTheory.AbCohRing.oStr_noetherian <;> assumption)
end

section

noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.TensAlg

variable {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)]

theorem atPl_eq_toLinearMap (w : T) (L : Module.End ℂ (V w)) :
    atPl w L = (PiTensorProduct.mapMultilinear ℂ V V).toLinearMap (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w L := rfl

theorem atPl_one (w : T) : atPl w (1 : Module.End ℂ (V w)) = 1 := by
  unfold atPl
  have h : Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w 1 = fun i => LinearMap.id := by
    funext i
    by_cases hi : i = w
    · subst hi; simp; rfl
    · simp [hi]
  rw [h]; exact PiTensorProduct.map_id

theorem atPl_sub_smul (w : T) (L : Module.End ℂ (V w)) (c : ℂ) (y : ⨂[ℂ] i, V i) :
    atPl w (L - c • 1) y = atPl w L y - c • y := by
  rw [atPl_eq_toLinearMap, map_sub, map_smul, ← atPl_eq_toLinearMap, ← atPl_eq_toLinearMap, atPl_one]
  simp

theorem atPl_tprod (w : T) (L : Module.End ℂ (V w)) (v : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v w (L (v w))) := by
  unfold atPl
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases hi : i = w
  · subst hi; simp
  · simp [hi]

theorem atPl_tprod_eq_zero (w : T) (L : Module.End ℂ (V w)) (v : ∀ i, V i) (h : L (v w) = 0) :
    atPl w L (PiTensorProduct.tprod ℂ v) = 0 := by
  rw [atPl_tprod, h]
  exact MultilinearMap.map_update_zero _ _ _

theorem tensAll_mono {H H' : ∀ w, Submodule ℂ (V w)} (h : ∀ w, H w ≤ H' w) : tensAll H ≤ tensAll H' := by
  apply Submodule.span_mono
  rintro y ⟨f, hf, rfl⟩
  exact ⟨f, fun w => h w (hf w), rfl⟩

theorem iInf_hwSub_le {R S : T → ℕ} (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ (V w))
    (μ : ∀ w, Ix (R w) (S w) → ℚ) :
    (⨅ w, hwSub (actAt w (a w)) (μ w)) ≤ tensAll (fun w => hwSub (a w) (μ w)) := by
  intro y hy
  rw [Submodule.mem_iInf] at hy
  refine GlobalTheory.T.mem_piTensorSpanAllFactors_of_jointKernel T V
    (fun w => {l | (∃ c, l = a w (Eab c c) - ((μ w c : ℚ) : ℂ) • 1) ∨ ∃ c d, posC c d ∧ l = a w (Eab c d)})
    (fun w => hwSub (a w) (μ w)) ?_ y ?_
  · intro w x hx
    simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
    refine ⟨fun c => ?_, fun c d hcd => ?_⟩
    · exact hx _ (Or.inl ⟨c, rfl⟩)
    · exact hx _ (Or.inr ⟨c, d, hcd, rfl⟩)
  · intro w l hl
    have hyw := hy w
    simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hyw
    rcases hl with ⟨c, rfl⟩ | ⟨c, d, hcd, rfl⟩
    · rw [atPl_sub_smul]
      have h1 := hyw.1 c
      rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, actAt_apply] at h1
      exact h1
    · have h2 := hyw.2 c d hcd
      rw [actAt_apply] at h2
      exact h2

end GlobalTheory.HoweR.TensAlg

namespace GlobalTheory.HoweR


open GlobalTheory.HoweR.TensAlg in
theorem howeAlg_tensAny : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)], ∀ (R S : T → ℕ) (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ (V w))
    (C : ∀ w, Submodule ℂ (V w)), (∀ w, Pack (a w) (C w)) → HoweAlg (fun w => actAt w (a w)) (tensAny C) := by
  intro T _ _ V _ _ R S a C hP
  have hG := GlobalTheory.T.isGoodGlRep_piTensorActionAtFactor_and_commute T V R S a (fun w => (hP w).1)
  choose α β α' β' hQ using fun w => (hP w).2.2.1
  choose μ v hv hgen hmul using fun w => (hP w).2.2.2.2
  refine GlobalTheory.T.howeAlg_of_cyclic_highest_weight T R S (⨂[ℂ] i, V i) (fun w => actAt w (a w)) hG.1 hG.2 (tensAny C) α β α' β'
    (fun w => GlobalTheory.T.glActionQuadraticRelationModulo_piTensorAtFactor T V C w (R w) (S w) (a w) _ _ _ _ (hQ w)) ?_ ?_
  · intro B
    choose U hUfd hU using fun w => (hP w).2.2.2.1 B
    refine ⟨tensAll U, (GlobalTheory.T.piTensorSpanAllFactors_sup_finite_singleton T V U C).2.1 hUfd, fun ν hν => ?_⟩
    exact (iInf_hwSub_le a ν).trans
      ((tensAll_mono (fun w => hU w (ν w) (fun c => hν w c))).trans (GlobalTheory.T.piTensorSpanAllFactors_sup_finite_singleton T V U C).1)
  · refine ⟨μ, PiTensorProduct.tprod ℂ v, fun w => ?_,
      fun N hN hC hvN => GlobalTheory.T.tprod_cyclic_modulo_spanSomeFactor T V R S a C v hgen N hN hC hvN, ?_⟩
    · have h := hv w
      simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at h ⊢
      refine ⟨fun c => ?_, fun c d hcd => ?_⟩
      · rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, actAt_apply, ← atPl_sub_smul]
        exact atPl_tprod_eq_zero w _ v (h.1 c)
      · rw [actAt_apply]
        exact atPl_tprod_eq_zero w _ v (h.2 c d hcd)
    · refine (iInf_hwSub_le a μ).trans ((tensAll_mono (fun w => hmul w)).trans ?_)
      refine (GlobalTheory.T.piTensorSpanAllFactors_sup_finite_singleton T V (fun w => Submodule.span ℂ {v w}) C).1.trans ?_
      exact sup_le_sup_right ((GlobalTheory.T.piTensorSpanAllFactors_sup_finite_singleton T V (fun w => Submodule.span ℂ {v w}) C).2.2 v) _

end GlobalTheory.HoweR

end
end

section

set_option autoImplicit false

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn

theorem lat_span_of_hypC {D : D7} {T : Top D} (h : LawsP T) {j : ℕ} (hj : InR D j) {large₂ : SizeData₂ D} {H : WeightAlgebra.KHyp}
    {C2 A2 CR Bx CT : ℝ} {S : WeightAlgebra.Scal (recB h.toLawsCore)} {ka wL wF : WeightFamilies.Wt D j} {Tn nP nW : ℕ} {h0 : ℝ}
    {nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ}
    (hyp : Formalism.MainNotions.Gaps.EtaleWeightGaps.HypC large₂ (recPJ h j hj) H C2 A2 CR Bx CT S ka wL wF Tn nP nW h0 nus) :
    Formalism.MainNotions.Gaps.EtaleWeightGaps.LatAt (recB h.toLawsCore) j ka ∧ ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) ka ∧
      WeightAlgebra.H2 (recPJ h j hj) S ka wL wF := by
  obtain ⟨hA, -, hB, -, hH2, -⟩ := hyp
  obtain ⟨-, -, -, hK, -, po, -, -, PLam, -, -, -, -, hka⟩ := hB
  have sK := GlobalTheory.RunLat.spanAt_of_shortG _ _ _ _ hka
  exact ⟨GlobalTheory.latAt_record D _ h.toLawsCore (GlobalTheory.RunIn.gamAt_of_lawsCore' D _ h.toLawsCore) large₂ H.CA hA j ka _
    (recPJ h j hj) S wL wF hK sK hH2, sK, hH2⟩

theorem ownAt_pos (D : D7) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) : 0 < ownAt D v := by
  unfold ownAt
  split_ifs
  · exact D.host.pde'_prime.pos
  · exact D.host.pde_prime.pos




theorem leaves_sup_span_data : ∀ CK : ℝ, ∃ x₁ : ℝ, ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → CoreTies L EX J R → OwnPin r → PageNum Tp x₁ → RunsHold Tp hK EX CK r → R.IsGrp F → R.tup_mu_conj → R.tup_mu_off → R.tup_mu_ne → LeafSup O ∧ LeafSpan O ∧ LeafLemmaS O ∧ LeafData O := by
  intro CK
  refine ⟨0, ?_⟩
  intro D G _ _ Pl0 T0 A J inst R F κ v₀ fw L Pm Tp hK EX r c O hrec _ _ _ hrun hgrp _ _ _
  obtain rfl : κ = fun i : Fin D.R.m => kaR Tp hK ((i : ℕ) + 1) := funext hrec.kap
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hrec.tied
  have hok := hrec.ok
  have h3 : LeafSup O ∧ LeafSpan O ∧ LeafLemmaS O := by
    refine leaves_sup_span_lemmaS_of_formTieK GlobalTheory.chartIndependence_unconditional D L Pm Tp hK hinj EX _ _ _ _ _ c O
      fun v i => ?_
    letI : Algebra (r.used v).full.J.Q.c.F D.what₂.LL := inst
    obtain ⟨a1, a2, a3⟩ := lat_span_of_hypC _ _ (hrun v (hok.laws v).p hinj _ (inR_succ i)).1
    exact ⟨(r.used v).full, (hok.laws v).p, _, inR_succ i, ownAt D v, inst, z i, act i, fun g => r.lev i (mirIncl R g),
      (ht v i).1.toFormTieK, (ht v i).1.act_eq, hok.laws v, hok.xiRat v i, hok.cover v i, ownAt_pos D v, a1, a2, a3⟩
  refine ⟨h3.1, h3.2.1, h3.2.2, ?_⟩
  have hU : ∀ g, g ∈ F.P0 ↔ ∀ PP : R.Pg, R.eG g PP ∈ unip (kP PP.1) D.R.r := fun g => by
    rw [GlobalTheory.OntoChain.mem_base_iff hgrp.levels]
    refine Iff.trans ?_ ((mem_pi_unip_iff R (R.eG g)).symm.trans ⟨fun H PP => H PP (Set.mem_univ _), fun H PP _ => H PP⟩)
    refine exists_congr fun u => and_congr_right fun _ => ?_
    rw [← eG_mirIncl, R.eG.injective.eq_iff]
  have key : ∀ v (i : Fin D.R.m), GlobalTheory.TraceLattice.TiedAt A hinj EX O (mirIncl R) F.P0 F.ψ0⁻¹
      (fun _ _ _ _ _ _ _ _ _ => True) v i := fun v i =>
    ⟨(r.used v).full, inst, R, _, v₀, (hok.laws v).p, fw, ownAt D v, i, _, _, _, z i, act i, r.lev i, 1, y v i,
      (ht v i).1, hok.laws v, hok.xiRat v i, kaWt_n _ _ _ _, GlobalTheory.TraceLattice.kaR_lastPos Tp hK (inR_succ i),
      @GlobalTheory.TraceLattice.detOneOn_of_pins D G _ _ _ _ A (r.used v).full inst R i (hok.laws v) _ (hok.level v i) hok.half _ hU,
      trivial⟩
  exact GlobalTheory.TraceLattice.leafData_of_onTie_of_leafSpan h3.2.1 fun w _ => ⟨key w, key _⟩

end GlobalTheory.BigOn
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_unramified_character_good : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v →
    (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) → ∀ t : E →ₐ[F] Fv F v,
    ∃ ν₀ : (Fv F v)ˣ →* ℂˣ, (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν₀ (unifAt v) : ℂ)) ^ m ≠ (r : ℂ)) ∧
      ∀ ι, G.M'.IsLinBar B.ψ t 1 1 ι → ∀ g₀ : GL (Fin a') (Fv F v), ∃ g ∈ UAt σ G.V' (evFin F v),
        ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
          Acts (evFin F v) (om' (g, 1)) φ φ₁ ∧ ι φ₁ = GlobalTheory.SplitFlip.omB ν₀ ν₀ g₀ 1 (ι φ) := by
  first | exact @GlobalTheory.GoodPlaceAct.act_omB | exact GlobalTheory.GoodPlaceAct.act_omB | (intros; apply GlobalTheory.GoodPlaceAct.act_omB <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

theorem _root_.GlobalTheory.T.augmentation_submodule_first_factor : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) →
    ∀ N : Submodule ℂ ((Fin a × Fin (a + a') → Fv F v) → ℂ), augAt om v ≤ N → N ≤ SB _ →
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ N, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h)) φ φ₁ → φ₁ ∈ N) →
      N = augAt om v ∨ N = SB _ := by
  first | exact @GlobalTheory.IrrCoinvV.irrV | exact GlobalTheory.IrrCoinvV.irrV | (intros; apply GlobalTheory.IrrCoinvV.irrV <;> assumption)
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.godement_summable_height_rpow_representatives : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → ∀ T, IsRepsJ σ J X T → ∀ (g : GAd σ J) (e : ℝ), ((n : ℝ) - (r + 1)) < e → Summable fun t : T => h (t.1.1 * g) ^ e := by
  first | exact @GlobalTheory.ResidueEisenstein.summable_height_rpow_reps | exact GlobalTheory.ResidueEisenstein.summable_height_rpow_reps | (intros; apply GlobalTheory.ResidueEisenstein.summable_height_rpow_reps <;> assumption)
end

section


theorem _root_.GlobalTheory.T.weil_convergence_of_kernel : GlobalTheory.ThK.KP → GlobalTheory.ThK.WeilConv := by
  first | exact @GlobalTheory.ThKWeil.weilConv | exact GlobalTheory.ThKWeil.weilConv | (intros; apply GlobalTheory.ThKWeil.weilConv <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.simpleSubquotient_dualWeyl_embeds_highestWeight : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (lam τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], IsSimpleModule (alg O N lam) Gm → SubQ O N lam ϖ Gm → ∃ mu : ι → ℕ → ℕ, (∀ τ, Antitone (res N (mu τ)) ∧ ∑ a : Fin N, mu τ a = ∑ a : Fin N, lam τ a ∧ (∀ a : Fin N, lam τ (N - 1) ≤ mu τ a ∧ mu τ a ≤ lam τ 0) ∧ ∃ (e : alg O N lam) (z : Gm), IsProj O N lam τ (res N (mu τ)) e ∧ e • z ≠ 0) ∧ Embeds O N lam mu ϖ Gm := by
  first | exact @GlobalTheory.HighWt.simpleSubquot_embeds | exact GlobalTheory.HighWt.simpleSubquot_embeds | (intros; apply GlobalTheory.HighWt.simpleSubquot_embeds <;> assumption)
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

theorem _root_.GlobalTheory.T.sections_adjointNef_separate_etaleFibre : GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.NefNumerics → ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)], IsProjOver p → IsProjOver (f ≫ p) → 1 ≤ n → letI := algebraΓOfHom p; letI := algebraΓOfHom (f ≫ p); ∀ (K : CanonLB (f ≫ p) n) (N : LB W) (hN : N.IsLB) (N' B : LB M) (hN' : N'.IsLB) (hB : B.IsLB) (m : ℕ) (x : Sp ℂ ⟶ W) (U : W.Opens), IsNef ℂ N → IsBig ℂ N → IsNef ℂ (N.pull f) → IsBig ℂ (N.pull f) → IsNef ℂ N' → (n + 1).choose 2 < m → cls B hB = m • CechPic.pull f (cls N hN) + cls N' hN' → x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → Etale (f ∣_ U) → (∀ (Z : Closeds W) (e : ℕ), IsIrreducible (Z : Set W) → Set.range x ⊆ Z → 1 ≤ e → topologicalKrullDim (Z : Set W) = e → 0 < interNumRed ℂ Z fun _ : Fin e => N) → ∀ (J : Type) [Fintype J] (z : J → (Sp ℂ ⟶ M)), Function.Injective z → (∀ j, z j ≫ f = x) → ∀ (k : J → (tens K.bundle B).ι) (hk : ∀ j, ⊤ ≤ z j ⁻¹ᵁ (tens K.bundle B).U (k j)) (a : J → ℂ), (∀ g : H0 (f ≫ p) (tens K.bundle B) ⊤, ∑ j, a j * H0.val (z j) (k j) le_top (hk j) g = 0) → a = 0 := by
  first | exact @GlobalTheory.EtaleSep.sections_separate_fibre | exact GlobalTheory.EtaleSep.sections_separate_fibre | (intros; apply GlobalTheory.EtaleSep.sections_separate_fibre <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.exists_freeThickening_level_finitelyMany_elements : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R) (n m : ℕ) (T : Thick κ t), IsLev T.δ (n + 1) → ∃ (F : Thick κ t) (u : T ⟶ F) (τ : Fin m → F.B), IsFree (n + 1) u τ ∧ (KK κ t).QAt u := by
  first | exact @GlobalTheory.PDForm.FreeFin.exists_free | exact GlobalTheory.PDForm.FreeFin.exists_free | (intros; apply GlobalTheory.PDForm.FreeFin.exists_free <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.crystallineDeRhamRelation_natural_smoothLift_morphism : (∀ (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀), φ₀ ≫ D.i = D'.i ≫ φ → ∀ c h h', Λ.Rel1 c h → Λ'.Rel1 (m.pull1 c) h' → IsPull1 hφ h h') ∧ ∀ (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀), φ₀ ≫ D.i = D'.i ≫ φ → ∀ c h h', Λ.Rel2 c h → Λ'.Rel2 (m.pull2 c) h' → IsPull2 hφ h h' := by
  first | exact @GlobalTheory.PDForm.LiftNat.main | exact GlobalTheory.PDForm.LiftNat.main | (intros; apply GlobalTheory.PDForm.LiftNat.main <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.intersection_pullback_eq_degree_mul_intersection : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), A.dim = B.dim → ∀ (J : Type) [Fintype J], Fintype.card J = A.dim → ∀ c : J → Pic B.X.left, inter A (fun j => CechPic.pull f.hom.left (c j)) = deg f * inter B c := by
  first | (exact @GlobalTheory.AV.AbVar.inter_pull_eq_deg_mul_inter) | (exact GlobalTheory.AV.AbVar.inter_pull_eq_deg_mul_inter) | (intros; apply GlobalTheory.AV.AbVar.inter_pull_eq_deg_mul_inter  <;> assumption)
end
