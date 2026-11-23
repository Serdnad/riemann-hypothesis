module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle245
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle228
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMBeta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMConseq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMContPf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle209
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle184
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle222
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRStepA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRStepB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRvStepB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPair
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle066
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle033
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle166
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle163
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle211
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle243
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainRecursionFromSingleDescent
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactSupportFiniteClass
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMkTop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle244
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle086
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle122
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory
open scoped Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

def RDSNicePoly : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (o κ : ℕ)
    (Θ : B.DiffOp k r Wp Wq), CutMP.PolyOp o κ Θ →
      ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), NiceAll D F → NiceAll D (B.opApply Θ F) ∧ NiceAll D (B.opAdj Θ F)

section swap

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end swap

theorem opProp1_of_poly (hN : RDSNicePoly) {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) {o κ : ℕ} {Θ : B.DiffOp k r Wp Wq} (hP : CutMP.PolyOp o κ Θ)
    (hC : B.Commutes D (B.GPos D) Θ) : OpProp1 D Θ := by
  obtain ⟨hS, hG, -⟩ := CutMP.polynomial_decay_admissible k r Wp Wq o κ Θ hP
  refine ⟨hS _, hC, fun ε _ => ⟨κ, Nat.cast_nonneg _, fun T hT => ?_⟩, fun F hF => hN k r Wp Wq D o κ Θ hP F hF⟩
  obtain ⟨-, -, hb⟩ := hG κ le_rfl T hT
  obtain ⟨C₁, hC₁⟩ := hb (B.opOrder Θ + 5)
  exact ⟨C₁, fun u v hu hv hl g hg _ => hC₁ u v hu hv hl g hg⟩

section ffl

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}

theorem ffl_mono {D₁ D₂ : Set (Q.Mx k r)} (h : ∀ g ∈ Q.Glev k r 0, g ∈ D₂ → g ∈ D₁) {J : Q.Mx k r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ Q.FFl k r z z' π π' 0 D₁) : J ∈ Q.FFl k r z z' π π' 0 D₂ := by
  obtain ⟨h1, h2, h3, h4⟩ := hJ
  refine ⟨fun g₀ hg₀ => h1 g₀ ⟨hg₀.1, h g₀ hg₀.1 hg₀.2⟩, fun g hg n hn => h2 g ⟨hg.1, h g hg.1 hg.2⟩ n hn,
    fun g hg n hn => h3 g ⟨hg.1, h g hg.1 hg.2⟩ n hn, fun g hg u hu u' hu' => h4 g ⟨hg.1, h g hg.1 hg.2⟩ u hu u' hu'⟩

end ffl

theorem rDSOpRGrp_of_nice (hN : RDSNicePoly) : RDSOpRGrp := by
  intro Wp Wq _ _ _ _ _ _ k r D Y σ
  obtain ⟨ε, hε⟩ := CutMP.jDRRadP_of_steps CutMP.residue_first_move_holds CutMP.residue_second_move_holds k r
  obtain ⟨Θ, hP, hO, hR⟩ := CutMP.ri_real (Wp := Wp) (Wq := Wq) D.z D.z' Y (σ * ε)
  have hComm : B.Commutes D (B.GPos D) Θ := by
    intro p hp F hF g hg
    rw [hO] at hF
    have hgG : g ∈ B.GV k r := hg.1
    have hsg : B.sgs p g ∈ B.GV k r := Formalism.FourierDecayAlt.P.B6.conj_product_mem_unitary_group D hp hgG
    rw [hR _ _ (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hF) g hgG hgG]
    have e2 : B.rho D p (B.opApply Θ F) g =
        B.rho D p (fun x => (σ * ε) • CutMP.rhatOp k r D.z D.z' Y F x) g := by
      simp only [B.rho]
      rw [hR _ _ hF _ hsg hsg]
    rw [e2, CutMP.inverse_function_positive_holds k r Wp Wq D Y p hp F hF g hg]
    simp only [B.rho, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  refine ⟨Θ, opProp1_of_poly hN D hP hComm, ?_⟩
  intro J hJ x hx
  have hJ' : J ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') :=
    ffl_mono (D₁ := JF.Om k r D.z D.z') (D₂ := Q.OmPlus k r D.z D.z')
      (fun g hg hgO => ⟨by simpa [Q.Glev] using hg.1, hgO⟩) hJ
  have hDom := Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus (k := k) (r := r) D.z_mem D.z'_mem
  have hcell : Q.wCell k r (Fin.last r) x.1 * x.2 ∈ Q.OmPlus k r D.z D.z' :=
    Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus D.z_mem D.z'_mem hx.1 hx.2.1 hx.2.2
  have key := hε Wp Wq D.z D.z' D.π D.π' (Q.OmPlus k r D.z D.z') Y D.z_mem D.z'_mem hDom J hJ' x.1 hx.1 x.2
    hx.2.1 hcell
  rw [← key]
  have hW0 : Q.wCell k r (Fin.last r) x.1 * x.2 ∈ Q.Glev k r 0 :=
    Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hx.1 _)
      (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hx.2.1)
  have hWG : Q.wCell k r (Fin.last r) x.1 * x.2 ∈ B.GV k r := by simpa [Q.Glev] using hW0.1
  have hCk : B.CkOn ((r + k : ℕ) : ℕ∞) (Q.Glev k r 0 ∩ JF.Om k r D.z D.z') J := by
    intro g₀ hg₀
    obtain ⟨U', F', hU', hg₀U, hc, he⟩ := hJ.1 g₀ hg₀
    refine ⟨U', F', hU', hg₀U, hc.of_le (by exact_mod_cast le_top), fun y hy hyG => he y hy ?_⟩
    simpa [Q.Glev] using hyG
  simp only [Q.resG]
  rw [hR _ J hCk _ ⟨hW0, hWG, hcell⟩ hWG, smul_smul, smul_smul, smul_smul]
  congr 1
  ring

theorem rDSOpRvGrp_of_nice (hN : RDSNicePoly) : RDSOpRvGrp := by
  intro Wp Wq _ _ _ _ _ _ k r D Y σ
  obtain ⟨ε, hε⟩ := CutMP.jDRRadM_of_parts CutMP.mirror_residue_beta_holds CutMP.mirror_residue_top_holds CutMP.GrpMA.mirror_residue_first_move
    CutMP.mirror_residue_second_move (CutMP.jDRvConseq_of CutMP.mirror_residue_continuity) k r
  obtain ⟨Θ, hP, hO, hR⟩ := CutMP.rim_real (Wp := Wp) (Wq := Wq) D.z D.z' Y (σ * ε)
  have hComm : B.Commutes D (B.GPos D) Θ := by
    intro p hp F hF g hg
    rw [hO] at hF
    have hgG : g ∈ B.GV k r := hg.1
    have hsg : B.sgs p g ∈ B.GV k r := Formalism.FourierDecayAlt.P.B6.conj_product_mem_unitary_group D hp hgG
    rw [hR _ _ (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hF) g hgG hgG]
    have e2 : B.rho D p (B.opApply Θ F) g =
        B.rho D p (fun x => (σ * ε) • CutMP.rvhatOp k r D.z D.z' Y F x) g := by
      simp only [B.rho]
      rw [hR _ _ hF _ hsg hsg]
    rw [e2, CutMP.inverse_function_minus_holds k r Wp Wq D Y p hp F hF g hg]
    simp only [B.rho, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  refine ⟨Θ, opProp1_of_poly hN D hP hComm, ?_⟩
  intro J hJ x hx
  have hJ' : J ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') :=
    ffl_mono (D₁ := JF.Om k r D.z D.z') (D₂ := Q.OmPlus k r D.z D.z')
      (fun g hg hgO => ⟨by simpa [Q.Glev] using hg.1, hgO⟩) hJ
  have hDom := Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus (k := k) (r := r) D.z_mem D.z'_mem
  have hcell : Q.wCell k r (Fin.last r) x.1 * x.2 ∈ Q.OmPlus k r D.z D.z' :=
    Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus D.z_mem D.z'_mem hx.1 hx.2.1 hx.2.2
  have key := hε Wp Wq D.z D.z' D.π D.π' (Q.OmPlus k r D.z D.z') Y D.z_mem D.z'_mem hDom J hJ' x.1 hx.1 x.2
    hx.2.1 hcell
  rw [← key]
  have hW0 : Q.wCell k r (Fin.last r) x.1 * x.2 ∈ Q.Glev k r 0 :=
    Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hx.1 _)
      (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hx.2.1)
  have hWG : Q.wCell k r (Fin.last r) x.1 * x.2 ∈ B.GV k r := by simpa [Q.Glev] using hW0.1
  have hCk : B.CkOn ((r + k : ℕ) : ℕ∞) (Q.Glev k r 0 ∩ JF.Om k r D.z D.z') J := by
    intro g₀ hg₀
    obtain ⟨U', F', hU', hg₀U, hc, he⟩ := hJ.1 g₀ hg₀
    refine ⟨U', F', hU', hg₀U, hc.of_le (by exact_mod_cast le_top), fun y hy hyG => he y hy ?_⟩
    simpa [Q.Glev] using hyG
  simp only [Q.resG]
  rw [hR _ J hCk _ ⟨hW0, hWG, hcell⟩ hWG, smul_smul, smul_smul, smul_smul]
  congr 1
  ring

end Formalism.FourierDecayAlt.P.CutSE
end
end

section

open MeasureTheory Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem spectral_pairing_exhaustion : RDSPExh := by
  intro k r Wp Wq _ _ _ _ _ _ D X hX C hC hCO
  have hX' : X ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') := by
    rwa [rdb_ffl_om_eq] at hX
  have hqC : IsCompact (Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.qOf D.z D.z' '' C) :=
    hC.image_of_continuousOn ((Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.qOf_contOn D.z D.z').mono fun g hg => (hCO hg).2)
  have hqQ : Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.qOf D.z D.z' '' C ⊆ JF.QDom k r D.z D.z' := by
    rintro _ ⟨g, hg, rfl⟩
    exact (Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.om_eq_sgs D (hCO hg)).choose_spec.2.1
  obtain ⟨K', hK'c, hCK', hK'Q⟩ := exists_compact_between hqC (Formalism.FourierDecayAlt.P.BigCellOpenDomain.qdom_open D.z D.z') hqQ
  obtain ⟨φ, hφ, ⟨C', hC'c, hC'O, hC'φ⟩, hint⟩ :=
    Formalism.FourierDecayAlt.P.CutMP.JA.SA.average_one_cutoff_on_orbits k r Wp Wq D K' hK'c hK'Q
  have hsuppC : tsupport (fun g => φ g • X g) ⊆ C' := by
    refine closure_minimal (fun g hg => ?_) hC'c.isClosed
    by_contra hgC
    exact hg (by simp [hC'φ g hgC])
  refine ⟨fun g => φ g • X g,
    Q.OmPlus k r D.z D.z' ∩ Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.qOf D.z D.z' ⁻¹' interior K', ?_, ?_, ?_,
    Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.isOpen_qOf D.z D.z' isOpen_interior, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    by_cases hO : g₀ ∈ Q.OmPlus k r D.z D.z'
    · obtain ⟨U₁, φ', hU₁, hg₁, hφ', hφe⟩ := hφ g₀ hg₀
      obtain ⟨U₂, f', hU₂, hg₂, hf', hfe⟩ := hX'.1 g₀ ⟨(Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 g₀).2 hg₀, hO⟩
      refine ⟨U₁ ∩ U₂, fun g => φ' g • f' g, hU₁.inter hU₂, ⟨hg₁, hg₂⟩, ?_, ?_⟩
      · exact (hφ'.mono Set.inter_subset_left).smul (hf'.mono Set.inter_subset_right)
      · intro g hg hgG
        simp only [hφe g hg.1 hgG, hfe g hg.2 ((Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 g).2 hgG)]
    · refine ⟨C'ᶜ, fun _ => 0, hC'c.isClosed.isOpen_compl, fun h => hO (hC'O h).2, contDiffOn_const, ?_⟩
      intro g hg _
      simp [hC'φ g hg]
  · exact hC'c.of_isClosed_subset (isClosed_tsupport _) hsuppC
  · exact hsuppC.trans hC'O
  · intro g hg
    exact ⟨(hCO hg).2, hCK' ⟨g, hg, rfl⟩⟩
  · intro p hp g hg hs
    refine ⟨hg.2, ?_⟩
    have h2 := hs.2
    simp only [Set.mem_preimage] at h2 ⊢
    rwa [Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.qOf_sgs D hp] at h2
  · intro g hg
    have hJ : B.JF D (fun g => φ g • X g) g = (∫ p, φ (B.sgs p g) ∂D.μSS) • X g := by
      change ∫ p, JF.xiP D p • B.rho D p (fun g => φ g • X g) g ∂D.μSS = _
      rw [← integral_smul_const]
      apply integral_congr_ae
      filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp
      have hr : B.rho D p (fun g => φ g • X g) g = φ (B.sgs p g) • B.rho D p X g := by
        unfold B.rho
        rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
      rw [hr, smul_comm, Formalism.FourierDecayAlt.P.CutMP.JA.SA.eqv_of_FFl D X hX' hp hg]
    refine ⟨fun hgU => ?_, fun h0 => by rw [hJ, h0, smul_zero]⟩
    obtain ⟨p₀, hp₀, -, hge⟩ := Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.om_eq_sgs D hg
    have h1 := hint p₀ hp₀ _ (interior_subset hgU.2)
    rw [← hge] at h1
    rw [hJ, h1, one_smul]

end Formalism.FourierDecayAlt.P.CutSE
end
end

section

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

private theorem continuousAt_w1_of_ne_zero (k r : ℕ) (l : Fin r) {c : ℂ} (hc : c ≠ 0) :
    ContinuousAt (w1 k r l) c := by
  refine continuousAt_pi.2 fun p => continuousAt_pi.2 fun q => ?_
  show ContinuousAt (fun c => w1 k r l c p q) c
  simp only [w1]
  split_ifs
  · exact continuousAt_id
  · exact (continuous_star.continuousAt).inv₀ (star_ne_zero.mpr hc)
  · exact continuousAt_const
  · exact continuousAt_const
private theorem continuousAt_wCell_fst_of_mem_OmX (k r : ℕ) (x : (Fin r → ℂ) × Mx k r) (hx : x.1 ∈ OmX r)
    (i : Fin (r + 1)) : ContinuousAt (fun y : (Fin r → ℂ) × Mx k r => wCell k r i y.1) x := by
  induction i using Fin.induction with
  | zero =>
    simp only [Formalism.FourierDecayAlt.P.Qx6.wCell_zero]
    exact continuousAt_const
  | succ l ih =>
    simp only [Formalism.FourierDecayAlt.P.Qx6.wCell_succ]
    refine ih.mul ?_
    have hf : ContinuousAt (fun y : (Fin r → ℂ) × Mx k r => y.1 l) x := by fun_prop
    exact (continuousAt_w1_of_ne_zero k r l (hx l)).comp (f := fun y : (Fin r → ℂ) × Mx k r => y.1 l) hf

theorem spectral_pairing_big_cell : RDSPEOm := by
  intro k r Wp Wq _ _ _ _ _ _ D
  have hmem : ∀ x ∈ DomR k r D.z D.z', eR k r x ∈ JF.Om k r D.z D.z' := by
    intro x hx
    refine ⟨?_, ?_⟩
    · exact Formalism.FourierDecayAlt.P.TLB.wCell_gv (Pa := M.Par.mk k r 0 0 0 0) D hx
    · exact Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus D.z_mem D.z'_mem hx.1 hx.2.1 hx.2.2
  refine ⟨hmem, ?_, ?_⟩
  · intro x hx
    refine ContinuousAt.continuousWithinAt ?_
    exact (continuousAt_wCell_fst_of_mem_OmX k r x hx.1 (Fin.last r)).mul continuous_snd.continuousAt
  · intro g hg
    exact ⟨hg.1, hg.2.2⟩

end Formalism.FourierDecayAlt.P.CutSE
end
end

section

open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem spectral_pairing_orbital_membership : RDSPJFMem := by
  intro k r Wp Wq _ _ _ _ _ _ D F hF hcs hts
  have hpos : ∀ g ∈ tsupport F, (0 : ℝ) < Gf k r D.z D.z' g := fun g hg => (hts hg).2.2
  obtain ⟨ε, hε, hεle⟩ := hcs.isCompact.exists_forall_le' (PositiveOrbitOpen.gf_cont D.z D.z').continuousOn hpos
  have hnice : NiceAll D F := by
    refine ⟨ε, hε, hF, fun A m => compact_support_finite_class k r _ F (tsupport F) hF hcs.isCompact ?_ A m, ?_⟩
    · intro g hg
      by_contra h
      exact hg (subset_tsupport _ h)
    · intro g _ hg
      exact hεle g (subset_tsupport _ hg)
  refine ⟨(radial_orbital_niceness k r Wp Wq D F hnice).1, ?_⟩
  intro g _ hne
  by_contra hno
  push_neg at hno
  apply hne
  show ∫ p, _ ∂D.μSS = 0
  refine integral_eq_zero_of_ae ?_
  filter_upwards [B5.ae_inSS D] with p hp
  have h0 : F (B.sgs p g) = 0 := by
    by_contra h
    exact hno p hp (subset_tsupport _ h)
  show _ • _ = (0 : Wq →L[ℂ] Wp)
  simp only [B.sgs] at h0
  rw [h0]
  simp

end Formalism.FourierDecayAlt.P.CutSE
end
end

section

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem spectral_pairing_inner_swap : RDSPIpSwap := by
  intro k r z z' Wp Wq _ _ _ _ _ _ π π' μ Φ Ψ c
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin r => ℂ)
    (Equiv.subtypeUnivEquiv (p := fun l : Fin r => ((0 : Fin (r + 1)) : ℕ) ≤ l) (fun l => Nat.zero_le _))
  set e := MeasurableEquiv.piCongrLeft (fun _ : Fin r => ℂ)
    (Equiv.subtypeUnivEquiv (p := fun l : Fin r => ((0 : Fin (r + 1)) : ℕ) ≤ l) (fun l => Nat.zero_le _)) with he
  have happ : ∀ (c' : Cf r 0) (l : {l : Fin r // ((0 : Fin (r + 1)) : ℕ) ≤ l}), e c' l.1 = c' l := by
    intro c' l
    rw [he]
    exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin r => ℂ)
      (Equiv.subtypeUnivEquiv (p := fun l : Fin r => ((0 : Fin (r + 1)) : ℕ) ≤ l) (fun l => Nat.zero_le _)) c' l
  have hglue : ∀ c' : Cf r 0, glue 0 c c' = e c' := fun c' => funext fun l => by
    simp only [glue]
    rw [dite_eq_left (show ((0 : Fin (r + 1)) : ℕ) ≤ (l : ℕ) from Nat.zero_le _)]
    exact (happ c' ⟨l, Nat.zero_le _⟩).symm
  have hprod : ∀ c' : Cf r 0,
      (∏ l : {l : Fin r // ((0 : Fin (r + 1)) : ℕ) ≤ l}, ‖c' l‖ ^ (-2 : ℤ)) = ∏ l : Fin r, (‖e c' l‖ ^ 2)⁻¹ := by
    intro c'
    refine Fintype.prod_equiv (Equiv.subtypeUnivEquiv (fun l => Nat.zero_le _)) _ _ (fun l => ?_)
    show ‖c' l‖ ^ (-2 : ℤ) = (‖e c' l.1‖ ^ 2)⁻¹
    rw [happ c' l, zpow_neg]
    norm_cast
  unfold radIp LocFacts₂ pairAt dxc
  simp only [B.hsInner]
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  rw [← hmp.integral_comp']
  refine integral_congr_ae (ae_of_all _ fun c' => ?_)
  simp only
  rw [hglue c', ENNReal.toReal_ofReal (Finset.prod_nonneg fun _ _ => by positivity), Complex.real_smul, hprod c']

end Formalism.FourierDecayAlt.P.CutSE
end
end

section

namespace Formalism.FourierDecayAlt.P

theorem head_top : KB.HeadTop := pb_headTop_of_mkTop top_truncation_of_averages

end Formalism.FourierDecayAlt.P
end
