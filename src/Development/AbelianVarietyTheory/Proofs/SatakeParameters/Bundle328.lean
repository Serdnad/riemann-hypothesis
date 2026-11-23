module

public import Formalism.LocalToGlobal.Columns.Bundle024
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Formalism.LocalToGlobal.KernelLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopLevelDatumTransformAtTwistPrimeUnderLevels
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle113
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumLawK1DepthTwiceM
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumTwistPrimeInvariantCongruentFrames
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle001
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle317
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle318
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle319
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle320
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle119
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle018
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle112
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.topLevelDatum_transform_at_twist_prime_under_levels : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) {G : ChGlob X R.m} {m2 : ℕ},
  ChIdx.Ok Ch sel mu cst L G m2 → QUnif sel mu → ∀ (b : L.β (m2 + 1)) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
  ∀ (g : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1))) (z : X.K), MidLev Ch sel mu cst (m2 + 1) P (L.h (m2 + 1) b P) g z →
  ∀ (g' : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))) (z' : X.K), TopLev Ch sel mu cst (m2 + 1 + 1) P g' z' →
  ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y₁ y₂ : Sp X.E (R.N (m2 + 1))),
  ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (y₁ - y₂) ∈ stdAt X.E (R.N (m2 + 1)) P.1 →
  ((qOf P.1 : X.E) ^ cst.M) • y₂ ∈ stdAt X.E (R.N (m2 + 1)) P.1 →
  z' * topDat Ch sel mu cst (m2 + 1) P (g'.symm.toLinearMap ∘ₗ y ∘ₗ g.toLinearMap) (g.symm y₁) *
      rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) * rhoT Ch sel mu (m2 + 1) P ((LinearEquiv.det g' : X.Eˣ) : X.E) =
    z * topDat Ch sel mu cst (m2 + 1) P y y₂ := by
  first | exact @GlobalTheory.TwTopLaw.topLawQ_midTop | exact GlobalTheory.TwTopLaw.topLawQ_midTop | (intros; apply GlobalTheory.TwTopLaw.topLawQ_midTop <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopStep GlobalTheory.TopLaw GlobalTheory.TopFrameQ

namespace GlobalTheory.TopFrameQM

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu))

theorem topDat_frames_qM {m2 : ℕ} (hm : R.m = m2 + 2) (hc : cst.Ok) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (hD : 2 * cst.M ≤ cst.D P)
    (κ : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1)))
    (κ' : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1)))
    (hκ : κ ∈ GLint X.E _ P.1)
    (hκc : ∀ w ∈ stdAt X.E _ P.1, ((qOf P.1 : X.E) ^ cst.D P)⁻¹ • (κ w - w) ∈ stdAt X.E _ P.1)
    (hκ' : κ' ∈ GLint X.E _ P.1)
    (hκ'c : ∀ w ∈ stdAt X.E _ P.1, ((qOf P.1 : X.E) ^ (2 * cst.M))⁻¹ • (κ' w - w) ∈ stdAt X.E _ P.1)
    (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y'' : Sp X.E (R.N (m2 + 1)))
    (hy'' : ∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y'' l)) :
    topDat Ch sel mu cst (m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
      topDat Ch sel mu cst (m2 + 1) P y y'' := by
  have hM1 : 1 ≤ cst.M := hc.M_pos
  have hMD : cst.M + 1 ≤ cst.D P := by omega
  have hMD' : cst.M + 1 ≤ 2 * cst.M := by omega
  have hq : (qOf P.1 : X.E) ≠ 0 := qOf_ne_zero
  have hκ's : κ'.symm ∈ GLint X.E _ P.1 := (GLint X.E _ P.1).inv_mem hκ'
  have hκs : κ.symm ∈ GLint X.E _ P.1 := (GLint X.E _ P.1).inv_mem hκ
  have hκ'sc := cong_symm hκ' hκ'c
  by_cases hg : ∀ j, abelian₂ P.1 (R.N (m2 + 1 + 1)) cst.M (y (Pi.single j 1))
  · unfold topDat
    congr 1
    · unfold PhiTopG
      rw [if_neg hP]
      have hc0 : cOf R (m2 + 1) = 0 := cOf_topB hm
      have hw : ∀ w ∈ stdAt X.E (R.N (m2 + 1)) P.1, ∀ l : Fin (R.N (m2 + 1 + 1)), l.1 + 1 < R.N (m2 + 1 + 1) →
          IntAt P.1 ((κ'.symm (y (κ w)) - y w) l / (qOf P.1 : X.E)) := by
        intro w hw l hl
        have hu := abelian₂.of_basis y hg (glint_mem (⟨κ, hκ⟩ : GLint X.E _ P.1) hw)
        have d1 := mem_stdAt.1 (abelian₂.move hκ's hκ'sc hMD' hu).2 l
        have e1 := intAt_inv_pow_le (a := 1) (by omega) d1
        have hu' : ((qOf P.1 : X.E) ^ cst.D P)⁻¹ • (κ w - w) ∈ stdAt X.E _ P.1 := hκc w hw
        have hyu := (abelian₂.of_basis y hg hu').2 l hl
        rw [map_smul, map_sub, Pi.smul_apply, smul_eq_mul] at hyu
        have e2 := intAt_inv_pow_le (a := 1) (by omega) hyu
        rw [pow_one] at e1 e2
        have e3 := e1.add e2
        rw [← add_div] at e3
        convert e3 using 2
        simp only [Pi.sub_apply]
        ring
      have key := fun z hz => GlobalTheory.TopInv.PhiQ_add (K := X.K) (GlobalTheory.TopInv.qOf_mem P.1) hq
        (resChar (mu : Chr X.F X.E X.K) P.1) R.k R.r (cOf R (m2 + 1)) (R.N (m2 + 1)) (R.N (m2 + 1 + 1) - 1) hc0
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) z hz
      refine (congrArg _ (add_sub_cancel _ _)).symm.trans (key _ ?_)
      intro s l
      have hws : (LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) (Pi.single s (1 : X.E)) : Sp X.E _) ∈
          stdAt X.E (R.N (m2 + 1)) P.1 :=
        mem_stdAt.2 fun a => GlobalTheory.TopInv.single_int s (Fin.castAdd _ a)
      have := hw _ hws ⟨l.1, by omega⟩ (by show l.1 + 1 < _; omega)
      exact this
    · have h1 := ftY_comp_glint sel mu cst hc P (fun _ => hD) ⟨κ, hκ⟩
          (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ κ'.symm.toLinearMap ∘ₗ y) y'' (κ.symm y'')
          (fun h => absurd h hP) (fun _ => hy'') (fun h => absurd h hP)
          (fun _ => by
            show ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (κ (κ.symm y'') - y'') ∈ _
            rw [LinearEquiv.apply_symm_apply, sub_self, smul_zero]
            exact zero_mem _)
      refine h1.trans ?_
      have hy''s : ((qOf P.1 : X.E) ^ cst.M) • y'' ∈ stdAt X.E _ P.1 :=
        mem_stdAt.2 fun l => by simpa only [Pi.smul_apply, smul_eq_mul] using hy'' l
      have hδ : ∀ i, IntAt P.1 (((qOf P.1 : X.E) ^ cst.M)⁻¹ *
          ((atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ κ'.symm.toLinearMap ∘ₗ y) -
            atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) (Pi.single i 1)) := by
        intro i
        have d1 := mem_stdAt.1 (abelian₂.move hκ's hκ'sc (v := y (Pi.single i 1)) hMD' (hg i)).2
        have e1 : ∀ l, IntAt P.1 ((κ'.symm (y (Pi.single i 1)) - y (Pi.single i 1)) l / (qOf P.1 : X.E) ^ cst.M) :=
          fun l => intAt_inv_pow_le (by omega) (d1 l)
        have e2 := GlobalTheory.TopInv.atNL_int (R.N (m2 + 1 + 1) - 1) _ _ e1
        rw [inv_mul_eq_div]
        convert e2 using 2
        simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
        rfl
      have h2 := GlobalTheory.ftY_pert_qM sel mu cst hc P hP hD (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y)
        _ y'' hδ hy''s
      rw [add_sub_cancel] at h2
      exact h2
  · have h0 : topDat Ch sel mu cst (m2 + 1) P y y'' = 0 := by
      by_contra hne
      exact hg (lam_of_topDat_ne Ch sel mu cst _ P hP y y'' hne)
    rw [h0]
    by_contra hne
    apply hg
    have h1 := lam_of_topDat_ne Ch sel mu cst _ P hP _ _ hne
    have h2 := lam_comp hκs hκ' hκ'c hMD' _ h1
    intro j
    have := h2 j
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using this

end Main

end GlobalTheory.TopFrameQM
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_satakeParameter_at_inertPlace_of_spherical : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → π.SphAt v → ∀ Dv : InertDatum L n v w, ∃ α, NG.SatAt π Dv α := by
  first | exact @GlobalTheory.SatExists.exists_satAt | exact GlobalTheory.SatExists.exists_satAt | (intros; apply GlobalTheory.SatExists.exists_satAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.isotypicFixedVector_isSatakeEigen_inertPlace : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.SatAt π Dv α → ∀ φ ∈ NG.isoTyp π.ρ π.S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ φ = φ) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), heckeFunI L n (Umax L n) Dv h φ = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • φ := by
  first | exact @GlobalTheory.EigIsoInert.eig_of_isoTyp_fixed | exact GlobalTheory.EigIsoInert.eig_of_isoTyp_fixed | (intros; apply GlobalTheory.EigIsoInert.eig_of_isoTyp_fixed <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernelEntry_period_ne_zero_and_lattice_laws : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex), t.δ ≠ 0 ∧ t.B.LatAll ∧ t.B.VecP t.χ ∧ t.B.EqP t.χ := by
  first | exact @GlobalTheory.TieBase.base_data | exact GlobalTheory.TieBase.base_data | (intros; apply GlobalTheory.TieBase.base_data <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.transportedLattices_two_classes_admissible : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) u μ i j c c', TaylorLogMetric.admitted D _ _ (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N j c')) := by
  first | exact @GlobalTheory.TwV.adm_seam_lat_rd_pair | exact GlobalTheory.TwV.adm_seam_lat_rd_pair | (intros; apply GlobalTheory.TwV.adm_seam_lat_rd_pair <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

theorem _root_.GlobalTheory.T.kernelEntries_hyp_of_heckeCharacterConditions : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → (∀ μ k, D.host.g k ∉ Y.Qp μ) → t.TopPinned → t.Hyp := by
  first | exact @GlobalTheory.kerEntTied_hyp | exact GlobalTheory.kerEntTied_hyp | (intros; apply GlobalTheory.kerEntTied_hyp <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.xiL_two_alt : ∀ {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (H : Formalism.L2.Th1.H.Sesq V) (α : V → ℂ) (H₁ : Formalism.L2.Th1.H.Sesq W) (α₁ : W → ℂ) (T : V ≃+ W), (∀ x y, H₁ (T x) (T y) = H x y) → (∀ x, α₁ (T x) = α x) → ∀ (A B Λ : AddSubgroup V) (A₁ B₁ Λ₁ : AddSubgroup W), SplitHyp H α A B Λ → (∀ x, T x ∈ Λ₁ ↔ x ∈ Λ) → (∀ x, T x ∈ A₁ ↔ x ∈ A) → (∀ x, T x ∈ B₁ ↔ x ∈ B) → (∃ S, Formalism.L2.Th1.H.IsReps Λ A S) → (∃ S, Formalism.L2.Th1.H.IsReps B (Λ ⊓ A) S) → (∃ S, Formalism.L2.Th1.H.IsReps Λ B S) → ∀ (vol : ℝ) (θ Φ : W → ℂ), (fun v => θ (T v)) ∈ Formalism.L2.Th1.H.fixedBy H α Λ → InvOn A B (fun v => Φ (T v)) → ∀ z, xiL H₁ α₁ vol (repsOf Λ₁ A₁) (repsOf B₁ (Λ₁ ⊓ A₁)) (repsOf Λ₁ B₁) Φ θ (T z) = xiL H α vol (repsOf Λ A) (repsOf B (Λ ⊓ A)) (repsOf Λ B) (fun v => Φ (T v)) (fun v => θ (T v)) z := by
  first | exact @GlobalTheory.TwU.XiTwo.xiL_two | exact GlobalTheory.TwU.XiTwo.xiL_two | (intros; apply GlobalTheory.TwU.XiTwo.xiL_two <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.char_determinantIdeal_unitary_smul_selfDual : ∀ (D : D7) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ {N : ℕ} (M : SDLat D.host.E N) (e : Matrix (Fin N) (Fin N) D.host.E), e * star e = 1 → χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) (SDLat.smulLat e M.1)) = (∏ τ, TaylorLogMetric.embT D τ e.det)⁻¹ * χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) M.1) := by
  first | exact @GlobalTheory.ChiMove.chi_detId_smulLat | exact GlobalTheory.ChiMove.chi_detId_smulLat | (intros; apply GlobalTheory.ChiMove.chi_detId_smulLat <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct

theorem _root_.GlobalTheory.T.dpstLetter_twist_tensor_equiv : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {L : FinExt l} {a : ℕ} (s : ↥(Dec (F := E) A) →* GL (Fin a) ↥L.1) (m : ↥(Dec (F := E) A) →* GL (Fin 1) ↥L.1) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (Bw.repE L s))] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (Bw.repE L m))] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))))], IsPst P (Bw.repE L s) → IsPst P (Bw.repE L m) → IsPst P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) → ∃ e : WDSpace P ι (Bw.repE L s) ⊗[ℂ] WDSpace P ι (Bw.repE L m) ≃ₗ[ℂ] WDSpace P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))), (∀ (σ : ↥(Weil h)) x, e (TensorProduct.map (wdRho P ι Bw h hj (Bw.repE L s) σ) (wdRho P ι Bw h hj (Bw.repE L m) σ) x) = wdRho P ι Bw h hj (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) σ (e x)) ∧ ∀ x, e (((wdN P ι (Bw.repE L s)).rTensor (WDSpace P ι (Bw.repE L m)) + (wdN P ι (Bw.repE L m)).lTensor (WDSpace P ι (Bw.repE L s)) : Module.End ℂ (WDSpace P ι (Bw.repE L s) ⊗[ℂ] WDSpace P ι (Bw.repE L m))) x) = wdN P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (e x) := by
  first | exact @GlobalTheory.Pst.TwistLetters.wdSpace_twist_equiv | exact GlobalTheory.Pst.TwistLetters.wdSpace_twist_equiv | (intros; apply GlobalTheory.Pst.TwistLetters.wdSpace_twist_equiv <;> assumption)
end
