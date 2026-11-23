module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1684
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2123
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSelfDualPairGaloisConjugateHomLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1898
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1980
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2081
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1911
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle754
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2124
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUniqueAdelicMatrixRealComponentsFinitePart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2125
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle328
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.BrPairBound

theorem pairK_one_re_nonneg {ι : Type} [Fintype ι] {m : ℕ} (w : ι → DomWeight m) (x : VV ℂ w) :
    0 ≤ (pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) x x).re := by
  by_cases h : x = 0
  · simp [h]
  · exact (Complex.lt_def.1 (GlobalTheory.CoefModel.pairK_pos w (G := fun _ => (1 : Matrix (Fin m) (Fin m) ℂ))
      (fun _ => Matrix.PosDef.one) x h)).1.le

theorem inf_bound : ∀ {K ι : Type} [Field K] [CharZero K] [Fintype ι] (φ : K →+* ℂ) {n N : ℕ} (hN : N = n + 1) (Λ : ι → DomWeight N)
    (σ : ι → DomWeight n), (∀ τ, Formalism.L2.Col.Br.Interlace hN (Λ τ) (σ τ)) → (∀ τ, Formalism.L2.Col.Br.SameShift (Λ τ) (σ τ)) →
    ∀ (u : VV K Λ) (v : VV K fun τ => (σ τ).dual),
    0 ≤ (pairK Λ (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (GlobalTheory.CoefModel.mapVV φ Λ u) (GlobalTheory.CoefModel.mapVV φ Λ u)).re ∧
    0 ≤ (pairK (fun τ => (σ τ).dual) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (GlobalTheory.CoefModel.mapVV φ _ v)
      (GlobalTheory.CoefModel.mapVV φ _ v)).re ∧
    ‖φ (GlobalTheory.BrPairF.brPairF σ hN Λ u v)‖ ^ 2 ≤ (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd hN.symm (Λ τ) (σ τ) ^ 2) *
      (pairK Λ (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (GlobalTheory.CoefModel.mapVV φ Λ u) (GlobalTheory.CoefModel.mapVV φ Λ u)).re *
      (pairK (fun τ => (σ τ).dual) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (GlobalTheory.CoefModel.mapVV φ _ v)
        (GlobalTheory.CoefModel.mapVV φ _ v)).re := by
  intro K ι _ _ _ φ n N hN Λ σ hI hS u v
  refine ⟨pairK_one_re_nonneg _ _, pairK_one_re_nonneg _ _, ?_⟩
  rw [GlobalTheory.T.branchingPairing_map_extendScalars_embedding φ hN Λ σ u v, GlobalTheory.BrPairF.brPairF_apply]
  set u' := GlobalTheory.CoefModel.mapVV φ Λ u
  set v' := GlobalTheory.CoefModel.mapVV φ _ v
  have h1 := GlobalTheory.T.bilinearFockPairing_sq_le_hermitianNorms σ (Formalism.L2.Col.Br.brStd hN Λ σ u') ((GlobalTheory.FunObj.funEquiv σ).symm v')
  have h2 := GlobalTheory.T.branchingMap_hermitianNorm_le_prod_bounds hN Λ σ hI hS u'
  have h3 := GlobalTheory.T.hermitianFockNorm_adjugateSubst_symm_le σ v'
  have p2 := pairK_one_re_nonneg σ ((GlobalTheory.FunObj.funEquiv σ).symm v')
  have p3 := pairK_one_re_nonneg Λ u'
  calc _ ≤ _ := h1
    _ ≤ _ := mul_le_mul h2 h3 p2 (mul_nonneg (Finset.prod_nonneg fun _ _ => sq_nonneg _) p3)
    _ = _ := by ring

end GlobalTheory.BrPairBound

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.schwartzBruhat_invariant_supported_eq_smul_vacuum : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om') (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E))
    (θ : 𝓞 D.host.E) (hθ : (θ : D.host.E) + D.sp.cm.sig θ = 1)
    (ι : ((Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) → ℂ)) (hι : Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι)
    (φ₀ : (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) (h0 : φ₀ ∈ GlobalTheory.WeilM.SB _) (hne : φ₀ ≠ 0)
    (hfix : (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) φ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • φ₀)))
    (huniq : ∀ ψ₀ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁), (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) ψ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • ψ₀)) → ∃ c : ℂ, ψ₀ = c • φ₀),
    ∀ g ∈ GlobalTheory.WeilM.SB (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)), (∀ s ∈ GlobalTheory.VacShape.Sa Bs Γ L₁ L₂, ∀ Y, g (Y + s) = g Y) →
      (∀ Y ∉ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂, g Y = 0) → ∃ c : ℂ, g = c • ι φ₀ := by
  first | exact @GlobalTheory.VacUniq.sa_bd_uniq | exact GlobalTheory.VacUniq.sa_bd_uniq | (intros; apply GlobalTheory.VacUniq.sa_bd_uniq <;> assumption)
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.BotPairSmall

theorem cvec_eig : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), ∀ j ∈ GlobalTheory.BotPairSmall.blockJ D 𝔪 o d, ∃ k ∈ intG D a, ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om 1 j (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0) = c • W.Om k 1 (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0) := by
  intro D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho j hj
  have hn : D.host.conj • 𝔪 ≠ ⊥ := GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm
  have hF := GlobalTheory.T.latticeIntertwiner_skewConj_mem_thetaFunctions D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho
  have hmove : ∀ g ∈ intG D a, ∀ g' ∈ intG D d, ∀ y y' : Matrix (Fin d) (Fin a) D.host.E,
      (∀ i l, (((g' : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * y.map (inc D) *
        (((g : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) - y'.map (inc D)) i l ∈ hatId D (D.host.conj • 𝔪)) →
      ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om g g' (Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ y) (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0)) =
        c • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ y') (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) := by
    intro g hg g' hg' y y' hy
    obtain ⟨m, hm0, hl⟩ := W.lift g g' y _ hF
    obtain ⟨z, hz1, hz2⟩ := GlobalTheory.T.exists_global_matrix_approx_two_adelic_moduli D _ hn a d (((g' : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * y.map (inc D) *
        (((g : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) m hm0
    rw [hl z hz1]
    obtain ⟨c1, hc1, e1⟩ := GlobalTheory.T.weil_skewIdealLatticeUnitVector_unimodular_eigen D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho g hg g' hg'
    obtain ⟨c2, hc2, e2⟩ := GlobalTheory.T.heisenbergTranslate_unitVector_congr_unimodular D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho z y' (fun i l => by
      have := sub_mem (hy i l) (hz2 i l)
      convert this using 1
      simp [Matrix.sub_apply, Matrix.map_apply, map_sub])
    refine ⟨c1 * c2, by rw [norm_mul, hc1, hc2, one_mul], ?_⟩
    rw [e1]
    have : ∀ (x : VC D a d) (F : VC D a d → ℂ) (c : ℂ), Wd D (tor0 D ⊤ δ) x (c • F) = c • Wd D (tor0 D ⊤ δ) x F := by
      intro x F c; funext w; simp only [Wd, U, Pi.smul_apply, smul_eq_mul]; ring
    rw [this, e2, smul_smul]

  obtain ⟨k, hk, hjk⟩ := GlobalTheory.T.blockVanishingLevel_unitBlock_mul_inv_stab D 𝔪 hm hcop o a d ho j hj
  obtain ⟨y', -, hy'⟩ := GlobalTheory.T.exists_global_matrix_approx_two_adelic_moduli D _ hn a d ((unitBlock D o a d).map (inc D) *
    (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) 1 one_pos
  have hjJ : j ∈ intG D d := GlobalTheory.BotPairSmall.blockJ_le D 𝔪 o d hj
  obtain ⟨c1, hc1, e1⟩ := hmove 1 (one_mem _) j hjJ (unitBlock D o a d) y' (fun i l => by
    have := add_mem (hjk i l) (hy' i l)
    convert this using 1
    simp [Matrix.sub_apply])
  obtain ⟨c2, hc2, e2⟩ := hmove k hk 1 (one_mem _) (unitBlock D o a d) y' (fun i l => by
    convert hy' i l using 1
    simp [Matrix.sub_apply])
  have hwd : ∀ (x : VC D a d) (F : VC D a d → ℂ) (c : ℂ), Wd D (tor0 D ⊤ δ) x (c • F) = c • Wd D (tor0 D ⊤ δ) x F := by
    intro x F c; funext w; simp only [Wd, U, Pi.smul_apply, smul_eq_mul]; ring
  set s : ℂ := ((Real.sqrt ((Ideal.absNorm (D.host.conj • 𝔪) : ℝ) ^ (a * d)) : ℂ)) with hs_def
  have hs : s ≠ 0 := by
    have h0 : (Ideal.absNorm (D.host.conj • 𝔪) : ℝ) ≠ 0 := by
      exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 hn)
    have : 0 < Real.sqrt ((Ideal.absNorm (D.host.conj • 𝔪) : ℝ) ^ (a * d)) :=
      Real.sqrt_pos.2 (pow_pos (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm h0)) _)
    exact Complex.ofReal_ne_zero.2 this.ne'
  have hcv := GlobalTheory.T.cosetVector_conj_isTheta_some_level D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho
  have hV : Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o a d)) (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) =
      s • GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0 := by
    rw [GlobalTheory.BotPairSmall.cvec, smul_smul, mul_inv_cancel₀ hs, one_smul]
  have hVT : Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o a d)) (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) ∈ TT D (tor0 D ⊤ δ) a d := by
    rw [hV]
    obtain ⟨h1, m, hm0, h2⟩ := hcv
    exact ⟨h1.const_smul s, m, hm0, fun x hx => by rw [hwd, h2 x hx]⟩
  have hc2' : c2 ≠ 0 := by intro h; rw [h, norm_zero] at hc2; exact zero_ne_one hc2
  refine ⟨k, hk, c1 / c2, by rw [norm_div, hc1, hc2, div_one], ?_⟩
  show W.Om 1 j (s⁻¹ • _) = (c1 / c2) • W.Om k 1 (s⁻¹ • _)
  rw [W.smul _ _ _ _ hVT, W.smul _ _ _ _ hVT, e1, e2, smul_smul, smul_smul, smul_smul]
  congr 1
  field_simp

end GlobalTheory.BotPairSmall
end
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

open GlobalTheory.FunObj.StdDatum

namespace GlobalTheory.BotPairSmall.CvFix

theorem om_cvec_of_congOne : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), ∀ k ∈ intG D a, CongOne D (D.host.conj • 𝔪) k → W.Om k 1 (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0) = GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0 := by
  intro D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho k hk hkc
  have hcc : D.host.conj • D.host.conj • 𝔪 = 𝔪 := by
    rw [smul_smul, GlobalTheory.GaloisTwist.conj_mul_conj, one_smul]
  have h := GlobalTheory.T.weil_fixes_cosetVector_congruent_one_mod_ideal D δ t0 hc e0 hv W (D.host.conj • 𝔪) (GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm) ?_ ?_ o (by omega) k hk hkc
  · exact h
  · rw [hcc, Ideal.isCoprime_iff_sup_eq, sup_comm]; exact hcop
  · intro u hu hu1
    apply hcond u hu
    rwa [hcc, mul_comm] at hu1

end GlobalTheory.BotPairSmall.CvFix
end

section

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.FunObj.StdDatum

theorem pres_stdSum : ∀ (D : D7) (δ t0 : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), oddE0 D ⊤ δ t0 a d e0 → a ≤ d → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → IsCoprime 𝔪 D.host.𝔟 → (∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) → ∀ R : Finset (GA D a), (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) → (∀ k ∈ intG D a, W.Om k 1 (stdSum W 𝔪 0 R) = stdSum W 𝔪 0 R) → Pres D ⊤ δ (Ideal.absNorm 𝔪) e0 (stdSum W 𝔪 0 R) := by
  intro D δ t0 hc a d e0 hv had W 𝔪 h𝔪 hco hb _hchar R hR huniq _hfix
  have he : e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) := hv.1
  have hN0 : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h𝔪)
  have hidx := GlobalTheory.T.index_standard_inf_skewThetaLattice_eq_absNorm_pow D δ hc 𝔪 h𝔪 hco a d
  haveI hfin : Finite (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) ⧸
      (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) :=
    AddSubgroup.index_ne_zero_iff_finite.1 (by rw [hidx]; positivity)
  letI : Fintype (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) ⧸
      (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) := Fintype.ofFinite _
  have wsm : ∀ (x : VC D a d) (c : ℂ) (G : VC D a d → ℂ), Wd D (tor0 D ⊤ δ) x (c • G) = c • Wd D (tor0 D ⊤ δ) x G := by
    intro x c G; funext z; simp only [Wd, U, Pi.smul_apply, smul_eq_mul]; ring
  have hr : ∀ i : R, ∃ (c : ℂ) (x : Matrix (Fin d) (Fin a) D.host.E), (∃ m : ℕ, 0 < m ∧ c ^ m = 1) ∧
      pt D (tor0 D ⊤ δ) δ x ∈ La0 D (tor0 D ⊤ δ) a d ∧
      (∀ i' j, (x.map (inc D) - (unitBlock D 0 a d).map (inc D) *
        ((((i : GA D a)⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i' j ∈ hatId D 𝔪) ∧
      W.Om i 1 (cosetV D δ 𝔪 0 a d e0) = ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ •
        (c • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x)
          (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0)) := by
    intro i
    obtain ⟨c, hcm, hce⟩ := GlobalTheory.T.weilOperator_integral_point_vacuum_rootOfUnity_smul D δ hc e0 he W i (hR i i.2)
    obtain ⟨x, hx, hxc, hom⟩ := GlobalTheory.T.weilAction_cosetVector_eq_translate_unitVector D δ hc e0 he W 𝔪 h𝔪 i (hR i i.2)
    refine ⟨c, x, hcm, hx, hxc, ?_⟩
    rw [hom, GlobalTheory.T.weil_integralPoint_skewLatticeUnitVector_same_eigen D δ hc e0 he W 𝔪 h𝔪 i (hR i i.2) c hce, wsm]
  choose c x hcm hx hxc hom using hr
  choose χ hχ using fun i : R => GlobalTheory.T.exists_addChar_thetaCommutatorPhase_skewLattice D δ hc 𝔪 (pt D (tor0 D ⊤ δ) δ (x i)) (hx i)
  have hone : ∀ k : GA D a, CongOne D 𝔪 (k⁻¹ * k) := by
    intro k i' j
    rw [inv_mul_cancel]
    simp
  have hinj : Function.Injective χ := by
    intro i j hij
    have hk : ∀ y ∈ La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d),
        Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (x i)) y =
          Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (x j)) y := by
      intro y hy
      rw [← hχ i ⟨y, hy⟩, ← hχ j ⟨y, hy⟩, hij]
    have h1 := GlobalTheory.T.stabilizer_congruent_of_commutatorPhase_eq D δ hc 𝔪 h𝔪 hco hb had i j (hR i i.2) (hR j j.2) (x i) (x j) (hx i) (hx j) (hxc i) (hxc j) hk
    exact Subtype.ext ((huniq j (hR j j.2)).unique ⟨i.2, h1⟩ ⟨j.2, hone j⟩)
  have hcard : Fintype.card R ≤ Ideal.absNorm 𝔪 ^ (a * d) := by
    rw [Fintype.card_coe]
    refine (GlobalTheory.T.card_principalCongruence_transversal_le_absNorm_pow D 𝔪 h𝔪 a R hR huniq).trans (Nat.pow_le_pow_right hN0 ?_)
    rw [pow_two]; exact Nat.mul_le_mul_left a had
  obtain ⟨rr, hrr, hint, hρ⟩ := GlobalTheory.T.sum_norm_sq_le_of_rootOfUnity_addChar_combination (Ideal.absNorm 𝔪) (a * d) c χ hN0 hcm hinj
    (by rw [← hidx, AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]) hcard
  choose z hz hzN using fun q : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) ⧸
      (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) =>
    GlobalTheory.T.skewIdealLattice_point_rational_normKills D δ hc 𝔪 h𝔪 _ (Quotient.out q).2
  set e := Fintype.equivFin (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) ⧸
      (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)))
  refine ⟨_, fun i => rr (e.symm i), fun i => z (e.symm i), fun i => hzN _, fun i => hint _, fun ρ => ?_, ?_⟩
  · rw [e.symm.sum_comp (fun q => ‖ρ (rr q)‖)]; exact hρ ρ
  funext y
  rw [e.symm.sum_comp (fun q => ((rr q : Qbar) : ℂ) * Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (z q)) e0 y)]
  simp only [stdSum, Finset.sum_apply]
  rw [← Finset.sum_coe_sort R]
  simp only [hom, Pi.smul_apply, smul_eq_mul, GlobalTheory.T.standardLattice_translate_unitVector_vacuum_expansion D δ hc 𝔪 h𝔪 e0 he _ (hx _), hidx,
    finsum_eq_sum_of_fintype, hrr, ← hz]
  have hs : ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ *
      ((Real.sqrt (((Ideal.absNorm 𝔪 ^ (a * d) : ℕ) : ℝ)) : ℂ))⁻¹ = (((Ideal.absNorm 𝔪 : ℂ)) ^ (a * d))⁻¹ := by
    have h1 : (((Ideal.absNorm 𝔪 ^ (a * d) : ℕ) : ℝ)) = (Ideal.absNorm 𝔪 : ℝ) ^ (a * d) := by push_cast; rfl
    rw [h1, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast; rfl
  have hχq : ∀ (i : R) q, χ i q = Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (x i))
      ((Quotient.out q : La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) : VC D a d) := by
    intro i q
    rw [← hχ i, QuotientAddGroup.out_eq']
  simp only [hχq, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
  rw [← hs]; ring

end GlobalTheory.FunObj.StdDatum

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped ContDiff

namespace GlobalTheory.CuspSmooth

theorem conj_list_prod {G : Type} [Group G] (g : G) (l : List G) :
    g⁻¹ * l.prod * g = (l.map fun a => g⁻¹ * a * g).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.prod_cons, List.map_cons]; rw [← ih]; group

theorem mem_Sm_blockEmb : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (ψ : GAd σ J → ℂ), GlobalTheory.StdPar.IsCuspOn σ J Xf Yf S K ψ → ∀ g₀ : GAd σ J,
        (∀ k : GlobalTheory.CuspRep.Kinf E d, g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀ ∈ K) →
        (fun x => ψ (ι x * g₀)) ∈ GlobalTheory.CuspRep.Sm E d := by
  intro F E _ _ _ _ _ _ σ hcm n J hJ r Xf Yf hW K hK S l d h ι hι hd _ _ _ ψ hψ g₀ _ g
  classical
  refine GlobalTheory.T.contDiffOn_invSet_of_smooth_along_prod_exp E d _ {X | ∃ v, ∀ i j, ∀ u, u ≠ v → X i j u = 0} ?_ ?_
  · rw [eq_top_iff]
    intro X _
    have e : X = ∑ v : InfinitePlace E, (Matrix.of fun i j => Pi.single v (X i j v)) := by
      ext i j u
      rw [Matrix.sum_apply, Finset.sum_apply]
      simp [Pi.single_apply]
    rw [e]
    exact Submodule.sum_mem _ fun v _ => Submodule.subset_span ⟨v, fun i j u hu => by simp [Pi.single_apply, hu]⟩
  · intro k X hX y hy
    choose v hv using hX
    have hγ : ∀ i, IsRealLine σ J (fun t : ℝ => g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (GlobalTheory.CuspRep.expGLi d (t • X i))) * g₀) :=
      fun i => GlobalTheory.EisCont.CentreFinite.isRealLine_conj hcm
        (GlobalTheory.T.isRealLine_blockEmbedding_exp_infinitePlace F E σ hcm n J hJ r Xf Yf hW l d h ι hι (v i) (X i) (hv i)) g₀
    have hs := hψ.1.smooth k _ hγ (ι (g * GlobalTheory.CuspRep.infGL E d hy.unit) * g₀)
    convert hs using 2 with t
    set P : GL (Fin d) (GlobalTheory.CuspRep.Cinf E) := (List.ofFn fun i => GlobalTheory.CuspRep.expGLi d (t i • X i)).prod
    have hP : (P : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E)) =
        (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod := by
      simp only [P]
      rw [← Units.coeHom_apply, map_list_prod, List.map_ofFn]
      rfl
    have hU : GlobalTheory.CuspRep.toL (Matrix.of y * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod) =
        GlobalTheory.CuspRep.toL (hy.unit * P).val := by
      rw [Units.val_mul, hP]
      congr 2
    rw [hU, GlobalTheory.CuspRep.chart_val]
    have e3 : (List.ofFn fun i => g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (GlobalTheory.CuspRep.expGLi d (t i • X i))) * g₀) =
        ((List.ofFn fun i => GlobalTheory.CuspRep.expGLi d (t i • X i)).map (ι.comp (GlobalTheory.CuspRep.infGL E d))).map
          (fun a => g₀⁻¹ * a * g₀) := by
      simp [List.map_ofFn, Function.comp_def]
    rw [e3, ← conj_list_prod, ← map_list_prod]
    simp only [P, map_mul, MonoidHom.comp_apply, mul_assoc, mul_inv_cancel_left]

end GlobalTheory.CuspSmooth
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormExact

theorem reads_smul_const_unique : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (G : VC D a d → ℂ) (f : WO S T → ℂ) (c c' : ℂ), G ≠ 0 →
  Reads ψ θ hS hT cc δ r (c • G) f → Reads ψ θ hS hT cc δ r (c' • G) f → c = c' := by
  intro D ψ θ S T a d hS hT cc δ r hs G f c c' hG h1 h2
  subst hS hT
  obtain ⟨Y, hY⟩ : ∃ Y, G Y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hG (funext hc)
  have hδ : δ ≠ 0 := delta_ne_zero hs.crv
  have hr : r ≠ 0 := IsScale.ne_zero hs.crv.1.1 hs.scale
  have hm : ∀ τ, δ * embT D τ r ≠ 0 := fun τ => mul_ne_zero hδ ((map_ne_zero _).2 hr)
  obtain ⟨x, ⟨hx, hx0⟩, -⟩ := GlobalTheory.StdUnn.exists_unique_of_comp_finPart D θ hs.inf T.rank S.rank
    (fun τ => Matrix.of fun i j => Y τ i j / (δ * embT D τ r)) 0
  replace hx0 : x.map (finPart D) = 0 := by rw [hx0]; exact Matrix.map_zero _ (map_zero _)
  have hxY : coordY θ rfl rfl δ r x = Y := by
    funext τ i j
    simp only [coordY, Fin.cast_eq_self, hx, Matrix.of_apply]
    have hE : embT D τ r ≠ 0 := (map_ne_zero _).2 hr
    field_simp [hm τ, hE, hδ]
  have e1 := h1.2 x hx0
  have e2 := h2.2 x hx0
  rw [hxY] at e1 e2
  rw [e1, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul] at e2
  have he := Complex.exp_ne_zero (-((Real.pi : ℂ) / 2) * Hf D (tor0 D cc δ) Y Y)
  have := mul_left_cancel₀ he e2
  exact mul_right_cancel₀ hY this

end GlobalTheory.NormExact
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.heisenbergFinitePoint_reads_classicalTranslation : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ G f, Reads ψ θ hS hT cc δ r G f → ∀ z : Matrix (Fin d) (Fin a) D.host.E,
    Reads ψ θ hS hT cc δ r (U D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) G) (heisO ψ S T (finPt hS hT r z) f) := by
  first | exact @GlobalTheory.NormExact.heisO_finPt_reads | exact GlobalTheory.NormExact.heisO_finPt_reads | (intros; apply GlobalTheory.NormExact.heisO_finPt_reads <;> assumption)
end
