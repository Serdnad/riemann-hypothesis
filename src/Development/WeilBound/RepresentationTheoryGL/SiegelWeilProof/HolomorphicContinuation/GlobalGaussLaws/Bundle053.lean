module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle020
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle418
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle398
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle309
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle317
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle260
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousStandardUnitaryChartAndSymm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle313
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle366
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle525
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle236
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle245
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle284
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle515
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerFunctionLinearThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle264
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle496
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle501
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle507
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle268
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IterPLin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle520
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerThetaEqSchwartzBruhat
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm

@[expose] public section

section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace PositivityTheory.Rg.Sw.Glob.RhoH




theorem annS_stable : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
    ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
    ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω → ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l →
    ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) →
    ∀ (τ : D.what₂.Tau) (Φ : schwartzA θ V.rank n), (∀ X, annS V l s θ τ X Φ.1 = 0) →
    ∀ k ∈ K D n, ∀ X, annS V l s θ τ X (ω k Φ).1 = 0 := by
  intro D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hl s hs τ Φ hann k hk X
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, hlam, hψeq, hchart, hdat, htr⟩ :=
    GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨lam', hlam', -, l', hl', habs⟩ := GlobalTheory.StdUnn.shift_char_realPar D ψ₀ hstd θ hθ μ' hsk
  have hll : lam' = lam := (algebraMap D.host.F D.host.E).injective (hlam'.trans hlam.symm)
  subst hll
  have hl'' : HasRealPar ψ θ l' := hψeq ▸ hl'
  have hleq : l = l' := GlobalTheory.T.archimedean_parameters_addChar_unique D ψ θ hθ l l' hl hl''
  subst hleq
  obtain ⟨hschS, hsurj, -⟩ := GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D ψ₀ hstd θ hθ A V μ 𝓕 hμ
  obtain ⟨f, hf, hfΦ⟩ := hsurj Φ.1 Φ.2
  obtain ⟨s', hstd', hcomm⟩ := GlobalTheory.T.exists_standardCartanInvolution_commute_compact D A μ' hsk κ hchart θ hθ

  have hkill1 : ∀ Z : Matrix (Fin V.rank) (Fin A.rank) ℂ,
      annih (heisO ψ₀ (dblSp A) V) θ τ (cplxO (s' τ) (s τ)) (Z * (dblDec A).qX.map (tauE D τ)) f = 0 := by
    intro Z
    apply GlobalTheory.T.doubledPairThetaFunction_eq_zero_of_schrodinger_eq_zero D ψ₀ hstd A V μ 𝓕 hμ _ (GlobalTheory.StdUnn.isThetaFunO_annih_of_std (A := A) (B := V) (ν := μ) (𝓨 := 𝓕) hstd hθ hμ τ _ _ hf)
    rw [GlobalTheory.T.annihilationOperator_schroedingerFunctions_doubledPair D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs f hf τ Z, hfΦ]
    exact hann Z
  have hkill : ∀ Y : Matrix (Fin V.rank) (Fin (dblSp A).rank) ℂ,
      annih (heisO ψ₀ (dblSp A) V) θ τ (cplxO (s' τ) (s τ)) Y f = 0 := by
    intro Y
    obtain ⟨Z, Z', c, hdec⟩ := GlobalTheory.T.annihilationOperator_doubledHermitianSpace_decomp D ψ₀ hstd θ hθ A V μ' hsk s' s hstd' hs τ Y
    rw [hdec f hf, hkill1, hkill1, smul_zero, add_zero]

  have hkk : κ (κ.symm k) ∈ K D A.rank := by
    rw [show κ (κ.symm k) = k from κ.apply_symm_apply k]
    exact hk
  have hS : ∀ τ', s' τ' * compAt θ τ' (Formalism.L2.Theta.mt (dblSp A) (κ.symm k)) =
      compAt θ τ' (Formalism.L2.Theta.mt (dblSp A) (κ.symm k)) * s' τ' := fun τ' => (hcomm (κ.symm k) hkk τ').symm
  have hm1 : ∀ τ', compAt θ τ' (Formalism.L2.Theta.mt V 1) = 1 := by
    intro τ'
    simp [Formalism.L2.Theta.mt, compAt, Matrix.map_one]
  have hT : ∀ τ', s τ' * compAt θ τ' (Formalism.L2.Theta.mt V 1) = compAt θ τ' (Formalism.L2.Theta.mt V 1) * s τ' := by
    intro τ'
    rw [hm1, Matrix.mul_one, Matrix.one_mul]
  let X' : Matrix (Fin V.rank) (Fin A.rank) ℂ := X
  set Y0 : Matrix (Fin V.rank) (Fin (dblSp A).rank) ℂ :=
    (X' * (dblDec A).qX.map (tauE D τ)) * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (κ.symm k)) with hY0
  have hmove := (GlobalTheory.FockMove.om_foldr hdat hθ (κ.symm k) 1 hS hT hf [(τ, Y0)]).2
  simp only [List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil] at hmove
  rw [hkill Y0, map_zero, hm1, Matrix.one_mul, hY0, Matrix.mul_assoc,
    GlobalTheory.WeilVacMove.compAt_mt_mul_inv, Matrix.mul_one] at hmove

  have htk := htr (κ.symm k) f hf Φ hfΦ.symm
  rw [show κ (κ.symm k) = k from κ.apply_symm_apply k] at htk
  have hth' : IsThetaFunO ψ₀ (dblSp A) V (omh (κ.symm k, 1) f) := hdat.om_pres _ f hf
  have e := GlobalTheory.T.annihilationOperator_schroedingerFunctions_doubledPair D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs _ hth' τ X'
  rw [← hmove] at e
  have hs0 : sch ψ₀ A V μ 𝓕 (0 : WO (dblSp A) V → ℂ) = 0 := by
    have := (GlobalTheory.StdUnn.sch_linear D ψ₀ hstd A V μ 𝓕 hμ f f hf hf 0).2.2.2
    rw [zero_smul, zero_smul] at this
    exact this
  rw [hs0] at e
  show annS V l s θ τ X ((ω k) Φ).1 = 0
  rw [show ((ω k) Φ).1 = sch ψ₀ A V μ 𝓕 (omh (κ.symm k, 1) f) from htk]
  exact e.symm

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace PositivityTheory.Rg.Sw.Glob.RhoH




theorem orbit_cont : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
    ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
    ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω → ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l →
    ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) →
    ∀ Φ : schwartzA θ V.rank n, Φ.1 ∈ fockA θ V n l s → ∀ Λ : schwartzA θ V.rank n →ₗ[ℂ] ℂ,
      ContinuousOn (fun g : G D n => Λ (ω g Φ)) (K D n : Set (G D n)) := by
  intro D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ Λ
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, hlam, hψeq, hchart, hdat, htr⟩ :=
    GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨lam', hlam', -, l', hl', habs⟩ := GlobalTheory.StdUnn.shift_char_realPar D ψ₀ hstd θ hθ μ' hsk
  have hll : lam' = lam := (algebraMap D.host.F D.host.E).injective (hlam'.trans hlam.symm)
  subst hll
  have hl'' : HasRealPar ψ θ l' := hψeq ▸ hl'
  have hleq : l = l' := GlobalTheory.T.archimedean_parameters_addChar_unique D ψ θ hθ l l' hl hl''
  subst hleq
  obtain ⟨hschS, hsurj, -⟩ := GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D ψ₀ hstd θ hθ A V μ 𝓕 hμ
  obtain ⟨f, hf, hfΦ⟩ := hsurj Φ.1 Φ.2
  obtain ⟨s', hstd', hcomm⟩ := GlobalTheory.T.exists_standardCartanInvolution_commute_compact D A μ' hsk κ hchart θ hθ
  have hfock : IsFockVec ψ₀ θ (dblSp A) V s' s f :=
    GlobalTheory.T.isFockVector_of_schrodinger_mem_fockSpace D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs f hf (hfΦ ▸ hΦ)
  have hcont := GlobalTheory.StdUnn.chart_continuous D A μ' hsk κ hchart
  let K' : Subgroup (GA D (dblSp A)) := (K D A.rank).comap κ.toMonoidHom
  have hK' : IsCompact (K' : Set (GA D (dblSp A))) := by
    have h1 : (K' : Set (GA D (dblSp A))) = κ.symm '' (K D A.rank : Set (G D A.rank)) := by
      ext g
      simp only [K', Subgroup.coe_comap, Set.mem_preimage, SetLike.mem_coe, MulEquiv.coe_toMonoidHom]
      constructor
      · intro hg; exact ⟨κ g, hg, κ.symm_apply_apply g⟩
      · rintro ⟨k, hk, rfl⟩; simpa using hk
    rw [h1]
    exact (GlobalTheory.StdUnn.HeightExists.isCompact_K).image hcont.2
  have hkf : GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.IsKFinVec omh K' f :=
    GlobalTheory.Core.Rk.IP.isKFinVec_of_isFockVec D ψ₀ θ (dblSp A) V 1 χ⁻¹ omh s' s hdat hθ
      (GlobalTheory.CartStd.isCartanInv_stdInv D A μ' hsk s' hstd') hs K' hK' (fun k hk τ => hcomm k hk τ) f hfock
  let Vf : Submodule ℂ (WO (dblSp A) V → ℂ) := Submodule.span ℂ {g | ∃ k ∈ K', g = omh (k, 1) f}
  have : FiniteDimensional ℂ Vf := hkf
  have hVth : ∀ v ∈ Vf, IsThetaFunO ψ₀ (dblSp A) V v := by
    intro v hv
    have hle : Vf ≤ Formalism.IndefR.Eqv.thetaSubO ψ₀ (dblSp A) V := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k, -, rfl⟩
      exact hdat.om_pres _ f hf
    exact hle hv

  let Sv : Vf →ₗ[ℂ] schwartzA θ V.rank n :=
    { toFun := fun v => ⟨sch ψ₀ A V μ 𝓕 v.1, hschS v.1 (hVth v.1 v.2)⟩
      map_add' := fun v w => Subtype.ext
        (GlobalTheory.StdUnn.sch_linear D ψ₀ hstd A V μ 𝓕 hμ v.1 w.1 (hVth v.1 v.2) (hVth w.1 w.2) 1).2.2.1
      map_smul' := fun c v => Subtype.ext
        (GlobalTheory.StdUnn.sch_linear D ψ₀ hstd A V μ 𝓕 hμ v.1 v.1 (hVth v.1 v.2) (hVth v.1 v.2) c).2.2.2 }
  have hΛc : Continuous (Λ ∘ₗ Sv) := LinearMap.continuous_of_finiteDimensional _

  have hmemK : ∀ g : G D A.rank, g ∈ K D A.rank → κ.symm g ∈ K' := by
    intro g hg
    show κ (κ.symm g) ∈ K D A.rank
    rw [κ.apply_symm_apply]
    exact hg
  let o : Set.Elem (((K D n : Subgroup (G D n)) : Set (G D n))) → Vf := fun g =>
    ⟨omh (κ.symm g.1, 1) f, Submodule.subset_span ⟨κ.symm g.1, hmemK g.1 g.2, rfl⟩⟩
  have hκs : Continuous (fun g : G D n => κ.symm g) := hcont.2
  have hval : Continuous (fun g : Set.Elem (((K D n : Subgroup (G D n)) : Set (G D n))) => (g.1 : G D n)) :=
    continuous_subtype_val
  have ho : Continuous o := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_pi fun w => ?_
    exact (hdat.om_cont f hf w).comp ((hκs.comp hval).prodMk continuous_const)
  have heq : ∀ g : Set.Elem (((K D n : Subgroup (G D n)) : Set (G D n))), Λ (ω g.1 Φ) = (Λ ∘ₗ Sv) (o g) := by
    intro g
    simp only [LinearMap.coe_comp, Function.comp_apply]
    congr 1
    apply Subtype.ext
    have := htr (κ.symm g.1) f hf Φ hfΦ.symm
    rw [show κ (κ.symm g.1) = g.1 from κ.apply_symm_apply g.1] at this
    exact this
  rw [continuousOn_iff_continuous_domRestrict]
  have : (Set.domRestrict (K D n : Set (G D n)) fun g => Λ (ω g Φ)) = (Λ ∘ₗ Sv) ∘ o := funext heq
  rw [this]
  exact hΛc.comp ho

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace PositivityTheory.Rg.Sw.Glob.RhoH

theorem fock_stable : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
    ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
    ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω → ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l →
    ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) →
    ∀ Φ : schwartzA θ V.rank n, Φ.1 ∈ fockA θ V n l s → ∀ k ∈ K D n, (ω k Φ).1 ∈ fockA θ V n l s := by
  intro D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ k hk
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, hlam, hψeq, hchart, hdat, htr⟩ :=
    GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨lam', hlam', -, l', hl', habs⟩ := GlobalTheory.StdUnn.shift_char_realPar D ψ₀ hstd θ hθ μ' hsk
  have hll : lam' = lam := (algebraMap D.host.F D.host.E).injective (hlam'.trans hlam.symm)
  subst hll
  have hl'' : HasRealPar ψ θ l' := hψeq ▸ hl'
  have hleq : l = l' := GlobalTheory.T.archimedean_parameters_addChar_unique D ψ θ hθ l l' hl hl''
  subst hleq
  obtain ⟨-, hsurj, -⟩ := GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D ψ₀ hstd θ hθ A V μ 𝓕 hμ
  obtain ⟨f, hf, hfΦ⟩ := hsurj Φ.1 Φ.2
  obtain ⟨s', hstd', hcomm⟩ := GlobalTheory.T.exists_standardCartanInvolution_commute_compact D A μ' hsk κ hchart θ hθ
  have hfock : IsFockVec ψ₀ θ (dblSp A) V s' s f :=
    GlobalTheory.T.isFockVector_of_schrodinger_mem_fockSpace D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs f hf (hfΦ ▸ hΦ)
  have hkk : κ (κ.symm k) ∈ K D A.rank := by
    rw [show κ (κ.symm k) = k from κ.apply_symm_apply k]
    exact hk
  have hfock' : IsFockVec ψ₀ θ (dblSp A) V s' s (omh (κ.symm k, 1) f) :=
    GlobalTheory.T.isPolynomialFockThetaVector_weilOperator_cartan D ψ₀ (dblSp A) V 1 χ⁻¹ omh hdat θ hθ s' s' s (κ.symm k)
      (fun τ => (hcomm (κ.symm k) hkk τ).symm) f hfock
  have hmem := GlobalTheory.T.schroedingerFunction_fockVector_polynomial_gaussian D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs _ hfock'
  have := htr (κ.symm k) f hf Φ hfΦ.symm
  rw [show κ (κ.symm k) = k from κ.apply_symm_apply k] at this
  exact this.symm ▸ hmem

theorem l_ne_zero : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
    ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
    ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω → ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l →
    ∀ τ, l τ ≠ 0 := by
  intro D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hl τ h0
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, hlam, hψeq, hchart, hdat, htr⟩ :=
    GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨lam', hlam', -, l', hl', habs⟩ := GlobalTheory.StdUnn.shift_char_realPar D ψ₀ hstd θ hθ μ' hsk
  have hll : lam' = lam := (algebraMap D.host.F D.host.E).injective (hlam'.trans hlam.symm)
  subst hll
  have hl'' : HasRealPar ψ θ l' := hψeq ▸ hl'
  have hleq : l = l' := GlobalTheory.T.archimedean_parameters_addChar_unique D ψ θ hθ l l' hl hl''
  subst hleq
  have h := habs τ
  rw [h0, abs_zero] at h
  have hx : ‖tauE D τ D.host.xi0‖ ≠ 0 :=
    norm_ne_zero_iff.2 ((map_ne_zero (tauE D τ)).2 (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D))
  have hm : ‖tauE D τ μ'‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero (tauE D τ)).2 hsk.1)
  exact (div_ne_zero hx hm) h.symm

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GCommH

variable {D : D7} {n : ℕ}

theorem gComm {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {χ : (AE D)ˣ →* Circle}
    (hχ : IsHeckeChar D χ) (hη : ResEta D χ V.rank) {θ : InfFam D} (hθ : IsInfFam θ) {μ : Measure (Mx D V.rank n)}
    {𝓕 : Set (Mx D V.rank n)} (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕)
    {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    (Φ Φh : schwartzA θ V.rank n) (h : GA D V) (hΦh : ∀ x, Φh.1 x = Φ.1 (mt V h ⬝ x)) (g : G D n) (x : Mx D V.rank n) :
    (ω g Φh).1 x = (ω g Φ).1 (mt V h ⬝ x) := by
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hs0, hsk, _, _, hκ, hW, hT⟩ := GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hψ χ hχ hη θ hθ μ 𝓕 hμ ω hω
  obtain ⟨f, hf, hfΦ⟩ := (GlobalTheory.SchSchwartzAll.schSchwartz D ψ₀ hs0 θ hθ A V μ 𝓕 hμ).2.1 Φ.1 Φ.2
  have hlaw := fun F (hF : IsThetaFunO ψ₀ (dblSp A) V F) => (GlobalTheory.T.schrodingerFunction_unitary_levi_radical_actions D ψ₀ A V χ⁻¹ omh hW μ 𝓕 hμ F hF).1
  have hf1 : IsThetaFunO ψ₀ (dblSp A) V (omh (1, h⁻¹) f) := hW.om_pres _ f hf
  have hΦh' : Φh.1 = sch ψ₀ A V μ 𝓕 (omh (1, h⁻¹) f) := by
    funext y
    rw [hΦh, hlaw f hf h⁻¹ y, inv_inv, hfΦ]
    rfl
  have key : ∀ g0 : GA D (dblSp A), (ω (κ g0) Φh).1 x = (ω (κ g0) Φ).1 (mt V h ⬝ x) := by
    intro g0
    have hc : omh (g0, 1) (omh (1, h⁻¹) f) = omh (1, h⁻¹) (omh (g0, 1) f) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk,
        one_mul, mul_one, one_mul, mul_one]
    have hg1 : IsThetaFunO ψ₀ (dblSp A) V (omh (g0, 1) f) := hW.om_pres _ f hf
    calc (ω (κ g0) Φh).1 x = sch ψ₀ A V μ 𝓕 (omh (g0, 1) (omh (1, h⁻¹) f)) x := congrFun (hT g0 _ hf1 Φh hΦh') x
      _ = sch ψ₀ A V μ 𝓕 (omh (1, h⁻¹) (omh (g0, 1) f)) x := by rw [hc]
      _ = sch ψ₀ A V μ 𝓕 (omh (g0, 1) f) (mt V h⁻¹⁻¹ ⬝ x) := hlaw _ hg1 h⁻¹ x
      _ = sch ψ₀ A V μ 𝓕 (omh (g0, 1) f) (mt V h ⬝ x) := by rw [inv_inv]
      _ = (ω (κ g0) Φ).1 (mt V h ⬝ x) := (congrFun (hT g0 f hf Φ hfΦ.symm) _).symm
  have e : κ (κ.symm g) = g := κ.apply_symm_apply g
  have k := key (κ.symm g)
  rw [e] at k
  exact k

end PositivityTheory.Rg.Sw.Glob.GCommH
end
end
