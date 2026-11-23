module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle058
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle214
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle068
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAdicCompleteTwistedInvariantLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle212
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle096
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle213
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle075
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle190
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle146
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle147
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle098
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierGlOrbitEqFourierEtaleKProd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle100
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle103
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle215
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle155
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle192
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle207
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle007
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
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.isAdicComplete_twistedInvariantLattice : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), IsAdicComplete (Ideal.span {(l : O)}) D.Y' := by
  first | exact @GlobalTheory.BK.BKDat.isAdicComplete_Y' | exact GlobalTheory.BK.BKDat.isAdicComplete_Y' | (intros; apply GlobalTheory.BK.BKDat.isAdicComplete_Y' <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.mixedModelPartialFourierColumn_twice_neg_column : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f : Gl r F → ℂ, IsTest f → WeilMix.ptrB M ψ (WeilMix.ptrB M ψ f) = WeilMix.negB f := by
  first | exact @GlobalTheory.JR.PartialInv.ptrB_ptrB | exact GlobalTheory.JR.PartialInv.ptrB_ptrB | (intros; apply GlobalTheory.JR.PartialInv.ptrB_ptrB <;> assumption)
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem _root_.GlobalTheory.T.hermitianDual_invAlgBaseChangeUnramified_iff : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (L : Submodule K'.O (overExt φ B ψ hψ hσ).A) (x y : B.A), (∀ z ∈ L, (overExt φ B ψ hψ hσ).herm x y z ∈ (algebraMap K'.O K'.E).range) ↔ (∀ z ∈ L, B.herm x y z ∈ (algebraMap K.O K.E).range) := by
  first | exact @GlobalTheory.UnitLemma.Unr.dual_iff | exact GlobalTheory.UnitLemma.Unr.dual_iff | (intros; apply GlobalTheory.UnitLemma.Unr.dual_iff <;> assumption)
end

section

open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker

theorem _root_.GlobalTheory.T.eisenstein_pow_mul_mem_colonIdeal_frobenius : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂) (τ : ZMod a), ∀ α ∈ colon O K (F.mat τ), (X ^ e + (l : O⟦X⟧)) ^ (H + η) * α ∈ colon O K ((F.mat (τ - 1)).map (frob K l)) := by
  first | exact @GlobalTheory.LiftCoker.E_pow_mul_mem_colon_frob | exact GlobalTheory.LiftCoker.E_pow_mul_mem_colon_frob | (intros; apply GlobalTheory.LiftCoker.E_pow_mul_mem_colon_frob <;> assumption)
end

section

open Polynomial

namespace GlobalTheory.UnitLemma.DescentGL

open GlobalTheory.UnitLemma

theorem stab_smul_comm {G X : Type} [CommGroup G] [MulAction G X] (t : G) (x : X) :
    MulAction.stabilizer G (t • x) = MulAction.stabilizer G x := by
  ext h
  simp only [MulAction.mem_stabilizer_iff]
  rw [smul_smul, mul_comm, ← smul_smul, smul_left_cancel_iff]

theorem countGL_prod : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂), ((LinearMap.mulLeft E g₁).charpoly * (LinearMap.mulLeft E g₂).charpoly).Separable → countGL O E ((g₁, g₂) : A₁ × A₂) = (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^ val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) * (countGL O E g₁ * countGL O E g₂) := by
  intro O _ _ _ _ E _ _ _ _ A₁ A₂ _ _ _ _ _ _ _ _ _ _ g₁ g₂ hsep
  have hs₁ := hsep.of_mul_left
  have hs₂ := hsep.of_mul_right
  have hres : resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly ≠ 0 :=
    resultant_ne_zero _ _ hsep.isCoprime
  rw [GlobalTheory.T.stableLatticeOrbitCount_eq_sum_orbits O E (A₁ × A₂) (g₁, g₂), GlobalTheory.T.stableLatticeOrbitCount_eq_sum_orbits O E A₁ g₁, GlobalTheory.T.stableLatticeOrbitCount_eq_sum_orbits O E A₂ g₂]
  haveI hf₁ := GlobalTheory.T.finite_unit_orbits_stable_lattices_separable O E A₁ g₁ hs₁
  haveI hf₂ := GlobalTheory.T.finite_unit_orbits_stable_lattices_separable O E A₂ g₂ hs₂
  obtain ⟨hfinY, hsum⟩ := GlobalTheory.T.stableLatticePair_orbits_finite_and_card_prod O E A₁ A₂ g₁ g₂ hf₁ hf₂
  have hq : (Nat.card (IsLocalRing.ResidueField O) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField O)).ne'
  have hfib := GlobalTheory.T.ncard_fibre_stableLatticePairProjection O E A₁ A₂ g₁ g₂ hres
  have hstab : ∀ y : LatPair O E g₁ g₂, MulAction.stabilizer (A₁ × A₂)ˣ y ≤ intUnits O (A₁ × A₂) ∧
      (MulAction.stabilizer (A₁ × A₂)ˣ y).relIndex (intUnits O (A₁ × A₂)) ≠ 0 := by
    intro y
    obtain ⟨h1, h2⟩ := GlobalTheory.T.stabilizer_stableLatticePair_relIndex_integralUnits O E A₁ A₂ g₁ g₂ y (GlobalTheory.T.stabilizer_stableLattice_le_integralUnitsSubgroup O E A₁ g₁ y.1) (GlobalTheory.T.stabilizer_stableLattice_le_integralUnitsSubgroup O E A₂ g₂ y.2)
    exact ⟨h1, by rw [h2]; exact mul_ne_zero (GlobalTheory.T.stabilizer_relIndex_intUnits_ne_zero' O E A₁ g₁ hs₁ y.1) (GlobalTheory.T.stabilizer_relIndex_intUnits_ne_zero' O E A₂ g₂ hs₂ y.2)⟩
  have hfin : ∀ y, (latProj O E g₁ g₂ ⁻¹' {y}).Finite := by
    intro y
    apply Set.finite_of_ncard_ne_zero
    have h := hfib y
    intro h0
    rw [h0, Nat.cast_zero] at h
    exact zpow_ne_zero _ hq h.symm
  have hCP := GlobalTheory.T.finsum_orbits_counting_principle_finite_fibres (A₁ × A₂)ˣ (stLat O E ((g₁, g₂) : A₁ × A₂)) (LatPair O E g₁ g₂) (intUnits O (A₁ × A₂))
    (latProj O E g₁ g₂) (GlobalTheory.T.stableLatticePair_projection_smul_units O E A₁ A₂ g₁ g₂) hfin hstab hfinY (fun _ => 1) (fun _ _ => rfl)
  simp only [one_mul] at hCP
  rw [hCP]
  have hterm : ∀ o : MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂),
      ((latProj O E g₁ g₂ ⁻¹' {Quotient.out o}).ncard : ℚ) *
        ((MulAction.stabilizer (A₁ × A₂)ˣ (Quotient.out o)).relIndex (intUnits O (A₁ × A₂)) : ℚ) =
      (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^ val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) *
        (((MulAction.stabilizer A₁ˣ (Quotient.out o).1).relIndex (intUnits O A₁) : ℚ) *
          ((MulAction.stabilizer A₂ˣ (Quotient.out o).2).relIndex (intUnits O A₂) : ℚ)) := by
    intro o
    rw [hfib, (GlobalTheory.T.stabilizer_stableLatticePair_relIndex_integralUnits O E A₁ A₂ g₁ g₂ _ (GlobalTheory.T.stabilizer_stableLattice_le_integralUnitsSubgroup O E A₁ g₁ _) (GlobalTheory.T.stabilizer_stableLattice_le_integralUnitsSubgroup O E A₂ g₂ _)).2, Nat.cast_mul]
  have hs := hsum (fun y => ((MulAction.stabilizer A₁ˣ y).relIndex (intUnits O A₁) : ℚ))
    (fun y => ((MulAction.stabilizer A₂ˣ y).relIndex (intUnits O A₂) : ℚ))
    (fun t y => by simp only [stab_smul_comm]) (fun t y => by simp only [stab_smul_comm])
  rw [finsum_congr hterm, ← mul_finsum, hs]

end GlobalTheory.UnitLemma.DescentGL
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.partialFourier_glOrbit_eq_fourier_etaleKProd : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ μK : Measure A.K, SelfDual μK (A.kerK ψ) → ∀ f' : Gl r F → ℂ, IsTest f' → ∀ (g : GL (Fin r) F) (b c : A.K), fourG M ψ f' (act g (LinDesc.pt A hG lam b c)) = A.fourK μK ψ (fun x => f' (act g (LinDesc.pt A hG lam x.1 x.2))) (b, c) := by
  first | exact @GlobalTheory.JR.LinDesc.fourG_act_pt_eq_fourK | exact GlobalTheory.JR.LinDesc.fourG_act_pt_eq_fourK | (intros; apply GlobalTheory.JR.LinDesc.fourG_act_pt_eq_fourK <;> assumption)
end

section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.gaussIntegral_one_mul_gaussIntegral_neg_one_eq_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ Λ : AddSubgroup A.L, IsOpen (Λ : Set A.L) → IsCompact (Λ : Set A.L) → {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1} ⊆ Λ → (∀ y ∈ {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1}, A.psiK ψ ((x : A.K) * A.NL y) = 1) → gaussInt A ψ x μ 1 Λ * gaussInt A ψ x μ (-1) Λ = 1 := by
  first | exact @GlobalTheory.JR.WeilQuad.gaussInt_one_mul_neg_one | exact GlobalTheory.JR.WeilQuad.gaussInt_one_mul_neg_one | (intros; apply GlobalTheory.JR.WeilQuad.gaussInt_one_mul_neg_one <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.selfDualMeasure_etaleHermitian_eq_coords : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (e : A.L), e * e = e → star e = 1 - e → ∀ (ν : Measure A.K) (μ : Measure A.L), SelfDual ν (Hyp.kx A ψ x) → SelfDual μ (A.kerL ψ x) → ∀ h : A.L → ℂ, IsTest h → ∫ y, h y ∂μ = ∫ a, ∫ b, h (Hyp.cc A e (a, b)) ∂ν ∂ν := by
  first | exact @GlobalTheory.JR.Hyp.measure_eq_coords | exact GlobalTheory.JR.Hyp.measure_eq_coords | (intros; apply GlobalTheory.JR.Hyp.measure_eq_coords <;> assumption)
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

theorem _root_.GlobalTheory.T.tendsto_finsum_div_rho_pow_zero : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι) (a : K.O), B.P.Separable → K.Small a → IsFrame B e π S → ∀ (I I' : Finset ι), (∀ i ∈ S, i ∈ I ∨ i ∈ I') → ∀ (N L : ℕ) (D : ℚ) (f : ℕ → Submodule K.O B.A → ℚ), (∀ M ∈ B.Lin, ∃ p, Pos B a e N M p) → (∀ k M, |f k M| ≤ D) → (∀ k, L ≤ k → ∀ M ∈ B.Lin, ∀ p, Pos B a e N M p → f k M ≠ 0 → Win I I' L k p ∧ ¬ Mid S L k p) → Tendsto (fun k : ℕ => ((∑ᶠ M ∈ B.Lin, f k M : ℚ) : ℝ) / (B.rho (algebraMap K.O B.A a ^ k) : ℝ)) atTop (𝓝 0) := by
  first | exact @GlobalTheory.UnitLemma.Desc.tendsto_badWindow_div_rho | exact GlobalTheory.UnitLemma.Desc.tendsto_badWindow_div_rho | (intros; apply GlobalTheory.UnitLemma.Desc.tendsto_badWindow_div_rho <;> assumption)
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

namespace GlobalTheory.PadicH2SeparatedDVR

open GlobalTheory.LocDualInt

theorem discrete_quot {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    (P : Submodule O O) (hP : IsOpen (P : Set O)) : DiscreteTopology (O ⧸ P) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro q
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective P q
  have hq := (Submodule.isOpenQuotientMap_mkQ P).isQuotientMap
  rw [← hq.isOpen_preimage]
  have : (P.mkQ ⁻¹' {Submodule.Quotient.mk x}) = (fun y => y - x) ⁻¹' (P : Set O) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Submodule.mkQ_apply, SetLike.mem_coe]
    exact Submodule.Quotient.eq P
  rw [this]
  exact hP.preimage (continuous_sub_right x)

theorem continuous_mk {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    (P : Submodule O O) : Continuous (Submodule.Quotient.mk : O → O ⧸ P) :=
  (Submodule.isOpenQuotientMap_mkQ P).continuous

theorem d1_mk {O : Type} [CommRing O] {G : Type} [Group G] (ε : G →* Oˣ) (ϖ : O) (n : ℕ)
    (b : G → O) :
    d1 (quotRep (twist ε O) ϖ n) (fun g => Submodule.Quotient.mk (b g)) =
      fun p => Submodule.Quotient.mk (d1 (twist ε O) b p) := by
  funext p
  show quotRep (twist ε O) ϖ n p.1 (Submodule.Quotient.mk (b p.2)) - Submodule.Quotient.mk (b (p.1 * p.2))
      + Submodule.Quotient.mk (b p.1) = Submodule.Quotient.mk ((twist ε O) p.1 (b p.2) - b (p.1 * p.2) + b p.1)
  rw [quotRep_mk, Submodule.Quotient.mk_add, Submodule.Quotient.mk_sub]

theorem separated_dvr_second_cohomology_mem : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O] {G : Type} [Group G] [TopologicalSpace G] (ε : G →* Oˣ) (ϖ : O), (∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O)) → (∀ U ∈ nhds (0 : O), ∃ n : ℕ, ((powSub (M := O) ϖ n : Submodule O O) : Set O) ⊆ U) → (∀ n : ℕ, (Z1 (quotRep (twist ε O) ϖ n) : Set (G → O ⧸ powSub (M := O) ϖ n)).Finite) → ∀ (w : G × G → O), w ∈ Z2 (twist ε O) → (∀ n : ℕ, ∃ b : G → O ⧸ powSub (M := O) ϖ n, Continuous b ∧ ∀ g h : G, d1 (quotRep (twist ε O) ϖ n) b (g, h) = Submodule.Quotient.mk (w (g, h))) → w ∈ B2 (twist ε O) := by
  intro O _ _ _ _ _ _ _ G _ _ ε ϖ hopen hbasis hfin w hw hmod
  haveI hdisc : ∀ n : ℕ, DiscreteTopology (O ⧸ powSub (M := O) ϖ n) := fun n => discrete_quot _ (hopen n)
  let α : ∀ s : ℕ, Set (G → O ⧸ powSub (M := O) ϖ s) := fun s =>
    {β | Continuous β ∧ d1 (quotRep (twist ε O) ϖ s) β = fun p => Submodule.Quotient.mk (w p)}
  have hα : ∀ s, (α s).Finite := by
    intro s
    rcases Set.eq_empty_or_nonempty (α s) with h | ⟨c, hc⟩
    · rw [h]; exact Set.finite_empty
    refine ((hfin s).image (fun f => f + c)).subset ?_
    rintro β ⟨hβ, hd⟩
    refine ⟨β - c, ⟨hβ.sub hc.1, fun g h => ?_⟩, by simp⟩
    have e : d1 (quotRep (twist ε O) ϖ s) (β - c) (g, h) = 0 := by
      rw [map_sub, hd, hc.2, sub_self]; rfl
    have e2 : quotRep (twist ε O) ϖ s g ((β - c) h) - (β - c) (g * h) + (β - c) g = 0 := e
    have : (β - c) g + quotRep (twist ε O) ϖ s g ((β - c) h) - (β - c) (g * h) = 0 := by
      rw [← e2]; abel
    exact (sub_eq_zero.1 this).symm
  let T : ℕ → Set (G → O) := fun r =>
    ⋂ s, ⋂ (_ : s ≤ r), (fun (b : G → O) g =>
      (Submodule.Quotient.mk (b g) : O ⧸ powSub (M := O) ϖ s)) ⁻¹' α s
  have hcl : ∀ r, IsClosed (T r) := fun r =>
    isClosed_iInter fun s => isClosed_iInter fun _ => (hα s).isClosed.preimage
      (continuous_pi fun g => (continuous_mk _).comp (continuous_apply g))
  have hne : ∀ r, (T r).Nonempty := by
    intro r
    obtain ⟨β, hβc, hβ⟩ := hmod r
    refine ⟨fun g => qlift (β g), Set.mem_iInter₂.2 fun s hs => ⟨?_, ?_⟩⟩
    · have e : (fun g => (Submodule.Quotient.mk (qlift (β g)) : O ⧸ powSub (M := O) ϖ s)) =
          fun g => Submodule.factor (powSub_anti (M := O) ϖ hs) (β g) := by
        funext g
        conv_rhs => rw [← mk_qlift (β g)]
        rfl
      show Continuous (fun g => (Submodule.Quotient.mk (qlift (β g)) : O ⧸ powSub (M := O) ϖ s))
      rw [e]
      exact (continuous_factor ϖ hs).comp hβc
    · rw [d1_mk]
      funext p
      have h1 : (Submodule.Quotient.mk (d1 (twist ε O) (fun g => qlift (β g)) p) :
          O ⧸ powSub (M := O) ϖ r) = Submodule.Quotient.mk (w p) := by
        rw [← congrFun (d1_mk ε ϖ r (fun g => qlift (β g))) p]
        have : (fun g => (Submodule.Quotient.mk (qlift (β g)) : O ⧸ powSub (M := O) ϖ r)) = β :=
          funext fun g => mk_qlift _
        rw [this]
        exact hβ p.1 p.2
      rw [Submodule.Quotient.eq] at h1 ⊢
      exact powSub_anti ϖ hs h1
  have hdec : ∀ r, T (r + 1) ⊆ T r := fun r b hb =>
    Set.mem_iInter₂.2 fun s hs => Set.mem_iInter₂.1 hb s (hs.trans (Nat.le_succ r))
  obtain ⟨b, hb⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T hdec hne
    (hcl 0).isCompact hcl
  have hb' : ∀ s, (fun g => (Submodule.Quotient.mk (b g) : O ⧸ powSub (M := O) ϖ s)) ∈ α s :=
    fun s => Set.mem_iInter₂.1 (Set.mem_iInter.1 hb s) s le_rfl
  have hbc : Continuous b := by
    rw [continuous_iff_continuousAt]
    intro x V hV
    have hW : (fun u => u + b x) ⁻¹' V ∈ nhds (0 : O) := by
      apply (continuous_add_const (b x)).continuousAt.preimage_mem_nhds
      simpa using hV
    obtain ⟨n, hn⟩ := hbasis _ hW
    have hloc : {y | (Submodule.Quotient.mk (b y) : O ⧸ powSub (M := O) ϖ n) =
        Submodule.Quotient.mk (b x)} ∈ nhds x :=
      ((isOpen_discrete {(Submodule.Quotient.mk (b x) : O ⧸ powSub (M := O) ϖ n)}).preimage
        (hb' n).1).mem_nhds rfl
    show b ⁻¹' V ∈ nhds x
    refine Filter.mem_of_superset hloc fun y hy => ?_
    have hy' : b y - b x ∈ powSub (M := O) ϖ n := (Submodule.Quotient.eq _).1 hy
    have := hn hy'
    simpa using this
  refine ⟨b, hbc, ?_⟩
  funext p
  have hall : ∀ n : ℕ, d1 (twist ε O) b p - w p ∈ powSub (M := O) ϖ n := by
    intro n
    have := congrFun (hb' n).2 p
    rw [d1_mk] at this
    exact (Submodule.Quotient.eq _).1 this
  by_contra hne'
  have hd : d1 (twist ε O) b p - w p ≠ 0 := sub_ne_zero.2 hne'
  obtain ⟨n, hn⟩ := hbasis _ (isOpen_compl_singleton.mem_nhds (Ne.symm hd))
  exact hn (hall n) rfl

end GlobalTheory.PadicH2SeparatedDVR
end

section

open GlobalTheory.BI GlobalTheory.BrauerZero

noncomputable section
namespace GlobalTheory.BrauerZero

theorem ind_eq_ind_map_subgroupOf {G : Type} [Group G] [Finite G] (E : Subgroup G) (H : Subgroup E)
    (φ : H → ℂ) :
    ind H φ = ind ((H.map E.subtype).subgroupOf E)
      (fun k => φ ((Subgroup.equivMapOfInjective H E.subtype Subtype.val_injective).symm
        ⟨((k : E) : G), k.2⟩)) := by
  classical
  have hS : (H.map E.subtype).subgroupOf E = H := by
    ext y
    simp [Subgroup.mem_subgroupOf]
  have hc : Nat.card ((H.map E.subtype).subgroupOf E) = Nat.card H :=
    Nat.card_congr (MulEquiv.subgroupCongr hS).toEquiv
  funext g
  simp only [ind, hc]
  congr 1
  refine finsum_congr fun x => ?_
  simp only [ext0]
  by_cases hy : x⁻¹ * g * x ∈ H
  · have hy' : x⁻¹ * g * x ∈ (H.map E.subtype).subgroupOf E := by rw [hS]; exact hy
    rw [dite_eq_left hy, dite_eq_left hy']
    congr 1
    apply (Subgroup.equivMapOfInjective H E.subtype Subtype.val_injective).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  · have hy' : x⁻¹ * g * x ∉ (H.map E.subtype).subgroupOf E := by rw [hS]; exact hy
    rw [dite_eq_right hy, dite_eq_right hy']

theorem ind_mem_D0_of_mem_D0 : ∀ {G : Type} [Group G] [Finite G] (E : Subgroup G) (f : E → ℂ),
    f ∈ D0 E → ind E f ∈ D0 G := by
  intro G _ _ E f hf
  induction hf using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨H, χ, rfl⟩ := hx
    have hK : H.map E.subtype ≤ E := by
      rintro _ ⟨y, _, rfl⟩
      exact y.2
    let χ' : H.map E.subtype →* ℂˣ :=
      χ.comp (Subgroup.equivMapOfInjective H E.subtype Subtype.val_injective).symm.toMonoidHom
    rw [ind_sub, ind_eq_ind_map_subgroupOf E H (fun h => (χ h : ℂ)),
      ind_eq_ind_map_subgroupOf E H (fun _ => (1 : ℂ))]
    have h1 : ind E (ind ((H.map E.subtype).subgroupOf E) (fun k =>
        ((χ ((Subgroup.equivMapOfInjective H E.subtype Subtype.val_injective).symm
          ⟨((k : E) : G), k.2⟩) : ℂˣ) : ℂ))) = ind (H.map E.subtype) (fun k => (χ' k : ℂ)) :=
      GlobalTheory.T.inducedClassFunctionFromSubgroup_trans (H.map E.subtype) E hK (fun k => (χ' k : ℂ))
    have h2 := GlobalTheory.T.inducedClassFunctionFromSubgroup_trans (H.map E.subtype) E hK (fun _ => (1 : ℂ))
    rw [h1, h2]
    exact AddSubgroup.subset_closure ⟨H.map E.subtype, χ', rfl⟩
  | zero =>
    have : ind E (0 : E → ℂ) = 0 := (indAddHomComplex E).map_zero
    rw [this]; exact zero_mem _
  | add a b _ _ ha hb =>
    have : ind E (a + b) = ind E a + ind E b := (indAddHomComplex E).map_add a b
    rw [this]; exact add_mem ha hb
  | neg a _ ha =>
    have : ind E (-a) = -ind E a := (indAddHomComplex E).map_neg a
    rw [this]; exact neg_mem ha

end GlobalTheory.BrauerZero
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem setIntegral_eq_mass_mul_avg : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ → ∀ [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → ∀ Φ : G → ℂ, Per Γ Φ → μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤ ∧ IntegrableOn Φ 𝓕 μ ∧ ∫ x in 𝓕, Φ x ∂μ = ((μ 𝓕).toReal : ℂ) * avg Γ Φ := by
  intro G _ _ _ _ _ _ Γ hΓ mG hB μ 𝓕 hμ h𝓕 Φ hΦ
  obtain ⟨hd, K, hK, hcov⟩ := hΓ
  have e := hB.measurable_eq
  subst e
  letI : MeasurableSpace G := borel G
  haveI : Countable Γ := countable_of_discrete_addSubgroup Γ
  have hne : μ 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne μ)
  have hfin : μ 𝓕 ≠ ⊤ := (GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact Γ hK hcov μ h𝓕).ne
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΦ.1.continuousOn
  have hb : ∀ x, ‖Φ x‖ ≤ C := fun x => by
    obtain ⟨γ, hγ, hk⟩ := hcov x
    have := hC _ hk
    rwa [hΦ.2 γ hγ] at this
  have hint : IntegrableOn Φ 𝓕 μ :=
    Measure.integrableOn_of_bounded hfin hΦ.1.aestronglyMeasurable (M := C) (Filter.Eventually.of_forall hb)
  refine ⟨hne, hfin, hint, ?_⟩
  have hex := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact G Γ K hK hcov).1
  have hex' : ∃ p : Measure G × Set G, p.1.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ p.2 p.1 ∧ p.1 p.2 = 1 := by
    obtain ⟨μ₀, F₀, h⟩ := hex
    exact ⟨(μ₀, F₀), h⟩
  have hav : avg Γ Φ = ∫ x in hex'.choose.2, Φ x ∂hex'.choose.1 := by
    simp only [avg]
    rw [dite_eq_left hex']
  rw [hav]
  obtain ⟨hμ₀, hF₀, h1⟩ := hex'.choose_spec
  generalize hex'.choose = p at hμ₀ hF₀ h1 ⊢
  obtain ⟨μ₀, F₀⟩ := p
  simp only at hμ₀ hF₀ h1 ⊢
  obtain ⟨c, hc⟩ : ∃ c : NNReal, μ = c • μ₀ := ⟨_, Measure.isAddLeftInvariant_eq_smul μ μ₀⟩
  have hac : μ ≪ μ₀ := hc ▸ Measure.smul_absolutelyContinuous
  have hF₀' : IsAddFundamentalDomain Γ F₀ μ := hF₀.mono hac
  have e1 : μ 𝓕 = μ F₀ := h𝓕.measure_eq hF₀'
  have e2 : ∫ x in 𝓕, Φ x ∂μ = ∫ x in F₀, Φ x ∂μ :=
    h𝓕.setIntegral_eq hF₀' fun g x => hΦ.2 g g.2 x
  rw [e1, e2, hc, Measure.restrict_smul, integral_smul_nnreal_measure, Measure.smul_apply, h1]
  simp [ENNReal.smul_def, NNReal.smul_def]

end GlobalTheory.CuspGeneric
end
