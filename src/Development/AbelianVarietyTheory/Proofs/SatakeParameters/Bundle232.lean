module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle101
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle011
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryMatrixOfOrthonormalLocalBasisAllPlaces
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle020
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle156
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle085
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle019
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle224
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle218
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle157
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle225
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle018
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.L2.DIV
open scoped TensorProduct

theorem _root_.GlobalTheory.T.openCharacter_eq_one_of_integralUnit_one_at_ramified : ∀ (F E L : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field L] (σ : L →+* ℂ) (ξ : Chr F E L), ξ ∈ openChr F E L → (ratId F E).range ≤ ξ.ker → ∀ x ∈ intU F E, (∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) ∈ Qprime ξ → GlobalTheory.Mem.Col2.afIso F E (x : AfE F E) P = 1) → ξ x = 1 := by
  first | exact @GlobalTheory.UnitCut.map_eq_one_of_one_at_ramified | exact GlobalTheory.UnitCut.map_eq_one_of_one_at_ramified | (intros; apply GlobalTheory.UnitCut.map_eq_one_of_one_at_ramified <;> assumption)
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.TripleGal GlobalTheory.Pst
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CharAboveRead

open scoped TensorProduct

theorem exists_isInduced_of {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (τ : E →+* Om l) (w : HeightOneSpectrum (𝓞 E)) (hw : w ∈ placesOver E l)
    (hτ : ∀ x : 𝓞 E, ‖τ (x : E)‖ < 1 ↔ x ∈ w.asIdeal) (A : ValuationSubring Ω) (hA : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O)
    (hj : Induces Bw) : ∃ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥Bw.LL.1, IsInduced Bw τ τ' := by
  let jE : E →+* Om l := Bw.j.comp (algebraMap E Ω)
  have hjE : ∀ x : 𝓞 E, ‖jE (x : E)‖ < 1 ↔ x ∈ w.asIdeal := fun x =>
    (hj.valuation_lt_one_iff _).symm.trans (hA x)
  have iso := GlobalTheory.GalFirstClause.Emb.norm_eq_of_samePlace τ jE w hw hτ hjE
  have hker : ∀ t ∈ RingHom.ker (GlobalTheory.GalFirstClause.Emb.tensLift jE), GlobalTheory.GalFirstClause.Emb.tensLift τ t = 0 := fun t ht =>
    norm_eq_zero.1 (le_antisymm ((GlobalTheory.GalFirstClause.Emb.norm_tensLift_le jE τ (fun x => (iso x).symm) t).trans
      (by rw [RingHom.mem_ker.1 ht, norm_zero])) (norm_nonneg _))
  have hrange : (GlobalTheory.GalFirstClause.Emb.tensLift jE).range ≤ Bw.Kw.1.toSubalgebra := by
    rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul a y =>
      change GlobalTheory.GalFirstClause.Emb.tensLift jE (a ⊗ₜ y) ∈ _
      rw [GlobalTheory.GalFirstClause.Emb.tensLift_tmul]
      exact mul_mem (Bw.Kw.1.algebraMap_mem a) (Bw.j_E y)
    | add t₁ t₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  have hfin : FiniteDimensional ℚ_[l] (Subalgebra.toSubmodule (GlobalTheory.GalFirstClause.Emb.tensLift jE).range) := by
    haveI : FiniteDimensional ℚ_[l] (Subalgebra.toSubmodule Bw.Kw.1.toSubalgebra) := Bw.Kw.2
    exact Submodule.finiteDimensional_of_le (Subalgebra.toSubmodule.monotone hrange)
  have hclosed : IsClosed ((GlobalTheory.GalFirstClause.Emb.tensLift jE).range : Set (Om l)) :=
    Submodule.closed_of_finiteDimensional (Subalgebra.toSubmodule (GlobalTheory.GalFirstClause.Emb.tensLift jE).range)
  have hle : Bw.Kw.1.toSubalgebra ≤ (GlobalTheory.GalFirstClause.Emb.tensLift jE).range := by
    intro y hy
    refine closure_minimal ?_ hclosed (Bw.j_dense hy)
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by
      change GlobalTheory.GalFirstClause.Emb.tensLift jE (1 ⊗ₜ x) = jE x; rw [GlobalTheory.GalFirstClause.Emb.tensLift_tmul, map_one, one_mul]⟩
  let σ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l :=
    ((Ideal.Quotient.liftₐ (RingHom.ker (GlobalTheory.GalFirstClause.Emb.tensLift jE)) (GlobalTheory.GalFirstClause.Emb.tensLift τ) hker).comp
      (Ideal.quotientKerEquivRange (GlobalTheory.GalFirstClause.Emb.tensLift jE)).symm.toAlgHom).comp (Subalgebra.inclusion hle)
  refine ⟨σ.codRestrict Bw.LL.1.toSubalgebra (fun y => Bw.LL_split σ y), fun x => ?_⟩
  have key : (Ideal.quotientKerEquivRange (GlobalTheory.GalFirstClause.Emb.tensLift jE)).symm
      (Subalgebra.inclusion hle ⟨jE x, Bw.j_E x⟩) = Ideal.Quotient.mk _ (1 ⊗ₜ x) := by
    rw [AlgEquiv.symm_apply_eq]
    apply Subtype.ext
    change jE x = GlobalTheory.GalFirstClause.Emb.tensLift jE (1 ⊗ₜ x)
    rw [GlobalTheory.GalFirstClause.Emb.tensLift_tmul, map_one, one_mul]
  change τ x = σ ⟨jE x, Bw.j_E x⟩
  change τ x = Ideal.Quotient.liftₐ _ (GlobalTheory.GalFirstClause.Emb.tensLift τ) hker
    ((Ideal.quotientKerEquivRange (GlobalTheory.GalFirstClause.Emb.tensLift jE)).symm (Subalgebra.inclusion hle ⟨jE x, Bw.j_E x⟩))
  rw [key, Ideal.Quotient.liftₐ_apply]
  change τ x = GlobalTheory.GalFirstClause.Emb.tensLift τ (1 ⊗ₜ x)
  rw [GlobalTheory.GalFirstClause.Emb.tensLift_tmul, map_one, one_mul]

theorem continuous_rankOneOperator {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    (μ : Γ →* Kˣ) (hμ : Continuous μ) : Continuous fun g => ((rk1 μ g : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K) := by
  have hv : Continuous fun g => ((μ g : Kˣ) : K) := Units.continuous_val.comp hμ
  refine continuous_pi fun i => continuous_pi fun k => ?_
  have e : ∀ g, ((rk1 μ g : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K) i k = ((μ g : Kˣ) : K) := fun g => by
    fin_cases i; fin_cases k; simp [rk1]
  simp only [e]
  exact hv

end GlobalTheory.CharAboveRead

namespace GlobalTheory.CharAboveRead



theorem deRham_and_jumps_rankOne_lAdic_character : ∀ (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (μ : G D.host.E D.nd.Om →* (Qbar l)ˣ), Continuous μ → ∀ (J : (D.host.E →+* Qbar l) → Multiset ℤ)
    (w : HeightOneSpectrum (𝓞 D.host.E)), w ∈ placesOver D.host.E l →
    (∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), Induces Bw →
      IsdRAt (D.loc l) Bw ((rk1 μ).comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) ∧
      ∀ (τ : D.host.E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        IsJumpsAt (D.loc l) Bw ((rk1 μ).comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) τ (J τ)) →
    W.IsdRW l ι (rk1 μ) w ∧ ∀ τ : D.host.E →+* Qbar l, (∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal) →
      W.jumpsW l ι (rk1 μ) τ = J τ := by
  intro D T W l _ ι μ hμ J w hw H
  have hcont : Continuous fun g => (rk1 μ g : Matrix (Fin 1) (Fin 1) (Qbar l)) := continuous_rankOneOperator μ hμ
  obtain ⟨K, ρ, hρc, hρ⟩ := GlobalTheory.GalFirstClause.finextRep l D.host.E D.nd.Om 1 (rk1 μ) hcont
  obtain ⟨j, L0, hj, hLL⟩ := GlobalTheory.PlaceBridge.exists_locBridge l D.host.E D.nd.Om w (D.nd.plOm.1 w) hw (D.nd.plOm.2 w)
  obtain ⟨Bw, hBj, hBLL, -, hBto⟩ := hLL L0 le_rfl
  have hind : Induces Bw := fun x => by rw [hBj]; exact hj x
  let LL' : FinExt l := supExt K Bw.LL
  have hK : K.1 ≤ LL'.1 := le_sup_left
  have hB : Bw.LL.1 ≤ LL'.1 := le_sup_right
  let ρ' : G D.host.E D.nd.Om →* GL (Fin 1) ↥LL'.1 := mapRep (IntermediateField.inclusion hK).toRingHom ρ
  have hρ' : mapRep (algebraMap ↥LL'.1 (Om l)) ρ' = rk1 μ := by
    rw [← hρ]
    ext g i k
    rfl
  have hρ'c : Continuous fun g => (ρ' g : Matrix (Fin 1) (Fin 1) ↥LL'.1) := by
    have hi : Continuous (IntermediateField.inclusion hK) :=
      continuous_induced_rng.2 continuous_subtype_val
    exact hρc.matrix_map hi
  have hmodel : IsModel Bw (resDec D.nd.plOm.1 (rk1 μ) w) LL'
      (ρ'.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) :=
    ⟨hB, by rw [← hρ']; rfl⟩
  let φ : ↥(OL L0) →+* Qbar l := L0.1.val.toRingHom.comp (OL L0).val.toRingHom
  have hφ : ∀ x, φ x = ((Bw.toLL x : ↥Bw.LL.1) : Om l) := fun x => (hBto x).symm
  have hcl := (W.loc l ι w hw _ Bw hind φ hφ).2 LL' hB 1 ρ' hρ'c
  rw [hρ'] at hcl
  have hab := H _ Bw hind
  have hdR : Bw.IsdRE (D.loc l) LL' (ρ'.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) :=
    (hmodel.isdRAt_iff (D.loc l)).1 hab.1
  refine ⟨hcl.2.1.2 hdR, fun τ hτ => ?_⟩
  obtain ⟨τ₀, hτ₀⟩ := exists_isInduced_of τ w hw hτ _ (D.nd.plOm.2 w) _ Bw hind
  let τ'' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1 := (IntermediateField.inclusion hB).comp τ₀
  have hτ'' : IsInduced Bw τ τ'' := fun x => hτ₀ x
  have hJ := hab.2 τ LL' τ'' hτ''
  ext n
  apply Nat.cast_injective (R := ℤ)
  rw [(hcl.2.2.2 τ τ'' hτ'').2 hdR n, IsJumpsAt.count_eq (D.loc l) hmodel hτ'' hJ n]

end GlobalTheory.CharAboveRead
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.unitaryMatrix_of_orthonormal_localBasis_allPlaces : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → 5 ≤ p → IsResidueClassZero D p → hP D p = 0 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p (YYl D L L') b → TaylorLogMetric.Orthonormal D b → ∃ γ : Fin r → (OrbitPlaces.Pl D × Fin N × Fin N') → MaximalUnramifiedExtension p, (∀ i j, ‖γ i j‖ ≤ 1 ∧ σ (σ (γ i j)) = γ i j) ∧ (∀ j j', ∑ i, σ (γ i j) * γ i j' = if j = j' then 1 else 0) ∧ ∀ (c : ℂ_[p]) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) (stdSer D lam (fun _ => 1) P P' G) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) = MvPowerSeries.subst (fun i => (∑ j, MvPowerSeries.C (γ i j : ℂ_[p]) * MvPowerSeries.X j : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) (thOrth D lam c b G) := by
  first | exact @GlobalTheory.KerStd.unitary_of_orthonormal | exact GlobalTheory.KerStd.unitary_of_orthonormal | (intros; apply GlobalTheory.KerStd.unitary_of_orthonormal <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.orthonormal_local_bases_carry_witt_lattices : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (fd : FData X D) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), (∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) * a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) → (∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 → TaylorLogMetric.admitted D _ _ (fd.kerN j La) (fd.kerN (j + 1) La') ∧ ∀ v, locSp (X.G.P.W v) (ρ v) (fd.kerN j La) = (X.latAt v j La.2).map (((fd.frM j La v).mulVecLin).restrictScalars (X.G.P.W v)) ∧ locSp (X.G.P.W v) (ρ v) (fd.kerN (j + 1) La') = (X.latAt v (j + 1) La'.2).map (((fd.frM (j + 1) La' v).mulVecLin).restrictScalars (X.G.P.W v))) → Lt.FrameLatMapLt X fd.frM hfin D (fun j La _ => fd.kerN j La) (fun j _ La' => fd.kerN (j + 1) La') ρ := by
  first | exact @GlobalTheory.TwV.frameLatMapLt_of_ties | exact GlobalTheory.TwV.frameLatMapLt_of_ties | (intros; apply GlobalTheory.TwV.frameLatMapLt_of_ties <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevOp

variable {D : D7} {V : HSp D} {P : Pl D.host.E}

theorem mem_hyp {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {k : GA D V} :
    k ∈ hyp V P ↔ k ∈ KsphC V ∅ ∧ SuppF V f k := by
  refine ⟨fun ⟨h, e', f', h', hs⟩ => ⟨h, ?_⟩, fun h => ⟨h.1, e, f, hP, h.2⟩⟩
  obtain ⟨-, rfl⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP).2.2.2.1 e' f' h'
  exact hs

theorem comm_of_supp {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {a b : GA D V} (ha : SuppF V f a)
    (hb : SuppF V (1 - f) b) : Commute a b :=
  have h1 := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP
  ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).1 f h1.1 h1.2.1).2.2 (1 - f) a b (by rw [mul_sub, mul_one, h1.1, sub_self]) ha hb

theorem full_iff {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {J : Set (GA D V)} {χ : GA D V → ℂ}
    (hJ : ∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅)) (hχ : ∀ g ∈ J, SuppF V f g → χ g = 1)
    (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (d : List ℤ) (B : Finset (GA D V)) :
    Hecke₂ V J χ SF P d B ↔ OffS D SF P ∧ SphOp V P d B := by
  have hK : {k | k ∈ J ∧ SuppF V f k} = {k | k ∈ KsphC V ∅ ∧ SuppF V f k} :=
    Set.ext fun k => and_congr_left fun hk => hJ k hk
  constructor
  · rintro ⟨e', f', ϖ, α, hS, hP', h1, h2, hd, -, -, hα, hD, hR, hc⟩
    obtain ⟨rfl, rfl⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP).2.2.2.1 e' f' hP'
    exact ⟨hS, _, _, ϖ, α, fun v hv => absurd hv (Finset.notMem_empty v), hP, h1, h2, hd, fun _ _ => Iff.rfl,
      fun _ _ _ => rfl, hα, hD, hR, hK ▸ hc⟩
  · rintro ⟨hS, e', f', ϖ, α, -, hP', h1, h2, hd, -, -, hα, hD, hR, hc⟩
    obtain ⟨rfl, rfl⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP).2.2.2.1 e' f' hP'
    exact ⟨_, _, ϖ, α, hS, hP, h1, h2, hd, hJ, hχ, hα, hD, hR, hK ▸ hc⟩

theorem offS_empty : OffS D ∅ P := fun v hv => absurd hv (Finset.notMem_empty v)

theorem rep_cases (d : List ℤ) : GlobalTheory.Hk3.rep V P d = ∅ ∨ SphOp V P d (GlobalTheory.Hk3.rep V P d) := by
  unfold GlobalTheory.Hk3.rep
  split_ifs with h
  · exact Or.inr h.choose_spec
  · exact Or.inl rfl

theorem heckeLin_translate {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {J : Subgroup (GA D V)}
    (hJ : ∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅)) {d : List ℤ} {R : Finset (GA D V)} (hR : SphOp V P d R)
    {F : GA D V → ℂ} (hF : ∀ k ∈ hyp V P, ∀ h, F (h * k) = F h) {k₁ k₂ : GA D V} (hk₁ : k₁ ∈ J)
    (s₁ : SuppF V f k₁) (s₂ : SuppF V (1 - f) k₂) (h : GA D V) :
    heckeLin V R F (h * (k₁ * k₂)) = heckeLin V R (fun x => F (x * (k₁ * k₂))) h := by
  obtain ⟨L, hL⟩ := GlobalTheory.HeckeKeep.exists_loc V f
  have hJ' : ∀ g, SuppF V f g → (g ∈ ((J ⊓ L : Subgroup (GA D V)) : Set (GA D V)) ↔ g ∈ KsphC V ∅) := fun g hg =>
    ⟨fun h => (hJ g hg).1 h.1, fun h => ⟨(hJ g hg).2 h, (hL g).2 hg⟩⟩
  have hop := (full_iff hP (χ := fun _ => 1) hJ' (fun _ _ _ => rfl) ∅ d R).2 ⟨offS_empty, hR⟩
  have hsupp : ∀ γ ∈ R, SuppF V f γ := by
    obtain ⟨e', f', ϖ, α, -, hP', -, -, -, -, -, -, -, hR, -⟩ := hR
    obtain ⟨-, rfl⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP).2.2.2.1 e' f' hP'
    exact hR
  have key := GlobalTheory.SphericalOps.level_heckeLin (J := J ⊓ L) (F := fun x => F (x * k₂)) (fun _ _ _ _ => (one_mul _).symm)
    (fun e' f' _ hP' k hk => by
      obtain ⟨-, rfl⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP).2.2.2.1 e' f' hP'
      exact ⟨k, hk, 1, one_mem _, (hL k).1 hk.2, GlobalTheory.HeckeKeep.suppF_one _, (mul_one k).symm⟩) hop
    (fun k hk g => by
      have s := (hL k).1 hk.2
      show F (g * k * k₂) = 1 * F (g * k₂)
      rw [one_mul, mul_assoc, (comm_of_supp hP s s₂).eq, ← mul_assoc,
        hF k ((mem_hyp hP).2 ⟨(hJ k s).1 hk.1, s⟩)]) k₁ ⟨hk₁, (hL _).2 s₁⟩ h
  rw [one_mul, heckeLin_apply, heckeLin_apply] at key
  rw [heckeLin_apply, heckeLin_apply]
  refine Eq.trans (Finset.sum_congr rfl fun a ha => ?_) (key.trans (Finset.sum_congr rfl fun a _ => ?_))
  · rw [← mul_assoc, mul_assoc _ k₂, ← (comm_of_supp hP (hsupp a ha) s₂).eq, ← mul_assoc]
  · show _ = F (h * a * (k₁ * k₂))
    rw [(comm_of_supp hP s₁ s₂).eq, ← mul_assoc, hF k₁ ((mem_hyp hP).2 ⟨(hJ _ s₁).1 hk₁, s₁⟩)]

theorem hk_apply (c : List ℤ →₀ ℂ) (F : GA D V → ℂ) (h : GA D V) :
    hk V P c F h = ∑ d ∈ c.support, c d * heckeLin V (GlobalTheory.Hk3.rep V P d) F h := by
  unfold hk Finsupp.sum
  rw [LinearMap.sum_apply, Finset.sum_apply]
  rfl

theorem hk_translate {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {J : Subgroup (GA D V)}
    (hJ : ∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅)) (c : List ℤ →₀ ℂ)
    {F : GA D V → ℂ} (hF : ∀ k ∈ hyp V P, ∀ h, F (h * k) = F h) {k₁ k₂ : GA D V} (hk₁ : k₁ ∈ J)
    (s₁ : SuppF V f k₁) (s₂ : SuppF V (1 - f) k₂) (h : GA D V) :
    hk V P c F (h * (k₁ * k₂)) = hk V P c (fun x => F (x * (k₁ * k₂))) h := by
  rw [hk_apply, hk_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  congr 1
  rcases rep_cases (V := V) (P := P) d with h0 | h0
  · rw [h0, heckeLin_apply, heckeLin_apply, Finset.sum_empty, Finset.sum_empty]
  · exact heckeLin_translate hP hJ h0 hF hk₁ s₁ s₂ h

theorem postOn_hk {S : D.what₂.Tau → SPar} (M : DSModel V S) (c : List ℤ →₀ ℂ) (U : MMap M) :
    postOn M (hk V P c) U = ∑ d ∈ c.support, c d • heckeOn M (GlobalTheory.Hk3.rep V P d) U := by
  ext v g
  rw [postOn_apply, hk_apply, MultilinearMap.sum_apply, Finset.sum_apply]
  rfl

theorem level_operators : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank), IsBaseFrame V β Λ N → ∀ P : Pl D.host.E, ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → (∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) → (∀ k ∈ hyp V P, k ∈ levG V β L ∧ levChi V β L k = 1) ∧ (∀ SF d B, Hecke₂ V (levS V β L) (levChi V β L) SF P d B ↔ OffS D SF P ∧ SphOp V P d B) ∧ (∀ c Φ, HasType V β L Φ → HasType V β L (hk V P c Φ)) ∧ (∀ c (g0 : G0 L.Pg L.r) Φ, (∀ k ∈ hyp V P, ∀ h, Φ (h * k) = Φ h) → actG0 V β L g0 (hk V P c Φ) = hk V P c (actG0 V β L g0 Φ)) ∧ ∀ (S : D.what₂.Tau → SPar) (θ : InfFam D) (M : DSModel V S) c, IsInfFam θ → ∀ U ∈ Mult θ M (levS V β L) (levChi V β L), postOn M (hk V P c) U ∈ Mult θ M (levS V β L) (levChi V β L) := by
  intro D V β Λ N L hB P hN hPP
  obtain ⟨e, f, hP⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.1 P
  obtain ⟨hJ, hχ, hs⟩ := (GlobalTheory.LevSplit.lev_split V β Λ N L hB).2 P e f hP hN hPP
  obtain ⟨hJ', -, hs'⟩ := (GlobalTheory.LevSplit.lev_split V β Λ N (flagL L) hB).2 P e f hP hN hPP
  have h1 : ∀ k ∈ hyp V P, k ∈ levG V β L ∧ levChi V β L k = 1 := fun k hk => by
    obtain ⟨a, b⟩ := (mem_hyp hP).1 hk
    exact ⟨(hJ k b).2 a, hχ k ((hJ k b).2 a) b⟩
  have hinv : ∀ Φ, HasType V β L Φ → ∀ k ∈ hyp V P, ∀ h, Φ (h * k) = Φ h := fun Φ hΦ k hk h => by
    rw [hΦ k (h1 k hk).1, (h1 k hk).2, one_mul]
  refine ⟨h1, full_iff hP hJ hχ, fun c Φ hΦ κ hκ h => ?_, fun c g0 Φ hΦ => ?_, fun S θ M c hθ U hU => ?_⟩
  · obtain ⟨k₁, hk₁, k₂, -, s₁, s₂, rfl⟩ := hs κ hκ
    have e1 : (fun x => Φ (x * (k₁ * k₂))) = levChi V β L (k₁ * k₂) • Φ := funext fun x => hΦ _ hκ x
    rw [hk_translate hP hJ c (hinv Φ hΦ) hk₁ s₁ s₂, e1, LinearMap.map_smul]
    rfl
  · unfold actG0
    split_ifs with hex
    · have hl := hex.choose_spec
      generalize hex.choose = κ at hl ⊢
      have hκ : κ ∈ levG V β (flagL L) := ⟨hl.1, hl.2.1, Subgroup.mem_top _⟩
      obtain ⟨k₁, hk₁, k₂, -, s₁, s₂, rfl⟩ := hs' κ hκ
      have e1 : (fun x => (levChi V β (flagL L) (k₁ * k₂))⁻¹ * Φ (x * (k₁ * k₂))) =
        (levChi V β (flagL L) (k₁ * k₂))⁻¹ • fun x => Φ (x * (k₁ * k₂)) := rfl
      rw [e1, LinearMap.map_smul]
      funext h
      rw [hk_translate hP hJ' c hΦ hk₁ s₁ s₂]
      rfl
    · rw [LinearMap.map_zero]
  · rw [postOn_hk]
    refine sum_mem fun d _ => Submodule.smul_mem _ _ ?_
    rcases rep_cases (V := V) (P := P) d with h0 | h0
    · have : heckeOn M (GlobalTheory.Hk3.rep V P d) U = 0 := by
        ext v g
        rw [h0, heckeOn, postOn_apply, heckeLin_apply, Finset.sum_empty]
        rfl
      rw [this]
      exact zero_mem _
    · have hop := (full_iff hP (J := levS V β L) hJ hχ ∅ d _).2 ⟨offS_empty, h0⟩
      rw [GlobalTheory.MultMem.mem_mult_iff] at hU ⊢
      refine GlobalTheory.SphericalOps.isMultMap_heckeOn hU (fun k hk => ?_) fun v κ hκ h => ?_
      · obtain ⟨_, _, _, _, -, -, -, -, -, -, -, -, -, -, hc⟩ := hop
        exact (hc.1 k hk).1
      · obtain ⟨k₁, hk₁, k₂, -, s₁, s₂, rfl⟩ := hs κ hκ
        have e1 : (fun x => U v (x * (k₁ * k₂))) = levChi V β L (k₁ * k₂) • U v := funext fun x => hU.lev v _ hκ x
        rw [heckeLin_translate hP hJ h0 (hinv _ (hU.lev v)) hk₁ s₁ s₂, e1, LinearMap.map_smul]
        rfl

end GlobalTheory.LevOp

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.inertHeckeOperators_rows_rational_selfAdjoint_labels : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → ∀ t, ∀ (I : Type) (pl : I → Pl D.host.E) (ty : I → List ℤ) (op : I → Module.End D.what₂.LL (A.MtildeCSD t).Forms) (inR : I → Prop), (∀ i, inR i → Good R t (pl i) ∧ _root_.Formalism.DivisionValues.conjPl (pl i) = pl i ∧ (ty i).Pairwise (fun a b => b ≤ a)) → Bridge.HeckeTie (Bridge.ratF D.sp.X') (R.B.R t).pres op inR (fun i => _root_.GlobalTheory.Hk3.IsLabElt D.sp.X' (pl i) (ty i)) (fun i => _root_.GlobalTheory.Hk3.IsLocElt D.sp.X' (pl i)) → ∀ i, inR i → (∀ a b, LinearMap.toMatrix (A.MtildeCSD t).basis (A.MtildeCSD t).basis (op i) a b ∈ cmMax D.what₂.LL) ∧ (∀ f g : (A.MtildeCSD t).Forms, (A.MtildeCSD t).csum ((op i f : (A.MtildeCSD t).Forms) : (A.MtildeCSD t).Cl → (A.MtildeCSD t).V) (g : (A.MtildeCSD t).Cl → (A.MtildeCSD t).V) = (A.MtildeCSD t).csum (f : (A.MtildeCSD t).Cl → (A.MtildeCSD t).V) ((op i g : (A.MtildeCSD t).Forms) : (A.MtildeCSD t).Cl → (A.MtildeCSD t).V)) ∧ IsLab D.sp.X' (pl i) (ty i) ∧ ∀ h, IsOpsX R t h → ∀ f, R.jX t (op i f) = h (pl i) (Finsupp.single (ty i) 1) (R.jX t f) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF hM t I pl ty op inR hin HT i hi
  obtain ⟨hgood, hconj, hpw⟩ := hin i hi
  have hd := GlobalTheory.InertRows.ext_op_eq D.sp.X' R.βX R.ΛX (R.datXt t) hL.βX
    R.cX.coef.ρ D.what₂.embLL (A.MtildeCSD t) (R.B.R t).pres pl ty op inR HT i hi hgood hpw
  have hint : ∀ h, IsOpsX R t h → ∀ f,
      R.jX t (op i f) = h (pl i) (Finsupp.single (ty i) 1) (R.jX t f) := by
    intro h hh f
    refine (hM.HX t).1 ((hM.jX t _).trans ((hd.2 f).trans ?_))
    exact (congrArg (hkF D.sp.X' (pl i) (Finsupp.single (ty i) 1)) (hM.jX t f).symm).trans
      (hh (pl i) hgood _ _).symm
  refine ⟨?_, ?_, hd.1, hint⟩
  · obtain ⟨_, _, _, hT⟩ := hF.tie
    open GlobalTheory.HeckeRational in
    exact (dcOp_matrix_mem_cmMax D.sp.X' R.cX.coef R.βX (R.datXt t) (R.B.R t).pres
      (hT.coefR t) hT.mapR
      (fun g a b => (GlobalTheory.coefAction_repr_mem_subfield (labLL D) _ _ labLL_mem_cmMax g a b).1)
      (HT.hA i) (op i) (HT.op_eq i hi)).2
  · intro f g
    obtain ⟨h, hh, hnormal⟩ := GlobalTheory.DefiniteOps.side D.sp.X' R.βX R.ΛX (R.datXt t)
      hL.βX (Good R t) (fun _ hp => hp) R.cX.coef.ρ (fun γ => hM.cX.2.1 γ)
      (R.B.R t).pres.y (R.B.R t).pres.reps
      (fun c => Finite.of_equiv _ ((R.B.R t).pres.stabI c).toEquiv) (R.HX t) (hM.HX t)
    have hdual : dualLab (ty i) = ty i :=
      ((GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing D.sp.X' (pl i) (ty i)).1 hd.1).2.2 hconj
    have hadj := (hnormal.2 (pl i) hgood (Finsupp.single (ty i) 1)).trans
      (congrArg (h (pl i)) (GlobalTheory.InertRows.dualC_single hdual))
    exact GlobalTheory.InertRows.csum_selfAdj (Bridge.ratF D.sp.X') (A.MtildeCSD t)
      D.what₂.embLL R.cX.coef.ρ _ _ (R.B.R t).pres (R.HX t) (hM.HX t)
      (R.jX t) (hM.jX t) (op i) _ hadj (hint h hh) f g
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_unramifiedLocalPair_of_inertWeilDatum : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E), IsWeilDatumO ψ S T χS χT om → _root_.Formalism.DivisionValues.conjPl P = P → VacFix ψ om P → ∀ e, IsPrimeIdem P e e → ∃ (ϖ : P.adicCompletion D.host.E) (σ : P.adicCompletion D.host.E →+* P.adicCompletion D.host.E) (q : ℕ) (δ : P.adicCompletion D.host.E) (JS : GL (Fin S.rank) (P.adicCompletion D.host.E)) (JT : GL (Fin T.rank) (P.adicCompletion D.host.E)) (ψ' : AddChar (P.adicCompletion D.host.E) ℂ) (M : Submodule ℂ (WO S T → ℂ)) (ρ : Matrix (Fin T.rank) (Fin S.rank) (P.adicCompletion D.host.E) → Module.End ℂ M) (ω : Formalism.UG.UJ σ (JS : Matrix (Fin S.rank) (Fin S.rank) (P.adicCompletion D.host.E)) × Formalism.UG.UJ σ (JT : Matrix (Fin T.rank) (Fin T.rank) (P.adicCompletion D.host.E)) →* Module.End ℂ M) (ιS : Formalism.UG.UJ σ (JS : Matrix (Fin S.rank) (Fin S.rank) (P.adicCompletion D.host.E)) →* GA D S) (ιT : Formalism.UG.UJ σ (JT : Matrix (Fin T.rank) (Fin T.rank) (P.adicCompletion D.host.E)) →* GA D T), LocPair ϖ σ q δ JS JT ψ' ρ ω ∧ (∀ g, g ∈ ιS.range ↔ SuppF S e g) ∧ (∀ g, g ∈ ιT.range ↔ SuppF T e g) ∧ (∀ g, ιS g ∈ hyp S P ↔ (g : GL (Fin S.rank) (P.adicCompletion D.host.E)) ∈ Formalism.UG.GLint (Fin S.rank) (Formalism.UG.intL _)) ∧ (∀ g, ιT g ∈ hyp T P ↔ (g : GL (Fin T.rank) (P.adicCompletion D.host.E)) ∈ Formalism.UG.GLint (Fin T.rank) (Formalism.UG.intL _)) ∧ (∀ g h (m : M), ((ω (g, h) m : M) : WO S T → ℂ) = om (ιS g, ιT h) m) ∧ (∀ f, IsVacAt ψ S T P f → f ∈ M) ∧ ∀ m : M, LocVac ρ m ↔ IsVacAt ψ S T P m := by
  first | exact @GlobalTheory.InertLoc.exists_locPair | exact GlobalTheory.InertLoc.exists_locPair | (intros; apply GlobalTheory.InertLoc.exists_locPair <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.inertHeckeOperators_lifts_rational_selfAdjoint_labels : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → ∀ j t, ∀ (I : Type) (pl : I → Pl D.host.E) (ty : I → List ℤ) (op : I → Module.End D.what₂.LL (A.MtCSD j t).Forms) (inR : I → Prop), (∀ i, inR i → Good R t (pl i) ∧ _root_.Formalism.DivisionValues.conjPl (pl i) = pl i ∧ (ty i).Pairwise (fun a b => b ≤ a)) → Bridge.HeckeTie (Bridge.ratF (Vc D j)) (R.B.L j t).pres op inR (fun i => _root_.GlobalTheory.Hk3.IsLabElt (Vc D j) (pl i) (ty i)) (fun i => _root_.GlobalTheory.Hk3.IsLocElt (Vc D j) (pl i)) → ∀ i, inR i → (∀ a b, LinearMap.toMatrix (A.MtCSD j t).basis (A.MtCSD j t).basis (op i) a b ∈ cmMax D.what₂.LL) ∧ (∀ f g : (A.MtCSD j t).Forms, (A.MtCSD j t).csum ((op i f : (A.MtCSD j t).Forms) : (A.MtCSD j t).Cl → (A.MtCSD j t).V) (g : (A.MtCSD j t).Cl → (A.MtCSD j t).V) = (A.MtCSD j t).csum (f : (A.MtCSD j t).Cl → (A.MtCSD j t).V) ((op i g : (A.MtCSD j t).Forms) : (A.MtCSD j t).Cl → (A.MtCSD j t).V)) ∧ IsLab (Vc D j) (pl i) (ty i) ∧ ∀ h, IsOpsV R j t h → ∀ f, R.jV j t (op i f) = h (pl i) (Finsupp.single (ty i) 1) (R.jV j t f) := by
  first | exact @GlobalTheory.InertHeckeLift.inert_lifts | exact GlobalTheory.InertHeckeLift.inert_lifts | (intros; apply GlobalTheory.InertHeckeLift.inert_lifts <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem phiC_eq_of_realises : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (a : D.what₂.Tau → ℤ) (Q : MvPolynomial (GL3Theta.FrV D n) ℂ) (R : XR (X.Pj i) ℂ), Realises X D pos i h a Q R → phiC X D pos i h a Q = R := by
  intro p _ X D pos i n h a Q R hR
  have hmem : Q ∈ (relPhi X D pos i h a).map (LinearMap.fst ℂ _ _) :=
    Submodule.mem_map.2 ⟨(Q, R), hR, rfl⟩
  have hsel : Realises X D pos i h a Q (phiC X D pos i h a Q) := selOf_mem (relPhi X D pos i h a) Q hmem
  have hz : phiC X D pos i h a Q - R = 0 := by
    apply GlobalTheory.T.evalModelPolynomialOnStdFrames_injective X D pos i h
    intro f
    rw [map_sub, Pi.sub_apply, hsel f, hR f, sub_self]
  exact sub_eq_zero.1 hz

end GlobalTheory.TwV.DelA
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.evalStdFrames_eq_detPower_mul_blockValue : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (R : XR (X.Pj i) ℂ) (f : Fr1 D n), ev1 X D pos i h R f = (∏ τ, (zT X D pos f.1 τ).det ^ eT X D pos i τ) * valZ X D pos i h R f.1 := by
  first | exact @GlobalTheory.TwV.DelA.ev1_eq_prod_det_pow_mul_valZ | exact GlobalTheory.TwV.DelA.ev1_eq_prod_det_pow_mul_valZ | (intros; apply GlobalTheory.TwV.DelA.ev1_eq_prod_det_pow_mul_valZ <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.realPlaceBlockWeightLastEntry_consecutive_levels : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (j : ℕ) (τ : D.what₂.Tau), (eT X D pos j τ = if IsOddPos (pos.symm τ).2 then wT X D pos j τ - cT1 X D pos j τ else X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 (NN X.G.P.m X.t j) - wT X D pos j τ) ∧ (eT X D pos (j + 1) τ = if IsOddPos (pos.symm τ).2 then wT X D pos j τ - cT1 X D pos j τ else -wT X D pos j τ) := by
  first | exact @GlobalTheory.TwV.DelA.eT_last_pair | exact GlobalTheory.TwV.DelA.eT_last_pair | (intros; apply GlobalTheory.TwV.DelA.eT_last_pair <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.operatorMatrices_at_complexPoint : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), evD X D pos ι hN d f' (yMat X Kc j v s).det = ι (zT X D pos f' (pos ⟨v, s⟩)).det ∧ (¬ IsOddPos s → (dyMat X Kc j v s).map (evD X D pos ι hN d f') = ((dfr X D hN d f' (pos ⟨v, s⟩)).map ι).submatrix (Fin.cast hN.1.symm) (Fin.cast hN.1.symm)) ∧ (IsOddPos s → (YtMat X Kc j v s).map (evD X D pos ι hN d f') = ι (zT X D pos f' (pos ⟨v, s⟩)).det • (((dfr X D hN d f' (pos ⟨v, s⟩)).transpose.submatrix Fin.rev id).map ι).submatrix (Fin.cast hN.1.symm) (Fin.cast hN.1.symm)) := by
  first | exact @GlobalTheory.TwV.DelA.evD_blockMats | exact GlobalTheory.TwV.DelA.evD_blockMats | (intros; apply GlobalTheory.TwV.DelA.evD_blockMats <;> assumption)
end
