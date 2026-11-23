module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle291
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusFixedMatrixUnitsOfLatticeBasis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRestrictionLatticeColumns
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle292
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceMirabolicDetAverageEqHarishChandraRestricti
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle308
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle328
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle329
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle314
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousGaloisLatticeMatrixIntegral
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.ProperSpace
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle337
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_frobeniusFixed_matrix_units_of_lattice_basis : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) → ∀ (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x y : Fin r × n), (∀ m, UnitM P (U m)) → ∀ (A₀ : GL (n × Fin r) P.R.B), (∀ i j, P.φB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) = (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) → ∀ W₀ : GL (n × Fin r) P.R.BdR, UnitM P W₀ → (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) = (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) * Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) * (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) → ∀ a : n → n → P.R.B, Submodule.span ℚ_[l] (Set.range fun jk : n × Fin r => ω jk.2 • a jk.1) = Submodule.span ℚ_[l] (Set.range (colv P ω A₀)) → ∃ A : GL n P.R.B, (∀ i j, P.φB^[r] ((A : Matrix n n P.R.B) i j) = (A : Matrix n n P.R.B) i j) ∧ ∀ m : Fin r, ∃ W : GL n P.R.BdR, UnitM P W ∧ (A : Matrix n n P.R.B).map (ev P m) = (U m : Matrix n n P.R.BdR) * Matrix.diagonal (fun j => tz P (eps x y (m, j))) * (W : Matrix n n P.R.BdR) := by
  first | exact @GlobalTheory.PMon.Extract.extract | exact GlobalTheory.PMon.Extract.extract | (intros; apply GlobalTheory.PMon.Extract.extract <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.mem_span_restrictionLattice_columns : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ), 0 < r → ∀ (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) → ∀ (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x y : Fin r × n) (A₀ : GL (n × Fin r) P.R.B), (∀ i j, P.φB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) = (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) → ∀ W₀ : GL (n × Fin r) P.R.BdR, UnitM P W₀ → (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) = (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) * Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) * (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) → ∀ a : n → P.R.B, LatC P U x y a → a ∈ Submodule.span ℚ_[l] (Set.range (colv P ω A₀)) := by
  first | exact @GlobalTheory.PMon.ResR.mem_span_colv | exact GlobalTheory.PMon.ResR.mem_span_colv | (intros; apply GlobalTheory.PMon.ResR.mem_span_colv <;> assumption)
end

section

open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

theorem _root_.GlobalTheory.T.centralIdempotent_mul_mirabolicDetAverage_eq_zero : ∀ (g : ℕ) [Fact g.Prime] (r : ℕ) (ψ : Gn g r → ℂ), IsIrr ψ → ∀ (θ : (ZMod g)ˣ →* ℂˣ) (a : Fin r → ZMod g)
    (b : Bool), tr (mirEl θ a b) ψ = 0 → zOf ψ * mirEl θ a b = 0 := by
  first | exact @GlobalTheory.MirAvg.zOf_mul_mirEl_eq_zero | exact GlobalTheory.MirAvg.zOf_mul_mirEl_eq_zero | (intros; apply GlobalTheory.MirAvg.zOf_mul_mirEl_eq_zero <;> assumption)
end

section

open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

theorem _root_.GlobalTheory.T.trace_mirabolicDetCharacterAverage_vector_indep : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (ψ : Gn g (n + 1) → ℂ), IsClass ψ → ∀ (θ : (ZMod g)ˣ →* ℂˣ)
    (a : Fin (n + 1) → ZMod g), a ≠ 0 → ∀ b : Bool,
      tr (mirEl θ a b) ψ = tr (mirEl θ (if b then Pi.single 0 1 else Pi.single (Fin.last n) 1) b) ψ := by
  first | exact @GlobalTheory.MirAvg.tr_mirEl_indep | exact GlobalTheory.MirAvg.tr_mirEl_indep | (intros; apply GlobalTheory.MirAvg.tr_mirEl_indep <;> assumption)
end

section

open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

theorem _root_.GlobalTheory.T.trace_mirabolicDetAverage_eq_harishChandraRestriction : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (ψ : Gn g (n + 1) → ℂ) (θ : (ZMod g)ˣ →* ℂˣ),
    tr (mirEl θ (Pi.single (Fin.last n) 1) false) ψ =
        (g : ℂ) ^ n * ∑ x : Gn g 1, ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res n 1 ψ 1 x ∧
      tr (mirEl θ (Pi.single 0 1) true) ψ =
        (g : ℂ) ^ n * ∑ x : Gn g 1, ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res 1 n ψ x 1 := by
  first | exact @GlobalTheory.ResTr.trace_mir | exact GlobalTheory.ResTr.trace_mir | (intros; apply GlobalTheory.ResTr.trace_mir <;> assumption)
end

section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

namespace GlobalTheory.UseLoc.Cases

theorem chiOC_one {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) : chiOC C 1 = 1 := by
  ext g; simp [chiOC]

theorem chiT_one {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) : chiT C θ 1 = θ := by
  rw [chiT, mul_inv_cancel, chiOC_one, one_mul]

theorem repV_eq_inv_smul_twist : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (g : Br.G D.nbr i w hw),
    repV C N g = ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ 1) g)⁻¹ : (↥C.LL.1)ˣ).val • repV C (twistM N θ) g := by
  intro D i w hw C k N θ g
  rw [chiT_one]
  have h : repV C (twistM N θ) g = (algebraMap (↥(OL C.LL)) (↥C.LL.1) (θ g : ↥(OL C.LL))) • repV C N g := by
    simp only [repV, matRep, mapM, twistM]
    simp [RingHom.mapMatrix_apply, Matrix.map_smul', Matrix.toLinAlgEquiv'_apply]
    rw [show ((θ g : ↥(OL C.LL)) • N g).map (algebraMap ↥(OL C.LL) ↥C.LL.1)
        = (algebraMap ↥(OL C.LL) ↥C.LL.1 (θ g : ↥(OL C.LL))) • (N g).map (algebraMap ↥(OL C.LL) ↥C.LL.1) from by
          ext a b; simp [Matrix.map_apply], map_smul]
    rfl
  rw [h, smul_smul]
  simp [tableLineDegreeTwo.charL]

end GlobalTheory.UseLoc.Cases
end

section

open Formalism.MainNotions.N Formalism.BasicNotions.Loc GlobalTheory.UseLoc

theorem _root_.GlobalTheory.T.exists_fieldExtension_of_integral_retraction : ∀ {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL)), (∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) → r 1 = 1 → ∃ p : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1, (∀ (a : ↥LL.1) (x : ↥LL'.1), p (IntermediateField.inclusion h a * x) = a * p x) ∧ ∀ x : ↥(OL LL'), p (x : ↥LL'.1) = ((r x : ↥(OL LL)) : ↥LL.1) := by
  first | exact @GlobalTheory.UseLoc.extRet_exists | exact GlobalTheory.UseLoc.extRet_exists | (intros; apply GlobalTheory.UseLoc.extRet_exists <;> assumption)
end

section

open Formalism.MainNotions.N Formalism.BasicNotions.Loc GlobalTheory.UseLoc

theorem _root_.GlobalTheory.T.exists_integral_retraction_localIntegers : ∀ {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1), ∃ r : ↥(OL LL') →+ ↥(OL LL), (∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) ∧ r 1 = 1 := by
  first | exact @GlobalTheory.UseLoc.exists_intRetraction | exact GlobalTheory.UseLoc.exists_intRetraction | (intros; apply GlobalTheory.UseLoc.exists_intRetraction <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module

theorem _root_.GlobalTheory.T.coboundary_descent_enlargement_coefficients : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (z : Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T),
    (fun g => liftQ C.le k (z g)) ∈ BD (latC C (locOC C M)) → z ∈ BD (Br.locLat D.nbr i w hw M) := by
  first | exact @GlobalTheory.UseLoc.DescBD.main | exact GlobalTheory.UseLoc.DescBD.main | (intros; apply GlobalTheory.UseLoc.DescBD.main <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.WeakClosed

theorem continuous_one_tmul : ∀ {l : ℕ} [Fact l.Prime] {K LL : FinExt l} (T : Lt K LL) {d : ℕ}
    (b : LatB T d), letI := twTop T b; Continuous fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t := by
  intro l _ K LL T d b
  haveI := LL.2
  haveI : Module.Free ℤ_[l] ↥(OL LL) :=
    (GlobalTheory.Per.integers_completeDVR l LL).elim fun _ h => h.2.2.2.1
  haveI : Module.Finite ℤ_[l] ↥(OL LL) :=
    (GlobalTheory.Per.integers_completeDVR l LL).elim fun _ h => h.2.2.2.2.1
  have hc : ∀ c : ℤ_[l], algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) c) =
      algebraMap ℚ_[l] ↥LL.1 (algebraMap ℤ_[l] ℚ_[l] c) := fun c =>
    (IsScalarTower.algebraMap_apply ℤ_[l] ↥(OL LL) ↥LL.1 c).symm.trans
      (IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1 c)
  letI := zlMod T
  haveI := zlTower T
  letI := twTop T b
  letI tC : TopologicalSpace (Cb l) := cbTop l
  letI tW : TopologicalSpace (WCb l) := wTop l
  have hemb : Topology.IsInducing (algebraMap ℤ_[l] ℚ_[l]) := Topology.IsInducing.subtypeVal
  have hb : ∀ i, Continuous fun t : ↥T.L.T => b.repr t i := by
    intro i
    obtain ⟨φ, hφ⟩ := GlobalTheory.Cyc.exists_form_lat hc T b i
    have h1 : Continuous φ := GlobalTheory.Cyc.continuous_form_of_moduleTopology (L := ↥LL.1) φ
    exact hemb.continuous_iff.2 ((h1.comp continuous_subtype_val).congr hφ)
  have hW : Continuous (algebraMap ℤ_[l] (WCb l)) := GlobalTheory.WeakTop.continuous_padicInt_witt _
  have h1 : ∀ (t : ↥T.L.T) i, GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b
      ((1 : RW LL) ⊗ₜ[↥(OL LL)] t) i = algebraMap ℤ_[l] (WCb l) (b.repr t i) := by
    intro t i
    rw [Algebra.TensorProduct.one_def, GlobalTheory.WeakTop.coords_tmul, one_smul,
      Algebra.algebraMap_eq_smul_one]
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  simp only [Function.comp_apply, h1]
  exact hW.comp (hb i)

end GlobalTheory.WeakClosed
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology



namespace GlobalTheory.WeakClosed

theorem compactSpace_oTop {l : ℕ} [Fact l.Prime] {LL : FinExt l} {e : ℕ}
    (bO : Module.Basis (Fin e) ℤ_[l] ↥(OL LL)) :
    @CompactSpace ↥(OL LL) (oTop bO) := by
  letI := oTop bO
  have hi : Topology.IsInducing (bO.equivFun : ↥(OL LL) → (Fin e → ℤ_[l])) := ⟨rfl⟩
  refine ⟨?_⟩
  rw [hi.isCompact_iff, Set.image_univ_of_surjective bO.equivFun.surjective]
  exact isCompact_univ

theorem compactSpace_aTop : ∀ {l : ℕ} [Fact l.Prime] {K LL : FinExt l} {e : ℕ} (bO : Module.Basis (Fin e) ℤ_[l] ↥(OL LL)), letI := aTop (K := K) bO; CompactSpace (AA K LL) := by
  intro l _ K LL e bO
  letI := oTop bO
  haveI := compactSpace_oTop bO
  haveI : CompactSpace (PowerSeries ↥(OL LL)) := by
    unfold PowerSeries MvPowerSeries
    exact Pi.compactSpace
  exact Pi.compactSpace

end GlobalTheory.WeakClosed
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.WeakTop

theorem coords_algebraMap_smul {R O W T ι : Type} [CommRing R] [CommRing O] [Algebra R O]
    [CommRing W] [Algebra R W] [AddCommGroup T] [Module O T] [Module R T] [IsScalarTower R O T]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R T) (c : R) (x : (O ⊗[R] W) ⊗[O] T) (i : ι) :
    coords W O b (algebraMap R O c • x) i = algebraMap R W c * coords W O b x i := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add (f := _), Pi.add_apply, hx, hy, mul_add]
  | tmul r t =>
    induction r using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [add_tmul, smul_add, map_add (f := _), Pi.add_apply, hx, hy, mul_add]
    | tmul a w =>
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', coords_tmul, coords_tmul, smul_eq_mul,
        mul_smul, algebraMap_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_smul,
        Algebra.smul_def]

end GlobalTheory.WeakTop

theorem GlobalTheory.WeakClosed.continuous_zl_smul : ∀ {l : ℕ} [Fact l.Prime] {K LL : FinExt l} (T : Lt K LL) {d : ℕ} (b : LatB T d) (m : TW (RW LL) T), letI := twTop T b; Continuous fun c : ℤ_[l] => algebraMap ℤ_[l] ↥(OL LL) c • m := by
  intro l _ K LL T d b m
  letI := twTop T b
  letI := zlMod T
  haveI := zlTower T
  letI := cbTop l
  letI := cbValued l
  letI := wTop l
  haveI : IsTopologicalRing (WCb l) := GlobalTheory.WeakTop.isTopologicalRing_witt
  have hW : Continuous (algebraMap ℤ_[l] (WCb l)) := GlobalTheory.WeakTop.continuous_padicInt_witt _
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  simp only [Function.comp_apply, GlobalTheory.WeakTop.coords_algebraMap_smul]
  exact hW.mul continuous_const
end
end
