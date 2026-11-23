module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle361
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle543
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle040
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle039
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle664
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OppositePathLocalTotalTensorMemCoefficientField
public import Development.AutomorphicArithmetic.DivisorFrames.ConjSizeHeckeCharLocalOfMemRangeEmbedding
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle007
public import Development.AutomorphicArithmetic.LocalEmbeddings.ArchFlip
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle425
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle041
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle034
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle478
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
noncomputable section
open Classical in
theorem GlobalTheory.KFinDecomp.cuspForm_kFinite_decomposition : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N ψ → ∀ (U : Subgroup (GA D N.V)), IsOpen (U : Set (GA D N.V)) → (∀ k ∈ U, k ∈ GfC N.V → ∀ g, ψ (g * k) = ψ g) → (∀ τ, GlobalTheory.CuspKFin.KFinAt θ N τ ψ) → ∀ (μ : Measure (GA D N.V)) (𝓕 : Set (GA D N.V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ N.V) 𝓕 μ → ∃ (n : ℕ) (T₀ : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap N.M) (u : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M), (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.IsGKMap θ N.M {k | k ∈ U ∧ k ∈ GfC N.V} 1 μ 𝓕 (T₀ j)) ∧ ψ = ∑ j, T₀ j (u j) := by
  intro D θ hθ hP N ψ hψ U hU hlev hK μ 𝓕 hμ h𝓕
  choose W i1 i2 i3 ρ hρc hρ using hK
  letI := i1; letI := i2; letI := i3
  obtain ⟨n, T₀, u, hv, hk, hl, he⟩ := GlobalTheory.T.kFiniteDecomposition_assemble_realPlaces D θ N (GlobalTheory.KFinDecomp.Cls θ N U)
    (fun τ f => GlobalTheory.Published.AutFin.HasTypeAt θ N.V τ (N.M.ε τ) (N.M.fr τ) (ρ τ) f)
    (fun f hf => hf.1.1.cont) (_root_.GlobalTheory.T.weil_representation_place_decomposition D θ hθ hP N U W ρ hρc) ψ ⟨hψ, hlev⟩ hρ
  refine ⟨n, T₀, u, fun j => ?_, he⟩
  have hc := fun v => (hv j v).1
  refine ⟨fun v => (hc v).1.toIsAutFun, fun v => (hc v).1.smooth, fun v => (hc v).2.1,
    fun v => GlobalTheory.CuspDecay.memLp_two_of_cuspBounded hP.cuspBounded hθ (hc v).1.toIsAutFun (hc v).1.smooth
      (hc v).1.growth (hc v).2.1 μ 𝓕 hμ h𝓕,
    fun v => unifModGrowth_of_isAutFunSm hθ (hc v).1, fun v k hk g => ?_, hk j, hl j⟩
  rw [Pi.one_apply, one_mul]
  exact (hv j v).2 k hk.1 hk.2 g
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

theorem _root_.GlobalTheory.T.cuspForm_decomposes_into_kFinite_components : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N ψ → ∀ (U : Subgroup (GA D N.V)), IsOpen (U : Set (GA D N.V)) → (∀ k ∈ U, k ∈ GfC N.V → ∀ g, ψ (g * k) = ψ g) → (∀ τ, GlobalTheory.CuspKFin.KFinAt θ N τ ψ) → ∀ (μ : Measure (GA D N.V)) (𝓕 : Set (GA D N.V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ N.V) 𝓕 μ → ∃ (n : ℕ) (T₀ : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap N.M) (u : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M), (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.IsGKMap θ N.M {k | k ∈ U ∧ k ∈ GfC N.V} 1 μ 𝓕 (T₀ j)) ∧ ψ = ∑ j, T₀ j (u j) := by
  first | exact @_root_.GlobalTheory.KFinDecomp.cuspForm_kFinite_decomposition | exact _root_.GlobalTheory.KFinDecomp.cuspForm_kFinite_decomposition | (intros; apply _root_.GlobalTheory.KFinDecomp.cuspForm_kFinite_decomposition <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
noncomputable section
namespace GlobalTheory.KFinCuspSum
theorem kFinite_cusp_form_eq_sum_values : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i j, i ≤ D.R.m → j ≤ D.R.m → ∀ ψ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) ψ → (∃ W : Submodule ℂ (GA D (G.V i j).V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (G.V i j).V τ), (G.V i j).M.fr τ * g * ((G.V i j).M.fr τ)⁻¹ ∈ Formalism.REAL.Kset ((G.V i j).M.ε τ) → ∀ f ∈ W, Formalism.L2.Theta.rTr (G.V i j).V (Formalism.L2.Theta.atTau R.θ (G.V i j).V τ g) f ∈ W) → ∃ (n : ℕ) (T : Fin n → Formalism.IndefR.Mult.MMap (G.V i j).M) (v : Fin n → (G.V i j).M.Vec), (∀ l, Formalism.IndefR.Mult.IsMultMap R.θ (G.V i j).M ∅ 1 (T l)) ∧ ∀ g, ψ g = ∑ l, T l (v l) g := by
  intro hP D G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i j hi hj ψ hψ hW
  obtain ⟨n, F, u, hF, hsum⟩ :=
    _root_.GlobalTheory.T.cuspForm_gelfandKirillov_finite_decomposition hP R.θ (G.V i j).V (G.V i j).S (G.V i j).M hR.inf ψ hψ.1 hψ.2.1 hψ.2.2 hW
  choose Tm hTm hext using fun l =>
    _root_.GlobalTheory.T.gelfandKirillov_globalization hP R.θ (G.V i j).V (G.V i j).S (G.V i j).M hR.inf (F l) (hF l)
  choose v hv hTv using fun l => hext l (u l)
  refine ⟨n, Tm, v, hTm, fun g => ?_⟩
  rw [hsum g]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hTv l]
end GlobalTheory.KFinCuspSum
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.kFinite_cusp_form_finite_sum_expansion : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i j, i ≤ D.R.m → j ≤ D.R.m → ∀ ψ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) ψ → (∃ W : Submodule ℂ (GA D (G.V i j).V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (G.V i j).V τ), (G.V i j).M.fr τ * g * ((G.V i j).M.fr τ)⁻¹ ∈ Formalism.REAL.Kset ((G.V i j).M.ε τ) → ∀ f ∈ W, Formalism.L2.Theta.rTr (G.V i j).V (Formalism.L2.Theta.atTau R.θ (G.V i j).V τ g) f ∈ W) → ∃ (n : ℕ) (T : Fin n → Formalism.IndefR.Mult.MMap (G.V i j).M) (v : Fin n → (G.V i j).M.Vec), (∀ l, Formalism.IndefR.Mult.IsMultMap R.θ (G.V i j).M ∅ 1 (T l)) ∧ ∀ g, ψ g = ∑ l, T l (v l) g := by
  first | exact @_root_.GlobalTheory.KFinCuspSum.kFinite_cusp_form_eq_sum_values | exact _root_.GlobalTheory.KFinCuspSum.kFinite_cusp_form_eq_sum_values | (intros; apply _root_.GlobalTheory.KFinCuspSum.kFinite_cusp_form_eq_sum_values <;> assumption)
end
end

section

section
open GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ArchTens
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.ConjSize ValuativeRel
open Formalism.L2.Host GlobalTheory.StepData
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
private theorem additive_character_pow_conductor {W : G.Weil} {w : Pl D.host.E} (hc : HasConductor (psiAt W w) 1) (n : ℕ) (x : Kw w)
    (hx : valuation (Kw w) ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) ≤ 1) :
    (psiAt W w x : ℂ) ^ (Ideal.absNorm w.asIdeal ^ n) = 1 := by
  have e := GivenAdm.isEquiv_val w
  set q := Ideal.absNorm w.asIdeal
  have hq : Valued.v ((q : ℕ) : Kw w) ≤ WithZero.exp (-1 : ℤ) := by
    have hmem : ((q : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal ^ 1 := by rw [pow_one]; exact Ideal.absNorm_mem w.asIdeal
    have h2 : Valued.v ((q : ℕ) : Kw w) = w.intValuation ((q:ℕ) : 𝓞 D.host.E) := by
      rw [← map_natCast (algebraMap (𝓞 D.host.E) (Kw w))]
      exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := D.host.E) w _).trans
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap _ _)
    rw [h2]
    have := (w.intValuation_le_pow_iff_mem ((q:ℕ) : 𝓞 D.host.E) 1).2 hmem
    simpa using this
  have hu : Valued.v ((unifAt w : (Kw w)ˣ) : Kw w) = WithZero.exp (-1 : ℤ) := unif_spec w
  have hx' : Valued.v ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) ≤ 1 := by
    have := (e ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) 1).1 (by rw [map_one]; exact hx)
    rwa [map_one] at this
  have hNx : Valued.v (((q ^ n : ℕ) : Kw w) * x) ≤ 1 := by
    refine le_trans ?_ hx'
    rw [map_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, Nat.cast_pow, map_pow, hu]
    gcongr <;> exact zero_le
  have hNx2 : valuation (Kw w) (((q ^ n : ℕ) : Kw w) * x) ≤ valuation (Kw w) 1 :=
    (e (((q ^ n : ℕ) : Kw w) * x) 1).2 (by rw [map_one]; exact hNx)
  have h1 : psiAt W w ((q ^ n) • x) = 1 := by
    rw [nsmul_eq_mul]
    exact (hc 1).2 (by simp) _ hNx2
  rw [← Circle.coe_pow, ← AddChar.map_nsmul_eq_pow, h1, Circle.coe_one]
private theorem congruence_le_given_level {μ₀ : T} (hL : L.Is μ₀) {t : T} {w : Pl D.host.E} (hw : w ∈ locPl G t)
    (he : depthAt G w = cosExp G w) (X : ℕ × ℕ) :
    glLatCong (unifAt w ^ depthAt G w) (GlobalTheory.SplitFlip.stdLat (Kw w) _) ≤ givenLevel G t w X := by
  obtain ⟨i, _ | j⟩ := X
  · rw [givenLevel, he]
  · rcases i with _ | i
    · obtain ⟨P, hP, -⟩ := GivenAdm.exists_types hL hw
      rw [GivenAdm.givenLevel_succ (hP _)]
      refine le_trans (fun g hg => mem_KOne.2 fun a b => ((GivenAdm.mem_glLatCong.1 hg).2 a b).trans_lt ?_)
        (TypeDatum.KOne_le _)
      rw [Units.val_pow_eq_pow_val, map_pow]
      exact pow_lt_one₀ zero_le' (isUnif_unifAt w ▸ uniformizer_lt_one) (by rw [depthAt]; omega)
    · exact fun g hg => (GivenAdm.mem_glLatCong.1 hg).1
private theorem local_grid_entries_unitary {K : Type} [Field K] {ι τ : K →+* ℂ} (t : T) (w : Pl D.host.E)
    (hmu : ∀ j x, Un ι τ ((L.C.mu0 j).loc w x : ℂ)) (hxi : ∀ x, Un ι τ ((L.xiH t).loc w x : ℂ))
    (hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x, Un ι τ ((G.ch.chiH i).loc w x : ℂ))
    {i j : ℕ} (hi : i < D.R.m) (hj : j < D.R.m) (u : (Kw w)ˣ) : Un ι τ ((locGrid G t w).nu i j u : ℂ) := by
  have e1 : (((locGrid G t w).nu i j u : ℂˣ) : ℂ) =
      ((L.C.mu0 ⟨j, hj⟩).loc w u : ℂ) * ((L.xiH t).loc w u : ℂ) * (((G.ch.chiH (D.R.m - i)).loc w u : ℂ))⁻¹ := by
    simp only [Grid.nu, locGrid, muBase, dif_pos hj, MonoidHom.div_apply, Units.val_div_eq_div_val, div_eq_mul_inv]
    simp [HChar.loc]
  rw [e1]
  exact ((hmu _ _).mul (hxi _)).mul (hchi _ (by omega) (by omega) _).inv
private theorem local_grid_rank_le (t : T) (w : Pl D.host.E) {i j : ℕ} (hi : i < D.R.m) (hj : j < D.R.m) :
    (locGrid G t w).rank (i + 1, j + 1) ≤ 2 * bigN D := by
  change D.R.r + (j + 1) * D.R.t + (i + 1) * sLen D ≤ 2 * bigN D
  have h1 : (j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ hj
  have h2 : (i + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
  have h3 : 1 * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ (by omega)
  have h4 : D.R.r ≤ sLen D := Nat.le_add_right _ _
  unfold bigN
  rw [mul_add D.R.m, mul_add D.R.m]
  omega
end
open Formalism.BasicNotions Formalism.IndefR.Links Formalism.L2.DIV NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.ConjSize in
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw in
theorem _root_.GlobalTheory.T.local_character_power_conductor_bound : _root_.GlobalTheory.FunPr.ThetaLocalInputs → BigC fun _ ch C _ => FlipAt ch C := by
  refine fun _ => ⟨0, fun CF _ => ⟨48, fun ε C hC => ⟨0, ?_⟩⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch _ hF σ Φ w₀ z
  obtain ⟨w, hw⟩ := w₀
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hde := GlobalTheory.FlipIntegrand.pde_ne_q_of_setting hS
  have hc : ∀ P ∈ R.toLevCh.Q A.μ0, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hch.guard A.μ0
  have hg := (Good.locGrid_isGood hL ch.G ch.W A.μ0 hde hc).1 w hw
  have hadm := GivenAdm.givenStage_isAdmissible hL ch.S.B A.μ0 Φ hw
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := hg.square 0 hm 0 hm
  have hW : w ∈ ch.G.pl.W0 := (GivenAdm.mem_locPl.1 hw).resolve_right fun h =>
    (hL.Q_ram A.μ0 w).2 (.inl h) (by rw [hL.xi_base]; exact fun _ _ => rfl)
  have he : depthAt ch.G w = cosExp ch.G w := by
    obtain ⟨h1, h2⟩ := GivenAdm.under_mem_and_place_above_eq_of_mem hW
    have := depthAt_w ch.G h1
    rw [h2] at this
    rw [this.1, this.2]
  have hmu : ∀ j x, Un D.what₂.embLL σ ((R.toLevCh.C.mu0 j).loc w x : ℂ) := fun j x => by
    obtain ⟨n, -, hn⟩ := (R.toLevCh.C.isMu0 j).inf
    exact UpperTheory.conjSize_heckeChar_local_of_mem_range_embedding _ _ _ _ hn _ _ _ _ (hF.chars.mu0 j w x)
  have hxi : ∀ x, Un D.what₂.embLL σ ((R.toLevCh.xiH A.μ0).loc w x : ℂ) := fun x => by
    rw [hL.xi_base]; exact Un.one
  have hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x, Un D.what₂.embLL σ ((ch.G.ch.chiH i).loc w x : ℂ) :=
    fun i a b x => UpperTheory.conjSize_heckeChar_local_of_mem_range_embedding _ _ _ _ (ch.G.ch.inf i a b) _ _ _ _ (hF.chars.chi i a b w x)
  have habs : ∀ u : (Kw w)ˣ, apow u (1 / 2) ∈ Set.range D.what₂.embLL := fun u =>
    RingHom.mem_fieldRange.1 (GlobalTheory.TflipField.apow_half_mem D.what₂.embLL.fieldRange w
      (RingHom.mem_fieldRange.2 (hF.sqrt w (.inr ⟨A.μ0, hw⟩))) u)
  have hq0 : Ideal.absNorm w.asIdeal ≠ 0 := fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hψ := fun x hx => (fun h => Un.of_pow_eq_one (τ := σ) (hF.roots A.μ0 w hw _ h) (pow_ne_zero _ hq0) h)
    (additive_character_pow_conductor (W := ch.W) h00.cond (depthAt ch.G w) x hx)
  have hν : ∀ x ∈ flipOrder D.R.m, (locGrid ch.G A.μ0 w).rank (x.1 + 1, x.2 + 1) ≤ 2 * bigN D ∧
      CondLE (unifAt w) (depthAt ch.G w) ((locGrid ch.G A.μ0 w).nu x.1 x.2) ∧
      ¬ IsUnram ((locGrid ch.G A.μ0 w).nu x.1 x.2) ∧ ∀ u, Un D.what₂.embLL σ ((locGrid ch.G A.μ0 w).nu x.1 x.2 u : ℂ) := by
    intro x hx
    simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, j, hj, rfl⟩ := hx
    have hs := hg.square i hi j hj
    have e := (locGrid ch.G A.μ0 w).alpha_div_beta i j
    exact ⟨local_grid_rank_le _ _ hi hj, by rw [← e]; exact hs.condν, by rw [← e]; exact hs.ram, local_grid_entries_unitary _ w hmu hxi hchi hi hj⟩
  have key := sz_flips h00.unif h00.cond h00.one_le habs hψ (2 * bigN D) (flipOrder D.R.m)
    (givenStage A.μ0 w ch.S.B Φ) 1 hν (canFlip_flipOrder _).1
    (fun X => ⟨(GivenAdm.givenLevel_open hL hw X).1, (GivenAdm.givenLevel_open hL hw X).2, congruence_le_given_level hL hw he X⟩)
    hadm.tensor (UpperTheory.localGrid_tensor_size_le_one_of_unimodular _ _ ch.S.B A.μ0 Φ w hmu hxi) z
  refine key.mono ?_
  rw [mul_one, (canFlip_flipOrder _).2.1, ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.ResCardPlace.resCard_Kw, he,
    ← Real.exp_log (pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hq0) _), Real.log_pow, Real.exp_le_exp]
  have h1 := ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.log_absNorm_le w
  have h2 := placeSz_nonneg ch.G w
  calc _ ≤ ((6 * cosExp ch.G w * (2 * bigN D) ^ 2 * D.R.m ^ 2 : ℕ) : ℝ) *
        (2 * Real.log (Ideal.absNorm (w.under (𝓞 D.host.F)).asIdeal)) := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
    _ = 48 * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * placeSz ch.G w := by rw [placeSz]; push_cast; ring
    _ ≤ _ := by gcongr
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.SquareAgree.DatA
theorem polarization_datum_lie_derivative : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ) (γ : Multiplicative ℝ →* UA D.sp.cm.sig Γ.W.J),
    (∀ t : ℝ, γ (Multiplicative.ofAdd t) = kapX X e hO.JX (oneP θ X τ Y t)) → γ ∈ Lines D.sp.cm.sig Γ.W →
    ∀ (Φ Φ' : WO W X → ℂ), IsDer θ X (fun h => ωA (1, h)) τ Y Φ Φ' →
    ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F))) (m : ℕ) (f f₁ : Fin m → SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)))
      (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
    (∀ i, f i ∈ Γ.M.Pol Bs.ψ Bs.emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ v ∉ T, φ i v = Γ.M.vac v) →
    (∀ i, ActsD (evI D.host.F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (f i) (f₁ i)) →
    IsDatum Γ.M ψ cA (∑ i, pure (f i) (φ i)) Φ →
    ∀ Φ'D, IsDatum Γ.M ψ cA Φ'D Φ' → Φ'D = ∑ i, pure (f₁ i) (φ i) := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hO hT τ Y γ hγ hL Φ Φ' hD T m f f₁ φ hf hA hΦ Φ'D hΦ'
  have hM := hT.geo.hM
  have hstd : ∀ i, ∀ᶠ v in Filter.cofinite, φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers D.host.F} 1 := by
    intro i
    filter_upwards [hM.std, T.finite_toSet.compl_mem_cofinite] with v hv hvT
    rw [(hf i).2.2 v hvT, hv]
  have hrest : ∀ i, Rest (evI D.host.F) (⇑(f i)) (GlobalTheory.EvZeroInf.finPart (φ i)) := fun i =>
    ⟨fun x z hz => GlobalTheory.EvZeroInf.finPart_add _ x z hz, by
      rw [← GlobalTheory.EvZeroInf.pure_eq_tens]; exact GlobalTheory.TensUniq.pure_mem_schA _ _ (hf i).2.1 (hstd i)⟩
  have hsum : ∀ g : Fin m → SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)),
      ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (g i) (φ i) = ∑ i, tens (evI D.host.F) (⇑(g i)) (GlobalTheory.EvZeroInf.finPart (φ i)) := fun g =>
    Finset.sum_congr rfl fun i _ => GlobalTheory.EvZeroInf.pure_eq_tens _ _
  have hone : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW 1 = 1 := by
    apply Subtype.ext; simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU]
  have hstdψ : IsStd ψ := hO.psi ▸ hT.base.std
  have hmem : ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i) ∈ GlobalTheory.WeilM.schA D.host.F _ :=
    Submodule.sum_mem _ fun i _ => GlobalTheory.TensUniq.pure_mem_schA _ _ (hf i).2.1 (hstd i)
  have hDat : IsDatum Γ.M ψ cA (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)) Φ' := by
    refine ⟨hmem, fun u => ?_⟩
    have h1 : HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho ψ u
        (om (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i))))) (Φ' (cA u)) 0 := by
      have h2 := hD (cA u)
      refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      have h3 := (hO.weilA _ _ hΦ 1 (oneP θ X τ Y t)).2 u
      rw [hone, ← hγ t] at h3
      exact h3
    have h4 := _root_.GlobalTheory.T.twisted_theta_line_derivative hP Bs Γ Xc om om' hT γ hL m f f₁ (fun i => GlobalTheory.EvZeroInf.finPart (φ i)) hrest hA u
    rw [← hsum, ← hsum, hO.psi] at h4
    exact h4.unique h1
  exact GlobalTheory.ThetaInj.theta_inj Γ.M ψ hstdψ cA Φ'D _ Φ' hΦ' hDat
end GlobalTheory.SquareAgree.DatA
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.twist_polarization_datum_lie_derivative : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ) (γ : Multiplicative ℝ →* UA D.sp.cm.sig Γ.W.J),
    (∀ t : ℝ, γ (Multiplicative.ofAdd t) = kapX X e hO.JX (oneP θ X τ Y t)) → γ ∈ Lines D.sp.cm.sig Γ.W →
    ∀ (Φ Φ' : WO W X → ℂ), IsDer θ X (fun h => ωA (1, h)) τ Y Φ Φ' →
    ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F))) (m : ℕ) (f f₁ : Fin m → SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)))
      (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
    (∀ i, f i ∈ Γ.M.Pol Bs.ψ Bs.emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ v ∉ T, φ i v = Γ.M.vac v) →
    (∀ i, ActsD (evI D.host.F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (f i) (f₁ i)) →
    IsDatum Γ.M ψ cA (∑ i, pure (f i) (φ i)) Φ →
    ∀ Φ'D, IsDatum Γ.M ψ cA Φ'D Φ' → Φ'D = ∑ i, pure (f₁ i) (φ i) := by
  first | exact @_root_.GlobalTheory.SquareAgree.DatA.polarization_datum_lie_derivative | exact _root_.GlobalTheory.SquareAgree.DatA.polarization_datum_lie_derivative | (intros; apply _root_.GlobalTheory.SquareAgree.DatA.polarization_datum_lie_derivative <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.TripleAssembly

theorem exists_pure_tensor_lieDeriv_left_factor : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
      ∀ τ, ∀ Y ∈ lieAt X τ, ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.W,
        (∀ t : ℝ, γ (Multiplicative.ofAdd t) = GlobalTheory.TripleRead.toUX X e h.JX (oneP θ X τ Y t)) →
        ∀ Φ ∈ algF ψ θ true A B, ∀ Φ' ∈ algF ψ θ true A B, IsDer θ X (fun g => ωA (1, g)) τ Y Φ Φ' →
        ∃ (m : ℕ) (f f₁ : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)))
          (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
          (∀ i, f i ∈ Γ.M.Pol Bs.ψ Bs.emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ i v = Γ.M.vac v) ∧
            GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (f i) (f₁ i)) ∧
          (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)) ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb ∧
          Φ = GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) ∧
          Φ' = GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)) := by
  intro hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hA hB e Bs Γ Xc om om' h tA tB R Rf hm τ Y hY γ hγ hγt
    Φ hΦ Φ' hΦ' hD
  classical
  have hg := hm.triple.geo
  have hψ' : Bs.ψ = ψ := h.ψ
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hψ' ▸ hm.triple.base.std
  have hG : Γ.M.IsGood ψ := hψ' ▸ hg.hM
  obtain ⟨Ψ, hΨ, rfl⟩ := (_root_.GlobalTheory.T.triple_invariant_theta_surjective hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hA hB e Bs Γ Xc om om' h tA tB
    R Rf hm).1 Φ hΦ
  obtain ⟨n, c, g, hsum⟩ := Submodule.mem_span_set'.1 hΨ
  choose f0 φ hf0 hφ hvac hpure using fun i => (g i).2
  let f : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)) := fun i => c i • f0 i
  have hΨeq : Ψ = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hpure i]
    funext x
    simp only [Pi.smul_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, f, SchwartzMap.smul_apply, smul_eq_mul, mul_assoc]
  subst hΨeq
  have hfP : ∀ i, f i ∈ Γ.M.Pol Bs.ψ Bs.emb := fun i => Submodule.smul_mem _ _ (hf0 i)
  obtain ⟨δ, hδ⟩ := _root_.GlobalTheory.DerPol.polarization_pair_derivation hP Γ.M Bs.ψ Bs.emb Xc.β (Xc.β / Xc.α) om hm.triple.base.cm hm.triple.base.std
    hm.triple.weil γ hγ
  refine ⟨n, f, fun i => δ (f i), φ, fun i => ⟨hfP i, hφ i, hvac i, (hδ _ (hfP i)).2⟩,
    Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨δ (f i), φ i, (hδ _ (hfP i)).1, hφ i, hvac i, rfl⟩, rfl, ?_⟩
  have hstdi : ∀ i, ∀ᶠ v in Filter.cofinite,
      φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers D.host.F} 1 := by
    intro i
    filter_upwards [hg.hM.std, hvac i] with v hv hv'
    rw [hv', hv]
  have hrest : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (⇑(f i)) (GlobalTheory.EvZeroInf.finPart (φ i)) :=
    fun i => ⟨fun x z hz => GlobalTheory.EvZeroInf.finPart_add _ x z hz, by
      rw [← GlobalTheory.EvZeroInf.pure_eq_tens]; exact GlobalTheory.TensUniq.pure_mem_schA _ _ (hφ i) (hstdi i)⟩
  have hsum' : ∀ k : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)),
      ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (k i) (φ i) =
        ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (⇑(k i)) (GlobalTheory.EvZeroInf.finPart (φ i)) := fun k =>
    Finset.sum_congr rfl fun i _ => GlobalTheory.EvZeroInf.pure_eq_tens _ _
  have hmem : ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) ∈ GlobalTheory.WeilM.schA D.host.F _ :=
    Submodule.sum_mem _ fun i _ => GlobalTheory.TensUniq.pure_mem_schA _ _ (hφ i) (hstdi i)
  have hone : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW 1 = 1 := by
    apply Subtype.ext; simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU]
  funext x
  have h1 : HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho ψ (GlobalTheory.TripleRead.ptO (sgn true W).gram e x)
      (om (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i))))) (Φ' x) 0 := by
    refine (hD x).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    have h3 := tA _ hmem 1 (oneP θ X τ Y t)
    rw [hone, ← hγt t] at h3
    exact congrFun h3 x
  have h4 := _root_.GlobalTheory.T.twisted_theta_line_derivative hP Bs Γ Xc om om' hm.triple γ hγ n f (fun i => δ (f i)) (fun i => GlobalTheory.EvZeroInf.finPart (φ i))
    hrest (fun i => (hδ _ (hfP i)).2) (GlobalTheory.TripleRead.ptO (sgn true W).gram e x)
  rw [← hsum', ← hsum', hψ'] at h4
  exact (h4.unique h1).symm
end GlobalTheory.TripleAssembly
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.tripleProduct_lieDeriv_left_pure_tensor : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
      ∀ τ, ∀ Y ∈ lieAt X τ, ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.W,
        (∀ t : ℝ, γ (Multiplicative.ofAdd t) = GlobalTheory.TripleRead.toUX X e h.JX (oneP θ X τ Y t)) →
        ∀ Φ ∈ algF ψ θ true A B, ∀ Φ' ∈ algF ψ θ true A B, IsDer θ X (fun g => ωA (1, g)) τ Y Φ Φ' →
        ∃ (m : ℕ) (f f₁ : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)))
          (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
          (∀ i, f i ∈ Γ.M.Pol Bs.ψ Bs.emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ i v = Γ.M.vac v) ∧
            GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (f i) (f₁ i)) ∧
          (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)) ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb ∧
          Φ = GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) ∧
          Φ' = GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)) := by
  first | exact @_root_.GlobalTheory.TripleAssembly.exists_pure_tensor_lieDeriv_left_factor | exact _root_.GlobalTheory.TripleAssembly.exists_pure_tensor_lieDeriv_left_factor | (intros; apply _root_.GlobalTheory.TripleAssembly.exists_pure_tensor_lieDeriv_left_factor <;> assumption)
end
end
