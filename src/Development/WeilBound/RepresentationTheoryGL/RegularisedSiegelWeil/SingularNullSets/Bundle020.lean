module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWB
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2186
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixThB
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle012
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle004
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle041
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle040
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle077
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle059
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle006
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Kdata
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle005
import Formalism.LocalRingCardinality.DataHost
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import GroundTheory.AutomorphicForms.Bundle012
import GroundTheory.GlobalFields.Adele.Topology
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LToSA
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle015
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LFixTh




open PositivityTheory.Rg.Rsw.L

variable {D : D7} {ρ p n : ℕ}

instance finDim (D : D7) : FiniteDimensional D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _

structure GoodPl (χ : (AE D)ˣ →* Circle) (b₀ : HermE D ρ) (v : Pl D) : Prop where
  good : LFixW.IsGood D.host.F D.host.E v
  unr : ∀ u ∈ GlobalTheory.ThK.unitsAt D.host.E v, χ u = 1
  bint : ∀ i j, inclR (Fv D.host.F v) (b₀.1 i j) ∈ intLoc D.host.F D.host.E v

theorem eventually_unr {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) :
    ∀ᶠ v in cofinite, ∀ u ∈ GlobalTheory.ThK.unitsAt D.host.E v, χ u = 1 := by
  classical
  let m : Pl D → (AE D)ˣ := fun v =>
    if h : ∃ u ∈ GlobalTheory.ThK.unitsAt D.host.E v, χ u ≠ 1 then h.choose else 1
  have hm : ∀ v, m v ∈ GlobalTheory.ThK.unitsAt D.host.E v := fun v => by
    simp only [m]
    split_ifs with h
    · exact h.choose_spec.1
    · exact one_mem _
  filter_upwards [GlobalTheory.ThK.ConeEulerChr.eventually_chr_eq_one (ν := χ) hχ.1 m (Eventually.of_forall hm)] with v hv u hu
  by_contra hne
  have h : ∃ u ∈ GlobalTheory.ThK.unitsAt D.host.E v, χ u ≠ 1 := ⟨u, hu, hne⟩
  have e : m v = h.choose := dif_pos h
  exact h.choose_spec.2 (e ▸ hv)

theorem eventually_goodPl {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (b₀ : HermE D ρ) :
    ∀ᶠ v in cofinite, GoodPl χ b₀ v := by
  filter_upwards [LFixW.eventually_good (F := D.host.F) (E := D.host.E), eventually_unr hχ,
    eventually_all.2 fun i => eventually_all.2 fun j =>
      GlobalTheory.AdelicU.SelfDual.eventually_mem_intLoc (F := D.host.F) (b₀.1 i j)] with v h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem adj_apply (x : Mx D ρ p) (i : Fin p) (j : Fin ρ) : adj x i j = cA D (x j i) := rfl

theorem cv_cA (v : Pl D) (x : AE D) : cv D v (cA D x) = sigR (Fv D.host.F v) D.sp.cm.sig (cv D v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => rw [map_add (cA D), map_add (cv D v), map_add (cv D v), hx, hy, map_add (sigR (Fv D.host.F v) D.sp.cm.sig)]

theorem one_cn {R : Type} [Ring R] (i j : Fin n) :
    (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) (Fin.castAdd n i) (Fin.natAdd n j) = 0 := by
  rw [← block_matrix_one (R := R), block_matrix_apply_top_right, Matrix.zero_apply]

theorem unip_one {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {b₀ : HermE D ρ} {S : Finset (Pl D)}
    (hS : ∀ v ∉ S, GoodPl χ b₀ v)
    (hker : ∀ y : AF D.host.F, y.1 = 0 → (∀ v ∈ S, y.2 v = 0) →
      (∀ v ∉ S, y.2 v ∈ v.adicCompletionIntegers D.host.F) → ψ y = 1)
    {g : G D p} (hg : g ∈ KOff D p S) {b : Mx D p p} (hb : mat g = blk4 1 b 0 1) {y : Mx D ρ p} (hy : IntOff S y) :
    ψ (halfTr (b * pr b₀ y y).trace) = 1 := by
  have hbe : ∀ i j, b i j = mat g (Fin.castAdd p i) (Fin.natAdd p j) := fun i j => by rw [hb, block_matrix_apply_top_right]
  have hbInf : ∀ w i j, compInf D.host.F D.host.E w (b i j) = 0 := fun w i j => by
    rw [hbe, (kOff_entry hg _ _).1 w, one_cn]
  have hbS : ∀ v ∈ S, ∀ i j, cv D v (b i j) = 0 := fun v hv i j => by
    rw [hbe, (kOff_entry hg _ _).2.1 v hv, one_cn]
  have hbI : ∀ v ∉ S, ∀ i j, cv D v (b i j) ∈ intLoc D.host.F D.host.E v := fun v hv i j => by
    rw [hbe]; exact (kOff_entry hg _ _).2.2 v hv
  have hPI : ∀ v ∉ S, ∀ k i, cv D v (pr b₀ y y k i) ∈ intLoc D.host.F D.host.E v := by
    intro v hv k i

    simp only [pr, Matrix.mul_apply, map_sum, map_mul]
    refine sum_mem fun l _ => mul_mem ?_ (sum_mem fun m _ => mul_mem ?_ (hy v hv m i))
    · rw [adj_apply, cv_cA]; exact sigR_mem_intLoc _ (hy v hv l k)
    · rw [Matrix.map_apply]; exact (hS v hv).bint l m
  have hX : ∀ (R : Type) [CommRing R] (f : AE D →+* R), f (b * pr b₀ y y).trace =
      ∑ i, ∑ k, f (b i k) * f (pr b₀ y y k i) := fun R _ f => by

    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul]
  have hXinf : ∀ w, compInf D.host.F D.host.E w (b * pr b₀ y y).trace = 0 := fun w => by
    rw [hX]; simp [hbInf]
  have hXS : ∀ v ∈ S, cv D v (b * pr b₀ y y).trace = 0 := fun v hv => by
    rw [hX]; simp [hbS v hv]
  have hXI : ∀ v ∉ S, cv D v (b * pr b₀ y y).trace ∈ intLoc D.host.F D.host.E v := fun v hv => by
    rw [hX]; exact sum_mem fun i _ => sum_mem fun k _ => mul_mem (hbI v hv i k) (hPI v hv k i)
  apply hker
  · refine funext fun w => ?_
    change evInf D.host.F w (algebraMap D.host.F (AF D.host.F) (1 / 2) * trA (b * pr b₀ y y).trace) = 0
    rw [map_mul, LFixW.evInf_apply w (trA _), LFixW.trA_fst, hXinf, map_zero, mul_zero]
  · intro v hv
    change evFin D.host.F v (algebraMap D.host.F (AF D.host.F) (1 / 2) * trA (b * pr b₀ y y).trace) = 0
    rw [map_mul, LFixW.evFin_apply v (trA _), LFixW.trA_snd, hXS v hv, map_zero, mul_zero]
  · intro v hv
    change evFin D.host.F v (algebraMap D.host.F (AF D.host.F) (1 / 2) * trA (b * pr b₀ y y).trace) ∈ _
    rw [map_mul, LFixW.evFin_apply v (trA _), LFixW.trA_snd, AlgHom.commutes, one_div]
    exact mul_mem (hS v hv).good.half (LFixW.trace_mem (hS v hv).good (hXI v hv))

end PositivityTheory.Rg.Rsw.L.LFixTh

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef (testT boxA fouA intF)

theorem oneD : OneD := by
  intro F _ _ hF ψ hψ S ε hε ν hν
  classical
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  obtain ⟨db, hdb⟩ := GlobalTheory.T.exists_adelic_haar_covolume_one F
  obtain ⟨⟨laminf, hinf⟩, hlamex⟩ := GlobalTheory.T.exists_standard_local_measures F
  choose lam hlam using hlamex
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.exists_local_approximate_identity F hF ψ hψ db hdb laminf lam hinf hlam
  obtain ⟨ρ, U, hρ, hρt, hU, hUt, hinv, hint, -, hlim⟩ := hS₁ (S ∪ S₁) Finset.subset_union_right
  haveI : db.IsAddHaarMeasure := hdb.1
  have hεε := idF_mul hε
  have hp : Continuous (AddMonoidHom.mulLeft ε) := continuous_const.mul continuous_id
  have hpp : ∀ x, AddMonoidHom.mulLeft ε (AddMonoidHom.mulLeft ε x) = AddMonoidHom.mulLeft ε x := fun x => by
    simp only [AddMonoidHom.coe_mulLeft, ← mul_assoc, hεε]
  have hcY : IsClosed (((AddMonoidHom.mulLeft ε).ker : Set (AF F))) := isClosed_eq hp continuous_const
  haveI : LocallyCompactSpace (AddMonoidHom.mulLeft ε).ker := hcY.locallyCompactSpace
  haveI : LocallyCompactSpace (fixE ε) := (isClosed_eq hp continuous_id).locallyCompactSpace
  haveI := hν
  haveI : SecondCountableTopology (fixE ε) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology (AddMonoidHom.mulLeft ε).ker := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace (fixE ε) := inferInstance
  haveI : SigmaCompactSpace (AddMonoidHom.mulLeft ε).ker := inferInstance
  haveI : SigmaFinite ν := inferInstance
  obtain ⟨c, hc, hdec⟩ := decomp (AddMonoidHom.mulLeft ε) hp hpp db ν (Measure.addHaar)
  have hloc := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), IsTopologicalRing (Fv F v) := fun v => (hloc v).1
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1
  have hne : ∀ k, ∫ y, testT (ρ k) (S ∪ S₁) (U k) y ∂db ≠ 0 := by
    intro k
    rw [hint k]
    refine mul_ne_zero (by exact_mod_cast (hρ k).2.2.2.ne') (Finset.prod_ne_zero_iff.2 fun v _ => ?_)
    have h1 : 0 < (lam v) (U k v) := (hU k v).2.1.measure_pos (lam v) ⟨0, (hU k v).2.2⟩
    have h2 : (lam v) (U k v) ≠ ⊤ := (hU k v).1.measure_lt_top.ne
    exact_mod_cast (ENNReal.toReal_pos h1.ne' h2).ne'
  choose g Gc hGc hgI hgb hgint hgeq using fun k => kdata ψ hψ Finset.subset_union_left hε db ν Measure.addHaar c hc
    hdec (ρ k) (hρ k).1 (hρ k).2.1 (hρ k).2.2.1 (U k) (fun v => (hU k v).2.2) (hinv k).1 (hinv k).2 (hne k)
  refine ⟨g, fun k s => Gc k * tR (ρ k) (S ∪ S₁) (U k) (-(ε * s)),
    fun k => {a | ε * a = a ∧ fstA F a ∈ tsupport (ρ k) ∧ ∀ v ∈ S, (sndA F a) v ∈ U k v},
    fun k => ⟨hgI k, hgb k, fun s => ⟨mul_nonneg (hGc k) (tR_nonneg (hρ k).2.2.1 _ _ _), hgint k s⟩⟩,
    fun h => ?_, fun k s hs => ?_, top1 S ε hε _ U hρt hUt⟩
  · have hl := hlim h.1
    have hm : sndA F h.1 ∈ intF (S ∪ S₁) := fun v hv => by
      rw [snd_eq, fix_snd hε (memH h) (fun h' => hv (Finset.mem_union_left _ h'))]
      exact zero_mem _
    rw [Set.indicator_of_mem hm] at hl
    simp only [hgeq]
    exact hl
  · have ht : tR (ρ k) (S ∪ S₁) (U k) (-(ε * s)) ≠ 0 := fun h0 => hs (by simp only [h0, mul_zero])
    unfold tR at ht
    have hρne : ρ k (fstA F (-(ε * s))) ≠ 0 := fun h0 => ht (by rw [h0, zero_mul])
    have hbox : sndA F (-(ε * s)) ∈ boxA (S ∪ S₁) (U k) := by
      by_contra hn
      exact ht (by rw [Set.indicator_of_notMem hn, mul_zero])
    exact ⟨by rw [mul_neg, ← mul_assoc, hεε], subset_tsupport _ hρne,
      fun v hv => hbox.1 v (Finset.mem_union_left _ hv)⟩

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField



namespace PositivityTheory.Rg.Rsw.L.LToS

variable {D : D7} {a b c r t : ℕ}

theorem adj_smul (e : AE D) (x : Mx D a b) : adj (e • x) = cA D e • adj x := by
  ext i j
  show cA D (e * x j i) = cA D e * cA D (x j i)
  exact map_mul _ _ _

theorem ip_smul {e : AE D} (he : e * e = e ∧ cA D e = e) (V : HSp D) (x : Mx D V.rank a) (y : Mx D V.rank b) :
    ip V (e • x) (e • y) = e • ip V x y := by
  simp only [ip, mm, adj_smul, he.2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he.1]

theorem yv_smul {e : AE D} (he : e * e = e ∧ cA D e = e) (V : HSp D) (b₀ : HermE D r)
    (z : Mx D V.rank r × Mx D V.rank t) : yv V b₀ (e • z.1, e • z.2) = e • yv V b₀ z := by
  simp only [yv, ip_smul he, mm, Matrix.mul_smul]

theorem pr_smul {e : AE D} (he : e * e = e ∧ cA D e = e) (b₀ : HermE D r) (x y : Mx D r t) :
    pr b₀ (e • x) (e • y) = e • pr b₀ x y := by
  simp only [pr, adj_smul, he.2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he.1]

theorem qv_smul {e : AE D} (he : e * e = e ∧ cA D e = e) (V : HSp D) (b₀ : HermE D r)
    (z : Mx D V.rank r × Mx D V.rank t) : qv V b₀ (e • z.1, e • z.2) = e • qv V b₀ z := by
  simp only [qv, yv_smul he, ip_smul he, pr_smul he, smul_sub]

theorem continuous_ip (V : HSp D) : Continuous fun p : Mx D V.rank a × Mx D V.rank b => ip V p.1 p.2 := by
  show Continuous fun p : Mx D V.rank a × Mx D V.rank b => adj p.1 * (gA V * p.2)
  exact (continuous_adj.comp continuous_fst).matrix_mul (continuous_const.matrix_mul continuous_snd)

theorem continuous_yv (V : HSp D) (b₀ : HermE D r) :
    Continuous fun z : Mx D V.rank r × Mx D V.rank t => yv V b₀ z := by
  show Continuous fun z : Mx D V.rank r × Mx D V.rank t => rat b₀.1⁻¹ * ip V z.1 z.2
  exact continuous_const.matrix_mul (continuous_ip V)

theorem isClosed_qv (V : HSp D) (b₀ : HermE D r) :
    IsClosed {z : Mx D V.rank r × Mx D V.rank t | qv V b₀ z = 0} := by
  have hy := continuous_yv (t := t) V b₀
  have h1 : Continuous fun z : Mx D V.rank r × Mx D V.rank t => ip V z.2 z.2 := by
    show Continuous fun z : Mx D V.rank r × Mx D V.rank t => adj z.2 * (gA V * z.2)
    exact (continuous_adj.comp continuous_snd).matrix_mul (continuous_const.matrix_mul continuous_snd)
  have h2 : Continuous fun z : Mx D V.rank r × Mx D V.rank t => pr b₀ (yv V b₀ z) (yv V b₀ z) := by
    show Continuous fun z : Mx D V.rank r × Mx D V.rank t => adj (yv V b₀ z) * ((b₀.1.map (incA D)) * yv V b₀ z)
    exact (continuous_adj.comp hy).matrix_mul (continuous_const.matrix_mul hy)
  have e : {z : Mx D V.rank r × Mx D V.rank t | qv V b₀ z = 0} =
      {z | ip V z.2 z.2 = pr b₀ (yv V b₀ z) (yv V b₀ z)} := Set.ext fun z => sub_eq_zero
  rw [e]
  exact isClosed_eq h1 h2

theorem map_transport {X : Type*} [MeasurableSpace X] {ν : Measure X} {A : Set X} (hA : MeasurableSet A)
    {f φ ψ : X → X} (hf : Measurable f) (hφ : Measurable φ) (hψ : Measurable ψ) (hA' : φ ⁻¹' A = A)
    (hc : ∀ z, ψ (f z) = f (φ z)) {κ : ℝ≥0} (hν : ν.map φ = κ • ν) :
    ((ν.restrict A).map f).map ψ = κ • (ν.restrict A).map f := by
  have h1 : (ν.restrict A).map φ = κ • ν.restrict A := by
    conv_lhs => rw [← hA']
    rw [← Measure.restrict_map hφ hA, hν, Measure.restrict_smul]
  rw [Measure.map_map hψ hf, show ψ ∘ f = f ∘ φ from funext hc, ← Measure.map_map hf hφ, h1, Measure.map_smul]
  exact hf.aemeasurable

end PositivityTheory.Rg.Rsw.L.LToS

end
end
