module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LToSA
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantFormVanishesLagrangianTest
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2186
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2155
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle012
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle007
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle016
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

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

variable {D : D7} {ρ p : ℕ}

theorem det_mem_subring {R : Type} [CommRing R] (T : Subring R) {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, M i j ∈ T) : M.det ∈ T := by
  let N : Matrix (Fin n) (Fin n) T := fun i j => ⟨M i j, h i j⟩
  have e : M = T.subtype.mapMatrix N := by ext i j; rfl
  rw [e, ← RingHom.map_det]
  exact (N.det).2

theorem evFin_eInf (v : Pl D) : evFin D.host.F v (GlobalTheory.ThK.ConeEuler.eInf D.host.F) = 0 := by
  rw [LFixW.evFin_apply, GlobalTheory.ThK.ConeEuler.eInf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd, LinearMap.inl_apply]
  rfl

theorem unitArch_eq_one (l : (AE D)ˣ) (hinf : ∀ w, compInf D.host.F D.host.E w (l : AE D) = 1) :
    GlobalTheory.ThK.ConeEuler.unitArch D.host.F D.host.E l = 1 := by
  apply Units.ext
  apply LIdemEx.ae_ext
  · intro w
    rw [GlobalTheory.IdeleCyl.compInf_unitArch, hinf, Units.val_one, map_one]
  · intro v
    change compFin D.host.F D.host.E v (GlobalTheory.ThK.ConeEuler.eInf D.host.F • (l : AE D) +
      (1 - GlobalTheory.ThK.ConeEuler.eInf D.host.F) • 1) = cv D v ((1 : (AE D)ˣ) : AE D)
    rw [map_add (f := _), GlobalTheory.ThK.compFin_smul, GlobalTheory.ThK.compFin_smul, evFin_eInf, map_sub, map_one, evFin_eInf, sub_zero,
      zero_smul, zero_add, one_smul, Units.val_one]

theorem unitAt_eq_one (l : (AE D)ˣ) (v : Pl D) (hat : cv D v (l : AE D) = 1) :
    GlobalTheory.ThK.ConeEuler.unitAt D.host.E v l = 1 := by
  apply Units.ext
  change GlobalTheory.ThK.ConeEuler.eFin v • (l : AE D) + (1 - GlobalTheory.ThK.ConeEuler.eFin v) • 1 = ((1 : (AE D)ˣ) : AE D)
  have h0 : compFin D.host.F D.host.E v ((l : AE D) - 1) = 0 := by
    rw [map_sub, map_one]; exact sub_eq_zero.2 hat
  have hk := GlobalTheory.InertLagUniq.liftV_one_smul_eq_zero (E := D.host.E) v _ h0
  have e : GlobalTheory.ThK.ConeEuler.eFin v • (l : AE D) + (1 - GlobalTheory.ThK.ConeEuler.eFin v) • (1 : AE D) =
      1 + GlobalTheory.ThK.ConeEuler.eFin v • ((l : AE D) - 1) := by
    rw [sub_smul, one_smul, smul_sub]; abel
  rw [e, Units.val_one]
  change 1 + GlobalTheory.LatVac.liftV v 1 • ((l : AE D) - 1) = 1
  rw [hk, add_zero]

theorem chr_abs_one {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) {b₀ : HermE D ρ} {S : Finset (Pl D)}
    (hS : ∀ v ∉ S, GoodPl χ b₀ v) (l : (AE D)ˣ) (hA : GlobalTheory.ThK.ConeEuler.unitArch D.host.F D.host.E l = 1)
    (hAt : ∀ v ∈ S, GlobalTheory.ThK.ConeEuler.unitAt D.host.E v l = 1)
    (hmem : ∀ v ∉ S, GlobalTheory.ThK.ConeEuler.unitAt D.host.E v l ∈ GlobalTheory.ThK.unitsAt D.host.E v) :
    χ l = 1 ∧ absE D.host.F D.host.E l = 1 := by
  have key := (GlobalTheory.ThK.ConeEulerChr.chr_abs_eq_finprod χ hχ.1 l 1).2
  have hfp : (∏ᶠ v : Pl D, (χ (GlobalTheory.ThK.ConeEuler.unitAt D.host.E v l) : ℂ) *
      ((absE D.host.F D.host.E (GlobalTheory.ThK.ConeEuler.unitAt D.host.E v l) : ℝ) : ℂ) ^ 1) = 1 := by
    rw [finprod_congr (g := fun _ => (1 : ℂ)) ?_, finprod_one]
    intro v
    by_cases hv : v ∈ S
    · rw [hAt v hv]; simp
    · have hm := hmem v hv
      rw [(hS v hv).unr _ hm, GlobalTheory.ThK.absE_of_mem_unitsAt hm]; simp
  rw [hfp, hA] at key
  simp only [map_one, Circle.coe_one, NNReal.coe_one, Complex.ofReal_one, mul_one, pow_one] at key
  have habs : absE D.host.F D.host.E l = 1 := by
    have hn := congrArg norm key
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, norm_one,
      Real.norm_of_nonneg (NNReal.coe_nonneg _)] at hn
    exact_mod_cast hn
  refine ⟨?_, habs⟩
  rw [habs, NNReal.coe_one, Complex.ofReal_one, mul_one] at key
  exact Circle.coe_eq_one.1 key

theorem levi_chr {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) {b₀ : HermE D ρ} {S : Finset (Pl D)}
    (hS : ∀ v ∉ S, GoodPl χ b₀ v) (a : GL (Fin p) (AE D))
    (h1 : ∀ i j w, compInf D.host.F D.host.E w (a.1 i j) = (1 : Matrix (Fin p) (Fin p) _) i j)
    (h2 : ∀ i j, ∀ v ∈ S, cv D v (a.1 i j) = (1 : Matrix (Fin p) (Fin p) _) i j)
    (h3 : ∀ i j, ∀ v ∉ S, cv D v (a.1 i j) ∈ intLoc D.host.F D.host.E v ∧
      cv D v ((a⁻¹).1 i j) ∈ intLoc D.host.F D.host.E v) :
    χ (Matrix.GeneralLinearGroup.det a) = 1 ∧ absA D (Matrix.GeneralLinearGroup.det a) = 1 := by
  have hv0 : ((Matrix.GeneralLinearGroup.det a : (AE D)ˣ) : AE D) = (a : Matrix (Fin p) (Fin p) (AE D)).det :=
    Matrix.GeneralLinearGroup.val_det_apply a
  have hv1 : (((Matrix.GeneralLinearGroup.det a)⁻¹ : (AE D)ˣ) : AE D) =
      ((a⁻¹ : GL (Fin p) (AE D)) : Matrix (Fin p) (Fin p) (AE D)).det := by
    rw [← map_inv]; exact Matrix.GeneralLinearGroup.val_det_apply _
  have hinf : ∀ w, compInf D.host.F D.host.E w ((Matrix.GeneralLinearGroup.det a : (AE D)ˣ) : AE D) = 1 := by
    intro w
    rw [hv0, RingHom.map_det]
    have e : (compInf D.host.F D.host.E w).mapMatrix (a : Matrix (Fin p) (Fin p) (AE D)) = 1 := by
      ext i j; exact h1 i j w
    rw [e, Matrix.det_one]
  have hat : ∀ v ∈ S, cv D v ((Matrix.GeneralLinearGroup.det a : (AE D)ˣ) : AE D) = 1 := by
    intro v hv
    rw [hv0, RingHom.map_det]
    have e : (cv D v).mapMatrix (a : Matrix (Fin p) (Fin p) (AE D)) = 1 := by
      ext i j; exact h2 i j v hv
    rw [e, Matrix.det_one]
  have hint : ∀ v ∉ S, cv D v ((Matrix.GeneralLinearGroup.det a : (AE D)ˣ) : AE D) ∈ intLoc D.host.F D.host.E v ∧
      cv D v (((Matrix.GeneralLinearGroup.det a)⁻¹ : (AE D)ˣ) : AE D) ∈ intLoc D.host.F D.host.E v := by
    intro v hv
    rw [hv0, hv1, RingHom.map_det, RingHom.map_det]
    exact ⟨det_mem_subring _ _ fun i j => (h3 i j v hv).1, det_mem_subring _ _ fun i j => (h3 i j v hv).2⟩
  refine chr_abs_one hχ hS _ (unitArch_eq_one _ hinf) (fun v hv => unitAt_eq_one _ v (hat v hv)) fun v hv => ?_
  refine GlobalTheory.ThK.mem_unitsAt.2 ⟨GlobalTheory.ThK.ConeEuler.unitAt_mem v _, ?_, ?_⟩
  · rw [GlobalTheory.ThK.ConeEuler.compFin_unitAt_self]; exact (hint v hv).1
  · rw [← map_inv, GlobalTheory.ThK.ConeEuler.compFin_unitAt_self]; exact (hint v hv).2

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
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw.L.LToS



namespace PositivityTheory.Rg.Rsw.L.LToS

variable {D : D7} {a b c r t : ℕ}

theorem fix_mul_left {e : AE D} {M : Mx D a a} (hM : e • (M - 1) = M - 1) (x : Mx D a b) :
    e • (mm M x - x) = mm M x - x := by
  have h : mm M x - x = (M - 1) * x := by rw [Matrix.sub_mul, Matrix.one_mul]
  rw [h, ← Matrix.smul_mul, hM]

theorem fix_add_mul {e : AE D} {y : Mx D b c} (hy : e • y = y) (x : Mx D a b) (z : Mx D a c) :
    e • (z + mm x y - z) = z + mm x y - z := by
  rw [add_sub_cancel_left]
  show e • (x * y) = x * y
  rw [← Matrix.mul_smul, hy]

theorem fix_mul_right {e : AE D} {g : Mx D b b} (hg : e • (g - 1) = g - 1) (x : Mx D a b) :
    e • (mm x g - x) = mm x g - x := by
  have h : mm x g - x = x * (g - 1) := by rw [Matrix.mul_sub, Matrix.mul_one]
  rw [h, ← Matrix.mul_smul, hg]

theorem hc_U (e : AE D) (M : Mx D a a) (z : Mx D a b × Mx D a c) :
    (mm M (e • z.1), mm M (e • z.2)) = (e • mm M z.1, e • mm M z.2) := by
  simp only [mm, Matrix.mul_smul]

theorem hc_S (e : AE D) (y : Mx D b c) (z : Mx D a b × Mx D a c) :
    (e • z.1, e • z.2 + mm (e • z.1) y) = (e • z.1, e • (z.2 + mm z.1 y)) := by
  simp only [mm, Matrix.smul_mul, smul_add]

theorem hc_C (e : AE D) (g : Mx D c c) (z : Mx D a b × Mx D a c) :
    (e • z.1, mm (e • z.2) g) = (e • z.1, e • mm z.2 g) := by
  simp only [mm, Matrix.smul_mul]

theorem continuous_addMul (y : Mx D b c) : Continuous fun z : Mx D a b × Mx D a c => z.2 + mm z.1 y :=
  continuous_snd.add (continuous_fst.matrix_mul continuous_const)

theorem measurable_S (y : Mx D b c) : Measurable fun z : Mx D a b × Mx D a c => (z.1, z.2 + mm z.1 y) :=
  (continuous_fst.prodMk (continuous_addMul y)).measurable

theorem continuous_mulR (M : Mx D c c) : Continuous fun z : Mx D a b × Mx D a c => mm z.2 M :=
  continuous_snd.matrix_mul continuous_const

theorem measurable_C (M : Mx D c c) : Measurable fun z : Mx D a b × Mx D a c => (z.1, mm z.2 M) :=
  (continuous_fst.prodMk (continuous_mulR M)).measurable

theorem continuous_hermitian_inner_self (V : HSp D) : Continuous fun z : Mx D V.rank r × Mx D V.rank t => ip V z.1 z.1 := by
  show Continuous fun z : Mx D V.rank r × Mx D V.rank t => adj z.1 * (gA V * z.1)
  exact (continuous_adj.comp continuous_fst).matrix_mul (continuous_const.matrix_mul continuous_fst)

theorem isOrb_e {V : HSp D} {b₀ : HermE D r} {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e)
    (hee : e * e = e ∧ cA D e = e) {ν : Measure (Mx D V.rank r × Mx D V.rank t)} (hν : IsOrb V b₀ 1 ν) :
    IsOrb V b₀ e ((ν.restrict {z | IntOff S z.1 ∧ IntOff S z.2}).map fun z => (e • z.1, e • z.2)) := by
  have hA : MeasurableSet {z : Mx D V.rank r × Mx D V.rank t | IntOff S z.1 ∧ IntOff S z.2} :=
    (((isClosed_intOff S).preimage continuous_fst).inter ((isClosed_intOff S).preimage continuous_snd)).measurableSet
  have hf : Measurable fun z : Mx D V.rank r × Mx D V.rank t => (e • z.1, e • z.2) :=
    ((continuous_fst.const_smul e).prodMk (continuous_snd.const_smul e)).measurable
  have := hν.fin
  refine ⟨⟨fun K hK => ?_⟩, ?_, fun h hh => ?_, fun y hy => ?_, fun g hg => ?_⟩
  · obtain ⟨K', hK', hmem⟩ := boxP he hK
    rw [Measure.map_apply hf hK.measurableSet, Measure.restrict_apply (hf hK.measurableSet)]
    exact lt_of_le_of_lt (measure_mono fun z hz => hmem z hz.2.1 hz.2.2 hz.1) hK'.measure_lt_top
  · have hG : IsClosed {z : Mx D V.rank r × Mx D V.rank t |
        e • z.1 = z.1 ∧ e • z.2 = z.2 ∧ ip V z.1 z.1 = e • rat b₀.1 ∧ qv V b₀ z = 0} :=
      (isClosed_eq (continuous_fst.const_smul e) continuous_fst).inter
        ((isClosed_eq (continuous_snd.const_smul e) continuous_snd).inter
          ((isClosed_eq (continuous_hermitian_inner_self V) continuous_const).inter (isClosed_qv V b₀)))
    have hm : MeasurableSet {z : Mx D V.rank r × Mx D V.rank t |
        ¬ (e • z.1 = z.1 ∧ e • z.2 = z.2 ∧ ip V z.1 z.1 = e • rat b₀.1 ∧ qv V b₀ z = 0)} := hG.isOpen_compl.measurableSet
    rw [Measure.map_apply hf hm]
    refine nonpos_iff_eq_zero.1 ?_
    refine (Measure.restrict_apply_le _ _).trans (le_of_eq (measure_mono_null (fun z hz => ?_) hν.supp))
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hz ⊢
    intro hg
    apply hz
    obtain ⟨-, -, h3, h4⟩ := hg
    refine ⟨by rw [smul_smul, hee.1], by rw [smul_smul, hee.1], ?_, ?_⟩
    · rw [ip_smul hee, h3, one_smul]
    · rw [qv_smul hee, h4, smul_zero]
  · have hφ : Measurable fun z : Mx D V.rank r × Mx D V.rank t => (mm (mt V h) z.1, mm (mt V h) z.2) :=
      ((continuous_const.matrix_mul continuous_fst).prodMk (continuous_const.matrix_mul continuous_snd)).measurable
    have key := map_transport (κ := 1) hA hf hφ hφ ?_ (fun z => hc_U e (mt V h) z)
      (by rw [one_smul]; exact hν.invU h (one_smul _ _))
    · rwa [one_smul] at key
    · ext z
      simp only [Set.mem_preimage, Set.mem_ofPred_eq]
      rw [intOff_iff he (fix_mul_left hh z.1), intOff_iff he (fix_mul_left hh z.2)]
  · have key := map_transport (κ := 1) hA hf (measurable_S y) (measurable_S y) ?_
      (fun z => hc_S e y z)
      (by rw [one_smul]; exact hν.invS y (one_smul _ _))
    · rwa [one_smul] at key
    · ext z
      simp only [Set.mem_preimage, Set.mem_ofPred_eq]
      rw [intOff_iff he (fix_add_mul hy z.1 z.2)]
  · exact map_transport hA hf (measurable_C (a := V.rank) (b := r) g.1) (measurable_C (a := V.rank) (b := r) g.1)
      (by
        ext z
        simp only [Set.mem_preimage, Set.mem_ofPred_eq]
        rw [intOff_iff he (fix_mul_right hg z.2)])
      (fun z => hc_C e g.1 z) (hν.cov g (one_smul _ _))

theorem toS_of (hI : IdemEx) : ToS := by
  classical
  intro D r t V b₀ _
  obtain ⟨S₁, h₁⟩ := exists_intOff (rat b₀.1⁻¹ : Mx D r r)
  obtain ⟨S₂, h₂⟩ := exists_intOff (gA V)
  refine ⟨S₁ ∪ S₂, fun S hS e he ν hν => ⟨isOrb_e he ((hI D S).2 e he) hν, fun z hz1 hz2 =>
    ⟨?_, yv_smul ((hI D S).2 e he) V b₀ z⟩⟩⟩
  show IntOff S (mm (rat b₀.1⁻¹) (mm (adj z.1) (mm (gA V) z.2)))
  exact intOff_mul (h₁ S (Finset.union_subset_left hS))
    (intOff_mul (intOff_adj hz1) (intOff_mul (h₂ S (Finset.union_subset_right hS)) hz2))

end PositivityTheory.Rg.Rsw.L.LToS

namespace PositivityTheory.Rg.Rsw.L

theorem toS : IdemEx → ToS := LToS.toS_of

end PositivityTheory.Rg.Rsw.L

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

namespace PositivityTheory.Rg.Rsw.L

theorem approxId : IdemEx → ApproxId := fun _ => LApproxId.approxId_of LApproxId.oneD

end PositivityTheory.Rg.Rsw.L

end
end
