module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle276
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle054
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle006
import Formalism.LocalRingCardinality.DataHost
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle018
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle171
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSchwartzAOfIsSchwartzBruhat
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
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

namespace PositivityTheory.Rg.Rsw.L.LApproxId

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef (testT boxA fouA intF)

variable {F : Type} [Field F] [NumberField F]

theorem add_mem_iff_of_zero {X : Type} [AddCommGroup X] {P : Set X} (h0 : (0 : X) ∈ P) {a b : X} (hab : a = 0 ∨ b = 0) :
    a + b ∈ P ↔ a ∈ P ∧ b ∈ P := by
  rcases hab with h | h <;> subst h <;> simp [h0]

theorem box_split {S S' : Finset (HeightOneSpectrum (𝓞 F))} (hSS : S ⊆ S') {ε : AF F} (hε : IsIdF S ε)
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hU : ∀ v, (0 : Fv F v) ∈ U v) {h y : AF F} (hh : ε * h = h)
    (hy : ε * y = 0) : sndA F (h + y) ∈ boxA S' U ↔ sndA F h ∈ boxA S' U ∧ sndA F y ∈ boxA S' U := by
  have hz : ∀ v, h.2 v = 0 ∨ y.2 v = 0 := fun v => by
    by_cases hv : v ∈ S
    · exact Or.inr (ker_snd hε hy hv)
    · exact Or.inl (fix_snd hε hh hv)
  have hadd : ∀ v, (sndA F (h + y)) v = h.2 v + y.2 v := fun v => rfl
  simp only [boxA, Set.mem_ofPred_eq, hadd]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun v hv => ((add_mem_iff_of_zero (hU v) (hz v)).1 (h1 v hv)).1,
      fun v hv => ((add_mem_iff_of_zero (zero_mem _) (hz v)).1 (h2 v hv)).1⟩,
      ⟨fun v hv => ((add_mem_iff_of_zero (hU v) (hz v)).1 (h1 v hv)).2,
      fun v hv => ((add_mem_iff_of_zero (zero_mem _) (hz v)).1 (h2 v hv)).2⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact ⟨fun v hv => (add_mem_iff_of_zero (hU v) (hz v)).2 ⟨h1 v hv, h3 v hv⟩,
      fun v hv => (add_mem_iff_of_zero (zero_mem _) (hz v)).2 ⟨h2 v hv, h4 v hv⟩⟩

def tR (ρ : Ainf F → ℝ) (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (y : AF F) : ℝ :=
  ρ (fstA F y) * (boxA S U).indicator (fun _ => (1 : ℝ)) (sndA F y)

theorem testT_eq (ρ : Ainf F → ℝ) (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (y : AF F) : testT ρ S U y = ((tR ρ S U y : ℝ) : ℂ) := by
  simp only [testT, tR, Set.indicator]
  split_ifs <;> simp

theorem tR_nonneg {ρ : Ainf F → ℝ} (hρ : ∀ y, 0 ≤ ρ y) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (y : AF F) : 0 ≤ tR ρ S U y :=
  mul_nonneg (hρ _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

def bR (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (y : AF F) : ℝ :=
  (boxA S U).indicator (fun _ => (1 : ℝ)) (sndA F y)

theorem tR_split {S S' : Finset (HeightOneSpectrum (𝓞 F))} (hSS : S ⊆ S') {ε : AF F} (hε : IsIdF S ε) (ρ : Ainf F → ℝ)
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hU : ∀ v, (0 : Fv F v) ∈ U v) {h y : AF F} (hh : ε * h = h)
    (hy : ε * y = 0) : tR ρ S' U (h + y) = tR ρ S' U h * bR S' U y := by
  have hf : fstA F (h + y) = fstA F h := by
    rw [map_add (f := _), fst_eq y, ker_fst hε hy, add_zero]
  have hb := box_split hSS hε U hU hh hy
  unfold tR bR
  rw [hf]
  by_cases h1 : sndA F h ∈ boxA S' U <;> by_cases h2 : sndA F y ∈ boxA S' U
  · rw [Set.indicator_of_mem (hb.2 ⟨h1, h2⟩), Set.indicator_of_mem h1, Set.indicator_of_mem h2]; ring
  · rw [Set.indicator_of_notMem (fun h' => h2 (hb.1 h').2), Set.indicator_of_notMem h2]; ring
  · rw [Set.indicator_of_notMem (fun h' => h1 (hb.1 h').1), Set.indicator_of_notMem h1]; ring
  · rw [Set.indicator_of_notMem (fun h' => h1 (hb.1 h').1), Set.indicator_of_notMem h1]; ring

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

namespace PositivityTheory.Rg.Rsw.L.LGoodEv

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Dec PI.VolStabS.PositiveNearLattice PI.VolStabS.AdmissibleCompactSupport

variable {D : D7}


open Classical in
theorem exists_int_off {K : Set (Af D.host.F)} (hK : IsCompact K) :
    ∃ T : Finset (Pl D), ∀ z ∈ K, ∀ v ∉ T, z v ∈ v.adicCompletionIntegers D.host.F := by
  classical
  let O : Finset (Pl D) → Set (Af D.host.F) :=
    fun T => {z | ∀ v, v ∉ T → z v ∈ (v.adicCompletionIntegers D.host.F : Set (v.adicCompletion D.host.F))}
  have hO : ∀ T, IsOpen (O T) := fun T =>
    RestrictedProduct.isOpen_forall_imp_mem (R := fun v : Pl D => v.adicCompletion D.host.F)
      (A := fun v => (v.adicCompletionIntegers D.host.F : Set (v.adicCompletion D.host.F)))
      (fun v => Valued.isOpen_valuationSubring _)
  have hcov : K ⊆ ⋃ T, O T := fun z _ => Set.mem_iUnion.2
    ⟨(Filter.eventually_cofinite.1 z.2).toFinset, fun v hv => by
      by_contra h
      exact hv ((Filter.eventually_cofinite.1 z.2).mem_toFinset.2 h)⟩
  obtain ⟨T, hT⟩ := hK.elim_directed_cover O hO hcov fun T T' =>
    ⟨T ∪ T', fun z hz v hv => hz v fun h => hv (Finset.mem_union_left _ h),
      fun z hz v hv => hz v fun h => hv (Finset.mem_union_right _ h)⟩
  exact ⟨T, fun z hz v hv => hT hz v hv⟩

def sPart {a b : ℕ} (S : Finset (Pl D)) (y : Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E) :
    Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E :=
  fun i j => algebraMap (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) (indS S) * y i j


open Classical in

theorem fin_good {a b : ℕ} (g : (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E)) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ y, g y =
      if (∀ v ∉ S, ∀ i j, projV v y i j ∈ intLoc D.host.F D.host.E v)
      then g (sPart S y) else 0 := by
  classical
  obtain ⟨hlc, hcs⟩ := hg
  let B := Module.finBasis D.host.F D.host.E
  have hT1 : ∀ (i : Fin a) (j : Fin b) (k : Fin (Module.finrank D.host.F D.host.E)), ∃ T : Finset (Pl D),
      ∀ y ∈ tsupport g, ∀ v ∉ T, crd B (Af D.host.F) (y i j) k v ∈ v.adicCompletionIntegers D.host.F := by
    intro i j k
    have hc : Continuous fun y : Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E => y i j :=
      (continuous_apply j).comp (continuous_apply i)
    obtain ⟨T, hT⟩ := exists_int_off (D := D) (hcs.isCompact.image ((continuous_crd B (Af D.host.F) k).comp hc))
    exact ⟨T, fun y hy v hv => hT _ ⟨y, hy, rfl⟩ v hv⟩
  choose T1 hT1 using hT1
  have hU := invariant_mem_nhds hlc hcs
  let Lc : (Fin a → Fin b → Fin (Module.finrank D.host.F D.host.E) → Af D.host.F) →
      (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E) :=
    fun c x i => ∑ k, c x i k • ((1 : Af D.host.F) ⊗ₜ[D.host.F] B k)
  have hL : Continuous Lc := by
    refine continuous_pi fun x => continuous_pi fun i => continuous_finsetSum _ fun k _ => ?_
    exact continuous_smul.comp
      (((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply x))).prodMk continuous_const)
  have hL0 : Lc (fun _ _ _ => 0) = 0 := by
    funext x i
    simp [Lc]
  have hp : Lc ⁻¹' {u | ∀ x, g (x + u) = g x} ∈ 𝓝 (fun _ => fun _ => fun _ => (0 : Af D.host.F)) :=
    hL.continuousAt.preimage_mem_nhds (by rw [hL0]; exact hU)
  obtain ⟨W1, hW1, h1⟩ := exists_nhds_of_pi hp
  obtain ⟨W2, hW2, h2⟩ := exists_nhds_of_pi hW1
  obtain ⟨W, hW, h3⟩ := exists_nhds_of_pi hW2
  obtain ⟨T2, P, hPO, hPT, hsub⟩ := exists_box_subset hW
  have hinv : ∀ x u, (∀ i j k v, crd B (Af D.host.F) (u i j) k v ∈ P v) → g (x + u) = g x := by
    intro x u hu
    have hu' : u = Lc fun i j k => crd B (Af D.host.F) (u i j) k := by
      funext i j
      exact eq_sum_crd B (Af D.host.F) (u i j)
    rw [hu']
    exact h1 _ (fun i => h2 _ fun j => h3 _ fun k => hsub (hu i j k)) x
  have hbad := Filter.eventually_cofinite.1 (GlobalTheory.AdelicU.Cofinite.eventually_mem_intLoc_iff_repr B)
  refine ⟨(Finset.univ.biUnion fun i => Finset.univ.biUnion fun j => Finset.univ.biUnion fun k => T1 i j k) ∪ T2 ∪
    hbad.toFinset, fun S hS y => ?_⟩
  have hS1 : ∀ i j k, T1 i j k ⊆ S := fun i j k v hv => hS (Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _,
      Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, hv⟩⟩⟩)))
  have hS2 : T2 ⊆ S := fun v hv => hS (Finset.mem_union_left _ (Finset.mem_union_right _ hv))
  have hS3 : ∀ v ∉ S, ∀ z : Fv D.host.F v ⊗[D.host.F] D.host.E, z ∈ intLoc D.host.F D.host.E v ↔
      ∀ k, crd B (Fv D.host.F v) z k ∈ v.adicCompletionIntegers D.host.F := by
    intro v hv
    have h' : v ∉ hbad.toFinset := fun h => hv (hS (Finset.mem_union_right _ h))
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at h'
    exact h'
  have hcrd : ∀ z k, crd B (Af D.host.F) (z - algebraMap (Af D.host.F) _ (indS S) * z) k =
      crd B (Af D.host.F) z k - indS S * crd B (Af D.host.F) z k := by
    intro z k
    simp only [crd, ← Algebra.smul_def, map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
  split_ifs with h
  · calc g y = g (sPart S y + (y - sPart S y)) := by rw [add_sub_cancel]
      _ = g (sPart S y) := hinv _ _ fun i j k v => ?_
    have e1 : crd B (Af D.host.F) ((y - sPart S y) i j) k v =
        crd B (Af D.host.F) (y i j) k v - indS S v * crd B (Af D.host.F) (y i j) k v := by
      rw [Pi.sub_apply, Pi.sub_apply, sPart, hcrd]
      rfl
    rw [e1, indS_apply]
    by_cases hv : v ∈ S
    · rw [if_pos hv, one_mul, sub_self]
      exact zero_mem _
    · rw [if_neg hv, zero_mul, sub_zero, hPT v fun h' => hv (hS2 h'), mem_intSub, ← crd_projV]
      exact (hS3 v hv _).1 (h v hv i j) k
  · push Not at h
    obtain ⟨v, hv, i, j, hij⟩ := h
    obtain ⟨k, hk⟩ : ∃ k, crd B (Fv D.host.F v) (projV v y i j) k ∉ v.adicCompletionIntegers D.host.F := by
      by_contra hc
      push Not at hc
      exact hij ((hS3 v hv _).2 hc)
    rw [crd_projV] at hk
    refine image_eq_zero_of_notMem_tsupport fun hy => hk ?_
    exact hT1 i j k y hy v fun h' => hv (hS1 i j k h')

end PositivityTheory.Rg.Rsw.L.LGoodEv

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




namespace PositivityTheory.Rg.Rsw.L.LBumpEx

variable {D : D7}

abbrev AfE (D : D7) : Type := Af D.host.F ⊗[D.host.F] D.host.E

abbrev Ev (D : D7) (v : Pl D) : Type := Fv D.host.F v ⊗[D.host.F] D.host.E

def cf (v : Pl D) : AfE D →ₐ[D.host.F] Ev D v :=
  Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E)

theorem cf_tmul (v : Pl D) (a : Af D.host.F) (x : D.host.E) : cf v (a ⊗ₜ[D.host.F] x) = evalV D.host.F v a ⊗ₜ[D.host.F] x :=
  rfl

theorem cv_eq (v : Pl D) (x : AE D) : cv D v x = cf v (finPart D x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a y => rfl
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), map_add (f := _), hx, hy]

theorem cf_mem_of_mem {z : AfE D} (hz : z ∈ intAE D) (v : Pl D) : cf v z ∈ intLoc D.host.F D.host.E v := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    rw [cf_tmul]
    exact tmul_mem_intLoc (ha v) x
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

def pr (φ : D.host.E →ₗ[D.host.F] D.host.F) : AfE D →ₗ[D.host.F] Af D.host.F :=
  (TensorProduct.rid D.host.F (Af D.host.F)).toLinearMap ∘ₗ φ.lTensor (Af D.host.F)

theorem pr_tmul (φ : D.host.E →ₗ[D.host.F] D.host.F) (a : Af D.host.F) (x : D.host.E) :
    pr φ (a ⊗ₜ[D.host.F] x) = φ x • a := by
  rw [pr, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul]

def aux₃ (φ : D.host.E →ₗ[D.host.F] D.host.F) (v : Pl D) : Ev D v →ₗ[D.host.F] Fv D.host.F v :=
  (TensorProduct.rid D.host.F (Fv D.host.F v)).toLinearMap ∘ₗ φ.lTensor (Fv D.host.F v)

theorem trace_projection_tmul (φ : D.host.E →ₗ[D.host.F] D.host.F) (v : Pl D) (a : Fv D.host.F v) (x : D.host.E) :
    aux₃ φ v (a ⊗ₜ[D.host.F] x) = φ x • a := by
  rw [aux₃, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul]

theorem evalV_pr (φ : D.host.E →ₗ[D.host.F] D.host.F) (v : Pl D) (y : AfE D) :
    evalV D.host.F v (pr φ y) = aux₃ φ v (cf v y) := by
  induction y using TensorProduct.inductionOn with
  | tmul a x => rw [pr_tmul, cf_tmul, trace_projection_tmul, AlgHom.map_smul_of_tower]
  | add y y' hy hy' => rw [LinearMap.map_add (f := _), map_add (f := _), map_add (f := _), LinearMap.map_add (f := _), hy, hy']

theorem trace_projection_mem_integers (φ : D.host.E →ₗ[D.host.F] D.host.F) (hφ : ∀ x : 𝓞 D.host.E, φ x ∈ (algebraMap (𝓞 D.host.F) D.host.F).range)
    (v : Pl D) {w : Ev D v} (hw : w ∈ intLoc D.host.F D.host.E v) : aux₃ φ v w ∈ v.adicCompletionIntegers D.host.F := by
  refine intLoc_induction (p := fun w => aux₃ φ v w ∈ v.adicCompletionIntegers D.host.F) (fun a ha x => ?_) ?_
    (fun y z hy hz => ?_) (fun y hy => ?_) hw
  · obtain ⟨r, hr⟩ := hφ x
    rw [trace_projection_tmul, ← hr, Algebra.smul_def]
    exact mul_mem (v.coe_mem_adicCompletionIntegers r) ha
  · rw [LinearMap.map_zero]; exact zero_mem _
  · rw [LinearMap.map_add (f := _)]; exact add_mem hy hz
  · rw [LinearMap.map_neg]; exact neg_mem hy

theorem sum_pr {k : ℕ} (s : Fin k → 𝓞 D.host.E) (φ : Fin k → D.host.E →ₗ[D.host.F] D.host.F)
    (hsum : ∀ x, ∑ j, φ j x • (s j : D.host.E) = x) (y : AfE D) :
    ∑ j, pr (φ j) y ⊗ₜ[D.host.F] ((s j : D.host.E)) = y := by
  induction y using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [pr_tmul, TensorProduct.smul_tmul]
    rw [← TensorProduct.tmul_sum, hsum x]
  | add y y' hy hy' => simp only [LinearMap.map_add (f := _), TensorProduct.add_tmul, Finset.sum_add_distrib, hy, hy']

theorem mem_of_cf_mem {z : AfE D} (hz : ∀ v : Pl D, cf v z ∈ intLoc D.host.F D.host.E v) : z ∈ intAE D := by
  obtain ⟨k, s, φ, hφ, hsum⟩ := GlobalTheory.AdelicU.SelfDual.exists_dualFamily_integers (F := D.host.F) (E := D.host.E)
  rw [← sum_pr s φ hsum z]
  refine sum_mem fun j _ => AddSubgroup.subset_closure ⟨pr (φ j) z, fun v => ?_, s j, rfl⟩
  rw [evalV_pr]
  exact trace_projection_mem_integers (φ j) (fun x => hφ x j) v (hz v)

theorem exists_nat_mul_mem {Q : Set (AfE D)} (hQ : IsCompact Q) :
    ∃ N : ℕ, 0 < N ∧ ∀ q ∈ Q, (N : AfE D) * q ∈ intAE D := by
  have : IsModuleTopology (Af D.host.F) (AfE D) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AfE D) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  obtain ⟨t, ht⟩ := hQ.elim_finite_subcover (fun n : ℕ => {q : AfE D | ((n + 1 : ℕ) : AfE D) * q ∈ intAE D})
    (fun n => (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage (continuous_const.mul continuous_id))
    (fun q _ => by
      obtain ⟨n, hn, h⟩ := GlobalTheory.IwaPlace.SdComap.exists_natCast_mul_mem_intAE q
      exact Set.mem_iUnion.2 ⟨n - 1, by rwa [Nat.sub_add_cancel hn]⟩)
  refine ⟨∏ n ∈ t, (n + 1), Finset.prod_pos fun _ _ => Nat.succ_pos _, fun q hq => ?_⟩
  obtain ⟨n, hn, hq'⟩ := Set.mem_iUnion₂.1 (ht hq)
  rw [← Finset.mul_prod_erase t _ hn, Nat.cast_mul, mul_comm ((n + 1 : ℕ) : AfE D), mul_assoc]
  exact GlobalTheory.HostAdeleIso.intAE_mul_mem D (GlobalTheory.IwaPlace.SdComap.natCast_mem_intAE _) hq'

def U (S : Finset (Pl D)) (ef : AfE D) (N m n : ℕ) : AddSubgroup (Matrix (Fin m) (Fin n) (AfE D)) where
  carrier := {w | (∀ v ∉ S, ∀ i j, cf v (w i j) ∈ intLoc D.host.F D.host.E v) ∧ ∀ i j, (N : AfE D) * (ef * w i j) ∈ intAE D}
  add_mem' := fun {a b} ha hb => ⟨fun v hv i j => by
      rw [Matrix.add_apply, map_add (f := _)]; exact add_mem (ha.1 v hv i j) (hb.1 v hv i j),
    fun i j => by rw [Matrix.add_apply, mul_add, mul_add]; exact add_mem (ha.2 i j) (hb.2 i j)⟩
  zero_mem' := ⟨fun v _ i j => by rw [Matrix.zero_apply, map_zero]; exact zero_mem _,
    fun i j => by rw [Matrix.zero_apply, mul_zero, mul_zero]; exact zero_mem _⟩
  neg_mem' := fun {a} ha => ⟨fun v hv i j => by rw [Matrix.neg_apply, map_neg]; exact neg_mem (ha.1 v hv i j),
    fun i j => by rw [Matrix.neg_apply, mul_neg, mul_neg]; exact neg_mem (ha.2 i j)⟩

theorem mem_U {S : Finset (Pl D)} {ef : AfE D} {N m n : ℕ} {w : Matrix (Fin m) (Fin n) (AfE D)} :
    w ∈ U S ef N m n ↔ (∀ v ∉ S, ∀ i j, cf v (w i j) ∈ intLoc D.host.F D.host.E v) ∧
      ∀ i j, (N : AfE D) * (ef * w i j) ∈ intAE D := Iff.rfl


open Classical in
theorem mem_U_iff {S : Finset (Pl D)} {ef : AfE D} (hef : ef * ef = ef)
    (hS : ∀ v : Pl D, cf v ef = if v ∈ S then 1 else 0) {N m n : ℕ} {w : Matrix (Fin m) (Fin n) (AfE D)}
    (hw : ∀ v ∉ S, ∀ i j, cf v (w i j) ∈ intLoc D.host.F D.host.E v) :
    w ∈ U S ef N m n ↔ (Matrix.of fun i j => ef * w i j) ∈ U S ef N m n := by
  have h2 : ∀ i j, (N : AfE D) * (ef * (Matrix.of fun i j => ef * w i j) i j) = (N : AfE D) * (ef * w i j) :=
    fun i j => by rw [Matrix.of_apply, ← mul_assoc ef ef, hef]
  rw [mem_U, mem_U]
  simp only [h2]
  refine ⟨fun h => ⟨fun v hv i j => ?_, h.2⟩, fun h => ⟨hw, h.2⟩⟩
  rw [Matrix.of_apply, map_mul, hS v, if_neg hv, zero_mul]
  exact zero_mem _

end PositivityTheory.Rg.Rsw.L.LBumpEx

end
end
