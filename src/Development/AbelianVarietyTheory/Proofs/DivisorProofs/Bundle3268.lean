module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3238
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueUniformisedFourierFrameAbsOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1304
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1492
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2636
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3239
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2912
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1564
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2638
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2702
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2703
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsBundleIsoExtendingGeneric
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3241
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.OLinRosati

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}


omit [IsDomain R] in
theorem thickMap_pullback_map {G : Over (Sp R)} (b : G ⟶ G) (e : ℕ) :
    thickMap R I e G ≫ ((Over.pullback (thick R I (e + 1))).map b).left =
      ((Over.pullback (thick R I e)).map b).left ≫ thickMap R I e G := by
  apply pullback.hom_ext <;>
    simp [thickMap, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc]

theorem linEnd_act {D : DegData R I} {O : Type} [Ring O] [StarRing O] [Module O D.toPre.X] {o : D.toPre.OAct O}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {U : UnifPre I D A G}
    {oA : A.OAct O} {oG : RingAct G O} (h : U.OLinear O o oA oG) (a : O) :
    LinEnd U (o.onB.act a) (DistribSMul.toAddMonoidHom D.toPre.X (star a)) (oG.act a) := by
  haveI := oG.hom a
  refine ⟨oG.hom a, fun e => inferInstance, fun e => thickMap_pullback_map _ e, fun e => h.q_lin e a, fun e => ?_⟩
  exact h.i_lin e a

theorem endData_act {D : DegPre R} {O : Type} [Ring O] [StarRing O] [Module O D.X] (o : D.OAct O) (a : O) :
    EndData D (o.onB.act a) (o.onB.act (star a)) (DistribSMul.toAddMonoidHom D.X a)
      (DistribSMul.toAddMonoidHom D.X (star a)) :=
  ⟨o.onB.hom a, o.onB.hom (star a), o.onB.rosati a, o.c_lin a, o.c_lin (star a), o.tau_bal a⟩

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (D : DegData R (maximalIdeal R)) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal R) D A G) (oA : A.OAct O) (oG : RingAct G O), IsSemiAbelian G → U.toUnifPre.OLinear O o oA oG → ∀ a : O, LBIso (cubeLB G ![fst G G ≫ oG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ oG.act (star a)] U.LG.L) := by
  intro R _ _ _ hR D O _ _ _ o A G _ _ U oA oG hG hlin a
  have hB : Base R := ⟨⟨hR.1, inferInstance, hR.2.1, hR.2.2.1⟩, hR.2.2.2⟩
  have h₁ := linEnd_act hlin a
  have h₂ := linEnd_act hlin (star a)
  rw [star_star] at h₂
  exact linEnd_adjoint_lbIso R hB D A G hG U _ _ _ _ (endData_act o a) _ _ h₁ h₂

end GlobalTheory.Mum.OLinRosati
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.key_value_uniformised_fourier_frame_abs_one : ∀ κ : Rule, Rule4 κ → KapF κ := by
  first | exact @GlobalTheory.MBLow.KapFPf.kapF_of_rule4 | exact GlobalTheory.MBLow.KapFPf.kapF_of_rule4 | (intros; apply GlobalTheory.MBLow.KapFPf.kapF_of_rule4 <;> assumption) | exact @GlobalTheory.MBLow.KapFPf.deform_of_series | exact GlobalTheory.MBLow.KapFPf.deform_of_series | (intros; apply GlobalTheory.MBLow.KapFPf.deform_of_series <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem finsum_weighted_regroup_along_fibres {A B : Type} (π : A → B) (m : A → ℤ) (n : B → ℤ) (d : A → ℕ) (g : A → ℝ) (h : B → ℝ)
    (P : B → Prop) (hm : (Function.support m).Finite) (hn : (Function.support n).Finite)
    (hP : ∀ z, n z ≠ 0 → P z) (hs : ∀ z, P z → ∑ᶠ (w : A) (_ : π w = z), m w * (d w : ℤ) = n z)
    (h₁ : ∀ w, m w ≠ 0 → P (π w) → g w = d w * h (π w)) (h₀ : ∀ w, m w ≠ 0 → ¬ P (π w) → g w = 0) :
    ∑ᶠ w, (m w : ℝ) * g w = ∑ᶠ z, (n z : ℝ) * h z := by
  classical
  set S := hm.toFinset with hS
  set T := hn.toFinset ∪ S.image π with hT
  have hmS : ∀ w, m w ≠ 0 ↔ w ∈ S := fun w => by simp [hS]
  rw [finsum_eq_sum_of_support_subset (s := S) _ (fun w hw => by
      have : m w ≠ 0 := fun h0 => hw (by simp [h0])
      exact Finset.mem_coe.2 ((hmS w).1 this)),
    finsum_eq_sum_of_support_subset (s := T) _ (fun z hz => by
      have : n z ≠ 0 := fun h0 => hz (by simp [h0])
      simp [hT, this]),
    ← Finset.sum_fiberwise_of_maps_to (s := S) (t := T) (g := π) (fun w hw => by
      simp only [hT, Finset.mem_union]; exact Or.inr (Finset.mem_image_of_mem _ hw))]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : P z
  · have e : ∑ᶠ (w : A) (_ : π w = z), m w * (d w : ℤ) = ∑ w ∈ S.filter (fun w => π w = z), m w * (d w : ℤ) := by
      refine finsum_mem_eq_sum_of_inter_support_eq (s := {w | π w = z}) _ ?_
      ext w
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Function.mem_support, Finset.coe_filter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨(hmS w).1 (left_ne_zero_of_mul h2), h1⟩, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1.2, h2⟩
    rw [← hs z hz, e]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun w hw => ?_
    obtain ⟨hw', rfl⟩ := Finset.mem_filter.1 hw
    rw [h₁ w ((hmS w).2 hw') hz, mul_assoc]
  · have e : n z = 0 := by
      by_contra h'
      exact hz (hP z h')
    rw [e, Int.cast_zero, zero_mul]
    refine Finset.sum_eq_zero fun w hw => ?_
    obtain ⟨hw', rfl⟩ := Finset.mem_filter.1 hw
    rw [h₀ w ((hmS w).2 hw') hz, mul_zero]

theorem finsum_cycInt_push : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → IsProjOver q → topologicalKrullDim Y = (e + 1 : ℕ) → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → ∀ (Δ : CartierDiv X) (Δ' : CartierDiv Y), (∀ z : X, Order.coheight z = 1 → ∑ᶠ (w : Y) (_ : π w = z), Δ'.mult w * (π.residueDegree w : ℤ) = Δ.mult z) → ∀ (L : Fin e → MLine p σ) (f : CxPts p σ → ℝ), Measurable f → ∑ᶠ w, (Δ'.mult w : ℝ) * cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w = ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L f z := by
  intro F _ X Y _ _ _ _ p q σ e hp hX hq hY π hπ _ Δ Δ' hΔ L f hf
  have hc : ∀ {Z : Scheme.{0}} {s : Z ⟶ Sp F}, IsProjOver s → CompactSpace Z := by
    rintro Z _ ⟨m, i, hi, rfl⟩
    have := isProper_str F m
    have : IsProper (i ≫ PSpace.str F m) := inferInstance
    exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str F m)
  haveI := hc hp
  haveI := hc hq
  have key := fun (w : Y) (hw : Δ'.mult w ≠ 0) => GlobalTheory.T.mixedChernIntegral_pointClosure_pullback F X Y p q σ hp hq π hπ e L f hf w
    ((GlobalTheory.T.coheight_eq_one_iff_closure_dim_projective F Y q e hq hY w).1 (CartierDiv.coheight_eq_one_of_mult_ne_zero (D := Δ') hw))
  exact finsum_weighted_regroup_along_fibres π Δ'.mult Δ.mult (fun w => π.residueDegree w) _ _ (fun z => Order.coheight z = 1)
    Δ'.finite_support_mult Δ.finite_support_mult
    (fun z hz => CartierDiv.coheight_eq_one_of_mult_ne_zero (D := Δ) hz) hΔ
    (fun w hw h => (key w hw).1 ((GlobalTheory.T.coheight_eq_one_iff_closure_dim_projective F X p e hp hX _).1 h))
    (fun w hw h => (key w hw).2 fun h' => h ((GlobalTheory.T.coheight_eq_one_iff_closure_dim_projective F X p e hp hX _).2 h'))

end GlobalTheory.Mix
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem GlobalTheory.Mix.part_le_add_of_dens_add {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (L₁ L₂ L₃ : Fin D → MLine p σ)
    (h : ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, dens L₁ c y = dens L₂ c y + dens L₃ c y) (ε : ℤˣ) :
    part L₁ ε ≤ part L₂ ε + part L₃ ε := by
  unfold part glueMeas
  refine iSup_le fun c => ?_
  refine le_trans ?_ (add_le_add
    (le_iSup (fun c : AlgChart p σ D => chartMeas c.e fun y => ENNReal.ofReal ((ε : ℤ) * dens L₂ c y)) c)
    (le_iSup (fun c : AlgChart p σ D => chartMeas c.e fun y => ENNReal.ofReal ((ε : ℤ) * dens L₃ c y)) c))
  refine Measure.le_iff.2 fun A hA => ?_
  have hB : MeasurableSet (c.e.source ∩ A) := c.e.open_source.measurableSet.inter hA
  have hI := GlobalTheory.ChartGlue.measurableSet_image c.e hB inter_subset_left
  have hsub : c.e '' (c.e.source ∩ A) ⊆ c.e.target := fun _ ⟨y, hy, e⟩ => e ▸ c.e.map_source hy.1
  have hcont : ContinuousOn (fun v => dens L₂ c (c.e.symm v)) c.e.target :=
    (GlobalTheory.T.continuousOn_mixedChernFormDensityInChart k X p σ D L₂ c).comp c.e.continuousOn_symm c.e.mapsTo_symm
  have hm : AEMeasurable (fun v => ENNReal.ofReal (((ε : ℤ) : ℝ) * dens L₂ c (c.e.symm v)))
      (volume.restrict (c.e '' (c.e.source ∩ A))) :=
    (((hcont.aemeasurable c.e.open_target.measurableSet).const_mul _).ennreal_ofReal).mono_measure
      (Measure.restrict_mono hsub le_rfl)
  rw [Measure.add_apply, chartMeas_apply _ _ hA, chartMeas_apply _ _ hA, chartMeas_apply _ _ hA,
    ← lintegral_add_left' hm]
  refine setLIntegral_mono' hI fun v hv => ?_
  beta_reduce
  rw [h c _ (c.e.map_target (hsub hv)), mul_add]
  exact ENNReal.ofReal_add_le

theorem GlobalTheory.Mix.int_add_of_dens_add : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [SecondCountableTopology (CxPts p σ)] (D : ℕ) (L₁ L₂ L₃ : Fin D → MLine p σ), (∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, dens L₁ c y = dens L₂ c y + dens L₃ c y) → ∀ f : CxPts p σ → ℝ, (Intg L₂ f → Intg L₃ f → Intg L₁ f) ∧ (Intg L₁ f → Intg L₂ f → Intg L₃ f → Mix.int L₁ f = Mix.int L₂ f + Mix.int L₃ f) := by
  intro k _ X p σ _ D L₁ L₂ L₃ h f
  refine ⟨fun h₂ h₃ => ⟨(h₂.1.add_measure h₃.1).mono_measure (GlobalTheory.Mix.part_le_add_of_dens_add L₁ L₂ L₃ h 1),
    (h₂.2.add_measure h₃.2).mono_measure (GlobalTheory.Mix.part_le_add_of_dens_add L₁ L₂ L₃ h (-1))⟩, fun h₁ h₂ h₃ => ?_⟩
  have := GlobalTheory.T.linear_relation_mixed_densities_integrals k X p σ D (Fin 3) ![1, -1, -1] ![L₁, L₂, L₃]
    (fun c y hy => by
      rw [Fin.sum_univ_three]
      show 1 * dens L₁ c y + -1 * dens L₂ c y + -1 * dens L₃ c y = 0
      rw [h c y hy]; ring) f
    (fun i => by
      fin_cases i
      · exact h₁
      · exact h₂
      · exact h₃)
  rw [Fin.sum_univ_three] at this
  change 1 * Mix.int L₁ f + -1 * Mix.int L₂ f + -1 * Mix.int L₃ f = 0 at this
  linarith
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CycFin

theorem cycle_facts : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) (p : X ⟶ Sp F) (σ : F →+* ℂ), IsProjOver p → ∀ (e : ℕ) (L : Fin e → MLine p σ) (z : X), topologicalKrullDim (closure ({z} : Set X)) = e → (∀ ε : ℤˣ, IsFiniteMeasure (part (fun i => (L i).pull (closι z) rfl) ε)) ∧ (∀ f : CxPts p σ → ℝ, Continuous f → CycIntg L f z) ∧ (∀ (U : X.Opens), z ∈ U → ∀ ε : ℤˣ, part (fun i => (L i).pull (closι z) rfl) ε (ptMap (closι z) rfl σ ⁻¹' ptsIn p σ U)ᶜ = 0) ∧ ∀ (M : MLine p σ) (s : M.B.Sec), z ∈ nonzeroLocus s → CycIntg L (M.logSec s) z := by
  intro hP F _ X p σ hp e L z hdim
  obtain ⟨hint, hgen, hdimeq, -⟩ := GlobalTheory.T.reducedClosureOfPoint_properties X z
  haveI := hint
  have hp' : IsProjOver (closι z ≫ p) := by
    obtain ⟨N, φ, hφ, rfl⟩ := hp
    exact ⟨N, closι z ≫ φ, inferInstance, Category.assoc _ _ _⟩
  haveI : IsLocallyNoetherian (clos z) := by
    obtain ⟨N, ι, _, -⟩ := hp'
    exact LocallyOfFiniteType.isLocallyNoetherian (ι ≫ PSpace.str F N)
  have hd : topologicalKrullDim (clos z) = ((e : ℕ) : WithBot ℕ∞) := hdimeq.trans hdim
  have H1 := GlobalTheory.T.mixedChernMeasure_finite_integrable_projective hP F (clos z) (closι z ≫ p) σ e hp' hd (fun i => (L i).pull (closι z) rfl)
  have hpre : ∀ U : X.Opens, ptMap (closι z) rfl σ ⁻¹' ptsIn p σ U = ptsIn (closι z ≫ p) σ (closι z ⁻¹ᵁ U) := by
    intro U
    ext y
    simp only [Set.mem_preimage, mem_ptsIn]
    rfl
  refine ⟨H1.1, fun f hf => H1.2 _ (hf.comp (PtsOver.continuous_map _ _ _)), ?_, ?_⟩
  · intro U hU ε
    have hgU : genericPoint (clos z) ∈ closι z ⁻¹ᵁ U := by
      show closι z (genericPoint (clos z)) ∈ U
      rw [hgen]; exact hU
    rw [hpre U]
    exact GlobalTheory.T.mixedChernFormSignedPartMeasure_compl_open_genericPoint_eq_zero F (clos z) (closι z ≫ p) σ σ.injective hp' e _ ε _ hgU
  · intro M s hs
    obtain ⟨s', hnz, hnsq, -⟩ := GlobalTheory.T.exists_pullback_section_zeros_norm_multiplicities F X (clos z) p (closι z ≫ p) σ (closι z) rfl M s
    have hgs : genericPoint (clos z) ∈ nonzeroLocus s' := by
      rw [hnz]
      show closι z (genericPoint (clos z)) ∈ nonzeroLocus s
      rw [hgen]; exact hs
    have H := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP F (clos z) (closι z ≫ p) σ e hp' hd (fun i => (L i).pull (closι z) rfl)
      (M.pull (closι z) rfl) s' hgs
    have he : (M.pull (closι z) rfl).logSec s' = fun y => M.logSec s (ptMap (closι z) rfl σ y) := by
      funext y
      simp only [MLine.logSec, hnsq]
    unfold CycIntg
    rw [← he]
    exact H

end GlobalTheory.CycFin
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaConstants_projectively_integral_normalModels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp (ratHull S.R) ⟶ Xo.XF c), UOver Xo c ρ.P (toRat S.R) u → ∀ (M : RatModel o' Ω) (g : M.Z ⟶ PSpace o n), Geo.Tor.IsNormalScheme M.Z → M.pt ≫ g = spMap (ratHull S.R).val.toRingHom ≫ u ≫ f → M.HasDiv S.th := by
  first | exact @GlobalTheory.UMin.thetaInt_hasDiv | exact GlobalTheory.UMin.thetaInt_hasDiv | (intros; apply GlobalTheory.UMin.thetaInt_hasDiv <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.OmExt

theorem thList_cast {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))) (m : ℕ)
    {K : Type} [Field K] {x y : Sp K ⟶ S} (e : x = y) (θ : SecAt G L x) {N : ℕ} (pt : Fin N → (Over.mk x ⟶ G))
    (c : Fin N → K) (H : ThList G L ρ m x θ pt c) : ∃ pt' : Fin N → (Over.mk y ⟶ G), ThList G L ρ m y (e ▸ θ) pt' c := by
  subst e; exact ⟨pt, H⟩

theorem inj_comp {R V : Type} [CommRing R] [CommRing V] [IsDomain V] (φ : R →+* V) (hφ : Function.Injective φ) :
    Function.Injective ((algebraMap V (FractionRing V)).comp φ) := by
  rw [RingHom.coe_comp]; exact (IsFractionRing.injective V (FractionRing V)).comp hφ

theorem exists_fracMap {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V)
    (hφ : Function.Injective φ) : ∃ φK : FractionRing R →+* FractionRing V,
      φK.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ :=
  ⟨IsFractionRing.lift (inj_comp φ hφ), RingHom.ext fun r => by
    rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]⟩

theorem secAt_ext {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) {R : Type} [CommRing R] {x : Sp R ⟶ S}
    {τ₁ τ₂ : SecAt G L x} (h : SecM.ofSec G τ₁ = SecM.ofSec G τ₂) : τ₁ = τ₂ :=
  ThetaRuleCompare.sec_ext fun j => congrFun (congrArg Subtype.val h) j

theorem cast_pullS {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) {Z : Scheme.{0}} {T : Over S}
    (σ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T)) {y₁ y₂ : Z ⟶ S} (e : y₁ = y₂) (u₁ : Over.mk y₁ ⟶ T) (u₂ : Over.mk y₂ ⟶ T)
    (hu : u₁.left = u₂.left) :
    SecM.ofSec G (VVRank.pullS G _ u₂ σ) = SecM.ofSec G (e ▸ VVRank.pullS G _ u₁ σ) := by
  subst e
  obtain rfl : u₁ = u₂ := Over.OverMorphism.ext hu
  rfl

theorem pull_pull_cast {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) {R V K K' : Type} [CommRing R]
    [CommRing V] [CommRing K] [CommRing K'] (χ : Sp R ⟶ S) (σ : SecAt G L χ) (φ : R →+* V) (a : R →+* K)
    (b : V →+* K') (φK : K →+* K') (h : spMap φK ≫ spMap a ≫ χ = spMap b ≫ spMap φ ≫ χ)
    (hc : φK.comp a = b.comp φ) :
    SecM.ofSec G (SecAt.pull G L (SecAt.pull G L σ φ) b) = SecM.ofSec G (h ▸ SecAt.pull G L (SecAt.pull G L σ a) φK) := by
  simp only [SecAt.pull]
  rw [ThetaRuleCompare.pullS_comp, ThetaRuleCompare.pullS_comp]
  refine cast_pullS G L σ h _ _ ?_
  simp only [Over.comp_left, Over.homMk_left]
  rw [← spMap_comp, ← spMap_comp, hc]

theorem secAt_eq_of_generic {S : Scheme.{0}} (G : Over S) [GrpObj G] [Flat G.hom] (L : LB G.left) {V : Type}
    [CommRing V] [IsDomain V] (x : Sp V ⟶ S) (τ₁ τ₂ : SecAt G L x)
    (h : SecAt.pull G L τ₁ (algebraMap V (FractionRing V)) = SecAt.pull G L τ₂ (algebraMap V (FractionRing V))) :
    τ₁ = τ₂ := by
  have hDom : IsDominant (spMap (algebraMap V (FractionRing V))) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V))).trans_le bot_le)⟩
  have hSD : IsSchemeTheoreticallyDominant (spMap (algebraMap V (FractionRing V))) :=
    (isSchemeTheoreticallyDominant_iff_isDominant _).2 hDom
  have hFl : Flat (fst (Over.mk x) G).left := inferInstanceAs (Flat (pullback.fst x G.hom))
  let ιK : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ x) ⟶ Over.mk x :=
    Over.homMk (spMap (algebraMap V (FractionRing V))) rfl
  have hP := ThetaRuleCompare.isPullback_whisker (A := G) ιK
  refine ThetaRuleCompare.sec_ext fun j => BundleExt.fn_ext_dense (spMap (algebraMap V (FractionRing V)))
    (fst (Over.mk x) G).left fun Z ρ r z hrz hz => ?_
  let ρ' : Z ⟶ (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ x) ⊗ G).left := hP.lift ρ r hrz.symm
  have hfac : ρ' ≫ (ιK ▷ G).left = ρ := hP.lift_fst _ _ _
  have hz' : ρ' z ∈ (LPow G L ((1 : ℕ) : ℤ) (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ x))).U j :=
    ThetaRuleCompare.chart_ge ιK j (show (ιK ▷ G).left (ρ' z) ∈ _ by rw [← Scheme.Hom.comp_apply, hfac]; exact hz)
  rw [← hfac, ← ThetaRuleCompare.gs_pullS ιK τ₁ ρ' z j hz', ← ThetaRuleCompare.gs_pullS ιK τ₂ ρ' z j hz']
  exact congrArg (fun u : SecAt G L (spMap (algebraMap V (FractionRing V)) ≫ x) => gs ρ' z _ (u.f j)) h

open GlobalTheory.VVRank GlobalTheory.EmbPull TopologicalSpace in
theorem mem_nonzeroLocus_of_pullS {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (a : ℤ) {T T' : Over S}
    (h : T' ⟶ T) (th : LB.Sec (LPow G L a T)) (z : (T' ⊗ G).left) (hz : z ∈ nonzeroLocus (VVRank.pullS G a h th)) :
    (h ▷ G).left z ∈ nonzeroLocus th := by
  obtain ⟨j, hj, u⟩ := (mem_nonzeroLocus _ z).1 hz
  have q := gs_pullTo (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => a) th (h ▷ G).left
    (fun _ => whisker_snd_left G h) (𝟙 _) z j hj
  rw [Category.id_comp] at q
  have q' := q.trans (gs_stalkMap (h ▷ G).left z _ (wchart_le_of_eq _ (fun _ => whisker_snd_left G h) j hj) _)
  refine (mem_nonzeroLocus _ _).2 ⟨j, wchart_le_of_eq (φ := fun _ : Fin 1 => (snd T G).left) _
    (fun _ => whisker_snd_left G h) j hj, ?_⟩
  exact (isUnit_map_iff _ _).1 (q' ▸ u)

theorem spMap_closedPoint {R : Type} [CommRing R] (s : PrimeSpectrum R) {V : Type} [CommRing V] [IsLocalRing V]
    (φ₀ : Localization.AtPrime s.asIdeal →+* V) [IsLocalHom φ₀] :
    (spMap (φ₀.comp (algebraMap R (Localization.AtPrime s.asIdeal)))).base (IsLocalRing.closedPoint V) = s := by
  show PrimeSpectrum.comap (φ₀.comp (algebraMap R (Localization.AtPrime s.asIdeal))) (IsLocalRing.closedPoint V) = s
  rw [PrimeSpectrum.comap_comp_apply, IsLocalRing.comap_closedPoint]
  ext1
  rw [PrimeSpectrum.comap_asIdeal]
  exact Localization.AtPrime.under_maximalIdeal

theorem om_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (g m N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (χ : Sp R ⟶ S) (θ : SecAt t.G t.PP.L (spMap (algebraMap R (FractionRing R)) ≫ χ)) (pt : Fin N → (Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ t.G)) (c : Fin N → R), Odd m → 3 ≤ m → IsUnit (m : R) → PolFib t.G t.PP.L g (spMap (algebraMap R (FractionRing R)) ≫ χ) → ThList t.G t.PP.L t.PP.rig m _ θ pt (fun a => algebraMap R (FractionRing R) (c a)) → (∃ a, IsUnit (c a)) → ∃ σ : SecAt t.G t.PP.L χ, SecM.ofSec t.G (SecAt.pull t.G t.PP.L σ (algebraMap R (FractionRing R))) = SecM.ofSec t.G θ ∧ ∀ s : Sp R, ∃ z : (Over.mk χ ⊗ t.G).left, (fst (Over.mk χ) t.G).left z = s ∧ z ∈ nonzeroLocus σ := by
  intro E _ _ _ H S t g m N R _ _ _ _ _ χ θ pt c hodd h3 hm hPol hT hunit
  have key : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (φ : R →+* V)
      (φK : FractionRing R →+* FractionRing V)
      (h : spMap φK ≫ spMap (algebraMap R (FractionRing R)) ≫ χ = spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ),
      φK.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ →
      ∃ σ : SecAt t.G t.PP.L (spMap φ ≫ χ), SecM.ofSec t.G (SecAt.pull t.G t.PP.L σ (algebraMap V (FractionRing V))) =
        SecM.ofSec t.G (h ▸ SecAt.pull t.G t.PP.L θ φK) ∧ NZ t.G t.PP.L (spMap φ ≫ χ) σ := by
    intro V _ _ _ hV φ φK h hc
    obtain ⟨pt₁, -, hT₁⟩ := GlobalTheory.T.isThetaConstantListOfFibre_pullback_field_extension S t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen m N _ _ φK _ θ pt _ hT
    obtain ⟨pt₂, hT₂⟩ := thList_cast t.G t.PP.L t.PP.rig m h _ pt₁ _ hT₁
    have hPF : PolFib t.G t.PP.L g (spMap φK ≫ spMap (algebraMap R (FractionRing R)) ≫ χ) :=
      (GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback S S t.G t.PP.L t.G t.PP.L (𝟙 S) (𝟙 _) t.PP.isLB t.PP.isLB (SiegLower.isGrpPullback_id _)
        (SiegLower.lbIso_pull_id t.PP.isLB) g (FractionRing R) _).2 _ φK hPol
    have hPF' : PolFib t.G t.PP.L g (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) := h ▸ hPF
    have hm' : IsUnit (m : V) := by simpa using hm.map φ
    have hcv : ∀ r, φK (algebraMap R (FractionRing R) r) = algebraMap V (FractionRing V) (φ r) :=
      fun r => congrArg (· r) hc
    have hPrim : Prim (algebraMap V (FractionRing V)) (fun a => φK (algebraMap R (FractionRing R) (c a))) := by
      obtain ⟨a, u, hu⟩ := hunit
      refine ⟨fun b => ?_, a, ?_, ?_⟩
      · dsimp only; rw [hcv]; exact RingHom.isIntegralElem_map _
      · dsimp only; rw [← hu]; exact ((u.isUnit.map (algebraMap R (FractionRing R))).map φK).ne_zero
      · dsimp only
        rw [← hu, hcv, show (algebraMap V (FractionRing V) (φ ↑u))⁻¹ = ((algebraMap V (FractionRing V)).comp φ) ↑u⁻¹ from
          (map_units_inv ((algebraMap V (FractionRing V)).comp φ) u).symm, RingHom.comp_apply]
        exact RingHom.isIntegralElem_map _
    exact GlobalTheory.T.exists_nonzero_section_closed_fibre_of_primitive_theta E H S t g m N V hV (spMap φ ≫ χ) (h ▸ SecAt.pull t.G t.PP.L θ φK) pt₂ _ hodd h3 hm' hPF' hT₂ hPrim
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_section_of_extends_over_complete_dvrs S t.G t.PP.L t.PP.isLB t.semi R χ θ
    (fun V _ _ _ hV φ φK h hc => (key V hV φ φK h hc).imp fun _ h' => h'.1)
  refine ⟨σ, hσ, fun s => ?_⟩
  obtain ⟨p, hps⟩ : ∃ p : PrimeSpectrum R, (p : Sp R) = s := ⟨s, rfl⟩
  have hinjp : Function.Injective (algebraMap R (Localization.AtPrime p.asIdeal)) :=
    IsLocalization.injective _ p.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : CharZero (Localization.AtPrime p.asIdeal) := charZero_of_injective_algebraMap hinjp
  obtain ⟨V, _, _, _, φ₀, hV, hinj, hloc⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating (Localization.AtPrime p.asIdeal)
  obtain ⟨φ, hφdef⟩ : ∃ φ : R →+* V, φ = φ₀.comp (algebraMap R (Localization.AtPrime p.asIdeal)) := ⟨_, rfl⟩
  have hφ : Function.Injective φ := by
    rw [hφdef, RingHom.coe_comp]; exact hinj.comp hinjp
  obtain ⟨φK, hc⟩ := exists_fracMap φ hφ
  have h : spMap φK ≫ spMap (algebraMap R (FractionRing R)) ≫ χ =
      spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ := by
    rw [← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp, hc]
  obtain ⟨σV, hσV, z, hz₁, hz₂⟩ := key V hV φ φK h hc
  have hθ : SecAt.pull t.G t.PP.L σ (algebraMap R (FractionRing R)) = θ := secAt_ext t.G t.PP.L hσ
  have hFl : Flat t.G.hom := by haveI := t.semi.smooth; infer_instance
  have e₁ := pull_pull_cast t.G t.PP.L χ σ φ (algebraMap R (FractionRing R)) (algebraMap V (FractionRing V)) φK h hc
  rw [hθ] at e₁
  have heq : SecAt.pull t.G t.PP.L σ φ = σV :=
    secAt_eq_of_generic t.G t.PP.L _ _ _ (secAt_ext t.G t.PP.L (e₁.trans hσV.symm))
  subst heq
  refine ⟨((Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ χ) ⟶ Over.mk χ) ▷ t.G).left z, ?_,
    mem_nonzeroLocus_of_pullS t.G _ _ σ z hz₂⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, whiskerRight_fst, Over.comp_left, Scheme.Hom.comp_apply, hz₁]
  show (spMap φ) (IsLocalRing.closedPoint V) = s
  rw [← hps, hφdef]
  exact spMap_closedPoint p φ₀

end GlobalTheory.UMin.OmExt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_thetaMap_affineNormalBase_universalGenerator : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m n : ℕ) (o R : Type) [CommRing o] [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (β : o →+* R) (x : Sp R ⟶ S) (θ : SecAt G L x), Odd m → 3 ≤ m → IsUnit (m : R) → n + 1 = m ^ (4 * g) → PolFib G L g x → (∀ (K : Type) [Field K] (i : R →+* K), IsGenSec G L _ (SecAt.pull G L θ i)) → ∃ f : Sp R ⟶ PSpace o n, f ≫ PSpace.str o n = spMap β ∧ ThMap G L ρ m x f := by
  first | exact @GlobalTheory.UMin.MapAff.theta_map_aff | exact GlobalTheory.UMin.MapAff.theta_map_aff | (intros; apply GlobalTheory.UMin.MapAff.theta_map_aff <;> assumption)
end
