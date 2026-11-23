module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle017
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.DoubleCoset
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
public import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1172
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle987
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1136
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilAdjoint

theorem map_unitOn {A B : Type} [CommRing A] [CommRing B] (β : A →+* B) (c : Aˣ) :
    Units.map (spMap β).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map β.toMonoidHom c) :=
  Units.ext (congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm

theorem weilIs_algHom {K : Type} [CommRing K] {B : Over (Sp K)} [GrpObj B] (hB : IsAbelianScheme B) {P : LB B.left}
    (hP : P.IsLB) {k : ℤ} {D E : Type} [CommRing D] [Algebra K D] [CommRing E] [Algebra K E] (α : D →ₐ[K] E)
    {x y : SpAlg K D ⟶ B} {x' y' : SpAlg K E ⟶ B} (hx : spOver α ≫ x = x') (hy : spOver α ≫ y = y') {U : Dˣ}
    (hU : Out.WeilIs B P k (T := SpAlg K D) x y (unitOn U)) :
    Out.WeilIs B P k (T := SpAlg K E) x' y' (unitOn (Units.map (α : D →+* E).toMonoidHom U)) := by
  rw [← map_unitOn, ← hx, ← hy]
  exact CommPairing.weilIs_pull GlobalTheory.globalFns_holds hB hP (T := SpAlg K D) (T' := SpAlg K E) (spOver α) hU

end GlobalTheory.WeilAdjoint
end
end

section

open MeasureTheory

noncomputable section

namespace GlobalTheory.Cusp.Shear

theorem isHaarMeasure_map_prodHomeo : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (Γ N N' : Subgroup G) [DiscreteTopology Γ] [LocallyCompactSpace N]
    [LocallyCompactSpace N'] (hle : N' ≤ N), (∀ p ∈ N, ∀ m ∈ N', p * m * p⁻¹ ∈ N') →
    GlobalTheory.Cusp.Cocompact Γ N → GlobalTheory.Cusp.Cocompact Γ N' →
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
      [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (s : V → G) (π : N → V)
      (hs : ∀ v, s v ∈ N) (hsc : Continuous s) (hπc : Continuous π) (hπmul : ∀ a b : N, π (a * b) = π a + π b)
      (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v) (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N'),
      (∀ v w, s (v + w) = s v * s w) → ∀ (μ : MeasureTheory.Measure V), μ.IsAddHaarMeasure →
      (((MeasureTheory.Measure.haar : MeasureTheory.Measure N').prod μ).map
        (GlobalTheory.Cusp.Shear.prodHomeo hle hs hsc hπc hπmul hπs hker)).IsHaarMeasure := by
  intro G _ _ _ _ _ _ _ Γ N N' _ _ _ hle hn hc hc' V _ _ _ _ _ _ _ _ s π hs hsc hπc hπmul hπs hker hsmul μ hμ
  set e := prodHomeo hle hs hsc hπc hπmul hπs hker with he_def
  set P : Measure (N' × V) := (Measure.haar : Measure N').prod μ with hP
  set ν : Measure N := P.map e with hν
  haveI := hc'.isMulRightInvariant (Measure.haar : Measure N')
  have hem : Measurable e := e.continuous.measurable
  haveI : IsFiniteMeasureOnCompacts ν := Measure.IsFiniteMeasureOnCompacts.map P e
  haveI : ν.IsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective

  haveI hR : ν.IsMulRightInvariant := ⟨fun n₀ => by
    set z₀ := e.symm n₀
    have hz₀ : ((n₀ : N) : G) = (z₀.1 : G) * s z₀.2 := by
      rw [← prodHomeo_apply hle hs hsc hπc hπmul hπs hker z₀]; simp [z₀, e]
    let c : V → N' := fun v => ⟨s v * z₀.1 * (s v)⁻¹, hn _ (hs v) _ z₀.1.2⟩
    have hcc : Continuous c := by fun_prop
    let T' : V × N' → V × N' := fun p => (p.1 + z₀.2, p.2 * c p.1)
    have hT' : MeasurePreserving T' (μ.prod (Measure.haar : Measure N')) (μ.prod (Measure.haar : Measure N')) :=
      (measurePreserving_add_right μ z₀.2).skew_product (g := fun v m => m * c v)
        (by apply Continuous.measurable; fun_prop)
        (.of_forall fun v => map_mul_right_eq_self _ _)
    have hT : MeasurePreserving (Prod.swap ∘ T' ∘ Prod.swap) P P :=
      Measure.measurePreserving_swap.comp (hT'.comp Measure.measurePreserving_swap)
    have hcomm : (fun n => n * n₀) ∘ e = e ∘ (Prod.swap ∘ T' ∘ Prod.swap) := by
      funext ⟨m, v⟩
      apply Subtype.ext
      change ((m : G) * s v) * (n₀ : G) = ((m * c v : N') : G) * s (v + z₀.2)
      rw [hz₀, hsmul, Subgroup.coe_mul]
      change _ = (m : G) * (s v * (z₀.1 : G) * (s v)⁻¹) * (s v * s z₀.2)
      group
    rw [hν, Measure.map_map (measurable_mul_const n₀) hem, hcomm, ← Measure.map_map hem hT.measurable, hT.map_eq]⟩
  haveI : IsFiniteMeasureOnCompacts ν.inv := Measure.IsFiniteMeasureOnCompacts.map ν (Homeomorph.inv N)
  haveI : ν.inv.IsOpenPosMeasure := (Homeomorph.inv N).continuous.isOpenPosMeasure_map (Homeomorph.inv N).surjective
  haveI : ν.inv.IsHaarMeasure := {}
  haveI := hc.isMulRightInvariant ν.inv
  have hL : ν.IsMulLeftInvariant := by rw [← Measure.inv_inv ν]; infer_instance
  exact {}

end GlobalTheory.Cusp.Shear

end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RelIdxRestr

theorem index_pi_univ {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

theorem relIndex_iInf_comap {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)]
    [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v))
    (hX : GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K) (C H : ∀ v, Subgroup (Y v))
    (_hfin : ∀ v, (H v).relIndex (C v) ≠ 0) (hev : ∀ᶠ v in cofinite, C v ≤ H v) :
    (⨅ v, (H v).comap (pf v)).relIndex (⨅ v, (C v).comap (pf v)) = ∏ᶠ v, (H v).relIndex (C v) := by
  classical
  set S : Finset V := (Filter.eventually_cofinite.1 hev).toFinset with hS
  have hSm : ∀ v, v ∉ S → C v ≤ H v := fun v hv => by
    by_contra h; exact hv (by simpa [hS] using h)
  set Cg := ⨅ v, (C v).comap (pf v)
  set Hg := ⨅ v, (H v).comap (pf v)
  have hmemC : ∀ x : X, x ∈ Cg ↔ ∀ v, pf v x ∈ C v := fun x => by simp [Cg, Subgroup.mem_iInf]
  have hmemH : ∀ x : X, x ∈ Hg ↔ ∀ v, pf v x ∈ H v := fun x => by simp [Hg, Subgroup.mem_iInf]
  let φ : Cg →* ∀ v : S, C v := MonoidHom.pi fun v =>
    ((pf v).comp Cg.subtype).codRestrict (C v) fun x => (hmemC x).1 x.2 v
  have hφ : ∀ x (v : S), ((φ x v : C v) : Y v) = pf v x := fun _ _ => rfl
  have hsurj : Function.Surjective φ := by
    intro y
    let z : ∀ v, Y v := fun v => if h : v ∈ S then (y ⟨v, h⟩ : Y v) else 1
    obtain ⟨x, -, hx⟩ := hX.exists_eq (fun w => w.elim) z
      (GlobalTheory.RestrMeas.eventually_of_finset S fun v hv => by simp [z, hv, one_mem])
    have hxC : x ∈ Cg := (hmemC x).2 fun v => by
      rw [hx v]
      by_cases h : v ∈ S
      · simp only [z, dif_pos h]; exact (y ⟨v, h⟩).2
      · simp only [z, dif_neg h]; exact one_mem _
    refine ⟨⟨x, hxC⟩, funext fun v => Subtype.ext ?_⟩
    rw [hφ]
    show pf v x = _
    rw [hx v]
    simp [z, v.2]
  have hcomap : Hg.subgroupOf Cg = (Subgroup.pi Set.univ fun v : S => (H v).subgroupOf (C v)).comap φ := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, Set.mem_univ, true_implies, hmemH]
    constructor
    · intro h v; exact h v
    · intro h v
      by_cases hv : v ∈ S
      · exact h ⟨v, hv⟩
      · exact hSm v hv ((hmemC x).1 x.2 v)
  rw [Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ hsurj, index_pi_univ,
    finprod_eq_prod_of_mulSupport_subset (s := S)]
  · exact (Finset.prod_coe_sort S fun v => (H v).relIndex (C v))
  · intro v hv
    by_contra h
    exact hv (Subgroup.relIndex_eq_one.2 (hSm v h))

end GlobalTheory.RelIdxRestr

end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerAbs

open GlobalTheory.RestrMeas

theorem finsum_doubleCoset_restr {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X]
    [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v))
    (hX : GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K) (T : Subgroup X)
    (Tv : ∀ v, Subgroup (Y v)) (hT : ∀ x, x ∈ T ↔ ∀ v, pf v x ∈ Tv v) (F : X → ℂ) (Fv : ∀ v, Y v → ℂ)
    (hF : ∀ x, F x = ∏ᶠ v, Fv v (pf v x))
    (hinv : ∀ v, ∀ t ∈ Tv v, ∀ y, ∀ k ∈ K v, Fv v (t * y * k) = Fv v y)
    (hfin : ∀ v, {q : DoubleCoset.Quotient (Tv v : Set (Y v)) (K v : Set (Y v)) | Fv v (Quotient.out q) ≠ 0}.Finite)
    (hev : ∀ᶠ v in cofinite, Fv v 1 = 1 ∧ ∀ y, Fv v y ≠ 0 → ∃ t ∈ Tv v, ∃ k ∈ K v, y = t * k) :
    ∑ᶠ q : DoubleCoset.Quotient (T : Set X) ((⨅ v, (K v).comap (pf v) : Subgroup X) : Set X), F (Quotient.out q) =
      ∏ᶠ v, ∑ᶠ q : DoubleCoset.Quotient (Tv v : Set (Y v)) (K v : Set (Y v)), Fv v (Quotient.out q) := by
  set Kg : Subgroup X := ⨅ v, (K v).comap (pf v) with hKg
  have memKg : ∀ x, x ∈ Kg ↔ ∀ v, pf v x ∈ K v := fun x => by simp [hKg, Subgroup.mem_iInf]
  obtain ⟨S0, hS0⟩ := exists_finset_of_eventually hev

  have L0 : ∀ v (z₁ z₂ : Y v), DoubleCoset.mk (Tv v) (K v) z₁ = DoubleCoset.mk (Tv v) (K v) z₂ →
      Fv v z₁ = Fv v z₂ := fun v z₁ z₂ h => by
    obtain ⟨t, ht, k, hk, e⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 h
    rw [e, hinv v t ht z₁ k hk]
  have L0' : ∀ v (z : Y v), Fv v (Quotient.out (DoubleCoset.mk (Tv v) (K v) z)) = Fv v z := fun v z =>
    L0 v _ _ (DoubleCoset.out_eq' _)

  have L1 : ∀ x y, DoubleCoset.mk T Kg x = DoubleCoset.mk T Kg y → ∀ v,
      DoubleCoset.mk (Tv v) (K v) (pf v x) = DoubleCoset.mk (Tv v) (K v) (pf v y) := fun x y h v => by
    obtain ⟨t, ht, k, hk, e⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 h
    exact (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨pf v t, (hT t).1 ht v, pf v k, (memKg k).1 hk v, by rw [e]; simp⟩

  have L1' : ∀ x y, (∀ v, DoubleCoset.mk (Tv v) (K v) (pf v x) = DoubleCoset.mk (Tv v) (K v) (pf v y)) →
      DoubleCoset.mk T Kg x = DoubleCoset.mk T Kg y := fun x y h => by
    have h' := fun v => (@DoubleCoset.eq _ _ _ _ _ _).1 (h v)
    choose t ht k hk e using h'
    let t' : ∀ v, Y v := fun v => if pf v x ∈ K v ∧ pf v y ∈ K v then 1 else t v
    have ht'T : ∀ v, t' v ∈ Tv v := fun v => by
      by_cases c : pf v x ∈ K v ∧ pf v y ∈ K v
      · simp only [t', if_pos c]; exact one_mem _
      · simp only [t', if_neg c]; exact ht v
    have ht'K : ∀ v, (pf v x)⁻¹ * (t' v)⁻¹ * pf v y ∈ K v := fun v => by
      by_cases c : pf v x ∈ K v ∧ pf v y ∈ K v
      · simp only [t', if_pos c, inv_one, mul_one]; exact mul_mem (inv_mem c.1) c.2
      · simp only [t', if_neg c]; rw [e v]; simpa [mul_assoc] using hk v
    have hev' : ∀ᶠ v in cofinite, t' v ∈ K v := ((hX.eventually_mem x).and (hX.eventually_mem y)).mono
      fun v c => by simp only [t', if_pos c]; exact one_mem _
    obtain ⟨g, -, hg⟩ := hX.exists_eq isEmptyElim t' hev'
    refine (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨g, (hT g).2 fun v => hg v ▸ ht'T v, x⁻¹ * g⁻¹ * y,
      (memKg _).2 fun v => by simpa [hg v] using ht'K v, by group⟩

  have ProjectionSandwichLength : ∀ x, (Function.mulSupport fun v => Fv v (pf v x)).Finite := fun x => by
    have hE : ∀ᶠ v in cofinite, pf v x ∈ K v ∧ v ∉ S0 :=
      (hX.eventually_mem x).and (eventually_of_finset S0 fun v hv => hv)
    refine (eventually_cofinite.1 hE).subset fun v hv c => hv ?_
    show Fv v (pf v x) = 1
    have := hinv v 1 (one_mem _) 1 (pf v x) c.1
    rw [one_mul, one_mul] at this
    rw [this, (hS0 v c.2).1]
  have L2 : ∀ x, F x ≠ 0 → ∀ v, Fv v (pf v x) ≠ 0 := fun x hx v h0 =>
    hx (by rw [hF]; exact finprod_eq_zero _ v h0 (ProjectionSandwichLength x))
  have KernelIndexFullLattice : ∀ v ∉ S0, ∀ y : Y v, Fv v y ≠ 0 → DoubleCoset.mk (Tv v) (K v) y = DoubleCoset.mk (Tv v) (K v) 1 ∧
      Fv v y = 1 := fun v hv y hy => by
    obtain ⟨t, ht, k, hk, e⟩ := (hS0 v hv).2 y hy
    refine ⟨((@DoubleCoset.eq _ _ _ _ _ _).2 ⟨t, ht, k, hk, by rw [e, mul_one]⟩).symm, ?_⟩
    rw [e, ← (hS0 v hv).1, ← hinv v t ht 1 k hk, mul_one]
  have DegreeKernelLowerBound : ∀ x, (∀ v ∉ S0, Fv v (pf v x) ≠ 0) → F x = ∏ v ∈ S0, Fv v (pf v x) := fun x h => by
    rw [hF]
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra hS
    exact hv (KernelIndexFullLattice v hS _ (h v hS)).2

  have L3 : ∀ v ∉ S0, ∑ᶠ q : DoubleCoset.Quotient (Tv v : Set (Y v)) (K v : Set (Y v)), Fv v (Quotient.out q) = 1 :=
    fun v hv => by
    rw [finsum_eq_single _ (DoubleCoset.mk (Tv v) (K v) 1), L0', (hS0 v hv).1]
    intro q hq
    by_contra h0
    apply hq
    rw [← DoubleCoset.out_eq' q]
    exact (KernelIndexFullLattice v hv _ h0).1
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S0) fun v hv => by_contra fun h => hv (L3 v h),
    ← Finset.prod_coe_sort S0]
  let Q := fun v : S0 => DoubleCoset.Quotient (Tv v.1 : Set (Y v.1)) (K v.1 : Set (Y v.1))
  let Φ : DoubleCoset.Quotient (T : Set X) (Kg : Set X) → ∀ v : S0, Q v :=
    fun q v => DoubleCoset.mk (Tv v.1) (K v.1) (pf v.1 (Quotient.out q))
  let H : (∀ v : S0, Q v) → ℂ := fun b => ∏ v : S0, Fv v.1 (Quotient.out (b v))
  have hH : ∀ b, H b ≠ 0 → ∀ v : S0, Fv v.1 (Quotient.out (b v)) ≠ 0 := fun b hb v =>
    Finset.prod_ne_zero_iff.1 hb v (Finset.mem_univ _)
  have hval : ∀ q, F (Quotient.out q) ≠ 0 → F (Quotient.out q) = H (Φ q) := fun q hq => by
    rw [DegreeKernelLowerBound _ fun v _ => L2 _ hq v, ← Finset.prod_coe_sort S0]
    exact Finset.prod_congr rfl fun v _ => (L0' v.1 _).symm
  have hbij : Set.BijOn Φ (Function.support fun q => F (Quotient.out q)) (Function.support H) := by
    refine ⟨fun q hq => ?_, fun q₁ h₁ q₂ h₂ e => ?_, fun b hb => ?_⟩
    · show H (Φ q) ≠ 0
      rw [← hval q hq]; exact hq
    · rw [← DoubleCoset.out_eq' q₁, ← DoubleCoset.out_eq' q₂]
      refine L1' _ _ fun v => ?_
      by_cases hv : v ∈ S0
      · exact congrFun e ⟨v, hv⟩
      · rw [(KernelIndexFullLattice v hv _ (L2 _ h₁ v)).1, (KernelIndexFullLattice v hv _ (L2 _ h₂ v)).1]
    · have hb' := hH b hb
      let y : ∀ v, Y v := fun v => if h : v ∈ S0 then Quotient.out (b ⟨v, h⟩) else 1
      obtain ⟨x, -, hx⟩ := hX.exists_eq isEmptyElim y
        (eventually_of_finset S0 fun v hv => by simp only [y, dif_neg hv]; exact one_mem _)
      have hq := L1 _ _ (DoubleCoset.out_eq' (DoubleCoset.mk T Kg x))
      have hxS : ∀ v : S0, DoubleCoset.mk (Tv v.1) (K v.1) (pf v.1 x) = b v := fun v => by
        rw [hx, show y v.1 = Quotient.out (b v) by simp [y, v.2]]
        exact DoubleCoset.out_eq' _
      have hΦ : Φ (DoubleCoset.mk T Kg x) = b := funext fun v => (hq v.1).trans (hxS v)
      refine ⟨DoubleCoset.mk T Kg x, ?_, hΦ⟩
      show F _ ≠ 0
      have hne : ∀ v ∉ S0, Fv v (pf v (Quotient.out (DoubleCoset.mk T Kg x))) ≠ 0 := fun v hv => by
        rw [L0 v _ _ (hq v), hx]; simp only [y, dif_neg hv, (hS0 v hv).1]; exact one_ne_zero
      rw [DegreeKernelLowerBound _ hne, Finset.prod_ne_zero_iff]
      intro v hv
      rw [L0 v _ _ (hq v), hx]
      simp only [y, dif_pos hv]
      exact hb' ⟨v, hv⟩
  refine ((finsum_mem_support _).symm.trans ((finsum_mem_eq_of_bijOn Φ hbij fun q hq => hval q hq).trans
    (finsum_mem_support H))).trans ?_
  have hsum : ∀ v : S0, ∑ᶠ q : Q v, Fv v.1 (Quotient.out q) =
      ∑ q ∈ (hfin v.1).toFinset, Fv v.1 (Quotient.out q) := fun v =>
    finsum_eq_sum_of_support_subset _ fun q hq => (hfin v.1).mem_toFinset.2 hq
  rw [Finset.prod_congr rfl fun v _ => hsum v, Finset.prod_univ_sum]
  refine finsum_eq_sum_of_support_subset H fun b hb => ?_
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  exact fun v => by simpa using hH b hb v

end GlobalTheory.EulerAbs
end
end

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

theorem _root_.GlobalTheory.T.dualWeyl_orthonormal_basis_values_at_unitary_sum_sq_le_one : ∀ (n : ℕ) (la : Fin n → ℕ), Antitone la → ∀ u : UN n, ∑ i, ‖evalAt u.1 (((toSpace la).symm (onBasis la i) : nabla la ℂ) : Pol n ℂ)‖ ^ 2 ≤ 1 := by
  first | exact @GlobalTheory.DualWeyl.EvBound.sum_sq_norm_evalAt_onBasis_le_one | exact GlobalTheory.DualWeyl.EvBound.sum_sq_norm_evalAt_onBasis_le_one | (intros; apply GlobalTheory.DualWeyl.EvBound.sum_sq_norm_evalAt_onBasis_le_one <;> assumption)
end

section

open MeasureTheory Matrix GlobalTheory.Orb
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
open scoped ContDiff

namespace GlobalTheory

theorem hasOrbInt_of_isCompact_cent_conj : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] (μ : Measure H) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (s : H), IsCompact (cent s : Set H) → ∀ (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant], IsProperOrbit (cent s) s → ∀ (y : H) (f : H → ℂ), Continuous f → HasCompactSupport f → HasOrbInt μ s dt f ((∫ x, f (x⁻¹ * (y⁻¹ * s * y) * x) ∂μ) / dt.real Set.univ) := by
  intro H _ _ _ _ _ _ _ _ μ _ _ s hT dt _ _ hP y f hf hc
  haveI : CompactSpace (cent s) := isCompact_iff_compactSpace.1 hT
  obtain ⟨C, hC, h0⟩ := hP _ hc
  have hcont : Continuous (conjFn s f) := hf.comp (by fun_prop)
  have hsupp : HasCompactSupport (conjFn s f) := by
    refine HasCompactSupport.intro' (hT.mul hC) (hT.mul hC).isClosed fun x hx => ?_
    by_contra hne
    obtain ⟨t, ht, htx⟩ := h0 x (subset_tsupport f hne)
    exact hx ⟨t⁻¹, (cent s).inv_mem ht, t * x, htx, by group⟩
  have hint : Integrable (conjFn s f) μ := hcont.integrable_of_hasCompactSupport hsupp
  have e : (∫ x, f (x⁻¹ * (y⁻¹ * s * y) * x) ∂μ) = ∫ x, f (x⁻¹ * s * x) ∂μ := by
    have := integral_mul_left_eq_self (μ := μ) (fun z => f (z⁻¹ * s * z)) y
    rw [← this]
    congr 1; ext x; congr 1; group
  rw [e]
  exact hasOrbInt_of_finite hint

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DiagThetaRule

open GlobalTheory.Doubling Formalism.IndefR.Datum

theorem JR_dblSp_gram {D : D7} (S : HSp D) :
    JR (F := D.host.F) (AF D.host.F) (dblSp S).gram =
      blkMat finSumFinEquiv (JR (F := D.host.F) (AF D.host.F) S.gram) (-(JR (F := D.host.F) (AF D.host.F) S.gram)) := by
  rw [show (dblSp S).gram = dblGram finSumFinEquiv S.gram from gram_hdbl S, dblGram, JR,
    blkMat_map _ _ (map_zero _)]
  simp [JR, Matrix.map_neg]

theorem neg_one_mem_UJ {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (J : Matrix n n A) : (-1 : GL n A) ∈ Formalism.UG.UJ σ J := by
  show Formalism.UG.cT σ (-1 : GL n A).val * J * (-1 : GL n A).val = J
  rw [Units.val_neg, Units.val_one, Formalism.UG.cT, Matrix.map_neg _ (map_neg σ), Matrix.map_one _ (map_zero σ) (map_one σ),
    Matrix.transpose_neg, Matrix.transpose_one, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg]

def epsPair {D : D7} (S : HSp D) : GL (Fin S.rank) (AE D) × GL (Fin S.rank) (AE D) := (1, -1)

theorem blkGL_epsPair_mem {D : D7} (S : HSp D) :
    blkGL finSumFinEquiv (epsPair S) ∈
      Formalism.UG.UJ (sigR (AF D.host.F) D.sp.cm.sig) (JR (F := D.host.F) (AF D.host.F) (dblSp S).gram) := by
  rw [JR_dblSp_gram, epsPair, blkGL_mem_UJ]
  exact ⟨one_mem _, neg_one_mem_UJ _ _⟩

def epsD {D : D7} (S : HSp D) : GA D (dblSp S) := ⟨blkGL finSumFinEquiv (epsPair S), blkGL_epsPair_mem S⟩

theorem mt_epsD {D : D7} (S : HSp D) :
    Formalism.L2.Theta.mt (dblSp S) (epsD S) =
      blkMat finSumFinEquiv (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) (-1) := rfl

end GlobalTheory.DiagThetaRule
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.CoreOfWeak

theorem core_of_weak : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → Core R.toRealDat F.lv2 ∧ IsSF R.toRealDat R.SF ∧ (∀ c, R.EEc c = EEc R.toRealDat R.SF c) ∧ ∀ i c, R.Wc' i c = Wcc R.toRealDat R.SF i c := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F h e
  have hc := Formalism.IndefR.Links.RealDat3.characterisation_of_weak h e
  refine ⟨⟨hc.lev, hc.grp, hc.fam, hc.models, hc.chain, hc.thP⟩, ?_, fun c => rfl, fun i c => rfl⟩
  intro v
  rw [h.inert.SF v, h.allPl]

end GlobalTheory.CoreOfWeak
end
