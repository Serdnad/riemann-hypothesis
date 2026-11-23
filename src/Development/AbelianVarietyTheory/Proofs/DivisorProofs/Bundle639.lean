module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle589
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle331
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle590
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle329
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle630
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle617
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle593
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle594
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle003
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatLocA
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003

@[expose] public section

section

open NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.partialZeta_values_at_neg_int_unique : ∀ {E : Type} [Field E] [NumberField E] {k : ℕ}, 2 ≤ k → ∀ {z z' : ClassGroup (GlobalTheory.CMVal.OF E) → ℚ}, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZetaVals k z → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZetaVals k z' → z = z' := by
  first | exact @GlobalTheory.ZetaValUnique.classZetaVals_unique | exact GlobalTheory.ZetaValUnique.classZetaVals_unique | (intros; apply GlobalTheory.ZetaValUnique.classZetaVals_unique <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.exists_tensorInduction_virtualCharacter_prime : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ χ ∈ Virt ℂ ℂ G, ∃ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), (∀ g, X (inl g) = ∏ t : Γ, χ (φ t g)) ∧ ∀ δ, X (inl δ * inr s) = χ (nrmG φ s (Nat.card Γ) δ) := by
  first | (exact @GlobalTheory.Shin.tensorInd_virt_prime) | (exact GlobalTheory.Shin.tensorInd_virt_prime) | (intros; apply GlobalTheory.Shin.tensorInd_virt_prime <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.ExpP

theorem main : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), HasQ N (wp N x) (cP N x) := by
  intro N _ x τ
  by_cases hx : x = 0
  · subst hx
    have h0 : wp N 0 τ = 0 := by
      simp [wp, tors, PeriodPair.weierstrassP_zero]
    simp only [cP, h0, if_true]
    simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  · have hB := GlobalTheory.T.weierstrass_division_value_q_expansion N x hx τ
    have hG := GlobalTheory.T.weierstrass_constant_q_expansion N τ
    have hd := hB.sub hG
    have hw : wp N x τ = wB N x τ - gN τ := by simp [wB]
    have hf : (fun n : ℕ => cP N x n * Complex.exp (2 * Real.pi * Complex.I * n * τ / N)) =
        fun n : ℕ => cB N x n * Complex.exp (2 * Real.pi * Complex.I * n * τ / N) -
          cG N n * Complex.exp (2 * Real.pi * Complex.I * n * τ / N) := by
      funext n
      simp [cP, hx, sub_mul]
    rw [hw, hf]
    exact hd

end GlobalTheory.WpFam.ExpP
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem psiG_gal (F : Type) [Field F] [Finite F] (t : F ≃+* F) (S : F[X] → ℂ) :
    ∀ (n : ℕ) (x : GL (Fin n) F),
      psiG S n (gal (t : F →+* F) n x) = psiG (fun P => S (P.map (t : F →+* F))) n x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x
    rw [GlobalTheory.T.primitiveFunctionCharpolyGL_harishChandra_recursion F S n (gal (t : F →+* F) n x), GlobalTheory.T.primitiveFunctionCharpolyGL_harishChandra_recursion F _ n x]
    congr 1
    · simp only [chG, gal]
      congr 1
      rw [← Matrix.charpoly_map]
      rfl
    · refine Finset.sum_congr rfl fun a ha => ?_
      rw [GlobalTheory.T.harishChandraInductionGL_fieldAutomorphism F t a (n - a) n]
      have ha' : a < n := Finset.mem_range.1 ha
      congr 1
      funext y
      exact ih a ha' y

theorem cusp_gal : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (t : F ≃+* F) (j : ℕ),
    (∀ x, t x = x ^ (ringChar F ^ j)) → ∀ (m k : ℕ) (x : GL (Fin m) F),
    cusp θ m k (gal (t : F →+* F) m x) = cusp θ m (k * ringChar F ^ j) x := by
  intro F _ _ θ t j ht m k x
  simp only [cusp]
  rw [psiG_gal F t]
  congr 2
  funext P
  exact GlobalTheory.T.rootSum_map_frobenius_pow_eq_rootSum_mul F θ (t : F →+* F) j (fun y => ht y) k P

end GlobalTheory.Shin
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory


set_option backward.isDefEq.respectTransparency false in
theorem finite_etale_family {A : CommRingCat.{0}} (P : ∀ B : CommRingCat.{0}, (A ⟶ B) → Prop)
    (h : ∀ p : Spec A, ∃ (B : CommRingCat.{0}) (g : A ⟶ B) (v : Spec B), g.hom.Etale ∧ Spec.map g v = p ∧ P B g) :
    ∃ (ι : Type) (_ : Finite ι) (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i),
      (∀ i, (g i).hom.Etale) ∧ (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, P (B i) (g i) := by
  choose B g v he hv hP using h
  have ho : ∀ p, IsOpen (Set.range (Spec.map (g p))) := fun p => by
    have : Etale (Spec.map (g p)) := (HasRingHomProperty.Spec_iff (P := @Etale)).2 (he p)
    exact (Spec.map (g p)).isOpenMap.isOpen_range
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun p => Set.range (Spec.map (g p))) ho
    (fun p _ => Set.mem_iUnion.2 ⟨p, v p, hv p⟩)
  refine ⟨s, inferInstance, fun i => B i, fun i => g i, fun i => he i, fun p => ?_, fun i => hP i⟩
  obtain ⟨i, hi, w, hw⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ p))
  exact ⟨⟨i, hi⟩, w, hw⟩


set_option backward.isDefEq.respectTransparency false in
noncomputable def ofRingsUnit (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) :
    M ⟶ onRings (ofRings R M) where
  app A := M.map (Scheme.ΓSpecIso A).inv ≫ (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).app (op (Spec A))
  naturality A B f := by
    have h := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality (Spec.map f).op
    rw [← Category.assoc, ← M.map_comp, Scheme.ΓSpecIso_inv_naturality, M.map_comp, Category.assoc, Category.assoc]
    congr 1


set_option backward.isDefEq.respectTransparency false in
theorem etale_affine_ring {A : CommRingCat.{0}} {V : Scheme.{0}} [IsAffine V] (j : V ⟶ Spec A) [Etale j] (v : V) :
    ∃ (B : CommRingCat.{0}) (g : A ⟶ B) (k : Spec B ⟶ V) (w : Spec B), g.hom.Etale ∧ Spec.map g = k ≫ j ∧ k w = v := by
  refine ⟨Γ(V, ⊤), Spec.preimage (V.isoSpec.inv ≫ j), V.isoSpec.inv, V.isoSpec.hom v, ?_, Spec.map_preimage _, ?_⟩
  · refine (HasRingHomProperty.Spec_iff (P := @Etale)).1 ?_
    rw [Spec.map_preimage]
    infer_instance
  · rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem ofRings_finitary : ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)), PreservesFilteredColimitsOfSize.{0, 0} M → Finitary (ofRings R M) := by
  intro R _ M hM
  refine GlobalTheory.T.finitary_of_locally_bijective_from_filtered_functor R M (ofRings R M) (ofRingsUnit R M) hM (fun A x => ?_) (fun A m hm => ?_)
  · obtain ⟨ι, hι, B, g, he, hc, hP⟩ := finite_etale_family (A := A)
      (fun B g => ∃ m : M.obj B, ((ofRingsUnit R M).app B).hom m = ((onRings (ofRings R M)).map g).hom x) (fun p => by
        obtain ⟨V, j, v, m, hV, hj, hv, hm⟩ := (ofRings_loc R M (Spec A)).1 x p
        obtain ⟨B, g, k, w, hg, hk, hw⟩ := etale_affine_ring j v
        refine ⟨B, g, w, hg, by rw [hk, Scheme.Hom.comp_apply, hw, hv],
          (M.map (k.appTop ≫ (Scheme.ΓSpecIso B).hom)).hom m, ?_⟩
        have h1 : (M.map (Scheme.ΓSpecIso B).inv).hom ((M.map (k.appTop ≫ (Scheme.ΓSpecIso B).hom)).hom m) =
            (M.map k.appTop).hom m := by
          rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← M.map_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
        change ofRings.sec M (Spec B) ((M.map (Scheme.ΓSpecIso B).inv).hom _) = Sec.res (F := ofRings R M) (Spec.map g) x
        rw [h1, ← (ofRings_loc R M V).2.2 _ k m, hm, hk]
        simp [Sec.res])
    choose m hm using hP
    exact ⟨ι, hι, B, g, m, he, hc, hm⟩
  · refine finite_etale_family (A := A) (fun B g => (M.map g).hom m = 0) (fun p => ?_)
    obtain ⟨V, j, v, hV, hj, hv, h0⟩ := (ofRings_loc R M (Spec A)).2.1 ((M.map (Scheme.ΓSpecIso A).inv).hom m) hm p
    obtain ⟨B, g, k, w, hg, hk, hw⟩ := etale_affine_ring j v
    refine ⟨B, g, w, hg, by rw [hk, Scheme.Hom.comp_apply, hw, hv], ?_⟩
    have h1 : g = (Scheme.ΓSpecIso A).inv ≫ j.appTop ≫ k.appTop ≫ (Scheme.ΓSpecIso B).hom := by
      rw [← Category.assoc j.appTop, ← Scheme.Hom.comp_appTop, ← hk, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    rw [h1, M.map_comp, M.map_comp, ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply, h0, map_zero]

end GlobalTheory
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem etale_leviNonneg : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ φ : Y → ℝ, (∀ x ∈ U, ∃ i, x ∈ (A.chart i).source ∧ ContDiffAt ℝ ∞ (φ ∘ (A.chart i).symm) (A.chart i x) ∧ ∀ ξ : Fin n → ℂ, 0 ≤ A.leviAt i φ x ξ) → LeviNonneg n (fun y : U => z y) (fun y : U => φ y) := by
  intro n Y _ _ _ _ _ ι La _ A U z hE φ hφ
  unfold LeviNonneg
  intro x ξ
  have hloc := GlobalTheory.T.etale_isLocalHomeomorph' n Y ι La A U z hE
  obtain ⟨e, he, hx⟩ := exists_chart n (fun y : U => z y) hloc x
  obtain ⟨i, hxi, hsm, hpos⟩ := hφ x.1 x.2
  have hzx : z x = e x := he hx
  have hv : e x ∈ e.target := e.map_source hx
  have hsx : e.symm (e x) = x := e.left_inv hx
  obtain ⟨hG, hev, -⟩ := GlobalTheory.T.contDiffAt_chart_inverse_of_etale n Y ι La A U z hE e he (e x) hv i (by rw [hsx]; exact hxi)
  rw [levi_eq_leviV n _ e he _ x hx ξ]
  show 0 ≤ (leviV n (fun y => ((φ (e.symm y : Y) : ℝ) : ℂ)) (z x) ξ).re
  rw [hzx]

  have heq : (fun y => ((φ (e.symm y : Y) : ℝ) : ℂ)) =ᶠ[𝓝 (e x)]
      (fun w => ((φ ((A.chart i).symm w) : ℝ) : ℂ)) ∘ (fun v' => A.chart i (e.symm v' : Y)) := by
    filter_upwards [hev] with v' hv'
    simp only [Function.comp_apply, (A.chart i).left_inv hv']
  have hcongr : leviV n (fun y => ((φ (e.symm y : Y) : ℝ) : ℂ)) (e x) ξ =
      leviV n ((fun w => ((φ ((A.chart i).symm w) : ℝ) : ℂ)) ∘
        (fun v' => A.chart i (e.symm v' : Y))) (e x) ξ := by
    unfold leviV
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    congr 2
    apply wd_congr
    filter_upwards [heq.eventuallyEq_nhds] with y hy
    exact ReciprocityTheory.L2DbarEstimates.wdb_congr n k _ _ y hy
  have hU : ContDiffAt ℝ 2 (fun w => ((φ ((A.chart i).symm w) : ℝ) : ℂ))
      ((fun v' => A.chart i (e.symm v' : Y)) (e x)) := by
    simp only [hsx]
    exact ((Complex.ofRealCLM.contDiff.contDiffAt).comp _ hsm).of_le (WithTop.coe_le_coe.mpr le_top)
  rw [hcongr, flA_leviV_comp hU (hG.of_le (WithTop.coe_le_coe.mpr le_top)) ξ]
  simp only [hsx]
  exact hpos _

end GlobalTheory.OTY
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.nonempty_atlasBallPartitionCover : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), Nonempty (Cover A) := by
  first | exact @GlobalTheory.OTY.nonempty_cover | exact GlobalTheory.OTY.nonempty_cover | (intros; apply GlobalTheory.OTY.nonempty_cover <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem eqv_basic : ∀ (R : Type) [CommRing R] (F : Shv R), (∀ (E E' : Spc) (f : E ⟶ E'), IsIso f → Eqv R f F) ∧ (∀ (E E' E'' : Spc) (f : E ⟶ E') (g : E' ⟶ E''), (Eqv R f F → Eqv R g F → Eqv R (f ≫ g) F) ∧ (Eqv R f F → Eqv R (f ≫ g) F → Eqv R g F) ∧ (Eqv R g F → Eqv R (f ≫ g) F → Eqv R f F)) ∧ (∀ (E E' : Spc) (f : E ⟶ E'), QuasiIso ((chains R).map f) → Eqv R f F) ∧ ∀ (E E' : Spc) (f : E ⟶ E'), Eqv R f F → (AcycF R E F ↔ AcycF R E' F) := by
  intro R _ F
  have hc : ∀ {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (n : ℤ),
      ⇑(pull R (f ≫ g) F n) = ⇑(pull R f F n) ∘ ⇑(pull R g F n) := by
    intro E E' E'' f g n
    funext x
    exact pull_comp R f g F n x
  have hid : ∀ (E : Spc) (n : ℤ), ⇑(pull R (𝟙 E) F n) = id := by
    intro E n
    funext x
    exact pull_id R E F n x
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro E E' f hf n
    haveI := hf
    have h1 : Function.LeftInverse (pull R (inv f) F n) (pull R f F n) := by
      intro x
      have := congrFun (hc (inv f) f n) x
      rw [IsIso.inv_hom_id, hid] at this
      exact this.symm
    have h2 : Function.RightInverse (pull R (inv f) F n) (pull R f F n) := by
      intro x
      have := congrFun (hc f (inv f) n) x
      rw [IsIso.hom_inv_id, hid] at this
      exact this.symm
    exact ⟨h1.injective, h2.surjective⟩
  · intro E E' E'' f g
    refine ⟨?_, ?_, ?_⟩
    · intro hf hg n
      rw [hc]
      exact (hf n).comp (hg n)
    · intro hf hfg n
      have := hfg n
      rw [hc] at this
      exact (Function.Bijective.of_comp_iff' (hf n) _).mp this
    · intro hg hfg n
      have := hfg n
      rw [hc] at this
      exact (Function.Bijective.of_comp_iff _ (hg n)).mp this
  · intro E E' f hq n
    exact GlobalTheory.T.quasiIso_hypercohomology_bijective R ((chains R).map f) F n
  · intro E E' f hf
    constructor
    · intro h n hn
      haveI := h n hn
      exact (hf n).1.subsingleton
    · intro h n hn
      haveI := h n hn
      exact (Equiv.ofBijective _ (hf n)).symm.subsingleton

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.HensMax

open IsLocalRing

theorem comap_maximalIdeal_of_localHom {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] : (maximalIdeal S).comap f = maximalIdeal R := by
  ext x
  simp only [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  exact ⟨fun h hx => h (hx.map f), fun h hx => h (isUnit_of_map_unit f x hx)⟩

theorem isSepClosed_of_ringEquiv {K L : Type} [Field K] [Field L] [IsSepClosed K] (e : K ≃+* L) : IsSepClosed L := by
  refine IsSepClosed.of_exists_root L fun p hm hirr hsep => ?_
  have hq : (p.map e.symm.toRingHom).Separable := hsep.map
  have hdeg : (p.map e.symm.toRingHom).degree ≠ 0 := by
    rw [Polynomial.degree_map]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root _ hdeg hq
  refine ⟨e x, ?_⟩
  have := congrArg (e : K →+* L) hx
  rw [Polynomial.eval_map, map_zero, Polynomial.hom_eval₂] at this
  have h2 : (e : K →+* L).comp e.symm.toRingHom = RingHom.id L := by ext; simp
  rw [h2, Polynomial.eval₂_id] at this
  exact this

end GlobalTheory.HensMax


open IsLocalRing in
theorem GlobalTheory.HensMax.exists_strictHens_of_maximal : ∀ (B : Type) [CommRing B] (P : Ideal B) [P.IsMaximal],
    IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) → ∃ (O : Type) (_ : CommRing O) (_ : Algebra B O),
    SH O ∧ IndEt B O ∧ ∀ Q : Ideal O, Q.IsMaximal → Q.comap (algebraMap B O) = P ∧ ∀ o : O, ∃ b : B, o - algebraMap B O b ∈ Q := by
  intro B _ P _ hsep
  obtain ⟨S, _, _, hH, hloc, -, -, hbij, ι, _, _, _, Si, hmono, hcov, hSi⟩ :=
    GlobalTheory.Henselisation.exists_henselisation (Localization.AtPrime P)
  letI : Algebra B S := ((algebraMap (Localization.AtPrime P) S).comp (algebraMap B (Localization.AtPrime P))).toAlgebra
  haveI : IsScalarTower B (Localization.AtPrime P) S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine ⟨S, inferInstance, inferInstance, ⟨hH, ?_⟩, ?_, ?_⟩
  · exact GlobalTheory.HensMax.isSepClosed_of_ringEquiv (RingEquiv.ofBijective _ hbij)
  · have hRS : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap (Localization.AtPrime P) S) := by
      refine GlobalTheory.StrictHensUnion.indEtale_of_directed_union _ S ι Si hmono hcov fun i => ?_
      obtain ⟨A, _, _, _, q, _, ⟨e⟩⟩ := hSi i
      exact GlobalTheory.StrictHensUnion.indEtale_of_algEquiv e
        (GlobalTheory.StrictHensUnion.indEtale_localization_of_etale _ A q.primeCompl)
    have hBR : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap B (Localization.AtPrime P)) :=
      GlobalTheory.StrictHensUnion.indEtale_localization_of_etale B B P.primeCompl
    show GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap B S)
    rw [IsScalarTower.algebraMap_eq B (Localization.AtPrime P) S]
    exact GlobalTheory.T.ind_etale_comp _ _ _ _ _ hBR hRS
  · intro Q hQ
    obtain rfl : Q = maximalIdeal S := IsLocalRing.eq_maximalIdeal hQ
    refine ⟨?_, fun o => ?_⟩
    · rw [IsScalarTower.algebraMap_eq B (Localization.AtPrime P) S, ← Ideal.comap_comap,
        GlobalTheory.HensMax.comap_maximalIdeal_of_localHom]
      exact Localization.AtPrime.under_maximalIdeal (I := P)
    · obtain ⟨y, hy⟩ := hbij.2 (residue S o)
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨b, hb⟩ := (IsLocalization.AtPrime.equivQuotMaximalIdeal P (Localization.AtPrime P)).surjective
        (Ideal.Quotient.mk _ r)
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk, Ideal.Quotient.eq] at hb
      refine ⟨b, ?_⟩
      have h1 : residue _ (algebraMap B (Localization.AtPrime P) b) = residue _ r := by
        rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
        exact hb
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hy, IsScalarTower.algebraMap_apply B (Localization.AtPrime P) S,
        ← ResidueField.map_residue, h1, sub_self]
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

theorem _root_.GlobalTheory.T.quaternion_norm_one_trace_open_adeles : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ g : DA F a b, nrm g = 1 → ∀ W : Set (DA F a b), W ∈ 𝓝 g → ∃ O : Set (AF F), IsOpen O ∧ O.Nonempty ∧ ∀ t ∈ O, ∃ u ∈ W, nrm u = 1 ∧ u.re = t := by
  first | exact @GlobalTheory.QSA.traceOpen_adele | exact GlobalTheory.QSA.traceOpen_adele | (intros; apply GlobalTheory.QSA.traceOpen_adele <;> assumption)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.kahlerFormsOverSubalgebra_standardOpen_iff_pow_smul : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I → ∀ (q : ℕ) (y : DR k K), y ∈ omB k K (rB k K x I) q ↔ ∃ N : ℕ, (algebraMap F K (∏ j ∈ I, x j / x i) ^ N) • y ∈ omB k K (rB k K x {i}) q := by
  first | (exact @GlobalTheory.omB_iff_pow_smul) | (exact GlobalTheory.omB_iff_pow_smul) | (intros; apply GlobalTheory.omB_iff_pow_smul <;> assumption)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.finite_cover_chart_smooth_normal : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ I : Finset (Fin (d + 1)), I.Nonempty → Module.Finite (rA k x I) (integralClosure (rA k x I) K) ∧ IsFractionRing (rB k K x I) K ∧ Algebra.Smooth k (rB k K x I) := by
  first | (exact @GlobalTheory.PD.rB_finite_frac_smooth) | (exact GlobalTheory.PD.rB_finite_frac_smooth) | (intros; apply GlobalTheory.PD.rB_finite_frac_smooth  <;> assumption)
end
