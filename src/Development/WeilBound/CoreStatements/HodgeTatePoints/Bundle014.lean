module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle003
public import Mathlib.RingTheory.Valuation.Integers
public import ReciprocityTheory.DualLattices.Bundle002
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle010
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RfHopf
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle004
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle018
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle023
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle030
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import ReciprocityTheory.DualLattices.Bundle007
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.HtPt.Rf

section
variable {R : Type} [CommRing R] {p : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  {N : Type} [AddCommGroup N] {pt : N → (sp (R₀ := R) R ⟶ G)}

theorem pt_zero (hpt : IsTorsPts G p pt) : pt 0 = 1 := by
  have h := hpt.add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem pt_nsmul (hpt : IsTorsPts G p pt) (n : ℕ) (x : N) : pt (n • x) = pt x ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero, pt_zero hpt]
  | succ n ih => rw [succ_nsmul, hpt.add, ih, pow_succ]

theorem exists_pts (T : TorsRep G p) (hpt : IsTorsPts G p pt) :
    ∃ φ : N → (T.A →ₐ[R] R), ∀ x, spMap (φ x) ≫ T.y = pt x := by
  choose φ hφ using fun x => (T.univ R (pt x) ((hpt.range _).2 ⟨x, rfl⟩)).exists
  exact ⟨φ, hφ⟩

omit [AddCommGroup N] in
theorem mem_torsFun {C : Type} [Field C] [Algebra R C] (T : TorsRep G p)
    {φ : N → (T.A →ₐ[R] R)} (hφ : ∀ x, spMap (φ x) ≫ T.y = pt x) (g : N → C) :
    g ∈ torsFun C T pt ↔ ∃ a : T.A, g = fun x => algebraMap R C (φ x a) := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, funext fun x => ha x _ (hφ x)⟩
  · rintro ⟨a, rfl⟩
    refine ⟨a, fun x ψ h => ?_⟩
    rw [tors_ext T (h.trans (hφ x).symm)]

omit [AddCommGroup N] in
theorem mem_vanIdeal (T : TorsRep G p) {φ : N → (T.A →ₐ[R] R)}
    (hφ : ∀ x, spMap (φ x) ≫ T.y = pt x) (K : Set N) (a : T.A) :
    a ∈ vanIdeal T pt K ↔ ∀ k ∈ K, φ k a = 0 := by
  constructor
  · exact fun h k hk => h k hk _ (hφ k)
  · intro h k hk ψ e
    rw [tors_ext T (e.trans (hφ k).symm)]
    exact h k hk

end

theorem tors_hopf : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → (∃ AA : HopfOrder (C := C) R N, AA.carrier = torsFun C T pt) ∧ (∀ a : T.A, (∀ φ : T.A →ₐ[R] R, φ a = 0) → a = 0) ∧ (∀ x, ∃! φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt x) ∧ (∀ φ : T.A →ₐ[R] R, ∃ x, spMap φ ≫ T.y = pt x) ∧ ∀ x : N, p • x = 0 := by
  intro p _ C _ _ _ v R _ _ hv hp G _ _ T N _ _ _ pt hpt
  obtain ⟨Δ, ε, s, hΔ, -, -, h1, h2, h3, h4, h5⟩ := tors_alg R p G T
  obtain ⟨φ, hφ⟩ := exists_pts T hpt
  have hsurj : ∀ ψ : T.A →ₐ[R] R, ∃ x, spMap ψ ≫ T.y = pt x := fun ψ =>
    ((hpt.range _).1 (tors_pow T ψ)).imp fun _ h => h.symm
  have hbij : Function.Bijective φ :=
    ⟨fun x y h => hpt.inj (by rw [← hφ, ← hφ, h]),
      fun ψ => (hsurj ψ).imp fun x h => tors_ext T ((hφ x).trans h.symm)⟩
  let : Bialgebra R T.A := Bialgebra.ofAlgHom Δ ε h1 h2 h3
  let : HopfAlgebra R T.A := HopfAlgebra.ofAlgHom s h4 (by
    change AlgHom.comp _ Δ = AlgHom.comp _ ε
    rw [← h4]
    conv_lhs => rw [← h5, ← AlgHom.comp_assoc]
    congr 1
    ext <;> simp)
  have : Coalgebra.IsCocomm R T.A := ⟨congr(($h5).toLinearMap)⟩
  have := T.fin
  have := T.free
  obtain ⟨hsep, -, AA, hAA⟩ := hopfalg p C v R hv hp T.A N φ hbij (fun x y a => by
    have : φ (x + y) = (Algebra.TensorProduct.lift (φ x) (φ y) (fun _ _ => Commute.all _ _)).comp Δ := by
      apply tors_ext T
      rw [lift_comul T Δ hΔ, Algebra.TensorProduct.lift_comp_includeLeft,
        show (Algebra.TensorProduct.lift (φ x) (φ y) (fun _ _ => Commute.all _ _)).comp
          Algebra.TensorProduct.includeRight = φ y by ext; simp, hφ, hφ, hφ, hpt.add]
    rw [this]
    rfl)
  refine ⟨⟨AA, ?_⟩, fun a ha => hsep a fun x => ha _, fun x => ?_, hsurj, fun x => hpt.inj ?_⟩
  · ext g
    rw [hAA, mem_torsFun T hφ]
  · exact T.univ R (pt x) ((hpt.range _).2 ⟨x, rfl⟩)
  · rw [pt_nsmul hpt, pt_zero hpt]
    exact (hpt.range _).2 ⟨x, rfl⟩

end PositivityTheory.HtPt.Rf
end

section

noncomputable section

namespace PositivityTheory.HtPt.Htat

open GlobalTheory.CompanionTheory.Ar.HT NumberField TensorProduct

theorem chart_build : ∀ (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (p R N : ℕ) (W Ω : Type) [AddCommGroup W] [Module A W] [Module.Finite A W] [Module.Projective A W] [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (j : W →ₗ[A] Ω), IsBaseChange K j → ∀ (ρ : 𝓞 E →+* Module.End A W) (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ R)) (h : (Fin N → 𝓞 E) →+ W), (∀ x, e x x = 0) → (∀ (a : 𝓞 E) (x y : Fin N → 𝓞 E), e (a • x) y = e x (RingOfIntegers.mapRingEquiv c a • y)) → (∀ φ : (Fin N → 𝓞 E) →+ ZMod (p ^ R), ∃ x, e x = φ) → (∀ x, e x = 0 → ∃ x', x = (p ^ R) • x') → (∀ (a : 𝓞 E) x, ∃ y, h (a • x) = ρ a (h x) + (p ^ R) • y) → ∃ D : HTChart A K c p R N Ω, D.om = LinearMap.range j ∧ D.e = e ∧ (∀ x, D.h x = j (h x)) ∧ ∀ a w, D.ρΩ a (j w) = j (ρ a w) := by
  intro A K _ _ _ _ _ E _ _ c p R N W Ω _ _ _ _ _ _ _ _ j hj ρ e h halt hadj hsurj hinj hlin
  classical
  have hsym : ∀ w : W, hj.equiv.symm (j w) = (1 : K) ⊗ₜ[A] w := by
    intro w
    rw [LinearEquiv.symm_apply_eq, IsBaseChange.equiv_tmul, one_smul]
  let T : 𝓞 E →+* Module.End K (K ⊗[A] W) := (Module.End.baseChangeHom A K W).toRingHom.comp ρ
  have hT : ∀ a (w : W), T a ((1 : K) ⊗ₜ[A] w) = (1 : K) ⊗ₜ[A] (ρ a w) := fun a w => rfl
  let ρΩ : 𝓞 E →+* Module.End K Ω :=
    { toFun := fun a => hj.equiv.toLinearMap ∘ₗ T a ∘ₗ hj.equiv.symm.toLinearMap
      map_one' := by ext x; simp
      map_mul' := by intro a b; ext x; simp [Module.End.mul_apply]
      map_zero' := by ext x; simp
      map_add' := by intro a b; ext x; simp }
  have hρ : ∀ a w, ρΩ a (j w) = j (ρ a w) := by
    intro a w
    show hj.equiv (T a (hj.equiv.symm (j w))) = _
    rw [hsym, hT, IsBaseChange.equiv_tmul, one_smul]
  have hinjj : Function.Injective j := by
    have h1 : Function.Injective ((Algebra.linearMap A K).rTensor W) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective A K)
    intro x y hxy
    apply (TensorProduct.lid A W).symm.injective
    apply h1
    apply hj.equiv.injective
    simp only [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one,
      IsBaseChange.equiv_tmul, one_smul]
    exact hxy
  have hfg : (LinearMap.range j).FG := Module.Finite.iff_fg.mp (Module.Finite.range j)
  have hspan : Submodule.span K (LinearMap.range j : Set Ω) = ⊤ := by
    rw [eq_top_iff]
    intro ω hω
    clear hω
    obtain ⟨t, rfl⟩ := hj.equiv.surjective ω
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s w =>
      rw [IsBaseChange.equiv_tmul]
      exact Submodule.smul_mem _ s (Submodule.subset_span ⟨w, rfl⟩)
    | add x y hx hy =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hx hy
  have hproj : Module.Projective A (LinearMap.range j) :=
    Module.Projective.of_equiv (LinearEquiv.ofInjective j hinjj)
  refine ⟨{ om := LinearMap.range j
            om_lat := by
              have hfull : Submodule.IsFullLattice K (LinearMap.range j) :=
                { toIsLattice := Submodule.IsLattice.of_fg K hfg, span_eq_top := hspan }
              first | exact hfull | exact hfull.toIsLattice
            om_proj := hproj
            ρΩ := ρΩ
            om_stable := ?_
            e := e
            alt := halt
            adj := hadj
            e_surj := hsurj
            e_inj := hinj
            h := j.toAddMonoidHom.comp h
            h_mem := fun x => ⟨h x, rfl⟩
            h_lin := ?_ }, rfl, rfl, fun x => rfl, hρ⟩
  · rintro a x ⟨w, rfl⟩
    exact ⟨ρ a w, (hρ a w).symm⟩
  · intro a x
    obtain ⟨y, hy⟩ := hlin a x
    refine ⟨j y, ⟨y, rfl⟩, ?_⟩
    show j (h (a • x)) = ρΩ a (j (h x)) + p ^ R • j y
    rw [hy, map_add (f := _), map_nsmul, hρ]

end PositivityTheory.HtPt.Htat
end
end

section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace PositivityTheory.HtPt.Gf

theorem trivflag_mono : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ϖ ϖ' : o) (N : ℕ) (b : Fin N → K → ℤ), ϖ' ∣ ϖ → Num.TrivFlagMod o ϖ y N b → Num.TrivFlagMod o ϖ' y N b := by
  intro o _ Ω _ _ K _ J _ y ϖ ϖ' N b ⟨c, hc⟩ ⟨g, h1, h2⟩
  refine ⟨g, fun s hs => ?_, fun s t hs ht => ?_⟩
  · obtain ⟨hg, h, hh, r, hr, e⟩ := h1 s hs
    refine ⟨hg, h, hh, algebraMap o Ω c * r, mul_mem (Subalgebra.algebraMap_mem _ c) hr, ?_⟩
    rw [e, hc, map_mul, mul_assoc]
  · obtain ⟨m, U, Z, hU, hZ, hU0, hUd, hm, e⟩ := h2 s t hs ht
    refine ⟨m, U, algebraMap o Ω c • Z, hU, fun i j => ?_, hU0, hUd, hm, ?_⟩
    · rw [Matrix.smul_apply, smul_eq_mul]
      exact mul_mem (Subalgebra.algebraMap_mem _ c) (hZ i j)
    · rw [e, hc, map_mul, mul_smul]

end PositivityTheory.HtPt.Gf
end

section

noncomputable section

namespace PositivityTheory.HtPt.Ga

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

section

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  (D : HTChart A K c p R N Ω)

theorem h_mem_om' (x : Fin N → 𝓞 E) : D.h x ∈ D.om' :=
  Submodule.mem_sup_left (Submodule.subset_span ⟨x, rfl⟩)

theorem proj_mem_omHT (σ : E →+* K) {y : Ω} (hy : y ∈ D.om') : eigProj D.ρΩ σ y ∈ D.omHT σ :=
  ⟨y, hy, rfl⟩

theorem q_mem (σ : E →+* K) (x : Fin N → A) : D.q σ x ∈ D.omHT σ := by
  unfold HTChart.q
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  exact proj_mem_omHT D σ (h_mem_om' D _)

theorem q_add (σ : E →+* K) (x y : Fin N → A) : D.q σ (x + y) = D.q σ x + D.q σ y := by
  unfold HTChart.q
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem q_smul (σ : E →+* K) (a : A) (x : Fin N → A) : D.q σ (a • x) = a • D.q σ x := by
  unfold HTChart.q
  simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

private theorem toZMod_cycZ_eq_one_of_cycMod_eq_one (σ : E →+* K) (hσ : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range)
    (z : Fin N → 𝓞 E) :
    ∃ x : Fin N → A, ∃ y' ∈ D.om, eigProj D.ρΩ σ (D.h z) = D.q σ x + ((p : A) ^ R) • eigProj D.ρΩ σ y' := by
  choose y hy he using fun i => D.h_lin (z i) (Pi.single i 1)
  choose b hb using fun i => hσ (z i)
  have hz : z = ∑ i, z i • Pi.single i (1 : 𝓞 E) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hrho : ∀ (a : 𝓞 E) (v : Ω), eigProj D.ρΩ σ (D.ρΩ a v) = σ (a : E) • eigProj D.ρΩ σ v := by
    intro a v
    have h1 := congrArg (fun f : Module.End K Ω => f v) (ProjEig.eigProj_mul_rho_comm D.ρΩ σ a)
    have h2 := congrArg (fun f : Module.End K Ω => f v) (ProjEig.rho_mul_eigProj D.ρΩ σ a)
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at h1 h2
    rw [h1, h2]
  refine ⟨b, ∑ i, y i, Submodule.sum_mem _ fun i _ => hy i, ?_⟩
  conv_lhs => rw [hz]

  rw [map_sum, map_sum]
  simp only [he, map_add (f := _), hrho, ← hb, algebraMap_smul]

  rw [Finset.sum_add_distrib, map_sum, Finset.smul_sum]
  unfold HTChart.q
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_nsmul, ← Nat.cast_smul_eq_nsmul A]
  push_cast
  rfl

theorem exists_q_add (σ : E →+* K) (hσ : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range)
    {y : Ω} (hy : y ∈ D.om') :
    ∃ x : Fin N → A, ∃ y' ∈ D.om, eigProj D.ρΩ σ y = D.q σ x + ((p : A) ^ R) • eigProj D.ρΩ σ y' := by
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨y0, hy0, rfl⟩ := Submodule.mem_map.mp ht
  clear hy ht
  have key : ∃ x : Fin N → A, ∃ y' ∈ D.om,
      eigProj D.ρΩ σ s = D.q σ x + ((p : A) ^ R) • eigProj D.ρΩ σ y' := by
    induction hs using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨z, rfl⟩ := hv
      exact toZMod_cycZ_eq_one_of_cycMod_eq_one D σ hσ z
    | zero => exact ⟨0, 0, D.om.zero_mem, by simp [HTChart.q]⟩
    | add u v _ _ hu hv =>
      obtain ⟨x1, y1, hy1, e1⟩ := hu
      obtain ⟨x2, y2, hy2, e2⟩ := hv
      refine ⟨x1 + x2, y1 + y2, D.om.add_mem hy1 hy2, ?_⟩
      rw [map_add (f := _), e1, e2, q_add, map_add (f := _), smul_add]
      abel
    | smul a v _ hv =>
      obtain ⟨x1, y1, hy1, e1⟩ := hv
      refine ⟨a • x1, a • y1, D.om.smul_mem a hy1, ?_⟩
      rw [LinearMap.map_smul_of_tower, e1, q_smul, LinearMap.map_smul_of_tower, smul_add, smul_comm a]
  obtain ⟨x, y', hy', e⟩ := key
  have ht0 : eigProj D.ρΩ σ (((p : A) ^ R • LinearMap.id : Ω →ₗ[A] Ω) y0)
      = ((p : A) ^ R) • eigProj D.ρΩ σ y0 := by
    simp [LinearMap.map_smul_of_tower]
  refine ⟨x, y' + y0, D.om.add_mem hy' hy0, ?_⟩
  rw [map_add (f := _), e, ht0, map_add (f := _), smul_add, add_assoc]

end

theorem q_surj : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (m : ℕ), (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → κ * (p : A) ^ m ∣ (p : A) ^ R → (∀ x ∈ D.om, κ • x ∈ D.om') → (∀ x, D.q σ x ∈ D.omHT σ) ∧ (D.omHT σ).FG ∧ ∀ y ∈ D.omHT σ, ∃ x : Fin N → A, ∃ y' ∈ D.omHT σ, y = D.q σ x + ((p : A) ^ m) • y' := by
  intro A K _ _ _ _ hAK E _ _ c hc p R N _ Ω _ _ _ _ D κ σ m hσ hdiv hκ
  classical
  refine ⟨fun x => q_mem D σ x, ?_, ?_⟩
  · unfold HTChart.omHT eigQuot
    apply Submodule.FG.map
    unfold HTChart.om'
    refine Submodule.FG.sup ?_ (Submodule.FG.map _ D.om_lat.fg)
    obtain ⟨T, hT⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (Fin N → 𝓞 E)).FG)
    refine ⟨T.image D.h, le_antisymm ?_ ?_⟩
    · apply Submodule.span_mono
      intro v hv
      simp only [Finset.coe_image, Set.mem_image] at hv
      obtain ⟨z, _, rfl⟩ := hv
      exact ⟨z, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨z, rfl⟩
      have hz : z ∈ Submodule.span ℤ (T : Set (Fin N → 𝓞 E)) := hT ▸ Submodule.mem_top
      induction hz using Submodule.span_induction with
      | mem w hw =>
        exact Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨w, hw, rfl⟩)
      | zero => simp
      | add u v _ _ hu hv =>
        rw [map_add (f := _)]
        exact Submodule.add_mem _ hu hv
      | smul n u _ hu =>
        rw [map_zsmul]
        exact zsmul_mem hu n
  · intro y hy
    simp only [HTChart.omHT, eigQuot] at hy
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hy
    obtain ⟨x, y'', hy'', e⟩ := exists_q_add D σ hσ hw
    obtain ⟨d, hd⟩ := hdiv
    refine ⟨x, d • eigProj D.ρΩ σ (κ • y''), ?_, ?_⟩
    · exact Submodule.smul_mem _ d (proj_mem_omHT D σ (hκ y'' hy''))
    · rw [LinearMap.restrictScalars_apply, e, hd, LinearMap.map_smul_of_tower]
      congr 1
      simp only [smul_smul]
      congr 1
      ring

end PositivityTheory.HtPt.Ga
end
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Ch

theorem unitAt_div {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {Λ : Lat ξ Ω} {p : Cpt ξ} {s t : Ω} (hs : Λ.IsGenAt p s) (ht : Λ.IsGenAt p t) :
    unitAt ξ p (s / t) := by
  have key : ∀ {s t : Ω}, Λ.IsGenAt p s → Λ.IsGenAt p t → s / t ∈ regAt ξ p := by
    intro s t hs ht
    have : s ∈ Submodule.span (regAt ξ p) {t} := by
      rw [← ht.2, hs.2]; exact Submodule.mem_span_singleton_self s
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 this
    have ha' : (a : Ω) * t = s := ha
    rw [← ha', mul_div_cancel_right₀ _ ht.1]
    exact a.2
  exact ⟨div_ne_zero hs.1 ht.1, key hs ht, by rw [inv_div]; exact key ht hs⟩

theorem isdeg_unique : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (Λ : Lat ξ Ω) (n n' : ℤ), IsCptGen ξ → Y.IsDeg Λ n → Y.IsDeg Λ n' → n = n' := by
  intro X Ω _ ξ K _ C z Y Λ n n' hξ ⟨h₀, h, s₀, s, r, g₀, g, hr, hf, e⟩
    ⟨h₀', h', s₀', s', r', g₀', g', hr', hf', e'⟩
  obtain ⟨φ, hφ, hu⟩ := ValHom.exists_valAt_hom X Ω ξ K z h₀ hξ
  have u₀ := unitAt_div g₀' g₀
  let c : K := φ ⟨s₀' / s₀, u₀.2.1⟩
  have hc : c ≠ 0 := ((hu ⟨_, u₀.2.1⟩).2 u₀).ne_zero
  have key : ∀ i, C.v i (r i) = C.v i (r' i) * C.v i c := by
    intro i
    obtain ⟨ψ, hψ, hv⟩ := ValHom.exists_valAt_hom X Ω ξ _ (Y.x i) (h i) hξ
    have u := unitAt_div (g i) (g' i)
    have hun : IsUnit (ψ ⟨_, u.2.1⟩) := (hv ⟨_, u.2.1⟩).2 u
    have hval := GlobalTheory.T.valAt_comp_local_hom X Ω ξ _ K (C.v i).valuationSubring.subtype (Y.x i) _ _
      ((hψ _ _).2 ⟨u.2.1, rfl⟩) (by rw [Y.gen i]; exact h₀)
    rw [Y.gen i] at hval
    obtain ⟨m1, e1⟩ := (hφ _ _).1 hval
    obtain ⟨m2, e2⟩ := (hφ _ _).1 (hr i).2
    obtain ⟨m3, e3⟩ := (hφ _ _).1 (hr' i).2
    have hone : C.v i ((C.v i).valuationSubring.subtype (ψ ⟨_, u.2.1⟩)) = 1 := by
      obtain ⟨w, hw⟩ := hun.exists_right_inv
      have h1 : C.v i ((ψ ⟨_, u.2.1⟩ : (C.v i).valuationSubring) : K) * C.v i (w : K) = 1 := by
        rw [← map_mul, ← MulMemClass.coe_mul, hw]; simp
      exact le_antisymm (ψ ⟨_, u.2.1⟩).2 (h1 ▸ mul_le_of_le_one_right' w.2)
    have : r i = (C.v i).valuationSubring.subtype (ψ ⟨_, u.2.1⟩) * (r' i * c) := by
      rw [← e1, ← e2, ← e3, ← map_mul, ← map_mul]
      congr 1
      refine Subtype.ext ?_
      have := (g' i).1
      have := g₀'.1
      have := g₀.1
      simp only [MulMemClass.coe_mul]
      field_simp
    rw [this, map_mul, hone, one_mul, map_mul]
  have h2 : ∀ i, (C.w i : ℤ) * WithZero.log (C.v i (r i)) =
      (C.w i : ℤ) * WithZero.log (C.v i (r' i)) + (C.w i : ℤ) * WithZero.log (C.v i c) := by
    intro i
    rw [key, WithZero.log_mul ((Valuation.ne_zero_iff _).2 (hr' i).1)
      ((Valuation.ne_zero_iff _).2 hc), mul_add]
  rw [e, e']
  simp only [h2]
  rw [finsum_add_distrib (hf'.subset fun i hi h1 => hi (by simp [h1]))
    ((C.fin c hc).subset fun i hi h1 => hi (by simp [h1])), C.prod c hc, add_zero]

end PositivityTheory.HtPt.Ch
end
