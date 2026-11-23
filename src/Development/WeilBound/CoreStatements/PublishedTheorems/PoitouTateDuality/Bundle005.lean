module

public import GroundTheory.ProfiniteCohomology.PoitouTate.PtCompactDualMapEqZeroOfPtCompactToGlobalEqZero
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle001
import GroundTheory.ProfiniteCohomology.CupProducts.Cocycles
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open CategoryTheory GroundTheory.ProfCoh

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

def reindexAdd {α β : Type} (P : β → Type) [∀ b, AddCommGroup (P b)] (e : α ≃ β) :
    (∀ a, P (e a)) ≃+ (∀ b, P b) :=
  { Equiv.piCongrLeft P e with
    map_add' := fun f g => by
      funext b
      obtain ⟨a, rfl⟩ := e.surjective b
      simp only [Equiv.toFun_as_coe, Pi.add_apply, Equiv.piCongrLeft_apply_apply] }

theorem reindexAdd_apply {α β : Type} (P : β → Type) [∀ b, AddCommGroup (P b)] (e : α ≃ β)
    (f : ∀ a, P (e a)) (a : α) : reindexAdd P e f (e a) = f a :=
  Equiv.piCongrLeft_apply_apply P e f a

theorem reindexAdd_symm_apply {α β : Type} (P : β → Type) [∀ b, AddCommGroup (P b)] (e : α ≃ β)
    (g : ∀ b, P b) (a : α) : (reindexAdd P e).symm g a = g (e a) := by
  have h := reindexAdd_apply P e ((reindexAdd P e).symm g) a
  rw [AddEquiv.apply_symm_apply] at h
  exact h.symm

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type} {Hv : ι → Type} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)

theorem ptLocalDualMap_reindex [Fintype ι] {κ : Type} [Fintype κ] (e : κ ≃ ι)
    (D : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep D] (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M]
    [Finite M] (inv : ∀ v, cohomology (Rep.res (φ v).toMonoidHom D) 2 →+ QZ) {r s : ℕ}
    (h : r + s = 2) (ξ : ∀ k, cohomology (Rep.res (φ (e k)).toMonoidHom M) r)
    (y : cohomology (dualRep D M) s) :
    ptLocalDualMap φ D M inv h
        (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) r) e ξ) y =
      ∑ k, ptLocalPairing φ D M inv (e k) h (ξ k) (ptRes φ (dualRep D M) (e k) s y) := by
  rw [ptLocalDualMap_apply]
  refine (Fintype.sum_equiv e _ _ (fun k => ?_)).symm
  rw [reindexAdd_apply]

theorem ptGlobalToLocal_reindex {κ : Type} (e : κ ≃ ι) (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M]
    (r : ℕ) (x : cohomology M r) (k : κ) :
    (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) r) e).symm
      ((ptGlobalToLocal φ M r).hom x) k = ptRes φ M (e k) r x := by
  rw [reindexAdd_symm_apply, ptGlobalToLocal_apply]

theorem locSq_reindex {κ : Type} (e : κ ≃ ι) (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M] (r : ℕ)
    {X : Type} [AddCommGroup X] {Xk : κ → Type} [∀ k, AddCommGroup (Xk k)]
    (res : ∀ k, X →+ Xk k) (E : X ≃+ cohomology M r)
    (Ev : ∀ k, Xk k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom M) r)
    (sq : ∀ k x, Ev k (res k x) = ptRes φ M (e k) r (E x)) (x : X) :
    (ptGlobalToLocal φ M r).hom (E x) =
      reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) r) e (fun k => Ev k (res k x)) := by
  apply (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) r) e).symm.injective
  rw [AddEquiv.symm_apply_apply]
  funext k
  rw [ptGlobalToLocal_reindex, sq]

def finsetCoeEquiv {α : Type} (S : Finset α) : S ≃ (S : Set α) where
  toFun v := ⟨v.1, Finset.mem_coe.2 v.2⟩
  invFun w := ⟨w.1, Finset.mem_coe.1 w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end PositivityTheory.Lit1.PTN
end
end

section

noncomputable section

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem resH1_bijective_of_inverse {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {R M : Type} [CommRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (rho : Representation R G M) (ψ : H →* G) (hψ : Continuous ψ)
    (χ : G →* H) (hχ : Continuous χ) (h1 : ∀ g, ψ (χ g) = g) (h2 : ∀ h, χ (ψ h) = h) :
    Function.Bijective (resH1 rho ψ hψ) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      rw [Submodule.Quotient.mk_eq_zero]
      rw [resH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hx
      refine (mem_coboundaries1 _ _).2 ⟨m, fun g => ?_⟩
      have e := hm (χ g)
      simp only [Submodule.coe_subtype] at e ⊢
      change z.1 (ψ (χ g)) = rho (ψ (χ g)) m - m at e
      rw [h1] at e
      exact e
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      refine ⟨Submodule.Quotient.mk ⟨z.1 ∘ χ, z.2.1.comp hχ, fun g h => ?_⟩, ?_⟩
      · have e := z.2.2 (χ g) (χ h)
        simp only [Function.comp_apply, map_mul]
        rw [e]
        change z.1 (χ g) + rho (ψ (χ g)) (z.1 (χ h)) = _
        rw [h1]
      · rw [resH1, Submodule.mapQ_apply]
        congr 1
        apply Subtype.ext
        funext h
        change z.1 (χ (ψ h)) = z.1 h
        rw [h2]

theorem resCmp1' {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (θ : G ≃ₜ* H) {ι : Type} {Lv Hv : ι → Type}
    [∀ v, Group (Lv v)] [∀ v, TopologicalSpace (Lv v)] [∀ v, IsTopologicalGroup (Lv v)]
    [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)] [∀ v, IsTopologicalGroup (Hv v)]
    (lam : ∀ v, Lv v →* G) (hlam : ∀ v, Continuous (lam v)) (φ : ∀ v, Hv v →ₜ* H)
    (ev : ∀ v, Hv v ≃* Lv v) (hev1 : ∀ v, Continuous (ev v)) (hev2 : ∀ v, Continuous (ev v).symm)
    (hev : ∀ v σ, θ (lam v (ev v σ)) = φ v σ) {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R G M) (hc : ContAction rho)
    (A : Rep.{0} (ULift.{0} ℤ) H) [IsDiscreteRep A] (eM : M ≃+ A.V)
    (hM : ∀ g m, eM (rho g m) = A.ρ (θ g) (eM m)) :
    ∃ (E : H1 rho ≃+ cohomology A 1)
      (Ev : ∀ v, H1 (rho.comp (lam v)) ≃+ cohomology (Rep.res (φ v).toMonoidHom A) 1),
      ∀ v x, Ev v (resH1 rho (lam v) (hlam v) x) = ptRes φ A v 1 (E x) := by
  have hθs : Continuous (θ.symm : H ≃* G).toMonoidHom := θ.symm.continuous
  let rho' : Representation R H M := rho.comp (θ.symm : H ≃* G).toMonoidHom
  have hM' : ∀ h m, eM (rho' h m) = A.ρ h (eM m) := fun h m => by
    show eM (rho (θ.symm h) m) = _
    rw [hM]
    simp
  obtain ⟨e1, he1a, he1b⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 H R M rho' A eM hM'
  have bij := resH1_bijective_of_inverse rho (θ.symm : H ≃* G).toMonoidHom hθs
    (θ : G ≃* H).toMonoidHom θ.continuous (fun g => θ.symm_apply_apply g) (fun h => θ.apply_symm_apply h)
  let r1 : H1 rho ≃ₗ[R] H1 rho' := LinearEquiv.ofBijective _ bij
  have hloc : ∀ v, ∀ σ m, eM (((rho.comp (lam v)).comp (ev v).toMonoidHom) σ m) =
      (Rep.res (φ v).toMonoidHom A).ρ σ (eM m) := fun v σ m => by
    show eM (rho (lam v (ev v σ)) m) = A.ρ (φ v σ) (eM m)
    rw [hM, hev]
  choose ev1 hev1a hev1b using fun v => PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 (Hv v) R M
    ((rho.comp (lam v)).comp (ev v).toMonoidHom) (Rep.res (φ v).toMonoidHom A) eM (hloc v)
  have bijv := fun v => resH1_bijective_of_inverse (rho.comp (lam v)) (ev v).toMonoidHom (hev1 v)
    (ev v).symm.toMonoidHom (hev2 v) (fun g => (ev v).apply_symm_apply g) (fun h => (ev v).symm_apply_apply h)
  let rv : ∀ v, H1 (rho.comp (lam v)) ≃ₗ[R] H1 ((rho.comp (lam v)).comp (ev v).toMonoidHom) :=
    fun v => LinearEquiv.ofBijective _ (bijv v)
  refine ⟨r1.toAddEquiv.trans e1, fun v => (rv v).toAddEquiv.trans (ev1 v), fun v x => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    obtain ⟨y, hy⟩ := he1a (restrictCocycles1 rho (θ.symm : H ≃* G).toMonoidHom hθs z)
    have hE : e1 (r1 (Submodule.Quotient.mk z)) = cohomologyπ A 1 y := he1b _ y hy
    show ev1 v (rv v (resH1 rho (lam v) (hlam v) (Submodule.Quotient.mk z))) =
      ptRes φ A v 1 (e1 (r1 (Submodule.Quotient.mk z)))
    rw [hE]
    have hP : ptRes φ A v 1 (cohomologyπ A 1 y) =
        cohomologyπ _ 1 (cocyclesMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) 1 y) := by
      unfold ptRes
      exact congrArg (fun f => f.hom y) (cohomologyπ_cohomologyMapAlong (φ v).toMonoidHom
        (continuous_toMonoidHom (φ v)) (𝟙 _) 1)
    rw [hP]
    apply hev1b v
    intro s
    rw [cochainOf_cocycleι_cocyclesMapAlong]
    dsimp only
    rw [hy]
    change eM (z.1 (θ.symm (φ v (s 0)))) = eM (z.1 (lam v (ev v (s 0))))
    rw [← hev]
    exact congrArg (fun t => eM (z.1 t)) (θ.symm_apply_apply _)

end PositivityTheory.Lit1.PTN
end
end

section

noncomputable section

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem resH2_bijective_of_inverse {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {R M : Type} [CommRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (rho : Representation R G M) (ψ : H →* G) (hψ : Continuous ψ)
    (χ : G →* H) (hχ : Continuous χ) (h1 : ∀ g, ψ (χ g) = g) (h2 : ∀ h, χ (ψ h) = h) :
    Function.Bijective (resH2 rho ψ hψ) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      rw [Submodule.Quotient.mk_eq_zero]
      rw [resH2, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem _ _).1 hx
      refine (separated_dvr_second_cohomology_mem _ _).2 ⟨c ∘ χ, hc.comp hχ, ?_⟩
      funext p
      have e := congrFun hcf (χ p.1, χ p.2)
      simp only [Submodule.coe_subtype] at e ⊢
      change _ = z.1 (ψ (χ p.1), ψ (χ p.2)) at e
      rw [h1, h1] at e
      rw [← e]
      simp [d1, h1]
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      refine ⟨Submodule.Quotient.mk ⟨fun p => z.1 (χ p.1, χ p.2),
        z.2.1.comp (hχ.prodMap hχ), fun g h k => ?_⟩, ?_⟩
      · have e := z.2.2 (χ g) (χ h) (χ k)
        simp only [map_mul]
        change rho (ψ (χ g)) _ - _ + _ - _ = 0 at e
        rw [h1] at e
        exact e
      · rw [resH2, Submodule.mapQ_apply]
        congr 1
        apply Subtype.ext
        funext p
        change z.1 (χ (ψ p.1), χ (ψ p.2)) = z.1 p
        rw [h2, h2]

theorem resCmp2B {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (θ : G ≃ₜ* H) {ι : Type} {Lv Hv : ι → Type}
    [∀ v, Group (Lv v)] [∀ v, TopologicalSpace (Lv v)] [∀ v, IsTopologicalGroup (Lv v)]
    [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)] [∀ v, IsTopologicalGroup (Hv v)]
    (lam : ∀ v, Lv v →* G) (hlam : ∀ v, Continuous (lam v)) (φ : ∀ v, Hv v →ₜ* H)
    (ev : ∀ v, Hv v ≃* Lv v) (hev1 : ∀ v, Continuous (ev v)) (hev2 : ∀ v, Continuous (ev v).symm)
    (hev : ∀ v σ, θ (lam v (ev v σ)) = φ v σ) {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R G M) (hc : ContAction rho)
    (A : Rep.{0} (ULift.{0} ℤ) H) [IsDiscreteRep A] (eM : M ≃+ A.V)
    (hM : ∀ g m, eM (rho g m) = A.ρ (θ g) (eM m)) :
    ∃ (E : H2 rho ≃+ cohomology A 2)
      (Ev : ∀ v, H2 (rho.comp (lam v)) ≃+ cohomology (Rep.res (φ v).toMonoidHom A) 2),
      ∀ v x, Ev v (resH2 rho (lam v) (hlam v) x) = ptRes φ A v 2 (E x) := by
  have hθs : Continuous (θ.symm : H ≃* G).toMonoidHom := θ.symm.continuous
  let rho' : Representation R H M := rho.comp (θ.symm : H ≃* G).toMonoidHom
  have hM' : ∀ h m, eM (rho' h m) = A.ρ h (eM m) := fun h m => by
    show eM (rho (θ.symm h) m) = _
    rw [hM]
    exact congrArg (fun t => A.ρ t (eM m)) (θ.apply_symm_apply h)
  obtain ⟨e2, he2a, he2b⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 H R M rho' A eM hM'
  have bij := resH2_bijective_of_inverse rho (θ.symm : H ≃* G).toMonoidHom hθs
    (θ : G ≃* H).toMonoidHom θ.continuous (fun g => θ.symm_apply_apply g)
    (fun h => θ.apply_symm_apply h)
  let r2 : H2 rho ≃ₗ[R] H2 rho' := LinearEquiv.ofBijective _ bij
  have hloc : ∀ v, ∀ σ m, eM (((rho.comp (lam v)).comp (ev v).toMonoidHom) σ m) =
      (Rep.res (φ v).toMonoidHom A).ρ σ (eM m) := fun v σ m => by
    show eM (rho (lam v (ev v σ)) m) = A.ρ (φ v σ) (eM m)
    rw [hM, hev]
  choose ev2 hev2a hev2b using fun v => PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 (Hv v) R M
    ((rho.comp (lam v)).comp (ev v).toMonoidHom) (Rep.res (φ v).toMonoidHom A) eM (hloc v)
  have bijv := fun v => resH2_bijective_of_inverse (rho.comp (lam v)) (ev v).toMonoidHom (hev1 v)
    (ev v).symm.toMonoidHom (hev2 v) (fun g => (ev v).apply_symm_apply g)
    (fun h => (ev v).symm_apply_apply h)
  let rv : ∀ v, H2 (rho.comp (lam v)) ≃ₗ[R] H2 ((rho.comp (lam v)).comp (ev v).toMonoidHom) :=
    fun v => LinearEquiv.ofBijective _ (bijv v)
  refine ⟨r2.toAddEquiv.trans e2, fun v => (rv v).toAddEquiv.trans (ev2 v), fun v x => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    obtain ⟨y, hy⟩ := he2a (restrictCocycles2 rho (θ.symm : H ≃* G).toMonoidHom hθs z)
    have hE : e2 (r2 (Submodule.Quotient.mk z)) = cohomologyπ A 2 y := he2b _ y hy
    show ev2 v (rv v (resH2 rho (lam v) (hlam v) (Submodule.Quotient.mk z))) =
      ptRes φ A v 2 (e2 (r2 (Submodule.Quotient.mk z)))
    rw [hE]
    have hP : ptRes φ A v 2 (cohomologyπ A 2 y) =
        cohomologyπ _ 2 (cocyclesMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) 2 y) := by
      unfold ptRes
      exact congrArg (fun f => f.hom y) (cohomologyπ_cohomologyMapAlong (φ v).toMonoidHom
        (continuous_toMonoidHom (φ v)) (𝟙 _) 2)
    rw [hP]
    apply hev2b v
    intro s
    rw [cochainOf_cocycleι_cocyclesMapAlong]
    dsimp only
    rw [hy]
    change eM (z.1 (θ.symm (φ v (s 0)), θ.symm (φ v (s 1)))) =
      eM (z.1 (lam v (ev v (s 0)), lam v (ev v (s 1))))
    rw [← hev, ← hev]
    exact congrArg (fun t => eM (z.1 t))
      (Prod.ext (θ.symm_apply_apply _) (θ.symm_apply_apply _))

end PositivityTheory.Lit1.PTN
end
end
