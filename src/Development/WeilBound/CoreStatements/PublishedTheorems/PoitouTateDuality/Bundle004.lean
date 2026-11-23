module

public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle184
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle186
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle179
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle178
public import GroundTheory.ProfiniteCohomology.Bundle001
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
public import GroundTheory.ProfiniteCohomology.CupProducts.Bundle002
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle001
public import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohCmpA
public import GroundTheory.ProfiniteCohomology.CupProducts.Bundle003
public import GroundTheory.ProfiniteCohomology.PoincareDuality.NsmulEqZeroOfNonemptyAddEquiv
public import GroundTheory.ProfiniteCohomology.PoincareDuality.TensorHomZmodDualIsoZmodMulPairing
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle153
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

namespace PositivityTheory.PTN

theorem ptConcl_of_iso_of (hL : PositivityTheory.PTN.LocHyp) : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → PTConclAt F' Ω' → PTConclAt F Ω := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE hPT
  intro l _ r hl hr ζ hζ inv hinv S hS Av hAv μ hμ M _ _ _ _ _ ρ hρ
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.galois_group_transport_isomorphism F Ω F' Ω' e E hE
  obtain ⟨eO, eV, heO, hV, hV2, hN⟩ := GlobalTheory.T.ring_isomorphism_transports_places F F' e
  have hloc := hL F Ω F' Ω' e E hE Φ hΦ
  have hpl := GlobalTheory.T.ring_equiv_transports_decomposition F Ω F' Ω' e E hE eO eV heO hV
  have hcyc := GlobalTheory.T.ring_equiv_cyclotomic_character F Ω F' Ω' e E hE Φ hΦ l r
  obtain ⟨inv', hinv'⟩ := GlobalTheory.T.ring_equiv_transports_inertia F Ω F' Ω' e E hE Φ hΦ
    (fun A A' hA σ => (hloc A A' hA σ).1) l r hcyc inv

  let S' : Finset (HeightOneSpectrum (𝓞 F')) := S.map eV.toEmbedding
  have hSS : ∀ v, v ∈ (S : Set (HeightOneSpectrum (𝓞 F))) ↔
      eV v ∈ (S' : Set (HeightOneSpectrum (𝓞 F'))) := by
    intro v; simp [S']
  let eI : S ≃ S' := Equiv.subtypeEquiv eV (fun v => by simp [S'])
  have heI : ∀ v : S, (eI v : HeightOneSpectrum (𝓞 F')) = eV v := fun _ => rfl
  let Av' : S' → ValuationSubring Ω' := fun v' => (Av (eI.symm v')).comap E.symm.toRingHom
  have hAv'' : ∀ (v : S) (x : Ω), E x ∈ Av' (eI v) ↔ x ∈ Av v := by
    intro v x
    simp [Av', ValuationSubring.mem_comap]
  have hPl' : ∀ v' : S', IsPlaceOver (Av' v') v'.1 := by
    intro v'
    obtain ⟨v, rfl⟩ := eI.surjective v'
    exact (hpl _ _ (hAv'' v) v.1).1 (hAv v)

  obtain ⟨Ψ, hΨ⟩ := GlobalTheory.T.galois_quotient_equiv_of_matching_places F Ω F' Ω' e E hE Φ hΦ eV hpl
    (fun A A' hA σ => (hloc A A' hA σ).2.1) _ _ hSS
  let μ' : GS Ω' (S' : Set (HeightOneSpectrum (𝓞 F'))) →* (ZMod (l ^ r))ˣ :=
    μ.comp (Ψ.symm : GS Ω' (S' : Set (HeightOneSpectrum (𝓞 F'))) →* _)
  have hμ' : μ'.comp (toGS Ω' _) = cycMod F' Ω' l r := by
    ext1 τ
    obtain ⟨σ, rfl⟩ := Φ.surjective τ
    have h1 : Ψ.symm (toGS Ω' _ (Φ σ)) = toGS Ω _ σ := by rw [← hΨ]; simp
    have h2 : μ (toGS Ω _ σ) = cycMod F Ω l r σ := DFunLike.congr_fun hμ σ
    show μ (Ψ.symm (toGS Ω' _ (Φ σ))) = _
    rw [h1, h2, hcyc]
  let ρ' : Representation (ZMod (l ^ r)) (GS Ω' (S' : Set (HeightOneSpectrum (𝓞 F')))) M :=
    ρ.comp (Ψ.symm : GS Ω' (S' : Set (HeightOneSpectrum (𝓞 F'))) →* _)
  have hρ' : ContAction ρ' := hρ.comp' Ψ.symm.continuous

  have hl' : l ≠ 2 ∨ IsTotallyComplex F' := hl.imp id (GlobalTheory.T.totally_complex_of_ring_equiv F F' e)
  have hζ' : IsPrimitiveRoot (E ζ) (l ^ r) := hζ.map_of_injective E.injective
  have hnorm' : InvNormalised (E ζ) inv' := by
    intro A' v' hP
    obtain ⟨v, rfl⟩ := eV.surjective v'
    let A : ValuationSubring Ω := A'.comap E.toRingHom
    have hA : ∀ x, E x ∈ A' ↔ x ∈ A := fun x => by simp [A, ValuationSubring.mem_comap]
    have hP0 : IsPlaceOver A v := (hpl A A' hA v).2 hP
    refine ⟨(hinv' A A' hA).1 (hinv A v hP0).1, ?_⟩
    exact GlobalTheory.T.ring_equiv_transports_residue F Ω F' Ω' e E hE Φ hΦ eO eV heO hV hV2 hN l r hcyc A A' hA (hloc A A' hA) ζ v
      (inv A) (inv' A') (hinv' A A' hA).2 (hinv A v hP0).2
  have hS' : ContainsAbove S' l := by
    intro v' hv'
    obtain ⟨v, rfl⟩ := eV.surjective v'
    have : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal := by
      rw [hV, map_natCast]; exact hv'
    exact Finset.mem_map_of_mem _ (hS v this)
  obtain ⟨h9, hsha⟩ := hPT l r hl' hr (E ζ) hζ' inv' hnorm' S' hS' Av' hPl' μ' hμ' M ρ' hρ'

  let eD : ∀ v : S, Dec (F := F) (Av v) ≃ₜ* Dec (F := F') (Av' (eI v)) := fun v =>
    subgroupIso Φ _ _ (fun σ => (hloc _ _ (hAv'' v) σ).1)
  have hcomp : ∀ (v : S) (d : Dec (F := F) (Av v)),
      locFam S' Av' (eI v) (eD v d) = Ψ (locFam S Av v d) := by
    intro v d
    exact (hΨ (d : G F Ω)).symm
  have hχ : ∀ g, μ' (Ψ g) = μ g := fun g => by simp [μ']
  have hρc : ∀ g m, ρ' (Ψ g) m = ρ g m := fun g m => by simp [ρ']
  refine ⟨?_, ?_⟩
  · refine (nineTermExact_iff S Av μ _ ρ hρ).2 ?_
    refine GlobalTheory.T.poitou_tate_sequence_transport (locFam S Av) (continuous_locFam S Av) (locFam S' Av') (continuous_locFam S' Av')
      μ μ' ρ ρ' Ψ eI eD hcomp hχ hρc _ _ hρ hρ' ?_ ((nineTermExact_iff S' Av' μ' _ ρ' hρ').1 h9)
    intro v z z' hz
    refine (hinv' _ _ (hAv'' v)).2 (cocycles2Map _ _ LinearMap.id continuous_id (locFam_apply_eq S Av μ hμ v) z)
      (cocycles2Map _ _ LinearMap.id continuous_id (locFam_apply_eq S' Av' μ' hμ' (eI v)) z') ?_
    intro g h g' h' hg hh
    have e1 : g' = eD v g := Subtype.ext hg
    have e2 : h' = eD v h := Subtype.ext hh
    subst e1 e2
    exact hz g h
  · exact (shaDual_iff S Av μ ρ).2 (GlobalTheory.T.tate_shafarevich_transport (locFam S Av) (continuous_locFam S Av) (locFam S' Av')
      (continuous_locFam S' Av') μ μ' ρ ρ' Ψ eI eD hcomp hχ hρc ((shaDual_iff S' Av' μ' ρ').1 hsha))

end PositivityTheory.PTN
end
end

section

noncomputable section

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal

namespace PositivityTheory.Lit1.PTN

theorem repCmp {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (θ : G ≃ₜ* H) {R M : Type} [CommRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (rho : Representation R G M) (hc : ContAction rho) :
    ∃ (A : Rep.{0} (ULift.{0} ℤ) H) (_ : IsDiscreteRep A) (eM : M ≃+ A.V),
      ∀ g m, eM (rho g m) = A.ρ (θ g) (eM m) := by
  obtain ⟨A, hA, eM, h⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gcRep G R M rho hc
  refine ⟨Rep.res (θ.symm : H ≃* G).toMonoidHom A,
    IsDiscreteRep.res θ.symm.continuous (φ := (θ.symm : H ≃* G).toMonoidHom) A, eM, ?_⟩
  intro g m
  rw [h]
  show A.ρ g (eM m) = A.ρ ((θ.symm : H ≃* G) (θ g)) (eM m)
  congr 2
  exact (θ.symm_apply_apply g).symm

end PositivityTheory.Lit1.PTN
end
end

section

noncomputable section

open CategoryTheory MonoidalCategory TensorProduct GroundTheory.ProfCoh ReciprocityTheory.Gal

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem transfer_cup_degree_two_zero {Lv Hv : Type} [Group Lv] [TopologicalSpace Lv] [IsTopologicalGroup Lv]
    [Group Hv] [TopologicalSpace Hv] [IsTopologicalGroup Hv] (ev : Hv ≃* Lv)
    (hevc : Continuous ev.toMonoidHom) {R : Type} [CommRing R] {M M' P : Type}
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [DiscreteTopology M']
    [AddCommGroup P] [Module R P] [TopologicalSpace P] [DiscreteTopology P]
    (rho : Representation R Lv M) (rho' : Representation R Lv M') (rhoP : Representation R Lv P)
    (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y))
    (A B C : Rep.{0} (ULift.{0} ℤ) Hv) [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    (eA : M ≃+ A.V) (eB : M' ≃+ B.V)
    (heA : ∀ σ m, eA (rho (ev σ) m) = A.ρ σ (eA m))
    (heB : ∀ σ m, eB (rho' (ev σ) m) = B.ρ σ (eB m))
    (μ : A ⊗ B ⟶ C) (rel : P → C.V → Prop)
    (hbμ : ∀ x y, rel (b x y) (μ.hom (eA x ⊗ₜ[ULift.{0} ℤ] eB y)))
    (E : H2 rho ≃+ cohomology A 2)
    (hE : ∀ (z : ↥(Z2 rho)) (x : cocycles A 2),
      (∀ s, cochainOf A (cocycleι A 2 x) s = eA (z.1 (ev (s 0), ev (s 1)))) →
        E (Submodule.Quotient.mk z) = cohomologyπ A 2 x)
    (E' : ↥(H0 rho') ≃+ cohomology B 0)
    (hE' : ∀ (z : ↥(H0 rho')) (x : cocycles B 0),
      (∀ s, cochainOf B (cocycleι B 0 x) s = eB z.1) → E' z = cohomologyπ B 0 x)
    {Q : Type} [AddCommGroup Q] (jp : H2 rhoP →+ Q) (J : cohomology C 2 →+ Q)
    (hJ : ∀ (W : ↥(Z2 rhoP)) (x : cocycles C 2),
      (∀ s, rel (W.1 (ev (s 0), ev (s 1))) (cochainOf C (cocycleι C 2 x) s)) →
        jp (Submodule.Quotient.mk W) = - J (cohomologyπ C 2 x))
    (z : ↥(Z2 rho)) (m : ↥(H0 rho')) :
    jp (cupProductH2H0 rho rho' rhoP b hb hbe (Submodule.Quotient.mk z) m) =
      - J (cupPairing μ (rfl : 2 + 0 = 2) (E (Submodule.Quotient.mk z)) (E' m)) := by
  obtain ⟨e2, he2a, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 Hv R M (rho.comp ev.toMonoidHom) A eA heA
  obtain ⟨x2, hx2⟩ := he2a (restrictCocycles2 rho ev.toMonoidHom hevc z)
  have hm : ∀ σ, (rho'.comp ev.toMonoidHom) σ m.1 = m.1 := fun σ => (mem_riemannRochSpace_iff_regularAt_everywhere rho' m.1).1 m.2 (ev σ)
  obtain ⟨x0, hx0⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.exists_coc B 0 (fun _ => eB m.1) (IsLocallyConstant.const _)
    (by
      refine (PositivityTheory.LocalTateOrthogonality.Gcoh.d_comp (rho'.comp ev.toMonoidHom) B eB heB 0 fun _ => m.1).trans ?_
      funext s
      rw [PositivityTheory.LocalTateOrthogonality.Gcoh.dn_zero, hm (s 0), sub_self]
      exact map_zero eB)
  have hmB : ∀ σ, B.ρ σ (eB m.1) = eB m.1 := fun σ => by
    rw [← heB]
    exact congrArg eB (hm σ)
  have hEz : E (Submodule.Quotient.mk z) = cohomologyπ A 2 x2 := hE z x2 (fun s => hx2 s)
  have hEm : E' m = cohomologyπ B 0 x0 := hE' m x0 (fun s => congrFun hx0 s)
  rw [hEz, hEm, cupPairing_cohomologyπ]
  refine hJ (cupCocycleZ2H0 rho rho' rhoP b hb hbe z m) _ (fun s => ?_)
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles]
  rw [show (cochainOf _ (cocycleι _ 0 x0) fun j : Fin 0 => s ⟨2 + j, by omega⟩) = eB m.1 from
    congrFun hx0 _]
  rw [hmB]
  rw [show (cochainOf _ (cocycleι _ 2 x2) fun i : Fin 2 => s ⟨i, by omega⟩) =
    eA (z.1 (ev (s 0), ev (s 1))) from by rw [hx2]; rfl]
  exact hbμ _ _

end PositivityTheory.Lit1.PTN
end
end

section

noncomputable section

open CategoryTheory MonoidalCategory TensorProduct GroundTheory.ProfCoh ReciprocityTheory.Gal

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem transfer_cup_degree_zero_two {Lv Hv : Type} [Group Lv] [TopologicalSpace Lv] [IsTopologicalGroup Lv]
    [Group Hv] [TopologicalSpace Hv] [IsTopologicalGroup Hv] (ev : Hv ≃* Lv)
    (hevc : Continuous ev.toMonoidHom) {R : Type} [CommRing R] {M M' P : Type}
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [DiscreteTopology M']
    [AddCommGroup P] [Module R P] [TopologicalSpace P] [DiscreteTopology P]
    (rho : Representation R Lv M) (rho' : Representation R Lv M') (rhoP : Representation R Lv P)
    (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y))
    (A B C : Rep.{0} (ULift.{0} ℤ) Hv) [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    (eA : M ≃+ A.V) (eB : M' ≃+ B.V)
    (heA : ∀ σ m, eA (rho (ev σ) m) = A.ρ σ (eA m))
    (heB : ∀ σ m, eB (rho' (ev σ) m) = B.ρ σ (eB m))
    (μ : A ⊗ B ⟶ C) (rel : P → C.V → Prop)
    (hbμ : ∀ x y, rel (b x y) (μ.hom (eA x ⊗ₜ[ULift.{0} ℤ] eB y)))
    (E : ↥(H0 rho) ≃+ cohomology A 0)
    (hE : ∀ (z : ↥(H0 rho)) (x : cocycles A 0),
      (∀ s, cochainOf A (cocycleι A 0 x) s = eA z.1) → E z = cohomologyπ A 0 x)
    (E' : H2 rho' ≃+ cohomology B 2)
    (hE' : ∀ (z : ↥(Z2 rho')) (x : cocycles B 2),
      (∀ s, cochainOf B (cocycleι B 2 x) s = eB (z.1 (ev (s 0), ev (s 1)))) →
        E' (Submodule.Quotient.mk z) = cohomologyπ B 2 x)
    {Q : Type} [AddCommGroup Q] (jp : H2 rhoP →+ Q) (J : cohomology C 2 →+ Q)
    (hJ : ∀ (W : ↥(Z2 rhoP)) (x : cocycles C 2),
      (∀ s, rel (W.1 (ev (s 0), ev (s 1))) (cochainOf C (cocycleι C 2 x) s)) →
        jp (Submodule.Quotient.mk W) = - J (cohomologyπ C 2 x))
    (m : ↥(H0 rho)) (z : ↥(Z2 rho')) :
    jp (cupProductH0H2 rho rho' rhoP b hb hbe m (Submodule.Quotient.mk z)) =
      - J (cupPairing μ (rfl : 0 + 2 = 2) (E m) (E' (Submodule.Quotient.mk z))) := by
  obtain ⟨e2, he2a, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 Hv R M' (rho'.comp ev.toMonoidHom) B eB heB
  obtain ⟨x2, hx2⟩ := he2a (restrictCocycles2 rho' ev.toMonoidHom hevc z)
  have hm : ∀ σ, (rho.comp ev.toMonoidHom) σ m.1 = m.1 := fun σ => (mem_riemannRochSpace_iff_regularAt_everywhere rho m.1).1 m.2 (ev σ)
  obtain ⟨x0, hx0⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.exists_coc A 0 (fun _ => eA m.1) (IsLocallyConstant.const _)
    (by
      refine (PositivityTheory.LocalTateOrthogonality.Gcoh.d_comp (rho.comp ev.toMonoidHom) A eA heA 0 fun _ => m.1).trans ?_
      funext s
      rw [PositivityTheory.LocalTateOrthogonality.Gcoh.dn_zero, hm (s 0), sub_self]
      exact map_zero eA)
  have hEm : E m = cohomologyπ A 0 x0 := hE m x0 (fun s => congrFun hx0 s)
  have hEz : E' (Submodule.Quotient.mk z) = cohomologyπ B 2 x2 := hE' z x2 (fun s => hx2 s)
  rw [hEm, hEz, cupPairing_cohomologyπ]
  refine hJ (cupCocycleH0Z2 rho rho' rhoP b hb hbe m z) _ (fun s => ?_)
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles]
  have h0 : Fin.partialProd s ⟨0, by omega⟩ = 1 := Fin.partialProd_zero s
  rw [h0, map_one]
  rw [show (cochainOf _ (cocycleι _ 0 x0) fun i : Fin 0 => s ⟨i, by omega⟩) = eA m.1 from
    congrFun hx0 _]
  rw [show (cochainOf _ (cocycleι _ 2 x2) fun j : Fin 2 => s ⟨0 + j, by omega⟩) =
    eB (z.1 (ev (s 0), ev (s 1))) from by rw [hx2]; rfl]
  exact hbμ _ _

theorem hloc2 {G D L H : Type} [Group G] [Group D] [Group L] [Group H] {R M : Type} [CommRing R]
    [AddCommGroup M] [Module R M] (ρ : Representation R G M) (φ : D →* G) (ev : L ≃* D) (e : G → H)
    (A : Rep.{0} (ULift.{0} ℤ) H) (eM : M ≃+ A.V)
    (hM : ∀ g m, eM (ρ g m) = A.ρ (e g) (eM m)) (F : L →* H) (hev : ∀ σ, e (φ (ev σ)) = F σ) :
    ∀ σ m, eM ((ρ.comp φ) (ev σ) m) = (Rep.res F A).ρ σ (eM m) := by
  intro σ m
  rw [MonoidHom.comp_apply, hM, hev]
  rfl

end PositivityTheory.Lit1.PTN
end
end

section

noncomputable section

open CategoryTheory MonoidalCategory TensorProduct GroundTheory.ProfCoh ReciprocityTheory.Gal

namespace PositivityTheory.Lit1.PTN

theorem cupPairing_swap_degree_one {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {A B C : Rep.{0} (ULift.{0} ℤ) Γ} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    (μ : A ⊗ B ⟶ C) (x : cohomology A 1) (y : cohomology B 1) :
    cupPairing μ (rfl : 1 + 1 = 2) x y = - cupPairing ((β_ B A).hom ≫ μ) (rfl : 1 + 1 = 2) y x := by
  rw [cupPairing_apply, cupPairing_apply, cohomologyMap_comp, ConcreteCategory.comp_apply,
    cohomologyMap_braiding_cup (rfl : 1 + 1 = 2) (rfl : 1 + 1 = 2) y x]
  have h1 : ((-1 : ULift.{0} ℤ) ^ (1 * 1)) = -1 := by simp
  rw [h1, neg_one_smul, map_neg, neg_neg]

attribute [local instance 2000] Rep.hV2

theorem transfer_cup_degree_one_one {Lv Hv : Type} [Group Lv] [TopologicalSpace Lv] [IsTopologicalGroup Lv]
    [Group Hv] [TopologicalSpace Hv] [IsTopologicalGroup Hv] (ev : Hv ≃* Lv)
    (hevc : Continuous ev.toMonoidHom) {R : Type} [CommRing R] {M M' P : Type}
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [DiscreteTopology M']
    [AddCommGroup P] [Module R P] [TopologicalSpace P] [DiscreteTopology P]
    (rho : Representation R Lv M) (rho' : Representation R Lv M') (rhoP : Representation R Lv P)
    (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y)) (hc : ContAction rho')
    (A B C : Rep.{0} (ULift.{0} ℤ) Hv) [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    (eA : M ≃+ A.V) (eB : M' ≃+ B.V)
    (heA : ∀ σ m, eA (rho (ev σ) m) = A.ρ σ (eA m))
    (heB : ∀ σ m, eB (rho' (ev σ) m) = B.ρ σ (eB m))
    (μ : A ⊗ B ⟶ C) (rel : P → C.V → Prop)
    (hbμ : ∀ x y, rel (b x y) (μ.hom (eA x ⊗ₜ[ULift.{0} ℤ] eB y)))
    (E : H1 rho ≃+ cohomology A 1)
    (hE : ∀ (z : ↥(Z1 rho)) (x : cocycles A 1),
      (∀ s, cochainOf A (cocycleι A 1 x) s = eA (z.1 (ev (s 0)))) →
        E (Submodule.Quotient.mk z) = cohomologyπ A 1 x)
    (E' : H1 rho' ≃+ cohomology B 1)
    (hE' : ∀ (z : ↥(Z1 rho')) (x : cocycles B 1),
      (∀ s, cochainOf B (cocycleι B 1 x) s = eB (z.1 (ev (s 0)))) →
        E' (Submodule.Quotient.mk z) = cohomologyπ B 1 x)
    {Q : Type} [AddCommGroup Q] (jp : H2 rhoP →+ Q) (J : cohomology C 2 →+ Q)
    (hJ : ∀ (W : ↥(Z2 rhoP)) (x : cocycles C 2),
      (∀ s, rel (W.1 (ev (s 0), ev (s 1))) (cochainOf C (cocycleι C 2 x) s)) →
        jp (Submodule.Quotient.mk W) = - J (cohomologyπ C 2 x))
    (z : ↥(Z1 rho)) (z' : ↥(Z1 rho')) :
    jp (cupProductH1H1 rho rho' rhoP b hb hbe hc (Submodule.Quotient.mk z) (Submodule.Quotient.mk z')) =
      - J (cupPairing μ (rfl : 1 + 1 = 2) (E (Submodule.Quotient.mk z)) (E' (Submodule.Quotient.mk z'))) := by
  obtain ⟨e1, he1a, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 Hv R M (rho.comp ev.toMonoidHom) A eA heA
  obtain ⟨x, hx⟩ := he1a (restrictCocycles1 rho ev.toMonoidHom hevc z)
  obtain ⟨e1', he1b, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 Hv R M' (rho'.comp ev.toMonoidHom) B eB heB
  obtain ⟨x', hx'⟩ := he1b (restrictCocycles1 rho' ev.toMonoidHom hevc z')
  have hEa : E (Submodule.Quotient.mk z) = cohomologyπ A 1 x := hE z x (fun s => hx s)
  have hEb : E' (Submodule.Quotient.mk z') = cohomologyπ B 1 x' := hE' z' x' (fun s => hx' s)
  have hcup : cupProductH1H1 rho rho' rhoP b hb hbe hc (Submodule.Quotient.mk z) (Submodule.Quotient.mk z') =
      Submodule.Quotient.mk (cupCocycleZ1Z1 rho rho' rhoP b hb hbe hc z z') := rfl
  rw [hEa, hEb, cupPairing_cohomologyπ, hcup]
  refine hJ _ _ (fun s => ?_)
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles, hx, hx']
  have h1 : Fin.partialProd s ⟨1, by omega⟩ = s 0 := by
    show Fin.partialProd s (Fin.succ 0) = s 0
    rw [Fin.partialProd_succ]
    show Fin.partialProd s 0 * s 0 = s 0
    rw [Fin.partialProd_zero, one_mul]
  rw [h1]
  have := hbμ (z.1 (ev (s 0))) (rho' (ev (s 0)) (z'.1 (ev (s 1))))
  rw [heB] at this
  exact this

theorem transfer_cup_one_one_general {Lv Hv : Type} [Group Lv] [TopologicalSpace Lv] [IsTopologicalGroup Lv]
    [Group Hv] [TopologicalSpace Hv] [IsTopologicalGroup Hv] [CompactSpace Hv]
    [TotallyDisconnectedSpace Hv] (ev : Hv ≃* Lv)
    (hevc : Continuous ev.toMonoidHom) {R : Type} [CommRing R] {M M' P : Type}
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [DiscreteTopology M']
    [AddCommGroup P] [Module R P] [TopologicalSpace P] [DiscreteTopology P]
    (rho : Representation R Lv M) (rho' : Representation R Lv M') (rhoP : Representation R Lv P)
    (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y)) (hc : ContAction rho')
    (A B C : Rep.{0} (ULift.{0} ℤ) Hv) [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    (eA : M ≃+ A.V) (eB : M' ≃+ B.V)
    (heA : ∀ σ m, eA (rho (ev σ) m) = A.ρ σ (eA m))
    (heB : ∀ σ m, eB (rho' (ev σ) m) = B.ρ σ (eB m))
    (μ' : B ⊗ A ⟶ C) (rel : P → C.V → Prop)
    (hbμ : ∀ y x, rel (b x y) (μ'.hom (eB y ⊗ₜ[ULift.{0} ℤ] eA x)))
    (E : H1 rho ≃+ cohomology A 1)
    (hE : ∀ (z : ↥(Z1 rho)) (x : cocycles A 1),
      (∀ s, cochainOf A (cocycleι A 1 x) s = eA (z.1 (ev (s 0)))) →
        E (Submodule.Quotient.mk z) = cohomologyπ A 1 x)
    (E' : H1 rho' ≃+ cohomology B 1)
    (hE' : ∀ (z : ↥(Z1 rho')) (x : cocycles B 1),
      (∀ s, cochainOf B (cocycleι B 1 x) s = eB (z.1 (ev (s 0)))) →
        E' (Submodule.Quotient.mk z) = cohomologyπ B 1 x)
    {Q : Type} [AddCommGroup Q] (jp : H2 rhoP →+ Q) (J : cohomology C 2 →+ Q)
    (hJ : ∀ (W : ↥(Z2 rhoP)) (x : cocycles C 2),
      (∀ s, rel (W.1 (ev (s 0), ev (s 1))) (cochainOf C (cocycleι C 2 x) s)) →
        jp (Submodule.Quotient.mk W) = - J (cohomologyπ C 2 x))
    (a : H1 rho') (b' : H1 rho) :
    jp (cupProductH1H1 rho rho' rhoP b hb hbe hc b' a) = J (cupPairing μ' (rfl : 1 + 1 = 2) (E' a) (E b')) := by
  induction a using Submodule.Quotient.induction_on with
  | H z' => ?_
  induction b' using Submodule.Quotient.induction_on with
  | H z => ?_
  have hbμ' : ∀ x y, rel (b x y) (((β_ A B).hom ≫ μ').hom (eA x ⊗ₜ[ULift.{0} ℤ] eB y)) :=
    fun x y => hbμ y x
  rw [cupPairing_swap_degree_one μ', map_neg,
    transfer_cup_degree_one_one ev hevc rho rho' rhoP b hb hbe hc A B C eA eB heA heB ((β_ A B).hom ≫ μ') rel hbμ'
      E hE E' hE' jp J hJ z z']

end PositivityTheory.Lit1.PTN
end
end

section

noncomputable section

open CategoryTheory GroundTheory.ProfCoh

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem bidualCmp {G : Type} [Group G] (D A : Rep.{0} (ULift.{0} ℤ) G) (N : ℕ) [NeZero N]
    (hD : Nonempty (D ≃+ ZMod N)) [Finite A] (hA : ∀ m : A, N • m = 0) :
    ∃ eB : A.V ≃+ (dualRep D (dualRep D A)).V,
      ∀ g a, eB (A.ρ g a) = (dualRep D (dualRep D A)).ρ g (eB a) := by
  have hb := bijective_toDualDual (D := D) (M := A) hD hA
  let f : A.V →+ (dualRep D (dualRep D A)).V :=
    { toFun := (toDualDual D A).hom, map_zero' := map_zero _, map_add' := map_add _ }
  refine ⟨AddEquiv.ofBijective f hb, fun g a => ?_⟩
  exact Rep.hom_comm_apply (toDualDual D A) g a

end PositivityTheory.Lit1.PTN
end
end
