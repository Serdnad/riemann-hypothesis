module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle052
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Matrix.PEquiv
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Bundle001
public import Mathlib.Basic.PEquiv
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem exists_zpow_eq_ringEquiv_on_roots_of_unity {K : Type*} [Field K] (M : ℕ) (hM : 1 ≤ M) (σ : K ≃+* K) :
    ∃ m : ℤ, ∀ x : K, x ^ M = 1 → σ x = x ^ m := by
  haveI : NeZero M := ⟨by omega⟩
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic ((σ.toMulEquiv.restrictRootsOfUnity M).toMonoidHom)
  refine ⟨m, fun x hx => ?_⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp [zero_pow (by omega : M ≠ 0)] at hx
  let g : rootsOfUnity M K := ⟨Units.mk0 x hx0, by rw [mem_rootsOfUnity]; ext; simp [hx]⟩
  have := congrArg (fun y : rootsOfUnity M K => ((y : Kˣ) : K)) (hm g)
  simpa [g] using this

private theorem commutator_fixes_root_of_unity {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] (M : ℕ) (hM : 1 ≤ M)
    (σ τ : Ω ≃ₐ[F] Ω) (ζ : Ω) (hζ : ζ ^ M = 1) : (σ * τ * σ⁻¹ * τ⁻¹) ζ = ζ := by
  obtain ⟨a, ha⟩ := exists_zpow_eq_ringEquiv_on_roots_of_unity M hM σ.toRingEquiv
  obtain ⟨b, hb⟩ := exists_zpow_eq_ringEquiv_on_roots_of_unity M hM τ.toRingEquiv
  have ha' : ∀ x : Ω, x ^ M = 1 → σ x = x ^ a := ha
  have hb' : ∀ x : Ω, x ^ M = 1 → τ x = x ^ b := hb
  have hμ : ∀ (ρ : Ω ≃ₐ[F] Ω) (x : Ω), x ^ M = 1 → (ρ x) ^ M = 1 := fun ρ x hx => by
    rw [← map_pow, hx, map_one]
  have hz : (σ⁻¹ (τ⁻¹ ζ)) ^ M = 1 := hμ _ _ (hμ _ _ hζ)
  have key : σ (τ (σ⁻¹ (τ⁻¹ ζ))) = τ (σ (σ⁻¹ (τ⁻¹ ζ))) := by
    rw [ha' _ (hμ τ _ hz), hb' _ hz, hb' _ (hμ σ _ hz), ha' _ hz, ← zpow_mul, ← zpow_mul, mul_comm]
  simp only [AlgEquiv.mul_apply]
  rw [key]
  simp

theorem UpperTheory.irreducible_weilDeligne_tame_level_eq_character :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (M : ℕ), 1 ≤ M →
    ∀ (m : ℕ) (b : WDRep h (Fin m → ℂ)), b.ρ.IsIrreducible →
    (∀ s : ↥(Ine (F := F) A), (∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ) → b.ρ (ineIncl h s) = 1) →
    ∃ (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ), WD.mk b = WD.lpOfChar h ξ hξ ∧ ∀ σ, b.ρ σ = 1 → ξ σ = 1 := by
  intro F Ω _ _ _ _ _ w A h M hM m b hirr hine
  haveI := hirr
  have hcomm : ∀ σ τ : Weil h, b.ρ σ * b.ρ τ = b.ρ τ * b.ρ σ := by
    intro σ τ
    have hdeg : deg (σ * τ * σ⁻¹ * τ⁻¹) = 0 := by
      simp only [deg_mul, deg_inv]
      ring
    have hc : ((σ * τ * σ⁻¹ * τ⁻¹ : Weil h) : G F Ω) ∈ Ine A := deg_eq_zero_iff.1 hdeg
    have hρc : b.ρ (σ * τ * σ⁻¹ * τ⁻¹) = 1 := by
      have e : ineIncl h ⟨_, hc⟩ = σ * τ * σ⁻¹ * τ⁻¹ := rfl
      rw [← e]
      apply hine
      intro ζ hζ
      show ((σ * τ * σ⁻¹ * τ⁻¹ : Weil h) : G F Ω) ζ = ζ
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using commutator_fixes_root_of_unity M hM (σ : G F Ω) τ ζ hζ
    have hst : σ * τ = (σ * τ * σ⁻¹ * τ⁻¹) * (τ * σ) := by group
    rw [← map_mul, hst, map_mul, hρc, one_mul, map_mul]
  have hnt : Nontrivial (Fin m → ℂ) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact (bot_ne_top : (⊥ : Subrepresentation b.ρ) ≠ ⊤) (Subrepresentation.ext (Subsingleton.elim _ _))
  have hscal : ∀ τ : Weil h, ∃ c : ℂ, ∀ v, b.ρ τ v = c • v := by
    intro τ
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (b.ρ τ)
    refine ⟨c, ?_⟩
    let S : Subrepresentation b.ρ := ⟨Module.End.eigenspace (b.ρ τ) c, fun g v hv => by
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      have := congrArg (fun f => f v) (hcomm τ g)
      simp only [Module.End.mul_apply] at this
      rw [this, hv, map_smul]⟩
    rcases eq_bot_or_eq_top S with hS | hS
    · exfalso
      obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
      have hvS : v ∈ S.toSubmodule := hv.1
      rw [hS] at hvS
      exact hv.2 ((Submodule.mem_bot ℂ).1 hvS)
    · intro v
      have hvS : v ∈ S.toSubmodule := by
        rw [hS]
        exact Submodule.mem_top
      exact Module.End.mem_eigenspace_iff.1 hvS
  obtain ⟨v0, hv0⟩ := exists_ne (0 : Fin m → ℂ)
  have hspan : Submodule.span ℂ {v0} = ⊤ := by
    let S : Subrepresentation b.ρ := ⟨Submodule.span ℂ {v0}, fun g v hv => by
      obtain ⟨c, hc⟩ := hscal g
      rw [hc]
      exact Submodule.smul_mem _ _ hv⟩
    rcases eq_bot_or_eq_top S with hS | hS
    · exfalso
      have hvS : v0 ∈ S.toSubmodule := Submodule.subset_span rfl
      rw [hS] at hvS
      exact hv0 ((Submodule.mem_bot ℂ).1 hvS)
    · exact congrArg Subrepresentation.toSubmodule hS
  have hm1 : m = 1 := by
    have h1 := finrank_span_singleton (K := ℂ) hv0
    rw [hspan, finrank_top, Module.finrank_fin_fun] at h1
    exact h1
  subst hm1
  let v1 : Fin 1 → ℂ := fun _ => 1
  have hEnd : ∀ (f : Module.End ℂ (Fin 1 → ℂ)) (v : Fin 1 → ℂ), f v = f v1 0 • v := by
    intro f v
    have hv : v = v 0 • v1 := by
      funext i
      fin_cases i
      simp [v1]
    rw [hv, map_smul]
    funext i
    fin_cases i
    simp [v1, mul_comm]
  have hne : ∀ σ : Weil h, b.ρ σ v1 0 ≠ 0 := by
    intro σ h0
    have hinv : b.ρ σ⁻¹ (b.ρ σ v1) = v1 := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [hEnd (b.ρ σ) v1, h0, zero_smul, map_zero] at hinv
    have := congrFun hinv 0
    simp [v1] at this
  let ξ : Weil h →* ℂˣ :=
    { toFun := fun σ => Units.mk0 _ (hne σ)
      map_one' := by
        ext
        simp [v1]
      map_mul' := by
        intro σ τ
        ext
        simp only [Units.val_mk0, Units.val_mul, map_mul, Module.End.mul_apply]
        rw [hEnd (b.ρ σ) (b.ρ τ v1)]
        simp }
  have hξ1 : ∀ σ, ξ σ = 1 ↔ b.ρ σ = 1 := by
    intro σ
    constructor
    · intro hσ
      have h1 : b.ρ σ v1 0 = 1 := by simpa [ξ] using congrArg Units.val hσ
      apply LinearMap.ext
      intro v
      rw [hEnd, h1, one_smul]
      rfl
    · intro hσ
      ext
      simp [ξ, hσ, v1]
  have hsm : IsSmooth ξ := by
    simpa only [IsSmooth, hξ1] using b.smooth
  have hN : b.N = 0 := by
    obtain ⟨k, hk⟩ := b.nilpotent
    set c := b.N v1 0 with hc
    have hNv : b.N v1 = c • v1 := hEnd b.N v1
    have hp : ∀ n : ℕ, (b.N ^ n) v1 = c ^ n • v1 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hNv, smul_smul, pow_succ]
    have hck : c ^ k = 0 := by
      have := congrFun (hp k) 0
      rw [hk] at this
      simpa [v1] using this.symm
    have hc0 : c = 0 := pow_eq_zero_iff'.1 hck |>.1
    apply LinearMap.ext
    intro v
    rw [hEnd, ← hc, hc0, zero_smul]
    rfl
  refine ⟨ξ, hsm, ?_, fun σ hσ => (hξ1 σ).2 hσ⟩
  unfold WD.lpOfChar
  apply WD.sound
  refine ⟨LinearEquiv.refl ℂ _, fun σ v => ?_, fun v => ?_⟩
  · funext i
    fin_cases i
    rw [LinearEquiv.refl_apply, LinearEquiv.refl_apply, hEnd (b.ρ σ) v]
    simp [WDRep.ofChars, diagEnd, ξ]
  · simp [hN, WDRep.ofChars]
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem UpperTheory.jacquet_borel_nontrivial_of_blocks_le_one :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (r : ℕ) (d : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin N), (∀ a, d a ≤ 1) → Nontrivial (Jacquet π (unipRad k e)) →
    Nontrivial (Jacquet π (unipB k (Fin N))) := by
  intro k _ _ _ _ N V _ _ π r d e hd hR
  have hinj : Function.Injective (blk e) := by
    intro i j hij
    apply e.symm.injective
    simp only [GlobalTheory.SmGL.blk] at hij
    revert hij
    generalize e.symm i = p
    generalize e.symm j = q
    intro hij
    obtain ⟨a, x⟩ := p
    obtain ⟨b, y⟩ := q
    simp only at hij
    subst hij
    have hxy : x = y := by
      have h1 := x.isLt
      have h2 := y.isLt
      have h3 := hd a
      ext
      omega
    rw [hxy]
  set S : Finset (Fin r) := Finset.univ.image (blk e) with hSdef
  have hS : S.card = N := by
    rw [hSdef, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  let f : Fin N → Fin N := fun i =>
    (S.orderIsoOfFin hS).symm ⟨blk e i, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have hflt : ∀ i j, blk e i < blk e j → f i < f j := by
    intro i j h
    simp only [f, OrderIso.lt_iff_lt]
    exact h
  have hfinj : Function.Injective f := by
    intro i j h
    apply hinj
    have := (S.orderIsoOfFin hS).symm.injective h
    simpa using this
  let σ : Fin N ≃ Fin N := Equiv.ofBijective f ⟨hfinj, Finite.injective_iff_surjective.mp hfinj⟩
  have hσ : ∀ i j, blk e i < blk e j → σ i < σ j := hflt
  have h1 : σ.toPEquiv.toMatrix * σ.symm.toPEquiv.toMatrix = (1 : Matrix (Fin N) (Fin N) k) := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]
  have h2 : σ.symm.toPEquiv.toMatrix * σ.toPEquiv.toMatrix = (1 : Matrix (Fin N) (Fin N) k) := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]
  let hh : GL (Fin N) k := ⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix, h1, h2⟩
  have hent : ∀ (g : GL (Fin N) k) (i j : Fin N),
      ((hh * g * hh⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = (g : Matrix (Fin N) (Fin N) k) (σ i) (σ j) := by
    intro g i j
    have hv : ((hh * g * hh⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)
        = σ.toPEquiv.toMatrix * (g : Matrix (Fin N) (Fin N) k) * σ.symm.toPEquiv.toMatrix := rfl
    rw [hv, PEquiv.mul_toMatrix_apply, ← Equiv.toPEquiv_symm, Equiv.symm_symm, Equiv.toPEquiv_apply]
    simp only [Matrix.mul_assoc]
    rw [PEquiv.toMatrix_mul_apply, Equiv.toPEquiv_apply]
  have memR : ∀ n : unipB k (Fin N), hh * (n : GL (Fin N) k) * hh⁻¹ ∈ unipRad k e := by
    intro n
    have hn := (mem_unipB k).mp n.2
    rw [mem_unipRad, mem_parab]
    refine ⟨?_, ?_⟩
    · intro i j hij
      rw [hent]
      exact hn.1 _ _ (hσ _ _ hij)
    · intro a x y
      have hxy : x = y := by
        have h1 := x.isLt
        have h2 := y.isLt
        have h3 := hd a
        ext
        omega
      subst hxy
      rw [hent, hn.2, Matrix.one_apply_eq]
  rw [← not_subsingleton_iff_nontrivial] at hR ⊢
  intro hB
  apply hR
  change Subsingleton (V ⧸ GlobalTheory.PRep.twKer π _ 1) at hB
  change Subsingleton (V ⧸ GlobalTheory.PRep.twKer π _ 1)
  rw [Submodule.Quotient.subsingleton_iff] at hB ⊢
  have key : GlobalTheory.PRep.twKer π (unipB k (Fin N)) 1 ≤
      (GlobalTheory.PRep.twKer π (unipRad k e) 1).comap (π hh) := by
    unfold GlobalTheory.PRep.twKer
    rw [Submodule.span_le]
    rintro w ⟨n, v, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, MonoidHom.one_apply, Units.val_one, one_smul, map_sub]
    apply Submodule.subset_span
    refine ⟨⟨hh * (n : GL (Fin N) k) * hh⁻¹, memR n⟩, π hh v, ?_⟩
    simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_mul, Module.End.mul_apply]
    rw [← Module.End.mul_apply (π hh⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [eq_top_iff]
  intro v _
  have hv : v = π hh (π hh⁻¹ v) := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [hv]
  exact key (hB ▸ Submodule.mem_top)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem UpperTheory.fixed_ne_bot_of_isSubquotient_of_isCompact :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ G V) (π : Representation ℂ G W) (H : Subgroup G), IsSmooth π → IsSubquotient σ π → IsCompact (H : Set G) →
    fixed σ H ≠ ⊥ → fixed π H ≠ ⊥ := by
  intro G _ _ _ V W _ _ _ _ σ π H hπ hsq hH hne
  obtain ⟨S, f, hf⟩ := hsq
  have hS : IsSmooth S.toRepresentation := fun v => by
    have : {g : G | S.toRepresentation g v = v} = {g : G | π g v = v} := by
      ext g; exact Subtype.ext_iff
    rw [this]; exact hπ v
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hne
  obtain ⟨u, rfl⟩ := hf x
  obtain ⟨v, hv, e⟩ := IwahoriOnto.exists_fixed_map_eq hS hH f.toLinearMap u fun h hh => by
    show f (S.toRepresentation h u) = f u
    rw [f.isIntertwining]
    simpa using hx ⟨h, hh⟩
  refine (Submodule.ne_bot_iff _).2 ⟨v.1, fun h => ?_, fun h0 => hx0 ?_⟩
  · exact congrArg Subtype.val (hv h)
  · have hv0 : v = 0 := Subtype.ext h0
    have e' : f.toLinearMap v = f u := e
    rw [← e', hv0, map_zero]
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem norm_lt_one_of_valuation_lt {F : Type} [Field F] [NumberField F] {w : HeightOneSpectrum (𝓞 F)} {p : ℕ} [Fact p.Prime]
    (j : w.adicCompletion F →+* Qbar p) (hj : Continuous j) (y : w.adicCompletion F) (hy : Valued.v y < 1) :
    ‖j y‖ < 1 := by
  have h2 := Valued.tendsto_zero_pow_of_v_lt_one hy
  have h3 := (hj.tendsto 0).comp h2
  rw [map_zero] at h3
  rw [← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
  refine h3.congr (fun n => ?_)
  simp

private theorem norm_le_one_of_valuation_le {F : Type} [Field F] [NumberField F] {w : HeightOneSpectrum (𝓞 F)} {p : ℕ} [Fact p.Prime]
    (j : w.adicCompletion F →+* Qbar p) (hj : Continuous j) (y : w.adicCompletion F) (hy : Valued.v y ≤ 1) :
    ‖j y‖ ≤ 1 := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  set t := algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F a) with ht
  have h1 : Valued.v t < 1 := by
    have : Valued.v t = w.valuation F (algebraMap (𝓞 F) F a) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    rw [this]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem w a).2 ha
  have ht0 : t ≠ 0 := by
    rw [ht, map_ne_zero]
    exact fun h => ha0 (by simpa using h)
  have hpos : 0 < ‖j t‖ := norm_pos_iff.mpr ((map_ne_zero j).mpr ht0)
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖j t‖⁻¹) hlt
  have h4 : Valued.v (t * y ^ n) < 1 := by
    rw [map_mul, map_pow]
    calc Valued.v t * Valued.v y ^ n ≤ Valued.v t * 1 := by
          gcongr
          exact pow_le_one' hy n
      _ < 1 := by rwa [mul_one]
  have h5 := norm_lt_one_of_valuation_lt j hj _ h4
  rw [map_mul, map_pow, norm_mul, norm_pow] at h5
  rw [inv_lt_iff_one_lt_mul₀' hpos] at hn
  exact absurd (hn.trans h5) (lt_irrefl _)

theorem UpperTheory.norm_locPow_sub_one_le_of_valuation_sub_one_le :
    ∀ (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (M : ℕ)
    (u : w.adicCompletion F), valuation (w.adicCompletion F) (u - 1) ≤ valuation (w.adicCompletion F) (M : w.adicCompletion F) →
    ‖GlobalTheory.HeckeGal.locPow ι (fun _ => 1) w u - 1‖ ≤ ‖(M : Qbar p)‖ := by
  intro F _ _ w p _ ι M u h
  have hv : Valued.v (u - 1) ≤ Valued.v (M : w.adicCompletion F) :=
    ((Valuation.Compatible.vle_iff_le (v := valuation (w.adicCompletion F)) _ _).mpr h :)
  have hM1 : ‖(M : Qbar p)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ M
  have key : ∀ j : w.adicCompletion F →+* Qbar p, Continuous j → ‖j u - 1‖ ≤ ‖(M : Qbar p)‖ := by
    intro j hj
    by_cases hM : (M : w.adicCompletion F) = 0
    · rw [hM, map_zero, le_zero_iff, map_eq_zero, sub_eq_zero] at hv
      simp [hv]
    · have hx : Valued.v ((u - 1) / (M : w.adicCompletion F)) ≤ 1 := by
        rw [map_div₀]
        exact div_le_one_of_le₀ hv zero_le
      have h1 := norm_le_one_of_valuation_le j hj _ hx
      have hM' : (M : Qbar p) ≠ 0 := by
        rw [← map_natCast j]
        exact (map_ne_zero j).mpr hM
      rw [map_div₀, map_sub, map_one, map_natCast, norm_div, div_le_one (norm_pos_iff.mpr hM')] at h1
      exact h1
  unfold GlobalTheory.HeckeGal.locPow
  refine finprod_induction (fun z : Qbar p => ‖z - 1‖ ≤ ‖(M : Qbar p)‖) (by simp) ?_ ?_
  · intro x y hx hy
    have hx1 : ‖x‖ ≤ 1 := by
      have := IsUltrametricDist.norm_add_le_max (x - 1) 1
      rw [sub_add_cancel, norm_one] at this
      exact this.trans (max_le (hx.trans hM1) le_rfl)
    have e : x * y - 1 = x * (y - 1) + (x - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hx)
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hx1).trans hy
  · intro j
    rw [zpow_one]
    exact key j.1 j.2
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

private theorem inv_int {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] [LinearOrder n] {c : GL n k}
    (hc : c ∈ GlobalTheory.SmGL.IwahoriOnto.lowerInt k n) (i j : n) : valuation k ((c⁻¹).val i j) ≤ 1 := by
  let M : Matrix n n 𝒪[k] := Matrix.of fun i j => ⟨c.val i j, hc.1 i j⟩
  have hdet : c.val.det = 1 := by
    rw [Matrix.det_of_lowerTriangular c.val fun i j hij => hc.2.1 i j hij]
    simp [hc.2.2]
  have hM : (algebraMap 𝒪[k] k).mapMatrix M = c.val := by ext i j; rfl
  have e : (c⁻¹).val = (algebraMap 𝒪[k] k).mapMatrix M.adjugate := by
    rw [RingHom.map_adjugate, hM, Matrix.coe_units_inv, Matrix.inv_def, hdet]
    simp
  rw [e]
  exact (M.adjugate i j).2

theorem UpperTheory.congruence_subgroup_eq_diagonal_unipotent_lower_iwahori :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1),
    ∀ g ∈ GlobalTheory.CentralExponent.cong (Fin N) γ hγ, ∃ d : Fin N → kˣ, (∀ i, valuation k ((d i : k) - 1) < γ) ∧
      ∃ x ∈ unipB k (Fin N), ∃ c ∈ GlobalTheory.SmGL.IwahoriOnto.lowerInt k (Fin N), g = diagT k (Fin N) d * x * c := by
  intro k _ _ _ _ N γ hγ g hg
  have hg' : ∀ i j, valuation k ((g.val - 1) i j) < γ := hg
  have h1 : g ∈ KOne k (Fin N) := GlobalTheory.StepData.mem_KOne.2 fun i j => (hg' i j).trans_le hγ
  have hI : g ∈ iwahori k (Fin N) := by
    refine mem_iwahori.2 ⟨GlobalTheory.StepData.KOne_le_KO h1, fun i j hij => ?_⟩
    have := (hg' i j).trans_le (show ((γ : ValueGroupWithZero k)) ≤ 1 from hγ)
    rwa [Matrix.sub_apply, Matrix.one_apply_ne hij.ne', sub_zero] at this
  obtain ⟨d, -, x, hx, c, hc, e⟩ := GlobalTheory.SmGL.IwahoriOnto.iwahori_factor k (Fin N) g hI
  refine ⟨d, fun i => ?_, x, hx, c, hc, e⟩
  have hcl : c ∈ unipBLower k (Fin N) :=
    (mem_unipB (n := (Fin N)ᵒᵈ) k).2 ⟨fun i j hij => hc.2.1 i j hij, hc.2.2⟩
  have hci : (c⁻¹).val i i = 1 := ((mem_unipB (n := (Fin N)ᵒᵈ) k).1 (inv_mem hcl)).2 i
  have h2 : (g * c⁻¹).val i i = d i := by
    rw [e, mul_inv_cancel_right, Units.val_mul, val_diagT, Matrix.diagonal_mul, ((mem_unipB k).1 hx).2 i, mul_one]
  have h3 : ((g.val - 1) * (c⁻¹).val) i i = (d i : k) - 1 := by
    rw [sub_mul, one_mul, Matrix.sub_apply, hci, ← Units.val_mul, h2]
  rw [← h3, Matrix.mul_apply]
  refine Valuation.map_sum_lt _ γ.ne_zero fun s _ => ?_
  rw [map_mul]
  exact (mul_le_of_le_one_right' (inv_int hc s i)).trans_lt (hg' i s)
end
