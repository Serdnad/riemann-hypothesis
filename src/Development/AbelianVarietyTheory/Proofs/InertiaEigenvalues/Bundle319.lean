module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle173
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta
import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeSpaceProjectionToPointEigenspaces
public import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalisedGlobalCocyclesInLocalSpan
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle290
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle292
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle293
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle294
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.Divisibility.Bundle001
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide

@[expose] public section

section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

noncomputable section

namespace GlobalTheory.LatSplit

theorem form_gen_span {L V M ι : Type} [Field L] [AddCommGroup V] [Module L V] [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] {σ : L →+* ℂ} (j : V →ₛₗ[σ] M) (b : Module.Basis ι L V)
    (hb : LinearIndependent ℂ (fun i => j (b i)) ∧ Submodule.span ℂ (Set.range fun i => j (b i)) = ⊤)
    (T : Finset M) (hT : Submodule.span ℂ (T : Set M) = ⊤) (hsub : ∀ x ∈ T, x ∈ Set.range j) :
    {x | j x ∈ T}.Finite ∧ Submodule.span L {x | j x ∈ T} = ⊤ := by
  haveI : Finite ι := hb.1.finite
  haveI := Fintype.ofFinite ι
  let B : Module.Basis ι ℂ M := Module.Basis.mk hb.1 hb.2.ge
  have hB : ∀ i, B i = j (b i) := fun i => by simp [B]
  have key : ∀ l : V →ₗ[L] L, ∃ l' : M →ₗ[ℂ] ℂ, ∀ x, l' (j x) = σ (l x) := fun l => by
    refine ⟨B.constr ℂ fun i => σ (l (b i)), fun x => ?_⟩
    conv_lhs => rw [← b.sum_repr x]
    conv_rhs => rw [← b.sum_repr x]

    simp only [map_sum, LinearMap.map_smulₛₗ, ← hB, Module.Basis.constr_basis, smul_eq_mul, map_mul, RingHom.id_apply]
  have hinj : Function.Injective j := fun x y hxy => by
    refine b.ext_elem fun i => σ.injective ?_
    obtain ⟨l', hl'⟩ := key (b.coord i)
    have h1 := hl' x
    rw [hxy, hl' y] at h1
    exact h1.symm
  refine ⟨T.finite_toSet.preimage hinj.injOn, ?_⟩
  by_contra hne
  obtain ⟨l, hl0, hl⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  obtain ⟨l', hl'⟩ := key l
  have h1 : l' = 0 := by
    rw [← LinearMap.ker_eq_top, eq_top_iff, ← hT, Submodule.span_le]
    intro y hy
    obtain ⟨x, rfl⟩ := hsub y hy
    have hx : l x = 0 := hl (Submodule.subset_span hy)
    show l' (j x) = 0
    rw [hl', hx, map_zero]
  refine hl0 (LinearMap.ext fun x => σ.injective ?_)
  rw [← hl', h1]
  simp

variable {D : D7} {M : MtFam D}

theorem genSet_props (j : ℕ) (w : D.what₂.places.Pl) :
    (genSet D (D.what₂.muTw w) j).Finite ∧ Submodule.span D.what₂.LL (genSet D (D.what₂.muTw w) j) = ⊤ :=
  form_gen_span (D.what₂.jMt _ j) (Module.Free.chooseBasis _ _) (D.what₂.jMt_basis _ j _) _
    (D.what₂.MtLat _ j).span_top (D.what₂.MtLat_sub _ j)

theorem latLoc_fg (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) : (latLoc B j w).FG :=
  Submodule.fg_span ((genSet_props (D := D) j w).1.image _)

theorem latLoc_span (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) :
    Submodule.span (FractionRing (B.Oc j w)) (latLoc B j w : Set (B.V j w)) = ⊤ := by
  rw [latLoc, Submodule.span_span_of_tower]
  have hG := (genSet_props (D := D) j w).2
  have key : ∀ x ∈ Submodule.span D.what₂.LL (genSet D (D.what₂.muTw w) j),
      B.iV j w x ∈ Submodule.span (FractionRing (B.Oc j w)) (B.iV j w '' genSet D (D.what₂.muTw w) j) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hy
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)
  rw [eq_top_iff, ← (B.iV_basis j w b).2, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact key _ (hG ▸ Submodule.mem_top)

theorem alg_stable (B : NLocBase D M) {j : ℕ} {w : D.what₂.places.Pl} (hl : LatStable B j w) :
    ∀ t ∈ heckeAlg B j w, ∀ x ∈ latLoc B j w, t x ∈ latLoc B j w := by
  intro t ht
  induction ht using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨v, k, hvk, rfl⟩ := hf
    exact hl v k hvk
  | algebraMap r =>
    intro x hx
    rw [Module.algebraMap_end_apply]
    exact (latLoc B j w).smul_mem r hx
  | add f g _ _ hf hg => intro x hx; exact Submodule.add_mem _ (hf x hx) (hg x hx)
  | mul f g _ _ hf hg => intro x hx; exact hf _ (hg x hx)

end GlobalTheory.LatSplit

namespace GlobalTheory.LatSplit

variable {D : D7} {M : MtFam D}

theorem proj_facts {K V : Type} [Field K] [AddCommGroup V] [Module K V] {P Q : Submodule K V} (hc : IsCompl P Q)
    (t : Module.End K V) (hP : ∀ x ∈ P, t x = x) (hQ : ∀ x ∈ Q, t x = 0) (y : V) : t y ∈ P ∧ y - t y ∈ Q := by
  have hy : y ∈ P ⊔ Q := hc.sup_eq_top ▸ Submodule.mem_top
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hy
  rw [map_add (f := _), hP p hp, hQ q hq, add_zero, add_sub_cancel_left]
  exact ⟨hp, hq⟩

theorem part_le_off {O K V : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V]
    [Module O V] [IsScalarTower O K V] [IsLocalRing O] (T : Subalgebra O (Module.End K V)) {I J : Ideal T} (h : I ≠ J) :
    NCov.part T I ≤ NCov.off T J :=
  iSup₂_le fun ψ hψ => le_iSup₂_of_le (f := fun ψ (_ : NCov.cls ψ ≠ J) => NCov.W T (NCov.pt ψ)) ψ
    (by rw [hψ]; exact h) le_rfl

theorem exists_proj (T : NormalizedLocalCompatibility D M) (hstd : HeckeStdTw T.B) {j : ℕ} {w : D.what₂.places.Pl} (h1 : 1 ≤ j)
    (h2 : j ≤ D.R.m) (hw : D.what₂.muAt w ≠ D.what₂.mu0) (hl : LatStable T.B j w) (I : Ideal (heckeAlg T.B j w)) :
    ∃ t ∈ heckeAlg T.B j w, (∀ x ∈ NCov.part (heckeAlg T.B j w) I, t x = x) ∧
      ∀ x ∈ NCov.off (heckeAlg T.B j w) I, t x = 0 := by
  obtain ⟨hfd, -⟩ := finrank_V T.B j w
  haveI := hfd
  obtain ⟨hS, hsplit, hint⟩ := gens_hypsTw T.B hstd h1 h2 (Or.inl hw)
  exact GlobalTheory.T.generalizedEigenPartProjector_mem_heckeAlgebra (T.B.Oc j w) (FractionRing (T.B.Oc j w)) (T.B.V j w) (heckeGens T.B j w) hS hsplit hint
    (latLoc T.B j w) (latLoc_fg T.B j w) (latLoc_span T.B j w)
    (fun a ha x hx => alg_stable T.B hl a (Algebra.subset_adjoin ha) x hx) I

theorem main : ∀ (D : D7) (M : MtFam D) (T : NormalizedLocalCompatibility D M) (j : ℕ) (w : D.what₂.places.Pl), 1 ≤ j → j ≤ D.R.m →
    D.what₂.muAt w ≠ D.what₂.mu0 → HeckeStdTw T.B → LatStable T.B j w → ∀ y : T.B.V j w,
    y ∈ latLoc T.B j w ↔ ∃ z : ∀ i : D.nd.Loc, TensorProduct (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i),
      (∀ i, z i ∈ D.nd.MtIn i) ∧ y = ∑ i ∈ (D.nd.locs j w).attach, T.Psi j w i.1 i.2 (z i.1) := by
  classical
  intro D M T j w h1 h2 hw hstd hl y
  obtain ⟨hfd, -⟩ := finrank_V T.B j w
  haveI := hfd
  obtain ⟨hS, hsplit, hint⟩ := gens_hypsTw T.B hstd h1 h2 (Or.inl hw)
  have hinj := IsFractionRing.injective (T.B.Oc j w) (FractionRing (T.B.Oc j w))
  choose tp htp hpart hoff using exists_proj T hstd h1 h2 hw hl
  have hc := fun I => NCov.isCompl_part_off hinj hS hsplit hint I
  have eL : latC T.B j w = latLoc T.B j w := rfl

  have hlp : ∀ I x, x ∈ NCov.latPart (heckeAlg T.B j w) (latC T.B j w) I → x ∈ latLoc T.B j w := by
    intro I x hx
    obtain ⟨hxP, hxL⟩ := Submodule.mem_inf.1 hx
    obtain ⟨l, hlL, q, hq, rfl⟩ := Submodule.mem_sup.1 hxL
    have e : tp I (l + q) = l + q := hpart I _ hxP
    rw [map_add (f := _), hoff I q hq, add_zero] at e
    rw [← e]
    exact alg_stable T.B hl _ (htp I) l hlL
  constructor
  · intro hy

    have ex : ∀ i (h : i ∈ D.nd.locs j w), ∃ z, z ∈ D.nd.MtIn i ∧ T.Psi j w i h z = tp (T.mx j w i) y := by
      intro i h
      haveI := RingHomInvPair.of_ringEquiv (T.phO j w i h)
      have hm : tp (T.mx j w i) y ∈ NCov.latPart (heckeAlg T.B j w) (latC T.B j w) (T.mx j w i) := by
        refine Submodule.mem_inf.2 ⟨(proj_facts (hc _) _ (hpart _) (hoff _) y).1, ?_⟩
        exact Submodule.mem_sup_left (alg_stable T.B hl _ (htp _) y hy)
      rw [← map_psiO_MtIn T hstd h] at hm
      obtain ⟨z, hz, e⟩ := Submodule.mem_map.1 hm
      exact ⟨z, hz, e⟩
    refine ⟨fun i => if h : i ∈ D.nd.locs j w then (ex i h).choose else 0, fun i => ?_, ?_⟩
    · by_cases h : i ∈ D.nd.locs j w
      · dsimp only; rw [dite_eq_left h]; exact (ex i h).choose_spec.1
      · dsimp only; rw [dite_eq_right h]; exact Submodule.zero_mem _
    · have hsum : ∑ i ∈ (D.nd.locs j w).attach,
          T.Psi j w i.1 i.2 (if h : i.1 ∈ D.nd.locs j w then (ex i.1 h).choose else 0) =
          ∑ i ∈ (D.nd.locs j w).attach, tp (T.mx j w i.1) y := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [dite_eq_left i.2]
        exact (ex i.1 i.2).choose_spec.2
      rw [hsum, ← sub_eq_zero]
      refine NCov.eq_zero_of_forall_mem_off hinj hS hsplit hint ((D.nd.locs j w).image (T.mx j w))
        (fun I hI => ?_) ?_
      · obtain ⟨i, hi, rfl⟩ := T.mx_all j w h1 h2 hw I hI
        exact Finset.mem_image_of_mem _ hi
      · intro I hI
        obtain ⟨i0, hi0, rfl⟩ := Finset.mem_image.1 hI
        rw [← Finset.add_sum_erase _ _ (Finset.mem_attach _ ⟨i0, hi0⟩), sub_add_eq_sub_sub]
        refine Submodule.sub_mem _ (proj_facts (hc _) _ (hpart _) (hoff _) y).2 (Submodule.sum_mem _ fun i hi => ?_)
        have hne : T.mx j w i.1 ≠ T.mx j w i0 := by
          intro e
          have := T.mx_inj j w i.2 hi0 e
          exact (Finset.mem_erase.1 hi).1 (Subtype.ext this)
        exact part_le_off _ hne (proj_facts (hc _) _ (hpart _) (hoff _) y).1
  · rintro ⟨z, hz, rfl⟩
    refine Submodule.sum_mem _ fun i _ => ?_
    haveI := RingHomInvPair.of_ringEquiv (T.phO j w i.1 i.2)
    refine hlp (T.mx j w i.1) _ ?_
    rw [← map_psiO_MtIn T hstd i.2]
    exact Submodule.mem_map_of_mem (hz i.1)

end GlobalTheory.LatSplit
end
end

section

noncomputable section

namespace GlobalTheory.RedFun.SubLat

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open GlobalTheory.TopSteps.StdAdm
open scoped LaurentSeries PowerSeries TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL]
  [CommRing O] [Algebra O LL] [TopologicalSpace LL]

def subLattice [IsDomain O] [IsPrincipalIdealRing O] (T : LocLat G Qp LL O) {lam : O}
    (hl : algebraMap O LL lam ≠ 0) (P : Submodule O ↥T.L.T) (hg : ∀ g, ∀ x ∈ P, latRep T.L g x ∈ P)
    (hP : ∀ x, lam • x ∈ P) : Lattice (O := O) T.ρ where
  T := P.map T.L.T.subtype
  stable := by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨latRep T.L g x, hg g x hx, rfl⟩
  fg := by
    have := finite_lat T
    exact (IsNoetherian.noetherian _).map _
  free := by
    have := finite_lat T
    have := T.L.free
    have : Module.Free O ↥P := Module.free_of_finite_type_torsion_free'
    exact Module.Free.of_equiv (Submodule.equivMapOfInjective _ T.L.T.injective_subtype _)
  span := by
    rw [eq_top_iff, ← T.L.span, Submodule.span_le]
    intro y hy
    have h1 : lam • y ∈ P.map T.L.T.subtype := ⟨lam • ⟨y, hy⟩, hP _, rfl⟩
    have h2 := Submodule.smul_mem _ (algebraMap O LL lam)⁻¹ (Submodule.subset_span (R := LL) h1)
    rwa [← algebraMap_smul LL lam y, inv_smul_smul₀ hl] at h2

variable {k : Type} [Field k] [Algebra O k]


omit [Algebra O LL] in
theorem lam_smul {lam : O} (hk : algebraMap O k lam = 0) {m : ℕ} (t : Fin m → k) : lam • t = 0 := by
  ext i
  simp [Algebra.smul_def, hk]

theorem exists_ker [IsDomain O] [IsPrincipalIdealRing O] {lam : O} (hl : algebraMap O LL lam ≠ 0)
    (hk : algebraMap O k lam = 0) (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k))
    (hq : Onto T A q) : ∃ (T' : LocLat G Qp LL O) (f : LatHom T'.L T.L),
      ∀ x : ↥T.L.T, q x = 0 ↔ ∃ y ∈ T'.L.T, f.f y = x := by
  have hq2 : ∀ σ x, q (latRep T.L σ x) = A.ρ σ (q x) := hq.2
  have hP : ∀ x, lam • x ∈ LinearMap.ker q := fun x => by
    rw [LinearMap.mem_ker, map_smul, lam_smul hk]
  have hg : ∀ σ, ∀ x ∈ LinearMap.ker q, latRep T.L σ x ∈ LinearMap.ker q := fun σ x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hq2, hx, map_zero]
  refine ⟨{ T with L := subLattice T hl (LinearMap.ker q) hg hP },
    ⟨LinearMap.id, fun _ _ => rfl, continuous_id, ?_⟩, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · intro x
    constructor
    · intro hx
      exact ⟨x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, h⟩
      have hzx : z = x := Subtype.ext h
      subst hzx
      exact hz

theorem exists_inv {lam : O} (hl : algebraMap O LL lam ≠ 0) (T T' : LocLat G Qp LL O) (f : LatHom T'.L T.L)
    (hf : Function.Injective f.f) (h : ∀ x ∈ T.L.T, ∃ y ∈ T'.L.T, f.f y = lam • x) :
    ∃ h : LatHom T.L T'.L, ∀ x, f.f (h.f x) = algebraMap O LL lam • x := by
  have hsurj : Function.Surjective f.f := by
    have hle : Submodule.span LL (T.L.T : Set T.V) ≤ LinearMap.range f.f := by
      rw [Submodule.span_le]
      intro x hx
      obtain ⟨y, -, hy⟩ := h x hx
      refine ⟨(algebraMap O LL lam)⁻¹ • y, ?_⟩
      rw [map_smul, hy, ← algebraMap_smul LL lam x, inv_smul_smul₀ hl]
    rw [T.L.span] at hle
    exact fun x => hle Submodule.mem_top
  let e := LinearEquiv.ofBijective f.f ⟨hf, hsurj⟩
  have h1 : ∀ z, f.f (e.symm z) = z := fun z => e.apply_symm_apply z
  let c := algebraMap O LL lam
  refine ⟨⟨c • (e.symm : T.V →ₗ[LL] T'.V), ?_, IsModuleTopology.continuous_of_linearMap _, ?_⟩, ?_⟩
  · intro σ x
    apply hf
    simp only [LinearMap.smul_apply, LinearEquiv.coe_coe, map_smul, f.equiv, h1]
  · intro x hx
    obtain ⟨y, hy, hfy⟩ := h x hx
    have hxy : (c • (e.symm : T.V →ₗ[LL] T'.V)) x = y := by
      apply hf
      rw [LinearMap.smul_apply, map_smul, LinearEquiv.coe_coe, h1, hfy, algebraMap_smul]
    rw [hxy]
    exact hy
  · intro x
    show f.f ((c • (e.symm : T.V →ₗ[LL] T'.V)) x) = c • x
    rw [LinearMap.smul_apply, map_smul, LinearEquiv.coe_coe, h1]

theorem exists_fibre [IsDomain O] [IsPrincipalIdealRing O] {lam : O} (hl : algebraMap O LL lam ≠ 0)
    (hk : algebraMap O k lam = 0) (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k))
    (T' : LocLat G Qp LL O) (A' : Ob k G) (q' : ↥T'.L.T →ₗ[O] (Fin A'.m → k))
    (g : (Fin A.m → k) →ₗ[k] (Fin A'.m → k)) (hq : Onto T A q) (hq' : Onto T' A' q') (hg : IsHom A A' g) :
    ∃ (T'' : LocLat G Qp LL O) (f : LatHom T''.L T.L) (f' : LatHom T''.L T'.L),
      (∀ x ∈ T.L.T, ∃ z ∈ T''.L.T, f.f z = x) ∧
      ∀ z : ↥T''.L.T, q' (GlobalTheory.EtaleExact.latMap f' z) = g (q (GlobalTheory.EtaleExact.latMap f z)) := by
  have hq2 : ∀ σ x, q (latRep T.L σ x) = A.ρ σ (q x) := hq.2
  have hq2' : ∀ σ x, q' (latRep T'.L σ x) = A'.ρ σ (q' x) := hq'.2
  have hg0 : ∀ σ x, g (A.ρ σ x) = A'.ρ σ (g x) := hg
  let φ : ↥(prodLat T T').L.T →ₗ[O] (Fin A'.m → k) :=
    q' ∘ₗ (LinearMap.snd O _ _ ∘ₗ (prodLatEquiv T T').toLinearMap) -
      (g.restrictScalars O) ∘ₗ q ∘ₗ (LinearMap.fst O _ _ ∘ₗ (prodLatEquiv T T').toLinearMap)
  have hφ : ∀ z, φ z = q' (prodLatEquiv T T' z).2 - g (q (prodLatEquiv T T' z).1) := fun z => rfl
  have hP : ∀ z, lam • z ∈ LinearMap.ker φ := fun z => by
    rw [LinearMap.mem_ker, map_smul, lam_smul hk]
  have hst : ∀ σ, ∀ z ∈ LinearMap.ker φ, latRep (prodLat T T').L σ z ∈ LinearMap.ker φ := by
    intro σ z hz
    rw [LinearMap.mem_ker, hφ] at hz ⊢
    simp only [prodLatEquiv_act]
    rw [hq2, hq2', hg0, ← map_sub, hz, map_zero]
  refine ⟨{ prodLat T T' with L := subLattice (prodLat T T') hl (LinearMap.ker φ) hst hP },
    ⟨LinearMap.fst LL T.V T'.V, fun _ _ => rfl, continuous_fst, ?_⟩,
    ⟨LinearMap.snd LL T.V T'.V, fun _ _ => rfl, continuous_snd, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨z, -, rfl⟩
    exact z.2.1
  · rintro _ ⟨z, -, rfl⟩
    exact z.2.2
  · intro x hx
    obtain ⟨x', hx'⟩ := hq'.1 (g (q ⟨x, hx⟩))
    let w : ↥(prodLat T T').L.T := ⟨(x, (x' : T'.V)), hx, x'.2⟩
    refine ⟨(x, (x' : T'.V)), ⟨w, ?_, rfl⟩, rfl⟩
    show φ w = 0
    rw [hφ]
    exact sub_eq_zero.mpr hx'
  · rintro ⟨_, ⟨w, hw, rfl⟩⟩
    have hw' : φ w = 0 := hw
    rw [hφ, sub_eq_zero] at hw'
    exact hw'

theorem ker_inv_fibre : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL] [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL] [TopologicalSpace LL] {k : Type} [Field k] [Algebra O k] (lam : O), algebraMap O LL lam ≠ 0 → algebraMap O k lam = 0 → (∀ (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q → ∃ (T' : LocLat G Qp LL O) (f : LatHom T'.L T.L), ∀ x : ↥T.L.T, q x = 0 ↔ ∃ y ∈ T'.L.T, f.f y = x) ∧ (∀ (T T' : LocLat G Qp LL O) (f : LatHom T'.L T.L), Function.Injective f.f → (∀ x ∈ T.L.T, ∃ y ∈ T'.L.T, f.f y = lam • x) → ∃ h : LatHom T.L T'.L, ∀ x, f.f (h.f x) = algebraMap O LL lam • x) ∧ ∀ (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)) (T' : LocLat G Qp LL O) (A' : Ob k G) (q' : ↥T'.L.T →ₗ[O] (Fin A'.m → k)) (g : (Fin A.m → k) →ₗ[k] (Fin A'.m → k)), Onto T A q → Onto T' A' q' → IsHom A A' g → ∃ (T'' : LocLat G Qp LL O) (f : LatHom T''.L T.L) (f' : LatHom T''.L T'.L), (∀ x ∈ T.L.T, ∃ z ∈ T''.L.T, f.f z = x) ∧ ∀ z : ↥T''.L.T, q' (GlobalTheory.EtaleExact.latMap f' z) = g (q (GlobalTheory.EtaleExact.latMap f z)) := by
  intro G _ _ Qp LL O _ _ _ _ _ _ _ _ k _ _ lam hl hk
  exact ⟨fun T A q hq => exists_ker hl hk T A q hq, fun T T' f hf h => exists_inv hl T T' f hf h,
    fun T A q T' A' q' g hq hq' hg => exists_fibre hl hk T A q T' A' q' g hq hq' hg⟩

end GlobalTheory.RedFun.SubLat
end
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

theorem _root_.GlobalTheory.T.localised_global_cocycles_in_local_span : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), (∀ f ∈ cocRho i r S Xs, InCut i r Xs (WpO D.nd i ρ π) w hw f) ∧ ∀ c : Fin D.R.t, ∀ f ∈ cocChi i r S Xs c, InCut i r Xs (chiRatO D.nd i ((c : ℕ) + 1)) w hw f := by
  first | exact @GlobalTheory.Cut.LocCoc.main | exact GlobalTheory.Cut.LocCoc.main | (intros; apply GlobalTheory.Cut.LocCoc.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

theorem _root_.GlobalTheory.T.typeSpace_projection_to_pointEigenspaces : ∀ (D : D7) (M : MtFam D) (i : D.nd.Loc), HeckeTied D M → HeckeRational D M → AVTied D M → SplitUnif D → HeckeScalar M i → D.nd.EigSpan → TypeTie D i := by
  first | exact @GlobalTheory.EtaJoin.TypeTieProof.typeTie_holds | exact GlobalTheory.EtaJoin.TypeTieProof.typeTie_holds | (intros; apply GlobalTheory.EtaJoin.TypeTieProof.typeTie_holds <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.LocalCocycleConstruction

open GlobalTheory.Cut.LocCoc

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), (∀ f ∈ cocRho i r S Xs, InCut i r Xs (WpO D.nd i ρ π) w hw f) ∧ ∀ c : Fin D.R.t, ∀ f ∈ cocChi i r S Xs c, InCut i r Xs (chiRatO D.nd i ((c : ℕ) + 1)) w hw f := by
  intro D i r ρ π Xs S _ hG _ w hw
  obtain ⟨-, hdec, hψ, -, -, -, -, -, -, ⟨hπ, -⟩, -⟩ := hG
  have key : ∀ γ u, (((S.ψρ fun x' => rTwO D.nd i r (S.p x') γ).map (toK D.nd i)).mulVec (S.e u).1,
      fun c : Fin D.R.t => toK D.nd i (S.ψχ c fun x' => rTwO D.nd i r (S.p x') γ) * (S.e u).2 c) =
      toK D.nd i (((chiU D.nd i 1 γ)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) •
        ((mapM (toK D.nd i) (rhoO D.nd i ρ π) γ).mulVec (S.e u).1,
        fun c : Fin D.R.t => toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) γ : (D.nd.O i)ˣ) : D.nd.O i) * (S.e u).2 c) := by
    intro γ u
    rw [← hψ _ (GlobalTheory.Cut.LocCoc.inR'_tw i r S γ) u, ← hdec, ← map_smul, hπ, ← Matrix.smul_mulVec]
    congr 2
    ext p q
    simp [mapM, rTwO, twistM]
  refine ⟨fun f hf => GlobalTheory.Cut.LocCoc.inCut_of_cocW i r S Xs _ _ (fun γ => ?_) w hw f hf,
    fun c f hf => GlobalTheory.Cut.LocCoc.inCut_of_cocW i r S Xs _ _ (fun γ => ?_) w hw f hf⟩
  · ext p q
    apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
    have h := congrArg (fun z => z.1 p) (key γ (S.e.symm (Pi.single q 1, 0)))
    simpa [mapM, WpO, twistM] using h
  · ext p q
    apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
    have h := congrArg (fun z => z.2 c) (key γ (S.e.symm (0, Pi.single c 1)))
    obtain rfl : p = q := Subsingleton.elim _ _
    simpa [chiRatO, twistM, mul_comm] using h

end GlobalTheory.Cut.LocalCocycleConstruction
end

section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.isotypicValuationAtRing_of_unrRho_hodgeL_noInv_negCount : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), UnrRho i s → HodgeL bkP i s → (∀ v, NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v) → NegCount bkP i s → IsotypicValuationAtRing bkP i s := by
  first | exact @GlobalTheory.TripleGal.firstAdmissibilityAt_of_parts | exact GlobalTheory.TripleGal.firstAdmissibilityAt_of_parts | (intros; apply GlobalTheory.TripleGal.firstAdmissibilityAt_of_parts <;> assumption)
end

section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.exists_complex_reading_local_embedding : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (ι : FractionRing (D.ntw.O0 i) →+* ℂ) (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) (τ : EmbV bkP i v hv), ∃ τc : D.host.E →+* ℂ, ReadEmb bkP i ι v hv τ τc ∧ ∀ (v' : HeightOneSpectrum (𝓞 D.host.E)) (hv' : v' ∈ placesOver D.host.E (D.ntw.l i)) (τ' : EmbV bkP i v' hv'), IsConjEmb bkP i v v' hv hv' τ τ' → ReadEmb bkP i ι v' hv' τ' (τc.comp (cj D)) := by
  first | exact @GlobalTheory.ReadEmbEx.exists_readEmb | exact GlobalTheory.ReadEmbEx.exists_readEmb | (intros; apply GlobalTheory.ReadEmbEx.exists_readEmb <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct

theorem _root_.GlobalTheory.T.tameInertiaElement_acts_by_scalar : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (z : GE N), IsotypicValuationAtRing bkP i s → IsTameInertiaElementAtTwistPrime X i z → ∃ d : (X.O0 i)ˣ, Tmat i s z = (d : X.O0 i) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) ∧ IsUnit ((d : X.O0 i) ^ 2 - 1) ∧ IsUnit ((d : X.O0 i) - 1) ∧ eps0 X i z = 1 := by
  first | exact @GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia | exact GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia | (intros; apply GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia <;> assumption)
end

section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.finrank_DdR_and_fil_zero_of_jump_multiset : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), ∀ (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) (τ : EmbV bkP i v hv) (M : Multiset ℤ), HodgeL bkP i s → (∀ a : ℤ, Formalism.WeaklyAdmissibleFiltrations.multV (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) τ a = (M.count a : ℤ)) → dimD bkP i v hv (Tgl i s) τ = Multiset.card M ∧ dimFil0 bkP i v hv (Tgl i s) τ = Multiset.card (M.filter (0 ≤ ·)) := by
  first | exact @GlobalTheory.JumpDims.dims_of_mult | exact GlobalTheory.JumpDims.dims_of_mult | (intros; apply GlobalTheory.JumpDims.dims_of_mult <;> assumption)
end

section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.noDecompositionInvariants_aboveL_of_noHodgeJump : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), NoJump bkP i s → ∀ v ∈ placesOver D.host.E (D.ntw.l i), NoInv i (Tmat i s) v := by
  first | exact @GlobalTheory.InvJump.noInv_of_noJump | exact GlobalTheory.InvJump.noInv_of_noJump | (intros; apply GlobalTheory.InvJump.noInv_of_noJump <;> assumption)
end

section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.selfDual_lattice_of_conjDualCharpoly : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i), ValuationStabilityAtRing D.ntw i s → CharDual i s → SelfDual i s := by
  first | exact @GlobalTheory.LatticeSelfDual.selfDual_of_charDual | exact GlobalTheory.LatticeSelfDual.selfDual_of_charDual | (intros; apply GlobalTheory.LatticeSelfDual.selfDual_of_charDual <;> assumption)
end
