module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle047
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ConjSep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a}

private theorem lev_mono {U U' : Subgroup (GL (Fin a) (Af E))} (h : U' ≤ U) {q : ℕ} {α : Geo.Co Ξ q}
    (hα : Geo.IsLev U Ξ α) : Geo.IsLev U' Ξ α :=
  ⟨hα.equiv, hα.basic, fun X => Submodule.span_mono (by
    rintro _ ⟨φ, v, hφ, rfl⟩
    exact ⟨φ, v, ⟨hφ.1, fun u hu => hφ.2.1 u (h hu), hφ.2.2⟩, rfl⟩) (hα.val X)⟩

private theorem lev_comb {U : Subgroup (GL (Fin a) (Af E))} {q : ℕ} (s : ℂ) {α β : Geo.Co Ξ q}
    (hα : Geo.IsLev U Ξ α) (hβ : Geo.IsLev U Ξ β) : Geo.IsLev U Ξ (s • α + β) := by
  have ap : ∀ X, (s • α + β) X = s • α X + β X := fun X => rfl
  refine ⟨fun k X => ?_, fun X i hi => ?_, fun X => ?_⟩
  · rw [ap, ap, hα.equiv k X, hβ.equiv k X, map_add (f := _), map_smul]
  · rw [ap, hα.basic X i hi, hβ.basic X i hi, smul_zero, add_zero]
  · rw [ap]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hα.val X)) (hβ.val X)

private theorem lev_zero {U : Subgroup (GL (Fin a) (Af E))} {q : ℕ} : Geo.IsLev U Ξ (0 : Geo.Co Ξ q) :=
  ⟨fun k X => by simp, fun X i _ => rfl, fun X => Submodule.zero_mem _⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.Cj.levSub :
    UpperTheory.V.Cj.LevSub := by
  intro E _ _ _ a Ξ q
  refine ⟨fun U s α β hα hβ => lev_comb s hα hβ, fun U U' h α => ⟨lev_mono h, fun hα => ?_⟩, ?_⟩
  · cases q with
    | zero => exact hα
    | succ q =>
      obtain ⟨η, h1, h2⟩ := hα
      exact ⟨η, lev_mono h h1, h2⟩
  · refine ⟨{ carrier := {ω | Lev Ξ ω}, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, fun ω => Iff.rfl, ?_⟩
    · rintro α β ⟨U, u1, u2, u3⟩ ⟨U', v1, v2, v3⟩
      have ho : IsOpen ((U ⊓ U' : Subgroup _) : Set (GL (Fin a) (Af E))) := u1.inter v1
      refine ⟨U ⊓ U', ho, u2.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) fun k hk => hk.1, ?_⟩
      have := lev_comb 1 (lev_mono inf_le_left u3) (lev_mono (U' := U ⊓ U') inf_le_right v3)
      rwa [one_smul] at this
    · obtain ⟨U, u1, u2⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E a
      exact ⟨U, u1, u2, lev_zero⟩
    · rintro s α ⟨U, u1, u2, u3⟩
      have := lev_comb s u3 lev_zero
      rw [add_zero] at this
      exact ⟨U, u1, u2, this⟩
    · rintro x ω ⟨U, u1, u2, u3⟩
      let e : GL (Fin a) (Af E) ≃ₜ GL (Fin a) (Af E) := (Homeomorph.mulLeft x⁻¹).trans (Homeomorph.mulRight x)
      have he : ((U.comap (MulAut.conj x⁻¹).toMonoidHom : Subgroup _) : Set (GL (Fin a) (Af E))) = e ⁻¹' U := by
        ext u
        simp [e]
      refine ⟨U.comap (MulAut.conj x⁻¹).toMonoidHom, ?_, ?_, (perNat E a U _ x (fun u hu => ?_) Ξ q ω u3).1⟩
      · rw [he]; exact u1.preimage e.continuous
      · rw [he]; exact e.isCompact_preimage.2 u2
      · simpa using hu
end

section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

private theorem geo_hd_smul_add {Γ M : Type} [AddCommGroup M] [Module ℂ M] (s : ℂ)
    (b b' : List Γ → M) (x : List Γ) :
    UpperTheory.V.Lit.Geo.hd (s • b + b') x =
      s • UpperTheory.V.Lit.Geo.hd b x + UpperTheory.V.Lit.Geo.hd b' x := by
  unfold UpperTheory.V.Lit.Geo.hd
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, Pi.smul_apply, smul_add, smul_comm]

theorem UpperTheory.V.Cj.cobLin :
    UpperTheory.V.Cj.CobLin := by
  intro Γ M _ _ _ ρ q s c c' hc hc'
  cases q with
  | zero =>
    simp only [UpperTheory.V.Lit.Geo.HCob] at hc hc' ⊢
    intro x hx
    rw [Pi.add_apply, Pi.smul_apply, hc x hx, hc' x hx, smul_zero, add_zero]
  | succ k =>
    simp only [UpperTheory.V.Lit.Geo.HCob] at hc hc' ⊢
    obtain ⟨b, hbe, hbc⟩ := hc
    obtain ⟨b', hbe', hbc'⟩ := hc'
    refine ⟨s • b + b', fun γ x hx => ?_, fun x hx => ?_⟩
    · rw [Pi.add_apply, Pi.smul_apply, Pi.add_apply, Pi.smul_apply, hbe γ x hx, hbe' γ x hx,
        map_add, map_smul]
    · rw [geo_hd_smul_add, Pi.add_apply, Pi.smul_apply, hbc x hx, hbc' x hx]
end

section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

private def Cv (_ : ℂ ≃+* ℂ) (V : Type) : Type := V

private instance (σ : ℂ ≃+* ℂ) (V : Type) [i : AddCommGroup V] : AddCommGroup (Cv σ V) := i

private noncomputable instance (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V] : Module ℂ (Cv σ V) :=
  Module.compHom V σ.symm.toRingHom

private def toCv (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] : V ≃+ Cv σ V := AddEquiv.refl V

private theorem smul_toCv (σ : ℂ ≃+* ℂ) {V : Type} [AddCommGroup V] [Module ℂ V] (c : ℂ) (v : V) :
    c • toCv σ V v = toCv σ V (σ.symm c • v) := rfl

private theorem toCv_smul (σ : ℂ ≃+* ℂ) {V : Type} [AddCommGroup V] [Module ℂ V] (c : ℂ) (v : V) :
    toCv σ V (c • v) = σ c • toCv σ V v := by
  rw [smul_toCv, RingEquiv.symm_apply_apply]

private noncomputable def cvRep (σ : ℂ ≃+* ℂ) {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : Representation ℂ G (Cv σ V) where
  toFun g :=
    { toFun := fun v => toCv σ V (ρ g ((toCv σ V).symm v))
      map_add' := fun x y => by simp only [map_add (f := _)]
      map_smul' := fun c x => congrArg (toCv σ V) (map_smul (ρ g) (σ.symm c) ((toCv σ V).symm x)) }
  map_one' := LinearMap.ext fun v => by simp
  map_mul' x y := LinearMap.ext fun v => by
    simp only [map_mul]
    rfl

private theorem cvRep_irr (σ : ℂ ≃+* ℂ) {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : (cvRep σ ρ).IsIrreducible := by
  obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff ρ).1 h
  refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => ?_⟩
  let W' : Submodule ℂ V :=
    { carrier := {v | toCv σ V v ∈ W}
      add_mem' := fun {x y} hx hy => W.add_mem hx hy
      zero_mem' := W.zero_mem
      smul_mem' := fun c x hx => by
        change toCv σ V (c • x) ∈ W
        rw [toCv_smul]
        exact W.smul_mem _ hx }
  rcases h1 W' (fun g v hv => hW g _ hv) with e | e
  · exact Or.inl ((Submodule.eq_bot_iff _).2 fun v hv => (Submodule.eq_bot_iff _).1 e ((toCv σ V).symm v) hv)
  · exact Or.inr (Submodule.eq_top_iff'.2 fun v => Submodule.eq_top_iff'.1 e ((toCv σ V).symm v))

theorem UpperTheory.V.Cj.conjEx :
    UpperTheory.V.Cj.ConjEx := by
  intro E _ _ a σ τ
  exact ⟨SmIrr.mk (Cv σ τ.V) (cvRep σ τ.ρ) τ.5 (cvRep_irr σ τ.ρ τ.irred), toCv σ τ.V, toCv_smul σ, fun _ _ => rfl⟩
end

section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

private theorem irrAbs_module {R M S W κ ι : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup S] [Module R S]
    [AddCommGroup W] [Module R W] [IsSimpleModule R S] [Finite ι] (Φ : (κ →₀ S) →ₗ[R] M) (hs : Function.Surjective Φ)
    (p : ι → W →ₗ[R] M) (hp : ∀ w, (∀ i, p i w = 0) → w = 0) (x : W) (hx : x ≠ 0) :
    ∃ f : S →ₗ[R] W, Function.Injective f := by
  haveI := IsSemisimpleModule.range Φ
  haveI : IsSemisimpleModule R M :=
    IsSemisimpleModule.congr (LinearEquiv.ofTop _ (LinearMap.range_eq_top.2 hs)).symm
  let e : W →ₗ[R] (ι → M) := LinearMap.pi p
  have he : Function.Injective e := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    exact hp w fun i => congrFun hw i
  haveI : IsSemisimpleModule R W := IsSemisimpleModule.of_injective e he
  haveI : Nontrivial W := ⟨⟨x, 0, hx⟩⟩
  obtain ⟨N, hN⟩ := IsSemisimpleModule.exists_simple_submodule R W
  haveI := hN
  haveI := IsSimpleModule.nontrivial R N
  obtain ⟨y, hy⟩ := exists_ne (0 : N)
  have hex : ∃ i, p i (y : W) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hy (Subtype.ext (hp _ h))
  obtain ⟨i, hi⟩ := hex
  let g : N →ₗ[R] M := (p i).comp N.subtype
  have hg : Function.Injective g := by
    rcases g.injective_or_eq_zero with h | h
    · exact h
    · exact absurd (LinearMap.congr_fun h y) hi
  obtain ⟨r, hr⟩ := IsSemisimpleModule.extension_property g hg LinearMap.id
  have hrΦ : r.comp Φ ≠ 0 := by
    obtain ⟨z, hz⟩ := hs (g y)
    intro h
    apply hy
    have h1 := LinearMap.congr_fun h z
    have h2 := LinearMap.congr_fun hr y
    simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply] at h1 h2
    rw [hz] at h1
    rw [← h2, h1]
  have hex2 : ∃ k, (r.comp Φ).comp (Finsupp.lsingle k) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hrΦ
    apply Finsupp.lhom_ext
    intro a b
    simpa using LinearMap.congr_fun (h a) b
  obtain ⟨k, hk⟩ := hex2
  have hf0 : Function.Injective ((r.comp Φ).comp (Finsupp.lsingle k)) :=
    (LinearMap.injective_or_eq_zero _).resolve_right hk
  exact ⟨N.subtype.comp ((r.comp Φ).comp (Finsupp.lsingle k)), N.injective_subtype.comp hf0⟩

theorem UpperTheory.V.Cj.irrAbs :
    UpperTheory.V.Cj.IrrAbs := by
  intro G S V W ι _ _ _ _ _ _ _ _ _ ρS ρV ρW hirr hsup p hp hsep
  classical
  let F : {f : S →ₗ[ℂ] V // ∀ (g : G) (v : S), f ((ρS g) v) = (ρV g) (f v)} →
      (ρS.asModule →ₗ[MonoidAlgebra ℂ G] ρV.asModule) := fun f =>
    Representation.IntertwiningMap.equivLinearMapAsModule ρS ρV
      ((f.1).intertwiningMap_of_isIntertwiningMap ρS ρV f.2)
  let Φ := Finsupp.lsum ℕ F
  have key : ∀ u : V, u ∈ (⨆ f : {f : S →ₗ[ℂ] V // ∀ (g : G) (v : S), f ((ρS g) v) = (ρV g) (f v)},
      LinearMap.range f.1) → ∃ z, Φ z = (show ρV.asModule from u) := by
    intro u hu
    refine Submodule.iSup_induction (motive := fun u : V => ∃ z, Φ z = (show ρV.asModule from u)) _ hu ?_ ?_ ?_
    · rintro f u ⟨s, rfl⟩
      exact ⟨Finsupp.single f s, Finsupp.lsum_single ℕ F f s⟩
    · exact ⟨0, map_zero Φ⟩
    · rintro a b ⟨za, ha⟩ ⟨zb, hb⟩
      exact ⟨za + zb, by rw [map_add (f := _), ha, hb]; rfl⟩
  have hΦ : Function.Surjective Φ := by
    intro v
    exact key v (by rw [hsup]; exact Submodule.mem_top)
  let P : ι → (ρW.asModule →ₗ[MonoidAlgebra ℂ G] ρV.asModule) := fun i =>
    Representation.IntertwiningMap.equivLinearMapAsModule ρW ρV
      ((p i).intertwiningMap_of_isIntertwiningMap ρW ρV (hp i))
  have hP : ∀ w : ρW.asModule, (∀ i, P i w = 0) → w = 0 := fun w h => hsep w h
  obtain ⟨x, hx⟩ := exists_ne (0 : W)
  haveI : IsSimpleModule (MonoidAlgebra ℂ G) ρS.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρS).1 hirr
  obtain ⟨f, hf⟩ := irrAbs_module Φ hΦ P hP (show ρW.asModule from x) hx
  let f' := (Representation.IntertwiningMap.equivLinearMapAsModule ρS ρW).symm f
  exact ⟨f'.toLinearMap, hf, fun g v => f'.isIntertwining ρS ρW g v⟩
end

section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

private theorem hcob_map {Γ M M' : Type} [Group Γ] [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']
    (ρ : Representation ℂ Γ M) (ρ' : Representation ℂ Γ M') (T : M →+ M') (hT : ∀ γ m, T (ρ γ m) = ρ' γ (T m))
    (q : ℕ) (c : List Γ → M) (hc : HCob ρ q c) : HCob ρ' q (fun x => T (c x)) := by
  cases q with
  | zero =>
    intro x hx
    change T (c x) = 0
    rw [hc x hx, map_zero]
  | succ k =>
    obtain ⟨b, b1, b2⟩ := hc
    refine ⟨fun x => T (b x), fun γ x hx => ?_, fun x hx => ?_⟩
    · change T (b _) = _
      rw [b1 γ x hx, hT]
    · change T (c x) = _
      rw [b2 x hx]

      simp only [hd, map_sum, map_zsmul]

private theorem sigCob_one {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) (σ : ℂ ≃+* ℂ) {Ξ Ξ' : AlgRep E a} (h : Ξ.d = Ξ'.d) (hσ : ConjMat σ h) (q : ℕ)
    (c : List ↥(⊤ : Subgroup (GL (Fin a) E)) → (GL (Fin a) (Af E) ⧸ U) → Fin Ξ.d → ℂ)
    (hc : HCob (levelRep ⊤ U (ratC Ξ)) q c) : HCob (levelRep ⊤ U (ratC Ξ')) q (sigC σ h c) := by
  let T : ((GL (Fin a) (Af E) ⧸ U) → Fin Ξ.d → ℂ) →+ ((GL (Fin a) (Af E) ⧸ U) → Fin Ξ'.d → ℂ) :=
    { toFun := fun f y i => σ (f y (Fin.cast h.symm i))
      map_zero' := by ext y i; simp
      map_add' := fun f g => by ext y i; simp }
  refine hcob_map _ _ T (fun γ f => ?_) q c hc
  funext y i
  change σ ((ratC Ξ γ *ᵥ f _) (Fin.cast h.symm i)) = (ratC Ξ' γ *ᵥ fun j => σ (f _ (Fin.cast h.symm j))) i

  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, ← hσ _ _ _]
  exact Fintype.sum_equiv (finCongr h) _ _ fun j => rfl

theorem UpperTheory.V.Cj.sigCob :
    UpperTheory.V.Cj.SigCob := by
  intro E _ _ _ a U σ Ξ Ξ' h hσ q c
  refine ⟨fun hc => ?_, sigCob_one U σ h hσ q c⟩
  have hσ' : ConjMat σ.symm h.symm := fun γ i j => by
    rw [RingEquiv.eq_symm_apply, ← hσ]; rfl
  have e : sigC σ.symm h.symm (sigC σ h c) = c := by
    funext z y i
    exact σ.symm_apply_apply _
  have := sigCob_one U σ.symm h.symm hσ' q _ hc
  rwa [e] at this
end

section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

theorem UpperTheory.V.Cj.twReg :
    UpperTheory.V.Cj.TwReg := by
  intro E _ _ _ a n π μ m hμ hm hr ν hν; refine (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun t => ?_
  have e := ((hμ t).twist ν).infChar_eq
  rw [e, (InfType.expo_of_infType E ν).2.1 _ hν t]
  obtain ⟨-, h1, h2⟩ := hr t
  refine ⟨(Multiset.nodup_of_le (hm t) h1).map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := h2 y (Multiset.mem_of_le (hm t) hy)
  exact ⟨k, by push_cast; ring⟩
end

section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

theorem UpperTheory.V.Cj.graph :
    UpperTheory.V.Cj.Graph := by
  intro G V V' W _ _ _ _ _ _ _ ρ ρ' ρW σ T hTs hTg M hM R hlin hg hex hiff
  have huniq : ∀ v w1 w2, w1 ∈ M → w2 ∈ M → R v w1 → R v w2 → w1 = w2 := by
    intro v w1 w2 m1 m2 r1 r2
    have h := hlin (-1) v v w1 w2 r1 r2
    have hm : σ (-1) • w1 + w2 ∈ M := M.add_mem (M.smul_mem _ m1) m2
    have h0 : (-1 : ℂ) • v + v = 0 := by simp
    rw [h0] at h
    have h1 := (hiff 0 _ hm h).1 rfl
    rw [map_neg, map_one, neg_one_smul, neg_add_eq_zero] at h1
    exact h1
  have hR0 : R 0 0 := by
    obtain ⟨w, hw, hr⟩ := hex 0
    rwa [(hiff 0 w hw hr).1 rfl] at hr
  choose j hjM hjR using fun v' : V' => hex (T.symm v')
  have hTsymm_smul : ∀ (c : ℂ) (v' : V'), T.symm (c • v') = σ.symm c • T.symm v' := by
    intro c v'
    apply T.injective
    rw [hTs, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  have hTsymm_g : ∀ (g : G) (v' : V'), T.symm (ρ' g v') = ρ g (T.symm v') := by
    intro g v'
    apply T.injective
    rw [hTg, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  let J : V' →ₗ[ℂ] W :=
    { toFun := j
      map_add' := by
        intro a b
        apply huniq (T.symm (a + b)) _ _ (hjM _) (M.add_mem (hjM a) (hjM b)) (hjR _)
        have h := hlin 1 _ _ _ _ (hjR a) (hjR b)
        simpa [map_add (f := _)] using h
      map_smul' := by
        intro c a
        apply huniq (T.symm (c • a)) _ _ (hjM _) (M.smul_mem c (hjM a)) (hjR _)
        have h := hlin (σ.symm c) _ _ _ _ (hjR a) hR0
        simpa [hTsymm_smul] using h }
  refine ⟨J, ?_, hjM, ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v' hv'
    have h := (hiff (T.symm v') (j v') (hjM v') (hjR v')).2 hv'
    simpa using congrArg T h
  · intro g v'
    apply huniq (T.symm (ρ' g v')) _ _ (hjM _) (hM g _ (hjM v')) (hjR _)
    rw [hTsymm_g]
    exact hg g _ _ (hjR v')
end

section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

theorem UpperTheory.V.Cj.satConj :
    UpperTheory.V.Cj.SatConj := by
  intro E _ _ _ n hC π
  induction π using Quotient.inductionOn with | _ π => ?_
  intro hπ σ
  obtain ⟨π', τ, τ', h1, h2, h3, -⟩ := hC π hπ σ
  obtain ⟨hs, hs'⟩ := sep_of_conj h1 h2 h3
  exact ⟨CG.mk π', fun w B hB => (hs.comp _).exists_hasSatGL (hs'.comp _) hB⟩
end

section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

private theorem cob_map {Γ M N : Type} [Group Γ] [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (ρ : Representation ℂ Γ M) (ρ' : Representation ℂ Γ N) (P : M →ₗ[ℂ] N) (hP : ∀ γ m, P (ρ γ m) = ρ' γ (P m))
    (q : ℕ) (c : List Γ → M) (h : HCob ρ q c) : HCob ρ' q (fun z => P (c z)) := by
  cases q with
  | zero =>
    intro z hz
    beta_reduce
    rw [h z hz, map_zero]
  | succ q =>
    obtain ⟨b, b1, b2⟩ := h
    refine ⟨fun z => P (b z), fun γ z hz => ?_, fun z hz => ?_⟩
    · beta_reduce
      rw [b1 γ z hz, hP]
    · beta_reduce
      rw [b2 z hz]

      simp only [hd, map_sum, map_zsmul]

private theorem coset_map {G : Type} [Group G] {U U' : Subgroup G} {x : G} (hx : ∀ u ∈ U', x⁻¹ * u * x ∈ U) :
    ∃ f : G ⧸ U' → G ⧸ U, (∀ y : G, f y = ((y * x : G) : G ⧸ U)) ∧ ∀ (g : G) s, f (g • s) = g • f s := by
  have wd : ∀ y y' : G, (QuotientGroup.leftRel U') y y' → ((y * x : G) : G ⧸ U) = ((y' * x : G) : G ⧸ U) := by
    intro y y' hy
    have h1 := hx _ (QuotientGroup.leftRel_apply.1 hy)
    refine QuotientGroup.eq.2 ?_
    convert h1 using 1
    group
  refine ⟨Quotient.lift _ wd, fun _ => rfl, fun g s => ?_⟩
  induction s using QuotientGroup.induction_on with | H y => ?_
  change ((g * y * x : G) : G ⧸ U) = ((g * (y * x) : G) : G ⧸ U)
  rw [mul_assoc]

theorem UpperTheory.V.Cj.relPull :
    UpperTheory.V.Cj.RelPull := by
  intro E _ _ _ a U U' x hx σ Ξ Ξ' h q α β ⟨hα, hβ, c, c', p, p', hc⟩
  obtain ⟨f, f1, f2⟩ := coset_map hx
  obtain ⟨a1, -, a2⟩ := perNat E a U U' x hx Ξ q α hα
  obtain ⟨b1, -, b2⟩ := perNat E a U U' x hx Ξ' q β hβ
  refine ⟨a1, b1, fun z s => c z (f s), fun z s => c' z (f s), a2 c _ (fun z y => by rw [f1]) p,
    b2 c' _ (fun z y => by rw [f1]) p', ?_⟩
  refine cob_map (levelRep ⊤ U (ratC Ξ')) (levelRep ⊤ U' (ratC Ξ')) (LinearMap.funLeft ℂ _ f) (fun γ m => ?_) q _ hc
  funext s
  change _ *ᵥ m (_ • f s) = _ *ᵥ m (f (_ • s))
  rw [f2]
end
