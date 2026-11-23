module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1683
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle735
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle142
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle140
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle729
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle736
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1790
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle047
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Analysis.Calculus.SmoothSeries
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin

noncomputable section

namespace GlobalTheory.UPel.HT.LieLin

section Transport

variable {O T V W : Type} [CommRing O] [CommRing T] [AddCommGroup V] [Module T V] [AddCommGroup W] [Module T W]
  (ψ : O →+* Module.End T V) (ν : O →+* Module.End T W) (e : V ≃ₗ[T] W) (he : ∀ c v, e (ψ c v) = ν c (e v))
include he

theorem mem_eigSub_transport (τ : O →+* T) (v : V) : e v ∈ eigSub ν τ ↔ v ∈ eigSub ψ τ := by
  simp only [mem_eigSub]
  refine forall_congr' fun c => ?_
  rw [← he, ← map_smul, e.injective.eq_iff]

theorem eigSub_transport (τ : O →+* T) : (eigSub ψ τ).map (e : V →ₗ[T] W) = eigSub ν τ := by
  ext w
  rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, ← mem_eigSub_transport ψ ν e he]
  simp

theorem finrank_eigSub_transport (τ : O →+* T) :
    Module.finrank T (eigSub ψ τ) = Module.finrank T (eigSub ν τ) := by
  rw [← eigSub_transport ψ ν e he τ]
  exact (e.submoduleMap (eigSub ψ τ)).finrank_eq

theorem lieMod_transport (ω : O) (ρ : T) {a : ℕ} (τ : Fin a → (O →+* T)) :
    LieMod ψ ω ρ τ ↔ LieMod ν ω ρ τ := by
  constructor
  · intro h w hw
    obtain ⟨u, hu, hs⟩ := h (e.symm w) (by
      apply e.injective
      rw [he, map_smul, LinearEquiv.apply_symm_apply, hw])
    refine ⟨fun i => e (u i), fun i => (mem_eigSub_transport ψ ν e he _ _).2 (hu i), ?_⟩

    rw [← map_sum, ← hs, LinearEquiv.apply_symm_apply]
  · intro h v hv
    obtain ⟨u, hu, hs⟩ := h (e v) (by rw [← he, hv, map_smul])
    refine ⟨fun i => e.symm (u i), fun i => ?_, ?_⟩
    · rw [← mem_eigSub_transport ψ ν e he, LinearEquiv.apply_symm_apply]
      exact hu i
    · apply e.injective

      rw [map_sum, hs]
      simp

end Transport

theorem spMap_comp_spMap' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem exists_baseMap {R : Type} [CommRing R] {S : Scheme.{0}} (s : S ⟶ Sp R) {U : S.Opens} (hU : IsAffineOpen U) :
    ∃ βB : R →+* Γ(S, U), ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R') (β : R →+* R'),
      spMap f ≫ hU.fromSpec ≫ s = spMap β → β = f.comp βB := by
  refine ⟨(Spec.preimage (hU.fromSpec ≫ s)).hom, fun R' _ f β h => ?_⟩
  have h2 : spMap (f.comp (Spec.preimage (hU.fromSpec ≫ s)).hom) = spMap β := by
    rw [← h, ← spMap_comp_spMap']
    congr 1
    show Spec.map (CommRingCat.ofHom (Spec.preimage (hU.fromSpec ≫ s)).hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have h3 := Spec.map_injective h2
  exact (congrArg CommRingCat.Hom.hom h3).symm

theorem lieHer_iff_mat {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] (b : Base D R) {S : Scheme.{0}}
    {A : Over S} [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) {U : S.Opens} (hU : IsAffineOpen U) {n : ℕ}
    (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) Γ(S, U))
    (hM : ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R'),
      ∃ e : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (spMap f ≫ hU.fromSpec) A ≃ₗ[R'] (Fin n → R'),
        ∀ (c : 𝓞 D.F) (v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (spMap f ≫ hU.fromSpec) A),
          e (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR (x0 := spMap f ≫ hU.fromSpec) (S := R') (act.toF D) c v) = matAct M f c (e v))
    {R' : Type} [CommRing R'] (f : Γ(S, U) →+* R') (β : R →+* R') :
    LieHer b act β (spMap f ≫ hU.fromSpec) ↔ LieHerMat b M f β := by
  unfold LieHer LieHerMat LieRankAt
  refine forall_congr' fun T' => forall_congr' fun _ => forall_congr' fun g => ?_
  have hx : spMap g ≫ spMap f ≫ hU.fromSpec = spMap (g.comp f) ≫ hU.fromSpec := by
    rw [← Category.assoc, spMap_comp_spMap']
  rw [hx]
  obtain ⟨e, he⟩ := hM T' (g.comp f)
  refine and_congr ?_ ?_
  · rw [GlobalTheory.T.harrisTaylorLieConditionAt_iff_kottwitzModuleCondition]
    exact lieMod_transport _ _ e he _ _ _
  · refine forall_congr' fun k => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun h =>
      forall_congr' fun i => ?_
    have hx2 : spMap h ≫ spMap (g.comp f) ≫ hU.fromSpec = spMap (h.comp (g.comp f)) ≫ hU.fromSpec := by
      rw [← Category.assoc, spMap_comp_spMap']
    rw [hx2]
    obtain ⟨e2, he2⟩ := hM k (h.comp (g.comp f))
    haveI : Module.Finite k (ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (spMap (h.comp (g.comp f)) ≫ hU.fromSpec) A) :=
      Module.Finite.equiv e2.symm
    rw [GlobalTheory.T.lieMult_iff_finrank_simultaneousEigenSubmodule _ _ _ _ _ _ _ _ inferInstance, finrank_eigSub_transport _ _ e2 he2]

theorem lieHerMat_iff_le {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] (b : Base D R) {B : Type}
    [CommRing B] (βB : R →+* B) {n : ℕ} (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (K₂ : Ideal B)
    (hK₂ : ∀ (T : Type) [CommRing T] (f : B →+* T), lieIdeal b βB M ≤ RingHom.ker f →
      ((∀ (k : Type) [Field k] [IsAlgClosed k] (h : T →+* k) (i : Fin D.a),
          Module.finrank k (eigSub (matAct M (h.comp f)) ((h.comp (f.comp βB)).comp (b.t i))) = D.m) ↔
        K₂ ≤ RingHom.ker f))
    {T : Type} [CommRing T] (f : B →+* T) :
    LieHerMat b M f (f.comp βB) ↔ lieIdeal b βB M ⊔ K₂ ≤ RingHom.ker f := by
  constructor
  · intro h
    obtain ⟨hL, hR⟩ := h T (RingHom.id T)
    have hJ : lieIdeal b βB M ≤ RingHom.ker f := (GlobalTheory.T.kottwitzLieConditionModule_iff_ideal_le_ker _ _ _ b _ βB n M T f).1 hL
    exact sup_le hJ ((hK₂ T f hJ).1 hR)
  · intro hK T' _ g
    have hker : RingHom.ker f ≤ RingHom.ker (g.comp f) := fun x hx => by
      rw [RingHom.mem_ker] at hx ⊢
      rw [RingHom.comp_apply, hx, map_zero]
    have hJ : lieIdeal b βB M ≤ RingHom.ker (g.comp f) := le_sup_left.trans (hK.trans hker)
    have h2 : K₂ ≤ RingHom.ker (g.comp f) := le_sup_right.trans (hK.trans hker)
    exact ⟨(GlobalTheory.T.kottwitzLieConditionModule_iff_ideal_le_ker _ _ _ b _ βB n M T' (g.comp f)).2 hJ, (hK₂ T' (g.comp f) hJ).2 h2⟩

theorem lieHer_ideal : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (S : Scheme.{0})
  (s : S ⟶ Sp R) (A : Over S) [GrpObj A] [IsCommMonObj A], Smooth A.hom → ∀ (act : OActN D.O A) (z : S),
  ∃ (U : S.Opens) (hU : IsAffineOpen U), z ∈ U ∧ ∃ K : Ideal Γ(S, U),
    ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R') (β : R →+* R'), spMap f ≫ hU.fromSpec ≫ s = spMap β →
      (LieHer b act β (spMap f ≫ hU.fromSpec) ↔ K ≤ RingHom.ker f) := by
  intro p _ D R _ b S s A _ _ hA act z
  obtain ⟨U, hU, hz, n, M, hM⟩ := GlobalTheory.T.exists_affine_nbhd_lie_matrix_smooth_comm_group (𝓞 D.F) S A hA (act.toF D) z
  obtain ⟨βB, hβB⟩ := exists_baseMap s hU
  obtain ⟨K₂, hK₂⟩ := GlobalTheory.T.exists_ideal_geometric_rank_iff_of_lie_condition p D R b Γ(S, U) βB n M
  refine ⟨U, hU, hz, lieIdeal b βB M ⊔ K₂, fun R' _ f β hc => ?_⟩
  obtain rfl := hβB R' f β hc
  rw [lieHer_iff_mat b act hU M hM f]
  exact lieHerMat_iff_le b βB M K₂ hK₂ f

end GlobalTheory.UPel.HT.LieLin
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical Topology

noncomputable section

namespace GlobalTheory.WeilLevel

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem eventually_invariant {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] {Φ : M → ℂ}
    (h1 : IsLocallyConstant Φ) (h2 : HasCompactSupport Φ) : ∀ᶠ u in 𝓝 (0 : M), ∀ x, Φ (x + u) = Φ x := by
  have h : ∀ᶠ u in 𝓝 (0 : M), ∀ x ∈ tsupport Φ, Φ (x + u) = Φ x ∧ Φ (x - u) = Φ x := by
    apply h2.isCompact.eventually_forall_of_forall_eventually
    intro x _
    have a1 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 + z.1 by fun_prop)).eventually_eq (0, x)
    have a2 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 - z.1 by fun_prop)).eventually_eq (0, x)
    have a3 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 by fun_prop)).eventually_eq (0, x)
    filter_upwards [a1, a2, a3] with z b1 b2 b3
    simp only [Function.comp, add_zero, sub_zero] at b1 b2 b3
    exact ⟨b1.trans b3.symm, b2.trans b3.symm⟩
  filter_upwards [h] with u hu x
  by_cases hx : x ∈ tsupport Φ
  · exact (hu x hx).1
  · by_cases hx' : x + u ∈ tsupport Φ
    · have := (hu _ hx').2
      rw [add_sub_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

theorem Bd_half_f (u y : Fin N → Af F) : Bd (Af F) (half F N) u y = u ⬝ᵥ y := by
  simp [Bd, half, dotProduct]

theorem annih_basis (hF : IsTotallyReal F) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) :
    (∀ K : Set (Fin N → Af F), IsCompact K → {y : Fin N → Af F | ∀ u ∈ K, ψ (pairA F 0 (u ⬝ᵥ y)) = 1} ∈ 𝓝 0) ∧
    ∀ U ∈ 𝓝 (0 : Fin N → Af F), ∃ L : AddSubgroup (Af F), IsOpen (L : Set (Af F)) ∧ IsCompact (L : Set (Af F)) ∧
      ∀ u : Fin N → Af F, (∀ l, u l ∈ L) → u ∈ U := by
  obtain ⟨lam, ν, hc⟩ := ctx_exists F hF ψ hψ N (half F N) (fun l => half_ne_zero l)
  obtain ⟨-, h2, h3⟩ := GlobalTheory.T.finiteAdeleVector_annihilators_compact_open_basis F N ψ lam ν (half F N) hc
  refine ⟨fun K hK => ?_, h3⟩
  have := h2 K hK
  simpa only [Bd_half_f] using this

def levelSub (L : AddSubgroup (Af F)) : AddSubgroup (VA F N) where
  carrier := {u | ∀ l, sndA F (u.1 l) ∈ L ∧ sndA F (u.2 l) ∈ L}
  zero_mem' := fun l => by simp
  add_mem' := fun ha hb l => by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add (f := _)]
    exact ⟨L.add_mem (ha l).1 (hb l).1, L.add_mem (ha l).2 (hb l).2⟩
  neg_mem' := fun ha l => by
    simp only [Prod.fst_neg, Prod.snd_neg, Pi.neg_apply, map_neg]
    exact ⟨L.neg_mem (ha l).1, L.neg_mem (ha l).2⟩

theorem isOpen_levelSub {L : AddSubgroup (Af F)} (hL : IsOpen (L : Set (Af F))) :
    IsOpen (levelSub (N := N) L : Set (VA F N)) := by
  have hs : Continuous fun z : AF F => sndA F z := continuous_snd
  have e : (levelSub (N := N) L : Set (VA F N)) =
      ⋂ l, ((fun u : VA F N => sndA F (u.1 l)) ⁻¹' L ∩ (fun u : VA F N => sndA F (u.2 l)) ⁻¹' L) := by
    ext u; simp [levelSub]
  rw [e]
  refine isOpen_iInter_of_finite fun l => IsOpen.inter ?_ ?_
  · exact hL.preimage (hs.comp ((continuous_apply l).comp continuous_fst))
  · exact hL.preimage (hs.comp ((continuous_apply l).comp continuous_snd))

end GlobalTheory.WeilLevel

namespace GlobalTheory.WeilLevel

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem adele_ext {z z' : AF F} (h1 : fstA F z = fstA F z') (h2 : sndA F z = sndA F z') : z = z' := Prod.ext h1 h2

theorem pure_level [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (hF : IsTotallyReal F) (hψ : IsCharAF F ψ)
    (f : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ) (g : (Fin N → Af F) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin N → Af F)) :
    ∃ U : AddSubgroup (VA F N), IsOpen (U : Set (VA F N)) ∧ ∀ u ∈ U, inf u.1 = 0 → inf u.2 = 0 →
      GlobalTheory.WeilM.schr ψ u (GlobalTheory.WeilM.pureA F f g) = GlobalTheory.WeilM.pureA F f g := by
  obtain ⟨hann, hbas⟩ := annih_basis (N := N) hF ψ hψ
  have hV := eventually_invariant hg.1 hg.2
  obtain ⟨L0, hL0o, hL0c, hL0V⟩ := hbas _ hV
  set c : Af F := algebraMap F (Af F) (1 / 2)
  have hK2 : IsCompact ((fun a : Fin N → Af F => c • a) '' {a | ∀ l, a l ∈ L0}) := by
    have : IsCompact {a : Fin N → Af F | ∀ l, a l ∈ L0} := by
      have := isCompact_univ_pi (fun _ : Fin N => hL0c)
      simpa [Set.pi] using this
    exact this.image (continuous_const_smul c)
  have hA1 := hann _ hg.2.isCompact
  have hA2 := hann _ hK2
  obtain ⟨L1, hL1o, -, hL1⟩ := hbas _ (Filter.inter_mem (Filter.inter_mem hV hA1) hA2)
  refine ⟨levelSub (L0 ⊓ L1), isOpen_levelSub (by rw [AddSubgroup.coe_inf]; exact hL0o.inter hL1o),
    fun u hu h1 h2 => ?_⟩
  set a : Fin N → Af F := fun l => sndA F (u.1 l)
  set b : Fin N → Af F := fun l => sndA F (u.2 l)
  have ha0 : ∀ l, a l ∈ L0 := fun l => (AddSubgroup.mem_inf.mp (hu l).1).1
  have ha1 : ∀ l, a l ∈ L1 := fun l => (AddSubgroup.mem_inf.mp (hu l).1).2
  have hb1 : ∀ l, b l ∈ L1 := fun l => (AddSubgroup.mem_inf.mp (hu l).2).2
  obtain ⟨⟨hVa, -⟩, -⟩ := hL1 a ha1
  obtain ⟨⟨-, hAb⟩, hA2b⟩ := hL1 b hb1
  have i1 : ∀ l, fstA F (u.1 l) = 0 := fun l => congrFun h1 l
  have i2 : ∀ l, fstA F (u.2 l) = 0 := fun l => congrFun h2 l
  funext x
  set xf : Fin N → Af F := fun i => (x i).2
  have ex : (fun i => ((x + u.1) i).2) = xf + a := by
    funext i; rfl
  have ex' : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + u.1) i).1) =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 := by
    funext i
    have : ((x + u.1) i).1 = (x i).1 := by
      show (x i).1 + (u.1 i).1 = (x i).1
      rw [show (u.1 i).1 = fstA F (u.1 i) from rfl, i1 i, add_zero]
    rw [this]
  simp only [GlobalTheory.WeilM.schr, GlobalTheory.WeilM.pureA]
  rw [ex, ex', hVa xf]
  by_cases hg0 : g xf = 0
  · rw [hg0]; simp
  have hxK : xf ∈ tsupport g := subset_tsupport g hg0
  have e : x ⬝ᵥ u.2 + ⅟(2 : AF F) * (u.1 ⬝ᵥ u.2) = pairA F 0 (xf ⬝ᵥ b) + pairA F 0 ((c • a) ⬝ᵥ b) := by
    apply adele_ext
    · simp only [map_add (f := _), map_mul]
      rw [show fstA F (x ⬝ᵥ u.2) = (fstA F).toRingHom (x ⬝ᵥ u.2) from rfl,
        show fstA F (u.1 ⬝ᵥ u.2) = (fstA F).toRingHom (u.1 ⬝ᵥ u.2) from rfl, RingHom.map_dotProduct, RingHom.map_dotProduct]
      have : (fstA F).toRingHom ∘ u.2 = 0 := funext i2
      rw [this, dotProduct_zero, dotProduct_zero, mul_zero, add_zero]
      rw [show ∀ p, fstA F (pairA F 0 p) = 0 from fun _ => rfl, show ∀ p, fstA F (pairA F 0 p) = 0 from fun _ => rfl, add_zero]
    · simp only [map_add (f := _), map_mul]
      rw [show sndA F (x ⬝ᵥ u.2) = (sndA F).toRingHom (x ⬝ᵥ u.2) from rfl,
        show sndA F (u.1 ⬝ᵥ u.2) = (sndA F).toRingHom (u.1 ⬝ᵥ u.2) from rfl, RingHom.map_dotProduct, RingHom.map_dotProduct,
        invOf_two_eq, AlgHom.commutes, smul_dotProduct, smul_eq_mul]
      rw [show ∀ p, sndA F (pairA F 0 p) = p from fun _ => rfl, show ∀ p, sndA F (pairA F 0 p) = p from fun _ => rfl]
      rfl
  rw [e, AddChar.map_add_eq_mul, hAb _ hxK, hA2b _ ⟨a, ha0, rfl⟩]
  ring

end GlobalTheory.WeilLevel

namespace GlobalTheory.WeilLevel

theorem schA_level : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ),
    IsTotallyReal F → IsCharAF F ψ → ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), ∃ U : AddSubgroup (VA F N),
      IsOpen (U : Set (VA F N)) ∧ ∀ u ∈ U, inf u.1 = 0 → inf u.2 = 0 → GlobalTheory.WeilM.schr ψ u Φ = Φ := by
  intro F _ _ N _ ψ hF hψ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact pure_level ψ hF hψ f g hg
  | zero =>
    exact ⟨⊤, isOpen_univ, fun u _ _ _ => by funext x; simp [GlobalTheory.WeilM.schr]⟩
  | add Φ Φ' _ _ h h' =>
    obtain ⟨U, hU, hUΦ⟩ := h
    obtain ⟨U', hU', hUΦ'⟩ := h'
    refine ⟨U ⊓ U', by rw [AddSubgroup.coe_inf]; exact hU.inter hU', fun u hu h1 h2 => ?_⟩
    funext x
    have e1 := congrFun (hUΦ u (AddSubgroup.mem_inf.mp hu).1 h1 h2) x
    have e2 := congrFun (hUΦ' u (AddSubgroup.mem_inf.mp hu).2 h1 h2) x
    simp only [GlobalTheory.WeilM.schr, Pi.add_apply] at e1 e2 ⊢
    rw [mul_add, e1, e2]
  | smul c Φ _ h =>
    obtain ⟨U, hU, hUΦ⟩ := h
    refine ⟨U, hU, fun u hu h1 h2 => ?_⟩
    funext x
    have e1 := congrFun (hUΦ u hu h1 h2) x
    simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul] at e1 ⊢
    rw [mul_left_comm, e1]

end GlobalTheory.WeilLevel

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.ThetaDeriv

theorem decay_majorant {F : Type} [Field F] [NumberField F] {N : ℕ} (hF : IsTotallyReal F)
    {Φ : (Fin N → AF F) → ℂ} (hΦ : Decay Φ) (ω : Set (Fin N → AF F)) (hω : IsCompact ω) :
    ∃ C : ℝ, ∃ c : (Fin N → F) → ℝ, Summable c ∧ (∀ ξ, 0 ≤ c ξ) ∧
      ∀ ξ, ∀ y ∈ ω, ‖Φ (rat ξ + y)‖ ≤ C * c ξ := by
  obtain ⟨-, ⟨K, hK, hKz⟩, hdec⟩ := hΦ
  obtain ⟨k, hk⟩ := GlobalTheory.SumMaj.summable_majorant F N hF K hK
  obtain ⟨C, hC⟩ := hdec k
  have hC0 : 0 ≤ C :=
    le_trans (mul_nonneg (norm_nonneg _) (pow_nonneg (by linarith [GlobalTheory.SumMaj.sz_nonneg (0 : Fin N → AF F)]) k))
      (hC 0)
  obtain ⟨c, hcs, hc0, hcb⟩ := hk ω hω
  refine ⟨C, c, hcs, hc0, fun ξ y hy => ?_⟩
  by_cases hmem : fin (rat ξ + y) ∈ K
  · have h1 := hcb ξ y hy hmem
    have h2 := hC (rat ξ + y)
    calc ‖Φ (rat ξ + y)‖ = ‖Φ (rat ξ + y)‖ * 1 := (mul_one _).symm
      _ ≤ ‖Φ (rat ξ + y)‖ * (c ξ * (1 + sz (rat ξ + y)) ^ k) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = c ξ * (‖Φ (rat ξ + y)‖ * (1 + sz (rat ξ + y)) ^ k) := by ring
      _ ≤ c ξ * C := mul_le_mul_of_nonneg_left h2 (hc0 ξ)
      _ = C * c ξ := mul_comm _ _
  · rw [hKz _ hmem, norm_zero]
    exact mul_nonneg hC0 (hc0 ξ)

variable {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)]

theorem schr_line_add (hF : IsTotallyReal F) (ψ : AddChar (AF F) ℂ) {M : ℝ →+ VA F N} (hM : IsRealLine M)
    (t h : ℝ) (Φ : (Fin N → AF F) → ℂ) :
    GlobalTheory.WeilM.schr ψ (M (t + h)) Φ = GlobalTheory.WeilM.schr ψ (M t) (GlobalTheory.WeilM.schr ψ (M h) Φ) := by
  rw [schr_schr, GlobalTheory.T.adelicSymplecticForm_realOneParamLine_eq_zero F N hF M hM t h, mul_zero, AddChar.map_zero_eq_one, one_smul, map_add (f := _)]

theorem exists_deriv_schr (hF : IsTotallyReal F) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ)
    {M : ℝ →+ VA F N} (hM : IsRealLine M) {Φ : (Fin N → AF F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin N)) :
    ∃ Φ' ∈ GlobalTheory.WeilM.schA F (Fin N), ∀ z, HasDerivAt (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) Φ z) (Φ' z) 0 := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨f', hf'⟩ := GlobalTheory.T.hasDerivAt_schrodingerLine_pureTensor_zero F N ψ hF hψ M hM f g hg
    exact ⟨_, Submodule.subset_span ⟨f', g, hg, rfl⟩, hf'⟩
  | zero =>
    refine ⟨0, zero_mem _, fun z => ?_⟩
    have e : (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) (0 : (Fin N → AF F) → ℂ) z) = fun _ => 0 := by
      funext s; simp [GlobalTheory.WeilM.schr]
    rw [e]
    exact hasDerivAt_const 0 0
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨Φ', h1m, h1d⟩ := h1
    obtain ⟨Ψ', h2m, h2d⟩ := h2
    refine ⟨Φ' + Ψ', add_mem h1m h2m, fun z => ?_⟩
    have e : (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) (Φ + Ψ) z) =
        fun s => GlobalTheory.WeilM.schr ψ (M s) Φ z + GlobalTheory.WeilM.schr ψ (M s) Ψ z := by
      funext s; simp [GlobalTheory.WeilM.schr, mul_add]
    rw [e]
    exact (h1d z).add (h2d z)
  | smul c Φ _ h =>
    obtain ⟨Φ', hm, hd⟩ := h
    refine ⟨c • Φ', Submodule.smul_mem _ c hm, fun z => ?_⟩
    have e : (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) (c • Φ) z) = fun s => c * GlobalTheory.WeilM.schr ψ (M s) Φ z := by
      funext s; simp [GlobalTheory.WeilM.schr]; ring
    rw [e]
    exact (hd z).const_mul c

theorem hasDerivAt_schr (hF : IsTotallyReal F) (ψ : AddChar (AF F) ℂ) {M : ℝ →+ VA F N} (hM : IsRealLine M)
    {Φ Φ' : (Fin N → AF F) → ℂ} (hd : ∀ z, HasDerivAt (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) Φ z) (Φ' z) 0)
    (z : Fin N → AF F) (t : ℝ) :
    HasDerivAt (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) Φ z) (GlobalTheory.WeilM.schr ψ (M t) Φ' z) t := by
  have h1 : HasDerivAt (fun h : ℝ => GlobalTheory.WeilM.schr ψ (M (t + h)) Φ z) (GlobalTheory.WeilM.schr ψ (M t) Φ' z) (t - t) := by
    have e : (fun h : ℝ => GlobalTheory.WeilM.schr ψ (M (t + h)) Φ z) = fun h =>
        ψ (z ⬝ᵥ (M t).2 + ⅟(2 : AF F) * ((M t).1 ⬝ᵥ (M t).2)) * GlobalTheory.WeilM.schr ψ (M h) Φ (z + (M t).1) := by
      funext h
      rw [schr_line_add hF ψ hM]
      rfl
    rw [e, sub_self]
    exact (hd (z + (M t).1)).const_mul _
  have h2 := h1.comp_sub_const t t
  simpa only [add_sub_cancel] using h2

end GlobalTheory.ThetaDeriv


open GlobalTheory.ThetaDeriv in
theorem GlobalTheory.ThetaTransform.hasDerivAt_heisV_line : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)]
    (ψ : AddChar (AF F) ℂ), IsTotallyReal F → IsCharAF F ψ → ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N),
    ∀ M : ℝ →+ VA F N, IsRealLine M → ∃ Φ' ∈ GlobalTheory.WeilM.schA F (Fin N),
      ∀ w, HasDerivAt (fun t : ℝ => heisV ψ (M t) (thV ψ Φ) w) (thV ψ Φ' w) 0 := by
  intro F _ _ N _ ψ hF hψ Φ hΦ M hM
  obtain ⟨Φ', hΦ'm, hΦ'd⟩ := exists_deriv_schr hF ψ hψ hM hΦ
  refine ⟨Φ', hΦ'm, fun w => ?_⟩
  have hnorm : ∀ x, ‖ψ x‖ = 1 := hψ.2.1
  have hM0 : M 0 = 0 := map_zero M
  set ω : Set (Fin N → AF F) := (fun s : ℝ => w.1 + (M s).1) '' Set.Icc (-1) 1 with hω
  have hωc : IsCompact ω := isCompact_Icc.image (continuous_const.add (continuous_fst.comp hM.1))
  obtain ⟨C, c, hcs, hc0, hcb⟩ := decay_majorant hF (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ' hΦ'm) ω hωc
  obtain ⟨C₀, c₀, hcs₀, hc0₀, hcb₀⟩ := decay_majorant hF (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ hΦ) {w.1} isCompact_singleton
  set ph : (Fin N → F) → ℂ := fun ξ => ψ (rat ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) with hph
  have e : (fun t : ℝ => heisV ψ (M t) (thV ψ Φ) w) =
      fun t => ∑' ξ : Fin N → F, ph ξ * GlobalTheory.WeilM.schr ψ (M t) Φ (rat ξ + w.1) := by
    funext t
    rw [← thV_schr]
    rfl
  have hv : thV ψ Φ' w = ∑' ξ : Fin N → F, ph ξ * GlobalTheory.WeilM.schr ψ (M 0) Φ' (rat ξ + w.1) := by
    rw [hM0]
    refine tsum_congr fun ξ => ?_
    simp [ph, GlobalTheory.WeilM.schr]
    rfl
  rw [e, hv]
  have hmem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine hasDerivAt_tsum_of_isPreconnected (hcs.mul_left C) isOpen_Ioo isPreconnected_Ioo
    (fun ξ t _ => (hasDerivAt_schr hF ψ hM hΦ'd (rat ξ + w.1) t).const_mul (ph ξ)) (fun ξ t ht => ?_) hmem ?_ hmem
  · have hy : w.1 + (M t).1 ∈ ω := ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
    have := hcb ξ _ hy
    simp only [ph, GlobalTheory.WeilM.schr, norm_mul, hnorm, one_mul]
    simpa [add_assoc] using this
  · refine Summable.of_norm_bounded (hcs₀.mul_left C₀) fun ξ => ?_
    have := hcb₀ ξ w.1 rfl
    simpa [hM0, GlobalTheory.WeilM.schr, ph, norm_mul, hnorm] using this
end
end
