module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NilpotentHeckeOperators.NilKill
import GroundTheory.LocalFields.UnramifiedHensel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostOk
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle017
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IrrOpen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPtOfIsPtHom
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Connected.Separation
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart

@[expose] public section

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.Th
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem relOf_act {T W κ : Type} [CommGroup T] [AddCommGroup W] [Module ℂ W]
    (θ : T →* (Module.End ℂ W)ˣ) (t : κ → T) :
    ∃ act : MvPolynomial κ ℂ →ₐ[ℂ] Module.End ℂ W, ∀ a, act (MvPolynomial.X a) = θ (t a) :=
  ⟨(MonoidAlgebra.lift ℂ (Module.End ℂ W) T ((Units.coeHom _).comp θ)).comp
    (MvPolynomial.aeval fun a => MonoidAlgebra.single (t a) 1), fun a => by simp⟩
private theorem relOf_int {R W W' κ S : Type} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module ℂ W']
    [CommRing S] [Algebra ℂ S] (c : R →+* ℂ) (v : κ → S)
    (act : MvPolynomial κ R →ₐ[R] Module.End R W) (act' : S →ₐ[ℂ] Module.End ℂ W') (g : W →+ W')
    (hg : ∀ r m, g (r • m) = c r • g m)
    (h : ∀ a m, act' (v a) (g m) = g (act (MvPolynomial.X a) m)) (F : MvPolynomial κ R) (m : W) :
    act' (MvPolynomial.eval₂Hom ((algebraMap ℂ S).comp c) v F) (g m) = g (act F m) := by
  induction F using MvPolynomial.induction_on generalizing m with
  | C r =>
    rw [MvPolynomial.eval₂Hom_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, RingHom.comp_apply, AlgHom.commutes]
    simp [hg]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, map_add (f := _), hp, hq]
  | mul_X p a hp =>
    rw [map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, MvPolynomial.eval₂Hom_X', h, hp]
private theorem relOf_uy {R W W' ι S : Type} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module ℂ W']
    [CommRing S] [Algebra R S] (c : R →+* ℂ) (act : S →ₐ[R] Module.End R W)
    (act' : MvPolynomial (ι ⊕ ι) ℂ →ₐ[ℂ] Module.End ℂ W') (g : W →+ W') (hg : ∀ r m, g (r • m) = c r • g m)
    (ψ : MvPolynomial (ι ⊕ ι) R →ₐ[R] S) (N : ℕ) (e : ι → ℕ) (E : ι ⊕ ι → Module.End R W)
    (hu : ∀ i, act (ψ (MvPolynomial.X (.inl i))) = (N : R) ^ e i • E (.inl i))
    (hy : ∀ i, act (1 + ψ (MvPolynomial.X (.inr i))) = E (.inr i))
    (h : ∀ a m, act' (MvPolynomial.X a) (g m) = g (E a m)) (F : MvPolynomial (ι ⊕ ι) R) (k : ℕ)
    (h0 : act' (MvPolynomial.eval₂Hom ((algebraMap ℂ (MvPolynomial (ι ⊕ ι) ℂ)).comp c)
      (Sum.elim (fun i => ((N : ℂ) ^ e i) • MvPolynomial.X (.inl i)) fun i => MvPolynomial.X (.inr i) - 1) F ^ k) = 0) (m : W) :
    g (act (ψ F ^ k) m) = 0 := by
  have h1 := relOf_int c (Sum.elim (fun i => ((N : ℂ) ^ e i) • MvPolynomial.X (.inl i)) fun i => MvPolynomial.X (.inr i) - 1)
    (act.comp ψ) act' g hg (fun a m => by
      rw [AlgHom.comp_apply]
      rcases a with i | i
      · rw [Sum.elim_inl, hu, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, hg, map_pow, map_natCast, h]
      · have e := hy i
        rw [map_add (f := _), map_one] at e
        rw [Sum.elim_inr, eq_sub_of_add_eq' e, map_sub, map_one, LinearMap.sub_apply, LinearMap.sub_apply, map_sub, h]
        rfl) (F ^ k) m
  rw [map_pow, h0, AlgHom.comp_apply, map_pow] at h1
  exact h1.symm
theorem UpperTheory.V.Th.relOfX_alt :
    _root_.UpperTheory.V.Pa.LocPAlt → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ) (b : TWBase (pairOf B.u) J Empty D) (V : s.Lev) (h : (globOf r V).Hom (globOf r V0)) (q : ℕ) (w : Fin q → Plc L) (A : LevMod b h w) (x δ : ∀ j, ((w j).adicCompletion L)ˣ), (∀ j, ((l : ℕ) : 𝓞 L) ∉ (w j).asIdeal) → (∀ j, IsUnif (x j)) → (∀ j, IsGenMod _ (ellC l _) (δ j)) → ∀ (T : ThData l A.ρ x δ) (ι : Qbar l ≃+* ℂ), (∀ m : A.P, (∀ y : _root_.UpperTheory.V.Pa.LevPtAlt A ι, y.sp m = 0) → m = 0) → ∀ (j : Fin q) (F : MvPolynomial (Fin n ⊕ Fin n) A.R), (∀ (y : _root_.UpperTheory.V.Pa.LevPtAlt A ι) θ, IsTheta (y.σ j).ρ (ellC l _) θ → ∀ χ : (Fin n → ((w j).adicCompletion L)ˣ) →* ℂˣ, (⨅ t, Module.End.maxGenEigenspace (θ t).val (χ t : ℂ)) ≠ ⊥ → ∀ (S : Type) [CommRing S] [Algebra ℂ S] (U : Fin n → S), (∀ i : Fin n, (U i - algebraMap ℂ S ((qj w j : ℂ) ^ (i : ℕ) * (χ (Pi.mulSingle i (x j)) : ℂ))) ^ n.factorial = 0) → MvPolynomial.eval₂ ((algebraMap ℂ S).comp (ι.toRingHom.comp y.θ)) (Sum.elim U fun i => algebraMap ℂ S (χ (Pi.mulSingle i (δ j)) : ℂ) - 1) F = 0) → T.act1 (MvPolynomial.rename (Sum.map (fun i => (j, i)) fun i => (j, i)) F) = 0 := by
  intro hP l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r B J D b V h q w A x δ _ _ hδ T ι hsep j F hF
  rw [← pow_one (MvPolynomial.rename _ F)]
  refine LinearMap.ext fun m => Subtype.ext (hsep _ fun y => ?_)
  obtain ⟨Θ, hΘ⟩ := thetaQ L n q w ℂ y.Y y.π (fun _ => ellC l _) fun j =>
    (Nat.cast_ne_zero.2 (Nat.card_pos (α := 𝓀[(w j).adicCompletion L])).ne').isUnit
  let t : Fin n ⊕ Fin n → Fin n → ((w j).adicCompletion L)ˣ :=
    Sum.elim (fun i => Pi.mulSingle i (x j)) fun i => Pi.mulSingle i (δ j)
  obtain ⟨act, hact⟩ := relOf_act (Θ j) t
  let c : A.R →+* ℂ := ι.toRingHom.comp y.θ
  let v : Fin n ⊕ Fin n → MvPolynomial (Fin n ⊕ Fin n) ℂ :=
    Sum.elim (fun i => ((qj w j : ℂ) ^ (i : ℕ)) • MvPolynomial.X (.inl i)) fun i => MvPolynomial.X (.inr i) - 1
  let g : fixd A.ρ (UC n w fun _ => ellC l _) →+ fixd y.π (UC n w fun _ => ellC l _) :=
    { toFun := fun m => ⟨y.sp m, fun u hu => by rw [← y.sp_act, m.2 u hu]⟩
      map_zero' := Subtype.ext (map_zero y.sp)
      map_add' := fun a a' => Subtype.ext (map_add y.sp _ _) }
  have hg : ∀ (r : A.R) m, g (r • m) = c r • g m := fun r m => Subtype.ext (y.sp_smul r m)
  have hΘg : ∀ t m, (Θ j t).val (g m) = g ((T.Θ1 j t).val m) := fun t m =>
    Subtype.ext (thetaMap L n q w A.R A.P ℂ y.Y A.ρ y.π _ T.Θ1 Θ T.h1 hΘ y.sp y.sp_act j t m (g m) rfl)
  have h0 := nilKillX hP.gl hP.bz L n q w y.Y y.π _ Θ hΘ j (y.σ j) (y.iso j) _ t (fun i => ⟨_, _, i, hδ j, rfl⟩) act hact
    (MvPolynomial.eval₂Hom ((algebraMap ℂ _).comp c) v F) (fun θ hθ χ hχ S _ _ φ h1 h2 => by
      refine Eq.trans ?_ (hF y θ hθ χ hχ S (fun i => ((qj w j : ℂ) ^ (i : ℕ)) • φ (MvPolynomial.X (.inl i))) fun i => ?_)
      · rw [MvPolynomial.coe_eval₂Hom]
        refine (MvPolynomial.eval₂_comp_left φ.toRingHom _ _ _).trans ?_
        congr 1
        · ext r
          exact φ.commutes _
        · funext a
          rcases a with i | i
          · exact map_smul φ _ _
          · exact (map_sub φ _ _).trans (by rw [h2, map_one]; rfl)
      · rw [map_mul, Algebra.smul_def, ← mul_sub, mul_pow]
        exact mul_eq_zero_of_right _ (h1 i))
  rw [← pow_one (MvPolynomial.eval₂Hom _ v F)] at h0
  exact congrArg Subtype.val (relOf_uy c T.act1 act g hg
    (MvPolynomial.rename (Sum.map (fun i => (j, i)) fun i => (j, i))) (qj w j) (fun i => (i : ℕ))
    (fun a => (T.Θ1 j (t a)).val)
    (fun i => by rw [MvPolynomial.rename_X]; exact T.act_uVariable_eq_pow j i)
    (fun i => by rw [MvPolynomial.rename_X]; exact T.act_yVariable j i)
    (fun a m => by rw [hact]; exact hΘg _ m) F _ h0 m)
end
end

section




section
open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia
private theorem totDisc_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  refine Set.eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponent, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  by_contra hx
  have hx' : x ∉ N := fun h => hx ((QuotientGroup.eq_one_iff x).2 h)
  have ho : IsOpen {g : G | g * x ∉ N} := hN.isOpen_compl.preimage (continuous_mul_const x)
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')
  let V : Subgroup (G ⧸ N) := U.toSubgroup.map (QuotientGroup.mk' N)
  have hVo : IsOpen (V : Set (G ⧸ N)) := QuotientGroup.isOpenMap_coe _ U.isOpen'
  have hV : IsClopen (V : Set (G ⧸ N)) := ⟨V.isClosed_of_isOpen hVo, hVo⟩
  obtain ⟨u, hu, hux⟩ := hV.connectedComponent_subset V.one_mem hy
  exact hU (U.toSubgroup.inv_mem hu) (QuotientGroup.eq.1 hux)
theorem UpperTheory.V.UnitaryThreeInertia.unitary_lift_of_reduced_core :
    _root_.UpperTheory.V.Aut.ThmS6Core_s → _root_.UpperTheory.V.Aut.ThmS6_s := by
  intro h K _ _ _ hK Ω _ _ _ l _ ι c N _ e ψ o₁ hd S A F hF
  obtain ⟨g₁, hg, H⟩ := h K hK Ω l ι c N e ψ o₁ hd S A F hF
  refine ⟨g₁, hg, fun R _ _ _ u hu => ⟨(H R u hu).1, fun ξ r h1 h2 => ?_⟩⟩
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI hcl := isClosed_NS Ω (S : Set Pl)
  haveI : CompactSpace (Gam Ω S) := inferInstance
  haveI : T2Space (Gam Ω S) := inferInstance
  haveI : TotallyDisconnectedSpace (Gam Ω S) := totDisc_quot _ hcl
  have hOk := hostFrame_ok Ω c e ψ o₁ hd S A F hF
  have hz : F.IsCharZeroPt g₁ r := isCharZeroPt_of_isPtHom (l := l) F hOk g₁ hg u hu (H R u hu).1 ξ r h1
  exact ⟨matIrr_open Ω c e ψ o₁ hd S A F hF g₁ hg r hz h2, matIrr_cyc Ω c e ψ o₁ hd S A F hF g₁ hg r hz h2,
    (H R u hu).2 ξ r h1 h2⟩
end
end

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp
open UpperTheory.V.Af
open scoped Matrix
namespace UpperTheory.V.Af.NewformAutomorphy
private theorem ss_of_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (h : IsSSRep (tw r χ)) : IsSSRep r := by
  have key : ∀ W, IsInv (tw r χ) W ↔ IsInv r W := fun W => by
    constructor
    · intro h g v hv
      have := W.smul_mem ((χ g : k)⁻¹) (h g v hv)
      rwa [tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this
    · intro h g v hv
      rw [tw_val, Matrix.smul_mulVec]
      exact W.smul_mem _ (h g v hv)
  intro W hW
  obtain ⟨W', hW', hc⟩ := h W ((key W).2 hW)
  exact ⟨W', (key W').1 hW', hc⟩
private theorem ev_not_mem (N : ℕ) (hN : N ≠ 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ((N : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
  have h0 : Ideal.span {((N : ℕ) : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq, not_not] at hw
  exact Ideal.dvd_span_singleton.2 hw
private theorem normV_eq (w : HeightOneSpectrum (𝓞 ℚ)) : normV w = Ideal.absNorm w.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
private theorem scale_charpoly {k : Type} [Field k] (φ : k →+* ℂ) (M : Matrix (Fin 2) (Fin 2) k) (c : k) (hc : c ≠ 0)
    (B : Multiset ℂ) (h : (c • M).charpoly.map φ = (B.map fun b => X - C (φ c * b)).prod) :
    M.charpoly.map φ = (B.map fun b => X - C b).prod := by
  have hc' : φ c ≠ 0 := by simpa using hc
  have hcard : B.card = 2 := by
    have h1 := congrArg natDegree h
    rw [natDegree_map, Matrix.charpoly_natDegree_eq_dim] at h1
    have h2 := natDegree_multiset_prod_X_sub_C_eq_card (B.map (φ c * ·))
    rw [Multiset.map_map] at h2
    simp only [Function.comp_def, Multiset.card_map] at h2
    rw [h2] at h1
    simpa using h1.symm
  obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hcard
  rw [Matrix.charpoly_fin_two] at h ⊢
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_X,
    map_C, Matrix.trace_smul, Matrix.det_smul, smul_eq_mul, map_mul, map_pow, Fintype.card_fin] at h ⊢
  have e0 := congrArg (eval 0) h
  have e1 := congrArg (eval 1) h
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at e0 e1
  have hd : φ M.det = x * y := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hc')
    linear_combination e0
  have ht : φ M.trace = x + y := by
    apply mul_left_cancel₀ hc'
    linear_combination e0 - e1
  rw [hd, ht, C_add, C_mul]
  ring
end UpperTheory.V.Af.NewformAutomorphy
open UpperTheory.V.Af.NewformAutomorphy in
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
theorem UpperTheory.V.Af.newformAutR_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.NewformAutR := by
  intro P k hk f l hl Ω _ _ _ ι W j hf
  obtain ⟨π, hinf, hsat⟩ := P.newform k hk f (-j)
  refine ⟨π, fun v => ⟨_, hinf v, ?_, ?_⟩, ss_of_tw _ _ hf.1, ?_⟩
  · simp only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_singleton, Multiset.nodup_singleton, and_true]
    intro h
    have h1 : (k : ℂ) = 1 := by linear_combination h
    have h2 : k = 1 := by exact_mod_cast h1
    omega
  · intro z hz
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ⟨-j, by push_cast; ring⟩
    · exact ⟨1 - k - j, by push_cast; ring⟩
  · filter_upwards [hf.2, ev_not_mem l hl.out.ne_zero, ev_not_mem f.M f.pos.ne'] with w hw hwl hwM
    have hM : ¬ normV w ∣ f.M := by
      rintro ⟨c, hc⟩
      apply hwM
      rw [hc, Nat.cast_mul, normV_eq]
      exact w.asIdeal.mul_mem_right _ (Ideal.absNorm_mem _)
    obtain ⟨B, hB, hpoly⟩ := hsat w hM
    refine ⟨B, hB, fun A hA => ⟨fun s hs => ?_, fun σ hσ => ?_⟩⟩
    · have h1 := (hw A hA).1 s hs
      have h2 : cycZ ℚ Ω l s = 1 := by
        refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
        rw [cycZ_toZModPow_eq (v := w) hwl hA (q := 1) (fun x hx => by simpa using hs.2 x hx) n]
        simp
      have h3 : (cycBar ℚ Ω l ^ j) s = 1 := by
        rw [MonoidHom.zpow_apply, cycBar, MonoidHom.comp_apply, h2, map_one, one_zpow]
      apply Units.ext
      have h4 := congrArg Units.val h1
      rwa [tw_val, h3, Units.val_one, one_smul] at h4
    · have h1 := (hw A hA).2 σ hσ
      rw [tw_val, ← hpoly] at h1
      refine scale_charpoly ι.toRingHom _ _ (Units.ne_zero ((cycBar ℚ Ω l ^ j) σ⁻¹)) _ ?_
      rw [h1]
      have h2 : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
        change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
        rw [cycZ_of_isFrob hwl hA hσ, map_natCast, map_natCast]
      have h3 : ι.toRingHom (((cycBar ℚ Ω l ^ j) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (normV w : ℂ) ^ (-j) := by
        rw [MonoidHom.zpow_apply, map_inv, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h2, map_zpow₀,
          map_inv₀, map_natCast, inv_zpow']
      rw [h3]
end
end

section




section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.LocGL Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.NewformAutAtL
open Polynomial
private theorem ss_of_tw' {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (h : IsSSRep (tw r χ)) : IsSSRep r := by
  have key : ∀ W, IsInv (tw r χ) W ↔ IsInv r W := fun W => by
    constructor
    · intro h g v hv
      have := W.smul_mem ((χ g : k)⁻¹) (h g v hv)
      rwa [tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this
    · intro h g v hv
      rw [tw_val, Matrix.smul_mulVec]
      exact W.smul_mem _ (h g v hv)
  intro W hW
  obtain ⟨W', hW', hc⟩ := h W ((key W).2 hW)
  exact ⟨W', (key W').1 hW', hc⟩
private theorem ev_not_mem' (N : ℕ) (hN : N ≠ 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ((N : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
  have h0 : Ideal.span {((N : ℕ) : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq, not_not] at hw
  exact Ideal.dvd_span_singleton.2 hw
private theorem normV_eq' (w : HeightOneSpectrum (𝓞 ℚ)) : normV w = Ideal.absNorm w.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
private theorem normV_rat' {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    normV w = p := by
  have hN : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 ℚ)}) = p := by
    rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank]
    simp
  have hd : Ideal.absNorm w.asIdeal ∣ p :=
    hN ▸ Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hw)
  rw [normV_eq']
  refine ((Nat.dvd_prime hp).1 hd).resolve_left ?_
  rw [Ideal.absNorm_eq_one_iff]
  exact w.isPrime.ne_top
private theorem scale_charpoly' {k : Type} [Field k] (φ : k →+* ℂ) (M : Matrix (Fin 2) (Fin 2) k) (c : k) (hc : c ≠ 0)
    (B : Multiset ℂ) (h : (c • M).charpoly.map φ = (B.map fun b => X - C (φ c * b)).prod) :
    M.charpoly.map φ = (B.map fun b => X - C b).prod := by
  have hc' : φ c ≠ 0 := by simpa using hc
  have hcard : B.card = 2 := by
    have h1 := congrArg natDegree h
    rw [natDegree_map, Matrix.charpoly_natDegree_eq_dim] at h1
    have h2 := natDegree_multiset_prod_X_sub_C_eq_card (B.map (φ c * ·))
    rw [Multiset.map_map] at h2
    simp only [Function.comp_def, Multiset.card_map] at h2
    rw [h2] at h1
    simpa using h1.symm
  obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hcard
  rw [Matrix.charpoly_fin_two] at h ⊢
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_X,
    map_C, Matrix.trace_smul, Matrix.det_smul, smul_eq_mul, map_mul, map_pow, Fintype.card_fin] at h ⊢
  have e0 := congrArg (eval 0) h
  have e1 := congrArg (eval 1) h
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at e0 e1
  have hd : φ M.det = x * y := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hc')
    linear_combination e0
  have ht : φ M.trace = x + y := by
    apply mul_left_cancel₀ hc'
    linear_combination e0 - e1
  rw [hd, ht, C_add, C_mul]
  ring
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
theorem exists_cuspidal_satake_prod_eq_hecke_poly_of_not_dvd_level : _root_.UpperTheory.V.Af.Hypotheses' → ∀ (e : ℕ) (g : Newform (2 * e + 1)) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (V : G ℚ Ω →* GL (Fin 2) (Qbar l)), 1 ≤ e →
    g.Att ι (tw V (cycBar ℚ Ω l ^ (-(e : ℤ)))) → ¬ l ∣ g.M →
    ∃ π : TR.CuspSub ℚ 2, π.IsRegAlg ∧ AttR ι V π ∧ ∀ w : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal →
      ∃ B, π.HasSat w B ∧
        ((algSat 2 l B).map fun b => Polynomial.X - Polynomial.C ((l : ℂ) ^ e * b)).prod = g.heckePoly l := by
  intro P e g l hl Ω _ _ _ ι V he hf hlM
  have hk : 2 ≤ 2 * e + 1 := by omega
  obtain ⟨π, hinf, hsat⟩ := P.newform (2 * e + 1) hk g (e : ℤ)
  refine ⟨π, fun v => ⟨_, hinf v, ?_, ?_⟩, ⟨ss_of_tw' _ _ hf.1, ?_⟩, ?_⟩
  · simp only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_singleton, Multiset.nodup_singleton, and_true]
    intro h
    have h1 : ((2 * e + 1 : ℕ) : ℂ) = 1 := by linear_combination h
    have h2 : 2 * e + 1 = 1 := by exact_mod_cast h1
    omega
  · intro z hz
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ⟨(e : ℤ), by push_cast; ring⟩
    · exact ⟨1 - ((2 * e + 1 : ℕ) : ℤ) + e, by push_cast; ring⟩
  · filter_upwards [hf.2, ev_not_mem' l hl.out.ne_zero, ev_not_mem' g.M g.pos.ne'] with w hw hwl hwM
    have hM : ¬ normV w ∣ g.M := by
      rintro ⟨c, hc⟩
      apply hwM
      rw [hc, Nat.cast_mul, normV_eq']
      exact w.asIdeal.mul_mem_right _ (Ideal.absNorm_mem _)
    obtain ⟨B, hB, hpoly⟩ := hsat w hM
    refine ⟨B, hB, fun A hA => ⟨fun s hs => ?_, fun σ hσ => ?_⟩⟩
    · have h1 := (hw A hA).1 s hs
      have h2 : cycZ ℚ Ω l s = 1 := by
        refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
        rw [cycZ_toZModPow_eq (v := w) hwl hA (q := 1) (fun x hx => by simpa using hs.2 x hx) n]
        simp
      have h3 : (cycBar ℚ Ω l ^ (-(e : ℤ))) s = 1 := by
        rw [MonoidHom.zpow_apply, cycBar, MonoidHom.comp_apply, h2, map_one, one_zpow]
      apply Units.ext
      have h4 := congrArg Units.val h1
      rwa [tw_val, h3, Units.val_one, one_smul] at h4
    · have h1 := (hw A hA).2 σ hσ
      rw [tw_val, ← hpoly] at h1
      refine scale_charpoly' ι.toRingHom _ _ (Units.ne_zero ((cycBar ℚ Ω l ^ (-(e : ℤ))) σ⁻¹)) _ ?_
      rw [h1]
      have h2 : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
        change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
        rw [cycZ_of_isFrob hwl hA hσ, map_natCast, map_natCast]
      have h3 : ι.toRingHom (((cycBar ℚ Ω l ^ (-(e : ℤ))) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (normV w : ℂ) ^ (e : ℤ) := by
        rw [MonoidHom.zpow_apply, map_inv, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h2, map_zpow₀,
          map_inv₀, map_natCast, inv_zpow', neg_neg]
      rw [h3]
  · intro w hw
    have hn : normV w = l := normV_rat' hl.out w hw
    have hM : ¬ normV w ∣ g.M := hn ▸ hlM
    obtain ⟨B, hB, hpoly⟩ := hsat w hM
    refine ⟨B, hB, ?_⟩
    rw [hn] at hpoly
    simpa only [zpow_natCast] using hpoly
end GlobalTheory.NewformAutAtL
end
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.LocGL Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_cuspidal_attached_satake_eq_hecke_poly_of_not_dvd : _root_.UpperTheory.V.Af.Hypotheses' → ∀ (e : ℕ) (g : Newform (2 * e + 1)) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (V : G ℚ Ω →* GL (Fin 2) (Qbar l)), 1 ≤ e →
    g.Att ι (tw V (cycBar ℚ Ω l ^ (-(e : ℤ)))) → ¬ l ∣ g.M →
    ∃ π : TR.CuspSub ℚ 2, π.IsRegAlg ∧ AttR ι V π ∧ ∀ w : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal →
      ∃ B, π.HasSat w B ∧
        ((algSat 2 l B).map fun b => Polynomial.X - Polynomial.C ((l : ℂ) ^ e * b)).prod = g.heckePoly l := by
  first | exact @_root_.GlobalTheory.NewformAutAtL.exists_cuspidal_satake_prod_eq_hecke_poly_of_not_dvd_level | exact _root_.GlobalTheory.NewformAutAtL.exists_cuspidal_satake_prod_eq_hecke_poly_of_not_dvd_level | (intros; apply _root_.GlobalTheory.NewformAutAtL.exists_cuspidal_satake_prod_eq_hecke_poly_of_not_dvd_level <;> assumption)
end
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Af
section Rep
variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k}
end Rep
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {r r' : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)}
variable [IsAlgClosure F Ω]
abbrev _root_.UpperTheory.V.Af.Hypotheses'.exists_rec_ty : Prop := ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (P : _root_.UpperTheory.V.Af.Hypotheses') {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w),
    ∃ rc : IrrGL (k := w.adicCompletion F) → WD h, _root_.UpperTheory.Zero.LLC.IsRecT h rc
end UpperTheory.V.Af
end
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.Gal.SV
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
theorem ratioW_of_hasSat_alt [IsTotallyReal F] (_P : _root_.UpperTheory.V.Af.Hypotheses') {n : ℕ} {π : TR.CuspSub F n} {ι : Qbar l ≃+* ℂ} {r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)}
    {wt : ℤ} {HT : (F →+* Qbar l) → Multiset ℤ} (H : IsGalRS π ι r wt HT) {w : HeightOneSpectrum (𝓞 F)}
    (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) {A : ValuationSubring Ω} (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) {B : Multiset ℂˣ} (hB : π.HasSat w B) :
    UpperTheory.GalN.V.RatioW (wdOf h hl ι r) := H.ratio w hl A h (H.plain w B hB)
end UpperTheory.Gal.SV
end
end
end
