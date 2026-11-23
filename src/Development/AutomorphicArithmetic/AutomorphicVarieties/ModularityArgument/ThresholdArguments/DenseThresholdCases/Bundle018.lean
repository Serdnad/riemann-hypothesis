module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle546
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle547
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle362
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CharFil
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle003
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Matrix GlobalTheory.PRep GlobalTheory.CuspRep.LocEx
open GlobalTheory.CuspRep (SmIrr Af locGL pLoc finGL)
namespace UpperTheory.V.Af.RealLocalComponent
section Gen
variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V]
private def orb (κ : Representation ℂ K V) (x : V) : (K →₀ ℂ) →ₗ[ℂ] V := Finsupp.linearCombination ℂ fun k => κ k x
private theorem orb_comm (κ : Representation ℂ K V) (T : Module.End ℂ V) (hT : ∀ k x, T (κ k x) = κ k (T x)) (x : V)
    (c : K →₀ ℂ) : orb κ (T x) c = T (orb κ x c) := by

  simp only [orb, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, hT]
private theorem orb_act (κ : Representation ℂ K V) (x : V) (k : K) (c : K →₀ ℂ) :
    orb κ x (c.mapDomain (k * ·)) = κ k (orb κ x c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c c' h h' => rw [Finsupp.mapDomain_add, map_add (f := _), map_add (f := _), map_add (f := _), h, h']
  | single a b => simp [orb]
private def annPart (κ : Representation ℂ K V) (φ : V) : Submodule ℂ V where
  carrier := {x | ∀ c, orb κ φ c = 0 → orb κ x c = 0}
  add_mem' := fun {x y} hx hy c hc => by
    have : orb κ (x + y) c = orb κ x c + orb κ y c := by
      simp only [orb, Finsupp.linearCombination_apply, Finsupp.sum, map_add (f := _), smul_add, Finset.sum_add_distrib]
    rw [this, hx c hc, hy c hc, add_zero]
  zero_mem' := fun c _ => by simp [orb, Finsupp.linearCombination_apply, Finsupp.sum]
  smul_mem' := fun a x hx c hc => by
    have := orb_comm κ (a • (1 : Module.End ℂ V)) (fun k x => by simp) x c
    simpa [hx c hc] using this
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
private theorem exists_type (κ : Representation ℂ K V) (φ : V)
    (hφ : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => κ k φ))) :
    ∃ (d : ℕ) (ξ : K →* Matrix (Fin d) (Fin d) ℂ), ∀ x ∈ annPart κ φ, ∃ f : (Fin d → ℂ) →ₗ[ℂ] V,
      (∀ k v, f (ξ k *ᵥ v) = κ k (f v)) ∧ x ∈ LinearMap.range f ∧ ∀ v, ∃ c, f v = orb κ x c := by
  have hO : ∀ k, ∀ y ∈ LinearMap.range (orb κ φ), κ k y ∈ LinearMap.range (orb κ φ) := by
    rintro k _ ⟨c, rfl⟩
    exact ⟨_, orb_act κ φ k c⟩
  haveI : FiniteDimensional ℂ (LinearMap.range (orb κ φ)) := by
    rw [orb, Finsupp.range_linearCombination]; exact hφ
  let b := Module.finBasis ℂ (LinearMap.range (orb κ φ))
  obtain ⟨s, hs⟩ := (orb κ φ).rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict _)
  refine ⟨_, (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp (sub κ _ hO), fun x hx => ?_⟩
  have key : ∀ c, orb κ x (s ((orb κ φ).rangeRestrict c)) = orb κ x c := fun c => by
    rw [← sub_eq_zero, ← map_sub]
    refine hx _ ?_
    rw [map_sub, sub_eq_zero]
    exact congrArg Subtype.val (LinearMap.congr_fun hs ((orb κ φ).rangeRestrict c))
  refine ⟨orb κ x ∘ₗ s ∘ₗ b.equivFun.symm.toLinearMap, fun k v => ?_,
    ⟨b.equivFun ((orb κ φ).rangeRestrict (Finsupp.single 1 1)), ?_⟩, fun v => ⟨_, rfl⟩⟩
  · obtain ⟨y, rfl⟩ := b.equivFun.surjective v
    obtain ⟨c, rfl⟩ := (orb κ φ).surjective_rangeRestrict y
    have h1 : (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp (sub κ _ hO) k *ᵥ b.equivFun ((orb κ φ).rangeRestrict c) =
        b.equivFun ((orb κ φ).rangeRestrict (c.mapDomain (k * ·))) := by
      have h2 : (orb κ φ).rangeRestrict (c.mapDomain (k * ·)) = sub κ _ hO k ((orb κ φ).rangeRestrict c) :=
        Subtype.ext (orb_act κ φ k c)
      rw [h2]
      exact LinearMap.toMatrix_mulVec_repr b b _ _
    rw [h1]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, key, orb_act]
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, key]
    simp [orb]
end Gen
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}
private theorem smooth_fin (π : TR.CuspSub F n) : IsSmooth π.finPart := fun v => by
  convert (π.cusp v.1 v.2).1.level using 1
  ext k
  exact Subtype.ext_iff
private theorem smooth_loc (π : TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) : IsSmooth (π.locRep w) := fun v =>
  (smooth_fin π v).preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL w)
private theorem cpt_fin (π : TR.CuspSub F n) (k : TR.Kinf F n) (g : GL (Fin n) (Af F)) (y : π.V) :
    π.op (.cpt k) (π.finPart g y) = π.finPart g (π.op (.cpt k) y) := by
  refine Subtype.ext ?_
  change (TR.rt F n (TR.infGL F n (Unitary.toUnits k)) * TR.rt F n (finGL F n g)) y.1 =
    (TR.rt F n (finGL F n g) * TR.rt F n (TR.infGL F n (Unitary.toUnits k))) y.1
  rw [← map_mul, ← map_mul, TR.infGL_comm]
private theorem fin_loc (π : TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) {k : GL (Fin n) (Af F)}
    (hk : GeneralLinearGroup.map (pLoc F w) k = 1) (g : GL (Fin n) (w.adicCompletion F)) (y : π.V) :
    π.finPart k (π.locRep w g y) = π.locRep w g (π.finPart k y) := by
  simp only [TR.CuspSub.locRep, MonoidHom.comp_apply]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, GlobalTheory.CuspRep.LocUniq.comm_locGL w hk]
private theorem bot_or_top (π : TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) (W : Submodule ℂ π.V)
    (h1 : ∀ g, ∀ x ∈ W, π.locRep w g x ∈ W)
    (h2 : ∀ T : Module.End ℂ π.V, (∀ g x, T (π.locRep w g x) = π.locRep w g (T x)) → ∀ x ∈ W, T x ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  have hop : ∀ o, ∀ x ∈ W, π.op o x ∈ W := fun o x hx => by
    cases o with
    | fin k =>
      have h3 := h1 (GeneralLinearGroup.map (pLoc F w) k) _ (h2
        (π.finPart ((locGL F n w (GeneralLinearGroup.map (pLoc F w) k))⁻¹ * k))
        (fin_loc π w (map_pLoc_inv_mul w k)) x hx)
      rwa [TR.CuspSub.locRep, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at h3
    | cpt k => exact h2 _ (fun g y => cpt_fin π k _ y) x hx
    | lie X => exact h2 _ (fun g y => Subtype.ext (LinearMap.congr_fun (TR.lie_rt_fin X (locGL F n w g)) y.1)) x hx
  rcases π.irred (W.map π.V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, hop o x hx, rfl⟩) with h | h
  · exact Or.inl (hi (h.trans (Submodule.map_bot _).symm))
  · exact Or.inr (hi (h.trans (Submodule.map_subtype_top _).symm))
private theorem isotypic (π : TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) (σ : SmIrr (GL (Fin n) (w.adicCompletion F)))
    (h : π.IsLocComp w σ) : LocIsotypic π.finPart w σ := by
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 π.ne_bot, ?_⟩
  refine (bot_or_top π w _ (fun g x hx => ?_) (fun T hT x hx => ?_)).resolve_left fun e => ?_
  · refine Submodule.mem_comap.1 ((iSup_le (a := Submodule.comap (π.locRep w g) _) fun f => ?_) hx)
    rintro _ ⟨v, rfl⟩
    exact Submodule.mem_iSup_of_mem f ⟨σ.ρ g v, f.2 g v⟩
  · refine Submodule.mem_comap.1 ((iSup_le (a := Submodule.comap T _) fun f => ?_) hx)
    rintro _ ⟨v, rfl⟩
    exact Submodule.mem_iSup_of_mem ⟨T ∘ₗ f.1, fun g v => by
      rw [LinearMap.comp_apply, f.2]; exact hT g _⟩ ⟨v, rfl⟩
  · obtain ⟨f, h0, hf⟩ := h
    exact h0 (LinearMap.range_eq_bot.1 ((iSup_eq_bot.1 e) ⟨f, hf⟩))
private def cptPart (π : TR.CuspSub F n) : Representation ℂ (TR.Kinf F n) π.V :=
  sub (TR.cptRep F n) π.V fun k => π.stable (.cpt k)
private theorem exists_comp (h : UpperTheory.V.Published.AdmissibleReal) (π : TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) :
    ∃ σ, π.IsLocComp w σ := by
  obtain ⟨φ₀, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  set φ : π.V := ⟨φ₀, hφ⟩
  have h0' : φ ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  set L := stab π.finPart φ
  have hL : IsOpen (L : Set (GL (Fin n) (Af F))) := smooth_fin π _
  obtain ⟨K, ho, hc, hK⟩ := exists_compact_open w _ hL
  have hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptPart π k φ)) := by
    have := (π.cusp φ₀ hφ).1.kfin
    refine FiniteDimensional.of_injective ((π.V.subtype ∘ₗ Submodule.subtype _).codRestrict
      (Submodule.span ℂ (Set.range fun k => TR.cptRep F n k φ₀)) fun v => ?_)
      fun v v' e => Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))
    refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap π.V.subtype _)).2 ?_ v.2)
    rintro _ ⟨k, rfl⟩
    exact Submodule.subset_span ⟨k, rfl⟩
  obtain ⟨d, ξ, hξ⟩ := exists_type (cptPart π) φ hfd
  have hcomm : ∀ g k x, π.finPart g (cptPart π k x) = cptPart π k (π.finPart g x) := fun g k x => (cpt_fin π k g x).symm
  let U : Submodule ℂ π.V := annPart (cptPart π) φ ⊓
    fixed π.finPart (L ⊓ (GeneralLinearGroup.map (n := Fin n) (pLoc F w)).ker)
  obtain ⟨σ, hσ, -⟩ := exists_irred (smooth_loc π w) ho (fun W hW e => by
      rcases bot_or_top π w (nullPart (π.locRep w) K) (fun g x hx => nullPart_act _ K g hx)
        (fun T hT x hx => nullPart_comm _ K T hT hx) with h2 | h2
      · exact le_bot_iff.1 (h2 ▸ le_nullPart (smooth_loc π w) hc W hW e)
      · exact absurd (eq_zero_of_mem_nullPart (smooth_loc π w) hc (mem_fix.2 hK) (h2 ▸ Submodule.mem_top)) h0')
    U (fun g x hx => ⟨fun c hc => by
        rw [TR.CuspSub.locRep, MonoidHom.comp_apply, orb_comm _ _ (hcomm _), hx.1 c hc, map_zero],
      mem_fix.2 fun k hk => by rw [fin_loc π w hk.2, mem_fix.1 hx.2 k hk]⟩)
    ((Submodule.ne_bot_iff _).2 ⟨φ, ⟨fun _ hc => hc, mem_fix.2 fun k hk => hk.1⟩, h0'⟩) (fun K' hK' => by
      obtain ⟨W, hW, hWf⟩ := h F n π (L ⊓ (K' ⊓ L.comap (locGL F n w)).comap (GeneralLinearGroup.map (pLoc F w)))
        (hL.inter ((hK'.inter (hL.preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL w))).preimage
          (continuous_map_pLoc w))) d ξ
      refine Submodule.finiteDimensional_of_le (S₂ := W) fun x hx => ?_
      obtain ⟨f, hf, hx1, hf2⟩ := hξ x hx.1.1
      refine hWf f hf (fun k hk v => ?_) hx1
      have h1 := mem_fix.1 hx.1.2 _ ⟨L.mul_mem (L.inv_mem hk.2.2) hk.1, map_pLoc_inv_mul w k⟩
      have h2 := mem_fix.1 hx.2 _ hk.2.1
      have h3 : π.finPart k x = x := by
        rw [← mul_inv_cancel_left (locGL F n w (GeneralLinearGroup.map (pLoc F w) k)) k, map_mul,
          Module.End.mul_apply, h1]
        exact h2
      obtain ⟨c, hc⟩ := hf2 v
      rw [hc, ← orb_comm _ _ (hcomm k), h3])
  exact ⟨σ, hσ⟩
end UpperTheory.V.Af.RealLocalComponent
theorem UpperTheory.V.Af.local_comp_real_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.LocCompR := fun P _ _ _ _ _ π w =>
  ⟨UpperTheory.V.Af.RealLocalComponent.exists_comp P.admR π w, UpperTheory.V.Af.RealLocalComponent.isotypic π w⟩
end
end
end

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
private theorem UpperTheory.V.Af.isOpen_fixMu {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {M : ℕ}
    (hM : 1 ≤ M) : IsOpen {s : G F Ω | ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ} := by
  classical
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots (show 0 < M from hM)] using hζ
  have e : {s : G F Ω | ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ} =
      ⋂ ζ ∈ {ζ : Ω | ζ ^ M = 1}, (MulAction.stabilizer (Ω ≃ₐ[F] Ω) ζ : Set (Ω ≃ₐ[F] Ω)) := by
    ext s
    simp [MulAction.mem_stabilizer_iff]
  rw [e]
  exact hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral ζ
theorem UpperTheory.V.Af.weil_deligne_away_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.WDAway := by
  intro _ F Ω _ _ _ _ _ l _ ι n M hM r _ w hl A h χ hχ hd x hx
  obtain ⟨g, hg⟩ := hd
  let r' : G F Ω →* GL (Fin n) (Qbar l) := (MulAut.conj g).toMonoidHom.comp r
  have hr' : ∀ s, r' s = g * r s * g⁻¹ := fun s => rfl
  have hx' : IsWDOf ι r' x := hx.of_conj hl g fun s => by rw [hr', inv_mul_cancel_right]
  obtain ⟨t, ht, φ, hφ, N, a, hN, ha, rfl⟩ := hx'
  have hs : IsSmooth (r'.comp (Weil h).subtype) := by
    refine .of_open ((UpperTheory.V.Af.isOpen_fixMu (F := F) (Ω := Ω) hM).preimage continuous_subtype_val)
      (fun ζ _ => rfl) fun σ hσ => Units.ext ?_
    change (r' σ : Matrix (Fin n) (Fin n) (Qbar l)) = 1
    rw [hr', hg σ σ.2]
    simp [fun i => hχ i σ hσ]
  obtain rfl : N = 0 := hN.unique ht ((isMonodromy_zero_iff (h := h)).mpr hs)
  refine ⟨fun i => (Units.map ι.toRingHom.toMonoidHom).comp (χ i), a, fun i s hs => ?_, rfl, ?_, fun s => ?_⟩
  · simp [hχ i s hs]
  · rw [ha.1, map_zero]
  · rw [IsFrobSS.ρ_ineIncl (ρ := hN.rep hl ht hφ ι) ha (hN.isSmooth_rep hl ht _ ι), hN.rep_apply, wdMat_zero, coe_ineIncl, hr',
      hg s s.2, toEndC_apply, Matrix.diagonal_map (map_zero ι)]
    rfl
end
end

section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.GalOfCusp
namespace UpperTheory.V.Af.JumpsAbove
variable {l : ℕ} [Fact l.Prime]
private theorem char_mult (K L : FinExt l) (κ : ↥(GK K) →* (↥L.1)ˣ) (hκ : Continuous fun g => (κ g : ↥L.1)) (w : ℤ)
    (hw : Loc.HasWeight (GK K).subtype κ w) (hd : IsDR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ))
    (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (a : ℤ) : multV ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) τ a = if a = -w then 1 else 0 := by
  have := L.2
  have := K.2
  have : IsModuleTopology ℚ_[l] ↥L.1 := isModuleTopologyOfFiniteDimensional
  obtain ⟨T⟩ := Loc.tiedP l
  have hφ : Topology.IsOpenEmbedding (GK K).subtype :=
    (IntermediateField.fixingSubgroup_isOpen K.1).isOpenEmbedding_subtypeVal
  have h := (Loc.charFil (GK K).subtype hφ κ hκ w hw).2
  have hF : ∀ i, Loc.FilT ↥L.1 ↥L.1 i = FilV ((Loc.PP l).PD K) (LL := ↥L.1) (V := ↥L.1) i := fun i => by
    have : (((Loc.PP l).PD (Loc.botExt l)).Fil i).restrictScalars ℚ_[l] =
        (((Loc.PP l).PD K).Fil i).restrictScalars ℚ_[l] := SetLike.coe_injective ((Loc.PP l).PD_Fil _ _ i)
    unfold Loc.FilT FilV
    rw [this]
  have hD : Loc.Ddr (GK K).subtype (Loc.chRep κ) = DdR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) := by
    unfold Loc.Ddr DdR
    refine iInf_congr fun g => ?_
    have h2 : actVdR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) g = Loc.actD (GK K).subtype (Loc.chRep κ) g := by
      unfold actVdR Loc.actD
      congr 1
      exact LinearMap.ext fun z => (Loc.PP l).PD_actdR K g z
    rw [h2]
  simp only [Loc.FilD, hF, hD] at h
  have hr := (((GlobalTheory.Per.Components.components_finrank l _ _ T K L _ (Formalism.WeaklyAdmissibleFiltrations.charRep κ)).1 τ).2.2 hd).trans
    (Module.finrank_self _)
  have hle : DdRE ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) τ ≤ DdR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) := inf_le_left
  have h1 : ∀ i, i ≤ -w → Module.finrank ↥L.1 ↥(FildR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) τ i) = 1 := fun i hi => by
    rw [FildR, inf_eq_left.2 (hle.trans (inf_eq_left.1 ((h i).1 hi))), hr]
  have h0 : ∀ i, -w < i → Module.finrank ↥L.1 ↥(FildR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) τ i) = 0 := fun i hi => by
    rw [FildR, le_bot_iff.1 ((inf_le_inf_right _ hle).trans ((h i).2 hi).le), finrank_bot]
  unfold multV
  rcases lt_trichotomy a (-w) with ha | ha | ha
  · rw [h1 a ha.le, h1 (a + 1) ha, if_neg ha.ne]; simp
  · rw [h1 a ha.le, h0 (a + 1) (by omega), if_pos ha]; simp
  · rw [h0 a ha, h0 (a + 1) (by omega), if_neg ha.ne']; simp
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
private theorem flag_mult (K L : FinExt l) (n : ℕ) : ∀ (ρ : Representation ↥L.1 ↥(GK K) (Fin n → ↥L.1))
    (M : ↥(GK K) → Matrix (Fin n) (Fin n) ↥L.1) (κ : Fin n → ↥(GK K) →* (↥L.1)ˣ),
    (∀ g x, ρ g x = (M g).mulVec x) → (∀ g i j, j < i → M g i j = 0) → (∀ g i, M g i i = κ i g) →
    IsDR ((Loc.PP l).PD K) ρ → (∀ i, IsDR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep (κ i))) ∧
      ∀ τ a, multV ((Loc.PP l).PD K) ρ τ a = ∑ i, multV ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep (κ i)) τ a := by
  obtain ⟨T⟩ := Loc.tiedP l
  induction n with
  | zero =>
    intro ρ M κ _ _ _ _
    refine ⟨fun i => i.elim0, fun τ a => ?_⟩
    have : Subsingleton (TensorProduct ℚ_[l] (Fin 0 → ↥L.1) (Loc.PP l).R.BdR) := inferInstance
    simp [multV, Module.finrank_zero_of_subsingleton]
  | succ n ih =>
    intro ρ M κ hρ hM hκ hd
    let ι : ↥L.1 →ₗ[↥L.1] (Fin (n + 1) → ↥L.1) := LinearMap.single _ (fun _ => ↥L.1) 0
    let π : (Fin (n + 1) → ↥L.1) →ₗ[↥L.1] (Fin n → ↥L.1) := LinearMap.funLeft _ _ Fin.succ
    let M' : ↥(GK K) → Matrix (Fin n) (Fin n) ↥L.1 := fun g => (M g).submatrix Fin.succ Fin.succ
    have hπ : ∀ g x, π (ρ g x) = (M' g).mulVec (π x) := fun g x => by
      funext i
      simp [π, M', hρ, LinearMap.funLeft_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
        hM g i.succ 0 (Fin.succ_pos i)]
    have hs : Function.Surjective π := LinearMap.funLeft_surjective_of_injective _ _ _ (Fin.succ_injective n)
    let ρ' : Representation ↥L.1 ↥(GK K) (Fin n → ↥L.1) :=
      { toFun := fun g => Matrix.toLin' (M' g)
        map_one' := LinearMap.ext fun y => by
          obtain ⟨x, rfl⟩ := hs y
          rw [Matrix.toLin'_apply, ← hπ, map_one]; rfl
        map_mul' := fun g h => LinearMap.ext fun y => by
          obtain ⟨x, rfl⟩ := hs y
          rw [Module.End.mul_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, ← hπ, ← hπ, ← hπ,
            map_mul]; rfl }
    obtain ⟨d0, d2, hm⟩ := GlobalTheory.Per.ExactMult.exact_hodge_add l _ _ T K L _ (Formalism.WeaklyAdmissibleFiltrations.charRep (κ 0)) _ ρ _ ρ' ι π
      (fun g x => by
        funext i
        rw [hρ]
        refine Fin.cases ?_ (fun i => ?_) i
        · simp [ι, Formalism.WeaklyAdmissibleFiltrations.charRep, hκ]
        · simp [ι, Formalism.WeaklyAdmissibleFiltrations.charRep, hM g i.succ 0 (Fin.succ_pos i)])
      hπ (fun x y h => by simpa [ι] using congrFun h 0) hs
      (by
        ext x
        simp only [LinearMap.mem_range, LinearMap.mem_ker]
        constructor
        · rintro ⟨y, rfl⟩
          funext i
          simp [ι, π, LinearMap.funLeft_apply]
        · intro h
          refine ⟨x 0, funext fun i => Fin.cases ?_ (fun i => ?_) i⟩
          · simp [ι]
          · simpa [ι, π, LinearMap.funLeft_apply] using (congrFun h i).symm) hd
    obtain ⟨e1, e2⟩ := ih ρ' M' (fun i => κ i.succ) (fun g x => rfl)
      (fun g i j h => hM g _ _ (Fin.succ_lt_succ_iff.2 h)) (fun g i => hκ g _) d2
    refine ⟨fun i => Fin.cases d0 e1 i, fun τ a => ?_⟩
    rw [(hm τ a).2.1, Fin.sum_univ_succ, e2]
private theorem exists_open (K : FinExt l) {M : ℕ} (hM : 1 ≤ M) : ∃ U : Subgroup ↥(GK K), IsOpen (U : Set ↥(GK K)) ∧
    ∀ s ∈ U, ∀ ζ : Om l, ζ ^ M = 1 → (s : GQ l) ζ = ζ := by
  have : NeZero M := ⟨by omega⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) M
  have : FiniteDimensional ℚ_[l] ↥(IntermediateField.adjoin ℚ_[l] {z}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)
  refine ⟨(IntermediateField.adjoin ℚ_[l] {z}).fixingSubgroup.comap (GK K).subtype,
    (IntermediateField.fixingSubgroup_isOpen _).preimage continuous_subtype_val, fun s hs ζ hζ => ?_⟩
  obtain ⟨i, -, rfl⟩ := hz.eq_pow_of_pow_eq_one hζ
  have h : (s : GQ l) z = z := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs z
    (IntermediateField.mem_adjoin_simple_self _ z)
  rw [map_pow, h]
end UpperTheory.V.Af.JumpsAbove
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.JumpsAbove in
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
theorem UpperTheory.V.Af.jumps_above_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.JumpsAbove := by
  rintro - F Ω _ _ _ _ _ l _ - n M hM m r hr w A - O _ _ _ Bw hj κ ⟨χ, hχ, ⟨g, hg⟩, hI⟩ τ J hJ
  obtain ⟨L, r', hL, hd, τ', -, hc⟩ := (GlobalTheory.ConjLocal.local_conj l (Loc.PP l) F Ω O _ Bw n _
    ((MulAut.conj g).toMonoidHom.comp (r.comp (Dec (F := F) A).subtype)) g (fun _ => rfl)).2.2.2 τ J hJ
  have he : ∀ s i j, ((r' s i j : ↥L.1) : Om l) = (g * r s * g⁻¹ : GL (Fin n) (Om l)) i j := fun s i j =>
    congrArg (fun f : ↥(Dec (F := F) A) →* GL (Fin n) (Om l) => (f s : Matrix (Fin n) (Fin n) (Om l)) i j) hL.2
  have hκ : ∀ s i, ((r' s i i : ↥L.1) : Om l) = κ i s := fun s i => (he s i i).trans ((hg s).2 i)
  let κ' : Fin n → ↥(GK Bw.Kw) →* (↥L.1)ˣ := fun i => MonoidHom.toHomUnits
    { toFun := fun s => r' (Bw.e.symm s) i i
      map_one' := by simp
      map_mul' := fun s t => Subtype.ext (by
        rw [IntermediateField.coe_mul, hκ, hκ, hκ, map_mul, map_mul, Units.val_mul]) }
  have hκ' : ∀ i s, ((κ' i s : ↥L.1) : Om l) = κ i (Bw.e.symm s) := fun i s => hκ _ _
  obtain ⟨d, hm⟩ := flag_mult Bw.Kw L n (Bw.repE L r') (fun s => r' (Bw.e.symm s)) κ' (fun _ _ => rfl)
    (fun s i j h => Subtype.ext ((he _ i j).trans ((hg _).1 i j h))) (fun _ _ => rfl)
    (by rw [IsDR, Module.finrank_fin_fun]; exact hd)
  obtain ⟨U, hU, hUζ⟩ := exists_open Bw.Kw hM
  have hcm : ∀ (s : ↥(GK Bw.Kw)) x, (s : GQ l) (Bw.j x) = Bw.j ((Bw.e.symm s : G F Ω) x) := fun s x => by
    rw [← Bw.e_comm, MulEquiv.apply_symm_apply]
  have key : ∀ i a, multV ((Loc.PP l).PD Bw.Kw) (Formalism.WeaklyAdmissibleFiltrations.charRep (κ' i)) τ' a = if a = -m i then 1 else 0 := fun i a => by
    refine char_mult Bw.Kw L (κ' i) (continuous_induced_rng.2 ?_) (m i) ⟨U, hU, fun s hs hq => ?_⟩ (d i) τ' a
    · have h1 : Continuous fun s : ↥(GK Bw.Kw) => g * r (Bw.e.symm s) * g⁻¹ :=
        (continuous_const.mul (hr.comp (continuous_subtype_val.comp Bw.e_symm_cont))).mul continuous_const
      exact ((Units.continuous_val.comp h1).matrix_elem i i).congr fun s => (he _ i i).symm
    · have hine : (Bw.e.symm s : G F Ω) ∈ Ine (F := F) A := by
        refine ⟨(Bw.e.symm s).2, fun x hx => ?_⟩
        rw [hj.valuation_lt_one_iff, map_sub, ← hcm]
        exact ((Loc.iqBasic l).2.2.1 _).1 hq _ ((hj x).1 ((A.valuation_le_one_iff x).1 hx))
      have h1 : χ i (Bw.e.symm s) = 1 := hχ i _ fun ζ hζ => Bw.j.injective (by
        rw [← hcm, hUζ s hs _ (by rw [← map_pow, hζ, map_one])])
      have h2 := (GlobalTheory.Survey.CrystallineCharacterRatio.chi_eq_cyc (Loc.PP l) Bw.j _ _ (hcm s)).symm.trans ((Loc.cycFacts l l).2.2 s)
      refine Units.ext (Subtype.ext ?_)
      rw [hκ', hI i _ hine, h1, mul_one, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val]
      refine Eq.trans ?_ (map_zpow₀ (algebraMap ↥L.1 (Om l)) _ _).symm
      congr 1
      exact congrArg (algebraMap ℚ_[l] (Om l)) h2
  ext a
  have h := hc a
  rw [LocBridge.multE, hm] at h
  simp only [key] at h
  rw [Multiset.count_map, ← Nat.cast_inj (R := ℤ), h]
  simp [Finset.card_def]
end
end

section




section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Filter Topology Matrix
namespace UpperTheory.V.Af.GlobalFixedVectors
variable {F : Type} [Field F] [NumberField F] {n M : ℕ}
end UpperTheory.V.Af.GlobalFixedVectors
open UpperTheory.V.Af UpperTheory.V.Af.GlobalFixedVectors in
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
theorem UpperTheory.V.Af.globFixed_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.GlobFixed := by
  classical
  intro _ F _ _ n M _ V _ _ ρ hρ h
  have key : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), HasFixed ρ (KAway n M S) → HasFixed ρ (KAway n M ∅) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact id
    | insert w S hw ih =>
      rintro ⟨v, hv0, hv⟩
      obtain ⟨σ, ⟨-, hσ⟩, hfix⟩ := h w
      let W : Submodule ℂ V := ⨅ k : KAway n M (insert w S), LinearMap.ker (ρ k - 1)
      have hWm : ∀ x, x ∈ W ↔ ∀ k ∈ KAway n M (insert w S), ρ k x = x := fun x => by
        simp [W, Submodule.mem_iInf, sub_eq_zero]
      obtain ⟨x, hxW, hx0, hx⟩ := sub_fixed σ.ρ σ.irred (ρ.comp (locGL F n w)) hσ W (fun g x hx => (hWm _).2 fun k hk => by
        have e : k * locGL F n w g = locGL F n w g * k := gl_ext fun u => by
          by_cases hu : u = w
          · subst hu; simp [(mem_KAway.1 hk).2 u (Finset.mem_insert_self _ _)]
          · simp [pLoc_locGL_of_ne hu]
        change ρ k (ρ (locGL F n w g) x) = ρ (locGL F n w g) x
        rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, (hWm x).1 hx k hk])
        (fun e => hv0 (by simpa [e] using (hWm v).2 hv)) _ hfix
      refine ih ⟨x, hx0, fun k hk => ?_⟩
      have h1 := loc_mem w (mem_KAway.1 hk).1
      have h2 : k * (locGL F n w (GeneralLinearGroup.map (pLoc F w) k))⁻¹ ∈ KAway n M (insert w S) := by
        refine mem_KAway.2 ⟨mul_mem (mem_KAway.1 hk).1 (inv_mem h1), fun u hu => ?_⟩
        by_cases huw : u = w
        · subst huw; simp [pLoc_locGL]
        · simp [pLoc_locGL_of_ne huw, (mem_KAway.1 hk).2 u ((Finset.mem_insert.1 hu).resolve_left huw)]
      have h3 : ρ (locGL F n w (GeneralLinearGroup.map (pLoc F w) k)) x = x := hx _ h1
      have h4 := (hWm x).1 hxW _ h2
      rwa [← h3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, h3] at h4
  obtain ⟨w⟩ : Nonempty (HeightOneSpectrum (𝓞 F)) := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
    exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField F)⟩⟩
  obtain ⟨σ, ⟨hV, -⟩, -⟩ := h w
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨S, hS⟩ := exists_KAway_subset (M := M) ((hρ v).mem_nhds (by simp))
  obtain ⟨x, hx0, hx⟩ := key S ⟨v, hv, fun k hk => hS hk⟩
  exact ⟨x, hx0, fun k hk => hx k (mem_KAway.2 ⟨hk, by simp⟩)⟩
end
end

section




section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
abbrev _root_.UpperTheory.V.Lev.fixedDvd_s_ty : Prop :=
    _root_.UpperTheory.V.Af.Hypotheses' → _root_.UpperTheory.V.Lev.FixedDvdAlt
end
end
