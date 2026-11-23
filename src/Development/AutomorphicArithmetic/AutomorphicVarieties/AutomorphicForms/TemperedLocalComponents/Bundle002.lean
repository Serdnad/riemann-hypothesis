module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ConjSep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle005
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle546
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle547
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CharFil
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CapCentral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.PCuspFin
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

section Conj

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k}

end Conj

private theorem infOf_of_weights {n : ℕ} (m : Fin n → ℤ) (μ : Multiset ℂ)
    (h : (Finset.univ.val.map fun i => -m i).map (fun n : ℤ => (n : ℂ)) = μ.map fun z => ((n : ℂ) - 1) / 2 - z) :
    μ = infOf m := by
  have h2 := congrArg (Multiset.map fun z : ℂ => ((n : ℂ) - 1) / 2 - z) h
  simp only [Multiset.map_map, Function.comp_def, sub_sub_cancel, Multiset.map_id', Int.cast_neg, sub_neg_eq_add] at h2
  exact h2.symm

private theorem exists_over (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] :
    ∃ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal := by
  have hl : (l : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hu : ¬ IsUnit (l : 𝓞 F) := fun hu => by
    have h := hu.map (Algebra.norm ℤ)
    rw [← map_natCast (algebraMap ℤ (𝓞 F)), Algebra.norm_algebraMap, isUnit_pow_iff Module.finrank_pos.ne'] at h
    exact (Nat.prime_iff_prime_int.1 Fact.out).not_unit h
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal (Ideal.span {(l : 𝓞 F)}) (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hmem : (l : 𝓞 F) ∈ P := hle (Ideal.mem_span_singleton_self _)
  exact ⟨⟨P, hP.isPrime, fun h0 => hl (by rw [h0] at hmem; exact hmem)⟩, hmem⟩

end UpperTheory.V.Af
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.ThetaPull

namespace UpperTheory.V.Af

private theorem regAlg_of_infOf {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} {m : Fin n → ℤ}
    (hm : StrictAnti m) {π : CuspSub K n} (h : ∀ τ, π.HasInfChar τ (infOf m)) : (CG.mk π).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  rw [CG.HasInfChar.infChar_eq (π := CG.mk π) (h τ)]
  refine ⟨Multiset.Nodup.map (fun i j e => hm.injective ?_) Finset.univ.nodup, fun z hz => ?_⟩
  · exact_mod_cast add_left_cancel e
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
    exact ⟨m i, add_comm _ _⟩

private theorem eventually_notMem {K : Type} [Field K] [NumberField K] {M : ℕ} (hM : 1 ≤ M) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, (M : 𝓞 K) ∉ w.asIdeal := by
  have h0 : Ideal.span {(M : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 (by omega)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  exact Ideal.dvd_span_singleton.2 (not_not.1 hw)

private theorem sep_theta {K : Type} [Field K] [NumberField K] [IsCMField K] {n : ℕ} {π π' : CuspSub K n} {σ : ℂ ≃+* ℂ}
    (hc : π.IsCsd) (h : Sep σ π.finPart π'.finPart) (h' : Sep σ.symm π'.finPart π.finPart) :
    Sep (RingEquiv.refl ℂ) π'.finPart (thetaSub π').finPart ∧ Sep (RingEquiv.refl ℂ) (thetaSub π').finPart π'.finPart := by
  obtain ⟨T, hT⟩ := hc
  have h1 := Sep.of_equiv (ρ := π.finPart.comp (thetaGL n (cFin K))) (ρ' := π.finPart) T fun g v => hT (.fin g) v
  have h2 := Sep.of_equiv (ρ := π'.finPart.comp (thetaGL n (cFin K))) (ρ' := (thetaSub π').finPart)
    ((pull K n).submoduleMap π'.V) fun g v => Subtype.ext (act_pull (.fin g) v.1).symm
  have e : σ.symm.trans σ = RingEquiv.refl ℂ := σ.symm_trans_self
  exact ⟨e ▸ ((h'.trans h1.2).trans (h.comp _)).trans h2.1, e ▸ ((h2.2.trans (h'.comp _)).trans h1.1).trans h⟩

end UpperTheory.V.Af

end

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
  set_option synthInstance.maxHeartbeats 200000 in
  have h1 : ∀ i, i ≤ -w → Module.finrank ↥L.1 ↥(FildR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) τ i) = 1 := fun i hi => by
    rw [FildR, inf_eq_left.2 (hle.trans (inf_eq_left.1 ((h i).1 hi))), hr]
  set_option synthInstance.maxHeartbeats 200000 in
  have h0 : ∀ i, -w < i → Module.finrank ↥L.1 ↥(FildR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) τ i) = 0 := fun i hi => by
    rw [FildR, le_bot_iff.1 ((inf_le_inf_right _ hle).trans ((h i).2 hi).le), finrank_bot]
  unfold multV
  rcases lt_trichotomy a (-w) with ha | ha | ha
  · rw [h1 a ha.le, h1 (a + 1) ha, if_neg ha.ne]; simp
  · rw [h1 a ha.le, h0 (a + 1) (by omega), if_pos ha]; simp
  · rw [h0 a ha, h0 (a + 1) (by omega), if_neg ha.ne']; simp

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

end

section

open NumberField GlobalTheory.CuspRep UpperTheory.V


open Matrix in
private theorem exists_contRep {K I : Type} [Group K] [TopologicalSpace K] {d : ℕ} (ξ : K →* Matrix (Fin d) (Fin d) ℂ)
    (ev : I → Module.Dual ℂ (Fin d → ℂ)) (hc : ∀ i v, Continuous fun k => ev i (ξ k *ᵥ v))
    (hs : ∀ k v, (∀ i, ev i v = 0) → ∀ i, ev i (ξ k *ᵥ v) = 0) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W) (ρ : Representation ℂ K W),
      GlobalTheory.Published.AutFin.IsContRep ρ ∧ ∀ i v, (fun k => ev i (ξ k *ᵥ v)) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
  let N : Submodule ℂ (Fin d → ℂ) := ⨅ i, LinearMap.ker (ev i)
  have hN : ∀ v, v ∈ N ↔ ∀ i, ev i v = 0 := fun v => by simp [N, Submodule.mem_iInf]
  let σ : Representation ℂ K (Fin d → ℂ) := (Matrix.toLinAlgEquiv' : _ ≃ₐ[ℂ] _).toMonoidHom.comp ξ
  have hσ : ∀ k v, σ k v = ξ k *ᵥ v := fun k v => Matrix.toLinAlgEquiv'_apply _ _
  have hle : ∀ k, N ≤ N.comap (σ k) := fun k v hv => (hN _).2 (hσ k v ▸ hs k v ((hN v).1 hv))
  have hq : ∀ k v, σ.quotient N hle k (N.mkQ v) = N.mkQ (ξ k *ᵥ v) := fun k v => by rw [← hσ]; rfl
  refine ⟨(Fin d → ℂ) ⧸ N, inferInstance, inferInstance, inferInstance, σ.quotient N hle, fun ℓ w => ?_, fun i v => ?_⟩
  · obtain ⟨v, rfl⟩ := N.mkQ_surjective w
    simp only [hq]
    have hl : ℓ ∘ₗ N.mkQ ∈ Submodule.span ℂ (Set.range ev) :=
      FiniteDimensional.mem_span_of_iInf_ker_le_ker fun x hx => by
        rw [LinearMap.mem_ker, LinearMap.comp_apply, (Submodule.Quotient.mk_eq_zero N).2 hx |> fun h => show N.mkQ x = 0 from h,
          map_zero]
    change Continuous fun k => (ℓ ∘ₗ N.mkQ) (ξ k *ᵥ v)
    generalize ℓ ∘ₗ N.mkQ = m at hl
    induction hl using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hc i v
    | zero => exact continuous_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul r x _ hx => exact hx.const_smul r
  · refine Submodule.subset_span ⟨N.liftQ (ev i) (iInf_le _ i), N.mkQ v, funext fun k => ?_⟩
    rw [hq]
    rfl

open Matrix in
theorem UpperTheory.V.Af.admissibleReal :
    UpperTheory.V.Published.AdmissibleReal := by
  intro F _ _ _ a π U hU d ξ
  obtain ⟨c, hc⟩ := TR.Cen.exists_cap_scalar π
  let I : Type := {f : (Fin d → ℂ) →ₗ[ℂ] π.V // ∀ k v, f (ξ k *ᵥ v) = π.op (.cpt k) (f v)} × GA F a
  let ev : I → Module.Dual ℂ (Fin d → ℂ) := fun i =>
    (LinearMap.proj i.2).comp ((TR.Sm F a).subtype.comp (π.V.subtype.comp i.1.1))
  have hev : ∀ (i : I) k v, ev i (ξ k *ᵥ v) = (TR.cptRep F a k (i.1.1 v).1).1 i.2 := fun i k v =>
    congrArg (fun x : π.V => x.1.1 i.2) (i.1.2 k v)
  obtain ⟨W, _, _, _, ρ, hρ, hco⟩ := exists_contRep ξ ev
    (fun i v => by simp only [hev]; exact TR.Cen.continuous_cptRep _ _)
    (fun k v h i => by rw [hev]; exact h (i.1, i.2 * TR.infGL F a (Unitary.toUnits k)))
  have hfin := UpperTheory.V.Af.cuspFormsFiniteReal F a U hU W ρ hρ c
  set S := Submodule.span ℂ {φ : TR.Sm F a | TR.IsCuspForm φ ∧ (∀ k ∈ U, TR.finRep F a k φ = φ) ∧
    (∀ g : GA F a, (fun k : TR.Kinf F a => (TR.cptRep F a k φ).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) ∧
    ∀ v u, TR.cap v u φ = c v u • φ}
  refine ⟨S.comap π.V.subtype, FiniteDimensional.of_injective
    ((π.V.subtype ∘ₗ (S.comap π.V.subtype).subtype).codRestrict S fun x => x.2) (fun x y e => ?_), ?_⟩
  · exact Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))
  · rintro f hf hfix _ ⟨v, rfl⟩
    refine Submodule.subset_span ⟨π.cusp _ (f v).2, fun k hk => congrArg Subtype.val (hfix k hk v), fun g => ?_,
      fun w u => hc w u _ (f v).2⟩
    have h := hco (⟨f, hf⟩, g) v
    simp only [hev] at h
    exact h
end
