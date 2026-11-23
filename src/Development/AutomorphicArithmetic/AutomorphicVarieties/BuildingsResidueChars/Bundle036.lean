module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle306
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
public import GroundTheory.AutomorphicForms.AdelicGLn
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LaurentBlockInduction.LdDefs
import Formalism.DoubleCosetMeasures.Statement
import GroundTheory.AutomorphicForms.GL2.ExistsEqPowMulOfValuationLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.AbW
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.InfEmbGrpEq
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private noncomputable def mulCh {Γ : Type} [Group Γ] (χ : Γ →* ℂˣ) : (Γ → ℂ) ≃ₗ[ℂ] (Γ → ℂ) where
  toFun φ g := (χ g : ℂ) * φ g
  invFun φ g := ((χ g)⁻¹ : ℂˣ) * φ g
  map_add' φ ψ := by ext g; simp [mul_add]
  map_smul' c φ := by ext g; simp [mul_left_comm]
  left_inv φ := by ext g; simp
  right_inv φ := by ext g; simp

private theorem cont_ch {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (χ : Γ →* ℂˣ)
    (h : IsOpen (χ.ker : Set Γ)) : Continuous fun g => (χ g : ℂ) := by
  refine Units.continuous_val.comp (continuous_of_continuousAt_one χ ?_)
  refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
  filter_upwards [h.mem_nhds χ.ker.one_mem] with g hg
  exact (MonoidHom.mem_ker.1 hg).symm

private theorem irr_tw {H M : Type} [Group H] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ H M) (η : H →* ℂˣ) :
    ρ.IsIrreducible ↔ (twRep ρ η).IsIrreducible := by
  rw [isIrreducible_iff, isIrreducible_iff]
  refine and_congr_right fun _ => forall_congr' fun W => imp_congr_left ?_
  refine forall_congr' fun g => forall_congr' fun v => forall_congr' fun _ => ?_
  exact (W.smul_mem_iff (Units.ne_zero (η g))).symm

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (χ : UA E n →* ℂˣ)

private theorem RU_mulCh (x : UA E n) (φ : UA E n → ℂ) :
    RU E n x (mulCh χ φ) = (χ x : ℂ) • mulCh χ (RU E n x φ) := by
  ext g
  change (χ (g * x) : ℂ) * φ (g * x) = (χ x : ℂ) * ((χ g : ℂ) * φ (g * x))
  rw [map_mul, Units.val_mul]; ring

private theorem form_mulCh (ho : IsOpen (χ.ker : Set (UA E n))) (hr : ∀ g ∈ ratU E n, χ g = 1) {φ : UA E n → ℂ}
    (h : IsAutFormU φ) : IsAutFormU (mulCh χ φ) := by
  refine ⟨(cont_ch χ ho).mul h.cont, fun γ hγ g => ?_, ?_, ?_⟩
  · change (χ (γ * g) : ℂ) * φ (γ * g) = (χ g : ℂ) * φ g
    rw [map_mul, hr γ hγ, one_mul, h.left γ hγ]
  · refine isOpen_stab_of_mem_nhds ((RU E n).comp (finU (E := E) (n := n)).subtype) (mulCh χ φ) ?_
    have h2 : IsOpen ((Subtype.val : finU (E := E) (n := n) → UA E n) ⁻¹' (χ.ker : Set (UA E n))) := ho.preimage continuous_subtype_val
    refine Filter.mem_of_superset ((h.level.inter h2).mem_nhds ⟨?_, ?_⟩) fun k hk => ?_
    · change RU E n 1 φ = φ
      simp
    · exact χ.ker.one_mem
    · have h1 : RU E n k φ = φ := hk.1
      have h3 : χ k = 1 := hk.2
      change RU E n k (mulCh χ φ) = mulCh χ φ
      rw [RU_mulCh, h1, h3]; simp
  · haveI := h.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)).map
      (mulCh χ).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    change RU E n k (mulCh χ φ) ∈ _
    rw [RU_mulCh]
    exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem (Submodule.subset_span ⟨k, rfl⟩))
end

theorem UpperTheory.exists_automorphicRep_twist_by_character :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (χ : UA E n →* ℂˣ), IsOpen (χ.ker : Set (UA E n)) → (∀ g ∈ ratU E n, χ g = 1) → ∀ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ → ∃ σ' : Submodule ℂ (UA E n → ℂ), IsAutRepU σ' ∧ (∀ w : Plc E, (∀ g ∈ locU n w, cLoc w g ∈ GlobalTheory.LFun.KGL w (n := n) → χ g = 1) → IsUnramU σ w → IsUnramU σ' w) ∧ ∀ (Gv : Subgroup (UA E n)) (H M : Type) [Group H] [AddCommGroup M] [Module ℂ M] (p : Gv →* H) (ρ : Representation ℂ H M) (η : H →* ℂˣ), (∀ x : Gv, χ x = η (p x)) → (IsCompAlong σ Gv p ρ ↔ IsCompAlong σ' Gv p (twRep ρ η)) := by
  intro E _ _ _ n χ ho hr σ hσ
  refine ⟨σ.comap (mulCh χ).symm.toLinearMap, ⟨fun φ hφ => ?_, fun x φ hφ => ?_, fun e => ?_, fun W hW hs => ?_⟩,
    fun w hw ⟨φ, hφ, h0, hf⟩ => ?_, fun Gv H M _ _ _ p ρ η hη => and_congr (irr_tw ρ η) ⟨?_, ?_⟩⟩
  · obtain ⟨ψ, rfl⟩ := (mulCh χ).surjective φ
    exact form_mulCh χ ho hr (hσ.aut ψ (by simpa using hφ))
  · obtain ⟨ψ, rfl⟩ := (mulCh χ).surjective φ
    rw [RU_mulCh]
    refine Submodule.smul_mem _ _ ?_
    simpa using hσ.stable x ψ (by simpa using hφ)
  · refine hσ.ne_bot (eq_bot_iff.2 fun φ hφ => ?_)
    have : mulCh χ φ ∈ σ.comap (mulCh χ).symm.toLinearMap := by simpa using hφ
    rw [e] at this
    simpa using this
  · have := hσ.irred (W.comap (mulCh χ).toLinearMap) (fun φ hφ => by simpa using hW hφ) fun x φ hφ => by
      have := hs x _ hφ
      change RU E n x (mulCh χ φ) ∈ W at this
      rw [RU_mulCh] at this
      exact (W.smul_mem_iff (Units.ne_zero (χ x))).1 this
    refine this.imp (fun e => eq_bot_iff.2 fun φ hφ => ?_) fun e => le_antisymm hW fun φ hφ => ?_
    · obtain ⟨ψ, rfl⟩ := (mulCh χ).surjective φ
      have : ψ ∈ W.comap (mulCh χ).toLinearMap := hφ
      rw [e] at this
      simpa using this
    · obtain ⟨ψ, rfl⟩ := (mulCh χ).surjective φ
      have : ψ ∈ σ := by simpa using hφ
      rw [← e] at this
      exact this
  · refine ⟨mulCh χ φ, by simpa using hφ, by simpa using h0, fun x hx hk => ?_⟩
    rw [RU_mulCh, hf x hx hk, hw x hx hk]; simp
  · rintro ⟨f, h0, h1, h2⟩
    refine ⟨(mulCh χ).toLinearMap ∘ₗ f, fun e => h0 (LinearMap.ext fun v => ?_), fun v => by simpa using h1 v, fun x v => ?_⟩
    · simpa using LinearMap.congr_fun e v
    · change mulCh χ (f ((η (p x) : ℂ) • ρ (p x) v)) = RU E n x (mulCh χ (f v))
      rw [RU_mulCh, map_smul, map_smul, h2, hη]
  · rintro ⟨f, h0, h1, h2⟩
    refine ⟨(mulCh χ).symm.toLinearMap ∘ₗ f, fun e => h0 (LinearMap.ext fun v => ?_), fun v => h1 v, fun x v => ?_⟩
    · simpa using LinearMap.congr_fun e v
    · apply (mulCh χ).injective
      apply smul_right_injective _ (Units.ne_zero (χ x))
      have := h2 x v
      rw [twRep_apply, map_smul, ← hη] at this
      change (χ x : ℂ) • mulCh χ ((mulCh χ).symm (f (ρ (p x) v))) = (χ x : ℂ) • mulCh χ (RU E n x ((mulCh χ).symm (f v)))
      rw [← RU_mulCh, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, this]
end

section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Af
open GlobalTheory.CuspRep (SmIrr Af invT finId pFin)
open scoped Matrix

section General

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}
  {h : G → ℂ} {x y : V}

private theorem pair_heckeVec_comp (hK : IsCommensurated K) (hh : h ∈ Hecke ℂ K) (hx : x ∈ fixed ρ K)
    (hy : y ∈ fixed ρ K) (β : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (d : G → ℂ) (hd : ∀ k ∈ K, d k = 1)
    (hi : ∀ g v w, β (ρ g v) (ρ g w) = d g * β v w) (θ : G →* G) (hθ : ∀ k ∈ K, θ k ∈ K) (z : ℂ)
    (ht : ∀ g, h g ≠ 0 → ∃ a ∈ K, ∃ b ∈ K, ∃ t, θ t = t⁻¹ ∧ g = a * t * b ∧ d t = z) :
    z * β (heckeVec (ρ.comp θ) K h x) y = β x (heckeVec ρ K h y) := by
  have hf := GlobalTheory.LGrp.mem_fixed.1 hx
  have hg := GlobalTheory.LGrp.mem_fixed.1 hy
  have bi : ∀ a ∈ K, ∀ b ∈ K, ∀ t, β (ρ (a * t * b) x) y = β (ρ t x) y := fun a ha b hb t => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hf b hb]
    exact (congrArg (β _) (hg a ha).symm).trans ((hi a _ _).trans (by rw [hd a ha, one_mul]))
  have bi' : ∀ a ∈ K, ∀ b ∈ K, ∀ t, β x (ρ (a * t * b) y) = β x (ρ t y) := fun a ha b hb t => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hg b hb]
    exact (congrArg (fun u => β u _) (hf a ha).symm).trans ((hi a _ _).trans (by rw [hd a ha, one_mul]))
  have inv : ∀ t, d t * β (ρ t⁻¹ x) y = β x (ρ t y) := fun t => by
    rw [← hi t]; simp
  have e1 := (z • β.flip y).toAddMonoidHom.map_finsum (finite_heckeVec hK hh (ρ.comp θ) x)
  have e2 := (β x).toAddMonoidHom.map_finsum (finite_heckeVec hK hh ρ y)
  refine e1.trans (Eq.trans (finsum_congr fun c => ?_) e2.symm)
  change z * β (h c.out • ρ (θ c.out) x) y = β x (h c.out • ρ c.out y)
  rw [map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  by_cases h0 : h c.out = 0
  · simp [h0]
  obtain ⟨a, ha, b, hb, t, htt, e, hz⟩ := ht _ h0
  rw [mul_left_comm]
  congr 1
  rw [e, map_mul θ, map_mul θ, bi _ (hθ a ha) _ (hθ b hb), bi' _ ha _ hb, htt, ← hz, inv]

private theorem exists_fixed_pair [TopologicalSpace G] [IsTopologicalGroup G] (hρ : IsSmooth ρ)
    (hK : IsCompact (K : Set G)) (l : V →ₗ[ℂ] ℂ) (hl : ∀ k ∈ K, ∀ v, l (ρ k v) = l v) (y : V) :
    ∃ y' ∈ fixed ρ K, l y' = l y := by
  classical
  open GlobalTheory.OrbitAvg in
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hfi : (GlobalTheory.OrbitAvg.stab ρ K y).FiniteIndex := by
    have ho : IsOpen (GlobalTheory.OrbitAvg.stab ρ K y : Set K) := (hρ y).preimage continuous_subtype_val
    haveI := (GlobalTheory.OrbitAvg.stab ρ K y).quotient_finite_of_isOpen ho
    exact Subgroup.finiteIndex_of_finite_quotient
  refine ⟨GlobalTheory.OrbitAvg.avg ρ K y,
    GlobalTheory.LGrp.mem_fixed.2 fun u hu => GlobalTheory.OrbitAvg.avg_invariant ρ K hfi ⟨u, hu⟩, ?_⟩
  haveI := Fintype.ofFinite (K ⧸ GlobalTheory.OrbitAvg.stab ρ K y)
  have hc : ((GlobalTheory.OrbitAvg.stab ρ K y).index : ℂ) ≠ 0 := by exact_mod_cast hfi.index_ne_zero
  have h1 : ∀ q : K ⧸ GlobalTheory.OrbitAvg.stab ρ K y, l (ρ (q.out : K) y) = l y := fun q => hl _ q.out.2 y

  simp only [GlobalTheory.OrbitAvg.avg, GlobalTheory.OrbitAvg.avgH, GlobalTheory.OrbitAvg.cv, finsum_eq_sum_of_fintype, map_smul, map_sum]
  rw [Finset.sum_congr rfl fun q _ => h1 q, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Subgroup.index, nsmul_eq_mul, smul_eq_mul, inv_mul_cancel_left₀ hc]

end General

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.ConjPlace in
theorem UpperTheory.satake_inv_mul_char_eq_of_similitude_pairing :
    ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (w : HeightOneSpectrum (𝓞 F)) (V : Type) [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion F)) V), GlobalTheory.PRep.IsSmooth ρ → ∀ (χ : HChar F), χ.UnrAt w →
        ∀ (β : V →ₗ[ℂ] V →ₗ[ℂ] ℂ), (∀ x, (∀ y, β x y = 0) → x = 0) →
        (∀ g x y, β (ρ g x) (ρ g y) = ((χ.loc w (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * β x y) →
        ∀ B : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL w ρ B → (B.map (·⁻¹)).map (· * χ.val w) = B := by
  intro E _ _ n w V _ _ ρ hρ χ hχ β hβ hi B hB
  classical
  obtain ⟨x, hx⟩ := hB.exists_vec
  have hd : ∀ k ∈ KGL w (n := n), ((χ.loc w (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) = 1 := fun k hk => by
    rw [hχ _ (GlobalTheory.SphGal.isUnitAt_det_of_mem hk), Units.val_one]
  have hKc : IsCompact (KGL w (n := n) : Set (GL (Fin n) (w.adicCompletion E))) :=
    GlobalTheory.LFun.IntPtsUnitary.isCompact_GLint _ (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers E w)
  obtain ⟨y₀, hy₀⟩ : ∃ y, β x y ≠ 0 := by
    by_contra hn
    exact hx.1 (hβ x fun y => by_contra fun h => hn ⟨y, h⟩)
  obtain ⟨y, hyK, hy⟩ := exists_fixed_pair hρ hKc (β x) (fun k hk v => by
    have := hi k x v
    rwa [GlobalTheory.LGrp.mem_fixed.1 hx.2.1 k hk, hd k hk, one_mul] at this) y₀
  have hne : β x y ≠ 0 := hy ▸ hy₀
  have hy' := hB.2 y hyK fun h0 => hne (by rw [h0, map_zero])
  let c := RingEquiv.refl (w.adicCompletion E)
  have hc : ∀ a, Valued.v (c a) = Valued.v a := fun _ => rfl
  have hx' := isSatVecGL_invT c hc rfl hx
  have hK := mem_iff_invT (n := n) c (map_mem_Ov_iff c hc)
  obtain ⟨p, hp⟩ := exists_isUnifV w
  obtain ⟨ϖ, rfl⟩ : ∃ ϖ : (w.adicCompletion E)ˣ, ϖ = p :=
    ⟨Units.mk0 p fun e => by simp [IsUnifV, e] at hp, rfl⟩
  refine eq_of_satEig_eq (qV_ne_zero w) (by simpa using hx.2.2.1) hx.2.2.1 fun j hj => ?_
  have key := pair_heckeVec_comp (Final.GLintComm E w n) (Tj_mem_hecke hp j) hx.2.1 hyK β _ hd hi
    (GlobalTheory.LFun.ConjPlace.invT c n).symm.toMonoidHom (fun k hk => (hK _).2 (by simpa using hk))
    ((χ.val w : ℂ) ^ j)
    (fun g hg => by
      rw [Tj_apply] at hg
      obtain ⟨a, ha, b, hb, e⟩ : ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w),
          g = a * dGL n ϖ j * b := by
        by_contra hn
        exact hg (if_neg hn)
      refine ⟨a, ha, b, hb, _, (GlobalTheory.LFun.ConjPlace.invT c n).symm_apply_eq.2 (invT_dGL c ϖ j).symm, e, ?_⟩
      rw [GlobalTheory.SphGal.loc_det_of_Tj hχ hp hj, Units.val_pow_eq_pow_val]
      rw [Tj_apply, if_pos ⟨1, one_mem _, 1, one_mem _, by rw [one_mul, mul_one]; rfl⟩]
      exact one_ne_zero)
  rw [hx'.2.2.2 _ hp j hj, hy'.2.2.2 _ hp j hj, map_smul, map_smul, LinearMap.smul_apply,
    smul_eq_mul, smul_eq_mul, ← mul_assoc] at key
  rw [GlobalTheory.SphGal.satEig_map_mul]
  exact mul_right_cancel₀ hne key
end

section

open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V UpperTheory.V.Fb

private theorem one_le_ht {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ}
    (y : GL (Fin a) (TR.Rinf E)) : 1 ≤ TR.height y := by
  unfold TR.height
  have := norm_nonneg (TR.toL y.val)
  have := norm_nonneg (TR.toL (y⁻¹).val)
  linarith

private theorem unif {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ} (φ : TR.Sm E a)
    (hl : IsOpen {k | TR.finRep E a k φ = φ})
    (hg : ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ.1 (g * TR.infGL E a y)‖ ≤ C * TR.height y ^ N)
    {Ω : Set (AdelicGLn.FiniteAdelicGL E a)} (hΩ : IsCompact Ω) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ k ∈ Ω, ∀ y, ‖φ.1 (finGL E a k * TR.infGL E a y)‖ ≤ C * TR.height y ^ N := by
  refine hΩ.induction_on (p := fun S => ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ k ∈ S, ∀ y,
    ‖φ.1 (finGL E a k * TR.infGL E a y)‖ ≤ C * TR.height y ^ N) ⟨0, 0, le_rfl, fun _ h => h.elim⟩ ?_ ?_ ?_
  · rintro s t hst ⟨C, N, hC, h⟩
    exact ⟨C, N, hC, fun k hk => h k (hst hk)⟩
  · rintro s t ⟨C, N, hC, h⟩ ⟨C', N', hC', h'⟩
    refine ⟨max C C', max N N', hC.trans (le_max_left _ _), fun k hk y => ?_⟩
    have h1 := one_le_ht y
    rcases hk with hk | hk
    · exact (h k hk y).trans (mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ h1 (le_max_left _ _))
        (pow_nonneg (zero_le_one.trans h1) _) (hC.trans (le_max_left _ _)))
    · exact (h' k hk y).trans (mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ h1 (le_max_right _ _))
        (pow_nonneg (zero_le_one.trans h1) _) (hC.trans (le_max_left _ _)))
  · intro x _
    obtain ⟨C, N, h⟩ := hg (finGL E a x)
    have ho : IsOpen ((fun k : AdelicGLn.FiniteAdelicGL E a => x⁻¹ * k) ⁻¹' {k | TR.finRep E a k φ = φ}) :=
      hl.preimage (continuous_const.mul continuous_id)
    refine ⟨_, mem_nhdsWithin_of_mem_nhds (ho.mem_nhds ?_), |C|, N, abs_nonneg C, fun k hk y => ?_⟩
    · change TR.finRep E a (x⁻¹ * x) φ = φ
      rw [inv_mul_cancel, map_one]
      rfl
    · have e : φ.1 (finGL E a x * TR.infGL E a y * finGL E a (x⁻¹ * k)) = φ.1 (finGL E a x * TR.infGL E a y) :=
        congrFun (congrArg Subtype.val hk) _
      rw [mul_assoc, TR.infGL_comm, ← mul_assoc, ← map_mul, mul_inv_cancel_left] at e
      rw [e]
      exact (h y).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (zero_le_one.trans (one_le_ht y)) _))
end

section

noncomputable section

open MeasureTheory Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic
open GroundTheory.Automorphic.GodementJacquet
open scoped NNReal Classical ValuativeRel

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

theorem UpperTheory.local_zeta_integral_laurent_expansion :
    UpperTheory.V.Z.Gam.LdLaurent := by
  intro F _ _ _ _ m _ _ _ μ _ α c hc hzero Φ hΦ
  obtain ⟨A, hA⟩ := hΦ.exists_ordDet_ge
  obtain ⟨K, hK, hKc⟩ := hc.exists_compact_tile
  obtain ⟨B, hB⟩ := exists_valBall_of_isCompact (hK.image Units.continuous_val)
  obtain ⟨J, hJ⟩ := hΦ.exists_eq_zero_of_small B
  have hm : (0 : ℤ) < m := by
    have := NeZero.pos m
    omega
  let sh : ℤ → Set (GL (Fin m) F) := fun k => {g | ordDet g = k}
  refine ⟨Finset.Icc (-((m : ℤ) * A)) (J * m), fun k => ∫ g in sh k, Φ g * c g ∂μ, ?_⟩
  intro s hs
  have hint := hc.integrable_zeta μ hΦ hs
  have hmeas : ∀ k, MeasurableSet (sh k) := fun k => (isClopen_shell F m k).isClosed.measurableSet
  have hdisj : Pairwise (fun i j => Disjoint (sh i) (sh j)) := by
    intro i j hij
    exact Set.disjoint_left.2 fun g hi hj => hij (hi.symm.trans hj)
  have huniv : (⋃ k, sh k) = Set.univ := Set.iUnion_eq_univ_iff.2 fun g => ⟨ordDet g, rfl⟩
  have hsplit := integral_iUnion hmeas hdisj hint.integrableOn
  rw [huniv, setIntegral_univ] at hsplit
  rw [hsplit]
  have hshell : ∀ k, ∫ g in sh k, Φ g * detPow g s * c g ∂μ = (∫ g in sh k, Φ g * c g ∂μ) * qs F s ^ k := by
    intro k
    rw [← integral_mul_const]
    refine setIntegral_congr_fun (hmeas k) fun g hg => ?_
    have hg' : ordDet g = k := hg
    rw [detPow_eq_qs_zpow, hg']
    ring
  simp_rw [hshell]
  apply tsum_eq_sum
  intro k hk
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
  have hk0 : ∫ g in sh k, Φ g * c g ∂μ = 0 := by
    rcases hk with hk | hk
    · apply setIntegral_eq_zero_of_forall_eq_zero
      intro g hg
      have hg' : ordDet g = k := hg
      have hΦ0 : Φ g = 0 := by
        by_contra hne
        have := hA g hne
        linarith
      rw [hΦ0, zero_mul]
    · have hcongr : ∫ g in sh k, Φ g * c g ∂μ = ∫ g in sh k, Φ 0 * c g ∂μ := by
        refine setIntegral_congr_fun (hmeas k) fun g hg => ?_
        have hg' : ordDet g = k := hg
        by_cases hcg : c g = 0
        · simp [hcg]
        · congr 1
          have hgh : centralUnif F m ^ (k / (m : ℤ)) * (centralUnif F m ^ (-(k / (m : ℤ))) * g) = g := by
            rw [← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
          have hordh : ordDet (centralUnif F m ^ (-(k / (m : ℤ))) * g) = k % m := by
            rw [ordDet_centralUnif_zpow_mul, hg', Int.emod_def]
            ring
          have htile : centralUnif F m ^ (-(k / (m : ℤ))) * g ∈ tile F m 0 := by
            simp only [tile, Set.mem_setOf_eq, zero_mul, zero_add]
            rw [hordh]
            exact ⟨Int.emod_nonneg _ hm.ne', Int.emod_lt_of_pos _ hm⟩
          have hch : c (centralUnif F m ^ (-(k / (m : ℤ))) * g) ≠ 0 := by
            rw [← hgh, hc.zpow_mul] at hcg
            exact right_ne_zero_of_mul hcg
          have hhK := hKc _ htile hch
          have hball := hB _ ⟨_, hhK, rfl⟩
          have hjJ : J ≤ k / (m : ℤ) := Int.le_ediv_of_mul_le hm hk.le
          rw [← hgh]
          exact hJ _ hjJ _ hball
      rw [hcongr, integral_const_mul, hzero k, mul_zero]
  rw [hk0, zero_mul]
end
end
