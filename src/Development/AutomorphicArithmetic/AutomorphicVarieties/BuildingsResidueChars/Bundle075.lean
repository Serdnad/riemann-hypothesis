module

import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta.EtaOK
import Formalism.DoubleCosetMeasures.Statement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle296
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle074
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle306
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle307
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle322
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle004
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.ToIdeleSq
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic

@[expose] public section

section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem unr_cancel {a b : kˣ →* ℂˣ} (ha : IsUnram a) (hab : IsUnram (a * b)) : IsUnram b := fun x hx => by
  have h := hab x hx
  rwa [MonoidHom.mul_apply, ha x hx, one_mul] at h

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem unr_inv {a : kˣ →* ℂˣ} (ha : IsUnram a) : IsUnram a⁻¹ := fun x hx => by
  rw [MonoidHom.inv_apply, ha x hx, inv_one]


private theorem lin_zero (a : kˣ →* ℂˣ) : (lin a).eval 0 = 1 := by
  unfold lin
  split_ifs <;> simp

end Loc

private theorem unrAt_iff {F : Type} [Field F] [NumberField F] (χ : HChar F) (w : HeightOneSpectrum (𝓞 F)) :
    χ.UnrAt w ↔ IsUnram (χ.loc w) := by
  haveI : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  refine forall_congr' fun x => imp_congr_left ?_
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion F)) Valued.v).eq_one_iff_eq_one.symm

private theorem unr_iff (u : Ad3.Pl) (a : (u.adicCompletion ℚ)ˣ →* ℂˣ) : IsUnramifiedChar a ↔ IsUnram a := by
  haveI : (Valued.v : Valuation (u.adicCompletion ℚ) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [isUnramifiedChar_iff]
  refine forall_congr' fun x => imp_congr_left ?_
  rw [Ad3P.DihedralUnramifiedPlaces.ord_eq u x.ne_zero, neg_eq_zero,
    (ValuativeRel.isEquiv (ValuativeRel.valuation (u.adicCompletion ℚ)) Valued.v).eq_one_iff_eq_one]
  have h0 : Valued.v (x : u.adicCompletion ℚ) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  constructor
  · intro h
    rw [← WithZero.exp_log h0, h, WithZero.exp_zero]
  · intro h
    rw [h, WithZero.log_one]

private theorem under_eq {K : Type} [Field K] [NumberField K] {p : Ad3.Pl} (w : PlacesOver K p) : w.1.under (𝓞 ℚ) = p :=
  HeightOneSpectrum.ext w.2.over.symm

private theorem exists_above (K : Type) [Field K] [NumberField K] (S : Finset Ad3.Pl) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), ∀ w, w ∈ T ↔ w.under (𝓞 ℚ) ∈ S := by
  refine ⟨S.biUnion fun p => (Finset.univ : Finset (PlacesOver K p)).map (Function.Embedding.subtype _), fun w => ?_⟩
  simp only [Finset.mem_biUnion, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hp, w', rfl⟩
    change w'.1.under (𝓞 ℚ) ∈ S
    rwa [under_eq]
  · exact fun h => ⟨_, h, ⟨w, ⟨rfl⟩⟩, rfl⟩

private theorem tri_pow (a x : ℂˣ) (f : ℕ) :
    ((({a ^ f, 1, (a ^ f)⁻¹} : Multiset ℂˣ).map (· * x ^ f)).map fun b : ℂˣ => (b : ℂ)) = (tri a x).map (· ^ f) := by
  simp [tri, mul_pow]
end

section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

private theorem unr_of {η : HeckeCharacter ℚ} {v : Ad3.Pl} (h : (toH η).UnrAt v) :
    IsUnramifiedChar (localChar η v) := by
  refine isUnramifiedChar_iff.2 fun x hx => ?_
  rw [← Ad3P.DihedralUnramifiedPlaces.loc_eq]
  apply h x
  show Valued.v (x : Ad3.Qv v) = 1
  rw [Ad3P.DihedralUnramifiedPlaces.ord_eq v x.ne_zero, neg_eq_zero] at hx
  have h0 : Valued.v (x : Ad3.Qv v) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  rw [← WithZero.exp_log h0, hx, WithZero.exp_zero]

private theorem unr_mul {c η : HeckeCharacter ℚ} {v : Ad3.Pl} (h₁ : IsUnramifiedChar (localChar c v))
    (h₂ : IsUnramifiedChar (localChar η v)) : IsUnramifiedChar (localChar (c * η) v) := by
  refine isUnramifiedChar_iff.2 fun x hx => ?_
  have e : localChar (c * η) v x = localChar c v x * localChar η v x := Units.ext rfl
  rw [e, isUnramifiedChar_iff.1 h₁ x hx, isUnramifiedChar_iff.1 h₂ x hx, one_mul]

private theorem val_mul' (c η : HeckeCharacter ℚ) (v : Ad3.Pl) :
    (toH (c * η)).val v = (toH c).val v * (toH η).val v := Units.ext rfl

private theorem norm_val (c : HeckeCharacter ℚ) (v : Ad3.Pl) : ‖((toH c).val v : ℂ)‖ = 1 :=
  Circle.norm_coe _

private theorem tri_mul (a x y : ℂˣ) : tri a (x * y) = (tri a x).map (· * (y : ℂ)) := by
  simp [tri, mul_assoc]
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.BasicNotions
open scoped TensorProduct

theorem UpperTheory.exists_fixed_vector_of_local_fixed_vectors :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : Submodule ℂ (UA E n → ℂ)), IsAutRepU σ → ∀ K : Subgroup (UA E n), K ≤ finU (E := E) (n := n) → (∀ w, ∀ k ∈ K, GlobalTheory.DefU.LocRet.ret0 w n k ∈ K) → ∀ T : Set (HeightOneSpectrum (𝓞 E)), T.Finite → (∀ k ∈ K, ∀ u ∉ T, cLoc u k ∈ GlobalTheory.LFun.KGL u (n := n)) → (∀ w, ∃ φ ∈ σ, φ ≠ 0 ∧ ∀ k ∈ K, k ∈ locU n w → RU E n k φ = φ) → ∃ φ ∈ σ, φ ≠ 0 ∧ ∀ k ∈ K, RU E n k φ = φ := by
  classical
  intro E _ _ _ n σ hσ K hKf hKr T hT hKT h
  let P : Finset (HeightOneSpectrum (𝓞 E)) → UA E n → Prop := fun S k =>
    k ∈ K ∧ ∀ w ∈ S, ∀ u : HeightOneSpectrum (𝓞 E),
      u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → cLoc u k = 1
  have hR : ∀ (a b : UA E n) (φ : UA E n → ℂ), RU E n (a * b) φ = RU E n a (RU E n b φ) := fun a b φ => by
    rw [map_mul, Module.End.mul_apply]
  have key : ∀ S : Finset (HeightOneSpectrum (𝓞 E)), (∃ φ ∈ σ, φ ≠ 0 ∧ ∀ k, P S k → RU E n k φ = φ) →
      ∃ φ ∈ σ, φ ≠ 0 ∧ ∀ k, P ∅ k → RU E n k φ = φ := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact id
    | insert w S hw ih =>
      rintro ⟨v, hvσ, hv0, hv⟩
      let W : Submodule ℂ (UA E n → ℂ) := σ ⊓ ⨅ k : {k // P (insert w S) k}, LinearMap.ker (RU E n k.1 - 1)
      have hWm : ∀ x, x ∈ W ↔ x ∈ σ ∧ ∀ k, P (insert w S) k → RU E n k x = x := fun x => by
        simp only [W, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
          Module.End.one_apply, sub_eq_zero, Subtype.forall]
      obtain ⟨φ, hφ, hφ0, hφK⟩ := h w
      obtain ⟨x, hxW, hx0, hx⟩ := UpperTheory.exists_fixed_vector_in_locally_stable_subspace E n σ hσ w (K ⊓ locU n w) inf_le_right
        ⟨φ, hφ, hφ0, fun k hk => hφK k hk.1 hk.2⟩ W inf_le_left
        (fun e => hv0 (by
          have := (hWm v).2 ⟨hvσ, hv⟩
          rwa [e, Submodule.mem_bot] at this))
        (fun g hg x hx => (hWm _).2 ⟨hσ.stable g x ((hWm x).1 hx).1, fun k hk => by
          have e : k * g = g * k := by
            refine Subtype.ext (GlobalTheory.DefU.LocRet.ga_ext' ?_ fun u => ?_)
            · simp only [Subgroup.coe_mul, map_mul, GlobalTheory.DefU.LocRet.mem_locU_inf hg, one_mul, mul_one]
            · by_cases hu : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))
              · have h1 : Matrix.GeneralLinearGroup.map ((pLoc E u).comp (pFin E)) k.1 = 1 :=
                  hk.2 w (Finset.mem_insert_self _ _) u hu
                simp only [Subgroup.coe_mul, map_mul, h1, one_mul, mul_one]
              · simp only [Subgroup.coe_mul, map_mul, GlobalTheory.DefU.LocRet.mem_locU_ne hg hu, one_mul, mul_one]
          rw [← hR, e, hR, ((hWm x).1 hx).2 k hk]⟩)
      refine ih ⟨x, ((hWm x).1 hxW).1, hx0, fun k hk => ?_⟩
      have h1 : GlobalTheory.DefU.LocRet.ret0 w n k ∈ K := hKr w k hk.1
      have h2 : P (insert w S) (k * (GlobalTheory.DefU.LocRet.ret0 w n k)⁻¹) := by
        refine ⟨mul_mem hk.1 (inv_mem h1), fun w' hw' u hu => ?_⟩
        by_cases huw : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))
        · have h3 : cLoc u (GlobalTheory.DefU.LocRet.ret0 w n k) = cLoc u k := GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_eq huw k
          rw [map_mul, map_inv, h3, mul_inv_cancel]
        · have h3 : cLoc u (GlobalTheory.DefU.LocRet.ret0 w n k) = 1 := GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_ne huw k
          rcases Finset.mem_insert.1 hw' with rfl | hw'
          · exact absurd hu huw
          · rw [map_mul, map_inv, h3, hk.2 w' hw' u hu, inv_one, mul_one]
      have h3 : RU E n (GlobalTheory.DefU.LocRet.ret0 w n k) x = x := hx _ ⟨h1, GlobalTheory.DefU.LocRet.unitaryAdelicLocalRetractionEnd_mem_localPoints k⟩
      have h4 := ((hWm x).1 hxW).2 _ h2
      rwa [← h3, ← hR, inv_mul_cancel_right, h3] at h4
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff σ).1 hσ.ne_bot
  obtain ⟨S, hS⟩ := UpperTheory.finiteAdelicUnitary_mem_nhds_one_of_trivial_at_places E n T hT _ ((hσ.aut v hv).level.mem_nhds (x := 1) (by simp))
  obtain ⟨x, hx, hx0, hxK⟩ := key S ⟨v, hv, hv0, fun k hk =>
    hS ⟨k, hKf hk.1⟩ (hKT k hk.1) fun u hu => hk.2 u hu u rfl⟩
  exact ⟨x, hx, hx0, fun k hk => hxK k ⟨hk, by simp⟩⟩
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU

theorem UpperTheory.exists_compact_fundamental_set_unitary :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∃ C : Set (UA E n), IsCompact C ∧ ∀ g, ∃ γ ∈ ratU E n, ∃ c ∈ C, g = γ * c := by
  intro E _ _ _ n
  classical
  obtain ⟨K, hKo, hKc⟩ := UpperTheory.exists_isOpen_isCompact_subgroup_finiteAdelicUnitary E n
  obtain ⟨S, hS⟩ := GlobalTheory.T.definiteUnitary_classSet_finite E n K hKo
  haveI : CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) := GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ
  haveI : ∀ v : InfinitePlace E, CompactSpace (embU n v.embedding) := fun v => by
    obtain ⟨e, -⟩ := GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E n v.embedding
    exact e.toHomeomorph.symm.compactSpace
  let P : (∀ v : InfinitePlace E, embU n v.embedding) → UA E n :=
    fun y => (Finset.univ.toList.map fun v => (y v : UA E n)).prod
  have hP : Continuous P :=
    continuous_list_prod _ fun v _ => continuous_subtype_val.comp (continuous_apply v)
  have hPc : IsCompact (Set.range P) := isCompact_range hP
  have hKc' : IsCompact (Subtype.val '' (K : Set (finU (E := E) (n := n)))) := hKc.image continuous_subtype_val
  refine ⟨_, (S.finite_toSet.isCompact.mul hPc).mul hKc', fun g => ?_⟩
  obtain ⟨γ, hγ, s, hs, x, hx, k, hk, e⟩ := hS g
  obtain ⟨y, hy, -, hyx⟩ := GlobalTheory.T.definiteUnitaryInfinitePoint_eq_list_prod_placeParts E n x hx
  refine ⟨γ, hγ, s * x * k, Set.mul_mem_mul (Set.mul_mem_mul hs ⟨fun v => ⟨y v, hy v⟩, hyx⟩) ⟨k, hk, rfl⟩, ?_⟩
  rw [e, mul_assoc, mul_assoc, mul_assoc]
end
