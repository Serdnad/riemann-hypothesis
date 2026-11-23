module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LeAdicClosure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle031
public import Mathlib.RingTheory.KrullDimension.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle028
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle033
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocRho
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PointLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MonMemPow
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle002

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem residue_eq_map_algebraMap_comp_res_of_isCO {O' C : Type} [CommRing O'] [IsLocalRing O'] [CommRing C] [Algebra O' C]
    [IsCO O' C] [IsLocalHom (algebraMap O' C)] :
    IsLocalRing.residue C =
      (IsLocalRing.ResidueField.map (algebraMap O' C)).comp (res O' C : C →+* ResidueField O') := by
  ext z
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O') z
  have h1 : (res O' C) z = (res O' C) (algebraMap O' C a) := by
    rw [← sub_eq_zero, ← map_sub, res_eq_zero_iff]
    exact ha
  have h2 : IsLocalRing.residue C z = IsLocalRing.residue C (algebraMap O' C a) := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact ha
  rw [RingHom.comp_apply, RingHom.coe_coe, h1, h2, AlgHom.commutes]
  exact (IsLocalRing.ResidueField.map_residue _ a).symm

private theorem nRep_isBar_of_isBar_comp_map {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ}
    {K K' : Type} [Field K] [CommRing K'] [Nontrivial K'] (f : k →+* K) (j : K →+* K')
    (σ : NRep F n K) (h : NRep.IsBar (j.comp f) (NRep.map j σ)) : NRep.IsBar f σ := by
  unfold NRep.IsBar at h ⊢
  exact ⟨fun g i => j.injective (h.1 g i), fun v i g => j.injective (h.2 v i g)⟩

theorem UpperTheory.V.Fr.pr_res :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), (∃ φ : ResidueField O →+* ResidueField L.O', (L.ρ.bar L.O').IsBar φ) ∧ ((∀ g, UpT ((L.ρ.bar L.O').r g)) ∨ ∀ g, UpT ((L.ρ.bar L.O').r g)ᵀ) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x L
  have hOloc : IsLocalHom (algebraMap O L.O') := by
    refine ⟨fun a ha => ?_⟩
    by_contra h
    have hm : algebraMap O L.O' a ∈ maximalIdeal L.O' := by
      rw [← L.unr]
      exact Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal a).mpr h)
    exact (IsLocalRing.mem_maximalIdeal _).mp hm ha
  haveI : IsLocalHom (algebraMap L.O' L.R) := IsCO.isLocalHom
  let f0 : ResidueField O →+* ResidueField L.O' := IsLocalRing.ResidueField.map (algebraMap O L.O')
  let jR : ResidueField L.O' →+* ResidueField L.R :=
    IsLocalRing.ResidueField.map (algebraMap L.O' L.R)
  have hloc := loc_rho hF hn S x L
  refine ⟨⟨f0, ?_⟩, ?_⟩
  · have hfR : IsResMap O L.R (jR.comp f0) := by
      intro a
      show jR (f0 (IsLocalRing.residue O a)) = _
      rw [IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue,
        IsScalarTower.algebraMap_apply O L.O' L.R a]
    have hbR := hloc.2.1 _ hfR
    rw [residue_eq_map_algebraMap_comp_res_of_isCO (O' := L.O') (C := L.R)] at hbR
    exact nRep_isBar_of_isBar_comp_map f0 jR _ hbR
  · by_cases hP : S.u.triP ≤ x
    · left
      have hle : L.ρ.triP ≤ maximalIdeal L.R := by
        rw [(hloc.2.2.1 (maximalIdeal L.R)).1]
        show S.u.triP ≤ Ideal.comap (L.ι : S.A →+* L.R) (maximalIdeal L.R)
        rw [L.lies]
        exact hP
      intro g i j hji
      have hm : L.ρ.r g i j ∈ maximalIdeal L.R := by
        refine hle ?_
        unfold NRep.triP
        exact Ideal.subset_span ⟨g, i, j, hji, rfl⟩
      show res L.O' L.R (L.ρ.r g i j) = 0
      exact (res_eq_zero_iff _ _ _).mpr hm
    · right
      have hle := (hloc.2.2.2 hP).2
      intro g i j hji
      have hm : L.ρ.r g j i ∈ maximalIdeal L.R := by
        refine hle ?_
        unfold NRep.triM
        exact Ideal.subset_span ⟨g, j, i, hji, rfl⟩
      show res L.O' L.R (L.ρ.r g j i) = 0
      exact (res_eq_zero_iff _ _ _).mpr hm
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem residue_eq_residueField_map_comp_res {O' C : Type} [CommRing O'] [IsLocalRing O'] [CommRing C] [Algebra O' C]
    [IsCO O' C] [IsLocalHom (algebraMap O' C)] :
    IsLocalRing.residue C =
      (IsLocalRing.ResidueField.map (algebraMap O' C)).comp (res O' C : C →+* ResidueField O') := by
  ext z
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O') z
  have h1 : (res O' C) z = (res O' C) (algebraMap O' C a) := by
    rw [← sub_eq_zero, ← map_sub, res_eq_zero_iff]
    exact ha
  have h2 : IsLocalRing.residue C z = IsLocalRing.residue C (algebraMap O' C a) := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact ha
  rw [RingHom.comp_apply, RingHom.coe_coe, h1, h2, AlgHom.commutes]
  exact (IsLocalRing.ResidueField.map_residue _ a).symm

private theorem nRep_isBar_comp_map_iff {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ}
    {K K' : Type} [Field K] [CommRing K'] [Nontrivial K'] (f : k →+* K) (j : K →+* K')
    (σ : NRep F n K) : NRep.IsBar (j.comp f) (NRep.map j σ) ↔ NRep.IsBar f σ := by
  unfold NRep.IsBar
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun g i => j.injective (h1 g i), fun v i g => j.injective (h2 v i g)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun g i => congrArg j (h1 g i), fun v i g => congrArg j (h2 v i g)⟩

theorem UpperTheory.V.Fr.def_iso :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), ∀ (C : Type) [CommRing C] [Algebra L.O' C] [IsCO L.O' C] (ρ : NRep F n C), ρ.Cont (maximalIdeal C) → ρ.map (res L.O' C : C →+* ResidueField L.O') = L.ρ.map (res L.O' L.R : L.R →+* ResidueField L.O') → ∃! g : L.R →ₐ[L.O'] C, L.ρ.map (g : L.R →+* C) = ρ := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x L C _ _ _ ρ hc hres
  have hOloc : IsLocalHom (algebraMap O L.O') := by
    refine ⟨fun a ha => ?_⟩
    by_contra h
    have hm : algebraMap O L.O' a ∈ maximalIdeal L.O' := by
      rw [← L.unr]
      exact Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal a).mpr h)
    exact (IsLocalRing.mem_maximalIdeal _).mp hm ha
  haveI : IsLocalHom (algebraMap L.O' C) := IsCO.isLocalHom
  haveI : IsLocalHom (algebraMap L.O' L.R) := IsCO.isLocalHom
  letI : Algebra O C := ((algebraMap L.O' C).comp (algebraMap O L.O')).toAlgebra
  haveI : IsScalarTower O L.O' C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hCloc : IsLocalHom (algebraMap O C) :=
    inferInstanceAs (IsLocalHom ((algebraMap L.O' C).comp (algebraMap O L.O')))
  have hCL : UpperTheory.V.CA.IsCL O C := by
    refine ⟨inferInstance, IsCO.complete (O := L.O'), hCloc, ?_⟩
    let φ : L.O' →ₐ[O] ResidueField C :=
      (IsScalarTower.toAlgHom O C (ResidueField C)).comp (IsScalarTower.toAlgHom O L.O' C)
    refine Module.Finite.of_surjective φ.toLinearMap ?_
    intro y
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := L.O') z
    refine ⟨a, ?_⟩
    show IsLocalRing.residue C (algebraMap L.O' C a) = IsLocalRing.residue C z
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ← neg_sub]
    exact neg_mem ha
  let f0 : ResidueField O →+* ResidueField L.O' := IsLocalRing.ResidueField.map (algebraMap O L.O')
  let jC : ResidueField L.O' →+* ResidueField C := IsLocalRing.ResidueField.map (algebraMap L.O' C)
  let jR : ResidueField L.O' →+* ResidueField L.R :=
    IsLocalRing.ResidueField.map (algebraMap L.O' L.R)
  have hfC : IsResMap O C (jC.comp f0) := by
    intro a
    show jC (f0 (IsLocalRing.residue O a)) = _
    rw [IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue]
    rfl
  have hfR : IsResMap O L.R (jR.comp f0) := by
    intro a
    show jR (f0 (IsLocalRing.residue O a)) = _
    rw [IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue,
      IsScalarTower.algebraMap_apply O L.O' L.R a]
  have hbR := (loc_rho hF hn S x L).2.1 _ hfR
  rw [residue_eq_residueField_map_comp_res (O' := L.O') (C := L.R)] at hbR
  have hσ : NRep.IsBar f0 (NRep.map (res L.O' L.R : L.R →+* ResidueField L.O') L.ρ) :=
    (nRep_isBar_comp_map_iff f0 jR _).mp hbR
  have hbar : NRep.IsBar (jC.comp f0) (NRep.map (IsLocalRing.residue C) ρ) := by
    rw [residue_eq_residueField_map_comp_res (O' := L.O') (C := C)]
    show NRep.IsBar (jC.comp f0) (NRep.map jC (NRep.map (res L.O' C : C →+* ResidueField L.O') ρ))
    rw [hres]
    exact (nRep_isBar_comp_map_iff f0 jC _).mpr hσ
  obtain ⟨ξ, hξ, hξx⟩ := point_loc hF hn S C hCL (jC.comp f0) hfC ρ hc hbar
  have hx0 : S.x0 ≤ x := by
    unfold Space.x0
    exact Ideal.map_le_iff_le_comap.mpr (loc_flat hF hn S x L).2.2
  let ξ1 : S.A →ₐ[O] ResidueField L.O' := ((res L.O' C).restrictScalars O).comp ξ
  let ξ2 : S.A →ₐ[O] ResidueField L.O' := ((res L.O' L.R).restrictScalars O).comp L.ι
  have h12 : ξ1 = ξ2 := by
    refine ext_A hF hn S (ResidueField L.O') ξ1 ξ2 ?_ ?_ ?_
    · exact (congrArg (NRep.map (res L.O' C : C →+* ResidueField L.O')) hξ).trans hres
    · intro a ha
      refine Ideal.mem_comap.mpr ?_
      show res L.O' C (ξ a) ∈ _
      rw [(res_eq_zero_iff L.O' C (ξ a)).mpr (hξx ha)]
      exact zero_mem _
    · intro a ha
      have hm : a ∈ Ideal.comap (L.ι : S.A →+* L.R) (maximalIdeal L.R) := by
        rw [L.lies]
        exact hx0 ha
      refine Ideal.mem_comap.mpr ?_
      show res L.O' L.R (L.ι a) ∈ _
      rw [(res_eq_zero_iff L.O' L.R (L.ι a)).mpr hm]
      exact zero_mem _
  obtain ⟨g, hg, huniq⟩ := L.univ C ξ (fun a => AlgHom.congr_fun h12 a)
  have hgι : (g : L.R →+* C).comp (L.ι : S.A →+* L.R) = (ξ : S.A →+* C) := RingHom.ext hg
  refine ⟨g, ?_, fun g' hg' => huniq g' ?_⟩
  · show NRep.map ((g : L.R →+* C).comp (L.ι : S.A →+* L.R)) S.u = ρ
    rw [hgι]
    exact hξ
  · let ξ' : S.A →ₐ[O] C := (g'.restrictScalars O).comp L.ι
    have h' : ξ' = ξ := by
      refine ext_A hF hn S C ξ' ξ ?_ ?_ hξx
      · exact hg'.trans hξ.symm
      · intro a ha
        have hm : a ∈ Ideal.comap (L.ι : S.A →+* L.R) (maximalIdeal L.R) := by
          rw [L.lies]
          exact hx0 ha
        refine Ideal.mem_comap.mpr ?_
        show g' (L.ι a) ∈ maximalIdeal C
        rw [← res_eq_zero_iff L.O' C, res_map]
        exact (res_eq_zero_iff L.O' L.R _).mpr hm
    intro a
    exact AlgHom.congr_fun h' a
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.local_deformation_trace_mod_maximal :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), (maximalIdeal O).map (algebraMap O L.R) ≤ maximalIdeal L.R ∧ (∀ (g : F.G0) (i : Fin n), F.Ψ g = 1 → L.ρ.r g i i - 1 ∈ maximalIdeal L.R) ∧ ∀ (P : Ideal L.R) [IsLocalRing (L.R ⧸ P)], (maximalIdeal O).map (algebraMap O L.R) ≤ P → Finite (ResidueField (L.R ⧸ P)) ∧ (∀ y ∈ maximalIdeal L.R, Ideal.Quotient.mk P y ∈ maximalIdeal (L.R ⧸ P)) ∧ (L.ρ.map (Ideal.Quotient.mk P)).Cont (maximalIdeal (L.R ⧸ P)) ∧ ∃ f : ResidueField O →+* L.R ⧸ P, (∀ a : O, Ideal.Quotient.mk P (algebraMap O L.R a) = f (residue O a)) ∧ ((L.ρ.map (Ideal.Quotient.mk P)).map (residue (L.R ⧸ P))).IsBar ((residue (L.R ⧸ P)).comp f) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x L
  obtain ⟨hc, hb, -⟩ := UpperTheory.V.Fr.loc_rho hF hn S x L
  have hm : ∀ a ∈ maximalIdeal O, algebraMap O L.R a ∈ maximalIdeal L.R := fun a ha => by
    have h1 : algebraMap O L.O' a ∈ maximalIdeal L.O' := L.unr ▸ Ideal.mem_map_of_mem _ ha
    rw [IsScalarTower.algebraMap_apply O L.O' L.R]
    exact map_nonunit (algebraMap L.O' L.R) _ h1
  haveI hloc : IsLocalHom (algebraMap O L.R) := ⟨fun a ha => by
    by_contra hna
    exact hm a hna ha⟩
  have hb0 := hb (ResidueField.map (algebraMap O L.R)) fun a => ResidueField.map_residue _ _
  refine ⟨Ideal.map_le_iff_le_comap.2 hm, fun g i hg => ?_, fun P _ hP => ?_⟩
  · have h := hb0.1 g i
    rw [hg, NRep.map_r] at h
    rw [← residue_eq_zero_iff, map_sub, h]
    simp
  haveI hlocP : IsLocalHom (Ideal.Quotient.mk P) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hmP : ∀ y ∈ maximalIdeal L.R, Ideal.Quotient.mk P y ∈ maximalIdeal (L.R ⧸ P) :=
    fun y hy => map_nonunit (Ideal.Quotient.mk P) y hy
  have hle : ∀ N : ℕ, maximalIdeal L.R ^ N ≤ (maximalIdeal (L.R ⧸ P) ^ N).comap (Ideal.Quotient.mk P) := fun N =>
    le_trans (Ideal.pow_right_mono (fun y hy => hmP y hy) N) (Ideal.le_comap_pow _ N)
  refine ⟨?_, hmP, ⟨fun i j N => ?_, fun v i N => ?_⟩, ?_⟩
  · haveI : Finite (ResidueField L.R) := Finite.of_surjective _ (resMap_bijective L.O' L.R).2
    refine Finite.of_surjective (ResidueField.map (Ideal.Quotient.mk P)) fun y => ?_
    obtain ⟨y, rfl⟩ := residue_surjective y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨residue _ y, ResidueField.map_residue _ _⟩
  · exact (hc.1 i j N).comp (Ideal.quotientMap _ (Ideal.Quotient.mk P) (hle N))
  · exact (hc.2 v i N).comp (Ideal.quotientMap _ (Ideal.Quotient.mk P) (hle N))
  · let f : ResidueField O →+* L.R ⧸ P :=
      Ideal.Quotient.lift (maximalIdeal O) ((Ideal.Quotient.mk P).comp (algebraMap O L.R))
        fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (hP (Ideal.mem_map_of_mem _ ha))
    have hf : ∀ a : O, Ideal.Quotient.mk P (algebraMap O L.R a) = f (residue O a) := fun a => rfl
    have key : ∀ (y : L.R) (t : ResidueField O), residue L.R y = ResidueField.map (algebraMap O L.R) t →
        residue (L.R ⧸ P) (Ideal.Quotient.mk P y) = residue (L.R ⧸ P) (f t) := fun y t h => by
      obtain ⟨a, rfl⟩ := residue_surjective t
      rw [← hf, ← ResidueField.map_residue (Ideal.Quotient.mk P), h, ResidueField.map_residue,
        ResidueField.map_residue]
    exact ⟨f, hf, fun g i => key _ _ (hb0.1 g i), fun v i g => key _ _ (hb0.2 v i g)⟩
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.seedpt :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (p : Ideal S.B) (ξ : Ideal S.A), p.IsPrime → ξ.IsPrime → S.u.TI ξ → p ≤ S.π ξ → ∃ x : PrimeSpectrum S.A, x.asIdeal.IsMaximal ∧ x ∈ S.BB ∧ ∀ L : S.Loc x.asIdeal, ∃ P : Ideal L.R, P.IsPrime ∧ L.ρ.TI P ∧ L.π P = p ∧ ringKrullDim (L.R ⧸ P) = ringKrullDim (S.B ⧸ p) + 1 := by
  intro l _ O _ _ _ _ F C₀ n hF hn S p ξ hp hξ hTI hpξ
  obtain ⟨η, hηp, hhom, hπ, hTIη, htd⟩ := frobenius_corner_lift_two_to_three hF hn S p ξ hp hξ hTI hpξ
  have hTIη' := hTIη
  unfold NRep.TI NRep.OffTri at hTIη'
  obtain ⟨x, hxmax, hxBB, hηx⟩ := l41 hF hn S η hηp hhom hTIη'.1.1
  refine ⟨x, hxmax, hxBB, fun L => ?_⟩
  have htd' : S.td η = ((1 : ℕ) : _) := by
    rw [htd]
    rfl
  obtain ⟨P, hP, himP, hdim⟩ := (loc_dim hF hn S x.asIdeal L).2 η hηp hηx 1 htd'
  have hloc := (loc_rho hF hn S x.asIdeal L).2.2.1 P
  rw [himP] at hloc
  refine ⟨P, hP, ?_, ?_, ?_⟩
  · unfold NRep.TI NRep.OffTri
    exact ⟨⟨fun h => hTIη'.1.1 (hloc.1.mp h), fun h => hTIη'.1.2 (hloc.2.1.mp h)⟩,
      fun h3 h => hTIη'.2 h3 (hloc.2.2.mp h)⟩
  · show S.π (L.im P) = p
    rw [himP, hπ]
  · rw [hdim, hπ]
    norm_num
end
