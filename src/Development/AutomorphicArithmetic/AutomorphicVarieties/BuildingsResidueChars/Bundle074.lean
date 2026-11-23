module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle727
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle337
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle296
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle299
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle067
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle069
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle071
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.ConjFlag
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.DiagGsp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.ShapeQ
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PicardGroup
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.BasicNotions
open scoped TensorProduct

theorem UpperTheory.exists_fixed_vector_in_locally_stable_subspace :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : Submodule ℂ (UA E n → ℂ)), IsAutRepU σ → ∀ (w : HeightOneSpectrum (𝓞 E)) (K : Subgroup (UA E n)), K ≤ locU n w → (∃ φ ∈ σ, φ ≠ 0 ∧ ∀ k ∈ K, RU E n k φ = φ) → ∀ W : Submodule ℂ (UA E n → ℂ), W ≤ σ → W ≠ ⊥ → (∀ x ∈ locU n w, ∀ φ ∈ W, RU E n x φ ∈ W) → ∃ φ ∈ W, φ ≠ 0 ∧ ∀ k ∈ K, RU E n k φ = φ := by
  intro E _ _ _ n π hπ w K hK hu W hWπ hW0 hW
  obtain ⟨φ, hφ, hφ0, hφK⟩ := hu
  let Ψ : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
  obtain ⟨τ, -, hirr, f, hf0, hfm, hf⟩ := GlobalTheory.DefU.LocAdm.exists_admissible_comp E n Ψ w
  let ρ : Representation ℂ (locU n w) Ψ.V := Ψ.rep.comp (locU n w).subtype
  let F : Representation.IntertwiningMap τ.ρ ρ :=
    ⟨f.codRestrict _ hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h => hf0 (LinearMap.ext fun v => by
    have := congrArg Subtype.val (DFunLike.congr_fun h v)
    exact this)
  obtain ⟨r, -, -, hr⟩ := GlobalTheory.DefU.LocRet.exists_ret E n w
  have htop := (GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (locU n w) Ψ.V τ.V τ.V Ψ.rep (locU n w).subtype
    τ.ρ τ.ρ Ψ.isIrreducible_rep hirr hirr (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1
  have hfi : ∀ (i : Representation.IntertwiningMap τ.ρ ρ) g u, i.toLinearMap (τ.ρ g u) = ρ g (i.toLinearMap u) :=
    fun i g u => Representation.IntertwiningMap.isIntertwining _ _ i g u
  let K' : Subgroup (locU n w) := K.comap (locU n w).subtype
  have hfix : ∃ v : τ.V, v ≠ 0 ∧ ∀ k ∈ K', τ.ρ k v = v := by
    by_contra hn
    have key := GlobalTheory.InertHeckeEigen.mem_of_mem_iSup ρ τ.ρ hirr
      (fun i : Representation.IntertwiningMap τ.ρ ρ => i.toLinearMap) hfi (K' : Set (locU n w)) ⊥
      (fun i v hv => by
        have hv' : v = 0 := by
          by_contra h
          exact hn ⟨v, h, hv⟩
        rw [hv', map_zero]
        exact Submodule.zero_mem _)
      (fun z hz _ _ => by rw [(Submodule.mem_bot ℂ).1 hz, map_zero]) ⟨φ, hφ⟩
      (fun k hk => Subtype.ext (hφK k.1 hk)) (by rw [htop]; exact Submodule.mem_top)
    exact hφ0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1 key))
  obtain ⟨v, hvW, hv0, hv⟩ := UpperTheory.V.Af.GlobalFixedVectors.sub_fixed τ.ρ hirr ρ
    (by
      rw [eq_top_iff, ← htop]
      exact iSup_le fun i => le_iSup_of_le ⟨i.toLinearMap, hfi i⟩ le_rfl)
    (W.comap π.subtype) (fun g v hv => hW g.1 g.2 v.1 hv)
    (fun e => hW0 ((Submodule.eq_bot_iff W).2 fun x hx => by
      have h : (⟨x, hWπ hx⟩ : π) ∈ W.comap π.subtype := hx
      rw [e] at h
      exact congrArg Subtype.val ((Submodule.mem_bot ℂ).1 h))) K' hfix
  exact ⟨v.1, hvW, fun e => hv0 (Subtype.ext e), fun k hk => congrArg Subtype.val (hv ⟨k, hK hk⟩ hk)⟩
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU

theorem UpperTheory.unitary_adelic_t2_locallyCompact_secondCountable :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), T2Space (UA E n) ∧ LocallyCompactSpace (UA E n) ∧ SecondCountableTopology (UA E n) ∧ DiscreteTopology (ratU E n) := by
  intro E _ _ _ n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.discreteTopology_latticeGL (E := E) (a := n)
  refine ⟨inferInstance, (GlobalTheory.DefU.LocAdm.isClosed_UA (E := E) (n := n)).isClosedEmbedding_subtypeVal.locallyCompactSpace,
    (Topology.IsEmbedding.subtypeVal (p := fun g : GA E n => g ∈ UA E n)).secondCountableTopology, ?_⟩
  have hm : ∀ x : ratU E n, ((x : UA E n) : GA E n) ∈ latticeGL E n := fun x => by
    obtain ⟨δ, hδ⟩ := x.2
    have h := GlobalTheory.CuspRep.CuspidalL2GL.ratGL_mem_latticeGL (E := E) δ
    rw [hδ] at h
    exact h
  let f : ratU E n → latticeGL E n := fun x => ⟨_, hm x⟩
  have hf : Continuous f := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hi : Function.Injective f := fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : latticeGL E n => (z : GA E n)) h))
  exact DiscreteTopology.of_continuous_injective hf hi
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.BasicNotions
open scoped TensorProduct

theorem UpperTheory.finiteAdelicUnitary_mem_nhds_one_of_trivial_at_places :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (T : Set (HeightOneSpectrum (𝓞 E))), T.Finite → ∀ U ∈ nhds (1 : finU (E := E) (n := n)), ∃ S : Finset (HeightOneSpectrum (𝓞 E)), ∀ k : finU (E := E) (n := n), (∀ u ∉ T, cLoc u (k : UA E n) ∈ GlobalTheory.LFun.KGL u (n := n)) → (∀ u ∈ S, cLoc u (k : UA E n) = 1) → k ∈ U := by
  classical
  intro E _ _ _ n T hT U hU
  have hι : Topology.IsInducing (fun x : finU (E := E) (n := n) => ((x : UA E n) : GA E n)) :=
    Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  rw [hι.nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  have hV' : finGL E n ⁻¹' V ∈ nhds (1 : GL (Fin n) (Af E)) :=
    GlobalTheory.DefU.LocAdm.continuous_finGL.continuousAt.preimage_mem_nhds (by rw [map_one]; exact hV)
  obtain ⟨S, hS⟩ := UpperTheory.V.Af.GlobalFixedVectors.exists_KAway_subset (M := 1) hV'
  refine ⟨S ∪ hT.toFinset, fun k hk hk1 => hVU ?_⟩
  have hall : ∀ u, cLoc u (k : UA E n) ∈ GlobalTheory.LFun.KGL u (n := n) := fun u => by
    by_cases hu : u ∈ T
    · rw [hk1 u (Finset.mem_union_right _ (hT.mem_toFinset.2 hu))]; exact one_mem _
    · exact hk u hu
  have ent : ∀ (x : UA E n), (∀ u, cLoc u x ∈ GlobalTheory.LFun.KGL u (n := n)) → ∀ a b,
      Matrix.GeneralLinearGroup.map (pFin E) (x : GA E n) a b ∈ UpperTheory.V.Af.Ohat E := fun x hx a b =>
    UpperTheory.V.Af.GlobalFixedVectors.mem_Ohat.2 fun u => by
      obtain ⟨Q, hQ⟩ := hx u
      have e : (cLoc u x).val a b ∈ u.adicCompletionIntegers E := by
        rw [← hQ]; exact (Q.val a b).2
      exact e
  have h1 := ent _ hall
  have hmem : Matrix.GeneralLinearGroup.map (pFin E) ((k : UA E n) : GA E n) ∈
      UpperTheory.V.Af.GlobalFixedVectors.KAway n 1 S := by
    refine UpperTheory.V.Af.GlobalFixedVectors.mem_KAway.2 ⟨UpperTheory.V.Af.mem_KLev.2 ⟨h1, fun a b => ?_, fun a b => ?_⟩, fun w hw => ?_⟩
    · rw [← map_inv]
      exact ent (k : UA E n)⁻¹ (fun u => by rw [map_inv]; exact inv_mem (hall u)) a b
    · refine ⟨_, sub_mem (h1 a b) ?_, by rw [Nat.cast_one, one_mul]⟩
      rw [Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · exact hk1 w (Finset.mem_union_left _ hw)
  have hk2 : Matrix.GeneralLinearGroup.map (pInf E) ((k : UA E n) : GA E n) = 1 := k.2
  have e : finGL E n (Matrix.GeneralLinearGroup.map (pFin E) ((k : UA E n) : GA E n)) = ((k : UA E n) : GA E n) :=
    ga_ext (by rw [pInf_finGL, hk2]) (by rw [pFin_finGL])
  have := hS hmem
  rwa [Set.mem_preimage, e] at this
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.Pst.DpstMap GlobalTheory.GalOfCusp

private theorem norm_le_one {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [NormedField K]
    (ψ : Γ →* Kˣ) (hψ : Continuous fun s => (ψ s : K)) (s : Γ) : ‖(ψ s : K)‖ ≤ 1 := by
  obtain ⟨C, hC⟩ := (isCompact_range hψ.norm).bddAbove
  by_contra hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (not_le.1 hlt)
  have := hC ⟨s ^ n, rfl⟩
  simp only [map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
  exact absurd hn (not_lt.2 this)

private theorem norm_eq_one {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [NormedField K]
    (ψ : Γ →* Kˣ) (hψ : Continuous fun s => (ψ s : K)) (s : Γ) : ‖(ψ s : K)‖ = 1 := by
  refine le_antisymm (norm_le_one ψ hψ s) ?_
  have h := norm_le_one ψ hψ s⁻¹
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h
  exact (inv_le_one₀ (norm_pos_iff.2 (ψ s).ne_zero)).1 h

theorem UpperTheory.continuous_character_compact_unit_values :
    UpperTheory.V.Af.Wd.CharEnd := by
  intro F Ω _ _ _ _ _ l hl ι w A h hw ψ a hψ hσ
  haveI : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  have hq1 : 1 < normV w := GlobalTheory.WeilDeligne.one_lt_normV w
  have hpow := normV_eq_pow (l := l) hw
  have hf : resDeg l w ≠ 0 := by
    intro h0
    rw [hpow, h0, pow_zero] at hq1
    exact lt_irrefl _ hq1
  have hl1 : ‖(l : Qbar l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have hlt : ‖((normV w : ℕ) : Qbar l)‖ < 1 := by
    rw [hpow, Nat.cast_pow, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hl1 hf
  have hpos : 0 < ‖((normV w : ℕ) : Qbar l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 (by omega))
  have ha : a = 0 := by
    have h1 := hσ (frob h)
    rw [deg_frob, mul_one, ← map_natCast ι, ← map_zpow₀] at h1
    have h2 := norm_eq_one ψ hψ (Subgroup.inclusion (Weil_le_Dec h) (frob h))
    rw [ι.injective h1, norm_zpow] at h2
    exact (zpow_eq_one_iff_right₀ hpos.le hlt.ne).1 h2
  refine ⟨ha, ?_⟩
  have hd := UpperTheory.weil_group_dense_in_galois_group F Ω w A h
  have he : (fun s => (ψ s : Qbar l)) = fun _ => 1 := by
    refine hd.equalizer hψ continuous_const (funext fun σ => ?_)
    have h1 := hσ σ
    rw [ha, zero_mul, zpow_zero, ← map_one ι] at h1
    exact ι.injective h1
  ext s
  simpa using congrFun he s
end

section

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2
open scoped Matrix Pointwise

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]

private theorem ex_lift (k₀ : IntermediateField ℚ Ω) {g : G ℚ Ω} (hg : g ∈ k₀.fixingSubgroup) :
    ∃ h : G k₀ Ω, resQ k₀ h = g :=
  ⟨{ g.toRingEquiv with commutes' := fun x => hg x }, rfl⟩

private theorem res_mem (F : IntermediateField ℚ Ω) (g : G F Ω) : resQ F g ∈ F.fixingSubgroup :=
  fun x => g.commutes x

private theorem val_comap (A : ValuationSubring Ω) (t : G ℚ Ω) (y : Ω) :
    (A.comap (t : Ω →+* Ω)).valuation y < 1 ↔ A.valuation (t y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, map_eq_zero_iff _ t.injective]
  rfl

private theorem dec_conj {A : ValuationSubring Ω} (t : G ℚ Ω) {s : G ℚ Ω} (hs : s ∈ Dec (F := ℚ) A) :
    t⁻¹ * s * t ∈ Dec (F := ℚ) (A.comap (t : Ω →+* Ω)) := by
  rw [← Subgroup.inv_mem_iff, mem_Dec]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
  show t (t⁻¹ (s (t x))) ∈ A ↔ t x ∈ A
  rw [mul_inv_apply, apply_mem_iff_of_mem_Dec hs]

private theorem ine_conj {A : ValuationSubring Ω} (t : G ℚ Ω) {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) A) :
    t⁻¹ * s * t ∈ Ine (F := ℚ) (A.comap (t : Ω →+* Ω)) := by
  refine ⟨dec_conj t hs.1, fun x hx => ?_⟩
  rw [val_comap, map_sub]
  show A.valuation (t (t⁻¹ (s (t x))) - t x) < 1
  rw [mul_inv_apply]
  refine hs.2 _ ?_
  rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
  exact hx

private theorem norm_of_cong {a b : (Qbar l)ˣ} (h : Cong a b) (hb : ‖(b : Qbar l)‖ = 1) : ‖(a : Qbar l)‖ = 1 := by
  have h' : ‖(a : Qbar l) - b‖ < ‖(b : Qbar l)‖ := hb ▸ h
  have e := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h'.ne
  rw [sub_add_cancel, max_eq_right h'.le] at e
  rw [e, hb]

private theorem pull (k₀ : IntermediateField ℚ Ω) [NumberField k₀] {S : Type} (r : G k₀ Ω →* GL (Fin 2) (Qbar l))
    {m : Fin 2 → ℤ} {ψ : Fin 2 → G k₀ Ω →* (Qbar l)ˣ} {B : ValuationSubring Ω} (hO : OrdAt r m ψ B) (h : S → G k₀ Ω)
    (hD : ∀ s, resQ k₀ (h s) ∈ Dec (F := ℚ) B) :
    ∃ κ : Fin 2 → S → (Qbar l)ˣ, S2.Flag (fun s => r (h s)) κ ∧
      (∀ i s, resQ k₀ (h s) ∈ Ine (F := ℚ) B → κ i s = cycBar ℚ Ω l (resQ k₀ (h s)) ^ m i) ∧ ∀ i s, Cong (κ i s) (ψ i (h s)) := by
  obtain ⟨κ, ⟨g, hg⟩, h2, h3⟩ := hO
  refine ⟨fun i s => κ i ⟨h s, hD s⟩, ⟨g, fun s => ⟨(hg ⟨h s, hD s⟩).1 1 0 (by decide), (hg ⟨h s, hD s⟩).2⟩⟩,
    fun i s hs => h2 i ⟨h s, hD s⟩ ⟨hD s, hs.2⟩, fun i s => h3 i ⟨h s, hD s⟩⟩

end

theorem UpperTheory.induced_flag_condition :
    UpperTheory.V.Sd.S2.IndFlag := by
  intro Ω _ _ _ l _ c D T k₀ _ _ φ ι k t r α β R δ H
  refine ⟨![(k : ℤ) + t, k, 0, -(t : ℤ)], ?_, fun A hA => ?_⟩
  · have := H.dat.hk
    have := H.dat.ht
    intro i
    fin_cases i <;> simp <;> omega
  have hA' : (A.comap (resQ T.F T.g0 : Ω →+* Ω)).valuation (l : Ω) < 1 := by
    rw [val_comap, map_natCast]
    exact hA
  have hD : ∀ s : Dec (F := T.F) A, resQ T.F s ∈ Dec (F := ℚ) A := fun s => s.2
  choose h hh using fun s : Dec (F := T.F) A => ex_lift k₀ (H.hyp.spl A hA (hD s))
  choose h' hh' using fun s : Dec (F := T.F) A => ex_lift k₀ (H.hyp.spl _ hA' (dec_conj (resQ T.F T.g0) (hD s)))
  have hcomm : ∀ (χ : G ℚ Ω →* (Qbar l)ˣ) s, χ (resQ k₀ (h' s)) = χ (resQ T.F s) := fun χ s => by
    rw [hh', map_mul, map_mul, map_inv, inv_mul_cancel_comm]
  have hne : ∃ s : Dec (F := T.F) A, ¬ Cong (up D.ξ (resQ T.F s)) 1 := by
    obtain ⟨g, hg, hg4⟩ := H.hyp.two.bigL A hA
    refine ⟨⟨g, hg⟩, fun hc => hg4 ?_⟩
    have := (H.chars.al g 1).2 (by rwa [pow_one])
    rw [pow_one] at this
    rw [this, one_pow]
  have hR : ∀ s, Rib (r (h s)) (up D.ξ (resQ T.F s)) := fun s => by
    have := H.rib (h s) (hh s ▸ res_mem T.F s)
    rwa [hh] at this
  have hR' : ∀ s, Rib (r (h' s)) (up D.ξ (resQ T.F s)) := fun s => by
    have := H.rib (h' s) (by
      rw [hh', ← map_inv, ← map_mul, ← map_mul]
      exact res_mem T.F _)
    rwa [hcomm] at this
  have hmix : ∀ s : Dec (F := T.F) A, (R (resQ T.F s) : M4 (Qbar l)) = mix (β / α) (r (h s)) (r (h' s)) := fun s => by
    rw [← hh s]
    exact H.mix.on _ _ (by rw [hh, hh'])
  have hγ : ‖((β / α : (Qbar l)ˣ) : Qbar l)‖ = 1 := by
    rw [Units.val_div_eq_div_val, norm_div, norm_of_cong H.α_cong (H.chars.unit _ _),
      norm_of_cong H.β_cong (H.chars.unit _ _), div_one]
  have hI : ∀ s : Dec (F := T.F) A, (s : G T.F Ω) ∈ Ine (F := T.F) A → resQ T.F s ∈ Ine (F := ℚ) A :=
    fun s hs => ⟨hD s, hs.2⟩
  have hdet : ∀ {M : GL (Fin 2) (Qbar l)} {a b : (Qbar l)ˣ}, Matrix.GeneralLinearGroup.det M = a * b →
      (M : Matrix (Fin 2) (Fin 2) (Qbar l)).det = a * b := fun e => congrArg Units.val e
  rcases H.dat.above A _ hA _ H.chars.out (fun y => (Iff.rfl : _ ↔ y ∈ A.comap (resQ T.F T.g0 : Ω →+* Ω))) with ⟨o, o'⟩ | ⟨o, o'⟩
  all_goals
    obtain ⟨κ, f, i1, c1⟩ := pull k₀ r o h fun s => hh s ▸ hD s
    obtain ⟨κ', f', i2, c2⟩ := pull k₀ r o' h' fun s => hh' s ▸ dec_conj _ (hD s)
    obtain ⟨d1, u1, w1⟩ := UpperTheory.mix_stable_line_local l _ _ _ κ hne hR f
    obtain ⟨d2, u2, w2⟩ := UpperTheory.mix_stable_line_local l _ _ _ κ' hne hR' f'
    have j1 := fun i s hs => i1 i s (hh s ▸ hI s hs)
    have j2 := fun i s hs => i2 i s (hh' s ▸ ine_conj _ (hI s hs))
    simp only [hh, hcomm] at j1 j2
    have c10 := c1 0
    have c11 := c1 1
    have c20 := c2 0
    have c21 := c2 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, MonoidHom.comp_apply, MonoidHom.one_apply, hh, hcomm] at c10 c11 c20 c21
  · obtain ⟨u, hu, eu⟩ := u1 c10
    obtain ⟨w, hw, ew⟩ := w2 c20
    obtain ⟨n, hn, hf⟩ := (UpperTheory.mix_flag_exists l H.hyp.good.l_odd _ u w hγ hu hw).1
    refine ⟨n, hn, fun s hs => ?_⟩
    obtain ⟨g1, g2⟩ := hf _ _ _ _ _ _ (Units.ne_zero _) (Units.ne_zero _) (eu ⟨s, hs⟩) (ew ⟨s, hs⟩) (hdet (d1 _)) (hdet (d2 _))
    rw [← hmix] at g1 g2
    refine ⟨g1, fun i => ?_⟩
    rw [g2]
    fin_cases i
    · exact ⟨c10 _, fun hs' => congrArg Units.val (j1 0 _ hs')⟩
    · exact ⟨c20 _, fun hs' => congrArg Units.val (j2 0 _ hs')⟩
    · exact ⟨c21 _, fun hs' => congrArg Units.val (j2 1 _ hs')⟩
    · exact ⟨c11 _, fun hs' => congrArg Units.val (j1 1 _ hs')⟩
  · obtain ⟨u, hu, eu⟩ := u2 c20
    obtain ⟨w, hw, ew⟩ := w1 c10
    obtain ⟨n, hn, hf⟩ := (UpperTheory.mix_flag_exists l H.hyp.good.l_odd _ u w hγ hu hw).2
    refine ⟨n, hn, fun s hs => ?_⟩
    obtain ⟨g1, g2⟩ := hf _ _ _ _ _ _ (Units.ne_zero _) (Units.ne_zero _) (ew ⟨s, hs⟩) (eu ⟨s, hs⟩) (hdet (d1 _)) (hdet (d2 _))
    rw [← hmix] at g1 g2
    refine ⟨g1, fun i => ?_⟩
    rw [g2]
    fin_cases i
    · exact ⟨c20 _, fun hs' => congrArg Units.val (j2 0 _ hs')⟩
    · exact ⟨c10 _, fun hs' => congrArg Units.val (j1 0 _ hs')⟩
    · exact ⟨c11 _, fun hs' => congrArg Units.val (j1 1 _ hs')⟩
    · exact ⟨c21 _, fun hs' => congrArg Units.val (j2 1 _ hs')⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem cont_resQ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [NumberField F] :
    Continuous (resQ F) := by
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  exact (galEmbTop ℚ F Ω).1.continuous

theorem UpperTheory.exists_residualRep_restriction_of_latticeShape :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ T : Tower D, T.Fit → ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → (T.fr ∅).Ok a → ∀ s : PD Unit (G ℚ Ω) k, LatShape D T.pr (resQ T.F T.g0) a s →
          ∃ s' : PD T.ι (G T.F Ω) k, (T.fr ∅).IsRes a s' ∧ T.OverQ s s' := by
  intro Ω _ _ _ l hl c D hD T hF k _ a _ _ P hS
  have hOk : T.Ok := hF.1
  have hP := hS.res.pair
  choose g hg hgD hgI using fun v : T.ι => Rq.placeMove T.F l hl.out (T.pl v) (D.pl l) (T.ovl v) (hD.pl_over l hl.out)
  have hν : ∀ x, IsUnit (a (D.th x)) := fun x => (D.th x).isUnit.map _
  have hd : ∀ x i, IsUnit (P.r x i i) := fun x i => by
    rw [hS.res.res.diag]
    exact (Units.isUnit _).map _
  have sh := fun v : T.ι => Rq.shapeQ _ _ _ (hS.supp (g v)) (hd (g v)) (hP.low ()) hS.flag
  choose n hn hb using fun v : T.ι => Rq.luG k _ (P.r (g v)) (P.n ()) (hν (g v)) (hP.mult (g v)) (hP.low ())
    (sh v).1.1 (sh v).1.2
  let Q : PD T.ι (G T.F Ω) k := ⟨P.r.comp (resQ T.F), n⟩
  have key : ∀ v, ∀ s ∈ Dec (F := T.F) (T.pl v), IsUp (adj (Q.n v) * Q.r s * Q.n v) ∧
      ∀ i, Q.ψ v i s = P.ψ () i ((g v)⁻¹ * resQ T.F s * g v) := fun v s hs =>
    Rq.conjFlag _ _ (P.r (g v)) (P.r ((g v)⁻¹ * resQ T.F s * g v)) (P.r (resQ T.F s)) _ _
      (hν (g v)) (hP.mult (g v)) (hP.low ()) (hn v) (hb v)
      (by rw [← map_mul, ← map_mul, mul_assoc, mul_inv_cancel_left]) (hP.flag () _ (hgD v s hs))
  have hconj : ∀ (χ : G ℚ Ω →* c.Oˣ) (x y : G ℚ Ω), χ (x⁻¹ * y * x) = χ y := fun χ x y => by
    rw [map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
  have hch : ∀ v, ∀ s ∈ Dec (F := T.F) (T.pl v), ∀ i, Q.ψ v i s = a (chi D T.pr i (resQ T.F s)) := fun v s hs i => by
    rw [(key v s hs).2, ← hconj (chi D T.pr i) (g v)]
    exact hS.res.res.char () _ (hgD v s hs) i
  refine ⟨Q, ⟨⟨fun x => hP.mult (resQ T.F x), Rq.killQ D hD T hOk _ _ _ P.r hP.kill, hP.nrm, hn,
    fun v s hs => (key v s hs).1, fun v s hs i => ?_⟩,
    ⟨fun x i => hS.res.res.diag (resQ T.F x) i, hch, Or.inl ⟨fun x => hS.supp _, fun v => (sh v).2 _ (hn v) (hb v)⟩⟩,
    fun i j N => (hS.res.cont i j N).comp_continuous (cont_resQ T.F)⟩, rfl, fun v => ⟨(), g v, hg v, hb v⟩⟩
  refine (hch v s hs.1 i).trans ?_
  rw [chi, Rq.muPs D hD T hOk _ s hs, Units.val_one, map_one]
end
