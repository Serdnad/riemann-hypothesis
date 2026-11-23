module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle003
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle003
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
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

private def rootEnt (a b i j : Fin 4) : ℤ :=
  if i = a ∧ j = b then 1 else if j.rev = a ∧ i.rev = b then -(sgn i * sgn j) else 0

private theorem rootEnt_adj : ∀ a b i j : Fin 4, a ≠ b →
    (sgn i * sgn j) * rootEnt a b j.rev i.rev = -rootEnt a b i j := by decide

private theorem rootEnt_zero : ∀ a b i j : Fin 4, wt i j ≠ wt a b → rootEnt a b i j = 0 := by decide

private theorem rootEnt_cases : ∀ a b i j : Fin 4, a ≠ b → wt i j = wt a b →
    (i = a ∧ j = b) ∨ (j.rev = a ∧ i.rev = b ∧ rootEnt a b i j = -(sgn i * sgn j)) := by decide

theorem UpperTheory.exists_sp4_root_vector_unique_on_weight :
    ∀ (E : Type) [Field E] [CharZero E] (a b : Fin 4), a ≠ b → ∃ X ∈ sp4 E, X a b = 1 ∧ (∀ i j, wt i j ≠ wt a b → X i j = 0) ∧ ∀ Y ∈ sp4 E, ∀ i j, wt i j = wt a b → Y i j = Y a b * X i j := by
  intro E _ _ a b hab
  refine ⟨Matrix.of fun i j => ((rootEnt a b i j : ℤ) : E), ?_, ?_, ?_, ?_⟩
  · show UpperTheory.V.GradeZeroInterpolatingElement.adj _ = -_
    ext i j
    rw [adj_apply, Matrix.neg_apply, Matrix.of_apply, Matrix.of_apply, zsmul_eq_mul, ← Int.cast_mul,
      rootEnt_adj a b i j hab, Int.cast_neg]
  · simp [rootEnt]
  · intro i j h
    simp [rootEnt_zero a b i j h]
  · intro Y hY i j h
    rcases rootEnt_cases a b i j hab h with ⟨rfl, rfl⟩ | ⟨h1, h2, h3⟩
    · simp [rootEnt]
    · have hY' : UpperTheory.V.GradeZeroInterpolatingElement.adj Y = -Y := hY
      have h4 := congrFun (congrFun hY' i) j
      rw [adj_apply, Matrix.neg_apply, h1, h2, zsmul_eq_mul] at h4
      rw [Matrix.of_apply, h3, Int.cast_neg]
      linear_combination h4
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial

private theorem ptFin_int {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

private theorem ptFin_pow {O S : Type} [CommRing O] [CommRing S] [Algebra O S] [IsNoetherianRing S] (m : Ideal S)
    (hres : ∀ x : S, ∃ a : O, x - algebraMap O S a ∈ m) (n : ℕ) :
    ∃ N : Submodule O S, N.FG ∧ ∀ x : S, ∃ y ∈ N, x - y ∈ m ^ n :=
  _root_.UpperTheory.Reformulated.B.PointFinitePower.ptFin_pow m hres n

private theorem ptFin_finite {O S : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
    [CommRing S] [Algebra O S] [IsLocalRing S] [IsNoetherianRing S] [Algebra.IsIntegral O S]
    (hloc : ∀ a ∈ maximalIdeal O, algebraMap O S a ∈ maximalIdeal S)
    (hres : ∀ x : S, ∃ a : O, x - algebraMap O S a ∈ maximalIdeal S) : Module.Finite O S := by
  set J : Ideal S := (maximalIdeal O).map (algebraMap O S) with hJ
  have hJle : J ≤ maximalIdeal S := Ideal.map_le_iff_le_comap.2 hloc
  have hJne : J ≠ ⊤ := fun h => (maximalIdeal.isMaximal S).ne_top (top_le_iff.1 (h ▸ hJle))
  haveI : IsHausdorff (maximalIdeal O) S :=
    IsHausdorff.map_algebraMap_iff.1 (IsHausdorff.of_isLocalRing J S hJne)
  have hrad : maximalIdeal S ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro P ⟨hJP, hP⟩
    have h1 : maximalIdeal O ≤ P.comap (algebraMap O S) := Ideal.map_le_iff_le_comap.1 hJP
    have h2 : P.comap (algebraMap O S) = maximalIdeal O :=
      ((maximalIdeal.isMaximal O).eq_of_le (Ideal.comap_ne_top _ hP.ne_top) h1).symm
    have h3 : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) P
      (by change (P.comap (algebraMap O S)).IsMaximal; rw [h2]; infer_instance)
    exact (eq_maximalIdeal h3).ge
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  obtain ⟨N, hN, h⟩ := ptFin_pow (maximalIdeal S) hres n
  refine (UpperTheory.V.abelian₂.nakayama O (maximalIdeal O) S).2 ⟨?_⟩
  have : (⊤ : Submodule O (S ⧸ (maximalIdeal O) • (⊤ : Submodule O S))) = N.map (Submodule.mkQ _) := by
    symm
    rw [Submodule.map_mkQ_eq_top, eq_top_iff]
    intro x _
    obtain ⟨y, hy, h1⟩ := h x
    have h2 : x - y ∈ (maximalIdeal O) • (⊤ : Submodule O S) := by
      rw [Ideal.smul_top_eq_map]
      exact hn h1
    simpa using Submodule.add_mem_sup h2 hy
  rw [this]
  exact hN.map _

theorem UpperTheory.V.Loc.ptFin :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (F : R →ₐ[O] DualNumber (PadicAlgCl l)), IsLocPt (dualFst F) → ∃ E' : FinExt l, ∀ a, (F a).fst ∈ E'.1 ∧ (F a).snd ∈ E'.1 := by
  intro l _ O _ _ _ _ _ _ _ _ _ R _ _ _ F hF
  classical
  set f := dualFst F with hf
  have hfa : ∀ a, (F a).fst = f a := fun a => rfl
  have hO : ∀ a : O, IsIntegral ℤ_[l] (algebraMap O (PadicAlgCl l) a) := fun a =>
    (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a).map (IsScalarTower.toAlgHom ℤ_[l] O (PadicAlgCl l))
  have hint : ∀ a : R, IsIntegral O (f a) := by
    intro a
    obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) a
    have h1 : IsIntegral O (f (a - algebraMap O R c)) := ((ptFin_int _).2 (hF _ hc).le).tower_top
    have h2 : f a = f (a - algebraMap O R c) + algebraMap O _ c := by simp
    rw [h2]
    exact h1.add isIntegral_algebraMap
  let g : R →ₐ[O] f.range := f.rangeRestrict
  have hg : Function.Surjective g := f.rangeRestrict_surjective
  haveI : IsLocalRing f.range := IsLocalRing.of_surjective' (g : R →+* f.range) hg
  haveI : IsNoetherianRing f.range := isNoetherianRing_of_surjective R _ (g : R →+* f.range) hg
  haveI : IsLocalHom (g : R →+* f.range) := IsLocalHom.of_surjective _ hg
  have hm : ∀ a ∈ maximalIdeal R, g a ∈ maximalIdeal f.range := fun a ha =>
    map_nonunit (g : R →+* f.range) a ha
  haveI : Algebra.IsIntegral O f.range := ⟨fun x => by
    obtain ⟨a, rfl⟩ := hg x
    exact (isIntegral_algHom_iff f.range.val Subtype.val_injective).1 (hint a)⟩
  haveI : Module.Finite O f.range := ptFin_finite
    (fun a ha => by
      rw [← g.commutes]
      exact hm _ (map_nonunit (algebraMap O R) a ha))
    (fun x => by
      obtain ⟨a, rfl⟩ := hg x
      obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) a
      exact ⟨c, by simpa using hm _ hc⟩)
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := O) (M := f.range)
  choose b hb using fun i => hg (s i)
  obtain ⟨r', o, ho⟩ := Module.Finite.exists_fin (R := ℤ_[l]) (M := O)
  obtain ⟨P, hP⟩ : (RingHom.ker f).FG := IsNoetherian.noetherian _
  let T : Set (PadicAlgCl l) := Set.range (fun i => algebraMap O (PadicAlgCl l) (o i)) ∪ Set.range (fun i => f (b i)) ∪
    Set.range (fun i => (F (b i)).snd) ∪ (fun p => (F p).snd) '' (P : Set R)
  have hT : T.Finite :=
    (((Set.finite_range _).union (Set.finite_range _)).union (Set.finite_range _)).union (P.finite_toSet.image _)
  haveI : Finite T := hT
  let E : IntermediateField ℚ_[l] (PadicAlgCl l) := IntermediateField.adjoin ℚ_[l] T
  have hE : FiniteDimensional ℚ_[l] E :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hTE : T ⊆ E := IntermediateField.subset_adjoin _ _
  have hOE : ∀ c : O, algebraMap O (PadicAlgCl l) c ∈ E := by
    intro c
    have hc : c ∈ Submodule.span ℤ_[l] (Set.range o) := ho ▸ Submodule.mem_top
    obtain ⟨u, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hc

    rw [map_sum]
    refine sum_mem fun i _ => ?_
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
    exact mul_mem (E.algebraMap_mem _) (hTE (Or.inl (Or.inl (Or.inl ⟨i, rfl⟩))))
  have hdec : ∀ a : R, ∃ u : Fin r → O, a - ∑ i, u i • b i ∈ RingHom.ker f := by
    intro a
    have hc : g a ∈ Submodule.span O (Set.range s) := hs ▸ Submodule.mem_top
    obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hc
    refine ⟨u, ?_⟩
    have h1 : g (a - ∑ i, u i • b i) = 0 := by simp [hb, hu]
    exact congrArg Subtype.val h1
  have h1 : ∀ a, f a ∈ E := by
    intro a
    obtain ⟨u, hu⟩ := hdec a
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hu

    rw [hu, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_smul, Algebra.smul_def]
    exact mul_mem (hOE _) (hTE (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩))))
  have h2 : ∀ a ∈ Ideal.span (P : Set R), (F a).snd ∈ E := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem z hz => exact hTE (Or.inr ⟨z, hz, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), TrivSqZeroExt.snd_add]; exact add_mem hx hy
    | smul c x hx0 hx =>
      have h0 : (F x).fst = 0 := by
        have : x ∈ RingHom.ker f := hP ▸ hx0
        exact this
      rw [smul_eq_mul, map_mul, DualNumber.snd_mul, h0, mul_zero, add_zero]
      exact mul_mem (h1 c) hx
  refine ⟨⟨E, hE⟩, fun a => ⟨h1 a, ?_⟩⟩
  obtain ⟨u, hu⟩ := hdec a
  have h3 := h2 _ (hP ▸ hu)
  have h4 : (F (∑ i, u i • b i)).snd ∈ E := by

    rw [map_sum, TrivSqZeroExt.snd_sum]
    refine sum_mem fun i _ => ?_
    rw [map_smul, TrivSqZeroExt.snd_smul, Algebra.smul_def]
    exact mul_mem (hOE _) (hTE (Or.inl (Or.inr ⟨i, rfl⟩)))
  have h5 := add_mem h3 h4
  rwa [← TrivSqZeroExt.snd_add, ← map_add, sub_add_cancel] at h5
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

private theorem exists_monic_integral_unit_root {l : ℕ} [Fact l.Prime] (a : Om l) (ha : ‖a‖ = 1) :
    ∃ Q : ℤ_[l][X], Q.Monic ∧ IsUnit (Q.coeff 0) ∧
      (X - C a) ∣ Q.map ((algebraMap ℚ_[l] (Om l)).comp (algebraMap ℤ_[l] ℚ_[l])) := by
  have hint : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  have hm : (minpoly ℚ_[l] a).Monic := minpoly.monic hint
  have hs : spectralNorm ℚ_[l] (Om l) a = 1 := ha
  have hc : ∀ n, ‖(minpoly ℚ_[l] a).coeff n‖ ≤ 1 :=
    (spectralValue_le_one_iff hm).1 (le_of_eq hs)
  have h0 : ‖(minpoly ℚ_[l] a).coeff 0‖ = 1 := by
    have h := spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[l] (Om l) a
    rw [hs] at h
    have hpos : (0 : ℝ) < (minpoly ℚ_[l] a).natDegree := by
      exact_mod_cast minpoly.natDegree_pos hint
    have h2 := congrArg (fun t : ℝ => t ^ (((minpoly ℚ_[l] a).natDegree : ℕ) : ℝ)) h
    simp only [Real.one_rpow] at h2
    rw [← Real.rpow_mul (norm_nonneg _), one_div, inv_mul_cancel₀ hpos.ne', Real.rpow_one] at h2
    exact h2.symm
  have hl : minpoly ℚ_[l] a ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hc n⟩, rfl⟩
  obtain ⟨Q, hQ, -, hQm⟩ := lifts_and_natDegree_eq_and_monic hl hm
  refine ⟨Q, hQm, ?_, ?_⟩
  · rw [PadicInt.isUnit_iff]
    rw [← hQ, coeff_map] at h0
    exact h0
  · rw [← Polynomial.map_map, hQ, dvd_iff_isRoot, IsRoot.def, eval_map_algebraMap]
    exact minpoly.aeval _ _

private theorem aux_mul {l : ℕ} [Fact l.Prime] (s : Multiset (Om l)) (hs : ∀ a ∈ s, ‖a‖ = 1) :
    ∃ Q : ℤ_[l][X], Q.Monic ∧ IsUnit (Q.coeff 0) ∧
      (s.map (fun a => X - C a)).prod ∣
        Q.map ((algebraMap ℚ_[l] (Om l)).comp (algebraMap ℤ_[l] ℚ_[l])) := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨1, monic_one, by simp, by simp⟩
  | cons a s ih =>
    obtain ⟨Q, h1, h2, h3⟩ := ih (fun b hb => hs b (Multiset.mem_cons_of_mem hb))
    obtain ⟨R, g1, g2, g3⟩ := exists_monic_integral_unit_root a (hs a (Multiset.mem_cons_self a s))
    refine ⟨R * Q, g1.mul h1, ?_, ?_⟩
    · rw [mul_coeff_zero]; exact g2.mul h2
    · rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.map_mul]
      exact mul_dvd_mul g3 h3

theorem UpperTheory.exists_monic_unit_coeff_zero_annihilating_of_spectrum_norm_one :
    ∀ {l : ℕ} [Fact l.Prime] (L : IntermediateField ℚ_[l] (Om l)) {d : ℕ} (F : Matrix (Fin d) (Fin d) ↥L), (∀ a ∈ spectrum (Om l) (F.map (algebraMap ↥L (Om l))), ‖a‖ = 1) → ∃ P : ℤ_[l][X], P.Monic ∧ IsUnit (P.coeff 0) ∧ aeval F (P.map ((algebraMap ℚ_[l] ↥L).comp (algebraMap ℤ_[l] ℚ_[l]))) = 0 := by
  intro l _ L d F hF
  set χ := (F.map (algebraMap ↥L (Om l))).charpoly with hχ
  have hχm : χ.Monic := Matrix.charpoly_monic _
  obtain ⟨Q, h1, h2, h3⟩ := aux_mul χ.roots (fun a ha =>
    hF a (Matrix.mem_spectrum_iff_isRoot_charpoly.2 ((mem_roots hχm.ne_zero).1 ha)))
  refine ⟨Q, h1, h2, ?_⟩
  rw [← (IsAlgClosed.splits χ).eq_prod_roots_of_monic hχm, hχ, Matrix.charpoly_map,
    IsScalarTower.algebraMap_eq ℚ_[l] L (Om l), RingHom.comp_assoc, ← Polynomial.map_map,
    map_dvd_map'] at h3
  obtain ⟨R, hR⟩ := h3
  rw [hR, map_mul, Matrix.aeval_self_charpoly, zero_mul]
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

private theorem norm_eq_of_aeval_minpoly_eq_zero' {l : ℕ} [Fact l.Prime] (L : IntermediateField ℚ_[l] (Om l)) (a μ : Om l)
    (h : Polynomial.aeval μ (minpoly L a) = 0) : ‖μ‖ = ‖a‖ := by
  haveI : Algebra.IsAlgebraic L (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) L
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root (Algebra.IsAlgebraic.isAlgebraic a) h
  rw [← hσ]
  exact spectralNorm_eq_of_equiv (K := ℚ_[l]) (L := PadicAlgCl l) (σ.restrictScalars ℚ_[l]) μ

private theorem aeval_mul_eq_mul_aeval_of_semiconj {K : Type} [Field K] {d r : ℕ} (F : Matrix (Fin d) (Fin d) K)
    (Y : Matrix (Fin d) (Fin r) K) (F' : Matrix (Fin r) (Fin r) K) (h : F * Y = Y * F')
    (q : Polynomial K) : Polynomial.aeval F q * Y = Y * Polynomial.aeval F' q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _), Matrix.add_mul, Matrix.mul_add, hp, hq]
  | monomial n c =>
    have hpow : ∀ m : ℕ, F ^ m * Y = Y * F' ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, hpow]

private theorem norm_det_eq_pow_of_aeval_minpoly_eq_zero {l : ℕ} [Fact l.Prime] (L : IntermediateField ℚ_[l] (Om l)) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ↥L) (a : Om l) (hA : Polynomial.aeval A (minpoly L a) = 0) :
    ‖((A.det : ↥L) : Om l)‖ = ‖a‖ ^ r := by
  set M : Matrix (Fin r) (Fin r) (Om l) := A.map (algebraMap ↥L (Om l)) with hMdef
  have hdet : ((A.det : ↥L) : Om l) = M.det := by
    rw [hMdef]
    exact RingHom.map_det (algebraMap ↥L (Om l)) A
  have hMp : Polynomial.aeval M (minpoly L a) = 0 := by
    have e := Polynomial.aeval_algHom_apply ((Algebra.ofId ↥L (Om l)).mapMatrix (m := Fin r)) A (minpoly L a)
    rw [hA, map_zero] at e
    exact e
  have hroot : ∀ μ ∈ M.charpoly.roots, ‖μ‖ = ‖a‖ := by
    intro μ hμ
    have hr : Polynomial.IsRoot M.charpoly μ := (Polynomial.mem_roots M.charpoly_monic.ne_zero).mp hμ
    have hs : μ ∈ spectrum (Om l) M := Matrix.mem_spectrum_of_isRoot_charpoly hr
    have hs2 := spectrum.subset_polynomial_aeval M ((minpoly L a).map (algebraMap ↥L (Om l))) ⟨μ, hs, rfl⟩
    rw [Polynomial.aeval_map_algebraMap, hMp] at hs2
    have hz : Polynomial.eval μ ((minpoly L a).map (algebraMap ↥L (Om l))) = 0 := by
      by_contra hx
      rw [spectrum.mem_iff, sub_zero] at hs2
      exact hs2 ((Units.mk0 _ hx).isUnit.map (algebraMap (Om l) (Matrix (Fin r) (Fin r) (Om l))))
    rw [Polynomial.eval_map_algebraMap] at hz
    exact norm_eq_of_aeval_minpoly_eq_zero' L a μ hz
  rw [hdet, Matrix.det_eq_prod_roots_charpoly]
  have hn := map_multiset_prod (normHom : Om l →*₀ ℝ) M.charpoly.roots
  simp only [normHom_apply] at hn
  rw [hn, Multiset.map_congr rfl hroot, Multiset.map_const', Multiset.prod_replicate,
    IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

private theorem exists_invariant_subspace_in_ker_of_det_zero {K : Type} [Field K] {d : ℕ} (F P : Matrix (Fin d) (Fin d) K)
    (hP : P.det = 0) (hc : F * P = P * F) :
    ∃ (r : ℕ) (Y : Matrix (Fin d) (Fin r) K) (Z : Matrix (Fin r) (Fin d) K) (F' : Matrix (Fin r) (Fin r) K),
      0 < r ∧ Z * Y = 1 ∧ F * Y = Y * F' ∧ P * Y = 0 := by
  classical
  set W := LinearMap.ker (Matrix.toLin' P) with hWdef
  have hW : W ≠ ⊥ := by
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hP
    intro h
    have hvW : v ∈ W := by
      rw [hWdef, LinearMap.mem_ker, Matrix.toLin'_apply]
      exact hv
    rw [h, Submodule.mem_bot] at hvW
    exact hv0 hvW
  have hr : 0 < Module.finrank K W := Nat.pos_of_ne_zero (fun h => hW (Submodule.finrank_eq_zero.mp h))
  have hinv : ∀ w ∈ W, Matrix.toLin' F w ∈ W := by
    intro w hw
    rw [hWdef, LinearMap.mem_ker, Matrix.toLin'_apply] at hw ⊢
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← hc, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]
  set e := (Module.finBasis K W).equivFun
  set ι : (Fin (Module.finrank K W) → K) →ₗ[K] (Fin d → K) := W.subtype ∘ₗ e.symm.toLinearMap with hι
  have hιker : LinearMap.ker ι = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact Subtype.val_injective.comp e.symm.injective
  obtain ⟨g, hg⟩ := ι.exists_leftInverse_of_injective hιker
  set G := e.toLinearMap ∘ₗ (Matrix.toLin' F).restrict hinv ∘ₗ e.symm.toLinearMap with hG
  refine ⟨Module.finrank K W, LinearMap.toMatrix' ι, LinearMap.toMatrix' g, LinearMap.toMatrix' G, hr, ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  · have hcomp : ι ∘ₗ G = Matrix.toLin' F ∘ₗ ι := by
      apply LinearMap.ext
      intro x
      simp [hι, hG, LinearMap.restrict_apply]
    calc F * LinearMap.toMatrix' ι = LinearMap.toMatrix' (Matrix.toLin' F) * LinearMap.toMatrix' ι := by
          rw [LinearMap.toMatrix'_toLin']
      _ = LinearMap.toMatrix' (Matrix.toLin' F ∘ₗ ι) := (LinearMap.toMatrix'_comp _ _).symm
      _ = LinearMap.toMatrix' (ι ∘ₗ G) := by rw [hcomp]
      _ = _ := LinearMap.toMatrix'_comp _ _
  · have hzero : Matrix.toLin' P ∘ₗ ι = 0 := by
      apply LinearMap.ext
      intro x
      rw [LinearMap.comp_apply, LinearMap.zero_apply]
      exact (e.symm x).2
    calc P * LinearMap.toMatrix' ι = LinearMap.toMatrix' (Matrix.toLin' P) * LinearMap.toMatrix' ι := by
          rw [LinearMap.toMatrix'_toLin']
      _ = LinearMap.toMatrix' (Matrix.toLin' P ∘ₗ ι) := (LinearMap.toMatrix'_comp _ _).symm
      _ = 0 := by rw [hzero, map_zero]

theorem UpperTheory.exists_invariant_block_det_norm_eq_pow_of_mem_spectrum :
    ∀ {l : ℕ} [Fact l.Prime] (L : IntermediateField ℚ_[l] (Om l)) {d : ℕ} (F : Matrix (Fin d) (Fin d) ↥L), ∀ a ∈ spectrum (Om l) (F.map (algebraMap ↥L (Om l))), ∃ (r : ℕ) (Y : Matrix (Fin d) (Fin r) ↥L) (Z : Matrix (Fin r) (Fin d) ↥L) (F' : Matrix (Fin r) (Fin r) ↥L), 0 < r ∧ Z * Y = 1 ∧ F * Y = Y * F' ∧ ‖((F'.det : ↥L) : Om l)‖ = ‖a‖ ^ r := by
  intro l _ L d F a ha
  set p := minpoly (↥L) a with hp
  have hPdet : (Polynomial.aeval F p).det = 0 := by
    have hs2 := spectrum.subset_polynomial_aeval (F.map (algebraMap ↥L (Om l)))
      (p.map (algebraMap ↥L (Om l))) ⟨a, ha, rfl⟩
    beta_reduce at hs2
    rw [Polynomial.eval_map_algebraMap, hp, minpoly.aeval, Polynomial.aeval_map_algebraMap] at hs2
    have e := Polynomial.aeval_algHom_apply ((Algebra.ofId ↥L (Om l)).mapMatrix (m := Fin d)) F (minpoly (↥L) a)
    rw [show ((Algebra.ofId ↥L (Om l)).mapMatrix (m := Fin d)) F = F.map (algebraMap ↥L (Om l)) from rfl] at e
    rw [e, spectrum.zero_mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hs2
    have h3 : algebraMap ↥L (Om l) (Polynomial.aeval F (minpoly (↥L) a)).det = 0 := by
      rw [RingHom.map_det]
      exact hs2
    exact (map_eq_zero_iff _ (algebraMap ↥L (Om l)).injective).mp h3
  have hcomm : F * Polynomial.aeval F p = Polynomial.aeval F p * F := (aeval_mul_eq_mul_aeval_of_semiconj F F F rfl p).symm
  obtain ⟨r, Y, Z, F', hr, hZY, hFY, hPY⟩ := exists_invariant_subspace_in_ker_of_det_zero F (Polynomial.aeval F p) hPdet hcomm
  have hF' : Polynomial.aeval F' p = 0 := by
    have h1 := aeval_mul_eq_mul_aeval_of_semiconj F Y F' hFY p
    rw [hPY] at h1
    calc Polynomial.aeval F' p = (Z * Y) * Polynomial.aeval F' p := by rw [hZY, Matrix.one_mul]
      _ = Z * (Y * Polynomial.aeval F' p) := Matrix.mul_assoc _ _ _
      _ = 0 := by rw [← h1, Matrix.mul_zero]
  exact ⟨r, Y, Z, F', hr, hZY, hFY, norm_det_eq_pow_of_aeval_minpoly_eq_zero L F' a hF'⟩
end
