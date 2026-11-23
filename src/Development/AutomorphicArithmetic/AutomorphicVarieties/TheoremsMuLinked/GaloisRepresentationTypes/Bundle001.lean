module

import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CliffPrime
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.RegCosetFour
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle012
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle028
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdZero
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle054
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.ExistsStabilizerIndexDvdOfNotIrreducibleRestrict
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.Bundle004
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IrreducibleSpans.Burnside
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.RelKill
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Mathlib.Topology.Algebra.MvPolynomial
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.MatrixIrreducibility.IrrOfMatIrr

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th

private theorem irr2 {G κ k A : Type} [Group G] [Field κ] [IsAlgClosed κ] [Field k] [CommRing A]
    (r : G →* GL (Fin 2) κ) (hr : U3.MatIrr ⊤ (Pr.gm r)) (j : A →+* κ) (hj : Function.Injective j) (φ : A →+* k)
    (χ : G →* kˣ) (t : G → A) (ht : ∀ g, j (t g) = (Pr.gm r g).trace)
    (hχ : ∀ g, φ (t g) = (χ g : kˣ) + ((χ g)⁻¹ : kˣ)) (U : Subgroup G) [U.Normal] {u : G} (hu : u ∈ U)
    (hd : (Pr.gm r u).det = 1) (hne : χ u ^ 2 ≠ 1) : U3.MatIrr U (Pr.gm r) := by
  have hy : ((χ u : kˣ) : k) ^ 2 - 1 ≠ 0 := fun h => hne (Units.ext (by simpa [sub_eq_zero] using h))
  rcases Pr.cliffPrime G κ 2 Nat.prime_two r hr U with h | h | ⟨b, la, π, -, hla, hπ, htr⟩
  · exact h
  · exfalso
    obtain ⟨a, ha⟩ := h u hu
    have e : t u ^ 2 = 4 := by
      apply hj
      rw [map_pow, ht, map_ofNat]
      rw [ha] at hd ⊢
      simp only [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul] at hd ⊢
      push_cast
      linear_combination 4 * hd
    have e2 := congrArg φ e
    rw [map_pow, hχ, map_ofNat] at e2
    have e3 := (χ u).mul_inv
    apply pow_ne_zero 2 hy
    linear_combination ((χ u : kˣ) : k) ^ 2 * e2 - (2 * ((χ u : kˣ) : k) ^ 2 + (χ u : kˣ) * ((χ u)⁻¹ : kˣ) + 1) * e3
  · exfalso
    obtain ⟨g, hg⟩ := htr 0 1
    have hne' : ∀ i, π g i ≠ i := by
      intro i hi
      fin_cases i
      · exact absurd (hg.symm.trans hi) (by decide)
      · exact absurd ((π g).injective (hg.trans hi.symm)) (by decide)
    have tr0 : ∀ s ∈ U, (Pr.gm r (g * s)).trace = 0 := fun s hs => by
      rw [← Matrix.trace_toLin'_eq, LinearMap.trace_eq_matrix_trace κ b]
      refine Finset.sum_eq_zero fun i _ => ?_
      obtain ⟨a, ha⟩ := hπ g i
      have := hla i ⟨s, hs⟩
      simp only [Pr.gm] at this ha
      rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Matrix.toLin'_apply]
      simp only [Pr.gm, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
      rw [this, Matrix.mulVec_smul, ha]
      simp [hne' i]
    have z : ∀ s ∈ U, ((χ (g * s) : kˣ) : k) ^ 2 + 1 = 0 := fun s hs => by
      have e : t (g * s) = 0 := hj (by rw [ht, tr0 s hs, map_zero])
      have e2 := hχ (g * s)
      rw [e, map_zero] at e2
      have e3 := (χ (g * s)).mul_inv
      linear_combination -((χ (g * s) : kˣ) : k) * e2 - e3
    have z1 := z 1 U.one_mem
    have z2 := z u hu
    rw [mul_one] at z1
    rw [map_mul, Units.val_mul] at z2
    apply hy
    linear_combination ((χ u : kˣ) : k) ^ 2 * z1 - z2

private theorem pair2 {κ : Type} [Field κ] :
    ∃ J : GL (Fin 2) κ, ∀ M : Matrix (Fin 2) (Fin 2) κ, M.transpose * J.val * M = M.det • J.val := by
  refine ⟨⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩, fun M => ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

private theorem freeRes {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (L : Type) [Field L]
    [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (h : FreeAt l W) :
    FreeAt l (W.comp (Base.galEmb ℚ L Ω)) :=
  _root_.UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.freeRes L W h
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

private theorem exists_place_above_prime_alt (K : Type) [Field K] [NumberField K] (l : ℕ) [hl : Fact l.Prime] :
    ∃ v : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl.out
  haveI : (Ideal.span {(l : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  obtain ⟨Q, hQ, hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 K) (Ideal.span {(l : ℤ)})
    (by rw [(RingHom.injective_iff_ker_eq_bot (algebraMap ℤ (𝓞 K))).1 (RingHom.injective_int _)]; exact bot_le)
  have hm : ((l : ℕ) : 𝓞 K) ∈ Q := by
    have : (l : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := by
      change (l : ℤ) ∈ Ideal.under ℤ Q
      rw [hc]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ, fun h => ?_⟩, hm⟩
  rw [h, Ideal.mem_bot] at hm
  exact hl.out.ne_zero (by exact_mod_cast hm)

private theorem charpoly_eq_prod_flag_characters {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* GL (Fin n) k)
    (κ : Fin n → H →* kˣ) (h : W.HasFlag r κ) (s : H) :
    (W.mat r s).charpoly = ∏ i, ((X : Polynomial k) - C ((κ i s : kˣ) : k)) := by
  obtain ⟨g, hg⟩ := h
  have h1 := Matrix.charpoly_units_conj g (W.mat r s)
  have h2 : ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular id :=
    fun i j hij => (hg s).1 i j hij
  have h3 := Matrix.charpoly_of_upperTriangular _ h2
  rw [← h1]
  simp only [Units.val_mul, Matrix.coe_units_inv] at h3
  refine h3.trans ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  have h4 := (hg s).2 i
  simp only [Units.val_mul, Matrix.coe_units_inv] at h4
  rw [h4]

private theorem continuous_linear_closed {G κ : Type} [TopologicalSpace G] [Field κ] [TopologicalSpace κ] [IsTopologicalRing κ] [T1Space κ] {n : ℕ}
    (a : G → Matrix (Fin n) (Fin n) κ) (ha : Continuous a) : Pr.LinClosed a := by
  intro f
  have h : (fun g => f (a g)) = fun g => ∑ i, ∑ j, a g i j * f (Matrix.single i j 1) := by
    funext g
    conv_lhs => rw [Matrix.matrix_eq_sum_single (a g)]

    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_eq_mul, ← map_smul]
    simp
  have hc : Continuous fun g => f (a g) := by
    rw [h]
    fun_prop
  exact isClosed_singleton.preimage hc

private theorem absolute_irreducible_rank_four (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (F : W.GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    (two : (2 : ResidueField O) ≠ 0) (χ : Fin 4 → F.G₀ →* (ResidueField O)ˣ)
    (K : Type) [Field K] [IsAlgClosed K] [TopologicalSpace K] [IsTopologicalRing K] [T1Space K] (twoK : (2 : K) ≠ 0)
    (ρ : F.G₀ →* GL (Fin 4) K) (hρ : Continuous ρ) (hb : U3.MatIrr ⊤ (W.mat ρ))
    (A : Type) [CommRing A] (j : A →+* K) (φ : A →+* ResidueField O) (hj : Function.Injective j) (hred : Pr.RedTo ρ j φ χ)
    (u : F.G₀) (hg : u ∈ F.G') (a : Fin 4 → Kˣ) (hu : (W.mat ρ u).charpoly = ∏ i, (X - C (a i : K))) (hfr : Pr.FreeRatios a)
    (hc : ∀ η : F.G₀ →* (ResidueField O)ˣ, η ^ 2 = 1 → (F.eps O (ResidueField O)).ker ≤ η.ker → (∀ i, ∃ j, η * χ i = χ j) → η = 1)
    (hd : ∃ i j, ∀ n : ℕ, 0 < n → n ≤ 4 → (χ i / χ j) ^ n ≠ 1) : Th.TypeI F ρ ∧ Th.N3 F ρ := by
  classical
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  haveI hN : F.G'.Normal := MonoidHom.normal_ker _
  have hm : Continuous (W.mat ρ) := Units.continuous_val.comp hρ
  have hfa : ∀ s t, s ≠ t → ¬ IsOfFinOrder (a s / a t) := fun s t hst h => by
    obtain ⟨m, hm0, hm1⟩ := isOfFinOrder_iff_pow_eq_one.1 h
    rw [div_pow, div_eq_one] at hm1
    exact hfr s t hst m hm0 hm1
  have hsep := Ws.charpoly_pow_separable_of_eigenvalue_ratios_not_finOrder _ 4 _ a hu hfa
  have hcomm : commutator F.G₀ ≤ F.G' := Abelianization.commutator_subset_ker _
  have hI : Th.TypeI F ρ := by
    by_contra hI
    obtain ⟨V, S, hV0, hV1, hNS, hS, hSi⟩ := Ws.exists_stabilizer_index_dvd_of_not_irreducible_restriction K F.G₀ 4 (W.mat ρ) hb F.G' hcomm
      ⟨_, hg, by simpa using hsep 1 one_pos⟩ hI
    obtain ⟨η, hη, hSη, hcp⟩ := Ws.exists_sign_twist_charpoly_of_not_irreducible_restriction K F.G₀ twoK (W.mat ρ) hb S (hcomm.trans hNS) hSi fun h =>
      (h V fun s hs => (hS s).1 hs).elim hV0 hV1
    haveI : S.FiniteIndex := ⟨fun h => by simp [h] at hSi⟩
    have hSo : IsOpen (S : Set F.G₀) := by
      refine S.isOpen_of_isClosed_of_finiteIndex ?_
      have h1 := Ws.isClosed_setOf_matrix_stabilizes_submodule F.G₀ K 4 _ (continuous_linear_closed _ hm) V
      convert h1 using 1
      ext s
      exact hS s
    have hk := Ws.sign_char_eq_one_of_cyclotomic_sub_one_not_isUnit l hl F.G₀ (F.ε.comp F.η.ker.subtype) (F.ε_cont.comp continuous_subtype_val) η
      (Subgroup.isOpen_mono hSη hSo) (hNS.trans hSη)
    have h1 := hc (W.pushCh (Int.castRingHom (ResidueField O)) η) ?_ ?_
      (Th.Det.perm4 K (ResidueField O) A F.G₀ 4 ρ j φ χ η hj hred hcp)
    · refine hη (MonoidHom.ext fun s => ?_)
      rcases Int.units_eq_one_or (η s) with h | h
      · exact h
      · have h2 := congrArg Units.val (DFunLike.congr_fun h1 s)
        simp only [MonoidHom.comp_apply, h] at h2
        exact absurd (by simp at h2; linear_combination -h2) two
    · ext s
      rcases Int.units_eq_one_or (η s) with h | h <;> simp [h]
    · intro s hs
      have h2 : η s = 1 := hk s fun h => by
        have h3 := h.map ((algebraMap O (ResidueField O)).comp (algebraMap ℤ_[l] O))
        have h4 : ((algebraMap O (ResidueField O)).comp (algebraMap ℤ_[l] O)) ((F.ε.comp F.η.ker.subtype) s : ℤ_[l]) = 1 :=
          congrArg Units.val (MonoidHom.mem_ker.1 hs)
        rw [map_sub, h4, map_one, sub_self] at h3
        exact not_isUnit_zero h3
      simp [MonoidHom.mem_ker, h2]
  refine ⟨hI, ?_⟩
  have hsp : Submodule.span K (Set.range ((W.mat ρ).comp F.G'.subtype)) = ⊤ :=
    KStar.Schema.span_eq_top_of_irreducible _ fun N hN => hI N fun s hs => hN ⟨s, hs⟩
  have hsp' : Submodule.span K (Set.range (W.mat ρ)) = ⊤ :=
    KStar.Schema.span_eq_top_of_irreducible _ fun N hN => hb N fun s _ => hN s
  have hnc := Ws.exists_noncommuting_images_in_finiteIndex_normal_subgroup K (ResidueField O) A F.G₀ (W.mat ρ) j φ χ hj hred hsp' hd F.G' _ hg hsep
  refine Ws.exists_mem_open_inter_subgroup_of_cosetwise_finiteIndex F.G₀ F.G' (fun s => (W.mat ρ s).charpoly.Separable) fun V hV σ => ?_
  exact AlgebraTools.regCosetFour K F.G' twoK ((W.mat ρ).comp F.G'.subtype)
    (fun f => isClosed_singleton.preimage (f.continuous_eval.comp
      (continuous_pi fun p => (hm.comp continuous_subtype_val).matrix_elem p.1 p.2)))
    hsp ⟨⟨_, hg⟩, a, hu, hfa⟩ (fun N _ h2 h3 => hnc N h2 h3) V hV σ
end

section

section Factor

open IsLocalRing UpperTheory.V UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.Base

private theorem int_iff_norm {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by
      rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

private theorem loc_of_int {O R A : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [CommRing A]
    [Nontrivial A] [Algebra O A] [Algebra.IsIntegral O A] (f : R →ₐ[O] A) : IsLocalHom f := by
  let g : R →+* f.range := f.rangeRestrict
  have hg : Function.Surjective g := f.rangeRestrict_surjective
  haveI : IsLocalRing f.range := IsLocalRing.of_surjective' g hg
  have hl : IsLocalHom g := IsLocalHom.of_surjective _ hg
  haveI : Algebra.IsIntegral f.range A := Algebra.IsIntegral.tower_top (R := O)
  have h2 : IsLocalHom (algebraMap f.range A) := Algebra.IsIntegral.isLocalHom _ _
  exact ⟨fun x hx => hl.map_nonunit x (h2.map_nonunit (g x) hx)⟩

private theorem exists_fac {l : ℕ} [Fact l.Prime] {c : Coef l} {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R]
    (f : R →ₐ[c.O] PadicAlgCl l) (hf : IsLocPt f) :
    ∃ (A : Subalgebra c.O (PadicAlgCl l)) (_ : IsDiscreteValuationRing A) (_ : Module.Finite c.O A), ∀ x, f x ∈ A := by
  haveI : IsLocalRing c.O := c.dvr.toIsLocalRing
  haveI := (dvrFacts l c.O).2.2.2.1
  obtain ⟨E, hE⟩ := Loc.ptFin (l := l) R ((TrivSqZeroExt.inlAlgHom c.O _ _).comp f) hf
  have hE' : ∀ a, f a ∈ E.1 := fun a => (hE a).1
  haveI := E.2
  haveI : Algebra.IsIntegral ℤ_[l] c.O := Algebra.IsIntegral.of_finite ℤ_[l] c.O
  have hint : ∀ x, IsIntegral ℤ_[l] (f x) := fun x => by
    obtain ⟨a, ha⟩ := residue_surjective (res c.O R x)
    have hm : x - algebraMap c.O R a ∈ maximalIdeal R := by
      rw [← res_eq_zero_iff c.O, map_sub, AlgHom.commutes, ← ha]
      exact sub_self _
    have h1 : IsIntegral ℤ_[l] (f (algebraMap c.O R a)) := by
      rw [f.commutes]
      exact (Algebra.IsIntegral.isIntegral a).map (IsScalarTower.toAlgHom ℤ_[l] c.O (PadicAlgCl l))
    have h2 := ((int_iff_norm _).2 (hf _ hm).le).add h1
    rwa [← map_add, sub_add_cancel] at h2
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.abelian₂.dvr_intClosure l E.1
  let j : E.1 →ₐ[ℤ_[l]] PadicAlgCl l := E.1.val.restrictScalars ℤ_[l]
  have hj : Function.Injective j := Subtype.val_injective
  let e := (integralClosure ℤ_[l] E.1).equivMapOfInjective j hj
  let B := (integralClosure ℤ_[l] E.1).map j
  have hB : ∀ x, f x ∈ B := fun x => ⟨⟨f x, hE' x⟩, (isIntegral_algHom_iff j hj).1 (hint x), rfl⟩
  let A : Subalgebra c.O (PadicAlgCl l) := { B.toSubsemiring with algebraMap_mem' := fun a => f.commutes a ▸ hB _ }
  have d1 : IsDiscreteValuationRing B := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  have d2 : Module.Finite ℤ_[l] B := Module.Finite.equiv e.toLinearEquiv
  haveI : Module.Finite ℤ_[l] A := d2
  exact ⟨A, d1, Module.Finite.of_restrictScalars_finite ℤ_[l] c.O A, hB⟩

end Factor

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th

end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th

private theorem adL_conj {C G V : Type} [CommRing C] [Group G] [AddCommGroup V] [Module C V] (ρ : Representation C G V)
    (c : G → V) (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) (γ g : G) :
    c g = ρ γ (c (γ⁻¹ * g * γ)) + c γ - ρ g (c γ) := by
  have h1 := hc γ (γ⁻¹ * g * γ)
  rw [← mul_assoc, mul_inv_cancel_left, hc] at h1
  rw [eq_sub_iff_add_eq, h1, add_comm]

private theorem adL_rho {C G V : Type} [CommRing C] [Group G] [AddCommGroup V] [Module C V] (ρ : Representation C G V)
    (γ g : G) (x : V) : ρ γ (ρ (γ⁻¹ * g * γ) x) = ρ g (ρ γ x) := by
  rw [← Module.End.mul_apply, ← map_mul, ← mul_assoc, mul_inv_cancel_left, map_mul, Module.End.mul_apply]

private theorem adL_emb {F Ω K : Type} [Field F] [Field Ω] [Field K] [CharZero F] [Algebra F Ω] [IsAlgClosure F Ω]
    (j j₀ : Ω →+* K) (h : j₀.comp (algebraMap F Ω) = j.comp (algebraMap F Ω)) :
    ∃ γ : Ω ≃ₐ[F] Ω, ∀ y, j (γ y) = j₀ y := by
  letI : Algebra F K := (j.comp (algebraMap F Ω)).toAlgebra
  letI : Algebra Ω K := j.toAlgebra
  haveI : IsScalarTower F Ω K := IsScalarTower.of_algebraMap_eq' rfl
  let f : Ω →ₐ[F] K := { j₀ with commutes' := fun x => RingHom.congr_fun h x }
  exact ⟨f.restrictNormal' Ω, fun y => f.restrictNormal_commutes Ω y⟩

private theorem adL_above {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] (j : Ω →+* Formalism.BasicNotions.Loc.Om l) {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (φ : H →* Formalism.BasicNotions.Loc.GQ l) (ψ : H →* G F Ω) (hφ : Topology.IsOpenEmbedding φ) (hψ : Continuous ψ)
    (hj : ∀ h y, φ h (j y) = j (ψ h y))
    {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] C V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V] (ρ : Representation C (G F Ω) V)
    (c : G F Ω → V) (hc : c ∈ Z1 ρ) (hb : Af.IsBK l ρ c) : (fun h => c (ψ h)) ∈ Loc.finiteCocycles φ (ρ.comp ψ) := by
  obtain ⟨j₀, hj₀, h0⟩ := hb.above (j.comp (algebraMap F Ω))
  obtain ⟨γ, hγ⟩ := adL_emb j j₀ hj₀
  let ψ' : H →* G F Ω := (MulAut.conj (γ⁻¹ : G F Ω)).toMonoidHom.comp ψ
  have hψ' : ∀ h, ψ' h = γ⁻¹ * ψ h * γ := fun h => by simp [ψ']
  obtain ⟨-, x, hx⟩ := (Loc.bkAbove (F := F) j₀ φ ψ' hφ (fun h y => by
    rw [← hγ, hj, ← hγ, hψ']
    simp) ρ c hc).2 h0
  refine ⟨⟨hc.1.comp hψ, fun g h => (congrArg c (map_mul ψ g h)).trans (hc.2 _ _)⟩,
    TensorProduct.AlgebraTensorModule.map (ρ γ) LinearMap.id x - c γ ⊗ₜ[ℚ_[l]] 1, fun h => ?_⟩
  have e : ∀ w, TensorProduct.AlgebraTensorModule.map (ρ γ) LinearMap.id (Loc.actC φ (ρ.comp ψ') h w) =
      Loc.actC φ (ρ.comp ψ) h (TensorProduct.AlgebraTensorModule.map (ρ γ) LinearMap.id w) := fun w => by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      simp only [Loc.actC, TensorProduct.AlgebraTensorModule.map_tmul, MonoidHom.comp_apply, hψ', adL_rho, LinearMap.id_apply]
    | add u v hu hv => simp only [map_add (f := _), hu, hv]
  have h2 := congrArg (TensorProduct.AlgebraTensorModule.map (ρ γ) LinearMap.id) (hx h)
  rw [map_sub, e, TensorProduct.AlgebraTensorModule.map_tmul] at h2
  have h3 : Loc.actC φ (ρ.comp ψ) h (c γ ⊗ₜ[ℚ_[l]] 1) = ρ (ψ h) (c γ) ⊗ₜ[ℚ_[l]] 1 := by simp [Loc.actC]
  change c (ψ h) ⊗ₜ[ℚ_[l]] _ = _
  rw [adL_conj ρ c hc.2 γ (ψ h), TensorProduct.sub_tmul, TensorProduct.add_tmul, map_sub, h3]
  simp only [LinearMap.id_apply, hψ'] at h2
  rw [h2]
  abel

open scoped Pointwise in
private theorem adL_ine {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω} (γ : G F Ω)
    {g : G F Ω} (hg : g ∈ Ine (F := F) (γ • A)) : γ⁻¹ * g * γ ∈ Ine (F := F) A := by
  have m : ∀ y : Ω, γ y ∈ γ • A ↔ y ∈ A := fun y => ValuationSubring.smul_mem_pointwise_smul_iff (g := γ)
  refine ⟨?_, fun x hx => ?_⟩
  · have h1 : g • γ • A = γ • A := hg.1
    change (γ⁻¹ * g * γ) • A = A
    rw [mul_smul, mul_smul, h1, inv_smul_smul]
  · have h2 := hg.2 (γ x) (by rwa [ValuationSubring.valuation_le_one_iff, m, ← ValuationSubring.valuation_le_one_iff])
    have e : g (γ x) - γ x = γ ((γ⁻¹ * g * γ) x - x) := by simp
    rwa [e, valuation_lt_one_iff', m, ← map_inv₀, m, map_eq_zero_iff _ γ.injective, ← valuation_lt_one_iff'] at h2

private theorem adL_away {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime]
    {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] C V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V] (ρ : Representation C (G F Ω) V)
    (c : G F Ω → V) (hc : c ∈ Z1 ρ) (hb : Af.IsBK l ρ c) (w : HeightOneSpectrum (𝓞 F)) (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal)
    (A : ValuationSubring Ω) (hA : IsPlaceOver A w) : ∃ x : V, ∀ g ∈ Ine (F := F) A, c g = ρ g x - x := by
  obtain ⟨A₀, hA₀, x, hx⟩ := hb.away w hw
  obtain ⟨γ, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hA₀ hA
  refine ⟨ρ γ x - c γ, fun g hg => ?_⟩
  rw [adL_conj ρ c hc.2 γ g, hx _ (adL_ine γ hg), map_sub, adL_rho, map_sub]
  abel

private theorem adL_pr {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) : Function.Surjective V.pr := fun g => by
  obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
  obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
  exact ⟨σ, Subtype.ext hτ⟩

private theorem adL_desc {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G)
    (hφ : Function.Surjective φ) (ρ : G →* GL (Fin n) A) (hD : D.comap φ = W.GDet.ofRep (W.mat (ρ.comp φ))) :
    D = W.GDet.ofRep (W.mat ρ) := by
  refine CA.d_gext _ _ fun g i _ _ => ?_
  obtain ⟨h, rfl⟩ := hφ g
  have e : (D.comap φ).chi (MonoidAlgebra.single h 1) = D.chi (MonoidAlgebra.single (φ h) 1) := by
    change D.D A[X] (MonoidAlgebra.mapDomainRingHom A[X] φ _) = D.D A[X] _
    congr 1
    rw [map_sub]
    simp
  unfold W.GDet.lam
  rw [← e, hD, (AlgebraTools.Det.repApi (W.mat (ρ.comp φ))).2.1,
    (AlgebraTools.Det.repApi (W.mat ρ)).2.1]
  rfl

private theorem adL_triv {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : W.Resid V.frame c.O n} {B : W.UniversalOrdinaryDeterminantRing r}
    {ι : Qbar l ≃+* ℂ} {x : B.Pt} {ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)} (H : NiceAPt ι x ρ) :
    ∀ u, ∀ g ∈ r.Ip u, ρ g = 1 :=
  (Ws.Eb.relKill B x ρ ((AlgebraTools.Det.irrIffSpan (W.mat ρ)).1 fun N hN => H.irr N fun g _ v hv => hN g v hv)
    (adL_desc x.D V.pr (adL_pr V) ρ H.rep)).2
end
