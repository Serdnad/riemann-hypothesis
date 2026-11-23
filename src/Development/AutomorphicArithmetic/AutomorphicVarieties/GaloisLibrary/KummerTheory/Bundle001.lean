module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.GaloisCohomology.StatementLoc
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Group.Defs
import Formalism.GaloisCohomology.Statement
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.FieldTheory.Fixed
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.NumberField.Basic
import ReciprocityTheory.GaloisValuations.GlobalA
public import Mathlib.RingTheory.RootsOfUnity.Minpoly
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

section Index

variable {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (ρ : Representation R Γ M)
  (H : Subgroup Γ) (hH : ∀ g g', g ∉ H → g' ∉ H → g * g' ∈ H)
include hH

private theorem val_eq (z : Z1 ρ) (hz : ∀ g ∈ H, z.1 g = 0) {g g' : Γ} (hg : g ∉ H) (hg' : g' ∉ H) :
    z.1 g' = z.1 g := by
  have h := z.2.2 g (g⁻¹ * g')
  rw [hz _ (hH _ _ (fun h => hg (H.inv_mem_iff.1 h)) hg'), map_zero, add_zero, mul_inv_cancel_left] at h
  exact h

end Index
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem isCM_of_conj (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    (h : ∀ x : K, ∃ y : K, ∀ φ : K →+* ℂ, φ y = starRingEnd ℂ (φ x)) : IsCMField K := by
  classical
  choose c hc using h
  let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  have hcc : ∀ x, c (c x) = x := fun x => φ.injective (by rw [hc, hc, Complex.conj_conj])
  let τ : K ≃+* K :=
    { toFun := c
      invFun := c
      left_inv := hcc
      right_inv := hcc
      map_mul' := fun x y => φ.injective (by simp only [hc, map_mul])
      map_add' := fun x y => φ.injective (by simp only [hc, map_add (f := _)]) }
  let σ : K ≃ₐ[ℚ] K := AlgEquiv.ofRingEquiv (f := τ) (fun q => by simp)
  have hσ : ∀ ψ : K →+* ℂ, ComplexEmbedding.IsConj ψ σ := fun ψ => by
    ext x
    exact (hc x ψ).symm
  have hσ' : Nat.card (Subgroup.zpowers σ) = 2 := by
    rw [Nat.card_zpowers, ComplexEmbedding.orderOf_isConj_two_of_ne_one (hσ φ)]
    exact (ComplexEmbedding.isConj_ne_one_iff (hσ φ)).mpr <| IsTotallyComplex.complexEmbedding_not_isReal φ
  let L := (FixedPoints.intermediateField (Subgroup.zpowers σ) : IntermediateField ℚ K)
  have : IsTotallyReal L := ⟨fun w ↦ by
    obtain ⟨W, rfl⟩ := w.comap_surjective (K := K)
    dsimp only
    rw [← InfinitePlace.mk_embedding W, InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff,
      ComplexEmbedding.isReal_iff]
    ext x
    have hx : c x.1 = x.1 := x.2 ⟨σ, Subgroup.mem_zpowers σ⟩
    have := hc x.1 W.embedding
    rw [hx] at this
    exact this.symm⟩
  have : Algebra.IsQuadraticExtension L K := ⟨by
    have : Fintype (Subgroup.zpowers σ) := Fintype.ofFinite _
    rw [← hσ', Nat.card_eq_fintype_card]
    exact FixedPoints.finrank_eq_card (Subgroup.zpowers σ) K⟩
  exact IsCMField.ofCMExtension L K
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.homExt :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G F Ω)) (M : Type) [AddCommGroup M] (φ : cycU l U → M), IsClosed (U : Set (G F Ω)) → IsLocallyConstant φ → (∀ a b, φ (a * b) = φ a + φ b) →
    ∃ (n : ℕ) (ψ : levU l U n → M), IsLocallyConstant ψ ∧ (∀ a b, ψ (a * b) = ψ a + ψ b) ∧ ∀ u : cycU l U, ψ ⟨u.1, cycU_le_levU l U n u.2⟩ = φ u := by
  intro F Ω _ _ _ _ _ l _ U M _ φ hU hφ hmul
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI hroots : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have hlp : l.Prime := Fact.out
  have hφ1 : φ 1 = 0 := by
    have h := hmul 1 1
    simpa using h
  have hprinc : ∀ (x : ℤ_[l]ˣ) (n : ℕ), x ∈ KStar.TotallyRealRoots.princ l n ↔ PadicInt.toZModPow n (x : ℤ_[l]) = 1 := by
    intro x n
    simp only [KStar.TotallyRealRoots.princ, KStar.TotallyRealRoots.redPow, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map,
      Units.val_one, MonoidHom.coe_coe]
    exact Iff.rfl
  have hopen_n : ∀ n, IsOpen ((Subgroup.comap (cycZ F Ω l) (KStar.TotallyRealRoots.princ l n) : Subgroup (G F Ω)) : Set (G F Ω)) := by
    intro n
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
    haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hlp.ne_zero⟩
    apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
    rw [krullTopology_mem_nhds_one_iff]
    refine ⟨IntermediateField.adjoin F {ζ}, IntermediateField.adjoin.finiteDimensional
      ((hζ.isIntegral (Nat.pos_of_neZero _)).tower_top), ?_⟩
    intro σ hσ
    simp only [SetLike.mem_coe, Subgroup.mem_comap]
    rw [hprinc]
    rcases Nat.eq_zero_or_pos n with h0 | hn0
    · subst h0
      haveI : Subsingleton (ZMod (l ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero l)
      exact Subsingleton.elim _ _
    show (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G F Ω) Ω σ)).val.toZModPow n = 1
    rw [cyclotomicCharacter.toZModPow, eq_comm]
    apply modularCyclotomicCharacter.unique
    intro t ht
    obtain ⟨i, hi, rfl⟩ := (hζ.isUnit_unit NeZero.out).eq_pow_of_mem_rootsOfUnity ht
    rw [ZMod.val_one'', pow_one]
    · exact hσ ⟨ζ ^ i, pow_mem (IntermediateField.mem_adjoin_simple_self F ζ) _⟩
    · exact (one_lt_pow₀ hlp.one_lt hn0.ne').ne'
  have hprinc_anti : ∀ (x : ℤ_[l]ˣ) (n m : ℕ), n ≤ m → x ∈ KStar.TotallyRealRoots.princ l m → x ∈ KStar.TotallyRealRoots.princ l n := by
    intro x n m hnm hx
    rw [hprinc] at hx ⊢
    rw [← PadicInt.cast_toZModPow n m hnm, hx]
    exact ZMod.cast_one (pow_dvd_pow l hnm)
  have hlev_anti : ∀ n m : ℕ, n ≤ m → (levU l U m : Set (G F Ω)) ⊆ levU l U n := by
    intro n m hnm x hx
    simp only [levU, SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_comap] at hx ⊢
    exact ⟨hx.1, hprinc_anti _ n m hnm hx.2⟩
  have hclosed : ∀ n, IsClosed ((levU l U n : Subgroup (G F Ω)) : Set (G F Ω)) := by
    intro n
    simp only [levU, Subgroup.coe_inf]
    exact hU.inter (Subgroup.isClosed_of_isOpen _ (hopen_n n))
  obtain ⟨O, hOo, hOeq⟩ := isOpen_induced_iff.mp (hφ.isOpen_fiber (φ 1))
  have h1O : (1 : G F Ω) ∈ O := by
    have h : (1 : cycU l U) ∈ Subtype.val ⁻¹' O := by rw [hOeq]; rfl
    simpa using h
  obtain ⟨E, hEfin, hEnorm, hEsub⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal F Ω O).mp (hOo.mem_nhds h1O)
  haveI := hEfin
  haveI := hEnorm
  have hNnorm : (E.fixingSubgroup : Subgroup (G F Ω)).Normal := by
    rw [← IntermediateField.restrictNormalHom_ker]
    exact MonoidHom.normal_ker _
  have hNopen : IsOpen ((E.fixingSubgroup : Subgroup (G F Ω)) : Set (G F Ω)) := E.fixingSubgroup_isOpen
  have hNker : ∀ c : cycU l U, (c : G F Ω) ∈ E.fixingSubgroup → φ c = 0 := by
    intro c hc
    have h : c ∈ Subtype.val ⁻¹' O := hEsub hc
    rw [hOeq] at h
    rw [← hφ1]
    exact h
  have hwd : ∀ (c c' : cycU l U) (w w' : G F Ω), w ∈ E.fixingSubgroup → w' ∈ E.fixingSubgroup →
      (c : G F Ω) * w = c' * w' → φ c = φ c' := by
    intro c c' w w' hw hw' h
    have hmem : ((c'⁻¹ * c : cycU l U) : G F Ω) ∈ E.fixingSubgroup := by
      have e : ((c'⁻¹ * c : cycU l U) : G F Ω) = w' * w⁻¹ := by
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
        rw [eq_mul_inv_iff_mul_eq, mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [e]
      exact Subgroup.mul_mem _ hw' (Subgroup.inv_mem _ hw)
    have h0 := hNker _ hmem
    rw [hmul] at h0
    have hinv : φ c'⁻¹ + φ c' = 0 := by rw [← hmul]; simp [hφ1]
    have e1 : φ c'⁻¹ = -φ c' := eq_neg_of_add_eq_zero_left hinv
    rw [e1] at h0
    exact (neg_add_eq_zero.mp h0).symm
  have hinter : ∀ x ∈ ⋂ n, (levU l U n : Set (G F Ω)), x ∈ cycU l U := by
    intro x hx
    simp only [Set.mem_iInter, levU, SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_comap] at hx
    simp only [cycU, Subgroup.mem_inf, MonoidHom.mem_ker]
    refine ⟨(hx 0).1, ?_⟩
    apply Units.ext
    apply (PadicInt.ext_of_toZModPow).mp
    intro n
    rw [(hprinc _ n).mp (hx n).2, Units.val_one, map_one]
  obtain ⟨n, hn⟩ := exists_subset_nhds_of_compactSpace (X := G F Ω) (ι := ℕ)
    (V := fun n => (levU l U n : Set (G F Ω)))
    (fun i j => ⟨max i j, hlev_anti _ _ (le_max_left _ _), hlev_anti _ _ (le_max_right _ _)⟩)
    hclosed
    (U := {a | ∃ c ∈ cycU l U, ∃ w ∈ E.fixingSubgroup, a = c * w})
    (by
      apply mem_nhdsSet_iff_forall.mpr
      intro x hx
      have hxc := hinter x hx
      refine Filter.mem_of_superset
        (IsOpen.mem_nhds (hNopen.preimage (continuous_const_mul x⁻¹)) (by simpa using Subgroup.one_mem _))
        (fun a ha => ⟨x, hxc, x⁻¹ * a, ha, by group⟩))
  have hex : ∀ y : levU l U n, ∃ c : cycU l U, ∃ w ∈ E.fixingSubgroup, (y : G F Ω) = c * w := by
    intro y
    obtain ⟨c, hc, w, hw, e⟩ := hn y.2
    exact ⟨⟨c, hc⟩, w, hw, e⟩
  choose cf wf hwf hcw using hex
  refine ⟨n, fun y => φ (cf y), ?_, ?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro y
    refine ⟨{z : levU l U n | (y : G F Ω)⁻¹ * z ∈ E.fixingSubgroup},
      hNopen.preimage (continuous_const.mul continuous_subtype_val), by simpa using Subgroup.one_mem _, ?_⟩
    intro z hz
    exact hwd (cf z) (cf y) (wf z) (wf y * ((y : G F Ω)⁻¹ * z)) (hwf z)
      (Subgroup.mul_mem _ (hwf y) hz)
      (by rw [← hcw z, ← mul_assoc, ← hcw y]; group)
  · intro a b
    rw [← hmul]
    have hv : ((cf b : G F Ω)⁻¹ * wf a * cf b) * wf b ∈ E.fixingSubgroup := by
      refine Subgroup.mul_mem _ ?_ (hwf b)
      have := hNnorm.conj_mem _ (hwf a) ((cf b : G F Ω)⁻¹)
      simpa using this
    refine hwd (cf (a * b)) (cf a * cf b) (wf (a * b)) _ (hwf _) hv ?_
    rw [← hcw (a * b), Subgroup.coe_mul, hcw a, hcw b, Subgroup.coe_mul]
    group
  · intro u
    exact hwd _ u (wf _) 1 (hwf _) (Subgroup.one_mem _) (by rw [← hcw, mul_one])
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem mem_princ_iff_norm_sub_one_le (l : ℕ) [Fact l.Prime] (a : ℕ) (x : ℤ_[l]ˣ) :
    x ∈ KStar.TotallyRealRoots.princ l a ↔ ‖(x : ℤ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(a : ℤ)) := by
  have h : x ∈ KStar.TotallyRealRoots.princ l a ↔ PadicInt.toZModPow a (x : ℤ_[l]) = 1 := by
    simp [KStar.TotallyRealRoots.princ, KStar.TotallyRealRoots.redPow, MonoidHom.mem_ker, Units.ext_iff]
  rw [h, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
    map_sub, map_one, sub_eq_zero]

private theorem princ_isClosed (l : ℕ) [Fact l.Prime] (a : ℕ) :
    IsClosed ((KStar.TotallyRealRoots.princ l a : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
  have e : ((KStar.TotallyRealRoots.princ l a : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) =
      {x : ℤ_[l]ˣ | ‖(x : ℤ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(a : ℤ))} := by
    ext x
    exact mem_princ_iff_norm_sub_one_le l a x
  rw [e]
  exact isClosed_le (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const

private theorem princ_antitone (l : ℕ) [Fact l.Prime] {a b : ℕ} (hab : a ≤ b) (x : ℤ_[l]ˣ)
    (hx : x ∈ KStar.TotallyRealRoots.princ l b) : x ∈ KStar.TotallyRealRoots.princ l a := by
  rw [mem_princ_iff_norm_sub_one_le] at hx ⊢
  refine hx.trans (zpow_le_zpow_right₀ ?_ (by omega))
  exact_mod_cast (Fact.out : l.Prime).one_lt.le

private theorem eq_one_of_mem_all_princ (l : ℕ) [Fact l.Prime] (x : ℤ_[l]ˣ)
    (hx : ∀ a, x ∈ KStar.TotallyRealRoots.princ l a) : x = 1 := by
  apply Units.ext
  refine (PadicInt.ext_of_toZModPow (x := (x : ℤ_[l])) (y := 1)).mp fun a => ?_
  have h := hx a
  simp only [KStar.TotallyRealRoots.princ, KStar.TotallyRealRoots.redPow, MonoidHom.mem_ker, Units.ext_iff] at h
  simpa using h

theorem UpperTheory.V.Kum.levCompact :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G F Ω)) (n : ℕ) (T : Type) [TopologicalSpace T] [CompactSpace T] (M : Type) [Zero M] (ψ : T × levU l U n → M), IsClosed (U : Set (G F Ω)) → IsLocallyConstant ψ →
    (∀ t (u : levU l U n), u.1 ∈ cycU l U → ψ (t, u) = 0) → ∃ m, n ≤ m ∧ ∀ t (u : levU l U n), u.1 ∈ levU l U m → ψ (t, u) = 0 := by
  intro F Ω _ _ _ _ _ l _ U n T _ _ M _ ψ hU hψ h0
  have memL : ∀ (m : ℕ) (x : G F Ω), x ∈ levU l U m ↔ x ∈ U ∧ cycZ F Ω l x ∈ KStar.TotallyRealRoots.princ l m := by
    intro m x
    simp [UpperTheory.V.Base.levU, Subgroup.mem_inf, Subgroup.mem_comap]
  have memC : ∀ x : G F Ω, x ∈ cycU l U ↔ x ∈ U ∧ cycZ F Ω l x = 1 := by
    intro x
    simp [UpperTheory.V.Base.cycU, Subgroup.mem_inf, MonoidHom.mem_ker]
  have closedL : ∀ m : ℕ, IsClosed ((levU l U m : Subgroup (G F Ω)) : Set (G F Ω)) := by
    intro m
    have e : ((levU l U m : Subgroup (G F Ω)) : Set (G F Ω)) =
        (U : Set (G F Ω)) ∩ (cycZ F Ω l) ⁻¹' ((KStar.TotallyRealRoots.princ l m : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
      ext x
      exact memL m x
    rw [e]
    exact hU.inter ((princ_isClosed l m).preimage (continuous_cycZ F Ω l))
  haveI : CompactSpace (levU l U n) := isCompact_iff_compactSpace.mp (closedL n).isCompact
  let K : Set (T × levU l U n) := {p | ψ p ≠ 0}
  have hKc : IsClosed K := by
    have ho : IsOpen (ψ ⁻¹' {0}) := hψ.isOpen_fiber 0
    exact ho.isClosed_compl
  let t : ℕ → Set (T × levU l U n) := fun m => {p | (p.2 : G F Ω) ∈ levU l U m}
  have htc : ∀ m, IsClosed (t m) := fun m =>
    (closedL m).preimage (continuous_subtype_val.comp continuous_snd)
  have hst : K ∩ ⋂ m, t m = ∅ := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_and]
    intro hp hall
    apply hp
    obtain ⟨s, u⟩ := p
    apply h0 s u
    rw [memC]
    refine ⟨((memL n u.1).1 u.2).1, eq_one_of_mem_all_princ l _ fun a => ((memL a u.1).1 (hall a)).2⟩
  obtain ⟨v, hv⟩ := hKc.isCompact.elim_finite_subfamily_closed t htc (Set.disjoint_iff_inter_eq_empty.mpr hst)
  refine ⟨max n (v.sup id), le_max_left _ _, ?_⟩
  intro s u hu
  by_contra hne
  have hmem : (s, u) ∈ K ∩ ⋂ i ∈ v, t i := by
    refine ⟨hne, ?_⟩
    simp only [Set.mem_iInter]
    intro i hi
    show (u : G F Ω) ∈ levU l U i
    rw [memL] at hu ⊢
    refine ⟨hu.1, princ_antitone l ?_ _ hu.2⟩
    exact (Finset.le_sup (f := id) hi).trans (le_max_right _ _)
  exact Set.disjoint_left.mp hv hmem.1 hmem.2
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.galOfCyc :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (E K : Type) [Field E] [Field K] [Algebra E K] [Algebra E Ω] [Algebra K Ω] [IsScalarTower E K Ω] [IsCyclotomicExtension {l ^ n} E K], galOf F K Ω = levU l (galOf F E Ω) n := by
  intro F Ω _ _ _ _ _ l _ n E K _ _ _ _ _ _ _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero (l : Ω) := ⟨by exact_mod_cast (Fact.out : l.Prime).ne_zero⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  ext σ
  have key : ∀ t : Ω, t ^ (l ^ n) = 1 →
      σ t = t ^ ((cycZ F Ω l σ).val.toZModPow n).val := fun t ht =>
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G F Ω) Ω σ) t ht
  show σ ∈ galOf F K Ω ↔ σ ∈ galOf F E Ω ⊓ Subgroup.comap (cycZ F Ω l) (KStar.TotallyRealRoots.princ l n)
  rw [Subgroup.mem_inf, Subgroup.mem_comap, KStar.TotallyRealRoots.princ, MonoidHom.mem_ker, KStar.TotallyRealRoots.redPow]
  constructor
  · intro h
    have hE : σ ∈ galOf F E Ω := fun x => by
      have hx := h (algebraMap E K x)
      rwa [← IsScalarTower.algebraMap_apply] at hx
    refine ⟨hE, ?_⟩
    have hζ : IsPrimitiveRoot (algebraMap K Ω (IsCyclotomicExtension.zeta (l ^ n) E K)) (l ^ n) :=
      (IsCyclotomicExtension.zeta_spec (l ^ n) E K).map_of_injective (algebraMap K Ω).injective
    have h1 := key _ hζ.pow_eq_one
    rw [h (IsCyclotomicExtension.zeta (l ^ n) E K)] at h1
    have hfin : IsOfFinOrder (algebraMap K Ω (IsCyclotomicExtension.zeta (l ^ n) E K)) :=
      orderOf_pos_iff.mp (by rw [← hζ.eq_orderOf]; exact Nat.pos_of_neZero _)
    have e : (algebraMap K Ω (IsCyclotomicExtension.zeta (l ^ n) E K)) ^
        ((cycZ F Ω l σ).val.toZModPow n).val =
        (algebraMap K Ω (IsCyclotomicExtension.zeta (l ^ n) E K)) ^ 1 := by
      rw [pow_one]
      exact h1.symm
    have h3 : ((cycZ F Ω l σ).val.toZModPow n).val ≡ 1 [MOD l ^ n] := by
      have h5 := hfin.pow_eq_pow_iff_modEq.mp e
      rwa [← hζ.eq_orderOf] at h5
    ext
    have h4 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h3
    rw [ZMod.natCast_zmod_val, Nat.cast_one] at h4
    simpa using h4
  · rintro ⟨hE, hc⟩
    have hc' : (cycZ F Ω l σ).val.toZModPow n = 1 := by
      have := congrArg Units.val hc
      simpa using this
    intro x
    let f1 : K →ₐ[E] Ω := IsScalarTower.toAlgHom E K Ω
    let f2 : K →ₐ[E] Ω :=
      { toRingHom := (σ : Ω →+* Ω).comp (algebraMap K Ω)
        commutes' := fun r => by
          show σ (algebraMap K Ω (algebraMap E K r)) = algebraMap E Ω r
          rw [← IsScalarTower.algebraMap_apply]
          exact hE r }
    have hx := IsCyclotomicExtension.adjoin_roots (S := {l ^ n}) (A := E) (B := K) x
    have hmem : x ∈ AlgHom.equalizer f1 f2 := by
      refine Algebra.adjoin_le (fun b hb => ?_) hx
      obtain ⟨m, hm, -, hbm⟩ := hb
      rw [Set.mem_singleton_iff] at hm
      subst hm
      have ht : (algebraMap K Ω b) ^ (l ^ n) = 1 := by rw [← map_pow, hbm, map_one]
      show algebraMap K Ω b = σ (algebraMap K Ω b)
      rw [key _ ht, hc', ZMod.val_one_eq_one_mod]
      conv_lhs => rw [← pow_one (algebraMap K Ω b), ← Nat.mod_add_div 1 (l ^ n), pow_add, pow_mul, ht, one_pow, mul_one]
    exact ((AlgHom.mem_equalizer f1 f2 x).mp hmem).symm
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem card_simple (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M]
    [h : IsSimpleModule ℤ_[l] M] : Nat.card M = l := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp h
  have hIm : I = IsLocalRing.maximalIdeal ℤ_[l] := IsLocalRing.eq_maximalIdeal hI
  subst hIm
  rw [Nat.card_congr e.toEquiv]
  have f := RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective (PadicInt.toZMod (p := l)))
  have g := Ideal.quotEquivOfEq (PadicInt.ker_toZMod (p := l))
  rw [← Nat.card_congr g.toEquiv, Nat.card_congr f.toEquiv, Nat.card_zmod]

private theorem aux (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M]
    (h : IsFiniteLength ℤ_[l] M) : ∃ k : ℕ, Module.length ℤ_[l] M = k ∧ Nat.card M = l ^ k := by
  induction h with
  | of_subsingleton =>
    exact ⟨0, by rw [Module.length_eq_zero]; rfl, by rw [Nat.card_of_subsingleton (0 : _)]; simp⟩
  | @of_simple_quotient M _ _ N _ _ ih =>
    obtain ⟨k, hk, hc⟩ := ih
    refine ⟨k + 1, ?_, ?_⟩
    · rw [Module.length_eq_add_of_exact N.subtype N.mkQ (Submodule.injective_subtype N)
        (Submodule.mkQ_surjective N) (LinearMap.exact_subtype_mkQ N), hk, Module.length_eq_one]
      rfl
    · rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.toAddSubgroup]
      have h1 : Nat.card (M ⧸ N.toAddSubgroup) = l := card_simple l (M ⧸ N)
      have h2 : Nat.card N.toAddSubgroup = l ^ k := hc
      rw [h1, h2, pow_succ, mul_comm]

theorem UpperTheory.V.Kum.lenOfCard :
    ∀ (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] [Finite M], ∃ k : ℕ, Module.length ℤ_[l] M = k ∧ Nat.card M = l ^ k := by
  intro l _ M _ _ _
  exact aux l M (isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩)
end
