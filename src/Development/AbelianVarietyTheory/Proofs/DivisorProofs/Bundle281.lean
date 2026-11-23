module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle126
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

section

open IsLocalRing Polynomial

namespace GlobalTheory.LocAcyc

theorem torsorsTrivial_of_ringEquiv {B B' : Type} [CommRing B] [CommRing B'] (e : B ≃+* B')
    (q : ℕ) (h : TorsorsTrivial B' q) : TorsorsTrivial B q := by
  intro D _ _ hfin hproj hff act hbij
  let : Algebra B' B := e.symm.toRingHom.toAlgebra
  let : Algebra B' D := ((algebraMap B D).comp e.symm.toRingHom).toAlgebra
  have : IsScalarTower B' B D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hmap : ∀ b : B, algebraMap B D b = algebraMap B' D (e b) := by
    intro b
    change algebraMap B D b = algebraMap B D (e.symm (e b))
    rw [RingEquiv.symm_apply_apply]
  have hsmul : ∀ (b : B) (d : D), b • d = (e b) • d := by
    intro b d
    rw [Algebra.smul_def, Algebra.smul_def, hmap]
  let eL : B ≃ₗ[B'] B' :=
    { e.toAddEquiv with
      map_smul' := fun b' b => by
        change e (e.symm b' * b) = b' * e b
        rw [map_mul, RingEquiv.apply_symm_apply] }
  have : Module.FaithfullyFlat B' B := Module.FaithfullyFlat.of_linearEquiv B' B' eL
  have : Module.Finite B' B := Module.Finite.equiv eL.symm
  have : Module.FaithfullyFlat B D := hff
  have : Module.Finite B D := hfin
  have hfin' : Module.Finite B' D := Module.Finite.trans B D
  have hff' : Module.FaithfullyFlat B' D := Module.FaithfullyFlat.trans B' B D
  have i1 : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  have i2 : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.symm _ _
  let sl : D ≃ₛₗ[e.toRingHom] D :=
    { AddEquiv.refl D with
      map_smul' := fun b d => hsmul b d }
  have := hproj
  have hproj' : Module.Projective B' D := Module.Projective.of_equiv sl
  let act' : Multiplicative (ZMod q) →* (D ≃ₐ[B'] D) :=
    { toFun := fun g => (act g).restrictScalars B'
      map_one' := by ext x; simp
      map_mul' := fun g g' => by ext x; simp }
  have : TensorProduct.CompatibleSMul B' B D D := ⟨fun b m n => by
    rw [hsmul b m, hsmul b n, TensorProduct.smul_tmul]⟩
  let s : TensorProduct B' D D ≃ₗ[B'] TensorProduct B D D :=
    TensorProduct.equivOfCompatibleSMul B B' B' D D
  have hcomp : ∀ x : TensorProduct B' D D,
      Algebra.TensorProduct.productMap
        (AlgHom.pi (fun _ : Multiplicative (ZMod q) => AlgHom.id B' D))
        (AlgHom.pi (fun g => (act' g).toAlgHom)) x =
      Algebra.TensorProduct.productMap
        (AlgHom.pi (fun _ : Multiplicative (ZMod q) => AlgHom.id B D))
        (AlgHom.pi (fun g => (act g).toAlgHom)) (s x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  obtain ⟨σ⟩ := h D hfin' hproj' hff' act' (by
    convert hbij.comp s.bijective using 1
    exact funext hcomp)
  refine ⟨{ toRingHom := (e.symm : B' →+* B).comp σ.toRingHom, commutes' := fun b => ?_ }⟩
  change e.symm (σ (algebraMap B D b)) = b
  rw [hmap, σ.commutes]
  exact e.symm_apply_apply b

end GlobalTheory.LocAcyc

namespace GlobalTheory.LocAcyc

theorem nonempty_genFib_equiv {T T' O : Type} [CommRing T] [IsDomain T] [CommRing T'] [CommRing O]
    [Algebra T T'] [Algebra T O] [Algebra T' O] [IsScalarTower T T' O] (M : Submonoid T)
    (hM : M ≤ nonZeroDivisors T) [IsLocalization M T'] :
    Nonempty (GenFib T O ≃+* GenFib T' O) := by
  have : IsDomain T' := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
  have hinj : Function.Injective (algebraMap T T') := IsLocalization.injective T' hM
  set M1 := Algebra.algebraMapSubmonoid O (nonZeroDivisors T)
  set M2 := Algebra.algebraMapSubmonoid O (nonZeroDivisors T')
  have h1 : M1 ≤ M2 := by
    rintro x ⟨s, hs, rfl⟩
    refine ⟨algebraMap T T' s, ?_, (IsScalarTower.algebraMap_apply T T' O s).symm⟩
    have hs' : s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hs
    exact mem_nonZeroDivisors_iff_ne_zero.mpr fun h => hs' (hinj (by rw [h, map_zero]))
  have h2 : ∀ x : M2, ∃ m : O, m * x ∈ M1 := by
    rintro ⟨x, y, hy, rfl⟩
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M y
    refine ⟨algebraMap T O s, a, ?_, ?_⟩
    · have hy' : IsLocalization.mk' T' a s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hy
      refine mem_nonZeroDivisors_iff_ne_zero.mpr ?_
      rintro rfl
      exact hy' (IsLocalization.mk'_zero s)
    · change algebraMap T O a = algebraMap T O s * algebraMap T' O (IsLocalization.mk' T' a s)
      rw [IsScalarTower.algebraMap_apply T T' O s, ← map_mul, IsLocalization.mk'_spec',
        ← IsScalarTower.algebraMap_apply]
  have : IsLocalization M2 (GenFib T O) :=
    IsLocalization.isLocalization_of_is_exists_mul_mem (S := GenFib T O) (M := M1) (N := M2) h1 h2
  exact ⟨(IsLocalization.algEquiv M2 (GenFib T O) (GenFib T' O)).toRingEquiv⟩

end GlobalTheory.LocAcyc

namespace GlobalTheory.LocAcyc


open CategoryTheory in
theorem keyAll_of_keyLocal : KeyLocal → KeyAll := by
  intro hL T O _ _ _ _ _ _ _ hAIC P _ φ hφ hSH q hq hqu
  set p : Ideal T := P.comap (C : T →+* T[X]) with hp
  have : p.IsPrime := Ideal.comap_isPrime _ _
  let T' := Localization.AtPrime p
  have hle : p.primeCompl ≤ nonZeroDivisors T := p.primeCompl_le_nonZeroDivisors
  have hAIC' : AbsIntClosed T' :=
    ((absIntClosed_localization_and_quotient T ⟨inferInstance, hAIC⟩).1 p.primeCompl
      (fun h => h (zero_mem p))).2

  have hTO : ∀ a : T, algebraMap T O a = algebraMap T[X] O (C a) := fun a => by
    rw [IsScalarTower.algebraMap_apply T T[X] O, Polynomial.algebraMap_eq]
  have hunit : ∀ s : p.primeCompl, IsUnit (algebraMap T O s) := by
    intro s
    have hs : C (s : T) ∈ P.primeCompl := s.2
    have hu := (IsLocalization.map_units (Localization.AtPrime P)
      (⟨C (s : T), hs⟩ : P.primeCompl)).map φ
    rw [← RingHom.comp_apply, hφ] at hu
    rwa [hTO]
  let : Algebra T' O := (IsLocalization.lift (M := p.primeCompl) (S := T') hunit).toAlgebra
  have : IsScalarTower T T' O :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq hunit x).symm)
  let : Algebra T'[X] O := (eval₂RingHom (algebraMap T' O) (algebraMap T[X] O X)).toAlgebra
  have : IsScalarTower T' T'[X] O :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      change _ = eval₂ (algebraMap T' O) (algebraMap T[X] O X) (algebraMap T' T'[X] x)
      rw [Polynomial.algebraMap_eq, eval₂_C])

  let : Algebra T[X] T'[X] := Polynomial.algebra T T'
  have : IsLocalization (Submonoid.map C p.primeCompl) T'[X] :=
    Polynomial.isLocalization p.primeCompl T'
  have hdisj : Disjoint (Submonoid.map C p.primeCompl : Set T[X]) (P : Set T[X]) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsP
    exact hs hsP
  set P' : Ideal T'[X] := P.map (algebraMap T[X] T'[X]) with hP'
  have hP'prime : P'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ T'[X] P inferInstance hdisj
  have hcomapP' : P'.comap (algebraMap T[X] T'[X]) = P :=
    IsLocalization.under_map_of_isPrime_disjoint _ T'[X] inferInstance hdisj
  have hCcomm : ∀ a : T, C (algebraMap T T' a) = algebraMap T[X] T'[X] (C a) := fun a => by
    change _ = (C a).map (algebraMap T T')
    rw [Polynomial.map_C]
  have hmax : P'.comap (C : T' →+* T'[X]) = maximalIdeal T' := by
    apply (IsLocalization.orderEmbedding p.primeCompl T').injective
    change (P'.comap C).under T = (maximalIdeal T').under T
    rw [IsLocalization.AtPrime.under_maximalIdeal T' p]
    ext a
    change C (algebraMap T T' a) ∈ P' ↔ C a ∈ P
    rw [hCcomm, ← Ideal.mem_comap, hcomapP']

  have : IsLocalization.AtPrime (Localization.AtPrime P') P := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.map C p.primeCompl) (Localization.AtPrime P') P'
    have hc : (P'.comap (algebraMap T[X] T'[X])).primeCompl = P.primeCompl := by
      ext x; simp only [Ideal.mem_primeCompl_iff, hcomapP']
    unfold IsLocalization.AtPrime at this ⊢
    rw [hc] at this
    exact this
  let e : Localization.AtPrime P ≃ₐ[T[X]] Localization.AtPrime P' :=
    IsLocalization.algEquiv P.primeCompl _ _
  let φ' : Localization.AtPrime P' →+* O := φ.comp e.symm.toRingEquiv.toRingHom
  have hOO : (algebraMap T'[X] O).comp (algebraMap T[X] T'[X]) = algebraMap T[X] O := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · change eval₂ (algebraMap T' O) (algebraMap T[X] O X) ((C a).map (algebraMap T T')) = _
      rw [Polynomial.map_C, eval₂_C, ← IsScalarTower.algebraMap_apply, hTO]
    · change eval₂ (algebraMap T' O) (algebraMap T[X] O X) ((X : T[X]).map (algebraMap T T')) = _
      rw [Polynomial.map_X, eval₂_X]
  have hφ' : φ'.comp (algebraMap T'[X] (Localization.AtPrime P')) = algebraMap T'[X] O := by
    refine IsLocalization.ringHom_ext (Submonoid.map C p.primeCompl) ?_
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, hOO]
    refine RingHom.ext fun f => ?_
    change φ (e.symm (algebraMap T[X] _ f)) = _
    rw [AlgEquiv.commutes, ← RingHom.comp_apply, hφ]
  have hSH' : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ' := by
    obtain ⟨h1, h2, h3, h4⟩ := hSH
    refine ⟨h1, h2, ?_, ?_⟩
    · refine ⟨fun a ha => ?_⟩
      change IsUnit (φ (e.symm a)) at ha
      have h5 : IsUnit (e.symm a) := h3.map_nonunit _ ha
      simpa using h5.map e
    · have : (RingHom.toMorphismProperty @RingHom.Etale).RespectsIso :=
        RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso
      unfold GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale at h4 ⊢
      rw [CommRingCat.ofHom_comp]
      have : IsIso (CommRingCat.ofHom e.symm.toRingEquiv.toRingHom) :=
        inferInstanceAs (IsIso (e.symm.toRingEquiv.toCommRingCatIso).hom)
      exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr h4
  have hqu' : IsUnit (q : T') := by
    simpa using hqu.map (algebraMap T T')
  have key := hL T' O hAIC' P' φ' hφ' hSH' hmax trivial q hq hqu'
  obtain ⟨eG⟩ := nonempty_genFib_equiv (T := T) (T' := T') (O := O) p.primeCompl hle
  exact torsorsTrivial_of_ringEquiv eG q key

end GlobalTheory.LocAcyc
end

section

open IsLocalRing Polynomial

namespace GlobalTheory.LocAcyc.Translate

theorem exists_X_sub_C_mem_of_isAlgClosed (k : Type) [Field k] [IsAlgClosed k]
    (Q : Ideal k[X]) [hQ : Q.IsPrime] :
    ∀ (n : ℕ) (g : k[X]), g ≠ 0 → g.natDegree = n → g ∈ Q → ∃ r : k, X - C r ∈ Q := by
  intro n
  induction n with
  | zero =>
    intro g hg hdeg hgQ
    exfalso
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg] at hgQ hg
    have h0 : g.coeff 0 ≠ 0 := fun h => hg (by rw [h, map_zero])
    exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hgQ (isUnit_C.2 (IsUnit.mk0 _ h0)))
  | succ n ih =>
    intro g hg hdeg hgQ
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_root g (by
      rw [Polynomial.degree_eq_natDegree hg, hdeg]; exact_mod_cast Nat.succ_ne_zero n)
    have hdiv := (mul_divByMonic_eq_iff_isRoot (p := g) (a := r)).2 hr
    rw [← hdiv] at hgQ hg
    rcases hQ.mem_or_mem hgQ with h | h
    · exact ⟨r, h⟩
    · refine ih _ (right_ne_zero_of_mul hg) ?_ h
      have := natDegree_divByMonic g (monic_X_sub_C r)
      rw [natDegree_X_sub_C] at this
      rw [this, hdeg]; omega

theorem exists_X_sub_C_mem (T : Type) [CommRing T] [IsLocalRing T] [IsAlgClosed (ResidueField T)]
    (P : Ideal T[X]) [hPp : P.IsPrime] (hP : P.comap (C : T →+* T[X]) = maximalIdeal T)
    (hne : P ≠ (maximalIdeal T).map (C : T →+* T[X])) : ∃ c : T, X - C c ∈ P := by
  set π : T[X] →+* (ResidueField T)[X] := mapRingHom (residue T) with hπ
  have hsurj : Function.Surjective π := map_surjective _ residue_surjective
  have hker : RingHom.ker π = (maximalIdeal T).map (C : T →+* T[X]) := by
    rw [hπ, ker_mapRingHom, ker_residue]
  have hle : RingHom.ker π ≤ P := by
    rw [hker, Ideal.map_le_iff_le_comap, hP]
  haveI hQ : (P.map π).IsPrime := Ideal.map_isPrime_of_surjective hsurj hle
  have hPQ : (P.map π).comap π = P := by
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.2 hle
  have hQbot : P.map π ≠ ⊥ := by
    intro h
    apply hne
    rw [← hker, ← hPQ, h, RingHom.ker_eq_comap_bot]
  obtain ⟨g, hgQ, hg⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQbot
  obtain ⟨r, hr⟩ := exists_X_sub_C_mem_of_isAlgClosed _ _ _ g hg rfl hgQ
  obtain ⟨c, rfl⟩ := residue_surjective r
  refine ⟨c, ?_⟩
  rw [← hPQ, Ideal.mem_comap]
  simpa [hπ] using hr

end GlobalTheory.LocAcyc.Translate

namespace GlobalTheory.LocAcyc.Translate

theorem keyClosedPts_of_keyOrigin : GlobalTheory.LocAcyc.KeyOrigin → GlobalTheory.LocAcyc.KeyClosedPts := by
  intro hKO
  unfold GlobalTheory.LocAcyc.KeyOrigin GlobalTheory.LocAcyc.KeyLocalWith at hKO
  unfold GlobalTheory.LocAcyc.KeyClosedPts GlobalTheory.LocAcyc.KeyLocalWith
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hPm hne q hq hqu
  have hne' : P ≠ (maximalIdeal T).map (C : T →+* T[X]) := hne
  haveI hac : IsAlgClosed (ResidueField T) :=
    (GlobalTheory.AbsIntClosedLocal.henselian_isAlgClosed_pow_surj T ⟨inferInstance, hT⟩).2.1
  obtain ⟨c, hc⟩ := exists_X_sub_C_mem T P hPm hne'
  let τ : T[X] ≃ₐ[T] T[X] := algEquivAevalXAddC (-c)
  have hτX : τ X = X - C c := by simp [τ, sub_eq_add_neg]
  have hτC : ∀ a : T, τ (C a) = C a := fun a => τ.commutes a
  let P' : Ideal T[X] := P.comap (τ : T[X] →+* T[X])
  haveI hP'p : P'.IsPrime := Ideal.comap_isPrime _ _
  have hP'C : P'.comap (C : T →+* T[X]) = maximalIdeal T := by
    rw [← hPm]; ext a
    simp only [Ideal.mem_comap, P']
    rw [show ((τ : T[X] →+* T[X]) (C a)) = C a from hτC a]
  have hXP' : (X : T[X]) ∈ P' := by
    simp only [P', Ideal.mem_comap]
    rw [show ((τ : T[X] →+* T[X]) X) = X - C c from hτX]; exact hc
  have hP' : P' = (maximalIdeal T).map (C : T →+* T[X]) ⊔ Ideal.span {X} := by
    apply le_antisymm
    · intro p hp
      have hd : p - C (p.coeff 0) ∈ Ideal.span {(X : T[X])} := Ideal.mem_span_singleton.2 X_dvd_sub_C
      have hc0 : C (p.coeff 0) ∈ P' := by
        have h1 : p - C (p.coeff 0) ∈ P' := by
          obtain ⟨u, hu⟩ := (X_dvd_sub_C : X ∣ p - C (p.coeff 0))
          rw [hu]; exact P'.mul_mem_right _ hXP'
        have := P'.sub_mem hp h1
        simpa using this
      have hc0' : p.coeff 0 ∈ maximalIdeal T := by rw [← hP'C]; exact hc0
      have : p = C (p.coeff 0) + (p - C (p.coeff 0)) := by ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hc0')) (Ideal.mem_sup_right hd)
    · refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap, hP'C]
      · rw [Ideal.span_le, Set.singleton_subset_iff]; exact hXP'

  let f' : T[X] →+* O := (algebraMap T[X] O).comp (τ : T[X] →+* T[X])
  let alg' : Algebra T[X] O := f'.toAlgebra
  have tower' : @IsScalarTower T T[X] O _ alg'.toSMul _ := by
    refine @IsScalarTower.of_algebraMap_eq T T[X] O _ _ _ _ alg' _ ?_
    intro x
    change algebraMap T O x = f' (algebraMap T T[X] x)
    simp only [f', RingHom.comp_apply]
    rw [show (τ : T[X] →+* T[X]) (algebraMap T T[X] x) = algebraMap T T[X] x from τ.commutes x,
      ← IsScalarTower.algebraMap_apply]

  have hmap : P'.primeCompl.map (τ : T[X] ≃+* T[X]).toMonoidHom = P.primeCompl := by
    ext x
    rw [Submonoid.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨(τ : T[X] ≃+* T[X]).symm x, ?_, by simp⟩
      change (τ : T[X] →+* T[X]) ((τ : T[X] ≃+* T[X]).symm x) ∉ P
      have hx' : x ∉ P := hx
      convert hx' using 2
      exact (τ : T[X] ≃+* T[X]).apply_symm_apply x
  let Lq : Localization.AtPrime P' ≃+* Localization.AtPrime P :=
    IsLocalization.ringEquivOfRingEquiv _ _ (τ : T[X] ≃+* T[X]) hmap
  let φ' : Localization.AtPrime P' →+* O := φ.comp (Lq : Localization.AtPrime P' →+* Localization.AtPrime P)
  have hφ' : φ'.comp (algebraMap T[X] (Localization.AtPrime P')) = f' := by
    refine RingHom.ext fun x => ?_
    simp only [φ', f', RingHom.comp_apply]
    rw [show (Lq : Localization.AtPrime P' →+* Localization.AtPrime P) (algebraMap T[X] _ x)
        = algebraMap T[X] (Localization.AtPrime P) ((τ : T[X] ≃+* T[X]) x) from
      IsLocalization.ringEquivOfRingEquiv_eq _ x]
    rw [← RingHom.comp_apply φ, hφ]
    rfl
  have hsh' : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ' := by
    obtain ⟨h1, h2, h3, h4⟩ := hsh
    refine ⟨h1, h2, ?_, ?_⟩
    · haveI := h3
      haveI : IsLocalHom (Lq : Localization.AtPrime P' →+* Localization.AtPrime P) :=
        ⟨fun a ha => by simpa using ha.map (Lq.symm : Localization.AtPrime P →+* Localization.AtPrime P')⟩
      exact RingHom.isLocalHom_comp _ _
    · have : (RingHom.toMorphismProperty @RingHom.Etale).RespectsIso :=
        RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso
      have h5 := CategoryTheory.MorphismProperty.RespectsIso.precomp
        (CategoryTheory.MorphismProperty.ind.{0} (RingHom.toMorphismProperty @RingHom.Etale))
        Lq.toCommRingCatIso.hom (CommRingCat.ofHom φ) h4
      unfold GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale
      convert h5 using 1
      rfl
  exact @hKO T O _ _ _ _ _ _ alg' tower' hT P' hP'p φ' hφ' hsh' hP'C hP' q hq hqu

end GlobalTheory.LocAcyc.Translate
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.GoodEtaleBase

theorem flat_noetherian_nzd_intClosed : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (ρ : Localization.AtPrime QA →+* A), ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A →
      RingHom.ker ρ = Ideal.span {algebraMap (Polynomial A) (Localization.AtPrime QA) Polynomial.X} →
    Module.Flat A (Localization.AtPrime QA) ∧ IsNoetherianRing (Localization.AtPrime QA) ∧
      algebraMap (Polynomial A) (Localization.AtPrime QA) Polynomial.X ∈ nonZeroDivisors (Localization.AtPrime QA) ∧
      ∀ f : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA), IsIntegral (Localization.AtPrime QA) f →
        ∃ r : Localization.AtPrime QA, algebraMap _ (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) r = f := by
  intro A _ _ _ _ _ _ EA _ _ _ _ _ QA _ _ ρ _ _
  set R := Localization.AtPrime QA
  haveI : Algebra.Smooth A (Polynomial A) := Algebra.Smooth.mk
  haveI : Algebra.Smooth A EA := Algebra.Smooth.comp A (Polynomial A) EA
  haveI : Module.Flat EA R := IsLocalization.flat R QA.primeCompl
  haveI : Module.Flat A EA := Algebra.Smooth.flat A EA
  haveI : Module.Flat (Polynomial A) EA := Algebra.Smooth.flat (Polynomial A) EA
  have hflat : Module.Flat A R := Module.Flat.trans A EA R
  refine ⟨hflat, ?_, ?_, ?_⟩
  · haveI : IsNoetherianRing EA := Algebra.FiniteType.isNoetherianRing (Polynomial A) EA
    exact IsLocalization.isNoetherianRing QA.primeCompl R inferInstance
  · haveI : Module.Flat (Polynomial A) R := Module.Flat.trans (Polynomial A) EA R
    have hX : (Polynomial.X : Polynomial A) ∈ nonZeroDivisors (Polynomial A) :=
      Polynomial.monic_X.mem_nonZeroDivisors
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R) hX
    have h1 : ∀ z : R, algebraMap (Polynomial A) R Polynomial.X * z = 0 → z = 0 := by
      intro z hz
      apply hreg
      simp only [Algebra.smul_def, smul_zero, mul_zero]
      exact hz
    exact ⟨h1, fun z hz => h1 z (by rw [mul_comm]; exact hz)⟩
  · intro f hf
    set K := FractionRing A
    letI : Algebra K (R ⊗[A] K) := Algebra.TensorProduct.rightAlgebra
    haveI : IsScalarTower A K (R ⊗[A] K) := inferInstance
    haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) (R ⊗[A] K) :=
      (Algebra.isLocalization_iff_isPushout (nonZeroDivisors A) K).2 inferInstance
    let e : GlobalTheory.LocAcyc.GenFib A R ≃ₐ[R] R ⊗[A] K :=
      IsLocalization.algEquiv (Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) _ _
    have H1 : Function.Bijective (TensorProduct.toIntegralClosure A EA K) :=
      TensorProduct.toIntegralClosure_bijective_of_smooth
    have H2 : Function.Bijective (TensorProduct.toIntegralClosure EA R (EA ⊗[A] K)) :=
      TensorProduct.toIntegralClosure_bijective_of_isLocalization QA.primeCompl
    have H : Function.Bijective (TensorProduct.toIntegralClosure A R K) :=
      TensorProduct.toIntegralClosure_bijective_of_tower H1 H2
    have hf' : IsIntegral R (e f) := hf.map e.toAlgHom
    obtain ⟨y, hy⟩ := H.2 ⟨e f, hf'⟩
    have hy' : (TensorProduct.toIntegralClosure A R K y : R ⊗[A] K) = e f := congrArg Subtype.val hy
    have key : ∀ y : R ⊗[A] integralClosure A K, ∃ b : R,
        (TensorProduct.toIntegralClosure A R K y : R ⊗[A] K) = b ⊗ₜ[A] (1 : K) := by
      intro y
      induction y with
      | tmul b c =>
        obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 c.2
        refine ⟨r • b, ?_⟩
        rw [TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, hr]
        rfl
      | add u v hu hv =>
        obtain ⟨a, ha⟩ := hu
        obtain ⟨b, hb⟩ := hv
        exact ⟨a + b, by rw [map_add (f := _), Subalgebra.coe_add, ha, hb, TensorProduct.add_tmul]⟩
    obtain ⟨b, hb⟩ := key y
    refine ⟨b, ?_⟩
    apply e.injective
    rw [AlgEquiv.commutes, ← hy', hb]
    rfl

end GlobalTheory.GoodEtaleBase
end
